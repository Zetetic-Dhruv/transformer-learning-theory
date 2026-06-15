/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MuxHierarchy

/-!
# The concrete depth-ladder rung `grade 1 ⊂ grade 2` via the alternation bound (Strategy A)

This module establishes the NEXT rung of the affine-mux depth hierarchy beyond the base
`grade 0 ⊂ grade 1` (`MuxHierarchy.lean`). The base separation used the convexity obstruction; that
tool does NOT extend (grade-1 routes are already non-convex). The right tool is the
**region-count ⇒ alternation bound** crux. We work in the 1-D carrier `d = 1`, route arity `k = 2`,
and (to make the region-count bound finite) the **arity-2** cascade grade `binCascadeGrade`.

## Scope: the CONCRETE rung `binGrade 1 ⊂ binGrade 2` landed; the general `∀L` ladder is open

This file lands the concrete next rung (the fallback of the brief) RIGOROUSLY, building the general
affine-on-fiber and fiber-threshold infrastructure that any `∀L` proof would also need. The general
`∀L` crux (`alternations ≤ 2·pieceCount` for all `L`) is NOT closed; the exact obstruction is recorded
at the end of §(6c): for `L ≥ 2` the trace along the line is NOT a single affine threshold (it is a
threshold composed through the earlier fold layers), so the clean "the trace switches at most once"
argument that powers the `L = 1` crux does not generalize. Closing it needs the full piecewise-linear
piece-count machinery (argmax-of-`n`-lines `= ≤ n` intervals; composition multiplies piece counts),
which is left as future infrastructure.

## The load-bearing chain (each link proved honestly, no `sorry`, no `native_decide`)

1. **Affine self-map composition** (`AffineSelfMap.comp`): so that a fixed composition of branch maps is
   itself an affine self-map.

2. **Affine-on-fiber** (`MuxCascade.run_eq_on_fiber`): for any base point `x₀`, the cascade map
   `C.run` agrees, on the whole trace-fiber `{y | C.trace y = C.trace x₀}`, with a single FIXED affine
   self-map `C.fiberMap x₀`. Proved by induction on depth: on the fiber the gate at every layer is
   pinned to the base point's trace value, so `runUpTo` is a fixed composition of branch-selected
   affine maps. (The base file defines `trace` but not affine-on-fiber.)

3. **Affine-threshold monotonicity** (`affine_threshold_no_TFT` / `affine_threshold_no_FTF`): a single
   affine threshold `t ↦ (0 ≤ α·t + β)` is monotone, hence cannot take the value pattern `X, ¬X, X` on
   three strictly-increasing points. This is the analytic atom of "an affine piece reads a binary argmax
   at most once".

4. **No alternation within a fiber** (`route_no_010_on_fiber` / `route_no_101_on_fiber`): for `d = 1`,
   `k = 2`, the route on one trace-fiber is exactly such a threshold of the carrier coordinate
   (`cascadeRoute_on_fiber_eq_threshold`), so it cannot route `0,1,0` or `1,0,1` on three same-fiber
   points.

5. **Trace monotonicity at depth 1** (`trace_no_ABA_depth_one`): for a depth-1 cascade, the trace along
   the line IS a single affine threshold (the layer-0 gate evaluated at the raw input), so the trace
   likewise cannot take pattern `T, ¬T, T` on three increasing points.

6. **THE CRUX** (`binCascade_depthOne_no_full_alternation`): a depth-1 arity-2 1-D route CANNOT realize
   a full `5`-point alternation `0,1,0,1,0` (nor `1,0,1,0,1`). Proof: among five sorted points the trace
   switches at most once (5), so three CONSECUTIVE points share a fiber; on those the route alternates
   `X,¬X,X`, contradicting (4). This is the region-count ⇒ alternation bound specialized to `L = 1`:
   `pieceCount ≤ ∏ arity = 2`, so `≤ 2·pieceCount = 4` constant runs `⇒ ≤ 3` alternations `< 4`.

7. **WITNESS** (`tentRoute` / `tentCascade`): the depth-2 double sign-fold realizes the 1-D route
   `||t| − 1| < ½` whose value pattern on the explicit increasing list `[-2,-1,0,1,2]` is `0,1,0,1,0`
   — a full `4`-alternation, beyond any depth-1 route's reach.

8. **SEPARATION** (`binCascadeGrade_one_ssubset_two`): `binGrade 1 ⊂ binGrade 2`. `⊆` via the
   identity-layer embedding (`binCascadeGrade_succ_subset`, generalizing the base `0 ↪ 1`); `≠` via
   the high-alternation witness — a REAL proved non-membership.
-/

open scoped BigOperators
open Set

noncomputable section

namespace TLT.TemperedDesignLaw.MuxHierarchy

universe u

/-! ## (1) Affine self-map composition (needed to express affine-on-fiber) -/

/-- Composition of affine self-maps: `(A.comp B).apply x = A.apply (B.apply x)`. -/
def AffineSelfMap.comp {d : ℕ} (A B : AffineSelfMap d) : AffineSelfMap d where
  mat := fun i j => ∑ l, A.mat i l * B.mat l j
  shift := fun i => (∑ l, A.mat i l * B.shift l) + A.shift i

@[simp] theorem AffineSelfMap.comp_apply {d : ℕ} (A B : AffineSelfMap d) (x : Fin d → ℝ) :
    (A.comp B).apply x = A.apply (B.apply x) := by
  funext i
  simp only [AffineSelfMap.comp, AffineSelfMap.apply]
  -- LHS = (∑ j, (∑ l, A i l * B l j) * x j) + ((∑ l, A i l * B.shift l) + A.shift i)
  -- RHS = (∑ l, A i l * ((∑ j, B l j * x j) + B.shift l)) + A.shift i
  -- Reduce both to the canonical double-sum form, then `Finset.sum_comm`.
  have key : ∀ j : Fin d, (∑ l, A.mat i l * B.mat l j) * x j = ∑ l, A.mat i l * B.mat l j * x j :=
    fun j => Finset.sum_mul ..
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  have keyR : ∀ l : Fin d, A.mat i l * ((∑ j, B.mat l j * x j) + B.shift l)
      = (∑ j, A.mat i l * B.mat l j * x j) + A.mat i l * B.shift l := by
    intro l
    have hd : A.mat i l * (∑ j, B.mat l j * x j) = ∑ j, A.mat i l * B.mat l j * x j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [mul_add, hd]
  rw [Finset.sum_congr rfl (fun l _ => keyR l), Finset.sum_add_distrib, Finset.sum_comm]
  ring

/-! ## (2) Affine-on-fiber: `C.run` is a fixed affine map on each trace-fiber -/

/-- The fixed affine map realizing `runUpTo m` on the trace-fiber of `x₀`: at each layer `i < m` it
applies the branch that `x₀`'s trace selects there. -/
def MuxCascade.prefixMap {d L : ℕ} (C : MuxCascade d L) (x₀ : Fin d → ℝ) :
    ℕ → AffineSelfMap d
  | 0 => AffineSelfMap.id d
  | (m + 1) =>
      if h : m < L then
        (C.layers ⟨m, h⟩).branches (C.trace x₀ ⟨m, h⟩) |>.comp (C.prefixMap x₀ m)
      else C.prefixMap x₀ m

/-- **Affine-on-fiber (the depth-induction core).** On the fiber `{y | C.trace y = C.trace x₀}`,
`runUpTo m` equals the fixed affine map `prefixMap C x₀ m`. The hypothesis `C.trace y = C.trace x₀`
pins the gate at every layer to `x₀`'s trace value, so the branch applied is fixed. -/
theorem MuxCascade.runUpTo_eq_prefixMap_on_fiber {d L : ℕ} (C : MuxCascade d L)
    (x₀ y : Fin d → ℝ) (hfib : C.trace y = C.trace x₀) :
    ∀ m, C.runUpTo m y = (C.prefixMap x₀ m).apply y := by
  intro m
  induction m with
  | zero => simp [MuxCascade.runUpTo, MuxCascade.prefixMap]
  | succ m ih =>
      rw [MuxCascade.runUpTo, MuxCascade.prefixMap]
      by_cases h : m < L
      · rw [dif_pos h, dif_pos h]
        rw [AffineSelfMap.comp_apply, ← ih]
        have hgate : (C.layers ⟨m, h⟩).gate (C.harity ⟨m, h⟩) (C.runUpTo m y)
            = C.trace x₀ ⟨m, h⟩ := by
          have : C.trace y ⟨m, h⟩ = C.trace x₀ ⟨m, h⟩ := by rw [hfib]
          simpa [MuxCascade.trace] using this
        simp only [AffineMuxLayer.applyLayer, hgate]
      · rw [dif_neg h, dif_neg h]
        exact ih

/-- The fixed affine self-map that the cascade map `C.run` agrees with on the trace-fiber of `x₀`. -/
def MuxCascade.fiberMap {d L : ℕ} (C : MuxCascade d L) (x₀ : Fin d → ℝ) : AffineSelfMap d :=
  C.prefixMap x₀ L

/-- **AFFINE-ON-FIBER.** `C.run` agrees with the fixed affine map `C.fiberMap x₀` on the whole
trace-fiber of `x₀`. -/
theorem MuxCascade.run_eq_on_fiber {d L : ℕ} (C : MuxCascade d L) (x₀ y : Fin d → ℝ)
    (hfib : C.trace y = C.trace x₀) :
    C.run y = (C.fiberMap x₀).apply y := by
  rw [MuxCascade.run, MuxCascade.fiberMap]
  exact C.runUpTo_eq_prefixMap_on_fiber x₀ y hfib L

/-! ## (3) The 1-D route reads off a single affine threshold per fiber -/

/-- An affine self-map on `Fin 1 → ℝ` acts on the single coordinate as `t ↦ a·t + b`. -/
theorem AffineSelfMap.apply_coord1 (A : AffineSelfMap 1) (x : Fin 1 → ℝ) :
    (A.apply x) 0 = A.mat 0 0 * x 0 + A.shift 0 := by
  simp [AffineSelfMap.apply]

/-- An affine functional on `Fin 1 → ℝ` evaluates as `t ↦ c·t + e`. -/
theorem AffineFunctional.eval_coord1 (f : AffineFunctional 1) (x : Fin 1 → ℝ) :
    f.eval x = f.lin 0 * x 0 + f.const := by
  simp [AffineFunctional.eval]

/-- **The route on a fiber is a single affine threshold of the carrier coordinate.** For `d = 1`,
`k = 2`, on the fiber of `x₀` the route value `cascadeRoute C rs hk y` equals `0` iff
`0 ≤ α · (y 0) + β` for fixed reals `α, β` (depending only on the fiber). -/
theorem cascadeRoute_on_fiber_eq_threshold {L : ℕ} (C : MuxCascade 1 L)
    (rs : Fin 2 → AffineFunctional 1) (x₀ : Fin 1 → ℝ) :
    ∃ α β : ℝ, ∀ y : Fin 1 → ℝ, C.trace y = C.trace x₀ →
      (cascadeRoute C rs (by norm_num) y = 0 ↔ 0 ≤ α * (y 0) + β) := by
  set A := C.fiberMap x₀ with hA
  refine ⟨(((rs 0).lin 0 - (rs 1).lin 0) * A.mat 0 0),
          (((rs 0).lin 0 - (rs 1).lin 0) * A.shift 0 + ((rs 0).const - (rs 1).const)), ?_⟩
  intro y hfib
  rw [cascadeRoute]
  rw [leastArgmax_two]
  have hrun : C.run y = A.apply y := C.run_eq_on_fiber x₀ y hfib
  have hs0 : (rs 0).eval (C.run y) = (rs 0).lin 0 * (C.run y 0) + (rs 0).const :=
    AffineFunctional.eval_coord1 _ _
  have hs1 : (rs 1).eval (C.run y) = (rs 1).lin 0 * (C.run y 0) + (rs 1).const :=
    AffineFunctional.eval_coord1 _ _
  have hc : C.run y 0 = A.mat 0 0 * y 0 + A.shift 0 := by
    rw [hrun]; exact AffineSelfMap.apply_coord1 A y
  constructor
  · intro h
    by_cases hcmp : (rs 1).eval (C.run y) ≤ (rs 0).eval (C.run y)
    · rw [hs0, hs1, hc] at hcmp; nlinarith [hcmp]
    · rw [if_neg hcmp] at h; exact absurd h (by decide)
  · intro h
    have hcmp : (rs 1).eval (C.run y) ≤ (rs 0).eval (C.run y) := by
      rw [hs0, hs1, hc]; nlinarith [h]
    rw [if_pos hcmp]

/-! ## (4) Affine-threshold monotonicity: no `X, ¬X, X` pattern -/

/-- **A single affine threshold cannot produce the pattern `true, false, true`.** If `0 ≤ α t₁ + β`,
`¬(0 ≤ α t₂ + β)`, `0 ≤ α t₃ + β` with `t₁ < t₂ < t₃`, contradiction: `0 ≤ α t + β` is monotone. -/
theorem affine_threshold_no_TFT (α β t₁ t₂ t₃ : ℝ) (h12 : t₁ < t₂) (h23 : t₂ < t₃)
    (h1 : 0 ≤ α * t₁ + β) (h2 : ¬ (0 ≤ α * t₂ + β)) (h3 : 0 ≤ α * t₃ + β) : False := by
  rcases le_or_gt 0 α with hα | hα
  · have : α * t₁ + β ≤ α * t₂ + β := by nlinarith
    exact h2 (le_trans h1 this)
  · have : α * t₃ + β ≤ α * t₂ + β := by nlinarith
    exact h2 (le_trans h3 this)

/-- **A single affine threshold cannot produce the pattern `false, true, false`.** Symmetric to
`affine_threshold_no_TFT` (negate the threshold). -/
theorem affine_threshold_no_FTF (α β t₁ t₂ t₃ : ℝ) (h12 : t₁ < t₂) (h23 : t₂ < t₃)
    (h1 : ¬ (0 ≤ α * t₁ + β)) (h2 : 0 ≤ α * t₂ + β) (h3 : ¬ (0 ≤ α * t₃ + β)) : False := by
  rcases le_or_gt 0 α with hα | hα
  · -- α ≥ 0 increasing: t₂ ≤ t₃ so α t₂ + β ≤ α t₃ + β, but h2 says ≥0 and h3 says <0 — use t₃
    have : α * t₂ + β ≤ α * t₃ + β := by nlinarith
    exact h3 (le_trans h2 this)
  · -- α < 0 decreasing: t₁ < t₂ so α t₂ + β ≤ α t₁ + β; h2 ≥0 forces α t₁+β ≥0, contradict h1
    have : α * t₂ + β ≤ α * t₁ + β := by nlinarith
    exact h1 (le_trans h2 this)

/-! ## (5) No alternation within a single fiber -/

/-- **NO `0,1,0` / `1,0,1` ON A FIBER.** For a grade route on `d = 1`, `k = 2`, three carrier points
with the SAME trace cannot route `0,1,0` (nor `1,0,1`): the route on a fiber is a single affine
threshold, which flips at most once. -/
theorem route_no_010_on_fiber {L : ℕ} (C : MuxCascade 1 L) (rs : Fin 2 → AffineFunctional 1)
    (y₁ y₂ y₃ : Fin 1 → ℝ) (hord12 : y₁ 0 < y₂ 0) (hord23 : y₂ 0 < y₃ 0)
    (htr : C.trace y₁ = C.trace y₂ ∧ C.trace y₂ = C.trace y₃)
    (hr1 : cascadeRoute C rs (by norm_num) y₁ = 0)
    (hr2 : cascadeRoute C rs (by norm_num) y₂ = 1)
    (hr3 : cascadeRoute C rs (by norm_num) y₃ = 0) : False := by
  obtain ⟨α, β, hthr⟩ := cascadeRoute_on_fiber_eq_threshold C rs y₂
  have hf1 : C.trace y₁ = C.trace y₂ := htr.1
  have hf3 : C.trace y₃ = C.trace y₂ := htr.2.symm
  have hf2 : C.trace y₂ = C.trace y₂ := rfl
  have e1 : (0 ≤ α * (y₁ 0) + β) := (hthr y₁ hf1).mp hr1
  have e3 : (0 ≤ α * (y₃ 0) + β) := (hthr y₃ hf3).mp hr3
  have e2 : ¬ (0 ≤ α * (y₂ 0) + β) := by
    intro hcontra
    have := (hthr y₂ hf2).mpr hcontra
    rw [hr2] at this; exact absurd this (by decide)
  exact affine_threshold_no_TFT α β (y₁ 0) (y₂ 0) (y₃ 0) hord12 hord23 e1 e2 e3

theorem route_no_101_on_fiber {L : ℕ} (C : MuxCascade 1 L) (rs : Fin 2 → AffineFunctional 1)
    (y₁ y₂ y₃ : Fin 1 → ℝ) (hord12 : y₁ 0 < y₂ 0) (hord23 : y₂ 0 < y₃ 0)
    (htr : C.trace y₁ = C.trace y₂ ∧ C.trace y₂ = C.trace y₃)
    (hr1 : cascadeRoute C rs (by norm_num) y₁ = 1)
    (hr2 : cascadeRoute C rs (by norm_num) y₂ = 0)
    (hr3 : cascadeRoute C rs (by norm_num) y₃ = 1) : False := by
  obtain ⟨α, β, hthr⟩ := cascadeRoute_on_fiber_eq_threshold C rs y₂
  have hf1 : C.trace y₁ = C.trace y₂ := htr.1
  have hf3 : C.trace y₃ = C.trace y₂ := htr.2.symm
  have hf2 : C.trace y₂ = C.trace y₂ := rfl
  -- route = 1 ↔ ¬(0 ≤ α t + β) ; route = 0 ↔ 0 ≤ α t + β
  have e1 : ¬ (0 ≤ α * (y₁ 0) + β) := by
    intro hcontra
    have := (hthr y₁ hf1).mpr hcontra; rw [hr1] at this; exact absurd this (by decide)
  have e3 : ¬ (0 ≤ α * (y₃ 0) + β) := by
    intro hcontra
    have := (hthr y₃ hf3).mpr hcontra; rw [hr3] at this; exact absurd this (by decide)
  have e2 : (0 ≤ α * (y₂ 0) + β) := (hthr y₂ hf2).mp hr2
  exact affine_threshold_no_FTF α β (y₁ 0) (y₂ 0) (y₃ 0) hord12 hord23 e1 e2 e3

/-! ## (6a) Trace monotonicity at depth 1: the depth-1 gate is a single affine threshold -/

/-- For a depth-1 cascade the trace at the only layer is its gate at the raw input
(`runUpTo 0 y = y`). -/
theorem trace_depth_one {d : ℕ} (C : MuxCascade d 1) (y : Fin d → ℝ) :
    C.trace y ⟨0, by norm_num⟩ = (C.layers ⟨0, by norm_num⟩).gate (C.harity _) y := rfl

/-- **Depth-1 binary gate is an affine threshold.** For `d = 1`, an arity-2 layer's gate is `0` iff
`0 ≤ α·(y 0) + β` for fixed `α, β`, since the two scores are affine in the single coordinate and the
`leastArgmax` of two values is the score comparison (`leastArgmax_two`). -/
theorem layer_binary_gate_threshold (Lyr : AffineMuxLayer 1 2) :
    ∃ α β : ℝ, ∀ y : Fin 1 → ℝ,
      (Lyr.gate (by norm_num) y = 0 ↔ 0 ≤ α * (y 0) + β) := by
  refine ⟨((Lyr.scores 0).lin 0 - (Lyr.scores 1).lin 0),
          ((Lyr.scores 0).const - (Lyr.scores 1).const), ?_⟩
  intro y
  simp only [AffineMuxLayer.gate]
  rw [leastArgmax_two]
  have hs0 : (Lyr.scores 0).eval y = (Lyr.scores 0).lin 0 * (y 0) + (Lyr.scores 0).const :=
    AffineFunctional.eval_coord1 _ _
  have hs1 : (Lyr.scores 1).eval y = (Lyr.scores 1).lin 0 * (y 0) + (Lyr.scores 1).const :=
    AffineFunctional.eval_coord1 _ _
  constructor
  · intro h
    by_cases hcmp : (Lyr.scores 1).eval y ≤ (Lyr.scores 0).eval y
    · rw [hs0, hs1] at hcmp; nlinarith [hcmp]
    · rw [if_neg hcmp] at h; exact absurd h (by decide)
  · intro h
    have hcmp : (Lyr.scores 1).eval y ≤ (Lyr.scores 0).eval y := by
      rw [hs0, hs1]; nlinarith [h]
    rw [if_pos hcmp]

/-- The arity-2 gate value is `1` exactly when the threshold fails. (A `Fin 2` value is `0` or `1`.) -/
theorem layer_binary_gate_one_iff (Lyr : AffineMuxLayer 1 2) (α β : ℝ)
    (hthr : ∀ y : Fin 1 → ℝ, (Lyr.gate (by norm_num) y = 0 ↔ 0 ≤ α * (y 0) + β)) :
    ∀ y : Fin 1 → ℝ, (Lyr.gate (by norm_num) y = 1 ↔ ¬ (0 ≤ α * (y 0) + β)) := by
  intro y
  constructor
  · intro h hcon
    have : Lyr.gate (by norm_num) y = 0 := (hthr y).mpr hcon
    rw [this] at h; exact absurd h (by decide)
  · intro h
    have hne0 : Lyr.gate (by norm_num) y ≠ 0 := fun h0 => h ((hthr y).mp h0)
    omega

/-- **TRACE NO-`T,¬T,T` AT DEPTH 1 (arity 2).** Given a depth-1 cascade whose trace at the single layer
is a single affine threshold of the carrier coordinate — `C.trace y i0 = 0 ↔ 0 ≤ α·(y 0) + β`, with
the trace landing in `Fin 2` — the trace along the line is monotone, so on three increasing points it
cannot return to its starting value after leaving it: it cannot be `t, t', t` with `t ≠ t'`. -/
theorem trace_no_ABA_depth_one (C : MuxCascade 1 1) (α β : ℝ)
    (harity2 : C.arity ⟨0, by norm_num⟩ = 2)
    (hthr : ∀ y : Fin 1 → ℝ,
      ((C.trace y ⟨0, by norm_num⟩).val = 0 ↔ 0 ≤ α * (y 0) + β))
    (y₁ y₂ y₃ : Fin 1 → ℝ) (hord12 : y₁ 0 < y₂ 0) (hord23 : y₂ 0 < y₃ 0)
    (h13 : C.trace y₁ = C.trace y₃) (h12 : C.trace y₁ ≠ C.trace y₂) : False := by
  set i0 : Fin 1 := ⟨0, by norm_num⟩ with hi0
  -- two depth-1 traces are equal iff they agree at the only index i0
  have htrace_iff : ∀ a b : Fin 1 → ℝ,
      (C.trace a = C.trace b) ↔ (C.trace a i0 = C.trace b i0) := by
    intro a b
    constructor
    · intro h; rw [h]
    · intro h; funext j
      have : j = i0 := by fin_cases j; rfl
      rw [this]; exact h
  have e13 : C.trace y₁ i0 = C.trace y₃ i0 := (htrace_iff y₁ y₃).mp h13
  have e12 : C.trace y₁ i0 ≠ C.trace y₂ i0 := fun hc => h12 ((htrace_iff y₁ y₂).mpr hc)
  -- the trace `.val` is 0 or 1; argue on the threshold pattern via `.val`
  have hval_lt : ∀ y : Fin 1 → ℝ, (C.trace y i0).val < 2 := by
    intro y; rw [← harity2]; exact (C.trace y i0).isLt
  -- the "= 1" version of the threshold (Fin 2 value)
  have hthr1 : ∀ y : Fin 1 → ℝ, ((C.trace y i0).val = 1 ↔ ¬ (0 ≤ α * (y 0) + β)) := by
    intro y
    have h2 := hval_lt y
    constructor
    · intro h hc
      have := (hthr y).mpr hc; omega
    · intro h
      have : (C.trace y i0).val ≠ 0 := fun h0 => h ((hthr y).mp h0)
      omega
  by_cases hp1 : (0 ≤ α * (y₁ 0) + β)
  · have hv1 : (C.trace y₁ i0).val = 0 := (hthr y₁).mpr hp1
    have hv3 : (C.trace y₃ i0).val = 0 := by rw [← e13]; exact hv1
    have hp3 : (0 ≤ α * (y₃ 0) + β) := (hthr y₃).mp hv3
    have hp2 : ¬ (0 ≤ α * (y₂ 0) + β) := by
      intro hcon
      have hv2 : (C.trace y₂ i0).val = 0 := (hthr y₂).mpr hcon
      exact e12 (Fin.ext (hv1.trans hv2.symm))
    exact affine_threshold_no_TFT α β (y₁ 0) (y₂ 0) (y₃ 0) hord12 hord23 hp1 hp2 hp3
  · have hv1 : (C.trace y₁ i0).val = 1 := (hthr1 y₁).mpr hp1
    have hv3 : (C.trace y₃ i0).val = 1 := by rw [← e13]; exact hv1
    have hp3 : ¬ (0 ≤ α * (y₃ 0) + β) := (hthr1 y₃).mp hv3
    have hp2 : (0 ≤ α * (y₂ 0) + β) := by
      by_contra hcon
      have hv2 : (C.trace y₂ i0).val = 1 := (hthr1 y₂).mpr hcon
      exact e12 (Fin.ext (hv1.trans hv2.symm))
    exact affine_threshold_no_FTF α β (y₁ 0) (y₂ 0) (y₃ 0) hord12 hord23 hp1 hp2 hp3

/-! ## (6b) The arity-2 cascade grade (`binCascadeGrade`) -/

/-- The depth-`L` arity-2 cascade built from a `Fin L`-family of arity-2 layers. The arity is
`fun _ => 2` *literally* (definitionally), so `arity i` reduces to `2`, the layers keep their
`AffineMuxLayer d 2` type, and the trace lands in `Fin 2` with no transport. -/
def binCascade {d L : ℕ} (layers : Fin L → AffineMuxLayer d 2) : MuxCascade d L where
  arity := fun _ => 2
  harity := fun _ => by norm_num
  layers := layers

/-- **The arity-2 cascade grade.** Routes realizable by SOME depth-`L` cascade ALL of whose layers
have arity `2`, together with SOME `k` affine route-scores. This is the arity-bounded analogue of
`muxCascadeGrade`; the region-count bound `pieceCount ≤ 2^L` is then finite and drives the alternation
bound. -/
def binCascadeGrade (d k L : ℕ) (hk : 0 < k) : Set ((Fin d → ℝ) → Fin k) :=
  { f | ∃ (layers : Fin L → AffineMuxLayer d 2) (routeScores : Fin k → AffineFunctional d),
      f = cascadeRoute (binCascade layers) routeScores hk }

/-- For a depth-1 binary cascade the trace at the single layer is a single affine threshold of the
carrier coordinate — read directly off the layer-0 gate (`trace_depth_one` + `layer_binary_gate`),
with NO `Fin`-cast since the arity is definitionally `2`. -/
theorem binCascade_depthOne_trace_threshold (Lyr : AffineMuxLayer 1 2) :
    ∃ α β : ℝ, ∀ y : Fin 1 → ℝ,
      (((binCascade (L := 1) (fun _ => Lyr)).trace y (0 : Fin 1)).val = 0 ↔ 0 ≤ α * (y 0) + β) := by
  obtain ⟨α, β, hthr⟩ := layer_binary_gate_threshold Lyr
  refine ⟨α, β, ?_⟩
  intro y
  -- trace y i0 = gate of layer 0 = Lyr.gate _ y (binCascade layers 0 = Lyr); both in Fin 2
  have htr : (binCascade (L := 1) (fun _ => Lyr)).trace y (0 : Fin 1) = Lyr.gate (by norm_num) y :=
    trace_depth_one (binCascade (L := 1) (fun _ => Lyr)) y
  rw [htr]
  -- (Lyr.gate _ y).val = 0 ↔ Lyr.gate _ y = 0 ↔ 0 ≤ α y0 + β
  rw [show ((Lyr.gate (by norm_num) y).val = 0) ↔ (Lyr.gate (by norm_num) y = 0) from
    ⟨fun h => Fin.ext h, fun h => by rw [h]; rfl⟩]
  exact hthr y

/-! ## (6c) THE CRUX: a depth-1 arity-2 route cannot realize a 5-point full alternation -/

/-- For a depth-1 binary cascade, full trace equality is equality of the single-layer trace `.val`. -/
theorem binCascade_depthOne_traceEq_iff (Lyr : AffineMuxLayer 1 2) (a b : Fin 1 → ℝ) :
    ((binCascade (L := 1) (fun _ => Lyr)).trace a = (binCascade (L := 1) (fun _ => Lyr)).trace b)
      ↔ ((binCascade (L := 1) (fun _ => Lyr)).trace a (0 : Fin 1)).val
          = ((binCascade (L := 1) (fun _ => Lyr)).trace b (0 : Fin 1)).val := by
  constructor
  · intro h; rw [h]
  · intro h
    funext j
    have hj : j = (0 : Fin 1) := by fin_cases j; rfl
    rw [hj]; exact Fin.ext h

/-- **THE CRUX (region-count ⇒ alternation bound, specialized to `L = 1`).** A depth-1 arity-2 cascade
route on `d = 1`, `k = 2`, CANNOT realize the full `5`-point alternation `0,1,0,1,0` on any five
strictly-increasing carrier points. Region-count: `pieceCount ≤ ∏ arity = 2`, so the trace along the
line switches at most once (`trace_no_ABA_depth_one`); hence three CONSECUTIVE points share a fiber,
and on those the route reads `X,¬X,X` — impossible (`route_no_010/101_on_fiber`). Thus a depth-1 route
has at most `3` alternations, strictly fewer than the witness's `4`. -/
theorem binCascade_depthOne_no_full_alternation
    (Lyr : AffineMuxLayer 1 2) (rs : Fin 2 → AffineFunctional 1)
    (p₀ p₁ p₂ p₃ p₄ : Fin 1 → ℝ)
    (h01 : p₀ 0 < p₁ 0) (h12 : p₁ 0 < p₂ 0) (h23 : p₂ 0 < p₃ 0) (h34 : p₃ 0 < p₄ 0)
    (hr0 : cascadeRoute (binCascade (L := 1) (fun _ => Lyr)) rs (by norm_num) p₀ = 0)
    (hr1 : cascadeRoute (binCascade (L := 1) (fun _ => Lyr)) rs (by norm_num) p₁ = 1)
    (hr2 : cascadeRoute (binCascade (L := 1) (fun _ => Lyr)) rs (by norm_num) p₂ = 0)
    (hr3 : cascadeRoute (binCascade (L := 1) (fun _ => Lyr)) rs (by norm_num) p₃ = 1)
    (hr4 : cascadeRoute (binCascade (L := 1) (fun _ => Lyr)) rs (by norm_num) p₄ = 0) : False := by
  set C := binCascade (L := 1) (fun _ => Lyr) with hC
  set i0 : Fin 1 := 0 with hi0
  -- the five trace bits
  set t0 := (C.trace p₀ i0).val with ht0
  set t1 := (C.trace p₁ i0).val with ht1
  set t2 := (C.trace p₂ i0).val with ht2
  set t3 := (C.trace p₃ i0).val with ht3
  set t4 := (C.trace p₄ i0).val with ht4
  -- bits are < 2
  have hlt : ∀ y : Fin 1 → ℝ, (C.trace y i0).val < 2 := fun y => (C.trace y i0).isLt
  have hb0 : t0 < 2 := hlt p₀
  have hb1 : t1 < 2 := hlt p₁
  have hb2 : t2 < 2 := hlt p₂
  have hb3 : t3 < 2 := hlt p₃
  have hb4 : t4 < 2 := hlt p₄
  -- the trace threshold (for the trace-no-ABA lemma)
  obtain ⟨α, β, hthr⟩ := binCascade_depthOne_trace_threshold Lyr
  -- helper: a trace-ABA among three increasing points is impossible
  have noTraceABA : ∀ (a b c : Fin 1 → ℝ), a 0 < b 0 → b 0 < c 0 →
      (C.trace a i0).val = (C.trace c i0).val →
      (C.trace a i0).val ≠ (C.trace b i0).val → False := by
    intro a b c hab hbc hac habne
    exact trace_no_ABA_depth_one C α β rfl hthr a b c hab hbc
      ((binCascade_depthOne_traceEq_iff Lyr a c).mpr hac)
      (fun he => habne ((binCascade_depthOne_traceEq_iff Lyr a b).mp he))
  -- helper: a route 0,1,0 within one fiber is impossible
  have noRoute010 : ∀ (a b c : Fin 1 → ℝ), a 0 < b 0 → b 0 < c 0 →
      (C.trace a i0).val = (C.trace b i0).val → (C.trace b i0).val = (C.trace c i0).val →
      cascadeRoute C rs (by norm_num) a = 0 → cascadeRoute C rs (by norm_num) b = 1 →
      cascadeRoute C rs (by norm_num) c = 0 → False := by
    intro a b c hab hbc heab hebc ra rb rc
    exact route_no_010_on_fiber C rs a b c hab hbc
      ⟨(binCascade_depthOne_traceEq_iff Lyr a b).mpr heab,
       (binCascade_depthOne_traceEq_iff Lyr b c).mpr hebc⟩ ra rb rc
  -- helper: a route 1,0,1 within one fiber is impossible
  have noRoute101 : ∀ (a b c : Fin 1 → ℝ), a 0 < b 0 → b 0 < c 0 →
      (C.trace a i0).val = (C.trace b i0).val → (C.trace b i0).val = (C.trace c i0).val →
      cascadeRoute C rs (by norm_num) a = 1 → cascadeRoute C rs (by norm_num) b = 0 →
      cascadeRoute C rs (by norm_num) c = 1 → False := by
    intro a b c hab hbc heab hebc ra rb rc
    exact route_no_101_on_fiber C rs a b c hab hbc
      ⟨(binCascade_depthOne_traceEq_iff Lyr a b).mpr heab,
       (binCascade_depthOne_traceEq_iff Lyr b c).mpr hebc⟩ ra rb rc
  -- Now the combinatorics on the five bits t0..t4 ∈ {0,1}.
  -- If three CONSECUTIVE bits are equal, the route there is X,¬X,X — contradiction.
  -- Consecutive triples & their route patterns: (0,1,2)=0,1,0 ; (1,2,3)=1,0,1 ; (2,3,4)=0,1,0.
  by_cases c012 : t0 = t1 ∧ t1 = t2
  · exact noRoute010 p₀ p₁ p₂ h01 h12 c012.1 c012.2 hr0 hr1 hr2
  by_cases c123 : t1 = t2 ∧ t2 = t3
  · exact noRoute101 p₁ p₂ p₃ h12 h23 c123.1 c123.2 hr1 hr2 hr3
  by_cases c234 : t2 = t3 ∧ t3 = t4
  · exact noRoute010 p₂ p₃ p₄ h23 h34 c234.1 c234.2 hr2 hr3 hr4
  -- No consecutive triple is constant. With binary bits and ≤1 trace switch (no-ABA), this is
  -- impossible; concretely, we now exhibit a trace-ABA. Push the negations.
  push Not at c012 c123 c234
  -- Identify a trace-ABA among the points. We argue by the bit values directly.
  -- First: no trace-ABA on any increasing triple (else done).
  -- Use the three "outer" triples to pin a contradiction with omega on the bits, given no-ABA.
  -- We derive each candidate ABA and discharge by `noTraceABA` if its hypotheses hold.
  -- Strategy: show that under "no constant consecutive triple", some ABA must occur.
  -- Case split fully on the five bits (each 0 or 1) and resolve each.
  interval_cases t0 <;> interval_cases t1 <;> interval_cases t2 <;>
    interval_cases t3 <;> interval_cases t4 <;>
    first
      | (exfalso; revert c012 c123 c234; decide)
      | (exact noTraceABA p₀ p₁ p₂ h01 h12 (by omega) (by omega))
      | (exact noTraceABA p₁ p₂ p₃ h12 h23 (by omega) (by omega))
      | (exact noTraceABA p₂ p₃ p₄ h23 h34 (by omega) (by omega))
      | (exact noTraceABA p₀ p₁ p₃ h01 (by linarith) (by omega) (by omega))
      | (exact noTraceABA p₀ p₂ p₄ (by linarith) (by linarith) (by omega) (by omega))

/-! ## (7) THE WITNESS: a depth-2 double sign-fold realizing the tent route `||t|−1| < ½` -/

/-- Fold layer 1 (arity 2): gate on the sign of the carrier coordinate (`gate = 0` iff `t ≥ 0`),
branch 0 = identity, branch 1 = negate. Output state = `|t|`. -/
def foldAbsLayer : AffineMuxLayer 1 2 where
  scores := fun i => if i = 0 then ⟨fun _ => 1, 0⟩ else ⟨fun _ => -1, 0⟩
  branches := fun i => if i = 0 then AffineSelfMap.id 1
                                else ⟨fun _ _ => -1, fun _ => 0⟩

/-- Fold layer 2 (arity 2): gate on the sign of `state − 1` (`gate = 0` iff `state ≥ 1`),
branch 0 = `s ↦ s − 1`, branch 1 = `s ↦ 1 − s`. Output state = `|state − 1|`. -/
def foldShiftLayer : AffineMuxLayer 1 2 where
  scores := fun i => if i = 0 then ⟨fun _ => 1, -1⟩ else ⟨fun _ => -1, 1⟩
  branches := fun i => if i = 0 then ⟨fun _ _ => 1, fun _ => -1⟩
                                else ⟨fun _ _ => -1, fun _ => 1⟩

/-- The two layers of the depth-2 tent cascade. -/
def tentLayers : Fin 2 → AffineMuxLayer 1 2 :=
  fun i => if i = 0 then foldAbsLayer else foldShiftLayer

/-- The depth-2 double sign-fold cascade. -/
def tentCascade : MuxCascade 1 2 := binCascade tentLayers

/-- The tent readout: `route 0 = s ↦ s − ½`, `route 1 = s ↦ ½ − s`. `route = 0` iff `state ≥ ½`. -/
def tentRouteScores : Fin 2 → AffineFunctional 1 :=
  fun j => if j = 0 then ⟨fun _ => 1, -(1/2)⟩ else ⟨fun _ => -1, 1/2⟩

/-- The tent route realized by the depth-2 cascade. By construction it lies in `binCascadeGrade 1 2 2`. -/
def tentRoute : (Fin 1 → ℝ) → Fin 2 :=
  cascadeRoute tentCascade tentRouteScores (by norm_num)

theorem tentRoute_mem_binGradeTwo :
    tentRoute ∈ binCascadeGrade 1 2 2 (by norm_num) :=
  ⟨tentLayers, tentRouteScores, rfl⟩

/-! ### (7a) Coordinate-level actions of the two fold layers -/

/-- `foldAbsLayer`'s two scores evaluate to `x 0` (score 0) and `-(x 0)` (score 1). -/
theorem foldAbsLayer_scores (x : Fin 1 → ℝ) :
    (foldAbsLayer.scores 0).eval x = x 0 ∧ (foldAbsLayer.scores 1).eval x = -(x 0) := by
  refine ⟨?_, ?_⟩
  · show (foldAbsLayer.scores 0).eval x = x 0
    have : foldAbsLayer.scores 0 = ⟨fun _ => 1, 0⟩ := by simp [foldAbsLayer]
    rw [this]; simp [AffineFunctional.eval]
  · show (foldAbsLayer.scores 1).eval x = -(x 0)
    have : foldAbsLayer.scores 1 = ⟨fun _ => -1, 0⟩ := by simp [foldAbsLayer]
    rw [this]; simp [AffineFunctional.eval]

/-- `foldAbsLayer`'s gate: `0` iff `x 0 ≥ 0`. -/
theorem foldAbsLayer_gate (x : Fin 1 → ℝ) :
    foldAbsLayer.gate (by norm_num) x = if 0 ≤ x 0 then 0 else 1 := by
  simp only [AffineMuxLayer.gate]; rw [leastArgmax_two]
  obtain ⟨h0, h1⟩ := foldAbsLayer_scores x
  simp only [h0, h1]
  by_cases hx : (0 : ℝ) ≤ x 0
  · rw [if_pos (by linarith), if_pos hx]
  · rw [if_neg (by push Not at hx ⊢; linarith), if_neg hx]

/-- `foldAbsLayer`'s carrier action: `x 0 ↦ |x 0|`. -/
theorem foldAbsLayer_apply (x : Fin 1 → ℝ) :
    (foldAbsLayer.applyLayer (by norm_num) x) 0 = if 0 ≤ x 0 then x 0 else -(x 0) := by
  simp only [AffineMuxLayer.applyLayer, foldAbsLayer_gate]
  by_cases hx : (0 : ℝ) ≤ x 0
  · rw [if_pos hx, if_pos hx]
    show ((foldAbsLayer.branches 0).apply x) 0 = x 0
    have : foldAbsLayer.branches 0 = AffineSelfMap.id 1 := by simp [foldAbsLayer]
    rw [this, AffineSelfMap.id_apply]
  · rw [if_neg hx, if_neg hx]
    show ((foldAbsLayer.branches 1).apply x) 0 = -(x 0)
    have : foldAbsLayer.branches 1 = ⟨fun _ _ => -1, fun _ => 0⟩ := by simp [foldAbsLayer]
    rw [this]; simp [AffineSelfMap.apply]

/-- `foldShiftLayer`'s two scores evaluate to `s 0 − 1` (score 0) and `1 − s 0` (score 1). -/
theorem foldShiftLayer_scores (s : Fin 1 → ℝ) :
    (foldShiftLayer.scores 0).eval s = s 0 - 1 ∧ (foldShiftLayer.scores 1).eval s = 1 - s 0 := by
  refine ⟨?_, ?_⟩
  · show (foldShiftLayer.scores 0).eval s = s 0 - 1
    have : foldShiftLayer.scores 0 = ⟨fun _ => 1, -1⟩ := by simp [foldShiftLayer]
    rw [this]; simp [AffineFunctional.eval]; ring
  · show (foldShiftLayer.scores 1).eval s = 1 - s 0
    have : foldShiftLayer.scores 1 = ⟨fun _ => -1, 1⟩ := by simp [foldShiftLayer]
    rw [this]; simp [AffineFunctional.eval]; ring

/-- `foldShiftLayer`'s gate: `0` iff `s 0 ≥ 1`. -/
theorem foldShiftLayer_gate (s : Fin 1 → ℝ) :
    foldShiftLayer.gate (by norm_num) s = if 1 ≤ s 0 then 0 else 1 := by
  simp only [AffineMuxLayer.gate]; rw [leastArgmax_two]
  obtain ⟨h0, h1⟩ := foldShiftLayer_scores s
  simp only [h0, h1]
  by_cases hx : (1 : ℝ) ≤ s 0
  · rw [if_pos (by linarith), if_pos hx]
  · rw [if_neg (by push Not at hx ⊢; linarith), if_neg hx]

/-- `foldShiftLayer`'s carrier action: `s 0 ↦ |s 0 − 1|`. -/
theorem foldShiftLayer_apply (s : Fin 1 → ℝ) :
    (foldShiftLayer.applyLayer (by norm_num) s) 0 = if 1 ≤ s 0 then s 0 - 1 else 1 - s 0 := by
  simp only [AffineMuxLayer.applyLayer, foldShiftLayer_gate]
  by_cases hx : (1 : ℝ) ≤ s 0
  · rw [if_pos hx, if_pos hx]
    show ((foldShiftLayer.branches 0).apply s) 0 = s 0 - 1
    have : foldShiftLayer.branches 0 = ⟨fun _ _ => 1, fun _ => -1⟩ := by simp [foldShiftLayer]
    rw [this]; simp [AffineSelfMap.apply]; ring
  · rw [if_neg hx, if_neg hx]
    show ((foldShiftLayer.branches 1).apply s) 0 = 1 - s 0
    have : foldShiftLayer.branches 1 = ⟨fun _ _ => -1, fun _ => 1⟩ := by simp [foldShiftLayer]
    rw [this]; simp [AffineSelfMap.apply]; ring

/-! ### (7b) The cascade run and the route value -/

/-- The layer of `tentCascade` at index `0` is `foldAbsLayer`, at index `1` is `foldShiftLayer`. -/
theorem tentCascade_layer0 : tentCascade.layers ⟨0, by norm_num⟩ = foldAbsLayer := rfl
theorem tentCascade_layer1 : tentCascade.layers ⟨1, by norm_num⟩ = foldShiftLayer := rfl

/-- `runUpTo 1` of the tent cascade applies `foldAbsLayer`. -/
theorem tentCascade_runUpTo_one (x : Fin 1 → ℝ) :
    (tentCascade.runUpTo 1 x) 0 = if 0 ≤ x 0 then x 0 else -(x 0) := by
  rw [MuxCascade.runUpTo, dif_pos (by norm_num : (0:ℕ) < 2)]
  show (foldAbsLayer.applyLayer _ (tentCascade.runUpTo 0 x)) 0 = _
  rw [MuxCascade.runUpTo]
  exact foldAbsLayer_apply x

/-- **The tent cascade's output coordinate is the double fold `||t| − 1|`.** -/
theorem tentCascade_run_coord (x : Fin 1 → ℝ) :
    (tentCascade.run x) 0
      = (if 1 ≤ (if 0 ≤ x 0 then x 0 else -(x 0)) then (if 0 ≤ x 0 then x 0 else -(x 0)) - 1
         else 1 - (if 0 ≤ x 0 then x 0 else -(x 0))) := by
  show (tentCascade.runUpTo 2 x) 0 = _
  rw [MuxCascade.runUpTo, dif_pos (by norm_num : (1:ℕ) < 2)]
  show (foldShiftLayer.applyLayer _ (tentCascade.runUpTo 1 x)) 0 = _
  rw [foldShiftLayer_apply, tentCascade_runUpTo_one]

/-- The tent readout scores evaluate to `s 0 − ½` (route 0) and `½ − s 0` (route 1). -/
theorem tentRouteScores_eval (s : Fin 1 → ℝ) :
    (tentRouteScores 0).eval s = s 0 - 1/2 ∧ (tentRouteScores 1).eval s = 1/2 - s 0 := by
  refine ⟨?_, ?_⟩
  · show (tentRouteScores 0).eval s = s 0 - 1/2
    have : tentRouteScores 0 = ⟨fun _ => 1, -(1/2)⟩ := by simp [tentRouteScores]
    rw [this]; simp [AffineFunctional.eval]; ring
  · show (tentRouteScores 1).eval s = 1/2 - s 0
    have : tentRouteScores 1 = ⟨fun _ => -1, 1/2⟩ := by simp [tentRouteScores]
    rw [this]; simp [AffineFunctional.eval]; ring

/-- **The tent route is the threshold `state ≥ ½`** on the doubly-folded coordinate: `route = 0` iff
`tentCascade.run x 0 ≥ ½`, else `1`. -/
theorem tentRoute_eq (x : Fin 1 → ℝ) :
    tentRoute x = if 1/2 ≤ (tentCascade.run x) 0 then 0 else 1 := by
  show cascadeRoute tentCascade tentRouteScores (by norm_num) x = _
  rw [cascadeRoute, leastArgmax_two]
  obtain ⟨h0, h1⟩ := tentRouteScores_eval (tentCascade.run x)
  simp only [h0, h1]
  by_cases hc : (1:ℝ)/2 ≤ (tentCascade.run x) 0
  · rw [if_pos (by linarith), if_pos hc]
  · rw [if_neg (by push Not at hc ⊢; linarith), if_neg hc]

/-! ### (7c) The tent route value on the explicit 5-point alternating sample -/

theorem tentRoute_at_m2 : tentRoute ![(-2 : ℝ)] = 0 := by
  rw [tentRoute_eq, tentCascade_run_coord]
  norm_num

theorem tentRoute_at_m1 : tentRoute ![(-1 : ℝ)] = 1 := by
  rw [tentRoute_eq, tentCascade_run_coord]
  norm_num

theorem tentRoute_at_0 : tentRoute ![(0 : ℝ)] = 0 := by
  rw [tentRoute_eq, tentCascade_run_coord]
  norm_num

theorem tentRoute_at_1 : tentRoute ![(1 : ℝ)] = 1 := by
  rw [tentRoute_eq, tentCascade_run_coord]
  norm_num

theorem tentRoute_at_2 : tentRoute ![(2 : ℝ)] = 0 := by
  rw [tentRoute_eq, tentCascade_run_coord]
  norm_num

/-! ## (8) THE SEPARATION: `binGrade 1 ⊂ binGrade 2` -/

/-- **NON-MEMBERSHIP (a REAL proved non-membership).** `tentRoute ∉ binCascadeGrade 1 2 1`. If it were a
depth-1 arity-2 route, then on the increasing sample `[-2,-1,0,1,2]` it would have to realize the full
`5`-point alternation `0,1,0,1,0`, contradicting the crux `binCascade_depthOne_no_full_alternation`. -/
theorem tentRoute_not_mem_binGradeOne :
    tentRoute ∉ binCascadeGrade 1 2 1 (by norm_num) := by
  rintro ⟨layers, rs, hf⟩
  -- the single layer
  set Lyr := layers 0 with hLyr
  -- binCascade layers = binCascade (fun _ => Lyr) since `layers` is determined by its only value
  have hlayers : layers = fun _ => Lyr := by
    funext i; have : i = 0 := by fin_cases i; rfl
    rw [this]
  rw [hlayers] at hf
  -- transport the 5 route values to the realizing cascade
  have hv0 : cascadeRoute (binCascade (L := 1) (fun _ => Lyr)) rs (by norm_num) ![(-2:ℝ)] = 0 := by
    rw [← hf]; exact tentRoute_at_m2
  have hv1 : cascadeRoute (binCascade (L := 1) (fun _ => Lyr)) rs (by norm_num) ![(-1:ℝ)] = 1 := by
    rw [← hf]; exact tentRoute_at_m1
  have hv2 : cascadeRoute (binCascade (L := 1) (fun _ => Lyr)) rs (by norm_num) ![(0:ℝ)] = 0 := by
    rw [← hf]; exact tentRoute_at_0
  have hv3 : cascadeRoute (binCascade (L := 1) (fun _ => Lyr)) rs (by norm_num) ![(1:ℝ)] = 1 := by
    rw [← hf]; exact tentRoute_at_1
  have hv4 : cascadeRoute (binCascade (L := 1) (fun _ => Lyr)) rs (by norm_num) ![(2:ℝ)] = 0 := by
    rw [← hf]; exact tentRoute_at_2
  exact binCascade_depthOne_no_full_alternation Lyr rs
    ![(-2:ℝ)] ![(-1:ℝ)] ![(0:ℝ)] ![(1:ℝ)] ![(2:ℝ)]
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hv0 hv1 hv2 hv3 hv4

/-! ### (8a) The depth-monotone embedding `binGrade L ↪ binGrade (L+1)` -/

/-- The do-nothing arity-2 layer: both branches are the identity (so its action is the identity
regardless of the gate). Prepending it embeds depth `L` into depth `L+1`. -/
def binIdLayer (d : ℕ) : AffineMuxLayer d 2 where
  scores := fun _ => ⟨fun _ => 0, 0⟩
  branches := fun _ => AffineSelfMap.id d

@[simp] theorem binIdLayer_applyLayer {d : ℕ} (hn : 0 < 2) (x : Fin d → ℝ) :
    (binIdLayer d).applyLayer hn x = x := by
  simp only [AffineMuxLayer.applyLayer]
  show ((binIdLayer d).branches _).apply x = x
  have : ∀ i : Fin 2, (binIdLayer d).branches i = AffineSelfMap.id d := fun _ => rfl
  rw [this]; exact AffineSelfMap.id_apply x

/-- The layer family obtained by APPENDING the do-nothing identity layer at the last index. The first
`L` layers are the original ones; the layer at index `L` is `binIdLayer`. -/
def appendIdLayers {L : ℕ} (layers : Fin L → AffineMuxLayer 1 2) :
    Fin (L + 1) → AffineMuxLayer 1 2 :=
  fun i => if h : i.val < L then layers ⟨i.val, h⟩ else binIdLayer 1

/-- For `m ≤ L`, running the first `m` layers of the appended cascade equals running them on the
original cascade — the appended family agrees with the original on every index `< L ≥ m`. -/
theorem appendId_runUpTo_eq {L : ℕ} (layers : Fin L → AffineMuxLayer 1 2) (x : Fin 1 → ℝ) :
    ∀ m, m ≤ L →
      (binCascade (L := L + 1) (appendIdLayers layers)).runUpTo m x
        = (binCascade (L := L) layers).runUpTo m x := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      have hmL : m < L := by omega
      have hmL1 : m < L + 1 := by omega
      rw [MuxCascade.runUpTo, MuxCascade.runUpTo, dif_pos hmL1, dif_pos hmL]
      -- the layers at index m coincide
      have hlayer : (binCascade (L := L + 1) (appendIdLayers layers)).layers ⟨m, hmL1⟩
          = (binCascade (L := L) layers).layers ⟨m, hmL⟩ := by
        show appendIdLayers layers ⟨m, hmL1⟩ = layers ⟨m, hmL⟩
        rw [appendIdLayers, dif_pos hmL]
      -- the recursive states coincide
      have hstate := ih (by omega)
      rw [hstate]
      -- applyLayer with equal layers and equal states
      simp only [AffineMuxLayer.applyLayer, AffineMuxLayer.gate, hlayer]
      rfl

/-- **APPEND-IDENTITY RUN INVARIANCE.** Appending the identity layer leaves the cascade output
unchanged: `run` of the depth-`(L+1)` appended cascade equals `run` of the depth-`L` original. -/
theorem appendId_run_eq {L : ℕ} (layers : Fin L → AffineMuxLayer 1 2) (x : Fin 1 → ℝ) :
    (binCascade (L := L + 1) (appendIdLayers layers)).run x
      = (binCascade (L := L) layers).run x := by
  show (binCascade (L := L + 1) (appendIdLayers layers)).runUpTo (L + 1) x = _
  rw [MuxCascade.runUpTo, dif_pos (by omega : L < L + 1)]
  -- last layer is binIdLayer, acts as identity
  have hlast : (binCascade (L := L + 1) (appendIdLayers layers)).layers ⟨L, by omega⟩
      = binIdLayer 1 := by
    show appendIdLayers layers ⟨L, by omega⟩ = binIdLayer 1
    rw [appendIdLayers, dif_neg (by simp)]
  rw [hlast]
  -- runUpTo L of the appended cascade equals runUpTo L of the original = run of the original
  have hpre := appendId_runUpTo_eq layers x L (le_refl L)
  rw [hpre]
  -- the identity layer leaves the state unchanged
  show (binIdLayer 1).applyLayer _ ((binCascade (L := L) layers).runUpTo L x)
      = (binCascade (L := L) layers).run x
  rw [binIdLayer_applyLayer]
  rfl

/-- **DEPTH-MONOTONE EMBEDDING `binGrade L ⊆ binGrade (L+1)`.** A depth-`L` arity-2 route is a
depth-`(L+1)` arity-2 route: append a do-nothing identity layer (`appendId_run_eq` keeps the output
fixed). Generalizes the base `muxCascadeGrade_zero_subset_one` from `0 ↪ 1` to all `L ↪ L+1`. -/
theorem binCascadeGrade_succ_subset {k L : ℕ} (hk : 0 < k) :
    binCascadeGrade 1 k L hk ⊆ binCascadeGrade 1 k (L + 1) hk := by
  rintro f ⟨layers, rs, rfl⟩
  refine ⟨appendIdLayers layers, rs, ?_⟩
  funext x
  simp only [cascadeRoute]
  rw [appendId_run_eq layers x]

/-! ### (8b) The strict separation atom `binGrade 1 ⊂ binGrade 2` -/

/-- **THE STRICT SEPARATION ATOM (the depth-ladder rung beyond the base).**
`binCascadeGrade 1 2 1 ⊂ binCascadeGrade 1 2 2`. The `⊆` is the depth-monotone identity-layer
embedding (`binCascadeGrade_succ_subset`); the strictness is the high-alternation witness:
`tentRoute` lies in grade 2 (`tentRoute_mem_binGradeTwo`) but NOT in grade 1
(`tentRoute_not_mem_binGradeOne`, via the region-count ⇒ alternation-bound crux). Each added layer
strictly enlarges the realizable arity-2 route class — depth genuinely buys expressivity, ONE RUNG
ABOVE the base `grade 0 ⊂ grade 1`, PROVED with the right tool (the alternation bound, not convexity:
grade-1 routes are already non-convex). -/
theorem binCascadeGrade_one_ssubset_two :
    binCascadeGrade 1 2 1 (by norm_num) ⊂ binCascadeGrade 1 2 2 (by norm_num) := by
  refine ⟨binCascadeGrade_succ_subset (by norm_num), ?_⟩
  intro hsubset
  -- equality would force tentRoute (grade 2) into grade 1
  have h2 : tentRoute ∈ binCascadeGrade 1 2 2 (by norm_num) := tentRoute_mem_binGradeTwo
  have h1 : tentRoute ∈ binCascadeGrade 1 2 1 (by norm_num) := hsubset h2
  exact tentRoute_not_mem_binGradeOne h1

/-!
## The general `∀L` obstruction (precise)

The `L = 1` crux closes because `trace_no_ABA_depth_one` holds: at depth 1 the trace along the carrier
line is a SINGLE affine threshold (`binCascade_depthOne_trace_threshold`), so it switches at most once,
forcing a fiber of `≥ 3` consecutive sample points. The analogous step FAILS for `L ≥ 2`:

* At depth `2` the layer-1 gate is evaluated at `runUpTo 1 y`, which is the (piecewise-affine) output
  of the layer-0 fold — NOT the raw coordinate. So the layer-1 trace bit, as a function of `t ∈ ℝ`, is
  a threshold COMPOSED with a fold, which can switch up to twice. The trace (now a pair of bits) can
  switch up to `3` times along the line, giving up to `4 = ∏ arity` trace blocks — consistent with
  `muxCascade_pieces_le_prod` but no longer "≤ 1 switch".

* Consequently the clean pigeonhole ("a fiber of `≥ 3` consecutive points exists") is unavailable, and
  there is no analogue of `trace_no_ABA_depth_one` for `L ≥ 2`.

The missing GENERAL infrastructure is the full piecewise-linear piece-count calculus: (i) the argmax of
`n` affine functions of one real variable partitions `ℝ` into `≤ n` intervals; (ii) PWL composition
multiplies piece counts; whence the trace switches `≤ ∏ arity − 1` times and
`alternations ≤ 2 · pieceCount ≤ 2 · ∏ arity` for ALL `L`. With that calculus the `∀L` ladder
`binGrade L ⊂ binGrade (L+1)` would follow by the iterated-fold witness (each extra fold doubles the
alternation count). This is left as future work; the affine-on-fiber and fiber-threshold links built
here are exactly the depth-uniform pieces such a proof reuses.
-/

end TLT.TemperedDesignLaw.MuxHierarchy

-- Axiom audit (must be {propext, Classical.choice, Quot.sound}):
-- #print axioms TLT.TemperedDesignLaw.MuxHierarchy.binCascadeGrade_one_ssubset_two
-- #print axioms TLT.TemperedDesignLaw.MuxHierarchy.binCascade_depthOne_no_full_alternation
-- #print axioms TLT.TemperedDesignLaw.MuxHierarchy.tentRoute_not_mem_binGradeOne
-- #print axioms TLT.TemperedDesignLaw.MuxHierarchy.MuxCascade.run_eq_on_fiber
