/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.QuadraticDepth

/-!
# The iterated quadratic tent and the general-`L` second-order depth-separation OBSTRUCTION

This file targets the general-`L` second-order depth separation
`quadDepthGrade 1 2 L ⊂ quadDepthGrade 1 2 (L+1)` for every `L`, the documented next step after the
base rung `quadDepthGrade_zero_ssubset_one` (`QuadraticDepth.lean`). It mirrors the affine depth
ladder `MuxDepthLadderGeneral.lean`, which closes the analogous separation with an iterated affine
tent achieving `2^L` route alternations against the affine route ceiling `2^{L+1} − 1`.

## What is proved here (sorry-free)

* `quadTentLayer : QuadMuxLayer 1` — a quadratic-gated layer whose carrier action is the tent fold
  `Λ(s) = 1 − |2s − 1|`. The gate is the quadratic score `s ↦ (2s − 1)²`'s comparison against a
  threshold (equivalently the affine threshold `2s − 1 ≥ 0` realized through a degenerate quadratic),
  and the two affine branches are the up/down halves of the tent. It is the affine `upTentLayer`
  re-expressed inside the quadratic-gated layer type.

* `quadTentCascade (L : ℕ) : QuadCascade 1 L` — iterate it (mirror of `upTentCascade`).

* `quadTentCascade_run_coord`, `quadTentRoute_eq`, `quadTentRoute_on_grid` — the iterated run is
  `tentMap^[L]`, and the route on the dyadic grid is the parity `1 − (j mod 2)`.

* `quadTentRoute_alternations_eq : seqChanges (route of quadTentCascade L on the dyadic grid) = 2^L`
  — the iterated quadratic tent achieves EXACTLY `2^L` route alternations (the base-2, NOT base-3,
  fold rate), proved exactly as `upTentRoute_alternations_eq`.

## Why the general-`L` separation does NOT close with this layer model (the obstruction, now QUANTIFIED)

The separation `quadDepthGrade 1 2 L ⊂ quadDepthGrade 1 2 (L+1)` would require a depth-`(L+1)`
quadratic-cascade witness whose route alternates `≥ 3^{L+1}` times (to exceed the depth-`L` route
ceiling `quadRoute_alternations_le ≤ 3^{L+1} − 1`). The iterated tent built here alternates only
`2^{L+1}` times at depth `L+1`, and for `L ≥ 1` we have `2^{L+1} < 3^{L+1} − 1`
(`quadTent_alternations_below_ceiling` below), so the tent route lies INSIDE grade `L`, not outside
it. The construction therefore does NOT separate the quadratic grades at any rung beyond the base
`L = 0` (where `2^{0+1} = 2 = 3^{0+1} − 1` is exactly the boundary already exploited by
`quadDepthGrade_zero_ssubset_one`).

This is forced by the layer type, not by a weak witness:

* A `QuadMuxLayer 1` gate is a binary `leastArgmax` of `2` quadratic scores (`QuadMuxLayer.gate :
  … → Fin 2`), so each layer uses at most **two** distinct affine branch maps.

* A quadratic gate `0 < A t² + B t + C` (with `A < 0`) holds exactly on one interval `(r₁, r₂)`,
  splitting the line into three regions `(−∞, r₁]`, `[r₁, r₂]`, `[r₂, ∞)`; this is the ≤ 2 gate
  switches giving the per-layer multiplier `3` in the BOUND `quadRoute_alternations_le ≤ 3^{L+1} − 1`.

* But the OUTER two regions select the SAME branch (`branch 0`), so the per-layer carrier map uses
  only two distinct affine maps. An injective affine `branch 0` cannot map both `[0, r₁]` and
  `[r₂, 1]` ONTO `[0, 1]`: if it covers the first lap (slope chosen so `branch 0(0) = 0`,
  `branch 0(r₁) = 1`), then on `[r₂, 1]` it outputs values `> 1`, so the third lap escapes `[0, 1]`
  and does not iterate. The achievable per-layer FOLD FACTOR is therefore `2`, not `3`, and the
  iterable witness achieves `2^L`, never `3^{L+1}`.

So the bound `3^{L+1} − 1` is correct but NOT tight for an iterable witness in this layer type.
Closing the general-`L` separation needs a richer per-layer model — e.g. an arity-3 quadratic gate
(`Fin 3` branches gated by two quadratic thresholds) so all three covering laps use distinct affine
maps and the fold factor is genuinely `3`. The pieces built here (the iterated-tent run identity, the
dyadic route identity, the exact `2^L` alternation count) are precisely the depth-uniform machinery
such a proof reuses; only the per-layer arity must be lifted from `2` to `3`.
-/

open scoped BigOperators
open Set

noncomputable section

open Classical

namespace TLT.TemperedDesignLaw

open TLT.TemperedDesignLaw.MuxHierarchy

/-! ## (1) The quadratic tent layer and its cascade -/

/-- **The quadratic tent layer.** Carrier action is the tent fold `Λ(s) = 1 − |2s − 1|`.

The gate distinguishes the two halves of the tent by a quadratic comparison: `score 0 = 0` and
`score 1 = -(2s − 1)² = -(4 s² − 4 s + 1)`. Thus `gate = 0` iff `score 1 ≤ score 0`, i.e. iff
`-(2s−1)² ≤ 0`, which holds for ALL `s`; we instead split the tent by reusing the affine threshold via
the branch geometry, mirroring `upTentLayer`'s `2s − 1 ≥ 0` split. To keep the gate genuinely binary
and matched to the up/down split we use `score 1 = 2s − 1` and `score 0 = 0` as a degenerate quadratic
(`M = 0`), exactly the affine `upTentLayer` re-typed: gate `0` iff `2s − 1 ≤ 0`. -/
def quadTentLayer : QuadMuxLayer 1 where
  scores := fun i => if i = 0 then QuadScore.zero 1
                              else ⟨fun _ _ => 0, fun _ => 2, -1⟩
  branches := fun i => if i = 0 then ⟨fun _ _ => 2, fun _ => 0⟩
                                else ⟨fun _ _ => -2, fun _ => 2⟩

/-- The depth-`L` iterated quadratic tent cascade. -/
def quadTentCascade (L : ℕ) : QuadCascade 1 L := QuadCascade.mk (fun _ => quadTentLayer)

/-- The two gate scores of the tent layer at `![s]`: `0` and `2s − 1`. -/
theorem quadTentLayer_scores (s : ℝ) :
    (quadTentLayer.scores 0).eval (fun _ => s) = 0 ∧
    (quadTentLayer.scores 1).eval (fun _ => s) = 2 * s - 1 := by
  refine ⟨?_, ?_⟩
  · show (quadTentLayer.scores 0).eval (fun _ => s) = 0
    have : quadTentLayer.scores 0 = QuadScore.zero 1 := by simp [quadTentLayer]
    rw [this]; simp
  · show (quadTentLayer.scores 1).eval (fun _ => s) = 2 * s - 1
    have : quadTentLayer.scores 1 = (⟨fun _ _ => 0, fun _ => 2, -1⟩ : QuadScore 1) := by
      simp [quadTentLayer]
    rw [this, QuadScore.eval_coord1]; ring

/-- The tent layer's gate: `0` iff `2s − 1 ≤ 0` (i.e. `s ≤ ½`), else `1`. -/
theorem quadTentLayer_gate (s : ℝ) :
    quadTentLayer.gate (fun _ => s) = if 2 * s - 1 ≤ 0 then 0 else 1 := by
  simp only [QuadMuxLayer.gate]; rw [leastArgmax_two]
  obtain ⟨h0, h1⟩ := quadTentLayer_scores s
  simp only [h0, h1]

/-- The tent layer's carrier action is `tentMap`: `s ↦ 1 − |2s − 1|`.

For `s ≤ ½` (gate `0`) the branch is `s ↦ 2s`; for `s > ½` (gate `1`) the branch is `s ↦ 2 − 2s`.
Both equal `1 − |2s − 1|`. -/
theorem quadTentLayer_apply (s : ℝ) :
    (quadTentLayer.applyLayer (fun _ => s)) 0 = tentMap s := by
  simp only [QuadMuxLayer.applyLayer, quadTentLayer_gate, tentMap]
  by_cases hx : 2 * s - 1 ≤ 0
  · rw [if_pos hx]
    show ((quadTentLayer.branches 0).apply (fun _ => s)) 0 = 1 - |2 * s - 1|
    have hb : quadTentLayer.branches 0 = (⟨fun _ _ => 2, fun _ => 0⟩ : AffineSelfMap 1) := by
      simp [quadTentLayer]
    rw [hb, AffineSelfMap.apply_coord1]
    rw [abs_of_nonpos hx]; ring
  · rw [if_neg hx]
    show ((quadTentLayer.branches 1).apply (fun _ => s)) 0 = 1 - |2 * s - 1|
    have hb : quadTentLayer.branches 1 = (⟨fun _ _ => -2, fun _ => 2⟩ : AffineSelfMap 1) := by
      simp [quadTentLayer]
    rw [hb, AffineSelfMap.apply_coord1]
    rw [abs_of_pos (by push Not at hx; linarith : (0:ℝ) < 2 * s - 1)]; ring

/-! ## (2) The iterated run is `tentMap^[L]` (mirror of `upTentCascade_runUpTo_coord`) -/

/-- **The iterated quadratic-tent run is the iterate of `tentMap`.** `runUpTo m` of
`quadTentCascade L` applied to `![t]` has carrier coordinate `tentMap^[m] t`. -/
theorem quadTentCascade_runUpTo_coord (L : ℕ) (t : ℝ) :
    ∀ m, m ≤ L → ((quadTentCascade L).runUpTo m (fun _ => t)) 0 = (tentMap^[m]) t := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      rw [QuadCascade.runUpTo, dif_pos (by omega : m < L)]
      show (quadTentLayer.applyLayer ((quadTentCascade L).runUpTo m (fun _ => t))) 0 = _
      have hstate : ((quadTentCascade L).runUpTo m (fun _ => t))
          = (fun _ => ((quadTentCascade L).runUpTo m (fun _ => t)) 0) := by
        funext i; fin_cases i; rfl
      rw [hstate, quadTentLayer_apply, ih (by omega), Function.iterate_succ_apply']

/-- The full run's carrier coordinate is `tentMap^[L] t`. -/
theorem quadTentCascade_run_coord (L : ℕ) (t : ℝ) :
    ((quadTentCascade L).run (fun _ => t)) 0 = (tentMap^[L]) t :=
  quadTentCascade_runUpTo_coord L t L (le_refl _)

/-! ## (3) The iterated-tent route and its value on the dyadic grid (mirror of `upTentRoute_*`) -/

/-- The iterated-tent route scores: threshold at `½` on the final coordinate (`route = 0` iff value
`≥ ½`). Identical affine readout as the affine tent. -/
def quadTentRouteScores : Fin 2 → AffineFunctional 1 :=
  fun j => if j = 0 then ⟨fun _ => 1, -(1/2)⟩ else ⟨fun _ => -1, 1/2⟩

theorem quadTentRouteScores_eval (s : Fin 1 → ℝ) :
    (quadTentRouteScores 0).eval s = s 0 - 1/2 ∧ (quadTentRouteScores 1).eval s = 1/2 - s 0 := by
  refine ⟨?_, ?_⟩
  · show (quadTentRouteScores 0).eval s = s 0 - 1/2
    have : quadTentRouteScores 0 = (⟨fun _ => 1, -(1/2)⟩ : AffineFunctional 1) := by
      simp [quadTentRouteScores]
    rw [this, AffineFunctional.eval_coord1]; ring
  · show (quadTentRouteScores 1).eval s = 1/2 - s 0
    have : quadTentRouteScores 1 = (⟨fun _ => -1, 1/2⟩ : AffineFunctional 1) := by
      simp [quadTentRouteScores]
    rw [this, AffineFunctional.eval_coord1]; ring

/-- The iterated-tent route value: `0` iff the final coordinate `≥ ½`. -/
theorem quadTentRoute_eq (L : ℕ) (t : ℝ) :
    quadCascadeRoute (quadTentCascade L) quadTentRouteScores (by norm_num) (fun _ => t)
      = if 1/2 ≤ (tentMap^[L]) t then 0 else 1 := by
  unfold quadCascadeRoute
  rw [leastArgmax_two]
  obtain ⟨h0, h1⟩ := quadTentRouteScores_eval ((quadTentCascade L).run (fun _ => t))
  simp only [h0, h1, quadTentCascade_run_coord]
  by_cases hc : (1:ℝ)/2 ≤ (tentMap^[L]) t
  · rw [if_pos (by linarith), if_pos hc]
  · rw [if_neg (by push Not at hc ⊢; linarith), if_neg hc]

/-- **The route value on the dyadic grid point `j / 2^L` is `1 − (j mod 2)`.** Via the dyadic
identity `tentMap_iterate_dyadic`: the final coordinate is `j mod 2 ∈ {0,1}`, and the threshold `≥ ½`
is met iff that value is `1` (`j` odd ⟹ route `0`); else (`j` even) route `1`. -/
theorem quadTentRoute_on_grid (L : ℕ) (j : ℕ) (hj : j ≤ 2 ^ L) :
    quadCascadeRoute (quadTentCascade L) quadTentRouteScores (by norm_num)
        (fun _ => (j : ℝ) / 2 ^ L)
      = if j % 2 = 0 then 1 else 0 := by
  rw [quadTentRoute_eq, tentMap_iterate_dyadic L j hj]
  have hmod : j % 2 = 0 ∨ j % 2 = 1 := by omega
  rcases hmod with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- The iterated-tent route along the dyadic grid, as a function of the grid index `k`. -/
theorem quadTentRoute_dyadicGrid (L : ℕ) (k : Fin (2 ^ L + 1)) :
    quadCascadeRoute (quadTentCascade L) quadTentRouteScores (by norm_num)
        (fun _ => dyadicGrid L k)
      = if k.val % 2 = 0 then 1 else 0 := by
  unfold dyadicGrid
  exact quadTentRoute_on_grid L k.val (by have := k.isLt; omega)

/-! ## (4) The exact route alternation count `= 2^L` (the base-2, NOT base-3, fold rate)

This is the quantified obstruction. The iterated quadratic tent achieves EXACTLY `2^L` route
alternations — the SAME count as the affine tent (`upTentRoute_alternations_eq`), NOT the `3^L`
that a genuine ternary fold would give. -/

/-- **THE QUADRATIC-TENT ROUTE ALTERNATION COUNT `= 2^L`.** The depth-`L` iterated quadratic-tent
route changes value at EVERY one of the `2^L` adjacent pairs of the dyadic grid (consecutive grid
indices have opposite parity), so `seqChanges = 2^L`. Proved exactly as `upTentRoute_alternations_eq`;
the carrier dynamics are identical because `quadTentLayer.applyLayer = tentMap = upTentLayer.applyLayer`
on the carrier coordinate. -/
theorem quadTentRoute_alternations_eq (L : ℕ) :
    seqChanges (fun k => quadCascadeRoute (quadTentCascade L) quadTentRouteScores (by norm_num)
        (fun _ => dyadicGrid L k)) = 2 ^ L := by
  unfold seqChanges
  have hall : (Finset.univ.filter (fun i : Fin (2 ^ L) =>
      (fun k => quadCascadeRoute (quadTentCascade L) quadTentRouteScores (by norm_num)
        (fun _ => dyadicGrid L k)) i.castSucc
      ≠ (fun k => quadCascadeRoute (quadTentCascade L) quadTentRouteScores (by norm_num)
        (fun _ => dyadicGrid L k)) i.succ)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    simp only
    rw [quadTentRoute_dyadicGrid, quadTentRoute_dyadicGrid]
    have hcs : (i.castSucc : Fin (2 ^ L + 1)).val = i.val := Fin.val_castSucc i
    have hsc : (i.succ : Fin (2 ^ L + 1)).val = i.val + 1 := Fin.val_succ i
    rw [hcs, hsc]
    rcases Nat.even_or_odd i.val with he | ho
    · obtain ⟨r, hr⟩ := he
      rw [if_pos (by omega), if_neg (by omega)]
      decide
    · obtain ⟨r, hr⟩ := ho
      rw [if_neg (by omega), if_pos (by omega)]
      decide
  rw [hall, Finset.card_univ, Fintype.card_fin]

/-! ## (5) Membership and the quantified obstruction -/

/-- The depth-`L` iterated quadratic-tent route, packaged as a route function. It lies in
`quadDepthGrade 1 2 L` by construction. -/
def quadTentRouteFn (L : ℕ) : (Fin 1 → ℝ) → Fin 2 :=
  quadCascadeRoute (quadTentCascade L) quadTentRouteScores (by norm_num)

theorem quadTentRouteFn_mem_grade (L : ℕ) :
    quadTentRouteFn L ∈ quadDepthGrade 1 2 L (by norm_num) :=
  ⟨fun _ => quadTentLayer, quadTentRouteScores, rfl⟩

/-- Helper: `2^{n+2} + 2 ≤ 3^{n+2}` for all `n` (i.e. `2^{L+1} + 2 ≤ 3^{L+1}` for `L ≥ 1`). -/
private theorem two_pow_add_two_le_three_pow (n : ℕ) :
    2 ^ (n + 2) + 2 ≤ 3 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h2 : 2 ^ (k + 1 + 2) = 2 * 2 ^ (k + 2) := by rw [pow_succ]; ring
      have h3 : 3 ^ (k + 1 + 2) = 3 * 3 ^ (k + 2) := by rw [pow_succ]; ring
      have hpow : (1 : ℕ) ≤ 3 ^ (k + 2) := Nat.one_le_pow _ _ (by norm_num)
      rw [h2, h3]; omega

/-- **THE QUANTIFIED OBSTRUCTION.** For `L ≥ 1`, the depth-`(L+1)` iterated quadratic-tent route
alternates `2^{L+1}` times, which is STRICTLY BELOW the depth-`L` route ceiling `3^{L+1} − 1`
(`quadRoute_alternations_le`). Hence this tent route does NOT exceed the ceiling and does NOT witness
`quadDepthGrade 1 2 L ⊂ quadDepthGrade 1 2 (L+1)`: a separating witness would need `≥ 3^{L+1}`
alternations, unreachable by an iterated 2-affine-branch quadratic layer (fold factor `2`, not `3`).

The gap `3^{L+1} − 1 − 2^{L+1}` is the precise quantitative obstruction; it is `0` only at `L = 0`
(`3 − 1 − 2 = 0`), the boundary already exploited by `quadDepthGrade_zero_ssubset_one`. -/
theorem quadTent_alternations_below_ceiling (L : ℕ) (hL : 1 ≤ L) :
    2 ^ (L + 1) < 3 ^ (L + 1) - 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  have hsuff : 2 ^ (n + 1 + 1) + 2 ≤ 3 ^ (n + 1 + 1) := by
    have := two_pow_add_two_le_three_pow n
    simpa [show n + 1 + 1 = n + 2 from rfl] using this
  have hpow : (1 : ℕ) ≤ 3 ^ (n + 1 + 1) := Nat.one_le_pow _ _ (by norm_num)
  omega

end TLT.TemperedDesignLaw
