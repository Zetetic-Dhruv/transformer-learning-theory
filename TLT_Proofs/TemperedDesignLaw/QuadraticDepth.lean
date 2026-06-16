/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.QuadraticWidth
import TLT_Proofs.TemperedDesignLaw.MuxDepthSeparationDim

/-!
# The general-`L` DEPTH separation for QUADRATIC-gated cascades (self-attention DEPTH)

This file is the DEPTH analogue of the affine depth ladder
`binCascadeGrade_ssubset_succ` (`MuxDepthLadderGeneral.lean`) and the depth companion of the
just-landed quadratic WIDTH separation `quadWidthGrade_ssubset_succ` (`QuadraticWidth.lean`).

A **quadratic-gated cascade** is a stack where each layer's GATE is a *quadratic* score (the
self-attention low-rank bilinear form `⟨Qx,Kx⟩ = xᵀ(QᵀK)x`) and the BRANCH map is *affine* (value
mixing). The trajectory therefore stays piecewise-affine while each gate is a quadratic threshold
that switches **≤ 2** times per trajectory-piece (vs ≤ 1 for an affine gate). The depth-`L`
line-alternation bound therefore composes with a per-layer factor of **3** (each piece splits into
≤ 3 by ≤ 2 gate switches), giving a finite bound `3^L − 1` for the trace and `3^{L+1} − 1` for the
route. A *ternary-tent* witness that oscillates `3^{L+1}` times along a triadic grid separates depth
`L+1` from depth `L`.

## The five pieces

1. **`QuadMuxLayer` / `quadDepthGrade`** (the grade): a binary cascade whose per-layer GATE is the
   argmax of 2 QUADRATIC scores (`QuadScore`), branches AFFINE (`AffineSelfMap`). `quadDepthGrade L`
   = routes realizable by a depth-`L` such cascade. The `⊆` depth-monotone embedding
   (`quadDepthGrade_succ_subset`) appends a do-nothing identity layer, mirroring
   `binCascadeGrade_succ_subset`.

2. **The PER-LAYER quadratic gate bound** (`quadBitAt_block_le_two`): a quadratic gate along a
   piecewise-affine trajectory switches **≤ 2** times per piece. This is `λ₂` at arity 2:
   `QuadLines.pair_comparison_le ≤ 2`. The composition over `L` layers is the **base-3 block-refine**
   `seqChanges_blockRefine_le_two : seqChanges (u, b) ≤ 3·seqChanges u + 2`, the quadratic analogue
   of `seqChanges_blockRefine_le ≤ 2·seqChanges u + 1`.

3. **The DEPTH-`L` line bound** (`quadTrace_alternations_le ≤ 3^L − 1`,
   `quadRoute_alternations_le ≤ 3^{L+1} − 1`): compose the per-layer ≤2-switch over depth.

4. **The BASE WITNESS** (`quadWitnessLayer` + `quadWitness_alternations_eq_two`): a single quadratic
   layer (gate score `1 − t²`) whose route alternates `2` along a 3-point sample (route `0,1,0`), the
   minimal non-affine fire-in-middle behaviour.

5. **The BASE SEPARATION** (`quadDepthGrade_zero_ssubset_one`): `quadDepthGrade 0 ⊂ quadDepthGrade 1`,
   a real proved `∉` (the L=1 quadratic witness alternates 2; the L=0 grade is the bare affine argmax,
   capped at 1). The general-`L` separation `quadDepthGrade L ⊂ quadDepthGrade (L+1)` for every `L` is
   the scheduled next step: it needs a ternary-tent witness whose route achieves more than `3^{L+1}−1`
   alternations, an iterated-fold construction past this file's per-layer fold-factor obstruction
   (documented at the end of the file).
-/

open scoped BigOperators
open Set

noncomputable section

namespace TLT.TemperedDesignLaw

open TLT.TemperedDesignLaw.MuxHierarchy

/-! ## (1) The quadratic-gated, affine-branched cascade

The minimal-divergence design: a layer carries `2` QUADRATIC scores (the gate) and `2` AFFINE
branches (value mixing). The gate is the `leastArgmax` of the quadratic scores; the branch is the
selected affine self-map. Because the branches stay affine, every `runUpTo m` on a trace-fiber is a
fixed composition of affine maps (affine), so the affine-on-fiber machinery survives. Only the GATE
is quadratic; restricted to a fiber it is a `QuadLines 2` argmax of the carrier parameter `t`, landing
in the proven `QuadLines.pair_comparison_le ≤ 2` atom. -/

/-- A quadratic-gated, affine-branched arity-2 mux layer on `Fin d → ℝ`: `2` quadratic gate scores and
`2` affine branch maps. -/
structure QuadMuxLayer (d : ℕ) where
  scores : Fin 2 → QuadScore d
  branches : Fin 2 → AffineSelfMap d

/-- The branch index selected by a quadratic layer at `x`: the `leastArgmax` of its `2` quadratic
scores. -/
def QuadMuxLayer.gate {d : ℕ} (Lyr : QuadMuxLayer d) (x : Fin d → ℝ) : Fin 2 :=
  leastArgmax (fun i => (Lyr.scores i).eval x) (by norm_num)

/-- The map of a quadratic layer: gate by the argmax of the `2` quadratic scores, apply the selected
affine branch. -/
def QuadMuxLayer.applyLayer {d : ℕ} (Lyr : QuadMuxLayer d) (x : Fin d → ℝ) : Fin d → ℝ :=
  (Lyr.branches (Lyr.gate x)).apply x

/-- A depth-`L` quadratic-gated cascade: a `Fin L`-family of quadratic layers. -/
structure QuadCascade (d L : ℕ) where
  layers : Fin L → QuadMuxLayer d

/-- Run the first `m` layers of a quadratic cascade (input-first). -/
def QuadCascade.runUpTo {d L : ℕ} (C : QuadCascade d L) : ℕ → (Fin d → ℝ) → (Fin d → ℝ)
  | 0, x => x
  | (m + 1), x =>
      if h : m < L then
        (C.layers ⟨m, h⟩).applyLayer (C.runUpTo m x)
      else C.runUpTo m x

/-- The composed region map of the whole quadratic cascade: run all `L` layers. -/
def QuadCascade.run {d L : ℕ} (C : QuadCascade d L) (x : Fin d → ℝ) : Fin d → ℝ :=
  C.runUpTo L x

/-- The active-branch **trace**: for each layer `i`, the branch index it selects when run on the
state after the preceding layers. Lives in `Fin L → Fin 2`. -/
def QuadCascade.trace {d L : ℕ} (C : QuadCascade d L) (x : Fin d → ℝ) : Fin L → Fin 2 :=
  fun i => (C.layers i).gate (C.runUpTo i.val x)

/-- The `k`-way affine argmax readout of a quadratic cascade. -/
def quadCascadeRoute {d L k : ℕ} (C : QuadCascade d L) (routeScores : Fin k → AffineFunctional d)
    (hk : 0 < k) : (Fin d → ℝ) → Fin k :=
  fun x => leastArgmax (fun j => (routeScores j).eval (C.run x)) hk

/-- **The quadratic depth grade.** Routes realizable by SOME depth-`L` quadratic-gated cascade
together with SOME `k` affine route-scores. This is the quadratic (self-attention) analogue of
`binCascadeGrade`. -/
def quadDepthGrade (d k L : ℕ) (hk : 0 < k) : Set ((Fin d → ℝ) → Fin k) :=
  { f | ∃ (layers : Fin L → QuadMuxLayer d) (routeScores : Fin k → AffineFunctional d),
      f = quadCascadeRoute ⟨layers⟩ routeScores hk }

/-! ## (2) Affine-on-fiber: `C.run` is a fixed AFFINE map on each trace-fiber

The branches are affine, so on a (partial-)trace fiber `runUpTo m` is a fixed composition of
branch-selected affine self-maps. Identical to the affine `MuxCascade.prefixMap` /
`runUpTo_eq_prefixMap_on_pfiber`, with the only change being the quadratic gate (which is pinned on
the fiber). -/

/-- The fixed affine map realizing `runUpTo m` on the trace-fiber of `x₀`: at each layer `i < m` it
applies the branch that `x₀`'s trace selects. -/
def QuadCascade.prefixMap {d L : ℕ} (C : QuadCascade d L) (x₀ : Fin d → ℝ) :
    ℕ → AffineSelfMap d
  | 0 => AffineSelfMap.id d
  | (m + 1) =>
      if h : m < L then
        (C.layers ⟨m, h⟩).branches (C.trace x₀ ⟨m, h⟩) |>.comp (C.prefixMap x₀ m)
      else C.prefixMap x₀ m

/-- The fixed affine self-map agreeing with `C.run` on the trace-fiber of `x₀`. -/
def QuadCascade.fiberMap {d L : ℕ} (C : QuadCascade d L) (x₀ : Fin d → ℝ) : AffineSelfMap d :=
  C.prefixMap x₀ L

/-- The **partial-trace fiber** predicate: `y` and `x₀` select the same branch at every layer `< m`. -/
def QuadCascade.PFiber {d L : ℕ} (C : QuadCascade d L) (x₀ y : Fin d → ℝ) (m : ℕ) : Prop :=
  ∀ i : Fin L, i.val < m → C.trace y i = C.trace x₀ i

/-- **PARTIAL affine-on-fiber.** On the partial-trace fiber of `x₀` (first `m` bits fixed),
`runUpTo m y = (prefixMap x₀ m).apply y`. -/
theorem QuadCascade.runUpTo_eq_prefixMap_on_pfiber {d L : ℕ} (C : QuadCascade d L)
    (x₀ y : Fin d → ℝ) :
    ∀ m, C.PFiber x₀ y m → C.runUpTo m y = (C.prefixMap x₀ m).apply y := by
  intro m
  induction m with
  | zero => intro _; simp [QuadCascade.runUpTo, QuadCascade.prefixMap]
  | succ m ih =>
      intro hpf
      rw [QuadCascade.runUpTo, QuadCascade.prefixMap]
      by_cases h : m < L
      · rw [dif_pos h, dif_pos h]
        have hpf_m : C.PFiber x₀ y m := fun i hi => hpf i (Nat.lt_succ_of_lt hi)
        rw [AffineSelfMap.comp_apply, ← ih hpf_m]
        have hgate : (C.layers ⟨m, h⟩).gate (C.runUpTo m y) = C.trace x₀ ⟨m, h⟩ := by
          have hbit : C.trace y ⟨m, h⟩ = C.trace x₀ ⟨m, h⟩ := hpf ⟨m, h⟩ (Nat.lt_succ_self m)
          simpa [QuadCascade.trace] using hbit
        simp only [QuadMuxLayer.applyLayer, hgate]
      · rw [dif_neg h, dif_neg h]
        exact ih (fun i hi => hpf i (Nat.lt_succ_of_lt hi))

/-- **FULL affine-on-fiber.** `C.run` agrees with the fixed affine map `C.fiberMap x₀` on the whole
trace-fiber of `x₀`. -/
theorem QuadCascade.run_eq_on_fiber {d L : ℕ} (C : QuadCascade d L) (x₀ y : Fin d → ℝ)
    (hfib : C.trace y = C.trace x₀) :
    C.run y = (C.fiberMap x₀).apply y := by
  rw [QuadCascade.run, QuadCascade.fiberMap]
  apply C.runUpTo_eq_prefixMap_on_pfiber x₀ y L
  intro i _; rw [hfib]

/-! ## (3) The geometric bridge: a quadratic gate through a fixed affine map is a `QuadLines 2` argmax

This is the SINGLE new geometric ingredient vs. the affine ladder. On `Fin 1 → ℝ`, a quadratic score
`s : QuadScore 1` evaluated at `A.apply (fun _ => t)` is a *quadratic in* `t` (since `QuadScore.eval`
is quadratic in the coordinate and `A` acts affinely on it). Hence the gate
`Lyr.gate (A.apply (fun _ => t))`, as a function of `t`, is `g.arg` for an explicit `QuadLines 2`. -/

/-- A quadratic score on `Fin 1 → ℝ` evaluates at the single coordinate as
`eval x = M·(x 0)² + a·(x 0) + b`. -/
theorem QuadScore.eval_coord1 (s : QuadScore 1) (x : Fin 1 → ℝ) :
    s.eval x = s.M 0 0 * (x 0)^2 + s.a 0 * (x 0) + s.b := by
  simp only [QuadScore.eval, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  ring

/-- **THE GEOMETRIC BRIDGE.** Given an arity-2 quadratic layer `Lyr` and a fixed affine self-map `A`
on `Fin 1 → ℝ`, the gate bit `Lyr.gate (A.apply (fun _ => t))`, as a function of `t`, is `g.arg` for
the explicit `QuadLines 2` `g` obtained by composing each quadratic score with `A`'s coordinate action
`t ↦ A.mat 0 0 · t + A.shift 0`. -/
theorem quadGate_comp_affine_eq_arg (Lyr : QuadMuxLayer 1) (A : AffineSelfMap 1) (t : ℝ) :
    Lyr.gate (A.apply (fun _ => t))
      = (QuadLines.mk
          (fun j => (Lyr.scores j).M 0 0 * (A.mat 0 0)^2)
          (fun j => 2 * (Lyr.scores j).M 0 0 * A.mat 0 0 * A.shift 0
                      + (Lyr.scores j).a 0 * A.mat 0 0)
          (fun j => (Lyr.scores j).M 0 0 * (A.shift 0)^2
                      + (Lyr.scores j).a 0 * A.shift 0 + (Lyr.scores j).b)).arg
          (by norm_num) t := by
  unfold QuadMuxLayer.gate QuadLines.arg
  congr 1
  funext j
  rw [QuadScore.eval_coord1]
  have hc : (A.apply (fun _ => t)) 0 = A.mat 0 0 * t + A.shift 0 := by
    rw [AffineSelfMap.apply_coord1]
  rw [hc]
  show (Lyr.scores j).M 0 0 * (A.mat 0 0 * t + A.shift 0)^2
        + (Lyr.scores j).a 0 * (A.mat 0 0 * t + A.shift 0) + (Lyr.scores j).b
      = (QuadLines.mk _ _ _).val j t
  unfold QuadLines.val
  ring

/-! ## (4) The PER-LAYER quadratic gate bound: `QuadLines 2` argmax flips ≤ 2 (piece ii)

The arity-2 specialization of the order-2 (Davenport–Schinzel) per-pair bound: the argmax of TWO
parabolas changes value **at most 2** times along any increasing sample. This is `λ₂` at arity 2 (the ≤2-per-pair from `QuadLines.pair_comparison_le`), the quadratic analogue of the
affine `affineArg_two_alternations_le ≤ 1`. It is what makes the per-layer multiplier `3` instead of
`2`. -/

/-- **THE PER-LAYER ≤2 BOUND.** For `QuadLines 2`, the active index `arg = leastArgmax (val 0, val 1)`
changes value at most `2` times along any increasing sample. Reason: `arg t = 1 ↔ val 0 t < val 1 t`
(by `leastArgmax_two`), so `arg` equals the strict comparison indicator, which `pair_comparison_le`
caps at `2`. -/
theorem QuadLines.arg_two_alternations_le (g : QuadLines 2) {m : ℕ}
    (pts : Fin (m + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => g.arg (by norm_num) (pts k)) ≤ 2 := by
  -- arg = the comparison indicator `[val 0 < val 1]`
  have hcongr : (fun k => g.arg (by norm_num) (pts k))
      = (fun k => if g.val 0 (pts k) < g.val 1 (pts k) then (1 : Fin 2) else 0) := by
    funext k
    unfold QuadLines.arg
    rw [leastArgmax_two]
    by_cases h : g.val 0 (pts k) < g.val 1 (pts k)
    · rw [if_pos h, if_neg (by linarith)]
    · rw [if_neg h, if_pos (by linarith)]
  rw [hcongr]
  exact g.pair_comparison_le 0 1 pts hinc

/-! ## (5) The base-3 block-refine: adding one ≤2-flipping binary bit at most triples (+2) changes

The combinatorial engine of the quadratic `∀L` ladder, replacing the affine `×2 + 1`
`seqChanges_blockRefine_le` with `×3 + 2`. Where the affine bit has block **no-return** (flips ≤ 1
per `u`-block), the quadratic bit has block **no-return-for-some-value** (flips ≤ 2 per `u`-block,
the `λ₂` order-2 phenomenon). The `blockOf` map is therefore at-most-**2**-to-1 (not 1-to-1) on the
`b`-only flips, giving `|Bonly| ≤ 2·(|U| + 1)` and `seqChanges (u,b) ≤ |U| + |Bonly| ≤ 3·|U| + 2`. -/

/-- The number of `u`-changes strictly before position `i`: the index of the `u`-block containing the
pair `(i.castSucc, i.succ)`. (Same as the affine `blockOf`.) -/
def blockOf2 {A : Type*} [DecidableEq A] {m : ℕ} (u : Fin (m + 1) → A) (i : Fin m) : ℕ :=
  (Finset.univ.filter (fun j : Fin m => j < i ∧ u j.castSucc ≠ u j.succ)).card

/-- **`u` is constant on the index interval `[i.castSucc, i'.succ]`** whenever `i < i'` are two
indices in the same `u`-block (`blockOf2 u i = blockOf2 u i'`), i.e. there is no `u`-change strictly
between them. Extracted verbatim from the affine `seqChanges_blockRefine_le`. -/
theorem u_const_on_block {A : Type*} [DecidableEq A] {m : ℕ} (u : Fin (m + 1) → A)
    (i i' : Fin m) (hlt : i < i') (_hiu : u i.castSucc = u i.succ) (hi'u : u i'.castSucc = u i'.succ)
    (hbi : blockOf2 u i = blockOf2 u i') :
    ∀ e, i.castSucc ≤ e → e ≤ i'.succ → u e = u i.castSucc := by
  -- no u-change in [i, i')
  have hno_uchange : ∀ j : Fin m, i ≤ j → j < i' → u j.castSucc = u j.succ := by
    intro j hij hji'
    by_contra hjc
    have hjlt_i' : j ∈ Finset.univ.filter (fun l : Fin m => l < i' ∧ u l.castSucc ≠ u l.succ) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji', hjc⟩
    have hjnlt_i : j ∉ Finset.univ.filter (fun l : Fin m => l < i ∧ u l.castSucc ≠ u l.succ) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
      intro hjlt _; exact absurd hjlt (not_lt.mpr hij)
    have hsubset : Finset.univ.filter (fun l : Fin m => l < i ∧ u l.castSucc ≠ u l.succ)
        ⊆ Finset.univ.filter (fun l : Fin m => l < i' ∧ u l.castSucc ≠ u l.succ) := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      exact ⟨lt_trans hl.1 hlt, hl.2⟩
    have heqset := Finset.eq_of_subset_of_card_le hsubset (by rw [← blockOf2, ← blockOf2, hbi])
    rw [heqset] at hjnlt_i
    exact hjnlt_i hjlt_i'
  -- extend to j ≤ i'
  have hno_uchange' : ∀ j : Fin m, i ≤ j → j ≤ i' → u j.castSucc = u j.succ := by
    intro j hij hji'
    rcases lt_or_eq_of_le hji' with h | h
    · exact hno_uchange j hij h
    · rw [h]; exact hi'u
  -- u constant on [i.castSucc, i'.succ]
  suffices H : ∀ pv : ℕ, ∀ hpv : pv < m + 1, i.castSucc ≤ (⟨pv, hpv⟩ : Fin (m+1)) →
      (⟨pv, hpv⟩ : Fin (m+1)) ≤ i'.succ → u ⟨pv, hpv⟩ = u i.castSucc by
    intro e he1 he2; obtain ⟨ev, hev⟩ := e; exact H ev hev he1 he2
  intro pv hpv hp1 hp2
  induction pv with
  | zero =>
      have : i.castSucc = (⟨0, hpv⟩ : Fin (m+1)) :=
        le_antisymm (by simpa [Fin.le_def] using hp1) (Fin.zero_le _)
      rw [← this]
  | succ k ih =>
      by_cases hik : i.castSucc ≤ (⟨k, Nat.lt_of_succ_lt hpv⟩ : Fin (m+1))
      · have hk2 : (⟨k, Nat.lt_of_succ_lt hpv⟩ : Fin (m+1)) ≤ i'.succ := by
          simp only [Fin.le_def] at hp2 ⊢; omega
        have hkm : k < m := by
          simp only [Fin.le_def, Fin.val_succ] at hp2; omega
        have hjmem : i ≤ (⟨k, hkm⟩ : Fin m) := by
          simp only [Fin.le_def, Fin.val_castSucc] at hik ⊢; exact hik
        have hjle : (⟨k, hkm⟩ : Fin m) ≤ i' := by
          simp only [Fin.le_def, Fin.val_succ] at hp2 ⊢; omega
        have hadjk := hno_uchange' ⟨k, hkm⟩ hjmem hjle
        have hcs : (⟨k, hkm⟩ : Fin m).castSucc = (⟨k, Nat.lt_of_succ_lt hpv⟩ : Fin (m+1)) :=
          Fin.ext rfl
        have hsc : (⟨k, hkm⟩ : Fin m).succ = (⟨k + 1, hpv⟩ : Fin (m+1)) :=
          Fin.ext rfl
        rw [hcs, hsc] at hadjk
        rw [← hadjk]
        exact ih (Nat.lt_of_succ_lt hpv) hik hk2
      · have : i.castSucc = (⟨k + 1, hpv⟩ : Fin (m+1)) := by
          apply le_antisymm hp1
          simp only [Fin.le_def] at hik hp1 ⊢; push Not at hik; omega
        rw [← this]

/-- A `Finset` whose every fiber under a map `φ` has card ≤ 2 has card ≤ `2 * (image φ).card`. -/
theorem card_le_two_mul_image {α β : Type*} [DecidableEq α] [DecidableEq β] (S : Finset α) (φ : α → β)
    (hfib : ∀ q : β, (S.filter (fun a => φ a = q)).card ≤ 2) :
    S.card ≤ 2 * (S.image φ).card := by
  classical
  -- S is the disjoint union of its fibers over the image
  have hpart : S.card = ∑ q ∈ S.image φ, (S.filter (fun a => φ a = q)).card := by
    rw [← Finset.card_eq_sum_card_fiberwise (fun a ha => Finset.mem_image_of_mem φ ha)]
  rw [hpart]
  calc ∑ q ∈ S.image φ, (S.filter (fun a => φ a = q)).card
      ≤ ∑ _q ∈ S.image φ, 2 := Finset.sum_le_sum (fun q _ => hfib q)
    _ = 2 * (S.image φ).card := by rw [Finset.sum_const, smul_eq_mul]; ring

/-- **THE BASE-3 BLOCK-REFINE BOUND.** Let `u : Fin(m+1)→A`, `b : Fin(m+1)→Fin 2`, and suppose `b` has
the **block no-return-for-some-value** property: on any index interval `[a,d]` on which `u` is
constant, there is a value `c` whose `b`-fiber inside `[a,d]` is no-return (so `b` flips ≤ 2 there).
Then the paired sequence `(u, b)` changes at most `3 · seqChanges u + 2` times. This is the quadratic
analogue of `seqChanges_blockRefine_le ≤ 2·seqChanges u + 1`: the per-layer multiplier is `3`
(`3^{m+1} − 1 = 3·(3^m − 1) + 2`). -/
theorem seqChanges_blockRefine_le_two {A : Type*} [DecidableEq A] {m : ℕ}
    (u : Fin (m + 1) → A) (b : Fin (m + 1) → Fin 2)
    (hblock : ∀ a d : Fin (m + 1), a ≤ d →
      (∀ e, a ≤ e → e ≤ d → u e = u a) →
      ∃ c : Fin 2, ∀ p r s : Fin (m + 1), a ≤ p → p ≤ s → s ≤ r → r ≤ d →
        b p = c → b r = c → b s = c) :
    seqChanges (fun k => (u k, b k)) ≤ 3 * seqChanges u + 2 := by
  classical
  set U : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => u i.castSucc ≠ u i.succ) with hU
  set Bonly : Finset (Fin m) :=
    Finset.univ.filter (fun i : Fin m => u i.castSucc = u i.succ ∧ b i.castSucc ≠ b i.succ)
    with hBonly
  have hsub : (Finset.univ.filter
        (fun i : Fin m => (u i.castSucc, b i.castSucc) ≠ (u i.succ, b i.succ))) ⊆ U ∪ Bonly := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Prod.mk.injEq, not_and_or,
      Finset.mem_union, hU, hBonly] at hi ⊢
    rcases hi with hu | hb
    · exact Or.inl hu
    · by_cases huc : u i.castSucc = u i.succ
      · exact Or.inr ⟨huc, hb⟩
      · exact Or.inl huc
  -- The core: every blockOf2-fiber over Bonly has card ≤ 2, via the enter/exit decomposition.
  have hfib : ∀ q : ℕ, (Bonly.filter (fun i => blockOf2 u i = q)).card ≤ 2 := by
    intro q
    set F : Finset (Fin m) := Bonly.filter (fun i => blockOf2 u i = q) with hF
    by_contra hcon
    push Not at hcon  -- 2 < F.card
    -- card ≥ 3: pick min and max of F; they span a u-constant interval; get no-return value c.
    have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
    set lo := F.min' hFne with hlo
    set hi := F.max' hFne with hhi
    have hlo_mem : lo ∈ F := F.min'_mem hFne
    have hhi_mem : hi ∈ F := F.max'_mem hFne
    have hlo_u : u lo.castSucc = u lo.succ :=
      ((Finset.mem_filter.mp ((Finset.mem_filter.mp hlo_mem).1)).2).1
    have hhi_u : u hi.castSucc = u hi.succ :=
      ((Finset.mem_filter.mp ((Finset.mem_filter.mp hhi_mem).1)).2).1
    have hlo_q : blockOf2 u lo = q := (Finset.mem_filter.mp hlo_mem).2
    have hhi_q : blockOf2 u hi = q := (Finset.mem_filter.mp hhi_mem).2
    -- lo < hi: else F.card ≤ 1, contradicting card ≥ 3
    have hlohi : lo < hi := by
      rcases lt_or_eq_of_le (F.min'_le _ hhi_mem) with h | h
      · exact h
      · exfalso
        -- lo = hi means every element equals lo (between min'=max')
        have hall : ∀ x ∈ F, x = lo := by
          intro x hx
          have h1 : lo ≤ x := F.min'_le _ hx
          have h2 : x ≤ hi := F.le_max' _ hx
          rw [← h] at h2; exact le_antisymm h2 h1
        have : F ⊆ {lo} := fun x hx => Finset.mem_singleton.mpr (hall x hx)
        have := Finset.card_le_card this
        simp at this; omega
    have huconst : ∀ e, lo.castSucc ≤ e → e ≤ hi.succ → u e = u lo.castSucc :=
      u_const_on_block u lo hi hlohi hlo_u hhi_u (hlo_q.trans hhi_q.symm)
    have hcd : (lo.castSucc : Fin (m+1)) ≤ hi.succ := by
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; have : lo.val ≤ hi.val := le_of_lt hlohi
      omega
    obtain ⟨c, hc⟩ := hblock lo.castSucc hi.succ hcd huconst
    -- every F-element is "enter" (b succ = c) or "exit" (b castSucc = c); each ≤ 1.
    -- enter set
    set enter : Finset (Fin m) := F.filter (fun i => b i.succ = c) with hEnter
    set exit : Finset (Fin m) := F.filter (fun i => b i.castSucc = c) with hExit
    -- ordering helper: any F-element x satisfies lo.cs ≤ x.cs ≤ x.succ ≤ hi.succ
    have hFbound : ∀ x ∈ F, (lo.castSucc : Fin (m+1)) ≤ x.castSucc ∧
        (x.castSucc : Fin (m+1)) ≤ x.succ ∧ (x.succ : Fin (m+1)) ≤ hi.succ := by
      intro x hx
      have h1 : lo ≤ x := F.min'_le _ hx
      have h2 : x ≤ hi := F.le_max' _ hx
      have h1' : lo.val ≤ x.val := h1
      have h2' : x.val ≤ hi.val := h2
      refine ⟨?_, ?_, ?_⟩
      · simp only [Fin.le_def, Fin.val_castSucc]; exact h1'
      · simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega
      · simp only [Fin.le_def, Fin.val_succ]; omega
    -- F ⊆ enter ∪ exit (each flip has exactly one endpoint = c)
    have hFsub : F ⊆ enter ∪ exit := by
      intro x hx
      have hxb : b x.castSucc ≠ b x.succ :=
        ((Finset.mem_filter.mp ((Finset.mem_filter.mp hx).1)).2).2
      simp only [hEnter, hExit, Finset.mem_union, Finset.mem_filter]
      by_cases hcs : b x.castSucc = c
      · exact Or.inr ⟨hx, hcs⟩
      · refine Or.inl ⟨hx, ?_⟩
        -- b x.castSucc ≠ c; binary ⟹ b x.castSucc = other; b x.succ ≠ b x.castSucc ⟹ b x.succ = c
        have hv : ∀ z : Fin 2, z ≠ c → z.val ≠ c.val := fun z hz h => hz (Fin.ext h)
        by_contra hsucc
        apply hxb
        apply Fin.ext
        have := hv _ hcs
        have := hv _ hsucc
        have l1 : (b x.castSucc).val < 2 := (b x.castSucc).isLt
        have l2 : (b x.succ).val < 2 := (b x.succ).isLt
        have l3 : c.val < 2 := c.isLt
        omega
    -- at most one enter
    have henter1 : enter.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [hEnter, Finset.mem_filter] at hx hy
      obtain ⟨hxF, hxc⟩ := hx
      obtain ⟨hyF, hyc⟩ := hy
      by_contra hne
      -- WLOG x < y; both b succ = c; no-return ⟹ b y.castSucc = c, but y is a flip
      have hyb : b y.castSucc ≠ b y.succ :=
        ((Finset.mem_filter.mp ((Finset.mem_filter.mp hyF).1)).2).2
      have hxb : b x.castSucc ≠ b x.succ :=
        ((Finset.mem_filter.mp ((Finset.mem_filter.mp hxF).1)).2).2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · -- x < y; p = x.succ (=c), r = y.succ (=c), s = y.castSucc (middle) ⟹ b y.cs = c
        have ho1 : (lo.castSucc : Fin (m+1)) ≤ x.succ := le_trans (hFbound x hxF).1 (hFbound x hxF).2.1
        have hps : (x.succ : Fin (m+1)) ≤ y.castSucc := by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          simp only [Fin.lt_def] at hlt; omega
        have hsr : (y.castSucc : Fin (m+1)) ≤ y.succ := (hFbound y hyF).2.1
        have := hc x.succ y.succ y.castSucc ho1 hps hsr (hFbound y hyF).2.2 hxc hyc
        exact hyb (this.trans hyc.symm)
      · -- y < x; p = y.succ (=c), r = x.succ (=c), s = x.castSucc (middle) ⟹ b x.cs = c
        have ho1 : (lo.castSucc : Fin (m+1)) ≤ y.succ := le_trans (hFbound y hyF).1 (hFbound y hyF).2.1
        have hps : (y.succ : Fin (m+1)) ≤ x.castSucc := by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          simp only [Fin.lt_def] at hgt; omega
        have hsr : (x.castSucc : Fin (m+1)) ≤ x.succ := (hFbound x hxF).2.1
        have := hc y.succ x.succ x.castSucc ho1 hps hsr (hFbound x hxF).2.2 hyc hxc
        exact hxb (this.trans hxc.symm)
    -- at most one exit
    have hexit1 : exit.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [hExit, Finset.mem_filter] at hx hy
      obtain ⟨hxF, hxc⟩ := hx
      obtain ⟨hyF, hyc⟩ := hy
      by_contra hne
      have hyb : b y.castSucc ≠ b y.succ :=
        ((Finset.mem_filter.mp ((Finset.mem_filter.mp hyF).1)).2).2
      have hxb : b x.castSucc ≠ b x.succ :=
        ((Finset.mem_filter.mp ((Finset.mem_filter.mp hxF).1)).2).2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · -- x < y; p = x.cs (=c), r = y.cs (=c), s = x.succ (middle) ⟹ b x.succ = c, contradict hxb
        have ho1 : (lo.castSucc : Fin (m+1)) ≤ x.castSucc := (hFbound x hxF).1
        have hsr : (x.castSucc : Fin (m+1)) ≤ x.succ := (hFbound x hxF).2.1
        have hps : (x.succ : Fin (m+1)) ≤ y.castSucc := by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          simp only [Fin.lt_def] at hlt; omega
        have hrd : (y.castSucc : Fin (m+1)) ≤ hi.succ :=
          le_trans (hFbound y hyF).2.1 (hFbound y hyF).2.2
        have := hc x.castSucc y.castSucc x.succ ho1 hsr hps hrd hxc hyc
        exact hxb (hxc.trans this.symm)
      · -- y < x; p = y.cs (=c), r = x.cs (=c), s = y.succ (middle) ⟹ b y.succ = c, contradict hyb
        have ho1 : (lo.castSucc : Fin (m+1)) ≤ y.castSucc := (hFbound y hyF).1
        have hsr : (y.castSucc : Fin (m+1)) ≤ y.succ := (hFbound y hyF).2.1
        have hps : (y.succ : Fin (m+1)) ≤ x.castSucc := by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          simp only [Fin.lt_def] at hgt; omega
        have hrd : (x.castSucc : Fin (m+1)) ≤ hi.succ :=
          le_trans (hFbound x hxF).2.1 (hFbound x hxF).2.2
        have := hc y.castSucc x.castSucc y.succ ho1 hsr hps hrd hyc hxc
        exact hyb (hyc.trans this.symm)
    -- F.card ≤ enter.card + exit.card ≤ 2, contradicting card ≥ 3
    have : F.card ≤ 2 := by
      calc F.card ≤ (enter ∪ exit).card := Finset.card_le_card hFsub
        _ ≤ enter.card + exit.card := Finset.card_union_le _ _
        _ ≤ 2 := by omega
    omega
  -- |Bonly| ≤ 2·(image card) ≤ 2·(|U|+1)
  have hBonly_card : Bonly.card ≤ 2 * (U.card + 1) := by
    have h1 : Bonly.card ≤ 2 * (Bonly.image (blockOf2 u)).card :=
      card_le_two_mul_image Bonly (blockOf2 u) hfib
    have h2 : (Bonly.image (blockOf2 u)).card ≤ U.card + 1 := by
      have hsub2 : Bonly.image (blockOf2 u) ⊆ Finset.range (U.card + 1) := by
        intro x hx
        simp only [Finset.mem_image] at hx
        obtain ⟨i, _, rfl⟩ := hx
        simp only [Finset.mem_range]
        have hle : blockOf2 u i ≤ U.card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [hU]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.2⟩
        omega
      calc (Bonly.image (blockOf2 u)).card ≤ (Finset.range (U.card + 1)).card :=
            Finset.card_le_card hsub2
        _ = U.card + 1 := Finset.card_range _
    omega
  have htotal : seqChanges (fun k => (u k, b k)) ≤ U.card + Bonly.card := by
    unfold seqChanges
    calc _ ≤ (U ∪ Bonly).card := Finset.card_le_card hsub
      _ ≤ U.card + Bonly.card := Finset.card_union_le _ _
  have hUcard : U.card = seqChanges u := rfl
  omega

/-! ## (6) The per-block no-return-for-some-value of a `QuadLines 2` argmax (feeding the block-refine)

The geometric input to the base-3 block-refine. A `QuadLines 2` argmax `g.arg`, restricted to a
monotone sample, has the **no-return-for-some-value** property: there is a value `c` whose win-set
`{t | g.arg t = c}` is `OrdConnected` (an interval), because one of the two parabola-comparison fibers
`{D ≤ 0}` (convex case) / `{0 < D}` (concave case) is `OrdConnected` by `quad_le_set_ordConnected`.
This is the `λ₂` no-return contract: NOT a global no-return (which is false for quadratics: DS order 2
permits `a,b,a`), but a no-return for the SINGLE value whose win-set is the convex side. -/

/-- **A `QuadLines 2` argmax win-set is `OrdConnected` for one value `c`.** There is `c : Fin 2` with
`{t | g.arg t = c}` an interval. (`c = 0` when the difference `val 1 − val 0` is convex, `c = 1`
when concave.) -/
theorem QuadLines.arg2_win_ordConnected (g : QuadLines 2) :
    ∃ c : Fin 2, OrdConnected {t : ℝ | g.arg (by norm_num) t = c} := by
  set AD := g.A 1 - g.A 0 with hAD
  set BD := g.a 1 - g.a 0 with hBD
  set CD := g.c 1 - g.c 0 with hCD
  -- arg t = 0 ↔ val 1 ≤ val 0 ↔ D ≤ 0 ; arg t = 1 ↔ val 0 < val 1 ↔ 0 < D
  have hD : ∀ t, g.val 1 t - g.val 0 t = AD * t^2 + BD * t + CD := by
    intro t; simp only [QuadLines.val, hAD, hBD, hCD]; ring
  have harg0 : ∀ t, g.arg (by norm_num) t = 0 ↔ AD * t^2 + BD * t + CD ≤ 0 := by
    intro t
    unfold QuadLines.arg; rw [leastArgmax_two]
    constructor
    · intro h
      by_cases hle : g.val 1 t ≤ g.val 0 t
      · have := hD t; linarith
      · rw [if_neg hle] at h; exact absurd h (by decide)
    · intro h
      have hle : g.val 1 t ≤ g.val 0 t := by have := hD t; linarith
      rw [if_pos hle]
  have harg1 : ∀ t, g.arg (by norm_num) t = 1 ↔ 0 < AD * t^2 + BD * t + CD := by
    intro t
    unfold QuadLines.arg; rw [leastArgmax_two]
    constructor
    · intro h
      by_cases hle : g.val 1 t ≤ g.val 0 t
      · rw [if_pos hle] at h; exact absurd h (by decide)
      · push Not at hle; have := hD t; linarith
    · intro h
      have hlt : g.val 0 t < g.val 1 t := by have := hD t; linarith
      rw [if_neg (by linarith)]
  rcases le_total 0 AD with hpos | hneg
  · -- D convex: {D ≤ 0} = {arg = 0} OrdConnected
    refine ⟨0, ?_⟩
    have hoc := quad_le_set_ordConnected AD BD CD hpos
    have hset : {t : ℝ | g.arg (by norm_num) t = 0} = {t : ℝ | AD * t^2 + BD * t + CD ≤ 0} := by
      ext t; simp only [Set.mem_setOf_eq]; exact harg0 t
    rw [hset]; exact hoc
  · -- D concave: {0 < D} = {arg = 1} OrdConnected (via -D convex)
    refine ⟨1, ?_⟩
    have hoc : OrdConnected {t : ℝ | (-AD) * t^2 + (-BD) * t + (-CD) < 0} :=
      quad_lt_set_ordConnected (-AD) (-BD) (-CD) (by linarith)
    have hset : {t : ℝ | g.arg (by norm_num) t = 1} = {t : ℝ | (-AD) * t^2 + (-BD) * t + (-CD) < 0} := by
      ext t; simp only [Set.mem_setOf_eq]; rw [harg1 t]; constructor <;> intro h <;> linarith
    rw [hset]; exact hoc

/-- **THE PER-BLOCK NO-RETURN-FOR-SOME-VALUE of a `QuadLines 2` argmax along an increasing sample.**
Pulling `arg2_win_ordConnected` back along a monotone sample: there is a value `c` such that on the
sample, `arg`'s `c`-fiber is no-return (`p ≤ s ≤ r, arg p = c, arg r = c ⟹ arg s = c`). This is the
exact `∃ c, no-return` contract that `seqChanges_blockRefine_le_two` consumes per `u`-block. -/
theorem QuadLines.arg2_sample_noReturn (g : QuadLines 2) {M : ℕ} (pts : Fin (M + 1) → ℝ)
    (hinc : Increasing pts) :
    ∃ c : Fin 2, ∀ p r s : Fin (M + 1), p ≤ s → s ≤ r →
      g.arg (by norm_num) (pts p) = c → g.arg (by norm_num) (pts r) = c →
      g.arg (by norm_num) (pts s) = c := by
  obtain ⟨c, hoc⟩ := g.arg2_win_ordConnected
  refine ⟨c, ?_⟩
  intro p r s hps hsr hp hr
  rw [ordConnected_def] at hoc
  have hmono : ∀ i j : Fin (M + 1), i ≤ j → pts i ≤ pts j := by
    intro i j hij
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact le_of_lt (hinc i j h)
  have hmem := hoc (Set.mem_setOf_eq ▸ hp) (Set.mem_setOf_eq ▸ hr)
    ⟨hmono p s hps, hmono s r hsr⟩
  exact hmem

/-! ## (7) The depth-`L` trace alternation bound `≤ 3^L − 1` (piece iii, trace half)

We specialize to the carrier `d = 1`. The layer-`m` gate bit and the prefix trace mirror the affine
`binBitAt` / `binPrefixVec`; the only change is the per-layer block contract, which is now
`∃ c, no-return` (≤ 2 flips) instead of global no-return (≤ 1 flip). The base-3 block-refine then
gives the trace bound `3^L − 1`. -/

/-- The layer-`m` gate bit of a quadratic cascade `⟨layers⟩` at the real point `t` (or `0` if
`m ≥ L`). -/
def quadBitAt {L : ℕ} (layers : Fin L → QuadMuxLayer 1) (m : ℕ) (t : ℝ) : Fin 2 :=
  if h : m < L then (QuadCascade.mk layers).trace (fun _ => t) ⟨m, h⟩ else 0

/-- The **prefix** trace of `⟨layers⟩`: first `m` bits as actual values, the rest masked to `0`. -/
def quadPrefixVec {L : ℕ} (layers : Fin L → QuadMuxLayer 1) (m : ℕ) (t : ℝ) : Fin L → Fin 2 :=
  fun i => if i.val < m then (QuadCascade.mk layers).trace (fun _ => t) i else 0

/-- The prefix at `m+1` is the prefix at `m` updated with the layer-`m` bit. -/
theorem quadPrefixVec_succ_eq {L : ℕ} (layers : Fin L → QuadMuxLayer 1) (m : ℕ) (t : ℝ) :
    quadPrefixVec layers (m + 1) t
      = fun i => if i.val = m then quadBitAt layers m t else quadPrefixVec layers m t i := by
  funext i
  unfold quadPrefixVec quadBitAt
  by_cases hi : i.val = m
  · subst hi
    rw [if_pos (Nat.lt_succ_self _), if_pos rfl, dif_pos i.isLt]
  · by_cases hlt : i.val < m
    · rw [if_pos (Nat.lt_succ_of_lt hlt), if_neg hi, if_pos hlt]
    · rw [if_neg (by omega), if_neg hi, if_neg hlt]

/-- The partial-fiber from prefix-equality. -/
theorem pfiber_of_quadPrefixVec_eq {L : ℕ} (layers : Fin L → QuadMuxLayer 1)
    (m : ℕ) (t₁ t₂ : ℝ) (heq : quadPrefixVec layers m t₁ = quadPrefixVec layers m t₂) :
    (QuadCascade.mk layers).PFiber (fun _ => t₁) (fun _ => t₂) m := by
  intro i hi
  have h := congrFun heq i
  unfold quadPrefixVec at h
  rw [if_pos hi, if_pos hi] at h
  exact h.symm

/-- **THE BLOCK NO-RETURN-FOR-SOME-VALUE FOR THE NEXT QUADRATIC BIT.** On any sample interval where the
prefix is constant, the layer-`m` quadratic bit has the `∃ c, no-return` contract: on that interval
`runUpTo m` is a fixed affine map (`runUpTo_eq_prefixMap_on_pfiber`), so the bit is a `QuadLines 2`
argmax of `t` (`quadGate_comp_affine_eq_arg`), whose win-sets give a no-return value
(`arg2_sample_noReturn`). This is the quadratic analogue of `binBitAt_block_noReturn`, downgraded from
no-return (≤1) to no-return-for-some-value (≤2) per the load-bearing `QuadLines.arg_no_return`-is-false
warning. -/
theorem quadBitAt_block_le_two {L : ℕ} (layers : Fin L → QuadMuxLayer 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) (m : ℕ) :
    ∀ a d : Fin (M + 1), a ≤ d →
      (∀ e, a ≤ e → e ≤ d →
        quadPrefixVec layers m (pts e) = quadPrefixVec layers m (pts a)) →
      ∃ c : Fin 2, ∀ p r s : Fin (M + 1), a ≤ p → p ≤ s → s ≤ r → r ≤ d →
        quadBitAt layers m (pts p) = c → quadBitAt layers m (pts r) = c →
        quadBitAt layers m (pts s) = c := by
  intro a d had hconst
  set C := QuadCascade.mk layers with hC
  by_cases hm : m < L
  · set A := C.prefixMap (fun _ => pts a) m with hA
    set Lyr := layers ⟨m, hm⟩ with hLyr
    -- the fixed QuadLines 2 g realizing the bit on the block
    set g := QuadLines.mk
        (fun j => (Lyr.scores j).M 0 0 * (A.mat 0 0)^2)
        (fun j => 2 * (Lyr.scores j).M 0 0 * A.mat 0 0 * A.shift 0 + (Lyr.scores j).a 0 * A.mat 0 0)
        (fun j => (Lyr.scores j).M 0 0 * (A.shift 0)^2 + (Lyr.scores j).a 0 * A.shift 0
                    + (Lyr.scores j).b) with hg
    -- the bit at any prefix-equal-to-a point equals g.arg
    have hbit : ∀ e : Fin (M + 1),
        quadPrefixVec layers m (pts e) = quadPrefixVec layers m (pts a) →
        quadBitAt layers m (pts e) = g.arg (by norm_num) (pts e) := by
      intro e he
      have hpf : C.PFiber (fun _ => pts a) (fun _ => pts e) m :=
        pfiber_of_quadPrefixVec_eq layers m (pts a) (pts e) he.symm
      have hrun : C.runUpTo m (fun _ => pts e) = A.apply (fun _ => pts e) :=
        C.runUpTo_eq_prefixMap_on_pfiber (fun _ => pts a) (fun _ => pts e) m hpf
      unfold quadBitAt
      rw [dif_pos hm]
      have htrace : C.trace (fun _ => pts e) ⟨m, hm⟩
          = Lyr.gate (C.runUpTo m (fun _ => pts e)) := rfl
      rw [htrace, hrun]
      exact quadGate_comp_affine_eq_arg Lyr A (pts e)
    -- transfer the no-return value of g to the bit
    obtain ⟨c, hc⟩ := g.arg2_sample_noReturn pts hinc
    refine ⟨c, ?_⟩
    intro p r s hap hps hsr hrd hp hr
    -- p, r, s are all prefix-equal-to-a (within [a,d] and prefix const on [a,d])
    have hpe : quadPrefixVec layers m (pts p) = quadPrefixVec layers m (pts a) :=
      hconst p hap (le_trans hps (le_trans hsr hrd))
    have hre : quadPrefixVec layers m (pts r) = quadPrefixVec layers m (pts a) :=
      hconst r (le_trans hap (le_trans hps hsr)) hrd
    have hse : quadPrefixVec layers m (pts s) = quadPrefixVec layers m (pts a) :=
      hconst s (le_trans hap hps) (le_trans hsr hrd)
    have ep := hbit p hpe
    have er := hbit r hre
    have es := hbit s hse
    rw [ep] at hp
    rw [er] at hr
    rw [es]
    exact hc p r s hps hsr hp hr
  · -- m ≥ L: bit is constant 0, trivially no-return for c = 0
    refine ⟨0, ?_⟩
    intro p r s _ _ _ _ _ _
    unfold quadBitAt; rw [dif_neg hm]

/-- **THE PREFIX-TRACE BASE-3 BOUND.** Along any increasing sample, the first-`m`-bits prefix trace of
`⟨layers⟩` changes at most `3^m − 1` times. Induction on `m`: the prefix at `m+1` is a function of the
pair `(prefix m, bit m)`; the bit has the block `∃c`-no-return contract (`quadBitAt_block_le_two`), so
`seqChanges_blockRefine_le_two` gives `≤ 3·(3^m − 1) + 2 = 3^{m+1} − 1`. -/
theorem quadPrefixVec_alternations_le {L : ℕ} (layers : Fin L → QuadMuxLayer 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    ∀ m, seqChanges (fun k => quadPrefixVec layers m (pts k)) ≤ 3 ^ m - 1 := by
  intro m
  induction m with
  | zero =>
      have hconst : ∀ k, quadPrefixVec layers 0 (pts k) = fun _ => 0 := by
        intro k; funext i; unfold quadPrefixVec; rw [if_neg (Nat.not_lt_zero _)]
      have : seqChanges (fun k => quadPrefixVec layers 0 (pts k))
          = seqChanges (fun _ : Fin (M + 1) => (fun _ : Fin L => (0 : Fin 2))) :=
        seqChanges_congr (fun k => hconst k)
      rw [this]
      unfold seqChanges
      simp
  | succ m ih =>
      have hpair : seqChanges (fun k => quadPrefixVec layers (m + 1) (pts k))
          ≤ seqChanges (fun k => (quadPrefixVec layers m (pts k), quadBitAt layers m (pts k))) := by
        have heq : (fun k => quadPrefixVec layers (m + 1) (pts k))
            = fun k => (fun p : (Fin L → Fin 2) × Fin 2 =>
                (fun i => if i.val = m then p.2 else p.1 i))
                (quadPrefixVec layers m (pts k), quadBitAt layers m (pts k)) := by
          funext k; rw [quadPrefixVec_succ_eq]
        rw [heq]
        exact seqChanges_comp_le
          (fun k => (quadPrefixVec layers m (pts k), quadBitAt layers m (pts k)))
          (fun p : (Fin L → Fin 2) × Fin 2 => (fun i => if i.val = m then p.2 else p.1 i))
      have hbr : seqChanges (fun k => (quadPrefixVec layers m (pts k), quadBitAt layers m (pts k)))
          ≤ 3 * seqChanges (fun k => quadPrefixVec layers m (pts k)) + 2 :=
        seqChanges_blockRefine_le_two _ _
          (fun a d had hconst =>
            quadBitAt_block_le_two layers pts hinc m a d had hconst)
      have hpow : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
      calc seqChanges (fun k => quadPrefixVec layers (m + 1) (pts k))
          ≤ 3 * seqChanges (fun k => quadPrefixVec layers m (pts k)) + 2 := le_trans hpair hbr
        _ ≤ 3 * (3 ^ m - 1) + 2 := by omega
        _ = 3 ^ (m + 1) - 1 := by rw [pow_succ]; omega

/-- **THE TRACE ALTERNATION BOUND `≤ 3^L − 1`.** The full active-branch trace of `⟨layers⟩` (as a
function of the carrier coordinate) changes at most `3^L − 1` times along any increasing sample. The
quadratic (base-3) analogue of `binTrace_alternations_le ≤ 2^L − 1`. -/
theorem quadTrace_alternations_le {L : ℕ} (layers : Fin L → QuadMuxLayer 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => (QuadCascade.mk layers).trace (fun _ => pts k)) ≤ 3 ^ L - 1 := by
  have hL := quadPrefixVec_alternations_le layers pts hinc L
  have heq : (fun k => quadPrefixVec layers L (pts k))
      = fun k => (QuadCascade.mk layers).trace (fun _ => pts k) := by
    funext k; funext i; unfold quadPrefixVec; rw [if_pos i.isLt]
  rw [heq] at hL
  exact hL

/-! ## (8) The route alternation bound `≤ 3^{L+1} − 1` (piece iii, route half)

One more block-refine on top of the trace. On a full-trace fiber the run is the fixed affine map
`fiberMap`, so the route is the affine-argmax of the (affine) readout scores through it, packaged as a
degenerate `QuadLines 2` (leading coeff `0`). Its `∃c`-no-return contract feeds the base-3
block-refine, adding one more `×3 + 2`: `3·(3^L − 1) + 2 = 3^{L+1} − 1`. -/

/-- The affine readout `rs` evaluated through a fixed affine map `A`, as a function of the line
parameter `t`, is `g.arg` for the (degenerate, leading-coeff-0) `QuadLines 2` `g`. -/
theorem quadRoute_comp_affine_eq_arg (rs : Fin 2 → AffineFunctional 1) (A : AffineSelfMap 1) (t : ℝ) :
    leastArgmax (fun j => (rs j).eval (A.apply (fun _ => t))) (by norm_num)
      = (QuadLines.mk
          (fun _ => (0 : ℝ))
          (fun j => (rs j).lin 0 * A.mat 0 0)
          (fun j => (rs j).lin 0 * A.shift 0 + (rs j).const)).arg (by norm_num) t := by
  unfold QuadLines.arg
  congr 1
  funext j
  rw [AffineFunctional.eval_coord1]
  have hc : (A.apply (fun _ => t)) 0 = A.mat 0 0 * t + A.shift 0 := by rw [AffineSelfMap.apply_coord1]
  rw [hc]
  show (rs j).lin 0 * (A.mat 0 0 * t + A.shift 0) + (rs j).const = (QuadLines.mk _ _ _).val j t
  unfold QuadLines.val
  ring

/-- **THE ROUTE BLOCK NO-RETURN-FOR-SOME-VALUE.** On any sample interval where the FULL trace is
constant (a single fiber), the route `quadCascadeRoute ⟨layers⟩ rs` has the `∃c`-no-return contract:
on the fiber the run is the fixed affine map `fiberMap`, so the route is a (degenerate) `QuadLines 2`
argmax of `t` (`quadRoute_comp_affine_eq_arg`), whose win-sets give a no-return value
(`arg2_sample_noReturn`). -/
theorem quadRoute_block_le_two {L : ℕ} (layers : Fin L → QuadMuxLayer 1)
    (rs : Fin 2 → AffineFunctional 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    ∀ a d : Fin (M + 1), a ≤ d →
      (∀ e, a ≤ e → e ≤ d →
        (QuadCascade.mk layers).trace (fun _ => pts e)
          = (QuadCascade.mk layers).trace (fun _ => pts a)) →
      ∃ c : Fin 2, ∀ p r s : Fin (M + 1), a ≤ p → p ≤ s → s ≤ r → r ≤ d →
        quadCascadeRoute (QuadCascade.mk layers) rs (by norm_num) (fun _ => pts p) = c →
        quadCascadeRoute (QuadCascade.mk layers) rs (by norm_num) (fun _ => pts r) = c →
        quadCascadeRoute (QuadCascade.mk layers) rs (by norm_num) (fun _ => pts s) = c := by
  intro a d had hconst
  set C := QuadCascade.mk layers with hC
  set A := C.fiberMap (fun _ => pts a) with hA
  set g := QuadLines.mk
      (fun _ => (0 : ℝ))
      (fun j => (rs j).lin 0 * A.mat 0 0)
      (fun j => (rs j).lin 0 * A.shift 0 + (rs j).const) with hg
  have hroute : ∀ e : Fin (M + 1),
      C.trace (fun _ => pts e) = C.trace (fun _ => pts a) →
      quadCascadeRoute C rs (by norm_num) (fun _ => pts e) = g.arg (by norm_num) (pts e) := by
    intro e he
    have hrun : C.run (fun _ => pts e) = A.apply (fun _ => pts e) :=
      C.run_eq_on_fiber (fun _ => pts a) (fun _ => pts e) he
    unfold quadCascadeRoute
    rw [hrun]
    exact quadRoute_comp_affine_eq_arg rs A (pts e)
  obtain ⟨c, hc⟩ := g.arg2_sample_noReturn pts hinc
  refine ⟨c, ?_⟩
  intro p r s hap hps hsr hrd hp hr
  have hpe : C.trace (fun _ => pts p) = C.trace (fun _ => pts a) :=
    hconst p hap (le_trans hps (le_trans hsr hrd))
  have hre : C.trace (fun _ => pts r) = C.trace (fun _ => pts a) :=
    hconst r (le_trans hap (le_trans hps hsr)) hrd
  have hse : C.trace (fun _ => pts s) = C.trace (fun _ => pts a) :=
    hconst s (le_trans hap hps) (le_trans hsr hrd)
  have ep := hroute p hpe
  have er := hroute r hre
  have es := hroute s hse
  rw [ep] at hp
  rw [er] at hr
  rw [es]
  exact hc p r s hps hsr hp hr

/-- **THE ROUTE ALTERNATION BOUND `≤ 3^{L+1} − 1`.** Along any increasing sample, the arity-2 route of
a depth-`L` quadratic cascade changes at most `3^{L+1} − 1` times. The route is a function of the pair
`(trace, route)`; the trace changes `≤ 3^L − 1` times (`quadTrace_alternations_le`) and the route has
the block `∃c`-no-return contract on trace-fibers (`quadRoute_block_le_two`), so
`seqChanges_blockRefine_le_two` adds one more `×3 + 2`: `≤ 3·(3^L − 1) + 2 = 3^{L+1} − 1`. This is the
quadratic (base-3) analogue of `binRoute_alternations_le ≤ 2^{L+1} − 1`. -/
theorem quadRoute_alternations_le {L : ℕ} (layers : Fin L → QuadMuxLayer 1)
    (rs : Fin 2 → AffineFunctional 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => quadCascadeRoute (QuadCascade.mk layers) rs (by norm_num) (fun _ => pts k))
      ≤ 3 ^ (L + 1) - 1 := by
  have hcomp : seqChanges (fun k => quadCascadeRoute (QuadCascade.mk layers) rs (by norm_num)
        (fun _ => pts k))
      ≤ seqChanges (fun k => ((QuadCascade.mk layers).trace (fun _ => pts k),
          quadCascadeRoute (QuadCascade.mk layers) rs (by norm_num) (fun _ => pts k))) := by
    have heq : (fun k => quadCascadeRoute (QuadCascade.mk layers) rs (by norm_num) (fun _ => pts k))
        = fun k => (fun p : (Fin L → Fin 2) × Fin 2 => p.2)
            ((QuadCascade.mk layers).trace (fun _ => pts k),
             quadCascadeRoute (QuadCascade.mk layers) rs (by norm_num) (fun _ => pts k)) := rfl
    rw [heq]
    exact seqChanges_comp_le _ (fun p : (Fin L → Fin 2) × Fin 2 => p.2)
  have hbr : seqChanges (fun k => ((QuadCascade.mk layers).trace (fun _ => pts k),
      quadCascadeRoute (QuadCascade.mk layers) rs (by norm_num) (fun _ => pts k)))
      ≤ 3 * seqChanges (fun k => (QuadCascade.mk layers).trace (fun _ => pts k)) + 2 :=
    seqChanges_blockRefine_le_two _ _
      (fun a d had hconst => quadRoute_block_le_two layers rs pts hinc a d had hconst)
  have htrace := quadTrace_alternations_le layers pts hinc
  have hpow : 1 ≤ 3 ^ L := Nat.one_le_pow _ _ (by norm_num)
  calc seqChanges (fun k => quadCascadeRoute (QuadCascade.mk layers) rs (by norm_num) (fun _ => pts k))
      ≤ 3 * seqChanges (fun k => (QuadCascade.mk layers).trace (fun _ => pts k)) + 2 :=
        le_trans hcomp hbr
    _ ≤ 3 * (3 ^ L - 1) + 2 := by omega
    _ = 3 ^ (L + 1) - 1 := by rw [pow_succ]; omega

/-! ## (9) The depth-monotone embedding `quadDepthGrade L ⊆ quadDepthGrade (L+1)` (piece i, ⊆ half)

Mirror of `binCascadeGrade_succ_subset_dim`: append a do-nothing identity quadratic layer (both
branches the identity), which keeps the output fixed. -/

/-- The do-nothing quadratic layer: all-zero gate scores, both branches the identity. Its action is
the identity regardless of the gate. -/
def quadIdLayer (d : ℕ) : QuadMuxLayer d where
  scores := fun _ => QuadScore.zero d
  branches := fun _ => AffineSelfMap.id d

@[simp] theorem quadIdLayer_applyLayer {d : ℕ} (x : Fin d → ℝ) :
    (quadIdLayer d).applyLayer x = x := by
  simp only [QuadMuxLayer.applyLayer]
  show ((quadIdLayer d).branches _).apply x = x
  have : ∀ i : Fin 2, (quadIdLayer d).branches i = AffineSelfMap.id d := fun _ => rfl
  rw [this]; exact AffineSelfMap.id_apply x

/-- The layer family obtained by APPENDING the do-nothing identity layer at the last index. -/
def appendQuadIdLayers {d L : ℕ} (layers : Fin L → QuadMuxLayer d) :
    Fin (L + 1) → QuadMuxLayer d :=
  fun i => if h : i.val < L then layers ⟨i.val, h⟩ else quadIdLayer d

/-- For `m ≤ L`, running the first `m` layers of the appended cascade equals running them on the
original cascade. -/
theorem appendQuadId_runUpTo_eq {d L : ℕ} (layers : Fin L → QuadMuxLayer d) (x : Fin d → ℝ) :
    ∀ m, m ≤ L →
      (QuadCascade.mk (appendQuadIdLayers layers)).runUpTo m x
        = (QuadCascade.mk layers).runUpTo m x := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      have hmL : m < L := by omega
      have hmL1 : m < L + 1 := by omega
      rw [QuadCascade.runUpTo, QuadCascade.runUpTo, dif_pos hmL1, dif_pos hmL]
      have hlayer : appendQuadIdLayers layers ⟨m, hmL1⟩ = layers ⟨m, hmL⟩ := by
        rw [appendQuadIdLayers, dif_pos hmL]
      have hstate := ih (by omega)
      show ((QuadCascade.mk (appendQuadIdLayers layers)).layers ⟨m, hmL1⟩).applyLayer
            ((QuadCascade.mk (appendQuadIdLayers layers)).runUpTo m x)
          = ((QuadCascade.mk layers).layers ⟨m, hmL⟩).applyLayer
            ((QuadCascade.mk layers).runUpTo m x)
      rw [hstate]
      show (appendQuadIdLayers layers ⟨m, hmL1⟩).applyLayer ((QuadCascade.mk layers).runUpTo m x)
          = (layers ⟨m, hmL⟩).applyLayer ((QuadCascade.mk layers).runUpTo m x)
      rw [hlayer]

/-- **APPEND-IDENTITY RUN INVARIANCE.** Appending the identity layer leaves the cascade output
unchanged. -/
theorem appendQuadId_run_eq {d L : ℕ} (layers : Fin L → QuadMuxLayer d) (x : Fin d → ℝ) :
    (QuadCascade.mk (appendQuadIdLayers layers)).run x = (QuadCascade.mk layers).run x := by
  show (QuadCascade.mk (appendQuadIdLayers layers)).runUpTo (L + 1) x = _
  rw [QuadCascade.runUpTo, dif_pos (by omega : L < L + 1)]
  have hlast : (QuadCascade.mk (appendQuadIdLayers layers)).layers ⟨L, by omega⟩
      = quadIdLayer d := by
    show appendQuadIdLayers layers ⟨L, by omega⟩ = quadIdLayer d
    rw [appendQuadIdLayers, dif_neg (by simp)]
  rw [hlast]
  have hpre := appendQuadId_runUpTo_eq layers x L (le_refl L)
  rw [hpre]
  show (quadIdLayer d).applyLayer ((QuadCascade.mk layers).runUpTo L x)
      = (QuadCascade.mk layers).run x
  rw [quadIdLayer_applyLayer]
  rfl

/-- **DEPTH-MONOTONE EMBEDDING `quadDepthGrade d k L ⊆ quadDepthGrade d k (L+1)`.** A depth-`L`
quadratic-gated route is realized at depth `L+1` by appending the do-nothing identity layer
(`appendQuadId_run_eq`). Mirrors `binCascadeGrade_succ_subset_dim`. -/
theorem quadDepthGrade_succ_subset {d k L : ℕ} (hk : 0 < k) :
    quadDepthGrade d k L hk ⊆ quadDepthGrade d k (L + 1) hk := by
  rintro f ⟨layers, rs, rfl⟩
  refine ⟨appendQuadIdLayers layers, rs, ?_⟩
  funext x
  simp only [quadCascadeRoute]
  rw [appendQuadId_run_eq layers x]

/-! ## (10) The base separation `quadDepthGrade 0 ⊂ quadDepthGrade 1` (pieces iii-witness, iv-base)

The general-`L` route bound `3^{L+1} − 1` is real but not tight for an iterable continuous witness:
with only 2 affine branches per layer a quadratic gate folds the unit interval into at most **2**
covering laps (the outer two of its three gate-regions share the same affine branch, so the third lap
escapes `[0,1]` and does not iterate cleanly). Hence the affine-style iterated tent achieves `2^L`
oscillations, which does NOT exceed `3^{L+1} − 1`; the general-`L` ternary-tent separation does not
close with this 2-branch layer model (see the obstruction note at the end of the file).

What DOES close, non-vacuously, is the **base rung** `grade 0 ⊂ grade 1`: a single quadratic gate
already produces a route alternating `0, 1, 0` (`seqChanges = 2`), whereas a depth-0 route (a bare
affine-argmax readout) alternates at most ONCE. The two crossings are exactly the order-2 (quadratic)
phenomenon an affine/order-1 route forbids. -/

/-- **Grade-0 route alternates ≤ 1 along any increasing sample.** A depth-0 quadratic cascade has
`run x = x`, so its arity-2 route is a bare affine-argmax of the two affine readout scores
(`leastArgmax_two`), i.e. a single affine threshold of the carrier coordinate, which flips at most
once. -/
theorem quadDepthGrade_zero_alternations_le (rs : Fin 2 → AffineFunctional 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => quadCascadeRoute (QuadCascade.mk (Fin.elim0)) rs (by norm_num)
        (fun _ => pts k)) ≤ 1 := by
  -- the route on (fun _ => pts k) is an AffineLines 2 arg (run = id at depth 0)
  set g := lineRestrictScores rs (AffineSelfMap.id 1) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) with hg
  have hroute : ∀ k, quadCascadeRoute (QuadCascade.mk (Fin.elim0)) rs (by norm_num) (fun _ => pts k)
      = g.arg (by norm_num) (pts k) := by
    intro k
    unfold quadCascadeRoute
    have hrun : (QuadCascade.mk (Fin.elim0 : Fin 0 → QuadMuxLayer 1)).run (fun _ => pts k)
        = (fun _ => pts k) := rfl
    rw [hrun]
    -- leastArgmax (rs_j (fun _ => pts k)) = g.arg via the lineEval bridge with A = id, v = 1, x₀ = 0
    have hline : (fun _ : Fin 1 => pts k)
        = (AffineSelfMap.id 1).apply (lineEval (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) (pts k)) := by
      funext i; fin_cases i
      simp [AffineSelfMap.id_apply, lineEval]
    rw [hline]
    exact argmax_comp_affine_on_line_eq_arg rs (by norm_num) (AffineSelfMap.id 1)
      (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) (pts k)
  rw [seqChanges_congr hroute]
  exact affineArg_two_alternations_le g pts hinc

/-! ### (10a) The depth-1 quadratic witness whose route is `0, 1, 0` -/

/-- The depth-1 witness layer: gate score `1 = 1 − t²` (a quadratic, `M = −1`), score `0 = 0`;
branch `1` (middle region `|t| < 1`) sends the state to the constant `5`, branch `0` (outer region
`|t| ≥ 1`) is the identity. -/
def quadWitnessLayer : QuadMuxLayer 1 where
  scores := fun i => if i = 0 then QuadScore.zero 1
                              else ⟨fun _ _ => -1, fun _ => 0, 1⟩
  branches := fun i => if i = 0 then AffineSelfMap.id 1
                                else ⟨fun _ _ => 0, fun _ => 5⟩

/-- The depth-1 witness readout: route `0` iff the final coordinate is `≤ 3`. `route 0 = s ↦ 3 − s`,
`route 1 = 0`. -/
def quadWitnessRoute : Fin 2 → AffineFunctional 1 :=
  fun j => if j = 0 then ⟨fun _ => -1, 3⟩ else ⟨fun _ => 0, 0⟩

/-- The witness layer's two gate scores at `![t]`: `0` and `1 − t²`. -/
theorem quadWitnessLayer_scores (t : ℝ) :
    (quadWitnessLayer.scores 0).eval (fun _ => t) = 0 ∧
    (quadWitnessLayer.scores 1).eval (fun _ => t) = 1 - t^2 := by
  refine ⟨?_, ?_⟩
  · show (quadWitnessLayer.scores 0).eval (fun _ => t) = 0
    have : quadWitnessLayer.scores 0 = QuadScore.zero 1 := by simp [quadWitnessLayer]
    rw [this]; simp
  · show (quadWitnessLayer.scores 1).eval (fun _ => t) = 1 - t^2
    have : quadWitnessLayer.scores 1 = (⟨fun _ _ => -1, fun _ => 0, 1⟩ : QuadScore 1) := by
      simp [quadWitnessLayer]
    rw [this, QuadScore.eval_coord1]; ring

/-- The witness layer's gate: `0` iff `1 − t² ≤ 0` (i.e. `|t| ≥ 1`), else `1`. -/
theorem quadWitnessLayer_gate (t : ℝ) :
    quadWitnessLayer.gate (fun _ => t) = if 1 - t^2 ≤ 0 then 0 else 1 := by
  simp only [QuadMuxLayer.gate]; rw [leastArgmax_two]
  obtain ⟨h0, h1⟩ := quadWitnessLayer_scores t
  simp only [h0, h1]

/-- The witness layer's carrier action: `t` when `|t| ≥ 1`, constant `5` when `|t| < 1`. -/
theorem quadWitnessLayer_apply (t : ℝ) :
    (quadWitnessLayer.applyLayer (fun _ => t)) 0 = if 1 - t^2 ≤ 0 then t else 5 := by
  simp only [QuadMuxLayer.applyLayer, quadWitnessLayer_gate]
  by_cases hx : 1 - t^2 ≤ 0
  · rw [if_pos hx, if_pos hx]
    show ((quadWitnessLayer.branches 0).apply (fun _ => t)) 0 = t
    have : quadWitnessLayer.branches 0 = AffineSelfMap.id 1 := by simp [quadWitnessLayer]
    rw [this, AffineSelfMap.id_apply]
  · rw [if_neg hx, if_neg hx]
    show ((quadWitnessLayer.branches 1).apply (fun _ => t)) 0 = 5
    have : quadWitnessLayer.branches 1 = (⟨fun _ _ => 0, fun _ => 5⟩ : AffineSelfMap 1) := by
      simp [quadWitnessLayer]
    rw [this]; simp [AffineSelfMap.apply]

/-- The depth-1 witness cascade's run coordinate. -/
theorem quadWitness_run_coord (t : ℝ) :
    ((QuadCascade.mk (fun _ : Fin 1 => quadWitnessLayer)).run (fun _ => t)) 0
      = if 1 - t^2 ≤ 0 then t else 5 := by
  show ((QuadCascade.mk (fun _ : Fin 1 => quadWitnessLayer)).runUpTo 1 (fun _ => t)) 0 = _
  rw [QuadCascade.runUpTo, dif_pos (by norm_num : (0:ℕ) < 1)]
  show (quadWitnessLayer.applyLayer ((QuadCascade.mk (fun _ : Fin 1 => quadWitnessLayer)).runUpTo 0
      (fun _ => t))) 0 = _
  rw [QuadCascade.runUpTo]
  exact quadWitnessLayer_apply t

/-- The witness readout scores: `3 − s` (route 0) and `0` (route 1). -/
theorem quadWitnessRoute_eval (s : Fin 1 → ℝ) :
    (quadWitnessRoute 0).eval s = 3 - s 0 ∧ (quadWitnessRoute 1).eval s = 0 := by
  refine ⟨?_, ?_⟩
  · show (quadWitnessRoute 0).eval s = 3 - s 0
    have : quadWitnessRoute 0 = (⟨fun _ => -1, 3⟩ : AffineFunctional 1) := by simp [quadWitnessRoute]
    rw [this]; simp [AffineFunctional.eval]; ring
  · show (quadWitnessRoute 1).eval s = 0
    have : quadWitnessRoute 1 = (⟨fun _ => 0, 0⟩ : AffineFunctional 1) := by simp [quadWitnessRoute]
    rw [this]; simp [AffineFunctional.eval]

/-- **The witness route value: `0` iff the run coordinate is `≤ 3`.** -/
theorem quadWitness_route_eq (t : ℝ) :
    quadCascadeRoute (QuadCascade.mk (fun _ : Fin 1 => quadWitnessLayer)) quadWitnessRoute
        (by norm_num) (fun _ => t)
      = if (if 1 - t^2 ≤ 0 then t else 5) ≤ 3 then 0 else 1 := by
  unfold quadCascadeRoute
  rw [leastArgmax_two]
  obtain ⟨h0, h1⟩ := quadWitnessRoute_eval
    ((QuadCascade.mk (fun _ : Fin 1 => quadWitnessLayer)).run (fun _ => t))
  simp only [h0, h1, quadWitness_run_coord]
  by_cases hc : (if 1 - t^2 ≤ 0 then t else 5) ≤ 3
  · rw [if_pos (by linarith [hc]), if_pos hc]
  · push Not at hc
    rw [if_neg (by linarith), if_neg (by push Not; linarith)]

/-! ### (10b) The route value on the 3-point sample and the base separation -/

/-- The increasing 3-point sample `(−2, 0, 2)`. -/
def quadWitnessPts : Fin 3 → ℝ := ![-2, 0, 2]

theorem quadWitnessPts_increasing : Increasing quadWitnessPts := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [quadWitnessPts, Fin.lt_def]

/-- The depth-1 witness route, packaged as a route function; it lies in `quadDepthGrade 1 2 1`. -/
def quadWitnessRouteFn : (Fin 1 → ℝ) → Fin 2 :=
  quadCascadeRoute (QuadCascade.mk (fun _ : Fin 1 => quadWitnessLayer)) quadWitnessRoute (by norm_num)

theorem quadWitnessRouteFn_mem_gradeOne :
    quadWitnessRouteFn ∈ quadDepthGrade 1 2 1 (by norm_num) :=
  ⟨fun _ => quadWitnessLayer, quadWitnessRoute, rfl⟩

/-- **The witness route alternates `0, 1, 0` along `(−2, 0, 2)`: `seqChanges = 2`.** At `t = ±2` the
gate sends to the identity (`run = ±2 ≤ 3`, route `0`); at `t = 0` the gate sends to the constant `5`
(`run = 5 > 3`, route `1`). The two crossings are the order-2 (quadratic) behaviour. -/
theorem quadWitness_alternations_eq_two :
    seqChanges (fun k => quadWitnessRouteFn (fun _ => quadWitnessPts k)) = 2 := by
  have hp0 : quadWitnessPts 0 = -2 := by simp [quadWitnessPts]
  have hp1 : quadWitnessPts 1 = 0 := by simp [quadWitnessPts]
  have hp2 : quadWitnessPts 2 = 2 := by simp [quadWitnessPts]
  have hr0 : quadWitnessRouteFn (fun _ => quadWitnessPts 0) = 0 := by
    unfold quadWitnessRouteFn; rw [hp0, quadWitness_route_eq]
    norm_num
  have hr1 : quadWitnessRouteFn (fun _ => quadWitnessPts 1) = 1 := by
    unfold quadWitnessRouteFn; rw [hp1, quadWitness_route_eq]
    norm_num
  have hr2 : quadWitnessRouteFn (fun _ => quadWitnessPts 2) = 0 := by
    unfold quadWitnessRouteFn; rw [hp2, quadWitness_route_eq]
    norm_num
  unfold seqChanges
  rw [show (Finset.univ.filter (fun i : Fin 2 =>
      (fun k => quadWitnessRouteFn (fun _ => quadWitnessPts k)) i.castSucc
        ≠ (fun k => quadWitnessRouteFn (fun _ => quadWitnessPts k)) i.succ)) = Finset.univ from ?_]
  · simp
  · rw [Finset.eq_univ_iff_forall]
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases i
    · show quadWitnessRouteFn (fun _ => quadWitnessPts 0) ≠ quadWitnessRouteFn (fun _ => quadWitnessPts 1)
      rw [hr0, hr1]; decide
    · show quadWitnessRouteFn (fun _ => quadWitnessPts 1) ≠ quadWitnessRouteFn (fun _ => quadWitnessPts 2)
      rw [hr1, hr2]; decide

/-- **Non-membership: the witness route is NOT in `quadDepthGrade 1 2 0`.** A depth-0 route alternates
≤ 1 along `(−2, 0, 2)` (`quadDepthGrade_zero_alternations_le`), but the witness alternates `2`. -/
theorem quadWitnessRouteFn_not_mem_gradeZero :
    quadWitnessRouteFn ∉ quadDepthGrade 1 2 0 (by norm_num) := by
  rintro ⟨layers, rs, hf⟩
  -- a depth-0 layer family is the empty family
  have hlayers : layers = Fin.elim0 := by funext i; exact absurd i.isLt (by omega)
  subst hlayers
  -- transport the witness alternation count to the realizing depth-0 cascade
  have hwit : seqChanges (fun k => quadWitnessRouteFn (fun _ => quadWitnessPts k)) = 2 :=
    quadWitness_alternations_eq_two
  have hbound : seqChanges (fun k => quadWitnessRouteFn (fun _ => quadWitnessPts k)) ≤ 1 := by
    have hrw : (fun k => quadWitnessRouteFn (fun _ => quadWitnessPts k))
        = fun k => quadCascadeRoute (QuadCascade.mk (Fin.elim0)) rs (by norm_num)
            (fun _ => quadWitnessPts k) := by
      funext k; rw [hf]
    rw [hrw]
    exact quadDepthGrade_zero_alternations_le rs quadWitnessPts quadWitnessPts_increasing
  omega

/-- **THE BASE DEPTH-LADDER SEPARATION `quadDepthGrade 1 2 0 ⊂ quadDepthGrade 1 2 1`.** The `⊆` is the
depth-monotone identity-layer embedding (`quadDepthGrade_succ_subset`); the strictness is the
single-quadratic-gate witness, which alternates `0, 1, 0` (`seqChanges = 2`,
`quadWitness_alternations_eq_two`) but lies outside grade 0, whose routes alternate ≤ 1
(`quadDepthGrade_zero_alternations_le`). A REAL proved `∉`: the second crossing is exactly the order-2
(quadratic gate) phenomenon an affine/order-1 depth-0 route forbids. -/
theorem quadDepthGrade_zero_ssubset_one :
    quadDepthGrade 1 2 0 (by norm_num) ⊂ quadDepthGrade 1 2 1 (by norm_num) := by
  refine ⟨quadDepthGrade_succ_subset (by norm_num), ?_⟩
  intro hsubset
  have hmem : quadWitnessRouteFn ∈ quadDepthGrade 1 2 1 (by norm_num) :=
    quadWitnessRouteFn_mem_gradeOne
  have h0 : quadWitnessRouteFn ∈ quadDepthGrade 1 2 0 (by norm_num) := hsubset hmem
  exact quadWitnessRouteFn_not_mem_gradeZero h0

/-!
## The general-`L` ternary-tent obstruction (precise)

The depth-`L` route bound `quadRoute_alternations_le ≤ 3^{L+1} − 1` is proved at general
`L`. The general-`L` SEPARATION would need a depth-`(L+1)` witness whose route alternates `≥ 3^{L+1}`
times. The natural candidate is an iterated **ternary tent** folding the unit interval into three
covering laps per layer. The obstruction is that the quadratic-gated, **2-affine-branch** layer model
of this file canNOT realize a clean ternary fold:

* A quadratic gate `0 < A t² + B t + C` (with `A < 0`) is true exactly on a single open interval
  `(r₁, r₂)`, partitioning the line into **three** regions `(−∞,r₁]`, `[r₁,r₂]`, `[r₂,∞)`. This is the
  ≤ 2 gate switches that give the per-layer multiplier `3` in the BOUND.

* But the OUTER two regions select the SAME branch (`branch 0`), so the layer output uses only **two**
  distinct affine maps. For a continuous covering tent the outer branch would have to map both
  `[0,r₁]` and `[r₂,1]` ONTO `[0,1]`, which is impossible for an injective affine map: if `branch 0`
  covers the first lap (`branch 0(0)=0`, `branch 0(r₁)=1`, slope `> 0`), then on `[r₂,1]` it outputs
  values `> 1`, so the third lap **escapes** `[0,1]` and does not iterate. The achievable per-layer
  fold factor is therefore **2**, not 3.

* Consequently the iterable witness achieves only `2^L` route oscillations, which never exceeds the
  depth-`L` ceiling `3^{L+1} − 1`. The general-`L` ternary-tent separation does not close with this
  layer model; the bound `3^{L+1} − 1` is correct but not tight for an iterable witness.

Closing the general-`L` separation would require a richer per-layer model, e.g. **3 affine branches
gated by two quadratic thresholds** (an arity-3 quadratic gate), so that all three covering laps use
distinct affine maps and the fold factor is 3. That arity-3 quadratic-gate cascade, together
with a triadic-grid `ternMap^[L](j/3^L) = (j mod 2)` identity (the base-3 analogue of
`tentMap_iterate_dyadic`), is the natural next step; the per-layer ≤2-switch bound
(`QuadLines.arg_two_alternations_le`) and the base-3 composition engine
(`seqChanges_blockRefine_le_two`) built here are exactly the depth-uniform pieces such a proof reuses.
The base rung `quadDepthGrade 0 ⊂ quadDepthGrade 1` above is a real, non-vacuous separation realized by
the order-2 (two-crossing) quadratic-gate phenomenon.
-/

end TLT.TemperedDesignLaw
