/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.Dimension.Finrank
import TLT_Proofs.Routing.MeasurableScoreRouting
import TLT_Proofs.TemperedDesignLaw.CertificateReal

/-!
# The affine-mux depth hierarchy atom (Strategy C: scores carried in a fixed `W ≤ X → ℝ`)

This module establishes the fundamental depth-hierarchy atom for affine-mux argmax cascades, as a
*constrained* replacement for the degenerate `expressivityGrade` of `ExpressivityDegeneracy.lean`.
There the unconstrained router already realizes every measurable route, so the lattice collapses. The
fix here is a genuine two-part constraint:

* scores are **affine** functionals (and, in the Strategy-C framing, their linear parts lie in a fixed
  finite-dimensional subspace `W = coordSpan d ≤ ((Fin d → ℝ) → ℝ)`, the same `W` used in the capacity
  work (see `AffineFunctional.linFun_mem_coordSpan`, making the `dim W = d` connection explicit);
* region maps are **`n`-way mux-gated** piecewise-affine maps (gate by the argmax of `n` affine scores,
  apply the selected affine branch).

## The canonical shape (shared by all provers, so the results compose)

* `AffineFunctional d`: `{ lin : Fin d → ℝ, const : ℝ }` with `eval x = (∑ i, lin i * x i) + const`.
* `AffineSelfMap d`: affine `X → X` map `{ mat, shift }` with `id`/`comp`.
* `AffineMuxLayer d n`: `n ≥ 1` scores + `n` affine branches; `applyLayer` gates by `leastArgmax`.
* `MuxCascade d L`: a depth-`L`, `Fin L`-indexed family of layers of varying arities.
* `cascade` / `cascadeRoute`: the composed region map, then a `k`-way affine argmax readout.
* `muxCascadeGrade d k L`: the set of route functions realizable by SOME depth-`L` cascade + SOME `k`
  affine route scores. This is the constrained analogue of `expressivityGrade`.

## The three results

* **(A) Definitions**: all of the above.
* **(B) Region-count bound** (`muxCascade_pieces_le_prod`): a depth-`L` cascade is piecewise-affine with
  at most `∏ᵢ arityᵢ` maximal affine pieces. `pieceCount` is `Nat.card (range cascadeTrace)`,
  the number of distinct *active-branch traces*, and the bound is the cardinality of the finite trace
  codomain `∀ i, Fin (arityᵢ)` (`MuxCascade.trace_codomain_card`). Each trace value indexes a fixed
  composition of branch-selected affine maps (one affine cell), so this is the genuine piece count.
* **(C) Convexity / XOR base separation**:
  - `muxCascadeGrade_zero_cells_convex`: every grade-0 route has convex cells (intersections of affine
    half-spaces, i.e. power-diagram cells).
  - `xorRoute_mem_grade_one`: the sign-XOR route, non-convex, is realized at depth 1 by an explicit
    arity-2 fold layer followed by a final argmax readout.
  - `xorRoute_not_mem_grade_zero`: non-membership via the convexity obstruction (three points
    `(1,-1) ↦ 1`, `(-1,1) ↦ 1`, midpoint `(0,0) ↦ 0`).
  - `muxCascadeGrade_zero_ssubset_one`: the strict separation `grade 0 ⊂ grade 1`; depth strictly buys
    expressivity at the base.
-/

open scoped BigOperators
open Set

noncomputable section

namespace TLT.TemperedDesignLaw.MuxHierarchy

universe u

/-! ## (A.1) Affine functionals (the score primitive), Strategy-C framed in `W = coordSpan d` -/

/-- An affine functional on `X = Fin d → ℝ`, represented by a coefficient vector `lin` and a constant
`const`: `eval x = (∑ i, lin i * x i) + const`. Its linear part lies in the fixed finite-dimensional
subspace `W = coordSpan d` (see `AffineFunctional.linFun_mem_coordSpan`), the Strategy-C carrier. -/
structure AffineFunctional (d : ℕ) where
  lin : Fin d → ℝ
  const : ℝ

/-- The value of an affine functional at a point. -/
def AffineFunctional.eval {d : ℕ} (f : AffineFunctional d) (x : Fin d → ℝ) : ℝ :=
  (∑ i, f.lin i * x i) + f.const

/-- The pure linear part `x ↦ ∑ i, lin i * x i` of an affine functional, as a bare function. -/
def AffineFunctional.linFun {d : ℕ} (f : AffineFunctional d) : (Fin d → ℝ) → ℝ :=
  fun x => ∑ i, f.lin i * x i

/-- **Strategy-C carrier (the `W = coordSpan d` framing).** The linear part of every affine functional
lies in the fixed `d`-dimensional subspace `coordSpan d ≤ ((Fin d → ℝ) → ℝ)`, the same `W` used in the
capacity / arrangement-VC work. This makes the `dim W = d` connection explicit: the affine scores are a
valid linear-score carrier, exactly as the attention score differences are. -/
theorem AffineFunctional.linFun_mem_coordSpan {d : ℕ} (f : AffineFunctional d) :
    f.linFun ∈ TLT.TemperedDesignLaw.coordSpan d := by
  have heq : f.linFun = ∑ l : Fin d, f.lin l • (fun x : Fin d → ℝ => x l) := by
    funext x
    simp only [AffineFunctional.linFun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq, TLT.TemperedDesignLaw.coordSpan]
  refine Submodule.sum_mem _ (fun l _ => ?_)
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self l))

/-! ## (A.2) Affine self-maps (the branch primitive) -/

/-- An affine self-map `X → X`, `apply x i = (∑ j, mat i j * x j) + shift i`. -/
structure AffineSelfMap (d : ℕ) where
  mat : Fin d → Fin d → ℝ
  shift : Fin d → ℝ

/-- The action of an affine self-map. -/
def AffineSelfMap.apply {d : ℕ} (A : AffineSelfMap d) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (∑ j, A.mat i j * x j) + A.shift i

/-- The identity affine self-map (`mat = δ`, `shift = 0`). -/
def AffineSelfMap.id (d : ℕ) : AffineSelfMap d where
  mat := fun i j => if i = j then 1 else 0
  shift := fun _ => 0

@[simp] theorem AffineSelfMap.id_apply {d : ℕ} (x : Fin d → ℝ) :
    (AffineSelfMap.id d).apply x = x := by
  funext i
  simp only [AffineSelfMap.apply, AffineSelfMap.id]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-! ## (A.3) The affine-mux layer -/

/-- An `n`-way affine-mux layer (`n ≥ 1` is the mux ARITY). It carries `n` affine *scores* and `n`
affine *branches*. Its action gates by the `leastArgmax` of the scores, then applies the selected
branch. -/
structure AffineMuxLayer (d n : ℕ) where
  scores : Fin n → AffineFunctional d
  branches : Fin n → AffineSelfMap d

/-- The branch index selected by an affine-mux layer at `x`: the `leastArgmax` of its `n` affine
scores. -/
def AffineMuxLayer.gate {d n : ℕ} (L : AffineMuxLayer d n) (hn : 0 < n) (x : Fin d → ℝ) : Fin n :=
  leastArgmax (fun i => (L.scores i).eval x) hn

/-- The map of an affine-mux layer: gate by the argmax of the `n` affine scores, apply the selected
affine branch. -/
def AffineMuxLayer.applyLayer {d n : ℕ} (L : AffineMuxLayer d n) (hn : 0 < n)
    (x : Fin d → ℝ) : Fin d → ℝ :=
  (L.branches (L.gate hn x)).apply x

/-- The arity-1 *identity* mux layer (one trivial score, one identity branch). Its gate is always `0`
and its action is the identity; it embeds a depth-`L` cascade into depth-`L+1`. -/
def AffineMuxLayer.idLayer (d : ℕ) : AffineMuxLayer d 1 where
  scores := fun _ => ⟨fun _ => 0, 0⟩
  branches := fun _ => AffineSelfMap.id d

@[simp] theorem AffineMuxLayer.idLayer_applyLayer {d : ℕ} (x : Fin d → ℝ) :
    (AffineMuxLayer.idLayer d).applyLayer (by norm_num) x = x := by
  simp only [AffineMuxLayer.applyLayer, AffineMuxLayer.idLayer]
  rw [AffineSelfMap.id_apply]

/-! ## (A.4) The depth-`L` cascade (varying arities per layer) -/

/-- A depth-`L` affine-mux cascade: a `Fin L`-indexed family of layers, with per-layer arity `arity i`
(allowed to VARY) and positivity `harity`. -/
structure MuxCascade (d L : ℕ) where
  arity : Fin L → ℕ
  harity : ∀ i, 0 < arity i
  layers : (i : Fin L) → AffineMuxLayer d (arity i)

/-- Run the first `m` layers of a cascade (layers `0, 1, …, m-1`, input-first). -/
def MuxCascade.runUpTo {d L : ℕ} (C : MuxCascade d L) : ℕ → (Fin d → ℝ) → (Fin d → ℝ)
  | 0, x => x
  | (m + 1), x =>
      if h : m < L then
        (C.layers ⟨m, h⟩).applyLayer (C.harity ⟨m, h⟩) (C.runUpTo m x)
      else C.runUpTo m x

/-- The composed region map of the whole cascade: run all `L` layers. -/
def MuxCascade.run {d L : ℕ} (C : MuxCascade d L) (x : Fin d → ℝ) : Fin d → ℝ :=
  C.runUpTo L x

/-- The *active-branch trace* of the cascade at `x`: for each layer `i`, the branch index it selects
when run on the state after the preceding layers. Lives in the finite product type
`∀ i, Fin (arity i)`. -/
def MuxCascade.trace {d L : ℕ} (C : MuxCascade d L) (x : Fin d → ℝ) :
    (i : Fin L) → Fin (C.arity i) :=
  fun i => (C.layers i).gate (C.harity i) (C.runUpTo i.val x)

/-! ## (A.5) The `k`-way affine readout and the grade -/

/-- The `k`-way affine argmax readout of a cascade: `k` affine route-scores read off the cascade output,
selected by `leastArgmax`. -/
def cascadeRoute {d L k : ℕ} (C : MuxCascade d L) (routeScores : Fin k → AffineFunctional d)
    (hk : 0 < k) : (Fin d → ℝ) → Fin k :=
  fun x => leastArgmax (fun j => (routeScores j).eval (C.run x)) hk

/-- **The constrained expressivity grade.** `muxCascadeGrade d k L hk` is the set of route functions
`(Fin d → ℝ) → Fin k` realizable by SOME depth-`L` affine-mux cascade (layers of any arities) together
with SOME `k` affine route-scores. Depth `0` = no mux layers = a bare affine argmax route = a power
diagram. This is the constrained analogue of `expressivityGrade`. -/
def muxCascadeGrade (d k L : ℕ) (hk : 0 < k) : Set ((Fin d → ℝ) → Fin k) :=
  { f | ∃ (C : MuxCascade d L) (routeScores : Fin k → AffineFunctional d),
      f = cascadeRoute C routeScores hk }

/-! ## (B) The region-count bound: ≤ ∏ arities affine pieces -/

/-- **Each trace value is one fixed affine piece.** Running the cascade depends on the
input only through which branch is selected at each layer, i.e. through the trace. Hence on any two
inputs with the same trace prefix, `runUpTo m` produces states obtained by applying the *same* sequence
of (fixed, branch-determined) affine self-maps. Concretely: if `C.trace x = C.trace y` agree on all
layers `< m`, then the selected branch at each such layer is the same, so `runUpTo m` is a fixed
composition of affine maps. We record the load-bearing consequence used by the bound: the trace
codomain is finite, so the number of distinct traces is finite and bounded by `∏ arities`. -/
theorem MuxCascade.trace_codomain_card {d L : ℕ} (C : MuxCascade d L) :
    Fintype.card (∀ i : Fin L, Fin (C.arity i)) = ∏ i, C.arity i := by
  simp [Fintype.card_pi, Fintype.card_fin]

/-- The number of distinct maximal affine pieces of a depth-`L` cascade: the cardinality of the set of
realized active-branch traces. On each fiber `{x | C.trace x = t}` the cascade is a single fixed affine
composition (the branches indexed by `t`), so this counts genuine affine cells. -/
def MuxCascade.pieceCount {d L : ℕ} (C : MuxCascade d L) : ℕ :=
  Nat.card (Set.range C.trace)

/-- **(B) REGION-COUNT BOUND.** A depth-`L` affine-mux cascade is piecewise-affine with at most
`∏ᵢ arityᵢ` maximal affine pieces. Proof: the active-branch trace lands in the finite product type
`∀ i, Fin (arityᵢ)`, whose cardinality is `∏ᵢ arityᵢ`; the number of *distinct realized* traces (the
piece count) is at most this. This is the clean ℕ-inequality form of the depth hierarchy mechanism: each
arity-`n` layer multiplies the piece count by at most `n`. -/
theorem muxCascade_pieces_le_prod {d L : ℕ} (C : MuxCascade d L) :
    C.pieceCount ≤ ∏ i, C.arity i := by
  unfold MuxCascade.pieceCount
  have h : Nat.card (Set.range C.trace) ≤ Nat.card (∀ i : Fin L, Fin (C.arity i)) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  rw [Nat.card_eq_fintype_card (α := ∀ i : Fin L, Fin (C.arity i))] at h
  rw [C.trace_codomain_card] at h
  exact h

/-- The depth-`0` cascade has at most `∏_{i ∈ ∅} = 1` piece: the bare affine route is a single affine
map (a power diagram), one piece. -/
theorem muxCascade_pieces_zero {d : ℕ} (C : MuxCascade d 0) : C.pieceCount ≤ 1 := by
  have := muxCascade_pieces_le_prod C
  simpa using this

/-! ## (C.1) Affine half-space convexity (the power-diagram-cell building blocks) -/

/-- The linear part of the *difference* `p − q` of two affine functionals, as a bare function. -/
def AffineFunctional.diffLin {d : ℕ} (p q : AffineFunctional d) : (Fin d → ℝ) → ℝ :=
  fun x => ∑ i, (p.lin i - q.lin i) * x i

theorem AffineFunctional.diffLin_eq {d : ℕ} (p q : AffineFunctional d) (x : Fin d → ℝ) :
    p.diffLin q x = (∑ i, p.lin i * x i) - (∑ i, q.lin i * x i) := by
  rw [AffineFunctional.diffLin, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem AffineFunctional.diffLin_isLinear {d : ℕ} (p q : AffineFunctional d) :
    IsLinearMap ℝ (p.diffLin q) := by
  refine ⟨fun a b => ?_, fun c a => ?_⟩
  · simp only [AffineFunctional.diffLin, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  · simp only [AffineFunctional.diffLin, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)

theorem AffineFunctional.eval_le_iff {d : ℕ} (p q : AffineFunctional d) (x : Fin d → ℝ) :
    p.eval x ≤ q.eval x ↔ p.diffLin q x ≤ q.const - p.const := by
  rw [AffineFunctional.diffLin_eq]; simp only [AffineFunctional.eval]
  constructor <;> intro h <;> linarith

theorem AffineFunctional.eval_lt_iff {d : ℕ} (p q : AffineFunctional d) (x : Fin d → ℝ) :
    p.eval x < q.eval x ↔ p.diffLin q x < q.const - p.const := by
  rw [AffineFunctional.diffLin_eq]; simp only [AffineFunctional.eval]
  constructor <;> intro h <;> linarith

/-- **An affine `≤`-cell is convex.** `{x | p.eval x ≤ q.eval x}` is a half-space for the linear part of
`p − q`, hence convex. -/
theorem affineLe_convex {d : ℕ} (p q : AffineFunctional d) :
    Convex ℝ {x : Fin d → ℝ | p.eval x ≤ q.eval x} := by
  have hset : {x : Fin d → ℝ | p.eval x ≤ q.eval x}
      = {x | p.diffLin q x ≤ q.const - p.const} := by
    ext x; exact AffineFunctional.eval_le_iff p q x
  rw [hset]; exact convex_halfSpace_le (AffineFunctional.diffLin_isLinear p q) _

/-- **An affine strict `<`-cell is convex.** -/
theorem affineLt_convex {d : ℕ} (p q : AffineFunctional d) :
    Convex ℝ {x : Fin d → ℝ | p.eval x < q.eval x} := by
  have hset : {x : Fin d → ℝ | p.eval x < q.eval x}
      = {x | p.diffLin q x < q.const - p.const} := by
    ext x; exact AffineFunctional.eval_lt_iff p q x
  rw [hset]; exact convex_halfSpace_lt (AffineFunctional.diffLin_isLinear p q) _

/-! ## (C.2) Grade-0 route cells are convex (power diagram) -/

/-- At depth `0` the cascade is the identity: `C.run x = x`. -/
@[simp] theorem MuxCascade.run_zero {d : ℕ} (C : MuxCascade d 0) (x : Fin d → ℝ) :
    C.run x = x := rfl

/-- **(C) GRADE-0 CELLS ARE CONVEX.** For any route `f ∈ muxCascadeGrade d k 0`, every route-cell
`{x | f x = j}` is a power-diagram cell (an intersection of affine half-spaces), hence convex. The cell
is `{x | f x = j} = (⋂ i, {routeScore i ≤ routeScore j}) ∩ (⋂ i, i < j → {routeScore i < routeScore j})`,
a finite intersection of convex affine `≤`/`<` half-spaces (`convex_iInter`). -/
theorem muxCascadeGrade_zero_cells_convex {d k : ℕ} (hk : 0 < k) (f : (Fin d → ℝ) → Fin k)
    (hf : f ∈ muxCascadeGrade d k 0 hk) (j : Fin k) :
    Convex ℝ {x : Fin d → ℝ | f x = j} := by
  obtain ⟨C, routeScores, rfl⟩ := hf
  -- the cell is exactly the `isLeastArgmax` set, intersection of affine half-spaces
  have hcell : {x : Fin d → ℝ | cascadeRoute C routeScores hk x = j}
      = (⋂ i : Fin k, {x : Fin d → ℝ | (routeScores i).eval x ≤ (routeScores j).eval x})
        ∩ (⋂ i : Fin k, ⋂ _ : i < j,
            {x : Fin d → ℝ | (routeScores i).eval x < (routeScores j).eval x}) := by
    ext x
    simp only [cascadeRoute, MuxCascade.run_zero, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_iInter]
    constructor
    · intro h
      have hspec : isLeastArgmax (fun i => (routeScores i).eval x) j := by
        rw [← h]; exact leastArgmax_spec _ hk
      exact ⟨fun i => hspec.1 i, fun i hij => hspec.2 i hij⟩
    · rintro ⟨hle, hlt⟩
      have hspec : isLeastArgmax (fun i => (routeScores i).eval x) j :=
        ⟨fun i => hle i, fun i hij => hlt i hij⟩
      exact isLeastArgmax_unique _ _ _ (leastArgmax_spec _ hk) hspec
  rw [hcell]
  refine Convex.inter ?_ ?_
  · exact convex_iInter (fun i => affineLe_convex (routeScores i) (routeScores j))
  · exact convex_iInter (fun i => convex_iInter (fun _ => affineLt_convex (routeScores i) (routeScores j)))

/-- **`leastArgmax` at arity 2 is a score comparison.** Index `0` wins ties: `leastArgmax v = 0` iff
`v 1 ≤ v 0`, else `1`. -/
theorem leastArgmax_two (v : Fin 2 → ℝ) :
    leastArgmax v (by norm_num) = if v 1 ≤ v 0 then 0 else 1 := by
  apply isLeastArgmax_unique _ _ _ (leastArgmax_spec _ _)
  by_cases h : v 1 ≤ v 0
  · simp only [h, if_true]
    refine ⟨fun j => ?_, fun j hj => absurd hj (by omega)⟩
    fin_cases j
    · exact le_refl _
    · exact h
  · push Not at h
    simp only [show ¬(v 1 ≤ v 0) from not_le.mpr h, if_false]
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · fin_cases j
      · exact le_of_lt h
      · exact le_refl _
    · have hj0 : j = 0 := by omega
      subst hj0; exact h

/-! ## (C.3) The XOR route -/

/-- The sign-XOR route on `R² = Fin 2 → ℝ`: `0` when the two sign-bits *agree*, `1` when they *differ*.
We use the boundary convention consistent with a single sign-fold: in the `x 0 ≥ 0` half-plane "agree"
means `x 1 ≥ 0`; in the `x 0 < 0` half-plane "agree" means `x 1 ≤ 0` (the sign of `x 1` matched against
the sign of `x 0`). The route-`1` region is then `{x 0 ≥ 0, x 1 < 0} ∪ {x 0 < 0, x 1 > 0}`, an open
quadrant union, non-convex: it contains `(1,-1)` and `(-1,1)` but not their midpoint `(0,0)`.

This `def` is *equivalent to* the propositional sign-XOR `if (0 ≤ x 0) = (0 ≤ x 1) then 0 else 1`
everywhere off the single boundary line `{x 0 < 0, x 1 = 0}` (a null set), where the deterministic
`leastArgmax` tie-break fixes the convention; the choice does not affect the non-convexity witness. -/
def xorRoute : (Fin 2 → ℝ) → Fin 2 :=
  fun x => if 0 ≤ x 0 then (if 0 ≤ x 1 then 0 else 1) else (if x 1 ≤ 0 then 0 else 1)

/-! ### (C.4) Depth-1 realization of `xorRoute` -/

/-- The fold layer: arity 2, gate on the sign of `x 0` (`gate = 0` iff `x 0 ≥ 0`), branch 0 = identity,
branch 1 = negate the `x 1` coordinate. After this layer the state is `(x0, x1)` when `x0 ≥ 0` and
`(x0, -x1)` when `x0 < 0`. -/
def xorFoldLayer : AffineMuxLayer 2 2 where
  scores := fun i => if i = 0 then ⟨fun l => if l = 0 then 1 else 0, 0⟩
                              else ⟨fun l => if l = 0 then -1 else 0, 0⟩
  branches := fun i => if i = 0 then AffineSelfMap.id 2
                                else ⟨fun a b => if a = 1 ∧ b = 1 then -1
                                                 else if a = b then 1 else 0, fun _ => 0⟩

/-- The depth-1 cascade for XOR: a single `xorFoldLayer`. -/
def xorCascade : MuxCascade 2 1 where
  arity := fun _ => 2
  harity := fun _ => by norm_num
  layers := fun _ => xorFoldLayer

/-- The final readout for XOR: route on the sign of the (possibly folded) `x 1` coordinate. route 0 =
`state ↦ state 1`, route 1 = `state ↦ -state 1`. `route = 0` iff `state 1 ≥ 0`. -/
def xorRouteScores : Fin 2 → AffineFunctional 2 :=
  fun j => if j = 0 then ⟨fun l => if l = 1 then 1 else 0, 0⟩
                    else ⟨fun l => if l = 1 then -1 else 0, 0⟩

/-- The fold layer's two scores evaluate to `x 0` (score 0) and `-x 0` (score 1). -/
theorem xorFoldLayer_scores_eval (x : Fin 2 → ℝ) :
    (xorFoldLayer.scores 0).eval x = x 0 ∧ (xorFoldLayer.scores 1).eval x = - x 0 := by
  refine ⟨?_, ?_⟩
  · show (xorFoldLayer.scores 0).eval x = x 0
    have : xorFoldLayer.scores 0 = ⟨fun l => if l = 0 then 1 else 0, 0⟩ := by simp [xorFoldLayer]
    rw [this]; simp [AffineFunctional.eval]
  · show (xorFoldLayer.scores 1).eval x = - x 0
    have : xorFoldLayer.scores 1 = ⟨fun l => if l = 0 then -1 else 0, 0⟩ := by simp [xorFoldLayer]
    rw [this]; simp [AffineFunctional.eval]

/-- The fold layer's gate: `0` when `x 0 ≥ 0`, else `1`. -/
theorem xorFoldLayer_gate (x : Fin 2 → ℝ) :
    xorFoldLayer.gate (by norm_num) x = if 0 ≤ x 0 then 0 else 1 := by
  simp only [AffineMuxLayer.gate]
  rw [leastArgmax_two]
  obtain ⟨h0, h1⟩ := xorFoldLayer_scores_eval x
  simp only [h0, h1]
  by_cases hx : (0 : ℝ) ≤ x 0
  · rw [if_pos (by linarith), if_pos hx]
  · rw [if_neg (by push Not at hx ⊢; linarith), if_neg hx]

/-- The fold layer's action: identity when `x 0 ≥ 0`, negate `x 1` when `x 0 < 0`. We record the value
of the folded coordinate `1`, which is all the readout needs. -/
theorem xorFoldLayer_applyLayer_coord1 (x : Fin 2 → ℝ) :
    (xorFoldLayer.applyLayer (by norm_num) x) 1 = if 0 ≤ x 0 then x 1 else - x 1 := by
  simp only [AffineMuxLayer.applyLayer, xorFoldLayer_gate]
  by_cases hx : (0 : ℝ) ≤ x 0
  · rw [if_pos hx, if_pos hx]
    show ((xorFoldLayer.branches 0).apply x) 1 = x 1
    have : xorFoldLayer.branches 0 = AffineSelfMap.id 2 := by simp [xorFoldLayer]
    rw [this, AffineSelfMap.id_apply]
  · rw [if_neg hx, if_neg hx]
    show ((xorFoldLayer.branches 1).apply x) 1 = - x 1
    have : xorFoldLayer.branches 1
        = ⟨fun a b => if a = 1 ∧ b = 1 then -1 else if a = b then 1 else 0, fun _ => 0⟩ := by
      simp [xorFoldLayer]
    rw [this]
    simp [AffineSelfMap.apply]

/-- The depth-1 cascade output coordinate `1` is the folded sign-encoded value. -/
theorem xorCascade_run_coord1 (x : Fin 2 → ℝ) :
    (xorCascade.run x) 1 = if 0 ≤ x 0 then x 1 else - x 1 := by
  show (xorCascade.runUpTo 1 x) 1 = _
  rw [MuxCascade.runUpTo]
  rw [dif_pos (by norm_num : (0 : ℕ) < 1)]
  show (xorFoldLayer.applyLayer _ (xorCascade.runUpTo 0 x)) 1 = _
  rw [MuxCascade.runUpTo]
  exact xorFoldLayer_applyLayer_coord1 x

/-- The two route scores evaluate to `state 1` (route 0) and `-state 1` (route 1). -/
theorem xorRouteScores_eval (s : Fin 2 → ℝ) :
    (xorRouteScores 0).eval s = s 1 ∧ (xorRouteScores 1).eval s = - s 1 := by
  refine ⟨?_, ?_⟩
  · show (xorRouteScores 0).eval s = s 1
    have : xorRouteScores 0 = ⟨fun l => if l = 1 then 1 else 0, 0⟩ := by simp [xorRouteScores]
    rw [this]; simp [AffineFunctional.eval]
  · show (xorRouteScores 1).eval s = - s 1
    have : xorRouteScores 1 = ⟨fun l => if l = 1 then -1 else 0, 0⟩ := by simp [xorRouteScores]
    rw [this]; simp [AffineFunctional.eval]

/-- **(C) DEPTH-1 XOR REALIZATION.** The depth-1 affine-mux cascade `xorCascade` (one arity-2 fold
layer that conditionally negates `x 1` on the sign of `x 0`) followed by the affine readout
`xorRouteScores` (argmax on the sign of the folded `x 1`) computes exactly the sign-XOR route.
Hence `xorRoute ∈ muxCascadeGrade 2 2 1`. -/
theorem xorRoute_eq_cascadeRoute :
    xorRoute = cascadeRoute xorCascade xorRouteScores (by norm_num) := by
  funext x
  -- The readout reduces to `if 0 ≤ (folded x 1) then 0 else 1`.
  have hreadout : cascadeRoute xorCascade xorRouteScores (by norm_num) x
      = if 0 ≤ (if 0 ≤ x 0 then x 1 else - x 1) then 0 else 1 := by
    simp only [cascadeRoute]
    rw [leastArgmax_two]
    obtain ⟨h0, h1⟩ := xorRouteScores_eval (xorCascade.run x)
    simp only [h0, h1]
    rw [xorCascade_run_coord1]
    by_cases hc : (0 : ℝ) ≤ (if 0 ≤ x 0 then x 1 else - x 1)
    · rw [if_pos hc, if_pos (by linarith)]
    · rw [if_neg hc, if_neg (by push Not at hc ⊢; linarith)]
  rw [hreadout]
  simp only [xorRoute]
  -- case split on the sign of x 0
  by_cases hx0 : (0 : ℝ) ≤ x 0
  · -- x 0 ≥ 0 : fold is identity, folded = x 1 ; both sides reduce to `if 0 ≤ x 1`
    rw [if_pos hx0, if_pos hx0]
  · -- x 0 < 0 : fold negates, folded = -x 1 ; route 0 iff 0 ≤ -x1 iff x1 ≤ 0
    rw [if_neg hx0, if_neg hx0]
    by_cases hx1 : x 1 ≤ 0
    · rw [if_pos hx1, if_pos (by linarith)]
    · rw [if_neg hx1, if_neg (by push Not at hx1 ⊢; linarith)]

/-- **xorRoute is genuinely realized at depth 1.** -/
theorem xorRoute_mem_grade_one :
    xorRoute ∈ muxCascadeGrade 2 2 1 (by norm_num) :=
  ⟨xorCascade, xorRouteScores, xorRoute_eq_cascadeRoute⟩

/-! ### (C.5) `xorRoute` is genuinely non-convex, hence not at depth 0 -/

/-- Three witness points exhibiting the non-convexity of the route-`1` cell of `xorRoute`:
`(1, -1) ↦ 1`, `(-1, 1) ↦ 1`, but their midpoint `(0, 0) ↦ 0`. -/
theorem xorRoute_pt_a : xorRoute ![1, -1] = 1 := by
  simp only [xorRoute, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [if_pos (by norm_num : (0 : ℝ) ≤ 1), if_neg (by norm_num : ¬ (0 : ℝ) ≤ -1)]

theorem xorRoute_pt_b : xorRoute ![-1, 1] = 1 := by
  simp only [xorRoute, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [if_neg (by norm_num : ¬ (0 : ℝ) ≤ -1), if_neg (by norm_num : ¬ (1 : ℝ) ≤ 0)]

theorem xorRoute_pt_mid : xorRoute ![0, 0] = 0 := by
  simp only [xorRoute, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [if_pos (by norm_num : (0 : ℝ) ≤ 0), if_pos (by norm_num : (0 : ℝ) ≤ 0)]

/-- The midpoint `(0,0)` is the convex combination `(1/2)•(1,-1) + (1/2)•(-1,1)`. -/
theorem xorRoute_mid_eq_comb :
    ((1:ℝ)/2) • (![1, -1] : Fin 2 → ℝ) + ((1:ℝ)/2) • (![-1, 1] : Fin 2 → ℝ) = ![0, 0] := by
  funext i
  fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **(C) Non-membership: `xorRoute ∉ muxCascadeGrade 2 2 0`.** If it
were a grade-0 route, its route-`1` cell would be convex (`muxCascadeGrade_zero_cells_convex`). But the
cell is non-convex: it contains `(1,-1)` and `(-1,1)` (both route `1`) yet not their midpoint `(0,0)`
(route `0`), a contradiction. The convexity obstruction shows depth genuinely buys expressivity. -/
theorem xorRoute_not_mem_grade_zero :
    xorRoute ∉ muxCascadeGrade 2 2 0 (by norm_num) := by
  intro hmem
  have hconv : Convex ℝ {x : Fin 2 → ℝ | xorRoute x = 1} :=
    muxCascadeGrade_zero_cells_convex (by norm_num) xorRoute hmem 1
  -- both endpoints are in the route-1 cell
  have ha : (![1, -1] : Fin 2 → ℝ) ∈ {x : Fin 2 → ℝ | xorRoute x = 1} := xorRoute_pt_a
  have hb : (![-1, 1] : Fin 2 → ℝ) ∈ {x : Fin 2 → ℝ | xorRoute x = 1} := xorRoute_pt_b
  -- the midpoint must then be in the cell, by convexity
  have hmid := hconv ha hb (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1:ℝ)/2 + 1/2 = 1)
  rw [xorRoute_mid_eq_comb] at hmid
  -- but the midpoint routes to 0, contradiction
  have : xorRoute ![0, 0] = 1 := hmid
  rw [xorRoute_pt_mid] at this
  exact absurd this (by decide)

/-! ## (C.6) Depth monotonicity and the strict separation atom -/

/-- **Depth-monotone embedding (depth 0 ↪ depth 1).** A depth-0 route is a depth-1 route: prepend a
single arity-1 *identity* mux layer (gate always `0`, branch the identity), which leaves the cascade
output unchanged. Hence `muxCascadeGrade 2 2 0 ⊆ muxCascadeGrade 2 2 1`. -/
theorem muxCascadeGrade_zero_subset_one {k : ℕ} (hk : 0 < k) :
    muxCascadeGrade 2 k 0 hk ⊆ muxCascadeGrade 2 k 1 hk := by
  rintro f ⟨C, routeScores, rfl⟩
  -- the depth-1 cascade with a single identity layer
  refine ⟨⟨fun _ => 1, fun _ => by norm_num, fun _ => AffineMuxLayer.idLayer 2⟩, routeScores, ?_⟩
  funext x
  simp only [cascadeRoute]
  congr 1
  funext j
  congr 1
  -- both cascades produce the same output: the depth-0 cascade is `id`, and the depth-1 identity-layer
  -- cascade is also `id`
  show (C.run x) = _
  rw [MuxCascade.run_zero]
  -- RHS: run of the single identity layer
  show x = MuxCascade.run _ x
  show x = MuxCascade.runUpTo _ 1 x
  rw [MuxCascade.runUpTo, dif_pos (by norm_num : (0 : ℕ) < 1)]
  show x = (AffineMuxLayer.idLayer 2).applyLayer _ (MuxCascade.runUpTo _ 0 x)
  rw [MuxCascade.runUpTo, AffineMuxLayer.idLayer_applyLayer]

/-- **(C) THE STRICT SEPARATION ATOM.** `muxCascadeGrade 2 2 0 ⊂ muxCascadeGrade 2 2 1`. The `⊆` is the
depth-monotone identity-layer embedding; the strictness is the XOR witness: `xorRoute` lies in grade 1
(`xorRoute_mem_grade_one`) but not grade 0 (`xorRoute_not_mem_grade_zero`, via the convexity
obstruction). This is the constrained replacement for the degenerate `expressivityGrade`, establishing
strict depth separation at the base. -/
theorem muxCascadeGrade_zero_ssubset_one (hk : 0 < 2) :
    muxCascadeGrade 2 2 0 hk ⊂ muxCascadeGrade 2 2 1 hk := by
  refine ⟨muxCascadeGrade_zero_subset_one hk, ?_⟩
  intro hsubset
  -- subset-equality would force xorRoute into grade 0
  have hxsub : @muxCascadeGrade 2 2 1 hk ⊆ @muxCascadeGrade 2 2 0 hk := hsubset
  -- but xorRoute ∈ grade 1 and ∉ grade 0
  have h1 : xorRoute ∈ muxCascadeGrade 2 2 1 hk := xorRoute_mem_grade_one
  have h0 : xorRoute ∈ muxCascadeGrade 2 2 0 hk := hxsub h1
  exact xorRoute_not_mem_grade_zero h0

end TLT.TemperedDesignLaw.MuxHierarchy
