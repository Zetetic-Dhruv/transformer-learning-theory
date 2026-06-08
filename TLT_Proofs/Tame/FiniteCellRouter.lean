/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Routing.MeasurableScoreRouting

/-!
# The finite-cell argmax router: an explicit Borel-cell partition

The argmax router of a `FiniteScoreRouterCode` partitions its domain into the `k` cells
`{x | i = argmax_j score(ρ, x, j)}` (least-index tie-break).  This file makes that cell
structure explicit and **load-bearing** for measurability, realizing Krapp–Wirth §A.3's *"every
definable set is a finite union of cells, and every cell is Borel"* (Lemma A.9) for measurable
scores.

The §A.3 chain `cells are Borel ⟹ routing is measurable ⟹ the patched class is well-behaved`
is formalized as stated: `route_measurable_via_cells` derives joint route-measurability *from*
the named Borel cell `jointArgmaxCell`, and `finiteCellRouter_wellBehaved` closes through it.

## Main definitions

* `FiniteScoreRouterCode.routeCell A ρ i` — the `i`-th argmax cell in the input space at a
  fixed parameter `ρ` (the §A.3 input-domain partition).
* `FiniteScoreRouterCode.jointArgmaxCell A i` — the `i`-th argmax cell in the joint
  parameter–input space `Ρ × X`; the routing fiber, whose Borelness drives joint measurability.

## Main results

* `routeCell_measurable`, `jointArgmaxCell_measurable` — each cell is Borel (a finite
  intersection of the measurable score-inequalities `{sⱼ ≤ sᵢ}`, `{sⱼ < sᵢ}`).
* `iUnion_routeCell`, `routeCell_disjoint`, `route_eq_on_routeCell` — the input-space cells
  cover the domain, are pairwise disjoint, and the router is constant on each.
* `route_measurable_via_cells` — joint route-measurability derived *from* the Borel cells.
* `finiteCellRouter_wellBehaved` — the cell router's patched class satisfies
  `WellBehavedVCMeasTarget`, closed through the explicit cell partition.

## Scope

For the measurability conclusion the measurable-score hypothesis carried by
`FiniteScoreRouterCode.score_meas` is strictly more general than o-minimal definability:
continuous score maps — every finite-dimensional transformer, and the ReLU/sigmoid networks of
Krapp–Wirth Thm 4.7 — are in particular measurable, so their argmax cells are Borel by exactly
the argument here.  The full model-theoretic apparatus (o-minimal structures, the Cell
Decomposition Theorem, and Lemma A.9 in its definability-derives-measurability form) is a
separate development, absent from Mathlib, and is deliberately **out of scope**; this file takes
no new axioms.
-/

/-!
## References
- [7] §A.3 cells / Lemma A.9 (every cell is Borel), Thm 4.7; [11] measurable selection
  (piecewise-constant on Borel cells); [14] finite-cell joint-measurability (cousin); standard
  product-σ-algebra measurability.
- Provenance: Classical-instantiation (measurable-score realization of [7] §A.3; weakens the
  hypothesis from o-minimal definability to measurability).
-/

universe u

open MeasureTheory Set

variable {X : Type u} [MeasurableSpace X] {k : ℕ}

/-! ### Input-space cell partition (at a fixed parameter) -/

/-- The `i`-th argmax routing cell at parameter `ρ`: the inputs whose least-index argmax head
is `i`.  This is the cell of the input-space partition induced by the router. -/
def FiniteScoreRouterCode.routeCell (A : FiniteScoreRouterCode X k) (ρ : A.Ρ) (i : Fin k) :
    Set X :=
  {x | isLeastArgmax (A.score ρ x) i}

/-- The cell is the finite intersection of the defining score-inequalities — the elementary
"cell" shape (a Boolean combination of `≤`/`<` between coordinate scores). -/
private lemma routeCell_eq_inter (A : FiniteScoreRouterCode X k) (ρ : A.Ρ) (i : Fin k) :
    A.routeCell ρ i =
      (⋂ j, {x | A.score ρ x j ≤ A.score ρ x i}) ∩
      ⋂ j ∈ ({j | j < i} : Set (Fin k)), {x | A.score ρ x j < A.score ρ x i} := by
  ext x
  simp only [FiniteScoreRouterCode.routeCell, isLeastArgmax, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_iInter]

/-- **Each argmax cell is Borel.**  The Krapp–Wirth Lemma A.9 conclusion ("every cell is
Borel"), realized for measurable scores: the cell is a finite intersection of the measurable
inequality sets between coordinate scores. -/
theorem FiniteScoreRouterCode.routeCell_measurable (A : FiniteScoreRouterCode X k) (ρ : A.Ρ)
    (i : Fin k) : MeasurableSet (A.routeCell ρ i) := by
  rw [routeCell_eq_inter A ρ i]
  exact (MeasurableSet.iInter fun j =>
        measurableSet_le ((A.score_meas j).comp measurable_prodMk_left)
          ((A.score_meas i).comp measurable_prodMk_left)).inter
      (MeasurableSet.biInter (Set.countable_univ.mono (Set.subset_univ _))
        fun j _ => measurableSet_lt ((A.score_meas j).comp measurable_prodMk_left)
          ((A.score_meas i).comp measurable_prodMk_left))

/-- The cells are exactly the routing fibers: `routeCell A ρ i = (route ρ)⁻¹{i}`. -/
theorem FiniteScoreRouterCode.routeCell_eq_route_preimage (A : FiniteScoreRouterCode X k)
    (hk : 0 < k) (ρ : A.Ρ) (i : Fin k) :
    A.routeCell ρ i = (fun x => A.route hk ρ x) ⁻¹' {i} := by
  ext x
  simp only [FiniteScoreRouterCode.routeCell, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_singleton_iff, FiniteScoreRouterCode.route]
  exact ⟨fun h => isLeastArgmax_unique _ _ _ (leastArgmax_spec _ hk) h,
         fun h => h ▸ leastArgmax_spec _ hk⟩

/-- The router is constant (equal to `i`) on its `i`-th cell. -/
theorem FiniteScoreRouterCode.route_eq_on_routeCell (A : FiniteScoreRouterCode X k) (hk : 0 < k)
    (ρ : A.Ρ) (i : Fin k) {x : X} (hx : x ∈ A.routeCell ρ i) : A.route hk ρ x = i := by
  exact isLeastArgmax_unique _ _ _ (leastArgmax_spec _ hk) hx

/-- **The cells cover the input space.**  Every input lies in some cell (its least-index
argmax head). -/
theorem FiniteScoreRouterCode.iUnion_routeCell (A : FiniteScoreRouterCode X k) (hk : 0 < k)
    (ρ : A.Ρ) : ⋃ i, A.routeCell ρ i = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true, FiniteScoreRouterCode.routeCell,
    Set.mem_setOf_eq]
  exact ⟨leastArgmax (A.score ρ x) hk, leastArgmax_spec _ hk⟩

/-- **Distinct cells are disjoint.**  Least-index argmax is unique, so an input cannot lie in
two cells. -/
theorem FiniteScoreRouterCode.routeCell_disjoint (A : FiniteScoreRouterCode X k) (ρ : A.Ρ)
    {i j : Fin k} (hij : i ≠ j) : Disjoint (A.routeCell ρ i) (A.routeCell ρ j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  exact hij (isLeastArgmax_unique _ _ _ hxi hxj)

/-! ### Joint argmax cell and route measurability -/

/-- The `i`-th argmax routing cell in the joint parameter–input space `Ρ × X`.  By
`route_preimage_eq` this is the routing fiber `(route ρ)⁻¹{i}`; unlike the per-parameter
`routeCell`, its Borelness yields *joint* route-measurability (separate measurability in each
variable would not). -/
def FiniteScoreRouterCode.jointArgmaxCell (A : FiniteScoreRouterCode X k) (i : Fin k) :
    Set (A.Ρ × X) :=
  {p | isLeastArgmax (A.score p.1 p.2) i}

/-- The joint cell is the finite intersection of the joint score-inequalities. -/
private lemma jointArgmaxCell_eq_inter (A : FiniteScoreRouterCode X k) (i : Fin k) :
    A.jointArgmaxCell i =
      (⋂ j, {p : A.Ρ × X | A.score p.1 p.2 j ≤ A.score p.1 p.2 i}) ∩
      ⋂ j ∈ ({j | j < i} : Set (Fin k)), {p : A.Ρ × X | A.score p.1 p.2 j < A.score p.1 p.2 i} := by
  ext p
  simp only [FiniteScoreRouterCode.jointArgmaxCell, isLeastArgmax, Set.mem_setOf_eq,
    Set.mem_inter_iff, Set.mem_iInter]

/-- **Each joint argmax cell is Borel.**  The Lemma A.9 conclusion at the joint level: a finite
intersection of the measurable inequality sets between coordinate scores, using the joint
measurability `score_meas` directly (no section argument needed). -/
theorem FiniteScoreRouterCode.jointArgmaxCell_measurable (A : FiniteScoreRouterCode X k)
    (i : Fin k) : MeasurableSet (A.jointArgmaxCell i) := by
  rw [jointArgmaxCell_eq_inter A i]
  exact (MeasurableSet.iInter fun j => measurableSet_le (A.score_meas j) (A.score_meas i)).inter
    (MeasurableSet.biInter (Set.countable_univ.mono (Set.subset_univ _))
      fun j _ => measurableSet_lt (A.score_meas j) (A.score_meas i))

/-- **Route-measurability through the cells.**  The argmax route is jointly measurable because
each routing fiber is the Borel cell `jointArgmaxCell` — the §A.3 implication
`finite union of Borel cells ⟹ measurable routing`, made explicit. -/
theorem FiniteScoreRouterCode.route_measurable_via_cells (A : FiniteScoreRouterCode X k)
    (hk : 0 < k) : Measurable (fun p : A.Ρ × X => A.route hk p.1 p.2) := by
  apply measurable_to_countable'
  intro i
  rw [A.route_preimage_eq hk i]
  exact A.jointArgmaxCell_measurable i

/-! ### Well-behavedness through the cells -/

/-- **Well-behavedness of the finite-cell argmax router.**  With Borel-parameterized experts,
the patched class of the cell router satisfies `WellBehavedVCMeasTarget`.  The proof flows
through the explicit Borel cell partition: `route_measurable_via_cells` supplies the joint
route-measurability *from* `jointArgmaxCell_measurable`, which feeds `multiPatchEval_measurable`
and the Borel-parameter well-behavedness bridge. -/
theorem finiteCellRouter_wellBehaved [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ] (hk : 0 < k)
    (e : Θ → Fin k → Concept X Bool) (A : FiniteScoreRouterCode X k)
    (he : ∀ i, Measurable (fun p : Θ × X => e p.1 i p.2)) :
    WellBehavedVCMeasTarget X (Set.range (multiPatchEval e (A.route hk))) :=
  borel_param_wellBehavedVCMeasTarget (multiPatchEval e (A.route hk))
    (multiPatchEval_measurable e (A.route hk) he (A.route_measurable_via_cells hk))
