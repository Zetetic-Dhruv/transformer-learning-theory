/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Routing.MeasurableScoreRouting
import FLT_Proofs.Complexity.VCDimension

/-!
# The symbol channel and its combinatorial capacity (TD10)

The hard routing decision of a `FiniteScoreRouterCode` — the *symbol channel* — sends each input to
the least-index argmax of its `k` scores. As the parameter varies this produces the **symbol class**
`symbolClass A`, a family of `Fin k`-valued functions on the input space. This file bounds the
combinatorial capacity of the symbol class by the capacity of the underlying **pairwise score
comparisons**.

The mechanism is that the route is a *deterministic function of the pairwise comparison pattern*:
`leastArgmax v` is determined by the relations `vᵢ ≤ vⱼ` alone (`leastArgmax_eq_of_le_iff`). Hence on
any finite sample the number of distinct routing-label patterns is at most the number of distinct
joint comparison patterns (`symbolRestr_ncard_le_cmpRestr`). Each ordered pair `(i, j)` contributes a
Boolean comparison class `comparisonClass A i j`, to which the shipped Sauer–Shelah growth bound
applies; the symbol channel's capacity is thereby reduced to the VC dimension of these comparison
classes — the geometry of the score-comparison arrangement.

## Main definitions

* `symbolClass A hk` — the class of routing-label functions `X → Fin k` realized by the router.
* `comparisonClass A i j` — the Boolean class of the score comparison `sᵢ ≤ sⱼ`.
* `routeRestr` / `cmpRestr` / `singleCmpRestr` — restrictions of the route / joint-comparison /
  per-pair-comparison maps to a finite sample.

## Main results

* `leastArgmax_eq_of_le_iff` — the argmax is determined by the pairwise `≤` pattern.
* `symbolRestr_ncard_le_cmpRestr` — on a finite sample, the count of routing-label patterns is at
  most the count of joint comparison patterns (the composition step).
* `cmpRestr_ncard_le_prod` — the joint comparison count is at most the product of the `k²` per-pair
  comparison counts (the arrangement decomposition step).
* `symbolRestr_ncard_le_prod` — the symbol-channel capacity bound: the routing-label pattern count is
  at most the product of the per-pair score-comparison pattern counts. Each factor is bounded by the
  shipped Sauer–Shelah growth bound (`growth_function_le_sum_choose_set`) at the VC dimension of
  `comparisonClass A i j`, the geometry of the score-comparison arrangement.
-/

noncomputable section

namespace TLT.TemperedDesignLaw

universe u

variable {X : Type u} [MeasurableSpace X] {k : ℕ}

/-! ### The argmax is determined by the comparison pattern -/

/-- **The least-argmax depends only on the pairwise `≤` pattern.** If two score vectors induce the
same ordering relation on every pair of coordinates, their least-index maximizers coincide. This is
the determinism that lets the symbol channel factor through the pairwise comparisons. -/
theorem leastArgmax_eq_of_le_iff (v v' : Fin k → ℝ) (hk : 0 < k)
    (h : ∀ i j, v i ≤ v j ↔ v' i ≤ v' j) :
    leastArgmax v hk = leastArgmax v' hk := by
  have hspec : isLeastArgmax v (leastArgmax v hk) := leastArgmax_spec v hk
  have hspec' : isLeastArgmax v' (leastArgmax v hk) := by
    refine ⟨fun j => (h j (leastArgmax v hk)).mp (hspec.1 j), fun j hj => ?_⟩
    have hlt : v j < v (leastArgmax v hk) := hspec.2 j hj
    rw [← not_le] at hlt ⊢
    exact fun hcon => hlt ((h (leastArgmax v hk) j).mpr hcon)
  exact isLeastArgmax_unique v' _ _ hspec' (leastArgmax_spec v' hk)

/-! ### The symbol class and the comparison classes -/

/-- **The symbol class.** The family of routing-label functions `X → Fin k` realized by the argmax
route of `A` as the parameter ranges over `A.Ρ`. This is the hard routing decision — the symbol
channel — whose capacity this file bounds. -/
def symbolClass (A : FiniteScoreRouterCode X k) (hk : 0 < k) : Set (X → Fin k) :=
  Set.range (A.route hk)

/-- The `(i, j)` pairwise score-comparison concept at parameter `ρ`: the Boolean indicator of
`sᵢ ≤ sⱼ`. -/
def comparisonConcept (A : FiniteScoreRouterCode X k) (ρ : A.Ρ) (i j : Fin k) : Concept X Bool :=
  fun x => decide (A.score ρ x i ≤ A.score ρ x j)

/-- **The comparison class** for the ordered pair `(i, j)`: the Boolean concept class of the score
comparison `sᵢ ≤ sⱼ` as the parameter varies. The route is a deterministic function of the joint
pattern of these `k²` classes, and the shipped Sauer–Shelah bound applies to each. -/
def comparisonClass (A : FiniteScoreRouterCode X k) (i j : Fin k) : ConceptClass X Bool :=
  Set.range (fun ρ => comparisonConcept A ρ i j)

/-- The routing-label restriction map: a parameter ↦ its `Fin k` routing labels on the sample `S`. -/
def routeRestr (A : FiniteScoreRouterCode X k) (hk : 0 < k) (S : Finset X) :
    A.Ρ → (↥S → Fin k) :=
  fun ρ x => A.route hk ρ (x : X)

/-- The joint comparison restriction map: a parameter ↦ the full pairwise comparison pattern on the
sample `S`. -/
def cmpRestr (A : FiniteScoreRouterCode X k) (S : Finset X) :
    A.Ρ → (↥S → (Fin k → Fin k → Bool)) :=
  fun ρ x i j => decide (A.score ρ (x : X) i ≤ A.score ρ (x : X) j)

/-- The per-pair comparison restriction: a parameter ↦ the Boolean comparison `sᵢ ≤ sⱼ` on the
sample `S`. The joint comparison pattern `cmpRestr` is the `k²`-tuple of these. -/
def singleCmpRestr (A : FiniteScoreRouterCode X k) (S : Finset X) (p : Fin k × Fin k) :
    A.Ρ → (↥S → Bool) :=
  fun ρ x => decide (A.score ρ (x : X) p.1 ≤ A.score ρ (x : X) p.2)

/-! ### The capacity reduction -/

/-- **The symbol channel factors through the comparison pattern.** On any finite sample `S`, the
number of distinct routing-label patterns realized by the symbol class is at most the number of
distinct joint pairwise-comparison patterns — because the route is a deterministic function of the
comparison pattern (`leastArgmax_eq_of_le_iff`). This reduces the symbol channel's combinatorial
capacity to that of the `k²` Boolean comparison classes. -/
theorem symbolRestr_ncard_le_cmpRestr (A : FiniteScoreRouterCode X k) (hk : 0 < k) (S : Finset X) :
    (Set.range (routeRestr A hk S)).ncard ≤ (Set.range (cmpRestr A S)).ncard := by
  have hfac : Function.FactorsThrough (routeRestr A hk S) (cmpRestr A S) := by
    intro ρ ρ' hcmp
    funext x
    simp only [routeRestr, FiniteScoreRouterCode.route]
    apply leastArgmax_eq_of_le_iff
    intro i j
    have h2 := congrFun (congrFun (congrFun hcmp x) i) j
    simpa only [cmpRestr, decide_eq_decide] using h2
  have hsub : Set.range (routeRestr A hk S) ⊆
      (Function.extend (cmpRestr A S) (routeRestr A hk S) (fun _ _ => ⟨0, hk⟩))
        '' Set.range (cmpRestr A S) := by
    rintro _ ⟨ρ, rfl⟩
    exact ⟨cmpRestr A S ρ, Set.mem_range_self ρ, hfac.extend_apply (fun _ _ => ⟨0, hk⟩) ρ⟩
  calc (Set.range (routeRestr A hk S)).ncard
      ≤ ((Function.extend (cmpRestr A S) (routeRestr A hk S) (fun _ _ => ⟨0, hk⟩))
          '' Set.range (cmpRestr A S)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Set.range (cmpRestr A S)).ncard := Set.ncard_image_le (Set.toFinite _)

/-- **The joint comparison count is at most the product of the per-pair counts.** The composition
half of the symbol-capacity bound: the joint pairwise-comparison restriction is the `k²`-tuple of the
per-pair comparison restrictions, an injection into the product, so its count is bounded by the
product of the per-pair comparison counts. -/
theorem cmpRestr_ncard_le_prod (A : FiniteScoreRouterCode X k) (S : Finset X) :
    (Set.range (cmpRestr A S)).ncard
      ≤ ∏ p : Fin k × Fin k, (Set.range (singleCmpRestr A S p)).ncard := by
  classical
  have hinj : Function.Injective
      (fun q : ↥S → (Fin k → Fin k → Bool) => fun p : Fin k × Fin k => fun x : ↥S => q x p.1 p.2) := by
    intro q q' h
    funext x i j
    exact congrFun (congrFun h (i, j)) x
  have hsub :
      (fun q : ↥S → (Fin k → Fin k → Bool) => fun p : Fin k × Fin k => fun x : ↥S => q x p.1 p.2)
          '' Set.range (cmpRestr A S)
        ⊆ ↑(Fintype.piFinset fun p => (Set.toFinite (Set.range (singleCmpRestr A S p))).toFinset) := by
    rintro _ ⟨_, ⟨ρ, rfl⟩, rfl⟩
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
    exact fun p => ⟨ρ, rfl⟩
  calc (Set.range (cmpRestr A S)).ncard
      = ((fun q : ↥S → (Fin k → Fin k → Bool) => fun p : Fin k × Fin k => fun x : ↥S => q x p.1 p.2)
          '' Set.range (cmpRestr A S)).ncard :=
        (Set.ncard_image_of_injective _ hinj).symm
    _ ≤ (↑(Fintype.piFinset fun p =>
          (Set.toFinite (Set.range (singleCmpRestr A S p))).toFinset) : Set _).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (Fintype.piFinset fun p =>
          (Set.toFinite (Set.range (singleCmpRestr A S p))).toFinset).card := by
        rw [Set.ncard_eq_toFinset_card', Finset.toFinset_coe]
    _ = ∏ p : Fin k × Fin k, ((Set.toFinite (Set.range (singleCmpRestr A S p))).toFinset).card :=
        Fintype.card_piFinset _
    _ = ∏ p : Fin k × Fin k, (Set.range (singleCmpRestr A S p)).ncard := by
        refine Finset.prod_congr rfl fun p _ => ?_
        exact (Set.ncard_eq_toFinset_card _).symm

/-- **The symbol-channel capacity bound (TD10): arrangement × composition.** On any finite sample
`S`, the number of distinct routing-label patterns the symbol class realizes is at most the *product*
over the `k²` ordered coordinate pairs of the per-pair score-comparison pattern counts. The two
factors of the argument: the route is determined by the joint comparison pattern
(`symbolRestr_ncard_le_cmpRestr`, the composition), and that joint pattern injects into the product of
the per-pair comparison patterns (`cmpRestr_ncard_le_prod`, the arrangement decomposition). Bounding
each factor `(Set.range (singleCmpRestr A S (i, j))).ncard` by the shipped Sauer–Shelah growth bound
`growth_function_le_sum_choose_set` at `VCDim X (comparisonClass A i j)` then yields the symbol
channel's capacity as a polynomial in `S.card` of degree the total comparison VC dimension. -/
theorem symbolRestr_ncard_le_prod (A : FiniteScoreRouterCode X k) (hk : 0 < k) (S : Finset X) :
    (Set.range (routeRestr A hk S)).ncard
      ≤ ∏ p : Fin k × Fin k, (Set.range (singleCmpRestr A S p)).ncard :=
  le_trans (symbolRestr_ncard_le_cmpRestr A hk S) (cmpRestr_ncard_le_prod A S)

end TLT.TemperedDesignLaw
