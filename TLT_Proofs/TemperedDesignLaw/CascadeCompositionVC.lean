/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.ArrangementVC
import FLT_Proofs.Complexity.IndependentVC.BooleanComb
import FLT_Proofs.Complexity.IndependentVC.BooleanCombFinite
import FLT_Proofs.Complexity.IndependentVC.FrameworkClosures

/-!
# Compositional VC / finite-VC closure for the depth-`L` argmax cascade (R2)

The single-layer arrangement-VC bound `symbolClass_growth_prod` (`ArrangementVC.lean`) bounds the
routing-label pattern count of *one* finite score router on a finite sample by a product over the
`k²` ordered coordinate pairs of Sauer–Shelah binomial sums at the per-pair `finrank`. This file
**composes that bound over depth `L`**: a depth-`L` argmax cascade — a `Fin L`-indexed family of
finite score routers of (possibly varying) arities `k ℓ`, jointly parametrised by the product
`∀ ℓ, (layer ℓ).Ρ` — has its full **route trace** `x ↦ (route₀ x, route₁ x, …, route_{L-1} x)`
controlled by a product over **(layer × ordered-pair)** of the same Sauer–Shelah sums, hence has
finite VC (is learnable).

## The cascade and its route trace

* `CascadeRouterCode X L k`: a depth-`L` family of finite score routers `layer ℓ : FiniteScoreRouterCode X (k ℓ)`.
* `CascadeRouterCode.Param`: the joint parameter `∀ ℓ, (layer ℓ).Ρ`.
* `cascadeTrace C hk`: the route trace `Param → X → (∀ ℓ, Fin (k ℓ))`, the depth-`L` generalisation
  of `symbolClass`'s single route `A.route`.
* `cascadeTraceRestr C hk S`: the restriction of the trace to a finite sample `S`.

## The two locked results

* **(form A, growth)** `cascadeTrace_growth_prod`: the depth-`L` cascade route trace's pattern count on
  any finite sample `S` is at most the product **over (layer × ordered-pair)** of the Sauer–Shelah
  binomial sums at the per-layer per-pair `finrank ℝ (W ℓ p)`. This is `symbolClass_growth_prod`
  composed over the `L` layers. General in `L`, the per-layer arities `k ℓ`, the input space `X`, and
  the per-layer per-pair finite-dim score-difference spaces `W ℓ p`.
* **(form B, VC)** `cascadeRouteSymbol_vcDim_finite`: each per-layer route-symbol bit-class
  `{ x ↦ decide (route_ℓ x = s) }` of the cascade has `VCDim < ⊤`, by expressing it as a `booleanComb`
  of the per-pair score-comparison classes (`comparisonClass`, each of finite VC by
  `comparisonClass_vcDim_le`) and applying FLT's closure `vcDim_booleanComb_finite`.

The mechanism: each per-layer, per-pair routing decision is a Bool comparison class of finite VC
(`comparisonClass_vcDim_le`); finite VC is closed under Boolean / structural combination
(`vcDim_booleanComb_finite`); the depth-`L` route is a deterministic function of these finitely many
decisions (the layer-`ℓ` route at `x` is `leastArgmax` of its `k ℓ` scores, determined by the pairwise
`≤` pattern by `leastArgmax_eq_of_le_iff`), so the composed class is finite-VC / polynomial-growth.
-/

noncomputable section

open Module

namespace TLT.TemperedDesignLaw

universe u

variable {X : Type u} [MeasurableSpace X]

/-! ### The depth-`L` argmax cascade and its route trace -/

/-- A **depth-`L` argmax cascade**: a `Fin L`-indexed family of finite score routers `layer ℓ`, the
`ℓ`-th of arity `k ℓ` (arities may vary per layer). Each layer is an independent
`FiniteScoreRouterCode X (k ℓ)` over the shared input space `X`; the cascade is jointly parametrised
by the product of the per-layer parameter spaces. This is the depth-`L` generalisation of the single
`FiniteScoreRouterCode` underlying `symbolClass`. -/
structure CascadeRouterCode (X : Type u) [MeasurableSpace X] (L : ℕ) (k : Fin L → ℕ) where
  /-- The `ℓ`-th layer: a finite score router of arity `k ℓ` over the shared input `X`. -/
  layer : (ℓ : Fin L) → FiniteScoreRouterCode X (k ℓ)

/-- The joint parameter space of a depth-`L` cascade: a parameter for each layer. -/
def CascadeRouterCode.Param {L : ℕ} {k : Fin L → ℕ} (C : CascadeRouterCode X L k) : Type u :=
  (ℓ : Fin L) → (C.layer ℓ).Ρ

/-- **The cascade route trace.** At a joint parameter `ρ` and input `x`, the tuple of per-layer argmax
routes `ℓ ↦ route_ℓ x`, an element of the finite product `∀ ℓ, Fin (k ℓ)`. This is the depth-`L`
generalisation of the single route `A.route hk`. -/
def cascadeTrace {L : ℕ} {k : Fin L → ℕ} (C : CascadeRouterCode X L k)
    (hk : ∀ ℓ, 0 < k ℓ) : C.Param → X → (∀ ℓ, Fin (k ℓ)) :=
  fun ρ x ℓ => (C.layer ℓ).route (hk ℓ) (ρ ℓ) x

/-- The cascade route-trace restriction to a finite sample `S`: a joint parameter ↦ its full per-layer
route trace on `S`. The depth-`L` generalisation of `routeRestr`. -/
def cascadeTraceRestr {L : ℕ} {k : Fin L → ℕ} (C : CascadeRouterCode X L k)
    (hk : ∀ ℓ, 0 < k ℓ) (S : Finset X) : C.Param → (↥S → (∀ ℓ, Fin (k ℓ))) :=
  fun ρ x => cascadeTrace C hk ρ (x : X)

/-! ### The composition step: the trace count factors over the layers -/

/-- **The cascade route-trace pattern count factors over the layers.** On any finite sample `S`, the
number of distinct route-trace patterns realised by the depth-`L` cascade is at most the *product over
the `L` layers* of the per-layer routing-label pattern counts `(Set.range (routeRestr (C.layer ℓ) ...))`.
The argument: each layer's parameter `ρ ℓ` is independent (the joint parameter is the product), so the
trace restriction `ρ ↦ (ℓ ↦ x ↦ route_ℓ x)` injects into the product of the per-layer route
restrictions; the count of a subset of a product Pi-finset is the product of the per-coordinate counts.
This is the depth analogue of `cmpRestr_ncard_le_prod` (which factors a single layer's joint comparison
over the `k²` pairs); here we factor the whole cascade over the `L` layers. -/
theorem cascadeTraceRestr_ncard_le_prod {L : ℕ} {k : Fin L → ℕ} (C : CascadeRouterCode X L k)
    (hk : ∀ ℓ, 0 < k ℓ) (S : Finset X) :
    (Set.range (cascadeTraceRestr C hk S)).ncard
      ≤ ∏ ℓ : Fin L, (Set.range (routeRestr (C.layer ℓ) (hk ℓ) S)).ncard := by
  classical
  -- Transpose the trace restriction `↥S → ∀ ℓ, Fin (k ℓ)` to `∀ ℓ, ↥S → Fin (k ℓ)`.
  set Φ : (↥S → (∀ ℓ, Fin (k ℓ))) → (∀ ℓ, ↥S → Fin (k ℓ)) :=
    fun q ℓ x => q x ℓ with hΦ
  have hinj : Function.Injective Φ := by
    intro q q' h
    funext x ℓ
    exact congrFun (congrFun h ℓ) x
  -- The transposed trace map sends `ρ` to the tuple of per-layer route restrictions.
  have htrans : ∀ ρ : C.Param,
      Φ (cascadeTraceRestr C hk S ρ) = fun ℓ => routeRestr (C.layer ℓ) (hk ℓ) S (ρ ℓ) := by
    intro ρ; rfl
  -- The transposed image lands in the product of the per-layer route ranges.
  have hsub :
      Φ '' Set.range (cascadeTraceRestr C hk S)
        ⊆ ↑(Fintype.piFinset fun ℓ =>
            (Set.toFinite (Set.range (routeRestr (C.layer ℓ) (hk ℓ) S))).toFinset) := by
    rintro _ ⟨_, ⟨ρ, rfl⟩, rfl⟩
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
    intro ℓ
    rw [htrans ρ]
    exact ⟨ρ ℓ, rfl⟩
  calc (Set.range (cascadeTraceRestr C hk S)).ncard
      = (Φ '' Set.range (cascadeTraceRestr C hk S)).ncard :=
        (Set.ncard_image_of_injective _ hinj).symm
    _ ≤ (↑(Fintype.piFinset fun ℓ =>
          (Set.toFinite (Set.range (routeRestr (C.layer ℓ) (hk ℓ) S))).toFinset) : Set _).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (Fintype.piFinset fun ℓ =>
          (Set.toFinite (Set.range (routeRestr (C.layer ℓ) (hk ℓ) S))).toFinset).card := by
        rw [Set.ncard_eq_toFinset_card', Finset.toFinset_coe]
    _ = ∏ ℓ : Fin L, ((Set.toFinite (Set.range (routeRestr (C.layer ℓ) (hk ℓ) S))).toFinset).card :=
        Fintype.card_piFinset _
    _ = ∏ ℓ : Fin L, (Set.range (routeRestr (C.layer ℓ) (hk ℓ) S)).ncard := by
        refine Finset.prod_congr rfl fun ℓ _ => ?_
        exact (Set.ncard_eq_toFinset_card _).symm

/-! ### (form A) The depth-`L` compositional growth bound -/

/-- **(form A) THE DEPTH-`L` COMPOSITIONAL ARRANGEMENT-VC BOUND (R2).** Under per-layer per-pair
linearity of the score differences (for each layer `ℓ` and ordered pair `p` of its `k ℓ` heads, the
score difference `x ↦ s_{p.2}(x) − s_{p.1}(x)` lies in a finite-dimensional `W ℓ p ≤ (X → ℝ)`), the
number of route-trace patterns the depth-`L` cascade realises on any finite sample `S` is at most the
**product over all (layer × ordered-pair)** of the Sauer–Shelah binomial sums at the per-layer per-pair
`finrank ℝ (W ℓ p)`:
`∏_ℓ ∏_{p : Fin (k ℓ)²} ∑_{r ≤ finrank (W ℓ p)} (|S| choose r)`,
a polynomial in `|S|` of degree the total comparison VC dimension `∑_ℓ ∑_p finrank (W ℓ p)`. This is
`symbolClass_growth_prod` composed over the `L` layers: the trace count factors over the layers
(`cascadeTraceRestr_ncard_le_prod`), and each per-layer factor is bounded by the single-layer
arrangement-VC product. General in the depth `L`, the per-layer arities `k ℓ`, the input space `X`, and
the per-layer per-pair finite-dimensional score-difference spaces `W ℓ p`. Conditional on `hlin`
(false for arbitrary measurable scores). -/
theorem cascadeTrace_growth_prod {L : ℕ} {k : Fin L → ℕ} (C : CascadeRouterCode X L k)
    (hk : ∀ ℓ, 0 < k ℓ)
    (W : (ℓ : Fin L) → Fin (k ℓ) × Fin (k ℓ) → Submodule ℝ (X → ℝ))
    (hWfin : ∀ ℓ p, FiniteDimensional ℝ (W ℓ p))
    (hlin : ∀ (ℓ : Fin L) (p : Fin (k ℓ) × Fin (k ℓ)) (ρ : (C.layer ℓ).Ρ),
      (fun x => (C.layer ℓ).score ρ x p.2 - (C.layer ℓ).score ρ x p.1) ∈ W ℓ p)
    (S : Finset X) :
    (Set.range (cascadeTraceRestr C hk S)).ncard
      ≤ ∏ ℓ : Fin L, ∏ p : Fin (k ℓ) × Fin (k ℓ),
          ∑ r ∈ Finset.range (finrank ℝ (W ℓ p) + 1), S.card.choose r := by
  refine le_trans (cascadeTraceRestr_ncard_le_prod C hk S) ?_
  refine Finset.prod_le_prod' (fun ℓ _ => ?_)
  exact symbolClass_growth_prod (C.layer ℓ) (hk ℓ) (W ℓ) (hWfin ℓ) (hlin ℓ) S

/-! ### (form B) Finite VC of the route-symbol bit-classes via Boolean combination -/

variable {k : ℕ}

/-- **The route-symbol bit-class** of a single finite score router `A`: as the parameter varies, the
Boolean indicator `x ↦ decide (A.route hk ρ x = s)` of "the argmax route is the symbol `s`". This is
the Bool-valued slice of `symbolClass` at the label `s`; finite VC of all these slices is the VC face
of a finite route class. -/
def routeSymbolClass (A : FiniteScoreRouterCode X k) (hk : 0 < k) (s : Fin k) : ConceptClass X Bool :=
  Set.range (fun ρ => fun x => decide (A.route hk ρ x = s))

/-- The fixed Boolean combiner for "least-argmax `= s`", read off the `k²` pairwise `≤` bits indexed by
`Fin (k * k)` via `finProdFinEquiv`. The bit at `finProdFinEquiv (i, j)` is interpreted as `vᵢ ≤ vⱼ`;
`s` is the least argmax iff every head `j` satisfies `v j ≤ v s` (bit `(j, s)` is `true`) and every
head `j < s` satisfies `v s > v j`, i.e. `¬ (v s ≤ v j)` (bit `(s, j)` is `false`). -/
def leastArgmaxCombiner (s : Fin k) : (Fin (k * k) → Bool) → Bool :=
  fun b => decide ((∀ j : Fin k, b (finProdFinEquiv (j, s)) = true) ∧
                   (∀ j : Fin k, j < s → b (finProdFinEquiv (s, j)) = false))

/-- The `Fin (k * k)`-indexed family of comparison classes of `A`: index `finProdFinEquiv (i, j)`
carries `comparisonClass A i j`, the `sᵢ ≤ sⱼ` Boolean class. The route-symbol class embeds in the
Boolean combination of these by `leastArgmaxCombiner`. -/
def comparisonFamily (A : FiniteScoreRouterCode X k) : Fin (k * k) → ConceptClass X Bool :=
  fun i => comparisonClass A (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

/-- **The route-symbol class is a Boolean combination of the comparison classes.** Every concept
`x ↦ decide (A.route hk ρ x = s)` in `routeSymbolClass A hk s` is realised by the fixed combiner
`leastArgmaxCombiner hk s` applied to the `k²` per-pair comparison bits of the *same* parameter `ρ`:
`A.route hk ρ x = s` iff `s` is the least argmax of the scores (`leastArgmax_spec` /
`isLeastArgmax_unique`), which is exactly the conjunction of the `≤`-bits the combiner reads. Hence
`routeSymbolClass A hk s ⊆ booleanComb (leastArgmaxCombiner s) (comparisonFamily A)`. -/
theorem routeSymbolClass_subset_booleanComb (A : FiniteScoreRouterCode X k) (hk : 0 < k) (s : Fin k) :
    routeSymbolClass A hk s
      ⊆ booleanComb (leastArgmaxCombiner s) (comparisonFamily A) := by
  rintro c ⟨ρ, rfl⟩
  refine ⟨fun i => comparisonConcept A ρ (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2,
    fun i => ⟨ρ, rfl⟩, ?_⟩
  funext x
  -- `route = s ↔ isLeastArgmax (score) s`, and the combiner decides exactly that conjunction.
  have hroute : A.route hk ρ x = s ↔ isLeastArgmax (A.score ρ x) s := by
    constructor
    · intro h; exact h ▸ leastArgmax_spec (A.score ρ x) hk
    · intro h; exact isLeastArgmax_unique _ _ _ (leastArgmax_spec (A.score ρ x) hk) h
  simp only [leastArgmaxCombiner, comparisonConcept, Equiv.symm_apply_apply]
  -- Reduce to the equivalence of the underlying Props.
  rw [decide_eq_decide, hroute, isLeastArgmax]
  -- LHS: `(∀ j, v j ≤ v s) ∧ (∀ j < s, v j < v s)`;
  -- RHS: `(∀ j, decide (v j ≤ v s) = true) ∧ (∀ j < s, decide (v s ≤ v j) = false)`.
  refine and_congr ?_ ?_
  · exact ⟨fun h j => decide_eq_true (h j), fun h j => of_decide_eq_true (h j)⟩
  · constructor
    · intro h j hj
      exact decide_eq_false (by simpa using not_le.mpr (h j hj))
    · intro h j hj
      exact not_le.mp (of_decide_eq_false (h j hj))

/-- **(form B, single layer) Finite VC of the route-symbol class.** Under per-pair linearity (each
score difference `x ↦ sⱼ(x) − sᵢ(x)` in a finite-dimensional `W p ≤ (X → ℝ)`), the route-symbol class
`routeSymbolClass A hk s` has finite VC dimension, for every symbol `s`. The mechanism: each comparison
class `comparisonClass A i j` has finite VC (`comparisonClass_vcDim_le`, the per-pair Dudley bound);
finite VC is closed under Boolean combination (`vcDim_booleanComb_finite`); and the route-symbol class
is a Boolean combination of the comparison classes (`routeSymbolClass_subset_booleanComb`), so finite VC
descends by monotonicity. Conditional on `hlin` (false for arbitrary measurable scores). -/
theorem routeSymbolClass_vcDim_finite (A : FiniteScoreRouterCode X k) (hk : 0 < k) (s : Fin k)
    (W : Fin (k * k) → Submodule ℝ (X → ℝ)) (hWfin : ∀ i, FiniteDimensional ℝ (W i))
    (hlin : ∀ (i : Fin (k * k)) (ρ : A.Ρ),
      (fun x => A.score ρ x (finProdFinEquiv.symm i).2 - A.score ρ x (finProdFinEquiv.symm i).1)
        ∈ W i) :
    VCDim X (routeSymbolClass A hk s) < ⊤ := by
  refine lt_of_le_of_lt (vcDim_mono (routeSymbolClass_subset_booleanComb A hk s)) ?_
  refine vcDim_booleanComb_finite (leastArgmaxCombiner s) (comparisonFamily A) (fun i => ?_)
  haveI := hWfin i
  exact lt_of_le_of_lt
    (TLT.Routing.Capacity.comparisonClass_vcDim_le A
      (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 (W i) (hlin i))
    (WithTop.coe_lt_top _)

/-- **(form B) Finite VC of the depth-`L` cascade's per-layer route-symbol bit-classes (R2).** For each
layer `ℓ` of the depth-`L` cascade and each symbol `s` of that layer, under per-pair linearity of the
layer's score differences, the route-symbol bit-class `routeSymbolClass (C.layer ℓ) (hk ℓ) s` has finite
VC dimension. The cascade route trace is, layerwise, exactly these finite-VC routers; finite VC is
closed under the Boolean combination that reads the argmax off the comparison bits
(`routeSymbolClass_vcDim_finite`). Thus the whole depth-`L` cascade route is built from finite-VC
(learnable) pieces. General in the depth `L`, the per-layer arities `k ℓ`, the input space `X`, and the
per-pair finite-dimensional score-difference spaces. Conditional on `hlin`. -/
theorem cascadeRouteSymbol_vcDim_finite {L : ℕ} {kL : Fin L → ℕ} (C : CascadeRouterCode X L kL)
    (hk : ∀ ℓ, 0 < kL ℓ) (ℓ : Fin L) (s : Fin (kL ℓ))
    (W : Fin (kL ℓ * kL ℓ) → Submodule ℝ (X → ℝ)) (hWfin : ∀ i, FiniteDimensional ℝ (W i))
    (hlin : ∀ (i : Fin (kL ℓ * kL ℓ)) (ρ : (C.layer ℓ).Ρ),
      (fun x => (C.layer ℓ).score ρ x (finProdFinEquiv.symm i).2
              - (C.layer ℓ).score ρ x (finProdFinEquiv.symm i).1) ∈ W i) :
    VCDim X (routeSymbolClass (C.layer ℓ) (hk ℓ) s) < ⊤ :=
  routeSymbolClass_vcDim_finite (C.layer ℓ) (hk ℓ) s W hWfin hlin

end TLT.TemperedDesignLaw
