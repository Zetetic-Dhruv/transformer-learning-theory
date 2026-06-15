/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MixtureParamLayer
import TLT_Proofs.Capacity.Chaining.LipschitzCoveringDischarge

/-!
# Soft-capacity at depth: the sharpness-scaled Dudley bound (TD9 S4)

The tempered mixture stack's empirical capacity is bounded by the library's Dudley entropy integral with
the parameter-Lipschitz constant scaling **linearly in the sharpness `β`** per layer, the statistical price
of sharpness in closed form, via the chaining apparatus.

* `valueVec_dist_le_of_pointwise`: a parameter-Lipschitz *pointwise* bound on `F` transports to the
  value-vector map (`valueVec` carries the sup metric on `Fin m → ℝ`). This is the `hlip` hypothesis of
  `capacityReal_le_dudley_of_lipschitz`, factored out of its inline transformer use.
* `paramStack_empiricalCapacity_le_dudley`: for a loss `ℓ` composed with any `ParamLayer` stack, the
  empirical capacity on the weight ball is at most the Dudley bound at constant `Lℓ · paramLipBound Ls`.
  Instantiated at `List.replicate L temperedParamLayer` (whose per-layer `paramLip = 2βKsθP + Kvθ`), the
  constant is `Lℓ · paramLipBound (replicate L temperedParamLayer)`, linear in `β`.
-/

open MeasureTheory

noncomputable section

namespace TLT.TemperedDesignLaw

open TLT.Capacity

/-- **The value-vector map is parameter-Lipschitz from a pointwise bound.** `valueVec F S` reads `F θ`
on the sample under the sup metric on `Fin m → ℝ`, so a uniform pointwise parameter-Lipschitz bound on `F`
transports verbatim to `valueVec`. This is exactly the `hlip` hypothesis the Dudley discharge
`capacityReal_le_dudley_of_lipschitz` consumes. -/
theorem valueVec_dist_le_of_pointwise {X : Type*} {d m : ℕ} (F : ParamSpace d → X → ℝ) (S : Fin m → X)
    {L : ℝ} (hL0 : 0 ≤ L) {θ θ' : ParamSpace d}
    (hpt : ∀ x, |F θ x - F θ' x| ≤ L * dist θ θ') :
    dist (valueVec F S θ) (valueVec F S θ') ≤ L * dist θ θ' := by
  rw [dist_pi_le_iff (mul_nonneg hL0 dist_nonneg)]
  intro j
  simp only [valueVec, Real.dist_eq]
  exact hpt (S j)

/-- **Soft capacity at depth: the sharpness-scaled Dudley bound.** A loss `ℓ` (Lipschitz, constant `Lℓ`)
composed with a `ParamLayer` stack `Ls` has empirical capacity on the radius-`R` weight ball bounded by the
library's Dudley entropy integral at parameter-Lipschitz constant `Lℓ · paramLipBound Ls`. With
`Ls = List.replicate L temperedParamLayer` the per-layer `paramLip` is `2·β·Ksθ·P + Kvθ`, so the constant
(and the whole capacity bound) is linear in the sharpness `β`. The `hlip` discharge uses
`valueVec_dist_le_of_pointwise` over the depth-`L` parameter-Lipschitz telescope `paramComp_param_lipschitz`;
the Dudley side-conditions are discharged by `empiricalCapacityReal_le_computable`. -/
def paramStack_empiricalCapacity_le_dudley {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d m : ℕ} [Nonempty (Fin d)] (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R)
    (Ls : List (ParamLayer (ParamSpace d) V)) (ℓ : V → ℝ) {Lℓ : ℝ} (hLℓ : 0 ≤ Lℓ)
    (hℓ : ∀ a b, |ℓ a - ℓ b| ≤ Lℓ * dist a b) {b : ℝ} (hb : 0 < b)
    (hFb : ∀ θ x, |ℓ (paramComp Ls θ x)| ≤ b) (S : Fin m → V)
    (hL : 0 < Lℓ * paramLipBound Ls) :=
  empiricalCapacityReal_le_computable hm hR (fun θ x => ℓ (paramComp Ls θ x)) hb hFb S hL
    (fun θ _ θ' _ =>
      valueVec_dist_le_of_pointwise _ S (mul_nonneg hLℓ (paramLipBound_nonneg Ls))
        (fun x => by
          calc |ℓ (paramComp Ls θ x) - ℓ (paramComp Ls θ' x)|
              ≤ Lℓ * dist (paramComp Ls θ x) (paramComp Ls θ' x) := hℓ _ _
            _ ≤ Lℓ * (paramLipBound Ls * dist θ θ') :=
                mul_le_mul_of_nonneg_left (paramComp_param_lipschitz Ls θ θ' x) hLℓ
            _ = Lℓ * paramLipBound Ls * dist θ θ' := (mul_assoc _ _ _).symm))

end TLT.TemperedDesignLaw
