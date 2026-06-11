/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MixtureOutput

/-!
# The tempered mixture layer's per-parameter modulus (the per-layer Lipschitz constant)

A tempered mixture layer reads a parameter `θ` into per-head scores `score θ` and payloads `val θ`, and
emits the `β`-tempered mixture `mixtureOutput (softmax (β • score θ)) (val θ)`. Its modulus in the
parameter is the per-layer Lipschitz constant that the depth telescoping (`paramComp_param_lipschitz`,
already in the library) composes into the stack bound `paramLipBound`:

* `temperedMixtureMap` — the layer's forward map `θ ↦ mixtureOutput (softmax (β • score θ)) (val θ)`.
* `temperedMixtureMap_param_dist_le` — the per-layer parameter modulus: with a `Ks`-Lipschitz score read,
  a `Kv`-Lipschitz payload read, and a payload-size bound `P`, the layer is `(2·β·Ks·P + Kv)`-Lipschitz in
  the parameter.

The product rule splits the change into the weight term (the simplex weights move by `2β·Ks` and carry the
payload size `P`) and the payload term (the weights sum to one and carry the payload Lipschitz `Kv`). The
sharpness `β` multiplies only the weight term — the per-layer constant the sharpness-scaled capacity bound
feeds into the telescope.
-/

open scoped BigOperators

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The tempered mixture layer's forward map.** Read the parameter `θ` into scores and payloads, then emit
the `β`-tempered mixture: `θ ↦ mixtureOutput (softmax (β • score θ)) (val θ)`. -/
def temperedMixtureMap {k : ℕ} {Θ : Type*} {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (β : ℝ) (score : Θ → Fin k → ℝ) (val : Θ → Fin k → V) (θ : Θ) : V :=
  mixtureOutput (softmax (β • score θ)) (val θ)

/-- **The per-layer parameter modulus.** With a `Ks`-Lipschitz score read, a `Kv`-Lipschitz payload read,
and a payload-size bound `P ≥ 0`, the tempered mixture layer is `(2·β·Ks·P + Kv)`-Lipschitz in the
parameter. The product rule: the simplex weights move by `2β·Ks` (carrying payload size `P`) and the weights
sum to one (carrying payload Lipschitz `Kv`). This per-layer constant feeds `paramLipBound` in the depth
telescope. -/
theorem temperedMixtureMap_param_dist_le {k : ℕ} [NeZero k] {Θ : Type*} [PseudoMetricSpace Θ]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {β : ℝ} (hβ : 0 ≤ β) {score : Θ → Fin k → ℝ} {val : Θ → Fin k → V} {Ks Kv P : ℝ}
    (hscore : ∀ θ θ', dist (score θ) (score θ') ≤ Ks * dist θ θ')
    (hval_lip : ∀ θ θ', dist (val θ) (val θ') ≤ Kv * dist θ θ')
    (hval_bd : ∀ θ, (∑ i, ‖val θ i‖) ≤ P) (θ θ' : Θ) :
    dist (temperedMixtureMap β score val θ) (temperedMixtureMap β score val θ')
      ≤ (2 * β * Ks * P + Kv) * dist θ θ' := by
  have hsw : dist (softmax (β • score θ)) (softmax (β • score θ')) ≤ 2 * β * (Ks * dist θ θ') :=
    (temperedSoftmax_dist_le hβ (score θ) (score θ')).trans
      (mul_le_mul_of_nonneg_left (hscore θ θ') (by linarith))
  have hwsum : (∑ i, ‖softmax (β • score θ') i‖) = 1 := by
    rw [show (∑ i, ‖softmax (β • score θ') i‖) = ∑ i, softmax (β • score θ') i from
      Finset.sum_congr rfl (fun i _ => Real.norm_of_nonneg (softmax_nonneg _ i))]
    exact softmax_sum_one _
  have ht1 : dist (softmax (β • score θ)) (softmax (β • score θ')) * (∑ i, ‖val θ i‖)
      ≤ (2 * β * Ks * P) * dist θ θ' := by
    calc dist (softmax (β • score θ)) (softmax (β • score θ')) * (∑ i, ‖val θ i‖)
        ≤ (2 * β * (Ks * dist θ θ')) * P :=
          mul_le_mul hsw (hval_bd θ) (Finset.sum_nonneg (fun i _ => norm_nonneg _))
            (le_trans dist_nonneg hsw)
      _ = (2 * β * Ks * P) * dist θ θ' := by ring
  rw [temperedMixtureMap, temperedMixtureMap, dist_eq_norm]
  refine (mixtureOutput_dist_le (softmax (β • score θ)) (softmax (β • score θ'))
    (val θ) (val θ')).trans ?_
  rw [hwsum, one_mul]
  calc dist (softmax (β • score θ)) (softmax (β • score θ')) * (∑ i, ‖val θ i‖)
        + dist (val θ) (val θ')
      ≤ (2 * β * Ks * P) * dist θ θ' + Kv * dist θ θ' := add_le_add ht1 (hval_lip θ θ')
    _ = (2 * β * Ks * P + Kv) * dist θ θ' := by ring

end TLT.TemperedDesignLaw
