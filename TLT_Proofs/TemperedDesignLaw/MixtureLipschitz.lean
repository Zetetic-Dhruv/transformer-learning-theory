/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.Conjectures
import TLT_Proofs.Bridge.Lipschitz.SoftmaxJacobian

/-!
# The mixture channel is sharpness-Lipschitz (the `2β` modulus atom)

The mixture channel `softWeights` is the `β`-tempered softmax of the scores. Reading it as
`softmax (β • s)` exposes its modulus exactly: the softmax map is `2`-Lipschitz (the shipped Jacobian
bound `softmax_lipschitz`), and pre-scaling the scores by the sharpness `β ≥ 0` multiplies the constant by
`β`. Hence the mixture weights move by at most `2·β` times the score change:

* `temperedSoftmax_dist_le`: the carrier-agnostic core: `dist (softmax (β•z)) (softmax (β•z')) ≤ 2·β·dist z z'`.
* `softWeights_eq_softmax_smul`: the bridge `softWeights A ρ x = softmax (β • score ρ x)`.
* `softWeights_param_dist_le`: the parameter form. The mixture weights at two parameters differ by at most
  `2·β` times the score-read difference. Composing with a `K`-Lipschitz score read gives the `2·β·K`
  modulus used by the sharpness-scaled capacity bound and the unrealizability modulus.

The constant is linear in `β`: the sharpness is exactly the knob that trades modulus for hardness.
-/

open scoped BigOperators

universe u

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The β-scaled softmax modulus** (carrier-agnostic core). Pre-scaling the logits by a sharpness
`β ≥ 0` makes the softmax `2·β`-Lipschitz: `dist (softmax (β•z)) (softmax (β•z')) ≤ 2·β·dist z z'`. The
shipped softmax Jacobian bound (`softmax_lipschitz`, constant `2`) composed with the `β`-scaling of the
input, stated standalone as the reusable atom. -/
theorem temperedSoftmax_dist_le {n : ℕ} [NeZero n] {β : ℝ} (hβ : 0 ≤ β) (z z' : Fin n → ℝ) :
    dist (softmax (β • z)) (softmax (β • z')) ≤ 2 * β * dist z z' := by
  have h := softmax_lipschitz.dist_le_mul (β • z) (β • z')
  have hscale : dist (β • z) (β • z') = β * dist z z' := by
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg hβ]
  rw [hscale] at h
  exact le_of_le_of_eq h (by push_cast; ring)

/-- **The bridge.** The mixture channel is the softmax of the `β`-scaled scores:
`softWeights A ρ x = softmax (β • score ρ x)`. Definitional; it lets the softmax modulus transport to the
mixture weights. -/
theorem softWeights_eq_softmax_smul {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : TemperedRouterFamily X k) (ρ : A.router.Ρ) (x : X) :
    softWeights A ρ x = softmax (A.β • A.router.score ρ x) := by
  funext i
  simp only [softWeights, softmax, Pi.smul_apply, smul_eq_mul]

/-- **The parameter-Lipschitz modulus of the mixture channel.** At a fixed input the mixture weights at two
parameters `ρ, ρ'` differ by at most `2·β` times the score-read difference:
`dist (softWeights A ρ x) (softWeights A ρ' x) ≤ 2·β·dist (score ρ x) (score ρ' x)`. Composing with a
`K`-Lipschitz score read yields the `2·β·K` modulus, the atom the soft-capacity chaining bound and the
mixture-channel unrealizability certificate both cite. -/
theorem softWeights_param_dist_le {X : Type u} [MeasurableSpace X] {k : ℕ} [NeZero k]
    (A : TemperedRouterFamily X k) (x : X) (ρ ρ' : A.router.Ρ) :
    dist (softWeights A ρ x) (softWeights A ρ' x)
      ≤ 2 * A.β * dist (A.router.score ρ x) (A.router.score ρ' x) := by
  rw [softWeights_eq_softmax_smul, softWeights_eq_softmax_smul]
  exact temperedSoftmax_dist_le A.hβ _ _

end TLT.TemperedDesignLaw
