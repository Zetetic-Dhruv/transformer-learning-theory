/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MixtureLipschitz

/-!
# The mixture output and its modulus (the product-rule bound)

The mixture channel's *output* is the convex-style combination `∑ᵢ wᵢ • valᵢ` of the per-head payloads
`val` under the mixture weights `w`. Its modulus has the product-rule shape: the output moves by the weight
change times the payload size plus the weight size times the payload change:

* `mixtureOutput_dist_le`: the general two-input bound
  `‖mix w val − mix w' val'‖ ≤ dist w w' · Σ‖valᵢ‖ + Σ‖w'ᵢ‖ · dist val val'`.
* `norm_mixtureOutput_sub_le`: the constant-payload corollary. With the payloads fixed, the output is
  `Σ‖valᵢ‖`-Lipschitz in the weights.
* `mixtureOutput_param_dist_le`: the sharpness-coupled form. Composing with the `2β` mixture-weight modulus,
  the mixture output at two parameters differs by at most `2β · Σ‖valᵢ‖` times the score-read difference.

The sharpness `β` enters only through the weights; the payload size `Σ‖valᵢ‖` is the `β`-independent factor
the depth telescoping carries. This is the per-layer modulus the sharpness-scaled capacity bound consumes.
-/

open scoped BigOperators

universe u

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The mixture output.** The payload combination `∑ᵢ wᵢ • valᵢ` under the mixture weights `w`: the
mixture channel's value, the soft counterpart of selecting a single payload. -/
def mixtureOutput {k : ℕ} {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (w : Fin k → ℝ) (val : Fin k → V) : V :=
  ∑ i, w i • val i

/-- **The product-rule modulus of the mixture output.** The output moves by the weight change times the
payload size plus the weight size times the payload change:
`‖mix w val − mix w' val'‖ ≤ dist w w' · Σ‖valᵢ‖ + Σ‖w'ᵢ‖ · dist val val'`. The finite-sum product rule,
splitting `wᵢvᵢ − w'ᵢv'ᵢ = (wᵢ−w'ᵢ)vᵢ + w'ᵢ(vᵢ−v'ᵢ)` and bounding each coordinate by the sup metric. -/
theorem mixtureOutput_dist_le {k : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w w' : Fin k → ℝ) (val val' : Fin k → V) :
    ‖mixtureOutput w val - mixtureOutput w' val'‖
      ≤ dist w w' * (∑ i, ‖val i‖) + (∑ i, ‖w' i‖) * dist val val' := by
  have heq : mixtureOutput w val - mixtureOutput w' val'
      = ∑ i, ((w i - w' i) • val i + w' i • (val i - val' i)) := by
    rw [mixtureOutput, mixtureOutput, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [sub_smul, smul_sub]; abel)
  rw [heq]
  calc ‖∑ i, ((w i - w' i) • val i + w' i • (val i - val' i))‖
      ≤ ∑ i, ‖(w i - w' i) • val i + w' i • (val i - val' i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, (dist w w' * ‖val i‖ + ‖w' i‖ * dist val val') := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul]
          refine add_le_add (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
            (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
          · rw [← dist_eq_norm]; exact dist_le_pi_dist w w' i
          · rw [← dist_eq_norm]; exact dist_le_pi_dist val val' i
    _ = dist w w' * (∑ i, ‖val i‖) + (∑ i, ‖w' i‖) * dist val val' := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

/-- **The constant-payload modulus.** With the payloads fixed, the mixture output is `Σ‖valᵢ‖`-Lipschitz
in the weights: `‖mix w val − mix w' val‖ ≤ dist w w' · Σ‖valᵢ‖`. The weight-change term of the product
rule (the payload-change term vanishes). -/
theorem norm_mixtureOutput_sub_le {k : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w w' : Fin k → ℝ) (val : Fin k → V) :
    ‖mixtureOutput w val - mixtureOutput w' val‖ ≤ dist w w' * (∑ i, ‖val i‖) := by
  have h := mixtureOutput_dist_le w w' val val
  rwa [dist_self, mul_zero, add_zero] at h

/-- **The sharpness-coupled mixture-output modulus.** At a fixed input and fixed payloads, the mixture
outputs at two parameters differ by at most `2β · Σ‖valᵢ‖` times the score-read difference:
the `2β` mixture-weight modulus (`softWeights_param_dist_le`) composed with the constant-payload
modulus. The per-layer modulus is linear in the sharpness `β`. -/
theorem mixtureOutput_param_dist_le {X : Type u} [MeasurableSpace X] {k : ℕ} [NeZero k]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : TemperedRouterFamily X k) (x : X) (ρ ρ' : A.router.Ρ) (val : Fin k → V) :
    dist (mixtureOutput (softWeights A ρ x) val) (mixtureOutput (softWeights A ρ' x) val)
      ≤ (2 * A.β * dist (A.router.score ρ x) (A.router.score ρ' x)) * (∑ i, ‖val i‖) := by
  rw [dist_eq_norm]
  refine (norm_mixtureOutput_sub_le (softWeights A ρ x) (softWeights A ρ' x) val).trans ?_
  exact mul_le_mul_of_nonneg_right (softWeights_param_dist_le A x ρ ρ')
    (Finset.sum_nonneg (fun i _ => norm_nonneg _))

end TLT.TemperedDesignLaw
