/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Forward.ForwardContinuity

/-!
# Per-layer weight-Lipschitz estimates over a bounded input domain

The forward-pass layers are Lipschitz in their *weights*, with constants conditioned on a bound on
the layer's input. For the matrix-multiply layer this is the exact transpose of the input-Lipschitz
estimate: where the input map `X ↦ W·X` is Lipschitz with the column-ℓ¹ norm of `W`, the weight map
`W ↦ W·X` is Lipschitz — globally in the weights — with the row-ℓ¹ norm of `X`. The ReLU layer
carries no weights, so it is `0`-weight-Lipschitz. These are the per-layer constants that the
parameter-Lipschitz composition amplifies, conditioned on the bounded activation domain that a
bounded weight ball and bounded network input produce.

## Main results

- `matMulCoord_param_lipschitz` — `W ↦ matMulCoord W X` is `β`-Lipschitz in the weights when the
  input `X` has row-ℓ¹ norms bounded by `β`.
- `reluCoord_param_lipschitz` — the ReLU layer is constant in any weight argument.
-/

/-!
## References
- induced operator norm = Lipschitz constant of `W↦WX` (row-ℓ¹ of X in sup metric); [35] Lem 2
  one-layer specialization; weightless ReLU.
- Provenance: Classical-instantiation (textbook induced-norm fact).
-/

namespace TLT

/-- **Linear-layer weight-Lipschitz (the bilinear mirror).** For a fixed input `X` whose rows have
ℓ¹ norm at most `β`, the matrix-multiply map `W ↦ matMulCoord W X` is `β`-Lipschitz in the weights
(sup metric), uniformly over all weights. This is the `W ↔ X` transpose of the input-Lipschitz
estimate `matMulSpecExecLayer.ideal_lip`. -/
lemma matMulCoord_param_lipschitz {s n p : ℕ} (X : Fin s → Fin n → ℝ) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : ∀ i, (∑ k, |X i k|) ≤ β) (W W' : Fin n → Fin p → ℝ) :
    dist (matMulCoord W X) (matMulCoord W' X) ≤ β * dist W W' := by
  refine (dist_pi_le_iff (by positivity)).mpr fun i => ?_
  refine (dist_pi_le_iff (by positivity)).mpr fun j => ?_
  simp only [matMulCoord, Real.dist_eq, ← Finset.sum_sub_distrib, ← mul_sub]
  calc |∑ k, X i k * (W k j - W' k j)|
      ≤ ∑ k, |X i k| * |W k j - W' k j| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun k _ => abs_mul _ _
    _ ≤ ∑ k, |X i k| * dist W W' := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [← Real.dist_eq]
        exact le_trans (dist_le_pi_dist (W k) (W' k) j) (dist_le_pi_dist W W' k)
    _ = (∑ k, |X i k|) * dist W W' := by rw [← Finset.sum_mul]
    _ ≤ β * dist W W' := mul_le_mul_of_nonneg_right (hβ i) dist_nonneg

/-- **ReLU carries no weights.** The componentwise ReLU `reluCoord` does not depend on any weight
argument, so it is `0`-weight-Lipschitz. -/
lemma reluCoord_param_lipschitz {s n : ℕ} (X : Fin s → Fin n → ℝ) :
    dist (reluCoord X) (reluCoord X) = 0 := dist_self _

end TLT
