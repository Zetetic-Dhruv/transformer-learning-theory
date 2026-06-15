/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.BigOperators.Field

/-!
# Softmax at the coordinate level

The softmax map `softmax z i = exp (z i) / ∑ⱼ exp (z j)` on `Fin n → ℝ`, with its basic
properties. This is the coordinate-level model of attention's `Activation.softmaxSpec`; it is the
target of the weight-Lipschitz analysis of attention (a covering-number bound needs the attention
output to be Lipschitz in its scores, which factors through the Lipschitz constant of `softmax`).

## Main results

- `softmax`: the coordinate softmax map.
- `softmax_pos` / `softmax_nonneg`: each coordinate is positive.
- `softmax_sum_one`: the coordinates sum to one (for a nonempty index).
- `softmax_le_one`: each coordinate is at most one.

## References

A. Vaswani et al., *Attention Is All You Need*, NeurIPS 2017 (softmax attention); H. Kim,
G. Papamakarios and A. Mnih, *The Lipschitz Constant of Self-Attention*, ICML 2021 (Lipschitz
analysis of attention on bounded domains).
-/

open Real

namespace TLT

variable {n : ℕ}

/-- The coordinate softmax map `softmax z i = exp (z i) / ∑ⱼ exp (z j)`. -/
noncomputable def softmax (z : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (z i) / ∑ j, Real.exp (z j)

/-- The softmax normalising constant is positive when the index set is nonempty. -/
lemma sum_exp_pos [NeZero n] (z : Fin n → ℝ) : 0 < ∑ j, Real.exp (z j) :=
  Finset.sum_pos (fun j _ => Real.exp_pos (z j)) (Finset.univ_nonempty)

/-- Each softmax coordinate is positive. -/
lemma softmax_pos [NeZero n] (z : Fin n → ℝ) (i : Fin n) : 0 < softmax z i :=
  div_pos (Real.exp_pos _) (sum_exp_pos z)

/-- Each softmax coordinate is nonnegative. -/
lemma softmax_nonneg [NeZero n] (z : Fin n → ℝ) (i : Fin n) : 0 ≤ softmax z i :=
  (softmax_pos z i).le

/-- The softmax coordinates sum to one. -/
lemma softmax_sum_one [NeZero n] (z : Fin n → ℝ) : ∑ i, softmax z i = 1 := by
  unfold softmax
  rw [← Finset.sum_div, div_self (sum_exp_pos z).ne']

/-- Each softmax coordinate is at most one. -/
lemma softmax_le_one [NeZero n] (z : Fin n → ℝ) (i : Fin n) : softmax z i ≤ 1 := by
  rw [← softmax_sum_one z]
  exact Finset.single_le_sum (fun j _ => softmax_nonneg z j) (Finset.mem_univ i)

/-! ### The softmax Jacobian and the Lipschitz bound

Softmax is globally Lipschitz: its Jacobian `J z = diag(p) − ppᵀ` (with `p = softmax z`) has, in the
supremum norm of `Fin n → ℝ`, operator norm bounded by an absolute constant. We take the elementary
bound `2` (each Jacobian coordinate is `pᵢ(vᵢ − ⟨p,v⟩)`, of size `≤ 2‖v‖∞`); the optimal sup-norm
constant is `1/2`. This constant is absolute: it does **not** grow with the score scale, so the
downstream capacity stays polynomial in the weights. -/

open ContinuousLinearMap in
/-- The softmax Jacobian as a continuous linear map: `v ↦ (i ↦ pᵢ·(vᵢ − ∑ₖ pₖ vₖ))`, `p = softmax z`. -/
noncomputable def softmaxJac [NeZero n] (z : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    softmax z i • proj i - softmax z i • ∑ k, softmax z k • proj k

@[simp] lemma softmaxJac_apply [NeZero n] (z v : Fin n → ℝ) (i : Fin n) :
    softmaxJac z v i = softmax z i * (v i - ∑ k, softmax z k * v k) := by
  simp only [softmaxJac, ContinuousLinearMap.pi_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.sum_apply, smul_eq_mul]
  ring

/-- Softmax has the Jacobian `softmaxJac z` as its Fréchet derivative at every point. The derivative
is computed as the product `exp(·ᵢ) · (∑ⱼ exp ·ⱼ)⁻¹` (chain/product/quotient rules) and rewritten to
the explicit Jacobian. -/
theorem softmax_hasFDerivAt [NeZero n] (z : Fin n → ℝ) :
    HasFDerivAt (softmax : (Fin n → ℝ) → (Fin n → ℝ)) (softmaxJac z) z := by
  have hSne : (∑ j, Real.exp (z j)) ≠ 0 := (sum_exp_pos z).ne'
  refine hasFDerivAt_pi'' fun i => ?_
  have hexp : HasFDerivAt (fun w : Fin n → ℝ => Real.exp (w i))
      (Real.exp (z i) • ContinuousLinearMap.proj i) z := (hasFDerivAt_apply i z).exp
  have hS : HasFDerivAt (fun w : Fin n → ℝ => ∑ j, Real.exp (w j))
      (∑ j, Real.exp (z j) • ContinuousLinearMap.proj j) z :=
    HasFDerivAt.fun_sum fun j _ => (hasFDerivAt_apply j z).exp
  have hinvS : HasFDerivAt (fun w : Fin n → ℝ => (∑ j, Real.exp (w j))⁻¹)
      (-((∑ j, Real.exp (z j)) ^ 2)⁻¹ • (∑ j, Real.exp (z j) • ContinuousLinearMap.proj j)) z :=
    (hasDerivAt_inv hSne).comp_hasFDerivAt z hS
  have hmul : HasFDerivAt (fun w : Fin n → ℝ => softmax w i) _ z := hexp.mul hinvS
  refine hmul.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.comp_apply, softmaxJac_apply,
    ContinuousLinearMap.sum_apply, smul_eq_mul, softmax, div_mul_eq_mul_div, ← Finset.sum_div]
  field_simp
  ring

/-- The softmax Jacobian has supremum-norm operator norm at most `2`, an absolute constant. -/
theorem softmaxJac_opNorm_le_two [NeZero n] (z : Fin n → ℝ) : ‖softmaxJac z‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
  have key : ∀ i, ‖softmaxJac z v i‖ ≤ 2 * ‖v‖ := by
    intro i
    have hinner : |∑ k, softmax z k * v k| ≤ ‖v‖ := by
      calc |∑ k, softmax z k * v k| ≤ ∑ k, |softmax z k * v k| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k, softmax z k * |v k| := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [abs_mul, abs_of_nonneg (softmax_nonneg z k)]
        _ ≤ ∑ k, softmax z k * ‖v‖ :=
            Finset.sum_le_sum fun k _ =>
              mul_le_mul_of_nonneg_left (norm_le_pi_norm v k) (softmax_nonneg z k)
        _ = ‖v‖ := by rw [← Finset.sum_mul, softmax_sum_one z, one_mul]
    have habs : |v i - ∑ k, softmax z k * v k| ≤ |v i| + |∑ k, softmax z k * v k| := by
      rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    have hvi : |v i| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i
    rw [softmaxJac_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (softmax_nonneg z i)]
    calc softmax z i * |v i - ∑ k, softmax z k * v k|
        ≤ 1 * (|v i| + |∑ k, softmax z k * v k|) :=
          mul_le_mul (softmax_le_one z i) habs (abs_nonneg _) (by norm_num)
      _ ≤ 2 * ‖v‖ := by rw [one_mul]; linarith [hvi, hinner]
  exact (pi_norm_le_iff_of_nonneg (x := softmaxJac z v)
    (show (0:ℝ) ≤ 2 * ‖v‖ by positivity)).mpr key

/-- **Softmax is globally `2`-Lipschitz** (supremum norm). The constant is absolute, independent of
the score scale, which is what keeps the downstream attention capacity bound polynomial. -/
theorem softmax_lipschitz [NeZero n] :
    LipschitzWith 2 (softmax : (Fin n → ℝ) → (Fin n → ℝ)) := by
  refine lipschitzWith_of_nnnorm_fderiv_le
    (fun z => (softmax_hasFDerivAt z).differentiableAt) fun z => ?_
  rw [(softmax_hasFDerivAt z).fderiv]
  exact_mod_cast softmaxJac_opNorm_le_two z

end TLT
