/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Fp32.SequentialSummationBackwardError
import NN.Floats.NeuralFloat.Rounding
import Mathlib.Algebra.BigOperators.Fin

/-!
# Mean-centering tames the naive variance: the affine envelope at the cancellation point

Layer normalization centers each row, `c = x − mean`, so the centered data has exact sum zero. The
spec then computes the per-row variance by the one-pass formula `E[c²] − E[c]²` (the corrected
two-pass scheme of Chan–Golub–LeVeque): the subtracted term `E[c]²` is the square of the fp32-computed
mean of `c`.

At the exact-cancellation point `∑ c = 0`, the *relative* error of the fp32 sum is vacuous (it would
force the result to be exactly zero, which rounding violates), but the **affine** error envelope
`fp32Foldl_error_le` is untouched: it bounds the fp32 sum of the centered data by the rounding budget
*alone* (`fp32_centered_sum_le_budget`). Squaring, the subtracted term `E[c]²` is at most the
*square* of the budget — second order in the unit roundoff — whereas the exact subtracted term is
exactly `0` (`centering_sum_zero`). So the pre-centering demotes the naive-variance cancellation from
first-order-catastrophic to second-order-benign.

## Main results

- `centering_sum_zero` / `centered_list_sum_zero` — the centering forces the exact sum to zero.
- `fp32_centered_sum_le_budget` — at the cancellation point, the fp32 sum is bounded by the budget alone.
- `cancellation_term_le_budget_sq` — the cancellation term is at most the square of the budget.
- `layerNorm_cancellation_secondOrder` — the spec variance's subtracted term `(fp32-mean c)²` is at
  most `(budget / d)²` (second order), while the exact subtracted term is `0`.
- `fp32Round_eq_self_of_genericFormat` — rounding fixes representable values; on the exactness region
  (`fp32Foldl_eq_sum_of_exact`) the cancellation term vanishes exactly (`cancellation_term_zero_of_exact`).
-/

/-!
## References
- [49] corrected two-pass / one-pass variance round-off (Chan–Golub–LeVeque; Neely/Björck correction
  term); [43] recursive-summation affine envelope (`γₙ`); [48] Sterbenz exactness; [50] Flocq
  `round_generic` (round fixes representable values); [52] König–Huygens.
- Provenance: Classical-instantiation — pre-centering demotes the naive-variance cancellation from
  first-order-catastrophic to second-order-benign. Relocated from `Boundary/` (pure fp32 numerics;
  no descriptive-set-theory content).
-/

open TorchLean.Floats
open TorchLean.Floats.IEEE754.IEEE32Exec

open Finset in
/-- The centering forces the exact mean of the centered data to zero. -/
theorem centering_sum_zero {n : ℕ} (a : Fin n → ℝ) (hn : (n : ℝ) ≠ 0) :
    (∑ j, (a j - (∑ k, a k) / (n : ℝ))) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_div_cancel₀ _ hn, sub_self]

/-- The list of centered entries has exact sum zero. -/
theorem centered_list_sum_zero {n : ℕ} (a : Fin n → ℝ) (hn : (n : ℝ) ≠ 0) :
    (List.ofFn (fun j => a j - (∑ k, a k) / (n : ℝ))).sum = 0 := by
  rw [List.sum_ofFn]
  simpa using centering_sum_zero a hn

/-- **At the exact-cancellation point the affine envelope survives.** When the entries sum to zero
(centered data), the fp32 left-fold sum is bounded by the accumulated rounding budget *alone* — the
relative bound is vacuous there, but the absolute (affine) bound is untouched. -/
theorem fp32_centered_sum_le_budget (xs : List ℝ) (hsum : xs.sum = 0)
    (hn : Fp32FoldlNormal 0 xs) :
    |fp32Foldl 0 xs| ≤ fp32FoldlErrorBudget 0 xs := by
  have h := fp32Foldl_error_le 0 xs hn
  simpa [hsum] using h

/-- The naive-variance cancellation term (the squared fp32 mean of centered data) is at most the
*square* of the rounding budget — second order in the unit roundoff — whereas the exact term is `0`. -/
theorem cancellation_term_le_budget_sq (xs : List ℝ) (hsum : xs.sum = 0)
    (hn : Fp32FoldlNormal 0 xs) :
    (fp32Foldl 0 xs) ^ 2 ≤ (fp32FoldlErrorBudget 0 xs) ^ 2 := by
  have h1 : |fp32Foldl 0 xs| ≤ fp32FoldlErrorBudget 0 xs := fp32_centered_sum_le_budget xs hsum hn
  calc (fp32Foldl 0 xs) ^ 2 = |fp32Foldl 0 xs| ^ 2 := (sq_abs _).symm
    _ ≤ (fp32FoldlErrorBudget 0 xs) ^ 2 := by gcongr

/-- **The spec layer-norm variance's subtracted term is second order.** For centered data `c`
(`c.sum = 0`) with `d = ` the row length, the one-pass formula's subtracted term — the square of the
fp32-computed mean `fp32Foldl 0 c / d` — is at most `(budget / d)²`, second order in the unit roundoff,
while the exact subtracted term `(c.sum / d)² = 0`. This is why centering before the variance is
numerically benign. -/
theorem layerNorm_cancellation_secondOrder (c : List ℝ) (d : ℝ) (hd : d ≠ 0)
    (hcentered : c.sum = 0) (hn : Fp32FoldlNormal 0 c) :
    (fp32Foldl 0 c / d) ^ 2 ≤ (fp32FoldlErrorBudget 0 c / d) ^ 2 := by
  rw [div_pow, div_pow]
  have hd2 : (0 : ℝ) < d ^ 2 := by positivity
  exact (div_le_div_iff_of_pos_right hd2).mpr (cancellation_term_le_budget_sq c hcentered hn)

/-! ### The 2-adic exactness refinement (Sterbenz)

Round-to-nearest fixes representable (grid) values, so when every accumulation step of the centering
sum lands exactly on the float grid — the case characterized 2-adically by Sterbenz's exponent
condition (`a − b` is exact when `a/2 ≤ b ≤ 2a`, i.e. the exponents differ by at most one) — the fp32
sum equals the exact sum with **zero** error. On that region the affine envelope is tight at zero, and
the cancellation term vanishes exactly. -/

/-- **Rounding is the identity on representable values.** If `x` lies in the binary32 generic format
(exactly representable), then `fp32Round x = x`. -/
theorem fp32Round_eq_self_of_genericFormat (x : ℝ)
    (hx : neuralGenericFormat binaryRadix fexp32 x) : fp32Round x = x := by
  simp only [neuralGenericFormat, neuralToReal] at hx
  have hsm : neuralScaledMantissa binaryRadix fexp32 x
      = (⌊neuralScaledMantissa binaryRadix fexp32 x⌋ : ℝ) := by
    have h2 := congrArg (· * neuralBpow binaryRadix (-neuralCexp binaryRadix fexp32 x)) hx
    simp only at h2
    conv_lhs => rw [neuralScaledMantissa]
    rw [h2, mul_assoc, ← neuralBpow.add_exp, add_neg_cancel]
    simp [neuralBpow]
  have hrnd : rnd32 (neuralScaledMantissa binaryRadix fexp32 x)
      = ⌊neuralScaledMantissa binaryRadix fexp32 x⌋ := by
    conv_lhs => rw [hsm]
    exact NeuralValidRnd.id _
  calc fp32Round x
      = (↑(rnd32 (neuralScaledMantissa binaryRadix fexp32 x)) : ℝ)
          * neuralBpow binaryRadix (neuralCexp binaryRadix fexp32 x) := rfl
    _ = x := by rw [hrnd]; exact hx.symm

/-- Every accumulation step of the fp32 left fold is exactly representable (no rounding error). -/
def Fp32FoldlExact : ℝ → List ℝ → Prop
  | _, [] => True
  | acc, x :: xs => fp32Round (acc + x) = acc + x ∧ Fp32FoldlExact (acc + x) xs

/-- **On the exactness region the affine envelope is tight at zero.** If every accumulation step is
exact (no rounding — e.g. when each step satisfies Sterbenz's exponent condition), the fp32 left fold
equals the exact running sum, with zero error. -/
theorem fp32Foldl_eq_sum_of_exact (acc : ℝ) (xs : List ℝ) (h : Fp32FoldlExact acc xs) :
    fp32Foldl acc xs = acc + xs.sum := by
  induction xs generalizing acc with
  | nil => simp [fp32Foldl]
  | cons x xs ih =>
    obtain ⟨hx, htail⟩ := h
    simp only [fp32Foldl, List.sum_cons]
    rw [hx, ih (acc + x) htail]; ring

/-- On the exactness region, the fp32 sum of centered data is exactly zero — the cancellation term
vanishes (the affine envelope is tight), matching the exact subtracted term. -/
theorem cancellation_term_zero_of_exact (c : List ℝ) (d : ℝ) (hcentered : c.sum = 0)
    (hexact : Fp32FoldlExact 0 c) : (fp32Foldl 0 c / d) ^ 2 = 0 := by
  rw [fp32Foldl_eq_sum_of_exact 0 c hexact, hcentered]
  simp
