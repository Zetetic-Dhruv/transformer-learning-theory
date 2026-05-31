/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import NN.Floats.NeuralFloat.Core
import NN.Floats.FP32.Core
import NN.Floats.FP32.Notation
import NN.Floats.IEEEExec.ErrorBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# A relative bound for the binary32 unit-in-the-last-place

Foundational lemma toward the IEEE-fp32 / ℝ rounding-error channel: the base-2 power at one below
the magnitude of `x` is at most `|x|`. This is the standard `bpow(mag x − 1) ≤ |x|` magnitude bound,
the missing piece that turns TorchLean's `neuralUlp` into a relative bound on the normal range.

## Main result

- `neuralBpow_magnitude_sub_one_le_abs` — `neuralBpow binaryRadix (neuralMagnitude binaryRadix x − 1)
  ≤ |x|` for `x ≠ 0`.
-/

open TorchLean.Floats

/-- The standard binary radix coerces to `2 : ℝ`. -/
private lemma binaryRadix_toReal_eq : binaryRadix.toReal = 2 := by
  simp [NeuralRadix.toReal, binaryRadix]

/-- `2 ^ (mag x − 1) ≤ |x|` for `x ≠ 0`, where `mag x = ⌊log₂|x|⌋ + 1`. -/
theorem neuralBpow_magnitude_sub_one_le_abs (x : ℝ) (hx : x ≠ 0) :
    neuralBpow binaryRadix (neuralMagnitude binaryRadix x - 1) ≤ |x| := by
  simp only [neuralBpow, neuralMagnitude, binaryRadix_toReal_eq, if_neg hx, add_sub_cancel_right]
  calc (2 : ℝ) ^ (⌊Real.log |x| / Real.log 2⌋ : ℤ)
      = (2 : ℝ) ^ ((⌊Real.log |x| / Real.log 2⌋ : ℤ) : ℝ) := (Real.rpow_intCast 2 _).symm
    _ ≤ (2 : ℝ) ^ (Real.log |x| / Real.log 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.floor_le _)
    _ = |x| := Real.rpow_logb (by norm_num) (by norm_num) (abs_pos.mpr hx)

/-- The FLT exponent function on its normal branch: `max (e − prec) emin = e − prec` when
`emin ≤ e − prec`. -/
private lemma FLTExp_eq_sub_of_le {emin prec e : ℤ} (h : emin ≤ e - prec) :
    FLTExp emin prec e = e - prec := by
  rw [FLTExp]; exact max_eq_left h

/-- `bpow` is additive in the exponent. -/
private lemma neuralBpow_add (β : NeuralRadix) (a b : ℤ) :
    neuralBpow β (a + b) = neuralBpow β a * neuralBpow β b := by
  simp only [neuralBpow, zpow_add₀ (NeuralRadix.ne_zero β)]

/-- **Relative ULP bound on the normal range.** For a normal `x` (`mag x ≥ −125`, i.e.
`|x| ≥ 2⁻¹²⁶`), the binary32 unit-in-the-last-place is at most `2⁻²³·|x|`. This is the crux that
turns `fp32Round_abs_error` into a relative envelope (hence `LocalAddBound` under normal range). -/
theorem neuralUlp_le_rel_on_normal (x : ℝ) (hx : x ≠ 0)
    (hnorm : (-125 : ℤ) ≤ neuralMagnitude binaryRadix x) :
    neuralUlp binaryRadix fexp32 x TrainingPhase.forward
      ≤ neuralBpow binaryRadix (-23) * |x| := by
  simp only [neuralUlp, if_neg hx, neuralCexp, fexp32, TrainingPhase.requiresHighPrecision,
    Bool.false_eq_true, if_false,
    FLTExp_eq_sub_of_le (by linarith : (-149 : ℤ) ≤ neuralMagnitude binaryRadix x - 24)]
  calc neuralBpow binaryRadix (neuralMagnitude binaryRadix x - 24)
      = neuralBpow binaryRadix (-23) * neuralBpow binaryRadix (neuralMagnitude binaryRadix x - 1) := by
        rw [← neuralBpow_add]; congr 1; ring
    _ ≤ neuralBpow binaryRadix (-23) * |x| :=
        mul_le_mul_of_nonneg_left (neuralBpow_magnitude_sub_one_le_abs x hx)
          (neuralBpow.nonneg binaryRadix (-23))

open TorchLean.Floats.IEEE754.IEEE32Exec

/-- `bpow(−1) = 1/2`. -/
private lemma neuralBpow_neg_one : neuralBpow binaryRadix (-1) = 1 / 2 := by
  simp only [neuralBpow, binaryRadix_toReal_eq]; norm_num

/-- `bpow(−24) = bpow(−23)/2`. -/
private lemma neuralBpow_half :
    neuralBpow binaryRadix (-24) = neuralBpow binaryRadix (-23) / 2 := by
  show neuralBpow binaryRadix (-23 + -1) = neuralBpow binaryRadix (-23) / 2
  rw [neuralBpow_add, neuralBpow_neg_one]; ring

/-- **Normal-range add bound.** When `a + b` is normal, fp32-rounding `a + b` is within
`2⁻²⁴·(|a|+|b|)` of `a + b` — the `LocalAddBound` envelope, valid on the normal range. -/
theorem fp32_addBound_on_normal (a b : ℝ) (hab : a + b ≠ 0)
    (hnorm : (-125 : ℤ) ≤ neuralMagnitude binaryRadix (a + b)) :
    |fp32Round (a + b) - (a + b)| ≤ neuralBpow binaryRadix (-24) * (|a| + |b|) := by
  calc |fp32Round (a + b) - (a + b)|
      ≤ eps₃₂ (a + b) := fp32Round_abs_error (a + b)
    _ = neuralUlp binaryRadix fexp32 (a + b) TrainingPhase.forward / 2 := by
        simp only [eps₃₂, eps32, ulp32]
    _ ≤ neuralBpow binaryRadix (-23) * |a + b| / 2 := by
        gcongr
        exact neuralUlp_le_rel_on_normal (a + b) hab hnorm
    _ = neuralBpow binaryRadix (-24) * |a + b| := by rw [neuralBpow_half]; ring
    _ ≤ neuralBpow binaryRadix (-24) * (|a| + |b|) :=
        mul_le_mul_of_nonneg_left (abs_add_le a b) (neuralBpow.nonneg binaryRadix (-24))

/-- The fp32 (round-to-nearest) right-fold sum of a list of reals: each partial sum is rounded. -/
noncomputable def fp32Sum : List ℝ → ℝ
  | [] => 0
  | x :: xs => fp32Round (x + fp32Sum xs)

/-- Every accumulation step `x + fp32Sum xs` lands in the binary32 normal range. -/
def Fp32SumNormal : List ℝ → Prop
  | [] => True
  | x :: xs => (x + fp32Sum xs ≠ 0 ∧ (-125 : ℤ) ≤ neuralMagnitude binaryRadix (x + fp32Sum xs))
               ∧ Fp32SumNormal xs

/-- The accumulated rounding-error budget of `fp32Sum`. -/
noncomputable def fp32SumErrorBudget : List ℝ → ℝ
  | [] => 0
  | x :: xs => neuralBpow binaryRadix (-24) * (|x| + |fp32Sum xs|) + fp32SumErrorBudget xs

/-- **Normal-range summation enclosure.** When every accumulation step stays in the binary32 normal
range, the fp32 fold-sum differs from the exact sum by at most the accumulated rounding-error budget.
This is the fp32-summation channel bound the attention score (a dot product) performs — derived from
the per-step bound `fp32_addBound_on_normal` by induction, *without* TorchLean's unconditional
`dotTreeResult_enclosure` (which fp32 cannot satisfy). -/
theorem fp32Sum_error_le :
    ∀ xs : List ℝ, Fp32SumNormal xs → |fp32Sum xs - xs.sum| ≤ fp32SumErrorBudget xs := by
  intro xs
  induction xs with
  | nil => intro _; simp [fp32Sum, fp32SumErrorBudget]
  | cons x xs ih =>
    intro h
    obtain ⟨⟨hne, hnorm⟩, htail⟩ := h
    calc |fp32Sum (x :: xs) - (x :: xs).sum|
        = |(fp32Round (x + fp32Sum xs) - (x + fp32Sum xs)) + (fp32Sum xs - xs.sum)| := by
          simp only [fp32Sum, List.sum_cons]; congr 1; ring
      _ ≤ |fp32Round (x + fp32Sum xs) - (x + fp32Sum xs)| + |fp32Sum xs - xs.sum| := abs_add_le _ _
      _ ≤ neuralBpow binaryRadix (-24) * (|x| + |fp32Sum xs|) + fp32SumErrorBudget xs := by
          gcongr
          · exact fp32_addBound_on_normal x (fp32Sum xs) hne hnorm
          · exact ih htail
      _ = fp32SumErrorBudget (x :: xs) := by simp [fp32SumErrorBudget]
