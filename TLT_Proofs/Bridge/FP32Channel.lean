/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import NN.Floats.NeuralFloat.Core
import NN.Floats.FP32.Core
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
