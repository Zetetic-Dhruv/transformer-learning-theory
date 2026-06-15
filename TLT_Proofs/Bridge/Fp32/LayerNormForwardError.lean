/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Fp32.RelativeUlpAndSummation
import TLT_Proofs.Bridge.Lipschitz.LayerNormLipschitz

/-!
# The layer-norm literal forward error

The third per-sub-layer literal forward error (after attention `attnLiteralForwardError` and the FFN
`ffnExec_forward_error`). Layer-norm is `(x − mean)/std · γ + β`; its only structural novelty over the
FFN is the **division** by the standard deviation. The whole leg therefore rides on:

* `abs_div_sub_div_le`: the perturbed-quotient bound `|a'/b' − a/b| ≤ |a'−a|/b' + |a|·|b'−b|/(b'·b)`,
  a real-analysis fact;
* the rounding atoms for the surrounding operations (`fp32Round_abs_error`, `fp32Sum_error_le`, the sqrt atom),
  abstracted as per-op error budgets `ρround / ρm / ρs`;
* the verified `ε = 1e-6` regulariser, which floors `rowStdCoord ≥ √ε` (`rowStdCoord_ge_sqrt_eps`), so the
  division denominator is bounded below.

The forward error then telescopes through the quotient exactly as the FFN telescoped through its two
matmuls: a coordinate bound lifted to the sup norm. It feeds `block3_forward_error` beside attention + FFN.
-/

namespace TLT.Fp32LN

open TLT TorchLean.Floats.IEEE754.IEEE32Exec

/-- **The perturbed-quotient bound** (the layer-norm leg's one new sub-argument). For positive
denominators, perturbing both numerator and denominator of a quotient costs the numerator perturbation
scaled by `1/b'` plus the denominator perturbation scaled by `|a|/(b'·b)`. Reusable real-analysis fact;
here it carries the `/std` of layer-norm. -/
theorem abs_div_sub_div_le {a a' b b' : ℝ} (hb : 0 < b) (hb' : 0 < b') :
    |a' / b' - a / b| ≤ |a' - a| / b' + |a| * |b' - b| / (b' * b) := by
  have hbb : (0 : ℝ) < b' * b := mul_pos hb' hb
  have key : a' / b' - a / b = (a' - a) / b' + a * (b - b') / (b' * b) := by
    field_simp; ring
  rw [key]
  calc |(a' - a) / b' + a * (b - b') / (b' * b)|
      ≤ |(a' - a) / b'| + |a * (b - b') / (b' * b)| := abs_add_le _ _
    _ = |a' - a| / b' + |a| * |b' - b| / (b' * b) := by
        rw [abs_div, abs_of_pos hb', abs_div, abs_of_pos hbb, abs_mul, abs_sub_comm b b']

/-- **The executed (starred) layer-norm**, given the executed per-row mean `meanE` and std `stdE`: center,
divide by the executed std, scale by `γ`, shift by `β`, and round once. The mean/std reductions (their own
`fp32Sum`/`sqrt` rounding, budgeted by `ρm`/`ρs` below) are supplied as inputs; this composite is the
affine-and-round the layer applies on top. -/
noncomputable def lnStarExec {s d : ℕ} (γ β : Fin d → ℝ) (meanE stdE : Fin s → ℝ)
    (X : Fin s → Fin d → ℝ) : Fin s → Fin d → ℝ :=
  fun i j => fp32Round ((X i j - meanE i) / stdE i * γ j + β j)

/-- **The layer-norm literal forward error.** Given the per-op rounding budgets (`ρround` for the final
affine round, `ρm` for the mean reduction (`fp32Sum`), `ρs` for the std (`fp32Sum` + sqrt atom)) and the
score bound `B`, `|γ| ≤ Cγ`, the executed layer-norm is within
`ρround + Cγ·(ρm/√ε + 2B·ρs/ε)` of `layerNormCoord`. The `ε = 1e-6` regulariser floors both standard
deviations at `√ε` (`rowStdCoord_ge_sqrt_eps` + `hstdE`), so the perturbed quotient `abs_div_sub_div_le`
controls the `/std` with denominators `≥ ε`. The mean/std reductions are supplied as budgets `ρm`/`ρs`,
dischargeable from `fp32Sum_error_le` and the sqrt atom. The sup norm converts to `dist` (`dist_eq_norm`)
to feed `block3_forward_error` alongside attention and FFN. -/
theorem lnExec_forward_error {s d : ℕ} (γ β : Fin d → ℝ) (meanE stdE : Fin s → ℝ)
    (X : Fin s → Fin d → ℝ) {B Cγ ρround ρm ρs : ℝ}
    (hB : 0 ≤ B) (hCγ0 : 0 ≤ Cγ) (hρm : 0 ≤ ρm) (hρs : 0 ≤ ρs) (hρr : 0 ≤ ρround)
    (hX : ∀ i k, |X i k| ≤ B) (hCγ : ∀ j, |γ j| ≤ Cγ)
    (hround : ∀ i j,
      |lnStarExec γ β meanE stdE X i j - ((X i j - meanE i) / stdE i * γ j + β j)| ≤ ρround)
    (hmean : ∀ i, |meanE i - rowMeanCoord i X| ≤ ρm) (hmeanB : ∀ i, |rowMeanCoord i X| ≤ B)
    (hstd : ∀ i, |stdE i - rowStdCoord i X| ≤ ρs)
    (hstdE : ∀ i, Real.sqrt Numbers.epsilon ≤ stdE i) :
    ‖lnStarExec γ β meanE stdE X - layerNormCoord γ β X‖
      ≤ ρround + Cγ * (ρm / Real.sqrt Numbers.epsilon + 2 * B * ρs / Numbers.epsilon) := by
  have heps : (0 : ℝ) < Numbers.epsilon := numbers_epsilon_real_pos
  have hsqeps : (0 : ℝ) < Real.sqrt Numbers.epsilon := Real.sqrt_pos.mpr heps
  have hbound : 0 ≤ ρround + Cγ * (ρm / Real.sqrt Numbers.epsilon + 2 * B * ρs / Numbers.epsilon) := by
    have h1 : (0 : ℝ) ≤ ρm / Real.sqrt Numbers.epsilon + 2 * B * ρs / Numbers.epsilon := by positivity
    positivity
  refine (pi_norm_le_iff_of_nonneg hbound).mpr (fun i => ?_)
  refine (pi_norm_le_iff_of_nonneg hbound).mpr (fun j => ?_)
  rw [Real.norm_eq_abs, Pi.sub_apply, Pi.sub_apply]
  have hstdEi : Real.sqrt Numbers.epsilon ≤ stdE i := hstdE i
  have hstdIi : Real.sqrt Numbers.epsilon ≤ rowStdCoord i X := rowStdCoord_ge_sqrt_eps i X
  have hstdEpos : 0 < stdE i := lt_of_lt_of_le hsqeps hstdEi
  have hstdIpos : 0 < rowStdCoord i X := rowStdCoord_pos i X
  have hquot : |(X i j - meanE i) / stdE i - (X i j - rowMeanCoord i X) / rowStdCoord i X|
      ≤ ρm / Real.sqrt Numbers.epsilon + 2 * B * ρs / Numbers.epsilon := by
    refine (abs_div_sub_div_le hstdIpos hstdEpos).trans ?_
    have hnum : |(X i j - meanE i) - (X i j - rowMeanCoord i X)| ≤ ρm := by
      rw [show (X i j - meanE i) - (X i j - rowMeanCoord i X) = rowMeanCoord i X - meanE i by ring,
        abs_sub_comm]
      exact hmean i
    have hXmean : |X i j - rowMeanCoord i X| ≤ 2 * B := by
      have h := abs_sub_le (X i j) 0 (rowMeanCoord i X)
      simp only [sub_zero, zero_sub, abs_neg] at h
      linarith [hX i j, hmeanB i]
    have hden : |stdE i - rowStdCoord i X| ≤ ρs := hstd i
    have hdenom : Numbers.epsilon ≤ stdE i * rowStdCoord i X := by
      have h := mul_le_mul hstdEi hstdIi hsqeps.le (le_trans hsqeps.le hstdEi)
      rwa [Real.mul_self_sqrt heps.le] at h
    have hterm1 : |(X i j - meanE i) - (X i j - rowMeanCoord i X)| / stdE i
        ≤ ρm / Real.sqrt Numbers.epsilon := by gcongr
    have hterm2 : |X i j - rowMeanCoord i X| * |stdE i - rowStdCoord i X| / (stdE i * rowStdCoord i X)
        ≤ 2 * B * ρs / Numbers.epsilon := by gcongr
    linarith
  have haffeq : (X i j - meanE i) / stdE i * γ j + β j - layerNormCoord γ β X i j
      = ((X i j - meanE i) / stdE i - (X i j - rowMeanCoord i X) / rowStdCoord i X) * γ j := by
    rw [layerNormCoord]; ring
  have hsecond : |(X i j - meanE i) / stdE i * γ j + β j - layerNormCoord γ β X i j|
      ≤ Cγ * (ρm / Real.sqrt Numbers.epsilon + 2 * B * ρs / Numbers.epsilon) := by
    rw [haffeq, abs_mul]
    calc |(X i j - meanE i) / stdE i - (X i j - rowMeanCoord i X) / rowStdCoord i X| * |γ j|
        ≤ (ρm / Real.sqrt Numbers.epsilon + 2 * B * ρs / Numbers.epsilon) * Cγ := by
          gcongr
          exact hCγ j
      _ = Cγ * (ρm / Real.sqrt Numbers.epsilon + 2 * B * ρs / Numbers.epsilon) := by ring
  calc |lnStarExec γ β meanE stdE X i j - layerNormCoord γ β X i j|
      ≤ |lnStarExec γ β meanE stdE X i j - ((X i j - meanE i) / stdE i * γ j + β j)|
        + |(X i j - meanE i) / stdE i * γ j + β j - layerNormCoord γ β X i j| := abs_sub_le _ _ _
    _ ≤ ρround + Cγ * (ρm / Real.sqrt Numbers.epsilon + 2 * B * ρs / Numbers.epsilon) :=
        add_le_add (hround i j) hsecond

end TLT.Fp32LN
