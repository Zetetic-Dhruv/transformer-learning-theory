/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Fp32.ExpConeError

/-!
# The tempered float cone (TD5, the numerical leg)

The tempered design law's `β`-axis raises the logits to `β·s`; in IEEE32 execution this enlarges the
range-reduction envelope `rrρ`, and the literal `exp`-on-cone error bound `exec32_exp_error_on_cone` is valid
only while `rrρ` stays in the cone regime `rrρ T ≤ 1/8`. Since `rrρ` is affine and increasing in its
argument `T` (the logit magnitude), the regime is an interval `T ≤ Tmax`, and at sharpness `β` with logit
magnitude bounded by `S` it is `β ≤ Tmax / S =: βmax`.

* `Tmax` / `betaMax`: the cone ceiling. `Tmax` is the largest logit magnitude and `βmax = Tmax/S` the
  largest sharpness for which the literal `exp` cone bound holds. The certified region is `[0, βmax]`.
* `rrρ_Tmax` / `rrρ_le_of_le_Tmax`: the range-reduction envelope hits `1/8` exactly at `Tmax`, hence stays
  `≤ 1/8` on `[·, Tmax]`.
* `δexpCone_temperedLogit_mono`: the tempered `exp`-cone envelope `δexpCone (β·S) η` is monotone in `β`
  (`TD5_envelope_monotone`). More sharpness gives a larger numerical envelope; the bound never diverges.
* `temperedExpCone_certified`: the certified region (`TD5_certified_region`). On the cone `β ≤ βmax`, the
  literal `IEEE32Exec.exp` of a tempered logit matches the ideal `Real.exp` within `δexpCone (β·S) η`.

All results use `δexpCone`/`rrρ`/`exec32_exp_error_on_cone` as defined elsewhere; the `β`-dependence enters
only through the scaled argument `β·S`.
-/

open TorchLean.Floats TorchLean.Floats.IEEE754 TorchLean.Floats.IEEE754.IEEE32Exec
open TorchLean.Floats.IEEE754.IEEE32Exec.Transcendentals TLT.ExpError

noncomputable section

namespace TLT.TemperedDesignLaw

/-- The largest logit magnitude in the `exp` cone regime: the `T` solving `rrρ T = 1/8`. -/
noncomputable def Tmax : ℝ := (1 / 8 - Real.log 2 / 2 ^ 48 - 2 ^ (-49 : ℤ)) / δinv

/-- The cone sharpness ceiling at logit-magnitude bound `S`: `βmax = Tmax / S`. The certified region for the
tempered float envelope is `[0, βmax]`. -/
noncomputable def betaMax (S : ℝ) : ℝ := Tmax / S

/-- The range-reduction anchor `δinv = (log 2)/10⁸` is positive. -/
lemma δinv_pos : 0 < δinv := by
  rw [δinv]
  exact div_pos (Real.log_pos one_lt_two) (by norm_num)

/-- The range-reduction envelope reaches `1/8` exactly at the cone ceiling `Tmax`. -/
lemma rrρ_Tmax : rrρ Tmax = 1 / 8 := by
  have hδ : δinv ≠ 0 := δinv_pos.ne'
  rw [rrρ, Tmax, div_mul_cancel₀ _ hδ]
  ring

/-- Below the cone ceiling the range-reduction envelope stays in the cone regime: `T ≤ Tmax ⟹ rrρ T ≤ 1/8`.
The affine envelope `rrρ` is increasing in `T` (slope `δinv > 0`). -/
lemma rrρ_le_of_le_Tmax {T : ℝ} (hT : T ≤ Tmax) : rrρ T ≤ 1 / 8 := by
  rw [← rrρ_Tmax, rrρ, rrρ]
  have hmul : T * δinv ≤ Tmax * δinv := mul_le_mul_of_nonneg_right hT δinv_pos.le
  linarith

/-- **The certificate region is sharp at the cone ceiling (TD8 numerical-cliff boundary).** The range
reduction stays in the cone regime EXACTLY up to `Tmax`: `rrρ T ≤ 1/8 ↔ T ≤ Tmax`. The `←` direction is
`rrρ_le_of_le_Tmax`; the strict `→` shows the certified region for the tempered float envelope ENDS at `Tmax`
Above `Tmax` the cone hypothesis is unsatisfiable, so the numerical certificate has a sharp boundary,
the `β`-axis analogue of the measurability cliff. -/
theorem rrρ_le_iff_le_Tmax {T : ℝ} : rrρ T ≤ 1 / 8 ↔ T ≤ Tmax := by
  rw [← rrρ_Tmax, rrρ, rrρ]
  constructor
  · intro h
    have hmul : T * δinv ≤ Tmax * δinv := by linarith
    exact le_of_mul_le_mul_right hmul δinv_pos
  · intro h
    have hmul : T * δinv ≤ Tmax * δinv := mul_le_mul_of_nonneg_right h δinv_pos.le
    linarith

/-- **`TD5_envelope_monotone`.** The tempered `exp`-cone envelope is monotone in the sharpness: for `S ≥ 0`
and `β₁ ≤ β₂`, `δexpCone (β₁·S) η ≤ δexpCone (β₂·S) η`. Only the range-reduction term `2·eᶭ·rrρ(β·S)` moves,
and it moves up. -/
lemma δexpCone_temperedLogit_mono {S η : ℝ} (hS : 0 ≤ S) {β₁ β₂ : ℝ} (h : β₁ ≤ β₂) :
    δexpCone (β₁ * S) η ≤ δexpCone (β₂ * S) η := by
  have hrr : rrρ (β₁ * S) ≤ rrρ (β₂ * S) := by
    rw [rrρ, rrρ]
    have hbS : β₁ * S ≤ β₂ * S := mul_le_mul_of_nonneg_right h hS
    have hmul : (β₁ * S) * δinv ≤ (β₂ * S) * δinv := mul_le_mul_of_nonneg_right hbS δinv_pos.le
    linarith
  rw [δexpCone, δexpCone]
  have hcoeff : (0 : ℝ) ≤ 2 * Real.exp η := by positivity
  linarith [mul_le_mul_of_nonneg_left hrr hcoeff]

/-- **`TD5_certified_region`.** On the cone `β ≤ βmax`, the literal `IEEE32Exec.exp` of a tempered logit `x`
(magnitude `≤ β·S`, upper bound `η ≤ ½`) matches the ideal `Real.exp` within the tempered envelope
`δexpCone (β·S) η`. Instantiates `exec32_exp_error_on_cone` at `T = β·S`, the cone hypothesis discharged from
`β ≤ βmax = Tmax/S`. -/
theorem temperedExpCone_certified (x : IEEE32Exec) (hfin : isFinite x = true)
    (hfinexp : isFinite (IEEE32Exec.exp x) = true) {β S η : ℝ} (hS : 0 < S) (hη2 : η ≤ 1 / 2)
    (hub : toReal x ≤ η) (hT : |toReal x| ≤ β * S) (hβ : β ≤ betaMax S) :
    |toReal (IEEE32Exec.exp x) - Real.exp (toReal x)| ≤ δexpCone (β * S) η := by
  refine exec32_exp_error_on_cone x hfin hfinexp η (β * S) hη2 hub hT (rrρ_le_of_le_Tmax ?_)
  calc β * S ≤ betaMax S * S := mul_le_mul_of_nonneg_right hβ hS.le
    _ = Tmax := by rw [betaMax, div_mul_cancel₀ _ hS.ne']

end TLT.TemperedDesignLaw
