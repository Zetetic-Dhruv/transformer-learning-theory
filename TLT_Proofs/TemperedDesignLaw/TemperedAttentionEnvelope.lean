/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.TemperedFloatCone
import TLT_Proofs.Bridge.Certificate.AttentionLiteralExecutedBinding

/-!
# The tempered attention envelope — monotonicity in the score bound (TD5)

The literal fp32 attention forward error `attnLiteralForwardError_onCone` bounds the executed head by the
closed form `rndLit … (δexpCone (2B'(1+u)) (2uB')) …`, where `B'` bounds the executed stabilized-logit
magnitude. On the sharpness axis the temperature scales the logits, so `B'` carries the sharpness: a larger
`B'` is a sharper (or larger-magnitude) score channel. This file establishes that the envelope is *monotone
increasing* in `B'` — sharper scores give a larger numerical envelope, never a divergence — by lifting the
monotonicity through each closed-form layer:

* `δexpCone_mono` — the exp-cone error is monotone in both the range-reduction argument `T` and the upper
  bound `η` (the product `eᶭ·rrρ T` is increasing in each, on `T ≥ 0`).
* `litTV_mono_δexp` — the softmax total-variation envelope is monotone in the exp atom `δ_exp` (its only
  `δ_exp` term is `2N·δ_exp/Dlo`).
* `rndLit_mono_δexp` — the literal rounding envelope is monotone in `δ_exp` (it enters through the two
  `litTV` occurrences; the score-rounding and value-budget terms are `δ_exp`-independent).
* `rndLit_temperedCone_mono` — composing the three, the cone envelope `rndLit … (δexpCone (2B'(1+u))
  (2uB')) …` is monotone in the score bound `B'`.

Everything is monotonicity of the *shipped* closed forms; no new envelope is introduced.
-/

open TLT.ExpError TLT.Fp32Attn TLT.Fp32AttnLit
open scoped BigOperators

noncomputable section

namespace TLT.TemperedDesignLaw

/-- The closed-form exp-cone error `δexpCone T η` is monotone in both arguments on `T ≥ 0`: the
range-reduction envelope `rrρ` is affine increasing and stays nonnegative for `T ≥ 0`, and `eᶭ` is
increasing, so the product `eᶭ·rrρ T` rises with both `T` and `η`. -/
lemma δexpCone_mono {T₁ T₂ η₁ η₂ : ℝ} (hT0 : 0 ≤ T₁) (hT : T₁ ≤ T₂) (hη : η₁ ≤ η₂) :
    δexpCone T₁ η₁ ≤ δexpCone T₂ η₂ := by
  rw [δexpCone, δexpCone]
  have hrr1 : 0 ≤ rrρ T₁ := by
    rw [rrρ]
    have hlog : 0 ≤ Real.log 2 := (Real.log_pos one_lt_two).le
    have h1 : 0 ≤ T₁ * δinv := mul_nonneg hT0 δinv_pos.le
    have h2 : 0 ≤ Real.log 2 / 2 ^ 48 := div_nonneg hlog (by positivity)
    have h3 : 0 ≤ (2 : ℝ) ^ (-49 : ℤ) := by positivity
    linarith
  have hrrmono : rrρ T₁ ≤ rrρ T₂ := by
    rw [rrρ, rrρ]
    have := mul_le_mul_of_nonneg_right hT δinv_pos.le
    linarith
  have hrr2 : 0 ≤ rrρ T₂ := le_trans hrr1 hrrmono
  have hexpmono : Real.exp η₁ ≤ Real.exp η₂ := Real.exp_le_exp.mpr hη
  have hprod : 2 * Real.exp η₁ * rrρ T₁ ≤ 2 * Real.exp η₂ * rrρ T₂ := by
    have ha : (0 : ℝ) ≤ 2 * Real.exp η₁ := by positivity
    have hstep1 : 2 * Real.exp η₁ * rrρ T₁ ≤ 2 * Real.exp η₁ * rrρ T₂ :=
      mul_le_mul_of_nonneg_left hrrmono ha
    have hb : 2 * Real.exp η₁ ≤ 2 * Real.exp η₂ := by linarith
    have hstep2 : 2 * Real.exp η₁ * rrρ T₂ ≤ 2 * Real.exp η₂ * rrρ T₂ :=
      mul_le_mul_of_nonneg_right hb hrr2
    linarith
  linarith [hprod]

/-- The literal softmax total-variation envelope `litTV` is monotone in the exp atom `δ_exp`: its sole
`δ_exp` dependence is the term `2N·δ_exp/Dlo`, increasing for `Dlo > 0`. -/
lemma litTV_mono_δexp {N : ℕ} {Dlo E_lit δ₁ δ₂ : ℝ} (hDlo : 0 < Dlo) (hδ : δ₁ ≤ δ₂) :
    litTV N Dlo δ₁ E_lit ≤ litTV N Dlo δ₂ E_lit := by
  rw [litTV, litTV]
  have hnum : 2 * ((N : ℝ) * δ₁) + u * (((N : ℝ) + 1) * E_lit) / (1 - (N : ℝ) * u)
            ≤ 2 * ((N : ℝ) * δ₂) + u * (((N : ℝ) + 1) * E_lit) / (1 - (N : ℝ) * u) := by
    have hNδ : (N : ℝ) * δ₁ ≤ (N : ℝ) * δ₂ := mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg N)
    linarith
  have hdiv : (2 * ((N : ℝ) * δ₁) + u * (((N : ℝ) + 1) * E_lit) / (1 - (N : ℝ) * u)) / Dlo
            ≤ (2 * ((N : ℝ) * δ₂) + u * (((N : ℝ) + 1) * E_lit) / (1 - (N : ℝ) * u)) / Dlo := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hDlo.le)
  linarith [hdiv]

/-- The literal rounding envelope `rndLit` is monotone in the exp atom `δ_exp`: it enters only through the
two `litTV (n+1) Dlo δ_exp E_lit` occurrences (the value-budget `rdotBudget` and score-rounding terms are
`δ_exp`-free), each monotone since `bVval ≥ 0` and `rdotBudget` is monotone in its argument. -/
lemma rndLit_mono_δexp {n d : ℕ} {B Λ scale Dlo E_lit δ₁ δ₂ : ℝ}
    (hB : 0 ≤ B) (hΛ0 : 0 ≤ Λ) (hnu : ((n + 1 : ℕ) : ℝ) * u < 1) (hdu : (d : ℝ) * u < 1)
    (hDlo : 0 < Dlo) (hδ : δ₁ ≤ δ₂) :
    rndLit n d B Λ scale Dlo δ₁ E_lit ≤ rndLit n d B Λ scale Dlo δ₂ E_lit := by
  rw [rndLit, rndLit]
  have hbV : 0 ≤ bVval d B Λ := by
    rw [bVval]
    have h1 := rdotBudget_nonneg hdu (mul_nonneg hB hΛ0)
    have h2 := mul_nonneg hB hΛ0
    linarith
  have htv : litTV (n + 1) Dlo δ₁ E_lit ≤ litTV (n + 1) Dlo δ₂ E_lit := litTV_mono_δexp hDlo hδ
  have harg : bVval d B Λ * (1 + litTV (n + 1) Dlo δ₁ E_lit)
            ≤ bVval d B Λ * (1 + litTV (n + 1) Dlo δ₂ E_lit) :=
    mul_le_mul_of_nonneg_left (by linarith) hbV
  have hterm1 : rdotBudget (n + 1) (bVval d B Λ * (1 + litTV (n + 1) Dlo δ₁ E_lit))
              ≤ rdotBudget (n + 1) (bVval d B Λ * (1 + litTV (n + 1) Dlo δ₂ E_lit)) :=
    rdotBudget_mono (by exact_mod_cast hnu) harg
  have hterm2 : bVval d B Λ * litTV (n + 1) Dlo δ₁ E_lit ≤ bVval d B Λ * litTV (n + 1) Dlo δ₂ E_lit :=
    mul_le_mul_of_nonneg_left htv hbV
  linarith [hterm1, hterm2]

/-- The literal cone envelope `rndLit … (δexpCone (2B'(1+u)) (2uB')) …` is monotone in the executed score
bound `B'`: both the range-reduction argument `2B'(1+u)` and the cone upper bound `2uB'` rise with `B'`, so
`δexpCone` rises (`δexpCone_mono`), and the envelope rises through it (`rndLit_mono_δexp`). The score bound
`B'` carries the sharpness on the temperature axis, so this is the statement that a sharper score channel
gives a larger — but never divergent — numerical envelope. -/
lemma rndLit_temperedCone_mono {n d : ℕ} {B Λ scale Dlo E_lit B'₁ B'₂ : ℝ}
    (hB : 0 ≤ B) (hΛ0 : 0 ≤ Λ) (hnu : ((n + 1 : ℕ) : ℝ) * u < 1) (hdu : (d : ℝ) * u < 1)
    (hDlo : 0 < Dlo) (hB'0 : 0 ≤ B'₁) (hB' : B'₁ ≤ B'₂) :
    rndLit n d B Λ scale Dlo (δexpCone (2 * B'₁ + 2 * u * B'₁) (2 * u * B'₁)) E_lit
      ≤ rndLit n d B Λ scale Dlo (δexpCone (2 * B'₂ + 2 * u * B'₂) (2 * u * B'₂)) E_lit := by
  apply rndLit_mono_δexp hB hΛ0 hnu hdu hDlo
  apply δexpCone_mono
  · nlinarith [u_nonneg, hB'0]
  · nlinarith [u_nonneg, hB', hB'0]
  · nlinarith [u_nonneg, hB']

open Spec Tensor TorchLean.Floats.IEEE754 TorchLean.Floats.IEEE754.IEEE32Exec in
/-- **The certified tempered attention region.** The literal fp32 attention forward error on a score row
bounded by `B'`, with the opaque cone-regime premise of `attnLiteralForwardError_onCone`
(`rrρ (2B'(1+u)) ≤ 1/8`) replaced by the checkable score-bound ceiling `B' ≤ Tmax / (2(1+u))`. Below the
ceiling the range-reduction argument `2B'(1+u)` stays under the cone ceiling `Tmax`, so the affine
range-reduction envelope stays in the cone (`rrρ_le_of_le_Tmax`), the per-logit exp atom is discharged on
the cone, and the executed head is within the closed form `rndLit … (δexpCone (2B'(1+u)) (2uB')) …` of the
ideal head — with no analytic exp-accuracy premise. `Tmax` is the exact cone ceiling; the score bound `B'`
carries the sharpness on the temperature axis, so `B' ≤ Tmax / (2(1+u))` is the certified sharpness window. -/
theorem litAttnForwardError_temperedCone {n d : ℕ} {h1 h2 : (n + 1) ≠ 0}
    (ctx : Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2)
    (Yt : Fin (n + 1) → Fin d → IEEE32Exec) (Wt : Fin d → Fin d → IEEE32Exec)
    (hQ : ctx.Q = Spec.matrixTensor Yt) (hK : ctx.K = Spec.matrixTensor Yt)
    (hV : ctx.V = matMulSpec (Spec.matrixTensor Yt) (Spec.matrixTensor Wt)) (hmask : ctx.mask = none)
    (F : Fin (n + 1) → Tensor IEEE32Exec (.dim (n + 1) .scalar)) {Dlo E_lit : ℝ}
    (hN : ExecAttnLitNormal ctx Yt Wt F Dlo E_lit) {B Λ B' : ℝ}
    (hB : 0 ≤ B) (hΛ0 : 0 ≤ Λ) (hc : 0 < toReal (litScaleFactor d : IEEE32Exec))
    (hX : ∀ a k, |toReal (Yt a k)| ≤ B) (hW : ∀ j, ∑ k, |toReal (Wt k j)| ≤ Λ)
    (hnu : ((n + 1 : ℕ) : ℝ) * u < 1) (hdu : (d : ℝ) * u < 1) (hE : 0 ≤ E_lit)
    (hscore : ∀ i k, |toReal (Tensor.vecGet (F i) k)| ≤ B')
    (hη2 : 2 * u * B' ≤ 1 / 2)
    (hB'max : B' ≤ Tmax / (2 * (1 + u))) :
    dist (execAttnLit ctx) (attnHead (1 / toReal (litScaleFactor d : IEEE32Exec))
        (fun a b => toReal (Wt a b)) (fun a b => toReal (Yt a b)))
      ≤ rndLit n d B Λ (1 / toReal (litScaleFactor d : IEEE32Exec)) Dlo
          (δexpCone (2 * B' + 2 * u * B') (2 * u * B')) E_lit := by
  have hu := u_nonneg
  have hupos : (0 : ℝ) < 2 * (1 + u) := by linarith
  have hcone : 2 * B' + 2 * u * B' ≤ Tmax := by
    have hmul : B' * (2 * (1 + u)) ≤ Tmax := (le_div_iff₀ hupos).mp hB'max
    nlinarith [hmul]
  exact attnLiteralForwardError_onCone ctx Yt Wt hQ hK hV hmask F hN hB hΛ0 hc hX hW hnu hdu hE
    hscore hη2 (rrρ_le_of_le_Tmax hcone)

end TLT.TemperedDesignLaw
