/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Fp32.ExpExecutedValue
import TLT_Proofs.Bridge.Fp32.RelativeUlpAndSummation
import TLT_Proofs.Capacity.Discretization.Float32IsDyadic

/-!
# Executed `Exec32.exp` on the softmax cone — discharging `hδ` to a closed-form theorem

The single-head literal forward error `attnLiteralForwardError` takes the per-input `exp`-accuracy
premise `hδ` as data. On the **softmax cone** — the post-shift logits the stabilization already forces
into `[−T, η]` — the literal `IEEE32Exec.exp`'s branch trichotomy collapses (overflow impossible,
underflow benign, main branch uniformly bounded), so `δ_exp` becomes a definition and `hδ` a theorem.

This file builds the **cone-free** layer first: the range-reduction `let`-bindings `rrK`/`rrF` named as
definitions (so the branch equation is a rewrite, not an existential), and the round-to-even residual
bound that pins `|rrF x| ≤ 2⁴⁷` — the only new mathematics; the rest routes through shipped lemmas.
-/

namespace TLT.ExpError

open TorchLean.Floats TorchLean.Floats.IEEE754 TorchLean.Floats.IEEE754.IEEE32Exec
open TorchLean.Floats.IEEE754.IEEE32Exec.Transcendentals

/-- **Round-to-even residual bound.** For `d > 0`, the ties-to-even rounded quotient leaves a residual
of magnitude at most `d/2`: `2·|n − roundQuotEvenInt n d · d| ≤ d`. This is the range-reduction bound —
applied at `d = 2⁴⁸` it pins `|rrF x| ≤ 2⁴⁷`, the `hf` hypothesis of `exec32_exp_error`. -/
lemma two_mul_abs_roundQuotEvenInt_residual_le (n d : ℤ) (hd : 0 < d) :
    2 * |n - roundQuotEvenInt n d * d| ≤ d := by
  have hdne : d ≠ 0 := ne_of_gt hd
  set q := Int.ediv n d with hqdef
  set r := Int.emod n d with hrdef
  have hr0 : 0 ≤ r := Int.emod_nonneg n hdne
  have hrd : r < d := Int.emod_lt_of_pos n hd
  have hn : d * q + r = n := Int.ediv_add_emod n d
  have key : n - q * d = r := by rw [mul_comm q d, ← hn]; ring
  have key2 : n - (q + 1) * d = r - d := by rw [← hn]; ring
  unfold roundQuotEvenInt
  simp only [hqdef.symm, hrdef.symm]
  split_ifs with h1 h2 h3
  · rw [key, abs_of_nonneg hr0]; omega
  · rw [key2, abs_of_nonpos (by omega), neg_sub]; omega
  · rw [key, abs_of_nonneg hr0]; omega
  · rw [key2, abs_of_nonpos (by omega), neg_sub]; omega

/-- The range reduction's integer part `k`, copied verbatim from `IEEE32Exec.exp`'s `let`-bindings. -/
def rrK (x : IEEE32Exec) : ℤ :=
  match toDyadic? x with
  | none => 0
  | some dx => roundDivPow2EvenInt (fixedMul (fixedOfDyadic dx) fixedInvLn2) fixedScale

/-- The range reduction's fractional part `fFixed ∈ [−½,½]·2⁴⁸`, copied verbatim from `IEEE32Exec.exp`. -/
def rrF (x : IEEE32Exec) : ℤ :=
  match toDyadic? x with
  | none => 0
  | some dx =>
      let yFixed := fixedMul (fixedOfDyadic dx) fixedInvLn2
      yFixed - roundDivPow2EvenInt yFixed fixedScale * pow2Int fixedScale

/-- **E1 — the branch-equation gate (unfolding decoupled from positivity).** On a finite input with
`pFixed = evalExp2Poly (rrF x) > 0`, the literal `IEEE32Exec.exp` is the main-branch round with the named
reduction `rrK`/`rrF`. Conclusion verbatim = `hbranch` of the shipped `exec32_exp_error`. The proof is the
`add_eq_roundDyadicToIEEE32_of_toDyadic?` idiom (`Exec32:675`) instantiated for `exp`: kill the
finiteness guards, supply `toDyadic? = some`, `simp` with `zeta` to crush the `let`s, close the final
`if` with `hpos`. -/
theorem exp_eq_round_of_finite (x : IEEE32Exec) (hx : isFinite x = true)
    (hpos : ¬ (evalExp2Poly (rrF x) ≤ 0)) :
    IEEE32Exec.exp x
      = roundDyadicToIEEE32 ⟨false, (evalExp2Poly (rrF x)).natAbs, rrK x - fixedScaleInt⟩ := by
  obtain ⟨dx, hd⟩ : ∃ dx, toDyadic? x = some dx := by
    rcases Option.eq_none_or_eq_some (toDyadic? x) with h | h
    · exact absurd (isFinite_eq_false_of_toDyadic?_eq_none x h) (by simp [hx])
    · exact h
  have hNaN : isNaN x = false := isNaN_eq_false_of_isFinite_eq_true x hx
  have hInf : isInf x = false := isInf_eq_false_of_isFinite_eq_true x hx
  have hposF : ¬ (evalExp2Poly (fixedMul (fixedOfDyadic dx) fixedInvLn2
      - roundDivPow2EvenInt (fixedMul (fixedOfDyadic dx) fixedInvLn2) fixedScale * pow2Int fixedScale)
      ≤ 0) := by simpa only [rrF, hd] using hpos
  unfold IEEE32Exec.exp
  simp only [rrK, rrF, hd, hNaN, hInf, Bool.false_eq_true, if_false, hposF]

/-- `|rrF x| ≤ 2⁴⁷` on a finite input — the range-reduction residual bound at `d = 2⁴⁸`, the `hf`
premise of `exec32_exp_error`. -/
theorem abs_rrF_le (x : IEEE32Exec) (hx : isFinite x = true) : |(rrF x : ℝ)| ≤ 2 ^ 47 := by
  obtain ⟨dx, hd⟩ : ∃ dx, toDyadic? x = some dx := by
    rcases Option.eq_none_or_eq_some (toDyadic? x) with h | h
    · exact absurd (isFinite_eq_false_of_toDyadic?_eq_none x h) (by simp [hx])
    · exact h
  have hrrF : rrF x = fixedMul (fixedOfDyadic dx) fixedInvLn2
      - roundDivPow2EvenInt (fixedMul (fixedOfDyadic dx) fixedInvLn2) fixedScale * pow2Int fixedScale := by
    simp only [rrF, hd]
  have hconv : roundDivPow2EvenInt (fixedMul (fixedOfDyadic dx) fixedInvLn2) fixedScale
      = roundQuotEvenInt (fixedMul (fixedOfDyadic dx) fixedInvLn2) (pow2Int fixedScale) := rfl
  have hp48 : pow2Int fixedScale = (2 : ℤ) ^ 48 := by
    simp only [pow2Int, fixedScale, pow2_eq_two_pow]; norm_num
  have hp : 0 < pow2Int fixedScale := by rw [hp48]; positivity
  have hb := two_mul_abs_roundQuotEvenInt_residual_le (fixedMul (fixedOfDyadic dx) fixedInvLn2)
      (pow2Int fixedScale) hp
  rw [← hconv, ← hrrF, hp48] at hb
  have hZ : |rrF x| ≤ (2 : ℤ) ^ 47 := by
    have h2 : (2 : ℤ) ^ 48 = 2 * 2 ^ 47 := by ring
    rw [h2] at hb; omega
  rw [← Int.cast_abs]
  calc ((|rrF x| : ℤ) : ℝ) ≤ (((2 : ℤ) ^ 47 : ℤ) : ℝ) := by exact_mod_cast hZ
    _ = 2 ^ 47 := by norm_num

/-- **E2 — positivity of the reduced polynomial.** On a finite input, `evalExp2Poly (rrF x) > 0`:
`|rrF x| ≤ 2⁴⁷` (above) ⇒ via `evalExp2Poly_error`, `poly/2⁴⁸ ≥ e^(reduced·ln2) − 10⁻⁶ ≥ 7/10 − 10⁻⁶ > 0`,
using `e^(reduced·ln2) ≥ e^(−ln2/2) = 2^(−½) ≥ 7/10` (via `(e^(−ln2/2))² = ½` and `(7/10)² = 49/100 < ½`). -/
theorem evalExp2Poly_pos_of_reduced (x : IEEE32Exec) (hx : isFinite x = true) :
    0 < evalExp2Poly (rrF x) := by
  have hf := abs_rrF_le x hx
  have hL3 := evalExp2Poly_error (rrF x) hf
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- e^(reduced·ln2) ≥ e^(−ln2/2)
  have hge : -(Real.log 2) / 2 ≤ (rrF x : ℝ) / 2 ^ 48 * Real.log 2 := by
    have hlb : -(1 : ℝ) / 2 ≤ (rrF x : ℝ) / 2 ^ 48 := by
      rw [le_div_iff₀ (by positivity)]
      have := (abs_le.mp hf).1
      nlinarith [this]
    nlinarith [hlb, hlog2]
  -- e^(−ln2/2) ≥ 7/10  via  (e^(−ln2/2))² = ½
  have hsq : Real.exp (-(Real.log 2) / 2) ^ 2 = 1 / 2 := by
    rw [sq, ← Real.exp_add, show -(Real.log 2) / 2 + -(Real.log 2) / 2 = -Real.log 2 by ring,
      Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have hlow : (7 : ℝ) / 10 ≤ Real.exp (-(Real.log 2) / 2) :=
    by nlinarith [hsq, (Real.exp_pos (-(Real.log 2) / 2)).le]
  have hmono : Real.exp (-(Real.log 2) / 2) ≤ Real.exp ((rrF x : ℝ) / 2 ^ 48 * Real.log 2) :=
    Real.exp_le_exp.mpr hge
  have hpos_real : (0 : ℝ) < (evalExp2Poly (rrF x) : ℝ) / 2 ^ 48 := by
    have := (abs_le.mp hL3).1
    nlinarith [this, hlow, hmono]
  have hpos_int : (0 : ℝ) < (evalExp2Poly (rrF x) : ℝ) := by
    have heq : (evalExp2Poly (rrF x) : ℝ) = (evalExp2Poly (rrF x) : ℝ) / 2 ^ 48 * 2 ^ 48 := by
      field_simp
    rw [heq]; exact mul_pos hpos_real (by positivity)
  exact_mod_cast hpos_int

/-- The `1/ln2` fixed-point anchor error, folded with `ln2` (`fixedInvLn2_approx_inv_log_two ≤ 1/10⁸`). -/
noncomputable def δinv : ℝ := Real.log 2 / 10 ^ 8

/-- **C0 — the closed-form range-reduction envelope.** `T·δinv` (anchor) + `ln2/2⁴⁸` (split) + `2⁻⁴⁹`
(quant). A definition, not data. -/
noncomputable def rrρ (T : ℝ) : ℝ := T * δinv + Real.log 2 / 2 ^ 48 + 2 ^ (-49 : ℤ)

/-- **C0 — the closed-form `exp`-on-cone error.** `3u` (round) + `2·10⁻⁶` (polynomial) +
`2·e^η·rrρ T` (range reduction through the MVT). The `δ_exp` that retires `hδ`. -/
noncomputable def δexpCone (T η : ℝ) : ℝ :=
  3 * (2 : ℝ) ^ (-24 : ℤ) + 2 * (1 / 10 ^ 6) + 2 * Real.exp η * rrρ T

/-- **C1 (normal regime) — the `eps₃₂` cap.** For a normal value of magnitude `≤ 3`, the half-ulp is at
most `2^(-24)·|v| ≤ 3·2^(-24)`. The chain is the one inside `fp32Round_rel_on_normal`. (Subnormal/underflow
values are the benign cold tail — handled by the flush-to-zero argument, not this cap.) -/
theorem eps32_le_three_u_of_normal {v : ℝ} (hv0 : v ≠ 0)
    (hnorm : (-125 : ℤ) ≤ neuralMagnitude binaryRadix v) (hv : |v| ≤ 3) :
    eps₃₂ v ≤ 3 * (2 : ℝ) ^ (-24 : ℤ) := by
  have hb23 : neuralBpow binaryRadix (-23) = (2 : ℝ) ^ (-23 : ℤ) :=
    TLT.Capacity.neuralBpow_binaryRadix_eq (-23)
  have h2 : (2 : ℝ) ^ (-23 : ℤ) = 2 * (2 : ℝ) ^ (-24 : ℤ) := by
    rw [show (-23 : ℤ) = 1 + (-24) by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; norm_num
  calc eps₃₂ v = neuralUlp binaryRadix fexp32 v TrainingPhase.forward / 2 := by
        simp only [eps₃₂, eps32, ulp32]
    _ ≤ neuralBpow binaryRadix (-23) * |v| / 2 := by
        gcongr; exact neuralUlp_le_rel_on_normal v hv0 hnorm
    _ = (2 : ℝ) ^ (-23 : ℤ) * |v| / 2 := by rw [hb23]
    _ ≤ (2 : ℝ) ^ (-23 : ℤ) * 3 / 2 := by gcongr
    _ = 3 * (2 : ℝ) ^ (-24 : ℤ) := by rw [h2]; ring

/-- **E3 core (sign-free).** `shiftPow2EvenInt n (e+48)`, read at scale `2⁴⁸`, is within a half-ulp
`2⁻⁴⁹` of `n·2^e`: exact on a left shift (`e ≥ -48`), one ties-to-even half-step on a right shift. -/
private lemma shiftPow2_div_error (n e : ℤ) :
    |(n : ℝ) * (2 : ℝ) ^ e - (shiftPow2EvenInt n (e + fixedScaleInt) : ℝ) / 2 ^ 48|
      ≤ (2 : ℝ) ^ (-49 : ℤ) := by
  rcases hk : e + fixedScaleInt with sh | sh
  · -- left shift: exact, error 0
    have he : e = (sh : ℤ) - 48 := by
      simp only [fixedScaleInt, fixedScale, Int.ofNat_eq_natCast] at hk; omega
    have hpow : (2 : ℝ) ^ sh / 2 ^ 48 = (2 : ℝ) ^ e := by
      rw [he, ← zpow_natCast (2 : ℝ) sh, ← zpow_natCast (2 : ℝ) 48,
          ← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
    have hval : (shiftPow2EvenInt n (Int.ofNat sh) : ℝ) / 2 ^ 48 = (n : ℝ) * (2 : ℝ) ^ e := by
      simp only [shiftPow2EvenInt, pow2Int, pow2_eq_two_pow, Int.ofNat_eq_natCast]
      push_cast
      rw [mul_div_assoc, hpow]
    rw [hval, sub_self, abs_zero]; positivity
  · -- right shift: one ties-to-even half-step
    have herr := roundDivPow2EvenInt_abs_error n (sh + 1) (Nat.succ_ne_zero sh)
    have he : e = -((sh : ℤ) + 1) - 48 := by
      simp only [fixedScaleInt, fixedScale, Int.ofNat_eq_natCast, Int.negSucc_eq] at hk; omega
    have hpow2 : ((pow2Int (sh + 1) : ℤ) : ℝ) = (2 : ℝ) ^ (sh + 1) := by
      simp only [pow2Int, pow2_eq_two_pow, Int.ofNat_eq_natCast]; push_cast; ring
    have hpow : (2 : ℝ) ^ e = 1 / (2 : ℝ) ^ (sh + 1) / 2 ^ 48 := by
      rw [he, ← zpow_natCast (2 : ℝ) (sh + 1), ← zpow_natCast (2 : ℝ) 48, div_div, one_div,
          ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_neg]
      congr 1
    have hval : (n : ℝ) * (2 : ℝ) ^ e = (n : ℝ) / ((pow2Int (sh + 1) : ℤ) : ℝ) / 2 ^ 48 := by
      rw [hpow2, hpow]; ring
    rw [hval]
    simp only [shiftPow2EvenInt]
    rw [div_sub_div_same, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 48)]
    rw [abs_sub_comm] at herr
    calc |(n : ℝ) / ((pow2Int (sh + 1) : ℤ) : ℝ) - (roundDivPow2EvenInt n (sh + 1) : ℝ)| / 2 ^ 48
        ≤ (1 / 2) / 2 ^ 48 := by gcongr
      _ = (2 : ℝ) ^ (-49 : ℤ) := by norm_num [zpow_neg, zpow_natCast]

/-- **E3 — range-reduction quantization.** The fixed-point conversion `fixedOfDyadic` of a finite
input, read at scale `2⁴⁸`, sits within `2⁻⁴⁹` of the exact value. -/
theorem rr_quant (x : IEEE32Exec) {dx : IEEE32Exec.Dyadic} (hx : toDyadic? x = some dx) :
    |toReal x - (fixedOfDyadic dx : ℝ) / 2 ^ 48| ≤ (2 : ℝ) ^ (-49 : ℤ) := by
  have hdy : toReal x = ((if dx.sign then -(Int.ofNat dx.mant) else (Int.ofNat dx.mant) : ℤ) : ℝ)
      * (2 : ℝ) ^ dx.exp := by
    rw [toReal_eq, hx]
    simp only [dyadicToReal, TLT.Capacity.neuralBpow_binaryRadix_eq]
    split_ifs <;> push_cast [Int.ofNat_eq_natCast] <;> ring
  rw [hdy]
  simp only [fixedOfDyadic]
  exact shiftPow2_div_error _ dx.exp

/-- **C2 core (abstract telescope).** For a reconstructed product `u·L` against a target `x`, the error
splits across three independent perturbations — the multiply `|u - p·q| ≤ a`, the reciprocal anchor
`|q - 1/L| ≤ b`, and the input quantization `|p - x| ≤ c` — bounded uniformly on `|x| ≤ T`. -/
private lemma rr_telescope (u p q x L T a b c : ℝ) (hL : 0 < L)
    (ha : |u - p * q| ≤ a) (hb : |q - 1 / L| ≤ b) (hc : |p - x| ≤ c) (hxT : |x| ≤ T) :
    |u * L - x| ≤ a * L + (T + c) * L * b + c := by
  have hT0 : 0 ≤ T := le_trans (abs_nonneg x) hxT
  have hc0 : 0 ≤ c := le_trans (abs_nonneg _) hc
  have hb0 : 0 ≤ b := le_trans (abs_nonneg _) hb
  have hp : |p| ≤ T + c := by
    have h1 := abs_sub_le p x 0
    simp only [sub_zero] at h1
    linarith
  have hid : u * L - x = (u - p * q) * L + p * L * (q - 1 / L) + (p - x) := by
    field_simp
    ring
  rw [hid]
  calc |(u - p * q) * L + p * L * (q - 1 / L) + (p - x)|
      ≤ |(u - p * q) * L| + |p * L * (q - 1 / L)| + |p - x| := abs_add_three _ _ _
    _ = |u - p * q| * L + |p| * L * |q - 1 / L| + |p - x| := by
        simp only [abs_mul, abs_of_pos hL]
    _ ≤ a * L + (T + c) * L * b + c := by
        gcongr <;> first | assumption | positivity

/-- **C2 — range-reduction envelope.** The reconstructed argument `(k + f/2⁴⁸)·ln2` of the main branch is
within `rrρ T` of the true input whenever `|toReal x| ≤ T`: the telescope through the `fixedMul` rounding
(`a = 2⁻⁴⁹`), the `1/ln2` anchor (`b = 10⁻⁸`), and the input quantization (`c = 2⁻⁴⁹`). -/
theorem rrError_le (x : IEEE32Exec) {dx : IEEE32Exec.Dyadic} (hx : toDyadic? x = some dx)
    (T : ℝ) (hT : |toReal x| ≤ T) :
    |((rrK x : ℝ) + (rrF x : ℝ) / 2 ^ 48) * Real.log 2 - toReal x| ≤ rrρ T := by
  have hp48 : ((pow2Int fixedScale : ℤ) : ℝ) = 2 ^ 48 := by
    simp only [pow2Int, fixedScale, pow2_eq_two_pow, Int.ofNat_eq_natCast]; push_cast; ring
  have hred : (rrK x : ℝ) + (rrF x : ℝ) / 2 ^ 48
      = (fixedMul (fixedOfDyadic dx) fixedInvLn2 : ℝ) / 2 ^ 48 := by
    simp only [rrK, rrF, hx]
    push_cast [hp48]
    field_simp
    ring
  rw [hred]
  have hln2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul := fixedMul_div_error (fixedOfDyadic dx) fixedInvLn2
  have hquant := rr_quant x hx
  have hanchor := fixedInvLn2_approx_inv_log_two
  rw [hp48] at hanchor
  refine (rr_telescope _ ((fixedOfDyadic dx : ℝ) / 2 ^ 48) _ (toReal x) (Real.log 2) T
    (1 / 2 / 2 ^ 48) (1 / 10 ^ 8) ((2 : ℝ) ^ (-49 : ℤ)) hln2pos hmul hanchor
    (by rw [abs_sub_comm]; exact hquant) hT).trans ?_
  simp only [rrρ, δinv]
  have h49 : (2 : ℝ) ^ (-49 : ℤ) = 1 / 2 / 2 ^ 48 := by norm_num [zpow_neg, zpow_natCast]
  rw [h49]
  have hbig : (1 : ℝ) / 2 / 2 ^ 48 + 1 / 2 / 2 ^ 48 / 10 ^ 8 ≤ 1 / 2 ^ 48 := by norm_num
  nlinarith [mul_le_mul_of_nonneg_left hbig (le_of_lt hln2pos), hln2pos]

end TLT.ExpError
