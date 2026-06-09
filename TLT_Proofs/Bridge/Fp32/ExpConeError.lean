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

end TLT.ExpError
