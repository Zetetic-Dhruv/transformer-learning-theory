/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Fp32.ExpPolynomialError
import NN.Floats.IEEEExec.RatScaling
import NN.Floats.IEEEExec.BridgeFP32
import NN.Floats.IEEEExec.DirectedRoundingSoundness
import NN.Floats.IEEEExec.ErrorBounds

/-!
# Executed `Exec32.exp`: wrapping the L3 polynomial into the bit-level value

L3 (`evalExp2Poly_error`) certifies the executed fixed-point Taylor polynomial against `2ᵗ`. The
output dyadic `⟨false, pFixed, k−48⟩` decodes to `(pFixed/2⁴⁸)·2ᵏ`, so with L3 the rounded output
`toReal(roundDyadicToIEEE32 ⟨…⟩)` is within `eps₃₂ + 2ᵏ·10⁻⁶` of `2ᵏ·2ᶠ`.
-/

/-!
## References
- [46] reconstruction by 2ᵏ (Tang); [44] ½-ulp; [50] dyadic value model; [51] correctly-rounded
  fp32 round; [47] range-reduction value error.
-/

namespace TLT.ExpError

open TorchLean.Floats TorchLean.Floats.IEEE754 TorchLean.Floats.IEEE754.IEEE32Exec
open TorchLean.Floats.IEEE754.IEEE32Exec.Transcendentals

/-- The exp-output dyadic (sign `false`, mantissa `|pFixed|`, exponent `k − 48`) decodes to
`pFixed · bpow(k−48)` for `pFixed > 0`. Via the public `dyadicToReal_pos`. -/
lemma dyadicToReal_exp_output (pFixed k : ℤ) (hp : 0 < pFixed) :
    dyadicToReal ⟨false, pFixed.natAbs, k - fixedScaleInt⟩
      = (pFixed : ℝ) * bpow (k - fixedScaleInt) := by
  rw [dyadicToReal_pos]
  have hnat : ((pFixed.natAbs : ℕ) : ℝ) = (pFixed : ℝ) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hp.le]
  rw [hnat]

/-- `bpow k = 2ᵏ = exp(k·ln 2)` (the dyadic power as an exponential). -/
lemma bpow_eq_exp (k : ℤ) : bpow k = Real.exp ((k : ℝ) * Real.log 2) := by
  have hb : bpow k = (2 : ℝ) ^ k := by simp [bpow, neuralBpow, binaryRadix, NeuralRadix.toReal]
  rw [hb, ← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    mul_comm (Real.log 2)]

/-- **The executed exp value.** With the range-reduced fraction `fFixed` (`|fFixed| ≤ 2⁴⁷`) and integer
`k`, the rounded output `toReal(roundDyadicToIEEE32 ⟨false, pFixed, k−48⟩)` is within
`eps₃₂ + 2ᵏ·10⁻⁶` of `2^(k + fFixed/2⁴⁸)`, combining L3 (`evalExp2Poly_error`), the dyadic decode
(`dyadicToReal_exp_output`), and the final round (L5 `toReal_roundDyadicToIEEE32_eq_fp32Round` +
`fp32Round_abs_error`). This is L3 carried through the IEEE round into the executed number. -/
lemma exec32_exp_value_error (fFixed k : ℤ) (hf : |(fFixed : ℝ)| ≤ 2 ^ 47)
    (hp : 0 < evalExp2Poly fFixed)
    (hfin : isFinite (roundDyadicToIEEE32 ⟨false, (evalExp2Poly fFixed).natAbs, k - fixedScaleInt⟩)
      = true) :
    |toReal (roundDyadicToIEEE32 ⟨false, (evalExp2Poly fFixed).natAbs, k - fixedScaleInt⟩)
       - Real.exp (((k : ℝ) + (fFixed : ℝ) / 2 ^ 48) * Real.log 2)|
      ≤ eps₃₂ (dyadicToReal ⟨false, (evalExp2Poly fFixed).natAbs, k - fixedScaleInt⟩)
        + bpow k * (1 / 10 ^ 6) := by
  set pF := evalExp2Poly fFixed with hpF
  set d : IEEE32Exec.Dyadic := ⟨false, pF.natAbs, k - fixedScaleInt⟩ with hd
  have hL5 : toReal (roundDyadicToIEEE32 d) = fp32Round (dyadicToReal d) :=
    toReal_roundDyadicToIEEE32_eq_fp32Round d hfin
  have hround : |fp32Round (dyadicToReal d) - dyadicToReal d| ≤ eps₃₂ (dyadicToReal d) :=
    fp32Round_abs_error (dyadicToReal d)
  have hb48 : bpow fixedScaleInt = (2 : ℝ) ^ 48 := by
    rw [show fixedScaleInt = Int.ofNat 48 from rfl, bpow_ofNat, pow2_eq_two_pow]; push_cast; ring
  have hbk : bpow (k - fixedScaleInt) = bpow k / 2 ^ 48 := by
    have hexp : (k - fixedScaleInt) + fixedScaleInt = k := by ring
    have h := bpow_add (k - fixedScaleInt) fixedScaleInt
    rw [hexp, hb48] at h
    rw [h, mul_div_assoc, div_self (by positivity : (2 : ℝ) ^ 48 ≠ 0), mul_one]
  have hdv : dyadicToReal d = (pF : ℝ) / 2 ^ 48 * bpow k := by
    rw [hd, dyadicToReal_exp_output pF k hp, hbk]; ring
  have hL3 : |(pF : ℝ) / 2 ^ 48 - Real.exp ((fFixed : ℝ) / 2 ^ 48 * Real.log 2)| ≤ 1 / 10 ^ 6 :=
    evalExp2Poly_error fFixed hf
  have htgt : Real.exp (((k : ℝ) + (fFixed : ℝ) / 2 ^ 48) * Real.log 2)
      = bpow k * Real.exp ((fFixed : ℝ) / 2 ^ 48 * Real.log 2) := by
    rw [bpow_eq_exp, ← Real.exp_add]; congr 1; ring
  calc |toReal (roundDyadicToIEEE32 d) - Real.exp (((k : ℝ) + (fFixed : ℝ) / 2 ^ 48) * Real.log 2)|
      ≤ |toReal (roundDyadicToIEEE32 d) - dyadicToReal d|
          + |dyadicToReal d - Real.exp (((k : ℝ) + (fFixed : ℝ) / 2 ^ 48) * Real.log 2)| :=
        abs_sub_le _ _ _
    _ ≤ eps₃₂ (dyadicToReal d) + bpow k * (1 / 10 ^ 6) := by
        refine add_le_add ?_ ?_
        · rw [hL5]; exact hround
        · rw [htgt, hdv,
            show (pF : ℝ) / 2 ^ 48 * bpow k - bpow k * Real.exp ((fFixed : ℝ) / 2 ^ 48 * Real.log 2)
              = bpow k * ((pF : ℝ) / 2 ^ 48 - Real.exp ((fFixed : ℝ) / 2 ^ 48 * Real.log 2)) by ring,
            abs_mul, abs_of_pos (bpow_pos k)]
          exact mul_le_mul_of_nonneg_left hL3 (bpow_nonneg k)

/-- **The executed `Exec32.exp` error.** For a finite input reaching the main branch (`hbranch`: the
range reduction produces `fFixed`, `k` with `pFixed > 0`), the executed bit-level exponential
`toReal(Exec32.exp x)` is within `eps₃₂ + 2ᵏ·10⁻⁶ + δ` of `Real.exp(toReal x)`, where `δ` bounds the
range-reduction value error. Combines `exec32_exp_value_error` (L3 carried through the IEEE round)
with the range-reduction relation. `hbranch` unfolds `Exec32.exp`'s main branch; `hval` supplies the
range-reduction error bound. -/
lemma exec32_exp_error (x : IEEE32Exec) (fFixed k : ℤ) (hf : |(fFixed : ℝ)| ≤ 2 ^ 47)
    (hp : 0 < evalExp2Poly fFixed)
    (hbranch : IEEE32Exec.exp x
      = roundDyadicToIEEE32 ⟨false, (evalExp2Poly fFixed).natAbs, k - fixedScaleInt⟩)
    (hfin : isFinite (IEEE32Exec.exp x) = true)
    {δ : ℝ}
    (hval : |Real.exp (((k : ℝ) + (fFixed : ℝ) / 2 ^ 48) * Real.log 2) - Real.exp (toReal x)| ≤ δ) :
    |toReal (IEEE32Exec.exp x) - Real.exp (toReal x)|
      ≤ eps₃₂ (dyadicToReal ⟨false, (evalExp2Poly fFixed).natAbs, k - fixedScaleInt⟩)
        + bpow k * (1 / 10 ^ 6) + δ := by
  have hfin' : isFinite (roundDyadicToIEEE32
      ⟨false, (evalExp2Poly fFixed).natAbs, k - fixedScaleInt⟩) = true := by
    rw [← hbranch]; exact hfin
  rw [hbranch]
  calc |toReal (roundDyadicToIEEE32 ⟨false, (evalExp2Poly fFixed).natAbs, k - fixedScaleInt⟩)
          - Real.exp (toReal x)|
      ≤ |toReal (roundDyadicToIEEE32 ⟨false, (evalExp2Poly fFixed).natAbs, k - fixedScaleInt⟩)
            - Real.exp (((k : ℝ) + (fFixed : ℝ) / 2 ^ 48) * Real.log 2)|
          + |Real.exp (((k : ℝ) + (fFixed : ℝ) / 2 ^ 48) * Real.log 2) - Real.exp (toReal x)| :=
        abs_sub_le _ _ _
    _ ≤ (eps₃₂ (dyadicToReal ⟨false, (evalExp2Poly fFixed).natAbs, k - fixedScaleInt⟩)
          + bpow k * (1 / 10 ^ 6)) + δ :=
        add_le_add (exec32_exp_value_error fFixed k hf hp hfin') hval
    _ = eps₃₂ (dyadicToReal ⟨false, (evalExp2Poly fFixed).natAbs, k - fixedScaleInt⟩)
          + bpow k * (1 / 10 ^ 6) + δ := by ring

end TLT.ExpError
