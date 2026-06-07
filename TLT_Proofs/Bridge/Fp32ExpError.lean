/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Exponential
import NN.Floats.IEEEExec.Exec32
import NN.Floats.IEEEExec.NatLemmas

/-!
# Bit-level `Exec32.exp` error — the rounding-error ground (L1: the fixed-point rounding atom)

TorchLean's executed `IEEE32Exec.exp` is a concrete deterministic algorithm (no `Float` delegation):
range-reduce `y = x / ln 2` in fixed point at scale `2⁴⁸`, split `y = k + f` with `f ∈ [−½,½]`,
evaluate `2^f` by a degree-10 fixed-point Taylor polynomial, then round `2^k · 2^f` to binary32. To
certify the executed forward for *the program the hardware runs*, the error
`|toReal(Exec32.exp x) − Real.exp(toReal x)|` must be **derived** from this algorithm — not assumed via
the `FP32` proof abstraction (`round∘Real.exp`), which TorchLean flags as a separate trust boundary.

Every fixed-point step rounds an integer quotient to nearest, ties-to-even, via `roundQuotEvenInt`.
This file's L1 is that layer's rounding atom: the ties-to-even integer round is within half a unit of
the exact quotient. It is the building block the range reduction and the Horner polynomial evaluation
both reduce to (`fixedMul = roundDivPow2EvenInt (· * ·) 48 = roundQuotEvenInt (· * ·) 2⁴⁸`).

## Main results

- `roundQuotEvenInt_abs_error` — `|roundQuotEvenInt num den − num/den| ≤ ½` for `den > 0`.
- `roundDivPow2EvenInt_abs_error` — the same for division by `2^shift` (the form `fixedMul` uses).
-/

namespace TLT.ExpError

open TorchLean.Floats.IEEE754.IEEE32Exec
open TorchLean.Floats.IEEE754.IEEE32Exec.Transcendentals

/-- **L1 — the fixed-point rounding atom.** Rounding an integer quotient `num/den` to the nearest
integer with ties-to-even (`roundQuotEvenInt`) lands within half a unit of the exact rational quotient.
This is the per-step rounding bound the range reduction and the Horner polynomial of `Exec32.exp` both
reduce to. -/
theorem roundQuotEvenInt_abs_error (num den : ℤ) (hden : 0 < den) :
    |(roundQuotEvenInt num den : ℝ) - (num : ℝ) / (den : ℝ)| ≤ 1 / 2 := by
  have hden0 : den ≠ 0 := ne_of_gt hden
  have hdenR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have key : den * Int.ediv num den + Int.emod num den = num := Int.mul_ediv_add_emod num den
  have hr0 : (0 : ℤ) ≤ Int.emod num den := Int.emod_nonneg num hden0
  have hrlt : Int.emod num den < den := Int.emod_lt_of_pos num hden
  set q := Int.ediv num den with hqdef
  set r := Int.emod num den with hrdef
  have hnumR : (num : ℝ) = (den : ℝ) * (q : ℝ) + (r : ℝ) := by exact_mod_cast key.symm
  have hr0R : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
  have hrltR : (r : ℝ) < (den : ℝ) := by exact_mod_cast hrlt
  have hdivR : (num : ℝ) / (den : ℝ) = (q : ℝ) + (r : ℝ) / (den : ℝ) := by
    rw [hnumR]; field_simp
  rw [hdivR]
  unfold roundQuotEvenInt
  simp only []
  split_ifs with h1 h2 hp
  · -- 2r < den  ⇒  value = q
    have h1R : (2 : ℝ) * (r : ℝ) < (den : ℝ) := by exact_mod_cast h1
    rw [show ((q : ℝ)) - ((q : ℝ) + (r : ℝ) / (den : ℝ)) = -((r : ℝ) / (den : ℝ)) by ring,
      abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ hdenR]
    linarith
  · -- 2r > den  ⇒  value = q + 1
    have h2R : (den : ℝ) < (2 : ℝ) * (r : ℝ) := by exact_mod_cast h2
    have hle1 : (r : ℝ) / (den : ℝ) ≤ 1 := by rw [div_le_one hdenR]; linarith
    push_cast
    rw [show ((q : ℝ) + 1) - ((q : ℝ) + (r : ℝ) / (den : ℝ)) = 1 - (r : ℝ) / (den : ℝ) by ring,
      abs_of_nonneg (by linarith), sub_le_iff_le_add, ← sub_le_iff_le_add',
      le_div_iff₀ hdenR]
    linarith
  · -- tie 2r = den, parity even ⇒ value = q
    have hnle : ¬ (2 * r < den) := h1
    have hnge : ¬ (den < 2 * r) := h2
    have htie : (2 : ℝ) * (r : ℝ) = (den : ℝ) := by
      have : 2 * r = den := by omega
      exact_mod_cast this
    rw [show ((q : ℝ)) - ((q : ℝ) + (r : ℝ) / (den : ℝ)) = -((r : ℝ) / (den : ℝ)) by ring,
      abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ hdenR]
    linarith
  · -- tie 2r = den, parity odd ⇒ value = q + 1
    have hnle : ¬ (2 * r < den) := h1
    have hnge : ¬ (den < 2 * r) := h2
    have htie : (2 : ℝ) * (r : ℝ) = (den : ℝ) := by
      have : 2 * r = den := by omega
      exact_mod_cast this
    have hle1 : (r : ℝ) / (den : ℝ) ≤ 1 := by rw [div_le_one hdenR]; linarith
    push_cast
    rw [show ((q : ℝ) + 1) - ((q : ℝ) + (r : ℝ) / (den : ℝ)) = 1 - (r : ℝ) / (den : ℝ) by ring,
      abs_of_nonneg (by linarith), sub_le_iff_le_add, ← sub_le_iff_le_add',
      le_div_iff₀ hdenR]
    linarith

/-- **L1′ — division by `2^shift`, ties-to-even, is within half a unit.** The form `fixedMul` uses
(`roundDivPow2EvenInt n shift = roundQuotEvenInt n (2^shift)` for `shift ≠ 0`). -/
theorem roundDivPow2EvenInt_abs_error (n : ℤ) (shift : ℕ) (hshift : shift ≠ 0) :
    |(roundDivPow2EvenInt n shift : ℝ) - (n : ℝ) / ((pow2Int shift : ℤ) : ℝ)| ≤ 1 / 2 := by
  have hpos : 0 < (pow2Int shift : ℤ) := by
    have hp : 0 < ((pow2 shift : ℤ)) := Nat.cast_pos.mpr (pow2_pos shift)
    simpa [pow2Int] using hp
  have heq : roundDivPow2EvenInt n shift = roundQuotEvenInt n (pow2Int shift) := by
    unfold roundDivPow2EvenInt; rw [if_neg (by simpa using hshift)]
  rw [heq]
  exact roundQuotEvenInt_abs_error n (pow2Int shift) hpos

/-- **L2 — the range-reduction constant.** The fixed-point reciprocal of `ln 2` baked into
`Exec32.exp` (`fixedInvLn2 / 2⁴⁸`, `fixedInvLn2 = round(2⁴⁸ / ln 2)`) approximates `1 / ln 2` to within
`10⁻⁸` — derived by bracketing `1 / ln 2` with Mathlib's nine-digit `ln 2` bounds and comparing to the
integer constant. This bounds the error injected by the `x / ln 2` range reduction. -/
theorem fixedInvLn2_approx_inv_log_two :
    |((fixedInvLn2 : ℤ) : ℝ) / ((pow2Int fixedScale : ℤ) : ℝ) - 1 / Real.log 2| ≤ 1 / 10 ^ 8 := by
  have hlo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hhi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hpos : (0 : ℝ) < Real.log 2 := by linarith
  have hpos' : (0 : ℝ) < 0.6931471803 := by norm_num
  have hL1 : 1 / Real.log 2 < 1 / 0.6931471803 := one_div_lt_one_div_of_lt hpos' hlo
  have hL2 : 1 / 0.6931471808 < 1 / Real.log 2 := one_div_lt_one_div_of_lt hpos hhi
  have hCval : ((fixedInvLn2 : ℤ) : ℝ) / ((pow2Int fixedScale : ℤ) : ℝ)
      = 406082553034800 / 281474976710656 := by
    norm_num [fixedInvLn2, pow2Int, fixedScale, pow2_eq_two_pow]
  rw [hCval, abs_le]
  refine ⟨?_, ?_⟩
  · have hA : (1 : ℝ) / 0.6931471803 ≤ 406082553034800 / 281474976710656 + 1 / 10 ^ 8 := by
      norm_num
    linarith
  · have hB : (406082553034800 : ℝ) / 281474976710656 ≤ 1 / 0.6931471808 + 1 / 10 ^ 8 := by
      norm_num
    linarith

/-- **E₁ — the degree-11 Taylor remainder for `exp`.** A direct specialization of `Real.exp_bound`:
the partial Taylor sum `∑_{m<11} sᵐ/m!` is within `|s|¹¹·12/(11!·11)` of `exp s` whenever `|s| ≤ 1`.
With `s = t·ln 2`, `|t| ≤ ½`, this is the approximation error of the *exact* Taylor polynomial of `2ᵗ`
(the polynomial `Exec32.exp` evaluates in fixed point) — the `E₁` term of the L3 decomposition. -/
theorem exp_sub_taylorSum_le {s : ℝ} (hs : |s| ≤ 1) :
    |Real.exp s - ∑ m ∈ Finset.range 11, s ^ m / (m.factorial : ℝ)|
      ≤ |s| ^ 11 * ((11 : ℕ).succ / ((Nat.factorial 11 : ℝ) * 11)) :=
  Real.exp_bound hs (by norm_num)

/-- **E₂ perturbation atom — the eleven coefficients as one orbit.** Changing the base of the
degree-10 Taylor partial sum from `ln 2` to a nearby `L` (within `ε`, both bounded by `B`) perturbs the
sum by at most `ε · ∑_{m<11} m·Bᵐ⁻¹/m!`. This is a single Lipschitz-in-base bound via Mathlib's
`abs_pow_sub_pow_le` (the `xᵐ−yᵐ = (x−y)·∑xⁱyᵐ⁻¹⁻ⁱ` generator) — replacing eleven per-coefficient
interval checks against `ln 2` by one structural lemma. The remaining `|cₘ/2⁴⁸ − Lᵐ/m!|` is then an
exact rational comparison. -/
lemma taylorSum_base_perturbation {L B ε t : ℝ}
    (hL : |L| ≤ B) (hln : |Real.log 2| ≤ B) (hε : |L - Real.log 2| ≤ ε) (ht : |t| ≤ 1) :
    |(∑ m ∈ Finset.range 11, L ^ m / (m.factorial : ℝ) * t ^ m)
        - ∑ m ∈ Finset.range 11, Real.log 2 ^ m / (m.factorial : ℝ) * t ^ m|
      ≤ ∑ m ∈ Finset.range 11, ε * ((m : ℝ) * B ^ (m - 1)) / (m.factorial : ℝ) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hL
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) hε
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun m _ => ?_))
  have hmax : max |L| |Real.log 2| ≤ B := max_le hL hln
  have h1 : |L ^ m - Real.log 2 ^ m| ≤ ε * ((m : ℝ) * B ^ (m - 1)) := by
    refine (abs_pow_sub_pow_le L (Real.log 2) m).trans ?_
    have hp : max |L| |Real.log 2| ^ (m - 1) ≤ B ^ (m - 1) :=
      pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) hmax _
    calc |L - Real.log 2| * (m : ℝ) * max |L| |Real.log 2| ^ (m - 1)
        ≤ ε * (m : ℝ) * B ^ (m - 1) := by gcongr
      _ = ε * ((m : ℝ) * B ^ (m - 1)) := by ring
  have h2 : |t ^ m| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) ht
  have heq : L ^ m / (m.factorial : ℝ) * t ^ m - Real.log 2 ^ m / (m.factorial : ℝ) * t ^ m
      = (L ^ m - Real.log 2 ^ m) * t ^ m / (m.factorial : ℝ) := by ring
  rw [heq, abs_div, abs_mul, Nat.abs_cast]
  have hnum : |L ^ m - Real.log 2 ^ m| * |t ^ m| ≤ ε * ((m : ℝ) * B ^ (m - 1)) := by
    have hrhs0 : 0 ≤ ε * ((m : ℝ) * B ^ (m - 1)) :=
      mul_nonneg hε0 (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hB0 _))
    calc |L ^ m - Real.log 2 ^ m| * |t ^ m|
        ≤ (ε * ((m : ℝ) * B ^ (m - 1))) * 1 := mul_le_mul h1 h2 (abs_nonneg _) hrhs0
      _ = ε * ((m : ℝ) * B ^ (m - 1)) := mul_one _
  gcongr

/-- The fixed-point Taylor coefficients of `Exec32.exp` (`exp2PolyCoeffsDesc`, ascending in `m`):
`expCoeff m = round(2⁴⁸·(ln 2)ᵐ/m!)`, verified `round(2⁴⁸·(ln2)ᵐ/m!)` ties-to-even for `m ≤ 10`. -/
def expCoeff : ℕ → ℤ
  | 0 => 281474976710656
  | 1 => 195103586505167
  | 2 => 67617750451595
  | 3 => 15623017693776
  | 4 => 2707262666570
  | 5 => 375306296874
  | 6 => 43357083587
  | 7 => 4293262892
  | 8 => 371982884
  | 9 => 28648765
  | 10 => 1985781
  | _ => 0

/-- The rational anchor `L = 0.6931471806` is within `10⁻⁹` of `ln 2` — from Mathlib's nine-digit
`ln 2` bracket. This routes all of E₂'s irrationality through a single `δ`. -/
lemma anchor_sub_log_two : |(6931471806 / 10 ^ 10 : ℝ) - Real.log 2| ≤ 1 / 10 ^ 9 := by
  have hlo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hhi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [abs_le]; constructor <;> norm_num <;> linarith

/-- **E₂ residual — the code polynomial vs the rational-anchor Taylor polynomial.** The eleven
coefficient differences `cₘ/2⁴⁸ − Lᵐ/m!` are exact rationals; on `|t| ≤ ½` the polynomial difference is
`≤ 10⁻⁹` (actual value `≈ 2.8×10⁻¹¹`). This is the `norm_num`-cheap half of E₂ — no irrational `ln 2`
enters. -/
lemma taylorSum_residual_le {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |(∑ m ∈ Finset.range 11, (expCoeff m / 2 ^ 48 : ℝ) * t ^ m)
       - ∑ m ∈ Finset.range 11, ((6931471806 / 10 ^ 10 : ℝ) ^ m / (m.factorial : ℝ)) * t ^ m|
      ≤ 1 / 10 ^ 9 := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ m ∈ Finset.range 11,
      |(expCoeff m / 2 ^ 48 : ℝ) * t ^ m - (6931471806 / 10 ^ 10) ^ m / (m.factorial : ℝ) * t ^ m|
        ≤ |(expCoeff m / 2 ^ 48 : ℝ) - (6931471806 / 10 ^ 10) ^ m / (m.factorial : ℝ)| * (1 / 2) ^ m := by
    intro m _; rw [← sub_mul, abs_mul, abs_pow]; gcongr
  refine (Finset.sum_le_sum hterm).trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, expCoeff, Nat.factorial]
  norm_num

/-- **E₂ — the code polynomial approximates the true `2ᵗ` Taylor polynomial.** Triangle through the
rational anchor `L`: the residual `|Q − T_L|` (exact rational, `taylorSum_residual_le`) plus the
parameter perturbation `|T_L − T|` (the orbit lemma, `taylorSum_base_perturbation`, all irrationality
through one `δ`). On `|t| ≤ ½` the code polynomial is within `10⁻⁸` of the true degree-10 Taylor
polynomial of `2ᵗ` — sub-ulp. -/
lemma taylorSum_code_vs_true {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |(∑ m ∈ Finset.range 11, (expCoeff m / 2 ^ 48 : ℝ) * t ^ m)
       - ∑ m ∈ Finset.range 11, ((Real.log 2) ^ m / (m.factorial : ℝ)) * t ^ m|
      ≤ 1 / 10 ^ 8 := by
  have hL : |(6931471806 / 10 ^ 10 : ℝ)| ≤ 6931471808 / 10 ^ 10 := by
    rw [abs_of_nonneg (by norm_num)]; norm_num
  have hln : |Real.log 2| ≤ 6931471808 / 10 ^ 10 := by
    rw [abs_of_nonneg (Real.log_nonneg (by norm_num))]; linarith [Real.log_two_lt_d9]
  have ht1 : |t| ≤ 1 := le_trans ht (by norm_num)
  have hpert := taylorSum_base_perturbation hL hln anchor_sub_log_two ht1
  have hresid := taylorSum_residual_le ht
  have hpsum : (∑ m ∈ Finset.range 11,
      (1 / 10 ^ 9 : ℝ) * ((m : ℝ) * (6931471808 / 10 ^ 10) ^ (m - 1)) / (m.factorial : ℝ))
      ≤ 9 / 10 ^ 9 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  calc |(∑ m ∈ Finset.range 11, (expCoeff m / 2 ^ 48 : ℝ) * t ^ m)
          - ∑ m ∈ Finset.range 11, ((Real.log 2) ^ m / (m.factorial : ℝ)) * t ^ m|
      ≤ |(∑ m ∈ Finset.range 11, (expCoeff m / 2 ^ 48 : ℝ) * t ^ m)
            - ∑ m ∈ Finset.range 11, ((6931471806 / 10 ^ 10 : ℝ) ^ m / (m.factorial : ℝ)) * t ^ m|
          + |(∑ m ∈ Finset.range 11, ((6931471806 / 10 ^ 10 : ℝ) ^ m / (m.factorial : ℝ)) * t ^ m)
            - ∑ m ∈ Finset.range 11, ((Real.log 2) ^ m / (m.factorial : ℝ)) * t ^ m| :=
        abs_sub_le _ _ _
    _ ≤ 1 / 10 ^ 9 + 9 / 10 ^ 9 := add_le_add hresid (le_trans hpert hpsum)
    _ ≤ 1 / 10 ^ 8 := by norm_num

/-- **E₁+E₂ — the fixed-point Taylor polynomial approximates `2ᵗ`.** Combining the Taylor remainder
(E₁, `Real.exp_bound`) with the code-vs-true coefficient bound (E₂): on `|t| ≤ ½` the polynomial
`∑ (cₘ/2⁴⁸) tᵐ` is within `10⁻⁷` of `2ᵗ = exp(t·ln 2)`. The bridge is `(ln2)ᵐ·tᵐ = (t·ln2)ᵐ`, which
turns the true Taylor polynomial into the partial `exp` series that `Real.exp_bound` controls. -/
lemma codePoly_approx_two_pow {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |(∑ m ∈ Finset.range 11, (expCoeff m / 2 ^ 48 : ℝ) * t ^ m) - Real.exp (t * Real.log 2)|
      ≤ 1 / 10 ^ 7 := by
  have hlog1 : |Real.log 2| ≤ 1 := by
    rw [abs_of_nonneg (Real.log_nonneg (by norm_num))]; linarith [Real.log_two_lt_d9]
  have hs : |t * Real.log 2| ≤ 1 := by
    rw [abs_mul]
    have h := mul_le_mul ht hlog1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have hE1 := exp_sub_taylorSum_le hs
  have hE2 := taylorSum_code_vs_true ht
  have heq : (∑ m ∈ Finset.range 11, ((Real.log 2) ^ m / (m.factorial : ℝ)) * t ^ m)
      = ∑ m ∈ Finset.range 11, (t * Real.log 2) ^ m / (m.factorial : ℝ) :=
    Finset.sum_congr rfl (fun m _ => by rw [mul_pow]; ring)
  rw [heq] at hE2
  have hE1b : |t * Real.log 2| ^ 11 * ((11 : ℕ).succ / ((Nat.factorial 11 : ℝ) * 11)) ≤ 3 / 10 ^ 8 := by
    have hp : |t * Real.log 2| ^ 11 ≤ 1 := pow_le_one₀ (abs_nonneg _) hs
    calc |t * Real.log 2| ^ 11 * ((11 : ℕ).succ / ((Nat.factorial 11 : ℝ) * 11))
        ≤ 1 * ((11 : ℕ).succ / ((Nat.factorial 11 : ℝ) * 11)) :=
          mul_le_mul_of_nonneg_right hp (by positivity)
      _ ≤ 3 / 10 ^ 8 := by norm_num [Nat.factorial]
  calc |(∑ m ∈ Finset.range 11, (expCoeff m / 2 ^ 48 : ℝ) * t ^ m) - Real.exp (t * Real.log 2)|
      ≤ |(∑ m ∈ Finset.range 11, (expCoeff m / 2 ^ 48 : ℝ) * t ^ m)
            - ∑ m ∈ Finset.range 11, (t * Real.log 2) ^ m / (m.factorial : ℝ)|
          + |(∑ m ∈ Finset.range 11, (t * Real.log 2) ^ m / (m.factorial : ℝ))
            - Real.exp (t * Real.log 2)| := abs_sub_le _ _ _
    _ ≤ 1 / 10 ^ 8 + 3 / 10 ^ 8 := add_le_add hE2 (by rw [abs_sub_comm]; exact le_trans hE1 hE1b)
    _ ≤ 1 / 10 ^ 7 := by norm_num

/-- **E₃ per-step atom.** One `fixedMul` step rounds the real product `t·(a/2⁴⁸)` to within half a
ULP at scale `2⁴⁸` — i.e. `2⁻⁴⁹`. Direct lift of L1′ (`roundDivPow2EvenInt_abs_error`). -/
lemma fixedMul_div_error (x a : ℤ) :
    |((fixedMul x a : ℤ) : ℝ) / 2 ^ 48 - (x : ℝ) / 2 ^ 48 * ((a : ℝ) / 2 ^ 48)| ≤ 1 / 2 / 2 ^ 48 := by
  have hfm : fixedMul x a = roundDivPow2EvenInt (x * a) 48 := rfl
  have hpow : ((pow2Int 48 : ℤ) : ℝ) = 2 ^ 48 := by
    unfold pow2Int; rw [pow2_eq_two_pow]; push_cast; ring
  have hL := roundDivPow2EvenInt_abs_error (x * a) 48 (by norm_num)
  rw [hpow] at hL
  have he : ((fixedMul x a : ℤ) : ℝ) / 2 ^ 48 - (x : ℝ) / 2 ^ 48 * ((a : ℝ) / 2 ^ 48)
      = (((roundDivPow2EvenInt (x * a) 48 : ℤ) : ℝ) - ((x * a : ℤ) : ℝ) / 2 ^ 48) / 2 ^ 48 := by
    rw [hfm]; push_cast; ring
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 48)]
  gcongr

/-- **E₃ — the fixed-point Horner rounding recurrence.** Evaluating a Horner fold in fixed point
(rounding each `fixedMul`) differs from the exact real Horner fold by at most the propagated initial
error plus `(#steps)·2⁻⁴⁹`. The amplification factor is `|t| ≤ 1`, so the rounding accumulates linearly
(`eₙ ≤ |init| + n·2⁻⁴⁹`), proven by induction over the fold via `fixedMul_div_error`. -/
lemma fixedHornerFoldl_error (x : ℤ) (hx : |(x : ℝ)| ≤ 2 ^ 47) :
    ∀ (cs : List ℤ) (a : ℤ) (ar : ℝ),
    |((cs.foldl (fun p c => c + fixedMul x p) a : ℤ) : ℝ) / 2 ^ 48
       - cs.foldl (fun q c => (c : ℝ) / 2 ^ 48 + (x : ℝ) / 2 ^ 48 * q) ar|
      ≤ |((a : ℝ) / 2 ^ 48) - ar| + (cs.length : ℝ) * (1 / 2 / 2 ^ 48) := by
  have ht : |(x : ℝ) / 2 ^ 48| ≤ 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 48), div_le_one (by positivity)]
    calc |(x : ℝ)| ≤ 2 ^ 47 := hx
      _ ≤ 2 ^ 48 := by norm_num
  intro cs
  induction cs with
  | nil => intro a ar; simp
  | cons c cs ih =>
      intro a ar
      simp only [List.foldl_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      refine (ih (c + fixedMul x a) ((c : ℝ) / 2 ^ 48 + (x : ℝ) / 2 ^ 48 * ar)).trans ?_
      have hstep : |((c + fixedMul x a : ℤ) : ℝ) / 2 ^ 48
            - ((c : ℝ) / 2 ^ 48 + (x : ℝ) / 2 ^ 48 * ar)|
          ≤ 1 / 2 / 2 ^ 48 + |((a : ℝ) / 2 ^ 48) - ar| := by
        have h1 := fixedMul_div_error x a
        have heq : ((c + fixedMul x a : ℤ) : ℝ) / 2 ^ 48 - ((c : ℝ) / 2 ^ 48 + (x : ℝ) / 2 ^ 48 * ar)
            = (((fixedMul x a : ℤ) : ℝ) / 2 ^ 48 - (x : ℝ) / 2 ^ 48 * ((a : ℝ) / 2 ^ 48))
              + (x : ℝ) / 2 ^ 48 * (((a : ℝ) / 2 ^ 48) - ar) := by push_cast; ring
        rw [heq]
        refine (abs_add_le _ _).trans (add_le_add h1 ?_)
        rw [abs_mul]
        calc |(x : ℝ) / 2 ^ 48| * |((a : ℝ) / 2 ^ 48) - ar|
            ≤ 1 * |((a : ℝ) / 2 ^ 48) - ar| := by gcongr
          _ = |((a : ℝ) / 2 ^ 48) - ar| := one_mul _
      have hdist : ((cs.length : ℝ) + 1) * (1 / 2 / 2 ^ 48)
          = (cs.length : ℝ) * (1 / 2 / 2 ^ 48) + 1 / 2 / 2 ^ 48 := by ring
      linarith [hstep, hdist]

/-- **E₃ — `evalExp2Poly` approximates the code polynomial.** TorchLean's integer-Horner
`evalExp2Poly xFixed` (over the concrete coefficient list), divided by `2⁴⁸`, is within `10·2⁻⁴⁹` of
the real polynomial `∑ (cₘ/2⁴⁸) tᵐ` (`t = xFixed/2⁴⁸`). Combines the fold rounding recurrence with the
Horner = sum identity for the literal coefficients. -/
lemma evalExp2Poly_approx_codePoly (xFixed : ℤ) (hx : |(xFixed : ℝ)| ≤ 2 ^ 47) :
    |((evalExp2Poly xFixed : ℤ) : ℝ) / 2 ^ 48
       - ∑ m ∈ Finset.range 11, (expCoeff m / 2 ^ 48 : ℝ) * ((xFixed : ℝ) / 2 ^ 48) ^ m|
      ≤ 10 * (1 / 2 / 2 ^ 48) := by
  have hev : evalExp2Poly xFixed
      = List.foldl (fun p c => c + fixedMul xFixed p) 1985781
          [28648765, 371982884, 4293262892, 43357083587, 375306296874, 2707262666570,
           15623017693776, 67617750451595, 195103586505167, 281474976710656] := rfl
  have hfold := fixedHornerFoldl_error xFixed hx
    [28648765, 371982884, 4293262892, 43357083587, 375306296874, 2707262666570,
     15623017693776, 67617750451595, 195103586505167, 281474976710656]
    1985781 ((1985781 : ℝ) / 2 ^ 48)
  have hsum : List.foldl (fun q c => (c : ℝ) / 2 ^ 48 + (xFixed : ℝ) / 2 ^ 48 * q)
      ((1985781 : ℝ) / 2 ^ 48)
      ([28648765, 371982884, 4293262892, 43357083587, 375306296874, 2707262666570,
       15623017693776, 67617750451595, 195103586505167, 281474976710656] : List ℤ)
      = ∑ m ∈ Finset.range 11, (expCoeff m / 2 ^ 48 : ℝ) * ((xFixed : ℝ) / 2 ^ 48) ^ m := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, expCoeff]
    norm_num [List.foldl]
    ring
  rw [hev]
  exact (hsum ▸ hfold).trans (le_of_eq (by simp))

/-- **L3 — `evalExp2Poly` evaluates `2ᵗ`.** TorchLean's bit-level fixed-point Taylor evaluation
`evalExp2Poly xFixed`, divided by `2⁴⁸`, is within `10⁻⁶` of `2ᵗ = exp(t·ln 2)` for `|t| ≤ ½`
(`t = xFixed/2⁴⁸`) — combining the polynomial-approximation bound `codePoly_approx_two_pow` (E₁+E₂,
the coefficient crux) with the Horner-rounding bound `evalExp2Poly_approx_codePoly` (E₃). The executed
degree-10 fixed-point polynomial is a certified `2ᵗ` to sub-ulp accuracy — *nothing supplied, exp
derived from its polynomial*. -/
lemma evalExp2Poly_error (xFixed : ℤ) (hx : |(xFixed : ℝ)| ≤ 2 ^ 47) :
    |((evalExp2Poly xFixed : ℤ) : ℝ) / 2 ^ 48
       - Real.exp ((xFixed : ℝ) / 2 ^ 48 * Real.log 2)| ≤ 1 / 10 ^ 6 := by
  have ht : |(xFixed : ℝ) / 2 ^ 48| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 48), div_le_iff₀ (by positivity)]
    calc |(xFixed : ℝ)| ≤ 2 ^ 47 := hx
      _ ≤ 1 / 2 * 2 ^ 48 := by norm_num
  have hcode := codePoly_approx_two_pow ht
  have hfold := evalExp2Poly_approx_codePoly xFixed hx
  calc |((evalExp2Poly xFixed : ℤ) : ℝ) / 2 ^ 48 - Real.exp ((xFixed : ℝ) / 2 ^ 48 * Real.log 2)|
      ≤ |((evalExp2Poly xFixed : ℤ) : ℝ) / 2 ^ 48
            - ∑ m ∈ Finset.range 11, (expCoeff m / 2 ^ 48 : ℝ) * ((xFixed : ℝ) / 2 ^ 48) ^ m|
          + |(∑ m ∈ Finset.range 11, (expCoeff m / 2 ^ 48 : ℝ) * ((xFixed : ℝ) / 2 ^ 48) ^ m)
            - Real.exp ((xFixed : ℝ) / 2 ^ 48 * Real.log 2)| := abs_sub_le _ _ _
    _ ≤ 10 * (1 / 2 / 2 ^ 48) + 1 / 10 ^ 7 := add_le_add hfold hcode
    _ ≤ 1 / 10 ^ 6 := by norm_num

end TLT.ExpError
