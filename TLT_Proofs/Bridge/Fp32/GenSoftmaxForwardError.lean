/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Fp32.AttentionForwardError

/-!
# The exp-value-parametric softmax forward error (`genSoftmaxTV`)

The model's rounded softmax (`AttentionForwardError`) is hard-wired to `rexp z = fp32Round ∘ Real.exp`.
This file abstracts the exponential channel: `genSoftmax e = fun i => fp32Round (e i / genDenom e)` for
an arbitrary positive exp-value vector `e`, and bounds `∑ⱼ |genSoftmax e j − softmax z j|` given only
`e j > 0` and a per-key error `|e j − Real.exp (z j)| ≤ ε j` (plus the standard normal-range conditions).

The model's `rsoftmax z = genSoftmax (rexp z)` is the instance `e = rexp z`, `ε j = u·exp zⱼ`. The
**literal** fp32 attention softmax is the instance `e = litExp` (`= toReal ∘ IEEE32Exec.exp ∘ shifted`),
`ε j = δ_exp` (the bit-level exp atom). One generalized lemma covers both instances.

## Main results
- `genSoftmax`/`genDenom`: the exp-value-parametric rounded softmax.
- `sum_abs_qtilde_gen`: the un-rounded weight total error in terms of `∑ε` and the denominator gap.
- `genSoftmaxTV`: the closed total-variation bound `∑ⱼ |genSoftmax e j − softmax z j| ≤ …`.
-/

open TorchLean.Floats (neuralMagnitude neuralBpow binaryRadix)
open TorchLean.Floats.IEEE754.IEEE32Exec

noncomputable section

namespace TLT.Fp32Attn

variable {n : ℕ}

/-- The exp-value-parametric softmax denominator: the fp32 left-fold of the exp values. -/
def genDenom (e : Fin n → ℝ) : ℝ := fp32Foldl 0 (List.ofFn e)

/-- The exp-value-parametric rounded softmax weights `i ↦ fp32Round (e i / genDenom e)`. -/
def genSoftmax (e : Fin n → ℝ) : Fin n → ℝ := fun i => fp32Round (e i / genDenom e)

/-- The exact sum of exp values (the un-folded denominator). -/
def eSum (e : Fin n → ℝ) : ℝ := ∑ j, e j

/-- The normal-range side conditions for the exp-value-parametric softmax. -/
def GenNormal (e : Fin n → ℝ) : Prop :=
  (∀ j, 0 < e j) ∧ Fp32FoldlNormal 0 (List.ofFn e)
    ∧ (∀ j, e j / genDenom e ≠ 0 ∧ (-125 : ℤ) ≤ neuralMagnitude binaryRadix (e j / genDenom e))

lemma genDenom_eq {e : Fin n → ℝ} : genDenom e = fp32Foldl 0 (List.ofFn e) := rfl

/-- The model's `rdenom` is the `e = rexp z` instance of `genDenom` (definitional). -/
lemma rdenom_eq_genDenom (z : Fin n → ℝ) : rdenom z = genDenom (rexp z) := rfl

/-- The model's `rsoftmax` is the `e = rexp z` instance of `genSoftmax` (definitional). -/
lemma rsoftmax_eq_genSoftmax (z : Fin n → ℝ) : rsoftmax z = genSoftmax (rexp z) := rfl

/-- **Softmax shift-invariance.** Subtracting a constant `c` from every logit leaves `softmax`
unchanged: `softmax (z − c) = softmax z`. The max-stabilized literal kernel subtracts the row maximum
before exponentiating, while the ideal target does not. Classical (Goodfellow–Bengio–Courville,
*Deep Learning* §4.1, numerical stability of softmax). -/
lemma softmax_shift_invariant [NeZero n] (z : Fin n → ℝ) (c : ℝ) :
    softmax (fun j => z j - c) = softmax z := by
  funext i
  have hc : Real.exp c ≠ 0 := (Real.exp_pos c).ne'
  have hs : (∑ j, Real.exp (z j)) ≠ 0 := by
    have := expSum_pos z; rw [expSum] at this; exact this.ne'
  rw [softmax_eq_div, softmax_eq_div, expSum, expSum]
  simp only [Real.exp_sub, ← Finset.sum_div]
  field_simp

/-- The sum of exp values is within `∑ε` of the exact denominator `∑ exp zⱼ`. -/
lemma abs_eSum_sub_le {z e : Fin n → ℝ} {ε : Fin n → ℝ}
    (he : ∀ j, |e j - Real.exp (z j)| ≤ ε j) : |eSum e - expSum z| ≤ ∑ j, ε j := by
  rw [eSum, expSum, ← Finset.sum_sub_distrib]
  calc |∑ j, (e j - Real.exp (z j))|
      ≤ ∑ j, |e j - Real.exp (z j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ε j := Finset.sum_le_sum (fun j _ => he j)

/-- The magnitude-sum of the exp values equals their sum (they are positive). -/
lemma e_map_abs_sum {e : Fin n → ℝ} (hpos : ∀ j, 0 < e j) :
    ((List.ofFn e).map (fun x => |x|)).sum = eSum e := by
  rw [List.map_ofFn, List.sum_ofFn, eSum]
  exact Finset.sum_congr rfl (fun j _ => abs_of_pos (hpos j))

/-- The exp-value sum is positive. -/
lemma eSum_pos [NeZero n] {e : Fin n → ℝ} (hpos : ∀ j, 0 < e j) : 0 < eSum e :=
  Finset.sum_pos (fun j _ => hpos j) Finset.univ_nonempty

/-- **Denominator-fold error.** `|genDenom e − eSum e| ≤ u·(n+1)·(∑|e|)/(1−n·u)`. -/
lemma abs_genDenom_sub_eSum_le {e : Fin n → ℝ} (hpos : ∀ j, 0 < e j)
    (hfold : Fp32FoldlNormal 0 (List.ofFn e)) (hnu : (n : ℝ) * u < 1) :
    |genDenom e - eSum e|
      ≤ u * (((n : ℝ) + 1) * eSum e) / (1 - (n : ℝ) * u) := by
  have hlen : ((List.ofFn e).length : ℝ) = (n : ℝ) := by simp
  have hun : neuralBpow binaryRadix (-24) * ((List.ofFn e).length : ℝ) < 1 := by
    rw [hlen, show neuralBpow binaryRadix (-24) = u from rfl, mul_comm]; exact hnu
  have hS : ((List.ofFn e).map (fun x => |x|)).sum ≤ eSum e := le_of_eq (e_map_abs_sum hpos)
  have hfoldErr := fp32Foldl_error_le_of_sum_bound (List.ofFn e) (eSum e) hfold hun hS
  rw [show neuralBpow binaryRadix (-24) = u from rfl, hlen] at hfoldErr
  have hsum : (List.ofFn e).sum = eSum e := by rw [List.sum_ofFn]; rfl
  rw [hsum] at hfoldErr
  calc |genDenom e - eSum e|
      ≤ u * (((n : ℝ) + 1) * eSum e) / (1 - u * (n : ℝ)) := hfoldErr
    _ = u * (((n : ℝ) + 1) * eSum e) / (1 - (n : ℝ) * u) := by rw [mul_comm u (n : ℝ)]

/-- **Total un-rounded weight error.** `∑ⱼ |e j/genDenom e − softmax z j| ≤ (∑ε + |genDenom e − D|)/genDenom e`,
where `D = ∑ exp zⱼ`. (The per-key bounds do not factor, but the sum does.) -/
lemma sum_abs_qtilde_gen [NeZero n] {z e : Fin n → ℝ} {ε : Fin n → ℝ}
    (he : ∀ j, |e j - Real.exp (z j)| ≤ ε j) (hden : 0 < genDenom e) :
    ∑ j, |e j / genDenom e - softmax z j|
      ≤ ((∑ j, ε j) + |genDenom e - expSum z|) / genDenom e := by
  have hD : 0 < expSum z := expSum_pos z
  have hkey : ∀ j, |e j / genDenom e - softmax z j|
      ≤ |e j - Real.exp (z j)| / genDenom e
        + Real.exp (z j) * |genDenom e - expSum z| / (genDenom e * expSum z) := by
    intro j
    calc |e j / genDenom e - softmax z j|
        ≤ |e j / genDenom e - Real.exp (z j) / genDenom e|
          + |Real.exp (z j) / genDenom e - softmax z j| := abs_sub_le _ _ _
      _ = |e j - Real.exp (z j)| / genDenom e
          + Real.exp (z j) * |genDenom e - expSum z| / (genDenom e * expSum z) := by
          congr 1
          · rw [div_sub_div_same, abs_div, abs_of_pos hden]
          · rw [softmax_eq_div, div_sub_div _ _ (ne_of_gt hden) (ne_of_gt hD), abs_div,
              abs_of_pos (mul_pos hden hD),
              show Real.exp (z j) * expSum z - genDenom e * Real.exp (z j)
                = Real.exp (z j) * (expSum z - genDenom e) from by ring,
              abs_mul, abs_of_pos (Real.exp_pos _), abs_sub_comm (expSum z)]
  refine (Finset.sum_le_sum (fun j _ => hkey j)).trans ?_
  rw [Finset.sum_add_distrib]
  have hfac1 : ∑ j, |e j - Real.exp (z j)| / genDenom e
      = (∑ j, |e j - Real.exp (z j)|) / genDenom e := by rw [Finset.sum_div]
  have hfac2 : ∑ j, Real.exp (z j) * |genDenom e - expSum z| / (genDenom e * expSum z)
      = |genDenom e - expSum z| / genDenom e := by
    rw [← Finset.sum_div, ← Finset.sum_mul, ← expSum, mul_comm (genDenom e) (expSum z),
      mul_div_mul_left _ _ (ne_of_gt hD)]
  rw [hfac1, hfac2, ← add_div]
  gcongr
  exact he _

/-- **Quotient rounding error.** `∑ⱼ |genSoftmax e j − e j/genDenom e| ≤ u·(eSum e/genDenom e)`. -/
lemma sum_abs_genSoftmax_sub_qtilde_gen {e : Fin n → ℝ} (h : GenNormal e) (hden : 0 < genDenom e) :
    ∑ j, |genSoftmax e j - e j / genDenom e| ≤ u * (eSum e / genDenom e) := by
  have hstep : ∀ j, |genSoftmax e j - e j / genDenom e| ≤ u * (e j / genDenom e) := by
    intro j
    have hb := fp32Round_rel_on_normal (e j / genDenom e) (h.2.2 j).1 (h.2.2 j).2
    rw [show neuralBpow binaryRadix (-24) = u from rfl] at hb
    have hpos : 0 ≤ e j / genDenom e := div_nonneg (h.1 j).le hden.le
    rw [abs_of_nonneg hpos] at hb
    exact hb
  calc ∑ j, |genSoftmax e j - e j / genDenom e|
      ≤ ∑ j, u * (e j / genDenom e) := Finset.sum_le_sum (fun j _ => hstep j)
    _ = u * (eSum e / genDenom e) := by rw [← Finset.mul_sum, ← Finset.sum_div, eSum]

/-- **The exp-value-parametric softmax total-variation bound.** With a positive lower bound `Dlo ≤ genDenom e`
on the rounded denominator (the surfaced no-underflow hypothesis), the rounded softmax weights differ from
the exact softmax weights by at most `u + u·B/Dlo + (2·∑ε + B)/Dlo`, where `B = u·(n+1)·(eSum e)/(1−n·u)`
is the denominator-fold budget. The model's `softmaxTV` is the instance `e = rexp z`, `ε = u·exp`. -/
lemma genSoftmaxTV [NeZero n] {z e : Fin n → ℝ} {ε : Fin n → ℝ} (h : GenNormal e)
    (he : ∀ j, |e j - Real.exp (z j)| ≤ ε j) (hnu : (n : ℝ) * u < 1)
    {Dlo : ℝ} (hDlo0 : 0 < Dlo) (hDlo : Dlo ≤ genDenom e) (hε0 : ∀ j, 0 ≤ ε j) :
    ∑ j, |genSoftmax e j - softmax z j|
      ≤ u + u * (u * (((n : ℝ) + 1) * eSum e) / (1 - (n : ℝ) * u)) / Dlo
        + (2 * (∑ j, ε j) + u * (((n : ℝ) + 1) * eSum e) / (1 - (n : ℝ) * u)) / Dlo := by
  have hden : 0 < genDenom e := lt_of_lt_of_le hDlo0 hDlo
  have hespos : 0 < eSum e := eSum_pos h.1
  have hεsum : 0 ≤ ∑ j, ε j := Finset.sum_nonneg (fun j _ => hε0 j)
  set B : ℝ := u * (((n : ℝ) + 1) * eSum e) / (1 - (n : ℝ) * u) with hB
  have hBnn : 0 ≤ B := by
    rw [hB]; apply div_nonneg _ (by linarith : (0:ℝ) ≤ 1 - (n:ℝ) * u)
    have : 0 ≤ u := u_nonneg; positivity
  have hfoldErr : |genDenom e - eSum e| ≤ B := abs_genDenom_sub_eSum_le h.1 h.2.1 hnu
  have hdensub : |eSum e - expSum z| ≤ ∑ j, ε j := abs_eSum_sub_le he
  have hgenexp : |genDenom e - expSum z| ≤ B + ∑ j, ε j := by
    calc |genDenom e - expSum z| ≤ |genDenom e - eSum e| + |eSum e - expSum z| := by
          have := abs_sub_le (genDenom e) (eSum e) (expSum z); linarith
      _ ≤ B + ∑ j, ε j := by linarith
  -- triangle
  have htri : ∑ j, |genSoftmax e j - softmax z j|
      ≤ ∑ j, |genSoftmax e j - e j / genDenom e| + ∑ j, |e j / genDenom e - softmax z j| := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum (fun j _ => abs_sub_le _ _ _)
  have hT1 := sum_abs_genSoftmax_sub_qtilde_gen h hden
  have hT2 := sum_abs_qtilde_gen he hden
  -- piece 1 : u·(eSum/genDenom) ≤ u + u·B/Dlo
  have heSum_le : eSum e ≤ genDenom e + B := by have := (abs_le.mp hfoldErr).1; linarith
  have hratio1 : eSum e / genDenom e ≤ 1 + B / Dlo := by
    have hstep : eSum e / genDenom e ≤ (genDenom e + B) / genDenom e := by gcongr
    rw [add_div, div_self (ne_of_gt hden)] at hstep
    have : B / genDenom e ≤ B / Dlo := div_le_div_of_nonneg_left hBnn hDlo0 hDlo
    linarith
  have hpiece1 : u * (eSum e / genDenom e) ≤ u + u * B / Dlo := by
    calc u * (eSum e / genDenom e) ≤ u * (1 + B / Dlo) := by
          exact mul_le_mul_of_nonneg_left hratio1 u_nonneg
      _ = u + u * B / Dlo := by ring
  -- piece 2 : (∑ε + |genDenom-expSum|)/genDenom ≤ (2∑ε + B)/Dlo
  have hpiece2 : ((∑ j, ε j) + |genDenom e - expSum z|) / genDenom e ≤ (2 * (∑ j, ε j) + B) / Dlo := by
    have hnum : (∑ j, ε j) + |genDenom e - expSum z| ≤ 2 * (∑ j, ε j) + B := by linarith
    have hnumnn : 0 ≤ (∑ j, ε j) + |genDenom e - expSum z| := add_nonneg hεsum (abs_nonneg _)
    calc ((∑ j, ε j) + |genDenom e - expSum z|) / genDenom e
        ≤ (2 * (∑ j, ε j) + B) / genDenom e := by gcongr
      _ ≤ (2 * (∑ j, ε j) + B) / Dlo := by
          apply div_le_div_of_nonneg_left _ hDlo0 hDlo; linarith
  calc ∑ j, |genSoftmax e j - softmax z j|
      ≤ u * (eSum e / genDenom e) + ((∑ j, ε j) + |genDenom e - expSum z|) / genDenom e := by
        linarith [htri, hT1, hT2]
    _ ≤ (u + u * B / Dlo) + (2 * (∑ j, ε j) + B) / Dlo := add_le_add hpiece1 hpiece2

/-- **Generic value-mix error.** For ANY weight vector `w` whose total variation from `softmax z` is
`≤ tv` and whose ℓ¹-mass is `≤ 1 + tv`, the rounded value-mix `rdot w (V·c)` is within
`rdotBudget n (bV·(1+tv)) + bV·tv` of the ideal mix `∑ⱼ softmax z j · V j c`. The model's `omixRow_error`
is the `w = rsoftmax z`, `tv = softmaxTV` instance; the literal kernel is the `w = genSoftmax (litExp)`,
`tv = τ(δ_exp)` instance. -/
lemma rdot_mix_error {d : ℕ} [NeZero n] (w z : Fin n → ℝ) (V : Fin n → Fin d → ℝ) (c : Fin d)
    (hmix : RdotNormal w (fun j => V j c)) (hnu : (n : ℝ) * u < 1)
    {bV tv : ℝ} (hbV0 : 0 ≤ bV) (hbV : ∀ j, |V j c| ≤ bV)
    (hsum : ∑ j, |w j| ≤ 1 + tv) (htv : ∑ j, |w j - softmax z j| ≤ tv) :
    |rdot w (fun j => V j c) - ∑ j, softmax z j * V j c|
      ≤ rdotBudget n (bV * (1 + tv)) + bV * tv := by
  have hStep1 : |rdot w (fun j => V j c) - ∑ j, w j * V j c| ≤ rdotBudget n (bV * (1 + tv)) := by
    refine rdot_error_le_of_sum_bound w (fun j => V j c) hmix hnu ?_
    calc ∑ j, |w j * V j c|
        = ∑ j, |w j| * |V j c| := by simp_rw [abs_mul]
      _ ≤ ∑ j, |w j| * bV := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_left (hbV j) (abs_nonneg _)
      _ = (∑ j, |w j|) * bV := by rw [Finset.sum_mul]
      _ ≤ (1 + tv) * bV := mul_le_mul_of_nonneg_right hsum hbV0
      _ = bV * (1 + tv) := by ring
  have hStep2 : |∑ j, w j * V j c - ∑ j, softmax z j * V j c| ≤ bV * tv := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ j, (w j * V j c - softmax z j * V j c)|
        ≤ ∑ j, |w j * V j c - softmax z j * V j c| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |w j - softmax z j| * |V j c| := by simp_rw [← sub_mul, abs_mul]
      _ ≤ ∑ j, |w j - softmax z j| * bV := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_left (hbV j) (abs_nonneg _)
      _ = (∑ j, |w j - softmax z j|) * bV := by rw [Finset.sum_mul]
      _ ≤ tv * bV := mul_le_mul_of_nonneg_right htv hbV0
      _ = bV * tv := by ring
  calc |rdot w (fun j => V j c) - ∑ j, softmax z j * V j c|
      ≤ |rdot w (fun j => V j c) - ∑ j, w j * V j c|
          + |∑ j, w j * V j c - ∑ j, softmax z j * V j c| := abs_sub_le _ _ _
    _ ≤ rdotBudget n (bV * (1 + tv)) + bV * tv := add_le_add hStep1 hStep2

/-- **`genSoftmax` ℓ¹-mass bound.** Given the total-variation bound `tv` (from `genSoftmaxTV`), the
exp-value-parametric weights have ℓ¹-mass `≤ 1 + tv`, the `rsoftmax_sum_le` analog, feeding the
generic mix lemma `rdot_mix_error`'s `hsum`. -/
lemma genSoftmax_sum_le [NeZero n] {e z : Fin n → ℝ} {tv : ℝ}
    (htv : ∑ j, |genSoftmax e j - softmax z j| ≤ tv) :
    ∑ j, |genSoftmax e j| ≤ 1 + tv := by
  calc ∑ j, |genSoftmax e j|
      ≤ ∑ j, (|genSoftmax e j - softmax z j| + |softmax z j|) :=
        Finset.sum_le_sum (fun j _ => by
          have h := abs_add_le (genSoftmax e j - softmax z j) (softmax z j)
          rw [sub_add_cancel] at h; exact h)
    _ = ∑ j, |genSoftmax e j - softmax z j| + ∑ j, |softmax z j| := by rw [Finset.sum_add_distrib]
    _ = ∑ j, |genSoftmax e j - softmax z j| + 1 := by
        congr 1
        rw [show (∑ j, |softmax z j|) = ∑ j, softmax z j from
          Finset.sum_congr rfl (fun j _ => abs_of_nonneg (softmax_nonneg z j)), softmax_sum_one]
    _ ≤ tv + 1 := by linarith
    _ = 1 + tv := by ring

end TLT.Fp32Attn
