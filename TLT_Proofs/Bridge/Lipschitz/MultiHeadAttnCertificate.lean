/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Certificate.AttentionTransformerCertificate
import TLT_Proofs.Bridge.Certificate.AttnStackCertificate

/-!
# A certified generalization bound for true multi-head attention

A genuine multi-head attention layer is a sum of `H` independent heads, each with its **own learnable
query/key/value projections**, so that distinct heads form distinct attention patterns:
`MHA(Y) = ∑_{h<H} headQK(W_Q^h, W_K^h, W_VO^h, Y)`. (A head with identity query/key projections,
i.e., shared scores across heads, would collapse the sum to a single head, since `attnVec` is linear in the
value matrix; the learnable query/key projections are what make the heads genuinely distinct.) Each
head is `headQK W_Q W_K W_VO Y i = attnVec(scores(Y·W_Q, Y·W_K)ᵢ, Y·W_VO)`, with the value and output
projections folded into one map `W_VO` (lossless: `attnVec(s, Y·W_V)·W_O = attnVec(s, Y·W_V·W_O)` by
linearity of `attnVec` in the value). Heads are full-width (head dimension = model dimension `d`).

The capacity is **linear in the head count `H`** and **independent of the sequence length**: the
sequence-length independence is inherited from `attnVec_lipschitz_on_ball`, whose constant is absolute
in the key count because softmax rows are probability vectors (Edelman et al. 2022, Cor. A.7; Trauger &
Tewari 2024, §4.2). Multi-head adds no new attention analysis: it is the single-head weight-Lipschitz
estimate composed with the linear projections (`matMulCoord_param_lipschitz`) and summed over heads.

## Main definitions

- `attnHeadQK`: a dot-product attention head with learnable query/key/value-output projections.
- `multiHeadAttn`: the sum of `H` such heads.

## Main results

- `attnHeadQK_weight_lip`: a head is Lipschitz in `(W_Q, W_K, W_VO)` on the bounded input domain.

## References

B. Edelman, S. Goel, S. Kakade, C. Zhang, *Inductive Biases and Variable Creation in Self-Attention
Mechanisms*, ICML 2022; A. Trauger and A. Tewari, *Sequence Length Independent Norm-Based
Generalization Bounds for Transformers*, AISTATS 2024; H. Kim, G. Papamakarios and A. Mnih, *The
Lipschitz Constant of Self-Attention*, ICML 2021.
-/

open MeasureTheory

noncomputable section

namespace TLT

variable {n d : ℕ}

/-- A dot-product attention head with learnable query, key and (folded) value-output projections: the
softmax scores are formed from the projected query `Y·W_Q` and key `Y·W_K`, and the value rows are the
projected `Y·W_VO`. Distinct `(W_Q, W_K)` across heads give distinct attention patterns. -/
noncomputable def attnHeadQK (scale : ℝ) (WQ WK WVO : Fin d → Fin d → ℝ) (Y : Fin n → Fin d → ℝ) :
    Fin n → Fin d → ℝ :=
  fun i => attnVec (attnScores scale (matMulCoord WQ Y i) (matMulCoord WK Y)) (matMulCoord WVO Y)

/-- **A head is Lipschitz in its query/key/value-output weights on the bounded input domain.** With the
projected query/key entries bounded by `B`, the projected value rows of norm `≤ bV`, and the input rows
of `ℓ¹` norm `≤ βY`, the head moves by at most
`2·bV·(d·B/scale)·(βY·‖ΔW_Q‖ + βY·‖ΔW_K‖) + βY·‖ΔW_VO‖`. This composes the `n`-free
`attnVec_lipschitz_on_ball` (Lipschitz in the projected `Q,K,V`) with the linear projection
weight-Lipschitz `matMulCoord_param_lipschitz` (Lipschitz `βY` in each projection weight). The `B`-cap
is the Kim et al. boundary; the constant carries no sequence-length factor. -/
lemma attnHeadQK_weight_lip [NeZero n] {scale B bV βY : ℝ} (hscale : 0 < scale) (hB : 0 ≤ B)
    (hbV0 : 0 ≤ bV) (hβY0 : 0 ≤ βY) (Y : Fin n → Fin d → ℝ) (hβY : ∀ i, (∑ a, |Y i a|) ≤ βY)
    (WQ WK WVO WQ' WK' WVO' : Fin d → Fin d → ℝ)
    (hQ'B : ∀ i e, |matMulCoord WQ' Y i e| ≤ B) (hKB : ∀ k' e, |matMulCoord WK Y k' e| ≤ B)
    (hVbV : ∀ j, ‖matMulCoord WVO Y j‖ ≤ bV) :
    dist (attnHeadQK scale WQ WK WVO Y) (attnHeadQK scale WQ' WK' WVO' Y)
      ≤ 2 * bV * ((d : ℝ) * B / scale) * (βY * dist WQ WQ' + βY * dist WK WK') + βY * dist WVO WVO' := by
  have hC : (0:ℝ) ≤ 2 * bV * ((d : ℝ) * B / scale) :=
    mul_nonneg (mul_nonneg (by norm_num) hbV0)
      (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hB) hscale.le)
  refine (dist_pi_le_iff (by positivity)).mpr (fun i => ?_)
  rw [dist_eq_norm]
  have hQrow : ‖matMulCoord WQ Y i - matMulCoord WQ' Y i‖ ≤ βY * dist WQ WQ' := by
    rw [show matMulCoord WQ Y i - matMulCoord WQ' Y i = (matMulCoord WQ Y - matMulCoord WQ' Y) i from rfl]
    exact le_trans (norm_le_pi_norm _ i)
      (le_trans (le_of_eq (dist_eq_norm _ _).symm) (matMulCoord_param_lipschitz Y hβY0 hβY WQ WQ'))
  have hKrow : ‖matMulCoord WK Y - matMulCoord WK' Y‖ ≤ βY * dist WK WK' :=
    le_trans (le_of_eq (dist_eq_norm _ _).symm) (matMulCoord_param_lipschitz Y hβY0 hβY WK WK')
  have hVrow : ‖matMulCoord WVO Y - matMulCoord WVO' Y‖ ≤ βY * dist WVO WVO' :=
    le_trans (le_of_eq (dist_eq_norm _ _).symm) (matMulCoord_param_lipschitz Y hβY0 hβY WVO WVO')
  calc ‖attnHeadQK scale WQ WK WVO Y i - attnHeadQK scale WQ' WK' WVO' Y i‖
      ≤ 2 * bV * ((d : ℝ) * B / scale)
            * (‖matMulCoord WQ Y i - matMulCoord WQ' Y i‖ + ‖matMulCoord WK Y - matMulCoord WK' Y‖)
          + ‖matMulCoord WVO Y - matMulCoord WVO' Y‖ := by
        simp only [attnHeadQK]
        exact attnVec_lipschitz_on_ball hscale hB hbV0 _ _ _ _ _ _ (hQ'B i) hKB hVbV
    _ ≤ 2 * bV * ((d : ℝ) * B / scale) * (βY * dist WQ WQ' + βY * dist WK WK') + βY * dist WVO WVO' := by
        gcongr

/-- Multi-head attention: the sum of `H` independent heads, each with its own query/key/value-output
projections. Distinct `(W_Q^h, W_K^h)` make the heads attend differently (with shared scores the sum
would collapse to a single head). -/
noncomputable def multiHeadAttn {H : ℕ} (scale : ℝ) (WQ WK WVO : Fin H → Fin d → Fin d → ℝ)
    (Y : Fin n → Fin d → ℝ) : Fin n → Fin d → ℝ :=
  ∑ h, attnHeadQK scale (WQ h) (WK h) (WVO h) Y

/-- **Multi-head attention is Lipschitz in its weights, linearly in the head count `H`.** The sum of
`H` heads moves by at most `H` times the per-head weight-Lipschitz bound (triangle inequality over the
heads); the per-head bound is the sequence-length-free `attnHeadQK_weight_lip`. So the multi-head
capacity scales linearly in `H` with no cross-head interaction (Edelman et al. 2022, App. A.6; Trauger &
Tewari 2024, §4.2) and no sequence-length factor. -/
lemma multiHeadAttn_weight_lip {H : ℕ} [NeZero n] {scale B bV βY : ℝ} (hscale : 0 < scale)
    (hB : 0 ≤ B) (hbV0 : 0 ≤ bV) (hβY0 : 0 ≤ βY) (Y : Fin n → Fin d → ℝ) (hβY : ∀ i, (∑ a, |Y i a|) ≤ βY)
    (WQ WK WVO WQ' WK' WVO' : Fin H → Fin d → Fin d → ℝ)
    (hQ'B : ∀ h i e, |matMulCoord (WQ' h) Y i e| ≤ B) (hKB : ∀ h k' e, |matMulCoord (WK h) Y k' e| ≤ B)
    (hVbV : ∀ h j, ‖matMulCoord (WVO h) Y j‖ ≤ bV) :
    dist (multiHeadAttn scale WQ WK WVO Y) (multiHeadAttn scale WQ' WK' WVO' Y)
      ≤ (H : ℝ) * (2 * bV * ((d : ℝ) * B / scale) * (βY * dist WQ WQ' + βY * dist WK WK')
          + βY * dist WVO WVO') := by
  have hper : ∀ h : Fin H,
      dist (attnHeadQK scale (WQ h) (WK h) (WVO h) Y) (attnHeadQK scale (WQ' h) (WK' h) (WVO' h) Y)
        ≤ 2 * bV * ((d : ℝ) * B / scale) * (βY * dist WQ WQ' + βY * dist WK WK') + βY * dist WVO WVO' := by
    intro h
    refine le_trans (attnHeadQK_weight_lip hscale hB hbV0 hβY0 Y hβY (WQ h) (WK h) (WVO h)
      (WQ' h) (WK' h) (WVO' h) (hQ'B h) (hKB h) (hVbV h)) ?_
    gcongr
    · exact dist_le_pi_dist WQ WQ' h
    · exact dist_le_pi_dist WK WK' h
    · exact dist_le_pi_dist WVO WVO' h
  calc dist (multiHeadAttn scale WQ WK WVO Y) (multiHeadAttn scale WQ' WK' WVO' Y)
      = ‖(∑ h, attnHeadQK scale (WQ h) (WK h) (WVO h) Y)
          - (∑ h, attnHeadQK scale (WQ' h) (WK' h) (WVO' h) Y)‖ := by
        rw [multiHeadAttn, multiHeadAttn, dist_eq_norm]
    _ = ‖∑ h, (attnHeadQK scale (WQ h) (WK h) (WVO h) Y
          - attnHeadQK scale (WQ' h) (WK' h) (WVO' h) Y)‖ := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ h, ‖attnHeadQK scale (WQ h) (WK h) (WVO h) Y
          - attnHeadQK scale (WQ' h) (WK' h) (WVO' h) Y‖ := norm_sum_le _ _
    _ ≤ ∑ _h : Fin H, (2 * bV * ((d : ℝ) * B / scale) * (βY * dist WQ WQ' + βY * dist WK WK')
          + βY * dist WVO WVO') := by
        refine Finset.sum_le_sum (fun h _ => ?_)
        rw [← dist_eq_norm]; exact hper h
    _ = (H : ℝ) * (2 * bV * ((d : ℝ) * B / scale) * (βY * dist WQ WQ' + βY * dist WK WK')
          + βY * dist WVO WVO') := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### Input-Lipschitz on the bounded domain (for the depth-`L` stack) -/

/-- **Linear-layer input-Lipschitz (the `X`-side mirror).** For a fixed weight `W` whose contracted
columns have `ℓ¹` norm at most `γ`, `X ↦ matMulCoord W X` is `γ`-Lipschitz in the input. -/
lemma matMulCoord_input_lipschitz {s nn p : ℕ} (W : Fin nn → Fin p → ℝ) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : ∀ j, (∑ k, |W k j|) ≤ γ) (X X' : Fin s → Fin nn → ℝ) :
    dist (matMulCoord W X) (matMulCoord W X') ≤ γ * dist X X' := by
  refine (dist_pi_le_iff (by positivity)).mpr fun i => ?_
  refine (dist_pi_le_iff (by positivity)).mpr fun j => ?_
  simp only [matMulCoord, Real.dist_eq, ← Finset.sum_sub_distrib, ← sub_mul]
  calc |∑ k, (X i k - X' i k) * W k j|
      ≤ ∑ k, |X i k - X' i k| * |W k j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => abs_mul _ _))
    _ ≤ ∑ k, dist X X' * |W k j| := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        rw [← Real.dist_eq]
        exact le_trans (dist_le_pi_dist (X i) (X' i) k) (dist_le_pi_dist X X' i)
    _ = dist X X' * (∑ k, |W k j|) := by rw [← Finset.mul_sum]
    _ ≤ dist X X' * γ := mul_le_mul_of_nonneg_left (hγ j) dist_nonneg
    _ = γ * dist X X' := by ring

/-- A projected entry is bounded by the input row-`ℓ¹` norm times the weight sup-norm. -/
lemma matMulCoord_entry_le {s nn p : ℕ} (W : Fin nn → Fin p → ℝ) (X : Fin s → Fin nn → ℝ) (i : Fin s)
    (j : Fin p) : |matMulCoord W X i j| ≤ (∑ k, |X i k|) * ‖W‖ := by
  simp only [matMulCoord]
  calc |∑ k, X i k * W k j| ≤ ∑ k, |X i k * W k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |X i k| * |W k j| := Finset.sum_congr rfl fun k _ => abs_mul _ _
    _ ≤ ∑ k, |X i k| * ‖W‖ := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact (le_of_eq (Real.norm_eq_abs _).symm).trans
          (le_trans (norm_le_pi_norm (W k) j) (norm_le_pi_norm W k))
    _ = (∑ k, |X i k|) * ‖W‖ := by rw [← Finset.sum_mul]

/-- **A head is input-Lipschitz on the bounded domain.** With the (input-side) projected query/key
entries bounded by `B`, the value rows of norm `≤ bV`, and each projection's contracted-column `ℓ¹`
norm `≤ γW`, the head is `(4·bV·(d·B/scale) + 1)·γW`-Lipschitz in its input: the `n`-free atom composed
with the linear projection input-Lipschitz. -/
lemma attnHeadQK_input_lip [NeZero n] {scale B bV γW : ℝ} (hscale : 0 < scale) (hB : 0 ≤ B)
    (hbV0 : 0 ≤ bV) (hγW0 : 0 ≤ γW) (WQ WK WVO : Fin d → Fin d → ℝ)
    (hγWQ : ∀ j, (∑ k, |WQ k j|) ≤ γW) (hγWK : ∀ j, (∑ k, |WK k j|) ≤ γW)
    (hγWVO : ∀ j, (∑ k, |WVO k j|) ≤ γW) (X X' : Fin n → Fin d → ℝ)
    (hQ'B : ∀ i e, |matMulCoord WQ X' i e| ≤ B) (hKB : ∀ k' e, |matMulCoord WK X k' e| ≤ B)
    (hVbV : ∀ j, ‖matMulCoord WVO X j‖ ≤ bV) :
    dist (attnHeadQK scale WQ WK WVO X) (attnHeadQK scale WQ WK WVO X')
      ≤ (2 * bV * ((d : ℝ) * B / scale) * (2 * γW) + γW) * dist X X' := by
  have hC : (0:ℝ) ≤ 2 * bV * ((d : ℝ) * B / scale) :=
    mul_nonneg (mul_nonneg (by norm_num) hbV0)
      (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hB) hscale.le)
  refine (dist_pi_le_iff (by positivity)).mpr (fun i => ?_)
  rw [dist_eq_norm]
  have hQrow : ‖matMulCoord WQ X i - matMulCoord WQ X' i‖ ≤ γW * dist X X' := by
    rw [show matMulCoord WQ X i - matMulCoord WQ X' i = (matMulCoord WQ X - matMulCoord WQ X') i from rfl]
    exact le_trans (norm_le_pi_norm _ i)
      (le_trans (le_of_eq (dist_eq_norm _ _).symm) (matMulCoord_input_lipschitz WQ hγW0 hγWQ X X'))
  have hKrow : ‖matMulCoord WK X - matMulCoord WK X'‖ ≤ γW * dist X X' :=
    le_trans (le_of_eq (dist_eq_norm _ _).symm) (matMulCoord_input_lipschitz WK hγW0 hγWK X X')
  have hVrow : ‖matMulCoord WVO X - matMulCoord WVO X'‖ ≤ γW * dist X X' :=
    le_trans (le_of_eq (dist_eq_norm _ _).symm) (matMulCoord_input_lipschitz WVO hγW0 hγWVO X X')
  calc ‖attnHeadQK scale WQ WK WVO X i - attnHeadQK scale WQ WK WVO X' i‖
      ≤ 2 * bV * ((d : ℝ) * B / scale)
            * (‖matMulCoord WQ X i - matMulCoord WQ X' i‖ + ‖matMulCoord WK X - matMulCoord WK X'‖)
          + ‖matMulCoord WVO X - matMulCoord WVO X'‖ := by
        simp only [attnHeadQK]
        exact attnVec_lipschitz_on_ball hscale hB hbV0 _ _ _ _ _ _ (hQ'B i) hKB hVbV
    _ ≤ 2 * bV * ((d : ℝ) * B / scale) * (γW * dist X X' + γW * dist X X') + γW * dist X X' := by gcongr
    _ = (2 * bV * ((d : ℝ) * B / scale) * (2 * γW) + γW) * dist X X' := by ring

/-- **Multi-head attention is input-Lipschitz on the bounded domain, linearly in `H`.** -/
lemma multiHeadAttn_input_lip {H : ℕ} [NeZero n] {scale B bV γW : ℝ} (hscale : 0 < scale) (hB : 0 ≤ B)
    (hbV0 : 0 ≤ bV) (hγW0 : 0 ≤ γW) (WQ WK WVO : Fin H → Fin d → Fin d → ℝ)
    (hγWQ : ∀ h j, (∑ k, |WQ h k j|) ≤ γW) (hγWK : ∀ h j, (∑ k, |WK h k j|) ≤ γW)
    (hγWVO : ∀ h j, (∑ k, |WVO h k j|) ≤ γW) (X X' : Fin n → Fin d → ℝ)
    (hQ'B : ∀ h i e, |matMulCoord (WQ h) X' i e| ≤ B) (hKB : ∀ h k' e, |matMulCoord (WK h) X k' e| ≤ B)
    (hVbV : ∀ h j, ‖matMulCoord (WVO h) X j‖ ≤ bV) :
    dist (multiHeadAttn scale WQ WK WVO X) (multiHeadAttn scale WQ WK WVO X')
      ≤ (H : ℝ) * (2 * bV * ((d : ℝ) * B / scale) * (2 * γW) + γW) * dist X X' := by
  have hper : ∀ h : Fin H,
      dist (attnHeadQK scale (WQ h) (WK h) (WVO h) X) (attnHeadQK scale (WQ h) (WK h) (WVO h) X')
        ≤ (2 * bV * ((d : ℝ) * B / scale) * (2 * γW) + γW) * dist X X' := fun h =>
    attnHeadQK_input_lip hscale hB hbV0 hγW0 (WQ h) (WK h) (WVO h) (hγWQ h) (hγWK h) (hγWVO h) X X'
      (hQ'B h) (hKB h) (hVbV h)
  calc dist (multiHeadAttn scale WQ WK WVO X) (multiHeadAttn scale WQ WK WVO X')
      = ‖(∑ h, attnHeadQK scale (WQ h) (WK h) (WVO h) X)
          - (∑ h, attnHeadQK scale (WQ h) (WK h) (WVO h) X')‖ := by
        rw [multiHeadAttn, multiHeadAttn, dist_eq_norm]
    _ = ‖∑ h, (attnHeadQK scale (WQ h) (WK h) (WVO h) X
          - attnHeadQK scale (WQ h) (WK h) (WVO h) X')‖ := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ h, ‖attnHeadQK scale (WQ h) (WK h) (WVO h) X
          - attnHeadQK scale (WQ h) (WK h) (WVO h) X'‖ := norm_sum_le _ _
    _ ≤ ∑ _h : Fin H, ((2 * bV * ((d : ℝ) * B / scale) * (2 * γW) + γW) * dist X X') := by
        refine Finset.sum_le_sum (fun h _ => ?_)
        rw [← dist_eq_norm]; exact hper h
    _ = (H : ℝ) * (2 * bV * ((d : ℝ) * B / scale) * (2 * γW) + γW) * dist X X' := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-! ### The post-norm multi-head attention block

`B_θ(X) = layerNorm_{γ,β}(X + MHA(X))`, the true-multi-head analogue of `normAttnBlock`. The residual
and layer-norm are the existing `normAttnCoord`; only the attention map changes. Forward-invariance and
the input cap come from layer-norm exactly as in the single-head block; the weight-Lipschitz now carries
the attention projection weights in addition to the affine `γ, β`. -/

/-- **The post-norm multi-head block is forward-invariant on the ball**: layer-norm caps the output at
`√d·Cγ + Cβ` regardless of the attention map. -/
lemma normMultiHeadBlock_forward_inv {H : ℕ} (hd : 0 < d) (γ β : Fin d → ℝ) {Cγ Cβ : ℝ}
    (hCγ : ∀ j, |γ j| ≤ Cγ) (hCβ : ∀ j, |β j| ≤ Cβ) (scale : ℝ)
    (WQ WK WVO : Fin H → Fin d → Fin d → ℝ) (X : Fin n → Fin d → ℝ) :
    ‖normAttnCoord γ β (multiHeadAttn scale WQ WK WVO) X‖ ≤ Real.sqrt d * Cγ + Cβ := by
  rw [normAttnCoord]; exact layerNormCoord_norm_le hd γ β hCγ hCβ _

/-- **The post-norm multi-head block is Lipschitz in all its weights.** Both the affine `γ, β` (through
the final layer-norm) and the attention projections `W_Q, W_K, W_VO` (through the residual) vary: the
bound is the layer-norm parameter-Lipschitz `√d·dist γ γ' + dist β β'` plus the layer-norm
input-Lipschitz `Cγ·(2√d+2)/√ε` times the multi-head weight-Lipschitz. -/
lemma normMultiHeadBlock_param_lip {H : ℕ} [NeZero n] (hd : 0 < d) {scale B bV βY : ℝ}
    (hscale : 0 < scale) (hB : 0 ≤ B) (hbV0 : 0 ≤ bV) (hβY0 : 0 ≤ βY)
    (WQ WK WVO WQ' WK' WVO' : Fin H → Fin d → Fin d → ℝ) (γ β γ' β' : Fin d → ℝ) {Cγ : ℝ}
    (hCγ : ∀ j, |γ' j| ≤ Cγ) (X : Fin n → Fin d → ℝ) (hβYX : ∀ i, (∑ a, |X i a|) ≤ βY)
    (hQ'B : ∀ h i e, |matMulCoord (WQ' h) X i e| ≤ B) (hKB : ∀ h k' e, |matMulCoord (WK h) X k' e| ≤ B)
    (hVbV : ∀ h j, ‖matMulCoord (WVO h) X j‖ ≤ bV) :
    dist (normAttnCoord γ β (multiHeadAttn scale WQ WK WVO) X)
         (normAttnCoord γ' β' (multiHeadAttn scale WQ' WK' WVO') X)
      ≤ (Real.sqrt d * dist γ γ' + dist β β')
        + Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon
          * ((H : ℝ) * (2 * bV * ((d : ℝ) * B / scale) * (βY * dist WQ WQ' + βY * dist WK WK')
              + βY * dist WVO WVO')) := by
  have hLNlip0 : (0:ℝ) ≤ Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon := by
    have hε : 0 < Real.sqrt Numbers.epsilon := Real.sqrt_pos.mpr numbers_epsilon_real_pos
    have hCγ0 : 0 ≤ Cγ := le_trans (abs_nonneg _) (hCγ ⟨0, hd⟩)
    exact div_nonneg (mul_nonneg hCγ0 (by positivity)) (Real.sqrt_nonneg _)
  have hresid : dist (fun i j => X i j + multiHeadAttn scale WQ WK WVO X i j)
      (fun i j => X i j + multiHeadAttn scale WQ' WK' WVO' X i j : Fin n → Fin d → ℝ)
      ≤ (H : ℝ) * (2 * bV * ((d : ℝ) * B / scale) * (βY * dist WQ WQ' + βY * dist WK WK')
          + βY * dist WVO WVO') := by
    refine le_trans ?_ (multiHeadAttn_weight_lip hscale hB hbV0 hβY0 X hβYX WQ WK WVO WQ' WK' WVO'
      hQ'B hKB hVbV)
    refine (dist_pi_le_iff dist_nonneg).mpr (fun i => (dist_pi_le_iff dist_nonneg).mpr (fun j => ?_))
    rw [Real.dist_eq, show (X i j + multiHeadAttn scale WQ WK WVO X i j)
          - (X i j + multiHeadAttn scale WQ' WK' WVO' X i j)
          = multiHeadAttn scale WQ WK WVO X i j - multiHeadAttn scale WQ' WK' WVO' X i j from by ring,
      ← Real.dist_eq]
    exact le_trans (dist_le_pi_dist (multiHeadAttn scale WQ WK WVO X i) _ j)
      (dist_le_pi_dist (multiHeadAttn scale WQ WK WVO X) _ i)
  calc dist (normAttnCoord γ β (multiHeadAttn scale WQ WK WVO) X)
            (normAttnCoord γ' β' (multiHeadAttn scale WQ' WK' WVO') X)
      = dist (layerNormCoord γ β (fun i j => X i j + multiHeadAttn scale WQ WK WVO X i j))
             (layerNormCoord γ' β' (fun i j => X i j + multiHeadAttn scale WQ' WK' WVO' X i j)) := by
        rw [normAttnCoord, normAttnCoord]
    _ ≤ dist (layerNormCoord γ β (fun i j => X i j + multiHeadAttn scale WQ WK WVO X i j))
             (layerNormCoord γ' β' (fun i j => X i j + multiHeadAttn scale WQ WK WVO X i j))
          + dist (layerNormCoord γ' β' (fun i j => X i j + multiHeadAttn scale WQ WK WVO X i j))
             (layerNormCoord γ' β' (fun i j => X i j + multiHeadAttn scale WQ' WK' WVO' X i j)) :=
        dist_triangle _ _ _
    _ ≤ (Real.sqrt d * dist γ γ' + dist β β')
          + Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon
            * ((H : ℝ) * (2 * bV * ((d : ℝ) * B / scale) * (βY * dist WQ WQ' + βY * dist WK WK')
                + βY * dist WVO WVO')) := by
        refine add_le_add (layerNormCoord_param_lipschitz hd γ β γ' β' _) ?_
        exact le_trans (layerNormCoord_lipschitz hd γ' β' hCγ _ _)
          (mul_le_mul_of_nonneg_left hresid hLNlip0)

/-- **The post-norm multi-head block is input-Lipschitz on the ball.** Layer-norm is globally
`Cγ·(2√d+2)/√ε`-Lipschitz; the residual `X ↦ X + MHA(X)` is `1 + L_mha`-Lipschitz on the ball, where
`L_mha = H·(2·bV·(d·B/scale)·(2·γW) + γW)` is the multi-head input-Lipschitz constant; the block is
their product. -/
lemma normMultiHeadBlock_input_lip {H : ℕ} [NeZero n] (hd : 0 < d) {scale B bV γW : ℝ}
    (hscale : 0 < scale) (hB : 0 ≤ B) (hbV0 : 0 ≤ bV) (hγW0 : 0 ≤ γW)
    (WQ WK WVO : Fin H → Fin d → Fin d → ℝ)
    (hγWQ : ∀ h j, (∑ k, |WQ h k j|) ≤ γW) (hγWK : ∀ h j, (∑ k, |WK h k j|) ≤ γW)
    (hγWVO : ∀ h j, (∑ k, |WVO h k j|) ≤ γW) (γ β : Fin d → ℝ) {Cγ : ℝ} (hCγ : ∀ j, |γ j| ≤ Cγ)
    (Xa Xb : Fin n → Fin d → ℝ) (hQXb : ∀ h i e, |matMulCoord (WQ h) Xb i e| ≤ B)
    (hKXa : ∀ h k' e, |matMulCoord (WK h) Xa k' e| ≤ B) (hVXa : ∀ h j, ‖matMulCoord (WVO h) Xa j‖ ≤ bV) :
    dist (normAttnCoord γ β (multiHeadAttn scale WQ WK WVO) Xa)
         (normAttnCoord γ β (multiHeadAttn scale WQ WK WVO) Xb)
      ≤ Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon
          * (1 + (H : ℝ) * (2 * bV * ((d : ℝ) * B / scale) * (2 * γW) + γW)) * dist Xa Xb := by
  set Lmha : ℝ := (H : ℝ) * (2 * bV * ((d : ℝ) * B / scale) * (2 * γW) + γW) with hLmha
  have hLmha0 : 0 ≤ Lmha := by
    have hC : (0:ℝ) ≤ 2 * bV * ((d : ℝ) * B / scale) :=
      mul_nonneg (mul_nonneg (by norm_num) hbV0)
        (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hB) hscale.le)
    rw [hLmha]; positivity
  have hCγ0 : 0 ≤ Cγ := le_trans (abs_nonneg _) (hCγ ⟨0, hd⟩)
  have hLNlip0 : (0:ℝ) ≤ Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon := by
    have hε : 0 < Real.sqrt Numbers.epsilon := Real.sqrt_pos.mpr numbers_epsilon_real_pos
    exact div_nonneg (mul_nonneg hCγ0 (by positivity)) (Real.sqrt_nonneg _)
  have hmha : dist (multiHeadAttn scale WQ WK WVO Xa) (multiHeadAttn scale WQ WK WVO Xb)
      ≤ Lmha * dist Xa Xb :=
    multiHeadAttn_input_lip hscale hB hbV0 hγW0 WQ WK WVO hγWQ hγWK hγWVO Xa Xb hQXb hKXa hVXa
  have hresid : dist (fun i j => Xa i j + multiHeadAttn scale WQ WK WVO Xa i j)
      (fun i j => Xb i j + multiHeadAttn scale WQ WK WVO Xb i j : Fin n → Fin d → ℝ)
      ≤ (1 + Lmha) * dist Xa Xb := by
    refine (dist_pi_le_iff (by positivity)).mpr (fun i => ?_)
    refine (dist_pi_le_iff (by positivity)).mpr (fun j => ?_)
    rw [Real.dist_eq]
    calc |(Xa i j + multiHeadAttn scale WQ WK WVO Xa i j)
            - (Xb i j + multiHeadAttn scale WQ WK WVO Xb i j)|
        ≤ |Xa i j - Xb i j|
            + |multiHeadAttn scale WQ WK WVO Xa i j - multiHeadAttn scale WQ WK WVO Xb i j| := by
          rw [show (Xa i j + multiHeadAttn scale WQ WK WVO Xa i j)
                - (Xb i j + multiHeadAttn scale WQ WK WVO Xb i j)
              = (Xa i j - Xb i j)
                + (multiHeadAttn scale WQ WK WVO Xa i j - multiHeadAttn scale WQ WK WVO Xb i j) from by
            ring]
          exact abs_add_le _ _
      _ ≤ dist Xa Xb + Lmha * dist Xa Xb := by
          refine add_le_add ?_ ?_
          · exact le_trans (le_trans (le_of_eq (Real.dist_eq _ _).symm) (dist_le_pi_dist (Xa i) (Xb i) j))
              (dist_le_pi_dist Xa Xb i)
          · rw [← Real.dist_eq]
            exact le_trans (le_trans (dist_le_pi_dist (multiHeadAttn scale WQ WK WVO Xa i) _ j)
              (dist_le_pi_dist (multiHeadAttn scale WQ WK WVO Xa) _ i)) hmha
      _ = (1 + Lmha) * dist Xa Xb := by ring
  calc dist (normAttnCoord γ β (multiHeadAttn scale WQ WK WVO) Xa)
            (normAttnCoord γ β (multiHeadAttn scale WQ WK WVO) Xb)
      = dist (layerNormCoord γ β (fun i j => Xa i j + multiHeadAttn scale WQ WK WVO Xa i j))
             (layerNormCoord γ β (fun i j => Xb i j + multiHeadAttn scale WQ WK WVO Xb i j)) := by
        rw [normAttnCoord, normAttnCoord]
    _ ≤ Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon
          * dist (fun i j => Xa i j + multiHeadAttn scale WQ WK WVO Xa i j)
                 (fun i j => Xb i j + multiHeadAttn scale WQ WK WVO Xb i j) :=
        layerNormCoord_lipschitz hd γ β hCγ _ _
    _ ≤ Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon * ((1 + Lmha) * dist Xa Xb) :=
        mul_le_mul_of_nonneg_left hresid hLNlip0
    _ = Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon * (1 + Lmha) * dist Xa Xb := by ring

/-! ### Continuity (for the capstone's measurability and weight-continuity hypotheses) -/

/-- The matrix-multiply layer is jointly continuous in its weights and input. -/
lemma continuous_matMulCoord_uncurry {s nn pp : ℕ} :
    Continuous (fun p : (Fin nn → Fin pp → ℝ) × (Fin s → Fin nn → ℝ) => matMulCoord p.1 p.2) := by
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  simp only [matMulCoord]
  exact continuous_finset_sum _ (fun k _ =>
    ((continuous_apply_apply i k).comp continuous_snd).mul ((continuous_apply_apply k j).comp continuous_fst))

/-- The scores are jointly continuous in the query and key. -/
lemma continuous_attnScores_uncurry {nK : ℕ} {scale : ℝ} :
    Continuous (fun p : (Fin d → ℝ) × (Fin nK → Fin d → ℝ) => attnScores scale p.1 p.2) := by
  refine continuous_pi (fun k' => ?_)
  simp only [attnScores]
  exact (continuous_finset_sum _ (fun e _ =>
    ((continuous_apply e).comp continuous_fst).mul
      ((continuous_apply_apply k' e).comp continuous_snd))).div_const scale

/-- A head is continuous in any continuous family of its query/key/value weights and input. -/
lemma continuous_attnHeadQK_comp [NeZero n] {scale : ℝ} {Θ : Type*} [TopologicalSpace Θ]
    {WQ WK WVO : Θ → (Fin d → Fin d → ℝ)} (hWQ : Continuous WQ) (hWK : Continuous WK)
    (hWVO : Continuous WVO) {Y : Θ → (Fin n → Fin d → ℝ)} (hY : Continuous Y) :
    Continuous (fun θ => attnHeadQK scale (WQ θ) (WK θ) (WVO θ) (Y θ)) := by
  refine continuous_pi (fun i => ?_)
  simp only [attnHeadQK]
  have hWKY : Continuous (fun θ => matMulCoord (WK θ) (Y θ)) :=
    continuous_matMulCoord_uncurry.comp (hWK.prodMk hY)
  have hWVOY : Continuous (fun θ => matMulCoord (WVO θ) (Y θ)) :=
    continuous_matMulCoord_uncurry.comp (hWVO.prodMk hY)
  have hQi : Continuous (fun θ => matMulCoord (WQ θ) (Y θ) i) :=
    (continuous_apply i).comp (continuous_matMulCoord_uncurry.comp (hWQ.prodMk hY))
  exact continuous_attnVec_uncurry.comp ((continuous_attnScores_uncurry.comp (hQi.prodMk hWKY)).prodMk hWVOY)

/-- Multi-head attention is continuous in any continuous family of its weights and input. -/
lemma continuous_multiHeadAttn_comp {H : ℕ} [NeZero n] {scale : ℝ} {Θ : Type*} [TopologicalSpace Θ]
    {WQ WK WVO : Θ → (Fin H → Fin d → Fin d → ℝ)} (hWQ : Continuous WQ) (hWK : Continuous WK)
    (hWVO : Continuous WVO) {Y : Θ → (Fin n → Fin d → ℝ)} (hY : Continuous Y) :
    Continuous (fun θ => multiHeadAttn scale (WQ θ) (WK θ) (WVO θ) (Y θ)) := by
  simp only [multiHeadAttn]
  exact continuous_finset_sum _ (fun h _ => continuous_attnHeadQK_comp
    ((continuous_apply h).comp hWQ) ((continuous_apply h).comp hWK) ((continuous_apply h).comp hWVO) hY)

open Capacity in
/-- **Joint continuity of the post-norm multi-head block in `(weights, input)`.** -/
lemma continuous_normMultiHeadBlock_weight {H q : ℕ} [NeZero n] {scale : ℝ}
    {WQ WK WVO : ParamSpace q → (Fin H → Fin d → Fin d → ℝ)} {γ β : ParamSpace q → (Fin d → ℝ)}
    (hWQ : Continuous WQ) (hWK : Continuous WK) (hWVO : Continuous WVO) (hγ : Continuous γ)
    (hβ : Continuous β) :
    Continuous (fun p : ParamSpace q × (Fin n → Fin d → ℝ) =>
      normAttnCoord (γ p.1) (β p.1) (multiHeadAttn scale (WQ p.1) (WK p.1) (WVO p.1)) p.2) := by
  unfold normAttnCoord
  refine continuous_layerNormCoord_uncurry (hγ.comp continuous_fst) (hβ.comp continuous_fst) ?_
  have hmha : Continuous (fun p : ParamSpace q × (Fin n → Fin d → ℝ) =>
      multiHeadAttn scale (WQ p.1) (WK p.1) (WVO p.1) p.2) :=
    continuous_multiHeadAttn_comp (hWQ.comp continuous_fst) (hWK.comp continuous_fst)
      (hWVO.comp continuous_fst) continuous_snd
  exact continuous_pi (fun i => continuous_pi (fun j =>
    ((continuous_apply_apply i j).comp continuous_snd).add ((continuous_apply_apply i j).comp hmha)))

/-! ### The depth-`L` true-multi-head stack and its certified generalization bound -/

open Capacity in
/-- The post-norm multi-head block as a depth-uniform `ParamLayerLocal`. The input-Lipschitz constant
holds on the activation ball where the projected query/key/value entries are bounded by `B`/`bV`; the
weight-Lipschitz constant carries the affine `Lγ, Lβ` and the per-head projection Lipschitz constants
`LWQ, LWK, LWVO`, the attention contribution scaling linearly in the head count `H`. -/
noncomputable def normMultiHeadBlock {H p : ℕ} [NeZero n]
    {scale B bV βY γW Cγ Lγ Lβ LWQ LWK LWVO : ℝ} (hscale : 0 < scale) (hB : 0 ≤ B) (hbV0 : 0 ≤ bV)
    (hβY0 : 0 ≤ βY) (hγW0 : 0 ≤ γW) (hCγ0 : 0 ≤ Cγ) (hLγ0 : 0 ≤ Lγ) (hLβ0 : 0 ≤ Lβ) (hLWQ0 : 0 ≤ LWQ)
    (hLWK0 : 0 ≤ LWK) (hLWVO0 : 0 ≤ LWVO) (WQ WK WVO : ParamSpace p → (Fin H → Fin d → Fin d → ℝ))
    (γ β : ParamSpace p → (Fin d → ℝ)) :
    ParamLayerLocal (ParamSpace p) (Fin n → Fin d → ℝ) where
  map θ X := normAttnCoord (γ θ) (β θ) (multiHeadAttn scale (WQ θ) (WK θ) (WVO θ)) X
  paramLip := (Real.sqrt d * Lγ + Lβ) + Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon
      * ((H : ℝ) * (2 * bV * ((d : ℝ) * B / scale) * (βY * LWQ + βY * LWK) + βY * LWVO))
  lip := Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon
      * (1 + (H : ℝ) * (2 * bV * ((d : ℝ) * B / scale) * (2 * γW) + γW))
  paramLip_nonneg := by
    have hLN : (0:ℝ) ≤ Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon :=
      div_nonneg (mul_nonneg hCγ0 (by positivity)) (Real.sqrt_nonneg _)
    have hC : (0:ℝ) ≤ 2 * bV * ((d : ℝ) * B / scale) :=
      mul_nonneg (mul_nonneg (by norm_num) hbV0) (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hB) hscale.le)
    exact add_nonneg (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hLγ0) hLβ0) (mul_nonneg hLN (by positivity))
  lip_nonneg := by
    have hLN : (0:ℝ) ≤ Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon :=
      div_nonneg (mul_nonneg hCγ0 (by positivity)) (Real.sqrt_nonneg _)
    have hC : (0:ℝ) ≤ 2 * bV * ((d : ℝ) * B / scale) :=
      mul_nonneg (mul_nonneg (by norm_num) hbV0) (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hB) hscale.le)
    exact mul_nonneg hLN (by positivity)

open Capacity in
/-- **Depth-graded true-multi-head weight-Lipschitz.** A depth-`L` stack of post-norm multi-head
blocks (shared weights across depth) is `lparamLipBound`-Lipschitz in the weights, on the
forward-invariant activation ball, with the constant growing with depth `L` and head count `H`. The
projected query/key/value bounds (`B`, `bV`) on the ball and the weight column-`ℓ¹` bound (`γW`) are the
Kim et al. cap made into hypotheses; the depth-uniform composition is `paramComp_param_lipschitz_on'`. -/
theorem normMultiHeadStack_weight_lip {H p : ℕ} [NeZero n] (hd : 0 < d)
    {scale R B bV βY γW Cγ Cβ Lγ Lβ LWQ LWK LWVO : ℝ} (hscale : 0 < scale) (hB : 0 ≤ B)
    (hbV0 : 0 ≤ bV) (hβY0 : 0 ≤ βY) (hγW0 : 0 ≤ γW) (hCγ0 : 0 ≤ Cγ) (_hCβ0 : 0 ≤ Cβ) (hLγ0 : 0 ≤ Lγ)
    (hLβ0 : 0 ≤ Lβ) (hLWQ0 : 0 ≤ LWQ) (hLWK0 : 0 ≤ LWK) (hLWVO0 : 0 ≤ LWVO)
    (WQ WK WVO : ParamSpace p → (Fin H → Fin d → Fin d → ℝ)) (γ β : ParamSpace p → (Fin d → ℝ))
    (hγB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ θ j| ≤ Cγ)
    (hβB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β θ j| ≤ Cβ)
    (hβYD : ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ i, (∑ a, |y i a|) ≤ βY)
    (hQB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h i e, |matMulCoord (WQ θ h) y i e| ≤ B)
    (hKB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h k' e, |matMulCoord (WK θ h) y k' e| ≤ B)
    (hVB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h j, ‖matMulCoord (WVO θ h) y j‖ ≤ bV)
    (hγWQ : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WQ θ h k j|) ≤ γW)
    (hγWK : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WK θ h k j|) ≤ γW)
    (hγWVO : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WVO θ h k j|) ≤ γW)
    (hγLip : ∀ θ θ', dist (γ θ) (γ θ') ≤ Lγ * dist θ θ')
    (hβLip : ∀ θ θ', dist (β θ) (β θ') ≤ Lβ * dist θ θ')
    (hWQLip : ∀ θ θ', dist (WQ θ) (WQ θ') ≤ LWQ * dist θ θ')
    (hWKLip : ∀ θ θ', dist (WK θ) (WK θ') ≤ LWK * dist θ θ')
    (hWVOLip : ∀ θ θ', dist (WVO θ) (WVO θ') ≤ LWVO * dist θ θ') (L : ℕ)
    {θ θ' : ParamSpace p} (hθ : θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))))
    (hθ' : θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))))
    {x : Fin n → Fin d → ℝ} (hx : x ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ)) :
    dist (lparamComp (List.replicate L (normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0
            hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 WQ WK WVO γ β)) θ x)
         (lparamComp (List.replicate L (normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0
            hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 WQ WK WVO γ β)) θ' x)
      ≤ lparamLipBound (List.replicate L (normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0
          hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 WQ WK WVO γ β)) * dist θ θ' := by
  have hLN0 : (0:ℝ) ≤ Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon :=
    div_nonneg (mul_nonneg hCγ0 (by positivity)) (Real.sqrt_nonneg _)
  have hC0 : (0:ℝ) ≤ 2 * bV * ((d : ℝ) * B / scale) :=
    mul_nonneg (mul_nonneg (by norm_num) hbV0) (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hB) hscale.le)
  set blk := normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0
    WQ WK WVO γ β with hblk
  refine paramComp_param_lipschitz_on'
    (K := (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))))
    (D := Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ)) _ ?_ ?_ ?_ hθ hθ' hx
  · intro Lb hLb θ₀ hθ₀ a ha b hb
    rw [List.eq_of_mem_replicate hLb, hblk]
    exact normMultiHeadBlock_input_lip hd hscale hB hbV0 hγW0 (WQ θ₀) (WK θ₀) (WVO θ₀)
      (hγWQ θ₀ hθ₀) (hγWK θ₀ hθ₀) (hγWVO θ₀ hθ₀) (γ θ₀) (β θ₀) (hγB θ₀ hθ₀) a b
      (hQB θ₀ hθ₀ b hb) (hKB θ₀ hθ₀ a ha) (hVB θ₀ hθ₀ a ha)
  · intro Lb hLb θ₀ hθ₀ θ₁ hθ₁ y hy
    rw [List.eq_of_mem_replicate hLb, hblk]
    refine le_trans (normMultiHeadBlock_param_lip hd hscale hB hbV0 hβY0 (WQ θ₀) (WK θ₀) (WVO θ₀)
      (WQ θ₁) (WK θ₁) (WVO θ₁) (γ θ₀) (β θ₀) (γ θ₁) (β θ₁) (hγB θ₁ hθ₁) y (hβYD y hy)
      (hQB θ₁ hθ₁ y hy) (hKB θ₀ hθ₀ y hy) (hVB θ₀ hθ₀ y hy)) ?_
    rw [show (blk.paramLip) * dist θ₀ θ₁
        = (Real.sqrt d * (Lγ * dist θ₀ θ₁) + Lβ * dist θ₀ θ₁)
          + Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon
            * ((H : ℝ) * (2 * bV * ((d : ℝ) * B / scale)
                * (βY * (LWQ * dist θ₀ θ₁) + βY * (LWK * dist θ₀ θ₁))
              + βY * (LWVO * dist θ₀ θ₁))) from by rw [hblk]; simp only [normMultiHeadBlock]; ring]
    gcongr
    · exact hγLip θ₀ θ₁
    · exact hβLip θ₀ θ₁
    · exact hWQLip θ₀ θ₁
    · exact hWKLip θ₀ θ₁
    · exact hWVOLip θ₀ θ₁
  · intro Lb hLb θ₀ hθ₀ y _
    rw [List.eq_of_mem_replicate hLb, hblk, mem_closedBall_zero_iff]
    exact normMultiHeadBlock_forward_inv hd (γ θ₀) (β θ₀) (hγB θ₀ hθ₀) (hβB θ₀ hθ₀) scale
      (WQ θ₀) (WK θ₀) (WVO θ₀) y

open Capacity in
/-- **Untied (standard-transformer) depth-`L` multi-head weight-Lipschitz.** As
`normMultiHeadStack_weight_lip`, but over `List.ofFn` of `L` *distinct* blocks, each layer `i` reading
its own decoders `(WQ i, WK i, WVO i, γ i, β i)` (disjoint parameter coordinates). The constants are
shared across layers, so the envelope is identical; only the weight-tying is dropped. Same machinery,
`List.mem_ofFn` in place of `List.eq_of_mem_replicate`. -/
theorem normMultiHeadStack_untied_weight_lip {H p L : ℕ} [NeZero n] (hd : 0 < d)
    {scale R B bV βY γW Cγ Cβ Lγ Lβ LWQ LWK LWVO : ℝ} (hscale : 0 < scale) (hB : 0 ≤ B)
    (hbV0 : 0 ≤ bV) (hβY0 : 0 ≤ βY) (hγW0 : 0 ≤ γW) (hCγ0 : 0 ≤ Cγ) (_hCβ0 : 0 ≤ Cβ) (hLγ0 : 0 ≤ Lγ)
    (hLβ0 : 0 ≤ Lβ) (hLWQ0 : 0 ≤ LWQ) (hLWK0 : 0 ≤ LWK) (hLWVO0 : 0 ≤ LWVO)
    (WQ WK WVO : Fin L → ParamSpace p → (Fin H → Fin d → Fin d → ℝ))
    (γ β : Fin L → ParamSpace p → (Fin d → ℝ))
    (hγB : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ i θ j| ≤ Cγ)
    (hβB : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β i θ j| ≤ Cβ)
    (hβYD : ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ k, (∑ a, |y k a|) ≤ βY)
    (hQB : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h a e, |matMulCoord (WQ i θ h) y a e| ≤ B)
    (hKB : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h k' e, |matMulCoord (WK i θ h) y k' e| ≤ B)
    (hVB : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h j, ‖matMulCoord (WVO i θ h) y j‖ ≤ bV)
    (hγWQ : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j,
      (∑ k, |WQ i θ h k j|) ≤ γW)
    (hγWK : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j,
      (∑ k, |WK i θ h k j|) ≤ γW)
    (hγWVO : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j,
      (∑ k, |WVO i θ h k j|) ≤ γW)
    (hγLip : ∀ i, ∀ θ θ', dist (γ i θ) (γ i θ') ≤ Lγ * dist θ θ')
    (hβLip : ∀ i, ∀ θ θ', dist (β i θ) (β i θ') ≤ Lβ * dist θ θ')
    (hWQLip : ∀ i, ∀ θ θ', dist (WQ i θ) (WQ i θ') ≤ LWQ * dist θ θ')
    (hWKLip : ∀ i, ∀ θ θ', dist (WK i θ) (WK i θ') ≤ LWK * dist θ θ')
    (hWVOLip : ∀ i, ∀ θ θ', dist (WVO i θ) (WVO i θ') ≤ LWVO * dist θ θ')
    {θ θ' : ParamSpace p} (hθ : θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))))
    (hθ' : θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))))
    {x : Fin n → Fin d → ℝ} (hx : x ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ)) :
    dist (lparamComp (List.ofFn (fun i => normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0
            hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 (WQ i) (WK i) (WVO i) (γ i) (β i))) θ x)
         (lparamComp (List.ofFn (fun i => normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0
            hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 (WQ i) (WK i) (WVO i) (γ i) (β i))) θ' x)
      ≤ lparamLipBound (List.ofFn (fun i => normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0
          hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 (WQ i) (WK i) (WVO i) (γ i) (β i))) * dist θ θ' := by
  refine paramComp_param_lipschitz_on'
    (K := (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))))
    (D := Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ)) _ ?_ ?_ ?_ hθ hθ' hx
  · intro Lb hLb θ₀ hθ₀ a ha b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hLb
    exact normMultiHeadBlock_input_lip hd hscale hB hbV0 hγW0 (WQ i θ₀) (WK i θ₀) (WVO i θ₀)
      (hγWQ i θ₀ hθ₀) (hγWK i θ₀ hθ₀) (hγWVO i θ₀ hθ₀) (γ i θ₀) (β i θ₀) (hγB i θ₀ hθ₀) a b
      (hQB i θ₀ hθ₀ b hb) (hKB i θ₀ hθ₀ a ha) (hVB i θ₀ hθ₀ a ha)
  · intro Lb hLb θ₀ hθ₀ θ₁ hθ₁ y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hLb
    refine le_trans (normMultiHeadBlock_param_lip hd hscale hB hbV0 hβY0 (WQ i θ₀) (WK i θ₀) (WVO i θ₀)
      (WQ i θ₁) (WK i θ₁) (WVO i θ₁) (γ i θ₀) (β i θ₀) (γ i θ₁) (β i θ₁) (hγB i θ₁ hθ₁) y (hβYD y hy)
      (hQB i θ₁ hθ₁ y hy) (hKB i θ₀ hθ₀ y hy) (hVB i θ₀ hθ₀ y hy)) ?_
    rw [show ((normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0
            (WQ i) (WK i) (WVO i) (γ i) (β i)).paramLip) * dist θ₀ θ₁
        = (Real.sqrt d * (Lγ * dist θ₀ θ₁) + Lβ * dist θ₀ θ₁)
          + Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon
            * ((H : ℝ) * (2 * bV * ((d : ℝ) * B / scale)
                * (βY * (LWQ * dist θ₀ θ₁) + βY * (LWK * dist θ₀ θ₁))
              + βY * (LWVO * dist θ₀ θ₁))) from by simp only [normMultiHeadBlock]; ring]
    gcongr
    · exact hγLip i θ₀ θ₁
    · exact hβLip i θ₀ θ₁
    · exact hWQLip i θ₀ θ₁
    · exact hWKLip i θ₀ θ₁
    · exact hWVOLip i θ₀ θ₁
  · intro Lb hLb θ₀ hθ₀ y _
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hLb
    rw [mem_closedBall_zero_iff]
    exact normMultiHeadBlock_forward_inv hd (γ i θ₀) (β i θ₀) (hγB i θ₀ hθ₀) (hβB i θ₀ hθ₀) scale
      (WQ i θ₀) (WK i θ₀) (WVO i θ₀) y

open Capacity in
/-- **Depth-graded true-multi-head certified generalization bound.** For a depth-`L` stack of post-norm
true-multi-head attention blocks `B_θ(X) = layerNorm_{γ θ, β θ}(X + ∑_{h<H} headQK^h(X))`, with
distinct learnable query/key/value projections per head, presented as the executed layer list `Ls` whose
ideal forward at the certified weights is the clamped stack (`hagree`): except on a sample event of
McDiarmid-small probability, the executed true risk is at most the executed empirical risk plus the
closed capacity budget `2·(12√2·(1/√m)·B_int) + ε` and the rounding correction `2·Lℓ·envBound`. The
capacity constant `lparamLipBound (replicate L block)` grows with depth `L` and head count `H` and is
**independent of the sequence length**. The input cap (clamp to the layer-norm activation ball) is the
Kim et al. boundary the bilinear scores force. -/
theorem normMultiHeadStack_certified_generalization {H p m : ℕ} [NeZero n] [Nonempty (Fin p)]
    [MeasurableSpace (Fin n → Fin d → ℝ)] [BorelSpace (Fin n → Fin d → ℝ)]
    {P : Measure (Fin n → Fin d → ℝ)} [IsProbabilityMeasure P] (hm : 0 < m)
    {R B bV βY γW scale Cγ Cβ Lγ Lβ LWQ LWK LWVO : ℝ} (hR : 0 ≤ R) (hscale : 0 < scale) (hd : 0 < d)
    (hB : 0 ≤ B) (hbV0 : 0 ≤ bV) (hβY0 : 0 ≤ βY) (hγW0 : 0 ≤ γW) (hCγ0 : 0 ≤ Cγ) (hCβ0 : 0 ≤ Cβ)
    (hLγ0 : 0 ≤ Lγ) (hLβ0 : 0 ≤ Lβ) (hLWQ0 : 0 ≤ LWQ) (hLWK0 : 0 ≤ LWK) (hLWVO0 : 0 ≤ LWVO)
    (WQ WK WVO : ParamSpace p → (Fin H → Fin d → Fin d → ℝ)) (γ β : ParamSpace p → (Fin d → ℝ))
    (hWQcont : Continuous WQ) (hWKcont : Continuous WK) (hWVOcont : Continuous WVO)
    (hγcont : Continuous γ) (hβcont : Continuous β)
    (hγB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ θ j| ≤ Cγ)
    (hβB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β θ j| ≤ Cβ)
    (hβYD : ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ i, (∑ a, |y i a|) ≤ βY)
    (hQB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h i e, |matMulCoord (WQ θ h) y i e| ≤ B)
    (hKB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h k' e, |matMulCoord (WK θ h) y k' e| ≤ B)
    (hVB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h j, ‖matMulCoord (WVO θ h) y j‖ ≤ bV)
    (hγWQ : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WQ θ h k j|) ≤ γW)
    (hγWK : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WK θ h k j|) ≤ γW)
    (hγWVO : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WVO θ h k j|) ≤ γW)
    (hγLip : ∀ θ θ', dist (γ θ) (γ θ') ≤ Lγ * dist θ θ')
    (hβLip : ∀ θ θ', dist (β θ) (β θ') ≤ Lβ * dist θ θ')
    (hWQLip : ∀ θ θ', dist (WQ θ) (WQ θ') ≤ LWQ * dist θ θ')
    (hWKLip : ∀ θ θ', dist (WK θ) (WK θ') ≤ LWK * dist θ θ')
    (hWVOLip : ∀ θ θ', dist (WVO θ) (WVO θ') ≤ LWVO * dist θ θ')
    (ℓ : (Fin n → Fin d → ℝ) → ℝ) {b : ℝ} (hb : 0 < b) (hℓb : ∀ v, |ℓ v| ≤ b)
    (hℓcont : Continuous ℓ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ) (hℓLip : ∀ u v, |ℓ u - ℓ v| ≤ Lℓ * dist u v)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R) (L : ℕ)
    (Ls : List (ExecLayer (Fin n → Fin d → ℝ)))
    (hagree : ∀ x, idealComp Ls x
        = lparamComp (List.replicate L (normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0
            hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 WQ WK WVO γ β))
            (embedBase Capacity.Dyadic w_T.1) (clampCoord (Real.sqrt d * Cγ + Cβ) x))
    (hintG : Integrable (fun x => ℓ (execComp Ls x)) P)
    (hLpos : 0 < Lℓ * lparamLipBound (List.replicate L (normMultiHeadBlock (n := n) hscale hB hbV0
        hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 WQ WK WVO γ β))) :
    (Measure.pi fun _ : Fin m => P).real
        {S | ¬ ((∫ x, ℓ (execComp Ls x) ∂P)
              ≤ (1 / (m : ℝ)) * ∑ i, ℓ (execComp Ls (S i))
                + (2 * ((12 * Real.sqrt 2) * (1 / Real.sqrt m)
                    * (∫⁻ ε in Set.Ioc (0 : ℝ) (2 * b),
                        ENNReal.ofReal (Real.sqrt (Real.log 2)
                          + Real.sqrt ((p : ℝ) * (4 * R * (Lℓ * lparamLipBound
                              (List.replicate L (normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0
                                hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 WQ WK WVO γ β)))))
                            * ε ^ (-(1 / 2) : ℝ))).toReal) + ε)
                + 2 * (Lℓ * envBound Ls))}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) := by
  set blk := normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0
    WQ WK WVO γ β with hblk
  set ρ := Real.sqrt d * Cγ + Cβ with hρ
  have hρ0 : (0 : ℝ) ≤ ρ := add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCγ0) hCβ0
  set F : ParamSpace p → (Fin n → Fin d → ℝ) → ℝ :=
    fun θ x => ℓ (lparamComp (List.replicate L blk) θ (clampCoord ρ x)) with hF
  have hblkcont : ∀ Lb ∈ List.replicate L blk,
      Continuous (fun pq : ParamSpace p × (Fin n → Fin d → ℝ) => Lb.map pq.1 pq.2) := by
    intro Lb hLb; rw [List.eq_of_mem_replicate hLb, hblk]
    exact continuous_normMultiHeadBlock_weight hWQcont hWKcont hWVOcont hγcont hβcont
  have hstackcont : Continuous (fun pq : ParamSpace p × (Fin n → Fin d → ℝ) =>
      lparamComp (List.replicate L blk) pq.1 pq.2) := continuous_lparamComp_uncurry _ hblkcont
  have hFb : ∀ θ x, |F θ x| ≤ b := fun θ x => hℓb _
  have hFcont : ∀ x, Continuous fun θ : ParamSpace p => F θ x := fun x =>
    hℓcont.comp (hstackcont.comp (continuous_id.prodMk continuous_const))
  have hFmeas : ∀ θ, Measurable (F θ) := fun θ =>
    (hℓcont.comp ((hstackcont.comp (continuous_const.prodMk continuous_id)).comp
      (continuous_clampCoord ρ))).measurable
  have hbridge : ∀ x, F (embedBase Capacity.Dyadic w_T.1) x = ℓ (idealComp Ls x) :=
    fun x => by simp only [hF]; rw [hagree x]
  have hintF : Integrable (fun x => ℓ (idealComp Ls x)) P := by
    have heq : (fun x => ℓ (idealComp Ls x)) = F (embedBase Capacity.Dyadic w_T.1) :=
      funext fun x => (hbridge x).symm
    rw [heq]; exact integrable_of_bound_of_measurable (hFmeas _) (fun x => hFb _ x)
  have hlip : ∀ S : Fin m → (Fin n → Fin d → ℝ),
      ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      dist (valueVec F S θ) (valueVec F S θ')
        ≤ Lℓ * lparamLipBound (List.replicate L blk) * dist θ θ' := by
    intro S θ hθ θ' hθ'
    refine (dist_pi_le_iff (mul_nonneg hLpos.le dist_nonneg)).mpr (fun j => ?_)
    rw [Real.dist_eq]; simp only [valueVec, hF]
    have hclampmem : clampCoord ρ (S j) ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) ρ := by
      rw [mem_closedBall_zero_iff]; exact clampCoord_norm_le hρ0 (S j)
    calc |ℓ (lparamComp (List.replicate L blk) θ (clampCoord ρ (S j)))
            - ℓ (lparamComp (List.replicate L blk) θ' (clampCoord ρ (S j)))|
        ≤ Lℓ * dist (lparamComp (List.replicate L blk) θ (clampCoord ρ (S j)))
              (lparamComp (List.replicate L blk) θ' (clampCoord ρ (S j))) := hℓLip _ _
      _ ≤ Lℓ * (lparamLipBound (List.replicate L blk) * dist θ θ') :=
          mul_le_mul_of_nonneg_left
            (normMultiHeadStack_weight_lip hd hscale hB hbV0 hβY0 hγW0 hCγ0 hCβ0 hLγ0 hLβ0 hLWQ0
              hLWK0 hLWVO0 WQ WK WVO γ β hγB hβB hβYD hQB hKB hVB hγWQ hγWK hγWVO hγLip hβLip hWQLip
              hWKLip hWVOLip L hθ hθ' hclampmem) hLℓ0
      _ = Lℓ * lparamLipBound (List.replicate L blk) * dist θ θ' := by ring
  exact certified_executed_generalization_dudley hm hR F hb hFb hFmeas hFcont hε w_T Ls ℓ hLℓ0
    hℓLip hbridge hintF hintG hLpos hlip

open Capacity in
/-- **Untied (standard-transformer) depth-`L` true-multi-head certified generalization bound.** As
`normMultiHeadStack_certified_generalization`, but over `List.ofFn` of `L` distinct blocks: the
standard (non-weight-tied) transformer regime, each layer reading its own parameter coordinates. -/
theorem normMultiHeadStack_untied_certified_generalization {H p L m : ℕ} [NeZero n] [Nonempty (Fin p)]
    [MeasurableSpace (Fin n → Fin d → ℝ)] [BorelSpace (Fin n → Fin d → ℝ)]
    {P : Measure (Fin n → Fin d → ℝ)} [IsProbabilityMeasure P] (hm : 0 < m)
    {R B bV βY γW scale Cγ Cβ Lγ Lβ LWQ LWK LWVO : ℝ} (hR : 0 ≤ R) (hscale : 0 < scale) (hd : 0 < d)
    (hB : 0 ≤ B) (hbV0 : 0 ≤ bV) (hβY0 : 0 ≤ βY) (hγW0 : 0 ≤ γW) (hCγ0 : 0 ≤ Cγ) (hCβ0 : 0 ≤ Cβ)
    (hLγ0 : 0 ≤ Lγ) (hLβ0 : 0 ≤ Lβ) (hLWQ0 : 0 ≤ LWQ) (hLWK0 : 0 ≤ LWK) (hLWVO0 : 0 ≤ LWVO)
    (WQ WK WVO : Fin L → ParamSpace p → (Fin H → Fin d → Fin d → ℝ))
    (γ β : Fin L → ParamSpace p → (Fin d → ℝ))
    (hWQcont : ∀ i, Continuous (WQ i)) (hWKcont : ∀ i, Continuous (WK i))
    (hWVOcont : ∀ i, Continuous (WVO i)) (hγcont : ∀ i, Continuous (γ i)) (hβcont : ∀ i, Continuous (β i))
    (hγB : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ i θ j| ≤ Cγ)
    (hβB : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β i θ j| ≤ Cβ)
    (hβYD : ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ k, (∑ a, |y k a|) ≤ βY)
    (hQB : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h a e, |matMulCoord (WQ i θ h) y a e| ≤ B)
    (hKB : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h k' e, |matMulCoord (WK i θ h) y k' e| ≤ B)
    (hVB : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h j, ‖matMulCoord (WVO i θ h) y j‖ ≤ bV)
    (hγWQ : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j,
      (∑ k, |WQ i θ h k j|) ≤ γW)
    (hγWK : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j,
      (∑ k, |WK i θ h k j|) ≤ γW)
    (hγWVO : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j,
      (∑ k, |WVO i θ h k j|) ≤ γW)
    (hγLip : ∀ i, ∀ θ θ', dist (γ i θ) (γ i θ') ≤ Lγ * dist θ θ')
    (hβLip : ∀ i, ∀ θ θ', dist (β i θ) (β i θ') ≤ Lβ * dist θ θ')
    (hWQLip : ∀ i, ∀ θ θ', dist (WQ i θ) (WQ i θ') ≤ LWQ * dist θ θ')
    (hWKLip : ∀ i, ∀ θ θ', dist (WK i θ) (WK i θ') ≤ LWK * dist θ θ')
    (hWVOLip : ∀ i, ∀ θ θ', dist (WVO i θ) (WVO i θ') ≤ LWVO * dist θ θ')
    (ℓ : (Fin n → Fin d → ℝ) → ℝ) {b : ℝ} (hb : 0 < b) (hℓb : ∀ v, |ℓ v| ≤ b)
    (hℓcont : Continuous ℓ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ) (hℓLip : ∀ u v, |ℓ u - ℓ v| ≤ Lℓ * dist u v)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R)
    (Ls : List (ExecLayer (Fin n → Fin d → ℝ)))
    (hagree : ∀ x, idealComp Ls x
        = lparamComp (List.ofFn (fun i => normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0
            hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 (WQ i) (WK i) (WVO i) (γ i) (β i)))
            (embedBase Capacity.Dyadic w_T.1) (clampCoord (Real.sqrt d * Cγ + Cβ) x))
    (hintG : Integrable (fun x => ℓ (execComp Ls x)) P)
    (hLpos : 0 < Lℓ * lparamLipBound (List.ofFn (fun i => normMultiHeadBlock (n := n) hscale hB hbV0
        hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 (WQ i) (WK i) (WVO i) (γ i) (β i)))) :
    (Measure.pi fun _ : Fin m => P).real
        {S | ¬ ((∫ x, ℓ (execComp Ls x) ∂P)
              ≤ (1 / (m : ℝ)) * ∑ i, ℓ (execComp Ls (S i))
                + (2 * ((12 * Real.sqrt 2) * (1 / Real.sqrt m)
                    * (∫⁻ ε in Set.Ioc (0 : ℝ) (2 * b),
                        ENNReal.ofReal (Real.sqrt (Real.log 2)
                          + Real.sqrt ((p : ℝ) * (4 * R * (Lℓ * lparamLipBound
                              (List.ofFn (fun i => normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0
                                hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 (WQ i) (WK i) (WVO i) (γ i) (β i))))))
                            * ε ^ (-(1 / 2) : ℝ))).toReal) + ε)
                + 2 * (Lℓ * envBound Ls))}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) := by
  set blks := fun i => normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0
    hLWVO0 (WQ i) (WK i) (WVO i) (γ i) (β i) with hblks
  set ρ := Real.sqrt d * Cγ + Cβ with hρ
  have hρ0 : (0 : ℝ) ≤ ρ := add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCγ0) hCβ0
  set F : ParamSpace p → (Fin n → Fin d → ℝ) → ℝ :=
    fun θ x => ℓ (lparamComp (List.ofFn blks) θ (clampCoord ρ x)) with hF
  have hblkcont : ∀ Lb ∈ List.ofFn blks,
      Continuous (fun pq : ParamSpace p × (Fin n → Fin d → ℝ) => Lb.map pq.1 pq.2) := by
    intro Lb hLb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hLb
    exact continuous_normMultiHeadBlock_weight (hWQcont i) (hWKcont i) (hWVOcont i) (hγcont i) (hβcont i)
  have hstackcont : Continuous (fun pq : ParamSpace p × (Fin n → Fin d → ℝ) =>
      lparamComp (List.ofFn blks) pq.1 pq.2) := continuous_lparamComp_uncurry _ hblkcont
  have hFb : ∀ θ x, |F θ x| ≤ b := fun θ x => hℓb _
  have hFcont : ∀ x, Continuous fun θ : ParamSpace p => F θ x := fun x =>
    hℓcont.comp (hstackcont.comp (continuous_id.prodMk continuous_const))
  have hFmeas : ∀ θ, Measurable (F θ) := fun θ =>
    (hℓcont.comp ((hstackcont.comp (continuous_const.prodMk continuous_id)).comp
      (continuous_clampCoord ρ))).measurable
  have hbridge : ∀ x, F (embedBase Capacity.Dyadic w_T.1) x = ℓ (idealComp Ls x) :=
    fun x => by simp only [hF]; rw [hagree x]
  have hintF : Integrable (fun x => ℓ (idealComp Ls x)) P := by
    have heq : (fun x => ℓ (idealComp Ls x)) = F (embedBase Capacity.Dyadic w_T.1) :=
      funext fun x => (hbridge x).symm
    rw [heq]; exact integrable_of_bound_of_measurable (hFmeas _) (fun x => hFb _ x)
  have hlip : ∀ S : Fin m → (Fin n → Fin d → ℝ),
      ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      dist (valueVec F S θ) (valueVec F S θ')
        ≤ Lℓ * lparamLipBound (List.ofFn blks) * dist θ θ' := by
    intro S θ hθ θ' hθ'
    refine (dist_pi_le_iff (mul_nonneg hLpos.le dist_nonneg)).mpr (fun j => ?_)
    rw [Real.dist_eq]; simp only [valueVec, hF]
    have hclampmem : clampCoord ρ (S j) ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) ρ := by
      rw [mem_closedBall_zero_iff]; exact clampCoord_norm_le hρ0 (S j)
    calc |ℓ (lparamComp (List.ofFn blks) θ (clampCoord ρ (S j)))
            - ℓ (lparamComp (List.ofFn blks) θ' (clampCoord ρ (S j)))|
        ≤ Lℓ * dist (lparamComp (List.ofFn blks) θ (clampCoord ρ (S j)))
              (lparamComp (List.ofFn blks) θ' (clampCoord ρ (S j))) := hℓLip _ _
      _ ≤ Lℓ * (lparamLipBound (List.ofFn blks) * dist θ θ') :=
          mul_le_mul_of_nonneg_left
            (normMultiHeadStack_untied_weight_lip hd hscale hB hbV0 hβY0 hγW0 hCγ0 hCβ0 hLγ0 hLβ0
              hLWQ0 hLWK0 hLWVO0 WQ WK WVO γ β hγB hβB hβYD hQB hKB hVB hγWQ hγWK hγWVO hγLip hβLip
              hWQLip hWKLip hWVOLip hθ hθ' hclampmem) hLℓ0
      _ = Lℓ * lparamLipBound (List.ofFn blks) * dist θ θ' := by ring
  exact certified_executed_generalization_dudley hm hR F hb hFb hFmeas hFcont hε w_T Ls ℓ hLℓ0
    hℓLip hbridge hintF hintG hLpos hlip

end TLT
