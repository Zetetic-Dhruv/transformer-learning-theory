/-
# Rectangular executed matmul + the bias-cancellation affine forward error

The pure-ℝ foundation of the FFN→`Spec.FeedForward` bridge. `VexecRect` is the rectangular twin of `Vexec`
(output dim `p ≠` contraction dim `n`) — a re-parametrization, since `rdot`/`rdotBudget`/`matMulCoord` are
all dimension-generic in the contraction. `affExec` adds a bias; the elegant collapse is that **the bias is
an exact additive offset in ℝ, so it cancels in the executed-vs-ideal difference** — the affine forward
error is *exactly* the matmul forward error, no bias term. (The bias's fp32-add rounding lives only in the
later `toReal` bridge, via the shipped `toReal_add_abs_error_of_isFinite`.)
-/
import TLT_Proofs.Bridge.Fp32.FFNForwardError

open TorchLean.Floats (neuralMagnitude neuralBpow binaryRadix)
open TorchLean.Floats.IEEE754.IEEE32Exec

noncomputable section

namespace TLT.Fp32FFNBias

open TLT TLT.Fp32Attn TLT.Fp32FFN

/-- **The rectangular executed (rounded) matmul.** Output dim `p` need not equal the contraction dim `n`.
Same body as `Vexec` (`fun i j => rdot (X i) (W·j)`); the value is the binary32 dot product read over ℝ. -/
def VexecRect {m n p : ℕ} (W : Fin n → Fin p → ℝ) (X : Fin m → Fin n → ℝ) : Fin m → Fin p → ℝ :=
  fun i j => rdot (X i) (fun k => W k j)

/-- Normal-range side conditions of every rectangular reduction. -/
def VexecRectNormal {m n p : ℕ} (W : Fin n → Fin p → ℝ) (X : Fin m → Fin n → ℝ) : Prop :=
  ∀ i j, RdotNormal (X i) (fun k => W k j)

/-- **Per-entry rectangular matmul rounding error** — mirrors `Vexec_entry_error`, contraction over
`Fin n` for any output `Fin p`, reusing the dimension-generic `rdot_error_le_of_sum_bound`. -/
lemma VexecRect_entry_error {m n p : ℕ} (W : Fin n → Fin p → ℝ) (X : Fin m → Fin n → ℝ)
    {B Λ : ℝ} (hB : 0 ≤ B) (_hΛ0 : 0 ≤ Λ) (hX : ∀ i k, |X i k| ≤ B)
    (hW : ∀ j, ∑ k, |W k j| ≤ Λ) (hnorm : VexecRectNormal W X) (hnu : (n : ℝ) * u < 1)
    (i : Fin m) (j : Fin p) :
    |VexecRect W X i j - matMulCoord W X i j| ≤ rdotBudget n (B * Λ) := by
  have hkey : ∑ k, |(X i) k * (fun k => W k j) k| ≤ B * Λ := by
    calc ∑ k, |(X i) k * (fun k => W k j) k|
        = ∑ k, |X i k| * |W k j| := by
          refine Finset.sum_congr rfl (fun k _ => ?_); rw [abs_mul]
      _ ≤ ∑ k, B * |W k j| :=
          Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hX i k) (abs_nonneg _))
      _ = B * ∑ k, |W k j| := by rw [Finset.mul_sum]
      _ ≤ B * Λ := mul_le_mul_of_nonneg_left (hW j) hB
  have he : matMulCoord W X i j = ∑ k, (X i) k * (fun k => W k j) k := by simp only [matMulCoord]
  rw [VexecRect, he]
  exact rdot_error_le_of_sum_bound (X i) (fun k => W k j) (hnorm i j) hnu hkey

/-- **Rectangular matmul forward error (sup norm).** -/
lemma VexecRect_error {m n p : ℕ} (W : Fin n → Fin p → ℝ) (X : Fin m → Fin n → ℝ)
    {B Λ : ℝ} (hB : 0 ≤ B) (hΛ0 : 0 ≤ Λ) (hX : ∀ i k, |X i k| ≤ B)
    (hW : ∀ j, ∑ k, |W k j| ≤ Λ) (hnorm : VexecRectNormal W X) (hnu : (n : ℝ) * u < 1) :
    ‖VexecRect W X - matMulCoord W X‖ ≤ rdotBudget n (B * Λ) := by
  have hbud : 0 ≤ rdotBudget n (B * Λ) := rdotBudget_nonneg hnu (mul_nonneg hB hΛ0)
  refine (pi_norm_le_iff_of_nonneg hbud).mpr (fun i => ?_)
  refine (pi_norm_le_iff_of_nonneg hbud).mpr (fun j => ?_)
  rw [Real.norm_eq_abs, Pi.sub_apply, Pi.sub_apply]
  exact VexecRect_entry_error W X hB hΛ0 hX hW hnorm hnu i j

/-- **The executed affine** `Vexec W X + b` (ℝ-model; the bias's fp32-add rounding is deferred to the
`toReal` bridge). The ideal is `matMulCoord W X + b`. -/
def affExec {m n p : ℕ} (W : Fin n → Fin p → ℝ) (b : Fin p → ℝ) (X : Fin m → Fin n → ℝ) :
    Fin m → Fin p → ℝ :=
  fun i j => VexecRect W X i j + b j

/-- The ideal (exact-real) affine. -/
def affIdeal {m n p : ℕ} (W : Fin n → Fin p → ℝ) (b : Fin p → ℝ) (X : Fin m → Fin n → ℝ) :
    Fin m → Fin p → ℝ :=
  fun i j => matMulCoord W X i j + b j

/-- **The bias-cancellation affine forward error.** The bias is an exact additive offset in ℝ, so it
cancels in the difference: `affExec − affIdeal = VexecRect − matMulCoord`. The affine error is therefore
*exactly* the matmul error — the bias costs nothing in the ℝ-model. -/
lemma affExec_forward_error {m n p : ℕ} (W : Fin n → Fin p → ℝ) (b : Fin p → ℝ) (X : Fin m → Fin n → ℝ)
    {B Λ : ℝ} (hB : 0 ≤ B) (hΛ0 : 0 ≤ Λ) (hX : ∀ i k, |X i k| ≤ B)
    (hW : ∀ j, ∑ k, |W k j| ≤ Λ) (hnorm : VexecRectNormal W X) (hnu : (n : ℝ) * u < 1) :
    ‖affExec W b X - affIdeal W b X‖ ≤ rdotBudget n (B * Λ) := by
  have heq : affExec W b X - affIdeal W b X = VexecRect W X - matMulCoord W X := by
    funext i j
    simp only [affExec, affIdeal, Pi.sub_apply]
    ring
  rw [heq]
  exact VexecRect_error W X hB hΛ0 hX hW hnorm hnu

/-- **The rectangular ideal matmul is `Λ`-Lipschitz in its input (sup norm).** The rectangular twin of
`matMulCoord_lipschitz`: output dim `q` need not equal the contraction dim `p`. With the contracted columns
of `W` bounded `∑ₖ|Wₖⱼ| ≤ Λ`, the map `X ↦ matMulCoord W X` satisfies
`‖matMulCoord W a − matMulCoord W b‖ ≤ Λ · ‖a − b‖` — each output entry is an `ℓ¹(W)`-weighted combination
of input gaps. The proof never uses squareness (contraction over `Fin p`, output `Fin q`). -/
lemma matMulCoordRect_lipschitz {s p q : ℕ} (W : Fin p → Fin q → ℝ) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hW : ∀ j, (∑ k, |W k j|) ≤ Λ) (a b : Fin s → Fin p → ℝ) :
    ‖matMulCoord W a - matMulCoord W b‖ ≤ Λ * ‖a - b‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => ?_)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun j => ?_)
  rw [Real.norm_eq_abs, Pi.sub_apply, Pi.sub_apply]
  simp only [matMulCoord, ← Finset.sum_sub_distrib, ← sub_mul]
  calc |∑ k, (a i k - b i k) * W k j|
      ≤ ∑ k, |a i k - b i k| * |W k j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => abs_mul _ _))
    _ ≤ ∑ k, ‖a - b‖ * |W k j| := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        calc |a i k - b i k| = ‖(a - b) i k‖ := by rw [Real.norm_eq_abs, Pi.sub_apply, Pi.sub_apply]
          _ ≤ ‖(a - b) i‖ := norm_le_pi_norm ((a - b) i) k
          _ ≤ ‖a - b‖ := norm_le_pi_norm (a - b) i
    _ = ‖a - b‖ * (∑ k, |W k j|) := by rw [← Finset.mul_sum]
    _ ≤ ‖a - b‖ * Λ := mul_le_mul_of_nonneg_left (hW j) (norm_nonneg _)
    _ = Λ * ‖a - b‖ := by ring

/-- **The executed FFN block with biases and a hidden dimension** — `affExec W2 b2 ∘ reluCoord ∘
affExec W1 b1`, the ℝ-model of `Spec.FeedForward.forward` read over ℝ (the bias roundings deferred to the
`toReal` bridge). -/
def ffnExecBias {n d h : ℕ} (W1 : Fin d → Fin h → ℝ) (b1 : Fin h → ℝ) (W2 : Fin h → Fin d → ℝ)
    (b2 : Fin d → ℝ) (X : Fin n → Fin d → ℝ) : Fin n → Fin d → ℝ :=
  affExec W2 b2 (reluCoord (affExec W1 b1 X))

/-- **The hidden-dim + bias FFN forward error.** `‖ffnExecBias − ffnCoord‖ ≤ rdotBudget h (B2'·Λ) +
Λ·rdotBudget d (B·Λ)`, the exact generalization of the square no-bias `ffnExec_forward_error`. The biases
cancel in BOTH legs (`affExec_forward_error`); they only shift the second matmul's input bound `B2'` (the
relu output, carried). Mirrors the triangle: second-leg matmul error ⊕ ideal-second-matmul Lipschitz on
the relu difference ⊕ first-leg matmul error. -/
lemma ffnExecBias_forward_error {n d h : ℕ} (W1 : Fin d → Fin h → ℝ) (b1 : Fin h → ℝ)
    (W2 : Fin h → Fin d → ℝ) (b2 : Fin d → ℝ) (X : Fin n → Fin d → ℝ)
    {B Λ B2' : ℝ} (hB : 0 ≤ B) (hΛ : 0 ≤ Λ) (hB2' : 0 ≤ B2') (hX : ∀ i k, |X i k| ≤ B)
    (hW1 : ∀ j, ∑ k, |W1 k j| ≤ Λ) (hW2 : ∀ j, ∑ k, |W2 k j| ≤ Λ)
    (hnorm1 : VexecRectNormal W1 X)
    (hnorm2 : VexecRectNormal W2 (reluCoord (affExec W1 b1 X)))
    (hreluB : ∀ i k, |reluCoord (affExec W1 b1 X) i k| ≤ B2')
    (hdu : (d : ℝ) * u < 1) (hhu : (h : ℝ) * u < 1) :
    ‖ffnExecBias W1 b1 W2 b2 X - ffnCoord W1 b1 W2 b2 X‖
      ≤ rdotBudget h (B2' * Λ) + Λ * rdotBudget d (B * Λ) := by
  have hfc : ffnCoord W1 b1 W2 b2 X = affIdeal W2 b2 (reluCoord (affIdeal W1 b1 X)) := by
    funext i j
    show (∑ l, max (matMulCoord W1 X i l + b1 l) 0 * W2 l j) + b2 j
        = (∑ l, reluCoord (affIdeal W1 b1 X) i l * W2 l j) + b2 j
    congr 1
  have hA : ‖affExec W2 b2 (reluCoord (affExec W1 b1 X))
        - affIdeal W2 b2 (reluCoord (affExec W1 b1 X))‖ ≤ rdotBudget h (B2' * Λ) :=
    affExec_forward_error W2 b2 (reluCoord (affExec W1 b1 X)) hB2' hΛ hreluB hW2 hnorm2 hhu
  have hfirst : ‖affExec W1 b1 X - affIdeal W1 b1 X‖ ≤ rdotBudget d (B * Λ) :=
    affExec_forward_error W1 b1 X hB hΛ hX hW1 hnorm1 hdu
  have hB2 : ‖affIdeal W2 b2 (reluCoord (affExec W1 b1 X))
        - affIdeal W2 b2 (reluCoord (affIdeal W1 b1 X))‖ ≤ Λ * rdotBudget d (B * Λ) := by
    have hcancel : affIdeal W2 b2 (reluCoord (affExec W1 b1 X))
          - affIdeal W2 b2 (reluCoord (affIdeal W1 b1 X))
        = matMulCoord W2 (reluCoord (affExec W1 b1 X)) - matMulCoord W2 (reluCoord (affIdeal W1 b1 X)) := by
      funext i j; simp only [affIdeal, Pi.sub_apply]; ring
    rw [hcancel]
    calc ‖matMulCoord W2 (reluCoord (affExec W1 b1 X)) - matMulCoord W2 (reluCoord (affIdeal W1 b1 X))‖
        ≤ Λ * ‖reluCoord (affExec W1 b1 X) - reluCoord (affIdeal W1 b1 X)‖ :=
          matMulCoordRect_lipschitz W2 hΛ hW2 _ _
      _ ≤ Λ * ‖affExec W1 b1 X - affIdeal W1 b1 X‖ :=
          mul_le_mul_of_nonneg_left (reluCoord_lipschitz _ _) hΛ
      _ ≤ Λ * rdotBudget d (B * Λ) := mul_le_mul_of_nonneg_left hfirst hΛ
  calc ‖ffnExecBias W1 b1 W2 b2 X - ffnCoord W1 b1 W2 b2 X‖
      = ‖(affExec W2 b2 (reluCoord (affExec W1 b1 X)) - affIdeal W2 b2 (reluCoord (affExec W1 b1 X)))
          + (affIdeal W2 b2 (reluCoord (affExec W1 b1 X))
              - affIdeal W2 b2 (reluCoord (affIdeal W1 b1 X)))‖ := by
        rw [ffnExecBias, hfc]; congr 1; abel
    _ ≤ ‖affExec W2 b2 (reluCoord (affExec W1 b1 X)) - affIdeal W2 b2 (reluCoord (affExec W1 b1 X))‖
        + ‖affIdeal W2 b2 (reluCoord (affExec W1 b1 X))
            - affIdeal W2 b2 (reluCoord (affIdeal W1 b1 X))‖ := norm_add_le _ _
    _ ≤ rdotBudget h (B2' * Λ) + Λ * rdotBudget d (B * Λ) := add_le_add hA hB2

end TLT.Fp32FFNBias
