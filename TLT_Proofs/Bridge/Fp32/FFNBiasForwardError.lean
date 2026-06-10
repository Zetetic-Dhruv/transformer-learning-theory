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

end TLT.Fp32FFNBias
