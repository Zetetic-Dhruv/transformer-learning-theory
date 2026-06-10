/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Fp32.AttentionForwardError
import TLT_Proofs.Bridge.Fp32.StackActivationExecutedValue

/-!
# A derived fp32 forward-error envelope for the FFN (feed-forward) block

The per-block analogue of `attnLiteralForwardError`: the MLP block `matmul → ReLU → matmul`. The
attention head's value projection is one rounded matmul (`Vexec`, with the derived budget
`rdotBudget d (B·Λ)`); an FFN block stacks **two** such matmuls around one ReLU. This file composes the
shipped matmul forward error (`Vexec_error`) twice with the **rounding-free** ReLU.

The ReLU contributes `rnd = 0`: the bit-level select `maximum x 0` read over ℝ is *exactly*
`max (toReal x) 0` (`TLT.Fp32Stack.reluExec_exact`), so it introduces no arithmetic rounding. The FFN
block's rounding is carried entirely by its two linear maps — matching `ffnBlock_envBound`
(`Forward/LiteralStackMargin.lean`), where a `[linear, ReLU]` block's depth envelope equals the linear
layer's rounding alone.

## Shape of the bound

Triangulating through the intermediate ideal-second-matmul `matMulCoord W2 (reluCoord (Vexec W1 X))`:

* the **second matmul** rounds against its (relu-of-executed-first-matmul) input, whose entries are
  bounded by `B' = B·Λ + rdotBudget d (B·Λ) = bVval d B Λ` (the executed-first-matmul magnitude bound,
  undamaged by ReLU since `|max(t,0)| ≤ |t|`), contributing `rdotBudget d (B'·Λ)`;
* the **first matmul**'s `rdotBudget d (B·Λ)` rounding propagates through the `1`-Lipschitz ReLU and the
  `Λ`-Lipschitz second ideal matmul, contributing `Λ · rdotBudget d (B·Λ)`.

So the FFN forward error is `rdotBudget d (bVval d B Λ · Λ) + Λ · rdotBudget d (B·Λ)`: linear-map
rounding twice, the activation free.

## Main results

- `reluCoord_lipschitz` — the coordinate ReLU is `1`-Lipschitz in the sup norm.
- `ffnExec_forward_error` — the FFN block forward error against the ideal `matmul → ReLU → matmul`.
- `ffnExec_eq_lit` — on a finite fp32 input the executed `reluCoord` is the literal IEEE ReLU
  (`reluExec_exact`); the two `Vexec` matmuls are the executed binary32 matmuls.
-/

open TorchLean.Floats (neuralMagnitude neuralBpow binaryRadix)
open TorchLean.Floats.IEEE754.IEEE32Exec

noncomputable section

namespace TLT.Fp32FFN

open TLT TLT.Fp32Attn

/-- The executed FFN block: `matmul₂ ∘ ReLU ∘ matmul₁` with both matmuls the rounded fp32 matmul
`Vexec` and the ReLU the exact coordinate `max (·) 0`. Read over ℝ this is the literal binary32 MLP
block (every linear op = real op + rounding; the ReLU select rounding-free). -/
def ffnExec {n d : ℕ} (W1 W2 : Fin d → Fin d → ℝ) (X : Fin n → Fin d → ℝ) : Fin n → Fin d → ℝ :=
  Vexec W2 (reluCoord (Vexec W1 X))

/-- The ideal (exact-real) FFN block: `matMulCoord W2 ∘ reluCoord ∘ matMulCoord W1`. -/
def ffnIdeal {n d : ℕ} (W1 W2 : Fin d → Fin d → ℝ) (X : Fin n → Fin d → ℝ) : Fin n → Fin d → ℝ :=
  matMulCoord W2 (reluCoord (matMulCoord W1 X))

/-! ## The ReLU is `1`-Lipschitz coordinatewise -/

/-- **The coordinate ReLU is `1`-Lipschitz in the sup norm.** `‖reluCoord a − reluCoord b‖ ≤ ‖a − b‖`:
each coordinate `max(·) 0` is `1`-Lipschitz (`abs_max_sub_max_le_abs`), and the sup norm of the
difference is the sup of the coordinatewise gaps. The activation neither amplifies nor rounds. -/
lemma reluCoord_lipschitz {n d : ℕ} (a b : Fin n → Fin d → ℝ) :
    ‖reluCoord a - reluCoord b‖ ≤ ‖a - b‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i => ?_)
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun j => ?_)
  rw [Real.norm_eq_abs, Pi.sub_apply, Pi.sub_apply, reluCoord, reluCoord]
  calc |max (a i j) 0 - max (b i j) 0|
      ≤ |a i j - b i j| := abs_max_sub_max_le_abs (a i j) (b i j) 0
    _ = ‖(a - b) i j‖ := by rw [Real.norm_eq_abs, Pi.sub_apply, Pi.sub_apply]
    _ ≤ ‖(a - b) i‖ := norm_le_pi_norm ((a - b) i) j
    _ ≤ ‖a - b‖ := norm_le_pi_norm (a - b) i

/-! ## The second ideal matmul is `Λ`-Lipschitz in the sup norm -/

/-- **The ideal matmul is `Λ`-Lipschitz in its input (sup norm).** With the contracted columns of `W`
bounded `∑ₖ|Wₖⱼ| ≤ Λ`, the map `X ↦ matMulCoord W X` satisfies
`‖matMulCoord W a − matMulCoord W b‖ ≤ Λ · ‖a − b‖`: each output entry is an `ℓ¹(W)`-weighted combination
of input gaps, and the sup norm of the difference is the sup of those entries (the `X`-side mirror of
`linearExecLayer.ideal_lip`). -/
lemma matMulCoord_lipschitz {n d : ℕ} (W : Fin d → Fin d → ℝ) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hW : ∀ j, (∑ k, |W k j|) ≤ Λ) (a b : Fin n → Fin d → ℝ) :
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

/-! ## The relu-output magnitude bound `B' = bVval d B Λ` -/

/-- **The relu-of-executed-first-matmul entries are bounded by `bVval d B Λ`.** The ReLU cannot enlarge
magnitude (`|max(t,0)| ≤ |t|`), so each entry inherits the executed-matmul bound `Vexec_entry_abs_le`:
`|reluCoord (Vexec W1 X) i j| ≤ |Vexec W1 X i j| ≤ B·Λ + rdotBudget d (B·Λ) = bVval d B Λ`. This is the
input bound `B'` for the second matmul's rounding. -/
lemma reluCoord_Vexec_entry_abs_le {n d : ℕ} (W1 : Fin d → Fin d → ℝ) (X : Fin n → Fin d → ℝ)
    {B Λ : ℝ} (hB : 0 ≤ B) (hΛ0 : 0 ≤ Λ) (hX : ∀ i k, |X i k| ≤ B)
    (hW1 : ∀ j, ∑ k, |W1 k j| ≤ Λ) (hnorm1 : VexecNormal W1 X) (hdu : (d : ℝ) * u < 1)
    (i : Fin n) (k : Fin d) :
    |reluCoord (Vexec W1 X) i k| ≤ bVval d B Λ := by
  have hrelu : |reluCoord (Vexec W1 X) i k| ≤ |Vexec W1 X i k| := by
    rw [reluCoord]
    rcases le_total (Vexec W1 X i k) 0 with hle | hge
    · rw [max_eq_right hle, abs_zero]; exact abs_nonneg _
    · rw [max_eq_left hge]
  exact hrelu.trans (Vexec_entry_abs_le W1 X hB hΛ0 hX hW1 hnorm1 hdu i k)

/-! ## The FFN block forward error -/

/-- **FFN block forward error (sup norm).** The executed `matmul → ReLU → matmul` is within
`rdotBudget d (bVval d B Λ · Λ) + Λ · rdotBudget d (B·Λ)` of the ideal block, where
`bVval d B Λ = B·Λ + rdotBudget d (B·Λ)` is the second matmul's input magnitude bound.

Proof: triangle through the intermediate `matMulCoord W2 (reluCoord (Vexec W1 X))`.
* **(A)** the executed-vs-ideal *second* matmul on the common (executed-first-matmul-then-ReLU) input is
  `≤ rdotBudget d (bVval d B Λ · Λ)` by `Vexec_error W2`, the second matmul's input bounded by
  `bVval d B Λ` (`reluCoord_Vexec_entry_abs_le`).
* **(B)** the ideal *second* matmul applied to two ReLU outputs differs by `≤ Λ · ‖reluCoord (Vexec W1 X)
  − reluCoord (matMulCoord W1 X)‖` (`matMulCoord_lipschitz`), `≤ Λ · ‖Vexec W1 X − matMulCoord W1 X‖`
  (`reluCoord_lipschitz`), `≤ Λ · rdotBudget d (B·Λ)` (`Vexec_error W1`).

The ReLU enters with no rounding term — its only contribution is the `1`-Lipschitz factor in (B). -/
theorem ffnExec_forward_error {n d : ℕ} (W1 W2 : Fin d → Fin d → ℝ) (X : Fin n → Fin d → ℝ)
    {B Λ : ℝ} (hB : 0 ≤ B) (hΛ : 0 ≤ Λ) (hX : ∀ i k, |X i k| ≤ B)
    (hW1 : ∀ j, ∑ k, |W1 k j| ≤ Λ) (hW2 : ∀ j, ∑ k, |W2 k j| ≤ Λ)
    (hnorm1 : VexecNormal W1 X)
    (hnorm2 : VexecNormal W2 (reluCoord (Vexec W1 X)))
    (hdu : (d : ℝ) * u < 1) :
    ‖ffnExec W1 W2 X - ffnIdeal W1 W2 X‖
      ≤ rdotBudget d (bVval d B Λ * Λ) + Λ * rdotBudget d (B * Λ) := by
  -- `B' = bVval d B Λ` is the second matmul's input magnitude bound; it is nonnegative.
  have hbV0 : 0 ≤ bVval d B Λ := by
    rw [bVval]
    have h1 : 0 ≤ rdotBudget d (B * Λ) := rdotBudget_nonneg hdu (mul_nonneg hB hΛ)
    have h2 : 0 ≤ B * Λ := mul_nonneg hB hΛ
    linarith
  -- (A): the executed-vs-ideal SECOND matmul on the common relu(Vexec W1 X) input.
  have hA : ‖Vexec W2 (reluCoord (Vexec W1 X)) - matMulCoord W2 (reluCoord (Vexec W1 X))‖
      ≤ rdotBudget d (bVval d B Λ * Λ) :=
    Vexec_error W2 (reluCoord (Vexec W1 X)) hbV0 hΛ
      (reluCoord_Vexec_entry_abs_le W1 X hB hΛ hX hW1 hnorm1 hdu) hW2 hnorm2 hdu
  -- the FIRST matmul forward error.
  have hfirst : ‖Vexec W1 X - matMulCoord W1 X‖ ≤ rdotBudget d (B * Λ) :=
    Vexec_error W1 X hB hΛ hX hW1 hnorm1 hdu
  -- (B): the ideal SECOND matmul applied to the two ReLU outputs.
  have hB2 : ‖matMulCoord W2 (reluCoord (Vexec W1 X)) - matMulCoord W2 (reluCoord (matMulCoord W1 X))‖
      ≤ Λ * rdotBudget d (B * Λ) := by
    calc ‖matMulCoord W2 (reluCoord (Vexec W1 X)) - matMulCoord W2 (reluCoord (matMulCoord W1 X))‖
        ≤ Λ * ‖reluCoord (Vexec W1 X) - reluCoord (matMulCoord W1 X)‖ :=
          matMulCoord_lipschitz W2 hΛ hW2 _ _
      _ ≤ Λ * ‖Vexec W1 X - matMulCoord W1 X‖ := by
          exact mul_le_mul_of_nonneg_left (reluCoord_lipschitz _ _) hΛ
      _ ≤ Λ * rdotBudget d (B * Λ) := mul_le_mul_of_nonneg_left hfirst hΛ
  -- Triangle and add.
  calc ‖ffnExec W1 W2 X - ffnIdeal W1 W2 X‖
      = ‖(Vexec W2 (reluCoord (Vexec W1 X)) - matMulCoord W2 (reluCoord (Vexec W1 X)))
          + (matMulCoord W2 (reluCoord (Vexec W1 X))
              - matMulCoord W2 (reluCoord (matMulCoord W1 X)))‖ := by
        rw [ffnExec, ffnIdeal]; congr 1; abel
    _ ≤ ‖Vexec W2 (reluCoord (Vexec W1 X)) - matMulCoord W2 (reluCoord (Vexec W1 X))‖
        + ‖matMulCoord W2 (reluCoord (Vexec W1 X))
            - matMulCoord W2 (reluCoord (matMulCoord W1 X))‖ := norm_add_le _ _
    _ ≤ rdotBudget d (bVval d B Λ * Λ) + Λ * rdotBudget d (B * Λ) := add_le_add hA hB2

/-! ## The executed FFN block reads as the literal IEEE kernels -/

/-- **The FFN block's ReLU layer is the literal IEEE ReLU.** On a finite fp32 matrix `M` (the
executed first matmul read over ℝ), the executed `reluCoord` applied to `M` equals the bit-level
`maximum · posZero` read over ℝ — coordinatewise, exactly, with no rounding (`reluExec_exact`). So the
FFN block's activation enters as the literal kernel with `rnd = 0`; its two `Vexec` matmuls are the
executed binary32 matmuls (the fp32-rounded dot products `rdot`). -/
theorem ffnExec_relu_eq_lit {n d : ℕ}
    (M : Fin n → Fin d → TorchLean.Floats.IEEE754.IEEE32Exec)
    (hM : ∀ i j, isFinite (M i j) = true) :
    reluCoord (fun i j => toReal (M i j)) = fun i j => toReal (maximum (M i j) posZero) := by
  funext i j
  rw [reluCoord]
  exact (TLT.Fp32Stack.reluExec_exact (M i j) (hM i j)).symm

end TLT.Fp32FFN
