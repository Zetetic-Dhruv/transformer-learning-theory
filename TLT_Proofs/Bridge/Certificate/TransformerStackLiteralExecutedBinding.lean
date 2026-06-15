/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Fp32.FFNForwardError
import TLT_Proofs.Bridge.Forward.LiteralBlockComposition

/-!
# The literal transformer-stack forward error: assembly

The single-head attention block is bound literal→ideal by `attnLiteralForwardError`; the FFN block by
`ffnExec_forward_error`. The composition primitive `block2_forward_error` yields the key bound: a
downstream FFN applied to any upstream literal block has forward error at most
`(FFN rounding) + Λ²·(upstream error)`.

The FFN-ideal is `Λ²`-Lipschitz (two `Λ`-Lipschitz linear maps with the free 1-Lipschitz ReLU between),
so `ffn_after_block_forward_error` carries any upstream block's forward error through with that constant.
Taking the upstream error from `attnLiteralForwardError` gives the `attention → FFN` composite block's
forward error against the ideal block.
-/

namespace TLT.StackLit

open TLT TLT.Fp32Attn TLT.Fp32FFN TLT.LitCompose

/-- **The ideal FFN block is `Λ²`-Lipschitz.** `matMulCoord W2 ∘ reluCoord ∘ matMulCoord W1`: each linear
map is `Λ`-Lipschitz (row-sum bound) and the ReLU is 1-Lipschitz, so the block contracts distances by
at most `Λ²`. -/
theorem ffnIdeal_lipschitz {n d : ℕ} (W1 W2 : Fin d → Fin d → ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hW1 : ∀ j, ∑ k, |W1 k j| ≤ Λ) (hW2 : ∀ j, ∑ k, |W2 k j| ≤ Λ) (a b : Fin n → Fin d → ℝ) :
    dist (ffnIdeal W1 W2 a) (ffnIdeal W1 W2 b) ≤ Λ ^ 2 * dist a b := by
  rw [dist_eq_norm, dist_eq_norm]
  simp only [ffnIdeal]
  calc ‖matMulCoord W2 (reluCoord (matMulCoord W1 a)) - matMulCoord W2 (reluCoord (matMulCoord W1 b))‖
      ≤ Λ * ‖reluCoord (matMulCoord W1 a) - reluCoord (matMulCoord W1 b)‖ :=
        matMulCoord_lipschitz W2 hΛ hW2 _ _
    _ ≤ Λ * ‖matMulCoord W1 a - matMulCoord W1 b‖ := by gcongr; exact reluCoord_lipschitz _ _
    _ ≤ Λ * (Λ * ‖a - b‖) := by gcongr; exact matMulCoord_lipschitz W1 hΛ hW1 _ _
    _ = Λ ^ 2 * ‖a - b‖ := by ring

/-- **FFN-after-a-block literal forward error.** Given any upstream block whose executed output `A_exec`
is within `ρ` of its ideal output `A_ideal`, and the FFN's run-time no-overflow bundle on `A_exec`, the
executed `attention → FFN` composite is within `(FFN rounding) + Λ²·ρ` of the ideal composite: the
FFN's own rounding plus the upstream error amplified by the FFN's `Λ²` Lipschitz constant. -/
theorem ffn_after_block_forward_error {n d : ℕ} (W1 W2 : Fin d → Fin d → ℝ)
    (A_exec A_ideal : Fin n → Fin d → ℝ) {B Λ ρ : ℝ} (hB : 0 ≤ B) (hΛ : 0 ≤ Λ)
    (hX : ∀ i k, |A_exec i k| ≤ B) (hW1 : ∀ j, ∑ k, |W1 k j| ≤ Λ) (hW2 : ∀ j, ∑ k, |W2 k j| ≤ Λ)
    (hnorm1 : VexecNormal W1 A_exec) (hnorm2 : VexecNormal W2 (reluCoord (Vexec W1 A_exec)))
    (hdu : (d : ℝ) * u < 1) (hattn : dist A_exec A_ideal ≤ ρ) :
    dist (ffnExec W1 W2 A_exec) (ffnIdeal W1 W2 A_ideal)
      ≤ rdotBudget d (bVval d B Λ * Λ) + Λ * rdotBudget d (B * Λ) + Λ ^ 2 * ρ := by
  refine block2_forward_error (fun _ : Unit => A_exec) (fun _ : Unit => A_ideal)
    (ffnExec W1 W2) (ffnIdeal W1 W2) () (by positivity) hattn ?_
    (fun a b => ffnIdeal_lipschitz W1 W2 hΛ hW1 hW2 a b)
  rw [dist_eq_norm]
  exact ffnExec_forward_error W1 W2 A_exec hB hΛ hX hW1 hW2 hnorm1 hnorm2 hdu

end TLT.StackLit
