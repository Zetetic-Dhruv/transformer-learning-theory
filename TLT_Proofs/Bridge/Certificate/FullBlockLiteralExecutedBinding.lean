/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Certificate.AttentionLiteralExecutedBinding
import TLT_Proofs.Bridge.Fp32.FFNForwardError
import TLT_Proofs.Bridge.Fp32.LayerNormForwardError
import TLT_Proofs.Bridge.Forward.LiteralBlockComposition

/-!
# The full literal transformer-block certificate — assembly toward closed-form, grounded bounds

The three per-sub-layer literal forward errors (attention `attnLiteralForwardError_onCone`, FFN
`ffnExec_forward_error`, LN `lnExec_forward_error`) compose via `block3_forward_error` into one
`attention → FFN → layerNorm` block forward error. This file drives the composition's hypotheses to
*closed form* in the actual weights `(W, B, Λ)` and the shipped rounding atoms — no abstracted budget left
as a free premise.

Rung 1 (here): the ideal attention-head output magnitude `‖attnHead scale W Y i‖ ≤ B·Λ`, the ℝ-side bound
that — through the cone certificate's `rndLit` slack — bounds the *executed* attention output feeding the
downstream FFN's input hypothesis. Closed-form in `(B, Λ)`, grounded in the softmax-convexity bound
`attnVec_norm_le` and the value-projection bound `matMulCoord_entry_abs_le`.
-/

namespace TLT.FullBlockLit

open TLT TLT.Fp32AttnLit TLT.Fp32Attn

/-- **The ideal attention head output is bounded by `B·Λ`.** The head `attnHead scale W Y i` is a
softmax-convex combination (`attnVec_norm_le`: nonnegative weights summing to one) of the value rows
`matMulCoord W Y`, each entry of which is `≤ B·Λ` (`matMulCoord_entry_abs_le`, from `‖Y row‖₁ ≤ B` and
`∑|W·j| ≤ Λ`). Hence the head's output row has sup-norm `≤ B·Λ` — the closed-form ℝ-side magnitude that,
plus the cone certificate's `rndLit`, bounds the executed attention output entering the FFN. -/
lemma attnHead_norm_le {n d : ℕ} [NeZero n] (scale : ℝ) (W : Fin d → Fin d → ℝ)
    (Y : Fin n → Fin d → ℝ) {B Λ : ℝ} (hB : 0 ≤ B) (hΛ : 0 ≤ Λ)
    (hX : ∀ i k, |Y i k| ≤ B) (hW : ∀ j, ∑ k, |W k j| ≤ Λ) (i : Fin n) :
    ‖attnHead scale W Y i‖ ≤ B * Λ := by
  simp only [attnHead]
  refine attnVec_norm_le _ _ (fun k => ?_)
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hB hΛ)).mpr (fun j => ?_)
  rw [Real.norm_eq_abs]
  exact matMulCoord_entry_abs_le W Y hB hX hW k j

/-- **Rung 2 — the executed attention output is bounded by `B·Λ + rnd`** (entrywise). Any executed map
`E` within `rnd` of the ideal head (e.g. `execAttnLit`, with `rnd = rndLit` from
`attnLiteralForwardError_onCone`) inherits the ideal bound `B·Λ` (rung 1) plus the forward-error slack.
This is the closed-form input bound the downstream FFN's `hX` hypothesis consumes — no abstracted
attention-output budget. -/
lemma execAttn_entry_abs_le_of_dist {n d : ℕ} [NeZero n] (scale : ℝ) (W : Fin d → Fin d → ℝ)
    (Y : Fin n → Fin d → ℝ) (E : Fin n → Fin d → ℝ) {B Λ rnd : ℝ} (hB : 0 ≤ B) (hΛ : 0 ≤ Λ)
    (hX : ∀ i k, |Y i k| ≤ B) (hW : ∀ j, ∑ k, |W k j| ≤ Λ)
    (hfwd : dist E (attnHead scale W Y) ≤ rnd) (i : Fin n) (j : Fin d) :
    |E i j| ≤ B * Λ + rnd := by
  have hhead : |attnHead scale W Y i j| ≤ B * Λ := by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (attnHead scale W Y i) j).trans (attnHead_norm_le scale W Y hB hΛ hX hW i)
  have hclose : |E i j - attnHead scale W Y i j| ≤ rnd := by
    rw [← Real.dist_eq]
    exact le_trans (dist_le_pi_dist (E i) (attnHead scale W Y i) j)
      (le_trans (dist_le_pi_dist E (attnHead scale W Y) i) hfwd)
  calc |E i j| = |(E i j - attnHead scale W Y i j) + attnHead scale W Y i j| := by ring_nf
    _ ≤ |E i j - attnHead scale W Y i j| + |attnHead scale W Y i j| := abs_add_le _ _
    _ ≤ rnd + B * Λ := add_le_add hclose hhead
    _ = B * Λ + rnd := by ring

end TLT.FullBlockLit
