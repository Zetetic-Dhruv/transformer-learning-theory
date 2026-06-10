/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Certificate.AttentionLiteralExecutedBinding
import TLT_Proofs.Bridge.Fp32.FFNForwardError
import TLT_Proofs.Bridge.Fp32.LayerNormForwardError
import TLT_Proofs.Bridge.Forward.LiteralBlockComposition
import TLT_Proofs.Bridge.Certificate.TransformerStackLiteralExecutedBinding
import TLT_Proofs.Bridge.Lipschitz.MultiHeadAttnCertificate

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

open TLT TLT.Fp32AttnLit TLT.Fp32Attn TLT.Fp32FFN TLT.Fp32LN TLT.LitCompose TLT.StackLit
open TorchLean.Floats.IEEE754.IEEE32Exec
open TorchLean.Floats (neuralMagnitude neuralBpow binaryRadix)

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

/-- **Rung 3 — the executed FFN output is bounded by `bVval d (bVval d B Λ) Λ`** (entrywise). The block
`Vexec W2 ∘ reluCoord ∘ Vexec W1`: the first projection lands every entry in `bVval d B Λ`
(`Vexec_entry_abs_le`); the ReLU is non-expansive (`|max x 0| ≤ |x|`); the second projection lands the
result in `bVval d (bVval d B Λ) Λ`. Closed-form nested `bVval` in the actual `(B, Λ)` — the input bound
the downstream layer-norm's `hX` consumes, with the per-matmul no-overflow regime (`VexecNormal`) explicit
(a genuine operating-domain precondition, not an error budget). -/
lemma ffnExec_entry_abs_le {n d : ℕ} (W1 W2 : Fin d → Fin d → ℝ) (E : Fin n → Fin d → ℝ)
    {B Λ : ℝ} (hB : 0 ≤ B) (hΛ : 0 ≤ Λ)
    (hE : ∀ i k, |E i k| ≤ B) (hW1 : ∀ j, ∑ k, |W1 k j| ≤ Λ) (hW2 : ∀ j, ∑ k, |W2 k j| ≤ Λ)
    (hn1 : VexecNormal W1 E) (hn2 : VexecNormal W2 (reluCoord (Vexec W1 E)))
    (hdu : (d : ℝ) * u < 1) (i : Fin n) (j : Fin d) :
    |ffnExec W1 W2 E i j| ≤ bVval d (bVval d B Λ) Λ := by
  have hBΛ : 0 ≤ B * Λ := mul_nonneg hB hΛ
  have hB' : 0 ≤ bVval d B Λ := by rw [bVval]; linarith [rdotBudget_nonneg hdu hBΛ]
  have hrelu : ∀ a k, |reluCoord (Vexec W1 E) a k| ≤ bVval d B Λ := by
    intro a k
    have h1 : |reluCoord (Vexec W1 E) a k| ≤ |Vexec W1 E a k| := by
      simp only [reluCoord]
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _)
    exact h1.trans (Vexec_entry_abs_le W1 E hB hΛ hE hW1 hn1 hdu a k)
  simp only [ffnExec]
  exact Vexec_entry_abs_le W2 (reluCoord (Vexec W1 E)) hB' hΛ hrelu hW2 hn2 hdu i j

/-- **Rung 4 — the layer-norm leg composed onto any upstream block.** Given an upstream block whose
executed output `A_exec` is within `ρ` of its ideal output `A_ideal` (e.g. `ρ =` the `attention → FFN`
block's forward error), the executed starred layer-norm on `A_exec` is within `ln_budget + Λ_ln·ρ` of the
ideal `layerNormCoord` on `A_ideal`: the layer-norm's own forward error `ln_budget` (the closed-form
`lnExec_forward_error` bound) plus the upstream error amplified by the layer-norm Lipschitz constant
`Λ_ln` (`layerNormCoord_lipschitz`). The block's forward error telescopes one sub-layer at a time;
mirrors `ffn_after_block_forward_error`. -/
theorem ln_after_block_forward_error {n d : ℕ} (γ β : Fin d → ℝ) (meanE stdE : Fin n → ℝ)
    (A_exec A_ideal : Fin n → Fin d → ℝ) {ρ ln_budget Λ_ln : ℝ} (hΛ_ln : 0 ≤ Λ_ln)
    (hupstream : dist A_exec A_ideal ≤ ρ)
    (hln : dist (lnStarExec γ β meanE stdE A_exec) (layerNormCoord γ β A_exec) ≤ ln_budget)
    (hlnlip : ∀ a b : Fin n → Fin d → ℝ,
      dist (layerNormCoord γ β a) (layerNormCoord γ β b) ≤ Λ_ln * dist a b) :
    dist (lnStarExec γ β meanE stdE A_exec) (layerNormCoord γ β A_ideal) ≤ ln_budget + Λ_ln * ρ :=
  block2_forward_error (fun _ : Unit => A_exec) (fun _ : Unit => A_ideal)
    (lnStarExec γ β meanE stdE) (layerNormCoord γ β) () hΛ_ln hupstream hln hlnlip

/-- **Rung 5 — the layer-norm mean reduction grounded to `rdotBudget`.** The per-row mean
`rowMeanCoord i X = (∑ₖ X i k)/d` is exactly the matmul `matMulCoord (·↦1/d) X i 0` against the uniform
weight (whose `ℓ¹` row-sum is `1`). So the executed mean `Vexec (·↦1/d) X i 0` is within the shipped
matmul rounding budget `rdotBudget d B` of the ideal mean — the layer-norm's `ρm` budget driven to closed
form by *reusing* the value-projection atom `Vexec_entry_error`, with no new summation-fold analysis. -/
lemma lnMean_error {n d : ℕ} (hd : 0 < d) (X : Fin n → Fin d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hX : ∀ i k, |X i k| ≤ B) (hn : VexecNormal (fun _ _ => (1 / (d : ℝ))) X)
    (hdu : (d : ℝ) * u < 1) (i : Fin n) (j : Fin d) :
    |Vexec (fun _ _ => (1 / (d : ℝ))) X i j - rowMeanCoord i X| ≤ rdotBudget d B := by
  have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hmm : matMulCoord (fun _ _ => (1 / (d : ℝ))) X i j = rowMeanCoord i X := by
    rw [matMulCoord, rowMeanCoord]; simp only [mul_one_div]; rw [← Finset.sum_div]
  have hΛ : ∀ j : Fin d, ∑ k : Fin d, |((fun _ _ => (1 / (d : ℝ))) k j)| ≤ 1 := by
    intro j
    simp only [abs_of_nonneg (le_of_lt (by positivity : (0 : ℝ) < 1 / (d : ℝ)))]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div,
      div_self (ne_of_gt hdpos)]
  have hkey := Vexec_entry_error (fun _ _ => (1 / (d : ℝ))) X hB zero_le_one hX hΛ hn hdu i j
  rw [hmm, mul_one] at hkey
  exact hkey

/-- **The literal `attention → FFN → layerNorm` block forward error.** Threading the three sub-layer
legs through their pointwise telescopes: the executed `attention → FFN` composite is within the FFN
rounding plus `Λ²·ρ_attn` of the ideal (`ffn_after_block_forward_error`, with `ρ_attn` the attention
cone certificate's `rndLit`); the executed layer-norm on that is within `ln_budget + Λ_ln·(·)` of the
ideal block (`ln_after_block_forward_error`). The full block telescopes to
`ln_budget + Λ_ln·(FFN budget + Λ²·ρ_attn)` — every term closed-form in the actual weights once the FFN
budget (`rdotBudget`, shipped) and the layer-norm budget `ln_budget` (its `ρm` grounded by `lnMean_error`,
`ρs`/`ρround` by the layer-norm reductions) are substituted. The block-level `ExecLayer` carrier (uniform
across blocks) then stacks these via `execComp_envelope`; the `gridExt` wrapper lifts to ∀-input. -/
theorem fullBlock_forward_error {n d : ℕ} (W1 W2 : Fin d → Fin d → ℝ) (γ β : Fin d → ℝ)
    (meanE stdE : Fin n → ℝ) (A_exec A_ideal : Fin n → Fin d → ℝ)
    {B Λ ρ_attn ln_budget Λ_ln : ℝ} (hB : 0 ≤ B) (hΛ : 0 ≤ Λ) (hΛ_ln : 0 ≤ Λ_ln)
    (hX : ∀ i k, |A_exec i k| ≤ B) (hW1 : ∀ j, ∑ k, |W1 k j| ≤ Λ) (hW2 : ∀ j, ∑ k, |W2 k j| ≤ Λ)
    (hn1 : VexecNormal W1 A_exec) (hn2 : VexecNormal W2 (reluCoord (Vexec W1 A_exec)))
    (hdu : (d : ℝ) * u < 1) (hattn : dist A_exec A_ideal ≤ ρ_attn)
    (hln : dist (lnStarExec γ β meanE stdE (ffnExec W1 W2 A_exec))
        (layerNormCoord γ β (ffnExec W1 W2 A_exec)) ≤ ln_budget)
    (hlnlip : ∀ a b : Fin n → Fin d → ℝ,
      dist (layerNormCoord γ β a) (layerNormCoord γ β b) ≤ Λ_ln * dist a b) :
    dist (lnStarExec γ β meanE stdE (ffnExec W1 W2 A_exec))
        (layerNormCoord γ β (ffnIdeal W1 W2 A_ideal))
      ≤ ln_budget + Λ_ln *
          (rdotBudget d (bVval d B Λ * Λ) + Λ * rdotBudget d (B * Λ) + Λ ^ 2 * ρ_attn) :=
  ln_after_block_forward_error γ β meanE stdE (ffnExec W1 W2 A_exec) (ffnIdeal W1 W2 A_ideal) hΛ_ln
    (ffn_after_block_forward_error W1 W2 A_exec A_ideal hB hΛ hX hW1 hW2 hn1 hn2 hdu hattn) hln hlnlip

/-- **Square-root difference bound on `[ε, ∞)`.** For `a, b ≥ ε > 0`, `√` is `1/(2√ε)`-Lipschitz:
`|√a − √b| ≤ |a − b| / (2√ε)`. Proved from `√a·√a = a` and `√a + √b ≥ 2√ε`; no packaged Mathlib lemma. -/
private lemma sqrt_sub_le {a b ε : ℝ} (hε : 0 < ε) (ha : ε ≤ a) (hb : ε ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ |a - b| / (2 * Real.sqrt ε) := by
  have hsqa : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt (le_trans hε.le ha)
  have hsqb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt (le_trans hε.le hb)
  have hεpos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hsum : 2 * Real.sqrt ε ≤ Real.sqrt a + Real.sqrt b := by
    have h1 : Real.sqrt ε ≤ Real.sqrt a := Real.sqrt_le_sqrt ha
    have h2 : Real.sqrt ε ≤ Real.sqrt b := Real.sqrt_le_sqrt hb
    linarith
  have hsumpos : 0 < Real.sqrt a + Real.sqrt b := by linarith
  have hfact : a - b = (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by
    have : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b)
        = Real.sqrt a * Real.sqrt a - Real.sqrt b * Real.sqrt b := by ring
    rw [this, hsqa, hsqb]
  have habs : |a - b| = |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) := by
    rw [hfact, abs_mul, abs_of_pos hsumpos]
  rw [habs, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt ε)]
  exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)

/-- **Centered-square perturbation.** Replacing the row mean `rm` by an approximation `me` within `ρm`
perturbs the centered square `(x − ·)²` by at most `ρm·(4B + ρm)`, when `|x|, |rm| ≤ B`. The `(a−b)(a+b)`
factoring of the squared difference; carries the layer-norm mean-error `ρm` through the variance. -/
private lemma centeredSq_diff_le {x me rm B ρm : ℝ} (hB : 0 ≤ B) (hρm : 0 ≤ ρm)
    (hx : |x| ≤ B) (hrm : |rm| ≤ B) (hme : |me - rm| ≤ ρm) :
    |(x - me) ^ 2 - (x - rm) ^ 2| ≤ ρm * (4 * B + ρm) := by
  have hfact : (x - me) ^ 2 - (x - rm) ^ 2 = (rm - me) * (2 * x - me - rm) := by ring
  rw [hfact, abs_mul]
  have h1 : |rm - me| ≤ ρm := by rw [abs_sub_comm]; exact hme
  have hmeB : |me| ≤ B + ρm := by
    calc |me| = |(me - rm) + rm| := by rw [sub_add_cancel]
      _ ≤ |me - rm| + |rm| := abs_add_le _ _
      _ ≤ ρm + B := add_le_add hme hrm
      _ = B + ρm := by ring
  have h2 : |2 * x - me - rm| ≤ 4 * B + ρm := by
    have hx' := abs_le.mp hx; have hme' := abs_le.mp hmeB; have hrm' := abs_le.mp hrm
    rw [abs_le]
    exact ⟨by linarith [hx'.1, hme'.2, hrm'.2], by linarith [hx'.2, hme'.1, hrm'.1]⟩
  exact mul_le_mul h1 h2 (abs_nonneg _) hρm

/-- **Rung 6 — the layer-norm variance budget grounded.** The per-row variance
`rowVarCoord i X = (∑ₖ(X i k − mean)²)/d` is the uniform-`1/d` matmul of the centered squares (same reuse
as `lnMean_error`). The executed variance `Vexec (·↦1/d) cSqExec` — where `cSqExec` is the executed
centered squares (within `εsq` of `(X − meanE)²`, the squaring round) — is within
`rdotBudget d ((2B+ρm)² + εsq) + (εsq + ρm·(4B+ρm))` of the ideal: the matmul rounding (leg A) plus the
centered-square perturbation carried through the uniform matmul (leg B, via `centeredSq_diff_le`). Closed
form in `(B, d, ρm, εsq)`; `εsq` grounds further to `2⁻²⁴·(2B+ρm)²` by the relative round bound. -/
lemma lnVar_error {n d : ℕ} (hd : 0 < d) (X : Fin n → Fin d → ℝ) (meanE : Fin n → ℝ)
    (cSqExec : Fin n → Fin d → ℝ) {B ρm εsq : ℝ} (hB : 0 ≤ B) (hρm : 0 ≤ ρm) (hεsq : 0 ≤ εsq)
    (hX : ∀ i k, |X i k| ≤ B) (hmean : ∀ i, |meanE i - rowMeanCoord i X| ≤ ρm)
    (hmeanB : ∀ i, |rowMeanCoord i X| ≤ B)
    (hsqround : ∀ i k, |cSqExec i k - (X i k - meanE i) ^ 2| ≤ εsq)
    (hn : VexecNormal (fun _ _ => (1 / (d : ℝ))) cSqExec) (hdu : (d : ℝ) * u < 1)
    (i : Fin n) (j : Fin d) :
    |Vexec (fun _ _ => (1 / (d : ℝ))) cSqExec i j - rowVarCoord i X|
      ≤ rdotBudget d ((2 * B + ρm) ^ 2 + εsq) + (εsq + ρm * (4 * B + ρm)) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hΛ : ∀ j' : Fin d, ∑ k : Fin d, |((fun _ _ => (1 / (d : ℝ))) k j')| ≤ 1 := by
    intro j'
    simp only [abs_of_nonneg (le_of_lt (by positivity : (0 : ℝ) < 1 / (d : ℝ)))]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div,
      div_self (ne_of_gt hdpos)]
  have hdiff : ∀ a b, |cSqExec a b - (X a b - rowMeanCoord a X) ^ 2| ≤ εsq + ρm * (4 * B + ρm) := by
    intro a b
    calc |cSqExec a b - (X a b - rowMeanCoord a X) ^ 2|
        ≤ |cSqExec a b - (X a b - meanE a) ^ 2|
          + |(X a b - meanE a) ^ 2 - (X a b - rowMeanCoord a X) ^ 2| := abs_sub_le _ _ _
      _ ≤ εsq + ρm * (4 * B + ρm) :=
          add_le_add (hsqround a b) (centeredSq_diff_le hB hρm (hX a b) (hmeanB a) (hmean a))
  have hcSqB : ∀ a b, |cSqExec a b| ≤ (2 * B + ρm) ^ 2 + εsq := by
    intro a b
    have hmeB : |meanE a| ≤ B + ρm := by
      calc |meanE a| = |(meanE a - rowMeanCoord a X) + rowMeanCoord a X| := by rw [sub_add_cancel]
        _ ≤ |meanE a - rowMeanCoord a X| + |rowMeanCoord a X| := abs_add_le _ _
        _ ≤ ρm + B := add_le_add (hmean a) (hmeanB a)
        _ = B + ρm := by ring
    have hxm : |X a b - meanE a| ≤ 2 * B + ρm := by
      calc |X a b - meanE a| = |X a b + -meanE a| := by ring_nf
        _ ≤ |X a b| + |(-meanE a)| := abs_add_le _ _
        _ = |X a b| + |meanE a| := by rw [abs_neg]
        _ ≤ B + (B + ρm) := add_le_add (hX a b) hmeB
        _ = 2 * B + ρm := by ring
    have hsqle : (X a b - meanE a) ^ 2 ≤ (2 * B + ρm) ^ 2 := by
      nlinarith [hxm, abs_nonneg (X a b - meanE a), sq_abs (X a b - meanE a)]
    calc |cSqExec a b|
        = |(X a b - meanE a) ^ 2 + (cSqExec a b - (X a b - meanE a) ^ 2)| := by ring_nf
      _ ≤ |(X a b - meanE a) ^ 2| + |cSqExec a b - (X a b - meanE a) ^ 2| := abs_add_le _ _
      _ ≤ (2 * B + ρm) ^ 2 + εsq := by
          gcongr
          · rw [abs_of_nonneg (sq_nonneg _)]; exact hsqle
          · exact hsqround a b
  have hlegA := Vexec_entry_error (fun _ _ => (1 / (d : ℝ))) cSqExec (by positivity) zero_le_one
    hcSqB hΛ hn hdu i j
  rw [mul_one] at hlegA
  have hlin : matMulCoord (fun _ _ => (1 / (d : ℝ))) cSqExec i j
      - matMulCoord (fun _ _ => (1 / (d : ℝ))) (fun a b => (X a b - rowMeanCoord a X) ^ 2) i j
      = matMulCoord (fun _ _ => (1 / (d : ℝ)))
          (fun a b => cSqExec a b - (X a b - rowMeanCoord a X) ^ 2) i j := by
    simp only [matMulCoord]; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro k _; ring
  have hlegB : |matMulCoord (fun _ _ => (1 / (d : ℝ))) cSqExec i j
      - matMulCoord (fun _ _ => (1 / (d : ℝ))) (fun a b => (X a b - rowMeanCoord a X) ^ 2) i j|
      ≤ εsq + ρm * (4 * B + ρm) := by
    rw [hlin]
    have := matMulCoord_entry_abs_le (fun _ _ => (1 / (d : ℝ)))
      (fun a b => cSqExec a b - (X a b - rowMeanCoord a X) ^ 2) (by positivity) hdiff hΛ i j
    rwa [mul_one] at this
  have hmm : matMulCoord (fun _ _ => (1 / (d : ℝ))) (fun a b => (X a b - rowMeanCoord a X) ^ 2) i j
      = rowVarCoord i X := by
    rw [matMulCoord, rowVarCoord]; simp only [mul_one_div]; rw [← Finset.sum_div]
  calc |Vexec (fun _ _ => (1 / (d : ℝ))) cSqExec i j - rowVarCoord i X|
      = |Vexec (fun _ _ => (1 / (d : ℝ))) cSqExec i j
          - matMulCoord (fun _ _ => (1 / (d : ℝ))) (fun a b => (X a b - rowMeanCoord a X) ^ 2) i j| := by
        rw [hmm]
    _ ≤ |Vexec (fun _ _ => (1 / (d : ℝ))) cSqExec i j
          - matMulCoord (fun _ _ => (1 / (d : ℝ))) cSqExec i j|
        + |matMulCoord (fun _ _ => (1 / (d : ℝ))) cSqExec i j
          - matMulCoord (fun _ _ => (1 / (d : ℝ))) (fun a b => (X a b - rowMeanCoord a X) ^ 2) i j| :=
        abs_sub_le _ _ _
    _ ≤ rdotBudget d ((2 * B + ρm) ^ 2 + εsq) + (εsq + ρm * (4 * B + ρm)) := add_le_add hlegA hlegB

/-- **Rung 7 — the layer-norm std budget grounded.** The standard deviation `rowStdCoord =
√(max(var,0)+ε)`; replacing the ideal variance by the executed one moves it by at most
`ρs_var / (2√ε)`, where `ρs_var` is the variance budget (`lnVar_error`) — the `√` is `1/(2√ε)`-Lipschitz
on `[ε,∞)` (`sqrt_sub_le`), the `ε = 1e-6` floor making the denominator nonzero, and `max(·,0)` is
1-Lipschitz. Closed form; this is the layer-norm `ρs` budget driven to the floor. -/
lemma lnStd_error {n d : ℕ} (hd : 0 < d) (X : Fin n → Fin d → ℝ) (meanE : Fin n → ℝ)
    (cSqExec : Fin n → Fin d → ℝ) {B ρm εsq : ℝ} (hB : 0 ≤ B) (hρm : 0 ≤ ρm) (hεsq : 0 ≤ εsq)
    (hX : ∀ i k, |X i k| ≤ B) (hmean : ∀ i, |meanE i - rowMeanCoord i X| ≤ ρm)
    (hmeanB : ∀ i, |rowMeanCoord i X| ≤ B)
    (hsqround : ∀ i k, |cSqExec i k - (X i k - meanE i) ^ 2| ≤ εsq)
    (hn : VexecNormal (fun _ _ => (1 / (d : ℝ))) cSqExec) (hdu : (d : ℝ) * u < 1)
    (i : Fin n) (j : Fin d) :
    |Real.sqrt (max (Vexec (fun _ _ => (1 / (d : ℝ))) cSqExec i j) 0 + Numbers.epsilon)
        - rowStdCoord i X|
      ≤ (rdotBudget d ((2 * B + ρm) ^ 2 + εsq) + (εsq + ρm * (4 * B + ρm)))
          / (2 * Real.sqrt Numbers.epsilon) := by
  have heps : (0 : ℝ) < Numbers.epsilon := numbers_epsilon_real_pos
  have hrowStd : rowStdCoord i X
      = Real.sqrt (max (rowVarCoord i X) 0 + Numbers.epsilon) := rfl
  rw [hrowStd]
  have ha : Numbers.epsilon
      ≤ max (Vexec (fun _ _ => (1 / (d : ℝ))) cSqExec i j) 0 + Numbers.epsilon := by
    have : (0 : ℝ) ≤ max (Vexec (fun _ _ => (1 / (d : ℝ))) cSqExec i j) 0 := le_max_right _ _
    linarith
  have hb : Numbers.epsilon ≤ max (rowVarCoord i X) 0 + Numbers.epsilon := by
    have : (0 : ℝ) ≤ max (rowVarCoord i X) 0 := le_max_right _ _
    linarith
  refine (sqrt_sub_le heps ha hb).trans ?_
  gcongr
  have hsimp : max (Vexec (fun _ _ => (1 / (d : ℝ))) cSqExec i j) 0 + Numbers.epsilon
      - (max (rowVarCoord i X) 0 + Numbers.epsilon)
      = max (Vexec (fun _ _ => (1 / (d : ℝ))) cSqExec i j) 0 - max (rowVarCoord i X) 0 := by ring
  rw [hsimp]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  exact lnVar_error hd X meanE cSqExec hB hρm hεsq hX hmean hmeanB hsqround hn hdu i j

/-- **The single fp32 round, relatively bounded on the normal range.** For `|z| ≤ M` with `z` in the
binary32 normal range, `|fp32Round z − z| ≤ 2⁻²⁴·M` — the relative round bound `fp32Round_rel_on_normal`
lifted to the closed magnitude bound `M` (no `eps₃₂`-monotonicity needed). The atom that grounds every
per-op round budget (`εsq` for the squaring, `ρround` for the affine) to a closed form in the actual
magnitudes. -/
private lemma fp32Round_abs_le_of_normal {z M : ℝ} (hz : |z| ≤ M)
    (hnormal : z ≠ 0 → (-125 : ℤ) ≤ neuralMagnitude binaryRadix z) :
    |fp32Round z - z| ≤ neuralBpow binaryRadix (-24) * M := by
  have hM : 0 ≤ M := le_trans (abs_nonneg z) hz
  have hnb : 0 ≤ neuralBpow binaryRadix (-24) := neuralBpow.nonneg binaryRadix (-24)
  by_cases h0 : z = 0
  · rw [h0, fp32Round_zero]; simp only [sub_self, abs_zero]; exact mul_nonneg hnb hM
  · calc |fp32Round z - z|
        ≤ neuralBpow binaryRadix (-24) * |z| := fp32Round_rel_on_normal z h0 (hnormal h0)
      _ ≤ neuralBpow binaryRadix (-24) * M := by gcongr

/-- The centered square is bounded by `(2B+ρm)²` when `|x|, |rm| ≤ B` and `|me − rm| ≤ ρm`
(`|x − me| ≤ 2B+ρm`, squared). -/
private lemma centeredSq_abs_le {x me rm B ρm : ℝ} (hB : 0 ≤ B) (hρm : 0 ≤ ρm)
    (hx : |x| ≤ B) (hrm : |rm| ≤ B) (hme : |me - rm| ≤ ρm) :
    (x - me) ^ 2 ≤ (2 * B + ρm) ^ 2 := by
  have hmeB : |me| ≤ B + ρm := by
    calc |me| = |(me - rm) + rm| := by rw [sub_add_cancel]
      _ ≤ |me - rm| + |rm| := abs_add_le _ _
      _ ≤ ρm + B := add_le_add hme hrm
      _ = B + ρm := by ring
  have hxm : |x - me| ≤ 2 * B + ρm := by
    calc |x - me| = |x + -me| := by ring_nf
      _ ≤ |x| + |(-me)| := abs_add_le _ _
      _ = |x| + |me| := by rw [abs_neg]
      _ ≤ B + (B + ρm) := add_le_add hx hmeB
      _ = 2 * B + ρm := by ring
  nlinarith [hxm, abs_nonneg (x - me), sq_abs (x - me)]

/-- **`εsq` grounded — the squaring round in closed form.** The executed centered square
`fp32Round((X − meanE)²)` is within `2⁻²⁴·(2B+ρm)²` of the exact `(X − meanE)²`, under the squaring's
normal-range regime `hnormal`. This discharges `lnVar_error`/`lnStd_error`'s `hsqround` with the closed
budget `εsq := 2⁻²⁴·(2B+ρm)²` — no free per-op budget left in the variance. -/
lemma centeredSqRound_le {n d : ℕ} (X : Fin n → Fin d → ℝ) (meanE : Fin n → ℝ) {B ρm : ℝ}
    (hB : 0 ≤ B) (hρm : 0 ≤ ρm) (hX : ∀ i k, |X i k| ≤ B)
    (hmean : ∀ i, |meanE i - rowMeanCoord i X| ≤ ρm) (hmeanB : ∀ i, |rowMeanCoord i X| ≤ B)
    (hnormal : ∀ i k, (X i k - meanE i) ^ 2 ≠ 0 →
      (-125 : ℤ) ≤ neuralMagnitude binaryRadix ((X i k - meanE i) ^ 2)) (i : Fin n) (k : Fin d) :
    |fp32Round ((X i k - meanE i) ^ 2) - (X i k - meanE i) ^ 2|
      ≤ neuralBpow binaryRadix (-24) * (2 * B + ρm) ^ 2 := by
  refine fp32Round_abs_le_of_normal ?_ (hnormal i k)
  rw [abs_of_nonneg (sq_nonneg _)]
  exact centeredSq_abs_le hB hρm (hX i k) (hmeanB i) (hmean i)

/-- **`ρround` grounded — the affine round in closed form.** The executed layer-norm `lnStarExec` is the
single `fp32Round` of the affine `(X − meanE)/stdE·γ + β`; given the affine magnitude bound `Maff` and the
affine's normal-range regime, that round is within `2⁻²⁴·Maff` of the exact affine. This discharges
`lnExec_forward_error`'s `hround` with the closed budget `ρround := 2⁻²⁴·Maff` (`Maff` itself closed-form
`((2B+ρm)/√ε)·Cγ + Cβ` from the input/`γ`/`β`/std bounds) — the same round atom as `εsq`. -/
lemma affineRound_le {n d : ℕ} (γ β : Fin d → ℝ) (meanE stdE : Fin n → ℝ) (X : Fin n → Fin d → ℝ)
    {Maff : ℝ} (hMaff : ∀ i j, |(X i j - meanE i) / stdE i * γ j + β j| ≤ Maff)
    (hnormal : ∀ i j, ((X i j - meanE i) / stdE i * γ j + β j) ≠ 0 →
      (-125 : ℤ) ≤ neuralMagnitude binaryRadix ((X i j - meanE i) / stdE i * γ j + β j))
    (i : Fin n) (j : Fin d) :
    |lnStarExec γ β meanE stdE X i j - ((X i j - meanE i) / stdE i * γ j + β j)|
      ≤ neuralBpow binaryRadix (-24) * Maff := by
  simp only [lnStarExec]
  exact fp32Round_abs_le_of_normal (hMaff i j) (hnormal i j)

/-- The coordinate matmul against the identity matrix is the identity. -/
lemma matMulCoord_id {n d : ℕ} (Y : Fin n → Fin d → ℝ) :
    matMulCoord (fun k j => if k = j then (1 : ℝ) else 0) Y = Y := by
  funext i j
  simp only [matMulCoord]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj; simp [hkj]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **The H=1 reconciliation.** The shipped multi-head attention `multiHeadAttn` at head-count `1` with
identity query/key projections and value projection `W` is exactly the single-head `attnHead scale W`
that the literal cone certificate binds to. This is what lets the single-head literal forward errors
instantiate the shipped multi-head capstone `transformerEncoderStackMH_executed_at_depth` at `H=1`. -/
lemma attnHead_eq_multiHead_one {n d : ℕ} (scale : ℝ) (W : Fin d → Fin d → ℝ) (Y : Fin n → Fin d → ℝ) :
    multiHeadAttn (n := n) (H := 1) scale (fun _ k j => if k = j then (1 : ℝ) else 0)
        (fun _ k j => if k = j then (1 : ℝ) else 0) (fun _ => W) Y
      = attnHead scale W Y := by
  simp only [multiHeadAttn, Fin.sum_univ_one]
  unfold attnHeadQK attnHead
  simp only [matMulCoord_id]

end TLT.FullBlockLit
