/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Fp32.ExpExecutedValue

/-!
# Executed `Exec32.exp` on the softmax cone — discharging `hδ` to a closed-form theorem

The single-head literal forward error `attnLiteralForwardError` takes the per-input `exp`-accuracy
premise `hδ` as data. On the **softmax cone** — the post-shift logits the stabilization already forces
into `[−T, η]` — the literal `IEEE32Exec.exp`'s branch trichotomy collapses (overflow impossible,
underflow benign, main branch uniformly bounded), so `δ_exp` becomes a definition and `hδ` a theorem.

This file builds the **cone-free** layer first: the range-reduction `let`-bindings `rrK`/`rrF` named as
definitions (so the branch equation is a rewrite, not an existential), and the round-to-even residual
bound that pins `|rrF x| ≤ 2⁴⁷` — the only new mathematics; the rest routes through shipped lemmas.
-/

namespace TLT.ExpError

open TorchLean.Floats TorchLean.Floats.IEEE754 TorchLean.Floats.IEEE754.IEEE32Exec
open TorchLean.Floats.IEEE754.IEEE32Exec.Transcendentals

/-- **Round-to-even residual bound.** For `d > 0`, the ties-to-even rounded quotient leaves a residual
of magnitude at most `d/2`: `2·|n − roundQuotEvenInt n d · d| ≤ d`. This is the range-reduction bound —
applied at `d = 2⁴⁸` it pins `|rrF x| ≤ 2⁴⁷`, the `hf` hypothesis of `exec32_exp_error`. -/
lemma two_mul_abs_roundQuotEvenInt_residual_le (n d : ℤ) (hd : 0 < d) :
    2 * |n - roundQuotEvenInt n d * d| ≤ d := by
  have hdne : d ≠ 0 := ne_of_gt hd
  set q := Int.ediv n d with hqdef
  set r := Int.emod n d with hrdef
  have hr0 : 0 ≤ r := Int.emod_nonneg n hdne
  have hrd : r < d := Int.emod_lt_of_pos n hd
  have hn : d * q + r = n := Int.ediv_add_emod n d
  have key : n - q * d = r := by rw [mul_comm q d, ← hn]; ring
  have key2 : n - (q + 1) * d = r - d := by rw [← hn]; ring
  unfold roundQuotEvenInt
  simp only [hqdef.symm, hrdef.symm]
  split_ifs with h1 h2 h3
  · rw [key, abs_of_nonneg hr0]; omega
  · rw [key2, abs_of_nonpos (by omega), neg_sub]; omega
  · rw [key, abs_of_nonneg hr0]; omega
  · rw [key2, abs_of_nonpos (by omega), neg_sub]; omega

/-- The range reduction's integer part `k`, copied verbatim from `IEEE32Exec.exp`'s `let`-bindings. -/
def rrK (x : IEEE32Exec) : ℤ :=
  match toDyadic? x with
  | none => 0
  | some dx => roundDivPow2EvenInt (fixedMul (fixedOfDyadic dx) fixedInvLn2) fixedScale

/-- The range reduction's fractional part `fFixed ∈ [−½,½]·2⁴⁸`, copied verbatim from `IEEE32Exec.exp`. -/
def rrF (x : IEEE32Exec) : ℤ :=
  match toDyadic? x with
  | none => 0
  | some dx =>
      let yFixed := fixedMul (fixedOfDyadic dx) fixedInvLn2
      yFixed - roundDivPow2EvenInt yFixed fixedScale * pow2Int fixedScale

end TLT.ExpError
