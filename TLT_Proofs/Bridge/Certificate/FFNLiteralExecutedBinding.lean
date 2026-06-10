/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Certificate.AttentionLiteralExecutedBinding
import TLT_Proofs.Bridge.Forward.LiteralBlockComposition
import TLT_Proofs.Bridge.Fp32.FFNBiasForwardError

/-!
# The literal executed binding of the fp32 feed-forward forward-error

`Bridge/Fp32/FFNBiasForwardError` proves the pure-ℝ forward error of the rectangular hidden-dim FFN
with biases (`ffnExecBias` vs `ffnCoord`). This file upgrades it to the **literal** TorchLean kernel:
the executed forward is `Spec.FeedForward.forward` at backend `IEEE32Exec`, read back over `ℝ` through
`toReal` — the exact tensor op the hardware runs.

`Spec.FeedForward.forward` is `addSpec (matMulSpec (reluSpec (addSpec (matMulSpec x W1) b̂1)) W2) b̂2`
(with `b̂ = broadcastTo` the bias). At `IEEE32Exec`, each `matMulSpec` fold reproduces the model's
rounded dot product `rdot` exactly (`toReal_get2_matMulSpec_ie`); each `reluSpec` entry is the exact
`maximum · posZero` (`reluExec_exact`, no rounding); each bias `addSpec` rounds within
`eps₃₂` (`toReal_add_abs_error_of_isFinite`). The forward error is the three-stage telescope
`block3_forward_error` (first affine → ReLU → second affine), whose only genuinely-new budget over the
ℝ-model `ffnExecBias_forward_error` is the two bias-add roundings (`b1` amplified by the second
matmul's `Λ`, `b2` direct).
-/

open TorchLean.Floats (eps₃₂)
open TorchLean.Floats.IEEE754
open TorchLean.Floats.IEEE754.IEEE32Exec
open Spec Tensor

noncomputable section

namespace TLT.Fp32FFNLit

open TLT TLT.Fp32Attn TLT.Fp32FFN TLT.Fp32FFNBias TLT.Fp32AttnLit TLT.LitCompose TLT.Fp32Stack

/-! ## IEEE-level coordinate reads of the feed-forward spec ops

The `_ie` reductions for `addSpec` / `reluSpec` / the bias broadcast, mirroring the matmul/softmax
reads in `Fp32AttnLit` and the ℝ-level `get2_addSpec`/`get2_reluSpec`/`get2_broadcast_col`. Each is the
definitional coordinate projection at backend `IEEE32Exec`. -/

/-- Matrix coordinate read of `addSpec` at `IEEE32Exec`: `(addSpec A B)[i,j] = A[i,j] + B[i,j]`
(the literal IEEE `add`, in instance notation). -/
lemma get2_addSpec_ie {m n : ℕ} (A B : Tensor IEEE32Exec (.dim m (.dim n .scalar)))
    (i : Fin m) (j : Fin n) :
    get2 (Tensor.addSpec A B) i j = get2 A i j + get2 B i j := by
  cases A with
  | dim rowsA =>
    cases B with
    | dim rowsB =>
      cases hA : rowsA i with
      | dim colsA =>
        cases hB : rowsB i with
        | dim colsB =>
          cases hcA : colsA j with
          | scalar a =>
            cases hcB : colsB j with
            | scalar b =>
              simp [Tensor.addSpec, Tensor.map2Spec, get2, get_eq, hA, hB, hcA, hcB]

/-- Matrix coordinate read of `reluSpec` at `IEEE32Exec`: `(reluSpec T)[i,j] = max T[i,j] 0`
(the literal IEEE `maximum · posZero`, in instance notation). -/
lemma get2_reluSpec_ie {m n : ℕ} (T : Tensor IEEE32Exec (.dim m (.dim n .scalar)))
    (i : Fin m) (j : Fin n) :
    get2 (Activation.reluSpec T) i j = maximum (get2 T i j) posZero := by
  cases T with
  | dim rows =>
    cases hrow : rows i with
    | dim cols =>
      cases hcol : cols j with
      | scalar x =>
        simp only [Activation.reluSpec, Activation.Math.reluSpec, Tensor.mapSpec, get2, get_eq,
          hrow, hcol]
        rfl

/-- Matrix coordinate read of a column-broadcast bias at `IEEE32Exec`: row `i` of the broadcast
`(seqLen × em)` tensor of a length-`em` bias vector `b` is `b` itself, so entry `[i,j] = b[j]`. -/
lemma get2_broadcast_bias_ie {sq em : ℕ} (v : Tensor IEEE32Exec (.dim em .scalar))
    (i : Fin sq) (j : Fin em) :
    get2 (broadcastTo (Shape.CanBroadcastTo.expand_dims (Shape.CanBroadcastTo.dim_eq
      (Shape.CanBroadcastTo.scalar_to_any .scalar))
        : Shape.CanBroadcastTo (.dim em .scalar) (.dim sq (.dim em .scalar))) v) i j
      = vecGet v j := by
  cases v with
  | dim cols =>
    cases hc : cols j with
    | scalar w => simp [get2, get_eq, broadcastTo, replicate, vecGet, hc, Tensor.toScalar]

/-! ## The literal affine read

Read an `IEEE32Exec` matrix / bias vector over `ℝ` coordinatewise. The literal affine
`addSpec (matMulSpec Xt Wt) (broadcast bt)` read over `ℝ` is within one `eps₃₂` bias rounding of the
ℝ-model affine `affExec` — the matmul part is reproduced EXACTLY by the keystone
`toReal_get2_matMulSpec_ie`, and only the bias add rounds. -/

/-- Coordinatewise `ℝ`-read of an `IEEE32Exec` matrix. -/
def tReal2 {m n : ℕ} (T : Tensor IEEE32Exec (.dim m (.dim n .scalar))) : Fin m → Fin n → ℝ :=
  fun i j => toReal (get2 T i j)

/-- Coordinatewise `ℝ`-read of an `IEEE32Exec` vector. -/
def tReal1 {m : ℕ} (v : Tensor IEEE32Exec (.dim m .scalar)) : Fin m → ℝ :=
  fun j => toReal (Tensor.vecGet v j)

/-- **Per-entry literal affine read.** The executed `addSpec (matMulSpec Xt Wt) (broadcast bt)`
coordinate `[i,j]`, read over `ℝ`, is within one `eps₃₂` bias-rounding of the ℝ-model affine
`affExec (tReal2 Wt) (tReal1 bt) (tReal2 Xt) [i,j]`. The matmul is reproduced exactly by the keystone
`toReal_get2_matMulSpec_ie`; only the broadcast bias add rounds (`toReal_add_abs_error_of_isFinite`). -/
lemma toReal_litAff_entry {s n p : ℕ} (Xt : Tensor IEEE32Exec (.dim s (.dim n .scalar)))
    (Wt : Tensor IEEE32Exec (.dim n (.dim p .scalar))) (bt : Tensor IEEE32Exec (.dim p .scalar))
    (i : Fin s) (j : Fin p) (hfin : MatMulCoordFinite Xt Wt i j)
    (hadd : isFinite (add (get2 (matMulSpec Xt Wt) i j) (Tensor.vecGet bt j)) = true) :
    |toReal (get2 (Tensor.addSpec (matMulSpec Xt Wt) (broadcastTo
        (Shape.CanBroadcastTo.expand_dims (Shape.CanBroadcastTo.dim_eq
          (Shape.CanBroadcastTo.scalar_to_any .scalar))
            : Shape.CanBroadcastTo (.dim p .scalar) (.dim s (.dim p .scalar))) bt)) i j)
        - affExec (tReal2 Wt) (tReal1 bt) (tReal2 Xt) i j|
      ≤ eps₃₂ (toReal (get2 (matMulSpec Xt Wt) i j) + toReal (Tensor.vecGet bt j)) := by
  rw [get2_addSpec_ie, get2_broadcast_bias_ie]
  have hmm : toReal (get2 (matMulSpec Xt Wt) i j) = VexecRect (tReal2 Wt) (tReal2 Xt) i j := by
    rw [toReal_get2_matMulSpec_ie Xt Wt i j hfin]; rfl
  have haff : affExec (tReal2 Wt) (tReal1 bt) (tReal2 Xt) i j
      = VexecRect (tReal2 Wt) (tReal2 Xt) i j + tReal1 bt j := rfl
  rw [haff, ← hmm]
  exact toReal_add_abs_error_of_isFinite _ _ hadd

/-- The literal affine read as a matrix-valued function: `toReal ∘ get2` of
`addSpec (matMulSpec Xt Wt) (broadcast bt)`. -/
def litAff {s n p : ℕ} (Xt : Tensor IEEE32Exec (.dim s (.dim n .scalar)))
    (Wt : Tensor IEEE32Exec (.dim n (.dim p .scalar))) (bt : Tensor IEEE32Exec (.dim p .scalar)) :
    Fin s → Fin p → ℝ :=
  fun i j => toReal (get2 (Tensor.addSpec (matMulSpec Xt Wt) (broadcastTo
    (Shape.CanBroadcastTo.expand_dims (Shape.CanBroadcastTo.dim_eq
      (Shape.CanBroadcastTo.scalar_to_any .scalar))
        : Shape.CanBroadcastTo (.dim p .scalar) (.dim s (.dim p .scalar))) bt)) i j)

/-- **Sup-norm literal affine forward error.** The literal affine read is within `ρ` of the ℝ-model
`affExec (tReal2 Wt) (tReal1 bt) (tReal2 Xt)`, where `ρ` bounds every per-entry bias rounding. -/
lemma litAff_forward_error {s n p : ℕ} (Xt : Tensor IEEE32Exec (.dim s (.dim n .scalar)))
    (Wt : Tensor IEEE32Exec (.dim n (.dim p .scalar))) (bt : Tensor IEEE32Exec (.dim p .scalar))
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hfin : ∀ i j, MatMulCoordFinite Xt Wt i j)
    (hadd : ∀ i j, isFinite (add (get2 (matMulSpec Xt Wt) i j) (Tensor.vecGet bt j)) = true)
    (hρ : ∀ i j, eps₃₂ (toReal (get2 (matMulSpec Xt Wt) i j) + toReal (Tensor.vecGet bt j)) ≤ ρ) :
    ‖litAff Xt Wt bt - affExec (tReal2 Wt) (tReal1 bt) (tReal2 Xt)‖ ≤ ρ := by
  refine (pi_norm_le_iff_of_nonneg hρ0).mpr (fun i => ?_)
  refine (pi_norm_le_iff_of_nonneg hρ0).mpr (fun j => ?_)
  rw [Real.norm_eq_abs, Pi.sub_apply, Pi.sub_apply]
  exact (toReal_litAff_entry Xt Wt bt i j (hfin i j) (hadd i j)).trans (hρ i j)

/-- The literal `reluSpec` read over `ℝ` is the exact coordinate ReLU (`reluExec_exact`, no rounding),
given the pre-activation entry is finite. -/
lemma toReal_get2_reluSpec {m n : ℕ} (T : Tensor IEEE32Exec (.dim m (.dim n .scalar)))
    (i : Fin m) (k : Fin n) (hfin : isFinite (get2 T i k) = true) :
    toReal (get2 (Activation.reluSpec T) i k) = max (toReal (get2 T i k)) 0 := by
  rw [get2_reluSpec_ie]
  exact reluExec_exact (get2 T i k) hfin

/-- The literal hidden activation, read over `ℝ`, is `reluCoord` of the `ℝ`-read pre-activation. -/
lemma tReal2_reluSpec {m n : ℕ} (T : Tensor IEEE32Exec (.dim m (.dim n .scalar)))
    (hfin : ∀ i k, isFinite (get2 T i k) = true) :
    tReal2 (Activation.reluSpec T) = reluCoord (tReal2 T) := by
  funext i k
  rw [tReal2, toReal_get2_reluSpec T i k (hfin i k), reluCoord, tReal2]

/-- **Literal affine read vs the EXACT `ℝ` ideal.** Triangle through `affExec`: the matmul rounding
(`affExec_forward_error`, `≤ rdotBudget n (B·Λ)`) plus the bias rounding (`litAff_forward_error`,
`≤ ρ`). This is the per-leg budget consumed by both FFN affines. -/
lemma litAff_vs_affIdeal {s n p : ℕ} (Xt : Tensor IEEE32Exec (.dim s (.dim n .scalar)))
    (Wt : Tensor IEEE32Exec (.dim n (.dim p .scalar))) (bt : Tensor IEEE32Exec (.dim p .scalar))
    {B Λ ρ : ℝ} (hB : 0 ≤ B) (hΛ0 : 0 ≤ Λ) (hρ0 : 0 ≤ ρ)
    (hX : ∀ i k, |tReal2 Xt i k| ≤ B) (hW : ∀ j, ∑ k, |tReal2 Wt k j| ≤ Λ)
    (hnorm : VexecRectNormal (tReal2 Wt) (tReal2 Xt)) (hnu : (n : ℝ) * u < 1)
    (hfin : ∀ i j, MatMulCoordFinite Xt Wt i j)
    (hadd : ∀ i j, isFinite (add (get2 (matMulSpec Xt Wt) i j) (Tensor.vecGet bt j)) = true)
    (hρ : ∀ i j, eps₃₂ (toReal (get2 (matMulSpec Xt Wt) i j) + toReal (Tensor.vecGet bt j)) ≤ ρ) :
    ‖litAff Xt Wt bt - affIdeal (tReal2 Wt) (tReal1 bt) (tReal2 Xt)‖ ≤ ρ + rdotBudget n (B * Λ) := by
  calc ‖litAff Xt Wt bt - affIdeal (tReal2 Wt) (tReal1 bt) (tReal2 Xt)‖
      = ‖(litAff Xt Wt bt - affExec (tReal2 Wt) (tReal1 bt) (tReal2 Xt))
          + (affExec (tReal2 Wt) (tReal1 bt) (tReal2 Xt)
              - affIdeal (tReal2 Wt) (tReal1 bt) (tReal2 Xt))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖litAff Xt Wt bt - affExec (tReal2 Wt) (tReal1 bt) (tReal2 Xt)‖
        + ‖affExec (tReal2 Wt) (tReal1 bt) (tReal2 Xt)
            - affIdeal (tReal2 Wt) (tReal1 bt) (tReal2 Xt)‖ := norm_add_le _ _
    _ ≤ ρ + rdotBudget n (B * Λ) :=
        add_le_add (litAff_forward_error Xt Wt bt hρ0 hfin hadd hρ)
          (affExec_forward_error (tReal2 Wt) (tReal1 bt) (tReal2 Xt) hB hΛ0 hX hW hnorm hnu)

/-- `ffnCoord` factors as `affIdeal ∘ reluCoord ∘ affIdeal` (the two biases folded in). -/
lemma ffnCoord_eq_affIdeal {s d h : ℕ} (W1 : Fin d → Fin h → ℝ) (b1 : Fin h → ℝ)
    (W2 : Fin h → Fin d → ℝ) (b2 : Fin d → ℝ) (X : Fin s → Fin d → ℝ) :
    ffnCoord W1 b1 W2 b2 X = affIdeal W2 b2 (reluCoord (affIdeal W1 b1 X)) := by
  funext i j
  show (∑ l, max (matMulCoord W1 X i l + b1 l) 0 * W2 l j) + b2 j
      = (∑ l, reluCoord (affIdeal W1 b1 X) i l * W2 l j) + b2 j
  congr 1

/-! ## The literal feed-forward execution -/

/-- The literal hidden activation tensor (the executed first affine, then ReLU), at `IEEE32Exec`. -/
def ffnHiddenT {d h s : ℕ} (ffn : Spec.FeedForward d h IEEE32Exec)
    (Xt : Tensor IEEE32Exec (.dim s (.dim d .scalar))) : Tensor IEEE32Exec (.dim s (.dim h .scalar)) :=
  Activation.reluSpec (Tensor.addSpec (matMulSpec Xt ffn.W1) (broadcastTo
    (Shape.CanBroadcastTo.expand_dims (Shape.CanBroadcastTo.dim_eq
      (Shape.CanBroadcastTo.scalar_to_any .scalar))
        : Shape.CanBroadcastTo (.dim h .scalar) (.dim s (.dim h .scalar))) ffn.b1))

/-- The literal feed-forward forward pass at `IEEE32Exec`, read back over `ℝ` coordinatewise — the
exact tensor op the hardware runs, the executed map of the FFN block. -/
def ffnExecLit {d h s : ℕ} (ffn : Spec.FeedForward d h IEEE32Exec)
    (Xt : Tensor IEEE32Exec (.dim s (.dim d .scalar))) : Fin s → Fin d → ℝ :=
  tReal2 (Spec.FeedForward.forward ffn Xt)

/-- **The literal feed-forward forward error (the FFN ROOT binding).** The executed
`Spec.FeedForward.forward` at `IEEE32Exec`, read over `ℝ`, is within
`(rdotBudget h (B2'·Λ) + ρ2) + Λ·(rdotBudget d (B·Λ) + ρ1)` of the ℝ-model `ffnCoord` on the
`toReal`-read weights — exactly the pure-ℝ `ffnExecBias_forward_error` budget plus the two bias
roundings (`ρ1` amplified by the second matmul's `Λ`, `ρ2` direct). The honest finiteness regime (each
matmul coordinate, each bias add, the pre-activation) is surfaced as hypotheses, not fabricated. -/
theorem ffnLiteral_forward_error {d h s : ℕ} (ffn : Spec.FeedForward d h IEEE32Exec)
    (Xt : Tensor IEEE32Exec (.dim s (.dim d .scalar)))
    {B B2' Λ ρ1 ρ2 : ℝ} (hB : 0 ≤ B) (hB2' : 0 ≤ B2') (hΛ : 0 ≤ Λ) (hρ1 : 0 ≤ ρ1) (hρ2 : 0 ≤ ρ2)
    (hX : ∀ i k, |tReal2 Xt i k| ≤ B)
    (hW1 : ∀ j, ∑ k, |tReal2 ffn.W1 k j| ≤ Λ) (hW2 : ∀ j, ∑ k, |tReal2 ffn.W2 k j| ≤ Λ)
    (hnorm1 : VexecRectNormal (tReal2 ffn.W1) (tReal2 Xt))
    (hnorm2 : VexecRectNormal (tReal2 ffn.W2) (tReal2 (ffnHiddenT ffn Xt)))
    (hB2bound : ∀ i k, |tReal2 (ffnHiddenT ffn Xt) i k| ≤ B2')
    (hdu : (d : ℝ) * u < 1) (hhu : (h : ℝ) * u < 1)
    (hfin1 : ∀ i k, MatMulCoordFinite Xt ffn.W1 i k)
    (hfin2 : ∀ i j, MatMulCoordFinite (ffnHiddenT ffn Xt) ffn.W2 i j)
    (hpreFin : ∀ i k, isFinite (get2 (Tensor.addSpec (matMulSpec Xt ffn.W1) (broadcastTo
      (Shape.CanBroadcastTo.expand_dims (Shape.CanBroadcastTo.dim_eq
        (Shape.CanBroadcastTo.scalar_to_any .scalar))
          : Shape.CanBroadcastTo (.dim h .scalar) (.dim s (.dim h .scalar))) ffn.b1)) i k) = true)
    (hadd1 : ∀ i k, isFinite (add (get2 (matMulSpec Xt ffn.W1) i k) (Tensor.vecGet ffn.b1 k)) = true)
    (hadd2 : ∀ i j, isFinite (add (get2 (matMulSpec (ffnHiddenT ffn Xt) ffn.W2) i j)
      (Tensor.vecGet ffn.b2 j)) = true)
    (hρ1bound : ∀ i k, eps₃₂ (toReal (get2 (matMulSpec Xt ffn.W1) i k)
      + toReal (Tensor.vecGet ffn.b1 k)) ≤ ρ1)
    (hρ2bound : ∀ i j, eps₃₂ (toReal (get2 (matMulSpec (ffnHiddenT ffn Xt) ffn.W2) i j)
      + toReal (Tensor.vecGet ffn.b2 j)) ≤ ρ2) :
    ‖ffnExecLit ffn Xt
        - ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2) (tReal2 Xt)‖
      ≤ (rdotBudget h (B2' * Λ) + ρ2) + Λ * (rdotBudget d (B * Λ) + ρ1) := by
  have hhidden : tReal2 (ffnHiddenT ffn Xt) = reluCoord (litAff Xt ffn.W1 ffn.b1) := by
    rw [ffnHiddenT, tReal2_reluSpec _ hpreFin]
    rfl
  show ‖litAff (ffnHiddenT ffn Xt) ffn.W2 ffn.b2
      - ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2) (tReal2 Xt)‖ ≤ _
  rw [ffnCoord_eq_affIdeal]
  have hcancel : affIdeal (tReal2 ffn.W2) (tReal1 ffn.b2) (tReal2 (ffnHiddenT ffn Xt))
        - affIdeal (tReal2 ffn.W2) (tReal1 ffn.b2)
            (reluCoord (affIdeal (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 Xt)))
      = matMulCoord (tReal2 ffn.W2) (tReal2 (ffnHiddenT ffn Xt))
          - matMulCoord (tReal2 ffn.W2)
              (reluCoord (affIdeal (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 Xt))) := by
    funext i j; simp only [affIdeal, Pi.sub_apply]; ring
  calc ‖litAff (ffnHiddenT ffn Xt) ffn.W2 ffn.b2
          - affIdeal (tReal2 ffn.W2) (tReal1 ffn.b2)
              (reluCoord (affIdeal (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 Xt)))‖
      = ‖(litAff (ffnHiddenT ffn Xt) ffn.W2 ffn.b2
            - affIdeal (tReal2 ffn.W2) (tReal1 ffn.b2) (tReal2 (ffnHiddenT ffn Xt)))
          + (affIdeal (tReal2 ffn.W2) (tReal1 ffn.b2) (tReal2 (ffnHiddenT ffn Xt))
              - affIdeal (tReal2 ffn.W2) (tReal1 ffn.b2)
                  (reluCoord (affIdeal (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 Xt))))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖litAff (ffnHiddenT ffn Xt) ffn.W2 ffn.b2
            - affIdeal (tReal2 ffn.W2) (tReal1 ffn.b2) (tReal2 (ffnHiddenT ffn Xt))‖
        + ‖affIdeal (tReal2 ffn.W2) (tReal1 ffn.b2) (tReal2 (ffnHiddenT ffn Xt))
            - affIdeal (tReal2 ffn.W2) (tReal1 ffn.b2)
                (reluCoord (affIdeal (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 Xt)))‖ := norm_add_le _ _
    _ ≤ (ρ2 + rdotBudget h (B2' * Λ)) + Λ * (ρ1 + rdotBudget d (B * Λ)) := by
        refine add_le_add
          (litAff_vs_affIdeal (ffnHiddenT ffn Xt) ffn.W2 ffn.b2 hB2' hΛ hρ2 hB2bound hW2 hnorm2 hhu
            hfin2 hadd2 hρ2bound) ?_
        rw [hcancel]
        calc ‖matMulCoord (tReal2 ffn.W2) (tReal2 (ffnHiddenT ffn Xt))
                - matMulCoord (tReal2 ffn.W2)
                    (reluCoord (affIdeal (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 Xt)))‖
            ≤ Λ * ‖tReal2 (ffnHiddenT ffn Xt)
                - reluCoord (affIdeal (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 Xt))‖ :=
              matMulCoordRect_lipschitz (tReal2 ffn.W2) hΛ hW2 _ _
          _ = Λ * ‖reluCoord (litAff Xt ffn.W1 ffn.b1)
                - reluCoord (affIdeal (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 Xt))‖ := by rw [hhidden]
          _ ≤ Λ * ‖litAff Xt ffn.W1 ffn.b1 - affIdeal (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 Xt)‖ :=
              mul_le_mul_of_nonneg_left (reluCoord_lipschitz _ _) hΛ
          _ ≤ Λ * (ρ1 + rdotBudget d (B * Λ)) :=
              mul_le_mul_of_nonneg_left
                (litAff_vs_affIdeal Xt ffn.W1 ffn.b1 hB hΛ hρ1 hX hW1 hnorm1 hdu hfin1 hadd1 hρ1bound)
                hΛ
    _ = (rdotBudget h (B2' * Λ) + ρ2) + Λ * (rdotBudget d (B * Λ) + ρ1) := by ring

end TLT.Fp32FFNLit
