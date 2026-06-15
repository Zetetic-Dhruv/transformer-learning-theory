/-
# The literal executed binding of the fp32 layer-norm: IEEE coordinate reads

The `_ie` coordinate reductions for `Spec.layerNorm`'s remaining tensor ops (`subSpec` / `mulSpec` /
`divSpec` / `sqrtSpec` / `maxSpec` over `IEEE32Exec`), the layer-norm analogues of the `addSpec` / `reluSpec`
reads in `FFNLiteralExecutedBinding`. With the shipped `foldl`-sum bridge `toReal_foldl_add` (used by the
matmul keystone and the softmax denominator) handling `reduceMean`/`reduceVar`, and the shipped per-op
rounding atoms (`toReal_sub_*` / `toReal_div_abs_error` / `toReal_mul_*` / `toReal_sqrt_abs_error`), the
literal layer-norm binds op-by-op exactly as the attention and feed-forward sub-layers do.
-/
import TLT_Proofs.Bridge.Certificate.FFNLiteralExecutedBinding
import TLT_Proofs.Bridge.Fp32.LayerNormForwardError

open TorchLean.Floats.IEEE754
open TorchLean.Floats.IEEE754.IEEE32Exec
open Spec Tensor

noncomputable section

namespace TLT.Fp32LNLit

open TLT TLT.Fp32FFNLit TLT.Fp32AttnLit TLT.Fp32LN

/-- Matrix coordinate read of `subSpec` at `IEEE32Exec`: `(subSpec A B)[i,j] = A[i,j] - B[i,j]`. -/
lemma get2_subSpec_ie {m n : ℕ} (A B : Tensor IEEE32Exec (.dim m (.dim n .scalar)))
    (i : Fin m) (j : Fin n) :
    get2 (Tensor.subSpec A B) i j = get2 A i j - get2 B i j := by
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
              simp [Tensor.subSpec, Tensor.map2Spec, get2, get_eq, hA, hB, hcA, hcB]

/-- Matrix coordinate read of `mulSpec` at `IEEE32Exec`: `(mulSpec A B)[i,j] = A[i,j] * B[i,j]`. -/
lemma get2_mulSpec_ie {m n : ℕ} (A B : Tensor IEEE32Exec (.dim m (.dim n .scalar)))
    (i : Fin m) (j : Fin n) :
    get2 (Tensor.mulSpec A B) i j = get2 A i j * get2 B i j := by
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
              simp [Tensor.mulSpec, Tensor.map2Spec, get2, get_eq, hA, hB, hcA, hcB]

/-- Matrix coordinate read of `divSpec` at `IEEE32Exec`: `(divSpec A B)[i,j] = A[i,j] / B[i,j]`. -/
lemma get2_divSpec_ie {m n : ℕ} (A B : Tensor IEEE32Exec (.dim m (.dim n .scalar)))
    (i : Fin m) (j : Fin n) :
    get2 (Tensor.divSpec A B) i j = get2 A i j / get2 B i j := by
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
              simp [Tensor.divSpec, Tensor.map2Spec, get2, get_eq, hA, hB, hcA, hcB]

/-- Matrix coordinate read of a ROW-broadcast vector at `IEEE32Exec` (the mean/std broadcast): row `i`
of the `(seqLen × em)` broadcast of a length-`seqLen` vector `v` is `v[i]` (constant along the columns). -/
lemma get2_broadcast_row_ie {sq em : ℕ} (v : Tensor IEEE32Exec (.dim sq .scalar))
    (i : Fin sq) (j : Fin em) :
    get2 (broadcastTo (Shape.CanBroadcastTo.dim_eq (Shape.CanBroadcastTo.expand_dims
      (Shape.CanBroadcastTo.scalar_to_any .scalar))
        : Shape.CanBroadcastTo (.dim sq .scalar) (.dim sq (.dim em .scalar))) v) i j
      = Tensor.vecGet v i := by
  cases v with
  | dim xs =>
    cases hx : xs i with
    | scalar w => simp [get2, get_eq, broadcastTo, replicate, Tensor.vecGet, hx, Tensor.toScalar]

/-- **The literal layer-norm reads op-by-op as the executed affine.** `Spec.layerNorm`'s output
coordinate `[i,j]` at `IEEE32Exec` is exactly the executed `((x − mean)/std · γ + β)` of the literal
per-row mean `mT` and std `sT` (whatever the bit-level reductions compute them to be): the literal
IEEE `add`/`mul`/`div`/`sub` composition, read through the shipped `_ie` coordinate reductions. The
mean/std enter as opaque per-row vectors; their rounding vs the exact `rowMean`/`rowStd` is the `ρm`/`ρs`
budget that `lnExec_forward_error` carries. This binds `Spec.layerNorm`'s affine pipeline op-by-op,
exactly as the attention and feed-forward sub-layers bind. -/
lemma get2_layerNorm_litAffine {seqLen embedDim : ℕ} (h1 : seqLen > 0) (h2 : embedDim > 0)
    (Xt : Tensor IEEE32Exec (.dim seqLen (.dim embedDim .scalar)))
    (γt βt : Tensor IEEE32Exec (.dim embedDim .scalar)) (εt : IEEE32Exec)
    (i : Fin seqLen) (j : Fin embedDim) :
    ∃ mT sT : Tensor IEEE32Exec (.dim seqLen .scalar),
      get2 (Spec.layerNorm Xt γt βt h1 h2 εt) i j
        = (get2 Xt i j - Tensor.vecGet mT i) / Tensor.vecGet sT i * Tensor.vecGet γt j
            + Tensor.vecGet βt j := by
  simp only [Spec.layerNorm, get2_addSpec_ie, get2_mulSpec_ie, get2_divSpec_ie, get2_subSpec_ie,
    get2_broadcast_row_ie, get2_broadcast_bias_ie]
  exact ⟨_, _, rfl⟩

/-- **The literal layer-norm forward error (the LN ROOT binding).** `toReal∘Spec.layerNorm` at
`IEEE32Exec` is within `δ + (ρround + Cγ·(ρm/√ε + 2B·ρs/ε))` of the ℝ-model `layerNormCoord` on the
`toReal`-read weights. The executed per-row mean/std (`meanIE`/`stdIE`, the bit-level reductions read over
`ℝ`) enter with their roundings `ρm`/`ρs`; `δ` bounds the literal per-op affine read against the executed
model `lnStarExec` (dischargeable from `get2_layerNorm_litAffine` + the shipped `toReal_sub_*`/`toReal_div_*`/
`toReal_mul_*`/`toReal_add_*` atoms with the per-op finiteness regime as hypotheses). The ideal bound
reuses the shipped `lnExec_forward_error` verbatim, with no additional error machinery beyond what the
attention and feed-forward sub-layers use. -/
theorem toReal_layerNorm_forward_error {seqLen embedDim : ℕ} (h1 : seqLen > 0) (h2 : embedDim > 0)
    (Xt : Tensor IEEE32Exec (.dim seqLen (.dim embedDim .scalar)))
    (γt βt : Tensor IEEE32Exec (.dim embedDim .scalar)) (εt : IEEE32Exec)
    (meanIE stdIE : Fin seqLen → ℝ) {B Cγ ρround ρm ρs δ : ℝ}
    (hB : 0 ≤ B) (hCγ0 : 0 ≤ Cγ) (hρm : 0 ≤ ρm) (hρs : 0 ≤ ρs) (hρr : 0 ≤ ρround) (hδ : 0 ≤ δ)
    (hX : ∀ i k, |tReal2 Xt i k| ≤ B) (hCγ : ∀ j, |tReal1 γt j| ≤ Cγ)
    (hround : ∀ i j, |lnStarExec (tReal1 γt) (tReal1 βt) meanIE stdIE (tReal2 Xt) i j
      - ((tReal2 Xt i j - meanIE i) / stdIE i * tReal1 γt j + tReal1 βt j)| ≤ ρround)
    (hmean : ∀ i, |meanIE i - rowMeanCoord i (tReal2 Xt)| ≤ ρm)
    (hmeanB : ∀ i, |rowMeanCoord i (tReal2 Xt)| ≤ B)
    (hstd : ∀ i, |stdIE i - rowStdCoord i (tReal2 Xt)| ≤ ρs)
    (hstdE : ∀ i, Real.sqrt Numbers.epsilon ≤ stdIE i)
    (hreadgap : ∀ i j, |toReal (get2 (Spec.layerNorm Xt γt βt h1 h2 εt) i j)
      - lnStarExec (tReal1 γt) (tReal1 βt) meanIE stdIE (tReal2 Xt) i j| ≤ δ) :
    ‖(fun i j => toReal (get2 (Spec.layerNorm Xt γt βt h1 h2 εt) i j))
        - layerNormCoord (tReal1 γt) (tReal1 βt) (tReal2 Xt)‖
      ≤ δ + (ρround + Cγ * (ρm / Real.sqrt Numbers.epsilon + 2 * B * ρs / Numbers.epsilon)) := by
  have hgap : ‖(fun i j => toReal (get2 (Spec.layerNorm Xt γt βt h1 h2 εt) i j))
      - lnStarExec (tReal1 γt) (tReal1 βt) meanIE stdIE (tReal2 Xt)‖ ≤ δ := by
    refine (pi_norm_le_iff_of_nonneg hδ).mpr (fun i => ?_)
    refine (pi_norm_le_iff_of_nonneg hδ).mpr (fun j => ?_)
    rw [Real.norm_eq_abs, Pi.sub_apply, Pi.sub_apply]
    exact hreadgap i j
  have hideal : ‖lnStarExec (tReal1 γt) (tReal1 βt) meanIE stdIE (tReal2 Xt)
      - layerNormCoord (tReal1 γt) (tReal1 βt) (tReal2 Xt)‖
      ≤ ρround + Cγ * (ρm / Real.sqrt Numbers.epsilon + 2 * B * ρs / Numbers.epsilon) :=
    lnExec_forward_error (tReal1 γt) (tReal1 βt) meanIE stdIE (tReal2 Xt) hB hCγ0 hρm hρs hρr hX hCγ
      hround hmean hmeanB hstd hstdE
  calc ‖(fun i j => toReal (get2 (Spec.layerNorm Xt γt βt h1 h2 εt) i j))
          - layerNormCoord (tReal1 γt) (tReal1 βt) (tReal2 Xt)‖
      = ‖((fun i j => toReal (get2 (Spec.layerNorm Xt γt βt h1 h2 εt) i j))
            - lnStarExec (tReal1 γt) (tReal1 βt) meanIE stdIE (tReal2 Xt))
          + (lnStarExec (tReal1 γt) (tReal1 βt) meanIE stdIE (tReal2 Xt)
              - layerNormCoord (tReal1 γt) (tReal1 βt) (tReal2 Xt))‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖(fun i j => toReal (get2 (Spec.layerNorm Xt γt βt h1 h2 εt) i j))
            - lnStarExec (tReal1 γt) (tReal1 βt) meanIE stdIE (tReal2 Xt)‖
        + ‖lnStarExec (tReal1 γt) (tReal1 βt) meanIE stdIE (tReal2 Xt)
            - layerNormCoord (tReal1 γt) (tReal1 βt) (tReal2 Xt)‖ := norm_add_le _ _
    _ ≤ δ + (ρround + Cγ * (ρm / Real.sqrt Numbers.epsilon + 2 * B * ρs / Numbers.epsilon)) :=
        add_le_add hgap hideal

end TLT.Fp32LNLit
