/-
# The literal executed binding of the fp32 layer-norm — IEEE coordinate reads

The `_ie` coordinate reductions for `Spec.layerNorm`'s remaining tensor ops (`subSpec` / `mulSpec` /
`divSpec` / `sqrtSpec` / `maxSpec` over `IEEE32Exec`), the layer-norm analogues of the `addSpec` / `reluSpec`
reads in `FFNLiteralExecutedBinding`. With the shipped `foldl`-sum bridge `toReal_foldl_add` (used by the
matmul keystone and the softmax denominator) handling `reduceMean`/`reduceVar`, and the shipped per-op
rounding atoms (`toReal_sub_*` / `toReal_div_abs_error` / `toReal_mul_*` / `toReal_sqrt_abs_error`), the
literal layer-norm binds op-by-op exactly as the attention and feed-forward sub-layers do.
-/
import TLT_Proofs.Bridge.Certificate.FFNLiteralExecutedBinding

open TorchLean.Floats.IEEE754
open TorchLean.Floats.IEEE754.IEEE32Exec
open Spec Tensor

noncomputable section

namespace TLT.Fp32LNLit

open TLT TLT.Fp32FFNLit TLT.Fp32AttnLit

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

end TLT.Fp32LNLit
