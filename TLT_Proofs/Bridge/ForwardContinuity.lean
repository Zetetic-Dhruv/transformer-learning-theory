/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Log.Base
import NN.Spec.Core.Tensor.Core
import NN.Spec.Core.Tensor.Linalg
import NN.Spec.Core.Tensor.Constructors
import NN.Spec.Core.TensorOps
import NN.Spec.Layers.Activation
import NN.Proofs.Tensor.Basic
import NN.Proofs.Autograd.FDeriv.Softmax

/-!
# Continuity of the transformer forward-pass atoms, in coordinates

The transformer forward map is a composition of tensor operations. Stated over curried real
coordinates (`Fin m → Fin n → ℝ`, which carry the product topology), each operation is continuous,
hence so is their composition — and a continuous map of a finite-dimensional real space is Borel
measurable.

This file builds the per-operation continuity lemmas. The first is the linear (matrix-multiply)
layer, which covers the embedding and output projections.

## Main results

- `matMulCoord` — the matrix-multiply layer in curried coordinates: `(X · W) i j = ∑ k, X i k · W k j`.
- `continuous_matMulCoord` — that layer is continuous in its input.
- `reluCoord` — the ReLU layer in coordinates: pointwise `max (·) 0`.
- `continuous_reluCoord` — that layer is continuous.

(Elementwise addition — residual and bias adds — is the pointwise `+` on `Fin m → Fin n → ℝ`, whose
continuity is `Continuous.add`, so it needs no separate atom.)
-/

open Spec

namespace TLT

/-- The matrix-multiply layer in curried real coordinates: with a fixed weight `W`, the input
`X : Fin m → Fin n → ℝ` maps to `fun i j => ∑ k, X i k * W k j`. -/
def matMulCoord {m n p : ℕ} (W : Fin n → Fin p → ℝ) (X : Fin m → Fin n → ℝ) :
    Fin m → Fin p → ℝ :=
  fun i j => ∑ k, X i k * W k j

/-- The coordinate matrix-multiply layer is continuous in its input. -/
theorem continuous_matMulCoord {m n p : ℕ} (W : Fin n → Fin p → ℝ) :
    Continuous (matMulCoord (m := m) W) := by
  unfold matMulCoord
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  refine continuous_finset_sum Finset.univ (fun k _ => ?_)
  exact (continuous_apply_apply i k).mul continuous_const

/-- The ReLU layer in curried real coordinates: pointwise `max (·) 0`. -/
def reluCoord {m n : ℕ} (X : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => max (X i j) 0

/-- The coordinate ReLU layer is continuous. -/
theorem continuous_reluCoord {m n : ℕ} :
    Continuous (reluCoord (m := m) (n := n)) := by
  unfold reluCoord
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  exact (continuous_apply_apply i j).max continuous_const

/-- Read a matrix tensor as curried real coordinates. -/
def matCoords {m n : ℕ} (T : Tensor ℝ (.dim m (.dim n .scalar))) : Fin m → Fin n → ℝ :=
  fun i j => get2 T i j

/-- Round-trip: the coordinates of a `matrixTensor` recover the function entrywise. -/
@[simp] lemma get2_matrixTensor {m n : ℕ} (X : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    get2 (matrixTensor X) i j = X i j := by
  simp [matrixTensor, vectorTensor, get2, get_eq]

/-- The TorchLean matrix-multiply layer, read in coordinates as a function of its input, equals the
clean coordinate layer `matMulCoord` and is therefore continuous. The weight tensor `W` is fixed. -/
theorem continuous_matCoords_matMulSpec {m n p : ℕ}
    (W : Tensor ℝ (.dim n (.dim p .scalar))) :
    Continuous (fun X : Fin m → Fin n → ℝ => matCoords (matMulSpec (matrixTensor X) W)) := by
  have h : (fun X : Fin m → Fin n → ℝ => matCoords (matMulSpec (matrixTensor X) W))
         = matMulCoord (matCoords W) := by
    funext X i j
    simp only [matCoords, matMulCoord, get2_mat_mul_spec]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [get2_matrixTensor]
  rw [h]
  exact continuous_matMulCoord _

/-- Matrix characterization of the ReLU layer: `(reluSpec T)[i,j] = max T[i,j] 0`. -/
lemma get2_reluSpec {m n : ℕ} (T : Tensor ℝ (.dim m (.dim n .scalar))) (i : Fin m) (j : Fin n) :
    get2 (Activation.reluSpec T) i j = max (get2 T i j) 0 := by
  cases T with
  | dim rows =>
    cases hrow : rows i with
    | dim cols =>
      cases hcol : cols j with
      | scalar x =>
        simp [Activation.reluSpec, Activation.Math.reluSpec, Tensor.mapSpec, get2, get_eq,
          hrow, hcol]

/-- The TorchLean ReLU layer, read in coordinates, equals `reluCoord` and is continuous. -/
theorem continuous_matCoords_reluSpec {m n : ℕ} :
    Continuous (fun X : Fin m → Fin n → ℝ => matCoords (Activation.reluSpec (matrixTensor X))) := by
  have h : (fun X : Fin m → Fin n → ℝ => matCoords (Activation.reluSpec (matrixTensor X)))
         = reluCoord := by
    funext X i j
    simp only [matCoords, reluCoord, get2_reluSpec, get2_matrixTensor]
  rw [h]
  exact continuous_reluCoord

/-- Matrix characterization of elementwise addition: `(addSpec A B)[i,j] = A[i,j] + B[i,j]`. -/
lemma get2_addSpec {m n : ℕ} (A B : Tensor ℝ (.dim m (.dim n .scalar))) (i : Fin m) (j : Fin n) :
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

/-- Reading the coordinates of an elementwise sum is the pointwise sum of the coordinates. -/
lemma matCoords_addSpec {m n : ℕ} (A B : Tensor ℝ (.dim m (.dim n .scalar))) :
    matCoords (Tensor.addSpec A B) = matCoords A + matCoords B := by
  funext i j
  simp only [matCoords, get2_addSpec, Pi.add_apply]

/-- Bridge foundation (softmax): the autograd softmax over `Vec n = EuclideanSpace ℝ (Fin n)` is
continuous, derived from its differentiability (`hasFDerivAt_softmaxVec`). The `Vec ≃L (Fin n → ℝ)`
transport (`EuclideanSpace.equiv`) then carries this to a coordinate statement. -/
theorem continuous_softmaxVec {n : ℕ} :
    Continuous (Proofs.Autograd.softmaxVec (n := n)) :=
  Differentiable.continuous fun x => (Proofs.Autograd.hasFDerivAt_softmaxVec x).differentiableAt

/-- The softmax over coordinates `Fin n → ℝ`, defined through the autograd `softmaxVec` and the
continuous-linear transport `EuclideanSpace.equiv : EuclideanSpace ℝ (Fin n) ≃L (Fin n → ℝ)`. -/
noncomputable def softmaxCoord {n : ℕ} (f : Fin n → ℝ) : Fin n → ℝ :=
  EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)
    (Proofs.Autograd.softmaxVec ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm f))

/-- The coordinate softmax is continuous: `softmaxVec` is differentiable (hence continuous), and the
`EuclideanSpace ≃L (Fin n → ℝ)` transport is continuous both ways. -/
theorem continuous_softmaxCoord {n : ℕ} : Continuous (softmaxCoord (n := n)) := by
  unfold softmaxCoord
  exact (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).continuous.comp
    (continuous_softmaxVec.comp (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm.continuous)

end TLT
