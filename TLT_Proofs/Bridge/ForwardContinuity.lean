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

/-- The verified layerNorm regularization constant for the ℝ backend is strictly positive
(`Numbers.epsilon = 1e-6`, `NN/Spec/Core/Context.lean`). This single scalar is what makes the entire
transformer forward map continuous: it bounds the layerNorm denominator away from zero. -/
lemma numbers_epsilon_real_pos : (0 : ℝ) < Numbers.epsilon := by
  have h : (Numbers.epsilon : ℝ) = 1e-6 := rfl
  rw [h]; norm_num

/-- The layerNorm standard deviation `std = √(max(var,0) + ε)` is strictly positive for every variance
value, because `ε > 0` (verified `1e-6`). This discharges the `divSpec` side-condition in layerNorm
unconditionally — the crux of the forward map's continuity. -/
lemma layerNorm_std_pos (v : ℝ) : 0 < Real.sqrt (max v 0 + Numbers.epsilon) := by
  refine Real.sqrt_pos.mpr ?_
  have h0 : (0 : ℝ) ≤ max v 0 := le_max_right v 0
  have hε : (0 : ℝ) < Numbers.epsilon := numbers_epsilon_real_pos
  linarith

/-- Per-row mean of a coordinate matrix. -/
noncomputable def rowMeanCoord {s d : ℕ} (i : Fin s) (X : Fin s → Fin d → ℝ) : ℝ :=
  (∑ k, X i k) / (d : ℝ)

lemma continuous_rowMeanCoord {s d : ℕ} (i : Fin s) :
    Continuous (rowMeanCoord (s := s) (d := d) i) := by
  unfold rowMeanCoord
  exact (continuous_finset_sum Finset.univ (fun k _ => continuous_apply_apply i k)).div_const _

/-- Per-row population variance of a coordinate matrix. -/
noncomputable def rowVarCoord {s d : ℕ} (i : Fin s) (X : Fin s → Fin d → ℝ) : ℝ :=
  (∑ k, (X i k - rowMeanCoord i X) ^ 2) / (d : ℝ)

lemma continuous_rowVarCoord {s d : ℕ} (i : Fin s) :
    Continuous (rowVarCoord (s := s) (d := d) i) := by
  unfold rowVarCoord
  refine (continuous_finset_sum Finset.univ (fun k _ => ?_)).div_const _
  exact ((continuous_apply_apply i k).sub (continuous_rowMeanCoord i)).pow 2

/-- Per-row layer-norm standard deviation (with the verified positive regularizer). -/
noncomputable def rowStdCoord {s d : ℕ} (i : Fin s) (X : Fin s → Fin d → ℝ) : ℝ :=
  Real.sqrt (max (rowVarCoord i X) 0 + Numbers.epsilon)

lemma continuous_rowStdCoord {s d : ℕ} (i : Fin s) :
    Continuous (rowStdCoord (s := s) (d := d) i) := by
  unfold rowStdCoord
  exact Real.continuous_sqrt.comp
    (((continuous_rowVarCoord i).max continuous_const).add continuous_const)

lemma rowStdCoord_pos {s d : ℕ} (i : Fin s) (X : Fin s → Fin d → ℝ) :
    0 < rowStdCoord i X := layerNorm_std_pos _

/-- Layer normalization in coordinates: per row, center, divide by the regularized standard deviation,
then scale by `γ` and shift by `β`. The division is everywhere-defined because `rowStdCoord_pos`. -/
noncomputable def layerNormCoord {s d : ℕ} (γ β : Fin d → ℝ) (X : Fin s → Fin d → ℝ) :
    Fin s → Fin d → ℝ :=
  fun i j => (X i j - rowMeanCoord i X) / rowStdCoord i X * γ j + β j

/-- The coordinate layer-normalization map is continuous (unconditionally — the denominator never
vanishes, by `rowStdCoord_pos`, which rests on the verified `ε = 1e-6`). -/
theorem continuous_layerNormCoord {s d : ℕ} (γ β : Fin d → ℝ) :
    Continuous (layerNormCoord (s := s) γ β) := by
  unfold layerNormCoord
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  refine ((Continuous.div ?_ (continuous_rowStdCoord i)
    (fun X => ne_of_gt (rowStdCoord_pos i X))).mul continuous_const).add continuous_const
  exact (continuous_apply_apply i j).sub (continuous_rowMeanCoord i)

/-- The feed-forward block in coordinates: two affine (matrix-multiply + bias) layers around a ReLU,
`out[i,j] = (∑ₗ max(⟨X i, W1·ₗ⟩ + b1 l, 0) · W2 l j) + b2 j`. -/
noncomputable def ffnCoord {s d h : ℕ} (W1 : Fin d → Fin h → ℝ) (b1 : Fin h → ℝ)
    (W2 : Fin h → Fin d → ℝ) (b2 : Fin d → ℝ) (X : Fin s → Fin d → ℝ) : Fin s → Fin d → ℝ :=
  fun i j => (∑ l, max (matMulCoord W1 X i l + b1 l) 0 * W2 l j) + b2 j

/-- The coordinate feed-forward block is continuous (composition of the continuous linear, bias, and
ReLU layers). -/
theorem continuous_ffnCoord {s d h : ℕ} (W1 : Fin d → Fin h → ℝ) (b1 : Fin h → ℝ)
    (W2 : Fin h → Fin d → ℝ) (b2 : Fin d → ℝ) :
    Continuous (ffnCoord (s := s) W1 b1 W2 b2) := by
  unfold ffnCoord
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  refine (continuous_finset_sum Finset.univ (fun l _ => ?_)).add continuous_const
  refine (Continuous.max ?_ continuous_const).mul continuous_const
  exact ((continuous_apply_apply i l).comp (continuous_matMulCoord W1)).add continuous_const

/-- General continuity of a contracted matrix product where **both** factors vary continuously:
`(A x · B x) i j = ∑ k, A x i k · B x k j`. This covers every matrix multiplication in attention —
the scores `Q·Kᵀ`, the value mixing `weights·V`, and the Q/K/V/output projections — where, unlike a
fixed-weight layer, both operands depend on the input. -/
theorem continuous_matMulVar {X : Type*} [TopologicalSpace X] {m n p : ℕ}
    {A : X → Fin m → Fin n → ℝ} {B : X → Fin n → Fin p → ℝ}
    (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x => fun (i : Fin m) (j : Fin p) => ∑ k, A x i k * B x k j) := by
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  refine continuous_finset_sum Finset.univ (fun k _ => ?_)
  exact ((continuous_apply_apply i k).comp hA).mul ((continuous_apply_apply k j).comp hB)

/-- The row-wise softmax attention weights are continuous in the (continuous) query/key projections. -/
private lemma continuous_attentionWeightsCoord {X : Type*} [TopologicalSpace X] {nQ nK dM : ℕ}
    (scale : ℝ) {Q : X → Fin nQ → Fin dM → ℝ} {K : X → Fin nK → Fin dM → ℝ}
    (hQ : Continuous Q) (hK : Continuous K) :
    Continuous (fun x => fun (q : Fin nQ) (k : Fin nK) =>
      softmaxCoord (fun k' => (∑ d, Q x q d * K x k' d) / scale) k) := by
  refine continuous_pi (fun q => continuous_softmaxCoord.comp ?_)
  refine continuous_pi (fun k' => Continuous.div_const ?_ scale)
  exact continuous_finset_sum Finset.univ (fun d _ =>
    ((continuous_apply_apply q d).comp hQ).mul ((continuous_apply_apply k' d).comp hK))

/-- Scaled-dot-product attention is continuous: given continuous query/key/value projections of the
input, the output `rowSoftmax(Q·Kᵀ / scale) · V` is continuous. This is the transformer's core
nonlinearity; it composes the bilinear scores, the row-wise softmax (`continuous_softmaxCoord`), and
the value mixing (`continuous_matMulVar`). -/
theorem continuous_attentionCoord {X : Type*} [TopologicalSpace X] {nQ nK dM dV : ℕ} (scale : ℝ)
    {Q : X → Fin nQ → Fin dM → ℝ} {K : X → Fin nK → Fin dM → ℝ} {V : X → Fin nK → Fin dV → ℝ}
    (hQ : Continuous Q) (hK : Continuous K) (hV : Continuous V) :
    Continuous (fun x => fun (q : Fin nQ) (e : Fin dV) =>
      ∑ k, softmaxCoord (fun k' => (∑ d, Q x q d * K x k' d) / scale) k * V x k e) :=
  continuous_matMulVar (continuous_attentionWeightsCoord scale hQ hK) hV

/-- Post-attention normalized residual block `layerNorm(X + attn X)`. -/
noncomputable def normAttnCoord {s d : ℕ} (γ β : Fin d → ℝ)
    (attn : (Fin s → Fin d → ℝ) → Fin s → Fin d → ℝ) (X : Fin s → Fin d → ℝ) : Fin s → Fin d → ℝ :=
  layerNormCoord γ β (fun i j => X i j + attn X i j)

private lemma continuous_normAttnCoord {s d : ℕ} (γ β : Fin d → ℝ)
    {attn : (Fin s → Fin d → ℝ) → Fin s → Fin d → ℝ} (hattn : Continuous attn) :
    Continuous (normAttnCoord γ β attn) := by
  unfold normAttnCoord
  refine (continuous_layerNormCoord γ β).comp ?_
  exact continuous_pi (fun i => continuous_pi (fun j =>
    (continuous_apply_apply i j).add ((continuous_apply_apply i j).comp hattn)))

/-- A transformer encoder layer in coordinates: residual self-attention then layer-norm, then residual
feed-forward then layer-norm. -/
noncomputable def encoderLayerCoord {s d h : ℕ} (γ1 β1 γ2 β2 : Fin d → ℝ)
    (W1 : Fin d → Fin h → ℝ) (b1 : Fin h → ℝ) (W2 : Fin h → Fin d → ℝ) (b2 : Fin d → ℝ)
    (attn : (Fin s → Fin d → ℝ) → Fin s → Fin d → ℝ) (X : Fin s → Fin d → ℝ) : Fin s → Fin d → ℝ :=
  layerNormCoord γ2 β2 (fun i j =>
    normAttnCoord γ1 β1 attn X i j + ffnCoord W1 b1 W2 b2 (normAttnCoord γ1 β1 attn X) i j)

/-- A transformer encoder layer is continuous, given a continuous self-attention map (which
`continuous_attentionCoord` supplies). Assembles the attention, residual, layer-norm, and feed-forward
continuities. -/
theorem continuous_encoderLayerCoord {s d h : ℕ} (γ1 β1 γ2 β2 : Fin d → ℝ)
    (W1 : Fin d → Fin h → ℝ) (b1 : Fin h → ℝ) (W2 : Fin h → Fin d → ℝ) (b2 : Fin d → ℝ)
    {attn : (Fin s → Fin d → ℝ) → Fin s → Fin d → ℝ} (hattn : Continuous attn) :
    Continuous (encoderLayerCoord γ1 β1 γ2 β2 W1 b1 W2 b2 attn) := by
  unfold encoderLayerCoord
  refine (continuous_layerNormCoord γ2 β2).comp (continuous_pi (fun i => continuous_pi (fun j => ?_)))
  exact ((continuous_apply_apply i j).comp (continuous_normAttnCoord γ1 β1 hattn)).add
    ((continuous_apply_apply i j).comp
      ((continuous_ffnCoord W1 b1 W2 b2).comp (continuous_normAttnCoord γ1 β1 hattn)))

/-- A left-fold of continuous endomorphisms is continuous. Applied to a list of continuous transformer
layers, this gives continuity of the whole stack (the encoder / decoder is a `List.foldl` of layers). -/
lemma continuous_listFoldl {α : Type*} [TopologicalSpace α] (fs : List (α → α))
    (h : ∀ f ∈ fs, Continuous f) :
    Continuous (fun x => fs.foldl (fun acc f => f acc) x) := by
  induction fs with
  | nil => exact continuous_id
  | cons f rest ih =>
    simp only [List.foldl_cons]
    exact (ih (fun g hg => h g (List.mem_cons.mpr (Or.inr hg)))).comp
      (h f (List.mem_cons.mpr (Or.inl rfl)))

end TLT
