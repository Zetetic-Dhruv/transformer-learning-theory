/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.ForwardContinuity
import NN.Spec.Layers.Normalization
import NN.Spec.Core.TensorReductionShape
import NN.Proofs.Tensor.Basic
import NN.Spec.Core.TensorOps
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
open Spec Spec.Tensor
open TLT

variable {α : Type} [AddCommMonoid α]

private lemma go_add {n : ℕ} {s : Shape} (values : Fin n → Tensor α s)
    (hsl : ∀ (i : Fin n) (acc : α), tensorFoldlSpec (·+·) acc (values i) = acc + sumSpec (values i)) :
    ∀ (fuel i : ℕ) (acc : α), n - i ≤ fuel →
      tensorFoldlSpec.go (·+·) n s values i acc
        = acc + tensorFoldlSpec.go (·+·) n s values i 0 := by
  intro fuel
  induction fuel with
  | zero =>
    intro i acc hi
    have hni : ¬ i < n := by grind
    rw [tensorFoldlSpec.go, tensorFoldlSpec.go]; simp [hni]
  | succ f ih =>
    intro i acc hi
    by_cases h : i < n
    · rw [tensorFoldlSpec.go]; simp only [h, dif_pos]
      conv_rhs => rw [tensorFoldlSpec.go]
      simp only [h, dif_pos]
      rw [hsl ⟨i, h⟩ acc, hsl ⟨i, h⟩ 0, zero_add]
      rw [ih (i + 1) (acc + sumSpec (values ⟨i, h⟩)) (by grind)]
      rw [ih (i + 1) (sumSpec (values ⟨i, h⟩)) (by grind), add_assoc]
    · rw [tensorFoldlSpec.go, tensorFoldlSpec.go]; simp [h]

private lemma tfold_acc : ∀ {s : Shape} (t : Tensor α s) (acc : α),
    tensorFoldlSpec (·+·) acc t = acc + sumSpec t := by
  intro s
  induction s with
  | scalar => intro t acc; cases t with | scalar v => simp [sumSpec, tensorFoldlSpec]
  | dim n s ih =>
    intro t acc
    cases t with
    | dim values =>
      simp only [tensorFoldlSpec]
      rw [go_add values (fun i a => ih (values i) a) n 0 acc (by grind)]
      simp [sumSpec, tensorFoldlSpec]

private lemma go_sum {n : ℕ} {s : Shape} (values : Fin n → Tensor α s)
    (hsl : ∀ (i : Fin n) (acc : α), tensorFoldlSpec (·+·) acc (values i) = acc + sumSpec (values i)) :
    ∀ (fuel i : ℕ), n - i ≤ fuel →
      tensorFoldlSpec.go (·+·) n s values i 0
        = ∑ k : Fin n, (if i ≤ (k : ℕ) then sumSpec (values k) else 0) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i hi
    have hni : ¬ i < n := by grind
    rw [tensorFoldlSpec.go]; simp only [hni, dif_neg, not_false_iff]
    symm; apply Finset.sum_eq_zero; intro k _
    have hk : ¬ i ≤ (k : ℕ) := by have := k.isLt; grind
    simp [hk]
  | succ f ih =>
    intro i hi
    by_cases h : i < n
    · rw [tensorFoldlSpec.go]; simp only [h, dif_pos]
      rw [hsl ⟨i, h⟩ 0, zero_add]
      rw [go_add values hsl f (i + 1) (sumSpec (values ⟨i, h⟩)) (by grind)]
      rw [ih (i + 1) (by grind)]
      have hsplit : (∑ k : Fin n, if i ≤ (k : ℕ) then sumSpec (values k) else 0)
          = (∑ k : Fin n, if i + 1 ≤ (k : ℕ) then sumSpec (values k) else 0)
            + ∑ k : Fin n, (if (k : ℕ) = i then sumSpec (values k) else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro k _; split_ifs <;> grind
      have hsingle : (∑ k : Fin n, if (k : ℕ) = i then sumSpec (values k) else 0)
          = sumSpec (values ⟨i, h⟩) := by
        rw [Finset.sum_eq_single_of_mem (⟨i, h⟩ : Fin n) (Finset.mem_univ _)]
        · simp
        · intro k _ hk
          have hki : (k : ℕ) ≠ i := fun hc => hk (Fin.ext hc)
          simp [hki]
      rw [hsplit, hsingle]; exact add_comm _ _
    · rw [tensorFoldlSpec.go]; simp only [h, dif_neg, not_false_iff]
      symm; apply Finset.sum_eq_zero; intro k _
      have hk : ¬ i ≤ (k : ℕ) := by have := k.isLt; grind
      simp [hk]

private lemma sumSpec_dim {n : ℕ} {s : Shape} (values : Fin n → Tensor α s) :
    sumSpec (Tensor.dim values) = ∑ k, sumSpec (values k) := by
  have hsl : ∀ (i : Fin n) (acc : α),
      tensorFoldlSpec (·+·) acc (values i) = acc + sumSpec (values i) :=
    fun i acc => tfold_acc (values i) acc
  rw [show sumSpec (Tensor.dim values) = tensorFoldlSpec.go (·+·) n s values 0 0 by
        simp [sumSpec, tensorFoldlSpec]]
  rw [go_sum values hsl n 0 (by grind)]
  simp

-- ===== reduceSum / reduceMean axis-1 characterization for 2D tensors =====

/-- `sumSpec` of a scalar tensor is its value. -/
private lemma sumSpec_scalar (v : α) : sumSpec (Tensor.scalar v) = v := by
  simp [sumSpec, tensorFoldlSpec]

/-- `reduceSum` along the last axis of a 2D tensor: each output row is the `sumSpec` of that row. -/
private lemma reduceSum_one {sq em : ℕ} (x : Tensor α (.dim sq (.dim em .scalar)))
    (h : Shape.reducibleAlong 1 (.dim sq (.dim em .scalar))) :
    reduceSum 1 x h = Tensor.dim (fun i => Tensor.scalar (sumSpec (getAtSpec x i))) := by
  cases x with
  | dim rows =>
    simp only [reduceSum, reduceDim, reduceDim.aux, reduceFirstDim, getAtSpec, cast_eq]
    congr 1
    funext i
    cases rows i with
    | dim slices => rfl

/-- The `sumSpec` of a matrix row is the `Finset.sum` of its `get2` entries. -/
private lemma sumSpec_row {sq em : ℕ} (x : Tensor α (.dim sq (.dim em .scalar))) (i : Fin sq) :
    sumSpec (getAtSpec x i) = ∑ j, get2 x i j := by
  cases x with
  | dim rows =>
    cases hrows : rows i with
    | dim cols =>
      simp only [getAtSpec]
      rw [hrows, sumSpec_dim]
      apply Finset.sum_congr rfl
      intro j _
      cases hcols : cols j with
      | scalar v =>
        rw [sumSpec_scalar]
        simp [get2, get_eq, hrows, hcols]

-- ===== reduceMean axis-1 value characterization =====

/-- The spec per-row mean equals the coordinate mean `(∑ⱼ Xᵢⱼ)/em`. -/
private lemma reduceMean_one_val {sq em : ℕ} (x : Tensor ℝ (.dim sq (.dim em .scalar)))
    (h : Shape.reducibleAlong 1 (.dim sq (.dim em .scalar))) (i : Fin sq) :
    Tensor.toScalar (Spec.get (reduceMean 1 x h) i) = (∑ j, get2 x i j) / (em : ℝ) := by
  rw [show reduceMean 1 x h = mapSpec (fun y => y / (em : ℝ)) (reduceSum 1 x h) from rfl,
    reduceSum_one]
  simp only [mapSpec, get_eq, Tensor.toScalar]
  rw [sumSpec_row]

-- ===== Vector (axis-0) reductions, for the variance =====

/-- Axis-0 sum-reduction of a vector is the scalar `sumSpec`. -/
private lemma reduceSum_zero_vec {em : ℕ} (t : Tensor ℝ (.dim em .scalar))
    (h : Shape.reducibleAlong 0 (.dim em .scalar)) :
    reduceSum 0 t h = Tensor.scalar (sumSpec t) := by
  cases t with
  | dim cols => simp only [reduceSum, reduceDim, reduceDim.aux, reduceFirstDim, cast_eq]

/-- `sumSpec` of a vector is the `Finset.sum` of its `vecGet` entries. -/
private lemma sumSpec_vec {em : ℕ} (t : Tensor ℝ (.dim em .scalar)) :
    sumSpec t = ∑ j, vecGet t j := by
  cases t with
  | dim cols =>
    rw [sumSpec_dim]
    apply Finset.sum_congr rfl
    intro j _
    cases hcols : cols j with
    | scalar v => rw [sumSpec_scalar]; simp [vecGet, get_eq, hcols, Tensor.toScalar]

/-- Axis-0 mean-reduction of a vector is the scalar `(sumSpec t)/em`. -/
private lemma reduceMean_zero_vec {em : ℕ} (t : Tensor ℝ (.dim em .scalar))
    (h : Shape.reducibleAlong 0 (.dim em .scalar)) :
    reduceMean 0 t h = Tensor.scalar (sumSpec t / (em : ℝ)) := by
  rw [show reduceMean 0 t h = mapSpec (fun y => y / (em : ℝ)) (reduceSum 0 t h) from rfl,
    reduceSum_zero_vec]
  simp [mapSpec]

-- ===== reduceVar (axis 1) value characterization =====

private lemma vecGet_mapSpec {em : ℕ} (f : ℝ → ℝ) (t : Tensor ℝ (.dim em .scalar)) (j : Fin em) :
    vecGet (mapSpec f t) j = f (vecGet t j) := by
  cases t with
  | dim cols =>
    cases hc : cols j with
    | scalar v => simp [vecGet, get_eq, mapSpec, hc, Tensor.toScalar]

private lemma sumSpec_mapSpec {em : ℕ} (f : ℝ → ℝ) (t : Tensor ℝ (.dim em .scalar)) :
    sumSpec (mapSpec f t) = ∑ j, f (vecGet t j) := by
  rw [sumSpec_vec]
  apply Finset.sum_congr rfl
  intro j _
  rw [vecGet_mapSpec]

private lemma reduceVar_zero_eq {em : ℕ} (t : Tensor ℝ (.dim em .scalar))
    (h : Shape.reducibleAlong 0 (.dim em .scalar)) :
    reduceVar 0 t h = subSpec (reduceMean 0 (mapSpec (fun x => x * x) t) h)
                              (mapSpec (fun x => x * x) (reduceMean 0 t h)) := by
  simp only [reduceVar]

private lemma reduceVar_zero_val {em : ℕ} (t : Tensor ℝ (.dim em .scalar))
    (h : Shape.reducibleAlong 0 (.dim em .scalar)) :
    Tensor.toScalar (reduceVar 0 t h)
      = (∑ j, vecGet t j * vecGet t j) / (em : ℝ)
        - sumSpec t / (em : ℝ) * (sumSpec t / (em : ℝ)) := by
  rw [reduceVar_zero_eq, reduceMean_zero_vec (mapSpec (fun x => x * x) t) h, reduceMean_zero_vec t h,
    sumSpec_mapSpec]
  rfl

private lemma vecGet_getAtSpec {sq em : ℕ} (Y : Tensor ℝ (.dim sq (.dim em .scalar)))
    (i : Fin sq) (j : Fin em) :
    vecGet (getAtSpec Y i) j = get2 Y i j := by
  cases Y with
  | dim rows =>
    cases hr : rows i with
    | dim cols =>
      cases hc : cols j with
      | scalar v => simp [vecGet, get2, get_eq, getAtSpec, hr, hc, Tensor.toScalar]

private lemma reduceVar_one_val {sq em : ℕ} (Y : Tensor ℝ (.dim sq (.dim em .scalar)))
    (h : Shape.reducibleAlong 1 (.dim sq (.dim em .scalar))) (i : Fin sq) :
    Tensor.toScalar (get (reduceVar 1 Y h) i)
      = (∑ j, get2 Y i j * get2 Y i j) / (em : ℝ)
        - (∑ j, get2 Y i j) / (em : ℝ) * ((∑ j, get2 Y i j) / (em : ℝ)) := by
  cases Y with
  | dim rows =>
    have e1 : sumSpec (rows i) = ∑ j, get2 (Tensor.dim rows) i j := sumSpec_row (Tensor.dim rows) i
    have e2 : ∀ j, vecGet (rows i) j = get2 (Tensor.dim rows) i j :=
      fun j => vecGet_getAtSpec (Tensor.dim rows) i j
    have hs : Tensor.toScalar (get (reduceVar 1 (Tensor.dim rows) h) i)
        = Tensor.toScalar (reduceVar 0 (rows i) (by cases h with | tail hi => exact hi)) := rfl
    rw [hs, reduceVar_zero_val, e1]
    simp only [e2]

/-- The variance-shift identity (computational formula): `E[X²] − E[X]² = E[(X − E[X])²]`. -/
private lemma variance_shift {n : ℕ} (a : Fin n → ℝ) :
    (∑ j, a j * a j) / (n : ℝ) - (∑ j, a j) / (n : ℝ) * ((∑ j, a j) / (n : ℝ))
      = (∑ j, (a j - (∑ k, a k) / (n : ℝ)) ^ 2) / (n : ℝ) := by
  have key : (∑ j, (a j - (∑ k, a k) / (n : ℝ)) ^ 2)
      = (∑ j, a j * a j) - 2 * ((∑ k, a k) / (n : ℝ)) * (∑ j, a j)
        + (n : ℝ) * ((∑ k, a k) / (n : ℝ)) ^ 2 := by
    have h1 : ∀ j, (a j - (∑ k, a k) / (n : ℝ)) ^ 2
        = a j * a j - 2 * ((∑ k, a k) / (n : ℝ)) * a j + ((∑ k, a k) / (n : ℝ)) ^ 2 :=
      fun j => by ring
    simp_rw [h1]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [key]
  rcases eq_or_ne (n : ℝ) 0 with hn | hn
  · rw [hn]; simp
  · field_simp; ring

/-- The spec per-row variance equals the coordinate (centered) variance `(∑ⱼ(Xᵢⱼ − meanᵢ)²)/em`. -/
private lemma reduceVar_one_rowVar {sq em : ℕ} (Y : Tensor ℝ (.dim sq (.dim em .scalar)))
    (h : Shape.reducibleAlong 1 (.dim sq (.dim em .scalar))) (i : Fin sq) :
    Tensor.toScalar (get (reduceVar 1 Y h) i)
      = (∑ j, (get2 Y i j - (∑ k, get2 Y i k) / (em : ℝ)) ^ 2) / (em : ℝ) := by
  rw [reduceVar_one_val, variance_shift (fun j => get2 Y i j)]

-- ===== elementwise get2 pushes (rank-2) =====

private lemma get2_mapSpec {m n : ℕ} (f : ℝ → ℝ)
    (A : Tensor ℝ (.dim m (.dim n .scalar))) (i : Fin m) (j : Fin n) :
    get2 (mapSpec f A) i j = f (get2 A i j) := by
  cases A with
  | dim rows =>
    cases hrows : rows i with
    | dim cols =>
      cases hcols : cols j with
      | scalar v => simp [get2, get_eq, mapSpec, hrows, hcols]

private lemma get2_map2Spec {m n : ℕ} {β γ : Type} (f : ℝ → β → γ)
    (A : Tensor ℝ (.dim m (.dim n .scalar))) (B : Tensor β (.dim m (.dim n .scalar)))
    (i : Fin m) (j : Fin n) :
    get2 (map2Spec f A B) i j = f (get2 A i j) (get2 B i j) := by
  cases A with
  | dim rowsA =>
    cases B with
    | dim rowsB =>
      cases hA : rowsA i with
      | dim colsA =>
        cases hB : rowsB i with
        | dim colsB =>
          cases hcA : colsA j with
          | scalar vA =>
            cases hcB : colsB j with
            | scalar vB => simp [get2, get_eq, map2Spec, hA, hB, hcA, hcB]

private lemma get2_subSpec {m n : ℕ} (A B : Tensor ℝ (.dim m (.dim n .scalar))) (i : Fin m) (j : Fin n) :
    get2 (subSpec A B) i j = get2 A i j - get2 B i j := by
  simp only [subSpec, get2_map2Spec]

private lemma get2_mulSpec {m n : ℕ} (A B : Tensor ℝ (.dim m (.dim n .scalar))) (i : Fin m) (j : Fin n) :
    get2 (mulSpec A B) i j = get2 A i j * get2 B i j := by
  simp only [mulSpec, get2_map2Spec]

private lemma get2_divSpec {m n : ℕ} (A B : Tensor ℝ (.dim m (.dim n .scalar))) (i : Fin m) (j : Fin n) :
    get2 (divSpec A B) i j = get2 A i j / get2 B i j := by
  simp only [divSpec, get2_map2Spec]

private lemma get2_broadcast_row {sq em : ℕ} (v : Tensor ℝ (.dim sq .scalar))
    (i : Fin sq) (j : Fin em) :
    get2 (broadcastTo (Shape.CanBroadcastTo.dim_eq (Shape.CanBroadcastTo.expand_dims
      (Shape.CanBroadcastTo.scalar_to_any .scalar))
        : Shape.CanBroadcastTo (.dim sq .scalar) (.dim sq (.dim em .scalar))) v) i j
      = vecGet v i := by
  cases v with
  | dim xs =>
    cases hx : xs i with
    | scalar w => simp [get2, get_eq, broadcastTo, replicate, vecGet, hx, Tensor.toScalar]

private lemma get2_broadcast_col {sq em : ℕ} (v : Tensor ℝ (.dim em .scalar))
    (i : Fin sq) (j : Fin em) :
    get2 (broadcastTo (Shape.CanBroadcastTo.expand_dims (Shape.CanBroadcastTo.dim_eq
      (Shape.CanBroadcastTo.scalar_to_any .scalar))
        : Shape.CanBroadcastTo (.dim em .scalar) (.dim sq (.dim em .scalar))) v) i j
      = vecGet v j := by
  cases v with
  | dim cols =>
    cases hc : cols j with
    | scalar w => simp [get2, get_eq, broadcastTo, replicate, vecGet, hc, Tensor.toScalar]

-- ===== vector (rank-1) get pushes, for the std vector =====

private lemma vecGet_map2Spec {n : ℕ} {β γ : Type} (f : ℝ → β → γ)
    (A : Tensor ℝ (.dim n .scalar)) (B : Tensor β (.dim n .scalar)) (i : Fin n) :
    vecGet (map2Spec f A B) i = f (vecGet A i) (vecGet B i) := by
  cases A with
  | dim colsA =>
    cases B with
    | dim colsB =>
      cases hA : colsA i with
      | scalar a =>
        cases hB : colsB i with
        | scalar b => simp [vecGet, get_eq, map2Spec, hA, hB, Tensor.toScalar]

private lemma vecGet_addSpec {n : ℕ} (A B : Tensor ℝ (.dim n .scalar)) (i : Fin n) :
    vecGet (addSpec A B) i = vecGet A i + vecGet B i := by
  simp only [addSpec, vecGet_map2Spec]

private lemma vecGet_maxSpec {n : ℕ} (A B : Tensor ℝ (.dim n .scalar)) (i : Fin n) :
    vecGet (maxSpec A B) i = max (vecGet A i) (vecGet B i) := by
  simp only [maxSpec, vecGet_map2Spec]

private lemma vecGet_fill {n : ℕ} (v : ℝ) (i : Fin n) :
    vecGet (fill v (.dim n .scalar)) i = v := by
  simp [vecGet, get_eq, fill, Tensor.toScalar]

private lemma vecGet_sqrtSpec {n : ℕ} (A : Tensor ℝ (.dim n .scalar)) (i : Fin n) :
    vecGet (sqrtSpec A) i = MathFunctions.sqrt (max (vecGet A i) 0) := by
  simp only [sqrtSpec, vecGet_mapSpec]

-- ===== whole-statistic reconciliations and the layer-norm coordinate bridge =====

/-- Row `i` of the spec last-axis mean reduction equals the coordinate row-mean `(∑ⱼ Xᵢⱼ)/em`. -/
private lemma reduceMeanLastGeneralWf_vecGet {sq em : ℕ}
    [Shape.WellFormed (Shape.dim sq (Shape.dim em Shape.scalar))]
    (Y : Tensor ℝ (.dim sq (.dim em .scalar)))
    (hr : Shape.rank (.dim sq (.dim em .scalar)) > 0)
    (hv : Shape.valid_axis_inst (Shape.rank (.dim sq (.dim em .scalar)) - 1) (.dim sq (.dim em .scalar)))
    (i : Fin sq) :
    Tensor.vecGet (reduceMeanLastGeneralWf Y hr hv) i = rowMeanCoord i (matCoords Y) := by
  rw [rowMeanCoord]; simp only [matCoords]; exact reduceMean_one_val Y _ i

/-- Row `i` of the spec last-axis variance reduction equals the coordinate row-variance
`(∑ⱼ(Xᵢⱼ − meanᵢ)²)/em`. -/
private lemma reduceVarLastGeneral_vecGet {sq em : ℕ} (C : Tensor ℝ (.dim sq (.dim em .scalar)))
    (inst : Shape.valid_axis_inst (Shape.rank (.dim sq (.dim em .scalar)) - 1) (.dim sq (.dim em .scalar)))
    (i : Fin sq) :
    Tensor.vecGet (reduceVarLastGeneral C inst) i = rowVarCoord i (matCoords C) := by
  rw [rowVarCoord]; simp only [matCoords, rowMeanCoord]; exact reduceVar_one_rowVar C _ i

/-- Centering each row by its own mean leaves the row variance unchanged: the mean of the centered
row is zero, so `var(X − mean X) = var X`. -/
private lemma rowVarCoord_of_centered {sq em : ℕ} (X : Fin sq → Fin em → ℝ) (i : Fin sq) :
    rowVarCoord i (fun i' k => X i' k - rowMeanCoord i' X) = rowVarCoord i X := by
  have hmean0 : rowMeanCoord i (fun i' k => X i' k - rowMeanCoord i' X) = 0 := by
    unfold rowMeanCoord
    rcases eq_or_ne (em : ℝ) 0 with h | h
    · simp [h]
    · rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp; ring
  unfold rowVarCoord; rw [hmean0]; simp

/-- The coordinates of the layer-norm centered tensor `x − broadcast(rowmean x)` are the entrywise
centered coordinates `Xᵢⱼ − meanᵢ`. -/
private lemma matCoords_centered_eq {sq em : ℕ}
    [Shape.WellFormed (Shape.dim sq (Shape.dim em Shape.scalar))]
    (Y : Tensor ℝ (.dim sq (.dim em .scalar)))
    {hr : Shape.rank (.dim sq (.dim em .scalar)) > 0}
    {hv : Shape.valid_axis_inst (Shape.rank (.dim sq (.dim em .scalar)) - 1) (.dim sq (.dim em .scalar))} :
    matCoords (subSpec Y (broadcastTo (Shape.CanBroadcastTo.dim_eq (Shape.CanBroadcastTo.expand_dims
      (Shape.CanBroadcastTo.scalar_to_any .scalar))
        : Shape.CanBroadcastTo (.dim sq .scalar) (.dim sq (.dim em .scalar)))
      (reduceMeanLastGeneralWf Y hr hv)))
      = fun i' k => matCoords Y i' k - rowMeanCoord i' (matCoords Y) := by
  funext i' k
  simp only [matCoords, get2_subSpec, get2_broadcast_row, reduceMeanLastGeneralWf_vecGet]

/-- **The layer-norm coordinate bridge.** Entry `(i, j)` of the literal spec op-tree
`Spec.layerNorm` equals the coordinate model `layerNormCoordEps`:
`(Xᵢⱼ − meanᵢ)/√(max(varᵢ, 0) + ε)·γⱼ + βⱼ`, where `meanᵢ`/`varᵢ` are the per-row statistics of
`matCoords Y`. Centering before the variance makes the std vector reconcile to `rowStdCoordEps`
(the centered-row variance equals the raw-row variance). This is the bridge that transports
continuity and measurability of the coordinate model to the literal layer-norm operation. -/
theorem get2_layerNorm {sq em : ℕ} (Y : Tensor ℝ (.dim sq (.dim em .scalar)))
    (γ β : Tensor ℝ (.dim em .scalar)) (hseq : sq > 0) (hemb : em > 0) (ε : ℝ) (hε : 0 ≤ ε)
    (i : Fin sq) (j : Fin em) :
    get2 (Spec.layerNorm Y γ β hseq hemb ε) i j
      = layerNormCoordEps ε (fun j => vecGet γ j) (fun j => vecGet β j) (matCoords Y) i j := by
  simp only [Spec.layerNorm, get2_addSpec, get2_mulSpec, get2_divSpec, get2_subSpec,
    get2_broadcast_row, get2_broadcast_col, reduceMeanLastGeneralWf_vecGet]
  dsimp only [Shape.rank, shapeAfterSum]
  rw [vecGet_sqrtSpec, vecGet_addSpec, vecGet_maxSpec, vecGet_fill, vecGet_fill,
    reduceVarLastGeneral_vecGet]
  simp only [matCoords_centered_eq, rowVarCoord_of_centered]
  rw [max_eq_left (add_nonneg (le_max_right _ _) hε)]
  simp only [layerNormCoordEps, rowStdCoordEps, matCoords]
  rfl

-- ===== continuity and measurability of the literal layer-norm op =====

/-- Round-trip: the coordinates of a `matrixTensor` recover the input function. -/
private lemma matCoords_matrixTensor {m n : ℕ} (X : Fin m → Fin n → ℝ) :
    matCoords (matrixTensor X) = X := by
  funext i j
  simp only [matCoords, get2_matrixTensor]

/-- The coordinate layer-normalization map with regularizer `ε` is continuous whenever `ε > 0`: the
denominator `rowStdCoordEps ε i X = √(max(varᵢ, 0) + ε) ≥ √ε > 0` never vanishes. (At `ε = 0` it is
only measurable, not continuous — the division is unguarded at the constant-input locus.) -/
theorem continuous_layerNormCoordEps {s d : ℕ} (ε : ℝ) (hε : 0 < ε) (γ β : Fin d → ℝ) :
    Continuous (layerNormCoordEps (s := s) ε γ β) := by
  unfold layerNormCoordEps
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  refine ((Continuous.div ((continuous_apply_apply i j).sub (continuous_rowMeanCoord i))
    (continuous_rowStdCoordEps ε i) (fun X => ?_)).mul continuous_const).add continuous_const
  rw [rowStdCoordEps]
  exact ne_of_gt (Real.sqrt_pos.mpr (by have := le_max_right (rowVarCoord i X) (0 : ℝ); linarith))

/-- The literal layer-norm op `Spec.layerNorm`, read in coordinates as a function of its input,
equals the coordinate model `layerNormCoordEps` (for every regularizer `ε ≥ 0`). -/
private lemma matCoords_layerNorm_eq {sq em : ℕ} (γ β : Tensor ℝ (.dim em .scalar))
    (hseq : sq > 0) (hemb : em > 0) (ε : ℝ) (hε : 0 ≤ ε) :
    (fun X : Fin sq → Fin em → ℝ => matCoords (Spec.layerNorm (matrixTensor X) γ β hseq hemb ε))
      = layerNormCoordEps ε (fun j => vecGet γ j) (fun j => vecGet β j) := by
  funext X i j
  show get2 (Spec.layerNorm (matrixTensor X) γ β hseq hemb ε) i j
     = layerNormCoordEps ε (fun j => vecGet γ j) (fun j => vecGet β j) X i j
  rw [get2_layerNorm (hε := hε), matCoords_matrixTensor]

/-- **The literal layer-norm op is measurable for every regularizer `ε ≥ 0`.** The unguarded division
in `Spec.layerNorm` is Borel (`Measurable.div` needs no nonzero hypothesis), so measurability holds
even at `ε = 0`, where the op is discontinuous at the constant-input locus. -/
theorem measurable_matCoords_layerNorm {sq em : ℕ} (γ β : Tensor ℝ (.dim em .scalar))
    (hseq : sq > 0) (hemb : em > 0) (ε : ℝ) (hε : 0 ≤ ε) :
    Measurable (fun X : Fin sq → Fin em → ℝ =>
      matCoords (Spec.layerNorm (matrixTensor X) γ β hseq hemb ε)) := by
  rw [matCoords_layerNorm_eq γ β hseq hemb ε hε]
  exact measurable_layerNormCoordEps ε _ _

/-- **The literal layer-norm op is continuous for every strict regularizer `ε > 0`.** Mirrors
`measurable_matCoords_layerNorm`: continuity is the regularizer-gated property (the denominator is
bounded away from zero by `√ε`), measurability is the regularizer-free invariant. -/
theorem continuous_matCoords_layerNorm {sq em : ℕ} (γ β : Tensor ℝ (.dim em .scalar))
    (hseq : sq > 0) (hemb : em > 0) (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun X : Fin sq → Fin em → ℝ =>
      matCoords (Spec.layerNorm (matrixTensor X) γ β hseq hemb ε)) := by
  rw [matCoords_layerNorm_eq γ β hseq hemb ε hε.le]
  exact continuous_layerNormCoordEps ε hε _ _
