/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Spec.ScaledDotProductAttentionCorrespondence

/-!
# Binding the literal TorchLean transformer encoder layer

The capacity stack (`TransformerStackCertificate`) uses single-head parameter-free self-attention
`selfAttn`; TorchLean's `TransformerEncoderLayer.forward` uses the multi-head `MultiHeadAttention.forward`.
At the canonical single-head configuration (one head, identity query/key/value/output projections),
the multi-head op reduces in coordinates to the single scaled-dot-product attention already bound by
`matCoords_scaledDotProductAttention`, hence to `selfAttn`.

The reduction routes through TorchLean's tensor-reshape machinery (`splitHeadsSpec`, `combineHeadsSpec`
= `reshapeSpec` = `unflattenSpec ∘ flattenSpec`), discharged with the round-trip
`Spec.Tensor.flatten_unflatten_inverse`.

## Main results

- `matMulCoord_id`: the identity matrix is the unit of the coordinate matrix-multiply.
-/

/-!
## References
- [27] §3.2.2 multi-head (h=1 special case, identity projections, split/combine-heads reshape);
  [53] `MultiHeadAttention.forward`, `splitHeadsSpec`/`combineHeadsSpec`/`reshapeSpec`.
-/

open Spec

noncomputable section

namespace TLT

variable {s d : ℕ}

/-- **The identity matrix is the unit of `matMulCoord`.** With `W k j = [k = j]`, the contracted
product `∑ₖ Xᵢₖ·Wₖⱼ` collapses to `Xᵢⱼ`. This is the coordinate content of the identity
query/key/value/output projections in the single-head reduction of multi-head attention. -/
lemma matMulCoord_id (X : Fin s → Fin d → ℝ) :
    matMulCoord (fun k j => if k = j then (1 : ℝ) else 0) X = X := by
  funext i j
  simp only [matMulCoord]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj; simp [if_neg hkj]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The `d × d` identity matrix as a literal tensor: the canonical query/key/value/output projection
that makes `selfAttention` parameter-free. -/
def idTensorM (d : ℕ) : Tensor ℝ (.dim d (.dim d .scalar)) :=
  matrixTensor (fun k j => if k = j then (1 : ℝ) else 0)

/-- **Matrix-tensor extensionality.** Two matrix-shaped scalar tensors agreeing in every coordinate
read `get2` are equal: this lifts a coordinate identity (`matCoords … = …`) to a tensor
identity (needed to feed `matCoords_scaledDotProductAttention`'s `ctx.Q = matrixTensor …` hypotheses). -/
lemma get2_ext {m n : ℕ} : ∀ {x y : Tensor ℝ (.dim m (.dim n .scalar))},
    (∀ i j, get2 x i j = get2 y i j) → x = y
  | Tensor.dim fx, Tensor.dim fy, h => by
    refine congrArg Tensor.dim (funext fun i => ?_)
    have hi : ∀ j, get2 (Tensor.dim fx) i j = get2 (Tensor.dim fy) i j := fun j => h i j
    cases hx : fx i with
    | dim gx =>
      cases hy : fy i with
      | dim gy =>
        refine congrArg Tensor.dim (funext fun j => ?_)
        have hij := hi j
        cases hgx : gx j with
        | scalar vx =>
          cases hgy : gy j with
          | scalar vy =>
            simp only [get2, get_eq, hx, hy, hgx, hgy] at hij
            rw [hij]

/-- **The literal matrix-multiply of two `matrixTensor`s, at the tensor level, is `matMulCoord`.** The
tensor-valued companion of `matCoords_matMulSpec`, obtained by `get2`-extensionality; the literal
op `matMulSpec (matrixTensor X) (matrixTensor W)` *is* `matrixTensor (matMulCoord W X)`, not merely
equal in coordinates. -/
lemma matMulSpec_matrixTensor {s d e : ℕ} (X : Fin s → Fin d → ℝ) (W : Fin d → Fin e → ℝ) :
    matMulSpec (matrixTensor X) (matrixTensor W) = matrixTensor (matMulCoord W X) := by
  refine get2_ext (fun i j => ?_)
  rw [get2_mat_mul_spec, get2_matrixTensor]
  simp only [matMulCoord, get2_matrixTensor]

/-- **The identity matrix tensor is the right unit of the literal matrix-multiply, for any tensor.**
`matMulSpec t I = t`: the literal content of an identity query/key/value/output projection, applied
to *any* tensor (both `t = matrixTensor X` for the input projections and `t = scaledDotProductAttention …`
for the output projection). -/
lemma matMulSpec_id_right {m d : ℕ} (t : Tensor ℝ (.dim m (.dim d .scalar))) :
    matMulSpec t (matrixTensor (fun k j : Fin d => if k = j then (1 : ℝ) else 0)) = t := by
  refine get2_ext (fun i j => ?_)
  rw [get2_mat_mul_spec]
  simp only [get2_matrixTensor]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj; simp [if_neg hkj]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **TorchLean's literal `selfAttention`, at identity projections, is `selfAttn` in coordinates.**
With identity query/key/value/output projections, the literal op
`matMulSpec (scaledDotProductAttention {Q,K,V := X}) I` reads coordinatewise as the capacity
model's parameter-free single-head self-attention `selfAttn √d X`. `selfAttention` is documented in
TorchLean as "the core of `nn.MultiheadAttention` / `TransformerEncoderLayer`"; the identity
projections collapse via `matMulSpec_id_right` and the inner attention is `scaledDotProductAttention`,
which is already bound by `matCoords_scaledDotProductAttention`. -/
theorem matCoords_selfAttention_id {n d : ℕ} (X : Fin (n + 1) → Fin d → ℝ) :
    matCoords (Spec.selfAttention (matrixTensor X)
        (idTensorM d) (idTensorM d) (idTensorM d) (idTensorM d) (Nat.succ_ne_zero n))
      = selfAttn (MathFunctions.sqrt (d : ℝ)) X := by
  simp only [Spec.selfAttention, idTensorM, matMulSpec_id_right]
  rw [matCoords_scaledDotProductAttention X (fun k j => if k = j then (1 : ℝ) else 0)
        _ rfl rfl (by rw [matMulCoord_id]) rfl]
  funext i
  simp only [attnHead, selfAttn, matMulCoord_id]

/-! ### Reshape is flat-content-preserving (the lever for the multi-head reshapes) -/

/-- **`flatten ∘ reshape = cast ∘ flatten`.** The defining identity `reshapeSpec t h =
unflatten s₂ (h ▸ flatten t)` composed with `flatten ∘ unflatten = id` collapses to: flattening a
reshape recovers the cast of the flattened original. This dissolves the cross-shape `Eq.recOn` on
*tensors* into a single transport on a flat vector `(.dim N .scalar)`, where the only residual cast is
a `Fin N` reindex, the structure that makes the `splitHeads`/`combineHeads` reshapes tractable. -/
lemma flattenSpec_reshapeSpec {α : Type} [Inhabited α] {s₁ s₂ : Spec.Shape}
    (t : Tensor α s₁) (h : s₁.size = s₂.size) :
    Spec.Tensor.flattenSpec (Spec.Tensor.reshapeSpec t h) = h ▸ Spec.Tensor.flattenSpec t := by
  simp only [Spec.Tensor.reshapeSpec]
  rw [Spec.Tensor.unflatten_flatten_inverse]

/-- **`flattenSpec` is injective.** Immediate from `unflatten ∘ flatten = id`: a tensor is recovered
from its flattening. Paired with `flattenSpec_reshapeSpec`, this reduces every reshape *tensor*
equality to a flat-vector equality; no `unflattenSpec` coordinate read is required. -/
lemma flattenSpec_injective {α : Type} [Inhabited α] {s : Spec.Shape} {x y : Tensor α s}
    (h : Spec.Tensor.flattenSpec x = Spec.Tensor.flattenSpec y) : x = y := by
  rw [← Spec.Tensor.flatten_unflatten_inverse x, ← Spec.Tensor.flatten_unflatten_inverse y, h]

/-- **A tensor is recovered from a flat vector by reshape, given the flattens agree.** `x = reshape t h`
whenever `flatten x = h ▸ flatten t`, the converse of `flattenSpec_reshapeSpec`, via injectivity. -/
lemma eq_reshapeSpec_of_flatten {α : Type} [Inhabited α] {s₁ s₂ : Spec.Shape}
    {x : Tensor α s₂} {t : Tensor α s₁} (h : s₁.size = s₂.size)
    (hf : Spec.Tensor.flattenSpec x = h ▸ Spec.Tensor.flattenSpec t) :
    x = Spec.Tensor.reshapeSpec t h := by
  apply flattenSpec_injective
  rw [flattenSpec_reshapeSpec]; exact hf

/-! ### Reading a flat vector through a size cast: the `Fin`-reindex (the general reshape read) -/

/-- **Reading a transported flat vector is reading at the `Fin`-cast index.** The `Eq.recOn` cast over a
size equality `N₁ = N₂` (the cast `reshapeSpec` carries) collapses under `cases`, leaving only a `Fin`
reindex; `1*d`-vs-`d` non-definitional-equality never touches a *tensor*, only an index. -/
lemma vecGet_eqRec {N₁ N₂ : ℕ} (h : N₁ = N₂) (v : Tensor ℝ (.dim N₁ .scalar)) (k : Fin N₂) :
    Spec.Tensor.vecGet (h ▸ v) k = Spec.Tensor.vecGet v (Fin.cast h.symm k) := by
  cases h; rfl

/-- **The general reshape coordinate read.** `reshapeSpec` reads, entrywise, as the original flattened
tensor at the `Fin`-cast index: `vecGet (flatten (reshape t h)) k = vecGet (flatten t) (Fin.cast h.symm k)`.
The lever turns the tensor reshape into a flat-vector cast; `vecGet_eqRec` turns the cast into a `Fin`
reindex. This is the reusable infrastructure for `splitHeads`/`combineHeads` at any head count. -/
lemma vecGet_flattenSpec_reshapeSpec {s₁ s₂ : Spec.Shape}
    (t : Tensor ℝ s₁) (h : s₁.size = s₂.size) (k : Fin s₂.size) :
    Spec.Tensor.vecGet (Spec.Tensor.flattenSpec (Spec.Tensor.reshapeSpec t h)) k
      = Spec.Tensor.vecGet (Spec.Tensor.flattenSpec t) (Fin.cast h.symm k) := by
  rw [flattenSpec_reshapeSpec]
  exact vecGet_eqRec h (Spec.Tensor.flattenSpec t) k

open Spec.Tensor in
/-- The flatten coordinate read (the `dim` case): flattening `Tensor.dim f` and reading flat index
`i·|s| + j` recovers `f i` flattened at `j`. Re-derived for our pin with the
`cases (flattenSpec (f i))` technique that makes the inner-tensor match reduce. -/
lemma flattenSpec_dim_apply {α : Type} [Inhabited α] {n : Nat} {s : Spec.Shape}
    (f : Fin n → Tensor α s) (i : Fin n) (j : Fin (Spec.Shape.size s))
    (hmpos : 0 < Spec.Shape.size s)
    (hidx : i.val * Spec.Shape.size s + j.val < n * Spec.Shape.size s) :
    (match flattenSpec (Tensor.dim f) with
      | Tensor.dim g => g ⟨i.val * Spec.Shape.size s + j.val, hidx⟩) =
    (match flattenSpec (f i) with
      | Tensor.dim g => g j) := by
  have hdiv : (i.val * Spec.Shape.size s + j.val) / Spec.Shape.size s = i.val := by
    calc (i.val * Spec.Shape.size s + j.val) / Spec.Shape.size s
          = (Spec.Shape.size s * i.val + j.val) / Spec.Shape.size s := by simp [Nat.mul_comm]
      _ = i.val + j.val / Spec.Shape.size s := by
            simpa using (Nat.mul_add_div (m := Spec.Shape.size s) hmpos i.val j.val)
      _ = i.val := by simp [Nat.div_eq_of_lt j.isLt]
  have hmod : (i.val * Spec.Shape.size s + j.val) % Spec.Shape.size s = j.val :=
    Nat.mul_add_mod_of_lt (a := i.val) (b := Spec.Shape.size s) (c := j.val) j.isLt
  have houter : (i.val * Spec.Shape.size s + j.val) / Spec.Shape.size s < n := by simp [hdiv]
  have hfin_outer :
      (⟨(i.val * Spec.Shape.size s + j.val) / Spec.Shape.size s, houter⟩ : Fin n) = i := by
    apply Fin.ext; simp [hdiv]
  cases hfi : flattenSpec (f i) with
  | dim gfi => simp [flattenSpec, hfi, hdiv, hmod]

open Spec.Tensor in
/-- `vecGet` form of the flatten coordinate read (what `vecTensor_ext` consumes). -/
lemma vecGet_flattenSpec_dim {α : Type} [Inhabited α] {n : Nat} {s : Spec.Shape}
    (f : Fin n → Tensor α s) (i : Fin n) (j : Fin (Spec.Shape.size s))
    (hmpos : 0 < Spec.Shape.size s)
    (hidx : i.val * Spec.Shape.size s + j.val < n * Spec.Shape.size s) :
    Spec.Tensor.vecGet (flattenSpec (Tensor.dim f))
        ⟨i.val * Spec.Shape.size s + j.val, hidx⟩
      = Spec.Tensor.vecGet (flattenSpec (f i)) j := by
  have hdiv : (i.val * Spec.Shape.size s + j.val) / Spec.Shape.size s = i.val := by
    calc (i.val * Spec.Shape.size s + j.val) / Spec.Shape.size s
          = (Spec.Shape.size s * i.val + j.val) / Spec.Shape.size s := by simp [Nat.mul_comm]
      _ = i.val + j.val / Spec.Shape.size s := by
            simpa using (Nat.mul_add_div (m := Spec.Shape.size s) hmpos i.val j.val)
      _ = i.val := by simp [Nat.div_eq_of_lt j.isLt]
  have hmod : (i.val * Spec.Shape.size s + j.val) % Spec.Shape.size s = j.val :=
    Nat.mul_add_mod_of_lt (a := i.val) (b := Spec.Shape.size s) (c := j.val) j.isLt
  cases hfi : flattenSpec (f i) with
  | dim gfi => simp [Spec.Tensor.vecGet, flattenSpec, hfi, hdiv, hmod, get_eq]

open Spec.Tensor in
/-- The flatten read with a general flat index, decomposed by `÷`/`%`. -/
lemma vecGet_flattenSpec_dim' {α : Type} [Inhabited α] {n : Nat} {s : Spec.Shape}
    (hpos : 0 < Spec.Shape.size s) (f : Fin n → Tensor α s) (k : Fin (n * Spec.Shape.size s)) :
    Spec.Tensor.vecGet (flattenSpec (Tensor.dim f)) k
      = Spec.Tensor.vecGet (flattenSpec
          (f ⟨k.val / Spec.Shape.size s, (Nat.div_lt_iff_lt_mul hpos).mpr k.isLt⟩))
          ⟨k.val % Spec.Shape.size s, Nat.mod_lt _ hpos⟩ := by
  have hkdm : k.val / Spec.Shape.size s * Spec.Shape.size s + k.val % Spec.Shape.size s = k.val := by
    conv_rhs => rw [← Nat.div_add_mod k.val (Spec.Shape.size s), Nat.mul_comm (Spec.Shape.size s)]
  have hidx : k.val / Spec.Shape.size s * Spec.Shape.size s + k.val % Spec.Shape.size s
      < n * Spec.Shape.size s := lt_of_eq_of_lt hkdm k.isLt
  have key := vecGet_flattenSpec_dim f
    ⟨k.val / Spec.Shape.size s, (Nat.div_lt_iff_lt_mul hpos).mpr k.isLt⟩
    ⟨k.val % Spec.Shape.size s, Nat.mod_lt _ hpos⟩ hpos hidx
  convert key using 2
  apply Fin.ext; exact hkdm.symm

/-- **Vector-tensor extensionality.** Two `Tensor ℝ (.dim N .scalar)` agreeing in every `vecGet` are
equal: this lifts a flat-vector coordinate identity to a tensor identity. -/
lemma vecTensor_ext {N : ℕ} : ∀ {x y : Tensor ℝ (.dim N .scalar)},
    (∀ k, Spec.Tensor.vecGet x k = Spec.Tensor.vecGet y k) → x = y
  | Tensor.dim gx, Tensor.dim gy, h => by
    refine congrArg Tensor.dim (funext fun k => ?_)
    have hk := h k
    cases hgx : gx k with
    | scalar vx =>
      cases hgy : gy k with
      | scalar vy =>
        simp only [Spec.Tensor.vecGet, get_eq, hgx, hgy, Tensor.toScalar] at hk
        rw [hk]

/-- **`matrixTensor ∘ matCoords = id`.** The reverse round-trip: a matrix tensor is recovered from its
coordinate reading. By `get2`-extensionality and `get2_matrixTensor`. -/
lemma matrixTensor_matCoords {n m : ℕ} (T : Tensor ℝ (.dim n (.dim m .scalar))) :
    matrixTensor (matCoords T) = T := by
  refine get2_ext (fun i j => ?_)
  simp only [get2_matrixTensor, matCoords]

/-- The flatten read specialised to a single (`Fin 1`) outer dimension. -/
lemma vecGet_flattenSpec_single {α : Type} [Inhabited α] {s : Spec.Shape}
    (hpos : 0 < Spec.Shape.size s) (u : Tensor α s)
    (k : Fin (Spec.Shape.size (Spec.Shape.dim 1 s))) :
    Spec.Tensor.vecGet (Spec.Tensor.flattenSpec (Tensor.dim (fun _ : Fin 1 => u))) k
      = Spec.Tensor.vecGet (Spec.Tensor.flattenSpec u) (Fin.cast (Nat.one_mul _) k) := by
  have hkv : k.val < Spec.Shape.size s := by
    have h := k.isLt; simp only [Spec.Shape.size, Nat.one_mul] at h; exact h
  have hidx : (0 : Fin 1).val * Spec.Shape.size s + (⟨k.val, hkv⟩ : Fin (Spec.Shape.size s)).val
      < 1 * Spec.Shape.size s := by simpa using hkv
  have key := vecGet_flattenSpec_dim (fun _ : Fin 1 => u) 0 ⟨k.val, hkv⟩ hpos hidx
  simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add] at key
  convert key using 2

open Spec in
/-- **Split-heads at numHeads = 1 is the single-wrapped reshape.** Extracting head 0 of
`splitHeadsSpec I 1 d` recovers `I` reshaped to the per-head `(n, d)`, the fact that reduces the
multi-head `match` to single-head self-attention. Proven by `flattenSpec_injective` + the reshape and
single reads, where every cast is a `Fin`-reindex preserving `.val`. -/
lemma splitHeadsSpec_one {n d : ℕ} (hpos : 0 < (Shape.dim n (.dim d .scalar)).size)
    (I : Tensor ℝ (.dim n (.dim (1 * d) .scalar)))
    (hsplit : (Shape.dim n (.dim (1 * d) .scalar)).size = (Shape.dim n (.dim d .scalar)).size) :
    splitHeadsSpec I 1 d rfl = Tensor.dim (fun _ : Fin 1 => Spec.Tensor.reshapeSpec I hsplit) := by
  apply flattenSpec_injective
  apply vecTensor_ext
  intro k
  simp only [splitHeadsSpec]
  rw [vecGet_flattenSpec_reshapeSpec,
    vecGet_flattenSpec_single hpos (u := Spec.Tensor.reshapeSpec I hsplit),
    vecGet_flattenSpec_reshapeSpec]
  refine congrArg (Spec.Tensor.vecGet (Spec.Tensor.flattenSpec I)) ?_
  apply Fin.ext
  simp

open Spec in
/-- **Combine-heads at numHeads = 1 is the reshape of the single head.** `combineHeadsSpec (single S)`
recovers `S` reshaped to `(n, 1*d)`, the output-side dual of `splitHeadsSpec_one`. The swap at
numHeads = 1 is flat-preserving; proven by `eq_reshapeSpec_of_flatten` + the lever + the nested
flatten reads, every cast a `.val`-preserving `Fin`-reindex. -/
lemma combineHeadsSpec_one {n d : ℕ} (hd : 0 < d) (S : Tensor ℝ (.dim n (.dim d .scalar)))
    (hcomb : (Shape.dim n (.dim d .scalar)).size = (Shape.dim n (.dim (1 * d) .scalar)).size) :
    combineHeadsSpec (Tensor.dim (fun _ : Fin 1 => S)) = Spec.Tensor.reshapeSpec S hcomb := by
  have hps : 0 < (Shape.dim d Shape.scalar).size := by simpa [Shape.size] using hd
  have hps1 : 0 < (Shape.dim 1 (Shape.dim d Shape.scalar)).size := by simpa [Shape.size] using hd
  cases S with
  | dim Srows =>
    apply eq_reshapeSpec_of_flatten
    simp only [combineHeadsSpec, Spec.Tensor.swapFirstTwoSpec]
    rw [flattenSpec_reshapeSpec]
    apply vecTensor_ext
    intro k
    simp only [vecGet_eqRec]
    rw [vecGet_flattenSpec_dim' hps1, vecGet_flattenSpec_single hps, vecGet_flattenSpec_dim' hps]
    refine congrArg₂ (fun t i => Spec.Tensor.vecGet (Spec.Tensor.flattenSpec t) i) ?_ ?_
    · congr 1; apply Fin.ext; simp [Shape.size, Nat.one_mul]
    · apply Fin.ext; simp [Shape.size, Nat.one_mul]

open Spec in
/-- **The literal multi-head attention forward at numHeads = 1 with identity projections is the reshape
of single-head self-attention.** `MultiHeadAttention.forward` (the op `TransformerEncoderLayer.forward`
calls) reduces, through `splitHeadsSpec_one`, `combineHeadsSpec_one`, and the identity-projection
collapse `matMulSpec_id_right`, to a reshape of `scaledDotProductAttention` applied to the per-head view
of the input. Composed with `matCoords_scaledDotProductAttention`, the literal multi-head op equals the
certified `selfAttn` up to a reshape, with no additional pathology. -/
theorem multiHeadAttention_forward_one {n d : ℕ}
    (hsplit : (Shape.dim (n + 1) (.dim (1 * d) .scalar)).size
      = (Shape.dim (n + 1) (.dim d .scalar)).size)
    (hcomb : (Shape.dim (n + 1) (.dim d .scalar)).size
      = (Shape.dim (n + 1) (.dim (1 * d) .scalar)).size) (hd : 0 < d)
    (x : Tensor ℝ (.dim (n + 1) (.dim (1 * d) .scalar))) :
    MultiHeadAttention.forward (n + 1) (Nat.succ_ne_zero n)
        ⟨idTensorM (1 * d), idTensorM (1 * d), idTensorM (1 * d), idTensorM (1 * d)⟩ x none
      = Spec.Tensor.reshapeSpec
          (matrixTensor (selfAttn (MathFunctions.sqrt (d : ℝ))
            (matCoords (Spec.Tensor.reshapeSpec x hsplit)))) hcomb := by
  have hps : 0 < (Shape.dim (n + 1) (.dim d .scalar)).size := by
    simp only [Shape.size]; positivity
  have hid : ∀ t : Tensor ℝ (.dim (n + 1) (.dim (1 * d) .scalar)),
      matMulSpec t (idTensorM (1 * d)) = t := fun t => matMulSpec_id_right t
  rw [MultiHeadAttention.forward]
  simp only [hid, splitHeadsSpec_one hps x hsplit, combineHeadsSpec_one hd _ hcomb]
  congr 1
  rw [← matrixTensor_matCoords (scaledDotProductAttention _)]
  congr 1
  rw [matCoords_scaledDotProductAttention (matCoords (Spec.Tensor.reshapeSpec x hsplit))
    (fun k j => if k = j then (1 : ℝ) else 0) _
    (matrixTensor_matCoords _).symm (matrixTensor_matCoords _).symm
    (by rw [matMulCoord_id]; exact (matrixTensor_matCoords _).symm) rfl]
  funext i e
  simp only [attnHead, selfAttn, matMulCoord_id]

/-! ### Toward #2: general `numHeads` and the swap as a real transpose -/

/-- **The first-two-axis swap transposes the outer two `get` indices.** For general `numHeads`,
`combineHeadsSpec`'s swap `(nH, n, hD) → (n, nH, hD)` is a genuine transpose (not flat-preserving as at
numHeads=1); read structurally, it just exchanges the two outer indices. The base case of the
general-multi-head reshape reads. -/
lemma get_get_swapFirstTwoSpec {m n' : ℕ} {s : Spec.Shape} (f : Fin m → Tensor ℝ (.dim n' s))
    (i : Fin n') (b : Fin m) :
    Spec.get (Spec.get (Spec.Tensor.swapFirstTwoSpec (Tensor.dim f)) i) b = Spec.get (f b) i := by
  cases hfb : f b with
  | dim g => simp [Spec.Tensor.swapFirstTwoSpec, get_eq, hfb]

end TLT
