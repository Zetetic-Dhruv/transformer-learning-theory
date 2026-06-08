/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Certificate.AttentionTransformerCertificate
import NN.Spec.Layers.Attention
import NN.Proofs.Tensor.Algebra

/-!
# Literal binding: TorchLean `scaledDotProductAttention` in coordinates

The coordinate characterization that connects the certified attention model `attnHead` to TorchLean's
*literal* `Spec.scaledDotProductAttention` tensor op. The op is
`matMulSpec (softmaxSpec (scaleSpec (matMulSpec Q Kᵀ) (1/√d))) V`; read in coordinates it is exactly
`attnHead √d W Y` with `Q = K = Y` (self-attention) and `V = Y·W` (the value projection).

The matrix-multiply and round-trip coordinate reads are reused from `ForwardContinuity`
(`get2_mat_mul_spec`, `get2_matrixTensor`, `matCoords`). The softmax-stabilization fact
(`softmaxVecSpec`, the max-stabilized form, agrees coordinatewise with the plain `exp/Σexp`) is the
`private` upstream lemma `SoftmaxEquivariance.softmax_vec_spec_eq_plain`; since it is not exported, its
proof chain (`scalarElim`, `scalarVal`, `softmaxVecPlain`, `softmax_vec_spec_eq_plain`) is reproduced
here verbatim as a private helper block, and the per-row softmax reads (`vecGet` of
`mapSpec`/`map2Spec`/`replicate`) follow the `LayerNormSpec` casing pattern.

## Main results

- `vecGet_softmaxVecSpec` — the per-row softmax-stabilization coordinate bridge.
-/

/-!
## References
- [27] Eq. 1 §3.2.1 SDPA; [29] softmax definition + shift-invariance (max-subtracted stable form);
  [53] `scaledDotProductAttention`, `softmaxSpec`/`softmaxVecSpec`.
- Provenance: Vendored-glue (literal SDPA op = attnHead in coordinates).
-/

open Spec Tensor

namespace TLT

/-! ### Reused softmax-stabilization chain

Verbatim copy of TorchLean's `private` `SoftmaxEquivariance.softmax_vec_spec_eq_plain` and its helper
chain (the lemma is not exported upstream). It states that the max-stabilized `softmaxVecSpec` equals
the plain `exp/Σexp` softmax — the stabilizing shift cancels. -/

/-- Eliminate a scalar tensor using the same matcher as `Activation.softmax_vec_spec`. -/
private abbrev scalarElim {β : Sort _} (t : Tensor ℝ .scalar) (k : ℝ → β) : β :=
  Activation.softmaxVecSpec.match_1 (motive := fun _ => β) t k

@[simp] private theorem scalarElim_scalar {β : Sort _} (k : ℝ → β) (v : ℝ) :
    scalarElim (β := β) (Spec.Tensor.scalar v) k = k v := rfl

private abbrev scalarVal (t : Tensor ℝ .scalar) : ℝ :=
  scalarElim (β := ℝ) t (fun v => v)

/-- Plain (unstabilized) softmax on a vector tensor. Proof helper. -/
private noncomputable def softmaxVecPlain {n : Nat} (t : Tensor ℝ (.dim n .scalar)) :
    Tensor ℝ (.dim n .scalar) :=
  match t with
  | .dim f =>
      let x : Fin n → ℝ := fun i => scalarVal (f i)
      let denom : ℝ := ∑ j : Fin n, Real.exp (x j)
      .dim (fun i => .scalar (Real.exp (x i) / denom))

/-- The stabilized spec `softmax_vec_spec` agrees with `softmaxVecPlain` over `ℝ`. -/
private theorem softmax_vec_spec_eq_plain {n : Nat} (t : Tensor ℝ (.dim (Nat.succ n) .scalar)) :
    Activation.softmaxVecSpec (α := ℝ) (n := Nat.succ n) t = softmaxVecPlain t := by
  classical
  cases t with
  | dim f =>
      let x : Fin (Nat.succ n) → ℝ := fun i => scalarVal (f i)
      -- The internal shift used by the stabilized definition (we do not use any "max" properties).
      let first : ℝ := x ⟨0, Nat.succ_pos n⟩
      -- Define `m` in the same shape as the spec definition (folding over indices with a `match`).
      let m : ℝ :=
        (List.finRange (Nat.succ n)).foldl
          (fun acc i => scalarElim (β := ℝ) (f i) (fun v => max acc v))
          first
      -- Denominators: shifted vs plain.
      let denomPlain : ℝ := ∑ j : Fin (Nat.succ n), Real.exp (x j)
      let denomShift : ℝ := ∑ j : Fin (Nat.succ n), Real.exp (x j - m)
      have hdenomShift :
          denomShift = denomPlain * Real.exp (-m) := by
        -- Rewrite each term `exp(x - m) = exp(x) * exp(-m)` and factor out the constant.
        calc
          denomShift
              = ∑ j : Fin (Nat.succ n), Real.exp (x j) * Real.exp (-m) := by
                  refine Finset.sum_congr rfl ?_
                  intro j _
                  simp [sub_eq_add_neg, Real.exp_add]
          _ = (∑ j : Fin (Nat.succ n), Real.exp (x j)) * Real.exp (-m) := by
                -- `∑ (a_j * c) = (∑ a_j) * c`.
                simpa [denomPlain] using (Finset.sum_mul (s := (Finset.univ : Finset (Fin (Nat.succ n))))
                  (f := fun j => Real.exp (x j)) (a := Real.exp (-m))).symm
      -- Now show coordinatewise equality: the `exp(-m)` factor cancels.
      apply congrArg Spec.Tensor.dim
      funext i
      have hmne : Real.exp (-m) ≠ 0 := Real.exp_ne_zero _
      -- The stabilized output is `exp(x_i - m) / denomShift`.
      -- The plain output is `exp(x_i) / denomPlain`.
      -- Use `mul_div_mul_right` to cancel the shared factor `exp(-m)`.
      have hcancel :
          Real.exp (x i - m) / denomShift = Real.exp (x i) / denomPlain := by
        -- Rewrite numerator and denominator into `(* exp(-m))` form, then cancel.
        calc
          Real.exp (x i - m) / denomShift
              = (Real.exp (x i) * Real.exp (-m)) / (denomPlain * Real.exp (-m)) := by
                  simp [hdenomShift, sub_eq_add_neg, Real.exp_add]
          _ = Real.exp (x i) / denomPlain := by
                simpa [mul_assoc] using (mul_div_mul_right (Real.exp (x i)) denomPlain hmne)
      -- Relate the implementation's list-fold denominator to the `∑` form (`denomShift`).
      have hfold :
          (List.finRange (Nat.succ n)).foldl (fun acc j => acc + Real.exp (x j - m)) 0 = denomShift := by
        dsimp [denomShift]
        simpa using
          (Spec.finRange_foldl_add_eq_finset_sum (n := Nat.succ n) (f := fun j => Real.exp (x j - m)))
      -- Finish by simplifying the scalar combinators and rewriting the denominator fold.
      have hTerm :
          ∀ j : Fin (Nat.succ n),
            scalarElim (β := ℝ)
                (Spec.Tensor.mapSpec MathFunctions.exp
                  (Spec.Tensor.map2Spec (fun a b => a - b) (f j) (Spec.Tensor.scalar m)))
                (fun v => v) =
              Real.exp (x j - m) := by
        intro j
        cases hj : f j with
        | scalar xj =>
            simp [scalarElim, scalarVal, Spec.Tensor.mapSpec, Spec.Tensor.map2Spec, x, hj]
            rfl
      have hfun :
          (fun (acc : ℝ) (j : Fin (Nat.succ n)) =>
              acc +
                scalarElim (β := ℝ)
                  (Spec.Tensor.mapSpec MathFunctions.exp
                    (Spec.Tensor.map2Spec (fun a b => a - b) (f j) (Spec.Tensor.scalar m)))
                  (fun v => v))
            =
          (fun (acc : ℝ) (j : Fin (Nat.succ n)) => acc + Real.exp (x j - m)) := by
        funext acc j
        simp [hTerm j]
      have hden :
          (List.finRange (Nat.succ n)).foldl
              (fun acc j =>
                acc +
                  scalarElim (β := ℝ)
                    (Spec.Tensor.mapSpec MathFunctions.exp
                      (Spec.Tensor.map2Spec (fun a b => a - b) (f j) (Spec.Tensor.scalar m)))
                    (fun v => v))
              0
            =
          denomShift := by
        simpa [hfun] using hfold

      -- Reduce to the real-valued cancellation lemma `hcancel` and lift through `Tensor.scalar`.
      cases hi : f i with
      | scalar xi =>
          have hcancel' : Real.exp (xi - m) / denomShift = Real.exp xi / denomPlain := by
            simpa [x, scalarVal, scalarElim, hi] using hcancel
          have hgoal :
              MathFunctions.exp
                    (xi -
                      List.foldl (fun acc i => scalarElim (β := ℝ) (f i) (fun v => max acc v))
                        (scalarElim (β := ℝ) (f ⟨0, Nat.succ_pos n⟩) (fun v => v))
                        (List.finRange (Nat.succ n))) /
                  List.foldl
                      (fun acc i =>
                        acc +
                          scalarElim (β := ℝ)
                            (Spec.Tensor.mapSpec MathFunctions.exp
                              (Spec.Tensor.map2Spec (fun x1 x2 => x1 - x2) (f i)
                                (Spec.Tensor.scalar
                                  (List.foldl
                                    (fun acc i => scalarElim (β := ℝ) (f i) (fun v => max acc v))
                                    (scalarElim (β := ℝ) (f ⟨0, Nat.succ_pos n⟩) (fun v => v))
                                    (List.finRange (Nat.succ n))))))
                            (fun v => v))
                      (0 : ℝ)
                      (List.finRange (Nat.succ n))
                =
              Real.exp xi /
                ∑ x : Fin (Nat.succ n),
                  Real.exp (scalarElim (β := ℝ) (f x) (fun v => v)) := by
            have htmp := hcancel'
            -- Replace the finite-sum denominator (`denomShift`) with the list-fold denominator used
            -- by the spec definition.
            rw [← hden] at htmp
            simpa [denomPlain, x, m, first, scalarVal, scalarElim] using htmp
          -- Normalized form of `hgoal` matching the shape produced by the `simp`-unfolding below.
          have hgoal' :
              MathFunctions.exp
                    (xi -
                      List.foldl (fun acc i => scalarElim (β := ℝ) (f i) (fun v => max acc v))
                        (scalarElim (β := ℝ) (f 0) (fun v => v))
                        (List.finRange (n + 1))) /
                  List.foldl
                      (fun acc i =>
                        acc +
                          scalarElim (β := ℝ)
                            (Spec.Tensor.mapSpec MathFunctions.exp
                              (Spec.Tensor.map2Spec (fun x1 x2 => x1 - x2) (f i)
                                (Spec.Tensor.scalar
                                  (List.foldl
                                    (fun acc i => scalarElim (β := ℝ) (f i) (fun v => max acc v))
                                    (scalarElim (β := ℝ) (f 0) (fun v => v))
                                    (List.finRange (n + 1))))))
                            (fun v => v))
                      (0 : ℝ)
                      (List.finRange (n + 1))
                =
              Real.exp xi /
                ∑ x : Fin (n + 1),
                  Real.exp (scalarElim (β := ℝ) (f x) (fun v => v)) := by
            simpa [Nat.succ_eq_add_one] using hgoal
          -- Unfold the scalar tensor ops at index `i` and use `hgoal`.
          simp [hi, scalarVal, scalarElim, Spec.replicate, Spec.Tensor.mapSpec, Spec.Tensor.map2Spec,
            Spec.Tensor.subSpec, Spec.Tensor.expSpec]
          -- `simp` has unfolded the tensor combinators, so the goal is a scalar identity.
          simpa [scalarVal, scalarElim] using hgoal'

/-! ### Vector coordinate reads -/

/-- Vector coordinate read of `mapSpec`: `(mapSpec f v)[j] = f (v[j])`. -/
lemma vecGet_mapSpec' {n : ℕ} (f : ℝ → ℝ) (v : Tensor ℝ (.dim n .scalar)) (j : Fin n) :
    Tensor.vecGet (mapSpec f v) j = f (Tensor.vecGet v j) := by
  cases v with
  | dim g =>
    cases hg : g j with
    | scalar x => simp [Tensor.vecGet, get_eq, mapSpec, hg, Tensor.toScalar]

/-- Vector coordinate read of `map2Spec`: `(map2Spec f a b)[j] = f (a[j]) (b[j])`. -/
lemma vecGet_map2Spec' {n : ℕ} {β γ : Type} (f : ℝ → β → γ) (a : Tensor ℝ (.dim n .scalar))
    (b : Tensor β (.dim n .scalar)) (j : Fin n) :
    Tensor.vecGet (map2Spec f a b) j = f (Tensor.vecGet a j) (Tensor.vecGet b j) := by
  cases a with
  | dim ga =>
    cases b with
    | dim gb =>
      cases hga : ga j with
      | scalar xa =>
        cases hgb : gb j with
        | scalar xb => simp [Tensor.vecGet, get_eq, map2Spec, hga, hgb, Tensor.toScalar]

/-- Vector coordinate read of `replicate`: every entry of a broadcast scalar is that scalar. -/
lemma vecGet_replicate {n : ℕ} (c : ℝ) (j : Fin n) :
    Tensor.vecGet (replicate (Tensor.scalar c) : Tensor ℝ (.dim n .scalar)) j = c := by
  simp [Tensor.vecGet, get_eq, replicate, Tensor.toScalar]

/-! ### The softmax-stabilization coordinate bridge -/

/-- **The softmax-stabilization coordinate bridge.** TorchLean's max-stabilized `softmaxVecSpec` reads
in coordinates as the plain softmax: `(softmaxVecSpec t)[j] = softmax (coordinates of t) j`. The
stabilization shift cancels (the cancellation is the reused `softmax_vec_spec_eq_plain`; `scalarVal`
agrees with `Tensor.vecGet` on scalars). -/
lemma vecGet_softmaxVecSpec {n : ℕ} (t : Tensor ℝ (.dim (n + 1) .scalar)) (i : Fin (n + 1)) :
    Tensor.vecGet (Activation.softmaxVecSpec t) i = softmax (fun k => Tensor.vecGet t k) i := by
  have hsv : ∀ s : Tensor ℝ .scalar, scalarVal s = Tensor.toScalar s :=
    fun s => by cases s with | scalar v => rfl
  rw [softmax_vec_spec_eq_plain t]
  cases t with
  | dim f =>
    simp only [softmaxVecPlain, Tensor.vecGet, get_eq, Tensor.toScalar, softmax, hsv]

/-! ### Matrix-level reads and the softmax lift -/

/-- `get2` of a `dim` tensor is the `vecGet` of the indexed row. -/
lemma get2_dim {m n : ℕ} (h : Fin m → Tensor ℝ (.dim n .scalar)) (i : Fin m) (j : Fin n) :
    get2 (Tensor.dim h) i j = Tensor.vecGet (h i) j := by
  cases hi : h i with
  | dim row => cases hr : row j with
    | scalar v => simp [get2, get_eq, Tensor.vecGet, Tensor.toScalar, hi, hr]

/-- Matrix coordinate read of `scaleSpec`: `(scaleSpec S c)[i,j] = S[i,j] · c`. -/
lemma get2_scaleSpec {m n : ℕ} (S : Tensor ℝ (.dim m (.dim n .scalar))) (c : ℝ) (i : Fin m)
    (j : Fin n) : get2 (Spec.Tensor.scaleSpec S c) i j = get2 S i j * c := by
  cases S with
  | dim rows => cases hrow : rows i with
    | dim cols => cases hcol : cols j with
      | scalar v => simp [get2, get_eq, Spec.Tensor.scaleSpec, Spec.Tensor.mapSpec, hrow, hcol]

/-- **The row-wise softmax coordinate bridge.** `softmaxSpec` of a score matrix reads in coordinates
as the row-wise plain softmax: `(softmaxSpec M)[i,j] = softmax (row i of M) j`. The row recursion of
`softmaxSpec` reduces to `softmaxVecSpec` per row, then `vecGet_softmaxVecSpec` applies. -/
lemma get2_softmaxSpec {nQ nK : ℕ} (M : Tensor ℝ (.dim nQ (.dim (nK + 1) .scalar))) (i : Fin nQ)
    (j : Fin (nK + 1)) :
    get2 (Activation.softmaxSpec M) i j = softmax (fun k => get2 M i k) j := by
  cases M with
  | dim g =>
    have hsm : Activation.softmaxSpec (Tensor.dim g)
        = Tensor.dim (fun i => Activation.softmaxVecSpec (g i)) := by
      simp only [Activation.softmaxSpec]
    rw [hsm, get2_dim, vecGet_softmaxVecSpec]
    refine congrArg (fun z => softmax z j) ?_
    funext k
    rw [get2_dim]

/-- Matrix coordinate read of `matrixTransposeSpec`: `(Kᵀ)[a,b] = K[b,a]`. -/
lemma get2_matrixTransposeSpec {m n : ℕ} (K : Tensor ℝ (.dim m (.dim n .scalar))) (a : Fin n)
    (b : Fin m) : get2 (Spec.Tensor.matrixTransposeSpec K) a b = get2 K b a := by
  cases K with
  | dim rows => cases hb : rows b with
    | dim cols => cases ha : cols a with
      | scalar v => simp [get2, get_eq, Spec.Tensor.matrixTransposeSpec, hb, ha]

/-! ### The literal attention coordinate characterization -/

/-- **TorchLean's `scaledDotProductAttention`, read in coordinates, is `attnHead`.** With queries and
keys both the input `Y` (self-attention) and values the learnable projection `Y·W`, the literal spec
op `matMulSpec (softmaxSpec (scaleSpec (Q·Kᵀ) (1/√d))) V` equals — coordinatewise — the certified
attention model `attnHead √d W Y`. This binds the certified bound to TorchLean's actual attention
operation, replacing the abstract `hagree` interface with the literal op. -/
theorem matCoords_scaledDotProductAttention {n d : ℕ} (Y : Fin (n + 1) → Fin d → ℝ)
    (W : Fin d → Fin d → ℝ)
    (ctx : AttentionContext ℝ (n + 1) (n + 1) d (Nat.succ_ne_zero n) (Nat.succ_ne_zero n))
    (hQ : ctx.Q = matrixTensor Y) (hK : ctx.K = matrixTensor Y)
    (hV : ctx.V = matrixTensor (matMulCoord W Y)) (hmask : ctx.mask = none) :
    matCoords (Spec.scaledDotProductAttention ctx)
      = attnHead (MathFunctions.sqrt (d : ℝ)) W Y := by
  funext i e
  simp only [matCoords, Spec.scaledDotProductAttention, hmask, get2_mat_mul_spec, get2_softmaxSpec,
    get2_scaleSpec, get2_matrixTransposeSpec, hQ, hK, hV, get2_matrixTensor,
    attnHead, attnVec, attnOut, mul_one_div]
  rfl

end TLT
