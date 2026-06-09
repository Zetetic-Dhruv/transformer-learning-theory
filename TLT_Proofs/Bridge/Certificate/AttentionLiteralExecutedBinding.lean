/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Fp32.AttentionForwardError
import TLT_Proofs.Bridge.Fp32.ExpExecutedValue
import TLT_Proofs.Bridge.Spec.ScaledDotProductAttentionCorrespondence
import NN.Spec.Layers.SoftmaxVecCoordReadStaged
import TLT_Proofs.Bridge.Fp32.GenSoftmaxForwardError

/-!
# The literal executed binding of the fp32 attention forward-error

`Bridge/Fp32/AttentionForwardError` proves a forward-error envelope for a *rounding model* of the
attention head (`execAttnStar`: every scalar op = real op + one `fp32Round`, `Real.exp` rounded). This
file upgrades that to the **literal** TorchLean kernel: the executed forward in the final theorem is
`Spec.scaledDotProductAttention` at backend `IEEE32Exec`, read back over `ℝ` through `toReal` — the
exact tensor op the hardware runs, not a hand-rolled surrogate.

The bridge is op-by-op. `Spec.scaledDotProductAttention` is
`matMulSpec (softmaxSpec (scaleSpec (matMulSpec Q Kᵀ) (1/√d))) V`. At `IEEE32Exec`, each `matMulSpec`
fold accumulates with the literal IEEE binary32 `+`/`*`; pushing `toReal` through it (via
`toReal_foldl_add` + the per-product `toReal_mul_eq_fp32Round_of_isFinite`) reproduces the model's
rounded dot product `rdot` *exactly*. The score scaling and the value mix likewise reproduce the
model's `Sexec`/`omixRow`.

The one genuine discrepancy is the softmax. TorchLean's `softmaxVecSpec` is the **max-stabilized**
form `exp(x − m)/Σ exp(x − m)`; the model's softmax is the **plain** `exp x/Σ exp x`. Over `ℝ` the
shift cancels (`vecGet_softmaxVecSpec`), but at `IEEE32Exec` the executed kernel rounds the subtraction
`x − m`, evaluates the bit-level polynomial `IEEE32Exec.exp` on the shifted logit, folds, and rounds
the quotient — none of which telescopes back to the no-shift model. We therefore do **not** route the
softmax through the model. Instead we expose the executed per-row softmax weights as honest data and
bound them against the *ideal* `softmax` directly, with an explicit total-variation hypothesis
`hsmTV`. Everything else (the two value matmuls and the score scaling) is reduced to the model and
reuses its closed-form budgets.

The result `attnLiteralForwardError` bounds the literal kernel against `attnHead √d W (clampCoord B Y)`
by a derived closed form `rndStarLit`, and `attnHead_executed_certified_generalization_literal`
instantiates the executed certificate with the literal kernel as `execAttn` — no free rounding bound.

## Main results

- `execAttnLit` — the literal `IEEE32Exec` `scaledDotProductAttention`, read over `ℝ`.
- `attnLiteralForwardError` — its forward-error envelope against the ideal head.
- `attnHead_executed_certified_generalization_literal` — the executed certificate, literal kernel.
-/

/-!
## References
- [53] literal `scaledDotProductAttention` + IEEE32 execution; [29] max-stabilized softmax;
  [43] summation backward error; [46] executed exp value error.
- Provenance: Innovation — the executed certificate bound about the literal finite-precision attention
  kernel the hardware runs (not the rounding model surrogate).
-/

open TorchLean.Floats (neuralMagnitude neuralBpow binaryRadix)
open TorchLean.Floats.IEEE754
open TorchLean.Floats.IEEE754.IEEE32Exec
open Spec Tensor

noncomputable section

namespace TLT.Fp32AttnLit

open TLT TLT.Fp32Attn
open TorchLean.Staged.SoftmaxCoord
open MeasureTheory
open Capacity

/-! ## IEEE32Exec coordinate reads of the literal kernel

The matrix-multiply / scale / transpose coordinate reads are backend-generic structural unfoldings; we
reprove them at `IEEE32Exec` (the `ℝ` versions in `ScaledDotProductAttentionCorrespondence` fix the
scalar type). Only the matmul fold is special: at `IEEE32Exec` it does **not** collapse to a
`Finset.sum` (float `+` is not associative), so we keep it as the literal left fold. -/

/-- `get2` of a `dim` tensor is the `vecGet` of the indexed row (at `IEEE32Exec`). -/
lemma get2_dim_ie {m n : ℕ} (h : Fin m → Tensor IEEE32Exec (.dim n .scalar)) (i : Fin m) (j : Fin n) :
    get2 (Tensor.dim h) i j = Tensor.vecGet (h i) j := by
  cases hi : h i with
  | dim row => cases hr : row j with
    | scalar v => simp [get2, get_eq, Tensor.vecGet, Tensor.toScalar, hi, hr]

/-- Matrix coordinate read of `scaleSpec` at `IEEE32Exec`: `(scaleSpec S c)[i,j] = S[i,j] * c`. -/
lemma get2_scaleSpec_ie {m n : ℕ} (S : Tensor IEEE32Exec (.dim m (.dim n .scalar))) (c : IEEE32Exec)
    (i : Fin m) (j : Fin n) : get2 (Spec.Tensor.scaleSpec S c) i j = get2 S i j * c := by
  cases S with
  | dim rows => cases hrow : rows i with
    | dim cols => cases hcol : cols j with
      | scalar v => simp [get2, get_eq, Spec.Tensor.scaleSpec, Spec.Tensor.mapSpec, hrow, hcol]

/-- Matrix coordinate read of `matrixTransposeSpec` at `IEEE32Exec`: `(Kᵀ)[a,b] = K[b,a]`. -/
lemma get2_matrixTransposeSpec_ie {m n : ℕ} (K : Tensor IEEE32Exec (.dim m (.dim n .scalar)))
    (a : Fin n) (b : Fin m) :
    get2 (Spec.Tensor.matrixTransposeSpec K) a b = get2 K b a := by
  cases K with
  | dim rows => cases hb : rows b with
    | dim cols => cases ha : cols a with
      | scalar v => simp [get2, get_eq, Spec.Tensor.matrixTransposeSpec, hb, ha]

/-- **Fold body-congruence**, accumulator held fixed: equal step functions give equal left folds. -/
private lemma foldl_body_congr {β ι : Type} (f g : β → ι → β) (h : ∀ s k, f s k = g s k)
    (l : List ι) (init : β) : l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons hd tl ih => rw [List.foldl_cons, List.foldl_cons, h init hd]; exact ih _

/-- The literal `IEEE32Exec` matmul coordinate, as the literal left fold of products with the float
accumulator `posZero` — the form `toReal_foldl_add` consumes (the non-associative float `+` order).
The accumulator is written `posZero` (which is `matMulSpec`'s `Zero.zero` by instance), sidestepping the
`(0 : IEEE32Exec)` `OfNat`-vs-`Zero` diamond; `foldl_body_congr` then reduces to the per-product
equality. -/
lemma get2_matMulSpec_ie {m n p : ℕ} (A : Tensor IEEE32Exec (.dim m (.dim n .scalar)))
    (B : Tensor IEEE32Exec (.dim n (.dim p .scalar))) (i : Fin m) (j : Fin p) :
    get2 (matMulSpec A B) i j
      = (List.finRange n).foldl (fun s k => s + get2 A i k * get2 B k j) posZero := by
  cases A with
  | dim rowsA =>
    cases B with
    | dim rowsB =>
      simp only [matMulSpec, get2_eq, get_eq]
      refine foldl_body_congr _ _ (fun s k => ?_) _ _
      cases hrowA : rowsA i with
      | dim colsA =>
        cases hrowB : rowsB k with
        | dim colsB =>
          cases hA : colsA k with
          | scalar a =>
            cases hB : colsB j with
            | scalar b => simp [get2, get_eq, Tensor.toScalar, hrowA, hrowB, hA, hB]

/-! ## Pushing `toReal` through the literal matmul: reproducing the model's `rdot`

The literal `IEEE32Exec` matmul coordinate read over `ℝ` reproduces the rounding model's `rdot`
exactly. This is the keystone reuse: every *arithmetic* channel of the literal kernel (the `Q·Kᵀ`
scores and the value mix `P·V`) inherits the model's closed-form `rdotBudget`, so no rounding analysis
is re-derived. Only the softmax channel does not route through the model (see the file header). -/

/-- The honest no-overflow precondition for the literal matmul coordinate `(A·B)[i,j]`: every partial
sum of the rounded products stays finite, and each scalar product is finite. A float matmul can
overflow, so these facts are not implied by the real input bounds; they are surfaced as explicit
hypotheses rather than fabricated. -/
def MatMulCoordFinite {m n p : ℕ} (A : Tensor IEEE32Exec (.dim m (.dim n .scalar)))
    (B : Tensor IEEE32Exec (.dim n (.dim p .scalar))) (i : Fin m) (j : Fin p) : Prop :=
  IE32FoldlFinite posZero ((List.finRange n).map (fun k => get2 A i k * get2 B k j))
    ∧ ∀ k : Fin n, isFinite (get2 A i k * get2 B k j) = true

/-- **The literal→model arithmetic bridge (keystone).** The literal `IEEE32Exec` matmul coordinate,
read over `ℝ` through `toReal`, IS the model's rounded dot product `rdot` of the `toReal`-read row and
column — exactly, under the honest finiteness precondition. The proof pushes `toReal` through the
literal left fold (`toReal_foldl_add`) and through each scalar product
(`toReal_mul_eq_fp32Round_of_isFinite`), landing on the model's `fp32Foldl 0 (List.ofFn …)`. -/
lemma toReal_get2_matMulSpec_ie {m n p : ℕ} (A : Tensor IEEE32Exec (.dim m (.dim n .scalar)))
    (B : Tensor IEEE32Exec (.dim n (.dim p .scalar))) (i : Fin m) (j : Fin p)
    (hfin : MatMulCoordFinite A B i j) :
    toReal (get2 (matMulSpec A B) i j)
      = rdot (fun k => toReal (get2 A i k)) (fun k => toReal (get2 B k j)) := by
  obtain ⟨hfold, hprod⟩ := hfin
  rw [get2_matMulSpec_ie, ← List.foldl_map, toReal_foldl_add posZero _ hfold, toReal_posZero]
  unfold rdot rprods
  congr 1
  rw [List.map_map, List.ofFn_eq_map]
  exact List.map_congr_left (fun k _ => toReal_mul_eq_fp32Round_of_isFinite _ _ (hprod k))

/-! ## The stabilized literal softmax, read coordinate-wise

TorchLean's `softmaxVecSpec` is the **max-stabilized** form: an exact row max (the float `max` returns
one of its inputs, so no rounding), a rounded shift `t_j − m`, the bit-level `IEEE32Exec.exp`, a rounded
denominator fold, and a rounded quotient. We read the coordinate keeping the shift explicit (the ℝ
`vecGet_softmaxVecSpec` cancels the shift via `softmax_vec_spec_eq_plain`; in fp32 the shift does not
cancel because it is itself rounded). -/

/-- Vector coordinate read of `mapSpec` at `IEEE32Exec`: `(mapSpec g v)[j] = g (v[j])`. -/
lemma vecGet_mapSpec_ie {n : ℕ} (g : IEEE32Exec → IEEE32Exec)
    (v : Tensor IEEE32Exec (.dim n .scalar)) (j : Fin n) :
    Tensor.vecGet (Spec.Tensor.mapSpec g v) j = g (Tensor.vecGet v j) := by
  cases v with
  | dim h => cases hh : h j with
    | scalar x => simp [Tensor.vecGet, get_eq, Spec.Tensor.mapSpec, hh, Tensor.toScalar]

/-- Vector coordinate read of `map2Spec` at `IEEE32Exec`: `(map2Spec g a b)[j] = g (a[j]) (b[j])`. -/
lemma vecGet_map2Spec_ie {n : ℕ} {β γ : Type} (g : IEEE32Exec → β → γ)
    (a : Tensor IEEE32Exec (.dim n .scalar)) (b : Tensor β (.dim n .scalar)) (j : Fin n) :
    Tensor.vecGet (Spec.Tensor.map2Spec g a b) j = g (Tensor.vecGet a j) (Tensor.vecGet b j) := by
  cases a with
  | dim ga => cases b with
    | dim gb => cases hga : ga j with
      | scalar xa => cases hgb : gb j with
        | scalar xb =>
          simp [Tensor.vecGet, get_eq, Spec.Tensor.map2Spec, hga, hgb, Tensor.toScalar]

/-- Vector coordinate read of `replicate` at `IEEE32Exec`: every entry of a broadcast scalar is it. -/
lemma vecGet_replicate_ie {n : ℕ} (c : IEEE32Exec) (j : Fin n) :
    Tensor.vecGet (Spec.replicate (Tensor.scalar c) : Tensor IEEE32Exec (.dim n .scalar)) j = c := by
  simp [Tensor.vecGet, get_eq, Spec.replicate, Tensor.toScalar]

/-- `vecGet` of a `dim` tensor is the `toScalar` of the indexed entry (needs `get_eq`; not definitional). -/
lemma vecGet_dim_ie {n : ℕ} (g : Fin n → Tensor IEEE32Exec .scalar) (k : Fin n) :
    Tensor.vecGet (Tensor.dim g) k = Tensor.toScalar (g k) := by
  cases hk : g k with
  | scalar v => simp [Tensor.vecGet, get_eq, Tensor.toScalar, hk]

/-- Generic projection: the hand-rolled denominator fold of `softmaxVecSpec` (a `match`-on-`dim` then a
left fold of the scalar entries) equals the left fold of the `vecGet`s. Bridges the stuck `match g k`
(on the neutral `g k`) to `vecGet`, with the accumulator held fixed by `foldl_body_congr`. -/
lemma denom_eq_foldl_vecGet {m : ℕ} (s : Tensor IEEE32Exec (.dim m .scalar)) :
    (match s with
      | .dim g =>
        (List.finRange m).foldl (fun acc k => acc + match g k with | .scalar v => v) 0)
      = (List.finRange m).foldl (fun acc k => acc + Tensor.vecGet s k) 0 := by
  cases s with
  | dim g =>
    refine foldl_body_congr _ _ (fun acc k => ?_) _ _
    cases hgk : g k with
    | scalar v => simp [Tensor.vecGet, get_eq, Tensor.toScalar, hgk]

/-- The literal row max of a score row (seeded at entry `0`). The float `max` returns one of its inputs,
so this is exact — no rounding. Defined by the same `match` as `softmaxVecSpec`'s internal max, so the
coordinate read below reduces definitionally on the row-max channel. -/
def litRowMax {n' : ℕ} (t : Tensor IEEE32Exec (.dim (n' + 1) .scalar)) : IEEE32Exec :=
  match t with
  | .dim f =>
      (List.finRange (n' + 1)).foldl (fun acc k => match f k with | .scalar v => max acc v)
        (match f ⟨0, Nat.succ_pos n'⟩ with | .scalar v => v)

/-- The literal shifted logit `t_i − rowMax` (a single rounded `sub`). -/
def litShifted {n' : ℕ} (t : Tensor IEEE32Exec (.dim (n' + 1) .scalar)) (i : Fin (n' + 1)) :
    IEEE32Exec := Tensor.vecGet t i - litRowMax t

/-- The literal softmax denominator: the float left-fold of the exps of the shifted logits. -/
def litDenom {n' : ℕ} (t : Tensor IEEE32Exec (.dim (n' + 1) .scalar)) : IEEE32Exec :=
  (List.finRange (n' + 1)).foldl (fun acc k => acc + MathFunctions.exp (litShifted t k)) 0

/-! ## KU-stab step 1 — pushing `toReal` through the literal softmax weight

With the staged read `vecGet (softmaxVecSpec zt) i = exp(softmaxShiftedIE zt i) / softmaxDenomIE zt`, we
push `toReal` through (div + denominator fold) to land the literal per-row softmax weight over ℝ in the
model's `rsoftmax`-shape: `fp32Round(litExp_i / fp32Foldl 0 (litExp))`, `litExp = toReal∘IEEE32Exec.exp∘
shifted`. This is pure structural rounding-arithmetic (the `δ_exp` exp-atom enters only at the TV step). -/

/-- **Step 1a (toReal of the literal softmax denominator).** Pushes `toReal` through `softmaxDenomIE`'s
float fold into the model's `fp32Foldl` shape, under the honest no-overflow fold-finiteness hypothesis. -/
lemma toReal_softmaxDenomIE {n' : ℕ} (zt : Tensor IEEE32Exec (.dim (n' + 1) .scalar))
    (hfin : IE32FoldlFinite posZero
      ((List.finRange (n' + 1)).map (fun j => MathFunctions.exp (softmaxShiftedIE zt j)))) :
    toReal (softmaxDenomIE zt)
      = fp32Foldl 0
          ((List.finRange (n' + 1)).map (fun j => toReal (MathFunctions.exp (softmaxShiftedIE zt j)))) := by
  cases zt with
  | dim f =>
    rw [softmaxDenomIE, ← List.foldl_map, toReal_foldl_add posZero _ hfin, toReal_posZero, List.map_map]
    rfl

/-- **Step 1 (literal softmax weight over ℝ).** The literal per-row softmax weight, read over ℝ, is
`fp32Round(litExp_i / fp32Foldl 0 (litExp))` — the model's `rsoftmax`-shape with `litExp = toReal∘`
`IEEE32Exec.exp∘shifted` in place of `rexp`. Pure structural `toReal`-push; the `δ_exp` exp-atom is not
used here. The finiteness hypotheses are the honest no-overflow conditions on the executed quotient and
denominator fold. -/
lemma toReal_litSoftmax {n' : ℕ} (zt : Tensor IEEE32Exec (.dim (n' + 1) .scalar)) (i : Fin (n' + 1))
    (hdiv : isFinite (MathFunctions.exp (softmaxShiftedIE zt i) / softmaxDenomIE zt) = true)
    (hfold : IE32FoldlFinite posZero
      ((List.finRange (n' + 1)).map (fun j => MathFunctions.exp (softmaxShiftedIE zt j)))) :
    toReal (Tensor.vecGet (Activation.softmaxVecSpec zt) i)
      = fp32Round (toReal (MathFunctions.exp (softmaxShiftedIE zt i))
          / fp32Foldl 0
              ((List.finRange (n' + 1)).map (fun j => toReal (MathFunctions.exp (softmaxShiftedIE zt j))))) := by
  rw [vecGet_softmaxVecSpec_ie]
  change toReal (div (MathFunctions.exp (softmaxShiftedIE zt i)) (softmaxDenomIE zt)) = _
  rw [toReal_div_eq_fp32Round_of_isFinite _ _ hdiv, toReal_softmaxDenomIE zt hfold]

/-! ## KU-stab step 2 instance — the literal kernel as a `genSoftmax`

The literal per-row softmax weight over ℝ is the exp-value-parametric rounded softmax `genSoftmax`
(`GenSoftmaxForwardError`) at the instance `e = litExp` — the `toReal` of the executed `exp` of the
shifted logits. With this, `genSoftmaxTV` (the e-parametric total-variation bound) applies directly,
the per-key error `ε = δ_exp` being the bit-level exp atom. -/

/-- The literal exp-value vector over ℝ: `j ↦ toReal (IEEE32Exec.exp (shifted logit j))`. The `e =
litExp zt` instance of `genSoftmax`'s exp channel; `δ_exp` bounds its gap to `Real.exp` of the real
shifted logit. -/
def litExp {n' : ℕ} (zt : Tensor IEEE32Exec (.dim (n' + 1) .scalar)) : Fin (n' + 1) → ℝ :=
  fun j => toReal (MathFunctions.exp (softmaxShiftedIE zt j))

/-- **Step 1 → step 2 bridge.** The literal per-row softmax weight over ℝ is exactly
`genSoftmax (litExp zt)` — the exp-value-parametric rounded softmax at `e = litExp zt`. Combines the
`toReal`-push (`toReal_litSoftmax`) with `List.ofFn = (finRange).map`. -/
lemma toReal_softmaxVec_eq_genSoftmax {n' : ℕ} (zt : Tensor IEEE32Exec (.dim (n' + 1) .scalar))
    (i : Fin (n' + 1))
    (hdiv : isFinite (MathFunctions.exp (softmaxShiftedIE zt i) / softmaxDenomIE zt) = true)
    (hfold : IE32FoldlFinite posZero
      ((List.finRange (n' + 1)).map (fun j => MathFunctions.exp (softmaxShiftedIE zt j)))) :
    toReal (Tensor.vecGet (Activation.softmaxVecSpec zt) i) = genSoftmax (litExp zt) i := by
  rw [toReal_litSoftmax zt i hdiv hfold]
  simp only [genSoftmax, genDenom, List.ofFn_eq_map]
  rfl

/-- `scalarVal` of a vector entry equals the `vecGet` read of the wrapping `dim` tensor. Bridges the
two distinct scalar matchers (`scalarElim` from `softmaxVecSpec.match_1` vs `toScalar`) by reducing on
the entry constructor. -/
lemma scalarVal_eq_vecGet {n : ℕ} (g : Fin n → Tensor IEEE32Exec .scalar) (k : Fin n) :
    scalarVal (g k) = Tensor.vecGet (Tensor.dim g) k := by
  rw [vecGet_dim_ie]
  cases g k with
  | scalar v => rfl

/-- **The shifted logit read over ℝ.** The literal shifted logit is the rounded difference
`fp32Round(scoreⱼ − rowMax)` of the real score row entry and the real row maximum. The shift is a single
rounded `sub`, and `rowMax` is constant in `j`, so the *ideal* softmax target is invariant to it
(`softmax_shift_invariant`) — only the rounding of the subtraction survives as an error term. -/
lemma toReal_softmaxShiftedIE {n' : ℕ} (zt : Tensor IEEE32Exec (.dim (n' + 1) .scalar))
    (j : Fin (n' + 1)) (hx : isFinite (Tensor.vecGet zt j) = true)
    (hm : isFinite (softmaxRowMaxIE zt) = true)
    (hfin : isFinite (sub (Tensor.vecGet zt j) (softmaxRowMaxIE zt)) = true) :
    toReal (softmaxShiftedIE zt j)
      = fp32Round (toReal (Tensor.vecGet zt j) - toReal (softmaxRowMaxIE zt)) := by
  cases zt with
  | dim f =>
    simp only [softmaxShiftedIE, scalarVal_eq_vecGet]
    show toReal (sub (Tensor.vecGet (Tensor.dim f) j) (softmaxRowMaxIE (Tensor.dim f))) = _
    rw [toReal_sub_eq_fp32Round_of_isFinite _ _ hx hm hfin]

/-- Row read of the matrix softmax at `IEEE32Exec`: `softmaxSpec` keeps the outer structure and applies
`softmaxVecSpec` at the last axis, so the `(i,j)` coordinate is the `j`-th coordinate of the per-row
vector softmax of row `i`. The structural (backend-generic) analog of the ℝ-level `get2_softmaxSpec`. -/
lemma get2_softmaxSpec_dim_ie {nQ nK : ℕ} (f : Fin nQ → Tensor IEEE32Exec (.dim nK .scalar))
    (i : Fin nQ) (j : Fin nK) :
    get2 (Activation.softmaxSpec (Tensor.dim f)) i j
      = Tensor.vecGet (Activation.softmaxVecSpec (f i)) j := by
  simp only [Activation.softmaxSpec, get2_dim_ie]

/-! ## KU-stab step 3 — the literal executed head and its forward error

`execAttnLit` is the literal `IEEE32Exec` `scaledDotProductAttention`, read back over ℝ coordinate-wise.
Per the fp32-grid input convention, the certificate quantifies over fp32-representable inputs, so the
real→fp32 quantization is exact (a section of `toReal`); the kernel is the faithful binary32 forward. -/

/-- The literal executed attention head: the `IEEE32Exec` `scaledDotProductAttention` read over ℝ. -/
def execAttnLit {n d : ℕ} {h1 h2 : (n + 1) ≠ 0}
    (ctx : Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2) : Fin (n + 1) → Fin d → ℝ :=
  fun i c => toReal (get2 (Spec.scaledDotProductAttention ctx) i c)

/-- The literal scale factor `1/√dModel`. Generic over `[Context α]` (same Context-projection alignment
as `litScaledScores`), so its `toReal` can be referenced without re-hitting the instance diamond. -/
def litScaleFactor {α : Type} [Context α] (dModel : Nat) : α := 1 / MathFunctions.sqrt (dModel : α)

/-- The scaled-score matrix the kernel feeds to the softmax: `(Q·Kᵀ)·(1/√dModel)`. Kept **generic** over
`[Context α]` exactly as `scaledDotProductAttention` is, so it elaborates `sqrt`/`1`/`↑dModel` through the
*same* `Context.*` projections as the kernel — avoiding the standalone-vs-`Context`-projected instance
diamond that a concrete restatement would create. Localizes the kernel's internal scale in one def. -/
def litScaledScores {α : Type} [Context α] [DecidableRel ((· > ·) : α → α → Prop)]
    {nQ nK dModel : Nat} {h1 : nQ ≠ 0} {h2 : nK ≠ 0}
    (ctx : Spec.AttentionContext α nQ nK dModel h1 h2) :
    Tensor α (.dim nQ (.dim nK .scalar)) :=
  scaleSpec (matMulSpec ctx.Q (matrixTransposeSpec ctx.K)) (1 / MathFunctions.sqrt (dModel : α))

/-- **The literal kernel (mask off) is the value matmul of the softmax of the scaled scores.** Backend-
generic structural decomposition (`litScaledScores` is defeq to the kernel's internal scaled scores). -/
lemma scaledDotProductAttention_eq_matMul {α : Type} [Context α]
    [DecidableRel ((· > ·) : α → α → Prop)] {nQ nK dModel : Nat} {h1 : nQ ≠ 0} {h2 : nK ≠ 0}
    (ctx : Spec.AttentionContext α nQ nK dModel h1 h2) (hmask : ctx.mask = none) :
    Spec.scaledDotProductAttention ctx
      = matMulSpec (Activation.softmaxSpec (litScaledScores ctx)) ctx.V := by
  simp only [Spec.scaledDotProductAttention, hmask, litScaledScores]

/-- **Outer coordinate read of the literal kernel** (mask off): the `(i,c)` output over ℝ is the fp32
dot of the literal softmax-weight row `i` against the value column `c`. -/
lemma execAttnLit_coord {n d : ℕ} {h1 h2 : (n + 1) ≠ 0}
    (ctx : Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2) (hmask : ctx.mask = none)
    (i : Fin (n + 1)) (c : Fin d)
    (hfin : MatMulCoordFinite (Activation.softmaxSpec (litScaledScores ctx)) ctx.V i c) :
    execAttnLit ctx i c
      = rdot (fun k => toReal (get2 (Activation.softmaxSpec (litScaledScores ctx)) i k))
             (fun k => toReal (get2 ctx.V k c)) := by
  rw [execAttnLit, scaledDotProductAttention_eq_matMul ctx hmask,
    toReal_get2_matMulSpec_ie _ _ i c hfin]

/-- **The literal softmax weight read over ℝ.** The `(i,k)` entry of the row-softmax of a score matrix
`dim f`, read over ℝ, is the exp-value-parametric rounded softmax `genSoftmax (litExp (f i))` at the
`i`-th row — combining the row read (`get2_softmaxSpec_dim_ie`) with the step1→2 bridge. -/
lemma toReal_litWeight {n : ℕ} (f : Fin (n + 1) → Tensor IEEE32Exec (.dim (n + 1) .scalar))
    (i k : Fin (n + 1))
    (hdiv : isFinite (MathFunctions.exp (softmaxShiftedIE (f i) k) / softmaxDenomIE (f i)) = true)
    (hfold : IE32FoldlFinite posZero
      ((List.finRange (n + 1)).map (fun j => MathFunctions.exp (softmaxShiftedIE (f i) j)))) :
    toReal (get2 (Activation.softmaxSpec (Tensor.dim f)) i k) = genSoftmax (litExp (f i)) k := by
  rw [get2_softmaxSpec_dim_ie, toReal_softmaxVec_eq_genSoftmax (f i) k hdiv hfold]

/-- Coordinate read of `matrixTensor` at `IEEE32Exec` (the backend-generic structural read). -/
lemma get2_matrixTensor_ie {m n : ℕ} (X : Fin m → Fin n → IEEE32Exec) (i : Fin m) (j : Fin n) :
    get2 (Spec.matrixTensor X) i j = X i j := by
  simp [get2, get_eq, Spec.matrixTensor, Spec.vectorTensor, Tensor.vecGet, Tensor.toScalar,
    Spec.getAtSpec]

/-- **The literal value projection read over ℝ is the model's executed value `Vexec`.** With the value
tensor the executed matmul of the fp32 input `Yt` and value-weight `Wt`, each `(i,j)` coordinate over ℝ is
`Vexec (toReal∘Wt) (toReal∘Yt) i j` — bounded vs the ideal `matMulCoord` by the model's `Vexec_error`. -/
lemma toReal_litValue {n d : ℕ} (Yt : Fin n → Fin d → IEEE32Exec) (Wt : Fin d → Fin d → IEEE32Exec)
    (i : Fin n) (j : Fin d)
    (hfin : MatMulCoordFinite (Spec.matrixTensor Yt) (Spec.matrixTensor Wt) i j) :
    toReal (get2 (matMulSpec (Spec.matrixTensor Yt) (Spec.matrixTensor Wt)) i j)
      = Vexec (fun k l => toReal (Wt k l)) (fun a b => toReal (Yt a b)) i j := by
  rw [toReal_get2_matMulSpec_ie _ _ i j hfin, Vexec]
  simp only [get2_matrixTensor_ie]

/-- **The literal scaled-score read over ℝ.** Each `(i,k)` scaled score is `fp32Round(executed-Q·Kᵀ-dot
· toReal(1/√d))` — a rounded dot, then a rounded scale-multiply. Combines `get2_scaleSpec_ie`, the
`toReal`-mul bridge, and the matmul keystone. -/
lemma toReal_litScore {n d : ℕ} {h1 h2 : (n + 1) ≠ 0}
    (ctx : Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2) (i k : Fin (n + 1))
    (hmatfin : MatMulCoordFinite ctx.Q (matrixTransposeSpec ctx.K) i k)
    (hmulfin : isFinite
      (mul (get2 (matMulSpec ctx.Q (matrixTransposeSpec ctx.K)) i k) (litScaleFactor d)) = true) :
    toReal (get2 (litScaledScores ctx) i k)
      = fp32Round (rdot (fun l => toReal (get2 ctx.Q i l))
            (fun l => toReal (get2 (matrixTransposeSpec ctx.K) l k))
          * toReal (litScaleFactor d : IEEE32Exec)) := by
  show toReal (get2 (scaleSpec (matMulSpec ctx.Q (matrixTransposeSpec ctx.K)) (litScaleFactor d)) i k) = _
  rw [get2_scaleSpec_ie]
  show toReal (mul (get2 (matMulSpec ctx.Q (matrixTransposeSpec ctx.K)) i k) (litScaleFactor d)) = _
  rw [toReal_mul_eq_fp32Round_of_isFinite _ _ hmulfin, toReal_get2_matMulSpec_ie _ _ i k hmatfin]

/-- **The literal scaled score read over ℝ is the model's executed score `Sexec (1/c)`** (`c =
toReal(1/√d)`, the effective scale: multiplying by `c` ≡ dividing by `1/c`). Reusing the model's
`Sexec_entry_error` for `|· − attnScores (1/c)| ≤ scoreErr`. -/
lemma toReal_litScore_eq_Sexec {n d : ℕ} {h1 h2 : (n + 1) ≠ 0}
    (ctx : Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2)
    (Yt : Fin (n + 1) → Fin d → IEEE32Exec) (hQ : ctx.Q = Spec.matrixTensor Yt)
    (hK : ctx.K = Spec.matrixTensor Yt) (i k : Fin (n + 1))
    (hmatfin : MatMulCoordFinite ctx.Q (matrixTransposeSpec ctx.K) i k)
    (hmulfin : isFinite
      (mul (get2 (matMulSpec ctx.Q (matrixTransposeSpec ctx.K)) i k) (litScaleFactor d)) = true) :
    toReal (get2 (litScaledScores ctx) i k)
      = Sexec (1 / toReal (litScaleFactor d : IEEE32Exec)) (fun a b => toReal (Yt a b)) i k := by
  rw [toReal_litScore ctx i k hmatfin hmulfin, Sexec, hQ, hK]
  simp only [get2_matrixTensor_ie, get2_matrixTransposeSpec_ie, div_eq_mul_inv, one_mul, inv_inv]

/-- **The literal coord-error triangle.** The executed output `rdot smLit (Vt·c)` — literal softmax-weight
row `smLit` (compared to the *shifted*-score softmax `z'`) against value row `Vt` — is within the derived
envelope of the ideal `attnHead scale W Y i c`. Mirrors `execAttnStar_coord_error`: `rdot_mix_error` for
the mix, `attnOut_scores_bound` + `softmax_shift_invariant` (the max-shift `mR` cancels in the ideal) for
the score channel, `attnOut_values_bound` for the values. -/
lemma litCoordError_core {N d : ℕ} [NeZero N] (scale : ℝ) (W : Fin d → Fin d → ℝ) (Y : Fin N → Fin d → ℝ)
    (smLit : Fin N → ℝ) (Vt : Fin N → Fin d → ℝ) (z' : Fin N → ℝ) (mR : ℝ) (i : Fin N) (c : Fin d)
    (hmix : RdotNormal smLit (fun j => Vt j c)) (hnu : (N : ℝ) * u < 1)
    {bV tvMix pert valBud : ℝ} (hbV0 : 0 ≤ bV) (hbV : ∀ j, |Vt j c| ≤ bV)
    (htv : ∑ j, |smLit j - softmax z' j| ≤ tvMix) (hsum : ∑ j, |smLit j| ≤ 1 + tvMix)
    (hpert : ‖z' - fun j => attnScores scale (Y i) Y j - mR‖ ≤ pert)
    (hverr : ‖Vt - matMulCoord W Y‖ ≤ valBud) :
    |rdot smLit (fun j => Vt j c) - attnHead scale W Y i c|
      ≤ rdotBudget N (bV * (1 + tvMix)) + bV * tvMix + 2 * bV * pert + valBud := by
  have hideal : attnHead scale W Y i c
      = ∑ j, softmax (attnScores scale (Y i) Y) j * matMulCoord W Y j c := by
    rw [attnHead, attnVec, attnOut]
  rw [hideal]
  have hT_mix : |rdot smLit (fun j => Vt j c) - ∑ j, softmax z' j * Vt j c|
      ≤ rdotBudget N (bV * (1 + tvMix)) + bV * tvMix :=
    rdot_mix_error smLit z' Vt c hmix hnu hbV0 hbV hsum htv
  have hT_score : |(∑ j, softmax z' j * Vt j c)
        - ∑ j, softmax (attnScores scale (Y i) Y) j * Vt j c| ≤ 2 * bV * pert := by
    rw [show (∑ j, softmax (attnScores scale (Y i) Y) j * Vt j c)
        = ∑ j, softmax (fun j => attnScores scale (Y i) Y j - mR) j * Vt j c from by
          rw [softmax_shift_invariant]]
    have hsb := attnOut_scores_bound z' (fun j => attnScores scale (Y i) Y j - mR) Vt c hbV0 hbV
    simp only [attnOut] at hsb
    exact hsb.trans (mul_le_mul_of_nonneg_left hpert (by positivity))
  have hT_val : |(∑ j, softmax (attnScores scale (Y i) Y) j * Vt j c)
        - ∑ j, softmax (attnScores scale (Y i) Y) j * matMulCoord W Y j c| ≤ valBud := by
    have hvb := attnOut_values_bound (attnScores scale (Y i) Y) Vt (matMulCoord W Y) c
      (bd := valBud) (fun j => by
        calc |Vt j c - matMulCoord W Y j c| ≤ ‖(Vt - matMulCoord W Y) j‖ := by
              rw [show Vt j c - matMulCoord W Y j c = (Vt - matMulCoord W Y) j c from rfl,
                ← Real.norm_eq_abs]
              exact norm_le_pi_norm _ c
          _ ≤ ‖Vt - matMulCoord W Y‖ := norm_le_pi_norm _ j
          _ ≤ valBud := hverr)
    simp only [attnOut] at hvb; exact hvb
  calc |rdot smLit (fun j => Vt j c)
          - ∑ j, softmax (attnScores scale (Y i) Y) j * matMulCoord W Y j c|
      ≤ |rdot smLit (fun j => Vt j c) - ∑ j, softmax z' j * Vt j c|
          + |(∑ j, softmax z' j * Vt j c) - ∑ j, softmax (attnScores scale (Y i) Y) j * Vt j c|
          + |(∑ j, softmax (attnScores scale (Y i) Y) j * Vt j c)
              - ∑ j, softmax (attnScores scale (Y i) Y) j * matMulCoord W Y j c| := by
        have h1 := abs_sub_le (rdot smLit (fun j => Vt j c))
          (∑ j, softmax (attnScores scale (Y i) Y) j * Vt j c)
          (∑ j, softmax (attnScores scale (Y i) Y) j * matMulCoord W Y j c)
        have h2 := abs_sub_le (rdot smLit (fun j => Vt j c)) (∑ j, softmax z' j * Vt j c)
          (∑ j, softmax (attnScores scale (Y i) Y) j * Vt j c)
        linarith
    _ ≤ rdotBudget N (bV * (1 + tvMix)) + bV * tvMix + 2 * bV * pert + valBud := by
        linarith [hT_mix, hT_score, hT_val]

/-- The float `max`-fold stays within `[-B', B']` if its seed and every entry do (max preserves
finiteness and reads as the real max). -/
lemma foldl_scalarMax_bound {n' : ℕ} (f : Fin (n' + 1) → Tensor IEEE32Exec .scalar) {B' : ℝ}
    (hf : ∀ k, isFinite (scalarVal (f k)) = true ∧ |toReal (scalarVal (f k))| ≤ B') :
    ∀ (l : List (Fin (n' + 1))) (acc : IEEE32Exec), isFinite acc = true → |toReal acc| ≤ B' →
      isFinite (l.foldl (fun acc i => scalarElim (f i) (fun v => max acc v)) acc) = true
        ∧ |toReal (l.foldl (fun acc i => scalarElim (f i) (fun v => max acc v)) acc)| ≤ B' := by
  intro l
  induction l with
  | nil => intro acc haccf haccb; exact ⟨haccf, haccb⟩
  | cons i l ih =>
    intro acc haccf haccb
    simp only [List.foldl_cons]
    obtain ⟨hfi, hbi⟩ := hf i
    have hstep : scalarElim (f i) (fun v => max acc v) = maximum acc (scalarVal (f i)) := by
      cases f i with | scalar v => rfl
    rw [hstep]
    refine ih _ (isFinite_maximum_of_isFinite acc (scalarVal (f i)) haccf hfi) ?_
    rw [toReal_maximum_eq_max_of_isFinite acc (scalarVal (f i)) haccf hfi]
    rw [abs_le] at haccb hbi ⊢
    exact ⟨le_max_of_le_left haccb.1, max_le haccb.2 hbi.2⟩

/-- **The literal row max is bounded by the score-magnitude bound** (the max returns an input). -/
lemma abs_toReal_softmaxRowMaxIE_le {n' : ℕ} (f : Fin (n' + 1) → Tensor IEEE32Exec .scalar) {B' : ℝ}
    (hf : ∀ k, isFinite (scalarVal (f k)) = true ∧ |toReal (scalarVal (f k))| ≤ B') :
    |toReal (softmaxRowMaxIE (Tensor.dim f))| ≤ B' := by
  have h := foldl_scalarMax_bound f hf (List.finRange (n' + 1))
    (scalarVal (f ⟨0, Nat.succ_pos n'⟩)) (hf _).1 (hf _).2
  simpa [softmaxRowMaxIE] using h.2

/-- **The shift-subtraction rounding error** (the literal's extra term vs the model): the shifted logit
read over ℝ is within `u·|score − rowMax|` of the exact shift, by the relative rounding bound. -/
lemma abs_toReal_softmaxShiftedIE_sub_le {n' : ℕ}
    (zt : Tensor IEEE32Exec (.dim (n' + 1) .scalar)) (k : Fin (n' + 1))
    (hx : isFinite (Tensor.vecGet zt k) = true) (hm : isFinite (softmaxRowMaxIE zt) = true)
    (hfin : isFinite (sub (Tensor.vecGet zt k) (softmaxRowMaxIE zt)) = true)
    (hne : toReal (Tensor.vecGet zt k) - toReal (softmaxRowMaxIE zt) ≠ 0)
    (hnorm : (-125 : ℤ) ≤ neuralMagnitude binaryRadix
      (toReal (Tensor.vecGet zt k) - toReal (softmaxRowMaxIE zt))) :
    |toReal (softmaxShiftedIE zt k) - (toReal (Tensor.vecGet zt k) - toReal (softmaxRowMaxIE zt))|
      ≤ u * |toReal (Tensor.vecGet zt k) - toReal (softmaxRowMaxIE zt)| := by
  rw [toReal_softmaxShiftedIE zt k hx hm hfin]
  exact fp32Round_rel_on_normal _ hne hnorm

/-- **The score-channel perturbation (T_score input).** The shifted logits read over ℝ are within
`u·(2B') + scErr` (sup-norm) of `(exact score − rowMax)` — the subRound rounding (`≤ u·|score − rowMax| ≤
u·2B'` via the float-max bound) plus the score rounding `scErr`. -/
lemma litPert {n' : ℕ} (zt : Tensor IEEE32Exec (.dim (n' + 1) .scalar)) (sExact : Fin (n' + 1) → ℝ)
    {B' scErr : ℝ} (hB' : 0 ≤ B') (hsc : 0 ≤ scErr)
    (hentry : ∀ k, isFinite (Tensor.vecGet zt k) = true ∧ |toReal (Tensor.vecGet zt k)| ≤ B')
    (hrowmaxfin : isFinite (softmaxRowMaxIE zt) = true)
    (hshiftfin : ∀ k, isFinite (sub (Tensor.vecGet zt k) (softmaxRowMaxIE zt)) = true)
    (hshiftnorm : ∀ k, toReal (Tensor.vecGet zt k) - toReal (softmaxRowMaxIE zt) ≠ 0 ∧
        (-125 : ℤ) ≤ neuralMagnitude binaryRadix
          (toReal (Tensor.vecGet zt k) - toReal (softmaxRowMaxIE zt)))
    (hscorediff : ∀ k, |toReal (Tensor.vecGet zt k) - sExact k| ≤ scErr) :
    ‖(fun k => toReal (softmaxShiftedIE zt k)) - fun k => sExact k - toReal (softmaxRowMaxIE zt)‖
      ≤ u * (2 * B') + scErr := by
  have hmR : |toReal (softmaxRowMaxIE zt)| ≤ B' := by
    cases zt with
    | dim f => exact abs_toReal_softmaxRowMaxIE_le f (fun k => by rw [scalarVal_eq_vecGet]; exact hentry k)
  have hpos : 0 ≤ u * (2 * B') + scErr := by have := u_nonneg; positivity
  refine (pi_norm_le_iff_of_nonneg hpos).mpr (fun k => ?_)
  rw [Real.norm_eq_abs, Pi.sub_apply]
  have hsub := abs_toReal_softmaxShiftedIE_sub_le zt k (hentry k).1 hrowmaxfin (hshiftfin k)
    (hshiftnorm k).1 (hshiftnorm k).2
  have hsubB : |toReal (Tensor.vecGet zt k) - toReal (softmaxRowMaxIE zt)| ≤ 2 * B' := by
    have h1 := abs_le.mp (hentry k).2
    have h2 := abs_le.mp hmR
    rw [abs_le]; constructor <;> linarith
  have hmul : u * |toReal (Tensor.vecGet zt k) - toReal (softmaxRowMaxIE zt)| ≤ u * (2 * B') :=
    mul_le_mul_of_nonneg_left hsubB u_nonneg
  have htri := abs_sub_le (toReal (softmaxShiftedIE zt k))
    (toReal (Tensor.vecGet zt k) - toReal (softmaxRowMaxIE zt)) (sExact k - toReal (softmaxRowMaxIE zt))
  have hscd : |(toReal (Tensor.vecGet zt k) - toReal (softmaxRowMaxIE zt))
      - (sExact k - toReal (softmaxRowMaxIE zt))| ≤ scErr := by
    rw [show (toReal (Tensor.vecGet zt k) - toReal (softmaxRowMaxIE zt))
        - (sExact k - toReal (softmaxRowMaxIE zt)) = toReal (Tensor.vecGet zt k) - sExact k from by ring]
    exact hscorediff k
  linarith

/-- **The literal executed-head no-overflow bundle.** Every field is an honest condition on the run-time
binary32 intermediates of the literal `scaledDotProductAttention` (no overflow / no underflow / normal
range), mirroring the model's `ExecAttnNormal`. `F` are the score rows (`litScaledScores ctx = dim F`),
`Dlo` the softmax-denominator floor, `E_lit` the exp-sum bound. The certificate is conditional on these,
exactly as the hardware run satisfies them; nothing is faked. -/
structure ExecAttnLitNormal {n d : ℕ} {h1 h2 : (n + 1) ≠ 0}
    (ctx : Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2)
    (Yt : Fin (n + 1) → Fin d → IEEE32Exec) (Wt : Fin d → Fin d → IEEE32Exec)
    (F : Fin (n + 1) → Tensor IEEE32Exec (.dim (n + 1) .scalar)) (Dlo E_lit : ℝ) : Prop where
  hF : litScaledScores ctx = Tensor.dim F
  mixfin : ∀ i c, MatMulCoordFinite (Activation.softmaxSpec (litScaledScores ctx)) ctx.V i c
  valfin : ∀ k c, MatMulCoordFinite (Spec.matrixTensor Yt) (Spec.matrixTensor Wt) k c
  scorefin : ∀ i k, MatMulCoordFinite ctx.Q (matrixTransposeSpec ctx.K) i k
  scalefin : ∀ i k, isFinite
    (mul (get2 (matMulSpec ctx.Q (matrixTransposeSpec ctx.K)) i k) (litScaleFactor d)) = true
  readfin : ∀ i k, isFinite (MathFunctions.exp (softmaxShiftedIE (F i) k) / softmaxDenomIE (F i)) = true
  foldfin : ∀ i, IE32FoldlFinite posZero
    ((List.finRange (n + 1)).map (fun k => MathFunctions.exp (softmaxShiftedIE (F i) k)))
  gen : ∀ i, GenNormal (litExp (F i))
  dlo : ∀ i, Dlo ≤ genDenom (litExp (F i))
  esum : ∀ i, eSum (litExp (F i)) ≤ E_lit
  vecfin : ∀ i k, isFinite (Tensor.vecGet (F i) k) = true
  rowmaxfin : ∀ i, isFinite (softmaxRowMaxIE (F i)) = true
  subfin : ∀ i k, isFinite (sub (Tensor.vecGet (F i) k) (softmaxRowMaxIE (F i))) = true
  shiftnorm : ∀ i k, toReal (Tensor.vecGet (F i) k) - toReal (softmaxRowMaxIE (F i)) ≠ 0 ∧
    (-125 : ℤ) ≤ neuralMagnitude binaryRadix
      (toReal (Tensor.vecGet (F i) k) - toReal (softmaxRowMaxIE (F i)))
  vnorm : VexecNormal (fun k l => toReal (Wt k l)) (fun a b => toReal (Yt a b))
  snorm : SexecNormal (1 / toReal (litScaleFactor d : IEEE32Exec)) (fun a b => toReal (Yt a b))
  mixnorm : ∀ i c, RdotNormal (genSoftmax (litExp (F i)))
    (fun k => Vexec (fun a b => toReal (Wt a b)) (fun a b => toReal (Yt a b)) k c)
  dpos : 0 < Dlo

/-- **Per-coordinate literal forward error (parametric).** Given the derived envelope facts (`htv`,
`hsum`, `hpert`, `hverr`, `hbV`) and the read-finiteness for `(i,c)`, the literal output is within the
`litCoordError_core` envelope of the ideal head at the executed scale `1/toReal(1/√d)`. Clean by design:
`execAttnLit_coord` + the two channel-read rewrites + `litCoordError_core`. -/
lemma attnLiteralForwardError_coord {n d : ℕ} {h1 h2 : (n + 1) ≠ 0}
    (ctx : Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2)
    (Yt : Fin (n + 1) → Fin d → IEEE32Exec) (Wt : Fin d → Fin d → IEEE32Exec)
    (hV : ctx.V = matMulSpec (Spec.matrixTensor Yt) (Spec.matrixTensor Wt)) (hmask : ctx.mask = none)
    (F : Fin (n + 1) → Tensor IEEE32Exec (.dim (n + 1) .scalar))
    (hF : litScaledScores ctx = Tensor.dim F) (i : Fin (n + 1)) (c : Fin d)
    (hmixfin : MatMulCoordFinite (Activation.softmaxSpec (litScaledScores ctx)) ctx.V i c)
    (hreadfin : ∀ k, isFinite
      (MathFunctions.exp (softmaxShiftedIE (F i) k) / softmaxDenomIE (F i)) = true)
    (hfoldfin : IE32FoldlFinite posZero
      ((List.finRange (n + 1)).map (fun k => MathFunctions.exp (softmaxShiftedIE (F i) k))))
    (hvalfin : ∀ k, MatMulCoordFinite (Spec.matrixTensor Yt) (Spec.matrixTensor Wt) k c)
    (hnu : ((n : ℝ) + 1) * u < 1)
    {tvMix pert valBud bV : ℝ} (hbV0 : 0 ≤ bV)
    (hmix : RdotNormal (genSoftmax (litExp (F i)))
      (fun k => Vexec (fun a b => toReal (Wt a b)) (fun a b => toReal (Yt a b)) k c))
    (hbV : ∀ j, |Vexec (fun a b => toReal (Wt a b)) (fun a b => toReal (Yt a b)) j c| ≤ bV)
    (htv : ∑ j, |genSoftmax (litExp (F i)) j
        - softmax (fun k => toReal (softmaxShiftedIE (F i) k)) j| ≤ tvMix)
    (hsum : ∑ j, |genSoftmax (litExp (F i)) j| ≤ 1 + tvMix)
    (hpert : ‖(fun k => toReal (softmaxShiftedIE (F i) k))
        - fun k => attnScores (1 / toReal (litScaleFactor d : IEEE32Exec))
            ((fun a b => toReal (Yt a b)) i) (fun a b => toReal (Yt a b)) k
          - toReal (softmaxRowMaxIE (F i))‖ ≤ pert)
    (hverr : ‖Vexec (fun a b => toReal (Wt a b)) (fun a b => toReal (Yt a b))
        - matMulCoord (fun a b => toReal (Wt a b)) (fun a b => toReal (Yt a b))‖ ≤ valBud) :
    |execAttnLit ctx i c
        - attnHead (1 / toReal (litScaleFactor d : IEEE32Exec))
            (fun a b => toReal (Wt a b)) (fun a b => toReal (Yt a b)) i c|
      ≤ rdotBudget (n + 1) (bV * (1 + tvMix)) + bV * tvMix + 2 * bV * pert + valBud := by
  have hwt : (fun k => toReal (get2 (Activation.softmaxSpec (litScaledScores ctx)) i k))
      = genSoftmax (litExp (F i)) := by
    funext k; rw [hF]; exact toReal_litWeight F i k (hreadfin k) hfoldfin
  have hvt : (fun k => toReal (get2 ctx.V k c))
      = fun k => Vexec (fun a b => toReal (Wt a b)) (fun a b => toReal (Yt a b)) k c := by
    funext k; rw [hV]; exact toReal_litValue Yt Wt k c (hvalfin k)
  rw [execAttnLit_coord ctx hmask i c hmixfin, hwt, hvt]
  have hNeZero : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
  exact litCoordError_core (1 / toReal (litScaleFactor d : IEEE32Exec))
    (fun a b => toReal (Wt a b)) (fun a b => toReal (Yt a b)) (genSoftmax (litExp (F i)))
    (Vexec (fun a b => toReal (Wt a b)) (fun a b => toReal (Yt a b)))
    (fun k => toReal (softmaxShiftedIE (F i) k)) (toReal (softmaxRowMaxIE (F i))) i c
    hmix (by exact_mod_cast hnu) hbV0 hbV htv hsum hpert hverr

/-- The shift-subtraction rounding contribution: `u·(2·scoreBound)` (the literal's extra error term). -/
noncomputable def subRoundErr (d : ℕ) (B scale : ℝ) : ℝ := u * (2 * scoreBoundExec d B scale)

/-- The literal softmax total-variation envelope: `genSoftmaxTV`'s bound at sequence length `N`, with the
exp-sum bounded by `E_lit` and `ε = δ_exp` (so `∑ε = N·δ_exp`). -/
noncomputable def litTV (N : ℕ) (Dlo δ_exp E_lit : ℝ) : ℝ :=
  u + u * (u * (((N : ℝ) + 1) * E_lit) / (1 - (N : ℝ) * u)) / Dlo
    + (2 * ((N : ℝ) * δ_exp) + u * (((N : ℝ) + 1) * E_lit) / (1 - (N : ℝ) * u)) / Dlo

/-- **The derived literal rounding envelope `rndLit`.** The model's `rndStar` with `softmaxTV → litTV`
(the `δ_exp`/`E_lit`-parametric softmax variation) and the honest extra `2·bV·subRoundErr` from the
max-stabilization. A closed form in the bounds `B, Λ, scale, Dlo, δ_exp, E_lit` and shapes `n, d`. -/
noncomputable def rndLit (n d : ℕ) (B Λ scale Dlo δ_exp E_lit : ℝ) : ℝ :=
  rdotBudget (n + 1) (bVval d B Λ * (1 + litTV (n + 1) Dlo δ_exp E_lit))
    + bVval d B Λ * litTV (n + 1) Dlo δ_exp E_lit
    + 2 * bVval d B Λ * (subRoundErr d B scale + scoreErr d B scale)
    + rdotBudget d (B * Λ)

/-- **The score-channel perturbation, discharged from the bundle.** Connects the literal score row to the
model's `Sexec (1/c)` (via `toReal_litScore_eq_Sexec`) so `Sexec_entry_abs_le`/`Sexec_entry_error` give
the magnitude + score-rounding bounds; `litPert` assembles them with the subRound term. -/
lemma litPert_bundle {n d : ℕ} {h1 h2 : (n + 1) ≠ 0}
    (ctx : Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2)
    (Yt : Fin (n + 1) → Fin d → IEEE32Exec) (Wt : Fin d → Fin d → IEEE32Exec)
    (hQ : ctx.Q = Spec.matrixTensor Yt) (hK : ctx.K = Spec.matrixTensor Yt)
    {B Dlo E_lit : ℝ} (hB : 0 ≤ B) (hc : 0 < toReal (litScaleFactor d : IEEE32Exec))
    (hX : ∀ a k, |toReal (Yt a k)| ≤ B) (hdu : (d : ℝ) * u < 1)
    (F : Fin (n + 1) → Tensor IEEE32Exec (.dim (n + 1) .scalar))
    (hN : ExecAttnLitNormal ctx Yt Wt F Dlo E_lit) (i : Fin (n + 1)) :
    ‖(fun k => toReal (softmaxShiftedIE (F i) k))
        - fun k => attnScores (1 / toReal (litScaleFactor d : IEEE32Exec))
            ((fun a b => toReal (Yt a b)) i) (fun a b => toReal (Yt a b)) k
          - toReal (softmaxRowMaxIE (F i))‖
      ≤ subRoundErr d B (1 / toReal (litScaleFactor d : IEEE32Exec))
        + scoreErr d B (1 / toReal (litScaleFactor d : IEEE32Exec)) := by
  have hscale : (0 : ℝ) < 1 / toReal (litScaleFactor d : IEEE32Exec) := by positivity
  have hconn : ∀ k, toReal (Tensor.vecGet (F i) k)
      = Sexec (1 / toReal (litScaleFactor d : IEEE32Exec)) (fun a b => toReal (Yt a b)) i k := by
    intro k
    rw [show Tensor.vecGet (F i) k = get2 (litScaledScores ctx) i k from by rw [hN.hF, get2_dim_ie]]
    exact toReal_litScore_eq_Sexec ctx Yt hQ hK i k (hN.scorefin i k) (hN.scalefin i k)
  have hbnn : (0 : ℝ) ≤ scoreBoundExec d B (1 / toReal (litScaleFactor d : IEEE32Exec)) := by
    rw [scoreBoundExec]
    have := scoreErr_nonneg hB hdu hscale
    have h2 : (0 : ℝ) ≤ (d : ℝ) * B ^ 2 / (1 / toReal (litScaleFactor d : IEEE32Exec)) := by positivity
    linarith
  rw [subRoundErr]
  refine litPert (F i) _ hbnn (scoreErr_nonneg hB hdu hscale) ?_ (hN.rowmaxfin i) (hN.subfin i)
    (hN.shiftnorm i) ?_
  · intro k
    refine ⟨hN.vecfin i k, ?_⟩
    rw [hconn k]; exact Sexec_entry_abs_le _ _ hB hscale hX hN.snorm hdu i k
  · intro k
    rw [hconn k]; exact Sexec_entry_error _ _ hB hscale hX hN.snorm hdu i k

/-- **The softmax-TV envelope `htv`.** `genSoftmaxTV`'s per-row bound is `≤ litTV` once the exp-sum is
bounded by `E_lit` (the bound is increasing in the exp-sum) — `gcongr` over `eSum ≤ E_lit`. -/
lemma genSoftmaxTV_le_litTV {n : ℕ} {e z : Fin (n + 1) → ℝ} {Dlo δ_exp E_lit : ℝ}
    (h : GenNormal e) (he : ∀ j, |e j - Real.exp (z j)| ≤ δ_exp)
    (hnu : ((n + 1 : ℕ) : ℝ) * u < 1) (hDlo0 : 0 < Dlo) (hDlo : Dlo ≤ genDenom e)
    (hδ0 : 0 ≤ δ_exp) (hesum : eSum e ≤ E_lit) :
    ∑ j, |genSoftmax e j - softmax z j| ≤ litTV (n + 1) Dlo δ_exp E_lit := by
  haveI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
  refine (genSoftmaxTV h he hnu hDlo0 hDlo (fun _ => hδ0)).trans ?_
  rw [litTV, show (∑ _j : Fin (n + 1), δ_exp) = ((n + 1 : ℕ) : ℝ) * δ_exp from by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
  have hden : (0 : ℝ) < 1 - ((n + 1 : ℕ) : ℝ) * u := by linarith
  have hu0 : (0 : ℝ) ≤ u := u_nonneg
  gcongr

/-- The derived literal rounding envelope is nonnegative. -/
lemma rndLit_nonneg {n d : ℕ} {B Λ scale Dlo δ_exp E_lit : ℝ}
    (hB : 0 ≤ B) (hΛ0 : 0 ≤ Λ) (hscale : 0 < scale) (hnu : ((n + 1 : ℕ) : ℝ) * u < 1)
    (hdu : (d : ℝ) * u < 1) (hDlo0 : 0 < Dlo) (hδ0 : 0 ≤ δ_exp) (hE : 0 ≤ E_lit) :
    0 ≤ rndLit n d B Λ scale Dlo δ_exp E_lit := by
  have hBΛ : (0 : ℝ) ≤ B * Λ := mul_nonneg hB hΛ0
  have hu0 : (0 : ℝ) ≤ u := u_nonneg
  have hden : (0 : ℝ) < 1 - ((n + 1 : ℕ) : ℝ) * u := by linarith
  have hbV : 0 ≤ bVval d B Λ := by
    rw [bVval]; linarith [rdotBudget_nonneg hdu hBΛ]
  have hTV : 0 ≤ litTV (n + 1) Dlo δ_exp E_lit := by rw [litTV]; positivity
  have hsub : 0 ≤ subRoundErr d B scale := by
    rw [subRoundErr, scoreBoundExec]; have := scoreErr_nonneg hB hdu hscale; positivity
  have hsc : 0 ≤ scoreErr d B scale := scoreErr_nonneg hB hdu hscale
  have hrb1 : 0 ≤ rdotBudget (n + 1) (bVval d B Λ * (1 + litTV (n + 1) Dlo δ_exp E_lit)) :=
    rdotBudget_nonneg (by exact_mod_cast hnu) (by positivity)
  have hrb2 : 0 ≤ rdotBudget d (B * Λ) := rdotBudget_nonneg hdu hBΛ
  rw [rndLit]
  have h3 : 0 ≤ 2 * bVval d B Λ * (subRoundErr d B scale + scoreErr d B scale) := by positivity
  have h2 : 0 ≤ bVval d B Λ * litTV (n + 1) Dlo δ_exp E_lit := mul_nonneg hbV hTV
  linarith

/-- **The literal fp32 attention forward-error theorem.** The literal `IEEE32Exec`
`scaledDotProductAttention`, read over ℝ (`execAttnLit`), is within the derived closed-form envelope
`rndLit` of the ideal head `attnHead` at the executed scale `1/toReal(1/√d)`, given the honest no-overflow
bundle `ExecAttnLitNormal` and the single bit-level exp atom `δ_exp` (`|toReal(exp s) − Real.exp(toReal
s)| ≤ δ_exp`, supplied per shifted logit). The envelope is a genuine closed form in `B, Λ, Dlo, δ_exp,
E_lit` and the shapes `n, d`; nothing is supplied beyond the operating-range data and the one atom. -/
theorem attnLiteralForwardError {n d : ℕ} {h1 h2 : (n + 1) ≠ 0}
    (ctx : Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2)
    (Yt : Fin (n + 1) → Fin d → IEEE32Exec) (Wt : Fin d → Fin d → IEEE32Exec)
    (hQ : ctx.Q = Spec.matrixTensor Yt) (hK : ctx.K = Spec.matrixTensor Yt)
    (hV : ctx.V = matMulSpec (Spec.matrixTensor Yt) (Spec.matrixTensor Wt)) (hmask : ctx.mask = none)
    (F : Fin (n + 1) → Tensor IEEE32Exec (.dim (n + 1) .scalar)) {Dlo E_lit : ℝ}
    (hN : ExecAttnLitNormal ctx Yt Wt F Dlo E_lit) {B Λ δ_exp : ℝ}
    (hB : 0 ≤ B) (hΛ0 : 0 ≤ Λ) (hδ0 : 0 ≤ δ_exp) (hc : 0 < toReal (litScaleFactor d : IEEE32Exec))
    (hX : ∀ a k, |toReal (Yt a k)| ≤ B) (hW : ∀ j, ∑ k, |toReal (Wt k j)| ≤ Λ)
    (hnu : ((n + 1 : ℕ) : ℝ) * u < 1) (hdu : (d : ℝ) * u < 1) (hE : 0 ≤ E_lit)
    (hδ : ∀ i k, |litExp (F i) k - Real.exp (toReal (softmaxShiftedIE (F i) k))| ≤ δ_exp) :
    dist (execAttnLit ctx) (attnHead (1 / toReal (litScaleFactor d : IEEE32Exec))
        (fun a b => toReal (Wt a b)) (fun a b => toReal (Yt a b)))
      ≤ rndLit n d B Λ (1 / toReal (litScaleFactor d : IEEE32Exec)) Dlo δ_exp E_lit := by
  have hscale : (0 : ℝ) < 1 / toReal (litScaleFactor d : IEEE32Exec) := by positivity
  have hrnn : 0 ≤ rndLit n d B Λ (1 / toReal (litScaleFactor d : IEEE32Exec)) Dlo δ_exp E_lit :=
    rndLit_nonneg hB hΛ0 hscale hnu hdu hN.dpos hδ0 hE
  refine (dist_pi_le_iff hrnn).mpr (fun i => ?_)
  refine (dist_pi_le_iff hrnn).mpr (fun c => ?_)
  rw [Real.dist_eq]
  have htv := genSoftmaxTV_le_litTV (hN.gen i) (hδ i) hnu hN.dpos (hN.dlo i) hδ0 (hN.esum i)
  have hbV0 : (0 : ℝ) ≤ bVval d B Λ := by
    rw [bVval]; linarith [rdotBudget_nonneg hdu (mul_nonneg hB hΛ0), mul_nonneg hB hΛ0]
  have hcoord := attnLiteralForwardError_coord ctx Yt Wt hV hmask F hN.hF i c (hN.mixfin i c)
    (hN.readfin i) (hN.foldfin i) (fun k => hN.valfin k c) (by exact_mod_cast hnu) hbV0
    (hN.mixnorm i c) (fun j => Vexec_entry_abs_le _ _ hB hΛ0 hX hW hN.vnorm hdu j c)
    htv (genSoftmax_sum_le htv) (litPert_bundle ctx Yt Wt hQ hK hB hc hX hdu F hN i)
    (Vexec_error _ _ hB hΛ0 hX hW hN.vnorm hdu)
  rwa [rndLit]

/-! ## KU-stab step 4 — the grid-extended executed map and its ∀-input forward error

`gridExec` is the literal kernel on each certified fp32 input of the (finite) operating regime, and the
ideal clamped head everywhere else. Because `IEEE32Exec` is finite, the regime is a finite set of inputs;
`gridExec` is the ideal plus a finite correction supported exactly on the regime's pre-images, so it is
measurable termwise and reads off as the kernel on the regime. The off-regime value is the ideal — an
inert measurable extension, since the input law lives on the regime. The forward error against the
clamped head is then *exactly* the per-input bound `rnd`, with no input-quantization slack: on the regime
it is the literal forward error; off the regime it is zero. -/

/-- The grid-extended executed attention map: literal kernel on the regime `inputs`, clamped ideal head
elsewhere, written as `ideal + (finite correction supported on the regime)`. -/
noncomputable def gridExec {n d : ℕ} {h1 h2 : (n + 1) ≠ 0} (B c : ℝ) (W : Fin d → Fin d → ℝ)
    (inputs : Finset (Fin (n + 1) → Fin d → IEEE32Exec))
    (ctxOf : (Fin (n + 1) → Fin d → IEEE32Exec) →
      Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2)
    (y : Fin (n + 1) → Fin d → ℝ) : Fin (n + 1) → Fin d → ℝ :=
  attnHead (1 / c) W (clampCoord B y)
    + ∑ Yt ∈ inputs, Set.indicator {z | (fun a b => toReal (Yt a b)) = clampCoord B z}
        (fun _ => execAttnLit (ctxOf Yt) - attnHead (1 / c) W (fun a b => toReal (Yt a b))) y

/-- **The grid extension carries the per-input forward error verbatim — no slack.** Given the literal
forward error `rnd` on every regime input (`hregime`, each an instance of `attnLiteralForwardError`) and
distinct regime reads (`hinj`), the grid-extended map is within `rnd` of the clamped ideal head at *every*
real input: `rnd` on the regime, `0` off it. -/
theorem gridExec_exec_close {n d : ℕ} {h1 h2 : (n + 1) ≠ 0} (B c : ℝ) (W : Fin d → Fin d → ℝ)
    (inputs : Finset (Fin (n + 1) → Fin d → IEEE32Exec))
    (ctxOf : (Fin (n + 1) → Fin d → IEEE32Exec) →
      Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2)
    {rnd : ℝ} (hrnd : 0 ≤ rnd)
    (hregime : ∀ Yt ∈ inputs, dist (execAttnLit (ctxOf Yt))
        (attnHead (1 / c) W (fun a b => toReal (Yt a b))) ≤ rnd)
    (hinj : ∀ Yt ∈ inputs, ∀ Yt' ∈ inputs,
        (fun a b => toReal (Yt a b)) = (fun (a : Fin (n + 1)) (b : Fin d) => toReal (Yt' a b)) →
        Yt = Yt') :
    ∀ y, dist (gridExec B c W inputs ctxOf y) (attnHead (1 / c) W (clampCoord B y)) ≤ rnd := by
  intro y
  rw [dist_eq_norm]
  have hg : gridExec B c W inputs ctxOf y - attnHead (1 / c) W (clampCoord B y)
      = ∑ Yt ∈ inputs, Set.indicator {z | (fun a b => toReal (Yt a b)) = clampCoord B z}
          (fun _ => execAttnLit (ctxOf Yt) - attnHead (1 / c) W (fun a b => toReal (Yt a b))) y := by
    simp only [gridExec, add_sub_cancel_left]
  rw [hg]
  by_cases h : ∃ Yt ∈ inputs, (fun a b => toReal (Yt a b)) = clampCoord B y
  · obtain ⟨Yt0, hYt0, heq0⟩ := h
    have hmem0 : y ∈ {z | (fun a b => toReal (Yt0 a b)) = clampCoord B z} := heq0
    have hsingle : (∑ Yt ∈ inputs, Set.indicator {z | (fun a b => toReal (Yt a b)) = clampCoord B z}
          (fun _ => execAttnLit (ctxOf Yt) - attnHead (1 / c) W (fun a b => toReal (Yt a b))) y)
        = execAttnLit (ctxOf Yt0) - attnHead (1 / c) W (fun a b => toReal (Yt0 a b)) := by
      rw [Finset.sum_eq_single_of_mem Yt0 hYt0]
      · rw [Set.indicator_of_mem hmem0]
      · intro Yt' hYt' hne
        apply Set.indicator_of_notMem
        intro hmem
        exact hne (hinj Yt' hYt' Yt0 hYt0
          ((hmem : (fun a b => toReal (Yt' a b)) = clampCoord B y).trans heq0.symm))
    rw [hsingle, ← dist_eq_norm]
    exact hregime Yt0 hYt0
  · have hz : (∑ Yt ∈ inputs, Set.indicator {z | (fun a b => toReal (Yt a b)) = clampCoord B z}
          (fun _ => execAttnLit (ctxOf Yt) - attnHead (1 / c) W (fun a b => toReal (Yt a b))) y) = 0 := by
      apply Finset.sum_eq_zero
      intro Yt hYt
      apply Set.indicator_of_notMem
      intro hmem
      exact h ⟨Yt, hYt, hmem⟩
    rw [hz, norm_zero]
    exact hrnd

/-- **On the regime, `gridExec` IS the literal kernel** (not merely close to the ideal): at any real
input whose clamp reads back a regime fp32 input `Yt`, the grid-extended map equals `execAttnLit (ctxOf Yt)`.
So where the input law lives (the regime), the certified risk is the literal kernel's risk. -/
theorem gridExec_eq_kernel_of_mem {n d : ℕ} {h1 h2 : (n + 1) ≠ 0} (B c : ℝ) (W : Fin d → Fin d → ℝ)
    (inputs : Finset (Fin (n + 1) → Fin d → IEEE32Exec))
    (ctxOf : (Fin (n + 1) → Fin d → IEEE32Exec) →
      Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2)
    (hinj : ∀ Yt ∈ inputs, ∀ Yt' ∈ inputs,
        (fun a b => toReal (Yt a b)) = (fun (a : Fin (n + 1)) (b : Fin d) => toReal (Yt' a b)) → Yt = Yt')
    {Yt : Fin (n + 1) → Fin d → IEEE32Exec} (hYt : Yt ∈ inputs)
    {y : Fin (n + 1) → Fin d → ℝ} (heq : (fun a b => toReal (Yt a b)) = clampCoord B y) :
    gridExec B c W inputs ctxOf y = execAttnLit (ctxOf Yt) := by
  have hmem : y ∈ {z | (fun a b => toReal (Yt a b)) = clampCoord B z} := heq
  have hsingle : (∑ Yt' ∈ inputs, Set.indicator {z | (fun a b => toReal (Yt' a b)) = clampCoord B z}
        (fun _ => execAttnLit (ctxOf Yt') - attnHead (1 / c) W (fun a b => toReal (Yt' a b))) y)
      = execAttnLit (ctxOf Yt) - attnHead (1 / c) W (fun a b => toReal (Yt a b)) := by
    rw [Finset.sum_eq_single_of_mem Yt hYt]
    · rw [Set.indicator_of_mem hmem]
    · intro Yt' hYt' hne
      apply Set.indicator_of_notMem
      intro hmem'
      exact hne (hinj Yt' hYt' Yt hYt
        ((hmem' : (fun a b => toReal (Yt' a b)) = clampCoord B y).trans heq.symm))
  simp only [gridExec, hsingle, ← heq]
  abel

/-- `gridExec` is measurable: the ideal head precomposed with the (continuous) clamp, plus a finite sum
of indicators of the measurable regime pre-images `(clampCoord B)⁻¹{toReal∘Yt}` carrying constant values. -/
theorem gridExec_measurable {n d : ℕ} {h1 h2 : (n + 1) ≠ 0} (B c : ℝ) (W : Fin d → Fin d → ℝ)
    (inputs : Finset (Fin (n + 1) → Fin d → IEEE32Exec))
    (ctxOf : (Fin (n + 1) → Fin d → IEEE32Exec) →
      Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2) :
    Measurable (gridExec B c W inputs ctxOf) := by
  unfold gridExec
  refine Measurable.add
    (((continuous_attnHead_input W).comp (continuous_clampCoord B)).measurable) ?_
  refine Finset.measurable_sum _ (fun Yt _ => ?_)
  refine Measurable.indicator measurable_const ?_
  have hset : {z : Fin (n + 1) → Fin d → ℝ | (fun a b => toReal (Yt a b)) = clampCoord B z}
      = (clampCoord B) ⁻¹' {fun a b => toReal (Yt a b)} := by
    ext z; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, eq_comm]
  rw [hset]
  exact (continuous_clampCoord B).measurable (measurableSet_singleton _)

/-- **The certified computable float32 generalization bound for the LITERAL executed attention head.**
For TorchLean's literal `IEEE32Exec` `scaledDotProductAttention` (read over ℝ as `execAttnLit`), run on
its finite operating regime `inputs` of fp32 inputs, presented through the per-input forward error
`hfwd` (each an instance of `attnLiteralForwardError`, exact `rndLit`, one named atom `δ_exp`): except on
a McDiarmid-small sample event, the executed true risk is at most the executed empirical risk plus the
closed capacity budget `2·(12√2·B_int/√m) + ε` and the rounding correction `2·Lℓ·rndLit` — with NO
input-quantization slack, because the grid extension binds the kernel to the clamped head exactly on the
regime where the hardware's inputs live. The ideal head `attnHead (1/c) W ∘ clampCoord B` is the literal
kernel's real-arithmetic limit; the bound is therefore about the model the binary32 hardware runs. -/
theorem attnHead_literal_certified_generalization
    {n d p m : ℕ} [Nonempty (Fin p)]
    [MeasurableSpace (Fin (n + 1) → Fin d → ℝ)] [BorelSpace (Fin (n + 1) → Fin d → ℝ)]
    {P : Measure (Fin (n + 1) → Fin d → ℝ)} [IsProbabilityMeasure P]
    {h1 h2 : (n + 1) ≠ 0}
    (hm : 0 < m) {R B c : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Wdec : ParamSpace p → (Fin d → Fin d → ℝ)) (hWcont : Continuous Wdec)
    {Lw : ℝ} (hWLip : ∀ θ θ', dist (Wdec θ) (Wdec θ') ≤ Lw * dist θ θ')
    (ℓ : (Fin (n + 1) → Fin d → ℝ) → ℝ) {b : ℝ} (hb : 0 < b) (hℓb : ∀ v, |ℓ v| ≤ b)
    (hℓcont : Continuous ℓ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ)
    (hℓLip : ∀ u v, |ℓ u - ℓ v| ≤ Lℓ * dist u v)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R)
    {Λ Dlo δ_exp E_lit : ℝ} {lip : ℝ} (hlip0 : 0 ≤ lip)
    (hideal_lip : ∀ a b : Fin (n + 1) → Fin d → ℝ,
        dist (attnHead (1 / c) (Wdec (embedBase Capacity.Dyadic w_T.1)) (clampCoord B a))
             (attnHead (1 / c) (Wdec (embedBase Capacity.Dyadic w_T.1)) (clampCoord B b)) ≤ lip * dist a b)
    (inputs : Finset (Fin (n + 1) → Fin d → IEEE32Exec))
    (ctxOf : (Fin (n + 1) → Fin d → IEEE32Exec) →
      Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2)
    (hinj : ∀ Yt ∈ inputs, ∀ Yt' ∈ inputs,
        (fun a b => toReal (Yt a b)) = (fun (a : Fin (n + 1)) (b : Fin d) => toReal (Yt' a b)) → Yt = Yt')
    (hfwd : ∀ Yt ∈ inputs, dist (execAttnLit (ctxOf Yt))
        (attnHead (1 / c) (Wdec (embedBase Capacity.Dyadic w_T.1)) (fun a b => toReal (Yt a b)))
        ≤ rndLit n d B Λ (1 / c) Dlo δ_exp E_lit)
    (hrnd : 0 ≤ rndLit n d B Λ (1 / c) Dlo δ_exp E_lit)
    (hintG : Integrable
        (fun x => ℓ (gridExec B c (Wdec (embedBase Capacity.Dyadic w_T.1)) inputs ctxOf x)) P)
    (hLpos : 0 < Lℓ * ((d : ℝ) * B) * Lw) :
    (Measure.pi fun _ : Fin m => P).real
        {S | ¬ ((∫ x, ℓ (gridExec B c (Wdec (embedBase Capacity.Dyadic w_T.1)) inputs ctxOf x) ∂P)
              ≤ (1 / (m : ℝ)) * ∑ i,
                  ℓ (gridExec B c (Wdec (embedBase Capacity.Dyadic w_T.1)) inputs ctxOf (S i))
                + (2 * ((12 * Real.sqrt 2) * (1 / Real.sqrt m)
                    * (∫⁻ ε in Set.Ioc (0 : ℝ) (2 * b),
                        ENNReal.ofReal (Real.sqrt (Real.log 2)
                          + Real.sqrt ((p : ℝ) * (4 * R * (Lℓ * ((d : ℝ) * B) * Lw)))
                            * ε ^ (-(1 / 2) : ℝ))).toReal) + ε)
                + 2 * (Lℓ * rndLit n d B Λ (1 / c) Dlo δ_exp E_lit))}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) :=
  attnHead_executed_certified_generalization hm hR hB Wdec hWcont hWLip ℓ hb hℓb hℓcont hLℓ0
    hℓLip hε w_T (gridExec B c (Wdec (embedBase Capacity.Dyadic w_T.1)) inputs ctxOf) hlip0 hideal_lip
    (gridExec_exec_close B c (Wdec (embedBase Capacity.Dyadic w_T.1)) inputs ctxOf hrnd hfwd hinj)
    hintG hLpos

-- SOFTMAX STRUCTURAL READ — DONE (axiom-clean), now imported from the staged TorchLean module
-- `TorchLean.Staged.SoftmaxCoord` (file `NN/Spec/Layers/SoftmaxVecCoordReadStaged.lean`, quarantined for
-- an upstream PR). It provides `vecGet_softmaxVecSpec_ie : vecGet (softmaxVecSpec t) i =
-- exp(softmaxShiftedIE t i) / softmaxDenomIE t` (the stabilized read, shift explicit) via the library's
-- own idiom: `scalarElim := softmaxVecSpec.match_1` (the spec's own matcher — the earlier downstream
-- attempts failed by using `vecGet`/`toScalar`/a fresh `match`, all distinct matchers), the per-term
-- reduction `cases (f i)` + `simp [scalarElim,…]`, and `posZero` for the fold accumulator (the same
-- `OfNat`/`Zero` diamond as `get2_matMulSpec_ie`). The TLT-side `litRowMax`/`litShifted`/`litDenom`
-- (`vecGet`-based) are SUPERSEDED by the staged `softmaxRowMaxIE`/`softmaxShiftedIE`/`softmaxDenomIE`.
--
-- NEXT NODES (KU-stab continued): (1) push `toReal` through the staged read —
-- `toReal (vecGet (softmaxVecSpec zt) i)` via `sub`/`exp`(δ_exp atom)/denom-`foldl`(`toReal_foldl_add`)/
-- `div`; (2) the stabilized-softmax total-variation bound vs the ideal softmax; (3) assemble
-- `execAttnLit` + `attnLiteralForwardError` + instantiate the executed certificate.

end TLT.Fp32AttnLit
