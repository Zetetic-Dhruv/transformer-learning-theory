/-
# The literal FFN BLOCK root binding

The executed feed-forward residual+LayerNorm block as a concrete `ExecLayer` over the actual TorchLean
`IEEE32Exec` feed-forward: the executed block map is `lnStarExec γ β (mean)(std) (X + gridExecFFN X)`,
where `gridExecFFN` is the ∀-input executed FFN (`ffnExecLit ∘ matrixTensor` on the finite fp32 regime,
the ideal `ffnCoord` off it) and `(mean, std)` are the literal `Vexec` row reductions of the residual.
Its forward error against the ideal block `layerNormCoord γ β (X + ffnCoord X)` is assembled from
`gridExecFFN_onball_error` (the FFN sub-error, from `ffnLiteral_forward_error`) ⊕ `lnExec_forward_error`
(the LayerNorm error) ⊕ `residual_block_forward_error` (the residual telescope). This binds the FFN half
of the transformer block to the actual `Spec.FeedForward.forward` at `IEEE32Exec`, mirroring
`MHBlockRootBinding` for the attention half.
-/
import TLT_Proofs.Bridge.Certificate.FFNLiteralExecutedBinding
import TLT_Proofs.Bridge.Certificate.FullBlockLiteralExecutedBinding

open TorchLean.Floats.IEEE754
open TorchLean.Floats.IEEE754.IEEE32Exec
open Spec Tensor

namespace TLT.FFNBlockRoot

open TLT TLT.Fp32FFNLit TLT.Fp32FFN TLT.Fp32FFNBias TLT.Fp32LN TLT.FullBlockLit TLT.GridExt

noncomputable section

/-- **The ∀-input executed FFN**, a `gridExt` instance: the literal `IEEE32Exec` feed-forward
`ffnExecLit ∘ matrixTensor` on the finite fp32 grid `inputs`, and the ideal `ffnCoord` (on the
`toReal`-read weights) off it. The FFN analogue of the attention `gridExec`. -/
def gridExecFFN {n d h : ℕ} (B : ℝ) (ffn : Spec.FeedForward d h IEEE32Exec)
    (inputs : Finset (Fin n → Fin d → IEEE32Exec)) (y : Fin n → Fin d → ℝ) : Fin n → Fin d → ℝ :=
  gridExt (ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2))
    (clampCoord B) inputs (fun Xt => fun a b => toReal (Xt a b))
    (fun Xt => ffnExecLit ffn (Spec.matrixTensor Xt)) y

/-- **The on-ball FFN sub-error.** On the closed ball of radius `B`, the `clampCoord B` inside the grid
extension is the identity, so the ∀-input bound `gridExt_exec_close` reads off as the executed FFN map
being within `rnd` of the unclamped ideal `ffnCoord`. This is the `ρ` fed to
`residual_block_forward_error` for the FFN block; `hregime` is discharged by `ffnLiteral_forward_error`. -/
lemma gridExecFFN_onball_error {n d h : ℕ} (B : ℝ) (ffn : Spec.FeedForward d h IEEE32Exec)
    (inputs : Finset (Fin n → Fin d → IEEE32Exec)) {rnd : ℝ} (hrnd : 0 ≤ rnd)
    (hregime : ∀ Xt ∈ inputs, dist (ffnExecLit ffn (Spec.matrixTensor Xt))
        (ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2)
          (fun a b => toReal (Xt a b))) ≤ rnd)
    (hinj : ∀ Xt ∈ inputs, ∀ Xt' ∈ inputs,
        (fun a b => toReal (Xt a b)) = (fun (a : Fin n) (b : Fin d) => toReal (Xt' a b)) → Xt = Xt')
    (y : Fin n → Fin d → ℝ) (hy : ‖y‖ ≤ B) :
    dist (gridExecFFN B ffn inputs y)
        (ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2) y) ≤ rnd := by
  have h := gridExt_exec_close
    (ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2)) (clampCoord B) inputs
    (fun Xt => fun a b => toReal (Xt a b)) (fun Xt => ffnExecLit ffn (Spec.matrixTensor Xt))
    hrnd hregime hinj y
  rwa [clampCoord_eq_of_norm_le hy] at h

/-- **The executed FFN residual+LayerNorm block forward error** (parametric in the LayerNorm budget).
The executed block `lnStarExec γ β meanE stdE (X + gridExecFFN X)` (literal `IEEE32Exec` feed-forward in
the residual, ℝ-model LayerNorm on top) is within `ln_budget + Λ_ln · rnd` of the ideal block
`layerNormCoord γ β (X + ffnCoord X)`, on the ball. Assembled from the bit-level FFN sub-error
(`gridExecFFN_onball_error`, discharged by `ffnLiteral_forward_error`) and the residual telescope
(`residual_block_forward_error`); the residual `+X` cancels in the LayerNorm-input distance. -/
lemma ffnBlockExec_forward_error {n d h : ℕ} (B : ℝ) (ffn : Spec.FeedForward d h IEEE32Exec)
    (inputs : Finset (Fin n → Fin d → IEEE32Exec)) {rnd : ℝ} (hrnd : 0 ≤ rnd)
    (hregime : ∀ Xt ∈ inputs, dist (ffnExecLit ffn (Spec.matrixTensor Xt))
        (ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2)
          (fun a b => toReal (Xt a b))) ≤ rnd)
    (hinj : ∀ Xt ∈ inputs, ∀ Xt' ∈ inputs,
        (fun a b => toReal (Xt a b)) = (fun (a : Fin n) (b : Fin d) => toReal (Xt' a b)) → Xt = Xt')
    (γ β : Fin d → ℝ) (meanE stdE : Fin n → ℝ) (X : Fin n → Fin d → ℝ) (hX : ‖X‖ ≤ B)
    {ln_budget Λ_ln : ℝ} (hΛ_ln : 0 ≤ Λ_ln)
    (hln : dist (lnStarExec γ β meanE stdE (X + gridExecFFN B ffn inputs X))
        (layerNormCoord γ β (X + gridExecFFN B ffn inputs X)) ≤ ln_budget)
    (hlnlip : ∀ a b : Fin n → Fin d → ℝ,
        dist (layerNormCoord γ β a) (layerNormCoord γ β b) ≤ Λ_ln * dist a b) :
    dist (lnStarExec γ β meanE stdE (X + gridExecFFN B ffn inputs X))
        (layerNormCoord γ β
          (X + ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2) X))
      ≤ ln_budget + Λ_ln * rnd :=
  residual_block_forward_error γ β meanE stdE X (gridExecFFN B ffn inputs X)
    (ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2) X) hΛ_ln
    (gridExecFFN_onball_error B ffn inputs hrnd hregime hinj X hX) hln hlnlip

/-- **The FFN block carrier `hrnd`**: the ∀-input forward error against the ideal FFN residual block
`normAttnCoord γ β (ffnCoord …)`. Precomposing the executed block with `clampCoord B` lands every input
in the ball, where `ffnBlockExec_forward_error` applies. Unlike the attention block, the ideal is the FFN
directly, with no `multiHeadAttn` reconciliation. -/
lemma ffnBlockRoot_hrnd {n d h : ℕ} (B : ℝ) (ffn : Spec.FeedForward d h IEEE32Exec) (hB : 0 ≤ B)
    (inputs : Finset (Fin n → Fin d → IEEE32Exec)) {rnd : ℝ} (hrnd : 0 ≤ rnd)
    (hregime : ∀ Xt ∈ inputs, dist (ffnExecLit ffn (Spec.matrixTensor Xt))
        (ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2)
          (fun a b => toReal (Xt a b))) ≤ rnd)
    (hinj : ∀ Xt ∈ inputs, ∀ Xt' ∈ inputs,
        (fun a b => toReal (Xt a b)) = (fun (a : Fin n) (b : Fin d) => toReal (Xt' a b)) → Xt = Xt')
    (γ β : Fin d → ℝ) (meanOf stdOf : (Fin n → Fin d → ℝ) → Fin n → ℝ)
    {ln_budget Λ_ln : ℝ} (hΛ_ln : 0 ≤ Λ_ln)
    (hln : ∀ y : Fin n → Fin d → ℝ, ‖y‖ ≤ B →
        dist (lnStarExec γ β (meanOf y) (stdOf y) (y + gridExecFFN B ffn inputs y))
            (layerNormCoord γ β (y + gridExecFFN B ffn inputs y)) ≤ ln_budget)
    (hlnlip : ∀ a b : Fin n → Fin d → ℝ,
        dist (layerNormCoord γ β a) (layerNormCoord γ β b) ≤ Λ_ln * dist a b)
    (x : Fin n → Fin d → ℝ) :
    dist (lnStarExec γ β (meanOf (clampCoord B x)) (stdOf (clampCoord B x))
            (clampCoord B x + gridExecFFN B ffn inputs (clampCoord B x)))
        (normAttnCoord γ β (ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2))
          (clampCoord B x))
      ≤ ln_budget + Λ_ln * rnd := by
  have hxb : ‖clampCoord B x‖ ≤ B := clampCoord_norm_le hB x
  rw [normAttnCoord]
  exact ffnBlockExec_forward_error B ffn inputs hrnd hregime hinj γ β
    (meanOf (clampCoord B x)) (stdOf (clampCoord B x)) (clampCoord B x) hxb hΛ_ln
    (hln (clampCoord B x) hxb) hlnlip

/-- **The literal FFN BLOCK carrier**: the `Es`-ready ambient `ExecLayer` whose executed map is the
bit-level `IEEE32Exec` feed-forward block (`lnStarExec(· + gridExecFFN ·)` clamp-precomposed) and whose
forward error against the ideal `normFFNBlock`-style block is the closed `ln_budget + Λ_ln · ffn_rnd`.
The FFN sublayer is bound to `Spec.FeedForward.forward` (via `gridExecFFN`/`ffnExecLit`,
`hregime` discharged by `ffnLiteral_forward_error`); the LayerNorm rides on top as ℝ-model
(`ln_budget`/reductions discharged downstream, the same deferred gap as the attention block). This is
the FFN half of the transformer-block root binding, ready to plug as `Es` into the shipped capstone. -/
noncomputable def ffnBlockRootExecLayer {n d h : ℕ} (hd : 0 < d) {Cγ Cβ Lf : ℝ} (hLf0 : 0 ≤ Lf)
    (ffn : Spec.FeedForward d h IEEE32Exec) (γ β : Fin d → ℝ)
    (hCγ : ∀ j, |γ j| ≤ Cγ) (hCβ : ∀ j, |β j| ≤ Cβ)
    (hffnlip : ∀ a ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ b ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      dist (ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2) a)
        (ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2) b) ≤ Lf * dist a b)
    (inputs : Finset (Fin n → Fin d → IEEE32Exec))
    {ffn_rnd : ℝ} (hffn_rnd : 0 ≤ ffn_rnd)
    (hregime : ∀ Xt ∈ inputs, dist (ffnExecLit ffn (Spec.matrixTensor Xt))
        (ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2)
          (fun a b => toReal (Xt a b))) ≤ ffn_rnd)
    (hinj : ∀ Xt ∈ inputs, ∀ Xt' ∈ inputs,
        (fun a b => toReal (Xt a b)) = (fun (a : Fin n) (b : Fin d) => toReal (Xt' a b)) → Xt = Xt')
    (meanOf stdOf : (Fin n → Fin d → ℝ) → Fin n → ℝ)
    {ln_budget Λ_ln : ℝ} (hΛ_ln : 0 ≤ Λ_ln)
    (hln : ∀ y : Fin n → Fin d → ℝ, ‖y‖ ≤ Real.sqrt d * Cγ + Cβ →
        dist (lnStarExec γ β (meanOf y) (stdOf y)
              (y + gridExecFFN (Real.sqrt d * Cγ + Cβ) ffn inputs y))
            (layerNormCoord γ β (y + gridExecFFN (Real.sqrt d * Cγ + Cβ) ffn inputs y)) ≤ ln_budget)
    (hlnlip : ∀ a b : Fin n → Fin d → ℝ,
        dist (layerNormCoord γ β a) (layerNormCoord γ β b) ≤ Λ_ln * dist a b) :
    ExecLayer (Fin n → Fin d → ℝ) :=
  clampedFFNBlockExecLayer hd hLf0 (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2)
    γ β hCγ hCβ hffnlip
    (fun x => lnStarExec γ β (meanOf (clampCoord (Real.sqrt d * Cγ + Cβ) x))
      (stdOf (clampCoord (Real.sqrt d * Cγ + Cβ) x))
      (clampCoord (Real.sqrt d * Cγ + Cβ) x
        + gridExecFFN (Real.sqrt d * Cγ + Cβ) ffn inputs (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
    (ln_budget + Λ_ln * ffn_rnd)
    (ffnBlockRoot_hrnd (Real.sqrt d * Cγ + Cβ) ffn
      (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (le_trans (abs_nonneg _) (hCγ ⟨0, hd⟩)))
        (le_trans (abs_nonneg _) (hCβ ⟨0, hd⟩)))
      inputs hffn_rnd hregime hinj γ β meanOf stdOf hΛ_ln hln hlnlip)

end

end TLT.FFNBlockRoot
