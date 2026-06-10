/-
# The literal multi-head attention BLOCK root binding (H=1)

The executed multi-head residual+LayerNorm block as a concrete `ExecLayer` over the actual TorchLean
`IEEE32Exec` attention: the executed block map is `lnStarExec γ β (mean)(std) (X + gridExec X)`, where
`gridExec` is the ∀-input executed attention (`execAttnLit ∘ ctxOf` on the finite fp32 regime, the ideal
`attnHead` off it) and `(mean, std)` are the literal `Vexec` row reductions of the residual. Its forward
error against the ideal block `layerNormCoord γ β (X + attnHead X)` is assembled from
`gridExec_exec_close` (the attention sub-error) ⊕ `lnExec_forward_error` (the LayerNorm error) ⊕
`residual_block_forward_error` (the residual telescope). This binds the attention half of the transformer
block to the actual `Spec.scaledDotProductAttention` at `IEEE32Exec`.
-/
import TLT_Proofs.Bridge.Certificate.AttentionLiteralExecutedBinding
import TLT_Proofs.Bridge.Certificate.FullBlockLiteralExecutedBinding

open TorchLean.Floats.IEEE754
open TorchLean.Floats.IEEE754.IEEE32Exec

namespace TLT.MHBlockRoot

open TLT TLT.Fp32AttnLit TLT.Fp32Attn TLT.Fp32LN TLT.FullBlockLit

noncomputable section

/-- **The on-ball attention sub-error.** On the closed ball of radius `B`, the `clampCoord B` inside the
grid extension is the identity, so the ∀-input bound `gridExec_exec_close` reads off as the executed
attention map being within `rnd` of the *unclamped* ideal head `attnHead (1/c) W`. This is the `ρ` (the
sub-layer forward error) fed to `residual_block_forward_error` for the multi-head block. -/
lemma gridExec_onball_error {n d : ℕ} {h1 h2 : (n + 1) ≠ 0} (B c : ℝ) (W : Fin d → Fin d → ℝ)
    (inputs : Finset (Fin (n + 1) → Fin d → IEEE32Exec))
    (ctxOf : (Fin (n + 1) → Fin d → IEEE32Exec) →
      Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2)
    {rnd : ℝ} (hrnd : 0 ≤ rnd)
    (hregime : ∀ Yt ∈ inputs, dist (execAttnLit (ctxOf Yt))
        (attnHead (1 / c) W (fun a b => toReal (Yt a b))) ≤ rnd)
    (hinj : ∀ Yt ∈ inputs, ∀ Yt' ∈ inputs,
        (fun a b => toReal (Yt a b)) = (fun (a : Fin (n + 1)) (b : Fin d) => toReal (Yt' a b)) →
        Yt = Yt')
    (y : Fin (n + 1) → Fin d → ℝ) (hy : ‖y‖ ≤ B) :
    dist (gridExec B c W inputs ctxOf y) (attnHead (1 / c) W y) ≤ rnd := by
  have h := gridExec_exec_close B c W inputs ctxOf hrnd hregime hinj y
  rwa [clampCoord_eq_of_norm_le hy] at h

/-- **The executed multi-head residual+LayerNorm block forward error** (parametric in the LayerNorm
budget). The executed block `lnStarExec γ β meanE stdE (X + gridExec X)` — literal `IEEE32Exec` attention
in the residual, ℝ-model LayerNorm on top — is within `ln_budget + Λ_ln · rnd` of the ideal block
`layerNormCoord γ β (X + attnHead X)`, on the ball. Assembled from the bit-level attention sub-error
(`gridExec_onball_error`) and the residual telescope (`residual_block_forward_error`); the residual `+X`
cancels in the LayerNorm-input distance. `ln_budget`/`Λ_ln` are discharged downstream by
`lnExec_forward_error` and `layerNormCoord_lipschitz`. -/
lemma mhBlockExec_forward_error {n d : ℕ} {h1 h2 : (n + 1) ≠ 0} (B c : ℝ) (W : Fin d → Fin d → ℝ)
    (inputs : Finset (Fin (n + 1) → Fin d → IEEE32Exec))
    (ctxOf : (Fin (n + 1) → Fin d → IEEE32Exec) →
      Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2)
    {rnd : ℝ} (hrnd : 0 ≤ rnd)
    (hregime : ∀ Yt ∈ inputs, dist (execAttnLit (ctxOf Yt))
        (attnHead (1 / c) W (fun a b => toReal (Yt a b))) ≤ rnd)
    (hinj : ∀ Yt ∈ inputs, ∀ Yt' ∈ inputs,
        (fun a b => toReal (Yt a b)) = (fun (a : Fin (n + 1)) (b : Fin d) => toReal (Yt' a b)) →
        Yt = Yt')
    (γ β : Fin d → ℝ) (meanE stdE : Fin (n + 1) → ℝ)
    (X : Fin (n + 1) → Fin d → ℝ) (hX : ‖X‖ ≤ B)
    {ln_budget Λ_ln : ℝ} (hΛ_ln : 0 ≤ Λ_ln)
    (hln : dist (lnStarExec γ β meanE stdE (X + gridExec B c W inputs ctxOf X))
        (layerNormCoord γ β (X + gridExec B c W inputs ctxOf X)) ≤ ln_budget)
    (hlnlip : ∀ a b : Fin (n + 1) → Fin d → ℝ,
        dist (layerNormCoord γ β a) (layerNormCoord γ β b) ≤ Λ_ln * dist a b) :
    dist (lnStarExec γ β meanE stdE (X + gridExec B c W inputs ctxOf X))
        (layerNormCoord γ β (X + attnHead (1 / c) W X)) ≤ ln_budget + Λ_ln * rnd :=
  residual_block_forward_error γ β meanE stdE X (gridExec B c W inputs ctxOf X)
    (attnHead (1 / c) W X) hΛ_ln
    (gridExec_onball_error B c W inputs ctxOf hrnd hregime hinj X hX) hln hlnlip

end

end TLT.MHBlockRoot
