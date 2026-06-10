/-
# The concrete literal transformer-stack certificate

Both block carriers' `hrnd`s with the LayerNorm budget DISCHARGED (via `lnStarExec_residual_budget`):
`mhBlock_hrnd_discharged` (attention) and `ffnBlock_hrnd_discharged` (FFN) prove the literal block —
`lnStarExec` on the genuine `Vexec` mean/std reductions of the residual `X + gridExec(FFN)(X)` — is within
the fully-closed budget `lnBudgetVal d Bln Cγ Maff + Λ_ln · rnd` of the ideal block, with NO abstract
LayerNorm slot. These are the `hrndMH`/`hrndFFN` the capstone `litMHEncoderStack_certified_generalization`
consumes; `litMHEncoderStack_literal_certified_generalization` plugs them, instantiating the parametric
capstone with the actual `IEEE32Exec` residual blocks (attention bound to `Spec.scaledDotProductAttention`,
FFN to `Spec.FeedForward.forward`; LayerNorm a faithful executed ℝ-model).
-/
import TLT_Proofs.Bridge.Certificate.MHBlockRootBinding
import TLT_Proofs.Bridge.Certificate.FFNBlockRootBinding
import TLT_Proofs.Bridge.Certificate.LNBudgetDischarge

open TorchLean.Floats (neuralMagnitude neuralBpow binaryRadix)
open TorchLean.Floats.IEEE754
open TorchLean.Floats.IEEE754.IEEE32Exec

namespace TLT.LitStackConcrete

open TLT TLT.LNBudget TLT.Fp32FFNLit TLT.Fp32FFN TLT.Fp32Attn TLT.FFNBlockRoot TLT.MHBlockRoot
open TLT.Fp32LN TLT.FullBlockLit

noncomputable section

/-- **The FFN block carrier `hrnd`, LayerNorm budget DISCHARGED.** The literal FFN residual block — with
the executed mean/std the genuine `Vexec` reductions of the residual `X + gridExecFFN X` — is within the
fully-closed `lnBudgetVal d Bln Cγ Maff + Λ_ln · ffn_rnd` of the ideal `normAttnCoord γ β (ffnCoord …)`.
The abstract LayerNorm hypotheses of `ffnBlockRoot_hrnd` are discharged by `lnStarExec_residual_budget`
on the residual; the honest LN normal-range regime (∀ y on the ball) is surfaced as hypotheses. -/
lemma ffnBlock_hrnd_discharged {n d hdim : ℕ} (hd : 0 < d) (B : ℝ)
    (ffn : Spec.FeedForward d hdim IEEE32Exec) (hB : 0 ≤ B)
    (inputs : Finset (Fin n → Fin d → IEEE32Exec)) {ffn_rnd : ℝ} (hffn_rnd : 0 ≤ ffn_rnd)
    (hregime : ∀ Xt ∈ inputs, dist (ffnExecLit ffn (Spec.matrixTensor Xt))
        (ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2)
          (fun a b => toReal (Xt a b))) ≤ ffn_rnd)
    (hinj : ∀ Xt ∈ inputs, ∀ Xt' ∈ inputs,
        (fun a b => toReal (Xt a b)) = (fun (a : Fin n) (b : Fin d) => toReal (Xt' a b)) → Xt = Xt')
    (γ β : Fin d → ℝ) {Cγ Maff Bln Λ_ln : ℝ} (hCγ0 : 0 ≤ Cγ) (hMaff0 : 0 ≤ Maff) (hBln : 0 ≤ Bln)
    (hCγ : ∀ j, |γ j| ≤ Cγ) (hdu : (d : ℝ) * u < 1) (hΛ_ln : 0 ≤ Λ_ln)
    (hlnlip : ∀ a b : Fin n → Fin d → ℝ,
        dist (layerNormCoord γ β a) (layerNormCoord γ β b) ≤ Λ_ln * dist a b)
    (hXln : ∀ y, ‖y‖ ≤ B → ∀ i k,
        |(y + gridExecFFN B ffn inputs y) i k| ≤ Bln)
    (hnMean : ∀ y, ‖y‖ ≤ B →
        VexecNormal (fun _ _ => (1 / (d : ℝ))) (y + gridExecFFN B ffn inputs y))
    (hnVar : ∀ y, ‖y‖ ≤ B →
        VexecNormal (fun _ _ => (1 / (d : ℝ))) (lnCSqExec hd (y + gridExecFFN B ffn inputs y)))
    (hsqNormal : ∀ y, ‖y‖ ≤ B → ∀ i k,
        ((y + gridExecFFN B ffn inputs y) i k
            - lnMeanExec hd (y + gridExecFFN B ffn inputs y) i) ^ 2 ≠ 0 →
        (-125 : ℤ) ≤ neuralMagnitude binaryRadix
          (((y + gridExecFFN B ffn inputs y) i k
            - lnMeanExec hd (y + gridExecFFN B ffn inputs y) i) ^ 2))
    (hMaffB : ∀ y, ‖y‖ ≤ B → ∀ i j,
        |((y + gridExecFFN B ffn inputs y) i j - lnMeanExec hd (y + gridExecFFN B ffn inputs y) i)
            / lnStdExec hd (y + gridExecFFN B ffn inputs y) i * γ j + β j| ≤ Maff)
    (haffNormal : ∀ y, ‖y‖ ≤ B → ∀ i j,
        ((y + gridExecFFN B ffn inputs y) i j - lnMeanExec hd (y + gridExecFFN B ffn inputs y) i)
            / lnStdExec hd (y + gridExecFFN B ffn inputs y) i * γ j + β j ≠ 0 →
        (-125 : ℤ) ≤ neuralMagnitude binaryRadix
          (((y + gridExecFFN B ffn inputs y) i j - lnMeanExec hd (y + gridExecFFN B ffn inputs y) i)
            / lnStdExec hd (y + gridExecFFN B ffn inputs y) i * γ j + β j))
    (x : Fin n → Fin d → ℝ) :
    dist (lnStarExec γ β
            (lnMeanExec hd (clampCoord B x + gridExecFFN B ffn inputs (clampCoord B x)))
            (lnStdExec hd (clampCoord B x + gridExecFFN B ffn inputs (clampCoord B x)))
            (clampCoord B x + gridExecFFN B ffn inputs (clampCoord B x)))
        (normAttnCoord γ β (ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2))
          (clampCoord B x))
      ≤ lnBudgetVal d Bln Cγ Maff + Λ_ln * ffn_rnd :=
  ffnBlockRoot_hrnd B ffn hB inputs hffn_rnd hregime hinj γ β
    (fun z => lnMeanExec hd (z + gridExecFFN B ffn inputs z))
    (fun z => lnStdExec hd (z + gridExecFFN B ffn inputs z)) hΛ_ln
    (fun y hy => lnStarExec_residual_budget hd γ β hBln hCγ0 hMaff0
      (y + gridExecFFN B ffn inputs y) (hXln y hy) hCγ hdu (hnMean y hy) (hnVar y hy)
      (hsqNormal y hy) (hMaffB y hy) (haffNormal y hy))
    hlnlip x

end

end TLT.LitStackConcrete
