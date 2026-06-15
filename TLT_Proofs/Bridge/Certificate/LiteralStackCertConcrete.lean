/-
# The concrete literal transformer-stack certificate

`mhBlock_hrnd_discharged` (attention) and `ffnBlock_hrnd_discharged` (FFN) prove that the literal block
(`lnStarExec` on the `Vexec` mean/std reductions of the residual `X + gridExec(FFN)(X)`) is within the
fully-closed budget `lnBudgetVal d Bln Cγ Maff + Λ_ln · rnd` of the ideal block, with no abstract
LayerNorm slot. The abstract LayerNorm hypotheses are discharged by `lnStarExec_residual_budget`.
`litMHEncoderStack_literal_certified_generalization` instantiates the parametric capstone with the actual
`IEEE32Exec` residual blocks (attention bound to `Spec.scaledDotProductAttention`, FFN to
`Spec.FeedForward.forward`; LayerNorm a faithful executed ℝ-model).
-/
import TLT_Proofs.Bridge.Certificate.MHBlockRootBinding
import TLT_Proofs.Bridge.Certificate.FFNBlockRootBinding
import TLT_Proofs.Bridge.Certificate.LNBudgetDischarge

open TorchLean.Floats (neuralMagnitude neuralBpow binaryRadix)
open TorchLean.Floats.IEEE754
open TorchLean.Floats.IEEE754.IEEE32Exec

namespace TLT.LitStackConcrete

open TLT TLT.LNBudget TLT.Fp32FFNLit TLT.Fp32FFN TLT.Fp32Attn TLT.Fp32AttnLit TLT.FFNBlockRoot
open TLT.MHBlockRoot TLT.Fp32LN TLT.FullBlockLit TLT.Capacity MeasureTheory

noncomputable section

/-- **The FFN block carrier `hrnd`, LayerNorm budget discharged.** The literal FFN residual block, with
the executed mean/std the `Vexec` reductions of the residual `X + gridExecFFN X`, is within the
fully-closed `lnBudgetVal d Bln Cγ Maff + Λ_ln · ffn_rnd` of the ideal `normAttnCoord γ β (ffnCoord …)`.
The abstract LayerNorm hypotheses of `ffnBlockRoot_hrnd` are discharged by `lnStarExec_residual_budget`
on the residual; the LN normal-range regime (∀ y on the ball) is surfaced as hypotheses. -/
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

/-- **The MH (attention) block carrier `hrnd`, LayerNorm budget discharged.** The literal multi-head
residual block, with executed mean/std the `Vexec` reductions of `X + gridExec X`, is within the
fully-closed `lnBudgetVal d Bln Cγ Maff + Λ_ln · attn_rnd` of the ideal
`normAttnCoord γ β (multiHeadAttn (H:=1) …)`. The abstract LayerNorm hypotheses of `mhBlockRoot_hrnd`
are discharged by `lnStarExec_residual_budget`. Attention is bound to
`Spec.scaledDotProductAttention`. -/
lemma mhBlock_hrnd_discharged {n d : ℕ} {h1 h2 : (n + 1) ≠ 0} (hd : 0 < d) (c : ℝ)
    (W : Fin d → Fin d → ℝ) {Cγ Cβ : ℝ} (hCγ0 : 0 ≤ Cγ) (hCβ0 : 0 ≤ Cβ)
    (inputs : Finset (Fin (n + 1) → Fin d → IEEE32Exec))
    (ctxOf : (Fin (n + 1) → Fin d → IEEE32Exec) →
      Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2)
    {attn_rnd : ℝ} (hattn_rnd : 0 ≤ attn_rnd)
    (hregime : ∀ Yt ∈ inputs, dist (execAttnLit (ctxOf Yt))
        (attnHead (1 / c) W (fun a b => toReal (Yt a b))) ≤ attn_rnd)
    (hinj : ∀ Yt ∈ inputs, ∀ Yt' ∈ inputs,
        (fun a b => toReal (Yt a b)) = (fun (a : Fin (n + 1)) (b : Fin d) => toReal (Yt' a b)) → Yt = Yt')
    (γ β : Fin d → ℝ) {Maff Bln Λ_ln : ℝ} (hMaff0 : 0 ≤ Maff) (hBln : 0 ≤ Bln)
    (hCγ : ∀ j, |γ j| ≤ Cγ) (hdu : (d : ℝ) * u < 1) (hΛ_ln : 0 ≤ Λ_ln)
    (hlnlip : ∀ a b : Fin (n + 1) → Fin d → ℝ,
        dist (layerNormCoord γ β a) (layerNormCoord γ β b) ≤ Λ_ln * dist a b)
    (hXln : ∀ y, ‖y‖ ≤ Real.sqrt d * Cγ + Cβ → ∀ i k,
        |(y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y) i k| ≤ Bln)
    (hnMean : ∀ y, ‖y‖ ≤ Real.sqrt d * Cγ + Cβ →
        VexecNormal (fun _ _ => (1 / (d : ℝ)))
          (y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y))
    (hnVar : ∀ y, ‖y‖ ≤ Real.sqrt d * Cγ + Cβ →
        VexecNormal (fun _ _ => (1 / (d : ℝ)))
          (lnCSqExec hd (y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y)))
    (hsqNormal : ∀ y, ‖y‖ ≤ Real.sqrt d * Cγ + Cβ → ∀ i k,
        ((y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y) i k
            - lnMeanExec hd (y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y) i) ^ 2 ≠ 0 →
        (-125 : ℤ) ≤ neuralMagnitude binaryRadix
          (((y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y) i k
            - lnMeanExec hd (y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y) i) ^ 2))
    (hMaffB : ∀ y, ‖y‖ ≤ Real.sqrt d * Cγ + Cβ → ∀ i j,
        |((y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y) i j
            - lnMeanExec hd (y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y) i)
            / lnStdExec hd (y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y) i * γ j + β j|
          ≤ Maff)
    (haffNormal : ∀ y, ‖y‖ ≤ Real.sqrt d * Cγ + Cβ → ∀ i j,
        ((y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y) i j
            - lnMeanExec hd (y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y) i)
            / lnStdExec hd (y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y) i * γ j + β j ≠ 0 →
        (-125 : ℤ) ≤ neuralMagnitude binaryRadix
          (((y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y) i j
            - lnMeanExec hd (y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y) i)
            / lnStdExec hd (y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y) i * γ j + β j))
    (x : Fin (n + 1) → Fin d → ℝ) :
    dist (lnStarExec γ β
            (lnMeanExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
              + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
            (lnStdExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
              + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
            (clampCoord (Real.sqrt d * Cγ + Cβ) x
              + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
        (normAttnCoord γ β (multiHeadAttn (H := 1) (1 / c) (fun _ k j => if k = j then 1 else 0)
            (fun _ k j => if k = j then 1 else 0) (fun _ => W)) (clampCoord (Real.sqrt d * Cγ + Cβ) x))
      ≤ lnBudgetVal d Bln Cγ Maff + Λ_ln * attn_rnd :=
  mhBlockRoot_hrnd c W hCγ0 hCβ0 inputs ctxOf hattn_rnd hregime hinj γ β
    (fun z => lnMeanExec hd (z + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf z))
    (fun z => lnStdExec hd (z + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf z)) hΛ_ln
    (fun y hy => lnStarExec_residual_budget hd γ β hBln hCγ0 hMaff0
      (y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y) (hXln y hy) hCγ hdu
      (hnMean y hy) (hnVar y hy) (hsqNormal y hy) (hMaffB y hy) (haffNormal y hy))
    hlnlip x

/-- **The concrete literal multi-head transformer encoder stack certificate.** The depth-`L`, `H=1`
executed encoder stack with the actual `IEEE32Exec` residual blocks (multi-head attention bound to
`Spec.scaledDotProductAttention` via `gridExec`/`execAttnLit`, feed-forward to
`Spec.FeedForward.forward` via `gridExecFFN`/`ffnExecLit`, each LayerNorm a faithful executed ℝ-model
on the `Vexec` mean/std reductions) satisfies the Dudley generalization bound. `hrndMH`/`hrndFFN` are the LN-discharged block
carriers (`mhBlock_hrnd_discharged`/`ffnBlock_hrnd_discharged`), plugged into the parametric capstone
`litMHEncoderStack_certified_generalization`. The conclusion is the capstone's at the literal `Es`.
Stated as a `def` whose inferred type is the capstone's Dudley bound at the literal `Es`. -/
def litMHEncoderStack_literal_certified_generalization
    {n d p hdim m : ℕ} [Nonempty (Fin p)]
    [MeasurableSpace (Fin (n + 1) → Fin d → ℝ)] [BorelSpace (Fin (n + 1) → Fin d → ℝ)]
    {P : MeasureTheory.Measure (Fin (n + 1) → Fin d → ℝ)} [MeasureTheory.IsProbabilityMeasure P]
    (hm : 0 < m)
    {R B bV βY γW Cγ Cβ Lγ Lβ bW1 bW2 c : ℝ} (hR : 0 ≤ R) (hc : 0 < c) (hd : 0 < d)
    (hB : 0 ≤ B) (hbV0 : 0 ≤ bV) (hβY0 : 0 ≤ βY) (hγW0 : 0 ≤ γW) (hCγ0 : 0 ≤ Cγ) (hCβ0 : 0 ≤ Cβ)
    (hLγ0 : 0 ≤ Lγ) (hLβ0 : 0 ≤ Lβ) (hbW1 : 0 ≤ bW1) (hbW2 : 0 ≤ bW2)
    (W' : Fin d → Fin d → ℝ) (ffn : Spec.FeedForward d hdim IEEE32Exec)
    (hW1c : ∀ l, (∑ k, |tReal2 ffn.W1 k l|) ≤ bW1) (hW2c : ∀ j, (∑ l, |tReal2 ffn.W2 l j|) ≤ bW2)
    (γ1 β1 γ2 β2 : Fin d → ℝ)
    (hγ1B : ∀ j, |γ1 j| ≤ Cγ) (hβ1B : ∀ j, |β1 j| ≤ Cβ) (hγ2B : ∀ j, |γ2 j| ≤ Cγ)
    (hβ2B : ∀ j, |β2 j| ≤ Cβ)
    (hβYD : ∀ y ∈ Metric.closedBall (0 : Fin (n + 1) → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ i, (∑ a, |y i a|) ≤ βY)
    (hidB : ∀ y ∈ Metric.closedBall (0 : Fin (n + 1) → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ i e, |y i e| ≤ B)
    (hVB : ∀ y ∈ Metric.closedBall (0 : Fin (n + 1) → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ (_ : Fin 1) j, ‖matMulCoord W' y j‖ ≤ bV)
    (hγWVO : ∀ j, (∑ k, |W' k j|) ≤ γW) (hγWid : (1 : ℝ) ≤ γW)
    (ℓ : (Fin (n + 1) → Fin d → ℝ) → ℝ) {b : ℝ} (hb : 0 < b) (hℓb : ∀ v, |ℓ v| ≤ b)
    (hℓcont : Continuous ℓ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ) (hℓLip : ∀ u v, |ℓ u - ℓ v| ≤ Lℓ * dist u v)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R)
    (hwT : embedBase Capacity.Dyadic w_T.1 ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p)))) (L : ℕ)
    {Lf : ℝ} (hLf0 : 0 ≤ Lf)
    (hffnlip : ∀ a ∈ Metric.closedBall (0 : Fin (n + 1) → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ bb ∈ Metric.closedBall (0 : Fin (n + 1) → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      dist (ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2) a)
        (ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2) bb) ≤ Lf * dist a bb)
    {Λ_ln : ℝ} (hΛ_ln : 0 ≤ Λ_ln) (hdu : (d : ℝ) * u < 1)
    (hlnlip : ∀ a b : Fin (n + 1) → Fin d → ℝ,
      dist (layerNormCoord γ1 β1 a) (layerNormCoord γ1 β1 b) ≤ Λ_ln * dist a b)
    (hlnlip2 : ∀ a b : Fin (n + 1) → Fin d → ℝ,
      dist (layerNormCoord γ2 β2 a) (layerNormCoord γ2 β2 b) ≤ Λ_ln * dist a b)
    -- attention block regime + LN regime (the `hrndMH` data):
    (inputsMH : Finset (Fin (n + 1) → Fin d → IEEE32Exec))
    (ctxOf : (Fin (n + 1) → Fin d → IEEE32Exec) →
      Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d (Nat.succ_ne_zero n) (Nat.succ_ne_zero n))
    {attn_rnd MaffMH BlnMH : ℝ} (hattn_rnd : 0 ≤ attn_rnd) (hMaffMH0 : 0 ≤ MaffMH) (hBlnMH0 : 0 ≤ BlnMH)
    (hrndMH : ∀ x, dist
        (lnStarExec γ1 β1
          (lnMeanExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
            + gridExec (Real.sqrt d * Cγ + Cβ) c W' inputsMH ctxOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
          (lnStdExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
            + gridExec (Real.sqrt d * Cγ + Cβ) c W' inputsMH ctxOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
          (clampCoord (Real.sqrt d * Cγ + Cβ) x
            + gridExec (Real.sqrt d * Cγ + Cβ) c W' inputsMH ctxOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
        (normAttnCoord γ1 β1 (multiHeadAttn (1 / c) (fun _ k j => if k = j then 1 else 0)
          (fun _ k j => if k = j then 1 else 0) (fun _ => W')) (clampCoord (Real.sqrt d * Cγ + Cβ) x))
      ≤ lnBudgetVal d BlnMH Cγ MaffMH + Λ_ln * attn_rnd)
    -- FFN block regime + LN regime (the `hrndFFN` data):
    (inputsFFN : Finset (Fin (n + 1) → Fin d → IEEE32Exec))
    {ffn_rnd MaffFFN BlnFFN : ℝ} (hffn_rnd : 0 ≤ ffn_rnd) (hMaffFFN0 : 0 ≤ MaffFFN)
    (hBlnFFN0 : 0 ≤ BlnFFN)
    (hrndFFN : ∀ x, dist
        (lnStarExec γ2 β2
          (lnMeanExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
            + gridExecFFN (Real.sqrt d * Cγ + Cβ) ffn inputsFFN (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
          (lnStdExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
            + gridExecFFN (Real.sqrt d * Cγ + Cβ) ffn inputsFFN (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
          (clampCoord (Real.sqrt d * Cγ + Cβ) x
            + gridExecFFN (Real.sqrt d * Cγ + Cβ) ffn inputsFFN (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
        (normAttnCoord γ2 β2 (ffnCoord (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2))
          (clampCoord (Real.sqrt d * Cγ + Cβ) x))
      ≤ lnBudgetVal d BlnFFN Cγ MaffFFN + Λ_ln * ffn_rnd)
    (hintG : MeasureTheory.Integrable
      (fun x => ℓ (execComp (clampExecLayer (Real.sqrt d * Cγ + Cβ) ::
        litStackEs hd (one_div_pos.mpr hc) hB hbV0 hγW0 (fun _ => W')
          (fun _ j => hγWVO j) hγWid γ1 β1 hγ1B hβ1B hidB hVB
          (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2) γ2 β2 hγ2B hβ2B hLf0 hffnlip
          (fun x => lnStarExec γ1 β1
            (lnMeanExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
              + gridExec (Real.sqrt d * Cγ + Cβ) c W' inputsMH ctxOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
            (lnStdExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
              + gridExec (Real.sqrt d * Cγ + Cβ) c W' inputsMH ctxOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
            (clampCoord (Real.sqrt d * Cγ + Cβ) x
              + gridExec (Real.sqrt d * Cγ + Cβ) c W' inputsMH ctxOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
          (fun x => lnStarExec γ2 β2
            (lnMeanExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
              + gridExecFFN (Real.sqrt d * Cγ + Cβ) ffn inputsFFN (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
            (lnStdExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
              + gridExecFFN (Real.sqrt d * Cγ + Cβ) ffn inputsFFN (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
            (clampCoord (Real.sqrt d * Cγ + Cβ) x
              + gridExecFFN (Real.sqrt d * Cγ + Cβ) ffn inputsFFN (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
          (lnBudgetVal d BlnMH Cγ MaffMH + Λ_ln * attn_rnd)
          (lnBudgetVal d BlnFFN Cγ MaffFFN + Λ_ln * ffn_rnd) hrndMH hrndFFN L) x)) P)
    (hLpos : 0 < Lℓ * lparamLipBound (List.flatten (List.replicate L
      [normMultiHeadBlock (n := n + 1) (p := p) (one_div_pos.mpr hc) hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0
          (le_refl 0) (le_refl 0) (le_refl 0) (fun _ _ k j => if k = j then 1 else 0)
          (fun _ _ k j => if k = j then 1 else 0) (fun _ => fun _ => W') (fun _ => γ1) (fun _ => β1),
       normFFNBlock (s := n + 1) (p := p) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2
          (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2)
          (fun _ => γ2) (fun _ => β2)]))) :=
  litMHEncoderStack_certified_generalization hm hR (one_div_pos.mpr hc) hd hB hbV0 hβY0 hγW0 hCγ0 hCβ0
    hLγ0 hLβ0 hbW1 hbW2 (fun _ => W') (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2)
    hW1c hW2c γ1 β1 γ2 β2 hγ1B hβ1B hγ2B hβ2B hβYD hidB hVB (fun _ j => hγWVO j) hγWid
    ℓ hb hℓb hℓcont hLℓ0 hℓLip hε w_T hwT L hLf0 hffnlip
    (fun x => lnStarExec γ1 β1
      (lnMeanExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
        + gridExec (Real.sqrt d * Cγ + Cβ) c W' inputsMH ctxOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
      (lnStdExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
        + gridExec (Real.sqrt d * Cγ + Cβ) c W' inputsMH ctxOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
      (clampCoord (Real.sqrt d * Cγ + Cβ) x
        + gridExec (Real.sqrt d * Cγ + Cβ) c W' inputsMH ctxOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
    (fun x => lnStarExec γ2 β2
      (lnMeanExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
        + gridExecFFN (Real.sqrt d * Cγ + Cβ) ffn inputsFFN (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
      (lnStdExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
        + gridExecFFN (Real.sqrt d * Cγ + Cβ) ffn inputsFFN (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
      (clampCoord (Real.sqrt d * Cγ + Cβ) x
        + gridExecFFN (Real.sqrt d * Cγ + Cβ) ffn inputsFFN (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
    (lnBudgetVal d BlnMH Cγ MaffMH + Λ_ln * attn_rnd)
    (lnBudgetVal d BlnFFN Cγ MaffFFN + Λ_ln * ffn_rnd) hrndMH hrndFFN
    (litStackEs hd (one_div_pos.mpr hc) hB hbV0 hγW0 (fun _ => W') (fun _ j => hγWVO j) hγWid
      γ1 β1 hγ1B hβ1B hidB hVB (tReal2 ffn.W1) (tReal1 ffn.b1) (tReal2 ffn.W2) (tReal1 ffn.b2)
      γ2 β2 hγ2B hβ2B hLf0 hffnlip
      (fun x => lnStarExec γ1 β1
        (lnMeanExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
          + gridExec (Real.sqrt d * Cγ + Cβ) c W' inputsMH ctxOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
        (lnStdExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
          + gridExec (Real.sqrt d * Cγ + Cβ) c W' inputsMH ctxOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
        (clampCoord (Real.sqrt d * Cγ + Cβ) x
          + gridExec (Real.sqrt d * Cγ + Cβ) c W' inputsMH ctxOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
      (fun x => lnStarExec γ2 β2
        (lnMeanExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
          + gridExecFFN (Real.sqrt d * Cγ + Cβ) ffn inputsFFN (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
        (lnStdExec hd (clampCoord (Real.sqrt d * Cγ + Cβ) x
          + gridExecFFN (Real.sqrt d * Cγ + Cβ) ffn inputsFFN (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
        (clampCoord (Real.sqrt d * Cγ + Cβ) x
          + gridExecFFN (Real.sqrt d * Cγ + Cβ) ffn inputsFFN (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
      (lnBudgetVal d BlnMH Cγ MaffMH + Λ_ln * attn_rnd)
      (lnBudgetVal d BlnFFN Cγ MaffFFN + Λ_ln * ffn_rnd) hrndMH hrndFFN L)
    rfl hintG hLpos

end

end TLT.LitStackConcrete
