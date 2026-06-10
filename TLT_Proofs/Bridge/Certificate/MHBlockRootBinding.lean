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

/-- **The carrier `hrnd`** — the ∀-input forward error against the `H=1` ideal block. Precomposing the
executed block with `clampCoord ρ` lands every input in the ball, where `mhBlockExec_forward_error`
applies; the `H=1` reconciliation `attnHead_eq_multiHead_one` matches the carrier's `multiHeadAttn` ideal to
the `attnHead` of the bit-level binding. `ρ = √d·Cγ+Cβ` is both the ball radius and the attention input
clamp `B`. -/
lemma mhBlockRoot_hrnd {n d : ℕ} {h1 h2 : (n + 1) ≠ 0} (c : ℝ) (W : Fin d → Fin d → ℝ)
    {Cγ Cβ : ℝ} (hCγ0 : 0 ≤ Cγ) (hCβ0 : 0 ≤ Cβ)
    (inputs : Finset (Fin (n + 1) → Fin d → IEEE32Exec))
    (ctxOf : (Fin (n + 1) → Fin d → IEEE32Exec) →
      Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2)
    {attn_rnd : ℝ} (hattn_rnd : 0 ≤ attn_rnd)
    (hregime : ∀ Yt ∈ inputs, dist (execAttnLit (ctxOf Yt))
        (attnHead (1 / c) W (fun a b => toReal (Yt a b))) ≤ attn_rnd)
    (hinj : ∀ Yt ∈ inputs, ∀ Yt' ∈ inputs,
        (fun a b => toReal (Yt a b)) = (fun (a : Fin (n + 1)) (b : Fin d) => toReal (Yt' a b)) →
        Yt = Yt')
    (γ β : Fin d → ℝ)
    (meanOf stdOf : (Fin (n + 1) → Fin d → ℝ) → Fin (n + 1) → ℝ)
    {ln_budget Λ_ln : ℝ} (hΛ_ln : 0 ≤ Λ_ln)
    (hln : ∀ y : Fin (n + 1) → Fin d → ℝ, ‖y‖ ≤ Real.sqrt d * Cγ + Cβ →
        dist (lnStarExec γ β (meanOf y) (stdOf y)
              (y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y))
            (layerNormCoord γ β (y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y)) ≤ ln_budget)
    (hlnlip : ∀ a b : Fin (n + 1) → Fin d → ℝ,
        dist (layerNormCoord γ β a) (layerNormCoord γ β b) ≤ Λ_ln * dist a b)
    (x : Fin (n + 1) → Fin d → ℝ) :
    dist (lnStarExec γ β (meanOf (clampCoord (Real.sqrt d * Cγ + Cβ) x))
            (stdOf (clampCoord (Real.sqrt d * Cγ + Cβ) x))
            (clampCoord (Real.sqrt d * Cγ + Cβ) x
              + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
        (normAttnCoord γ β (multiHeadAttn (H := 1) (1 / c) (fun _ k j => if k = j then 1 else 0)
            (fun _ k j => if k = j then 1 else 0) (fun _ => W))
          (clampCoord (Real.sqrt d * Cγ + Cβ) x))
      ≤ ln_budget + Λ_ln * attn_rnd := by
  have hρ : (0 : ℝ) ≤ Real.sqrt d * Cγ + Cβ := by positivity
  have hxb : ‖clampCoord (Real.sqrt d * Cγ + Cβ) x‖ ≤ Real.sqrt d * Cγ + Cβ := clampCoord_norm_le hρ x
  have heq : normAttnCoord γ β (multiHeadAttn (H := 1) (1 / c) (fun _ k j => if k = j then 1 else 0)
        (fun _ k j => if k = j then 1 else 0) (fun _ => W)) (clampCoord (Real.sqrt d * Cγ + Cβ) x)
      = layerNormCoord γ β (clampCoord (Real.sqrt d * Cγ + Cβ) x
          + attnHead (1 / c) W (clampCoord (Real.sqrt d * Cγ + Cβ) x)) := by
    rw [normAttnCoord, attnHead_eq_multiHead_one]
    rfl
  rw [heq]
  exact mhBlockExec_forward_error (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf hattn_rnd hregime hinj
    γ β (meanOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)) (stdOf (clampCoord (Real.sqrt d * Cγ + Cβ) x))
    (clampCoord (Real.sqrt d * Cγ + Cβ) x) hxb hΛ_ln
    (hln (clampCoord (Real.sqrt d * Cγ + Cβ) x) hxb) hlnlip

/-- Row-sum of the constant identity head projection is `1`, hence `≤ γW` whenever `1 ≤ γW`. -/
private lemma id_rowSum_le {d : ℕ} {γW : ℝ} (hγWid : (1 : ℝ) ≤ γW) (j : Fin d) :
    (∑ k, |(if k = j then (1 : ℝ) else 0)|) ≤ γW := by
  have hfun : (fun k => |(if k = j then (1 : ℝ) else 0)|) = fun k : Fin d => if k = j then (1 : ℝ) else 0 := by
    funext k; split <;> simp
  have h1 : (∑ k, |(if k = j then (1 : ℝ) else 0)|) = 1 := by rw [hfun]; simp
  rw [h1]; exact hγWid

/-- **The literal multi-head attention BLOCK carrier (H=1)** — the `Es`-ready ambient `ExecLayer` whose
executed map is the bit-level `IEEE32Exec` attention block (`lnStarExec(· + gridExec ·)` clamp-precomposed)
and whose forward error against the ideal `normMultiHeadBlock`-style block is the closed
`ln_budget + Λ_ln · attn_rnd`. The attention sublayer is genuinely bound to `Spec.scaledDotProductAttention`
(via `gridExec`/`execAttnLit`); the LayerNorm rides on top as ℝ-model (`ln_budget`/reductions discharged
downstream — the same deferred gap as the FFN). The identity query/key projections collapse the projection
bounds via `matMulCoord_id`/`id_rowSum_le`; the value weight `W` and its bounds are carried. This is the
attention half of the transformer-block ROOT binding, ready to plug as `Es` into the shipped capstone. -/
noncomputable def mhBlockRootExecLayer {n d : ℕ} {h1 h2 : (n + 1) ≠ 0} (hd : 0 < d)
    {c bV γW Cγ Cβ : ℝ} (hscale : (0 : ℝ) < 1 / c) (hbV0 : 0 ≤ bV) (hγW0 : 0 ≤ γW) (hγWid : (1 : ℝ) ≤ γW)
    (W : Fin d → Fin d → ℝ) (hγWVO : ∀ (_ : Fin 1) j, (∑ k, |W k j|) ≤ γW)
    (γ β : Fin d → ℝ) (hCγ : ∀ j, |γ j| ≤ Cγ) (hCβ : ∀ j, |β j| ≤ Cβ)
    (hidB : ∀ y ∈ Metric.closedBall (0 : Fin (n + 1) → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ i e, |y i e| ≤ Real.sqrt d * Cγ + Cβ)
    (hVB : ∀ y ∈ Metric.closedBall (0 : Fin (n + 1) → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ (_ : Fin 1) j, ‖matMulCoord W y j‖ ≤ bV)
    (inputs : Finset (Fin (n + 1) → Fin d → IEEE32Exec))
    (ctxOf : (Fin (n + 1) → Fin d → IEEE32Exec) →
      Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2)
    {attn_rnd : ℝ} (hattn_rnd : 0 ≤ attn_rnd)
    (hregime : ∀ Yt ∈ inputs, dist (execAttnLit (ctxOf Yt))
        (attnHead (1 / c) W (fun a b => toReal (Yt a b))) ≤ attn_rnd)
    (hinj : ∀ Yt ∈ inputs, ∀ Yt' ∈ inputs,
        (fun a b => toReal (Yt a b)) = (fun (a : Fin (n + 1)) (b : Fin d) => toReal (Yt' a b)) →
        Yt = Yt')
    (meanOf stdOf : (Fin (n + 1) → Fin d → ℝ) → Fin (n + 1) → ℝ)
    {ln_budget Λ_ln : ℝ} (hΛ_ln : 0 ≤ Λ_ln)
    (hln : ∀ y : Fin (n + 1) → Fin d → ℝ, ‖y‖ ≤ Real.sqrt d * Cγ + Cβ →
        dist (lnStarExec γ β (meanOf y) (stdOf y)
              (y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y))
            (layerNormCoord γ β (y + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf y)) ≤ ln_budget)
    (hlnlip : ∀ a b : Fin (n + 1) → Fin d → ℝ,
        dist (layerNormCoord γ β a) (layerNormCoord γ β b) ≤ Λ_ln * dist a b) :
    ExecLayer (Fin (n + 1) → Fin d → ℝ) :=
  clampedMHBlockExecLayer hd hscale
    (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (le_trans (abs_nonneg _) (hCγ ⟨0, hd⟩)))
      (le_trans (abs_nonneg _) (hCβ ⟨0, hd⟩))) hbV0 hγW0
    (fun _ k j => if k = j then 1 else 0) (fun _ k j => if k = j then 1 else 0) (fun _ => W)
    (fun _ j => id_rowSum_le hγWid j) (fun _ j => id_rowSum_le hγWid j) hγWVO γ β hCγ hCβ
    (fun y hy _ i e => by simpa only [matMulCoord_id] using hidB y hy i e)
    (fun y hy _ k' e => by simpa only [matMulCoord_id] using hidB y hy k' e)
    (fun y hy h j => hVB y hy h j)
    (fun x => lnStarExec γ β (meanOf (clampCoord (Real.sqrt d * Cγ + Cβ) x))
      (stdOf (clampCoord (Real.sqrt d * Cγ + Cβ) x))
      (clampCoord (Real.sqrt d * Cγ + Cβ) x
        + gridExec (Real.sqrt d * Cγ + Cβ) c W inputs ctxOf (clampCoord (Real.sqrt d * Cγ + Cβ) x)))
    (ln_budget + Λ_ln * attn_rnd)
    (mhBlockRoot_hrnd c W (le_trans (abs_nonneg _) (hCγ ⟨0, hd⟩)) (le_trans (abs_nonneg _) (hCβ ⟨0, hd⟩))
      inputs ctxOf hattn_rnd hregime hinj γ β meanOf stdOf hΛ_ln hln hlnlip)

end

end TLT.MHBlockRoot
