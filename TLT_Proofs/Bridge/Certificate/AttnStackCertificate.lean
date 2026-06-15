/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Certificate.AttentionTransformerCertificate
import TLT_Proofs.Bridge.Lipschitz.ParameterPerturbationEnvelope

/-!
# Depth-graded soft-attention capacity: the multi-block stack

The post-norm attention block `B_θ(X) = layerNorm_{γ,β}(X + selfAttn X)` is the standard transformer
attention sublayer. It is forward-invariant on the supremum-norm ball (layer-norm bounds its output),
input-Lipschitz there (layer-norm ∘ residual ∘ self-attention, each Lipschitz on the ball), and
weight-Lipschitz in its affine parameters. So a depth-`L` stack of these blocks is a `ParamLayerLocal`
list, and `paramComp_param_lipschitz_on'` (depth-uniform) yields the depth-`L` value-vector Lipschitz
constant `lparamLipBound`, the soft side of the depth-graded boundary.

## Main results

- `normAttnBlock_input_lip`: the block is input-Lipschitz on the ball.
- `normAttnBlock_param_lip`: the block is Lipschitz in its `γ, β` weights.
- `normAttnBlock_forward_inv`: the block maps the ball into itself.
-/

/-!
## References
- [31] self-attention on-ball Lipschitz `4ndB²/scale+1`; [32] attention capacity; [33] seq-length-
  free depth/head; [41] weight-tied universal-transformer; [16][54][26] Dudley/covering; LayerNorm
  Lipschitz.
-/

open MeasureTheory

noncomputable section

namespace TLT

variable {n d : ℕ}

/-- **The post-norm attention block is input-Lipschitz on the ball.** Layer-norm is globally
`Cγ·(2√d+2)/√ε`-Lipschitz; the residual self-attention `X ↦ X + selfAttn X` is `1 + L_attn`-Lipschitz
on the ball (`L_attn = 4·n·d·B²/scale + 1`); the composition is their product. -/
lemma normAttnBlock_input_lip [NeZero n] (hd : 0 < d) {scale B : ℝ} (hscale : 0 < scale) (hB : 0 ≤ B)
    (γ β : Fin d → ℝ) {Cγ : ℝ} (hCγ : ∀ j, |γ j| ≤ Cγ)
    (Xa Xb : Fin n → Fin d → ℝ) (hXa : ∀ i, ‖Xa i‖ ≤ B) (hXb : ∀ i, ‖Xb i‖ ≤ B) :
    dist (normAttnCoord γ β (selfAttn scale) Xa) (normAttnCoord γ β (selfAttn scale) Xb)
      ≤ Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon
          * (1 + (4 * (d * B ^ 2 / scale) + 1)) * dist Xa Xb := by
  have hsA : ‖selfAttn scale Xa - selfAttn scale Xb‖ ≤ (4 * (d * B ^ 2 / scale) + 1) * ‖Xa - Xb‖ :=
    selfAttn_lipschitz_on_ball hscale hB Xa Xb hXa hXb
  have hCγ0 : 0 ≤ Cγ := le_trans (abs_nonneg _) (hCγ ⟨0, hd⟩)
  have hLsA0 : (0:ℝ) ≤ 4 * (d * B ^ 2 / scale) + 1 := by
    have : (0:ℝ) ≤ 4 * (d * B ^ 2 / scale) :=
      mul_nonneg (by positivity) (div_nonneg (by positivity) hscale.le)
    linarith
  -- the residual argument moves by at most `(1 + L_attn)·dist`
  have hresid : dist (fun i j => Xa i j + selfAttn scale Xa i j)
      (fun i j => Xb i j + selfAttn scale Xb i j : Fin n → Fin d → ℝ)
      ≤ (1 + (4 * (d * B ^ 2 / scale) + 1)) * dist Xa Xb := by
    refine (dist_pi_le_iff (by positivity)).mpr (fun i => ?_)
    refine (dist_pi_le_iff (by positivity)).mpr (fun j => ?_)
    rw [Real.dist_eq]
    calc |(Xa i j + selfAttn scale Xa i j) - (Xb i j + selfAttn scale Xb i j)|
        ≤ |Xa i j - Xb i j| + |selfAttn scale Xa i j - selfAttn scale Xb i j| := by
          rw [show (Xa i j + selfAttn scale Xa i j) - (Xb i j + selfAttn scale Xb i j)
                = (Xa i j - Xb i j) + (selfAttn scale Xa i j - selfAttn scale Xb i j) from by ring]
          exact abs_add_le _ _
      _ ≤ dist Xa Xb + (4 * (d * B ^ 2 / scale) + 1) * dist Xa Xb := by
          refine add_le_add ?_ ?_
          · exact le_trans (le_trans (le_of_eq (Real.dist_eq _ _).symm) (dist_le_pi_dist (Xa i) (Xb i) j))
              (dist_le_pi_dist Xa Xb i)
          · rw [show selfAttn scale Xa i j - selfAttn scale Xb i j
                  = (selfAttn scale Xa - selfAttn scale Xb) i j from rfl, ← Real.norm_eq_abs, dist_eq_norm]
            exact le_trans (le_trans (norm_le_pi_norm _ j) (norm_le_pi_norm _ i)) hsA
      _ = (1 + (4 * (d * B ^ 2 / scale) + 1)) * dist Xa Xb := by ring
  calc dist (normAttnCoord γ β (selfAttn scale) Xa) (normAttnCoord γ β (selfAttn scale) Xb)
      = dist (layerNormCoord γ β (fun i j => Xa i j + selfAttn scale Xa i j))
             (layerNormCoord γ β (fun i j => Xb i j + selfAttn scale Xb i j)) := by
        rw [normAttnCoord, normAttnCoord]
    _ ≤ Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon
          * dist (fun i j => Xa i j + selfAttn scale Xa i j)
                 (fun i j => Xb i j + selfAttn scale Xb i j) :=
        layerNormCoord_lipschitz hd γ β hCγ _ _
    _ ≤ Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon
          * ((1 + (4 * (d * B ^ 2 / scale) + 1)) * dist Xa Xb) :=
        mul_le_mul_of_nonneg_left hresid
          (by have : 0 < Real.sqrt Numbers.epsilon := Real.sqrt_pos.mpr numbers_epsilon_real_pos
              exact div_nonneg (mul_nonneg hCγ0 (by positivity)) (Real.sqrt_nonneg _))
    _ = Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon
          * (1 + (4 * (d * B ^ 2 / scale) + 1)) * dist Xa Xb := by ring

/-- **The post-norm attention block is Lipschitz in its affine weights.** Only the final layer-norm
carries `γ, β`; the residual self-attention is weight-free, so `layerNormCoord_param_lipschitz` applies
to the common residual input. -/
lemma normAttnBlock_param_lip [NeZero n] (hd : 0 < d) {scale : ℝ} (γ β γ' β' : Fin d → ℝ)
    (X : Fin n → Fin d → ℝ) :
    dist (normAttnCoord γ β (selfAttn scale) X) (normAttnCoord γ' β' (selfAttn scale) X)
      ≤ Real.sqrt d * dist γ γ' + dist β β' := by
  rw [normAttnCoord, normAttnCoord]
  exact layerNormCoord_param_lipschitz hd γ β γ' β' _

/-- **The post-norm attention block is forward-invariant on the ball.** Layer-norm caps its output at
`√d·Cγ + Cβ` regardless of input. -/
lemma normAttnBlock_forward_inv (hd : 0 < d) (γ β : Fin d → ℝ) {Cγ Cβ : ℝ}
    (hCγ : ∀ j, |γ j| ≤ Cγ) (hCβ : ∀ j, |β j| ≤ Cβ) (scale : ℝ) (X : Fin n → Fin d → ℝ) :
    ‖normAttnCoord γ β (selfAttn scale) X‖ ≤ Real.sqrt d * Cγ + Cβ := by
  rw [normAttnCoord]
  exact layerNormCoord_norm_le hd γ β hCγ hCβ _

/-- **Self-attention is continuous in its input.** Each output row is the value-mix of the per-row
softmax scores; the scores and value matrix are continuous, so `continuous_attnVec_uncurry` applies. -/
lemma continuous_selfAttn {n d : ℕ} [NeZero n] (scale : ℝ) :
    Continuous (selfAttn scale (n := n) (d := d)) := by
  refine continuous_pi (fun i => ?_)
  simp only [selfAttn]
  exact continuous_attnVec_uncurry.comp ((continuous_attnScores_self i).prodMk continuous_id)

/-- **Joint continuity of coordinate layer-norm in `(γ, β, input)`.** The normalized coordinate is
input-continuous (the denominator `rowStdCoord` never vanishes); the affine scale/shift are linear in
`(γ, β)`. -/
lemma continuous_layerNormCoord_uncurry {s d : ℕ} {Θ : Type*} [TopologicalSpace Θ]
    {γ β : Θ → Fin d → ℝ} (hγ : Continuous γ) (hβ : Continuous β)
    {Y : Θ → Fin s → Fin d → ℝ} (hY : Continuous Y) :
    Continuous (fun θ => layerNormCoord (γ θ) (β θ) (Y θ)) := by
  unfold layerNormCoord
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  refine (((((continuous_apply_apply i j).comp hY).sub ((continuous_rowMeanCoord i).comp hY)).div
    ((continuous_rowStdCoord i).comp hY) (fun θ => ne_of_gt (rowStdCoord_pos i (Y θ)))).mul
    ((continuous_apply j).comp hγ)).add ((continuous_apply j).comp hβ)

open Capacity

/-- **Joint continuity of the post-norm attention block in `(weights, input)`.** The block is
`layerNorm_{γ θ, β θ}(X + selfAttn X)`: the residual self-attention is input-continuous and weight-free,
`γ, β` are weight-continuous, and layer-norm is jointly continuous. -/
lemma continuous_normAttnBlock_weight {n d q : ℕ} [NeZero n] {scale : ℝ}
    {γ β : ParamSpace q → (Fin d → ℝ)} (hγ : Continuous γ) (hβ : Continuous β) :
    Continuous (fun p : ParamSpace q × (Fin n → Fin d → ℝ) =>
      normAttnCoord (γ p.1) (β p.1) (selfAttn scale) p.2) := by
  unfold normAttnCoord
  refine continuous_layerNormCoord_uncurry (hγ.comp continuous_fst) (hβ.comp continuous_fst) ?_
  exact continuous_pi (fun i => continuous_pi (fun j =>
    ((continuous_apply_apply i j).comp continuous_snd).add
      ((continuous_apply_apply i j).comp ((continuous_selfAttn scale).comp continuous_snd))))

/-- **Continuity in `(weights, input)` of the threaded layer composition.** Given that each layer map
is jointly continuous, the composed `lparamComp` (threading one weight through all layers) is jointly
continuous, by induction on the layer list. -/
lemma continuous_lparamComp_uncurry {Θ V : Type*} [PseudoMetricSpace Θ] [PseudoMetricSpace V]
    (Ls : List (ParamLayerLocal Θ V))
    (hc : ∀ L ∈ Ls, Continuous (fun p : Θ × V => L.map p.1 p.2)) :
    Continuous (fun p : Θ × V => lparamComp Ls p.1 p.2) := by
  induction Ls with
  | nil => simp only [lparamComp]; exact continuous_snd
  | cons L Ls ih =>
      simp only [lparamComp]
      exact (ih (fun L' hL' => hc L' (List.mem_cons_of_mem L hL'))).comp
        (continuous_fst.prodMk (hc L List.mem_cons_self))

/-- The post-norm attention block as a depth-uniform `ParamLayerLocal`: its input-Lipschitz constant
(on the activation ball of radius `√d·Cγ + Cβ`) and its `√d·Lγ + Lβ` weight-Lipschitz constant. -/
noncomputable def normAttnBlock {n d p : ℕ} [NeZero n] {scale Cγ Cβ Lγ Lβ : ℝ} (hscale : 0 < scale)
    (hCγ0 : 0 ≤ Cγ) (_hCβ0 : 0 ≤ Cβ) (hLγ0 : 0 ≤ Lγ) (hLβ0 : 0 ≤ Lβ)
    (γ β : ParamSpace p → (Fin d → ℝ)) :
    ParamLayerLocal (ParamSpace p) (Fin n → Fin d → ℝ) where
  map θ X := normAttnCoord (γ θ) (β θ) (selfAttn scale) X
  paramLip := Real.sqrt d * Lγ + Lβ
  lip := Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon
          * (1 + (4 * (d * (Real.sqrt d * Cγ + Cβ) ^ 2 / scale) + 1))
  paramLip_nonneg := add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hLγ0) hLβ0
  lip_nonneg := by
    have hε : 0 < Real.sqrt Numbers.epsilon := Real.sqrt_pos.mpr numbers_epsilon_real_pos
    have h1 : (0:ℝ) ≤ 4 * (d * (Real.sqrt d * Cγ + Cβ) ^ 2 / scale) :=
      mul_nonneg (by positivity) (div_nonneg (by positivity) hscale.le)
    exact mul_nonneg (div_nonneg (mul_nonneg hCγ0 (by positivity)) (Real.sqrt_nonneg _)) (by linarith)

/-- **Depth-graded soft-attention weight-Lipschitz (the headline).** A depth-`L` stack of post-norm
attention blocks (shared affine weights) is `lparamLipBound`-Lipschitz in the weights, on the
forward-invariant activation ball `↥(closedBall 0 (√d·Cγ + Cβ))`. The constant `lparamLipBound (replicate
L block)` grows with the depth `L`, the soft side of the depth-graded boundary, discharged through the
depth-uniform `paramComp_param_lipschitz_on'`. -/
theorem normAttnStack_weight_lip {n d p : ℕ} [NeZero n] (hd : 0 < d) {scale R Cγ Cβ Lγ Lβ : ℝ}
    (hscale : 0 < scale) (hCγ0 : 0 ≤ Cγ) (hCβ0 : 0 ≤ Cβ) (hLγ0 : 0 ≤ Lγ) (hLβ0 : 0 ≤ Lβ)
    (γ β : ParamSpace p → (Fin d → ℝ))
    (hγB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ θ j| ≤ Cγ)
    (hβB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β θ j| ≤ Cβ)
    (hγLip : ∀ θ θ', dist (γ θ) (γ θ') ≤ Lγ * dist θ θ')
    (hβLip : ∀ θ θ', dist (β θ) (β θ') ≤ Lβ * dist θ θ') (L : ℕ)
    {θ θ' : ParamSpace p} (hθ : θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))))
    (hθ' : θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))))
    {x : Fin n → Fin d → ℝ}
    (hx : x ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ)) :
    dist (lparamComp (List.replicate L (normAttnBlock (n := n) hscale hCγ0 hCβ0 hLγ0 hLβ0 γ β)) θ x)
         (lparamComp (List.replicate L (normAttnBlock (n := n) hscale hCγ0 hCβ0 hLγ0 hLβ0 γ β)) θ' x)
      ≤ lparamLipBound (List.replicate L (normAttnBlock (n := n) hscale hCγ0 hCβ0 hLγ0 hLβ0 γ β)) * dist θ θ' := by
  set blk := normAttnBlock (n := n) hscale hCγ0 hCβ0 hLγ0 hLβ0 γ β with hblk
  refine paramComp_param_lipschitz_on'
    (K := (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))))
    (D := Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ)) _ ?_ ?_ ?_ hθ hθ' hx
  · -- hin: input-Lipschitz on the ball
    intro Lb hLb θ₀ hθ₀ a ha b hb
    rw [List.eq_of_mem_replicate hLb, hblk]
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)] at ha hb
    exact normAttnBlock_input_lip hd hscale (by positivity) (γ θ₀) (β θ₀) (hγB θ₀ hθ₀) a b ha hb
  · -- hloc: weight-Lipschitz on the ball
    intro Lb hLb θ₀ hθ₀ θ₁ hθ₁ y _
    rw [List.eq_of_mem_replicate hLb, hblk]
    calc dist (normAttnCoord (γ θ₀) (β θ₀) (selfAttn scale) y)
              (normAttnCoord (γ θ₁) (β θ₁) (selfAttn scale) y)
        ≤ Real.sqrt d * dist (γ θ₀) (γ θ₁) + dist (β θ₀) (β θ₁) :=
          normAttnBlock_param_lip hd (γ θ₀) (β θ₀) (γ θ₁) (β θ₁) y
      _ ≤ Real.sqrt d * (Lγ * dist θ₀ θ₁) + Lβ * dist θ₀ θ₁ :=
          add_le_add (mul_le_mul_of_nonneg_left (hγLip θ₀ θ₁) (Real.sqrt_nonneg _)) (hβLip θ₀ θ₁)
      _ = (Real.sqrt d * Lγ + Lβ) * dist θ₀ θ₁ := by ring
  · -- hinv: forward-invariance
    intro Lb hLb θ₀ hθ₀ y _
    rw [List.eq_of_mem_replicate hLb, hblk, mem_closedBall_zero_iff]
    exact normAttnBlock_forward_inv hd (γ θ₀) (β θ₀) (hγB θ₀ hθ₀) (hβB θ₀ hθ₀) scale y

/-- **Depth-graded soft-attention certified generalization bound.** For a depth-`L` stack of post-norm
attention blocks `B_θ(X) = layerNorm_{γ θ, β θ}(X + selfAttn X)` (the soft, cascaded quadrant), presented
as the executed layer list `Ls` whose ideal forward at the certified weights is the clamped stack
(`hagree`): except on a sample event of McDiarmid-small probability, the executed true risk is at most
the executed empirical risk plus the closed capacity budget `2·(12√2·(1/√m)·B_int) + ε` and the rounding
correction `2·Lℓ·envBound`. The capacity constant `lparamLipBound (replicate L block)` **grows with the
depth `L`, the soft side of the depth-graded boundary; the weight-Lipschitz envelope of the stack is
discharged through the depth-uniform composition. The input cap (clamp to the activation ball of radius
`√d·Cγ + Cβ`, the layer-norm output bound) follows from self-attention's lack of a global Lipschitz
constant. -/
theorem normAttnStack_certified_generalization {n d p m : ℕ} [NeZero n] [Nonempty (Fin p)]
    [MeasurableSpace (Fin n → Fin d → ℝ)] [BorelSpace (Fin n → Fin d → ℝ)]
    {P : Measure (Fin n → Fin d → ℝ)} [IsProbabilityMeasure P]
    (hm : 0 < m) {R scale Cγ Cβ Lγ Lβ : ℝ} (hR : 0 ≤ R) (hscale : 0 < scale) (hd : 0 < d)
    (hCγ0 : 0 ≤ Cγ) (hCβ0 : 0 ≤ Cβ) (hLγ0 : 0 ≤ Lγ) (hLβ0 : 0 ≤ Lβ)
    (γ β : ParamSpace p → (Fin d → ℝ)) (hγcont : Continuous γ) (hβcont : Continuous β)
    (hγB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ θ j| ≤ Cγ)
    (hβB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β θ j| ≤ Cβ)
    (hγLip : ∀ θ θ', dist (γ θ) (γ θ') ≤ Lγ * dist θ θ')
    (hβLip : ∀ θ θ', dist (β θ) (β θ') ≤ Lβ * dist θ θ')
    (ℓ : (Fin n → Fin d → ℝ) → ℝ) {b : ℝ} (hb : 0 < b) (hℓb : ∀ v, |ℓ v| ≤ b)
    (hℓcont : Continuous ℓ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ)
    (hℓLip : ∀ u v, |ℓ u - ℓ v| ≤ Lℓ * dist u v)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R) (L : ℕ)
    (Ls : List (ExecLayer (Fin n → Fin d → ℝ)))
    (hagree : ∀ x, idealComp Ls x
        = lparamComp (List.replicate L (normAttnBlock (n := n) hscale hCγ0 hCβ0 hLγ0 hLβ0 γ β))
            (embedBase Capacity.Dyadic w_T.1) (clampCoord (Real.sqrt d * Cγ + Cβ) x))
    (hintG : Integrable (fun x => ℓ (execComp Ls x)) P)
    (hLpos : 0 < Lℓ * lparamLipBound
        (List.replicate L (normAttnBlock (n := n) hscale hCγ0 hCβ0 hLγ0 hLβ0 γ β))) :
    (Measure.pi fun _ : Fin m => P).real
        {S | ¬ ((∫ x, ℓ (execComp Ls x) ∂P)
              ≤ (1 / (m : ℝ)) * ∑ i, ℓ (execComp Ls (S i))
                + (2 * ((12 * Real.sqrt 2) * (1 / Real.sqrt m)
                    * (∫⁻ ε in Set.Ioc (0 : ℝ) (2 * b),
                        ENNReal.ofReal (Real.sqrt (Real.log 2)
                          + Real.sqrt ((p : ℝ) * (4 * R * (Lℓ * lparamLipBound
                              (List.replicate L (normAttnBlock (n := n) hscale hCγ0 hCβ0 hLγ0 hLβ0 γ β)))))
                            * ε ^ (-(1 / 2) : ℝ))).toReal) + ε)
                + 2 * (Lℓ * envBound Ls))}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) := by
  set blk := normAttnBlock (n := n) hscale hCγ0 hCβ0 hLγ0 hLβ0 γ β with hblk
  set ρ := Real.sqrt d * Cγ + Cβ with hρ
  have hρ0 : (0 : ℝ) ≤ ρ := add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCγ0) hCβ0
  set F : ParamSpace p → (Fin n → Fin d → ℝ) → ℝ :=
    fun θ x => ℓ (lparamComp (List.replicate L blk) θ (clampCoord ρ x)) with hF
  have hblkcont : ∀ Lb ∈ List.replicate L blk,
      Continuous (fun pq : ParamSpace p × (Fin n → Fin d → ℝ) => Lb.map pq.1 pq.2) := by
    intro Lb hLb
    rw [List.eq_of_mem_replicate hLb, hblk]
    exact continuous_normAttnBlock_weight hγcont hβcont
  have hstackcont : Continuous (fun pq : ParamSpace p × (Fin n → Fin d → ℝ) =>
      lparamComp (List.replicate L blk) pq.1 pq.2) := continuous_lparamComp_uncurry _ hblkcont
  have hFb : ∀ θ x, |F θ x| ≤ b := fun θ x => hℓb _
  have hFcont : ∀ x, Continuous fun θ : ParamSpace p => F θ x := fun x =>
    hℓcont.comp (hstackcont.comp (continuous_id.prodMk continuous_const))
  have hFmeas : ∀ θ, Measurable (F θ) := fun θ =>
    (hℓcont.comp ((hstackcont.comp (continuous_const.prodMk continuous_id)).comp
      (continuous_clampCoord ρ))).measurable
  have hbridge : ∀ x, F (embedBase Capacity.Dyadic w_T.1) x = ℓ (idealComp Ls x) :=
    fun x => by simp only [hF]; rw [hagree x]
  have hintF : Integrable (fun x => ℓ (idealComp Ls x)) P := by
    have heq : (fun x => ℓ (idealComp Ls x)) = F (embedBase Capacity.Dyadic w_T.1) :=
      funext fun x => (hbridge x).symm
    rw [heq]; exact integrable_of_bound_of_measurable (hFmeas _) (fun x => hFb _ x)
  have hlip : ∀ S : Fin m → (Fin n → Fin d → ℝ),
      ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      dist (valueVec F S θ) (valueVec F S θ')
        ≤ Lℓ * lparamLipBound (List.replicate L blk) * dist θ θ' := by
    intro S θ hθ θ' hθ'
    refine (dist_pi_le_iff (mul_nonneg hLpos.le dist_nonneg)).mpr (fun j => ?_)
    rw [Real.dist_eq]
    simp only [valueVec, hF]
    have hclampmem : clampCoord ρ (S j) ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) ρ := by
      rw [mem_closedBall_zero_iff]; exact clampCoord_norm_le hρ0 (S j)
    calc |ℓ (lparamComp (List.replicate L blk) θ (clampCoord ρ (S j)))
            - ℓ (lparamComp (List.replicate L blk) θ' (clampCoord ρ (S j)))|
        ≤ Lℓ * dist (lparamComp (List.replicate L blk) θ (clampCoord ρ (S j)))
              (lparamComp (List.replicate L blk) θ' (clampCoord ρ (S j))) := hℓLip _ _
      _ ≤ Lℓ * (lparamLipBound (List.replicate L blk) * dist θ θ') :=
          mul_le_mul_of_nonneg_left
            (normAttnStack_weight_lip hd hscale hCγ0 hCβ0 hLγ0 hLβ0 γ β hγB hβB hγLip hβLip L
              hθ hθ' hclampmem) hLℓ0
      _ = Lℓ * lparamLipBound (List.replicate L blk) * dist θ θ' := by ring
  exact certified_executed_generalization_dudley hm hR F hb hFb hFmeas hFcont hε w_T Ls ℓ hLℓ0
    hℓLip hbridge hintF hintG hLpos hlip

end TLT

