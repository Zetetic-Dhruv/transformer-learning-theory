/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Certificate.AttnStackCertificate
import TLT_Proofs.Bridge.Lipschitz.LinearLayerWeightLipschitz

/-!
# The full transformer encoder stack: adding the feed-forward block

T1 (`AttnStackCertificate`) gave the depth-graded soft-attention capacity. The full transformer
encoder layer is the post-norm attention block followed by a post-norm feed-forward residual block
`layerNorm_{γ₂,β₂}(Y + ffn Y)`. This file adds the feed-forward sub-block as a `ParamLayerLocal`:

* `ffnCoord_input_lipschitz` — the feed-forward map is globally `bW₁·bW₂`-Lipschitz in the input
  (`bW₁, bW₂` the column-ℓ¹ norms of the two weight matrices) — unlike attention, no input cap is
  needed (linear ∘ ReLU ∘ linear is globally Lipschitz);
* `ffnCoord_param_lipschitz` — the feed-forward map is Lipschitz in its `(W₁, b₁, W₂, b₂)` weights on
  the bounded input domain.

These are the missing capacity ingredients (the minimal-FFN certificate kept its capacity abstract);
together with the layer-norm estimates they make the feed-forward residual block a depth-uniform
`ParamLayerLocal`, so the full encoder stack composes through `paramComp_param_lipschitz_on'` exactly
as the attention stack does.
-/

/-!
## References
- [36] FFN globally Lipschitz; [31] residual self-attention on-ball; [33] seq-length-free depth-
  graded capacity; [41] universal-transformer; [16][54][26] Dudley/covering; LayerNorm Lipschitz.
- Provenance: Innovation (executed instantiation) — the depth-L full single-head encoder stack
  certified bound; supporting FFN/LayerNorm/residual Lipschitz lemmas are matched.
-/

open MeasureTheory

noncomputable section

namespace TLT

variable {s d h : ℕ}

/-- **The feed-forward block is globally input-Lipschitz.** `ffnCoord = (·W₂) ∘ relu ∘ (·W₁ + b₁) + b₂`
moves by at most `bW₁·bW₂·dist X X'`, where `bW₁ ≥ ∑ₖ|W₁ k l|` and `bW₂ ≥ ∑ₗ|W₂ l j|` are column-ℓ¹
bounds: the inner linear map contracts by `bW₁`, ReLU is `1`-Lipschitz, the outer linear map by `bW₂`.
No input cap is needed — linear/ReLU layers are globally Lipschitz (contrast self-attention). -/
lemma ffnCoord_input_lipschitz (W1 : Fin d → Fin h → ℝ) (b1 : Fin h → ℝ)
    (W2 : Fin h → Fin d → ℝ) (b2 : Fin d → ℝ) {bW1 bW2 : ℝ} (hbW1 : 0 ≤ bW1) (hbW2 : 0 ≤ bW2)
    (hW1 : ∀ l, (∑ k, |W1 k l|) ≤ bW1) (hW2 : ∀ j, (∑ l, |W2 l j|) ≤ bW2)
    (X X' : Fin s → Fin d → ℝ) :
    dist (ffnCoord W1 b1 W2 b2 X) (ffnCoord W1 b1 W2 b2 X') ≤ bW1 * bW2 * dist X X' := by
  have hC : (0 : ℝ) ≤ bW1 * bW2 * dist X X' := mul_nonneg (mul_nonneg hbW1 hbW2) dist_nonneg
  refine (dist_pi_le_iff hC).mpr fun i => ?_
  refine (dist_pi_le_iff hC).mpr fun j => ?_
  rw [Real.dist_eq]
  simp only [ffnCoord, add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
  calc |∑ l, (max (matMulCoord W1 X i l + b1 l) 0 * W2 l j
              - max (matMulCoord W1 X' i l + b1 l) 0 * W2 l j)|
      ≤ ∑ l, |max (matMulCoord W1 X i l + b1 l) 0 * W2 l j
              - max (matMulCoord W1 X' i l + b1 l) 0 * W2 l j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, |matMulCoord W1 X i l - matMulCoord W1 X' i l| * |W2 l j| := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [← sub_mul, abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        calc |max (matMulCoord W1 X i l + b1 l) 0 - max (matMulCoord W1 X' i l + b1 l) 0|
            ≤ |(matMulCoord W1 X i l + b1 l) - (matMulCoord W1 X' i l + b1 l)| :=
              abs_max_sub_max_le_abs _ _ _
          _ = |matMulCoord W1 X i l - matMulCoord W1 X' i l| := by rw [add_sub_add_right_eq_sub]
    _ ≤ ∑ l, bW1 * dist X X' * |W2 l j| := by
        refine Finset.sum_le_sum fun l _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        calc |matMulCoord W1 X i l - matMulCoord W1 X' i l|
            = |∑ k, (X i k - X' i k) * W1 k l| := by
              simp only [matMulCoord, ← Finset.sum_sub_distrib, ← sub_mul]
          _ ≤ ∑ k, |X i k - X' i k| * |W1 k l| :=
              (Finset.abs_sum_le_sum_abs _ _).trans
                (le_of_eq (Finset.sum_congr rfl fun k _ => abs_mul _ _))
          _ ≤ ∑ k, dist X X' * |W1 k l| := by
              refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              rw [← Real.dist_eq]
              exact le_trans (dist_le_pi_dist (X i) (X' i) k) (dist_le_pi_dist X X' i)
          _ = dist X X' * ∑ k, |W1 k l| := by rw [Finset.mul_sum]
          _ ≤ dist X X' * bW1 := mul_le_mul_of_nonneg_left (hW1 l) dist_nonneg
          _ = bW1 * dist X X' := by ring
    _ = bW1 * dist X X' * ∑ l, |W2 l j| := by rw [← Finset.mul_sum]
    _ ≤ bW1 * dist X X' * bW2 :=
        mul_le_mul_of_nonneg_left (hW2 j) (mul_nonneg hbW1 dist_nonneg)
    _ = bW1 * bW2 * dist X X' := by ring

/-- **A post-norm residual block is input-Lipschitz, for any input-Lipschitz inner map.** The block
`layerNorm_{γ,β}(X + f X)` moves by `Cγ·(2√d+2)/√ε · (1 + L_f)` times the input distance: layer-norm is
globally Lipschitz, and the residual `X ↦ X + f X` is `(1 + L_f)`-Lipschitz. Used for both
`f = selfAttn` (Lipschitz only on the ball) and `f = ffnCoord` (globally Lipschitz). -/
lemma normResidualBlock_input_lip (hd : 0 < d) (γ β : Fin d → ℝ) {Cγ : ℝ} (hCγ : ∀ j, |γ j| ≤ Cγ)
    {f : (Fin s → Fin d → ℝ) → (Fin s → Fin d → ℝ)} {Lf : ℝ} (hLf0 : 0 ≤ Lf)
    (Xa Xb : Fin s → Fin d → ℝ) (hf : dist (f Xa) (f Xb) ≤ Lf * dist Xa Xb) :
    dist (normAttnCoord γ β f Xa) (normAttnCoord γ β f Xb)
      ≤ Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon * (1 + Lf) * dist Xa Xb := by
  have hCγ0 : 0 ≤ Cγ := le_trans (abs_nonneg _) (hCγ ⟨0, hd⟩)
  have hresid : dist (fun i j => Xa i j + f Xa i j)
      (fun i j => Xb i j + f Xb i j : Fin s → Fin d → ℝ) ≤ (1 + Lf) * dist Xa Xb := by
    refine (dist_pi_le_iff (by positivity)).mpr (fun i => ?_)
    refine (dist_pi_le_iff (by positivity)).mpr (fun j => ?_)
    rw [Real.dist_eq]
    calc |(Xa i j + f Xa i j) - (Xb i j + f Xb i j)|
        ≤ |Xa i j - Xb i j| + |f Xa i j - f Xb i j| := by
          rw [show (Xa i j + f Xa i j) - (Xb i j + f Xb i j)
                = (Xa i j - Xb i j) + (f Xa i j - f Xb i j) from by ring]
          exact abs_add_le _ _
      _ ≤ dist Xa Xb + Lf * dist Xa Xb := by
          refine add_le_add ?_ ?_
          · exact le_trans (le_trans (le_of_eq (Real.dist_eq _ _).symm)
              (dist_le_pi_dist (Xa i) (Xb i) j)) (dist_le_pi_dist Xa Xb i)
          · calc |f Xa i j - f Xb i j| = dist (f Xa i j) (f Xb i j) := (Real.dist_eq _ _).symm
              _ ≤ dist (f Xa i) (f Xb i) := dist_le_pi_dist (f Xa i) (f Xb i) j
              _ ≤ dist (f Xa) (f Xb) := dist_le_pi_dist (f Xa) (f Xb) i
              _ ≤ Lf * dist Xa Xb := hf
      _ = (1 + Lf) * dist Xa Xb := by ring
  calc dist (normAttnCoord γ β f Xa) (normAttnCoord γ β f Xb)
      = dist (layerNormCoord γ β (fun i j => Xa i j + f Xa i j))
             (layerNormCoord γ β (fun i j => Xb i j + f Xb i j)) := by rw [normAttnCoord, normAttnCoord]
    _ ≤ Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon
          * dist (fun i j => Xa i j + f Xa i j) (fun i j => Xb i j + f Xb i j) :=
        layerNormCoord_lipschitz hd γ β hCγ _ _
    _ ≤ Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon * ((1 + Lf) * dist Xa Xb) :=
        mul_le_mul_of_nonneg_left hresid
          (by have : 0 < Real.sqrt Numbers.epsilon := Real.sqrt_pos.mpr numbers_epsilon_real_pos
              exact div_nonneg (mul_nonneg hCγ0 (by positivity)) (Real.sqrt_nonneg _))
    _ = Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon * (1 + Lf) * dist Xa Xb := by ring

/-- **A post-norm residual block is Lipschitz in its `γ, β` weights** (the inner map is weight-free).
Reduces to layer-norm's parameter-Lipschitz estimate on the common residual input. -/
lemma normResidualBlock_param_lip (hd : 0 < d) (γ β γ' β' : Fin d → ℝ)
    (f : (Fin s → Fin d → ℝ) → (Fin s → Fin d → ℝ)) (X : Fin s → Fin d → ℝ) :
    dist (normAttnCoord γ β f X) (normAttnCoord γ' β' f X) ≤ Real.sqrt d * dist γ γ' + dist β β' := by
  rw [normAttnCoord, normAttnCoord]
  exact layerNormCoord_param_lipschitz hd γ β γ' β' _

/-- **A post-norm residual block is forward-invariant on the ball.** Layer-norm caps its output at
`√d·Cγ + Cβ` regardless of input. -/
lemma normResidualBlock_forward_inv (hd : 0 < d) (γ β : Fin d → ℝ) {Cγ Cβ : ℝ}
    (hCγ : ∀ j, |γ j| ≤ Cγ) (hCβ : ∀ j, |β j| ≤ Cβ)
    (f : (Fin s → Fin d → ℝ) → (Fin s → Fin d → ℝ)) (X : Fin s → Fin d → ℝ) :
    ‖normAttnCoord γ β f X‖ ≤ Real.sqrt d * Cγ + Cβ := by
  rw [normAttnCoord]
  exact layerNormCoord_norm_le hd γ β hCγ hCβ _

open Capacity

/-- The post-norm feed-forward residual block as a depth-uniform `ParamLayerLocal`: the feed-forward
inner map has fixed weights (input-Lipschitz constant `bW₁·bW₂`), and the learnable parameters are the
post-norm layer-norm affine `(γ, β)` — exactly the parameter class of the attention block, so the two
compose into one transformer encoder stack. -/
noncomputable def normFFNBlock {s d h p : ℕ} {Cγ Cβ Lγ Lβ bW1 bW2 : ℝ}
    (hCγ0 : 0 ≤ Cγ) (_hCβ0 : 0 ≤ Cβ) (hLγ0 : 0 ≤ Lγ) (hLβ0 : 0 ≤ Lβ)
    (hbW1 : 0 ≤ bW1) (hbW2 : 0 ≤ bW2)
    (W1 : Fin d → Fin h → ℝ) (b1 : Fin h → ℝ) (W2 : Fin h → Fin d → ℝ) (b2 : Fin d → ℝ)
    (γ β : ParamSpace p → (Fin d → ℝ)) :
    ParamLayerLocal (ParamSpace p) (Fin s → Fin d → ℝ) where
  map θ X := normAttnCoord (γ θ) (β θ) (ffnCoord W1 b1 W2 b2) X
  paramLip := Real.sqrt d * Lγ + Lβ
  lip := Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon * (1 + bW1 * bW2)
  paramLip_nonneg := add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hLγ0) hLβ0
  lip_nonneg := by
    have hε : 0 < Real.sqrt Numbers.epsilon := Real.sqrt_pos.mpr numbers_epsilon_real_pos
    exact mul_nonneg (div_nonneg (mul_nonneg hCγ0 (by positivity)) (Real.sqrt_nonneg _))
      (add_nonneg zero_le_one (mul_nonneg hbW1 hbW2))

/-- **Depth-graded full-transformer weight-Lipschitz (the T2 headline).** A depth-`L` stack of
transformer encoder layers — each layer the post-norm attention block followed by the post-norm
feed-forward residual block (`[attnBlock, ffnBlock]`, flattened over `L` copies) — is
`lparamLipBound`-Lipschitz in the learnable layer-norm weights, on the forward-invariant activation
ball `closedBall 0 (√d·Cγ + Cβ)`. The constant grows with depth `L`: the full transformer's
depth-graded soft capacity, discharged through `paramComp_param_lipschitz_on'` exactly as the
attention-only stack, with each block's input-Lipschitz, weight-Lipschitz, and forward-invariance
estimate dispatched by whether it is the attention or feed-forward block. -/
theorem transformerEncoderStack_weight_lip {s d hdim p : ℕ} [NeZero s] (hd : 0 < d)
    {scale R Cγ Cβ Lγ Lβ bW1 bW2 : ℝ} (hscale : 0 < scale) (hCγ0 : 0 ≤ Cγ) (hCβ0 : 0 ≤ Cβ)
    (hLγ0 : 0 ≤ Lγ) (hLβ0 : 0 ≤ Lβ) (hbW1 : 0 ≤ bW1) (hbW2 : 0 ≤ bW2)
    (W1 : Fin d → Fin hdim → ℝ) (b1 : Fin hdim → ℝ) (W2 : Fin hdim → Fin d → ℝ) (b2 : Fin d → ℝ)
    (hW1c : ∀ l, (∑ k, |W1 k l|) ≤ bW1) (hW2c : ∀ j, (∑ l, |W2 l j|) ≤ bW2)
    (γ1 β1 γ2 β2 : ParamSpace p → (Fin d → ℝ))
    (hγ1B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ1 θ j| ≤ Cγ)
    (hβ1B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β1 θ j| ≤ Cβ)
    (hγ2B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ2 θ j| ≤ Cγ)
    (hβ2B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β2 θ j| ≤ Cβ)
    (hγ1Lip : ∀ θ θ', dist (γ1 θ) (γ1 θ') ≤ Lγ * dist θ θ')
    (hβ1Lip : ∀ θ θ', dist (β1 θ) (β1 θ') ≤ Lβ * dist θ θ')
    (hγ2Lip : ∀ θ θ', dist (γ2 θ) (γ2 θ') ≤ Lγ * dist θ θ')
    (hβ2Lip : ∀ θ θ', dist (β2 θ) (β2 θ') ≤ Lβ * dist θ θ') (L : ℕ)
    {θ θ' : ParamSpace p} (hθ : θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))))
    (hθ' : θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))))
    {x : Fin s → Fin d → ℝ}
    (hx : x ∈ Metric.closedBall (0 : Fin s → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ)) :
    dist (lparamComp (List.flatten (List.replicate L
            [normAttnBlock (n := s) hscale hCγ0 hCβ0 hLγ0 hLβ0 γ1 β1,
             normFFNBlock (s := s) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2])) θ x)
         (lparamComp (List.flatten (List.replicate L
            [normAttnBlock (n := s) hscale hCγ0 hCβ0 hLγ0 hLβ0 γ1 β1,
             normFFNBlock (s := s) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2])) θ' x)
      ≤ lparamLipBound (List.flatten (List.replicate L
            [normAttnBlock (n := s) hscale hCγ0 hCβ0 hLγ0 hLβ0 γ1 β1,
             normFFNBlock (s := s) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2])) * dist θ θ' := by
  set aBlk := normAttnBlock (n := s) hscale hCγ0 hCβ0 hLγ0 hLβ0 γ1 β1 with haBlk
  set fBlk := normFFNBlock (s := s) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2 with hfBlk
  have hρ0 : (0 : ℝ) ≤ Real.sqrt d * Cγ + Cβ := add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCγ0) hCβ0
  have hmem : ∀ Lb ∈ List.flatten (List.replicate L [aBlk, fBlk]), Lb = aBlk ∨ Lb = fBlk := by
    intro Lb hLb
    rcases List.mem_flatten.mp hLb with ⟨t, ht, hLbt⟩
    rw [List.eq_of_mem_replicate ht] at hLbt
    simpa using hLbt
  refine paramComp_param_lipschitz_on'
    (K := (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))))
    (D := Metric.closedBall (0 : Fin s → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ)) _ ?_ ?_ ?_ hθ hθ' hx
  · -- hin: each block input-Lipschitz on the ball
    intro Lb hLb θ₀ hθ₀ a ha b hb
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hρ0] at ha hb
    rcases hmem Lb hLb with h | h
    · rw [h, haBlk]
      exact normAttnBlock_input_lip hd hscale hρ0 (γ1 θ₀) (β1 θ₀) (hγ1B θ₀ hθ₀) a b ha hb
    · rw [h, hfBlk]
      exact normResidualBlock_input_lip hd (γ2 θ₀) (β2 θ₀) (hγ2B θ₀ hθ₀) (mul_nonneg hbW1 hbW2) a b
        (ffnCoord_input_lipschitz W1 b1 W2 b2 hbW1 hbW2 hW1c hW2c a b)
  · -- hloc: each block weight-Lipschitz on the ball
    intro Lb hLb θ₀ hθ₀ θ₁ hθ₁ y _
    rcases hmem Lb hLb with h | h
    · rw [h, haBlk]
      calc dist (normAttnCoord (γ1 θ₀) (β1 θ₀) (selfAttn scale) y)
                (normAttnCoord (γ1 θ₁) (β1 θ₁) (selfAttn scale) y)
          ≤ Real.sqrt d * dist (γ1 θ₀) (γ1 θ₁) + dist (β1 θ₀) (β1 θ₁) :=
            normResidualBlock_param_lip hd (γ1 θ₀) (β1 θ₀) (γ1 θ₁) (β1 θ₁) (selfAttn scale) y
        _ ≤ Real.sqrt d * (Lγ * dist θ₀ θ₁) + Lβ * dist θ₀ θ₁ :=
            add_le_add (mul_le_mul_of_nonneg_left (hγ1Lip θ₀ θ₁) (Real.sqrt_nonneg _)) (hβ1Lip θ₀ θ₁)
        _ = (Real.sqrt d * Lγ + Lβ) * dist θ₀ θ₁ := by ring
    · rw [h, hfBlk]
      calc dist (normAttnCoord (γ2 θ₀) (β2 θ₀) (ffnCoord W1 b1 W2 b2) y)
                (normAttnCoord (γ2 θ₁) (β2 θ₁) (ffnCoord W1 b1 W2 b2) y)
          ≤ Real.sqrt d * dist (γ2 θ₀) (γ2 θ₁) + dist (β2 θ₀) (β2 θ₁) :=
            normResidualBlock_param_lip hd (γ2 θ₀) (β2 θ₀) (γ2 θ₁) (β2 θ₁) (ffnCoord W1 b1 W2 b2) y
        _ ≤ Real.sqrt d * (Lγ * dist θ₀ θ₁) + Lβ * dist θ₀ θ₁ :=
            add_le_add (mul_le_mul_of_nonneg_left (hγ2Lip θ₀ θ₁) (Real.sqrt_nonneg _)) (hβ2Lip θ₀ θ₁)
        _ = (Real.sqrt d * Lγ + Lβ) * dist θ₀ θ₁ := by ring
  · -- hinv: each block forward-invariant
    intro Lb hLb θ₀ hθ₀ y _
    rw [mem_closedBall_zero_iff]
    rcases hmem Lb hLb with h | h
    · rw [h, haBlk]
      exact normResidualBlock_forward_inv hd (γ1 θ₀) (β1 θ₀) (hγ1B θ₀ hθ₀) (hβ1B θ₀ hθ₀)
        (selfAttn scale) y
    · rw [h, hfBlk]
      exact normResidualBlock_forward_inv hd (γ2 θ₀) (β2 θ₀) (hγ2B θ₀ hθ₀) (hβ2B θ₀ hθ₀)
        (ffnCoord W1 b1 W2 b2) y

/-- **Joint continuity of the feed-forward residual block in `(weights, input)`.** Mirrors the
attention block: layer-norm is jointly continuous, the feed-forward inner map is input-continuous and
weight-free, and `γ, β` are weight-continuous. -/
lemma continuous_normFFNBlock_weight {s d hdim q : ℕ}
    (W1 : Fin d → Fin hdim → ℝ) (b1 : Fin hdim → ℝ) (W2 : Fin hdim → Fin d → ℝ) (b2 : Fin d → ℝ)
    {γ β : ParamSpace q → (Fin d → ℝ)} (hγ : Continuous γ) (hβ : Continuous β) :
    Continuous (fun pq : ParamSpace q × (Fin s → Fin d → ℝ) =>
      normAttnCoord (γ pq.1) (β pq.1) (ffnCoord W1 b1 W2 b2) pq.2) := by
  unfold normAttnCoord
  refine continuous_layerNormCoord_uncurry (hγ.comp continuous_fst) (hβ.comp continuous_fst) ?_
  exact continuous_pi (fun i => continuous_pi (fun j =>
    ((continuous_apply_apply i j).comp continuous_snd).add
      ((continuous_apply_apply i j).comp ((continuous_ffnCoord W1 b1 W2 b2).comp continuous_snd))))

/-- **Depth-graded full-transformer certified generalization bound (the T2 capstone).** For a depth-`L`
stack of transformer encoder layers (post-norm attention block ∘ post-norm feed-forward residual
block), presented as the executed layer list `Ls` whose ideal forward at the certified weights is the
clamped stack (`hagree`): except on a sample event of McDiarmid-small probability, the executed true
risk is at most the executed empirical risk plus the closed capacity budget
`2·(12√2·(1/√m)·B_int) + ε` and the rounding correction `2·Lℓ·envBound`. The capacity constant
`lparamLipBound` grows with depth `L` — the full transformer's depth-graded soft capacity. The input
cap (clamp to the layer-norm activation ball of radius `√d·Cγ + Cβ`) is the hypothesis self-attention's
lack of a global Lipschitz constant forces; the feed-forward block, being globally Lipschitz, needs
none. -/
theorem transformerEncoderStack_certified_generalization {s d hdim p m : ℕ} [NeZero s]
    [Nonempty (Fin p)] [MeasurableSpace (Fin s → Fin d → ℝ)] [BorelSpace (Fin s → Fin d → ℝ)]
    {P : Measure (Fin s → Fin d → ℝ)} [IsProbabilityMeasure P]
    (hm : 0 < m) {R scale Cγ Cβ Lγ Lβ bW1 bW2 : ℝ} (hR : 0 ≤ R) (hscale : 0 < scale) (hd : 0 < d)
    (hCγ0 : 0 ≤ Cγ) (hCβ0 : 0 ≤ Cβ) (hLγ0 : 0 ≤ Lγ) (hLβ0 : 0 ≤ Lβ) (hbW1 : 0 ≤ bW1) (hbW2 : 0 ≤ bW2)
    (W1 : Fin d → Fin hdim → ℝ) (b1 : Fin hdim → ℝ) (W2 : Fin hdim → Fin d → ℝ) (b2 : Fin d → ℝ)
    (hW1c : ∀ l, (∑ k, |W1 k l|) ≤ bW1) (hW2c : ∀ j, (∑ l, |W2 l j|) ≤ bW2)
    (γ1 β1 γ2 β2 : ParamSpace p → (Fin d → ℝ))
    (hγ1cont : Continuous γ1) (hβ1cont : Continuous β1)
    (hγ2cont : Continuous γ2) (hβ2cont : Continuous β2)
    (hγ1B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ1 θ j| ≤ Cγ)
    (hβ1B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β1 θ j| ≤ Cβ)
    (hγ2B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ2 θ j| ≤ Cγ)
    (hβ2B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β2 θ j| ≤ Cβ)
    (hγ1Lip : ∀ θ θ', dist (γ1 θ) (γ1 θ') ≤ Lγ * dist θ θ')
    (hβ1Lip : ∀ θ θ', dist (β1 θ) (β1 θ') ≤ Lβ * dist θ θ')
    (hγ2Lip : ∀ θ θ', dist (γ2 θ) (γ2 θ') ≤ Lγ * dist θ θ')
    (hβ2Lip : ∀ θ θ', dist (β2 θ) (β2 θ') ≤ Lβ * dist θ θ')
    (ℓ : (Fin s → Fin d → ℝ) → ℝ) {b : ℝ} (hb : 0 < b) (hℓb : ∀ v, |ℓ v| ≤ b)
    (hℓcont : Continuous ℓ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ)
    (hℓLip : ∀ u v, |ℓ u - ℓ v| ≤ Lℓ * dist u v)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R) (L : ℕ)
    (Ls : List (ExecLayer (Fin s → Fin d → ℝ)))
    (hagree : ∀ x, idealComp Ls x
        = lparamComp (List.flatten (List.replicate L
            [normAttnBlock (n := s) hscale hCγ0 hCβ0 hLγ0 hLβ0 γ1 β1,
             normFFNBlock (s := s) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2]))
            (embedBase Capacity.Dyadic w_T.1) (clampCoord (Real.sqrt d * Cγ + Cβ) x))
    (hintG : Integrable (fun x => ℓ (execComp Ls x)) P)
    (hLpos : 0 < Lℓ * lparamLipBound (List.flatten (List.replicate L
        [normAttnBlock (n := s) hscale hCγ0 hCβ0 hLγ0 hLβ0 γ1 β1,
         normFFNBlock (s := s) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2]))) :
    (Measure.pi fun _ : Fin m => P).real
        {S | ¬ ((∫ x, ℓ (execComp Ls x) ∂P)
              ≤ (1 / (m : ℝ)) * ∑ i, ℓ (execComp Ls (S i))
                + (2 * ((12 * Real.sqrt 2) * (1 / Real.sqrt m)
                    * (∫⁻ ε in Set.Ioc (0 : ℝ) (2 * b),
                        ENNReal.ofReal (Real.sqrt (Real.log 2)
                          + Real.sqrt ((p : ℝ) * (4 * R * (Lℓ * lparamLipBound (List.flatten
                              (List.replicate L
                                [normAttnBlock (n := s) hscale hCγ0 hCβ0 hLγ0 hLβ0 γ1 β1,
                                 normFFNBlock (s := s) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2])))))
                            * ε ^ (-(1 / 2) : ℝ))).toReal) + ε)
                + 2 * (Lℓ * envBound Ls))}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) := by
  set aBlk := normAttnBlock (n := s) hscale hCγ0 hCβ0 hLγ0 hLβ0 γ1 β1 with haBlk
  set fBlk := normFFNBlock (s := s) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2 with hfBlk
  set St := List.flatten (List.replicate L [aBlk, fBlk]) with hSt
  set ρ := Real.sqrt d * Cγ + Cβ with hρ
  have hρ0 : (0 : ℝ) ≤ ρ := add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCγ0) hCβ0
  have hmem : ∀ Lb ∈ St, Lb = aBlk ∨ Lb = fBlk := by
    intro Lb hLb
    rcases List.mem_flatten.mp hLb with ⟨t, ht, hLbt⟩
    rw [List.eq_of_mem_replicate ht] at hLbt
    simpa using hLbt
  set F : ParamSpace p → (Fin s → Fin d → ℝ) → ℝ :=
    fun θ x => ℓ (lparamComp St θ (clampCoord ρ x)) with hF
  have hblkcont : ∀ Lb ∈ St,
      Continuous (fun pq : ParamSpace p × (Fin s → Fin d → ℝ) => Lb.map pq.1 pq.2) := by
    intro Lb hLb
    rcases hmem Lb hLb with h | h
    · rw [h, haBlk]; exact continuous_normAttnBlock_weight hγ1cont hβ1cont
    · rw [h, hfBlk]; exact continuous_normFFNBlock_weight W1 b1 W2 b2 hγ2cont hβ2cont
  have hstackcont : Continuous (fun pq : ParamSpace p × (Fin s → Fin d → ℝ) =>
      lparamComp St pq.1 pq.2) := continuous_lparamComp_uncurry _ hblkcont
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
  have hlip : ∀ S : Fin m → (Fin s → Fin d → ℝ),
      ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      dist (valueVec F S θ) (valueVec F S θ') ≤ Lℓ * lparamLipBound St * dist θ θ' := by
    intro S θ hθ θ' hθ'
    refine (dist_pi_le_iff (mul_nonneg hLpos.le dist_nonneg)).mpr (fun j => ?_)
    rw [Real.dist_eq]
    simp only [valueVec, hF]
    have hclampmem : clampCoord ρ (S j) ∈ Metric.closedBall (0 : Fin s → Fin d → ℝ) ρ := by
      rw [mem_closedBall_zero_iff]; exact clampCoord_norm_le hρ0 (S j)
    calc |ℓ (lparamComp St θ (clampCoord ρ (S j))) - ℓ (lparamComp St θ' (clampCoord ρ (S j)))|
        ≤ Lℓ * dist (lparamComp St θ (clampCoord ρ (S j)))
              (lparamComp St θ' (clampCoord ρ (S j))) := hℓLip _ _
      _ ≤ Lℓ * (lparamLipBound St * dist θ θ') :=
          mul_le_mul_of_nonneg_left
            (transformerEncoderStack_weight_lip hd hscale hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2
              W1 b1 W2 b2 hW1c hW2c γ1 β1 γ2 β2 hγ1B hβ1B hγ2B hβ2B hγ1Lip hβ1Lip hγ2Lip hβ2Lip L
              hθ hθ' hclampmem) hLℓ0
      _ = Lℓ * lparamLipBound St * dist θ θ' := by ring
  exact certified_executed_generalization_dudley hm hR F hb hFb hFmeas hFcont hε w_T Ls ℓ hLℓ0
    hℓLip hbridge hintF hintG hLpos hlip

end TLT
