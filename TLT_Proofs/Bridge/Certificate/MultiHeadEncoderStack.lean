/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Lipschitz.MultiHeadAttnCertificate
import TLT_Proofs.Bridge.Certificate.TransformerStackCertificate

/-!
# The full true-multi-head transformer encoder stack

`MultiHeadAttnCertificate` gave the certified bound for a depth-`L` stack of pure true-multi-head
attention blocks. The full transformer encoder layer is the multi-head attention block followed by the
post-norm feed-forward residual block. Both block types are already `ParamLayerLocal`s, so they compose
into one stack by the same mechanism as `TransformerStackCertificate` for single-head attention:

* `transformerEncoderStackMH_weight_lip`: a depth-`L` stack of `[multiHeadBlock, ffnBlock]` layers is
  `lparamLipBound`-Lipschitz in the weights on the activation ball.
* `transformerEncoderStackMH_certified_generalization`: its certified generalization bound.

Both are stated in the weight-tied (universal-transformer) regime over `List.replicate`; the untied
standard-transformer variant is the same machinery over `List.ofFn` of `L` distinct blocks reading
disjoint parameter coordinates (`transformerEncoderStackMH_untied_*` below).
-/

/-!
## References
- [31] per-head bounded-domain boundary (true multi-head WQ/WK/WVO); [32][33] norm-based attention
  capacity / seq-length-free linear-H; [41] weight-tied; [16][54][26] Dudley/covering; LayerNorm.
-/

open MeasureTheory

noncomputable section

namespace TLT

open Capacity

variable {n d hdim : ℕ}

/-- **Weight-Lipschitz of the depth-`L` true-multi-head transformer encoder stack.** Each encoder layer
is the post-norm multi-head attention block followed by the post-norm feed-forward residual block
(`[multiHeadBlock, ffnBlock]`, flattened over `L` copies). The stack is `lparamLipBound`-Lipschitz in
its weights on the activation ball; the per-block obligations are dispatched by block type, the
multi-head block through `normMultiHeadBlock_*` and the feed-forward block through
`normResidualBlock_*` (exactly as the single-head stack). -/
theorem transformerEncoderStackMH_weight_lip {H p : ℕ} [NeZero n] (hd : 0 < d)
    {scale R B bV βY γW Cγ Cβ Lγ Lβ LWQ LWK LWVO bW1 bW2 : ℝ} (hscale : 0 < scale) (hB : 0 ≤ B)
    (hbV0 : 0 ≤ bV) (hβY0 : 0 ≤ βY) (hγW0 : 0 ≤ γW) (hCγ0 : 0 ≤ Cγ) (hCβ0 : 0 ≤ Cβ) (hLγ0 : 0 ≤ Lγ)
    (hLβ0 : 0 ≤ Lβ) (hLWQ0 : 0 ≤ LWQ) (hLWK0 : 0 ≤ LWK) (hLWVO0 : 0 ≤ LWVO) (hbW1 : 0 ≤ bW1)
    (hbW2 : 0 ≤ bW2) (WQ WK WVO : ParamSpace p → (Fin H → Fin d → Fin d → ℝ))
    (W1 : Fin d → Fin hdim → ℝ) (b1 : Fin hdim → ℝ) (W2 : Fin hdim → Fin d → ℝ) (b2 : Fin d → ℝ)
    (hW1c : ∀ l, (∑ k, |W1 k l|) ≤ bW1) (hW2c : ∀ j, (∑ l, |W2 l j|) ≤ bW2)
    (γ1 β1 γ2 β2 : ParamSpace p → (Fin d → ℝ))
    (hγ1B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ1 θ j| ≤ Cγ)
    (hβ1B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β1 θ j| ≤ Cβ)
    (hγ2B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ2 θ j| ≤ Cγ)
    (hβ2B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β2 θ j| ≤ Cβ)
    (hβYD : ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ i, (∑ a, |y i a|) ≤ βY)
    (hQB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h i e, |matMulCoord (WQ θ h) y i e| ≤ B)
    (hKB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h k' e, |matMulCoord (WK θ h) y k' e| ≤ B)
    (hVB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h j, ‖matMulCoord (WVO θ h) y j‖ ≤ bV)
    (hγWQ : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WQ θ h k j|) ≤ γW)
    (hγWK : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WK θ h k j|) ≤ γW)
    (hγWVO : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WVO θ h k j|) ≤ γW)
    (hγ1Lip : ∀ θ θ', dist (γ1 θ) (γ1 θ') ≤ Lγ * dist θ θ')
    (hβ1Lip : ∀ θ θ', dist (β1 θ) (β1 θ') ≤ Lβ * dist θ θ')
    (hWQLip : ∀ θ θ', dist (WQ θ) (WQ θ') ≤ LWQ * dist θ θ')
    (hWKLip : ∀ θ θ', dist (WK θ) (WK θ') ≤ LWK * dist θ θ')
    (hWVOLip : ∀ θ θ', dist (WVO θ) (WVO θ') ≤ LWVO * dist θ θ')
    (hγ2Lip : ∀ θ θ', dist (γ2 θ) (γ2 θ') ≤ Lγ * dist θ θ')
    (hβ2Lip : ∀ θ θ', dist (β2 θ) (β2 θ') ≤ Lβ * dist θ θ') (L : ℕ)
    {θ θ' : ParamSpace p} (hθ : θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))))
    (hθ' : θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))))
    {x : Fin n → Fin d → ℝ} (hx : x ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ)) :
    dist (lparamComp (List.flatten (List.replicate L
            [normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0
                WQ WK WVO γ1 β1,
             normFFNBlock (s := n) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2])) θ x)
         (lparamComp (List.flatten (List.replicate L
            [normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0
                WQ WK WVO γ1 β1,
             normFFNBlock (s := n) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2])) θ' x)
      ≤ lparamLipBound (List.flatten (List.replicate L
            [normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0
                WQ WK WVO γ1 β1,
             normFFNBlock (s := n) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2])) * dist θ θ' := by
  set aBlk := normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0
    WQ WK WVO γ1 β1 with haBlk
  set fBlk := normFFNBlock (s := n) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2 with hfBlk
  have hρ0 : (0 : ℝ) ≤ Real.sqrt d * Cγ + Cβ := add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCγ0) hCβ0
  have hmem : ∀ Lb ∈ List.flatten (List.replicate L [aBlk, fBlk]), Lb = aBlk ∨ Lb = fBlk := by
    intro Lb hLb
    rcases List.mem_flatten.mp hLb with ⟨t, ht, hLbt⟩
    rw [List.eq_of_mem_replicate ht] at hLbt
    simpa using hLbt
  refine paramComp_param_lipschitz_on'
    (K := (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))))
    (D := Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ)) _ ?_ ?_ ?_ hθ hθ' hx
  · intro Lb hLb θ₀ hθ₀ a ha b hb
    rcases hmem Lb hLb with h | h
    · rw [h, haBlk]
      exact normMultiHeadBlock_input_lip hd hscale hB hbV0 hγW0 (WQ θ₀) (WK θ₀) (WVO θ₀)
        (hγWQ θ₀ hθ₀) (hγWK θ₀ hθ₀) (hγWVO θ₀ hθ₀) (γ1 θ₀) (β1 θ₀) (hγ1B θ₀ hθ₀) a b
        (hQB θ₀ hθ₀ b hb) (hKB θ₀ hθ₀ a ha) (hVB θ₀ hθ₀ a ha)
    · rw [h, hfBlk]
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hρ0] at ha hb
      exact normResidualBlock_input_lip hd (γ2 θ₀) (β2 θ₀) (hγ2B θ₀ hθ₀) (mul_nonneg hbW1 hbW2) a b
        (ffnCoord_input_lipschitz W1 b1 W2 b2 hbW1 hbW2 hW1c hW2c a b)
  · intro Lb hLb θ₀ hθ₀ θ₁ hθ₁ y hy
    rcases hmem Lb hLb with h | h
    · rw [h, haBlk]
      refine le_trans (normMultiHeadBlock_param_lip hd hscale hB hbV0 hβY0 (WQ θ₀) (WK θ₀) (WVO θ₀)
        (WQ θ₁) (WK θ₁) (WVO θ₁) (γ1 θ₀) (β1 θ₀) (γ1 θ₁) (β1 θ₁) (hγ1B θ₁ hθ₁) y (hβYD y hy)
        (hQB θ₁ hθ₁ y hy) (hKB θ₀ hθ₀ y hy) (hVB θ₀ hθ₀ y hy)) ?_
      rw [show (aBlk.paramLip) * dist θ₀ θ₁
          = (Real.sqrt d * (Lγ * dist θ₀ θ₁) + Lβ * dist θ₀ θ₁)
            + Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon
              * ((H : ℝ) * (2 * bV * ((d : ℝ) * B / scale)
                  * (βY * (LWQ * dist θ₀ θ₁) + βY * (LWK * dist θ₀ θ₁))
                + βY * (LWVO * dist θ₀ θ₁))) from by rw [haBlk]; simp only [normMultiHeadBlock]; ring]
      gcongr
      · exact hγ1Lip θ₀ θ₁
      · exact hβ1Lip θ₀ θ₁
      · exact hWQLip θ₀ θ₁
      · exact hWKLip θ₀ θ₁
      · exact hWVOLip θ₀ θ₁
    · rw [h, hfBlk]
      calc dist (normAttnCoord (γ2 θ₀) (β2 θ₀) (ffnCoord W1 b1 W2 b2) y)
                (normAttnCoord (γ2 θ₁) (β2 θ₁) (ffnCoord W1 b1 W2 b2) y)
          ≤ Real.sqrt d * dist (γ2 θ₀) (γ2 θ₁) + dist (β2 θ₀) (β2 θ₁) :=
            normResidualBlock_param_lip hd (γ2 θ₀) (β2 θ₀) (γ2 θ₁) (β2 θ₁) (ffnCoord W1 b1 W2 b2) y
        _ ≤ Real.sqrt d * (Lγ * dist θ₀ θ₁) + Lβ * dist θ₀ θ₁ :=
            add_le_add (mul_le_mul_of_nonneg_left (hγ2Lip θ₀ θ₁) (Real.sqrt_nonneg _)) (hβ2Lip θ₀ θ₁)
        _ = (Real.sqrt d * Lγ + Lβ) * dist θ₀ θ₁ := by ring
  · intro Lb hLb θ₀ hθ₀ y _
    rw [mem_closedBall_zero_iff]
    rcases hmem Lb hLb with h | h
    · rw [h, haBlk]
      exact normMultiHeadBlock_forward_inv hd (γ1 θ₀) (β1 θ₀) (hγ1B θ₀ hθ₀) (hβ1B θ₀ hθ₀) scale
        (WQ θ₀) (WK θ₀) (WVO θ₀) y
    · rw [h, hfBlk]
      exact normResidualBlock_forward_inv hd (γ2 θ₀) (β2 θ₀) (hγ2B θ₀ hθ₀) (hβ2B θ₀ hθ₀)
        (ffnCoord W1 b1 W2 b2) y

/-- **Certified generalization bound for the depth-`L` true-multi-head transformer encoder stack.**
For a depth-`L` stack of encoder layers (true-multi-head attention block ∘ post-norm feed-forward
residual block), presented as the executed layer list `Ls` whose ideal forward at the certified weights
is the clamped stack (`hagree`): except on a sample event of McDiarmid-small probability, the executed
true risk is at most the executed empirical risk plus the closed capacity budget
`2·(12√2·(1/√m)·B_int) + ε` and the rounding correction `2·Lℓ·envBound`. The capacity is
sequence-length-free and grows with depth `L` and head count `H`; this removes the
"no interleaved feed-forward" residual, in the weight-tied (universal-transformer) regime. -/
theorem transformerEncoderStackMH_certified_generalization {H p m : ℕ} [NeZero n] [Nonempty (Fin p)]
    [MeasurableSpace (Fin n → Fin d → ℝ)] [BorelSpace (Fin n → Fin d → ℝ)]
    {P : Measure (Fin n → Fin d → ℝ)} [IsProbabilityMeasure P] (hm : 0 < m)
    {R B bV βY γW scale Cγ Cβ Lγ Lβ LWQ LWK LWVO bW1 bW2 : ℝ} (hR : 0 ≤ R) (hscale : 0 < scale)
    (hd : 0 < d) (hB : 0 ≤ B) (hbV0 : 0 ≤ bV) (hβY0 : 0 ≤ βY) (hγW0 : 0 ≤ γW) (hCγ0 : 0 ≤ Cγ)
    (hCβ0 : 0 ≤ Cβ) (hLγ0 : 0 ≤ Lγ) (hLβ0 : 0 ≤ Lβ) (hLWQ0 : 0 ≤ LWQ) (hLWK0 : 0 ≤ LWK)
    (hLWVO0 : 0 ≤ LWVO) (hbW1 : 0 ≤ bW1) (hbW2 : 0 ≤ bW2)
    (WQ WK WVO : ParamSpace p → (Fin H → Fin d → Fin d → ℝ))
    (W1 : Fin d → Fin hdim → ℝ) (b1 : Fin hdim → ℝ) (W2 : Fin hdim → Fin d → ℝ) (b2 : Fin d → ℝ)
    (hW1c : ∀ l, (∑ k, |W1 k l|) ≤ bW1) (hW2c : ∀ j, (∑ l, |W2 l j|) ≤ bW2)
    (γ1 β1 γ2 β2 : ParamSpace p → (Fin d → ℝ))
    (hWQcont : Continuous WQ) (hWKcont : Continuous WK) (hWVOcont : Continuous WVO)
    (hγ1cont : Continuous γ1) (hβ1cont : Continuous β1) (hγ2cont : Continuous γ2) (hβ2cont : Continuous β2)
    (hγ1B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ1 θ j| ≤ Cγ)
    (hβ1B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β1 θ j| ≤ Cβ)
    (hγ2B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ2 θ j| ≤ Cγ)
    (hβ2B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β2 θ j| ≤ Cβ)
    (hβYD : ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ i, (∑ a, |y i a|) ≤ βY)
    (hQB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h i e, |matMulCoord (WQ θ h) y i e| ≤ B)
    (hKB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h k' e, |matMulCoord (WK θ h) y k' e| ≤ B)
    (hVB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h j, ‖matMulCoord (WVO θ h) y j‖ ≤ bV)
    (hγWQ : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WQ θ h k j|) ≤ γW)
    (hγWK : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WK θ h k j|) ≤ γW)
    (hγWVO : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WVO θ h k j|) ≤ γW)
    (hγ1Lip : ∀ θ θ', dist (γ1 θ) (γ1 θ') ≤ Lγ * dist θ θ')
    (hβ1Lip : ∀ θ θ', dist (β1 θ) (β1 θ') ≤ Lβ * dist θ θ')
    (hWQLip : ∀ θ θ', dist (WQ θ) (WQ θ') ≤ LWQ * dist θ θ')
    (hWKLip : ∀ θ θ', dist (WK θ) (WK θ') ≤ LWK * dist θ θ')
    (hWVOLip : ∀ θ θ', dist (WVO θ) (WVO θ') ≤ LWVO * dist θ θ')
    (hγ2Lip : ∀ θ θ', dist (γ2 θ) (γ2 θ') ≤ Lγ * dist θ θ')
    (hβ2Lip : ∀ θ θ', dist (β2 θ) (β2 θ') ≤ Lβ * dist θ θ')
    (ℓ : (Fin n → Fin d → ℝ) → ℝ) {b : ℝ} (hb : 0 < b) (hℓb : ∀ v, |ℓ v| ≤ b)
    (hℓcont : Continuous ℓ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ) (hℓLip : ∀ u v, |ℓ u - ℓ v| ≤ Lℓ * dist u v)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R) (L : ℕ)
    (Ls : List (ExecLayer (Fin n → Fin d → ℝ)))
    (hagree : ∀ x, idealComp Ls x
        = lparamComp (List.flatten (List.replicate L
            [normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0
                WQ WK WVO γ1 β1,
             normFFNBlock (s := n) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2]))
            (embedBase Capacity.Dyadic w_T.1) (clampCoord (Real.sqrt d * Cγ + Cβ) x))
    (hintG : Integrable (fun x => ℓ (execComp Ls x)) P)
    (hLpos : 0 < Lℓ * lparamLipBound (List.flatten (List.replicate L
        [normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0
            WQ WK WVO γ1 β1,
         normFFNBlock (s := n) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2]))) :
    (Measure.pi fun _ : Fin m => P).real
        {S | ¬ ((∫ x, ℓ (execComp Ls x) ∂P)
              ≤ (1 / (m : ℝ)) * ∑ i, ℓ (execComp Ls (S i))
                + (2 * ((12 * Real.sqrt 2) * (1 / Real.sqrt m)
                    * (∫⁻ ε in Set.Ioc (0 : ℝ) (2 * b),
                        ENNReal.ofReal (Real.sqrt (Real.log 2)
                          + Real.sqrt ((p : ℝ) * (4 * R * (Lℓ * lparamLipBound (List.flatten
                              (List.replicate L
                                [normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0
                                    hLWQ0 hLWK0 hLWVO0 WQ WK WVO γ1 β1,
                                 normFFNBlock (s := n) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2])))))
                            * ε ^ (-(1 / 2) : ℝ))).toReal) + ε)
                + 2 * (Lℓ * envBound Ls))}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) := by
  set aBlk := normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0
    WQ WK WVO γ1 β1 with haBlk
  set fBlk := normFFNBlock (s := n) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2 with hfBlk
  set St := List.flatten (List.replicate L [aBlk, fBlk]) with hSt
  set ρ := Real.sqrt d * Cγ + Cβ with hρ
  have hρ0 : (0 : ℝ) ≤ ρ := add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCγ0) hCβ0
  have hmem : ∀ Lb ∈ St, Lb = aBlk ∨ Lb = fBlk := by
    intro Lb hLb
    rcases List.mem_flatten.mp hLb with ⟨t, ht, hLbt⟩
    rw [List.eq_of_mem_replicate ht] at hLbt
    simpa using hLbt
  set F : ParamSpace p → (Fin n → Fin d → ℝ) → ℝ :=
    fun θ x => ℓ (lparamComp St θ (clampCoord ρ x)) with hF
  have hblkcont : ∀ Lb ∈ St,
      Continuous (fun pq : ParamSpace p × (Fin n → Fin d → ℝ) => Lb.map pq.1 pq.2) := by
    intro Lb hLb
    rcases hmem Lb hLb with h | h
    · rw [h, haBlk]; exact continuous_normMultiHeadBlock_weight hWQcont hWKcont hWVOcont hγ1cont hβ1cont
    · rw [h, hfBlk]; exact continuous_normFFNBlock_weight W1 b1 W2 b2 hγ2cont hβ2cont
  have hstackcont : Continuous (fun pq : ParamSpace p × (Fin n → Fin d → ℝ) =>
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
  have hlip : ∀ S : Fin m → (Fin n → Fin d → ℝ),
      ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      dist (valueVec F S θ) (valueVec F S θ') ≤ Lℓ * lparamLipBound St * dist θ θ' := by
    intro S θ hθ θ' hθ'
    refine (dist_pi_le_iff (mul_nonneg hLpos.le dist_nonneg)).mpr (fun j => ?_)
    rw [Real.dist_eq]; simp only [valueVec, hF]
    have hclampmem : clampCoord ρ (S j) ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) ρ := by
      rw [mem_closedBall_zero_iff]; exact clampCoord_norm_le hρ0 (S j)
    calc |ℓ (lparamComp St θ (clampCoord ρ (S j))) - ℓ (lparamComp St θ' (clampCoord ρ (S j)))|
        ≤ Lℓ * dist (lparamComp St θ (clampCoord ρ (S j)))
              (lparamComp St θ' (clampCoord ρ (S j))) := hℓLip _ _
      _ ≤ Lℓ * (lparamLipBound St * dist θ θ') :=
          mul_le_mul_of_nonneg_left
            (transformerEncoderStackMH_weight_lip hd hscale hB hbV0 hβY0 hγW0 hCγ0 hCβ0 hLγ0 hLβ0
              hLWQ0 hLWK0 hLWVO0 hbW1 hbW2 WQ WK WVO W1 b1 W2 b2 hW1c hW2c γ1 β1 γ2 β2 hγ1B hβ1B hγ2B
              hβ2B hβYD hQB hKB hVB hγWQ hγWK hγWVO hγ1Lip hβ1Lip hWQLip hWKLip hWVOLip hγ2Lip hβ2Lip L
              hθ hθ' hclampmem) hLℓ0
      _ = Lℓ * lparamLipBound St * dist θ θ' := by ring
  exact certified_executed_generalization_dudley hm hR F hb hFb hFmeas hFcont hε w_T Ls ℓ hLℓ0
    hℓLip hbridge hintF hintG hLpos hlip

end TLT
