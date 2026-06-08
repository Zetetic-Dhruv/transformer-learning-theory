/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Lipschitz.SoftmaxJacobian

/-!
# Lipschitz bounds for the attention output

The single-query attention output is the softmax-weighted combination of value vectors
`attnOut s V c = ∑ⱼ softmax(s)ⱼ · V j c`, where `s` are the key scores and `V` the value matrix. Two
Lipschitz estimates — one in the scores, one in the values — are the mathematical core of the
attention layer's weight-Lipschitz constant: the scores are bilinear in the query/key weights and the
values are linear in the value weights, so composing these with the linear layers yields the attention
layer's `ParamLayer` constant.

* In the **values**, the output is `1`-Lipschitz: it is a convex combination (`softmax` sums to one),
  so perturbing `V` moves the output by at most the perturbation.
* In the **scores**, the output is Lipschitz with constant `2·nK·(bound on V)`: this is where the
  softmax Lipschitz constant enters (`softmax_lipschitz`), and the constant is *absolute* in the score
  scale — the point established in `Softmax.lean`.

## References

A. Vaswani et al., *Attention Is All You Need*, NeurIPS 2017; H. Kim, G. Papamakarios and A. Mnih,
*The Lipschitz Constant of Self-Attention*, ICML 2021.
-/

open Real

namespace TLT

variable {nK d : ℕ}

/-- The single-query attention output: the softmax-weighted sum of the value vectors. -/
noncomputable def attnOut (s : Fin nK → ℝ) (V : Fin nK → Fin d → ℝ) (c : Fin d) : ℝ :=
  ∑ j, softmax s j * V j c

/-- **Attention is `1`-Lipschitz in the values** (per output coordinate): the output is a convex
combination of the values, so it moves by at most the perturbation of the values. -/
theorem attnOut_values_bound [NeZero nK] (s : Fin nK → ℝ) (V V' : Fin nK → Fin d → ℝ) (c : Fin d)
    {bd : ℝ} (hbd : ∀ j, |V j c - V' j c| ≤ bd) :
    |attnOut s V c - attnOut s V' c| ≤ bd := by
  have h : attnOut s V c - attnOut s V' c = ∑ j, softmax s j * (V j c - V' j c) := by
    unfold attnOut; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [h]
  calc |∑ j, softmax s j * (V j c - V' j c)|
      ≤ ∑ j, |softmax s j * (V j c - V' j c)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, softmax s j * |V j c - V' j c| := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (softmax_nonneg s j)]
    _ ≤ ∑ j, softmax s j * bd :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hbd j) (softmax_nonneg s j)
    _ = bd := by rw [← Finset.sum_mul, softmax_sum_one s, one_mul]

/-- **Attention is Lipschitz in the scores** with the *absolute* constant `2·bV` (per output
coordinate, `bV` bounding the value entries) — **independent of the number of keys**. The score map
`z ↦ attnOut z V c = ∑ⱼ softmax(z)ⱼ Vⱼc` is the fixed linear readout `L ∘ softmax` with
`L w = ∑ⱼ Vⱼc wⱼ`, so its score-gradient is the composition `L ∘ softmaxJac z`. The naïve product
`‖L‖·‖softmaxJac z‖` would carry `∑ⱼ|Vⱼc| ≤ nK·bV`; but the composed operator has norm `≤ 2·bV`,
because the softmax Jacobian centres by `⟨p,v⟩` (the probability-simplex constraint `∑ⱼ pⱼ = 1`):
`∑ⱼ pⱼ|vⱼ − ⟨p,v⟩| ≤ 2‖v‖`, an `O(1)` quantity. The mean-value inequality on the bounded score
segment then closes it. The constant being absolute in both the score scale (Kim et al.) and the key
count is what keeps the downstream capacity polynomial in the weights and free of the sequence length. -/
theorem attnOut_scores_bound [NeZero nK] (s s' : Fin nK → ℝ) (V : Fin nK → Fin d → ℝ) (c : Fin d)
    {bV : ℝ} (hbV0 : 0 ≤ bV) (hbV : ∀ j, |V j c| ≤ bV) :
    |attnOut s V c - attnOut s' V c| ≤ 2 * bV * ‖s - s'‖ := by
  set L : (Fin nK → ℝ) →L[ℝ] ℝ := ∑ j, (V j c) • ContinuousLinearMap.proj j with hL
  have hLapp : ∀ w : Fin nK → ℝ, L w = ∑ j, V j c * w j := fun w => by
    simp only [hL, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hfun : ∀ z, attnOut z V c = L (softmax z) := fun z => by
    rw [attnOut, hLapp]; exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hderiv : ∀ z, HasFDerivAt (fun z => L (softmax z)) (L.comp (softmaxJac z)) z :=
    fun z => (L.hasFDerivAt).comp z (softmax_hasFDerivAt z)
  have hbound : ∀ z, ‖L.comp (softmaxJac z)‖ ≤ 2 * bV := fun z => by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    rw [ContinuousLinearMap.comp_apply, hLapp, Real.norm_eq_abs]
    have hinner : |∑ k, softmax z k * v k| ≤ ‖v‖ := by
      calc |∑ k, softmax z k * v k| ≤ ∑ k, |softmax z k * v k| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k, softmax z k * |v k| := Finset.sum_congr rfl (fun k _ => by
            rw [abs_mul, abs_of_nonneg (softmax_nonneg z k)])
        _ ≤ ∑ k, softmax z k * ‖v‖ := Finset.sum_le_sum (fun k _ =>
            mul_le_mul_of_nonneg_left (norm_le_pi_norm v k) (softmax_nonneg z k))
        _ = ‖v‖ := by rw [← Finset.sum_mul, softmax_sum_one z, one_mul]
    have habs : ∀ j, |v j - ∑ k, softmax z k * v k| ≤ ‖v‖ + ‖v‖ := fun j => by
      have h1 : |v j - ∑ k, softmax z k * v k| ≤ |v j| + |∑ k, softmax z k * v k| := by
        rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
      have hvj : |v j| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v j
      linarith [h1, hvj, hinner]
    calc |∑ j, V j c * softmaxJac z v j|
        ≤ ∑ j, |V j c * softmaxJac z v j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |V j c| * (softmax z j * |v j - ∑ k, softmax z k * v k|) :=
          Finset.sum_congr rfl (fun j _ => by
            rw [softmaxJac_apply, abs_mul, abs_mul, abs_of_nonneg (softmax_nonneg z j)])
      _ ≤ ∑ j, bV * (softmax z j * (‖v‖ + ‖v‖)) := Finset.sum_le_sum (fun j _ =>
          mul_le_mul (hbV j) (mul_le_mul_of_nonneg_left (habs j) (softmax_nonneg z j))
            (mul_nonneg (softmax_nonneg z j) (abs_nonneg _)) hbV0)
      _ = ∑ j, bV * (‖v‖ + ‖v‖) * softmax z j := Finset.sum_congr rfl (fun j _ => by ring)
      _ = bV * (‖v‖ + ‖v‖) * ∑ j, softmax z j := (Finset.mul_sum _ _ _).symm
      _ = 2 * bV * ‖v‖ := by rw [softmax_sum_one z]; ring
  rw [show |attnOut s V c - attnOut s' V c| = ‖(fun z => L (softmax z)) s - (fun z => L (softmax z)) s'‖
      from by rw [hfun s, hfun s', Real.norm_eq_abs]]
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hderiv z).hasFDerivWithinAt) (fun z _ => hbound z) convex_univ
    (Set.mem_univ s') (Set.mem_univ s)

/-- The single-query attention scores `s[k'] = ⟨Q, K_{k'}⟩ / scale` — bilinear in the query/key. -/
noncomputable def attnScores (scale : ℝ) (Q : Fin d → ℝ) (K : Fin nK → Fin d → ℝ) :
    Fin nK → ℝ := fun k' => (∑ e, Q e * K k' e) / scale

/-- **The scores are Lipschitz only on a bounded domain.** With query/key entries bounded by `B`, the
bilinear score map is `dB/scale`-Lipschitz in `(Q,K)`. The constant is finite *only* because of the
`B`-cap — the bilinear form has no global Lipschitz constant (Kim et al.), and the `B` is exactly the
input cap `K = {‖x‖ ≤ B}` the certified bound already carries. -/
theorem attnScores_dist_le {scale B : ℝ} (hscale : 0 < scale) (hB : 0 ≤ B)
    (Q Q' : Fin d → ℝ) (K K' : Fin nK → Fin d → ℝ)
    (hQ' : ∀ e, |Q' e| ≤ B) (hK : ∀ k' e, |K k' e| ≤ B) :
    ‖attnScores scale Q K - attnScores scale Q' K'‖
      ≤ (d * B / scale) * (‖Q - Q'‖ + ‖K - K'‖) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun k' => ?_)
  rw [Real.norm_eq_abs, Pi.sub_apply]
  have hQe : ∀ e, |Q e - Q' e| ≤ ‖Q - Q'‖ := fun e => by
    rw [show Q e - Q' e = (Q - Q') e from rfl, ← Real.norm_eq_abs]; exact norm_le_pi_norm _ e
  have hKe : ∀ e, |K k' e - K' k' e| ≤ ‖K - K'‖ := fun e => by
    rw [show K k' e - K' k' e = (K - K') k' e from rfl, ← Real.norm_eq_abs]
    exact le_trans (norm_le_pi_norm _ e) (norm_le_pi_norm _ k')
  rw [attnScores, attnScores, ← sub_div, abs_div, abs_of_pos hscale, div_le_iff₀ hscale]
  calc |∑ e, Q e * K k' e - ∑ e, Q' e * K' k' e|
      = |∑ e, (Q e * K k' e - Q' e * K' k' e)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ e, |Q e * K k' e - Q' e * K' k' e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e, (‖Q - Q'‖ * B + B * ‖K - K'‖) := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        calc |Q e * K k' e - Q' e * K' k' e|
            = |(Q e - Q' e) * K k' e + Q' e * (K k' e - K' k' e)| := by ring_nf
          _ ≤ |(Q e - Q' e) * K k' e| + |Q' e * (K k' e - K' k' e)| := abs_add_le _ _
          _ = |Q e - Q' e| * |K k' e| + |Q' e| * |K k' e - K' k' e| := by rw [abs_mul, abs_mul]
          _ ≤ ‖Q - Q'‖ * B + B * ‖K - K'‖ :=
              add_le_add (mul_le_mul (hQe e) (hK k' e) (abs_nonneg _) (norm_nonneg _))
                (mul_le_mul (hQ' e) (hKe e) (abs_nonneg _) hB)
    _ = (d * B / scale) * (‖Q - Q'‖ + ‖K - K'‖) * scale := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- **Attention is Lipschitz on the bounded domain `K = {‖·‖ ≤ B}`.** Composing the conditional
bilinear-score bound (the only non-global part) with the *global* softmax-mixing bounds
(`attnOut_scores_bound`, `attnOut_values_bound`): with query/key entries `≤ B` and value entries `≤ bV`,
the attention output moves by at most `2·nK·bV·(dB/scale)·(‖ΔQ‖+‖ΔK‖) + ‖ΔV‖`. The `B`-cap is the Kim
et al. boundary, made into a constructive constant. -/
theorem attnOut_lipschitz_on_ball [NeZero nK] {scale B bV : ℝ} (hscale : 0 < scale) (hB : 0 ≤ B)
    (hbV0 : 0 ≤ bV) (Q Q' : Fin d → ℝ) (K K' : Fin nK → Fin d → ℝ) (V V' : Fin nK → Fin d → ℝ)
    (c : Fin d) (hQ' : ∀ e, |Q' e| ≤ B) (hK : ∀ k' e, |K k' e| ≤ B) (hV : ∀ j, |V j c| ≤ bV) :
    |attnOut (attnScores scale Q K) V c - attnOut (attnScores scale Q' K') V' c|
      ≤ 2 * bV * (d * B / scale) * (‖Q - Q'‖ + ‖K - K'‖) + ‖V - V'‖ := by
  have hVterm : |attnOut (attnScores scale Q' K') V c - attnOut (attnScores scale Q' K') V' c|
      ≤ ‖V - V'‖ :=
    attnOut_values_bound _ V V' c (fun j => by
      have h1 : |V j c - V' j c| ≤ ‖(V - V') j‖ := by
        rw [show V j c - V' j c = (V - V') j c from rfl, ← Real.norm_eq_abs]
        exact norm_le_pi_norm _ c
      exact le_trans h1 (norm_le_pi_norm _ j))
  calc |attnOut (attnScores scale Q K) V c - attnOut (attnScores scale Q' K') V' c|
      ≤ |attnOut (attnScores scale Q K) V c - attnOut (attnScores scale Q' K') V c|
        + |attnOut (attnScores scale Q' K') V c - attnOut (attnScores scale Q' K') V' c| :=
        abs_sub_le _ _ _
    _ ≤ 2 * bV * ‖attnScores scale Q K - attnScores scale Q' K'‖ + ‖V - V'‖ :=
        add_le_add (attnOut_scores_bound _ _ V c hbV0 hV) hVterm
    _ ≤ 2 * bV * ((d * B / scale) * (‖Q - Q'‖ + ‖K - K'‖)) + ‖V - V'‖ := by
        gcongr
        exact attnScores_dist_le hscale hB Q Q' K K' hQ' hK
    _ = 2 * bV * (d * B / scale) * (‖Q - Q'‖ + ‖K - K'‖) + ‖V - V'‖ := by ring

/-- The single-query attention output as a vector over the output coordinates. -/
noncomputable def attnVec (s : Fin nK → ℝ) (V : Fin nK → Fin d → ℝ) : Fin d → ℝ :=
  fun c => attnOut s V c

/-- The attention output vector is the softmax-weighted sum of the value rows. -/
lemma attnVec_eq_sum_smul (s : Fin nK → ℝ) (V : Fin nK → Fin d → ℝ) :
    attnVec s V = ∑ j, softmax s j • V j := by
  funext c
  simp only [attnVec, attnOut, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- **Attention is forward-invariant on a norm ball.** The output is a convex combination of the value
rows — the softmax weights are nonnegative and sum to one — so if every value row has norm `≤ B`, so
does the attention output. This softmax-convexity is what makes attention a self-map of the ball, the
forward-invariance hypothesis of the bounded-activation `ExecLayer`. -/
lemma attnVec_norm_le [NeZero nK] (s : Fin nK → ℝ) (V : Fin nK → Fin d → ℝ) {B : ℝ}
    (hV : ∀ j, ‖V j‖ ≤ B) : ‖attnVec s V‖ ≤ B := by
  rw [attnVec_eq_sum_smul]
  calc ‖∑ j, softmax s j • V j‖
      ≤ ∑ j, ‖softmax s j • V j‖ := norm_sum_le _ _
    _ = ∑ j, softmax s j * ‖V j‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (softmax_nonneg s j)]
    _ ≤ ∑ j, softmax s j * B :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hV j) (softmax_nonneg s j)
    _ = B := by rw [← Finset.sum_mul, softmax_sum_one s, one_mul]

/-- **Attention is Lipschitz on the bounded domain, at the vector level.** The per-coordinate
`attnOut_lipschitz_on_ball` lifted to the output vector in the supremum norm: with query/key entries
`≤ B` and value rows of norm `≤ bV`, the attention output vector moves by at most
`2·nK·bV·(dB/scale)·(‖ΔQ‖+‖ΔK‖) + ‖ΔV‖`. This is the on-`D` Lipschitz estimate that the
bounded-activation `ExecLayer` constructor consumes. -/
lemma attnVec_lipschitz_on_ball [NeZero nK] {scale B bV : ℝ} (hscale : 0 < scale) (hB : 0 ≤ B)
    (hbV0 : 0 ≤ bV) (Q Q' : Fin d → ℝ) (K K' V V' : Fin nK → Fin d → ℝ)
    (hQ' : ∀ e, |Q' e| ≤ B) (hK : ∀ k' e, |K k' e| ≤ B) (hV : ∀ j, ‖V j‖ ≤ bV) :
    ‖attnVec (attnScores scale Q K) V - attnVec (attnScores scale Q' K') V'‖
      ≤ 2 * bV * (d * B / scale) * (‖Q - Q'‖ + ‖K - K'‖) + ‖V - V'‖ := by
  have hR0 : (0:ℝ) ≤ 2 * bV * (d * B / scale) * (‖Q - Q'‖ + ‖K - K'‖) + ‖V - V'‖ := by
    have h1 : (0:ℝ) ≤ 2 * bV * (d * B / scale) :=
      mul_nonneg (mul_nonneg (by norm_num) hbV0)
        (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) hscale.le)
    exact add_nonneg (mul_nonneg h1 (by positivity)) (norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg hR0).mpr (fun c => ?_)
  rw [Real.norm_eq_abs, Pi.sub_apply]
  simp only [attnVec]
  exact attnOut_lipschitz_on_ball hscale hB hbV0 Q Q' K K' V V' c hQ' hK
    (fun j => le_trans (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (V j) c) (hV j))

/-- **Attention is `1`-Lipschitz in the value matrix (vector level), with the scores held fixed.** A
convex combination of the value rows, so perturbing the values by `‖V − V'‖` moves the output by at
most that — globally (no domain cap needed; the domain dependence lives only in the scores). This is
the value-projection weight-Lipschitz atom: a learnable value projection enters attention only through
the value matrix. -/
lemma attnVec_values_lipschitz [NeZero nK] (s : Fin nK → ℝ) (V V' : Fin nK → Fin d → ℝ) :
    dist (attnVec s V) (attnVec s V') ≤ ‖V - V'‖ := by
  refine (dist_pi_le_iff (norm_nonneg _)).mpr (fun c => ?_)
  rw [Real.dist_eq]
  simp only [attnVec]
  exact attnOut_values_bound s V V' c (fun j => le_trans
    (by rw [show V j c - V' j c = (V - V') j c from rfl, ← Real.norm_eq_abs]; exact norm_le_pi_norm _ c)
    (norm_le_pi_norm _ j))

end TLT
