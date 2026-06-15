/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Certificate.CertifiedTransformerBound
import TLT_Proofs.Bridge.Forward.BoundedExecLayer
import TLT_Proofs.Bridge.Lipschitz.LinearLayerWeightLipschitz

/-!
# A certified computable generalization bound for an attention head

The concrete instantiation of `certified_executed_generalization_dudley` on a genuine attention model:
a single dot-product attention head with a **learnable value projection** `W`, evaluated on a
clamped input. The learnable weight is an *attention* weight (not merely a layer-norm affine), so the
capacity term genuinely measures the attention class; the Kim et al. boundary becomes a learning
bound.

The head is `attnHead scale W Y i = attnVec (scores Y) (Y · W)`: the softmax scores come from the
input `Y`, the value rows are the learned projection `Y · W`. Because the output is a convex
combination of the value rows, the head is `1`-Lipschitz in the value matrix, so its weight-Lipschitz
constant is the input row-`ℓ¹` bound (`attnHead_weight_lip`), finite because the input is clamped to
the certified region. Composed with the loss, this discharges the `hlip` hypothesis of the capstone.

## Main definitions

- `attnHead`: a dot-product attention head with a learnable value projection.

## Main results

- `attnHead_weight_lip`: the head is `β`-Lipschitz in the value-projection weights, `β` the input
  row-`ℓ¹` bound.
-/

/-!
## References
- [31] attention nonexpansive averaging / bounded-domain; [32] attention-class capacity; [16][54][26]
  Dudley/covering; [36] capacity template.
-/

open MeasureTheory

noncomputable section

namespace TLT

open Capacity

/-- A single dot-product attention head with a learnable value projection `W`: the softmax scores are
formed from the input `Y`, and the value rows are the projected `Y · W`. -/
noncomputable def attnHead {n d : ℕ} (scale : ℝ) (W : Fin d → Fin d → ℝ)
    (Y : Fin n → Fin d → ℝ) : Fin n → Fin d → ℝ :=
  fun i => attnVec (attnScores scale (Y i) Y) (matMulCoord W Y)

/-- **The attention head is Lipschitz in its value-projection weights.** With the input rows of `Y`
bounded in `ℓ¹` by `β`, the head moves by at most `β · dist W W'` when the value projection changes:
the scores are fixed (they do not depend on `W`), and the head is `1`-Lipschitz in the value matrix
(`attnVec_values_lipschitz`), which is `β`-Lipschitz in `W` (`matMulCoord_param_lipschitz`). -/
lemma attnHead_weight_lip {n d : ℕ} [NeZero n] {scale : ℝ} (Y : Fin n → Fin d → ℝ) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : ∀ i, (∑ k, |Y i k|) ≤ β) (W W' : Fin d → Fin d → ℝ) :
    dist (attnHead scale W Y) (attnHead scale W' Y) ≤ β * dist W W' := by
  refine (dist_pi_le_iff (mul_nonneg hβ0 dist_nonneg)).mpr (fun i => ?_)
  calc dist (attnHead scale W Y i) (attnHead scale W' Y i)
      ≤ ‖matMulCoord W Y - matMulCoord W' Y‖ := attnVec_values_lipschitz _ _ _
    _ = dist (matMulCoord W Y) (matMulCoord W' Y) := (dist_eq_norm _ _).symm
    _ ≤ β * dist W W' := matMulCoord_param_lipschitz Y hβ0 hβ W W'

/-! ### Continuity and boundedness of the attention head -/

/-- Softmax is continuous. -/
lemma continuous_softmax {n : ℕ} [NeZero n] : Continuous (softmax : (Fin n → ℝ) → Fin n → ℝ) :=
  continuous_pi (fun i => (Real.continuous_exp.comp (continuous_apply i)).div
    (continuous_finset_sum _ (fun j _ => Real.continuous_exp.comp (continuous_apply j)))
    (fun z => (sum_exp_pos z).ne'))

/-- The attention output `attnVec` is jointly continuous in the scores and the value matrix. -/
lemma continuous_attnVec_uncurry {n d : ℕ} [NeZero n] :
    Continuous (fun p : (Fin n → ℝ) × (Fin n → Fin d → ℝ) => attnVec p.1 p.2) := by
  refine continuous_pi (fun c => ?_)
  simp only [attnVec, attnOut]
  refine continuous_finset_sum _ (fun j _ => ?_)
  exact ((continuous_apply j).comp (continuous_softmax.comp continuous_fst)).mul
    ((continuous_apply_apply j c).comp continuous_snd)

/-- The single-query scores `Y ↦ attnScores scale (Y i) Y` are continuous in the input. -/
lemma continuous_attnScores_self {n d : ℕ} {scale : ℝ} (i : Fin n) :
    Continuous (fun Y : Fin n → Fin d → ℝ => attnScores scale (Y i) Y) := by
  refine continuous_pi (fun k' => ?_)
  simp only [attnScores]
  exact (continuous_finset_sum _ (fun e _ =>
    (continuous_apply_apply i e).mul (continuous_apply_apply k' e))).div_const scale

/-- The attention head is continuous in its input. -/
lemma continuous_attnHead_input {n d : ℕ} [NeZero n] {scale : ℝ} (W : Fin d → Fin d → ℝ) :
    Continuous (fun Y : Fin n → Fin d → ℝ => attnHead scale W Y) := by
  have hv : Continuous (fun Y : Fin n → Fin d → ℝ => matMulCoord W Y) := continuous_matMulCoord W
  refine continuous_pi (fun i => ?_)
  simp only [attnHead]
  exact continuous_attnVec_uncurry.comp ((continuous_attnScores_self i).prodMk hv)

/-- The attention head is continuous in its value-projection weights. -/
lemma continuous_attnHead_weight {n d : ℕ} [NeZero n] {scale : ℝ} (Y : Fin n → Fin d → ℝ) :
    Continuous (fun W : Fin d → Fin d → ℝ => attnHead scale W Y) := by
  have hmm : Continuous (fun W : Fin d → Fin d → ℝ => matMulCoord W Y) := by
    refine continuous_pi (fun i => continuous_pi (fun j => ?_))
    simp only [matMulCoord]
    exact continuous_finset_sum _ (fun k _ => continuous_const.mul (continuous_apply_apply k j))
  refine continuous_pi (fun i => ?_)
  simp only [attnHead]
  exact continuous_attnVec_uncurry.comp (continuous_const.prodMk hmm)

/-- The coordinatewise clamp is continuous. -/
lemma continuous_clampCoord {s d : ℕ} (B : ℝ) :
    Continuous (clampCoord B : (Fin s → Fin d → ℝ) → Fin s → Fin d → ℝ) := by
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  simp only [clampCoord]
  exact ((continuous_apply_apply i j).min continuous_const).max continuous_const

/-- Each clamped entry has magnitude at most `B`. -/
lemma abs_clampCoord_le {s d : ℕ} {B : ℝ} (hB : 0 ≤ B) (X : Fin s → Fin d → ℝ) (i : Fin s)
    (k : Fin d) : |clampCoord B X i k| ≤ B := by
  have h1 : ‖clampCoord B X i k‖ ≤ ‖clampCoord B X i‖ := norm_le_pi_norm _ k
  have h2 : ‖clampCoord B X i‖ ≤ ‖clampCoord B X‖ := norm_le_pi_norm _ i
  rw [← Real.norm_eq_abs]
  exact le_trans h1 (le_trans h2 (clampCoord_norm_le hB X))

/-- A clamped row has `ℓ¹` norm at most `d · B`. -/
lemma clampCoord_row_l1_le {s d : ℕ} {B : ℝ} (hB : 0 ≤ B) (X : Fin s → Fin d → ℝ) (i : Fin s) :
    (∑ k, |clampCoord B X i k|) ≤ (d : ℝ) * B := by
  calc (∑ k, |clampCoord B X i k|) ≤ ∑ _k : Fin d, B :=
        Finset.sum_le_sum (fun k _ => abs_clampCoord_le hB X i k)
    _ = (d : ℝ) * B := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The certified computable generalization bound for an attention head.** For an executed forward
presented by the layer list `Ls` whose ideal is the clamped attention head `x ↦ attnHead scale W (clamp x)`
at the certified value-projection weights `W = Wdec(w_T)`, with a bounded Lipschitz loss `ℓ` and a
Lipschitz weight decoder `Wdec`: except on a sample event of McDiarmid-small probability, the executed
true risk is at most the executed empirical risk plus the closed capacity-and-rounding budget
`2·(12√2·B_int/√m) + ε + 2·Lℓ·envBound`, where the affine entropy integral carries the
attention-class Lipschitz constant `L = Lℓ·(d·B)·Lw`. The learnable weight is the *attention* value
projection, so the capacity genuinely measures the attention class on the certified region `K = {‖x‖≤B}`
the input cap the clamp realizes. -/
theorem attnHead_certified_generalization {n d p m : ℕ} [NeZero n] [Nonempty (Fin p)]
    [MeasurableSpace (Fin n → Fin d → ℝ)] [BorelSpace (Fin n → Fin d → ℝ)]
    {P : Measure (Fin n → Fin d → ℝ)} [IsProbabilityMeasure P]
    (hm : 0 < m) {R B scale : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Wdec : ParamSpace p → (Fin d → Fin d → ℝ)) (hWcont : Continuous Wdec)
    {Lw : ℝ} (hWLip : ∀ θ θ', dist (Wdec θ) (Wdec θ') ≤ Lw * dist θ θ')
    (ℓ : (Fin n → Fin d → ℝ) → ℝ) {b : ℝ} (hb : 0 < b) (hℓb : ∀ v, |ℓ v| ≤ b)
    (hℓcont : Continuous ℓ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ)
    (hℓLip : ∀ u v, |ℓ u - ℓ v| ≤ Lℓ * dist u v)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R)
    (prep : (Fin n → Fin d → ℝ) → (Fin n → Fin d → ℝ)) (hprep_meas : Measurable prep)
    (hprep_bound : ∀ x i, (∑ k, |prep x i k|) ≤ (d : ℝ) * B)
    (Ls : List (ExecLayer (Fin n → Fin d → ℝ)))
    (hagree : ∀ x, idealComp Ls x
        = attnHead scale (Wdec (embedBase Capacity.Dyadic w_T.1)) (prep x))
    (hintG : Integrable (fun x => ℓ (execComp Ls x)) P)
    (hLpos : 0 < Lℓ * ((d : ℝ) * B) * Lw) :
    (Measure.pi fun _ : Fin m => P).real
        {S | ¬ ((∫ x, ℓ (execComp Ls x) ∂P)
              ≤ (1 / (m : ℝ)) * ∑ i, ℓ (execComp Ls (S i))
                + (2 * ((12 * Real.sqrt 2) * (1 / Real.sqrt m)
                    * (∫⁻ ε in Set.Ioc (0 : ℝ) (2 * b),
                        ENNReal.ofReal (Real.sqrt (Real.log 2)
                          + Real.sqrt ((p : ℝ) * (4 * R * (Lℓ * ((d : ℝ) * B) * Lw)))
                            * ε ^ (-(1 / 2) : ℝ))).toReal) + ε)
                + 2 * (Lℓ * envBound Ls))}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) := by
  set F : ParamSpace p → (Fin n → Fin d → ℝ) → ℝ :=
    fun θ x => ℓ (attnHead scale (Wdec θ) (prep x)) with hF
  have hdB0 : (0 : ℝ) ≤ (d : ℝ) * B := mul_nonneg (Nat.cast_nonneg d) hB
  have hFb : ∀ θ x, |F θ x| ≤ b := fun θ x => hℓb _
  have hFcont : ∀ x, Continuous fun θ : ParamSpace p => F θ x := fun x =>
    hℓcont.comp ((continuous_attnHead_weight (prep x)).comp hWcont)
  have hFmeas : ∀ θ, Measurable (F θ) := fun θ =>
    hℓcont.measurable.comp ((continuous_attnHead_input (Wdec θ)).measurable.comp hprep_meas)
  have hbridge : ∀ x, F (embedBase Capacity.Dyadic w_T.1) x = ℓ (idealComp Ls x) :=
    fun x => by simp only [hF]; rw [hagree x]
  have hintF : Integrable (fun x => ℓ (idealComp Ls x)) P := by
    have heq : (fun x => ℓ (idealComp Ls x)) = F (embedBase Capacity.Dyadic w_T.1) :=
      funext fun x => (hbridge x).symm
    rw [heq]; exact integrable_of_bound_of_measurable (hFmeas _) (fun x => hFb _ x)
  have hlip : ∀ S : Fin m → (Fin n → Fin d → ℝ),
      ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      dist (valueVec F S θ) (valueVec F S θ') ≤ Lℓ * ((d : ℝ) * B) * Lw * dist θ θ' := by
    intro S θ _ θ' _
    refine (dist_pi_le_iff (mul_nonneg hLpos.le dist_nonneg)).mpr (fun j => ?_)
    rw [Real.dist_eq]
    simp only [valueVec, hF]
    calc |ℓ (attnHead scale (Wdec θ) (prep (S j)))
            - ℓ (attnHead scale (Wdec θ') (prep (S j)))|
        ≤ Lℓ * dist (attnHead scale (Wdec θ) (prep (S j)))
              (attnHead scale (Wdec θ') (prep (S j))) := hℓLip _ _
      _ ≤ Lℓ * ((d : ℝ) * B * dist (Wdec θ) (Wdec θ')) :=
          mul_le_mul_of_nonneg_left
            (attnHead_weight_lip (prep (S j)) hdB0 (hprep_bound (S j))
              (Wdec θ) (Wdec θ')) hLℓ0
      _ ≤ Lℓ * ((d : ℝ) * B * (Lw * dist θ θ')) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hWLip θ θ') hdB0) hLℓ0
      _ = Lℓ * ((d : ℝ) * B) * Lw * dist θ θ' := by ring
  exact certified_executed_generalization_dudley hm hR F hb hFb hFmeas hFcont hε w_T Ls ℓ hLℓ0
    hℓLip hbridge hintF hintG hLpos hlip

end TLT
