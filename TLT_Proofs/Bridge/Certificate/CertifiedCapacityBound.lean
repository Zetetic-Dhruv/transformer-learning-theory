/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Capacity.SubGaussianRademacher.UniformGapMcDiarmidConcentration
import TLT_Proofs.Bridge.Certificate.CertifiedRiskBound

/-!
# Certified high-probability generalization bound for the executed model

The capacity analysis (`perNet_gap_concentration`) controls the *ideal* forward map's generalization
gap with high probability over the sample, and the float-transfer assembly
(`certifiedRiskBound_of_idealRisk`) carries an ideal-risk bound to the *executed* model up to the
rounding envelope `2·Lℓ·envBound`. This file joins them: whenever the ideal forward map at the
executed network's weights is the loss composed with the ideal layer composition
(`F (embedBase …) = ℓ ∘ idealComp Ls`), the executed true risk exceeds the executed empirical risk
plus the capacity-and-rounding budget only on a sample event of McDiarmid-small probability.

The capacity term `∫ S', empiricalCapacityReal R F S'` is left abstract here; the covering-number
discharge of the Dudley hypotheses turns it into a computable quantity, but that refinement is
independent of this ideal-to-executed wiring.

## Main results

- `certified_executed_generalization` — with probability at least `1 − exp(−2ε²/(m·(2b/m)²))` over the
  sample, the executed true risk is at most the executed empirical risk plus
  `2·capacity + ε + 2·Lℓ·envBound`.
-/

/-!
## References
- [18] McDiarmid tail; [19][54] Rademacher backbone; [25][26] uniform-capacity reduction.
- Provenance: Innovation — the high-probability executed-model generalization bound (McDiarmid gap
  + `2·L·envBound` in one bound). Concentration/Rademacher legs vendored/classical.
-/

open MeasureTheory

noncomputable section

namespace TLT

open Capacity

variable {V : Type*} [PseudoMetricSpace V] [MeasurableSpace V] {P : Measure V} {m : ℕ}

/-- **Certified executed generalization bound.** Fix an executed network whose ℝ-shadow weight `w_T`
lies in the dyadic ball, and suppose the ideal forward map at those weights is the loss composed with
the ideal layer composition (`hbridge`). Then, except on a sample event of probability at most the
McDiarmid rate, the executed true risk is bounded by the executed empirical risk plus the statistical
capacity `2·∫capacity + ε` and the rounding budget `2·Lℓ·envBound`. The ideal capacity bound
(`perNet_gap_concentration`) and the float-transfer assembly (`certifiedRiskBound_of_idealRisk`) are
joined through the bridge identity. -/
theorem certified_executed_generalization [IsProbabilityMeasure P] {d : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 ≤ R) (F : ParamSpace d → V → ℝ) {b : ℝ} (hFb : ∀ θ x, |F θ x| ≤ b)
    (hFmeas : ∀ θ, Measurable (F θ)) (hFcont : ∀ x, Continuous fun θ : ParamSpace d => F θ x)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R)
    (Ls : List (ExecLayer V)) (ℓ : V → ℝ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ)
    (hℓLip : ∀ p q, |ℓ p - ℓ q| ≤ Lℓ * dist p q)
    (hbridge : ∀ x, F (embedBase Capacity.Dyadic w_T.1) x = ℓ (idealComp Ls x))
    (hintF : Integrable (fun x => ℓ (idealComp Ls x)) P)
    (hintG : Integrable (fun x => ℓ (execComp Ls x)) P) :
    (Measure.pi fun _ : Fin m => P).real
        {S | ¬ ((∫ x, ℓ (execComp Ls x) ∂P)
              ≤ (1 / (m : ℝ)) * ∑ i, ℓ (execComp Ls (S i))
                + (2 * (∫ S', empiricalCapacityReal R F S' ∂(Measure.pi fun _ : Fin m => P)) + ε)
                + 2 * (Lℓ * envBound Ls))}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) := by
  have htrue : trueRisk P (F (embedBase Capacity.Dyadic w_T.1)) = ∫ x, ℓ (idealComp Ls x) ∂P := by
    simp only [trueRisk]
    exact integral_congr_ae (Filter.Eventually.of_forall hbridge)
  refine le_trans (measureReal_mono ?_)
    (perNet_gap_concentration (P := P) hm hR F hFb hFmeas hFcont hε w_T)
  intro S hS
  simp only [Set.mem_setOf_eq] at hS ⊢
  by_contra hB1
  push Not at hB1
  have hemp : empMean (F (embedBase Capacity.Dyadic w_T.1)) S
      = (1 / (m : ℝ)) * ∑ i, ℓ (idealComp Ls (S i)) := by
    simp only [empMean]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => hbridge (S j))
  have hCap : (∫ x, ℓ (idealComp Ls x) ∂P)
      ≤ (1 / (m : ℝ)) * ∑ i, ℓ (idealComp Ls (S i))
        + (2 * (∫ S', empiricalCapacityReal R F S' ∂(Measure.pi fun _ : Fin m => P)) + ε) := by
    rw [← htrue, ← hemp]; linarith [hB1]
  exact hS (certifiedRiskBound_of_idealRisk Ls (fun x => x) hm S ℓ hLℓ0 hℓLip hintF hintG hCap)

/-- **Certified computable generalization bound.** The capstone: replacing the abstract expected
capacity `∫capacity` of `certified_executed_generalization` by any uniform per-sample capacity bound
`capBound` (`0 ≤ capBound`, `empiricalCapacityReal ≤ capBound` for every sample). Then, except on a
sample event of McDiarmid-small probability, the executed true risk is at most the executed empirical
risk plus the *computable* capacity-and-rounding budget `2·capBound + ε + 2·Lℓ·envBound`. Supplying
`capBound = 12√2·(1/√m)·entropyIntegral` (the Dudley bound, finite by the covering discharge) makes
the budget a closed quantity in the model's weights. -/
theorem certified_executed_generalization_computable [IsProbabilityMeasure P] {d : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 ≤ R) (F : ParamSpace d → V → ℝ) {b : ℝ} (hFb : ∀ θ x, |F θ x| ≤ b)
    (hFmeas : ∀ θ, Measurable (F θ)) (hFcont : ∀ x, Continuous fun θ : ParamSpace d => F θ x)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R)
    (Ls : List (ExecLayer V)) (ℓ : V → ℝ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ)
    (hℓLip : ∀ p q, |ℓ p - ℓ q| ≤ Lℓ * dist p q)
    (hbridge : ∀ x, F (embedBase Capacity.Dyadic w_T.1) x = ℓ (idealComp Ls x))
    (hintF : Integrable (fun x => ℓ (idealComp Ls x)) P)
    (hintG : Integrable (fun x => ℓ (execComp Ls x)) P)
    {capBound : ℝ} (hcap0 : 0 ≤ capBound)
    (hcap : ∀ S : Fin m → V, empiricalCapacityReal R F S ≤ capBound) :
    (Measure.pi fun _ : Fin m => P).real
        {S | ¬ ((∫ x, ℓ (execComp Ls x) ∂P)
              ≤ (1 / (m : ℝ)) * ∑ i, ℓ (execComp Ls (S i))
                + (2 * capBound + ε)
                + 2 * (Lℓ * envBound Ls))}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) := by
  have hintcap : (∫ S', empiricalCapacityReal R F S' ∂(Measure.pi fun _ : Fin m => P)) ≤ capBound := by
    rcases Classical.em (Integrable (fun S' => empiricalCapacityReal R F S')
        (Measure.pi fun _ : Fin m => P)) with hint | hint
    · calc (∫ S', empiricalCapacityReal R F S' ∂(Measure.pi fun _ : Fin m => P))
          ≤ ∫ _S', capBound ∂(Measure.pi fun _ : Fin m => P) :=
            integral_mono hint (integrable_const _) hcap
        _ = capBound := by rw [integral_const]; simp
    · rw [integral_undef hint]; exact hcap0
  refine le_trans (measureReal_mono ?_)
    (certified_executed_generalization (P := P) hm hR F hFb hFmeas hFcont hε w_T Ls ℓ hLℓ0 hℓLip
      hbridge hintF hintG)
  intro S hS
  simp only [Set.mem_setOf_eq] at hS ⊢
  intro hQint
  exact hS (by linarith [hintcap])

end TLT
