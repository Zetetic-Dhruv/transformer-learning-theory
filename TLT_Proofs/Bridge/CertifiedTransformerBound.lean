/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.CertifiedCapacityBound
import TLT_Proofs.Capacity.CoveringDischarge

/-!
# The certified computable float32 generalization bound

The final assembly. Composing the capstone `certified_executed_generalization_computable` (the certified
bound with an abstract per-sample capacity budget) with the uniform Dudley capacity bound
`empiricalCapacityReal_le_computable` (the covering-number discharge of the entropy integral) yields a
single statement: for a forward map that is bounded, measurable, and continuous in its weights, whose
value-vector map is Lipschitz on the weight ball, and whose executed (IEEE binary32) layers carry the
rounding envelope, the executed true risk exceeds the executed empirical risk plus the **closed
capacity-and-rounding budget** only on a sample event of McDiarmid-small probability:

`R_true^exec ≤ R̂_emp^exec + 2·(12√2·(1/√m)·B) + ε + 2·Lℓ·envBound`,

with `B` the affine entropy integral — a determinate quantity in the weight-ball radius `R`, the
parameter-Lipschitz constant `L`, the input dimension `d`, the loss bound `b`, and the sample size `m`.

## Main results

- `certified_executed_generalization_dudley` — the certified computable float32 generalization bound.
-/

open MeasureTheory

noncomputable section

namespace TLT

open Capacity

variable {V : Type*} [PseudoMetricSpace V] [MeasurableSpace V] {P : Measure V} {m : ℕ}

/-- **The certified computable float32 generalization bound.** For an executed network presented as the
layer list `Ls`, whose ideal forward at the certified weights `w_T` is the loss composed with the ideal
layer composition (`hbridge`), whose weight-parametrised forward `F` is bounded, measurable, and
continuous in the weights, and whose value-vector map is `L`-Lipschitz on the weight ball of radius
`R` (`hlip`): except on a sample event of probability at most the McDiarmid rate
`exp(−2ε²/(m·(2b/m)²))`, the executed true risk is at most the executed empirical risk plus the
closed capacity-and-rounding budget `2·(12√2·(1/√m)·B) + ε + 2·Lℓ·envBound`, where `B` is the affine
Dudley entropy integral. The `R`-ball-conditional Lipschitz hypothesis is the genuine boundary
(self-attention is not globally Lipschitz); the budget is computable from the model's weights. -/
theorem certified_executed_generalization_dudley [IsProbabilityMeasure P] {d : ℕ} [Nonempty (Fin d)]
    (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R) (F : ParamSpace d → V → ℝ) {b : ℝ} (hb : 0 < b)
    (hFb : ∀ θ x, |F θ x| ≤ b) (hFmeas : ∀ θ, Measurable (F θ))
    (hFcont : ∀ x, Continuous fun θ : ParamSpace d => F θ x)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R)
    (Ls : List (ExecLayer V)) (ℓ : V → ℝ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ)
    (hℓLip : ∀ p q, |ℓ p - ℓ q| ≤ Lℓ * dist p q)
    (hbridge : ∀ x, F (embedBase Capacity.Dyadic w_T.1) x = ℓ (idealComp Ls x))
    (hintF : Integrable (fun x => ℓ (idealComp Ls x)) P)
    (hintG : Integrable (fun x => ℓ (execComp Ls x)) P) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ S : Fin m → V, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        ∀ θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        dist (valueVec F S θ) (valueVec F S θ') ≤ L * dist θ θ') :
    (Measure.pi fun _ : Fin m => P).real
        {S | ¬ ((∫ x, ℓ (execComp Ls x) ∂P)
              ≤ (1 / (m : ℝ)) * ∑ i, ℓ (execComp Ls (S i))
                + (2 * ((12 * Real.sqrt 2) * (1 / Real.sqrt m)
                    * (∫⁻ ε in Set.Ioc (0 : ℝ) (2 * b),
                        ENNReal.ofReal (Real.sqrt (Real.log 2)
                          + Real.sqrt ((d : ℝ) * (4 * R * L)) * ε ^ (-(1 / 2) : ℝ))).toReal) + ε)
                + 2 * (Lℓ * envBound Ls))}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) :=
  certified_executed_generalization_computable hm hR F hFb hFmeas hFcont hε w_T Ls ℓ hLℓ0 hℓLip
    hbridge hintF hintG (by positivity)
    (fun S => empiricalCapacityReal_le_computable hm hR F hb hFb S hL (hlip S))

end TLT
