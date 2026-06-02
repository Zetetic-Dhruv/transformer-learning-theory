/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Capacity.DyadicBase
import TLT_Proofs.Capacity.SymmetrizationDudley

/-!
# The base-invariant generalization bound

Combining the in-expectation symmetrization with the dense base-change capacity invariance: for a
uniformly bounded model `F` parametrised over the **dyadic** weight ball (the countable base that
contains every executed float value), the expected uniform deviation of true risk from empirical mean
is at most twice the **real** ball's empirical Rademacher complexity.

This is the experiment→theory bridge for the generalization gap: the gap of the (countable, executed)
dyadic class is controlled by the capacity of the (continuous, theoretical) real class. Crucially, the
measurability hypotheses of symmetrization are discharged for free — the dyadic ball is **countable**,
so each supremum envelope is a countable supremum of measurable functions.

## Main results

- `expectedGap_le_two_capacityReal` — expected uniform deviation ≤ 2 · real-ball capacity.
-/

open MeasureTheory

noncomputable section

namespace TLT.Capacity

variable {X : Type*} [MeasurableSpace X] {P : Measure X} {d m : ℕ}

/-- The coordinatewise embedding sends the zero weight vector to the origin. -/
theorem embedBase_zero (B : Type*) [CommRing B] [NumBase B] :
    embedBase B (0 : Fin d → B) = 0 := by
  have hz : (fun i => NumBase.toReal ((0 : Fin d → B) i)) = (0 : Fin d → ℝ) := by
    funext i; simp
  unfold embedBase; rw [hz, WithLp.toLp_zero]

/-- The empirical Rademacher average composed with sampling is measurable in the sample. -/
theorem measurable_empRadVec_sample {g : X → ℝ} (hg : Measurable g) (σ : SignVector m) :
    Measurable (fun S : Fin m → X => empRadVec (fun j => g (S j)) σ) := by
  unfold empRadVec empRad
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum Finset.univ fun j _ => ?_
  exact (hg.comp (measurable_pi_apply j)).mul measurable_const

/-- **Base-invariant generalization bound.** For a uniformly bounded model `F` that is continuous in
its parameters and measurable in its input, the expected uniform deviation over the dyadic weight ball
is at most twice the empirical Rademacher complexity of the real weight ball. The measurability
hypotheses of symmetrization are discharged via the countability of the dyadic base. -/
theorem expectedGap_le_two_capacityReal [IsProbabilityMeasure P] (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R)
    (F : ParamSpace d → X → ℝ) {b : ℝ} (hFb : ∀ θ x, |F θ x| ≤ b)
    (hFmeas : ∀ θ, Measurable (F θ)) (hFcont : ∀ x, Continuous fun θ : ParamSpace d => F θ x) :
    ∫ S, ⨆ w : BaseWeightPreimage Dyadic R,
        (trueRisk P (F (embedBase Dyadic w.1)) - empMean (F (embedBase Dyadic w.1)) S)
        ∂(Measure.pi fun _ : Fin m => P)
      ≤ 2 * ∫ S, empiricalCapacityReal R F S ∂(Measure.pi fun _ : Fin m => P) := by
  have h0base : (0 : Fin d → Dyadic) ∈ BaseWeightPreimage Dyadic R := by
    show embedBase Dyadic (0 : Fin d → Dyadic) ∈ RealBall d R
    rw [embedBase_zero]
    simp only [RealBall, Metric.mem_closedBall, dist_self]; exact hR
  haveI : Nonempty (BaseWeightPreimage Dyadic R) := ⟨⟨0, h0base⟩⟩
  set g : BaseWeightPreimage Dyadic R → X → ℝ := fun w => F (embedBase Dyadic w.1) with hg
  have hgb : ∀ w x, |g w x| ≤ b := fun w x => hFb _ _
  have hgmeas : ∀ w, Measurable (g w) := fun w => hFmeas _
  have hgi : ∀ w, Integrable (g w) P :=
    fun w => integrable_of_bound_of_measurable (hgmeas w) (fun x => hgb w x)
  have hφ : Measurable fun S : Fin m → X => ⨆ w, (trueRisk P (g w) - empMean (g w) S) :=
    Measurable.iSup fun w => measurable_const.sub (measurable_empMean (hgmeas w))
  have hψ : Measurable fun q : (Fin m → X) × (Fin m → X) =>
      ⨆ w, (empMean (g w) q.2 - empMean (g w) q.1) :=
    Measurable.iSup fun w =>
      ((measurable_empMean (hgmeas w)).comp measurable_snd).sub
        ((measurable_empMean (hgmeas w)).comp measurable_fst)
  have hrad : ∀ σ : SignVector m,
      Measurable fun S : Fin m → X => ⨆ w, empRadVec (fun j => g w (S j)) σ :=
    fun σ => Measurable.iSup fun w => measurable_empRadVec_sample (hgmeas w) σ
  have hsymm := symmetrization_le hm g hgb hgi hgmeas hφ hψ hrad
  refine hsymm.trans (le_of_eq ?_)
  congr 1
  refine integral_congr_ae (ae_of_all _ fun S => ?_)
  exact empiricalCapacity_base_eq_real Dyadic hR F S hFcont

omit [MeasurableSpace X] in
/-- **Dudley bound on the real-ball capacity.** The real-ball empirical Rademacher complexity is at
most `12√2·(1/√m)` times the Dudley entropy integral of its value-vector set. The totally-bounded,
diameter and finite-entropy hypotheses are exactly those discharged, for a Lipschitz model, by a
covering-number bound on the (compact) weight ball. -/
theorem capacityReal_le_dudley (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R) (F : ParamSpace d → X → ℝ) {b : ℝ}
    (hFb : ∀ θ x, |F θ x| ≤ b) (S : Fin m → X)
    (hs : TotallyBounded (lossValueSet (fun θ : RealBall d R => F θ.1) S)) {D : ℝ} (hD : 0 < D)
    (hdiam : Metric.diam (lossValueSet (fun θ : RealBall d R => F θ.1) S) ≤ D)
    (hfin : entropyIntegralENNReal (lossValueSet (fun θ : RealBall d R => F θ.1) S) D ≠ ⊤) :
    empiricalCapacityReal R F S
      ≤ (12 * Real.sqrt 2) * (1 / Real.sqrt m)
          * entropyIntegral (lossValueSet (fun θ : RealBall d R => F θ.1) S) D := by
  haveI : Nonempty (RealBall d R) :=
    ⟨⟨0, by simp only [RealBall, Metric.mem_closedBall, dist_self]; exact hR⟩⟩
  exact empRadComplexity_le_dudley hm (fun θ : RealBall d R => F θ.1)
    (fun θ x => hFb θ.1 x) S hs hD hdiam hfin

end TLT.Capacity
