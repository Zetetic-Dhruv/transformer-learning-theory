/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Capacity.McDiarmid
import TLT_Proofs.Capacity.BaseInvariantBound

/-!
# Concentration of the uniform generalization gap

The empirical mean of a bounded function has the bounded-differences property with constant `2b/m`:
altering a single sample point changes exactly one of the `m` averaged terms, so the average moves by
at most `2b/m`. The uniform gap `⨆_w (trueRisk w − empMean w S)` inherits this — a supremum of
functions that each move by at most `2b/m` itself moves by at most `2b/m` — so McDiarmid's inequality
converts the in-expectation uniform-deviation bound into a per-sample high-probability bound.

## Main results

- `empMean_boundedDifferences` — the empirical mean has bounded differences `2b/m`.
- `gapSup_boundedDifferences` — the uniform gap inherits bounded differences `2b/m`.
- `gapSup_concentration` — McDiarmid concentration of the uniform gap above its mean.
-/

open MeasureTheory

noncomputable section

namespace TLT.Capacity

variable {X : Type*} [MeasurableSpace X] {P : Measure X} {m : ℕ}

omit [MeasurableSpace X] in
/-- **The empirical mean has bounded differences `2b/m`.** Altering one of the `m` sample points
changes only its own term in the average, so the mean moves by at most `2b/m`. -/
lemma empMean_boundedDifferences (hm : 0 < m) {g : X → ℝ} {b : ℝ} (hb : ∀ x, |g x| ≤ b) :
    HasBoundedDifferences (fun S : Fin m → X => empMean g S) (2 * b / m) := by
  intro i S S' hagree
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum : (∑ j, g (S j)) - ∑ j, g (S' j) = g (S i) - g (S' i) := by
    rw [← Finset.sum_sub_distrib,
      Finset.sum_eq_single i (fun j _ hj => by rw [hagree j hj]; ring)
        (fun h => absurd (Finset.mem_univ i) h)]
  have hdiff : empMean g S - empMean g S' = (1 / m) * (g (S i) - g (S' i)) := by
    simp only [empMean]; rw [← mul_sub, hsum]
  have h1 := abs_le.mp (hb (S i))
  have h2 := abs_le.mp (hb (S' i))
  have hgi : |g (S i) - g (S' i)| ≤ 2 * b :=
    abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  rw [hdiff, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / m)]
  calc 1 / m * |g (S i) - g (S' i)| ≤ 1 / m * (2 * b) :=
        mul_le_mul_of_nonneg_left hgi (by positivity)
    _ = 2 * b / m := by ring

omit [MeasurableSpace X] in
/-- **The uniform gap has bounded differences `2b/m`.** A supremum of empirical-mean gaps, each with
bounded differences `2b/m`, itself has bounded differences `2b/m`. This is the hypothesis that lets
McDiarmid's inequality convert the in-expectation uniform deviation into a high-probability bound. -/
lemma gapSup_boundedDifferences {ι : Type*} [Nonempty ι] (hm : 0 < m) {c : ι → ℝ} {g : ι → X → ℝ}
    {b : ℝ} (hc : ∀ w, |c w| ≤ b) (hb : ∀ w x, |g w x| ≤ b) :
    HasBoundedDifferences (fun S : Fin m → X => ⨆ w, (c w - empMean (g w) S)) (2 * b / m) := by
  intro i S S' hagree
  have hbdd : ∀ T : Fin m → X, BddAbove (Set.range fun w => c w - empMean (g w) T) := fun T =>
    ⟨2 * b, by
      rintro y ⟨w, rfl⟩
      have hcw := abs_le.mp (hc w)
      have hew := abs_le.mp (empMean_abs_le hm (hb w) T)
      linarith [hcw.1, hcw.2, hew.1, hew.2]⟩
  have key : ∀ T T' : Fin m → X, (∀ w, |empMean (g w) T - empMean (g w) T'| ≤ 2 * b / m) →
      (⨆ w, (c w - empMean (g w) T)) - ⨆ w, (c w - empMean (g w) T') ≤ 2 * b / m := by
    intro T T' hww
    have hle : (⨆ w, (c w - empMean (g w) T)) ≤ (⨆ w, (c w - empMean (g w) T')) + 2 * b / m := by
      refine ciSup_le fun w => ?_
      have hw := abs_le.mp (hww w)
      calc c w - empMean (g w) T ≤ (c w - empMean (g w) T') + 2 * b / m := by linarith [hw.1, hw.2]
        _ ≤ (⨆ w, (c w - empMean (g w) T')) + 2 * b / m := by linarith [le_ciSup (hbdd T') w]
    linarith
  have hempw : ∀ w, |empMean (g w) S - empMean (g w) S'| ≤ 2 * b / m := fun w =>
    empMean_boundedDifferences hm (hb w) i S S' hagree
  have hempw' : ∀ w, |empMean (g w) S' - empMean (g w) S| ≤ 2 * b / m := fun w => by
    rw [abs_sub_comm]; exact hempw w
  show |(⨆ w, (c w - empMean (g w) S)) - ⨆ w, (c w - empMean (g w) S')| ≤ 2 * b / m
  rw [abs_le]
  exact ⟨by linarith [key S' S hempw'], key S S' hempw⟩

/-- **Concentration of the uniform gap.** The uniform deviation `⨆_w (c_w − empMean(g_w) S)`
concentrates above its mean with the McDiarmid rate `exp(−2ε²/(m·(2b/m)²))`. Combined with the
in-expectation bound `E_S[⨆_w …] ≤ 2·capacity`, this gives the per-sample high-probability
generalization bound. -/
theorem gapSup_concentration {ι : Type*} [Nonempty ι] [Countable ι] [IsProbabilityMeasure P]
    (hm : 0 < m) {c : ι → ℝ} {g : ι → X → ℝ} {b ε : ℝ} (hc : ∀ w, |c w| ≤ b)
    (hb : ∀ w x, |g w x| ≤ b) (hgmeas : ∀ w, Measurable (g w)) (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin m => P).real
        {S | ε ≤ (⨆ w, (c w - empMean (g w) S))
              - ∫ S', (⨆ w, (c w - empMean (g w) S')) ∂(Measure.pi fun _ : Fin m => P)}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) := by
  have hb0 : 0 ≤ b := (abs_nonneg (c (Classical.arbitrary ι))).trans (hc _)
  have hmeas : Measurable fun S : Fin m → X => ⨆ w, (c w - empMean (g w) S) :=
    Measurable.iSup fun w => measurable_const.sub (measurable_empMean (hgmeas w))
  exact mcdiarmid _ hmeas (by positivity) (gapSup_boundedDifferences hm hc hb) hε

/-- **Generalization gap exceeds twice the capacity with small probability.** Chaining the in-
expectation symmetrization bound (`expectedGap_le_two_capacityReal`) with McDiarmid concentration: the
probability that the uniform deviation exceeds `2·capacity + ε` is at most the McDiarmid rate. This is
the per-sample high-probability generalization bound over the dyadic weight ball. -/
theorem expectedGap_concentration [IsProbabilityMeasure P] {d : ℕ} (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R)
    (F : ParamSpace d → X → ℝ) {b : ℝ} (hFb : ∀ θ x, |F θ x| ≤ b)
    (hFmeas : ∀ θ, Measurable (F θ)) (hFcont : ∀ x, Continuous fun θ : ParamSpace d => F θ x)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin m => P).real
        {S | 2 * (∫ S', empiricalCapacityReal R F S' ∂(Measure.pi fun _ : Fin m => P)) + ε
              ≤ ⨆ w : BaseWeightPreimage Dyadic R,
                  (trueRisk P (F (embedBase Dyadic w.1)) - empMean (F (embedBase Dyadic w.1)) S)}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) := by
  have h0 : (0 : Fin d → Dyadic) ∈ BaseWeightPreimage Dyadic R := by
    show embedBase Dyadic (0 : Fin d → Dyadic) ∈ RealBall d R
    rw [embedBase_zero]; simp only [RealBall, Metric.mem_closedBall, dist_self]; exact hR
  haveI : Nonempty (BaseWeightPreimage Dyadic R) := ⟨⟨0, h0⟩⟩
  have hgi : ∀ w : BaseWeightPreimage Dyadic R, Integrable (F (embedBase Dyadic w.1)) P :=
    fun w => integrable_of_bound_of_measurable (hFmeas (embedBase Dyadic w.1))
      fun x => hFb (embedBase Dyadic w.1) x
  have hc : ∀ w : BaseWeightPreimage Dyadic R, |trueRisk P (F (embedBase Dyadic w.1))| ≤ b :=
    fun w => trueRisk_abs_le (hgi w) fun x => hFb (embedBase Dyadic w.1) x
  have hconc := gapSup_concentration (P := P) (ι := BaseWeightPreimage Dyadic R)
    (g := fun w => F (embedBase Dyadic w.1)) hm hc
    (fun w x => hFb (embedBase Dyadic w.1) x) (fun w => hFmeas (embedBase Dyadic w.1)) hε
  have hexp := expectedGap_le_two_capacityReal (P := P) hm hR F hFb hFmeas hFcont
  refine le_trans (measureReal_mono fun S hS => ?_) hconc
  simp only [Set.mem_setOf_eq] at hS ⊢
  linarith [hexp]

/-- **Per-net high-probability generalization bound.** For any fixed dyadic net `w₀` in the ball, its
individual gap `trueRisk − empMean` is dominated by the uniform supremum, so its tail above
`2·capacity + ε` inherits the McDiarmid rate. This is the ideal-risk generalization bound that the
executed-model risk transfer consumes for the float32 net's ℝ-shadow. -/
theorem perNet_gap_concentration [IsProbabilityMeasure P] {d : ℕ} (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R)
    (F : ParamSpace d → X → ℝ) {b : ℝ} (hFb : ∀ θ x, |F θ x| ≤ b)
    (hFmeas : ∀ θ, Measurable (F θ)) (hFcont : ∀ x, Continuous fun θ : ParamSpace d => F θ x)
    {ε : ℝ} (hε : 0 ≤ ε) (w₀ : BaseWeightPreimage Dyadic R) :
    (Measure.pi fun _ : Fin m => P).real
        {S | 2 * (∫ S', empiricalCapacityReal R F S' ∂(Measure.pi fun _ : Fin m => P)) + ε
              ≤ trueRisk P (F (embedBase Dyadic w₀.1)) - empMean (F (embedBase Dyadic w₀.1)) S}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) := by
  haveI : Nonempty (BaseWeightPreimage Dyadic R) := ⟨w₀⟩
  refine le_trans (measureReal_mono fun S hS => ?_)
    (expectedGap_concentration (P := P) hm hR F hFb hFmeas hFcont hε)
  simp only [Set.mem_setOf_eq] at hS ⊢
  have hbdd : BddAbove (Set.range fun w : BaseWeightPreimage Dyadic R =>
      trueRisk P (F (embedBase Dyadic w.1)) - empMean (F (embedBase Dyadic w.1)) S) :=
    ⟨2 * b, by
      rintro y ⟨w, rfl⟩
      have hgi : Integrable (F (embedBase Dyadic w.1)) P :=
        integrable_of_bound_of_measurable (hFmeas _) fun x => hFb _ x
      have hcw := abs_le.mp (trueRisk_abs_le hgi fun x => hFb _ x)
      have hew := abs_le.mp (empMean_abs_le hm (fun x => hFb (embedBase Dyadic w.1) x) S)
      linarith [hcw.1, hcw.2, hew.1, hew.2]⟩
  exact hS.trans (le_ciSup hbdd w₀)

end TLT.Capacity
