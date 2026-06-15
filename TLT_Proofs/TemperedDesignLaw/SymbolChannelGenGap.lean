/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.Symmetrization
import TLT_Proofs.TemperedDesignLaw.HardCertDischarge
import TLT_Proofs.TemperedDesignLaw.ArrangementVC

/-!
# The symbol-channel population generalization gap

This module proves the population generalization bound for the **hard symbol route's** per-pair
comparison class, via the FLT Bool symmetrization machinery.

## Proof strategy

`symmetrization_step` (FLT, `FLT_Proofs.Complexity.Symmetrization`) requires only that the concepts
in the class are measurable (`∀ h ∈ C, Measurable h`) and that the target concept is measurable,
not the discrete-`X` cone (`MeasurableConceptClass` / `∀ c, Measurable c`) that
`vcdim_finite_imp_uc'` / `fundamental_rademacher` demand. The comparison class
`comparisonClass A i j` satisfies exactly this: every member is measurable by
`comparisonConcept_measurable` (from the router's joint score-measurability).

Composing:
* `symmetrization_step` : `D^m{bad one-sided gap ≥ ε} ≤ 2 · (D^m ⊗ D^m){double-sample event ≥ ε/2}`,
* `double_sample_pattern_bound` : `(double-sample event) ≤ GrowthFunction C (2m) · exp(-mε²/8)`
  (needs `[Infinite X]` + a `NullMeasurableSet` leg, supplied here by `WellBehavedVC X C`),
* `comparisonClass_growthFunction_le` : `GrowthFunction C (2m) ≤ ∑ r ≤ finrank W, (2m).choose r`
  (the Sauer–Shelah arrangement bound, S3),

yields a population gap controlled by the **Sauer polynomial of the arrangement dimension**.

## Why not the Massart/Rademacher expected-gap form

The Massart bound (`empiricalRademacherComplexity_le_massart`) bounds the *empirical Rademacher
complexity*. The FLT generalization machinery, however, does **not** bridge empirical Rademacher
complexity to the population gap (`Symmetrization.lean` never references it); its symmetrization
chain produces the gap via the **growth function + Hoeffding** instead
(`double_sample_pattern_bound : … ≤ GrowthFunction · exp(-mε²/8)`). The population gap below is
therefore the growth-function/Hoeffding bound, the same generalization guarantee the Massart term
targets, obtained through the FLT symmetrization chain.
-/

noncomputable section

namespace TLT.TemperedDesignLaw

open MeasureTheory

universe u

variable {X : Type u} [MeasurableSpace X] {k : ℕ}

/-- **Population generalization gap for the comparison class (growth-function form).**

For a router code `A`, an ordered pair `(i, j)`, an arbitrary *measurable* target concept `c`, and
a sample size `m` with `0 < m` and `m` large enough (`2 log 2 ≤ m ε²`), the probability under the
`m`-fold product measure that **some** comparison concept `h ∈ comparisonClass A i j` has population
risk exceeding its empirical risk by `ε` is bounded by

`2 · GrowthFunction X (comparisonClass A i j) (2m) · exp(-m ε² / 8)`.

This is the one-sided uniform generalization gap for the symbol route's per-pair comparison channel.
It composes the FLT Bool symmetrization step (`symmetrization_step`, which requires only that the
class's concepts are measurable, supplied by `comparisonConcept_measurable`, not the discrete-`X`
cone) with the double-sample growth bound (`double_sample_pattern_bound`). The `NullMeasurableSet`
leg of the latter is the standard FLT regularity predicate `WellBehavedVC`. -/
theorem comparisonClass_gen_gap [Infinite X]
    (A : FiniteScoreRouterCode X k) (i j : Fin k)
    (D : Measure X) [IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hWB : WellBehavedVC X (comparisonClass A i j))
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hm_large : 2 * Real.log 2 ≤ ↑m * ε ^ 2) :
    Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | ∃ h ∈ comparisonClass A i j,
        TrueErrorReal X h c D -
          EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε}
      ≤ ENNReal.ofReal
          (2 * (↑(GrowthFunction X (comparisonClass A i j) (2 * m)) *
            Real.exp (-(↑m * ε ^ 2 / 8)))) := by
  -- Every concept in the comparison class is measurable, the only measurability the symmetrization
  -- step requires (not the discrete-X cone).
  have hmeas_C : ∀ h ∈ comparisonClass A i j, Measurable h := by
    rintro h ⟨ρ, rfl⟩
    exact comparisonConcept_measurable A ρ i j
  -- The NullMeasurableSet leg of `double_sample_pattern_bound`, from `WellBehavedVC`.
  have hE_nullmeas := hWB D c m ε
  -- Symmetrization (Bool, measurable concepts only) : bad event ≤ 2 · double-sample event.
  have h_symm := symmetrization_step D (comparisonClass A i j) c hmeas_C hc_meas m hm ε hε hm_large
  -- Double-sample event ≤ GrowthFunction · exp(-mε²/8).
  have h_dbl := double_sample_pattern_bound D (comparisonClass A i j) c hmeas_C hc_meas m hm ε hε
    hE_nullmeas
  -- Compose: bad ≤ 2 · double-sample ≤ 2 · (GF · exp).
  calc Measure.pi (fun _ : Fin m => D)
        {xs : Fin m → X | ∃ h ∈ comparisonClass A i j,
          TrueErrorReal X h c D -
            EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε}
      ≤ 2 * (Measure.pi (fun _ : Fin m => D)).prod (Measure.pi (fun _ : Fin m => D))
          {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ comparisonClass A i j,
            EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
            EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2} :=
        h_symm
    _ ≤ 2 * ENNReal.ofReal (↑(GrowthFunction X (comparisonClass A i j) (2 * m)) *
          Real.exp (-(↑m * ε ^ 2 / 8))) := by
        exact mul_le_mul_right h_dbl 2
    _ = ENNReal.ofReal
          (2 * (↑(GrowthFunction X (comparisonClass A i j) (2 * m)) *
            Real.exp (-(↑m * ε ^ 2 / 8)))) := by
        have h2 : (2 : ENNReal) = ENNReal.ofReal 2 := by
          rw [ENNReal.ofReal_ofNat]
        rw [h2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]

/-- **Population generalization gap for the comparison class (Sauer-polynomial form).**

Same as `comparisonClass_gen_gap`, but with the growth function replaced by the
arrangement-VC Sauer–Shelah polynomial (`comparisonClass_growthFunction_le`, S3): under the
linearity hypothesis that each score gap `sⱼ - sᵢ` lives in a finite-dimensional `W`,

`GrowthFunction X (comparisonClass A i j) (2m) ≤ ∑ r ≤ finrank W, (2m).choose r`,

so the population gap is bounded by `2 · (∑ r ≤ finrank W, (2m).choose r) · exp(-m ε² / 8)`. This is
the symbol-channel generalization gap stated in closed form against the arrangement dimension. -/
theorem comparisonClass_gen_gap_sauer [Infinite X]
    (A : FiniteScoreRouterCode X k) (i j : Fin k)
    (W : Submodule ℝ (X → ℝ)) [FiniteDimensional ℝ W]
    (hlin : ∀ ρ : A.Ρ, (fun x => A.score ρ x j - A.score ρ x i) ∈ W)
    (D : Measure X) [IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hWB : WellBehavedVC X (comparisonClass A i j))
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hm_large : 2 * Real.log 2 ≤ ↑m * ε ^ 2) :
    Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | ∃ h ∈ comparisonClass A i j,
        TrueErrorReal X h c D -
          EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε}
      ≤ ENNReal.ofReal
          (2 * (↑(∑ r ∈ Finset.range (Module.finrank ℝ W + 1), (2 * m).choose r) *
            Real.exp (-(↑m * ε ^ 2 / 8)))) := by
  refine le_trans (comparisonClass_gen_gap A i j D c hc_meas hWB m hm ε hε hm_large) ?_
  apply ENNReal.ofReal_le_ofReal
  have hGF : GrowthFunction X (comparisonClass A i j) (2 * m) ≤
      ∑ r ∈ Finset.range (Module.finrank ℝ W + 1), (2 * m).choose r :=
    comparisonClass_growthFunction_le A i j W hlin (2 * m)
  have hGFr : (↑(GrowthFunction X (comparisonClass A i j) (2 * m)) : ℝ) ≤
      ↑(∑ r ∈ Finset.range (Module.finrank ℝ W + 1), (2 * m).choose r) := by
    exact_mod_cast hGF
  have hexp_nonneg : 0 ≤ Real.exp (-(↑m * ε ^ 2 / 8)) := (Real.exp_pos _).le
  have hmono : (↑(GrowthFunction X (comparisonClass A i j) (2 * m)) : ℝ) *
        Real.exp (-(↑m * ε ^ 2 / 8)) ≤
      (↑(∑ r ∈ Finset.range (Module.finrank ℝ W + 1), (2 * m).choose r) : ℝ) *
        Real.exp (-(↑m * ε ^ 2 / 8)) :=
    mul_le_mul_of_nonneg_right hGFr hexp_nonneg
  linarith [hmono]

end TLT.TemperedDesignLaw
