/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The sub-Gaussian maximal inequality

The expected maximum of finitely many centered sub-Gaussian random variables grows at most like
`σ · √(2 log N)`. This is the base estimate of a chaining argument: it is the bound applied at each
scale of a Dudley entropy decomposition, where the variables are the increments of a stochastic
process over an `ε`-net and `σ` is the scale.

## Main results

* `expMulSup'_le_sum` — the soft-max bound `exp(t · sup f) ≤ ∑ᵢ exp(t · fᵢ)`.
* `absSup'_le_sum` — the bound `|sup f| ≤ ∑ᵢ |fᵢ|` on a finite set.
* `meanLeLogMgf` — the Cramér–Jensen estimate `E[X] ≤ (1/t) · log E[exp(tX)]` for `t > 0`, the
  exponential form of Jensen's inequality for the convex function `exp`.
* `subGaussianFiniteMax` — for `N ≥ 2` centered random variables whose cumulant generating function
  is bounded by `t²σ²/2`, the expected maximum is at most `σ · √(2 log N)`.

## References

The maximal inequality is Massart's finite-class lemma; see
Boucheron, Lugosi and Massart, *Concentration Inequalities: A Nonasymptotic Theory of Independence*
(Oxford University Press, 2013), and
Massart, *Concentration Inequalities and Model Selection*, École d'Été de Probabilités de
Saint-Flour XXXIII (Lecture Notes in Mathematics 1896, Springer, 2003).
-/

open MeasureTheory ProbabilityTheory Real

noncomputable section

namespace TLT.Capacity

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Soft-max bound: `exp(t · sup' f) ≤ ∑ᵢ exp(t · fᵢ)`. The supremum over a finite set is attained,
so the left side equals one summand of a sum of positive terms. -/
theorem expMulSup'_le_sum {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) (t : ℝ) :
    Real.exp (t * s.sup' hs f) ≤ ∑ i ∈ s, Real.exp (t * f i) := by
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup' hs f
  rw [hmax]
  exact Finset.single_le_sum (f := fun i => Real.exp (t * f i)) (fun i _ => (exp_pos _).le) hj

/-- The supremum of finitely many reals is bounded by the sum of their absolute values. -/
theorem absSup'_le_sum {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    |s.sup' hs f| ≤ ∑ i ∈ s, |f i| := by
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup' hs f
  rw [hmax]
  exact Finset.single_le_sum (f := fun i => |f i|) (fun i _ => abs_nonneg _) hj

/-- Cramér–Jensen estimate: `E[X] ≤ (1/t) · log E[exp(tX)]` for `t > 0`. This is Jensen's inequality
`exp(E[tX]) ≤ E[exp(tX)]` for the convex function `exp`, rearranged. -/
theorem meanLeLogMgf {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX_int : Integrable X μ)
    {t : ℝ} (ht : 0 < t) (hexpX_int : Integrable (fun ω => Real.exp (t * X ω)) μ) :
    ∫ ω, X ω ∂μ ≤ (1 / t) * Real.log (∫ ω, Real.exp (t * X ω) ∂μ) := by
  have htX_int : Integrable (fun ω => t * X ω) μ := hX_int.const_mul t
  have hJensen := convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
    (by simp) htX_int hexpX_int
  rw [integral_const_mul] at hJensen
  have h2 : t * ∫ ω, X ω ∂μ ≤ Real.log (∫ ω, Real.exp (t * X ω) ∂μ) :=
    (Real.log_exp _).symm.trans_le (Real.log_le_log (exp_pos _) hJensen)
  have key : t * (∫ ω, X ω ∂μ) ≤ t * ((1 / t) * Real.log (∫ ω, Real.exp (t * X ω) ∂μ)) := by
    rw [← mul_assoc, mul_one_div, div_self ht.ne', one_mul]; exact h2
  exact le_of_mul_le_mul_left key ht

/-- **Sub-Gaussian maximal inequality (Massart's finite-class lemma).** For `N = |s| ≥ 2` random
variables `Xᵢ` whose cumulant generating function is bounded by `t²σ²/2` (the centered sub-Gaussian
condition with proxy variance `σ²`), the expectation of their maximum is at most `σ · √(2 log N)`.

This is the per-scale estimate of a chaining argument. The proof is the exponential (Chernoff)
method: bound `exp(t · E[max])` by Jensen, dominate the maximum by a soft-max sum, apply the MGF
bound to each term, take logarithms, and optimize over `t` at `t = √(2 log N) / σ`. -/
theorem subGaussianFiniteMax {ι : Type*} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    {s : Finset ι} (hs : s.Nonempty) (hs_card : 2 ≤ s.card)
    (hX_meas : ∀ i ∈ s, Measurable (X i))
    (hX_int : ∀ i ∈ s, Integrable (X i) μ)
    (hX_cgf : ∀ i ∈ s, ∀ t, cgf (X i) μ t ≤ t ^ 2 * σ ^ 2 / 2)
    (hX_exp_int : ∀ i ∈ s, ∀ t, Integrable (fun ω => Real.exp (t * X i ω)) μ) :
    ∫ ω, s.sup' hs (fun i => X i ω) ∂μ ≤ σ * Real.sqrt (2 * Real.log s.card) := by
  set n := s.card with hn_def
  have hn_pos : 0 < n := Nat.lt_of_lt_of_le (by norm_num) hs_card
  have hlogn_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hs_card)
  set t_opt := Real.sqrt (2 * Real.log n) / σ with ht_def
  have ht_pos : 0 < t_opt := div_pos (Real.sqrt_pos.mpr (by positivity)) hσ
  -- The pointwise maximum is measurable.
  have hsup_meas : Measurable (fun ω => s.sup' hs (fun i => X i ω)) := by
    have heq : (fun ω => s.sup' hs (fun i => X i ω)) = s.sup' hs X := by
      funext ω; rw [Finset.sup'_apply]
    rw [heq]; exact Finset.measurable_sup' hs (fun i hi => hX_meas i hi)
  -- Optimization identity: the value at `t_opt` is exactly `σ · √(2 log n)`.
  have h_algebra : (1 / t_opt) * (Real.log n + t_opt ^ 2 * σ ^ 2 / 2) =
      σ * Real.sqrt (2 * Real.log n) := by
    rw [ht_def]
    have h1 : (Real.sqrt (2 * Real.log n) / σ) ^ 2 = (2 * Real.log n) / σ ^ 2 := by
      rw [div_pow, sq_sqrt (by positivity : (0:ℝ) ≤ 2 * Real.log n)]
    calc (1 / (Real.sqrt (2 * Real.log n) / σ)) *
            (Real.log n + (Real.sqrt (2 * Real.log n) / σ) ^ 2 * σ ^ 2 / 2)
        = (σ / Real.sqrt (2 * Real.log n)) *
            (Real.log n + (2 * Real.log n) / σ ^ 2 * σ ^ 2 / 2) := by rw [one_div, inv_div, h1]
      _ = (σ / Real.sqrt (2 * Real.log n)) * (Real.log n + Real.log n) := by
          congr 1; field_simp
      _ = σ * (2 * Real.log n / Real.sqrt (2 * Real.log n)) := by ring
      _ = σ * Real.sqrt (2 * Real.log n) := by
          congr 1
          rw [div_eq_iff (Real.sqrt_ne_zero'.mpr (by positivity : (0:ℝ) < 2 * Real.log n))]
          exact (Real.mul_self_sqrt (by positivity)).symm
  -- The maximum is integrable (dominated by the sum of absolute values).
  have hsup_int : Integrable (fun ω => s.sup' hs (fun i => X i ω)) μ := by
    refine (integrable_finset_sum s (fun i hi => (hX_int i hi).abs)).mono'
      hsup_meas.aestronglyMeasurable (ae_of_all μ (fun ω => ?_))
    rw [Real.norm_eq_abs]
    exact absSup'_le_sum hs (fun i => X i ω)
  -- MGF bound for each variable at the optimal exponent.
  have hMGF_bound : ∀ i ∈ s, ∫ ω, Real.exp (t_opt * X i ω) ∂μ ≤
      Real.exp (t_opt ^ 2 * σ ^ 2 / 2) := by
    intro i hi
    have hcgf := hX_cgf i hi t_opt
    unfold ProbabilityTheory.cgf at hcgf
    have h := exp_le_exp.mpr hcgf
    unfold ProbabilityTheory.mgf at h
    rwa [exp_log (integral_exp_pos (hX_exp_int i hi t_opt))] at h
  have hsum_int : Integrable (fun ω => ∑ i ∈ s, Real.exp (t_opt * X i ω)) μ :=
    integrable_finset_sum s (fun i hi => hX_exp_int i hi t_opt)
  -- Soft-max + linearity: `E[exp(t·max)] ≤ N · exp(t²σ²/2)`.
  have hsup_exp_bound : ∫ ω, Real.exp (t_opt * s.sup' hs (fun i => X i ω)) ∂μ ≤
      n * Real.exp (t_opt ^ 2 * σ ^ 2 / 2) := by
    calc ∫ ω, Real.exp (t_opt * s.sup' hs (fun i => X i ω)) ∂μ
        ≤ ∫ ω, ∑ i ∈ s, Real.exp (t_opt * X i ω) ∂μ :=
          integral_mono_of_nonneg (ae_of_all μ (fun ω => (exp_pos _).le)) hsum_int
            (ae_of_all μ (fun ω => expMulSup'_le_sum hs (fun i => X i ω) t_opt))
      _ = ∑ i ∈ s, ∫ ω, Real.exp (t_opt * X i ω) ∂μ :=
          integral_finset_sum s (fun i hi => hX_exp_int i hi t_opt)
      _ ≤ ∑ _i ∈ s, Real.exp (t_opt ^ 2 * σ ^ 2 / 2) := Finset.sum_le_sum hMGF_bound
      _ = n * Real.exp (t_opt ^ 2 * σ ^ 2 / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul, hn_def]
  have hsup_exp_int : Integrable (fun ω => Real.exp (t_opt * s.sup' hs (fun i => X i ω))) μ := by
    refine hsum_int.mono' (hsup_meas.const_mul t_opt).exp.aestronglyMeasurable
      (ae_of_all μ (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact expMulSup'_le_sum hs (fun i => X i ω) t_opt
  have hsup_exp_pos : 0 < ∫ ω, Real.exp (t_opt * s.sup' hs (fun i => X i ω)) ∂μ :=
    integral_exp_pos hsup_exp_int
  -- Logarithm of the exponential-moment bound.
  have hlog_bound : Real.log (∫ ω, Real.exp (t_opt * s.sup' hs (fun i => X i ω)) ∂μ) ≤
      Real.log n + t_opt ^ 2 * σ ^ 2 / 2 := by
    calc Real.log (∫ ω, Real.exp (t_opt * s.sup' hs (fun i => X i ω)) ∂μ)
        ≤ Real.log (n * Real.exp (t_opt ^ 2 * σ ^ 2 / 2)) :=
          Real.log_le_log hsup_exp_pos hsup_exp_bound
      _ = Real.log n + t_opt ^ 2 * σ ^ 2 / 2 := by
          rw [Real.log_mul (by exact_mod_cast hn_pos.ne') (exp_pos _).ne', Real.log_exp]
  -- Assemble: Jensen, the log bound, and the optimization identity.
  calc ∫ ω, s.sup' hs (fun i => X i ω) ∂μ
      ≤ (1 / t_opt) * Real.log (∫ ω, Real.exp (t_opt * s.sup' hs (fun i => X i ω)) ∂μ) :=
        meanLeLogMgf hsup_int ht_pos hsup_exp_int
    _ ≤ (1 / t_opt) * (Real.log n + t_opt ^ 2 * σ ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hlog_bound (by positivity)
    _ = σ * Real.sqrt (2 * Real.log n) := h_algebra

end TLT.Capacity
