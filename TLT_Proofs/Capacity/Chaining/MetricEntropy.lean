/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Metric entropy and the Dudley entropy integral

The **metric entropy** of a set `s` at scale `ε` is `log N(ε, s)`, the logarithm of its (internal)
covering number. Its square root, integrated against `dε` from `0` to the diameter, is the **Dudley
entropy integral** `∫₀^D √(log N(ε, s)) dε`, the canonical capacity functional bounding the expected
supremum of a sub-Gaussian process indexed by `s` (Dudley's theorem).

The covering number is Mathlib's internal `Metric.coveringNumber`. The entropy integral is defined as
the real part of an `ℝ≥0∞` Lebesgue integral, so it is well-defined even though the integrand may be
unbounded near `0`; finiteness of the integral is an additional hypothesis where needed.

## Main definitions

* `metricEntropy ε s`: `log N(ε, s)`.
* `sqrtEntropy ε s`: `√(log N(ε, s))`, the Dudley integrand value.
* `entropyIntegral s D`: `∫₀^D √(log N(ε, s)) dε`, the Dudley entropy integral.

## References

R. M. Dudley, *The sizes of compact subsets of Hilbert space and continuity of Gaussian processes*,
Journal of Functional Analysis 1 (1967), 290–330. See also R. Vershynin, *High-Dimensional
Probability* (Cambridge University Press, 2018), Chapter 8.
-/

open MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace TLT.Capacity

variable {A : Type*} [PseudoMetricSpace A]

/-- The metric entropy of `s` at scale `ε`: the logarithm of the internal covering number
`N(ε, s)` (taken as a natural number, so the empty/uncoverable cases give entropy `0`). -/
def metricEntropy (ε : ℝ) (s : Set A) : ℝ :=
  Real.log ((Metric.coveringNumber ε.toNNReal s).toNat : ℝ)

/-- The square root of the metric entropy; the integrand of the Dudley entropy integral. -/
def sqrtEntropy (ε : ℝ) (s : Set A) : ℝ := Real.sqrt (metricEntropy ε s)

/-- The metric entropy is nonnegative (the covering number is a natural number, so its logarithm,
under the `log 0 = 0` convention, is `≥ 0`). -/
lemma metricEntropy_nonneg (ε : ℝ) (s : Set A) : 0 ≤ metricEntropy ε s :=
  Real.log_natCast_nonneg _

/-- The Dudley integrand is nonnegative. -/
lemma sqrtEntropy_nonneg (ε : ℝ) (s : Set A) : 0 ≤ sqrtEntropy ε s := Real.sqrt_nonneg _

/-- `log` is monotone along the natural numbers (using `log 0 = 0`). -/
private lemma log_natCast_mono {m n : ℕ} (h : m ≤ n) : Real.log m ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using Real.log_natCast_nonneg n
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast h)

/-- The metric entropy is antitone in the scale `ε`: finer scales need more balls. Requires the
covering number at the finer scale to be finite (which holds for totally bounded `s`). -/
lemma metricEntropy_anti {ε₁ ε₂ : ℝ} {s : Set A} (hε : ε₁ ≤ ε₂)
    (hfin : Metric.coveringNumber ε₁.toNNReal s ≠ ⊤) :
    metricEntropy ε₂ s ≤ metricEntropy ε₁ s := by
  unfold metricEntropy
  exact log_natCast_mono (ENat.toNat_le_toNat
    (Metric.coveringNumber_anti (Real.toNNReal_mono hε)) hfin)

/-- The Dudley integrand is antitone in the scale (same hypothesis). -/
lemma sqrtEntropy_anti {ε₁ ε₂ : ℝ} {s : Set A} (hε : ε₁ ≤ ε₂)
    (hfin : Metric.coveringNumber ε₁.toNNReal s ≠ ⊤) :
    sqrtEntropy ε₂ s ≤ sqrtEntropy ε₁ s :=
  Real.sqrt_le_sqrt (metricEntropy_anti hε hfin)

/-- The Dudley integrand as an extended-nonnegative-real valued function, for the entropy integral. -/
def dudleyIntegrand (ε : ℝ) (s : Set A) : ℝ≥0∞ := ENNReal.ofReal (sqrtEntropy ε s)

/-- The Dudley entropy integral as an extended nonnegative real (always defined, possibly `⊤`). -/
def entropyIntegralENNReal (s : Set A) (D : ℝ) : ℝ≥0∞ :=
  ∫⁻ ε in Set.Ioc 0 D, dudleyIntegrand ε s

/-- **The Dudley entropy integral** `∫₀^D √(log N(ε, s)) dε`. -/
def entropyIntegral (s : Set A) (D : ℝ) : ℝ := (entropyIntegralENNReal s D).toReal

/-- The entropy integral is nonnegative. -/
lemma entropyIntegral_nonneg {s : Set A} {D : ℝ} : 0 ≤ entropyIntegral s D := ENNReal.toReal_nonneg

end TLT.Capacity
