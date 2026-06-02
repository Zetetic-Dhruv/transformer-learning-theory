/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Capacity.MetricEntropy
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Finiteness of the Dudley entropy integral

The Dudley entropy integral `∫₀^D √(log N(ε, s)) dε` is finite whenever the square-root entropy is
controlled by an integrable singularity `K·ε^(−1/2)` near zero. For a polynomially covered class —
metric entropy `O(log(1/ε))`, hence `√entropy = O(√(log(1/ε)))` and in particular `O(ε^{−1/2})` —
the exponent `−1/2 > −1` makes the singularity integrable, so the entropy integral does not blow up.

This discharges the finiteness side condition `entropyIntegralENNReal s D ≠ ⊤` that the Dudley
chaining bound carries as a hypothesis.

## Main results

- `entropyIntegralENNReal_ne_top_of_sqrtEntropy_le` — finiteness from a `K·ε^(−1/2)` envelope.
- `entropyIntegralENNReal_ne_top_of_coveringNumber_le` — finiteness from a polynomial covering bound
  `N(ε) ≤ (1 + C/ε)^d`.
-/

open MeasureTheory Set

noncomputable section

namespace TLT.Capacity

variable {A : Type*} [PseudoMetricSpace A]

/-- **Finiteness of the entropy integral.** If the square-root metric entropy is bounded by the
integrable singularity `K·ε^(−1/2)` on `(0, D]`, then the Dudley entropy integral is finite. -/
lemma entropyIntegralENNReal_ne_top_of_sqrtEntropy_le {s : Set A} {K D : ℝ} (hK : 0 ≤ K)
    (hD : 0 < D) (hbound : ∀ ε ∈ Set.Ioc (0 : ℝ) D, sqrtEntropy ε s ≤ K * ε ^ (-(1 / 2) : ℝ)) :
    entropyIntegralENNReal s D ≠ ⊤ := by
  have hrpow : IntegrableOn (fun ε : ℝ => ε ^ (-(1 / 2) : ℝ)) (Ioc 0 D) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff hD).mpr (by norm_num)
  have hint : IntegrableOn (fun ε : ℝ => K * ε ^ (-(1 / 2) : ℝ)) (Ioc 0 D) := hrpow.const_mul K
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc 0 D)] fun ε : ℝ => K * ε ^ (-(1 / 2) : ℝ) :=
    (ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all _ fun ε hε => mul_nonneg hK (Real.rpow_nonneg hε.1.le _))
  have hfin : (∫⁻ ε in Ioc 0 D, ENNReal.ofReal (K * ε ^ (-(1 / 2) : ℝ))) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal hnonneg).mp hint.2
  refine ne_of_lt (lt_of_le_of_lt ?_ hfin)
  rw [entropyIntegralENNReal]
  refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun ε hε => ?_))
  exact ENNReal.ofReal_le_ofReal (hbound ε hε)

/-- **Finiteness from an affine envelope.** If the square-root metric entropy is bounded by a
constant plus the integrable singularity, `c + K·ε^(−1/2)` on `(0, D]`, the Dudley entropy integral
is finite: the constant term is integrable on the finite interval and the singularity is integrable
because `−1/2 > −1`. The constant absorbs, e.g., the `+1` from an `insert 0` and `log 2` factors. -/
lemma entropyIntegralENNReal_ne_top_of_sqrtEntropy_le_affine {s : Set A} {c K D : ℝ}
    (hc : 0 ≤ c) (hK : 0 ≤ K) (hD : 0 < D)
    (hbound : ∀ ε ∈ Set.Ioc (0 : ℝ) D, sqrtEntropy ε s ≤ c + K * ε ^ (-(1 / 2) : ℝ)) :
    entropyIntegralENNReal s D ≠ ⊤ := by
  have hrpow : IntegrableOn (fun ε : ℝ => ε ^ (-(1 / 2) : ℝ)) (Ioc 0 D) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff hD).mpr (by norm_num)
  have hconst : IntegrableOn (fun _ : ℝ => c) (Ioc 0 D) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hint : IntegrableOn (fun ε : ℝ => c + K * ε ^ (-(1 / 2) : ℝ)) (Ioc 0 D) :=
    hconst.add (hrpow.const_mul K)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc 0 D)] fun ε : ℝ => c + K * ε ^ (-(1 / 2) : ℝ) :=
    (ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all _ fun ε hε => add_nonneg hc (mul_nonneg hK (Real.rpow_nonneg hε.1.le _)))
  have hfin : (∫⁻ ε in Ioc 0 D, ENNReal.ofReal (c + K * ε ^ (-(1 / 2) : ℝ))) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal hnonneg).mp hint.2
  refine ne_of_lt (lt_of_le_of_lt ?_ hfin)
  rw [entropyIntegralENNReal]
  refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun ε hε => ?_))
  exact ENNReal.ofReal_le_ofReal (hbound ε hε)

/-- A polynomial covering bound `N(ε) ≤ (1 + C/ε)^d` gives the integrable square-root-entropy
envelope `√(d·C)·ε^(−1/2)`: the metric entropy is `≤ d·log(1 + C/ε) ≤ d·C/ε`, so its square root is
`≤ √(d·C)·ε^(−1/2)`. -/
lemma sqrtEntropy_le_of_coveringNumber_le {s : Set A} {C : ℝ} (hC : 0 ≤ C) {d : ℕ} {ε : ℝ}
    (hε : 0 < ε)
    (hcov : ((Metric.coveringNumber ε.toNNReal s).toNat : ℝ) ≤ (1 + C / ε) ^ d) :
    sqrtEntropy ε s ≤ Real.sqrt (d * C) * ε ^ (-(1 / 2) : ℝ) := by
  have hme : metricEntropy ε s ≤ d * (C / ε) := by
    rw [metricEntropy]
    rcases eq_or_ne (Metric.coveringNumber ε.toNNReal s).toNat 0 with h0 | h0
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; positivity
    · have h1 : (1 : ℝ) ≤ ((Metric.coveringNumber ε.toNNReal s).toNat : ℝ) :=
        Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr h0)
      calc Real.log ((Metric.coveringNumber ε.toNNReal s).toNat : ℝ)
          ≤ Real.log ((1 + C / ε) ^ d) := Real.log_le_log (by linarith) hcov
        _ = d * Real.log (1 + C / ε) := by rw [Real.log_pow]
        _ ≤ d * (C / ε) := by
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
            have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + C / ε by positivity)
            linarith
  rw [sqrtEntropy]
  calc Real.sqrt (metricEntropy ε s)
      ≤ Real.sqrt ((d : ℝ) * (C / ε)) := Real.sqrt_le_sqrt hme
    _ = Real.sqrt (d * C) * ε ^ (-(1 / 2) : ℝ) := by
        rw [show (d : ℝ) * (C / ε) = (d * C) * ε⁻¹ by ring, Real.sqrt_mul (by positivity)]
        congr 1
        rw [Real.sqrt_inv, Real.rpow_neg hε.le, ← Real.sqrt_eq_rpow]

/-- **Finiteness from a polynomial covering bound.** If the covering number of `s` is bounded by
`(1 + C/ε)^d` for every scale in `(0, D]`, the Dudley entropy integral is finite. -/
lemma entropyIntegralENNReal_ne_top_of_coveringNumber_le {s : Set A} {C : ℝ} (hC : 0 ≤ C) {d : ℕ}
    {D : ℝ} (hD : 0 < D)
    (hcov : ∀ ε ∈ Set.Ioc (0 : ℝ) D,
      ((Metric.coveringNumber ε.toNNReal s).toNat : ℝ) ≤ (1 + C / ε) ^ d) :
    entropyIntegralENNReal s D ≠ ⊤ :=
  entropyIntegralENNReal_ne_top_of_sqrtEntropy_le (Real.sqrt_nonneg _) hD
    fun ε hε => sqrtEntropy_le_of_coveringNumber_le hC hε.1 (hcov ε hε)

end TLT.Capacity
