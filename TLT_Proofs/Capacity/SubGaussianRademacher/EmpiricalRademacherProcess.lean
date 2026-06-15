/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.Rademacher
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Count

/-!
# The empirical Rademacher process is sub-Gaussian

The empirical Rademacher process at index `θ` is `R_θ(σ) = (1/m)·∑ᵢ g(θ)ᵢ·sign(σᵢ)`, where `σ` is a
uniformly random sign vector and `g(θ)ᵢ` is the value of the `θ`-indexed function at sample `i`. Its
increments are bounded Rademacher sums, hence sub-Gaussian: under the uniform sign measure,
`E[exp(l·(R_θ − R_θ'))] ≤ exp(l²·c²/(2m))` whenever `c` bounds the per-sample increments.

The MGF bound `rademacher_mgf_bound` is integrated against the uniform sign measure and extended to
negative exponents by the sign symmetry of the Rademacher sum.

## Main results

- `radMeasure`: the uniform probability measure on the `2^m` sign vectors.
- `integral_radMeasure`: integration against it is the average over sign vectors.
- `empRad`: the empirical Rademacher average.
- `empRad_increment_mgf_le`: the increment is sub-Gaussian with proxy `1/√m`.

## References

P. L. Bartlett and S. Mendelson, *Rademacher and Gaussian complexities: risk bounds and structural
results*, JMLR 3 (2002); the Rademacher MGF bound is Hoeffding's lemma applied coordinatewise.
-/

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

namespace TLT.Capacity

/-- The uniform probability measure on the `2^m` sign vectors. -/
def radMeasure (m : ℕ) : Measure (SignVector m) :=
  (Fintype.card (SignVector m) : ℝ≥0∞)⁻¹ • Measure.count

instance instIsProbRad (m : ℕ) : IsProbabilityMeasure (radMeasure m) := by
  refine ⟨?_⟩
  rw [radMeasure, Measure.smul_apply, smul_eq_mul, Measure.count_univ,
    ENat.card_eq_coe_fintype_card]
  rw [show ((Fintype.card (SignVector m) : ℕ∞) : ℝ≥0∞)
      = (Fintype.card (SignVector m) : ℝ≥0∞) by simp]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp)

/-- Integration against the uniform sign measure is the average over sign vectors. -/
lemma integral_radMeasure {m : ℕ} (f : SignVector m → ℝ) :
    ∫ σ, f σ ∂(radMeasure m) = (1 / (Fintype.card (SignVector m) : ℝ)) * ∑ σ, f σ := by
  rw [radMeasure, integral_smul_measure, integral_count, smul_eq_mul]
  congr 1
  rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- The empirical Rademacher average for index `θ` with per-sample values `g θ : Fin m → ℝ`. -/
def empRad {A : Type*} {m : ℕ} (g : A → Fin m → ℝ) (θ : A) (σ : SignVector m) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, g θ i * boolToSign (σ i)

/-- **The empirical Rademacher process increment is sub-Gaussian** (proxy `1/√m`): for any bound `c`
on the per-sample increments `|g θ i − g θ' i|`, the increment's MGF under the uniform sign measure is
at most `exp(l²·c²/(2m))`, for every `l`. -/
theorem empRad_increment_mgf_le {A : Type*} {m : ℕ} (hm : 0 < m) (g : A → Fin m → ℝ) (θ θ' : A)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ i, |g θ i - g θ' i| ≤ c) (l : ℝ) :
    ∫ σ, Real.exp (l * (empRad g θ σ - empRad g θ' σ)) ∂(radMeasure m)
      ≤ Real.exp (l ^ 2 * c ^ 2 / (2 * m)) := by
  have hdiff : ∀ σ, empRad g θ σ - empRad g θ' σ =
      (1 / (m : ℝ)) * ∑ i, (g θ i - g θ' i) * boolToSign (σ i) := by
    intro σ
    simp only [empRad, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1; exact Finset.sum_congr rfl fun i _ => by ring
  rw [integral_radMeasure]
  simp only [hdiff]
  by_cases hl : 0 ≤ l
  · exact rademacher_mgf_bound hm (fun i => g θ i - g θ' i) c hc0 hc l hl
  · have hl' : l < 0 := not_le.mp hl
    have hc' : ∀ i, |g θ' i - g θ i| ≤ c := fun i => by rw [abs_sub_comm]; exact hc i
    have hkey := rademacher_mgf_bound hm (fun i => g θ' i - g θ i) c hc0 hc' (-l) (by linarith)
    have harg : ∀ σ : SignVector m,
        Real.exp (-l * ((1 / (m : ℝ)) * ∑ i, (g θ' i - g θ i) * boolToSign (σ i))) =
        Real.exp (l * ((1 / (m : ℝ)) * ∑ i, (g θ i - g θ' i) * boolToSign (σ i))) := by
      intro σ; congr 1
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [harg] at hkey
    rwa [show ((-l) ^ 2 : ℝ) = l ^ 2 by rw [neg_pow, neg_one_sq, one_mul]] at hkey

end TLT.Capacity
