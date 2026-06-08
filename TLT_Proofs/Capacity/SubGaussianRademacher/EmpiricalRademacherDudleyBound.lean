/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Capacity.SubGaussianRademacher.EmpiricalRademacherIsSubGaussian
import SLT.Dudley

/-!
# Dudley's bound on the empirical Rademacher complexity

Applying the chaining theorem `dudley` to the empirical Rademacher process bounds the expected supremum
of the process over a value-vector set `s` (the empirical image of a function class) by the Dudley
entropy integral of `s` in the supremum metric, scaled by `1/√m`:

`E[⨆_{v∈s} (1/m)∑ᵢ vᵢ·sign(σᵢ)] ≤ 12√2 · (1/√m) · entropyIntegral s D`.

This is the route from a covering-number bound on `s` to a bound on the empirical Rademacher
complexity, hence — after symmetrization — to a generalization bound. The measurability, integrability
and continuity hypotheses of `dudley` are discharged here using that the sign-vector space is finite
and the process is linear in its value vector.

## Main results

- `empRad_dudley` — the empirical Rademacher complexity is bounded by the Dudley entropy integral.
-/

/-!
## References
- [16] Dudley entropy integral; [21] Ch. 13; [19] Rademacher side; constant 12√2 + the `dudley`
  theorem are vendored [54] (Thm 3.8).
- Provenance: Vendored-glue (instantiation of vendored `dudley` for the finite sign space; bound
  credited to Zhang–Lee–Liu [54]).
-/

open MeasureTheory Real

noncomputable section

namespace TLT.Capacity

variable {m : ℕ}

/-- Every real function on the finite sign-vector space is measurable. -/
lemma measurable_signVector (f : SignVector m → ℝ) : Measurable f := measurable_of_finite f

/-- Every real function on the finite sign-vector space is integrable against the uniform measure. -/
lemma integrable_radMeasure (f : SignVector m → ℝ) : Integrable f (radMeasure m) := by
  refine Integrable.mono' (integrable_const (Finset.univ.sup' Finset.univ_nonempty fun σ => ‖f σ‖))
    (measurable_signVector f).aestronglyMeasurable (ae_of_all _ fun σ => ?_)
  exact Finset.le_sup' (fun σ => ‖f σ‖) (Finset.mem_univ σ)

/-- **Dudley's bound on the empirical Rademacher complexity.** For a totally bounded value-vector set
`s` containing the zero vector, with finite entropy integral, the expected supremum of the empirical
Rademacher process over `s` is at most `12√2·(1/√m)·entropyIntegral s D`. -/
theorem empRad_dudley (hm : 0 < m) (s : Set (Fin m → ℝ)) (hs : TotallyBounded s)
    {D : ℝ} (hD : 0 < D) (hdiam : Metric.diam s ≤ D) (h0 : (0 : Fin m → ℝ) ∈ s)
    (hfin : entropyIntegralENNReal s D ≠ ⊤) :
    ∫ σ, ⨆ v ∈ s, empRadVec v σ ∂(radMeasure m)
      ≤ (12 * Real.sqrt 2) * (1 / Real.sqrt m) * entropyIntegral s D := by
  refine dudley (by positivity) (empRadVec_isSubGaussianProcess hm) hs hD hdiam 0 h0
    (fun σ => ?_) (fun v => measurable_signVector _) (fun v v' l => integrable_radMeasure _) hfin
    (fun σ => ?_)
  · simp only [empRadVec, empRad, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero]
  · have : Continuous (fun v : Fin m → ℝ => empRadVec v σ) := by
      simp only [empRadVec, empRad]
      exact continuous_const.mul
        (continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const)
    exact this.comp continuous_subtype_val

end TLT.Capacity
