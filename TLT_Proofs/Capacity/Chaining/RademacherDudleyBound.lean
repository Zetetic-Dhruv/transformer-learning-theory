/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Capacity.Chaining.RademacherSymmetrization
import TLT_Proofs.Capacity.SubGaussianRademacher.EmpiricalRademacherDudleyBound

/-!
# The empirical Rademacher complexity is bounded by the Dudley entropy integral

The empirical Rademacher complexity of a uniformly bounded real function class on a sample `S` is the
expected supremum, over the class, of the signed empirical average. Realising the class as its set of
loss value-vectors `{(g i (S 1), …, g i (S m)) : i}` (with the zero vector adjoined as the anchor the
chaining bound requires), Dudley's chaining theorem bounds that expected supremum by `12√2·(1/√m)`
times the Dudley entropy integral of the value-vector set in the supremum metric.

Together, the in-expectation symmetrization and the chaining bound convert a covering-number control
of the value-vector set into a control of the expected uniform deviation. Total-boundedness, diameter,
and finite entropy of the value-vector set are carried as hypotheses, discharged for a
Lipschitz-parametrised class by a covering-number bound on the parameter ball.

## Main results

- `lossValueSet`: the loss value-vectors realised on `S`, with the zero vector adjoined.
- `empRadComplexity_le_dudley`: the empirical Rademacher complexity is at most the Dudley integral.

## References

R. M. Dudley, *The sizes of compact subsets of Hilbert space and continuity of Gaussian processes*,
J. Funct. Anal. 1 (1967); P. L. Bartlett and S. Mendelson, *Rademacher and Gaussian complexities*,
JMLR 3 (2002).
-/

open MeasureTheory Real

noncomputable section

namespace TLT.Capacity

variable {X : Type*} [MeasurableSpace X] {m : ℕ} {ι : Type*}

/-- The set of loss value-vectors realised by the class `g` on the sample `S`, with the zero vector
adjoined (the anchor required by the Dudley bound). -/
def lossValueSet (g : ι → X → ℝ) (S : Fin m → X) : Set (Fin m → ℝ) :=
  insert 0 (Set.range fun i => fun j => g i (S j))

omit [MeasurableSpace X] in
/-- **The empirical Rademacher complexity is bounded by the Dudley entropy integral.** For a uniformly
bounded class with totally-bounded, finite-entropy value-vector set, the empirical Rademacher
complexity on `S` is at most `12√2·(1/√m)·entropyIntegral (lossValueSet g S) D`. -/
theorem empRadComplexity_le_dudley [Nonempty ι] (hm : 0 < m) (g : ι → X → ℝ) {b : ℝ}
    (hb : ∀ i x, |g i x| ≤ b) (S : Fin m → X) (hs : TotallyBounded (lossValueSet g S))
    {D : ℝ} (hD : 0 < D) (hdiam : Metric.diam (lossValueSet g S) ≤ D)
    (hfin : entropyIntegralENNReal (lossValueSet g S) D ≠ ⊤) :
    empRadComplexity g S ≤ (12 * Real.sqrt 2) * (1 / Real.sqrt m) *
      entropyIntegral (lossValueSet g S) D := by
  have h0 : (0 : Fin m → ℝ) ∈ lossValueSet g S := Set.mem_insert _ _
  have hbdd : ∀ σ, BddAbove ((fun v => empRadVec v σ) '' lossValueSet g S) := by
    intro σ
    refine ⟨max b 0, ?_⟩
    rintro y ⟨v, hv, rfl⟩
    simp only [lossValueSet, Set.mem_insert_iff, Set.mem_range] at hv
    rcases hv with rfl | ⟨i, rfl⟩
    · simp only [empRadVec, empRad, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero]
      exact le_max_right b 0
    · exact le_trans (le_trans (le_abs_self _) (empRadVec_abs_le hm (fun j => hb i (S j)) σ))
        (le_max_left b 0)
  calc empRadComplexity g S
      = ∫ σ, ⨆ i, empRadVec (fun j => g i (S j)) σ ∂(radMeasure m) := rfl
    _ ≤ ∫ σ, ⨆ v : ↥(lossValueSet g S), empRadVec (↑v) σ ∂(radMeasure m) :=
        integral_mono (integrable_radMeasure_of_finite _) (integrable_radMeasure_of_finite _)
          (fun σ => ciSup_le fun i =>
            le_ciSup_set (hbdd σ) (Set.mem_insert_of_mem _ (Set.mem_range_self i)))
    _ = ∫ σ, ⨆ v ∈ lossValueSet g S, empRadVec v σ ∂(radMeasure m) :=
        integral_congr_ae (ae_of_all _ fun σ =>
          (biSup_eq_iSup_subtype_real (f := fun v : Fin m → ℝ => empRadVec v σ) ⟨0, h0⟩
            ⟨0, h0, by simp only [empRadVec, empRad, Pi.zero_apply, zero_mul,
              Finset.sum_const_zero, mul_zero]⟩).symm)
    _ ≤ (12 * Real.sqrt 2) * (1 / Real.sqrt m) * entropyIntegral (lossValueSet g S) D :=
        empRad_dudley hm (lossValueSet g S) hs hD hdiam h0 hfin

end TLT.Capacity
