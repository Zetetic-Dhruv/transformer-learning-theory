/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Capacity.RademacherProcess
import SLT.SubGaussian

/-!
# The empirical Rademacher process as a sub-Gaussian process

Indexing the empirical Rademacher average by its value vector `v : Fin m → ℝ`, with the supremum
metric on `Fin m → ℝ`, the process `empRadVec v = (1/m)·∑ᵢ vᵢ·sign(σᵢ)` is a sub-Gaussian process with
proxy `1/√m` (`empRadVec_isSubGaussianProcess`). This is exactly the hypothesis that the chaining
bound `dudley` consumes: given a totally bounded value-vector set (the empirical image of a function
class) with finite entropy integral, the expected supremum of the empirical Rademacher process is
controlled by the Dudley entropy integral of that set in the supremum metric.

## References

R. M. Dudley, *The sizes of compact subsets of Hilbert space and continuity of Gaussian processes*,
J. Funct. Anal. 1 (1967); P. L. Bartlett and S. Mendelson, *Rademacher and Gaussian complexities*,
JMLR 3 (2002).
-/

open MeasureTheory Real

noncomputable section

namespace TLT.Capacity

/-- The empirical Rademacher process indexed by the value vector `v : Fin m → ℝ`. -/
def empRadVec {m : ℕ} (v : Fin m → ℝ) (σ : SignVector m) : ℝ := empRad (fun w => w) v σ

/-- **The empirical Rademacher process is sub-Gaussian** in the supremum metric on value vectors, with
proxy `1/√m`. This is the hypothesis consumed by `dudley`: it turns a covering-number bound on the
value-vector set into a bound on the expected supremum of the empirical Rademacher process. -/
theorem empRadVec_isSubGaussianProcess {m : ℕ} (hm : 0 < m) :
    IsSubGaussianProcess (radMeasure m) (empRadVec (m := m)) (1 / Real.sqrt m) := by
  intro v v' l
  have hc : ∀ i, |v i - v' i| ≤ dist v v' := fun i => by
    rw [← Real.dist_eq]; exact dist_le_pi_dist v v' i
  have hbound := empRad_increment_mgf_le hm (fun w => w) v v' dist_nonneg hc l
  refine hbound.trans_eq ?_
  congr 1
  have hsq : (1 / Real.sqrt m) ^ 2 = 1 / m := by
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  rw [hsq]; ring

end TLT.Capacity
