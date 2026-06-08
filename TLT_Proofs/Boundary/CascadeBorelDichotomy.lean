/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Boundary.BaseUpMoECascade
import TLT_Proofs.Tame.SingletonBadEventBorel

/-!
# The cascade measurability dichotomy is sharp, at every depth

`cascadeNonInvariance` gives the wild side: when the base score range is non-Borel, the depth-`L`
MoE cascade bad event is analytic-but-not-Borel at every depth. This file supplies the tame side
and the sharp characterization.

Since `cascadeBadEvent M L = singletonBadEvent (Set.range M.g)` at every depth
(`cascadeBadEvent_eq_singletonBadEvent`) and `singletonBadEvent A` is Borel iff `A` is Borel
(`singletonBadEvent_measurableSet_iff`), the cascade bad event is Borel **iff** the base score
range is Borel — uniformly in depth. In particular, over a σ-compact base parameter space the
cascade is well-behaved at every depth.

## Main results

- `cascadeBadEvent_measurableSet_iff` — the depth-`L` cascade bad event is Borel iff `Set.range M.g`
  is Borel, at every depth `L`.
- `cascadeBadEvent_measurable_of_sigmaCompact` — over a σ-compact base, the cascade bad event is
  Borel at every depth.
-/

/-!
## References
- [1][4] descriptive-set-theory mechanism; [4][6] σ-compact continuous image is Borel; builds
  on the cascade collapse + `singletonBadEvent_measurableSet_iff`.
- Provenance: Innovation — the sharp depth-uniform Borel-iff-base-Borel dichotomy (corollary).
-/

namespace TLT.Boundary

open MeasureTheory Set TLT.Tame

variable {β : Type} [TopologicalSpace β] [PolishSpace β]
  [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] {width : ℕ}

/-- **Sharp cascade dichotomy.** The depth-`L` MoE cascade bad event is Borel **iff** the base
score range `Set.range M.g` is Borel — at every depth `L`. The depth-uniform sharpening of the
single-layer `singletonBadEvent_measurableSet_iff`. -/
theorem cascadeBadEvent_measurableSet_iff (M : BaseUpMoECascadeCode β width) (L : ℕ) :
    MeasurableSet (cascadeBadEvent M L) ↔ MeasurableSet (Set.range M.g) := by
  rw [cascadeBadEvent_eq_singletonBadEvent M L]
  exact singletonBadEvent_measurableSet_iff (Set.range M.g)

/-- **Tame cascade, depth-uniform.** Over a σ-compact base parameter space the depth-`L` cascade
bad event is Borel at every depth — the tame counterpart of `cascadeNonInvariance`. -/
theorem cascadeBadEvent_measurable_of_sigmaCompact [SigmaCompactSpace β]
    (M : BaseUpMoECascadeCode β width) (L : ℕ) :
    MeasurableSet (cascadeBadEvent M L) :=
  (cascadeBadEvent_measurableSet_iff M L).mpr
    (measurableSet_range_of_continuous_of_sigmaCompactSpace M.g_cont)

end TLT.Boundary
