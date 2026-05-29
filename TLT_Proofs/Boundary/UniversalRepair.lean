/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Boundary.Cascade

/-!
# Universal repair: the cascade bad event is null-measurable at every depth (UniversalRepair)

This file is the *tame-of-the-wild* leaf of the `P4_cascade` pipeline.  Although the
depth-`L` cascade bad event `cascadeBadEvent M L` is non-Borel whenever the base score's
range is non-Borel (`cascadeNonInvariance`), it is **`NullMeasurableSet`** for *every*
finite measure, at *every* routing depth — the non-measurability is "repairable" by passing
to the measure completion.

The mechanism is purely descriptive-set-theoretic and **`h_non_borel`-free**: the bad event
is *analytic* (`planarWitnessEvent_analytic` pulled back through the *continuous* reduction
map of `cascadeReductionInvariant`), and **analytic ⇒ null-measurable** for any finite Borel
measure on a Polish space (FLT `analyticSet_nullMeasurableSet`).  This is the honest upper
bound that pairs with the non-invariance lower bound: the cascade pathology never escapes
`NullMeasurableSet`, so the empirical-process (symmetrization) machinery still runs.

The repair consumes only the **continuity** of the reduction map (surjectivity is unused
here — that is the non-Borel leg's input in `cascadeNonInvariance`), so the single
`cascadeReductionInvariant` object is load-bearing for *both* leaves.

Note `GhostPairs1` is **not** a `UniversallyMeasurableSpace` (it is built on `ℝ`, where that
typeclass provably fails), so the repair is genuinely a per-measure `NullMeasurableSet`
statement quantified over every finite measure, not a domain-level universal-measurability
instance.
-/

open MeasureTheory Set

namespace TLT.Boundary

variable {β : Type} [TopologicalSpace β] [PolishSpace β]
  [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] {width : ℕ}

/-- **Universal repair (the depth-`L` leaf).**  For *every* finite measure on `GhostPairs1`
and *every* routing depth `L`, the cascade empirical-process bad event is
`NullMeasurableSet` — even though it is non-Borel (`cascadeNonInvariance`) once the base
range is non-Borel.  Analyticity alone drives this, so there is **no** `h_non_borel`
hypothesis: the bad event is the preimage of the analytic `planarWitnessEvent` under the
*continuous* reduction map of `cascadeReductionInvariant`, hence analytic, hence
null-measurable (`analyticSet_nullMeasurableSet`) at every depth and against every finite
measure.  Surjectivity of the reduction map is unused — it is the non-Borel leg's input. -/
theorem universalRepair (M : MoECascadeCode β width) (L : ℕ)
    {μ : Measure GhostPairs1} [IsFiniteMeasure μ] :
    NullMeasurableSet (cascadeBadEvent M L) μ := by
  obtain ⟨red_L, hcont, _, heq⟩ := cascadeReductionInvariant M L
  rw [heq]
  exact analyticSet_nullMeasurableSet
    ((planarWitnessEvent_analytic (Set.range M.g)
      (analyticSet_range_of_polishSpace M.g_cont)).preimage hcont)

end TLT.Boundary
