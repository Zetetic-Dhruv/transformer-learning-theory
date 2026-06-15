/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Tame parameter spaces: σ-compactness forces a measurable score range

If the router's parameter space `β` is σ-compact and the score map
`g : β → ℝ` is continuous, then `Set.range g` is measurable. Over any
σ-compact parameter space, the pathology exploited by
`TLT_Proofs.Strictness.NonBorelWitness` cannot arise, because that witness
requires `Set.range g` to be a non-measurable analytic set, which σ-compactness
forbids.

## Note on the Mathlib API

This Mathlib pin (`fde0cc5`) has **no** `IsFsigma` predicate. The proof routes
directly through `IsCompact.measurableSet` (`T2Space`-compact sets are
measurable) on each compact piece of the σ-compact cover supplied by
`isSigmaCompact_range`. The conclusion is identical.
-/

/-!
## References
- [4][6] continuous image of a σ-compact space is Fσ, hence Borel; [7] the dichotomy frame.
-/

namespace TLT.Tame

open Set

/-- **Range reflection (tame half).**

If the parameter space `β` is σ-compact and the score map `g : β → ℝ` is
continuous, then its range is measurable.

This is the contrapositive of the non-Borel witness: the witness needs
`Set.range g` to be a non-measurable analytic set, so it can only live over a
*non*-σ-compact (e.g. Baire `ℕ → ℕ`) parameter space, never over `ℝ^d` or any
σ-compact space. No measurability assumption on `g` beyond continuity is needed;
σ-compactness of the *domain* alone suffices. -/
theorem measurableSet_range_of_continuous_of_sigmaCompactSpace
    {β : Type*} [TopologicalSpace β] [SigmaCompactSpace β]
    {g : β → ℝ} (hg : Continuous g) :
    MeasurableSet (Set.range g) := by
  obtain ⟨K, hKc, hKu⟩ := isSigmaCompact_range hg
  rw [← hKu]
  exact MeasurableSet.iUnion fun n => (hKc n).measurableSet

end TLT.Tame
