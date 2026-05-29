/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Tame.SigmaCompactParam
import TLT_Proofs.Strictness.NonBorelWitness

/-!
# The measurability dichotomy for attention routers (Location)

This file is the leaf of the `P0_settle_debate` pipeline.  It conjoins the two
halves of the measurability question for attention routers into a **single
theorem**, settling the "agent vs. witness" debate:

* **Tame half (the agent's world).** For *any* σ-compact parameter space `β`
  and *any* continuous score map `g : β → ℝ`, the range `Set.range g` is
  measurable (`TLT_Proofs.Tame.SigmaCompactParam`).  Every finite-dimensional
  transformer — every finite product of `ℝ^d` blocks — has a σ-compact
  parameter space, so its routing pathology is *measurability-free*.

* **Wild half (the witness's world).** There nonetheless *exists* a binary
  attention router with continuous scores over a Polish parameter space whose
  induced empirical-process bad event is **not** Borel-measurable
  (`TLT_Proofs.Strictness.NonBorelWitness`).  Such a witness can only be built
  over a *non*-σ-compact (Baire-type) parameter space.

The dichotomy is governed by the single toggle `SigmaCompactSpace β`: its
presence forces measurability; only its absence admits the analytic-non-Borel
pathology.  This is the honest *location* theorem — it pins exactly where the
boundary sits, rather than over-claiming non-measurability for σ-compact
architectures (the error that started the debate).
-/

namespace TLT.Boundary

open MeasureTheory Set
open TLT.Tame TLT.Strictness

/-- **The measurability dichotomy.**  Under the classical existence of an
analytic non-Borel subset of `ℝ`:

1. (tame) every continuous score map over a σ-compact parameter space has a
   measurable range; and
2. (wild) there is a Polish-parametrised binary attention router with jointly
   measurable experts whose empirical-process bad event is not Borel.

The hinge is `SigmaCompactSpace`: present ⟹ no pathology; absent ⟹ witness. -/
theorem attention_measurability_dichotomy
    (hex : ∃ A : Set ℝ, AnalyticSet A ∧ ¬ MeasurableSet A) :
    (∀ (β : Type) [TopologicalSpace β] [SigmaCompactSpace β] (g : β → ℝ),
        Continuous g → MeasurableSet (Set.range g))
    ∧
    (∃ (β : Type) (_hτ : TopologicalSpace β) (_hP : PolishSpace β)
        (_hm : MeasurableSpace β) (_hBor : BorelSpace β)
        (_hStd : StandardBorelSpace β)
        (g : β → ℝ) (hg : Continuous g),
        Measurable (fun p : ℝ × ℝ => pointIndicatorExpert p.1 p.2) ∧
        Measurable (fun p : ℝ × ℝ => zeroExpert p.1 p.2) ∧
        ¬ MeasurableSet (witnessBadEventSet g hg)) := by
  refine ⟨?_, ?_⟩
  · intro β _ _ g hg
    exact measurableSet_range_of_continuous_of_sigmaCompact hg
  · exact attention_architecture_produces_non_borel_bad_event hex

end TLT.Boundary
