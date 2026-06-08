/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Attention.SoftAttentionWellBehaved
import TLT_Proofs.Strictness.AttentionNonBorelWitness

/-!
# Soft attention is unconditionally well-behaved; hard attention need not be

The measurability behaviour of attention depends on whether routing is soft (softmax-weighted) or
hard (argmax). This file states the separation:

* **soft** — the softmax-weighted attention concept class satisfies `WellBehavedVCMeasTarget` for
  *every* width `d`, head count `nK`, and parameter space (no σ-compactness needed): the softmax
  family is jointly measurable, so `borel_param` applies unconditionally;
* **hard** — there is an argmax attention router with continuous scores over a Polish, non-σ-compact
  parameter space whose empirical-process bad event is *not* Borel (the non-Borel witness).

Softmax thus removes the measurability pathology that argmax routing can exhibit.

## Main result

- `soft_vs_hard_attention_measurabilitySeparation` — the conjunction of the two halves.
-/

/-!
## References
- [27] hard-vs-soft attention (expressivity axis); [7][1][2] measurability axis; builds on the
  soft-well-behaved + hard-non-Borel witness.
- Provenance: Innovation — soft/hard attention separation on the measurability/Borel axis,
  orthogonal to the published expressivity-axis separations.
-/

open MeasureTheory Set TLT.Strictness

namespace TLT.Bridge

/-- **Soft/hard attention measurability separation.** Soft (softmax-weighted) attention is
unconditionally well-behaved, while hard (argmax) attention admits a continuous-score witness over a
Polish parameter space whose bad event is non-Borel. Assumes the classical existence of an analytic
non-Borel subset of `ℝ`. -/
theorem soft_vs_hard_attention_measurabilitySeparation
    (hex : ∃ A : Set ℝ, AnalyticSet A ∧ ¬ MeasurableSet A) :
    (∀ d nK : ℕ, WellBehavedVCMeasTarget (Fin d → ℝ) (Set.range (softAttentionConcept d nK)))
    ∧ (∃ (β : Type) (_hτ : TopologicalSpace β) (_hP : PolishSpace β)
        (_hm : MeasurableSpace β) (_hBor : BorelSpace β) (_hStd : StandardBorelSpace β)
        (g : β → ℝ) (hg : Continuous g),
        Measurable (fun p : ℝ × ℝ => pointIndicatorExpert p.1 p.2) ∧
        Measurable (fun p : ℝ × ℝ => zeroExpert p.1 p.2) ∧
        ¬ MeasurableSet (witnessBadEventSet g hg)) :=
  ⟨fun d nK => softAttention_wellBehaved d nK,
   attention_nonBorel_badEvent hex⟩

end TLT.Bridge
