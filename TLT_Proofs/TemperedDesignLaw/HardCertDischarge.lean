/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Routing.SymbolOpcountCapacity

/-!
# The hard generalization arm: per-pair finite-VC and measurability

The hard certificate's statistical bound (`symbolGap ≤ symbolBound`, feeding `CapacityProfile.hard_cert`)
turns the arrangement-VC capacity (`symbolClass_growth_prod`, S3) into a generalization bound for the
symbol channel. This file contributes two structural preconditions to that argument:

* `comparisonClass_vcDim_lt_top`: each per-pair comparison class has **finite** VC dimension (the
  precondition for any VC→generalization theorem), from the Dudley sign-class bound `comparisonClass_vcDim_le`.
* `comparisonConcept_measurable`: each per-pair comparison concept is **measurable**, from the router's
  joint score-measurability field `score_meas` (section measurability + `measurableSet_le`).

## Note: the FLT Bool generalization cone requires a discrete input space
The FLT generalization cone (`vcdim_finite_imp_uc'`, `fundamental_rademacher`, `vcdim_finite_imp_pac`)
requires `hc_meas : ∀ c : Concept X Bool, Measurable c` / `MeasurableConceptClass X C`, i.e. **every**
Bool concept on `X` measurable, which forces an essentially **discrete** `X`. The symbol channel's input
space is general (continuous), so the cone does not apply off-the-shelf. The natural resolution is to route
the generalization through the **finite sample** `Fin m → X` (where all concepts are measurable) via the
growth bound `symbolClass_growth_prod`, or to obtain a weaker-measurability uniform-convergence variant.
The **multiclass combination** (Fin k symbol-route 0-1 gap ≤ ∑ over pairs of per-pair gaps) is a separate
step.
-/

noncomputable section

namespace TLT.TemperedDesignLaw

open TLT.Routing.Capacity

universe u

variable {X : Type u} [MeasurableSpace X] {k : ℕ}

/-- **Per-pair finite VC.** Under the linearity hypothesis, each comparison class has
finite VC dimension (`VCDim X (comparisonClass A i j) ≤ finrank ℝ W < ⊤`), the precondition every
VC→generalization theorem consumes. -/
theorem comparisonClass_vcDim_lt_top (A : FiniteScoreRouterCode X k) (i j : Fin k)
    (W : Submodule ℝ (X → ℝ)) [FiniteDimensional ℝ W]
    (hlin : ∀ ρ : A.Ρ, (fun x => A.score ρ x j - A.score ρ x i) ∈ W) :
    VCDim X (comparisonClass A i j) < ⊤ :=
  lt_of_le_of_lt (comparisonClass_vcDim_le A i j W hlin) (WithTop.coe_lt_top _)

/-- **Per-pair comparison concepts are measurable (A5-2a, the `hmeas_C` input).** Each
`comparisonConcept A ρ i j = (x ↦ decide (score ρ x i ≤ score ρ x j))` is measurable: its `true`-fiber is
`{x | score ρ x i ≤ score ρ x j}`, measurable via the router's joint score-measurability field
`score_meas` (sectioned at `ρ` by `measurable_prodMk_left`) and `measurableSet_le`. This is the
concepts-in-class measurability the finite-sample generalization route consumes (`MeasurableConceptClass`'s
`hmeas_C`); it sidesteps the discrete-`X` obstruction, which is about *all* concepts, not those in the
class. -/
theorem comparisonConcept_measurable (A : FiniteScoreRouterCode X k) (ρ : A.Ρ) (i j : Fin k) :
    Measurable (comparisonConcept A ρ i j) := by
  have hf : Measurable (fun x => A.score ρ x i) := (A.score_meas i).comp measurable_prodMk_left
  have hg : Measurable (fun x => A.score ρ x j) := (A.score_meas j).comp measurable_prodMk_left
  refine measurable_to_bool ?_
  have hpre : comparisonConcept A ρ i j ⁻¹' {true} = {x | A.score ρ x i ≤ A.score ρ x j} := by
    ext x
    simp only [comparisonConcept, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
      decide_eq_true_eq]
  rw [hpre]
  exact measurableSet_le hf hg

end TLT.TemperedDesignLaw
