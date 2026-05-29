/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Tame.SigmaCompactParam
import TLT_Proofs.Tame.SingletonBadEventBorel
import TLT_Proofs.Strictness.NonBorelWitness
import TLT_Proofs.Boundary.UniversalRepair

/-!
# The measurability dichotomy for attention routers (Location)

This file is the leaf of the `P0_settle_debate` pipeline.  It conjoins the two
halves of the measurability question for attention routers into a **single
theorem**, settling the "agent vs. witness" debate:

* **Tame half (the agent's world).** For *any* σ-compact parameter space `β`
  and *any* continuous score map `g : β → ℝ`, the range `Set.range g` is
  measurable (`TLT_Proofs.Tame.SigmaCompactParam`) **and** the induced singleton
  empirical-process bad event is Borel (`TLT_Proofs.Tame.SingletonBadEventBorel`).
  Every finite-dimensional transformer — every finite product of `ℝ^d` blocks —
  has a σ-compact parameter space, so its routing pathology is *measurability-free*.

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

This makes precise — and machine-checks — the measurability assumption that
Krapp–Wirth (2024, arXiv:2410.10243) identify as tacit in the Fundamental Theorem of
Statistical Learning (their *well-behavedness*, i.e. measurability of the
uniform-convergence bad event `U⁻¹([0,ε])`): the tame half is exactly where it holds,
the wild half a concrete instance where it fails.  (`hex` is the classical existence of
an analytic non-Borel subset of ℝ — Suslin–Lusin 1917 — assumed, as is standard.)
-/

namespace TLT.Boundary

open MeasureTheory Set
open TLT.Tame TLT.Strictness

/-- **The measurability dichotomy.**  Under the classical existence of an
analytic non-Borel subset of `ℝ`:

1. (tame) every continuous score map over a σ-compact parameter space has a
   measurable range;
2. (wild) there is a Polish-parametrised binary attention router with jointly
   measurable experts whose empirical-process bad event is not Borel; and
3. (depth-graded wild) there is a *genuine* base-up MoE cascade (`witnessCascade` —
   the witness's own quadratic-cost router stacked as real 2-head routing layers)
   whose depth-`L` bad event is, at *every* routing depth, analytic and non-Borel
   yet `NullMeasurableSet` for every finite measure (`cascadeNonInvariance`,
   `universalRepair`).  The wild side made depth-uniform.

The hinge is `SigmaCompactSpace`: present ⟹ no pathology; absent ⟹ witness. -/
theorem attention_measurability_dichotomy
    (hex : ∃ A : Set ℝ, AnalyticSet A ∧ ¬ MeasurableSet A) :
    (∀ (β : Type) [TopologicalSpace β] [SigmaCompactSpace β] (g : β → ℝ),
        Continuous g → MeasurableSet (Set.range g)
          ∧ MeasurableSet (singletonBadEvent (Set.range g)))
    ∧
    (∃ (β : Type) (_hτ : TopologicalSpace β) (_hP : PolishSpace β)
        (_hm : MeasurableSpace β) (_hBor : BorelSpace β)
        (_hStd : StandardBorelSpace β)
        (g : β → ℝ) (hg : Continuous g),
        Measurable (fun p : ℝ × ℝ => pointIndicatorExpert p.1 p.2) ∧
        Measurable (fun p : ℝ × ℝ => zeroExpert p.1 p.2) ∧
        ¬ MeasurableSet (witnessBadEventSet g hg))
    ∧
    (∃ (β : Type) (_hτ : TopologicalSpace β) (_hP : PolishSpace β)
        (_hm : MeasurableSpace β) (_hBor : BorelSpace β)
        (_hStd : StandardBorelSpace β) (_hne : Nonempty β)
        (g : β → ℝ) (hg : Continuous g), ∀ L : ℕ,
        (AnalyticSet (cascadeBadEvent (witnessCascade g hg) L)
          ∧ ¬ MeasurableSet (cascadeBadEvent (witnessCascade g hg) L))
        ∧ ∀ (μ : Measure GhostPairs1) [IsFiniteMeasure μ],
            NullMeasurableSet (cascadeBadEvent (witnessCascade g hg) L) μ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro β _ _ g hg
    exact ⟨measurableSet_range_of_continuous_of_sigmaCompact hg,
      singletonBadEvent_measurable_of_sigmaCompact hg⟩
  · exact attention_architecture_produces_non_borel_bad_event hex
  · obtain ⟨A, hA_an, hA_non⟩ := hex
    obtain ⟨β, hτ, hP, g, hg_cont, hg_range⟩ :=
      MeasureTheory.analyticSet_iff_exists_polishSpace_range.mp hA_an
    obtain ⟨_, ρ, _⟩ := (@Set.nonempty_iff_ne_empty _ (Set.range g)).mpr
      (fun heq => (hg_range ▸ hA_non) (heq.symm ▸ MeasurableSet.empty))
    refine ⟨β, hτ, hP, @borel β hτ,
      @BorelSpace.mk β hτ (@borel β hτ) rfl,
      @standardBorel_of_polish β (@borel β hτ) hτ
        (@BorelSpace.mk β hτ (@borel β hτ) rfl) hP,
      ⟨ρ⟩, g, hg_cont, fun L => ⟨?_, ?_⟩⟩
    · exact @cascadeNonInvariance β hτ hP (@borel β hτ)
        (@BorelSpace.mk β hτ (@borel β hτ) rfl)
        (@standardBorel_of_polish β (@borel β hτ) hτ
          (@BorelSpace.mk β hτ (@borel β hτ) rfl) hP) 2
        (@witnessCascade β hτ hP (@borel β hτ)
          (@BorelSpace.mk β hτ (@borel β hτ) rfl)
          (@standardBorel_of_polish β (@borel β hτ) hτ
            (@BorelSpace.mk β hτ (@borel β hτ) rfl) hP) ⟨ρ⟩ g hg_cont)
        L (hg_range ▸ hA_non)
    · exact fun μ _inst => @universalRepair β hτ hP (@borel β hτ)
        (@BorelSpace.mk β hτ (@borel β hτ) rfl)
        (@standardBorel_of_polish β (@borel β hτ) hτ
          (@BorelSpace.mk β hτ (@borel β hτ) rfl) hP) 2
        (@witnessCascade β hτ hP (@borel β hτ)
          (@BorelSpace.mk β hτ (@borel β hτ) rfl)
          (@standardBorel_of_polish β (@borel β hτ) hτ
            (@BorelSpace.mk β hτ (@borel β hτ) rfl) hP) ⟨ρ⟩ g hg_cont)
        L μ _inst

end TLT.Boundary
