/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import FLT_Proofs.Theorem.BorelAnalyticSeparation
import FLT_Proofs.Complexity.Amalgamation
import TLT_Proofs.Routing.MeasurableScoreRouting

-- ℝ instances (ContinuousMul ℝ, ContinuousSub ℝ, T2Space ℝ, MeasurableSpace ℝ,
-- BorelSpace ℝ) come transitively via the Polish/BorelSpace imports above.

/-!
# Non-Borel Bad Event in Binary Attention

The witness is a `FiniteScoreRouterCode ℝ 2` (the binary/2-head case of the library's single
routing primitive): head `0` carries the constant cost `0`, head `1` the quadratic cost
`(x - g ρ)²`. Its Boolean route `quadraticCostRoute` (route to head `0`) fires iff
`(x - g ρ)² ≤ 0`, i.e. `x = g ρ`, recovering the score-comparison decision via
`FiniteScoreRouterCode.route_two_eq_scoreComparison`.

## Main results

- `quadraticCostRouter`            : the witness `FiniteScoreRouterCode ℝ 2`
- `quadraticCostRoute`             : its Boolean route (fires iff `x = g ρ`)
- `witnessBadEventSet`             : the sample-space bad event we prove non-Borel
- `attention_nonBorel_badEvent` : THE HEADLINE THEOREM
-/

/-!
## References
- [1] existence of an analytic non-Borel set; [2][5] analytic ⇒ universally/null-measurable;
  [4] analytic ⇔ continuous image of a Polish space; [7] the Borel-(V) condition refuted for
  attention; [12] the classical CH measurability-failure ancestor; [57] FLT `singletonClassOn`,
  `singletonBadEvent`, `planarWitnessEvent`, `singleton_badEvent_not_measurable`.
-/

open Classical
open MeasureTheory Set

namespace TLT.Strictness

/-! ## Witness experts (parameter-indexed Concept families) -/

/-- The `e₁` argument to `patchEval`: a parameter-indexed family of singleton
point indicators. Definitional alias of FLT's `singletonConcept`. -/
noncomputable def pointIndicatorExpert : ℝ → Concept ℝ Bool :=
  singletonConcept

/-- The `e₂` argument to `patchEval`: a constant-false expert family. -/
noncomputable def zeroExpert : ℝ → Concept ℝ Bool :=
  fun _ => zeroConcept

/-! ## Witness router

A `FiniteScoreRouterCode ℝ 2` with `score ρ x 0 = 0` and `score ρ x 1 = (x - g ρ)²`.
By `route_two_eq_scoreComparison` the argmax route is `0` iff `score 1 ≤ score 0`, i.e. `(x - g ρ)² ≤ 0`,
i.e. `x = g ρ`. The Boolean route `quadraticCostRoute` reads "routed to head `0`".

All typeclass requirements are explicit instance arguments on the def (no inline
`letI`/`haveI` per project policy).
-/

/-- The witness `FiniteScoreRouterCode ℝ 2` from a continuous parameterization `g : β → ℝ`
of an analytic non-Borel set. Head `0` is the constant cost `0`; head `1` is the quadratic
cost `(x - g ρ)²`. -/
noncomputable def quadraticCostRouter
    {β : Type}
    [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g) :
    FiniteScoreRouterCode ℝ 2 where
  Ρ := β
  instMeasΡ := inferInstance
  instStdΡ := inferInstance
  score := fun ρ x i => if i = 0 then 0 else (x - g ρ) ^ 2
  score_meas := fun i => by
    fin_cases i
    · simp only [Fin.zero_eta, ↓reduceIte]; exact measurable_const
    · simpa using (measurable_snd.sub (hg.measurable.comp measurable_fst)).pow_const 2

/-- The Boolean route of the witness: `true` iff the argmax selects head `0`. -/
noncomputable def quadraticCostRoute
    {β : Type}
    [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g) : β → Concept ℝ Bool :=
  fun ρ x => decide ((quadraticCostRouter g hg).route (by norm_num) ρ x = 0)

/-- Back-compat alias per dictionary v3.0. -/
noncomputable abbrev gaussianLikeRouter
    {β : Type}
    [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g) :
    FiniteScoreRouterCode ℝ 2 :=
  quadraticCostRouter g hg

/-! ## The bad-event set -/

/-- The bad event of the witness `patchEval` class at sample size 1, target
`zeroConcept`, threshold `1/2`. The headline theorem proves this set is not
Borel-measurable. -/
noncomputable def witnessBadEventSet
    {β : Type}
    [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g) :
    Set ((Fin 1 → ℝ) × (Fin 1 → ℝ)) :=
  {p | ∃ h ∈ Set.range (patchEval pointIndicatorExpert zeroExpert
                         (quadraticCostRoute g hg)),
    EmpiricalError ℝ Bool h (fun i => (p.2 i, zeroConcept (p.2 i)))
        (zeroOneLoss Bool) -
    EmpiricalError ℝ Bool h (fun i => (p.1 i, zeroConcept (p.1 i)))
        (zeroOneLoss Bool) ≥ (1 : ℝ) / 2}

/-! ## Auxiliary measurability and continuity lemmas -/

/-- The parameter-indexed singleton expert family is jointly measurable. -/
theorem pointIndicatorExpert_measurable :
    Measurable (fun p : ℝ × ℝ => pointIndicatorExpert p.1 p.2) := by
  unfold pointIndicatorExpert singletonConcept
  exact Measurable.piecewise
    (isClosed_eq continuous_snd continuous_fst).measurableSet
    measurable_const measurable_const

/-- The constant-false expert family is jointly measurable. -/
theorem zeroExpert_measurable :
    Measurable (fun p : ℝ × ℝ => zeroExpert p.1 p.2) :=
  measurable_const

/-- Continuity of head `1`'s score `(x - g ρ)²` of the witness router. -/
theorem quadraticCostRouter_score_continuous_L
    {β : Type}
    [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g) :
    Continuous
      (fun p : β × ℝ => ((quadraticCostRouter g hg).score p.1 p.2 1)) := by
  simp only [quadraticCostRouter]
  exact (continuous_snd.sub (hg.comp continuous_fst)).pow 2

/-- Continuity of head `0`'s score (constant `0`) of the witness router. -/
theorem quadraticCostRouter_score_continuous_R
    {β : Type}
    [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g) :
    Continuous
      (fun p : β × ℝ => ((quadraticCostRouter g hg).score p.1 p.2 0)) := by
  simp only [quadraticCostRouter]
  exact continuous_const

/-- The witness Boolean route fires iff `x = g ρ`. -/
theorem quadraticCostRouter_route_eq
    {β : Type}
    [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g) (ρ : β) (x : ℝ) :
    quadraticCostRoute g hg ρ x = true ↔ x = g ρ := by
  have hs0 : (quadraticCostRouter g hg).score ρ x 0 = 0 := rfl
  have hs1 : (quadraticCostRouter g hg).score ρ x 1 = (x - g ρ) ^ 2 := rfl
  unfold quadraticCostRoute
  rw [decide_eq_true_eq, FiniteScoreRouterCode.route_two_eq_scoreComparison, hs0, hs1]
  by_cases h : (x - g ρ) ^ 2 ≤ 0
  · rw [if_pos h]
    exact ⟨fun _ => sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm h (sq_nonneg _))), fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun hc => absurd hc (by decide),
           fun heq => absurd (by rw [heq, sub_self]; norm_num : (x - g ρ) ^ 2 ≤ 0) h⟩

/-- Helper for `patchEval_class_eq_singletonClassOn`: the patchEval of the witness
reduces to a nested conditional in `(x = g ρ)` and `(x = θ₁)`. -/
private lemma patchEval_witness_apply
    {β : Type} [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g)
    (θ₁ θ₂ : ℝ) (ρ : β) (x : ℝ) :
    patchEval pointIndicatorExpert zeroExpert
      (quadraticCostRoute g hg) (θ₁, θ₂, ρ) x =
    (if x = g ρ then (if x = θ₁ then true else false) else false) := by
  unfold patchEval pointIndicatorExpert zeroExpert singletonConcept zeroConcept
  by_cases hx : x = g ρ
  · rw [if_pos hx,
        if_pos ((quadraticCostRouter_route_eq g hg ρ x).mpr hx)]
  · rw [if_neg hx,
        if_neg (fun hroute =>
          hx ((quadraticCostRouter_route_eq g hg ρ x).mp hroute))]

/-! ## The class-equality lemma -/

/-- The witness `patchEval` class equals `singletonClassOn (range g)`. -/
theorem patchEval_class_eq_singletonClassOn
    {β : Type}
    [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g)
    (h_non_borel : ¬ MeasurableSet (Set.range g)) :
    Set.range (patchEval pointIndicatorExpert zeroExpert
               (quadraticCostRoute g hg))
    = singletonClassOn (Set.range g) := by
  ext h
  simp only [Set.mem_range, singletonClassOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨θ₁, θ₂, ρ⟩, rfl⟩
    by_cases heq : θ₁ = g ρ
    · right
      refine ⟨g ρ, ⟨ρ, rfl⟩, ?_⟩
      funext x
      rw [patchEval_witness_apply g hg θ₁ θ₂ ρ x]
      by_cases hx : x = g ρ
      · simp only [if_pos hx, heq]
        unfold singletonConcept
        rw [if_pos hx]
      · simp only [if_neg hx]
        unfold singletonConcept
        rw [if_neg hx]
    · left
      funext x
      rw [patchEval_witness_apply g hg θ₁ θ₂ ρ x]
      unfold zeroConcept
      by_cases hx : x = g ρ
      · simp only [if_pos hx]
        rw [if_neg]
        intro hxθ
        exact heq (hx ▸ hxθ.symm)
      · simp only [if_neg hx]
  · rintro (rfl | ⟨a, ⟨ρ_a, rfl⟩, rfl⟩)
    · obtain ⟨θ₁, hθ₁⟩ := (Set.ne_univ_iff_exists_notMem (Set.range g)).mp
        (fun heq => h_non_borel (heq.symm ▸ MeasurableSet.univ))
      obtain ⟨_, ρ, _⟩ := (@Set.nonempty_iff_ne_empty _ (Set.range g)).mpr
        (fun heq => h_non_borel (heq.symm ▸ MeasurableSet.empty))
      refine ⟨(θ₁, 0, ρ), ?_⟩
      funext x
      rw [patchEval_witness_apply g hg θ₁ 0 ρ x]
      unfold zeroConcept
      by_cases hx : x = g ρ
      · simp only [if_pos hx]
        rw [if_neg]
        intro hxθ
        exact hθ₁ ⟨ρ, hx ▸ hxθ⟩
      · simp only [if_neg hx]
    · refine ⟨(g ρ_a, 0, ρ_a), ?_⟩
      funext x
      rw [patchEval_witness_apply g hg (g ρ_a) 0 ρ_a x]
      unfold singletonConcept
      by_cases hx : x = g ρ_a
      · simp only [if_pos hx]
      · simp only [if_neg hx]

/-! ## Bad-event reduction to FLT's `singletonBadEvent` -/

/-- The witness bad event equals FLT's `singletonBadEvent` on `range g`. -/
theorem witnessBadEventSet_eq_singletonBadEvent
    {β : Type}
    [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g)
    (h_non_borel : ¬ MeasurableSet (Set.range g)) :
    witnessBadEventSet g hg = singletonBadEvent (Set.range g) := by
  unfold witnessBadEventSet singletonBadEvent
  rw [patchEval_class_eq_singletonClassOn g hg h_non_borel]

/-- The witness bad event is not Borel-measurable. -/
theorem witnessBadEventSet_not_measurable
    {β : Type}
    [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g)
    (h_non_borel : ¬ MeasurableSet (Set.range g)) :
    ¬ MeasurableSet (witnessBadEventSet g hg) := by
  rw [witnessBadEventSet_eq_singletonBadEvent g hg h_non_borel]
  exact singleton_badEvent_not_measurable (Set.range g) h_non_borel

/-! ## HEADLINE THEOREM -/

/-- HEADLINE: under the classical existence of an analytic non-Borel subset of ℝ
(Souslin 1917, Lusin 1917), there exists a binary attention router with continuous score
functions over a Polish parameter space, jointly measurable experts, whose induced
`patchEval` class produces a sample-space bad event that is not Borel-measurable.

This refutes the silent Borel-σ-algebra assumption of Krapp–Wirth 2024 for the
architecturally relevant class of attention constructions. -/
theorem attention_nonBorel_badEvent
    (hex : ∃ A : Set ℝ, MeasureTheory.AnalyticSet A ∧ ¬ MeasurableSet A) :
    ∃ (β : Type) (_hτ : TopologicalSpace β) (_hP : PolishSpace β)
      (_hm : MeasurableSpace β) (_hBor : BorelSpace β)
      (_hStd : StandardBorelSpace β)
      (g : β → ℝ) (hg : Continuous g),
      Measurable (fun p : ℝ × ℝ => pointIndicatorExpert p.1 p.2) ∧
      Measurable (fun p : ℝ × ℝ => zeroExpert p.1 p.2) ∧
      ¬ MeasurableSet (witnessBadEventSet g hg) := by
  obtain ⟨A, hA_an, hA_non⟩ := hex
  obtain ⟨β, hτ, hP, g, hg_cont, hg_range⟩ :=
    MeasureTheory.analyticSet_iff_exists_polishSpace_range.mp hA_an
  exact ⟨β, hτ, hP, @borel β hτ,
         @BorelSpace.mk β hτ (@borel β hτ) rfl,
         @standardBorel_of_polish β (@borel β hτ) hτ
           (@BorelSpace.mk β hτ (@borel β hτ) rfl) hP,
         g, hg_cont,
         pointIndicatorExpert_measurable,
         zeroExpert_measurable,
         @witnessBadEventSet_not_measurable β hτ hP (@borel β hτ)
           (@BorelSpace.mk β hτ (@borel β hτ) rfl)
           (@standardBorel_of_polish β (@borel β hτ) hτ
             (@BorelSpace.mk β hτ (@borel β hτ) rfl) hP)
           g hg_cont (hg_range ▸ hA_non)⟩

end TLT.Strictness
