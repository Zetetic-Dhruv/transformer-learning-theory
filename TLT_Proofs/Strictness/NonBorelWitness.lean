/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import FLT_Proofs.Theorem.BorelAnalyticSeparation
import FLT_Proofs.Complexity.Amalgamation
import TLT_Proofs.Attention.BinaryRouting

-- ℝ instances (ContinuousMul ℝ, ContinuousSub ℝ, T2Space ℝ, MeasurableSpace ℝ,
-- BorelSpace ℝ) come transitively via the Polish/BorelSpace imports above.
-
/-!
# Non-Borel Bad Event in Binary Attention

## Main results

- `pointIndicatorExpert`            : ℝ → Concept ℝ Bool — singleton-indicator family
- `zeroExpert`                      : ℝ → Concept ℝ Bool — constant-false family
- `quadraticCostRouter`             : the witness `BinaryAttentionRouterCode ℝ`
- `witnessBadEventSet`              : the sample-space bad event we prove non-Borel
- `attention_architecture_produces_non_borel_bad_event` : THE HEADLINE THEOREM
-/

open Classical
open MeasureTheory Set

namespace TLT.Strictness

/-! ## Witness experts (parameter-indexed Concept families) -/

/-- The `e₁` argument to `patchEval`: a parameter-indexed family of singleton
point indicators. Definitional alias of FLT's `singletonConcept`. The
analytic-non-Borel obstruction enters through this discrete encoding (per
inquiry URS Inv.1 caveat / KU.3). -/
noncomputable def pointIndicatorExpert : ℝ → Concept ℝ Bool :=
  singletonConcept

/-- The `e₂` argument to `patchEval`: a constant-false expert family. -/
noncomputable def zeroExpert : ℝ → Concept ℝ Bool :=
  fun _ => zeroConcept

/-! ## Witness router

The router with score functions `scoreL ρ x = (x - g ρ)²` and `scoreR ρ x = 0`.
The route fires (returns `true`) iff `(x - g ρ)² ≤ 0`, equivalently `x = g ρ`.

All typeclass requirements are explicit instance arguments on the def — no
inline `letI`/`haveI` per project policy. Caller is responsible for
synthesizing `MeasurableSpace`, `BorelSpace`, `StandardBorelSpace` instances
on `β` from its Polish topology (typically via `borel β`,
`BorelSpace.mk rfl`, and `standardBorel_of_polish`).
-/

/-- The witness `BinaryAttentionRouterCode ℝ` constructed from a continuous
parameterization `g : β → ℝ` of an analytic non-Borel set.

Aliased as `gaussianLikeRouter` per dictionary v3.0 paradigm-alignment naming;
the canonical name `quadraticCostRouter` reflects the W₂-cost / RBF-kernel
reading of the `(x - g ρ)²` score (RT-Dict-2 finding). -/
noncomputable def quadraticCostRouter
    {β : Type}
    [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g) :
    BinaryAttentionRouterCode ℝ where
  Ρ := β
  instMeasΡ := inferInstance
  instStdΡ := inferInstance
  scoreL := fun ρ x => (x - g ρ) ^ 2
  scoreR := fun _ _ => 0
  scoreL_meas := ((continuous_snd.sub (hg.comp continuous_fst)).pow 2).measurable
  scoreR_meas := measurable_const

/-- Back-compat alias per dictionary v3.0. The original name from the inquiry
URS; the canonical name `quadraticCostRouter` is preferred per paradigm
alignment. -/
noncomputable abbrev gaussianLikeRouter
    {β : Type}
    [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g) :
    BinaryAttentionRouterCode ℝ :=
  quadraticCostRouter g hg

/-! ## The bad-event set

A file-scope `def` of the sample-space bad event of the witness class at
target `zeroConcept`, sample size `m = 1`, threshold `1/2`. All typeclass
parameters are explicit on this def; consumers thread them.
-/

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
                         (quadraticCostRouter g hg).route),
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

/-- Continuity of `scoreL` of the witness router. -/
theorem quadraticCostRouter_score_continuous_L
    {β : Type}
    [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g) :
    Continuous
      (fun p : β × ℝ => ((quadraticCostRouter g hg).scoreL p.1 p.2)) :=
  (continuous_snd.sub (hg.comp continuous_fst)).pow 2

/-- Continuity of `scoreR` (constant 0) of the witness router. -/
theorem quadraticCostRouter_score_continuous_R
    {β : Type}
    [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g) :
    Continuous
      (fun p : β × ℝ => ((quadraticCostRouter g hg).scoreR p.1 p.2)) :=
  continuous_const

/-- The witness router fires iff `x = g ρ`. -/
theorem quadraticCostRouter_route_eq
    {β : Type}
    [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g) (ρ : β) (x : ℝ) :
    (quadraticCostRouter g hg).route ρ x = true ↔ x = g ρ := by
  unfold BinaryAttentionRouterCode.route quadraticCostRouter
  by_cases h : (x - g ρ)^2 ≤ 0
  · rw [if_pos h]
    refine ⟨fun _ => sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm h (sq_nonneg _))),
           fun _ => rfl⟩
  · rw [if_neg h]
    refine ⟨fun heq => (Bool.false_ne_true heq).elim, fun heq => ?_⟩
    subst heq
    exfalso
    apply h
    simp

/-- Helper for `patchEval_class_eq_singletonClassOn`: the patchEval of the
witness construction reduces to a nested conditional in (x = g ρ) and (x = θ₁).

This captures the witness's behavior under patchEval in a single equation,
allowing downstream proofs to rewrite the patchEval directly without re-deriving
the route-substitution + if-then-else manipulation. -/
private lemma patchEval_witness_apply
    {β : Type} [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g)
    (θ₁ θ₂ : ℝ) (ρ : β) (x : ℝ) :
    patchEval pointIndicatorExpert zeroExpert
      (quadraticCostRouter g hg).route (θ₁, θ₂, ρ) x =
    (if x = g ρ then (if x = θ₁ then true else false) else false) := by
  unfold patchEval pointIndicatorExpert zeroExpert singletonConcept zeroConcept
  by_cases hx : x = g ρ
  · rw [if_pos hx,
        if_pos ((quadraticCostRouter_route_eq g hg ρ x).mpr hx)]
  · rw [if_neg hx,
        if_neg (fun hroute =>
          hx ((quadraticCostRouter_route_eq g hg ρ x).mp hroute))]

/-! ## The class-equality lemma (KU.1 from inquiry URS)

This is the load-bearing collapse: the parameter-indexed `patchEval` class
of the witness equals FLT's `singletonClassOn (range g)`.

- Forward (⊆): case-split on `θ₁ = g ρ` to show every value of `patchEval` is
  either `singletonConcept (g ρ)` or `zeroConcept`.
- Reverse (⊇): for the `zeroConcept` disjunct, use `range g ≠ ℝ` (because
  `range g` is non-Borel and `ℝ` is Borel) to find `θ₁ ∉ range g`.
-/

/-- The witness `patchEval` class equals `singletonClassOn (range g)`. -/
theorem patchEval_class_eq_singletonClassOn
    {β : Type}
    [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    (g : β → ℝ) (hg : Continuous g)
    (h_non_borel : ¬ MeasurableSet (Set.range g)) :
    Set.range (patchEval pointIndicatorExpert zeroExpert
               (quadraticCostRouter g hg).route)
    = singletonClassOn (Set.range g) := by
  ext h
  simp only [Set.mem_range, singletonClassOn, Set.mem_setOf_eq]
  constructor
  · -- Forward: h ∈ Set.range patchEval → h ∈ singletonClassOn (Set.range g)
    rintro ⟨⟨θ₁, θ₂, ρ⟩, rfl⟩
    by_cases heq : θ₁ = g ρ
    · -- Case θ₁ = g ρ: patchEval value is singletonConcept (g ρ)
      right
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
    · -- Case θ₁ ≠ g ρ: patchEval value is zeroConcept
      left
      funext x
      rw [patchEval_witness_apply g hg θ₁ θ₂ ρ x]
      unfold zeroConcept
      by_cases hx : x = g ρ
      · simp only [if_pos hx]
        rw [if_neg]
        intro hxθ
        exact heq (hx ▸ hxθ.symm)
      · simp only [if_neg hx]
  · -- Reverse: h ∈ singletonClassOn → h ∈ Set.range patchEval
    rintro (rfl | ⟨a, ⟨ρ_a, rfl⟩, rfl⟩)
    · -- h = zeroConcept case: pick θ₁ ∉ range g
      obtain ⟨θ₁, hθ₁⟩ := (Set.ne_univ_iff_exists_notMem (Set.range g)).mp
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
    · -- h = singletonConcept (g ρ_a), g ρ_a ∈ range g case
      -- (note: rfl in rintro substitutes a := g ρ_a)
      refine ⟨(g ρ_a, 0, ρ_a), ?_⟩
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

/-! ## HEADLINE THEOREM

Existence of a non-Borel attention witness.

Polish space `β` and its associated
Borel σ-algebra + StandardBorelSpace come out as data alongside the
continuous parameterization `g`.
-/

/-- HEADLINE: under the classical existence of an analytic non-Borel subset
of ℝ (Souslin 1917, Lusin 1917), there exists a binary
attention router with continuous score functions over a Polish parameter
space, jointly measurable experts, whose induced `patchEval` class produces
a sample-space bad event that is not Borel-measurable.

This refutes the silent Borel-σ-algebra assumption of Krapp–Wirth 2024
(`feedback_no_inline_let_have_file_scope_only.md` round-2 literature
red-team) for the architecturally relevant class of attention constructions. -/
theorem attention_architecture_produces_non_borel_bad_event
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
