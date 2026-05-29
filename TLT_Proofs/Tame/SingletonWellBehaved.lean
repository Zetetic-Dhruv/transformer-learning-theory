/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Tame.SingletonBadEventBorel
import FLT_Proofs.Complexity.Measurability

/-!
# Singleton class is Krapp–Wirth well-behaved at the measurable-target Borel level

The bare `KrappWirthWellBehaved ℝ C` is unsatisfiable: `KrappWirthV` quantifies the
ghost-gap-sup measurability over *all* targets `c`, and for non-measurable `c` the gap is
non-measurable (non-measurable products, Krapp–Wirth Lemma A.10). The correct target is the
measurable-target, bad-event formulation — FLT's `WellBehavedVCMeasTarget`, which carries no
`U` field. This file discharges its **Borel** strengthening for `singletonClassOn A` under
`MeasurableSet A`, generalizing `Tame.singletonBadEvent_measurable` from `m = 1, c = zeroConcept`
to every sample size `m` and every measurable target `c`, via a finite-sample reduction of the
uncountable `∃ h ∈ singletonClassOn A` to the `2m` sample-matching singletons plus the
`zeroConcept` residual.
-/

namespace TLT.Tame

open MeasureTheory Set

variable {m : ℕ}

/-- Each empirical-error term is measurable when the concept family `H` evaluated at the
selected sample coordinates is measurable (and the target `c` is measurable). -/
private lemma empiricalError_family_measurable
    {c : Concept ℝ Bool} (hc : Measurable c)
    {H : ((Fin m → ℝ) × (Fin m → ℝ)) → Concept ℝ Bool}
    {q : ((Fin m → ℝ) × (Fin m → ℝ)) → (Fin m → ℝ)} (hq : Measurable q)
    (hH : ∀ i, Measurable (fun p => (H p) (q p i))) :
    Measurable (fun p => EmpiricalError ℝ Bool (H p)
      (fun i => (q p i, c (q p i))) (zeroOneLoss Bool)) := by
  unfold EmpiricalError
  by_cases hm : m = 0
  · simp only [if_pos hm]; exact measurable_const
  · simp only [if_neg hm]
    refine Measurable.div_const (Finset.measurable_sum Finset.univ (fun i _ => ?_)) _
    simp only [zeroOneLoss]
    exact Measurable.ite
      (measurableSet_eq_fun (hH i) (hc.comp ((measurable_pi_apply i).comp hq)))
      measurable_const measurable_const

/-- The one-sided ghost gap of a measurable concept family is measurable. -/
private lemma oneSidedGhostGap_family_measurable
    {c : Concept ℝ Bool} (hc : Measurable c)
    {H : ((Fin m → ℝ) × (Fin m → ℝ)) → Concept ℝ Bool}
    (hH2 : ∀ i, Measurable (fun p => (H p) (p.2 i)))
    (hH1 : ∀ i, Measurable (fun p => (H p) (p.1 i))) :
    Measurable (fun p => oneSidedGhostGap (H p) c m p) := by
  unfold oneSidedGhostGap
  exact (empiricalError_family_measurable hc measurable_snd hH2).sub
        (empiricalError_family_measurable hc measurable_fst hH1)

/-- Empirical error depends on the hypothesis only through its values on the sample. -/
private lemma empiricalError_congr {c : Concept ℝ Bool}
    {h₁ h₂ : Concept ℝ Bool} {q : Fin m → ℝ}
    (hq : ∀ i, h₁ (q i) = h₂ (q i)) :
    EmpiricalError ℝ Bool h₁ (fun i => (q i, c (q i))) (zeroOneLoss Bool)
  = EmpiricalError ℝ Bool h₂ (fun i => (q i, c (q i))) (zeroOneLoss Bool) := by
  unfold EmpiricalError
  by_cases hm : m = 0
  · simp only [if_pos hm]
  · simp only [if_neg hm]
    exact congrArg (· / (m : ℝ)) (Finset.sum_congr rfl (fun i _ => by rw [hq i]))

/-- The one-sided ghost gap depends on the hypothesis only through its values on the sample. -/
private lemma oneSidedGhostGap_congr {c : Concept ℝ Bool}
    {h₁ h₂ : Concept ℝ Bool} {p : (Fin m → ℝ) × (Fin m → ℝ)}
    (h2 : ∀ i, h₁ (p.2 i) = h₂ (p.2 i)) (h1 : ∀ i, h₁ (p.1 i) = h₂ (p.1 i)) :
    oneSidedGhostGap h₁ c m p = oneSidedGhostGap h₂ c m p := by
  unfold oneSidedGhostGap
  rw [empiricalError_congr h2, empiricalError_congr h1]

/-- Every hypothesis in `singletonClassOn A` is measurable (reuses FLT). -/
instance singletonClassOn_measurableHypotheses (A : Set ℝ) :
    MeasurableHypotheses ℝ (singletonClassOn A) where
  mem_measurable := singletonClassOn_measurable A

/-- A point-indexed singleton concept, evaluated at a measurable point, is measurable. -/
private lemma singletonConcept_eval_measurable
    {β : Type*} [MeasurableSpace β] {a : β → ℝ} {x : β → ℝ}
    (ha : Measurable a) (hx : Measurable x) :
    Measurable (fun p => singletonConcept (a p) (x p)) := by
  unfold singletonConcept
  exact Measurable.ite (measurableSet_eq_fun hx ha) measurable_const measurable_const

/-- **Finite-sample reduction.**  The uncountable `∃ h ∈ singletonClassOn A` collapses to the
`zeroConcept` term plus the `2m` singletons matching a sample coordinate; a singleton on a
value missing every sample agrees with `zeroConcept` on the sample, so its residual is
absorbed by the `zeroConcept` term. -/
private lemma singletonClass_badEvent_eq (A : Set ℝ) (c : Concept ℝ Bool) (ε : ℝ) :
    {p : (Fin m → ℝ) × (Fin m → ℝ) | ∃ h ∈ singletonClassOn A,
        oneSidedGhostGap h c m p ≥ ε / 2}
    = ({p | oneSidedGhostGap zeroConcept c m p ≥ ε / 2}
        ∪ ⋃ j : Fin m, {p | p.1 j ∈ A ∧ oneSidedGhostGap (singletonConcept (p.1 j)) c m p ≥ ε / 2})
      ∪ ⋃ j : Fin m, {p | p.2 j ∈ A ∧ oneSidedGhostGap (singletonConcept (p.2 j)) c m p ≥ ε / 2} := by
  ext p
  simp only [singletonClassOn, Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion]
  constructor
  · rintro ⟨h, hmem, hgap⟩
    rcases hmem with rfl | ⟨a, haA, rfl⟩
    · exact Or.inl (Or.inl hgap)
    · by_cases hs1 : ∃ j, p.1 j = a
      · obtain ⟨j, hj⟩ := hs1
        exact Or.inl (Or.inr ⟨j, by rw [hj]; exact haA, by rw [hj]; exact hgap⟩)
      · by_cases hs2 : ∃ j, p.2 j = a
        · obtain ⟨j, hj⟩ := hs2
          exact Or.inr ⟨j, by rw [hj]; exact haA, by rw [hj]; exact hgap⟩
        · simp only [not_exists] at hs1 hs2
          refine Or.inl (Or.inl ?_)
          rw [oneSidedGhostGap_congr (h₂ := zeroConcept)
            (fun i => by simp only [singletonConcept, zeroConcept, if_neg (hs2 i)])
            (fun i => by simp only [singletonConcept, zeroConcept, if_neg (hs1 i)])] at hgap
          exact hgap
  · rintro ((hgap | ⟨j, hjA, hgap⟩) | ⟨j, hjA, hgap⟩)
    · exact ⟨zeroConcept, Or.inl rfl, hgap⟩
    · exact ⟨singletonConcept (p.1 j), Or.inr ⟨p.1 j, hjA, rfl⟩, hgap⟩
    · exact ⟨singletonConcept (p.2 j), Or.inr ⟨p.2 j, hjA, rfl⟩, hgap⟩

/-- **Measurable-target Borel bad event for the singleton class.**  Over `MeasurableSet A` and
a measurable target `c`, the singleton-class empirical-process bad event is Borel — at *every*
sample size `m` and *every* `ε`.  Generalizes `singletonBadEvent_measurable` (the `m = 1`,
`c = zeroConcept` slice). -/
theorem singletonClass_oneSidedBadEvent_measurable
    {A : Set ℝ} (hA : MeasurableSet A) {c : Concept ℝ Bool} (hc : Measurable c) (ε : ℝ) :
    MeasurableSet {p : (Fin m → ℝ) × (Fin m → ℝ) | ∃ h ∈ singletonClassOn A,
      oneSidedGhostGap h c m p ≥ ε / 2} := by
  rw [singletonClass_badEvent_eq A c ε]
  refine MeasurableSet.union (MeasurableSet.union ?_ (MeasurableSet.iUnion fun j => ?_))
    (MeasurableSet.iUnion fun j => ?_)
  · exact (oneSidedGhostGap_family_measurable (H := fun _ => zeroConcept) hc
      (fun _ => measurable_const) (fun _ => measurable_const)) measurableSet_Ici
  · refine MeasurableSet.inter (((measurable_pi_apply j).comp measurable_fst) hA) ?_
    exact (oneSidedGhostGap_family_measurable (H := fun p => singletonConcept (p.1 j)) hc
      (fun i => singletonConcept_eval_measurable
        ((measurable_pi_apply j).comp measurable_fst) ((measurable_pi_apply i).comp measurable_snd))
      (fun i => singletonConcept_eval_measurable
        ((measurable_pi_apply j).comp measurable_fst) ((measurable_pi_apply i).comp measurable_fst)))
      measurableSet_Ici
  · refine MeasurableSet.inter (((measurable_pi_apply j).comp measurable_snd) hA) ?_
    exact (oneSidedGhostGap_family_measurable (H := fun p => singletonConcept (p.2 j)) hc
      (fun i => singletonConcept_eval_measurable
        ((measurable_pi_apply j).comp measurable_snd) ((measurable_pi_apply i).comp measurable_snd))
      (fun i => singletonConcept_eval_measurable
        ((measurable_pi_apply j).comp measurable_snd) ((measurable_pi_apply i).comp measurable_fst)))
      measurableSet_Ici

/-- **Integration into FLT.**  The singleton class satisfies Krapp–Wirth measurable-target
well-behavedness — discharged here at the strict **Borel** level (`MeasurableSet`), which
implies the `NullMeasurableSet` that `WellBehavedVCMeasTarget` requires. -/
theorem singletonClassOn_wellBehavedVCMeasTarget (A : Set ℝ) (hA : MeasurableSet A) :
    WellBehavedVCMeasTarget ℝ (singletonClassOn A) := by
  intro D _ c hc m ε
  exact (singletonClass_oneSidedBadEvent_measurable hA hc ε).nullMeasurableSet

end TLT.Tame
