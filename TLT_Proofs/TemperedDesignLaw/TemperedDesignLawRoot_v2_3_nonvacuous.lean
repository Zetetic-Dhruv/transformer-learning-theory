/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.TwoCertificateCrossover
import TLT_Proofs.TemperedDesignLaw.TemperedFloatCone
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Tempered design law root contract

This file contains the root contract for the tempered design law.  It is a
cite-only assembly interface: every field below is a concrete mathematical
obligation that must be supplied by a landed theorem.  The repository-level
zero-sorry / axiom audit is intentionally not represented as a mathematical
`Prop` here; it is recorded by the build/audit JSON.

The root separates three kinds of evidence:

* the capacity profile, with the smooth and hard certificates for the same gap;
* the numerical window, whose cone condition is obtained from the cone-boundary
  theorem in `TemperedFloatCone`;
* the hard-tame mathematical leg, carrying exactness, executable decidability,
  expressivity grading, and statistical certification on the same routed object.

The comparison between the capacity crossover and the numerical ceiling is a
pair of guarded regime theorems.  The constants decide which guard applies.
-/

open MeasureTheory
open TLT.ExpError

noncomputable section

namespace TLT.TemperedDesignLaw

/-- Shared numerical and statistical data for one concrete configuration. -/
structure RegionData where
  /-- Sharpness at which the executable soft model is run. -/
  beta : ℝ
  /-- Crossover sharpness of the smooth and hard certificates. -/
  betaStar : ℝ
  /-- Score-range bound on the clamp ball. -/
  S : ℝ
  hbeta_nonneg : 0 ≤ beta
  hbetaStar_nonneg : 0 ≤ betaStar
  hS_pos : 0 < S

/-- The comfort regime: the capacity-certificate crossover is inside the certified float window. -/
def ComfortRegime (R : RegionData) : Prop :=
  R.betaStar ≤ betaMax R.S

/-- The tension regime: the certified float window ends before the capacity-certificate crossover. -/
def TensionRegime (R : RegionData) : Prop :=
  betaMax R.S < R.betaStar

/-- Classification of the two pinned constants.  This is only a case split over the real constants;
it is not evidence for either guarded conclusion. -/
theorem regime_dichotomy (R : RegionData) : ComfortRegime R ∨ TensionRegime R := by
  by_cases h : R.betaStar ≤ betaMax R.S
  · exact Or.inl h
  · exact Or.inr (not_le.mp h)

/-- Capacity data for the same generalization gap at every sharpness in scope. -/
structure CapacityProfile (R : RegionData) where
  /-- The generalization quantity being bounded at sharpness `β`. -/
  gap : ℝ → ℝ
  /-- Smooth/Dudley certificate. -/
  smoothBound : ℝ → ℝ
  /-- Hard-symbol-plus-leakage certificate. -/
  hardBound : ℝ → ℝ
  smooth_mono : Monotone smoothBound
  hard_anti : Antitone hardBound
  /-- Smooth certificate bounds the same gap on the numerically certified window. -/
  smooth_cert : ∀ β, 0 ≤ β → β ≤ betaMax R.S → gap β ≤ smoothBound β
  /-- Hard certificate bounds the same gap on the same window. -/
  hard_cert : ∀ β, 0 ≤ β → β ≤ betaMax R.S → gap β ≤ hardBound β
  /-- The smooth certificate is the binding side up to the crossover. -/
  smooth_binds_left : ∀ β, 0 ≤ β → β ≤ R.betaStar → smoothBound β ≤ hardBound β
  /-- The hard certificate is the binding side from the crossover onward. -/
  hard_binds_right : ∀ β, R.betaStar ≤ β → hardBound β ≤ smoothBound β
  /-- At the crossover the two certificate formulae agree. -/
  betaStar_crosses : smoothBound R.betaStar = hardBound R.betaStar

/-- Pointwise two-certificate bound. -/
def CapacityProfile.twoCert {R : RegionData} (C : CapacityProfile R) : ℝ → ℝ :=
  twoCertMin C.smoothBound C.hardBound

/-- The two-certificate bound is derived from the two actual certificates. -/
theorem CapacityProfile.bound_at {R : RegionData} (C : CapacityProfile R)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβwin : β ≤ betaMax R.S) :
    C.gap β ≤ C.twoCert β :=
  gap_le_twoCertMin (C.smooth_cert β hβ0 hβwin) (C.hard_cert β hβ0 hβwin)

/-- On the left side of the crossover, the min certificate is the smooth certificate. -/
theorem CapacityProfile.twoCert_eq_smooth_of_left {R : RegionData} (C : CapacityProfile R)
    {β : ℝ} (hβ0 : 0 ≤ β) (hleft : β ≤ R.betaStar) :
    C.twoCert β = C.smoothBound β := by
  exact min_eq_left (C.smooth_binds_left β hβ0 hleft)

/-- On the right side of the crossover, the min certificate is the hard certificate. -/
theorem CapacityProfile.twoCert_eq_hard_of_right {R : RegionData} (C : CapacityProfile R)
    {β : ℝ} (hright : R.betaStar ≤ β) :
    C.twoCert β = C.hardBound β := by
  exact min_eq_right (C.hard_binds_right β hright)

/-- The numerical leg: the run sharpness is inside the certified exponential cone window. -/
structure NumericalLeg (R : RegionData) where
  beta_window : R.beta ≤ betaMax R.S

/-- The cone condition follows from the certified sharpness window and the cone-boundary theorem. -/
theorem NumericalLeg.cone {R : RegionData} (N : NumericalLeg R) :
    rrρ (R.beta * R.S) ≤ 1 / 8 := by
  apply (rrρ_le_iff_le_Tmax).2
  calc
    R.beta * R.S ≤ betaMax R.S * R.S :=
      mul_le_mul_of_nonneg_right N.beta_window R.hS_pos.le
    _ = Tmax := by
      rw [betaMax, div_mul_cancel₀ _ R.hS_pos.ne']

/-- Measurability status of the soft/tame/wild legs, plus the named cost of using the repair. -/
structure MeasurabilityCliffLeg (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  softEvent : Set Ω
  hardTameEvent : Set Ω
  hardWildEvent : Set Ω
  soft_finite_borel : MeasurableSet softEvent
  hard_tame_borel : MeasurableSet hardTameEvent
  hard_wild_nonBorel : ¬ MeasurableSet hardWildEvent
  hard_wild_nullRepair : NullMeasurableSet hardWildEvent μ
  crossingCost : ℝ
  crossingCost_eq_outerMass : crossingCost = μ.real hardWildEvent
  crossingCost_nonneg : 0 ≤ crossingCost

/-- Mathematical hard-tame properties on one routed object.

The repository-level Lean audit is deliberately not a field here.  It belongs in the JSON/build
witness, not inside the object language of the mathematics. -/
structure HardTameMathLeg (X Route : Type*) where
  /-- Hard symbolic route. -/
  hardSymbol : X → Route
  /-- Top-one reading of the finite-sharpness soft cascade. -/
  softTop1 : ℝ → X → Route
  /-- Ideal symbolic exactness for every positive sharpness. -/
  exact_positive_beta : ∀ β, 0 < β → ∀ x, softTop1 β x = hardSymbol x
  /-- Executed route, after finite arithmetic. -/
  executedSymbol : X → Route
  /-- Runtime-checkable certificate for route stability. -/
  routeStableCheck : X → Bool
  /-- Soundness of the runtime checker. -/
  routeStableCheck_sound : ∀ x, routeStableCheck x = true → executedSymbol x = hardSymbol x
  /-- Symbol class realized by the hard-tame cascade (the base grade of the expressivity lattice). -/
  symbolClass : Set (X → Route)
  /-- Expressivity grade indexed by depth `L` and width/expert count `K`: a genuine `(L,K)`
  realizability lattice (cf. `ExpressivityLattice.expressivityGrade`), NOT a constant collapse. -/
  expressivityGrade : ℕ → ℕ → Set (X → Route)
  /-- **Corrected expressivity statement** (NS2/NS3/NS4/TD13).  The shipped field
  `expressivity_graded : ∀ L K, expressivityGrade L K = symbolClass` was a *degenerate collapse*
  (constant in `L,K` — the wrong shape for a capacity ladder; flagged by the closure audit and the
  noological synthesis).  The honest replacement is the genuine **monotone-ladder** shape: the diagonal
  depth ladder is monotone (deeper cascades realize at least as many routes), each width slice is
  monotone (more experts realize at least as many routes), and the base grade `(0,0)` is the symbol
  class.  Inhabited by `ExpressivityLattice.expressivityGrade_monotone_depth` /
  `expressivityGrade_monotone_width` / `expressivityGrade_zero_depth`.  The *strict* separation (proper
  inclusion = genuine expressivity growth) is the open expressivity-lower-bound frontier, not asserted
  here. -/
  expressivity_monotone_depth : Monotone (fun L => expressivityGrade L L)
  expressivity_monotone_width : ∀ L, Monotone (fun K => expressivityGrade L K)
  expressivity_base : expressivityGrade 0 0 = symbolClass
  /-- Statistical quantity for the hard-tame symbolic class. -/
  symbolGap : ℝ
  /-- Hard-tame symbolic statistical certificate. -/
  symbolBound : ℝ
  statistically_certified : symbolGap ≤ symbolBound

/-- The mathematical TD16 certificate.  Lean verification is an external witness in the audit JSON. -/
structure TemperedDesignLawCertificate (R : RegionData)
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (X Route : Type*) where
  capacity : CapacityProfile R
  numerical : NumericalLeg R
  measurability : MeasurabilityCliffLeg Ω μ
  hardTame : HardTameMathLeg X Route

/-- Comfort-regime conclusion.  Here the certificate switch is visible inside the numerical window. -/
structure ComfortConclusion (R : RegionData)
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (X Route : Type*) where
  cert : TemperedDesignLawCertificate R Ω μ X Route
  regime : ComfortRegime R
  betaStar_is_float_certified : R.betaStar ≤ betaMax R.S
  betaStar_bound : cert.capacity.gap R.betaStar ≤ cert.capacity.twoCert R.betaStar
  certified_switch : cert.capacity.twoCert R.betaStar = cert.capacity.smoothBound R.betaStar

/-- Tension-regime conclusion.  Every certified sharpness lies before the certificate switch, so the
executable window sees only the smooth-binding side of the two-certificate profile. -/
structure TensionConclusion (R : RegionData)
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (X Route : Type*) where
  cert : TemperedDesignLawCertificate R Ω μ X Route
  regime : TensionRegime R
  betaStar_not_float_certified : ¬ R.betaStar ≤ betaMax R.S
  all_certified_before_crossover : ∀ β, 0 ≤ β → β ≤ betaMax R.S → β < R.betaStar
  all_certified_bind_smooth : ∀ β, 0 ≤ β → β ≤ betaMax R.S →
    cert.capacity.twoCert β = cert.capacity.smoothBound β

/-- Guarded assembly in the comfort regime. -/
def comfortConclusion_of_certificate {R : RegionData}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Route : Type*}
    (cert : TemperedDesignLawCertificate R Ω μ X Route) (h : ComfortRegime R) :
    ComfortConclusion R Ω μ X Route where
  cert := cert
  regime := h
  betaStar_is_float_certified := h
  betaStar_bound := cert.capacity.bound_at R.hbetaStar_nonneg h
  certified_switch := by
    rw [CapacityProfile.twoCert, twoCertMin, cert.capacity.betaStar_crosses]
    exact min_eq_left le_rfl

/-- Guarded assembly in the tension regime. -/
def tensionConclusion_of_certificate {R : RegionData}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Route : Type*}
    (cert : TemperedDesignLawCertificate R Ω μ X Route) (h : TensionRegime R) :
    TensionConclusion R Ω μ X Route where
  cert := cert
  regime := h
  betaStar_not_float_certified := not_le_of_gt h
  all_certified_before_crossover := by
    intro β _ hβwin
    exact lt_of_le_of_lt hβwin h
  all_certified_bind_smooth := by
    intro β hβ0 hβwin
    exact cert.capacity.twoCert_eq_smooth_of_left hβ0 (le_of_lt (lt_of_le_of_lt hβwin h))

end TLT.TemperedDesignLaw
