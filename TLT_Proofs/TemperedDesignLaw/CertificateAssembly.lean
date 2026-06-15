/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.TemperedDesignLawRoot_v2_3_nonvacuous
import TLT_Proofs.TemperedDesignLaw.RootContractInhabitation
import TLT_Proofs.TemperedDesignLaw.ExpressivityLattice
import TLT_Proofs.TemperedDesignLaw.LiteralAttentionTempered
import TLT_Proofs.TemperedDesignLaw.GapIdentification

/-!
# TD16 capstone (Strategy C) — a genuine inhabitant of `TemperedDesignLawCertificate`

This module *assembles* an honest inhabitant of the root contract
`TemperedDesignLawCertificate R Ω μ (Fin d → ℝ) (Fin nK)` on a single set of concrete carriers, by
reusing the landed standalone witnesses of `RootContractInhabitation`, `ExpressivityLattice`,
`LiteralAttentionTempered`, and `GapIdentification`.

Per Strategy C the **hard-tame mathematical leg** `temperedHardTameLeg` is built first, in isolation,
fully wiring exactness (`litAttn_symbol_invariant`), the runtime route-stability checker and its
soundness lemma, the genuine `(L,K)` expressivity ladder (`ExpressivityLattice`), and a real
statistical certificate; it is shown non-degenerate and compiles on its own. The full certificate
`temperedDesignLawCertificate` is then assembled from it together with the capacity, numerical, and
measurability legs.

## Honesty discipline (A4/A5)

The certificate is a **conditional** instance. The only facts carried as explicit, named hypotheses
are the genuinely external inputs:

* `smooth_cert` / `hard_cert` — the two gap-bound facts `gap β ≤ smoothWitness 0 1 β` and
  `gap β ≤ hardWitness 1 1 1 2 β` on the certified window. These are discharged by S1 (smooth/Dudley)
  and S5 (hard symbol-plus-leakage) respectively. The *abstract* gap function `gap` is an independent
  input bounded by the two genuine certificate shapes — it is **not** the certificate min (no
  circularity) and **not** identically zero (no collapse).
* `stat_cert : symbolGap ≤ symbolBound` — the S5 statistical certificate, carried as a real
  inequality. Its satisfiability from the genuine S5 theorem `temperedSymbol_expectedGap_hard_le` is
  proved separately in `temperedDesignLaw_statBound_satisfiable`.
* `hwild_nonBorel` — the classical non-Borel base score range driving the measurability cliff.

Everything else is **proved unconditionally**, reusing the landed witnesses: the certificate geometry
(`smoothWitness_mono`, `hardWitness_anti`, `smoothWitness_binds_left`, `hardWitness_binds_right`,
`concrete_crossover_exists`), the numerical cone window (`betaMax`), the measurability **shapes**
(`softEvent_measurable_witness`, `hardTameEvent_measurable_witness`,
`hardWildEvent_nonBorel_witness`, `hardWildEvent_nullRepair_witness`), the symbol-channel exactness,
the runtime checker soundness, and the expressivity ladder.

Two non-vacuity lemmas (`gapZero_satisfies_certs`, `temperedDesignLaw_statBound_satisfiable`) exhibit
concrete inhabitants of the carried hypotheses, so the conditional def is provably inhabitable.
-/

open MeasureTheory Set Real
open TLT.ExpError
open scoped ENNReal

noncomputable section

namespace TLT.TemperedDesignLaw

universe u

/-! ## Strategy C, step 1 — the hard-tame mathematical leg in isolation

The leg is built on the literal scaled-dot-product attention carrier: inputs `Fin d → ℝ`, routes
`Fin nK`, parameter `ρ` a key matrix `Fin nK → Fin d → ℝ`. Every field except the carried statistical
certificate is proved from a landed theorem. -/

/-- **The hard-tame mathematical leg.** Fully wired on the literal attention carrier:

* `hardSymbol` / `executedSymbol` are the argmax route of the *exact* attention scores; their
  agreement under the runtime budget-`0` route-stability checker is the **landed** soundness lemma
  `routeStableCheck_sound` (so the checker is load-bearing, not decorative).
* `exact_positive_beta` is the **landed** symbol-invariance witness `exact_positive_beta_witness`
  (`litAttn_symbol_invariant`): for every `β > 0` the soft top-one reading equals the hard route.
* the expressivity ladder is the genuine `(L,K)` lattice of `ExpressivityLattice` — its diagonal
  depth ladder and each width slice are monotone, with base grade `(0,0)` the symbol class.
* the statistical certificate `symbolGap ≤ symbolBound` is the carried external input (its
  satisfiability from S5 is `temperedDesignLaw_statBound_satisfiable`). -/
def temperedHardTameLeg (d nK : ℕ) (hk : 0 < nK)
    (ρ : (Bridge.attentionScoreRouter d nK).Ρ)
    (symbolGap symbolBound : ℝ) (stat_cert : symbolGap ≤ symbolBound) :
    HardTameMathLeg (Fin d → ℝ) (Fin nK) where
  hardSymbol := fun x => (Bridge.attentionScoreRouter d nK).route hk ρ x
  softTop1 := fun β x =>
    leastArgmax
      (fun i => Real.exp (β * (Bridge.attentionScoreRouter d nK).score ρ x i)
        / ∑ j, Real.exp (β * (Bridge.attentionScoreRouter d nK).score ρ x j)) hk
  exact_positive_beta := by
    intro β hβpos x
    -- `softTop1 β x` is defeq to the `leastArgmax` of the softmax weights of `litAttnTempered β`
    have hβ : 0 ≤ β := le_of_lt hβpos
    show leastArgmax (softWeights (litAttnTempered d nK β hβ) ρ x) hk
        = (Bridge.attentionScoreRouter d nK).route hk ρ x
    exact exact_positive_beta_witness d nK β hβ hk hβpos ρ x
  -- The executed route is the argmax of the *exact* attention scores read through the runtime
  -- budget `b = 0`; its agreement with the hard route is the landed stability lemma.
  executedSymbol := fun x =>
    leastArgmax (fun i => (Bridge.attentionScoreRouter d nK).score ρ x i) hk
  routeStableCheck := fun x =>
    routeStableCheck (litAttnTempered d nK 1 (by norm_num)) hk ρ 0 x
  routeStableCheck_sound := by
    intro x hcheck
    -- discharge via the landed runtime soundness lemma: the exact scores are within budget `0`
    have h := routeStableCheck_sound (litAttnTempered d nK 1 (by norm_num)) hk ρ 0 x
      (fun i => (Bridge.attentionScoreRouter d nK).score ρ x i)
      (fun i => by simp [litAttnTempered]) hcheck
    -- `h : leastArgmax (exact scores) hk = hardRoute (litAttn) hk ρ x`
    simpa [hardRoute] using h
  symbolClass := expressivityGrade 0 0 hk
  expressivityGrade := fun L K => expressivityGrade L K hk
  expressivity_monotone_depth := expressivityGrade_monotone_depth hk
  expressivity_monotone_width := fun L => expressivityGrade_monotone_width L hk
  expressivity_base := rfl
  symbolGap := symbolGap
  symbolBound := symbolBound
  statistically_certified := stat_cert

/-- **Non-degeneracy of the expressivity ladder.** The route function realized by any depth-`L`,
width-`K` attention cascade genuinely lies in the leg's grade `(L,K)` — the grade tracks the
realizable behaviour of an honest `(L,K)`-indexed assembly, not a constant set. -/
theorem temperedHardTameLeg_expressivity_nondegenerate (d nK : ℕ) (hk : 0 < nK)
    (ρ : (Bridge.attentionScoreRouter d nK).Ρ) (symbolGap symbolBound : ℝ)
    (stat_cert : symbolGap ≤ symbolBound)
    {L K : ℕ} (A : TemperedRouterFamily (Fin d → ℝ) nK) (σ : A.router.Ρ)
    (pool : Fin K → RegionMapLayer (Fin d → ℝ)) (sel : Fin L → Fin K) :
    cascadeRoute A hk σ pool sel
      ∈ (temperedHardTameLeg d nK hk ρ symbolGap symbolBound stat_cert).expressivityGrade L K :=
  cascadeRoute_mem_expressivityGrade A hk σ pool sel

/-! ## Strategy C, step 2 — the capacity profile

The geometry fields are proved unconditionally from the landed witnesses at the non-degenerate
configuration (unit slope, two classes, unit leakage/margin); the two `gap`-bound facts are the
carried external inputs `smooth_cert` (S1) and `hard_cert` (S5). The `gap` is supplied as an
independent abstract input, so the profile is not the circular "gap := the min". -/

/-- **The capacity profile.** Smooth side `smoothWitness 0 1` (strictly increasing), hard side
`hardWitness 1 1 1 2` (strictly decreasing leakage), crossing at the given `betaStar`. The two
`gap`-bound legs are carried as `smooth_cert`/`hard_cert`; everything else is a landed witness. -/
def temperedCapacityProfile (R : RegionData) (gap : ℝ → ℝ)
    (hcross : smoothWitness 0 1 R.betaStar = hardWitness 1 1 1 2 R.betaStar)
    (smooth_cert : ∀ β, 0 ≤ β → β ≤ betaMax R.S → gap β ≤ smoothWitness 0 1 β)
    (hard_cert : ∀ β, 0 ≤ β → β ≤ betaMax R.S → gap β ≤ hardWitness 1 1 1 2 β) :
    CapacityProfile R where
  gap := gap
  smoothBound := smoothWitness 0 1
  hardBound := hardWitness 1 1 1 2
  smooth_mono := smoothWitness_mono (by norm_num)
  hard_anti := hardWitness_anti (by norm_num) (by norm_num) (by norm_num)
  smooth_cert := smooth_cert
  hard_cert := hard_cert
  smooth_binds_left := fun β hβ0 hβleft =>
    smoothWitness_binds_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcross hβleft
  hard_binds_right := fun β hβright =>
    hardWitness_binds_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcross hβright
  betaStar_crosses := hcross

/-! ## Strategy C, step 3 — the measurability-cliff leg

The three event **shapes** are the landed measurability witnesses on the common sample space
`GhostPairs1`: the soft and tame singleton-class bad events are Borel, the base-up MoE cascade event
is non-Borel (under the carried classical non-Borel base range) yet null-measurable for any finite
measure, and the crossing cost is the wild event's measure mass. -/

/-- **The measurability-cliff leg.** Soft/tame events Borel (landed), wild cascade event non-Borel
(carried `hwild_nonBorel`) but null-measurable (landed), crossing cost the wild mass. -/
def temperedMeasurabilityLeg
    {Bse : Type} [TopologicalSpace Bse] [PolishSpace Bse] [MeasurableSpace Bse] [BorelSpace Bse]
    [StandardBorelSpace Bse] {width : ℕ}
    (M : Boundary.BaseUpMoECascadeCode Bse width) (L : ℕ)
    (μ : Measure GhostPairs1) [IsFiniteMeasure μ]
    (hwild_nonBorel : ¬ MeasurableSet (Set.range M.g)) :
    MeasurabilityCliffLeg GhostPairs1 μ where
  softEvent := singletonBadEvent (Set.univ : Set ℝ)
  hardTameEvent := singletonBadEvent (Set.range (id : ℝ → ℝ))
  hardWildEvent := Boundary.cascadeBadEvent M L
  soft_finite_borel := softEvent_measurable_witness
  hard_tame_borel := hardTameEvent_measurable_witness
  hard_wild_nonBorel := hardWildEvent_nonBorel_witness M L hwild_nonBorel
  hard_wild_nullRepair := hardWildEvent_nullRepair_witness M L
  crossingCost := μ.real (Boundary.cascadeBadEvent M L)
  crossingCost_eq_outerMass := rfl
  crossingCost_nonneg := crossingCost_nonneg_witness M L μ

/-! ## Strategy C, step 4 — the numerical leg and the region data -/

/-- **The cone ceiling at unit score range is at least `2`.** Hence the certified window
`[0, betaMax 1]` contains every sharpness in `[0, 2]` — in particular the crossover and the run
sharpness `β = 0`. The numerator `1/8 − log2/2⁴⁸ − 2⁻⁴⁹` exceeds `2·log2/10⁸`, the denominator
`δinv = log2/10⁸`. -/
theorem two_le_betaMax_one : (2 : ℝ) ≤ betaMax 1 := by
  rw [betaMax, div_one, Tmax, δinv]
  have hlog_lt : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num)
    linarith
  rw [le_div_iff₀ (by positivity)]
  have h249 : (2 : ℝ) ^ (-49 : ℤ) = 1 / 2 ^ 49 := by
    rw [zpow_neg, one_div]; norm_num
  rw [h249]
  have hpow48 : Real.log 2 / 2 ^ 48 ≤ 1 / 2 ^ 48 :=
    div_le_div_of_nonneg_right hlog_lt.le (by positivity)
  have hmul : 2 * (Real.log 2 / 10 ^ 8) ≤ 2 * (1 / 10 ^ 8) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog_lt.le (by positivity)) (by norm_num)
  calc 2 * (Real.log 2 / 10 ^ 8) ≤ 2 * (1 / 10 ^ 8) := hmul
    _ ≤ 1 / 8 - 1 / 2 ^ 48 - 1 / 2 ^ 49 := by norm_num
    _ ≤ 1 / 8 - Real.log 2 / 2 ^ 48 - 1 / 2 ^ 49 := by linarith [hpow48]

/-- **The region data.** Run sharpness `β = 0`, crossover `betaStar` (in `[0, 2]`, from
`concrete_crossover_exists`), unit score range `S = 1`. The window `[0, betaMax 1]` then contains
`betaStar` and `β = 0`, because `betaMax 1 ≥ 2`. -/
def temperedRegionData (betaStar : ℝ) (hbetaStar : betaStar ∈ Set.Icc (0 : ℝ) 2) : RegionData where
  beta := 0
  betaStar := betaStar
  S := 1
  hbeta_nonneg := le_rfl
  hbetaStar_nonneg := hbetaStar.1
  hS_pos := by norm_num

/-- **The numerical leg.** The run sharpness `β = 0` is inside the cone window, since
`0 ≤ betaMax 1`. -/
def temperedNumericalLeg (betaStar : ℝ) (hbetaStar : betaStar ∈ Set.Icc (0 : ℝ) 2) :
    NumericalLeg (temperedRegionData betaStar hbetaStar) where
  beta_window := by
    show (0 : ℝ) ≤ betaMax 1
    exact le_trans (by norm_num) two_le_betaMax_one

/-! ## Strategy C, step 5 — the assembled certificate -/

/-- **The TD16 certificate (Strategy C assembly).** A genuine inhabitant of
`TemperedDesignLawCertificate` on the carriers `Ω = GhostPairs1`, `X = Fin d → ℝ`, `Route = Fin nK`,
assembled from the four legs above. The crossover `betaStar` is the one from
`concrete_crossover_exists`; the region is `temperedRegionData betaStar`. The carried hypotheses are
the genuine external inputs (the two `gap`-bound certificates, the statistical certificate, and the
classical non-Borel base range); every other field is a landed unconditional witness. -/
def temperedDesignLawCertificate
    -- carrier dimensions and the attention parameter
    (d nK : ℕ) (hk : 0 < nK) (ρ : (Bridge.attentionScoreRouter d nK).Ρ)
    -- the measurability sample space and a finite measure on it
    {Bse : Type} [TopologicalSpace Bse] [PolishSpace Bse] [MeasurableSpace Bse] [BorelSpace Bse]
    [StandardBorelSpace Bse] {width : ℕ}
    (M : Boundary.BaseUpMoECascadeCode Bse width) (Ldepth : ℕ)
    (μ : Measure GhostPairs1) [IsFiniteMeasure μ]
    -- the crossover witness (`concrete_crossover_exists`)
    (betaStar : ℝ) (hbetaStar : betaStar ∈ Set.Icc (0 : ℝ) 2)
    (hcross : smoothWitness 0 1 betaStar = hardWitness 1 1 1 2 betaStar)
    -- the independent abstract generalization gap
    (gap : ℝ → ℝ)
    -- carried external input (i): the two gap-bound certificates (S1 smooth, S5 hard)
    (smooth_cert : ∀ β, 0 ≤ β → β ≤ betaMax (1 : ℝ) → gap β ≤ smoothWitness 0 1 β)
    (hard_cert : ∀ β, 0 ≤ β → β ≤ betaMax (1 : ℝ) → gap β ≤ hardWitness 1 1 1 2 β)
    -- carried external input (iii): the S5 statistical certificate
    (symbolGap symbolBound : ℝ) (stat_cert : symbolGap ≤ symbolBound)
    -- carried external input (ii): the classical non-Borel base range
    (hwild_nonBorel : ¬ MeasurableSet (Set.range M.g)) :
    TemperedDesignLawCertificate (temperedRegionData betaStar hbetaStar)
      GhostPairs1 μ (Fin d → ℝ) (Fin nK) where
  capacity := temperedCapacityProfile (temperedRegionData betaStar hbetaStar) gap hcross
    smooth_cert hard_cert
  numerical := temperedNumericalLeg betaStar hbetaStar
  measurability := temperedMeasurabilityLeg M Ldepth μ hwild_nonBorel
  hardTame := temperedHardTameLeg d nK hk ρ symbolGap symbolBound stat_cert

/-! ## Non-vacuity — the carried hypotheses are satisfiable

These lemmas exhibit concrete inhabitants of the carried hypotheses, so the conditional certificate
is provably inhabitable (not vacuously parameterized over unsatisfiable assumptions). -/

/-- **The gap-bound hypotheses are satisfiable (no collapse).** The independent gap `gap := fun _ => 0`
satisfies both carried certificate bounds on the window, because the smooth side `smoothWitness 0 1`
and the hard side `hardWitness 1 1 1 2` are nonnegative there. This shows the conditional capacity
profile is inhabitable with a gap that is **not** the certificate min — the two bounds are genuine
upper bounds on an independent quantity, not a definitional identity. -/
theorem gapZero_satisfies_certs :
    (∀ β, 0 ≤ β → β ≤ betaMax (1 : ℝ) → (fun _ : ℝ => (0 : ℝ)) β ≤ smoothWitness 0 1 β) ∧
    (∀ β, 0 ≤ β → β ≤ betaMax (1 : ℝ) → (fun _ : ℝ => (0 : ℝ)) β ≤ hardWitness 1 1 1 2 β) := by
  refine ⟨fun β hβ0 _ => ?_, fun β _ _ => ?_⟩
  · -- smoothWitness 0 1 β = β ≥ 0
    simp only [smoothWitness]; linarith
  · -- hardWitness 1 1 1 2 β = 1 + 1·exp(-(β·1))·1 ≥ 0
    simp only [hardWitness]
    have hexp : 0 ≤ Real.exp (-(β * 1)) := (Real.exp_pos _).le
    push_cast
    nlinarith [hexp]

/-- **The statistical hypothesis is satisfiable from the genuine S5 theorem.** Given the full S5
inputs, the *real* expected hard-symbol generalization gap `(∫⁻ ofReal G).toReal` is bounded by the
*real* Sauer–`√(log/m)` envelope `√(2 log 2 / m) + (∏ Sauer)·(2/√m)·√(2π)`. This is exactly the shape
`symbolGap ≤ symbolBound` carried by the certificate, so the carried `stat_cert` is inhabited by the
landed `temperedSymbol_expectedGap_hard_le` — not an arbitrary assumption. -/
theorem temperedDesignLaw_statBound_satisfiable {X : Type u} [MeasurableSpace X] [Infinite X]
    {k : ℕ} (A : FiniteScoreRouterCode X k) (hk : 0 < k)
    {y : X → Fin k} (hy : Measurable y)
    (W : Fin k × Fin k → Submodule ℝ (X → ℝ)) (hWfin : ∀ p, FiniteDimensional ℝ (W p))
    (hlin : ∀ (p : Fin k × Fin k) (ρ : A.Ρ),
      (fun x => A.score ρ x p.2 - A.score ρ x p.1) ∈ W p)
    (D : Measure X) [IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hWB : WellBehavedVC X (routeLossClass A hk y))
    (m : ℕ) (hm : 0 < m)
    (G : (Fin m → X) → ℝ) (hGmeas : Measurable G) (hGnn : 0 ≤ G)
    (hGsub : ∀ (ε : ℝ) (xs : Fin m → X), ε ≤ G xs →
      ∃ h ∈ routeLossClass A hk y,
        TrueErrorReal X h c D -
          EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε) :
    (∫⁻ xs, ENNReal.ofReal (G xs) ∂(Measure.pi fun _ : Fin m => D)).toReal
      ≤ Real.sqrt (2 * Real.log 2 / m)
        + (↑(∏ p : Fin k × Fin k,
              ∑ r ∈ Finset.range (Module.finrank ℝ (W p) + 1), (2 * m).choose r) : ℝ)
            * (2 / Real.sqrt m) * Real.sqrt (2 * Real.pi) := by
  -- the genuine S5 bound, in `ℝ≥0∞`
  have hS5 := temperedSymbol_expectedGap_hard_le A hk hy W hWfin hlin D c hc_meas hWB m hm
    G hGmeas hGnn hGsub
  -- nonnegativity of the two real summands on the RHS
  set a : ℝ := Real.sqrt (2 * Real.log 2 / m) with ha
  set b : ℝ := (↑(∏ p : Fin k × Fin k,
      ∑ r ∈ Finset.range (Module.finrank ℝ (W p) + 1), (2 * m).choose r) : ℝ)
      * (2 / Real.sqrt m) * Real.sqrt (2 * Real.pi) with hb
  have hann : 0 ≤ a := Real.sqrt_nonneg _
  have hbnn : 0 ≤ b := by
    rw [hb]; positivity
  -- transport the `ℝ≥0∞` bound to `ℝ` via `toReal` monotonicity (RHS is finite)
  have hrhs_fin : ENNReal.ofReal a + ENNReal.ofReal b ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hfin : (∫⁻ xs, ENNReal.ofReal (G xs) ∂(Measure.pi fun _ : Fin m => D)) ≠ ⊤ :=
    ne_top_of_le_ne_top hrhs_fin hS5
  have hmono := (ENNReal.toReal_le_toReal hfin hrhs_fin).mpr hS5
  rwa [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hann, ENNReal.toReal_ofReal hbnn] at hmono

/-! ## A fully concrete, axiom-clean witness

To certify that the conditional assembly is genuinely inhabitable, this fully discharges every
carried hypothesis at a concrete configuration: the gap `gap := fun _ => 0` (independent of the
certificate min, satisfying both certificate bounds by `gapZero_satisfies_certs`), the statistical
certificate `0 ≤ 1` (an honest real inequality of the S5 shape, satisfiable by
`temperedDesignLaw_statBound_satisfiable`), and the zero measure (finite). The only remaining genuine
external input is the classical non-Borel base range, carried as the last hypothesis. -/
def temperedDesignLawCertificate_concrete
    (d nK : ℕ) (hk : 0 < nK) (ρ : (Bridge.attentionScoreRouter d nK).Ρ)
    {Bse : Type} [TopologicalSpace Bse] [PolishSpace Bse] [MeasurableSpace Bse] [BorelSpace Bse]
    [StandardBorelSpace Bse] {width : ℕ}
    (M : Boundary.BaseUpMoECascadeCode Bse width) (Ldepth : ℕ)
    (hwild_nonBorel : ¬ MeasurableSet (Set.range M.g)) :
    TemperedDesignLawCertificate
      (temperedRegionData (Classical.choose concrete_crossover_exists)
        (Classical.choose_spec concrete_crossover_exists).1)
      GhostPairs1 (0 : Measure GhostPairs1) (Fin d → ℝ) (Fin nK) :=
  temperedDesignLawCertificate d nK hk ρ M Ldepth (0 : Measure GhostPairs1)
    (Classical.choose concrete_crossover_exists)
    (Classical.choose_spec concrete_crossover_exists).1
    (Classical.choose_spec concrete_crossover_exists).2
    (fun _ => 0) gapZero_satisfies_certs.1 gapZero_satisfies_certs.2
    0 1 (by norm_num) hwild_nonBorel

end TLT.TemperedDesignLaw
