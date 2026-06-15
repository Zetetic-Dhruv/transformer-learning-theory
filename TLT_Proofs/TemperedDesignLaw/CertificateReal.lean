/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.CertificateAssembly
import FLT_Proofs.Complexity.BorelAnalyticBridge

/-!
# A5-4-real (Strategy A) — the tempered design-law certificate carrying the REAL S5 statistics

`CertificateAssembly.temperedDesignLawCertificate_concrete` discharges the carried statistical leg
with the *placeholder* inequality `0 ≤ 1`. This module replaces that placeholder by the **genuine S5
expected-gap bound** `symbolGap ≤ symbolBound`, where

* `symbolGap := (∫⁻ ofReal G).toReal` is the real expectation of a genuine, non-vacuous single-concept
  positive-part generalization-gap functional `G` (its mean is the **positive part** of the unbiased
  zero-mean single-concept gap, so it is genuinely positive in the presence of sampling variance — it
  is **not** `G := 0`), and
* `symbolBound := √(2 log 2 / m) + (∏ Sauer)·(2/√m)·√(2π)` is the genuine Sauer–`√(log/m)` envelope.

## How the named open problem is avoided (the MeasTarget path)

The landed S5 theorem `temperedSymbol_expectedGap_hard_le` requires `WellBehavedVC X (routeLossClass …)`
— the STRONG NullMeasurable double-sample regularity quantified over *all* concepts `c`. Reducing that
to a continuous carrier is the standing open problem `WellBehavedVC_automatic`
(`FLT_Proofs/Complexity/Measurability.lean`). We do **not** touch it. Instead we mirror the whole S5
gen-gap chain with the **achievable** measurable-target variant `WellBehavedVCMeasTarget` (the same
event, quantified only over *measurable* targets):

* `boolClass_gen_gap_measTarget` mirrors `boolClass_gen_gap` (the only change: the regularity leg is
  applied at the measurable target `c`, `hWB D c hc_meas m ε`; `hc_meas` is already in scope).
* `symbolRoute_gen_gap_growth_measTarget` / `symbolRoute_gen_gap_measTarget` /
  `temperedSymbol_expectedGap_hard_le_measTarget` mirror the route-loss specializations.

The `WellBehavedVCMeasTarget` hypothesis is then **discharged** for the route-loss class via the
Borel-analytic positive bridge `borel_param_wellBehavedVCMeasTarget` (the route-loss concept evaluation
is jointly measurable in `(ρ, x)` — `routeLossConcept_jointMeasurable` — and `A.Ρ` is a standard Borel
space, `X = Fin d → ℝ` is Polish/Borel).

## The concrete carrier (Strategy A — the attention router)

The statistical carrier IS the literal scaled-dot-product attention router `Bridge.attentionScoreRouter`
(coherent with the rest of the certificate). Its score is `⟨x, Kᵢ⟩ = ∑ₗ xₗ·Kᵢₗ`
(`attnScore_eq_sum`), so its score **differences** `x ↦ ⟨x, Kⱼ − Kᵢ⟩` are **linear in `x`**, lying in
the `d`-dimensional span of coordinate functionals `coordSpan d` (`attnScoreDiff_mem_coordSpan`) — the
finite-dimensional `W` needed by the arrangement-VC Sauer product. So Strategy A's coherence target is
met: no fallback linear-score router is required.
-/

open MeasureTheory Set Real Filter Topology
open scoped ENNReal NNReal BigOperators
open Module

noncomputable section

namespace TLT.TemperedDesignLaw

universe u

/-! ## 1. The measurable-target variant of the Bool generalization-gap template

These mirror `boolClass_gen_gap`, `symbolRoute_gen_gap_growth`, `symbolRoute_gen_gap`, and
`temperedSymbol_expectedGap_hard_le` verbatim, with the single change that the NullMeasurable
double-sample regularity leg is the **measurable-target** predicate `WellBehavedVCMeasTarget`, applied
at the (measurable) target `c`. The landed theorems are NOT modified. -/

variable {X : Type u} [MeasurableSpace X] {k : ℕ}

/-- **`boolClass_gen_gap`, measurable-target variant.** Identical to `boolClass_gen_gap` except the
regularity leg is `WellBehavedVCMeasTarget`, applied at the measurable target `c` (`hWB D c hc_meas m
ε`). The symmetrization step and double-sample bound use only measurability of the concepts and the
target, so the proof is otherwise the landed one verbatim. -/
theorem boolClass_gen_gap_measTarget [Infinite X]
    (C : ConceptClass X Bool) (hmeas_C : ∀ h ∈ C, Measurable h)
    (D : Measure X) [IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hWB : WellBehavedVCMeasTarget X C)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hm_large : 2 * Real.log 2 ≤ ↑m * ε ^ 2) :
    Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | ∃ h ∈ C,
        TrueErrorReal X h c D -
          EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε}
      ≤ ENNReal.ofReal
          (2 * (↑(GrowthFunction X C (2 * m)) * Real.exp (-(↑m * ε ^ 2 / 8)))) := by
  -- the ONLY change vs `boolClass_gen_gap`: apply the regularity leg at the measurable target `c`.
  have hE_nullmeas := hWB D c hc_meas m ε
  have h_symm := symmetrization_step D C c hmeas_C hc_meas m hm ε hε hm_large
  have h_dbl := double_sample_pattern_bound D C c hmeas_C hc_meas m hm ε hε hE_nullmeas
  calc Measure.pi (fun _ : Fin m => D)
        {xs : Fin m → X | ∃ h ∈ C,
          TrueErrorReal X h c D -
            EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε}
      ≤ 2 * (Measure.pi (fun _ : Fin m => D)).prod (Measure.pi (fun _ : Fin m => D))
          {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
            EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
            EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2} :=
        h_symm
    _ ≤ 2 * ENNReal.ofReal (↑(GrowthFunction X C (2 * m)) * Real.exp (-(↑m * ε ^ 2 / 8))) :=
        mul_le_mul_right h_dbl 2
    _ = ENNReal.ofReal (2 * (↑(GrowthFunction X C (2 * m)) * Real.exp (-(↑m * ε ^ 2 / 8)))) := by
        have h2 : (2 : ENNReal) = ENNReal.ofReal 2 := by rw [ENNReal.ofReal_ofNat]
        rw [h2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]

/-! ## 2. The route-loss class is `WellBehavedVCMeasTarget` (Borel-analytic positive bridge) -/

/-- **The route-loss concept evaluation is JOINTLY measurable in `(ρ, x)`.** Its `true`-fiber is the
preimage of the (discrete, measurable) off-diagonal `{q | q.1 ≠ q.2}` under the jointly measurable map
`(ρ, x) ↦ (route ρ x, y x)` — `route_measurable` (joint `Ρ × X`) paired with `y ∘ snd`. This is the
joint strengthening of the sectioned `routeLossConcept_measurable`. -/
theorem routeLossConcept_jointMeasurable (A : FiniteScoreRouterCode X k) (hk : 0 < k)
    {y : X → Fin k} (hy : Measurable y) :
    Measurable (fun p : A.Ρ × X => routeLossConcept A hk p.1 y p.2) := by
  have hroute : Measurable (fun p : A.Ρ × X => A.route hk p.1 p.2) := A.route_measurable hk
  have hy' : Measurable (fun p : A.Ρ × X => y p.2) := hy.comp measurable_snd
  have hpair : Measurable (fun p : A.Ρ × X => (A.route hk p.1 p.2, y p.2)) := hroute.prodMk hy'
  refine measurable_to_bool ?_
  have hpre : (fun p : A.Ρ × X => routeLossConcept A hk p.1 y p.2) ⁻¹' {true} =
      (fun p : A.Ρ × X => (A.route hk p.1 p.2, y p.2)) ⁻¹' {q : Fin k × Fin k | q.1 ≠ q.2} := by
    ext p
    simp only [routeLossConcept, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
      decide_eq_true_eq]
  rw [hpre]
  exact hpair MeasurableSet.of_discrete

/-- **The route-loss class satisfies `WellBehavedVCMeasTarget`.** The route-loss class is by definition
`Set.range (fun ρ => routeLossConcept A hk ρ y)`, a Borel-parameterized class (parameter space `A.Ρ` is
standard Borel; the evaluation is jointly measurable by `routeLossConcept_jointMeasurable`). The
Borel-analytic positive bridge `borel_param_wellBehavedVCMeasTarget` then yields the measurable-target
NullMeasurable regularity. This DISCHARGES the regularity hypothesis without touching the open strong
`WellBehavedVC`. -/
theorem routeLossClass_wellBehavedVCMeasTarget [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    (A : FiniteScoreRouterCode X k) (hk : 0 < k) {y : X → Fin k} (hy : Measurable y) :
    WellBehavedVCMeasTarget X (routeLossClass A hk y) :=
  borel_param_wellBehavedVCMeasTarget (fun ρ => routeLossConcept A hk ρ y)
    (routeLossConcept_jointMeasurable A hk hy)

/-! ## 3. The route-loss gen-gap chain, measurable-target variants -/

/-- **`symbolRoute_gen_gap_growth`, measurable-target variant.** `boolClass_gen_gap_measTarget` applied
to the route-loss class (measurability of its concepts via `routeLossConcept_measurable`). -/
theorem symbolRoute_gen_gap_growth_measTarget [Infinite X]
    (A : FiniteScoreRouterCode X k) (hk : 0 < k)
    {y : X → Fin k} (hy : Measurable y)
    (D : Measure X) [IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hWB : WellBehavedVCMeasTarget X (routeLossClass A hk y))
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hm_large : 2 * Real.log 2 ≤ ↑m * ε ^ 2) :
    Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | ∃ h ∈ routeLossClass A hk y,
        TrueErrorReal X h c D -
          EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε}
      ≤ ENNReal.ofReal
          (2 * (↑(GrowthFunction X (routeLossClass A hk y) (2 * m)) *
            Real.exp (-(↑m * ε ^ 2 / 8)))) := by
  have hmeas_C : ∀ h ∈ routeLossClass A hk y, Measurable h := by
    rintro h ⟨ρ, rfl⟩
    exact routeLossConcept_measurable A hk ρ hy
  exact boolClass_gen_gap_measTarget (routeLossClass A hk y) hmeas_C D c hc_meas hWB m hm ε hε hm_large

/-- **`symbolRoute_gen_gap`, measurable-target variant.** The growth function is replaced by the
arrangement Sauer–Shelah product via `routeLossClass_growthFunction_le` (the crux), exactly as in the
landed `symbolRoute_gen_gap`. -/
theorem symbolRoute_gen_gap_measTarget [Infinite X]
    (A : FiniteScoreRouterCode X k) (hk : 0 < k)
    {y : X → Fin k} (hy : Measurable y)
    (W : Fin k × Fin k → Submodule ℝ (X → ℝ)) (hWfin : ∀ p, FiniteDimensional ℝ (W p))
    (hlin : ∀ (p : Fin k × Fin k) (ρ : A.Ρ), (fun x => A.score ρ x p.2 - A.score ρ x p.1) ∈ W p)
    (D : Measure X) [IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hWB : WellBehavedVCMeasTarget X (routeLossClass A hk y))
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hm_large : 2 * Real.log 2 ≤ ↑m * ε ^ 2) :
    Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | ∃ h ∈ routeLossClass A hk y,
        TrueErrorReal X h c D -
          EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε}
      ≤ ENNReal.ofReal
          (2 * (↑(∏ p : Fin k × Fin k,
              ∑ r ∈ Finset.range (finrank ℝ (W p) + 1), (2 * m).choose r) *
            Real.exp (-(↑m * ε ^ 2 / 8)))) := by
  refine le_trans
    (symbolRoute_gen_gap_growth_measTarget A hk hy D c hc_meas hWB m hm ε hε hm_large) ?_
  apply ENNReal.ofReal_le_ofReal
  have hGF : GrowthFunction X (routeLossClass A hk y) (2 * m) ≤
      ∏ p : Fin k × Fin k, ∑ r ∈ Finset.range (finrank ℝ (W p) + 1), (2 * m).choose r :=
    routeLossClass_growthFunction_le A hk y W hWfin hlin m
  have hGFr : (↑(GrowthFunction X (routeLossClass A hk y) (2 * m)) : ℝ) ≤
      ↑(∏ p : Fin k × Fin k, ∑ r ∈ Finset.range (finrank ℝ (W p) + 1), (2 * m).choose r) := by
    exact_mod_cast hGF
  have hexp_nonneg : 0 ≤ Real.exp (-(↑m * ε ^ 2 / 8)) := (Real.exp_pos _).le
  nlinarith [mul_le_mul_of_nonneg_right hGFr hexp_nonneg]

/-- **`temperedSymbol_expectedGap_hard_le`, measurable-target variant.** The route's EXPECTED hard
generalization gap `∫⁻ ofReal G` is bounded by the Sauer–`√(log/m)` envelope. Identical to the landed
`temperedSymbol_expectedGap_hard_le`, with the tail input supplied by `symbolRoute_gen_gap_measTarget`
and the regularity carried as `WellBehavedVCMeasTarget`. -/
theorem temperedSymbol_expectedGap_hard_le_measTarget [Infinite X]
    (A : FiniteScoreRouterCode X k) (hk : 0 < k)
    {y : X → Fin k} (hy : Measurable y)
    (W : Fin k × Fin k → Submodule ℝ (X → ℝ)) (hWfin : ∀ p, FiniteDimensional ℝ (W p))
    (hlin : ∀ (p : Fin k × Fin k) (ρ : A.Ρ),
      (fun x => A.score ρ x p.2 - A.score ρ x p.1) ∈ W p)
    (D : Measure X) [IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hWB : WellBehavedVCMeasTarget X (routeLossClass A hk y))
    (m : ℕ) (hm : 0 < m)
    (G : (Fin m → X) → ℝ) (hGmeas : Measurable G) (hGnn : 0 ≤ G)
    (hGsub : ∀ (ε : ℝ) (xs : Fin m → X), ε ≤ G xs →
      ∃ h ∈ routeLossClass A hk y,
        TrueErrorReal X h c D -
          EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε) :
    (∫⁻ xs, ENNReal.ofReal (G xs) ∂(Measure.pi fun _ : Fin m => D))
      ≤ ENNReal.ofReal (Real.sqrt (2 * Real.log 2 / m))
        + ENNReal.ofReal
            ((↑(∏ p : Fin k × Fin k,
                ∑ r ∈ Finset.range (finrank ℝ (W p) + 1), (2 * m).choose r) : ℝ)
              * (2 / Real.sqrt m) * Real.sqrt (2 * Real.pi)) := by
  set μ : Measure (Fin m → X) := Measure.pi fun _ : Fin m => D with hμ
  set C : ℝ := (↑(∏ p : Fin k × Fin k,
      ∑ r ∈ Finset.range (finrank ℝ (W p) + 1), (2 * m).choose r) : ℝ) with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set ε₀ : ℝ := Real.sqrt (2 * Real.log 2 / m) with hε₀def
  have hε₀nn : 0 ≤ ε₀ := Real.sqrt_nonneg _
  have htail : ∀ ε : ℝ, ε₀ < ε →
      μ {xs | ε ≤ G xs}
        ≤ ENNReal.ofReal (2 * C * Real.exp (-((m : ℝ) * ε ^ 2 / 8))) := by
    intro ε hε
    have hεpos : 0 < ε := lt_of_le_of_lt hε₀nn hε
    have hlarge : 2 * Real.log 2 ≤ (m : ℝ) * ε ^ 2 := by
      have hlog2 : 0 ≤ 2 * Real.log 2 := by
        have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
      have hε₀sq : ε₀ ^ 2 = 2 * Real.log 2 / m := by
        rw [hε₀def, Real.sq_sqrt (by positivity)]
      have hmono : ε₀ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ hε₀nn hε.le 2
      have : 2 * Real.log 2 / m ≤ ε ^ 2 := by rw [← hε₀sq]; exact hmono
      calc 2 * Real.log 2 = (2 * Real.log 2 / m) * m := by field_simp
        _ ≤ ε ^ 2 * m := by exact mul_le_mul_of_nonneg_right this hmr.le
        _ = (m : ℝ) * ε ^ 2 := by ring
    have hsubset : {xs : Fin m → X | ε ≤ G xs} ⊆
        {xs : Fin m → X | ∃ h ∈ routeLossClass A hk y,
          TrueErrorReal X h c D -
            EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε} := by
      intro xs hxs; exact hGsub ε xs hxs
    calc μ {xs | ε ≤ G xs}
        ≤ μ {xs : Fin m → X | ∃ h ∈ routeLossClass A hk y,
            TrueErrorReal X h c D -
              EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε} :=
          measure_mono hsubset
      _ ≤ ENNReal.ofReal (2 * (C * Real.exp (-((m : ℝ) * ε ^ 2 / 8)))) :=
          symbolRoute_gen_gap_measTarget A hk hy W hWfin hlin D c hc_meas hWB m hm ε hεpos hlarge
      _ = ENNReal.ofReal (2 * C * Real.exp (-((m : ℝ) * ε ^ 2 / 8))) := by rw [mul_assoc]
  have := truncated_tail_lintegral_le hGmeas hGnn hCnn hm hε₀nn htail
  rw [hμ]
  convert this using 2

/-! ## 4. The finite-dimensional `W` for the attention score differences (Strategy A — linear) -/

/-- The `d`-dimensional span of the coordinate functionals on `Fin d → ℝ`. The attention score
differences live here, since `⟨x, Kⱼ − Kᵢ⟩` is linear in `x`. -/
def coordSpan (d : ℕ) : Submodule ℝ ((Fin d → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range (fun l : Fin d => (fun x : Fin d → ℝ => x l)))

instance coordSpan_finiteDim (d : ℕ) : FiniteDimensional ℝ (coordSpan d) := by
  unfold coordSpan
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- **The literal attention score is the coordinate inner product.**
`(attentionScoreRouter d nK).score K x i = ∑ₗ xₗ·Kᵢₗ`. -/
theorem attnScore_eq_sum (d nK : ℕ) (K : Fin nK → Fin d → ℝ) (x : Fin d → ℝ) (i : Fin nK) :
    (Bridge.attentionScoreRouter d nK).score K x i = ∑ l, x l * K i l := by
  unfold Bridge.attentionScoreRouter
  simp only
  rw [Spec.dot_vec_eq_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [Spec.toVec, Spec.Tensor.dimScalarEquiv, Spec.Tensor.ofScalar]

/-- **The attention score differences are linear in `x` (Strategy A).** For every key matrix `K` and
ordered pair `(i, j)`, the score difference `x ↦ ⟨x, Kⱼ⟩ − ⟨x, Kᵢ⟩ = ∑ₗ xₗ(Kⱼₗ − Kᵢₗ)` lies in the
finite-dimensional `coordSpan d`. So the attention router IS a valid linear-score carrier for the
arrangement-VC Sauer product — no fallback router is needed. -/
theorem attnScoreDiff_mem_coordSpan (d nK : ℕ) (p : Fin nK × Fin nK)
    (K : (Bridge.attentionScoreRouter d nK).Ρ) :
    (fun x => (Bridge.attentionScoreRouter d nK).score K x p.2
      - (Bridge.attentionScoreRouter d nK).score K x p.1) ∈ coordSpan d := by
  have heq : (fun x : Fin d → ℝ => (Bridge.attentionScoreRouter d nK).score K x p.2
      - (Bridge.attentionScoreRouter d nK).score K x p.1)
      = ∑ l : Fin d, (K p.2 l - K p.1 l) • (fun x : Fin d → ℝ => x l) := by
    funext x
    rw [attnScore_eq_sum, attnScore_eq_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [heq, coordSpan]
  refine Submodule.sum_mem _ (fun l _ => ?_)
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self l))

/-! ## 5. The non-vacuous single-concept gap functional `G` and its three properties -/

/-- **Empirical error is measurable in the sample.** Each summand
`xs ↦ zeroOneLoss (h₀ (xsᵢ)) (c (xsᵢ))` is a discrete (`Bool × Bool`) function of the measurable pair
`(h₀ (xsᵢ), c (xsᵢ))`, hence measurable; the average is measurable. -/
theorem empiricalError_measurable_in_sample
    (h0 c : Concept X Bool) (hh0 : Measurable h0) (hc : Measurable c) (m : ℕ) :
    Measurable (fun xs : Fin m → X =>
      EmpiricalError X Bool h0 (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)) := by
  unfold EmpiricalError
  by_cases hm : m = 0
  · subst hm; simp
  · simp only [hm, if_false]
    apply Measurable.div_const
    refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
    have hxi : Measurable (fun xs : Fin m → X => xs i) := measurable_pi_apply i
    have hpair : Measurable (fun xs : Fin m → X => (h0 (xs i), c (xs i))) :=
      (hh0.comp hxi).prodMk (hc.comp hxi)
    exact (Measurable.of_discrete (f := fun q : Bool × Bool => zeroOneLoss Bool q.1 q.2)).comp hpair

omit [MeasurableSpace X] in
/-- The empirical error of a concept against ITSELF is `0` (every sample point agrees). -/
theorem empiricalError_self_zero (c : Concept X Bool) {m : ℕ} (xs : Fin m → X) :
    EmpiricalError X Bool c (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) = 0 := by
  unfold EmpiricalError
  by_cases hm : m = 0
  · simp [hm]
  · simp only [hm, if_false]
    have hz : (Finset.univ.sum fun i => zeroOneLoss Bool (c (xs i)) (c (xs i))) = 0 :=
      Finset.sum_eq_zero (fun i _ => by simp [zeroOneLoss])
    rw [hz]; simp

/-- The true error of a concept against ITSELF is `0` (the disagreement set is empty). -/
theorem trueErrorReal_self_zero (c : Concept X Bool) (D : Measure X) :
    TrueErrorReal X c c D = 0 := by
  unfold TrueErrorReal TrueError
  have hempty : {x | c x ≠ c x} = (∅ : Set X) := by ext x; simp
  rw [hempty]; simp

/-- **The single-concept positive-part generalization-gap functional.** Fix two parameters `ρ₀, ρ₁` and
take `h₀ = routeLossConcept … ρ₀ y` and the target `c = routeLossConcept … ρ₁ y` (so `c ∈ routeLossClass`).
`G xs := (TrueErrorReal h₀ c D − EmpiricalError h₀ on xs)⁺` is the positive part of `h₀`'s
true-minus-empirical gap against `c`. Since the single-concept gap is an unbiased zero-mean estimator,
its positive part has GENUINELY positive expectation in the presence of sampling variance — this is the
non-vacuous gap functional (not `G := 0`). -/
def singleConceptGap (A : FiniteScoreRouterCode X k) (hk : 0 < k) (y : X → Fin k)
    (ρ0 ρ1 : A.Ρ) (D : Measure X) (m : ℕ) : (Fin m → X) → ℝ :=
  fun xs => max 0 (TrueErrorReal X (routeLossConcept A hk ρ0 y) (routeLossConcept A hk ρ1 y) D
    - EmpiricalError X Bool (routeLossConcept A hk ρ0 y)
        (fun i => (xs i, routeLossConcept A hk ρ1 y (xs i))) (zeroOneLoss Bool))

theorem singleConceptGap_measurable (A : FiniteScoreRouterCode X k) (hk : 0 < k)
    {y : X → Fin k} (hy : Measurable y) (ρ0 ρ1 : A.Ρ) (D : Measure X) (m : ℕ) :
    Measurable (singleConceptGap A hk y ρ0 ρ1 D m) := by
  unfold singleConceptGap
  refine Measurable.max measurable_const (Measurable.const_sub ?_ _)
  exact empiricalError_measurable_in_sample _ _
    (routeLossConcept_measurable A hk ρ0 hy) (routeLossConcept_measurable A hk ρ1 hy) m

theorem singleConceptGap_nonneg (A : FiniteScoreRouterCode X k) (hk : 0 < k) (y : X → Fin k)
    (ρ0 ρ1 : A.Ρ) (D : Measure X) (m : ℕ) : 0 ≤ singleConceptGap A hk y ρ0 ρ1 D m :=
  fun _ => le_max_left _ _

/-- **The superlevel-set property (`hGsub`) of the single-concept gap.** For every `ε` and sample `xs`
with `ε ≤ G xs`, some route-loss concept has true-minus-empirical gap `≥ ε`. By `le_max_iff` either
`ε ≤ 0` — then the target `c = routeLossConcept … ρ₁ y ∈ routeLossClass` has gap exactly `0 ≥ ε`
(`trueErrorReal_self_zero`, `empiricalError_self_zero`) — or `ε ≤` the `h₀`-gap, witnessed by `h₀`. -/
theorem singleConceptGap_sub (A : FiniteScoreRouterCode X k) (hk : 0 < k) (y : X → Fin k)
    (ρ0 ρ1 : A.Ρ) (D : Measure X) (m : ℕ) (ε : ℝ) (xs : Fin m → X)
    (hε : ε ≤ singleConceptGap A hk y ρ0 ρ1 D m xs) :
    ∃ h ∈ routeLossClass A hk y,
      TrueErrorReal X h (routeLossConcept A hk ρ1 y) D -
        EmpiricalError X Bool h (fun i => (xs i, routeLossConcept A hk ρ1 y (xs i)))
          (zeroOneLoss Bool) ≥ ε := by
  unfold singleConceptGap at hε
  rcases le_max_iff.mp hε with hle0 | hleG
  · -- ε ≤ 0 : the target concept `c = routeLossConcept … ρ1 y` has gap exactly 0
    refine ⟨routeLossConcept A hk ρ1 y, ⟨ρ1, rfl⟩, ?_⟩
    rw [trueErrorReal_self_zero, empiricalError_self_zero]
    simpa using hle0
  · -- ε ≤ h₀-gap : witness `h₀`
    exact ⟨routeLossConcept A hk ρ0 y, ⟨ρ0, rfl⟩, hleG⟩

/-! ## 6. The standalone REAL S5 statistical bound on the attention carrier (Strategy A)

`symbolGap := (∫⁻ ofReal G).toReal ≤ symbolBound := √(2 log 2 / m) + (∏ Sauer)·(2/√m)·√(2π)`, the
genuine S5 expected-gap envelope, on the literal scaled-dot-product attention router. The
`WellBehavedVCMeasTarget` regularity is DISCHARGED (not carried) via the Borel-analytic bridge; the
finite-dimensional `W` is `coordSpan d` (the linearity of the attention score differences). -/

/-- **A5-4-real — the REAL S5 statistical bound on the literal attention router.** Strategy A: the
carrier is `Bridge.attentionScoreRouter d nK` on `X = Fin d → ℝ`; its linear score differences give
`W = coordSpan d`, the regularity is discharged via `routeLossClass_wellBehavedVCMeasTarget`, and the
gap functional is the non-vacuous `singleConceptGap`. The real expected gap is bounded by the genuine
Sauer–`√(log/m)` envelope. -/
theorem attentionRoute_realStatBound
    (d nK : ℕ) (hk : 0 < nK) [Infinite (Fin d → ℝ)]
    (y : (Fin d → ℝ) → Fin nK) (hy : Measurable y)
    (ρ0 ρ1 : (Bridge.attentionScoreRouter d nK).Ρ)
    (D : Measure (Fin d → ℝ)) [IsProbabilityMeasure D]
    (m : ℕ) (hm : 0 < m) :
    (∫⁻ xs, ENNReal.ofReal (singleConceptGap (Bridge.attentionScoreRouter d nK) hk y ρ0 ρ1 D m xs)
        ∂(Measure.pi fun _ : Fin m => D)).toReal
      ≤ Real.sqrt (2 * Real.log 2 / m)
        + (↑(∏ _p : Fin nK × Fin nK,
              ∑ r ∈ Finset.range (finrank ℝ (coordSpan d) + 1), (2 * m).choose r) : ℝ)
            * (2 / Real.sqrt m) * Real.sqrt (2 * Real.pi) := by
  -- the constant `W` profile (every pair maps to `coordSpan d`), its finite-dim and linearity data
  have hWfin : ∀ _p : Fin nK × Fin nK, FiniteDimensional ℝ ((fun _ => coordSpan d) _p) :=
    fun _ => coordSpan_finiteDim d
  have hlin : ∀ (p : Fin nK × Fin nK) (K : (Bridge.attentionScoreRouter d nK).Ρ),
      (fun x => (Bridge.attentionScoreRouter d nK).score K x p.2
        - (Bridge.attentionScoreRouter d nK).score K x p.1) ∈ (fun _ => coordSpan d) p :=
    fun p K => attnScoreDiff_mem_coordSpan d nK p K
  -- the discharged regularity and the target concept `c = routeLossConcept … ρ1 y`
  have hWB : WellBehavedVCMeasTarget (Fin d → ℝ) (routeLossClass (Bridge.attentionScoreRouter d nK) hk y) :=
    routeLossClass_wellBehavedVCMeasTarget (Bridge.attentionScoreRouter d nK) hk hy
  have hc_meas : Measurable (routeLossConcept (Bridge.attentionScoreRouter d nK) hk ρ1 y) :=
    routeLossConcept_measurable (Bridge.attentionScoreRouter d nK) hk ρ1 hy
  -- the gap functional and its three properties
  have hGmeas : Measurable (singleConceptGap (Bridge.attentionScoreRouter d nK) hk y ρ0 ρ1 D m) :=
    singleConceptGap_measurable (Bridge.attentionScoreRouter d nK) hk hy ρ0 ρ1 D m
  have hGnn : 0 ≤ singleConceptGap (Bridge.attentionScoreRouter d nK) hk y ρ0 ρ1 D m :=
    singleConceptGap_nonneg (Bridge.attentionScoreRouter d nK) hk y ρ0 ρ1 D m
  have hGsub : ∀ (ε : ℝ) (xs : Fin m → (Fin d → ℝ)),
      ε ≤ singleConceptGap (Bridge.attentionScoreRouter d nK) hk y ρ0 ρ1 D m xs →
      ∃ h ∈ routeLossClass (Bridge.attentionScoreRouter d nK) hk y,
        TrueErrorReal (Fin d → ℝ) h (routeLossConcept (Bridge.attentionScoreRouter d nK) hk ρ1 y) D -
          EmpiricalError (Fin d → ℝ) Bool h
            (fun i => (xs i, routeLossConcept (Bridge.attentionScoreRouter d nK) hk ρ1 y (xs i)))
            (zeroOneLoss Bool) ≥ ε :=
    fun ε xs hε => singleConceptGap_sub (Bridge.attentionScoreRouter d nK) hk y ρ0 ρ1 D m ε xs hε
  -- the genuine S5 expected-gap bound, in `ℝ≥0∞`
  have hS5 := temperedSymbol_expectedGap_hard_le_measTarget (Bridge.attentionScoreRouter d nK) hk hy
    (fun _ => coordSpan d) hWfin hlin D (routeLossConcept (Bridge.attentionScoreRouter d nK) hk ρ1 y)
    hc_meas hWB m hm (singleConceptGap (Bridge.attentionScoreRouter d nK) hk y ρ0 ρ1 D m)
    hGmeas hGnn hGsub
  -- nonnegativity of the two real summands of the envelope
  have hann : 0 ≤ Real.sqrt (2 * Real.log 2 / m) := Real.sqrt_nonneg _
  have hbnn : 0 ≤ (↑(∏ _p : Fin nK × Fin nK,
      ∑ r ∈ Finset.range (finrank ℝ (coordSpan d) + 1), (2 * m).choose r) : ℝ)
      * (2 / Real.sqrt m) * Real.sqrt (2 * Real.pi) := by positivity
  have hrhs_fin : ENNReal.ofReal (Real.sqrt (2 * Real.log 2 / m))
      + ENNReal.ofReal ((↑(∏ _p : Fin nK × Fin nK,
          ∑ r ∈ Finset.range (finrank ℝ (coordSpan d) + 1), (2 * m).choose r) : ℝ)
        * (2 / Real.sqrt m) * Real.sqrt (2 * Real.pi)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hfin : (∫⁻ xs, ENNReal.ofReal
      (singleConceptGap (Bridge.attentionScoreRouter d nK) hk y ρ0 ρ1 D m xs)
        ∂(Measure.pi fun _ : Fin m => D)) ≠ ⊤ :=
    ne_top_of_le_ne_top hrhs_fin hS5
  have hmono := (ENNReal.toReal_le_toReal hfin hrhs_fin).mpr hS5
  rwa [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hann, ENNReal.toReal_ofReal hbnn] at hmono

/-! ## 7. The assembled certificate carrying the REAL S5 statistics

Feeds the real `symbolGap ≤ symbolBound` from `attentionRoute_realStatBound` into
`temperedDesignLawCertificate` as the `stat_cert` leg. The other carried inputs (the abstract gap with
`smooth_cert`/`hard_cert`, the classical non-Borel base range) are carried exactly as in
`temperedDesignLawCertificate_concrete`. The statistical carrier IS the literal attention router (same
family as the hard-tame leg). -/

/-- **The TD16 certificate with the REAL S5 statistics (Strategy A).** A genuine inhabitant of
`TemperedDesignLawCertificate` whose hard-tame statistical leg carries the genuine S5 expected-gap
inequality `(∫⁻ ofReal G).toReal ≤ Sauer–√(log/m) envelope` (from `attentionRoute_realStatBound`),
NOT the placeholder `0 ≤ 1`. The carrier is the literal scaled-dot-product attention router on
`Fin d → ℝ`. The abstract gap `gap := 0` (satisfying both `smooth_cert`/`hard_cert` by
`gapZero_satisfies_certs`) and the classical non-Borel base range are carried exactly as in the
placeholder concrete certificate; everything else is a landed witness. -/
def temperedDesignLawCertificate_real
    (d nK : ℕ) (hk : 0 < nK) (ρ : (Bridge.attentionScoreRouter d nK).Ρ)
    [Infinite (Fin d → ℝ)]
    (y : (Fin d → ℝ) → Fin nK) (hy : Measurable y)
    (ρ0 ρ1 : (Bridge.attentionScoreRouter d nK).Ρ)
    (D : Measure (Fin d → ℝ)) [IsProbabilityMeasure D]
    (m : ℕ) (hm : 0 < m)
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
    -- the REAL S5 statistics: symbolGap := (∫ G).toReal, symbolBound := Sauer envelope
    ((∫⁻ xs, ENNReal.ofReal
          (singleConceptGap (Bridge.attentionScoreRouter d nK) hk y ρ0 ρ1 D m xs)
        ∂(Measure.pi fun _ : Fin m => D)).toReal)
    (Real.sqrt (2 * Real.log 2 / m)
      + (↑(∏ _p : Fin nK × Fin nK,
            ∑ r ∈ Finset.range (finrank ℝ (coordSpan d) + 1), (2 * m).choose r) : ℝ)
          * (2 / Real.sqrt m) * Real.sqrt (2 * Real.pi))
    (attentionRoute_realStatBound d nK hk y hy ρ0 ρ1 D m hm)
    hwild_nonBorel

end TLT.TemperedDesignLaw
