/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.SymbolRouteGenGap
import TLT_Proofs.TemperedDesignLaw.SmoothCertDischarge
import TLT_Proofs.TemperedDesignLaw.HardeningEnvelope
import TLT_Proofs.TemperedDesignLaw.RiskDecomposition
import TLT_Proofs.Capacity.Discretization.SymmetrizationBaseInvariantBound
import SLT.MeasureInfrastructure
import SLT.SubGaussian
import SLT.MetricEntropy

/-!
# S2: Gap identification, binding the tempered route's expected generalization gap

This module converts the symbol route's **tail** bound
(`symbolRoute_gen_gap`, of the Sauer–exp form `Dᵐ{gap ≥ ε} ≤ 2·(∏Sauer)·exp(−mε²/8)`) into a bound on
the route's **expected** generalization gap, via the layer-cake formula plus the truncated Gaussian
tail integral.

## Sub-target 1: HARD tail to expectation (the analytic crux)

The crux lemma `truncated_tail_integral_le` is fully self-contained: for a probability measure `μ`, a
nonnegative measurable real random variable `G`, and a tail bound
`μ{G ≥ ε} ≤ ofReal (2·C·exp(−mε²/8))` for all `ε > 0`, the expected value `E[G]` is bounded by an
explicit `ε₀ + C·(2/√m)·√(2π)` for **any** split point `ε₀ > 0` (truncating the small-`ε` part by the
length·1 estimate and the large-`ε` part by the Gaussian tail integral).  The optimal split is taken at
the point where the tail crosses `1`, but the bound holds for every `ε₀`.

The Gaussian shape: `exp(−mε²/8) = exp(−ε²/(2τ²))` with `τ = 2/√m`, and
`∫₀^∞ 2·exp(−ε²/2τ²) dε = τ·√(2π) = (2/√m)·√(2π)` is exactly `gaussian_tail_integral`.
-/

open MeasureTheory Set Real Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace TLT.TemperedDesignLaw

universe u

/-! ## The analytic crux: a truncated tail → expectation bound -/

/-- **The Gaussian-shaped tail integral, in `ℝ≥0∞`.** For `C ≥ 0` and `m > 0`,
`∫⁻_{Ioi 0} ofReal (2·C·exp(−mε²/8)) dε = ofReal (C·(2/√m)·√(2π))`. The exponent rewrites as
`−ε²/(2τ²)` with `τ = 2/√m`, so `gaussian_tail_integral` gives the closed form. -/
lemma lintegral_gaussianTail_eq
    {C : ℝ} (hC : 0 ≤ C) {m : ℕ} (hm : 0 < m) :
    (∫⁻ ε in Ioi (0 : ℝ), ENNReal.ofReal (2 * C * Real.exp (-((m : ℝ) * ε ^ 2 / 8))))
      = ENNReal.ofReal (C * (2 / Real.sqrt m) * Real.sqrt (2 * Real.pi)) := by
  set τ : ℝ := 2 / Real.sqrt m with hτdef
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsqrtm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmr
  have hτpos : 0 < τ := by rw [hτdef]; positivity
  -- pointwise rewrite of the exponent: −mε²/8 = −ε²/(2τ²)
  have hτsq : 2 * τ ^ 2 = 8 / (m : ℝ) := by
    rw [hτdef]; rw [div_pow, Real.sq_sqrt hmr.le]; ring
  have hpt : ∀ ε : ℝ, 2 * C * Real.exp (-((m : ℝ) * ε ^ 2 / 8))
      = C * (2 * Real.exp (-ε ^ 2 / (2 * τ ^ 2))) := by
    intro ε
    rw [hτsq]
    have : -ε ^ 2 / (8 / (m : ℝ)) = -((m : ℝ) * ε ^ 2 / 8) := by
      field_simp
    rw [this]; ring
  -- convert the lintegral of ofReal to ofReal of the (real) integral
  have hcongr : (fun ε : ℝ => ENNReal.ofReal (2 * C * Real.exp (-((m : ℝ) * ε ^ 2 / 8))))
      = (fun ε : ℝ => ENNReal.ofReal (C * (2 * Real.exp (-ε ^ 2 / (2 * τ ^ 2))))) := by
    funext ε; rw [hpt]
  rw [setLIntegral_congr_fun measurableSet_Ioi (fun ε _ => by rw [hpt ε])]
  -- the integrand C·(2 exp(...)) is nonneg and integrable on Ioi 0
  have hintegrable : IntegrableOn (fun ε : ℝ => C * (2 * Real.exp (-ε ^ 2 / (2 * τ ^ 2))))
      (Ioi (0 : ℝ)) := by
    have hbase : IntegrableOn (fun ε : ℝ => 2 * Real.exp (-ε ^ 2 / (2 * τ ^ 2)))
        (Ioi (0 : ℝ)) := by
      apply Integrable.const_mul
      have : (fun ε : ℝ => Real.exp (-ε ^ 2 / (2 * τ ^ 2)))
          = (fun ε : ℝ => Real.exp (-(1 / (2 * τ ^ 2)) * ε ^ 2)) := by
        funext ε; congr 1; field_simp
      rw [this]
      exact integrableOn_Ioi_exp_neg_mul_sq_iff.mpr (by positivity : 0 < 1 / (2 * τ ^ 2))
    exact hbase.const_mul C
  rw [← ofReal_integral_eq_lintegral_ofReal hintegrable
    (ae_of_all _ (fun ε => by positivity))]
  congr 1
  rw [integral_const_mul, gaussian_tail_integral hτpos, hτdef]
  ring

/-- **Truncated tail → expected-gap bound (the S2 analytic crux), `ℝ≥0∞` form.**  Let `μ` be a
probability measure, `G` a nonnegative measurable real random variable, and suppose the tail satisfies
`μ{G ≥ ε} ≤ ofReal (2·C·exp(−mε²/8))` for all `ε > ε₀` (the Sauer–exp shape of `symbolRoute_gen_gap`,
which only holds in the large-`ε` regime `m·ε² ≥ 2 log 2`; the split point `ε₀` is taken at that lower
bound). Then the expected gap (as `∫⁻ ofReal G`, i.e. `E[G⁺]`, always well-defined without an
integrability hypothesis) satisfies
`∫⁻ ω, ofReal (G ω) ≤ ofReal ε₀ + ofReal (C·(2/√m)·√(2π))`.

The small-`ε` part `(0, ε₀]` is bounded by `length·1` (`setLIntegral_Ioc_le_length_mul_sup`, using that
`μ` is a probability measure so every tail-set measure is `≤ 1`); the large-`ε` part `(ε₀, ∞)` is bounded
by the Gaussian tail integral over all of `Ioi 0` (`lintegral_gaussianTail_eq`). -/
theorem truncated_tail_lintegral_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {G : Ω → ℝ} (hGmeas : Measurable G) (hGnn : 0 ≤ G)
    {C : ℝ} (hC : 0 ≤ C) {m : ℕ} (hm : 0 < m)
    {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀)
    (htail : ∀ ε : ℝ, ε₀ < ε →
      μ {ω | ε ≤ G ω} ≤ ENNReal.ofReal (2 * C * Real.exp (-((m : ℝ) * ε ^ 2 / 8)))) :
    (∫⁻ ω, ENNReal.ofReal (G ω) ∂μ)
      ≤ ENNReal.ofReal ε₀ + ENNReal.ofReal (C * (2 / Real.sqrt m) * Real.sqrt (2 * Real.pi)) := by
  -- Step 1 (layer cake): ∫⁻ ofReal(G) = ∫⁻_{Ioi 0} μ{G ≥ t} dt.
  have hGnn_ae : 0 ≤ᵐ[μ] G := ae_of_all _ hGnn
  rw [lintegral_eq_lintegral_tail hGmeas.aemeasurable hGnn_ae]
  -- Step 2: split Ioi 0 = Ioc 0 ε₀ ∪ Ioi ε₀.
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) ε₀ ∪ Ioi ε₀ := (Ioc_union_Ioi_eq_Ioi hε₀).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) ε₀) (Ioi ε₀) := Set.Ioc_disjoint_Ioi_same
  rw [hsplit, lintegral_union measurableSet_Ioi hdisj]
  refine add_le_add ?_ ?_
  · -- small-ε part: bounded by length·1
    have hle1 : ∀ t ∈ Ioc (0 : ℝ) ε₀, μ {ω | t ≤ G ω} ≤ (1 : ℝ≥0∞) :=
      fun t _ => prob_le_one
    calc (∫⁻ t in Ioc (0 : ℝ) ε₀, μ {ω | t ≤ G ω})
        ≤ ENNReal.ofReal (ε₀ - 0) * 1 := setLIntegral_Ioc_le_length_mul_sup hle1
      _ = ENNReal.ofReal ε₀ := by rw [sub_zero, mul_one]
  · -- large-ε part: tail ≤ gaussian, then extend Ioi ε₀ ⊆ Ioi 0 and use the closed form
    calc (∫⁻ t in Ioi ε₀, μ {ω | t ≤ G ω})
        ≤ ∫⁻ t in Ioi ε₀, ENNReal.ofReal (2 * C * Real.exp (-((m : ℝ) * t ^ 2 / 8))) := by
          refine setLIntegral_mono' measurableSet_Ioi ?_
          intro t ht
          exact htail t ht
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2 * C * Real.exp (-((m : ℝ) * t ^ 2 / 8))) :=
          lintegral_mono_set (Ioi_subset_Ioi hε₀)
      _ = ENNReal.ofReal (C * (2 / Real.sqrt m) * Real.sqrt (2 * Real.pi)) :=
          lintegral_gaussianTail_eq hC hm

/-! ## Sub-target 1: instantiating the crux at the symbol route

`symbolRoute_gen_gap` supplies exactly the large-`ε` tail input the crux needs, with
`C = ∏_{(i,j)} ∑_{r ≤ finrank Wᵢⱼ} (2m choose r)` (a `Nat` cast, hence `≥ 0`) and the split point
`ε₀ = √(2 log 2 / m)` (where `m·ε₀² = 2 log 2`, the `hm_large` boundary). Below `ε₀` the tail is bounded
by `1` (probability measure); above it `symbolRoute_gen_gap` applies. The "gap functional" `G` is any
nonnegative measurable real random variable whose superlevel set `{ε ≤ G}` sits inside the route's
"some concept's gap exceeds `ε`" event (the uniform routing-gap functional). -/

open Module

/-- **S2 sub-target 1: the symbol route's expected generalization gap is bounded by the explicit
Sauer-`√(log/m)` envelope.**  For any nonnegative measurable real gap functional `G` whose superlevel
sets sit inside the symbol route's "some route-loss concept's true-minus-empirical gap exceeds `ε`"
event, the expected gap `E[G⁺] = ∫⁻ ofReal G` (always well-defined) is bounded by
`ε₀ + (∏ Sauer)·(2/√m)·√(2π)`, with `ε₀ = √(2 log 2 / m)`.

This binds the symbol route's hard tail bound `symbolRoute_gen_gap` to a **real expected quantity** via
the layer-cake crux `truncated_tail_lintegral_le`: the small-`ε` part is bounded by `ε₀`, the large-`ε`
part by the truncated Gaussian tail integral `lintegral_gaussianTail_eq`. -/
theorem temperedSymbol_expectedGap_hard_le {X : Type u} [MeasurableSpace X] [Infinite X] {k : ℕ}
    (A : FiniteScoreRouterCode X k) (hk : 0 < k)
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
    (∫⁻ xs, ENNReal.ofReal (G xs) ∂(Measure.pi fun _ : Fin m => D))
      ≤ ENNReal.ofReal (Real.sqrt (2 * Real.log 2 / m))
        + ENNReal.ofReal
            ((↑(∏ p : Fin k × Fin k,
                ∑ r ∈ Finset.range (finrank ℝ (W p) + 1), (2 * m).choose r) : ℝ)
              * (2 / Real.sqrt m) * Real.sqrt (2 * Real.pi)) := by
  set μ : Measure (Fin m → X) := Measure.pi fun _ : Fin m => D with hμ
  -- The Sauer product constant and the split point.
  set C : ℝ := (↑(∏ p : Fin k × Fin k,
      ∑ r ∈ Finset.range (finrank ℝ (W p) + 1), (2 * m).choose r) : ℝ) with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set ε₀ : ℝ := Real.sqrt (2 * Real.log 2 / m) with hε₀def
  have hε₀nn : 0 ≤ ε₀ := Real.sqrt_nonneg _
  -- The large-ε tail: for ε > ε₀ we have m·ε² > 2 log 2, so `symbolRoute_gen_gap` applies, and the
  -- superlevel set `{ε ≤ G}` sits inside the route's exists-event.
  have htail : ∀ ε : ℝ, ε₀ < ε →
      μ {xs | ε ≤ G xs}
        ≤ ENNReal.ofReal (2 * C * Real.exp (-((m : ℝ) * ε ^ 2 / 8))) := by
    intro ε hε
    have hεpos : 0 < ε := lt_of_le_of_lt hε₀nn hε
    -- m·ε² ≥ 2 log 2 (from ε > ε₀ = √(2 log 2 / m))
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
    -- superlevel set ⊆ exists-event, then monotonicity + symbolRoute_gen_gap.
    have hsubset : {xs : Fin m → X | ε ≤ G xs} ⊆
        {xs : Fin m → X | ∃ h ∈ routeLossClass A hk y,
          TrueErrorReal X h c D -
            EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε} := by
      intro xs hxs
      exact hGsub ε xs hxs
    calc μ {xs | ε ≤ G xs}
        ≤ μ {xs : Fin m → X | ∃ h ∈ routeLossClass A hk y,
            TrueErrorReal X h c D -
              EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε} :=
          measure_mono hsubset
      _ ≤ ENNReal.ofReal (2 * (C * Real.exp (-((m : ℝ) * ε ^ 2 / 8)))) :=
          symbolRoute_gen_gap A hk hy W hWfin hlin D c hc_meas hWB m hm ε hεpos hlarge
      _ = ENNReal.ofReal (2 * C * Real.exp (-((m : ℝ) * ε ^ 2 / 8))) := by
          rw [mul_assoc]
  -- Apply the analytic crux.
  have := truncated_tail_lintegral_le hGmeas hGnn hCnn hm hε₀nn htail
  -- rewrite the bound to the stated closed form
  rw [hμ]
  convert this using 2

/-! ## Sub-target 2: SMOOTH (Dudley) expected-gap bound

The soft mixture route's output, composed with the loss, is a real family `F : ParamSpace d → V → ℝ`.
`expectedGap_le_two_capacityReal` bounds its **expected** uniform deviation by `2·∫ empiricalCapacityReal`.
Feeding the per-sample Dudley capacity bound (the integrated form of `temperedStack_smooth_cert`,
supplied as `hExpCap : ∫ empiricalCapacityReal ≤ capBound`) gives the smooth expected-gap envelope
`E[gap] ≤ 2·capBound`. -/

open TLT.Capacity

/-- **S2 sub-target 2: the SMOOTH (Dudley) expected-gap bound.**  For a uniformly bounded, measurable,
parameter-continuous real family `F` (the soft mixture route's loss-composed output), the expected
uniform deviation over the dyadic weight ball is at most `2·capBound`, where `capBound` is any bound on
the expected empirical capacity `∫ S, empiricalCapacityReal R F S`. With `F` the tempered stack's
loss-composed family and `capBound = dudleyCapBound …` (the integrated `temperedStack_smooth_cert`), this
is the smooth-side expected generalization gap of the tempered soft route.

The bound follows from `expectedGap_le_two_capacityReal` together with the expected-capacity bound,
connecting the soft mixture route's expected gap to the Dudley capacity envelope. -/
theorem temperedSoftRoute_expectedGap_smooth_le
    {X : Type*} [MeasurableSpace X] {P : Measure X} [IsProbabilityMeasure P] {d m : ℕ}
    (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R)
    (F : Capacity.ParamSpace d → X → ℝ) {b : ℝ} (hFb : ∀ θ x, |F θ x| ≤ b)
    (hFmeas : ∀ θ, Measurable (F θ)) (hFcont : ∀ x, Continuous fun θ : Capacity.ParamSpace d => F θ x)
    {capBound : ℝ}
    (hExpCap : (∫ S, empiricalCapacityReal R F S ∂(Measure.pi fun _ : Fin m => P)) ≤ capBound) :
    (∫ S, ⨆ w : BaseWeightPreimage Capacity.Dyadic R,
        (trueRisk P (F (embedBase Capacity.Dyadic w.1)) - empMean (F (embedBase Capacity.Dyadic w.1)) S)
        ∂(Measure.pi fun _ : Fin m => P))
      ≤ 2 * capBound := by
  calc (∫ S, ⨆ w : BaseWeightPreimage Capacity.Dyadic R,
          (trueRisk P (F (embedBase Capacity.Dyadic w.1)) - empMean (F (embedBase Capacity.Dyadic w.1)) S)
          ∂(Measure.pi fun _ : Fin m => P))
      ≤ 2 * ∫ S, empiricalCapacityReal R F S ∂(Measure.pi fun _ : Fin m => P) :=
        expectedGap_le_two_capacityReal hm hR F hFb hFmeas hFcont
    _ ≤ 2 * capBound := by
        exact mul_le_mul_of_nonneg_left hExpCap (by norm_num)

/-! ## Sub-target 3 (partial): the soft-route loss bridge to the hard route payload

For a **route-factored (output-Lipschitz) loss** `Φ`, the soft mixture output's loss at any point is
bounded by the hard route payload's loss plus the β-leakage. This is the per-point bridge inequality
that would let a hard-route certificate dominate the soft-route gap, composing
`RouteFactoredLoss.mixture_le_route` (soft loss ≤ route-payload loss + `Lℓ·‖soft − payload‖`) with
`softMixture_sub_hardPayload_le_exp` (the deviation `≤ (k−1)·exp(−βγ)·D`).

Note on scope. The hard bound of sub-target 1 is stated for the **0-1 routing-loss class**
(`routeLossClass`, Boolean concepts), while this bridge lives in the **output-Lipschitz** loss world
(`RouteFactoredLoss`). The `RouteFactoredLoss` modelling note records that the output-Lipschitz
factorization does not accommodate the 0-1 routing loss; aligning the two loss structures is an
open factorization-strength design choice. The full bridge "hard 0-1 cert dominates the soft Lipschitz
gap" is not closed here; the present per-point loss inequality is the fragment that compiles. -/

/-- **S2 sub-target 3 (partial): the soft-route per-point loss bridge.** For a route-factored loss `Φ`,
the soft mixture output's loss is within the β-leakage envelope of the hard route payload's loss:
`Φ.loss(soft mixture) y ≤ Φ.loss(val hardRoute) y + Φ.Lℓ·(k−1)·exp(−βγ)·D`.

Composes `RouteFactoredLoss.mixture_le_route` with `softMixture_sub_hardPayload_le_exp` (β-hardening
leakage). This is the bridge inequality whose population integral binds the soft gap to the hard route +
leakage; the loss-class mismatch to the 0-1 hard cert is the open factorization-strength choice (see the
module note). -/
theorem softRoute_loss_bridge_le {X : Type u} [MeasurableSpace X] {k : ℕ} [NeZero k]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {Y : Type*}
    (Φ : RouteFactoredLoss V Y) (A : TemperedRouterFamily X k) (hk : 0 < k)
    (ρ : A.router.Ρ) (x : X) (val : Fin k → V) (y : Y) {D : ℝ}
    (hD : ∀ i, ‖val i - val (hardRoute A hk ρ x)‖ ≤ D) :
    Φ.loss (mixtureOutput (softWeights A ρ x) val) y
      ≤ Φ.loss (val (hardRoute A hk ρ x)) y
        + Φ.Lℓ * (((k : ℝ) - 1) * Real.exp (-(A.β * gammaMargin A hk ρ x)) * D) := by
  have hstep : Φ.Lℓ * ‖mixtureOutput (softWeights A ρ x) val - val (hardRoute A hk ρ x)‖
      ≤ Φ.Lℓ * (((k : ℝ) - 1) * Real.exp (-(A.β * gammaMargin A hk ρ x)) * D) :=
    mul_le_mul_of_nonneg_left
      (softMixture_sub_hardPayload_le_exp A hk ρ x val hD) Φ.Lℓ_nonneg
  have hmix := Φ.mixture_le_route (softWeights A ρ x) val (hardRoute A hk ρ x) y
  linarith [hmix, hstep]

end TLT.TemperedDesignLaw

