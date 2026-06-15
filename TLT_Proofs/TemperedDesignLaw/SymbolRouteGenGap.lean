/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.Symmetrization
import TLT_Proofs.TemperedDesignLaw.HardCertDischarge
import TLT_Proofs.TemperedDesignLaw.ArrangementVC

/-!
# A5-2c: the FULL symbol-ROUTE population generalization gap

Population generalization bound for the **hard symbol route's 0-1 loss** (the routing-error
channel), as opposed to the per-pair score-comparison channel of `SymbolChannelGenGap.lean`.

## 1. `boolClass_gen_gap`: the template, generalized

`boolClass_gen_gap` is the generalization bound for an arbitrary measurable Bool class
`C : ConceptClass X Bool`. The symmetrization machinery (`symmetrization_step` +
`double_sample_pattern_bound`) requires only that every concept in `C` is measurable (`hmeas_C`),
the target is measurable (`hc_meas`), and a `WellBehavedVC` regularity leg (`hWB`). The
comparison-class version is `boolClass_gen_gap` applied with `comparisonConcept_measurable`.

## 2. The route-loss application

* `routeLossConcept A hk ρ y x := decide (A.route hk ρ x ≠ y x)`: the 0-1 routing loss against the
  target labelling `y`, as a Boolean concept on `X`.
* `routeLossClass A hk y := Set.range (fun ρ => routeLossConcept A hk ρ y)`: the loss class as `ρ`
  varies.

Then:
* `routeLossConcept_measurable`: measurable, from `route_measurable` (joint `Ρ × X`) sectioned at `ρ`
  via `measurable_prodMk_left`, paired with measurable `y`, and discreteness of `Fin k`.
* `routeLossClass_growthFunction_le`: the loss factors through the route, so on every sample the
  loss-pattern count is at most the route-pattern count, which `symbolClass_growth_prod` (S3) bounds
  by the arrangement Sauer product. The growth function is the `sSup` of the per-sample restriction
  counts, so this uniform per-sample bound bounds the `sSup`.
* `symbolRoute_gen_gap`: `boolClass_gen_gap` for `routeLossClass`, with the growth function
  replaced by the arrangement Sauer product. The symbol-route population gap is at most
  `2 · (∏ Sauer) · exp(-mε²/8)`.
-/

noncomputable section

open Module MeasureTheory

namespace TLT.TemperedDesignLaw

universe u

variable {X : Type u} [MeasurableSpace X] {k : ℕ}

/-! ## 1. The template, generalized: an arbitrary measurable Bool class -/

/-- **A5-2c.1: population generalization gap for an arbitrary measurable Bool class.**

For a concept class `C : ConceptClass X Bool`, the population (one-sided uniform) generalization
gap satisfies

`Dᵐ{∃ h ∈ C, TrueErr h − EmpErr h ≥ ε} ≤ 2 · GrowthFunction X C (2m) · exp(−mε²/8)`,

assuming measurability of every concept in `C` (`hmeas_C`), measurability of the target (`hc_meas`),
and the `WellBehavedVC` regularity leg (`hWB`). Applied to `comparisonClass A i j` with
`comparisonConcept_measurable` one recovers `comparisonClass_gen_gap`; applied to `routeLossClass`
one recovers `symbolRoute_gen_gap` below. -/
theorem boolClass_gen_gap [Infinite X]
    (C : ConceptClass X Bool) (hmeas_C : ∀ h ∈ C, Measurable h)
    (D : Measure X) [IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hWB : WellBehavedVC X C)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hm_large : 2 * Real.log 2 ≤ ↑m * ε ^ 2) :
    Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | ∃ h ∈ C,
        TrueErrorReal X h c D -
          EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε}
      ≤ ENNReal.ofReal
          (2 * (↑(GrowthFunction X C (2 * m)) *
            Real.exp (-(↑m * ε ^ 2 / 8)))) := by
  -- The NullMeasurableSet leg of `double_sample_pattern_bound`, from `WellBehavedVC`.
  have hE_nullmeas := hWB D c m ε
  -- Symmetrization (Bool, measurable concepts only): bad event ≤ 2 · double-sample event.
  have h_symm := symmetrization_step D C c hmeas_C hc_meas m hm ε hε hm_large
  -- Double-sample event ≤ GrowthFunction · exp(-mε²/8).
  have h_dbl := double_sample_pattern_bound D C c hmeas_C hc_meas m hm ε hε hE_nullmeas
  -- Compose: bad ≤ 2 · double-sample ≤ 2 · (GF · exp).
  calc Measure.pi (fun _ : Fin m => D)
        {xs : Fin m → X | ∃ h ∈ C,
          TrueErrorReal X h c D -
            EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) ≥ ε}
      ≤ 2 * (Measure.pi (fun _ : Fin m => D)).prod (Measure.pi (fun _ : Fin m => D))
          {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
            EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
            EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2} :=
        h_symm
    _ ≤ 2 * ENNReal.ofReal (↑(GrowthFunction X C (2 * m)) *
          Real.exp (-(↑m * ε ^ 2 / 8))) := by
        exact mul_le_mul_right h_dbl 2
    _ = ENNReal.ofReal
          (2 * (↑(GrowthFunction X C (2 * m)) *
            Real.exp (-(↑m * ε ^ 2 / 8)))) := by
        have h2 : (2 : ENNReal) = ENNReal.ofReal 2 := by rw [ENNReal.ofReal_ofNat]
        rw [h2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]

/-! ## 2. The symbol-route 0-1 loss class -/

/-- The **route-loss concept** at parameter `ρ` against the target labelling `y`: the Boolean
indicator of the routing error `route ρ x ≠ y x`. This is the 0-1 loss of the hard symbol route,
read as a concept on `X`. -/
def routeLossConcept (A : FiniteScoreRouterCode X k) (hk : 0 < k) (ρ : A.Ρ) (y : X → Fin k) :
    Concept X Bool :=
  fun x => decide (A.route hk ρ x ≠ y x)

/-- The **route-loss class** against the target labelling `y`: the Boolean concept class of the
routing-error indicator as the parameter varies. The route loss factors through the route, so this
class's combinatorial capacity is bounded by that of the symbol class itself. -/
def routeLossClass (A : FiniteScoreRouterCode X k) (hk : 0 < k) (y : X → Fin k) :
    ConceptClass X Bool :=
  Set.range (fun ρ => routeLossConcept A hk ρ y)

/-- **(a) The route-loss concept is measurable.** Its `true`-fiber is `{x | route ρ x ≠ y x}`, the
preimage of the (discrete, hence measurable) off-diagonal `{p : Fin k × Fin k | p.1 ≠ p.2}` under the
measurable map `x ↦ (route ρ x, y x)`. The route section is measurable from the joint
`route_measurable` precomposed with `Prod.mk ρ` (`measurable_prodMk_left`); `y` is measurable by
hypothesis. -/
theorem routeLossConcept_measurable (A : FiniteScoreRouterCode X k) (hk : 0 < k) (ρ : A.Ρ)
    {y : X → Fin k} (hy : Measurable y) :
    Measurable (routeLossConcept A hk ρ y) := by
  -- The route, sectioned at `ρ`, is measurable.
  have hroute : Measurable (fun x => A.route hk ρ x) :=
    (A.route_measurable hk).comp measurable_prodMk_left
  -- The joint map `x ↦ (route ρ x, y x)` is measurable.
  have hpair : Measurable (fun x => (A.route hk ρ x, y x)) := hroute.prodMk hy
  refine measurable_to_bool ?_
  have hpre : routeLossConcept A hk ρ y ⁻¹' {true} =
      (fun x => (A.route hk ρ x, y x)) ⁻¹' {p : Fin k × Fin k | p.1 ≠ p.2} := by
    ext x
    simp only [routeLossConcept, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
      decide_eq_true_eq]
  rw [hpre]
  exact hpair MeasurableSet.of_discrete

/-! ## (b) The loss factors through the route, so the growth function is bounded -/

/-- **The route-loss restriction is the image of the route restriction.** On a sample `S`, every loss
pattern realized by `routeLossClass A hk y` is the pointwise `decide (· ≠ y ·)` image of a route
pattern realized by `routeRestr A hk S`. Hence the loss-restriction set injects (as an image) into the
route-restriction range, and its `ncard` is at most the route-pattern count. -/
theorem routeLossRestr_ncard_le_routeRestr (A : FiniteScoreRouterCode X k) (hk : 0 < k)
    (y : X → Fin k) (S : Finset X) :
    (restrictionSet (routeLossClass A hk y) S).ncard
      ≤ (Set.range (routeRestr A hk S)).ncard := by
  -- The "loss-of-a-route" map: a route pattern `r : S → Fin k` ↦ its loss pattern `S → Bool`.
  set g : (↥S → Fin k) → (↥S → Bool) := fun r x => decide (r x ≠ y (x : X)) with hg
  -- Every loss pattern in the restriction set is `g` of some route pattern in `routeRestr`'s range.
  have hsub : restrictionSet (routeLossClass A hk y) S ⊆ g '' Set.range (routeRestr A hk S) := by
    rintro f ⟨c, ⟨ρ, rfl⟩, hcf⟩
    refine ⟨routeRestr A hk S ρ, Set.mem_range_self ρ, ?_⟩
    funext x
    -- `f x = routeLossConcept A hk ρ y x = decide (route ρ x ≠ y x) = g (routeRestr … ρ) x`.
    have := hcf x
    simp only [routeLossConcept, routeRestr, hg] at this ⊢
    exact this
  calc (restrictionSet (routeLossClass A hk y) S).ncard
      ≤ (g '' Set.range (routeRestr A hk S)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Set.range (routeRestr A hk S)).ncard := Set.ncard_image_le (Set.toFinite _)

/-- **(b) The route-loss growth function is bounded by the arrangement Sauer product.** Under per-pair
linearity, the growth function of `routeLossClass A hk y` at `2m` is at most the product over the `k²`
ordered pairs of the Sauer–Shelah binomial sums:

`GrowthFunction X (routeLossClass A hk y) (2m) ≤ ∏_{(i,j)} ∑_{r ≤ finrank Wᵢⱼ} (2m choose r)`.

The growth function is the `sSup` over `|S| = 2m` samples of the loss-restriction pattern count; each
such count is at most the route-pattern count (`routeLossRestr_ncard_le_routeRestr`, the loss factors
through the route), which `symbolClass_growth_prod` (S3) bounds uniformly by the product. So the
uniform per-sample bound bounds the `sSup`. -/
theorem routeLossClass_growthFunction_le (A : FiniteScoreRouterCode X k) (hk : 0 < k)
    (y : X → Fin k)
    (W : Fin k × Fin k → Submodule ℝ (X → ℝ)) (hWfin : ∀ p, FiniteDimensional ℝ (W p))
    (hlin : ∀ (p : Fin k × Fin k) (ρ : A.Ρ), (fun x => A.score ρ x p.2 - A.score ρ x p.1) ∈ W p)
    (m : ℕ) :
    GrowthFunction X (routeLossClass A hk y) (2 * m)
      ≤ ∏ p : Fin k × Fin k, ∑ r ∈ Finset.range (finrank ℝ (W p) + 1), (2 * m).choose r := by
  -- The uniform per-sample bound: every `|S| = 2m` restriction count ≤ the product.
  have hbound : ∀ S : { S : Finset X // S.card = 2 * m },
      (restrictionSet (routeLossClass A hk y) S.val).ncard
        ≤ ∏ p : Fin k × Fin k, ∑ r ∈ Finset.range (finrank ℝ (W p) + 1), (2 * m).choose r := by
    rintro ⟨S, hS⟩
    calc (restrictionSet (routeLossClass A hk y) S).ncard
        ≤ (Set.range (routeRestr A hk S)).ncard :=
          routeLossRestr_ncard_le_routeRestr A hk y S
      _ ≤ ∏ p : Fin k × Fin k, ∑ r ∈ Finset.range (finrank ℝ (W p) + 1), S.card.choose r :=
          symbolClass_growth_prod A hk W hWfin hlin S
      _ = ∏ p : Fin k × Fin k, ∑ r ∈ Finset.range (finrank ℝ (W p) + 1), (2 * m).choose r := by
          rw [hS]
  -- `GrowthFunction = sSup (range of restriction counts)`; bound the `sSup` by `hbound`.
  show sSup (Set.range fun S : { S : Finset X // S.card = 2 * m } =>
      (restrictionSet (routeLossClass A hk y) S.val).ncard) ≤ _
  rcases Set.eq_empty_or_nonempty (Set.range fun S : { S : Finset X // S.card = 2 * m } =>
      (restrictionSet (routeLossClass A hk y) S.val).ncard) with he | hne
  · simp [he]
  · refine csSup_le hne ?_
    rintro b ⟨S, rfl⟩
    exact hbound S

/-! ## (c) The symbol-route population generalization gap -/

/-- **A5-2c: the FULL symbol-route population generalization gap (growth-function form).**

For a router code `A`, a measurable target labelling `y : X → Fin k`, and a sample size `m` large
enough, the probability under the `m`-fold product measure that **some** route-loss concept in
`routeLossClass A hk y` has population (0-1 routing) risk exceeding its empirical risk by `ε` is bounded
by `2 · GrowthFunction X (routeLossClass A hk y) (2m) · exp(−mε²/8)`.

This is `boolClass_gen_gap` applied to the route-loss class, with measurability supplied by
`routeLossConcept_measurable`. -/
theorem symbolRoute_gen_gap_growth [Infinite X]
    (A : FiniteScoreRouterCode X k) (hk : 0 < k)
    {y : X → Fin k} (hy : Measurable y)
    (D : Measure X) [IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hWB : WellBehavedVC X (routeLossClass A hk y))
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
  exact boolClass_gen_gap (routeLossClass A hk y) hmeas_C D c hc_meas hWB m hm ε hε hm_large

/-- **A5-2c: the FULL symbol-route population generalization gap (arrangement Sauer form).**

Same as `symbolRoute_gen_gap_growth`, but with the growth function replaced by the
arrangement-VC Sauer–Shelah product (`routeLossClass_growthFunction_le`): under per-pair
linearity of the score differences (each `x ↦ sⱼ(x) − sᵢ(x)` in a finite-dimensional `Wᵢⱼ`),

`Dᵐ{∃ h ∈ routeLossClass, TrueErr h − EmpErr h ≥ ε}
   ≤ 2 · (∏_{(i,j)} ∑_{r ≤ finrank Wᵢⱼ} (2m choose r)) · exp(−mε²/8)`.

The symbol-route 0-1 population generalization gap in closed form against the arrangement
dimension, analogous to `comparisonClass_gen_gap_sauer`. Conditional on `hlin`; the linearity
hypothesis is not satisfied for arbitrary measurable scores. -/
theorem symbolRoute_gen_gap [Infinite X]
    (A : FiniteScoreRouterCode X k) (hk : 0 < k)
    {y : X → Fin k} (hy : Measurable y)
    (W : Fin k × Fin k → Submodule ℝ (X → ℝ)) (hWfin : ∀ p, FiniteDimensional ℝ (W p))
    (hlin : ∀ (p : Fin k × Fin k) (ρ : A.Ρ), (fun x => A.score ρ x p.2 - A.score ρ x p.1) ∈ W p)
    (D : Measure X) [IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hWB : WellBehavedVC X (routeLossClass A hk y))
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
    (symbolRoute_gen_gap_growth A hk hy D c hc_meas hWB m hm ε hε hm_large) ?_
  apply ENNReal.ofReal_le_ofReal
  have hGF : GrowthFunction X (routeLossClass A hk y) (2 * m) ≤
      ∏ p : Fin k × Fin k, ∑ r ∈ Finset.range (finrank ℝ (W p) + 1), (2 * m).choose r :=
    routeLossClass_growthFunction_le A hk y W hWfin hlin m
  have hGFr : (↑(GrowthFunction X (routeLossClass A hk y) (2 * m)) : ℝ) ≤
      ↑(∏ p : Fin k × Fin k, ∑ r ∈ Finset.range (finrank ℝ (W p) + 1), (2 * m).choose r) := by
    exact_mod_cast hGF
  have hexp_nonneg : 0 ≤ Real.exp (-(↑m * ε ^ 2 / 8)) := (Real.exp_pos _).le
  have hmono : (↑(GrowthFunction X (routeLossClass A hk y) (2 * m)) : ℝ) *
        Real.exp (-(↑m * ε ^ 2 / 8)) ≤
      (↑(∏ p : Fin k × Fin k, ∑ r ∈ Finset.range (finrank ℝ (W p) + 1), (2 * m).choose r) : ℝ) *
        Real.exp (-(↑m * ε ^ 2 / 8)) :=
    mul_le_mul_of_nonneg_right hGFr hexp_nonneg
  linarith [hmono]

end TLT.TemperedDesignLaw
