/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Routing.MeasurableScoreRouting

/-!
# The tempered design law: statements (the temperature–depth phase portrait)

A routed transformer is one object on a two-parameter approximation square: **sharpness** `β` and
**precision** `u`. Every headline quantity (expressivity, statistical capacity, numerical error,
measurability, decidability) is a decoration of that square, with certified edges between the four
corners (ideal/float × soft/hard). The soft→hard bridge has the same grammar as the real→float bridge:
`β` plays the role of `u`, the mixture leakage `(k−1)·exp(−β·γ)` plays the role of the rounding envelope,
and the margin interior plays the role of the normality regime, composed by the identical `envBound`
telescope over `ExecLayer`.

This file states the law's nodes as Lean `Prop`s; their proofs are developed downstream.

## Convention dictionary (the sharpness/temperature collision, resolved here and nowhere else)

The shipped library's routing parameter is a **sharpness** (inverse temperature): `softmaxWeight` of
`β`-scaled scores, with the hard route recovered as `β → ∞`. Thermodynamic temperature is `T := 1/β`,
with the hard route at `T → 0`. **All statements below use `β`** (sharpness, in `[0, ∞)`); any informal
temperature reading is `T = 1/β`. A statement mixing the two without this dictionary is malformed.

## Two channels (the single largest source of false statements in this domain)

Every claim names its channel:
* **Symbol channel**: the route label (`leastArgmax` of the scores). It is `β`-invariant for `β > 0`
  (`top1_softmax_eq_argmax`: scaling scores by `β > 0` preserves the argmax).
* **Mixture channel**: the simplex weights (`softWeights`). It is `β`-sensitive.

Conflating them (e.g. reading a mixture-channel certificate as a symbol-channel fact) is forbidden.
-/

open scoped BigOperators

universe u

noncomputable section

namespace TLT.TemperedDesignLaw

/-! ## TD0.1: `TemperedRouterFamily` and the two channels -/

/-- A finite score router paired with a sharpness `β ∈ [0, ∞)`: the soft (mixture) channel is the
`β`-tempered softmax of the scores; the hard (symbol) channel is the router's `leastArgmax` route. -/
structure TemperedRouterFamily (X : Type u) [MeasurableSpace X] (k : ℕ) where
  /-- The underlying finite score router. -/
  router : FiniteScoreRouterCode X k
  /-- The sharpness (inverse temperature). -/
  β : ℝ
  /-- Sharpness is nonnegative. -/
  hβ : 0 ≤ β

/-- **The mixture channel.** The `β`-tempered softmax weight of class `i`:
`exp(β·sᵢ) / Σⱼ exp(β·sⱼ)`. `β`-sensitive; the soft reading of the router. -/
def softWeights {X : Type u} [MeasurableSpace X] {k : ℕ} (A : TemperedRouterFamily X k)
    (ρ : A.router.Ρ) (x : X) (i : Fin k) : ℝ :=
  Real.exp (A.β * A.router.score ρ x i) / ∑ j, Real.exp (A.β * A.router.score ρ x j)

/-- **The symbol channel.** The hard route: the deterministic `leastArgmax` of the scores,
`β`-invariant (the `β → ∞` reading of the mixture). -/
def hardRoute {X : Type u} [MeasurableSpace X] {k : ℕ} (A : TemperedRouterFamily X k) (hk : 0 < k)
    (ρ : A.router.Ρ) (x : X) : Fin k :=
  A.router.route hk ρ x

/-- **TD1 (per-layer core): symbol invariance.** For `β > 0`, the `leastArgmax` of the tempered
softmax weights is exactly the hard route: the symbol channel does not see the sharpness. (At `β = 0`
the weights are uniform and this fails; see GB1.) -/
def TD0_symbol_invariant {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : TemperedRouterFamily X k) (hk : 0 < k) : Prop :=
  0 < A.β → ∀ (ρ : A.router.Ρ) (x : X), leastArgmax (softWeights A ρ x) hk = hardRoute A hk ρ x

/-! ## TD0.2: the margin function and the two shells -/

/-- The second-highest score: the supremum of the scores over the indices other than `top`
(degenerate `top`-valued when no other index exists, i.e. `k = 1`). -/
def secondScore {k : ℕ} (s : Fin k → ℝ) (top : Fin k) : ℝ :=
  if h : (Finset.univ.filter (fun i => i ≠ top)).Nonempty
  then (Finset.univ.filter (fun i => i ≠ top)).sup' h s
  else s top

/-- **The margin function.** Top score minus second score under the `leastArgmax` order: the gap the
route survives perturbation by (well-defined by `isLeastArgmax_unique`). -/
def gammaMargin {X : Type u} [MeasurableSpace X] {k : ℕ} (A : TemperedRouterFamily X k) (hk : 0 < k)
    (ρ : A.router.Ρ) (x : X) : ℝ :=
  A.router.score ρ x (leastArgmax (A.router.score ρ x) hk)
    - secondScore (A.router.score ρ x) (leastArgmax (A.router.score ρ x) hk)

/-- **The margin interior** at radius `g`: the inputs whose margin is at least `g` (the certifiable
region (both the `β`-shell complement and the `u`-shell complement live here at their respective radii). -/
def marginInterior {X : Type u} [MeasurableSpace X] {k : ℕ} (A : TemperedRouterFamily X k)
    (hk : 0 < k) (ρ : A.router.Ρ) (g : ℝ) : Set X :=
  {x | g ≤ gammaMargin A hk ρ x}

/-- **The β-shell** at radius `g`: the complement of the margin interior, the boundary layer where
mixture leakage is not yet exponentially small. -/
def betaShell {X : Type u} [MeasurableSpace X] {k : ℕ} (A : TemperedRouterFamily X k) (hk : 0 < k)
    (ρ : A.router.Ρ) (g : ℝ) : Set X :=
  {x | gammaMargin A hk ρ x < g}

/-- **The u-shell** at radius `r`: the inputs whose margin is below `r`, the same object as the
β-shell at a different radius. This is the float-margin band where the executed route may differ. -/
def uShell {X : Type u} [MeasurableSpace X] {k : ℕ} (A : TemperedRouterFamily X k) (hk : 0 < k)
    (ρ : A.router.Ρ) (r : ℝ) : Set X :=
  {x | gammaMargin A hk ρ x ≤ r}

/-! ## TD2: the two-sided per-layer leakage law -/

/-- **The off-route mass**: the total mixture weight on classes other than the hard route; the mixture
channel's deviation from the one-hot symbol channel. -/
def offRouteMass {X : Type u} [MeasurableSpace X] {k : ℕ} (A : TemperedRouterFamily X k) (hk : 0 < k)
    (ρ : A.router.Ρ) (x : X) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => i ≠ hardRoute A hk ρ x), softWeights A ρ x i

/-- **TD2 (upper): leakage decays margin-exponentially.** The off-route mass is at most
`(k−1)·exp(−β·γ)`: the softmax log-leakage is linear in the margin. -/
def TD2_leakage_upper {X : Type u} [MeasurableSpace X] {k : ℕ} (A : TemperedRouterFamily X k)
    (hk : 0 < k) : Prop :=
  ∀ (ρ : A.router.Ρ) (x : X),
    offRouteMass A hk ρ x ≤ ((k : ℝ) - 1) * Real.exp (-(A.β * gammaMargin A hk ρ x))

/-- **TD2 (lower): leakage is not faster than exponential.** With at least two experts (`2 ≤ k`),
the off-route mass is at least `exp(−β·γ)/k`: the second-place weight alone witnesses this bound, so
softmax cannot harden superexponentially. (At `k = 1` the off-route mass is identically `0`, the
degenerate single-expert endpoint with no routing.) -/
def TD2_leakage_lower {X : Type u} [MeasurableSpace X] {k : ℕ} (A : TemperedRouterFamily X k)
    (hk : 0 < k) : Prop :=
  2 ≤ k → ∀ (ρ : A.router.Ρ) (x : X),
    Real.exp (-(A.β * gammaMargin A hk ρ x)) / (k : ℝ) ≤ offRouteMass A hk ρ x

/-! ## TD7: float-symbol stability (the u-shell theorem) -/

/-- **TD7: the executed route equals the ideal route off the u-shell.** Whenever the per-coordinate
score-rounding budget `b` satisfies `2·b < γ` (the margin), the `leastArgmax` of any executed scores
`sExec` (within `b` of the exact scores) is exactly the hard route: the symbol channel decides exactly
on the margin interior. (The instance `b := scoreRndBudget` from `rdotBudget` applies at `IEEE32Exec`.) -/
def TD7_route_stable {X : Type u} [MeasurableSpace X] {k : ℕ} (A : TemperedRouterFamily X k)
    (hk : 0 < k) : Prop :=
  ∀ (ρ : A.router.Ρ) (x : X) (sExec : Fin k → ℝ) (b : ℝ),
    (∀ i, |sExec i - A.router.score ρ x i| ≤ b) → 2 * b < gammaMargin A hk ρ x →
    leastArgmax sExec hk = hardRoute A hk ρ x

end TLT.TemperedDesignLaw
