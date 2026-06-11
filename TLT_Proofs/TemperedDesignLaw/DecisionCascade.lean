/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.Stability

/-!
# Decision exactness at depth (the u-edge composition)

The symbol map `y ↦ val y (route y)` is discontinuous at decision boundaries, so it carries no Lipschitz
constant and is not a `RegionExecLayer`. It is composed with a metric-free exact telescope instead.

Scope and honesty. The single non-trivial piece here is `regionMap_exact_telescope`, and even that is the
degenerate (zero-gap) case of the metric telescope `regionEnvelope_telescope`: a `propext`-only equality
induction with no error transport. The two `route*` facts are short corollaries of `TD7`
(`leastArgmax_stable_of_half_margin`) and of that telescope — proofs of three lines each. Crucially,
`trajInRegions` (the executed trajectory remains in the half-margin regions) is taken as a **hypothesis**:
discharging it is the genuinely hard u-edge content (it needs the per-layer forward-error coupling that
keeps the executed state close enough to the ideal for the margin to survive), and that is **not** done
here. So this file states the per-layer route stability lifted to depth *conditionally on* the margin
trajectory; it does not establish the trajectory condition.

* `RegionMapLayer` — a depth layer with an ideal map, an executed map, and a region (no metric).
* `regionMap_exact_telescope` — if every executed map equals its ideal on its region and the executed
  trajectory stays in the regions, the compositions coincide exactly.
* `routeRegionLayer` / `routeRegionLayer_exact_on_region` — the symbol layer, and the `TD7` corollary that
  the routes agree on the half-margin region.
* `routeCascade_replicate_exact` — the conditional depth-`L` statement: given the margin trajectory, the
  executed symbol cascade equals the ideal symbol cascade exactly.
-/

open scoped BigOperators

noncomputable section

namespace TLT.TemperedDesignLaw

/-- A metric-free depth layer: an ideal map, an executed map, and a region on which they are required to
agree. The decision-channel analogue of `RegionExecLayer`, with no Lipschitz structure (the symbol map is a
jump map). -/
structure RegionMapLayer (V : Type*) where
  /-- The ideal layer map. -/
  ideal : V → V
  /-- The executed layer map. -/
  exec : V → V
  /-- The region on which the executed map agrees with the ideal. -/
  region : Set V

variable {V : Type*}

/-- The executed composition (list head first). -/
def rmExecComp : List (RegionMapLayer V) → V → V
  | [], x => x
  | L :: Ls, x => rmExecComp Ls (L.exec x)

/-- The ideal composition (list head first). -/
def rmIdealComp : List (RegionMapLayer V) → V → V
  | [], x => x
  | L :: Ls, x => rmIdealComp Ls (L.ideal x)

/-- The executed trajectory stays in the per-layer regions. -/
def rmTrajInRegions : List (RegionMapLayer V) → V → Prop
  | [], _ => True
  | L :: Ls, x => x ∈ L.region ∧ rmTrajInRegions Ls (L.exec x)

/-- **The metric-free exact telescope.** If every executed map agrees with its ideal on its region and the
executed trajectory stays in the regions, the executed composition equals the ideal composition exactly. -/
theorem regionMap_exact_telescope (Ls : List (RegionMapLayer V)) :
    ∀ x, rmTrajInRegions Ls x → (∀ L ∈ Ls, ∀ y ∈ L.region, L.exec y = L.ideal y) →
      rmExecComp Ls x = rmIdealComp Ls x := by
  induction Ls with
  | nil => intro x _ _; rfl
  | cons L Ls ih =>
      intro x htraj hexact
      obtain ⟨hxreg, htrajtail⟩ := htraj
      have hLx : L.exec x = L.ideal x := hexact L (List.mem_cons.mpr (Or.inl rfl)) x hxreg
      rw [rmExecComp, rmIdealComp, hLx]
      rw [hLx] at htrajtail
      exact ih (L.ideal x) htrajtail (fun L' hL' => hexact L' (List.mem_cons.mpr (Or.inr hL')))

/-- **The symbol layer.** Ideal map routes by the exact scores; executed map routes by the rounded scores
`execScore`; the region is the half-margin interior `{|execScore − score| ≤ b at every head} ∩ {2b < γ}`. -/
def routeRegionLayer {k : ℕ} [NeZero k] {X : Type*} [MeasurableSpace X] (A : TemperedRouterFamily X k)
    (hk : 0 < k) (ρ : A.router.Ρ) (execScore : X → Fin k → ℝ) (val : X → Fin k → X) (b : ℝ) :
    RegionMapLayer X where
  ideal := fun y => val y (leastArgmax (A.router.score ρ y) hk)
  exec := fun y => val y (leastArgmax (execScore y) hk)
  region := {y | (∀ i, |execScore y i - A.router.score ρ y i| ≤ b) ∧ 2 * b < gammaMargin A hk ρ y}

/-- On the half-margin region the executed symbol map equals the ideal symbol map: the rounded-score route
equals the exact-score route by `TD7` (`leastArgmax_stable_of_half_margin`), so the selected payloads agree. -/
lemma routeRegionLayer_exact_on_region {k : ℕ} [NeZero k] {X : Type*} [MeasurableSpace X]
    (A : TemperedRouterFamily X k) (hk : 0 < k) (ρ : A.router.Ρ) (execScore : X → Fin k → ℝ)
    (val : X → Fin k → X) (b : ℝ) :
    ∀ y ∈ (routeRegionLayer A hk ρ execScore val b).region,
      (routeRegionLayer A hk ρ execScore val b).exec y =
        (routeRegionLayer A hk ρ execScore val b).ideal y := by
  intro y hy
  obtain ⟨hbudget, hmargin⟩ := hy
  exact congrArg (val y)
    (leastArgmax_stable_of_half_margin (A.router.score ρ y) (execScore y) hk hbudget hmargin)

/-- **Conditional decision exactness at depth.** For a depth-`L` homogeneous symbol cascade, *given* that
the executed trajectory stays in the half-margin regions (`trajInRegions`, not established here), the
executed symbol cascade equals the ideal symbol cascade exactly. A short corollary of `TD7` and
`regionMap_exact_telescope`; the unconditional statement awaits the forward-error discharge of the margin
trajectory. -/
theorem routeCascade_replicate_exact {k : ℕ} [NeZero k] {X : Type*} [MeasurableSpace X]
    (A : TemperedRouterFamily X k) (hk : 0 < k) (ρ : A.router.Ρ) (execScore : X → Fin k → ℝ)
    (val : X → Fin k → X) (b : ℝ) (L : ℕ) (x : X)
    (htraj : rmTrajInRegions (List.replicate L (routeRegionLayer A hk ρ execScore val b)) x) :
    rmExecComp (List.replicate L (routeRegionLayer A hk ρ execScore val b)) x =
      rmIdealComp (List.replicate L (routeRegionLayer A hk ρ execScore val b)) x := by
  refine regionMap_exact_telescope _ x htraj (fun L' hL' => ?_)
  rw [(List.mem_replicate.mp hL').2]
  exact routeRegionLayer_exact_on_region A hk ρ execScore val b

end TLT.TemperedDesignLaw
