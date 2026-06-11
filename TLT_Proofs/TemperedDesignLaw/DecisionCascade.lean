/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.Stability

/-!
# Decision exactness at depth (the u-edge, transcendental-free)

The symbol channel is a *jump* map — `y ↦ val y (route y)` is discontinuous at decision boundaries, so it
carries no Lipschitz constant and does not fit the metric region telescope. But it does not need one: off
the `u`-shell the executed route equals the ideal route *exactly* (route stability, `TD7`), so the executed
and ideal symbol cascades coincide exactly — a pure equality induction over a metric-free layer:

* `RegionMapLayer` — a depth layer with an ideal map, an executed map, and a region (no metric).
* `regionMap_exact_telescope` — if every executed map equals its ideal on its region and the executed
  trajectory stays in the regions, the compositions coincide exactly.
* `routeRegionLayer` / `routeRegionLayer_exact_on_region` — the symbol layer: ideal route from the exact
  scores, executed route from the rounded scores; on the region where the score perturbation is below half
  the margin, the two routes (hence the two maps) agree, discharged by `TD7`.
* `routeCascade_replicate_exact` — the depth-`L` decision exactness: the executed symbol cascade equals the
  ideal symbol cascade exactly on the joint margin interior. No transcendental, kernel-decidable — the
  carrier-tower fixed point of the `u`-edge.
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

/-- **Decision exactness at depth (u-edge).** A depth-`L` homogeneous symbol cascade: on the joint margin
interior (the executed trajectory stays in the half-margin regions) the executed symbol cascade equals the
ideal symbol cascade **exactly** — no transcendental, kernel-decidable. The carrier-tower fixed point. -/
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
