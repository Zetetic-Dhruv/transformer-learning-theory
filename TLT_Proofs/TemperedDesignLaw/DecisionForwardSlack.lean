/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.DecisionCascade

/-!
# Discharging the decision-edge region condition (the exact case)

The metric edge discharges `trajInRegions` via the forward-error slack (`regionForward_slack`). The decision
edge is the *exact* corner, and there the discharge is cleaner: on the region the executed map equals the
ideal map, so once the **ideal** route trajectory stays in the regions the executed trajectory *coincides*
with it — there is no error to track, hence no slack. This removes the self-referential `trajInRegions`
hypothesis from the decision cascade, leaving a condition on the smooth ideal trajectory.

* `rmIdealTrajInRegions` — the ideal trajectory stays in the per-layer regions.
* `rmTrajInRegions_of_ideal` — ideal trajectory in regions + per-layer exactness ⟹ executed trajectory in
  regions (the two trajectories coincide).
* `routeCascade_exact_of_ideal` — depth-`L` decision exactness conditioned on the **ideal** route trajectory
  staying in the half-margin regions: the executed symbol cascade equals the ideal symbol cascade.
-/

noncomputable section

namespace TLT.TemperedDesignLaw

variable {V : Type*}

/-- The ideal trajectory stays in the per-layer regions. -/
def rmIdealTrajInRegions : List (RegionMapLayer V) → V → Prop
  | [], _ => True
  | L :: Ls, x => x ∈ L.region ∧ rmIdealTrajInRegions Ls (L.ideal x)

/-- **Exact-case discharge of the executed region condition.** If the ideal trajectory stays in the regions
and each executed map agrees with its ideal on its region, then the executed trajectory stays in the regions
— it coincides with the ideal trajectory exactly. The decision-edge analogue of `regionForward_slack`; here
exactness makes the trajectories coincide outright, with no forward-error slack. -/
theorem rmTrajInRegions_of_ideal (Ls : List (RegionMapLayer V)) :
    ∀ x, rmIdealTrajInRegions Ls x → (∀ L ∈ Ls, ∀ y ∈ L.region, L.exec y = L.ideal y) →
      rmTrajInRegions Ls x := by
  induction Ls with
  | nil => intro x _ _; trivial
  | cons L Ls ih =>
      intro x hideal hexact
      obtain ⟨hxreg, hidealtail⟩ := hideal
      refine ⟨hxreg, ?_⟩
      have hLx : L.exec x = L.ideal x := hexact L (List.mem_cons.mpr (Or.inl rfl)) x hxreg
      rw [hLx]
      exact ih (L.ideal x) hidealtail (fun L' hL' => hexact L' (List.mem_cons.mpr (Or.inr hL')))

/-- **Decision exactness at depth, conditioned on the ideal trajectory.** Given that the *ideal* route
trajectory stays in the half-margin regions, the executed symbol cascade equals the ideal symbol cascade —
the executed region condition is now discharged from the (smooth) ideal trajectory rather than assumed. -/
theorem routeCascade_exact_of_ideal {k : ℕ} [NeZero k] {X : Type*} [MeasurableSpace X]
    (A : TemperedRouterFamily X k) (hk : 0 < k) (ρ : A.router.Ρ) (execScore : X → Fin k → ℝ)
    (val : X → Fin k → X) (b : ℝ) (L : ℕ) (x : X)
    (hideal : rmIdealTrajInRegions (List.replicate L (routeRegionLayer A hk ρ execScore val b)) x) :
    rmExecComp (List.replicate L (routeRegionLayer A hk ρ execScore val b)) x =
      rmIdealComp (List.replicate L (routeRegionLayer A hk ρ execScore val b)) x := by
  have hexact : ∀ L' ∈ List.replicate L (routeRegionLayer A hk ρ execScore val b),
      ∀ y ∈ L'.region, L'.exec y = L'.ideal y := fun L' hL' => by
    rw [(List.mem_replicate.mp hL').2]; exact routeRegionLayer_exact_on_region A hk ρ execScore val b
  exact regionMap_exact_telescope _ x (rmTrajInRegions_of_ideal _ x hideal hexact) hexact

end TLT.TemperedDesignLaw
