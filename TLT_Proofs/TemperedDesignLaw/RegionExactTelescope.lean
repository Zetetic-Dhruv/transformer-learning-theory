/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.RegionTelescope

/-!
# The exact region telescope (the decision-channel depth engine, `rnd = 0`)

The metric region telescope bounds the executed/ideal gap by the rounding envelope. At the `u`-edge the
per-layer gap is not merely small but *exactly zero* on the region: off the `u`-shell the executed route
equals the ideal route (route stability, `TD7`). When the local gap is exact, the composition is exact —
no Lipschitz transport, no envelope, a pure equality induction:

* `regionExact_telescope` — if every executed map equals its ideal map *on its region* and the executed
  trajectory stays in the regions, then the executed composition equals the ideal composition exactly.

Instantiated at a stack whose per-layer maps coincide off the `u`-shell, this is **decision exactness at
depth**: the executed symbol cascade equals the ideal symbol cascade exactly on the joint margin interior —
the discrete, transcendental-free fixed point of the carrier tower (the `ρ = 0` corner of the region
telescope).
-/

noncomputable section

namespace TLT.TemperedDesignLaw

variable {V : Type*} [PseudoMetricSpace V]

/-- **The exact region telescope.** If every executed layer map agrees with its ideal map on its region,
and the executed trajectory stays in the per-layer regions, then the executed composition equals the ideal
composition exactly. The `rnd = 0` corner of `regionEnvelope_telescope` — decision exactness at depth, with
no metric transport. -/
theorem regionExact_telescope (Ls : List (RegionExecLayer V)) :
    ∀ (x : V), trajInRegions Ls x → (∀ L ∈ Ls, ∀ y ∈ L.region, L.exec y = L.ideal y) →
      rExecComp Ls x = rIdealComp Ls x := by
  induction Ls with
  | nil => intro x _ _; rfl
  | cons L Ls ih =>
      intro x htraj hexact
      obtain ⟨hxreg, htrajtail⟩ := htraj
      have hLx : L.exec x = L.ideal x := hexact L (List.mem_cons.mpr (Or.inl rfl)) x hxreg
      rw [rExecComp, rIdealComp, hLx]
      rw [hLx] at htrajtail
      exact ih (L.ideal x) htrajtail (fun L' hL' => hexact L' (List.mem_cons.mpr (Or.inr hL')))

end TLT.TemperedDesignLaw
