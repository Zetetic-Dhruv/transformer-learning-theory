/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.RegionTelescope

/-!
# Discharging the region condition (the forward-error / margin-slack coupling)

The region telescope `regionEnvelope_telescope` takes `trajInRegions` — "the executed trajectory stays in
the per-layer regions" — as a hypothesis. That condition is circular at face value: the executed point lies
in the region only because it is close to the ideal point, and it is close only because the per-layer
closeness applied (which needed region membership). This file breaks the circle with the standard slack
invariant, carried on the *ideal* trajectory (the smooth, well-defined side):

* `idealDeep Ls i δ` — the ideal trajectory from `i` stays *deep* in the regions: at each layer the closed
  ball around the ideal point, of radius the accumulated forward-error envelope, lies in that layer's region.
* `regionForward_slack` — if the executed input is within `δ` of the ideal input and `idealDeep` holds, then
  `trajInRegions` holds: a coupled induction where, at each layer, the slack places the executed point inside
  the region, the per-layer closeness then applies, and the error transports to the next layer.
* `regionEnvelope_telescope_of_idealDeep` — the envelope bound with `trajInRegions` now *discharged* from the
  ideal-side `idealDeep` condition, not assumed. The depth bound is conditional on a checkable property of
  the ideal trajectory rather than a self-referential property of the executed one.
-/

noncomputable section

namespace TLT.TemperedDesignLaw

variable {V : Type*} [PseudoMetricSpace V]

/-- The ideal trajectory from `i` stays deep in the regions: at each layer the closed ball around the ideal
point, of radius the accumulated forward-error envelope `δ`, lies in that layer's region; the radius grows
to `rnd + lip·δ` at the next layer. -/
def idealDeep : List (RegionExecLayer V) → V → ℝ → Prop
  | [], _, _ => True
  | L :: Ls, i, δ => (∀ z, dist z i ≤ δ → z ∈ L.region) ∧ idealDeep Ls (L.ideal i) (L.rnd + L.lip * δ)

/-- **Forward-error discharge of the region condition.** If the executed input is within `δ` of the ideal
input and the ideal trajectory stays deep in the regions, then the executed trajectory stays in the regions.
The coupled induction breaking the circularity: at each layer the executed point lies in the region (slack
plus the inherited `δ`-closeness), so the per-layer closeness applies and the error transports to
`rnd + lip·δ` at the next layer. -/
theorem regionForward_slack (Ls : List (RegionExecLayer V)) :
    ∀ (e i : V) (δ : ℝ), dist e i ≤ δ → idealDeep Ls i δ → trajInRegions Ls e := by
  induction Ls with
  | nil => intro e i δ _ _; trivial
  | cons L Ls ih =>
      intro e i δ hei hdeep
      obtain ⟨hball, hdeeptail⟩ := hdeep
      have he_reg : e ∈ L.region := hball e hei
      refine ⟨he_reg, ?_⟩
      refine ih (L.exec e) (L.ideal i) (L.rnd + L.lip * δ) ?_ hdeeptail
      calc dist (L.exec e) (L.ideal i)
          ≤ dist (L.exec e) (L.ideal e) + dist (L.ideal e) (L.ideal i) := dist_triangle _ _ _
        _ ≤ L.rnd + L.lip * δ :=
            add_le_add (L.exec_close_on e he_reg)
              ((L.ideal_lip e i).trans (mul_le_mul_of_nonneg_left hei L.lip_nonneg))

/-- **The envelope bound under the ideal-deep condition.** If the ideal trajectory from `x` stays deep in
the regions (by the accumulated envelope), the executed/ideal composition gap is at most `rEnvBound` — with
the region condition discharged from the ideal-side slack rather than assumed. -/
theorem regionEnvelope_telescope_of_idealDeep (Ls : List (RegionExecLayer V)) (x : V)
    (hdeep : idealDeep Ls x 0) :
    dist (rExecComp Ls x) (rIdealComp Ls x) ≤ rEnvBound Ls :=
  regionEnvelope_telescope Ls x (regionForward_slack Ls x x 0 (le_of_eq (dist_self x)) hdeep)

end TLT.TemperedDesignLaw
