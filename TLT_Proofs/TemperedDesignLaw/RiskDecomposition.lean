/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.RouteFactoredLoss

/-!
# The three-source pointwise risk decomposition (TD12)

The tempered design law lives on a square with four corners (ideal/float × soft/hard). At the
*float-soft* corner (the corner the IEEE executable transformer actually occupies), the loss
decomposes, by one triangle step through the *ideal-hard* corner, into three named sources:

1. the **route term** `loss(idealHard, y)`: the statistical risk of the hard route (priced by
   TD10/TD11);
2. the **float source** `Lℓ · uEdge`: the precision (`u`-edge) envelope, `Lℓ` times the executed-vs-ideal
   distance;
3. the **hardening source** `Lℓ · βEdge`: the sharpness (`β`-edge) leakage, `Lℓ` times the
   ideal-soft-vs-hard distance.

`risk_threeSource_pointwise` is this decomposition, pointwise on the corner region, for any
`RouteFactoredLoss` (TD0.5) once the two edge envelopes are supplied. It is the system-level
identity that prices the whole machine; the expectation-level statement (integrating over the corner
interior and the two shells) consumes the shell-mass control, and the confident-misroute corollary
consumes the executed-equals-ideal route transfer; both kept as downstream consumers of this kernel.
-/

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The three-source pointwise risk decomposition.** For a route-factored loss `Φ`, the loss at the
float-soft point `p` is at most the loss at the ideal-hard point `r` plus `Φ.Lℓ` times the sum of the
two edge envelopes: the precision edge `‖p − q‖ ≤ uEdge` (executed vs ideal-soft `q`) and the
hardening edge `‖q − r‖ ≤ βEdge` (ideal-soft vs ideal-hard). One Lipschitz step plus the triangle
inequality through the ideal-soft midpoint; the three summands are the route term `Φ.loss r y`, the
float source `Φ.Lℓ · uEdge`, and the hardening source `Φ.Lℓ · βEdge`. -/
theorem risk_threeSource_pointwise {V : Type*} [NormedAddCommGroup V] {Y : Type*}
    (Φ : RouteFactoredLoss V Y) (p q r : V) (y : Y) {uEdge βEdge : ℝ}
    (hu : ‖p - q‖ ≤ uEdge) (hβ : ‖q - r‖ ≤ βEdge) :
    Φ.loss p y ≤ Φ.loss r y + Φ.Lℓ * (uEdge + βEdge) := by
  have hlip := abs_le.mp (Φ.loss_lipschitz y p r)
  have htri : ‖p - r‖ ≤ uEdge + βEdge := by
    calc ‖p - r‖ = ‖(p - q) + (q - r)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖p - q‖ + ‖q - r‖ := norm_add_le _ _
      _ ≤ uEdge + βEdge := by linarith
  have hL : Φ.Lℓ * ‖p - r‖ ≤ Φ.Lℓ * (uEdge + βEdge) :=
    mul_le_mul_of_nonneg_left htri Φ.Lℓ_nonneg
  linarith [hlip.2]

end TLT.TemperedDesignLaw
