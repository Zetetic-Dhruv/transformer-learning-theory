/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.RegionTelescopeLinear
import TLT_Proofs.TemperedDesignLaw.HardeningEnvelope

/-!
# The tempered hardening layer as a region-exec layer (the keystone's payoff, TD3-depth)

The per-layer hardening atom (`softMixture_sub_hardPayload_le_exp`) is packaged as a `RegionExecLayer`
whose **ideal** is the soft mixture map (smooth, Lipschitz) and whose **executed** map is the hard route
(a jump map, within the hardening budget of the soft map on the margin interior). The `exec_close_on`
field is discharged from the atom via margin-interior monotonicity. A stack of these inherits the
depth-`L` hardening envelope from `regionEnvelope_telescope_linear`:

> for tempered layers with non-expansive soft maps (`Lsoft ≤ 1`) and margin interiors `{γ ≥ g}` as regions,
> if the executed (hard-route) trajectory stays in the margin interiors, then
> `dist (hardCascade x) (softCascade x) ≤ L · (k−1)·exp(−β·g)·D`.

This is TD3-depth: the depth-`L` hardening envelope on the joint margin interior, assembled from the
per-layer atom and the region telescope keystone, with `β` playing the role of precision analogously to the
rounding envelope at the `u`-edge.
-/

open scoped BigOperators

universe u

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The tempered hardening layer as a `RegionExecLayer`.** Ideal = the soft mixture map (Lipschitz with the
supplied constant `Lsoft`); executed = the hard-route payload map; region = the margin interior `{γ ≥ g}`;
local rounding bound `rnd = (k−1)·exp(−β·g)·D`. The `exec_close_on` obligation is discharged by the per-layer
hardening atom together with the margin-interior monotonicity of the envelope. -/
def temperedHardeningRegionLayer {k : ℕ} [NeZero k] {V : Type u} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [MeasurableSpace V] (A : TemperedRouterFamily V k) (hk : 0 < k)
    (ρ : A.router.Ρ) (val : V → Fin k → V) (g D Lsoft : ℝ) (hLsoft : 0 ≤ Lsoft)
    (hk1 : 0 ≤ (k : ℝ) - 1) (hD0 : 0 ≤ D)
    (hsoftLip : ∀ a b, dist (mixtureOutput (softWeights A ρ a) (val a))
      (mixtureOutput (softWeights A ρ b) (val b)) ≤ Lsoft * dist a b)
    (hD : ∀ y i, ‖val y i - val y (hardRoute A hk ρ y)‖ ≤ D) : RegionExecLayer V where
  ideal := fun y => mixtureOutput (softWeights A ρ y) (val y)
  exec := fun y => val y (hardRoute A hk ρ y)
  lip := Lsoft
  rnd := ((k : ℝ) - 1) * Real.exp (-(A.β * g)) * D
  region := {y | g ≤ gammaMargin A hk ρ y}
  lip_nonneg := hLsoft
  ideal_lip := hsoftLip
  exec_close_on := by
    intro y hy
    rw [dist_comm, dist_eq_norm]
    refine (softMixture_sub_hardPayload_le_exp A hk ρ y (val y) (hD y)).trans ?_
    apply mul_le_mul_of_nonneg_right _ hD0
    apply mul_le_mul_of_nonneg_left _ hk1
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hy A.hβ))

end TLT.TemperedDesignLaw
