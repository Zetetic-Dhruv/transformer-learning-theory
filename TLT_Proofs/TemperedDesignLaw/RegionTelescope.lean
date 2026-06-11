/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.Conjectures

/-!
# The region-restricted depth telescope (the keystone for the conditional-closeness edges)

The shipped forward telescope (`execComp_envelope`) composes layers whose per-layer closeness holds
*everywhere*. Both the tempered hardening edge (closeness only on the margin interior) and the float
margin edge (the executed route equals the ideal route only off the `u`-shell) need the *conditional*
version: per-layer closeness holds only on a region `Dₗ`, and the bound holds provided the executed
trajectory stays inside the regions.

This file states that abstraction once, for any region-restricted layer stack:

* `RegionExecLayer` — a layer with an ideal map, an executed map, a Lipschitz constant, a rounding bound,
  and a **region**; closeness `exec ≈ ideal` is required only *on the region*.
* `trajInRegions` — the executed trajectory stays in the per-layer regions.
* `regionEnvelope_telescope` — under `trajInRegions`, the executed/ideal composition gap is at most the
  same `rEnvBound` telescope `∑ₖ rndₖ · ∏_{j>k} lipⱼ`.

The intricate margin-to-region step (the executed point lies in `Dₗ` because the ideal point has margin
above the accumulated envelope) is factored *out* into the `trajInRegions` hypothesis, which the concrete
edges discharge from their margin geometry. The telescope itself is then the standard induction — the one
abstraction both edges share.
-/

noncomputable section

namespace TLT.TemperedDesignLaw

variable {V : Type*} [PseudoMetricSpace V]

/-- A depth layer whose executed map is close to its ideal map **only on a region** `region`. The
conditional-closeness analogue of the shipped `ExecLayer`. -/
structure RegionExecLayer (V : Type*) [PseudoMetricSpace V] where
  /-- The ideal (exact) layer map. -/
  ideal : V → V
  /-- The executed layer map. -/
  exec : V → V
  /-- The Lipschitz constant of the ideal map. -/
  lip : ℝ
  /-- The local rounding bound between executed and ideal, valid on `region`. -/
  rnd : ℝ
  /-- The region on which the executed map is close to the ideal. -/
  region : Set V
  /-- The Lipschitz constant is nonnegative. -/
  lip_nonneg : 0 ≤ lip
  /-- The ideal map is `lip`-Lipschitz. -/
  ideal_lip : ∀ a b, dist (ideal a) (ideal b) ≤ lip * dist a b
  /-- Executed-ideal closeness holds on the region. -/
  exec_close_on : ∀ y ∈ region, dist (exec y) (ideal y) ≤ rnd

/-- The executed forward map: compose the executed layer maps (list head first). -/
def rExecComp : List (RegionExecLayer V) → V → V
  | [], x => x
  | L :: Ls, x => rExecComp Ls (L.exec x)

/-- The ideal forward map: compose the ideal layer maps (list head first). -/
def rIdealComp : List (RegionExecLayer V) → V → V
  | [], x => x
  | L :: Ls, x => rIdealComp Ls (L.ideal x)

/-- The product of the per-layer ideal-Lipschitz constants. -/
def rLipProd : List (RegionExecLayer V) → ℝ
  | [] => 1
  | L :: Ls => L.lip * rLipProd Ls

/-- The accumulated rounding envelope `∑ₖ rndₖ · ∏_{j>k} lipⱼ`. -/
def rEnvBound : List (RegionExecLayer V) → ℝ
  | [] => 0
  | L :: Ls => L.rnd * rLipProd Ls + rEnvBound Ls

/-- The executed trajectory stays inside the per-layer regions (each prefix-executed point lies in the
next layer's region). -/
def trajInRegions : List (RegionExecLayer V) → V → Prop
  | [], _ => True
  | L :: Ls, x => x ∈ L.region ∧ trajInRegions Ls (L.exec x)

lemma rLipProd_nonneg (Ls : List (RegionExecLayer V)) : 0 ≤ rLipProd Ls := by
  induction Ls with
  | nil => simp [rLipProd]
  | cons L Ls ih => rw [rLipProd]; exact mul_nonneg L.lip_nonneg ih

/-- The ideal composition is `rLipProd`-Lipschitz. -/
lemma rIdealComp_lip (Ls : List (RegionExecLayer V)) (a b : V) :
    dist (rIdealComp Ls a) (rIdealComp Ls b) ≤ rLipProd Ls * dist a b := by
  induction Ls generalizing a b with
  | nil => simp [rIdealComp, rLipProd]
  | cons L Ls ih =>
      calc dist (rIdealComp (L :: Ls) a) (rIdealComp (L :: Ls) b)
          = dist (rIdealComp Ls (L.ideal a)) (rIdealComp Ls (L.ideal b)) := by rw [rIdealComp, rIdealComp]
        _ ≤ rLipProd Ls * dist (L.ideal a) (L.ideal b) := ih _ _
        _ ≤ rLipProd Ls * (L.lip * dist a b) :=
              mul_le_mul_of_nonneg_left (L.ideal_lip a b) (rLipProd_nonneg Ls)
        _ = rLipProd (L :: Ls) * dist a b := by rw [rLipProd]; ring

/-- **The region-restricted depth telescope.** Provided the executed trajectory stays inside the per-layer
regions, the executed/ideal composition gap is at most the rounding envelope `rEnvBound`. The conditional-
closeness abstraction shared by the tempered-hardening edge and the float-margin edge. -/
theorem regionEnvelope_telescope (Ls : List (RegionExecLayer V)) :
    ∀ (x : V), trajInRegions Ls x →
      dist (rExecComp Ls x) (rIdealComp Ls x) ≤ rEnvBound Ls := by
  induction Ls with
  | nil => intro x _; simp [rExecComp, rIdealComp, rEnvBound]
  | cons L Ls ih =>
      intro x htraj
      obtain ⟨hxreg, htrajtail⟩ := htraj
      calc dist (rExecComp (L :: Ls) x) (rIdealComp (L :: Ls) x)
          = dist (rExecComp Ls (L.exec x)) (rIdealComp Ls (L.ideal x)) := by
            rw [rExecComp, rIdealComp]
        _ ≤ dist (rExecComp Ls (L.exec x)) (rIdealComp Ls (L.exec x))
            + dist (rIdealComp Ls (L.exec x)) (rIdealComp Ls (L.ideal x)) := dist_triangle _ _ _
        _ ≤ rEnvBound Ls + rLipProd Ls * L.rnd :=
              add_le_add (ih (L.exec x) htrajtail)
                ((rIdealComp_lip Ls (L.exec x) (L.ideal x)).trans
                  (mul_le_mul_of_nonneg_left (L.exec_close_on x hxreg) (rLipProd_nonneg Ls)))
        _ = rEnvBound (L :: Ls) := by rw [rEnvBound]; ring

end TLT.TemperedDesignLaw
