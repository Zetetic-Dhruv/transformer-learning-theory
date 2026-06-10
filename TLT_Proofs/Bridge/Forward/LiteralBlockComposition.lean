/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Per-input literal-block forward-error composition

The literal forward error of each transformer sub-block — attention (`attnLiteralForwardError`), the FFN
(`ffnExec_forward_error`), layer-norm — is a *per-input* bound, conditional on that block's run-time
no-overflow bundle. Composing them into a stack forward error is a pointwise telescope: the executed
composite is within `(this block's rounding) + (its ideal Lipschitz)·(everything upstream)` of the ideal
composite.

These primitives compose two and three blocks pointwise. The depth-`L` list version is the shipped
`execComp_envelope` once each block is wrapped as an `ExecLayer` over its operating regime; these
pointwise forms are what the *per-input* literal bindings (which carry their bundle as a hypothesis on
the specific input) telescope through directly, without first uniformising over a ball.
-/

namespace TLT.LitCompose

variable {U V W X : Type*} [PseudoMetricSpace U] [PseudoMetricSpace V] [PseudoMetricSpace W]
  [PseudoMetricSpace X]

/-- **Two-block pointwise forward error.** If the first block's executed map is within `ρf` of its ideal
at `x`, the second block's executed map is within `ρg` of its ideal at the executed intermediate
`fE x`, and the second block's ideal is `Λg`-Lipschitz, then the composite executed map is within
`ρg + Λg·ρf` of the composite ideal at `x`. The downstream block amplifies upstream rounding by its
Lipschitz constant — the envelope's recursion, one step. -/
theorem block2_forward_error (fE fI : U → V) (gE gI : V → W) (x : U) {ρf ρg Λg : ℝ}
    (hΛg : 0 ≤ Λg) (hf : dist (fE x) (fI x) ≤ ρf)
    (hg : dist (gE (fE x)) (gI (fE x)) ≤ ρg)
    (hgLip : ∀ a b, dist (gI a) (gI b) ≤ Λg * dist a b) :
    dist (gE (fE x)) (gI (fI x)) ≤ ρg + Λg * ρf :=
  calc dist (gE (fE x)) (gI (fI x))
      ≤ dist (gE (fE x)) (gI (fE x)) + dist (gI (fE x)) (gI (fI x)) := dist_triangle _ _ _
    _ ≤ ρg + Λg * dist (fE x) (fI x) := add_le_add hg (hgLip _ _)
    _ ≤ ρg + Λg * ρf := by gcongr

/-- **Three-block pointwise forward error** (e.g. attention → FFN → layer-norm in one transformer
block). The middle and top blocks amplify everything upstream by their ideal Lipschitz constants:
`ρh + Λh·ρg + Λh·Λg·ρf`. -/
theorem block3_forward_error (fE fI : U → V) (gE gI : V → W) (hE hI : W → X) (x : U)
    {ρf ρg ρh Λg Λh : ℝ} (hΛg : 0 ≤ Λg) (hΛh : 0 ≤ Λh)
    (hf : dist (fE x) (fI x) ≤ ρf)
    (hg : dist (gE (fE x)) (gI (fE x)) ≤ ρg)
    (hh : dist (hE (gE (fE x))) (hI (gE (fE x))) ≤ ρh)
    (hgLip : ∀ a b, dist (gI a) (gI b) ≤ Λg * dist a b)
    (hhLip : ∀ a b, dist (hI a) (hI b) ≤ Λh * dist a b) :
    dist (hE (gE (fE x))) (hI (gI (fI x))) ≤ ρh + Λh * (ρg + Λg * ρf) := by
  have hgComp : dist (gE (fE x)) (gI (fI x)) ≤ ρg + Λg * ρf :=
    block2_forward_error fE fI gE gI x hΛg hf hg hgLip
  calc dist (hE (gE (fE x))) (hI (gI (fI x)))
      ≤ dist (hE (gE (fE x))) (hI (gE (fE x))) + dist (hI (gE (fE x))) (hI (gI (fI x))) :=
        dist_triangle _ _ _
    _ ≤ ρh + Λh * (ρg + Λg * ρf) := add_le_add hh (le_trans (hhLip _ _) (by gcongr))

end TLT.LitCompose
