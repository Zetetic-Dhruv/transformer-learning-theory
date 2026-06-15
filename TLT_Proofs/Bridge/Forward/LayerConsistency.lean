/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Lipschitz.ParameterPerturbationEnvelope
import TLT_Proofs.Bridge.Forward.ForwardEnvelope

/-!
# Consistency of the parametric and executed forward views

The forward pass is described two ways: as a `ParamLayer` list whose maps vary with the weights `θ`
(the capacity-side view, where the parameter dependence is the object of study), and as an
`ExecLayer` list whose ideal maps are fixed functions (the certificate-side view, where the rounding
envelope is the object of study). These are the same forward map seen from two angles, and keeping
them in agreement by hand is a recurring source of friction.

`ParamLayer.toExecLayer` freezes a `ParamLayer` at a chosen weight, producing the corresponding
ideal `ExecLayer`, and `idealComp_toExecLayer` is the resulting identity: the executed-view ideal
composition of the frozen layers equals the parametric composition at that weight. This makes the
two views provably interchangeable, so the capacity bound (stated over `paramComp`) and the
certificate (stated over `idealComp`) refer to the same model at the executed network's weights.

## Main results

- `idealComp_toExecLayer`: the ideal composition of weight-frozen `ParamLayer`s equals `paramComp`.
-/

/-!
## References
- [36] input-Lipschitz constant of a layer; internal parametric↔executed view bridge.
-/

namespace TLT

variable {Θ V : Type*} [PseudoMetricSpace Θ] [PseudoMetricSpace V]

/-- Freeze a `ParamLayer` at the weight `θ`, viewing it as an ideal `ExecLayer` (no rounding): its
ideal and executed maps are both `P.map θ`, and its ideal Lipschitz constant is the layer's
input-Lipschitz constant. -/
def ParamLayer.toExecLayer (P : ParamLayer Θ V) (θ : Θ) : ExecLayer V where
  ideal := P.map θ
  exec := P.map θ
  lip := P.lip
  rnd := 0
  lip_nonneg := P.lip_nonneg
  ideal_lip := P.input_lipschitz θ
  exec_close := fun y => by simp

@[simp] lemma ParamLayer.toExecLayer_ideal (P : ParamLayer Θ V) (θ : Θ) :
    (P.toExecLayer θ).ideal = P.map θ := rfl

/-- **Parametric/executed forward consistency.** The executed-view ideal composition of the layers
frozen at the weight `θ` equals the parametric composition at `θ`. The two forward descriptions are
the same map. -/
theorem idealComp_toExecLayer (Ps : List (ParamLayer Θ V)) (θ : Θ) (x : V) :
    idealComp (Ps.map (·.toExecLayer θ)) x = paramComp Ps θ x := by
  induction Ps generalizing x with
  | nil => rfl
  | cons P Ps ih =>
      simp only [List.map_cons, idealComp, paramComp, ParamLayer.toExecLayer_ideal]
      exact ih (P.map θ x)

end TLT
