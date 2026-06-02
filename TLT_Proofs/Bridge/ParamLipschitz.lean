/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Parameter-Lipschitz envelope of a composed forward pass

For a covering-number bound on a parametric function class one needs the forward map to be Lipschitz
in its **weights**: `‖f_θ(x) − f_{θ'}(x)‖ ≤ L_param · ‖θ − θ'‖`, uniformly over a bounded input
domain. This is distinct from the input-Lipschitz constant of `ForwardEnvelope` (`lipProd`): there the
input varies at fixed weights; here the weights vary at fixed input.

A composed forward pass `f_θ = L_N(θ) ∘ ⋯ ∘ L_1(θ)` accumulates a weight perturbation through the same
recurrence as the rounding envelope. Perturbing layer `k`'s weights moves its output by
`paramLip_k · dist θ θ'`, and that displacement is then amplified by the *input*-Lipschitz constants of
the downstream layers, giving

`dist (paramComp Ls θ x) (paramComp Ls θ' x) ≤ (∑ₖ paramLip_k · ∏_{j>k} lip_j) · dist θ θ'`.

`paramLipBound` is exactly this sum — structurally identical to `ForwardEnvelope.envBound` with the
per-layer weight-Lipschitz constant in place of the rounding bound — and `paramComp_param_lipschitz`
is the resulting uniform Lipschitz estimate. The per-layer constants `paramLip` are supplied by the
concrete layer instances (attention, layer normalisation, feed-forward), where each is finite on the
relevant bounded domain.

## Main results

- `ParamLayer` — a weight-parametrised layer carrying its input- and weight-Lipschitz constants.
- `paramComp` / `inputLipProd` / `paramLipBound` — the parametric composition, the input-Lipschitz
  product, and the accumulated weight-Lipschitz envelope.
- `paramComp_input_lip` — the composed map is `inputLipProd`-Lipschitz in the input.
- `paramComp_param_lipschitz` — the composed map is `paramLipBound`-Lipschitz in the weights.
-/

namespace TLT

variable {Θ V : Type*} [PseudoMetricSpace Θ] [PseudoMetricSpace V]

/-- A forward-pass layer presented as a function of its weights `θ : Θ`, carrying the Lipschitz
constant `lip` of the layer map in its input and the Lipschitz constant `paramLip` of the layer map in
its weights (each uniform over the other argument on the relevant domain). -/
structure ParamLayer (Θ V : Type*) [PseudoMetricSpace Θ] [PseudoMetricSpace V] where
  /-- The layer map as a function of its weights. -/
  map : Θ → V → V
  /-- The Lipschitz constant of the layer map in its weights. -/
  paramLip : ℝ
  /-- The Lipschitz constant of the layer map in its input. -/
  lip : ℝ
  paramLip_nonneg : 0 ≤ paramLip
  lip_nonneg : 0 ≤ lip
  param_lipschitz : ∀ θ θ' y, dist (map θ y) (map θ' y) ≤ paramLip * dist θ θ'
  input_lipschitz : ∀ θ a b, dist (map θ a) (map θ b) ≤ lip * dist a b

/-- The parametric forward map: compose the weight-parametrised layer maps (list head applied first),
all reading the same shared weight vector `θ`. -/
def paramComp : List (ParamLayer Θ V) → Θ → V → V
  | [], _, x => x
  | L :: Ls, θ, x => paramComp Ls θ (L.map θ x)

/-- The product of the per-layer input-Lipschitz constants. -/
def inputLipProd : List (ParamLayer Θ V) → ℝ
  | [] => 1
  | L :: Ls => L.lip * inputLipProd Ls

/-- The accumulated weight-Lipschitz envelope `∑ₖ paramLip_k · ∏_{j>k} lip_j`. -/
def paramLipBound : List (ParamLayer Θ V) → ℝ
  | [] => 0
  | L :: Ls => L.paramLip * inputLipProd Ls + paramLipBound Ls

lemma inputLipProd_nonneg (Ls : List (ParamLayer Θ V)) : 0 ≤ inputLipProd Ls := by
  induction Ls with
  | nil => simp [inputLipProd]
  | cons L Ls ih => exact mul_nonneg L.lip_nonneg ih

lemma paramLipBound_nonneg (Ls : List (ParamLayer Θ V)) : 0 ≤ paramLipBound Ls := by
  induction Ls with
  | nil => simp [paramLipBound]
  | cons L Ls ih =>
    exact add_nonneg (mul_nonneg L.paramLip_nonneg (inputLipProd_nonneg Ls)) ih

/-- The composed parametric map is `inputLipProd`-Lipschitz in its input, at fixed weights. -/
lemma paramComp_input_lip (Ls : List (ParamLayer Θ V)) (θ : Θ) (a b : V) :
    dist (paramComp Ls θ a) (paramComp Ls θ b) ≤ inputLipProd Ls * dist a b := by
  induction Ls generalizing a b with
  | nil => simp [paramComp, inputLipProd]
  | cons L Ls ih =>
    calc dist (paramComp Ls θ (L.map θ a)) (paramComp Ls θ (L.map θ b))
        ≤ inputLipProd Ls * dist (L.map θ a) (L.map θ b) := ih _ _
      _ ≤ inputLipProd Ls * (L.lip * dist a b) :=
          mul_le_mul_of_nonneg_left (L.input_lipschitz θ a b) (inputLipProd_nonneg Ls)
      _ = inputLipProd (L :: Ls) * dist a b := by simp [inputLipProd]; ring

/-- **Parameter-Lipschitz envelope.** The composed parametric forward map is `paramLipBound`-Lipschitz
in its weights, uniformly over the input: `dist (f_θ x) (f_{θ'} x) ≤ paramLipBound Ls · dist θ θ'`.

The proof is the same telescoping recurrence as the rounding envelope: inserting the intermediate
point `paramComp Ls θ' (L.map θ x)` splits the head layer's weight perturbation (bounded by `L.paramLip
· dist θ θ'` and amplified by the downstream input-Lipschitz product) from the tail's contribution. -/
theorem paramComp_param_lipschitz (Ls : List (ParamLayer Θ V)) (θ θ' : Θ) (x : V) :
    dist (paramComp Ls θ x) (paramComp Ls θ' x) ≤ paramLipBound Ls * dist θ θ' := by
  induction Ls generalizing x with
  | nil => simp [paramComp, paramLipBound]
  | cons L Ls ih =>
    calc dist (paramComp Ls θ (L.map θ x)) (paramComp Ls θ' (L.map θ' x))
        ≤ dist (paramComp Ls θ (L.map θ x)) (paramComp Ls θ' (L.map θ x))
            + dist (paramComp Ls θ' (L.map θ x)) (paramComp Ls θ' (L.map θ' x)) := dist_triangle _ _ _
      _ ≤ paramLipBound Ls * dist θ θ' + inputLipProd Ls * (L.paramLip * dist θ θ') := by
          refine add_le_add (ih _) ?_
          calc dist (paramComp Ls θ' (L.map θ x)) (paramComp Ls θ' (L.map θ' x))
              ≤ inputLipProd Ls * dist (L.map θ x) (L.map θ' x) := paramComp_input_lip Ls θ' _ _
            _ ≤ inputLipProd Ls * (L.paramLip * dist θ θ') :=
                mul_le_mul_of_nonneg_left (L.param_lipschitz θ θ' x) (inputLipProd_nonneg Ls)
      _ = paramLipBound (L :: Ls) * dist θ θ' := by simp [paramLipBound]; ring

end TLT
