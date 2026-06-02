/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Parameter-Lipschitz composition over bounded weight and activation domains

A weight-parametrised forward map has *no* uniform Lipschitz constants: a linear layer's
input-Lipschitz constant scales with the magnitude of its weights, and its weight-Lipschitz constant
scales with the magnitude of the activation it multiplies. Both estimates are therefore conditional —
the input-Lipschitz bound holds for weights in an admissible set `K`, and the weight-Lipschitz bound
holds for activations in a forward-invariant set `D`. Neither is a field of the layer; both are
supplied at composition time with their domains.

`ParamLayerLocal` carries only the layer map and its nominal constants. `lparamComp` folds the
layers, `lparamComp_input_lip_on` is the conditional input-Lipschitz estimate (for weights in `K`),
and `paramComp_param_lipschitz_on` is the conditional weight-Lipschitz envelope
`∑ₖ paramLipₖ · ∏_{j>k} lipⱼ` (for weights in `K`, activations in the forward-invariant `D`). The
forward-invariance of `D` is the activation cap a layer-normalised architecture provides per block.

## Main definitions

- `ParamLayerLocal` — a weight-parametrised layer with nominal input- and weight-Lipschitz constants.
- `lparamComp` / `linputLipProd` / `lparamLipBound` — the composition and its Lipschitz envelopes.

## Main results

- `lparamComp_input_lip_on` — the composed map is `linputLipProd`-Lipschitz in the input, for weights
  in `K`.
- `paramComp_param_lipschitz_on` — the weight-Lipschitz envelope, for weights in `K` and activations
  in a forward-invariant `D`.
-/

namespace TLT

variable {Θ V : Type*} [PseudoMetricSpace Θ] [PseudoMetricSpace V]

/-- A weight-parametrised layer carrying its map and nominal Lipschitz constants `lip` (input) and
`paramLip` (weight); the constants are valid only on the admissible weight/activation domains, which
are supplied at composition time (see `paramComp_param_lipschitz_on`). -/
structure ParamLayerLocal (Θ V : Type*) [PseudoMetricSpace Θ] [PseudoMetricSpace V] where
  /-- The layer map as a function of its weights. -/
  map : Θ → V → V
  /-- The weight-Lipschitz constant (valid on the bounded activation domain). -/
  paramLip : ℝ
  /-- The input-Lipschitz constant (valid on the admissible weight domain). -/
  lip : ℝ
  paramLip_nonneg : 0 ≤ paramLip
  lip_nonneg : 0 ≤ lip

/-- The parametric forward map: compose the layer maps threading the same weights (head first). -/
def lparamComp : List (ParamLayerLocal Θ V) → Θ → V → V
  | [], _, x => x
  | L :: Ls, θ, x => lparamComp Ls θ (L.map θ x)

/-- The product of the per-layer input-Lipschitz constants. -/
def linputLipProd : List (ParamLayerLocal Θ V) → ℝ
  | [] => 1
  | L :: Ls => L.lip * linputLipProd Ls

/-- The accumulated weight-Lipschitz envelope `∑ₖ paramLip_k · ∏_{j>k} lip_j`. -/
def lparamLipBound : List (ParamLayerLocal Θ V) → ℝ
  | [] => 0
  | L :: Ls => L.paramLip * linputLipProd Ls + lparamLipBound Ls

lemma linputLipProd_nonneg (Ls : List (ParamLayerLocal Θ V)) : 0 ≤ linputLipProd Ls := by
  induction Ls with
  | nil => simp [linputLipProd]
  | cons L Ls ih => simp only [linputLipProd]; exact mul_nonneg L.lip_nonneg ih

lemma lparamLipBound_nonneg (Ls : List (ParamLayerLocal Θ V)) : 0 ≤ lparamLipBound Ls := by
  induction Ls with
  | nil => simp [lparamLipBound]
  | cons L Ls ih =>
      simp only [lparamLipBound]
      exact add_nonneg (mul_nonneg L.paramLip_nonneg (linputLipProd_nonneg Ls)) ih

/-- **Conditional input-Lipschitz of the composition.** For weights `θ` in the admissible set `K` on
which each layer's input-Lipschitz estimate holds, the composed map is `linputLipProd`-Lipschitz in
the input. -/
lemma lparamComp_input_lip_on {K : Set Θ} (Ls : List (ParamLayerLocal Θ V))
    (hin : ∀ L ∈ Ls, ∀ θ ∈ K, ∀ a b, dist (L.map θ a) (L.map θ b) ≤ L.lip * dist a b)
    {θ : Θ} (hθ : θ ∈ K) (a b : V) :
    dist (lparamComp Ls θ a) (lparamComp Ls θ b) ≤ linputLipProd Ls * dist a b := by
  induction Ls generalizing a b with
  | nil => simp [lparamComp, linputLipProd]
  | cons L Ls ih =>
      have hLmem : L ∈ L :: Ls := List.mem_cons_self
      calc dist (lparamComp Ls θ (L.map θ a)) (lparamComp Ls θ (L.map θ b))
          ≤ linputLipProd Ls * dist (L.map θ a) (L.map θ b) :=
            ih (fun L' hL' => hin L' (List.mem_cons_of_mem L hL')) _ _
        _ ≤ linputLipProd Ls * (L.lip * dist a b) :=
            mul_le_mul_of_nonneg_left (hin L hLmem θ hθ a b) (linputLipProd_nonneg Ls)
        _ = L.lip * linputLipProd Ls * dist a b := by ring

/-- **Conditional weight-Lipschitz envelope.** For weights in `K` (on which each layer's input-
Lipschitz estimate holds) and a forward-invariant activation domain `D` (every layer maps `D` into
`D` for weights in `K`, and each layer's weight-Lipschitz estimate holds on `D`), the composed
parametric map is `lparamLipBound`-Lipschitz in the weights. -/
theorem paramComp_param_lipschitz_on {K : Set Θ} {D : Set V} (Ls : List (ParamLayerLocal Θ V))
    (hin : ∀ L ∈ Ls, ∀ θ ∈ K, ∀ a b, dist (L.map θ a) (L.map θ b) ≤ L.lip * dist a b)
    (hloc : ∀ L ∈ Ls, ∀ θ ∈ K, ∀ θ' ∈ K, ∀ y ∈ D,
      dist (L.map θ y) (L.map θ' y) ≤ L.paramLip * dist θ θ')
    (hinv : ∀ L ∈ Ls, ∀ θ ∈ K, ∀ y ∈ D, L.map θ y ∈ D)
    {θ θ' : Θ} (hθ : θ ∈ K) (hθ' : θ' ∈ K) {x : V} (hx : x ∈ D) :
    dist (lparamComp Ls θ x) (lparamComp Ls θ' x) ≤ lparamLipBound Ls * dist θ θ' := by
  induction Ls generalizing x with
  | nil => simp [lparamComp, lparamLipBound]
  | cons L Ls ih =>
      have hLmem : L ∈ L :: Ls := List.mem_cons_self
      have hmap : L.map θ x ∈ D := hinv L hLmem θ hθ x hx
      have ihtail := ih (fun L' hL' => hin L' (List.mem_cons_of_mem L hL'))
        (fun L' hL' => hloc L' (List.mem_cons_of_mem L hL'))
        (fun L' hL' => hinv L' (List.mem_cons_of_mem L hL')) hmap
      calc dist (lparamComp (L :: Ls) θ x) (lparamComp (L :: Ls) θ' x)
          ≤ dist (lparamComp Ls θ (L.map θ x)) (lparamComp Ls θ' (L.map θ x))
              + dist (lparamComp Ls θ' (L.map θ x)) (lparamComp Ls θ' (L.map θ' x)) :=
            dist_triangle _ _ _
        _ ≤ lparamLipBound Ls * dist θ θ' + linputLipProd Ls * (L.paramLip * dist θ θ') := by
            refine add_le_add ihtail ?_
            calc dist (lparamComp Ls θ' (L.map θ x)) (lparamComp Ls θ' (L.map θ' x))
                ≤ linputLipProd Ls * dist (L.map θ x) (L.map θ' x) :=
                  lparamComp_input_lip_on Ls (fun L' hL' => hin L' (List.mem_cons_of_mem L hL'))
                    hθ' _ _
              _ ≤ linputLipProd Ls * (L.paramLip * dist θ θ') :=
                  mul_le_mul_of_nonneg_left (hloc L hLmem θ hθ θ' hθ' x hx) (linputLipProd_nonneg Ls)
        _ = lparamLipBound (L :: Ls) * dist θ θ' := by simp only [lparamLipBound]; ring

end TLT
