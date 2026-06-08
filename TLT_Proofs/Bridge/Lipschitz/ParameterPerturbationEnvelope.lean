/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Parameter-Lipschitz envelope of a composed forward pass (global and local)

For a covering-number bound on a parametric function class one needs the forward map to be
Lipschitz in its **weights**: `‖f_θ(x) − f_{θ'}(x)‖ ≤ L_param · ‖θ − θ'‖`, uniformly over a
bounded input domain. This is distinct from the input-Lipschitz constant of `ForwardEnvelope`
(`lipProd`): there the input varies at fixed weights; here the weights vary at fixed input.

A composed forward pass `f_θ = L_N(θ) ∘ ⋯ ∘ L_1(θ)` accumulates a weight perturbation through the
same recurrence as the rounding envelope: perturbing layer `k`'s weights moves its output by
`paramLip_k · dist θ θ'`, amplified by the downstream input-Lipschitz constants, giving
`∑ₖ paramLip_k · ∏_{j>k} lip_j`.

This file carries **two** layer abstractions, a genuine global/local pair:

* `ParamLayer` (global). The input- and weight-Lipschitz estimates are **fields** of the layer,
  holding unconditionally. Suitable for layers with a uniform Lipschitz constant.
* `ParamLayerLocal` (local). The layer carries **only** its map and nominal constants; the
  Lipschitz estimates are supplied at composition time, conditional on an admissible weight set
  `K` and a forward-invariant activation domain `D`. This is required for self-attention, which
  has **no** global Lipschitz constant (Kim et al. 2021) — its bound is valid only on a bounded
  activation ball, which the layer-normalised architecture provides per block.

`ParamLayer` is the special case of `ParamLayerLocal` with `K = univ`, `D = univ` and total
proofs; `ParamLayer.toLocal` and `paramComp_eq_lparamComp_toLocal` make that relationship explicit,
recovering the global envelope as a corollary of the local one.

## Main results

- `ParamLayer` / `paramComp` / `paramComp_param_lipschitz` — global weight-Lipschitz envelope.
- `ParamLayerLocal` / `lparamComp` / `paramComp_param_lipschitz_on(')` — conditional envelope.
- `ParamLayer.toLocal` / `paramComp_eq_lparamComp_toLocal` — the global ⟶ local bridge.
-/

/-!
## References
- [35] Lemma 2 (telescoping weight-perturbation envelope `∑ₖ paramLip_k·∏_{j>k} lip_j`); [36]
  product-of-Lipschitz composition; [31] Thm 3.1 (motivates the local/conditional variant).
- Provenance: Classical-instantiation (envelope = Neyshabur Lem 2; global/local pair is design).
-/

namespace TLT

variable {Θ V : Type*} [PseudoMetricSpace Θ] [PseudoMetricSpace V]

/-! ## Global parameter-Lipschitz layer -/

/-- A forward-pass layer presented as a function of its weights `θ : Θ`, carrying the Lipschitz
constant `lip` of the layer map in its input and the Lipschitz constant `paramLip` of the layer map
in its weights (each uniform over the other argument on the relevant domain). -/
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

/-- The parametric forward map: compose the weight-parametrised layer maps (list head applied
first), all reading the same shared weight vector `θ`. -/
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

/-- **Parameter-Lipschitz envelope.** The composed parametric forward map is `paramLipBound`-
Lipschitz in its weights, uniformly over the input: `dist (f_θ x) (f_{θ'} x) ≤ paramLipBound Ls ·
dist θ θ'`. -/
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

/-! ## Local (conditional) parameter-Lipschitz layer

A weight-parametrised forward map has *no* uniform Lipschitz constants: a linear layer's
input-Lipschitz constant scales with the magnitude of its weights, and its weight-Lipschitz
constant scales with the magnitude of the activation it multiplies. Both estimates are therefore
conditional — the input-Lipschitz bound holds for weights in an admissible set `K`, and the
weight-Lipschitz bound holds for activations in a forward-invariant set `D`. Neither is a field of
the layer; both are supplied at composition time with their domains. -/

/-- A weight-parametrised layer carrying its map and nominal Lipschitz constants `lip` (input) and
`paramLip` (weight); the constants are valid only on the admissible weight/activation domains,
supplied at composition time (see `paramComp_param_lipschitz_on`). -/
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

/-- **Conditional input-Lipschitz of the composition.** For weights `θ` in the admissible set `K`
on which each layer's input-Lipschitz estimate holds, the composed map is `linputLipProd`-Lipschitz
in the input. -/
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

/-- **Conditional input-Lipschitz of the composition (domain-restricted).** As
`lparamComp_input_lip_on`, but the per-layer input-Lipschitz estimate need hold only on a
forward-invariant activation domain `D` — admitting layers (such as attention) that are Lipschitz
only on a bounded domain, while the globally-Lipschitz layers satisfy it by ignoring the
membership. -/
lemma lparamComp_input_lip_on' {K : Set Θ} {D : Set V} (Ls : List (ParamLayerLocal Θ V))
    (hin : ∀ L ∈ Ls, ∀ θ ∈ K, ∀ a ∈ D, ∀ b ∈ D, dist (L.map θ a) (L.map θ b) ≤ L.lip * dist a b)
    (hinv : ∀ L ∈ Ls, ∀ θ ∈ K, ∀ y ∈ D, L.map θ y ∈ D)
    {θ : Θ} (hθ : θ ∈ K) {a b : V} (ha : a ∈ D) (hb : b ∈ D) :
    dist (lparamComp Ls θ a) (lparamComp Ls θ b) ≤ linputLipProd Ls * dist a b := by
  induction Ls generalizing a b with
  | nil => simp [lparamComp, linputLipProd]
  | cons L Ls ih =>
      have hLmem : L ∈ L :: Ls := List.mem_cons_self
      have hmapa : L.map θ a ∈ D := hinv L hLmem θ hθ a ha
      have hmapb : L.map θ b ∈ D := hinv L hLmem θ hθ b hb
      calc dist (lparamComp Ls θ (L.map θ a)) (lparamComp Ls θ (L.map θ b))
          ≤ linputLipProd Ls * dist (L.map θ a) (L.map θ b) :=
            ih (fun L' hL' => hin L' (List.mem_cons_of_mem L hL'))
               (fun L' hL' => hinv L' (List.mem_cons_of_mem L hL')) hmapa hmapb
        _ ≤ linputLipProd Ls * (L.lip * dist a b) :=
            mul_le_mul_of_nonneg_left (hin L hLmem θ hθ a ha b hb) (linputLipProd_nonneg Ls)
        _ = L.lip * linputLipProd Ls * dist a b := by ring

/-- **Conditional weight-Lipschitz envelope (domain-restricted input-Lipschitz).** As
`paramComp_param_lipschitz_on`, but the per-layer input-Lipschitz estimate need hold only on the
forward-invariant domain `D` — so attention, Lipschitz only on a bounded activation ball, is
admitted alongside the globally-Lipschitz linear and ReLU layers. -/
theorem paramComp_param_lipschitz_on' {K : Set Θ} {D : Set V} (Ls : List (ParamLayerLocal Θ V))
    (hin : ∀ L ∈ Ls, ∀ θ ∈ K, ∀ a ∈ D, ∀ b ∈ D, dist (L.map θ a) (L.map θ b) ≤ L.lip * dist a b)
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
      have hmap' : L.map θ' x ∈ D := hinv L hLmem θ' hθ' x hx
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
                  lparamComp_input_lip_on' Ls (fun L' hL' => hin L' (List.mem_cons_of_mem L hL'))
                    (fun L' hL' => hinv L' (List.mem_cons_of_mem L hL')) hθ' hmap hmap'
              _ ≤ linputLipProd Ls * (L.paramLip * dist θ θ') :=
                  mul_le_mul_of_nonneg_left (hloc L hLmem θ hθ θ' hθ' x hx) (linputLipProd_nonneg Ls)
        _ = lparamLipBound (L :: Ls) * dist θ θ' := by simp only [lparamLipBound]; ring

/-! ## The global ⟶ local bridge

A `ParamLayer` is the special case of a `ParamLayerLocal` whose conditional Lipschitz hypotheses
hold with `K = univ`, `D = univ` (the proof fields supply them unconditionally). `toLocal` forgets
the proofs; `paramComp_eq_lparamComp_toLocal` shows the two compositions agree, so the global
envelope `paramComp_param_lipschitz` is recovered as the `K = D = univ` instance of the local one. -/

/-- A global `ParamLayer` as a `ParamLayerLocal` (same map and constants; the global Lipschitz
proofs become the unconditional instance of the conditional hypotheses). -/
def ParamLayer.toLocal (L : ParamLayer Θ V) : ParamLayerLocal Θ V where
  map := L.map
  paramLip := L.paramLip
  lip := L.lip
  paramLip_nonneg := L.paramLip_nonneg
  lip_nonneg := L.lip_nonneg

/-- The global and local compositions agree under `toLocal`. -/
lemma paramComp_eq_lparamComp_toLocal (Ls : List (ParamLayer Θ V)) (θ : Θ) (x : V) :
    paramComp Ls θ x = lparamComp (Ls.map ParamLayer.toLocal) θ x := by
  induction Ls generalizing x with
  | nil => simp [paramComp, lparamComp]
  | cons L Ls ih => simp only [paramComp, lparamComp, List.map_cons, ParamLayer.toLocal, ih]

end TLT
