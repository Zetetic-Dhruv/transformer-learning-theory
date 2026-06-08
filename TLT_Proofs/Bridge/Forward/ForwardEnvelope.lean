/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Forward.ExecutedForward

/-!
# The full-network rounding envelope: composing per-layer rounding error through the forward pass

The executed forward pass is a composition of executed layers `f̂_k ∘ ⋯ ∘ f̂_1`, the rounded
counterparts of the ideal layers `f_k ∘ ⋯ ∘ f_1`. This file propagates a *per-layer* rounding error
to a *network-level* envelope between the executed and ideal forward maps.

Each layer is packaged as an `ExecLayer`, carrying its ideal map, its executed map, the Lipschitz
constant `Λ` of the ideal map, and a uniform local rounding bound `δ` (`∀ y, dist (f̂ y) (f y) ≤ δ` —
the form supplied at the reduction level by `Fp32Reduction.ie32_foldl_closed_envelope`). Inserting
`f_i(ŷ_{i-1})` and using the triangle inequality together with the Lipschitz bound gives the standard
error recurrence

`eᵢ ≤ δᵢ + Λᵢ · e_{i-1}`,  `e₀ = 0`,

whose solution is `e_k ≤ ∑ᵢ δᵢ · ∏_{j>i} Λⱼ`. `envBound` is exactly this sum, computed by recursion
over the layer list, and `execComp_envelope` is the resulting uniform bound. Chaining it into
`executed_risk_transfer` gives `execComp_risk_transfer`: the executed expected risk is within
`L · envBound` of the ideal.

The envelope is finite exactly where the per-layer ideal Lipschitz constants are. This is a constraint
on the layers, not on the bound: a layer-normalization layer is Lipschitz only with a positive
regularizer (its constant scales like `1/√ε`), and dot-product self-attention is Lipschitz only on a
bounded input domain (its constant depends on the domain bound). On those layers the `ExecLayer.lip`
field records the corresponding constant; outside such a domain no finite envelope exists.

## Main results

- `ExecLayer` — a layer paired with its executed counterpart, its ideal Lipschitz constant, and a
  uniform local rounding bound.
- `idealComp` / `execComp` / `lipProd` / `envBound` — the ideal and executed compositions, the
  Lipschitz-constant product, and the accumulated network envelope.
- `execComp_envelope` — the executed forward is uniformly within `envBound` of the ideal forward.
- `execComp_risk_transfer` — the executed expected risk is within `L · envBound` of the ideal.
-/

/-!
## References
- [38] quantized forward-error envelope `Δ=δ_m+∑(∏_{j>i}L_j)δ_i` (= `envBound`); [43] classical
  accumulated-rounding ancestor; [36] product-of-Lipschitz composition.
- Provenance: Classical-instantiation (clean recursive Lean formalization of the [38]/[43] envelope).
-/

open MeasureTheory

namespace TLT

variable {V : Type*} [PseudoMetricSpace V]

/-- A forward-pass layer paired with its executed (rounded) counterpart, carrying the Lipschitz
constant `lip` of the ideal map and a uniform local rounding bound `rnd`. -/
structure ExecLayer (V : Type*) [PseudoMetricSpace V] where
  /-- The ideal (exact real) layer map. -/
  ideal : V → V
  /-- The executed (rounded) layer map. -/
  exec : V → V
  /-- The Lipschitz constant of the ideal map. -/
  lip : ℝ
  /-- The uniform local rounding bound between the executed and ideal maps. -/
  rnd : ℝ
  lip_nonneg : 0 ≤ lip
  ideal_lip : ∀ a b, dist (ideal a) (ideal b) ≤ lip * dist a b
  exec_close : ∀ y, dist (exec y) (ideal y) ≤ rnd

/-- The ideal forward map: compose the ideal layer maps (list head applied first). -/
def idealComp : List (ExecLayer V) → V → V
  | [], x => x
  | L :: Ls, x => idealComp Ls (L.ideal x)

/-- The executed forward map: compose the executed (rounded) layer maps. -/
def execComp : List (ExecLayer V) → V → V
  | [], x => x
  | L :: Ls, x => execComp Ls (L.exec x)

/-- The product of the per-layer ideal Lipschitz constants. -/
def lipProd : List (ExecLayer V) → ℝ
  | [] => 1
  | L :: Ls => L.lip * lipProd Ls

/-- The network rounding envelope: each layer's local rounding error amplified by the product of its
downstream Lipschitz constants, summed over the layers. -/
def envBound : List (ExecLayer V) → ℝ
  | [] => 0
  | L :: Ls => L.rnd * lipProd Ls + envBound Ls

/-- The Lipschitz-constant product is nonnegative. -/
lemma lipProd_nonneg (Ls : List (ExecLayer V)) : 0 ≤ lipProd Ls := by
  induction Ls with
  | nil => simp [lipProd]
  | cons L Ls ih => simp only [lipProd]; exact mul_nonneg L.lip_nonneg ih

/-- The ideal forward map is Lipschitz with constant `lipProd Ls` (composition of Lipschitz layers). -/
lemma idealComp_lip (Ls : List (ExecLayer V)) (a b : V) :
    dist (idealComp Ls a) (idealComp Ls b) ≤ lipProd Ls * dist a b := by
  induction Ls generalizing a b with
  | nil => simp [idealComp, lipProd]
  | cons L Ls ih =>
    simp only [idealComp, lipProd]
    calc dist (idealComp Ls (L.ideal a)) (idealComp Ls (L.ideal b))
        ≤ lipProd Ls * dist (L.ideal a) (L.ideal b) := ih _ _
      _ ≤ lipProd Ls * (L.lip * dist a b) :=
          mul_le_mul_of_nonneg_left (L.ideal_lip a b) (lipProd_nonneg Ls)
      _ = L.lip * lipProd Ls * dist a b := by ring

/-- **The full-network rounding envelope.** The executed forward map is uniformly within `envBound` of
the ideal forward map: each layer's local rounding error, amplified by the product of its downstream
Lipschitz constants, accumulates to the network envelope. -/
theorem execComp_envelope (Ls : List (ExecLayer V)) (x : V) :
    dist (execComp Ls x) (idealComp Ls x) ≤ envBound Ls := by
  induction Ls generalizing x with
  | nil => simp [execComp, idealComp, envBound]
  | cons L Ls ih =>
    simp only [execComp, idealComp, envBound]
    calc dist (execComp Ls (L.exec x)) (idealComp Ls (L.ideal x))
        ≤ dist (execComp Ls (L.exec x)) (idealComp Ls (L.exec x))
            + dist (idealComp Ls (L.exec x)) (idealComp Ls (L.ideal x)) := dist_triangle _ _ _
      _ ≤ envBound Ls + lipProd Ls * dist (L.exec x) (L.ideal x) :=
          add_le_add (ih _) (idealComp_lip Ls _ _)
      _ ≤ envBound Ls + lipProd Ls * L.rnd := by
          linarith [mul_le_mul_of_nonneg_left (L.exec_close x) (lipProd_nonneg Ls)]
      _ = L.rnd * lipProd Ls + envBound Ls := by ring

/-- **The full-network executed risk transfer.** Chaining the network envelope into
`executed_risk_transfer`: for an `L`-Lipschitz loss, the executed composed forward's expected risk is
within `L · envBound` of the ideal, with `envBound` the concrete network rounding envelope built from
the per-layer Lipschitz constants and local rounding bounds. -/
theorem execComp_risk_transfer {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Ls : List (ExecLayer V)) (input : Ω → V) (ℓ : V → ℝ) {L : ℝ}
    (hL0 : 0 ≤ L) (hLip : ∀ p q, |ℓ p - ℓ q| ≤ L * dist p q)
    (hintF : Integrable (fun x => ℓ (idealComp Ls (input x))) μ)
    (hintG : Integrable (fun x => ℓ (execComp Ls (input x))) μ) :
    |(∫ x, ℓ (execComp Ls (input x)) ∂μ) - (∫ x, ℓ (idealComp Ls (input x)) ∂μ)|
      ≤ L * envBound Ls :=
  executed_risk_transfer ℓ hL0 hLip (fun x => execComp_envelope Ls (input x)) hintF hintG

end TLT
