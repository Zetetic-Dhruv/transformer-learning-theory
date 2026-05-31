/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.TransformerRoot
import TLT_Proofs.Bridge.TorchLeanAttention

/-!
# Attention routing of a transformer is well-behaved

For a transformer over the reals, the scaled-dot-product attention argmax router induced by its
embedding dimension satisfies Krapp–Wirth measurable-target well-behavedness, packaged as a
`Resolution` of the transformer object.

Well-behavedness is a property of the attention *architecture* at the transformer's embedding
dimension (its query/key width): the routing hypothesis class — quantified over every standard-Borel
parameter space and measurable expert embedding — has a measurable empirical-process bad event. A
particular transformer's weights are one member of that class, so the statement is uniform in the
transformer and depends on it through `cfg.embedDim`.

## Main results

- `TransformerObject.scoreRouter` — the attention score-router at a transformer's embedding
  dimension, routing over `nK` key positions.
- `WellBehavedAttentionRouting` — the property that this routing is well-behaved for every
  standard-Borel parameter space and measurable expert embedding.
- `transformerAttention_wellBehaved` — that property holds for every real transformer (lifting
  `attentionRouting_wellBehaved`).
- `transformerAttention_resolution` — the corresponding discharged `Resolution`.
-/

open MeasureTheory Set

noncomputable section

namespace TLT

/-- The scaled-dot-product attention score-router at a transformer's embedding dimension, routing
over `nK` key positions: the input is a query coordinate vector `Fin cfg.embedDim → ℝ` and the
parameter is the key matrix. -/
def TransformerObject.scoreRouter (T : RealTransformer) (nK : ℕ) :
    FiniteScoreRouterCode (Fin T.cfg.embedDim → ℝ) nK :=
  Bridge.attentionScoreRouter T.cfg.embedDim nK

/-- The attention routing of `T` is well-behaved: for every key count `nK`, standard-Borel parameter
space `Θ`, and measurable expert embedding `e`, the patched class of the `nK`-key argmax router
satisfies `WellBehavedVCMeasTarget`. -/
def WellBehavedAttentionRouting (T : RealTransformer) : Prop :=
  ∀ (nK : ℕ) (hnK : 0 < nK) {Θ : Type} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (e : Θ → Fin nK → Concept (Fin T.cfg.embedDim → ℝ) Bool),
    (∀ i, Measurable (fun p : Θ × (Fin T.cfg.embedDim → ℝ) => e p.1 i p.2)) →
    WellBehavedVCMeasTarget (Fin T.cfg.embedDim → ℝ)
      (Set.range (multiPatchEval e ((T.scoreRouter nK).route hnK)))

/-- Every real transformer's attention routing is well-behaved, lifting
`attentionRouting_wellBehaved` to the transformer object. -/
theorem transformerAttention_wellBehaved (T : RealTransformer) :
    WellBehavedAttentionRouting T := by
  intro nK hnK _ _ _ e he
  exact Bridge.attentionRouting_wellBehaved hnK e he

/-- The discharged resolution recording that the attention routing of `T` is well-behaved. -/
def transformerAttention_resolution (T : RealTransformer) :
    Resolution T WellBehavedAttentionRouting :=
  Resolution.discharged (transformerAttention_wellBehaved T)

end TLT
