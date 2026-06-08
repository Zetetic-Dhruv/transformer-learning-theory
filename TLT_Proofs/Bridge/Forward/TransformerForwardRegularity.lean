/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Forward.ForwardContinuity
import TLT_Proofs.Bridge.Spec.TransformerObjectVocabulary

/-!
# The transformer forward map is continuous — discharged as a `Resolution` of the root object

The transformer forward pass, read over real coordinates, is an input embedding (a linear map), a
stack of transformer layers, and an output projection (a linear map). Each layer is continuous
(`continuous_encoderLayerCoord`: residual self-attention + layer-normalization + residual
feed-forward + layer-normalization, with the attention continuous by `continuous_attentionCoord` and
the layer-normalization division everywhere-defined by the verified positive regularizer
`layerNorm_std_pos`). The embeddings and projection are continuous (`continuous_matMulCoord`), and a
left-fold of continuous layers is continuous (`continuous_listFoldl`). Composing these gives a
continuous forward map.

This file packages that continuity as a property of `TransformerObject` and discharges it as a
`Resolution` — the root object's record that the conjecture "the forward map is continuous" is proved.

## Main results

- `ForwardMapContinuous` — the property that the coordinate forward map (embedding · layers ·
  projection) at the transformer's embedding dimension is continuous.
- `transformerForwardMap_continuous` — that property holds for every real transformer.
- `transformerForwardMap_continuous_resolution` — the discharged `Resolution`.
-/

/-!
## References
- composition preserves continuity (`Continuous.comp`) and measurability (`Measurable.comp`);
  `Measurable.div` unconditional (measurability survives at ε=0 where continuity fails).
- Provenance: Classical-instantiation (real forward-map regularity; relocated from the fp32 cluster
  — contains no fp32 content). `Resolution` wrappers are organizational scaffolding.
-/

open scoped Topology

noncomputable section

namespace TLT

/-- The transformer forward map is continuous: at the transformer's embedding dimension, an input
embedding `Wembed`, a stack of continuous `layers` (the transformer encoder/decoder layers, continuous
by `continuous_encoderLayerCoord`), and an output projection `Wout` compose to a continuous map of the
input coordinates. -/
def ForwardMapContinuous (T : RealTransformer) : Prop :=
  ∀ {seqLen : ℕ} (Wembed Wout : Fin T.cfg.embedDim → Fin T.cfg.embedDim → ℝ)
    (layers : List ((Fin seqLen → Fin T.cfg.embedDim → ℝ) → Fin seqLen → Fin T.cfg.embedDim → ℝ)),
    (∀ L ∈ layers, Continuous L) →
    Continuous (fun X : Fin seqLen → Fin T.cfg.embedDim → ℝ =>
      matMulCoord Wout (layers.foldl (fun acc L => L acc) (matMulCoord Wembed X)))

/-- Every real transformer's forward map is continuous (composition of the continuous embedding, the
continuous-layer stack, and the continuous output projection). -/
theorem transformerForwardMap_continuous (T : RealTransformer) : ForwardMapContinuous T := by
  intro seqLen Wembed Wout layers hL
  exact (continuous_matMulCoord Wout).comp
    ((continuous_listFoldl layers hL).comp (continuous_matMulCoord Wembed))

/-- The discharged resolution recording that the forward map of `T` is continuous — closing the
forward-continuity conjecture as a `Resolution` of the root transformer object. -/
def transformerForwardMap_continuous_resolution (T : RealTransformer) :
    Resolution T ForwardMapContinuous :=
  Resolution.discharged (transformerForwardMap_continuous T)

/-! ### The measurable forward map (regularizer-free)

Measurability needs no nonzero-denominator hypothesis (`Measurable.div` is unconditional), so it holds
for *measurable* layers — and the transformer layers are measurable for **every** layer-norm
regularizer `ε ≥ 0` (`measurable_layerNormCoordEps`), including `ε = 0`, where the forward map is
measurable but not continuous. -/

/-- The transformer forward map is **measurable**: an input embedding, a stack of measurable layers,
and an output projection compose to a measurable map of the input coordinates. -/
def ForwardMapMeasurable (T : RealTransformer) : Prop :=
  ∀ {seqLen : ℕ} (Wembed Wout : Fin T.cfg.embedDim → Fin T.cfg.embedDim → ℝ)
    (layers : List ((Fin seqLen → Fin T.cfg.embedDim → ℝ) → Fin seqLen → Fin T.cfg.embedDim → ℝ)),
    (∀ L ∈ layers, Measurable L) →
    Measurable (fun X : Fin seqLen → Fin T.cfg.embedDim → ℝ =>
      matMulCoord Wout (layers.foldl (fun acc L => L acc) (matMulCoord Wembed X)))

/-- Every real transformer's forward map is measurable (composition of the measurable embedding, the
measurable-layer stack, and the measurable output projection). -/
theorem transformerForwardMap_measurable (T : RealTransformer) : ForwardMapMeasurable T := by
  intro seqLen Wembed Wout layers hL
  exact (measurable_matMulCoord Wout).comp
    ((measurable_listFoldl layers hL).comp (measurable_matMulCoord Wembed))

/-- The discharged resolution recording that the forward map of `T` is measurable — regularizer-free
(it holds even at `ε = 0`, where continuity fails). -/
def transformerForwardMap_measurable_resolution (T : RealTransformer) :
    Resolution T ForwardMapMeasurable :=
  Resolution.discharged (transformerForwardMap_measurable T)

end TLT
