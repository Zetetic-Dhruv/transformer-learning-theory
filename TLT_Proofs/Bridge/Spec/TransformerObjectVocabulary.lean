/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import NN.Spec.Models.Transformer
import NN.Floats.Float32
import NN.Floats.IEEEExec.Exec32
import Mathlib.Data.Real.Basic

/-!
# Transformer statements over real and IEEE binary32 backends

Minimal common vocabulary for stating and resolving properties of TorchLean's `Spec.Transformer`,
uniformly across numeric backends `α` — in particular `α = ℝ` (learning theory) and
`α = IEEE32Exec` (IEEE binary32 execution). The architecture shape is backend-independent (four
`Nat`); only the tensors live over `α`.

This file deliberately contains no concrete property, no proved theorem about a specific
transformer, no cross-backend reading of parameters, and no result-specific observable. Those are
built in separate files on top of this vocabulary.

## Contents

- `TransformerConfig` — the backend-independent architecture shape (four `Nat`).
- `TransformerObject α` — a `Spec.Transformer` at backend `α`, paired with its shape.
- `TransformerProperty α` — a property of such an object, as a `Prop`.
- `Resolution T P` — a proof-carrying resolution of a property `P` of a subject `T`: either a proof
  (`discharged`) or a refutation (`refuted`). A property for which no `Resolution T P` inhabitant has
  yet been supplied is simply unresolved.
- `RealTransformer` / `FP32Transformer` — the `ℝ` and `IEEE32Exec` readings.
- `TransformerObject.forwardMap` — the forward map of the object at a given sequence length.
-/

/-!
## References
- [27] transformer architecture (numLayers/headCount/embedDim/hiddenDim); [53] `Spec.Transformer`,
  backend-parametric Tensor/Context; [51] IEEE binary32 backend.
- Provenance: Innovation (organizational vocabulary) — the backend-parametric `TransformerObject` +
  `Resolution` proof-carrying scaffold; not a theorem.
-/

open Spec
open TorchLean.Floats

namespace TLT

universe u

variable {α : Type} [Context α] [DecidableRel ((· > ·) : α → α → Prop)]

/-- Backend-independent architecture shape for a `Spec.Transformer`. -/
structure TransformerConfig where
  numLayers : Nat
  headCount : Nat
  embedDim  : Nat
  hiddenDim : Nat

/-- A transformer architecture realized at numeric backend `α`. The shape is stored in `cfg`; the
network is TorchLean's actual `Spec.Transformer` at that shape and backend. -/
structure TransformerObject (α : Type) [Context α]
    [DecidableRel ((· > ·) : α → α → Prop)] where
  cfg : TransformerConfig
  net :
    Spec.Transformer
      cfg.numLayers
      cfg.headCount
      cfg.embedDim
      cfg.hiddenDim
      α

/-- A property of a transformer at backend `α`, as a `Prop`. -/
abbrev TransformerProperty (α : Type) [Context α]
    [DecidableRel ((· > ·) : α → α → Prop)] : Type :=
  TransformerObject α → Prop

/-- A proof-carrying resolution of a property `P` of a subject `T`: `discharged` carries a proof of
the property, `refuted` carries a proof of its negation. Generic in the subject `S`, so it resolves
properties of a transformer at any backend — and of any other subject. -/
inductive Resolution {S : Type u} (T : S) (P : S → Prop) : Type u where
  | discharged (proof : P T) : Resolution T P
  | refuted    (proof : ¬ P T) : Resolution T P

/-- The learning-theory reading: a transformer over the reals. -/
abbrev RealTransformer : Type :=
  TransformerObject ℝ

/-- The execution reading: a transformer over IEEE binary32. -/
abbrev FP32Transformer : Type :=
  TransformerObject IEEE32Exec

namespace TransformerObject

/-- The forward map of a transformer object at a given sequence length. -/
def forwardMap (T : TransformerObject α) {seqLen : Nat}
    (hSeq : seqLen > 0)
    (hEmbed : T.cfg.embedDim > 0)
    (input target : Tensor α (.dim seqLen (.dim T.cfg.embedDim .scalar))) :
    Tensor α (.dim seqLen (.dim T.cfg.embedDim .scalar)) :=
  Spec.Transformer.forward
    (numLayers := T.cfg.numLayers)
    (headCount := T.cfg.headCount)
    (embedDim := T.cfg.embedDim)
    (hiddenDim := T.cfg.hiddenDim)
    (seqLen := seqLen)
    T.net
    input
    target
    hSeq
    hEmbed

end TransformerObject

end TLT
