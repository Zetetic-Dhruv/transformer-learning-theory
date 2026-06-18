/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.NeuroSymbolicDesign
import TLT_Proofs.TemperedDesignLaw.NeuroSymbolicDesignSO

/-!
# The Transformer object design-law root

The root manifest of **abstract design conjectures** for the Transformer object. Each conjecture about
an ideal transformer is a *type* (a design certificate) and is accompanied by a **proven instance** that
inhabits it. A certificate is a proven sub-conjecture: its type encodes a property an ideal design must
have (type-forced, so no trivial inhabitant exists), and an inhabitant witnesses that a concrete design
has it.

This file is the single home for the abstract design conjectures. The types are re-exported into the
root `TLT` namespace; each is registered with the theorem that exhibits a proven inhabitant.

## Registry

| design conjecture (the type) | status | proven instance |
|---|---|---|
| `NeuroSymbolicDesignCertificate` — exact, hierarchically graded, statistically certified symbolic factorization into a symbol-conditioned downstream | **proven, unconditional; two designs** | first-order (affine `binCascadeGrade`): `neuroSymbolicDesign_realizable` (`nsDesignWitness`); second-order (quadratic `quadDepthGrade`): `soNeuroSymbolicDesign_realizable` (`soDesignWitness`) |
| `TemperedDesignLawCertificate` — two complementary generalization certificates on one routed-symbol gap, the measurability cliff, the hard-tame leg | proven, conditional on a classical non-Borel base range | `TemperedDesignLaw.MuxCertificate.temperedDesignLawCertificate_binary` |
| `TransformerDesignLaw` — config-indexed capacity ⊕ measurability ⊕ expressivity | two of three legs proved | `Bridge.Certificate.ConfigDesignLaw` |

Adding a design conjecture: state the certificate type (its fields are the type-forced properties),
register it here with a theorem exhibiting an inhabitant, and cite the proving module. An open
conjecture is stated as a `Prop` with no proof; it graduates to a registered row when an instance lands.

The literal binding of these conjectures to the `RealTransformer` object
(`Bridge.Spec.TransformerObjectVocabulary`) is the next step; it pulls the executable neural-network
spec into the manifest.
-/

namespace TLT

-- The neurosymbolic design certificate, re-exported at the Transformer-object root.
export TLT.TemperedDesignLaw (NeuroSymbolicDesignCertificate)

/-- **Proven sub-conjecture: a neurosymbolic design is realizable.** The ideal-neurosymbolic-transformer
spec `NeuroSymbolicDesignCertificate` is inhabited unconditionally by `nsDesignWitness`: an exact,
hierarchically graded, statistically certified symbolic factorization into a symbol-conditioned
downstream, with the strict expressivity hierarchy discharged by the constrained affine-mux cascade. -/
theorem neuroSymbolicDesign_realizable :
    Nonempty (NeuroSymbolicDesignCertificate (Fin 1 → ℝ) (Fin 2) (Fin 2)) :=
  ⟨TemperedDesignLaw.nsDesignWitness⟩

/-- **Proven sub-conjecture: a second-order (quadratic / self-attention) neurosymbolic design is
realizable.** The same spec is inhabited by `soDesignWitness`, whose strict expressivity hierarchy is
the quadratic-gate separation `quadDepthGrade_zero_ssubset_one` and whose router is a quadratic score
threshold. So `NeuroSymbolicDesignCertificate` admits both a first-order (affine) and a second-order
(quadratic) design: the spec discriminates the score class without admitting a trivial inhabitant. -/
theorem soNeuroSymbolicDesign_realizable :
    Nonempty (NeuroSymbolicDesignCertificate (Fin 1 → ℝ) (Fin 2) (Fin 2)) :=
  ⟨TemperedDesignLaw.soDesignWitness⟩

end TLT
