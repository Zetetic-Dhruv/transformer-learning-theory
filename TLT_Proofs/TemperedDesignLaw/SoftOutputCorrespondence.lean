/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.LiteralAttentionTempered
import TLT_Proofs.Bridge.Certificate.AttentionTransformerCertificate
import TLT_Proofs.Bridge.Spec.ScaledDotProductAttentionCorrespondence

/-!
# The soft-output correspondence — the abstract mixture is the literal attention output

The tempered design law's hardening envelope is stated for the abstract soft mixture
`mixtureOutput (softWeights A ρ x) val` with an *abstract* payload `val`. This file identifies that mixture
with the literal scaled-dot-product attention output, closing the gap flagged in `litAttn_hardening`'s
docstring (`val` abstract → the literal value vectors).

The hinge is that the **temperature is the inverse attention scale**: TorchLean's attention applies the softmax
to the scaled scores `⟨q,kⱼ⟩ / scale`, while the tempered router applies it to `β · ⟨q,kⱼ⟩`, so the two soft
weight families coincide exactly when `β = 1/scale`. With the payload taken to be the literal value vectors
`matMulCoord W Y` (the V-projection), the mixture is then the ideal head `attnHead`.

* `mixtureOutput_softWeights_eq_attnHead` — at `β = 1/scale`, the soft mixture of the literal attention's
  routing weights with the literal value vectors `matMulCoord W Y` equals the ideal head `attnHead scale W Y`.
* `mixtureOutput_softWeights_eq_litAttention` — the end-to-end statement: composing the previous identity with
  the shipped coordinate binding `matCoords_scaledDotProductAttention`, the mixture equals the literal
  `Spec.scaledDotProductAttention` output (read in coordinates) at the standard scale `√d`.
-/

open scoped BigOperators

noncomputable section

namespace TLT.TemperedDesignLaw

/-- TorchLean's `Spec.dot` of two coordinate vectors (carried to vector tensors by the inverse of
`Tensor.dimScalarEquiv`) is the coordinate inner product. -/
private lemma spec_dot_equivSymm_eq_sum {d : ℕ} (x y : Fin d → ℝ) :
    Spec.dot ((Spec.Tensor.dimScalarEquiv d).symm x) ((Spec.Tensor.dimScalarEquiv d).symm y)
      = ∑ j : Fin d, x j * y j := by
  rw [Spec.dot_vec_eq_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [Spec.toVec, Spec.Tensor.dimScalarEquiv, Spec.Tensor.ofScalar]

/-- **The soft-output correspondence (weights × value vectors).** The tempered router's soft weights are the
softmax of `β · ⟨q,kⱼ⟩`; the literal attention's weights are the softmax of `⟨q,kⱼ⟩ / scale`. At `β = 1/scale`
they coincide, so the soft mixture of the literal attention's routing weights with the literal value vectors
`matMulCoord W Y` (the V-projection) is exactly the ideal head `attnHead scale W Y`. -/
theorem mixtureOutput_softWeights_eq_attnHead {n d : ℕ} {β scale : ℝ} (hβ : 0 ≤ β)
    (hβscale : β = 1 / scale) (W : Fin d → Fin d → ℝ) (Y : Fin n → Fin d → ℝ) (i : Fin n) :
    mixtureOutput (softWeights (litAttnTempered d n β hβ) Y (Y i)) (matMulCoord W Y)
      = attnHead scale W Y i := by
  rw [softWeights_eq_softmax_smul]
  have hs : (litAttnTempered d n β hβ).β • (litAttnTempered d n β hβ).router.score Y (Y i)
          = attnScores scale (Y i) Y := by
    funext k
    show β * Spec.dot ((Spec.Tensor.dimScalarEquiv d).symm (Y i))
        ((Spec.Tensor.dimScalarEquiv d).symm (Y k)) = (∑ e, Y i e * Y k e) / scale
    rw [spec_dot_equivSymm_eq_sum, hβscale]; ring
  rw [hs]
  simp only [attnHead, attnVec_eq_sum_smul, mixtureOutput]

open Spec in
/-- **The end-to-end soft-output correspondence.** Composing `mixtureOutput_softWeights_eq_attnHead` (at the
standard scale `√d`, hence `β = 1/√d`) with the shipped coordinate binding `matCoords_scaledDotProductAttention`
(`matCoords (scaledDotProductAttention ctx) = attnHead (√d) W Y`), the soft mixture of the literal attention's
routing weights with the literal value vectors is the literal `Spec.scaledDotProductAttention` output read in
coordinates. This is the `val = literal value vectors`, `mixtureOutput = Spec.attention output` identity. -/
theorem mixtureOutput_softWeights_eq_litAttention {n d : ℕ}
    (Y : Fin (n + 1) → Fin d → ℝ) (W : Fin d → Fin d → ℝ)
    (ctx : AttentionContext ℝ (n + 1) (n + 1) d (Nat.succ_ne_zero n) (Nat.succ_ne_zero n))
    (hQ : ctx.Q = matrixTensor Y) (hK : ctx.K = matrixTensor Y)
    (hV : ctx.V = matrixTensor (matMulCoord W Y)) (hmask : ctx.mask = none)
    (hβ : 0 ≤ 1 / MathFunctions.sqrt (d : ℝ)) (i : Fin (n + 1)) :
    mixtureOutput
        (softWeights (litAttnTempered d (n + 1) (1 / MathFunctions.sqrt (d : ℝ)) hβ) Y (Y i))
        (matMulCoord W Y)
      = matCoords (Spec.scaledDotProductAttention ctx) i := by
  rw [matCoords_scaledDotProductAttention Y W ctx hQ hK hV hmask]
  exact mixtureOutput_softWeights_eq_attnHead hβ rfl W Y i

end TLT.TemperedDesignLaw
