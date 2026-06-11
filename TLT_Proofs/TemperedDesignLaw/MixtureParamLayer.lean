/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MixtureLayer
import TLT_Proofs.Bridge.Lipschitz.ParameterPerturbationEnvelope

/-!
# The tempered mixture layer as a `ParamLayer` (the capacity hand-off)

Packaging the tempered mixture layer as a `ParamLayer` makes it a first-class citizen of the shipped
parameter-perturbation machinery: a *stack* of tempered layers then inherits the depth-`L`
parameter-Lipschitz bound `paramComp_param_lipschitz` (with `paramLipBound` the per-layer telescope), and
through it the Dudley covering/capacity bound — with the sharpness `β` carried linearly in every per-layer
constant.

* `temperedParamLayer` — the constructor. From a score read and a payload read that are Lipschitz in *both*
  the parameter and the input (with a payload-size bound), it builds the `ParamLayer` whose two Lipschitz
  constants are `2·β·Ksθ·P + Kvθ` (parameter axis) and `2·β·Ksy·P + Kvy` (input axis). Both discharge by the
  per-layer modulus `temperedMixtureMap_param_dist_le`, read on the two currying axes.

No new depth lemma is introduced: the depth bound is the shipped `paramComp_param_lipschitz` applied to a
list of these layers. The sharpness scaling is the content — every constant is linear in `β`.
-/

open scoped BigOperators

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The tempered mixture layer as a `ParamLayer`.** Given a score read `score` and payload read `val` that
are `Ksθ`/`Kvθ`-Lipschitz in the parameter (uniformly in the input), `Ksy`/`Kvy`-Lipschitz in the input
(uniformly in the parameter), and payload-size–bounded by `P`, the layer
`(θ, y) ↦ mixtureOutput (softmax (β • score θ y)) (val θ y)` is a `ParamLayer` with parameter modulus
`2·β·Ksθ·P + Kvθ` and input modulus `2·β·Ksy·P + Kvy`. A stack of these inherits the shipped depth-`L`
parameter-Lipschitz bound. -/
def temperedParamLayer {k : ℕ} [NeZero k] {Θ : Type*} [PseudoMetricSpace Θ]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : ℝ) (score : Θ → V → Fin k → ℝ) (val : Θ → V → Fin k → V) (Ksθ Kvθ Ksy Kvy P : ℝ)
    (hβ : 0 ≤ β) (hKsθ : 0 ≤ Ksθ) (hKvθ : 0 ≤ Kvθ) (hKsy : 0 ≤ Ksy) (hKvy : 0 ≤ Kvy) (hP : 0 ≤ P)
    (hScoreθ : ∀ y θ θ', dist (score θ y) (score θ' y) ≤ Ksθ * dist θ θ')
    (hValθ : ∀ y θ θ', dist (val θ y) (val θ' y) ≤ Kvθ * dist θ θ')
    (hScorey : ∀ θ a b, dist (score θ a) (score θ b) ≤ Ksy * dist a b)
    (hValy : ∀ θ a b, dist (val θ a) (val θ b) ≤ Kvy * dist a b)
    (hValbd : ∀ θ y, (∑ i, ‖val θ y i‖) ≤ P) : ParamLayer Θ V where
  map θ y := mixtureOutput (softmax (β • score θ y)) (val θ y)
  paramLip := 2 * β * Ksθ * P + Kvθ
  lip := 2 * β * Ksy * P + Kvy
  paramLip_nonneg := by
    have h := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hβ) hKsθ) hP
    linarith
  lip_nonneg := by
    have h := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hβ) hKsy) hP
    linarith
  param_lipschitz θ θ' y :=
    temperedMixtureMap_param_dist_le hβ (hScoreθ y) (hValθ y) (fun a => hValbd a y) θ θ'
  input_lipschitz θ a b :=
    temperedMixtureMap_param_dist_le hβ (hScorey θ) (hValy θ) (fun c => hValbd θ c) a b

end TLT.TemperedDesignLaw
