/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Tame.FiniteCellRouter
import TLT_Proofs.Tame.SingletonBadEventBorel
import NN.Spec.Core.Tensor
import NN.Proofs.Tensor.Basic
import NN.Proofs.Tensor.Algebra

/-!
# Scaled-dot-product attention routing is well-behaved

The per-key attention score `⟨x, Kᵢ⟩` is TorchLean's `Spec.dot` of the query and key vector
tensors (the `Q Kᵀ` entry: `attentionScores ctx = matMulSpec ctx.Q (matrixTransposeSpec ctx.K)`).
This file instantiates `FiniteScoreRouterCode` with that score, so the attention argmax routing
inherits `WellBehavedVCMeasTarget` from `finiteCellRouter_wellBehaved`.

The router is stated over coordinate query/key vectors `Fin d → ℝ` (carried to vector tensors by
`Tensor.dimScalarEquiv`), where the `MeasurableSpace` / `PolishSpace` / `BorelSpace` /
`StandardBorelSpace` instances are the native `Pi` instances; the score is TorchLean's `Spec.dot`,
reduced to a coordinate sum by `Spec.dot_vec_eq_sum`.

## Main results

- `attentionScoreRouter` — TorchLean's `Spec.dot` attention score as a `FiniteScoreRouterCode`.
- `attentionRouting_wellBehaved` — its patched class satisfies `WellBehavedVCMeasTarget`.
-/

/-!
## References
- [27] §3.2.1 scaled dot-product score `QKᵀ`; [53] `Spec.dot`/`matMulSpec`; standard measurability
  of coordinate sums; [57] FLT/TLT tame lemmas (instantiated, not proved here).
- Provenance: Vendored-glue (binds the literal TorchLean score to the tame router).
-/

open MeasureTheory Set

noncomputable section

namespace TLT.Bridge

variable {d nK : ℕ}

/-- TorchLean's `Spec.dot` of two coordinate vectors (carried to vector tensors by the inverse of
`Tensor.dimScalarEquiv`) is the coordinate inner product.  Combines `Spec.dot_vec_eq_sum` with the
coordinate round-trip `toVec ∘ dimScalarEquiv.symm = id`. -/
private lemma dot_dimScalarEquivSymm_eq_sum (x y : Fin d → ℝ) :
    Spec.dot ((Spec.Tensor.dimScalarEquiv d).symm x) ((Spec.Tensor.dimScalarEquiv d).symm y)
      = ∑ j : Fin d, x j * y j := by
  rw [Spec.dot_vec_eq_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [Spec.toVec, Spec.Tensor.dimScalarEquiv, Spec.Tensor.ofScalar]

/-- TorchLean's scaled-dot-product attention score as a `FiniteScoreRouterCode`: the input is a
query coordinate vector `Fin d → ℝ`, the parameter is the key matrix `Fin nK → Fin d → ℝ`, and the
score for head/key `i` is `Spec.dot x Kᵢ` — exactly `attentionScores`'s `(·, i)` entry. -/
def attentionScoreRouter (d nK : ℕ) : FiniteScoreRouterCode (Fin d → ℝ) nK where
  Ρ := Fin nK → Fin d → ℝ
  instMeasΡ := inferInstance
  instStdΡ := inferInstance
  score := fun K x i =>
    Spec.dot ((Spec.Tensor.dimScalarEquiv d).symm x) ((Spec.Tensor.dimScalarEquiv d).symm (K i))
  score_meas := fun i => by
    simp only [dot_dimScalarEquivSymm_eq_sum]
    refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
    exact ((measurable_pi_apply j).comp measurable_snd).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst))

/-- With Borel-parameterized experts, the patched class of the scaled-dot-product attention argmax
router satisfies `WellBehavedVCMeasTarget`, via `finiteCellRouter_wellBehaved`. -/
theorem attentionRouting_wellBehaved (hnK : 0 < nK) {Θ : Type}
    [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (e : Θ → Fin nK → Concept (Fin d → ℝ) Bool)
    (he : ∀ i, Measurable (fun p : Θ × (Fin d → ℝ) => e p.1 i p.2)) :
    WellBehavedVCMeasTarget (Fin d → ℝ)
      (Set.range (multiPatchEval e ((attentionScoreRouter d nK).route hnK))) :=
  finiteCellRouter_wellBehaved hnK e (attentionScoreRouter d nK) he

/-- The scaled-dot-product attention score `K ↦ ⟨x, Kᵢ⟩`, as a function of the **key parameters**,
is continuous: over the coordinate sum `∑ⱼ xⱼ·Kᵢⱼ` it is a finite sum of coordinate projections
scaled by constants. -/
theorem continuous_attentionScore (d nK : ℕ) (x : Fin d → ℝ) (i : Fin nK) :
    Continuous (fun K : Fin nK → Fin d → ℝ => (attentionScoreRouter d nK).score K x i) := by
  simp only [attentionScoreRouter, dot_dimScalarEquivSymm_eq_sum]
  exact continuous_finset_sum Finset.univ (fun j _ =>
    continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))

/-- **The concrete attention bad event is Borel.** Instantiating the abstract tame result
(`singletonBadEvent_measurable_of_sigmaCompact`) on the *actual* finite-dimensional attention
parameter space `Fin nK → Fin d → ℝ`: that space is σ-compact, and the scaled-dot-product score map
over it is continuous, so the singleton-class empirical-process bad event of the attention scores is
Borel. This is the end-to-end instantiation on a concrete finite-dimensional transformer parameter
space — the tame side realized for the actual attention scoring, not an abstract score map. -/
theorem attentionScore_badEvent_measurable (d nK : ℕ) (x : Fin d → ℝ) (i : Fin nK) :
    MeasurableSet (singletonBadEvent
      (Set.range (fun K : Fin nK → Fin d → ℝ => (attentionScoreRouter d nK).score K x i))) :=
  TLT.Tame.singletonBadEvent_measurable_of_sigmaCompact (continuous_attentionScore d nK x i)

end TLT.Bridge
