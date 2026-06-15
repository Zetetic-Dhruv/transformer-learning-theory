/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Spec.ScaledDotProductScoreRouter

/-!
# Soft (softmax-weighted) attention is well-behaved

The argmax/top-1 router discretizes attention; the actual transformer output is the
softmax-weighted average of values, `out(K, V, x) = ∑ᵢ softmax(⟨x, Kᵢ⟩)ᵢ · Vᵢ`. This file shows
the soft-attention concept class (thresholding that value-weighted softmax output) satisfies
`WellBehavedVCMeasTarget`, using TorchLean's `Spec.dot` scores (via `attentionScoreRouter`),
`softmaxWeight`, and the Borel-parameter bridge.

## Main results

- `softAttentionConcept`: the thresholded value-weighted softmax-attention output, as a concept.
- `softAttention_wellBehaved`: its concept class satisfies `WellBehavedVCMeasTarget`.
-/

/-!
## References
- [27] softmax-weighted attention readout; [29] softmax measurability; [7][2][4] analytic/
  measurability bridge; [9] joint measurability; [57] FLT `borel_param_wellBehavedVCMeasTarget`.
-/

open MeasureTheory Set

noncomputable section

namespace TLT.Bridge

variable {d nK : ℕ}

/-- The value-weighted softmax-attention output as a concept: threshold `∑ᵢ wᵢ · Vᵢ` at `0`, where
`wᵢ = softmax(⟨x, Kᵢ⟩)ᵢ` are the softmax weights of TorchLean's `Spec.dot` scores. The parameter
bundles the keys `K` and the values `V`. -/
def softAttentionConcept (d nK : ℕ)
    (KV : (Fin nK → Fin d → ℝ) × (Fin nK → ℝ)) : Concept (Fin d → ℝ) Bool :=
  fun x => decide (0 < ∑ i : Fin nK, softmaxWeight (attentionScoreRouter d nK) KV.1 x i * KV.2 i)

/-- The value-weighted softmax output is jointly measurable in the parameters `(K, V)` and the
input `x`. -/
private lemma softAttentionOut_measurable (d nK : ℕ) :
    Measurable (fun p : ((Fin nK → Fin d → ℝ) × (Fin nK → ℝ)) × (Fin d → ℝ) =>
      ∑ i : Fin nK, softmaxWeight (attentionScoreRouter d nK) p.1.1 p.2 i * p.1.2 i) := by
  refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
  exact ((softmaxWeight_measurable (attentionScoreRouter d nK) i).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
    ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))

/-- The `true`-preimage of the soft-attention family is the positivity set of the output. -/
private lemma softAttention_preimage (d nK : ℕ) :
    (fun p : ((Fin nK → Fin d → ℝ) × (Fin nK → ℝ)) × (Fin d → ℝ) =>
        softAttentionConcept d nK p.1 p.2) ⁻¹' {true}
      = {p | 0 < ∑ i : Fin nK, softmaxWeight (attentionScoreRouter d nK) p.1.1 p.2 i * p.1.2 i} := by
  ext p
  simp [softAttentionConcept]

/-- **Soft attention is well-behaved.** The thresholded value-weighted softmax-attention concept
class satisfies `WellBehavedVCMeasTarget` (the softmax-weighted attention readout, not the argmax
discretization). -/
theorem softAttention_wellBehaved (d nK : ℕ) :
    WellBehavedVCMeasTarget (Fin d → ℝ) (Set.range (softAttentionConcept d nK)) := by
  refine borel_param_wellBehavedVCMeasTarget (softAttentionConcept d nK) ?_
  apply measurable_to_bool
  rw [softAttention_preimage]
  exact measurableSet_lt measurable_const (softAttentionOut_measurable d nK)

end TLT.Bridge
