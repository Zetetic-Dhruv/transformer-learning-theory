/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.SymbolCapacity
import FLT_Proofs.Complexity.IndependentVC.Pseudodimension

/-!
# The capacity face of the symbol route's comparisons (the capacity ↔ opcount junction)

The opcount reading (`SymbolOpcount`) shows the hard route factors through the Boolean
`≤`-comparison matrix. The **dual** capacity reading of that same comparison object is as
follows: each per-pair comparison is a **halfspace** (the sign of the score difference), so, when
the scores are linear, its VC dimension is controlled by the Dudley sign-class bound.

## Results
* `comparisonConcept_eq_sign_sub`: a score comparison `sᵢ ≤ sⱼ` is exactly the sign concept
  `0 ≤ sⱼ − sᵢ` of the score-difference functional. The comparison class is therefore a class of
  halfspaces; the *same* comparison matrix `argmaxFromCmp` reads (opcount), now read as a halfspace.
* `comparisonClass_vcDim_le`: **conditional Dudley/VC bound (the capacity face).** If the per-pair
  score-difference functionals lie in a finite-dimensional subspace `W ≤ (X → ℝ)` (the **linearity**
  hypothesis: scores affine in a finite feature map), then `VCDim X (comparisonClass A i j) ≤
  finrank ℝ W`, via the embedding into FLT's non-strict sign class `signClassLE W`
  (`FLT_Proofs.Complexity.IndependentVC.Pseudodimension.vcDim_signClassLE_le`, the Dudley 1978 /
  Wenocur–Dudley 1981 bound). For arbitrary measurable scores the bound is false, so the linearity
  hypothesis is essential. Non-strict `signClassLE` (`0 ≤ g`), not strict `signClass` (`0 < g`): the
  tie `sᵢ = sⱼ` is the one the least-index argmax breaks.

The capacity face is dual to the opcount factorization: one comparison object, read two ways.
`argmaxFromCmp` (opcount: zero transcendental, exact) and a halfspace (capacity: Dudley-VC-bounded).
-/

namespace TLT.Routing.Capacity

open TLT.TemperedDesignLaw

variable {X : Type*} [MeasurableSpace X] {k : ℕ}

/-- **A score comparison is a halfspace.** The per-pair comparison concept `sᵢ ≤ sⱼ` equals the sign
concept `0 ≤ sⱼ − sᵢ` of the score-difference functional `x ↦ sⱼ(x) − sᵢ(x)`. Proved by
`sub_nonneg`. The VC bound is `comparisonClass_vcDim_le`. -/
theorem comparisonConcept_eq_sign_sub (A : FiniteScoreRouterCode X k) (ρ : A.Ρ) (i j : Fin k) :
    comparisonConcept A ρ i j = fun x => decide (0 ≤ A.score ρ x j - A.score ρ x i) := by
  funext x
  simp only [comparisonConcept, decide_eq_decide]
  exact sub_nonneg.symm

/-- **The comparison class is Dudley-VC-bounded (capacity face, conditional on linearity).** If every
per-pair score-difference functional `x ↦ sⱼ(x) − sᵢ(x)` lies in a finite-dimensional subspace `W` of
`(X → ℝ)` (the linearity hypothesis, satisfied when the scores are affine in a finite feature map),
then the comparison class embeds in the non-strict sign class `signClassLE W` (each comparison is the
sign concept of its difference, which lies in `W`, by `comparisonConcept_eq_sign_sub`), so its VC
dimension is at most `finrank ℝ W` by FLT's Dudley bound `vcDim_signClassLE_le`.

Conditional on `hlin`: for arbitrary measurable scores the comparison class is unrestricted and the
bound is false, so the hypothesis is essential; it is exactly the linearity of the router's scores. -/
theorem comparisonClass_vcDim_le (A : FiniteScoreRouterCode X k) (i j : Fin k)
    (W : Submodule ℝ (X → ℝ)) [FiniteDimensional ℝ W]
    (hlin : ∀ ρ : A.Ρ, (fun x => A.score ρ x j - A.score ρ x i) ∈ W) :
    VCDim X (comparisonClass A i j) ≤ (Module.finrank ℝ W : WithTop ℕ) := by
  refine le_trans (vcDim_mono ?_) (vcDim_signClassLE_le W)
  intro c hc
  simp only [comparisonClass, Set.mem_range] at hc
  obtain ⟨ρ, rfl⟩ := hc
  exact ⟨_, hlin ρ, comparisonConcept_eq_sign_sub A ρ i j⟩

end TLT.Routing.Capacity
