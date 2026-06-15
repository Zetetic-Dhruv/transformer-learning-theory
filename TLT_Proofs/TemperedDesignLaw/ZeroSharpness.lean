/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.Conjectures

/-!
# The zero-sharpness endpoint: the third regime (GB1)

The sharpness axis has *three* regimes, not two: uniform routing at `β = 0`, tempered on `(0, ∞)`, hard at
the limit. Symbol invariance (`TD1`) holds only on `(0, ∞]`; at the `β = 0` endpoint the mixture weights are
uniform and the symbol channel decouples from the scores entirely. This is the precise boundary where
`TD1`'s strict-positivity hypothesis (`0 < β`) is necessary.

* `softWeights_zero`: at `β = 0` every mixture weight equals `1/k`, uniform and score-independent.
* `leastArgmax_softWeights_zero`: consequently the symbol channel reads the degenerate least index `0`
  regardless of the scores: the symbol channel is broken at the zero endpoint (it agrees with the hard
  route only when the score argmax is already index `0`).
-/

open scoped BigOperators

universe u

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **Uniform routing at zero sharpness.** At `β = 0` the tempered softmax is uniform: every mixture weight
is `1/k`, independent of the scores. The first of the three sharpness regimes (the score-decoupled
endpoint). -/
theorem softWeights_zero {X : Type u} [MeasurableSpace X] {k : ℕ} [NeZero k]
    (A : TemperedRouterFamily X k) (hβ0 : A.β = 0) (ρ : A.router.Ρ) (x : X) (i : Fin k) :
    softWeights A ρ x i = ((k : ℝ))⁻¹ := by
  simp only [softWeights, hβ0, zero_mul, Real.exp_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, one_div]

/-- **The symbol channel breaks at zero sharpness.** Because the weights are uniform, their `leastArgmax`
is the degenerate least index `0` regardless of the scores. The symbol channel no longer tracks the score
argmax. This is the failure of symbol invariance at `β = 0` that forces `TD1`'s `0 < β` hypothesis. -/
theorem leastArgmax_softWeights_zero {X : Type u} [MeasurableSpace X] {k : ℕ} [NeZero k]
    (A : TemperedRouterFamily X k) (hβ0 : A.β = 0) (hk : 0 < k) (ρ : A.router.Ρ) (x : X) :
    leastArgmax (softWeights A ρ x) hk = ⟨0, hk⟩ := by
  refine isLeastArgmax_unique (softWeights A ρ x) (leastArgmax (softWeights A ρ x) hk) ⟨0, hk⟩
    (leastArgmax_spec _ hk) ⟨fun j => ?_, fun j hj => ?_⟩
  · exact le_of_eq (by rw [softWeights_zero A hβ0 ρ x j, softWeights_zero A hβ0 ρ x ⟨0, hk⟩])
  · exact absurd hj (Nat.not_lt_zero j.val)

end TLT.TemperedDesignLaw
