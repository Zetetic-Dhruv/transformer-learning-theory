/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.Conjectures
import TLT_Proofs.Bridge.Lipschitz.SoftmaxJacobian

/-!
# Exactness impossibility at finite sharpness (TD17 part i)

At any finite sharpness `β`, the tempered mixture weights `softWeights A ρ x` are *strictly* below
one in every coordinate: the softmax normaliser sums at least two positive exponentials, so the
numerator is a strict fraction of the denominator. Consequently the soft weights are **never exactly
one-hot** — no coordinate ever reaches the hard value `1`. This is the negative that fences the design
law on the sharpness axis: annealing approaches the argmax but never attains it at any finite `β`.

* `softmax_lt_one` — the kernel: with at least two classes, every softmax coordinate is strictly `< 1`.
* `softWeights_lt_one` — the tempered router instance: every mixture weight is strictly `< 1` at every
  finite `β`, so the mixture is never one-hot.

This is the pointwise (in fact uniform-in-`x`) sharpening of the registered analytic route (the weights
are real-analytic and hence not locally constant); the strict bound gives the exactness impossibility
directly from `softmax_sum_one` and positivity, with no analytic-continuation hypothesis. The executed
shadow is the opposite: finitely many dyadic weights on a finite grid *are* locally constant, which is
why exact hard behaviour is an ideal-tier impossibility, never seen by hardware.
-/

universe u

noncomputable section

namespace TLT

/-- **The softmax exactness bound.** With at least two classes, every softmax coordinate is strictly
below one: the normaliser `∑ⱼ exp (z j)` strictly exceeds the single term `exp (z i)` because some
other coordinate contributes a positive exponential. The strict companion of `softmax_le_one`. -/
lemma softmax_lt_one {n : ℕ} [NeZero n] (z : Fin n → ℝ) (i : Fin n) (hn : 2 ≤ n) :
    softmax z i < 1 := by
  rw [← softmax_sum_one z]
  haveI : Nontrivial (Fin n) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_fin]; omega)
  obtain ⟨j, hj⟩ := exists_ne i
  exact Finset.single_lt_sum hj (Finset.mem_univ i) (Finset.mem_univ j)
    (softmax_pos z j) (fun k _ _ => softmax_nonneg z k)

end TLT

namespace TLT.TemperedDesignLaw

/-- **Exactness impossibility for the tempered mixture (TD17 i).** With at least two classes, every
tempered mixture weight `softWeights A ρ x i` is strictly below one, at every finite sharpness `β` and
every input `x`. Hence the mixture is never exactly one-hot: the soft reading approaches the hard route
but never attains it at any finite `β`. The weight is the softmax of the `β`-scaled scores, so this is
`softmax_lt_one` at `z = β · score`. -/
theorem softWeights_lt_one {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : TemperedRouterFamily X k) (ρ : A.router.Ρ) (x : X) (i : Fin k) (hk2 : 2 ≤ k) :
    softWeights A ρ x i < 1 := by
  haveI : NeZero k := ⟨by omega⟩
  exact softmax_lt_one (fun j => A.β * A.router.score ρ x j) i hk2

end TLT.TemperedDesignLaw
