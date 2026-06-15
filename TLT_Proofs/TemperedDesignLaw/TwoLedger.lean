/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.HardeningEnvelope

/-!
# The per-layer two-ledger decomposition (the β = u meeting point)

The deviation of an *executed* soft layer from the hard route splits, by one triangle step, into two
ledgers over the *same* layer: a **numerical** ledger (the executed mixture vs the ideal-real mixture) and a
**tempered** ledger (the ideal mixture vs the hard route, the margin-exponential hardening). This is the
per-layer kernel of the design law's central identity. The sharpness `β` plays the role of precision `u`,
and the two error sources add exactly as the rounding and approximation envelopes do.

* `executedSoft_sub_hard_two_ledger`: `‖executed − hard‖ ≤ rnd + (k−1)·exp(−β·γ)·D`. The numerical ledger
  `rnd` (an abstract per-layer rounding bound, concretized by the IEEE executed mixture downstream) plus the
  tempered ledger.
* `temperedLedger_antitone_beta`: the tempered ledger is monotone decreasing in the sharpness. More
  sharpness, less hardening leakage.
-/

open scoped BigOperators

universe u

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The per-layer two-ledger bound.** An executed soft layer's deviation from the hard route is at most the
numerical ledger `rnd` (executed vs ideal mixture) plus the tempered ledger `(k−1)·exp(−β·γ)·D` (ideal
mixture vs hard route). One triangle step over the ideal mixture; the two error sources add. -/
theorem executedSoft_sub_hard_two_ledger {X : Type u} [MeasurableSpace X] {k : ℕ} [NeZero k]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : TemperedRouterFamily X k) (hk : 0 < k) (ρ : A.router.Ρ) (x : X) (val : Fin k → V)
    (executedSoft : V) {D rnd : ℝ} (hD : ∀ i, ‖val i - val (hardRoute A hk ρ x)‖ ≤ D)
    (hrnd : ‖executedSoft - mixtureOutput (softWeights A ρ x) val‖ ≤ rnd) :
    ‖executedSoft - val (hardRoute A hk ρ x)‖
      ≤ rnd + ((k : ℝ) - 1) * Real.exp (-(A.β * gammaMargin A hk ρ x)) * D := by
  calc ‖executedSoft - val (hardRoute A hk ρ x)‖
      = ‖(executedSoft - mixtureOutput (softWeights A ρ x) val)
          + (mixtureOutput (softWeights A ρ x) val - val (hardRoute A hk ρ x))‖ := by
            rw [sub_add_sub_cancel]
    _ ≤ ‖executedSoft - mixtureOutput (softWeights A ρ x) val‖
          + ‖mixtureOutput (softWeights A ρ x) val - val (hardRoute A hk ρ x)‖ := norm_add_le _ _
    _ ≤ rnd + ((k : ℝ) - 1) * Real.exp (-(A.β * gammaMargin A hk ρ x)) * D :=
        add_le_add hrnd (softMixture_sub_hardPayload_le_exp A hk ρ x val hD)

/-- **The tempered ledger is monotone in sharpness.** For nonnegative margin and payload diameter, the
hardening ledger `(k−1)·exp(−β·γ)·D` decreases as the sharpness `β` increases: more sharpness, less leakage.
The envelope never grows as `β` increases. -/
theorem temperedLedger_antitone_beta {k : ℕ} {D γ β β' : ℝ}
    (hk1 : 0 ≤ (k : ℝ) - 1) (hD : 0 ≤ D) (hγ : 0 ≤ γ) (hββ' : β ≤ β') :
    ((k : ℝ) - 1) * Real.exp (-(β' * γ)) * D ≤ ((k : ℝ) - 1) * Real.exp (-(β * γ)) * D := by
  apply mul_le_mul_of_nonneg_right _ hD
  apply mul_le_mul_of_nonneg_left _ hk1
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hββ' hγ))

end TLT.TemperedDesignLaw
