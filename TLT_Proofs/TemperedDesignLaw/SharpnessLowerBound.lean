/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.HardeningEnvelope

/-!
# The sharpness rung, lower edge — realizability for large sharpness (TD14 S3)

The upper edge of the sharpness rung bounds the modulus a tempered class can realize; the lower edge says
every hard target *is* realized to any tolerance once the sharpness is large enough. It is the monotone
inversion of the hardening envelope `(k−1)·exp(−β·γ)·D`: solving the exponential for `β` gives the explicit
threshold `β ≥ (1/g)·log((k−1)·D/ε)` past which, on the margin interior `γ ≥ g`, the soft mixture is within
`ε` of the hard payload.

* `softMixture_within_eps_of_beta` — for `β ≥ (1/g)·log((k−1)·D/ε)` and `γ ≥ g`, the soft mixture output is
  within `ε` of the hard route payload. Together with the upper modulus (`temperedClass_dist_le`) this is
  the two-sided sharpness rung.
-/

open scoped BigOperators

universe u

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The realizability lower bound (the sharpness rung, lower edge).** On the margin interior `γ ≥ g`, once
the sharpness exceeds the threshold `(1/g)·log((k−1)·D/ε)` the soft mixture output is within `ε` of the hard
route payload. The monotone inversion of the hardening envelope: the explicit sharpness at which the soft
channel `ε`-realizes the hard target. -/
theorem softMixture_within_eps_of_beta {X : Type u} [MeasurableSpace X] {k : ℕ} [NeZero k]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : TemperedRouterFamily X k) (hk : 0 < k) (ρ : A.router.Ρ) (x : X) (val : Fin k → V)
    {D ε g : ℝ} (hD : ∀ i, ‖val i - val (hardRoute A hk ρ x)‖ ≤ D) (hg : g ≤ gammaMargin A hk ρ x)
    (hk1 : 0 ≤ (k : ℝ) - 1) (hε : 0 < ε) (hg0 : 0 < g) (hkD : 0 < ((k : ℝ) - 1) * D)
    (hβthr : (1 / g) * Real.log (((k : ℝ) - 1) * D / ε) ≤ A.β) :
    ‖mixtureOutput (softWeights A ρ x) val - val (hardRoute A hk ρ x)‖ ≤ ε := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD (hardRoute A hk ρ x))
  -- the executed gap dominated by the envelope at the lower margin `g`
  have hmono : Real.exp (-(A.β * gammaMargin A hk ρ x)) ≤ Real.exp (-(A.β * g)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hg A.hβ))
  have hbound : ‖mixtureOutput (softWeights A ρ x) val - val (hardRoute A hk ρ x)‖
      ≤ ((k : ℝ) - 1) * Real.exp (-(A.β * g)) * D :=
    (softMixture_sub_hardPayload_le_exp A hk ρ x val hD).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hk1) hD0)
  -- the threshold turns the envelope below `ε`
  have hElog : Real.log (((k : ℝ) - 1) * D / ε) ≤ A.β * g := by
    have h := hβthr
    rw [one_div, inv_mul_eq_div, div_le_iff₀ hg0] at h
    exact h
  have hExpLe : ((k : ℝ) - 1) * D / ε ≤ Real.exp (A.β * g) :=
    (Real.log_le_iff_le_exp (div_pos hkD hε)).mp hElog
  have hexp_le : ((k : ℝ) - 1) * Real.exp (-(A.β * g)) * D ≤ ε := by
    rw [Real.exp_neg]
    have h2 : ((k : ℝ) - 1) * D ≤ Real.exp (A.β * g) * ε := (div_le_iff₀ hε).mp hExpLe
    calc ((k : ℝ) - 1) * (Real.exp (A.β * g))⁻¹ * D
        = ((k : ℝ) - 1) * D / Real.exp (A.β * g) := by ring
      _ ≤ ε := (div_le_iff₀ (Real.exp_pos _)).mpr (h2.trans_eq (mul_comm _ _))
  exact hbound.trans hexp_le

end TLT.TemperedDesignLaw
