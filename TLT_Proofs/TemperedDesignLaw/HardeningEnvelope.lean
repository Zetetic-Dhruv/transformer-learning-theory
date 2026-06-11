/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MixtureOutput
import TLT_Proofs.TemperedDesignLaw.LeakageLaw

/-!
# The per-layer hardening closeness (the β-edge per-layer envelope)

The soft mixture output and the hard one-hot output (the payload at the route) differ by exactly the
off-route weighted payload deviation. Centering the payloads at the route, the route term vanishes and the
gap is controlled by the off-route mass times the payload diameter:

* `norm_mixtureOutput_sub_payload_le` — the carrier-agnostic core: for any sub-probability weights summing
  to one and a payload-diameter bound `D`, `‖mixtureOutput w val − val r‖ ≤ (Σ_{i≠r} wᵢ) · D`.
* `softMixture_sub_hardPayload_le` — the router form: the soft mixture is within `offRouteMass · D` of the
  hard payload at the route.
* `softMixture_sub_hardPayload_le_exp` — the β-hardening: chaining the leakage bound (`TD2`), the gap is at
  most `(k−1)·exp(−β·γ)·D`, decaying margin-exponentially in the sharpness. As `β → ∞` the soft layer
  collapses to the hard route — the per-layer envelope of the depth-`L` hardening telescope.

This is the `β`-edge counterpart of the rounding envelope: the per-layer closeness the executed-layer
telescope (`execComp_envelope`) composes into the depth bound, with `β` playing the role of precision.
-/

open scoped BigOperators

universe u

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The carrier-agnostic hardening core.** With nonnegative weights summing to one and a payload-diameter
bound `‖valᵢ − val_r‖ ≤ D`, the mixture output is within `(Σ_{i≠r} wᵢ) · D` of the route payload `val r`:
centering the payloads at `r`, the route term cancels and only the off-route mass survives. -/
theorem norm_mixtureOutput_sub_payload_le {k : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : Fin k → ℝ) (val : Fin k → V) (r : Fin k) {D : ℝ}
    (hwnn : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1) (hD : ∀ i, ‖val i - val r‖ ≤ D) :
    ‖mixtureOutput w val - val r‖ ≤ (∑ i ∈ Finset.univ.filter (· ≠ r), w i) * D := by
  have hcenter : mixtureOutput w val - val r = ∑ i, w i • (val i - val r) := by
    have e1 : ∑ i, w i • (val i - val r) = (∑ i, w i • val i) - (∑ i, w i) • val r := by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => smul_sub _ _ _)
    rw [e1, hwsum, one_smul, mixtureOutput]
  have hdrop : (∑ i, w i • (val i - val r))
      = ∑ i ∈ Finset.univ.filter (· ≠ r), w i • (val i - val r) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) (fun i _ hi => ?_)).symm
    have hir : i = r := by
      by_contra h
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [hir, sub_self, smul_zero]
  rw [hcenter, hdrop]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [norm_smul, Real.norm_of_nonneg (hwnn i)]
  exact mul_le_mul_of_nonneg_left (hD i) (hwnn i)

/-- **The router hardening closeness.** The soft mixture output is within `offRouteMass · D` of the hard
payload `val (hardRoute)`: the carrier-agnostic core with the softmax weights (nonnegative, summing to
one). -/
theorem softMixture_sub_hardPayload_le {X : Type u} [MeasurableSpace X] {k : ℕ} [NeZero k]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : TemperedRouterFamily X k) (hk : 0 < k) (ρ : A.router.Ρ) (x : X) (val : Fin k → V) {D : ℝ}
    (hD : ∀ i, ‖val i - val (hardRoute A hk ρ x)‖ ≤ D) :
    ‖mixtureOutput (softWeights A ρ x) val - val (hardRoute A hk ρ x)‖ ≤ offRouteMass A hk ρ x * D := by
  have hwnn : ∀ i, 0 ≤ softWeights A ρ x i := by
    simp only [softWeights_eq_softmax_smul]; exact fun i => softmax_nonneg _ i
  have hwsum : ∑ i, softWeights A ρ x i = 1 := by
    simp only [softWeights_eq_softmax_smul]; exact softmax_sum_one _
  rw [offRouteMass]
  exact norm_mixtureOutput_sub_payload_le (softWeights A ρ x) val (hardRoute A hk ρ x) hwnn hwsum hD

/-- **The β-hardening per-layer envelope.** Chaining the leakage bound (`TD2`), the soft–hard gap decays
margin-exponentially in the sharpness: `‖soft − hard‖ ≤ (k−1)·exp(−β·γ)·D`. As `β → ∞` the soft layer
collapses to the hard route — the per-layer envelope of the hardening telescope. -/
theorem softMixture_sub_hardPayload_le_exp {X : Type u} [MeasurableSpace X] {k : ℕ} [NeZero k]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : TemperedRouterFamily X k) (hk : 0 < k) (ρ : A.router.Ρ) (x : X) (val : Fin k → V) {D : ℝ}
    (hD : ∀ i, ‖val i - val (hardRoute A hk ρ x)‖ ≤ D) :
    ‖mixtureOutput (softWeights A ρ x) val - val (hardRoute A hk ρ x)‖
      ≤ ((k : ℝ) - 1) * Real.exp (-(A.β * gammaMargin A hk ρ x)) * D := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD (hardRoute A hk ρ x))
  refine (softMixture_sub_hardPayload_le A hk ρ x val hD).trans ?_
  exact mul_le_mul_of_nonneg_right (TD2_leakage_upper_proof A hk ρ x) hD0

end TLT.TemperedDesignLaw
