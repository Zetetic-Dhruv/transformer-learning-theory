/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.SymbolChannel

/-!
# The two-sided per-layer leakage law (TD2)

The off-route mass — the mixture channel's total weight on classes other than the hard route — decays
margin-exponentially, two-sided:

* **Upper** `offRouteMass ≤ (k−1)·exp(−β·γ)`: each off-route weight is `exp(β·sᵢ)/Z ≤
  exp(β·s_second)/exp(β·s_top) = exp(−β·γ)`, summed over the `k−1` off-route indices.
* **Lower** `exp(−β·γ)/k ≤ offRouteMass` (for `2 ≤ k`): the second-place weight alone is
  `exp(β·s_second)/Z ≥ exp(β·s_second)/(exp(β·s_top)·k) = exp(−β·γ)/k`, since `Z ≤ exp(β·s_top)·k`.

Softmax's structural privilege among positive routing kernels: margin-linear log-leakage.
-/

open scoped BigOperators

universe u

noncomputable section

namespace TLT.TemperedDesignLaw

/-- Off-route scores are bounded by the second score: for `i ≠ top`, `sᵢ ≤ secondScore`. -/
lemma score_le_secondScore {k : ℕ} (s : Fin k → ℝ) (top i : Fin k) (hi : i ≠ top) :
    s i ≤ secondScore s top := by
  have hmem : i ∈ Finset.univ.filter (fun j => j ≠ top) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  rw [secondScore, dif_pos ⟨i, hmem⟩]
  exact Finset.le_sup' s hmem

/-- **TD2 (upper) — leakage decays margin-exponentially.** -/
theorem TD2_leakage_upper_proof {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : TemperedRouterFamily X k) (hk : 0 < k) : TD2_leakage_upper A hk := by
  intro ρ x
  have hZpos : (0 : ℝ) < ∑ j, Real.exp (A.β * A.router.score ρ x j) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hterm : ∀ i ∈ Finset.univ.filter (fun i => i ≠ hardRoute A hk ρ x),
      softWeights A ρ x i ≤ Real.exp (-(A.β * gammaMargin A hk ρ x)) := by
    intro i hi
    have hitop : i ≠ leastArgmax (A.router.score ρ x) hk := by
      have := (Finset.mem_filter.mp hi).2; rwa [hardRoute_eq_leastArgmax] at this
    have hnum : Real.exp (A.β * A.router.score ρ x i)
        ≤ Real.exp (A.β * secondScore (A.router.score ρ x)
          (leastArgmax (A.router.score ρ x) hk)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (score_le_secondScore _ _ _ hitop) A.hβ)
    have hden : Real.exp (A.β * A.router.score ρ x (leastArgmax (A.router.score ρ x) hk))
        ≤ ∑ j, Real.exp (A.β * A.router.score ρ x j) :=
      Finset.single_le_sum (f := fun j => Real.exp (A.β * A.router.score ρ x j))
        (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ _)
    rw [softWeights, gammaMargin, mul_sub, neg_sub, Real.exp_sub]
    exact div_le_div₀ (Real.exp_pos _).le hnum (Real.exp_pos _) hden
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) (le_of_eq ?_)
  rw [nsmul_eq_mul, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin, Nat.cast_sub hk, Nat.cast_one]

/-- **TD2 (lower) — leakage is not faster than exponential** (with `2 ≤ k`). -/
theorem TD2_leakage_lower_proof {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : TemperedRouterFamily X k) (hk : 0 < k) : TD2_leakage_lower A hk := by
  intro hk2 ρ x
  have hZpos : (0 : ℝ) < ∑ j, Real.exp (A.β * A.router.score ρ x j) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hne : (Finset.univ.filter (fun j => j ≠ leastArgmax (A.router.score ρ x) hk)).Nonempty := by
    obtain ⟨a, ha⟩ := Fintype.exists_ne_of_one_lt_card
      (by rw [Fintype.card_fin]; omega) (leastArgmax (A.router.score ρ x) hk)
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
  obtain ⟨sec, hsec_mem, hsec_eq⟩ := Finset.exists_mem_eq_sup' hne (A.router.score ρ x)
  have hsecScore : A.router.score ρ x sec
      = secondScore (A.router.score ρ x) (leastArgmax (A.router.score ρ x) hk) := by
    rw [secondScore, dif_pos hne]; exact hsec_eq.symm
  have hZle : (∑ j, Real.exp (A.β * A.router.score ρ x j))
      ≤ Real.exp (A.β * A.router.score ρ x (leastArgmax (A.router.score ρ x) hk)) * (k : ℝ) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ (fun j _ => Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (leastArgmax_is_maximizer _ hk j) A.hβ))) (le_of_eq ?_)
    rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, mul_comm]
  have hexp_eq : Real.exp (-(A.β * gammaMargin A hk ρ x))
      = Real.exp (A.β * A.router.score ρ x sec)
        / Real.exp (A.β * A.router.score ρ x (leastArgmax (A.router.score ρ x) hk)) := by
    rw [gammaMargin, ← hsecScore,
      show -(A.β * (A.router.score ρ x (leastArgmax (A.router.score ρ x) hk)
            - A.router.score ρ x sec))
          = A.β * A.router.score ρ x sec
            - A.β * A.router.score ρ x (leastArgmax (A.router.score ρ x) hk) from by ring,
      Real.exp_sub]
  calc Real.exp (-(A.β * gammaMargin A hk ρ x)) / (k : ℝ)
      = Real.exp (A.β * A.router.score ρ x sec)
          / (Real.exp (A.β * A.router.score ρ x (leastArgmax (A.router.score ρ x) hk))
              * (k : ℝ)) := by rw [hexp_eq, div_div]
    _ ≤ Real.exp (A.β * A.router.score ρ x sec)
          / ∑ j, Real.exp (A.β * A.router.score ρ x j) := by gcongr
    _ = softWeights A ρ x sec := rfl
    _ ≤ offRouteMass A hk ρ x :=
        Finset.single_le_sum (f := fun i => softWeights A ρ x i)
          (fun i _ => div_nonneg (Real.exp_pos _).le hZpos.le)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            rw [hardRoute_eq_leastArgmax]; exact (Finset.mem_filter.mp hsec_mem).2⟩)

end TLT.TemperedDesignLaw
