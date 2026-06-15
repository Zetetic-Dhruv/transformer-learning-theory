/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.LeakageLaw

/-!
# Float-symbol stability: the u-shell theorem (TD7)

The route label survives a per-coordinate score perturbation strictly below half the margin. The general
fact is order-theoretic: if every executed score is within `b` of the exact score and `2·b < γ` (the
top-minus-second margin), then the executed `leastArgmax` equals the exact `leastArgmax`. Instantiated at
the executed scores (the per-coordinate budget `b` from `rdotBudget`), this gives the exact decision off
the `u`-shell.
-/

open scoped BigOperators

universe u

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The general argmax-perturbation lemma (the strongest form).** If every coordinate of `sExec` is
within `b` of `s` and `2·b` is below the margin `s_top − s_second`, the two vectors have the same
`leastArgmax`. The reusable order-theoretic core of float-symbol stability: an off-route score, lifted by
`b`, still cannot reach the top score lowered by `b`, because the gap exceeds `2·b`. -/
theorem leastArgmax_stable_of_half_margin {k : ℕ} (s sExec : Fin k → ℝ) (hk : 0 < k) {b : ℝ}
    (hb : ∀ i, |sExec i - s i| ≤ b)
    (hm : 2 * b < s (leastArgmax s hk) - secondScore s (leastArgmax s hk)) :
    leastArgmax sExec hk = leastArgmax s hk := by
  refine isLeastArgmax_unique sExec _ _ (leastArgmax_spec sExec hk) ?_
  have hkey : ∀ j, j ≠ leastArgmax s hk → sExec j < sExec (leastArgmax s hk) := by
    intro j hj
    have h1 : sExec j ≤ s j + b := by have := (abs_le.mp (hb j)).2; linarith
    have h2 : s j ≤ secondScore s (leastArgmax s hk) := score_le_secondScore s _ j hj
    have h3 : s (leastArgmax s hk) - b ≤ sExec (leastArgmax s hk) := by
      have := (abs_le.mp (hb (leastArgmax s hk))).1; linarith
    linarith
  exact ⟨fun j => by
      by_cases hj : j = leastArgmax s hk
      · exact le_of_eq (by rw [hj])
      · exact (hkey j hj).le,
    fun j hjlt => hkey j (ne_of_lt hjlt)⟩

/-- **TD7: the executed route equals the ideal route off the u-shell.** Whenever the per-coordinate
score budget `b` satisfies `2·b < γ`, the `leastArgmax` of any executed scores within `b` of the exact
scores is the hard route. -/
theorem TD7_route_stable_proof {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : TemperedRouterFamily X k) (hk : 0 < k) : TD7_route_stable A hk := by
  intro ρ x sExec b hb hmargin
  rw [hardRoute_eq_leastArgmax]
  exact leastArgmax_stable_of_half_margin (A.router.score ρ x) sExec hk hb hmargin

end TLT.TemperedDesignLaw
