/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.Stability

/-!
# Margin transport (making the region condition concrete, TD3 S3)

The depth bounds rest on the ideal trajectory staying in the margin interior `{γ ≥ g}` by an envelope's
worth of slack. That is only meaningful if the margin cannot collapse under a small perturbation — i.e. if
the margin *transports*: a state within `δ` of one with large margin still has a margin not much smaller.

The subtlety is that `γ = top − second` is built from order statistics whose witnessing indices can switch.
The clean route fixes the index: within *half* the margin (the route-stability regime, `TD7`) the top index
does **not** move, so the second score is a supremum over a **fixed** complement and transports by the raw
per-coordinate Lipschitz bound. The margin then drops by at most twice the score perturbation.

* `gammaMargin_lower_of_close` — if the scores at `z` differ from those at `i` by at most `Ks·d` per head
  and that is below half the margin at `i`, then `γ(z) ≥ γ(i) − 2·Ks·d`.

This is what turns the abstract `idealDeep` (closed balls inside the regions) into a checkable property of
the ideal trajectory's margins: a ball of radius `δ` around a state with margin `≥ g + 2·Ks·δ` lies in
`{γ ≥ g}`.
-/

open scoped BigOperators

universe u

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **Margin transport.** With at least two heads, if every score at `z` is within `Ks·d` of the score at
`i`, and `2·Ks·d` is below the margin at `i` (the route-stability regime), then the margin at `z` is at
least the margin at `i` minus `2·Ks·d`. The top index is pinned by `TD7`, so the second score is a supremum
over a fixed complement and transports coordinatewise. -/
theorem gammaMargin_lower_of_close {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : TemperedRouterFamily X k) (hk : 0 < k) (hk2 : 2 ≤ k) (ρ : A.router.Ρ) (z i : X) {Ks d : ℝ}
    (hLip : ∀ j, |A.router.score ρ z j - A.router.score ρ i j| ≤ Ks * d)
    (hstable : 2 * (Ks * d) < gammaMargin A hk ρ i) :
    gammaMargin A hk ρ i - 2 * (Ks * d) ≤ gammaMargin A hk ρ z := by
  have htz : leastArgmax (A.router.score ρ z) hk = leastArgmax (A.router.score ρ i) hk :=
    leastArgmax_stable_of_half_margin _ _ hk hLip hstable
  rw [gammaMargin, gammaMargin, htz]
  set ti := leastArgmax (A.router.score ρ i) hk with hti
  have hne : (Finset.univ.filter (fun j => j ≠ ti)).Nonempty := by
    obtain ⟨a, ha⟩ := Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; exact hk2) ti
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
  have h_top : A.router.score ρ i ti - Ks * d ≤ A.router.score ρ z ti := by
    have := (abs_le.mp (hLip ti)).1; linarith
  have h_sec : secondScore (A.router.score ρ z) ti ≤ secondScore (A.router.score ρ i) ti + Ks * d := by
    rw [secondScore, dif_pos hne, secondScore, dif_pos hne]
    apply Finset.sup'_le
    intro j hj
    have hjle : A.router.score ρ z j ≤ A.router.score ρ i j + Ks * d := by
      have := (abs_le.mp (hLip j)).2; linarith
    have hsup : A.router.score ρ i j ≤
        (Finset.univ.filter (fun j => j ≠ ti)).sup' hne (A.router.score ρ i) :=
      Finset.le_sup' (A.router.score ρ i) hj
    linarith [hjle, hsup]
  linarith [h_top, h_sec]

/-- **The concrete region condition.** If the score read is `Ks`-Lipschitz around `i` and the margin at `i`
exceeds `g` by `2·Ks·δ`, then every state within `δ` of `i` has margin at least `g` — i.e. the closed
`δ`-ball around `i` lies in the margin interior `{γ ≥ g}`. This is exactly the first conjunct of `idealDeep`
for the hardening layer's region, now reduced to a checkable inequality on the ideal trajectory's margin
(`γ(i) ≥ g + 2·Ks·δ`) rather than an abstract ball-containment. -/
theorem marginInterior_of_margin_slack {X : Type u} [MeasurableSpace X] [PseudoMetricSpace X] {k : ℕ}
    (A : TemperedRouterFamily X k) (hk : 0 < k) (hk2 : 2 ≤ k) (ρ : A.router.Ρ) (i : X) {g δ Ks : ℝ}
    (hKs : 0 ≤ Ks) (hg : 0 < g)
    (hLip : ∀ z j, |A.router.score ρ z j - A.router.score ρ i j| ≤ Ks * dist z i)
    (hi : g + 2 * Ks * δ ≤ gammaMargin A hk ρ i) :
    ∀ z, dist z i ≤ δ → g ≤ gammaMargin A hk ρ z := by
  intro z hz
  have hKsd : Ks * dist z i ≤ Ks * δ := mul_le_mul_of_nonneg_left hz hKs
  have hstable : 2 * (Ks * dist z i) < gammaMargin A hk ρ i := by nlinarith [hi, hg, hKsd]
  have htrans := gammaMargin_lower_of_close A hk hk2 ρ z i (fun j => hLip z j) hstable
  nlinarith [htrans, hi, hKsd]

end TLT.TemperedDesignLaw
