/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MarginTransport
import TLT_Proofs.TemperedDesignLaw.RegionForwardSlack

/-!
# Per-network margin discharge of the ideal-depth condition (TD3)

The depth-`L` hardening bound rests on the ideal trajectory staying deep in the regions (`idealDeep`), whose
conjuncts are abstract ball-containments `∀ z, dist z (M^[ℓ] i) ≤ δ_ℓ → z ∈ region`. `marginInterior_of_margin_slack`
discharges *one* such conjunct from a margin inequality `γ(i) ≥ g + 2Ks·δ`. This file lifts that through the
homogeneous depth recursion so the whole `idealDeep` for a replicated layer reduces to a checkable family of
per-depth margin inequalities along the ideal trajectory.

* `hardeningRadius` — the ideal-ball radius at depth `ℓ`: `δ₀ = δ`, `δ_{ℓ+1} = rnd + lip·δ_ℓ`, the same
  recursion `idealDeep` runs along `List.replicate L hl`.
* `hardeningRadius_shift` — one ideal step shifts the radius sequence (`δ'_ℓ = δ_{ℓ+1}` for `δ' = rnd + lip·δ`).
* `idealDeep_of_trajectoryMargins` — if the scores are `Ks`-Lipschitz, the layer's region is the margin
  interior `{γ ≥ g}`, and the ideal trajectory's margin at each depth exceeds `g` by `2Ks·δ_ℓ`, then `idealDeep`
  holds. This turns the abstract ball-containments into the per-network margin inequalities
  `γ(M^[ℓ] i) ≥ g + 2Ks·δ_ℓ` along the soft trajectory `M = hl.ideal`; a concrete weight configuration
  discharges them by exhibiting its own trajectory margins.
-/

universe u

noncomputable section

namespace TLT.TemperedDesignLaw

/-- The ideal-ball radius at depth `ℓ` in a homogeneous region cascade with per-layer rounding `rnd` and
ideal-map Lipschitz constant `lip`: `δ₀ = δ`, `δ_{ℓ+1} = rnd + lip·δ_ℓ`. This is the radius `idealDeep` carries
along `List.replicate L hl`. -/
def hardeningRadius (rnd lip δ : ℝ) : ℕ → ℝ
  | 0 => δ
  | ℓ + 1 => rnd + lip * hardeningRadius rnd lip δ ℓ

/-- One ideal step shifts the radius sequence: stepping `ℓ` times from the next radius `rnd + lip·δ` equals
stepping `ℓ+1` times from `δ`. -/
lemma hardeningRadius_shift (rnd lip δ : ℝ) (ℓ : ℕ) :
    hardeningRadius rnd lip (rnd + lip * δ) ℓ = hardeningRadius rnd lip δ (ℓ + 1) := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
      show rnd + lip * hardeningRadius rnd lip (rnd + lip * δ) ℓ
         = rnd + lip * hardeningRadius rnd lip δ (ℓ + 1)
      rw [ih]

/-- **The ideal-depth condition from per-network trajectory margins.** For a homogeneous region cascade
`List.replicate L hl` whose region is the margin interior `{γ ≥ g}` and whose scores are `Ks`-Lipschitz, if the
ideal trajectory's margin at every depth `ℓ` exceeds `g` by `2Ks·δ_ℓ` (the growing ideal-ball radius), then the
ideal trajectory stays deep in the regions. Each abstract ball-containment conjunct of `idealDeep` is discharged
by `marginInterior_of_margin_slack` at the corresponding trajectory point; the depth induction shifts the
radius (`hardeningRadius_shift`) and the trajectory (`Function.iterate_succ_apply`) together. -/
theorem idealDeep_of_trajectoryMargins {V : Type u} [MeasurableSpace V] [PseudoMetricSpace V] {k : ℕ}
    (A : TemperedRouterFamily V k) (hk : 0 < k) (hk2 : 2 ≤ k) (ρ : A.router.Ρ) (hl : RegionExecLayer V)
    {g Ks : ℝ} (hKs : 0 ≤ Ks) (hg : 0 < g)
    (hregion : ∀ y, y ∈ hl.region ↔ g ≤ gammaMargin A hk ρ y)
    (hLip : ∀ z w j, |A.router.score ρ z j - A.router.score ρ w j| ≤ Ks * dist z w)
    (L : ℕ) (i : V) (δ : ℝ)
    (hmargin : ∀ ℓ, ℓ < L →
      g + 2 * Ks * hardeningRadius hl.rnd hl.lip δ ℓ ≤ gammaMargin A hk ρ (hl.ideal^[ℓ] i)) :
    idealDeep (List.replicate L hl) i δ := by
  induction L generalizing i δ with
  | zero => exact trivial
  | succ L ih =>
      rw [List.replicate_succ]
      simp only [idealDeep]
      refine ⟨fun z hz => ?_, ?_⟩
      · rw [hregion]
        have h0 := hmargin 0 (Nat.succ_pos L)
        simp only [hardeningRadius, Function.iterate_zero_apply] at h0
        exact marginInterior_of_margin_slack A hk hk2 ρ i hKs hg (fun z' j => hLip z' i j) h0 z hz
      · refine ih (hl.ideal i) (hl.rnd + hl.lip * δ) (fun ℓ hℓ => ?_)
        have hm := hmargin (ℓ + 1) (Nat.succ_lt_succ hℓ)
        rw [hardeningRadius_shift]
        rwa [Function.iterate_succ_apply] at hm

end TLT.TemperedDesignLaw
