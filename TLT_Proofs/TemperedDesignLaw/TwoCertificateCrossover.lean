/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.TwoLedger
import Mathlib.Topology.Order.IntermediateValue

/-!
# The two-certificate minimum and the sharpness crossover (TD11)

The generalization gap of a route-factored objective admits two certificates: a **smooth** certificate
that degrades with the sharpness `β` (the chaining/Dudley capacity of the soft mixture, TD9), and a
**hard** certificate that improves with `β` (the symbol-class capacity, TD10, plus the hardening
leakage `(k−1)·exp(−β·γ)·D`, TD2, which shrinks as `β` grows). The uniform certificate is their
pointwise minimum; because one side is nondecreasing and the other nonincreasing, the binding side
switches once, at a crossover sharpness `βStar`.

* `twoCertMin f g`: the pointwise minimum of two certificates; `gap_le_twoCertMin` is the uniform
  bound (the gap is below both, hence below the minimum).
* `smoothBinding_downClosed`: for a nondecreasing `f` and nonincreasing `g`, the set where the smooth
  side binds (`f ≤ g`) is downward closed, giving the regime structure behind the single crossover.
* `crossover_exists`: under continuity and the endpoint sign conditions, a crossover point exists
  where the two certificates are equal (the intermediate value theorem applied to `f − g`).
* `hardBound_antitone`: the concrete hard certificate `symbolBound + (k−1)·exp(−β·γ)·D` is
  nonincreasing in `β` (via `temperedLedger_antitone_beta`): the `g` side, instantiated at the
  tempered router's hardening leakage.

The smooth certificate `f` enters as a nondecreasing-in-`β` hypothesis, discharged downstream by the
sharpness-scaled Dudley bound `paramStack_empiricalCapacity_le_dudley` (its parameter-Lipschitz
constant is affine increasing in `β`).
-/

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The two-certificate minimum.** The uniform certificate: the pointwise minimum of a smooth
certificate `f` (degrading in sharpness) and a hard certificate `g` (improving in sharpness). -/
def twoCertMin (f g : ℝ → ℝ) : ℝ → ℝ := fun β => min (f β) (g β)

/-- **The uniform bound.** If the generalization gap is below both certificates at sharpness `β`, it
is below their minimum, which is the certificate uniform in `β`. -/
theorem gap_le_twoCertMin {f g : ℝ → ℝ} {gap β : ℝ} (hf : gap ≤ f β) (hg : gap ≤ g β) :
    gap ≤ twoCertMin f g β :=
  le_min hf hg

/-- **The smooth-binding region is downward closed.** For a nondecreasing smooth certificate `f` and a
nonincreasing hard certificate `g`, if the smooth side binds at `β'` (`f β' ≤ g β'`) then it binds at
every smaller `β`. So the smooth side binds on a down-set and the hard side beyond it; this is the regime
structure that makes the crossover a single switch. -/
theorem smoothBinding_downClosed {f g : ℝ → ℝ} (hf : Monotone f) (hg : Antitone g) {β β' : ℝ}
    (hββ' : β ≤ β') (h : f β' ≤ g β') : f β ≤ g β :=
  le_trans (hf hββ') (le_trans h (hg hββ'))

/-- **The crossover exists.** If the smooth certificate `f` starts at or below the hard certificate `g`
(`f a ≤ g a`) and ends at or above it (`g b ≤ f b`), with both continuous on `[a, b]`, then there is a
crossover sharpness `βStar ∈ [a, b]` at which the two certificates are equal, by the intermediate value
theorem applied to `f − g`. -/
theorem crossover_exists {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (ha : f a ≤ g a) (hb : g b ≤ f b) :
    ∃ βStar ∈ Set.Icc a b, f βStar = g βStar := by
  have hc : ContinuousOn (fun x => f x - g x) (Set.Icc a b) := hf.sub hg
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x => f x - g x) a) ((fun x => f x - g x) b) :=
    Set.mem_Icc.mpr ⟨by dsimp only; linarith, by dsimp only; linarith⟩
  obtain ⟨βStar, hmem, heq⟩ := intermediate_value_Icc hab hc h0
  exact ⟨βStar, hmem, by simpa [sub_eq_zero] using heq⟩

/-- **The hard certificate is nonincreasing in sharpness.** The concrete hard bound
`symbolBound + (k−1)·exp(−β·γ)·D` decreases as `β` grows: the symbol-class capacity `symbolBound` is
sharpness invariant and the hardening leakage shrinks (`temperedLedger_antitone_beta`). This is the `g`
side of the crossover, instantiated at the tempered router's leakage. -/
theorem hardBound_antitone {k : ℕ} {symbolBound D γ : ℝ} (hk1 : 0 ≤ (k : ℝ) - 1) (hD : 0 ≤ D)
    (hγ : 0 ≤ γ) :
    Antitone (fun β : ℝ => symbolBound + ((k : ℝ) - 1) * Real.exp (-(β * γ)) * D) := by
  intro β β' hββ'
  dsimp only
  have h := temperedLedger_antitone_beta hk1 hD hγ hββ'
  linarith

end TLT.TemperedDesignLaw
