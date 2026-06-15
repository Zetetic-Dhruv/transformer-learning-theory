/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MixtureLayer

/-!
# The sharpness rung: the mixture channel's modulus and unrealizability certificates

A function is in the **tempered class** at sharpness `β` if it is realized as the tempered mixture map of a
`Ks`-Lipschitz score read and a `Kv`-Lipschitz, `P`-bounded payload read over the *input*. The per-layer
modulus (`temperedMixtureMap_param_dist_le`, instantiated on the input axis) then bounds every member
uniformly:

* `TemperedClass`: the set of input-to-output maps realizable at sharpness `β` with the stated moduli.
* `temperedClass_dist_le`: the uniform modulus; every member is `(2·β·Ks·P + Kv)`-Lipschitz.
* `not_mem_temperedClass_of_dist_gt`: the unrealizability certificate. A target with a witnessed pair
  `x, x'` whose output gap exceeds the modulus is not in the class. The witness pair is the (dyadic-checkable)
  certificate of unrealizability; no characterization of the realizable image is claimed, only the modulus.

This is the upper, expressivity-bounding edge of the sharpness rung: at fixed sharpness the mixture channel
cannot realize targets steeper than its modulus, and the modulus grows linearly in `β`.
-/

open scoped BigOperators

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The tempered class** at sharpness `β` (with score-Lipschitz `Ks`, payload-Lipschitz `Kv`, payload-size
bound `P`): the input-to-output maps realized as a tempered mixture map of a `Ks`-Lipschitz score read and a
`Kv`-Lipschitz, `P`-bounded payload read. Empty for `β < 0`. -/
def TemperedClass {k : ℕ} {X : Type*} [PseudoMetricSpace X] {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (β Ks Kv P : ℝ) : Set (X → V) :=
  {f | 0 ≤ β ∧ ∃ (score : X → Fin k → ℝ) (val : X → Fin k → V),
    (∀ x x', dist (score x) (score x') ≤ Ks * dist x x') ∧
    (∀ x x', dist (val x) (val x') ≤ Kv * dist x x') ∧
    (∀ x, (∑ i, ‖val x i‖) ≤ P) ∧
    f = temperedMixtureMap β score val}

/-- **The uniform modulus.** Every member of the tempered class is `(2·β·Ks·P + Kv)`-Lipschitz: the
per-layer modulus applied on the input axis. The sharpness `β` bounds the steepness the channel can realize,
linearly. -/
theorem temperedClass_dist_le {k : ℕ} [NeZero k] {X : Type*} [PseudoMetricSpace X] {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {β Ks Kv P : ℝ} {f : X → V}
    (hf : f ∈ TemperedClass (k := k) β Ks Kv P) (x x' : X) :
    dist (f x) (f x') ≤ (2 * β * Ks * P + Kv) * dist x x' := by
  simp only [TemperedClass, Set.mem_setOf_eq] at hf
  obtain ⟨hβ, score, val, hsc, hvl, hvb, hfeq⟩ := hf
  rw [hfeq]
  exact temperedMixtureMap_param_dist_le hβ hsc hvl hvb x x'

/-- **The unrealizability certificate.** A target with a witnessed pair `x, x'` whose output gap exceeds the
modulus `(2·β·Ks·P + Kv)·dist x x'` is not realizable in the tempered class. The witness pair is the
certificate: a pointwise, checkable obstruction; the realizable image itself is not characterized. -/
theorem not_mem_temperedClass_of_dist_gt {k : ℕ} [NeZero k] {X : Type*} [PseudoMetricSpace X]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {β Ks Kv P : ℝ} {f : X → V} {x x' : X}
    (hwit : (2 * β * Ks * P + Kv) * dist x x' < dist (f x) (f x')) :
    f ∉ TemperedClass (k := k) β Ks Kv P := by
  intro hf
  exact absurd (temperedClass_dist_le hf x x') (not_le.mpr hwit)

end TLT.TemperedDesignLaw
