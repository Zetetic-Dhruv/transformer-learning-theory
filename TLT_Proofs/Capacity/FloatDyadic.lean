/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Capacity.DyadicBase
import NN.Floats.NeuralFloat.Core
import NN.Floats.IEEEExec.RatScaling
import NN.Floats.IEEEExec.RealSemantics
import NN.Floats.IEEEExec.BridgeFP32Total

/-!
# Executed float32 values are dyadic rationals

Every finite IEEE-754 binary32 value is exactly a dyadic rational: its real interpretation is
`(±mantissa)·2^exponent`, an integer multiple of an integer power of two. Decoding through the
executed model's exact-dyadic semantics (`toReal_eq`) and reading off the mantissa and exponent
places that value in the image of the dyadic inclusion `dyadicToReal : Dyadic → ℝ`.

This is the inclusion that lets the dyadic-ball capacity bound dominate the executed model: the
float32 weight vector of any executed network embeds into the dyadic weight ball, so the supremum
over the dyadic ball — which equals the real ball's capacity by base-change invariance — covers it.

## Main results

- `ieee32_toReal_mem_range_dyadicToReal` — a finite float32 value lies in the range of the dyadic
  inclusion into `ℝ`.
-/

open TorchLean.Floats TorchLean.Floats.IEEE754

noncomputable section

namespace TLT.Capacity

/-- Every integer power of two is a dyadic rational. -/
lemma two_zpow_mem_dyadicSubring (e : ℤ) : (2 : ℚ) ^ e ∈ DyadicSubring := by
  have h2 : (2 : ℚ) ∈ DyadicSubring := by
    simpa using intCast_mem DyadicSubring (2 : ℤ)
  have h2inv : (2 : ℚ)⁻¹ ∈ DyadicSubring := Subring.subset_closure (Set.mem_singleton _)
  rcases e with n | n
  · show (2 : ℚ) ^ (n : ℤ) ∈ DyadicSubring
    rw [zpow_natCast]; exact pow_mem h2 n
  · rw [zpow_negSucc, ← inv_pow]; exact pow_mem h2inv (n + 1)

/-- Any integer multiple of an integer power of two lies in the range of the dyadic inclusion. -/
lemma intMul_two_zpow_mem_range (k : ℤ) (e : ℤ) :
    (k : ℝ) * (2 : ℝ) ^ e ∈ Set.range (dyadicToReal : Dyadic → ℝ) := by
  refine ⟨⟨(k : ℚ) * (2 : ℚ) ^ e, mul_mem (intCast_mem _ k) (two_zpow_mem_dyadicSubring e)⟩, ?_⟩
  have hcast : dyadicToReal ⟨(k : ℚ) * (2 : ℚ) ^ e,
      mul_mem (intCast_mem _ k) (two_zpow_mem_dyadicSubring e)⟩
      = (((k : ℚ) * (2 : ℚ) ^ e : ℚ) : ℝ) := rfl
  rw [hcast]; push_cast; ring

/-- The binary power-of-two scaling equals `2 ^ e` over the reals. -/
lemma neuralBpow_binaryRadix_eq (e : ℤ) : neuralBpow binaryRadix e = (2 : ℝ) ^ e := by
  simp [neuralBpow, binaryRadix, NeuralRadix.toReal]

/-- The executed model's exact-dyadic interpretation of a decoded value is a dyadic rational. -/
lemma torch_dyadicToReal_mem_range (d : IEEE32Exec.Dyadic) :
    IEEE32Exec.dyadicToReal d ∈ Set.range (dyadicToReal : Dyadic → ℝ) := by
  rw [IEEE32Exec.dyadicToReal, neuralBpow_binaryRadix_eq]
  split_ifs with hs
  · obtain ⟨w, hw⟩ := intMul_two_zpow_mem_range (-(d.mant : ℤ)) d.exp
    exact ⟨w, hw.trans (by push_cast; ring)⟩
  · obtain ⟨w, hw⟩ := intMul_two_zpow_mem_range (d.mant : ℤ) d.exp
    exact ⟨w, hw.trans (by push_cast; ring)⟩

/-- **Every finite executed float32 value is a dyadic rational.** Its real value lies in the image
of the dyadic inclusion `dyadicToReal : Dyadic → ℝ`. -/
theorem ieee32_toReal_mem_range_dyadicToReal (x : IEEE32Exec)
    (hx : IEEE32Exec.isFinite x = true) :
    IEEE32Exec.toReal x ∈ Set.range (dyadicToReal : Dyadic → ℝ) := by
  have hne : IEEE32Exec.toDyadic? x ≠ none := fun h => by
    rw [IEEE32Exec.isFinite_eq_false_of_toDyadic?_eq_none x h] at hx
    exact absurd hx (by simp)
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hne
  rw [IEEE32Exec.toReal_eq, hd]
  exact torch_dyadicToReal_mem_range d

end TLT.Capacity
