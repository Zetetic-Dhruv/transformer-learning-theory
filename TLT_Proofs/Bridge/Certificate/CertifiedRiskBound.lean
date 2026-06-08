/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Forward.ForwardEnvelope

/-!
# Certified risk bound for the executed forward pass: the float-transfer assembly

A generalization bound proved for the ideal (real-arithmetic) forward pass is transferred to the
**executed** (IEEE binary32) forward pass by the rounding envelope. If, for an `L`-Lipschitz loss `ℓ`,
the ideal true risk is within a `capacity` term of the ideal empirical risk, then the **executed**
true risk is within `capacity + 2·L·envBound` of the **executed** empirical risk — every additional
term computable from the layer data (`envBound`, the Lipschitz constant `L`).

The two float-transfer legs are `execComp_risk_transfer` (true risk, an integral) and
`empRisk_transfer` (empirical risk, a finite average), each bounding the executed–ideal gap by
`L·envBound`. The real-side hypothesis `hCapacity` is exactly the statistical generalization bound for
the ideal forward map; it is supplied separately by the metric-entropy / chaining capacity analysis.

## Main results

- `empRisk_transfer` — the executed and ideal empirical risks differ by at most `L·envBound`.
- `certifiedRiskBound_of_idealRisk` — the executed true risk is bounded by the executed empirical risk
  plus the capacity plus `2·L·envBound`, given the ideal-side generalization bound.
-/

/-!
## References
- [22] Lipschitz-loss contraction / risk transfer; [36][54] ideal-side capacity term; [53] executed
  forward; [56] verified-ML context.
- Provenance: Innovation — the float-transfer assembly carrying an ideal generalization bound to the
  executed IEEE-binary32 forward via `2·L·envBound`. Capacity legs matched/vendored; transfer is TLT.
-/

open MeasureTheory

namespace TLT

variable {V : Type*} [PseudoMetricSpace V]

/-- **Empirical-risk float transfer.** For an `L`-Lipschitz loss `ℓ`, the executed and ideal empirical
risks over a sample of size `n > 0` differ by at most `L · envBound Ls`: each per-sample loss gap is
`≤ L · dist (execComp …) (idealComp …) ≤ L · envBound Ls`, and the average preserves the bound. -/
theorem empRisk_transfer (Ls : List (ExecLayer V)) {n : ℕ} (hn : 0 < n) (xs : Fin n → V)
    (ℓ : V → ℝ) {L : ℝ} (hL0 : 0 ≤ L) (hLip : ∀ p q, |ℓ p - ℓ q| ≤ L * dist p q) :
    |(1 / (n : ℝ)) * ∑ i, ℓ (execComp Ls (xs i)) - (1 / (n : ℝ)) * ∑ i, ℓ (idealComp Ls (xs i))|
      ≤ L * envBound Ls := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm : ∀ i, |ℓ (execComp Ls (xs i)) - ℓ (idealComp Ls (xs i))| ≤ L * envBound Ls := by
    intro i
    calc |ℓ (execComp Ls (xs i)) - ℓ (idealComp Ls (xs i))|
        ≤ L * dist (execComp Ls (xs i)) (idealComp Ls (xs i)) := hLip _ _
      _ ≤ L * envBound Ls := mul_le_mul_of_nonneg_left (execComp_envelope Ls (xs i)) hL0
  calc |(1 / (n : ℝ)) * ∑ i, ℓ (execComp Ls (xs i)) - (1 / (n : ℝ)) * ∑ i, ℓ (idealComp Ls (xs i))|
      = (1 / (n : ℝ)) * |∑ i, (ℓ (execComp Ls (xs i)) - ℓ (idealComp Ls (xs i)))| := by
        rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (1 / (n : ℝ)) * ∑ i, |ℓ (execComp Ls (xs i)) - ℓ (idealComp Ls (xs i))| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (1 / (n : ℝ)) * ∑ _i, L * envBound Ls :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hterm i)) (by positivity)
    _ = L * envBound Ls := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- **Certified executed risk bound (float-transfer assembly).** Given an `L`-Lipschitz loss and the
ideal-side generalization bound `hCapacity` (ideal true risk `≤` ideal empirical risk `+ capacity`),
the **executed** true risk is bounded by the **executed** empirical risk plus `capacity + 2·L·envBound`.

This is the spine of the executed certificate: the statistical capacity term is supplied for the ideal
forward map by the metric-entropy / chaining analysis, and the two rounding legs
(`execComp_risk_transfer`, `empRisk_transfer`) carry the bound to the executed model. -/
theorem certifiedRiskBound_of_idealRisk {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Ls : List (ExecLayer V)) (input : Ω → V)
    {n : ℕ} (hn : 0 < n) (xs : Fin n → V) (ℓ : V → ℝ) {L capacity : ℝ}
    (hL0 : 0 ≤ L) (hLip : ∀ p q, |ℓ p - ℓ q| ≤ L * dist p q)
    (hintF : Integrable (fun x => ℓ (idealComp Ls (input x))) μ)
    (hintG : Integrable (fun x => ℓ (execComp Ls (input x))) μ)
    (hCapacity : (∫ x, ℓ (idealComp Ls (input x)) ∂μ)
        ≤ (1 / (n : ℝ)) * ∑ i, ℓ (idealComp Ls (xs i)) + capacity) :
    (∫ x, ℓ (execComp Ls (input x)) ∂μ)
      ≤ (1 / (n : ℝ)) * ∑ i, ℓ (execComp Ls (xs i)) + capacity + 2 * (L * envBound Ls) := by
  have hA := abs_le.mp (execComp_risk_transfer Ls input ℓ hL0 hLip hintF hintG)
  have hE := abs_le.mp (empRisk_transfer Ls hn xs ℓ hL0 hLip)
  linarith [hA.2, hE.1, hCapacity]

end TLT
