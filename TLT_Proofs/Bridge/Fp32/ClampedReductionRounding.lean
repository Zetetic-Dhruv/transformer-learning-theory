/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Fp32.SequentialSummationBackwardError

/-!
# Derived fp32 rounding for clamped reductions

The recursive rounding budget of the fp32 left fold (`fp32FoldlErrorBudget`, bounded in closed form by
`fp32FoldlErrorBudget_closed_form`) is here specialized to the **clamped operating domain**. When the
summands have bounded total magnitude (`∑ᵢ|xᵢ| ≤ S`, the situation forced by the activation clamp
`‖X‖ ≤ B`), the fp32 reduction differs from the exact sum by at most a concrete constant

`|fp32Foldl 0 xs − ∑ xs| ≤ u·(n+1)·S / (1 − n·u)`,  `u = 2⁻²⁴`, `n = length`.

This is the per-operation rounding atom, derived from the round-to-nearest model (via
`fp32Foldl_error_le` and the backward-error closed form), to which every sum-structured block
operation reduces: the matrix-multiply dot products, the attention scores, the value mix `∑ softmax·V`,
and the layer-norm mean and variance reductions. It is the `rnd` evidence the executed-forward layers
carry.

## Scope (the supplied-atom frontier)

This derives the rounding of the **reduction / fold** class. The block's remaining elementary
operations are *not* reductions: `exp` (softmax), `sqrt` (layer-norm standard deviation), and the
reciprocal/division (softmax denominator, layer-norm normalization). The framework carries their
*ideal* spec maps (`Spec.Layers.Activation.expSpec`, `sqrtSpec`, `divSpec`, over `ℝ`) but no
first-principles fp32 error model, so their per-operation rounding is supplied by the IEEE-754 standard
model (correctly-rounded `sqrt` and `÷`; `exp` within a small multiple of `u`). The full block rounding
`ρ_block` is the forward-envelope composition (`Bridge/ForwardEnvelope`) of the derived fold atoms here
and those supplied transcendental atoms; `ρ_block` then feeds `nonexpansiveExecLayer`
(`Bridge/NonExpansiveDepthEnvelope`) for the derived, machine-`ε`×depth executed bound.

## Main results

- `fp32Foldl_error_le_of_sum_bound`: the closed-form rounding bound for an fp32 reduction whose
  summands have total magnitude `≤ S`.
-/

/-!
## References
- [43] §4 summation backward error specialized to the clamped domain (acc=0, total magnitude ≤ S).
-/

open TorchLean.Floats (neuralBpow binaryRadix)

/-- **Rounding bound for a magnitude-bounded fp32 reduction.** On the clamped operating domain, where
the summands' total magnitude is bounded (`∑ᵢ|xᵢ| ≤ S`) and the reduction length keeps `n·u < 1`, the
fp32 left fold differs from the exact sum by at most `u·(n+1)·S / (1 − n·u)` (`u = 2⁻²⁴`, `n` the
length). The bound follows from the round-to-nearest model via `fp32Foldl_error_le` and the
backward-error closed form `fp32FoldlErrorBudget_closed_form`. -/
theorem fp32Foldl_error_le_of_sum_bound (xs : List ℝ) (S : ℝ)
    (hnorm : Fp32FoldlNormal 0 xs)
    (hun : neuralBpow binaryRadix (-24) * (xs.length : ℝ) < 1)
    (hS : (xs.map (fun x => |x|)).sum ≤ S) :
    |fp32Foldl 0 xs - xs.sum|
      ≤ neuralBpow binaryRadix (-24) * (((xs.length : ℝ) + 1) * S)
        / (1 - neuralBpow binaryRadix (-24) * (xs.length : ℝ)) := by
  have hu0 : 0 ≤ neuralBpow binaryRadix (-24) := neuralBpow.nonneg binaryRadix (-24)
  have hpos : 0 < 1 - neuralBpow binaryRadix (-24) * (xs.length : ℝ) := by linarith
  have hnum : neuralBpow binaryRadix (-24)
        * ((xs.length : ℝ) * |(0:ℝ)| + ((xs.length : ℝ) + 1) * (xs.map (fun x => |x|)).sum)
      ≤ neuralBpow binaryRadix (-24) * (((xs.length : ℝ) + 1) * S) := by
    rw [abs_zero, mul_zero, zero_add]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS (by positivity)) hu0
  calc |fp32Foldl 0 xs - xs.sum|
      ≤ fp32FoldlErrorBudget 0 xs := by
        simpa only [zero_add] using fp32Foldl_error_le 0 xs hnorm
    _ ≤ neuralBpow binaryRadix (-24)
          * ((xs.length : ℝ) * |(0:ℝ)| + ((xs.length : ℝ) + 1) * (xs.map (fun x => |x|)).sum)
        / (1 - neuralBpow binaryRadix (-24) * (xs.length : ℝ)) :=
        fp32FoldlErrorBudget_closed_form 0 xs hnorm hun
    _ ≤ neuralBpow binaryRadix (-24) * (((xs.length : ℝ) + 1) * S)
        / (1 - neuralBpow binaryRadix (-24) * (xs.length : ℝ)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hpos.le)
