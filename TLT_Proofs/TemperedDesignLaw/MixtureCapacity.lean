/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MixtureParamLayer

/-!
# The depth-linear capacity constant (the soft-capacity depth scaling)

The shipped depth telescope `paramComp_param_lipschitz` bounds a stack's parameter-Lipschitz by
`paramLipBound`, the accumulated envelope `∑ₖ paramLipₖ · ∏_{j>k} lipⱼ`. For a *homogeneous non-expansive*
stack — every layer the same, input-Lipschitz `≤ 1` — that envelope is at most depth times the per-layer
parameter modulus:

* `inputLipProd_replicate_le_one` — the downstream input-Lipschitz product of a non-expansive replicated
  stack is `≤ 1`.
* `paramLipBound_replicate_le` — `paramLipBound (replicate n L) ≤ n · L.paramLip`: the capacity constant
  grows at most linearly in depth.

For a stack of `temperedParamLayer`s (per-layer parameter modulus `2·β·Ksθ·P + Kvθ`, input modulus
`2·β·Ksy·P + Kvy`), this reads: when `2·β·Ksy·P + Kvy ≤ 1` the depth-`n` capacity constant is at most
`n · (2·β·Ksθ·P + Kvθ)` — linear in depth *and* in the sharpness `β`. Composed with the shipped
`capacityReal_le_dudley_of_lipschitz`, this is the sharpness-scaled empirical Rademacher complexity bound;
the constant is `O(n·β)`, the precise rate at which soft capacity grows with depth and sharpness.

The shipped certificates carry `paramLipBound (replicate L blk)` symbolically; these lemmas extract its
explicit depth-linearity.
-/

open scoped BigOperators

noncomputable section

namespace TLT.TemperedDesignLaw

/-- The downstream input-Lipschitz product of a non-expansive replicated stack is at most one:
`inputLipProd (replicate n L) ≤ 1` whenever `L.lip ≤ 1`. -/
lemma inputLipProd_replicate_le_one {Θ V : Type*} [PseudoMetricSpace Θ] [PseudoMetricSpace V]
    (L : ParamLayer Θ V) (h : L.lip ≤ 1) (n : ℕ) : inputLipProd (List.replicate n L) ≤ 1 := by
  induction n with
  | zero => simp [inputLipProd]
  | succ n ih =>
      rw [List.replicate_succ, inputLipProd]
      calc L.lip * inputLipProd (List.replicate n L)
          ≤ L.lip * 1 := mul_le_mul_of_nonneg_left ih L.lip_nonneg
        _ = L.lip := mul_one _
        _ ≤ 1 := h

/-- **The depth-linear capacity constant.** For a homogeneous non-expansive stack the accumulated
parameter-Lipschitz envelope grows at most linearly in depth: `paramLipBound (replicate n L) ≤ n · L.paramLip`
whenever `L.lip ≤ 1`. For a `temperedParamLayer` this gives the `n · (2·β·Ksθ·P + Kvθ)` depth×sharpness
scaling of the soft-capacity constant. -/
lemma paramLipBound_replicate_le {Θ V : Type*} [PseudoMetricSpace Θ] [PseudoMetricSpace V]
    (L : ParamLayer Θ V) (h : L.lip ≤ 1) (n : ℕ) :
    paramLipBound (List.replicate n L) ≤ n * L.paramLip := by
  induction n with
  | zero => simp [paramLipBound]
  | succ n ih =>
      rw [List.replicate_succ, paramLipBound]
      have h1 : L.paramLip * inputLipProd (List.replicate n L) ≤ L.paramLip := by
        have := mul_le_mul_of_nonneg_left (inputLipProd_replicate_le_one L h n) L.paramLip_nonneg
        rwa [mul_one] at this
      push_cast
      calc L.paramLip * inputLipProd (List.replicate n L) + paramLipBound (List.replicate n L)
          ≤ L.paramLip + (n : ℝ) * L.paramLip := add_le_add h1 ih
        _ = ((n : ℝ) + 1) * L.paramLip := by ring

end TLT.TemperedDesignLaw
