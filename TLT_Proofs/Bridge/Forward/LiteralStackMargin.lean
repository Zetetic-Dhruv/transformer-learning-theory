/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Forward.ExecLayerInstances
import TLT_Proofs.Bridge.Forward.NonExpansiveDepthEnvelope
import TLT_Proofs.Bridge.Fp32.StackActivationExecutedValue

/-!
# The literal executed-stack margin

The single-head attention literal binding (`attnLiteralForwardError`) bounds one bit-level block. A
depth-`L` stack composes such blocks; the generic composition `execComp_envelope` and its non-expansive
linear-in-depth refinement `execComp_envelope_linear` give the depth margin for a list of `ExecLayer`s.
The results below supply the **literal connection** for the FFN activation:

* `reluExecLayer_exec_eq_lit`: the `reluExecLayer` faithfully models the bit-level IEEE ReLU.
  On a finite fp32 input its executed map (read over ℝ) equals `toReal ∘ (maximum · 0)` coordinatewise,
  so the model layer is the literal kernel with `rnd = 0`.
* `envBound_relu_cons`: a ReLU layer is **free** in the depth envelope. Prepending it leaves `envBound`
  unchanged (`rnd = 0`). Only the rounding layers (linear / attention / layerNorm) accumulate.
* `ffnBlockStack_margin`: a literal `[linear, ReLU] × L` FFN stack is within `L·ρ` of the ideal. The `L`
  ReLU layers are free; only the `L` linear layers round.
-/

namespace TLT

open TorchLean.Floats.IEEE754 TorchLean.Floats.IEEE754.IEEE32Exec TLT.Fp32Stack

/-- **The `reluExecLayer` is the literal IEEE ReLU.** On a finite fp32 input vector `v`, the
`reluExecLayer`'s executed map, applied to `v` read over ℝ, equals the bit-level `maximum v 0` read
over ℝ, coordinatewise. The FFN activation therefore enters the depth envelope as the literal kernel
with `rnd = 0`, via `reluExec_exact`. -/
theorem reluExecLayer_exec_eq_lit {n : ℕ} (v : Fin n → IEEE32Exec)
    (hv : ∀ i, isFinite (v i) = true) :
    reluExecLayer.exec (fun i => toReal (v i)) = fun i => toReal (maximum (v i) posZero) := by
  funext i
  simp only [reluExecLayer]
  exact (reluExec_exact (v i) (hv i)).symm

/-- **A ReLU layer is free in the depth envelope.** Prepending the rounding-free `reluExecLayer` to a
stack leaves `envBound` unchanged: `rnd = 0` contributes nothing regardless of the downstream Lipschitz
product. The FFN activation incurs no cost in the executed forward error. -/
theorem envBound_relu_cons {n : ℕ} (Ls : List (ExecLayer (Fin n → ℝ))) :
    envBound (reluExecLayer :: Ls) = envBound Ls := by
  simp only [envBound, reluExecLayer, zero_mul, zero_add]

/-- **The executed-stack margin.** A non-expansive executed stack (every layer 1-Lipschitz, each
rounding within `ρ`) is within `(#layers)·ρ` of the ideal forward map: linear in depth with no
exponential blow-up. The depth-side analogue of the single-block `rndLit`. -/
theorem executedStackMargin {V : Type*} [PseudoMetricSpace V] [Nonempty V]
    {Ls : List (ExecLayer V)} {ρ : ℝ} (hlip : ∀ L ∈ Ls, L.lip ≤ 1) (hrnd : ∀ L ∈ Ls, L.rnd ≤ ρ)
    (x : V) :
    dist (execComp Ls x) (idealComp Ls x) ≤ Ls.length * ρ :=
  execComp_envelope_linear hlip hrnd x

/-- **A literal FFN block rounds only at its linear layer.** The envelope of a `[linear, ReLU]` block is
exactly the linear layer's rounding `lin.rnd`; the bit-level ReLU contributes nothing. A depth-`L`
FFN tower's forward error is carried entirely by its `L` linear maps; the activations are free. -/
theorem ffnBlock_envBound {n : ℕ} (lin : ExecLayer (Fin n → ℝ)) :
    envBound [lin, reluExecLayer] = lin.rnd := by
  simp only [envBound, lipProd, reluExecLayer, mul_one, zero_mul, add_zero, zero_add]

end TLT
