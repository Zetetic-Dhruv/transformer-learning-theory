/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import NN.Floats.IEEEExec.BridgeFP32Total
import NN.Floats.IEEEExec.BridgeFP32

/-!
# Literal executed activations — the stack-side rounding atoms

The single-head attention literal binding rests on one bit-level transcendental atom (`exp`, discharged
on the softmax cone). Extending the literal binding to the full transformer *stack* adds two activation
atoms:

* the FFN's **ReLU**, which is rounding-free — `maximum x 0` read over ℝ is *exactly* `max (toReal x) 0`;
* layer-normalization's **sqrt**, whose bit-level accuracy is already shipped in TorchLean
  (`toReal_sqrt_eq_fp32Round_of_isFinite`, `toReal_sqrt_abs_error_of_isFinite`).

This file states the ReLU atom and re-exports the sqrt accuracy in the `fp32Round` shape the stack-side
forward error consumes, so the depth composition reads its per-layer rounding off shipped facts.
-/

namespace TLT.Fp32Stack

open TorchLean.Floats TorchLean.Floats.IEEE754 TorchLean.Floats.IEEE754.IEEE32Exec

/-- **reluExec_exact — the literal ReLU introduces no rounding.** The bit-level `maximum x 0` read over ℝ
is *exactly* `max (toReal x) 0 = relu (toReal x)`: a select copies one of its inputs, so there is no
rounding. The FFN activation contributes `rnd = 0` to the depth envelope. -/
theorem reluExec_exact (x : IEEE32Exec) (hx : isFinite x = true) :
    toReal (maximum x posZero) = max (toReal x) 0 := by
  rw [toReal_maximum_eq_max_of_isFinite x posZero hx (by decide), toReal_posZero]

/-- The literal `maximum x 0` is finite when `x` is — needed so the ReLU layer composes (its output feeds
the next executed layer). -/
theorem isFinite_reluExec (x : IEEE32Exec) (hx : isFinite x = true) :
    isFinite (maximum x posZero) = true :=
  isFinite_maximum_of_isFinite x posZero hx (by decide)

/-- **The layerNorm `sqrt` atom, in `fp32Round` shape.** The bit-level `IEEE32Exec.sqrt` of a finite input
reads back as the rounded real square root — the only rounding the executed standard deviation incurs.
A thin re-export of the shipped `toReal_sqrt_eq_fp32Round_of_isFinite` for the stack-side consumer. -/
theorem sqrtExec_eq_fp32Round (x : IEEE32Exec) (hfin : isFinite (sqrt x) = true) :
    toReal (sqrt x) = fp32Round (Real.sqrt (toReal x)) :=
  toReal_sqrt_eq_fp32Round_of_isFinite x hfin

end TLT.Fp32Stack
