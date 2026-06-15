/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Forward.ForwardContinuity
import TLT_Proofs.Bridge.Forward.TransformerForwardRegularity
import TLT_Proofs.Bridge.Fp32.RelativeUlpAndSummation
import NN.Floats.NeuralFloat.Rounding
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The IEEE-754-executed transformer forward map: measurable, and risk-stable under its rounding envelope

Executed in IEEE-754 binary32, the transformer forward pass rounds every operation to the float grid.
Read over real coordinates, the executed map is piecewise constant on the rounding cells, hence
discontinuous, yet it is **measurable**: IEEE round-to-nearest is measurable, because it decomposes
into measurable atoms (the base-2 magnitude `⌊log₂⌋`, the canonical-exponent selection, the base-power
scaling, and round-to-nearest-even) with no appeal to continuity. The executed forward, a composition
of measurable maps, is therefore measurable.

Measurability is what makes the expected risk a well-defined integral. Consequently, given a uniform
bound `ε` between the executed and ideal forward maps (a rounding envelope) and an `L`-Lipschitz loss,
the executed expected risk lies within `L · ε` of the ideal expected risk; this transfer rests on
the measurability of both maps. The continuity of the real forward map needs the layer-normalization
regularizer, but measurability, and hence this risk bound, survives regardless.

## Main results

- `measurable_fp32Round`: IEEE-754 round-to-nearest, as a real function, is measurable.
- `fp32RoundCoord` / `measurable_fp32RoundCoord`: elementwise fp32 rounding of a coordinate matrix is
  measurable.
- `ForwardMapExecutedMeasurable` / `transformerForwardMap_executed_measurable`: the executed forward
  map (fp32-rounded embedding, a stack of measurable executed layers, fp32-rounded projection) is
  measurable.
- `transformerForwardMap_executed_measurable_resolution`: the discharged `Resolution`.
- `executed_risk_transfer`: under the rounding envelope and an `L`-Lipschitz loss, the executed and
  ideal expected risks differ by at most `L · ε`.
-/

/-!
## References
- step/piecewise-constant maps are Borel; Lipschitz-loss bounded-perturbation risk transfer; [53]
  IEEE32 execution; [55] SLT measurability scaffolding context.
-/

open MeasureTheory
open TorchLean.Floats
open TorchLean.Floats.IEEE754.IEEE32Exec

noncomputable section

namespace TLT

/-! ### Measurability of IEEE-754 round-to-nearest

`fp32Round = neuralRound binaryRadix fexp32 rnd32` is `rnd32(x · β^(-cexp x)) · β^(cexp x)`. Each piece
is measurable: the magnitude `⌊log|x|⌋`, the integer-valued canonical exponent, the base power, and the
round-to-nearest-even; none of which requires monotonicity or continuity of the rounding. -/

private lemma measurable_intCastR : Measurable (fun n : ℤ => (n : ℝ)) :=
  continuous_of_discreteTopology.measurable

/-- Round-to-nearest-even (`ℝ → ℤ`) is measurable: it is `⌊·⌋` corrected by measurable comparisons of
the fractional part and a parity test on the floor. -/
private lemma measurable_neuralNearestEven : Measurable neuralNearestEven := by
  unfold neuralNearestEven
  have hfract : Measurable (fun x : ℝ => x - (⌊x⌋ : ℝ)) :=
    measurable_id.sub (measurable_intCastR.comp Int.measurable_floor)
  have hEven : MeasurableSet {x : ℝ | Even ⌊x⌋} :=
    Int.measurable_floor ((Set.to_countable {n : ℤ | Even n}).measurableSet)
  refine Measurable.ite (measurableSet_lt hfract measurable_const) Int.measurable_floor ?_
  refine Measurable.ite (measurableSet_lt measurable_const hfract)
    (Int.measurable_floor.add_const 1) ?_
  exact Measurable.ite hEven Int.measurable_floor (Int.measurable_floor.add_const 1)

/-- The base-`β` magnitude `mag(x) = ⌊log_β|x|⌋ + 1` (and `0` at `0`) is measurable. -/
private lemma measurable_neuralMagnitude (β : NeuralRadix) : Measurable (neuralMagnitude β) := by
  unfold neuralMagnitude
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  exact (Int.measurable_floor.comp
    ((Real.measurable_log.comp continuous_abs.measurable).div measurable_const)).add_const 1

/-- The canonical exponent `cexp = fexp ∘ mag` is measurable. -/
private lemma measurable_neuralCexp (β : NeuralRadix) (fexp : ℤ → ℤ) [NeuralValidExp fexp] :
    Measurable (neuralCexp β fexp) :=
  continuous_of_discreteTopology.measurable.comp (measurable_neuralMagnitude β)

/-- The scaled mantissa `x · β^(-cexp x)` is measurable. -/
private lemma measurable_neuralScaledMantissa (β : NeuralRadix) (fexp : ℤ → ℤ) [NeuralValidExp fexp] :
    Measurable (neuralScaledMantissa β fexp) := by
  unfold neuralScaledMantissa neuralBpow
  exact measurable_id.mul
    (continuous_of_discreteTopology.measurable.comp (measurable_neuralCexp β fexp).neg)

/-- **IEEE-754 round-to-nearest is measurable.** `fp32Round` is a totally discontinuous step function
on the float grid, but it decomposes into measurable atoms (magnitude, exponent, base power,
round-to-nearest-even), so it is Borel measurable; no continuity is required. -/
theorem measurable_fp32Round : Measurable fp32Round := by
  unfold fp32Round neuralRound neuralToReal
  refine Measurable.mul ?_ ?_
  · exact measurable_intCastR.comp
      (measurable_neuralNearestEven.comp (measurable_neuralScaledMantissa binaryRadix fexp32))
  · unfold neuralBpow
    exact continuous_of_discreteTopology.measurable.comp (measurable_neuralCexp binaryRadix fexp32)

/-! ### The executed forward map is measurable -/

/-- Elementwise fp32 rounding of a coordinate matrix. -/
def fp32RoundCoord {s d : ℕ} (X : Fin s → Fin d → ℝ) : Fin s → Fin d → ℝ :=
  fun i j => fp32Round (X i j)

/-- Elementwise fp32 rounding is measurable. -/
theorem measurable_fp32RoundCoord {s d : ℕ} : Measurable (fp32RoundCoord (s := s) (d := d)) := by
  refine measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (fun j => ?_))
  exact measurable_fp32Round.comp ((measurable_pi_apply j).comp (measurable_pi_apply i))

/-- The IEEE-754-executed forward map is measurable: an fp32-rounded input embedding, a stack of
measurable executed layers, and an fp32-rounded output projection compose to a measurable map of the
input coordinates. -/
def ForwardMapExecutedMeasurable (T : RealTransformer) : Prop :=
  ∀ {seqLen : ℕ} (Wembed Wout : Fin T.cfg.embedDim → Fin T.cfg.embedDim → ℝ)
    (layers : List ((Fin seqLen → Fin T.cfg.embedDim → ℝ) → Fin seqLen → Fin T.cfg.embedDim → ℝ)),
    (∀ L ∈ layers, Measurable L) →
    Measurable (fun X : Fin seqLen → Fin T.cfg.embedDim → ℝ =>
      fp32RoundCoord (matMulCoord Wout
        (layers.foldl (fun acc L => L acc) (fp32RoundCoord (matMulCoord Wembed X)))))

/-- Every real transformer's executed forward map is measurable (a composition of the measurable
elementwise rounding, the measurable embedding and projection, and the measurable-layer stack). -/
theorem transformerForwardMap_executed_measurable (T : RealTransformer) :
    ForwardMapExecutedMeasurable T := by
  intro seqLen Wembed Wout layers hL
  exact measurable_fp32RoundCoord.comp ((measurable_matMulCoord Wout).comp
    ((measurable_listFoldl layers hL).comp
      (measurable_fp32RoundCoord.comp (measurable_matMulCoord Wembed))))

/-- The discharged resolution recording that the executed forward map of `T` is measurable. -/
def transformerForwardMap_executed_measurable_resolution (T : RealTransformer) :
    Resolution T ForwardMapExecutedMeasurable :=
  Resolution.discharged (transformerForwardMap_executed_measurable T)

/-! ### Risk transfer under the rounding envelope -/

/-- **Executed-model risk transfer.** If the executed predictor `G` is uniformly within `ε` of the
ideal predictor `F` (the rounding envelope) and the loss `ℓ` is `L`-Lipschitz, then the executed
expected risk differs from the ideal expected risk by at most `L · ε`. Both risks are well-defined
integrals precisely because `F` and `G` are measurable (the hypothesis supplied for the executed
forward by `transformerForwardMap_executed_measurable`). -/
theorem executed_risk_transfer {Ω P : Type*} [MeasurableSpace Ω] [PseudoMetricSpace P]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F G : Ω → P} (ℓ : P → ℝ) {L ε : ℝ} (hL0 : 0 ≤ L)
    (hLip : ∀ p q, |ℓ p - ℓ q| ≤ L * dist p q) (henv : ∀ x, dist (G x) (F x) ≤ ε)
    (hintF : Integrable (fun x => ℓ (F x)) μ) (hintG : Integrable (fun x => ℓ (G x)) μ) :
    |(∫ x, ℓ (G x) ∂μ) - (∫ x, ℓ (F x) ∂μ)| ≤ L * ε := by
  have hpt : ∀ x, |ℓ (G x) - ℓ (F x)| ≤ L * ε := fun x =>
    (hLip (G x) (F x)).trans (mul_le_mul_of_nonneg_left (henv x) hL0)
  rw [← integral_sub hintG hintF]
  calc |∫ x, (ℓ (G x) - ℓ (F x)) ∂μ|
      ≤ ∫ x, |ℓ (G x) - ℓ (F x)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _x, L * ε ∂μ := integral_mono (hintG.sub hintF).abs (integrable_const _) hpt
    _ = L * ε := by rw [integral_const]; simp

end TLT
