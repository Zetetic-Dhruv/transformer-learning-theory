/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Learner.Closure
import TLT_Proofs.Routing.MeasurableScoreRouting

/-!
# Attention-Based Learners

Parametric learner families whose hypothesis selection is jointly measurable, and their
specialization to `k`-head attention routing. Binary attention learning is the `k = 2` case.

## Main results

- `ParametricLearnerFamily` : a learner parameterized by a measurable space
- `ParametricLearnerFamily.instMeasurableBatchLearner` : the induced learner is measurable
- `ParametricFiniteHeadAttentionLearner` : `k`-head attention-routed parametric learner
- `ParametricFiniteHeadAttentionLearner.instMBL'` : measurability of the attention learner

## References

- Learner/Core.lean (BatchLearner, MeasurableBatchLearner)
- Learner/Closure.lean (combineLearner, concatLearner)
- Attention/Routing.lean (FiniteScoreRouterCode, multiPatchEval, route_measurable)
-/

universe u

open Classical
open MeasureTheory Set

/-! ## ParametricLearnerFamily -/

/-- A parametric learner family: a measurable parameter space with a jointly
    measurable evaluation map and a measurable parameter selection rule. -/
structure ParametricLearnerFamily (X : Type u) [MeasurableSpace X] where
  Params : Type u
  instMeasParams : MeasurableSpace Params
  eval : Params → Concept X Bool
  eval_meas : @Measurable (Params × X) Bool (instMeasParams.prod ‹MeasurableSpace X›)
    inferInstance (fun p => eval p.1 p.2)
  param_of_sample : {m : ℕ} → (Fin m → X × Bool) → Params
  param_meas : ∀ m, @Measurable (Fin m → X × Bool) Params inferInstance instMeasParams
    (fun S => @param_of_sample m S)

attribute [instance] ParametricLearnerFamily.instMeasParams

/-! ## toBatchLearner + MeasurableBatchLearner -/

/-- Convert a ParametricLearnerFamily to a BatchLearner. -/
noncomputable def ParametricLearnerFamily.toBatchLearner
    {X : Type u} [MeasurableSpace X]
    (P : ParametricLearnerFamily X) : BatchLearner X Bool where
  hypotheses := Set.range P.eval
  learn := fun {m} S => P.eval (@P.param_of_sample m S)
  output_in_H := fun {m} S => ⟨@P.param_of_sample m S, rfl⟩

/-- The BatchLearner induced by a ParametricLearnerFamily is measurable. -/
instance ParametricLearnerFamily.instMeasurableBatchLearner
    {X : Type u} [MeasurableSpace X]
    (P : ParametricLearnerFamily X) :
    MeasurableBatchLearner X P.toBatchLearner where
  eval_measurable m := by
    letI := P.instMeasParams
    show Measurable (fun p : (Fin m → X × Bool) × X => P.eval (P.param_of_sample p.1) p.2)
    exact P.eval_meas.comp
      (Measurable.prodMk ((P.param_meas m).comp measurable_fst) measurable_snd)

/-! ## ParametricFiniteHeadAttentionLearner

The `k`-head attention-routed parametric learner. Binary attention learning is the `k = 2`
specialization (head ordering recovers the score-comparison route, `route_two_eq_scoreComparison`). -/

/-- A parametric learner that uses `k`-head attention routing to combine `k` experts.
    All parameters (router scores, expert evaluations) come from a single parameter
    space `Params`, with diagonal embedding into `(Params, Params)` for the
    `multiPatchEval` interface. -/
structure ParametricFiniteHeadAttentionLearner (X : Type u) [MeasurableSpace X] (k : ℕ) where
  Params : Type u
  instMeasParams : MeasurableSpace Params
  instStdParams : @StandardBorelSpace Params instMeasParams
  score : Params → X → Fin k → ℝ
  score_meas : ∀ (i : Fin k), @Measurable (Params × X) ℝ
    (instMeasParams.prod ‹MeasurableSpace X›) inferInstance (fun p => score p.1 p.2 i)
  expert : Params → Fin k → Concept X Bool
  expert_meas : ∀ (i : Fin k), @Measurable (Params × X) Bool
    (instMeasParams.prod ‹MeasurableSpace X›) inferInstance (fun p => expert p.1 i p.2)
  param_of_sample : {m : ℕ} → (Fin m → X × Bool) → Params
  param_meas : ∀ m, @Measurable (Fin m → X × Bool) Params inferInstance instMeasParams
    (fun S => @param_of_sample m S)

attribute [instance] ParametricFiniteHeadAttentionLearner.instMeasParams
attribute [instance] ParametricFiniteHeadAttentionLearner.instStdParams

/-- Extract the FiniteScoreRouterCode from a ParametricFiniteHeadAttentionLearner. -/
noncomputable def ParametricFiniteHeadAttentionLearner.routerCode
    {X : Type u} [MeasurableSpace X] {k : ℕ}
    (T : ParametricFiniteHeadAttentionLearner X k) : FiniteScoreRouterCode X k where
  Ρ := T.Params
  instMeasΡ := T.instMeasParams
  instStdΡ := T.instStdParams
  score := T.score
  score_meas := T.score_meas

/-! ## Conversion to ParametricLearnerFamily + MeasurableBatchLearner -/

/-- Convert a ParametricFiniteHeadAttentionLearner to a ParametricLearnerFamily.
    Uses diagonal embedding `θ ↦ (θ, θ)` for `multiPatchEval(expert, route)(θ, θ)`. -/
noncomputable def ParametricFiniteHeadAttentionLearner.toParametricLearnerFamily
    {X : Type u} [MeasurableSpace X] {k : ℕ}
    (T : ParametricFiniteHeadAttentionLearner X k) (hk : 0 < k) :
    ParametricLearnerFamily X where
  Params := T.Params
  instMeasParams := T.instMeasParams
  eval := fun θ x => multiPatchEval T.expert (T.routerCode.route hk) (θ, θ) x
  eval_meas := by
    letI := T.instMeasParams
    have hmulti := multiPatchEval_measurable T.expert (T.routerCode.route hk)
      T.expert_meas (T.routerCode.route_measurable hk)
    have hdiag : Measurable (fun p : T.Params × X => ((p.1, p.1), p.2) :
        T.Params × X → (T.Params × T.Params) × X) :=
      (measurable_fst.prodMk measurable_fst).prodMk measurable_snd
    exact hmulti.comp hdiag
  param_of_sample := T.param_of_sample
  param_meas := T.param_meas

/-- The finite-head attention-based learner satisfies MeasurableBatchLearner. (Binary
    attention learning is this at `k = 2`.) -/
instance ParametricFiniteHeadAttentionLearner.instMBL'
    {X : Type u} [MeasurableSpace X] {k : ℕ}
    (T : ParametricFiniteHeadAttentionLearner X k) (hk : 0 < k) :
    MeasurableBatchLearner X (T.toParametricLearnerFamily hk).toBatchLearner :=
  ParametricLearnerFamily.instMeasurableBatchLearner (T.toParametricLearnerFamily hk)
