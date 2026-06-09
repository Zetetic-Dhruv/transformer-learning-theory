/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Spec.ScaledDotProductAttentionCorrespondence

/-!
# The certified generalization bound for the executed attention head

The final assembly. The certified bound `attnHead_certified_generalization` is instantiated against the
**executed** (IEEE binary32) attention operation by wrapping it as a single `ExecLayer`:

* its `ideal` is the clamped coordinate attention `x ↦ attnHead scale W (clampCoord B x)` over ℝ —
  which is exactly TorchLean's literal `Spec.scaledDotProductAttention` in coordinates
  (`matCoords_scaledDotProductAttention`), made globally Lipschitz by the clamp;
* its `exec` is the executed IEEE32 attention map read over ℝ;
* its `rnd` is the per-layer rounding bound, and `exec_close` the float32 envelope for the operation —
  supplied by the rounding machinery (`fp32Sum_error_le`, the per-op `SpecExecLayer`s), exactly the
  executed-model interface the capstone consumes.

With this single-layer list `Ls = [L]`, `idealComp Ls` is the ideal attention by construction (so
`hagree` is `rfl`), `execComp Ls` is the executed attention, and `envBound Ls` is the rounding bound
`rnd`. The capstone then yields the closed certified bound **about the executed operation**:

`R_true^exec ≤ R̂_emp^exec + 2·(12√2·B_int/√m) + ε + 2·Lℓ·rnd`.

## Main results

- `attnHead_executed_certified_generalization` — the certified computable float32 generalization bound
  for the executed attention head.
-/

/-!
## References
- [31] clamp-induced Lipschitzness / boundary; [53] literal `scaledDotProductAttention` + IEEE32
  execution; [16][54][26] Dudley/covering; [32] attention capacity.
- Provenance: Innovation (executed instantiation) — generalization bound about the literal
  finite-precision attention kernel the hardware runs.
-/

open MeasureTheory

noncomputable section

namespace TLT

open Capacity

/-- **The certified computable float32 generalization bound for the executed attention head.** For the
executed (IEEE binary32) attention map `execAttn`, presented through the rounding envelope
`hexec_close` (the executed op is within `rnd` of the ideal real attention) with an integrable executed
loss, and with the ideal attention's on-domain Lipschitz estimate `hideal_lip`: except on a sample
event of McDiarmid-small probability, the executed true risk is at most the executed empirical risk
plus the closed capacity budget `2·(12√2·(1/√m)·B_int) + ε` and the rounding correction `2·Lℓ·rnd`.
The ideal map `x ↦ attnHead scale W (clampCoord B x)` is TorchLean's literal `scaledDotProductAttention`
read in coordinates (`matCoords_scaledDotProductAttention`); the bound is therefore about the model the
hardware actually runs. -/
theorem attnHead_executed_certified_generalization {n d p m : ℕ} [NeZero n] [Nonempty (Fin p)]
    [MeasurableSpace (Fin n → Fin d → ℝ)] [BorelSpace (Fin n → Fin d → ℝ)]
    {P : Measure (Fin n → Fin d → ℝ)} [IsProbabilityMeasure P]
    (hm : 0 < m) {R B scale : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (Wdec : ParamSpace p → (Fin d → Fin d → ℝ)) (hWcont : Continuous Wdec)
    {Lw : ℝ} (hWLip : ∀ θ θ', dist (Wdec θ) (Wdec θ') ≤ Lw * dist θ θ')
    (ℓ : (Fin n → Fin d → ℝ) → ℝ) {b : ℝ} (hb : 0 < b) (hℓb : ∀ v, |ℓ v| ≤ b)
    (hℓcont : Continuous ℓ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ)
    (hℓLip : ∀ u v, |ℓ u - ℓ v| ≤ Lℓ * dist u v)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R)
    (execAttn : (Fin n → Fin d → ℝ) → (Fin n → Fin d → ℝ))
    {lip rnd : ℝ} (hlip0 : 0 ≤ lip)
    (hideal_lip : ∀ a b : Fin n → Fin d → ℝ,
        dist (attnHead scale (Wdec (embedBase Capacity.Dyadic w_T.1)) (clampCoord B a))
             (attnHead scale (Wdec (embedBase Capacity.Dyadic w_T.1)) (clampCoord B b)) ≤ lip * dist a b)
    (hexec_close : ∀ y : Fin n → Fin d → ℝ, dist (execAttn y)
        (attnHead scale (Wdec (embedBase Capacity.Dyadic w_T.1)) (clampCoord B y)) ≤ rnd)
    (hintG : Integrable (fun x => ℓ (execAttn x)) P)
    (hLpos : 0 < Lℓ * ((d : ℝ) * B) * Lw) :
    (Measure.pi fun _ : Fin m => P).real
        {S | ¬ ((∫ x, ℓ (execAttn x) ∂P)
              ≤ (1 / (m : ℝ)) * ∑ i, ℓ (execAttn (S i))
                + (2 * ((12 * Real.sqrt 2) * (1 / Real.sqrt m)
                    * (∫⁻ ε in Set.Ioc (0 : ℝ) (2 * b),
                        ENNReal.ofReal (Real.sqrt (Real.log 2)
                          + Real.sqrt ((p : ℝ) * (4 * R * (Lℓ * ((d : ℝ) * B) * Lw)))
                            * ε ^ (-(1 / 2) : ℝ))).toReal) + ε)
                + 2 * (Lℓ * rnd))}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) := by
  have hbound := attnHead_certified_generalization hm hR hB Wdec hWcont hWLip ℓ hb hℓb hℓcont hLℓ0
    hℓLip hε w_T (clampCoord B) (continuous_clampCoord B).measurable (clampCoord_row_l1_le hB)
    [({ ideal := fun x => attnHead scale (Wdec (embedBase Capacity.Dyadic w_T.1)) (clampCoord B x)
        exec := execAttn
        lip := lip
        rnd := rnd
        lip_nonneg := hlip0
        ideal_lip := hideal_lip
        exec_close := hexec_close } : ExecLayer (Fin n → Fin d → ℝ))]
    (fun _ => rfl) hintG hLpos
  simpa only [execComp, idealComp, envBound, lipProd, mul_one, add_zero] using hbound

end TLT
