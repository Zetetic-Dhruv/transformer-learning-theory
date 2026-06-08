/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Certificate.MultiHeadEncoderStack
import TLT_Proofs.Bridge.Certificate.MeasurabilityPrecondition

/-!
# The architecture design law, indexed by `TransformerConfig`

The certified-generalization machinery proves a bound for a transformer presented through loose
dimension parameters (head count, embedding dimension, hidden dimension, depth). This file packages
those four numbers as a single `TransformerConfig` and states the capacity bound as a map
**out of the configuration space**: for every architecture shape `cfg`, the depth-`cfg.numLayers`,
`cfg.headCount`-head, `cfg.embedDim`-dimensional, `cfg.hiddenDim`-hidden encoder admits a certified
generalization budget (`config_capacity_law`). The four Nats flow through the parameter-perturbation
envelope (`lparamLipBound` of the depth-replicated block stack — the capacity grows with depth and
head count) into the Dudley capacity term; this is the capacity leg of the transformer design law.

`TransformerDesignLaw` then assembles the design law at a config from its legs:

* **capacity** — the config-indexed certified generalization budget (`config_capacity_law`);
* **measurability** — the executed forward is measurable, the certificate's own precondition
  (`MeasurabilityPrecondition`); and
* **expressivity** — an explicit *open* hypothesis `Expr`. The config-indexed expressivity lower
  bound is the third leg of the design law and is **not** proved here; it enters the law as a stated
  obligation, so the assembled `TransformerDesignLaw` is honest about discharging two of three legs.

## Main results

- `CertifiedGeneralization` — the config-indexed certified-generalization predicate (the executed true
  risk is within the empirical risk plus a capacity budget and rounding, off a small sample event).
- `config_capacity_law` — every `TransformerConfig` admits a certified generalization budget: the
  capacity leg as a map out of configuration space.
- `TransformerDesignLaw` — the design law at a config, assembled from capacity ⊕ measurability ⊕ the
  (open) expressivity leg.
-/

/-!
## References
- [57] FLT empirical-process / McDiarmid symmetrization; [Dudley 1967] entropy integral; the
  capacity tower (classical/vendored). [27] transformer architecture shape.
- Provenance: Innovation (organizational) — indexing the certified capacity bound by the
  backend-independent `TransformerConfig`, and assembling the design law from its legs with the
  expressivity floor as an explicit open obligation.
- TLT contribution (Dhruv Gupta), `config_capacity_law` / `TransformerDesignLaw`: the certified
  capacity bound as a map out of configuration space, and the design-law assembly that discharges the
  capacity and measurability legs while stating the expressivity leg as open. Method: package the four
  architecture Nats as `TransformerConfig` and forward the depth-graded encoder certificate; bundle the
  legs with expressivity as a hypothesis.
-/

open MeasureTheory
open TLT.Capacity

namespace TLT

/-- **The config-indexed certified-generalization predicate.** At sequence length `n` and embedding
dimension `cfg.embedDim`, with executed layer list `Ls` and loss `ℓ`: the executed true risk exceeds
the executed empirical risk by more than the capacity `budget` plus the `rounding` correction only on
a sample event of probability at most `δ`. The architecture shape `cfg` enters through `Ls` (the
executed depth-`cfg.numLayers` stack) and the budget. -/
def CertifiedGeneralization (cfg : TransformerConfig) {n : ℕ}
    [MeasurableSpace (Fin n → Fin cfg.embedDim → ℝ)]
    (P : Measure (Fin n → Fin cfg.embedDim → ℝ)) (m : ℕ)
    (Ls : List (ExecLayer (Fin n → Fin cfg.embedDim → ℝ)))
    (ℓ : (Fin n → Fin cfg.embedDim → ℝ) → ℝ) (budget rounding δ : ℝ) : Prop :=
  (Measure.pi fun _ : Fin m => P).real
      {S | ¬ ((∫ x, ℓ (execComp Ls x) ∂P)
            ≤ (1 / (m : ℝ)) * ∑ i, ℓ (execComp Ls (S i)) + budget + rounding)} ≤ δ

variable {n : ℕ}

/-- **The capacity leg of the design law, out of configuration space.** For every architecture shape
`cfg`, the tied depth-`cfg.numLayers` true-multi-head encoder stack (`cfg.headCount` heads, embedding
`cfg.embedDim`, hidden `cfg.hiddenDim`) admits a certified generalization budget: a capacity `budget`,
a `rounding` correction, and a small probability `δ` with `CertifiedGeneralization`. The budget is the
Dudley capacity of the depth-replicated block stack — it is recovered from the depth-graded encoder
certificate, so it grows through the parameter-perturbation envelope with depth and head count. -/
theorem config_capacity_law (cfg : TransformerConfig) {p m : ℕ} [NeZero n] [Nonempty (Fin p)]
    [MeasurableSpace (Fin n → Fin cfg.embedDim → ℝ)] [BorelSpace (Fin n → Fin cfg.embedDim → ℝ)]
    {P : Measure (Fin n → Fin cfg.embedDim → ℝ)} [IsProbabilityMeasure P] (hm : 0 < m)
    {R B bV βY γW scale Cγ Cβ Lγ Lβ LWQ LWK LWVO bW1 bW2 : ℝ} (hR : 0 ≤ R) (hscale : 0 < scale)
    (hd : 0 < cfg.embedDim) (hB : 0 ≤ B) (hbV0 : 0 ≤ bV) (hβY0 : 0 ≤ βY) (hγW0 : 0 ≤ γW) (hCγ0 : 0 ≤ Cγ)
    (hCβ0 : 0 ≤ Cβ) (hLγ0 : 0 ≤ Lγ) (hLβ0 : 0 ≤ Lβ) (hLWQ0 : 0 ≤ LWQ) (hLWK0 : 0 ≤ LWK)
    (hLWVO0 : 0 ≤ LWVO) (hbW1 : 0 ≤ bW1) (hbW2 : 0 ≤ bW2)
    (WQ WK WVO : ParamSpace p → (Fin cfg.headCount → Fin cfg.embedDim → Fin cfg.embedDim → ℝ))
    (W1 : Fin cfg.embedDim → Fin cfg.hiddenDim → ℝ) (b1 : Fin cfg.hiddenDim → ℝ)
    (W2 : Fin cfg.hiddenDim → Fin cfg.embedDim → ℝ) (b2 : Fin cfg.embedDim → ℝ)
    (hW1c : ∀ l, (∑ k, |W1 k l|) ≤ bW1) (hW2c : ∀ j, (∑ l, |W2 l j|) ≤ bW2)
    (γ1 β1 γ2 β2 : ParamSpace p → (Fin cfg.embedDim → ℝ))
    (hWQcont : Continuous WQ) (hWKcont : Continuous WK) (hWVOcont : Continuous WVO)
    (hγ1cont : Continuous γ1) (hβ1cont : Continuous β1) (hγ2cont : Continuous γ2) (hβ2cont : Continuous β2)
    (hγ1B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ1 θ j| ≤ Cγ)
    (hβ1B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β1 θ j| ≤ Cβ)
    (hγ2B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ2 θ j| ≤ Cγ)
    (hβ2B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β2 θ j| ≤ Cβ)
    (hβYD : ∀ y ∈ Metric.closedBall (0 : Fin n → Fin cfg.embedDim → ℝ) (Real.sqrt cfg.embedDim * Cγ + Cβ),
      ∀ i, (∑ a, |y i a|) ≤ βY)
    (hQB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin cfg.embedDim → ℝ) (Real.sqrt cfg.embedDim * Cγ + Cβ),
      ∀ h i e, |matMulCoord (WQ θ h) y i e| ≤ B)
    (hKB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin cfg.embedDim → ℝ) (Real.sqrt cfg.embedDim * Cγ + Cβ),
      ∀ h k' e, |matMulCoord (WK θ h) y k' e| ≤ B)
    (hVB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin cfg.embedDim → ℝ) (Real.sqrt cfg.embedDim * Cγ + Cβ),
      ∀ h j, ‖matMulCoord (WVO θ h) y j‖ ≤ bV)
    (hγWQ : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WQ θ h k j|) ≤ γW)
    (hγWK : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WK θ h k j|) ≤ γW)
    (hγWVO : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WVO θ h k j|) ≤ γW)
    (hγ1Lip : ∀ θ θ', dist (γ1 θ) (γ1 θ') ≤ Lγ * dist θ θ')
    (hβ1Lip : ∀ θ θ', dist (β1 θ) (β1 θ') ≤ Lβ * dist θ θ')
    (hWQLip : ∀ θ θ', dist (WQ θ) (WQ θ') ≤ LWQ * dist θ θ')
    (hWKLip : ∀ θ θ', dist (WK θ) (WK θ') ≤ LWK * dist θ θ')
    (hWVOLip : ∀ θ θ', dist (WVO θ) (WVO θ') ≤ LWVO * dist θ θ')
    (hγ2Lip : ∀ θ θ', dist (γ2 θ) (γ2 θ') ≤ Lγ * dist θ θ')
    (hβ2Lip : ∀ θ θ', dist (β2 θ) (β2 θ') ≤ Lβ * dist θ θ')
    (ℓ : (Fin n → Fin cfg.embedDim → ℝ) → ℝ) {b : ℝ} (hb : 0 < b) (hℓb : ∀ v, |ℓ v| ≤ b)
    (hℓcont : Continuous ℓ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ) (hℓLip : ∀ u v, |ℓ u - ℓ v| ≤ Lℓ * dist u v)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R)
    (Ls : List (ExecLayer (Fin n → Fin cfg.embedDim → ℝ)))
    (hagree : ∀ x, idealComp Ls x
        = lparamComp (List.flatten (List.replicate cfg.numLayers
            [normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0
                WQ WK WVO γ1 β1,
             normFFNBlock (s := n) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2]))
            (embedBase Capacity.Dyadic w_T.1) (clampCoord (Real.sqrt cfg.embedDim * Cγ + Cβ) x))
    (hintG : Integrable (fun x => ℓ (execComp Ls x)) P)
    (hLpos : 0 < Lℓ * lparamLipBound (List.flatten (List.replicate cfg.numLayers
        [normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0
            WQ WK WVO γ1 β1,
         normFFNBlock (s := n) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2]))) :
    ∃ budget rounding δ, CertifiedGeneralization cfg P m Ls ℓ budget rounding δ :=
  ⟨_, _, _, transformerEncoderStackMH_certified_generalization hm hR hscale hd hB hbV0 hβY0 hγW0 hCγ0
    hCβ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 hbW1 hbW2 WQ WK WVO W1 b1 W2 b2 hW1c hW2c γ1 β1 γ2 β2
    hWQcont hWKcont hWVOcont hγ1cont hβ1cont hγ2cont hβ2cont hγ1B hβ1B hγ2B hβ2B hβYD hQB hKB hVB
    hγWQ hγWK hγWVO hγ1Lip hβ1Lip hWQLip hWKLip hWVOLip hγ2Lip hβ2Lip ℓ hb hℓb hℓcont hLℓ0 hℓLip hε
    w_T cfg.numLayers Ls hagree hintG hLpos⟩

/-- **The transformer design law at a configuration.** Assembled from its legs at architecture shape
`cfg`: the capacity leg (a certified generalization budget, `config_capacity_law`), the measurability
leg (the executed forward is measurable — the certificate's precondition), and the expressivity leg
`Expr`, supplied as an **open** hypothesis. The capacity and measurability legs are discharged from the
library's certificates; the config-indexed expressivity lower bound is the third leg and is stated, not
proved — so this record is honest that the full design law is two-of-three legs proved with expressivity
the open obligation. -/
structure TransformerDesignLaw (cfg : TransformerConfig) (T : RealTransformer) (Expr : Prop) {p m : ℕ}
    [NeZero n] [Nonempty (Fin p)]
    [MeasurableSpace (Fin n → Fin cfg.embedDim → ℝ)] [BorelSpace (Fin n → Fin cfg.embedDim → ℝ)]
    (P : Measure (Fin n → Fin cfg.embedDim → ℝ))
    (Ls : List (ExecLayer (Fin n → Fin cfg.embedDim → ℝ)))
    (ℓ : (Fin n → Fin cfg.embedDim → ℝ) → ℝ) : Prop where
  /-- Capacity leg: a certified generalization budget for `cfg`'s architecture. -/
  capacity : ∃ budget rounding δ, CertifiedGeneralization cfg P m Ls ℓ budget rounding δ
  /-- Measurability leg: the executed forward is measurable (the certificate's precondition). -/
  measurability : ForwardMapExecutedMeasurable T
  /-- Expressivity leg: the config-indexed expressivity lower bound — OPEN, supplied as a hypothesis. -/
  expressivity : Expr

end TLT
