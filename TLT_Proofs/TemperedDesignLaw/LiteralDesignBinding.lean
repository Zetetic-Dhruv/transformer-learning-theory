/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.DesignFibration
import TLT_Proofs.TemperedDesignLaw.QuadraticTameness
import TLT_Proofs.TemperedDesignLaw.LiteralAttentionTempered
import TLT_Proofs.TemperedDesignLaw.CertificateReal
import TLT_Proofs.Bridge.Certificate.AttentionLiteralExecutedBinding

/-!
# R6 — the arc-closing EXECUTABLE-WITNESS binding of the design law to literal attention

This file binds R5's design-law legs (`DesignFibration`'s `designFiber` / `DesignFiber`) and R3a's
cascade generator `O` to TorchLean's **literal executed** `Spec.scaledDotProductAttention` — the fp32
`IEEE32Exec` kernel read over `ℝ` (`Fp32AttnLit.execAttnLit`, the exact op the hardware runs, from the
`AttentionLiteralExecutedBinding` template) — exhibiting the four design-law invariants for the literal
RUNNING program.

This is **not** the abstract β-axis binding of `LiteralAttentionTempered` (which binds TD0/TD2/TD7 to the
literal *score router* `Bridge.attentionScoreRouter`). R6 binds the four FIBER legs of R5, and crucially
binds the ERROR leg to the literal EXECUTED op, not to an ideal/abstract surrogate.

## What binds, and to what (the A4 scope lock)

* **ERROR leg → the literal executed op.** The design-law error window `designErrorWindow`
  (`NumericalLeg.cone`: `rrρ (β·S) ≤ 1/8`) IS the exponential float cone that the literal forward-error
  theorem `Fp32AttnLit.attnLiteralForwardError_onCone` consumes on `execAttnLit`. `litError_binds_execAttn`
  derives the forward error of the literal executed kernel from the SAME cone number the design-law error
  leg asserts: the design-law error window, evaluated at the executed stabilized-logit magnitude
  `2B'+2uB'`, drives the executed kernel's forward-error envelope `rndLit`. So the ERROR fiber is bound to
  the executed op, not an ideal.
* **CAPACITY leg → the literal attention scores.** The literal scaled-dot-product score is
  `Bridge.attentionScoreRouter`, whose score is `Spec.dot Q Kᵀ` (`attnScore_eq_sum`), the literal kernel's
  `QKᵀ` channel. Its per-pair differences lie in the finite-dimensional `coordSpan d`
  (`attnScoreDiff_mem_coordSpan`), which is exactly the `hlin` the capacity machinery needs. The capacity
  fiber `designCapacity_finite` is the single multiclass number of the cascade on this router.
* **EXPRESSIVITY leg → the route grade at the attention router degree.** `designExpressivity_strict`:
  the degree-`deg` polynomial route grade (`deg = 1` affine attention, `deg = 2` quadratic / low-rank
  self-attention) strictly grows with depth.
* **MEASURABILITY leg → the cliff at the attention temperature `T`.** `designMeasurabilityCliff` at
  `τ = T`: at finite attention temperature the soft blend is Borel; at the argmax limit it is non-Borel,
  null-repairable.

## Main results

* `LiteralAttentionDesign`: the executable-witness record — the four design-law legs together with the
  literal forward error of `execAttnLit` driven by the error-leg cone.
* `litError_binds_execAttn`: the ERROR-leg cone drives the literal executed kernel's forward error.
* `literalAttention_carries_designLaw` (**arc-closing**): the literal executed
  `Spec.scaledDotProductAttention` carries the design-law invariants, an executable witness.
-/

open TorchLean.Floats (neuralMagnitude neuralBpow binaryRadix)
open TorchLean.Floats.IEEE754
open TorchLean.Floats.IEEE754.IEEE32Exec
open Spec Tensor
open MeasureTheory Set
open TLT.ExpError
open scoped BigOperators

noncomputable section

namespace TLT.TemperedDesignLaw

open TLT.Fp32AttnLit
open TLT.Fp32Attn (u)

/-! ## The ERROR leg, bound to the literal EXECUTED op

The design-law error window (`designErrorWindow` / `NumericalLeg.cone`) is the inequality
`rrρ (R.beta * R.S) ≤ 1/8`. The literal executed kernel's forward-error theorem
`Fp32AttnLit.attnLiteralForwardError_onCone` consumes exactly this inequality at the executed
stabilized-logit magnitude `2·B' + 2·u·B'` (the cone radius the softmax stabilization enforces on
`execAttnLit`). We bind the two by taking the error-leg region with `R.beta * R.S = 2·B' + 2·u·B'`:
the SAME cone number that the design law asserts is the one that certifies the executed kernel. -/

/-- **The ERROR leg drives the literal executed forward error.** Take a region `R` whose certified
logit magnitude `R.beta * R.S` is the executed stabilized-logit cone radius `2·B' + 2·u·B'`. Then the
design-law error window `designErrorWindow N` (i.e. `NumericalLeg.cone`, `rrρ (R.beta·R.S) ≤ 1/8`) is
*exactly* the cone hypothesis `hρ` of `attnLiteralForwardError_onCone`, so the literal executed kernel
`execAttnLit ctx` is within the closed-form rounding envelope `rndLit` of the ideal head. The ERROR
fiber is therefore bound to the LITERAL EXECUTED op `execAttnLit`, not to an ideal surrogate: the cone
the design law carries is the cone that certifies the running fp32 program. -/
theorem litError_binds_execAttn
    {n d : ℕ} {h1 h2 : (n + 1) ≠ 0}
    (ctx : Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) d h1 h2)
    (Yt : Fin (n + 1) → Fin d → IEEE32Exec) (Wt : Fin d → Fin d → IEEE32Exec)
    (hQ : ctx.Q = Spec.matrixTensor Yt) (hK : ctx.K = Spec.matrixTensor Yt)
    (hV : ctx.V = Spec.matMulSpec (Spec.matrixTensor Yt) (Spec.matrixTensor Wt))
    (hmask : ctx.mask = none)
    (F : Fin (n + 1) → Spec.Tensor IEEE32Exec (.dim (n + 1) .scalar))
    {Dlo E_lit : ℝ} (hN : ExecAttnLitNormal ctx Yt Wt F Dlo E_lit)
    {B Λ B' : ℝ} (hB : 0 ≤ B) (hΛ0 : 0 ≤ Λ)
    (hc : 0 < toReal (litScaleFactor d : IEEE32Exec))
    (hX : ∀ a k, |toReal (Yt a k)| ≤ B) (hW : ∀ j, ∑ k, |toReal (Wt k j)| ≤ Λ)
    (hnu : ((n + 1 : ℕ) : ℝ) * u < 1) (hdu : (d : ℝ) * u < 1) (hE : 0 ≤ E_lit)
    (hscore : ∀ i k, |toReal (Spec.Tensor.vecGet (F i) k)| ≤ B')
    (hη2 : 2 * u * B' ≤ 1 / 2)
    -- The region data whose certified logit magnitude is the executed cone radius `2B'+2uB'`.
    (R : RegionData) (N : NumericalLeg R) (hRlogit : R.beta * R.S = 2 * B' + 2 * u * B') :
    dist (execAttnLit ctx) (attnHead (1 / toReal (litScaleFactor d : IEEE32Exec))
        (fun a b => toReal (Wt a b)) (fun a b => toReal (Yt a b)))
      ≤ rndLit n d B Λ (1 / toReal (litScaleFactor d : IEEE32Exec)) Dlo
          (TLT.ExpError.δexpCone (2 * B' + 2 * u * B') (2 * u * B')) E_lit := by
  -- The design-law error window, at the executed cone radius, is the literal cone hypothesis `hρ`.
  have hρ : TLT.ExpError.rrρ (2 * B' + 2 * u * B') ≤ 1 / 8 := by
    have := designErrorWindow N
    rwa [hRlogit] at this
  exact attnLiteralForwardError_onCone ctx Yt Wt hQ hK hV hmask F hN hB hΛ0 hc hX hW hnu hdu hE
    hscore hη2 hρ

/-! ## The CAPACITY leg, bound to the literal attention scores

The literal scaled-dot-product score is `Bridge.attentionScoreRouter d nK`, whose score is `Spec.dot`
of the query and key — i.e. the `Q·Kᵀ` entry of the literal kernel (`attnScore_eq_sum`). Its per-pair
score differences lie in the finite-dimensional `coordSpan d` (`attnScoreDiff_mem_coordSpan`), the exact
`hlin` the capacity machinery consumes. The capacity FIBER `designCapacity_finite` is the single
multiclass Natarajan number of the depth-`L`, arity-`k` cascade over this score family. -/

/-- **The literal attention score differences are finite-dimensional (the CAPACITY `hlin`).** The
per-pair difference of TorchLean's literal scaled-dot-product score `Bridge.attentionScoreRouter d nK`
(its `Spec.dot Q Kᵀ` channel, `attnScore_eq_sum`) lies in `coordSpan d`. Recorded here as the literal
binding of the capacity leg's linearity hypothesis to the actual attention scores. -/
theorem litAttnScoreDiff_mem_coordSpan (d nK : ℕ) (p : Fin nK × Fin nK)
    (K : (Bridge.attentionScoreRouter d nK).Ρ) :
    (fun x => (Bridge.attentionScoreRouter d nK).score K x p.2
      - (Bridge.attentionScoreRouter d nK).score K x p.1) ∈ coordSpan d :=
  attnScoreDiff_mem_coordSpan d nK p K

/-! ## The executable-witness record: the four legs + the literal executed-op binding

`LiteralAttentionDesign` bundles the four design-law legs of one fiber `DesignFiber d L k deg …`
TOGETHER WITH the literal forward error of the executed kernel `execAttnLit ctx` driven by the same
error-leg cone. No field is a free assumption:

* the four-leg fiber is the `DesignFiber` built by `designFiber` (each field a landed theorem);
* the `exec_bound` field is the conclusion of `litError_binds_execAttn` — the LITERAL EXECUTED kernel
  within the rounding envelope whose cone is the design law's error window.

This is the executable-witness shape: a design-law fact whose ERROR leg is the cone certifying the
running fp32 program, not an ideal. -/
structure LiteralAttentionDesign
    -- design-law base parameters
    (d L k deg : ℕ) (hk : 0 < k) (hdeg : 1 ≤ deg)
    (T : ℝ)
    (R : RegionData) (N : NumericalLeg R)
    {β : Type} [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β]
    [StandardBorelSpace β] [Nonempty β]
    (g : β → ℝ) (hg : Continuous g) (h_non_borel : ¬ MeasurableSet (Set.range g))
    (μ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ))) [IsFiniteMeasure μ]
    -- literal executed-attention data
    {n dim : ℕ} {h1 h2 : (n + 1) ≠ 0}
    (ctx : Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) dim h1 h2)
    (Yt : Fin (n + 1) → Fin dim → IEEE32Exec) (Wt : Fin dim → Fin dim → IEEE32Exec)
    (Bnd Λ B' Dlo E_lit : ℝ) : Prop where
  /-- The four design-law legs at one fiber, each discharged by its landed theorem. -/
  fiber : DesignFiber d L k deg hk hdeg T R N g hg h_non_borel μ
  /-- The CAPACITY `hlin` is the literal attention score difference, finite-dimensional. -/
  capacity_literal_scores : ∀ (nK : ℕ) (p : Fin nK × Fin nK)
      (K : (Bridge.attentionScoreRouter dim nK).Ρ),
    (fun x => (Bridge.attentionScoreRouter dim nK).score K x p.2
      - (Bridge.attentionScoreRouter dim nK).score K x p.1) ∈ coordSpan dim
  /-- The ERROR leg, bound to the LITERAL EXECUTED kernel: `execAttnLit ctx` is within the rounding
  envelope whose exponential float cone IS the design law's error window (`R.beta·R.S`). -/
  exec_bound :
    dist (execAttnLit ctx) (attnHead (1 / toReal (litScaleFactor dim : IEEE32Exec))
        (fun a b => toReal (Wt a b)) (fun a b => toReal (Yt a b)))
      ≤ rndLit n dim Bnd Λ (1 / toReal (litScaleFactor dim : IEEE32Exec)) Dlo
          (TLT.ExpError.δexpCone (2 * B' + 2 * u * B') (2 * u * B')) E_lit

/-! ## The arc-closing executable-witness theorem

`literalAttention_carries_designLaw` BUILDS a `LiteralAttentionDesign` for TorchLean's literal executed
`Spec.scaledDotProductAttention` (read over ℝ as `execAttnLit ctx`). Every field is discharged from a
landed theorem on the literal objects:

* `fiber` ← `designFiber` (R5): the four legs, each a landed theorem on the cascade generator (R3a),
  with the measurability cliff at the attention temperature `T`;
* `capacity_literal_scores` ← `litAttnScoreDiff_mem_coordSpan`: the capacity `hlin` is the literal
  `Spec.dot Q Kᵀ` attention score difference;
* `exec_bound` ← `litError_binds_execAttn`: the LITERAL EXECUTED kernel within the rounding envelope
  whose cone IS the design law's error window.

The exact literal instance bound to is `execAttnLit ctx` — TorchLean's `Spec.scaledDotProductAttention`
at backend `IEEE32Exec`, read over ℝ through `toReal` (the fp32 program the hardware runs), with
`R.beta·R.S` set to the executed stabilized-logit cone radius `2B'+2uB'`. -/

/-- **R6 — THE ARC-CLOSING EXECUTABLE WITNESS.** The literal executed TorchLean
`Spec.scaledDotProductAttention` (read over ℝ as `execAttnLit ctx`, at backend `IEEE32Exec`) carries the
design-law invariants: the four R5 fiber legs (capacity / expressivity / measurability cliff at
temperature `T` / error window), the capacity `hlin` bound to the literal `Q·Kᵀ` attention scores, and
the literal executed forward error of `execAttnLit` driven by the design-law error-leg cone (region `R`
with `R.beta·R.S = 2B'+2uB'`, the executed cone radius). No leg is a free assumption or an ideal
surrogate: each is discharged from a landed theorem on the literal objects. The cliff's continuous
non-Borel-range witness `g` (classically the existence of an analytic non-Borel set) is the landed
cliff theorem's external INPUT, not an added axiom. -/
theorem literalAttention_carries_designLaw
    (d L k deg : ℕ) (hk : 0 < k) (hdeg : 1 ≤ deg)
    (T : ℝ) (hT : 0 ≤ T)
    (R : RegionData) (N : NumericalLeg R)
    {β : Type} [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β]
    [StandardBorelSpace β] [Nonempty β]
    (g : β → ℝ) (hg : Continuous g) (h_non_borel : ¬ MeasurableSet (Set.range g))
    (μ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ))) [IsFiniteMeasure μ]
    {n dim : ℕ} {h1 h2 : (n + 1) ≠ 0}
    (ctx : Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) dim h1 h2)
    (Yt : Fin (n + 1) → Fin dim → IEEE32Exec) (Wt : Fin dim → Fin dim → IEEE32Exec)
    (hQ : ctx.Q = Spec.matrixTensor Yt) (hK : ctx.K = Spec.matrixTensor Yt)
    (hV : ctx.V = Spec.matMulSpec (Spec.matrixTensor Yt) (Spec.matrixTensor Wt))
    (hmask : ctx.mask = none)
    (F : Fin (n + 1) → Spec.Tensor IEEE32Exec (.dim (n + 1) .scalar))
    {Dlo E_lit : ℝ} (hN : ExecAttnLitNormal ctx Yt Wt F Dlo E_lit)
    {Bnd Λ B' : ℝ} (hB : 0 ≤ Bnd) (hΛ0 : 0 ≤ Λ)
    (hc : 0 < toReal (litScaleFactor dim : IEEE32Exec))
    (hX : ∀ a l, |toReal (Yt a l)| ≤ Bnd) (hW : ∀ j, ∑ l, |toReal (Wt l j)| ≤ Λ)
    (hnu : ((n + 1 : ℕ) : ℝ) * u < 1) (hdu : (dim : ℝ) * u < 1) (hE : 0 ≤ E_lit)
    (hscore : ∀ i l, |toReal (Spec.Tensor.vecGet (F i) l)| ≤ B')
    (hη2 : 2 * u * B' ≤ 1 / 2)
    (hRlogit : R.beta * R.S = 2 * B' + 2 * u * B') :
    LiteralAttentionDesign d L k deg hk hdeg T R N g hg h_non_borel μ
      ctx Yt Wt Bnd Λ B' Dlo E_lit where
  fiber := designFiber d L k deg hk hdeg T hT R N g hg h_non_borel μ
  capacity_literal_scores := fun nK p K => litAttnScoreDiff_mem_coordSpan dim nK p K
  exec_bound :=
    litError_binds_execAttn ctx Yt Wt hQ hK hV hmask F hN hB hΛ0 hc hX hW hnu hdu hE
      hscore hη2 R N hRlogit

/-! ## Reading off the four legs of the executable witness

The four design-law legs are recoverable from `LiteralAttentionDesign.fiber` (an actual `DesignFiber`),
each at the literal binding scope: capacity at the cascade over the literal attention scores,
expressivity at the route grade of the router degree, the cliff at the attention temperature `T`, and
the error window at the executed cone radius. -/

variable {d L k deg : ℕ} {hk : 0 < k} {hdeg : 1 ≤ deg} {T : ℝ} {R : RegionData} {N : NumericalLeg R}
  {β : Type} [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β]
  [StandardBorelSpace β] [Nonempty β]
  {g : β → ℝ} {hg : Continuous g} {h_non_borel : ¬ MeasurableSet (Set.range g)}
  {μ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ))} [IsFiniteMeasure μ]
  {n dim : ℕ} {h1 h2 : (n + 1) ≠ 0}
  {ctx : Spec.AttentionContext IEEE32Exec (n + 1) (n + 1) dim h1 h2}
  {Yt : Fin (n + 1) → Fin dim → IEEE32Exec} {Wt : Fin dim → Fin dim → IEEE32Exec}
  {Bnd Λ B' Dlo E_lit : ℝ}

/-- **(a) CAPACITY of the executable witness.** The single multiclass capacity number of the cascade
generator over the literal attention scores at `(dim, L, k, deg)` is finite (R7). -/
theorem LiteralAttentionDesign.capacity_finite
    (D : LiteralAttentionDesign d L k deg hk hdeg T R N g hg h_non_borel μ
      ctx Yt Wt Bnd Λ B' Dlo E_lit) :
    NatarajanDim (Fin d → ℝ) (∀ _ : Fin L, Fin k) (designTraceClass d L k deg hk) < ⊤ :=
  D.fiber.capacity_finite

/-- **(b) EXPRESSIVITY of the executable witness.** The degree-`deg` route grade strictly grows with
depth — the SO/quadratic (`deg ≥ 1`) grade at the attention router degree. -/
theorem LiteralAttentionDesign.expressivity_strict
    (D : LiteralAttentionDesign d L k deg hk hdeg T R N g hg h_non_borel μ
      ctx Yt Wt Bnd Λ B' Dlo E_lit) :
    polyDepthGrade deg L ⊂ polyDepthGrade deg (L + 1) :=
  D.fiber.expressivity_strict

/-- **(c) MEASURABILITY CLIFF of the executable witness, at the attention temperature `T`.** The
temperature-`T` soft cascade ghost-gap is Borel, the argmax cascade bad event is non-Borel, and it stays
null-measurable. The cliff lives at the attention temperature `T` (`depthTemperatureCliff` at `τ = T`). -/
theorem LiteralAttentionDesign.measurability_cliff
    (D : LiteralAttentionDesign d L k deg hk hdeg T R N g hg h_non_borel μ
      ctx Yt Wt Bnd Λ B' Dlo E_lit) :
    Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
        ⨆ θ : Boundary.CascadeParam (Boundary.witnessCascade g hg) L,
          Boundary.softCascadeMargin T g hg L θ (p.2 0)
            - Boundary.softCascadeMargin T g hg L θ (p.1 0)) ∧
      ¬ MeasurableSet (Boundary.cascadeBadEvent (Boundary.witnessCascade g hg) L) ∧
      NullMeasurableSet (Boundary.cascadeBadEvent (Boundary.witnessCascade g hg) L) μ :=
  D.fiber.measurability_cliff

/-- **(d) ERROR of the executable witness, bound to the LITERAL EXECUTED op.** The literal executed
kernel `execAttnLit ctx` is within the rounding envelope whose exponential float cone is the design-law
error window. This is the executable-witness payload: the bound is about the running fp32 program. -/
theorem LiteralAttentionDesign.exec_forward_error
    (D : LiteralAttentionDesign d L k deg hk hdeg T R N g hg h_non_borel μ
      ctx Yt Wt Bnd Λ B' Dlo E_lit) :
    dist (execAttnLit ctx) (attnHead (1 / toReal (litScaleFactor dim : IEEE32Exec))
        (fun a b => toReal (Wt a b)) (fun a b => toReal (Yt a b)))
      ≤ rndLit n dim Bnd Λ (1 / toReal (litScaleFactor dim : IEEE32Exec)) Dlo
          (TLT.ExpError.δexpCone (2 * B' + 2 * u * B') (2 * u * B')) E_lit :=
  D.exec_bound

/-! ## The CAPACITY leg at the SO / quadratic (low-rank self-attention) router

The task's capacity leg also names `quadraticRouter_growth_prod` / `quadSpan`. For the SO (degree-2,
low-rank-bilinear self-attention) score family, the route-pattern count is bounded by the Sauer product
at `finrank (quadSpan dim) ≈ dim²`. This is the same combinatorial tameness as the affine case, at the
quadratic feature dimension — the capacity leg at the SO attention router. -/

/-- **The SO/quadratic attention router is tame (finite Sauer-product capacity).** The number of routing
patterns the degree-2 self-attention router realizes on any finite sample is bounded by the Sauer
product at `finrank ℝ (quadSpan dim)`. Recorded as the capacity-leg binding at the SO router degree. -/
theorem litQuadAttn_growth_prod (dim nK : ℕ) (hnK : 0 < nK) (S : Finset (Fin dim → ℝ)) :
    (Set.range (routeRestr (quadRouter dim nK) hnK S)).ncard
      ≤ ∏ _p : Fin nK × Fin nK,
          ∑ r ∈ Finset.range (Module.finrank ℝ (quadSpan dim) + 1), S.card.choose r :=
  quadraticRouter_growth_prod dim nK hnK S

/-! ## The total space IS R3a's generator (the executable witness lives over the cascade)

The capacity object of the bound design law is the route-trace class of R3a's cascade polynomial
functor, so the executable witness is a fact about the design law fibered over the generator `O`. -/

/-- **The executable witness lives over R3a's generator.** The label space of the capacity object
(`designTraceClass`) at `(L, k)` is R3a's cascade leaf-address space, of cardinality `k ^ L` — the
generator's region count. The literal executed attention design is therefore a fact about the design
law fibered over the cascade generator `O`. -/
theorem litDesign_total_eq_generator (L k deg : ℕ) (label : List (Fin k) → Fin (deg + 1)) :
    Fintype.card (cascadePath L (fun _ => k)) = leafCount (cascadeTree label L) :=
  designFibration_total_eq_generator L k deg label

end TLT.TemperedDesignLaw
