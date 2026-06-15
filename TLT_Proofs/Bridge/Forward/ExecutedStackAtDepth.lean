/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Lipschitz.MultiHeadAttnCertificate
import TLT_Proofs.Bridge.Certificate.MultiHeadEncoderStack

/-!
# Executed-at-depth: discharging `hagree` by construction

The depth-`L` certified bounds take an executed layer list `Ls` together with the hypothesis
`hagree : idealComp Ls = lparamComp St θ ∘ clampCoord ρ` connecting the executed forward to the
clamped spec stack. This file discharges that hypothesis **by construction**, for an arbitrary
`ParamLayerLocal` stack, so the IEEE-binary32 executed instantiation at depth is concrete rather than
assumed.

The obstruction: `ExecLayer.ideal_lip` is a *global* Lipschitz field, but a post-norm attention block
is Lipschitz only on the activation ball `D` (the Kim et al. boundary). The resolution: each executed
layer's ideal is the **pre-clamped** block `block ∘ clampCoord ρ`, globally Lipschitz (clamp is
`1`-Lipschitz into `D`, the block is Lipschitz on `D`). Forward-invariance (`block : D → D`) makes the
inner clamps identities, so the pre-clamped composition telescopes to the clamped spec stack:
`idealComp (clampExecLayer ρ :: Es) = lparamComp St θ ∘ clampCoord ρ`. The per-layer rounding errors
then compose through `envBound` at depth.

## Main results

- `clampExecLayer`: the coordinatewise clamp as an exact (`rnd = 0`) `ExecLayer`.
- `idealComp_preClampExec`: the executed forward's ideal equals the clamped spec stack, when each
  executed layer's ideal is the pre-clamped block (`List.Forall₂`) and the stack is forward-invariant.
-/

/-!
## References
- [38] envelope; [31] bounded-domain boundary; capstones via the vendored McDiarmid/Dudley/
  Rademacher backbone [54]/[55].
-/

open MeasureTheory

noncomputable section

namespace TLT

open Capacity

variable {n d : ℕ}

/-- The coordinatewise clamp onto the radius-`ρ` ball as an `ExecLayer`: exact (`rnd = 0`),
`1`-Lipschitz. As the first layer of the executed forward it lands every input in the activation ball,
where the subsequent pre-clamped blocks behave as the spec stack. -/
def clampExecLayer (ρ : ℝ) : ExecLayer (Fin n → Fin d → ℝ) where
  ideal := clampCoord ρ
  exec := clampCoord ρ
  lip := 1
  rnd := 0
  lip_nonneg := zero_le_one
  ideal_lip := fun a b => by rw [one_mul]; exact clampCoord_lipschitz ρ a b
  exec_close := fun y => by simp

/-- **The pre-clamped executed forward telescopes to the clamped spec stack (on the ball).** If each
executed layer `E` has ideal `block ∘ clampCoord ρ` (paired with the spec block `B` by `List.Forall₂`)
and every block maps the radius-`ρ` ball into itself, then for any input already in the ball the
executed ideal composition equals the parametric composition. The inner clamps are dropped one by one
using forward-invariance (the running activation stays in the ball, where the clamp is the identity). -/
lemma idealComp_preClampExec {p : ℕ} {ρ : ℝ} (θ : ParamSpace p)
    {St : List (ParamLayerLocal (ParamSpace p) (Fin n → Fin d → ℝ))}
    {Es : List (ExecLayer (Fin n → Fin d → ℝ))}
    (hF : List.Forall₂ (fun B E => E.ideal = fun x => B.map θ (clampCoord ρ x)) St Es)
    (hinv : ∀ B ∈ St, ∀ y : Fin n → Fin d → ℝ, ‖y‖ ≤ ρ → ‖B.map θ y‖ ≤ ρ)
    {y : Fin n → Fin d → ℝ} (hy : ‖y‖ ≤ ρ) :
    idealComp Es y = lparamComp St θ y := by
  induction hF generalizing y with
  | nil => rfl
  | @cons B E St' Es' hBE hF' ih =>
      simp only [idealComp, lparamComp]
      rw [hBE]
      simp only []
      rw [clampCoord_eq_of_norm_le hy]
      exact ih (fun B' hB' => hinv B' (List.mem_cons_of_mem _ hB'))
        (hinv B List.mem_cons_self y hy)

/-- **`hagree`, discharged by construction.** With `Ls = clampExecLayer ρ :: Es`, the executed forward's
ideal composition is exactly the clamped spec stack `x ↦ lparamComp St θ (clampCoord ρ x)`,
the hypothesis the certified bounds assume. -/
theorem idealComp_clampExecLayer_cons {p : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (θ : ParamSpace p)
    {St : List (ParamLayerLocal (ParamSpace p) (Fin n → Fin d → ℝ))}
    {Es : List (ExecLayer (Fin n → Fin d → ℝ))}
    (hF : List.Forall₂ (fun B E => E.ideal = fun x => B.map θ (clampCoord ρ x)) St Es)
    (hinv : ∀ B ∈ St, ∀ y : Fin n → Fin d → ℝ, ‖y‖ ≤ ρ → ‖B.map θ y‖ ≤ ρ)
    (x : Fin n → Fin d → ℝ) :
    idealComp (clampExecLayer ρ :: Es) x = lparamComp St θ (clampCoord ρ x) := by
  simp only [idealComp, clampExecLayer]
  exact idealComp_preClampExec θ hF hinv (clampCoord_norm_le hρ0 x)

/-- **Executed-at-depth certified generalization for the true-multi-head stack.** The depth-`L`
multi-head certified bound with its `hagree` hypothesis *discharged by construction*: given the float32
executed layers `Es` whose per-layer ideals are the pre-clamped blocks (`hForall2`) at the certified
weights, `Ls = clampExecLayer ρ :: Es` is a concrete executed forward whose ideal is the clamped stack,
so the McDiarmid bound holds with the depth-composed rounding envelope `envBound Ls`; no abstract
executed-forward hypothesis remains. -/
theorem normMultiHeadStack_executed_at_depth {H p m : ℕ} [NeZero n] [Nonempty (Fin p)]
    [MeasurableSpace (Fin n → Fin d → ℝ)] [BorelSpace (Fin n → Fin d → ℝ)]
    {P : Measure (Fin n → Fin d → ℝ)} [IsProbabilityMeasure P] (hm : 0 < m)
    {R B bV βY γW scale Cγ Cβ Lγ Lβ LWQ LWK LWVO : ℝ} (hR : 0 ≤ R) (hscale : 0 < scale) (hd : 0 < d)
    (hB : 0 ≤ B) (hbV0 : 0 ≤ bV) (hβY0 : 0 ≤ βY) (hγW0 : 0 ≤ γW) (hCγ0 : 0 ≤ Cγ) (hCβ0 : 0 ≤ Cβ)
    (hLγ0 : 0 ≤ Lγ) (hLβ0 : 0 ≤ Lβ) (hLWQ0 : 0 ≤ LWQ) (hLWK0 : 0 ≤ LWK) (hLWVO0 : 0 ≤ LWVO)
    (WQ WK WVO : ParamSpace p → (Fin H → Fin d → Fin d → ℝ)) (γ β : ParamSpace p → (Fin d → ℝ))
    (hWQcont : Continuous WQ) (hWKcont : Continuous WK) (hWVOcont : Continuous WVO)
    (hγcont : Continuous γ) (hβcont : Continuous β)
    (hγB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ θ j| ≤ Cγ)
    (hβB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β θ j| ≤ Cβ)
    (hβYD : ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ i, (∑ a, |y i a|) ≤ βY)
    (hQB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h i e, |matMulCoord (WQ θ h) y i e| ≤ B)
    (hKB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h k' e, |matMulCoord (WK θ h) y k' e| ≤ B)
    (hVB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h j, ‖matMulCoord (WVO θ h) y j‖ ≤ bV)
    (hγWQ : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WQ θ h k j|) ≤ γW)
    (hγWK : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WK θ h k j|) ≤ γW)
    (hγWVO : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WVO θ h k j|) ≤ γW)
    (hγLip : ∀ θ θ', dist (γ θ) (γ θ') ≤ Lγ * dist θ θ')
    (hβLip : ∀ θ θ', dist (β θ) (β θ') ≤ Lβ * dist θ θ')
    (hWQLip : ∀ θ θ', dist (WQ θ) (WQ θ') ≤ LWQ * dist θ θ')
    (hWKLip : ∀ θ θ', dist (WK θ) (WK θ') ≤ LWK * dist θ θ')
    (hWVOLip : ∀ θ θ', dist (WVO θ) (WVO θ') ≤ LWVO * dist θ θ')
    (ℓ : (Fin n → Fin d → ℝ) → ℝ) {b : ℝ} (hb : 0 < b) (hℓb : ∀ v, |ℓ v| ≤ b)
    (hℓcont : Continuous ℓ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ) (hℓLip : ∀ u v, |ℓ u - ℓ v| ≤ Lℓ * dist u v)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R)
    (hwT : embedBase Capacity.Dyadic w_T.1 ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p)))) (L : ℕ)
    (Es : List (ExecLayer (Fin n → Fin d → ℝ)))
    (hForall2 : List.Forall₂ (fun (Bk : ParamLayerLocal (ParamSpace p) (Fin n → Fin d → ℝ)) E =>
        E.ideal = fun x => Bk.map (embedBase Capacity.Dyadic w_T.1) (clampCoord (Real.sqrt d * Cγ + Cβ) x))
      (List.replicate L (normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0
        hLWVO0 WQ WK WVO γ β)) Es)
    (hintG : Integrable (fun x => ℓ (execComp (clampExecLayer (Real.sqrt d * Cγ + Cβ) :: Es) x)) P)
    (hLpos : 0 < Lℓ * lparamLipBound (List.replicate L (normMultiHeadBlock (n := n) hscale hB hbV0 hβY0
        hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 WQ WK WVO γ β))) :
    (Measure.pi fun _ : Fin m => P).real
        {S | ¬ ((∫ x, ℓ (execComp (clampExecLayer (Real.sqrt d * Cγ + Cβ) :: Es) x) ∂P)
              ≤ (1 / (m : ℝ)) * ∑ i, ℓ (execComp (clampExecLayer (Real.sqrt d * Cγ + Cβ) :: Es) (S i))
                + (2 * ((12 * Real.sqrt 2) * (1 / Real.sqrt m)
                    * (∫⁻ ε in Set.Ioc (0 : ℝ) (2 * b),
                        ENNReal.ofReal (Real.sqrt (Real.log 2)
                          + Real.sqrt ((p : ℝ) * (4 * R * (Lℓ * lparamLipBound
                              (List.replicate L (normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0
                                hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 WQ WK WVO γ β)))))
                            * ε ^ (-(1 / 2) : ℝ))).toReal) + ε)
                + 2 * (Lℓ * envBound (clampExecLayer (Real.sqrt d * Cγ + Cβ) :: Es)))}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) := by
  have hρ0 : (0 : ℝ) ≤ Real.sqrt d * Cγ + Cβ :=
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCγ0) hCβ0
  have hinv : ∀ Bk ∈ List.replicate L (normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0
        hLβ0 hLWQ0 hLWK0 hLWVO0 WQ WK WVO γ β),
      ∀ y : Fin n → Fin d → ℝ, ‖y‖ ≤ Real.sqrt d * Cγ + Cβ →
        ‖Bk.map (embedBase Capacity.Dyadic w_T.1) y‖ ≤ Real.sqrt d * Cγ + Cβ := by
    intro Bk hBk y _
    rw [List.eq_of_mem_replicate hBk]
    exact normMultiHeadBlock_forward_inv hd (γ (embedBase Capacity.Dyadic w_T.1))
      (β (embedBase Capacity.Dyadic w_T.1)) (hγB _ hwT) (hβB _ hwT) scale
      (WQ (embedBase Capacity.Dyadic w_T.1)) (WK (embedBase Capacity.Dyadic w_T.1))
      (WVO (embedBase Capacity.Dyadic w_T.1)) y
  exact normMultiHeadStack_certified_generalization hm hR hscale hd hB hbV0 hβY0 hγW0 hCγ0 hCβ0 hLγ0
    hLβ0 hLWQ0 hLWK0 hLWVO0 WQ WK WVO γ β hWQcont hWKcont hWVOcont hγcont hβcont hγB hβB hβYD hQB hKB
    hVB hγWQ hγWK hγWVO hγLip hβLip hWQLip hWKLip hWVOLip ℓ hb hℓb hℓcont hLℓ0 hℓLip hε w_T L
    (clampExecLayer (Real.sqrt d * Cγ + Cβ) :: Es)
    (fun x => idealComp_clampExecLayer_cons hρ0 (embedBase Capacity.Dyadic w_T.1) hForall2 hinv x)
    hintG hLpos

/-- **The depth-`L` executed forward is within the depth-composed envelope of the clamped spec stack.**
Combining `execComp_envelope` (executed within `envBound` of ideal) with the pre-clamp bridge: for the
concrete executed layers `Es` whose ideals are the pre-clamped blocks, the IEEE-binary32 forward
`execComp (clampExecLayer ρ :: Es)` is uniformly within `envBound (clampExecLayer ρ :: Es)` of the
clamped spec stack. When each `Es` layer's `rnd` is its per-layer fp32 rounding envelope, that bound is
the depth-composed forward error. (The per-layer `rnd` is supplied as data, exactly as the single-layer
executed certificate supplies it; deriving it from the per-operation γₙ is the literal-fp32-block
forward-error envelope, a separate result.) -/
theorem executedForward_envelope_at_depth {p : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (θ : ParamSpace p)
    {St : List (ParamLayerLocal (ParamSpace p) (Fin n → Fin d → ℝ))}
    {Es : List (ExecLayer (Fin n → Fin d → ℝ))}
    (hF : List.Forall₂ (fun B E => E.ideal = fun x => B.map θ (clampCoord ρ x)) St Es)
    (hinv : ∀ B ∈ St, ∀ y : Fin n → Fin d → ℝ, ‖y‖ ≤ ρ → ‖B.map θ y‖ ≤ ρ)
    (x : Fin n → Fin d → ℝ) :
    dist (execComp (clampExecLayer ρ :: Es) x) (lparamComp St θ (clampCoord ρ x))
      ≤ envBound (clampExecLayer ρ :: Es) := by
  rw [← idealComp_clampExecLayer_cons hρ0 θ hF hinv x]
  exact execComp_envelope (clampExecLayer ρ :: Es) x

/-- **Executed-at-depth for the untied standard-transformer stack**: the generic bridge applied to the
untied certified bound. -/
theorem normMultiHeadStack_untied_executed_at_depth {H p L m : ℕ} [NeZero n] [Nonempty (Fin p)]
    [MeasurableSpace (Fin n → Fin d → ℝ)] [BorelSpace (Fin n → Fin d → ℝ)]
    {P : Measure (Fin n → Fin d → ℝ)} [IsProbabilityMeasure P] (hm : 0 < m)
    {R B bV βY γW scale Cγ Cβ Lγ Lβ LWQ LWK LWVO : ℝ} (hR : 0 ≤ R) (hscale : 0 < scale) (hd : 0 < d)
    (hB : 0 ≤ B) (hbV0 : 0 ≤ bV) (hβY0 : 0 ≤ βY) (hγW0 : 0 ≤ γW) (hCγ0 : 0 ≤ Cγ) (hCβ0 : 0 ≤ Cβ)
    (hLγ0 : 0 ≤ Lγ) (hLβ0 : 0 ≤ Lβ) (hLWQ0 : 0 ≤ LWQ) (hLWK0 : 0 ≤ LWK) (hLWVO0 : 0 ≤ LWVO)
    (WQ WK WVO : Fin L → ParamSpace p → (Fin H → Fin d → Fin d → ℝ))
    (γ β : Fin L → ParamSpace p → (Fin d → ℝ))
    (hWQcont : ∀ i, Continuous (WQ i)) (hWKcont : ∀ i, Continuous (WK i))
    (hWVOcont : ∀ i, Continuous (WVO i)) (hγcont : ∀ i, Continuous (γ i)) (hβcont : ∀ i, Continuous (β i))
    (hγB : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ i θ j| ≤ Cγ)
    (hβB : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β i θ j| ≤ Cβ)
    (hβYD : ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ k, (∑ a, |y k a|) ≤ βY)
    (hQB : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h a e, |matMulCoord (WQ i θ h) y a e| ≤ B)
    (hKB : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h k' e, |matMulCoord (WK i θ h) y k' e| ≤ B)
    (hVB : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h j, ‖matMulCoord (WVO i θ h) y j‖ ≤ bV)
    (hγWQ : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WQ i θ h k j|) ≤ γW)
    (hγWK : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WK i θ h k j|) ≤ γW)
    (hγWVO : ∀ i, ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ h j, (∑ k, |WVO i θ h k j|) ≤ γW)
    (hγLip : ∀ i, ∀ θ θ', dist (γ i θ) (γ i θ') ≤ Lγ * dist θ θ')
    (hβLip : ∀ i, ∀ θ θ', dist (β i θ) (β i θ') ≤ Lβ * dist θ θ')
    (hWQLip : ∀ i, ∀ θ θ', dist (WQ i θ) (WQ i θ') ≤ LWQ * dist θ θ')
    (hWKLip : ∀ i, ∀ θ θ', dist (WK i θ) (WK i θ') ≤ LWK * dist θ θ')
    (hWVOLip : ∀ i, ∀ θ θ', dist (WVO i θ) (WVO i θ') ≤ LWVO * dist θ θ')
    (ℓ : (Fin n → Fin d → ℝ) → ℝ) {b : ℝ} (hb : 0 < b) (hℓb : ∀ v, |ℓ v| ≤ b)
    (hℓcont : Continuous ℓ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ) (hℓLip : ∀ u v, |ℓ u - ℓ v| ≤ Lℓ * dist u v)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R)
    (hwT : embedBase Capacity.Dyadic w_T.1 ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))))
    (Es : List (ExecLayer (Fin n → Fin d → ℝ)))
    (hForall2 : List.Forall₂ (fun (Bk : ParamLayerLocal (ParamSpace p) (Fin n → Fin d → ℝ)) E =>
        E.ideal = fun x => Bk.map (embedBase Capacity.Dyadic w_T.1) (clampCoord (Real.sqrt d * Cγ + Cβ) x))
      (List.ofFn (fun i => normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0
        hLWK0 hLWVO0 (WQ i) (WK i) (WVO i) (γ i) (β i))) Es)
    (hintG : Integrable (fun x => ℓ (execComp (clampExecLayer (Real.sqrt d * Cγ + Cβ) :: Es) x)) P)
    (hLpos : 0 < Lℓ * lparamLipBound (List.ofFn (fun i => normMultiHeadBlock (n := n) hscale hB hbV0
        hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 (WQ i) (WK i) (WVO i) (γ i) (β i)))) :
    (Measure.pi fun _ : Fin m => P).real
        {S | ¬ ((∫ x, ℓ (execComp (clampExecLayer (Real.sqrt d * Cγ + Cβ) :: Es) x) ∂P)
              ≤ (1 / (m : ℝ)) * ∑ i, ℓ (execComp (clampExecLayer (Real.sqrt d * Cγ + Cβ) :: Es) (S i))
                + (2 * ((12 * Real.sqrt 2) * (1 / Real.sqrt m)
                    * (∫⁻ ε in Set.Ioc (0 : ℝ) (2 * b),
                        ENNReal.ofReal (Real.sqrt (Real.log 2)
                          + Real.sqrt ((p : ℝ) * (4 * R * (Lℓ * lparamLipBound
                              (List.ofFn (fun i => normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0
                                hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 (WQ i) (WK i) (WVO i) (γ i) (β i))))))
                            * ε ^ (-(1 / 2) : ℝ))).toReal) + ε)
                + 2 * (Lℓ * envBound (clampExecLayer (Real.sqrt d * Cγ + Cβ) :: Es)))}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) := by
  have hρ0 : (0 : ℝ) ≤ Real.sqrt d * Cγ + Cβ :=
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCγ0) hCβ0
  have hinv : ∀ Bk ∈ List.ofFn (fun i => normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0
        hLβ0 hLWQ0 hLWK0 hLWVO0 (WQ i) (WK i) (WVO i) (γ i) (β i)),
      ∀ y : Fin n → Fin d → ℝ, ‖y‖ ≤ Real.sqrt d * Cγ + Cβ →
        ‖Bk.map (embedBase Capacity.Dyadic w_T.1) y‖ ≤ Real.sqrt d * Cγ + Cβ := by
    intro Bk hBk y _
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hBk
    exact normMultiHeadBlock_forward_inv hd (γ i (embedBase Capacity.Dyadic w_T.1))
      (β i (embedBase Capacity.Dyadic w_T.1)) (hγB i _ hwT) (hβB i _ hwT) scale
      (WQ i (embedBase Capacity.Dyadic w_T.1)) (WK i (embedBase Capacity.Dyadic w_T.1))
      (WVO i (embedBase Capacity.Dyadic w_T.1)) y
  exact normMultiHeadStack_untied_certified_generalization hm hR hscale hd hB hbV0 hβY0 hγW0 hCγ0 hCβ0
    hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 WQ WK WVO γ β hWQcont hWKcont hWVOcont hγcont hβcont hγB hβB hβYD hQB
    hKB hVB hγWQ hγWK hγWVO hγLip hβLip hWQLip hWKLip hWVOLip ℓ hb hℓb hℓcont hLℓ0 hℓLip hε w_T
    (clampExecLayer (Real.sqrt d * Cγ + Cβ) :: Es)
    (fun x => idealComp_clampExecLayer_cons hρ0 (embedBase Capacity.Dyadic w_T.1) hForall2 hinv x)
    hintG hLpos

/-- **Executed-at-depth for the FFN-union encoder stack**: the generic bridge applied to the full
true-multi-head encoder layer (attention ∘ feed-forward) certified bound; forward-invariance is
dispatched by block type. -/
theorem transformerEncoderStackMH_executed_at_depth {H p hdim m : ℕ} [NeZero n] [Nonempty (Fin p)]
    [MeasurableSpace (Fin n → Fin d → ℝ)] [BorelSpace (Fin n → Fin d → ℝ)]
    {P : Measure (Fin n → Fin d → ℝ)} [IsProbabilityMeasure P] (hm : 0 < m)
    {R B bV βY γW scale Cγ Cβ Lγ Lβ LWQ LWK LWVO bW1 bW2 : ℝ} (hR : 0 ≤ R) (hscale : 0 < scale)
    (hd : 0 < d) (hB : 0 ≤ B) (hbV0 : 0 ≤ bV) (hβY0 : 0 ≤ βY) (hγW0 : 0 ≤ γW) (hCγ0 : 0 ≤ Cγ)
    (hCβ0 : 0 ≤ Cβ) (hLγ0 : 0 ≤ Lγ) (hLβ0 : 0 ≤ Lβ) (hLWQ0 : 0 ≤ LWQ) (hLWK0 : 0 ≤ LWK)
    (hLWVO0 : 0 ≤ LWVO) (hbW1 : 0 ≤ bW1) (hbW2 : 0 ≤ bW2)
    (WQ WK WVO : ParamSpace p → (Fin H → Fin d → Fin d → ℝ))
    (W1 : Fin d → Fin hdim → ℝ) (b1 : Fin hdim → ℝ) (W2 : Fin hdim → Fin d → ℝ) (b2 : Fin d → ℝ)
    (hW1c : ∀ l, (∑ k, |W1 k l|) ≤ bW1) (hW2c : ∀ j, (∑ l, |W2 l j|) ≤ bW2)
    (γ1 β1 γ2 β2 : ParamSpace p → (Fin d → ℝ))
    (hWQcont : Continuous WQ) (hWKcont : Continuous WK) (hWVOcont : Continuous WVO)
    (hγ1cont : Continuous γ1) (hβ1cont : Continuous β1) (hγ2cont : Continuous γ2) (hβ2cont : Continuous β2)
    (hγ1B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ1 θ j| ≤ Cγ)
    (hβ1B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β1 θ j| ≤ Cβ)
    (hγ2B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |γ2 θ j| ≤ Cγ)
    (hβ2B : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))), ∀ j, |β2 θ j| ≤ Cβ)
    (hβYD : ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ i, (∑ a, |y i a|) ≤ βY)
    (hQB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h i e, |matMulCoord (WQ θ h) y i e| ≤ B)
    (hKB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
      ∀ h k' e, |matMulCoord (WK θ h) y k' e| ≤ B)
    (hVB : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p))),
      ∀ y ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
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
    (ℓ : (Fin n → Fin d → ℝ) → ℝ) {b : ℝ} (hb : 0 < b) (hℓb : ∀ v, |ℓ v| ≤ b)
    (hℓcont : Continuous ℓ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ) (hℓLip : ∀ u v, |ℓ u - ℓ v| ≤ Lℓ * dist u v)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R)
    (hwT : embedBase Capacity.Dyadic w_T.1 ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin p)))) (L : ℕ)
    (Es : List (ExecLayer (Fin n → Fin d → ℝ)))
    (hForall2 : List.Forall₂ (fun (Bk : ParamLayerLocal (ParamSpace p) (Fin n → Fin d → ℝ)) E =>
        E.ideal = fun x => Bk.map (embedBase Capacity.Dyadic w_T.1) (clampCoord (Real.sqrt d * Cγ + Cβ) x))
      (List.flatten (List.replicate L
        [normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0
            WQ WK WVO γ1 β1,
         normFFNBlock (s := n) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2])) Es)
    (hintG : Integrable (fun x => ℓ (execComp (clampExecLayer (Real.sqrt d * Cγ + Cβ) :: Es) x)) P)
    (hLpos : 0 < Lℓ * lparamLipBound (List.flatten (List.replicate L
        [normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0
            WQ WK WVO γ1 β1,
         normFFNBlock (s := n) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2]))) :
    (Measure.pi fun _ : Fin m => P).real
        {S | ¬ ((∫ x, ℓ (execComp (clampExecLayer (Real.sqrt d * Cγ + Cβ) :: Es) x) ∂P)
              ≤ (1 / (m : ℝ)) * ∑ i, ℓ (execComp (clampExecLayer (Real.sqrt d * Cγ + Cβ) :: Es) (S i))
                + (2 * ((12 * Real.sqrt 2) * (1 / Real.sqrt m)
                    * (∫⁻ ε in Set.Ioc (0 : ℝ) (2 * b),
                        ENNReal.ofReal (Real.sqrt (Real.log 2)
                          + Real.sqrt ((p : ℝ) * (4 * R * (Lℓ * lparamLipBound (List.flatten
                              (List.replicate L
                                [normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0
                                    hLWQ0 hLWK0 hLWVO0 WQ WK WVO γ1 β1,
                                 normFFNBlock (s := n) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2])))))
                            * ε ^ (-(1 / 2) : ℝ))).toReal) + ε)
                + 2 * (Lℓ * envBound (clampExecLayer (Real.sqrt d * Cγ + Cβ) :: Es)))}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) := by
  have hρ0 : (0 : ℝ) ≤ Real.sqrt d * Cγ + Cβ :=
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCγ0) hCβ0
  set aBlk := normMultiHeadBlock (n := n) hscale hB hbV0 hβY0 hγW0 hCγ0 hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0
    WQ WK WVO γ1 β1 with haBlk
  set fBlk := normFFNBlock (s := n) hCγ0 hCβ0 hLγ0 hLβ0 hbW1 hbW2 W1 b1 W2 b2 γ2 β2 with hfBlk
  have hinv : ∀ Bk ∈ List.flatten (List.replicate L [aBlk, fBlk]),
      ∀ y : Fin n → Fin d → ℝ, ‖y‖ ≤ Real.sqrt d * Cγ + Cβ →
        ‖Bk.map (embedBase Capacity.Dyadic w_T.1) y‖ ≤ Real.sqrt d * Cγ + Cβ := by
    intro Bk hBk y _
    have hmem : Bk = aBlk ∨ Bk = fBlk := by
      rcases List.mem_flatten.mp hBk with ⟨t, ht, hBt⟩
      rw [List.eq_of_mem_replicate ht] at hBt; simpa using hBt
    rcases hmem with h | h
    · rw [h, haBlk]
      exact normMultiHeadBlock_forward_inv hd (γ1 (embedBase Capacity.Dyadic w_T.1))
        (β1 (embedBase Capacity.Dyadic w_T.1)) (hγ1B _ hwT) (hβ1B _ hwT) scale
        (WQ (embedBase Capacity.Dyadic w_T.1)) (WK (embedBase Capacity.Dyadic w_T.1))
        (WVO (embedBase Capacity.Dyadic w_T.1)) y
    · rw [h, hfBlk]
      exact normResidualBlock_forward_inv hd (γ2 (embedBase Capacity.Dyadic w_T.1))
        (β2 (embedBase Capacity.Dyadic w_T.1)) (hγ2B _ hwT) (hβ2B _ hwT) (ffnCoord W1 b1 W2 b2) y
  exact transformerEncoderStackMH_certified_generalization hm hR hscale hd hB hbV0 hβY0 hγW0 hCγ0 hCβ0
    hLγ0 hLβ0 hLWQ0 hLWK0 hLWVO0 hbW1 hbW2 WQ WK WVO W1 b1 W2 b2 hW1c hW2c γ1 β1 γ2 β2 hWQcont hWKcont
    hWVOcont hγ1cont hβ1cont hγ2cont hβ2cont hγ1B hβ1B hγ2B hβ2B hβYD hQB hKB hVB hγWQ hγWK hγWVO
    hγ1Lip hβ1Lip hWQLip hWKLip hWVOLip hγ2Lip hβ2Lip ℓ hb hℓb hℓcont hLℓ0 hℓLip hε w_T L
    (clampExecLayer (Real.sqrt d * Cγ + Cβ) :: Es)
    (fun x => idealComp_clampExecLayer_cons hρ0 (embedBase Capacity.Dyadic w_T.1) hForall2 hinv x)
    hintG hLpos

end TLT

