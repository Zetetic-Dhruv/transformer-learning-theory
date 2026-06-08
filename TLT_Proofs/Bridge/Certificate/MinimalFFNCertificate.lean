/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Certificate.CertifiedCapacityBound

/-!
# A certified generalization bound for a minimal feed-forward network

This file is the first concrete instantiation of `certified_executed_generalization`: a two-layer
feed-forward network `x ↦ W₂ · relu(W₁ · x)` over the coordinate space `Fin n → ℝ`, composed with a
bounded Lipschitz loss. The abstract bridge needs the ideal forward map to be bounded, measurable, and
continuous in the weights; this file discharges those for the explicit network. Boundedness comes from
the bounded loss, measurability from continuity in the input, and continuity in the weights from the
joint continuity of the matrix–vector product.

The executed (rounded) network and its empirical-risk integrability are taken as the executed-model
interface — supplied by the IEEE binary32 executed-forward analysis — together with the agreement that
the executed layers' ideal part is the network at the certified weights.

## Main definitions

- `matVec` / `reluVec` / `ffn2` — the linear, ReLU, and two-layer forward maps over `Fin n → ℝ`.
- `ffnLoss` — the loss composed with the two-layer forward, as a function of the parameters.

## Main results

- `continuous_matVec_uncurry` — the matrix–vector product is jointly continuous in matrix and vector.
- `continuous_ffn2_param` / `continuous_ffn2_input` — the two-layer forward is continuous in the
  weights and in the input.
- `minimalFFN_certified_generalization` — the certified executed generalization bound for the network.
-/

/-!
## References
- [36] FFN spectral/covering capacity; [19][54] Rademacher/covering (left abstract); joint
  continuity of matvec/ReLU.
- Provenance: Innovation (executed instantiation) — first concrete executed-model bound on the
  2-layer ReLU FFN; capacity is the standard quantity, kept abstract.
-/

open MeasureTheory

noncomputable section

namespace TLT

open Capacity

variable {n : ℕ}

/-- The linear (matrix–vector) map over `Fin n → ℝ`: `(matVec W v) i = ∑ⱼ Wᵢⱼ vⱼ`. -/
def matVec (W : Fin n → Fin n → ℝ) (v : Fin n → ℝ) : Fin n → ℝ := fun i => ∑ j, W i j * v j

/-- The ReLU map over `Fin n → ℝ`: pointwise `max (·) 0`. -/
def reluVec (v : Fin n → ℝ) : Fin n → ℝ := fun i => max (v i) 0

/-- The two-layer feed-forward map `x ↦ W₂ · relu(W₁ · x)`. -/
def ffn2 (W₁ W₂ : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  matVec W₂ (reluVec (matVec W₁ x))

/-- The loss composed with the two-layer forward, as a function of the parameters and input. -/
def ffnLoss {d : ℕ} (W₁ W₂ : ParamSpace d → (Fin n → Fin n → ℝ)) (ℓ : (Fin n → ℝ) → ℝ) :
    ParamSpace d → (Fin n → ℝ) → ℝ :=
  fun θ x => ℓ (ffn2 (W₁ θ) (W₂ θ) x)

/-- The matrix–vector product is jointly continuous in the matrix and the vector. -/
theorem continuous_matVec_uncurry :
    Continuous fun p : (Fin n → Fin n → ℝ) × (Fin n → ℝ) => matVec p.1 p.2 := by
  unfold matVec
  refine continuous_pi fun i => continuous_finset_sum Finset.univ fun j _ => ?_
  exact ((continuous_apply_apply i j).comp continuous_fst).mul
    ((continuous_apply j).comp continuous_snd)

/-- The ReLU map is continuous. -/
theorem continuous_reluVec : Continuous (reluVec : (Fin n → ℝ) → Fin n → ℝ) := by
  unfold reluVec
  exact continuous_pi fun i => (continuous_apply i).max continuous_const

/-- The two-layer forward map is continuous in the weights, for a fixed input. -/
theorem continuous_ffn2_param {d : ℕ} (W₁ W₂ : ParamSpace d → (Fin n → Fin n → ℝ))
    (hW₁ : Continuous W₁) (hW₂ : Continuous W₂) (x : Fin n → ℝ) :
    Continuous fun θ => ffn2 (W₁ θ) (W₂ θ) x := by
  have h1 : Continuous fun θ => matVec (W₁ θ) x :=
    continuous_matVec_uncurry.comp (hW₁.prodMk continuous_const)
  exact continuous_matVec_uncurry.comp (hW₂.prodMk (continuous_reluVec.comp h1))

/-- The two-layer forward map is continuous in the input, for fixed weights. -/
theorem continuous_ffn2_input (W₁ W₂ : Fin n → Fin n → ℝ) :
    Continuous fun x => ffn2 W₁ W₂ x := by
  have h1 : Continuous fun x : Fin n → ℝ => matVec W₁ x :=
    continuous_matVec_uncurry.comp (continuous_const.prodMk continuous_id)
  exact continuous_matVec_uncurry.comp (continuous_const.prodMk (continuous_reluVec.comp h1))

/-- **Certified executed generalization bound for the minimal feed-forward network.** For weight
decoders `W₁, W₂` continuous in the parameters, a bounded Lipschitz loss `ℓ`, and an executed-layer
list `Ls` whose ideal part is the network at the certified weights `w_T`, the executed true risk
exceeds the executed empirical risk plus the capacity-and-rounding budget only on a sample event of
McDiarmid-small probability. -/
theorem minimalFFN_certified_generalization [MeasurableSpace (Fin n → ℝ)]
    [BorelSpace (Fin n → ℝ)] {P : Measure (Fin n → ℝ)} [IsProbabilityMeasure P]
    {m d : ℕ} (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R)
    (W₁ W₂ : ParamSpace d → (Fin n → Fin n → ℝ)) (hW₁ : Continuous W₁) (hW₂ : Continuous W₂)
    (ℓ : (Fin n → ℝ) → ℝ) {b : ℝ} (hℓb : ∀ v, |ℓ v| ≤ b) (hℓcont : Continuous ℓ)
    {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ) (hℓLip : ∀ p q, |ℓ p - ℓ q| ≤ Lℓ * dist p q)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R)
    (Ls : List (ExecLayer (Fin n → ℝ)))
    (hagree : ∀ x, idealComp Ls x
        = ffn2 (W₁ (embedBase Capacity.Dyadic w_T.1)) (W₂ (embedBase Capacity.Dyadic w_T.1)) x)
    (hintG : Integrable (fun x => ℓ (execComp Ls x)) P) :
    (Measure.pi fun _ : Fin m => P).real
        {S | ¬ ((∫ x, ℓ (execComp Ls x) ∂P)
              ≤ (1 / (m : ℝ)) * ∑ i, ℓ (execComp Ls (S i))
                + (2 * (∫ S', empiricalCapacityReal R (ffnLoss W₁ W₂ ℓ) S'
                    ∂(Measure.pi fun _ : Fin m => P)) + ε)
                + 2 * (Lℓ * envBound Ls))}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) := by
  have hFb : ∀ θ x, |ffnLoss W₁ W₂ ℓ θ x| ≤ b := fun θ x => hℓb _
  have hFcont : ∀ x, Continuous fun θ : ParamSpace d => ffnLoss W₁ W₂ ℓ θ x :=
    fun x => hℓcont.comp (continuous_ffn2_param W₁ W₂ hW₁ hW₂ x)
  have hFmeas : ∀ θ, Measurable (ffnLoss W₁ W₂ ℓ θ) :=
    fun θ => (hℓcont.comp (continuous_ffn2_input (W₁ θ) (W₂ θ))).measurable
  have hbridge : ∀ x, ffnLoss W₁ W₂ ℓ (embedBase Capacity.Dyadic w_T.1) x = ℓ (idealComp Ls x) :=
    fun x => by simp only [ffnLoss]; rw [hagree x]
  have hintF : Integrable (fun x => ℓ (idealComp Ls x)) P := by
    have heq : (fun x => ℓ (idealComp Ls x))
        = ffnLoss W₁ W₂ ℓ (embedBase Capacity.Dyadic w_T.1) := funext fun x => (hbridge x).symm
    rw [heq]
    exact integrable_of_bound_of_measurable (hFmeas _) fun x => hFb _ x
  exact certified_executed_generalization hm hR (ffnLoss W₁ W₂ ℓ) hFb hFmeas hFcont hε w_T Ls ℓ
    hLℓ0 hℓLip hbridge hintF hintG

end TLT
