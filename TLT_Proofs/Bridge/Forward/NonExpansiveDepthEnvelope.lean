/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Forward.ExecutedStackAtDepth

/-!
# Linear-in-depth rounding envelope for non-expansive layer stacks

The generic network rounding envelope `envBound = ∑ᵢ rndᵢ · ∏_{j>i} Λⱼ` (`ForwardEnvelope`) amplifies
each layer's local rounding error by the product of its downstream ideal Lipschitz constants. When the
per-layer constants exceed `1` (as for a layer-normalization layer, whose constant scales like
`1/√ε`), that product is exponential in depth, and the certified executed bound is non-vacuous only
for shallow stacks.

This file isolates the exact condition under which the envelope is instead **linear** in depth: every
layer is *non-expansive*, `lip ≤ 1`. Then the downstream product is `≤ 1` (`lipProd_le_one_of_nonexpansive`),
the envelope collapses to the *sum* of the per-layer rounding bounds (`envBound_le_sum_rnd_of_nonexpansive`),
and under a uniform per-layer bound `ρ` it is at most `(#layers) · ρ` (`envBound_le_length_mul_of_nonexpansive`).
The forward and risk transfers inherit this: `execComp_envelope_linear` and `execComp_risk_transfer_linear`
give a correction that grows linearly, not exponentially, in depth.

Non-expansiveness is the sharp dividing line. Reset layers (the coordinatewise activation clamp,
`clampExecLayer`) are non-expansive by construction, and `nonexpansiveExecLayer` packages any
`1`-Lipschitz ideal map with a genuine rounding bound, witnessing that the linear bound is non-trivial
(tight in `ρ`). For the post-norm multi-head block the ideal Lipschitz constant is
`Cγ·(2√d+2)/√ε · (1 + L_mha)`; `normMultiHeadBlock_nonexpansive` shows the block is non-expansive
exactly when that constant is `≤ 1`, the certified-non-expansive regime (small `‖γ‖`, residual scaling,
or large `ε`; see the stabilization studied in deep-transformer signal-propagation analyses, e.g. Wang et
al., *DeepNet*, 2022; Takase et al., 2023.

## Main results

- `lipProd_le_one_of_nonexpansive`: a non-expansive stack has downstream Lipschitz product `≤ 1`.
- `envBound_le_sum_rnd_of_nonexpansive`: the envelope is at most the sum of per-layer rounding bounds.
- `envBound_le_length_mul_of_nonexpansive`: under a uniform bound `ρ`, the envelope is `≤ (#layers)·ρ`.
- `execComp_envelope_linear` / `execComp_risk_transfer_linear`: linear-in-depth forward / risk transfer.
- `nonexpansiveExecLayer`, `replicate_nonexpansive_envelope_linear`: a witness with nonzero rounding.
- `normMultiHeadBlock_nonexpansive`: the post-norm multi-head block is non-expansive when its
  input-Lipschitz constant is `≤ 1`.
-/

/-!
## References
- [38][43] forward-error envelope + relative-rounding (`γₙ`) model; [31] LayerNorm `1/√ε` Lipschitz
  + signal cap; [39][40] DeepNet/Takase non-expansive deep stabilization.
-/

open MeasureTheory

namespace TLT

variable {V : Type*} [PseudoMetricSpace V]

/-- A layer's rounding bound is nonnegative: `exec_close` bounds a distance at any point, and a
distance is nonnegative (needs a point, hence `Nonempty V`). -/
lemma ExecLayer.rnd_nonneg [Nonempty V] (L : ExecLayer V) : 0 ≤ L.rnd :=
  le_trans dist_nonneg (L.exec_close (Classical.arbitrary V))

/-- If every layer is non-expansive (`lip ≤ 1`), the product of the per-layer ideal Lipschitz
constants is `≤ 1`: the exponential `∏ lipᵢ` collapses to a bound of `1`. -/
lemma lipProd_le_one_of_nonexpansive {Ls : List (ExecLayer V)}
    (h : ∀ L ∈ Ls, L.lip ≤ 1) : lipProd Ls ≤ 1 := by
  induction Ls with
  | nil => simp [lipProd]
  | cons L Ls ih =>
      have hL : L.lip ≤ 1 := h L List.mem_cons_self
      have htail : lipProd Ls ≤ 1 := ih (fun L' hL' => h L' (List.mem_cons_of_mem _ hL'))
      simp only [lipProd]
      calc L.lip * lipProd Ls ≤ 1 * 1 := mul_le_mul hL htail (lipProd_nonneg Ls) zero_le_one
        _ = 1 := mul_one 1

/-- **Non-expansive stacks have a summed (not amplified) rounding envelope.** When every layer is
non-expansive, the network envelope is at most the sum of the per-layer rounding bounds; the
amplifying downstream product is `≤ 1`. -/
lemma envBound_le_sum_rnd_of_nonexpansive [Nonempty V] {Ls : List (ExecLayer V)}
    (h : ∀ L ∈ Ls, L.lip ≤ 1) : envBound Ls ≤ (Ls.map (·.rnd)).sum := by
  induction Ls with
  | nil => simp [envBound]
  | cons L Ls ih =>
      have htaillip : ∀ L' ∈ Ls, L'.lip ≤ 1 := fun L' hL' => h L' (List.mem_cons_of_mem _ hL')
      have htailprod : lipProd Ls ≤ 1 := lipProd_le_one_of_nonexpansive htaillip
      have hrndnn : 0 ≤ L.rnd := L.rnd_nonneg
      have IH : envBound Ls ≤ (Ls.map (·.rnd)).sum := ih htaillip
      have h1 : L.rnd * lipProd Ls ≤ L.rnd :=
        le_trans (mul_le_mul_of_nonneg_left htailprod hrndnn) (le_of_eq (mul_one _))
      simp only [envBound, List.map_cons, List.sum_cons]
      linarith

/-- **Linear-in-depth envelope under a uniform per-layer rounding bound.** If every layer is
non-expansive and rounds within `ρ`, the network envelope is at most `(#layers) · ρ`: linear in
depth with no exponential blow-up. -/
lemma envBound_le_length_mul_of_nonexpansive [Nonempty V] {Ls : List (ExecLayer V)} {ρ : ℝ}
    (hlip : ∀ L ∈ Ls, L.lip ≤ 1) (hrnd : ∀ L ∈ Ls, L.rnd ≤ ρ) :
    envBound Ls ≤ Ls.length * ρ := by
  induction Ls with
  | nil => simp [envBound]
  | cons L Ls ih =>
      have hLrnd : L.rnd ≤ ρ := hrnd L List.mem_cons_self
      have hrndnn : 0 ≤ L.rnd := L.rnd_nonneg
      have htaillip : ∀ L' ∈ Ls, L'.lip ≤ 1 := fun L' hL' => hlip L' (List.mem_cons_of_mem _ hL')
      have htailrnd : ∀ L' ∈ Ls, L'.rnd ≤ ρ := fun L' hL' => hrnd L' (List.mem_cons_of_mem _ hL')
      have htailprod : lipProd Ls ≤ 1 := lipProd_le_one_of_nonexpansive htaillip
      have IH : envBound Ls ≤ Ls.length * ρ := ih htaillip htailrnd
      have h1 : L.rnd * lipProd Ls ≤ ρ :=
        le_trans (le_trans (mul_le_mul_of_nonneg_left htailprod hrndnn) (le_of_eq (mul_one _))) hLrnd
      simp only [envBound, List.length_cons, Nat.cast_add, Nat.cast_one]
      have hexp : ((Ls.length : ℝ) + 1) * ρ = Ls.length * ρ + ρ := by ring
      rw [hexp]; linarith

/-- **The executed forward is within `(#layers)·ρ` of the ideal for non-expansive stacks.** The
depth-uniform-rounding correction is linear in depth when every layer satisfies `lip ≤ 1`. -/
theorem execComp_envelope_linear [Nonempty V] {Ls : List (ExecLayer V)} {ρ : ℝ}
    (hlip : ∀ L ∈ Ls, L.lip ≤ 1) (hrnd : ∀ L ∈ Ls, L.rnd ≤ ρ) (x : V) :
    dist (execComp Ls x) (idealComp Ls x) ≤ Ls.length * ρ :=
  le_trans (execComp_envelope Ls x) (envBound_le_length_mul_of_nonexpansive hlip hrnd)

/-- **Linear-in-depth executed risk transfer.** For an `Lℓ`-Lipschitz loss and a non-expansive stack
with uniform per-layer rounding `ρ`, the executed expected risk is within `Lℓ·(#layers)·ρ` of the
ideal; the correction grows linearly in depth. -/
theorem execComp_risk_transfer_linear [Nonempty V] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Ls : List (ExecLayer V)} {ρ : ℝ}
    (hlip : ∀ L ∈ Ls, L.lip ≤ 1) (hrnd : ∀ L ∈ Ls, L.rnd ≤ ρ)
    (input : Ω → V) (ℓ : V → ℝ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ)
    (hLip : ∀ p q, |ℓ p - ℓ q| ≤ Lℓ * dist p q)
    (hintF : Integrable (fun x => ℓ (idealComp Ls (input x))) μ)
    (hintG : Integrable (fun x => ℓ (execComp Ls (input x))) μ) :
    |(∫ x, ℓ (execComp Ls (input x)) ∂μ) - (∫ x, ℓ (idealComp Ls (input x)) ∂μ)|
      ≤ Lℓ * (Ls.length * ρ) :=
  le_trans (execComp_risk_transfer Ls input ℓ hLℓ0 hLip hintF hintG)
    (mul_le_mul_of_nonneg_left (envBound_le_length_mul_of_nonexpansive hlip hrnd) hLℓ0)

/-- A non-expansive executed layer with a genuine rounding bound `ρ`: any `1`-Lipschitz ideal map
paired with an executed map within `ρ`. The `(#layers)·ρ` envelope is inhabited by layers with nonzero
rounding, so the bound is non-trivial and tight in `ρ`. -/
def nonexpansiveExecLayer (ideal exec : V → V) (ρ : ℝ)
    (hlip : ∀ a b, dist (ideal a) (ideal b) ≤ dist a b)
    (hclose : ∀ y, dist (exec y) (ideal y) ≤ ρ) : ExecLayer V where
  ideal := ideal
  exec := exec
  lip := 1
  rnd := ρ
  lip_nonneg := zero_le_one
  ideal_lip := fun a b => by rw [one_mul]; exact hlip a b
  exec_close := hclose

@[simp] lemma nonexpansiveExecLayer_lip (ideal exec : V → V) (ρ : ℝ)
    (hlip : ∀ a b, dist (ideal a) (ideal b) ≤ dist a b)
    (hclose : ∀ y, dist (exec y) (ideal y) ≤ ρ) :
    (nonexpansiveExecLayer ideal exec ρ hlip hclose).lip = 1 := rfl

/-- **Replicated non-expansive stack.** A depth-`Ln` stack of identical non-expansive layers each
rounding within `ρ` has executed-vs-ideal forward error `≤ Ln·ρ`: linear in depth and tight in `ρ`. -/
theorem replicate_nonexpansive_envelope_linear [Nonempty V]
    (E : ExecLayer V) (hE : E.lip ≤ 1) {ρ : ℝ} (hEρ : E.rnd ≤ ρ) (Ln : ℕ) (x : V) :
    dist (execComp (List.replicate Ln E) x) (idealComp (List.replicate Ln E) x) ≤ Ln * ρ := by
  have hlip : ∀ L ∈ List.replicate Ln E, L.lip ≤ 1 := by
    intro L hL; rw [List.eq_of_mem_replicate hL]; exact hE
  have hrnd : ∀ L ∈ List.replicate Ln E, L.rnd ≤ ρ := by
    intro L hL; rw [List.eq_of_mem_replicate hL]; exact hEρ
  calc dist (execComp (List.replicate Ln E) x) (idealComp (List.replicate Ln E) x)
      ≤ (List.replicate Ln E).length * ρ := execComp_envelope_linear hlip hrnd x
    _ = Ln * ρ := by rw [List.length_replicate]

section MachineEps

variable {E : Type*} [NormedAddCommGroup E]

/-- A non-expansive executed layer whose ideal map has **bounded image** (`‖ideal y‖ ≤ R`) and whose
executed map rounds *relatively* (`dist (exec y) (ideal y) ≤ u·‖ideal y‖`, with `u` the unit roundoff):
the absolute per-layer rounding is then uniformly `≤ u·R`. The image bound is the post-norm reset,
layer normalization caps the signal, so relative rounding becomes a uniform absolute bound that does
*not* grow with the upstream activation norm. -/
def boundedRelRoundExecLayer (ideal exec : E → E) (u R : ℝ) (hu : 0 ≤ u)
    (hlip : ∀ a b, dist (ideal a) (ideal b) ≤ dist a b) (himg : ∀ y, ‖ideal y‖ ≤ R)
    (hrel : ∀ y, dist (exec y) (ideal y) ≤ u * ‖ideal y‖) : ExecLayer E where
  ideal := ideal
  exec := exec
  lip := 1
  rnd := u * R
  lip_nonneg := zero_le_one
  ideal_lip := fun a b => by rw [one_mul]; exact hlip a b
  exec_close := fun y => le_trans (hrel y) (mul_le_mul_of_nonneg_left (himg y) hu)

/-- **Machine-epsilon × depth envelope.** A depth-`Ln` stack of identical bounded-output, relatively
rounded, non-expansive layers has executed-vs-ideal forward error `≤ Ln·(u·R)`: linear in depth and
proportional to the unit roundoff `u`, hence non-vacuous for any realistic depth (`Ln ≲ 1/(u·R)`).
The per-layer scale is the machine epsilon times the post-norm signal cap `R`. -/
theorem replicate_boundedRelRound_envelope [Nonempty E]
    (ideal exec : E → E) (u R : ℝ) (hu : 0 ≤ u)
    (hlip : ∀ a b, dist (ideal a) (ideal b) ≤ dist a b) (himg : ∀ y, ‖ideal y‖ ≤ R)
    (hrel : ∀ y, dist (exec y) (ideal y) ≤ u * ‖ideal y‖) (Ln : ℕ) (x : E) :
    dist (execComp (List.replicate Ln
            (boundedRelRoundExecLayer ideal exec u R hu hlip himg hrel)) x)
         (idealComp (List.replicate Ln
            (boundedRelRoundExecLayer ideal exec u R hu hlip himg hrel)) x)
      ≤ Ln * (u * R) :=
  replicate_nonexpansive_envelope_linear
    (boundedRelRoundExecLayer ideal exec u R hu hlip himg hrel)
    (by simp [boundedRelRoundExecLayer]) (ρ := u * R)
    (by simp [boundedRelRoundExecLayer]) Ln x

end MachineEps

section Concrete

variable {n d : ℕ}

/-- The coordinatewise activation clamp (`clampExecLayer`, the executed-forward reset) is
non-expansive: `lip = 1`. Reset layers populate the non-expansive class to which the linear envelope
applies. -/
lemma clampExecLayer_nonexpansive (ρ : ℝ) :
    (clampExecLayer ρ : ExecLayer (Fin n → Fin d → ℝ)).lip ≤ 1 := by
  simp [clampExecLayer]

/-- **The post-norm multi-head block is non-expansive exactly in the certified-non-expansive regime.**
Its input-Lipschitz constant is `K = Cγ·(2√d+2)/√ε · (1 + L_mha)` with
`L_mha = H·(2·bV·(d·B/scale)·(2·γW) + γW)`. When `K ≤ 1` (small `‖γ‖`, residual scaling, or large `ε`),
the block contracts (`dist (block Xa) (block Xb) ≤ dist Xa Xb`), so a stack of such blocks satisfies
the linear-envelope hypothesis `lip ≤ 1` and the correction grows linearly in depth. The constant `K`
is `> 1` for typical regularizers `ε`, which is the source of the generic envelope's exponential depth
dependence; `K ≤ 1` is the sharp condition that removes it. -/
lemma normMultiHeadBlock_nonexpansive {H : ℕ} [NeZero n] (hd : 0 < d) {scale B bV γW : ℝ}
    (hscale : 0 < scale) (hB : 0 ≤ B) (hbV0 : 0 ≤ bV) (hγW0 : 0 ≤ γW)
    (WQ WK WVO : Fin H → Fin d → Fin d → ℝ)
    (hγWQ : ∀ h j, (∑ k, |WQ h k j|) ≤ γW) (hγWK : ∀ h j, (∑ k, |WK h k j|) ≤ γW)
    (hγWVO : ∀ h j, (∑ k, |WVO h k j|) ≤ γW) (γ β : Fin d → ℝ) {Cγ : ℝ} (hCγ : ∀ j, |γ j| ≤ Cγ)
    (Xa Xb : Fin n → Fin d → ℝ) (hQXb : ∀ h i e, |matMulCoord (WQ h) Xb i e| ≤ B)
    (hKXa : ∀ h k' e, |matMulCoord (WK h) Xa k' e| ≤ B) (hVXa : ∀ h j, ‖matMulCoord (WVO h) Xa j‖ ≤ bV)
    (hK : Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon
            * (1 + (H : ℝ) * (2 * bV * ((d : ℝ) * B / scale) * (2 * γW) + γW)) ≤ 1) :
    dist (normAttnCoord γ β (multiHeadAttn scale WQ WK WVO) Xa)
         (normAttnCoord γ β (multiHeadAttn scale WQ WK WVO) Xb) ≤ dist Xa Xb := by
  refine le_trans (normMultiHeadBlock_input_lip hd hscale hB hbV0 hγW0 WQ WK WVO
    hγWQ hγWK hγWVO γ β hCγ Xa Xb hQXb hKXa hVXa) ?_
  have h := mul_le_mul_of_nonneg_right hK (dist_nonneg : (0:ℝ) ≤ dist Xa Xb)
  rwa [one_mul] at h

/-- **The post-norm multi-head block has uniformly bounded output.** Layer normalization caps every
output coordinate at `√d·Cγ + Cβ` regardless of the input, so the block's image lies in that ball no
matter how large the upstream activation norm. This supplies the bounded signal scale `R` that makes
the per-layer rounding `≤ u·R` in `replicate_boundedRelRound_envelope`, giving depth-`L` error
`≤ L·u·(√d·Cγ + Cβ)` for a non-expansive (`K ≤ 1`), relatively rounded tied block stack. -/
lemma normMultiHeadBlock_image_le {H : ℕ} (hd : 0 < d) (γ β : Fin d → ℝ) {Cγ Cβ : ℝ}
    (hCγ : ∀ j, |γ j| ≤ Cγ) (hCβ : ∀ j, |β j| ≤ Cβ) {scale : ℝ}
    (WQ WK WVO : Fin H → Fin d → Fin d → ℝ) (X : Fin n → Fin d → ℝ) :
    ‖normAttnCoord γ β (multiHeadAttn scale WQ WK WVO) X‖ ≤ Real.sqrt d * Cγ + Cβ := by
  rw [normAttnCoord]
  exact layerNormCoord_norm_le hd γ β hCγ hCβ _

end Concrete

end TLT
