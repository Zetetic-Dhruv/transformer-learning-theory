/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.ForwardEnvelope
import TLT_Proofs.Bridge.AttentionLipschitz

/-!
# Bounded-activation executed layers

`ExecLayer.ideal_lip` is a *global* Lipschitz field: `∀ a b, dist (ideal a) (ideal b) ≤ lip · dist a b`.
Dot-product self-attention has no global Lipschitz constant (its score map is bilinear, so the
Jacobian is unbounded — Kim, Papamakarios and Mnih, ICML 2021), so attention cannot be an `ExecLayer`
over an unbounded activation space.

The resolution carries the input cap in the *type*. A layer that is forward-invariant on a bounded
domain `D` (maps `D` into `D`) and Lipschitz / rounding-controlled *on `D`* is a bona-fide `ExecLayer`
over the metric subtype `↥D`: on the subtype the distance is the ambient distance, so the global
`ideal_lip` field is *exactly* the on-`D` estimate. The certified bound's input cap `K = {‖x‖ ≤ B}`
is then the layer space itself, and the global capstone (`certified_executed_generalization_dudley`)
applies verbatim with `V := ↥D`.

## Main results

- `execLayerOfForwardInvariant` — the bounded-activation `ExecLayer` constructor: on-`D` data
  (invariance + Lipschitz + rounding) yields a global `ExecLayer (↥D)`.

## References

H. Kim, G. Papamakarios and A. Mnih, *The Lipschitz Constant of Self-Attention*, ICML 2021.
-/

namespace TLT

/-- **The bounded-activation `ExecLayer` constructor.** Given a bounded domain `D` on which the ideal
and executed maps are forward-invariant (`hidealinv`, `hexecinv`), the ideal map is `lip`-Lipschitz
(`hlipD`), and the executed map is within `rnd` of the ideal (`hrndD`), the pair is a genuine
`ExecLayer` over the metric subtype `↥D`. Because the subtype distance is the ambient distance, the
*global* `ideal_lip` field of the resulting layer is precisely the on-`D` Lipschitz estimate — this is
what lets a map that is Lipschitz only on a ball (such as attention; Kim et al. 2021) serve as a
certificate-side layer. -/
def execLayerOfForwardInvariant {E : Type*} [PseudoMetricSpace E] (D : Set E)
    (idealMap execMap : E → E) (lip rnd : ℝ) (hlip0 : 0 ≤ lip)
    (hidealinv : ∀ x ∈ D, idealMap x ∈ D) (hexecinv : ∀ x ∈ D, execMap x ∈ D)
    (hlipD : ∀ a ∈ D, ∀ b ∈ D, dist (idealMap a) (idealMap b) ≤ lip * dist a b)
    (hrndD : ∀ y ∈ D, dist (execMap y) (idealMap y) ≤ rnd) :
    ExecLayer (↥D) where
  ideal x := ⟨idealMap x.1, hidealinv x.1 x.2⟩
  exec x := ⟨execMap x.1, hexecinv x.1 x.2⟩
  lip := lip
  rnd := rnd
  lip_nonneg := hlip0
  ideal_lip a b := by simp only [Subtype.dist_eq]; exact hlipD a.1 a.2 b.1 b.2
  exec_close y := by simp only [Subtype.dist_eq]; exact hrndD y.1 y.2

/-! ### Self-attention as a bounded-activation layer

Single-head dot-product self-attention with identity projections, presented as a self-map of the
token-matrix space, demonstrates the constructor end-to-end: it is forward-invariant on the
supremum-norm ball (softmax-convexity) and Lipschitz on that ball (the score map is bilinear, hence
Lipschitz only with the ball cap — Kim et al.), so it is a genuine `ExecLayer` over the ball even
though it has no global Lipschitz constant. -/

section SelfAttention

variable {n d : ℕ}

/-- Single-head dot-product self-attention with identity query/key/value projections, as a self-map of
the token matrix `X : Fin n → Fin d → ℝ`: token `i`'s output row is the softmax (over keys `j`) of the
dot-product scores `⟨X i, X j⟩ / scale`, applied to the value rows `X j`. -/
noncomputable def selfAttn (scale : ℝ) (X : Fin n → Fin d → ℝ) : Fin n → Fin d → ℝ :=
  fun i => attnVec (attnScores scale (X i) X) X

/-- **Self-attention is forward-invariant on the supremum-norm ball.** Each output row is a convex
combination of the value rows (which are the input rows), so it never leaves the ball that contains
the input rows: the radius-`B` ball is exactly invariant. -/
lemma selfAttn_forward_invariant [NeZero n] {scale B : ℝ} (X : Fin n → Fin d → ℝ)
    (hX : ∀ i, ‖X i‖ ≤ B) (i : Fin n) : ‖selfAttn scale X i‖ ≤ B :=
  attnVec_norm_le (attnScores scale (X i) X) X hX

/-- **Self-attention is Lipschitz on the supremum-norm ball.** The bilinear score map is Lipschitz
only under the ball cap (Kim et al. 2021); on the radius-`B` ball the self-attention self-map has the
explicit constant `4·n·d·B²/scale + 1` — finite precisely because of the cap. -/
lemma selfAttn_lipschitz_on_ball [NeZero n] {scale B : ℝ} (hscale : 0 < scale) (hB : 0 ≤ B)
    (X X' : Fin n → Fin d → ℝ) (hX : ∀ i, ‖X i‖ ≤ B) (hX' : ∀ i, ‖X' i‖ ≤ B) :
    ‖selfAttn scale X - selfAttn scale X'‖
      ≤ (4 * n * (d * B ^ 2 / scale) + 1) * ‖X - X'‖ := by
  have hL0 : (0:ℝ) ≤ 4 * n * (d * B ^ 2 / scale) + 1 := by
    have : (0:ℝ) ≤ 4 * n * (d * B ^ 2 / scale) :=
      mul_nonneg (by positivity) (div_nonneg (by positivity) hscale.le)
    linarith
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hL0 (norm_nonneg _))).mpr (fun i => ?_)
  rw [Pi.sub_apply]
  have hrow : ‖X i - X' i‖ ≤ ‖X - X'‖ := by
    rw [show X i - X' i = (X - X') i from rfl]; exact norm_le_pi_norm (X - X') i
  have hcoef : (0:ℝ) ≤ 2 * n * B * (d * B / scale) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hB)
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) hscale.le)
  calc ‖selfAttn scale X i - selfAttn scale X' i‖
      ≤ 2 * n * B * (d * B / scale) * (‖X i - X' i‖ + ‖X - X'‖) + ‖X - X'‖ :=
        attnVec_lipschitz_on_ball hscale hB hB (X i) (X' i) X X' X X'
          (fun e => le_trans (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (X' i) e) (hX' i))
          (fun k' e => le_trans (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (X k') e) (hX k'))
          hX
    _ ≤ 2 * n * B * (d * B / scale) * (‖X - X'‖ + ‖X - X'‖) + ‖X - X'‖ := by
        have := mul_le_mul_of_nonneg_left (add_le_add_right hrow ‖X - X'‖) hcoef
        linarith
    _ = (4 * n * (d * B ^ 2 / scale) + 1) * ‖X - X'‖ := by ring

/-- **Self-attention is a bounded-activation `ExecLayer`.** Dot-product self-attention has no global
Lipschitz constant, yet on the radius-`B` ball it is forward-invariant (softmax-convexity) and
Lipschitz (constant `4·n·d·B²/scale + 1`); so — via `execLayerOfForwardInvariant` — it is a genuine
`ExecLayer` over the ball `↥(closedBall 0 B)`, ready to sit in the certificate-side layer list of the
generalization capstone. The executed (rounded) map, its forward-invariance, and its uniform on-ball
rounding bound `rnd` are supplied as data — the float32 instantiation provides them. -/
noncomputable def selfAttnExecLayer [NeZero n] {scale B : ℝ} (hscale : 0 < scale) (hB : 0 ≤ B)
    (execMap : (Fin n → Fin d → ℝ) → (Fin n → Fin d → ℝ)) (rnd : ℝ)
    (hexecinv : ∀ X ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) B, execMap X ∈ Metric.closedBall 0 B)
    (hrnd : ∀ X ∈ Metric.closedBall (0 : Fin n → Fin d → ℝ) B,
        dist (execMap X) (selfAttn scale X) ≤ rnd) :
    ExecLayer (↥(Metric.closedBall (0 : Fin n → Fin d → ℝ) B)) :=
  execLayerOfForwardInvariant (Metric.closedBall 0 B) (selfAttn scale) execMap
    (4 * n * (d * B ^ 2 / scale) + 1) rnd
    (by
      have h : (0:ℝ) ≤ 4 * n * (d * B ^ 2 / scale) :=
        mul_nonneg (by positivity) (div_nonneg (by positivity) hscale.le)
      linarith)
    (fun X hX => by
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hB]
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hB] at hX
      exact fun i => selfAttn_forward_invariant X hX i)
    hexecinv
    (fun a ha b hb => by
      rw [dist_eq_norm, dist_eq_norm]
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hB] at ha hb
      exact selfAttn_lipschitz_on_ball hscale hB a b ha hb)
    hrnd

end SelfAttention

end TLT
