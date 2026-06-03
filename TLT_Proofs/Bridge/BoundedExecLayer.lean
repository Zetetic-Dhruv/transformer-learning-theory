/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.ForwardEnvelope
import TLT_Proofs.Bridge.AttentionLipschitz
import TLT_Proofs.Bridge.LayerNormLipschitz

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

/-! ### Layer normalization as a bounded-activation layer

Layer normalization maps the whole activation space into the ball of radius `√d·Cγ + Cβ`
(`layerNormCoord_norm_le`) and is globally Lipschitz there (`layerNormCoord_lipschitz`), so it is an
`ExecLayer` over that ball — the *same* kind of bounded domain on which self-attention lives. This is
what re-establishes a forward-invariant activation domain after norm-growing linear maps, and lets a
layer-norm-terminated block be a self-map of one fixed activation ball. -/

section LayerNorm

variable {s d : ℕ}

/-- **Layer normalization is a bounded-activation `ExecLayer`.** Over `↥(closedBall 0 (√d·Cγ+Cβ))` —
forward-invariance from `layerNormCoord_norm_le`, the `Cγ·(2√d+2)/√ε` Lipschitz constant from
`layerNormCoord_lipschitz`. The executed (rounded) map and its uniform rounding bound are supplied as
data. -/
noncomputable def layerNormExecLayer (hd : 0 < d) (γ β : Fin d → ℝ) {Cγ Cβ : ℝ}
    (hCγ : ∀ j, |γ j| ≤ Cγ) (hCβ : ∀ j, |β j| ≤ Cβ)
    (execMap : (Fin s → Fin d → ℝ) → (Fin s → Fin d → ℝ)) (rnd : ℝ)
    (hexecinv : ∀ X ∈ Metric.closedBall (0 : Fin s → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
        execMap X ∈ Metric.closedBall 0 (Real.sqrt d * Cγ + Cβ))
    (hrnd : ∀ X ∈ Metric.closedBall (0 : Fin s → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ),
        dist (execMap X) (layerNormCoord γ β X) ≤ rnd) :
    ExecLayer (↥(Metric.closedBall (0 : Fin s → Fin d → ℝ) (Real.sqrt d * Cγ + Cβ))) :=
  execLayerOfForwardInvariant (Metric.closedBall 0 (Real.sqrt d * Cγ + Cβ)) (layerNormCoord γ β)
    execMap (Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon) rnd
    (by
      have hCγ0 : 0 ≤ Cγ := le_trans (abs_nonneg _) (hCγ ⟨0, hd⟩)
      exact div_nonneg (mul_nonneg hCγ0 (by positivity)) (Real.sqrt_nonneg _))
    (fun X _ => by
      rw [mem_closedBall_zero_iff]; exact layerNormCoord_norm_le hd γ β hCγ hCβ X)
    hexecinv
    (fun a _ b _ => layerNormCoord_lipschitz hd γ β hCγ a b)
    hrnd

end LayerNorm

/-! ### The coordinatewise clamp onto the activation ball

In the supremum norm the metric projection onto the ball `{‖x‖ ≤ B}` is the coordinatewise clamp onto
`[-B, B]`. It is `1`-Lipschitz, lands in the ball, and is the identity on the ball — so a network that
clamps its activations to the certified region `K = {‖x‖ ≤ B}` agrees with the unclamped network on
all of `K`, while being globally bounded and (composed with attention) globally Lipschitz. This is
what lets the bounded-domain attention estimates close the forward map over the *whole* space. -/

section Clamp

variable {s d : ℕ}

/-- Coordinatewise clamp onto `[-B, B]`: the metric projection onto the supremum-norm ball of radius
`B`. -/
def clampCoord (B : ℝ) (X : Fin s → Fin d → ℝ) : Fin s → Fin d → ℝ :=
  fun i j => max (min (X i j) B) (-B)

/-- The scalar clamp `t ↦ max (min t B) (-B)` is `1`-Lipschitz. -/
lemma lipschitzWith_scalar_clamp (B : ℝ) :
    LipschitzWith 1 (fun t : ℝ => max (min t B) (-B)) :=
  (LipschitzWith.id.min_const B).max_const (-B)

/-- The clamp lands in the ball of radius `B`. -/
lemma clampCoord_norm_le {B : ℝ} (hB : 0 ≤ B) (X : Fin s → Fin d → ℝ) : ‖clampCoord B X‖ ≤ B := by
  refine (pi_norm_le_iff_of_nonneg hB).mpr (fun i => ?_)
  refine (pi_norm_le_iff_of_nonneg hB).mpr (fun j => ?_)
  rw [Real.norm_eq_abs]
  simp only [clampCoord]
  exact abs_le.mpr ⟨le_max_right _ _, max_le (min_le_right _ _) (neg_le_self hB)⟩

/-- The clamp is `1`-Lipschitz (coordinatewise, hence in the supremum norm). -/
lemma clampCoord_lipschitz (B : ℝ) (X Y : Fin s → Fin d → ℝ) :
    dist (clampCoord B X) (clampCoord B Y) ≤ dist X Y := by
  refine (dist_pi_le_iff dist_nonneg).mpr (fun i => ?_)
  refine (dist_pi_le_iff dist_nonneg).mpr (fun j => ?_)
  calc dist (clampCoord B X i j) (clampCoord B Y i j)
      ≤ 1 * dist (X i j) (Y i j) := by
        simpa [clampCoord] using (lipschitzWith_scalar_clamp B).dist_le_mul (X i j) (Y i j)
    _ = dist (X i j) (Y i j) := one_mul _
    _ ≤ dist X Y := le_trans (dist_le_pi_dist (X i) (Y i) j) (dist_le_pi_dist X Y i)

/-- The clamp is the identity on the ball of radius `B`: clamping an activation already in the cap
changes nothing. -/
lemma clampCoord_eq_of_norm_le {B : ℝ} {X : Fin s → Fin d → ℝ} (hX : ‖X‖ ≤ B) :
    clampCoord B X = X := by
  funext i j
  have hxij : |X i j| ≤ B :=
    le_trans (le_trans (le_of_eq (Real.norm_eq_abs _).symm) (norm_le_pi_norm (X i) j))
      (le_trans (norm_le_pi_norm X i) hX)
  rw [abs_le] at hxij
  simp only [clampCoord, min_eq_left hxij.2, max_eq_left hxij.1]

end Clamp

end TLT
