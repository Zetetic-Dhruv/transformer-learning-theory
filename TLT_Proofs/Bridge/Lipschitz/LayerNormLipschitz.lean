/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Forward.ForwardContinuity
import Mathlib.Algebra.Order.Chebyshev

/-!
# The Lipschitz constant of layer normalization

Layer normalization centers each row, divides by the regularized standard deviation
`σ = √(var + ε)`, and applies an affine `γ, β`. With the verified positive regularizer `ε`
(`Numbers.epsilon = 1e-6`) flooring the standard deviation at `√ε`, the map is **globally** Lipschitz
in the input, unlike self-attention, which is Lipschitz only on a bounded domain.

The constant is `(sup|γ|)·(2√d + 2)/√ε`. The crux is that the standard deviation is globally
`2`-Lipschitz: `|var X − var Y| ≤ 2·dist(X,Y)·(σ_X + σ_Y)`, and the `(σ_X + σ_Y)` cancels against the
`√` difference quotient, so no `ε`/`d` blowup appears there; the `1/√ε` enters only through the final
`1/σ ≤ 1/√ε` quotient. The normalized output is bounded by `√d` (`aⱼ² ≤ ∑ₖ aₖ² = d·var ≤ d·σ²`).

## Main results

- `rowStdCoord_dist_le`: the per-row standard deviation is `2`-Lipschitz in the input.
- `layerNormCoord_lipschitz`: layer normalization is `(sup|γ|)·(2√d + 2)/√ε`-Lipschitz.
-/

/-!
## References
- [28] LayerNorm; [37] globally Lipschitz / √d output bound (ellipsoid∩hyperplane); LayerNorm-
  Lipschitz `≤ 1/σ ≤ 1/√ε` (normalization-layer literature); std 2-Lipschitz, variance-perturbation.
-/

open scoped BigOperators

namespace TLT

variable {s d : ℕ}

/-- A single entry difference is bounded by the sup-metric distance. -/
lemma abs_sub_le_dist (X Y : Fin s → Fin d → ℝ) (i : Fin s) (j : Fin d) :
    |X i j - Y i j| ≤ dist X Y :=
  calc |X i j - Y i j| = dist (X i j) (Y i j) := (Real.dist_eq _ _).symm
    _ ≤ dist (X i) (Y i) := dist_le_pi_dist (X i) (Y i) j
    _ ≤ dist X Y := dist_le_pi_dist X Y i

/-- The regularized standard deviation is at least `√ε` (the verified positive regularizer floors the
denominator). -/
lemma rowStdCoord_ge_sqrt_eps (i : Fin s) (X : Fin s → Fin d → ℝ) :
    Real.sqrt Numbers.epsilon ≤ rowStdCoord i X := by
  unfold rowStdCoord
  apply Real.sqrt_le_sqrt
  have := le_max_right (rowVarCoord i X) 0
  linarith

/-- The per-row mean is `1`-Lipschitz in the input. -/
lemma rowMeanCoord_dist_le (hd : 0 < d) (i : Fin s) (X Y : Fin s → Fin d → ℝ) :
    |rowMeanCoord i X - rowMeanCoord i Y| ≤ dist X Y := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have heq : rowMeanCoord i X - rowMeanCoord i Y = (∑ k, (X i k - Y i k)) / (d : ℝ) := by
    simp only [rowMeanCoord, div_sub_div_same, ← Finset.sum_sub_distrib]
  rw [heq, abs_div, abs_of_pos hd', div_le_iff₀ hd']
  calc |∑ k, (X i k - Y i k)| ≤ ∑ k, |X i k - Y i k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k, dist X Y := Finset.sum_le_sum (fun k _ => abs_sub_le_dist X Y i k)
    _ = dist X Y * (d : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The centered entry is `2`-Lipschitz in the input (the entry plus the `1`-Lipschitz mean). -/
lemma centered_dist_le (hd : 0 < d) (i : Fin s) (j : Fin d) (X Y : Fin s → Fin d → ℝ) :
    |(X i j - rowMeanCoord i X) - (Y i j - rowMeanCoord i Y)| ≤ 2 * dist X Y := by
  have h1 := abs_sub_le_dist X Y i j
  have h2 := rowMeanCoord_dist_le hd i X Y
  calc |(X i j - rowMeanCoord i X) - (Y i j - rowMeanCoord i Y)|
      = |(X i j - Y i j) - (rowMeanCoord i X - rowMeanCoord i Y)| := by ring_nf
    _ ≤ |X i j - Y i j| + |rowMeanCoord i X - rowMeanCoord i Y| := abs_sub _ _
    _ ≤ 2 * dist X Y := by linarith

/-- The sum of squared centered entries is `d` times the variance. -/
lemma sum_sq_centered_eq (hd : 0 < d) (i : Fin s) (X : Fin s → Fin d → ℝ) :
    ∑ k, (X i k - rowMeanCoord i X) ^ 2 = (d : ℝ) * rowVarCoord i X := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [rowVarCoord]; field_simp

/-- The variance is at most the squared regularized standard deviation. -/
lemma rowVarCoord_le_sq_std (i : Fin s) (X : Fin s → Fin d → ℝ) :
    rowVarCoord i X ≤ rowStdCoord i X ^ 2 := by
  have hε := numbers_epsilon_real_pos
  have hmax := le_max_right (rowVarCoord i X) 0
  rw [rowStdCoord, Real.sq_sqrt (by linarith [le_max_left (rowVarCoord i X) 0])]
  linarith [le_max_left (rowVarCoord i X) 0]

/-- A centered entry is at most `√d · σ` (the normalized output is bounded by `√d`). -/
lemma abs_centered_le_sqrt_d_mul_std (hd : 0 < d) (i : Fin s) (j : Fin d) (X : Fin s → Fin d → ℝ) :
    |X i j - rowMeanCoord i X| ≤ Real.sqrt d * rowStdCoord i X := by
  have hstd0 : 0 ≤ rowStdCoord i X := (rowStdCoord_pos i X).le
  have hsq : (X i j - rowMeanCoord i X) ^ 2 ≤ (Real.sqrt d * rowStdCoord i X) ^ 2 := by
    have h1 : (X i j - rowMeanCoord i X) ^ 2 ≤ ∑ k, (X i k - rowMeanCoord i X) ^ 2 :=
      Finset.single_le_sum (f := fun k => (X i k - rowMeanCoord i X) ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    rw [sum_sq_centered_eq hd i X] at h1
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    exact h1.trans (mul_le_mul_of_nonneg_left (rowVarCoord_le_sq_std i X) (Nat.cast_nonneg d))
  calc |X i j - rowMeanCoord i X|
      = Real.sqrt ((X i j - rowMeanCoord i X) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((Real.sqrt d * rowStdCoord i X) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt d * rowStdCoord i X := Real.sqrt_sq (by positivity)

/-- The sum of absolute centered entries is at most `d · σ` (Cauchy–Schwarz). -/
lemma sum_abs_centered_le (hd : 0 < d) (i : Fin s) (X : Fin s → Fin d → ℝ) :
    ∑ k, |X i k - rowMeanCoord i X| ≤ (d : ℝ) * rowStdCoord i X := by
  have hstd0 : 0 ≤ rowStdCoord i X := (rowStdCoord_pos i X).le
  have hsq : (∑ k, |X i k - rowMeanCoord i X|) ^ 2 ≤ ((d : ℝ) * rowStdCoord i X) ^ 2 := by
    calc (∑ k, |X i k - rowMeanCoord i X|) ^ 2
        ≤ (d : ℝ) * ∑ k, |X i k - rowMeanCoord i X| ^ 2 := by
          have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
            (f := fun k => |X i k - rowMeanCoord i X|)
          simpa [Finset.card_univ, Fintype.card_fin] using h
      _ = (d : ℝ) * ((d : ℝ) * rowVarCoord i X) := by
          simp only [sq_abs]; rw [sum_sq_centered_eq hd i X]
      _ ≤ (d : ℝ) * ((d : ℝ) * rowStdCoord i X ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (rowVarCoord_le_sq_std i X) (Nat.cast_nonneg d))
            (Nat.cast_nonneg d)
      _ = ((d : ℝ) * rowStdCoord i X) ^ 2 := by ring
  calc ∑ k, |X i k - rowMeanCoord i X|
      = Real.sqrt ((∑ k, |X i k - rowMeanCoord i X|) ^ 2) :=
        (Real.sqrt_sq (Finset.sum_nonneg (fun k _ => abs_nonneg _))).symm
    _ ≤ Real.sqrt (((d : ℝ) * rowStdCoord i X) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = (d : ℝ) * rowStdCoord i X := Real.sqrt_sq (by positivity)

/-- The variance difference is controlled by `2·dist·(σ_X + σ_Y)`, the factor that cancels the `√`
difference quotient. -/
lemma rowVarCoord_dist_le (hd : 0 < d) (i : Fin s) (X Y : Fin s → Fin d → ℝ) :
    |rowVarCoord i X - rowVarCoord i Y|
      ≤ 2 * dist X Y * (rowStdCoord i X + rowStdCoord i Y) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have heq : rowVarCoord i X - rowVarCoord i Y
      = (∑ k, ((X i k - rowMeanCoord i X) ^ 2 - (Y i k - rowMeanCoord i Y) ^ 2)) / (d : ℝ) := by
    simp only [rowVarCoord, div_sub_div_same, ← Finset.sum_sub_distrib]
  rw [heq, abs_div, abs_of_pos hd', div_le_iff₀ hd']
  calc |∑ k, ((X i k - rowMeanCoord i X) ^ 2 - (Y i k - rowMeanCoord i Y) ^ 2)|
      ≤ ∑ k, |(X i k - rowMeanCoord i X) ^ 2 - (Y i k - rowMeanCoord i Y) ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, 2 * dist X Y * (|X i k - rowMeanCoord i X| + |Y i k - rowMeanCoord i Y|) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [show (X i k - rowMeanCoord i X) ^ 2 - (Y i k - rowMeanCoord i Y) ^ 2
              = ((X i k - rowMeanCoord i X) - (Y i k - rowMeanCoord i Y))
                * ((X i k - rowMeanCoord i X) + (Y i k - rowMeanCoord i Y)) by ring, abs_mul]
        exact mul_le_mul (centered_dist_le hd i k X Y) (abs_add_le _ _) (abs_nonneg _) (by positivity)
    _ = 2 * dist X Y * (∑ k, |X i k - rowMeanCoord i X| + ∑ k, |Y i k - rowMeanCoord i Y|) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 * dist X Y * ((d : ℝ) * rowStdCoord i X + (d : ℝ) * rowStdCoord i Y) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (sum_abs_centered_le hd i X) (sum_abs_centered_le hd i Y)) (by positivity)
    _ = 2 * dist X Y * (rowStdCoord i X + rowStdCoord i Y) * (d : ℝ) := by ring

/-- **The standard deviation is globally 2-Lipschitz.** The `(σ_X + σ_Y)` from the variance bound
cancels the `√` difference quotient, so no `ε`/`d` blowup appears. -/
lemma rowStdCoord_dist_le (hd : 0 < d) (i : Fin s) (X Y : Fin s → Fin d → ℝ) :
    |rowStdCoord i X - rowStdCoord i Y| ≤ 2 * dist X Y := by
  have hsum_pos : 0 < rowStdCoord i X + rowStdCoord i Y :=
    add_pos (rowStdCoord_pos i X) (rowStdCoord_pos i Y)
  have hX : rowStdCoord i X ^ 2 = max (rowVarCoord i X) 0 + Numbers.epsilon := by
    rw [rowStdCoord,
      Real.sq_sqrt (by linarith [le_max_right (rowVarCoord i X) 0, numbers_epsilon_real_pos])]
  have hY : rowStdCoord i Y ^ 2 = max (rowVarCoord i Y) 0 + Numbers.epsilon := by
    rw [rowStdCoord,
      Real.sq_sqrt (by linarith [le_max_right (rowVarCoord i Y) 0, numbers_epsilon_real_pos])]
  have hsq : |rowStdCoord i X - rowStdCoord i Y| * (rowStdCoord i X + rowStdCoord i Y)
      = |max (rowVarCoord i X) 0 - max (rowVarCoord i Y) 0| := by
    rw [← abs_of_pos hsum_pos, ← abs_mul]
    congr 1
    linear_combination hX - hY
  have key : |rowStdCoord i X - rowStdCoord i Y| * (rowStdCoord i X + rowStdCoord i Y)
      ≤ 2 * dist X Y * (rowStdCoord i X + rowStdCoord i Y) := by
    rw [hsq]
    exact le_trans (abs_max_sub_max_le_abs _ _ _) (rowVarCoord_dist_le hd i X Y)
  exact le_of_mul_le_mul_right key hsum_pos

/-- The normalized-difference quotient bound: `|aX/σX − aY/σY| ≤ (2·sd + 2)/ε · D`, from the bounded
normalized output (`|aX| ≤ sd·σX`), the centered difference (`|aX−aY| ≤ 2D`), the `σ` difference
(`|σX−σY| ≤ 2D`), and the floor `ε ≤ σY`. The `1/√ε` enters only here, through `1/σ ≤ 1/ε`. -/
lemma normalized_diff_bound {aX aY σX σY sd ε D : ℝ} (hσX : 0 < σX) (hσY : 0 < σY) (hε : 0 < ε)
    (hσY_ge : ε ≤ σY) (haX : |aX| ≤ sd * σX) (hsd0 : 0 ≤ sd) (hadiff : |aX - aY| ≤ 2 * D)
    (hσdiff : |σX - σY| ≤ 2 * D) (hD0 : 0 ≤ D) :
    |aX / σX - aY / σY| ≤ (2 * sd + 2) / ε * D := by
  have hterm2 : |aX / σY - aY / σY| ≤ 2 * D / ε := by
    rw [div_sub_div_same, abs_div, abs_of_pos hσY]; gcongr
  have hterm1 : |aX / σX - aX / σY| ≤ sd * (2 * D / ε) := by
    have he : aX / σX - aX / σY = aX / σX * ((σY - σX) / σY) := by field_simp
    rw [he, abs_mul]
    have h1 : |aX / σX| ≤ sd := by rw [abs_div, abs_of_pos hσX, div_le_iff₀ hσX]; exact haX
    have h2 : |(σY - σX) / σY| ≤ 2 * D / ε := by
      rw [abs_div, abs_of_pos hσY, abs_sub_comm]; gcongr
    exact mul_le_mul h1 h2 (abs_nonneg _) hsd0
  calc |aX / σX - aY / σY|
      ≤ |aX / σX - aX / σY| + |aX / σY - aY / σY| := by
        rw [show aX / σX - aY / σY = (aX / σX - aX / σY) + (aX / σY - aY / σY) by ring]
        exact abs_add_le _ _
    _ ≤ sd * (2 * D / ε) + 2 * D / ε := add_le_add hterm1 hterm2
    _ = (2 * sd + 2) / ε * D := by ring

/-- **Layer normalization is globally Lipschitz.** With `Cγ` an upper bound on `|γ|`, the coordinate
layer-norm map is `Cγ·(2√d + 2)/√ε`-Lipschitz in the input, a finite global constant in contrast to
self-attention. The `√ε` is the verified regularizer's square-root floor on the standard deviation. -/
theorem layerNormCoord_lipschitz (hd : 0 < d) (γ β : Fin d → ℝ) {Cγ : ℝ} (hCγ : ∀ j, |γ j| ≤ Cγ)
    (X Y : Fin s → Fin d → ℝ) :
    dist (layerNormCoord γ β X) (layerNormCoord γ β Y)
      ≤ Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon * dist X Y := by
  have hCγ0 : 0 ≤ Cγ := le_trans (abs_nonneg _) (hCγ ⟨0, hd⟩)
  have hepspos : 0 < Real.sqrt Numbers.epsilon := Real.sqrt_pos.mpr numbers_epsilon_real_pos
  refine (dist_pi_le_iff (by positivity)).mpr
    (fun i => (dist_pi_le_iff (by positivity)).mpr (fun j => ?_))
  rw [Real.dist_eq]
  have hlnc : layerNormCoord γ β X i j - layerNormCoord γ β Y i j
      = ((X i j - rowMeanCoord i X) / rowStdCoord i X
          - (Y i j - rowMeanCoord i Y) / rowStdCoord i Y) * γ j := by
    simp only [layerNormCoord]; ring
  rw [hlnc, abs_mul]
  have hn := normalized_diff_bound (rowStdCoord_pos i X) (rowStdCoord_pos i Y) hepspos
    (rowStdCoord_ge_sqrt_eps i Y) (abs_centered_le_sqrt_d_mul_std hd i j X) (Real.sqrt_nonneg _)
    (centered_dist_le hd i j X Y) (rowStdCoord_dist_le hd i X Y) dist_nonneg
  calc |(X i j - rowMeanCoord i X) / rowStdCoord i X
          - (Y i j - rowMeanCoord i Y) / rowStdCoord i Y| * |γ j|
      ≤ (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon * dist X Y * Cγ :=
        mul_le_mul hn (hCγ j) (abs_nonneg _) (by positivity)
    _ = Cγ * (2 * Real.sqrt d + 2) / Real.sqrt Numbers.epsilon * dist X Y := by ring

/-- **Layer normalization has bounded output.** Each normalized entry `(Xᵢⱼ − meanᵢ)/σᵢ` has magnitude
at most `√d` (`abs_centered_le_sqrt_d_mul_std`), so every output coordinate is at most `√d·Cγ + Cβ` in
absolute value, and the output supremum-norm is bounded *uniformly in the input*. This is the
forward-invariance enabler: layer-norm maps the whole activation space into the ball of radius
`√d·Cγ + Cβ`, re-establishing a bounded activation domain no matter how far upstream linear maps have
grown the norm. -/
lemma layerNormCoord_norm_le (hd : 0 < d) (γ β : Fin d → ℝ) {Cγ Cβ : ℝ}
    (hCγ : ∀ j, |γ j| ≤ Cγ) (hCβ : ∀ j, |β j| ≤ Cβ) (X : Fin s → Fin d → ℝ) :
    ‖layerNormCoord γ β X‖ ≤ Real.sqrt d * Cγ + Cβ := by
  have hCγ0 : 0 ≤ Cγ := le_trans (abs_nonneg _) (hCγ ⟨0, hd⟩)
  have hCβ0 : 0 ≤ Cβ := le_trans (abs_nonneg _) (hCβ ⟨0, hd⟩)
  have hR0 : (0:ℝ) ≤ Real.sqrt d * Cγ + Cβ :=
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCγ0) hCβ0
  refine (pi_norm_le_iff_of_nonneg hR0).mpr (fun i => ?_)
  refine (pi_norm_le_iff_of_nonneg hR0).mpr (fun j => ?_)
  rw [Real.norm_eq_abs]
  simp only [layerNormCoord]
  have hσ : 0 < rowStdCoord i X := rowStdCoord_pos i X
  have hnorm : |(X i j - rowMeanCoord i X) / rowStdCoord i X| ≤ Real.sqrt d := by
    rw [abs_div, abs_of_pos hσ, div_le_iff₀ hσ]
    exact abs_centered_le_sqrt_d_mul_std hd i j X
  calc |(X i j - rowMeanCoord i X) / rowStdCoord i X * γ j + β j|
      ≤ |(X i j - rowMeanCoord i X) / rowStdCoord i X * γ j| + |β j| := abs_add_le _ _
    _ = |(X i j - rowMeanCoord i X) / rowStdCoord i X| * |γ j| + |β j| := by rw [abs_mul]
    _ ≤ Real.sqrt d * Cγ + Cβ :=
        add_le_add (mul_le_mul hnorm (hCγ j) (abs_nonneg _) (Real.sqrt_nonneg _)) (hCβ j)

/-- **Layer normalization is Lipschitz in its affine weights.** For a fixed input, the map
`(γ,β) ↦ layerNormCoord γ β X` moves by at most `√d·dist γ γ' + dist β β'`: the normalized entry
(bounded by `√d`) multiplies the `γ` perturbation, and the `β` perturbation enters directly. This is
the weight-Lipschitz atom layer-norm contributes to the parameter-Lipschitz composition (the affine
`γ, β` are the layer's learnable weights). -/
lemma layerNormCoord_param_lipschitz (hd : 0 < d) (γ β γ' β' : Fin d → ℝ) (X : Fin s → Fin d → ℝ) :
    dist (layerNormCoord γ β X) (layerNormCoord γ' β' X)
      ≤ Real.sqrt d * dist γ γ' + dist β β' := by
  refine (dist_pi_le_iff (by positivity)).mpr (fun i => ?_)
  refine (dist_pi_le_iff (by positivity)).mpr (fun j => ?_)
  rw [Real.dist_eq]
  simp only [layerNormCoord]
  have hσ : 0 < rowStdCoord i X := rowStdCoord_pos i X
  have hnorm : |(X i j - rowMeanCoord i X) / rowStdCoord i X| ≤ Real.sqrt d := by
    rw [abs_div, abs_of_pos hσ, div_le_iff₀ hσ]
    exact abs_centered_le_sqrt_d_mul_std hd i j X
  have hγ : |γ j - γ' j| ≤ dist γ γ' := by rw [← Real.dist_eq]; exact dist_le_pi_dist γ γ' j
  have hβ : |β j - β' j| ≤ dist β β' := by rw [← Real.dist_eq]; exact dist_le_pi_dist β β' j
  calc |(X i j - rowMeanCoord i X) / rowStdCoord i X * γ j + β j
          - ((X i j - rowMeanCoord i X) / rowStdCoord i X * γ' j + β' j)|
      = |(X i j - rowMeanCoord i X) / rowStdCoord i X * (γ j - γ' j) + (β j - β' j)| := by
        congr 1; ring
    _ ≤ |(X i j - rowMeanCoord i X) / rowStdCoord i X * (γ j - γ' j)| + |β j - β' j| :=
        abs_add_le _ _
    _ = |(X i j - rowMeanCoord i X) / rowStdCoord i X| * |γ j - γ' j| + |β j - β' j| := by
        rw [abs_mul]
    _ ≤ Real.sqrt d * dist γ γ' + dist β β' :=
        add_le_add (mul_le_mul hnorm hγ (abs_nonneg _) (Real.sqrt_nonneg _)) hβ

end TLT
