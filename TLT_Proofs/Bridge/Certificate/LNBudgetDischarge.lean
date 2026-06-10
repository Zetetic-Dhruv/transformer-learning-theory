/-
# Discharging the LayerNorm budget with the concrete executed reductions

The block carriers (`mhBlockRootExecLayer` / `ffnBlockRootExecLayer`) carry an abstract LayerNorm budget
(`meanOf`/`stdOf`/`ln_budget`/`hln`). This file discharges it: it instantiates the executed per-row mean
and std as the genuine `Vexec` uniform-`1/d` matmul reductions (the bit-level fp32 reductions, read over
`ℝ`), and proves the carriers' `hln` with the closed-form `lnBudgetVal d B Cγ Maff` — every per-op
rounding (`ρm` mean, `ρs` std, `ρround` affine) is the floor-driven closed budget. The LayerNorm is now a
faithful executed ℝ-model (its mean/std ARE `toReal` of the IEEE reductions), no abstract budget left.
-/
import TLT_Proofs.Bridge.Certificate.FullBlockLiteralExecutedBinding

open TorchLean.Floats (neuralMagnitude neuralBpow binaryRadix)
open TorchLean.Floats.IEEE754.IEEE32Exec

namespace TLT.LNBudget

open TLT TLT.Fp32LN TLT.Fp32FFN TLT.Fp32Attn TLT.FullBlockLit

noncomputable section

/-! ## The concrete executed mean / centered-square / std reductions -/

/-- The executed per-row mean: the `Vexec` uniform-`1/d` matmul (the fp32 row sum, scaled), read at
column `0`. The bit-level executed mean of `Spec.layerNorm`'s `reduceMean`. -/
def lnMeanExec {n d : ℕ} (hd : 0 < d) (X : Fin n → Fin d → ℝ) : Fin n → ℝ :=
  fun i => Vexec (fun _ _ => (1 / (d : ℝ))) X i ⟨0, hd⟩

/-- The executed centered squares: `fp32Round` of `(X − meanE)²` (the squaring round). -/
def lnCSqExec {n d : ℕ} (hd : 0 < d) (X : Fin n → Fin d → ℝ) : Fin n → Fin d → ℝ :=
  fun i k => fp32Round ((X i k - lnMeanExec hd X i) ^ 2)

/-- The executed per-row std: `√(max(Vexec-variance, 0) + ε)` — the `Vexec` uniform-`1/d` matmul of the
executed centered squares, clamped, regularised, square-rooted. The bit-level executed std. -/
def lnStdExec {n d : ℕ} (hd : 0 < d) (X : Fin n → Fin d → ℝ) : Fin n → ℝ :=
  fun i => Real.sqrt
    (max (Vexec (fun _ _ => (1 / (d : ℝ))) (lnCSqExec hd X) i ⟨0, hd⟩) 0 + Numbers.epsilon)

/-! ## The closed-form budget components -/

/-- Mean reduction budget `ρm = rdotBudget d B`. -/
def lnRhoM (d : ℕ) (B : ℝ) : ℝ := rdotBudget d B

/-- Squaring-round budget `εsq = 2⁻²⁴·(2B+ρm)²`. -/
def lnEpsSq (d : ℕ) (B : ℝ) : ℝ := neuralBpow binaryRadix (-24) * (2 * B + lnRhoM d B) ^ 2

/-- Std reduction budget `ρs = (matmul-var-round + centered-square-perturbation) / (2√ε)`. -/
def lnRhoS (d : ℕ) (B : ℝ) : ℝ :=
  (rdotBudget d ((2 * B + lnRhoM d B) ^ 2 + lnEpsSq d B)
      + (lnEpsSq d B + lnRhoM d B * (4 * B + lnRhoM d B)))
    / (2 * Real.sqrt Numbers.epsilon)

/-- The full LayerNorm forward-error budget `ρround + Cγ·(ρm/√ε + 2B·ρs/ε)`, closed form in
`(d, B, Cγ, Maff)`. -/
def lnBudgetVal (d : ℕ) (B Cγ Maff : ℝ) : ℝ :=
  neuralBpow binaryRadix (-24) * Maff
    + Cγ * (lnRhoM d B / Real.sqrt Numbers.epsilon + 2 * B * lnRhoS d B / Numbers.epsilon)

/-- The row mean of a `B`-bounded matrix is `B`-bounded. -/
lemma rowMeanCoord_abs_le {n d : ℕ} (hd : 0 < d) {X : Fin n → Fin d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hX : ∀ i k, |X i k| ≤ B) (i : Fin n) : |rowMeanCoord i X| ≤ B := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  rw [rowMeanCoord, abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
  calc |∑ k, X i k| ≤ ∑ k, |X i k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d, B := Finset.sum_le_sum (fun k _ => hX i k)
    _ = B * (d : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

/-- **The LayerNorm budget discharge.** With the executed mean/std reductions `lnMeanExec`/`lnStdExec`,
the executed LayerNorm `lnStarExec` is within the closed-form `lnBudgetVal d B Cγ Maff` of the ideal
`layerNormCoord`, under the honest normal-range regime (the two `Vexec` reductions normal, the squaring
and the affine in the binary32 normal range, the affine magnitude bounded by `Maff`). This is the
carriers' `hln` (at a fixed residual `X`); the budgets `ρm`/`εsq`/`ρs`/`ρround` are all floor-driven. -/
lemma lnStarExec_residual_budget {n d : ℕ} (hd : 0 < d) (γ β : Fin d → ℝ) {B Cγ Maff : ℝ}
    (hB : 0 ≤ B) (hCγ0 : 0 ≤ Cγ) (hMaff0 : 0 ≤ Maff)
    (X : Fin n → Fin d → ℝ) (hX : ∀ i k, |X i k| ≤ B) (hCγ : ∀ j, |γ j| ≤ Cγ) (hdu : (d : ℝ) * u < 1)
    (hnMean : VexecNormal (fun _ _ => (1 / (d : ℝ))) X)
    (hnVar : VexecNormal (fun _ _ => (1 / (d : ℝ))) (lnCSqExec hd X))
    (hsqNormal : ∀ i k, (X i k - lnMeanExec hd X i) ^ 2 ≠ 0 →
      (-125 : ℤ) ≤ neuralMagnitude binaryRadix ((X i k - lnMeanExec hd X i) ^ 2))
    (hMaffB : ∀ i j,
      |(X i j - lnMeanExec hd X i) / lnStdExec hd X i * γ j + β j| ≤ Maff)
    (haffNormal : ∀ i j,
      ((X i j - lnMeanExec hd X i) / lnStdExec hd X i * γ j + β j) ≠ 0 →
      (-125 : ℤ) ≤ neuralMagnitude binaryRadix
        ((X i j - lnMeanExec hd X i) / lnStdExec hd X i * γ j + β j)) :
    dist (lnStarExec γ β (lnMeanExec hd X) (lnStdExec hd X) X) (layerNormCoord γ β X)
      ≤ lnBudgetVal d B Cγ Maff := by
  have hρm : (0 : ℝ) ≤ lnRhoM d B := rdotBudget_nonneg hdu hB
  have hmean : ∀ i, |lnMeanExec hd X i - rowMeanCoord i X| ≤ lnRhoM d B :=
    fun i => lnMean_error hd X hB hX hnMean hdu i ⟨0, hd⟩
  have hmeanB : ∀ i, |rowMeanCoord i X| ≤ B := fun i => rowMeanCoord_abs_le hd hB hX i
  have hεsq : (0 : ℝ) ≤ lnEpsSq d B :=
    mul_nonneg (neuralBpow.nonneg _ _) (sq_nonneg _)
  have hsqround : ∀ i k, |lnCSqExec hd X i k - (X i k - lnMeanExec hd X i) ^ 2| ≤ lnEpsSq d B :=
    fun i k => centeredSqRound_le X (lnMeanExec hd X) hB hρm hX hmean hmeanB hsqNormal i k
  have hρs : (0 : ℝ) ≤ lnRhoS d B := by
    rw [lnRhoS]
    refine div_nonneg ?_ (by positivity)
    have h1 : (0 : ℝ) ≤ rdotBudget d ((2 * B + lnRhoM d B) ^ 2 + lnEpsSq d B) :=
      rdotBudget_nonneg hdu (by positivity)
    have h2 : (0 : ℝ) ≤ lnEpsSq d B + lnRhoM d B * (4 * B + lnRhoM d B) := by positivity
    linarith
  have hstd : ∀ i, |lnStdExec hd X i - rowStdCoord i X| ≤ lnRhoS d B :=
    fun i => lnStd_error hd X (lnMeanExec hd X) (lnCSqExec hd X) hB hρm hεsq hX hmean hmeanB
      hsqround hnVar hdu i ⟨0, hd⟩
  have hstdE : ∀ i, Real.sqrt Numbers.epsilon ≤ lnStdExec hd X i := by
    intro i
    rw [lnStdExec]
    refine Real.sqrt_le_sqrt ?_
    have := le_max_right (Vexec (fun _ _ => (1 / (d : ℝ))) (lnCSqExec hd X) i ⟨0, hd⟩) 0
    linarith
  have hround : ∀ i j, |lnStarExec γ β (lnMeanExec hd X) (lnStdExec hd X) X i j
      - ((X i j - lnMeanExec hd X i) / lnStdExec hd X i * γ j + β j)|
      ≤ neuralBpow binaryRadix (-24) * Maff :=
    fun i j => affineRound_le γ β (lnMeanExec hd X) (lnStdExec hd X) X hMaffB haffNormal i j
  have hρr : (0 : ℝ) ≤ neuralBpow binaryRadix (-24) * Maff :=
    mul_nonneg (neuralBpow.nonneg _ _) hMaff0
  rw [dist_eq_norm]
  exact lnExec_forward_error γ β (lnMeanExec hd X) (lnStdExec hd X) X hB hCγ0 hρm hρs hρr hX hCγ
    hround hmean hmeanB hstd hstdE

end

end TLT.LNBudget
