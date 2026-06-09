/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Certificate.AttentionExecutedCertificate
import TLT_Proofs.Bridge.Fp32.ClampedReductionRounding

/-\!
# A derived fp32 forward-error envelope for the attention head

The executed certificate `attnHead_executed_certified_generalization`
(`Bridge/Certificate/AttentionExecutedCertificate`) takes a *free* rounding bound `rnd` and a *free*
envelope hypothesis `hexec_close : ∀ y, dist (execAttn y) (attnHead …) ≤ rnd`. This file closes that
gap: it gives a concrete executed forward `execAttn⋆` — the literal fp32 attention head, every scalar
operation modelled as "the real operation followed by one IEEE binary32 rounding step" — and **proves**
the forward-error bound `dist (execAttn⋆ Y) (attnHead scale W (clampCoord B Y)) ≤ rnd⋆` with `rnd⋆` a
**derived closed form** in the clamp bound `B`, the weight `ℓ¹`-bound `Λ`, the unit roundoff
`u = 2⁻²⁴`, and the shapes `n, d`. The certificate is then instantiated with this derived data, leaving
no free rounding argument.
-/

open TorchLean.Floats (neuralMagnitude neuralBpow binaryRadix)
open TorchLean.Floats.IEEE754.IEEE32Exec

noncomputable section

namespace TLT.Fp32Attn

/-- The binary32 unit roundoff `u = 2⁻²⁴ = neuralBpow binaryRadix (-24)`. -/
noncomputable def u : ℝ := neuralBpow binaryRadix (-24)

/-- The unit roundoff is nonnegative. -/
lemma u_nonneg : 0 ≤ u := neuralBpow.nonneg binaryRadix (-24)

/-- `u = 2⁻²⁴` as a literal real. -/
lemma u_eq : u = (2 : ℝ) ^ (-24 : ℤ) := by
  simp only [u, neuralBpow]
  norm_num [TorchLean.Floats.NeuralRadix.toReal, binaryRadix]

/-- `u < 1`. -/
lemma u_lt_one : u < 1 := by
  rw [u_eq, show (-24 : ℤ) = -(24 : ℕ) from rfl, zpow_neg, zpow_natCast, inv_lt_one_iff₀]
  right
  exact one_lt_pow₀ (by norm_num) (by norm_num)

/-- `u ≤ 1`. -/
lemma u_le_one : u ≤ 1 := u_lt_one.le

/-\! ## The reusable rounded dot product

Every reduction in the head (value projection, scores, the softmax denominator, the value mix) is a
dot product. The executed forward computes it as: round each scalar product, then accumulate the sum
with a `fp32Round` after every addition (`fp32Foldl`, the left fold matching the literal accumulator
order). `rdot` packages this; `rdot_error_le` gives its derived closed-form rounding error against the
exact real dot product `∑ₖ aₖ·bₖ`. -/

/-- The rounded scalar products `k ↦ fp32Round (a k * b k)`. -/
def rprods {K : ℕ} (a b : Fin K → ℝ) : List ℝ :=
  List.ofFn (fun k => fp32Round (a k * b k))

/-- The rounded dot product: round each product, then fp32-fold the sum left-to-right. -/
def rdot {K : ℕ} (a b : Fin K → ℝ) : ℝ :=
  fp32Foldl 0 (rprods a b)

/-- The normal-range side conditions of `rdot a b`: every fold accumulation step is in the binary32
normal range, and every scalar product `a k * b k` is a normal nonzero (so its rounding obeys the
relative `u`-bound). These are the honest no-underflow/no-overflow hypotheses for the reduction. -/
def RdotNormal {K : ℕ} (a b : Fin K → ℝ) : Prop :=
  Fp32FoldlNormal 0 (rprods a b)
    ∧ ∀ k, a k * b k ≠ 0 ∧ (-125 : ℤ) ≤ neuralMagnitude binaryRadix (a k * b k)

/-- Each rounded product is within `u·|aₖ·bₖ|` of the exact product (relative round-to-nearest on the
normal range). -/
lemma abs_rprod_sub_le {K : ℕ} (a b : Fin K → ℝ) (h : RdotNormal a b) (k : Fin K) :
    |fp32Round (a k * b k) - a k * b k| ≤ u * |a k * b k| := by
  obtain ⟨_, hp⟩ := h
  exact fp32Round_rel_on_normal (a k * b k) (hp k).1 (hp k).2

/-- The exact sum of rounded products differs from the exact dot product by at most `u·∑ₖ|aₖ·bₖ|`. -/
lemma abs_rprods_sum_sub_le {K : ℕ} (a b : Fin K → ℝ) (h : RdotNormal a b) :
    |(rprods a b).sum - ∑ k, a k * b k| ≤ u * ∑ k, |a k * b k| := by
  have hsum : (rprods a b).sum = ∑ k, fp32Round (a k * b k) := by
    rw [rprods, List.sum_ofFn]
  rw [hsum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  calc |∑ k, (fp32Round (a k * b k) - a k * b k)|
      ≤ ∑ k, |fp32Round (a k * b k) - a k * b k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, u * |a k * b k| := Finset.sum_le_sum (fun k _ => abs_rprod_sub_le a b h k)

/-- Each rounded product has magnitude at most `(1+u)·|aₖ·bₖ|`. -/
lemma abs_rprod_le {K : ℕ} (a b : Fin K → ℝ) (h : RdotNormal a b) (k : Fin K) :
    |fp32Round (a k * b k)| ≤ (1 + u) * |a k * b k| := by
  calc |fp32Round (a k * b k)|
      = |(fp32Round (a k * b k) - a k * b k) + a k * b k| := by ring_nf
    _ ≤ |fp32Round (a k * b k) - a k * b k| + |a k * b k| := abs_add_le _ _
    _ ≤ u * |a k * b k| + |a k * b k| := by linarith [abs_rprod_sub_le a b h k]
    _ = (1 + u) * |a k * b k| := by ring

/-- The magnitude-sum of the rounded products is at most `(1+u)·∑ₖ|aₖ·bₖ|`. -/
lemma rprods_map_abs_sum_le {K : ℕ} (a b : Fin K → ℝ) (h : RdotNormal a b) :
    ((rprods a b).map (fun x => |x|)).sum ≤ (1 + u) * ∑ k, |a k * b k| := by
  rw [rprods, List.map_ofFn, List.sum_ofFn, Finset.mul_sum]
  exact Finset.sum_le_sum (fun k _ => abs_rprod_le a b h k)

/-- The list of rounded products has length `K`. -/
@[simp] lemma rprods_length {K : ℕ} (a b : Fin K → ℝ) : (rprods a b).length = K := by
  simp [rprods]

/-- **Derived closed-form rounding error of `rdot`.** With every accumulation step and every product
normal (`RdotNormal`) and `K·u < 1`, the rounded dot product differs from the exact dot product
`∑ₖ aₖ·bₖ` by at most `u·(K+1)·(1+u)·P/(1−K·u) + u·P`, where `P = ∑ₖ|aₖ·bₖ|`. Derived from the
round-to-nearest model: the fold rounding via `fp32Foldl_error_le_of_sum_bound`, the per-product
rounding via `fp32Round_rel_on_normal`. -/
lemma rdot_error_le {K : ℕ} (a b : Fin K → ℝ) (h : RdotNormal a b)
    (hKu : (K : ℝ) * u < 1) :
    |rdot a b - ∑ k, a k * b k|
      ≤ u * (((K : ℝ) + 1) * ((1 + u) * ∑ k, |a k * b k|)) / (1 - (K : ℝ) * u)
        + u * ∑ k, |a k * b k| := by
  set P : ℝ := ∑ k, |a k * b k| with hP
  have hPnn : 0 ≤ P := Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hlen : ((rprods a b).length : ℝ) = (K : ℝ) := by simp
  have hun : neuralBpow binaryRadix (-24) * ((rprods a b).length : ℝ) < 1 := by
    rw [hlen]; rw [show neuralBpow binaryRadix (-24) = u from rfl, mul_comm]; exact hKu
  have hfold := fp32Foldl_error_le_of_sum_bound (rprods a b) ((1 + u) * P) h.1 hun
    (rprods_map_abs_sum_le a b h)
  have hfold' : |rdot a b - (rprods a b).sum|
      ≤ u * (((K : ℝ) + 1) * ((1 + u) * P)) / (1 - (K : ℝ) * u) := by
    rw [show neuralBpow binaryRadix (-24) = u from rfl, hlen] at hfold
    show |fp32Foldl 0 (rprods a b) - (rprods a b).sum| ≤ _
    convert hfold using 2
    ring
  calc |rdot a b - ∑ k, a k * b k|
      ≤ |rdot a b - (rprods a b).sum| + |(rprods a b).sum - ∑ k, a k * b k| := by
        have := abs_sub_le (rdot a b) ((rprods a b).sum) (∑ k, a k * b k); linarith
    _ ≤ u * (((K : ℝ) + 1) * ((1 + u) * P)) / (1 - (K : ℝ) * u) + u * P :=
        add_le_add hfold' (abs_rprods_sum_sub_le a b h)

/-\! ## The closed-form rounded-dot budget, monotone in the magnitude bound -/

/-- The closed-form rounding budget of a `K`-term rounded dot product whose product magnitudes sum to
at most `P`: `u·(K+1)·(1+u)·P/(1−K·u) + u·P`. -/
noncomputable def rdotBudget (K : ℕ) (P : ℝ) : ℝ :=
  u * (((K : ℝ) + 1) * ((1 + u) * P)) / (1 - (K : ℝ) * u) + u * P

/-- The budget is monotone in the magnitude bound `P` (for `K·u < 1`). -/
lemma rdotBudget_mono {K : ℕ} (hKu : (K : ℝ) * u < 1) {P Q : ℝ} (hPQ : P ≤ Q) :
    rdotBudget K P ≤ rdotBudget K Q := by
  have hpos : 0 < 1 - (K : ℝ) * u := by linarith
  have hu0 : 0 ≤ u := u_nonneg
  unfold rdotBudget
  gcongr

/-- The budget is nonnegative when `0 ≤ P` and `K·u < 1`. -/
lemma rdotBudget_nonneg {K : ℕ} (hKu : (K : ℝ) * u < 1) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ rdotBudget K P := by
  have hpos : 0 < 1 - (K : ℝ) * u := by linarith
  have hu0 : 0 ≤ u := u_nonneg
  unfold rdotBudget
  have ht1 : 0 ≤ u * (((K : ℝ) + 1) * ((1 + u) * P)) / (1 - (K : ℝ) * u) := by
    apply div_nonneg _ hpos.le; positivity
  have ht2 : 0 ≤ u * P := by positivity
  linarith

/-- `rdot` error in terms of the budget at any magnitude bound `S` (monotone form). -/
lemma rdot_error_le_of_sum_bound {K : ℕ} (a b : Fin K → ℝ) (h : RdotNormal a b)
    (hKu : (K : ℝ) * u < 1) {S : ℝ} (hS : ∑ k, |a k * b k| ≤ S) :
    |rdot a b - ∑ k, a k * b k| ≤ rdotBudget K S :=
  (rdot_error_le a b h hKu).trans (rdotBudget_mono hKu hS)

/-\! ## Stage 1 — the rounded value projection `matMulCoord W X`

The value rows are `V = matMulCoord W X`, `V i j = ∑ₖ Xᵢₖ·Wₖⱼ`. The executed value matrix rounds each
such dot product (`rdot`). With the input clamped (`|Xᵢₖ| ≤ B`) and the weight columns `ℓ¹`-bounded
(`∑ₖ|Wₖⱼ| ≤ Λ`), each entry's rounding error is `≤ rdotBudget d (B·Λ)`. -/

/-- The executed (rounded) value projection: each entry is a rounded dot product of an input row
against a weight column. Equals `matMulCoord W X` in exact real arithmetic. -/
def Vexec {n d : ℕ} (W : Fin d → Fin d → ℝ) (X : Fin n → Fin d → ℝ) : Fin n → Fin d → ℝ :=
  fun i j => rdot (X i) (fun k => W k j)

/-- The normal-range side conditions of every value-projection reduction. -/
def VexecNormal {n d : ℕ} (W : Fin d → Fin d → ℝ) (X : Fin n → Fin d → ℝ) : Prop :=
  ∀ i j, RdotNormal (X i) (fun k => W k j)

/-- **Per-entry value-projection rounding error.** Each executed value entry is within
`rdotBudget d (B·Λ)` of the exact value entry `matMulCoord W X i j`. -/
lemma Vexec_entry_error {n d : ℕ} (W : Fin d → Fin d → ℝ) (X : Fin n → Fin d → ℝ)
    {B Λ : ℝ} (hB : 0 ≤ B) (_hΛ0 : 0 ≤ Λ) (hX : ∀ i k, |X i k| ≤ B)
    (hW : ∀ j, ∑ k, |W k j| ≤ Λ) (hnorm : VexecNormal W X) (hdu : (d : ℝ) * u < 1)
    (i : Fin n) (j : Fin d) :
    |Vexec W X i j - matMulCoord W X i j| ≤ rdotBudget d (B * Λ) := by
  have hkey : ∑ k, |(X i) k * (fun k => W k j) k| ≤ B * Λ := by
    calc ∑ k, |(X i) k * (fun k => W k j) k|
        = ∑ k, |X i k| * |W k j| := by
          refine Finset.sum_congr rfl (fun k _ => ?_); rw [abs_mul]
      _ ≤ ∑ k, B * |W k j| :=
          Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hX i k) (abs_nonneg _))
      _ = B * ∑ k, |W k j| := by rw [Finset.mul_sum]
      _ ≤ B * Λ := mul_le_mul_of_nonneg_left (hW j) hB
  have he : matMulCoord W X i j = ∑ k, (X i) k * (fun k => W k j) k := by
    simp only [matMulCoord]
  rw [Vexec, he]
  exact rdot_error_le_of_sum_bound (X i) (fun k => W k j) (hnorm i j) hdu hkey

/-- **Value-projection forward error (sup norm).** The executed value matrix is within
`rdotBudget d (B·Λ)` of `matMulCoord W X`. -/
lemma Vexec_error {n d : ℕ} (W : Fin d → Fin d → ℝ) (X : Fin n → Fin d → ℝ)
    {B Λ : ℝ} (hB : 0 ≤ B) (hΛ0 : 0 ≤ Λ) (hX : ∀ i k, |X i k| ≤ B)
    (hW : ∀ j, ∑ k, |W k j| ≤ Λ) (hnorm : VexecNormal W X) (hdu : (d : ℝ) * u < 1) :
    ‖Vexec W X - matMulCoord W X‖ ≤ rdotBudget d (B * Λ) := by
  have hbud : 0 ≤ rdotBudget d (B * Λ) := rdotBudget_nonneg hdu (mul_nonneg hB hΛ0)
  refine (pi_norm_le_iff_of_nonneg hbud).mpr (fun i => ?_)
  refine (pi_norm_le_iff_of_nonneg hbud).mpr (fun j => ?_)
  rw [Real.norm_eq_abs, Pi.sub_apply, Pi.sub_apply]
  exact Vexec_entry_error W X hB hΛ0 hX hW hnorm hdu i j

/-\! ## Stage 2 — the rounded scaled scores `attnScores scale (X i) X`

For query row `i`, the scores are `s i k' = (∑ₑ Xᵢₑ·Xₖ'ₑ)/scale`. The executed scores round the dot
product (`rdot`), divide by the exact `scale`, and round once more. With the input clamped each score
dot magnitude is `≤ d·B²`, so the score error per entry is bounded by a closed form in `B, d, u, scale`.
-/

/-- The executed (rounded) scaled score `s̃ i k'`: round the dot product `rdot (X i) (X k')`, divide
by `scale`, round once. Equals `attnScores scale (X i) X k'` in exact real arithmetic. -/
def Sexec {n d : ℕ} (scale : ℝ) (X : Fin n → Fin d → ℝ) : Fin n → Fin n → ℝ :=
  fun i k' => fp32Round (rdot (X i) (X k') / scale)

/-- The normal-range side conditions of every score reduction: the dot product is `RdotNormal`, and the
divided quantity `rdot (X i) (X k') / scale` is a normal nonzero (so the final rounding obeys the
relative `u`-bound). -/
def SexecNormal {n d : ℕ} (scale : ℝ) (X : Fin n → Fin d → ℝ) : Prop :=
  ∀ i k', RdotNormal (X i) (X k')
    ∧ rdot (X i) (X k') / scale ≠ 0
    ∧ (-125 : ℤ) ≤ neuralMagnitude binaryRadix (rdot (X i) (X k') / scale)

/-- The dot-magnitude bound for a score dot product: `∑ₑ|Xᵢₑ·Xₖ'ₑ| ≤ d·B²`. -/
lemma score_dot_sum_le {n d : ℕ} (X : Fin n → Fin d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hX : ∀ i k, |X i k| ≤ B) (i k' : Fin n) :
    ∑ e, |(X i) e * (X k') e| ≤ (d : ℝ) * B ^ 2 := by
  calc ∑ e, |(X i) e * (X k') e|
      = ∑ e, |X i e| * |X k' e| := by
        refine Finset.sum_congr rfl (fun e _ => ?_); rw [abs_mul]
    _ ≤ ∑ _e : Fin d, B * B :=
        Finset.sum_le_sum (fun e _ => mul_le_mul (hX i e) (hX k' e) (abs_nonneg _) hB)
    _ = (d : ℝ) * B ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The closed-form score-error bound per entry: `(u·(d·B² + rdotBudget d (d·B²)) + rdotBudget d (d·B²))/scale`. -/
noncomputable def scoreErr (d : ℕ) (B scale : ℝ) : ℝ :=
  (u * ((d : ℝ) * B ^ 2 + rdotBudget d ((d : ℝ) * B ^ 2)) + rdotBudget d ((d : ℝ) * B ^ 2)) / scale

/-- The score-error bound is nonnegative. -/
lemma scoreErr_nonneg {d : ℕ} {B scale : ℝ} (_hB : 0 ≤ B) (hdu : (d : ℝ) * u < 1)
    (hscale : 0 < scale) : 0 ≤ scoreErr d B scale := by
  rw [scoreErr]
  apply div_nonneg _ hscale.le
  have hdb : 0 ≤ rdotBudget d ((d : ℝ) * B ^ 2) :=
    rdotBudget_nonneg hdu (by positivity)
  have hdB2 : 0 ≤ (d : ℝ) * B ^ 2 := by positivity
  have hu0 : 0 ≤ u := u_nonneg
  have h1 : 0 ≤ u * ((d : ℝ) * B ^ 2 + rdotBudget d ((d : ℝ) * B ^ 2)) := by
    apply mul_nonneg hu0; linarith
  linarith

/-- **Per-entry score rounding error.** Each executed score is within `scoreErr d B scale` of the exact
score `attnScores scale (X i) X k'`. -/
lemma Sexec_entry_error {n d : ℕ} (scale : ℝ) (X : Fin n → Fin d → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hscale : 0 < scale) (hX : ∀ i k, |X i k| ≤ B)
    (hnorm : SexecNormal scale X) (hdu : (d : ℝ) * u < 1) (i k' : Fin n) :
    |Sexec scale X i k' - attnScores scale (X i) X k'| ≤ scoreErr d B scale := by
  obtain ⟨hdot, hdivne, hdivnorm⟩ := hnorm i k'
  set D : ℝ := ∑ e, (X i) e * (X k') e with hD
  have hDdef : attnScores scale (X i) X k' = D / scale := by
    simp only [attnScores, hD]
  have hdotE : |rdot (X i) (X k') - D| ≤ rdotBudget d ((d : ℝ) * B ^ 2) :=
    rdot_error_le_of_sum_bound (X i) (X k') hdot hdu (score_dot_sum_le X hB hX i k')
  have hDabs : |D| ≤ (d : ℝ) * B ^ 2 := by
    calc |D| = |∑ e, (X i) e * (X k') e| := by rw [hD]
      _ ≤ ∑ e, |(X i) e * (X k') e| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ (d : ℝ) * B ^ 2 := score_dot_sum_le X hB hX i k'
  have hround : |fp32Round (rdot (X i) (X k') / scale) - rdot (X i) (X k') / scale|
      ≤ u * |rdot (X i) (X k') / scale| := by
    have := fp32Round_rel_on_normal (rdot (X i) (X k') / scale) hdivne hdivnorm
    rwa [show neuralBpow binaryRadix (-24) = u from rfl] at this
  have hrdotabs : |rdot (X i) (X k') / scale|
      ≤ ((d : ℝ) * B ^ 2 + rdotBudget d ((d : ℝ) * B ^ 2)) / scale := by
    rw [abs_div, abs_of_pos hscale, div_le_div_iff_of_pos_right hscale]
    calc |rdot (X i) (X k')|
        = |(rdot (X i) (X k') - D) + D| := by ring_nf
      _ ≤ |rdot (X i) (X k') - D| + |D| := abs_add_le _ _
      _ ≤ rdotBudget d ((d : ℝ) * B ^ 2) + (d : ℝ) * B ^ 2 := by linarith
      _ = (d : ℝ) * B ^ 2 + rdotBudget d ((d : ℝ) * B ^ 2) := by ring
  rw [Sexec, hDdef]
  calc |fp32Round (rdot (X i) (X k') / scale) - D / scale|
      ≤ |fp32Round (rdot (X i) (X k') / scale) - rdot (X i) (X k') / scale|
          + |rdot (X i) (X k') / scale - D / scale| := by
        have := abs_sub_le (fp32Round (rdot (X i) (X k') / scale)) (rdot (X i) (X k') / scale)
          (D / scale); linarith
    _ ≤ u * (((d : ℝ) * B ^ 2 + rdotBudget d ((d : ℝ) * B ^ 2)) / scale)
          + rdotBudget d ((d : ℝ) * B ^ 2) / scale := by
        refine add_le_add ?_ ?_
        · exact le_trans hround (mul_le_mul_of_nonneg_left hrdotabs u_nonneg)
        · rw [← sub_div, abs_div, abs_of_pos hscale, div_le_div_iff_of_pos_right hscale]
          exact hdotE
    _ = scoreErr d B scale := by rw [scoreErr]; ring

/-\! ## Stage 3 — the rounded softmax and value mix

For a query row, with rounded scores `z̃ : Fin n → ℝ` and rounded value rows `Ṽ`, the executed softmax
computes `ẽⱼ = fp32Round (exp z̃ⱼ)` (the rounding model "real exp + one rounding step"; the heavier
bridge to the literal polynomial `IEEE32Exec.exp` is `exec32_exp_error`, not used here), the denominator
`D̃ = fp32-fold of ẽ`, the weights `p̃ⱼ = fp32Round (ẽⱼ / D̃)`, and mixes `õ c = rdot p̃ (Ṽ · c)`. We bound
the total weight error `∑ⱼ|p̃ⱼ − softmax z̃ⱼ|` and propagate it through the mix.

The softmax-denominator non-underflow is the genuine boundary here: a sum of positive exponentials can
in principle underflow to a non-normal/zero float, after which no clamp-ball argument recovers the
quotient. We surface it as the explicit honest hypothesis `Dlo ≤ D̃` (a positive lower bound on the
rounded denominator). Everything else — the exp bounds, the denominator fold, the quotient and mix
rounding — is derived from the round-to-nearest model. -/

/-- The rounded exponentials of a score vector: `j ↦ fp32Round (Real.exp (z j))`. -/
def rexp {n : ℕ} (z : Fin n → ℝ) : Fin n → ℝ :=
  fun j => fp32Round (Real.exp (z j))

/-- The rounded softmax denominator: the fp32 left-fold of the rounded exponentials. -/
def rdenom {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  fp32Foldl 0 (List.ofFn (rexp z))

/-- The rounded softmax weights: `j ↦ fp32Round (rexp z j / rdenom z)`. -/
def rsoftmax {n : ℕ} (z : Fin n → ℝ) : Fin n → ℝ :=
  fun j => fp32Round (rexp z j / rdenom z)

/-- The normal-range side conditions of the rounded softmax of `z`: each `exp zⱼ` rounds normally,
every denominator accumulation step is normal, and each quotient `rexp z j / rdenom z` rounds
normally. -/
def RsoftmaxNormal {n : ℕ} (z : Fin n → ℝ) : Prop :=
  (∀ j, Real.exp (z j) ≠ 0 ∧ (-125 : ℤ) ≤ neuralMagnitude binaryRadix (Real.exp (z j)))
    ∧ Fp32FoldlNormal 0 (List.ofFn (rexp z))
    ∧ (∀ j, rexp z j / rdenom z ≠ 0
        ∧ (-125 : ℤ) ≤ neuralMagnitude binaryRadix (rexp z j / rdenom z))

/-- Each rounded exponential is within `u·exp zⱼ` of the exact exponential. -/
lemma abs_rexp_sub_le {n : ℕ} (z : Fin n → ℝ) (h : RsoftmaxNormal z) (j : Fin n) :
    |rexp z j - Real.exp (z j)| ≤ u * Real.exp (z j) := by
  have hb := fp32Round_rel_on_normal (Real.exp (z j)) (h.1 j).1 (h.1 j).2
  rw [show neuralBpow binaryRadix (-24) = u from rfl, abs_of_pos (Real.exp_pos (z j))] at hb
  show |fp32Round (Real.exp (z j)) - Real.exp (z j)| ≤ u * Real.exp (z j)
  exact hb

/-- Each rounded exponential is positive (it is within a `< 1` relative error of a positive exact
exponential). -/
lemma rexp_pos {n : ℕ} (z : Fin n → ℝ) (h : RsoftmaxNormal z) (j : Fin n) : 0 < rexp z j := by
  have h1 : |rexp z j - Real.exp (z j)| ≤ u * Real.exp (z j) := abs_rexp_sub_le z h j
  have h2 : rexp z j - Real.exp (z j) ≥ -(u * Real.exp (z j)) := by
    have := abs_le.mp h1; linarith [this.1]
  have h3 : (1 - u) * Real.exp (z j) ≤ rexp z j := by nlinarith [Real.exp_pos (z j), u_lt_one]
  have h4 : 0 < (1 - u) * Real.exp (z j) :=
    mul_pos (by linarith [u_lt_one]) (Real.exp_pos _)
  linarith

/-- The rounded exponential is nonnegative. -/
lemma rexp_nonneg {n : ℕ} (z : Fin n → ℝ) (h : RsoftmaxNormal z) (j : Fin n) : 0 ≤ rexp z j :=
  (rexp_pos z h j).le

/-- `|rexp z j| = rexp z j` (it is positive). -/
lemma abs_rexp {n : ℕ} (z : Fin n → ℝ) (h : RsoftmaxNormal z) (j : Fin n) :
    |rexp z j| = rexp z j := abs_of_pos (rexp_pos z h j)

/-- The exact softmax denominator `D = ∑ⱼ exp zⱼ`. -/
def expSum {n : ℕ} (z : Fin n → ℝ) : ℝ := ∑ j, Real.exp (z j)

/-- The sum of rounded exponentials `∑ⱼ ẽⱼ` (the un-folded denominator). -/
def rexpSum {n : ℕ} (z : Fin n → ℝ) : ℝ := ∑ j, rexp z j

/-- The exact softmax denominator is positive (a nonempty sum of positive exponentials). -/
lemma expSum_pos {n : ℕ} [NeZero n] (z : Fin n → ℝ) : 0 < expSum z :=
  Finset.sum_pos (fun j _ => Real.exp_pos (z j)) Finset.univ_nonempty

/-- The sum of rounded exponentials is within `u·D` of the exact denominator `D`. -/
lemma abs_rexpSum_sub_le {n : ℕ} (z : Fin n → ℝ) (h : RsoftmaxNormal z) :
    |rexpSum z - expSum z| ≤ u * expSum z := by
  rw [rexpSum, expSum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  calc |∑ j, (rexp z j - Real.exp (z j))|
      ≤ ∑ j, |rexp z j - Real.exp (z j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, u * Real.exp (z j) := Finset.sum_le_sum (fun j _ => abs_rexp_sub_le z h j)

/-- The sum of rounded exponentials is at most `(1+u)·D`. -/
lemma rexpSum_le {n : ℕ} (z : Fin n → ℝ) (h : RsoftmaxNormal z) :
    rexpSum z ≤ (1 + u) * expSum z := by
  have h1 : rexpSum z - expSum z ≤ u * expSum z := (abs_le.mp (abs_rexpSum_sub_le z h)).2
  nlinarith [h1]

/-- The sum of rounded exponentials is positive. -/
lemma rexpSum_pos {n : ℕ} [NeZero n] (z : Fin n → ℝ) (h : RsoftmaxNormal z) : 0 < rexpSum z :=
  Finset.sum_pos (fun j _ => rexp_pos z h j) Finset.univ_nonempty

/-- The magnitude-sum of the rounded exponentials equals their sum (they are positive). -/
lemma rexp_map_abs_sum {n : ℕ} (z : Fin n → ℝ) (h : RsoftmaxNormal z) :
    ((List.ofFn (rexp z)).map (fun x => |x|)).sum = rexpSum z := by
  rw [List.map_ofFn, List.sum_ofFn, rexpSum]
  exact Finset.sum_congr rfl (fun j _ => abs_rexp z h j)

/-- The denominator fold differs from the sum of rounded exponentials by the fold budget at the
magnitude bound `(1+u)·D`. -/
lemma abs_rdenom_sub_rexpSum_le {n : ℕ} (z : Fin n → ℝ) (h : RsoftmaxNormal z)
    (hnu : (n : ℝ) * u < 1) :
    |rdenom z - rexpSum z|
      ≤ u * (((n : ℝ) + 1) * ((1 + u) * expSum z)) / (1 - (n : ℝ) * u) := by
  have hlen : ((List.ofFn (rexp z)).length : ℝ) = (n : ℝ) := by simp
  have hun : neuralBpow binaryRadix (-24) * ((List.ofFn (rexp z)).length : ℝ) < 1 := by
    rw [hlen, show neuralBpow binaryRadix (-24) = u from rfl, mul_comm]; exact hnu
  have hS : ((List.ofFn (rexp z)).map (fun x => |x|)).sum ≤ (1 + u) * expSum z := by
    rw [rexp_map_abs_sum z h]; exact rexpSum_le z h
  have hfold := fp32Foldl_error_le_of_sum_bound (List.ofFn (rexp z)) ((1 + u) * expSum z)
    h.2.1 hun hS
  rw [show neuralBpow binaryRadix (-24) = u from rfl, hlen] at hfold
  have hsum : (List.ofFn (rexp z)).sum = rexpSum z := by rw [List.sum_ofFn]; rfl
  rw [hsum] at hfold
  show |rdenom z - rexpSum z| ≤ _
  rw [rdenom, mul_comm (n : ℝ) u]; exact hfold

/-\! ### The total-variation error of the rounded softmax weights -/

/-- The exact softmax weight in denominator form: `softmax z j = exp zⱼ / D`. -/
lemma softmax_eq_div {n : ℕ} (z : Fin n → ℝ) (j : Fin n) :
    softmax z j = Real.exp (z j) / expSum z := by
  rw [softmax, expSum]

/-- **Per-key quotient error (un-rounded weight vs exact weight).** Bounds
`|rexp z j / rdenom z − softmax z j|` by `exp zⱼ · (u·D + |D̃ − D|) / (D̃ · D)`. -/
lemma abs_qtilde_sub_softmax_le {n : ℕ} [NeZero n] (z : Fin n → ℝ) (h : RsoftmaxNormal z)
    (hden : 0 < rdenom z) (j : Fin n) :
    |rexp z j / rdenom z - softmax z j|
      ≤ Real.exp (z j) * (u * expSum z + |rdenom z - expSum z|) / (rdenom z * expSum z) := by
  have hD : 0 < expSum z := expSum_pos z
  rw [softmax_eq_div, div_sub_div _ _ (ne_of_gt hden) (ne_of_gt hD), abs_div,
    abs_of_pos (mul_pos hden hD), div_le_div_iff_of_pos_right (mul_pos hden hD)]
  have hnum : rexp z j * expSum z - rdenom z * Real.exp (z j)
      = (rexp z j - Real.exp (z j)) * expSum z + Real.exp (z j) * (expSum z - rdenom z) := by ring
  rw [hnum]
  calc |(rexp z j - Real.exp (z j)) * expSum z + Real.exp (z j) * (expSum z - rdenom z)|
      ≤ |(rexp z j - Real.exp (z j)) * expSum z| + |Real.exp (z j) * (expSum z - rdenom z)| :=
        abs_add_le _ _
    _ = |rexp z j - Real.exp (z j)| * expSum z + Real.exp (z j) * |expSum z - rdenom z| := by
        rw [abs_mul, abs_mul, abs_of_pos hD, abs_of_pos (Real.exp_pos _)]
    _ ≤ u * Real.exp (z j) * expSum z + Real.exp (z j) * |rdenom z - expSum z| := by
        rw [abs_sub_comm (expSum z) (rdenom z)]
        gcongr
        exact abs_rexp_sub_le z h j
    _ = Real.exp (z j) * (u * expSum z + |rdenom z - expSum z|) := by ring

/-- **Total un-rounded softmax-weight error.** `∑ⱼ |rexp z j / rdenom z − softmax z j| ≤ (u·D + |D̃ − D|)/D̃`. -/
lemma sum_abs_qtilde_sub_softmax_le {n : ℕ} [NeZero n] (z : Fin n → ℝ) (h : RsoftmaxNormal z)
    (hden : 0 < rdenom z) :
    ∑ j, |rexp z j / rdenom z - softmax z j|
      ≤ (u * expSum z + |rdenom z - expSum z|) / rdenom z := by
  have hD : 0 < expSum z := expSum_pos z
  have hbound : ∑ j, |rexp z j / rdenom z - softmax z j|
      ≤ ∑ j, Real.exp (z j) * (u * expSum z + |rdenom z - expSum z|) / (rdenom z * expSum z) :=
    Finset.sum_le_sum (fun j _ => abs_qtilde_sub_softmax_le z h hden j)
  refine hbound.trans ?_
  rw [← Finset.sum_div]
  have hfac : ∑ j, Real.exp (z j) * (u * expSum z + |rdenom z - expSum z|)
      = expSum z * (u * expSum z + |rdenom z - expSum z|) := by
    rw [← Finset.sum_mul, ← expSum]
  rw [hfac]
  rw [div_le_div_iff₀ (mul_pos hden hD) hden]
  have hWnn : 0 ≤ u * expSum z + |rdenom z - expSum z| :=
    add_nonneg (mul_nonneg u_nonneg hD.le) (abs_nonneg _)
  nlinarith [hWnn, mul_pos hden hD, hD.le, hden.le]

/-- **Total rounding error of the un-rounded weights.** `∑ⱼ |rsoftmax z j − rexp z j/rdenom z| ≤ u·(∑ⱼ ẽⱼ)/D̃`. -/
lemma sum_abs_rsoftmax_sub_qtilde_le {n : ℕ} (z : Fin n → ℝ) (h : RsoftmaxNormal z)
    (hden : 0 < rdenom z) :
    ∑ j, |rsoftmax z j - rexp z j / rdenom z| ≤ u * (rexpSum z / rdenom z) := by
  have hstep : ∀ j, |rsoftmax z j - rexp z j / rdenom z| ≤ u * (rexp z j / rdenom z) := by
    intro j
    have hb := fp32Round_rel_on_normal (rexp z j / rdenom z) (h.2.2 j).1 (h.2.2 j).2
    rw [show neuralBpow binaryRadix (-24) = u from rfl] at hb
    have hpos : 0 ≤ rexp z j / rdenom z := div_nonneg (rexp_nonneg z h j) hden.le
    rw [abs_of_nonneg hpos] at hb
    show |fp32Round (rexp z j / rdenom z) - rexp z j / rdenom z| ≤ u * (rexp z j / rdenom z)
    exact hb
  calc ∑ j, |rsoftmax z j - rexp z j / rdenom z|
      ≤ ∑ j, u * (rexp z j / rdenom z) := Finset.sum_le_sum (fun j _ => hstep j)
    _ = u * (rexpSum z / rdenom z) := by
        rw [← Finset.mul_sum, ← Finset.sum_div, rexpSum]

/-\! ### Closed-form softmax-weight total-variation bound -/

/-- The closed-form denominator fold budget at the exp upper bound `E` (so `D = ∑exp ≤ n·E`):
`u·(n+1)·(1+u)·(n·E)/(1−n·u)`. -/
noncomputable def denomBudget (n : ℕ) (E : ℝ) : ℝ :=
  u * (((n : ℝ) + 1) * ((1 + u) * ((n : ℝ) * E))) / (1 - (n : ℝ) * u)

/-- The denominator fold budget is nonnegative when `0 ≤ E` and `n·u < 1`. -/
lemma denomBudget_nonneg {n : ℕ} (hnu : (n : ℝ) * u < 1) {E : ℝ} (hE : 0 ≤ E) :
    0 ≤ denomBudget n E := by
  have hpos : 0 < 1 - (n : ℝ) * u := by linarith
  unfold denomBudget
  apply div_nonneg _ hpos.le
  have : 0 ≤ u := u_nonneg
  positivity

/-- The exact denominator is bounded by `n·E` under an exp upper bound `E`. -/
lemma expSum_le {n : ℕ} (z : Fin n → ℝ) {E : ℝ} (hE : ∀ j, Real.exp (z j) ≤ E) :
    expSum z ≤ (n : ℝ) * E := by
  calc expSum z = ∑ j, Real.exp (z j) := rfl
    _ ≤ ∑ _j : Fin n, E := Finset.sum_le_sum (fun j _ => hE j)
    _ = (n : ℝ) * E := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The denominator-fold error in closed form: `|D̃ − ∑ẽⱼ| ≤ denomBudget n E`. -/
lemma abs_rdenom_sub_rexpSum_le_closed {n : ℕ} (z : Fin n → ℝ) (h : RsoftmaxNormal z)
    (hnu : (n : ℝ) * u < 1) {E : ℝ} (hE : ∀ j, Real.exp (z j) ≤ E) :
    |rdenom z - rexpSum z| ≤ denomBudget n E := by
  refine (abs_rdenom_sub_rexpSum_le z h hnu).trans ?_
  have hpos : 0 < 1 - (n : ℝ) * u := by linarith
  have hu0 : 0 ≤ u := u_nonneg
  have hu1 : (0 : ℝ) ≤ 1 + u := by linarith
  have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  unfold denomBudget
  gcongr
  exact expSum_le z hE

/-- **Closed-form total softmax-weight error.** With the exp upper bound `E` and a positive lower bound
`Dlo ≤ D̃` on the rounded denominator (the surfaced no-underflow hypothesis), the rounded softmax weights
differ from the exact softmax weights by at most
`softmaxTV n E Dlo = u + (u·denomBudget n E + 2·u·(n·E) + denomBudget n E)/Dlo` in total. -/
noncomputable def softmaxTV (n : ℕ) (E Dlo : ℝ) : ℝ :=
  u + (u * denomBudget n E + 2 * u * ((n : ℝ) * E) + denomBudget n E) / Dlo

/-- The total softmax-weight error is bounded by `softmaxTV n E Dlo`. -/
lemma sum_abs_rsoftmax_sub_softmax_le {n : ℕ} [NeZero n] (z : Fin n → ℝ) (h : RsoftmaxNormal z)
    (hnu : (n : ℝ) * u < 1) {E Dlo : ℝ} (hE : ∀ j, Real.exp (z j) ≤ E)
    (hDlo0 : 0 < Dlo) (hDlo : Dlo ≤ rdenom z) :
    ∑ j, |rsoftmax z j - softmax z j| ≤ softmaxTV n E Dlo := by
  have hden : 0 < rdenom z := lt_of_lt_of_le hDlo0 hDlo
  have hD : 0 < expSum z := expSum_pos z
  have hEnn : 0 ≤ E := by
    have j0 : Fin n := Classical.arbitrary (Fin n)
    exact le_trans (Real.exp_pos (z j0)).le (hE j0)
  have hdb : 0 ≤ denomBudget n E := denomBudget_nonneg hnu hEnn
  have htri : ∑ j, |rsoftmax z j - softmax z j|
      ≤ ∑ j, |rsoftmax z j - rexp z j / rdenom z|
        + ∑ j, |rexp z j / rdenom z - softmax z j| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => abs_sub_le _ _ _)
  have hT1 := sum_abs_rsoftmax_sub_qtilde_le z h hden
  have hT2 := sum_abs_qtilde_sub_softmax_le z h hden
  have hdenomsub : |rdenom z - rexpSum z| ≤ denomBudget n E :=
    abs_rdenom_sub_rexpSum_le_closed z h hnu hE
  have hrexpsub : |rexpSum z - expSum z| ≤ u * expSum z := abs_rexpSum_sub_le z h
  have hexpnE : expSum z ≤ (n : ℝ) * E := expSum_le z hE
  -- piece 1
  have hrexpsum_le : rexpSum z ≤ rdenom z + denomBudget n E := by
    have := (abs_le.mp hdenomsub).1; linarith
  have hratio1 : rexpSum z / rdenom z ≤ 1 + denomBudget n E / Dlo := by
    have hstep : rexpSum z / rdenom z ≤ (rdenom z + denomBudget n E) / rdenom z := by
      gcongr
    rw [add_div, div_self (ne_of_gt hden)] at hstep
    have hstep2 : denomBudget n E / rdenom z ≤ denomBudget n E / Dlo :=
      div_le_div_of_nonneg_left hdb hDlo0 hDlo
    linarith
  have hpiece1 : u * (rexpSum z / rdenom z) ≤ u + u * denomBudget n E / Dlo := by
    have := mul_le_mul_of_nonneg_left hratio1 u_nonneg
    calc u * (rexpSum z / rdenom z) ≤ u * (1 + denomBudget n E / Dlo) := this
      _ = u + u * denomBudget n E / Dlo := by ring
  -- piece 2
  have hdenom_exp_sub : |rdenom z - expSum z| ≤ denomBudget n E + u * ((n : ℝ) * E) := by
    calc |rdenom z - expSum z| ≤ |rdenom z - rexpSum z| + |rexpSum z - expSum z| := by
          have := abs_sub_le (rdenom z) (rexpSum z) (expSum z); linarith
      _ ≤ denomBudget n E + u * expSum z := by linarith
      _ ≤ denomBudget n E + u * ((n : ℝ) * E) := by
          have : u * expSum z ≤ u * ((n : ℝ) * E) := mul_le_mul_of_nonneg_left hexpnE u_nonneg
          linarith
  have hnum2 : u * expSum z + |rdenom z - expSum z|
      ≤ 2 * u * ((n : ℝ) * E) + denomBudget n E := by
    have h1 : u * expSum z ≤ u * ((n : ℝ) * E) := mul_le_mul_of_nonneg_left hexpnE u_nonneg
    nlinarith [hdenom_exp_sub, h1]
  have hnum2nn : 0 ≤ u * expSum z + |rdenom z - expSum z| :=
    add_nonneg (mul_nonneg u_nonneg hD.le) (abs_nonneg _)
  have hpiece2 : (u * expSum z + |rdenom z - expSum z|) / rdenom z
      ≤ (2 * u * ((n : ℝ) * E) + denomBudget n E) / Dlo := by
    calc (u * expSum z + |rdenom z - expSum z|) / rdenom z
        ≤ (2 * u * ((n : ℝ) * E) + denomBudget n E) / rdenom z := by gcongr
      _ ≤ (2 * u * ((n : ℝ) * E) + denomBudget n E) / Dlo := by
          have hnn : 0 ≤ 2 * u * ((n : ℝ) * E) + denomBudget n E := by
            have : 0 ≤ 2 * u * ((n : ℝ) * E) := by
              have : 0 ≤ u := u_nonneg
              positivity
            linarith
          exact div_le_div_of_nonneg_left hnn hDlo0 hDlo
  -- combine
  rw [softmaxTV]
  have hcomb : ∑ j, |rsoftmax z j - softmax z j|
      ≤ (u + u * denomBudget n E / Dlo)
        + (2 * u * ((n : ℝ) * E) + denomBudget n E) / Dlo := by
    calc ∑ j, |rsoftmax z j - softmax z j|
        ≤ u * (rexpSum z / rdenom z)
          + (u * expSum z + |rdenom z - expSum z|) / rdenom z := by linarith [htri, hT1, hT2]
      _ ≤ (u + u * denomBudget n E / Dlo)
          + (2 * u * ((n : ℝ) * E) + denomBudget n E) / Dlo := add_le_add hpiece1 hpiece2
  refine hcomb.trans ?_
  rw [add_div, add_div]
  ring_nf
  rfl

/-\! ### The rounded value mix and its error (T_mix) -/

/-- The executed output coordinate for a row: the rounded dot product of the rounded softmax weights
against the rounded value column. -/
def omixRow {n d : ℕ} (z : Fin n → ℝ) (V : Fin n → Fin d → ℝ) (c : Fin d) : ℝ :=
  rdot (rsoftmax z) (fun j => V j c)

/-- The sum of rounded softmax weights is within `softmaxTV` of `1`. -/
lemma rsoftmax_sum_le {n : ℕ} [NeZero n] (z : Fin n → ℝ) (h : RsoftmaxNormal z)
    (hnu : (n : ℝ) * u < 1) {E Dlo : ℝ} (hE : ∀ j, Real.exp (z j) ≤ E)
    (hDlo0 : 0 < Dlo) (hDlo : Dlo ≤ rdenom z) :
    ∑ j, |rsoftmax z j| ≤ 1 + softmaxTV n E Dlo := by
  have htv := sum_abs_rsoftmax_sub_softmax_le z h hnu hE hDlo0 hDlo
  calc ∑ j, |rsoftmax z j|
      ≤ ∑ j, (|rsoftmax z j - softmax z j| + |softmax z j|) :=
        Finset.sum_le_sum (fun j _ => by
          have h := abs_add_le (rsoftmax z j - softmax z j) (softmax z j)
          rw [sub_add_cancel] at h; exact h)
    _ = ∑ j, |rsoftmax z j - softmax z j| + ∑ j, |softmax z j| := by rw [Finset.sum_add_distrib]
    _ = ∑ j, |rsoftmax z j - softmax z j| + 1 := by
        congr 1
        rw [show (∑ j, |softmax z j|) = ∑ j, softmax z j from
          Finset.sum_congr rfl (fun j _ => abs_of_nonneg (softmax_nonneg z j)), softmax_sum_one]
    _ ≤ softmaxTV n E Dlo + 1 := by linarith
    _ = 1 + softmaxTV n E Dlo := by ring

/-- **The value-mix rounding error (T_mix).** With the rounded value entries bounded by `bV`, the
executed output coordinate `omixRow z̃ Ṽ c` is within
`rdotBudget n (bV·(1+softmaxTV)) + bV·softmaxTV` of the exact softmax-mix `∑ⱼ softmax z̃ⱼ · Ṽⱼc`. -/
lemma omixRow_error {n d : ℕ} [NeZero n] (z : Fin n → ℝ) (V : Fin n → Fin d → ℝ) (c : Fin d)
    (h : RsoftmaxNormal z) (hmix : RdotNormal (rsoftmax z) (fun j => V j c))
    (hnu : (n : ℝ) * u < 1) {E Dlo bV : ℝ} (hbV0 : 0 ≤ bV) (hbV : ∀ j, |V j c| ≤ bV)
    (hE : ∀ j, Real.exp (z j) ≤ E) (hDlo0 : 0 < Dlo) (hDlo : Dlo ≤ rdenom z) :
    |omixRow z V c - ∑ j, softmax z j * V j c|
      ≤ rdotBudget n (bV * (1 + softmaxTV n E Dlo)) + bV * softmaxTV n E Dlo := by
  have htv := sum_abs_rsoftmax_sub_softmax_le z h hnu hE hDlo0 hDlo
  have hsumw := rsoftmax_sum_le z h hnu hE hDlo0 hDlo
  -- mix-fold magnitude bound
  have hPbound : ∑ j, |(rsoftmax z) j * (fun j => V j c) j| ≤ bV * (1 + softmaxTV n E Dlo) := by
    calc ∑ j, |(rsoftmax z) j * (fun j => V j c) j|
        = ∑ j, |rsoftmax z j| * |V j c| := by
          refine Finset.sum_congr rfl (fun j _ => ?_); rw [abs_mul]
      _ ≤ ∑ j, |rsoftmax z j| * bV :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hbV j) (abs_nonneg _))
      _ = (∑ j, |rsoftmax z j|) * bV := by rw [Finset.sum_mul]
      _ ≤ (1 + softmaxTV n E Dlo) * bV := mul_le_mul_of_nonneg_right hsumw hbV0
      _ = bV * (1 + softmaxTV n E Dlo) := by ring
  have hfoldmix : |omixRow z V c - ∑ j, (rsoftmax z) j * (fun j => V j c) j|
      ≤ rdotBudget n (bV * (1 + softmaxTV n E Dlo)) :=
    rdot_error_le_of_sum_bound (rsoftmax z) (fun j => V j c) hmix hnu hPbound
  -- weight error propagated through the mix
  have hweight : |∑ j, rsoftmax z j * V j c - ∑ j, softmax z j * V j c| ≤ bV * softmaxTV n E Dlo := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ j, (rsoftmax z j * V j c - softmax z j * V j c)|
        ≤ ∑ j, |rsoftmax z j * V j c - softmax z j * V j c| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |rsoftmax z j - softmax z j| * |V j c| := by
          refine Finset.sum_congr rfl (fun j _ => ?_); rw [← sub_mul, abs_mul]
      _ ≤ ∑ j, |rsoftmax z j - softmax z j| * bV :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hbV j) (abs_nonneg _))
      _ = (∑ j, |rsoftmax z j - softmax z j|) * bV := by rw [Finset.sum_mul]
      _ ≤ softmaxTV n E Dlo * bV := mul_le_mul_of_nonneg_right htv hbV0
      _ = bV * softmaxTV n E Dlo := by ring
  calc |omixRow z V c - ∑ j, softmax z j * V j c|
      ≤ |omixRow z V c - ∑ j, (rsoftmax z) j * (fun j => V j c) j|
          + |∑ j, rsoftmax z j * V j c - ∑ j, softmax z j * V j c| := by
        have := abs_sub_le (omixRow z V c) (∑ j, (rsoftmax z) j * (fun j => V j c) j)
          (∑ j, softmax z j * V j c)
        simpa using this
    _ ≤ rdotBudget n (bV * (1 + softmaxTV n E Dlo)) + bV * softmaxTV n E Dlo :=
        add_le_add hfoldmix hweight

/-\! ### Auxiliary bounds for the row assembly -/

/-- The exact value-row entry is bounded by `B·Λ`. -/
lemma matMulCoord_entry_abs_le {n d : ℕ} (W : Fin d → Fin d → ℝ) (X : Fin n → Fin d → ℝ)
    {B Λ : ℝ} (hB : 0 ≤ B) (hX : ∀ i k, |X i k| ≤ B) (hW : ∀ j, ∑ k, |W k j| ≤ Λ)
    (i : Fin n) (j : Fin d) : |matMulCoord W X i j| ≤ B * Λ := by
  calc |matMulCoord W X i j| = |∑ k, X i k * W k j| := by rw [matMulCoord]
    _ ≤ ∑ k, |X i k * W k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |X i k| * |W k j| := by
        refine Finset.sum_congr rfl (fun k _ => ?_); rw [abs_mul]
    _ ≤ ∑ k, B * |W k j| :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hX i k) (abs_nonneg _))
    _ = B * ∑ k, |W k j| := by rw [Finset.mul_sum]
    _ ≤ B * Λ := mul_le_mul_of_nonneg_left (hW j) hB

/-- The rounded-value bound: `|Vexec W X i j| ≤ B·Λ + rdotBudget d (B·Λ) =: bVval`. -/
noncomputable def bVval (d : ℕ) (B Λ : ℝ) : ℝ := B * Λ + rdotBudget d (B * Λ)

/-- The executed value entry is bounded by `bVval d B Λ`. -/
lemma Vexec_entry_abs_le {n d : ℕ} (W : Fin d → Fin d → ℝ) (X : Fin n → Fin d → ℝ)
    {B Λ : ℝ} (hB : 0 ≤ B) (hΛ0 : 0 ≤ Λ) (hX : ∀ i k, |X i k| ≤ B) (hW : ∀ j, ∑ k, |W k j| ≤ Λ)
    (hnorm : VexecNormal W X) (hdu : (d : ℝ) * u < 1) (i : Fin n) (j : Fin d) :
    |Vexec W X i j| ≤ bVval d B Λ := by
  have hentry := Vexec_entry_error W X hB hΛ0 hX hW hnorm hdu i j
  have hideal := matMulCoord_entry_abs_le W X hB hX hW i j
  calc |Vexec W X i j|
      = |(Vexec W X i j - matMulCoord W X i j) + matMulCoord W X i j| := by ring_nf
    _ ≤ |Vexec W X i j - matMulCoord W X i j| + |matMulCoord W X i j| := abs_add_le _ _
    _ ≤ rdotBudget d (B * Λ) + B * Λ := by linarith
    _ = bVval d B Λ := by rw [bVval]; ring

/-- The exact score-entry magnitude is bounded by `d·B²/scale`. -/
lemma attnScores_entry_abs_le {n d : ℕ} (scale : ℝ) (X : Fin n → Fin d → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hscale : 0 < scale) (hX : ∀ i k, |X i k| ≤ B) (i k' : Fin n) :
    |attnScores scale (X i) X k'| ≤ (d : ℝ) * B ^ 2 / scale := by
  rw [attnScores, abs_div, abs_of_pos hscale, div_le_div_iff_of_pos_right hscale]
  calc |∑ e, (X i) e * X k' e| ≤ ∑ e, |(X i) e * X k' e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ (d : ℝ) * B ^ 2 := score_dot_sum_le X hB hX i k'

/-- The rounded-score magnitude is bounded by `d·B²/scale + scoreErr d B scale =: scoreBoundExec`. -/
noncomputable def scoreBoundExec (d : ℕ) (B scale : ℝ) : ℝ :=
  (d : ℝ) * B ^ 2 / scale + scoreErr d B scale

/-- The executed score-entry magnitude is bounded by `scoreBoundExec d B scale`. -/
lemma Sexec_entry_abs_le {n d : ℕ} (scale : ℝ) (X : Fin n → Fin d → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hscale : 0 < scale) (hX : ∀ i k, |X i k| ≤ B)
    (hnorm : SexecNormal scale X) (hdu : (d : ℝ) * u < 1) (i k' : Fin n) :
    |Sexec scale X i k'| ≤ scoreBoundExec d B scale := by
  have hentry := Sexec_entry_error scale X hB hscale hX hnorm hdu i k'
  have hideal := attnScores_entry_abs_le scale X hB hscale hX i k'
  calc |Sexec scale X i k'|
      = |(Sexec scale X i k' - attnScores scale (X i) X k') + attnScores scale (X i) X k'| := by
        ring_nf
    _ ≤ |Sexec scale X i k' - attnScores scale (X i) X k'| + |attnScores scale (X i) X k'| :=
        abs_add_le _ _
    _ ≤ scoreErr d B scale + (d : ℝ) * B ^ 2 / scale := by linarith
    _ = scoreBoundExec d B scale := by rw [scoreBoundExec]; ring

/-\! ## The executed forward and its per-coordinate error -/

/-- The exp upper bound on the rounded scores: `E = exp(scoreBoundExec)`. Derived from the rounded
score-magnitude bound. -/
noncomputable def expBoundExec (d : ℕ) (B scale : ℝ) : ℝ := Real.exp (scoreBoundExec d B scale)

/-- The derived rounding envelope `rnd⋆` for one attention head: the sum of the value-mix, softmax,
score, and value-projection rounding contributions. `Dlo` is the surfaced positive lower bound on the
rounded softmax denominators. -/
noncomputable def rndStar (n d : ℕ) (B Λ scale Dlo : ℝ) : ℝ :=
  rdotBudget n (bVval d B Λ * (1 + softmaxTV n (expBoundExec d B scale) Dlo))
    + bVval d B Λ * softmaxTV n (expBoundExec d B scale) Dlo
    + 2 * bVval d B Λ * scoreErr d B scale
    + rdotBudget d (B * Λ)

/-- The executed (rounded) attention head, evaluated on the clamped input. Each output coordinate is the
rounded value mix of the rounded softmax of the rounded scores against the rounded value rows. Read over
`ℝ`, this is the literal binary32 `attnHead` (every op = real op + one rounding step). -/
def execAttnStar {n d : ℕ} (scale : ℝ) (W : Fin d → Fin d → ℝ) (B : ℝ)
    (Y : Fin n → Fin d → ℝ) : Fin n → Fin d → ℝ :=
  fun i c => omixRow (Sexec scale (clampCoord B Y) i) (Vexec W (clampCoord B Y)) c

/-- The bundled normal/finiteness hypotheses for the executed head on input `Y` (clamped to `X`). All
are honest no-underflow/no-overflow conditions on the run-time intermediates of the binary32 forward;
`hDlo`/`hDlo0` are the surfaced softmax-denominator non-underflow assumption. -/
structure ExecAttnNormal {n d : ℕ} (scale : ℝ) (W : Fin d → Fin d → ℝ) (B Dlo : ℝ)
    (Y : Fin n → Fin d → ℝ) : Prop where
  /-- The value-projection reductions are normal. -/
  vnorm : VexecNormal W (clampCoord B Y)
  /-- The score reductions and score-divide rounds are normal. -/
  snorm : SexecNormal scale (clampCoord B Y)
  /-- The softmax exp/denominator/quotient rounds are normal, per query row. -/
  rnorm : ∀ i, RsoftmaxNormal (Sexec scale (clampCoord B Y) i)
  /-- The value-mix reductions are normal, per query row and output coordinate. -/
  mnorm : ∀ i c, RdotNormal (rsoftmax (Sexec scale (clampCoord B Y) i))
            (fun j => Vexec W (clampCoord B Y) j c)
  /-- A positive lower bound on each rounded softmax denominator (no-underflow). -/
  dpos : 0 < Dlo
  /-- The rounded softmax denominators stay above `Dlo`. -/
  dlo : ∀ i, Dlo ≤ rdenom (Sexec scale (clampCoord B Y) i)

/-- **Per-coordinate forward error of the executed head.** Each output coordinate of `execAttnStar` is
within `rndStar n d B Λ scale Dlo` of the ideal head `attnHead scale W (clampCoord B Y)`. -/
lemma execAttnStar_coord_error {n d : ℕ} [NeZero n] (scale : ℝ) (W : Fin d → Fin d → ℝ)
    {B Λ Dlo : ℝ} (hB : 0 ≤ B) (hΛ0 : 0 ≤ Λ) (hscale : 0 < scale)
    (hW : ∀ j, ∑ k, |W k j| ≤ Λ) (hnu : (n : ℝ) * u < 1) (hdu : (d : ℝ) * u < 1)
    (Y : Fin n → Fin d → ℝ) (hbundle : ExecAttnNormal scale W B Dlo Y) (i : Fin n) (c : Fin d) :
    |execAttnStar scale W B Y i c
        - attnHead scale W (clampCoord B Y) i c| ≤ rndStar n d B Λ scale Dlo := by
  set X : Fin n → Fin d → ℝ := clampCoord B Y with hX
  set zt : Fin n → ℝ := Sexec scale X i with hzt
  set z : Fin n → ℝ := attnScores scale (X i) X with hz
  set Vt : Fin n → Fin d → ℝ := Vexec W X with hVt
  set V : Fin n → Fin d → ℝ := matMulCoord W X with hV
  have hXcl : ∀ a k, |X a k| ≤ B := fun a k => abs_clampCoord_le hB Y a k
  set bV : ℝ := bVval d B Λ with hbV
  set E : ℝ := expBoundExec d B scale with hE
  have hbV0 : 0 ≤ bV := by
    rw [hbV, bVval]
    have h1 : 0 ≤ rdotBudget d (B * Λ) := rdotBudget_nonneg hdu (mul_nonneg hB hΛ0)
    have h2 : 0 ≤ B * Λ := mul_nonneg hB hΛ0
    linarith
  -- value entries bounded by bV
  have hVtabs : ∀ jc : Fin n, |Vt jc c| ≤ bV := fun jc =>
    Vexec_entry_abs_le W X hB hΛ0 hXcl hW hbundle.vnorm hdu jc c
  -- exp bound on rounded scores
  have hEbound : ∀ j, Real.exp (zt j) ≤ E := by
    intro j
    have hsj : zt j ≤ scoreBoundExec d B scale :=
      le_trans (le_abs_self _) (Sexec_entry_abs_le scale X hB hscale hXcl hbundle.snorm hdu i j)
    rw [hE, expBoundExec]
    exact Real.exp_le_exp.mpr hsj
  -- T_mix
  have hTmix : |omixRow zt Vt c - ∑ j, softmax zt j * Vt j c|
      ≤ rdotBudget n (bV * (1 + softmaxTV n E Dlo)) + bV * softmaxTV n E Dlo :=
    omixRow_error zt Vt c (hbundle.rnorm i) (hbundle.mnorm i c) hnu hbV0 hVtabs hEbound
      hbundle.dpos (hbundle.dlo i)
  -- T_score : exact softmax of zt vs z, values Vt
  have hTscore : |(∑ j, softmax zt j * Vt j c) - ∑ j, softmax z j * Vt j c|
      ≤ 2 * bV * scoreErr d B scale := by
    have hsb := attnOut_scores_bound zt z Vt c hbV0 hVtabs
    simp only [attnOut] at hsb
    refine hsb.trans ?_
    have hscErrnn : 0 ≤ scoreErr d B scale := scoreErr_nonneg hB hdu hscale
    have hzz : ‖zt - z‖ ≤ scoreErr d B scale := by
      refine (pi_norm_le_iff_of_nonneg hscErrnn).mpr (fun k' => ?_)
      rw [Real.norm_eq_abs, Pi.sub_apply, hzt, hz]
      exact Sexec_entry_error scale X hB hscale hXcl hbundle.snorm hdu i k'
    have : 2 * bV * ‖zt - z‖ ≤ 2 * bV * scoreErr d B scale :=
      mul_le_mul_of_nonneg_left hzz (by positivity)
    exact this
  -- T_val : exact softmax of z, values Vt vs V
  have hTval : |(∑ j, softmax z j * Vt j c) - ∑ j, softmax z j * V j c|
      ≤ rdotBudget d (B * Λ) := by
    have hvb := attnOut_values_bound z Vt V c (bd := ‖Vt - V‖) (fun jc => by
      have h1 : |Vt jc c - V jc c| ≤ ‖(Vt - V) jc‖ := by
        rw [show Vt jc c - V jc c = (Vt - V) jc c from rfl, ← Real.norm_eq_abs]
        exact norm_le_pi_norm _ c
      exact le_trans h1 (norm_le_pi_norm _ jc))
    simp only [attnOut] at hvb
    refine hvb.trans ?_
    rw [hVt, hV]
    exact Vexec_error W X hB hΛ0 hXcl hW hbundle.vnorm hdu
  -- assemble
  have hgoal : execAttnStar scale W B Y i c = omixRow zt Vt c := by
    rw [execAttnStar, ← hX, ← hzt, ← hVt]
  have hideal : attnHead scale W X i c = ∑ j, softmax z j * V j c := by
    rw [attnHead, attnVec, attnOut, ← hz, ← hV]
  rw [hgoal, hideal]
  rw [rndStar, ← hbV, ← hE]
  calc |omixRow zt Vt c - ∑ j, softmax z j * V j c|
      ≤ |omixRow zt Vt c - ∑ j, softmax zt j * Vt j c|
          + |(∑ j, softmax zt j * Vt j c) - ∑ j, softmax z j * Vt j c|
          + |(∑ j, softmax z j * Vt j c) - ∑ j, softmax z j * V j c| := by
        have h1 := abs_sub_le (omixRow zt Vt c) (∑ j, softmax z j * Vt j c)
          (∑ j, softmax z j * V j c)
        have h2 := abs_sub_le (omixRow zt Vt c) (∑ j, softmax zt j * Vt j c)
          (∑ j, softmax z j * Vt j c)
        linarith
    _ ≤ (rdotBudget n (bV * (1 + softmaxTV n E Dlo)) + bV * softmaxTV n E Dlo)
          + 2 * bV * scoreErr d B scale + rdotBudget d (B * Λ) := by
        have := add_le_add (add_le_add hTmix hTscore) hTval; linarith

/-- The derived rounding envelope is nonnegative. -/
lemma rndStar_nonneg {n d : ℕ} {B Λ scale Dlo : ℝ} (hB : 0 ≤ B) (hΛ0 : 0 ≤ Λ)
    (hscale : 0 < scale) (hnu : (n : ℝ) * u < 1) (hdu : (d : ℝ) * u < 1) (hDlo0 : 0 < Dlo) :
    0 ≤ rndStar n d B Λ scale Dlo := by
  have hBΛ : 0 ≤ B * Λ := mul_nonneg hB hΛ0
  have hbV0 : 0 ≤ bVval d B Λ := by
    rw [bVval]; linarith [rdotBudget_nonneg hdu hBΛ]
  have hE : (0 : ℝ) ≤ expBoundExec d B scale := (Real.exp_pos _).le
  have hscErr : 0 ≤ scoreErr d B scale := scoreErr_nonneg hB hdu hscale
  have hdbd : 0 ≤ rdotBudget d (B * Λ) := rdotBudget_nonneg hdu hBΛ
  -- softmaxTV ≥ 0
  have htvnn : 0 ≤ softmaxTV n (expBoundExec d B scale) Dlo := by
    rw [softmaxTV]
    have hdb : 0 ≤ denomBudget n (expBoundExec d B scale) := denomBudget_nonneg hnu hE
    have hnum : 0 ≤ u * denomBudget n (expBoundExec d B scale)
        + 2 * u * ((n : ℝ) * expBoundExec d B scale) + denomBudget n (expBoundExec d B scale) := by
      have hu0 : 0 ≤ u := u_nonneg
      have : 0 ≤ 2 * u * ((n : ℝ) * expBoundExec d B scale) := by positivity
      have : 0 ≤ u * denomBudget n (expBoundExec d B scale) := mul_nonneg hu0 hdb
      positivity
    have : 0 ≤ (u * denomBudget n (expBoundExec d B scale)
        + 2 * u * ((n : ℝ) * expBoundExec d B scale) + denomBudget n (expBoundExec d B scale)) / Dlo :=
      div_nonneg hnum hDlo0.le
    linarith [u_nonneg]
  have hmixfold : 0 ≤ rdotBudget n (bVval d B Λ * (1 + softmaxTV n (expBoundExec d B scale) Dlo)) := by
    apply rdotBudget_nonneg hnu
    apply mul_nonneg hbV0; linarith
  rw [rndStar]
  have h2 : 0 ≤ bVval d B Λ * softmaxTV n (expBoundExec d B scale) Dlo := mul_nonneg hbV0 htvnn
  have h3 : 0 ≤ 2 * bVval d B Λ * scoreErr d B scale := by
    have : 0 ≤ 2 * bVval d B Λ := by linarith
    exact mul_nonneg this hscErr
  linarith

/-- **The derived attention forward-error bound.** For the executed head `execAttnStar` and any input
`Y` whose binary32 intermediates satisfy the bundled normal/finiteness conditions `ExecAttnNormal`, the
executed head is within the derived closed form `rndStar n d B Λ scale Dlo` of the ideal head
`attnHead scale W (clampCoord B Y)`. The `rnd⋆` is a genuine closed-form function of the bounds
`B, Λ, scale, Dlo` and the shapes `n, d` (via the unit roundoff `u = 2⁻²⁴`); nothing is supplied. -/
theorem attnForwardError {n d : ℕ} [NeZero n] (scale : ℝ) (W : Fin d → Fin d → ℝ)
    {B Λ Dlo : ℝ} (hB : 0 ≤ B) (hΛ0 : 0 ≤ Λ) (hscale : 0 < scale)
    (hW : ∀ j, ∑ k, |W k j| ≤ Λ) (hnu : (n : ℝ) * u < 1) (hdu : (d : ℝ) * u < 1)
    (Y : Fin n → Fin d → ℝ) (hbundle : ExecAttnNormal scale W B Dlo Y) :
    dist (execAttnStar scale W B Y) (attnHead scale W (clampCoord B Y))
      ≤ rndStar n d B Λ scale Dlo := by
  have hrnn : 0 ≤ rndStar n d B Λ scale Dlo :=
    rndStar_nonneg hB hΛ0 hscale hnu hdu hbundle.dpos
  refine (dist_pi_le_iff hrnn).mpr (fun i => ?_)
  refine (dist_pi_le_iff hrnn).mpr (fun c => ?_)
  rw [Real.dist_eq]
  exact execAttnStar_coord_error scale W hB hΛ0 hscale hW hnu hdu Y hbundle i c

/-\! ## The executed certificate, with the rounding hypothesis discharged -/

open MeasureTheory Capacity in
/-- **The certified computable float32 generalization bound for the executed attention head, with the
rounding envelope DERIVED.** Identical in conclusion to `attnHead_executed_certified_generalization`,
but the executed map is the concrete literal-fp32 head `execAttnStar` and the rounding bound is the
derived closed form `rndStar n d B Λ scale Dlo` — no free `rnd`, and the envelope hypothesis is
discharged by `attnForwardError` (so it is *proved*, not supplied). The only added inputs are honest
operating-range data: the weight `ℓ¹`-bound `Λ` (with `0 ≤ Λ`, `hW`), the positive scale `hscale`, the
length/dimension roundoff conditions `n·u < 1`, `d·u < 1`, and the bundled binary32
normal/no-overflow / softmax-denominator-no-underflow conditions `hnormAll` (carrying the positive
denominator floor `Dlo`). The bound is therefore entirely about the literal finite-precision attention
the hardware runs, with the rounding correction `2·Lℓ·rndStar` a closed form in the model's data. -/
theorem attnHead_executed_certified_generalization_derived
    {n d p m : ℕ} [NeZero n] [Nonempty (Fin p)]
    [MeasurableSpace (Fin n → Fin d → ℝ)] [BorelSpace (Fin n → Fin d → ℝ)]
    {P : Measure (Fin n → Fin d → ℝ)} [IsProbabilityMeasure P]
    (hm : 0 < m) {R B scale : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B) (hscale : 0 < scale)
    (Wdec : ParamSpace p → (Fin d → Fin d → ℝ)) (hWcont : Continuous Wdec)
    {Lw : ℝ} (hWLip : ∀ θ θ', dist (Wdec θ) (Wdec θ') ≤ Lw * dist θ θ')
    (ℓ : (Fin n → Fin d → ℝ) → ℝ) {b : ℝ} (hb : 0 < b) (hℓb : ∀ v, |ℓ v| ≤ b)
    (hℓcont : Continuous ℓ) {Lℓ : ℝ} (hLℓ0 : 0 ≤ Lℓ)
    (hℓLip : ∀ u v, |ℓ u - ℓ v| ≤ Lℓ * dist u v)
    {ε : ℝ} (hε : 0 ≤ ε) (w_T : BaseWeightPreimage Capacity.Dyadic R)
    {Λ Dlo : ℝ} (hΛ0 : 0 ≤ Λ)
    (hW : ∀ j, ∑ k, |Wdec (embedBase Capacity.Dyadic w_T.1) k j| ≤ Λ)
    (hnu : (n : ℝ) * u < 1) (hdu : (d : ℝ) * u < 1)
    {lip : ℝ} (hlip0 : 0 ≤ lip)
    (hideal_lip : ∀ a b : Fin n → Fin d → ℝ,
        dist (attnHead scale (Wdec (embedBase Capacity.Dyadic w_T.1)) (clampCoord B a))
             (attnHead scale (Wdec (embedBase Capacity.Dyadic w_T.1)) (clampCoord B b)) ≤ lip * dist a b)
    (hnormAll : ∀ Y : Fin n → Fin d → ℝ,
        ExecAttnNormal scale (Wdec (embedBase Capacity.Dyadic w_T.1)) B Dlo Y)
    (hintG : Integrable
        (fun x => ℓ (execAttnStar scale (Wdec (embedBase Capacity.Dyadic w_T.1)) B x)) P)
    (hLpos : 0 < Lℓ * ((d : ℝ) * B) * Lw) :
    (Measure.pi fun _ : Fin m => P).real
        {S | ¬ ((∫ x, ℓ (execAttnStar scale (Wdec (embedBase Capacity.Dyadic w_T.1)) B x) ∂P)
              ≤ (1 / (m : ℝ)) * ∑ i, ℓ (execAttnStar scale (Wdec (embedBase Capacity.Dyadic w_T.1)) B (S i))
                + (2 * ((12 * Real.sqrt 2) * (1 / Real.sqrt m)
                    * (∫⁻ ε in Set.Ioc (0 : ℝ) (2 * b),
                        ENNReal.ofReal (Real.sqrt (Real.log 2)
                          + Real.sqrt ((p : ℝ) * (4 * R * (Lℓ * ((d : ℝ) * B) * Lw)))
                            * ε ^ (-(1 / 2) : ℝ))).toReal) + ε)
                + 2 * (Lℓ * rndStar n d B Λ scale Dlo))}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * (2 * b / m) ^ 2)) :=
  TLT.attnHead_executed_certified_generalization hm hR hB Wdec hWcont hWLip ℓ hb hℓb hℓcont hLℓ0
    hℓLip hε w_T (execAttnStar scale (Wdec (embedBase Capacity.Dyadic w_T.1)) B) hlip0 hideal_lip
    (fun y => attnForwardError scale (Wdec (embedBase Capacity.Dyadic w_T.1)) hB hΛ0 hscale hW hnu hdu
      y (hnormAll y))
    hintG hLpos

end TLT.Fp32Attn
