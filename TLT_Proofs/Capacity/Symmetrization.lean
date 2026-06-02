/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TLT_Proofs.Capacity.RademacherSubGaussian

/-!
# Symmetrization: the in-expectation bound on the expected uniform deviation

The real-valued (in-expectation) symmetrization inequality bounds the expected uniform deviation
`E[sup_f (R_true(f) − R̂_emp(f))]` by twice the expected empirical Rademacher complexity. Its
load-bearing step is that, on the double sample `(S, S') ∼ P^m × P^m`, exchanging the paired
coordinates `Sᵢ ↔ S'ᵢ` (independently per coordinate, indexed by a sign vector) is measure-preserving
— because each factor `P` is symmetric under `Prod.swap`. Averaging over all `2^m` sign patterns turns
the ghost-sample difference into a Rademacher-signed sum, which the supremum's subadditivity and the
sign symmetry of the uniform sign measure split into two copies of the empirical Rademacher complexity.

The development is for a real-valued function class indexed by `ι`, with the loss family `g : ι → X → ℝ`
uniformly bounded; measurability of the supremum envelopes is carried as hypotheses (discharged, for a
separable index, where the family is used).

## Main results

- `swapAt` — swap the `i`-th paired coordinate of a double sample iff `σ i`.
- `measurePreserving_swapAt` — the swap preserves the double-sample product measure.
- `flipSign` / `integral_comp_flipSign` — flipping every sign preserves the uniform sign measure.
- `symmetrization_le` — the expected uniform deviation is at most twice the expected empirical
  Rademacher complexity.

## References

P. L. Bartlett and S. Mendelson, *Rademacher and Gaussian complexities*, JMLR 3 (2002);
M. Mohri, A. Rostamizadeh and A. Talwalkar, *Foundations of Machine Learning*, 2nd ed. (2018), Thm 3.3;
M. Ledoux and M. Talagrand, *Probability in Banach Spaces* (1991), §6.
-/

open MeasureTheory Real

noncomputable section

namespace TLT.Capacity

variable {X : Type*} [MeasurableSpace X] {P : Measure X} {m : ℕ}

/-- Swap the `i`-th paired coordinate of a double sample iff `σ i` is true. -/
def swapAt (σ : Fin m → Bool) (p : Fin m → X × X) : Fin m → X × X :=
  fun i => (if σ i then Prod.swap else id) (p i)

/-- The double-sample coordinate swap is measure-preserving: each factor `P` is symmetric under
`Prod.swap`, so swapping any subset of paired coordinates preserves `P^m × P^m`. -/
theorem measurePreserving_swapAt [IsProbabilityMeasure P] (σ : Fin m → Bool) :
    MeasurePreserving (swapAt σ) (Measure.pi fun _ : Fin m => P.prod P)
      (Measure.pi fun _ : Fin m => P.prod P) := by
  unfold swapAt
  apply measurePreserving_pi
  intro i
  by_cases h : σ i = true
  · rw [show (if σ i then (Prod.swap : X × X → X × X) else id) = Prod.swap from if_pos h]
    exact Measure.measurePreserving_swap
  · rw [show (if σ i then (Prod.swap : X × X → X × X) else id) = id from if_neg h]
    exact MeasurePreserving.id _

/-- The double-sample swap is measurable. -/
lemma measurable_swapAt (σ : Fin m → Bool) : Measurable (swapAt (X := X) σ) := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases h : σ i = true
  · simp only [swapAt, if_pos h]; exact measurable_swap.comp (measurable_pi_apply i)
  · simp only [swapAt, if_neg h]; exact measurable_pi_apply i

omit [MeasurableSpace X] in
/-- The double-sample swap is an involution: applying it twice (with the same sign vector) is the
identity, because `Prod.swap` and `id` are each their own inverse. -/
@[simp] lemma swapAt_swapAt (σ : Fin m → Bool) (p : Fin m → X × X) :
    swapAt σ (swapAt σ p) = p := by
  funext i
  show (if σ i then Prod.swap else id) ((if σ i then Prod.swap else id) (p i)) = p i
  cases hb : σ i with
  | false => simp
  | true => simp [Prod.swap_swap]

/-- The double-sample swap as a measurable equivalence (it is its own inverse). -/
def swapAtEquiv (σ : Fin m → Bool) : (Fin m → X × X) ≃ᵐ (Fin m → X × X) where
  toFun := swapAt σ
  invFun := swapAt σ
  left_inv := swapAt_swapAt σ
  right_inv := swapAt_swapAt σ
  measurable_toFun := measurable_swapAt σ
  measurable_invFun := measurable_swapAt σ

/-- Integration is invariant under the double-sample swap. -/
theorem integral_comp_swapAt [IsProbabilityMeasure P] (σ : Fin m → Bool)
    (F : (Fin m → X × X) → ℝ) :
    ∫ p, F (swapAt σ p) ∂(Measure.pi fun _ : Fin m => P.prod P)
      = ∫ p, F p ∂(Measure.pi fun _ : Fin m => P.prod P) :=
  (measurePreserving_swapAt σ).integral_comp (swapAtEquiv σ).measurableEmbedding F

/-! ### Algebra of the empirical Rademacher average and the sign flip -/

/-- A flipped sign contributes the opposite value. -/
lemma boolToSign_not (b : Bool) : boolToSign (!b) = - boolToSign b := by
  cases b <;> simp [boolToSign]

/-- The empirical Rademacher average is additive (here: subtractive) in the value vector. -/
lemma empRadVec_sub (v w : Fin m → ℝ) (σ : SignVector m) :
    empRadVec (v - w) σ = empRadVec v σ - empRadVec w σ := by
  simp only [empRadVec, empRad, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

/-- The empirical Rademacher average negates with the value vector. -/
lemma empRadVec_neg (v : Fin m → ℝ) (σ : SignVector m) :
    empRadVec (-v) σ = - empRadVec v σ := by
  simp only [empRadVec, empRad, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, mul_neg]

/-- Flip every sign of a sign vector. -/
def flipSign (σ : SignVector m) : SignVector m := fun j => !(σ j)

@[simp] lemma flipSign_flipSign (σ : SignVector m) : flipSign (flipSign σ) = σ := by
  funext j; simp [flipSign]

/-- Flipping every sign is an involutive self-equivalence of the sign-vector space. -/
def flipSignEquiv : SignVector m ≃ SignVector m where
  toFun := flipSign
  invFun := flipSign
  left_inv := flipSign_flipSign
  right_inv := flipSign_flipSign

/-- The uniform sign measure is invariant under flipping every sign (it is a self-bijection of the
finite sign-vector space, which preserves the counting measure). -/
lemma integral_comp_flipSign (F : SignVector m → ℝ) :
    ∫ σ, F (flipSign σ) ∂(radMeasure m) = ∫ σ, F σ ∂(radMeasure m) := by
  rw [integral_radMeasure, integral_radMeasure]
  congr 1
  exact Equiv.sum_comp flipSignEquiv F

/-- The empirical Rademacher average flips sign when every sign is flipped. -/
lemma empRadVec_flipSign (v : Fin m → ℝ) (σ : SignVector m) :
    empRadVec v (flipSign σ) = - empRadVec v σ := by
  have h : ∀ i, v i * boolToSign ((flipSign σ) i) = -(v i * boolToSign (σ i)) := by
    intro i; rw [flipSign, boolToSign_not]; ring
  simp only [empRadVec, empRad]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_neg_distrib, mul_neg]

/-! ### True risk, empirical mean, and the ghost-sample identity -/

/-- The true risk (population mean) of `g` under the measure `μ`. -/
def trueRisk (μ : Measure X) (g : X → ℝ) : ℝ := ∫ x, g x ∂μ

/-- The empirical mean of `g` over a sample `S : Fin m → X`. -/
def empMean (g : X → ℝ) (S : Fin m → X) : ℝ := (1 / (m : ℝ)) * ∑ j, g (S j)

/-- **Ghost-sample identity.** The true risk equals the expected empirical mean over an independent
sample `S ∼ P^m`: each coordinate `S j` has law `P`, so `E_S[(1/m)∑ⱼ g(Sⱼ)] = E[g]`. -/
lemma trueRisk_eq_integral_empMean [IsProbabilityMeasure P] (hm : 0 < m) (g : X → ℝ)
    (hg : Integrable g P) :
    trueRisk P g = ∫ S, empMean g S ∂(Measure.pi fun _ : Fin m => P) := by
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hint : ∀ j : Fin m,
      Integrable (fun S : Fin m → X => g (S j)) (Measure.pi fun _ : Fin m => P) :=
    fun j => integrable_comp_eval hg
  have heval : ∀ j : Fin m,
      ∫ S, g (S j) ∂(Measure.pi fun _ : Fin m => P) = ∫ x, g x ∂P :=
    fun j => integral_comp_eval hg.aestronglyMeasurable
  unfold trueRisk empMean
  rw [integral_const_mul, integral_finset_sum _ (fun j _ => hint j),
    Finset.sum_congr rfl (fun j _ => heval j), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, one_div, ← mul_assoc, inv_mul_cancel₀ hmne, one_mul]

/-! ### Uniform bounds (supplying `BddAbove` for the suprema and integrability) -/

/-- The empirical Rademacher average is bounded by the value bound, since `|boolToSign| = 1`. -/
lemma empRadVec_abs_le (hm : 0 < m) {v : Fin m → ℝ} {b : ℝ} (hv : ∀ i, |v i| ≤ b)
    (σ : SignVector m) : |empRadVec v σ| ≤ b := by
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  simp only [empRadVec, empRad]
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (m : ℝ))]
  calc (1 / (m:ℝ)) * |∑ i, v i * boolToSign (σ i)|
      ≤ (1 / (m:ℝ)) * ∑ i, |v i * boolToSign (σ i)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (1 / (m:ℝ)) * ∑ _i : Fin m, b := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
        rw [abs_mul, boolToSign_abs_eq_one, mul_one]; exact hv i
    _ = b := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_div,
          ← mul_assoc, inv_mul_cancel₀ hmne, one_mul]

omit [MeasurableSpace X] in
/-- The empirical mean is bounded by the value bound. -/
lemma empMean_abs_le (hm : 0 < m) {g : X → ℝ} {b : ℝ} (hg : ∀ x, |g x| ≤ b) (S : Fin m → X) :
    |empMean g S| ≤ b := by
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  unfold empMean
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (m : ℝ))]
  calc (1 / (m:ℝ)) * |∑ j, g (S j)|
      ≤ (1 / (m:ℝ)) * ∑ j, |g (S j)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (1 / (m:ℝ)) * ∑ _j : Fin m, b :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hg (S j)) (by positivity)
    _ = b := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_div,
          ← mul_assoc, inv_mul_cancel₀ hmne, one_mul]

/-- The true risk is bounded by the value bound (a probability average of bounded values). -/
lemma trueRisk_abs_le [IsProbabilityMeasure P] {g : X → ℝ} {b : ℝ} (hg : Integrable g P)
    (hb : ∀ x, |g x| ≤ b) : |trueRisk P g| ≤ b := by
  unfold trueRisk
  calc |∫ x, g x ∂P| ≤ ∫ x, |g x| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ _x, b ∂P := integral_mono hg.abs (integrable_const b) hb
    _ = b := by rw [integral_const]; simp

/-! ### Supremum subadditivity and the coordinate projections of the double sample -/

/-- Subadditivity of the conditional supremum across a difference: `⨆(xᵢ−yᵢ) ≤ ⨆xᵢ + ⨆(−yᵢ)`. -/
lemma ciSup_sub_le {ι : Type*} [Nonempty ι] {x y : ι → ℝ}
    (hx : BddAbove (Set.range x)) (hy : BddAbove (Set.range fun i => - y i)) :
    ⨆ i, (x i - y i) ≤ (⨆ i, x i) + ⨆ i, (- y i) := by
  refine ciSup_le fun i => ?_
  have h1 : x i ≤ ⨆ i, x i := le_ciSup hx i
  have h2 : - y i ≤ ⨆ i, (- y i) := le_ciSup hy i
  calc x i - y i = x i + (- y i) := by ring
    _ ≤ (⨆ i, x i) + ⨆ i, (- y i) := add_le_add h1 h2

/-- Extracting the first coordinate of every pair is measure-preserving from the double sample
`(P×P)^m` onto `P^m` (compose the pi/prod regrouping with the first projection). -/
lemma measurePreserving_fstCoord [IsProbabilityMeasure P] :
    MeasurePreserving (fun p : Fin m → X × X => fun j => (p j).1)
      (Measure.pi fun _ : Fin m => P.prod P) (Measure.pi fun _ : Fin m => P) :=
  (measurePreserving_fst (μ := Measure.pi fun _ : Fin m => P)
    (ν := Measure.pi fun _ : Fin m => P)).comp
    (measurePreserving_arrowProdEquivProdArrow X X (Fin m) (fun _ => P) (fun _ => P))

/-- Extracting the second coordinate of every pair is measure-preserving from `(P×P)^m` onto `P^m`. -/
lemma measurePreserving_sndCoord [IsProbabilityMeasure P] :
    MeasurePreserving (fun p : Fin m → X × X => fun j => (p j).2)
      (Measure.pi fun _ : Fin m => P.prod P) (Measure.pi fun _ : Fin m => P) :=
  (measurePreserving_snd (μ := Measure.pi fun _ : Fin m => P)
    (ν := Measure.pi fun _ : Fin m => P)).comp
    (measurePreserving_arrowProdEquivProdArrow X X (Fin m) (fun _ => P) (fun _ => P))

/-- Integration of a function of the first coordinates over the double sample reduces to integration
over a single sample. -/
lemma integral_comp_fstCoord [IsProbabilityMeasure P] {F : (Fin m → X) → ℝ}
    (hF : AEStronglyMeasurable F (Measure.pi fun _ : Fin m => P)) :
    ∫ p, F (fun j => (p j).1) ∂(Measure.pi fun _ : Fin m => P.prod P)
      = ∫ S, F S ∂(Measure.pi fun _ : Fin m => P) := by
  rw [← (measurePreserving_fstCoord (P := P) (m := m)).map_eq] at hF ⊢
  rw [integral_map (measurePreserving_fstCoord (P := P) (m := m)).measurable.aemeasurable hF]

/-- Integration of a function of the second coordinates over the double sample reduces to integration
over a single sample. -/
lemma integral_comp_sndCoord [IsProbabilityMeasure P] {F : (Fin m → X) → ℝ}
    (hF : AEStronglyMeasurable F (Measure.pi fun _ : Fin m => P)) :
    ∫ p, F (fun j => (p j).2) ∂(Measure.pi fun _ : Fin m => P.prod P)
      = ∫ S, F S ∂(Measure.pi fun _ : Fin m => P) := by
  rw [← (measurePreserving_sndCoord (P := P) (m := m)).map_eq] at hF ⊢
  rw [integral_map (measurePreserving_sndCoord (P := P) (m := m)).measurable.aemeasurable hF]

/-! ### The swap computation: the paired swap turns the ghost gap into a Rademacher sum -/

omit [MeasurableSpace X] in
/-- The double-sample swap turns the (second − first) empirical-mean difference into a Rademacher sum:
swapping the `j`-th pair negates the `j`-th contribution exactly as the sign `boolToSign (σ j)` does. -/
lemma swap_empMean_diff (g : X → ℝ) (σ : SignVector m) (p : Fin m → X × X) :
    empMean g (fun j => ((swapAt σ p) j).2) - empMean g (fun j => ((swapAt σ p) j).1)
      = empRadVec (fun j => g (p j).1) σ - empRadVec (fun j => g (p j).2) σ := by
  have key : ∀ j, g ((swapAt σ p) j).2 - g ((swapAt σ p) j).1
      = g (p j).1 * boolToSign (σ j) - g (p j).2 * boolToSign (σ j) := by
    intro j
    show g ((if σ j then Prod.swap else id) (p j)).2 - g ((if σ j then Prod.swap else id) (p j)).1
       = g (p j).1 * boolToSign (σ j) - g (p j).2 * boolToSign (σ j)
    cases hb : σ j with
    | false => simp only [boolToSign, id_eq, Bool.false_eq_true, if_false]; ring
    | true => simp only [boolToSign, if_true, Prod.fst_swap, Prod.snd_swap]; ring
  simp only [empMean, empRadVec, empRad]
  rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact congrArg (1 / (m : ℝ) * ·) (Finset.sum_congr rfl fun j _ => key j)

/-! ### The in-expectation symmetrization bound -/

/-- A conditional supremum of uniformly bounded reals is bounded by the same bound. -/
lemma abs_ciSup_le {ι : Type*} [Nonempty ι] {a : ι → ℝ} {B : ℝ} (h : ∀ i, |a i| ≤ B) :
    |⨆ i, a i| ≤ B := by
  have hbdd : BddAbove (Set.range a) :=
    ⟨B, fun y hy => by obtain ⟨i, rfl⟩ := hy; exact (abs_le.mp (h i)).2⟩
  rw [abs_le]
  refine ⟨?_, ciSup_le fun i => (abs_le.mp (h i)).2⟩
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  exact le_trans (abs_le.mp (h i₀)).1 (le_ciSup hbdd i₀)

/-- A bounded measurable real function on a finite measure space is integrable. -/
lemma integrable_of_bound_of_measurable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    [IsFiniteMeasure ν] {f : Y → ℝ} {C : ℝ} (hf : Measurable f) (hC : ∀ y, |f y| ≤ C) :
    Integrable f ν :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hC y)

variable {ι : Type*}

/-- The empirical Rademacher complexity of the class `g` on the sample `S`: the expected (over a
uniform sign vector) supremum, over the class, of the signed empirical average. -/
def empRadComplexity (g : ι → X → ℝ) (S : Fin m → X) : ℝ :=
  ∫ σ, ⨆ i, empRadVec (fun j => g i (S j)) σ ∂(radMeasure m)

omit [MeasurableSpace X] in
/-- The empirical Rademacher complexity is bounded by the value bound. -/
lemma empRadComplexity_abs_le [Nonempty ι] (hm : 0 < m) (g : ι → X → ℝ) {b : ℝ}
    (hb : ∀ i x, |g i x| ≤ b) (S : Fin m → X) : |empRadComplexity g S| ≤ b := by
  unfold empRadComplexity
  calc |∫ σ, ⨆ i, empRadVec (fun j => g i (S j)) σ ∂(radMeasure m)|
      ≤ ∫ σ, |⨆ i, empRadVec (fun j => g i (S j)) σ| ∂(radMeasure m) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _σ, b ∂(radMeasure m) :=
        integral_mono
          (integrable_of_bound_of_measurable (measurable_of_finite _)
            (fun σ => abs_ciSup_le fun i => empRadVec_abs_le hm (fun j => hb i (S j)) σ)).abs
          (integrable_const b)
          (fun σ => abs_ciSup_le fun i => empRadVec_abs_le hm (fun j => hb i (S j)) σ)
    _ = b := by rw [integral_const]; simp

/-- The empirical Rademacher complexity is measurable in the sample. -/
lemma measurable_empRadComplexity (g : ι → X → ℝ)
    (hrad : ∀ σ : SignVector m, Measurable fun S : Fin m → X => ⨆ i, empRadVec (fun j => g i (S j)) σ) :
    Measurable (empRadComplexity (m := m) g) := by
  have h : empRadComplexity (m := m) g = fun S => (1 / (Fintype.card (SignVector m) : ℝ)) *
      ∑ σ, ⨆ i, empRadVec (fun j => g i (S j)) σ := by
    funext S; unfold empRadComplexity; rw [integral_radMeasure]
  rw [h]
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro σ _
  exact hrad σ

/-- The empirical mean is measurable in the sample whenever the loss is measurable. -/
lemma measurable_empMean {g : X → ℝ} (hg : Measurable g) :
    Measurable (fun S : Fin m → X => empMean g S) := by
  unfold empMean
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j _
  exact hg.comp (measurable_pi_apply j)

omit [MeasurableSpace X] in
/-- The double-sample empirical-mean gap is bounded by twice the value bound. -/
lemma empMean_diff_abs_le (hm : 0 < m) {g : X → ℝ} {b : ℝ} (hb : ∀ x, |g x| ≤ b)
    (S S' : Fin m → X) : |empMean g S' - empMean g S| ≤ 2 * b := by
  have h1 := abs_le.mp (empMean_abs_le hm hb S')
  have h2 := abs_le.mp (empMean_abs_le hm hb S)
  rw [abs_le]; exact ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

/-- The true-risk minus empirical-mean gap is bounded by twice the value bound. -/
lemma trueRisk_empMean_diff_abs_le [IsProbabilityMeasure P] (hm : 0 < m) {g : X → ℝ} {b : ℝ}
    (hgi : Integrable g P) (hb : ∀ x, |g x| ≤ b) (S : Fin m → X) :
    |trueRisk P g - empMean g S| ≤ 2 * b := by
  have h1 := abs_le.mp (trueRisk_abs_le hgi hb)
  have h2 := abs_le.mp (empMean_abs_le hm hb S)
  rw [abs_le]; exact ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

omit [MeasurableSpace X] in
/-- The double-sample gap family is bounded above (uniformly in the class index). -/
lemma bddAbove_empMean_diff (hm : 0 < m) (g : ι → X → ℝ) {b : ℝ} (hb : ∀ i x, |g i x| ≤ b)
    (S S' : Fin m → X) : BddAbove (Set.range fun i => empMean (g i) S' - empMean (g i) S) :=
  ⟨2 * b, by rintro y ⟨i, rfl⟩; exact (abs_le.mp (empMean_diff_abs_le hm (hb i) S S')).2⟩

set_option maxHeartbeats 400000 in
/-- **Ghost sample + Jensen (pointwise).** For a fixed sample `S`, the uniform deviation is at most the
inner expectation of the double-sample gap (replace the true risk by the ghost-sample empirical mean,
then `sup ∫ ≤ ∫ sup`). -/
lemma unifDev_pointwise_le [IsProbabilityMeasure P] [Nonempty ι] (hm : 0 < m)
    (g : ι → X → ℝ) {b : ℝ} (hb : ∀ i x, |g i x| ≤ b) (hgi : ∀ i, Integrable (g i) P)
    (hgmeas : ∀ i, Measurable (g i))
    (hψ : Measurable fun q : (Fin m → X) × (Fin m → X) =>
      ⨆ i, (empMean (g i) q.2 - empMean (g i) q.1)) (S : Fin m → X) :
    (⨆ i, (trueRisk P (g i) - empMean (g i) S))
      ≤ ∫ S', ⨆ i, (empMean (g i) S' - empMean (g i) S) ∂(Measure.pi fun _ : Fin m => P) := by
  have hinner_int : Integrable (fun S' : Fin m → X =>
      ⨆ i, (empMean (g i) S' - empMean (g i) S)) (Measure.pi fun _ : Fin m => P) :=
    integrable_of_bound_of_measurable (hψ.comp measurable_prodMk_left)
      (fun S' => abs_ciSup_le fun i => empMean_diff_abs_le hm (hb i) S S')
  refine ciSup_le fun i => ?_
  have hmean_int : Integrable (fun S' : Fin m → X => empMean (g i) S')
      (Measure.pi fun _ : Fin m => P) :=
    integrable_of_bound_of_measurable (measurable_empMean (hgmeas i)) (empMean_abs_le hm (hb i))
  have hghost : trueRisk P (g i) - empMean (g i) S
      = ∫ S', (empMean (g i) S' - empMean (g i) S) ∂(Measure.pi fun _ : Fin m => P) := by
    rw [integral_sub hmean_int (integrable_const _), integral_const,
      ← trueRisk_eq_integral_empMean hm (g i) (hgi i)]
    simp
  rw [hghost]
  exact integral_mono (hmean_int.sub (integrable_const _)) hinner_int
    (fun S' => le_ciSup (bddAbove_empMean_diff hm g hb S S') i)

set_option maxHeartbeats 800000 in
/-- **Ghost sample + Jensen.** The expected uniform deviation is at most the expected double-sample
gap over `(S, S') ∼ P^m × P^m`. -/
lemma integral_unifDev_le_double [IsProbabilityMeasure P] [Nonempty ι] (hm : 0 < m)
    (g : ι → X → ℝ) {b : ℝ} (hb : ∀ i x, |g i x| ≤ b) (hgi : ∀ i, Integrable (g i) P)
    (hgmeas : ∀ i, Measurable (g i))
    (hφ : Measurable fun S : Fin m → X => ⨆ i, (trueRisk P (g i) - empMean (g i) S))
    (hψ : Measurable fun q : (Fin m → X) × (Fin m → X) =>
      ⨆ i, (empMean (g i) q.2 - empMean (g i) q.1)) :
    ∫ S, ⨆ i, (trueRisk P (g i) - empMean (g i) S) ∂(Measure.pi fun _ : Fin m => P)
      ≤ ∫ q, ⨆ i, (empMean (g i) q.2 - empMean (g i) q.1)
          ∂((Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin m => P)) := by
  have hψ'_int : Integrable (fun q : (Fin m → X) × (Fin m → X) =>
      ⨆ i, (empMean (g i) q.2 - empMean (g i) q.1))
      ((Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin m => P)) :=
    integrable_of_bound_of_measurable hψ (fun q => abs_ciSup_le fun i => empMean_diff_abs_le hm (hb i) q.1 q.2)
  have hφ_int : Integrable (fun S : Fin m → X => ⨆ i, (trueRisk P (g i) - empMean (g i) S))
      (Measure.pi fun _ : Fin m => P) :=
    integrable_of_bound_of_measurable hφ
      (fun S => abs_ciSup_le fun i => trueRisk_empMean_diff_abs_le hm (hgi i) (hb i) S)
  rw [integral_prod _ hψ'_int]
  exact integral_mono hφ_int hψ'_int.integral_prod_left
    (unifDev_pointwise_le hm g hb hgi hgmeas hψ)

/-- Every real function on the finite sign-vector space is integrable against the uniform measure. -/
lemma integrable_radMeasure_of_finite (f : SignVector m → ℝ) : Integrable f (radMeasure m) := by
  refine Integrable.mono' (integrable_const (Finset.univ.sup' Finset.univ_nonempty fun σ => ‖f σ‖))
    (measurable_of_finite f).aestronglyMeasurable (ae_of_all _ fun σ => ?_)
  exact Finset.le_sup' (fun σ => ‖f σ‖) (Finset.mem_univ σ)

set_option maxHeartbeats 400000 in
omit [MeasurableSpace X] in
/-- **The swap-averaged double gap is at most two empirical Rademacher complexities.** For a fixed
double sample `p`, averaging the swapped ghost gap over all sign vectors and using the subadditivity of
the supremum together with the sign symmetry of the uniform sign measure splits it into the empirical
Rademacher complexity on each half of the sample. -/
lemma swap_integral_le [Nonempty ι] (hm : 0 < m) (g : ι → X → ℝ) {b : ℝ} (hb : ∀ i x, |g i x| ≤ b)
    (p : Fin m → X × X) :
    ∫ σ, ⨆ i, (empMean (g i) (fun j => ((swapAt σ p) j).2)
        - empMean (g i) (fun j => ((swapAt σ p) j).1)) ∂(radMeasure m)
      ≤ empRadComplexity g (fun j => (p j).1) + empRadComplexity g (fun j => (p j).2) := by
  have hbddx : ∀ σ, BddAbove (Set.range fun i => empRadVec (fun j => g i (p j).1) σ) :=
    fun σ => ⟨b, by rintro y ⟨i, rfl⟩
                    exact (abs_le.mp (empRadVec_abs_le hm (fun j => hb i (p j).1) σ)).2⟩
  have hbddny : ∀ σ, BddAbove (Set.range fun i => - empRadVec (fun j => g i (p j).2) σ) :=
    fun σ => ⟨b, by rintro y ⟨i, rfl⟩
                    have := (abs_le.mp (empRadVec_abs_le hm (fun j => hb i (p j).2) σ)).1; linarith⟩
  have hfst : ∫ σ, ⨆ i, empRadVec (fun j => g i (p j).1) σ ∂(radMeasure m)
      = empRadComplexity g (fun j => (p j).1) := rfl
  have hsnd : ∫ σ, ⨆ i, (- empRadVec (fun j => g i (p j).2) σ) ∂(radMeasure m)
      = empRadComplexity g (fun j => (p j).2) := by
    unfold empRadComplexity
    rw [← integral_comp_flipSign (fun σ => ⨆ i, empRadVec (fun j => g i (p j).2) σ)]
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    exact iSup_congr fun i => (empRadVec_flipSign (fun j => g i (p j).2) σ).symm
  calc ∫ σ, ⨆ i, (empMean (g i) (fun j => ((swapAt σ p) j).2)
          - empMean (g i) (fun j => ((swapAt σ p) j).1)) ∂(radMeasure m)
      = ∫ σ, ⨆ i, (empRadVec (fun j => g i (p j).1) σ
          - empRadVec (fun j => g i (p j).2) σ) ∂(radMeasure m) := by
        refine integral_congr_ae (ae_of_all _ fun σ => ?_)
        exact iSup_congr fun i => swap_empMean_diff (g i) σ p
    _ ≤ ∫ σ, ((⨆ i, empRadVec (fun j => g i (p j).1) σ)
          + ⨆ i, (- empRadVec (fun j => g i (p j).2) σ)) ∂(radMeasure m) :=
        integral_mono (integrable_radMeasure_of_finite _) (integrable_radMeasure_of_finite _)
          (fun σ => ciSup_sub_le (hbddx σ) (hbddny σ))
    _ = (∫ σ, ⨆ i, empRadVec (fun j => g i (p j).1) σ ∂(radMeasure m))
          + ∫ σ, ⨆ i, (- empRadVec (fun j => g i (p j).2) σ) ∂(radMeasure m) :=
        integral_add (integrable_radMeasure_of_finite _) (integrable_radMeasure_of_finite _)
    _ = empRadComplexity g (fun j => (p j).1) + empRadComplexity g (fun j => (p j).2) := by
        rw [hfst, hsnd]

set_option maxHeartbeats 400000 in
/-- **Swap-averaging identity.** Integrating a bounded function over the double sample equals
integrating its average over all paired-coordinate swaps, since each swap preserves the measure. -/
lemma integral_swapAverage_eq [IsProbabilityMeasure P] (F : (Fin m → X × X) → ℝ) (hF : Measurable F)
    {C : ℝ} (hC : ∀ p, |F p| ≤ C) :
    ∫ p, F p ∂(Measure.pi fun _ : Fin m => P.prod P)
      = ∫ p, (∫ σ, F (swapAt σ p) ∂(radMeasure m)) ∂(Measure.pi fun _ : Fin m => P.prod P) := by
  have hjoint : Integrable (fun z : (Fin m → X × X) × SignVector m => F (swapAt z.2 z.1))
      ((Measure.pi fun _ : Fin m => P.prod P).prod (radMeasure m)) :=
    integrable_of_bound_of_measurable
      (measurable_from_prod_countable_left fun σ => hF.comp (measurable_swapAt σ)) (fun z => hC _)
  calc ∫ p, F p ∂(Measure.pi fun _ : Fin m => P.prod P)
      = ∫ _σ, (∫ p, F p ∂(Measure.pi fun _ : Fin m => P.prod P)) ∂(radMeasure m) := by
        rw [integral_const]; simp
    _ = ∫ σ, (∫ p, F (swapAt σ p) ∂(Measure.pi fun _ : Fin m => P.prod P)) ∂(radMeasure m) := by
        refine integral_congr_ae (ae_of_all _ fun σ => ?_); exact (integral_comp_swapAt σ F).symm
    _ = ∫ p, (∫ σ, F (swapAt σ p) ∂(radMeasure m)) ∂(Measure.pi fun _ : Fin m => P.prod P) :=
        (integral_integral_swap (f := fun p σ => F (swapAt σ p)) hjoint).symm

/-- The swap-averaged inner integral is integrable over the double sample. -/
lemma integrable_swap_inner [IsProbabilityMeasure P] (F : (Fin m → X × X) → ℝ) (hF : Measurable F)
    {C : ℝ} (hC : ∀ p, |F p| ≤ C) :
    Integrable (fun p => ∫ σ, F (swapAt σ p) ∂(radMeasure m))
      (Measure.pi fun _ : Fin m => P.prod P) := by
  have hjoint : Integrable (fun z : (Fin m → X × X) × SignVector m => F (swapAt z.2 z.1))
      ((Measure.pi fun _ : Fin m => P.prod P).prod (radMeasure m)) :=
    integrable_of_bound_of_measurable
      (measurable_from_prod_countable_left fun σ => hF.comp (measurable_swapAt σ)) (fun z => hC _)
  exact hjoint.integral_prod_left

set_option maxHeartbeats 800000 in
/-- **Swap-averaging + subadditivity + symmetry.** The expected double-sample gap is at most twice the
expected empirical Rademacher complexity. -/
lemma integral_double_le_radComplexity [IsProbabilityMeasure P] [Nonempty ι] (hm : 0 < m)
    (g : ι → X → ℝ) {b : ℝ} (hb : ∀ i x, |g i x| ≤ b)
    (hψ : Measurable fun q : (Fin m → X) × (Fin m → X) =>
      ⨆ i, (empMean (g i) q.2 - empMean (g i) q.1))
    (hrad : ∀ σ : SignVector m,
      Measurable fun S : Fin m → X => ⨆ i, empRadVec (fun j => g i (S j)) σ) :
    ∫ q, ⨆ i, (empMean (g i) q.2 - empMean (g i) q.1)
        ∂((Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin m => P))
      ≤ 2 * ∫ S, empRadComplexity g S ∂(Measure.pi fun _ : Fin m => P) := by
  have hΨ_meas : Measurable (fun p : Fin m → X × X =>
      ⨆ i, (empMean (g i) (fun j => (p j).2) - empMean (g i) (fun j => (p j).1))) :=
    hψ.comp (MeasurableEquiv.arrowProdEquivProdArrow X X (Fin m)).measurable
  have hΨ_bd : ∀ p : Fin m → X × X, |⨆ i, (empMean (g i) (fun j => (p j).2)
      - empMean (g i) (fun j => (p j).1))| ≤ 2 * b :=
    fun p => abs_ciSup_le fun i =>
      empMean_diff_abs_le hm (hb i) (fun j => (p j).1) (fun j => (p j).2)
  have hrc_meas : Measurable (empRadComplexity (m := m) g) := measurable_empRadComplexity g hrad
  have hrc_fst : Integrable (fun p : Fin m → X × X => empRadComplexity g (fun j => (p j).1))
      (Measure.pi fun _ : Fin m => P.prod P) :=
    integrable_of_bound_of_measurable (hrc_meas.comp (measurePreserving_fstCoord (P := P)).measurable)
      (fun p => empRadComplexity_abs_le hm g hb _)
  have hrc_snd : Integrable (fun p : Fin m → X × X => empRadComplexity g (fun j => (p j).2))
      (Measure.pi fun _ : Fin m => P.prod P) :=
    integrable_of_bound_of_measurable (hrc_meas.comp (measurePreserving_sndCoord (P := P)).measurable)
      (fun p => empRadComplexity_abs_le hm g hb _)
  calc ∫ q, ⨆ i, (empMean (g i) q.2 - empMean (g i) q.1)
          ∂((Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin m => P))
      = ∫ p, ⨆ i, (empMean (g i) (fun j => (p j).2) - empMean (g i) (fun j => (p j).1))
          ∂(Measure.pi fun _ : Fin m => P.prod P) :=
        ((measurePreserving_arrowProdEquivProdArrow X X (Fin m) (fun _ => P) (fun _ => P)).integral_comp
          (MeasurableEquiv.arrowProdEquivProdArrow X X (Fin m)).measurableEmbedding
          (fun q => ⨆ i, (empMean (g i) q.2 - empMean (g i) q.1))).symm
    _ = ∫ p, (∫ σ, ⨆ i, (empMean (g i) (fun j => ((swapAt σ p) j).2)
          - empMean (g i) (fun j => ((swapAt σ p) j).1)) ∂(radMeasure m))
          ∂(Measure.pi fun _ : Fin m => P.prod P) :=
        integral_swapAverage_eq _ hΨ_meas hΨ_bd
    _ ≤ ∫ p, (empRadComplexity g (fun j => (p j).1) + empRadComplexity g (fun j => (p j).2))
          ∂(Measure.pi fun _ : Fin m => P.prod P) :=
        integral_mono (integrable_swap_inner _ hΨ_meas hΨ_bd) (hrc_fst.add hrc_snd)
          (fun p => swap_integral_le hm g hb p)
    _ = (∫ p, empRadComplexity g (fun j => (p j).1) ∂(Measure.pi fun _ : Fin m => P.prod P))
          + ∫ p, empRadComplexity g (fun j => (p j).2) ∂(Measure.pi fun _ : Fin m => P.prod P) :=
        integral_add hrc_fst hrc_snd
    _ = (∫ S, empRadComplexity g S ∂(Measure.pi fun _ : Fin m => P))
          + ∫ S, empRadComplexity g S ∂(Measure.pi fun _ : Fin m => P) := by
        rw [integral_comp_fstCoord hrc_meas.aestronglyMeasurable,
          integral_comp_sndCoord hrc_meas.aestronglyMeasurable]
    _ = 2 * ∫ S, empRadComplexity g S ∂(Measure.pi fun _ : Fin m => P) := by ring

/-- **In-expectation symmetrization.** The expected uniform deviation of true risk from empirical mean
over a uniformly bounded real function class is at most twice the expected empirical Rademacher
complexity of the class. The class is indexed by `ι` with loss family `g : ι → X → ℝ`; measurability of
the supremum envelopes is carried as hypotheses (discharged, for a separable index, where the family is
used). This is the classical Rademacher symmetrization lemma, with the optimal constant `2`. -/
theorem symmetrization_le [IsProbabilityMeasure P] [Nonempty ι] (hm : 0 < m)
    (g : ι → X → ℝ) {b : ℝ} (hb : ∀ i x, |g i x| ≤ b) (hgi : ∀ i, Integrable (g i) P)
    (hgmeas : ∀ i, Measurable (g i))
    (hφ : Measurable fun S : Fin m → X => ⨆ i, (trueRisk P (g i) - empMean (g i) S))
    (hψ : Measurable fun q : (Fin m → X) × (Fin m → X) =>
      ⨆ i, (empMean (g i) q.2 - empMean (g i) q.1))
    (hrad : ∀ σ : SignVector m,
      Measurable fun S : Fin m → X => ⨆ i, empRadVec (fun j => g i (S j)) σ) :
    ∫ S, ⨆ i, (trueRisk P (g i) - empMean (g i) S) ∂(Measure.pi fun _ : Fin m => P)
      ≤ 2 * ∫ S, empRadComplexity g S ∂(Measure.pi fun _ : Fin m => P) :=
  (integral_unifDev_le_double hm g hb hgi hgmeas hφ hψ).trans
    (integral_double_le_radComplexity hm g hb hψ hrad)

end TLT.Capacity
