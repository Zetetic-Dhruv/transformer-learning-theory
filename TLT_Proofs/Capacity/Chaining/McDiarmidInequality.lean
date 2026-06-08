/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# McDiarmid's bounded-differences inequality

A function `f` of `m` independent coordinates that changes by at most `c` when any single coordinate
is altered concentrates around its mean: `P[f − E f ≥ ε] ≤ exp(−2ε²/(m·c²))`. This converts the
in-expectation uniform-deviation bound (the expected supremum of the empirical Rademacher process) into
a high-probability per-net generalization bound — the form the float-transfer spine consumes.

The proof is the moment-generating-function tensorization: peel one coordinate at a time
(`measurePreserving_piFinSuccAbove`), bounding each conditional increment's MGF by Hoeffding's lemma
(`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`), then a Chernoff optimisation.

## Main definitions

- `HasBoundedDifferences` — bounded change under a single-coordinate perturbation.
- `condIntegrate` — the conditional expectation integrating out the first coordinate.

## Main results

- `mgf_le_of_range_zero_mean` — one-coordinate Hoeffding bound in range form.
- `mgf_bddiff_le` — the moment-generating-function tensorization, `E[exp(t(f − E f))] ≤ exp(m·c²·t²/8)`.
- `mcdiarmid` — the bounded-differences concentration inequality.
-/

/-!
## References
- [18] McDiarmid 1989; [15] Hoeffding's lemma; [21] entropy-method (MGF) tensorization route.
- Provenance: Classical-instantiation (MGF-tensorization proof of the bounded-differences ineq.).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

noncomputable section

namespace TLT.Capacity

variable {X : Type*} [MeasurableSpace X] {P : Measure X} {m : ℕ}

/-- `f` has bounded differences `c`: altering one coordinate of the input changes `f` by at most `c`. -/
def HasBoundedDifferences (f : (Fin m → X) → ℝ) (c : ℝ) : Prop :=
  ∀ (i : Fin m) (S S' : Fin m → X), (∀ j, j ≠ i → S j = S' j) → |f S - f S'| ≤ c

/-- **One-coordinate Hoeffding MGF bound.** A centered random variable almost surely in `[a, b]` has
moment generating function at most `exp((b−a)²·t²/8)`. -/
lemma mgf_exp_le_of_centered [IsProbabilityMeasure P] {g : X → ℝ} (hmeas : AEMeasurable g P)
    {a b : ℝ} (hab : ∀ᵐ x ∂P, g x ∈ Set.Icc a b) (hc : ∫ x, g x ∂P = 0) (t : ℝ) :
    ∫ x, Real.exp (t * g x) ∂P ≤ Real.exp ((b - a) ^ 2 * t ^ 2 / 8) := by
  have hsg := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hmeas hab hc
  have hmgf := hsg.mgf_le (t := t)
  calc ∫ x, Real.exp (t * g x) ∂P = mgf g P t := rfl
    _ ≤ Real.exp (((‖b - a‖₊ / 2 : ℝ≥0) ^ 2 : ℝ) * t ^ 2 / 2) := hmgf
    _ = Real.exp ((b - a) ^ 2 * t ^ 2 / 8) := by
        congr 1
        push_cast [coe_nnnorm, Real.norm_eq_abs]
        rw [div_pow, sq_abs]; ring

/-- A centered random variable almost surely in an interval `[a, b]` whose width is bounded by `c`
on both sides has moment generating function at most `exp(c²·t²/8)`. Keeping `a, b, c` as explicit
endpoints confines the width relaxation `(b−a)² ≤ c²` to opaque atoms. -/
lemma mgf_exp_le_of_width [IsProbabilityMeasure P] {g : X → ℝ} (hmeas : AEMeasurable g P)
    {a b c : ℝ} (hab : ∀ᵐ x ∂P, g x ∈ Set.Icc a b) (hwidth : b - a ≤ c) (hwidth' : a - b ≤ c)
    (hc : ∫ x, g x ∂P = 0) (t : ℝ) :
    ∫ x, Real.exp (t * g x) ∂P ≤ Real.exp (c ^ 2 * t ^ 2 / 8) := by
  refine (mgf_exp_le_of_centered hmeas hab hc t).trans (Real.exp_le_exp.2 ?_)
  have hsq : (b - a) ^ 2 ≤ c ^ 2 := by nlinarith [hwidth, hwidth']
  nlinarith [sq_nonneg t, hsq]

/-- **Hoeffding's lemma in range form.** A centered random variable whose values span a range of
width at most `c` (`g x − g x' ≤ c` for all `x, x'`) has moment generating function at most
`exp(c²·t²/8)`. The tight width-`c` interval is anchored at the infimum and supremum of the range,
which are finite because the range bound makes `g` bounded. This is the per-coordinate increment
estimate consumed by the tensorization. -/
lemma mgf_le_of_range_zero_mean [IsProbabilityMeasure P] {g : X → ℝ} (hmeas : AEMeasurable g P)
    {c : ℝ} (hc0 : 0 ≤ c) (hrange : ∀ x x', g x - g x' ≤ c) (hz : ∫ x, g x ∂P = 0) (t : ℝ) :
    ∫ x, Real.exp (t * g x) ∂P ≤ Real.exp (c ^ 2 * t ^ 2 / 8) := by
  haveI : Nonempty X := nonempty_of_isProbabilityMeasure P
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hbddBelow : BddBelow (Set.range g) :=
    ⟨g x₀ - c, by rintro y ⟨x, rfl⟩; linarith [hrange x₀ x]⟩
  have hbddAbove : BddAbove (Set.range g) :=
    ⟨g x₀ + c, by rintro y ⟨x, rfl⟩; linarith [hrange x x₀]⟩
  have hlo : ∀ x, (⨅ y, g y) ≤ g x := fun x => ciInf_le hbddBelow x
  have hhi : ∀ x, g x ≤ ⨆ y, g y := fun x => le_ciSup hbddAbove x
  have hIcc : ∀ᵐ x ∂P, g x ∈ Set.Icc (⨅ y, g y) (⨆ y, g y) :=
    ae_of_all _ fun x => ⟨hlo x, hhi x⟩
  have hxa : ∀ x, g x - c ≤ ⨅ y, g y := fun x => le_ciInf fun x' => by linarith [hrange x x']
  have hwidth : (⨆ y, g y) ≤ (⨅ y, g y) + c := ciSup_le fun x => by linarith [hxa x]
  have hab_le : (⨅ y, g y) ≤ ⨆ y, g y := (hlo x₀).trans (hhi x₀)
  exact mgf_exp_le_of_width hmeas hIcc (by linarith) (by linarith) hz t

omit [MeasurableSpace X] in
/-- Changing the input on a set `s` of coordinates changes a bounded-differences function by at most
`s.card · c`: a one-coordinate-at-a-time telescoping along `s`. -/
lemma abs_sub_le_of_boundedDifferences {f : (Fin m → X) → ℝ} {c : ℝ}
    (hbd : HasBoundedDifferences f c) (s : Finset (Fin m)) (S S' : Fin m → X)
    (hagree : ∀ j ∉ s, S j = S' j) : |f S - f S'| ≤ s.card * c := by
  induction s using Finset.induction_on generalizing S S' with
  | empty =>
      have hSS' : S = S' := funext fun j => hagree j (Finset.notMem_empty j)
      simp [hSS']
  | @insert i s hi ih =>
      have h1 : |f S - f (Function.update S' i (S i))| ≤ s.card * c := by
        refine ih S (Function.update S' i (S i)) fun j hj => ?_
        by_cases hji : j = i
        · subst hji; rw [Function.update_self]
        · rw [Function.update_of_ne hji]
          exact hagree j fun hmem => (Finset.mem_insert.1 hmem).elim hji (fun h => hj h)
      have h2 : |f (Function.update S' i (S i)) - f S'| ≤ c :=
        hbd i (Function.update S' i (S i)) S' fun j hj => Function.update_of_ne hj _ _
      calc |f S - f S'|
          ≤ |f S - f (Function.update S' i (S i))| + |f (Function.update S' i (S i)) - f S'| :=
            abs_sub_le _ _ _
        _ ≤ s.card * c + c := add_le_add h1 h2
        _ = (insert i s).card * c := by rw [Finset.card_insert_of_notMem hi]; push_cast; ring

omit [MeasurableSpace X] in
/-- A bounded-differences function differs from any fixed reference point by at most `m · c`, hence
is bounded (used to discharge the integrability side conditions of the tensorization). -/
lemma abs_f_le {f : (Fin m → X) → ℝ} {c : ℝ} (hbd : HasBoundedDifferences f c)
    (S₀ S : Fin m → X) : |f S| ≤ |f S₀| + m * c := by
  have h : |f S - f S₀| ≤ m * c := by
    have := abs_sub_le_of_boundedDifferences hbd Finset.univ S S₀
      fun j hj => absurd (Finset.mem_univ j) hj
    simpa [Finset.card_univ] using this
  have htri : |f S| ≤ |f S - f S₀| + |f S₀| := by
    simpa using abs_add_le (f S - f S₀) (f S₀)
  linarith

/-- Prepending a coordinate, `(x, r) ↦ Fin.cons x r`, is measurable. -/
lemma measurable_consPair {n : ℕ} :
    Measurable fun p : X × (Fin n → X) => (Fin.cons p.1 p.2 : Fin (n + 1) → X) := by
  refine measurable_pi_iff.2 fun j => ?_
  induction j using Fin.cases with
  | zero => simpa using measurable_fst
  | succ j' => simpa using (measurable_pi_apply j').comp measurable_snd

/-- A bounded measurable function composed into `exp(t·(· − K))` is integrable on a probability
measure: the integrand is positive and bounded by `exp(|t|·(B + |K|))`. -/
lemma integrable_exp_mul_sub {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    [IsProbabilityMeasure ν] {h : Y → ℝ} (hh : Measurable h) {B : ℝ} (hB : ∀ y, |h y| ≤ B)
    (t K : ℝ) : Integrable (fun y => Real.exp (t * (h y - K))) ν := by
  refine Integrable.of_bound ((hh.sub_const K).const_mul t).exp.aestronglyMeasurable
    (Real.exp (|t| * (B + |K|))) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  have habs : |h y - K| ≤ B + |K| := by
    have hsl := abs_sub_le (h y) 0 K
    simp only [sub_zero, zero_sub, abs_neg] at hsl
    linarith [hB y]
  calc t * (h y - K) ≤ |t * (h y - K)| := le_abs_self _
    _ = |t| * |h y - K| := abs_mul t (h y - K)
    _ ≤ |t| * (B + |K|) := mul_le_mul_of_nonneg_left habs (abs_nonneg t)

/-- **Peel the first coordinate.** Integrating an integrable function over the `(n+1)`-fold product
is the iterated integral that conditions on the last `n` coordinates and integrates out the first,
realised concretely through `Fin.cons`. -/
lemma integral_pi_succ [IsProbabilityMeasure P] {n : ℕ} (F : (Fin (n + 1) → X) → ℝ)
    (hF : Integrable F (Measure.pi fun _ : Fin (n + 1) => P)) :
    ∫ S, F S ∂(Measure.pi fun _ : Fin (n + 1) => P)
      = ∫ r, ∫ x, F (Fin.cons x r) ∂P ∂(Measure.pi fun _ : Fin n => P) := by
  have hmp0 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) 0
  rw [← hmp0.symm.integral_comp' F, integral_prod_symm]
  · simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk,
      Fin.insertNth_zero']
  · exact (hmp0.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hF

/-- A bounded measurable real function is integrable with respect to a finite measure. -/
lemma integrable_of_bounded {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [IsFiniteMeasure ν]
    {h : Y → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ y, |h y| ≤ C) : Integrable h ν :=
  Integrable.of_bound hh.aestronglyMeasurable C
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hC y)

/-- Prepending a fixed tail, `x ↦ f (Fin.cons x r)`, is measurable. -/
lemma measurable_f_cons {n : ℕ} {f : (Fin (n + 1) → X) → ℝ} (hf : Measurable f) (r : Fin n → X) :
    Measurable fun x => f (Fin.cons x r) :=
  hf.comp (measurable_consPair.comp (measurable_id.prodMk measurable_const))

/-- The conditional expectation that integrates out the first coordinate. -/
def condIntegrate (P : Measure X) {n : ℕ} (f : (Fin (n + 1) → X) → ℝ) : (Fin n → X) → ℝ :=
  fun r => ∫ x, f (Fin.cons x r) ∂P

lemma condIntegrate_apply {n : ℕ} (f : (Fin (n + 1) → X) → ℝ) (r : Fin n → X) :
    condIntegrate P f r = ∫ x, f (Fin.cons x r) ∂P := rfl

/-- Integrating out a coordinate preserves measurability. -/
lemma measurable_condIntegrate [IsProbabilityMeasure P] {n : ℕ} {f : (Fin (n + 1) → X) → ℝ}
    (hf : Measurable f) : Measurable (condIntegrate P f) :=
  ((hf.comp measurable_consPair).stronglyMeasurable.integral_prod_left').measurable

/-- A bound on `f` transfers to its conditional expectation. -/
lemma abs_condIntegrate_le [IsProbabilityMeasure P] {n : ℕ} {f : (Fin (n + 1) → X) → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ S, |f S| ≤ C) (r : Fin n → X) :
    |condIntegrate P f r| ≤ C := by
  have hir : Integrable (fun x => f (Fin.cons x r)) P :=
    integrable_of_bounded (measurable_f_cons hf r) fun x => hC _
  calc |condIntegrate P f r| = ‖∫ x, f (Fin.cons x r) ∂P‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, ‖f (Fin.cons x r)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ _, C ∂P := integral_mono hir.norm (integrable_const C)
        fun x => by rw [Real.norm_eq_abs]; exact hC _
    _ = C := by rw [integral_const]; simp

/-- Integrating out a coordinate preserves bounded differences. -/
lemma boundedDifferences_condIntegrate [IsProbabilityMeasure P] {n : ℕ} {f : (Fin (n + 1) → X) → ℝ}
    {c C : ℝ} (hf : Measurable f) (hbd : HasBoundedDifferences f c) (hC : ∀ S, |f S| ≤ C) :
    HasBoundedDifferences (condIntegrate P f) c := by
  intro i r r' hrr'
  have key : ∀ x, |f (Fin.cons x r) - f (Fin.cons x r')| ≤ c := fun x =>
    hbd i.succ (Fin.cons x r) (Fin.cons x r') (by
      intro j hj
      induction j using Fin.cases with
      | zero => simp
      | succ k => rw [Fin.cons_succ, Fin.cons_succ]
                  exact hrr' k fun hk => hj (by rw [hk]))
  have hir : Integrable (fun x => f (Fin.cons x r)) P :=
    integrable_of_bounded (measurable_f_cons hf r) fun x => hC _
  have hir' : Integrable (fun x => f (Fin.cons x r')) P :=
    integrable_of_bounded (measurable_f_cons hf r') fun x => hC _
  calc |condIntegrate P f r - condIntegrate P f r'|
      = ‖∫ x, (f (Fin.cons x r) - f (Fin.cons x r')) ∂P‖ := by
        rw [condIntegrate_apply, condIntegrate_apply, integral_sub hir hir', Real.norm_eq_abs]
    _ ≤ ∫ x, ‖f (Fin.cons x r) - f (Fin.cons x r')‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ _, c ∂P := integral_mono (hir.sub hir').norm (integrable_const c)
        fun x => by rw [Real.norm_eq_abs]; exact key x
    _ = c := by rw [integral_const]; simp

/-- The integral of the conditional expectation recovers the full integral (Fubini). -/
lemma integral_condIntegrate_eq [IsProbabilityMeasure P] {n : ℕ} {f : (Fin (n + 1) → X) → ℝ}
    (hf_int : Integrable f (Measure.pi fun _ : Fin (n + 1) => P)) :
    ∫ r, condIntegrate P f r ∂(Measure.pi fun _ : Fin n => P)
      = ∫ S, f S ∂(Measure.pi fun _ : Fin (n + 1) => P) :=
  (integral_pi_succ f hf_int).symm

/-- **The moment-generating-function tensorization.** For a measurable function with bounded
differences `c`, the centered MGF over the `m`-fold product is at most `exp(m·c²·t²/8)`. Each
coordinate contributes one Hoeffding factor `exp(c²·t²/8)`, peeled off via the conditional
expectation `condIntegrate` and combined by Fubini and induction. -/
lemma mgf_bddiff_le [IsProbabilityMeasure P] {c : ℝ} (hc0 : 0 ≤ c) :
    ∀ (m : ℕ) (f : (Fin m → X) → ℝ), Measurable f → HasBoundedDifferences f c → ∀ t : ℝ,
      ∫ S, Real.exp (t * (f S - ∫ S', f S' ∂(Measure.pi fun _ : Fin m => P)))
          ∂(Measure.pi fun _ : Fin m => P)
        ≤ Real.exp (m * c ^ 2 * t ^ 2 / 8) := by
  intro m
  induction m with
  | zero =>
      intro f _ _ t
      have hzero : ∀ S : Fin 0 → X,
          f S - ∫ S', f S' ∂(Measure.pi fun _ : Fin 0 => P) = 0 := by
        intro S
        have hc : (∫ S', f S' ∂(Measure.pi fun _ : Fin 0 => P)) = f S := by
          rw [show (fun S' : Fin 0 → X => f S') = fun _ => f S from
            funext fun S' => congrArg f (Subsingleton.elim S' S), integral_const]
          simp
        rw [hc]; ring
      simp_rw [hzero, mul_zero, Real.exp_zero]
      simp
  | succ n ih =>
      intro f hf hbd t
      obtain ⟨x₀⟩ : Nonempty X := nonempty_of_isProbabilityMeasure P
      obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ S, |f S| ≤ B := ⟨_, fun S => abs_f_le hbd (fun _ => x₀) S⟩
      set μf : ℝ := ∫ S, f S ∂(Measure.pi fun _ : Fin (n + 1) => P) with hμf
      have hf_int : Integrable f (Measure.pi fun _ : Fin (n + 1) => P) :=
        integrable_of_bounded hf hB
      have hg_bd : HasBoundedDifferences (condIntegrate P f) c :=
        boundedDifferences_condIntegrate hf hbd hB
      have hμf_g : μf = ∫ r, condIntegrate P f r ∂(Measure.pi fun _ : Fin n => P) :=
        hμf.trans (integral_condIntegrate_eq hf_int).symm
      -- exp-bound on the centered model, used for both integrability obligations
      have hFmeas : Measurable fun S => Real.exp (t * (f S - μf)) :=
        ((hf.sub_const μf).const_mul t).exp
      have hFC : ∀ S, |Real.exp (t * (f S - μf))| ≤ Real.exp (|t| * (B + |μf|)) := fun S => by
        rw [abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.2 ?_
        have habs : |f S - μf| ≤ B + |μf| := by
          have hsl := abs_sub_le (f S) 0 μf
          simp only [sub_zero, zero_sub, abs_neg] at hsl
          linarith [hB S]
        calc t * (f S - μf) ≤ |t * (f S - μf)| := le_abs_self _
          _ = |t| * |f S - μf| := abs_mul t (f S - μf)
          _ ≤ |t| * (B + |μf|) := mul_le_mul_of_nonneg_left habs (abs_nonneg t)
      have hF_int : Integrable (fun S => Real.exp (t * (f S - μf)))
          (Measure.pi fun _ : Fin (n + 1) => P) := integrable_of_bounded hFmeas hFC
      -- inner Hoeffding factor, conditional on the tail `r`
      have hinner : ∀ r : Fin n → X,
          ∫ x, Real.exp (t * (f (Fin.cons x r) - μf)) ∂P
            ≤ Real.exp (c ^ 2 * t ^ 2 / 8) * Real.exp (t * (condIntegrate P f r - μf)) := by
        intro r
        have hmeas_r := measurable_f_cons hf r
        have hir : Integrable (fun x => f (Fin.cons x r)) P :=
          integrable_of_bounded hmeas_r fun x => hB _
        have hmean0 : ∫ x, (f (Fin.cons x r) - condIntegrate P f r) ∂P = 0 := by
          rw [integral_sub hir (integrable_const _), integral_const]
          simp [condIntegrate_apply]
        have hrange0 : ∀ x x', (f (Fin.cons x r) - condIntegrate P f r)
            - (f (Fin.cons x' r) - condIntegrate P f r) ≤ c := fun x x' => by
          calc (f (Fin.cons x r) - condIntegrate P f r) - (f (Fin.cons x' r) - condIntegrate P f r)
              = f (Fin.cons x r) - f (Fin.cons x' r) := by ring
            _ ≤ |f (Fin.cons x r) - f (Fin.cons x' r)| := le_abs_self _
            _ ≤ c := hbd 0 (Fin.cons x r) (Fin.cons x' r) (fun j hj => by
                induction j using Fin.cases with
                | zero => exact absurd rfl hj
                | succ k => rw [Fin.cons_succ, Fin.cons_succ])
        have hHoeff := mgf_le_of_range_zero_mean
          (hmeas_r.sub_const (condIntegrate P f r)).aemeasurable hc0 hrange0 hmean0 t
        have hrw : (fun x => Real.exp (t * (f (Fin.cons x r) - μf)))
            = fun x => Real.exp (t * (condIntegrate P f r - μf))
                * Real.exp (t * (f (Fin.cons x r) - condIntegrate P f r)) := by
          funext x; rw [← Real.exp_add]; congr 1; ring
        rw [hrw, integral_const_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right hHoeff (Real.exp_pos _).le
      -- assemble: peel, monotone outer bound, induction hypothesis
      have hLHS_int : Integrable (condIntegrate P fun S => Real.exp (t * (f S - μf)))
          (Measure.pi fun _ : Fin n => P) :=
        integrable_of_bounded (measurable_condIntegrate hFmeas) (abs_condIntegrate_le hFmeas hFC)
      have hgC : ∀ r, |Real.exp (t * (condIntegrate P f r - μf))| ≤ Real.exp (|t| * (B + |μf|)) :=
        fun r => by
          rw [abs_of_pos (Real.exp_pos _)]
          refine Real.exp_le_exp.2 ?_
          have habs : |condIntegrate P f r - μf| ≤ B + |μf| := by
            have hsl := abs_sub_le (condIntegrate P f r) 0 μf
            simp only [sub_zero, zero_sub, abs_neg] at hsl
            linarith [abs_condIntegrate_le (P := P) hf hB r]
          calc t * (condIntegrate P f r - μf) ≤ |t * (condIntegrate P f r - μf)| := le_abs_self _
            _ = |t| * |condIntegrate P f r - μf| := abs_mul _ _
            _ ≤ |t| * (B + |μf|) := mul_le_mul_of_nonneg_left habs (abs_nonneg t)
      have hg_exp_int : Integrable (fun r => Real.exp (t * (condIntegrate P f r - μf)))
          (Measure.pi fun _ : Fin n => P) :=
        integrable_of_bounded (((measurable_condIntegrate hf).sub_const μf).const_mul t).exp hgC
      have hRHS_int : Integrable (fun r => Real.exp (c ^ 2 * t ^ 2 / 8)
          * Real.exp (t * (condIntegrate P f r - μf))) (Measure.pi fun _ : Fin n => P) :=
        hg_exp_int.const_mul (Real.exp (c ^ 2 * t ^ 2 / 8))
      rw [integral_pi_succ _ hF_int]
      calc ∫ r, ∫ x, Real.exp (t * (f (Fin.cons x r) - μf)) ∂P ∂(Measure.pi fun _ : Fin n => P)
          ≤ ∫ r, Real.exp (c ^ 2 * t ^ 2 / 8) * Real.exp (t * (condIntegrate P f r - μf))
              ∂(Measure.pi fun _ : Fin n => P) := integral_mono hLHS_int hRHS_int hinner
        _ = Real.exp (c ^ 2 * t ^ 2 / 8)
              * ∫ r, Real.exp (t * (condIntegrate P f r - μf)) ∂(Measure.pi fun _ : Fin n => P) :=
            integral_const_mul _ _
        _ ≤ Real.exp (c ^ 2 * t ^ 2 / 8) * Real.exp (n * c ^ 2 * t ^ 2 / 8) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            rw [hμf_g]
            exact ih (condIntegrate P f) (measurable_condIntegrate hf) hg_bd t
        _ = Real.exp ((n + 1 : ℕ) * c ^ 2 * t ^ 2 / 8) := by
            rw [← Real.exp_add]; congr 1; push_cast; ring

/-- **McDiarmid's bounded-differences inequality.** A measurable function of `m` independent
coordinates that changes by at most `c` when any single coordinate is altered concentrates above
its mean: `P[f − E f ≥ ε] ≤ exp(−2ε²/(m·c²))`. This is the Chernoff optimisation of the
moment-generating-function tensorization. -/
theorem mcdiarmid [IsProbabilityMeasure P] {m : ℕ} (f : (Fin m → X) → ℝ) (hf : Measurable f)
    {c : ℝ} (hc0 : 0 ≤ c) (hbd : HasBoundedDifferences f c) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin m => P).real
        {S | ε ≤ f S - ∫ S', f S' ∂(Measure.pi fun _ : Fin m => P)}
      ≤ Real.exp (-2 * ε ^ 2 / ((m : ℝ) * c ^ 2)) := by
  by_cases hmc : (m : ℝ) * c ^ 2 = 0
  · rw [hmc, div_zero, Real.exp_zero]; exact measureReal_le_one
  · have hmc_pos : 0 < (m : ℝ) * c ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hmc)
    obtain ⟨x₀⟩ : Nonempty X := nonempty_of_isProbabilityMeasure P
    obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ S, |f S| ≤ B := ⟨_, fun S => abs_f_le hbd (fun _ => x₀) S⟩
    set μ := Measure.pi fun _ : Fin m => P with hμ_def
    set μf := ∫ S', f S' ∂μ with hμf
    set t := 4 * ε / ((m : ℝ) * c ^ 2) with ht_def
    have ht : 0 ≤ t := by rw [ht_def]; positivity
    have hint : Integrable (fun S => Real.exp (t * (f S - μf))) μ :=
      integrable_exp_mul_sub hf hB t μf
    have hmarkov := measure_ge_le_exp_mul_mgf (μ := μ) (X := fun S => f S - μf) ε ht hint
    have hmgf : mgf (fun S => f S - μf) μ t ≤ Real.exp ((m : ℝ) * c ^ 2 * t ^ 2 / 8) :=
      mgf_bddiff_le hc0 m f hf hbd t
    calc (μ.real {S | ε ≤ f S - μf})
        ≤ Real.exp (-t * ε) * mgf (fun S => f S - μf) μ t := hmarkov
      _ ≤ Real.exp (-t * ε) * Real.exp ((m : ℝ) * c ^ 2 * t ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
      _ = Real.exp (-t * ε + (m : ℝ) * c ^ 2 * t ^ 2 / 8) := (Real.exp_add _ _).symm
      _ = Real.exp (-2 * ε ^ 2 / ((m : ℝ) * c ^ 2)) := by
          congr 1; rw [ht_def]; field_simp; ring

end TLT.Capacity
