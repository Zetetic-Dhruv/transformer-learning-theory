/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.QuadraticWidth
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The CUBIC (degree-3) WIDTH region-count results: the order-3 Davenport–Schinzel structure

This file is the degree-3 generalization of `QuadraticWidth.lean`. The quadratic (order-2) case
forbids the length-4 alternation `a,b,a,b` (`NoABAB`) and admits the **linear** tight bound
`λ₂(n) ≤ 2n − 1` (`ds_order2_length_le`). The cubic (order-3) case forbids the length-5 alternation
`a,b,a,b,a` (`NoABABA`); the true asymptotic of the order-3 Davenport–Schinzel length is the
*super-linear* `λ₃(n) = Θ(n · α(n))` (inverse Ackermann), which has **no linear closed form**.

## What is CLOSED here (Stage 1: the order-3 structure), sorry-free and axiom-clean

* **`NoABABA`** — the order-3 forbidden-pattern predicate: no `a,b,a,b,a` subsequence (a length-5
  alternation of two symbols).
* **`CubicScore` / `CubicLines`** — degree-3 score functions, mirroring `QuadScore`/`QuadLines`.
* **`CubicLines.pair_comparison_le ≤ 3`** — the per-pair order-3 bound. The difference of two cubics
  is a degree-≤3 real polynomial. **Each flip of the strict comparison indicator `[0 < D]` is
  charged against root *multiplicity*, not distinct roots.** A transversal crossing costs
  multiplicity 1; a tangency-from-above at a sample (the `1,0,1` double-dip, two flips at one point)
  is a genuine *double root* (`cubic_mult_two_of_localMin`: a from-above touch is a local minimum,
  so the derivative vanishes and the root multiplicity is `≥ 2`). Total flips ≤ total root
  multiplicity = `D.roots.card ≤ natDegree D ≤ 3`. This is the degree-3 upgrade of the quadratic
  `≤ 2`, whose OrdConnected/convexity proof does NOT survive (a cubic sublevel set is not an
  interval).
* **`cubicArg_noABABA`** — the argmax of `n` cubics along an increasing sample has `NoABABA`: an
  `a,b,a,b,a` argmax pattern forces the `a`-vs-`b` comparison to flip `≥ 4` times
  (`seqChanges_ge_four`), contradicting the per-pair bound `≤ 3`. This is the cubic analogue of the
  quadratic `quadArg_noABAB`.

## What is the SUPERLINEARITY phase transition (Stage 2)

The phase-transition statement is that the cubic region count is NOT `O(n)`: unlike the quadratic
`2n − 1`, the order-3 DS length is super-linear. The standard witness is the Wiernik–Sharir
recursive gadget whose alternation count is `Θ(n · α(n))`. The explicit recursive cubic
construction is the genuine remaining obligation; we state the target precisely and do NOT fake an
unproven count. See the status comments at the end of the file.

## The α-gap (NOT attempted)

The exact `Θ(n · α(n))` count requires the inverse Ackermann function `α`, which is **absent from
Mathlib**, and the Hart–Sharir bijection. This is named as the aspirational α-gap and is deliberately
left open.
-/

open scoped BigOperators
open List Set Finset Polynomial

noncomputable section

namespace TLT.TemperedDesignLaw

open TLT.TemperedDesignLaw.MuxHierarchy

set_option linter.deprecated false

/-! ## Stage 1, piece (i): the order-3 forbidden pattern `NoABABA` -/

/-- A list over `Fin n` is **order-3 Davenport–Schinzel admissible** if it has no `a, b, a, b, a`
alternation as a (not-necessarily-contiguous) `Sublist`. This is the degree-3 analogue of `NoABAB`. -/
def NoABABA {n : ℕ} (w : List (Fin n)) : Prop :=
  ∀ a b : Fin n, a ≠ b → ¬ ([a, b, a, b, a] <+ w)

/-- **Build a 5-element alternation sublist from five strictly increasing positions.** If positions
`p₀ < p₁ < p₂ < p₃ < p₄` of `w` carry values `a, b, a, b, a`, then `[a, b, a, b, a] <+ w`.
(Degree-3 analogue of `four_sublist`.) -/
theorem five_sublist {n : ℕ} (w : List (Fin n)) (a b : Fin n)
    (p₀ p₁ p₂ p₃ p₄ : ℕ) (h₀ : p₀ < w.length) (h₁ : p₁ < w.length) (h₂ : p₂ < w.length)
    (h₃ : p₃ < w.length) (h₄ : p₄ < w.length)
    (l₀₁ : p₀ < p₁) (l₁₂ : p₁ < p₂) (l₂₃ : p₂ < p₃) (l₃₄ : p₃ < p₄)
    (w₀ : w.get ⟨p₀, h₀⟩ = a) (w₁ : w.get ⟨p₁, h₁⟩ = b)
    (w₂ : w.get ⟨p₂, h₂⟩ = a) (w₃ : w.get ⟨p₃, h₃⟩ = b) (w₄ : w.get ⟨p₄, h₄⟩ = a) :
    [a, b, a, b, a] <+ w := by
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
  set g : Fin ([a, b, a, b, a].length) → Fin w.length :=
    fun i => match i with
      | ⟨0, _⟩ => ⟨p₀, h₀⟩
      | ⟨1, _⟩ => ⟨p₁, h₁⟩
      | ⟨2, _⟩ => ⟨p₂, h₂⟩
      | ⟨3, _⟩ => ⟨p₃, h₃⟩
      | ⟨4, _⟩ => ⟨p₄, h₄⟩
      | ⟨k + 5, h⟩ => absurd h (by simp)
    with hg
  have hmono : StrictMono g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.lt_def] <;> omega
  refine ⟨OrderEmbedding.ofStrictMono g hmono, ?_⟩
  intro ix
  have hgix : (OrderEmbedding.ofStrictMono g hmono) ix = g ix := rfl
  rw [hgix]
  fin_cases ix <;> simp only [hg] <;> simp_all

/-! ## Stage 1, piece (ii): a 5-alternation forces `seqChanges ≥ 4` -/

/-- **A `0,1,0,1,0`-style pattern forces `seqChanges ≥ 4`.** Four changes live in four disjoint
ranges (degree-3 analogue of `seqChanges_ge_three`). -/
theorem seqChanges_ge_four {β : Type*} [DecidableEq β] {M : ℕ} (c : Fin (M + 1) → β)
    (i j k l p : Fin (M + 1)) (hij : i < j) (hjk : j < k) (hkl : k < l) (hlp : l < p)
    (hcij : c i ≠ c j) (hcjk : c j ≠ c k) (hckl : c k ≠ c l) (hclp : c l ≠ c p) :
    4 ≤ seqChanges c := by
  obtain ⟨e1, he1p, he1q, he1c⟩ := change_in_range c i.val j.val i.isLt j.isLt hij hcij
  obtain ⟨e2, he2p, he2q, he2c⟩ := change_in_range c j.val k.val j.isLt k.isLt hjk hcjk
  obtain ⟨e3, he3p, he3q, he3c⟩ := change_in_range c k.val l.val k.isLt l.isLt hkl hckl
  obtain ⟨e4, he4p, he4q, he4c⟩ := change_in_range c l.val p.val l.isLt p.isLt hlp hclp
  have hij' : i.val < j.val := hij
  have hjk' : j.val < k.val := hjk
  have hkl' : k.val < l.val := hkl
  have hlp' : l.val < p.val := hlp
  have h12 : e1.val < e2.val := by omega
  have h23 : e2.val < e3.val := by omega
  have h34 : e3.val < e4.val := by omega
  have hne12 : e1 ≠ e2 := by intro h; rw [h] at h12; exact absurd h12 (lt_irrefl _)
  have hne13 : e1 ≠ e3 := by intro h; rw [h] at h12; omega
  have hne14 : e1 ≠ e4 := by intro h; rw [h] at h12; omega
  have hne23 : e2 ≠ e3 := by intro h; rw [h] at h23; exact absurd h23 (lt_irrefl _)
  have hne24 : e2 ≠ e4 := by intro h; rw [h] at h23; omega
  have hne34 : e3 ≠ e4 := by intro h; rw [h] at h34; exact absurd h34 (lt_irrefl _)
  set S := Finset.univ.filter (fun i : Fin M => c i.castSucc ≠ c i.succ) with hS
  have hsub : ({e1, e2, e3, e4} : Finset (Fin M)) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with h | h | h | h <;> subst h <;> assumption
  have hcard4 : ({e1, e2, e3, e4} : Finset (Fin M)).card = 4 :=
    Finset.card_eq_four.mpr ⟨e1, e2, e3, e4, hne12, hne13, hne14, hne23, hne24, hne34, rfl⟩
  calc 4 = ({e1, e2, e3, e4} : Finset (Fin M)).card := hcard4.symm
    _ ≤ S.card := Finset.card_le_card hsub
    _ = seqChanges c := rfl

/-- **Extract five increasing indices from a `[a,b,a,b,a] <+ List.ofFn s` alternation.** Degree-3
analogue of `ofFn_four_indices`. -/
theorem ofFn_five_indices {β : Type*} {m : ℕ} (s : Fin (m + 1) → β) (a b : β)
    (h : [a, b, a, b, a] <+ List.ofFn s) :
    ∃ i j k l p : Fin (m + 1), i < j ∧ j < k ∧ k < l ∧ l < p ∧
      s i = a ∧ s j = b ∧ s k = a ∧ s l = b ∧ s p = a := by
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq] at h
  obtain ⟨f, hf⟩ := h
  have hlenofn : (List.ofFn s).length = m + 1 := List.length_ofFn
  have h5 : [a, b, a, b, a].length = 5 := rfl
  let i5 : Fin [a, b, a, b, a].length := ⟨0, by rw [h5]; omega⟩
  let j5 : Fin [a, b, a, b, a].length := ⟨1, by rw [h5]; omega⟩
  let k5 : Fin [a, b, a, b, a].length := ⟨2, by rw [h5]; omega⟩
  let l5 : Fin [a, b, a, b, a].length := ⟨3, by rw [h5]; omega⟩
  let p5 : Fin [a, b, a, b, a].length := ⟨4, by rw [h5]; omega⟩
  have hij : i5 < j5 := Fin.mk_lt_mk.mpr (by norm_num)
  have hjk : j5 < k5 := Fin.mk_lt_mk.mpr (by norm_num)
  have hkl : k5 < l5 := Fin.mk_lt_mk.mpr (by norm_num)
  have hlp : l5 < p5 := Fin.mk_lt_mk.mpr (by norm_num)
  refine ⟨Fin.cast hlenofn (f i5), Fin.cast hlenofn (f j5), Fin.cast hlenofn (f k5),
    Fin.cast hlenofn (f l5), Fin.cast hlenofn (f p5), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Fin.cast_lt_cast hlenofn).mpr (f.strictMono hij)
  · exact (Fin.cast_lt_cast hlenofn).mpr (f.strictMono hjk)
  · exact (Fin.cast_lt_cast hlenofn).mpr (f.strictMono hkl)
  · exact (Fin.cast_lt_cast hlenofn).mpr (f.strictMono hlp)
  · have hgi := hf i5; rw [List.get_ofFn] at hgi
    have hlhs : [a, b, a, b, a].get i5 = a := rfl
    rw [hlhs] at hgi; exact hgi.symm
  · have hgi := hf j5; rw [List.get_ofFn] at hgi
    have hlhs : [a, b, a, b, a].get j5 = b := rfl
    rw [hlhs] at hgi; exact hgi.symm
  · have hgi := hf k5; rw [List.get_ofFn] at hgi
    have hlhs : [a, b, a, b, a].get k5 = a := rfl
    rw [hlhs] at hgi; exact hgi.symm
  · have hgi := hf l5; rw [List.get_ofFn] at hgi
    have hlhs : [a, b, a, b, a].get l5 = b := rfl
    rw [hlhs] at hgi; exact hgi.symm
  · have hgi := hf p5; rw [List.get_ofFn] at hgi
    have hlhs : [a, b, a, b, a].get p5 = a := rfl
    rw [hlhs] at hgi; exact hgi.symm

/-! ## Stage 1, piece (iii): the cubic score families -/

/-- A general degree-3 multivariate score. Mirrors `QuadScore`; only the one-variable specialization
`CubicLines` is used below. -/
structure CubicScore (d : ℕ) where
  cub : Fin d → Fin d → Fin d → ℝ
  quad : Fin d → Fin d → ℝ
  lin : Fin d → ℝ
  const : ℝ

/-- The value of a `CubicScore` at a point. -/
def CubicScore.eval {d : ℕ} (s : CubicScore d) (x : Fin d → ℝ) : ℝ :=
  (∑ p, ∑ q, ∑ r, s.cub p q r * x p * x q * x r)
    + (∑ p, ∑ q, s.quad p q * x p * x q) + (∑ p, s.lin p * x p) + s.const

/-- A finite family of `n` one-variable cubics `val i t = A i · t³ + B i · t² + C i · t + E i`.
(Degree-3 analogue of `QuadLines`.) -/
structure CubicLines (n : ℕ) where
  A : Fin n → ℝ
  B : Fin n → ℝ
  C : Fin n → ℝ
  E : Fin n → ℝ

/-- The value of cubic `i` at the real point `t`. -/
def CubicLines.val {n : ℕ} (g : CubicLines n) (i : Fin n) (t : ℝ) : ℝ :=
  g.A i * t^3 + g.B i * t^2 + g.C i * t + g.E i

/-- The active (least-argmax) index of the family at `t`. -/
def CubicLines.arg {n : ℕ} (g : CubicLines n) (hn : 0 < n) (t : ℝ) : Fin n :=
  leastArgmax (fun i => g.val i t) hn

/-! ## Stage 1, piece (iv): the cubic-difference polynomial -/

/-- The real cubic-difference polynomial `ED + CD·X + BD·X² + AD·X³`. -/
def cubicDiffPoly (AD BD CD ED : ℝ) : Polynomial ℝ :=
  Polynomial.C ED + Polynomial.C CD * Polynomial.X
    + Polynomial.C BD * Polynomial.X ^ 2 + Polynomial.C AD * Polynomial.X ^ 3

theorem cubicDiffPoly_eval (AD BD CD ED t : ℝ) :
    (cubicDiffPoly AD BD CD ED).eval t = AD * t ^ 3 + BD * t ^ 2 + CD * t + ED := by
  simp only [cubicDiffPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]
  ring

theorem cubicDiffPoly_natDegree_le (AD BD CD ED : ℝ) :
    (cubicDiffPoly AD BD CD ED).natDegree ≤ 3 := by
  unfold cubicDiffPoly
  compute_degree

/-! ## Stage 1, piece (v): the MULTIPLICITY machinery for the per-pair bound

The quadratic per-pair bound `≤ 2` used convexity (the sublevel set of a convex quadratic is an
interval, `OrdConnected`). At degree 3 the sublevel set is NOT an interval, so we count roots **with
multiplicity**. The subtle point is the tangency-from-above (`1,0,1` double-dip): two indicator
flips at a single sample point. Such a point is a *local minimum* of `D` with value 0, so its root
multiplicity is `≥ 2` (`cubic_mult_two_of_localMin`), exactly paying for the two flips. The total
flip count is then dominated by `D.roots.card ≤ natDegree D ≤ 3`.
-/

/-- **A real polynomial with a value-0 local minimum at `x` has root multiplicity `≥ 2` at `x`.**
A local minimum of the (analytic) evaluation forces the derivative to vanish there; combined with
`x` being a root, the algebraic root multiplicity is at least 2 (`char 0`). -/
theorem cubic_mult_two_of_localMin (P : Polynomial ℝ) (x : ℝ) (hP : P ≠ 0)
    (hroot : P.eval x = 0) (hmin : IsLocalMin (fun t => P.eval t) x) :
    2 ≤ rootMultiplicity x P := by
  have hderiv0 : deriv (fun t => P.eval t) x = 0 := hmin.deriv_eq_zero
  have hderiv_eval : deriv (fun t => P.eval t) x = (derivative P).eval x := Polynomial.deriv P
  have h2 : (derivative P).IsRoot x := by
    rw [Polynomial.IsRoot, ← hderiv_eval, hderiv0]
  have hkey := Polynomial.derivative_rootMultiplicity_of_root (hroot : P.IsRoot x)
  rcases eq_or_ne (derivative P) 0 with hd | hd
  · have hconst : P.natDegree = 0 := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hd
    have hPeq : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hconst
    have hev : P.eval x = P.coeff 0 := by rw [hPeq]; simp
    have h1' : P.coeff 0 = 0 := by rw [← hev]; exact hroot
    rw [hPeq, h1'] at hP; simp at hP
  · have hpos : 0 < rootMultiplicity x (derivative P) := (Polynomial.rootMultiplicity_pos hd).mpr h2
    omega

/-- **No interior root + positive left endpoint ⟹ positive on the open interval.** If `D` is
continuous, has no root in `Ioo a b`, and `D a > 0`, then `D > 0` throughout `Ioo a b` (an IVT
crossing would produce an interior root). -/
theorem pos_of_noroot_left {D : ℝ → ℝ} (hD : Continuous D) {a b : ℝ}
    (hnr : ∀ y ∈ Set.Ioo a b, D y ≠ 0) (hpa : 0 < D a) :
    ∀ y ∈ Set.Ioo a b, 0 < D y := by
  intro y hy
  by_contra hyn
  push Not at hyn
  rcases eq_or_lt_of_le hyn with h0 | hlt
  · exact hnr y hy h0
  · have hcont : ContinuousOn D (Set.Icc a y) := hD.continuousOn
    obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo' (le_of_lt hy.1) hcont ⟨hlt, hpa⟩
    exact hnr r ⟨hr.1, lt_trans hr.2 hy.2⟩ hr0

/-- **No interior root + positive right endpoint ⟹ positive on the open interval.** Mirror of
`pos_of_noroot_left`. -/
theorem pos_of_noroot_right {D : ℝ → ℝ} (hD : Continuous D) {a b : ℝ}
    (hnr : ∀ y ∈ Set.Ioo a b, D y ≠ 0) (hpb : 0 < D b) :
    ∀ y ∈ Set.Ioo a b, 0 < D y := by
  intro y hy
  by_contra hyn
  push Not at hyn
  rcases eq_or_lt_of_le hyn with h0 | hlt
  · exact hnr y hy h0
  · have hcont : ContinuousOn D (Set.Icc y b) := hD.continuousOn
    obtain ⟨w, hw, hw0⟩ := intermediate_value_Ioo (le_of_lt hy.2) hcont ⟨hlt, hpb⟩
    exact hnr w ⟨lt_trans hy.1 hw.1, hw.2⟩ hw0

/-- **The from-above touch is a local minimum.** If `D` is continuous, positive at flanking points
`l < x < r`, zero at `x`, and has no root strictly between `l,x` or `x,r`, then `D` has a local
minimum at `x`. This is the analytic core of the `1,0,1` double-dip: a tangency-from-above. -/
theorem localmin_of_collision {D : ℝ → ℝ} (hD : Continuous D) {l x r : ℝ}
    (hlx : l < x) (hxr : x < r) (hDl : 0 < D l) (hDr : 0 < D r) (hDx : D x = 0)
    (hnr1 : ∀ y ∈ Set.Ioo l x, D y ≠ 0) (hnr2 : ∀ y ∈ Set.Ioo x r, D y ≠ 0) :
    IsLocalMin D x := by
  have hp1 : ∀ y ∈ Set.Ioo l x, 0 < D y := pos_of_noroot_left hD hnr1 hDl
  have hp2 : ∀ y ∈ Set.Ioo x r, 0 < D y := pos_of_noroot_right hD hnr2 hDr
  rw [IsLocalMin, IsMinFilter]
  filter_upwards [Ioo_mem_nhds hlx hxr] with y hy
  rw [hDx]
  rcases lt_trichotomy y x with h | h | h
  · exact le_of_lt (hp1 y ⟨hy.1, h⟩)
  · rw [h, hDx]
  · exact le_of_lt (hp2 y ⟨h, hy.2⟩)

/-- **At a flip there is a root in the closed gap.** If the strict-positivity of `D` differs at the
two endpoints `a < b`, then `D` has a root in `Icc a b` (intermediate value theorem). -/
theorem flip_gives_closed_root {D : ℝ → ℝ} (hD : Continuous D) {a b : ℝ} (hab : a < b)
    (hflip : (0 < D a) ≠ (0 < D b)) : ∃ r ∈ Set.Icc a b, D r = 0 := by
  have hcont : ContinuousOn D (Set.Icc a b) := hD.continuousOn
  by_cases hca : 0 < D a
  · have hsb : ¬ (0 < D b) := fun h => hflip (by rw [eq_iff_iff]; exact ⟨fun _ => h, fun _ => hca⟩)
    have hble : D b ≤ 0 := not_lt.mp hsb
    obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' (le_of_lt hab) hcont ⟨hble, le_of_lt hca⟩
    exact ⟨r, hr, hr0⟩
  · have hsb : 0 < D b := by
      by_contra h
      exact hflip (by rw [eq_iff_iff]; exact ⟨fun hh => absurd hh hca, fun hh => absurd hh h⟩)
    have hale : D a ≤ 0 := not_lt.mp hca
    obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc (le_of_lt hab) hcont ⟨hale, le_of_lt hsb⟩
    exact ⟨r, hr, hr0⟩

/-- **At a flip, a root choice with the adaptive interior/boundary dichotomy.** Either the chosen
root sits strictly inside the gap (`Ioo`), or the gap has *no* interior root at all (which, with the
flip, forces the root to a single endpoint and `D` to be single-signed on the open interior). -/
theorem flip_root_choice {D : ℝ → ℝ} (hD : Continuous D) {a b : ℝ} (hab : a < b)
    (hflip : (0 < D a) ≠ (0 < D b)) :
    ∃ r ∈ Set.Icc a b, D r = 0 ∧ (r ∈ Set.Ioo a b ∨ ∀ y ∈ Set.Ioo a b, D y ≠ 0) := by
  by_cases hint : ∃ y ∈ Set.Ioo a b, D y = 0
  · obtain ⟨y, hy, hy0⟩ := hint
    exact ⟨y, ⟨le_of_lt hy.1, le_of_lt hy.2⟩, hy0, Or.inl hy⟩
  · push Not at hint
    obtain ⟨r, hr, hr0⟩ := flip_gives_closed_root hD hab hflip
    exact ⟨r, hr, hr0, Or.inr hint⟩

/-- **No three gaps share a root.** Among the flip-gaps, at most 2 distinct gaps can carry the same
chosen root (which would have to be the unique shared sample point). Uses only that `pts` is strictly
increasing and each chosen root lies in its gap's `Icc`. -/
theorem flip_roots_card_le_two {m : ℕ} {pts : Fin (m + 1) → ℝ}
    (hstrict : ∀ i j : Fin (m + 1), i < j → pts i < pts j)
    (S : Finset (Fin m)) (ρ : Fin m → ℝ)
    (hIcc : ∀ e ∈ S, ρ e ∈ Set.Icc (pts e.castSucc) (pts e.succ)) (x : ℝ) :
    (S.filter (fun e => ρ e = x)).card ≤ 2 := by
  by_contra h
  push Not at h
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := two_lt_card_iff.mp h
  simp only [Finset.mem_filter] at ha hb hc
  have hmono : ∀ i j : Fin (m + 1), i ≤ j → pts i ≤ pts j := by
    intro i j hij
    rcases eq_or_lt_of_le hij with h' | h'
    · rw [h']
    · exact le_of_lt (hstrict i j h')
  have succle : ∀ i j : Fin m, i < j → (i.succ : Fin (m+1)) ≤ j.castSucc := by
    intro i j hij; simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
  have mid_contra : ∀ p q s : Fin m, p ∈ S → q ∈ S → s ∈ S → ρ p = x → ρ q = x → ρ s = x →
      p < q → q < s → False := by
    intro p q s hpS hqS hsS hpx hqx hsx hpq hqs
    have hp := hIcc p hpS; rw [hpx] at hp
    have hq := hIcc q hqS; rw [hqx] at hq
    have hs := hIcc s hsS; rw [hsx] at hs
    have hxle : x ≤ pts q.castSucc := le_trans hp.2 (hmono _ _ (succle p q hpq))
    have heq1 : x = pts q.castSucc := le_antisymm hxle hq.1
    have hxge : pts q.succ ≤ x := le_trans (hmono _ _ (succle q s hqs)) hs.1
    have heq2 : x = pts q.succ := le_antisymm hq.2 hxge
    have hlt : pts q.castSucc < pts q.succ :=
      hstrict _ _ (by simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega)
    rw [← heq1, ← heq2] at hlt; exact absurd hlt (lt_irrefl _)
  rcases lt_trichotomy a b with h1 | h1 | h1
  · rcases lt_trichotomy b c with h2 | h2 | h2
    · exact mid_contra a b c ha.1 hb.1 hc.1 ha.2 hb.2 hc.2 h1 h2
    · exact absurd h2 hbc
    · rcases lt_trichotomy a c with h3 | h3 | h3
      · exact mid_contra a c b ha.1 hc.1 hb.1 ha.2 hc.2 hb.2 h3 h2
      · exact absurd h3 hac
      · exact mid_contra c a b hc.1 ha.1 hb.1 hc.2 ha.2 hb.2 h3 h1
  · exact absurd h1 hab
  · rcases lt_trichotomy a c with h2 | h2 | h2
    · exact mid_contra b a c hb.1 ha.1 hc.1 hb.2 ha.2 hc.2 h1 h2
    · exact absurd h2 hac
    · rcases lt_trichotomy b c with h3 | h3 | h3
      · exact mid_contra b c a hb.1 hc.1 ha.1 hb.2 hc.2 ha.2 h3 h2
      · exact absurd h3 hbc
      · exact mid_contra c b a hc.1 hb.1 ha.1 hc.2 hb.2 ha.2 h3 h1

/-! ## Stage 1, piece (vi): THE PER-PAIR ORDER-3 BOUND `≤ 3` -/

open Classical in
/-- **THE PER-PAIR ORDER-3 BOUND.** Along any increasing sample, the strict comparison
`val i < val j` of two cubics changes value at most **3** times. The difference `D = val j − val i`
is a degree-≤3 real polynomial. Each flip is charged against root *multiplicity*: transversal
crossings cost 1, while a tangency-from-above (the `1,0,1` double-dip, two flips at one sample) is a
genuine double root (`cubic_mult_two_of_localMin`). Hence the flip count is dominated by
`D.roots.card ≤ natDegree D ≤ 3`. -/
theorem CubicLines.pair_comparison_le {n : ℕ} (g : CubicLines n) (i j : Fin n) {m : ℕ}
    (pts : Fin (m + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => if g.val i (pts k) < g.val j (pts k) then (1 : Fin 2) else 0) ≤ 3 := by
  -- strict-increasing as a plain predicate
  have hstrict : ∀ a b : Fin (m + 1), a < b → pts a < pts b := fun a b h => hinc a b h
  set AD := g.A j - g.A i with hAD
  set BD := g.B j - g.B i with hBD
  set CD := g.C j - g.C i with hCD
  set ED := g.E j - g.E i with hED
  set P := cubicDiffPoly AD BD CD ED with hP
  set D : ℝ → ℝ := fun t => P.eval t with hD
  have hDexp : ∀ t, D t = g.val j t - g.val i t := by
    intro t
    simp only [hD, hP, cubicDiffPoly_eval, hAD, hBD, hCD, hED, CubicLines.val]; ring
  have hcmp : ∀ t, (g.val i t < g.val j t) ↔ (0 < D t) := by
    intro t; rw [hDexp]; constructor <;> intro h <;> linarith
  have hcongr : (fun k => if g.val i (pts k) < g.val j (pts k) then (1 : Fin 2) else 0)
      = (fun k => if 0 < D (pts k) then (1 : Fin 2) else 0) := by
    funext k; by_cases h : g.val i (pts k) < g.val j (pts k)
    · rw [if_pos h, if_pos ((hcmp (pts k)).mp h)]
    · rw [if_neg h, if_neg (fun hh => h ((hcmp (pts k)).mpr hh))]
  rw [hcongr]
  set c : Fin (m + 1) → Fin 2 := fun k => if 0 < D (pts k) then (1 : Fin 2) else 0 with hc
  have hDcont : Continuous D := P.continuous
  unfold seqChanges
  set S : Finset (Fin m) := Finset.univ.filter (fun e : Fin m => c e.castSucc ≠ c e.succ) with hS
  -- the indicator-flip ⟺ strict-positivity flip
  have hflipiff : ∀ e ∈ S, (0 < D (pts e.castSucc)) ≠ (0 < D (pts e.succ)) := by
    intro e he
    have hch : c e.castSucc ≠ c e.succ := (Finset.mem_filter.mp he).2
    intro heq
    apply hch
    simp only [hc]
    by_cases h1 : 0 < D (pts e.castSucc)
    · rw [if_pos h1, if_pos (by rw [← heq]; exact h1)]
    · rw [if_neg h1, if_neg (by rw [← heq]; exact h1)]
  -- gap endpoints are strictly ordered
  have hgaplt : ∀ e : Fin m, pts e.castSucc < pts e.succ := fun e =>
    hstrict _ _ (by simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega)
  -- adaptive root choice
  have hchoice : ∀ e ∈ S, ∃ r ∈ Set.Icc (pts e.castSucc) (pts e.succ), D r = 0 ∧
      (r ∈ Set.Ioo (pts e.castSucc) (pts e.succ) ∨
       ∀ y ∈ Set.Ioo (pts e.castSucc) (pts e.succ), D y ≠ 0) :=
    fun e he => flip_root_choice hDcont (hgaplt e) (hflipiff e he)
  choose! ρ hρIcc hρ0 hρdich using hchoice
  -- handle P = 0 separately
  rcases eq_or_ne P 0 with hPz | hPne
  · -- P = 0 ⟹ D ≡ 0 ⟹ indicator constant ⟹ S empty
    have : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      have hch : c e.castSucc ≠ c e.succ := (Finset.mem_filter.mp he).2
      apply hch
      simp only [hc, hD, hPz, Polynomial.eval_zero, lt_irrefl, if_false]
    rw [this]; simp
  -- P ≠ 0: multiset domination of the chosen-root multiset into P.roots
  -- card S = (S.val.map ρ).card ≤ P.roots.card ≤ natDegree ≤ 3
  have hcardmap : (S.val.map ρ).card = S.card := by rw [Multiset.card_map]; rfl
  -- the per-point count bound: count x (S.val.map ρ) ≤ rootMultiplicity x P
  have hcount : ∀ x : ℝ, Multiset.count x (S.val.map ρ) ≤ rootMultiplicity x P := by
    intro x
    -- rewrite count as filter card
    have hcm : Multiset.count x (S.val.map ρ) = (S.filter (fun e => ρ e = x)).card := by
      rw [Multiset.count_map, Finset.card, Finset.filter_val]
      congr 1
      apply Multiset.filter_congr
      intro a _; rw [eq_comm]
    rw [hcm]
    -- card ≤ 2 always
    have hcard2 : (S.filter (fun e => ρ e = x)).card ≤ 2 :=
      flip_roots_card_le_two hstrict S ρ hρIcc x
    rcases Nat.lt_or_ge (S.filter (fun e => ρ e = x)).card 2 with hlt | hge
    · interval_cases hcc : (S.filter (fun e => ρ e = x)).card
      · omega
      · obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcc
        have heS : e ∈ S.filter (fun e => ρ e = x) := by
          rw [he]; exact Finset.mem_singleton_self e
        simp only [Finset.mem_filter] at heS
        have hrx : P.eval x = 0 := by
          have := hρ0 e heS.1; rw [heS.2] at this; exact this
        have : 0 < rootMultiplicity x P := (Polynomial.rootMultiplicity_pos hPne).mpr hrx
        omega
    · -- card = 2: the two gaps collide ⟹ tangency-from-above ⟹ double root
      have hcardeq : (S.filter (fun e => ρ e = x)).card = 2 := le_antisymm hcard2 hge
      obtain ⟨e1, e2, hne12, hfeq⟩ := Finset.card_eq_two.mp hcardeq
      -- recover memberships
      have he1mem : e1 ∈ S.filter (fun e => ρ e = x) := by rw [hfeq]; simp
      have he2mem : e2 ∈ S.filter (fun e => ρ e = x) := by rw [hfeq]; simp
      simp only [Finset.mem_filter] at he1mem he2mem
      obtain ⟨he1S, he1x⟩ := he1mem
      obtain ⟨he2S, he2x⟩ := he2mem
      -- x is a root of P
      have hrx : P.eval x = 0 := by have := hρ0 e1 he1S; rw [he1x] at this; exact this
      -- order e1, e2 so that lo < hi
      -- introduce a helper that, for adjacent colliding gaps lo<hi, builds the local min
      have build_min : ∀ lo hi : Fin m, lo ∈ S → hi ∈ S → ρ lo = x → ρ hi = x → lo < hi →
          IsLocalMin (fun t => P.eval t) x := by
        intro lo hi hloS hhiS hlox hhix hlohi
        -- from the Icc memberships and ordering, x = pts lo.succ = pts hi.castSucc
        have hmono : ∀ p q : Fin (m + 1), p ≤ q → pts p ≤ pts q := by
          intro p q hpq
          rcases eq_or_lt_of_le hpq with h' | h'
          · rw [h']
          · exact le_of_lt (hstrict p q h')
        have hloIcc := hρIcc lo hloS; rw [hlox] at hloIcc
        have hhiIcc := hρIcc hi hhiS; rw [hhix] at hhiIcc
        have hsucle : (lo.succ : Fin (m+1)) ≤ hi.castSucc := by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
        have hxle : x ≤ pts hi.castSucc := le_trans hloIcc.2 (hmono _ _ hsucle)
        have hxeq_cs : x = pts hi.castSucc := le_antisymm hxle hhiIcc.1
        have hxeq_su : x = pts lo.succ := by
          have hle1 : x ≤ pts lo.succ := hloIcc.2
          have hge1 : pts lo.succ ≤ x := by
            calc pts lo.succ ≤ pts hi.castSucc := hmono _ _ hsucle
              _ = x := hxeq_cs.symm
          exact le_antisymm hle1 hge1
        -- the flanking samples: left = pts lo.castSucc, right = pts hi.succ
        have hLlt : pts lo.castSucc < x := by rw [hxeq_su]; exact hgaplt lo
        have hRgt : x < pts hi.succ := by rw [hxeq_cs]; exact hgaplt hi
        -- D at flanking samples is > 0 (since x is a 0-sample, neighbors must be positive given flip)
        -- D x = 0 ⟹ c at x-sample is 0 ⟹ flanking c = 1 ⟹ D flanking > 0
        have hDx : D x = 0 := by have := hρ0 lo hloS; rw [hlox] at this; exact this
        -- left endpoint positivity: flip at lo means (0<D lo.cs) ≠ (0<D lo.su=x); D x = 0 ⟹ not pos at x
        have hnotposx : ¬ (0 < D x) := by rw [hDx]; exact lt_irrefl 0
        have hloflip := hflipiff lo hloS
        have hDlpos : 0 < D (pts lo.castSucc) := by
          by_contra hh
          -- then both endpoints not positive ⟹ no flip
          apply hloflip
          rw [eq_iff_iff]
          constructor
          · intro hx; exact absurd hx hh
          · intro hx; rw [hxeq_su] at hnotposx; exact absurd hx hnotposx
        have hhiflip := hflipiff hi hhiS
        have hDrpos : 0 < D (pts hi.succ) := by
          by_contra hh
          apply hhiflip
          rw [eq_iff_iff]
          constructor
          · intro hx; rw [hxeq_cs] at hnotposx; exact absurd hx hnotposx
          · intro hx; exact absurd hx hh
        -- no interior roots in the two gaps (else the dichotomy's first branch would have placed ρ interior)
        have hnr1 : ∀ y ∈ Set.Ioo (pts lo.castSucc) x, D y ≠ 0 := by
          rw [hxeq_su]
          rcases hρdich lo hloS with hint | hnone
          · -- ρ lo ∈ Ioo, but ρ lo = x = pts lo.succ = right endpoint, contradiction with Ioo
            rw [hlox, hxeq_su] at hint
            exact absurd hint.2 (lt_irrefl _)
          · exact hnone
        have hnr2 : ∀ y ∈ Set.Ioo x (pts hi.succ), D y ≠ 0 := by
          rw [hxeq_cs]
          rcases hρdich hi hhiS with hint | hnone
          · rw [hhix, hxeq_cs] at hint
            exact absurd hint.1 (lt_irrefl _)
          · exact hnone
        exact localmin_of_collision hDcont hLlt hRgt hDlpos hDrpos hDx hnr1 hnr2
      -- apply build_min in the correct order
      have hmin : IsLocalMin (fun t => P.eval t) x := by
        rcases lt_or_gt_of_ne hne12 with hlt12 | hgt12
        · exact build_min e1 e2 he1S he2S he1x he2x hlt12
        · exact build_min e2 e1 he2S he1S he2x he1x hgt12
      have hge2 : 2 ≤ rootMultiplicity x P := cubic_mult_two_of_localMin P x hPne hrx hmin
      omega
  -- assemble: card S ≤ P.roots.card ≤ natDegree ≤ 3
  have hdom : (S.val.map ρ) ≤ P.roots := by
    rw [Multiset.le_iff_count]
    intro x
    have hc1 := hcount x
    rwa [Polynomial.count_roots]
  calc S.card = (S.val.map ρ).card := hcardmap.symm
    _ ≤ P.roots.card := Multiset.card_le_card hdom
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ 3 := cubicDiffPoly_natDegree_le AD BD CD ED

/-! ## Stage 1, piece (vii): the argmax has `NoABABA` -/

/-- The least-argmax of a `CubicLines` family is a maximizer. -/
theorem CubicLines.arg_eq_maximizer {n : ℕ} (g : CubicLines n) (hn : 0 < n) (t : ℝ) (a b : Fin n)
    (h : g.arg hn t = a) : g.val b t ≤ g.val a t := by
  have := leastArgmax_is_maximizer (fun i => g.val i t) hn b
  rw [show leastArgmax (fun i => g.val i t) hn = a from h] at this
  exact this

/-- The least-argmax of a `CubicLines` family is the least maximizer. -/
theorem CubicLines.arg_eq_least {n : ℕ} (g : CubicLines n) (hn : 0 < n) (t : ℝ) (a jj : Fin n)
    (h : g.arg hn t = a) (hj : jj < a) : g.val jj t < g.val a t := by
  have := leastArgmax_is_least (fun i => g.val i t) hn jj
  rw [show leastArgmax (fun i => g.val i t) hn = a from h] at this
  exact this hj

/-- **THE CUBIC ARGMAX IS `NoABABA`.** Along ANY strictly-increasing sample, the active index of `n`
cubics has no `a,b,a,b,a` alternation. An `a,b,a,b,a` argmax pattern forces the `a`-vs-`b`
comparison indicator to flip `≥ 4` times (`seqChanges_ge_four`), contradicting the per-pair order-3
bound `CubicLines.pair_comparison_le ≤ 3`. This is the cubic analogue of `quadArg_noABAB` and the
order-3 Davenport–Schinzel structure. -/
theorem cubicArg_noABABA {n : ℕ} (g : CubicLines n) (hn : 0 < n) {m : ℕ}
    (pts : Fin (m + 1) → ℝ) (hinc : Increasing pts) :
    NoABABA (List.ofFn (fun k => g.arg hn (pts k))) := by
  intro a b hab hsub
  obtain ⟨i, j, k, l, p, hij, hjk, hkl, hlp, hai, hbj, hak, hbl, hap⟩ :=
    ofFn_five_indices (fun k => g.arg hn (pts k)) a b hsub
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · -- a < b : indicator c t = [val a t < val b t] reads 1,0,1,0,1 (a-points 0, b-points 1)
    set c : Fin (m + 1) → Fin 2 :=
      fun t => if g.val a (pts t) < g.val b (pts t) then (1 : Fin 2) else 0 with hc
    have hca : ∀ t, g.arg hn (pts t) = a → c t = 0 := by
      intro t ht
      have hle : g.val b (pts t) ≤ g.val a (pts t) := g.arg_eq_maximizer hn (pts t) a b ht
      rw [hc]; simp only; rw [if_neg (by linarith)]
    have hcb : ∀ t, g.arg hn (pts t) = b → c t = 1 := by
      intro t ht
      have hlt' : g.val a (pts t) < g.val b (pts t) := g.arg_eq_least hn (pts t) b a ht hlt
      rw [hc]; simp only; rw [if_pos hlt']
    have hci := hca i hai
    have hcj := hcb j hbj
    have hck := hca k hak
    have hcl := hcb l hbl
    have hcp := hca p hap
    have h4 : 4 ≤ seqChanges c :=
      seqChanges_ge_four c i j k l p hij hjk hkl hlp
        (by rw [hci, hcj]; decide) (by rw [hcj, hck]; decide)
        (by rw [hck, hcl]; decide) (by rw [hcl, hcp]; decide)
    have h3 : seqChanges c ≤ 3 := g.pair_comparison_le a b pts hinc
    omega
  · -- b < a : indicator c t = [val b t < val a t]
    set c : Fin (m + 1) → Fin 2 :=
      fun t => if g.val b (pts t) < g.val a (pts t) then (1 : Fin 2) else 0 with hc
    have hca : ∀ t, g.arg hn (pts t) = a → c t = 1 := by
      intro t ht
      have hlt' : g.val b (pts t) < g.val a (pts t) := g.arg_eq_least hn (pts t) a b ht hgt
      rw [hc]; simp only; rw [if_pos hlt']
    have hcb : ∀ t, g.arg hn (pts t) = b → c t = 0 := by
      intro t ht
      have hle : g.val a (pts t) ≤ g.val b (pts t) := g.arg_eq_maximizer hn (pts t) b a ht
      rw [hc]; simp only; rw [if_neg (by linarith)]
    have hci := hca i hai
    have hcj := hcb j hbj
    have hck := hca k hak
    have hcl := hcb l hbl
    have hcp := hca p hap
    have h4 : 4 ≤ seqChanges c :=
      seqChanges_ge_four c i j k l p hij hjk hkl hlp
        (by rw [hci, hcj]; decide) (by rw [hcj, hck]; decide)
        (by rw [hck, hcl]; decide) (by rw [hcl, hcp]; decide)
    have h3 : seqChanges c ≤ 3 := g.pair_comparison_le b a pts hinc
    omega

/-! ## Stage 2: the SUPERLINEARITY phase transition (status)

The order-3 Davenport–Schinzel length `λ₃(n)` is super-linear: `λ₃(n) = Θ(n · α(n))` where `α` is the
inverse Ackermann function. In particular `λ₃(n)` is NOT `O(n)`, unlike the quadratic `2n − 1`. The
closed order-3 structure above (`cubicArg_noABABA`) is the qualitative phase-transition marker: the
forbidden pattern jumps from length 4 (quadratic, linear count) to length 5 (cubic, super-linear
count).

**Remaining obligation (the superlinearity witness).** A fully formal super-linearity proof requires
an explicit family of `n` cubics whose argmax alternation count provably exceeds `C · n` for every
constant `C`. The standard construction is the Wiernik–Sharir recursive gadget. Formalizing it
requires: (a) a recursive cubic-fan builder; (b) the count recurrence `λ₃(2n) ≥ 2 λ₃(n) + Ω(n)`
unrolled to a `Θ(n · α(n))` lower bound; (c) the inverse Ackermann function `α`, which is **absent
from Mathlib**. We do NOT fake this count. The qualitative jump (length-5 forbidden pattern, no linear
closed form) is captured by `cubicArg_noABABA` together with this status note; the quantitative
`Θ(n · α(n))` is the aspirational α-gap and is deliberately left open.
-/

end TLT.TemperedDesignLaw
