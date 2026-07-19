/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.ArrangementVC
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

/-!
# The tameness bridge for degree-`d` polynomial (argmax-router) scores

The degree-`d` generalization of `QuadraticTameness.lean` (degree `2`) and the affine `coordSpan`
case (degree `1`). There the per-pair score *difference* of two affine/quadratic scores lives in the
finite-dimensional span of the degree-≤1 / degree-≤2 monomials, so the landed arrangement-VC
Sauer-product bound `symbolClass_growth_prod` (`ArrangementVC.lean`) applies and the route class has
**finite VC** (polynomial growth). Here we lift that to arbitrary degree `d`: a degree-≤`d` polynomial
score difference lies in the span `polySpan dim d` of the degree-≤`d` monomials, which is
finite-dimensional (`finrank ≤ Fintype.card {a // ∑ a ≤ d} = C(d+dim,dim)`), so the *same* machinery
gives the degree-`d` argmax router's symbol class finite VC.

The mechanism is the design-manual thesis at full generality: the only nontrivial hypothesis of
`symbolClass_growth_prod` is `hlin`, that each per-pair score difference lies in a finite-dimensional
submodule `W`. For any degree-≤`d` polynomial scores the difference is again degree-≤`d`, hence in
`polySpan dim d`. We instantiate `W := polySpan dim d` and obtain the finite Sauer-product growth
bound for free, with feature dimension `≤ C(d+dim,dim)` (the number of degree-≤`d` monomials).

## Results

* `polySpan dim d` : the span of the degree-≤`d` monomial evaluation functions
  `x ↦ ∏ i, (x i)^(a i)` for `a : Fin dim → ℕ` with `∑ i, a i ≤ d`. `FiniteDimensional` by
  construction (a span of a finite set), with `finrank ≤ Fintype.card (PolyMonoIdx dim d)`
  (`finrank_polySpan_le_card`) and, exactly, `finrank ≤ (d + dim).choose dim` (`finrank_polySpan_le`).
* `card_polyMonoIdx` : the exact stars-and-bars count
  `Fintype.card (PolyMonoIdx dim d) = (d + dim).choose dim`.
* `polyScoreDiff_mem_polySpan` : every degree-≤`d` polynomial-score difference
  `x ↦ s.eval x − t.eval x` lies in `polySpan dim d` (a finite ℝ-linear combination of the monomials).
* `polyRouter dim nK d` : a `FiniteScoreRouterCode (Fin dim → ℝ) nK` whose scores are degree-≤`d`
  evaluated polynomials.
* `polyRouter_growth_prod` (**the tameness bridge**) : the Sauer-product capacity bound for the
  degree-`d` polynomial-scored route class, an instantiation of `symbolClass_growth_prod` at
  `W := polySpan dim d`. Finite VC, same machinery, `finrank polySpan ≤ C(d+dim,dim)`.

This completes the capacity face of the design law's degree-`d` master parameter: every fixed-degree
polynomial argmax router is learnable (finite VC); only non-polynomial (arbitrary measurable) scores
escape to infinite VC / the wild non-Borel regime.
-/

open scoped BigOperators
open Module

noncomputable section

namespace TLT.TemperedDesignLaw

/-! ## 1. The degree-`d` monomial feature span `polySpan dim d` -/

/-- The index type of the degree-≤`d` monomials on `Fin dim → ℝ`: the exponent vectors
`a : Fin dim → ℕ` with total degree `∑ i, a i ≤ d`. It is a `Fintype` (each coordinate is bounded by
`d`), of cardinality `(d + dim).choose dim` (`card_polyMonoIdx`, stars and bars). -/
abbrev PolyMonoIdx (dim d : ℕ) := {a : Fin dim → ℕ // ∑ i, a i ≤ d}

/-- **`PolyMonoIdx dim d` is a `Fintype`.** Each exponent `a i ≤ ∑ a ≤ d`, so the subtype injects into
`Fin dim → Fin (d + 1)`, a finite type. -/
instance polyMonoIdxFintype (dim d : ℕ) : Fintype (PolyMonoIdx dim d) := by
  classical
  apply Fintype.ofInjective
    (f := fun a : PolyMonoIdx dim d => (fun i => (⟨a.1 i, by
      have h1 : a.1 i ≤ ∑ j, a.1 j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have h2 := a.2
      omega⟩ : Fin (d + 1))))
  intro a b hab
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun hab i)

/-- The degree-≤`d` monomial functions on `Fin dim → ℝ`, indexed by `PolyMonoIdx dim d`:
the exponent vector `a` maps to `x ↦ ∏ i, (x i)^(a i)`. -/
def polyMono (dim d : ℕ) : PolyMonoIdx dim d → ((Fin dim → ℝ) → ℝ) :=
  fun a => fun x => ∏ i, (x i) ^ (a.1 i)

/-- **The degree-`d` feature span.** The span of the degree-≤`d` monomials on `Fin dim → ℝ`. Every
degree-≤`d` polynomial-score difference lives here (`polyScoreDiff_mem_polySpan`), so this is the
finite-dimensional `W` that the arrangement-VC Sauer product needs for degree-`d` polynomial scores.
It is to the degree-`d` case what `coordSpan dim` (degree `1`) and `quadSpan dim` (degree `2`) are to
those cases, only `≤ C(d+dim,dim)`-dimensional. -/
def polySpan (dim d : ℕ) : Submodule ℝ ((Fin dim → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range (polyMono dim d))

/-- **`polySpan dim d` is finite-dimensional.** It is the span of a finite set (the
`PolyMonoIdx dim d`-indexed range, and `PolyMonoIdx dim d` is a `Fintype`). Identical pattern to
`coordSpan_finiteDim` / `quadSpan_finiteDim`. -/
instance polySpan_finiteDim (dim d : ℕ) : FiniteDimensional ℝ (polySpan dim d) := by
  unfold polySpan
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- **The dimension budget (finite form).** `finrank ℝ (polySpan dim d) ≤ Fintype.card (PolyMonoIdx dim d)`:
the span of the `PolyMonoIdx dim d`-indexed family has rank at most the cardinality of the index. This
is the FINITE bound that tameness needs; `finrank_polySpan_le` upgrades it to the exact binomial. -/
theorem finrank_polySpan_le_card (dim d : ℕ) :
    finrank ℝ (polySpan dim d) ≤ Fintype.card (PolyMonoIdx dim d) := by
  unfold polySpan
  exact finrank_range_le_card (polyMono dim d)

/-! ## 2. The exact stars-and-bars count `Fintype.card (PolyMonoIdx dim d) = C(d+dim,dim)` -/

/-- **The exact stars-and-bars count.** `Fintype.card {a : Fin dim → ℕ // ∑ i, a i ≤ d} = (d + dim).choose dim`:
the number of monomials of degree `≤ d` in `dim` variables. Proved by the slack-variable bijection to
the exact-degree exponent vectors on `dim + 1` variables (`Finset.piAntidiag univ d`, whose card is
`(dim + 1).multichoose d = (dim + d).choose d = (d + dim).choose dim` by stars and bars). -/
theorem card_polyMonoIdx (dim d : ℕ) :
    Fintype.card (PolyMonoIdx dim d) = (d + dim).choose dim := by
  classical
  -- Step 1: the slack-variable bijection `{a : Fin dim → ℕ // ∑ a ≤ d} ≃ piAntidiag (univ : Fin (dim+1)) d`
  -- (append a `(dim+1)`-th coordinate `d − ∑ a` so the total degree becomes exactly `d`).
  have hcard1 :
      Fintype.card (PolyMonoIdx dim d)
        = (Finset.piAntidiag (Finset.univ : Finset (Fin (dim + 1))) d).card := by
    rw [← Fintype.card_coe (Finset.piAntidiag (Finset.univ : Finset (Fin (dim + 1))) d)]
    apply Fintype.card_congr
    refine {
      toFun := fun a => ⟨Fin.snoc a.1 (d - ∑ i, a.1 i), ?_⟩
      invFun := fun b => ⟨Fin.init b.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
    · rw [Finset.mem_piAntidiag]
      refine ⟨?_, fun i _ => Finset.mem_univ i⟩
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      have := a.2
      omega
    · have hb := b.2
      rw [Finset.mem_piAntidiag] at hb
      have hsum : ∑ i, b.1 i = d := hb.1
      rw [Fin.sum_univ_castSucc] at hsum
      have : ∑ i : Fin dim, Fin.init b.1 i ≤ ∑ i : Fin dim, Fin.init b.1 i + b.1 (Fin.last dim) := by
        omega
      simp only [Fin.init] at this ⊢
      omega
    · intro a
      apply Subtype.ext
      funext i
      simp [Fin.init, Fin.snoc_castSucc]
    · intro b
      apply Subtype.ext
      have hb := b.2
      rw [Finset.mem_piAntidiag] at hb
      have hsum : ∑ i, b.1 i = d := hb.1
      rw [Fin.sum_univ_castSucc] at hsum
      funext i
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last, Fin.init]
        have : ∑ j : Fin dim, b.1 j.castSucc + b.1 (Fin.last dim) = d := hsum
        omega
      · intro j
        simp [Fin.snoc_castSucc, Fin.init]
  -- Step 2: `#(piAntidiag univ d) = #(finsuppAntidiag univ d) = (dim+1+d-1).choose d` (stars and bars).
  rw [hcard1,
    show (Finset.piAntidiag (Finset.univ : Finset (Fin (dim + 1))) d).card
        = (Finset.finsuppAntidiag (Finset.univ : Finset (Fin (dim + 1))) d).card by
      rw [Finset.finsuppAntidiag, Finset.card_map, Finset.card_attach],
    Finset.card_finsuppAntidiag_nat_eq_choose]
  -- Step 3: `(#univ + d - 1).choose d = (d + dim).choose dim`.
  simp only [Finset.card_univ, Fintype.card_fin]
  have h1 : dim + 1 + d - 1 = d + dim := by omega
  rw [h1]
  exact Nat.choose_symm_of_eq_add (n := d + dim) (a := d) (b := dim) (by omega)

/-- **The dimension budget (exact binomial).** `finrank ℝ (polySpan dim d) ≤ (d + dim).choose dim`:
the number of degree-≤`d` monomials in `dim` variables. The exact stars-and-bars capacity that makes
the degree-`d` bound nonvacuous (vs. `dim` in the affine `coordSpan` case and `dim²+dim+1` in the
quadratic `quadSpan` case). -/
theorem finrank_polySpan_le (dim d : ℕ) :
    finrank ℝ (polySpan dim d) ≤ (d + dim).choose dim := by
  refine le_trans (finrank_polySpan_le_card dim d) ?_
  rw [card_polyMonoIdx dim d]

/-! ## 3. Degree-`d` polynomial scores and the score-difference membership -/

/-- A degree-≤`d` polynomial score on `Fin dim → ℝ`, carried as its coefficient vector over the
degree-≤`d` monomial index. `eval x = ∑ a, coeff a · ∏ i, (x i)^(a i)`. This is the minimal degree-`d`
score type: a literal ℝ-linear combination of `polyMono dim d`, so its differences land in `polySpan`
on the nose and its evaluation is jointly measurable in `(coeff, x)`. -/
structure PolyScore (dim d : ℕ) where
  /-- The coefficient of each degree-≤`d` monomial. -/
  coeff : PolyMonoIdx dim d → ℝ

/-- Evaluate a degree-≤`d` polynomial score at `x`: the linear combination of the monomials. -/
def PolyScore.eval {dim d : ℕ} (s : PolyScore dim d) (x : Fin dim → ℝ) : ℝ :=
  ∑ a : PolyMonoIdx dim d, s.coeff a * polyMono dim d a x

/-- **Every degree-≤`d` polynomial-score difference lies in `polySpan dim d`.** For two scores `s t`,
the difference `x ↦ s.eval x − t.eval x = ∑ a, (s.coeff a − t.coeff a) · polyMono a x` is a finite
ℝ-linear combination of the monomials `polyMono dim d`, hence in their span. The degree-`d` analogue
of `attnScoreDiff_mem_coordSpan` (degree 1) and `quadScoreDiff_mem_quadSpan` (degree 2). -/
theorem polyScoreDiff_mem_polySpan (dim d : ℕ) (s t : PolyScore dim d) :
    (fun x => s.eval x - t.eval x) ∈ polySpan dim d := by
  have heq : (fun x : Fin dim → ℝ => s.eval x - t.eval x)
      = ∑ a : PolyMonoIdx dim d, (s.coeff a - t.coeff a) • polyMono dim d a := by
    funext x
    simp only [PolyScore.eval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  rw [heq, polySpan]
  exact Submodule.sum_mem _ (fun a _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a)))

/-! ## 4. The degree-`d` polynomial-scored route class -/

/-- The parameter space of the degree-`d` polynomial router: `nK` independent coefficient vectors, one
per head, carried as raw data so the native `Pi` `MeasurableSpace`/`StandardBorelSpace` instances apply
(`PolyScore` is a bare structure). `polyParamScore` reconstructs the `i`-th `PolyScore` from this data. -/
abbrev PolyParam (dim nK d : ℕ) := Fin nK → PolyMonoIdx dim d → ℝ

/-- `PolyParam dim nK d` is a standard Borel space (a finite product of copies of ℝ). -/
instance polyParam_sb (dim nK d : ℕ) : StandardBorelSpace (PolyParam dim nK d) := inferInstance

/-- Reconstruct the `i`-th polynomial score from the raw coefficient data. -/
def polyParamScore {dim nK d : ℕ} (K : PolyParam dim nK d) (i : Fin nK) : PolyScore dim d :=
  ⟨K i⟩

/-- **The degree-`d` polynomial-scored router** as a `FiniteScoreRouterCode (Fin dim → ℝ) nK`. The
input is a coordinate vector `x : Fin dim → ℝ`, the parameter is `nK` coefficient vectors
(`PolyParam dim nK d`), and the score for head `i` is `PolyScore.eval` of the `i`-th reconstructed
degree-≤`d` polynomial at `x`. This is the degree-`d` argmax-router score class. -/
def polyRouter (dim nK d : ℕ) : FiniteScoreRouterCode (Fin dim → ℝ) nK where
  Ρ := PolyParam dim nK d
  instMeasΡ := inferInstance
  instStdΡ := polyParam_sb dim nK d
  score := fun K x i => (polyParamScore K i).eval x
  score_meas := fun i => by
    simp only [polyParamScore, PolyScore.eval, polyMono]
    -- measurable as a finite sum (over monomials) of products of coordinate projections, jointly in (K, x)
    refine Finset.measurable_sum Finset.univ (fun a _ => ?_)
    have hcoeff : Measurable (fun p : PolyParam dim nK d × (Fin dim → ℝ) => p.1 i a) :=
      (measurable_pi_apply a).comp ((measurable_pi_apply i).comp measurable_fst)
    have hmono : Measurable (fun p : PolyParam dim nK d × (Fin dim → ℝ) => ∏ j, (p.2 j) ^ (a.1 j)) := by
      refine Finset.measurable_prod Finset.univ (fun j _ => ?_)
      exact ((measurable_pi_apply j).comp measurable_snd).pow_const (a.1 j)
    exact hcoeff.mul hmono

/-- **The polynomial router's score is literally `PolyScore.eval`.** Definitional unfolding. -/
@[simp] theorem polyRouter_score (dim nK d : ℕ) (K : PolyParam dim nK d) (x : Fin dim → ℝ)
    (i : Fin nK) : (polyRouter dim nK d).score K x i = (polyParamScore K i).eval x := rfl

/-- **The polynomial router's per-pair score differences lie in `polySpan dim d`.** Specializing
`polyScoreDiff_mem_polySpan` to the two reconstructed polynomial scores at the heads of the ordered
pair. This is the `hlin` hypothesis of the arrangement-VC Sauer product, satisfied for degree-`d`
polynomial scores. -/
theorem polyRouterScoreDiff_mem_polySpan (dim nK d : ℕ) (p : Fin nK × Fin nK)
    (K : (polyRouter dim nK d).Ρ) :
    (fun x => (polyRouter dim nK d).score K x p.2 - (polyRouter dim nK d).score K x p.1)
      ∈ polySpan dim d := by
  simpa using polyScoreDiff_mem_polySpan dim d (polyParamScore K p.2) (polyParamScore K p.1)

/-! ## 5. The tameness bridge: finite Sauer-product capacity for the degree-`d` route class -/

/-- **THE TAMENESS BRIDGE (degree-`d` polynomial scores).** The arrangement-VC Sauer-product capacity
bound for the degree-`d` polynomial-scored route class, an instantiation of the landed affine machinery
`symbolClass_growth_prod` at `W := polySpan dim d`. On any finite sample `S`, the number of
routing-label patterns the degree-`d` router realises is at most the product over the `nK²` ordered
pairs of the Sauer–Shelah binomial sums at `finrank ℝ (polySpan dim d) ≤ C(d+dim,dim)`, a polynomial
in `|S|` of degree the total comparison VC dimension `≤ nK²·C(d+dim,dim)`.

The point: this is the *same* machinery as the affine (`coordSpan`, degree 1) and quadratic
(`quadSpan`, degree 2) cases, only the feature dimension grows to the `C(d+dim,dim)` degree-≤`d`
monomials. Every fixed-degree polynomial argmax router is **learnable** (finite VC) precisely because
polynomial score-differences are finite-dimensional. Only non-polynomial (arbitrary measurable) scores
escape this (to infinite VC / the wild non-Borel regime). -/
theorem polyRouter_growth_prod (dim nK d : ℕ) (hnK : 0 < nK) (S : Finset (Fin dim → ℝ)) :
    (Set.range (routeRestr (polyRouter dim nK d) hnK S)).ncard
      ≤ ∏ _p : Fin nK × Fin nK,
          ∑ r ∈ Finset.range (finrank ℝ (polySpan dim d) + 1), S.card.choose r := by
  have h := symbolClass_growth_prod (polyRouter dim nK d) hnK
    (fun _ => polySpan dim d) (fun _ => inferInstance)
    (fun p K => polyRouterScoreDiff_mem_polySpan dim nK d p K) S
  simpa using h

/-- **The single-polynomial form of the tameness bridge.** Collapsing the per-pair product (every
factor shares the single feature space `polySpan dim d`): the degree-`d` route class's combinatorial
capacity on `S` is `(∑_{r ≤ finrank polySpan dim d} |S| choose r)^{nK²}`, finite for every sample.
The explicit `symbolClass_growth_uniform` instantiation. -/
theorem polyRouter_growth_uniform (dim nK d : ℕ) (hnK : 0 < nK) (S : Finset (Fin dim → ℝ)) :
    (Set.range (routeRestr (polyRouter dim nK d) hnK S)).ncard
      ≤ (∑ r ∈ Finset.range (finrank ℝ (polySpan dim d) + 1), S.card.choose r) ^ (nK * nK) :=
  symbolClass_growth_uniform (polyRouter dim nK d) hnK (polySpan dim d)
    (fun i j K => by
      simpa using polyScoreDiff_mem_polySpan dim d (polyParamScore K j) (polyParamScore K i)) S

end TLT.TemperedDesignLaw
