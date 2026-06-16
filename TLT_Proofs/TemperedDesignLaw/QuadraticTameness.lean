/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.ArrangementVC
import TLT_Proofs.TemperedDesignLaw.QuadraticExpressivity

/-!
# The tameness bridge for quadratic (self-attention / low-rank bilinear) scores

The companion to `QuadraticExpressivity.lean`. There the power-diagram (convexity) characterization
of the argmax cells *fails* for quadratic scores, while the finite region count *survives*. Here we
prove the complementary half: a quadratic-scored route class is still **learnable**: it has finite
VC capacity, via the *same* arrangement-VC Sauer-product machinery as the affine case, only with a
larger feature dimension (`≈ d²` instead of `d`).

The mechanism is the design-manual thesis made precise: the only nontrivial hypothesis of the landed
arrangement-VC bound `symbolClass_growth_prod` (`ArrangementVC.lean`) is `hlin`, that each per-pair
score *difference* lies in a finite-dimensional submodule `W` of `(X → ℝ)`. For quadratic scores
`scoreᵢ(x) = xᵀMᵢx + ⟨aᵢ,x⟩ + bᵢ` the difference `scoreⱼ − scoreᵢ` is a degree-≤2 polynomial, which
lies in the *finite-dimensional* span of the degree-≤2 monomials `{xᵢxⱼ} ∪ {xᵢ} ∪ {1}`. So we
instantiate `W := quadSpan d` and get the finite Sauer-product growth bound for free.

## Results

* `quadSpan d`: the span of the `d² + d + 1` degree-≤2 monomials on `Fin d → ℝ`; `FiniteDimensional`
  by construction (a span of a finite set), with `finrank ≤ d² + d + 1` (`finrank_quadSpan_le`).
* `quadScoreDiff_mem_quadSpan`: every quadratic-score difference `x ↦ s.eval x − t.eval x` lies in
  `quadSpan d`: the quadratic, written as the explicit linear combination of the monomials.
* `quadRouter`: a `FiniteScoreRouterCode (Fin d → ℝ) nK` whose scores are literally `QuadScore.eval`.
* `quadRouterScoreDiff_mem_quadSpan`: the router's per-pair score differences lie in `quadSpan d`.
* `quadraticRouter_growth_prod` (**the tameness bridge**): the Sauer-product capacity bound for the
  quadratic-scored route class, an instantiation of `symbolClass_growth_prod` at
  `W := quadSpan d`. Finite VC, same machinery, `finrank quadSpan ≈ d²`.

The conclusion stated plainly: the low-rank-bilinear (self-attention) constraint keeps the route
class learnable because polynomial score-differences are finite-dimensional. Only non-polynomial
(arbitrary measurable) scores escape to infinite VC / the wild non-Borel regime.
-/

open scoped BigOperators
open Module

noncomputable section

namespace TLT.TemperedDesignLaw

/-! ## 1. The quadratic feature span `quadSpan d` -/

/-- The index type of the degree-≤2 monomials on `Fin d → ℝ`: the `d²` quadratics `xᵢ·xⱼ`
(indexed by ordered pairs `Fin d × Fin d`), the `d` linears `xᵢ`, and the constant `1`. As a
`Fintype` it has cardinality `d² + d + 1`, which is the dimension budget of `quadSpan d`. -/
abbrev QuadMonoIdx (d : ℕ) := (Fin d × Fin d) ⊕ Fin d ⊕ Unit

/-- The degree-≤2 monomial functions on `Fin d → ℝ`, indexed by `QuadMonoIdx d`:
`xᵢ·xⱼ` for `inl (i,j)`, `xᵢ` for `inr (inl i)`, and the constant `1` for `inr (inr ())`. -/
def quadMono (d : ℕ) : QuadMonoIdx d → ((Fin d → ℝ) → ℝ) :=
  fun b => match b with
    | .inl (i, j) => fun x : Fin d → ℝ => x i * x j
    | .inr (.inl i) => fun x : Fin d → ℝ => x i
    | .inr (.inr _) => fun _ : Fin d → ℝ => (1 : ℝ)

/-- **The quadratic feature span.** The span of the `d² + d + 1` degree-≤2 monomials on `Fin d → ℝ`.
Every quadratic score difference lives here (`quadScoreDiff_mem_quadSpan`), so this is the
finite-dimensional `W` that the arrangement-VC Sauer product needs for quadratic / self-attention
scores. It is to the quadratic case what `coordSpan d` is to the affine case, only `≈ d²`-dimensional
instead of `d`-dimensional. -/
def quadSpan (d : ℕ) : Submodule ℝ ((Fin d → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range (quadMono d))

/-- **`quadSpan d` is finite-dimensional.** It is the span of a finite set (the `QuadMonoIdx d`-indexed
range, and `QuadMonoIdx d` is a `Fintype`). Identical pattern to `coordSpan_finiteDim`. -/
instance quadSpan_finiteDim (d : ℕ) : FiniteDimensional ℝ (quadSpan d) := by
  unfold quadSpan
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- **The dimension budget.** `finrank ℝ (quadSpan d) ≤ d² + d + 1`: the span of `d² + d + 1`
generators has rank at most `d² + d + 1`. This is the `≈ d²` capacity that makes the
quadratic bound nonvacuous (vs. `d` in the affine `coordSpan` case). -/
theorem finrank_quadSpan_le (d : ℕ) : finrank ℝ (quadSpan d) ≤ d * d + d + 1 := by
  have h : finrank ℝ (quadSpan d) ≤ Fintype.card (QuadMonoIdx d) := by
    unfold quadSpan
    exact finrank_range_le_card (quadMono d)
  refine le_trans h ?_
  simp only [QuadMonoIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_unit]
  omega

/-! ## 2. A quadratic score difference lies in `quadSpan` -/

/-- **Every quadratic-score difference lies in `quadSpan d`.** For two quadratic scores `s t`, the
difference `x ↦ s.eval x − t.eval x` is the degree-≤2 polynomial
`∑ᵢⱼ (s.Mᵢⱼ − t.Mᵢⱼ)·xᵢxⱼ + ∑ᵢ (s.aᵢ − t.aᵢ)·xᵢ + (s.b − t.b)·1`, a finite ℝ-linear combination of
the monomials `quadMono d`, hence in their span. This is the quadratic analogue of
`attnScoreDiff_mem_coordSpan`; the membership is real (the difference is the quadratic, the
constant block carried because `s.b ≠ t.b` is a summand of the difference). -/
theorem quadScoreDiff_mem_quadSpan (d : ℕ) (s t : QuadScore d) :
    (fun x => s.eval x - t.eval x) ∈ quadSpan d := by
  have heq : (fun x : Fin d → ℝ => s.eval x - t.eval x)
      = (∑ i, ∑ j, (s.M i j - t.M i j) • quadMono d (.inl (i, j)))
        + (∑ i, (s.a i - t.a i) • quadMono d (.inr (.inl i)))
        + (s.b - t.b) • quadMono d (.inr (.inr ())) := by
    funext x
    simp only [QuadScore.eval, quadMono, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, mul_one]
    have hM : (∑ i, ∑ j, s.M i j * x i * x j) - (∑ i, ∑ j, t.M i j * x i * x j)
        = ∑ i, ∑ j, (s.M i j - t.M i j) * (x i * x j) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have ha : (∑ i, s.a i * x i) - (∑ i, t.a i * x i)
        = ∑ i, (s.a i - t.a i) * x i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [show ((∑ i, ∑ j, s.M i j * x i * x j) + (∑ i, s.a i * x i) + s.b)
        - ((∑ i, ∑ j, t.M i j * x i * x j) + (∑ i, t.a i * x i) + t.b)
      = ((∑ i, ∑ j, s.M i j * x i * x j) - (∑ i, ∑ j, t.M i j * x i * x j))
        + ((∑ i, s.a i * x i) - (∑ i, t.a i * x i)) + (s.b - t.b) by ring]
    rw [hM, ha]
  rw [heq, quadSpan]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (Sum.inl (i, j))))))
  · exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (Sum.inr (Sum.inl i)))))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (Sum.inr (Sum.inr ()))))

/-! ## 3. The quadratic-scored route class -/

/-- The parameter space of the quadratic router: `nK` independent quadratic scores, carried as raw
data `(matrix parts, linear parts, constants)` so that the native `Pi`/product `MeasurableSpace` and
`StandardBorelSpace` instances apply (`QuadScore` is a bare structure with no such instances).
`quadParamScore` reconstructs the `i`-th `QuadScore` from this data. -/
abbrev QuadParam (d nK : ℕ) :=
  (Fin nK → Fin d → Fin d → ℝ) × (Fin nK → Fin d → ℝ) × (Fin nK → ℝ)

/-- `QuadParam d nK` is a standard Borel space. The full three-way product overflows the default
synthesis depth, so the two component instances are supplied as `letI` hints; the conclusion is then
`inferInstanceAs` the product (with the canonical product `MeasurableSpace`, which `inferInstance`
finds unaided). -/
instance quadParam_sb (d nK : ℕ) : StandardBorelSpace (QuadParam d nK) :=
  letI _h1 : StandardBorelSpace (Fin nK → Fin d → Fin d → ℝ) := inferInstance
  letI _h2 : StandardBorelSpace ((Fin nK → Fin d → ℝ) × (Fin nK → ℝ)) := inferInstance
  inferInstanceAs (StandardBorelSpace
    ((Fin nK → Fin d → Fin d → ℝ) × (Fin nK → Fin d → ℝ) × (Fin nK → ℝ)))

/-- Reconstruct the `i`-th quadratic score from the raw parameter data. -/
def quadParamScore {d nK : ℕ} (K : QuadParam d nK) (i : Fin nK) : QuadScore d :=
  ⟨K.1 i, K.2.1 i, K.2.2 i⟩

/-- **The quadratic-scored router** as a `FiniteScoreRouterCode (Fin d → ℝ) nK`. The input is a
coordinate vector `x : Fin d → ℝ`, the parameter is `nK` quadratic scores (raw data `QuadParam d nK`),
and the score for head `i` is literally `QuadScore.eval` of the `i`-th reconstructed quadratic at `x`:
`scoreᵢ(x) = xᵀMᵢx + ⟨aᵢ,x⟩ + bᵢ`. This is the self-attention / low-rank-bilinear score class. -/
def quadRouter (d nK : ℕ) : FiniteScoreRouterCode (Fin d → ℝ) nK where
  Ρ := QuadParam d nK
  instMeasΡ := inferInstance
  instStdΡ := quadParam_sb d nK
  score := fun K x i => (quadParamScore K i).eval x
  score_meas := fun i => by
    simp only [quadParamScore, QuadScore.eval]
    -- measurable as a finite sum of products of coordinate projections (jointly in (K, x))
    refine Measurable.add (Measurable.add ?_ ?_) ?_
    · refine Finset.measurable_sum Finset.univ (fun a _ => ?_)
      refine Finset.measurable_sum Finset.univ (fun b _ => ?_)
      have hMab : Measurable (fun p : QuadParam d nK × (Fin d → ℝ) => p.1.1 i a b) :=
        ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp
          ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst))))
      have hxa : Measurable (fun p : QuadParam d nK × (Fin d → ℝ) => p.2 a) :=
        (measurable_pi_apply a).comp measurable_snd
      have hxb : Measurable (fun p : QuadParam d nK × (Fin d → ℝ) => p.2 b) :=
        (measurable_pi_apply b).comp measurable_snd
      exact (hMab.mul hxa).mul hxb
    · refine Finset.measurable_sum Finset.univ (fun a _ => ?_)
      have hai : Measurable (fun p : QuadParam d nK × (Fin d → ℝ) => p.1.2.1 i a) :=
        (measurable_pi_apply a).comp ((measurable_pi_apply i).comp
          (measurable_fst.comp (measurable_snd.comp measurable_fst)))
      have hxa : Measurable (fun p : QuadParam d nK × (Fin d → ℝ) => p.2 a) :=
        (measurable_pi_apply a).comp measurable_snd
      exact hai.mul hxa
    · exact (measurable_pi_apply i).comp (measurable_snd.comp (measurable_snd.comp measurable_fst))

/-- **The quadratic router's score is literally `QuadScore.eval`.** Definitional unfolding; recorded
so the membership and growth statements are visibly about the quadratic, not a relabeling. -/
@[simp] theorem quadRouter_score (d nK : ℕ) (K : QuadParam d nK) (x : Fin d → ℝ) (i : Fin nK) :
    (quadRouter d nK).score K x i = (quadParamScore K i).eval x := rfl

/-- **The quadratic router's per-pair score differences lie in `quadSpan d`.** Specializing
`quadScoreDiff_mem_quadSpan` to the two reconstructed quadratics at the heads of the ordered pair.
This is the `hlin` hypothesis of the arrangement-VC Sauer product, satisfied for quadratic scores. -/
theorem quadRouterScoreDiff_mem_quadSpan (d nK : ℕ) (p : Fin nK × Fin nK)
    (K : (quadRouter d nK).Ρ) :
    (fun x => (quadRouter d nK).score K x p.2 - (quadRouter d nK).score K x p.1) ∈ quadSpan d := by
  simpa using quadScoreDiff_mem_quadSpan d (quadParamScore K p.2) (quadParamScore K p.1)

/-! ## 4. The tameness bridge: finite Sauer-product capacity for the quadratic route class -/

/-- **THE TAMENESS BRIDGE (quadratic / self-attention scores).** The arrangement-VC Sauer-product
capacity bound for the quadratic-scored route class, an instantiation of the landed affine
machinery `symbolClass_growth_prod` at `W := quadSpan d`. On any finite sample `S`, the number of
routing-label patterns the quadratic router realises is at most the product over the `nK²` ordered
pairs of the Sauer–Shelah binomial sums at `finrank ℝ (quadSpan d)`, a polynomial in `|S|` of degree
the total quadratic-comparison VC dimension `nK² · finrank ℝ (quadSpan d) ≤ nK²·(d²+d+1)`.

The point: this is the *same* machinery as the affine case (`attnScoreDiff_mem_coordSpan` feeding the
same `symbolClass_growth_prod`), only the feature dimension is `≈ d²` (the quadratic monomials)
instead of `d` (the linear ones). The low-rank-bilinear (self-attention) constraint keeps the route
class **learnable** (finite VC) precisely because polynomial score-differences are
finite-dimensional. Only non-polynomial (arbitrary measurable) scores escape this (to infinite VC /
the wild non-Borel regime), because their differences span no finite-dimensional `W`. -/
theorem quadraticRouter_growth_prod (d nK : ℕ) (hnK : 0 < nK) (S : Finset (Fin d → ℝ)) :
    (Set.range (routeRestr (quadRouter d nK) hnK S)).ncard
      ≤ ∏ _p : Fin nK × Fin nK,
          ∑ r ∈ Finset.range (finrank ℝ (quadSpan d) + 1), S.card.choose r := by
  have h := symbolClass_growth_prod (quadRouter d nK) hnK
    (fun _ => quadSpan d) (fun _ => inferInstance)
    (fun p K => quadRouterScoreDiff_mem_quadSpan d nK p K) S
  simpa using h

/-- **The single-polynomial form of the tameness bridge.** Collapsing the per-pair product (every
factor shares the single feature space `quadSpan d`): the quadratic route class's combinatorial
capacity on `S` is `(∑_{r ≤ finrank quadSpan d} |S| choose r)^{nK²}`, finite for every sample. The
explicit `symbolClass_growth_uniform` instantiation. -/
theorem quadraticRouter_growth_uniform (d nK : ℕ) (hnK : 0 < nK) (S : Finset (Fin d → ℝ)) :
    (Set.range (routeRestr (quadRouter d nK) hnK S)).ncard
      ≤ (∑ r ∈ Finset.range (finrank ℝ (quadSpan d) + 1), S.card.choose r) ^ (nK * nK) :=
  symbolClass_growth_uniform (quadRouter d nK) hnK (quadSpan d)
    (fun i j K => by
      simpa using quadScoreDiff_mem_quadSpan d (quadParamScore K j) (quadParamScore K i)) S

end TLT.TemperedDesignLaw
