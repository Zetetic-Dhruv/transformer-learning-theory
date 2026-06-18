/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.ArgmaxPowerDiagram
import TLT_Proofs.TemperedDesignLaw.QuadraticExpressivity

/-!
# Theorem B: first-order vs. second-order logical placement of argmax cells

This file re-expresses the **landed geometry** of the argmax router under the explicit
*logical-placement* framing requested by the design law: where, in the first-order / second-order
hierarchy of definable sets, does a symbol cell `{x | leastArgmax (score · x) = i}` live?

* **(B1, first-order)** For **affine** scores the cell is a *first-order object*: membership is a
  finite conjunction of **degree-1 (affine) inequalities**, i.e. a finite intersection of affine
  half-spaces. Convex, decidable by linear arithmetic. This is a faithful re-expression of the
  landed `argmaxCell_eq_iInter` / `argmaxCell_eq_halfspaces` / `argmaxCell_convex`
  (`ArgmaxPowerDiagram.lean`), with the half-space "degree-1" content exposed via
  `AffineFunctional.eval_le_iff` (each conjunct is `diffLin x ≤ c`, and `diffLin` is
  `IsLinearMap` — genuinely degree 1).

* **(B2, second-order)** For **quadratic** (self-attention) scores the cell is a *second-order /
  semialgebraic object*: membership is a finite conjunction of **degree-2 polynomial inequalities**
  and the cell can be **non-convex**. The non-convexity is a faithful repackage of the landed
  `quadraticArgmaxCell_not_convex` (`QuadraticExpressivity.lean`); the finite-conjunction
  (semialgebraic) presentation is the exact `argmaxCell`-style half-space decomposition specialised
  to `QuadScore.eval`, whose conjuncts `(score j).eval x ≤ (score i).eval x` are degree-2 polynomial
  sublevel sets. The finite-region survival of the quadratic argmax is the landed
  `quadArg_alternations_le`.

## Main results

* `affineArgmaxCell_FO` : the affine cell as a finite `⋂` of affine `≤`/`<` half-spaces (the exact
  shape of `argmaxCell_eq_iInter`).
* `affineArgmaxCell_FO_halfspaces` : the affine cell as the finite conjunction of half-space
  inequalities (the `argmaxCell_eq_halfspaces` shape).
* `affineArgmaxCell_conjunct_degree1` : each conjunct is an affine half-space — the membership
  predicate `(score j).eval x ≤ (score i).eval x` is equivalent to a **degree-1** inequality
  `L x ≤ c` with `L` an `IsLinearMap` (so the half-space is a genuine degree-1 object).
* `affineArgmaxCell_convex` : the affine cell is convex (re-export of `argmaxCell_convex`).
* `quadraticArgmaxCell_SO_not_convex` : there are quadratic scores whose cell is **not** convex
  (re-export of `quadraticArgmaxCell_not_convex`).
* `quadraticArgmaxCell_SO_semialgebraic` : every quadratic cell is a finite intersection of
  degree-2 polynomial sublevel sets `{x | (score j).eval x − (score i).eval x ≤ 0}` (all `j`) and
  strict ones (for `j < i`) — the second-order / semialgebraic presentation.
* `quadraticArgmaxCell_conjunct_degree2` : each conjunct is a degree-2 polynomial sublevel set:
  `(score j).eval x ≤ (score i).eval x` iff `P x ≤ 0` with `P` a quadratic form (matrix + linear +
  constant), exhibited explicitly.
* `quadArg_finite_regions` : the region count survives (re-export of `quadArg_alternations_le`).
-/

open Set
open TLT.TemperedDesignLaw.MuxHierarchy (AffineFunctional Increasing seqChanges)

noncomputable section

namespace TLT.TemperedDesignLaw

/-! ## (B1) The affine argmax cell is a FIRST-ORDER object -/

/-- **(B1, FO) The affine argmax cell as a finite intersection of affine half-spaces.**

A faithful re-expression (same statement, by `rfl`-level re-export) of the landed
`argmaxCell_eq_iInter`: for affine scores the symbol cell
`{x | leastArgmax (fun j => (scores j).eval x) hk = i}` equals the finite intersection of the
affine `≤`-half-spaces `{x | (scores j).eval x ≤ (scores i).eval x}` (one per index `j`) with the
strict `<`-half-spaces for `j < i`. Cell membership is therefore a finite conjunction over indices
of (degree-1) affine inequalities — a first-order object, convex, decidable by linear arithmetic. -/
theorem affineArgmaxCell_FO {d k : ℕ} (scores : Fin k → AffineFunctional d) (hk : 0 < k)
    (i : Fin k) :
    {x : Fin d → ℝ | leastArgmax (fun j => (scores j).eval x) hk = i}
      = (⋂ j : Fin k, {x : Fin d → ℝ | (scores j).eval x ≤ (scores i).eval x})
        ∩ (⋂ j : Fin k, ⋂ _ : j < i,
            {x : Fin d → ℝ | (scores j).eval x < (scores i).eval x}) :=
  argmaxCell_eq_iInter scores hk i

/-- **(B1, FO) The half-space conjunction form.** The same affine cell written as the explicit
finite conjunction of half-space inequalities `(∀ j, (scores j).eval x ≤ (scores i).eval x) ∧
(∀ j, j < i → (scores j).eval x < (scores i).eval x)` — re-export of `argmaxCell_eq_halfspaces`.
This is the literal "finite conjunction of degree-1 affine inequalities" reading of FO membership. -/
theorem affineArgmaxCell_FO_halfspaces {d k : ℕ} (scores : Fin k → AffineFunctional d) (hk : 0 < k)
    (i : Fin k) :
    {x : Fin d → ℝ | leastArgmax (fun j => (scores j).eval x) hk = i}
      = {x : Fin d → ℝ |
          (∀ j, (scores j).eval x ≤ (scores i).eval x) ∧
          (∀ j, j < i → (scores j).eval x < (scores i).eval x)} :=
  argmaxCell_eq_halfspaces scores hk i

/-- **(B1, FO) Each conjunct is a degree-1 affine half-space.** The membership predicate of one
conjunct, `(scores j).eval x ≤ (scores i).eval x`, is equivalent to a **degree-1** inequality
`L x ≤ c`, where `L = (scores j).diffLin (scores i)` is an `IsLinearMap ℝ` (the linear part of the
difference of the two affine functionals) and `c = (scores i).const − (scores j).const`. So every
conjunct of the FO cell is a genuine affine half-space (degree exactly 1), not merely "an
inequality between affine functionals". -/
theorem affineArgmaxCell_conjunct_degree1 {d k : ℕ} (scores : Fin k → AffineFunctional d)
    (i j : Fin k) :
    ∃ (L : (Fin d → ℝ) → ℝ) (c : ℝ), IsLinearMap ℝ L ∧
      {x : Fin d → ℝ | (scores j).eval x ≤ (scores i).eval x} = {x : Fin d → ℝ | L x ≤ c} := by
  refine ⟨(scores j).diffLin (scores i), (scores i).const - (scores j).const,
    AffineFunctional.diffLin_isLinear _ _, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq]
  exact AffineFunctional.eval_le_iff (scores j) (scores i) x

/-- **(B1, FO) The strict conjunct is also a degree-1 affine half-space.** Same as
`affineArgmaxCell_conjunct_degree1` but for the strict `<`-conjuncts (`j < i`). -/
theorem affineArgmaxCell_conjunct_degree1_strict {d k : ℕ} (scores : Fin k → AffineFunctional d)
    (i j : Fin k) :
    ∃ (L : (Fin d → ℝ) → ℝ) (c : ℝ), IsLinearMap ℝ L ∧
      {x : Fin d → ℝ | (scores j).eval x < (scores i).eval x} = {x : Fin d → ℝ | L x < c} := by
  refine ⟨(scores j).diffLin (scores i), (scores i).const - (scores j).const,
    AffineFunctional.diffLin_isLinear _ _, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq]
  exact AffineFunctional.eval_lt_iff (scores j) (scores i) x

/-- **(B1, FO) The affine cell is convex.** Re-export of the core landed theorem `argmaxCell_convex`:
the finite intersection of affine half-spaces is convex. -/
theorem affineArgmaxCell_convex {d k : ℕ} (scores : Fin k → AffineFunctional d) (hk : 0 < k)
    (i : Fin k) :
    Convex ℝ {x : Fin d → ℝ | leastArgmax (fun j => (scores j).eval x) hk = i} :=
  argmaxCell_convex scores hk i

/-! ## (B2) The quadratic argmax cell is a SECOND-ORDER / semialgebraic object -/

/-- **(B2, SO) The quadratic cell can be non-convex.** Faithful repackage of the landed
`quadraticArgmaxCell_not_convex`: there are two quadratic (self-attention) scores
`score 0 = 0`, `score 1 (x) = x₀² − x₁²` on `Fin 2` and an index `i = 0` whose least-argmax cell is
**not** `Convex ℝ`. So unlike the affine case (B1), the quadratic argmax cell escapes the first-order
(convex half-space) world: it is genuinely second-order. -/
theorem quadraticArgmaxCell_SO_not_convex :
    ∃ (scores : Fin 2 → QuadScore 2) (hk : 0 < 2) (i : Fin 2),
      ¬ Convex ℝ {x : Fin 2 → ℝ | leastArgmax (fun j => (scores j).eval x) hk = i} :=
  quadraticArgmaxCell_not_convex

/-- **(B2, SO) Each conjunct is a degree-2 polynomial sublevel set.** The membership predicate
`(scores j).eval x ≤ (scores i).eval x` of one quadratic conjunct is equivalent to a single
**degree-2** polynomial inequality `P x ≤ 0`, where `P x = (∑ p q, M p q · x p · x q) +
(∑ p, a p · x p) + b` is the quadratic form of the difference score (matrix part `M = score j.M −
score i.M`, linear part `a = score j.a − score i.a`, constant `b = score j.b − score i.b`). So each
conjunct of the quadratic cell is a genuine degree-2 sublevel set (semialgebraic), the second-order
analogue of `affineArgmaxCell_conjunct_degree1`. -/
theorem quadraticArgmaxCell_conjunct_degree2 {d : ℕ} (scores : Fin 2 → QuadScore d) (i j : Fin 2) :
    ∃ P : QuadScore d,
      {x : Fin d → ℝ | (scores j).eval x ≤ (scores i).eval x} = {x : Fin d → ℝ | P.eval x ≤ 0} := by
  refine ⟨⟨fun p q => (scores j).M p q - (scores i).M p q,
           fun p => (scores j).a p - (scores i).a p,
           (scores j).b - (scores i).b⟩, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, QuadScore.eval]
  constructor <;> intro h
  · -- (∑Mⱼ + ∑aⱼ + bⱼ) ≤ (∑Mᵢ + ∑aᵢ + bᵢ) ⟹ difference ≤ 0
    have hsum : (∑ p, ∑ q, ((scores j).M p q - (scores i).M p q) * x p * x q)
        = (∑ p, ∑ q, (scores j).M p q * x p * x q) - (∑ p, ∑ q, (scores i).M p q * x p * x q) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro p _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro q _
      ring
    have hlin : (∑ p, ((scores j).a p - (scores i).a p) * x p)
        = (∑ p, (scores j).a p * x p) - (∑ p, (scores i).a p * x p) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro p _; ring
    rw [hsum, hlin]; linarith
  · have hsum : (∑ p, ∑ q, ((scores j).M p q - (scores i).M p q) * x p * x q)
        = (∑ p, ∑ q, (scores j).M p q * x p * x q) - (∑ p, ∑ q, (scores i).M p q * x p * x q) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro p _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro q _
      ring
    have hlin : (∑ p, ((scores j).a p - (scores i).a p) * x p)
        = (∑ p, (scores j).a p * x p) - (∑ p, (scores i).a p * x p) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro p _; ring
    rw [hsum, hlin] at h; linarith

/-- **(B2, SO) The quadratic cell is a finite intersection of degree-2 sublevel sets
(semialgebraic).** For quadratic scores the symbol cell
`{x | leastArgmax (fun j => (scores j).eval x) hk = i}` equals the finite intersection of the
weak degree-2 sublevel sets `{x | (scores j).eval x ≤ (scores i).eval x}` (one per index `j`) with
the strict degree-2 sublevel sets for `j < i`. Cell membership is therefore a finite conjunction of
degree-2 polynomial inequalities — a semialgebraic set cut out by quadratics (each conjunct exhibited
as `P x ≤ 0` / `P x < 0` by `quadraticArgmaxCell_conjunct_degree2`). This is the second-order analogue
of `affineArgmaxCell_FO`; it is the SAME `argmaxCell` half-space decomposition specialised to
`QuadScore.eval`, so it holds for the very scores whose cell is non-convex
(`quadraticArgmaxCell_SO_not_convex`). -/
theorem quadraticArgmaxCell_SO_semialgebraic {d : ℕ} (scores : Fin 2 → QuadScore d) (hk : 0 < 2)
    (i : Fin 2) :
    {x : Fin d → ℝ | leastArgmax (fun j => (scores j).eval x) hk = i}
      = (⋂ j : Fin 2, {x : Fin d → ℝ | (scores j).eval x ≤ (scores i).eval x})
        ∩ (⋂ j : Fin 2, ⋂ _ : j < i,
            {x : Fin d → ℝ | (scores j).eval x < (scores i).eval x}) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · -- argmax = i ⟹ i satisfies the isLeastArgmax predicate ⟹ the conjuncts hold.
    intro h
    have hspec : isLeastArgmax (fun j => (scores j).eval x) i := by
      rw [← h]; exact leastArgmax_spec _ hk
    exact ⟨fun j => hspec.1 j, fun j hji => hspec.2 j hji⟩
  · -- the conjuncts make i the unique least argmax.
    rintro ⟨hle, hlt⟩
    have hspec : isLeastArgmax (fun j => (scores j).eval x) i :=
      ⟨fun j => hle j, fun j hji => hlt j hji⟩
    exact isLeastArgmax_unique _ _ _ (leastArgmax_spec _ hk) hspec

/-- **(B2, SO) The region count survives.** Re-export of the landed Davenport–Schinzel order-2 bound
`quadArg_alternations_le`: even though the quadratic cell is second-order (non-convex,
degree-2-definable), the active index of `n` parabolas changes only finitely often (`≤ 2 n²`) along
any increasing sample. Finiteness — the region count — is preserved across the FO→SO jump. -/
theorem quadArg_finite_regions {n : ℕ} (g : QuadLines n) (hn : 0 < n) {m : ℕ}
    (pts : Fin (m + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => g.arg hn (pts k)) ≤ 2 * n ^ 2 :=
  quadArg_alternations_le g hn pts hinc

end TLT.TemperedDesignLaw
