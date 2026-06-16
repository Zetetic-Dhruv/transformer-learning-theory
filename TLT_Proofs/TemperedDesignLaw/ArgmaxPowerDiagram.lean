/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Analysis.Convex.Basic
import TLT_Proofs.TemperedDesignLaw.MuxHierarchy

/-!
# The depth-1 neurosymbolic argmax atom: argmax cells are power-diagram cells

A transformer router reads a discrete symbol from continuous scores via `leastArgmax` (the least
index achieving the max). When the `k` scores are **affine** in the input `x : Fin d → ℝ`, the
symbol map partitions input space into **power-diagram (weighted Voronoi) cells**: each symbol cell
is an intersection of affine half-spaces, hence a convex polyhedron. This is the depth-1
expressivity characterization, the positive direction of the neurosymbolic argmax atom (non-convex
partitions such as XOR are NOT single-argmax realizable: the depth-1 lower bound, proved
separately in `MuxHierarchy.xorRoute_not_mem_grade_zero`).

## Main results

* `argmaxCell_eq_halfspaces` : the symbol cell `{x | leastArgmax (scores · eval x) = i}` equals the
  intersection of the affine half-spaces
  `(∀ j, (scores j).eval x ≤ (scores i).eval x) ∧ (∀ j, j < i → (scores j).eval x < (scores i).eval x)`.
  This is the **exact** power-diagram-cell characterization (a genuine set equality on the full
  `Fin d → ℝ`, for arbitrary `d`, `k`).
* `argmaxCell_eq_iInter` : the same cell as a finite `⋂` of affine `≤`/`<` half-spaces (one per `j`,
  strict below `i`).
* `argmaxCell_convex` : **the core theorem**: every symbol cell is `Convex ℝ`. Proved by rewriting
  the cell as the `⋂` of convex affine half-spaces (`affineLe_convex`, `affineLt_convex`) and closing
  with `convex_iInter` / `Convex.inter`.

These are the bare-route (`scores : Fin k → AffineFunctional d`) statements of the power-diagram
characterization; the depth-`0` cascade-route corollary is `MuxHierarchy.muxCascadeGrade_zero_cells_convex`.
-/

open Set
open TLT.TemperedDesignLaw.MuxHierarchy
  (AffineFunctional affineLe_convex affineLt_convex)
-- `isLeastArgmax`, `leastArgmax`, `leastArgmax_spec`, `isLeastArgmax_unique` live in the root
-- namespace (`TLT_Proofs/Routing/MeasurableScoreRouting.lean` has no `namespace`).

noncomputable section

namespace TLT.TemperedDesignLaw

/-! ## The half-space characterization of an affine argmax cell -/

/-- **The power-diagram-cell characterization (the "exactly" content).** For affine scores, the
symbol cell `{x | leastArgmax (fun j => (scores j).eval x) hk = i}` equals the set cut out by the
half-space inequalities
`(∀ j, (scores j).eval x ≤ (scores i).eval x) ∧ (∀ j, j < i → (scores j).eval x < (scores i).eval x)`.

Each conjunct is an affine half-space in `x` (a `≤` or strict `<` between two affine functionals),
so the cell is their finite intersection, a power-diagram (weighted Voronoi) cell. This is a
genuine set equality on all of `Fin d → ℝ`, for arbitrary `d` and `k`. -/
theorem argmaxCell_eq_halfspaces {d k : ℕ} (scores : Fin k → AffineFunctional d) (hk : 0 < k)
    (i : Fin k) :
    {x : Fin d → ℝ | leastArgmax (fun j => (scores j).eval x) hk = i}
      = {x : Fin d → ℝ |
          (∀ j, (scores j).eval x ≤ (scores i).eval x) ∧
          (∀ j, j < i → (scores j).eval x < (scores i).eval x)} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · -- the argmax equals `i`, so `i` satisfies the `isLeastArgmax` predicate
    intro h
    have hspec : isLeastArgmax (fun j => (scores j).eval x) i := by
      rw [← h]; exact leastArgmax_spec _ hk
    exact ⟨fun j => hspec.1 j, fun j hji => hspec.2 j hji⟩
  · -- the inequalities make `i` the (unique) least argmax
    rintro ⟨hle, hlt⟩
    have hspec : isLeastArgmax (fun j => (scores j).eval x) i :=
      ⟨fun j => hle j, fun j hji => hlt j hji⟩
    exact isLeastArgmax_unique _ _ _ (leastArgmax_spec _ hk) hspec

/-- The same symbol cell written as a finite intersection of affine half-spaces: the `≤`-cells for
every `j`, intersected with the strict `<`-cells for every `j < i`. This is the explicit
power-diagram presentation used by the convexity proof. -/
theorem argmaxCell_eq_iInter {d k : ℕ} (scores : Fin k → AffineFunctional d) (hk : 0 < k)
    (i : Fin k) :
    {x : Fin d → ℝ | leastArgmax (fun j => (scores j).eval x) hk = i}
      = (⋂ j : Fin k, {x : Fin d → ℝ | (scores j).eval x ≤ (scores i).eval x})
        ∩ (⋂ j : Fin k, ⋂ _ : j < i,
            {x : Fin d → ℝ | (scores j).eval x < (scores i).eval x}) := by
  rw [argmaxCell_eq_halfspaces scores hk i]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]

/-! ## The core theorem: argmax cells are convex (power-diagram cells) -/

/-- **CORE THEOREM: argmax cells are convex (power diagram).** When the `k` scores are affine in
`x`, each symbol cell `{x | leastArgmax (fun j => (scores j).eval x) hk = i}` is `Convex ℝ`: it is the
intersection of the affine half-spaces `{x | (scores j).eval x ≤ (scores i).eval x}` (all `j`) and the
strict half-spaces `{x | (scores j).eval x < (scores i).eval x}` (for `j < i`), each convex by
`affineLe_convex` / `affineLt_convex`; a finite intersection of convex sets is convex
(`convex_iInter` / `Convex.inter`). This is the positive direction of the depth-1 neurosymbolic
argmax atom: single-argmax routes realize exactly the power-diagram (convex-cell) partitions. -/
theorem argmaxCell_convex {d k : ℕ} (scores : Fin k → AffineFunctional d) (hk : 0 < k) (i : Fin k) :
    Convex ℝ {x : Fin d → ℝ | leastArgmax (fun j => (scores j).eval x) hk = i} := by
  rw [argmaxCell_eq_iInter scores hk i]
  refine Convex.inter ?_ ?_
  · exact convex_iInter (fun j => affineLe_convex (scores j) (scores i))
  · exact convex_iInter (fun j => convex_iInter (fun _ => affineLt_convex (scores j) (scores i)))

end TLT.TemperedDesignLaw
