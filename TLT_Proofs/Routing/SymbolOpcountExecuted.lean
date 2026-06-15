/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Routing.SymbolOpcount
import NN.Floats.IEEEExec.BridgeFP32Total

/-!
# The executed (b = 0) face of the comparison-only route

`SymbolOpcount` proves the operation-type factorization at the real-arithmetic level: the
`noncomputable` `leastArgmax` of real scores equals the comparison-only program `argmaxFromCmp`
applied to the Boolean `≤`-comparison matrix (`leastArgmax_eq_argmaxFromCmp`).

The *executed* refinement is: the route computed **purely from IEEE binary32
`compare`** (no real arithmetic, no `exp`/`log`/`div`) equals the ideal real-valued `leastArgmax`
route with **zero** rounding (`b = 0`), under per-score finiteness.

The mechanism is that the fp32 `compare` atom is **real-exact**: on finite inputs
`compare x y = some .gt ↔ toReal y < toReal x` (`compare_eq_some_gt_iff_toReal_gt_of_isFinite`), so the
executed `≤`-bit `compare (s i) (s j) ≠ some .gt` agrees *bit-for-bit* with the real `toReal (s i) ≤
toReal (s j)`. Hence the executed comparison matrix equals the ℝ comparison matrix, and composing that
matrix-equality with `leastArgmax_eq_argmaxFromCmp` (the route is a function of the comparison matrix
alone) gives the executed route = the ideal ℝ-argmax route, exactly.

The theorem is **conditional on per-score finiteness** (`hfin : ∀ i, isFinite (s i) = true`), a regime
hypothesis matching the existing `*LiteralExecutedBinding` regime bundles.

## Main results
* `cmpExec_eq_real`: the executed `≤`-bit equals the ℝ `≤`-bit (the only step touching the fp32 atom).
* `executed_route_eq_leastArgmax`: `argmaxFromCmp` of the fp32-`compare` matrix = `leastArgmax` of the
  real scores.
-/

namespace TLT.Routing.Executed

open TorchLean.Floats.IEEE754 TorchLean.Floats.IEEE754.IEEE32Exec

variable {k : ℕ}

/-- **The executed `≤`-bit.** The comparison-only route reads, for each pair `(i, j)`, the single
binary32 bit "`s i` does not strictly exceed `s j`", i.e. `compare (s i) (s j) ≠ some .gt`. This is
computed from the hardware `compare : IEEE32Exec → IEEE32Exec → Option Ordering` alone, with no real
arithmetic and no transcendental operations. -/
def cmpExec (s : Fin k → IEEE32Exec) (i j : Fin k) : Bool :=
  decide (compare (s i) (s j) ≠ some .gt)

/-- **The matrix-equality atom: the executed `≤`-bit equals the real `≤`-bit.** Under per-score
finiteness, the fp32 comparison `compare (s i) (s j) ≠ some .gt` agrees with `toReal (s i) ≤
toReal (s j)`, with no rounding.

This is the single step that touches the float-execution stratum. It consumes the real-exactness atom
`compare_eq_some_gt_iff_toReal_gt_of_isFinite`, the biconditional
`compare … = some .gt ↔ toReal (s j) < toReal (s i)`. Because that atom is an *iff*, the `none` case
cannot spuriously break the bit: if `compare … = none` then `none ≠ some .gt` holds, but the iff's
`.mpr` shows `toReal (s j) < toReal (s i)` would force `compare … = some .gt ≠ none`, so the
contrapositive `compare … ≠ some .gt → ¬ (toReal (s j) < toReal (s i))` is valid with no separate
totality lemma. Concretely `compare … ≠ some .gt ↔ ¬ (toReal (s j) < toReal (s i)) ↔ toReal (s i) ≤
toReal (s j)` by `not_lt`. (Totality is available in-layer: by real trichotomy each of `<`/`=`/`>`
is matched by `compare … = some .lt`/`.eq`/`.gt` via the three iff-atoms, giving `compare … ≠ none`;
but the iff already discharges the `none` case, so the proof does not need it.) -/
theorem cmpExec_eq_real (s : Fin k → IEEE32Exec) (hfin : ∀ i, isFinite (s i) = true) (i j : Fin k) :
    cmpExec s i j = decide (toReal (s i) ≤ toReal (s j)) := by
  unfold cmpExec
  -- the real-exact `gt` atom on the finite pair `(s i, s j)`: a biconditional
  have hgt : compare (s i) (s j) = some .gt ↔ toReal (s j) < toReal (s i) :=
    compare_eq_some_gt_iff_toReal_gt_of_isFinite (s i) (s j) (hfin i) (hfin j)
  -- `≠ some .gt ↔ ¬ (toReal (s j) < toReal (s i)) ↔ toReal (s i) ≤ toReal (s j)`
  apply decide_eq_decide.mpr
  constructor
  · intro hng
    -- contrapositive of `hgt.mpr`: this discharges the `none` case without a totality lemma
    have : ¬ (toReal (s j) < toReal (s i)) := fun h => hng (hgt.mpr h)
    exact not_lt.mp this
  · intro hle hgte
    exact absurd (hgt.mp hgte) (not_lt.mpr hle)

/-- **Executed exactness (`b = 0`).** The symbol route computed *purely* from IEEE binary32
comparisons (`argmaxFromCmp` over the fp32-`compare` `≤`-matrix `compare (s i) (s j) ≠ some .gt`)
equals the ideal real-valued `leastArgmax` route on the scores' real values, with **zero** rounding,
under per-score finiteness.

Proof: rewrite the executed matrix to the ℝ matrix `fun i j => decide (toReal (s i) ≤ toReal (s j))`
pointwise via `cmpExec_eq_real` (the only fp32 step), then close by the real-level factorization
`(leastArgmax_eq_argmaxFromCmp (fun i => toReal (s i)) hk).symm`. The route from fp32 comparisons
alone coincides with the exact ℝ-argmax route, the executed (`b = 0`) face of
`leastArgmax_eq_argmaxFromCmp`. -/
theorem executed_route_eq_leastArgmax (s : Fin k → IEEE32Exec) (hk : 0 < k)
    (hfin : ∀ i, isFinite (s i) = true) :
    argmaxFromCmp (fun i j => decide (compare (s i) (s j) ≠ some .gt)) hk
      = leastArgmax (fun i => toReal (s i)) hk := by
  have hmatrix : (fun i j => decide (compare (s i) (s j) ≠ some .gt))
      = (fun i j => decide (toReal (s i) ≤ toReal (s j))) := by
    funext i j
    exact cmpExec_eq_real s hfin i j
  rw [hmatrix]
  exact (leastArgmax_eq_argmaxFromCmp (fun i => toReal (s i)) hk).symm

end TLT.Routing.Executed
