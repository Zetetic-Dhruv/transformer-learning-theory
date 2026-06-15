/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Routing.MeasurableScoreRouting

/-!
# The symbol route as a comparison-only operation (the operation-type reading)

The hard routing decision `leastArgmax` is `noncomputable`: it is `Finset.min'` of the maximizer
filter over the real scores, and `≤` on `ℝ` is not computably decidable. Yet the route depends only on
the pairwise comparison *pattern* (`leastArgmax_eq_of_le_iff`), and a comparison `vᵢ ≤ vⱼ` is, at the
operation level, a single decidable bit — no `exp`/`log`/`div`, zero transcendental operations. This
file gives the route its **operation-type** reading: the same least-maximizer selection, run on a
`Bool` comparison matrix, is an explicit **computable** algorithm `argmaxFromCmp`.

`argmaxFromCmp` is a plain `def` (it `#eval`s), in deliberate contrast to the `noncomputable`
`leastArgmax`; the computability gap is exactly the `ℝ`-`≤` versus `Bool`-comparison gap. On its own
the definition is only the carrier: the content is the (non-defeq) factorization
`leastArgmax v hk = argmaxFromCmp (fun i j => decide (v i ≤ v j)) hk` proved in later results, which
exhibits the noncomputable real-argmax as this transcendental-free program.

## Main definitions
* `argmaxFromCmp cmp hk` — the least index dominating every index under the Boolean comparison matrix
  `cmp` (the least maximizer), with `0` as the default when `cmp` admits no global maximizer.
-/

variable {k : ℕ}

/-- **The comparison-only argmax.** Given the Boolean pairwise-comparison matrix `cmp` (read as
`cmp j i = true` ⟺ "`j` does not beat `i`", i.e. the `≤`-comparison `score j ≤ score i`), select the
least index `i` that dominates every `j` (`∀ j, cmp j i = true`), defaulting to `0` when no such index
exists. The dominating-index predicate is decidable over the finite index type, so this is a genuine
**`def`** — a transcendental-free, comparison-only program — unlike the `noncomputable` `leastArgmax`
it will be shown to factor. -/
def argmaxFromCmp (cmp : Fin k → Fin k → Bool) (hk : 0 < k) : Fin k :=
  if h : ∃ i, ∀ j, cmp j i = true then Fin.find (fun i => ∀ j, cmp j i = true) h
  else ⟨0, hk⟩

/-- **`argmaxFromCmp` selects a maximizer.** Whenever the comparison matrix admits a global maximizer —
some index dominated-by-everything (`∀ j, cmp j i = true`) — the selected index dominates every index.
This is the `Fin.find` counterpart of `leastArgmax_is_maximizer` (which is about `Finset.min'`). -/
theorem argmaxFromCmp_is_maximizer (cmp : Fin k → Fin k → Bool) (hk : 0 < k)
    (h : ∃ i, ∀ j, cmp j i = true) : ∀ j, cmp j (argmaxFromCmp cmp hk) = true := by
  simp only [argmaxFromCmp, dif_pos h]
  exact Fin.find_spec h

/-- **`argmaxFromCmp` selects the LEAST maximizer.** Any index strictly below the selected one fails to
dominate every index — so the selection is the least maximizer. The `Fin.find` counterpart of
`leastArgmax_is_least`, routed through `Fin.find_min` rather than `Finset.min'`-minimality. -/
theorem argmaxFromCmp_is_least (cmp : Fin k → Fin k → Bool) (hk : 0 < k)
    (h : ∃ i, ∀ j, cmp j i = true) {j : Fin k} (hj : j < argmaxFromCmp cmp hk) :
    ¬ (∀ l, cmp l j = true) := by
  simp only [argmaxFromCmp, dif_pos h] at hj
  exact Fin.find_min h hj

/-- **The factorization — the real-score route *is* the comparison-only program.** The `noncomputable`
least-argmax of real scores equals `argmaxFromCmp` applied to their Boolean `≤`-comparison matrix. This
is the operation-type content of the symbol channel: the routing decision — defined over `ℝ`, where `≤`
is not computably decidable — coincides with an explicit transcendental-free **decidable** algorithm.

The proof is a genuine uniqueness argument (`isLeastArgmax_unique` against `leastArgmax_spec`), **not**
definitional: `leastArgmax` is `Finset.min'` of a filter over the reals while `argmaxFromCmp` is
`Fin.find` over `Bool`, so the two are not defeq and the equation does not (and cannot) close by `rfl`. -/
theorem leastArgmax_eq_argmaxFromCmp (v : Fin k → ℝ) (hk : 0 < k) :
    leastArgmax v hk = argmaxFromCmp (fun i j => decide (v i ≤ v j)) hk := by
  have hex : ∃ i, ∀ j, (fun i j => decide (v i ≤ v j)) j i = true :=
    ⟨leastArgmax v hk, fun j => by simpa using leastArgmax_is_maximizer v hk j⟩
  apply isLeastArgmax_unique v _ _ (leastArgmax_spec v hk)
  refine ⟨fun j => ?_, fun j hj => ?_⟩
  · -- the selected index is a maximizer of `v`
    simpa using argmaxFromCmp_is_maximizer (fun i j => decide (v i ≤ v j)) hk hex j
  · -- it is the least such: any earlier index is strictly dominated
    have hnot := argmaxFromCmp_is_least (fun i j => decide (v i ≤ v j)) hk hex hj
    simp only [decide_eq_true_eq] at hnot
    push_neg at hnot
    obtain ⟨l, hl⟩ := hnot
    have hmax := argmaxFromCmp_is_maximizer (fun i j => decide (v i ≤ v j)) hk hex l
    simp only [decide_eq_true_eq] at hmax
    exact lt_of_lt_of_le hl hmax

/-- **Router-lift (corollary).** The router's hard routing decision is the comparison-only program
applied to the score-comparison matrix: each output label is `argmaxFromCmp` of the `k²` Boolean
comparisons `score i ≤ score j`. So the symbol/hard route uses score comparisons only — zero
transcendental operations — at the design-law surface. This is just the presentation of
`leastArgmax_eq_argmaxFromCmp` at `v := A.score ρ x` (`A.route` is definitionally `leastArgmax` of the
scores); the content is that v-level factorization, not a separate result. -/
theorem FiniteScoreRouterCode.route_eq_argmaxFromCmp {X : Type*} [MeasurableSpace X] {n : ℕ}
    (A : FiniteScoreRouterCode X n) (hn : 0 < n) (ρ : A.Ρ) (x : X) :
    A.route hn ρ x = argmaxFromCmp (fun i j => decide (A.score ρ x i ≤ A.score ρ x j)) hn :=
  leastArgmax_eq_argmaxFromCmp (A.score ρ x) hn

/-- **Operation-type predicate: a route map uses comparisons only.** A selection map
`f : (Fin k → ℝ) → Fin k` is *comparison-only* when it factors through the Boolean pairwise
`≤`-comparison matrix of its input — there is a `Bool`-matrix decoder `g` with
`f v = g (fun i j => decide (v i ≤ v j))` for every `v`. Such an `f` reads only the finitely many
comparison bits, never the real magnitudes, so it is computed with **zero transcendental operations**
(no `exp`/`log`/`div`): the operation-type reading of the routing decision.

This is a genuine restriction, not a vacuous tag: the comparison matrix takes finitely many values
while `v` ranges over an uncountable space, so any magnitude-dependent map (a threshold `if 1 < v 0 …`)
fails it (`comparisonOnly_not_vacuous`). The soft/mixture route sits on the failing side — its weights
read exact magnitudes and are never one-hot (`softWeights_lt_one`, `ExactnessImpossibility`). -/
def ComparisonOnly (f : (Fin k → ℝ) → Fin k) : Prop :=
  ∃ g : (Fin k → Fin k → Bool) → Fin k, ∀ v, f v = g (fun i j => decide (v i ≤ v j))

/-- **The hard route is comparison-only (the operation-type theorem).** The least-argmax routing map
factors through the Boolean comparison matrix, witnessed *constructively* by `argmaxFromCmp` (the
decoder) via `leastArgmax_eq_argmaxFromCmp`. This turns "the route is transcendental-free" from a
description into a theorem: the symbol channel's decision is a function of score comparisons alone. -/
theorem leastArgmax_comparisonOnly (hk : 0 < k) :
    ComparisonOnly (fun v : Fin k → ℝ => leastArgmax v hk) :=
  ⟨fun cmp => argmaxFromCmp cmp hk, fun v => leastArgmax_eq_argmaxFromCmp v hk⟩

/-- **`ComparisonOnly` is a genuine restriction, not a vacuous tag.** A magnitude threshold
`v ↦ if v 0 = 0 then 0 else 1` is *not* comparison-only: the all-zero and all-one inputs share the same
(all-`true`) comparison matrix, yet the map sends them to different indices — so no `Bool`-matrix
decoder can reproduce it. This fences the predicate to the order-determined maps, exactly where the
hard route lives and the magnitude-reading soft route does not. -/
theorem comparisonOnly_not_vacuous :
    ¬ ComparisonOnly (fun v : Fin 2 → ℝ => if v 0 = 0 then (0 : Fin 2) else 1) := by
  rintro ⟨g, hg⟩
  have h0 := hg (fun _ => (0 : ℝ))
  have h1 := hg (fun _ => (1 : ℝ))
  simp at h0 h1
  exact absurd (h0.trans h1.symm) (by decide)

/-! ## Executed fp32 exactness (proved in `SymbolOpcountExecuted`)

The operation-type results above live at the real-arithmetic level. Their *executed* refinement —
that the comparison-only route run in IEEE binary32 equals the ideal-ℝ route with **zero** rounding
error (`b = 0`) — is proved in the sibling module `TLT_Proofs.Routing.SymbolOpcountExecuted`
(`executed_route_eq_leastArgmax`, conditional on per-score finiteness), which imports the fp32 stratum.
**This** module stays Mathlib-only; only the sibling imports `NN.Floats.IEEEExec.BridgeFP32Total`.

The reduction is exact: a comparison `score i ≤ score j` is a single sign bit, and the fp32 comparison
atom is *real-exact* — `compare_eq_some_lt_iff_toReal_lt` (`NN.Floats.IEEEExec.BridgeFP32`) shows the
binary32 `compare` agrees with the real `<`, with **no rounding** on `≤`. Hence the fp32-executed
comparison matrix *equals* the ℝ comparison matrix, and composing that equality with
`leastArgmax_eq_argmaxFromCmp` (the route is a function of the comparison matrix alone) yields the
executed route = the ideal route, exactly. That atom lives in the float-execution stratum
(`neural-networks` / TorchLean `IEEE32Exec`), which this layer does not depend on, so the composition
is a cross-library extension rather than an in-layer theorem.

Type-sensitivity (why it cannot be in-layer): over `ℝ`, `decide (v i ≤ v j)` is `Classical.dec` and
**noncomputable**; genuine *executable* comparison-only exactness appears only at the fp32 atom. -/
