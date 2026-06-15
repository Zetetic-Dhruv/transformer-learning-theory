/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.ExpressivityLattice

/-!
# The expressivity-lattice degeneracy: the S4 strict-separation bound does not hold

The `(L, K)` lattice of `ExpressivityLattice.lean` is built from a genuine `(L, K)`-shaped index type
(a width-`K` expert pool and a length-`L` selector), and its monotone ladders are real cascade
embeddings. One might hope that this yields a *strict* expressivity lower bound, namely that
`expressivityGrade L K ⊊ expressivityGrade (L+1) (K+1)`, i.e. that growing depth/width strictly
enlarges the realizable route class. This file proves that **no such strict separation holds for any
measurable route function**, because the router family `A` in the existential defining
`expressivityGrade` is **completely unconstrained**.

The bare argmax router at depth `0`, width `0` (no cascade layers at all) already realizes **every
measurable route function** `f : X → Fin k`: take the indicator-score router whose score vector at `x`
is the one-hot of `f x` (value `1` on coordinate `f x`, `0` elsewhere). Its unique maximizer is `f x`,
so its `leastArgmax` route *is* `f`. The cascade adds nothing on top of an already-universal base.

## Main results

* `leastArgmax_indicator`: the `leastArgmax` of a one-hot score vector is its hot index.
* `indicatorRouter`: the `FiniteScoreRouterCode` whose route is exactly `f` (parameter `Ρ := PUnit`).
* `bareRouter_realizes_measurable` (**THE DEGENERACY**): every measurable `f` lies in
  `expressivityGrade 0 0`.
* `measurable_mem_expressivityGrade`: every measurable `f` lies in *every* grade.
* `expressivityGrade_zero_eq_measurable`: the exact base characterization,
  `expressivityGrade 0 0 = {f | Measurable f}` (⊇ from the indicator router; ⊆ from
  `FiniteScoreRouterCode.route_measurable`).
* `strict_separation_not_genuine` (**THE CONCLUSION**): on measurable functions the two grades
  `(L, K)` and `(L+1, K+1)` coincide, so the claimed `⊊` can only be witnessed by a *non-measurable*
  route function (an unconstrained region map). It is not a genuine expressivity bound.

This is a negative result: it proves why the stated separation fails.
-/

open scoped BigOperators

noncomputable section

namespace TLT.TemperedDesignLaw

universe u

/-! ### (1) The least argmax of a one-hot score vector -/

/-- **One-hot maximizer.** The `leastArgmax` of the indicator score vector
`fun i => if c = i then 1 else 0` is `c` itself: `c` is the unique maximizer (it attains the value `1`,
every other index attains `0 < 1`), so the deterministic tie-breaking `leastArgmax` returns it. -/
theorem leastArgmax_indicator {k : ℕ} (hk : 0 < k) (c : Fin k) :
    leastArgmax (fun i => if c = i then (1 : ℝ) else 0) hk = c := by
  -- `c` satisfies `isLeastArgmax` for the one-hot vector, and `leastArgmax` also satisfies it; unique.
  apply isLeastArgmax_unique _ _ _ (leastArgmax_spec _ hk)
  refine ⟨fun j => ?_, fun j hj => ?_⟩
  · -- maximizer: every coordinate `≤` the hot value `1`
    by_cases hcj : c = j
    · simp [hcj]
    · simp [hcj]
  · -- strict on indices below `c`: such `j ≠ c`, so its value is `0 < 1`
    have hne : c ≠ j := fun h => (lt_irrefl _) (h ▸ hj)
    simp only [if_neg hne]
    exact zero_lt_one

/-! ### (2) The indicator router that realizes an arbitrary measurable `f` -/

variable {X : Type u} [MeasurableSpace X] {k : ℕ}

/-- **The indicator router.** Given a measurable `f : X → Fin k`, the score router with trivial
parameter space `Ρ := PUnit` and one-hot scores `score () x i := if f x = i then 1 else 0`. Its argmax
route is exactly `f` (see `indicatorRouter_route`). The per-head measurability comes from the fact that
the hot set `{x | f x = i}` is measurable (`f` is measurable and `{i}` is measurable in `Fin k`). -/
def indicatorRouter (f : X → Fin k) (hf : Measurable f) : FiniteScoreRouterCode X k where
  Ρ := PUnit
  instMeasΡ := inferInstance
  instStdΡ := inferInstance
  score := fun _ x i => if f x = i then (1 : ℝ) else 0
  score_meas := fun i => by
    -- the score, as a function of `p : PUnit × X`, is the indicator of the measurable set
    -- `{p | f p.2 = i}` = `(f ∘ snd) ⁻¹' {i}`.
    have hset : MeasurableSet {p : PUnit × X | f p.2 = i} :=
      (hf.comp measurable_snd) (measurableSet_singleton i)
    exact Measurable.piecewise hset measurable_const measurable_const

/-- The indicator router's argmax route is exactly `f`: at every `x`, the one-hot score vector's
unique maximizer is `f x`, recovered by `leastArgmax_indicator`. -/
@[simp] theorem indicatorRouter_route (hk : 0 < k) (f : X → Fin k) (hf : Measurable f) :
    (indicatorRouter f hf).route hk = fun (_ : PUnit) x => f x := by
  funext _ x
  show leastArgmax (fun i => if f x = i then (1 : ℝ) else 0) hk = f x
  exact leastArgmax_indicator hk (f x)

/-! ### (3) THE DEGENERACY: the bare router already realizes every measurable `f` -/

/-- **THE DEGENERACY (the core).** Every measurable route function `f : X → Fin k` already lies in the
base grade `expressivityGrade 0 0`: no cascade layers, no width, just the bare argmax router. The
witness is the tempered family built from `indicatorRouter f hf` (sharpness `β = 0`), parameter
`ρ = PUnit.unit`, the empty pool and the empty selector. At depth `0` the cascade has no layers, so
`cascadeRoute` collapses to the bare route `A.router.route hk ρ`, which is `f` by
`indicatorRouter_route`.

Because the router family `A` is **unconstrained** in the existential defining `expressivityGrade`,
the lattice's base is already universal among measurable functions: there is no expressivity content to
separate. -/
theorem bareRouter_realizes_measurable (hk : 0 < k) (f : X → Fin k) (hf : Measurable f) :
    f ∈ expressivityGrade 0 0 hk := by
  refine ⟨⟨indicatorRouter f hf, 0, le_refl 0⟩, PUnit.unit, Fin.elim0, Fin.elim0, ?_⟩
  funext x
  -- `cascadeLayers (L := 0) _ _ = []`, so `rmIdealComp [] x = x`, and the bare route is `f x`.
  show f x = (indicatorRouter f hf).route hk PUnit.unit
      (rmIdealComp (cascadeLayers Fin.elim0 Fin.elim0) x)
  have hempty : cascadeLayers (L := 0) (Fin.elim0 : Fin 0 → RegionMapLayer X) Fin.elim0 = [] := rfl
  rw [hempty]
  show f x = (indicatorRouter f hf).route hk PUnit.unit x
  rw [indicatorRouter_route hk f hf]

/-! ### (4) The monotone corollary: every well-shaped grade contains every measurable function -/

/-- **The monotone corollary.** Whenever the grade is well-shaped (`L ≤ K`, so the pool `Fin K` can
host the length-`L` selector), every measurable `f` lies in `expressivityGrade L K`. It is already in
the base `expressivityGrade 0 0` (the degeneracy), and the grade only grows from there under the landed
monotone ladders: climb the *joint* depth/width ladder `(0,0) → (L,L)`, then the width ladder
`(L,L) → (L,K)`.

The hypothesis `L ≤ K` is genuinely necessary, not a convenience: for `K < L` the selector type
`Fin L → Fin K` can be empty (e.g. `K = 0 < L`), in which case the grade is *empty* and contains no
function at all. The degeneracy is a statement about the realizable region `L ≤ K`, which is exactly
the region the depth ladder traverses (depth raises width in lockstep). -/
theorem measurable_mem_expressivityGrade (hk : 0 < k) (L K : ℕ) (hLK : L ≤ K) (f : X → Fin k)
    (hf : Measurable f) : f ∈ expressivityGrade L K hk := by
  -- Step A: from the base, raise to depth/width `(L, L)` along the joint depth ladder.
  have hbase : f ∈ expressivityGrade 0 0 hk := bareRouter_realizes_measurable hk f hf
  have hLL : f ∈ expressivityGrade L L hk :=
    expressivityGrade_monotone_depth hk (Nat.zero_le L) hbase
  -- Step B: at fixed depth `L`, raise width `L → K` along the width ladder (`L ≤ K`).
  exact expressivityGrade_monotone_width L hk hLK hLL

/-! ### (5) The exact base characterization -/

/-- **Sectioned route measurability.** The bare argmax route of a finite score router, at a fixed
parameter `ρ`, is a measurable function of the input: the joint `(Ρ × X)`-measurability
`FiniteScoreRouterCode.route_measurable` precomposed with the measurable section `x ↦ (ρ, x)`
(`measurable_prodMk_left`).

This is stated on `FiniteScoreRouterCode` directly (rather than inlined through the
`TemperedRouterFamily.router` projection) so that the `MeasurableSpace`/`StandardBorelSpace` instances
on the parameter space resolve without forcing `whnf` through the projection. -/
theorem route_section_measurable (R : FiniteScoreRouterCode X k) (hk : 0 < k) (ρ : R.Ρ) :
    Measurable (fun x => R.route hk ρ x) :=
  (R.route_measurable hk).comp measurable_prodMk_left

/-- **The exact base characterization.** The depth-`0`, width-`0` grade is *exactly* the set of
measurable route functions:

* `⊇` is the degeneracy `bareRouter_realizes_measurable`.
* `⊆` because at depth `0` every member is a bare argmax route `A.router.route hk ρ`, which is
  measurable: `FiniteScoreRouterCode.route_measurable` gives joint `(Ρ × X)`-measurability, and the
  section at the fixed parameter `ρ` (precomposition with `fun x => (ρ, x)`, i.e.
  `measurable_prodMk_left`) is measurable.

So the lattice's base already *equals* the full measurable route class; this is the strongest possible form of
the degeneracy. -/
theorem expressivityGrade_zero_eq_measurable (hk : 0 < k) :
    (expressivityGrade 0 0 hk : Set (X → Fin k)) = {f | Measurable f} := by
  ext f
  constructor
  · -- ⊆ : every base member is a measurable bare route
    intro hf
    rw [expressivityGrade_zero_depth 0 hk] at hf
    obtain ⟨A, ρ, rfl⟩ := hf
    -- the section of the jointly-measurable route at `ρ`
    exact route_section_measurable A.router hk ρ
  · -- ⊇ : the degeneracy
    intro hf
    exact bareRouter_realizes_measurable hk f hf

/-! ### (6) The conclusion: the strict separation is not a genuine expressivity bound -/

/-- **THE CONCLUSION (the negative result, made explicit).** On *measurable* route functions the two
grades `(L, K)` and `(L+1, K+1)` coincide: for every measurable `f` (and any well-shaped `L ≤ K`),
`f ∈ expressivityGrade L K ↔ f ∈ expressivityGrade (L+1) (K+1)`. Both sides are unconditionally true by
the monotone corollary.

Consequently the hoped-for strict separation `expressivityGrade L K ⊊ expressivityGrade (L+1) (K+1)`
can be witnessed **only by a non-measurable route function**, specifically by an unconstrained (non-measurable)
region map, never by a measurable transformer route. The separation, as stated over the
unconstrained router family, is therefore **not a genuine expressivity lower bound**: it reflects the
freedom of the existential's router argument, not any depth/width-induced gain in realizable measurable
behaviour. -/
theorem strict_separation_not_genuine (hk : 0 < k) (L K : ℕ) (hLK : L ≤ K) (f : X → Fin k)
    (hf : Measurable f) :
    f ∈ expressivityGrade L K hk ↔ f ∈ expressivityGrade (L + 1) (K + 1) hk := by
  constructor
  · intro _
    exact measurable_mem_expressivityGrade hk (L + 1) (K + 1) (by omega) f hf
  · intro _
    exact measurable_mem_expressivityGrade hk L K hLK f hf

/-! ### Concrete degeneracy sanity check (a non-constant measurable `f`) -/

/-- A concrete *non-constant* measurable route function on `ℝ`: `f x = 1` if `0 ≤ x`, else `0`. -/
def stepRoute : ℝ → Fin 2 := fun x => if 0 ≤ x then 1 else 0

theorem stepRoute_measurable : Measurable stepRoute := by
  unfold stepRoute
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

/-- It is genuinely non-constant (it takes both values), so it is *not* a constant route. -/
theorem stepRoute_nonconstant : stepRoute 1 ≠ stepRoute (-1) := by
  have h1 : stepRoute 1 = 1 := by
    simp only [stepRoute, if_pos (by norm_num : (0 : ℝ) ≤ 1)]
  have h2 : stepRoute (-1) = 0 := by
    simp only [stepRoute, if_neg (by norm_num : ¬ (0 : ℝ) ≤ -1)]
  rw [h1, h2]
  decide

/-- The concrete non-constant `stepRoute` lies in the *base* grade `expressivityGrade 0 0`: the
indicator router realizes it with no cascade at all. This witnesses that the degeneracy is not a
vacuous or constant phenomenon. -/
theorem stepRoute_mem_base :
    stepRoute ∈ expressivityGrade 0 0 (by norm_num : 0 < 2) :=
  bareRouter_realizes_measurable (by norm_num) stepRoute stepRoute_measurable

end TLT.TemperedDesignLaw

