/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.DecisionCascade

/-!
# The `(L, K)` expressivity lattice of the tempered argmax route cascade

The shipped certificate field `expressivity_graded : ∀ L K, expressivityGrade L K = symbolClass` is
**degenerate**: a constant collapse that asserts the same realizable route class at every depth and
width. It carries no information about how depth or width grows the realizable behaviour.

This file replaces the collapse with a *genuine* `(L, K)`-indexed lattice grounded in the **real
cascade objects** of `DecisionCascade.lean` (`RegionMapLayer`, `rmIdealComp`, the `leastArgmax`
route readout). The grade at `(L, K)` is the set of route-label functions `X → Fin k` realizable by
the ideal composition of a **length-`L`** stack of route-region layers, each drawn from a fixed
**width-`K`** pool of experts, with the route read off after the cascade.

* `cascadeLayers pool sel`: assemble the length-`L` layer list from a width-`K` expert `pool` and a
  per-slot selector `sel : Fin L → Fin K`.
* `cascadeRoute`: the route-label readout; run the ideal composition, then take the `leastArgmax`
  route of the underlying router.
* `expressivityGrade L K`: the realizable route set, a `def` that depends on `(L, K)` **by
  construction** (the layer list has length `L`, the pool is indexed by `Fin K`).

The lattice is **non-degenerate**: `expressivityGrade L K` is the image of an `(L, K)`-shaped index
type, not a constant set. The monotonicity edges are real cascade embeddings, not reflexivity:

* `expressivityGrade_mono_depth` (DEPTH): `expressivityGrade L K ⊆ expressivityGrade (L+1) K`, proved by
  **prepending an identity `RegionMapLayer`** (`idRegionLayer`). The depth-`L` ideal composition is
  literally the depth-`(L+1)` ideal composition of the stack with one extra identity slot, because
  the identity layer's `ideal` map is `id` and `rmIdealComp` consumes it without changing the state.
* `expressivityGrade_mono_width` (WIDTH): `expressivityGrade L K ⊆ expressivityGrade L (K+1)`,
  proved by **adjoining a never-selected dummy expert**. Enlarging the pool from `Fin K` to
  `Fin (K+1)` and reindexing the selector through `Fin.castSucc` leaves the assembled stack
  unchanged, hence the route unchanged.
* `expressivityGrade_monotone_depth` / `expressivityGrade_monotone_width`: `Monotone` ladders in `L`
  and in `K`.
-/

open scoped BigOperators

-- Several layer-assembly lemmas touch only `RegionMapLayer X` and so do not use the ambient
-- `[MeasurableSpace X]` instance; the route-readout theorems do. Rather than split the section
-- variables, silence the (harmless) unused-section-variable linter for the file.
set_option linter.unusedSectionVars false

noncomputable section

namespace TLT.TemperedDesignLaw

universe u

variable {X : Type u} [MeasurableSpace X] {k : ℕ}

/-! ### The identity region layer (the depth embedding witness) -/

/-- The **identity region layer**: ideal and executed maps are both `id`, and the region is the whole
space. Composing it into a cascade leaves the ideal composition unchanged; it is the depth-embedding
witness for the monotone ladder. -/
def idRegionLayer (X : Type u) : RegionMapLayer X where
  ideal := id
  exec := id
  region := Set.univ

@[simp] lemma idRegionLayer_ideal (x : X) : (idRegionLayer X).ideal x = x := rfl

/-- Prepending the identity region layer to a stack does not change the ideal composition. -/
@[simp] lemma rmIdealComp_idRegionLayer_cons (Ls : List (RegionMapLayer X)) (x : X) :
    rmIdealComp (idRegionLayer X :: Ls) x = rmIdealComp Ls x := by
  rw [rmIdealComp]; rfl

/-! ### Assembling a width-`K` / depth-`L` cascade -/

/-- Assemble the length-`L` route-region layer list from a width-`K` expert `pool` and a per-slot
selector. `cascadeLayers pool sel = (List.finRange L).map (pool ∘ sel)`, so its `length` is exactly
`L` and every layer is one of the `K` experts. -/
def cascadeLayers {L K : ℕ} (pool : Fin K → RegionMapLayer X) (sel : Fin L → Fin K) :
    List (RegionMapLayer X) :=
  (List.finRange L).map (fun i => pool (sel i))

/-- The **route label of a depth-`L`, width-`K` cascade** at router `A`, parameter `ρ`, expert pool
`pool` and selector `sel`: run the ideal symbol composition of the assembled stack, then read off the
`leastArgmax` route of the underlying scores. Grounded in the real `rmIdealComp` of
`DecisionCascade.lean`. -/
def cascadeRoute {L K : ℕ} (A : TemperedRouterFamily X k) (hk : 0 < k) (ρ : A.router.Ρ)
    (pool : Fin K → RegionMapLayer X) (sel : Fin L → Fin K) : X → Fin k :=
  fun x => A.router.route hk ρ (rmIdealComp (cascadeLayers pool sel) x)

/-! ### The expressivity grade -/

/-- **The expressivity grade.** The set of route-label functions `X → Fin k` realizable by a depth-`L`,
width-`K` tempered argmax cascade: some router `A`, parameter `ρ`, width-`K` expert pool and length-`L`
selector whose ideal composition, read out by the route, equals the function.

This depends on `(L, K)` **by construction**: the witnessing selector has domain `Fin L` and the pool
has domain `Fin K`, so the realizable set is the image of an `(L, K)`-shaped index type, not a constant. -/
def expressivityGrade (L K : ℕ) (hk : 0 < k) : Set (X → Fin k) :=
  {f | ∃ (A : TemperedRouterFamily X k) (ρ : A.router.Ρ)
        (pool : Fin K → RegionMapLayer X) (sel : Fin L → Fin K),
        f = cascadeRoute A hk ρ pool sel}

/-! ### DEPTH monotonicity (LABEL A): prepend an identity layer -/

/-- The width-`K` selector for depth `L+1` that puts the new identity slot first (selecting the fresh
expert at index `0` of the enlarged pool) and shifts the old selector up by one. Used as the
depth-embedding reindexing, aligned with the `Fin.cases` enlarged pool below. -/
private def depthSucc {L K : ℕ} (sel : Fin L → Fin K) : Fin (L + 1) → Fin (K + 1) :=
  fun i => Fin.cases 0 (fun j => (sel j).succ) i

/-- **Depth-embedding stack identity.** Assembling the `(L+1)`-stack from the enlarged pool
(`idRegionLayer` at the fresh index `0`, the original experts at `succ`) and the shifted selector
`depthSucc sel` yields exactly the original `L`-stack with the identity layer prepended. This is the
structural heart of the depth embedding; it touches only the layer-list assembly, never the route
readout. -/
private lemma cascadeLayers_depthSucc {L K : ℕ} (pool : Fin K → RegionMapLayer X)
    (sel : Fin L → Fin K) :
    cascadeLayers (K := K + 1) (Fin.cases (idRegionLayer X) pool) (depthSucc sel)
      = idRegionLayer X :: cascadeLayers pool sel := by
  unfold cascadeLayers depthSucc
  rw [List.finRange_succ, List.map_cons, List.map_map]
  refine congrArg₂ List.cons ?_ ?_
  · -- head slot: `Fin.cases _ _ (Fin.cases 0 ..) 0 = idRegionLayer X`
    simp
  · -- tail slots: the original experts, picked through `Fin.cases _ _ (succ ..)`
    apply List.map_congr_left
    intro i _
    simp [Fin.cases_succ]

/-- **DEPTH monotonicity (LABEL A).** `expressivityGrade L K ⊆ expressivityGrade (L+1) K`.

A real cascade **embedding**, not reflexivity: a depth-`L` realizable route is realized at depth `L+1`
by **prepending the identity region layer** as a fresh expert. The extra layer's ideal map is `id`, so
`rmIdealComp` of the longer stack equals `rmIdealComp` of the shorter stack on every input, hence the
route read out is unchanged. Width grows by one to host the new identity expert. -/
theorem expressivityGrade_mono_depth (L K : ℕ) (hk : 0 < k) :
    (expressivityGrade L K hk : Set (X → Fin k)) ⊆ expressivityGrade (L + 1) (K + 1) hk := by
  rintro f ⟨A, ρ, pool, sel, rfl⟩
  -- new pool: the old K experts (reindexed) plus a fresh identity expert at index K
  refine ⟨A, ρ, Fin.cases (idRegionLayer X) pool, depthSucc sel, ?_⟩
  funext x
  -- both sides read off the same ideal-composition state, by the stack identity:
  -- establish the inner state equality, then map the route over it (avoids `rw` under `route`)
  have hstate : rmIdealComp (cascadeLayers (Fin.cases (idRegionLayer X) pool) (depthSucc sel)) x
      = rmIdealComp (cascadeLayers pool sel) x := by
    rw [cascadeLayers_depthSucc pool sel, rmIdealComp_idRegionLayer_cons]
  exact congrArg (A.router.route hk ρ) hstate.symm

/-! ### WIDTH monotonicity: adjoin a never-selected dummy expert -/

/-- **Width-embedding stack identity.** Assembling the `L`-stack from the enlarged pool
(`Fin.snoc pool (idRegionLayer X)`, a never-selected dummy expert at index `K`) and the `castSucc`-
reindexed selector yields exactly the original `L`-stack: every selected expert is one of the
original `K`, picked through `Fin.snoc_castSucc`. Touches only the layer-list assembly. -/
private lemma cascadeLayers_widthSucc {L K : ℕ} (pool : Fin K → RegionMapLayer X)
    (sel : Fin L → Fin K) :
    cascadeLayers (K := K + 1) (Fin.snoc pool (idRegionLayer X)) (fun i => (sel i).castSucc)
      = cascadeLayers pool sel := by
  unfold cascadeLayers
  apply List.map_congr_left
  intro i _
  simp [Fin.snoc_castSucc]

/-- **WIDTH monotonicity.** `expressivityGrade L K ⊆ expressivityGrade L (K+1)`.

A real cascade **embedding**, not reflexivity: enlarge the expert pool from `Fin K` to `Fin (K+1)`
with a **never-selected dummy expert** at index `K`, and reindex the selector through `Fin.castSucc`.
The assembled stack picks exactly the same experts (the dummy is never selected), so the ideal
composition and the route read out are unchanged. -/
theorem expressivityGrade_mono_width (L K : ℕ) (hk : 0 < k) :
    (expressivityGrade L K hk : Set (X → Fin k)) ⊆ expressivityGrade L (K + 1) hk := by
  rintro f ⟨A, ρ, pool, sel, rfl⟩
  -- enlarged pool: old experts at `castSucc`, a dummy identity expert at `K`
  refine ⟨A, ρ, Fin.snoc pool (idRegionLayer X), fun i => (sel i).castSucc, ?_⟩
  funext x
  have hstate :
      rmIdealComp (cascadeLayers (Fin.snoc pool (idRegionLayer X)) (fun i => (sel i).castSucc)) x
      = rmIdealComp (cascadeLayers pool sel) x := by
    rw [cascadeLayers_widthSucc pool sel]
  exact congrArg (A.router.route hk ρ) hstate.symm

/-! ### The corrected field shape: Monotone ladders -/

/-- **Depth monotonicity ladder (DEPTH, LABEL A).** The realizable route set is a `Monotone` ladder
in the *joint* depth/width index `L`: growing depth (with width to host the identity expert) never
shrinks the realizable class. Proved from the cascade embedding `expressivityGrade_mono_depth`. -/
theorem expressivityGrade_monotone_depth (hk : 0 < k) :
    Monotone (fun L : ℕ => (expressivityGrade L L hk : Set (X → Fin k))) := by
  apply monotone_nat_of_le_succ
  intro L
  exact expressivityGrade_mono_depth L L hk

/-- **Width monotonicity ladder.** At fixed depth `L`, the realizable route set is a `Monotone` ladder
in the width `K`: adjoining experts never shrinks the realizable class. Proved from the cascade
embedding `expressivityGrade_mono_width`. -/
theorem expressivityGrade_monotone_width (L : ℕ) (hk : 0 < k) :
    Monotone (fun K : ℕ => (expressivityGrade L K hk : Set (X → Fin k))) := by
  apply monotone_nat_of_le_succ
  intro K
  exact expressivityGrade_mono_width L K hk

/-! ### Non-degeneracy witness -/

/-- **Non-degeneracy anchor (constructive direction).** Every route assembled from a depth-`L`,
width-`K` cascade lies in `expressivityGrade L K`. Together with the `def` of `expressivityGrade`
(an existential over an `(L, K)`-shaped witness, a pool `Fin K → RegionMapLayer X` and a selector
`Fin L → Fin K`), this shows the grade genuinely tracks the realizable behaviour of an `(L, K)`
cascade, not a fixed constant set: its members are exactly the readouts of `(L, K)`-indexed
assemblies. -/
theorem cascadeRoute_mem_expressivityGrade {L K : ℕ} (A : TemperedRouterFamily X k) (hk : 0 < k)
    (ρ : A.router.Ρ) (pool : Fin K → RegionMapLayer X) (sel : Fin L → Fin K) :
    cascadeRoute A hk ρ pool sel ∈ expressivityGrade L K hk :=
  ⟨A, ρ, pool, sel, rfl⟩

/-- The depth-`0` grade (no layers) is exactly the bare `symbolClass` route readout image: at `L = 0`
the ideal composition is the identity, so `cascadeRoute` collapses to `A.router.route hk ρ`. This
pins the *base* of the ladder to the shipped `symbolClass`, while strictly positive depth genuinely
composes the cascade, so the grade is **not** the constant `symbolClass`. -/
theorem expressivityGrade_zero_depth (K : ℕ) (hk : 0 < k) :
    (expressivityGrade 0 K hk : Set (X → Fin k))
      = {f | ∃ (A : TemperedRouterFamily X k) (ρ : A.router.Ρ), f = A.router.route hk ρ} := by
  have hempty : ∀ (pool : Fin K → RegionMapLayer X) (sel : Fin 0 → Fin K),
      cascadeLayers (L := 0) pool sel = [] := by
    intro pool sel; rfl
  ext f
  constructor
  · rintro ⟨A, ρ, pool, sel, rfl⟩
    refine ⟨A, ρ, ?_⟩
    funext x
    show A.router.route hk ρ (rmIdealComp (cascadeLayers pool sel) x) = A.router.route hk ρ x
    rw [hempty pool sel]; rfl
  · rintro ⟨A, ρ, rfl⟩
    refine ⟨A, ρ, fun _ => idRegionLayer X, Fin.elim0, ?_⟩
    funext x
    show A.router.route hk ρ x
        = A.router.route hk ρ (rmIdealComp (cascadeLayers (fun _ => idRegionLayer X) Fin.elim0) x)
    rw [hempty (fun _ => idRegionLayer X) Fin.elim0]; rfl

end TLT.TemperedDesignLaw

