/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MuxDepthLadder

/-!
# The 1-D linear-region calculus (Strategy C) and the affine-argmax alternation bound

This module supplies the missing **1-D linear-region calculus** that the prior depth-ladder work
(`MuxDepthLadder.lean`) stalled on: it had `trace_no_ABA_depth_one` for `L = 1` but no `L ≥ 2`
analogue, because that required the general *piecewise-linear piece-count* machinery. Here we land
that machinery.

## (i) THE PRIMARY DELIVERABLE — the affine-argmax interval / alternation bound

For `n ≥ 1` affine functions `g i t = a i * t + c i` of a real variable `t`, the active index
`affineArg g hn t := leastArgmax (fun i => g i t) hn` partitions `ℝ` into at most `n` constancy
intervals. We prove this via the brief's clean strategy, sharpened:

* **`affineArg_win_ordConnected`** — the WIN-SET of each index `i`, `{t | affineArg g hn t = i}`, is an
  `OrdConnected` subset of `ℝ` (an interval). Reason: the `leastArgmax`-win set is
  `{t | ∀ j, g j t ≤ g i t} ∩ {t | ∀ j < i, g j t < g i t}`, a finite intersection of affine
  half-lines `{t | (a j − a i) t ≤/<  c i − c j}`, each of which is `OrdConnected` (it is the
  preimage of `Iic`/`Iio` under the affine map `t ↦ (a j − a i) t`, which is monotone or antitone),
  and `OrdConnected` is closed under intersection.

  (This is exactly the convex-envelope structure of Strategy C made discrete: `t ↦ ⨆ i, g i t` is a
  convex piecewise-affine envelope, and the active-index win-sets are precisely its linear-piece
  domains; an interval each.)

* **`affineArg_alternations_le`** — along ANY strictly increasing sample `pts : Fin (m+1) → ℝ`, the
  number of index-changes of `affineArg` is `≤ n − 1` (`seqChanges (k ↦ arg (pts k)) ≤ n − 1`). Reason
  (the interval ⇒ block argument): each win-set being an interval means the sample-positions mapping to
  a given index `i` form a CONTIGUOUS block of positions (`SeqNoReturn`); with `n` indices and `n`
  contiguous blocks, the value sequence changes at most `n − 1` times (`seqChanges_le_of_noReturn`,
  proved by injecting the change-indices into `univ \ {first value}`). The arity-2 specialization
  `affineArg_two_alternations_le` recovers "an affine threshold flips ≤ once".

## (ii) Composition / refinement on the alternation count

`seqChanges_pair_le` (a paired sequence changes `≤` the sum of component changes) and the doubling
engine `seqChanges_blockRefine_le` (refining a coarse sequence `u` by ONE binary bit `b` that flips
`≤ once` per `u`-constant block changes `≤ 2·seqChanges u + 1` times). This is the alternation-level
form of "PWL composition multiplies piece counts" specialized to the arity-2 fold the ladder needs.

## The application: the `∀L` ladder (CLOSED)

We connect to `binCascade`: the depth-`L` arity-2 run on `d = 1` and its route.
* `binTrace_alternations_le` — the trace changes `≤ 2^L − 1` times (induction on `L`, one block-refine
  per layer). This is the `∀L` analogue the base file lacked (`trace_no_ABA` only held at `L = 1`).
* `binRoute_alternations_le` — the route changes `≤ 2^{L+1} − 1` times (one more block-refine: the
  route is a single affine threshold on each trace-fiber).
* `upTentRoute_alternations_eq` — the depth-`L` iterated up-tent route changes EXACTLY `2^L` times
  along the dyadic grid (the dyadic identity `tentMap^[L](j/2^L) = j mod 2`).
* `binCascadeGrade_ssubset_succ` — `binGrade 1 2 L ⊂ binGrade 1 2 (L+1)` for ALL `L`: the depth-`(L+1)`
  tent route (`2^{L+1}` alternations) exceeds the depth-`L` route bound (`2^{L+1} − 1`) — a REAL `∀L`
  proved non-membership, NOT `⊆` relabeled.

All proofs are `sorry`-free, `native_decide`-free; axiom audit at the foot of the file.
-/

open scoped BigOperators
open Set

noncomputable section

namespace TLT.TemperedDesignLaw.MuxHierarchy

universe u

/-! ## (i.0) The affine-argmax active index of `n` 1-D affine functions -/

/-- A finite family of 1-D affine functions `g i t = a i * t + c i`, packaged by its
slope vector `a` and intercept vector `c`. -/
structure AffineLines (n : ℕ) where
  a : Fin n → ℝ
  c : Fin n → ℝ

/-- The value of line `i` at the real point `t`. -/
def AffineLines.val {n : ℕ} (g : AffineLines n) (i : Fin n) (t : ℝ) : ℝ := g.a i * t + g.c i

/-- The active (least-argmax) index of the family at `t`: the least index whose line is highest. -/
def AffineLines.arg {n : ℕ} (g : AffineLines n) (hn : 0 < n) (t : ℝ) : Fin n :=
  leastArgmax (fun i => g.val i t) hn

/-! ## (i.1) Each pairwise comparison set of two affine lines is an interval (`OrdConnected`)

The atom of the whole calculus: `{t | g j t ≤ g i t}` and `{t | g j t < g i t}` are intervals.
A single affine function `t ↦ (a j − a i) t + (c j − c i)` is *both convex and concave*, so its
sublevel set `{t | … ≤ 0}` (and strict version) is an interval; we prove this directly via the
linear-interpolation identity, which needs no slope-sign case split.
-/

/-- The difference value `g i t − g j t = (a i − a j) t + (c i − c j)`. On a real interval it
interpolates linearly, which is what makes its sign-sets intervals. -/
theorem AffineLines.val_sub_affine {n : ℕ} (g : AffineLines n) (i j : Fin n) (t : ℝ) :
    g.val i t - g.val j t = (g.a i - g.a j) * t + (g.c i - g.c j) := by
  simp only [AffineLines.val]; ring

/-- The affine difference `D i j t = g i t − g j t`, as a function of `t`. -/
private def AffineLines.diff {n : ℕ} (g : AffineLines n) (i j : Fin n) (t : ℝ) : ℝ :=
  (g.a i - g.a j) * t + (g.c i - g.c j)

private theorem AffineLines.diff_eq {n : ℕ} (g : AffineLines n) (i j : Fin n) (t : ℝ) :
    g.diff i j t = g.val i t - g.val j t := by
  simp only [AffineLines.diff, AffineLines.val]; ring

/-- **Interpolation:** for `x ≤ z ≤ y` the affine `D` value at `z` is a convex combination of its
values at `x` and `y`. This is the single analytic fact behind all interval/`OrdConnected` claims. -/
private theorem AffineLines.diff_interp {n : ℕ} (g : AffineLines n) (i j : Fin n)
    {x y z : ℝ} (hxz : x ≤ z) (hzy : z ≤ y) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ g.diff i j z = (1 - θ) * g.diff i j x + θ * g.diff i j y := by
  rcases eq_or_lt_of_le (le_trans hxz hzy) with hxyeq | hxylt
  · -- x = y ⇒ z = x : take θ = 0
    have hzx : z = x := le_antisymm (hxyeq ▸ hzy) hxz
    exact ⟨0, le_refl _, by norm_num, by rw [hzx]; ring⟩
  · have hpos : 0 < y - x := by linarith
    refine ⟨(z - x) / (y - x), div_nonneg (by linarith) (le_of_lt hpos), ?_, ?_⟩
    · rw [div_le_one hpos]; linarith
    · -- D z = (1-θ) D x + θ D y.  Multiply through by (y-x) > 0 and use `field_simp`-free algebra.
      set θ : ℝ := (z - x) / (y - x) with hθ
      have hθmul : θ * (y - x) = z - x := by rw [hθ]; field_simp
      simp only [AffineLines.diff]
      -- goal: (a i - a j) z + (c i - c j) = (1-θ)((a i - a j) x + (c i - c j)) + θ((a i - a j) y + ...)
      have key : (1 - θ) * ((g.a i - g.a j) * x + (g.c i - g.c j))
            + θ * ((g.a i - g.a j) * y + (g.c i - g.c j))
          = (g.a i - g.a j) * (x + θ * (y - x)) + (g.c i - g.c j) := by ring
      rw [key, hθmul]; ring_nf

/-- **A `≤`-comparison set of two affine lines is `OrdConnected` (an interval).**
`{t | g j t ≤ g i t}`. The difference `D = g i − g j` is affine; on `Icc x y` it interpolates, so
`D x ≥ 0` and `D y ≥ 0` force `D z ≥ 0`. -/
theorem AffineLines.le_set_ordConnected {n : ℕ} (g : AffineLines n) (i j : Fin n) :
    OrdConnected {t : ℝ | g.val j t ≤ g.val i t} := by
  rw [ordConnected_def]
  intro x hx y hy z hz
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  obtain ⟨hxz, hzy⟩ := hz
  have hDx : 0 ≤ g.diff i j x := by rw [AffineLines.diff_eq]; linarith
  have hDy : 0 ≤ g.diff i j y := by rw [AffineLines.diff_eq]; linarith
  obtain ⟨θ, hθ0, hθ1, hDz⟩ := AffineLines.diff_interp g i j hxz hzy
  have hpos : 0 ≤ g.diff i j z := by
    rw [hDz]
    have h1 : 0 ≤ (1 - θ) * g.diff i j x := mul_nonneg (by linarith) hDx
    have h2 : 0 ≤ θ * g.diff i j y := mul_nonneg hθ0 hDy
    linarith
  rw [AffineLines.diff_eq] at hpos; linarith

/-- **A strict `<`-comparison set of two affine lines is `OrdConnected` (an interval).**
`{t | g j t < g i t}`. -/
theorem AffineLines.lt_set_ordConnected {n : ℕ} (g : AffineLines n) (i j : Fin n) :
    OrdConnected {t : ℝ | g.val j t < g.val i t} := by
  rw [ordConnected_def]
  intro x hx y hy z hz
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  obtain ⟨hxz, hzy⟩ := hz
  have hDx : 0 < g.diff i j x := by rw [AffineLines.diff_eq]; linarith
  have hDy : 0 < g.diff i j y := by rw [AffineLines.diff_eq]; linarith
  obtain ⟨θ, hθ0, hθ1, hDz⟩ := AffineLines.diff_interp g i j hxz hzy
  have hpos : 0 < g.diff i j z := by
    rw [hDz]
    rcases eq_or_lt_of_le hθ0 with h0 | h0
    · rw [← h0]; simp only [sub_zero, one_mul, zero_mul, add_zero]; exact hDx
    · have h1 : 0 < θ * g.diff i j y := mul_pos h0 hDy
      have h2 : 0 ≤ (1 - θ) * g.diff i j x := mul_nonneg (by linarith) (le_of_lt hDx)
      linarith
  rw [AffineLines.diff_eq] at hpos; linarith

/-! ## (i.2) Each `arg`-win-set is an interval (`OrdConnected`) -/

/-- **The win-set of an index is the `isLeastArgmax` cell.** `arg g hn t = i` iff `i` is the
least-argmax of the values at `t` — i.e. `i` weakly beats all indices and strictly beats all smaller
ones. -/
theorem AffineLines.arg_eq_iff {n : ℕ} (g : AffineLines n) (hn : 0 < n) (t : ℝ) (i : Fin n) :
    g.arg hn t = i ↔ ((∀ j, g.val j t ≤ g.val i t) ∧ (∀ j, j < i → g.val j t < g.val i t)) := by
  unfold AffineLines.arg
  constructor
  · intro h
    have hspec : isLeastArgmax (fun j => g.val j t) i := by
      rw [← h]; exact leastArgmax_spec _ hn
    exact ⟨hspec.1, hspec.2⟩
  · rintro ⟨hle, hlt⟩
    exact isLeastArgmax_unique _ _ _ (leastArgmax_spec _ hn) ⟨hle, hlt⟩

/-- **(i) THE WIN-SET IS AN INTERVAL.** `{t | arg g hn t = i}` is `OrdConnected`: it is the finite
intersection of the affine `≤`-cells `{t | g j t ≤ g i t}` (over all `j`) and the affine `<`-cells
`{t | g j t < g i t}` (over `j < i`), each `OrdConnected` by `le_set_ordConnected` /
`lt_set_ordConnected`, and `OrdConnected` is closed under (arbitrary) intersection. -/
theorem AffineLines.arg_win_ordConnected {n : ℕ} (g : AffineLines n) (hn : 0 < n) (i : Fin n) :
    OrdConnected {t : ℝ | g.arg hn t = i} := by
  have hset : {t : ℝ | g.arg hn t = i}
      = (⋂ j : Fin n, {t : ℝ | g.val j t ≤ g.val i t})
        ∩ (⋂ j : Fin n, ⋂ _ : j < i, {t : ℝ | g.val j t < g.val i t}) := by
    ext t
    simp only [AffineLines.arg_eq_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hset]
  refine OrdConnected.inter ?_ ?_
  · exact ordConnected_iInter (fun j => g.le_set_ordConnected i j)
  · exact ordConnected_iInter (fun j => ordConnected_iInter (fun _ => g.lt_set_ordConnected i j))

/-- **NO-RETURN (the working form of the interval bound).** If `arg` takes the SAME value `i` at two
points `x ≤ y`, it takes that value at every point in between. Immediate from
`arg_win_ordConnected`. This is what powers the contiguous-block alternation count. -/
theorem AffineLines.arg_no_return {n : ℕ} (g : AffineLines n) (hn : 0 < n)
    {x y z : ℝ} (hxz : x ≤ z) (hzy : z ≤ y) {i : Fin n}
    (hx : g.arg hn x = i) (hy : g.arg hn y = i) : g.arg hn z = i := by
  have hoc := g.arg_win_ordConnected hn i
  rw [ordConnected_def] at hoc
  exact hoc (Set.mem_setOf_eq ▸ hx) (Set.mem_setOf_eq ▸ hy) ⟨hxz, hzy⟩

/-! ## (i.3) The alternation count and its `≤ n − 1` bound (the contiguous-block argument)

We abstract the combinatorial heart: any sequence `s : Fin (m+1) → β` (`β` a finite type, here
`β = Fin n`) with the **no-return** property
`∀ a c b, a ≤ c → c ≤ b → s a = s b → s c = s a`
changes value at most `Fintype.card β − 1` times. The proof maps each change-index `i` (where
`s i.castSucc ≠ s i.succ`) to the value `s i.succ`; no-return makes this map injective and forces its
image to miss `s 0`, so the number of change-indices is `≤ card β − 1`.
-/

/-- The number of value-changes of a sequence `s : Fin (m+1) → β` along its `m` adjacent pairs. -/
def seqChanges {β : Type*} [DecidableEq β] {m : ℕ} (s : Fin (m + 1) → β) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => s i.castSucc ≠ s i.succ)).card

/-- The "no-return" property of a sequence: a value, once left (as the index increases), never recurs.
Equivalently each value-fiber is an interval of indices. -/
def SeqNoReturn {β : Type*} {m : ℕ} (s : Fin (m + 1) → β) : Prop :=
  ∀ a b c : Fin (m + 1), a ≤ c → c ≤ b → s a = s b → s c = s a

/-- **THE CONTIGUOUS-BLOCK ALTERNATION BOUND (abstract).** A no-return sequence into a finite type
changes value at most `card β − 1` times. The change-indices inject (via `i ↦ s i.succ`) into
`(univ : Finset β) \ {s 0}`. -/
theorem seqChanges_le_of_noReturn {β : Type*} [DecidableEq β] [Fintype β] {m : ℕ}
    (s : Fin (m + 1) → β) (hnr : SeqNoReturn s) :
    seqChanges s ≤ Fintype.card β - 1 := by
  classical
  set S : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => s i.castSucc ≠ s i.succ) with hS
  -- the value entered at each change index
  set φ : Fin m → β := fun i => s i.succ with hφ
  -- φ is injective on S
  have hinj : ∀ i ∈ S, ∀ i' ∈ S, φ i = φ i' → i = i' := by
    intro i hi i' hi' heq
    by_contra hne
    -- WLOG i < i'
    have hi_ch : s i.castSucc ≠ s i.succ := (Finset.mem_filter.mp hi).2
    have hi'_ch : s i'.castSucc ≠ s i'.succ := (Finset.mem_filter.mp hi').2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- i < i' : s i.succ = s i'.succ = v.  positions i.succ ≤ i'.castSucc ≤ i'.succ all have v
      have hle1 : (i.succ : Fin (m+1)) ≤ i'.castSucc := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        omega
      have hle2 : (i'.castSucc : Fin (m+1)) ≤ i'.succ := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
      have hv : s i.succ = s i'.succ := heq
      -- no-return on [i.succ, i'.succ] containing i'.castSucc
      have hmid : s i'.castSucc = s i.succ := hnr i.succ i'.succ i'.castSucc hle1 hle2 hv
      -- but s i'.castSucc ≠ s i'.succ = s i.succ (= heq)
      exact hi'_ch (hmid.trans hv)
    · -- symmetric : i' < i
      have hle1 : (i'.succ : Fin (m+1)) ≤ i.castSucc := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
      have hle2 : (i.castSucc : Fin (m+1)) ≤ i.succ := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
      have hv : s i'.succ = s i.succ := heq.symm
      have hmid : s i.castSucc = s i'.succ := hnr i'.succ i.succ i.castSucc hle1 hle2 hv
      exact hi_ch (hmid.trans hv)
  -- the image of S under φ misses s 0
  have hmiss : ∀ i ∈ S, φ i ≠ s 0 := by
    intro i hi heq0
    have hi_ch : s i.castSucc ≠ s i.succ := (Finset.mem_filter.mp hi).2
    -- s i.succ = s 0.  positions 0 ≤ i.castSucc ≤ i.succ all share value
    have hle1 : (0 : Fin (m+1)) ≤ i.castSucc := Fin.zero_le _
    have hle2 : (i.castSucc : Fin (m+1)) ≤ i.succ := by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
    have hv : s 0 = s i.succ := heq0.symm
    have hmid : s i.castSucc = s 0 := hnr 0 i.succ i.castSucc hle1 hle2 hv
    exact hi_ch (hmid.trans heq0.symm)
  -- so S injects into univ \ {s 0}, whose card is card β − 1
  have hsub : S.image φ ⊆ Finset.univ \ {s 0} := by
    intro b hb
    simp only [Finset.mem_image] at hb
    obtain ⟨i, hi, rfl⟩ := hb
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact hmiss i hi
  have hcard_image : S.card = (S.image φ).card :=
    (Finset.card_image_of_injOn (fun i hi i' hi' h => hinj i hi i' hi' h)).symm
  have hcard_le : (S.image φ).card ≤ (Finset.univ \ {s 0} : Finset β).card :=
    Finset.card_le_card hsub
  have hsdiff : (Finset.univ \ {s 0} : Finset β).card = Fintype.card β - 1 := by
    rw [Finset.card_sdiff]
    simp [Finset.card_univ]
  rw [seqChanges, ← hS, hcard_image]
  omega

/-! ## (i.3b) Structural lemmas on `seqChanges` (congruence, pointwise map, the pair-union bound) -/

/-- `seqChanges` only depends on the sequence pointwise: equal sequences have equal change-counts. -/
theorem seqChanges_congr {β : Type*} [DecidableEq β] {m : ℕ} {s s' : Fin (m + 1) → β}
    (h : ∀ k, s k = s' k) : seqChanges s = seqChanges s' := by
  unfold seqChanges
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [h i.castSucc, h i.succ]

/-- **Pointwise map does not increase changes.** If `s' k = f (s k)` then `s'` changes only where `s`
does, so `seqChanges s' ≤ seqChanges s`. (Used to push the route through a threshold.) -/
theorem seqChanges_comp_le {β γ : Type*} [DecidableEq β] [DecidableEq γ] {m : ℕ}
    (s : Fin (m + 1) → β) (f : β → γ) :
    seqChanges (fun k => f (s k)) ≤ seqChanges s := by
  unfold seqChanges
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  intro hc
  exact hi (by rw [hc])

/-- **THE PAIR-UNION BOUND.** The number of changes of a paired sequence is at most the sum of the
two component change-counts: a pair changes only when at least one component changes (the pair's
change-set is contained in the union of the components' change-sets). -/
theorem seqChanges_pair_le {β γ : Type*} [DecidableEq β] [DecidableEq γ] {m : ℕ}
    (u : Fin (m + 1) → β) (v : Fin (m + 1) → γ) :
    seqChanges (fun k => (u k, v k)) ≤ seqChanges u + seqChanges v := by
  classical
  unfold seqChanges
  have hsub : (Finset.univ.filter
        (fun i : Fin m => (u i.castSucc, v i.castSucc) ≠ (u i.succ, v i.succ)))
      ⊆ (Finset.univ.filter (fun i : Fin m => u i.castSucc ≠ u i.succ))
        ∪ (Finset.univ.filter (fun i : Fin m => v i.castSucc ≠ v i.succ)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, ne_eq,
      Prod.mk.injEq, not_and_or] at hi ⊢
    exact hi
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _

/-- `seqChanges` as a sum of `0/1` indicators over the `m` adjacent pairs. -/
theorem seqChanges_eq_sum {β : Type*} [DecidableEq β] {m : ℕ} (s : Fin (m + 1) → β) :
    seqChanges s = ∑ i : Fin m, (if s i.castSucc ≠ s i.succ then 1 else 0) := by
  unfold seqChanges
  rw [Finset.card_filter]

/-! ## (i.3c) THE BLOCK-REFINE (doubling) LEMMA — adding one binary bit at most doubles changes

This is the combinatorial engine of the `∀L` ladder. We have a "coarse" sequence `u` and a binary
"refinement" bit `b`; the refined pair changes whenever `u` does, OR `b` flips inside a `u`-constant
block. If `b` flips **at most once per `u`-constant block** (the geometric input: inside a
trace-fiber the next gate is a single affine threshold), then the refined pair changes at most
`2 · seqChanges u + 1` times. (`2^{m+1} − 1 = 2(2^m − 1) + 1`.)
-/

/-- The number of `u`-changes strictly before position `i` — the index of the `u`-block containing
the pair `(i.castSucc, i.succ)`. -/
private def blockOf {A : Type*} [DecidableEq A] {m : ℕ} (u : Fin (m + 1) → A) (i : Fin m) : ℕ :=
  (Finset.univ.filter (fun j : Fin m => j < i ∧ u j.castSucc ≠ u j.succ)).card

/-- **THE BLOCK-REFINE BOUND.** Let `u : Fin(m+1)→A`, `b : Fin(m+1)→Fin 2`, and suppose `b` has the
**block no-return** property: on any index interval `[a,d]` on which `u` is constant, `b` does not
return to an earlier value (it flips ≤ once). Then the paired sequence `(u, b)` changes at most
`2 · seqChanges u + 1` times. -/
theorem seqChanges_blockRefine_le {A : Type*} [DecidableEq A] {m : ℕ}
    (u : Fin (m + 1) → A) (b : Fin (m + 1) → Fin 2)
    (hblock : ∀ a c d : Fin (m + 1), a ≤ c → c ≤ d →
      (∀ e, a ≤ e → e ≤ d → u e = u a) → b a = b d → b c = b a) :
    seqChanges (fun k => (u k, b k)) ≤ 2 * seqChanges u + 1 := by
  classical
  set U : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => u i.castSucc ≠ u i.succ) with hU
  set Bonly : Finset (Fin m) :=
    Finset.univ.filter (fun i : Fin m => u i.castSucc = u i.succ ∧ b i.castSucc ≠ b i.succ)
    with hBonly
  have hsub : (Finset.univ.filter
        (fun i : Fin m => (u i.castSucc, b i.castSucc) ≠ (u i.succ, b i.succ))) ⊆ U ∪ Bonly := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Prod.mk.injEq, not_and_or,
      Finset.mem_union, hU, hBonly] at hi ⊢
    rcases hi with hu | hb
    · exact Or.inl hu
    · by_cases huc : u i.castSucc = u i.succ
      · exact Or.inr ⟨huc, hb⟩
      · exact Or.inl huc
  -- The core: blockOf is injective on Bonly.
  have hinj : ∀ i ∈ Bonly, ∀ i' ∈ Bonly, blockOf u i = blockOf u i' → i = i' := by
    -- a symmetric helper for the ordered case i < i'
    have hcase : ∀ i i' : Fin m, i ∈ Bonly → i' ∈ Bonly → i < i' →
        blockOf u i = blockOf u i' → False := by
      intro i i' hi hi' hlt hbi
      simp only [hBonly, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
      obtain ⟨hiu, hib⟩ := hi
      obtain ⟨hi'u, hi'b⟩ := hi'
      -- no u-change in [i, i')
      have hno_uchange : ∀ j : Fin m, i ≤ j → j < i' → u j.castSucc = u j.succ := by
        intro j hij hji'
        by_contra hjc
        have hjlt_i' : j ∈ Finset.univ.filter (fun l : Fin m => l < i' ∧ u l.castSucc ≠ u l.succ) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji', hjc⟩
        have hjnlt_i : j ∉ Finset.univ.filter (fun l : Fin m => l < i ∧ u l.castSucc ≠ u l.succ) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
          intro hjlt _; exact absurd hjlt (not_lt.mpr hij)
        have hsubset : Finset.univ.filter (fun l : Fin m => l < i ∧ u l.castSucc ≠ u l.succ)
            ⊆ Finset.univ.filter (fun l : Fin m => l < i' ∧ u l.castSucc ≠ u l.succ) := by
          intro l hl
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
          exact ⟨lt_trans hl.1 hlt, hl.2⟩
        have heqset := Finset.eq_of_subset_of_card_le hsubset (by rw [← blockOf, ← blockOf, hbi])
        rw [heqset] at hjnlt_i
        exact hjnlt_i hjlt_i'
      -- extend to j ≤ i' (at j = i', u is constant since i' ∈ Bonly)
      have hno_uchange' : ∀ j : Fin m, i ≤ j → j ≤ i' → u j.castSucc = u j.succ := by
        intro j hij hji'
        rcases lt_or_eq_of_le hji' with h | h
        · exact hno_uchange j hij h
        · rw [h]; exact hi'u
      -- u constant on [i.castSucc, i'.succ]
      have huconst : ∀ e, i.castSucc ≤ e → e ≤ i'.succ → u e = u i.castSucc := by
        -- prove `∀ p, i.castSucc ≤ p → p ≤ i'.succ → u p = u i.castSucc` by induction on p.val
        suffices H : ∀ pv : ℕ, ∀ hpv : pv < m + 1, i.castSucc ≤ (⟨pv, hpv⟩ : Fin (m+1)) →
            (⟨pv, hpv⟩ : Fin (m+1)) ≤ i'.succ → u ⟨pv, hpv⟩ = u i.castSucc by
          intro e he1 he2; obtain ⟨ev, hev⟩ := e; exact H ev hev he1 he2
        intro pv hpv hp1 hp2
        induction pv with
        | zero =>
            have : i.castSucc = (⟨0, hpv⟩ : Fin (m+1)) :=
              le_antisymm (by simpa [Fin.le_def] using hp1) (Fin.zero_le _)
            rw [← this]
        | succ k ih =>
            by_cases hik : i.castSucc ≤ (⟨k, Nat.lt_of_succ_lt hpv⟩ : Fin (m+1))
            · have hk2 : (⟨k, Nat.lt_of_succ_lt hpv⟩ : Fin (m+1)) ≤ i'.succ := by
                simp only [Fin.le_def] at hp2 ⊢; omega
              have hkm : k < m := by
                simp only [Fin.le_def, Fin.val_succ] at hp2; omega
              -- the adjacent pair at index ⟨k⟩ is u-constant
              have hjmem : i ≤ (⟨k, hkm⟩ : Fin m) := by
                simp only [Fin.le_def, Fin.val_castSucc] at hik ⊢; exact hik
              have hjle : (⟨k, hkm⟩ : Fin m) ≤ i' := by
                simp only [Fin.le_def, Fin.val_succ] at hp2 ⊢
                omega
              have hadjk := hno_uchange' ⟨k, hkm⟩ hjmem hjle
              have hcs : (⟨k, hkm⟩ : Fin m).castSucc = (⟨k, Nat.lt_of_succ_lt hpv⟩ : Fin (m+1)) :=
                Fin.ext rfl
              have hsc : (⟨k, hkm⟩ : Fin m).succ = (⟨k + 1, hpv⟩ : Fin (m+1)) :=
                Fin.ext rfl
              rw [hcs, hsc] at hadjk
              rw [← hadjk]
              exact ih (Nat.lt_of_succ_lt hpv) hik hk2
            · have : i.castSucc = (⟨k + 1, hpv⟩ : Fin (m+1)) := by
                apply le_antisymm hp1
                simp only [Fin.le_def] at hik hp1 ⊢; push Not at hik; omega
              rw [← this]
      -- within this u-block, b has no-return; but i,i' are both b-flips with i<i' ⟹ contradiction.
      -- positions i.cs ≤ i.succ ≤ i'.cs ≤ i'.succ.  b is no-return on [i.cs, i'.succ].
      -- ordering facts
      have ho1 : (i.castSucc : Fin (m+1)) ≤ i.succ := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
      have ho2 : (i.succ : Fin (m+1)) ≤ i'.castSucc := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; simp only [Fin.lt_def] at hlt; omega
      have ho3 : (i'.castSucc : Fin (m+1)) ≤ i'.succ := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
      -- u constant referenced to base point i.succ (shifting `huconst`)
      have huconst' : ∀ e, i.succ ≤ e → e ≤ i'.succ → u e = u i.succ := by
        intro e he1 he2
        have h1 := huconst e (le_trans ho1 he1) he2
        have h2 := huconst i.succ ho1 (le_trans ho2 ho3)
        rw [h1, h2]
      -- Step 1: b i.castSucc ≠ b i'.succ  (else no-return collapses the i-flip)
      have hstep1 : b i.castSucc ≠ b i'.succ := by
        intro hcd
        have := hblock i.castSucc i.succ i'.succ ho1 (le_trans ho2 ho3) huconst hcd
        exact hib (this.symm)
      -- Step 2: from the two binary flips, b i.succ = b i'.castSucc
      -- b i.succ ≠ b i.castSucc (hib), b i.castSucc ≠ b i'.succ (hstep1) ⟹ b i.succ = b i'.succ
      have hbinary : b i.succ = b i'.succ := by
        set x := (b i.castSucc).val with hx
        set y := (b i.succ).val with hy
        set z := (b i'.succ).val with hz
        have e1 : x ≠ y := fun h => hib (Fin.ext h)
        have e2 : x ≠ z := fun h => hstep1 (Fin.ext h)
        have l1 : x < 2 := (b i.castSucc).isLt
        have l2 : y < 2 := (b i.succ).isLt
        have l3 : z < 2 := (b i'.succ).isLt
        apply Fin.ext
        show y = z
        omega
      -- Step 3: no-return on [i.succ, i'.succ] with equal endpoints forces b i'.castSucc = b i.succ
      have hcollapse := hblock i.succ i'.castSucc i'.succ ho2 ho3 huconst' hbinary
      -- but i'.castSucc flips at i', i.e. b i'.castSucc ≠ b i'.succ = b i.succ — contradiction
      exact hi'b (hcollapse.trans hbinary)
    intro i hi i' hi' hbi
    rcases lt_trichotomy i i' with h | h | h
    · exact absurd hbi (fun hbi' => hcase i i' hi hi' h hbi')
    · exact h
    · exact absurd hbi.symm (fun hbi' => hcase i' i hi' hi h hbi')
  -- |Bonly| ≤ |U| + 1
  have hBonly_card : Bonly.card ≤ U.card + 1 := by
    have hmaps : ∀ i ∈ Bonly, blockOf u i ∈ Finset.range (U.card + 1) := by
      intro i _
      simp only [Finset.mem_range]
      have hle : blockOf u i ≤ U.card := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [hU]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.2⟩
      omega
    calc Bonly.card = (Bonly.image (blockOf u)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range (U.card + 1)).card :=
          Finset.card_le_card (fun x hx => by
            simp only [Finset.mem_image] at hx
            obtain ⟨i, hi, rfl⟩ := hx; exact hmaps i hi)
      _ = U.card + 1 := Finset.card_range _
  have htotal : seqChanges (fun k => (u k, b k)) ≤ U.card + Bonly.card := by
    unfold seqChanges
    calc _ ≤ (U ∪ Bonly).card := Finset.card_le_card hsub
      _ ≤ U.card + Bonly.card := Finset.card_union_le _ _
  have hUcard : U.card = seqChanges u := rfl
  omega

/-! ## (i.4) THE PRIMARY DELIVERABLE: `affineArg_alternations_le` (the `≤ n − 1` alternation bound) -/

/-- A strictly increasing real sample of `m + 1` points. -/
def Increasing {m : ℕ} (pts : Fin (m + 1) → ℝ) : Prop :=
  ∀ i j : Fin (m + 1), i < j → pts i < pts j

/-- The active-index sequence `k ↦ arg (pts k)` of an increasing sample has the **no-return**
property: it is the pullback of `OrdConnected` win-sets along a monotone sample. -/
theorem AffineLines.argSeq_noReturn {n : ℕ} (g : AffineLines n) (hn : 0 < n) {m : ℕ}
    (pts : Fin (m + 1) → ℝ) (hinc : Increasing pts) :
    SeqNoReturn (fun k => g.arg hn (pts k)) := by
  intro a b c hac hcb hab
  -- pts a ≤ pts c ≤ pts b (monotone from strict-increasing)
  have hmono : ∀ i j : Fin (m + 1), i ≤ j → pts i ≤ pts j := by
    intro i j hij
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact le_of_lt (hinc i j h)
  have h1 : pts a ≤ pts c := hmono a c hac
  have h2 : pts c ≤ pts b := hmono c b hcb
  -- arg at a equals arg at b (= hab); no-return gives arg at c equal too
  show g.arg hn (pts c) = g.arg hn (pts a)
  exact g.arg_no_return hn h1 h2 rfl hab.symm

/-- **(i) THE PRIMARY DELIVERABLE — the affine-argmax alternation bound.** For `n ≥ 1` affine lines
and ANY strictly-increasing sample `pts : Fin (m+1) → ℝ`, the number of index-changes of the active
index `arg` is at most `n − 1`. Proof: the active-index sequence has the no-return property
(`argSeq_noReturn`, from the `OrdConnected` win-sets `arg_win_ordConnected`); the abstract
contiguous-block bound `seqChanges_le_of_noReturn` then gives `≤ card (Fin n) − 1 = n − 1`. -/
theorem affineArg_alternations_le {n : ℕ} (g : AffineLines n) (hn : 0 < n) {m : ℕ}
    (pts : Fin (m + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => g.arg hn (pts k)) ≤ n - 1 := by
  have := seqChanges_le_of_noReturn (fun k => g.arg hn (pts k)) (g.argSeq_noReturn hn pts hinc)
  rwa [Fintype.card_fin] at this

/-- The arity-`2` specialization: an affine-argmax of TWO lines changes value **at most once** along
any increasing sample. (This is the analytic content of "an affine threshold flips ≤ once", recovered
from the general calculus.) -/
theorem affineArg_two_alternations_le (g : AffineLines 2) {m : ℕ}
    (pts : Fin (m + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => g.arg (by norm_num) (pts k)) ≤ 1 := by
  have := affineArg_alternations_le g (by norm_num) pts hinc
  omega

/-! ## (ii) + APPLICATION — the depth-`L` arity-2 run/route alternation bound, by induction on `L`

We now connect the calculus to the cascade. The key geometric facts (general `L`, `d = 1`):

* On a **partial-trace fiber** (the first `m` gate bits fixed), `runUpTo m` is a fixed affine map of
  the carrier coordinate (`MuxCascade.runUpTo_eq_prefixMap_on_pfiber`).
* Hence the layer-`m` gate bit, restricted to a partial-fiber, is a single affine threshold of `t`,
  which (via the `n = 2` calculus) has **no-return** there.
* Therefore each extra layer at most **doubles + 1** the trace alternations (`seqChanges_blockRefine_le`):
  `traceChanges ≤ 2^L − 1` (`binTrace_alternations_le`).
* The route reads a single affine threshold on each full-trace fiber, so it adds one more doubling:
  `binRoute_alternations_le : routeChanges ≤ 2^{L+1} − 1`.
-/

/-- The **partial-trace fiber** predicate: `y` and `x₀` select the same branch at every layer `< m`. -/
def MuxCascade.PFiber {L : ℕ} (C : MuxCascade 1 L) (x₀ y : Fin 1 → ℝ) (m : ℕ) : Prop :=
  ∀ i : Fin L, i.val < m → C.trace y i = C.trace x₀ i

/-- **PARTIAL affine-on-fiber.** On the partial-trace fiber of `x₀` (first `m` bits fixed),
`runUpTo m y = (prefixMap x₀ m).apply y`. Same induction as the base full-fiber lemma, but using only
the bits `< m`. -/
theorem MuxCascade.runUpTo_eq_prefixMap_on_pfiber {L : ℕ} (C : MuxCascade 1 L)
    (x₀ y : Fin 1 → ℝ) :
    ∀ m, C.PFiber x₀ y m → C.runUpTo m y = (C.prefixMap x₀ m).apply y := by
  intro m
  induction m with
  | zero => intro _; simp [MuxCascade.runUpTo, MuxCascade.prefixMap]
  | succ m ih =>
      intro hpf
      rw [MuxCascade.runUpTo, MuxCascade.prefixMap]
      by_cases h : m < L
      · rw [dif_pos h, dif_pos h]
        -- partial fiber up to m holds (sub-predicate)
        have hpf_m : C.PFiber x₀ y m := fun i hi => hpf i (Nat.lt_succ_of_lt hi)
        rw [AffineSelfMap.comp_apply, ← ih hpf_m]
        have hgate : (C.layers ⟨m, h⟩).gate (C.harity ⟨m, h⟩) (C.runUpTo m y)
            = C.trace x₀ ⟨m, h⟩ := by
          have hbit : C.trace y ⟨m, h⟩ = C.trace x₀ ⟨m, h⟩ := hpf ⟨m, h⟩ (Nat.lt_succ_self m)
          simpa [MuxCascade.trace] using hbit
        simp only [AffineMuxLayer.applyLayer, hgate]
      · rw [dif_neg h, dif_neg h]
        exact ih (fun i hi => hpf i (Nat.lt_succ_of_lt hi))

/-! ### (ii.a) A binary gate evaluated through a fixed affine map is an affine-argmax of 2 lines -/

/-- Given an arity-2 layer `Lyr` and a fixed affine self-map `A` on `Fin 1 → ℝ`, the gate bit
`Lyr.gate (A.apply ![t])`, as a function of `t`, is `g.arg` for the explicit `AffineLines 2` `g`
obtained by composing each score's affine form with `A`'s coordinate action `t ↦ A.mat 0 0 · t +
A.shift 0`. -/
theorem gate_comp_affine_eq_arg (Lyr : AffineMuxLayer 1 2) (A : AffineSelfMap 1) (t : ℝ) :
    Lyr.gate (by norm_num) (A.apply (fun _ => t))
      = (AffineLines.mk
          (fun j => (Lyr.scores j).lin 0 * A.mat 0 0)
          (fun j => (Lyr.scores j).lin 0 * A.shift 0 + (Lyr.scores j).const)).arg
          (by norm_num) t := by
  unfold AffineMuxLayer.gate AffineLines.arg
  congr 1
  funext j
  -- (scores j).eval (A.apply ![t]) = lin 0 * (A.apply ![t]) 0 + const
  rw [AffineFunctional.eval_coord1]
  -- (A.apply ![t]) 0 = A.mat 0 0 * t + A.shift 0
  have hc : (A.apply (fun _ => t)) 0 = A.mat 0 0 * t + A.shift 0 := by
    rw [AffineSelfMap.apply_coord1]
  rw [hc]
  show (Lyr.scores j).lin 0 * (A.mat 0 0 * t + A.shift 0) + (Lyr.scores j).const
      = (AffineLines.mk _ _).val j t
  unfold AffineLines.val
  ring

/-! ### (ii.b) The trace alternation bound by induction on `L`

We specialize to `binCascade layers` so that `arity` is **definitionally** `2`: then the trace lands
in `Fin 2` and the layers are literally `AffineMuxLayer 1 2`, eliminating all `Fin`-casts.
-/

/-- The layer-`m` gate bit of `binCascade layers` at the real point `t` (or `0` if `m ≥ L`). -/
def binBitAt {L : ℕ} (layers : Fin L → AffineMuxLayer 1 2) (m : ℕ) (t : ℝ) : Fin 2 :=
  if h : m < L then (binCascade layers).trace (fun _ => t) ⟨m, h⟩ else 0

/-- The **prefix** trace of `binCascade layers`: first `m` bits as actual values, the rest masked
to `0`. (A function `Fin L → Fin 2`, used as the coarse sequence in the block-refine.) -/
def binPrefixVec {L : ℕ} (layers : Fin L → AffineMuxLayer 1 2) (m : ℕ) (t : ℝ) :
    Fin L → Fin 2 :=
  fun i => if i.val < m then (binCascade layers).trace (fun _ => t) i else 0

/-- The prefix at `m+1` is the prefix at `m` updated with the layer-`m` bit; hence it is a function of
the pair `(binPrefixVec layers m, binBitAt layers m)`. -/
theorem binPrefixVec_succ_eq {L : ℕ} (layers : Fin L → AffineMuxLayer 1 2) (m : ℕ) (t : ℝ) :
    binPrefixVec layers (m + 1) t
      = fun i => if i.val = m then binBitAt layers m t else binPrefixVec layers m t i := by
  funext i
  unfold binPrefixVec binBitAt
  by_cases hi : i.val = m
  · subst hi
    rw [if_pos (Nat.lt_succ_self _), if_pos rfl, dif_pos i.isLt]
  · by_cases hlt : i.val < m
    · rw [if_pos (Nat.lt_succ_of_lt hlt), if_neg hi, if_pos hlt]
    · rw [if_neg (by omega), if_neg hi, if_neg hlt]

/-- **The partial-fiber from prefix-equality.** If the prefix vectors of `t₁` and `t₂` agree, then
`![t₂]` is in the partial-trace fiber of `![t₁]` up to `m`. -/
theorem pfiber_of_binPrefixVec_eq {L : ℕ} (layers : Fin L → AffineMuxLayer 1 2)
    (m : ℕ) (t₁ t₂ : ℝ) (heq : binPrefixVec layers m t₁ = binPrefixVec layers m t₂) :
    (binCascade layers).PFiber (fun _ => t₁) (fun _ => t₂) m := by
  intro i hi
  have h := congrFun heq i
  unfold binPrefixVec at h
  rw [if_pos hi, if_pos hi] at h
  exact h.symm

/-- **THE BLOCK NO-RETURN FOR THE NEXT BIT.** On any sample interval where the prefix is constant, the
layer-`m` bit has no-return: on that interval `runUpTo m` is a single fixed affine map
(`runUpTo_eq_prefixMap_on_pfiber`), so the bit is an affine-argmax of 2 lines, whose win-sets are
intervals (`arg_no_return`). -/
theorem binBitAt_block_noReturn {L : ℕ} (layers : Fin L → AffineMuxLayer 1 2)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) (m : ℕ) :
    ∀ a c d : Fin (M + 1), a ≤ c → c ≤ d →
      (∀ e, a ≤ e → e ≤ d →
        binPrefixVec layers m (pts e) = binPrefixVec layers m (pts a)) →
      binBitAt layers m (pts a) = binBitAt layers m (pts d) →
      binBitAt layers m (pts c) = binBitAt layers m (pts a) := by
  intro a c d hac hcd hconst hbad
  set C := binCascade layers with hC
  by_cases hm : m < L
  · have hmono : ∀ i j : Fin (M + 1), i ≤ j → pts i ≤ pts j := by
      intro i j hij
      rcases eq_or_lt_of_le hij with h | h
      · rw [h]
      · exact le_of_lt (hinc i j h)
    set A := C.prefixMap (fun _ => pts a) m with hA
    set Lyr := layers ⟨m, hm⟩ with hLyr
    set g := AffineLines.mk
        (fun j => ((Lyr.scores j).lin 0 * A.mat 0 0))
        (fun j => ((Lyr.scores j).lin 0 * A.shift 0 + (Lyr.scores j).const)) with hg
    -- bit at any prefix-equal-to-a point equals g.arg
    have hbit : ∀ e : Fin (M + 1),
        binPrefixVec layers m (pts e) = binPrefixVec layers m (pts a) →
        binBitAt layers m (pts e) = g.arg (by norm_num) (pts e) := by
      intro e he
      have hpf : C.PFiber (fun _ => pts a) (fun _ => pts e) m :=
        pfiber_of_binPrefixVec_eq layers m (pts a) (pts e) he.symm
      have hrun : C.runUpTo m (fun _ => pts e) = A.apply (fun _ => pts e) :=
        C.runUpTo_eq_prefixMap_on_pfiber (fun _ => pts a) (fun _ => pts e) m hpf
      unfold binBitAt
      rw [dif_pos hm]
      -- trace bit = layer gate at runUpTo m ; arity definitionally 2 so no cast
      have htrace : C.trace (fun _ => pts e) ⟨m, hm⟩
          = Lyr.gate (by norm_num) (C.runUpTo m (fun _ => pts e)) := rfl
      rw [htrace, hrun]
      exact gate_comp_affine_eq_arg Lyr A (pts e)
    have ea : binBitAt layers m (pts a) = g.arg (by norm_num) (pts a) := hbit a rfl
    have ec : binBitAt layers m (pts c) = g.arg (by norm_num) (pts c) :=
      hbit c (hconst c hac hcd)
    have ed : binBitAt layers m (pts d) = g.arg (by norm_num) (pts d) :=
      hbit d (hconst d (le_trans hac hcd) (le_refl _))
    have hargad : g.arg (by norm_num) (pts a) = g.arg (by norm_num) (pts d) := by
      rw [← ea, ← ed]; exact hbad
    have hargc : g.arg (by norm_num) (pts c) = g.arg (by norm_num) (pts a) :=
      g.arg_no_return (by norm_num) (hmono a c hac) (hmono c d hcd) rfl hargad.symm
    rw [ec, ea]; exact hargc
  · have h0 : ∀ e, binBitAt layers m (pts e) = 0 := fun e => by
      unfold binBitAt; rw [dif_neg hm]
    rw [h0 c, h0 a]

/-- **THE PREFIX-TRACE DOUBLING BOUND.** Along any increasing sample, the first-`m`-bits prefix trace
of `binCascade layers` changes at most `2^m − 1` times. Induction on `m`: the prefix at `m+1` is a
function of the pair `(prefix m, bit m)`; the bit has block-no-return (`binBitAt_block_noReturn`), so
`seqChanges_blockRefine_le` gives `≤ 2 · (2^m − 1) + 1 = 2^{m+1} − 1`. -/
theorem binPrefixVec_alternations_le {L : ℕ} (layers : Fin L → AffineMuxLayer 1 2)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    ∀ m, seqChanges (fun k => binPrefixVec layers m (pts k)) ≤ 2 ^ m - 1 := by
  intro m
  induction m with
  | zero =>
      -- prefix at 0 is the all-zero constant ⟹ 0 changes
      have hconst : ∀ k, binPrefixVec layers 0 (pts k) = fun _ => 0 := by
        intro k; funext i; unfold binPrefixVec; rw [if_neg (Nat.not_lt_zero _)]
      have : seqChanges (fun k => binPrefixVec layers 0 (pts k))
          = seqChanges (fun _ : Fin (M + 1) => (fun _ : Fin L => (0 : Fin 2))) :=
        seqChanges_congr (fun k => hconst k)
      rw [this]
      -- a constant sequence has 0 changes
      unfold seqChanges
      simp
  | succ m ih =>
      -- prefix(m+1) = f(pair(prefix m, bit m))
      have hpair : seqChanges (fun k => binPrefixVec layers (m + 1) (pts k))
          ≤ seqChanges (fun k => (binPrefixVec layers m (pts k), binBitAt layers m (pts k))) := by
        have heq : (fun k => binPrefixVec layers (m + 1) (pts k))
            = fun k => (fun p : (Fin L → Fin 2) × Fin 2 =>
                (fun i => if i.val = m then p.2 else p.1 i))
                (binPrefixVec layers m (pts k), binBitAt layers m (pts k)) := by
          funext k; rw [binPrefixVec_succ_eq]
        rw [heq]
        exact seqChanges_comp_le
          (fun k => (binPrefixVec layers m (pts k), binBitAt layers m (pts k)))
          (fun p : (Fin L → Fin 2) × Fin 2 => (fun i => if i.val = m then p.2 else p.1 i))
      -- block-refine on the pair
      have hbr : seqChanges (fun k => (binPrefixVec layers m (pts k), binBitAt layers m (pts k)))
          ≤ 2 * seqChanges (fun k => binPrefixVec layers m (pts k)) + 1 :=
        seqChanges_blockRefine_le _ _
          (fun a c d hac hcd hconst hbad =>
            binBitAt_block_noReturn layers pts hinc m a c d hac hcd hconst hbad)
      -- arithmetic: 2*(2^m−1)+1 = 2^{m+1}−1
      have hpow : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      calc seqChanges (fun k => binPrefixVec layers (m + 1) (pts k))
          ≤ 2 * seqChanges (fun k => binPrefixVec layers m (pts k)) + 1 := le_trans hpair hbr
        _ ≤ 2 * (2 ^ m - 1) + 1 := by omega
        _ = 2 ^ (m + 1) - 1 := by rw [pow_succ]; omega

/-- **THE TRACE ALTERNATION BOUND.** The full active-branch trace of `binCascade layers` (as a function
of the carrier coordinate) changes at most `2^L − 1` times along any increasing sample. This is the
`∀L` analogue of the base file's `L = 1` `trace_no_ABA`. -/
theorem binTrace_alternations_le {L : ℕ} (layers : Fin L → AffineMuxLayer 1 2)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => (binCascade layers).trace (fun _ => pts k)) ≤ 2 ^ L - 1 := by
  have hL := binPrefixVec_alternations_le layers pts hinc L
  -- binPrefixVec layers L = full trace (all bits < L are actual)
  have heq : (fun k => binPrefixVec layers L (pts k))
      = fun k => (binCascade layers).trace (fun _ => pts k) := by
    funext k; funext i; unfold binPrefixVec; rw [if_pos i.isLt]
  rw [heq] at hL
  exact hL

/-! ### (ii.c) The route alternation bound: one more doubling on top of the trace -/

/-- **THE ROUTE BLOCK NO-RETURN.** On any sample interval where the FULL trace is constant (a single
trace-fiber), the arity-2 route `cascadeRoute (binCascade layers) rs` has no-return: on the fiber the
run is the fixed affine map `fiberMap`, so the route is an affine-argmax of 2 lines (the readout
scores composed with `fiberMap`), whose win-sets are intervals. -/
theorem binRoute_block_noReturn {L : ℕ} (layers : Fin L → AffineMuxLayer 1 2)
    (rs : Fin 2 → AffineFunctional 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    ∀ a c d : Fin (M + 1), a ≤ c → c ≤ d →
      (∀ e, a ≤ e → e ≤ d →
        (binCascade layers).trace (fun _ => pts e) = (binCascade layers).trace (fun _ => pts a)) →
      cascadeRoute (binCascade layers) rs (by norm_num) (fun _ => pts d)
        = cascadeRoute (binCascade layers) rs (by norm_num) (fun _ => pts a) →
      cascadeRoute (binCascade layers) rs (by norm_num) (fun _ => pts c)
        = cascadeRoute (binCascade layers) rs (by norm_num) (fun _ => pts a) := by
  intro a c d hac hcd hconst hbad
  set C := binCascade layers with hC
  have hmono : ∀ i j : Fin (M + 1), i ≤ j → pts i ≤ pts j := by
    intro i j hij
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact le_of_lt (hinc i j h)
  -- the fixed affine map on the fiber of ![pts a]
  set A := C.fiberMap (fun _ => pts a) with hA
  -- the route readout as an `arg` of 2 affine lines through A: build it from `rs` as a "layer"
  set readoutLyr : AffineMuxLayer 1 2 := ⟨rs, fun _ => AffineSelfMap.id 1⟩ with hRead
  set g := AffineLines.mk
      (fun j => ((rs j).lin 0 * A.mat 0 0))
      (fun j => ((rs j).lin 0 * A.shift 0 + (rs j).const)) with hg
  -- route at any fiber point equals g.arg
  have hroute : ∀ e : Fin (M + 1),
      C.trace (fun _ => pts e) = C.trace (fun _ => pts a) →
      cascadeRoute C rs (by norm_num) (fun _ => pts e) = g.arg (by norm_num) (pts e) := by
    intro e he
    have hrun : C.run (fun _ => pts e) = A.apply (fun _ => pts e) :=
      C.run_eq_on_fiber (fun _ => pts a) (fun _ => pts e) he
    unfold cascadeRoute
    rw [hrun]
    -- leastArgmax of (rs j).eval (A.apply ![pts e]) = readoutLyr.gate (A.apply ![pts e]) = g.arg
    have hgate : (readoutLyr.gate (by norm_num) (A.apply (fun _ => pts e)))
        = g.arg (by norm_num) (pts e) := gate_comp_affine_eq_arg readoutLyr A (pts e)
    -- readoutLyr.gate = leastArgmax of scores = the cascadeRoute argmax
    show leastArgmax (fun j => (rs j).eval (A.apply (fun _ => pts e))) (by norm_num)
        = g.arg (by norm_num) (pts e)
    rw [← hgate]
    rfl
  have ea := hroute a rfl
  have ec := hroute c (hconst c hac hcd)
  have ed := hroute d (hconst d (le_trans hac hcd) (le_refl _))
  have hargad : g.arg (by norm_num) (pts a) = g.arg (by norm_num) (pts d) := by
    rw [← ea, ← ed]; exact hbad.symm
  have hargc : g.arg (by norm_num) (pts c) = g.arg (by norm_num) (pts a) :=
    g.arg_no_return (by norm_num) (hmono a c hac) (hmono c d hcd) rfl hargad.symm
  rw [ec, ea]; exact hargc

/-- **THE ROUTE ALTERNATION BOUND `≤ 2^{L+1} − 1`.** Along any increasing sample, the arity-2 route of
a depth-`L` `binCascade` changes at most `2^{L+1} − 1` times. Proof: the route is a function of the
pair `(trace, route)`; the trace changes `≤ 2^L − 1` times (`binTrace_alternations_le`) and the route
has block-no-return on trace-fibers (`binRoute_block_noReturn`), so `seqChanges_blockRefine_le` adds one
more doubling: `≤ 2·(2^L − 1) + 1 = 2^{L+1} − 1`. -/
theorem binRoute_alternations_le {L : ℕ} (layers : Fin L → AffineMuxLayer 1 2)
    (rs : Fin 2 → AffineFunctional 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => cascadeRoute (binCascade layers) rs (by norm_num) (fun _ => pts k))
      ≤ 2 ^ (L + 1) - 1 := by
  -- route = π₂ ∘ (trace, route)
  have hcomp : seqChanges (fun k => cascadeRoute (binCascade layers) rs (by norm_num) (fun _ => pts k))
      ≤ seqChanges (fun k => ((binCascade layers).trace (fun _ => pts k),
          cascadeRoute (binCascade layers) rs (by norm_num) (fun _ => pts k))) := by
    have heq : (fun k => cascadeRoute (binCascade layers) rs (by norm_num) (fun _ => pts k))
        = fun k => (fun p : (Fin L → Fin 2) × Fin 2 => p.2)
            ((binCascade layers).trace (fun _ => pts k),
             cascadeRoute (binCascade layers) rs (by norm_num) (fun _ => pts k)) := rfl
    rw [heq]
    exact seqChanges_comp_le _ (fun p : (Fin L → Fin 2) × Fin 2 => p.2)
  -- block-refine on the pair (trace, route)
  have hbr : seqChanges (fun k => ((binCascade layers).trace (fun _ => pts k),
      cascadeRoute (binCascade layers) rs (by norm_num) (fun _ => pts k)))
      ≤ 2 * seqChanges (fun k => (binCascade layers).trace (fun _ => pts k)) + 1 :=
    seqChanges_blockRefine_le _ _
      (fun a c d hac hcd hconst hbad =>
        binRoute_block_noReturn layers rs pts hinc a c d hac hcd hconst hbad.symm)
  have htrace := binTrace_alternations_le layers pts hinc
  have hpow : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  calc seqChanges (fun k => cascadeRoute (binCascade layers) rs (by norm_num) (fun _ => pts k))
      ≤ 2 * seqChanges (fun k => (binCascade layers).trace (fun _ => pts k)) + 1 :=
        le_trans hcomp hbr
    _ ≤ 2 * (2 ^ L - 1) + 1 := by omega
    _ = 2 ^ (L + 1) - 1 := by rw [pow_succ]; omega

/-! ## (iii) THE ITERATED-TENT WITNESS and the `∀L` SEPARATION

We build the depth-`L` iterated up-tent cascade. The tent fold `Λ(s) = 1 − |2s − 1|` is an arity-2
layer (gate on `2s − 1 ≥ 0`, branches `s ↦ 2 − 2s` and `s ↦ 2s`). Its `L`-fold iterate satisfies the
clean dyadic identity `Λ^[L](j / 2^L) = (j mod 2 : ℝ)`, so its route (threshold at `½`) alternates
`2^L` times along the increasing dyadic grid `k ↦ k / 2^L` — **exceeding the depth-`L` route bound
`2^{L+1} − 1`** at one extra depth, giving the `∀L` separation.
-/

/-- The up-tent affine functional values: gate on `2s − 1 ≥ 0`. -/
def upTentLayer : AffineMuxLayer 1 2 where
  scores := fun i => if i = 0 then ⟨fun _ => 2, -1⟩ else ⟨fun _ => -2, 1⟩
  branches := fun i => if i = 0 then ⟨fun _ _ => -2, fun _ => 2⟩
                                else ⟨fun _ _ => 2, fun _ => 0⟩

/-- The depth-`L` iterated up-tent cascade. -/
def upTentCascade (L : ℕ) : MuxCascade 1 L := binCascade (fun _ => upTentLayer)

/-- The tent fold as a bare real map `Λ(s) = 1 − |2s − 1|`. -/
def tentMap (s : ℝ) : ℝ := 1 - |2 * s - 1|

/-- The up-tent layer's two scores evaluate to `2 s − 1` and `1 − 2 s`. -/
theorem upTentLayer_scores (s : Fin 1 → ℝ) :
    (upTentLayer.scores 0).eval s = 2 * s 0 - 1 ∧ (upTentLayer.scores 1).eval s = 1 - 2 * s 0 := by
  refine ⟨?_, ?_⟩
  · show (upTentLayer.scores 0).eval s = 2 * s 0 - 1
    have : upTentLayer.scores 0 = ⟨fun _ => 2, -1⟩ := by simp [upTentLayer]
    rw [this]; simp [AffineFunctional.eval]; ring
  · show (upTentLayer.scores 1).eval s = 1 - 2 * s 0
    have : upTentLayer.scores 1 = ⟨fun _ => -2, 1⟩ := by simp [upTentLayer]
    rw [this]; simp [AffineFunctional.eval]; ring

/-- The up-tent layer's gate: `0` iff `2 s − 1 ≥ 0` (i.e. `s ≥ ½`). -/
theorem upTentLayer_gate (s : Fin 1 → ℝ) :
    upTentLayer.gate (by norm_num) s = if 0 ≤ 2 * s 0 - 1 then 0 else 1 := by
  simp only [AffineMuxLayer.gate]; rw [leastArgmax_two]
  obtain ⟨h0, h1⟩ := upTentLayer_scores s
  simp only [h0, h1]
  by_cases hx : (0 : ℝ) ≤ 2 * s 0 - 1
  · rw [if_pos (by linarith), if_pos hx]
  · rw [if_neg (by push Not at hx ⊢; linarith), if_neg hx]

/-- The up-tent layer's carrier action is `tentMap`: `s ↦ 1 − |2s − 1|`. -/
theorem upTentLayer_apply (s : Fin 1 → ℝ) :
    (upTentLayer.applyLayer (by norm_num) s) 0 = tentMap (s 0) := by
  simp only [AffineMuxLayer.applyLayer, upTentLayer_gate, tentMap]
  by_cases hx : (0 : ℝ) ≤ 2 * s 0 - 1
  · rw [if_pos hx]
    show ((upTentLayer.branches 0).apply s) 0 = 1 - |2 * s 0 - 1|
    have hb : upTentLayer.branches 0 = ⟨fun _ _ => -2, fun _ => 2⟩ := by simp [upTentLayer]
    rw [hb]; simp [AffineSelfMap.apply]
    rw [abs_of_nonneg hx]; ring
  · rw [if_neg hx]
    show ((upTentLayer.branches 1).apply s) 0 = 1 - |2 * s 0 - 1|
    have hb : upTentLayer.branches 1 = ⟨fun _ _ => 2, fun _ => 0⟩ := by simp [upTentLayer]
    rw [hb]; simp [AffineSelfMap.apply]
    rw [abs_of_neg (by linarith : 2 * s 0 - 1 < 0)]; ring

/-- **The iterated-tent run is the iterate of `tentMap`.** `runUpTo m` of `upTentCascade L` applied to
`![t]` has carrier coordinate `tentMap^[m] t`. -/
theorem upTentCascade_runUpTo_coord (L : ℕ) (t : ℝ) :
    ∀ m, m ≤ L → ((upTentCascade L).runUpTo m (fun _ => t)) 0 = (tentMap^[m]) t := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      rw [MuxCascade.runUpTo, dif_pos (by omega : m < L)]
      show (upTentLayer.applyLayer _ ((upTentCascade L).runUpTo m (fun _ => t))) 0 = _
      rw [upTentLayer_apply]
      rw [ih (by omega)]
      rw [Function.iterate_succ_apply']

/-- The full run's carrier coordinate is `tentMap^[L] t`. -/
theorem upTentCascade_run_coord (L : ℕ) (t : ℝ) :
    ((upTentCascade L).run (fun _ => t)) 0 = (tentMap^[L]) t :=
  upTentCascade_runUpTo_coord L t L (le_refl _)

/-- **THE DYADIC IDENTITY (the heart of the witness lower bound).** The `L`-fold tent iterate maps the
dyadic grid point `j / 2^L` to the parity `(j mod 2 : ℝ)`, for `j ≤ 2^L`. Proved by induction on `L`:
one tent fold maps `j / 2^{L+1}` to `num / 2^L` with `num ≤ 2^L` and `num ≡ j (mod 2)`. -/
theorem tentMap_iterate_dyadic :
    ∀ L : ℕ, ∀ j : ℕ, j ≤ 2 ^ L →
      (tentMap^[L]) ((j : ℝ) / 2 ^ L) = ((j % 2 : ℕ) : ℝ) := by
  intro L
  induction L with
  | zero =>
      intro j hj
      -- 2^0 = 1, so j ≤ 1, j ∈ {0,1}; tentMap^[0] = id; j/1 = j = j%2
      simp only [pow_zero, Function.iterate_zero, id_eq] at *
      interval_cases j <;> norm_num
  | succ L ih =>
      intro j hj
      rw [Function.iterate_succ_apply]
      -- compute tentMap (j / 2^{L+1})
      have hpowpos : (0 : ℝ) < 2 ^ (L + 1) := by positivity
      have hpowLpos : (0 : ℝ) < 2 ^ L := by positivity
      set num : ℕ := if j ≤ 2 ^ L then j else 2 ^ (L + 1) - j with hnum
      have hnum_le : num ≤ 2 ^ L := by
        rw [hnum]; split
        · assumption
        · rename_i h; push Not at h
          have : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring
          omega
      have htent : tentMap ((j : ℝ) / 2 ^ (L + 1)) = (num : ℝ) / 2 ^ L := by
        unfold tentMap
        rw [pow_succ]
        -- 2 * (j / (2^L * 2)) - 1 = j/2^L - 1 = (j - 2^L)/2^L
        have hLne : (2 : ℝ) ^ L ≠ 0 := ne_of_gt hpowLpos
        have hrw : 2 * ((j : ℝ) / (2 ^ L * 2)) - 1 = ((j : ℝ) - 2 ^ L) / 2 ^ L := by
          rw [eq_div_iff hLne]; field_simp
        rw [hrw]
        rw [abs_div, abs_of_pos hpowLpos]
        by_cases hcase : j ≤ 2 ^ L
        · rw [hnum, if_pos hcase]
          rw [abs_of_nonpos (by
            have : (j : ℝ) ≤ 2 ^ L := by exact_mod_cast hcase
            linarith)]
          field_simp; ring
        · push Not at hcase
          rw [hnum, if_neg (not_le.mpr hcase)]
          have hjR : (2 : ℝ) ^ L < j := by exact_mod_cast hcase
          rw [abs_of_pos (by linarith)]
          have hcast : ((2 ^ (L + 1) - j : ℕ) : ℝ) = (2 : ℝ) ^ (L + 1) - j := by
            have : j ≤ 2 ^ (L + 1) := hj
            push_cast [Nat.cast_sub this]; ring
          rw [hcast, pow_succ]
          field_simp; ring
      rw [htent, ih num hnum_le]
      -- num % 2 = j % 2
      have hmod : num % 2 = j % 2 := by
        rw [hnum]; split
        · rfl
        · rename_i h
          have hpoweven : 2 ^ (L + 1) % 2 = 0 := by
            rw [pow_succ]; omega
          have : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring
          omega
      rw [hmod]

/-! ### (iii.a) The iterated-tent route and its value on the dyadic grid -/

/-- The iterated-tent route: threshold at `½` on the final coordinate (`route = 0` iff value `≥ ½`),
realized by the same readout scores as the base tent. -/
def upTentRouteScores : Fin 2 → AffineFunctional 1 :=
  fun j => if j = 0 then ⟨fun _ => 1, -(1/2)⟩ else ⟨fun _ => -1, 1/2⟩

theorem upTentRouteScores_eval (s : Fin 1 → ℝ) :
    (upTentRouteScores 0).eval s = s 0 - 1/2 ∧ (upTentRouteScores 1).eval s = 1/2 - s 0 := by
  refine ⟨?_, ?_⟩
  · show (upTentRouteScores 0).eval s = s 0 - 1/2
    have : upTentRouteScores 0 = ⟨fun _ => 1, -(1/2)⟩ := by simp [upTentRouteScores]
    rw [this]; simp [AffineFunctional.eval]; ring
  · show (upTentRouteScores 1).eval s = 1/2 - s 0
    have : upTentRouteScores 1 = ⟨fun _ => -1, 1/2⟩ := by simp [upTentRouteScores]
    rw [this]; simp [AffineFunctional.eval]; ring

/-- The iterated-tent route value: `0` iff the final coordinate `≥ ½`. -/
theorem upTentRoute_eq (L : ℕ) (t : ℝ) :
    cascadeRoute (upTentCascade L) upTentRouteScores (by norm_num) (fun _ => t)
      = if 1/2 ≤ (tentMap^[L]) t then 0 else 1 := by
  unfold cascadeRoute
  rw [leastArgmax_two]
  obtain ⟨h0, h1⟩ := upTentRouteScores_eval ((upTentCascade L).run (fun _ => t))
  simp only [h0, h1]
  rw [upTentCascade_run_coord]
  by_cases hc : (1:ℝ)/2 ≤ (tentMap^[L]) t
  · rw [if_pos (by linarith), if_pos hc]
  · rw [if_neg (by push Not at hc ⊢; linarith), if_neg hc]

/-- **The route value on the dyadic grid point `j / 2^L` is `1 − (j mod 2)`.** Combining
`upTentRoute_eq` with the dyadic identity: the final coordinate is `j mod 2 ∈ {0,1}`, and the
threshold `≥ ½` is met iff that value is `1` (j odd) ⟹ route `0`; else (j even) route `1`. -/
theorem upTentRoute_on_grid (L : ℕ) (j : ℕ) (hj : j ≤ 2 ^ L) :
    cascadeRoute (upTentCascade L) upTentRouteScores (by norm_num) (fun _ => (j : ℝ) / 2 ^ L)
      = if j % 2 = 0 then 1 else 0 := by
  rw [upTentRoute_eq, tentMap_iterate_dyadic L j hj]
  have hmod : j % 2 = 0 ∨ j % 2 = 1 := by omega
  rcases hmod with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

/-! ### (iii.b) The dyadic sample and the route alternation lower bound `= 2^L` -/

/-- The increasing dyadic sample of `2^L + 1` points `k ↦ k / 2^L`, `k = 0 … 2^L`. -/
def dyadicGrid (L : ℕ) : Fin (2 ^ L + 1) → ℝ := fun k => (k.val : ℝ) / 2 ^ L

theorem dyadicGrid_increasing (L : ℕ) : Increasing (dyadicGrid L) := by
  intro i j hij
  unfold dyadicGrid
  have hpow : (0 : ℝ) < 2 ^ L := by positivity
  have hlt : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast (Fin.lt_def.mp hij)
  exact div_lt_div_of_pos_right hlt hpow

/-- The iterated-tent route along the dyadic grid, as a function of the grid index `k`. -/
theorem upTentRoute_dyadicGrid (L : ℕ) (k : Fin (2 ^ L + 1)) :
    cascadeRoute (upTentCascade L) upTentRouteScores (by norm_num) (fun _ => dyadicGrid L k)
      = if k.val % 2 = 0 then 1 else 0 := by
  unfold dyadicGrid
  exact upTentRoute_on_grid L k.val (by have := k.isLt; omega)

/-- **THE WITNESS ALTERNATION LOWER BOUND `= 2^L`.** The depth-`L` iterated-tent route changes value at
EVERY one of the `2^L` adjacent pairs of the dyadic grid (consecutive grid indices have opposite
parity, so the route flips every step). Hence `seqChanges = 2^L`. -/
theorem upTentRoute_alternations_eq (L : ℕ) :
    seqChanges (fun k => cascadeRoute (upTentCascade L) upTentRouteScores (by norm_num)
        (fun _ => dyadicGrid L k)) = 2 ^ L := by
  unfold seqChanges
  -- every adjacent pair is a change
  have hall : (Finset.univ.filter (fun i : Fin (2 ^ L) =>
      (fun k => cascadeRoute (upTentCascade L) upTentRouteScores (by norm_num)
        (fun _ => dyadicGrid L k)) i.castSucc
      ≠ (fun k => cascadeRoute (upTentCascade L) upTentRouteScores (by norm_num)
        (fun _ => dyadicGrid L k)) i.succ)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    simp only
    rw [upTentRoute_dyadicGrid, upTentRoute_dyadicGrid]
    -- i.castSucc.val = i.val, i.succ.val = i.val + 1 : opposite parity
    have hcs : (i.castSucc : Fin (2 ^ L + 1)).val = i.val := Fin.val_castSucc i
    have hsc : (i.succ : Fin (2 ^ L + 1)).val = i.val + 1 := Fin.val_succ i
    rw [hcs, hsc]
    rcases Nat.even_or_odd i.val with he | ho
    · obtain ⟨r, hr⟩ := he
      rw [if_pos (by omega), if_neg (by omega)]
      decide
    · obtain ⟨r, hr⟩ := ho
      rw [if_neg (by omega), if_pos (by omega)]
      decide
  rw [hall, Finset.card_univ, Fintype.card_fin]

/-! ## (iv) THE `∀L` SEPARATION: `binGrade 1 2 L ⊂ binGrade 1 2 (L+1)` for ALL `L` -/

/-- The depth-`(L+1)` iterated-tent route, packaged as a route function. It lies in
`binCascadeGrade 1 2 (L+1)` by construction. -/
def upTentRoute (L : ℕ) : (Fin 1 → ℝ) → Fin 2 :=
  cascadeRoute (upTentCascade L) upTentRouteScores (by norm_num)

theorem upTentRoute_mem_grade (L : ℕ) :
    upTentRoute L ∈ binCascadeGrade 1 2 L (by norm_num) :=
  ⟨fun _ => upTentLayer, upTentRouteScores, rfl⟩

/-- **NON-MEMBERSHIP (a REAL `∀L` proved non-membership).** The depth-`(L+1)` iterated-tent route is
NOT in `binCascadeGrade 1 2 L`. If it were a depth-`L` arity-2 route, then on the increasing dyadic
grid `dyadicGrid (L+1)` it would change `≤ 2^{L+1} − 1` times (`binRoute_alternations_le`); but it
changes `2^{L+1}` times (`upTentRoute_alternations_eq`) — a contradiction. -/
theorem upTentRoute_not_mem_grade (L : ℕ) :
    upTentRoute (L + 1) ∉ binCascadeGrade 1 2 L (by norm_num) := by
  rintro ⟨layers, rs, hf⟩
  -- the witness alternation count along the (L+1)-grid
  have hwit : seqChanges (fun k => upTentRoute (L + 1) (fun _ => dyadicGrid (L + 1) k)) = 2 ^ (L + 1) :=
    upTentRoute_alternations_eq (L + 1)
  -- but as a depth-L route it has ≤ 2^{L+1} − 1 alternations
  have hbound : seqChanges (fun k => upTentRoute (L + 1) (fun _ => dyadicGrid (L + 1) k))
      ≤ 2 ^ (L + 1) - 1 := by
    have hrw : (fun k => upTentRoute (L + 1) (fun _ => dyadicGrid (L + 1) k))
        = fun k => cascadeRoute (binCascade layers) rs (by norm_num)
            (fun _ => dyadicGrid (L + 1) k) := by
      funext k; rw [hf]
    rw [hrw]
    exact binRoute_alternations_le layers rs (dyadicGrid (L + 1)) (dyadicGrid_increasing (L + 1))
  rw [hwit] at hbound
  have hpow : 1 ≤ 2 ^ (L + 1) := Nat.one_le_two_pow
  omega

/-- **THE `∀L` DEPTH-LADDER SEPARATION.** For every `L`,
`binCascadeGrade 1 2 L ⊂ binCascadeGrade 1 2 (L+1)`. The `⊆` is the depth-monotone identity-layer
embedding (`binCascadeGrade_succ_subset`); the strictness is the iterated-tent witness: the depth-`(L+1)`
tent route lies in grade `(L+1)` (`upTentRoute_mem_grade`) but NOT in grade `L`
(`upTentRoute_not_mem_grade`, via the `∀L` route-alternation bound `binRoute_alternations_le`). Depth
genuinely buys expressivity at EVERY rung — the uniform fixed-width depth hierarchy. -/
theorem binCascadeGrade_ssubset_succ (L : ℕ) :
    binCascadeGrade 1 2 L (by norm_num) ⊂ binCascadeGrade 1 2 (L + 1) (by norm_num) := by
  refine ⟨binCascadeGrade_succ_subset (by norm_num), ?_⟩
  intro hsubset
  have hmem : upTentRoute (L + 1) ∈ binCascadeGrade 1 2 (L + 1) (by norm_num) :=
    upTentRoute_mem_grade (L + 1)
  have h1 : upTentRoute (L + 1) ∈ binCascadeGrade 1 2 L (by norm_num) := hsubset hmem
  exact upTentRoute_not_mem_grade L h1

end TLT.TemperedDesignLaw.MuxHierarchy
