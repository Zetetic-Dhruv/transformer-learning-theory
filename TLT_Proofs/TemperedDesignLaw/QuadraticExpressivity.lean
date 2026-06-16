/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MuxDepthLadderGeneral
import Mathlib.Analysis.Convex.Basic

/-!
# Quadratic (low-rank bilinear / self-attention) scores: convexity refuted, region count survives

True self-attention scores are **low-rank bilinear**: `score(x) = ⟨Q x, K x⟩ = xᵀ(QᵀK)x`, a
*quadratic* form in `x`.  This file re-examines the two affine results of the tempered design law
under this added quadratic constraint, and proves both directions.

## The power-diagram characterization fails for quadratic scores (`quadraticArgmaxCell_not_convex`)

For affine scores the least-argmax cell `{x | leastArgmax (score · x) = i}` is convex
(`argmaxCell_convex`, `ArgmaxPowerDiagram.lean`).  For quadratic scores it need not be: with
`score 0 = 0` and `score 1 (x) = x₀² − x₁²` (a rank-2 bilinear / self-attention form), the
winner-`0` cell contains `{x | x₀² ≤ x₁²}`, which is **not convex**: `(1,1)` and `(1,−1)` lie in
it but their midpoint `(1,0)` does not.  This is a real proved `¬ Convex` (three explicit points).

## The finite region count survives for quadratic scores (`quadArg_alternations_le`)

The one-variable analogue.  For `n` parabolas `val i t = A i·t² + a i·t + c i`, the active index
`arg t = leastArgmax (val · t)` changes only finitely often along any increasing sample.  Where the
affine bound is `n − 1` (each pair crosses ≤ 1 time, order-1), the quadratic bound is the
**Davenport–Schinzel order-2** crude pairwise bound: each pairwise difference is a one-variable
quadratic, *convex or concave*, so each of its (weak/strict) sign predicates changes ≤ 2 times along
an increasing sample (its `≤`/`<` sublevel set is an interval (`OrdConnected`) by convexity), and
the active index changes only when some pair's comparison changes.  Summing over the `≤ n²` ordered
comparisons gives a finite bound `2 · (2 n²) = 4 n²`.  Finiteness is the point: the region count is
preserved.

The analytic atom is `quad_le_set_ordConnected` (a convex quadratic's sublevel set is an interval),
proved from the convexity-of-the-square inequality, exactly mirroring the affine `diff_interp`
calculus in `MuxDepthLadderGeneral.lean`.
-/

open scoped BigOperators
open Set

noncomputable section

namespace TLT.TemperedDesignLaw

open TLT.TemperedDesignLaw.MuxHierarchy

/-! ## A2: a quadratic argmax cell that is NOT convex -/

/-- A self-contained **quadratic score** on `Fin d`: a matrix part `M`, a linear part `a`, and a
constant `b`.  `eval x = (∑ i j, M i j · x i · x j) + (∑ i, a i · x i) + b`.  The matrix part is a
genuine (possibly low-rank) bilinear form, which is exactly what a self-attention score
`⟨Q x, K x⟩ = xᵀ(QᵀK)x` is. -/
structure QuadScore (d : ℕ) where
  M : Fin d → Fin d → ℝ
  a : Fin d → ℝ
  b : ℝ

/-- Evaluation of a quadratic score at a point `x : Fin d → ℝ`. -/
def QuadScore.eval {d : ℕ} (s : QuadScore d) (x : Fin d → ℝ) : ℝ :=
  (∑ i, ∑ j, s.M i j * x i * x j) + (∑ i, s.a i * x i) + s.b

/-- The all-zero quadratic score (`M = a = 0`, `b = 0`): `eval x = 0`. -/
def QuadScore.zero (d : ℕ) : QuadScore d := ⟨fun _ _ => 0, fun _ => 0, 0⟩

@[simp] theorem QuadScore.zero_eval {d : ℕ} (x : Fin d → ℝ) : (QuadScore.zero d).eval x = 0 := by
  simp [QuadScore.eval, QuadScore.zero]

/-- The diagonal rank-2 bilinear score `diff x = x₀² − x₁²` (`M = diag(1,−1)`, `a = 0`, `b = 0`).
This is a self-attention form `xᵀ(QᵀK)x`. -/
def QuadScore.diffScore : QuadScore 2 :=
  ⟨fun i j => if i = j then (if i = 0 then 1 else -1) else 0, fun _ => 0, 0⟩

theorem QuadScore.diffScore_eval (x : Fin 2 → ℝ) :
    QuadScore.diffScore.eval x = (x 0)^2 - (x 1)^2 := by
  simp only [QuadScore.eval, QuadScore.diffScore, Fin.sum_univ_two]
  norm_num
  ring

/-- **The power-diagram (convexity) characterization fails for quadratic / self-attention
scores.**  There are two quadratic scores `score 0 = 0`, `score 1 (x) = x₀² − x₁²` on `Fin 2` and an
index `i = 0` whose least-argmax cell is **not convex**: `(1,1)` and `(1,−1)` are in the cell (there
`x₀² ≤ x₁²`, so the all-zero score `0` weakly wins and least-index `0` is selected), but the midpoint
`(1,0)` is not (`1 ≤ 0` is false, so score `1` strictly wins). -/
theorem quadraticArgmaxCell_not_convex :
    ∃ (scores : Fin 2 → QuadScore 2) (hk : 0 < 2) (i : Fin 2),
      ¬ Convex ℝ {x : Fin 2 → ℝ | leastArgmax (fun j => (scores j).eval x) hk = i} := by
  classical
  refine ⟨![QuadScore.zero 2, QuadScore.diffScore], by norm_num, 0, ?_⟩
  -- the cell membership criterion: `x` is in the cell iff `x₀² − x₁² ≤ 0`.
  have hmem : ∀ x : Fin 2 → ℝ,
      leastArgmax (fun j => (![QuadScore.zero 2, QuadScore.diffScore] j).eval x) (by norm_num) = 0
        ↔ (x 0)^2 - (x 1)^2 ≤ 0 := by
    intro x
    have hval0 : (![QuadScore.zero 2, QuadScore.diffScore] 0).eval x = 0 := by
      simp
    have hval1 : (![QuadScore.zero 2, QuadScore.diffScore] 1).eval x = (x 0)^2 - (x 1)^2 := by
      simp [QuadScore.diffScore_eval]
    constructor
    · intro h
      -- `0` is the least argmax, so it weakly beats index `1`: `val 1 ≤ val 0 = 0`.
      have hmax := leastArgmax_is_maximizer (fun j => (![QuadScore.zero 2, QuadScore.diffScore] j).eval x)
        (by norm_num) 1
      rw [h] at hmax
      rw [hval0, hval1] at hmax
      linarith
    · intro h
      -- `val 1 ≤ 0 = val 0`, so `0` weakly beats all; and `0` is the least index, so it wins.
      have hspec : isLeastArgmax (fun j => (![QuadScore.zero 2, QuadScore.diffScore] j).eval x) 0 := by
        refine ⟨?_, ?_⟩
        · rw [Fin.forall_fin_two]
          refine ⟨?_, ?_⟩
          · simp only; rw [hval0]
          · simp only; rw [hval0, hval1]; linarith
        · intro j hj
          exact absurd hj (by simp)
      exact isLeastArgmax_unique _ _ _
        (leastArgmax_spec (fun j => (![QuadScore.zero 2, QuadScore.diffScore] j).eval x) (by norm_num))
        hspec
  -- now disprove convexity via three explicit points.
  intro hconv
  -- the two in-points `p = (1,1)`, `q = (1,-1)`, midpoint `(1,0)`.
  set p : Fin 2 → ℝ := ![1, 1] with hp
  set q : Fin 2 → ℝ := ![1, -1] with hq
  have hpmem : p ∈ {x : Fin 2 → ℝ |
      leastArgmax (fun j => (![QuadScore.zero 2, QuadScore.diffScore] j).eval x) (by norm_num) = 0} := by
    simp only [Set.mem_setOf_eq, hmem]; norm_num [hp]
  have hqmem : q ∈ {x : Fin 2 → ℝ |
      leastArgmax (fun j => (![QuadScore.zero 2, QuadScore.diffScore] j).eval x) (by norm_num) = 0} := by
    simp only [Set.mem_setOf_eq, hmem]; norm_num [hq]
  -- the midpoint with coefficients `1/2, 1/2`.
  have hmid := (convex_iff_add_mem.mp hconv) hpmem hqmem
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  rw [Set.mem_setOf_eq, hmem] at hmid
  -- the midpoint is `(1, 0)`: `1² − 0² = 1 ≤ 0` is false.
  have hmidpt : ((1:ℝ)/2) • p + ((1:ℝ)/2) • q = ![1, 0] := by
    funext k; fin_cases k <;> · simp only [hp, hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; norm_num
  rw [hmidpt] at hmid
  norm_num at hmid

/-! ## A1: the finite alternation bound for quadratic argmax (the region count survives)

We package `n` parabolas as `QuadLines n` and prove a crude finite bound on the number of changes
of the active index along any increasing sample.  The machinery (`seqChanges`, `Increasing`,
`SeqNoReturn`, `seqChanges_pair_le`) is reused from `MuxDepthLadderGeneral.lean`.
-/

/-- A finite family of `n` one-variable parabolas `val i t = A i · t² + a i · t + c i`. -/
structure QuadLines (n : ℕ) where
  A : Fin n → ℝ
  a : Fin n → ℝ
  c : Fin n → ℝ

/-- The value of parabola `i` at the real point `t`. -/
def QuadLines.val {n : ℕ} (g : QuadLines n) (i : Fin n) (t : ℝ) : ℝ :=
  g.A i * t^2 + g.a i * t + g.c i

/-- The active (least-argmax) index of the family at `t`. -/
def QuadLines.arg {n : ℕ} (g : QuadLines n) (hn : 0 < n) (t : ℝ) : Fin n :=
  leastArgmax (fun i => g.val i t) hn

/-! ### (A1.0) The analytic atom: a convex quadratic's sublevel set is an interval -/

/-- Convexity-of-the-square: for `z = (1−θ)x + θy`, `0 ≤ θ ≤ 1`, `z² ≤ (1−θ)x² + θy²`. -/
theorem sq_convex_comb (x y θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ((1 - θ) * x + θ * y)^2 ≤ (1 - θ) * x^2 + θ * y^2 := by
  nlinarith [mul_nonneg (mul_nonneg h0 (by linarith : (0:ℝ) ≤ 1 - θ)) (sq_nonneg (x - y))]

/-- A quadratic `A t² + B t + C` with `A ≥ 0` (convex) lies below the chord. -/
theorem quad_convex_le (A B C : ℝ) (hA : 0 ≤ A) (x y θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    A * ((1 - θ) * x + θ * y)^2 + B * ((1 - θ) * x + θ * y) + C
      ≤ (1 - θ) * (A * x^2 + B * x + C) + θ * (A * y^2 + B * y + C) := by
  have hAsq : A * ((1 - θ) * x + θ * y)^2 ≤ A * ((1 - θ) * x^2 + θ * y^2) :=
    mul_le_mul_of_nonneg_left (sq_convex_comb x y θ h0 h1) hA
  nlinarith [hAsq]

/-- Interpolation point: any `z ∈ [x,y]` is `(1−θ)x + θy` for some `0 ≤ θ ≤ 1`. -/
theorem interp_exists {x y z : ℝ} (hxz : x ≤ z) (hzy : z ≤ y) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ z = (1 - θ) * x + θ * y := by
  rcases eq_or_lt_of_le (le_trans hxz hzy) with hxy | hxy
  · exact ⟨0, le_refl _, by norm_num, by
      have : z = x := le_antisymm (hxy ▸ hzy) hxz; rw [this]; ring⟩
  · have hpos : 0 < y - x := by linarith
    refine ⟨(z - x) / (y - x), div_nonneg (by linarith) (le_of_lt hpos),
      by rw [div_le_one hpos]; linarith, ?_⟩
    field_simp
    ring

/-- **THE ANALYTIC ATOM.** For a *convex* quadratic (`A ≥ 0`), the (weak) sublevel set
`{t | A t² + B t + C ≤ 0}` is `OrdConnected` (an interval). -/
theorem quad_le_set_ordConnected (A B C : ℝ) (hA : 0 ≤ A) :
    OrdConnected {t : ℝ | A * t^2 + B * t + C ≤ 0} := by
  rw [ordConnected_def]
  intro x hx y hy z hz
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  obtain ⟨hxz, hzy⟩ := hz
  obtain ⟨θ, h0, h1, hzeq⟩ := interp_exists hxz hzy
  have hchord := quad_convex_le A B C hA x y θ h0 h1
  rw [← hzeq] at hchord
  nlinarith [mul_nonneg h0 (le_of_lt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_refl 1))),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - θ) (neg_nonneg.mpr hx),
    mul_nonneg h0 (neg_nonneg.mpr hy)]

/-- The strict version: for a convex quadratic, `{t | A t² + B t + C < 0}` is `OrdConnected`. -/
theorem quad_lt_set_ordConnected (A B C : ℝ) (hA : 0 ≤ A) :
    OrdConnected {t : ℝ | A * t^2 + B * t + C < 0} := by
  rw [ordConnected_def]
  intro x hx y hy z hz
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  obtain ⟨hxz, hzy⟩ := hz
  obtain ⟨θ, h0, h1, hzeq⟩ := interp_exists hxz hzy
  have hchord := quad_convex_le A B C hA x y θ h0 h1
  rw [← hzeq] at hchord
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - θ) (le_of_lt (neg_pos.mpr hx)),
    mul_nonneg h0 (le_of_lt (neg_pos.mpr hy))]

/-! ### (A1.1) Combinatorial bridges on `seqChanges` -/

/-- **A `Fin 2`-valued sequence whose `c`-fiber is no-return changes ≤ 2 times.**  If, for the value
`c`, the positions with `b k = c` form a contiguous block (a value once left, going up, never
recurs), then `b` changes at most twice (it enters the block once and exits once).  We only need that
the codomain has *two* values, so the non-`c` value is unique. -/
theorem seqChanges_fin2_block_le {m : ℕ} (b : Fin (m + 1) → Fin 2) (c : Fin 2)
    (hnr : ∀ p r s : Fin (m + 1), p ≤ s → s ≤ r → b p = c → b r = c → b s = c) :
    seqChanges b ≤ 2 := by
  classical
  unfold seqChanges
  -- classify each change index by whether it ENTERS the c-block (b succ = c) or EXITS (b cs = c).
  set S : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => b i.castSucc ≠ b i.succ) with hS
  set enter : Finset (Fin m) := S.filter (fun i => b i.succ = c) with hEnter
  set exit : Finset (Fin m) := S.filter (fun i => b i.castSucc = c) with hExit
  -- every change index is an enter or an exit (since b is 2-valued: a change moves to/from c).
  have hSsub : S ⊆ enter ∪ exit := by
    intro i hi
    have hch : b i.castSucc ≠ b i.succ := (Finset.mem_filter.mp hi).2
    simp only [hEnter, hExit, Finset.mem_union, Finset.mem_filter]
    -- one of the two endpoints is c (else both equal the unique non-c value, contradicting hch).
    by_cases hcs : b i.castSucc = c
    · exact Or.inr ⟨hi, hcs⟩
    · -- b i.castSucc ≠ c ⟹ b i.castSucc is the other value; if b i.succ ≠ c too they'd be equal.
      refine Or.inl ⟨hi, ?_⟩
      by_contra hsucc
      apply hch
      -- both ≠ c in Fin 2 ⟹ both equal the unique other element ⟹ equal.
      have hval : ∀ x : Fin 2, x ≠ c → x.val ≠ c.val := fun x hx => fun h => hx (Fin.ext h)
      apply Fin.ext
      have := hval _ hcs
      have := hval _ hsucc
      have l1 : (b i.castSucc).val < 2 := (b i.castSucc).isLt
      have l2 : (b i.succ).val < 2 := (b i.succ).isLt
      have l3 : c.val < 2 := c.isLt
      omega
  -- at most one enter
  have henter_le : enter.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi i' hi'
    simp only [hEnter, Finset.mem_filter, hS] at hi hi'
    obtain ⟨⟨_, hich⟩, hic⟩ := hi
    obtain ⟨⟨_, hi'ch⟩, hi'c⟩ := hi'
    by_contra hne
    -- WLOG i < i'.  b i.succ = c, b i'.succ = c, but b i'.castSucc ≠ b i'.succ = c.
    -- no-return on [i.succ, i'.succ] forces b i'.castSucc = c, contradiction.
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have ho1 : (i.succ : Fin (m+1)) ≤ i'.castSucc := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc, Fin.lt_def] at hlt ⊢; omega
      have ho2 : (i'.castSucc : Fin (m+1)) ≤ i'.succ := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
      have := hnr i.succ i'.succ i'.castSucc ho1 ho2 hic hi'c
      exact hi'ch (this.trans hi'c.symm)
    · have ho1 : (i'.succ : Fin (m+1)) ≤ i.castSucc := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc, Fin.lt_def] at hlt ⊢; omega
      have ho2 : (i.castSucc : Fin (m+1)) ≤ i.succ := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
      have := hnr i'.succ i.succ i.castSucc ho1 ho2 hi'c hic
      exact hich (this.trans hic.symm)
  -- at most one exit (symmetric: an exit index has b castSucc = c)
  have hexit_le : exit.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi i' hi'
    simp only [hExit, Finset.mem_filter, hS] at hi hi'
    obtain ⟨⟨_, hich⟩, hic⟩ := hi
    obtain ⟨⟨_, hi'ch⟩, hi'c⟩ := hi'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · -- i < i'.  b i.castSucc = c, b i'.castSucc = c; no-return on [i.castSucc, i'.castSucc]
      -- forces b i.succ = c, but b i.castSucc ≠ b i.succ, contradiction.
      have ho1 : (i.castSucc : Fin (m+1)) ≤ i.succ := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
      have ho2 : (i.succ : Fin (m+1)) ≤ i'.castSucc := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc, Fin.lt_def] at hlt ⊢; omega
      have := hnr i.castSucc i'.castSucc i.succ ho1 ho2 hic hi'c
      exact hich (hic.trans this.symm)
    · have ho1 : (i'.castSucc : Fin (m+1)) ≤ i'.succ := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
      have ho2 : (i'.succ : Fin (m+1)) ≤ i.castSucc := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc, Fin.lt_def] at hlt ⊢; omega
      have := hnr i'.castSucc i.castSucc i'.succ ho1 ho2 hi'c hic
      exact hi'ch (hi'c.trans this.symm)
  calc S.card ≤ (enter ∪ exit).card := Finset.card_le_card hSsub
    _ ≤ enter.card + exit.card := Finset.card_union_le _ _
    _ ≤ 2 := by omega

/-- **The component-sum bound.** A sequence into a finite product changes at most the sum of its
component change-counts.  (Generalizes `seqChanges_pair_le` from a binary to an arbitrary finite
product.) -/
theorem seqChanges_pi_le {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ a, DecidableEq (β a)] {m : ℕ} (s : Fin (m + 1) → ∀ a, β a) :
    seqChanges s ≤ ∑ a : ι, seqChanges (fun k => s k a) := by
  classical
  unfold seqChanges
  -- change-set of s ⊆ ⋃ a, change-set of component a.
  have hsub : (Finset.univ.filter (fun i : Fin m => s i.castSucc ≠ s i.succ))
      ⊆ Finset.univ.biUnion
          (fun a : ι => Finset.univ.filter (fun i : Fin m => s i.castSucc a ≠ s i.succ a)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    by_contra hcon
    push Not at hcon
    exact hi (funext fun a => hcon a)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ a : ι, (Finset.univ.filter (fun i : Fin m => s i.castSucc a ≠ s i.succ a)).card :=
          Finset.card_biUnion_le
    _ = _ := rfl

/-! ### (A1.2) The per-pair bound: a quadratic comparison changes ≤ 2 times -/

/-- Monotonicity of an increasing sample. -/
theorem increasing_mono {m : ℕ} {pts : Fin (m + 1) → ℝ} (hinc : Increasing pts)
    {i j : Fin (m + 1)} (hij : i ≤ j) : pts i ≤ pts j := by
  rcases eq_or_lt_of_le hij with h | h
  · rw [h]
  · exact le_of_lt (hinc i j h)

open Classical in
/-- **A two-valued sequence whose `vIn`-fiber is the preimage of an `OrdConnected` set under an
increasing sample changes ≤ 2 times.**  The fiber over `vIn` (positions in `U`) is no-return because
`U` is an interval and the sample is monotone, so `seqChanges_fin2_block_le` applies. -/
theorem seqChanges_ordConnected_indicator_le {m : ℕ} {pts : Fin (m + 1) → ℝ}
    (hinc : Increasing pts) {U : Set ℝ} (hU : OrdConnected U) (vIn vOut : Fin 2)
    (hv : vIn ≠ vOut) :
    seqChanges (fun k => if pts k ∈ U then vIn else vOut) ≤ 2 := by
  apply seqChanges_fin2_block_le _ vIn
  intro p r s hps hsr hp hr
  -- hp, hr : indicator = vIn at p, r ⟹ pts p, pts r ∈ U ⟹ (interval) pts s ∈ U ⟹ indicator = vIn.
  have hpU : pts p ∈ U := by by_contra h; rw [if_neg h] at hp; exact hv hp.symm
  have hrU : pts r ∈ U := by by_contra h; rw [if_neg h] at hr; exact hv hr.symm
  have hsU : pts s ∈ U := by
    rw [ordConnected_def] at hU
    exact hU hpU hrU ⟨increasing_mono hinc hps, increasing_mono hinc hsr⟩
  rw [if_pos hsU]

open Classical in
/-- **THE PER-PAIR ORDER-2 BOUND.** Along any increasing sample, the strict comparison
`val i < val j` of two parabolas changes value at most **2** times.  Reason: the difference
`D = val j − val i` is a one-variable quadratic; it is convex or concave, so one of the two sublevel
sets `{D < 0}` / `{D ≤ 0}` (equivalently `{0 < D}`) is an interval (`OrdConnected`), so the
comparison's `false`- or `true`-fiber is a contiguous block, capping changes at 2. -/
theorem QuadLines.pair_comparison_le {n : ℕ} (g : QuadLines n) (i j : Fin n) {m : ℕ}
    (pts : Fin (m + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => if g.val i (pts k) < g.val j (pts k) then (1 : Fin 2) else 0) ≤ 2 := by
  -- D t = val j t − val i t = (A j − A i) t² + (a j − a i) t + (c j − c i).
  set AD := g.A j - g.A i with hAD
  set BD := g.a j - g.a i with hBD
  set CD := g.c j - g.c i with hCD
  have hDexp : ∀ t, g.val j t - g.val i t = AD * t^2 + BD * t + CD := by
    intro t; simp only [QuadLines.val, hAD, hBD, hCD]; ring
  have hcmp : ∀ t, (g.val i t < g.val j t) ↔ (0 < AD * t^2 + BD * t + CD) := by
    intro t; rw [← hDexp]; constructor <;> intro h <;> linarith
  rcases le_total 0 AD with hpos | hneg
  · -- D convex: {t | D t ≤ 0} is OrdConnected.  The comparison's `true`-value (0) sits OUTSIDE this
    -- set (where 0 < D), so feed the indicator with `vIn = 0` inside `{D ≤ 0}` and `vOut = 1`.
    have hoc : OrdConnected {t : ℝ | AD * t^2 + BD * t + CD ≤ 0} :=
      quad_le_set_ordConnected AD BD CD hpos
    have hind := seqChanges_ordConnected_indicator_le hinc hoc (0 : Fin 2) 1 (by decide)
    have hcongr : (fun k => if g.val i (pts k) < g.val j (pts k) then (1 : Fin 2) else 0)
        = (fun k => if pts k ∈ {t : ℝ | AD * t^2 + BD * t + CD ≤ 0} then (0 : Fin 2) else 1) := by
      funext k
      simp only [Set.mem_setOf_eq, hcmp]
      by_cases h : 0 < AD * (pts k)^2 + BD * (pts k) + CD
      · rw [if_pos h, if_neg (by linarith)]
      · rw [if_neg h, if_pos (by linarith)]
    rw [hcongr]; exact hind
  · -- D concave: -D is convex with leading coeff -AD ≥ 0, so {t | -D t < 0} = {t | 0 < D t} is
    -- OrdConnected.  The comparison's `true`-value (1) sits INSIDE this set; feed `vIn = 1`.
    have hoc : OrdConnected {t : ℝ | (-AD) * t^2 + (-BD) * t + (-CD) < 0} :=
      quad_lt_set_ordConnected (-AD) (-BD) (-CD) (by linarith)
    have hind := seqChanges_ordConnected_indicator_le hinc hoc (1 : Fin 2) 0 (by decide)
    have hcongr : (fun k => if g.val i (pts k) < g.val j (pts k) then (1 : Fin 2) else 0)
        = (fun k => if pts k ∈ {t : ℝ | (-AD) * t^2 + (-BD) * t + (-CD) < 0} then (1 : Fin 2) else 0) := by
      funext k
      simp only [Set.mem_setOf_eq, hcmp]
      by_cases h : 0 < AD * (pts k)^2 + BD * (pts k) + CD
      · rw [if_pos h, if_pos (by linarith)]
      · rw [if_neg h, if_neg (by linarith)]
    rw [hcongr]; exact hind

/-! ### (A1.3) Assembly: the active index is a function of the strict-comparison profile -/

/-- **The least-argmax depends only on the strict order profile.**  If two value vectors `v, w` induce
the same strict comparisons (`v p < v q ↔ w p < w q` for all `p, q`), they have the same least-argmax.
For reals `≤` is `¬ (>)`, so both the maximizer condition and the least-index condition are
determined by the strict profile. -/
theorem leastArgmax_eq_of_strictProfile {k : ℕ} (v w : Fin k → ℝ) (hk : 0 < k)
    (h : ∀ p q : Fin k, (v p < v q ↔ w p < w q)) :
    leastArgmax v hk = leastArgmax w hk := by
  refine isLeastArgmax_unique w (leastArgmax v hk) (leastArgmax w hk) ?_ (leastArgmax_spec w hk)
  -- show `leastArgmax v hk` is the least-argmax of `w`.
  obtain ⟨hmax, hlt⟩ := leastArgmax_spec v hk
  refine ⟨?_, ?_⟩
  · intro j
    -- w j ≤ w (lv) ⟺ ¬ (w (lv) < w j) ⟺ ¬ (v (lv) < v j) ⟸ v j ≤ v (lv).
    by_contra hcon
    push Not at hcon
    rw [← h] at hcon
    exact absurd (hmax j) (not_le.mpr hcon)
  · intro j hj
    rw [← h]; exact hlt j hj

open Classical in
/-- The strict-comparison **profile** of the family at a point: for every ordered pair `(p,q)`, a bit
saying whether `val p < val q`. -/
def QuadLines.profile {n : ℕ} (g : QuadLines n) (t : ℝ) : Fin n × Fin n → Fin 2 :=
  fun pq => if g.val pq.1 t < g.val pq.2 t then 1 else 0

open Classical in
/-- The active index is a function of the profile: equal profiles ⟹ equal active index. -/
theorem QuadLines.arg_eq_of_profile_eq {n : ℕ} (g : QuadLines n) (hn : 0 < n) {s s' : ℝ}
    (h : g.profile s = g.profile s') : g.arg hn s = g.arg hn s' := by
  apply leastArgmax_eq_of_strictProfile
  intro p q
  have hpq := congrFun h (p, q)
  simp only [QuadLines.profile] at hpq
  by_cases hs : g.val p s < g.val q s
  · rw [if_pos hs] at hpq
    by_cases hs' : g.val p s' < g.val q s'
    · exact ⟨fun _ => hs', fun _ => hs⟩
    · rw [if_neg hs'] at hpq; exact absurd hpq.symm (by decide)
  · rw [if_neg hs] at hpq
    by_cases hs' : g.val p s' < g.val q s'
    · rw [if_pos hs'] at hpq; exact absurd hpq (by decide)
    · exact ⟨fun h => absurd h hs, fun h => absurd h hs'⟩

/-! ### (A1.4) THE PRIMARY DELIVERABLE: the finite alternation bound for quadratic argmax -/

open Classical in
/-- **The finite alternation bound (the region count survives).**  For `n ≥ 1` parabolas
`val i t = A i·t² + a i·t + c i` and ANY strictly-increasing sample `pts : Fin (m+1) → ℝ`, the active
index `arg = leastArgmax (val · ·)` changes value at most `2 · n²` times.  This is the
Davenport–Schinzel **order-2** analogue of the affine order-1 bound `n − 1`
(`affineArg_alternations_le`): each of the `n²` ordered pairwise comparisons is the sign of a
one-variable quadratic, which (being convex or concave) flips ≤ 2 times along an increasing sample
(`QuadLines.pair_comparison_le`); the active index is a function of the comparison profile
(`arg_eq_of_profile_eq`), so it changes only when some comparison does, and summing the per-pair
bound over all `n²` ordered pairs gives `2 · n²`.  A crude finite bound; finiteness is the point. -/
theorem quadArg_alternations_le {n : ℕ} (g : QuadLines n) (hn : 0 < n) {m : ℕ}
    (pts : Fin (m + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => g.arg hn (pts k)) ≤ 2 * n^2 := by
  -- (1) arg-changes ≤ profile-changes (arg is a function of the profile).
  have hstep1 : seqChanges (fun k => g.arg hn (pts k))
      ≤ seqChanges (fun k => g.profile (pts k)) := by
    unfold seqChanges
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro hcon
    exact hi (g.arg_eq_of_profile_eq hn hcon)
  -- (2) profile-changes ≤ Σ over ordered pairs of per-pair comparison-changes.
  have hstep2 : seqChanges (fun k => g.profile (pts k))
      ≤ ∑ pq : Fin n × Fin n,
          seqChanges (fun k => (g.profile (pts k)) pq) :=
    seqChanges_pi_le (fun k => g.profile (pts k))
  -- (3) each per-pair comparison changes ≤ 2.
  have hstep3 : ∀ pq : Fin n × Fin n,
      seqChanges (fun k => (g.profile (pts k)) pq) ≤ 2 := by
    intro pq
    have := g.pair_comparison_le pq.1 pq.2 pts hinc
    -- `(g.profile (pts k)) pq` unfolds to the per-pair indicator.
    convert this using 2
  -- combine.
  calc seqChanges (fun k => g.arg hn (pts k))
      ≤ seqChanges (fun k => g.profile (pts k)) := hstep1
    _ ≤ ∑ pq : Fin n × Fin n, seqChanges (fun k => (g.profile (pts k)) pq) := hstep2
    _ ≤ ∑ _pq : Fin n × Fin n, 2 := Finset.sum_le_sum (fun pq _ => hstep3 pq)
    _ = 2 * n^2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          smul_eq_mul]
        ring

/-! ### (A1.5) A depth-1 width separation (arity 2 ∉ arity 1)

The crude bound `2 n²` is not tight, so it cannot itself power a width separation.  But the
*qualitative* order-2 phenomenon already separates the smallest widths: at arity `1` the active index
is constant (`seqChanges = 0`), whereas at arity `2` two parabolas that cross **twice** make the
active index alternate `0,1,0` (`seqChanges = 2`).  Since two crossings is exactly what an order-2
(quadratic) comparison permits and an order-1 (affine) one forbids, this is the
quadratic-specific width increment, realized concretely below.
-/

/-- At arity `1` the active index is always `0`, so it never changes: `seqChanges = 0`.  This is the
arity-1 alternation ceiling that the arity-2 witness will exceed. -/
theorem quadArg_arity_one_no_alternation (g : QuadLines 1) {m : ℕ} (pts : Fin (m + 1) → ℝ) :
    seqChanges (fun k => g.arg (by norm_num) (pts k)) = 0 := by
  have hconst : ∀ k, g.arg (by norm_num) (pts k) = 0 := by
    intro k; exact Subsingleton.elim _ _
  unfold seqChanges
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  simp only [ne_eq, not_not, hconst]

/-- The arity-2 witness: `val 0 t = 0`, `val 1 t = 1 − t²` (so the two parabolas cross at `t = ±1`).
This is `QuadLines 2` with `A = (0, −1)`, `a = (0,0)`, `c = (0, 1)`. -/
def widthWitness : QuadLines 2 := ⟨![0, -1], ![0, 0], ![0, 1]⟩

theorem widthWitness_val0 (t : ℝ) : widthWitness.val 0 t = 0 := by
  simp [QuadLines.val, widthWitness]

theorem widthWitness_val1 (t : ℝ) : widthWitness.val 1 t = 1 - t^2 := by
  simp [QuadLines.val, widthWitness]; ring

/-- The witness' active index: `arg t = 1` exactly when `1 − t² > 0` (parabola `1` strictly wins),
else `0`. -/
theorem widthWitness_arg (t : ℝ) :
    widthWitness.arg (by norm_num) t = (if 0 < 1 - t^2 then (1 : Fin 2) else 0) := by
  by_cases h : 0 < 1 - t^2
  · rw [if_pos h]
    -- index 1 strictly beats index 0, so least-argmax = 1.
    have hspec : isLeastArgmax (fun i => widthWitness.val i t) 1 := by
      refine ⟨?_, ?_⟩
      · rw [Fin.forall_fin_two]
        refine ⟨?_, ?_⟩
        · simp only; rw [widthWitness_val0, widthWitness_val1]; linarith
        · simp only; rw [widthWitness_val1]
      · intro j hj
        have hj0 : j = 0 := by omega
        subst hj0
        simp only; rw [widthWitness_val0, widthWitness_val1]; linarith
    exact isLeastArgmax_unique _ _ _ (leastArgmax_spec _ (by norm_num)) hspec
  · rw [if_neg h]
    -- index 0 weakly beats all and is least, so least-argmax = 0.
    have hspec : isLeastArgmax (fun i => widthWitness.val i t) 0 := by
      refine ⟨?_, ?_⟩
      · rw [Fin.forall_fin_two]
        refine ⟨?_, ?_⟩
        · simp only; rw [widthWitness_val0]
        · simp only; rw [widthWitness_val0, widthWitness_val1]; linarith
      · intro j hj; exact absurd hj (by simp)
    exact isLeastArgmax_unique _ _ _ (leastArgmax_spec _ (by norm_num)) hspec

/-- The 3-point increasing sample `(−2, 0, 2)`. -/
def widthPts : Fin 3 → ℝ := ![-2, 0, 2]

theorem widthPts_increasing : Increasing widthPts := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [widthPts, Fin.lt_def]

/-- **A width separation (arity 2 ∉ arity 1).**  The arity-2 witness `widthWitness`
makes its active index alternate `0, 1, 0` along `(−2, 0, 2)`, giving `seqChanges = 2`; but EVERY
arity-1 family has `seqChanges = 0` on the same sample.  Hence the arity-2 alternation route is not
realizable at arity 1.  (The two crossings of the two parabolas are exactly the order-2 behaviour
that an affine/order-1 comparison cannot produce.) -/
theorem widthSeparation :
    seqChanges (fun k => widthWitness.arg (by norm_num) (widthPts k)) = 2
    ∧ ∀ g : QuadLines 1, seqChanges (fun k => g.arg (by norm_num) (widthPts k)) = 0 := by
  refine ⟨?_, ?_⟩
  · -- compute the arg-sequence: at -2 → 0, at 0 → 1, at 2 → 0.
    have hp0 : widthPts 0 = -2 := by simp [widthPts]
    have hp1 : widthPts 1 = 0 := by simp [widthPts]
    have hp2 : widthPts 2 = 2 := by simp [widthPts]
    have ha0 : widthWitness.arg (by norm_num) (widthPts 0) = 0 := by
      rw [widthWitness_arg, hp0, if_neg (by norm_num)]
    have ha1 : widthWitness.arg (by norm_num) (widthPts 1) = 1 := by
      rw [widthWitness_arg, hp1, if_pos (by norm_num)]
    have ha2 : widthWitness.arg (by norm_num) (widthPts 2) = 0 := by
      rw [widthWitness_arg, hp2, if_neg (by norm_num)]
    -- seqChanges over m = 2 (Fin 2 adjacent pairs): both pairs change.
    unfold seqChanges
    rw [show (Finset.univ.filter (fun i : Fin 2 =>
        widthWitness.arg (by norm_num) (widthPts i.castSucc)
          ≠ widthWitness.arg (by norm_num) (widthPts i.succ))) = Finset.univ from ?_]
    · simp
    · rw [Finset.eq_univ_iff_forall]
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      fin_cases i
      · show widthWitness.arg (by norm_num) (widthPts 0) ≠ widthWitness.arg (by norm_num) (widthPts 1)
        rw [ha0, ha1]; decide
      · show widthWitness.arg (by norm_num) (widthPts 1) ≠ widthWitness.arg (by norm_num) (widthPts 2)
        rw [ha1, ha2]; decide
  · intro g
    exact quadArg_arity_one_no_alternation g widthPts

end TLT.TemperedDesignLaw
