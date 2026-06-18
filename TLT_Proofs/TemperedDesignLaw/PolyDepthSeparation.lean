/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.QuadDepthSeparation3

/-!
# The degree-`d` generalization of the polynomial-router DEPTH separation (base `d+1`)

This file proves the GENERAL-`d` second-order DEPTH separation
`polyDepthGrade d L ⊂ polyDepthGrade d (L+1)` for EVERY `L` and EVERY `d ≥ 1`, via the **arity-`(d+1)`**
route. It is the parametrised lift of:

* the affine `d = 1` (binary, base `2`) separation `binCascadeGrade_ssubset_succ`, and
* the quadratic `d = 2` (arity-`3`, base `3`) separation `quadDepthGrade3_ssubset_succ`
  (`QuadDepthSeparation3.lean`),

to arbitrary degree `d`. Every base-`3` constant of `QuadDepthSeparation3.lean` becomes base-`(d+1)`.

## The model

A `PolyMuxLayer d` is an arity-`(d+1)` gated, affine-branched mux layer: `d+1` quadratic gate scores
that SHARE a common bilinear (self-attention) part `Mcommon` — so the expert-vs-expert *comparison* is
affine and the argmax cells on any line are intervals — and `d+1` DISTINCT affine branch maps. This is
the faithful multi-expert (`k = d+1`) router whose per-layer gate folds a line into `d+1` monotone
laps with `d+1` distinct affine branches (a genuine fold; no shared-branch collapse). Iterated to depth
`L`, with an arity-`2` affine readout, it defines the grade `polyDepthGrade d L`.

## The pieces (all sorry-free; mirror of `QuadDepthSeparation3.lean` at base `d+1`)

1. `PolyMuxLayer d` / `polyDepthGrade d L`: the arity-`(d+1)` gated layer, iterated to a depth-`L`
   cascade `PolyCascade d L`, with the arity-`2` affine readout grade.

2. `seqChanges_blockRefine_poly_le`: the per-value GLOBAL-no-return base-`n` block-refine
   `seqChanges (u, b) ≤ n · seqChanges u + (n − 1)` for an arity-`n` bit `b`. At `n = d+1` this is
   `≤ (d+1) · u + d`; at `n = 2` (the binary route) it is `≤ 2 · u + 1`. The `Fin n` analogue of
   `seqChanges_blockRefine3_le` (which was the `n = 3` case); the per-block fiber-card `≤ n − 1` comes
   from per-value no-return into an `n`-element codomain (the image misses the entry value).

3. `polyRoute_alternations_le ≤ (d+1)^(L+1) − 1`: the depth-`L` line/route alternation ceiling. The
   trace bit is an `AffineLines (d+1)` argmax of `t` with GLOBAL no-return, giving the base-`(d+1)`
   trace bound `≤ (d+1)^L − 1`; the route is an `AffineLines 2` argmax with GLOBAL no-return, so one
   more `× 2 + 1` refine gives `≤ 2 · (d+1)^L − 1 ≤ (d+1)^(L+1) − 1`. Analogue of
   `quadRoute3_alternations_le`.

4. `polyTentMap d : ℝ → ℝ`: the `(d+1)`-ary tent, `d+1` monotone laps each onto `[0,1]`; the analogue
   of `ternMap` (`d = 2`). `polyTentLayer d` realizes it as a `PolyMuxLayer d` with `d+1` distinct
   affine anchors gated by an affine-score `leastArgmax`.

5. `polyTentMap_iterate`: on the `(d+1)`-adic grid `j / (d+1)^L` the `L`-fold tent equals `(j mod 2)`;
   the analogue of `ternMap_iterate_triadic`.

6. `polyTentRoute_alternations_eq = (d+1)^(L+1)`: the depth-`(L+1)` tent saturates `(d+1)^(L+1)` route
   alternations on the `(d+1)`-adic grid — `> (d+1)^(L+1) − 1`, so `∉` grade `L`, `∈` grade `(L+1)`.

7. `polyDepthGrade_ssubset_succ d L`: combine — the GENERAL-`d` strict depth ladder.

## Honesty (A4)

This is the base-`(d+1)` STRUCTURAL separation, general in `d`: the `(d+1)`-ary tent (which saturates
`(d+1)^(L+1)` line alternations) against the `(d+1)^(L+1) − 1` route ceiling. It is the
`quadDepthGrade3` level lifted to arbitrary `d` (the induction is parametrised in `d`, not fixed). The
full shallow-network *approximation* lower bound is NOT formalized here and remains open.
-/

open scoped BigOperators
open Set

noncomputable section

open Classical

namespace TLT.TemperedDesignLaw

open TLT.TemperedDesignLaw.MuxHierarchy

/-! ## (0) The general base-`n` per-value block-refine `≤ n · u + (n − 1)`

The combinatorial engine of the general-`d` ladder. We refine a coarse sequence `u` by a `Fin n` bit
`b` whose value-fibers, on every `u`-constant index interval, have **per-value global no-return** (each
value once left never recurs). With `n` values that forces the `blockOf2`-fibers over the `b`-only
flips to have card `≤ n − 1` (the image of the entry map misses the block's left-endpoint value),
giving `|Bonly| ≤ (n−1)·(|U|+1)` and `seqChanges (u, b) ≤ |U| + |Bonly| ≤ n·|U| + (n−1)`. This is the
arity-`n` generalization of `seqChanges_blockRefine3_le` (the `n = 3` case). -/

/-- A `Finset` whose every fiber under a map `φ` has card `≤ N` has card `≤ N · (image φ).card`. The
arity-`n` generalization of `card_le_two_mul_image` (the `N = 2` case). -/
theorem card_le_mul_image {α β : Type*} [DecidableEq α] [DecidableEq β] (N : ℕ) (S : Finset α)
    (φ : α → β) (hfib : ∀ q : β, (S.filter (fun a => φ a = q)).card ≤ N) :
    S.card ≤ N * (S.image φ).card := by
  classical
  have hpart : S.card = ∑ q ∈ S.image φ, (S.filter (fun a => φ a = q)).card := by
    rw [← Finset.card_eq_sum_card_fiberwise (fun a ha => Finset.mem_image_of_mem φ ha)]
  rw [hpart]
  calc ∑ q ∈ S.image φ, (S.filter (fun a => φ a = q)).card
      ≤ ∑ _q ∈ S.image φ, N := Finset.sum_le_sum (fun q _ => hfib q)
    _ = N * (S.image φ).card := by rw [Finset.sum_const, smul_eq_mul]; ring

/-- **THE BASE-`n` PER-VALUE BLOCK-REFINE.** Let `u : Fin(m+1)→A`, `b : Fin(m+1)→Fin n` with `0 < n`,
and suppose `b` has the **per-block global no-return** property: on any index interval `[a,d]` on which
`u` is constant, for EVERY value `c` the `c`-fiber of `b` inside `[a,d]` is no-return. Then the paired
sequence `(u, b)` changes at most `n · seqChanges u + (n − 1)` times. At `n = 3` this is
`seqChanges_blockRefine3_le`; at `n = d+1` it is `≤ (d+1)·u + d`; at `n = 2` it is `≤ 2·u + 1`. -/
theorem seqChanges_blockRefine_poly_le {A : Type*} [DecidableEq A] {m n : ℕ} (hn : 0 < n)
    (u : Fin (m + 1) → A) (b : Fin (m + 1) → Fin n)
    (hblock : ∀ a d : Fin (m + 1), a ≤ d →
      (∀ e, a ≤ e → e ≤ d → u e = u a) →
      ∀ c : Fin n, ∀ p r s : Fin (m + 1), a ≤ p → p ≤ s → s ≤ r → r ≤ d →
        b p = c → b r = c → b s = c) :
    seqChanges (fun k => (u k, b k)) ≤ n * seqChanges u + (n - 1) := by
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
  -- The core: every blockOf2-fiber over Bonly has card ≤ n − 1.
  have hfib : ∀ q : ℕ, (Bonly.filter (fun i => blockOf2 u i = q)).card ≤ n - 1 := by
    intro q
    set F : Finset (Fin m) := Bonly.filter (fun i => blockOf2 u i = q) with hF
    by_contra hcon
    push Not at hcon  -- n - 1 < F.card
    have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
    -- a flip-index witnesses two distinct values of `b`, so `2 ≤ n`; with `hcon : n-1 < F.card` this
    -- forces `2 ≤ F.card`, hence `lo < hi`.
    have hn2 : 2 ≤ n := by
      obtain ⟨x, hx⟩ := hFne
      have hxb : b x.castSucc ≠ b x.succ :=
        ((Finset.mem_filter.mp ((Finset.mem_filter.mp hx).1)).2).2
      by_contra hlt
      have hn1 : n = 1 := by omega
      have : b x.castSucc = b x.succ := by
        apply Fin.ext
        have l1 : (b x.castSucc).val < n := (b x.castSucc).isLt
        have l2 : (b x.succ).val < n := (b x.succ).isLt
        omega
      exact hxb this
    have hcard2 : 2 ≤ F.card := by omega
    set lo := F.min' hFne with hlo
    set hi := F.max' hFne with hhi
    have hlo_mem : lo ∈ F := F.min'_mem hFne
    have hhi_mem : hi ∈ F := F.max'_mem hFne
    have hlo_u : u lo.castSucc = u lo.succ :=
      ((Finset.mem_filter.mp ((Finset.mem_filter.mp hlo_mem).1)).2).1
    have hhi_u : u hi.castSucc = u hi.succ :=
      ((Finset.mem_filter.mp ((Finset.mem_filter.mp hhi_mem).1)).2).1
    have hlo_q : blockOf2 u lo = q := (Finset.mem_filter.mp hlo_mem).2
    have hhi_q : blockOf2 u hi = q := (Finset.mem_filter.mp hhi_mem).2
    -- lo < hi (else card ≤ 1 ≤ n − 1, contradicting card > n − 1 only when n − 1 ≥ 1; but if
    -- card ≤ 1 then n − 1 < 1 forces n = 1, and card ≤ 1 ≤ n − 1 = 0 is false — handled by omega.)
    have hlohi : lo < hi := by
      rcases lt_or_eq_of_le (F.min'_le _ hhi_mem) with h | h
      · exact h
      · exfalso
        have hall : ∀ x ∈ F, x = lo := by
          intro x hx
          have h1 : lo ≤ x := F.min'_le _ hx
          have h2 : x ≤ hi := F.le_max' _ hx
          rw [← h] at h2; exact le_antisymm h2 h1
        have hsing : F ⊆ {lo} := fun x hx => Finset.mem_singleton.mpr (hall x hx)
        have hcle := Finset.card_le_card hsing
        simp only [Finset.card_singleton] at hcle
        omega
    have huconst : ∀ e, lo.castSucc ≤ e → e ≤ hi.succ → u e = u lo.castSucc :=
      u_const_on_block u lo hi hlohi hlo_u hhi_u (hlo_q.trans hhi_q.symm)
    have hcd : (lo.castSucc : Fin (m+1)) ≤ hi.succ := by
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; have : lo.val ≤ hi.val := le_of_lt hlohi
      omega
    have hFbound : ∀ x ∈ F, (lo.castSucc : Fin (m+1)) ≤ x.castSucc ∧
        (x.castSucc : Fin (m+1)) ≤ x.succ ∧ (x.succ : Fin (m+1)) ≤ hi.succ := by
      intro x hx
      have h1 : lo ≤ x := F.min'_le _ hx
      have h2 : x ≤ hi := F.le_max' _ hx
      have h1' : lo.val ≤ x.val := h1
      have h2' : x.val ≤ hi.val := h2
      refine ⟨?_, ?_, ?_⟩
      · simp only [Fin.le_def, Fin.val_castSucc]; exact h1'
      · simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega
      · simp only [Fin.le_def, Fin.val_succ]; omega
    have hnr : ∀ c : Fin n, ∀ p r s : Fin (m + 1), lo.castSucc ≤ p → p ≤ s → s ≤ r → r ≤ hi.succ →
        b p = c → b r = c → b s = c :=
      hblock lo.castSucc hi.succ hcd huconst
    -- entry map `i ↦ b i.succ` injects into `univ \ {b lo.castSucc}`, card `n − 1`.
    set φ : Fin m → Fin n := fun i => b i.succ with hφ
    have hinj : ∀ x ∈ F, ∀ x' ∈ F, φ x = φ x' → x = x' := by
      intro x hx x' hx' heq0
      have heq : b x.succ = b x'.succ := heq0
      by_contra hne
      have hxb : b x.castSucc ≠ b x.succ :=
        ((Finset.mem_filter.mp ((Finset.mem_filter.mp hx).1)).2).2
      have hx'b : b x'.castSucc ≠ b x'.succ :=
        ((Finset.mem_filter.mp ((Finset.mem_filter.mp hx').1)).2).2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have ho1 : (lo.castSucc : Fin (m+1)) ≤ x.succ := le_trans (hFbound x hx).1 (hFbound x hx).2.1
        have hps : (x.succ : Fin (m+1)) ≤ x'.castSucc := by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          simp only [Fin.lt_def] at hlt; omega
        have hsr : (x'.castSucc : Fin (m+1)) ≤ x'.succ := (hFbound x' hx').2.1
        have := hnr (b x.succ) x.succ x'.succ x'.castSucc ho1 hps hsr (hFbound x' hx').2.2 rfl heq.symm
        exact hx'b (this.trans heq)
      · have ho1 : (lo.castSucc : Fin (m+1)) ≤ x'.succ := le_trans (hFbound x' hx').1 (hFbound x' hx').2.1
        have hps : (x'.succ : Fin (m+1)) ≤ x.castSucc := by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          simp only [Fin.lt_def] at hgt; omega
        have hsr : (x.castSucc : Fin (m+1)) ≤ x.succ := (hFbound x hx).2.1
        have := hnr (b x'.succ) x'.succ x.succ x.castSucc ho1 hps hsr (hFbound x hx).2.2 rfl heq
        exact hxb (this.trans heq.symm)
    have hmiss : ∀ x ∈ F, φ x ≠ b lo.castSucc := by
      intro x hx heq00
      have heq0 : b x.succ = b lo.castSucc := heq00
      have hxb : b x.castSucc ≠ b x.succ :=
        ((Finset.mem_filter.mp ((Finset.mem_filter.mp hx).1)).2).2
      have ho1 : (lo.castSucc : Fin (m+1)) ≤ lo.castSucc := le_refl _
      have hps : (lo.castSucc : Fin (m+1)) ≤ x.castSucc := (hFbound x hx).1
      have hsr : (x.castSucc : Fin (m+1)) ≤ x.succ := (hFbound x hx).2.1
      have hrd : (x.succ : Fin (m+1)) ≤ hi.succ := (hFbound x hx).2.2
      have := hnr (b lo.castSucc) lo.castSucc x.succ x.castSucc ho1 hps hsr hrd rfl heq0
      exact hxb (this.trans heq0.symm)
    have hsubF : F.image φ ⊆ Finset.univ \ {b lo.castSucc} := by
      intro c hc
      simp only [Finset.mem_image] at hc
      obtain ⟨x, hx, rfl⟩ := hc
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact hmiss x hx
    have hcard_image : F.card = (F.image φ).card :=
      (Finset.card_image_of_injOn (fun x hx x' hx' h => hinj x hx x' hx' h)).symm
    have hcard_le : (F.image φ).card ≤ (Finset.univ \ {b lo.castSucc} : Finset (Fin n)).card :=
      Finset.card_le_card hsubF
    have hsdiff : (Finset.univ \ {b lo.castSucc} : Finset (Fin n)).card = n - 1 := by
      rw [Finset.card_univ_diff]
      simp
    omega
  -- |Bonly| ≤ (n−1)·(image card) ≤ (n−1)·(|U|+1)
  have hBonly_card : Bonly.card ≤ (n - 1) * (U.card + 1) := by
    have h1 : Bonly.card ≤ (n - 1) * (Bonly.image (blockOf2 u)).card :=
      card_le_mul_image (n - 1) Bonly (blockOf2 u) hfib
    have h2 : (Bonly.image (blockOf2 u)).card ≤ U.card + 1 := by
      have hsub2 : Bonly.image (blockOf2 u) ⊆ Finset.range (U.card + 1) := by
        intro x hx
        simp only [Finset.mem_image] at hx
        obtain ⟨i, _, rfl⟩ := hx
        simp only [Finset.mem_range]
        have hle : blockOf2 u i ≤ U.card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [hU]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.2⟩
        omega
      calc (Bonly.image (blockOf2 u)).card ≤ (Finset.range (U.card + 1)).card :=
            Finset.card_le_card hsub2
        _ = U.card + 1 := Finset.card_range _
    calc Bonly.card ≤ (n - 1) * (Bonly.image (blockOf2 u)).card := h1
      _ ≤ (n - 1) * (U.card + 1) := Nat.mul_le_mul_left _ h2
  have htotal : seqChanges (fun k => (u k, b k)) ≤ U.card + Bonly.card := by
    unfold seqChanges
    calc _ ≤ (U ∪ Bonly).card := Finset.card_le_card hsub
      _ ≤ U.card + Bonly.card := Finset.card_union_le _ _
  have hUcard : U.card = seqChanges u := rfl
  -- U.card + (n−1)(U.card+1) = n·U.card + (n−1)
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hexpand : U.card + (n' + 1 - 1) * (U.card + 1) = (n' + 1) * seqChanges u + (n' + 1 - 1) := by
    rw [← hUcard]; simp only [Nat.add_sub_cancel]; ring
  calc seqChanges (fun k => (u k, b k))
      ≤ U.card + Bonly.card := htotal
    _ ≤ U.card + (n' + 1 - 1) * (U.card + 1) := by
        have := hBonly_card; omega
    _ = (n' + 1) * seqChanges u + (n' + 1 - 1) := hexpand

/-! ## (1) The arity-`(d+1)` polynomial-gated, affine-branched cascade -/

/-- An arity-`(d+1)` quadratic-gated, affine-branched mux layer on `Fin D → ℝ` (a multi-expert
`k = d+1` router). The gate scores share a common quadratic (self-attention bilinear) part `Mcommon`;
only their per-expert linear/constant parts vary, so the expert-vs-expert comparison is affine and the
argmax cells on any line are intervals. The arity is `d+1`: `d+1` distinct affine branches realize a
`(d+1)`-fold of the line. (`d = 1`: binary; `d = 2`: the arity-`3` `QuadMuxLayer3`.) -/
structure PolyMuxLayer (d D : ℕ) where
  /-- The shared quadratic (self-attention bilinear) part of every gate score. -/
  Mcommon : Fin D → Fin D → ℝ
  /-- The per-expert linear part of the gate score. -/
  gateLin : Fin (d + 1) → Fin D → ℝ
  /-- The per-expert constant part of the gate score. -/
  gateConst : Fin (d + 1) → ℝ
  branches : Fin (d + 1) → AffineSelfMap D

/-- The `i`-th gate score of an arity-`(d+1)` layer: the shared `Mcommon` plus the per-expert
linear/constant parts. -/
def PolyMuxLayer.scores {d D : ℕ} (Lyr : PolyMuxLayer d D) (i : Fin (d + 1)) : QuadScore D :=
  ⟨Lyr.Mcommon, Lyr.gateLin i, Lyr.gateConst i⟩

/-- The branch index selected by an arity-`(d+1)` layer at `x`: the `leastArgmax` of its `d+1`
scores. -/
def PolyMuxLayer.gate {d D : ℕ} (Lyr : PolyMuxLayer d D) (x : Fin D → ℝ) : Fin (d + 1) :=
  leastArgmax (fun i => (Lyr.scores i).eval x) (Nat.succ_pos d)

/-- The map of an arity-`(d+1)` layer: gate by the argmax of the `d+1` quadratic scores, apply the
selected affine branch. -/
def PolyMuxLayer.applyLayer {d D : ℕ} (Lyr : PolyMuxLayer d D) (x : Fin D → ℝ) : Fin D → ℝ :=
  (Lyr.branches (Lyr.gate x)).apply x

/-- A depth-`L` arity-`(d+1)` polynomial-gated cascade. -/
structure PolyCascade (d D L : ℕ) where
  layers : Fin L → PolyMuxLayer d D

/-- Run the first `m` layers (input-first). -/
def PolyCascade.runUpTo {d D L : ℕ} (C : PolyCascade d D L) : ℕ → (Fin D → ℝ) → (Fin D → ℝ)
  | 0, x => x
  | (m + 1), x =>
      if h : m < L then
        (C.layers ⟨m, h⟩).applyLayer (C.runUpTo m x)
      else C.runUpTo m x

/-- The composed region map: run all `L` layers. -/
def PolyCascade.run {d D L : ℕ} (C : PolyCascade d D L) (x : Fin D → ℝ) : Fin D → ℝ :=
  C.runUpTo L x

/-- The active-branch trace, in `Fin L → Fin (d+1)`. -/
def PolyCascade.trace {d D L : ℕ} (C : PolyCascade d D L) (x : Fin D → ℝ) : Fin L → Fin (d + 1) :=
  fun i => (C.layers i).gate (C.runUpTo i.val x)

/-- The arity-`2` affine argmax readout of an arity-`(d+1)` cascade (the route into `Fin 2`). -/
def polyCascadeRoute {d D L : ℕ} (C : PolyCascade d D L) (routeScores : Fin 2 → AffineFunctional D) :
    (Fin D → ℝ) → Fin 2 :=
  fun x => leastArgmax (fun j => (routeScores j).eval (C.run x)) (by norm_num)

/-- **The degree-`d` polynomial depth grade.** Routes `(Fin D → ℝ) → Fin 2` realizable by SOME
depth-`L` arity-`(d+1)` polynomial-gated cascade with SOME `2` affine readout scores. Generalizes
`quadDepthGrade3` (`d = 2`). -/
def polyDepthGrade (d L : ℕ) : Set ((Fin 1 → ℝ) → Fin 2) :=
  { f | ∃ (layers : Fin L → PolyMuxLayer d 1) (routeScores : Fin 2 → AffineFunctional 1),
      f = polyCascadeRoute ⟨layers⟩ routeScores }

/-! ## (2) Affine-on-fiber: `C.run` is a fixed AFFINE map on each trace-fiber (mirror) -/

/-- The fixed affine map realizing `runUpTo m` on the trace-fiber of `x₀`. -/
def PolyCascade.prefixMap {d D L : ℕ} (C : PolyCascade d D L) (x₀ : Fin D → ℝ) :
    ℕ → AffineSelfMap D
  | 0 => AffineSelfMap.id D
  | (m + 1) =>
      if h : m < L then
        (C.layers ⟨m, h⟩).branches (C.trace x₀ ⟨m, h⟩) |>.comp (C.prefixMap x₀ m)
      else C.prefixMap x₀ m

/-- The fixed affine self-map agreeing with `C.run` on the trace-fiber of `x₀`. -/
def PolyCascade.fiberMap {d D L : ℕ} (C : PolyCascade d D L) (x₀ : Fin D → ℝ) : AffineSelfMap D :=
  C.prefixMap x₀ L

/-- The **partial-trace fiber** predicate. -/
def PolyCascade.PFiber {d D L : ℕ} (C : PolyCascade d D L) (x₀ y : Fin D → ℝ) (m : ℕ) : Prop :=
  ∀ i : Fin L, i.val < m → C.trace y i = C.trace x₀ i

/-- **PARTIAL affine-on-fiber.** -/
theorem PolyCascade.runUpTo_eq_prefixMap_on_pfiber {d D L : ℕ} (C : PolyCascade d D L)
    (x₀ y : Fin D → ℝ) :
    ∀ m, C.PFiber x₀ y m → C.runUpTo m y = (C.prefixMap x₀ m).apply y := by
  intro m
  induction m with
  | zero => intro _; simp [PolyCascade.runUpTo, PolyCascade.prefixMap]
  | succ m ih =>
      intro hpf
      rw [PolyCascade.runUpTo, PolyCascade.prefixMap]
      by_cases h : m < L
      · rw [dif_pos h, dif_pos h]
        have hpf_m : C.PFiber x₀ y m := fun i hi => hpf i (Nat.lt_succ_of_lt hi)
        rw [AffineSelfMap.comp_apply, ← ih hpf_m]
        have hgate : (C.layers ⟨m, h⟩).gate (C.runUpTo m y) = C.trace x₀ ⟨m, h⟩ := by
          have hbit : C.trace y ⟨m, h⟩ = C.trace x₀ ⟨m, h⟩ := hpf ⟨m, h⟩ (Nat.lt_succ_self m)
          simpa [PolyCascade.trace] using hbit
        simp only [PolyMuxLayer.applyLayer, hgate]
      · rw [dif_neg h, dif_neg h]
        exact ih (fun i hi => hpf i (Nat.lt_succ_of_lt hi))

/-- **FULL affine-on-fiber.** -/
theorem PolyCascade.run_eq_on_fiber {d D L : ℕ} (C : PolyCascade d D L) (x₀ y : Fin D → ℝ)
    (hfib : C.trace y = C.trace x₀) :
    C.run y = (C.fiberMap x₀).apply y := by
  rw [PolyCascade.run, PolyCascade.fiberMap]
  apply C.runUpTo_eq_prefixMap_on_pfiber x₀ y L
  intro i _; rw [hfib]

/-! ## (3) The geometric bridge: the shared-form gate through an affine map is an `AffineLines (d+1)`
argmax -/

/-- **THE GEOMETRIC BRIDGE.** Given an arity-`(d+1)` layer `Lyr` and a fixed affine self-map `A` on
`Fin 1 → ℝ`, the gate `Lyr.gate (A.apply ![t])`, as a function of `t`, equals `g.arg` for the explicit
`AffineLines (d+1)` `g` whose line `i` is the per-expert affine residual. The shared `Mcommon` part
cancels (`leastArgmax_add_const`). -/
theorem polyGate_comp_affine_eq_arg {d : ℕ} (Lyr : PolyMuxLayer d 1) (A : AffineSelfMap 1) (t : ℝ) :
    Lyr.gate (A.apply (fun _ => t))
      = (AffineLines.mk
          (fun i => Lyr.gateLin i 0 * A.mat 0 0)
          (fun i => Lyr.gateLin i 0 * A.shift 0 + Lyr.gateConst i)).arg
          (Nat.succ_pos d) t := by
  unfold PolyMuxLayer.gate AffineLines.arg
  set s := (A.apply (fun _ => t)) 0 with hs
  have hsc : ∀ i, (Lyr.scores i).eval (A.apply (fun _ => t))
      = Lyr.Mcommon 0 0 * s^2 + (Lyr.gateLin i 0 * s + Lyr.gateConst i) := by
    intro i
    rw [QuadScore.eval_coord1]
    simp only [PolyMuxLayer.scores, hs]
    ring
  have hsval : s = A.mat 0 0 * t + A.shift 0 := by rw [hs, AffineSelfMap.apply_coord1]
  have hrw : (fun i => (Lyr.scores i).eval (A.apply (fun _ => t)))
      = (fun i => Lyr.Mcommon 0 0 * s^2
          + (AffineLines.mk (fun i => Lyr.gateLin i 0 * A.mat 0 0)
              (fun i => Lyr.gateLin i 0 * A.shift 0 + Lyr.gateConst i)).val i t) := by
    funext i; rw [hsc i]
    congr 1
    unfold AffineLines.val
    rw [hsval]; ring
  rw [hrw, leastArgmax_add_const]

/-- An `AffineLines (d+1)` argmax, restricted to a monotone sample, has per-value no-return. -/
theorem affineArg_sample_noReturn {n : ℕ} (hn : 0 < n) (g : AffineLines n) {M : ℕ}
    (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    ∀ c : Fin n, ∀ p r s : Fin (M + 1), p ≤ s → s ≤ r →
      g.arg hn (pts p) = c → g.arg hn (pts r) = c →
      g.arg hn (pts s) = c := by
  intro c p r s hps hsr hp hr
  have hmono : ∀ i j : Fin (M + 1), i ≤ j → pts i ≤ pts j := by
    intro i j hij
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact le_of_lt (hinc i j h)
  have hoc := g.arg_win_ordConnected hn c
  rw [ordConnected_def] at hoc
  exact hoc (Set.mem_setOf_eq ▸ hp) (Set.mem_setOf_eq ▸ hr) ⟨hmono p s hps, hmono s r hsr⟩

/-! ## (4) The depth-`L` trace alternation bound `≤ (d+1)^L − 1` -/

/-- The layer-`m` gate bit of an arity-`(d+1)` cascade `⟨layers⟩` at the real point `t` (or `0` if
`m ≥ L`). -/
def polyBitAt {d L : ℕ} (layers : Fin L → PolyMuxLayer d 1) (m : ℕ) (t : ℝ) : Fin (d + 1) :=
  if h : m < L then (PolyCascade.mk layers).trace (fun _ => t) ⟨m, h⟩ else 0

/-- The **prefix** trace: first `m` bits as actual values, the rest masked to `0`. -/
def polyPrefixVec {d L : ℕ} (layers : Fin L → PolyMuxLayer d 1) (m : ℕ) (t : ℝ) :
    Fin L → Fin (d + 1) :=
  fun i => if i.val < m then (PolyCascade.mk layers).trace (fun _ => t) i else 0

/-- The prefix at `m+1` is the prefix at `m` updated with the layer-`m` bit. -/
theorem polyPrefixVec_succ_eq {d L : ℕ} (layers : Fin L → PolyMuxLayer d 1) (m : ℕ) (t : ℝ) :
    polyPrefixVec layers (m + 1) t
      = fun i => if i.val = m then polyBitAt layers m t else polyPrefixVec layers m t i := by
  funext i
  unfold polyPrefixVec polyBitAt
  by_cases hi : i.val = m
  · subst hi
    rw [if_pos (Nat.lt_succ_self _), if_pos rfl, dif_pos i.isLt]
  · by_cases hlt : i.val < m
    · rw [if_pos (Nat.lt_succ_of_lt hlt), if_neg hi, if_pos hlt]
    · rw [if_neg (by omega), if_neg hi, if_neg hlt]

/-- The partial-fiber from prefix-equality. -/
theorem pfiber_of_polyPrefixVec_eq {d L : ℕ} (layers : Fin L → PolyMuxLayer d 1)
    (m : ℕ) (t₁ t₂ : ℝ) (heq : polyPrefixVec layers m t₁ = polyPrefixVec layers m t₂) :
    (PolyCascade.mk layers).PFiber (fun _ => t₁) (fun _ => t₂) m := by
  intro i hi
  have h := congrFun heq i
  unfold polyPrefixVec at h
  rw [if_pos hi, if_pos hi] at h
  exact h.symm

/-- **THE PER-BLOCK GLOBAL NO-RETURN FOR THE NEXT ARITY-`(d+1)` BIT.** On any sample interval where the
prefix is constant, the layer-`m` gate bit has per-value no-return: on that interval `runUpTo m` is a
fixed affine map, so the bit is an `AffineLines (d+1)` argmax of `t` (`polyGate_comp_affine_eq_arg`),
whose win-sets give per-value no-return (`affineArg_sample_noReturn`). -/
theorem polyBitAt_block_noReturn {d L : ℕ} (layers : Fin L → PolyMuxLayer d 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) (m : ℕ) :
    ∀ a e : Fin (M + 1), a ≤ e →
      (∀ f, a ≤ f → f ≤ e →
        polyPrefixVec layers m (pts f) = polyPrefixVec layers m (pts a)) →
      ∀ c : Fin (d + 1), ∀ p r s : Fin (M + 1), a ≤ p → p ≤ s → s ≤ r → r ≤ e →
        polyBitAt layers m (pts p) = c → polyBitAt layers m (pts r) = c →
        polyBitAt layers m (pts s) = c := by
  intro a e hae hconst
  set C := PolyCascade.mk layers with hC
  by_cases hm : m < L
  · set A := C.prefixMap (fun _ => pts a) m with hA
    set Lyr := layers ⟨m, hm⟩ with hLyr
    set g := AffineLines.mk
        (fun i => Lyr.gateLin i 0 * A.mat 0 0)
        (fun i => Lyr.gateLin i 0 * A.shift 0 + Lyr.gateConst i) with hg
    have hbit : ∀ f : Fin (M + 1),
        polyPrefixVec layers m (pts f) = polyPrefixVec layers m (pts a) →
        polyBitAt layers m (pts f) = g.arg (Nat.succ_pos d) (pts f) := by
      intro f hf
      have hpf : C.PFiber (fun _ => pts a) (fun _ => pts f) m :=
        pfiber_of_polyPrefixVec_eq layers m (pts a) (pts f) hf.symm
      have hrun : C.runUpTo m (fun _ => pts f) = A.apply (fun _ => pts f) :=
        C.runUpTo_eq_prefixMap_on_pfiber (fun _ => pts a) (fun _ => pts f) m hpf
      unfold polyBitAt
      rw [dif_pos hm]
      have htrace : C.trace (fun _ => pts f) ⟨m, hm⟩
          = Lyr.gate (C.runUpTo m (fun _ => pts f)) := rfl
      rw [htrace, hrun]
      exact polyGate_comp_affine_eq_arg Lyr A (pts f)
    intro c p r s hap hps hsr hre hp hr
    have hpe : polyPrefixVec layers m (pts p) = polyPrefixVec layers m (pts a) :=
      hconst p hap (le_trans hps (le_trans hsr hre))
    have hree : polyPrefixVec layers m (pts r) = polyPrefixVec layers m (pts a) :=
      hconst r (le_trans hap (le_trans hps hsr)) hre
    have hse : polyPrefixVec layers m (pts s) = polyPrefixVec layers m (pts a) :=
      hconst s (le_trans hap hps) (le_trans hsr hre)
    have ep := hbit p hpe
    have er := hbit r hree
    have es := hbit s hse
    rw [ep] at hp
    rw [er] at hr
    rw [es]
    exact affineArg_sample_noReturn (Nat.succ_pos d) g pts hinc c p r s hps hsr hp hr
  · intro c p r s _ _ _ _ hp _
    unfold polyBitAt at hp ⊢; rw [dif_neg hm] at hp ⊢; exact hp

/-- **THE PREFIX-TRACE BASE-`(d+1)` BOUND.** Along any increasing sample, the first-`m`-bits prefix
trace of `⟨layers⟩` changes at most `(d+1)^m − 1` times. Induction on `m` via the base-`(d+1)`
block-refine `seqChanges_blockRefine_poly_le`. -/
theorem polyPrefixVec_alternations_le {d L : ℕ} (layers : Fin L → PolyMuxLayer d 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    ∀ m, seqChanges (fun k => polyPrefixVec layers m (pts k)) ≤ (d + 1) ^ m - 1 := by
  intro m
  induction m with
  | zero =>
      have hconst : ∀ k, polyPrefixVec layers 0 (pts k) = fun _ => 0 := by
        intro k; funext i; unfold polyPrefixVec; rw [if_neg (Nat.not_lt_zero _)]
      have heq : seqChanges (fun k => polyPrefixVec layers 0 (pts k))
          = seqChanges (fun _ : Fin (M + 1) => (fun _ : Fin L => (0 : Fin (d + 1)))) :=
        seqChanges_congr (fun k => hconst k)
      rw [heq]
      unfold seqChanges
      simp
  | succ m ih =>
      have hpair : seqChanges (fun k => polyPrefixVec layers (m + 1) (pts k))
          ≤ seqChanges (fun k => (polyPrefixVec layers m (pts k), polyBitAt layers m (pts k))) := by
        have heq : (fun k => polyPrefixVec layers (m + 1) (pts k))
            = fun k => (fun p : (Fin L → Fin (d + 1)) × Fin (d + 1) =>
                (fun i => if i.val = m then p.2 else p.1 i))
                (polyPrefixVec layers m (pts k), polyBitAt layers m (pts k)) := by
          funext k; rw [polyPrefixVec_succ_eq]
        rw [heq]
        exact seqChanges_comp_le
          (fun k => (polyPrefixVec layers m (pts k), polyBitAt layers m (pts k)))
          (fun p : (Fin L → Fin (d + 1)) × Fin (d + 1) =>
            (fun i => if i.val = m then p.2 else p.1 i))
      have hbr : seqChanges (fun k => (polyPrefixVec layers m (pts k), polyBitAt layers m (pts k)))
          ≤ (d + 1) * seqChanges (fun k => polyPrefixVec layers m (pts k)) + ((d + 1) - 1) :=
        seqChanges_blockRefine_poly_le (Nat.succ_pos d) _ _
          (fun a e hae hconst =>
            polyBitAt_block_noReturn layers pts hinc m a e hae hconst)
      have hpow : 1 ≤ (d + 1) ^ m := Nat.one_le_pow _ _ (Nat.succ_pos d)
      obtain ⟨q, hq⟩ : ∃ q, (d + 1) ^ m = q + 1 := ⟨(d + 1) ^ m - 1, by omega⟩
      have hkey : (d + 1) * ((d + 1) ^ m - 1) + ((d + 1) - 1) = (d + 1) ^ (m + 1) - 1 := by
        rw [pow_succ, hq]
        have hexp : (q + 1) * (d + 1) = (d + 1) * q + (d + 1) := by ring
        rw [hexp]
        simp only [Nat.add_sub_cancel]
        omega
      calc seqChanges (fun k => polyPrefixVec layers (m + 1) (pts k))
          ≤ (d + 1) * seqChanges (fun k => polyPrefixVec layers m (pts k)) + ((d + 1) - 1) :=
            le_trans hpair hbr
        _ ≤ (d + 1) * ((d + 1) ^ m - 1) + ((d + 1) - 1) :=
            Nat.add_le_add_right (Nat.mul_le_mul_left (d + 1) ih) ((d + 1) - 1)
        _ = (d + 1) ^ (m + 1) - 1 := hkey

/-- **THE TRACE ALTERNATION BOUND `≤ (d+1)^L − 1`.** -/
theorem polyTrace_alternations_le {d L : ℕ} (layers : Fin L → PolyMuxLayer d 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => (PolyCascade.mk layers).trace (fun _ => pts k)) ≤ (d + 1) ^ L - 1 := by
  have hL := polyPrefixVec_alternations_le layers pts hinc L
  have heq : (fun k => polyPrefixVec layers L (pts k))
      = fun k => (PolyCascade.mk layers).trace (fun _ => pts k) := by
    funext k; funext i; unfold polyPrefixVec; rw [if_pos i.isLt]
  rw [heq] at hL
  exact hL

/-! ## (5) The route alternation bound `≤ (d+1)^{L+1} − 1`

One more block-refine on top of the trace, this time with the BINARY route bit. On a full-trace fiber
the run is the fixed affine `fiberMap`, so the route is the `AffineLines 2` argmax of the readout
scores through it, with per-value (both-value) no-return. The base-`2` per-value block-refine
(`seqChanges_blockRefine_poly_le` at `n = 2`) gives `≤ 2 · trace + 1 ≤ 2·(d+1)^L − 1 ≤ (d+1)^{L+1} −
1`. -/

/-- The readout `rs` evaluated through a fixed affine map `A` is an `AffineLines 2` argmax of `t`. -/
theorem route_comp_affine_eq_arg (rs : Fin 2 → AffineFunctional 1) (A : AffineSelfMap 1) (t : ℝ) :
    leastArgmax (fun j => (rs j).eval (A.apply (fun _ => t))) (by norm_num)
      = (AffineLines.mk
          (fun j => (rs j).lin 0 * A.mat 0 0)
          (fun j => (rs j).lin 0 * A.shift 0 + (rs j).const)).arg (by norm_num) t := by
  unfold AffineLines.arg
  congr 1
  funext j
  rw [AffineFunctional.eval_coord1]
  have hc : (A.apply (fun _ => t)) 0 = A.mat 0 0 * t + A.shift 0 := by rw [AffineSelfMap.apply_coord1]
  rw [hc]
  show (rs j).lin 0 * (A.mat 0 0 * t + A.shift 0) + (rs j).const = (AffineLines.mk _ _).val j t
  unfold AffineLines.val
  ring

/-- **THE ROUTE BLOCK PER-VALUE NO-RETURN.** On any sample interval where the FULL trace is constant,
the route has per-value no-return: the run on the fiber is the fixed affine `fiberMap`, so the route is
an `AffineLines 2` argmax of `t`, whose win-sets are intervals. -/
theorem route_block_noReturn {d L : ℕ} (layers : Fin L → PolyMuxLayer d 1)
    (rs : Fin 2 → AffineFunctional 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    ∀ a e : Fin (M + 1), a ≤ e →
      (∀ f, a ≤ f → f ≤ e →
        (PolyCascade.mk layers).trace (fun _ => pts f)
          = (PolyCascade.mk layers).trace (fun _ => pts a)) →
      ∀ c : Fin 2, ∀ p r s : Fin (M + 1), a ≤ p → p ≤ s → s ≤ r → r ≤ e →
        polyCascadeRoute (PolyCascade.mk layers) rs (fun _ => pts p) = c →
        polyCascadeRoute (PolyCascade.mk layers) rs (fun _ => pts r) = c →
        polyCascadeRoute (PolyCascade.mk layers) rs (fun _ => pts s) = c := by
  intro a e hae hconst
  set C := PolyCascade.mk layers with hC
  set A := C.fiberMap (fun _ => pts a) with hA
  set g := AffineLines.mk
      (fun j => (rs j).lin 0 * A.mat 0 0)
      (fun j => (rs j).lin 0 * A.shift 0 + (rs j).const) with hg
  have hroute : ∀ f : Fin (M + 1),
      C.trace (fun _ => pts f) = C.trace (fun _ => pts a) →
      polyCascadeRoute C rs (fun _ => pts f) = g.arg (by norm_num) (pts f) := by
    intro f hf
    have hrun : C.run (fun _ => pts f) = A.apply (fun _ => pts f) :=
      C.run_eq_on_fiber (fun _ => pts a) (fun _ => pts f) hf
    unfold polyCascadeRoute
    rw [hrun]
    exact route_comp_affine_eq_arg rs A (pts f)
  intro c p r s hap hps hsr hre hp hr
  have hpe : C.trace (fun _ => pts p) = C.trace (fun _ => pts a) :=
    hconst p hap (le_trans hps (le_trans hsr hre))
  have hree : C.trace (fun _ => pts r) = C.trace (fun _ => pts a) :=
    hconst r (le_trans hap (le_trans hps hsr)) hre
  have hse : C.trace (fun _ => pts s) = C.trace (fun _ => pts a) :=
    hconst s (le_trans hap hps) (le_trans hsr hre)
  have ep := hroute p hpe
  have er := hroute r hree
  have es := hroute s hse
  rw [ep] at hp
  rw [er] at hr
  rw [es]
  exact affineArg_sample_noReturn (by norm_num) g pts hinc c p r s hps hsr hp hr

/-- **THE ROUTE ALTERNATION BOUND `≤ (d+1)^{L+1} − 1`.** Along any increasing sample, the arity-`2`
route of a depth-`L` arity-`(d+1)` polynomial cascade changes at most `(d+1)^{L+1} − 1` times: the
route is a function of the pair `(trace, route)`; the trace changes `≤ (d+1)^L − 1` times
(`polyTrace_alternations_le`) and the binary route has per-value no-return on trace-fibers
(`route_block_noReturn`), so the base-`2` per-value block-refine adds one more `× 2 + 1`, giving
`2·(d+1)^L − 1 ≤ (d+1)^{L+1} − 1`. -/
theorem polyRoute_alternations_le {d L : ℕ} (hd : 1 ≤ d) (layers : Fin L → PolyMuxLayer d 1)
    (rs : Fin 2 → AffineFunctional 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => polyCascadeRoute (PolyCascade.mk layers) rs (fun _ => pts k))
      ≤ (d + 1) ^ (L + 1) - 1 := by
  have hcomp : seqChanges (fun k => polyCascadeRoute (PolyCascade.mk layers) rs (fun _ => pts k))
      ≤ seqChanges (fun k => ((PolyCascade.mk layers).trace (fun _ => pts k),
          polyCascadeRoute (PolyCascade.mk layers) rs (fun _ => pts k))) := by
    have heq : (fun k => polyCascadeRoute (PolyCascade.mk layers) rs (fun _ => pts k))
        = fun k => (fun p : (Fin L → Fin (d + 1)) × Fin 2 => p.2)
            ((PolyCascade.mk layers).trace (fun _ => pts k),
             polyCascadeRoute (PolyCascade.mk layers) rs (fun _ => pts k)) := rfl
    rw [heq]
    exact seqChanges_comp_le _ (fun p : (Fin L → Fin (d + 1)) × Fin 2 => p.2)
  have hbr : seqChanges (fun k => ((PolyCascade.mk layers).trace (fun _ => pts k),
      polyCascadeRoute (PolyCascade.mk layers) rs (fun _ => pts k)))
      ≤ 2 * seqChanges (fun k => (PolyCascade.mk layers).trace (fun _ => pts k)) + (2 - 1) :=
    seqChanges_blockRefine_poly_le (by norm_num) _ _
      (fun a e hae hconst => route_block_noReturn layers rs pts hinc a e hae hconst)
  have htrace := polyTrace_alternations_le layers pts hinc
  have hpow : 1 ≤ (d + 1) ^ L := Nat.one_le_pow _ _ (Nat.succ_pos d)
  obtain ⟨q, hq⟩ : ∃ q, (d + 1) ^ L = q + 1 := ⟨(d + 1) ^ L - 1, by omega⟩
  have hkey : 2 * ((d + 1) ^ L - 1) + 1 ≤ (d + 1) ^ (L + 1) - 1 := by
    rw [pow_succ, hq]
    have hexp : (q + 1) * (d + 1) = (d + 1) * q + (d + 1) := by ring
    rw [hexp]
    simp only [Nat.add_sub_cancel]
    -- goal: 2*q + 1 ≤ (d+1)*q + (d+1) - 1, i.e. 2q + 1 ≤ (d+1)*q + d
    have hq2 : 2 * q ≤ (d + 1) * q := Nat.mul_le_mul_right q (by omega : 2 ≤ d + 1)
    omega
  calc seqChanges (fun k => polyCascadeRoute (PolyCascade.mk layers) rs (fun _ => pts k))
      ≤ 2 * seqChanges (fun k => (PolyCascade.mk layers).trace (fun _ => pts k)) + (2 - 1) :=
        le_trans hcomp hbr
    _ ≤ 2 * ((d + 1) ^ L - 1) + 1 := by
        have := Nat.mul_le_mul_left 2 htrace; omega
    _ ≤ (d + 1) ^ (L + 1) - 1 := hkey

/-! ## (6) The (d+1)-ary tent witness and its iterate (polyTentMap d)^[L]

The (d+1)-ary tent `polyTentMap d` folds the line into `d+1` monotone laps, each onto `[0,1]`, keyed by
the threshold `i/(d+1)`: on lap `i ∈ {0,…,d}` the map is `(d+1)·s - i` (up) for `i` even and
`(i+1) - (d+1)·s` (down) for `i` odd. The `d+1` laps use `d+1` DISTINCT affine branches (a genuine
fold; no shared-branch collapse), gated by an affine-score `leastArgmax`, so the fold factor is a
genuine `d+1`. The lap index is clamped to `{0,…,d}` (the last lap `[d/(d+1), 1]` absorbs the right
endpoint), exactly as `ternMap`'s last lap `[2/3, ∞)` does for `d = 2`. -/

/-- The affine lap value: lap `i` of the (d+1)-ary tent at `s`, `(d+1)·s - i` (even) or
`(i+1) - (d+1)·s` (odd). -/
def polyLap (d : ℕ) (i : ℕ) (s : ℝ) : ℝ :=
  if i % 2 = 0 then (d + 1) * s - i else (i + 1) - (d + 1) * s

/-- The lap index of `s` for the (d+1)-ary tent: `⌊(d+1)·s⌋₊` clamped to `{0,…,d}`. On the grid point
`j/(d+1)^{L+1}` this is `min d (j/(d+1)^L)` (`polyLapIndex_grid`). -/
def polyLapIndex (d : ℕ) (s : ℝ) : ℕ := min d ⌊(d + 1 : ℝ) * s⌋₊

/-- **The (d+1)-ary tent fold as a SINGLE real map** `polyTentMap d : ℝ → ℝ`: apply the lap formula
`polyLap d i s` at the clamped lap index `i = min d ⌊(d+1)·s⌋₊`. The analogue of `ternMap` (`d = 2`). -/
def polyTentMap (d : ℕ) (s : ℝ) : ℝ := polyLap d (polyLapIndex d s) s

/-- **ONE FOLD OF THE (d+1)-ADIC GRID.** For `j ≤ (d+1)^{L+1}`, the grid point `j/(d+1)^{L+1}` lies in
the clamped lap `i = min d (j/(d+1)^L)`, and `polyLap d i (j/(d+1)^{L+1}) = num/(d+1)^L` with
`num ≤ (d+1)^L` and `num ≡ j (mod 2)`. The single arithmetic fact behind the iterate identity;
generalizes `ternMap_fold_grid` (`d = 2`). -/
private theorem floor_div_nat_real (j P : ℕ) (hP : 0 < P) :
    ⌊((j : ℝ) / ((P : ℕ) : ℝ))⌋₊ = j / P := by
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ (by exact_mod_cast hP)]
    have hle := Nat.div_mul_le_self j P
    have hc : ((j / P : ℕ) : ℝ) * (P : ℝ) = ((j / P * P : ℕ) : ℝ) := by push_cast; ring
    rw [hc]; exact_mod_cast hle
  · rw [div_lt_iff₀ (by exact_mod_cast hP)]
    have hlt : j < (j / P + 1) * P := by
      have h1 := Nat.div_add_mod j P
      have h2 : j % P < P := Nat.mod_lt j hP
      nlinarith [h1, h2, Nat.div_mul_le_self j P]
    have hc : ((↑(j / P) : ℝ) + 1) * (P : ℝ) = (((j / P + 1) * P : ℕ) : ℝ) := by push_cast; ring
    rw [hc]; exact_mod_cast hlt

theorem polyLap_fold_grid (d L : ℕ) (j : ℕ) (hj : j ≤ (d + 1) ^ (L + 1)) :
    ∃ num : ℕ, num ≤ (d + 1) ^ L ∧ num % 2 = j % 2 ∧
      polyLap d (min d (j / (d + 1) ^ L)) ((j : ℝ) / (d + 1) ^ (L + 1)) = (num : ℝ) / (d + 1) ^ L := by
  have hpowLpos : (0 : ℝ) < ((d : ℝ) + 1) ^ L := by positivity
  have hLne : ((d : ℝ) + 1) ^ L ≠ 0 := ne_of_gt hpowLpos
  have hsucc : ((d : ℝ) + 1) ^ (L + 1) = ((d : ℝ) + 1) * ((d : ℝ) + 1) ^ L := by rw [pow_succ]; ring
  set P : ℕ := (d + 1) ^ L with hP
  have hPpos : 0 < P := Nat.pow_pos (Nat.succ_pos d)
  set i : ℕ := min d (j / P) with hi
  have hile : i ≤ d := Nat.min_le_left _ _
  have hiright : i ≤ j / P := Nat.min_le_right _ _
  -- clamped lap bounds: i·P ≤ j ≤ (i+1)·P
  have hjP : j ≤ (d + 1) * P := by rw [hP, ← pow_succ']; exact hj
  have hexp : (i + 1) * P = i * P + P := by ring
  have hdiv_lo : i * P ≤ j := by
    have h1 : (j / P) * P ≤ j := Nat.div_mul_le_self j P
    calc i * P ≤ (j / P) * P := Nat.mul_le_mul_right _ hiright
      _ ≤ j := h1
  have hdiv_hi : j ≤ (i + 1) * P := by
    rcases Nat.lt_or_ge (j / P) (d + 1) with hlt' | hge'
    · -- i = j/P, j < (j/P + 1)·P ≤ (i+1)·P
      have hieq : i = j / P := by rw [hi]; omega
      have hlt : j < (j / P + 1) * P := by
        have h1 := Nat.div_add_mod j P
        have h2 : j % P < P := Nat.mod_lt j hPpos
        nlinarith [h1, h2, Nat.div_mul_le_self j P]
      rw [← hieq] at hlt; omega
    · -- j/P ≥ d+1, so i = d; j ≤ (d+1)·P = (i+1)·P
      have hieq : i = d := by rw [hi]; omega
      rw [hieq]; exact hjP
  have hPcast : (P : ℝ) = ((d : ℝ) + 1) ^ L := by rw [hP]; push_cast; ring
  rcases Nat.even_or_odd i with hpar | hpar
  · obtain ⟨ki, hki⟩ := hpar
    have hieven : i % 2 = 0 := by omega
    refine ⟨j - i * P, by omega, ?_, ?_⟩
    · have hiP : (i * P) % 2 = 0 := by rw [Nat.mul_mod, hieven]; simp
      omega
    · unfold polyLap
      rw [if_pos hieven, hsucc]
      have hcast : ((j - i * P : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) * (P : ℝ) := by
        rw [Nat.cast_sub hdiv_lo]; push_cast; ring
      rw [hcast, hPcast]; field_simp
  · obtain ⟨ki, hki⟩ := hpar
    have hiodd : i % 2 = 1 := by omega
    refine ⟨(i + 1) * P - j, by omega, ?_, ?_⟩
    · have hiP : ((i + 1) * P) % 2 = 0 := by
        have hpar1 : (i + 1) % 2 = 0 := by omega
        rw [Nat.mul_mod, hpar1]; simp
      omega
    · unfold polyLap
      rw [if_neg (by omega), hsucc]
      have hcast : (((i + 1) * P - j : ℕ) : ℝ) = ((i : ℝ) + 1) * (P : ℝ) - (j : ℝ) := by
        rw [Nat.cast_sub hdiv_hi]; push_cast; ring
      rw [hcast, hPcast]; field_simp

/-- **The clamped lap index on the grid.** `polyLapIndex d (j/(d+1)^{L+1}) = min d (j/(d+1)^L)`. -/
theorem polyLapIndex_grid (d L : ℕ) (j : ℕ) :
    polyLapIndex d ((j : ℝ) / (d + 1) ^ (L + 1)) = min d (j / (d + 1) ^ L) := by
  unfold polyLapIndex
  congr 1
  have hsucc : ((d : ℝ) + 1) ^ (L + 1) = ((d : ℝ) + 1) * ((d : ℝ) + 1) ^ L := by rw [pow_succ]; ring
  have hdpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hpowLpos : (0 : ℝ) < ((d : ℝ) + 1) ^ L := by positivity
  have hval : (d + 1 : ℝ) * ((j : ℝ) / (d + 1) ^ (L + 1)) = (j : ℝ) / ((d : ℝ) + 1) ^ L := by
    rw [hsucc]; field_simp
  rw [hval]
  have hPcast : ((d : ℝ) + 1) ^ L = (((d + 1) ^ L : ℕ) : ℝ) := by push_cast; ring
  rw [hPcast]
  exact floor_div_nat_real j ((d + 1) ^ L) (Nat.pow_pos (Nat.succ_pos d))

/-- **THE (d+1)-ADIC ITERATE IDENTITY.** The `L`-fold tent iterate maps the grid point `j/(d+1)^L` to
the parity `(j mod 2 : ℝ)`, for `j ≤ (d+1)^L`. The analogue of `ternMap_iterate_triadic`. -/
theorem polyTentMap_iterate (d : ℕ) :
    ∀ L : ℕ, ∀ j : ℕ, j ≤ (d + 1) ^ L →
      ((polyTentMap d)^[L]) ((j : ℝ) / (d + 1) ^ L) = ((j % 2 : ℕ) : ℝ) := by
  intro L
  induction L with
  | zero =>
      intro j hj
      simp only [pow_zero, Function.iterate_zero, id_eq] at *
      interval_cases j <;> norm_num
  | succ L ih =>
      intro j hj
      rw [Function.iterate_succ_apply]
      have hstep : polyTentMap d ((j : ℝ) / (d + 1) ^ (L + 1))
          = polyLap d (min d (j / (d + 1) ^ L)) ((j : ℝ) / (d + 1) ^ (L + 1)) := by
        unfold polyTentMap; rw [polyLapIndex_grid]
      rw [hstep]
      obtain ⟨num, hnum_le, hnum_mod, hfold⟩ := polyLap_fold_grid d L j hj
      rw [hfold, ih num hnum_le, hnum_mod]

/-! ## (7) The (d+1)-ary tent layer realizing polyTentMap as a PolyMuxLayer

The tent layer has `d+1` distinct affine branches (lap `i` is `(d+1)·s - i` or `(i+1) - (d+1)·s`) gated
by the SHARED-quadratic nearest-anchor score `scoreᵢ(s) = -((d+1)·s - (i+1/2))²` (a genuine bilinear
self-attention form `Mcommon = -(d+1)²`, with only the per-expert linear/const parts varying). The
score increment `scoreᵢ - scoreᵢ₋₁ = 2((d+1)·s - i)` is affine, so the argmax cells on the line are
intervals; the (least) argmax of `s ≥ 0` is `min d ⌊(d+1)·s⌋₊ = polyLapIndex d s`, except at integer
`(d+1)·s` where the tie picks one lower — but the tent is CONTINUOUS there (adjacent laps agree), so the
carrier still equals `polyTentMap d s`. The `d+1` DISTINCT affine branches make this a genuine `(d+1)`
fold. -/

/-- **The (d+1)-ary tent layer.** Branches: lap `i` is `s ↦ (d+1)·s - i` (`i` even) or
`s ↦ (i+1) - (d+1)·s` (`i` odd). Gate scores: the shared-quadratic nearest-half-integer-anchor scores
`scoreᵢ(s) = -((d+1)·s - (i+1/2))²`, i.e. `Mcommon = -(d+1)²`, `gateLinᵢ = 2(i+1/2)(d+1)`,
`gateConstᵢ = -(i+1/2)²`. A genuine `PolyMuxLayer d` (genuinely quadratic self-attention gate). -/
def polyTentLayer (d : ℕ) : PolyMuxLayer d 1 where
  Mcommon := fun _ _ => -((d : ℝ) + 1) ^ 2
  gateLin := fun i => fun _ => 2 * ((i : ℝ) + 1 / 2) * ((d : ℝ) + 1)
  gateConst := fun i => -((i : ℝ) + 1 / 2) ^ 2
  branches := fun i =>
    if i.val % 2 = 0 then ⟨fun _ _ => (d + 1), fun _ => -(i : ℝ)⟩
    else ⟨fun _ _ => -(d + 1), fun _ => (i : ℝ) + 1⟩

/-- The tent layer's gate score at `s`: `scoreᵢ(s) = -((d+1)·s - (i+1/2))²`. -/
theorem polyTentLayer_score (d : ℕ) (i : Fin (d + 1)) (s : ℝ) :
    ((polyTentLayer d).scores i).eval (fun _ => s)
      = -(((d : ℝ) + 1) * s - ((i : ℝ) + 1 / 2)) ^ 2 := by
  rw [QuadScore.eval_coord1]
  simp only [PolyMuxLayer.scores, polyTentLayer]
  ring

/-- The score comparison: `scoreᵢ ≤ scoreⱼ ↔ |(d+1)s - (i+1/2)| ≥ |(d+1)s - (j+1/2)|` (nearer anchor
wins). We use the squared form: `scoreᵢ ≤ scoreⱼ ↔ ((d+1)s-(j+1/2))² ≤ ((d+1)s-(i+1/2))²`. -/
theorem polyTentLayer_score_le (d : ℕ) (i j : Fin (d + 1)) (s : ℝ) :
    ((polyTentLayer d).scores i).eval (fun _ => s) ≤ ((polyTentLayer d).scores j).eval (fun _ => s)
      ↔ (((d : ℝ) + 1) * s - ((j : ℝ) + 1 / 2)) ^ 2 ≤ (((d : ℝ) + 1) * s - ((i : ℝ) + 1 / 2)) ^ 2 := by
  rw [polyTentLayer_score, polyTentLayer_score]
  constructor <;> intro h <;> linarith

/-- **Tent continuity at an integer boundary.** When `(d+1)·s = k+1` (the shared boundary of laps `k`
and `k+1`), both lap formulas agree: `polyLap d k s = polyLap d (k+1) s`. -/
theorem polyLap_boundary (d k : ℕ) (s : ℝ) (hb : ((d : ℝ) + 1) * s = (k : ℝ) + 1) :
    polyLap d k s = polyLap d (k + 1) s := by
  unfold polyLap
  rcases Nat.even_or_odd k with hpar | hpar
  · obtain ⟨r, hr⟩ := hpar
    have hk : k % 2 = 0 := by omega
    have hk1 : (k + 1) % 2 = 1 := by omega
    rw [if_pos hk, if_neg (by omega)]
    rw [hb]; push_cast; ring
  · obtain ⟨r, hr⟩ := hpar
    have hk : k % 2 = 1 := by omega
    have hk1 : (k + 1) % 2 = 0 := by omega
    rw [if_neg (by omega), if_pos hk1]
    rw [hb]; push_cast; ring

/-- **THE TENT LAYER CARRIER ACTION.** For `s ∈ [0,1]`, the tent layer's carrier action equals
`polyTentMap d s`: the nearest-anchor gate `g` satisfies `g ≤ (d+1)·s ≤ g+1` (it is the closest anchor,
hence in its own lap), so on lap `g` the affine branch reproduces the lap formula; and `polyLap d g s`
coincides with `polyTentMap d s = polyLap d (min d ⌊(d+1)s⌋₊) s` (equal lap, or adjacent laps agreeing
at the shared boundary via `polyLap_boundary`). -/
theorem polyTentLayer_apply (d : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ((polyTentLayer d).applyLayer (fun _ => s)) 0 = polyTentMap d s := by
  set x : ℝ := ((d : ℝ) + 1) * s with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hxd1 : x ≤ (d : ℝ) + 1 := by
    rw [hxdef]; nlinarith [hs0, hs1, (by positivity : (0:ℝ) ≤ (d:ℝ) + 1)]
  set n : ℕ := ⌊x⌋₊ with hn
  have hnle : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hnlt : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  set g : Fin (d + 1) := (polyTentLayer d).gate (fun _ => s) with hg
  have hgmax : ∀ j : Fin (d + 1),
      ((polyTentLayer d).scores j).eval (fun _ => s) ≤ ((polyTentLayer d).scores g).eval (fun _ => s) :=
    leastArgmax_is_maximizer _ _
  have hgleast : ∀ j : Fin (d + 1), j < g →
      ((polyTentLayer d).scores j).eval (fun _ => s) < ((polyTentLayer d).scores g).eval (fun _ => s) :=
    fun j hj => leastArgmax_is_least _ _ j hj
  -- nearest-anchor: for all j, (x-(g+1/2))² ≤ (x-(j+1/2))²
  have hgclose : ∀ j : Fin (d + 1), (x - ((g : ℝ) + 1 / 2)) ^ 2 ≤ (x - ((j : ℝ) + 1 / 2)) ^ 2 := by
    intro j
    have hj := hgmax j
    rw [polyTentLayer_score, polyTentLayer_score, ← hxdef] at hj
    linarith
  -- strict version for j < g
  have hgclose_lt : ∀ j : Fin (d + 1), j < g →
      (x - ((g : ℝ) + 1 / 2)) ^ 2 < (x - ((j : ℝ) + 1 / 2)) ^ 2 := by
    intro j hj
    have h := hgleast j hj
    rw [polyTentLayer_score, polyTentLayer_score, ← hxdef] at h
    linarith
  -- Claim A: g ≤ x. If x < g then g ≥ 1 and g-1 is strictly closer, contradicting hgleast.
  have hglo : (g : ℝ) ≤ x := by
    by_contra hlt
    push Not at hlt
    have hg1 : 1 ≤ g.val := by
      by_contra h0
      have : g.val = 0 := by omega
      rw [this] at hlt; push_cast at hlt; linarith
    -- j = g - 1
    set jm : Fin (d + 1) := ⟨g.val - 1, by omega⟩ with hjm
    have hjmlt : jm < g := by
      rw [hjm, Fin.lt_def]
      show g.val - 1 < g.val
      omega
    have hjmval : (jm : ℝ) = (g : ℝ) - 1 := by rw [hjm]; push_cast [Nat.cast_sub hg1]; ring
    have hclose := hgclose_lt jm hjmlt
    rw [hjmval] at hclose
    -- (x-(g+1/2))² < (x-(g-1+1/2))² = (x-(g-1/2))² ; but x < g so g is FARTHER. contradiction.
    nlinarith [hclose, hlt]
  -- The carrier action of the gate `g` is always the lap-`g` formula.
  have hcarrier : ((polyTentLayer d).applyLayer (fun _ => s)) 0 = polyLap d g.val s := by
    simp only [PolyMuxLayer.applyLayer, ← hg]
    unfold polyLap
    by_cases hgpar : g.val % 2 = 0
    · have hb : (polyTentLayer d).branches g
          = (⟨fun _ _ => (d + 1), fun _ => -(g.val : ℝ)⟩ : AffineSelfMap 1) := by
        simp only [polyTentLayer]; rw [if_pos hgpar]
      rw [if_pos hgpar, hb, AffineSelfMap.apply_coord1]
      rw [hxdef] at *; push_cast; ring
    · have hb : (polyTentLayer d).branches g
          = (⟨fun _ _ => -(d + 1), fun _ => (g.val : ℝ) + 1⟩ : AffineSelfMap 1) := by
        simp only [polyTentLayer]; rw [if_neg hgpar]
      rw [if_neg hgpar, hb, AffineSelfMap.apply_coord1]
      rw [hxdef] at *; push_cast; ring
  -- Claim B: x ≤ g + 1 when g < d (else g = d and use the clamp).
  by_cases hgd : g.val = d
  · -- g = d: x ∈ [d, d+1], polyTentMap uses min d n = d = g.
    have hgvR : (g : ℝ) = (d : ℝ) := by exact_mod_cast hgd
    have hgloD : (d : ℝ) ≤ x := by rw [← hgvR]; exact hglo
    have hdn : d ≤ n := by
      have hlt' : (d : ℝ) < (n : ℝ) + 1 := by linarith [hnlt, hgloD]
      exact_mod_cast Nat.lt_add_one_iff.mp (by exact_mod_cast hlt')
    have hmin : min d n = d := by omega
    rw [polyTentMap, polyLapIndex, ← hxdef, ← hn, hmin, hcarrier, hgd]
  · -- g < d: x ≤ g + 1.
    have hgltd : g.val < d := by omega
    have hghi : x ≤ (g : ℝ) + 1 := by
      by_contra hlt
      push Not at hlt
      set jp : Fin (d + 1) := ⟨g.val + 1, by omega⟩ with hjp
      have hjpval : (jp : ℝ) = (g : ℝ) + 1 := by rw [hjp]; push_cast; ring
      have hclose := hgclose jp
      rw [hjpval] at hclose
      nlinarith [hclose, hlt]
    -- x ∈ [g, g+1]; n = ⌊x⌋ ∈ {g, g+1}.
    have hgvR : (g : ℝ) = (g.val : ℝ) := rfl
    have hng : g.val ≤ n := by
      have hxlt : x < (n : ℝ) + 1 := hnlt
      -- g ≤ x < n+1 ⟹ g < n+1 ⟹ g ≤ n
      have : (g.val : ℝ) < (n : ℝ) + 1 := by rw [← hgvR]; linarith [hglo]
      exact_mod_cast Nat.lt_add_one_iff.mp (by exact_mod_cast this)
    have hngle : n ≤ g.val + 1 := by
      -- n ≤ x ≤ g+1 ⟹ n ≤ g+1
      have : (n : ℝ) ≤ (g.val : ℝ) + 1 := by rw [← hgvR]; linarith [hnle, hghi]
      exact_mod_cast (by exact_mod_cast this : (n : ℝ) ≤ ((g.val + 1 : ℕ) : ℝ))
    rw [polyTentMap, polyLapIndex, ← hxdef, ← hn]
    -- min d n: since n ≤ g+1 ≤ d, min d n = n.
    have hmin : min d n = n := by omega
    rw [hmin, hcarrier]
    rcases (by omega : n = g.val ∨ n = g.val + 1) with hng' | hng'
    · rw [hng']
    · -- n = g+1: x ∈ [g, g+1] and ⌊x⌋ = g+1 ⟹ x = g+1 (the boundary). use continuity.
      have hxb : x = (g : ℝ) + 1 := by
        have h1 : (g : ℝ) + 1 ≤ x := by
          have : ((g.val + 1 : ℕ) : ℝ) ≤ x := by rw [← hng']; exact hnle
          push_cast at this; linarith
        linarith [hghi]
      rw [hng']
      exact polyLap_boundary d g.val s (by rw [← hxdef]; rw [hxb])

/-- **The tent maps the unit interval into itself.** For `s ∈ [0,1]`, `polyTentMap d s ∈ [0,1]`: on
each lap the affine formula `(d+1)s - i` or `(i+1) - (d+1)s` lands in `[0,1]`. -/
theorem polyTentMap_unit (d : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ polyTentMap d s ∧ polyTentMap d s ≤ 1 := by
  set x : ℝ := ((d : ℝ) + 1) * s with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hxd1 : x ≤ (d : ℝ) + 1 := by
    rw [hxdef]; nlinarith [hs0, hs1, (by positivity : (0:ℝ) ≤ (d:ℝ) + 1)]
  set n : ℕ := ⌊x⌋₊ with hn
  have hnle : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hnlt : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  set i : ℕ := min d n with hi
  have hile : i ≤ d := Nat.min_le_left _ _
  have hiright : i ≤ n := Nat.min_le_right _ _
  -- i ≤ x ≤ i+1 (the lap bounds): i ≤ n ≤ x, and x < n+1 ≤ ... if i = n; if i = d < n then x ≤ d+1 = i+1.
  have hilo : (i : ℝ) ≤ x := le_trans (by exact_mod_cast hiright) hnle
  have hihi : x ≤ (i : ℝ) + 1 := by
    rcases Nat.lt_or_ge n (d + 1) with hlt | hge
    · -- i = n (since min d n = n when n ≤ d) or i = d.  In either case x < n+1 and i ≥ ... use i = n.
      have hin : i = n := by omega
      rw [hin]; linarith [hnlt]
    · -- n ≥ d+1, so i = d; x ≤ d+1 = i+1
      have hid : i = d := by omega
      rw [hid]; exact hxd1
  rw [polyTentMap, polyLapIndex, ← hxdef, ← hn, ← hi]
  unfold polyLap
  by_cases hpar : i % 2 = 0
  · rw [if_pos hpar, ← hxdef]; constructor <;> [nlinarith [hilo]; nlinarith [hihi]]
  · rw [if_neg hpar, ← hxdef]; constructor <;> [nlinarith [hihi]; nlinarith [hilo]]

/-! ## (8) The iterated tent cascade and the run-coordinate identity -/

/-- The depth-`L` iterated tent cascade. -/
def polyTentCascade (d L : ℕ) : PolyCascade d 1 L := PolyCascade.mk (fun _ => polyTentLayer d)

/-- **The iterated tent run is the iterate of `polyTentMap`.** For an input `t ∈ [0,1]`, the carrier
coordinate after `m ≤ L` layers is `(polyTentMap d)^[m] t`. The induction maintains the invariant that
the running state lies in `[0,1]` (`polyTentMap_unit`). -/
theorem polyTentCascade_runUpTo_coord (d L : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ m, m ≤ L → ((polyTentCascade d L).runUpTo m (fun _ => t)) 0 = (polyTentMap d)^[m] t
      ∧ 0 ≤ (polyTentMap d)^[m] t ∧ (polyTentMap d)^[m] t ≤ 1 := by
  intro m
  induction m with
  | zero => intro _; exact ⟨rfl, ht0, ht1⟩
  | succ m ih =>
      intro hm
      obtain ⟨hcoord, hmem0, hmem1⟩ := ih (by omega)
      rw [PolyCascade.runUpTo, dif_pos (by omega : m < L)]
      have hstate : ((polyTentCascade d L).runUpTo m (fun _ => t))
          = (fun _ => ((polyTentCascade d L).runUpTo m (fun _ => t)) 0) := by
        funext i; fin_cases i; rfl
      have hval : ((polyTentLayer d).applyLayer ((polyTentCascade d L).runUpTo m (fun _ => t))) 0
          = (polyTentMap d)^[m + 1] t := by
        rw [hstate, hcoord]
        show ((polyTentLayer d).applyLayer (fun _ => (polyTentMap d)^[m] t)) 0 = _
        rw [polyTentLayer_apply d _ hmem0 hmem1, Function.iterate_succ_apply']
      refine ⟨?_, ?_, ?_⟩
      · show ((polyTentCascade d L).layers ⟨m, by omega⟩).applyLayer _ 0 = _
        exact hval
      · rw [Function.iterate_succ_apply']; exact (polyTentMap_unit d _ hmem0 hmem1).1
      · rw [Function.iterate_succ_apply']; exact (polyTentMap_unit d _ hmem0 hmem1).2

/-- The full run's carrier coordinate is `(polyTentMap d)^[L] t` for `t ∈ [0,1]`. -/
theorem polyTentCascade_run_coord (d L : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((polyTentCascade d L).run (fun _ => t)) 0 = (polyTentMap d)^[L] t :=
  (polyTentCascade_runUpTo_coord d L t ht0 ht1 L (le_refl _)).1

/-! ## (9) The tent route and its (d+1)^L alternation count on the (d+1)-adic grid -/

/-- The tent route scores: threshold at `½` on the final coordinate (`route = 0` iff value `≥ ½`).
The same affine readout as the dyadic/triadic tent. -/
def polyTentRouteScores : Fin 2 → AffineFunctional 1 :=
  fun j => if j = 0 then ⟨fun _ => 1, -(1 / 2)⟩ else ⟨fun _ => -1, 1 / 2⟩

theorem polyTentRouteScores_eval (s : Fin 1 → ℝ) :
    (polyTentRouteScores 0).eval s = s 0 - 1 / 2 ∧ (polyTentRouteScores 1).eval s = 1 / 2 - s 0 := by
  refine ⟨?_, ?_⟩
  · show (polyTentRouteScores 0).eval s = s 0 - 1 / 2
    have : polyTentRouteScores 0 = (⟨fun _ => 1, -(1 / 2)⟩ : AffineFunctional 1) := by
      simp [polyTentRouteScores]
    rw [this, AffineFunctional.eval_coord1]; ring
  · show (polyTentRouteScores 1).eval s = 1 / 2 - s 0
    have : polyTentRouteScores 1 = (⟨fun _ => -1, 1 / 2⟩ : AffineFunctional 1) := by
      simp [polyTentRouteScores]
    rw [this, AffineFunctional.eval_coord1]; ring

/-- The tent route value at `t ∈ [0,1]`: `0` iff the final coordinate `≥ ½`. -/
theorem polyTentRoute_eq (d L : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    polyCascadeRoute (polyTentCascade d L) polyTentRouteScores (fun _ => t)
      = if 1 / 2 ≤ (polyTentMap d)^[L] t then 0 else 1 := by
  unfold polyCascadeRoute
  rw [leastArgmax_two]
  obtain ⟨h0, h1⟩ := polyTentRouteScores_eval ((polyTentCascade d L).run (fun _ => t))
  simp only [h0, h1, polyTentCascade_run_coord d L t ht0 ht1]
  by_cases hc : (1 : ℝ) / 2 ≤ (polyTentMap d)^[L] t
  · rw [if_pos (by linarith), if_pos hc]
  · rw [if_neg (by push Not at hc ⊢; linarith), if_neg hc]

/-- **The route value on the (d+1)-adic grid point `j/(d+1)^L` is `1 − (j mod 2)`.** -/
theorem polyTentRoute_on_grid (d L : ℕ) (j : ℕ) (hj : j ≤ (d + 1) ^ L) :
    polyCascadeRoute (polyTentCascade d L) polyTentRouteScores (fun _ => (j : ℝ) / (d + 1) ^ L)
      = if j % 2 = 0 then 1 else 0 := by
  have hpowpos : (0 : ℝ) < (d + 1) ^ L := by positivity
  have ht0 : 0 ≤ (j : ℝ) / (d + 1) ^ L := by positivity
  have ht1 : (j : ℝ) / (d + 1) ^ L ≤ 1 := by
    rw [div_le_one hpowpos]; exact_mod_cast hj
  rw [polyTentRoute_eq d L _ ht0 ht1, polyTentMap_iterate d L j hj]
  rcases (by omega : j % 2 = 0 ∨ j % 2 = 1) with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- The increasing (d+1)-adic grid of `(d+1)^L + 1` points `k ↦ k/(d+1)^L`. -/
def polyGrid (d L : ℕ) : Fin ((d + 1) ^ L + 1) → ℝ := fun k => (k.val : ℝ) / (d + 1) ^ L

theorem polyGrid_increasing (d L : ℕ) : Increasing (polyGrid d L) := by
  intro i j hij
  unfold polyGrid
  have hpow : (0 : ℝ) < (d + 1) ^ L := by positivity
  have hlt : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast (Fin.lt_def.mp hij)
  exact div_lt_div_of_pos_right hlt hpow

/-- The tent route along the (d+1)-adic grid, as a function of the grid index `k`. -/
theorem polyTentRoute_polyGrid (d L : ℕ) (k : Fin ((d + 1) ^ L + 1)) :
    polyCascadeRoute (polyTentCascade d L) polyTentRouteScores (fun _ => polyGrid d L k)
      = if k.val % 2 = 0 then 1 else 0 := by
  unfold polyGrid
  exact polyTentRoute_on_grid d L k.val (by have := k.isLt; omega)

/-- **THE WITNESS ALTERNATION COUNT `= (d+1)^L`.** The depth-`L` iterated tent route changes value at
EVERY one of the `(d+1)^L` adjacent pairs of the (d+1)-adic grid (consecutive grid indices have opposite
parity), so `seqChanges = (d+1)^L`. The analogue of `ternTentRoute3_alternations_eq = 3^L`. -/
theorem polyTentRoute_alternations_eq (d L : ℕ) :
    seqChanges (fun k => polyCascadeRoute (polyTentCascade d L) polyTentRouteScores
        (fun _ => polyGrid d L k)) = (d + 1) ^ L := by
  unfold seqChanges
  have hall : (Finset.univ.filter (fun i : Fin ((d + 1) ^ L) =>
      (fun k => polyCascadeRoute (polyTentCascade d L) polyTentRouteScores
        (fun _ => polyGrid d L k)) i.castSucc
      ≠ (fun k => polyCascadeRoute (polyTentCascade d L) polyTentRouteScores
        (fun _ => polyGrid d L k)) i.succ)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    simp only
    rw [polyTentRoute_polyGrid, polyTentRoute_polyGrid]
    have hcs : (i.castSucc : Fin ((d + 1) ^ L + 1)).val = i.val := Fin.val_castSucc i
    have hsc : (i.succ : Fin ((d + 1) ^ L + 1)).val = i.val + 1 := Fin.val_succ i
    rw [hcs, hsc]
    rcases Nat.even_or_odd i.val with he | ho
    · obtain ⟨r, hr⟩ := he
      rw [if_pos (by omega), if_neg (by omega)]
      decide
    · obtain ⟨r, hr⟩ := ho
      rw [if_neg (by omega), if_pos (by omega)]
      decide
  rw [hall, Finset.card_univ, Fintype.card_fin]

/-! ## (10) The depth-monotone embedding `polyDepthGrade d L ⊆ polyDepthGrade d (L+1)` -/

/-- The do-nothing arity-`(d+1)` layer: all-equal gate scores, all branches the identity. Its action is
the identity regardless of the gate. -/
def polyIdLayer (d D : ℕ) : PolyMuxLayer d D where
  Mcommon := fun _ _ => 0
  gateLin := fun _ _ => 0
  gateConst := fun _ => 0
  branches := fun _ => AffineSelfMap.id D

@[simp] theorem polyIdLayer_applyLayer {d D : ℕ} (x : Fin D → ℝ) :
    (polyIdLayer d D).applyLayer x = x := by
  simp only [PolyMuxLayer.applyLayer]
  show ((polyIdLayer d D).branches _).apply x = x
  have : ∀ i : Fin (d + 1), (polyIdLayer d D).branches i = AffineSelfMap.id D := fun _ => rfl
  rw [this]; exact AffineSelfMap.id_apply x

/-- Append the do-nothing identity layer at the last index. -/
def appendPolyIdLayers {d D L : ℕ} (layers : Fin L → PolyMuxLayer d D) :
    Fin (L + 1) → PolyMuxLayer d D :=
  fun i => if h : i.val < L then layers ⟨i.val, h⟩ else polyIdLayer d D

theorem appendPolyId_runUpTo_eq {d D L : ℕ} (layers : Fin L → PolyMuxLayer d D) (x : Fin D → ℝ) :
    ∀ m, m ≤ L →
      (PolyCascade.mk (appendPolyIdLayers layers)).runUpTo m x
        = (PolyCascade.mk layers).runUpTo m x := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      have hmL : m < L := by omega
      have hmL1 : m < L + 1 := by omega
      rw [PolyCascade.runUpTo, PolyCascade.runUpTo, dif_pos hmL1, dif_pos hmL]
      have hlayer : appendPolyIdLayers layers ⟨m, hmL1⟩ = layers ⟨m, hmL⟩ := by
        rw [appendPolyIdLayers, dif_pos hmL]
      have hstate := ih (by omega)
      show ((PolyCascade.mk (appendPolyIdLayers layers)).layers ⟨m, hmL1⟩).applyLayer
            ((PolyCascade.mk (appendPolyIdLayers layers)).runUpTo m x)
          = ((PolyCascade.mk layers).layers ⟨m, hmL⟩).applyLayer
            ((PolyCascade.mk layers).runUpTo m x)
      rw [hstate]
      show (appendPolyIdLayers layers ⟨m, hmL1⟩).applyLayer ((PolyCascade.mk layers).runUpTo m x)
          = (layers ⟨m, hmL⟩).applyLayer ((PolyCascade.mk layers).runUpTo m x)
      rw [hlayer]

/-- **APPEND-IDENTITY RUN INVARIANCE.** -/
theorem appendPolyId_run_eq {d D L : ℕ} (layers : Fin L → PolyMuxLayer d D) (x : Fin D → ℝ) :
    (PolyCascade.mk (appendPolyIdLayers layers)).run x = (PolyCascade.mk layers).run x := by
  show (PolyCascade.mk (appendPolyIdLayers layers)).runUpTo (L + 1) x = _
  rw [PolyCascade.runUpTo, dif_pos (by omega : L < L + 1)]
  have hlast : (PolyCascade.mk (appendPolyIdLayers layers)).layers ⟨L, by omega⟩
      = polyIdLayer d D := by
    show appendPolyIdLayers layers ⟨L, by omega⟩ = polyIdLayer d D
    rw [appendPolyIdLayers, dif_neg (by simp)]
  rw [hlast]
  have hpre := appendPolyId_runUpTo_eq layers x L (le_refl L)
  rw [hpre]
  show (polyIdLayer d D).applyLayer ((PolyCascade.mk layers).runUpTo L x)
      = (PolyCascade.mk layers).run x
  rw [polyIdLayer_applyLayer]
  rfl

/-- **DEPTH-MONOTONE EMBEDDING `polyDepthGrade d L ⊆ polyDepthGrade d (L+1)`.** -/
theorem polyDepthGrade_succ_subset {d L : ℕ} :
    polyDepthGrade d L ⊆ polyDepthGrade d (L + 1) := by
  rintro f ⟨layers, rs, rfl⟩
  refine ⟨appendPolyIdLayers layers, rs, ?_⟩
  funext x
  simp only [polyCascadeRoute]
  rw [appendPolyId_run_eq layers x]

/-! ## (11) THE GENERAL-`d` `∀L` DEPTH SEPARATION -/

/-- The depth-`L` tent route, packaged as a route function; it lies in `polyDepthGrade d L`. -/
def polyTentRouteFn (d L : ℕ) : (Fin 1 → ℝ) → Fin 2 :=
  polyCascadeRoute (polyTentCascade d L) polyTentRouteScores

theorem polyTentRouteFn_mem_grade (d L : ℕ) :
    polyTentRouteFn d L ∈ polyDepthGrade d L :=
  ⟨fun _ => polyTentLayer d, polyTentRouteScores, rfl⟩

/-- **Non-membership (`∀L`, `d ≥ 1`): the depth-`(L+1)` tent route is NOT in `polyDepthGrade d L`.**
If it were a depth-`L` arity-`(d+1)` route, then on the increasing (d+1)-adic grid `polyGrid (L+1)` it
would change `≤ (d+1)^{L+1} − 1` times (`polyRoute_alternations_le`); but it changes `(d+1)^{L+1}` times
(`polyTentRoute_alternations_eq`), a contradiction. -/
theorem polyTentRouteFn_not_mem_grade (d L : ℕ) (hd : 1 ≤ d) :
    polyTentRouteFn d (L + 1) ∉ polyDepthGrade d L := by
  rintro ⟨layers, rs, hf⟩
  have hwit : seqChanges (fun k => polyTentRouteFn d (L + 1) (fun _ => polyGrid d (L + 1) k))
      = (d + 1) ^ (L + 1) := polyTentRoute_alternations_eq d (L + 1)
  have hbound : seqChanges (fun k => polyTentRouteFn d (L + 1) (fun _ => polyGrid d (L + 1) k))
      ≤ (d + 1) ^ (L + 1) - 1 := by
    have hrw : (fun k => polyTentRouteFn d (L + 1) (fun _ => polyGrid d (L + 1) k))
        = fun k => polyCascadeRoute (PolyCascade.mk layers) rs
            (fun _ => polyGrid d (L + 1) k) := by
      funext k; rw [hf]
    rw [hrw]
    exact polyRoute_alternations_le hd layers rs (polyGrid d (L + 1)) (polyGrid_increasing d (L + 1))
  rw [hwit] at hbound
  have hpow : 1 ≤ (d + 1) ^ (L + 1) := Nat.one_le_pow _ _ (Nat.succ_pos d)
  omega

/-- **THE GENERAL-`d` `∀L` DEPTH-LADDER SEPARATION.** For every degree `d ≥ 1` and every depth `L`,
`polyDepthGrade d L ⊂ polyDepthGrade d (L+1)`.

The `⊆` is the depth-monotone identity-layer embedding (`polyDepthGrade_succ_subset`); the strictness is
the iterated `(d+1)`-ary tent witness: the depth-`(L+1)` tent route lies in grade `(L+1)`
(`polyTentRouteFn_mem_grade`) but NOT in grade `L` (`polyTentRouteFn_not_mem_grade`, via the base-`(d+1)`
route bound `polyRoute_alternations_le`). The per-layer gate folds the line into `d+1` monotone laps
with `d+1` DISTINCT affine branches, so depth buys a genuine base-`(d+1)` fold at every rung.

This generalizes the affine `d = 1` (`binCascadeGrade_ssubset_succ`) and quadratic `d = 2`
(`quadDepthGrade3_ssubset_succ`) separations to arbitrary degree `d`; the induction is parametrised in
`d`. -/
theorem polyDepthGrade_ssubset_succ (d L : ℕ) (hd : 1 ≤ d) :
    polyDepthGrade d L ⊂ polyDepthGrade d (L + 1) := by
  refine ⟨polyDepthGrade_succ_subset, ?_⟩
  intro hsubset
  have hmem : polyTentRouteFn d (L + 1) ∈ polyDepthGrade d (L + 1) :=
    polyTentRouteFn_mem_grade d (L + 1)
  have h1 : polyTentRouteFn d (L + 1) ∈ polyDepthGrade d L := hsubset hmem
  exact polyTentRouteFn_not_mem_grade d L hd h1

end TLT.TemperedDesignLaw
