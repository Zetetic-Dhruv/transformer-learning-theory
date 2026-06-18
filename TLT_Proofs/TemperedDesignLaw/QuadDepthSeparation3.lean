/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.QuadDepthSeparation

/-!
# The ARITY-3 second-order DEPTH separation for quadratic-gated cascades (multi-expert k=3)

This file proves a GENUINE general-`L` second-order DEPTH separation
`quadDepthGrade3 1 2 L ⊂ quadDepthGrade3 1 2 (L+1)` for EVERY `L`, via the **arity-3** route.

It is a **NEW grade** and a **DIFFERENT statement** than the existing arity-2 grade
`quadDepthGrade` (`QuadraticDepth.lean` / `QuadDepthSeparation.lean`). There the iterated quadratic
tent only achieves the base-2 fold rate `2^L`, because the arity-2 quadratic gate's two OUTER regions
share branch `0` (a shared-branch collapse), so the fold factor is `2`, not `3`, and the general-`L`
separation does NOT close in that model (documented obstruction in `QuadDepthSeparation.lean`).

The arity-3 route AVOIDS that collapse: a `QuadMuxLayer3` has `3` DISTINCT affine branches gated by
`leastArgmax` of `3` quadratic scores. An iterated **ternary tent** with `3` distinct laps achieves a
genuine `3^(L+1)` route alternations against the base-3 ceiling `3^(L+1) - 1`. This is a multi-expert
(`k = 3`) quadratic router, faithful to `k`-expert self-attention.

## The pieces (all sorry-free; mirror of `MuxDepthLadderGeneral.lean` at base 3)

1. `QuadMuxLayer3` / `quadDepthGrade3` (the grade): an arity-3 quadratic-gated layer
   (`branches : Fin 3 → AffineSelfMap 1`, gate = `leastArgmax` of `3` quadratic scores), iterated to a
   depth-`L` cascade `QuadCascade3`, with the arity-2 affine readout grade `quadDepthGrade3`.

2. The base-3 block-refine engine `seqChanges_blockRefine3_le`: a `Fin 3`-valued bit with the per-block
   **global no-return** contract (each value's win-set within a `u`-constant block is an interval)
   flips `≤ 2` per block, so the paired sequence changes `≤ 3·seqChanges u + 2`. This is the `Fin 3`
   analogue of `seqChanges_blockRefine_le_two`; the per-block fiber-card-`≤ 2` comes from no-return into
   a 3-element codomain.

3. The depth-`L` line/route alternation bound `≤ 3^(L+1) - 1` (`quadRoute3_alternations_le`): the
   trace bit on each fiber is an `AffineLines 3` argmax of `t` (gate scores affine in the carrier),
   which has GLOBAL no-return; compose the base-3 block-refine over depth and add one more for the route.

4. The ternary tent generator `ternTentLayer3` with `3` distinct affine branches realizing the triadic
   fold `T(s) = ternMap s` (up-down-up onto `[0,1]`), and its iterate `ternMap^[L]`.

5. `ternTentRoute3_alternations_eq = 3^(L+1)` on the triadic grid `j/3^(L+1)` (the triadic identity
   `ternMap^[L](j/3^L) = the parity-3 phase`, the base-3 analogue of `tentMap_iterate_dyadic`).

6. `quadDepthGrade3_ssubset_succ`: the depth-`(L+1)` ternary tent (`3^(L+1) > 3^(L+1)-1`) is `∉` grade
   `L`, `∈` grade `L+1`.
-/

open scoped BigOperators
open Set

noncomputable section

open Classical

namespace TLT.TemperedDesignLaw

open TLT.TemperedDesignLaw.MuxHierarchy

/-! ## (1) The arity-3 quadratic-gated, affine-branched cascade -/

/-- An arity-3 quadratic-gated, affine-branched mux layer on `Fin d → ℝ`: `3` quadratic gate scores
and `3` affine branch maps (a multi-expert `k = 3` quadratic router).

The gate scores **share a common quadratic part** `Mcommon` (only their linear/constant parts vary).
This is exactly the self-attention / nearest-anchor gate `scoreᵢ(x) = ⟨Qx,Kx⟩ + ⟨vᵢ,x⟩ + cᵢ`, where the
bilinear form `⟨Qx,Kx⟩` is shared across experts and only the per-expert linear bias differs (the
"prototype" `vᵢ`). It is genuinely quadratic (a real bilinear self-attention form `xᵀ(QᵀK)x`), but the
expert-vs-expert *comparison* `scoreᵢ − scoreⱼ` is affine in `x` (the shared `Mcommon` cancels), so the
argmax cells on any line are intervals — exactly the nearest-anchor Voronoi structure that gives the
tight base-3 fold. The arity-2 grade `QuadMuxLayer` instead allowed independent quadratic parts; for
the *depth ladder* what matters is the comparison geometry, and this shared-form gate is the faithful
multi-expert one. -/
structure QuadMuxLayer3 (d : ℕ) where
  /-- The shared quadratic (self-attention bilinear) part of every gate score. -/
  Mcommon : Fin d → Fin d → ℝ
  /-- The per-expert linear part of the gate score. -/
  gateLin : Fin 3 → Fin d → ℝ
  /-- The per-expert constant part of the gate score. -/
  gateConst : Fin 3 → ℝ
  branches : Fin 3 → AffineSelfMap d

/-- The `i`-th gate score of an arity-3 layer: a quadratic score with the shared `Mcommon` and the
per-expert linear/constant parts. -/
def QuadMuxLayer3.scores {d : ℕ} (Lyr : QuadMuxLayer3 d) (i : Fin 3) : QuadScore d :=
  ⟨Lyr.Mcommon, Lyr.gateLin i, Lyr.gateConst i⟩

/-- The branch index selected by an arity-3 layer at `x`: the `leastArgmax` of its `3` scores. -/
def QuadMuxLayer3.gate {d : ℕ} (Lyr : QuadMuxLayer3 d) (x : Fin d → ℝ) : Fin 3 :=
  leastArgmax (fun i => (Lyr.scores i).eval x) (by norm_num)

/-- The map of an arity-3 layer: gate by the argmax of the `3` quadratic scores, apply the selected
affine branch. -/
def QuadMuxLayer3.applyLayer {d : ℕ} (Lyr : QuadMuxLayer3 d) (x : Fin d → ℝ) : Fin d → ℝ :=
  (Lyr.branches (Lyr.gate x)).apply x

/-- A depth-`L` arity-3 quadratic-gated cascade. -/
structure QuadCascade3 (d L : ℕ) where
  layers : Fin L → QuadMuxLayer3 d

/-- Run the first `m` layers (input-first). -/
def QuadCascade3.runUpTo {d L : ℕ} (C : QuadCascade3 d L) : ℕ → (Fin d → ℝ) → (Fin d → ℝ)
  | 0, x => x
  | (m + 1), x =>
      if h : m < L then
        (C.layers ⟨m, h⟩).applyLayer (C.runUpTo m x)
      else C.runUpTo m x

/-- The composed region map: run all `L` layers. -/
def QuadCascade3.run {d L : ℕ} (C : QuadCascade3 d L) (x : Fin d → ℝ) : Fin d → ℝ :=
  C.runUpTo L x

/-- The active-branch trace, in `Fin L → Fin 3`. -/
def QuadCascade3.trace {d L : ℕ} (C : QuadCascade3 d L) (x : Fin d → ℝ) : Fin L → Fin 3 :=
  fun i => (C.layers i).gate (C.runUpTo i.val x)

/-- The arity-2 affine argmax readout of an arity-3 cascade (the route into `Fin 2`). -/
def quadCascade3Route {d L : ℕ} (C : QuadCascade3 d L) (routeScores : Fin 2 → AffineFunctional d) :
    (Fin d → ℝ) → Fin 2 :=
  fun x => leastArgmax (fun j => (routeScores j).eval (C.run x)) (by norm_num)

/-- **The arity-3 quadratic depth grade.** Routes `(Fin d → ℝ) → Fin 2` realizable by SOME depth-`L`
arity-3 quadratic-gated cascade with SOME `2` affine readout scores. NEW grade, distinct from the
arity-2 `quadDepthGrade`. -/
def quadDepthGrade3 (d L : ℕ) : Set ((Fin d → ℝ) → Fin 2) :=
  { f | ∃ (layers : Fin L → QuadMuxLayer3 d) (routeScores : Fin 2 → AffineFunctional d),
      f = quadCascade3Route ⟨layers⟩ routeScores }

/-! ## (2) Affine-on-fiber: `C.run` is a fixed AFFINE map on each trace-fiber (mirror) -/

/-- The fixed affine map realizing `runUpTo m` on the trace-fiber of `x₀`. -/
def QuadCascade3.prefixMap {d L : ℕ} (C : QuadCascade3 d L) (x₀ : Fin d → ℝ) :
    ℕ → AffineSelfMap d
  | 0 => AffineSelfMap.id d
  | (m + 1) =>
      if h : m < L then
        (C.layers ⟨m, h⟩).branches (C.trace x₀ ⟨m, h⟩) |>.comp (C.prefixMap x₀ m)
      else C.prefixMap x₀ m

/-- The fixed affine self-map agreeing with `C.run` on the trace-fiber of `x₀`. -/
def QuadCascade3.fiberMap {d L : ℕ} (C : QuadCascade3 d L) (x₀ : Fin d → ℝ) : AffineSelfMap d :=
  C.prefixMap x₀ L

/-- The **partial-trace fiber** predicate. -/
def QuadCascade3.PFiber {d L : ℕ} (C : QuadCascade3 d L) (x₀ y : Fin d → ℝ) (m : ℕ) : Prop :=
  ∀ i : Fin L, i.val < m → C.trace y i = C.trace x₀ i

/-- **PARTIAL affine-on-fiber.** -/
theorem QuadCascade3.runUpTo_eq_prefixMap_on_pfiber {d L : ℕ} (C : QuadCascade3 d L)
    (x₀ y : Fin d → ℝ) :
    ∀ m, C.PFiber x₀ y m → C.runUpTo m y = (C.prefixMap x₀ m).apply y := by
  intro m
  induction m with
  | zero => intro _; simp [QuadCascade3.runUpTo, QuadCascade3.prefixMap]
  | succ m ih =>
      intro hpf
      rw [QuadCascade3.runUpTo, QuadCascade3.prefixMap]
      by_cases h : m < L
      · rw [dif_pos h, dif_pos h]
        have hpf_m : C.PFiber x₀ y m := fun i hi => hpf i (Nat.lt_succ_of_lt hi)
        rw [AffineSelfMap.comp_apply, ← ih hpf_m]
        have hgate : (C.layers ⟨m, h⟩).gate (C.runUpTo m y) = C.trace x₀ ⟨m, h⟩ := by
          have hbit : C.trace y ⟨m, h⟩ = C.trace x₀ ⟨m, h⟩ := hpf ⟨m, h⟩ (Nat.lt_succ_self m)
          simpa [QuadCascade3.trace] using hbit
        simp only [QuadMuxLayer3.applyLayer, hgate]
      · rw [dif_neg h, dif_neg h]
        exact ih (fun i hi => hpf i (Nat.lt_succ_of_lt hi))

/-- **FULL affine-on-fiber.** -/
theorem QuadCascade3.run_eq_on_fiber {d L : ℕ} (C : QuadCascade3 d L) (x₀ y : Fin d → ℝ)
    (hfib : C.trace y = C.trace x₀) :
    C.run y = (C.fiberMap x₀).apply y := by
  rw [QuadCascade3.run, QuadCascade3.fiberMap]
  apply C.runUpTo_eq_prefixMap_on_pfiber x₀ y L
  intro i _; rw [hfib]

/-! ## (3) The base-3 block-refine for a `Fin 3` bit with per-block global no-return

The combinatorial engine of the arity-3 `∀L` ladder. We refine a coarse sequence `u` by a `Fin 3`
bit `b` whose value-fibers, on every `u`-constant index interval, are no-return (each value once left
never recurs, i.e. each win-set is a contiguous block). With 3 values that forces `≤ 2` `b`-flips per
`u`-block, so (mirroring `seqChanges_blockRefine_le_two`) the `blockOf2`-fibers over the `b`-only flips
have card `≤ 2`, giving `|Bonly| ≤ 2·(|U| + 1)` and `seqChanges (u, b) ≤ |U| + |Bonly| ≤ 3·|U| + 2`. -/

/-- **THE BASE-3 BLOCK-REFINE FOR A `Fin 3` BIT.** Let `u : Fin(m+1)→A`, `b : Fin(m+1)→Fin 3`, and
suppose `b` has the **per-block global no-return** property: on any index interval `[a,d]` on which `u`
is constant, for EVERY value `c` the `c`-fiber of `b` inside `[a,d]` is no-return. Then the paired
sequence `(u, b)` changes at most `3 · seqChanges u + 2` times. The `Fin 3` analogue of
`seqChanges_blockRefine_le_two`. -/
theorem seqChanges_blockRefine3_le {A : Type*} [DecidableEq A] {m : ℕ}
    (u : Fin (m + 1) → A) (b : Fin (m + 1) → Fin 3)
    (hblock : ∀ a d : Fin (m + 1), a ≤ d →
      (∀ e, a ≤ e → e ≤ d → u e = u a) →
      ∀ c : Fin 3, ∀ p r s : Fin (m + 1), a ≤ p → p ≤ s → s ≤ r → r ≤ d →
        b p = c → b r = c → b s = c) :
    seqChanges (fun k => (u k, b k)) ≤ 3 * seqChanges u + 2 := by
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
  -- The core: every blockOf2-fiber over Bonly has card ≤ 2.
  have hfib : ∀ q : ℕ, (Bonly.filter (fun i => blockOf2 u i = q)).card ≤ 2 := by
    intro q
    set F : Finset (Fin m) := Bonly.filter (fun i => blockOf2 u i = q) with hF
    by_contra hcon
    push Not at hcon  -- 2 < F.card, i.e. card ≥ 3
    -- card ≥ 3: there exist three distinct indices in F.  Use that F lies in a single u-block.
    have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
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
    -- lo < hi (else card ≤ 1)
    have hlohi : lo < hi := by
      rcases lt_or_eq_of_le (F.min'_le _ hhi_mem) with h | h
      · exact h
      · exfalso
        have hall : ∀ x ∈ F, x = lo := by
          intro x hx
          have h1 : lo ≤ x := F.min'_le _ hx
          have h2 : x ≤ hi := F.le_max' _ hx
          rw [← h] at h2; exact le_antisymm h2 h1
        have : F ⊆ {lo} := fun x hx => Finset.mem_singleton.mpr (hall x hx)
        have := Finset.card_le_card this
        simp at this; omega
    have huconst : ∀ e, lo.castSucc ≤ e → e ≤ hi.succ → u e = u lo.castSucc :=
      u_const_on_block u lo hi hlohi hlo_u hhi_u (hlo_q.trans hhi_q.symm)
    have hcd : (lo.castSucc : Fin (m+1)) ≤ hi.succ := by
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; have : lo.val ≤ hi.val := le_of_lt hlohi
      omega
    -- ordering helper for any F-element
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
    -- no-return on the block, for every value c
    have hnr : ∀ c : Fin 3, ∀ p r s : Fin (m + 1), lo.castSucc ≤ p → p ≤ s → s ≤ r → r ≤ hi.succ →
        b p = c → b r = c → b s = c :=
      hblock lo.castSucc hi.succ hcd huconst
    -- The change-indices in F, mapped by `i ↦ b i.succ`, inject into `univ \ {b lo.castSucc}`.
    -- This is the localized `seqChanges_le_of_noReturn` argument, giving |F| ≤ card (Fin 3) - 1 = 2.
    set φ : Fin m → Fin 3 := fun i => b i.succ with hφ
    have hinj : ∀ x ∈ F, ∀ x' ∈ F, φ x = φ x' → x = x' := by
      intro x hx x' hx' heq0
      have heq : b x.succ = b x'.succ := heq0
      by_contra hne
      have hxb : b x.castSucc ≠ b x.succ :=
        ((Finset.mem_filter.mp ((Finset.mem_filter.mp hx).1)).2).2
      have hx'b : b x'.castSucc ≠ b x'.succ :=
        ((Finset.mem_filter.mp ((Finset.mem_filter.mp hx').1)).2).2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · -- x < x' : p = x.succ, r = x'.succ, s = x'.castSucc all = φ x (= b x.succ)
        have ho1 : (lo.castSucc : Fin (m+1)) ≤ x.succ := le_trans (hFbound x hx).1 (hFbound x hx).2.1
        have hps : (x.succ : Fin (m+1)) ≤ x'.castSucc := by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          simp only [Fin.lt_def] at hlt; omega
        have hsr : (x'.castSucc : Fin (m+1)) ≤ x'.succ := (hFbound x' hx').2.1
        have := hnr (b x.succ) x.succ x'.succ x'.castSucc ho1 hps hsr (hFbound x' hx').2.2 rfl heq.symm
        exact hx'b (this.trans heq)
      · -- x' < x : p = x'.succ, r = x.succ, s = x.castSucc all = φ x' (= b x'.succ)
        have ho1 : (lo.castSucc : Fin (m+1)) ≤ x'.succ := le_trans (hFbound x' hx').1 (hFbound x' hx').2.1
        have hps : (x'.succ : Fin (m+1)) ≤ x.castSucc := by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          simp only [Fin.lt_def] at hgt; omega
        have hsr : (x.castSucc : Fin (m+1)) ≤ x.succ := (hFbound x hx).2.1
        have := hnr (b x'.succ) x'.succ x.succ x.castSucc ho1 hps hsr (hFbound x hx).2.2 rfl heq
        exact hxb (this.trans heq.symm)
    -- the image misses `b lo.castSucc`
    have hmiss : ∀ x ∈ F, φ x ≠ b lo.castSucc := by
      intro x hx heq00
      have heq0 : b x.succ = b lo.castSucc := heq00
      have hxb : b x.castSucc ≠ b x.succ :=
        ((Finset.mem_filter.mp ((Finset.mem_filter.mp hx).1)).2).2
      -- p = lo.castSucc, r = x.succ, s = x.castSucc all = b lo.castSucc
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
    have hcard_le : (F.image φ).card ≤ (Finset.univ \ {b lo.castSucc} : Finset (Fin 3)).card :=
      Finset.card_le_card hsubF
    have hsdiff : (Finset.univ \ {b lo.castSucc} : Finset (Fin 3)).card = 2 := by
      rw [Finset.card_univ_diff]
      simp
    omega
  -- |Bonly| ≤ 2·(image card) ≤ 2·(|U|+1)
  have hBonly_card : Bonly.card ≤ 2 * (U.card + 1) := by
    have h1 : Bonly.card ≤ 2 * (Bonly.image (blockOf2 u)).card :=
      card_le_two_mul_image Bonly (blockOf2 u) hfib
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
    omega
  have htotal : seqChanges (fun k => (u k, b k)) ≤ U.card + Bonly.card := by
    unfold seqChanges
    calc _ ≤ (U ∪ Bonly).card := Finset.card_le_card hsub
      _ ≤ U.card + Bonly.card := Finset.card_union_le _ _
  have hUcard : U.card = seqChanges u := rfl
  omega

/-! ## (4) The geometric bridge: the shared-form gate through an affine map is an `AffineLines 3` argmax

The single new geometric ingredient. The shared quadratic part `Mcommon` contributes the SAME value to
every gate score, and `leastArgmax` depends only on the score comparisons, so it cancels: the gate, as
a function of the line parameter `t`, is the `AffineLines 3` argmax of the per-expert affine residuals.
`AffineLines 3` argmax win-sets are intervals (`AffineLines.arg_win_ordConnected`), giving GLOBAL
no-return — the input the base-3 block-refine consumes. -/

/-- **Adding a common term to all entries preserves `leastArgmax`.** -/
theorem leastArgmax_add_const {k : ℕ} (v : Fin k → ℝ) (c : ℝ) (hk : 0 < k) :
    leastArgmax (fun i => c + v i) hk = leastArgmax v hk := by
  refine isLeastArgmax_unique v _ _ ?_ (leastArgmax_spec v hk)
  obtain ⟨hmax, hlt⟩ := leastArgmax_spec (fun i => c + v i) hk
  refine ⟨fun j => ?_, fun j hj => ?_⟩
  · have := hmax j; simp only at this; linarith
  · have := hlt j hj; simp only at this; linarith

/-- **THE GEOMETRIC BRIDGE.** Given an arity-3 layer `Lyr` and a fixed affine self-map `A` on
`Fin 1 → ℝ`, the gate `Lyr.gate (A.apply ![t])`, as a function of `t`, equals `g.arg` for the explicit
`AffineLines 3` `g` whose line `i` is the per-expert affine residual
`t ↦ gateLin i 0 · (A.mat 0 0 · t + A.shift 0) + gateConst i`. The shared `Mcommon` part cancels. -/
theorem quadGate3_comp_affine_eq_arg (Lyr : QuadMuxLayer3 1) (A : AffineSelfMap 1) (t : ℝ) :
    Lyr.gate (A.apply (fun _ => t))
      = (AffineLines.mk
          (fun i => Lyr.gateLin i 0 * A.mat 0 0)
          (fun i => Lyr.gateLin i 0 * A.shift 0 + Lyr.gateConst i)).arg
          (by norm_num) t := by
  unfold QuadMuxLayer3.gate AffineLines.arg
  -- the score at A.apply ![t] = Mcommon-term (shared) + affine residual
  set s := (A.apply (fun _ => t)) 0 with hs
  have hsc : ∀ i, (Lyr.scores i).eval (A.apply (fun _ => t))
      = Lyr.Mcommon 0 0 * s^2 + (Lyr.gateLin i 0 * s + Lyr.gateConst i) := by
    intro i
    rw [QuadScore.eval_coord1]
    simp only [QuadMuxLayer3.scores, hs]
    ring
  have hsval : s = A.mat 0 0 * t + A.shift 0 := by rw [hs, AffineSelfMap.apply_coord1]
  -- pull out the common term
  have hrw : (fun i => (Lyr.scores i).eval (A.apply (fun _ => t)))
      = (fun i => Lyr.Mcommon 0 0 * s^2
          + (AffineLines.mk (fun i => Lyr.gateLin i 0 * A.mat 0 0)
              (fun i => Lyr.gateLin i 0 * A.shift 0 + Lyr.gateConst i)).val i t) := by
    funext i; rw [hsc i]
    congr 1
    unfold AffineLines.val
    rw [hsval]; ring
  rw [hrw, leastArgmax_add_const]

/-! ## (5) The per-block GLOBAL no-return of an `AffineLines 3` argmax (feeding the block-refine)

An `AffineLines 3` argmax has GLOBAL no-return: each win-set `{t | arg t = c}` is an interval
(`AffineLines.arg_win_ordConnected`), so along a monotone sample every value's fiber is contiguous —
exactly the per-value no-return the `Fin 3` block-refine `seqChanges_blockRefine3_le` consumes. (This is
why the shared-`Mcommon` gate is the right model: it makes the per-fiber gate `AffineLines 3`, not
`QuadLines 3`; the latter only has no-return-for-some-value and would not yield the tight base-3 fold.) -/

/-- An `AffineLines 3` argmax, restricted to a monotone sample, has per-value no-return. -/
theorem affineArg3_sample_noReturn (g : AffineLines 3) {M : ℕ} (pts : Fin (M + 1) → ℝ)
    (hinc : Increasing pts) :
    ∀ c : Fin 3, ∀ p r s : Fin (M + 1), p ≤ s → s ≤ r →
      g.arg (by norm_num) (pts p) = c → g.arg (by norm_num) (pts r) = c →
      g.arg (by norm_num) (pts s) = c := by
  intro c p r s hps hsr hp hr
  have hmono : ∀ i j : Fin (M + 1), i ≤ j → pts i ≤ pts j := by
    intro i j hij
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact le_of_lt (hinc i j h)
  have hoc := g.arg_win_ordConnected (by norm_num) c
  rw [ordConnected_def] at hoc
  exact hoc (Set.mem_setOf_eq ▸ hp) (Set.mem_setOf_eq ▸ hr) ⟨hmono p s hps, hmono s r hsr⟩

/-! ## (6) The depth-`L` trace alternation bound `≤ 3^L − 1` -/

/-- The layer-`m` gate bit of an arity-3 cascade `⟨layers⟩` at the real point `t` (or `0` if `m ≥ L`). -/
def quad3BitAt {L : ℕ} (layers : Fin L → QuadMuxLayer3 1) (m : ℕ) (t : ℝ) : Fin 3 :=
  if h : m < L then (QuadCascade3.mk layers).trace (fun _ => t) ⟨m, h⟩ else 0

/-- The **prefix** trace: first `m` bits as actual values, the rest masked to `0`. -/
def quad3PrefixVec {L : ℕ} (layers : Fin L → QuadMuxLayer3 1) (m : ℕ) (t : ℝ) : Fin L → Fin 3 :=
  fun i => if i.val < m then (QuadCascade3.mk layers).trace (fun _ => t) i else 0

/-- The prefix at `m+1` is the prefix at `m` updated with the layer-`m` bit. -/
theorem quad3PrefixVec_succ_eq {L : ℕ} (layers : Fin L → QuadMuxLayer3 1) (m : ℕ) (t : ℝ) :
    quad3PrefixVec layers (m + 1) t
      = fun i => if i.val = m then quad3BitAt layers m t else quad3PrefixVec layers m t i := by
  funext i
  unfold quad3PrefixVec quad3BitAt
  by_cases hi : i.val = m
  · subst hi
    rw [if_pos (Nat.lt_succ_self _), if_pos rfl, dif_pos i.isLt]
  · by_cases hlt : i.val < m
    · rw [if_pos (Nat.lt_succ_of_lt hlt), if_neg hi, if_pos hlt]
    · rw [if_neg (by omega), if_neg hi, if_neg hlt]

/-- The partial-fiber from prefix-equality. -/
theorem pfiber_of_quad3PrefixVec_eq {L : ℕ} (layers : Fin L → QuadMuxLayer3 1)
    (m : ℕ) (t₁ t₂ : ℝ) (heq : quad3PrefixVec layers m t₁ = quad3PrefixVec layers m t₂) :
    (QuadCascade3.mk layers).PFiber (fun _ => t₁) (fun _ => t₂) m := by
  intro i hi
  have h := congrFun heq i
  unfold quad3PrefixVec at h
  rw [if_pos hi, if_pos hi] at h
  exact h.symm

/-- **THE PER-BLOCK GLOBAL NO-RETURN FOR THE NEXT ARITY-3 BIT.** On any sample interval where the
prefix is constant, the layer-`m` gate bit has the per-value no-return contract: on that interval
`runUpTo m` is a fixed affine map, so the bit is an `AffineLines 3` argmax of `t`
(`quadGate3_comp_affine_eq_arg`), whose win-sets give per-value no-return (`arg3_sample_noReturn`). -/
theorem quad3BitAt_block_noReturn {L : ℕ} (layers : Fin L → QuadMuxLayer3 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) (m : ℕ) :
    ∀ a d : Fin (M + 1), a ≤ d →
      (∀ e, a ≤ e → e ≤ d →
        quad3PrefixVec layers m (pts e) = quad3PrefixVec layers m (pts a)) →
      ∀ c : Fin 3, ∀ p r s : Fin (M + 1), a ≤ p → p ≤ s → s ≤ r → r ≤ d →
        quad3BitAt layers m (pts p) = c → quad3BitAt layers m (pts r) = c →
        quad3BitAt layers m (pts s) = c := by
  intro a d had hconst
  set C := QuadCascade3.mk layers with hC
  by_cases hm : m < L
  · set A := C.prefixMap (fun _ => pts a) m with hA
    set Lyr := layers ⟨m, hm⟩ with hLyr
    set g := AffineLines.mk
        (fun i => Lyr.gateLin i 0 * A.mat 0 0)
        (fun i => Lyr.gateLin i 0 * A.shift 0 + Lyr.gateConst i) with hg
    have hbit : ∀ e : Fin (M + 1),
        quad3PrefixVec layers m (pts e) = quad3PrefixVec layers m (pts a) →
        quad3BitAt layers m (pts e) = g.arg (by norm_num) (pts e) := by
      intro e he
      have hpf : C.PFiber (fun _ => pts a) (fun _ => pts e) m :=
        pfiber_of_quad3PrefixVec_eq layers m (pts a) (pts e) he.symm
      have hrun : C.runUpTo m (fun _ => pts e) = A.apply (fun _ => pts e) :=
        C.runUpTo_eq_prefixMap_on_pfiber (fun _ => pts a) (fun _ => pts e) m hpf
      unfold quad3BitAt
      rw [dif_pos hm]
      have htrace : C.trace (fun _ => pts e) ⟨m, hm⟩
          = Lyr.gate (C.runUpTo m (fun _ => pts e)) := rfl
      rw [htrace, hrun]
      exact quadGate3_comp_affine_eq_arg Lyr A (pts e)
    intro c p r s hap hps hsr hrd hp hr
    have hpe : quad3PrefixVec layers m (pts p) = quad3PrefixVec layers m (pts a) :=
      hconst p hap (le_trans hps (le_trans hsr hrd))
    have hre : quad3PrefixVec layers m (pts r) = quad3PrefixVec layers m (pts a) :=
      hconst r (le_trans hap (le_trans hps hsr)) hrd
    have hse : quad3PrefixVec layers m (pts s) = quad3PrefixVec layers m (pts a) :=
      hconst s (le_trans hap hps) (le_trans hsr hrd)
    have ep := hbit p hpe
    have er := hbit r hre
    have es := hbit s hse
    rw [ep] at hp
    rw [er] at hr
    rw [es]
    exact affineArg3_sample_noReturn g pts hinc c p r s hps hsr hp hr
  · -- m ≥ L: bit constant 0, trivially per-value no-return
    intro c p r s _ _ _ _ hp _
    unfold quad3BitAt at hp ⊢; rw [dif_neg hm] at hp ⊢; exact hp

/-- **THE PREFIX-TRACE BASE-3 BOUND.** Along any increasing sample, the first-`m`-bits prefix trace of
`⟨layers⟩` changes at most `3^m − 1` times. Induction on `m` via `seqChanges_blockRefine3_le`. -/
theorem quad3PrefixVec_alternations_le {L : ℕ} (layers : Fin L → QuadMuxLayer3 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    ∀ m, seqChanges (fun k => quad3PrefixVec layers m (pts k)) ≤ 3 ^ m - 1 := by
  intro m
  induction m with
  | zero =>
      have hconst : ∀ k, quad3PrefixVec layers 0 (pts k) = fun _ => 0 := by
        intro k; funext i; unfold quad3PrefixVec; rw [if_neg (Nat.not_lt_zero _)]
      have : seqChanges (fun k => quad3PrefixVec layers 0 (pts k))
          = seqChanges (fun _ : Fin (M + 1) => (fun _ : Fin L => (0 : Fin 3))) :=
        seqChanges_congr (fun k => hconst k)
      rw [this]
      unfold seqChanges
      simp
  | succ m ih =>
      have hpair : seqChanges (fun k => quad3PrefixVec layers (m + 1) (pts k))
          ≤ seqChanges (fun k => (quad3PrefixVec layers m (pts k), quad3BitAt layers m (pts k))) := by
        have heq : (fun k => quad3PrefixVec layers (m + 1) (pts k))
            = fun k => (fun p : (Fin L → Fin 3) × Fin 3 =>
                (fun i => if i.val = m then p.2 else p.1 i))
                (quad3PrefixVec layers m (pts k), quad3BitAt layers m (pts k)) := by
          funext k; rw [quad3PrefixVec_succ_eq]
        rw [heq]
        exact seqChanges_comp_le
          (fun k => (quad3PrefixVec layers m (pts k), quad3BitAt layers m (pts k)))
          (fun p : (Fin L → Fin 3) × Fin 3 => (fun i => if i.val = m then p.2 else p.1 i))
      have hbr : seqChanges (fun k => (quad3PrefixVec layers m (pts k), quad3BitAt layers m (pts k)))
          ≤ 3 * seqChanges (fun k => quad3PrefixVec layers m (pts k)) + 2 :=
        seqChanges_blockRefine3_le _ _
          (fun a d had hconst =>
            quad3BitAt_block_noReturn layers pts hinc m a d had hconst)
      have hpow : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
      calc seqChanges (fun k => quad3PrefixVec layers (m + 1) (pts k))
          ≤ 3 * seqChanges (fun k => quad3PrefixVec layers m (pts k)) + 2 := le_trans hpair hbr
        _ ≤ 3 * (3 ^ m - 1) + 2 := by omega
        _ = 3 ^ (m + 1) - 1 := by rw [pow_succ]; omega

/-- **THE TRACE ALTERNATION BOUND `≤ 3^L − 1`.** -/
theorem quad3Trace_alternations_le {L : ℕ} (layers : Fin L → QuadMuxLayer3 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => (QuadCascade3.mk layers).trace (fun _ => pts k)) ≤ 3 ^ L - 1 := by
  have hL := quad3PrefixVec_alternations_le layers pts hinc L
  have heq : (fun k => quad3PrefixVec layers L (pts k))
      = fun k => (QuadCascade3.mk layers).trace (fun _ => pts k) := by
    funext k; funext i; unfold quad3PrefixVec; rw [if_pos i.isLt]
  rw [heq] at hL
  exact hL

/-! ## (7) The route alternation bound `≤ 3^{L+1} − 1`

One more block-refine on top of the trace. On a full-trace fiber the run is the fixed affine map
`fiberMap`, so the binary route is the `AffineLines 2` argmax of the readout scores through it. Its
win-sets are intervals (global no-return), which a-fortiori gives the `∃c`-no-return contract that the
arity-2 base-3 block-refine `seqChanges_blockRefine_le_two` consumes, adding one more `×3 + 2`. -/

/-- The readout `rs` evaluated through a fixed affine map `A` is an `AffineLines 2` argmax of `t`. -/
theorem route3_comp_affine_eq_arg (rs : Fin 2 → AffineFunctional 1) (A : AffineSelfMap 1) (t : ℝ) :
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

/-- **THE ROUTE BLOCK `∃c`-NO-RETURN.** On any sample interval where the FULL trace is constant, the
route has the `∃c`-no-return contract (in fact both values are no-return): the run on the fiber is the
fixed affine `fiberMap`, so the route is an `AffineLines 2` argmax of `t`, whose win-sets are
intervals. -/
theorem route3_block_le_two {L : ℕ} (layers : Fin L → QuadMuxLayer3 1)
    (rs : Fin 2 → AffineFunctional 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    ∀ a d : Fin (M + 1), a ≤ d →
      (∀ e, a ≤ e → e ≤ d →
        (QuadCascade3.mk layers).trace (fun _ => pts e)
          = (QuadCascade3.mk layers).trace (fun _ => pts a)) →
      ∃ c : Fin 2, ∀ p r s : Fin (M + 1), a ≤ p → p ≤ s → s ≤ r → r ≤ d →
        quadCascade3Route (QuadCascade3.mk layers) rs (fun _ => pts p) = c →
        quadCascade3Route (QuadCascade3.mk layers) rs (fun _ => pts r) = c →
        quadCascade3Route (QuadCascade3.mk layers) rs (fun _ => pts s) = c := by
  intro a d had hconst
  set C := QuadCascade3.mk layers with hC
  set A := C.fiberMap (fun _ => pts a) with hA
  set g := AffineLines.mk
      (fun j => (rs j).lin 0 * A.mat 0 0)
      (fun j => (rs j).lin 0 * A.shift 0 + (rs j).const) with hg
  have hroute : ∀ e : Fin (M + 1),
      C.trace (fun _ => pts e) = C.trace (fun _ => pts a) →
      quadCascade3Route C rs (fun _ => pts e) = g.arg (by norm_num) (pts e) := by
    intro e he
    have hrun : C.run (fun _ => pts e) = A.apply (fun _ => pts e) :=
      C.run_eq_on_fiber (fun _ => pts a) (fun _ => pts e) he
    unfold quadCascade3Route
    rw [hrun]
    exact route3_comp_affine_eq_arg rs A (pts e)
  -- both values of an AffineLines 2 argmax are no-return; pick c = 0
  refine ⟨0, ?_⟩
  intro p r s hap hps hsr hrd hp hr
  have hpe : C.trace (fun _ => pts p) = C.trace (fun _ => pts a) :=
    hconst p hap (le_trans hps (le_trans hsr hrd))
  have hre : C.trace (fun _ => pts r) = C.trace (fun _ => pts a) :=
    hconst r (le_trans hap (le_trans hps hsr)) hrd
  have hse : C.trace (fun _ => pts s) = C.trace (fun _ => pts a) :=
    hconst s (le_trans hap hps) (le_trans hsr hrd)
  have ep := hroute p hpe
  have er := hroute r hre
  have es := hroute s hse
  rw [ep] at hp
  rw [er] at hr
  rw [es]
  have hmono : ∀ i j : Fin (M + 1), i ≤ j → pts i ≤ pts j := by
    intro i j hij
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact le_of_lt (hinc i j h)
  exact g.arg_no_return (by norm_num) (hmono p s hps) (hmono s r hsr) hp hr

/-- **THE ROUTE ALTERNATION BOUND `≤ 3^{L+1} − 1`.** Along any increasing sample, the arity-2 route of
a depth-`L` arity-3 quadratic cascade changes at most `3^{L+1} − 1` times: the route is a function of
the pair `(trace, route)`; the trace changes `≤ 3^L − 1` times (`quad3Trace_alternations_le`) and the
route has the block `∃c`-no-return contract on trace-fibers (`route3_block_le_two`), so the arity-2
base-3 block-refine `seqChanges_blockRefine_le_two` adds one more `×3 + 2`. -/
theorem quadRoute3_alternations_le {L : ℕ} (layers : Fin L → QuadMuxLayer3 1)
    (rs : Fin 2 → AffineFunctional 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => quadCascade3Route (QuadCascade3.mk layers) rs (fun _ => pts k))
      ≤ 3 ^ (L + 1) - 1 := by
  have hcomp : seqChanges (fun k => quadCascade3Route (QuadCascade3.mk layers) rs (fun _ => pts k))
      ≤ seqChanges (fun k => ((QuadCascade3.mk layers).trace (fun _ => pts k),
          quadCascade3Route (QuadCascade3.mk layers) rs (fun _ => pts k))) := by
    have heq : (fun k => quadCascade3Route (QuadCascade3.mk layers) rs (fun _ => pts k))
        = fun k => (fun p : (Fin L → Fin 3) × Fin 2 => p.2)
            ((QuadCascade3.mk layers).trace (fun _ => pts k),
             quadCascade3Route (QuadCascade3.mk layers) rs (fun _ => pts k)) := rfl
    rw [heq]
    exact seqChanges_comp_le _ (fun p : (Fin L → Fin 3) × Fin 2 => p.2)
  have hbr : seqChanges (fun k => ((QuadCascade3.mk layers).trace (fun _ => pts k),
      quadCascade3Route (QuadCascade3.mk layers) rs (fun _ => pts k)))
      ≤ 3 * seqChanges (fun k => (QuadCascade3.mk layers).trace (fun _ => pts k)) + 2 :=
    seqChanges_blockRefine_le_two _ _
      (fun a d had hconst => route3_block_le_two layers rs pts hinc a d had hconst)
  have htrace := quad3Trace_alternations_le layers pts hinc
  have hpow : 1 ≤ 3 ^ L := Nat.one_le_pow _ _ (by norm_num)
  calc seqChanges (fun k => quadCascade3Route (QuadCascade3.mk layers) rs (fun _ => pts k))
      ≤ 3 * seqChanges (fun k => (QuadCascade3.mk layers).trace (fun _ => pts k)) + 2 :=
        le_trans hcomp hbr
    _ ≤ 3 * (3 ^ L - 1) + 2 := by omega
    _ = 3 ^ (L + 1) - 1 := by rw [pow_succ]; omega

/-! ## (8) The ternary tent witness and its iterate `ternMap^[L]`

The ternary tent `ternMap` folds `[0,1]` into THREE monotone laps each onto `[0,1]`:
`3s` on `[0,⅓]` (up), `2−3s` on `[⅓,⅔]` (down), `3s−2` on `[⅔,1]` (up). The three laps use THREE
DISTINCT affine branches — there is no shared-branch collapse — gated by an affine-score `leastArgmax`
(slopes `−1, 0, 1`), so the fold factor is a genuine `3`. -/

/-- The ternary tent fold as a bare real map: `3s` on `(−∞,⅓]`, `2−3s` on `[⅓,⅔]`, `3s−2` on `[⅔,∞)`. -/
def ternMap (s : ℝ) : ℝ := if s ≤ 1/3 then 3 * s else if s ≤ 2/3 then 2 - 3 * s else 3 * s - 2

/-- **The ternary tent layer.** Affine-score gate (slopes `−1, 0, 1`; argmax `0` on `(−∞,⅓]`, `1` on
`[⅓,⅔]`, `2` on `[⅔,∞)`), three distinct affine branches `3s`, `2−3s`, `3s−2`. The gate quadratic part
`Mcommon` is `0` (a degenerate quadratic score), so the layer is a genuine `QuadMuxLayer3`. -/
def ternTentLayer3 : QuadMuxLayer3 1 where
  Mcommon := fun _ _ => 0
  gateLin := fun i => if i = 0 then (fun _ => -1) else if i = 1 then (fun _ => 0) else (fun _ => 1)
  gateConst := fun i => if i = 0 then 1/3 else if i = 1 then 0 else -(2/3)
  branches := fun i => if i = 0 then ⟨fun _ _ => 3, fun _ => 0⟩
                       else if i = 1 then ⟨fun _ _ => -3, fun _ => 2⟩
                       else ⟨fun _ _ => 3, fun _ => -2⟩

/-- The depth-`L` iterated ternary tent cascade. -/
def ternTentCascade3 (L : ℕ) : QuadCascade3 1 L := QuadCascade3.mk (fun _ => ternTentLayer3)

/-- The three gate scores of the ternary tent layer at `![s]`: `−s + ⅓`, `0`, `s − ⅔`. -/
theorem ternTentLayer3_scores (s : ℝ) :
    (ternTentLayer3.scores 0).eval (fun _ => s) = -s + 1/3 ∧
    (ternTentLayer3.scores 1).eval (fun _ => s) = 0 ∧
    (ternTentLayer3.scores 2).eval (fun _ => s) = s - 2/3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [QuadScore.eval_coord1]
    simp only [QuadMuxLayer3.scores, ternTentLayer3]
    rw [if_pos (by decide), if_pos (by decide)]; ring
  · rw [QuadScore.eval_coord1]
    simp only [QuadMuxLayer3.scores, ternTentLayer3]
    rw [if_neg (by decide), if_pos (by decide), if_neg (by decide), if_pos (by decide)]; ring
  · rw [QuadScore.eval_coord1]
    simp only [QuadMuxLayer3.scores, ternTentLayer3]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]; ring

/-- The ternary tent layer's gate: `0` on `s ≤ ⅓`, `1` on `⅓ ≤ s ≤ ⅔`, `2` on `⅔ ≤ s`. -/
theorem ternTentLayer3_gate (s : ℝ) :
    ternTentLayer3.gate (fun _ => s) = if s ≤ 1/3 then 0 else if s ≤ 2/3 then 1 else 2 := by
  simp only [QuadMuxLayer3.gate]
  obtain ⟨h0, h1, h2⟩ := ternTentLayer3_scores s
  set v : Fin 3 → ℝ := fun i => (ternTentLayer3.scores i).eval (fun _ => s) with hv
  have hv0 : v 0 = -s + 1/3 := h0
  have hv1 : v 1 = 0 := h1
  have hv2 : v 2 = s - 2/3 := h2
  have hvall : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  apply isLeastArgmax_unique _ _ _ (leastArgmax_spec v (by norm_num))
  by_cases hc1 : s ≤ 1/3
  · rw [if_pos hc1]
    refine ⟨fun j => ?_, fun j hj => absurd hj (by omega)⟩
    rcases hvall j with rfl | rfl | rfl
    · rw [hv0]
    · rw [hv0, hv1]; linarith
    · rw [hv0, hv2]; linarith
  · rw [if_neg hc1]
    by_cases hc2 : s ≤ 2/3
    · rw [if_pos hc2]
      push Not at hc1
      refine ⟨fun j => ?_, fun j hj => ?_⟩
      · rcases hvall j with rfl | rfl | rfl
        · rw [hv0, hv1]; linarith
        · rw [hv1]
        · rw [hv2, hv1]; linarith
      · -- hj : j < 1, so j = 0
        rcases hvall j with rfl | rfl | rfl
        · rw [hv0, hv1]; linarith
        · exact absurd hj (by decide)
        · exact absurd hj (by decide)
    · rw [if_neg hc2]
      push Not at hc1 hc2
      refine ⟨fun j => ?_, fun j hj => ?_⟩
      · rcases hvall j with rfl | rfl | rfl
        · rw [hv0, hv2]; linarith
        · rw [hv1, hv2]; linarith
        · rw [hv2]
      · -- hj : j < 2, so j = 0 or 1
        rcases hvall j with rfl | rfl | rfl
        · rw [hv0, hv2]; linarith
        · rw [hv1, hv2]; linarith
        · exact absurd hj (by decide)

/-- The ternary tent layer's carrier action is `ternMap`. -/
theorem ternTentLayer3_apply (s : ℝ) :
    (ternTentLayer3.applyLayer (fun _ => s)) 0 = ternMap s := by
  simp only [QuadMuxLayer3.applyLayer, ternTentLayer3_gate, ternMap]
  by_cases hc1 : s ≤ 1/3
  · rw [if_pos hc1, if_pos hc1]
    show ((ternTentLayer3.branches 0).apply (fun _ => s)) 0 = 3 * s
    have hb : ternTentLayer3.branches 0 = (⟨fun _ _ => 3, fun _ => 0⟩ : AffineSelfMap 1) := by
      simp [ternTentLayer3]
    rw [hb, AffineSelfMap.apply_coord1]; ring
  · rw [if_neg hc1, if_neg hc1]
    by_cases hc2 : s ≤ 2/3
    · rw [if_pos hc2, if_pos hc2]
      show ((ternTentLayer3.branches 1).apply (fun _ => s)) 0 = 2 - 3 * s
      have hb : ternTentLayer3.branches 1 = (⟨fun _ _ => -3, fun _ => 2⟩ : AffineSelfMap 1) := by
        simp [ternTentLayer3]
      rw [hb, AffineSelfMap.apply_coord1]; ring
    · rw [if_neg hc2, if_neg hc2]
      show ((ternTentLayer3.branches 2).apply (fun _ => s)) 0 = 3 * s - 2
      have hb : ternTentLayer3.branches 2 = (⟨fun _ _ => 3, fun _ => -2⟩ : AffineSelfMap 1) := by
        simp [ternTentLayer3]
      rw [hb, AffineSelfMap.apply_coord1]; ring

/-- **The iterated ternary-tent run is the iterate of `ternMap`.** -/
theorem ternTentCascade3_runUpTo_coord (L : ℕ) (t : ℝ) :
    ∀ m, m ≤ L → ((ternTentCascade3 L).runUpTo m (fun _ => t)) 0 = (ternMap^[m]) t := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      rw [QuadCascade3.runUpTo, dif_pos (by omega : m < L)]
      show (ternTentLayer3.applyLayer ((ternTentCascade3 L).runUpTo m (fun _ => t))) 0 = _
      have hstate : ((ternTentCascade3 L).runUpTo m (fun _ => t))
          = (fun _ => ((ternTentCascade3 L).runUpTo m (fun _ => t)) 0) := by
        funext i; fin_cases i; rfl
      rw [hstate, ternTentLayer3_apply, ih (by omega), Function.iterate_succ_apply']

/-- The full run's carrier coordinate is `ternMap^[L] t`. -/
theorem ternTentCascade3_run_coord (L : ℕ) (t : ℝ) :
    ((ternTentCascade3 L).run (fun _ => t)) 0 = (ternMap^[L]) t :=
  ternTentCascade3_runUpTo_coord L t L (le_refl _)

/-! ## (9) The triadic-grid identity `ternMap^[L](j/3^L) = (j mod 2)`

The base-3 analogue of `tentMap_iterate_dyadic`. One ternary fold maps `j/3^{L+1}` to `num/3^L` with
`num ≤ 3^L` and `num ≡ j (mod 2)` (each of the three laps preserves parity since `3^L` is odd). -/

/-- One ternary fold of the triadic grid point `j / 3^{L+1}` lands on `num / 3^L` with `num ≤ 3^L` and
`num ≡ j (mod 2)`. The three cases are the three laps of `ternMap`. -/
theorem ternMap_fold_grid (L : ℕ) (j : ℕ) (hj : j ≤ 3 ^ (L + 1)) :
    ∃ num : ℕ, num ≤ 3 ^ L ∧ num % 2 = j % 2 ∧
      ternMap ((j : ℝ) / 3 ^ (L + 1)) = (num : ℝ) / 3 ^ L := by
  have hpowLpos : (0 : ℝ) < 3 ^ L := by positivity
  have hpow1pos : (0 : ℝ) < 3 ^ (L + 1) := by positivity
  have hLne : (3 : ℝ) ^ L ≠ 0 := ne_of_gt hpowLpos
  have hsucc : (3 : ℝ) ^ (L + 1) = 3 * 3 ^ L := by rw [pow_succ]; ring
  have hpowodd : 3 ^ L % 2 = 1 := by
    have : (3:ℕ) ^ L % 2 = (3 % 2) ^ L % 2 := by rw [Nat.pow_mod]
    simpa using this
  set q := (j : ℝ) / 3 ^ (L + 1) with hq
  -- the three lap cases, keyed by j vs 3^L, 2·3^L
  by_cases hc1 : j ≤ 3 ^ L
  · -- lap 1: q ≤ 1/3, ternMap q = 3q = j/3^L, num = j
    refine ⟨j, hc1, rfl, ?_⟩
    have hqle : q ≤ 1/3 := by
      rw [hq, hsucc]
      rw [div_le_iff₀ (by positivity)]
      have hjR : (j : ℝ) ≤ 3 ^ L := by exact_mod_cast hc1
      nlinarith [hpowLpos]
    unfold ternMap; rw [if_pos hqle, hq, hsucc]
    field_simp
  · push Not at hc1
    by_cases hc2 : j ≤ 2 * 3 ^ L
    · -- lap 2: 1/3 ≤ q ≤ 2/3, ternMap q = 2 - 3q = (2·3^L - j)/3^L, num = 2·3^L - j
      refine ⟨2 * 3 ^ L - j, by omega, ?_, ?_⟩
      · -- (2·3^L - j) % 2 = j % 2 since 2·3^L even
        have h2 : 2 * 3 ^ L % 2 = 0 := by omega
        omega
      · have hq1 : ¬ q ≤ 1/3 := by
          push Not
          rw [hq, hsucc, lt_div_iff₀ (by positivity)]
          have hjR : (3:ℝ) ^ L < j := by exact_mod_cast hc1
          nlinarith [hpowLpos]
        have hq2 : q ≤ 2/3 := by
          rw [hq, hsucc, div_le_iff₀ (by positivity)]
          have hjR : (j : ℝ) ≤ 2 * 3 ^ L := by exact_mod_cast hc2
          nlinarith [hpowLpos]
        unfold ternMap; rw [if_neg hq1, if_pos hq2, hq, hsucc]
        have hcast : ((2 * 3 ^ L - j : ℕ) : ℝ) = 2 * (3:ℝ) ^ L - j := by
          have : j ≤ 2 * 3 ^ L := hc2
          push_cast [Nat.cast_sub this]; ring
        rw [hcast]; field_simp
    · -- lap 3: 2/3 ≤ q, ternMap q = 3q - 2 = (j - 2·3^L)/3^L, num = j - 2·3^L
      push Not at hc2
      have hjle : j ≤ 3 * 3 ^ L := by have := hj; rw [pow_succ] at this; omega
      refine ⟨j - 2 * 3 ^ L, by omega, ?_, ?_⟩
      · have h2 : 2 * 3 ^ L % 2 = 0 := by omega
        omega
      · have hq2 : ¬ q ≤ 2/3 := by
          push Not
          rw [hq, hsucc, lt_div_iff₀ (by positivity)]
          have hjR : (2 * 3 ^ L : ℝ) < j := by exact_mod_cast hc2
          nlinarith [hpowLpos]
        have hq1 : ¬ q ≤ 1/3 := by
          push Not
          rw [hq, hsucc, lt_div_iff₀ (by positivity)]
          have hjR : (3:ℝ) ^ L < j := by
            have : (3:ℝ)^L < 2 * 3^L := by nlinarith [hpowLpos]
            have hjR2 : (2 * 3 ^ L : ℝ) < j := by exact_mod_cast hc2
            linarith
          nlinarith [hpowLpos]
        unfold ternMap; rw [if_neg hq1, if_neg hq2, hq, hsucc]
        have hcast : ((j - 2 * 3 ^ L : ℕ) : ℝ) = (j : ℝ) - 2 * (3:ℝ) ^ L := by
          have : 2 * 3 ^ L ≤ j := le_of_lt hc2
          push_cast [Nat.cast_sub this]; ring
        rw [hcast]; field_simp

/-- **THE TRIADIC IDENTITY.** The `L`-fold ternary tent iterate maps the triadic grid point `j / 3^L`
to the parity `(j mod 2 : ℝ)`, for `j ≤ 3^L`. The base-3 analogue of `tentMap_iterate_dyadic`. -/
theorem ternMap_iterate_triadic :
    ∀ L : ℕ, ∀ j : ℕ, j ≤ 3 ^ L →
      (ternMap^[L]) ((j : ℝ) / 3 ^ L) = ((j % 2 : ℕ) : ℝ) := by
  intro L
  induction L with
  | zero =>
      intro j hj
      simp only [pow_zero, Function.iterate_zero, id_eq] at *
      interval_cases j <;> norm_num
  | succ L ih =>
      intro j hj
      rw [Function.iterate_succ_apply]
      obtain ⟨num, hnum_le, hnum_mod, htent⟩ := ternMap_fold_grid L j hj
      rw [htent, ih num hnum_le, hnum_mod]

/-! ## (10) The ternary-tent route and its `3^{L+1}` alternation count on the triadic grid -/

/-- The ternary-tent route scores: threshold at `½` on the final coordinate (`route = 0` iff value
`≥ ½`). Same affine readout as the dyadic tent. -/
def ternTentRouteScores : Fin 2 → AffineFunctional 1 :=
  fun j => if j = 0 then ⟨fun _ => 1, -(1/2)⟩ else ⟨fun _ => -1, 1/2⟩

theorem ternTentRouteScores_eval (s : Fin 1 → ℝ) :
    (ternTentRouteScores 0).eval s = s 0 - 1/2 ∧ (ternTentRouteScores 1).eval s = 1/2 - s 0 := by
  refine ⟨?_, ?_⟩
  · show (ternTentRouteScores 0).eval s = s 0 - 1/2
    have : ternTentRouteScores 0 = (⟨fun _ => 1, -(1/2)⟩ : AffineFunctional 1) := by
      simp [ternTentRouteScores]
    rw [this, AffineFunctional.eval_coord1]; ring
  · show (ternTentRouteScores 1).eval s = 1/2 - s 0
    have : ternTentRouteScores 1 = (⟨fun _ => -1, 1/2⟩ : AffineFunctional 1) := by
      simp [ternTentRouteScores]
    rw [this, AffineFunctional.eval_coord1]; ring

/-- The ternary-tent route value: `0` iff the final coordinate `≥ ½`. -/
theorem ternTentRoute3_eq (L : ℕ) (t : ℝ) :
    quadCascade3Route (ternTentCascade3 L) ternTentRouteScores (fun _ => t)
      = if 1/2 ≤ (ternMap^[L]) t then 0 else 1 := by
  unfold quadCascade3Route
  rw [leastArgmax_two]
  obtain ⟨h0, h1⟩ := ternTentRouteScores_eval ((ternTentCascade3 L).run (fun _ => t))
  simp only [h0, h1, ternTentCascade3_run_coord]
  by_cases hc : (1:ℝ)/2 ≤ (ternMap^[L]) t
  · rw [if_pos (by linarith), if_pos hc]
  · rw [if_neg (by push Not at hc ⊢; linarith), if_neg hc]

/-- **The route value on the triadic grid point `j / 3^L` is `1 − (j mod 2)`.** -/
theorem ternTentRoute3_on_grid (L : ℕ) (j : ℕ) (hj : j ≤ 3 ^ L) :
    quadCascade3Route (ternTentCascade3 L) ternTentRouteScores (fun _ => (j : ℝ) / 3 ^ L)
      = if j % 2 = 0 then 1 else 0 := by
  rw [ternTentRoute3_eq, ternMap_iterate_triadic L j hj]
  have hmod : j % 2 = 0 ∨ j % 2 = 1 := by omega
  rcases hmod with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- The increasing triadic grid of `3^L + 1` points `k ↦ k / 3^L`. -/
def triadicGrid (L : ℕ) : Fin (3 ^ L + 1) → ℝ := fun k => (k.val : ℝ) / 3 ^ L

theorem triadicGrid_increasing (L : ℕ) : Increasing (triadicGrid L) := by
  intro i j hij
  unfold triadicGrid
  have hpow : (0 : ℝ) < 3 ^ L := by positivity
  have hlt : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast (Fin.lt_def.mp hij)
  exact div_lt_div_of_pos_right hlt hpow

/-- The ternary-tent route along the triadic grid, as a function of the grid index `k`. -/
theorem ternTentRoute3_triadicGrid (L : ℕ) (k : Fin (3 ^ L + 1)) :
    quadCascade3Route (ternTentCascade3 L) ternTentRouteScores (fun _ => triadicGrid L k)
      = if k.val % 2 = 0 then 1 else 0 := by
  unfold triadicGrid
  exact ternTentRoute3_on_grid L k.val (by have := k.isLt; omega)

/-- **THE WITNESS ALTERNATION COUNT `= 3^L`.** The depth-`L` iterated ternary-tent route changes value
at EVERY one of the `3^L` adjacent pairs of the triadic grid (consecutive grid indices have opposite
parity), so `seqChanges = 3^L`. The base-3 analogue of `upTentRoute_alternations_eq = 2^L`. -/
theorem ternTentRoute3_alternations_eq (L : ℕ) :
    seqChanges (fun k => quadCascade3Route (ternTentCascade3 L) ternTentRouteScores
        (fun _ => triadicGrid L k)) = 3 ^ L := by
  unfold seqChanges
  have hall : (Finset.univ.filter (fun i : Fin (3 ^ L) =>
      (fun k => quadCascade3Route (ternTentCascade3 L) ternTentRouteScores
        (fun _ => triadicGrid L k)) i.castSucc
      ≠ (fun k => quadCascade3Route (ternTentCascade3 L) ternTentRouteScores
        (fun _ => triadicGrid L k)) i.succ)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    simp only
    rw [ternTentRoute3_triadicGrid, ternTentRoute3_triadicGrid]
    have hcs : (i.castSucc : Fin (3 ^ L + 1)).val = i.val := Fin.val_castSucc i
    have hsc : (i.succ : Fin (3 ^ L + 1)).val = i.val + 1 := Fin.val_succ i
    rw [hcs, hsc]
    rcases Nat.even_or_odd i.val with he | ho
    · obtain ⟨r, hr⟩ := he
      rw [if_pos (by omega), if_neg (by omega)]
      decide
    · obtain ⟨r, hr⟩ := ho
      rw [if_neg (by omega), if_pos (by omega)]
      decide
  rw [hall, Finset.card_univ, Fintype.card_fin]

/-! ## (11) The depth-monotone embedding `quadDepthGrade3 L ⊆ quadDepthGrade3 (L+1)` -/

/-- The do-nothing arity-3 layer: all-equal gate scores (so the gate is `leastArgmax` of constants
`= 0`), both... all branches the identity. Its action is the identity regardless of the gate. -/
def quadIdLayer3 (d : ℕ) : QuadMuxLayer3 d where
  Mcommon := fun _ _ => 0
  gateLin := fun _ _ => 0
  gateConst := fun _ => 0
  branches := fun _ => AffineSelfMap.id d

@[simp] theorem quadIdLayer3_applyLayer {d : ℕ} (x : Fin d → ℝ) :
    (quadIdLayer3 d).applyLayer x = x := by
  simp only [QuadMuxLayer3.applyLayer]
  show ((quadIdLayer3 d).branches _).apply x = x
  have : ∀ i : Fin 3, (quadIdLayer3 d).branches i = AffineSelfMap.id d := fun _ => rfl
  rw [this]; exact AffineSelfMap.id_apply x

/-- Append the do-nothing identity layer at the last index. -/
def appendQuadId3Layers {d L : ℕ} (layers : Fin L → QuadMuxLayer3 d) :
    Fin (L + 1) → QuadMuxLayer3 d :=
  fun i => if h : i.val < L then layers ⟨i.val, h⟩ else quadIdLayer3 d

theorem appendQuadId3_runUpTo_eq {d L : ℕ} (layers : Fin L → QuadMuxLayer3 d) (x : Fin d → ℝ) :
    ∀ m, m ≤ L →
      (QuadCascade3.mk (appendQuadId3Layers layers)).runUpTo m x
        = (QuadCascade3.mk layers).runUpTo m x := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      have hmL : m < L := by omega
      have hmL1 : m < L + 1 := by omega
      rw [QuadCascade3.runUpTo, QuadCascade3.runUpTo, dif_pos hmL1, dif_pos hmL]
      have hlayer : appendQuadId3Layers layers ⟨m, hmL1⟩ = layers ⟨m, hmL⟩ := by
        rw [appendQuadId3Layers, dif_pos hmL]
      have hstate := ih (by omega)
      show ((QuadCascade3.mk (appendQuadId3Layers layers)).layers ⟨m, hmL1⟩).applyLayer
            ((QuadCascade3.mk (appendQuadId3Layers layers)).runUpTo m x)
          = ((QuadCascade3.mk layers).layers ⟨m, hmL⟩).applyLayer
            ((QuadCascade3.mk layers).runUpTo m x)
      rw [hstate]
      show (appendQuadId3Layers layers ⟨m, hmL1⟩).applyLayer ((QuadCascade3.mk layers).runUpTo m x)
          = (layers ⟨m, hmL⟩).applyLayer ((QuadCascade3.mk layers).runUpTo m x)
      rw [hlayer]

/-- **APPEND-IDENTITY RUN INVARIANCE.** -/
theorem appendQuadId3_run_eq {d L : ℕ} (layers : Fin L → QuadMuxLayer3 d) (x : Fin d → ℝ) :
    (QuadCascade3.mk (appendQuadId3Layers layers)).run x = (QuadCascade3.mk layers).run x := by
  show (QuadCascade3.mk (appendQuadId3Layers layers)).runUpTo (L + 1) x = _
  rw [QuadCascade3.runUpTo, dif_pos (by omega : L < L + 1)]
  have hlast : (QuadCascade3.mk (appendQuadId3Layers layers)).layers ⟨L, by omega⟩
      = quadIdLayer3 d := by
    show appendQuadId3Layers layers ⟨L, by omega⟩ = quadIdLayer3 d
    rw [appendQuadId3Layers, dif_neg (by simp)]
  rw [hlast]
  have hpre := appendQuadId3_runUpTo_eq layers x L (le_refl L)
  rw [hpre]
  show (quadIdLayer3 d).applyLayer ((QuadCascade3.mk layers).runUpTo L x)
      = (QuadCascade3.mk layers).run x
  rw [quadIdLayer3_applyLayer]
  rfl

/-- **DEPTH-MONOTONE EMBEDDING `quadDepthGrade3 d L ⊆ quadDepthGrade3 d (L+1)`.** -/
theorem quadDepthGrade3_succ_subset {d L : ℕ} :
    quadDepthGrade3 d L ⊆ quadDepthGrade3 d (L + 1) := by
  rintro f ⟨layers, rs, rfl⟩
  refine ⟨appendQuadId3Layers layers, rs, ?_⟩
  funext x
  simp only [quadCascade3Route]
  rw [appendQuadId3_run_eq layers x]

/-! ## (12) THE `∀L` ARITY-3 DEPTH SEPARATION -/

/-- The depth-`L` ternary-tent route, packaged as a route function; it lies in `quadDepthGrade3 1 L`. -/
def ternTentRoute3Fn (L : ℕ) : (Fin 1 → ℝ) → Fin 2 :=
  quadCascade3Route (ternTentCascade3 L) ternTentRouteScores

theorem ternTentRoute3Fn_mem_grade (L : ℕ) :
    ternTentRoute3Fn L ∈ quadDepthGrade3 1 L :=
  ⟨fun _ => ternTentLayer3, ternTentRouteScores, rfl⟩

/-- **Non-membership (`∀L`): the depth-`(L+1)` ternary-tent route is NOT in `quadDepthGrade3 1 L`.**
If it were a depth-`L` arity-3 route, then on the increasing triadic grid `triadicGrid (L+1)` it would
change `≤ 3^{L+1} − 1` times (`quadRoute3_alternations_le`); but it changes `3^{L+1}` times
(`ternTentRoute3_alternations_eq`), a contradiction. -/
theorem ternTentRoute3Fn_not_mem_grade (L : ℕ) :
    ternTentRoute3Fn (L + 1) ∉ quadDepthGrade3 1 L := by
  rintro ⟨layers, rs, hf⟩
  have hwit : seqChanges (fun k => ternTentRoute3Fn (L + 1) (fun _ => triadicGrid (L + 1) k))
      = 3 ^ (L + 1) := ternTentRoute3_alternations_eq (L + 1)
  have hbound : seqChanges (fun k => ternTentRoute3Fn (L + 1) (fun _ => triadicGrid (L + 1) k))
      ≤ 3 ^ (L + 1) - 1 := by
    have hrw : (fun k => ternTentRoute3Fn (L + 1) (fun _ => triadicGrid (L + 1) k))
        = fun k => quadCascade3Route (QuadCascade3.mk layers) rs
            (fun _ => triadicGrid (L + 1) k) := by
      funext k; rw [hf]
    rw [hrw]
    exact quadRoute3_alternations_le layers rs (triadicGrid (L + 1)) (triadicGrid_increasing (L + 1))
  rw [hwit] at hbound
  have hpow : 1 ≤ 3 ^ (L + 1) := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- **THE `∀L` ARITY-3 DEPTH-LADDER SEPARATION.** For every `L`,
`quadDepthGrade3 1 L ⊂ quadDepthGrade3 1 (L+1)`. The `⊆` is the depth-monotone identity-layer
embedding (`quadDepthGrade3_succ_subset`); the strictness is the iterated ternary-tent witness: the
depth-`(L+1)` ternary-tent route lies in grade `(L+1)` (`ternTentRoute3Fn_mem_grade`) but NOT in grade
`L` (`ternTentRoute3Fn_not_mem_grade`, via the base-3 route bound `quadRoute3_alternations_le`).

This is the NEW arity-3 (multi-expert `k = 3`) separation. Unlike the arity-2 grade `quadDepthGrade`
— where the shared-branch collapse caps the iterable fold at `2^L`, leaving the general-`L` separation
OPEN — here three DISTINCT affine branches give a genuine base-3 fold: depth buys expressivity at every
rung. -/
theorem quadDepthGrade3_ssubset_succ (L : ℕ) :
    quadDepthGrade3 1 L ⊂ quadDepthGrade3 1 (L + 1) := by
  refine ⟨quadDepthGrade3_succ_subset, ?_⟩
  intro hsubset
  have hmem : ternTentRoute3Fn (L + 1) ∈ quadDepthGrade3 1 (L + 1) :=
    ternTentRoute3Fn_mem_grade (L + 1)
  have h1 : ternTentRoute3Fn (L + 1) ∈ quadDepthGrade3 1 L := hsubset hmem
  exact ternTentRoute3Fn_not_mem_grade L h1

end TLT.TemperedDesignLaw
