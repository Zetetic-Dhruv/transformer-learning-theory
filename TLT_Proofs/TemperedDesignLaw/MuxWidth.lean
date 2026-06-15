/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MuxDepthLadderGeneral

/-!
# The WIDTH separation: fixed depth 1, varying mux ARITY (`constArityGrade n ⊂ constArityGrade (n+1)`)

This module establishes the **second** hierarchy direction of the affine-mux argmax calculus:
complementary to the landed VARYING-DEPTH, FIXED-ARITY ladder (`binCascadeGrade_ssubset_succ` in
`MuxDepthLadderGeneral.lean`). Here DEPTH is fixed at `1` and the mux **arity** varies: a wider mux
(arity `n+1`) realizes strictly more 1-D route functions than a narrower one (arity `n`).

Together, the two separate hierarchy directions complement each other: the depth ladder buys
expressivity by stacking layers; the width separation buys it by widening a single layer.

## The mechanism: the SAME region-count idea, now indexed by ARITY instead of DEPTH

Everything reuses the 1-D linear-region calculus already proved in `MuxDepthLadderGeneral.lean`:
`AffineLines`, `AffineLines.arg` (their `leastArgmax`), `affineArg_alternations_le` (the active index
of `n` affine functions of `t ∈ ℝ` changes `≤ n − 1` times along any strictly-increasing sample),
plus the alternation-combinatorics engine (`seqChanges`, `seqChanges_comp_le`,
`seqChanges_blockRefine_le`).

* **GRADE** (`constArityGrade n hn`): the set of route functions `(Fin 1 → ℝ) → Fin 2` realizable by
  SOME depth-`1` cascade whose single layer has arity EXACTLY `n`, with SOME 2 affine route-scores.
  Fixing arity `= n` is what makes "increasing `n`" meaningful.

* **BOUND** (`constArityRoute_alternations_le`): a depth-1 arity-`n` route changes value at most
  `2 · n − 1` times along any strictly-increasing grid. At depth 1 `runUpTo 0 = id`, so the single
  gate sees `t` directly and IS `affineArg` of `n` affine lines, switching `≤ n − 1` times
  (`affineArg_alternations_le`); on each gate-piece the run is one fixed affine branch, so the 2-way
  readout is `affineArg` of 2 lines and switches `≤ once` (`seqChanges_blockRefine_le`). Hence
  `≤ 2 · (n − 1) + 1 = 2n − 1`.

* **WITNESS** (`fanRoute n`): an explicit depth-1 arity-`(n+1)` "fan/staircase" fold whose readout
  alternates `2n + 1` times on the explicit increasing half-integer grid `k ↦ k / 2`,
  `k = 0 … 2n+1`. The fan scores `2 i · t − i²` have an upper envelope that steps the gate through
  `0,1,…,n`; branch `i` is `t ↦ 1 − 2(t − i)`, so the route reads exactly `k mod 2` at `t = k/2`, a
  full alternation. `2n + 1 > 2n − 1`, beyond every arity-`n` route's reach.

* **SEPARATION** (`constArityGrade_ssubset_succ`): `constArityGrade n ⊂ constArityGrade (n+1)` for all
  `n ≥ 1`. `⊆` via a width-monotone embedding (`constArityGrade_subset_succ`): an arity-`n` layer
  embeds into arity-`(n+1)` by appending a DUPLICATE of its last score+branch, a never-winning extra
  index that leaves the gate (hence the route) unchanged (`leastArgmax_dupLast_eq`). `≠` via the
  witness, a proved non-membership, not a relabeling of `⊆`.

-/

open scoped BigOperators
open Set

noncomputable section

namespace TLT.TemperedDesignLaw.MuxHierarchy

universe u

/-! ## (A) The depth-1, fixed-arity cascade and its grade -/

/-- The depth-1 cascade whose single layer is `Lyr` of arity exactly `n` (the arity function is
`fun _ => n` definitionally, so the trace lands in `Fin n` with no transport). -/
def arityCascade {n : ℕ} (hn : 0 < n) (Lyr : AffineMuxLayer 1 n) : MuxCascade 1 1 where
  arity := fun _ => n
  harity := fun _ => hn
  layers := fun _ => Lyr

/-- **The fixed-arity grade (depth 1, route arity 2).** `constArityGrade n hn` is the set of route
functions `(Fin 1 → ℝ) → Fin 2` realizable by SOME depth-1 cascade whose single layer has arity
EXACTLY `n`, together with SOME 2 affine route-scores. Fixing the arity to `n` is what makes the
statement "a wider mux realizes more routes" meaningful. -/
def constArityGrade (n : ℕ) (hn : 0 < n) : Set ((Fin 1 → ℝ) → Fin 2) :=
  { f | ∃ (Lyr : AffineMuxLayer 1 n) (rs : Fin 2 → AffineFunctional 1),
      f = cascadeRoute (arityCascade hn Lyr) rs (by norm_num) }

/-- The depth-1 cascade output is a single layer application: `run ![t] = Lyr.applyLayer ![t]`. -/
theorem arityCascade_run {n : ℕ} (hn : 0 < n) (Lyr : AffineMuxLayer 1 n) (x : Fin 1 → ℝ) :
    (arityCascade hn Lyr).run x = Lyr.applyLayer hn x := by
  show (arityCascade hn Lyr).runUpTo 1 x = _
  rw [MuxCascade.runUpTo, dif_pos (by norm_num : (0 : ℕ) < 1)]
  show (Lyr.applyLayer hn ((arityCascade hn Lyr).runUpTo 0 x)) = _
  rw [MuxCascade.runUpTo]

/-- The depth-1 cascade's single gate bit at `x` is exactly `Lyr.gate hn x`. -/
theorem arityCascade_gate {n : ℕ} (hn : 0 < n) (Lyr : AffineMuxLayer 1 n) (x : Fin 1 → ℝ) :
    (arityCascade hn Lyr).trace x (0 : Fin 1) = Lyr.gate hn x := rfl

/-! ## (B) The gate of a 1-D arity-`n` layer IS `affineArg` of `n` lines -/

/-- **The single gate is `affineArg` of `n` affine lines.** For a 1-D arity-`n` layer, the gate at
`![t]` is the active (`leastArgmax`) index of the explicit `AffineLines n` whose line `j` is
`(scores j).lin 0 · t + (scores j).const`. This is the depth-1 (`runUpTo 0 = id`) specialization of
`gate_comp_affine_eq_arg`: the gate sees `t` directly. -/
def layerLines {n : ℕ} (Lyr : AffineMuxLayer 1 n) : AffineLines n :=
  AffineLines.mk (fun j => (Lyr.scores j).lin 0) (fun j => (Lyr.scores j).const)

theorem layer_gate_eq_arg {n : ℕ} (hn : 0 < n) (Lyr : AffineMuxLayer 1 n) (t : ℝ) :
    Lyr.gate hn (fun _ => t) = (layerLines Lyr).arg hn t := by
  unfold AffineMuxLayer.gate AffineLines.arg layerLines
  congr 1
  funext j
  rw [AffineFunctional.eval_coord1]
  show (Lyr.scores j).lin 0 * t + (Lyr.scores j).const = (AffineLines.mk _ _).val j t
  unfold AffineLines.val
  ring

/-! ## (C) The trace-bit (gate) alternation bound `≤ n − 1` -/

/-- **THE GATE/TRACE ALTERNATION BOUND `≤ n − 1`.** Along any increasing sample, the depth-1 arity-`n`
gate bit changes value at most `n − 1` times, directly from `affineArg_alternations_le`, since the
gate IS `affineArg` of `n` lines. -/
theorem arityCascade_gate_alternations_le {n : ℕ} (hn : 0 < n) (Lyr : AffineMuxLayer 1 n)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => (arityCascade hn Lyr).trace (fun _ => pts k) (0 : Fin 1)) ≤ n - 1 := by
  have heq : (fun k => (arityCascade hn Lyr).trace (fun _ => pts k) (0 : Fin 1))
      = fun k => (layerLines Lyr).arg hn (pts k) := by
    funext k
    rw [arityCascade_gate hn Lyr, layer_gate_eq_arg hn Lyr]
  rw [heq]
  exact affineArg_alternations_le (layerLines Lyr) hn pts hinc

/-! ## (D) The route block-no-return on a gate-fiber (the readout flips ≤ once per gate-piece) -/

/-- **THE ROUTE BLOCK NO-RETURN.** On any sample interval where the gate is constant (a single
gate-piece), the depth-1 arity-`n` route has no-return: on that piece the run is the fixed affine
branch `Lyr.branches gateval`, so the route is `affineArg` of 2 lines (the readout scores composed
through that branch), whose win-sets are intervals (`arg_no_return`). -/
theorem arityRoute_block_noReturn {n : ℕ} (hn : 0 < n) (Lyr : AffineMuxLayer 1 n)
    (rs : Fin 2 → AffineFunctional 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    ∀ a c d : Fin (M + 1), a ≤ c → c ≤ d →
      (∀ e, a ≤ e → e ≤ d →
        (arityCascade hn Lyr).trace (fun _ => pts e) (0 : Fin 1)
          = (arityCascade hn Lyr).trace (fun _ => pts a) (0 : Fin 1)) →
      cascadeRoute (arityCascade hn Lyr) rs (by norm_num) (fun _ => pts a)
        = cascadeRoute (arityCascade hn Lyr) rs (by norm_num) (fun _ => pts d) →
      cascadeRoute (arityCascade hn Lyr) rs (by norm_num) (fun _ => pts c)
        = cascadeRoute (arityCascade hn Lyr) rs (by norm_num) (fun _ => pts a) := by
  intro a c d hac hcd hconst hbad
  set C := arityCascade hn Lyr with hC
  have hmono : ∀ i j : Fin (M + 1), i ≤ j → pts i ≤ pts j := by
    intro i j hij
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact le_of_lt (hinc i j h)
  -- the fixed branch on the gate-piece of `a`
  set gateval := Lyr.gate hn (fun _ => pts a) with hgateval
  set A := Lyr.branches gateval with hA
  -- the readout, packaged as a 2-way "layer", evaluated through the branch map `A`
  set readoutLyr : AffineMuxLayer 1 2 := ⟨rs, fun _ => AffineSelfMap.id 1⟩ with hRead
  set g := AffineLines.mk
      (fun j => ((rs j).lin 0 * A.mat 0 0))
      (fun j => ((rs j).lin 0 * A.shift 0 + (rs j).const)) with hg
  -- route at any gate-piece-equal point equals g.arg
  have hroute : ∀ e : Fin (M + 1),
      C.trace (fun _ => pts e) (0 : Fin 1) = C.trace (fun _ => pts a) (0 : Fin 1) →
      cascadeRoute C rs (by norm_num) (fun _ => pts e) = g.arg (by norm_num) (pts e) := by
    intro e he
    -- gate at e equals gateval
    have hge : Lyr.gate hn (fun _ => pts e) = gateval := by
      rw [hgateval]
      have := he
      rw [arityCascade_gate hn Lyr, arityCascade_gate hn Lyr] at this
      exact this
    -- run at e is the fixed branch applied to ![pts e]
    have hrun : C.run (fun _ => pts e) = A.apply (fun _ => pts e) := by
      rw [arityCascade_run hn Lyr]
      show (Lyr.branches (Lyr.gate hn (fun _ => pts e))).apply (fun _ => pts e) = A.apply _
      rw [hge]
    unfold cascadeRoute
    rw [hrun]
    have hgate : (readoutLyr.gate (by norm_num) (A.apply (fun _ => pts e)))
        = g.arg (by norm_num) (pts e) := gate_comp_affine_eq_arg readoutLyr A (pts e)
    show leastArgmax (fun j => (rs j).eval (A.apply (fun _ => pts e))) (by norm_num)
        = g.arg (by norm_num) (pts e)
    rw [← hgate]
    rfl
  have ea := hroute a rfl
  have ec := hroute c (hconst c hac hcd)
  have ed := hroute d (hconst d (le_trans hac hcd) (le_refl _))
  have hargad : g.arg (by norm_num) (pts a) = g.arg (by norm_num) (pts d) := by
    rw [← ea, ← ed]; exact hbad
  have hargc : g.arg (by norm_num) (pts c) = g.arg (by norm_num) (pts a) :=
    g.arg_no_return (by norm_num) (hmono a c hac) (hmono c d hcd) rfl hargad.symm
  rw [ec, ea]; exact hargc

/-! ## (E) THE ROUTE ALTERNATION BOUND `≤ 2n − 1` (the block-refine on top of the gate bound) -/

/-- **THE DEPTH-1 ARITY-`n` ROUTE ALTERNATION BOUND `≤ 2n − 1`.** Along any strictly-increasing
sample, a depth-1 arity-`n` route changes value at most `2n − 1` times. The route is a function of
the pair `(gate, route)`; the gate changes `≤ n − 1` times (`arityCascade_gate_alternations_le`) and
the route has block-no-return on gate-pieces (`arityRoute_block_noReturn`), so
`seqChanges_blockRefine_le` gives one doubling: `≤ 2 · (n − 1) + 1 = 2n − 1`. This is the
arity-parameterized analogue of the depth file's route bound at `L = 1`. -/
theorem constArityRoute_alternations_le {n : ℕ} (hn : 0 < n) (Lyr : AffineMuxLayer 1 n)
    (rs : Fin 2 → AffineFunctional 1)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => cascadeRoute (arityCascade hn Lyr) rs (by norm_num) (fun _ => pts k))
      ≤ 2 * n - 1 := by
  -- route = π₂ ∘ (gate, route)
  have hcomp : seqChanges (fun k =>
        cascadeRoute (arityCascade hn Lyr) rs (by norm_num) (fun _ => pts k))
      ≤ seqChanges (fun k => ((arityCascade hn Lyr).trace (fun _ => pts k) (0 : Fin 1),
          cascadeRoute (arityCascade hn Lyr) rs (by norm_num) (fun _ => pts k))) := by
    have heq : (fun k => cascadeRoute (arityCascade hn Lyr) rs (by norm_num) (fun _ => pts k))
        = fun k => (fun p : Fin n × Fin 2 => p.2)
            ((arityCascade hn Lyr).trace (fun _ => pts k) (0 : Fin 1),
             cascadeRoute (arityCascade hn Lyr) rs (by norm_num) (fun _ => pts k)) := rfl
    rw [heq]
    exact seqChanges_comp_le _ (fun p : Fin n × Fin 2 => p.2)
  -- block-refine on the pair (gate, route)
  have hbr : seqChanges (fun k => ((arityCascade hn Lyr).trace (fun _ => pts k) (0 : Fin 1),
      cascadeRoute (arityCascade hn Lyr) rs (by norm_num) (fun _ => pts k)))
      ≤ 2 * seqChanges (fun k => (arityCascade hn Lyr).trace (fun _ => pts k) (0 : Fin 1)) + 1 :=
    seqChanges_blockRefine_le _ _
      (fun a c d hac hcd hconst hbad =>
        arityRoute_block_noReturn hn Lyr rs pts hinc a c d hac hcd hconst hbad)
  have hgate := arityCascade_gate_alternations_le hn Lyr pts hinc
  have hpos : 1 ≤ n := hn
  calc seqChanges (fun k =>
          cascadeRoute (arityCascade hn Lyr) rs (by norm_num) (fun _ => pts k))
      ≤ 2 * seqChanges (fun k => (arityCascade hn Lyr).trace (fun _ => pts k) (0 : Fin 1)) + 1 :=
        le_trans hcomp hbr
    _ ≤ 2 * (n - 1) + 1 := by omega
    _ = 2 * n - 1 := by omega

/-! ## (F) THE WITNESS: a depth-1 arity-`(n+1)` "fan/staircase" fold with `2n + 1` alternations -/

/-- The fan scores: line `i` is `2 i · t − i²`. Their upper envelope steps through `0,1,…,n`, with
line `i` winning on `(i − ½, i + ½)`; at the half-integer breakpoints the `leastArgmax` tie-break
picks the smaller index, so at `t = k/2` the gate is `⌊k/2⌋`. -/
def fanLayer (n : ℕ) : AffineMuxLayer 1 (n + 1) where
  scores := fun i => ⟨fun _ => 2 * (i.val : ℝ), -((i.val : ℝ) ^ 2)⟩
  branches := fun i => ⟨fun _ _ => -2, fun _ => 1 + 2 * (i.val : ℝ)⟩

/-- The fan cascade: a single `fanLayer n` at depth 1, arity `n + 1`. -/
def fanCascade (n : ℕ) : MuxCascade 1 1 := arityCascade (by norm_num) (fanLayer n)

/-- The fan readout: route on the threshold `state ≥ ½` (`route = 0` iff state `≥ ½`). Same readout
shape as the tent route. -/
def fanRouteScores : Fin 2 → AffineFunctional 1 :=
  fun j => if j = 0 then ⟨fun _ => 1, -(1/2)⟩ else ⟨fun _ => -1, 1/2⟩

theorem fanRouteScores_eval (s : Fin 1 → ℝ) :
    (fanRouteScores 0).eval s = s 0 - 1/2 ∧ (fanRouteScores 1).eval s = 1/2 - s 0 := by
  refine ⟨?_, ?_⟩
  · show (fanRouteScores 0).eval s = s 0 - 1/2
    have : fanRouteScores 0 = ⟨fun _ => 1, -(1/2)⟩ := by simp [fanRouteScores]
    rw [this]; simp [AffineFunctional.eval]; ring
  · show (fanRouteScores 1).eval s = 1/2 - s 0
    have : fanRouteScores 1 = ⟨fun _ => -1, 1/2⟩ := by simp [fanRouteScores]
    rw [this]; simp [AffineFunctional.eval]; ring

/-- The fan route, packaged as a route function. In `constArityGrade (n+1)` by construction. -/
def fanRoute (n : ℕ) : (Fin 1 → ℝ) → Fin 2 :=
  cascadeRoute (fanCascade n) fanRouteScores (by norm_num)

theorem fanRoute_mem_grade (n : ℕ) :
    fanRoute n ∈ constArityGrade (n + 1) (by norm_num) :=
  ⟨fanLayer n, fanRouteScores, rfl⟩

/-- A fan score's evaluation at `![t]`: `(scores i).eval ![t] = 2 i · t − i²`. -/
theorem fanLayer_score_eval (n : ℕ) (i : Fin (n + 1)) (t : ℝ) :
    (((fanLayer n).scores i).eval (fun _ => t)) = 2 * (i.val : ℝ) * t - (i.val : ℝ) ^ 2 := by
  rw [AffineFunctional.eval_coord1]
  show 2 * (i.val : ℝ) * t + -((i.val : ℝ) ^ 2) = _
  ring

/-- **THE GATE OF THE FAN AT A HALF-INTEGER `t = k/2` is `⌊k/2⌋`.** For `k ≤ 2n + 1`, the
`leastArgmax` of the fan scores at `t = k/2` is the index `⟨k / 2, _⟩` (integer division). The score
difference `score_m − score_j` at `t = k/2` is `(m − j)(k − m − j)`, which is `≥ 0` for all `j` and
`> 0` for `j < m`, so `m = k / 2` is the (least) argmax. -/
theorem fanLayer_gate_at_half (n : ℕ) (k : ℕ) (hk : k ≤ 2 * n + 1) :
    (fanLayer n).gate (by norm_num) (fun _ => (k : ℝ) / 2)
      = ⟨k / 2, by omega⟩ := by
  set m : ℕ := k / 2 with hm
  have hmle : m ≤ n := by omega
  set i0 : Fin (n + 1) := ⟨m, by omega⟩ with hi0
  -- value of score j at t = k/2
  have hval : ∀ j : Fin (n + 1),
      (((fanLayer n).scores j).eval (fun _ => (k : ℝ) / 2))
        = 2 * (j.val : ℝ) * ((k : ℝ) / 2) - (j.val : ℝ) ^ 2 := by
    intro j; exact fanLayer_score_eval n j ((k : ℝ) / 2)
  -- the key sign computation: score i0 − score j = (m − j)(k − m − j) ≥ 0, strict for j < m
  have hdiff : ∀ j : Fin (n + 1),
      (((fanLayer n).scores i0).eval (fun _ => (k : ℝ) / 2))
        - (((fanLayer n).scores j).eval (fun _ => (k : ℝ) / 2))
        = ((m : ℝ) - (j.val : ℝ)) * ((k : ℝ) - (m : ℝ) - (j.val : ℝ)) := by
    intro j
    rw [hval i0, hval j]
    show 2 * (m : ℝ) * ((k : ℝ) / 2) - (m : ℝ) ^ 2
          - (2 * (j.val : ℝ) * ((k : ℝ) / 2) - (j.val : ℝ) ^ 2)
        = ((m : ℝ) - (j.val : ℝ)) * ((k : ℝ) - (m : ℝ) - (j.val : ℝ))
    ring
  -- k = 2m or k = 2m+1
  have hk2 : k = 2 * m ∨ k = 2 * m + 1 := by omega
  -- prove isLeastArgmax i0
  apply isLeastArgmax_unique _ _ _ (leastArgmax_spec _ _)
  refine ⟨?_, ?_⟩
  · -- ∀ j, score j ≤ score i0
    intro j
    show (((fanLayer n).scores j).eval (fun _ => (k : ℝ) / 2))
        ≤ (((fanLayer n).scores i0).eval (fun _ => (k : ℝ) / 2))
    have hd := hdiff j
    -- need: score j ≤ score i0, i.e. score i0 − score j ≥ 0
    have hsign : (0 : ℝ) ≤ ((m : ℝ) - (j.val : ℝ)) * ((k : ℝ) - (m : ℝ) - (j.val : ℝ)) := by
      rcases hk2 with he | ho
      · -- k = 2m : (m−j)(2m−m−j) = (m−j)² ≥ 0
        have hkr : (k : ℝ) = 2 * (m : ℝ) := by rw [he]; push_cast; ring
        rw [hkr]
        have : ((m : ℝ) - (j.val : ℝ)) * (2 * (m : ℝ) - (m : ℝ) - (j.val : ℝ))
            = ((m : ℝ) - (j.val : ℝ)) ^ 2 := by ring
        rw [this]; positivity
      · -- k = 2m+1 : (m−j)(2m+1−m−j) = (m−j)(m+1−j)
        have hkr : (k : ℝ) = 2 * (m : ℝ) + 1 := by rw [ho]; push_cast; ring
        rw [hkr]
        have hrw : ((m : ℝ) - (j.val : ℝ)) * (2 * (m : ℝ) + 1 - (m : ℝ) - (j.val : ℝ))
            = ((m : ℝ) - (j.val : ℝ)) * (((m : ℝ) + 1) - (j.val : ℝ)) := by ring
        rw [hrw]
        -- product of two reals that are both ≥ 0 or both ≤ 0 (consecutive integer gaps)
        rcases le_or_gt (j.val : ℝ) (m : ℝ) with hjm | hjm
        · -- j ≤ m : both factors ≥ 0
          apply mul_nonneg (by linarith)
          linarith
        · -- j > m, so j ≥ m+1 (integers) : both factors ≤ 0 ⟹ product ≥ 0
          have hjm1 : (m : ℝ) + 1 ≤ (j.val : ℝ) := by
            have hlt : m < j.val := by exact_mod_cast hjm
            have : m + 1 ≤ j.val := hlt
            exact_mod_cast this
          nlinarith [hjm1, hjm]
    linarith [hsign, hd]
  · -- ∀ j < i0, score j < score i0
    intro j hj
    show (((fanLayer n).scores j).eval (fun _ => (k : ℝ) / 2))
        < (((fanLayer n).scores i0).eval (fun _ => (k : ℝ) / 2))
    have hjlt : j.val < m := by
      have hjlt' : j < i0 := hj
      simpa [hi0, Fin.lt_def] using hjlt'
    have hd := hdiff j
    have hstrict : (0 : ℝ) < ((m : ℝ) - (j.val : ℝ)) * ((k : ℝ) - (m : ℝ) - (j.val : ℝ)) := by
      have hjr : (j.val : ℝ) < (m : ℝ) := by exact_mod_cast hjlt
      rcases hk2 with he | ho
      · have hkr : (k : ℝ) = 2 * (m : ℝ) := by rw [he]; push_cast; ring
        rw [hkr]
        have : ((m : ℝ) - (j.val : ℝ)) * (2 * (m : ℝ) - (m : ℝ) - (j.val : ℝ))
            = ((m : ℝ) - (j.val : ℝ)) ^ 2 := by ring
        rw [this]
        have hpos : (0 : ℝ) < (m : ℝ) - (j.val : ℝ) := by linarith
        positivity
      · have hkr : (k : ℝ) = 2 * (m : ℝ) + 1 := by rw [ho]; push_cast; ring
        rw [hkr]
        have hrw : ((m : ℝ) - (j.val : ℝ)) * (2 * (m : ℝ) + 1 - (m : ℝ) - (j.val : ℝ))
            = ((m : ℝ) - (j.val : ℝ)) * (((m : ℝ) + 1) - (j.val : ℝ)) := by ring
        rw [hrw]
        apply mul_pos (by linarith) (by linarith)
    linarith [hstrict, hd]

/-- **THE FAN ROUTE AT `t = k/2` is `k mod 2`.** For `k ≤ 2n + 1`: the gate selects branch
`m = ⌊k/2⌋`, whose affine action is `t ↦ 1 − 2(t − m)`, so the folded coordinate at `t = k/2` is
`1 − (k − 2m) = 1 − (k mod 2)`. The readout (`route = 0` iff state `≥ ½`) then reads `0` when `k` is
even and `1` when `k` is odd, i.e. exactly `k mod 2`. -/
theorem fanRoute_at_half (n : ℕ) (k : ℕ) (hk : k ≤ 2 * n + 1) :
    fanRoute n (fun _ => (k : ℝ) / 2) = if k % 2 = 0 then 0 else 1 := by
  set m : ℕ := k / 2 with hm
  -- the run coordinate after the selected branch
  have hgate : (fanLayer n).gate (by norm_num) (fun _ => (k : ℝ) / 2) = ⟨m, by omega⟩ :=
    fanLayer_gate_at_half n k hk
  -- run = branch m applied to ![k/2]
  have hrun : ((fanCascade n).run (fun _ => (k : ℝ) / 2)) 0
      = 1 - 2 * ((k : ℝ) / 2 - (m : ℝ)) := by
    rw [fanCascade, arityCascade_run]
    show ((fanLayer n).branches ((fanLayer n).gate (by norm_num) (fun _ => (k : ℝ) / 2))).apply
          (fun _ => (k : ℝ) / 2) 0 = _
    rw [hgate]
    show (((fanLayer n).branches ⟨m, by omega⟩).apply (fun _ => (k : ℝ) / 2)) 0 = _
    rw [AffineSelfMap.apply_coord1]
    show (-2 : ℝ) * ((k : ℝ) / 2) + (1 + 2 * (m : ℝ)) = 1 - 2 * ((k : ℝ) / 2 - (m : ℝ))
    ring
  -- route value via the readout threshold
  have hroute : fanRoute n (fun _ => (k : ℝ) / 2)
      = if 1/2 ≤ ((fanCascade n).run (fun _ => (k : ℝ) / 2)) 0 then 0 else 1 := by
    show cascadeRoute (fanCascade n) fanRouteScores (by norm_num) (fun _ => (k : ℝ) / 2) = _
    rw [cascadeRoute, leastArgmax_two]
    obtain ⟨h0, h1⟩ := fanRouteScores_eval ((fanCascade n).run (fun _ => (k : ℝ) / 2))
    simp only [h0, h1]
    by_cases hc : (1:ℝ)/2 ≤ ((fanCascade n).run (fun _ => (k : ℝ) / 2)) 0
    · rw [if_pos (by linarith), if_pos hc]
    · rw [if_neg (by push Not at hc ⊢; linarith), if_neg hc]
  rw [hroute, hrun]
  -- now compute: 1 - 2(k/2 - m) ; with k = 2m (even) → state = 1 ≥ ½ → 0 ; k = 2m+1 (odd) → 0 < ½ → 1
  have hk2 : k = 2 * m ∨ k = 2 * m + 1 := by omega
  rcases hk2 with he | ho
  · -- even
    have hkr : (k : ℝ) / 2 = (m : ℝ) := by
      rw [he]; push_cast; ring
    rw [hkr]
    rw [if_pos (by norm_num : (1:ℝ)/2 ≤ 1 - 2 * ((m:ℝ) - (m:ℝ)))]
    rw [if_pos (by omega : k % 2 = 0)]
  · -- odd
    have hkr : (k : ℝ) / 2 = (m : ℝ) + 1/2 := by
      rw [ho]; push_cast; ring
    rw [hkr]
    rw [if_neg (by norm_num : ¬ (1:ℝ)/2 ≤ 1 - 2 * (((m:ℝ) + 1/2) - (m:ℝ)))]
    rw [if_neg (by omega : ¬ k % 2 = 0)]

/-! ### (F.a) The increasing half-integer grid and the witness alternation count `= 2n + 1` -/

/-- The increasing half-integer grid of `2n + 2` points `k ↦ k / 2`, `k = 0 … 2n+1`. -/
def halfGrid (n : ℕ) : Fin (2 * n + 1 + 1) → ℝ := fun k => (k.val : ℝ) / 2

theorem halfGrid_increasing (n : ℕ) : Increasing (halfGrid n) := by
  intro i j hij
  unfold halfGrid
  have hlt : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast (Fin.lt_def.mp hij)
  linarith

/-- The fan route along the half-integer grid, as a function of the grid index `k`. -/
theorem fanRoute_halfGrid (n : ℕ) (k : Fin (2 * n + 1 + 1)) :
    fanRoute n (fun _ => halfGrid n k) = if k.val % 2 = 0 then 0 else 1 := by
  unfold halfGrid
  exact fanRoute_at_half n k.val (by have := k.isLt; omega)

/-- **THE WITNESS ALTERNATION LOWER BOUND `= 2n + 1`.** The depth-1 arity-`(n+1)` fan route changes
value at EVERY one of the `2n + 1` adjacent pairs of the half-integer grid (consecutive grid indices
have opposite parity, so the route flips at every step). Hence `seqChanges = 2n + 1`. -/
theorem fanRoute_alternations_eq (n : ℕ) :
    seqChanges (fun k => fanRoute n (fun _ => halfGrid n k)) = 2 * n + 1 := by
  unfold seqChanges
  have hall : (Finset.univ.filter (fun i : Fin (2 * n + 1) =>
      (fun k => fanRoute n (fun _ => halfGrid n k)) i.castSucc
      ≠ (fun k => fanRoute n (fun _ => halfGrid n k)) i.succ)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    simp only
    rw [fanRoute_halfGrid, fanRoute_halfGrid]
    have hcs : (i.castSucc : Fin (2 * n + 1 + 1)).val = i.val := Fin.val_castSucc i
    have hsc : (i.succ : Fin (2 * n + 1 + 1)).val = i.val + 1 := Fin.val_succ i
    rw [hcs, hsc]
    rcases Nat.even_or_odd i.val with he | ho
    · obtain ⟨r, hr⟩ := he
      rw [if_pos (by omega), if_neg (by omega)]
      decide
    · obtain ⟨r, hr⟩ := ho
      rw [if_neg (by omega), if_pos (by omega)]
      decide
  rw [hall, Finset.card_univ, Fintype.card_fin]

/-! ## (G) THE WIDTH-MONOTONE EMBEDDING `constArityGrade n ⊆ constArityGrade (n+1)` -/

/-- The "duplicate-last" extension of a value vector `v : Fin n → ℝ` to `Fin (n+1)`: index `j` keeps
`v ⟨j, _⟩` for `j < n`, and the new last index `n` duplicates `v ⟨n−1, _⟩`. The duplicate never makes
a strictly-new maximum, so the `leastArgmax` is unchanged (and lands among the original indices). -/
def dupLast {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun j => if h : j.val < n then v ⟨j.val, h⟩ else v ⟨n - 1, by omega⟩

/-- **THE DUPLICATE-LAST `leastArgmax` INVARIANCE.** Extending `n` values by a duplicate of the last
leaves the `leastArgmax` at the `castSucc`-image of the original argmax: the duplicate ties an existing
value (so makes no new strict max) and carries a larger index (so the least maximizer is unchanged). -/
theorem leastArgmax_dupLast_eq {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) :
    leastArgmax (dupLast hn v) (by omega) = Fin.castSucc (leastArgmax v hn) := by
  set i := leastArgmax v hn with hi
  have hiext_val : (Fin.castSucc i).val = i.val := Fin.val_castSucc i
  have hiext_lt : (Fin.castSucc i).val < n := by rw [hiext_val]; exact i.isLt
  -- value of dupLast at iext is v i
  have hval_iext : dupLast hn v (Fin.castSucc i) = v i := by
    show (if h : (Fin.castSucc i).val < n then v ⟨(Fin.castSucc i).val, h⟩
            else v ⟨n - 1, by omega⟩) = v i
    rw [dif_pos hiext_lt]
    have : (⟨(Fin.castSucc i).val, hiext_lt⟩ : Fin n) = i := Fin.ext hiext_val
    rw [this]
  apply isLeastArgmax_unique _ _ _ (leastArgmax_spec _ _)
  refine ⟨?_, ?_⟩
  · -- ∀ j, dupLast v j ≤ dupLast v iext = v i
    intro j
    show dupLast hn v j ≤ dupLast hn v (Fin.castSucc i)
    rw [hval_iext]
    show (if h : j.val < n then v ⟨j.val, h⟩ else v ⟨n - 1, by omega⟩) ≤ v i
    by_cases hj : j.val < n
    · rw [dif_pos hj]
      rw [hi]; exact leastArgmax_is_maximizer v hn ⟨j.val, hj⟩
    · rw [dif_neg hj]
      rw [hi]; exact leastArgmax_is_maximizer v hn ⟨n - 1, by omega⟩
  · -- ∀ j < iext, dupLast v j < dupLast v iext = v i
    intro j hj
    show dupLast hn v j < dupLast hn v (Fin.castSucc i)
    rw [hval_iext]
    have hjlt : j.val < (Fin.castSucc i).val := Fin.lt_def.mp hj
    have hjn : j.val < n := by rw [hiext_val] at hjlt; omega
    show (if h : j.val < n then v ⟨j.val, h⟩ else v ⟨n - 1, by omega⟩) < v i
    rw [dif_pos hjn]
    rw [hi]
    apply leastArgmax_is_least v hn ⟨j.val, hjn⟩
    show (⟨j.val, hjn⟩ : Fin n) < leastArgmax v hn
    rw [Fin.lt_def]
    show j.val < (leastArgmax v hn).val
    rw [hiext_val] at hjlt
    exact hjlt

/-- The width-monotone layer embedding: an arity-`n` layer becomes an arity-`(n+1)` layer by appending
a DUPLICATE of its last score and last branch. -/
def widenLayer {n : ℕ} (hn : 0 < n) (Lyr : AffineMuxLayer 1 n) : AffineMuxLayer 1 (n + 1) where
  scores := fun j => if h : j.val < n then Lyr.scores ⟨j.val, h⟩ else Lyr.scores ⟨n - 1, by omega⟩
  branches := fun j => if h : j.val < n then Lyr.branches ⟨j.val, h⟩ else Lyr.branches ⟨n - 1, by omega⟩

/-- The widened layer's score VALUES are the `dupLast`-extension of the originals: at every `x`,
`(widenLayer Lyr).scores j).eval x = dupLast (fun i => (Lyr.scores i).eval x) j`. -/
theorem widenLayer_scoreVals {n : ℕ} (hn : 0 < n) (Lyr : AffineMuxLayer 1 n) (x : Fin 1 → ℝ)
    (j : Fin (n + 1)) :
    ((widenLayer hn Lyr).scores j).eval x = dupLast hn (fun i => (Lyr.scores i).eval x) j := by
  show ((if h : j.val < n then Lyr.scores ⟨j.val, h⟩ else Lyr.scores ⟨n - 1, by omega⟩).eval x)
      = (if h : j.val < n then (fun i => (Lyr.scores i).eval x) ⟨j.val, h⟩
          else (fun i => (Lyr.scores i).eval x) ⟨n - 1, by omega⟩)
  by_cases hj : j.val < n
  · rw [dif_pos hj, dif_pos hj]
  · rw [dif_neg hj, dif_neg hj]

/-- **THE WIDENED GATE EQUALS THE EMBEDDED GATE.** The arity-`(n+1)` widened layer selects exactly the
`castSucc`-image of the index the arity-`n` layer selects: the duplicate extra score never wins
(`leastArgmax_dupLast_eq`). -/
theorem widenLayer_gate {n : ℕ} (hn : 0 < n) (Lyr : AffineMuxLayer 1 n) (x : Fin 1 → ℝ) :
    (widenLayer hn Lyr).gate (by omega) x = Fin.castSucc (Lyr.gate hn x) := by
  unfold AffineMuxLayer.gate
  have heq : (fun j => ((widenLayer hn Lyr).scores j).eval x)
      = dupLast hn (fun i => (Lyr.scores i).eval x) := by
    funext j; exact widenLayer_scoreVals hn Lyr x j
  rw [heq]
  exact leastArgmax_dupLast_eq hn (fun i => (Lyr.scores i).eval x)

/-- **THE WIDENED LAYER ACTS IDENTICALLY.** The widened arity-`(n+1)` layer's map equals the original
arity-`n` layer's map: the gate is the embedded gate, and the branch at the `castSucc`-image is the
original branch. -/
theorem widenLayer_applyLayer {n : ℕ} (hn : 0 < n) (Lyr : AffineMuxLayer 1 n) (x : Fin 1 → ℝ) :
    (widenLayer hn Lyr).applyLayer (by omega) x = Lyr.applyLayer hn x := by
  unfold AffineMuxLayer.applyLayer
  rw [widenLayer_gate hn Lyr x]
  -- the branch at castSucc (Lyr.gate ..) is Lyr.branches (Lyr.gate ..)
  set i := Lyr.gate hn x with hi
  have hbranch : (widenLayer hn Lyr).branches (Fin.castSucc i) = Lyr.branches i := by
    have hlt : (Fin.castSucc i).val < n := by rw [Fin.val_castSucc]; exact i.isLt
    show (if h : (Fin.castSucc i).val < n then Lyr.branches ⟨(Fin.castSucc i).val, h⟩
            else Lyr.branches ⟨n - 1, by omega⟩) = Lyr.branches i
    rw [dif_pos hlt]
    have : (⟨(Fin.castSucc i).val, hlt⟩ : Fin n) = i := Fin.ext (by rw [Fin.val_castSucc])
    rw [this]
  rw [hbranch]

/-- **THE WIDENED RUN EQUALS THE ORIGINAL RUN.** -/
theorem widenCascade_run_eq {n : ℕ} (hn : 0 < n) (Lyr : AffineMuxLayer 1 n) (x : Fin 1 → ℝ) :
    (arityCascade (by omega) (widenLayer hn Lyr)).run x = (arityCascade hn Lyr).run x := by
  rw [arityCascade_run, arityCascade_run]
  exact widenLayer_applyLayer hn Lyr x

/-- **THE WIDTH-MONOTONE EMBEDDING `constArityGrade n ⊆ constArityGrade (n+1)`.** A depth-1 arity-`n`
route is a depth-1 arity-`(n+1)` route: widen the single layer by a duplicate of its last
score+branch (`widenCascade_run_eq` keeps the run, hence the route, fixed). The extra index never
wins, so this is a genuine width embedding, not a relabeling. -/
theorem constArityGrade_subset_succ {n : ℕ} (hn : 0 < n) :
    constArityGrade n hn ⊆ constArityGrade (n + 1) (by omega) := by
  rintro f ⟨Lyr, rs, rfl⟩
  refine ⟨widenLayer hn Lyr, rs, ?_⟩
  funext x
  simp only [cascadeRoute]
  rw [widenCascade_run_eq hn Lyr x]

/-! ## (H) THE WIDTH SEPARATION: `constArityGrade n ⊂ constArityGrade (n+1)` -/

/-- **NON-MEMBERSHIP.** The arity-`(n+1)` fan route is NOT in `constArityGrade n`. If it were a
depth-1 arity-`n` route, then along the increasing half-integer grid `halfGrid n` it would change
`≤ 2n − 1` times (`constArityRoute_alternations_le`); but it changes `2n + 1` times
(`fanRoute_alternations_eq`), a contradiction. -/
theorem fanRoute_not_mem_grade {n : ℕ} (hn : 0 < n) :
    fanRoute n ∉ constArityGrade n hn := by
  rintro ⟨Lyr, rs, hf⟩
  -- the witness alternation count along the half-integer grid
  have hwit : seqChanges (fun k => fanRoute n (fun _ => halfGrid n k)) = 2 * n + 1 :=
    fanRoute_alternations_eq n
  -- but as a depth-1 arity-n route it has ≤ 2n − 1 alternations
  have hbound : seqChanges (fun k => fanRoute n (fun _ => halfGrid n k)) ≤ 2 * n - 1 := by
    have hrw : (fun k => fanRoute n (fun _ => halfGrid n k))
        = fun k => cascadeRoute (arityCascade hn Lyr) rs (by norm_num) (fun _ => halfGrid n k) := by
      funext k; rw [hf]
    rw [hrw]
    exact constArityRoute_alternations_le hn Lyr rs (halfGrid n) (halfGrid_increasing n)
  rw [hwit] at hbound
  omega

/-- **THE WIDTH SEPARATION (the second hierarchy direction).** For every `n ≥ 1`,
`constArityGrade n ⊂ constArityGrade (n+1)`: at fixed depth 1, a wider mux (arity `n+1`) realizes
strictly more 1-D route functions than a narrower one (arity `n`). The `⊆` is the width-monotone
duplicate-last embedding (`constArityGrade_subset_succ`); the strictness is the fan witness: the
arity-`(n+1)` fan route lies in arity `(n+1)` (`fanRoute_mem_grade`) but NOT in arity `n`
(`fanRoute_not_mem_grade`, via the arity-`n` alternation bound `≤ 2n − 1` from
`affineArg_alternations_le`, exceeded by the witness's `2n + 1`). Width buys expressivity: the
fixed-depth, varying-arity hierarchy, complementary to the varying-depth, fixed-arity ladder. -/
theorem constArityGrade_ssubset_succ {n : ℕ} (hn : 0 < n) :
    constArityGrade n hn ⊂ constArityGrade (n + 1) (by omega) := by
  refine ⟨constArityGrade_subset_succ hn, ?_⟩
  intro hsubset
  have hmem : fanRoute n ∈ constArityGrade (n + 1) (by omega) := fanRoute_mem_grade n
  have h1 : fanRoute n ∈ constArityGrade n hn := hsubset hmem
  exact fanRoute_not_mem_grade hn h1

end TLT.TemperedDesignLaw.MuxHierarchy
