/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MuxDepthLadderGeneral

/-!
# The general-`(d,k)` depth separation `binCascadeGrade d k L ⊂ binCascadeGrade d k (L+1)`

This module closes the open frontier: the depth-ladder strict separation at GENERAL input dimension
`d ≥ 1` and GENERAL route arity `k ≥ 2`. The 1-D arity-2 case is `binCascadeGrade_ssubset_succ`
(`MuxDepthLadderGeneral.lean`); here we generalize it.

## The new analytic content: the d-general line-alternation bound

The 1-D route-alternation bound `binRoute_alternations_le` is pinned to `MuxCascade 1 L` and to a sample
`fun _ => pts k` of the single carrier coordinate. The genuinely new ingredient is that, in `d`
dimensions, ANY arity-2 cascade restricted to a LINE `ℓ t = fun i => t * v i + x₀ i` still alternates at
most `2^{L+1} − 1` times. We prove this by transcribing the 1-D chain to `d` dimensions along the line:

* the partial-trace fiber affine-on-fiber `runUpTo_eq_prefixMap_on_pfiberDim` (the d-general `PFiberDim`);
* `gate_comp_affine_on_line_eq_arg`: a d-dim layer gate, evaluated through a fixed affine self-map of the
  line, is the `arg` of an explicit `AffineLines 2` of the line parameter `t`, because an affine
  functional of an affine-in-`t` image is affine in `t`. This is the SINGLE new geometric bridge; it lands
  back in the existing 1-D `AffineLines` calculus, so `AffineLines.arg_no_return` /
  `affineArg_alternations_le` apply verbatim;
* `binBitAtDim_block_noReturn`, `binPrefixVecDim_alternations_le`, `binTraceDim_alternations_le`,
  `binRouteDim_block_noReturn`, `binRouteDim_alternations_le` transcribe the doubling chain, reusing the
  dimension-free combinatorics `seqChanges_blockRefine_le` / `seqChanges_comp_le`. For the general route
  arity `k`, the route-on-fiber is a `k`-line argmax (no-return), so confining its realized values to two
  labels forces ≤ one binary flip per fiber; this is what `binRouteDim_alternations_le` exploits (a
  two-valued confinement hypothesis, supplied by the `{0,1}`-valued witness), so the sharp `2^{L+1} − 1`
  bound holds for all `k`.

## The witness and the separation

The witness lifts the 1-D iterated up-tent route to `d` dimensions reading only coordinate `0`
(`liftTentLayer`, `liftRouteScores`). Off-axis coordinates are ignored by the lifted layers (identity
off coordinate `0`, scores read only coordinate `0`), and labels `≥ 2` in the `k`-way readout are made
strictly dominated (constant `−1`), so the lifted route reads the same `{kidx0, kidx1}` value as
`upTentRoute`. Restricting to the line `ℓ t = t • e₀` (`axisDir`) makes the witness alternation count
`= 2^{L+1}` (`liftTentRoute_alternations_eq`, via the dyadic identity `tentMap_iterate_dyadic`),
exceeding the depth-`L` line bound `2^{L+1} − 1`. Hence `binCascadeGrade_ssubset_succ_dim`.
-/

open scoped BigOperators
open Set

noncomputable section

namespace TLT.TemperedDesignLaw.MuxHierarchy

universe u

/-! ## (0) The line `ℓ t = fun i => t * v i + x₀ i` and affine-on-line algebra -/

/-- The parametrized line `lineEval v x₀ t i = t * v i + x₀ i`. -/
def lineEval {d : ℕ} (v x₀ : Fin d → ℝ) (t : ℝ) : Fin d → ℝ := fun i => t * v i + x₀ i

/-- **The key analytic bridge (scalar form).** An affine functional of `d` variables, evaluated on a
fixed affine self-map `A` applied to the line `ℓ t`, is affine in `t`: it equals `α * t + β` for the
explicit slope/intercept built from `f`, `A`, `v`, `x₀`. This is the only genuinely new computation; it
reduces every d-general argmax-along-a-line to a 1-D `AffineLines` family. -/
theorem eval_apply_lineEval {d : ℕ} (f : AffineFunctional d) (A : AffineSelfMap d)
    (v x₀ : Fin d → ℝ) (t : ℝ) :
    f.eval (A.apply (lineEval v x₀ t))
      = (∑ i, f.lin i * (∑ j, A.mat i j * v j)) * t
        + ((∑ i, f.lin i * ((∑ j, A.mat i j * x₀ j) + A.shift i)) + f.const) := by
  simp only [AffineFunctional.eval, AffineSelfMap.apply, lineEval]
  -- expand the inner sum ∑ j, A.mat i j * (t * v j + x₀ j) = t * (∑ j, A.mat i j * v j) + ∑ j, A.mat i j * x₀ j
  have hinner : ∀ i : Fin d,
      (∑ j, A.mat i j * (t * v j + x₀ j)) + A.shift i
        = t * (∑ j, A.mat i j * v j) + ((∑ j, A.mat i j * x₀ j) + A.shift i) := by
    intro i
    have hsplit : (∑ j, A.mat i j * (t * v j + x₀ j))
        = (∑ j, t * (A.mat i j * v j)) + (∑ j, A.mat i j * x₀ j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsplit, Finset.mul_sum, add_assoc]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hinner i])]
  -- now LHS = (∑ i, f.lin i * (t * S i + R i)) + f.const, distribute
  rw [show (∑ i, f.lin i * (t * (∑ j, A.mat i j * v j) + ((∑ j, A.mat i j * x₀ j) + A.shift i)))
      = (∑ i, f.lin i * (∑ j, A.mat i j * v j)) * t
        + (∑ i, f.lin i * ((∑ j, A.mat i j * x₀ j) + A.shift i)) from by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring]
  ring

/-- The `AffineLines n` family obtained by restricting an `n`-family of `d`-dim affine scores to the
line, through a fixed affine self-map `A`. (Arity-generic: used at `n = 2` for trace bits and at
`n = k` for the route.) -/
def lineRestrictScores {d n : ℕ} (scores : Fin n → AffineFunctional d) (A : AffineSelfMap d)
    (v x₀ : Fin d → ℝ) : AffineLines n :=
  AffineLines.mk
    (fun j => ∑ i, (scores j).lin i * (∑ l, A.mat i l * v l))
    (fun j => (∑ i, (scores j).lin i * ((∑ l, A.mat i l * x₀ l) + A.shift i)) + (scores j).const)

/-- **THE ARGMAX-ALONG-A-LINE BRIDGE (arity-generic).** The `leastArgmax` of `n` `d`-dim affine scores,
evaluated through a fixed affine self-map `A` applied to the line `ℓ t`, is the 1-D `arg` of the explicit
`AffineLines n` family `lineRestrictScores scores A v x₀`. The single new geometric fact; it lands back in
the existing 1-D `AffineLines` calculus. -/
theorem argmax_comp_affine_on_line_eq_arg {d n : ℕ} (scores : Fin n → AffineFunctional d)
    (hn : 0 < n) (A : AffineSelfMap d) (v x₀ : Fin d → ℝ) (t : ℝ) :
    leastArgmax (fun j => (scores j).eval (A.apply (lineEval v x₀ t))) hn
      = (lineRestrictScores scores A v x₀).arg hn t := by
  unfold AffineLines.arg
  congr 1
  funext j
  rw [eval_apply_lineEval]
  show _ = (lineRestrictScores scores A v x₀).val j t
  unfold lineRestrictScores AffineLines.val
  ring

/-- The arity-2 specialization: a d-dim arity-2 layer gate, evaluated through `A` on the line, is the
`arg` of `AffineLines 2`. -/
theorem gate_comp_affine_on_line_eq_arg {d : ℕ} (Lyr : AffineMuxLayer d 2) (A : AffineSelfMap d)
    (v x₀ : Fin d → ℝ) (t : ℝ) :
    Lyr.gate (by norm_num) (A.apply (lineEval v x₀ t))
      = (lineRestrictScores Lyr.scores A v x₀).arg (by norm_num) t :=
  argmax_comp_affine_on_line_eq_arg Lyr.scores (by norm_num) A v x₀ t

/-! ## (1) The d-general partial-trace fiber and affine-on-fiber -/

/-- The **partial-trace fiber** predicate at general input dimension `d`: `y` and `x₀` select the same
branch at every layer `< m`. (The `MuxDepthLadderGeneral` `PFiber` is pinned to `d = 1`.) -/
def MuxCascade.PFiberDim {d L : ℕ} (C : MuxCascade d L) (x₀ y : Fin d → ℝ) (m : ℕ) : Prop :=
  ∀ i : Fin L, i.val < m → C.trace y i = C.trace x₀ i

/-- **PARTIAL affine-on-fiber at general `d`.** On the partial-trace fiber of `x₀` (first `m` bits
fixed), `runUpTo m y = (prefixMap x₀ m).apply y`. Same induction as the `d = 1` lemma, using only the
bits `< m`; all steps (`comp_apply`, `trace`, `gate`) are d-general. -/
theorem MuxCascade.runUpTo_eq_prefixMap_on_pfiberDim {d L : ℕ} (C : MuxCascade d L)
    (x₀ y : Fin d → ℝ) :
    ∀ m, C.PFiberDim x₀ y m → C.runUpTo m y = (C.prefixMap x₀ m).apply y := by
  intro m
  induction m with
  | zero => intro _; simp [MuxCascade.runUpTo, MuxCascade.prefixMap]
  | succ m ih =>
      intro hpf
      rw [MuxCascade.runUpTo, MuxCascade.prefixMap]
      by_cases h : m < L
      · rw [dif_pos h, dif_pos h]
        have hpf_m : C.PFiberDim x₀ y m := fun i hi => hpf i (Nat.lt_succ_of_lt hi)
        rw [AffineSelfMap.comp_apply, ← ih hpf_m]
        have hgate : (C.layers ⟨m, h⟩).gate (C.harity ⟨m, h⟩) (C.runUpTo m y)
            = C.trace x₀ ⟨m, h⟩ := by
          have hbit : C.trace y ⟨m, h⟩ = C.trace x₀ ⟨m, h⟩ := hpf ⟨m, h⟩ (Nat.lt_succ_self m)
          simpa [MuxCascade.trace] using hbit
        simp only [AffineMuxLayer.applyLayer, hgate]
      · rw [dif_neg h, dif_neg h]
        exact ih (fun i hi => hpf i (Nat.lt_succ_of_lt hi))

/-! ## (2) The d-general line trace/route alternation chain -/

/-- The layer-`m` gate bit of `binCascade layers` along the line `ℓ t` (or `0` if `m ≥ L`). -/
def binBitAtDim {d L : ℕ} (layers : Fin L → AffineMuxLayer d 2) (v x₀ : Fin d → ℝ)
    (m : ℕ) (t : ℝ) : Fin 2 :=
  if h : m < L then (binCascade layers).trace (lineEval v x₀ t) ⟨m, h⟩ else 0

/-- The **prefix** trace of `binCascade layers` along the line: first `m` bits as actual values, the rest
masked to `0`. -/
def binPrefixVecDim {d L : ℕ} (layers : Fin L → AffineMuxLayer d 2) (v x₀ : Fin d → ℝ)
    (m : ℕ) (t : ℝ) : Fin L → Fin 2 :=
  fun i => if i.val < m then (binCascade layers).trace (lineEval v x₀ t) i else 0

/-- The prefix at `m+1` is the prefix at `m` updated with the layer-`m` bit. -/
theorem binPrefixVecDim_succ_eq {d L : ℕ} (layers : Fin L → AffineMuxLayer d 2)
    (v x₀ : Fin d → ℝ) (m : ℕ) (t : ℝ) :
    binPrefixVecDim layers v x₀ (m + 1) t
      = fun i => if i.val = m then binBitAtDim layers v x₀ m t
                 else binPrefixVecDim layers v x₀ m t i := by
  funext i
  unfold binPrefixVecDim binBitAtDim
  by_cases hi : i.val = m
  · subst hi
    rw [if_pos (Nat.lt_succ_self _), if_pos rfl, dif_pos i.isLt]
  · by_cases hlt : i.val < m
    · rw [if_pos (Nat.lt_succ_of_lt hlt), if_neg hi, if_pos hlt]
    · rw [if_neg (by omega), if_neg hi, if_neg hlt]

/-- **The partial-fiber from prefix-equality (line version).** -/
theorem pfiberDim_of_binPrefixVecDim_eq {d L : ℕ} (layers : Fin L → AffineMuxLayer d 2)
    (v x₀ : Fin d → ℝ) (m : ℕ) (t₁ t₂ : ℝ)
    (heq : binPrefixVecDim layers v x₀ m t₁ = binPrefixVecDim layers v x₀ m t₂) :
    (binCascade layers).PFiberDim (lineEval v x₀ t₁) (lineEval v x₀ t₂) m := by
  intro i hi
  have h := congrFun heq i
  unfold binPrefixVecDim at h
  rw [if_pos hi, if_pos hi] at h
  exact h.symm

/-- **THE BLOCK NO-RETURN FOR THE NEXT BIT (line version).** On any line-sample interval where the
prefix is constant, the layer-`m` bit has no-return: there `runUpTo m` along the line is a single fixed
affine map of the line parameter, so the bit is an affine-argmax of 2 lines (via
`gate_comp_affine_on_line_eq_arg`), whose win-sets are intervals (`arg_no_return`). -/
theorem binBitAtDim_block_noReturn {d L : ℕ} (layers : Fin L → AffineMuxLayer d 2)
    (v x₀ : Fin d → ℝ) {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) (m : ℕ) :
    ∀ a c e : Fin (M + 1), a ≤ c → c ≤ e →
      (∀ f, a ≤ f → f ≤ e →
        binPrefixVecDim layers v x₀ m (pts f) = binPrefixVecDim layers v x₀ m (pts a)) →
      binBitAtDim layers v x₀ m (pts a) = binBitAtDim layers v x₀ m (pts e) →
      binBitAtDim layers v x₀ m (pts c) = binBitAtDim layers v x₀ m (pts a) := by
  intro a c e hac hce hconst hbae
  set C := binCascade layers with hC
  by_cases hm : m < L
  · have hmono : ∀ i j : Fin (M + 1), i ≤ j → pts i ≤ pts j := by
      intro i j hij
      rcases eq_or_lt_of_le hij with h | h
      · rw [h]
      · exact le_of_lt (hinc i j h)
    set A := C.prefixMap (lineEval v x₀ (pts a)) m with hA
    set Lyr := layers ⟨m, hm⟩ with hLyr
    set g := lineRestrictScores Lyr.scores A v x₀ with hg
    -- bit at any prefix-equal-to-a point equals g.arg
    have hbit : ∀ f : Fin (M + 1),
        binPrefixVecDim layers v x₀ m (pts f) = binPrefixVecDim layers v x₀ m (pts a) →
        binBitAtDim layers v x₀ m (pts f) = g.arg (by norm_num) (pts f) := by
      intro f hf
      have hpf : C.PFiberDim (lineEval v x₀ (pts a)) (lineEval v x₀ (pts f)) m :=
        pfiberDim_of_binPrefixVecDim_eq layers v x₀ m (pts a) (pts f) hf.symm
      have hrun : C.runUpTo m (lineEval v x₀ (pts f)) = A.apply (lineEval v x₀ (pts f)) :=
        C.runUpTo_eq_prefixMap_on_pfiberDim (lineEval v x₀ (pts a)) (lineEval v x₀ (pts f)) m hpf
      unfold binBitAtDim
      rw [dif_pos hm]
      have htrace : C.trace (lineEval v x₀ (pts f)) ⟨m, hm⟩
          = Lyr.gate (by norm_num) (C.runUpTo m (lineEval v x₀ (pts f))) := rfl
      rw [htrace, hrun]
      exact gate_comp_affine_on_line_eq_arg Lyr A v x₀ (pts f)
    have ea : binBitAtDim layers v x₀ m (pts a) = g.arg (by norm_num) (pts a) := hbit a rfl
    have ec : binBitAtDim layers v x₀ m (pts c) = g.arg (by norm_num) (pts c) :=
      hbit c (hconst c hac hce)
    have ed : binBitAtDim layers v x₀ m (pts e) = g.arg (by norm_num) (pts e) :=
      hbit e (hconst e (le_trans hac hce) (le_refl _))
    have hargae : g.arg (by norm_num) (pts a) = g.arg (by norm_num) (pts e) := by
      rw [← ea, ← ed]; exact hbae
    have hargc : g.arg (by norm_num) (pts c) = g.arg (by norm_num) (pts a) :=
      g.arg_no_return (by norm_num) (hmono a c hac) (hmono c e hce) rfl hargae.symm
    rw [ec, ea]; exact hargc
  · have h0 : ∀ f, binBitAtDim layers v x₀ m (pts f) = 0 := fun f => by
      unfold binBitAtDim; rw [dif_neg hm]
    rw [h0 c, h0 a]

/-- **THE PREFIX-TRACE DOUBLING BOUND (line version).** Along any increasing line-sample, the
first-`m`-bits prefix trace changes at most `2^m − 1` times. -/
theorem binPrefixVecDim_alternations_le {d L : ℕ} (layers : Fin L → AffineMuxLayer d 2)
    (v x₀ : Fin d → ℝ) {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    ∀ m, seqChanges (fun k => binPrefixVecDim layers v x₀ m (pts k)) ≤ 2 ^ m - 1 := by
  intro m
  induction m with
  | zero =>
      have hconst : ∀ k, binPrefixVecDim layers v x₀ 0 (pts k) = fun _ => 0 := by
        intro k; funext i; unfold binPrefixVecDim; rw [if_neg (Nat.not_lt_zero _)]
      have : seqChanges (fun k => binPrefixVecDim layers v x₀ 0 (pts k))
          = seqChanges (fun _ : Fin (M + 1) => (fun _ : Fin L => (0 : Fin 2))) :=
        seqChanges_congr (fun k => hconst k)
      rw [this]
      unfold seqChanges
      simp
  | succ m ih =>
      have hpair : seqChanges (fun k => binPrefixVecDim layers v x₀ (m + 1) (pts k))
          ≤ seqChanges (fun k => (binPrefixVecDim layers v x₀ m (pts k),
              binBitAtDim layers v x₀ m (pts k))) := by
        have heq : (fun k => binPrefixVecDim layers v x₀ (m + 1) (pts k))
            = fun k => (fun p : (Fin L → Fin 2) × Fin 2 =>
                (fun i => if i.val = m then p.2 else p.1 i))
                (binPrefixVecDim layers v x₀ m (pts k), binBitAtDim layers v x₀ m (pts k)) := by
          funext k; rw [binPrefixVecDim_succ_eq]
        rw [heq]
        exact seqChanges_comp_le
          (fun k => (binPrefixVecDim layers v x₀ m (pts k), binBitAtDim layers v x₀ m (pts k)))
          (fun p : (Fin L → Fin 2) × Fin 2 => (fun i => if i.val = m then p.2 else p.1 i))
      have hbr : seqChanges (fun k => (binPrefixVecDim layers v x₀ m (pts k),
          binBitAtDim layers v x₀ m (pts k)))
          ≤ 2 * seqChanges (fun k => binPrefixVecDim layers v x₀ m (pts k)) + 1 :=
        seqChanges_blockRefine_le _ _
          (fun a c e hac hce hconst hbae =>
            binBitAtDim_block_noReturn layers v x₀ pts hinc m a c e hac hce hconst hbae)
      have hpow : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      calc seqChanges (fun k => binPrefixVecDim layers v x₀ (m + 1) (pts k))
          ≤ 2 * seqChanges (fun k => binPrefixVecDim layers v x₀ m (pts k)) + 1 := le_trans hpair hbr
        _ ≤ 2 * (2 ^ m - 1) + 1 := by omega
        _ = 2 ^ (m + 1) - 1 := by rw [pow_succ]; omega

/-- **THE TRACE ALTERNATION BOUND (line version).** The full active-branch trace of `binCascade layers`
along the line changes at most `2^L − 1` times along any increasing line-sample. -/
theorem binTraceDim_alternations_le {d L : ℕ} (layers : Fin L → AffineMuxLayer d 2)
    (v x₀ : Fin d → ℝ) {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => (binCascade layers).trace (lineEval v x₀ (pts k))) ≤ 2 ^ L - 1 := by
  have hL := binPrefixVecDim_alternations_le layers v x₀ pts hinc L
  have heq : (fun k => binPrefixVecDim layers v x₀ L (pts k))
      = fun k => (binCascade layers).trace (lineEval v x₀ (pts k)) := by
    funext k; funext i; unfold binPrefixVecDim; rw [if_pos i.isLt]
  rw [heq] at hL
  exact hL

/-- **THE ROUTE BLOCK NO-RETURN (arity-`k`, line version).** On any line-sample interval where the FULL
trace is constant (a single trace-fiber), the `k`-way route has no-return: on the fiber the run along the
line is the fixed affine map `fiberMap`, so the route is an affine-argmax of `k` lines (the readout
scores composed with `fiberMap`), whose win-sets are intervals (`arg_no_return`). -/
theorem binRouteDim_block_noReturn {d L k : ℕ} (layers : Fin L → AffineMuxLayer d 2)
    (rs : Fin k → AffineFunctional d) (hk : 0 < k) (v x₀ : Fin d → ℝ)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    ∀ a c e : Fin (M + 1), a ≤ c → c ≤ e →
      (∀ f, a ≤ f → f ≤ e →
        (binCascade layers).trace (lineEval v x₀ (pts f))
          = (binCascade layers).trace (lineEval v x₀ (pts a))) →
      cascadeRoute (binCascade layers) rs hk (lineEval v x₀ (pts e))
        = cascadeRoute (binCascade layers) rs hk (lineEval v x₀ (pts a)) →
      cascadeRoute (binCascade layers) rs hk (lineEval v x₀ (pts c))
        = cascadeRoute (binCascade layers) rs hk (lineEval v x₀ (pts a)) := by
  intro a c e hac hce hconst hbae
  set C := binCascade layers with hC
  have hmono : ∀ i j : Fin (M + 1), i ≤ j → pts i ≤ pts j := by
    intro i j hij
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact le_of_lt (hinc i j h)
  set A := C.fiberMap (lineEval v x₀ (pts a)) with hA
  set g := lineRestrictScores rs A v x₀ with hg
  have hroute : ∀ f : Fin (M + 1),
      C.trace (lineEval v x₀ (pts f)) = C.trace (lineEval v x₀ (pts a)) →
      cascadeRoute C rs hk (lineEval v x₀ (pts f)) = g.arg hk (pts f) := by
    intro f hf
    have hrun : C.run (lineEval v x₀ (pts f)) = A.apply (lineEval v x₀ (pts f)) :=
      C.run_eq_on_fiber (lineEval v x₀ (pts a)) (lineEval v x₀ (pts f)) hf
    unfold cascadeRoute
    rw [hrun]
    exact argmax_comp_affine_on_line_eq_arg rs hk A v x₀ (pts f)
  have ea := hroute a rfl
  have ec := hroute c (hconst c hac hce)
  have ed := hroute e (hconst e (le_trans hac hce) (le_refl _))
  have hargae : g.arg hk (pts a) = g.arg hk (pts e) := by
    rw [← ea, ← ed]; exact hbae.symm
  have hargc : g.arg hk (pts c) = g.arg hk (pts a) :=
    g.arg_no_return hk (hmono a c hac) (hmono c e hce) rfl hargae.symm
  rw [ec, ea]; exact hargc

/-- The binary collapse of a `Fin k` route relative to a distinguished index `z`: `z ↦ 0`, else `↦ 1`. -/
def binCollapse {k : ℕ} (z j : Fin k) : Fin 2 := if j = z then 0 else 1

/-- **THE d-GENERAL LINE-ALTERNATION BOUND `≤ 2^{L+1} − 1` (the new content).** Along any increasing
sample of the line `ℓ t = fun i => t * v i + x₀ i`, IF the `k`-way route of a depth-`L` `binCascade` at
GENERAL input dimension `d` takes only the two distinguished values `{z, o}` (`z ≠ o`) on the sample,
then it changes at most `2^{L+1} − 1` times. Generalizes `binRoute_alternations_le` (`d = 1`, arity-2
route, sample of the bare coordinate) to all `d`, all lines, and all route arities `k` with two-valued
output, via the line-restriction bridge `argmax_comp_affine_on_line_eq_arg`. (The two-valued confinement
is what the genuine non-membership supplies: the realization equals a `{0,1}`-valued witness, so its
`Fin k` route takes only two values, and the no-return on each fiber then forces ≤ one binary flip per
fiber.) -/
theorem binRouteDim_alternations_le {d L k : ℕ} (layers : Fin L → AffineMuxLayer d 2)
    (rs : Fin k → AffineFunctional d) (hk : 0 < k) (v x₀ : Fin d → ℝ)
    {M : ℕ} (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) (z o : Fin k) (hzo : z ≠ o)
    (hbin : ∀ j : Fin (M + 1),
      cascadeRoute (binCascade layers) rs hk (lineEval v x₀ (pts j)) = z ∨
      cascadeRoute (binCascade layers) rs hk (lineEval v x₀ (pts j)) = o) :
    seqChanges (fun k => cascadeRoute (binCascade layers) rs hk (lineEval v x₀ (pts k)))
      ≤ 2 ^ (L + 1) - 1 := by
  -- the binary-collapsed route `b`
  set route : Fin (M + 1) → Fin k :=
    fun j => cascadeRoute (binCascade layers) rs hk (lineEval v x₀ (pts j)) with hroute
  set b : Fin (M + 1) → Fin 2 := fun j => binCollapse z (route j) with hb
  -- on the confined sample, the collapse separates the two values: seqChanges route = seqChanges b
  have hcollapse_inj : ∀ j j' : Fin (M + 1), route j = route j' ↔ b j = b j' := by
    intro j j'
    constructor
    · intro h; rw [hb]; simp only; rw [h]
    · intro h
      have hbj : route j = z ∨ route j = o := hbin j
      have hbj' : route j' = z ∨ route j' = o := hbin j'
      rcases hbj with hj | hj <;> rcases hbj' with hj' | hj'
      · rw [hj, hj']
      · exfalso; rw [hb] at h
        simp only [binCollapse, hj, hj', if_true, if_neg (Ne.symm hzo)] at h
        exact absurd h (by decide)
      · exfalso; rw [hb] at h
        simp only [binCollapse, hj, hj', if_true, if_neg (Ne.symm hzo)] at h
        exact absurd h (by decide)
      · rw [hj, hj']
  have hseq_eq : seqChanges route = seqChanges b := by
    unfold seqChanges
    congr 1
    apply Finset.filter_congr
    intro i _
    simp only [ne_eq, not_iff_not]
    exact hcollapse_inj i.castSucc i.succ
  -- `b` is a function of (trace, route): `b = binCollapse ∘ route`
  rw [hseq_eq]
  -- bound seqChanges b by the block-refine on (trace, b)
  have hcomp : seqChanges b
      ≤ seqChanges (fun k => ((binCascade layers).trace (lineEval v x₀ (pts k)), b k)) := by
    have heq : b = fun k => (fun p : (Fin L → Fin 2) × Fin 2 => p.2)
        ((binCascade layers).trace (lineEval v x₀ (pts k)), b k) := rfl
    rw [heq]
    exact seqChanges_comp_le _ (fun p : (Fin L → Fin 2) × Fin 2 => p.2)
  -- block-no-return for `b`: on a trace-fiber the route is no-return; confined to {0,1} ⟹ b flips ≤ once
  have hbr : seqChanges (fun k => ((binCascade layers).trace (lineEval v x₀ (pts k)), b k))
      ≤ 2 * seqChanges (fun k => (binCascade layers).trace (lineEval v x₀ (pts k))) + 1 := by
    apply seqChanges_blockRefine_le
    intro a c e hac hce huconst hbae
    -- the trace is constant on [a,e]
    have htrconst : ∀ f, a ≤ f → f ≤ e →
        (binCascade layers).trace (lineEval v x₀ (pts f))
          = (binCascade layers).trace (lineEval v x₀ (pts a)) := by
      intro f haf hfe
      have := huconst f haf hfe
      exact this
    -- route has no-return on the fiber: route c, route a related when route e = route a (via b)
    -- We show route a = route e from b a = b e and confinement, then route no-return gives route c = route a.
    have hrae : route a = route e := by
      rw [hcollapse_inj a e]; exact hbae
    have hrouteNR : route c = route a :=
      binRouteDim_block_noReturn layers rs hk v x₀ pts hinc a c e hac hce htrconst hrae.symm
    rw [hb]; simp only; rw [hrouteNR]
  have htrace := binTraceDim_alternations_le layers v x₀ pts hinc
  have hpow : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  calc seqChanges b
      ≤ 2 * seqChanges (fun k => (binCascade layers).trace (lineEval v x₀ (pts k))) + 1 :=
        le_trans hcomp hbr
    _ ≤ 2 * (2 ^ L - 1) + 1 := by omega
    _ = 2 ^ (L + 1) - 1 := by rw [pow_succ]; omega

/-! ## (3) The d-general witness: the coordinate-`0` lifted iterated up-tent route -/

/-- The coordinate-`0` axis direction `e₀ = fun i => if i.val = 0 then 1 else 0`. (Uses `i.val = 0`
to avoid an `OfNat (Fin d) 0` instance, which is unavailable for general `d ≥ 1`.) -/
def axisDir (d : ℕ) : Fin d → ℝ := fun i => if i.val = 0 then 1 else 0

/-- The witness line: `ℓ t = lineEval (axisDir d) 0 t = fun i => if i.val = 0 then t else 0`. -/
theorem axisLine_eq {d : ℕ} (t : ℝ) (i : Fin d) :
    lineEval (axisDir d) (fun _ => 0) t i = if i.val = 0 then t else 0 := by
  unfold lineEval axisDir
  by_cases hi : i.val = 0 <;> simp [hi]

/-- The coordinate-`0` lifted up-tent layer at input dimension `d ≥ 1`: it gates on `2·x 0 − 1 ≥ 0`
(reading only coordinate `0`) and folds coordinate `0` by the tent map, leaving all other coordinates
fixed. The index comparisons use `.val = 0` (no `OfNat (Fin d)` needed). -/
def liftTentLayer (d : ℕ) : AffineMuxLayer d 2 where
  scores := fun i => if i = 0 then ⟨fun l => if l.val = 0 then 2 else 0, -1⟩
                              else ⟨fun l => if l.val = 0 then -2 else 0, 1⟩
  branches := fun i => if i = 0
    then ⟨fun a b => if a.val = 0 ∧ b.val = 0 then -2 else if a = b then 1 else 0,
          fun a => if a.val = 0 then 2 else 0⟩
    else ⟨fun a b => if a.val = 0 ∧ b.val = 0 then 2 else if a = b then 1 else 0,
          fun _ => 0⟩

/-- The coordinate-`0` index, as `Fin d` for `d ≥ 1`. -/
def idx0 {d : ℕ} (hd : 1 ≤ d) : Fin d := ⟨0, by omega⟩

/-- The lifted tent layer's two scores evaluate to `2·x 0 − 1` and `1 − 2·x 0` (reading coord `0`). -/
theorem liftTentLayer_scores {d : ℕ} (hd : 1 ≤ d) (x : Fin d → ℝ) :
    (((liftTentLayer d).scores 0).eval x = 2 * x (idx0 hd) - 1) ∧
    (((liftTentLayer d).scores 1).eval x = 1 - 2 * x (idx0 hd)) := by
  have hval0 : ∀ b : Fin d, b.val = 0 ↔ b = idx0 hd := by
    intro b; constructor
    · intro h; exact Fin.ext (by rw [h]; rfl)
    · intro h; rw [h]; rfl
  constructor
  · show (((liftTentLayer d).scores 0)).eval x = 2 * x (idx0 hd) - 1
    have hs : (liftTentLayer d).scores 0 = ⟨fun l => if l.val = 0 then 2 else 0, -1⟩ := by
      simp [liftTentLayer]
    rw [hs]
    simp only [AffineFunctional.eval]
    rw [Finset.sum_eq_single (idx0 hd)]
    · rw [if_pos (by rfl)]; ring
    · intro b _ hb; rw [if_neg (by rw [hval0 b]; exact hb)]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  · show (((liftTentLayer d).scores 1)).eval x = 1 - 2 * x (idx0 hd)
    have hs : (liftTentLayer d).scores 1 = ⟨fun l => if l.val = 0 then -2 else 0, 1⟩ := by
      simp [liftTentLayer]
    rw [hs]
    simp only [AffineFunctional.eval]
    rw [Finset.sum_eq_single (idx0 hd)]
    · rw [if_pos (by rfl)]; ring
    · intro b _ hb; rw [if_neg (by rw [hval0 b]; exact hb)]; ring
    · intro h; exact absurd (Finset.mem_univ _) h

/-- The lifted tent layer's gate: `0` iff `2·x 0 − 1 ≥ 0` (reads coordinate `0`). -/
theorem liftTentLayer_gate {d : ℕ} (hd : 1 ≤ d) (x : Fin d → ℝ) :
    (liftTentLayer d).gate (by norm_num) x = if 0 ≤ 2 * x (idx0 hd) - 1 then 0 else 1 := by
  simp only [AffineMuxLayer.gate]; rw [leastArgmax_two]
  obtain ⟨h0, h1⟩ := liftTentLayer_scores hd x
  simp only [h0, h1]
  by_cases hx : (0 : ℝ) ≤ 2 * x (idx0 hd) - 1
  · rw [if_pos (by linarith), if_pos hx]
  · rw [if_neg (by push Not at hx ⊢; linarith), if_neg hx]

/-- The lifted tent layer's coordinate-`0` action is `tentMap`: `(applyLayer x) 0 = 1 − |2·x 0 − 1|`. -/
theorem liftTentLayer_apply_coord0 {d : ℕ} (hd : 1 ≤ d) (x : Fin d → ℝ) :
    (liftTentLayer d).applyLayer (by norm_num) x (idx0 hd) = tentMap (x (idx0 hd)) := by
  simp only [AffineMuxLayer.applyLayer, tentMap]
  rw [liftTentLayer_gate hd]
  by_cases hx : (0 : ℝ) ≤ 2 * x (idx0 hd) - 1
  · rw [if_pos hx]
    show ((liftTentLayer d).branches 0).apply x (idx0 hd) = 1 - |2 * x (idx0 hd) - 1|
    have hb : (liftTentLayer d).branches 0
        = ⟨fun a b => if a.val = 0 ∧ b.val = 0 then -2 else if a = b then 1 else 0,
           fun a => if a.val = 0 then 2 else 0⟩ := by simp [liftTentLayer]
    rw [hb]
    simp only [AffineSelfMap.apply]
    rw [Finset.sum_eq_single (idx0 hd)]
    · rw [if_pos ⟨rfl, rfl⟩, if_pos (by rfl), abs_of_nonneg hx]; ring
    · intro b _ hb2
      rw [if_neg (by rintro ⟨_, h2⟩; exact hb2 (Fin.ext (by rw [h2]; rfl))),
          if_neg (fun he => hb2 he.symm)]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hx]
    show ((liftTentLayer d).branches 1).apply x (idx0 hd) = 1 - |2 * x (idx0 hd) - 1|
    have hb : (liftTentLayer d).branches 1
        = ⟨fun a b => if a.val = 0 ∧ b.val = 0 then 2 else if a = b then 1 else 0,
           fun _ => 0⟩ := by simp [liftTentLayer]
    rw [hb]
    simp only [AffineSelfMap.apply]
    rw [Finset.sum_eq_single (idx0 hd)]
    · rw [if_pos ⟨rfl, rfl⟩, abs_of_neg (by linarith : 2 * x (idx0 hd) - 1 < 0)]; ring
    · intro b _ hb2
      rw [if_neg (by rintro ⟨_, h2⟩; exact hb2 (Fin.ext (by rw [h2]; rfl))),
          if_neg (fun he => hb2 he.symm)]; ring
    · intro h; exact absurd (Finset.mem_univ _) h

/-- The depth-`L` coordinate-`0` lifted up-tent cascade. -/
def liftTentCascade (d L : ℕ) : MuxCascade d L := binCascade (fun _ => liftTentLayer d)

/-- **The lifted iterated-tent run reads `tentMap^[m]` on coordinate `0`.** -/
theorem liftTentCascade_runUpTo_coord0 {d : ℕ} (hd : 1 ≤ d) (L : ℕ) (t : ℝ) :
    ∀ m, m ≤ L →
      ((liftTentCascade d L).runUpTo m (lineEval (axisDir d) (fun _ => 0) t)) (idx0 hd)
        = (tentMap^[m]) t := by
  intro m
  induction m with
  | zero =>
      intro _
      show (lineEval (axisDir d) (fun _ => 0) t) (idx0 hd) = _
      rw [axisLine_eq]
      simp only [Function.iterate_zero, id_eq]
      rw [if_pos (by rfl)]
  | succ m ih =>
      intro hm
      rw [MuxCascade.runUpTo, dif_pos (by omega : m < L)]
      show (liftTentLayer d).applyLayer _
          ((liftTentCascade d L).runUpTo m (lineEval (axisDir d) (fun _ => 0) t)) (idx0 hd) = _
      rw [liftTentLayer_apply_coord0 hd]
      rw [ih (by omega)]
      rw [Function.iterate_succ_apply']

/-- The full lifted run's coordinate-`0` value is `tentMap^[L] t`. -/
theorem liftTentCascade_run_coord0 {d : ℕ} (hd : 1 ≤ d) (L : ℕ) (t : ℝ) :
    ((liftTentCascade d L).run (lineEval (axisDir d) (fun _ => 0) t)) (idx0 hd) = (tentMap^[L]) t :=
  liftTentCascade_runUpTo_coord0 hd L t L (le_refl _)

/-! ### (3a) The `k`-way readout confined to `{0,1}` -/

/-- The index `0 : Fin k` for `k ≥ 1`, written with an explicit witness to avoid `OfNat (Fin k)`. -/
def kidx0 {k : ℕ} (hk : 0 < k) : Fin k := ⟨0, hk⟩
/-- The index `1 : Fin k` for `k ≥ 2`. -/
def kidx1 {k : ℕ} (hk2 : 2 ≤ k) : Fin k := ⟨1, by omega⟩

/-- The `k`-way lifted readout: score `0` reads `x 0 − ½`, score `1` reads `½ − x 0` (both on
coordinate `0`), and every score with index `≥ 2` is the constant `−1` (so it is strictly dominated
whenever the coordinate-`0` value lies in `[0,1]`, confining the route to `{0,1}`). -/
def liftRouteScores (d k : ℕ) : Fin k → AffineFunctional d :=
  fun j => if j.val = 0 then ⟨fun l => if l.val = 0 then 1 else 0, -(1/2)⟩
           else if j.val = 1 then ⟨fun l => if l.val = 0 then -1 else 0, 1/2⟩
           else ⟨fun _ => 0, -1⟩

/-- The evaluations of the three readout cases at a point `x` (reading coordinate `0`). -/
theorem liftRouteScores_eval {d k : ℕ} (hd : 1 ≤ d) (x : Fin d → ℝ) (j : Fin k) :
    (liftRouteScores d k j).eval x
      = if j.val = 0 then x (idx0 hd) - 1/2
        else if j.val = 1 then 1/2 - x (idx0 hd)
        else (-1 : ℝ) := by
  have hval0 : ∀ b : Fin d, b.val = 0 ↔ b = idx0 hd := by
    intro b; constructor
    · intro h; exact Fin.ext (by rw [h]; rfl)
    · intro h; rw [h]; rfl
  unfold liftRouteScores
  by_cases h0 : j.val = 0
  · rw [if_pos h0, if_pos h0]
    simp only [AffineFunctional.eval]
    rw [Finset.sum_eq_single (idx0 hd)]
    · rw [if_pos (by rfl)]; ring
    · intro b _ hb; rw [if_neg (by rw [hval0 b]; exact hb)]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : j.val = 1
    · rw [if_pos h1, if_pos h1]
      simp only [AffineFunctional.eval]
      rw [Finset.sum_eq_single (idx0 hd)]
      · rw [if_pos (by rfl)]; ring
      · intro b _ hb; rw [if_neg (by rw [hval0 b]; exact hb)]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg h1, if_neg h1]
      simp only [AffineFunctional.eval]
      rw [Finset.sum_eq_zero (fun i _ => by ring)]; ring

/-- **THE LIFTED ROUTE VALUE FORMULA.** When the final coordinate-`0` value `c = tentMap^[L] t` lies in
`[0,1]`, the `k`-way lifted route reads exactly the same `{0,1}` threshold as the 1-D up-tent route:
`route = kidx0` if `½ ≤ c`, else `kidx1`. The constant `−1` scores (indices `≥ 2`) are strictly
dominated, so the route never leaves `{0,1}`. -/
theorem liftRoute_value {d k : ℕ} (hd : 1 ≤ d) (hk2 : 2 ≤ k) (L : ℕ) (t : ℝ) :
    cascadeRoute (liftTentCascade d L) (liftRouteScores d k) (by omega) (lineEval (axisDir d) (fun _ => 0) t)
      = if 1/2 ≤ (tentMap^[L]) t then kidx0 (by omega) else kidx1 hk2 := by
  set c := (tentMap^[L]) t with hc
  -- the score vector v j = (liftRouteScores d k j).eval (run x)
  set x := lineEval (axisDir d) (fun _ => 0) t with hx
  have hrunc : ((liftTentCascade d L).run x) (idx0 hd) = c := liftTentCascade_run_coord0 hd L t
  set v : Fin k → ℝ := fun j => (liftRouteScores d k j).eval ((liftTentCascade d L).run x) with hv
  -- v 0 = c - 1/2, v 1 = 1/2 - c, v (≥2) = -1
  have hvval : ∀ j : Fin k,
      v j = if j.val = 0 then c - 1/2 else if j.val = 1 then 1/2 - c else (-1 : ℝ) := by
    intro j
    rw [hv]; simp only
    rw [liftRouteScores_eval hd, hrunc]
  unfold cascadeRoute
  show leastArgmax v (by omega) = _
  by_cases hge : (1:ℝ)/2 ≤ c
  · rw [if_pos hge]
    apply isLeastArgmax_unique v _ _ (leastArgmax_spec v (by omega))
    have hk0 : (kidx0 (by omega : 0 < k)).val = 0 := rfl
    have hvk0 : v (kidx0 (by omega)) = c - 1/2 := by
      rw [hvval (kidx0 (by omega)), if_pos hk0]
    constructor
    · intro j
      rw [hvk0, hvval j]
      by_cases h0 : j.val = 0
      · rw [if_pos h0]
      · rw [if_neg h0]
        by_cases h1 : j.val = 1
        · rw [if_pos h1]; linarith
        · rw [if_neg h1]; linarith
    · intro j hj
      exfalso
      have : j.val < (kidx0 (by omega : 0 < k)).val := hj
      simp only [kidx0] at this
      omega
  · rw [if_neg hge]
    push Not at hge
    apply isLeastArgmax_unique v _ _ (leastArgmax_spec v (by omega))
    have hk1 : (kidx1 hk2).val = 1 := rfl
    have hvk1 : v (kidx1 hk2) = 1/2 - c := by
      rw [hvval (kidx1 hk2), if_neg (by rw [hk1]; norm_num), if_pos hk1]
    constructor
    · intro j
      rw [hvk1, hvval j]
      by_cases h0 : j.val = 0
      · rw [if_pos h0]; linarith
      · rw [if_neg h0]
        by_cases h1 : j.val = 1
        · rw [if_pos h1]
        · rw [if_neg h1]; linarith
    · intro j hj
      have hjlt : j.val < (kidx1 hk2).val := hj
      rw [hk1] at hjlt
      have hj0 : j.val = 0 := by omega
      rw [hvk1, hvval j, if_pos hj0]
      linarith

/-! ### (3b) The d-general witness route and its alternation count on the dyadic grid -/

/-- **The d-general witness:** the depth-`(L+1)` coordinate-`0` lifted iterated-tent route with `k`-way
readout. It lies in `binCascadeGrade d k (L+1)` by construction. -/
def liftTentRoute (d k L : ℕ) (hk : 0 < k) : (Fin d → ℝ) → Fin k :=
  cascadeRoute (liftTentCascade d L) (liftRouteScores d k) hk

theorem liftTentRoute_mem_grade {d k L : ℕ} (hk : 0 < k) :
    liftTentRoute d k L hk ∈ binCascadeGrade d k L hk :=
  ⟨fun _ => liftTentLayer d, liftRouteScores d k, rfl⟩

/-- The witness route value on the dyadic grid point `g`: `kidx0` if `g` is odd, `kidx1` if `g` even.
(At an even grid index the final coordinate is `0 < ½`, so the route is `kidx1`; at odd it is `1 ≥ ½`,
route `kidx0`.) -/
theorem liftTentRoute_on_grid {d k : ℕ} (hd : 1 ≤ d) (hk2 : 2 ≤ k) (L : ℕ)
    (g : Fin (2 ^ (L + 1) + 1)) :
    liftTentRoute d k (L + 1) (by omega) (lineEval (axisDir d) (fun _ => 0) (dyadicGrid (L + 1) g))
      = if g.val % 2 = 0 then kidx1 hk2 else kidx0 (by omega) := by
  unfold liftTentRoute dyadicGrid
  have hg_le : g.val ≤ 2 ^ (L + 1) := by have := g.isLt; omega
  have hiter : (tentMap^[L + 1]) ((g.val : ℝ) / 2 ^ (L + 1)) = ((g.val % 2 : ℕ) : ℝ) :=
    tentMap_iterate_dyadic (L + 1) g.val hg_le
  rw [liftRoute_value hd hk2 (L + 1) ((g.val : ℝ) / 2 ^ (L + 1)), hiter]
  by_cases hpar : g.val % 2 = 0
  · rw [hpar, if_pos rfl, if_neg (by norm_num : ¬ (1:ℝ)/2 ≤ ((0 : ℕ) : ℝ))]
  · have hpar1 : g.val % 2 = 1 := by omega
    rw [hpar1, if_neg (by omega : ¬ (1 : ℕ) = 0),
        if_pos (by norm_num : (1:ℝ)/2 ≤ ((1 : ℕ) : ℝ))]

/-- **THE WITNESS ALTERNATION LOWER BOUND `= 2^{L+1}`.** The d-general lifted iterated-tent route changes
value at every one of the `2^{L+1}` adjacent pairs of the dyadic grid (consecutive grid indices have
opposite parity, so the route flips between `kidx0` and `kidx1`, which differ since `k ≥ 2`). -/
theorem liftTentRoute_alternations_eq {d k : ℕ} (hd : 1 ≤ d) (hk2 : 2 ≤ k) (L : ℕ) :
    seqChanges (fun g => liftTentRoute d k (L + 1) (by omega)
        (lineEval (axisDir d) (fun _ => 0) (dyadicGrid (L + 1) g))) = 2 ^ (L + 1) := by
  have hne : kidx0 (by omega : 0 < k) ≠ kidx1 hk2 := by
    intro h; have : (0 : ℕ) = 1 := congrArg Fin.val h; omega
  unfold seqChanges
  have hall : (Finset.univ.filter (fun i : Fin (2 ^ (L + 1)) =>
      (fun g => liftTentRoute d k (L + 1) (by omega)
        (lineEval (axisDir d) (fun _ => 0) (dyadicGrid (L + 1) g))) i.castSucc
      ≠ (fun g => liftTentRoute d k (L + 1) (by omega)
        (lineEval (axisDir d) (fun _ => 0) (dyadicGrid (L + 1) g))) i.succ)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    simp only
    rw [liftTentRoute_on_grid hd hk2, liftTentRoute_on_grid hd hk2]
    have hcs : (i.castSucc : Fin (2 ^ (L + 1) + 1)).val = i.val := Fin.val_castSucc i
    have hsc : (i.succ : Fin (2 ^ (L + 1) + 1)).val = i.val + 1 := Fin.val_succ i
    rw [hcs, hsc]
    rcases Nat.even_or_odd i.val with he | ho
    · obtain ⟨r, hr⟩ := he
      rw [if_pos (by omega), if_neg (by omega)]
      exact (Ne.symm hne)
    · obtain ⟨r, hr⟩ := ho
      rw [if_neg (by omega), if_pos (by omega)]
      exact hne
  rw [hall, Finset.card_univ, Fintype.card_fin]

/-! ## (4) THE NON-MEMBERSHIP AND THE GENERAL-`(d,k)` SEPARATION -/

/-- **NON-MEMBERSHIP (the crux, general `d ≥ 1`, `k ≥ 2`).** The depth-`(L+1)` lifted iterated-tent
route is NOT in `binCascadeGrade d k L`. If it were a depth-`L` arity-2 route on `Fin d → ℝ`, then,
restricting to the coordinate-`0` line and sampling the dyadic grid `dyadicGrid (L+1)`, that route would
take values in `{kidx0, kidx1}` (it equals the witness, which does), so by the d-general line-alternation
bound `binRouteDim_alternations_le` it would change `≤ 2^{L+1} − 1` times. But the witness changes
`2^{L+1}` times (`liftTentRoute_alternations_eq`), a contradiction. This is a genuine proved `∉`: an
alternation-count obstruction along a line, generalizing `upTentRoute_not_mem_grade` to all `d` and `k`. -/
theorem liftTentRoute_not_mem_grade {d k : ℕ} (hd : 1 ≤ d) (hk2 : 2 ≤ k) (L : ℕ) :
    liftTentRoute d k (L + 1) (by omega) ∉ binCascadeGrade d k L (by omega) := by
  rintro ⟨layers, rs, hf⟩
  -- the witness alternation count along the (L+1)-grid line
  have hwit : seqChanges (fun g => liftTentRoute d k (L + 1) (by omega)
      (lineEval (axisDir d) (fun _ => 0) (dyadicGrid (L + 1) g))) = 2 ^ (L + 1) :=
    liftTentRoute_alternations_eq hd hk2 L
  -- as a depth-L route it has ≤ 2^{L+1} − 1 alternations along the line
  -- first: the adversary route equals the witness, hence is {kidx0, kidx1}-valued on the grid line
  have hadv : ∀ g : Fin (2 ^ (L + 1) + 1),
      cascadeRoute (binCascade layers) rs (by omega)
          (lineEval (axisDir d) (fun _ => 0) (dyadicGrid (L + 1) g))
        = liftTentRoute d k (L + 1) (by omega)
          (lineEval (axisDir d) (fun _ => 0) (dyadicGrid (L + 1) g)) := by
    intro g; rw [hf]
  have hbin : ∀ g : Fin (2 ^ (L + 1) + 1),
      cascadeRoute (binCascade layers) rs (by omega)
          (lineEval (axisDir d) (fun _ => 0) (dyadicGrid (L + 1) g)) = kidx1 hk2 ∨
      cascadeRoute (binCascade layers) rs (by omega)
          (lineEval (axisDir d) (fun _ => 0) (dyadicGrid (L + 1) g)) = kidx0 (by omega) := by
    intro g
    rw [hadv g, liftTentRoute_on_grid hd hk2]
    by_cases hpar : g.val % 2 = 0
    · rw [if_pos hpar]; exact Or.inl rfl
    · rw [if_neg hpar]; exact Or.inr rfl
  have hne : kidx1 hk2 ≠ kidx0 (by omega : 0 < k) := by
    intro h; have : (1 : ℕ) = 0 := congrArg Fin.val h; omega
  have hbound : seqChanges (fun g => cascadeRoute (binCascade layers) rs (by omega)
      (lineEval (axisDir d) (fun _ => 0) (dyadicGrid (L + 1) g))) ≤ 2 ^ (L + 1) - 1 :=
    binRouteDim_alternations_le layers rs (by omega) (axisDir d) (fun _ => 0)
      (dyadicGrid (L + 1)) (dyadicGrid_increasing (L + 1)) (kidx1 hk2) (kidx0 (by omega)) hne hbin
  -- rewrite the bound's seqChanges to the witness's via hadv, then contradict
  have hrw : (fun g => cascadeRoute (binCascade layers) rs (by omega)
      (lineEval (axisDir d) (fun _ => 0) (dyadicGrid (L + 1) g)))
      = fun g => liftTentRoute d k (L + 1) (by omega)
          (lineEval (axisDir d) (fun _ => 0) (dyadicGrid (L + 1) g)) := by
    funext g; exact hadv g
  rw [hrw, hwit] at hbound
  have hpow : 1 ≤ 2 ^ (L + 1) := Nat.one_le_two_pow
  omega

/-- **THE GENERAL-`(d,k)` DEPTH-LADDER SEPARATION (the open frontier, closed).** For every input
dimension `d ≥ 1`, route arity `k ≥ 2`, and depth `L`,
`binCascadeGrade d k L ⊂ binCascadeGrade d k (L+1)`. The `⊆` is the depth-monotone identity-layer
embedding at general `d` (`binCascadeGrade_succ_subset_dim`); the strictness is the coordinate-`0` lifted
iterated-tent witness: the depth-`(L+1)` lifted tent route lies in grade `(L+1)`
(`liftTentRoute_mem_grade`) but NOT in grade `L` (`liftTentRoute_not_mem_grade`, via the genuinely-new
d-general line-alternation bound `binRouteDim_alternations_le`). Depth strictly buys expressivity at every
rung, at every input dimension and route arity. -/
theorem binCascadeGrade_ssubset_succ_dim {d k : ℕ} (hd : 1 ≤ d) (hk2 : 2 ≤ k) (L : ℕ) :
    binCascadeGrade d k L (by omega) ⊂ binCascadeGrade d k (L + 1) (by omega) := by
  refine ⟨binCascadeGrade_succ_subset_dim (by omega), ?_⟩
  intro hsubset
  have hmem : liftTentRoute d k (L + 1) (by omega) ∈ binCascadeGrade d k (L + 1) (by omega) :=
    liftTentRoute_mem_grade (by omega)
  have h1 : liftTentRoute d k (L + 1) (by omega) ∈ binCascadeGrade d k L (by omega) := hsubset hmem
  exact liftTentRoute_not_mem_grade hd hk2 L h1

end TLT.TemperedDesignLaw.MuxHierarchy
