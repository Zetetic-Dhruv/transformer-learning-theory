/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.QuadraticExpressivity
import TLT_Proofs.TemperedDesignLaw.MuxWidth
import Mathlib.Data.List.Destutter
import Mathlib.Data.List.NodupEquivFin

/-!
# The general-`n` WIDTH separation for QUADRATIC (self-attention) argmax routes

This file upgrades the *crude* alternation bound `quadArg_alternations_le ≤ 2 n²`
(`QuadraticExpressivity.lean`) to the *tight* Davenport–Schinzel order-2 bound `≤ 2 n − 2`, and
uses it to prove a genuine general-`n` width separation, mirroring the AFFINE width hierarchy
`constArityGrade_ssubset_succ` (`MuxWidth.lean`).

## The four pieces

* **`ds_order2_length_le` (λ₂, the standalone combinatorial crux).** A list `w : List (Fin n)` with
  no two ADJACENT elements equal (`IsChain (· ≠ ·)`) and no length-4 alternation `a,b,a,b` as a
  SUBSEQUENCE (`NoABAB`) has `w.length ≤ 2 n − 1`. This is the classical order-2 Davenport–Schinzel
  bound, NOT in Mathlib, reconstructed here by the *re-occurrence injection*: every position whose
  symbol already appeared (`RO`) injects, via its left neighbour, into the alphabet minus the very
  first symbol (`leftNb_ne_first`, `leftNb_inj_lt`, both no-`abab` contradictions built from
  `four_sublist`); so `#RO ≤ #alphabet − 1`, and `length = #FO + #RO ≤ 2·#alphabet − 1 ≤ 2n − 1`.

* **`quadArg_alternations_le_tight` (the bridge + tight bound).** The argmax of `n` parabolas along
  any increasing sample is no-`abab` (`quadArg_noABAB`: an `a,b,a,b` argmax pattern forces a pair
  comparison to flip ≥ 3 times, contradicting `QuadLines.pair_comparison_le ≤ 2`). Destuttering the
  argmax sample into a list collapses to a no-adjacent-repeat, no-`abab` word of length
  `seqChanges + 1`, so `ds_order2_length_le` gives `seqChanges ≤ 2n − 2`.

* **`quadFan_alternations_eq` (the tight witness).** An explicit fan of `n+1` parabolas: a flat hub
  `val 0 = 0` and `n` sharp downward spikes `val i = 1 − 4(t − i)²`, whose argmax along the
  half-integer sample reads `0, 1, 0, 2, 0, …, 0, n, 0`, achieving exactly `2 n` alternations
  (`2 n + 1` pieces, the tight DS maximum for `n+1` symbols).

* **`quadWidthGrade_ssubset_succ` (the separation).** `quadWidthGrade n ⊂ quadWidthGrade (n+1)`:
  `⊆` via the never-winning duplicate-last parabola embedding (`leastArgmax_dupLast_eq`); `≠` a REAL
  proved non-membership: the `(n+1)`-fan's `2 n` alternations exceed every arity-`n` route's tight
  ceiling `2 n − 2`.
-/

open scoped BigOperators
open List

noncomputable section

namespace TLT.TemperedDesignLaw

open TLT.TemperedDesignLaw.MuxHierarchy

set_option linter.deprecated false

/-! ## Piece (i): the standalone order-2 Davenport–Schinzel length bound `λ₂ ≤ 2n − 1` -/

/-- A list over `Fin n` is **order-2 Davenport–Schinzel admissible** if it has no `a, b, a, b`
alternation as a (not-necessarily-contiguous) `Sublist`. -/
def NoABAB {n : ℕ} (w : List (Fin n)) : Prop :=
  ∀ a b : Fin n, a ≠ b → ¬ ([a, b, a, b] <+ w)

/-- **Build a 4-element alternation sublist from four strictly increasing positions.** If positions
`p < q < r < s` of `w` carry values `a, b, a, b`, then `[a, b, a, b] <+ w`. (Via the
order-embedding characterization of `Sublist`.) -/
theorem four_sublist {n : ℕ} (w : List (Fin n)) (a b : Fin n)
    (p q r s : ℕ) (hp : p < w.length) (hq : q < w.length) (hr : r < w.length) (hs : s < w.length)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (hwp : w.get ⟨p, hp⟩ = a) (hwq : w.get ⟨q, hq⟩ = b)
    (hwr : w.get ⟨r, hr⟩ = a) (hws : w.get ⟨s, hs⟩ = b) :
    [a, b, a, b] <+ w := by
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
  set g : Fin ([a, b, a, b].length) → Fin w.length :=
    fun i => match i with
      | ⟨0, _⟩ => ⟨p, hp⟩
      | ⟨1, _⟩ => ⟨q, hq⟩
      | ⟨2, _⟩ => ⟨r, hr⟩
      | ⟨3, _⟩ => ⟨s, hs⟩
      | ⟨k + 4, h⟩ => absurd h (by simp)
    with hg
  have hmono : StrictMono g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.lt_def] <;> omega
  refine ⟨OrderEmbedding.ofStrictMono g hmono, ?_⟩
  intro ix
  have hgix : (OrderEmbedding.ofStrictMono g hmono) ix = g ix := rfl
  rw [hgix]
  fin_cases ix <;> simp only [hg] <;> simp_all

/-- First-occurrence positions of `w`. -/
def FO {n : ℕ} (w : List (Fin n)) : Finset (Fin w.length) :=
  Finset.univ.filter (fun i => ∀ j : Fin w.length, j < i → w.get j ≠ w.get i)

/-- Re-occurrence positions of `w` (some equal value appears strictly earlier). -/
def RO {n : ℕ} (w : List (Fin n)) : Finset (Fin w.length) :=
  Finset.univ.filter (fun i => ∃ j : Fin w.length, j < i ∧ w.get j = w.get i)

/-- A re-occurrence position has index `≥ 1` (position `0` is always a first occurrence). -/
theorem RO_pos {n : ℕ} (w : List (Fin n)) (i : Fin w.length) (hi : i ∈ RO w) : 1 ≤ i.val := by
  simp only [RO, Finset.mem_filter] at hi
  obtain ⟨j, hji, _⟩ := hi.2
  have : j.val < i.val := hji; omega

/-- `IsChain (· ≠ ·)` means no two adjacent elements are equal. -/
theorem adj_ne {n : ℕ} (w : List (Fin n)) (hch : w.IsChain (· ≠ ·)) (k : ℕ) (hk : k + 1 < w.length) :
    w.get ⟨k, by omega⟩ ≠ w.get ⟨k + 1, hk⟩ := by
  have := hch.getElem (i := k) hk; simpa [List.get_eq_getElem] using this

/-- The left-neighbour symbol of position `i` (when `i.val ≥ 1`). -/
def leftNb {n : ℕ} (w : List (Fin n)) (i : Fin w.length) (hi : 1 ≤ i.val) : Fin n :=
  w.get ⟨i.val - 1, by have := i.isLt; omega⟩

theorem mem_take_of_get_lt {n : ℕ} (w : List (Fin n)) (j : Fin w.length) (k : ℕ) (h : j.val < k) :
    w.get j ∈ w.take k := by
  rw [List.mem_take_iff_getElem]
  exact ⟨j.val, by simp only [lt_min_iff]; exact ⟨h, j.isLt⟩, by rw [List.get_eq_getElem]⟩

/-- Every symbol that occurs has a (minimal) first occurrence position. -/
theorem firstOcc_exists {n : ℕ} (w : List (Fin n)) (x : Fin n) (hx : x ∈ w) :
    ∃ i : Fin w.length, w.get i = x ∧ ∀ j : Fin w.length, j < i → w.get j ≠ x := by
  have hlt : idxOf x w < w.length := List.idxOf_lt_length_iff.mpr hx
  refine ⟨⟨idxOf x w, hlt⟩, List.idxOf_get hlt, ?_⟩
  intro j hji hval
  have hjlt : j.val < idxOf x w := hji
  have hmem : w.get j ∈ w.take (idxOf x w) := mem_take_of_get_lt w j _ hjlt
  rw [hval] at hmem
  rw [List.mem_take_iff_idxOf_lt hx] at hmem
  exact absurd hmem (lt_irrefl _)

/-- `length = #(first occurrences) + #(re-occurrences)`. -/
theorem length_eq {n : ℕ} (w : List (Fin n)) : w.length = (FO w).card + (RO w).card := by
  have hdisj : Disjoint (FO w) (RO w) := by
    rw [Finset.disjoint_left]
    intro i hiFO hiRO
    simp only [FO, RO, Finset.mem_filter] at hiFO hiRO
    obtain ⟨j, hji, hval⟩ := hiRO.2
    exact hiFO.2 j hji hval
  have hunion : FO w ∪ RO w = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro i
    simp only [FO, RO, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : ∃ j : Fin w.length, j < i ∧ w.get j = w.get i
    · exact Or.inr h
    · left; intro j hji hval; exact h ⟨j, hji, hval⟩
  have hc : (FO w).card + (RO w).card = (FO w ∪ RO w).card :=
    (Finset.card_union_of_disjoint hdisj).symm
  rw [hc, hunion, Finset.card_univ, Fintype.card_fin]

/-- `#(first occurrences) = #(distinct symbols)`. -/
theorem FO_card {n : ℕ} (w : List (Fin n)) : (FO w).card = w.toFinset.card := by
  rw [← Finset.card_image_of_injOn (f := fun i => w.get i)]
  · congr 1
    ext x
    simp only [Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨i, _, rfl⟩; exact List.get_mem w i
    · intro hx
      obtain ⟨i, hgi, hmin⟩ := firstOcc_exists w x hx
      refine ⟨i, ?_, hgi⟩
      simp only [FO, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j hji; rw [hgi]; exact hmin j hji
  · intro i hiFO j hjFO hij
    simp only [FO, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hiFO hjFO
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hjFO i h hij
    · exact hiFO j h hij.symm

/-- **The left-neighbour of a re-occurrence is never the first symbol.** If it were, then with
`s = w[0]`, `a = w[i]` (which recurs at some `p < i`), the positions `0, p, i−1, i` carry
`s, a, s, a`, an `abab`, contradicting `NoABAB`. -/
theorem leftNb_ne_first {n : ℕ} (w : List (Fin n)) (hch : w.IsChain (· ≠ ·)) (hab : NoABAB w)
    (hpos : 0 < w.length) (i : Fin w.length) (hi : i ∈ RO w) :
    leftNb w i (RO_pos w i hi) ≠ w.get ⟨0, hpos⟩ := by
  intro hcontra
  have hilt : i.val < w.length := i.isLt
  set s := w.get ⟨0, hpos⟩ with hs
  set a := w.get i with ha
  simp only [RO, Finset.mem_filter] at hi
  obtain ⟨p, hpi, hpa⟩ := hi.2
  have hplt : p.val < i.val := hpi
  have h1i : 1 ≤ i.val := by omega
  have hbound : i.val - 1 + 1 < w.length := by omega
  have hbound' : i.val - 1 < w.length := by omega
  have hbs : w.get ⟨i.val - 1, hbound'⟩ = s := hcontra
  have hane : a ≠ s := by
    rw [ha, ← hbs]
    have hadj := adj_ne w hch (i.val - 1) hbound
    have he1 : (⟨i.val - 1 + 1, hbound⟩ : Fin w.length) = i := by
      apply Fin.ext; show i.val - 1 + 1 = i.val; omega
    rw [he1] at hadj; exact fun h => hadj h.symm
  have hpa' : w.get p = a := hpa
  have hp1 : 1 ≤ p.val := by
    rcases Nat.eq_zero_or_pos p.val with h0 | h1
    · exfalso
      have hpe : p = (⟨0, hpos⟩ : Fin w.length) := by apply Fin.ext; show p.val = 0; omega
      rw [hpe] at hpa'; exact hane (hpa'.symm.trans (by rw [hs]))
    · exact h1
  have hpne : p.val ≠ i.val - 1 := by
    intro hpe
    have heq : p = (⟨i.val - 1, hbound'⟩ : Fin w.length) := by
      apply Fin.ext; show p.val = i.val - 1; omega
    rw [heq] at hpa'; exact hane (hpa'.symm.trans hbs)
  have hfour := four_sublist w s a 0 p (i.val - 1) i.val hpos p.isLt hbound' hilt
    (by omega) (by omega) (by omega) rfl hpa' hbs ha.symm
  exact hab s a (Ne.symm hane) hfour

/-- **The left-neighbour map is injective on re-occurrences.** Two re-occurrences `i < i'` with the
same left neighbour `b` give positions `pₐ, i−1, i, i'−1` carrying `a, b, a, b`, an `abab`. -/
theorem leftNb_inj_lt {n : ℕ} (w : List (Fin n)) (hch : w.IsChain (· ≠ ·)) (hab : NoABAB w)
    (i i' : Fin w.length) (hiRO : i ∈ RO w) (hi'RO : i' ∈ RO w) (hlt : i < i')
    (heq : leftNb w i (RO_pos w i hiRO) = leftNb w i' (RO_pos w i' hi'RO)) : False := by
  have h1i : 1 ≤ i.val := RO_pos w i hiRO
  have h1i' : 1 ≤ i'.val := RO_pos w i' hi'RO
  have hii' : i.val < i'.val := hlt
  have hilt : i.val < w.length := i.isLt
  have hi'lt : i'.val < w.length := i'.isLt
  have hbound_i : i.val - 1 + 1 < w.length := by omega
  set a := w.get i with ha
  set b := leftNb w i (RO_pos w i hiRO) with hb
  have hb_i : w.get ⟨i.val - 1, by omega⟩ = b := rfl
  have hb_i' : w.get ⟨i'.val - 1, by omega⟩ = b := heq.symm
  simp only [RO, Finset.mem_filter] at hiRO
  obtain ⟨pa, hpai, hpaa⟩ := hiRO.2
  have hpalt : pa.val < i.val := hpai
  have hval_pa : w.get pa = a := hpaa
  have hval_i : w.get ⟨i.val, hilt⟩ = a := rfl
  have hab_ne : a ≠ b := by
    rw [← hb_i]
    have hadj := adj_ne w hch (i.val - 1) hbound_i
    have he1 : (⟨i.val - 1 + 1, hbound_i⟩ : Fin w.length) = ⟨i.val, hilt⟩ := by
      apply Fin.ext; show i.val - 1 + 1 = i.val; omega
    rw [he1] at hadj
    show w.get ⟨i.val, hilt⟩ ≠ w.get ⟨i.val - 1, by omega⟩
    exact fun h => hadj h.symm
  have hpane : pa.val ≠ i.val - 1 := by
    intro hpe
    have heqp : pa = (⟨i.val - 1, by omega⟩ : Fin w.length) := by
      apply Fin.ext; show pa.val = i.val - 1; omega
    rw [heqp] at hval_pa
    exact hab_ne (hval_pa.symm.trans hb_i)
  have hi_ne : i.val ≠ i'.val - 1 := by
    intro hpe
    have heqi : (⟨i.val, hilt⟩ : Fin w.length) = ⟨i'.val - 1, by omega⟩ := by apply Fin.ext; exact hpe
    rw [heqi] at hval_i
    exact hab_ne (hval_i.symm.trans hb_i')
  have hfour := four_sublist w a b pa (i.val - 1) i.val (i'.val - 1)
    pa.isLt (by omega) hilt (by omega)
    (by omega) (by omega) (by omega)
    hval_pa hb_i hval_i hb_i'
  exact hab a b hab_ne hfour

theorem leftNbT_mem {n : ℕ} (w : List (Fin n)) (i : Fin w.length) :
    w.get ⟨i.val - 1, by have := i.isLt; omega⟩ ∈ w.toFinset := by
  rw [List.mem_toFinset]; exact List.get_mem w _

/-- **`#(re-occurrences) ≤ #(distinct symbols) − 1`**, the heart of the bound: re-occurrences
inject (via their left neighbour) into the alphabet with the first symbol removed. -/
theorem RO_card_le {n : ℕ} (w : List (Fin n)) (hch : w.IsChain (· ≠ ·)) (hab : NoABAB w)
    (hpos : 0 < w.length) : (RO w).card ≤ w.toFinset.card - 1 := by
  set F : Fin w.length → Fin n := fun i => w.get ⟨i.val - 1, by have := i.isLt; omega⟩ with hF
  have hmaps : Set.MapsTo F (RO w : Set (Fin w.length))
      (↑(w.toFinset \ {w.get ⟨0, hpos⟩})) := by
    intro i hi
    simp only [Finset.coe_sdiff, Finset.coe_singleton, Set.mem_diff, Finset.mem_coe,
      Set.mem_singleton_iff]
    refine ⟨leftNbT_mem w i, ?_⟩
    have := leftNb_ne_first w hch hab hpos i hi
    simpa [hF, leftNb] using this
  have hinj : Set.InjOn F (RO w : Set (Fin w.length)) := by
    intro i hi i' hi' heq
    simp only [Finset.mem_coe] at hi hi'
    have heq' : leftNb w i (RO_pos w i hi) = leftNb w i' (RO_pos w i' hi') := by
      simpa [hF, leftNb] using heq
    rcases lt_trichotomy i i' with h | h | h
    · exact absurd heq' (fun he => (leftNb_inj_lt w hch hab i i' hi hi' h he).elim)
    · exact h
    · exact absurd heq'.symm (fun he => (leftNb_inj_lt w hch hab i' i hi' hi h he).elim)
  have hcard := Finset.card_le_card_of_injOn F hmaps hinj
  rw [Finset.card_sdiff] at hcard
  have h1 : ({w.get ⟨0, hpos⟩} ∩ w.toFinset).card = 1 := by
    rw [Finset.inter_eq_left.mpr]
    · exact Finset.card_singleton _
    · rw [Finset.singleton_subset_iff, List.mem_toFinset]; exact List.get_mem w _
  rw [h1] at hcard; exact hcard

/-- **λ₂, the standalone order-2 Davenport–Schinzel length bound.** A `Fin n`-word with no adjacent
repeats and no `a,b,a,b` alternation has length `≤ 2n − 1`. -/
theorem ds_order2_length_le {n : ℕ} (w : List (Fin n)) (hch : w.IsChain (· ≠ ·))
    (hab : NoABAB w) : w.length ≤ 2 * n - 1 := by
  by_cases hne : w = []
  · subst hne; simp
  · have hpos : 0 < w.length := List.length_pos_iff.mpr hne
    have hlen := length_eq w
    have hfo := FO_card w
    have hro := RO_card_le w hch hab hpos
    have htc : 1 ≤ w.toFinset.card := by
      have hmem : w.get ⟨0, hpos⟩ ∈ w.toFinset := by rw [List.mem_toFinset]; exact List.get_mem w _
      exact Finset.card_pos.mpr ⟨_, hmem⟩
    have htn : w.toFinset.card ≤ n := by
      calc w.toFinset.card ≤ (Finset.univ : Finset (Fin n)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = n := by rw [Finset.card_univ, Fintype.card_fin]
    omega

/-! ## Piece (ii): the bridge from a no-`abab` sample to the tight `seqChanges` bound -/

/-- The number of adjacent changes in a list. -/
def adjChanges {β : Type*} [DecidableEq β] (l : List β) : ℕ :=
  match l with
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if a ≠ b then 1 else 0) + adjChanges (b :: t)

/-- `seqChanges` peels off the first adjacent comparison. -/
theorem seqChanges_cons {β : Type*} [DecidableEq β] {m : ℕ} (s : Fin (m + 2) → β) :
    seqChanges s = (if s 0 ≠ s 1 then 1 else 0) + seqChanges (fun i : Fin (m + 1) => s i.succ) := by
  unfold seqChanges
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.succ_castSucc]; rfl

/-- The length of `destutter'` for the `(· ≠ ·)` relation is `1 + adjChanges`. -/
theorem destutter'_length {β : Type*} [DecidableEq β] (a : β) (l : List β) :
    (l.destutter' (· ≠ ·) a).length = 1 + adjChanges (a :: l) := by
  induction l generalizing a with
  | nil => simp [List.destutter', adjChanges]
  | cons b t ih =>
    rw [List.destutter'_cons]
    by_cases h : (a ≠ b)
    · rw [if_pos h, List.length_cons, ih b]
      simp only [adjChanges, if_pos h]; ring
    · rw [if_neg h, ih a]
      simp only [adjChanges, if_neg h]
      simp only [ne_eq, Decidable.not_not] at h
      subst h; ring

/-- For a nonempty list, `length (destutter (· ≠ ·) l) = 1 + adjChanges l`. -/
theorem destutter_length {β : Type*} [DecidableEq β] (a : β) (l : List β) :
    ((a :: l).destutter (· ≠ ·)).length = 1 + adjChanges (a :: l) := by
  rw [List.destutter_cons']; exact destutter'_length a l

/-- `adjChanges (List.ofFn s) = seqChanges s`. -/
theorem adjChanges_ofFn {β : Type*} [DecidableEq β] : ∀ {m : ℕ} (s : Fin (m + 1) → β),
    adjChanges (List.ofFn s) = seqChanges s := by
  intro m
  induction m with
  | zero =>
    intro s
    rw [show (List.ofFn s) = [s 0] from by rw [List.ofFn_succ]; simp [List.ofFn_zero]]
    simp [adjChanges]; unfold seqChanges; simp
  | succ k ih =>
    intro s
    rw [List.ofFn_succ]
    set s' : Fin (k + 1) → β := fun i => s i.succ with hs'
    rw [show List.ofFn s' = s' 0 :: List.ofFn (fun i : Fin k => s' i.succ) from List.ofFn_succ]
    show (if s 0 ≠ s' 0 then 1 else 0) + adjChanges (s' 0 :: List.ofFn (fun i : Fin k => s' i.succ))
        = seqChanges s
    have hrest : adjChanges (s' 0 :: List.ofFn (fun i : Fin k => s' i.succ)) = seqChanges s' := by
      rw [← List.ofFn_succ]; exact ih s'
    have hs'0 : s' 0 = s 1 := by rw [hs']; simp [Fin.succ_zero_eq_one]
    rw [hrest, hs'0, seqChanges_cons]

/-- **Extract four increasing indices from a `[a,b,a,b] <+ List.ofFn s` alternation.** -/
theorem ofFn_four_indices {β : Type*} {m : ℕ} (s : Fin (m + 1) → β) (a b : β)
    (h : [a, b, a, b] <+ List.ofFn s) :
    ∃ i j k l : Fin (m + 1), i < j ∧ j < k ∧ k < l ∧
      s i = a ∧ s j = b ∧ s k = a ∧ s l = b := by
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq] at h
  obtain ⟨f, hf⟩ := h
  have hlenofn : (List.ofFn s).length = m + 1 := List.length_ofFn
  have h4 : [a, b, a, b].length = 4 := rfl
  let i4 : Fin [a, b, a, b].length := ⟨0, by rw [h4]; omega⟩
  let j4 : Fin [a, b, a, b].length := ⟨1, by rw [h4]; omega⟩
  let k4 : Fin [a, b, a, b].length := ⟨2, by rw [h4]; omega⟩
  let l4 : Fin [a, b, a, b].length := ⟨3, by rw [h4]; omega⟩
  have hij : i4 < j4 := Fin.mk_lt_mk.mpr (by norm_num)
  have hjk : j4 < k4 := Fin.mk_lt_mk.mpr (by norm_num)
  have hkl : k4 < l4 := Fin.mk_lt_mk.mpr (by norm_num)
  refine ⟨Fin.cast hlenofn (f i4), Fin.cast hlenofn (f j4), Fin.cast hlenofn (f k4),
    Fin.cast hlenofn (f l4), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Fin.cast_lt_cast hlenofn).mpr (f.strictMono hij)
  · exact (Fin.cast_lt_cast hlenofn).mpr (f.strictMono hjk)
  · exact (Fin.cast_lt_cast hlenofn).mpr (f.strictMono hkl)
  · have hgi := hf i4; rw [List.get_ofFn] at hgi
    have hlhs : [a, b, a, b].get i4 = a := rfl
    rw [hlhs] at hgi; exact hgi.symm
  · have hgi := hf j4; rw [List.get_ofFn] at hgi
    have hlhs : [a, b, a, b].get j4 = b := rfl
    rw [hlhs] at hgi; exact hgi.symm
  · have hgi := hf k4; rw [List.get_ofFn] at hgi
    have hlhs : [a, b, a, b].get k4 = a := rfl
    rw [hlhs] at hgi; exact hgi.symm
  · have hgi := hf l4; rw [List.get_ofFn] at hgi
    have hlhs : [a, b, a, b].get l4 = b := rfl
    rw [hlhs] at hgi; exact hgi.symm

/-- **A change index exists strictly inside any interval whose endpoints differ.** -/
theorem change_in_range {β : Type*} [DecidableEq β] {M : ℕ} (c : Fin (M + 1) → β)
    (p q : ℕ) (hp : p < M + 1) (hq : q < M + 1) (hpq : p < q) (hne : c ⟨p, hp⟩ ≠ c ⟨q, hq⟩) :
    ∃ e : Fin M, p ≤ e.val ∧ e.val + 1 ≤ q ∧ c e.castSucc ≠ c e.succ := by
  by_contra hcon
  push Not at hcon
  have hconst : ∀ r : ℕ, ∀ hr : r < M + 1, p ≤ r → r ≤ q → c ⟨r, hr⟩ = c ⟨p, hp⟩ := by
    intro r
    induction r with
    | zero =>
        intro hr hpr hrq
        have hp0 : p = 0 := by omega
        congr 1; apply Fin.ext; simp [hp0]
    | succ k ih =>
        intro hr hpr hrq
        rcases Nat.lt_or_ge p (k + 1) with hlt | hge
        · have hkM : k < M := by omega
          have hkp : p ≤ k := by omega
          have hkq : k + 1 ≤ q := by omega
          have hnoch := hcon ⟨k, hkM⟩ hkp hkq
          have hcs : (⟨k, hkM⟩ : Fin M).castSucc = (⟨k, by omega⟩ : Fin (M + 1)) := Fin.ext rfl
          have hsc : (⟨k, hkM⟩ : Fin M).succ = (⟨k + 1, hr⟩ : Fin (M + 1)) := Fin.ext rfl
          rw [hcs, hsc] at hnoch
          rw [← hnoch]
          exact ih (by omega) hkp (by omega)
        · have hpk : p = k + 1 := by omega
          congr 1; apply Fin.ext; simp [hpk]
  exact hne (hconst q hq (le_of_lt hpq) (le_refl q)).symm

/-- **A `0,1,0,1`-style pattern forces `seqChanges ≥ 3`.** Three changes live in three disjoint
ranges. -/
theorem seqChanges_ge_three {β : Type*} [DecidableEq β] {M : ℕ} (c : Fin (M + 1) → β)
    (i j k l : Fin (M + 1)) (hij : i < j) (hjk : j < k) (hkl : k < l)
    (hcij : c i ≠ c j) (hcjk : c j ≠ c k) (hckl : c k ≠ c l) :
    3 ≤ seqChanges c := by
  obtain ⟨e1, he1p, he1q, he1c⟩ := change_in_range c i.val j.val i.isLt j.isLt hij hcij
  obtain ⟨e2, he2p, he2q, he2c⟩ := change_in_range c j.val k.val j.isLt k.isLt hjk hcjk
  obtain ⟨e3, he3p, he3q, he3c⟩ := change_in_range c k.val l.val k.isLt l.isLt hkl hckl
  have hij' : i.val < j.val := hij
  have hjk' : j.val < k.val := hjk
  have hkl' : k.val < l.val := hkl
  have h12 : e1.val < e2.val := by omega
  have h23 : e2.val < e3.val := by omega
  have hne12 : e1 ≠ e2 := by intro h; rw [h] at h12; exact absurd h12 (lt_irrefl _)
  have hne13 : e1 ≠ e3 := by intro h; rw [h] at h12; omega
  have hne23 : e2 ≠ e3 := by intro h; rw [h] at h23; exact absurd h23 (lt_irrefl _)
  set S := Finset.univ.filter (fun i : Fin M => c i.castSucc ≠ c i.succ) with hS
  have hsub : ({e1, e2, e3} : Finset (Fin M)) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with h | h | h <;> subst h <;> assumption
  have hcard3 : ({e1, e2, e3} : Finset (Fin M)).card = 3 :=
    Finset.card_eq_three.mpr ⟨e1, e2, e3, hne12, hne13, hne23, rfl⟩
  calc 3 = ({e1, e2, e3} : Finset (Fin M)).card := hcard3.symm
    _ ≤ S.card := Finset.card_le_card hsub
    _ = seqChanges c := rfl

/-- The least-argmax is a maximizer: `arg t = a → val b t ≤ val a t`. -/
theorem arg_eq_maximizer {n : ℕ} (g : QuadLines n) (hn : 0 < n) (t : ℝ) (a b : Fin n)
    (h : g.arg hn t = a) : g.val b t ≤ g.val a t := by
  have := leastArgmax_is_maximizer (fun i => g.val i t) hn b
  rw [show leastArgmax (fun i => g.val i t) hn = a from h] at this
  exact this

/-- The least-argmax is the least maximizer: `arg t = a → ∀ j < a, val j t < val a t`. -/
theorem arg_eq_least {n : ℕ} (g : QuadLines n) (hn : 0 < n) (t : ℝ) (a j : Fin n)
    (h : g.arg hn t = a) (hj : j < a) : g.val j t < g.val a t := by
  have := leastArgmax_is_least (fun i => g.val i t) hn j
  rw [show leastArgmax (fun i => g.val i t) hn = a from h] at this
  exact this hj

/-- **The argmax sample is `NoABAB`.** An `a,b,a,b` argmax pattern forces the `a`-vs-`b` comparison
indicator to flip ≥ 3 times along the increasing sample (`seqChanges_ge_three`), contradicting the
order-2 per-pair bound `QuadLines.pair_comparison_le ≤ 2`. -/
theorem quadArg_noABAB {n : ℕ} (g : QuadLines n) (hn : 0 < n) {m : ℕ}
    (pts : Fin (m + 1) → ℝ) (hinc : Increasing pts) :
    NoABAB (List.ofFn (fun k => g.arg hn (pts k))) := by
  intro a b hab hsub
  obtain ⟨i, j, k, l, hij, hjk, hkl, hai, hbj, hak, hbl⟩ :=
    ofFn_four_indices (fun k => g.arg hn (pts k)) a b hsub
  -- choose comparison orientation by index order of a, b
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · -- a < b : indicator c t = [val a t < val b t] reads 0,1,0,1
    set c : Fin (m + 1) → Fin 2 :=
      fun t => if g.val a (pts t) < g.val b (pts t) then (1 : Fin 2) else 0 with hc
    -- value at an `arg = a` point is 0 (a maximizer ⟹ ¬(val a < val b))
    have hca : ∀ t, g.arg hn (pts t) = a → c t = 0 := by
      intro t ht
      have hle : g.val b (pts t) ≤ g.val a (pts t) := arg_eq_maximizer g hn (pts t) a b ht
      rw [hc]; simp only; rw [if_neg (by linarith)]
    -- value at an `arg = b` point is 1 (a < b least ⟹ val a < val b strict)
    have hcb : ∀ t, g.arg hn (pts t) = b → c t = 1 := by
      intro t ht
      have hlt' : g.val a (pts t) < g.val b (pts t) := arg_eq_least g hn (pts t) b a ht hlt
      rw [hc]; simp only; rw [if_pos hlt']
    have hci := hca i hai
    have hcj := hcb j hbj
    have hck := hca k hak
    have hcl := hcb l hbl
    have h3 : 3 ≤ seqChanges c :=
      seqChanges_ge_three c i j k l hij hjk hkl
        (by rw [hci, hcj]; decide) (by rw [hcj, hck]; decide) (by rw [hck, hcl]; decide)
    have h2 : seqChanges c ≤ 2 := g.pair_comparison_le a b pts hinc
    omega
  · -- b < a : indicator c t = [val b t < val a t] reads 0,1,0,1
    set c : Fin (m + 1) → Fin 2 :=
      fun t => if g.val b (pts t) < g.val a (pts t) then (1 : Fin 2) else 0 with hc
    have hca : ∀ t, g.arg hn (pts t) = a → c t = 1 := by
      intro t ht
      have hlt' : g.val b (pts t) < g.val a (pts t) := arg_eq_least g hn (pts t) a b ht hgt
      rw [hc]; simp only; rw [if_pos hlt']
    have hcb : ∀ t, g.arg hn (pts t) = b → c t = 0 := by
      intro t ht
      have hle : g.val a (pts t) ≤ g.val b (pts t) := arg_eq_maximizer g hn (pts t) b a ht
      rw [hc]; simp only; rw [if_neg (by linarith)]
    have hci := hca i hai
    have hcj := hcb j hbj
    have hck := hca k hak
    have hcl := hcb l hbl
    have h3 : 3 ≤ seqChanges c :=
      seqChanges_ge_three c i j k l hij hjk hkl
        (by rw [hci, hcj]; decide) (by rw [hcj, hck]; decide) (by rw [hck, hcl]; decide)
    have h2 : seqChanges c ≤ 2 := g.pair_comparison_le b a pts hinc
    omega

/-- **THE TIGHT BOUND (Davenport–Schinzel order 2).** Along ANY strictly-increasing sample, the
active index of `n` parabolas changes value at most `2n − 2` times. This is the tight upgrade of the
crude `quadArg_alternations_le ≤ 2 n²`. -/
theorem quadArg_alternations_le_tight {n : ℕ} (g : QuadLines n) (hn : 0 < n) {m : ℕ}
    (pts : Fin (m + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => g.arg hn (pts k)) ≤ 2 * n - 2 := by
  classical
  set q : Fin (m + 1) → Fin n := fun k => g.arg hn (pts k) with hq
  -- the destuttered sample: a no-adjacent-repeat, no-abab word over Fin n
  set w : List (Fin n) := (List.ofFn q).destutter (· ≠ ·) with hw
  -- length = seqChanges + 1
  have hofn_ne : List.ofFn q ≠ [] := by
    rw [← List.length_pos_iff, List.length_ofFn]; omega
  obtain ⟨hd, tl, hdl⟩ := List.exists_cons_of_ne_nil hofn_ne
  have hlen : w.length = seqChanges q + 1 := by
    rw [hw, hdl, destutter_length, ← hdl, adjChanges_ofFn]; ring
  -- w is IsChain (≠)
  have hchain : w.IsChain (· ≠ ·) := List.isChain_destutter _ _
  -- w is NoABAB (inherited from ofFn q via destutter_sublist)
  have hnoabab : NoABAB w := by
    intro a b hab hsub
    have hsub' : [a, b, a, b] <+ List.ofFn q :=
      hsub.trans (List.destutter_sublist (· ≠ ·) (List.ofFn q))
    exact quadArg_noABAB g hn pts hinc a b hab hsub'
  -- apply λ₂
  have hbound := ds_order2_length_le w hchain hnoabab
  rw [hlen] at hbound
  omega

/-! ## Piece (iii): the tight witness: a fan of `n+1` parabolas with `2n` alternations -/

/-- The fan of `n + 1` parabolas: a flat hub `val 0 t = 0` and `n` sharp downward spikes
`val i t = 1 − 4(t − i)²` (`i = 1 … n`). The spike `i` is the unique winner at `t = i`. -/
def quadFan (n : ℕ) : QuadLines (n + 1) where
  A := fun i => if i.val = 0 then 0 else -4
  a := fun i => if i.val = 0 then 0 else 8 * (i.val : ℝ)
  c := fun i => if i.val = 0 then 0 else 1 - 4 * (i.val : ℝ) ^ 2

theorem quadFan_val0 (n : ℕ) (j : Fin (n + 1)) (hj : j.val = 0) (t : ℝ) :
    (quadFan n).val j t = 0 := by
  simp only [QuadLines.val, quadFan, hj, if_pos]; norm_num

theorem quadFan_vali (n : ℕ) (i : Fin (n + 1)) (hi : i.val ≠ 0) (t : ℝ) :
    (quadFan n).val i t = 1 - 4 * (t - (i.val : ℝ)) ^ 2 := by
  simp only [QuadLines.val, quadFan, if_neg hi]; ring

/-- **At a half-integer `t = m + ½` the hub (index `0`) wins.** Every spike value
`1 − 4(m+½−i)² ≤ 0`, since `2(m+½−i) = 2m+1−2i` is odd, hence `|m+½−i| ≥ ½`. -/
theorem quadFan_arg_hub (n : ℕ) (m : ℕ) (_hm : m ≤ n) :
    (quadFan n).arg (by omega) ((m : ℝ) + 1 / 2) = ⟨0, by omega⟩ := by
  apply isLeastArgmax_unique _ _ _ (leastArgmax_spec _ _)
  refine ⟨?_, ?_⟩
  · intro j
    show (quadFan n).val j ((m : ℝ) + 1 / 2) ≤ (quadFan n).val ⟨0, by omega⟩ ((m : ℝ) + 1 / 2)
    rw [quadFan_val0 n ⟨0, by omega⟩ rfl]
    by_cases hj : j.val = 0
    · rw [quadFan_val0 n j hj]
    · rw [quadFan_vali n j hj]
      have hsq : ((m : ℝ) + 1 / 2 - (j.val : ℝ)) ^ 2 ≥ 1 / 4 := by
        have hint : (1 : ℤ) ≤ (2 * (m : ℤ) + 1 - 2 * (j.val : ℤ)) ^ 2 := by
          have hne : (2 * (m : ℤ) + 1 - 2 * (j.val : ℤ)) ≠ 0 := by omega
          rcases lt_or_gt_of_ne hne with hl | hg
          · nlinarith
          · nlinarith
        have hcast : (1 : ℝ) ≤ (2 * (m : ℝ) + 1 - 2 * (j.val : ℝ)) ^ 2 := by exact_mod_cast hint
        nlinarith [hcast]
      nlinarith [hsq]
  · intro j hj
    exact absurd hj (by simp [Fin.lt_def])

/-- **At an integer `t = i` (`1 ≤ i ≤ n`) the spike `i` is the unique winner.** -/
theorem quadFan_arg_spike (n : ℕ) (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    (quadFan n).arg (by omega) (i : ℝ) = ⟨i, by omega⟩ := by
  have hival : (⟨i, by omega⟩ : Fin (n + 1)).val ≠ 0 := by simp; omega
  apply isLeastArgmax_unique _ _ _ (leastArgmax_spec _ _)
  refine ⟨?_, ?_⟩
  · intro j
    show (quadFan n).val j (i : ℝ) ≤ (quadFan n).val ⟨i, by omega⟩ (i : ℝ)
    rw [quadFan_vali n ⟨i, by omega⟩ hival]
    have hself : (1 : ℝ) - 4 * ((i : ℝ) - ((⟨i, by omega⟩ : Fin (n + 1)).val : ℝ)) ^ 2 = 1 := by
      norm_num
    rw [hself]
    by_cases hj : j.val = 0
    · rw [quadFan_val0 n j hj]; norm_num
    · rw [quadFan_vali n j hj]
      nlinarith [sq_nonneg ((i : ℝ) - (j.val : ℝ))]
  · intro j hj
    show (quadFan n).val j (i : ℝ) < (quadFan n).val ⟨i, by omega⟩ (i : ℝ)
    rw [quadFan_vali n ⟨i, by omega⟩ hival]
    have hself : (1 : ℝ) - 4 * ((i : ℝ) - ((⟨i, by omega⟩ : Fin (n + 1)).val : ℝ)) ^ 2 = 1 := by
      norm_num
    rw [hself]
    have hjlt : j.val < i := hj
    by_cases hj0 : j.val = 0
    · rw [quadFan_val0 n j hj0]; norm_num
    · rw [quadFan_vali n j hj0]
      have hdiff : (1 : ℝ) ≤ ((i : ℝ) - (j.val : ℝ)) := by
        have : (j.val : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast (by omega : j.val + 1 ≤ i)
        linarith
      nlinarith [hdiff]

/-- The increasing sample `pts k = (k + 1) / 2`, `k = 0 … 2n`, of `2n + 1` points. -/
def fanPts (n : ℕ) : Fin (2 * n + 1) → ℝ := fun k => ((k.val : ℝ) + 1) / 2

theorem fanPts_increasing (n : ℕ) : Increasing (fanPts n) := by
  intro i j hij
  unfold fanPts
  have : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast (Fin.lt_def.mp hij)
  linarith

/-- **The fan argmax along the sample, indexed by parity.** At even `k = 2r` (a half-integer point)
the hub `0` wins; at odd `k = 2r+1` (an integer point `r+1`) the spike `r+1` wins. -/
theorem quadFan_arg_fanPts (n : ℕ) (k : Fin (2 * n + 1)) :
    (quadFan n).arg (by omega) (fanPts n k)
      = if k.val % 2 = 0 then ⟨0, by omega⟩ else ⟨(k.val + 1) / 2, by have := k.isLt; omega⟩ := by
  have hk : k.val < 2 * n + 1 := k.isLt
  unfold fanPts
  rcases Nat.even_or_odd k.val with he | ho
  · -- even: k = 2r, point = r + 1/2, hub
    obtain ⟨r, hr⟩ := he
    have hrn : r ≤ n := by omega
    rw [if_pos (by omega)]
    have hpt : ((k.val : ℝ) + 1) / 2 = (r : ℝ) + 1 / 2 := by rw [hr]; push_cast; ring
    rw [hpt]
    exact quadFan_arg_hub n r hrn
  · -- odd: k = 2r+1, point = r + 1, spike (r+1)
    obtain ⟨r, hr⟩ := ho
    have hrn : r + 1 ≤ n := by omega
    rw [if_neg (by omega)]
    have hpt : ((k.val : ℝ) + 1) / 2 = ((r + 1 : ℕ) : ℝ) := by rw [hr]; push_cast; ring
    rw [hpt, quadFan_arg_spike n (r + 1) (by omega) hrn]
    congr 1; show r + 1 = (k.val + 1) / 2; omega

/-- **THE WITNESS ALTERNATION COUNT `= 2n`.** The `(n+1)`-fan's argmax flips at every one of the
`2n` adjacent pairs of the sample (consecutive indices have opposite parity, so the argmax toggles
between the hub and a spike). This is the tight DS maximum for `n + 1` symbols. -/
theorem quadFan_alternations_eq (n : ℕ) :
    seqChanges (fun k => (quadFan n).arg (by omega) (fanPts n k)) = 2 * n := by
  unfold seqChanges
  have hall : (Finset.univ.filter (fun i : Fin (2 * n) =>
      (fun k => (quadFan n).arg (by omega) (fanPts n k)) i.castSucc
        ≠ (fun k => (quadFan n).arg (by omega) (fanPts n k)) i.succ)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    simp only
    -- compare via .val
    intro hcon
    have hval : ((quadFan n).arg (by omega) (fanPts n i.castSucc)).val
        = ((quadFan n).arg (by omega) (fanPts n i.succ)).val := by rw [hcon]
    rw [quadFan_arg_fanPts, quadFan_arg_fanPts] at hval
    have hcs : (i.castSucc : Fin (2 * n + 1)).val = i.val := Fin.val_castSucc i
    have hsc : (i.succ : Fin (2 * n + 1)).val = i.val + 1 := Fin.val_succ i
    rcases Nat.even_or_odd i.val with he | ho
    · obtain ⟨r, hr⟩ := he
      rw [if_pos (by rw [hcs]; omega), if_neg (by rw [hsc]; omega)] at hval
      simp only [hsc] at hval; omega
    · obtain ⟨r, hr⟩ := ho
      rw [if_neg (by rw [hcs]; omega), if_pos (by rw [hsc]; omega)] at hval
      simp only [hcs] at hval; omega
  rw [hall, Finset.card_univ, Fintype.card_fin]

/-! ## Piece (iii): the width grade, the embedding, and the SEPARATION -/

/-- `seqChanges` is preserved by an injective post-composition. -/
theorem seqChanges_inj_comp {β γ : Type*} [DecidableEq β] [DecidableEq γ] {m : ℕ}
    (s : Fin (m + 1) → β) (f : β → γ) (hf : Function.Injective f) :
    seqChanges (fun k => f (s k)) = seqChanges s := by
  unfold seqChanges
  congr 1
  apply Finset.filter_congr
  intro i _
  simp only [ne_eq]
  constructor
  · intro h heq; exact h (by rw [heq])
  · intro h heq; exact h (hf heq)

/-- **The depth-1 quadratic-argmax width grade.** `quadWidthGrade n hn` is the set of integer-valued
route functions `ℝ → ℕ` realizable as `t ↦ (g.arg hn t).val` for SOME family `g : QuadLines n` of
`n` parabolas. Fixing arity `= n` makes "widening the fan" meaningful. -/
def quadWidthGrade (n : ℕ) (hn : 0 < n) : Set (ℝ → ℕ) :=
  { f | ∃ g : QuadLines n, f = fun t => ((g.arg hn t).val) }

/-- The duplicate-last extension of a `QuadLines n` family to `QuadLines (n+1)`: parabola `n`
duplicates parabola `n−1`. -/
def quadWiden {n : ℕ} (hn : 0 < n) (g : QuadLines n) : QuadLines (n + 1) where
  A := dupLast hn g.A
  a := dupLast hn g.a
  c := dupLast hn g.c

/-- The widened family's value vector is the `dupLast`-extension of the original's value vector. -/
theorem quadWiden_val {n : ℕ} (hn : 0 < n) (g : QuadLines n) (t : ℝ) (j : Fin (n + 1)) :
    (quadWiden hn g).val j t = dupLast hn (fun i => g.val i t) j := by
  show (quadWiden hn g).A j * t ^ 2 + (quadWiden hn g).a j * t + (quadWiden hn g).c j
      = dupLast hn (fun i => g.val i t) j
  simp only [quadWiden, dupLast, QuadLines.val]
  by_cases hj : j.val < n
  · simp only [dif_pos hj]
  · simp only [dif_neg hj]

/-- **The widened argmax equals the embedded argmax.** The duplicate parabola never wins, so
`(quadWiden g).arg t = castSucc (g.arg t)` (`leastArgmax_dupLast_eq`), hence the `ℕ`-route is
unchanged. -/
theorem quadWiden_arg {n : ℕ} (hn : 0 < n) (g : QuadLines n) (t : ℝ) :
    (quadWiden hn g).arg (by omega) t = Fin.castSucc (g.arg hn t) := by
  show leastArgmax (fun j => (quadWiden hn g).val j t) (by omega) = _
  have heq : (fun j => (quadWiden hn g).val j t) = dupLast hn (fun i => g.val i t) := by
    funext j; exact quadWiden_val hn g t j
  rw [heq]
  exact leastArgmax_dupLast_eq hn (fun i => g.val i t)

/-- **The width-monotone embedding `quadWidthGrade n ⊆ quadWidthGrade (n+1)`.** -/
theorem quadWidthGrade_subset_succ {n : ℕ} (hn : 0 < n) :
    quadWidthGrade n hn ⊆ quadWidthGrade (n + 1) (by omega) := by
  rintro f ⟨g, rfl⟩
  refine ⟨quadWiden hn g, ?_⟩
  funext t
  rw [quadWiden_arg hn g t, Fin.val_castSucc]

/-- The fan's `ℕ`-route lies in `quadWidthGrade (n+1)`. -/
theorem fanRoute_mem (n : ℕ) :
    (fun t => ((quadFan n).arg (by omega : 0 < n + 1) t).val) ∈ quadWidthGrade (n + 1) (by omega) :=
  ⟨quadFan n, rfl⟩

/-- **NON-MEMBERSHIP.** The `(n+1)`-fan route is NOT in `quadWidthGrade n`: along `fanPts` it would
change `≤ 2n − 2` times (`quadArg_alternations_le_tight`), but it changes `2n` times
(`quadFan_alternations_eq`). -/
theorem fanRoute_not_mem {n : ℕ} (hn : 0 < n) :
    (fun t => ((quadFan n).arg (by omega : 0 < n + 1) t).val) ∉ quadWidthGrade n hn := by
  rintro ⟨g, hg⟩
  -- the fan's alternation count along fanPts (Fin (n+1)-valued)
  have hwit : seqChanges (fun k => (quadFan n).arg (by omega) (fanPts n k)) = 2 * n :=
    quadFan_alternations_eq n
  -- pushing through Fin.val (injective) preserves the count: still 2n
  have hwitval : seqChanges (fun k => ((quadFan n).arg (by omega : 0 < n + 1) (fanPts n k)).val)
      = 2 * n := by
    rw [seqChanges_inj_comp (fun k => (quadFan n).arg (by omega) (fanPts n k))
      (fun i : Fin (n + 1) => i.val) Fin.val_injective]
    exact hwit
  -- but as an arity-n route via g it factors as Fin.val ∘ g.arg, so ≤ 2n − 2
  have hfac : (fun k => ((quadFan n).arg (by omega : 0 < n + 1) (fanPts n k)).val)
      = fun k => ((g.arg hn (fanPts n k)).val) := by
    funext k; have := congrFun hg (fanPts n k); simpa using this
  have hbound : seqChanges (fun k => ((g.arg hn (fanPts n k)).val)) ≤ 2 * n - 2 := by
    calc seqChanges (fun k => ((g.arg hn (fanPts n k)).val))
        ≤ seqChanges (fun k => g.arg hn (fanPts n k)) :=
          seqChanges_comp_le (fun k => g.arg hn (fanPts n k)) (fun i : Fin n => i.val)
      _ ≤ 2 * n - 2 := quadArg_alternations_le_tight g hn (fanPts n) (fanPts_increasing n)
  rw [hfac] at hwitval
  omega

/-- **THE QUADRATIC WIDTH SEPARATION (general `n`).** For every `n ≥ 1`,
`quadWidthGrade n ⊂ quadWidthGrade (n+1)`: a wider fan of quadratic (self-attention) scores realizes
strictly more argmax-route functions. `⊆` is the never-winning duplicate-last embedding
(`quadWidthGrade_subset_succ`); strictness is the explicit `(n+1)`-fan witness, whose `2 n`
alternations exceed the arity-`n` tight Davenport–Schinzel ceiling `2 n − 2`
(`quadArg_alternations_le_tight`), a REAL proved non-membership. -/
theorem quadWidthGrade_ssubset_succ {n : ℕ} (hn : 0 < n) :
    quadWidthGrade n hn ⊂ quadWidthGrade (n + 1) (by omega) := by
  refine ⟨quadWidthGrade_subset_succ hn, ?_⟩
  intro hsubset
  have hmem := fanRoute_mem n
  have h1 := hsubset hmem
  exact fanRoute_not_mem hn h1

end TLT.TemperedDesignLaw
