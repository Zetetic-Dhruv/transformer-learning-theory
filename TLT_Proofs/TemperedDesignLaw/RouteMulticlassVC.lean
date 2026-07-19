/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.CascadeCompositionVC
import FLT_Proofs.Complexity.Structures
import FLT_Proofs.Complexity.IndependentVC.Finiteness

/-!
# The multiclass capacity (single Natarajan number) of the depth-`L` route-trace class (R7)

The compositional growth bound `cascadeTrace_growth_prod` (`CascadeCompositionVC.lean`) controls the
number of route-trace *patterns* the depth-`L` argmax cascade realises on a finite sample. This file
packages that capacity into the **one multiclass invariant** the learning pathway needs: a single
`WithTop ℕ` number, the **Natarajan dimension** of the route-trace concept class, and proves it
**finite**.

## The route-trace concept class and its multiclass capacity

* `cascadeTraceClass C hk : ConceptClass X (∀ ℓ, Fin (k ℓ))` — the route-trace class
  `Set.range (cascadeTrace C hk)`: the set of all per-input route traces `x ↦ (route_0 x, …)` as the
  joint parameter ranges. The multiclass codomain `∀ ℓ, Fin (k ℓ)` is a `Fintype`, so the textbook
  Natarajan dimension `NatarajanDim X (∀ ℓ, Fin (k ℓ)) (cascadeTraceClass C hk)` is defined.

## The locked result

* `cascadeTraceClass_natarajanDim_lt_top` (**R7, the multiclass capacity is finite**): under
  per-(layer, ordered-pair) linearity of the score differences (each in a finite-dimensional `W ℓ p`),
  `NatarajanDim X (∀ ℓ, Fin (k ℓ)) (cascadeTraceClass C hk) < ⊤`. General in the depth `L`, the
  per-layer arities `k ℓ`, the input space `X`, and the per-(layer, pair) finite-dimensional
  score-difference spaces `W ℓ p`. Conditional on `hlin` (false for arbitrary measurable scores).

## Proof architecture (M-Contrapositive shell over an M-Pipeline)

The Natarajan dimension is an `iSup` over Natarajan-shattered finite sets `S`. The mechanism:

1. **Natarajan-shatter ⇒ `2^{|S|}` patterns.** If `S` is Natarajan-shattered with disagreeing
   witnesses `f₀ ≠ f₁`, the `2^{|S|}` Boolean selections `b : ↥S → Bool` inject (via
   `b ↦ (x ↦ if b x then f₀ x else f₁ x)`, injective because `f₀ x ≠ f₁ x`) into the route-trace
   restriction range on `S` (each selection is realised by some parameter). So
   `2^{|S|} ≤ (Set.range (cascadeTraceRestr C hk S)).ncard`
   (`two_pow_card_le_traceRestr_ncard_of_natShatters`).
2. **Growth bound.** `cascadeTrace_growth_prod` bounds that range by the (layer × pair) product of
   Sauer–Shelah sums, which `cascadeTrace_growth_poly` collapses to one polynomial `K · |S|^D` of
   degree `D = ∑_ℓ ∑_p finrank ℝ (W ℓ p)`.
3. **Downward closure.** Natarajan-shattering is closed under subsets of the sample
   (`natShatters_of_subset`), so an infinite Natarajan dimension produces Natarajan-shattered sets of
   *every* size `m`, hence `2^m ≤ K · m^D` for all large `m`.
4. **Exponential beats polynomial.** `no_eventually_two_pow_le_poly` (FLT) refutes that. Hence the
   dimension is finite.
-/

noncomputable section

open Module Filter

namespace TLT.TemperedDesignLaw

universe u

variable {X : Type u} [MeasurableSpace X]

/-! ### The route-trace concept class -/

/-- **The depth-`L` route-trace concept class.** `Set.range (cascadeTrace C hk)`: the set of all
per-input route traces `x ↦ (ℓ ↦ route_ℓ x)` as the joint parameter ranges, a `ConceptClass` over the
finite multiclass label space `∀ ℓ, Fin (k ℓ)`. This is the multiclass object whose single Natarajan
dimension R7 bounds. -/
def cascadeTraceClass {L : ℕ} {k : Fin L → ℕ} (C : CascadeRouterCode X L k)
    (hk : ∀ ℓ, 0 < k ℓ) : ConceptClass X (∀ ℓ, Fin (k ℓ)) :=
  Set.range (cascadeTrace C hk)

/-! ### Step 1: Natarajan-shattering forces `2^{|S|}` route-trace patterns -/

/-- **A Natarajan-shattered sample forces `2^{|S|}` route-trace patterns.** If a finite sample `S` is
Natarajan-shattered by the route-trace class with witnesses `f₀ f₁` disagreeing everywhere on `S`, then
the `2^{|S|}` Boolean selections `b : ↥S → Bool` inject — via `b ↦ (x ↦ if b x then f₀ x else f₁ x)`,
injective because `f₀ x ≠ f₁ x` — into the route-trace restriction range on `S` (each selection is
realised by a parameter), so `2^{|S|} ≤ (Set.range (cascadeTraceRestr C hk S)).ncard`. -/
theorem two_pow_card_le_traceRestr_ncard_of_natShatters {L : ℕ} {k : Fin L → ℕ}
    (C : CascadeRouterCode X L k) (hk : ∀ ℓ, 0 < k ℓ) {S : Finset X}
    (f₀ f₁ : X → (∀ ℓ, Fin (k ℓ))) (hne : ∀ x ∈ S, f₀ x ≠ f₁ x)
    (hrel : ∀ (h : X → Bool), ∃ c ∈ cascadeTraceClass C hk, ∀ x ∈ S,
      c x = if h x then f₀ x else f₁ x) :
    2 ^ S.card ≤ (Set.range (cascadeTraceRestr C hk S)).ncard := by
  classical
  -- The selection map: a Boolean selection on `S` ↦ the witnessed trace pattern.
  set Ψ : (↥S → Bool) → (↥S → (∀ ℓ, Fin (k ℓ))) :=
    fun b x => if b x then f₀ (x : X) else f₁ (x : X) with hΨ
  have hΨinj : Function.Injective Ψ := by
    intro b b' h
    funext x
    have hx := congrFun h x
    simp only [hΨ] at hx
    by_cases hb : b x <;> by_cases hb' : b' x
    · simp [hb, hb']
    · simp only [hb, hb', if_true] at hx
      exact absurd hx (hne (x : X) x.2)
    · simp only [hb, hb', if_true] at hx
      exact absurd hx.symm (hne (x : X) x.2)
    · simp [hb, hb']
  -- Every selection's pattern lies in the trace-restriction range.
  have hsub : Set.range Ψ ⊆ Set.range (cascadeTraceRestr C hk S) := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨c, ⟨ρ, rfl⟩, hc⟩ :=
      hrel (fun x => if hx : x ∈ S then b ⟨x, hx⟩ else false)
    refine ⟨ρ, ?_⟩
    funext x
    have := hc (x : X) x.2
    simp only [cascadeTraceRestr, dif_pos x.2] at this ⊢
    rw [this, hΨ]
  -- Count: `2^{|S|} = card (↥S → Bool) = ncard (range Ψ) ≤ ncard (trace range)`.
  have hcard_dom : Nat.card (↥S → Bool) = 2 ^ S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  have hcard_range : (Set.range Ψ).ncard = 2 ^ S.card := by
    rw [Set.ncard_range_of_injective hΨinj, hcard_dom]
  rw [← hcard_range]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

/-! ### Step 2: the (layer × pair) product of Sauer–Shelah sums is one polynomial -/

/-- **A Sauer–Shelah binomial sum is a single monomial bound.** For `1 ≤ m`,
`∑_{r ≤ R} (m choose r) ≤ (R + 1) · m ^ R`: each `m choose r ≤ m ^ r ≤ m ^ R`, and there are `R + 1`
terms. (The single-factor bound underlying the polynomial collapse; cf. `vcDim_finite_imp_growth_poly`
in FLT.) -/
theorem sum_choose_le_mul_pow {R m : ℕ} (hm : 1 ≤ m) :
    ∑ r ∈ Finset.range (R + 1), m.choose r ≤ (R + 1) * m ^ R := by
  calc ∑ r ∈ Finset.range (R + 1), m.choose r
      ≤ ∑ _r ∈ Finset.range (R + 1), m ^ R := by
        refine Finset.sum_le_sum (fun r hr => ?_)
        exact le_trans (Nat.choose_le_pow m r)
          (Nat.pow_le_pow_right hm (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)))
    _ = (R + 1) * m ^ R := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **The depth-`L` route-trace growth bound collapses to a single polynomial.** Under the
per-(layer, pair) linearity hypothesis, the route-trace pattern count on any sample `S` with `1 ≤ |S|`
is at most `K · |S| ^ D`, where `D = ∑_ℓ ∑_p finrank ℝ (W ℓ p)` is the total comparison VC dimension and
`K = ∏_ℓ ∏_p (finrank ℝ (W ℓ p) + 1)`. This collapses the (layer × pair) product of Sauer–Shelah sums
of `cascadeTrace_growth_prod` into one monomial-times-constant bound, ready for the
exponential-beats-polynomial crux. -/
theorem cascadeTrace_growth_poly {L : ℕ} {k : Fin L → ℕ} (C : CascadeRouterCode X L k)
    (hk : ∀ ℓ, 0 < k ℓ)
    (W : (ℓ : Fin L) → Fin (k ℓ) × Fin (k ℓ) → Submodule ℝ (X → ℝ))
    (hWfin : ∀ ℓ p, FiniteDimensional ℝ (W ℓ p))
    (hlin : ∀ (ℓ : Fin L) (p : Fin (k ℓ) × Fin (k ℓ)) (ρ : (C.layer ℓ).Ρ),
      (fun x => (C.layer ℓ).score ρ x p.2 - (C.layer ℓ).score ρ x p.1) ∈ W ℓ p)
    {S : Finset X} (hS : 1 ≤ S.card) :
    (Set.range (cascadeTraceRestr C hk S)).ncard
      ≤ (∏ ℓ : Fin L, ∏ p : Fin (k ℓ) × Fin (k ℓ), (finrank ℝ (W ℓ p) + 1))
          * S.card ^ (∑ ℓ : Fin L, ∑ p : Fin (k ℓ) × Fin (k ℓ), finrank ℝ (W ℓ p)) := by
  refine le_trans (cascadeTrace_growth_prod C hk W hWfin hlin S) ?_
  -- Bound each Sauer–Shelah factor by `(finrank + 1) · |S| ^ finrank`, then regroup the product.
  calc ∏ ℓ : Fin L, ∏ p : Fin (k ℓ) × Fin (k ℓ),
          ∑ r ∈ Finset.range (finrank ℝ (W ℓ p) + 1), S.card.choose r
      ≤ ∏ ℓ : Fin L, ∏ p : Fin (k ℓ) × Fin (k ℓ),
          (finrank ℝ (W ℓ p) + 1) * S.card ^ finrank ℝ (W ℓ p) := by
        refine Finset.prod_le_prod' (fun ℓ _ => Finset.prod_le_prod' (fun p _ => ?_))
        exact sum_choose_le_mul_pow hS
    _ = (∏ ℓ : Fin L, ∏ p : Fin (k ℓ) × Fin (k ℓ), (finrank ℝ (W ℓ p) + 1))
          * S.card ^ (∑ ℓ : Fin L, ∑ p : Fin (k ℓ) × Fin (k ℓ), finrank ℝ (W ℓ p)) := by
        -- Inner: `∏_p (a_p · s^{R_p}) = (∏_p a_p) · s^{∑_p R_p}`.
        have hinner : ∀ ℓ : Fin L,
            ∏ p : Fin (k ℓ) × Fin (k ℓ),
              (finrank ℝ (W ℓ p) + 1) * S.card ^ finrank ℝ (W ℓ p)
              = (∏ p : Fin (k ℓ) × Fin (k ℓ), (finrank ℝ (W ℓ p) + 1))
                  * S.card ^ (∑ p : Fin (k ℓ) × Fin (k ℓ), finrank ℝ (W ℓ p)) := by
          intro ℓ
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        simp only [hinner]
        -- Outer: same distribution over `ℓ`.
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-! ### Step 3: Natarajan-shattering is closed under subsets of the sample -/

omit [MeasurableSpace X] in
/-- **The Natarajan-shatter condition is downward closed.** If a sample `S` is Natarajan-shattered by a
class `C` (with disagreeing witnesses `f₀ f₁` and every Boolean selection realised on `S`), then every
subset `T ⊆ S` is Natarajan-shattered by `C`, with the *same* witnesses: `f₀ x ≠ f₁ x` still holds on
`T ⊆ S`, and any realising concept on `S` realises the same selection on `T`. (The multiclass analogue
of `shatters_of_subset`.) -/
theorem natShatters_of_subset {Y : Type*} {C : ConceptClass X Y} {S T : Finset X} (hTS : T ⊆ S)
    (hS : ∃ (f₀ f₁ : X → Y), (∀ x ∈ S, f₀ x ≠ f₁ x) ∧
      ∀ (h : X → Bool), ∃ c ∈ C, ∀ x ∈ S, c x = if h x then f₀ x else f₁ x) :
    ∃ (f₀ f₁ : X → Y), (∀ x ∈ T, f₀ x ≠ f₁ x) ∧
      ∀ (h : X → Bool), ∃ c ∈ C, ∀ x ∈ T, c x = if h x then f₀ x else f₁ x := by
  obtain ⟨f₀, f₁, hne, hrel⟩ := hS
  refine ⟨f₀, f₁, fun x hx => hne x (hTS hx), fun h => ?_⟩
  obtain ⟨c, hcC, hc⟩ := hrel h
  exact ⟨c, hcC, fun x hx => hc x (hTS hx)⟩

/-! ### Step 4 (R7): the single multiclass capacity number is finite -/

/-- **R7 — THE MULTICLASS CAPACITY OF THE DEPTH-`L` ROUTE-TRACE CLASS IS FINITE.** Under
per-(layer, ordered-pair) linearity of the score differences (each `x ↦ s_{p.2}(x) − s_{p.1}(x)` in a
finite-dimensional `W ℓ p ≤ (X → ℝ)`), the **single Natarajan dimension** of the depth-`L` route-trace
concept class is finite:
`NatarajanDim X (∀ ℓ, Fin (k ℓ)) (cascadeTraceClass C hk) < ⊤`.

This packages the per-(layer, symbol) bit-class capacity (R2 form B) into the one multiclass invariant
the learning pathway consumes. General in the depth `L`, the per-layer arities `k ℓ`, the input space
`X`, and the per-(layer, pair) finite-dimensional score-difference spaces `W ℓ p`. Conditional on `hlin`
(false for arbitrary measurable scores).

Proof (M-Contrapositive over an M-Pipeline): if the dimension were `⊤`, the defining `iSup` would be
unbounded, yielding Natarajan-shattered sets of size exceeding every `m`; by downward closure
(`natShatters_of_subset`) Natarajan-shattered sets of *every* size `m` exist. Each forces
`2^m ≤ (route-trace pattern count) ≤ K · m^D` (`two_pow_card_le_traceRestr_ncard_of_natShatters` then
`cascadeTrace_growth_poly`), where `D = ∑_ℓ ∑_p finrank ℝ (W ℓ p)`. But `2^m` eventually exceeds any
polynomial (`no_eventually_two_pow_le_poly`, FLT), a contradiction. -/
theorem cascadeTraceClass_natarajanDim_lt_top {L : ℕ} {k : Fin L → ℕ} (C : CascadeRouterCode X L k)
    (hk : ∀ ℓ, 0 < k ℓ)
    (W : (ℓ : Fin L) → Fin (k ℓ) × Fin (k ℓ) → Submodule ℝ (X → ℝ))
    (hWfin : ∀ ℓ p, FiniteDimensional ℝ (W ℓ p))
    (hlin : ∀ (ℓ : Fin L) (p : Fin (k ℓ) × Fin (k ℓ)) (ρ : (C.layer ℓ).Ρ),
      (fun x => (C.layer ℓ).score ρ x p.2 - (C.layer ℓ).score ρ x p.1) ∈ W ℓ p) :
    NatarajanDim X (∀ ℓ, Fin (k ℓ)) (cascadeTraceClass C hk) < ⊤ := by
  classical
  -- The polynomial bound `2^m ≤ K · m^D` for every Natarajan-shattered set of size `m ≥ 1`.
  set K : ℕ := ∏ ℓ : Fin L, ∏ p : Fin (k ℓ) × Fin (k ℓ), (finrank ℝ (W ℓ p) + 1) with hK
  set D : ℕ := ∑ ℓ : Fin L, ∑ p : Fin (k ℓ) × Fin (k ℓ), finrank ℝ (W ℓ p) with hD
  -- For any Natarajan-shattered `T` of size `m ≥ 1`, `2^m ≤ K · m^D`.
  have hbound : ∀ {T : Finset X}, 1 ≤ T.card →
      (∃ (f₀ f₁ : X → (∀ ℓ, Fin (k ℓ))), (∀ x ∈ T, f₀ x ≠ f₁ x) ∧
        ∀ (h : X → Bool), ∃ c ∈ cascadeTraceClass C hk, ∀ x ∈ T,
          c x = if h x then f₀ x else f₁ x) →
      2 ^ T.card ≤ K * T.card ^ D := by
    intro T hT hShat
    obtain ⟨f₀, f₁, hne, hrel⟩ := hShat
    calc 2 ^ T.card
        ≤ (Set.range (cascadeTraceRestr C hk T)).ncard :=
          two_pow_card_le_traceRestr_ncard_of_natShatters C hk f₀ f₁ hne hrel
      _ ≤ K * T.card ^ D := cascadeTrace_growth_poly C hk W hWfin hlin hT
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  have hinf : NatarajanDim X (∀ ℓ, Fin (k ℓ)) (cascadeTraceClass C hk) = ⊤ := htop
  -- Unbounded `iSup` ⇒ Natarajan-shattered sets of size exceeding every `m`.
  have hunb := (iSup₂_eq_top
    (fun (S : Finset X) (_ : ∃ (f₀ f₁ : X → (∀ ℓ, Fin (k ℓ))), (∀ x ∈ S, f₀ x ≠ f₁ x) ∧
      ∀ (h : X → Bool), ∃ c ∈ cascadeTraceClass C hk, ∀ x ∈ S,
        c x = if h x then f₀ x else f₁ x) => (S.card : WithTop ℕ))).mp
    (by rw [NatarajanDim] at hinf; exact hinf)
  -- Hence (downward closure) Natarajan-shattered sets of *every* size `m`, giving `2^m ≤ K·m^D`.
  apply no_eventually_two_pow_le_poly (K : ℝ) D
  rw [eventually_atTop]
  refine ⟨1, fun m hm => ?_⟩
  obtain ⟨S, hShatS, hmS⟩ := hunb m (WithTop.coe_lt_top m)
  have hmS' : m < S.card := by exact_mod_cast hmS
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (le_of_lt hmS')
  have hTshat := natShatters_of_subset hTS hShatS
  have hTcard1 : 1 ≤ T.card := by rw [hTcard]; exact hm
  have hpoly := hbound hTcard1 hTshat
  rw [hTcard] at hpoly
  calc (2 : ℝ) ^ m = ((2 ^ m : ℕ) : ℝ) := by norm_cast
    _ ≤ ((K * m ^ D : ℕ) : ℝ) := by exact_mod_cast hpoly
    _ = (K : ℝ) * (m : ℝ) ^ D := by push_cast; ring

end TLT.TemperedDesignLaw
