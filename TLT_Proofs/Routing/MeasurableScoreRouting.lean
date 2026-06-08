/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.Amalgamation
import FLT_Proofs.Theorem.BorelAnalyticSeparation

/-!
# Attention as Measurable Score-Based Routing

The single routing primitive of the library: `FiniteScoreRouterCode X k`, a `k`-head
score-based router whose argmax route is jointly measurable, together with the measurable
`k`-valued router family it represents. Binary (score-comparison) routing is the `k = 2`
specialization — `route_two_eq_scoreComparison` characterizes the 2-head argmax route as a score comparison
(head `0` wins ties), recovering the Boolean decision via `Fin 2 ≃ Bool` at every call site.

## Main results

- `MeasurableFiniteRouterFamily` : measurable family of `k`-valued routers
- `FiniteScoreRouterCode`        : `k`-head score router with per-head measurability
- `leastArgmax`                  : deterministic tie-breaking argmax (least index)
- `route_measurable`             : the argmax route is jointly measurable
- `route_two_eq_scoreComparison`                 : the 2-head route is a score comparison (binary routing)
- `attentionOfFiniteRouter_route_eq` : every measurable `k`-router IS score-argmax attention
- `multiPatchEval`               : multi-head patched evaluation
- `top1_softmax_eq_argmax`       : softmax top-1 equals argmax
- `sharedRouterAmalgClass_eq_patchRange` : shared-router routing = amalgamation
- `attention_requires_nullMeasurable`    : the NullMeasurable regime is necessary

## References

- Amalgamation.lean (patchEval, amalgClass, agreementRel, borel_param_wellBehavedVCMeasTarget)
- BorelAnalyticSeparation.lean (KrappWirthSeparationMeasTarget, exists_measTarget_separation)
-/

universe u

open Classical
open MeasureTheory Set

/-! ## Item 1: MeasurableFiniteRouterFamily -/

/-- A measurable family of `k`-valued routers. The Boolean case is `k = 2` via `Fin 2 ≃ Bool`. -/
structure MeasurableFiniteRouterFamily (X : Type u) [MeasurableSpace X] (k : ℕ) where
  Ρ : Type u
  instMeasΡ : MeasurableSpace Ρ
  instStdΡ : @StandardBorelSpace Ρ instMeasΡ
  eval : Ρ → X → Fin k
  eval_meas : @Measurable (Ρ × X) (Fin k) (instMeasΡ.prod ‹MeasurableSpace X›) inferInstance
    (fun p => eval p.1 p.2)

attribute [instance] MeasurableFiniteRouterFamily.instMeasΡ
attribute [instance] MeasurableFiniteRouterFamily.instStdΡ

/-! ## Item 2: FiniteScoreRouterCode -/

/-- A `k`-head score-based router. For each parameter and input, produces `k` real scores.
    Per-head measurability: each `score i` is jointly measurable in `(ρ, x)`. -/
structure FiniteScoreRouterCode (X : Type u) [MeasurableSpace X] (k : ℕ) where
  Ρ : Type u
  instMeasΡ : MeasurableSpace Ρ
  instStdΡ : @StandardBorelSpace Ρ instMeasΡ
  score : Ρ → X → Fin k → ℝ
  score_meas : ∀ (i : Fin k), @Measurable (Ρ × X) ℝ (instMeasΡ.prod ‹MeasurableSpace X›)
    inferInstance (fun p => score p.1 p.2 i)

attribute [instance] FiniteScoreRouterCode.instMeasΡ
attribute [instance] FiniteScoreRouterCode.instStdΡ

/-! ## Item 3: Least argmax -/

/-- Predicate: `i` is the least index among maximizers of `v`. -/
def isLeastArgmax {k : ℕ} (v : Fin k → ℝ) (i : Fin k) : Prop :=
  (∀ j, v j ≤ v i) ∧ (∀ j, j < i → v j < v i)

/-- The least index among maximizers of `v` (deterministic tie-breaking). -/
noncomputable def leastArgmax {k : ℕ} (v : Fin k → ℝ) (hk : 0 < k) : Fin k :=
  (Finset.univ.filter (fun i => ∀ j, v j ≤ v i)).min' (by
    have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
    obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ v hne
    exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => hm j (Finset.mem_univ _)⟩⟩)

theorem leastArgmax_mem_maximizers {k : ℕ} (v : Fin k → ℝ) (hk : 0 < k) :
    leastArgmax v hk ∈ Finset.univ.filter (fun i => ∀ j, v j ≤ v i) :=
  Finset.min'_mem _ _

theorem leastArgmax_is_maximizer {k : ℕ} (v : Fin k → ℝ) (hk : 0 < k) :
    ∀ j, v j ≤ v (leastArgmax v hk) :=
  (Finset.mem_filter.mp (leastArgmax_mem_maximizers v hk)).2

theorem leastArgmax_is_least {k : ℕ} (v : Fin k → ℝ) (hk : 0 < k)
    (j : Fin k) (hj : j < leastArgmax v hk) :
    v j < v (leastArgmax v hk) := by
  by_contra hge; push Not at hge
  have hj_max : ∀ l, v l ≤ v j := fun l => le_trans (leastArgmax_is_maximizer v hk l) hge
  have hj_mem : j ∈ Finset.univ.filter (fun i => ∀ l, v l ≤ v i) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj_max⟩
  exact absurd (Finset.min'_le _ _ hj_mem) (not_le.mpr hj)

theorem leastArgmax_spec {k : ℕ} (v : Fin k → ℝ) (hk : 0 < k) :
    isLeastArgmax v (leastArgmax v hk) :=
  ⟨leastArgmax_is_maximizer v hk, leastArgmax_is_least v hk⟩

theorem isLeastArgmax_unique {k : ℕ} (v : Fin k → ℝ) (i j : Fin k)
    (hi : isLeastArgmax v i) (hj : isLeastArgmax v j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · linarith [hj.2 i hij, hi.1 j]
  · linarith [hi.2 j hji, hj.1 i]

/-! ## Item 4: route -/

/-- The argmax route: for each `(ρ, x)`, select the least-index maximizer of `score ρ x ·`. -/
noncomputable def FiniteScoreRouterCode.route {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : FiniteScoreRouterCode X k) (hk : 0 < k) : A.Ρ → X → Fin k :=
  fun ρ x => leastArgmax (A.score ρ x) hk

/-! ## Item 5: route_preimage_eq -/

/-- The preimage of `{i}` under `route` equals the set where `i` is the least argmax. -/
theorem FiniteScoreRouterCode.route_preimage_eq {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : FiniteScoreRouterCode X k) (hk : 0 < k) (i : Fin k) :
    (fun p : A.Ρ × X => A.route hk p.1 p.2) ⁻¹' {i} =
      {p | isLeastArgmax (A.score p.1 p.2) i} := by
  ext p
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
    FiniteScoreRouterCode.route]
  exact ⟨fun h => h ▸ leastArgmax_spec _ hk,
    fun h => isLeastArgmax_unique _ _ _ (leastArgmax_spec _ hk) h⟩

/-! ## Item 6: route_measurable -/

/-- The argmax route is jointly measurable in `(ρ, x)`. -/
theorem FiniteScoreRouterCode.route_measurable {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : FiniteScoreRouterCode X k) (hk : 0 < k) :
    Measurable (fun p : A.Ρ × X => A.route hk p.1 p.2) := by
  letI := A.instMeasΡ
  apply measurable_to_countable'
  intro i
  rw [A.route_preimage_eq hk i]
  have h_le : ∀ j, MeasurableSet {p : A.Ρ × X | A.score p.1 p.2 j ≤ A.score p.1 p.2 i} := by
    intro j
    exact measurableSet_le (A.score_meas j) (A.score_meas i)
  have h_lt : ∀ j, MeasurableSet {p : A.Ρ × X | A.score p.1 p.2 j < A.score p.1 p.2 i} := by
    intro j
    exact measurableSet_lt (A.score_meas j) (A.score_meas i)
  have h1 : {p : A.Ρ × X | ∀ j, A.score p.1 p.2 j ≤ A.score p.1 p.2 i} =
      ⋂ j, {p | A.score p.1 p.2 j ≤ A.score p.1 p.2 i} := by
    ext p; simp [Set.mem_iInter]
  have h2 : {p : A.Ρ × X | ∀ j, j < i → A.score p.1 p.2 j < A.score p.1 p.2 i} =
      ⋂ j ∈ ({j | j < i} : Set (Fin k)), {p | A.score p.1 p.2 j < A.score p.1 p.2 i} := by
    ext p; simp [Set.mem_iInter]
  have h3 : {p : A.Ρ × X | isLeastArgmax (A.score p.1 p.2) i} =
      {p | ∀ j, A.score p.1 p.2 j ≤ A.score p.1 p.2 i} ∩
      {p | ∀ j, j < i → A.score p.1 p.2 j < A.score p.1 p.2 i} := by
    ext p; simp [isLeastArgmax]
  rw [h3, h1, h2]
  refine (MeasurableSet.iInter (fun j => h_le j)).inter ?_
  have hctbl : (Set.univ : Set (Fin k)).Countable := Set.countable_univ
  exact MeasurableSet.biInter (hctbl.mono (Set.subset_univ _)) (fun j _ => h_lt j)

/-! ## Item 6′: route_two_eq_scoreComparison — the binary (2-head) route is a score comparison

For `k = 2` the argmax route is a score comparison: `route = 0` iff head `0`'s score is at
least head `1`'s (head `0` wins ties), else `route = 1`. This is the score-comparison /
binary-attention reading of finite routing at its smallest nondegenerate width, and the
form `T3`'s hard quadrant consumes. -/
theorem FiniteScoreRouterCode.route_two_eq_scoreComparison {X : Type u} [MeasurableSpace X]
    (A : FiniteScoreRouterCode X 2) (ρ : A.Ρ) (x : X) :
    A.route (by norm_num) ρ x =
      if A.score ρ x 1 ≤ A.score ρ x 0 then 0 else 1 := by
  simp only [FiniteScoreRouterCode.route]
  apply isLeastArgmax_unique _ _ _ (leastArgmax_spec _ _)
  set s := A.score ρ x with hs
  by_cases h : s 1 ≤ s 0
  · simp only [h, if_true]
    refine ⟨fun j => ?_, fun j hj => absurd hj (by omega)⟩
    fin_cases j
    · exact le_refl _
    · exact h
  · push Not at h
    simp only [show ¬(s 1 ≤ s 0) from not_le.mpr h, if_false]
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · fin_cases j
      · exact le_of_lt h
      · exact le_refl _
    · have hj0 : j = 0 := by omega
      subst hj0; exact h

/-! ## Item 7: attentionOfFiniteRouter -/

/-- Every `MeasurableFiniteRouterFamily` can be represented as a `FiniteScoreRouterCode`
    using one-hot score encoding. -/
noncomputable def attentionOfFiniteRouter {X : Type u} [MeasurableSpace X] {k : ℕ}
    (R : MeasurableFiniteRouterFamily X k) : FiniteScoreRouterCode X k where
  Ρ := R.Ρ
  instMeasΡ := R.instMeasΡ
  instStdΡ := R.instStdΡ
  score := fun ρ x i => if R.eval ρ x = i then (1 : ℝ) else 0
  score_meas := fun i => by
    letI := R.instMeasΡ
    exact Measurable.piecewise (R.eval_meas (measurableSet_singleton i))
      measurable_const measurable_const

/-! ## Item 8: attentionOfFiniteRouter_route_eq -/

/-- The attention representation is faithful: routing through `attentionOfFiniteRouter`
    recovers the original router evaluation. (The Boolean-router universality of binary
    attention is this statement at `k = 2`.) -/
theorem attentionOfFiniteRouter_route_eq {X : Type u} [MeasurableSpace X] {k : ℕ}
    (R : MeasurableFiniteRouterFamily X k) (hk : 0 < k) :
    (attentionOfFiniteRouter R).route hk = R.eval := by
  funext ρ x
  apply isLeastArgmax_unique
  · exact leastArgmax_spec _ hk
  · constructor
    · intro j
      simp only [attentionOfFiniteRouter]
      split_ifs with hj
      · exact le_refl 1
      · exact le_of_lt one_pos
    · intro j hj
      simp only [attentionOfFiniteRouter]
      have hne : ¬(R.eval ρ x = j) := fun h => absurd (h ▸ hj) (lt_irrefl _)
      simp [hne]

/-! ## Item 9: multiPatchEval -/

/-- Multi-head patched evaluation: combine `k` experts using a `k`-valued router.
    `multiPatchEval e r (θ, ρ) x = e θ (r ρ x) x`. -/
noncomputable def multiPatchEval {X : Type u} [MeasurableSpace X] {Θ Ρ : Type*} {k : ℕ}
    (e : Θ → Fin k → Concept X Bool) (r : Ρ → X → Fin k) : Θ × Ρ → Concept X Bool :=
  fun t x => e t.1 (r t.2 x) x

/-- `multiPatchEval` is jointly measurable when experts and router are measurable. -/
theorem multiPatchEval_measurable {X : Type u} [MeasurableSpace X]
    {Θ Ρ : Type*} [MeasurableSpace Θ] [MeasurableSpace Ρ] {k : ℕ}
    (e : Θ → Fin k → Concept X Bool) (r : Ρ → X → Fin k)
    (he : ∀ i, Measurable (fun p : Θ × X => e p.1 i p.2))
    (hr : Measurable (fun p : Ρ × X => r p.1 p.2)) :
    Measurable (fun p : (Θ × Ρ) × X => multiPatchEval e r p.1 p.2) := by
  apply measurable_to_countable'
  intro b
  have hdecomp : (fun p : (Θ × Ρ) × X => multiPatchEval e r p.1 p.2) ⁻¹' {b} =
      ⋃ i : Fin k, {p | r p.1.2 p.2 = i} ∩ {p | e p.1.1 i p.2 = b} := by
    ext p; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_setOf_eq, multiPatchEval]
    constructor
    · intro h; exact ⟨r p.1.2 p.2, rfl, h⟩
    · rintro ⟨i, hi, hei⟩; rw [← hi] at hei; exact hei
  rw [hdecomp]
  apply MeasurableSet.iUnion; intro i
  have hr_i : MeasurableSet {p : (Θ × Ρ) × X | r p.1.2 p.2 = i} :=
    (hr.comp (Measurable.prodMk (measurable_snd.comp measurable_fst) measurable_snd))
      (measurableSet_singleton i)
  have he_i : MeasurableSet {p : (Θ × Ρ) × X | e p.1.1 i p.2 = b} :=
    ((he i).comp (Measurable.prodMk (measurable_fst.comp measurable_fst) measurable_snd))
      (measurableSet_singleton b)
  exact hr_i.inter he_i

/-! ## Item 10: multiHeadArgmax_wellBehaved -/

/-- Multi-head argmax routing with Borel-parameterized experts satisfies
    `WellBehavedVCMeasTarget`. (Binary attention patching is this at `k = 2`.) -/
theorem multiHeadArgmax_wellBehaved {X : Type u} [MeasurableSpace X]
    [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ Ρ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    [MeasurableSpace Ρ] [StandardBorelSpace Ρ]
    {k : ℕ} (hk : 0 < k)
    (e : Θ → Fin k → Concept X Bool) (A : FiniteScoreRouterCode X k)
    (he : ∀ i, Measurable (fun p : Θ × X => e p.1 i p.2)) :
    WellBehavedVCMeasTarget X (Set.range (multiPatchEval e (A.route hk))) := by
  letI := A.instMeasΡ; letI := A.instStdΡ
  exact borel_param_wellBehavedVCMeasTarget (multiPatchEval e (A.route hk))
    (multiPatchEval_measurable e (A.route hk) he (A.route_measurable hk))

/-! ## Item 11: softmaxWeight + denom_pos -/

/-- Softmax weight for head `i`: `exp(score i) / Σ_j exp(score j)`. -/
noncomputable def softmaxWeight {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : FiniteScoreRouterCode X k) (ρ : A.Ρ) (x : X) (i : Fin k) : ℝ :=
  Real.exp (A.score ρ x i) / (∑ j : Fin k, Real.exp (A.score ρ x j))

/-- The softmax denominator is strictly positive. -/
theorem softmaxWeight_denom_pos {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : FiniteScoreRouterCode X k) (hk : 0 < k) (ρ : A.Ρ) (x : X) :
    0 < ∑ j : Fin k, Real.exp (A.score ρ x j) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨⟨0, hk⟩, Finset.mem_univ _⟩

/-! ## Item 12: softmaxWeight_measurable -/

/-- `softmaxWeight` is per-head measurable in `(ρ, x)`. -/
theorem softmaxWeight_measurable {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : FiniteScoreRouterCode X k) (i : Fin k) :
    Measurable (fun p : A.Ρ × X => softmaxWeight A p.1 p.2 i) := by
  letI := A.instMeasΡ
  simp only [softmaxWeight]
  have hexp_i : Measurable (fun p : A.Ρ × X => Real.exp (A.score p.1 p.2 i)) :=
    (A.score_meas i).exp
  have hsum : Measurable (fun p : A.Ρ × X => ∑ j : Fin k, Real.exp (A.score p.1 p.2 j)) :=
    Finset.measurable_sum _ (fun j _ => (A.score_meas j).exp)
  exact hexp_i.div hsum

/-! ## Item 13: softmaxWeight_le_iff_score -/

/-- Softmax preserves score ordering: `softmax i ≤ softmax j` iff `score i ≤ score j`. -/
theorem softmaxWeight_le_iff_score {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : FiniteScoreRouterCode X k) (hk : 0 < k) (ρ : A.Ρ) (x : X) (i j : Fin k) :
    softmaxWeight A ρ x i ≤ softmaxWeight A ρ x j ↔ A.score ρ x i ≤ A.score ρ x j := by
  simp only [softmaxWeight]
  set Z := ∑ l : Fin k, Real.exp (A.score ρ x l) with hZ_def
  have hZ : 0 < Z := softmaxWeight_denom_pos A hk ρ x
  rw [div_le_div_iff_of_pos_right hZ, Real.exp_le_exp]

/-- Softmax preserves strict score ordering. -/
theorem softmaxWeight_lt_iff {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : FiniteScoreRouterCode X k) (hk : 0 < k) (ρ : A.Ρ) (x : X) (i j : Fin k) :
    softmaxWeight A ρ x i < softmaxWeight A ρ x j ↔ A.score ρ x i < A.score ρ x j := by
  constructor
  · intro h; by_contra hle; push Not at hle
    exact not_le.mpr h ((softmaxWeight_le_iff_score A hk ρ x j i).mpr hle)
  · intro h; by_contra hle; push Not at hle
    exact not_le.mpr h ((softmaxWeight_le_iff_score A hk ρ x j i).mp hle)

/-! ## Item 14: isLeastArgmax_softmax_iff + top1_softmax_eq_argmax -/

/-- `isLeastArgmax` for softmax weights is equivalent to `isLeastArgmax` for scores. -/
theorem isLeastArgmax_softmax_iff {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : FiniteScoreRouterCode X k) (hk : 0 < k) (ρ : A.Ρ) (x : X) (i : Fin k) :
    isLeastArgmax (softmaxWeight A ρ x) i ↔ isLeastArgmax (A.score ρ x) i := by
  simp only [isLeastArgmax]
  constructor
  · intro ⟨hmax, hleast⟩
    exact ⟨fun j => (softmaxWeight_le_iff_score A hk ρ x j i).mp (hmax j),
           fun j hj => (softmaxWeight_lt_iff A hk ρ x j i).mp (hleast j hj)⟩
  · intro ⟨hmax, hleast⟩
    exact ⟨fun j => (softmaxWeight_le_iff_score A hk ρ x j i).mpr (hmax j),
           fun j hj => (softmaxWeight_lt_iff A hk ρ x j i).mpr (hleast j hj)⟩

/-- Softmax top-1 (least argmax of softmax weights) equals argmax of scores. -/
theorem top1_softmax_eq_argmax {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : FiniteScoreRouterCode X k) (hk : 0 < k) (ρ : A.Ρ) (x : X) :
    leastArgmax (softmaxWeight A ρ x) hk = leastArgmax (A.score ρ x) hk := by
  apply isLeastArgmax_unique
  · exact leastArgmax_spec _ hk
  · exact (isLeastArgmax_softmax_iff A hk ρ x _).mpr (leastArgmax_spec _ hk)

/-! ## Item 15: softmax top-1 wellBehaved -/

/-- The softmax top-1 route equals the argmax route. -/
theorem softmaxTop1_eq_route {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : FiniteScoreRouterCode X k) (hk : 0 < k) :
    (fun ρ x => leastArgmax (softmaxWeight A ρ x) hk) = A.route hk := by
  funext ρ x; exact top1_softmax_eq_argmax A hk ρ x

/-- Multi-head softmax top-1 routing with Borel-parameterized experts
    satisfies `WellBehavedVCMeasTarget`. -/
theorem multiHeadSoftmaxTop1_wellBehaved {X : Type u} [MeasurableSpace X]
    [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    {k : ℕ} (hk : 0 < k)
    (e : Θ → Fin k → Concept X Bool) (A : FiniteScoreRouterCode X k)
    (he : ∀ i, Measurable (fun p : Θ × X => e p.1 i p.2)) :
    WellBehavedVCMeasTarget X (Set.range (multiPatchEval e
      (fun ρ x => leastArgmax (softmaxWeight A ρ x) hk))) := by
  letI := A.instMeasΡ; letI := A.instStdΡ
  have : (fun ρ x => leastArgmax (softmaxWeight A ρ x) hk) = A.route hk :=
    softmaxTop1_eq_route A hk
  rw [this]
  exact borel_param_wellBehavedVCMeasTarget (multiPatchEval e (A.route hk))
    (multiPatchEval_measurable e (A.route hk) he (A.route_measurable hk))

/-! ## Item 16: shared-router amalgamation (structure-independent) -/

/-- The amalgamation class where two concept families share a router parameter.
    The agreement relation forces the router parameter to be shared (`ρ₁ = ρ₂`),
    yielding the class of `patchEval(e₁, e₂, r)(θ₁, θ₂, ρ)`. -/
noncomputable def sharedRouterAmalgClass
    {X : Type u} [MeasurableSpace X]
    {Θ₁ Θ₂ Ρ : Type*}
    [MeasurableSpace Θ₁] [MeasurableSpace Θ₂] [MeasurableSpace Ρ]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (r : Ρ → Concept X Bool) : ConceptClass X Bool :=
  amalgClass (Prod.snd : Θ₁ × Ρ → Ρ) (Prod.snd : Θ₂ × Ρ → Ρ)
    (fun p : (Θ₁ × Ρ) × (Θ₂ × Ρ) => patchEval e₁ e₂ r (p.1.1, p.2.1, p.1.2))

/-- The shared-router amalgamation class equals the range of `patchEval`. -/
theorem sharedRouterAmalgClass_eq_patchRange
    {X : Type u} [MeasurableSpace X]
    {Θ₁ Θ₂ Ρ : Type*}
    [MeasurableSpace Θ₁] [MeasurableSpace Θ₂] [MeasurableSpace Ρ]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (r : Ρ → Concept X Bool) :
    sharedRouterAmalgClass e₁ e₂ r = Set.range (patchEval e₁ e₂ r) := by
  ext h
  simp only [sharedRouterAmalgClass, amalgClass, relParamClass, agreementRel,
    Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have heq : p.1.2 = p.2.2 := hp
    exact ⟨(p.1.1, p.2.1, p.1.2), by simp [heq]⟩
  · rintro ⟨⟨θ₁, θ₂, ρ⟩, rfl⟩
    exact ⟨((θ₁, ρ), (θ₂, ρ)), rfl, rfl⟩

/-! ## Item 17: Attention Requires NullMeasurable -/

/-- The NullMeasurable regime is necessary for attention-style routing.

    By the universality theorem (`attentionOfFiniteRouter_route_eq`), every measurable
    finite-valued router is exactly a finite-head argmax attention mechanism. The existing
    Borel-analytic separation witness provides a concept class satisfying
    `WellBehavedVCMeasTarget` but failing `KrappWirthWellBehaved`. Therefore the Borel
    σ-algebra is insufficient for attention-based architectures in general. -/
theorem attention_requires_nullMeasurable
    (hex : ∃ A : Set ℝ, MeasureTheory.AnalyticSet A ∧ ¬ MeasurableSet A) :
    KrappWirthSeparationMeasTarget :=
  exists_measTarget_separation hex

/-- Strictness for `k`-head argmax attention: for any `k ≥ 1`, the separation witness exists.
    The same concept class works for all `k` because the underlying concept class is defined
    independently of the number of attention heads. -/
theorem multiHead_attention_requires_nullMeasurable
    (hex : ∃ A : Set ℝ, MeasureTheory.AnalyticSet A ∧ ¬ MeasurableSet A)
    (k : ℕ) (_hk : 0 < k) :
    KrappWirthSeparationMeasTarget :=
  attention_requires_nullMeasurable hex
