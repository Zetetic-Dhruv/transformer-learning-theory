/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Routing.MeasurableScoreRouting
import TLT_Proofs.Strictness.AttentionNonBorelWitness

/-!
# Base-up MoE cascades and the depth-L bad event (Cascade)

This file constructs a mixture-of-experts (MoE) cascade built by stacking
`FiniteScoreRouterCode` routing layers *on top of* the non-Borel witness router,
and the empirical-process bad event `cascadeBadEvent M L` it induces at routing
depth `L`.

## Base-up placement

The witness score map `g` (whose range is the analytic, possibly non-Borel set)
is injected at the **base** (depth `0`), and the `FiniteScoreRouterCode` layers
sit *above* it.  This is the key design decision:

* If `g` were placed at the *final* layer, the depth-`L` event would merely
  *contain* the single-layer witness event untouched, and the non-invariance
  theorem would collapse to a projection corollary.
* Placing `g` at the base forces the obstruction to propagate **up** through all
  `L` routing layers.  Concretely, `cascadeEval` routes each input `x` down a
  `width`-ary tree of depth `L` whose every internal node is a genuine
  `FiniteScoreRouterCode.route` decision and whose leaves are base witness
  experts.  The routing is *per input*, so the reduction to the planar
  witness (the `cascadeReductionInvariant` proved below) is a genuine
  `L`-fold composite rather than a projection onto an untouched sub-event.

## One map, one reduction object, two lemmas (descriptive set theory)

The eventual non-invariance theorem has an *analytic* half and a *non-Borel*
half.  An early conjecture held that these must travel by **different** maps: the
analytic half by a Suslin *image* (`MeasurableSet.analyticSet_image`) and the
non-Borel half by *preimage under a measurable surjection*
(`Measurable.measurableSet_preimage_iff_of_surjective`), because there is **no**
measurable-preimage-of-analytic lemma (Mathlib's `AnalyticSet.preimage` needs
*continuity*).  The reduction refutes that conjecture: **one** map carries both.

The reduction collapses `cascadeBadEvent M L` to the **depth-independent** set
`singletonBadEvent (Set.range g)` at *every* depth `L`
(`cascadeBadEvent_eq_singletonBadEvent`, itself non-Borelness-free), and that set
is `samplePair1ToPlane ⁻¹' planarWitnessEvent (Set.range g)`
(FLT `singleton_badEvent_eq_preimage_planar`).  The map `samplePair1ToPlane` is a
**continuous surjection**, and `cascadeReductionInvariant` packages it as exactly that;
**both** halves consume the *same* reduction object, differing only in
*which property of the map* they use:

* **Analytic half.** `Set.range g` is analytic from continuity
  (`analyticSet_range_of_polishSpace`), hence so is its `planarWitnessEvent`
  (FLT `planarWitnessEvent_analytic`); the preimage under the **continuous** `red_L`
  is then analytic (`AnalyticSet.preimage`).  It is depth-uniform because the reduced
  set is depth-*independent*, not because it "stays Borel": when `Set.range g`
  is the non-Borel analytic set, the reduced set is itself non-Borel.
* **Non-Borel half.** `planarWitnessEvent (Set.range g)` is non-Borel
  (FLT `planarWitnessEvent_not_measurable`); its non-measurability reflects back
  through the **surjection** `red_L`
  (`Measurable.measurableSet_preimage_iff_of_surjective`).

Exposing `Continuous` rather than the weaker `Measurable` in the reduction object is
what lets a *single* object serve both legs: the analytic leg cannot run off
`Measurable` alone.  The construction, the depth-uniform reduction
(`cascadeBadEvent_eq_singletonBadEvent`, `cascadeReductionInvariant`), and the
non-invariance result (`cascadeNonInvariance`) are all established here; the
universal-repair result is in the downstream file.

## Faithfulness anchor

At depth `0` the construction collapses definitionally to the single-layer
witness: `cascadeBadEvent M 0 = witnessBadEventSet M.g M.g_cont`
(`cascadeBadEvent_zero`).  This pins `cascadeBadEvent` as the depth-graded
generalisation of the single-layer non-Borel witness.
-/

/-!
## References
- [42] hierarchical MoE tree (argmax routing); [1][4] analytic preimage / Borel-image-without-
  injectivity; [7] Def. 3.2 bad event; [57] FLT `singletonBadEvent`, `planarWitnessEvent`.
-/

open Classical
open MeasureTheory Set
open TLT.Strictness

namespace TLT.Boundary

/-- A **base-up mixture-of-experts cascade** over the non-Borel witness.

The witness score map `g : β → ℝ` (whose range carries the analytic obstruction)
sits at the base; `layer n` is the `(n+1)`-th routing layer stacked above it,
each a `width`-head `FiniteScoreRouterCode` over `ℝ`.  The Polish/Borel/standard
structure on the base parameter space `β` is supplied as explicit instance
arguments (project policy: typeclass arguments on the def, not a bundled data
field). -/
structure BaseUpMoECascadeCode (β : Type) [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] (width : ℕ) where
  /-- Routing width is positive, so each layer's argmax route is defined. -/
  hwidth : 0 < width
  /-- The base witness score map; `Set.range g` is the analytic set. -/
  g : β → ℝ
  /-- Continuity of the base score (so `Set.range g` is analytic). -/
  g_cont : Continuous g
  /-- The routing layers stacked above the base (depth = number of layers used). -/
  layer : ℕ → FiniteScoreRouterCode ℝ width
  /-- Each routing layer is **nondegenerate**: its parameter space is inhabited.
  This is the exact twin of `hwidth`: `0 < width` excludes the degenerate
  zero-head router, `Nonempty (layer n).Ρ` excludes the degenerate
  parameter-free router.  It is load-bearing, not decorative: the realizability
  (`⊇`) direction of the depth-`L` reduction builds a uniform parameter by
  selecting one setting `(layerNonempty n).some` at every internal node, so an
  empty layer would make `CascadeParam M (n+1)` empty and collapse
  `cascadeClass M (n+1)` to `∅`. -/
  layerNonempty : ∀ n, Nonempty (layer n).Ρ

variable {β : Type} [TopologicalSpace β] [PolishSpace β]
  [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] {width : ℕ}

/-- The parameter space of the depth-`n` cascade.  At depth `0` it is the base
witness parameter `ℝ × ℝ × β` (the `patchEval` parameter of the witness class);
at depth `n+1` it bundles the new layer's parameter with one depth-`n`
sub-parameter per routing outcome, i.e. a `width`-ary tree of routing
parameters of height `n+1`. -/
def CascadeParam (M : BaseUpMoECascadeCode β width) : ℕ → Type
  | 0 => ℝ × ℝ × β
  | n + 1 => (M.layer n).Ρ × (Fin width → CascadeParam M n)

/-- The depth-`L` MoE forward pass on input `x`.

At depth `0` it evaluates the base witness concept
`patchEval pointIndicatorExpert zeroExpert (quadraticCostRoute g)`.
At depth `n+1` the top layer routes `x` to one of `width` sub-trees via
`FiniteScoreRouterCode.route`, and evaluation recurses into the chosen sub-tree
**on the same input** `x`.  The route depends on `x`, so the obstruction at the
base genuinely threads through every layer. -/
noncomputable def cascadeEval (M : BaseUpMoECascadeCode β width) :
    (n : ℕ) → CascadeParam M n → ℝ → Bool
  | 0 => fun θ x =>
      patchEval pointIndicatorExpert zeroExpert
        (quadraticCostRoute M.g M.g_cont) θ x
  | n + 1 => fun p x =>
      cascadeEval M n (p.2 ((M.layer n).route M.hwidth p.1 x)) x

/-- The concept realised by the depth-`L` cascade at parameter `Π`. -/
noncomputable def cascadeConcept (M : BaseUpMoECascadeCode β width) (L : ℕ)
    (params : CascadeParam M L) : Concept ℝ Bool :=
  fun x => cascadeEval M L params x

/-- The depth-`L` cascade concept class: all concepts realisable by some
depth-`L` parameter. -/
noncomputable def cascadeClass (M : BaseUpMoECascadeCode β width) (L : ℕ) :
    ConceptClass ℝ Bool :=
  Set.range (cascadeConcept M L)

/-- The **depth-`L` empirical-process bad event** of the cascade, at sample size
`1`, target `zeroConcept`, threshold `1/2`: the depth-graded
generalisation of `witnessBadEventSet`. -/
noncomputable def cascadeBadEvent (M : BaseUpMoECascadeCode β width) (L : ℕ) :
    Set GhostPairs1 :=
  {p | ∃ h ∈ cascadeClass M L,
    EmpiricalError ℝ Bool h (fun i => (p.2 i, zeroConcept (p.2 i)))
        (zeroOneLoss Bool) -
    EmpiricalError ℝ Bool h (fun i => (p.1 i, zeroConcept (p.1 i)))
        (zeroOneLoss Bool) ≥ (1 : ℝ) / 2}

/-- **Faithfulness anchor.**  At depth `0` the cascade bad event equals the single-layer
non-Borel witness bad event.  This holds definitionally: `cascadeClass M 0` is the range
of the base `patchEval` family, exactly the class underlying `witnessBadEventSet`. -/
theorem cascadeBadEvent_zero (M : BaseUpMoECascadeCode β width) :
    cascadeBadEvent M 0 = witnessBadEventSet M.g M.g_cont :=
  rfl

/-! ## The depth-`L` reduction to the planar witness

The reduction collapses `cascadeBadEvent M L` to FLT's `singletonBadEvent (range g)`
at *every* depth `L`, then transports it to `planarWitnessEvent (range g)` by the
established `singleton_badEvent_eq_preimage_planar`.  The collapse is **not** a class equality; per-input MoE routing genuinely enlarges
`cascadeClass` beyond `singletonClassOn (range g)`, but the `m = 1` bad event collapses
regardless, because
the gap predicate forces a positive witness `h (p.2 0) = true` whose firing pins
`p.2 0 ∈ range g`, and `h` being a function forces `p.1 0 ≠ p.2 0`.
-/

/-- The `m = 1`, target-`zeroConcept`, threshold-`1/2` gap predicate fires **iff** the
hypothesis separates the two ghost points: positive on `p.2 0`, negative on `p.1 0`.
This is the depth-independent kernel of the whole reduction; it isolates the
empirical-process arithmetic from any cascade structure. -/
private lemma gap_ge_half_iff (h : Concept ℝ Bool) (p : GhostPairs1) :
    EmpiricalError ℝ Bool h (fun i => (p.2 i, zeroConcept (p.2 i)))
        (zeroOneLoss Bool) -
    EmpiricalError ℝ Bool h (fun i => (p.1 i, zeroConcept (p.1 i)))
        (zeroOneLoss Bool) ≥ (1 : ℝ) / 2
    ↔ (h (p.2 0) = true ∧ h (p.1 0) = false) := by
  unfold EmpiricalError
  simp only [show (1 : ℕ) ≠ 0 from one_ne_zero, ↓reduceIte, Fin.sum_univ_one,
    Nat.cast_one, div_one]
  unfold zeroOneLoss zeroConcept
  cases h (p.2 0) <;> cases h (p.1 0) <;> norm_num

/-- **Obstruction propagates to the base.**  If the depth-`n` cascade fires
`true` on `x`, then `x` lies in the base witness range `Set.range M.g`, *at every
depth*.  The induction threads the firing down through all `n` routing layers: each
top-layer `FiniteScoreRouterCode.route` only selects a sub-tree, never changes the
input, so a leaf `true` is a base `patchEval` `true`, which by
`quadraticCostRouter_route_eq` pins `x = M.g ρ`. -/
private lemma cascadeEval_true_mem_range (M : BaseUpMoECascadeCode β width) :
    ∀ (n : ℕ) (params : CascadeParam M n) (x : ℝ),
      cascadeEval M n params x = true → x ∈ Set.range M.g := by
  intro n
  induction n with
  | zero =>
      intro params x hx
      obtain ⟨θ₁, θ₂, ρ⟩ := params
      by_cases hr : quadraticCostRoute M.g M.g_cont ρ x = true
      · exact ⟨ρ, ((quadraticCostRouter_route_eq M.g M.g_cont ρ x).mp hr).symm⟩
      · exfalso
        simp only [cascadeEval, patchEval, zeroExpert, zeroConcept, if_neg hr] at hx
        exact Bool.false_ne_true hx
  | succ n ih =>
      intro params x hx
      simp only [cascadeEval] at hx
      exact ih _ x hx

/-- **Realizability survives the lift (⊇ direction, uses `layerNonempty`).**  Every base
singleton concept `singletonConcept a` with `a ∈ Set.range M.g` is realised by the
depth-`n` cascade, *at every depth*.  The successor step builds a **uniform** parameter:
fix one nondegenerate layer setting `(M.layerNonempty n).some` at the new top node and
route every outcome into the *same* depth-`n` sub-parameter, so the cascade ignores the
top route and collapses to the depth-`n` realiser (definitional `congrFun`).  The
`layerNonempty` field is load-bearing here: without an inhabitant of
`(M.layer n).Ρ`, `CascadeParam M (n+1)` could be empty and this witness would not
exist. -/
private lemma singletonConcept_mem_cascadeClass (M : BaseUpMoECascadeCode β width) :
    ∀ (n : ℕ) (a : ℝ), a ∈ Set.range M.g → singletonConcept a ∈ cascadeClass M n := by
  intro n
  induction n with
  | zero =>
      intro a ha
      obtain ⟨ρ_a, hρ_a⟩ := ha
      refine ⟨(a, 0, ρ_a), ?_⟩
      funext x
      show patchEval pointIndicatorExpert zeroExpert
        (quadraticCostRoute M.g M.g_cont) (a, 0, ρ_a) x = singletonConcept a x
      unfold patchEval pointIndicatorExpert zeroExpert singletonConcept zeroConcept
      by_cases hx : x = a
      · rw [if_pos hx, if_pos ((quadraticCostRouter_route_eq M.g M.g_cont ρ_a x).mpr
          (hx.trans hρ_a.symm))]
      · rw [if_neg hx, if_neg (fun hroute =>
          hx (((quadraticCostRouter_route_eq M.g M.g_cont ρ_a x).mp hroute).trans hρ_a))]
  | succ n ih =>
      intro a ha
      obtain ⟨params_n, hparams_n⟩ := ih a ha
      refine ⟨((M.layerNonempty n).some, fun _ => params_n), ?_⟩
      funext x
      exact congrFun hparams_n x

/-- **The depth-`L` bad-event collapse.**  At sample size `1` the
cascade bad event coincides with FLT's singleton bad event over `Set.range M.g`, *at
every depth* `L`, even though the realizable *classes* diverge.  The gap predicate
(`gap_ge_half_iff`) forces any witness `h` to fire positively on `p.2 0`; firing pins
`p.2 0 ∈ Set.range M.g` (`cascadeEval_true_mem_range`, the ⊆ direction) and, conversely,
that membership lets the uniform singleton realise the gap
(`singletonConcept_mem_cascadeClass`, the ⊇ direction).  Non-Borelness of `Set.range M.g` is not invoked here; it enters only at the
non-invariance leaf downstream. -/
theorem cascadeBadEvent_eq_singletonBadEvent (M : BaseUpMoECascadeCode β width) (L : ℕ) :
    cascadeBadEvent M L = singletonBadEvent (Set.range M.g) := by
  ext p
  constructor
  · rintro ⟨h, hmem, hgap⟩
    rw [gap_ge_half_iff] at hgap
    obtain ⟨hpos, hneg⟩ := hgap
    obtain ⟨params, hparams⟩ := hmem
    refine ⟨singletonConcept (p.2 0), Or.inr ⟨p.2 0,
      cascadeEval_true_mem_range M L params (p.2 0) ((congrFun hparams (p.2 0)).trans hpos),
      rfl⟩, ?_⟩
    rw [gap_ge_half_iff]
    refine ⟨?_, ?_⟩
    · show (if p.2 0 = p.2 0 then true else false) = true
      rw [if_pos rfl]
    · show (if p.1 0 = p.2 0 then true else false) = false
      exact if_neg (fun heq => Bool.false_ne_true
        (hneg.symm.trans ((congrArg h heq).trans hpos)))
  · rintro ⟨h, hmem, hgap⟩
    rw [gap_ge_half_iff] at hgap
    obtain ⟨hpos, hneg⟩ := hgap
    refine ⟨singletonConcept (p.2 0),
      singletonConcept_mem_cascadeClass M L (p.2 0) ?_, ?_⟩
    · rcases hmem with rfl | ⟨a, ha_range, rfl⟩
      · exact (Bool.false_ne_true hpos).elim
      · by_cases hc : p.2 0 = a
        · rw [hc]; exact ha_range
        · simp only [singletonConcept, if_neg hc] at hpos
          exact absurd hpos Bool.false_ne_true
    · rw [gap_ge_half_iff]
      refine ⟨?_, ?_⟩
      · show (if p.2 0 = p.2 0 then true else false) = true
        rw [if_pos rfl]
      · show (if p.1 0 = p.2 0 then true else false) = false
        exact if_neg (fun heq => Bool.false_ne_true
          (hneg.symm.trans ((congrArg h heq).trans hpos)))

/-- **The depth-`L` cascade reduction invariant.**  There is a *continuous*
surjection `red_L : GhostPairs1 → ℝ × ℝ` reducing the depth-`L` cascade bad event to the
planar witness `planarWitnessEvent (Set.range M.g)`.  The reducing map is the
depth-independent ghost projection `samplePair1ToPlane`; depth enters only through the
bad-event collapse `cascadeBadEvent_eq_singletonBadEvent`, so the *same* `red_L` works at
every routing depth.  This is the load-bearing object carried by **both** legs of the
downstream non-invariance theorem (`cascadeNonInvariance`), each off a *different* property
of the one map:

* the **analytic** leg lifts `planarWitnessEvent_analytic` forward along the equality
  through the **continuity** of `red_L` (`AnalyticSet.preimage`; surjectivity unused); and
* the **non-Borel** leg reflects `planarWitnessEvent_not_measurable` back through the
  **surjection** `red_L` (`Measurable.measurableSet_preimage_iff_of_surjective`).

Neither map-property is decorative: continuity is exactly what the analytic leg consumes,
surjectivity exactly what the non-Borel leg consumes.  Exposing `Continuous` (not the
weaker `Measurable`) is what lets the *single* reduction object serve both legs; the
analytic leg cannot run off `Measurable` alone, as `AnalyticSet.preimage` needs
continuity. -/
theorem cascadeReductionInvariant (M : BaseUpMoECascadeCode β width) (L : ℕ) :
    ∃ red_L : GhostPairs1 → ℝ × ℝ,
      Continuous red_L ∧ Function.Surjective red_L ∧
      cascadeBadEvent M L = red_L ⁻¹' planarWitnessEvent (Set.range M.g) := by
  refine ⟨samplePair1ToPlane, ?_, ?_, ?_⟩
  · exact Continuous.prodMk ((continuous_apply 0).comp continuous_fst)
      ((continuous_apply 0).comp continuous_snd)
  · intro ⟨x, y⟩
    exact ⟨(fun _ => x, fun _ => y), by simp [samplePair1ToPlane]⟩
  · rw [cascadeBadEvent_eq_singletonBadEvent]
    exact singleton_badEvent_eq_preimage_planar (Set.range M.g)

/-- **Cascade non-invariance.**  If the base score's range is
non-Borel, the depth-`L` cascade empirical-process bad event is analytic but **not** Borel,
at *every* routing depth `L`.  Both halves are pulled back through the single continuous
surjection `red_L` of `cascadeReductionInvariant`, each off a different property of that one
map: the analytic half off **continuity** (`AnalyticSet.preimage` lifting
`planarWitnessEvent_analytic`), the non-Borel half off **surjectivity**
(`planarWitnessEvent_not_measurable` reflected by
`Measurable.measurableSet_preimage_iff_of_surjective`).  Depth-uniformity is automatic (the
reduction is depth-independent), yet by the base-up placement the obstruction is genuinely
threaded through all `L` routing layers; this is not a projection onto an untouched
sub-event. -/
theorem cascadeNonInvariance (M : BaseUpMoECascadeCode β width) (L : ℕ)
    (h_non_borel : ¬ MeasurableSet (Set.range M.g)) :
    AnalyticSet (cascadeBadEvent M L) ∧ ¬ MeasurableSet (cascadeBadEvent M L) := by
  obtain ⟨red_L, hcont, hsurj, heq⟩ := cascadeReductionInvariant M L
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact (planarWitnessEvent_analytic (Set.range M.g)
      (analyticSet_range_of_polishSpace M.g_cont)).preimage hcont
  · rw [heq, hcont.measurable.measurableSet_preimage_iff_of_surjective hsurj]
    exact planarWitnessEvent_not_measurable (Set.range M.g) h_non_borel

/-- A **genuine** base-up MoE cascade witness over a continuous parameterization `g` of an
analytic set.  The non-Borel-witness quadratic-cost router sits at the base, and *every*
routing layer is that **same** quadratic-cost router (a `FiniteScoreRouterCode ℝ 2`, so
`width = 2`), not a degenerate constant layer.  The obstruction therefore threads through every per-input routing decision at every
depth.  `layerNonempty` is discharged by `[Nonempty β]`, which a consumer supplies from
`Set.range g` being nonempty (a non-Borel range is nonempty).  This is the witness that
makes the depth-graded wild side of `TLT.Boundary.attention_router_measurability_dichotomy`
explicit. -/
noncomputable def witnessCascade {β : Type}
    [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β]
    [StandardBorelSpace β] [Nonempty β] (g : β → ℝ) (hg : Continuous g) :
    BaseUpMoECascadeCode β 2 where
  hwidth := two_pos
  g := g
  g_cont := hg
  layer := fun _ => quadraticCostRouter g hg
  layerNonempty := fun _ => inferInstanceAs (Nonempty β)

end TLT.Boundary
