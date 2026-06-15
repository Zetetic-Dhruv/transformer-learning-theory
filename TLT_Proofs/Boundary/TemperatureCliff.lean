/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Boundary.MeasurabilityCliff

/-!
# The temperature cliff: softmax routing is Borel, the argmax limit is not

This file makes the softmax/argmax descriptive-complexity boundary concrete in the routing
*temperature*. Over the non-Borel witness `g : β → ℝ` (continuous, `Set.range g` analytic and
non-Borel), the same quadratic-cost score is read two ways:

* **Finite temperature (soft).** `softWitnessMargin τ g` is the real-valued, continuous relaxation
  of the base witness concept: a softmax-`τ` routing weight times a soft point indicator. It is
  continuous in its parameter `(θ₁, θ₂, ρ) : ℝ × ℝ × β` (the depth-`0` cascade parameter) for every
  finite `τ`. Continuity collapses the parameter supremum to a countable dense one, so the soft
  ghost-gap `p ↦ ⨆_θ (margin θ p₂ − margin θ p₁)` is **measurable** (the Borel ghost-gap condition),
  via `measurable_iSup_gap_of_continuous`.
* **The argmax limit (hard).** Sharpening to a hard decision is the argmax route, exactly the
  top-`1` of the softmax (`softmaxTop1_eq_argmax`/`softmaxTop1_eq_route`). The base-up MoE cascade
  over that argmax route has, at *every* depth `L`, a **non-Borel** bad event
  (`cascadeNonInvariance`), while staying null-measurable under every finite measure
  (`universalRepair`).

So temperature is the toggle: the routing map is continuous (Borel everywhere) for `τ < ∞`, and the
`τ = ∞` (argmax) reading is the discontinuous map whose bad event drops to analytic non-Borel. The
drop is a descriptive-complexity drop, not a learnability drop; the hard model stays learnable
(null-measurable). This realizes the softmax/argmax boundary on the library's own non-Borel witness.

## Main results

- `softWitnessMargin`: the temperature-`τ` real-valued soft relaxation of the base witness concept.
- `softWitnessMargin_isKW`: for every finite `τ`, the soft ghost-gap supremum is measurable.
- `temperatureCliff`: the toggle; soft Borel ghost-gap (`τ < ∞`) ∧ non-Borel argmax cascade bad
  event at every depth (`τ = ∞`) ∧ null-measurable survival ∧ argmax = softmax top-`1`.
-/

/-!
## References
- [Vaswani 2017] scaled dot-product/softmax attention; the temperature/sharpening reading of softmax.
- [1] existence of an analytic non-Borel set; [4] analytic ⇔ continuous image of a Polish space;
  [7] the Borel ghost-gap (V) condition; [57] FLT `cascadeBadEvent`, `singletonBadEvent`.
-/

open MeasureTheory Set TopologicalSpace

namespace TLT.Boundary

open TLT.Strictness

variable {β : Type} [TopologicalSpace β] [PolishSpace β]
  [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]

/-- The temperature-`τ` soft routing weight of the base ("route to `g ρ`") head: the continuous
relaxation `1 / (1 + exp(τ (x − g ρ)²))` of the argmax route-to-head-`0` decision of
`quadraticCostRouter`. As `τ → ∞` it sharpens to the indicator of `x = g ρ` (off the tie set). -/
noncomputable def softRouteWeight (τ : ℝ) (g : β → ℝ) (ρ : β) (x : ℝ) : ℝ :=
  (1 + Real.exp (τ * (x - g ρ) ^ 2))⁻¹

/-- The temperature-`τ` soft point weight: the continuous relaxation `exp(−τ (x − θ₁)²)` of the
point indicator `1{x = θ₁}` of `pointIndicatorExpert`. -/
noncomputable def softPointWeight (τ θ₁ x : ℝ) : ℝ :=
  Real.exp (-(τ * (x - θ₁) ^ 2))

/-- The temperature-`τ` **soft witness margin**: the real-valued continuous relaxation of the base
witness concept `patchEval pointIndicatorExpert zeroExpert (quadraticCostRoute g)`. The parameter
`(θ₁, θ₂, ρ) : ℝ × ℝ × β` is the depth-`0` cascade parameter (`CascadeParam (witnessCascade g hg) 0`);
`θ₂` is unused (mirroring `zeroExpert`). -/
noncomputable def softWitnessMargin (τ : ℝ) (g : β → ℝ) : (ℝ × ℝ × β) → ℝ → ℝ :=
  fun θ x => softRouteWeight τ g θ.2.2 x * softPointWeight τ θ.1 x

omit [PolishSpace β] [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] in
/-- The soft route weight is jointly continuous in `(ρ, x)`. -/
theorem softRouteWeight_continuous (τ : ℝ) (g : β → ℝ) (hg : Continuous g) :
    Continuous (fun p : β × ℝ => softRouteWeight τ g p.1 p.2) := by
  unfold softRouteWeight
  refine Continuous.inv₀ (continuous_const.add (Real.continuous_exp.comp
    (continuous_const.mul ((continuous_snd.sub (hg.comp continuous_fst)).pow 2)))) ?_
  intro p; positivity

/-- The soft point weight is jointly continuous in `(θ₁, x)`. -/
theorem softPointWeight_continuous (τ : ℝ) :
    Continuous (fun p : ℝ × ℝ => softPointWeight τ p.1 p.2) := by
  unfold softPointWeight
  exact Real.continuous_exp.comp
    (continuous_const.mul ((continuous_snd.sub continuous_fst).pow 2)).neg

omit [PolishSpace β] [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] in
/-- For each input `x`, the soft witness margin is continuous in the parameter `θ`. -/
theorem softWitnessMargin_continuous_param (τ : ℝ) (g : β → ℝ) (hg : Continuous g) (x : ℝ) :
    Continuous (fun θ : ℝ × ℝ × β => softWitnessMargin τ g θ x) := by
  unfold softWitnessMargin
  refine Continuous.mul ?_ ?_
  · exact (softRouteWeight_continuous τ g hg).comp
      ((continuous_snd.comp continuous_snd).prodMk continuous_const)
  · exact (softPointWeight_continuous τ).comp (continuous_fst.prodMk continuous_const)

omit [PolishSpace β] [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] in
/-- For each parameter `θ`, the soft witness margin is continuous (hence measurable) in `x`. -/
theorem softWitnessMargin_continuous_input (τ : ℝ) (g : β → ℝ) (hg : Continuous g)
    (θ : ℝ × ℝ × β) :
    Continuous (fun x => softWitnessMargin τ g θ x) := by
  unfold softWitnessMargin
  refine Continuous.mul ?_ ?_
  · exact (softRouteWeight_continuous τ g hg).comp (continuous_const.prodMk continuous_id)
  · exact (softPointWeight_continuous τ).comp (continuous_const.prodMk continuous_id)

omit [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] in
/-- The soft witness margin is nonnegative. -/
theorem softWitnessMargin_nonneg (τ : ℝ) (g : β → ℝ) (θ : ℝ × ℝ × β) (x : ℝ) :
    0 ≤ softWitnessMargin τ g θ x := by
  unfold softWitnessMargin softRouteWeight softPointWeight; positivity

omit [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] in
/-- The soft witness margin is bounded by `1` at nonnegative temperature. -/
theorem softWitnessMargin_le_one {τ : ℝ} (hτ : 0 ≤ τ) (g : β → ℝ) (θ : ℝ × ℝ × β) (x : ℝ) :
    softWitnessMargin τ g θ x ≤ 1 := by
  unfold softWitnessMargin softRouteWeight softPointWeight
  refine mul_le_one₀ (inv_le_one_of_one_le₀ (le_add_of_nonneg_right (Real.exp_pos _).le))
    (Real.exp_pos _).le ?_
  rw [Real.exp_le_one_iff]
  have : 0 ≤ τ * (x - θ.1) ^ 2 := mul_nonneg hτ (sq_nonneg _)
  linarith

omit [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] in
/-- **The soft endpoint, concretely at temperature `τ`.** For every finite (nonnegative) temperature,
the soft witness ghost-gap supremum is measurable (the Borel ghost-gap condition), instantiated by the
continuous softmax-`τ` margin and discharged by the continuity-collapse engine. Note the soft side
needs only topology and separability of the weight space, not its Borel structure. -/
theorem softWitnessMargin_isKW {τ : ℝ} (hτ : 0 ≤ τ) (g : β → ℝ) (hg : Continuous g) [Nonempty β] :
    Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
      ⨆ θ : ℝ × ℝ × β, softWitnessMargin τ g θ (p.2 0) - softWitnessMargin τ g θ (p.1 0)) := by
  refine measurable_iSup_gap_of_continuous
    (fun (θ : ℝ × ℝ × β) (p : (Fin 1 → ℝ) × (Fin 1 → ℝ)) =>
      softWitnessMargin τ g θ (p.2 0) - softWitnessMargin τ g θ (p.1 0)) ?_ ?_ ?_
  · intro θ
    exact ((softWitnessMargin_continuous_input τ g hg θ).measurable.comp
      ((measurable_pi_apply 0).comp measurable_snd)).sub
      ((softWitnessMargin_continuous_input τ g hg θ).measurable.comp
      ((measurable_pi_apply 0).comp measurable_fst))
  · intro p
    exact (softWitnessMargin_continuous_param τ g hg (p.2 0)).sub
      (softWitnessMargin_continuous_param τ g hg (p.1 0))
  · intro p
    refine ⟨1, ?_⟩
    rintro y ⟨θ, rfl⟩
    have h1 := softWitnessMargin_le_one hτ g θ (p.2 0)
    have h2 := softWitnessMargin_nonneg τ g θ (p.1 0)
    linarith

/-- **The temperature cliff.** Over the non-Borel witness `g`, the routing temperature is the exact
toggle of descriptive complexity:

* **soft (`τ < ∞`):** the soft witness ghost-gap supremum is measurable, i.e. the Borel ghost-gap
  condition (`softWitnessMargin_isKW`);
* **hard (`τ = ∞`, argmax), at every depth `L`:** the base-up MoE cascade bad event is **not** Borel
  (`cascadeNonInvariance`), yet stays null-measurable under every finite measure (`universalRepair`),
  so learnability survives;
* **identification:** the hard argmax route *is* the top-`1` of the softmax routing
  (`softmaxTop1_eq_route`), the `τ = ∞` reading of the same router.

The two regimes share one witness and one score; only the temperature differs. This is a measurability
cliff, not a learnability cliff. -/
theorem temperatureCliff {τ : ℝ} (hτ : 0 ≤ τ) (g : β → ℝ) (hg : Continuous g) [Nonempty β]
    (h_non_borel : ¬ MeasurableSet (Set.range g)) (L : ℕ)
    (μ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ))) [IsFiniteMeasure μ] :
    Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
        ⨆ θ : ℝ × ℝ × β, softWitnessMargin τ g θ (p.2 0) - softWitnessMargin τ g θ (p.1 0)) ∧
      ¬ MeasurableSet (cascadeBadEvent (witnessCascade g hg) L) ∧
      NullMeasurableSet (cascadeBadEvent (witnessCascade g hg) L) μ ∧
      (fun ρ x => leastArgmax (softmaxWeight (quadraticCostRouter g hg) ρ x) (by norm_num))
        = (quadraticCostRouter g hg).route (by norm_num) := by
  refine ⟨softWitnessMargin_isKW hτ g hg, (cascadeNonInvariance (witnessCascade g hg) L h_non_borel).2,
    universalRepair (witnessCascade g hg) L, softmaxTop1_eq_route (quadraticCostRouter g hg) ?_⟩
  norm_num

end TLT.Boundary
