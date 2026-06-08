/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Boundary.TemperatureCliff

/-!
# The temperature cliff, depth-uniform on the tree parameter

The depth-`0` soft witness margin lifts to every routing depth `L` over the **tree** parameter
`CascadeParam (witnessCascade g hg) L`, the same object whose argmax cascade bad event is non-Borel.
Instead of routing each input to one subtree (argmax), the soft cascade margin **softmax-blends** the
subtree margins. Two facts carry the lift:

* **Separability of the tree, uniform in depth.** `CascadeParam (witnessCascade g hg) n` is a finite
  iterated product of the Polish base `β` and `ℝ`, hence second-countable — so it is a separable
  topological space at *every* depth. The recursive instances below supply
  `TopologicalSpace`/`SecondCountableTopology`/`Nonempty` for variable `n`.
* **Continuity survives the blend.** A finite convex combination of continuous functions is
  continuous, so `softCascadeMargin` is continuous in the tree parameter at every depth (proved by
  induction). Continuity then collapses the parameter supremum, and the engine
  `measurable_iSup_gap_of_continuous` delivers the Borel ghost-gap.

So `depthTemperatureCliff` is the temperature cliff on the *same depth-`L` tree object*: the soft
ghost-gap is Borel while the argmax cascade bad event is non-Borel, at every depth, with learnability
surviving (null-measurable).

## Main results

- `softCascadeMargin` — the temperature-`τ` soft margin over the depth-`L` cascade tree parameter.
- `softCascadeMargin_isKW` — its ghost-gap supremum is measurable at every depth `L`.
- `depthTemperatureCliff` — soft Borel ghost-gap ∧ non-Borel argmax cascade ∧ null-measurable, at
  every depth `L`, on one tree object.
-/

/-!
## References
- [Vaswani 2017] softmax attention and the temperature/sharpening reading; [42] hierarchical MoE tree.
- [1][4] analytic non-Borel set / continuous image of a Polish space; [57] FLT cascade bad event.
- Provenance: Innovation — the depth-uniform soft cascade margin over the MoE tree parameter, lifting
  the temperature cliff to every routing depth on the same object.
- TLT contribution (Dhruv Gupta), `depthTemperatureCliff`: the routing-temperature toggle between a
  Borel soft ghost-gap and the non-Borel argmax cascade holds at every depth `L`, over the tree
  parameter, by softmax-blending subtree margins. Method: recursive separability instances for the
  tree + continuity-of-the-blend induction feeding the continuity-collapse engine.
-/

open MeasureTheory Set TopologicalSpace

namespace TLT.Boundary

variable {β : Type} [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β]
  [StandardBorelSpace β]

/-! ### Separability instances for the witness cascade tree, uniform in depth -/

/-- The depth-`n` witness cascade parameter carries the product/Pi topology. -/
instance instTopCascadeWitness {g : β → ℝ} {hg : Continuous g} [Nonempty β] :
    ∀ n, TopologicalSpace (CascadeParam (witnessCascade g hg) n)
  | 0 => inferInstanceAs (TopologicalSpace (ℝ × ℝ × β))
  | n + 1 =>
      haveI : TopologicalSpace (CascadeParam (witnessCascade g hg) n) := instTopCascadeWitness n
      inferInstanceAs (TopologicalSpace (β × (Fin 2 → CascadeParam (witnessCascade g hg) n)))

/-- The depth-`n` witness cascade parameter is nonempty. -/
instance instNonemptyCascadeWitness {g : β → ℝ} {hg : Continuous g} [Nonempty β] :
    ∀ n, Nonempty (CascadeParam (witnessCascade g hg) n)
  | 0 => inferInstanceAs (Nonempty (ℝ × ℝ × β))
  | n + 1 =>
      haveI : Nonempty (CascadeParam (witnessCascade g hg) n) := instNonemptyCascadeWitness n
      inferInstanceAs (Nonempty (β × (Fin 2 → CascadeParam (witnessCascade g hg) n)))

/-- The depth-`n` witness cascade parameter is second-countable (hence separable), at every depth. -/
instance instSCTCascadeWitness {g : β → ℝ} {hg : Continuous g} [Nonempty β] :
    ∀ n, SecondCountableTopology (CascadeParam (witnessCascade g hg) n)
  | 0 => inferInstanceAs (SecondCountableTopology (ℝ × ℝ × β))
  | n + 1 =>
      haveI : SecondCountableTopology (CascadeParam (witnessCascade g hg) n) := instSCTCascadeWitness n
      inferInstanceAs (SecondCountableTopology (β × (Fin 2 → CascadeParam (witnessCascade g hg) n)))

/-! ### The temperature-`τ` softmax blend over the witness scores -/

/-- The witness router's two scores: head `0` the constant `0`, head `1` the quadratic cost. -/
noncomputable def witnessScore (g : β → ℝ) (ρ : β) (x : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then 0 else (x - g ρ) ^ 2

/-- The temperature-`τ` softmax blend weight of head `i` over the witness scores. -/
noncomputable def softBlendWeight (τ : ℝ) (g : β → ℝ) (ρ : β) (x : ℝ) (i : Fin 2) : ℝ :=
  Real.exp (τ * witnessScore g ρ x i) / ∑ j, Real.exp (τ * witnessScore g ρ x j)

omit [PolishSpace β] [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] in
/-- Each witness score is jointly continuous in `(ρ, x)`. -/
theorem witnessScore_continuous (g : β → ℝ) (hg : Continuous g) (i : Fin 2) :
    Continuous (fun p : β × ℝ => witnessScore g p.1 p.2 i) := by
  unfold witnessScore
  by_cases h : i = 0
  · simp only [h, ↓reduceIte]; exact continuous_const
  · simp only [h, ↓reduceIte]; exact (continuous_snd.sub (hg.comp continuous_fst)).pow 2

omit [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] in
/-- The blend denominator is strictly positive. -/
theorem softBlend_denom_pos (τ : ℝ) (g : β → ℝ) (ρ : β) (x : ℝ) :
    0 < ∑ j, Real.exp (τ * witnessScore g ρ x j) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨0, Finset.mem_univ _⟩

omit [PolishSpace β] [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] in
/-- The blend weight is jointly continuous in `(ρ, x)`. -/
theorem softBlendWeight_continuous (τ : ℝ) (g : β → ℝ) (hg : Continuous g) (i : Fin 2) :
    Continuous (fun p : β × ℝ => softBlendWeight τ g p.1 p.2 i) := by
  unfold softBlendWeight
  refine Continuous.div
    (Real.continuous_exp.comp (continuous_const.mul (witnessScore_continuous g hg i)))
    (continuous_finset_sum _ (fun j _ =>
      Real.continuous_exp.comp (continuous_const.mul (witnessScore_continuous g hg j)))) ?_
  exact fun p => ne_of_gt (softBlend_denom_pos τ g p.1 p.2)

omit [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] in
/-- The blend weight is nonnegative. -/
theorem softBlendWeight_nonneg (τ : ℝ) (g : β → ℝ) (ρ : β) (x : ℝ) (i : Fin 2) :
    0 ≤ softBlendWeight τ g ρ x i := by
  unfold softBlendWeight; positivity

omit [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] in
/-- The blend weights sum to one. -/
theorem softBlendWeight_sum (τ : ℝ) (g : β → ℝ) (ρ : β) (x : ℝ) :
    ∑ i, softBlendWeight τ g ρ x i = 1 := by
  unfold softBlendWeight
  rw [← Finset.sum_div, div_self (ne_of_gt (softBlend_denom_pos τ g ρ x))]

/-! ### The soft cascade margin over the tree parameter -/

/-- The temperature-`τ` **soft cascade margin** over the depth-`n` tree parameter: at depth `0` the
base soft witness margin; at depth `n+1` the softmax-`τ` blend of the two subtree margins (a convex
combination, not an argmax route). -/
noncomputable def softCascadeMargin (τ : ℝ) (g : β → ℝ) (hg : Continuous g) [Nonempty β] :
    ∀ n, CascadeParam (witnessCascade g hg) n → ℝ → ℝ
  | 0 => softWitnessMargin τ g
  | n + 1 => fun p x => ∑ i, softBlendWeight τ g p.1 x i * softCascadeMargin τ g hg n (p.2 i) x

/-- For each input `x`, the soft cascade margin is continuous in the tree parameter — at every depth.
The successor step is a finite sum of products of (the blend, continuous in `p.1`) and (the subtree
margin, continuous by induction in `p.2 i`). -/
theorem softCascadeMargin_continuous_param (τ : ℝ) (g : β → ℝ) (hg : Continuous g) [Nonempty β] :
    ∀ (n : ℕ) (x : ℝ),
      Continuous (fun p : CascadeParam (witnessCascade g hg) n => softCascadeMargin τ g hg n p x)
  | 0, x => softWitnessMargin_continuous_param τ g hg x
  | n + 1, x => by
      show Continuous (fun p : β × (Fin 2 → CascadeParam (witnessCascade g hg) n) =>
        ∑ i, softBlendWeight τ g p.1 x i * softCascadeMargin τ g hg n (p.2 i) x)
      refine continuous_finset_sum _ (fun i _ => Continuous.mul ?_ ?_)
      · exact (softBlendWeight_continuous τ g hg i).comp (continuous_fst.prodMk continuous_const)
      · exact (softCascadeMargin_continuous_param τ g hg n x).comp
          ((continuous_apply i).comp continuous_snd)

/-- For each tree parameter `p`, the soft cascade margin is continuous (hence measurable) in `x`. -/
theorem softCascadeMargin_continuous_input (τ : ℝ) (g : β → ℝ) (hg : Continuous g) [Nonempty β] :
    ∀ (n : ℕ) (p : CascadeParam (witnessCascade g hg) n),
      Continuous (fun x => softCascadeMargin τ g hg n p x)
  | 0, p => softWitnessMargin_continuous_input τ g hg p
  | n + 1, p => by
      show Continuous (fun x =>
        ∑ i, softBlendWeight τ g p.1 x i * softCascadeMargin τ g hg n (p.2 i) x)
      refine continuous_finset_sum _ (fun i _ => Continuous.mul ?_ ?_)
      · exact (softBlendWeight_continuous τ g hg i).comp (continuous_const.prodMk continuous_id)
      · exact softCascadeMargin_continuous_input τ g hg n (p.2 i)

/-- The soft cascade margin lands in `[0, 1]` at nonnegative temperature — at every depth (a convex
combination of `[0,1]` values with weights summing to one). -/
theorem softCascadeMargin_mem {τ : ℝ} (hτ : 0 ≤ τ) (g : β → ℝ) (hg : Continuous g) [Nonempty β] :
    ∀ (n : ℕ) (p : CascadeParam (witnessCascade g hg) n) (x : ℝ),
      0 ≤ softCascadeMargin τ g hg n p x ∧ softCascadeMargin τ g hg n p x ≤ 1
  | 0, p, x => ⟨softWitnessMargin_nonneg τ g p x, softWitnessMargin_le_one hτ g p x⟩
  | n + 1, p, x => by
      show 0 ≤ ∑ i, softBlendWeight τ g p.1 x i * softCascadeMargin τ g hg n (p.2 i) x ∧
        ∑ i, softBlendWeight τ g p.1 x i * softCascadeMargin τ g hg n (p.2 i) x ≤ 1
      refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (softBlendWeight_nonneg τ g p.1 x i)
        (softCascadeMargin_mem hτ g hg n (p.2 i) x).1), ?_⟩
      calc ∑ i, softBlendWeight τ g p.1 x i * softCascadeMargin τ g hg n (p.2 i) x
          ≤ ∑ i, softBlendWeight τ g p.1 x i * 1 :=
            Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
              (softCascadeMargin_mem hτ g hg n (p.2 i) x).2 (softBlendWeight_nonneg τ g p.1 x i))
        _ = 1 := by rw [Finset.sum_congr rfl (fun i _ => mul_one _)]; exact softBlendWeight_sum τ g p.1 x

/-- **The soft endpoint at every depth `L`.** The soft cascade ghost-gap supremum over the tree
parameter is measurable — the Borel ghost-gap condition, depth-uniform on the witness cascade tree. -/
theorem softCascadeMargin_isKW {τ : ℝ} (hτ : 0 ≤ τ) (g : β → ℝ) (hg : Continuous g) [Nonempty β]
    (L : ℕ) :
    Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
      ⨆ θ : CascadeParam (witnessCascade g hg) L,
        softCascadeMargin τ g hg L θ (p.2 0) - softCascadeMargin τ g hg L θ (p.1 0)) := by
  refine measurable_iSup_gap_of_continuous
    (fun (θ : CascadeParam (witnessCascade g hg) L) (p : (Fin 1 → ℝ) × (Fin 1 → ℝ)) =>
      softCascadeMargin τ g hg L θ (p.2 0) - softCascadeMargin τ g hg L θ (p.1 0)) ?_ ?_ ?_
  · intro θ
    exact ((softCascadeMargin_continuous_input τ g hg L θ).measurable.comp
        ((measurable_pi_apply 0).comp measurable_snd)).sub
      ((softCascadeMargin_continuous_input τ g hg L θ).measurable.comp
        ((measurable_pi_apply 0).comp measurable_fst))
  · intro p
    exact (softCascadeMargin_continuous_param τ g hg L (p.2 0)).sub
      (softCascadeMargin_continuous_param τ g hg L (p.1 0))
  · intro p
    refine ⟨1, ?_⟩
    rintro y ⟨θ, rfl⟩
    have h1 := (softCascadeMargin_mem hτ g hg L θ (p.2 0)).2
    have h2 := (softCascadeMargin_mem hτ g hg L θ (p.1 0)).1
    linarith

/-- **The temperature cliff, depth-uniform on the tree.** Over the non-Borel witness `g`, at every
routing depth `L`: the soft cascade ghost-gap supremum over the tree parameter is measurable (Borel
ghost-gap), while the argmax cascade bad event on the *same* tree is non-Borel (`cascadeNonInvariance`)
yet stays null-measurable under every finite measure (`universalRepair`). The routing temperature is
the toggle, uniformly in depth: continuous blend ⇒ Borel; argmax ⇒ analytic non-Borel. -/
theorem depthTemperatureCliff {τ : ℝ} (hτ : 0 ≤ τ) (g : β → ℝ) (hg : Continuous g) [Nonempty β]
    (h_non_borel : ¬ MeasurableSet (Set.range g)) (L : ℕ)
    (μ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ))) [IsFiniteMeasure μ] :
    Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
        ⨆ θ : CascadeParam (witnessCascade g hg) L,
          softCascadeMargin τ g hg L θ (p.2 0) - softCascadeMargin τ g hg L θ (p.1 0)) ∧
      ¬ MeasurableSet (cascadeBadEvent (witnessCascade g hg) L) ∧
      NullMeasurableSet (cascadeBadEvent (witnessCascade g hg) L) μ :=
  ⟨softCascadeMargin_isKW hτ g hg L, (cascadeNonInvariance (witnessCascade g hg) L h_non_borel).2,
    universalRepair (witnessCascade g hg) L⟩

end TLT.Boundary
