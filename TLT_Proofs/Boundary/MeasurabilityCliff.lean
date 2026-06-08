/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Bases
import TLT_Proofs.Boundary.BaseUpMoECascade
import TLT_Proofs.Boundary.CascadeNullMeasurable

/-!
# The Borel ghost-gap condition for continuous parameterized families

The one-sided ghost-gap supremum map `G(p) = ⨆_θ gap_θ(p)` is the object whose Borel
measurability is the strong "Borel ghost-gap" regularity invoked at the symmetrization step of
VC learning. For a parameterized family in which the gap is **continuous in the parameter** over
a **separable** parameter space, that supremum is Borel: continuity collapses the uncountable
supremum to a countable dense one, and a countable supremum of measurable functions is
measurable. No σ-compactness, Kσ-section, or measurable-selection analysis is used here —
continuity alone delivers the Borel level.

This is the **soft endpoint** of the softmax/argmax descriptive-complexity boundary, and it lands
directly on the library's most general transformer. The certified-generalization framework states
every transformer the library bounds as a weight-functional `F : (Fin d → ℝ) → V → ℝ` (the weight
space `Fin d → ℝ` is `ParamSpace d`) carrying, exactly, `hFcont : ∀ x, Continuous (fun θ => F θ x)`
— continuity in the weights — and `hFmeas : ∀ θ, Measurable (F θ)`. `transformerFunctional_isKW`
discharges the Borel ghost-gap condition from precisely those hypotheses, so it covers the **full
multi-head encoder stack** `transformerEncoderStackMH` (multi-head attention ∘ FFN ∘ layer-norm ∘
residual, depth-graded, tied and untied) — the most general object certified — and every
single-head, multi-head, and FFN instance below it.

The **hard** (argmax) routing has no such continuity: there the supremum map's superlevel set is
the analytic, non-Borel bad event of `TLT.Boundary.cascadeNonInvariance`. The two endpoints are
reached by different mechanisms — continuity-collapse here; the failure of σ-compact (Kσ)
parameter fibers there — and crossing from one to the other is forced by the argmax limit itself,
which discretizes the routing and removes the continuity this argument depends on.

## Main results

- `measurable_iSup_gap_of_continuous` — the supremum gap of a per-sample-measurable,
  parameter-continuous, uniformly-bounded family over a separable parameter space is measurable.
- `transformerFunctional_isKW` — the soft endpoint on the general transformer weight-functional:
  the supremum one-sided ghost gap is measurable (the Borel ghost-gap condition).
-/

open MeasureTheory Set TopologicalSpace

namespace TLT.Boundary

/-- For a continuous real function on a topological space, the supremum over the whole space
equals the supremum over any dense subset, given a uniform upper bound. The supremum over the
dense set bounds the closure of its image, and that closure contains the whole range by
continuity. -/
private lemma iSup_eq_iSup_subtype_of_dense
    {Θ : Type*} [TopologicalSpace Θ] [Nonempty Θ]
    {D : Set Θ} (hDd : Dense D) (hDne : D.Nonempty)
    (h : Θ → ℝ) (hc : Continuous h) (hb : BddAbove (Set.range h)) :
    ⨆ θ, h θ = ⨆ θ : D, h (θ : Θ) := by
  haveI : Nonempty D := hDne.to_subtype
  have hbD : BddAbove (Set.range fun θ : D => h (θ : Θ)) := by
    apply BddAbove.mono _ hb
    rintro _ ⟨θ, rfl⟩
    exact ⟨(θ : Θ), rfl⟩
  refine le_antisymm (ciSup_le fun θ₀ => ?_) (ciSup_le fun θ => le_ciSup hb (θ : Θ))
  set c : ℝ := ⨆ θ : D, h (θ : Θ) with hc_def
  have hsub : h '' D ⊆ Iic c := by
    rintro _ ⟨θ, hθ, rfl⟩
    exact le_ciSup hbD (⟨θ, hθ⟩ : D)
  have hθ₀ : h θ₀ ∈ closure (h '' D) :=
    image_closure_subset_closure_image hc ⟨θ₀, hDd θ₀, rfl⟩
  exact (closure_minimal hsub isClosed_Iic) hθ₀

/-- **Borel ghost-gap from parameter-continuity (the soft endpoint of the cliff).** If the
per-sample gap `θ ↦ gap θ p` is continuous on a separable parameter space, `p ↦ gap θ p` is
measurable for each parameter, and the family is uniformly bounded above, then the supremum-gap
`p ↦ ⨆_θ gap θ p` is measurable — the Borel ghost-gap condition. Continuity collapses the
supremum to a countable dense one (`iSup_eq_iSup_subtype_of_dense`); a countable supremum of
measurable functions is measurable. -/
theorem measurable_iSup_gap_of_continuous
    {Θ : Type*} [TopologicalSpace Θ] [SeparableSpace Θ] [Nonempty Θ]
    {P : Type*} [MeasurableSpace P]
    (gap : Θ → P → ℝ)
    (hmeas : ∀ θ, Measurable (gap θ))
    (hcont : ∀ p, Continuous fun θ => gap θ p)
    (hbdd : ∀ p, BddAbove (Set.range fun θ => gap θ p)) :
    Measurable (fun p => ⨆ θ, gap θ p) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense Θ
  haveI : Countable D := hDc.to_subtype
  have hDne : D.Nonempty := hDd.nonempty
  have hEq : (fun p => ⨆ θ, gap θ p) = fun p => ⨆ θ : D, gap (θ : Θ) p := by
    funext p
    exact iSup_eq_iSup_subtype_of_dense hDd hDne (fun θ => gap θ p) (hcont p) (hbdd p)
  rw [hEq]
  exact Measurable.iSup fun (θ : D) => hmeas (θ : Θ)

/-- **The soft endpoint, on the library's most general transformer: the Borel ghost-gap condition
(KW).** For a transformer weight-functional `F : (Fin d → ℝ) → V → ℝ` — the form in which the
certified-generalization framework states every transformer it bounds, with `Fin d → ℝ` the weight
space `ParamSpace d` — that is measurable in its input (`hFmeas`) and continuous in its weights
(`hFcont`), and a continuous loss `ℓ` with a uniform bound on the one-sided ghost gap (which holds
over a bounded weight ball, the domain on which attention is bounded — Kim et al. 2021), the
supremum of the ghost gap over the weight space is measurable.

Because `hFcont`/`hFmeas` are exactly the hypotheses `transformerEncoderStackMH_certified_generalization`
discharges, this covers the **full multi-head encoder stack** (attention ∘ FFN ∘ layer-norm ∘
residual, depth-graded, tied and untied) and every instance below it. The hard argmax cascade has
no such continuity and lands at the analytic non-Borel bad event of `cascadeNonInvariance`: the
cliff, on the objects the library actually certifies. -/
theorem transformerFunctional_isKW
    {d : ℕ} {V : Type*} [MeasurableSpace V]
    (F : (Fin d → ℝ) → V → ℝ)
    (hFmeas : ∀ θ, Measurable (F θ))
    (hFcont : ∀ x, Continuous fun θ : Fin d → ℝ => F θ x)
    {ℓ : ℝ → ℝ} (hℓ : Continuous ℓ)
    (hbdd : ∀ p : V × V, BddAbove (Set.range fun θ => ℓ (F θ p.2) - ℓ (F θ p.1))) :
    Measurable fun p : V × V => ⨆ θ : Fin d → ℝ, ℓ (F θ p.2) - ℓ (F θ p.1) := by
  apply measurable_iSup_gap_of_continuous
  · intro θ
    exact (hℓ.measurable.comp ((hFmeas θ).comp measurable_snd)).sub
      (hℓ.measurable.comp ((hFmeas θ).comp measurable_fst))
  · intro p
    exact (hℓ.comp (hFcont p.2)).sub (hℓ.comp (hFcont p.1))
  · exact hbdd

/-- **The measurability cliff (capstone).** At the softmax/argmax boundary of attention routing the
descriptive regularity of the one-sided ghost-gap drops, strictly, and the drop is genuine new
content — not a trivial conjunction of the two endpoints.

* **Soft side (the strong condition holds).** For the library's most general transformer
  weight-functional `F` (continuous in the weights, `transformerFunctional_isKW`), the ghost-gap
  supremum `p ↦ ⨆_θ ℓ(F θ p₂) − ℓ(F θ p₁)` *is measurable*: the Borel ghost-gap condition (KW).
* **Hard side (only the weak condition survives, strictly).** For the argmax MoE cascade over the
  non-Borel witness, the bad event is still null-measurable under every finite measure
  (`universalRepair`: learnability survives via WB_meas, arXiv:2604.25028 Prop. 2.3), yet **no
  measurable function has it as a `½`-superlevel set** — so no measurable ghost-gap supremum exists
  and KW fails.

**Why this is non-trivial.** The third conjunct is proven, not assumed: a measurable `G` with
`badEvent = G⁻¹(Ici ½)` would make the bad event Borel, contradicting `cascadeNonInvariance`. This
is the strict separation `KW ⊊ WB_meas` (the paper's Theorem 4.1) *located at the attention
regularization boundary*. The failure is **not** a route-measurability artifact — the routing is
measurable; the non-Borelness is the parameter *projection* (a Suslin operation), which does not
preserve Borelness and so survives the closure of Borel functions under pointwise limits. Nor is it
ill-posedness: analytic ⇒ universally measurable (Luzin), so the hard model stays learnable. The
cliff is purely a Borel→analytic descriptive-complexity drop forced by the smooth-to-discrete
argmax limit — the temperature instance of arXiv:2604.25028 Theorem 4.1, on the objects the library
actually certifies. -/
theorem measurabilityCliff
    {d : ℕ} {V : Type*} [MeasurableSpace V]
    (F : (Fin d → ℝ) → V → ℝ)
    (hFmeas : ∀ θ, Measurable (F θ)) (hFcont : ∀ x, Continuous fun θ : Fin d → ℝ => F θ x)
    {ℓ : ℝ → ℝ} (hℓ : Continuous ℓ)
    (hbdd : ∀ p : V × V, BddAbove (Set.range fun θ => ℓ (F θ p.2) - ℓ (F θ p.1)))
    {β : Type} [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β]
    [StandardBorelSpace β] [Nonempty β] (g : β → ℝ) (hg : Continuous g)
    (h_non_borel : ¬ MeasurableSet (Set.range g)) (L : ℕ)
    (μ : Measure GhostPairs1) [IsFiniteMeasure μ] :
    -- SOFT: the general transformer's ghost-gap supremum is measurable (KW)
    Measurable (fun p : V × V => ⨆ θ : Fin d → ℝ, ℓ (F θ p.2) - ℓ (F θ p.1)) ∧
    -- HARD: learnability survives (WB_meas, null-measurable under every finite measure) …
    NullMeasurableSet (cascadeBadEvent (witnessCascade g hg) L) μ ∧
    -- … yet no measurable ghost-gap supremum represents the bad event (KW fails) — strict separation
    ¬ ∃ G : GhostPairs1 → ℝ, Measurable G ∧
        cascadeBadEvent (witnessCascade g hg) L = G ⁻¹' Set.Ici (1 / 2) := by
  refine ⟨transformerFunctional_isKW F hFmeas hFcont hℓ hbdd,
          universalRepair (witnessCascade g hg) L, ?_⟩
  rintro ⟨G, hG, hEq⟩
  refine (cascadeNonInvariance (witnessCascade g hg) L h_non_borel).2 ?_
  rw [hEq]
  exact hG measurableSet_Ici

end TLT.Boundary
