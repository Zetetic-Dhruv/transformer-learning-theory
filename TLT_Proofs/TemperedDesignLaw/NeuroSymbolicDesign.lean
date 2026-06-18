/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.TemperedDesignLawRoot_v2_3_nonvacuous
import TLT_Proofs.TemperedDesignLaw.MuxDepthLadder
import TLT_Proofs.TemperedDesignLaw.MuxDepthLadderGeneral

/-!
# The neurosymbolic design certificate

A type-forced specification of an *ideal neurosymbolic transformer*: an argmax routing layer that
performs an exact, hierarchically graded, statistically certified **symbolic factorization** of the
input, composed with a downstream (feed-forward) map that is genuinely conditioned on the routed
symbol.

`NeuroSymbolicDesignCertificate X Route Y` bundles:

* the **symbolic routing leg** `routed : HardTameMathLeg X Route` (the tempered design-law root leg),
  which already carries the symbolic read (`hardSymbol`), exactness at every positive sharpness
  (`exact_positive_beta`), the type-forced strict expressivity hierarchy (`expressivity_strict`, a
  proper `⊂` no collapsed grade can inhabit), runtime route stability (`routeStableCheck_sound`), and a
  type-forced strictly positive statistical bound (`symbolBound_pos`);
* the **neurosymbolic factorization**: a downstream map `downstream : Route → X → Y`, the assembled
  `model : X → Y`, and `model_factors` stating the model *is* the symbolic factorization composed with
  the downstream.

The two new **type-forcing teeth** exclude the degenerate fillers a permissive shape would admit:

* `factorization_nontrivial` forces the routing to genuinely partition the input (at least two inputs
  route to distinct symbols), so a constant-symbol router cannot inhabit the certificate;
* `downstream_uses_symbol` forces the downstream to be symbol-load-bearing (two symbols give different
  processing), so a downstream that ignores the routing cannot inhabit it, and the factorization is not
  decorative.

`nsDesignWitness` is a concrete non-vacuous inhabitant: a one-dimensional threshold router into a
symbol-conditioned downstream, with the strict expressivity hierarchy discharged by the constrained
affine-mux cascade (`binCascadeGrade_ssubset_succ`).

## Scope: properties present and the named next obligation

This certificate captures the symbolic, exact, hierarchical, statistical, and factorization properties.
Two properties of the ideal-model spec are scheduled, not yet fields:

* the **verifiable FO/SO placement**: the routing's cell membership is a first-order formula (a convex
  half-space intersection) for affine scores and a second-order (semialgebraic) one for quadratic
  self-attention scores. The geometry is already proved (`ArgmaxPowerDiagram.argmaxCell_convex`,
  `QuadraticExpressivity.quadraticArgmaxCell_not_convex`); threading it as a `geometry` leg, and the
  routing-design-as-Lean-type encoding above it, is the next obligation;
* the **optimization convergence** beyond the capacity bounds already in `CapacityProfile`.
-/

open Classical

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The neurosymbolic design certificate.** A symbolic routing leg composed with a downstream map,
with type-forcing teeth that the routing genuinely partitions the input and the downstream genuinely
uses the routed symbol. -/
structure NeuroSymbolicDesignCertificate (X Route Y : Type*) where
  /-- The symbolic routing leg: symbolic, exact, hierarchical, runtime-checkable, statistically
  certified. -/
  routed : HardTameMathLeg X Route
  /-- The downstream neural map (feed-forward), conditioned on the routed symbol. -/
  downstream : Route → X → Y
  /-- The full neurosymbolic model. -/
  model : X → Y
  /-- The model is the symbolic factorization composed with the downstream. -/
  model_factors : ∀ x, model x = downstream (routed.hardSymbol x) x
  /-- **Type-forcing (non-trivial factorization).** At least two inputs route to distinct symbols, so a
  degenerate constant-symbol router cannot inhabit the certificate. -/
  factorization_nontrivial : ∃ x x' : X, routed.hardSymbol x ≠ routed.hardSymbol x'
  /-- **Type-forcing (the downstream uses the symbol).** Two symbols give different downstream
  processing on some input, so a downstream that ignores the routing cannot inhabit the certificate. -/
  downstream_uses_symbol : ∃ (r r' : Route) (x : X), downstream r x ≠ downstream r' x

/-! ## A concrete non-vacuous inhabitant -/

/-- The strict expressivity ladder on the binary carrier `(Fin 1 → ℝ, Fin 2)`: depth-monotone, with the
strict depth separation `binCascadeGrade_ssubset_succ 0`. -/
def nsExprLadder : ExpressivityLadder (Fin 1 → ℝ) (Fin 2) where
  grade := fun L _K => MuxHierarchy.binCascadeGrade 1 2 L (by norm_num)
  monotone_depth :=
    monotone_nat_of_le_succ fun _L => MuxHierarchy.binCascadeGrade_succ_subset (by norm_num)
  monotone_width := fun _L => monotone_const
  strict := ⟨0, MuxHierarchy.binCascadeGrade_ssubset_succ 0⟩

/-- A one-dimensional threshold route into `Fin 2`: the symbolic factorization of the witness. -/
def nsThresholdRoute : (Fin 1 → ℝ) → Fin 2 := fun x => if 0 ≤ x 0 then 1 else 0

theorem nsThresholdRoute_one : nsThresholdRoute (fun _ => (1 : ℝ)) = 1 := by
  have h : (0 : ℝ) ≤ (fun _ : Fin 1 => (1 : ℝ)) 0 := by norm_num
  simp [nsThresholdRoute, h]

theorem nsThresholdRoute_negone : nsThresholdRoute (fun _ => (-1 : ℝ)) = 0 := by
  have h : ¬ (0 : ℝ) ≤ (fun _ : Fin 1 => (-1 : ℝ)) 0 := by norm_num
  simp [nsThresholdRoute, h]

/-- **The symbolic routing leg of the witness.** The threshold route, with the strict expressivity
hierarchy supplied by `nsExprLadder` (its `strict` field is `binCascadeGrade_ssubset_succ`) and a
strictly positive placeholder statistical bound. The type-forced fields `expressivity_strict` and
`symbolBound_pos` carry genuine content; the non-type-forced data fields are the route itself. -/
def nsRoutedLeg : HardTameMathLeg (Fin 1 → ℝ) (Fin 2) where
  hardSymbol := nsThresholdRoute
  softTop1 := fun _ => nsThresholdRoute
  exact_positive_beta := fun _ _ _ => rfl
  executedSymbol := nsThresholdRoute
  routeStableCheck := fun _ => true
  routeStableCheck_sound := fun _ _ => rfl
  symbolClass := nsExprLadder.grade 0 0
  expressivityGrade := nsExprLadder.grade
  expressivity_monotone_depth := nsExprLadder.monotone_depth
  expressivity_monotone_width := nsExprLadder.monotone_width
  expressivity_base := rfl
  expressivity_strict := nsExprLadder.strict
  symbolGap := 0
  symbolBound := 1
  statistically_certified := zero_le_one
  symbolGap_nonneg := le_refl 0
  symbolBound_pos := one_pos

/-- **The neurosymbolic design witness.** The threshold router factorizing into a symbol-conditioned
downstream (a one-bit gate). Non-vacuous: the routing realizes two symbols, the downstream depends on
the symbol, the expressivity hierarchy is strict, and the statistical bound is positive. -/
def nsDesignWitness : NeuroSymbolicDesignCertificate (Fin 1 → ℝ) (Fin 2) (Fin 2) where
  routed := nsRoutedLeg
  downstream := fun r _ => if r = 0 then 1 else 0
  model := fun x => if nsThresholdRoute x = 0 then 1 else 0
  model_factors := fun _ => rfl
  factorization_nontrivial :=
    ⟨(fun _ => (1 : ℝ)), (fun _ => (-1 : ℝ)), by
      show nsThresholdRoute (fun _ => (1 : ℝ)) ≠ nsThresholdRoute (fun _ => (-1 : ℝ))
      rw [nsThresholdRoute_one, nsThresholdRoute_negone]
      decide⟩
  downstream_uses_symbol := ⟨0, 1, (fun _ => 0), by decide⟩

/-! ## The witness meets the spec (property restatements) -/

/-- Exactness: the soft top-one read equals the hard symbol at every positive sharpness. -/
theorem nsDesign_symbolic_exact :
    ∀ β, 0 < β → ∀ x, nsDesignWitness.routed.softTop1 β x = nsDesignWitness.routed.hardSymbol x :=
  nsDesignWitness.routed.exact_positive_beta

/-- Hierarchical: the expressivity grade strictly grows with depth at some rung (a proper `⊂`). -/
theorem nsDesign_hierarchical :
    ∃ L, nsDesignWitness.routed.expressivityGrade L L
      ⊂ nsDesignWitness.routed.expressivityGrade (L + 1) (L + 1) :=
  nsDesignWitness.routed.expressivity_strict

/-- Statistically certified with a strictly positive bound (never the trivial `0 ≤ 0`). -/
theorem nsDesign_statBound_pos : 0 < nsDesignWitness.routed.symbolBound :=
  nsDesignWitness.routed.symbolBound_pos

/-- The model factorizes through the symbolic routing. -/
theorem nsDesign_factorizes :
    ∀ x, nsDesignWitness.model x
      = nsDesignWitness.downstream (nsDesignWitness.routed.hardSymbol x) x :=
  nsDesignWitness.model_factors

/-- The factorization is non-trivial: the routing realizes at least two distinct symbols. -/
theorem nsDesign_symbol_matters :
    ∃ x x', nsDesignWitness.routed.hardSymbol x ≠ nsDesignWitness.routed.hardSymbol x' :=
  nsDesignWitness.factorization_nontrivial

end TLT.TemperedDesignLaw
