/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.NeuroSymbolicDesign
import TLT_Proofs.TemperedDesignLaw.QuadraticDepth

/-!
# The second-order (quadratic / self-attention) neurosymbolic design certificate

A second-order instance of `NeuroSymbolicDesignCertificate`, mirroring the verified first-order
witness (`nsDesignWitness`) field-for-field, with the *first-order* affine-mux cascade swapped for
the *second-order* quadratic-gated cascade.

Where the first-order witness used `MuxHierarchy.binCascadeGrade` (affine per-layer scores) and the
first-order threshold router `nsThresholdRoute` (`if 0 ≤ x 0`), this witness uses
`quadDepthGrade` (quadratic per-layer gate, `QuadScore`) and a *quadratic score threshold* router
`soQuadRoute` (`if x 0 ^ 2 ≤ 1`). The expressivity ladder's strict separation is discharged by the
order-2 (two-crossing) quadratic-gate phenomenon `quadDepthGrade_zero_ssubset_one`, the second-order
analogue of `binCascadeGrade_ssubset_succ 0`.

* `soExprLadder` : the strict quadratic-depth ladder on the binary carrier `(Fin 1 → ℝ, Fin 2)`.
* `soQuadRoute` : the quadratic threshold router, with two realized symbols (`soQuadRoute_one`,
  `soQuadRoute_zero`).
* `soRoutedLeg` : the symbolic routing leg (`HardTameMathLeg`) carrying the quadratic ladder.
* `soDesignWitness` : the non-vacuous second-order inhabitant of `NeuroSymbolicDesignCertificate`.

The property restatements (`soDesign_*`) mirror the first-order ones (`nsDesign_*`).
-/

open Classical

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The strict second-order expressivity ladder** on the binary carrier `(Fin 1 → ℝ, Fin 2)`:
depth-monotone, with the strict depth separation `quadDepthGrade_zero_ssubset_one`. The quadratic-gate
analogue of `nsExprLadder`. -/
def soExprLadder : ExpressivityLadder (Fin 1 → ℝ) (Fin 2) where
  grade := fun L _K => quadDepthGrade 1 2 L (by norm_num)
  monotone_depth :=
    monotone_nat_of_le_succ fun _L => quadDepthGrade_succ_subset (by norm_num)
  monotone_width := fun _L => monotone_const
  strict := ⟨0, quadDepthGrade_zero_ssubset_one⟩

/-- A one-dimensional **quadratic** threshold route into `Fin 2`: the second-order symbolic
factorization of the witness. Routes to `1` inside the quadratic cell `x 0 ^ 2 ≤ 1` and to `0`
outside it. -/
def soQuadRoute : (Fin 1 → ℝ) → Fin 2 := fun x => if x 0 ^ 2 ≤ 1 then 1 else 0

theorem soQuadRoute_one : soQuadRoute (fun _ => (0 : ℝ)) = 1 := by
  have h : (fun _ : Fin 1 => (0 : ℝ)) 0 ^ 2 ≤ 1 := by norm_num
  simp only [soQuadRoute, if_pos h]

theorem soQuadRoute_zero : soQuadRoute (fun _ => (2 : ℝ)) = 0 := by
  have h : ¬ (fun _ : Fin 1 => (2 : ℝ)) 0 ^ 2 ≤ 1 := by norm_num
  simp [soQuadRoute, h]

/-- **The symbolic routing leg of the second-order witness.** The quadratic threshold route, with the
strict expressivity hierarchy supplied by `soExprLadder` (its `strict` field is
`quadDepthGrade_zero_ssubset_one`) and a strictly positive placeholder statistical bound. The
type-forced fields `expressivity_strict` and `symbolBound_pos` carry genuine content; the
non-type-forced data fields are the route itself. Mirrors `nsRoutedLeg`. -/
def soRoutedLeg : HardTameMathLeg (Fin 1 → ℝ) (Fin 2) where
  hardSymbol := soQuadRoute
  softTop1 := fun _ => soQuadRoute
  exact_positive_beta := fun _ _ _ => rfl
  executedSymbol := soQuadRoute
  routeStableCheck := fun _ => true
  routeStableCheck_sound := fun _ _ => rfl
  symbolClass := soExprLadder.grade 0 0
  expressivityGrade := soExprLadder.grade
  expressivity_monotone_depth := soExprLadder.monotone_depth
  expressivity_monotone_width := soExprLadder.monotone_width
  expressivity_base := rfl
  expressivity_strict := soExprLadder.strict
  symbolGap := 0
  symbolBound := 1
  statistically_certified := zero_le_one
  symbolGap_nonneg := le_refl 0
  symbolBound_pos := one_pos

/-- **The second-order neurosymbolic design witness.** The quadratic threshold router factorizing into
a symbol-conditioned downstream (a one-bit gate). Non-vacuous: the routing realizes two symbols, the
downstream depends on the symbol, the (quadratic) expressivity hierarchy is strict, and the statistical
bound is positive. Mirrors `nsDesignWitness`. -/
def soDesignWitness : NeuroSymbolicDesignCertificate (Fin 1 → ℝ) (Fin 2) (Fin 2) where
  routed := soRoutedLeg
  downstream := fun r _ => if r = 0 then 1 else 0
  model := fun x => if soQuadRoute x = 0 then 1 else 0
  model_factors := fun _ => rfl
  factorization_nontrivial :=
    ⟨(fun _ => (0 : ℝ)), (fun _ => (2 : ℝ)), by
      show soQuadRoute (fun _ => (0 : ℝ)) ≠ soQuadRoute (fun _ => (2 : ℝ))
      rw [soQuadRoute_one, soQuadRoute_zero]
      decide⟩
  downstream_uses_symbol := ⟨0, 1, (fun _ => 0), by decide⟩

/-! ## The witness meets the spec (property restatements) -/

/-- Exactness: the soft top-one read equals the hard symbol at every positive sharpness. -/
theorem soDesign_symbolic_exact :
    ∀ β, 0 < β → ∀ x, soDesignWitness.routed.softTop1 β x = soDesignWitness.routed.hardSymbol x :=
  soDesignWitness.routed.exact_positive_beta

/-- Hierarchical: the (quadratic) expressivity grade strictly grows with depth at some rung (a proper
`⊂`). -/
theorem soDesign_hierarchical :
    ∃ L, soDesignWitness.routed.expressivityGrade L L
      ⊂ soDesignWitness.routed.expressivityGrade (L + 1) (L + 1) :=
  soDesignWitness.routed.expressivity_strict

/-- Statistically certified with a strictly positive bound (never the trivial `0 ≤ 0`). -/
theorem soDesign_statBound_pos : 0 < soDesignWitness.routed.symbolBound :=
  soDesignWitness.routed.symbolBound_pos

/-- The model factorizes through the symbolic routing. -/
theorem soDesign_factorizes :
    ∀ x, soDesignWitness.model x
      = soDesignWitness.downstream (soDesignWitness.routed.hardSymbol x) x :=
  soDesignWitness.model_factors

/-- The factorization is non-trivial: the routing realizes at least two distinct symbols. -/
theorem soDesign_symbol_matters :
    ∃ x x', soDesignWitness.routed.hardSymbol x ≠ soDesignWitness.routed.hardSymbol x' :=
  soDesignWitness.factorization_nontrivial

end TLT.TemperedDesignLaw
