/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MuxDepthSeparationDim

/-!
# The constrained-cascade expressivity ladder as the certificate's expressivity witness

The certificate's hard-tame leg requires an `ExpressivityLadder`: a depth/width-indexed realizable route
grade that is monotone along the depth and width slices and carries a strict depth separation
`grade L L ⊂ grade (L+1) (L+1)` for some `L`. A collapsed (constant) grade cannot inhabit the strict
field, so the certificate type forces genuine expressivity growth.

The constrained affine-mux cascade supplies the witness on the binary carrier `(Fin 1 → ℝ, Fin 2)`:
`binaryExpressivityLadder` uses `MuxHierarchy.binCascadeGrade`, with the depth-monotone embedding
`binCascadeGrade_succ_subset` and the strict separation `binCascadeGrade_ssubset_succ` (proper inclusion
at every depth rung, via the one-dimensional linear-region calculus). `temperedDesignLawCertificate_binary`
is the resulting certificate, fully closed except for the classical non-Borel base range.

`dimExpressivityLadder` and `temperedDesignLawCertificate_dim` extend this to the general carrier
`(Fin d → ℝ, Fin nK)` for `d ≥ 1` and `nK ≥ 2`, using the general-`(d,k)` separation
`binCascadeGrade_ssubset_succ_dim`, so the expressivity type-forcing is realized at every input dimension
and route count, not only the binary case.

This module sits above the mux hierarchy, which itself imports the certificate; placing the witness here
keeps the certificate foundation independent of the cascade construction it is parameterized by.
-/

open MeasureTheory Set

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The constrained-cascade expressivity ladder** on the binary carrier `(Fin 1 → ℝ, Fin 2)`. The grade
at depth `L` is `MuxHierarchy.binCascadeGrade 1 2 L` (routes realizable by a depth-`L` arity-2 affine-mux
cascade), independent of the width index. The depth ladder is monotone by the identity-layer embedding
`binCascadeGrade_succ_subset`; the strict separation `binCascadeGrade_ssubset_succ` makes the depth-`0`
grade a proper subset of the depth-`1` grade, so the ladder is genuinely non-degenerate. -/
def binaryExpressivityLadder : ExpressivityLadder (Fin 1 → ℝ) (Fin 2) where
  grade := fun L _K => MuxHierarchy.binCascadeGrade 1 2 L (by norm_num)
  monotone_depth :=
    monotone_nat_of_le_succ fun _L => MuxHierarchy.binCascadeGrade_succ_subset (by norm_num)
  monotone_width := fun _L => monotone_const
  strict := ⟨0, MuxHierarchy.binCascadeGrade_ssubset_succ 0⟩

/-- **A certificate at the binary carrier `(Fin 1 → ℝ, Fin 2)` with the strict expressivity separation
discharged.** Every carried hypothesis is discharged from a landed theorem except the classical non-Borel
base range: the gap bounds by `gapZero_satisfies_certs`, the statistical bound by `0 ≤ 1`, and the strict
depth separation by `binaryExpressivityLadder` (whose `strict` field is `binCascadeGrade_ssubset_succ`).
The certificate type's `expressivity_strict` field therefore carries genuine content here, not a trivial
filler. -/
def temperedDesignLawCertificate_binary
    (ρ : (Bridge.attentionScoreRouter 1 2).Ρ)
    {Bse : Type} [TopologicalSpace Bse] [PolishSpace Bse] [MeasurableSpace Bse] [BorelSpace Bse]
    [StandardBorelSpace Bse] {width : ℕ}
    (M : Boundary.BaseUpMoECascadeCode Bse width) (Ldepth : ℕ)
    (hwild_nonBorel : ¬ MeasurableSet (Set.range M.g)) :
    TemperedDesignLawCertificate
      (temperedRegionData (Classical.choose concrete_crossover_exists)
        (Classical.choose_spec concrete_crossover_exists).1)
      GhostPairs1 (0 : Measure GhostPairs1) (Fin 1 → ℝ) (Fin 2) :=
  temperedDesignLawCertificate_concrete 1 2 (by norm_num) ρ M Ldepth
    binaryExpressivityLadder hwild_nonBorel

/-- **The constrained-cascade expressivity ladder at the general carrier** `(Fin d → ℝ, Fin nK)`, for
input dimension `d ≥ 1` and route count `nK ≥ 2`. The grade at depth `L` is `binCascadeGrade d nK L`,
monotone by `binCascadeGrade_succ_subset_dim`; the strict separation is the general-`(d,k)` depth ladder
`binCascadeGrade_ssubset_succ_dim`, so `expressivity_strict` is discharged at the full attention carrier,
not only the binary one. -/
def dimExpressivityLadder (d nK : ℕ) (hd : 1 ≤ d) (hnK : 2 ≤ nK) :
    ExpressivityLadder (Fin d → ℝ) (Fin nK) where
  grade := fun L _K => MuxHierarchy.binCascadeGrade d nK L (by omega)
  monotone_depth :=
    monotone_nat_of_le_succ fun _L => MuxHierarchy.binCascadeGrade_succ_subset_dim (by omega)
  monotone_width := fun _L => monotone_const
  strict := ⟨0, MuxHierarchy.binCascadeGrade_ssubset_succ_dim hd hnK 0⟩

/-- **A certificate at the general carrier `(Fin d → ℝ, Fin nK)` (`d ≥ 1`, `nK ≥ 2`) with the strict
expressivity separation discharged.** The general-carrier analogue of `temperedDesignLawCertificate_binary`:
`expressivity_strict` is closed by `dimExpressivityLadder` (whose `strict` field is the general-`(d,k)`
`binCascadeGrade_ssubset_succ_dim`), so the only carried input is the classical non-Borel base range. This
realizes the certificate's expressivity type-forcing at every input dimension and route count. -/
def temperedDesignLawCertificate_dim
    (d nK : ℕ) (hd : 1 ≤ d) (hnK : 2 ≤ nK) (ρ : (Bridge.attentionScoreRouter d nK).Ρ)
    {Bse : Type} [TopologicalSpace Bse] [PolishSpace Bse] [MeasurableSpace Bse] [BorelSpace Bse]
    [StandardBorelSpace Bse] {width : ℕ}
    (M : Boundary.BaseUpMoECascadeCode Bse width) (Ldepth : ℕ)
    (hwild_nonBorel : ¬ MeasurableSet (Set.range M.g)) :
    TemperedDesignLawCertificate
      (temperedRegionData (Classical.choose concrete_crossover_exists)
        (Classical.choose_spec concrete_crossover_exists).1)
      GhostPairs1 (0 : Measure GhostPairs1) (Fin d → ℝ) (Fin nK) :=
  temperedDesignLawCertificate_concrete d nK (by omega) ρ M Ldepth
    (dimExpressivityLadder d nK hd hnK) hwild_nonBorel

end TLT.TemperedDesignLaw
