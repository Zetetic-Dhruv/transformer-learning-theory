/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.Conjectures
import TLT_Proofs.Strictness.AttentionNonBorelWitness
import TLT_Proofs.Boundary.TemperatureCliffDepth

/-!
# The measurability-cliff witness as a tempered router family (TD0.4 binding)

The non-Borel-witness machinery (`quadraticCostRouter`, `softBlendWeight`, `BaseUpMoECascadeCode`) and the
design law's `TemperedRouterFamily` are built on the *same* substrate — both route through
`FiniteScoreRouterCode ℝ 2`. This file records the cliff witness as a tempered router family, so the design
law's shells and the cliff's measurability dichotomy decorate one object (consumed by the square's corner
decorations).

`witnessTemperedFamily` is the binding object. Its soft and hard channels agree with the cliff's
`softBlendWeight` and quadratic-cost route **by construction**: the witness router's scores are the witness
scores `if i = 0 then 0 else (x − g ρ)²` verbatim, so the two frameworks share one routing map and cannot
drift. The depth-`L` tempered cascade is the shipped composition (`routeCascade`/`temperedHardeningRegionLayer`
on this family); this node owns only the witness binding, not a new cascade object.
-/

open TLT.Strictness TLT.Boundary

noncomputable section

namespace TLT.TemperedDesignLaw

variable {β : Type} [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β]
  [StandardBorelSpace β]

/-- **The cliff witness as a tempered router family.** The measurability-cliff's quadratic-cost router, read
as a `TemperedRouterFamily ℝ 2` at sharpness `τ`. The binding object placing the non-Borel witness inside the
design-law grammar: the design law's `softWeights`, `hardRoute`, `gammaMargin`, `marginInterior`, `betaShell`
become applicable to the cliff witness, so the soft/hard corners and the cliff's measurability status decorate
one object. The soft channel computes `softBlendWeight` and the hard channel the quadratic-cost route by
unfolding (the router's scores are the witness scores verbatim) — the routing unification leaves no drift. -/
def witnessTemperedFamily (τ : ℝ) (hτ : 0 ≤ τ) (g : β → ℝ) (hg : Continuous g) :
    TemperedRouterFamily ℝ 2 where
  router := quadraticCostRouter g hg
  β := τ
  hβ := hτ

end TLT.TemperedDesignLaw
