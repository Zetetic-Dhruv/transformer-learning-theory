/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.HardeningEnvelope
import TLT_Proofs.TemperedDesignLaw.Stability
import TLT_Proofs.Bridge.Spec.ScaledDotProductScoreRouter

/-!
# The literal binding: the tempered design law on TorchLean's attention

The design law is abstract over `TemperedRouterFamily`, which bundles a `FiniteScoreRouterCode` with a
sharpness `β`. TorchLean's scaled-dot-product attention score is already a `FiniteScoreRouterCode`
(`Bridge.attentionScoreRouter`), so it is a tempered router family, and every β-axis result instantiates
onto the literal attention with no extra hypotheses beyond what the abstract theorems require.

* `litAttnTempered`: TorchLean's scaled-dot-product attention as a tempered router family at sharpness `β`.
* `litAttn_leakage_upper`: the two-sided leakage law on the literal attention; the off-route softmax mass
  is `≤ (nK−1)·exp(−β·γ)`.
* `litAttn_symbol_invariant`: for `β > 0` the literal soft attention's `leastArgmax` is the hard attention
  route (the symbol channel does not see the temperature).
* `litAttn_route_stable`: the executed route equals the ideal route off the `u`-shell.

These are the abstract design-law theorems (`TD0`/`TD2`/`TD7`) applied to `litAttnTempered`. The hardening
envelope on the literal value vectors, where the soft mixture is identified with the actual
`Spec.scaledDotProductAttention` output, is `litAttn_hardening_literal` in `SoftOutputCorrespondence`
(it depends on the soft-output correspondence and lives downstream of this file).
-/

open scoped BigOperators

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The literal tempered router.** TorchLean's scaled-dot-product attention score as a tempered router
family at sharpness `β`: keys `Fin nK`, query `Fin d → ℝ`. -/
def litAttnTempered (d nK : ℕ) (β : ℝ) (hβ : 0 ≤ β) : TemperedRouterFamily (Fin d → ℝ) nK where
  router := Bridge.attentionScoreRouter d nK
  β := β
  hβ := hβ

/-- **Leakage law on the literal attention.** The off-route softmax mass of TorchLean's attention is at most
`(nK−1)·exp(−β·γ)`. This is `TD2_leakage_upper_proof` instantiated on `litAttnTempered`, confirming that
the abstract leakage law holds of the literal attention scores (`Bridge.attentionScoreRouter`). -/
theorem litAttn_leakage_upper (d nK : ℕ) {β : ℝ} (hβ : 0 ≤ β) (hk : 0 < nK)
    (ρ : (litAttnTempered d nK β hβ).router.Ρ) (x : Fin d → ℝ) :
    offRouteMass (litAttnTempered d nK β hβ) hk ρ x
      ≤ ((nK : ℝ) - 1) * Real.exp (-(β * gammaMargin (litAttnTempered d nK β hβ) hk ρ x)) :=
  TD2_leakage_upper_proof (litAttnTempered d nK β hβ) hk ρ x

/-- **Symbol invariance on the literal attention.** For `β > 0` the literal soft attention's `leastArgmax`
is exactly the hard attention route. This is `TD0_symbol_invariant_proof` instantiated on `litAttnTempered`,
confirming that the symbol channel of the abstract design law holds of the literal attention scores. -/
theorem litAttn_symbol_invariant (d nK : ℕ) {β : ℝ} (hβ : 0 ≤ β) (hk : 0 < nK) (hβpos : 0 < β)
    (ρ : (litAttnTempered d nK β hβ).router.Ρ) (x : Fin d → ℝ) :
    leastArgmax (softWeights (litAttnTempered d nK β hβ) ρ x) hk
      = hardRoute (litAttnTempered d nK β hβ) hk ρ x :=
  TD0_symbol_invariant_proof (litAttnTempered d nK β hβ) hk hβpos ρ x

/-- **Route stability on the literal attention.** The executed route (from rounded scores within budget `b`)
equals the hard route whenever `2·b` is below the margin. This is `TD7_route_stable_proof` instantiated on
`litAttnTempered`, confirming that route stability holds of the literal attention scores. -/
theorem litAttn_route_stable (d nK : ℕ) {β : ℝ} (hβ : 0 ≤ β) (hk : 0 < nK)
    (ρ : (litAttnTempered d nK β hβ).router.Ρ) (x : Fin d → ℝ) (sExec : Fin nK → ℝ) (b : ℝ)
    (hb : ∀ i, |sExec i - (litAttnTempered d nK β hβ).router.score ρ x i| ≤ b)
    (hm : 2 * b < gammaMargin (litAttnTempered d nK β hβ) hk ρ x) :
    leastArgmax sExec hk = hardRoute (litAttnTempered d nK β hβ) hk ρ x :=
  TD7_route_stable_proof (litAttnTempered d nK β hβ) hk ρ x sExec b hb hm

end TLT.TemperedDesignLaw
