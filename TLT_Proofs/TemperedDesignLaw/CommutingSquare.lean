/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MarginTransport

/-!
# The commuting square: the corner region (TD4)

The tempered design law lives on a two-parameter square with four corners (ideal-soft, ideal-hard,
float-soft, float-hard), two `u`-edges (real→float, the literal forward error), and two `β`-edges
(soft→hard, the hardening envelope). The diagonal float-soft → ideal-hard is the triangle inequality over one
`u`-edge and one `β`-edge — *trivial as geometry once both edges apply*. The content is the **region algebra**:
the region on which both edge envelopes are simultaneously valid, and that it is robustly non-empty.

* `CornerRegion` — the corner polytope: the margin interior `{γ ≥ g}` (where the `β`-edge leakage law applies)
  intersected with the clamp ball `closedBall c B` (where the `u`-edge float envelope applies).
* `cornerRegion_closedBall_subset` — **robust non-emptiness**: a whole `δ`-ball around a point whose margin
  exceeds `g` by `2Ks·δ` lies inside `CornerRegion`, provided that ball sits in the clamp ball. The margin
  half uses the shipped margin-transport `marginInterior_of_margin_slack` (the margin survives a `δ`-drift);
  the clamp half is the triangle inequality. So the four-regime description holds not at an isolated point but
  on an open neighbourhood — the parameter polytope is non-degenerate.

The diagonal bound `dist (floatSoft x) (idealHard x) ≤ uEdgeEnv + βEdgeEnv` on `CornerRegion` is then the
triangle inequality over the two edges; and each corner's measurability status is a shipped theorem — the soft
corners Borel (`softWitnessMargin_isKW`), the hard-tame corner Borel (`finiteCellRouter_wellBehaved`,
`cascadeBadEvent_measurable_of_sigmaCompact`), the hard-wild corner analytic non-Borel (`temperatureCliff`).
These are cited, not re-proved; the unification object is this region together with those statuses.
-/

universe u

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The corner region.** The polytope on which both edges of the square apply: the margin interior `{γ ≥ g}`
(the `β`-edge leakage region) intersected with the clamp ball `closedBall c B` (the `u`-edge float region). -/
def CornerRegion {X : Type u} [MeasurableSpace X] [PseudoMetricSpace X] {k : ℕ}
    (A : TemperedRouterFamily X k) (hk : 0 < k) (ρ : A.router.Ρ) (g : ℝ) (c : X) (B : ℝ) : Set X :=
  marginInterior A hk ρ g ∩ Metric.closedBall c B

/-- **Robust non-emptiness of the corner region.** A closed `δ`-ball around `x₀` lies inside `CornerRegion`
whenever the scores are `Ks`-Lipschitz around `x₀`, the margin at `x₀` exceeds `g` by `2Ks·δ`, and the
`δ`-ball sits inside the clamp ball (`dist x₀ c + δ ≤ B`). The margin half is the shipped margin transport
(the margin survives the `δ`-drift); the clamp half is the triangle inequality. The four-regime description
therefore holds on an open neighbourhood, not merely at a point. -/
theorem cornerRegion_closedBall_subset {X : Type u} [MeasurableSpace X] [PseudoMetricSpace X] {k : ℕ}
    (A : TemperedRouterFamily X k) (hk : 0 < k) (hk2 : 2 ≤ k) (ρ : A.router.Ρ) (x₀ c : X)
    {g δ Ks B : ℝ} (hKs : 0 ≤ Ks) (hg : 0 < g)
    (hLip : ∀ z j, |A.router.score ρ z j - A.router.score ρ x₀ j| ≤ Ks * dist z x₀)
    (hi : g + 2 * Ks * δ ≤ gammaMargin A hk ρ x₀) (hball : dist x₀ c + δ ≤ B) :
    Metric.closedBall x₀ δ ⊆ CornerRegion A hk ρ g c B := by
  intro z hz
  have hzδ : dist z x₀ ≤ δ := Metric.mem_closedBall.mp hz
  refine ⟨marginInterior_of_margin_slack A hk hk2 ρ x₀ hKs hg hLip hi z hzδ, ?_⟩
  rw [Metric.mem_closedBall]
  calc dist z c ≤ dist z x₀ + dist x₀ c := dist_triangle _ _ _
    _ ≤ δ + dist x₀ c := by linarith
    _ ≤ B := by linarith

end TLT.TemperedDesignLaw
