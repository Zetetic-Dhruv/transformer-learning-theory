/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.Conjectures

/-!
# The margin-shell reduction — covering the boundary layer by pairwise score slabs

The boundary layer `betaShell A hk ρ g` (inputs whose top-minus-second score margin is below `g`) is the
region where the mixture leakage is not yet exponentially small and the executed route may differ from the
ideal. This file reduces *shell mass* to *per-slab volume* in three exact steps, each carrying no analytic
hypothesis:

* **Pointwise certificate** (`exists_close_pair_of_mem_betaShell`): every shell input has a *witnessed*
  ordered pair `(i, j)` — the score-maximizer `i` and a near-second index `j` — with `i` dominating `j` by
  strictly less than `g`. The membership test is the comparison of two scores, so shell membership is a
  decidable per-input certificate even though shell *mass* is analytic.
* **Set cover** (`betaShell_subset_biUnion_pairSlab`): the shell is contained in the finite union of the
  `k·(k−1)` off-diagonal directed slabs `pairSlab`.
* **Abstract mass bound** (`measure_betaShell_le_sum_pairSlab`): for *any* measure on the input space, the
  shell mass is at most the sum of the slab masses — finite subadditivity over the cover, requiring no
  measurability of the sets.

The remaining factor — bounding each slab mass `μ (pairSlab A ρ g i j)` by a density ceiling times the slab
width `g` divided by the score-difference gradient norm — is the analytic step under a density-bounded law,
developed downstream. These three reductions are the geometry-free core it composes with.
-/

open scoped BigOperators
open MeasureTheory

universe u

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The directed score slab** for an ordered pair `(i, j)`: the inputs where head `i`'s score dominates
head `j`'s (`score j ≤ score i`) by strictly less than `g`. This is the one-sided slab the shell actually
lands in — sharper than the absolute band `|score i − score j| < g` — because on the shell the maximizer
dominates its near-second by a small gap. The geometric primitive the boundary layer decomposes into. -/
def pairSlab {X : Type u} [MeasurableSpace X] {k : ℕ} (A : TemperedRouterFamily X k)
    (ρ : A.router.Ρ) (g : ℝ) (i j : Fin k) : Set X :=
  {x | A.router.score ρ x j ≤ A.router.score ρ x i ∧
    A.router.score ρ x i - A.router.score ρ x j < g}

/-- **The pointwise shell certificate.** With at least two heads (`2 ≤ k`, the regime where a second score
exists), every shell input `x` carries a witnessed ordered pair `(i, j)`: the score-maximizer `i`
dominates a near-second index `j` (`score j ≤ score i`) by strictly less than the shell radius `g`. The
per-input certificate behind the cover — a comparison of two scores, hence decidable. -/
theorem exists_close_pair_of_mem_betaShell {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : TemperedRouterFamily X k) (hk : 0 < k) (hk2 : 2 ≤ k) (ρ : A.router.Ρ) {g : ℝ} {x : X}
    (hx : x ∈ betaShell A hk ρ g) :
    ∃ i j : Fin k, i ≠ j ∧ A.router.score ρ x j ≤ A.router.score ρ x i ∧
      A.router.score ρ x i - A.router.score ρ x j < g := by
  simp only [betaShell, Set.mem_setOf_eq, gammaMargin] at hx
  have hne : (Finset.univ.filter
      (fun j => j ≠ leastArgmax (A.router.score ρ x) hk)).Nonempty := by
    obtain ⟨a, ha⟩ := Fintype.exists_ne_of_one_lt_card
      (by rw [Fintype.card_fin]; grind) (leastArgmax (A.router.score ρ x) hk)
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
  obtain ⟨sec, hsec_mem, hsec_eq⟩ := Finset.exists_mem_eq_sup' hne (A.router.score ρ x)
  have hsecScore : A.router.score ρ x sec
      = secondScore (A.router.score ρ x) (leastArgmax (A.router.score ρ x) hk) := by
    rw [secondScore, dif_pos hne]; exact hsec_eq.symm
  refine ⟨leastArgmax (A.router.score ρ x) hk, sec, ((Finset.mem_filter.mp hsec_mem).2).symm,
    leastArgmax_is_maximizer _ hk sec, ?_⟩
  rw [hsecScore]; exact hx

/-- **The shell cover.** The boundary layer is contained in the finite union of the off-diagonal directed
slabs: every shell input lands in the slab of its witnessed maximizer/near-second pair. -/
theorem betaShell_subset_biUnion_pairSlab {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : TemperedRouterFamily X k) (hk : 0 < k) (hk2 : 2 ≤ k) (ρ : A.router.Ρ) (g : ℝ) :
    betaShell A hk ρ g
      ⊆ ⋃ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), pairSlab A ρ g p.1 p.2 := by
  intro x hx
  obtain ⟨i, j, hij, hji, hlt⟩ := exists_close_pair_of_mem_betaShell A hk hk2 ρ hx
  exact Set.mem_iUnion₂.mpr
    ⟨(i, j), Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩, hji, hlt⟩

/-- **The abstract shell-mass bound.** For *any* measure on the input space, the boundary-layer mass is at
most the sum of the off-diagonal slab masses — finite subadditivity over the cover, with no measurability
hypothesis. This is the union bound that reduces shell mass to per-slab volume (the latter bounded, under a
density-bounded law, by the density ceiling times `g` over the score-difference gradient norm, downstream). -/
theorem measure_betaShell_le_sum_pairSlab {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : TemperedRouterFamily X k) (hk : 0 < k) (hk2 : 2 ≤ k) (ρ : A.router.Ρ) (g : ℝ)
    (μ : Measure X) :
    μ (betaShell A hk ρ g)
      ≤ ∑ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)), μ (pairSlab A ρ g p.1 p.2) := by
  refine (measure_mono (betaShell_subset_biUnion_pairSlab A hk hk2 ρ g)).trans ?_
  apply measure_biUnion_finset_le

end TLT.TemperedDesignLaw
