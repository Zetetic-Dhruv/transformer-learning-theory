/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Routing.SymbolOpcountCapacity
import FLT_Proofs.Complexity.IndependentVC.Growth
import FLT_Proofs.Complexity.IndependentVC.GrowthMul
import FLT_Proofs.Complexity.IndependentVC.GrowthSauerShelah
import FLT_Proofs.Complexity.Ordinal

/-!
# The arrangement-VC capacity bound for the symbol channel (the S3 bridge)

This file closes the **arrangement → VC → growth** composition for the symbol channel: it bounds the
number of routing-label patterns the symbol class realises on a finite sample by a *polynomial* in the
sample size, of degree the total comparison VC dimension. It is the capacity core dual to the opcount
factorisation, composing two already-landed endpoints with FLT's Sauer–Shelah growth machinery:

* `symbolRestr_ncard_le_prod` (`SymbolCapacity`) — the routing-label pattern count is at most the
  product over the `k²` ordered pairs of the per-pair score-comparison pattern counts;
* `comparisonClass_vcDim_le` (`SymbolOpcountCapacity`) — each per-pair comparison class is a halfspace
  class, with VC dimension at most `finrank ℝ W` under the linearity hypothesis `hlin` (scores affine
  in a finite feature map);

bridged by FLT's `restrictionSet_ncard_le_growthFunction` (per-pair restriction count ≤ growth
function) and `growthFunction_le_sum_choose` (Sauer–Shelah: finite VC ⇒ growth ≤ ∑ binomials,
Vapnik–Chervonenkis 1971 / Sauer 1972 / Shelah 1972).

## Results
* `shatters_card_le_of_vcDim_le` — from `VCDim X C ≤ d`, any `C`-shattered set has `≤ d` points.
* `singleCmpRestr_ncard_le_growthFunction` — the per-pair restriction count is at most the growth
  function of the comparison class (the comparison restriction is a restriction of `comparisonClass`).
* `comparisonClass_growthFunction_le` — Sauer–Shelah at the per-pair halfspace VC bound.
* `symbolClass_growth_prod` — **the arrangement-VC capacity bound (S3):** under per-pair linearity,
  the routing-label pattern count on any sample `S` is at most `∏_{(i,j)} ∑_{r ≤ finrank Wᵢⱼ} (|S| choose r)`
  — a polynomial in `|S|` of degree the total comparison VC dimension. Conditional on `hlin`
  (load-bearing: false for arbitrary measurable scores).
-/

noncomputable section

open Module

namespace TLT.TemperedDesignLaw

open TLT.Routing.Capacity

universe u

variable {X : Type u} [MeasurableSpace X] {k : ℕ}

/-- **A `VCDim` upper bound bounds every shattered set.** If `VCDim X C ≤ d` then any set shattered by
`C` has at most `d` points. (Extracts the finite VC value and applies `vcdim_card_le`.) -/
theorem shatters_card_le_of_vcDim_le {C : ConceptClass X Bool} {d : ℕ}
    (hC : VCDim X C ≤ (d : WithTop ℕ)) {s : Finset X} (hs : Shatters X C s) : s.card ≤ d := by
  have h1 : (s.card : WithTop ℕ) ≤ VCDim X C := by
    unfold VCDim
    exact le_iSup₂ (f := fun (S : Finset X) (_ : Shatters X C S) => (S.card : WithTop ℕ)) s hs
  exact_mod_cast le_trans h1 hC

/-- **Per-pair restriction count ≤ growth function.** The per-pair comparison restriction
`singleCmpRestr A S (i,j)` ranges over restrictions of the comparison class `comparisonClass A i j`, so
its pattern count is bounded by that class's growth function at `|S|`. -/
theorem singleCmpRestr_ncard_le_growthFunction (A : FiniteScoreRouterCode X k) (S : Finset X)
    (p : Fin k × Fin k) :
    (Set.range (singleCmpRestr A S p)).ncard
      ≤ GrowthFunction X (comparisonClass A p.1 p.2) S.card := by
  refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
    (restrictionSet_ncard_le_growthFunction (comparisonClass A p.1 p.2) rfl)
  rintro _ ⟨ρ, rfl⟩
  exact ⟨comparisonConcept A ρ p.1 p.2, ⟨ρ, rfl⟩, fun x => rfl⟩

/-- **Sauer–Shelah at the per-pair halfspace VC bound.** Under the linearity hypothesis, the comparison
class's growth function is bounded by the Sauer–Shelah binomial sum at `finrank ℝ W`. -/
theorem comparisonClass_growthFunction_le (A : FiniteScoreRouterCode X k) (i j : Fin k)
    (W : Submodule ℝ (X → ℝ)) [FiniteDimensional ℝ W]
    (hlin : ∀ ρ : A.Ρ, (fun x => A.score ρ x j - A.score ρ x i) ∈ W) (m : ℕ) :
    GrowthFunction X (comparisonClass A i j) m
      ≤ ∑ r ∈ Finset.range (finrank ℝ W + 1), m.choose r :=
  growthFunction_le_sum_choose (comparisonClass A i j) (finrank ℝ W)
    (fun s hs => shatters_card_le_of_vcDim_le (comparisonClass_vcDim_le A i j W hlin) hs) m

/-- **The arrangement-VC capacity bound for the symbol channel (S3).** Under per-pair linearity of the
score differences (each `x ↦ sⱼ(x) − sᵢ(x)` in a finite-dimensional `Wᵢⱼ`), the number of routing-label
patterns the symbol class realises on a finite sample `S` is at most the product over the `k²` ordered
pairs of the Sauer–Shelah binomial sums — a polynomial in `|S|` of degree the total comparison VC
dimension `∑ finrank ℝ Wᵢⱼ`. Conditional on `hlin`: false for arbitrary measurable scores. -/
theorem symbolClass_growth_prod (A : FiniteScoreRouterCode X k) (hk : 0 < k)
    (W : Fin k × Fin k → Submodule ℝ (X → ℝ)) (hWfin : ∀ p, FiniteDimensional ℝ (W p))
    (hlin : ∀ (p : Fin k × Fin k) (ρ : A.Ρ), (fun x => A.score ρ x p.2 - A.score ρ x p.1) ∈ W p)
    (S : Finset X) :
    (Set.range (routeRestr A hk S)).ncard
      ≤ ∏ p : Fin k × Fin k, ∑ r ∈ Finset.range (finrank ℝ (W p) + 1), S.card.choose r := by
  refine le_trans (symbolRestr_ncard_le_prod A hk S) ?_
  refine Finset.prod_le_prod' (fun p _ => ?_)
  haveI := hWfin p
  exact le_trans (singleCmpRestr_ncard_le_growthFunction A S p)
    (comparisonClass_growthFunction_le A p.1 p.2 (W p) (hlin p) S.card)

/-- **TD10 — the symbol-channel capacity argument, closed (uniform feature space).** When all `k²`
score differences lie in a *single* finite-dimensional `W`, the routing-label pattern count on any
sample `S` is bounded by one polynomial in `|S|` of degree `k² · finrank ℝ W`: the symbol class's
combinatorial capacity is `(∑_{r ≤ finrank W} |S| choose r)^{k²}`. This is the explicit
single-polynomial form of `symbolClass_growth_prod` (the per-pair product collapses since every factor
shares `W`), and it is the statement that discharges the TD10 capacity obligation. Conditional on the
per-pair linearity `hlin` (load-bearing: false for arbitrary measurable scores). -/
theorem symbolClass_growth_uniform (A : FiniteScoreRouterCode X k) (hk : 0 < k)
    (W : Submodule ℝ (X → ℝ)) [FiniteDimensional ℝ W]
    (hlin : ∀ (i j : Fin k) (ρ : A.Ρ), (fun x => A.score ρ x j - A.score ρ x i) ∈ W) (S : Finset X) :
    (Set.range (routeRestr A hk S)).ncard
      ≤ (∑ r ∈ Finset.range (finrank ℝ W + 1), S.card.choose r) ^ (k * k) := by
  have h := symbolClass_growth_prod A hk (fun _ => W) (fun _ => inferInstance)
    (fun p ρ => hlin p.1 p.2 ρ) S
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using h

end TLT.TemperedDesignLaw
