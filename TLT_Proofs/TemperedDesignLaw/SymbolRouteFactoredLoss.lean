/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.SymbolRouteGenGap
import TLT_Proofs.TemperedDesignLaw.SymbolChannel

/-!
# The symbol-level route-factored loss and the symbol-channel soft↔hard bridge (TD0.5)

`RouteFactoredLoss` (in `RouteFactoredLoss.lean`) is the **output-Lipschitz** factorization: it admits the
clipped/Lipschitz regression losses but not the 0-1 routing loss (discontinuous in the output). This module
provides the **symbol-level form**: the loss lives on the routed **symbol** `Fin k` rather than the output
`V`, so it admits the 0-1 routing loss, and the soft-vs-hard penalty absorbs the **off-route mass** (the
indicator that the soft top-one route disagrees with the hard route) instead of an output-Lipschitz deviation.

## The soft↔hard bridge for the symbol channel

For the tempered family at any sharpness `β > 0`, `TD0_symbol_invariant_proof` gives that the soft mixture's
top-one route (`leastArgmax (softWeights …)`) is **exactly** the hard route: the symbol channel does not see
the temperature. Hence the off-route penalty is identically `0` and the soft symbol channel's 0-1 route-loss
concept *equals* the hard route-loss concept `routeLossConcept`. Concretely
(`softRouteLossConcept_mem_routeLossClass`) the soft symbol channel's 0-1 loss is a member of the class
`routeLossClass` that S5's `symbolRoute_gen_gap` (Sauer) bounds, so the hard certificate certifies the soft
symbol channel verbatim, with no surrogate.

## What this does NOT close

This bridges the **0-1 symbol/route** channel only. Whether the *smooth* (output-Lipschitz / Dudley, S1)
certificate certifies the **same** generalization quantity as the 0-1 hard certificate is a separate modelling
decision (the factorization-strength choice the `RouteFactoredLoss` note flags "for ratification"):
either (a) commit the design law to a **surrogate** bound `0-1 ≤ Lipschitz surrogate` (a margin/calibration
claim), so the smooth certificate bounds the 0-1 route gap too; or (b) keep the two certificates **per-channel**
(output regression vs symbol routing) and redesign `CapacityProfile` to carry a gap per channel.
-/

noncomputable section

namespace TLT.TemperedDesignLaw

open MeasureTheory

universe u

/-- **A symbol-level route-factored loss.** A loss on the routed **symbol** `Fin k` (uniformly bounded and
nonnegative), the strictly weaker companion of the output-Lipschitz `RouteFactoredLoss`. Because the loss is
read off the discrete symbol rather than the continuous output, it **admits the 0-1 routing loss**
(`zeroOneSymbolLoss`), which the output-Lipschitz form cannot. -/
structure SymbolRouteFactoredLoss (k : ℕ) (Y : Type*) where
  /-- The per-symbol loss. -/
  loss : Fin k → Y → ℝ
  /-- The uniform loss bound (e.g. `1` for the 0-1 loss). -/
  bound : ℝ
  /-- The bound is nonnegative. -/
  bound_nonneg : 0 ≤ bound
  /-- The loss is nonnegative. -/
  loss_nonneg : ∀ s y, 0 ≤ loss s y
  /-- The loss is bounded by `bound`. -/
  loss_le_bound : ∀ s y, loss s y ≤ bound

/-- **The symbol route-factored bound.** The soft top-one route's loss is at most the hard route's loss plus
an **off-route penalty**: `0` when the routes agree, and at most `bound` when they disagree. This is the
symbol-channel analogue of `RouteFactoredLoss.mixture_le_route`; the penalty absorbs the routing disagreement
rather than an output deviation, which is exactly what lets the 0-1 loss factor. -/
theorem SymbolRouteFactoredLoss.softRoute_le_hardRoute {k : ℕ} {Y : Type*}
    (Φ : SymbolRouteFactoredLoss k Y) (softR hardR : Fin k) (y : Y) :
    Φ.loss softR y ≤ Φ.loss hardR y + (if softR = hardR then 0 else Φ.bound) := by
  by_cases h : softR = hardR
  · simp [h]
  · simp only [h, if_false]
    have h1 := Φ.loss_le_bound softR y
    have h2 := Φ.loss_nonneg hardR y
    linarith

/-- **Instance: the 0-1 symbol routing loss** `if s = y then 0 else 1`, the discrete routing loss that the
output-Lipschitz `RouteFactoredLoss` cannot admit. -/
def zeroOneSymbolLoss (k : ℕ) : SymbolRouteFactoredLoss k (Fin k) where
  loss s y := if s = y then 0 else 1
  bound := 1
  bound_nonneg := zero_le_one
  loss_nonneg s y := by split_ifs <;> norm_num
  loss_le_bound s y := by split_ifs <;> norm_num

variable {X : Type u} [MeasurableSpace X] {k : ℕ}

/-- **The soft symbol channel's 0-1 route-loss concept.** The Boolean indicator that the soft mixture's
top-one route `leastArgmax (softWeights …)` disagrees with the target label (the soft analogue of the hard
`routeLossConcept`). -/
def softRouteLossConcept (A : TemperedRouterFamily X k) (hk : 0 < k) (ρ : A.router.Ρ) (y : X → Fin k) :
    Concept X Bool :=
  fun x => decide (leastArgmax (softWeights A ρ x) hk ≠ y x)

/-- **The symbol-channel soft↔hard bridge.** For `β > 0` the soft symbol channel's 0-1 route-loss concept is
**equal** to the hard route-loss concept: by `TD0_symbol_invariant_proof` the soft top-one route is the hard
route, so the two 0-1 losses coincide pointwise. The off-route penalty of `softRoute_le_hardRoute` is therefore
identically `0` on the tempered family; the symbol channel is sharpness-blind. -/
theorem softRouteLossConcept_eq_routeLossConcept (A : TemperedRouterFamily X k) (hk : 0 < k)
    (hβ : 0 < A.β) (ρ : A.router.Ρ) (y : X → Fin k) :
    softRouteLossConcept A hk ρ y = routeLossConcept A.router hk ρ y := by
  funext x
  have hinv : leastArgmax (softWeights A ρ x) hk = A.router.route hk ρ x :=
    TD0_symbol_invariant_proof A hk hβ ρ x
  simp only [softRouteLossConcept, routeLossConcept, hinv]

/-- **The soft symbol channel is certified by S5.** For `β > 0` the soft 0-1 route-loss concept is a member of
the hard route-loss class `routeLossClass A.router`, so S5's uniform symbol-route generalization bound
(`symbolRoute_gen_gap`, the Sauer–Shelah arrangement bound), which controls every concept in that class,
certifies the soft symbol channel verbatim, without any surrogate. -/
theorem softRouteLossConcept_mem_routeLossClass (A : TemperedRouterFamily X k) (hk : 0 < k)
    (hβ : 0 < A.β) (ρ : A.router.Ρ) (y : X → Fin k) :
    softRouteLossConcept A hk ρ y ∈ routeLossClass A.router hk y := by
  rw [softRouteLossConcept_eq_routeLossConcept A hk hβ ρ y]
  exact ⟨ρ, rfl⟩

end TLT.TemperedDesignLaw
