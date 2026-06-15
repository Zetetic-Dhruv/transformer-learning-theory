/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.Conjectures

/-!
# The symbol channel is sharpness-invariant (TD1, per-layer core)

The route label (the `leastArgmax` of the scores) does not see the sharpness `β` for `β > 0`. The
general fact is order-theoretic: a strictly monotone reparametrization of the scores preserves the
`leastArgmax` (it preserves both the maximizer set and the least-index tie-break). The tempered softmax
`exp(β·s)/Z` is exactly such a reparametrization of the scores (`×β`, then `exp`, then `÷Z`, each
strictly monotone for `β > 0`, `Z > 0`), so its `leastArgmax` is the hard route.
-/

open scoped BigOperators

universe u

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **The order-theoretic core.** A strictly monotone reparametrization of a score vector preserves the
`leastArgmax`: `leastArgmax (φ ∘ v) = leastArgmax v` for `StrictMono φ`. The single reusable fact behind
symbol-channel sharpness-invariance: `φ` preserves the maximizer set (non-strict order) and the
least-index tie-break (strict order), so the unique least-argmax is the same vector. -/
theorem leastArgmax_comp_strictMono {k : ℕ} (v : Fin k → ℝ) (hk : 0 < k) {φ : ℝ → ℝ}
    (hφ : StrictMono φ) : leastArgmax (fun i => φ (v i)) hk = leastArgmax v hk := by
  refine isLeastArgmax_unique v _ _ ?_ (leastArgmax_spec v hk)
  obtain ⟨hmax, hleast⟩ := leastArgmax_spec (fun i => φ (v i)) hk
  exact ⟨fun j => hφ.le_iff_le.mp (hmax j), fun j hj => hφ.lt_iff_lt.mp (hleast j hj)⟩

/-- **TD1 (per-layer core): symbol-channel sharpness invariance.** For `β > 0`, the `leastArgmax` of the
tempered softmax weights is exactly the hard route. Proof: the softmax `exp(β·s)/Z` is a strictly
monotone reparametrization of the scores (`leastArgmax_comp_strictMono` with `φ = fun t => exp(β·t)/Z`),
so its `leastArgmax` equals the scores' `leastArgmax`, which is the route (`top1_softmax_eq_argmax` +
`softmaxTop1_eq_route`). -/
theorem TD0_symbol_invariant_proof {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : TemperedRouterFamily X k) (hk : 0 < k) : TD0_symbol_invariant A hk := by
  intro hβ ρ x
  have hZ : (0 : ℝ) < ∑ j, Real.exp (A.β * A.router.score ρ x j) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hφ : StrictMono
      (fun t => Real.exp (A.β * t) / ∑ j, Real.exp (A.β * A.router.score ρ x j)) := by
    intro a b hab
    dsimp only
    have h2 : Real.exp (A.β * a) < Real.exp (A.β * b) :=
      Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hab hβ)
    gcongr
  have hsw : softWeights A ρ x
      = fun i => (fun t => Real.exp (A.β * t) / ∑ j, Real.exp (A.β * A.router.score ρ x j))
          (A.router.score ρ x i) := rfl
  rw [hardRoute, hsw, leastArgmax_comp_strictMono _ hk hφ]
  exact ((top1_softmax_eq_argmax A.router hk ρ x).symm).trans
    (congrFun (congrFun (softmaxTop1_eq_route A.router hk) ρ) x)

/-- The hard route is the `leastArgmax` of the scores; the symbol channel reads the score argmax
directly (`softmaxTop1_eq_route` + `top1_softmax_eq_argmax`). -/
theorem hardRoute_eq_leastArgmax {X : Type u} [MeasurableSpace X] {k : ℕ}
    (A : TemperedRouterFamily X k) (hk : 0 < k) (ρ : A.router.Ρ) (x : X) :
    hardRoute A hk ρ x = leastArgmax (A.router.score ρ x) hk :=
  (congrFun (congrFun (softmaxTop1_eq_route A.router hk) ρ) x).symm.trans
    (top1_softmax_eq_argmax A.router hk ρ x)

end TLT.TemperedDesignLaw
