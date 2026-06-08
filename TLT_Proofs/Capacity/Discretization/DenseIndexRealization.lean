/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Capacity.Discretization.DenseBaseChangeCapacity

/-!
# Dense index realizations of a real domain

The capacity-invariance thesis is not about dyadics: it is about *any* countable family of points
that realizes a dense subset of a real domain `K`. `DenseIndexFor K` packages exactly that data — a
countable index type `I`, a realization `I → E` landing in `K`, and the density of those realized
points in `K`. The supremum of a continuous functional over such an index equals its supremum over
`K` itself.

This isolates the thesis-level object — *capacity does not depend on which countable dense index
realizes the real class* — from the numerical base that supplies one such index. The dyadic grid is
then merely one instance (`dyadicDenseIndexForRealBall`), and `ciSup_baseGrid_eq_ciSup_realBall`
becomes a special case. No geometry, Lipschitz, or covering reasoning appears here; the real domain
`K` is the ambient comparison target and the index disappears through the equality.

## Main definitions

- `DenseIndexFor` — a countable family realizing a dense subset of a real domain.

## Main results

- `ciSup_denseIndex_eq` — the supremum of a continuous functional over a dense index equals its
  supremum over the domain.
-/

/-!
## References
- dense-subset supremum equality (Mathlib `Dense.ciSup'`; parallel [55]).
- Provenance: Innovation (definitional packaging) — the `DenseIndexFor` index-agnostic abstraction;
  its one theorem is the standard dense-subset supremum equality.
-/

open Metric

noncomputable section

namespace TLT.Capacity

variable {E : Type*} [PseudoMetricSpace E] {K : Set E}

/-- A **dense index realization** of a real domain `K`: a countable index type whose realized points
lie in `K` and are dense in `K`. The capacity over such an index equals the capacity over `K`. -/
structure DenseIndexFor (K : Set E) where
  /-- The index type. -/
  I : Type*
  /-- The index is countable (this is what makes the experiment-side supremum measurable). -/
  countable : Countable I
  /-- The realization of each index as a point of the ambient space. -/
  realize : I → E
  /-- Every realized point lies in the domain `K`. -/
  mem : ∀ i, realize i ∈ K
  /-- The realized points are dense in `K` (as a subset of the subtype `↥K`). -/
  dense : Dense (Set.range fun i => (⟨realize i, mem i⟩ : K))

attribute [instance] DenseIndexFor.countable

/-- **The dense-index supremum equals the domain supremum.** For a continuous functional `φ` on the
real domain `K`, the supremum over a dense index realizing `K` equals the supremum over all of `K`.
The index `I` is countable, so the left-hand supremum is an experiment-side countable supremum; the
right-hand side is the real-domain target. -/
theorem ciSup_denseIndex_eq (D : DenseIndexFor K) (φ : K → ℝ) (hφ : Continuous φ) :
    (⨆ i : D.I, φ ⟨D.realize i, D.mem i⟩) = ⨆ θ : K, φ θ := by
  have hsurj : Function.Surjective
      (fun i : D.I => (⟨⟨D.realize i, D.mem i⟩, ⟨i, rfl⟩⟩ :
        Set.range fun i => (⟨D.realize i, D.mem i⟩ : K))) := by
    rintro ⟨θ, i, hi⟩
    exact ⟨i, by simp only [Subtype.mk.injEq]; exact hi⟩
  calc (⨆ i : D.I, φ ⟨D.realize i, D.mem i⟩)
      = ⨆ x : Set.range fun i => (⟨D.realize i, D.mem i⟩ : K), φ x.1 :=
        ciSup_comp_surjective hsurj (fun x => φ x.1)
    _ = ⨆ θ : K, φ θ := D.dense.ciSup' hφ

/-- The dyadic grid in the real ball is a dense index realization of the ball: the canonical
experiment-side index of the theory-side `RealBall d R`. The density is exactly `dense_baseGridInBall`.
-/
def dyadicDenseIndexForRealBall (B : Type*) [CommRing B] [DenseNumBase B] {d : ℕ} (R : ℝ)
    (hR : 0 ≤ R) : DenseIndexFor (RealBall d R) where
  I := BaseWeightPreimage B R
  countable := inferInstance
  realize := fun w => embedBase B w.1
  mem := fun w => w.2
  dense := by
    have hset : (Set.range fun w : BaseWeightPreimage B R => (⟨embedBase B w.1, w.2⟩ : RealBall d R))
        = BaseGridInBall B (d := d) R := by
      ext θK
      constructor
      · rintro ⟨w, hw⟩; exact ⟨w.1, w.2, by rw [← hw]⟩
      · rintro ⟨w, hw, hθ⟩; exact ⟨⟨w, hw⟩, Subtype.ext hθ.symm⟩
    rw [hset]; exact dense_baseGridInBall B (d := d) hR

end TLT.Capacity
