/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Topology.Order.IsLUB
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import TLT_Proofs.Capacity.Symmetrization

/-!
# Numerical bases and the dense base-change capacity invariance

A *numerical base* is a countable subring of `ℝ` — a number system whose arithmetic embeds exactly
into `ℝ`. A *dense* numerical base additionally has dense image. The point of the abstraction is that
the statistical capacity of a parametrised function class — the expected supremum of the empirical
Rademacher process over a weight ball — is **invariant under dense base change**: computing the
capacity with weights drawn from any dense base (e.g. the dyadic rationals, the rationals) gives the
same number as computing it over the real ball. The only base-dependent quantity is the arithmetic
error of *executing* in finite precision, which is a separate, additive term.

This file builds the grammar (`NumBase`, `DenseNumBase`) and the density anchors used by the
invariance theorem; the invariance theorem itself rests on `Dense.ciSup` for a continuous functional
over a dense subset of the (compact) weight ball.

## Main definitions

- `NumBase B` — a countable ring with an injective ring hom `toReal : B →+* ℝ`.
- `DenseNumBase B` — additionally `DenseRange toReal`.
- `embedBase` — the coordinatewise embedding of `B`-weights into the real parameter space.

## Main results (this section)

- `denseRange_embedBase` — `B`-weights are dense in the real parameter space when `B` is dense.
-/

open Set Metric MeasureTheory

noncomputable section

namespace TLT.Capacity

/-! ### The numerical-base grammar -/

/-- A numerical base: a countable ring whose arithmetic embeds *exactly* (as a ring hom) and
injectively into `ℝ`. The ring-hom requirement is load-bearing — the forward pass composes the base's
arithmetic, so base-change must commute with the realised computation. -/
class NumBase (B : Type*) [CommRing B] where
  /-- The exact embedding into `ℝ`, a ring hom. -/
  toReal : B →+* ℝ
  /-- The embedding is injective: `B` is a faithful exact substructure of `ℝ`. -/
  inj_toReal : Function.Injective toReal
  /-- `B` is countable, which makes the symmetrisation supremum measurable for free. -/
  [countable : Countable B]

attribute [instance] NumBase.countable

/-- A *dense* numerical base: its image is dense in `ℝ`, so the weight-ball capacity equals the real
ball's. -/
class DenseNumBase (B : Type*) [CommRing B] extends NumBase B where
  /-- The image of `toReal` is dense in `ℝ`. -/
  dense_toReal : DenseRange (NumBase.toReal : B → ℝ)

/-! ### The real parameter space and the base embedding -/

/-- The real parameter space: `d`-dimensional Euclidean space (the `ℓ²` metric gives the clean
volumetric covering used downstream). -/
abbrev ParamSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The coordinatewise embedding of `B`-weights into the real parameter space. -/
def embedBase (B : Type*) [CommRing B] [NumBase B] {d : ℕ} :
    (Fin d → B) → ParamSpace d :=
  fun w => WithLp.toLp 2 (fun i => NumBase.toReal (w i))

/-- The closed real weight ball of radius `R`. -/
def RealBall (d : ℕ) (R : ℝ) : Set (ParamSpace d) := Metric.closedBall 0 R

/-- The experiment-side index: the `B`-weights whose real embedding lies in the ball. This is the
**preimage** of a real geometric condition under the base embedding, not a geometric domain itself —
it carries no metric/Lipschitz/covering content and exists only to index the dense base-change. -/
def BaseWeightPreimage (B : Type*) [CommRing B] [NumBase B] {d : ℕ} (R : ℝ) : Set (Fin d → B) :=
  {w | embedBase B w ∈ RealBall d R}

/-- The image, in the real parameter space, of the `B`-weight ball. -/
def BaseRealSet (B : Type*) [CommRing B] [NumBase B] {d : ℕ} (R : ℝ) : Set (ParamSpace d) :=
  {θ | ∃ w : Fin d → B, w ∈ BaseWeightPreimage B R ∧ θ = embedBase B w}

/-! ### FR1 — finite-product density of the base embedding -/

/-- **`B`-weights are dense in the real parameter space.** A dense base embeds coordinatewise to a
dense subset of `ℝᵈ`: approximate each coordinate, the Euclidean error is controlled by `√d` times the
coordinate tolerance. -/
theorem denseRange_embedBase (B : Type*) [CommRing B] [DenseNumBase B] (d : ℕ) :
    DenseRange (embedBase B : (Fin d → B) → ParamSpace d) := by
  rw [Metric.denseRange_iff]
  intro θ r hr
  set δ : ℝ := r / (Real.sqrt d + 1) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hchoice : ∀ i, ∃ b : B, dist (θ i) (NumBase.toReal b) < δ := fun i =>
    (Metric.denseRange_iff.mp DenseNumBase.dense_toReal) (θ i) δ hδpos
  choose w hw using hchoice
  refine ⟨w, ?_⟩
  rw [EuclideanSpace.dist_eq]
  calc Real.sqrt (∑ i, dist (θ i) ((embedBase B w) i) ^ 2)
      ≤ Real.sqrt (∑ _i : Fin d, δ ^ 2) := by
        apply Real.sqrt_le_sqrt
        refine Finset.sum_le_sum fun i _ => ?_
        have hcoord : (embedBase B w) i = NumBase.toReal (w i) := rfl
        rw [hcoord]
        exact pow_le_pow_left₀ dist_nonneg (le_of_lt (hw i)) 2
    _ = Real.sqrt ((d : ℝ) * δ ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = Real.sqrt d * δ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hδpos.le]
    _ < r := by
        rw [hδ]
        have h2 : 0 < Real.sqrt d + 1 := by positivity
        rw [mul_div_assoc', div_lt_iff₀ h2]
        nlinarith [Real.sqrt_nonneg (d : ℝ)]

/-! ### FR2 — the base grid is dense in the (closed) weight ball -/

/-- The base-grid points that lie in the real ball, as a subset of the ball. -/
def BaseGridInBall (B : Type*) [CommRing B] [NumBase B] {d : ℕ} (R : ℝ) :
    Set (RealBall d R) :=
  {θK | ∃ w : Fin d → B, w ∈ BaseWeightPreimage B R ∧ (θK : ParamSpace d) = embedBase B w}

/-- **The base grid is dense in the closed real ball.** Direct approximation of a boundary point by a
dense ambient set can spill outside the ball; the fix is to first contract the target radially inward by
`(1 - t)` (landing strictly inside the ball with a positive margin), then approximate the contracted
point so closely that the approximant stays in the ball. -/
theorem dense_baseGridInBall (B : Type*) [CommRing B] [DenseNumBase B] {d : ℕ} {R : ℝ}
    (hR : 0 ≤ R) : Dense (BaseGridInBall B (d := d) R) := by
  have h0mem : (0 : ParamSpace d) ∈ RealBall d R := by
    simp only [RealBall, Metric.mem_closedBall, dist_self]; exact hR
  intro θK
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hθR : ‖(θK : ParamSpace d)‖ ≤ R := by
    have := θK.2; simp only [RealBall, mem_closedBall_zero_iff] at this; exact this
  have hemb0 : embedBase B (0 : Fin d → B) = 0 := by
    have hz : (fun i => NumBase.toReal ((0 : Fin d → B) i)) = (0 : Fin d → ℝ) := by
      funext i; simp
    unfold embedBase; rw [hz, WithLp.toLp_zero]
  by_cases hθ0 : (θK : ParamSpace d) = 0
  · -- target is the centre: the zero grid point works
    refine ⟨⟨0, h0mem⟩, ⟨0, ?_, ?_⟩, ?_⟩
    · show embedBase B (0 : Fin d → B) ∈ RealBall d R
      rw [hemb0]; exact h0mem
    · exact hemb0.symm
    · rw [Subtype.dist_eq]
      show dist (θK : ParamSpace d) 0 < ε
      rw [hθ0, dist_self]; exact hε
  · -- contract radially inward, then approximate
    set n : ℝ := ‖(θK : ParamSpace d)‖ with hn
    have hnpos : 0 < n := by rw [hn]; exact norm_pos_iff.mpr hθ0
    set t : ℝ := min (1/2) (ε / (4 * n)) with ht
    have htpos : 0 < t := by rw [ht]; positivity
    have htle : t ≤ 1/2 := min_le_left _ _
    have htn : t * n ≤ ε / 4 := by
      have : t ≤ ε / (4 * n) := min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at this; nlinarith
    set p : ParamSpace d := (1 - t) • (θK : ParamSpace d) with hp
    have hsub : (θK : ParamSpace d) - p = t • (θK : ParamSpace d) := by
      rw [hp]; module
    have hdist_θp : dist (θK : ParamSpace d) p = t * n := by
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have hpnorm : ‖p‖ = (1 - t) * n := by
      rw [hp, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t)]
    set margin : ℝ := R - (1 - t) * n with hmargin
    have hmarginpos : 0 < margin := by rw [hmargin]; nlinarith
    set δ : ℝ := min (ε / 2) margin with hδ
    have hδpos : 0 < δ := by rw [hδ]; exact lt_min (by linarith) hmarginpos
    obtain ⟨w, hw⟩ := (Metric.denseRange_iff.mp (denseRange_embedBase B d)) p δ hδpos
    -- hw : dist p (embedBase B w) < δ
    have hynorm : ‖embedBase B w‖ < R := by
      have h1 : ‖embedBase B w‖ ≤ ‖p‖ + dist p (embedBase B w) := by
        calc ‖embedBase B w‖ = ‖p + (embedBase B w - p)‖ := by congr 1; abel
          _ ≤ ‖p‖ + ‖embedBase B w - p‖ := norm_add_le _ _
          _ = ‖p‖ + dist p (embedBase B w) := by rw [dist_eq_norm, norm_sub_rev]
      rw [hpnorm] at h1
      have hδm : δ ≤ margin := min_le_right _ _
      rw [hmargin] at hδm
      linarith [hw]
    have hymem : embedBase B w ∈ RealBall d R := by
      simp only [RealBall, mem_closedBall_zero_iff]; exact le_of_lt hynorm
    refine ⟨⟨embedBase B w, hymem⟩, ⟨w, hymem, rfl⟩, ?_⟩
    rw [Subtype.dist_eq]
    calc dist (θK : ParamSpace d) (embedBase B w)
        ≤ dist (θK : ParamSpace d) p + dist p (embedBase B w) := dist_triangle _ _ _
      _ < t * n + δ := by linarith [hdist_θp, hw]
      _ ≤ ε / 4 + ε / 2 := by linarith [min_le_left (ε/2) margin, htn]
      _ < ε := by linarith

/-! ### FR3 — dense supremum over the ball -/

/-- **The supremum of a continuous functional over the base grid equals its supremum over the whole
ball.** Immediate from `Dense.ciSup'` (no boundedness needed) given the density of the grid (FR2). -/
theorem ciSup_baseGrid_eq_ciSup_realBall (B : Type*) [CommRing B] [DenseNumBase B] {d : ℕ} {R : ℝ}
    (hR : 0 ≤ R) (φ : RealBall d R → ℝ) (hφ : Continuous φ) :
    (⨆ θ : BaseGridInBall B (d := d) R, φ θ.1) = ⨆ θ : RealBall d R, φ θ :=
  (dense_baseGridInBall B (d := d) hR).ciSup' hφ

/-- A real supremum is invariant under reindexing by a surjection (the ranges coincide). The
conditionally-complete (ℝ) analogue of `Function.Surjective.iSup_comp`. -/
theorem ciSup_comp_surjective {ι ι' : Type*} {f : ι → ι'} (hf : Function.Surjective f)
    (g : ι' → ℝ) : ⨆ x, g (f x) = ⨆ y, g y := by
  have hr : Set.range (fun x => g (f x)) = Set.range g := by
    ext y
    refine ⟨?_, ?_⟩
    · rintro ⟨x, rfl⟩; exact ⟨f x, rfl⟩
    · rintro ⟨y', rfl⟩; obtain ⟨x, rfl⟩ := hf y'; exact ⟨x, rfl⟩
  show sSup (Set.range fun x => g (f x)) = sSup (Set.range g)
  rw [hr]

/-! ### FR4 — the Rademacher functional and the pointwise capacity equality -/

/-- The empirical Rademacher average is continuous in its value vector (it is linear). -/
theorem continuous_empRadVec {m : ℕ} (σ : SignVector m) :
    Continuous (fun v : Fin m → ℝ => empRadVec v σ) := by
  simp only [empRadVec, empRad]
  exact continuous_const.mul
    (continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const)

/-- The empirical Rademacher functional at a real parameter `θ`, on sample `S`, with sign vector `σ`. -/
def radFunctional {X : Type*} {d m : ℕ} (F : ParamSpace d → X → ℝ) (S : Fin m → X)
    (σ : SignVector m) (θ : ParamSpace d) : ℝ :=
  empRadVec (fun j => F θ (S j)) σ

/-- The Rademacher functional is continuous in the parameter when the model is. -/
theorem continuous_radFunctional {X : Type*} {d m : ℕ} (F : ParamSpace d → X → ℝ) (S : Fin m → X)
    (σ : SignVector m) (hF : ∀ x, Continuous fun θ : ParamSpace d => F θ x) :
    Continuous (fun θ : ParamSpace d => radFunctional F S σ θ) := by
  unfold radFunctional
  exact (continuous_empRadVec σ).comp (continuous_pi fun j => hF (S j))

/-- **Pointwise capacity equality.** For a fixed sign vector, the supremum of the Rademacher functional
over the embedded `B`-weight ball equals its supremum over the real ball: reindex the `B`-weights onto
the dense grid, then apply the dense-supremum equality (FR3). -/
theorem capacity_pointwise_eq (B : Type*) [CommRing B] [DenseNumBase B] {X : Type*} {d m : ℕ} {R : ℝ}
    (hR : 0 ≤ R) (F : ParamSpace d → X → ℝ) (S : Fin m → X) (σ : SignVector m)
    (hF : ∀ x, Continuous fun θ : ParamSpace d => F θ x) :
    (⨆ w : BaseWeightPreimage B R, radFunctional F S σ (embedBase B w.1))
      = ⨆ θ : RealBall d R, radFunctional F S σ θ.1 := by
  have hsurj : Function.Surjective
      (fun w : BaseWeightPreimage B R =>
        (⟨⟨embedBase B w.1, w.2⟩, ⟨w.1, w.2, rfl⟩⟩ : BaseGridInBall B (d := d) R)) := by
    rintro ⟨θ_ball, w', hw', hθeq⟩
    refine ⟨⟨w', hw'⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext; exact hθeq.symm
  calc (⨆ w : BaseWeightPreimage B R, radFunctional F S σ (embedBase B w.1))
      = ⨆ θK : BaseGridInBall B (d := d) R, radFunctional F S σ θK.1.1 :=
        ciSup_comp_surjective hsurj (fun θK => radFunctional F S σ θK.1.1)
    _ = ⨆ θ : RealBall d R, radFunctional F S σ θ.1 :=
        ciSup_baseGrid_eq_ciSup_realBall B hR (fun θ => radFunctional F S σ θ.1)
          ((continuous_radFunctional F S σ hF).comp continuous_subtype_val)

/-! ### FR5 — the empirical capacity equality (the base-invariance theorem) -/

/-- The empirical Rademacher complexity of the `B`-weight ball on sample `S`. -/
def empiricalCapacityBase (B : Type*) [CommRing B] [NumBase B] {X : Type*} {d m : ℕ} (R : ℝ)
    (F : ParamSpace d → X → ℝ) (S : Fin m → X) : ℝ :=
  ∫ σ, ⨆ w : BaseWeightPreimage B R, radFunctional F S σ (embedBase B w.1) ∂radMeasure m

/-- The empirical Rademacher complexity of the real weight ball on sample `S`. -/
def empiricalCapacityReal {X : Type*} {d m : ℕ} (R : ℝ) (F : ParamSpace d → X → ℝ) (S : Fin m → X) :
    ℝ :=
  ∫ σ, ⨆ θ : RealBall d R, radFunctional F S σ θ.1 ∂radMeasure m

/-- **Dense base-change capacity invariance.** The empirical Rademacher complexity computed over any
dense numerical base equals the one computed over the reals: the capacity is a base-invariant. -/
theorem empiricalCapacity_base_eq_real (B : Type*) [CommRing B] [DenseNumBase B] {X : Type*}
    {d m : ℕ} {R : ℝ} (hR : 0 ≤ R) (F : ParamSpace d → X → ℝ) (S : Fin m → X)
    (hF : ∀ x, Continuous fun θ : ParamSpace d => F θ x) :
    empiricalCapacityBase B R F S = empiricalCapacityReal R F S := by
  unfold empiricalCapacityBase empiricalCapacityReal
  exact integral_congr_ae (ae_of_all _ fun σ => capacity_pointwise_eq B hR F S σ hF)

end TLT.Capacity
