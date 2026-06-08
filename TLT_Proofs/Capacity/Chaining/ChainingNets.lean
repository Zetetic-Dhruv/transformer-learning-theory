/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Capacity.Chaining.MetricEntropy
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Chaining infrastructure: dyadic nets and approximation

Dudley's chaining argument approximates each point of a totally bounded index set `s` by a hierarchy
of finite `ε`-nets at the dyadic scales `ε_k = D · 2^{-k}`. This file provides that scaffolding on
top of Mathlib's `Metric.coveringNumber` / `Metric.minimalCover`:

* the dyadic scales and their arithmetic;
* `coveringNumber_ne_top_of_totallyBounded`, the finiteness of the covering number for a totally
  bounded set (the prerequisite for `minimalCover` to be an actual cover);
* `coveringNet`, the canonical minimal `ε`-net, with its cardinality equal to the covering number and
  its `ε`-approximation property;
* the telescoping bound: consecutive dyadic approximations of a point are within `(3/2)·ε_k`.

## References

A. N. Kolmogorov and V. M. Tikhomirov, *ε-entropy and ε-capacity of sets in function spaces*,
Uspekhi Mat. Nauk 14 (1959); R. M. Dudley, *The sizes of compact subsets of Hilbert space and
continuity of Gaussian processes*, J. Funct. Anal. 1 (1967), 290–330.
-/

open Metric Set
open scoped ENNReal NNReal

noncomputable section

namespace TLT.Capacity

variable {A : Type*} [PseudoMetricSpace A]

/-! ### Dyadic scales -/

/-- The dyadic scale at level `k`: `ε_k = D · 2^{-k}`. -/
def dyadicScale (D : ℝ) (k : ℕ) : ℝ := D * (2 : ℝ) ^ (-(k : ℤ))

lemma dyadicScale_pos {D : ℝ} (hD : 0 < D) (k : ℕ) : 0 < dyadicScale D k :=
  mul_pos hD (zpow_pos (by norm_num) _)

lemma dyadicScale_zero (D : ℝ) : dyadicScale D 0 = D := by simp [dyadicScale]

lemma dyadicScale_succ (D : ℝ) (k : ℕ) : dyadicScale D (k + 1) = dyadicScale D k / 2 := by
  simp only [dyadicScale, Nat.cast_add, Nat.cast_one, neg_add,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

lemma dyadicScale_anti {D : ℝ} (hD : 0 < D) {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    dyadicScale D k₂ ≤ dyadicScale D k₁ := by
  apply mul_le_mul_of_nonneg_left _ hD.le
  apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  exact neg_le_neg (by exact_mod_cast h)

/-! ### Finiteness of the covering number -/

/-- For a totally bounded set, the (internal) covering number at any positive scale is finite. This
is the prerequisite for `minimalCover` to be a genuine cover. Proof: total boundedness yields a finite
external cover at scale `ε/2`, and an external `ε/2`-cover bounds the internal `ε`-covering number. -/
lemma coveringNumber_ne_top_of_totallyBounded {s : Set A} (hs : TotallyBounded s)
    {ε : ℝ≥0} (hε : 0 < ε) : Metric.coveringNumber ε s ≠ ⊤ := by
  obtain ⟨t, htfin, htcover⟩ := Metric.totallyBounded_iff.mp hs ((ε : ℝ) / 2) (by positivity)
  have hIsCover : Metric.IsCover (ε / 2) s t := by
    rw [Metric.isCover_iff_subset_iUnion_closedBall]
    refine htcover.trans (Set.iUnion₂_mono fun y _ => ?_)
    have hcoe : ((ε / 2 : ℝ≥0) : ℝ) = (ε : ℝ) / 2 := by push_cast; ring
    rw [hcoe]; exact Metric.ball_subset_closedBall
  have hε2 : (2 : ℝ≥0) * (ε / 2) = ε := by apply NNReal.coe_injective; push_cast; ring
  have hle : Metric.coveringNumber ε s ≤ t.encard := by
    calc Metric.coveringNumber ε s
        = Metric.coveringNumber (2 * (ε / 2)) s := by rw [hε2]
      _ ≤ Metric.externalCoveringNumber (ε / 2) s :=
          Metric.coveringNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ t.encard := hIsCover.externalCoveringNumber_le_encard
  exact (lt_of_le_of_lt hle htfin.encard_lt_top).ne

/-! ### The canonical minimal net -/

/-- The canonical minimal `ε`-net of `s`: `Metric.minimalCover` packaged as a `Finset`. -/
def coveringNet (ε : ℝ) (s : Set A) : Finset A :=
  (Metric.finite_minimalCover (ε := ε.toNNReal) (A := s)).toFinset

lemma coveringNet_subset {ε : ℝ} {s : Set A} : (coveringNet ε s : Set A) ⊆ s := by
  rw [coveringNet, Set.Finite.coe_toFinset]; exact Metric.minimalCover_subset

/-- The cardinality of the canonical net equals the covering number (when finite). -/
lemma coveringNet_card {ε : ℝ} {s : Set A}
    (hfin : Metric.coveringNumber ε.toNNReal s ≠ ⊤) :
    (coveringNet ε s).card = (Metric.coveringNumber ε.toNNReal s).toNat := by
  have h : ((coveringNet ε s).card : ℕ∞) = Metric.coveringNumber ε.toNNReal s := by
    rw [coveringNet, ← Metric.finite_minimalCover.encard_eq_coe_toFinset_card,
      Metric.encard_minimalCover hfin]
  rw [← h, ENat.toNat_coe]

/-- The canonical net `ε`-covers `s`: every point of `s` is within `ε` of a net point (`ε ≥ 0`,
covering number finite). -/
lemma coveringNet_approx {ε : ℝ} {s : Set A} (hε : 0 ≤ ε)
    (hfin : Metric.coveringNumber ε.toNNReal s ≠ ⊤) {x : A} (hx : x ∈ s) :
    ∃ y ∈ coveringNet ε s, dist x y ≤ ε := by
  have hcov := Metric.isCover_minimalCover hfin
  rw [Metric.isCover_iff_subset_iUnion_closedBall] at hcov
  obtain ⟨y, hy_mem, hy_ball⟩ := Set.mem_iUnion₂.mp (hcov hx)
  refine ⟨y, ?_, ?_⟩
  · rw [coveringNet, Set.Finite.mem_toFinset]; exact hy_mem
  · rw [Metric.mem_closedBall] at hy_ball
    rwa [Real.coe_toNNReal ε hε] at hy_ball

/-! ### Chaining approximation and telescoping -/

/-- The chaining approximation at level `k`: any point of `s` has a net point within `ε_k`. -/
lemma chaining_approximation {s : Set A} {D : ℝ} (hD : 0 < D)
    (hs : TotallyBounded s) (k : ℕ) {x : A} (hx : x ∈ s) :
    ∃ y ∈ coveringNet (dyadicScale D k) s, dist x y ≤ dyadicScale D k :=
  coveringNet_approx (dyadicScale_pos hD k).le
    (coveringNumber_ne_top_of_totallyBounded hs (Real.toNNReal_pos.mpr (dyadicScale_pos hD k))) hx

/-- Telescoping bound: two consecutive dyadic approximations of a point lie within `(3/2)·ε_k`. -/
lemma telescoping_bound {D : ℝ} (k : ℕ) {x y_k y_k1 : A}
    (hk : dist x y_k ≤ dyadicScale D k) (hk1 : dist x y_k1 ≤ dyadicScale D (k + 1)) :
    dist y_k y_k1 ≤ 3 / 2 * dyadicScale D k := by
  calc dist y_k y_k1
      ≤ dist y_k x + dist x y_k1 := dist_triangle _ _ _
    _ ≤ dyadicScale D k + dyadicScale D (k + 1) := by
        rw [dist_comm]; exact add_le_add hk hk1
    _ = dyadicScale D k + dyadicScale D k / 2 := by rw [dyadicScale_succ]
    _ = 3 / 2 * dyadicScale D k := by ring

end TLT.Capacity
