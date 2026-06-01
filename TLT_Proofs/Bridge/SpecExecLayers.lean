/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.ExecLayerInstances
import TLT_Proofs.Bridge.ForwardContinuity

/-!
# Wiring the literal TorchLean spec ops into the network envelope

`ExecLayerInstances` builds `ExecLayer` records over the coordinate space `Fin s → Fin d → ℝ`. This
file connects them to the **literal** TorchLean spec operations: each spec op, read in coordinates via
`matCoords ∘ Spec.op ∘ matrixTensor`, is the corresponding coordinate map, so the spec ops populate the
`ExecLayer` list consumed by `execComp_envelope` / `execComp_risk_transfer`.

- `matCoords_reluSpec` / `matCoords_matMulSpec` — the literal `Activation.reluSpec` and `matMulSpec`,
  read in coordinates, are `reluCoord` and `matMulCoord`.
- `reluSpecExecLayer` — the literal ReLU layer as an `ExecLayer`: `1`-Lipschitz, rounding-free
  (`reluSpecExecLayer_ideal` certifies its ideal map is the literal `reluSpec` in coordinates).
- `matMulSpecExecLayer` — the literal matrix-multiply layer as an `ExecLayer`: Lipschitz with the
  operator ∞-norm column bound, with the executed map and its uniform rounding bound supplied (the
  domain-dependent fp32 budget).

Layer-normalization (`get2_layerNorm` connects `Spec.layerNorm` to `layerNormCoordEps`) and attention
are the remaining spec ops; their `ExecLayer.lip` constants are regularizer- or domain-dependent and are
not constructed here.
-/

open Spec

namespace TLT

variable {s d : ℕ}

/-- Bridge: the literal ReLU spec op, read in coordinates, is `reluCoord`. -/
lemma matCoords_reluSpec (X : Fin s → Fin d → ℝ) :
    matCoords (Activation.reluSpec (matrixTensor X)) = reluCoord X := by
  funext i j
  simp only [matCoords, reluCoord, get2_reluSpec, get2_matrixTensor]

/-- Bridge: the literal matrix-multiply spec op, read in coordinates, is `matMulCoord`. -/
lemma matCoords_matMulSpec (W : Tensor ℝ (.dim d (.dim d .scalar))) (X : Fin s → Fin d → ℝ) :
    matCoords (matMulSpec (matrixTensor X) W) = matMulCoord (matCoords W) X := by
  funext i j
  simp only [matCoords, matMulCoord, get2_mat_mul_spec]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [get2_matrixTensor]

/-- The literal ReLU spec op as an `ExecLayer` over `Fin s → Fin d → ℝ`: `1`-Lipschitz in the sup
metric and rounding-free (the componentwise `max (·) 0` select introduces no arithmetic error). -/
def reluSpecExecLayer : ExecLayer (Fin s → Fin d → ℝ) where
  ideal := reluCoord
  exec := reluCoord
  lip := 1
  rnd := 0
  lip_nonneg := zero_le_one
  ideal_lip := by
    intro a b
    rw [one_mul]
    refine (dist_pi_le_iff dist_nonneg).mpr (fun i => ?_)
    refine (dist_pi_le_iff dist_nonneg).mpr (fun j => ?_)
    simp only [reluCoord]
    calc dist (max (a i j) 0) (max (b i j) 0)
        ≤ dist (a i j) (b i j) := by
          simp only [Real.dist_eq]; exact abs_max_sub_max_le_abs _ _ _
      _ ≤ dist a b := le_trans (dist_le_pi_dist (a i) (b i) j) (dist_le_pi_dist a b i)
  exec_close := by intro y; simp

/-- The `reluSpecExecLayer` ideal map is the literal ReLU spec op read in coordinates. -/
lemma reluSpecExecLayer_ideal (X : Fin s → Fin d → ℝ) :
    (reluSpecExecLayer (s := s) (d := d)).ideal X
      = matCoords (Activation.reluSpec (matrixTensor X)) :=
  (matCoords_reluSpec X).symm

/-- The literal matrix-multiply spec op as an `ExecLayer` over `Fin s → Fin d → ℝ`: Lipschitz with the
operator ∞-norm column bound `Λ` (a uniform bound on the column absolute sums `∑ₖ |Wₖⱼ|`), proved here.
The executed map and its uniform rounding bound `rnd` are supplied (e.g. the reduction-level rounding
budget on a bounded input domain). -/
def matMulSpecExecLayer (W : Fin d → Fin d → ℝ) (Λ : ℝ) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ j, (∑ k, |W k j|) ≤ Λ)
    (exec : (Fin s → Fin d → ℝ) → (Fin s → Fin d → ℝ)) (rnd : ℝ)
    (hclose : ∀ Y, dist (exec Y) (matMulCoord W Y) ≤ rnd) :
    ExecLayer (Fin s → Fin d → ℝ) where
  ideal := matMulCoord W
  exec := exec
  lip := Λ
  rnd := rnd
  lip_nonneg := hΛ0
  ideal_lip := by
    intro a b
    refine (dist_pi_le_iff (by positivity)).mpr (fun i => ?_)
    refine (dist_pi_le_iff (by positivity)).mpr (fun j => ?_)
    simp only [matMulCoord, Real.dist_eq, ← Finset.sum_sub_distrib, ← sub_mul]
    calc |∑ k, (a i k - b i k) * W k j|
        ≤ ∑ k, |a i k - b i k| * |W k j| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl (fun k _ => abs_mul _ _)
      _ ≤ ∑ k, dist a b * |W k j| := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          rw [← Real.dist_eq]; exact le_trans (dist_le_pi_dist (a i) (b i) k) (dist_le_pi_dist a b i)
      _ = dist a b * ∑ k, |W k j| := by rw [← Finset.mul_sum]
      _ ≤ dist a b * Λ := mul_le_mul_of_nonneg_left (hΛ j) dist_nonneg
      _ = Λ * dist a b := mul_comm _ _
  exec_close := hclose

end TLT
