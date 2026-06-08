/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Forward.ForwardEnvelope

/-!
# Per-operation `ExecLayer` instances: making the network envelope concrete

`ForwardEnvelope` reduces the executed-vs-ideal forward bound to per-layer data: an ideal Lipschitz
constant `Λ` and a uniform local rounding bound `rnd`. This file supplies concrete `ExecLayer` records
for forward-pass operations over the coordinate space `Fin n → ℝ` (the sup metric), so the network
envelope `execComp_envelope` and the risk transfer `execComp_risk_transfer` instantiate on real layers.

Two regimes appear, reflecting that fp32 rounding error is *relative* (proportional to magnitude):

- **Rounding-free selects (ReLU).** A componentwise `max (·) 0` introduces no arithmetic rounding, so
  its local bound is `rnd = 0`; it is `1`-Lipschitz in the sup metric. `reluExecLayer` is fully
  self-contained.
- **Arithmetic layers (linear / matmul).** A square linear map is Lipschitz with the operator
  ∞-norm — a uniform row absolute-sum bound `Λ` — proved here. Its rounding error is uniform only on a
  bounded input domain, so the executed map and its uniform bound `rnd` are taken as parameters
  (supplied, e.g., by the reduction-level `ie32_foldl_closed_envelope` on the input domain).
  `linearExecLayer` proves the Lipschitz side and threads the supplied rounding side.

Layer-normalization (Lipschitz only with a positive regularizer, constant scaling like `1/√ε`) and
dot-product attention (Lipschitz only on a bounded input domain) carry domain- or regularizer-dependent
constants in the `ExecLayer.lip` field; their explicit constants are not constructed here.

## Main results

- `reluExecLayer` — the ReLU layer: `1`-Lipschitz, rounding-free.
- `linearExecLayer` — a square linear layer: Lipschitz with the operator ∞-norm bound, with the
  executed map and its uniform rounding bound supplied.
-/

/-!
## References
- ∞-induced operator norm = max absolute row sum = Lipschitz constant of `x↦Wx`; [36] per-layer
  linear Lipschitz; [38][43] arithmetic-layer rounding datum (selects are rounding-free).
- Provenance: Classical-instantiation (concrete ReLU/linear ExecLayer records).
-/

namespace TLT

variable {n : ℕ}

/-- The ReLU layer as an `ExecLayer` over `Fin n → ℝ`: `1`-Lipschitz in the sup metric and
rounding-free (the componentwise `max (·) 0` select introduces no arithmetic error). -/
def reluExecLayer : ExecLayer (Fin n → ℝ) where
  ideal := fun f i => max (f i) 0
  exec := fun f i => max (f i) 0
  lip := 1
  rnd := 0
  lip_nonneg := zero_le_one
  ideal_lip := by
    intro a b
    rw [one_mul]
    refine (dist_pi_le_iff dist_nonneg).mpr (fun i => ?_)
    calc dist (max (a i) 0) (max (b i) 0)
        ≤ dist (a i) (b i) := by
          simp only [Real.dist_eq]; exact abs_max_sub_max_le_abs (a i) (b i) 0
      _ ≤ dist a b := dist_le_pi_dist a b i
  exec_close := by intro y; simp

/-- A square linear layer as an `ExecLayer` over `Fin n → ℝ`. The ideal map `x ↦ W x` is Lipschitz with
the operator ∞-norm bound `Λ` (a uniform bound on the row absolute sums `∑ⱼ |Wᵢⱼ|`), proved here. The
executed map and its uniform rounding bound `rnd` are supplied (e.g. the reduction-level rounding budget
on a bounded input domain). -/
def linearExecLayer (W : Fin n → Fin n → ℝ) (Λ : ℝ) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ i, (∑ j, |W i j|) ≤ Λ)
    (exec : (Fin n → ℝ) → (Fin n → ℝ)) (rnd : ℝ)
    (hclose : ∀ y, dist (exec y) (fun i => ∑ j, W i j * y j) ≤ rnd) :
    ExecLayer (Fin n → ℝ) where
  ideal := fun f i => ∑ j, W i j * f j
  exec := exec
  lip := Λ
  rnd := rnd
  lip_nonneg := hΛ0
  ideal_lip := by
    intro a b
    refine (dist_pi_le_iff (by positivity)).mpr (fun i => ?_)
    simp only [Real.dist_eq, ← Finset.sum_sub_distrib, ← mul_sub]
    calc |∑ j, W i j * (a j - b j)|
        ≤ ∑ j, |W i j * (a j - b j)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |W i j| * |a j - b j| := by simp only [abs_mul]
      _ ≤ ∑ j, |W i j| * dist a b := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          exact mul_le_mul_of_nonneg_left
            (by rw [← Real.dist_eq]; exact dist_le_pi_dist a b j) (abs_nonneg _)
      _ = (∑ j, |W i j|) * dist a b := by rw [Finset.sum_mul]
      _ ≤ Λ * dist a b := mul_le_mul_of_nonneg_right (hΛ i) dist_nonneg
  exec_close := hclose

end TLT
