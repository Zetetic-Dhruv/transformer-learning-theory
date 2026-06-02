/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Capacity.SubGaussianMax
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Sub-Gaussian processes

A stochastic process `X` indexed by a pseudo-metric space is **sub-Gaussian** with parameter `σ` when
its increments have a sub-Gaussian moment generating function controlled by the index distance:
`E[exp(l·(X s − X t))] ≤ exp(l²σ²·d(s,t)²/2)`. This is the canonical hypothesis of the chaining
argument: it makes the increment `X s − X t` sub-Gaussian with proxy variance `σ²·d(s,t)²`, so that
over a finite net the expected maximum is controlled by the metric diameter.

## Main results

* `IsSubGaussianProcess` — the increment sub-Gaussian condition.
* `subGaussianProcessFiniteMax` — for a centered process and a finite index set `T` of diameter
  `≤ D`, `E[max_{t∈T} X t] ≤ σ · diam(T) · √(2 log |T|)`, the per-net estimate of a chaining bound,
  obtained from `subGaussianFiniteMax` with proxy `σ' = σ · diam(T)`.

## References

Boucheron, Lugosi and Massart, *Concentration Inequalities: A Nonasymptotic Theory of Independence*
(Oxford University Press, 2013), Chapter 13 (chaining and the generic chaining).
-/

open MeasureTheory ProbabilityTheory Real

noncomputable section

namespace TLT.Capacity

variable {Ω : Type*} [MeasurableSpace Ω] {A : Type*} [PseudoMetricSpace A]

/-- A process `X : A → Ω → ℝ` is sub-Gaussian with parameter `σ` if every increment `X s − X t` has
moment generating function bounded by `exp(l²σ²·d(s,t)²/2)` for all `l`. -/
def IsSubGaussianProcess (μ : Measure Ω) (X : A → Ω → ℝ) (σ : ℝ) : Prop :=
  ∀ s t : A, ∀ l : ℝ,
    ∫ ω, Real.exp (l * (X s ω - X t ω)) ∂μ ≤ Real.exp (l ^ 2 * σ ^ 2 * dist s t ^ 2 / 2)

/-- **Per-net maximal estimate for a centered sub-Gaussian process.** If `X` is sub-Gaussian with
parameter `σ`, is centered at a point `t₀ ∈ T` (so `X t₀ ≡ 0`), and `T` is a finite index set of at
least two points, then `E[max_{t∈T} X t] ≤ σ · diam(T) · √(2 log |T|)`.

This is the bound applied at one scale of a chaining decomposition: the increments `X t = X t − X t₀`
are sub-Gaussian with proxy variance `(σ·diam T)²`, so the maximal inequality `subGaussianFiniteMax`
applies with `σ' = σ · diam(T)`. -/
theorem subGaussianProcessFiniteMax {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : A → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ) (hX : IsSubGaussianProcess μ X σ)
    {T : Finset A} (hT : T.Nonempty) (hT_card : 2 ≤ T.card)
    (t₀ : A) (ht₀ : t₀ ∈ T) (hcenter : ∀ ω, X t₀ ω = 0)
    (hX_meas : ∀ t, Measurable (X t))
    (hX_int : ∀ t ∈ T, Integrable (X t) μ)
    (hX_int_exp : ∀ t ∈ T, ∀ l : ℝ, Integrable (fun ω => Real.exp (l * X t ω)) μ)
    (hdiam_pos : 0 < Metric.diam (T : Set A)) :
    ∫ ω, T.sup' hT (fun t => X t ω) ∂μ ≤
      σ * Metric.diam (T : Set A) * Real.sqrt (2 * Real.log T.card) := by
  set σ' := σ * Metric.diam (T : Set A) with hσ'_def
  have hσ' : 0 < σ' := mul_pos hσ hdiam_pos
  -- Each variable's cgf is bounded with proxy `σ'`.
  have h_cgf_bound : ∀ t ∈ T, ∀ l, cgf (X t) μ l ≤ l ^ 2 * σ' ^ 2 / 2 := by
    intro t ht l
    unfold ProbabilityTheory.cgf ProbabilityTheory.mgf
    have h_mgf_bound : ∫ ω, Real.exp (l * X t ω) ∂μ ≤ Real.exp (l ^ 2 * σ' ^ 2 / 2) := by
      have h1 : ∫ ω, Real.exp (l * X t ω) ∂μ = ∫ ω, Real.exp (l * (X t ω - X t₀ ω)) ∂μ := by
        congr 1; ext ω; simp only [hcenter ω, sub_zero]
      have hdist : dist t t₀ ^ 2 ≤ Metric.diam (T : Set A) ^ 2 := by
        refine sq_le_sq' ?_ (Metric.dist_le_diam_of_mem (Finset.finite_toSet T).isBounded ht ht₀)
        exact (neg_nonpos.mpr Metric.diam_nonneg).trans dist_nonneg
      have hstep : l ^ 2 * σ ^ 2 * dist t t₀ ^ 2 ≤ l ^ 2 * σ' ^ 2 := by
        calc l ^ 2 * σ ^ 2 * dist t t₀ ^ 2
            ≤ l ^ 2 * σ ^ 2 * Metric.diam (T : Set A) ^ 2 :=
              mul_le_mul_of_nonneg_left hdist (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          _ = l ^ 2 * σ' ^ 2 := by rw [hσ'_def, mul_pow]; ring
      rw [h1]
      exact (hX t t₀ l).trans (exp_le_exp.mpr (by linarith [hstep]))
    have h_mgf_pos : 0 < ∫ ω, Real.exp (l * X t ω) ∂μ := integral_exp_pos (hX_int_exp t ht l)
    calc Real.log (∫ ω, Real.exp (l * X t ω) ∂μ)
        ≤ Real.log (Real.exp (l ^ 2 * σ' ^ 2 / 2)) := Real.log_le_log h_mgf_pos h_mgf_bound
      _ = l ^ 2 * σ' ^ 2 / 2 := Real.log_exp _
  -- Apply the maximal inequality with proxy `σ'`; `set` has rewritten the goal to use `σ'`.
  exact subGaussianFiniteMax (μ := μ) (X := X) hσ' hT hT_card (fun i _ => hX_meas i) hX_int
    h_cgf_bound hX_int_exp

end TLT.Capacity
