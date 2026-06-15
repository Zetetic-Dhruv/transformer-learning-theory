/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.RouteFactoredLoss
import TLT_Proofs.TemperedDesignLaw.Conjectures
import FLT_Proofs.Basic

/-!
# The margin-ramp surrogate bridge (TD16: the smooth/hard crossover via the learning route)

The hard certificate (S5) and the smooth/Dudley certificate (S1) must bound the **same** channel for
the single-gap TD16 crossover to close. S5 controls the **0-1 route loss** of the `leastArgmax` symbol
channel; S1's machinery only controls **output-Lipschitz** losses (`RouteFactoredLoss`), which the
discontinuous 0-1 loss is not. This file builds the standard Bartlett–Mendelson *margin-ramp surrogate*
of the routing 0-1 loss and proves it **dominates** the 0-1 route loss, packaged as an output-Lipschitz
`RouteFactoredLoss`. The smooth certificate, applied to this surrogate's `RouteFactoredLoss` capacity,
therefore upper-bounds the 0-1 route risk, the same quantity the hard certificate bounds.

The construction is the textbook clamped margin ramp `min 1 (max 0 (1 − t/γ))`
composed with the signed routing margin `s y − max_{i ≠ y} s i`, connected here to
this library's `leastArgmax`/`secondScore` routing primitives and the `RouteFactoredLoss` interface.

## Main results

- `marginRamp` + `marginRamp_nonneg` / `marginRamp_le_one` / `marginRamp_eq_one_of_nonpos` /
  `marginRamp_lipschitz`: the clamped ramp and its four defining properties (it clamps to
  `[0,1]`, equals `1` left of the boundary, and is `(1/γ)`-Lipschitz).
- `routeSignedMargin` + `routeSignedMargin_lipschitz`: the signed routing margin, `2`-Lipschitz in the
  score vector under the Pi sup norm.
- `zeroOne_le_marginRamp`: **THE DOMINATION.** `0-1 route loss ≤ surrogate`, tight (`= 1 = 1`) at the
  routing boundary.
- `routeRampSurrogateLoss`: the **output-Lipschitz `RouteFactoredLoss`** with Lipschitz
  constant `Lℓ = 2/γ`. This is the object S1's smooth/Dudley capacity bound consumes.
- `routeRisk01_le_surrogateRisk`: the **measure/integral** risk-domination: `∫ 0-1-route ≤ ∫ surrogate`.
  `routeRisk01_le_surrogateRisk_prob` discharges the surrogate's integrability automatically on a
  probability measure (the ramp is bounded in `[0,1]`). `routeRisk01_le_surrogateRisk_sample` is the
  finite-sample average form.

## References

- `RouteFactoredLoss.lean` (the `RouteFactoredLoss` structure + `distLoss` Lipschitz-proof idiom)
- `MeasurableScoreRouting.lean` (`leastArgmax`, `leastArgmax_is_maximizer`)
- `Conjectures.lean` (`secondScore`)
- `FLT_Proofs.Basic` (`zeroOneLoss`)
-/

open scoped BigOperators
open MeasureTheory

universe u

noncomputable section

namespace TLT.TemperedDesignLaw

/-! ## Part 1: the clamped margin ramp -/

/-- **The clamped margin ramp** (Bartlett–Mendelson surrogate at scale `γ`): the affine map `1 − t/γ`
clamped to `[0, 1]`. As a function of the margin `t`, it is `1` when the margin is non-positive (a routing
error, or a tie), decays linearly across the margin band `(0, γ)`, and is `0` once the margin exceeds `γ`. -/
def marginRamp (γ t : ℝ) : ℝ := min 1 (max 0 (1 - t / γ))

/-- The ramp is non-negative (the lower clamp). -/
theorem marginRamp_nonneg (γ t : ℝ) : 0 ≤ marginRamp γ t := by
  unfold marginRamp
  exact le_min (by norm_num) (le_max_left _ _)

/-- The ramp is at most `1` (the upper clamp). -/
theorem marginRamp_le_one (γ t : ℝ) : marginRamp γ t ≤ 1 := by
  unfold marginRamp
  exact min_le_left _ _

/-- **The ramp saturates at `1` on the error side.** For `γ > 0`, a non-positive margin (`t ≤ 0`, i.e. a
routing error or tie) forces `1 − t/γ ≥ 1`, so the ramp clamps to `1`. This is the half of the clamp that
makes the domination tight. -/
theorem marginRamp_eq_one_of_nonpos {γ t : ℝ} (hγ : 0 < γ) (ht : t ≤ 0) :
    marginRamp γ t = 1 := by
  unfold marginRamp
  have h1 : 1 ≤ 1 - t / γ := by
    have : t / γ ≤ 0 := div_nonpos_of_nonpos_of_nonneg ht (le_of_lt hγ)
    linarith
  rw [max_eq_right (le_trans (by norm_num) h1)]
  exact min_eq_left h1

/-- `x ↦ min a c` is `1`-Lipschitz in `a` (the dual of `abs_max_sub_max_le_abs`, recovered by negation). -/
theorem abs_min_sub_min_le_abs (a b c : ℝ) : |min a c - min b c| ≤ |a - b| := by
  have h := abs_max_sub_max_le_abs (-a) (-b) (-c)
  rw [max_neg_neg, max_neg_neg] at h
  calc |min a c - min b c| = |(-min a c) - (-min b c)| := by rw [← abs_neg]; ring_nf
    _ ≤ |(-a) - (-b)| := h
    _ = |a - b| := by rw [← abs_neg]; ring_nf

/-- The clamp `x ↦ min 1 (max 0 x)` is `1`-Lipschitz (min and max with constants are each `1`-Lipschitz). -/
theorem clamp01_lipschitz (a b : ℝ) :
    |min 1 (max 0 a) - min 1 (max 0 b)| ≤ |a - b| := by
  rw [min_comm 1 (max 0 a), min_comm 1 (max 0 b)]
  refine (abs_min_sub_min_le_abs (max 0 a) (max 0 b) 1).trans ?_
  rw [max_comm 0 a, max_comm 0 b]
  exact abs_max_sub_max_le_abs a b 0

/-- **The ramp is `(1/γ)`-Lipschitz** for `γ > 0`: it is the `1`-Lipschitz clamp composed with the affine
map `t ↦ 1 − t/γ` of slope `−1/γ`. -/
theorem marginRamp_lipschitz {γ : ℝ} (hγ : 0 < γ) (a b : ℝ) :
    |marginRamp γ a - marginRamp γ b| ≤ (1 / γ) * |a - b| := by
  unfold marginRamp
  refine (clamp01_lipschitz (1 - a / γ) (1 - b / γ)).trans ?_
  have hrw : (1 - a / γ) - (1 - b / γ) = (1 / γ) * (b - a) := by field_simp; ring
  rw [hrw, abs_mul, abs_sub_comm b a]
  gcongr
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / γ)]

/-! ## Part 2: the signed routing margin -/

/-- **The signed routing margin** of the score vector `s` at the true label `y`: the gap between the true
label's score and the best competing score `secondScore s y = max_{i ≠ y} s i`. It is `> 0` exactly when
the argmax route is `y` with slack, `≤ 0` when the route is wrong (or tied). -/
def routeSignedMargin {k : ℕ} (s : Fin k → ℝ) (y : Fin k) : ℝ := s y - secondScore s y

/-- **`Finset.sup'` is non-expansive.** If each coordinate moves by at most `C`, the `sup'` moves by at most
`C`. Proved by `Finset.sup'_le` in both directions: each `f b ≤ g b + |f b − g b| ≤ sup' g + C`. -/
theorem sup'_lipschitz {β : Type*} (T : Finset β) (h : T.Nonempty) (f g : β → ℝ) (C : ℝ)
    (hC : ∀ i ∈ T, |f i - g i| ≤ C) :
    |T.sup' h f - T.sup' h g| ≤ C := by
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · have hle : T.sup' h f ≤ T.sup' h g + C := by
      apply Finset.sup'_le h
      intro b hb
      have h1 : f b ≤ g b + |f b - g b| := by have := le_abs_self (f b - g b); linarith
      calc f b ≤ g b + |f b - g b| := h1
        _ ≤ T.sup' h g + C := by gcongr; exact Finset.le_sup' g hb; exact hC b hb
    linarith
  · have hle : T.sup' h g ≤ T.sup' h f + C := by
      apply Finset.sup'_le h
      intro b hb
      have h1 : g b ≤ f b + |f b - g b| := by have := neg_abs_le (f b - g b); linarith
      calc g b ≤ f b + |f b - g b| := h1
        _ ≤ T.sup' h f + C := by gcongr; exact Finset.le_sup' f hb; exact hC b hb
    linarith

/-- **Pi sup-norm coordinate bound.** Each coordinate gap is bounded by the (sup) norm of the difference.
On `Fin k → ℝ` the norm is the Pi sup norm `‖f‖ = maxᵢ |f i|`, so `|s i − s' i| ≤ ‖s − s'‖`. -/
theorem pi_pointwise_le {k : ℕ} (s s' : Fin k → ℝ) (i : Fin k) : |s i - s' i| ≤ ‖s - s'‖ := by
  have h := norm_le_pi_norm (s - s') i
  simp only [Pi.sub_apply, Real.norm_eq_abs] at h
  exact h

/-- **`secondScore` is `1`-Lipschitz** in `s` (Pi sup norm). The competing-index filter `{i ≠ y}` does not
depend on `s`, so both branches of the `dif` use the same non-emptiness witness; the `sup'` branch is
`1`-Lipschitz by `sup'_lipschitz`, the degenerate branch is the bare coordinate bound. -/
theorem secondScore_lipschitz {k : ℕ} (s s' : Fin k → ℝ) (y : Fin k) :
    |secondScore s y - secondScore s' y| ≤ ‖s - s'‖ := by
  unfold secondScore
  by_cases hne : (Finset.univ.filter (fun i => i ≠ y)).Nonempty
  · rw [dif_pos hne, dif_pos hne]
    exact sup'_lipschitz _ hne s s' (‖s - s'‖) (fun i _ => pi_pointwise_le s s' i)
  · rw [dif_neg hne, dif_neg hne]
    exact pi_pointwise_le s s' y

/-- **The signed routing margin is `2`-Lipschitz** in the score vector (Pi sup norm): the `s y` term is
`1`-Lipschitz and the `secondScore` term is `1`-Lipschitz, so their difference is `2`-Lipschitz. -/
theorem routeSignedMargin_lipschitz {k : ℕ} (s s' : Fin k → ℝ) (y : Fin k) :
    |routeSignedMargin s y - routeSignedMargin s' y| ≤ 2 * ‖s - s'‖ := by
  unfold routeSignedMargin
  have hsy : |s y - s' y| ≤ ‖s - s'‖ := pi_pointwise_le s s' y
  have hsec : |secondScore s y - secondScore s' y| ≤ ‖s - s'‖ := secondScore_lipschitz s s' y
  have key : (s y - secondScore s y) - (s' y - secondScore s' y)
      = (s y - s' y) - (secondScore s y - secondScore s' y) := by ring
  rw [key]
  calc |(s y - s' y) - (secondScore s y - secondScore s' y)|
      ≤ |s y - s' y| + |secondScore s y - secondScore s' y| := abs_sub _ _
    _ ≤ ‖s - s'‖ + ‖s - s'‖ := by gcongr
    _ = 2 * ‖s - s'‖ := by ring

/-! ## Part 3: the domination -/

/-- **The margin is non-positive when the route is wrong.** If the `leastArgmax` route differs from the
true label `y`, then `y`'s score is dominated by some competing score (the route's own), so the second-best
score is `≥ s y` and the signed margin is `≤ 0`. This is where the maximizer property of `leastArgmax`
enters and is what makes the domination tight at the boundary. -/
theorem routeSignedMargin_nonpos_of_ne {k : ℕ} (s : Fin k → ℝ) (hk : 0 < k) (y : Fin k)
    (hne : leastArgmax s hk ≠ y) : routeSignedMargin s y ≤ 0 := by
  unfold routeSignedMargin secondScore
  set m := leastArgmax s hk with hm
  have hmem : m ∈ Finset.univ.filter (fun i => i ≠ y) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
  have hfne : (Finset.univ.filter (fun i => i ≠ y)).Nonempty := ⟨m, hmem⟩
  rw [dif_pos hfne]
  have h1 : s m ≤ (Finset.univ.filter (fun i => i ≠ y)).sup' hfne s := Finset.le_sup' s hmem
  have h2 : s y ≤ s m := leastArgmax_is_maximizer s hk y
  linarith

/-- **THE DOMINATION.** For `γ > 0` and `k > 0`, the 0-1 loss of the `leastArgmax` route is dominated by the
margin-ramp surrogate of the signed routing margin:
`zeroOneLoss (leastArgmax s) y ≤ marginRamp γ (routeSignedMargin s y)`.

The inequality is tight at the routing boundary: when the route is correct the left side is `0` and the
right side is non-negative; when the route is wrong (or tied) both sides equal `1` (`zeroOneLoss = 1` by
definition and `marginRamp = 1` by `marginRamp_eq_one_of_nonpos`, since the margin is `≤ 0`). -/
theorem zeroOne_le_marginRamp {k : ℕ} (γ : ℝ) (hγ : 0 < γ) (s : Fin k → ℝ) (hk : 0 < k) (y : Fin k) :
    zeroOneLoss (Fin k) (leastArgmax s hk) y ≤ marginRamp γ (routeSignedMargin s y) := by
  unfold zeroOneLoss
  by_cases heq : leastArgmax s hk = y
  · rw [if_pos heq]; exact marginRamp_nonneg _ _
  · rw [if_neg heq, marginRamp_eq_one_of_nonpos hγ (routeSignedMargin_nonpos_of_ne s hk y heq)]

/-! ## Part 4: the output-Lipschitz `RouteFactoredLoss` (the S1 interface) -/

/-- **The route margin-ramp surrogate as a `RouteFactoredLoss`.** The loss is `marginRamp γ` composed with
the signed routing margin; the output space is the score vector `Fin k → ℝ` (Pi sup norm), the target space
is the label `Fin k`. The output-Lipschitz constant `Lℓ = 2/γ` is obtained by composing the
`(1/γ)`-Lipschitz ramp with the `2`-Lipschitz margin. This is the object S1's smooth/Dudley capacity bound
applies to, so the smooth certificate controls the 0-1 route risk through the domination above. -/
def routeRampSurrogateLoss (γ : ℝ) (hγ : 0 < γ) {k : ℕ} :
    RouteFactoredLoss (Fin k → ℝ) (Fin k) where
  loss s y := marginRamp γ (routeSignedMargin s y)
  Lℓ := 2 / γ
  Lℓ_nonneg := by positivity
  loss_lipschitz y p q := by
    calc |marginRamp γ (routeSignedMargin p y) - marginRamp γ (routeSignedMargin q y)|
        ≤ (1 / γ) * |routeSignedMargin p y - routeSignedMargin q y| :=
          marginRamp_lipschitz hγ _ _
      _ ≤ (1 / γ) * (2 * ‖p - q‖) := by
          gcongr
          exact routeSignedMargin_lipschitz p q y
      _ = (2 / γ) * ‖p - q‖ := by ring

/-- The surrogate `RouteFactoredLoss`'s output loss is exactly the pointwise surrogate (defeq witness). -/
theorem routeRampSurrogateLoss_loss (γ : ℝ) (hγ : 0 < γ) {k : ℕ} (s : Fin k → ℝ) (y : Fin k) :
    (routeRampSurrogateLoss γ hγ).loss s y = marginRamp γ (routeSignedMargin s y) := rfl

/-- The surrogate's output-Lipschitz constant is the genuine `2/γ`. -/
theorem routeRampSurrogateLoss_Lℓ (γ : ℝ) (hγ : 0 < γ) {k : ℕ} :
    (routeRampSurrogateLoss γ hγ (k := k)).Lℓ = 2 / γ := rfl

/-! ## Part 5: the risk consequence (the bridge statement)

The pointwise domination lifts to risks by monotonicity. We give the **measure/integral** form, which links
the smooth certificate's bound on the surrogate's `RouteFactoredLoss` capacity (S1) to the 0-1 route risk
that the hard certificate (S5) bounds, together with the finite-sample average form. -/

/-- **THE BRIDGE (measure form).** For any measure `μ` on the sample space, the expected 0-1 route loss is
at most the expected surrogate loss, by Bochner-integral monotonicity of the pointwise domination
`zeroOne_le_marginRamp`. The integrability hypotheses are the standard side conditions for the integral
inequality; `routeRisk01_le_surrogateRisk_prob` discharges them on a probability measure. -/
theorem routeRisk01_le_surrogateRisk
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} (γ : ℝ) (hγ : 0 < γ) (hk : 0 < k)
    (S : Ω → (Fin k → ℝ)) (Y : Ω → Fin k)
    (hint01 : Integrable (fun ω => zeroOneLoss (Fin k) (leastArgmax (S ω) hk) (Y ω)) μ)
    (hintSur : Integrable (fun ω => marginRamp γ (routeSignedMargin (S ω) (Y ω))) μ) :
    ∫ ω, zeroOneLoss (Fin k) (leastArgmax (S ω) hk) (Y ω) ∂μ
      ≤ ∫ ω, marginRamp γ (routeSignedMargin (S ω) (Y ω)) ∂μ := by
  refine integral_mono hint01 hintSur ?_
  intro ω
  exact zeroOne_le_marginRamp γ hγ (S ω) hk (Y ω)

/-- The surrogate loss is integrable on any probability measure, given AE-measurability: the ramp is bounded
in `[0, 1]`, so `Integrable.of_mem_Icc` applies on the finite measure. -/
theorem surrogate_integrable_of_prob
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {k : ℕ} (γ : ℝ) (S : Ω → (Fin k → ℝ)) (Y : Ω → Fin k)
    (hmeas : AEMeasurable (fun ω => marginRamp γ (routeSignedMargin (S ω) (Y ω))) μ) :
    Integrable (fun ω => marginRamp γ (routeSignedMargin (S ω) (Y ω))) μ := by
  apply Integrable.of_mem_Icc 0 1 hmeas
  filter_upwards with ω
  exact ⟨marginRamp_nonneg _ _, marginRamp_le_one _ _⟩

/-- The 0-1 route loss is integrable on any probability measure, given AE-measurability: it takes values in
`{0, 1} ⊆ [0, 1]`, so `Integrable.of_mem_Icc` applies. -/
theorem routeLoss01_integrable_of_prob
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {k : ℕ} (hk : 0 < k) (S : Ω → (Fin k → ℝ)) (Y : Ω → Fin k)
    (hmeas : AEMeasurable (fun ω => zeroOneLoss (Fin k) (leastArgmax (S ω) hk) (Y ω)) μ) :
    Integrable (fun ω => zeroOneLoss (Fin k) (leastArgmax (S ω) hk) (Y ω)) μ := by
  apply Integrable.of_mem_Icc 0 1 hmeas
  filter_upwards with ω
  unfold zeroOneLoss
  by_cases h : leastArgmax (S ω) hk = Y ω <;> simp [h]

/-- **THE BRIDGE (probability form, self-discharging).** On a probability measure, the expected 0-1 route
risk is at most the expected surrogate risk, with integrability discharged automatically from the boundedness
of both integrands (only AE-measurability of the two composites is required). This is the clean statement the
TD16 crossover consumes: the right-hand side is the population risk of the `routeRampSurrogateLoss` whose
`RouteFactoredLoss` capacity the smooth/Dudley certificate (S1) bounds. -/
theorem routeRisk01_le_surrogateRisk_prob
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {k : ℕ} (γ : ℝ) (hγ : 0 < γ) (hk : 0 < k)
    (S : Ω → (Fin k → ℝ)) (Y : Ω → Fin k)
    (hmeas01 : AEMeasurable (fun ω => zeroOneLoss (Fin k) (leastArgmax (S ω) hk) (Y ω)) μ)
    (hmeasSur : AEMeasurable (fun ω => marginRamp γ (routeSignedMargin (S ω) (Y ω))) μ) :
    ∫ ω, zeroOneLoss (Fin k) (leastArgmax (S ω) hk) (Y ω) ∂μ
      ≤ ∫ ω, marginRamp γ (routeSignedMargin (S ω) (Y ω)) ∂μ :=
  routeRisk01_le_surrogateRisk μ γ hγ hk S Y
    (routeLoss01_integrable_of_prob μ hk S Y hmeas01)
    (surrogate_integrable_of_prob μ γ S Y hmeasSur)

/-- **THE BRIDGE (finite-sample average form).** Over a sample of size `m`, the empirical 0-1 route risk is
at most the empirical surrogate risk, by `Finset.sum_le_sum` of the pointwise domination then dividing by
`m`. The integration-free witness that the domination lifts to risks. -/
theorem routeRisk01_le_surrogateRisk_sample {k : ℕ} (γ : ℝ) (hγ : 0 < γ) (hk : 0 < k)
    {m : ℕ} (S : Fin m → (Fin k → ℝ)) (Y : Fin m → Fin k) :
    (∑ i, zeroOneLoss (Fin k) (leastArgmax (S i) hk) (Y i)) / m
      ≤ (∑ i, marginRamp γ (routeSignedMargin (S i) (Y i))) / m := by
  have hsum : (∑ i, zeroOneLoss (Fin k) (leastArgmax (S i) hk) (Y i))
      ≤ (∑ i, marginRamp γ (routeSignedMargin (S i) (Y i))) :=
    Finset.sum_le_sum (fun i _ => zeroOne_le_marginRamp γ hγ (S i) hk (Y i))
  gcongr

end TLT.TemperedDesignLaw
