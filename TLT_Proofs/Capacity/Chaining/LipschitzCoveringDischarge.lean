/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import SLT.CoveringNumber
import TLT_Proofs.Capacity.Chaining.DudleyEntropyIntegralFiniteness
import TLT_Proofs.Capacity.Discretization.SymmetrizationBaseInvariantBound

/-!
# Discharging the Dudley side-conditions by a Lipschitz-image covering bound

The Dudley bound `capacityReal_le_dudley` carries three side-conditions on the value-vector set
`lossValueSet`: it is totally bounded, has bounded diameter, and has a finite entropy integral. For a
class that is a parameter-Lipschitz image of a Euclidean weight ball, all three follow from
boundedness and a volumetric covering bound.

The covering bound is supplied by the vendored volumetric estimate `coveringNumber_euclideanBall_le`
(a bound on the *external* covering number), bridged here to Mathlib's *internal*
`Metric.coveringNumber` — which the entropy machinery uses — through the keystone
`externalCoveringNumber_le_coveringNumber_ext` and Mathlib's factor-two internal/external comparison.
Crucially the bridge routes through the internal covering number, so the parameter-Lipschitz estimate
is only ever applied to net centres lying *inside* the ball: a class that is Lipschitz only on the
bounded weight ball — not globally — still admits the covering bound.

## Main results

- `externalCoveringNumber_le_coveringNumber_ext` — Mathlib's external covering number is at most the
  vendored covering number (every vendored net is a Mathlib cover).
-/

/-!
## References
- [26] Cor. 4.2.13 Euclidean-ball covering `(1+2R/ε)^d`; [25] Lem. 5.7 volume-ratio; Lipschitz-
  image covering `N(ε,f(S))≤N(ε/L,S)` (standard; weight-ball specialization [33]); [16] Dudley.
- Provenance: Vendored-glue (bridges the vendored [54] external covering number to Mathlib's
  internal one; the math is classical, the bridge is TLT engineering — not a new theorem).
-/

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace TLT.Capacity

/-- **Keystone bridge.** Every vendored external `eps`-net (centres anywhere, closed `dist`-balls) is a
Mathlib `eps`-cover, so Mathlib's external covering number at radius `eps.toNNReal` is at most the
vendored covering number at radius `eps`. This transports the vendored volumetric Euclidean-ball bound
into Mathlib's covering-number world. -/
theorem externalCoveringNumber_le_coveringNumber_ext {A : Type*} [PseudoMetricSpace A] {eps : ℝ}
    (heps : 0 ≤ eps) (s : Set A) :
    Metric.externalCoveringNumber eps.toNNReal s ≤ coveringNumber eps s := by
  refine le_sInf ?_
  rintro n ⟨t, hnet, rfl⟩
  have hcov : Metric.IsCover eps.toNNReal s (↑t : Set A) := by
    intro a ha
    have hmem : a ∈ ⋃ x ∈ t, Metric.closedBall x eps := hnet ha
    simp only [Set.mem_iUnion, Metric.mem_closedBall, exists_prop] at hmem
    obtain ⟨x, hx, hdist⟩ := hmem
    refine ⟨x, hx, ?_⟩
    show edist a x ≤ (eps.toNNReal : ℝ≥0∞)
    calc edist a x = ENNReal.ofReal (dist a x) := edist_dist a x
      _ ≤ ENNReal.ofReal eps := ENNReal.ofReal_le_ofReal hdist
      _ = (eps.toNNReal : ℝ≥0∞) := rfl
  calc Metric.externalCoveringNumber eps.toNNReal s ≤ (↑t : Set A).encard :=
        hcov.externalCoveringNumber_le_encard
    _ = (t.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard t

/-- A finite `ℕ∞` value bounded above (via `.untop`, cast to `ℝ`) by `K` bounds the real cast of the
`.toNat` of anything below it. The conversion glue between the `ℕ∞`-valued covering inequalities and
the real-valued volumetric bound. -/
lemma toNatCast_le_of_le_untop {a b : ℕ∞} (hab : a ≤ b) (hb : b ≠ ⊤) {K : ℝ}
    (hbK : ((b.untop hb : ℕ) : ℝ) ≤ K) : ((a.toNat : ℕ) : ℝ) ≤ K := by
  obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp hb
  rw [WithTop.untop_coe] at hbK
  have hle : a.toNat ≤ n := by
    rw [← ENat.toNat_coe n]
    exact ENat.toNat_le_toNat hab (WithTop.coe_ne_top)
  exact le_trans (by exact_mod_cast hle) hbK

/-- A finite `ℕ∞` value bounded above (as a real `.toNat`) by `K` bounds the real `.toNat` of anything
below it. -/
lemma toNat_real_le_of_le {a b : ℕ∞} (hab : a ≤ b) (hb : b ≠ ⊤) {K : ℝ}
    (hbK : ((b.toNat : ℕ) : ℝ) ≤ K) : ((a.toNat : ℕ) : ℝ) ≤ K :=
  le_trans (by exact_mod_cast ENat.toNat_le_toNat hab hb) hbK

/-- The internal Mathlib ball covering number is at most the vendored covering number at half the
radius, via Mathlib's factor-two internal/external comparison and the keystone bridge. -/
theorem coveringNumber_euclideanBall_le_slt {d : ℕ} {R δ : ℝ} (hδ : 0 < δ) :
    Metric.coveringNumber (Real.toNNReal δ) (euclideanBall R : Set (EuclideanSpace ℝ (Fin d)))
      ≤ coveringNumber (δ / 2) (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))) := by
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  have h2mul : (2 : ℝ≥0) * Real.toNNReal (δ / 2) = Real.toNNReal δ := by
    rw [show (2 : ℝ≥0) = Real.toNNReal 2 from (Real.toNNReal_ofNat 2).symm,
      ← Real.toNNReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1; ring
  have step := le_trans
    (Metric.coveringNumber_two_mul_le_externalCoveringNumber (Real.toNNReal (δ / 2))
      (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))))
    (externalCoveringNumber_le_coveringNumber_ext hδ2.le
      (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))))
  rwa [h2mul] at step

/-- The internal Mathlib ball covering number is finite (the ball is totally bounded). -/
theorem coveringNumber_euclideanBall_ne_top {d : ℕ} {R δ : ℝ} (hδ : 0 < δ) :
    Metric.coveringNumber (Real.toNNReal δ)
      (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))) ≠ ⊤ := by
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  have hfin : coveringNumber (δ / 2) (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))) ≠ ⊤ :=
    ne_top_of_lt (coveringNumber_lt_top_of_totallyBounded hδ2 (euclideanBall_totallyBounded R))
  exact (lt_of_le_of_lt (coveringNumber_euclideanBall_le_slt hδ) (lt_top_iff_ne_top.mpr hfin)).ne

/-- **Internal Euclidean-ball covering bound.** Mathlib's internal `Metric.coveringNumber` of the
weight ball admits the volumetric bound `(1 + 4R/δ)^d`, obtained from the vendored *external*
volumetric estimate through the keystone bridge and Mathlib's factor-two internal/external comparison.
The factor two doubles the radius constant (`2R → 4R`); the integrable `ε^{-1/2}` form is unchanged. -/
theorem coveringNumber_euclideanBall_toNat_le {d : ℕ} [Nonempty (Fin d)] {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ) :
    (((Metric.coveringNumber (Real.toNNReal δ)
        (euclideanBall R : Set (EuclideanSpace ℝ (Fin d)))).toNat : ℕ) : ℝ)
      ≤ (1 + 4 * R / δ) ^ d := by
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  have hfin : coveringNumber (δ / 2) (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))) ≠ ⊤ :=
    ne_top_of_lt (coveringNumber_lt_top_of_totallyBounded hδ2 (euclideanBall_totallyBounded R))
  refine toNatCast_le_of_le_untop (coveringNumber_euclideanBall_le_slt hδ) hfin
    ((coveringNumber_euclideanBall_le (ι := Fin d) hR hδ2).trans (le_of_eq ?_))
  rw [Fintype.card_fin]
  congr 1
  field_simp
  ring

/-- **Internal Lipschitz-image covering bound (on-domain Lipschitz).** If `f` is `L`-Lipschitz *on*
`s` (not necessarily globally), then the internal covering number of `f '' s` at radius `L·δ` is at
most that of `s` at radius `δ`. The internal cover keeps centres inside `s`, so the on-`s` estimate is
all that is needed — a map Lipschitz only on the bounded weight ball, not globally, still admits the
image bound. -/
theorem coveringNumber_image_le_of_lipschitzOn {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {f : X → Y} {s : Set X} {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hf : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ L * dist x y) :
    Metric.coveringNumber (Real.toNNReal (L * δ)) (f '' s)
      ≤ Metric.coveringNumber (Real.toNNReal δ) s := by
  simp only [Metric.coveringNumber]
  refine le_iInf fun C => le_iInf fun hCsub => le_iInf fun hCcov => ?_
  have himg : Metric.IsCover (Real.toNNReal (L * δ)) (f '' s) (f '' C) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hedist⟩ := hCcov hx
    refine ⟨f c, ⟨c, hc, rfl⟩, ?_⟩
    have hcs : c ∈ s := hCsub hc
    have hedist' : ENNReal.ofReal (dist x c) ≤ ENNReal.ofReal δ := by
      rw [← edist_dist]; exact hedist
    have hdistxc : dist x c ≤ δ := (ENNReal.ofReal_le_ofReal_iff hδ).mp hedist'
    show edist (f x) (f c) ≤ (Real.toNNReal (L * δ) : ℝ≥0∞)
    calc edist (f x) (f c) = ENNReal.ofReal (dist (f x) (f c)) := edist_dist _ _
      _ ≤ ENNReal.ofReal (L * δ) :=
          ENNReal.ofReal_le_ofReal (le_trans (hf x hx c hcs)
            (mul_le_mul_of_nonneg_left hdistxc hL))
      _ = (Real.toNNReal (L * δ) : ℝ≥0∞) := rfl
  exact iInf_le_of_le (f '' C) (iInf_le_of_le (Set.image_mono hCsub)
    (iInf_le_of_le himg (Set.encard_image_le f C)))

/-- Adjoining one point (the Dudley `0` anchor) increases the internal covering number by at most one:
extend any cover of `s` by the new point. -/
theorem coveringNumber_insert_le {X : Type*} [PseudoMetricSpace X] (ε : ℝ≥0) (a : X) (s : Set X) :
    Metric.coveringNumber ε (insert a s) ≤ Metric.coveringNumber ε s + 1 := by
  rcases eq_or_ne (Metric.coveringNumber ε s) ⊤ with h | h
  · simp [h]
  · obtain ⟨C, hCsub, _, hCcov, hCcard⟩ := Metric.exists_set_encard_eq_coveringNumber h
    have hcov' : Metric.IsCover ε (insert a s) (insert a C) := by
      intro y hy
      rw [Set.mem_insert_iff] at hy
      rcases hy with hya | hys
      · exact ⟨a, Set.mem_insert a C, by rw [hya]; simp⟩
      · obtain ⟨c, hc, hedist⟩ := hCcov hys
        exact ⟨c, Set.mem_insert_of_mem _ hc, hedist⟩
    calc Metric.coveringNumber ε (insert a s)
        ≤ (insert a C).encard :=
          hcov'.coveringNumber_le_encard (Set.insert_subset_insert hCsub)
      _ ≤ C.encard + 1 := Set.encard_insert_le C a
      _ = Metric.coveringNumber ε s + 1 := by rw [hCcard]

/-- **Square-root entropy affine envelope from a `+1` covering bound.** A covering bound
`(1 + C/ε)^d + 1` — the `+1` being the adjoined Dudley `0` anchor — gives the affine square-root
entropy envelope `√(log 2) + √(dC)·ε^{−1/2}`; the `log 2` absorbs the doubling `N + 1 ≤ 2N`. -/
lemma sqrtEntropy_le_affine_of_coveringNumber_succ_le {A : Type*} [PseudoMetricSpace A]
    {s : Set A} {C : ℝ} (hC : 0 ≤ C) {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hcov : ((Metric.coveringNumber ε.toNNReal s).toNat : ℝ) ≤ (1 + C / ε) ^ d + 1) :
    sqrtEntropy ε s ≤ Real.sqrt (Real.log 2) + Real.sqrt (d * C) * ε ^ (-(1 / 2) : ℝ) := by
  have hCε : (0 : ℝ) ≤ C / ε := div_nonneg hC hε.le
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hone : (1 : ℝ) ≤ (1 + C / ε) ^ d := by
    calc (1 : ℝ) = 1 ^ d := (one_pow d).symm
      _ ≤ (1 + C / ε) ^ d := by gcongr <;> linarith
  have hme : metricEntropy ε s ≤ Real.log 2 + d * (C / ε) := by
    rw [metricEntropy]
    rcases eq_or_ne (Metric.coveringNumber ε.toNNReal s).toNat 0 with h0 | h0
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]
      linarith [mul_nonneg (Nat.cast_nonneg d) hCε]
    · have h1 : (1 : ℝ) ≤ ((Metric.coveringNumber ε.toNNReal s).toNat : ℝ) :=
        Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr h0)
      calc Real.log ((Metric.coveringNumber ε.toNNReal s).toNat : ℝ)
          ≤ Real.log ((1 + C / ε) ^ d + 1) := Real.log_le_log (by linarith) hcov
        _ ≤ Real.log (2 * (1 + C / ε) ^ d) := Real.log_le_log (by positivity) (by linarith)
        _ = Real.log 2 + d * Real.log (1 + C / ε) := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        _ ≤ Real.log 2 + d * (C / ε) := by
            have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + C / ε by positivity)
            nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ (d : ℝ)), hlog]
  have hsub : Real.sqrt (Real.log 2 + d * (C / ε))
      ≤ Real.sqrt (Real.log 2) + Real.sqrt (d * (C / ε)) := by
    have key : Real.log 2 + d * (C / ε)
        ≤ (Real.sqrt (Real.log 2) + Real.sqrt (d * (C / ε))) ^ 2 := by
      have e1 := Real.sq_sqrt hlog2
      have e2 := Real.sq_sqrt (show (0 : ℝ) ≤ d * (C / ε) by positivity)
      nlinarith [Real.sqrt_nonneg (Real.log 2), Real.sqrt_nonneg ((d : ℝ) * (C / ε))]
    calc Real.sqrt (Real.log 2 + d * (C / ε))
        ≤ Real.sqrt ((Real.sqrt (Real.log 2) + Real.sqrt (d * (C / ε))) ^ 2) :=
          Real.sqrt_le_sqrt key
      _ = Real.sqrt (Real.log 2) + Real.sqrt (d * (C / ε)) := Real.sqrt_sq (by positivity)
  rw [sqrtEntropy]
  calc Real.sqrt (metricEntropy ε s)
      ≤ Real.sqrt (Real.log 2 + d * (C / ε)) := Real.sqrt_le_sqrt hme
    _ ≤ Real.sqrt (Real.log 2) + Real.sqrt (d * (C / ε)) := hsub
    _ = Real.sqrt (Real.log 2) + Real.sqrt (d * C) * ε ^ (-(1 / 2) : ℝ) := by
        rw [show (d : ℝ) * (C / ε) = (d * C) * ε⁻¹ by ring, Real.sqrt_mul (by positivity)]
        congr 1
        rw [Real.sqrt_inv, Real.rpow_neg hε.le, ← Real.sqrt_eq_rpow]

/-- A `ℕ∞` value below `b + 1` (with `b` finite, real-bounded by `K`) has real `.toNat` at most
`K + 1` — the insert-anchor bookkeeping. -/
lemma toNat_real_le_succ_of_le {a b : ℕ∞} (hab : a ≤ b + 1) (hb : b ≠ ⊤) {K : ℝ}
    (hbK : ((b.toNat : ℕ) : ℝ) ≤ K) : ((a.toNat : ℕ) : ℝ) ≤ K + 1 := by
  lift b to ℕ using hb with n
  have hab' : a ≤ ((n + 1 : ℕ) : ℕ∞) := by rw [Nat.cast_add, Nat.cast_one]; exact hab
  have hle : a.toNat ≤ n + 1 := ENat.toNat_le_of_le_coe hab'
  simp only [ENat.toNat_coe] at hbK
  calc ((a.toNat : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hle
    _ ≤ K + 1 := by push_cast; linarith

/-- The Mathlib covering number of a parameter-Lipschitz image of the weight ball is finite. -/
theorem coveringNumber_image_euclideanBall_ne_top {Y : Type*} [PseudoMetricSpace Y] {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → Y} {R L ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hf : ∀ x ∈ euclideanBall R, ∀ y ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        dist (f x) (f y) ≤ L * dist x y) :
    Metric.coveringNumber (Real.toNNReal ε)
      (f '' (euclideanBall R : Set (EuclideanSpace ℝ (Fin d)))) ≠ ⊤ := by
  have hLne : L ≠ 0 := hL.ne'
  have hh := coveringNumber_image_le_of_lipschitzOn (f := f)
    (s := (euclideanBall R : Set (EuclideanSpace ℝ (Fin d)))) (L := L) (δ := ε / L)
    hL.le (div_pos hε hL).le hf
  rw [show L * (ε / L) = ε from by rw [mul_comm]; exact div_mul_cancel₀ ε hLne] at hh
  exact (lt_of_le_of_lt hh
    (lt_top_iff_ne_top.mpr (coveringNumber_euclideanBall_ne_top (div_pos hε hL)))).ne

/-- **Lipschitz-image covering bound for the weight ball.** A map `L`-Lipschitz on the ball sends the
ball into a set whose covering number at radius `ε` is `≤ (1 + 4RL/ε)^d` — the chained internal
Lipschitz-image (centres in the ball, so on-ball Lipschitz suffices) and the internal Euclidean-ball
bound. -/
theorem coveringNumber_image_euclideanBall_toNat_le {Y : Type*} [PseudoMetricSpace Y] {d : ℕ}
    [Nonempty (Fin d)] {f : EuclideanSpace ℝ (Fin d) → Y} {R L ε : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (hε : 0 < ε)
    (hf : ∀ x ∈ euclideanBall R, ∀ y ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        dist (f x) (f y) ≤ L * dist x y) :
    (((Metric.coveringNumber (Real.toNNReal ε)
        (f '' (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))))).toNat : ℕ) : ℝ)
      ≤ (1 + 4 * R * L / ε) ^ d := by
  have hLne : L ≠ 0 := hL.ne'
  have hh := coveringNumber_image_le_of_lipschitzOn (f := f)
    (s := (euclideanBall R : Set (EuclideanSpace ℝ (Fin d)))) (L := L) (δ := ε / L)
    hL.le (div_pos hε hL).le hf
  rw [show L * (ε / L) = ε from by rw [mul_comm]; exact div_mul_cancel₀ ε hLne] at hh
  refine toNat_real_le_of_le hh (coveringNumber_euclideanBall_ne_top (div_pos hε hL)) ?_
  refine (coveringNumber_euclideanBall_toNat_le hR (div_pos hε hL)).trans (le_of_eq ?_)
  have hεne : ε ≠ 0 := hε.ne'
  congr 1
  field_simp

/-- The value-vector map: a weight to the vector of its losses on the sample points. -/
def valueVec {X : Type*} {d m : ℕ} (F : ParamSpace d → X → ℝ) (S : Fin m → X) :
    ParamSpace d → (Fin m → ℝ) := fun θ j => F θ (S j)

/-- **Finiteness of the Dudley entropy integral for a parameter-Lipschitz class.** If the value-vector
map is `L`-Lipschitz on the weight ball, the entropy integral of its loss-value set is finite — the
`+1` of the `0` anchor and the `log 2` doubling absorb into the affine envelope. -/
theorem entropyIntegralENNReal_lossValueSet_ne_top {X : Type*} {d m : ℕ} [Nonempty (Fin d)]
    {R : ℝ} (hR : 0 ≤ R) (F : ParamSpace d → X → ℝ) (S : Fin m → X) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        ∀ θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        dist (valueVec F S θ) (valueVec F S θ') ≤ L * dist θ θ')
    {D : ℝ} (hD : 0 < D) :
    entropyIntegralENNReal (lossValueSet (fun w : RealBall d R => F w.1) S) D ≠ ⊤ := by
  have hset : lossValueSet (fun w : RealBall d R => F w.1) S
      = insert 0 (valueVec F S '' (euclideanBall R : Set (EuclideanSpace ℝ (Fin d)))) := by
    rw [lossValueSet, Set.image_eq_range]
    rfl
  rw [hset]
  refine entropyIntegralENNReal_ne_top_of_sqrtEntropy_le_affine
    (c := Real.sqrt (Real.log 2)) (K := Real.sqrt ((d : ℝ) * (4 * R * L)))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hD (fun ε hε => ?_)
  refine sqrtEntropy_le_affine_of_coveringNumber_succ_le (by positivity : (0 : ℝ) ≤ 4 * R * L)
    hε.1 ?_
  exact toNat_real_le_succ_of_le (coveringNumber_insert_le (Real.toNNReal ε) 0 _)
    (coveringNumber_image_euclideanBall_ne_top hL hε.1 hlip)
    (coveringNumber_image_euclideanBall_toNat_le hR hL hε.1 hlip)

/-- The loss-value set sits inside the sup-norm ball of radius `b`: each loss coordinate is bounded by
`b`, and the adjoined `0` lies at the centre. -/
theorem lossValueSet_subset_closedBall {X : Type*} {d m : ℕ} {R : ℝ} (F : ParamSpace d → X → ℝ)
    {b : ℝ} (hb0 : 0 ≤ b) (hFb : ∀ θ x, |F θ x| ≤ b) (S : Fin m → X) :
    lossValueSet (fun w : RealBall d R => F w.1) S ⊆ Metric.closedBall (0 : Fin m → ℝ) b := by
  rw [lossValueSet]
  refine Set.insert_subset (Metric.mem_closedBall_self hb0) ?_
  rintro v ⟨w, rfl⟩
  rw [Metric.mem_closedBall, dist_pi_le_iff hb0]
  intro j
  simpa [Real.dist_eq] using hFb w.1 (S j)

/-- **Total boundedness of the loss-value set.** A uniformly bounded class has a loss-value set inside
a sup-norm ball, which is compact in the finite-dimensional coordinate space, hence totally bounded. -/
theorem totallyBounded_lossValueSet {X : Type*} {d m : ℕ} {R : ℝ} (F : ParamSpace d → X → ℝ)
    {b : ℝ} (hb0 : 0 ≤ b) (hFb : ∀ θ x, |F θ x| ≤ b) (S : Fin m → X) :
    TotallyBounded (lossValueSet (fun w : RealBall d R => F w.1) S) :=
  (ProperSpace.isCompact_closedBall (0 : Fin m → ℝ) b).totallyBounded.subset
    (lossValueSet_subset_closedBall F hb0 hFb S)

/-- **Diameter of the loss-value set.** It is at most `2b`, the diameter of the enclosing sup-norm
ball of radius `b`. -/
theorem diam_lossValueSet_le {X : Type*} {d m : ℕ} {R : ℝ} (F : ParamSpace d → X → ℝ)
    {b : ℝ} (hb0 : 0 ≤ b) (hFb : ∀ θ x, |F θ x| ≤ b) (S : Fin m → X) :
    Metric.diam (lossValueSet (fun w : RealBall d R => F w.1) S) ≤ 2 * b :=
  le_trans (Metric.diam_mono (lossValueSet_subset_closedBall F hb0 hFb S)
    Metric.isBounded_closedBall) (Metric.diam_closedBall hb0)

/-! ### Transfer to the vendored covering number / entropy (the side `capacityReal_le_dudley` uses)

The Dudley wrapper carries the *vendored* `entropyIntegralENNReal` (built on the vendored, external
`coveringNumber`), not Mathlib's internal one the work above discharges. Finiteness (`≠ ⊤`) is a
one-directional fact: it transfers along the free direction `vendored ≤ Mathlib-internal`, since every
finite internal Mathlib cover is a valid vendored net (internal centres are centres-anywhere). The
constructive image bound — which needs centre control and so internal covering — is done once on the
Mathlib side; only the scalar finiteness crosses the namespace gap. -/

/-- **The free direction.** Every finite internal Mathlib cover of `s` is a vendored `eps`-net, so the
vendored covering number is at most Mathlib's internal covering number. -/
theorem sltCoveringNumber_le_metricCoveringNumber {A : Type*} [PseudoMetricSpace A] {eps : ℝ}
    (heps : 0 ≤ eps) (s : Set A) :
    coveringNumber eps s ≤ Metric.coveringNumber eps.toNNReal s := by
  simp only [Metric.coveringNumber]
  refine le_iInf fun C => le_iInf fun hCsub => le_iInf fun hCcov => ?_
  rcases C.finite_or_infinite with hCfin | hCinf
  · have hnet : IsENet hCfin.toFinset eps s := by
      intro a ha
      obtain ⟨y, hy, hedist⟩ := hCcov ha
      rw [Set.mem_iUnion₂]
      refine ⟨y, hCfin.mem_toFinset.mpr hy, ?_⟩
      rw [Metric.mem_closedBall]
      have h : ENNReal.ofReal (dist a y) ≤ ENNReal.ofReal eps := by rw [← edist_dist]; exact hedist
      exact (ENNReal.ofReal_le_ofReal_iff heps).mp h
    calc coveringNumber eps s ≤ (hCfin.toFinset.card : ℕ∞) := coveringNumber_le_card hnet
      _ = C.encard := (Set.Finite.encard_eq_coe_toFinset_card hCfin).symm
  · rw [Set.Infinite.encard_eq hCinf]; exact le_top

/-- The vendored per-net entropy `metricEntropyOfNat` is just `log n` (its `n ≤ 1` clamp agrees with
`log 0 = log 1 = 0`). -/
lemma metricEntropyOfNat_eq_log (n : ℕ) : metricEntropyOfNat n = Real.log (n : ℝ) := by
  unfold metricEntropyOfNat
  split_ifs with hn
  · interval_cases n <;> simp
  · rfl

/-- The vendored metric entropy is `log` of the vendored covering number's `toNat` (the `⊤` arm gives
`log 0 = 0`). -/
lemma sltMetricEntropy_eq_log {A : Type*} [PseudoMetricSpace A] (eps : ℝ) (s : Set A) :
    _root_.metricEntropy eps s = Real.log ((ENat.toNat (coveringNumber eps s) : ℕ) : ℝ) := by
  unfold _root_.metricEntropy
  split
  · rename_i h; rw [h]; simp
  · rename_i n h; rw [metricEntropyOfNat_eq_log, h]; rfl

/-- **Pointwise square-root entropy comparison (finite regime).** Where Mathlib's internal covering
number is finite, the vendored square-root entropy is at most the Mathlib one — via the free
covering direction and `log`/`√` monotonicity. The `.toNat` `⊤ ↦ 0` quirk is avoided exactly because
the Mathlib covering number is finite. -/
lemma sltSqrtEntropy_le {A : Type*} [PseudoMetricSpace A] {eps : ℝ} (heps : 0 ≤ eps) {s : Set A}
    (hfin : Metric.coveringNumber eps.toNNReal s ≠ ⊤) :
    _root_.sqrtEntropy eps s ≤ sqrtEntropy eps s := by
  show Real.sqrt (_root_.metricEntropy eps s) ≤ Real.sqrt (metricEntropy eps s)
  apply Real.sqrt_le_sqrt
  rw [sltMetricEntropy_eq_log]
  unfold metricEntropy
  have hle : ENat.toNat (coveringNumber eps s)
      ≤ (Metric.coveringNumber eps.toNNReal s).toNat :=
    ENat.toNat_le_toNat (sltCoveringNumber_le_metricCoveringNumber heps s) hfin
  rcases Nat.eq_zero_or_pos (ENat.toNat (coveringNumber eps s)) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    rcases Nat.eq_zero_or_pos (Metric.coveringNumber eps.toNNReal s).toNat with h0' | hpos'
    · rw [h0', Nat.cast_zero, Real.log_zero]
    · exact Real.log_nonneg (Nat.one_le_cast.mpr hpos')
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)

/-- The Mathlib internal covering number of the loss-value set is finite at every scale (the
parameter-Lipschitz image plus the `0` anchor is totally bounded). -/
theorem metricCoveringNumber_lossValueSet_ne_top {X : Type*} {d m : ℕ} [Nonempty (Fin d)] {R : ℝ}
    (F : ParamSpace d → X → ℝ) (S : Fin m → X) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        ∀ θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        dist (valueVec F S θ) (valueVec F S θ') ≤ L * dist θ θ')
    {eps : ℝ} (heps : 0 < eps) :
    Metric.coveringNumber (Real.toNNReal eps)
      (lossValueSet (fun w : RealBall d R => F w.1) S) ≠ ⊤ := by
  have hset : lossValueSet (fun w : RealBall d R => F w.1) S
      = insert 0 (valueVec F S '' (euclideanBall R : Set (EuclideanSpace ℝ (Fin d)))) := by
    rw [lossValueSet, Set.image_eq_range]; rfl
  rw [hset]
  exact ne_top_of_le_ne_top
    (WithTop.add_ne_top.mpr ⟨coveringNumber_image_euclideanBall_ne_top hL heps hlip, ENat.one_ne_top⟩)
    (coveringNumber_insert_le (Real.toNNReal eps) 0 _)

/-- **Finiteness of the *vendored* entropy integral for a parameter-Lipschitz class** — the form
`capacityReal_le_dudley` consumes. The vendored entropy integral is dominated, pointwise on `(0,D]`
(where the Mathlib covering number is finite), by Mathlib's; the latter is finite by `FR8b`. -/
theorem sltEntropyIntegralENNReal_lossValueSet_ne_top {X : Type*} {d m : ℕ} [Nonempty (Fin d)]
    {R : ℝ} (hR : 0 ≤ R) (F : ParamSpace d → X → ℝ) (S : Fin m → X) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        ∀ θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        dist (valueVec F S θ) (valueVec F S θ') ≤ L * dist θ θ')
    {D : ℝ} (hD : 0 < D) :
    _root_.entropyIntegralENNReal (lossValueSet (fun w : RealBall d R => F w.1) S) D ≠ ⊤ := by
  refine ne_top_of_le_ne_top (entropyIntegralENNReal_lossValueSet_ne_top hR F S hL hlip hD) ?_
  unfold _root_.entropyIntegralENNReal entropyIntegralENNReal _root_.dudleyIntegrand
  refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun eps heps => ?_))
  exact ENNReal.ofReal_le_ofReal
    (sltSqrtEntropy_le heps.1.le (metricCoveringNumber_lossValueSet_ne_top F S hL hlip heps.1))

/-- **Dudley capacity bound for a parameter-Lipschitz class.** Discharging all three Dudley
side-conditions — total boundedness, diameter `≤ 2b`, and finiteness of the (vendored) entropy
integral — for a uniformly bounded class whose value-vector map is `L`-Lipschitz on the weight ball.
This removes those hypotheses from `capacityReal_le_dudley`, leaving boundedness and
parameter-Lipschitzness. -/
theorem capacityReal_le_dudley_of_lipschitz {X : Type*} {d m : ℕ} [Nonempty (Fin d)] (hm : 0 < m)
    {R : ℝ} (hR : 0 ≤ R) (F : ParamSpace d → X → ℝ) {b : ℝ} (hb : 0 < b)
    (hFb : ∀ θ x, |F θ x| ≤ b) (S : Fin m → X) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        ∀ θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        dist (valueVec F S θ) (valueVec F S θ') ≤ L * dist θ θ') :
    empiricalCapacityReal R F S
      ≤ (12 * Real.sqrt 2) * (1 / Real.sqrt m)
          * _root_.entropyIntegral (lossValueSet (fun θ : RealBall d R => F θ.1) S) (2 * b) :=
  capacityReal_le_dudley hm hR F hFb S (totallyBounded_lossValueSet F hb.le hFb S)
    (D := 2 * b) (by linarith) (diam_lossValueSet_le F hb.le hFb S)
    (sltEntropyIntegralENNReal_lossValueSet_ne_top hR F S hL hlip (D := 2 * b) (by linarith))

/-! ### Uniform (sample-independent) computable capacity bound

The Dudley capacity of `capacityReal_le_dudley_of_lipschitz` carries the sample-dependent entropy
integral. Bounding the square-root entropy by the *uniform* affine envelope `√(log2) + √(4dRL)·ε^{−1/2}`
(uniform because the covering constant `4RL` is sample-independent) turns it into a single closed
quantity in `(d,R,L,b,m)` — the per-sample capacity bound the computable certificate consumes. -/

/-- The affine envelope `c + K·ε^{−1/2}` has finite lower integral on `(0,D]` (the singularity
`ε^{−1/2}` is integrable since `−1/2 > −1`). -/
lemma affineLintegral_lt_top {c K D : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K) (hD : 0 < D) :
    (∫⁻ ε in Set.Ioc (0 : ℝ) D, ENNReal.ofReal (c + K * ε ^ (-(1 / 2) : ℝ))) < ⊤ := by
  have hrpow : IntegrableOn (fun ε : ℝ => ε ^ (-(1 / 2) : ℝ)) (Set.Ioc 0 D) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff hD).mpr (by norm_num)
  have hconst : IntegrableOn (fun _ : ℝ => c) (Set.Ioc 0 D) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hint : IntegrableOn (fun ε : ℝ => c + K * ε ^ (-(1 / 2) : ℝ)) (Set.Ioc 0 D) :=
    hconst.add (hrpow.const_mul K)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 D)] fun ε : ℝ => c + K * ε ^ (-(1 / 2) : ℝ) :=
    (ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all _ fun ε hε => add_nonneg hc (mul_nonneg hK (Real.rpow_nonneg hε.1.le _)))
  exact (hasFiniteIntegral_iff_ofReal hnonneg).mp hint.2

/-- The Mathlib internal covering bound for the loss-value set: `(1 + 4RL/ε)^d + 1` (the image bound
plus the `0` anchor). -/
theorem coveringNumber_lossValueSet_toNat_le {X : Type*} {d m : ℕ} [Nonempty (Fin d)] {R : ℝ}
    (hR : 0 ≤ R) (F : ParamSpace d → X → ℝ) (S : Fin m → X) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        ∀ θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        dist (valueVec F S θ) (valueVec F S θ') ≤ L * dist θ θ')
    {eps : ℝ} (heps : 0 < eps) :
    (((Metric.coveringNumber (Real.toNNReal eps)
        (lossValueSet (fun w : RealBall d R => F w.1) S)).toNat : ℕ) : ℝ)
      ≤ (1 + 4 * R * L / eps) ^ d + 1 := by
  have hset : lossValueSet (fun w : RealBall d R => F w.1) S
      = insert 0 (valueVec F S '' (euclideanBall R : Set (EuclideanSpace ℝ (Fin d)))) := by
    rw [lossValueSet, Set.image_eq_range]; rfl
  rw [hset]
  exact toNat_real_le_succ_of_le (coveringNumber_insert_le (Real.toNNReal eps) 0 _)
    (coveringNumber_image_euclideanBall_ne_top hL heps hlip)
    (coveringNumber_image_euclideanBall_toNat_le hR hL heps hlip)

/-- The vendored square-root entropy of the loss-value set is bounded by the uniform affine envelope. -/
lemma sltSqrtEntropy_lossValueSet_le_affine {X : Type*} {d m : ℕ} [Nonempty (Fin d)] {R : ℝ}
    (hR : 0 ≤ R) (F : ParamSpace d → X → ℝ) (S : Fin m → X) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        ∀ θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        dist (valueVec F S θ) (valueVec F S θ') ≤ L * dist θ θ')
    {eps : ℝ} (heps : 0 < eps) :
    _root_.sqrtEntropy eps (lossValueSet (fun w : RealBall d R => F w.1) S)
      ≤ Real.sqrt (Real.log 2) + Real.sqrt ((d : ℝ) * (4 * R * L)) * eps ^ (-(1 / 2) : ℝ) :=
  le_trans (sltSqrtEntropy_le heps.le (metricCoveringNumber_lossValueSet_ne_top F S hL hlip heps))
    (sqrtEntropy_le_affine_of_coveringNumber_succ_le (by positivity) heps
      (coveringNumber_lossValueSet_toNat_le hR F S hL hlip heps))

/-- **Uniform computable entropy bound.** The (vendored) entropy integral of the loss-value set at
scale `2b` is at most the affine envelope's integral — a single quantity in `(d,R,L,b)` independent of
the sample. -/
theorem entropyIntegral_lossValueSet_le {X : Type*} {d m : ℕ} [Nonempty (Fin d)] {R : ℝ}
    (hR : 0 ≤ R) (F : ParamSpace d → X → ℝ) (S : Fin m → X) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        ∀ θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        dist (valueVec F S θ) (valueVec F S θ') ≤ L * dist θ θ')
    {b : ℝ} (hb : 0 < b) :
    _root_.entropyIntegral (lossValueSet (fun w : RealBall d R => F w.1) S) (2 * b)
      ≤ (∫⁻ ε in Set.Ioc (0 : ℝ) (2 * b),
          ENNReal.ofReal (Real.sqrt (Real.log 2)
            + Real.sqrt ((d : ℝ) * (4 * R * L)) * ε ^ (-(1 / 2) : ℝ))).toReal := by
  refine ENNReal.toReal_mono (ne_of_lt (affineLintegral_lt_top (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (by linarith))) ?_
  unfold _root_.entropyIntegralENNReal _root_.dudleyIntegrand
  refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun ε hε => ?_))
  exact ENNReal.ofReal_le_ofReal (sltSqrtEntropy_lossValueSet_le_affine hR F S hL hlip hε.1)

/-- **Uniform computable capacity bound.** The empirical capacity of every sample is bounded by the
single closed quantity `12√2·(1/√m)·B`, with `B` the affine entropy integral — the per-sample bound
the computable certificate (`certified_executed_generalization_computable`) consumes. -/
theorem empiricalCapacityReal_le_computable {X : Type*} {d m : ℕ} [Nonempty (Fin d)] (hm : 0 < m)
    {R : ℝ} (hR : 0 ≤ R) (F : ParamSpace d → X → ℝ) {b : ℝ} (hb : 0 < b) (hFb : ∀ θ x, |F θ x| ≤ b)
    (S : Fin m → X) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ θ ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        ∀ θ' ∈ (euclideanBall R : Set (EuclideanSpace ℝ (Fin d))),
        dist (valueVec F S θ) (valueVec F S θ') ≤ L * dist θ θ') :
    empiricalCapacityReal R F S
      ≤ (12 * Real.sqrt 2) * (1 / Real.sqrt m)
          * (∫⁻ ε in Set.Ioc (0 : ℝ) (2 * b),
              ENNReal.ofReal (Real.sqrt (Real.log 2)
                + Real.sqrt ((d : ℝ) * (4 * R * L)) * ε ^ (-(1 / 2) : ℝ))).toReal :=
  le_trans (capacityReal_le_dudley_of_lipschitz hm hR F hb hFb S hL hlip)
    (mul_le_mul_of_nonneg_left (entropyIntegral_lossValueSet_le hR F S hL hlip hb) (by positivity))

end TLT.Capacity
