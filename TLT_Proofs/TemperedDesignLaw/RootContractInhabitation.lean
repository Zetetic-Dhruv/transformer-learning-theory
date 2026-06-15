/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.TwoCertificateCrossover
import TLT_Proofs.TemperedDesignLaw.LiteralAttentionTempered
import TLT_Proofs.TemperedDesignLaw.MixtureCapacityDudley
import TLT_Proofs.Boundary.CascadeBorelDichotomy
import TLT_Proofs.Boundary.CascadeNullMeasurable
import TLT_Proofs.Tame.SingletonBadEventBorel

/-!
# Inhabitation of the tempered design law root-contract obligation fields

The root contract `TemperedDesignLawCertificate` bundles four legs of evidence, each a structure
whose fields are abstract mathematical obligations over generic carriers.  This file shows the
substantive obligation fields are inhabitable: for each one it proves the field's statement,
specialized to a concrete landed witness object, from the corresponding landed theorem.

The fields fall into three groups.

* **Capacity leg.**  The hard certificate is nonincreasing in sharpness
  (`hardBound_antitone_witness`, from the concrete leakage bound `hardBound_antitone`).

* **Measurability-cliff leg.**  On the common sample space `GhostPairs1` the soft and tame events
  are Borel (`softEvent_measurable_witness`, `hardTameEvent_measurable_witness`), the wild cascade
  event is non-Borel whenever the base score range is non-Borel
  (`hardWildEvent_nonBorel_witness`), it is null-measurable for every finite measure
  (`hardWildEvent_nullRepair_witness`), and the crossing cost is its measure mass
  (`crossingCost_eq_outerMass_witness`).

* **Hard-tame mathematical leg.**  At every positive sharpness the top-one reading of the literal
  tempered attention is its hard route (`exact_positive_beta_witness`), and a runtime margin check
  certifies the executed route equals the hard route (`routeStableCheck`, `routeStableCheck_sound`).

Two obligation fields are deliberately not inhabited here, because the mathematics they require is
not yet a landed theorem: the hard statistical certificate (a generalization bound composed from the
symbol-class arrangement capacity) and the expressivity grade (the depth/expert expressivity ladder).
-/

open MeasureTheory Set

noncomputable section

namespace TLT.TemperedDesignLaw

/-! ## Capacity leg -/

/-- **`hard_anti` inhabitation.**  The concrete hard certificate
`symbolBound + (k−1)·exp(−β·γ)·D` is nonincreasing in the sharpness `β`: the symbol-class capacity
`symbolBound` is sharpness invariant and the hardening leakage shrinks.  This is the obligation field
`CapacityProfile.hard_anti` at the tempered router's leakage certificate. -/
theorem hardBound_antitone_witness {k : ℕ} {symbolBound D γ : ℝ} (hk1 : 0 ≤ (k : ℝ) - 1)
    (hD : 0 ≤ D) (hγ : 0 ≤ γ) :
    Antitone (fun β : ℝ => symbolBound + ((k : ℝ) - 1) * Real.exp (-(β * γ)) * D) :=
  hardBound_antitone hk1 hD hγ

/-! ## Measurability-cliff leg

The three events live on the common sample space `GhostPairs1`, the size-one sample-pair space of
the empirical-process bad events.  The soft and tame events are concrete Borel bad events; the wild
event is the base-up MoE cascade bad event, which is non-Borel exactly when the base score range is
non-Borel, yet null-measurable for every finite measure. -/

/-- **`soft_finite_borel` inhabitation.**  The singleton-class bad event on a measurable target is
Borel.  Taken on `Set.univ`, this inhabits the obligation field
`MeasurabilityCliffLeg.soft_finite_borel` with a concrete Borel event on `GhostPairs1`. -/
theorem softEvent_measurable_witness :
    MeasurableSet (singletonBadEvent (Set.univ : Set ℝ)) :=
  Tame.singletonBadEvent_measurable Set.univ MeasurableSet.univ

/-- **`hard_tame_borel` inhabitation.**  Over the σ-compact parameter space `ℝ` the singleton-class
empirical-process bad event on the range of a continuous score map is Borel.  Taken at the identity
score, this inhabits `MeasurabilityCliffLeg.hard_tame_borel`: a genuine tame bad event whose
Borelness comes from σ-compactness of the parameter space, not from triviality of the target. -/
theorem hardTameEvent_measurable_witness :
    MeasurableSet (singletonBadEvent (Set.range (id : ℝ → ℝ))) :=
  Tame.singletonBadEvent_measurable_of_sigmaCompact (g := (id : ℝ → ℝ)) continuous_id

/-- **`hard_wild_nonBorel` inhabitation.**  Whenever the base score range is non-Borel, the depth-`L`
base-up MoE cascade bad event is non-Borel — at every depth.  This inhabits the obligation field
`MeasurabilityCliffLeg.hard_wild_nonBorel`; the non-Borel hypothesis is exactly the one the
attention non-Borel witness carries (classically, an analytic non-Borel subset of `ℝ`). -/
theorem hardWildEvent_nonBorel_witness {β : Type} [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] {width : ℕ}
    (M : Boundary.BaseUpMoECascadeCode β width) (L : ℕ)
    (h_non_borel : ¬ MeasurableSet (Set.range M.g)) :
    ¬ MeasurableSet (Boundary.cascadeBadEvent M L) :=
  fun h => h_non_borel ((Boundary.cascadeBadEvent_measurableSet_iff M L).mp h)

/-- **`hard_wild_nullRepair` inhabitation.**  For every finite measure and every routing depth the
cascade bad event is null-measurable — the non-Borel pathology is repaired by passing to the measure
completion.  This inhabits the obligation field `MeasurabilityCliffLeg.hard_wild_nullRepair`; no
non-Borel hypothesis is needed, because analyticity alone drives the repair. -/
theorem hardWildEvent_nullRepair_witness {β : Type} [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] {width : ℕ}
    (M : Boundary.BaseUpMoECascadeCode β width) (L : ℕ)
    {μ : Measure GhostPairs1} [IsFiniteMeasure μ] :
    NullMeasurableSet (Boundary.cascadeBadEvent M L) μ :=
  Boundary.universalRepair M L

/-- **`crossingCost_nonneg` inhabitation.**  Setting the crossing cost to the measure mass of the wild
event makes the obligation field `MeasurabilityCliffLeg.crossingCost_eq_outerMass` hold definitionally;
its companion `crossingCost_nonneg` is the genuine content, the nonnegativity of that mass. -/
theorem crossingCost_nonneg_witness {β : Type} [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β] {width : ℕ}
    (M : Boundary.BaseUpMoECascadeCode β width) (L : ℕ) (μ : Measure GhostPairs1) :
    0 ≤ μ.real (Boundary.cascadeBadEvent M L) :=
  measureReal_nonneg

/-! ## Hard-tame mathematical leg -/

/-- **`exact_positive_beta` inhabitation.**  At every positive sharpness the top-one reading of the
literal tempered attention (the `leastArgmax` of the softmax weights) is exactly its hard route: the
symbol channel does not see the temperature.  This is the obligation field
`HardTameMathLeg.exact_positive_beta`, the top-one reading at sharpness `β` against the hard route.
The witness is TorchLean's scaled-dot-product attention (`litAttnTempered`); the sharpness and its
sign enter as parameters because the router family bundles the nonnegativity of `β`. -/
theorem exact_positive_beta_witness (d nK : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hk : 0 < nK) (hβpos : 0 < β)
    (ρ : (litAttnTempered d nK β hβ).router.Ρ) (x : Fin d → ℝ) :
    leastArgmax (softWeights (litAttnTempered d nK β hβ) ρ x) hk
      = hardRoute (litAttnTempered d nK β hβ) hk ρ x :=
  litAttn_symbol_invariant d nK hβ hk hβpos ρ x

/-- **The runtime route-stability checker.**  Returns `true` exactly when twice the per-coordinate
score-rounding budget `b` is strictly below the route margin `γ`.  This is the `Bool`-valued
certificate of the obligation field `HardTameMathLeg.routeStableCheck`: a decidable runtime guard on
the executed route. -/
def routeStableCheck {X : Type*} [MeasurableSpace X] {k : ℕ} (A : TemperedRouterFamily X k)
    (hk : 0 < k) (ρ : A.router.Ρ) (b : ℝ) (x : X) : Bool :=
  decide (2 * b < gammaMargin A hk ρ x)

/-- **`routeStableCheck_sound` inhabitation.**  When the runtime checker passes, any executed scores
within the budget `b` of the exact scores have `leastArgmax` equal to the hard route.  This is the
obligation field `HardTameMathLeg.routeStableCheck_sound` wrapping the order-theoretic stability
lemma `leastArgmax_stable_of_half_margin` (via `TD7_route_stable_proof`) behind the decidable guard. -/
theorem routeStableCheck_sound {X : Type*} [MeasurableSpace X] {k : ℕ}
    (A : TemperedRouterFamily X k) (hk : 0 < k) (ρ : A.router.Ρ) (b : ℝ) (x : X)
    (sExec : Fin k → ℝ) (hb : ∀ i, |sExec i - A.router.score ρ x i| ≤ b)
    (hcheck : routeStableCheck A hk ρ b x = true) :
    leastArgmax sExec hk = hardRoute A hk ρ x :=
  TD7_route_stable_proof A hk ρ x sExec b hb (of_decide_eq_true hcheck)

/-! ## Capacity leg — the crossover-region fields

The capacity profile's monotonicity, binding-side, and crossover fields are inhabited at a concrete
pair of certificate shapes: a `β`-affine smooth certificate (the parameter-Lipschitz growth) and the
symbol-plus-leakage hard certificate.  The smooth side is genuinely increasing and the hard side
genuinely decreasing, so the crossover is an interior point, not a degenerate coincidence. -/

/-- A concrete `β`-affine smooth certificate (the parameter-Lipschitz growth shape). -/
def smoothWitness (base slope : ℝ) : ℝ → ℝ := fun β => base + slope * β

/-- A concrete hard certificate: sharpness-invariant symbol capacity plus hardening leakage. -/
def hardWitness (symbolBound D γ : ℝ) (k : ℕ) : ℝ → ℝ :=
  fun β => symbolBound + ((k : ℝ) - 1) * Real.exp (-(β * γ)) * D

/-- **`smooth_mono` inhabitation.**  The `β`-affine smooth certificate is monotone for nonnegative
slope (strictly increasing for positive slope — a non-degenerate witness). -/
theorem smoothWitness_mono {base slope : ℝ} (hslope : 0 ≤ slope) :
    Monotone (smoothWitness base slope) := by
  intro a b hab
  simp only [smoothWitness]
  have := mul_le_mul_of_nonneg_left hab hslope
  linarith

/-- The hard certificate is antitone, via the landed leakage monotonicity `hardBound_antitone`. -/
theorem hardWitness_anti {symbolBound D γ : ℝ} {k : ℕ} (hk1 : 0 ≤ (k : ℝ) - 1) (hD : 0 ≤ D)
    (hγ : 0 ≤ γ) : Antitone (hardWitness symbolBound D γ k) :=
  hardBound_antitone hk1 hD hγ

/-- **`betaStar_crosses` inhabitation.**  When the affine smooth certificate starts at or below the
hard certificate at `β = 0` and has overtaken it by `β₁`, the intermediate value theorem furnishes a
crossover sharpness in `[0, β₁]` at which the two certificate formulae agree. -/
theorem smoothWitness_hardWitness_crosses {base slope symbolBound D γ : ℝ} {k : ℕ}
    {β₁ : ℝ} (h0 : (0 : ℝ) ≤ β₁)
    (hstart : smoothWitness base slope 0 ≤ hardWitness symbolBound D γ k 0)
    (hover : hardWitness symbolBound D γ k β₁ ≤ smoothWitness base slope β₁) :
    ∃ betaStar ∈ Set.Icc (0 : ℝ) β₁,
      smoothWitness base slope betaStar = hardWitness symbolBound D γ k betaStar := by
  refine crossover_exists h0 ?_ ?_ hstart hover
  · exact (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  · refine (continuous_const.add ?_).continuousOn
    exact (continuous_const.mul
      (Real.continuous_exp.comp ((continuous_id.mul continuous_const).neg))).mul continuous_const

/-- **`smooth_binds_left` inhabitation.**  Below the crossover the smooth certificate is the binding
side, by downward closure of the smooth-binding region (`smoothBinding_downClosed`) at the concrete
monotone/antitone pair. -/
theorem smoothWitness_binds_left {base slope symbolBound D γ : ℝ} {k : ℕ}
    (hslope : 0 ≤ slope) (hk1 : 0 ≤ (k : ℝ) - 1) (hD : 0 ≤ D) (hγ : 0 ≤ γ)
    {betaStar β : ℝ}
    (hcross : smoothWitness base slope betaStar = hardWitness symbolBound D γ k betaStar)
    (hβ : β ≤ betaStar) :
    smoothWitness base slope β ≤ hardWitness symbolBound D γ k β :=
  smoothBinding_downClosed (smoothWitness_mono hslope) (hardWitness_anti hk1 hD hγ) hβ
    (le_of_eq hcross)

/-- **`hard_binds_right` inhabitation.**  From the crossover onward the hard certificate is the binding
side: monotone smooth and antitone hard sandwich the crossing equality. -/
theorem hardWitness_binds_right {base slope symbolBound D γ : ℝ} {k : ℕ}
    (hslope : 0 ≤ slope) (hk1 : 0 ≤ (k : ℝ) - 1) (hD : 0 ≤ D) (hγ : 0 ≤ γ)
    {betaStar β : ℝ}
    (hcross : smoothWitness base slope betaStar = hardWitness symbolBound D γ k betaStar)
    (hβ : betaStar ≤ β) :
    hardWitness symbolBound D γ k β ≤ smoothWitness base slope β :=
  calc hardWitness symbolBound D γ k β
      ≤ hardWitness symbolBound D γ k betaStar := hardWitness_anti hk1 hD hγ hβ
    _ = smoothWitness base slope betaStar := hcross.symm
    _ ≤ smoothWitness base slope β := smoothWitness_mono hslope hβ

/-- **A concrete crossover genuinely exists.**  At a non-degenerate configuration (unit slope, two
classes, unit leakage and margin) the smooth and hard certificates cross in `[0, 2]`: the sign
hypotheses of `smoothWitness_hardWitness_crosses` are discharged at honest numbers, so the crossover
field is inhabited unconditionally, not merely under assumption. -/
theorem concrete_crossover_exists :
    ∃ betaStar ∈ Set.Icc (0 : ℝ) 2,
      smoothWitness 0 1 betaStar = hardWitness 1 1 1 2 betaStar := by
  refine smoothWitness_hardWitness_crosses (by norm_num) ?_ ?_
  · simp only [smoothWitness, hardWitness]
    have : Real.exp (-((0 : ℝ) * 1)) = 1 := by rw [zero_mul, neg_zero, Real.exp_zero]
    rw [this]; norm_num
  · simp only [smoothWitness, hardWitness]
    have h : Real.exp (-((2 : ℝ) * 1)) ≤ 1 := by
      have := Real.exp_le_exp.mpr (show (-((2 : ℝ) * 1)) ≤ 0 by norm_num)
      rwa [Real.exp_zero] at this
    push_cast
    nlinarith [h]

/-! ## Capacity leg — the smooth certificate and its β-monotone structure

The soft (Dudley) certificate `smooth_cert : gap β ≤ smoothBound β` is the landed capacity bound
`paramStack_empiricalCapacity_le_dudley` at the β-indexed tempered stack: `gap β` the genuine empirical
capacity `empiricalCapacityReal R (fun θ x => ℓ (paramComp (Lsβ β) θ x)) S`, and `smoothBound β` the
genuine Dudley entropy integral at the parameter-Lipschitz constant `Lℓ · paramLipBound (Lsβ β)`. Its
β-monotonicity — the smooth certificate worsening with sharpness — reduces to the parameter-Lipschitz
bound being monotone in the per-layer moduli, established here for replicated stacks. The tempered
stack is the instance: `temperedParamLayer` contributes `paramLip = 2·β·Ksθ·P + Kvθ` and
`lip = 2·β·Ksy·P + Kvy`, both affine-increasing in `β`, so both telescoped bounds increase with `β`. -/

/-- The depth-`n` input-Lipschitz product of a replicated layer is monotone in the per-layer input
modulus (for a nonnegative modulus). -/
theorem inputLipProd_replicate_mono {Θ V : Type*} [PseudoMetricSpace Θ] [PseudoMetricSpace V]
    (L L' : ParamLayer Θ V) (hlip0 : 0 ≤ L.lip) (hlip : L.lip ≤ L'.lip) (n : ℕ) :
    inputLipProd (List.replicate n L) ≤ inputLipProd (List.replicate n L') := by
  induction n with
  | zero => simp [inputLipProd]
  | succ k ih =>
    simp only [List.replicate_succ, inputLipProd]
    exact mul_le_mul hlip ih (inputLipProd_nonneg _) (le_trans hlip0 hlip)

/-- **The smooth certificate's Lipschitz constant is monotone in the per-layer moduli.** The depth-`n`
parameter-Lipschitz bound of a replicated layer increases when both per-layer moduli increase: deeper
sharpness enlarges every layer's parameter and input modulus, hence the whole certificate constant
`paramLipBound` — and so the Dudley `smoothBound`. -/
theorem paramLipBound_replicate_mono {Θ V : Type*} [PseudoMetricSpace Θ] [PseudoMetricSpace V]
    (L L' : ParamLayer Θ V) (hp0 : 0 ≤ L.paramLip) (hp : L.paramLip ≤ L'.paramLip)
    (hlip0 : 0 ≤ L.lip) (hlip : L.lip ≤ L'.lip) (n : ℕ) :
    paramLipBound (List.replicate n L) ≤ paramLipBound (List.replicate n L') := by
  induction n with
  | zero => simp [paramLipBound]
  | succ k ih =>
    simp only [List.replicate_succ, paramLipBound]
    linarith [ih, mul_le_mul hp (inputLipProd_replicate_mono L L' hlip0 hlip k)
      (inputLipProd_nonneg _) (le_trans hp0 hp)]

/-- **The smooth (Dudley) certificate is monotone along a layer family with increasing moduli.**
Composing `dudleyCapBound_mono_L` (the bound grows with the parameter-Lipschitz constant) with
`paramLipBound_replicate_mono` (the depth-`n` telescope grows with the per-layer moduli): a depth-`n`
replicated stack whose per-layer parameter and input moduli both increase pays a larger Dudley capacity
price.  This is the `smooth_mono` mechanism for the genuine `dudleyCapBound` object, abstract over the
layer family — instantiating `L`, `L'` at `temperedParamLayer β`, `temperedParamLayer β'` (whose moduli
`2βKsθP+Kvθ` and `2βKsyP+Kvy` increase with `β`) yields the sharpness-monotonicity of the tempered
smooth certificate. -/
theorem dudleyCapBound_paramLipBound_replicate_mono {Θ V : Type*}
    [PseudoMetricSpace Θ] [PseudoMetricSpace V] (d m : ℕ) {R b Lℓ : ℝ}
    (hR : 0 ≤ R) (hb : 0 < b) (hLℓ : 0 ≤ Lℓ)
    (L L' : ParamLayer Θ V) (hp0 : 0 ≤ L.paramLip) (hp : L.paramLip ≤ L'.paramLip)
    (hlip0 : 0 ≤ L.lip) (hlip : L.lip ≤ L'.lip) (n : ℕ) :
    TLT.Capacity.dudleyCapBound d m R b (Lℓ * paramLipBound (List.replicate n L))
      ≤ TLT.Capacity.dudleyCapBound d m R b (Lℓ * paramLipBound (List.replicate n L')) :=
  TLT.Capacity.dudleyCapBound_mono_L d m hR hb
    (mul_le_mul_of_nonneg_left (paramLipBound_replicate_mono L L' hp0 hp hlip0 hlip n) hLℓ)

/-- **Concrete tempered corollary: the smooth certificate of the depth-`n` tempered stack worsens with
sharpness.** A one-application instantiation of `dudleyCapBound_paramLipBound_replicate_mono` at the
tempered mixture layer `temperedParamLayer β`, whose per-layer moduli `2βKsθP+Kvθ`, `2βKsyP+Kvy` increase
with `β`.  The four modulus facts: nonnegativity from the layer's own `paramLip_nonneg`/`lip_nonneg`
fields; monotonicity from `Ksθ, Ksy, P ≥ 0`.  Stated for `β ≤ β'` (both `≥ 0`) rather than as `Monotone`
because `temperedParamLayer` carries a `0 ≤ β` argument, which blocks a junk-free total `ℝ → ℝ` family. -/
theorem temperedStack_dudleyCapBound_mono
    {k : ℕ} [NeZero k] {Θ : Type*} [PseudoMetricSpace Θ]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d m : ℕ) {R b Lℓ : ℝ} (hR : 0 ≤ R) (hb : 0 < b) (hLℓ : 0 ≤ Lℓ)
    (score : Θ → V → Fin k → ℝ) (val : Θ → V → Fin k → V) (Ksθ Kvθ Ksy Kvy P : ℝ)
    (hKsθ : 0 ≤ Ksθ) (hKvθ : 0 ≤ Kvθ) (hKsy : 0 ≤ Ksy) (hKvy : 0 ≤ Kvy) (hP : 0 ≤ P)
    (hScoreθ : ∀ y θ θ', dist (score θ y) (score θ' y) ≤ Ksθ * dist θ θ')
    (hValθ : ∀ y θ θ', dist (val θ y) (val θ' y) ≤ Kvθ * dist θ θ')
    (hScorey : ∀ θ a c, dist (score θ a) (score θ c) ≤ Ksy * dist a c)
    (hValy : ∀ θ a c, dist (val θ a) (val θ c) ≤ Kvy * dist a c)
    (hValbd : ∀ θ y, (∑ i, ‖val θ y i‖) ≤ P)
    (n : ℕ) {β β' : ℝ} (hβ : 0 ≤ β) (hβ' : 0 ≤ β') (hββ' : β ≤ β') :
    TLT.Capacity.dudleyCapBound d m R b (Lℓ * paramLipBound (List.replicate n
        (temperedParamLayer β score val Ksθ Kvθ Ksy Kvy P hβ hKsθ hKvθ hKsy hKvy hP
          hScoreθ hValθ hScorey hValy hValbd)))
      ≤ TLT.Capacity.dudleyCapBound d m R b (Lℓ * paramLipBound (List.replicate n
        (temperedParamLayer β' score val Ksθ Kvθ Ksy Kvy P hβ' hKsθ hKvθ hKsy hKvy hP
          hScoreθ hValθ hScorey hValy hValbd))) := by
  refine dudleyCapBound_paramLipBound_replicate_mono d m hR hb hLℓ _ _ ?_ ?_ ?_ ?_ n
  · exact ParamLayer.paramLip_nonneg _
  · show 2 * β * Ksθ * P + Kvθ ≤ 2 * β' * Ksθ * P + Kvθ
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hββ') hKsθ) hP]
  · exact ParamLayer.lip_nonneg _
  · show 2 * β * Ksy * P + Kvy ≤ 2 * β' * Ksy * P + Kvy
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hββ') hKsy) hP]

end TLT.TemperedDesignLaw
