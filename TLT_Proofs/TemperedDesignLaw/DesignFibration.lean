/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.RouteMulticlassVC
import TLT_Proofs.TemperedDesignLaw.PolyTameness
import TLT_Proofs.TemperedDesignLaw.PolyDepthSeparation
import TLT_Proofs.TemperedDesignLaw.CascadePolyFunctor
import TLT_Proofs.TemperedDesignLaw.CertificateAssembly
import TLT_Proofs.Boundary.TemperatureCliffDepth

/-!
# The four design-law legs as fiberwise invariants of the cascade generator (R5)

The four legs of the tempered design law — capacity (generalization), expressivity/tameness, the
measurability cliff, and the numerical error window — are exhibited here as the **fiber invariants of a
fibration whose total space is the cascade generator `O`** (R3a's `cascadePFunctor`/`cascadeTree`) over
the design-parameter base `(d, L, k, deg, T)`.

The point of the fibration framing, against the `TemperedDesignLawCertificate` bundle: there the four
legs are *carried structures* whose fields may be assumed inputs. Here every fiber invariant is a
`Prop`-valued fact **discharged by an actual landed theorem at the parameter point**, with the cascade
generator (R3a) as the total space. A `DesignFiber` is therefore *not a free record*: each of its four
fields is a proposition that can only be inhabited by the corresponding landed theorem.

## The base, the total space, and the fiber

* **Base.** The design parameters `(d, L, k, deg, T)`: input dimension `d`, depth `L`, per-layer arity
  `k` (uniform here; the cascade code allows `Fin L → ℕ`), score degree `deg`, routing temperature `T`.
* **Total space (the generator `O`).** R3a's cascade polynomial functor: `cascadePFunctor (Fin (deg+1)) k`
  with the depth-`L` unfold `cascadeTree`, whose leaf addresses `cascadePath L (fun _ => k)` are the route
  traces. `designFibration_total_eq_generator` ties the fiber recovery back to this object.
* **Fiber.** `DesignFiber d L k deg T`: the four invariants at one parameter point, each a `Prop`:
  - `capacity_finite` — the single multiclass capacity number is finite (R7);
  - `expressivity_strict` — the depth grade strictly grows (`polyDepthGrade_ssubset_succ`);
  - `measurability_cliff` — soft Borel / hard non-Borel / null-repair, **at temperature `T`**
    (`Boundary.depthTemperatureCliff`);
  - `error_window` — the run sharpness is inside the certified exponential float cone (`NumericalLeg.cone`).

## The discharge map `designFiber`

`designFiber d L k deg T …` builds the fiber by **calling each landed theorem** on the cascade at those
parameters. No field is a free assumption: the cascade `polyCascadeCode` of depth `L`, arity `k`, on the
degree-`deg` polynomial router carrier `Fin d → ℝ` is the witness whose four invariants are R7 /
`polyDepthGrade_ssubset_succ` / `depthTemperatureCliff` / `NumericalLeg.cone`.

## A5 split

The capacity / expressivity / numerical fibers live at the **hard argmax limit** (the `T → ∞` route),
while the measurability fiber lives at finite temperature `T` (soft → hard). The hard-side fibration over
`(d, L, k, deg)` is closed here at full generality, and the temperature `T` is threaded into the
measurability fiber via `depthTemperatureCliff` (which is itself stated at temperature `τ = T`). The one
piece NOT closed in-turn is the **analytic coupling** that derives the hard-limit capacity/expressivity
invariants as the `T → ∞` limit of the soft-temperature objects on the *same* carrier (so that all four
legs are literally fibers of one temperature-parameterized family). That requires threading `T` through
the soft/hard cliff coherently on a shared score carrier, which is not buildable from the landed theorems
in-turn; it is reported as the precise task `R6` in the module docstring's closing note.
-/

open MeasureTheory Set
open TLT.ExpError
open scoped BigOperators

noncomputable section

namespace TLT.TemperedDesignLaw

universe u

/-! ## The cascade generator at parameters `(d, L, k, deg)`: a `CascadeRouterCode` of poly routers

The depth-`L`, uniform-arity-`k`, degree-`deg` polynomial-scored cascade on the carrier `Fin d → ℝ`.
Every layer is the degree-`deg` polynomial router `polyRouter d k deg` (R1's tameness carrier), so the
per-(layer, pair) score differences are linear in the degree-`deg` monomial features (`polySpan d deg`),
which is exactly the `hlin`/`W` data R7 consumes. This is the concrete generator whose capacity fiber is
discharged at the parameter point. -/

/-- **The degree-`deg` polynomial cascade generator** at depth `L`, uniform arity `k`, input dimension
`d`: a `CascadeRouterCode (Fin d → ℝ) L (fun _ => k)` whose every layer is `polyRouter d k deg`. -/
def polyCascadeCode (d L k deg : ℕ) : CascadeRouterCode (Fin d → ℝ) L (fun _ => k) where
  layer := fun _ℓ => polyRouter d k deg

/-- The per-(layer, pair) score-difference space for the polynomial cascade generator: the degree-`deg`
monomial span `polySpan d deg`, uniform across layers and pairs. -/
def polyCascadeW (d L k deg : ℕ) :
    (ℓ : Fin L) → Fin k × Fin k → Submodule ℝ ((Fin d → ℝ) → ℝ) :=
  fun _ℓ _p => polySpan d deg

/-- Each score-difference space is finite-dimensional (`polySpan_finiteDim`). -/
theorem polyCascadeW_finiteDim (d L k deg : ℕ) :
    ∀ ℓ p, FiniteDimensional ℝ (polyCascadeW d L k deg ℓ p) :=
  fun _ℓ _p => polySpan_finiteDim d deg

/-- **The cascade generator's per-(layer, pair) score differences are linear** in the degree-`deg`
features: each `x ↦ s_{p.2}(x) − s_{p.1}(x)` lies in `polySpan d deg`. This is `hlin` for R7, discharged
by `polyRouterScoreDiff_mem_polySpan` at each layer. -/
theorem polyCascadeCode_hlin (d L k deg : ℕ) :
    ∀ (ℓ : Fin L) (p : Fin k × Fin k) (ρ : ((polyCascadeCode d L k deg).layer ℓ).Ρ),
      (fun x => ((polyCascadeCode d L k deg).layer ℓ).score ρ x p.2
        - ((polyCascadeCode d L k deg).layer ℓ).score ρ x p.1) ∈ polyCascadeW d L k deg ℓ p :=
  fun _ℓ p ρ => polyRouterScoreDiff_mem_polySpan d k deg p ρ

/-! ## Fiber leg (a): the single multiclass capacity number is finite (R7)

The capacity fiber is the finiteness of the **single Natarajan-dimension number** of the cascade
generator's route-trace class. It is discharged by R7 `cascadeTraceClass_natarajanDim_lt_top` on
`polyCascadeCode`, with the `hlin`/`W` data supplied by `polyCascadeCode_hlin`/`polyCascadeW_finiteDim`. -/

/-- **The cascade generator's route-trace concept class** at parameters `(d, L, k, deg)`, with arity
positivity `hk : 0 < k`: `cascadeTraceClass (polyCascadeCode d L k deg) (fun _ => hk)` over the finite
multiclass label space `∀ _ : Fin L, Fin k`. The total object whose single capacity number R7 bounds. -/
def designTraceClass (d L k deg : ℕ) (hk : 0 < k) :
    ConceptClass (Fin d → ℝ) (∀ _ : Fin L, Fin k) :=
  cascadeTraceClass (polyCascadeCode d L k deg) (fun _ => hk)

/-- **(a) CAPACITY, DISCHARGED BY R7.** The single multiclass capacity number — the Natarajan dimension
of the cascade generator's route-trace class at `(d, L, k, deg)` — is finite. Produced by the landed
theorem `cascadeTraceClass_natarajanDim_lt_top` on `polyCascadeCode`, with the per-(layer, pair)
linearity discharged from R1's polynomial tameness (`polyCascadeCode_hlin`). General in `d, L, k, deg`
(arity `k > 0`). -/
theorem designCapacity_finite (d L k deg : ℕ) (hk : 0 < k) :
    NatarajanDim (Fin d → ℝ) (∀ _ : Fin L, Fin k) (designTraceClass d L k deg hk) < ⊤ :=
  cascadeTraceClass_natarajanDim_lt_top (polyCascadeCode d L k deg) (fun _ => hk)
    (polyCascadeW d L k deg) (polyCascadeW_finiteDim d L k deg) (polyCascadeCode_hlin d L k deg)

/-! ## Fiber leg (b): the expressivity grade strictly grows with depth

The expressivity fiber is the **strict depth separation** of the polynomial depth grade. It is
discharged by `polyDepthGrade_ssubset_succ`: the degree-`deg` (≥1) depth-`L` grade is a proper subset of
the depth-`(L+1)` grade. A collapsed (constant-in-depth) family cannot inhabit this `⊂`. -/

/-- **(b) EXPRESSIVITY, DISCHARGED BY `polyDepthGrade_ssubset_succ`.** The degree-`deg` (`deg ≥ 1`)
depth-`L` polynomial route grade is a proper subset of the depth-`(L+1)` grade:
`polyDepthGrade deg L ⊂ polyDepthGrade deg (L+1)`. Produced by the landed theorem
`polyDepthGrade_ssubset_succ`; this is the type-forcing tooth excluding a depth-collapsed generator.
General in `deg` (`deg ≥ 1`) and `L`. -/
theorem designExpressivity_strict (deg L : ℕ) (hdeg : 1 ≤ deg) :
    polyDepthGrade deg L ⊂ polyDepthGrade deg (L + 1) :=
  polyDepthGrade_ssubset_succ deg L hdeg

/-! ## Fiber leg (c): the measurability cliff, at routing temperature `T`

The measurability fiber is the **temperature cliff at temperature `T`**: the soft cascade ghost-gap
supremum (temperature-`T` softmax blend) is Borel-measurable, while the depth-`L` argmax cascade bad
event on the same tree is non-Borel yet null-measurable under any finite measure. It is discharged by
`Boundary.depthTemperatureCliff` at `τ = T`. The non-Borel base range `h_non_borel` is the genuine
external input of the landed cliff theorem (it depends on a continuous non-Borel-range witness `g`,
classically equivalent to the existence of an analytic non-Borel set in ℝ); it is a hypothesis of the
landed theorem, not a free fiber field. This is the leg where the temperature `T` is genuinely threaded
into the design law: at finite `T` the soft side is Borel, at the `T → ∞` argmax it is not. -/

/-- **(c) MEASURABILITY CLIFF, DISCHARGED BY `depthTemperatureCliff`, AT TEMPERATURE `T`.** For a
continuous non-Borel-range witness `g : β → ℝ` and routing temperature `T ≥ 0`, at depth `L` and under
any finite measure `μ`: the temperature-`T` soft cascade ghost-gap is measurable, the argmax cascade bad
event is non-Borel, and it stays null-measurable. The conjunction is produced by the landed theorem
`Boundary.depthTemperatureCliff` with `τ := T`. General in `β` (Polish/Borel/standard-Borel, nonempty),
`g`, `L`, `μ`, and the temperature `T`. -/
theorem designMeasurabilityCliff
    {β : Type} [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β]
    [StandardBorelSpace β] [Nonempty β]
    (T : ℝ) (hT : 0 ≤ T) (g : β → ℝ) (hg : Continuous g)
    (h_non_borel : ¬ MeasurableSet (Set.range g)) (L : ℕ)
    (μ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ))) [IsFiniteMeasure μ] :
    Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
        ⨆ θ : Boundary.CascadeParam (Boundary.witnessCascade g hg) L,
          Boundary.softCascadeMargin T g hg L θ (p.2 0)
            - Boundary.softCascadeMargin T g hg L θ (p.1 0)) ∧
      ¬ MeasurableSet (Boundary.cascadeBadEvent (Boundary.witnessCascade g hg) L) ∧
      NullMeasurableSet (Boundary.cascadeBadEvent (Boundary.witnessCascade g hg) L) μ :=
  Boundary.depthTemperatureCliff hT g hg h_non_borel L μ

/-! ## Fiber leg (d): the numerical error window (the certified exponential float cone)

The error fiber is the **certified-window cone bound**: at any run sharpness `β` inside the certified
float window `β ≤ betaMax S`, the relative rounding ratio satisfies `rrρ (β·S) ≤ 1/8`. It is discharged
by `NumericalLeg.cone` (the cone-boundary theorem `rrρ_le_iff_le_Tmax`), the same numerical leg the
`TemperedDesignLawCertificate` carries. -/

/-- **(d) ERROR WINDOW, DISCHARGED BY `NumericalLeg.cone`.** For a region `R` and a numerical leg
`N : NumericalLeg R` (the run sharpness `R.beta` inside the certified float window), the exponential cone
relative-rounding ratio is bounded: `rrρ (R.beta · R.S) ≤ 1/8`. Produced by the landed theorem
`NumericalLeg.cone`. General in `R`. -/
theorem designErrorWindow {R : RegionData} (N : NumericalLeg R) :
    rrρ (R.beta * R.S) ≤ 1 / 8 :=
  N.cone

/-! ## The fiber structure: the four invariants at one parameter point

`DesignFiber` is the fiber of the design-law fibration at a parameter point `(d, L, k, deg, T)`. Each of
its four fields is a `Prop`-valued invariant — **not free data**: the only way to inhabit a field is to
supply the proof produced by the corresponding landed theorem (R7 / `polyDepthGrade_ssubset_succ` /
`depthTemperatureCliff` / `NumericalLeg.cone`). The measurability leg additionally fixes a non-Borel
witness `g` and a finite measure `μ` (the external inputs of the cliff theorem); these are bundled into
the fiber's type so the cliff conjunction is a closed proposition. -/

/-- **The fiber of the design-law fibration at `(d, L, k, deg, T)`.** Carries the four design-law legs
as fiberwise invariants, each a `Prop` discharged by a landed theorem:

* `capacity_finite` — the single multiclass capacity number is finite (R7);
* `expressivity_strict` — the polynomial depth grade strictly grows (`polyDepthGrade_ssubset_succ`);
* `measurability_cliff` — soft Borel / hard non-Borel / null-repair at temperature `T`
  (`depthTemperatureCliff`), for the carried non-Borel witness `g` and finite measure `μ`;
* `error_window` — the run sharpness lies in the certified exponential float cone (`NumericalLeg.cone`).

No field is a free assumption: each is the proposition a landed theorem proves. The fiber is
parameterized by the arity positivity `hk`, the degree positivity `hdeg`, the temperature `T` (with
`0 ≤ T`), a region `R` with its numerical leg `N`, and the cliff witness data `(β, g, hg, h_non_borel, μ)`. -/
structure DesignFiber
    (d L k deg : ℕ) (hk : 0 < k) (hdeg : 1 ≤ deg)
    (T : ℝ)
    (R : RegionData) (N : NumericalLeg R)
    {β : Type} [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β]
    [StandardBorelSpace β] [Nonempty β]
    (g : β → ℝ) (hg : Continuous g) (h_non_borel : ¬ MeasurableSet (Set.range g))
    (μ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ))) [IsFiniteMeasure μ] : Prop where
  /-- (a) The single multiclass capacity number is finite (R7). -/
  capacity_finite :
    NatarajanDim (Fin d → ℝ) (∀ _ : Fin L, Fin k) (designTraceClass d L k deg hk) < ⊤
  /-- (b) The polynomial depth grade strictly grows with depth (`polyDepthGrade_ssubset_succ`). -/
  expressivity_strict : polyDepthGrade deg L ⊂ polyDepthGrade deg (L + 1)
  /-- (c) The temperature-`T` measurability cliff (`depthTemperatureCliff`): soft Borel ghost-gap,
  non-Borel argmax bad event, and its null-measurable repair. -/
  measurability_cliff :
    Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
        ⨆ θ : Boundary.CascadeParam (Boundary.witnessCascade g hg) L,
          Boundary.softCascadeMargin T g hg L θ (p.2 0)
            - Boundary.softCascadeMargin T g hg L θ (p.1 0)) ∧
      ¬ MeasurableSet (Boundary.cascadeBadEvent (Boundary.witnessCascade g hg) L) ∧
      NullMeasurableSet (Boundary.cascadeBadEvent (Boundary.witnessCascade g hg) L) μ
  /-- (d) The run sharpness lies in the certified exponential float cone (`NumericalLeg.cone`). -/
  error_window : rrρ (R.beta * R.S) ≤ 1 / 8

/-! ## The fibration: the discharge map `designFiber`

`designFiber` is the fibration's projection: at each parameter point it BUILDS the fiber by calling each
landed theorem on the cascade generator at those parameters. This is where the non-vacuity is realized —
every field is filled by the actual theorem, none by a free assumption. -/

/-- **THE DESIGN-LAW FIBRATION.** The fiber over the design-parameter point `(d, L, k, deg, T)`,
**built by discharging each of the four invariants from its landed theorem** on the cascade generator
`polyCascadeCode d L k deg`:

* `capacity_finite` := `designCapacity_finite` (R7 `cascadeTraceClass_natarajanDim_lt_top`);
* `expressivity_strict` := `designExpressivity_strict` (`polyDepthGrade_ssubset_succ`);
* `measurability_cliff` := `designMeasurabilityCliff` (`depthTemperatureCliff` at `τ = T`);
* `error_window` := `designErrorWindow` (`NumericalLeg.cone`).

Each field is a *theorem application*, not a free input — this is the fibration recovering the four legs
fiberwise from the generator. General in `d, L, k, deg` (with `k > 0`, `deg ≥ 1`), the temperature `T`
(`0 ≤ T`), the region `R` and its numerical leg `N`, and the cliff witness `(g, hg, h_non_borel, μ)`. -/
def designFiber
    (d L k deg : ℕ) (hk : 0 < k) (hdeg : 1 ≤ deg)
    (T : ℝ) (hT : 0 ≤ T)
    (R : RegionData) (N : NumericalLeg R)
    {β : Type} [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β]
    [StandardBorelSpace β] [Nonempty β]
    (g : β → ℝ) (hg : Continuous g) (h_non_borel : ¬ MeasurableSet (Set.range g))
    (μ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ))) [IsFiniteMeasure μ] :
    DesignFiber d L k deg hk hdeg T R N g hg h_non_borel μ where
  capacity_finite := designCapacity_finite d L k deg hk
  expressivity_strict := designExpressivity_strict deg L hdeg
  measurability_cliff := designMeasurabilityCliff T hT g hg h_non_borel L μ
  error_window := designErrorWindow N

/-! ## The total space IS the cascade generator `O` (R3a)

The fibration's total space is the cascade generator: R3a's polynomial functor `cascadePFunctor` with its
depth-`L` unfold `cascadeTree`, whose leaf addresses `cascadePath L (fun _ => k)` are the route traces.
The capacity fiber's underlying object `designTraceClass` is, **by definition**, a concept class valued
in the generator's leaf-address space `cascadePath L (fun _ => k)`, and the cardinality of that space is
exactly the leaf count of the R3a polynomial-functor tree. This is the fibration recovering the legs from
the generator: the same route-trace object that carries the capacity number IS R3a's leaf-address space. -/

/-- **THE FIBRATION'S LABEL SPACE IS R3a's GENERATOR LEAF-ADDRESS SPACE.** The multiclass label space of
the capacity fiber's route-trace class `designTraceClass d L k deg hk` — namely `∀ _ : Fin L, Fin k` — is
definitionally the cascade generator's leaf-address space `cascadePath L (fun _ => k)` (R3a's
`cascadePFunctor` unfold). The fiber's capacity object is therefore literally a concept class into the
generator's leaf addresses. -/
theorem designTraceClass_label_eq_cascadePath (d L k deg : ℕ) (hk : 0 < k) :
    (designTraceClass d L k deg hk : Set ((Fin d → ℝ) → (∀ _ : Fin L, Fin k)))
      = (designTraceClass d L k deg hk : Set ((Fin d → ℝ) → cascadePath L (fun _ => k))) :=
  rfl

/-- **`designFibration_total_eq_generator` — THE TOTAL SPACE IS THE CASCADE GENERATOR (R3a).** The
cardinality of the fibration's leaf-address (route-trace label) space at `(d, L, k)` equals the leaf
count of R3a's cascade polynomial-functor tree `cascadeTree label L`: for any symbol label,
`Fintype.card (cascadePath L (fun _ => k)) = leafCount (cascadeTree label L) = k ^ L`. This ties the
fibration's fiber object back to the generator `O = cascadePFunctor (Fin (deg+1)) k`: the route traces the
capacity fiber bounds are exactly the root-to-leaf paths of the unfolded polynomial functor, so the
total space of the fibration IS the cascade generator (R3a's `cascadePFunctor`/`cascadeTree`). General in
`L`, `k`, `deg`, and the symbol label. -/
theorem designFibration_total_eq_generator
    (L k deg : ℕ) (label : List (Fin k) → Fin (deg + 1)) :
    Fintype.card (cascadePath L (fun _ => k))
      = leafCount (cascadeTree label L) :=
  cascadePath_card_eq_leafCount k L label

/-- **The fibration's capacity object respects the generator's region count.** The label space of the
route-trace class has cardinality `∏ _ : Fin L, k = k ^ L`, the cascade generator's `∏ arity` region
count (R3a's `cascadePath_card`): the finite region count of the generator at `(L, k)`. This is the
cardinal the single capacity number (`designCapacity_finite`) is finite *relative to*. -/
theorem designFibration_regionCount (L k : ℕ) :
    Fintype.card (cascadePath L (fun _ => k)) = ∏ _i : Fin L, k :=
  cascadePath_card L (fun _ => k)

/-! ## The temperature coupling over the full `(d, L, k, deg, T)` base (hard-side closed; T-coupling A5)

The four legs are coupled in one fiber `designFiber d L k deg hk hdeg T …` indexed by the full design
base **including the temperature `T`**: the measurability leg lives at temperature `T` (soft side,
`depthTemperatureCliff` at `τ = T`), while capacity / expressivity / error live at the hard argmax limit
(`T → ∞`). The hard-side `(d, L, k, deg)` fibration is closed at full generality; the temperature is
threaded into the cliff leg. The theorem below records this coupling: at any `T ≥ 0` the four legs
co-inhabit one fiber. -/

/-- **THE TEMPERATURE COUPLING (hard side closed, cliff at temperature `T`).** At every temperature
`T ≥ 0`, the four design-law legs co-inhabit a single fiber `designFiber … T …`: capacity (R7),
expressivity (`polyDepthGrade_ssubset_succ`), and error (`NumericalLeg.cone`) at the hard argmax limit,
together with the measurability cliff at temperature `T` (`depthTemperatureCliff`). The fiber is produced
by `designFiber`, so each leg is discharged from its landed theorem. This is the coupled
`(d, L, k, deg, T)`-fibration restricted to the buildable (hard-side + cliff-at-`T`) part. -/
theorem designFiber_couples_over_temperature
    (d L k deg : ℕ) (hk : 0 < k) (hdeg : 1 ≤ deg)
    (T : ℝ) (hT : 0 ≤ T)
    (R : RegionData) (N : NumericalLeg R)
    {β : Type} [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β]
    [StandardBorelSpace β] [Nonempty β]
    (g : β → ℝ) (hg : Continuous g) (h_non_borel : ¬ MeasurableSet (Set.range g))
    (μ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ))) [IsFiniteMeasure μ] :
    Nonempty (DesignFiber d L k deg hk hdeg T R N g hg h_non_borel μ) :=
  ⟨designFiber d L k deg hk hdeg T hT R N g hg h_non_borel μ⟩

/-
## A5 SPLIT — task R6: the analytic `T → ∞` coupling on a shared score carrier

`designFiber` couples the four legs over `(d, L, k, deg, T)` with the measurability leg at temperature
`T` and the other three at the hard argmax limit. What is NOT closed here, and is genuinely not buildable
from the landed theorems in-turn, is the **analytic coupling** deriving the hard-limit capacity and
expressivity invariants as the `T → ∞` limit of the *same soft-temperature objects* the cliff leg uses,
on one shared score carrier — i.e. exhibiting `designTraceClass` (the route-trace class R7 bounds) as the
`T → ∞` limit of a soft-temperature trace class continuously deformed from `Boundary.softCascadeMargin`.

The only landed soft→hard argmax-limit fact is the single-layer
`RootContractInhabitation.exact_positive_beta_witness` (`leastArgmax (softWeights …) = hardRoute` for
every `β > 0`); there is no depth-`L` route-trace-class analogue coupling `cascadeTraceClass` to the soft
cascade. Building it requires:
  (i) a depth-`L` soft-temperature route-trace class on the *same* polynomial-score carrier as the cliff's
      `witnessCascade`/`softCascadeMargin`, and
  (ii) an argmax-limit theorem `softTraceClass T → cascadeTraceClass as T → ∞` lifting
      `exact_positive_beta_witness` through the depth-`L` cascade,
neither of which is among the landed theorems. This is reported as the precise follow-up task **R6**; it
must NOT be faked by making any fiber field a free assumption.
-/

end TLT.TemperedDesignLaw
