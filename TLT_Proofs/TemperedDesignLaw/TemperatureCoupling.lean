/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.SymbolChannel
import TLT_Proofs.TemperedDesignLaw.MixtureLipschitz
import TLT_Proofs.TemperedDesignLaw.RouteMulticlassVC
import TLT_Proofs.TemperedDesignLaw.PolyDepthSeparation
import TLT_Proofs.TemperedDesignLaw.ZeroSharpness
import TLT_Proofs.Boundary.TemperatureCliffDepth
import TLT_Proofs.Boundary.CascadeBorelDichotomy
import TLT_Proofs.TemperedDesignLaw.MuxHierarchy

/-!
# Temperature coupling: the route fiber is temperature-invariant, the measure leg is not (R11)

The tempered design law's four legs (expressivity, capacity, numerics, measurability) live on a
two-parameter object indexed by **sharpness** `β` (equivalently temperature `T = 1/β`) and depth `L`.
This file proves the structural asymmetry that organizes the whole phase portrait:

* the **route** (the symbol channel: the per-layer `leastArgmax`, hence the route trace, hence its
  multiclass capacity and its expressivity grade) is **temperature-invariant** for every `β > 0`;
* only the **measure/margin leg** (the soft-blend margin and the Borel/non-Borel dichotomy of the
  bad event) moves with `T` — the cliff.

This is the **measurability-as-base** picture: `T` is the base over which the four legs co-fiber,
and it moves only the measure-phase; the route is the constant fiber.

## The obligations (each `=` at maximal generality, `β > 0`)

* `KU1_routeInvariance` — per-layer route invariance for a general `FiniteScoreRouterCode` and `0 < β`:
  `leastArgmax (softWeights A ρ x) hk = leastArgmax (A.router.score ρ x) hk`. Proved via the explicit
  `β`-bridge (`softWeights_eq_softmax_smul`, then `leastArgmax_comp_strictMono` to strip `β`, then the
  softmax rank-preservation `isLeastArgmax_softmax_iff` lifted to a `leastArgmax` equality by
  `isLeastArgmax_unique`).
* `KU2_softCascadeTrace_eq` — the depth-lift: `softCascadeTrace = cascadeTrace` for `0 < β`, by a
  per-layer state-agreement argument over the depth-`L` cascade.
* `KU3_softCascadeTraceClass_eq` — the route classes coincide: `softCascadeTraceClass = cascadeTraceClass`.
* `KU4_capacity_T_invariant` / `KU4_expressivity_T_invariant` — the capacity (R7 Natarajan dimension)
  and expressivity (poly-depth grade ladder) legs are carried unchanged by the soft route class.
* `KU5_measureLeg_T_dependent` — the cliff at `τ = T` is the `T`-dependent measure phase.
* `KU6_measurabilityAsBase` — the assembly: the route fiber is `T`-invariant while the measure leg is
  `T`-dependent, on the co-located carriers (capacity/expressivity on `CascadeRouterCode`, the cliff on
  `witnessCascade`; see the A5 note on `UK1` below for why these stay on distinct carriers).

## `UK1` (carrier mismatch — A5-split, not faked here)

The cliff's `softCascadeMargin` lives on `witnessCascade g hg : BaseUpMoECascadeCode β 2` (a recursive
mixture-of-experts cascade with genuine inter-layer state passing through `CascadeParam`), whereas the
capacity/expressivity legs live on `CascadeRouterCode X L k` (a depth-`L` family of independent
per-layer argmax routers on a shared input — no inter-layer state). These are genuinely different
carriers, co-located by R5 but not unified. `KU6` is therefore the co-fibering of the legs **on their
co-located carriers**; forcing a single carrier requires route-invariance on the witness carrier and an
explicit carrier coupling, which is split out as a separate task (couple `witnessCascade` ↔ the capacity
carrier under temperature-invariant routing). It is **not** faked here.
-/

open scoped BigOperators
open MeasureTheory

universe u

noncomputable section

namespace TLT.TemperedDesignLaw

variable {X : Type u} [MeasurableSpace X]

/-! ## KU1: per-layer route invariance (the spine primitive)

For a general tempered router family at any positive sharpness, the top-1 reading of the soft mixture
weights is the hard route. The proof is the explicit `β`-bridge the URS prescribes, resolving the
`softmaxWeight`-vs-`softWeights(β)` caveat in-kernel: `softWeights = softmax (β • score)` is the softmax
of the `β`-scaled scores, whereas the shipped rank-preservation lemma `isLeastArgmax_softmax_iff` is
stated for the unscaled `softmaxWeight A = softmax (score)`. The `β`-scaling is stripped by the
strict-monotone post-composition `leastArgmax_comp_strictMono` (`φ = β • ·`, strictly monotone since
`β > 0`), landing exactly on the unscaled softmax, after which the rank-preservation iff applies. -/

/-- **KU1v — the bare-vector `β`-bridge atom.** For any score vector `v : Fin k → ℝ` and any sharpness
`β > 0`, the unscaled softmax of the `β`-scaled vector has the same `leastArgmax` as `v`: strip `β`
(strict-mono, since `β > 0`) then apply rank-preservation through `leastArgmax_comp_strictMono`. This is
the generic atom underlying every route-invariance statement in this file — it depends only on the
score vector `v` and the positive scalar `β`, not on any router/cascade structure. The proof is the
refactor of the original `leastArgmax_softmax_smul_eq`, which only ever used `A.router.score ρ x` as an
opaque `Fin k → ℝ` and `A.β` as the scalar. The hypothesis `0 < β` is load-bearing: at `β = 0` the
softmax of `0 • v` is uniform and the `leastArgmax` collapses to `⟨0, hk⟩` regardless of `v`
(cf. `KU1_fails_at_zero`). -/
theorem leastArgmax_softmax_smul_vec {k : ℕ} (v : Fin k → ℝ) (hk : 0 < k) {β : ℝ}
    (hβ : 0 < β) :
    leastArgmax (softmax (β • v)) hk = leastArgmax v hk := by
  -- `softmax (β • v) i = exp (β • v i) / Z`; viewed as `φ ∘ v` with `φ t = exp (β t) / Z`.
  set Z := ∑ j, Real.exp (β * v j) with hZ_def
  have hZ : (0 : ℝ) < Z :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  -- `φ t = exp (β t) / Z` is strictly monotone for `β > 0`, `Z > 0`.
  have hφ : StrictMono (fun t : ℝ => Real.exp (β * t) / Z) := by
    intro a b hab
    dsimp only
    have h2 : Real.exp (β * a) < Real.exp (β * b) :=
      Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hab hβ)
    gcongr
  -- `softmax (β • v) = φ ∘ v`, definitionally.
  have hsm : softmax (β • v)
      = fun i => (fun t : ℝ => Real.exp (β * t) / Z) (v i) := by
    funext i
    simp only [softmax, Pi.smul_apply, smul_eq_mul, hZ_def]
  rw [hsm]
  exact leastArgmax_comp_strictMono _ hk hφ

/-- **The `β`-bridge atom (router-family form).** The unscaled softmax of the `β`-scaled scores has the
same `leastArgmax` as the raw scores. Now a thin corollary of the bare-vector atom
`leastArgmax_softmax_smul_vec` applied to `v = A.router.score ρ x`, `β = A.β`. -/
theorem leastArgmax_softmax_smul_eq {k : ℕ} (A : TemperedRouterFamily X k) (hk : 0 < k)
    (hβ : 0 < A.β) (ρ : A.router.Ρ) (x : X) :
    leastArgmax (softmax (A.β • A.router.score ρ x)) hk
      = leastArgmax (A.router.score ρ x) hk :=
  leastArgmax_softmax_smul_vec (A.router.score ρ x) hk hβ

/-- **KU1 (per-layer route invariance, `0 < β`).** For a general finite score router at any positive
sharpness, the `leastArgmax` of the tempered softmax (mixture) weights equals the `leastArgmax` of the
raw scores: the symbol channel does not see the temperature. The statement is `=` at maximal generality
(any `X`, any arity `k`, any router, any `β > 0`); the hypothesis `0 < A.β` is load-bearing — at
`A.β = 0` the weights are uniform and the `leastArgmax` collapses to `⟨0, hk⟩` (`leastArgmax_softWeights_zero`).

Proof route (the URS spine, bridge resolved explicitly):
`softWeights = softmax (β • score)` (`softWeights_eq_softmax_smul`) `→` strip `β` via
`leastArgmax_comp_strictMono` `→` softmax rank-preservation (`isLeastArgmax_softmax_iff` lifted to a
`leastArgmax` equality through `isLeastArgmax_unique`, packaged as `top1_softmax_eq_argmax`). -/
theorem KU1_routeInvariance {k : ℕ} (A : TemperedRouterFamily X k) (hk : 0 < k)
    (hβ : 0 < A.β) (ρ : A.router.Ρ) (x : X) :
    leastArgmax (softWeights A ρ x) hk = leastArgmax (A.router.score ρ x) hk := by
  rw [softWeights_eq_softmax_smul]
  exact leastArgmax_softmax_smul_eq A hk hβ ρ x

/-- KU1 packaged against `hardRoute` (the route-code form), for downstream use. Identical content to
`KU1_routeInvariance` via `hardRoute_eq_leastArgmax`. -/
theorem KU1_routeInvariance_hardRoute {k : ℕ} (A : TemperedRouterFamily X k) (hk : 0 < k)
    (hβ : 0 < A.β) (ρ : A.router.Ρ) (x : X) :
    leastArgmax (softWeights A ρ x) hk = hardRoute A hk ρ x := by
  rw [KU1_routeInvariance A hk hβ ρ x, hardRoute_eq_leastArgmax]

/-- The KU1 bridge bites only at `β > 0`: the explicit `β = 0` boundary witness (`ZeroSharpness`). At
`β = 0` the soft route collapses to `⟨0, hk⟩` regardless of the scores, so the route-invariance `=`
is **false** in general at `β = 0` — this records that `0 < β` in `KU1_routeInvariance` is not a
decorative hypothesis. -/
theorem KU1_fails_at_zero {k : ℕ} [NeZero k] (A : TemperedRouterFamily X k) (hβ0 : A.β = 0)
    (hk : 0 < k) (ρ : A.router.Ρ) (x : X) :
    leastArgmax (softWeights A ρ x) hk = ⟨0, hk⟩ :=
  leastArgmax_softWeights_zero A hβ0 hk ρ x

/-! ## KU2: the depth-lift (M-Pipeline) — `softCascadeTrace = cascadeTrace`

A **tempered cascade** equips each layer of a `CascadeRouterCode` with its own sharpness `β ℓ`. The
soft-route trace `softCascadeTrace` routes layer `ℓ` by the `leastArgmax` of that layer's **soft mixture
weights** (`softWeights`) — genuinely the soft channel, not the argmax route. The depth-lift is the
theorem that, for all `β ℓ > 0`, this soft trace equals the hard `cascadeTrace`.

**State-agreement note (the load-bearing structure, made precise on this carrier).** The URS frames the
depth-lift as a state-agreement induction: equal per-layer routes ⇒ equal chosen branch ⇒ equal
`runUpTo` state ⇒ equal next route. On the capacity carrier `CascadeRouterCode`, the layers are
**independent** routers over a *shared* input `x` (the joint parameter is the product `∀ ℓ, (layer ℓ).Ρ`,
and `cascadeTrace C hk ρ x ℓ = (C.layer ℓ).route (hk ℓ) (ρ ℓ) x`): the inter-layer "state" is the
constant `x`, so the state recursion is the trivial fixed point and the induction degenerates to a
**pointwise per-layer route agreement** — each layer's soft route equals its hard route by `KU1`. The
genuine `runUpTo`-state cascade with non-trivial inter-layer state passing is `BaseUpMoECascadeCode`
(the witness/measure carrier, `UK1`); lifting `softCascadeTrace` to that carrier with a non-degenerate
state-agreement induction is the A5-split task, not done here. We do not pretend the capacity carrier
has state it does not have. -/

/-- A **tempered cascade router code**: a depth-`L` cascade of independent per-layer finite score
routers, each equipped with its own sharpness `β ℓ ≥ 0`. The hard cascade `toCascade` forgets the
sharpnesses; `softCascadeTrace` reads each layer through its soft mixture channel at `β ℓ`. -/
structure TemperedCascadeRouterCode (X : Type u) [MeasurableSpace X] (L : ℕ) (k : Fin L → ℕ) where
  /-- The underlying hard cascade. -/
  toCascade : CascadeRouterCode X L k
  /-- The per-layer sharpness. -/
  β : Fin L → ℝ
  /-- Each sharpness is nonnegative. -/
  hβ : ∀ ℓ, 0 ≤ β ℓ

/-- The tempered router family at layer `ℓ`: the cascade's `ℓ`-th finite score router at sharpness
`β ℓ`. This is what `softCascadeTrace` routes through. -/
def TemperedCascadeRouterCode.layerFamily {L : ℕ} {k : Fin L → ℕ}
    (C : TemperedCascadeRouterCode X L k) (ℓ : Fin L) : TemperedRouterFamily X (k ℓ) where
  router := C.toCascade.layer ℓ
  β := C.β ℓ
  hβ := C.hβ ℓ

/-- **The soft-route cascade trace.** At a joint parameter `ρ` and input `x`, the tuple of per-layer
**soft** routes `ℓ ↦ leastArgmax (softWeights (layerFamily ℓ) (ρ ℓ) x)`. This routes through the soft
mixture channel at each layer's sharpness — it is *not* `cascadeTrace` definitionally (the per-layer
body is `leastArgmax (softWeights …)`, the mixture-channel reading, not `leastArgmax (score …)`); the
two coincide only as a *theorem* (`KU2_softCascadeTrace_eq`) and only for `β ℓ > 0`. -/
def softCascadeTrace {L : ℕ} {k : Fin L → ℕ} (C : TemperedCascadeRouterCode X L k)
    (hk : ∀ ℓ, 0 < k ℓ) : C.toCascade.Param → X → (∀ ℓ, Fin (k ℓ)) :=
  fun ρ x ℓ => leastArgmax (softWeights (C.layerFamily ℓ) (ρ ℓ) x) (hk ℓ)

/-- **KU2 (depth-lift, M-Pipeline).** For all positive per-layer sharpnesses, the soft-route cascade
trace equals the hard `cascadeTrace`. The proof is `funext` over the depth index followed by the
per-layer route agreement `KU1_routeInvariance_hardRoute` (each soft layer route equals that layer's
hard route, which is exactly the `cascadeTrace` body `(C.toCascade.layer ℓ).route …`). The statement is
`=` at maximal generality (any depth `L`, any per-layer arities `k`, any input space `X`, all
`β ℓ > 0`); the positivity hypothesis is load-bearing per layer (KU1 fails at `β ℓ = 0`). -/
theorem KU2_softCascadeTrace_eq {L : ℕ} {k : Fin L → ℕ} (C : TemperedCascadeRouterCode X L k)
    (hk : ∀ ℓ, 0 < k ℓ) (hβ : ∀ ℓ, 0 < C.β ℓ) (ρ : C.toCascade.Param) (x : X) :
    softCascadeTrace C hk ρ x = cascadeTrace C.toCascade hk ρ x := by
  funext ℓ
  -- per-layer state agreement: the layers are independent over the shared `x`, so the depth
  -- recursion is pointwise and each coordinate is `KU1` at layer `ℓ`.
  show leastArgmax (softWeights (C.layerFamily ℓ) (ρ ℓ) x) (hk ℓ)
      = (C.toCascade.layer ℓ).route (hk ℓ) (ρ ℓ) x
  rw [KU1_routeInvariance_hardRoute (C.layerFamily ℓ) (hk ℓ) (hβ ℓ) (ρ ℓ) x]
  rfl

/-! ## KU2★: the GENUINELY STATEFUL route-invariance on `MuxCascade` (the hard core)

The stateless `softCascadeTrace` above lives on `CascadeRouterCode`, where the layers are independent
routers over a shared input and the "depth-lift" is a pointwise per-coordinate application of `KU1`.
**That carrier is forbidden as the route-invariance carrier** (the depth-lift there is trivial). The
genuine stateful carrier is `MuxHierarchy.MuxCascade`, whose `runUpTo` recursion threads an evolving
state: `runUpTo (m+1) x = (layers m).applyLayer (runUpTo m x)`. Here the soft route at layer `m` reads
the *soft-evolved* state, so the depth-lift is a real **state-agreement induction**, not pointwise.

We build a soft gate (route at temperature `1/β`), a soft `applyLayer`, a soft `runUpTo`, and a soft
trace, each whose body is `leastArgmax (softmax (β • …))` — genuinely the soft mixture channel, *not*
the hard route by definition. The equality to the hard objects is a **theorem** (`KU2_softMuxTrace_eq`),
proved by induction on depth, and is false at `β = 0` (the gate would collapse). -/

open MuxHierarchy

/-- **KU-soft-gate.** The soft (temperature-`1/β`) gate of an affine-mux layer: the `leastArgmax` of the
**softmax of the `β`-scaled scores**, i.e. the branch index read through the soft mixture channel at
sharpness `β`. Its body is `leastArgmax (softmax (β • fun i => (L.scores i).eval x))` — the soft channel,
*not* `L.gate` by definition. -/
def softGate {d n : ℕ} (L : AffineMuxLayer d n) (hn : 0 < n) (β : ℝ) (x : Fin d → ℝ) : Fin n :=
  leastArgmax (softmax (β • fun i => (L.scores i).eval x)) hn

/-- **KU-soft-gate = gate (`β > 0`).** The soft gate does not see the temperature: for `β > 0` it equals
the hard `AffineMuxLayer.gate`. Direct application of the bare-vector atom `leastArgmax_softmax_smul_vec`
to the score vector `v = fun i => (L.scores i).eval x`. The hypothesis `0 < β` is load-bearing. -/
theorem softGate_eq_gate {d n : ℕ} (L : AffineMuxLayer d n) (hn : 0 < n) {β : ℝ} (hβ : 0 < β)
    (x : Fin d → ℝ) : softGate L hn β x = L.gate hn x := by
  rw [softGate, AffineMuxLayer.gate]
  exact leastArgmax_softmax_smul_vec (fun i => (L.scores i).eval x) hn hβ

/-- **KU-soft-applyLayer.** The soft layer map: gate softly (at `β`), then apply the selected affine
branch. Body uses `softGate`, so it is genuinely soft-routed. -/
def softApplyLayer {d n : ℕ} (L : AffineMuxLayer d n) (hn : 0 < n) (β : ℝ)
    (x : Fin d → ℝ) : Fin d → ℝ :=
  (L.branches (softGate L hn β x)).apply x

/-- **KU-soft-applyLayer = applyLayer (`β > 0`).** The soft layer map equals the hard `applyLayer`: the
soft gate selects the same branch (`softGate_eq_gate`), so the same affine branch is applied. -/
theorem softApplyLayer_eq_applyLayer {d n : ℕ} (L : AffineMuxLayer d n) (hn : 0 < n) {β : ℝ}
    (hβ : 0 < β) (x : Fin d → ℝ) : softApplyLayer L hn β x = L.applyLayer hn x := by
  rw [softApplyLayer, AffineMuxLayer.applyLayer, softGate_eq_gate L hn hβ x]

/-- **The SOFT cascade state.** `softRunUpTo C β m x` runs the first `m` layers of the cascade using the
**soft** layer map `softApplyLayer` at per-layer sharpness `β ⟨m,h⟩`, threading the evolving state
exactly as `MuxCascade.runUpTo` does — it is the genuine soft-routed state, *not* `runUpTo` by
definition (the body is `softApplyLayer …`, whose gate is `leastArgmax (softmax …)`). -/
def softRunUpTo {d L : ℕ} (C : MuxCascade d L) (β : Fin L → ℝ) :
    ℕ → (Fin d → ℝ) → (Fin d → ℝ)
  | 0, x => x
  | (m + 1), x =>
      if h : m < L then
        softApplyLayer (C.layers ⟨m, h⟩) (C.harity ⟨m, h⟩) (β ⟨m, h⟩) (softRunUpTo C β m x)
      else softRunUpTo C β m x

/-- **KU2★ (THE HARD CORE — the stateful state-agreement induction).** For all per-layer sharpnesses
`β ℓ > 0`, the soft cascade state agrees with the hard `runUpTo` state at **every** depth `m`. This is
the genuine stateful induction: it threads the evolving state, *not* a pointwise per-layer comparison.

* base `m = 0`: both states are `x` (`rfl`);
* step `m+1`: `softRunUpTo (m+1) = softApplyLayer (softRunUpTo m)` `= softApplyLayer (runUpTo m)` [by
  the IH, rewriting the *state* the soft layer acts on] `= applyLayer (runUpTo m)`
  [`softApplyLayer_eq_applyLayer` on the agreed state, using `β ⟨m,h⟩ > 0`] `= runUpTo (m+1)`.

The IH-rewrite of the inner state is exactly what makes this non-pointwise: the soft layer at depth `m`
reads the soft-evolved state, and we must first prove that state equals the hard-evolved state before
the per-layer agreement (`softApplyLayer_eq_applyLayer`) can fire. -/
theorem softRunUpTo_eq_runUpTo {d L : ℕ} (C : MuxCascade d L) {β : Fin L → ℝ}
    (hβ : ∀ ℓ, 0 < β ℓ) (m : ℕ) (x : Fin d → ℝ) :
    softRunUpTo C β m x = C.runUpTo m x := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [softRunUpTo, MuxCascade.runUpTo]
      by_cases h : m < L
      · rw [dif_pos h, dif_pos h]
        -- thread the state: first the IH (soft state = hard state at depth m), then per-layer agreement
        rw [ih, softApplyLayer_eq_applyLayer (C.layers ⟨m, h⟩) (C.harity ⟨m, h⟩) (hβ ⟨m, h⟩)]
      · rw [dif_neg h, dif_neg h, ih]

/-- **The SOFT mux trace.** At input `x`, the tuple of per-layer soft gates read on the **soft-evolved**
state: `softMuxTrace C β x i = softGate (C.layers i) (C.harity i) (β i) (softRunUpTo C β i.val x)`. Its
body is `leastArgmax (softmax (β • …))` on the soft state — genuinely soft-routed; equality to
`MuxCascade.trace` is the theorem `KU2_softMuxTrace_eq`, *not* a definitional unfolding. -/
def softMuxTrace {d L : ℕ} (C : MuxCascade d L) (β : Fin L → ℝ) (x : Fin d → ℝ) :
    (i : Fin L) → Fin (C.arity i) :=
  fun i => softGate (C.layers i) (C.harity i) (β i) (softRunUpTo C β i.val x)

/-- **KU2★ (route trace, stateful).** For all per-layer sharpnesses `β ℓ > 0`, the soft mux trace equals
the hard `MuxCascade.trace`. Each layer's soft gate on the soft-evolved state equals the hard gate on
the `runUpTo` state, by `softGate_eq_gate` (soft gate = gate, `β i > 0`) composed with
`softRunUpTo_eq_runUpTo` (the soft state = the hard state — KU2★'s induction). This is the genuine
stateful route-invariance: the soft trace reads the evolving soft state, and its equality to the hard
trace is carried by the state-agreement induction, not pointwise. The statement is `=` at maximal
generality (any `d`, `L`, per-layer arities, all `β ℓ > 0`); `0 < β ℓ` is load-bearing (the gate
collapses at `β ℓ = 0`). -/
theorem KU2_softMuxTrace_eq {d L : ℕ} (C : MuxCascade d L) {β : Fin L → ℝ}
    (hβ : ∀ ℓ, 0 < β ℓ) (x : Fin d → ℝ) :
    softMuxTrace C β x = MuxCascade.trace C x := by
  funext i
  rw [softMuxTrace, MuxCascade.trace,
    softGate_eq_gate (C.layers i) (C.harity i) (hβ i),
    softRunUpTo_eq_runUpTo C hβ i.val x]

/-- **The soft cascade run** (all `L` layers, soft-routed). Equal to `MuxCascade.run` for `β ℓ > 0`. -/
def softRun {d L : ℕ} (C : MuxCascade d L) (β : Fin L → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  softRunUpTo C β L x

theorem softRun_eq_run {d L : ℕ} (C : MuxCascade d L) {β : Fin L → ℝ}
    (hβ : ∀ ℓ, 0 < β ℓ) (x : Fin d → ℝ) : softRun C β x = C.run x :=
  softRunUpTo_eq_runUpTo C hβ L x

/-! ## KU3★/KU4★: the route fiber is T-invariant on the stateful carrier

`softMuxTrace = trace` (KU2★) is the spine: every route-derived quantity of the soft cascade equals
that of the hard cascade. We make this concrete for the two route legs:

* **expressivity** (KU3★/KU4★-expressivity): the soft trace function `softMuxTrace C β` is literally the
  hard trace function `MuxCascade.trace C` (`funext` of KU2★), so it has the **same realized-trace
  range**, hence the **same `pieceCount`**, hence the **same** `muxCascade_pieces_le_prod` membership in
  the grade ladder;
* **capacity** (KU4★-capacity): the region-count bound `softPieceCount ≤ ∏ arities` is carried unchanged
  (the soft piece count *is* the hard piece count).

These are `=`/`≤` at maximal generality (any `d`, `L`, arities; all `β ℓ > 0`). -/

/-- The soft cascade's piece count: `Nat.card` of the range of `softMuxTrace C β`. Body is the soft
trace, so it is genuinely the soft-routed piece count, not `pieceCount` by definition. -/
def softPieceCount {d L : ℕ} (C : MuxCascade d L) (β : Fin L → ℝ) : ℕ :=
  Nat.card (Set.range (softMuxTrace C β))

/-- **KU3★ (route-trace function equality).** For `β ℓ > 0`, the soft trace function equals the hard
trace function as maps `(Fin d → ℝ) → ∀ i, Fin (C.arity i)`. (Function-extensional form of KU2★, the
hook for every range/cardinality consequence below.) -/
theorem KU3_softMuxTrace_funext {d L : ℕ} (C : MuxCascade d L) {β : Fin L → ℝ}
    (hβ : ∀ ℓ, 0 < β ℓ) : softMuxTrace C β = MuxCascade.trace C := by
  funext x; exact KU2_softMuxTrace_eq C hβ x

/-- **KU4★ (capacity, T-invariant: same piece count).** For `β ℓ > 0`, the soft cascade has the **same
piece count** as the hard cascade (the trace functions are equal, hence the same realized-trace range).
Capacity is a function of the route, and the route is T-invariant. -/
theorem KU4_softPieceCount_eq {d L : ℕ} (C : MuxCascade d L) {β : Fin L → ℝ}
    (hβ : ∀ ℓ, 0 < β ℓ) : softPieceCount C β = C.pieceCount := by
  rw [softPieceCount, MuxCascade.pieceCount, KU3_softMuxTrace_funext C hβ]

/-- **KU4★ (capacity bound, T-invariant: the region-count bound is carried unchanged).** For `β ℓ > 0`,
the soft cascade satisfies the **same** region-count bound `≤ ∏ᵢ arityᵢ` as the hard cascade. This is
the stateful-carrier capacity leg: the depth-hierarchy region count `muxCascade_pieces_le_prod` (R7's
capacity mechanism on `MuxCascade`) transported across `softPieceCount = pieceCount`.

**Carrier note (honest, per the URS).** R7's single `NatarajanDim` capacity lives on the *stateless*
`CascadeRouterCode` (independent per-layer routers on a shared input — a **different carrier**). The
stateful `MuxCascade` carrier's capacity is exactly this region-count bound, which threads the evolving
state. The two are co-located capacity legs on distinct carriers; we do not conflate them. -/
theorem KU4_capacity_T_invariant {d L : ℕ} (C : MuxCascade d L) {β : Fin L → ℝ}
    (hβ : ∀ ℓ, 0 < β ℓ) : softPieceCount C β ≤ ∏ i, C.arity i := by
  rw [KU4_softPieceCount_eq C hβ]; exact muxCascade_pieces_le_prod C

/-- The soft cascade's `k`-way affine readout: route the soft run output through `k` affine scores.
Body uses `softRun`, so it is genuinely soft-routed. -/
def softCascadeRoute {d L k : ℕ} (C : MuxCascade d L) (β : Fin L → ℝ)
    (routeScores : Fin k → AffineFunctional d) (hk : 0 < k) : (Fin d → ℝ) → Fin k :=
  fun x => leastArgmax (fun j => (routeScores j).eval (softRun C β x)) hk

/-- **KU4★ (expressivity, T-invariant: same realized route ⇒ same grade membership).** For `β ℓ > 0`,
the soft readout route equals the hard `cascadeRoute`, so any route realized by the soft cascade lies in
the **same** `muxCascadeGrade` as the corresponding hard cascade route. Expressivity is a function of
the route, and the route is T-invariant. -/
theorem KU4_softCascadeRoute_eq {d L k : ℕ} (C : MuxCascade d L) {β : Fin L → ℝ}
    (hβ : ∀ ℓ, 0 < β ℓ) (routeScores : Fin k → AffineFunctional d) (hk : 0 < k) :
    softCascadeRoute C β routeScores hk = MuxHierarchy.cascadeRoute C routeScores hk := by
  funext x
  rw [softCascadeRoute, MuxHierarchy.cascadeRoute, softRun_eq_run C hβ x]

/-- **KU4★ (expressivity grade membership, T-invariant).** For `β ℓ > 0`, the soft readout route lies in
`muxCascadeGrade d k L` — the **same** expressivity grade as the hard cascade route (it equals
`cascadeRoute C routeScores hk`, the witness of grade membership). -/
theorem KU4_expressivity_T_invariant {d L k : ℕ} (C : MuxCascade d L) {β : Fin L → ℝ}
    (hβ : ∀ ℓ, 0 < β ℓ) (routeScores : Fin k → AffineFunctional d) (hk : 0 < k) :
    softCascadeRoute C β routeScores hk ∈ muxCascadeGrade d k L hk :=
  ⟨C, routeScores, KU4_softCascadeRoute_eq C hβ routeScores hk⟩

/-! ## KU5/KU6: the measure leg is the only T-dependent leg — measurability-as-base

The route fiber (KU2★ + KU3★ + KU4★) is **T-invariant**: at every `β ℓ > 0` the soft cascade reads the
same trace, has the same piece count, satisfies the same region-count bound, and realizes the same
expressivity grade as the hard cascade. The **only** leg that moves with temperature is the
**measure/margin** leg: the cliff `TLT.Boundary.depthTemperatureCliff` at `τ = T`, where the soft
ghost-gap supremum is Borel (continuous blend) while the argmax cascade bad event is non-Borel yet
null-measurable. This is the **measurability-as-base** picture: `T` is the base over which the four legs
co-fiber, and it moves only the measure phase. -/

/-- **KU5 (the measure leg is T-dependent — the cliff).** A re-export of the cliff
`TLT.Boundary.depthTemperatureCliff` as the temperature-dependent measure leg, at routing temperature
`τ` and every depth `L`: over a non-Borel base witness `g`, the soft (temperature-`τ`) ghost-gap
supremum is **measurable** (Borel — continuous blend), while the argmax cascade bad event on the *same*
tree is **non-Borel** yet **null-measurable** under every finite measure. The temperature is the toggle:
this is the genuinely `T`-dependent leg, in contrast to the `T`-invariant route fiber above. -/
theorem KU5_measureLeg_T_dependent {β : Type} [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β] [StandardBorelSpace β]
    {τ : ℝ} (hτ : 0 ≤ τ) (g : β → ℝ) (hg : Continuous g) [Nonempty β]
    (h_non_borel : ¬ MeasurableSet (Set.range g)) (L : ℕ)
    (μ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ))) [IsFiniteMeasure μ] :
    Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
        ⨆ θ : TLT.Boundary.CascadeParam (TLT.Boundary.witnessCascade g hg) L,
          TLT.Boundary.softCascadeMargin τ g hg L θ (p.2 0)
            - TLT.Boundary.softCascadeMargin τ g hg L θ (p.1 0)) ∧
      ¬ MeasurableSet (TLT.Boundary.cascadeBadEvent (TLT.Boundary.witnessCascade g hg) L) ∧
      NullMeasurableSet (TLT.Boundary.cascadeBadEvent (TLT.Boundary.witnessCascade g hg) L) μ :=
  TLT.Boundary.depthTemperatureCliff hτ g hg h_non_borel L μ

/-- **KU6 (measurability-as-base co-fibering, MuxCascade side).** The assembly, packaged as the
structural asymmetry of the temperature base `T`, **on the stateful `MuxCascade` carrier**:

* the **route fiber is `T`-invariant** — at every `β ℓ > 0` the soft mux trace equals the hard trace
  (`KU2_softMuxTrace_eq`), the soft piece count equals the hard piece count
  (`KU4_softPieceCount_eq`), and the soft readout route lies in the same expressivity grade
  (`KU4_expressivity_T_invariant`);
* the **measure leg is `T`-dependent** — the cliff `KU5_measureLeg_T_dependent`.

Concretely (Lean form): the route trace and the region-count bound are returned as *equalities/bounds
independent of `β`* (the fiber), bundled here to certify that the temperature-dependence lives entirely
off the route. The conjunct that "the measure leg is the cliff" is `KU5`, surfaced above; this lemma is
the route-fiber half of the co-fibering, on the stateful carrier, with no dependence on `β` other than
positivity.

**SURFACED TO DHRUV — carrier coupling (NOT self-split).** The cliff `KU5` lives on
`TLT.Boundary.BaseUpMoECascadeCode β width` (a recursive mixture-of-experts cascade with genuine
inter-layer state through `TLT.Boundary.CascadeParam`), whereas the route fiber here lives on
`MuxHierarchy.MuxCascade d L` (the affine-mux argmax cascade with `runUpTo` state). These are **two
genuinely different stateful carriers**, co-located by the design law but not unified. Forcing the cliff
and the route fiber onto a *single* carrier requires an explicit coupling
`MuxCascade ↔ BaseUpMoECascadeCode` under temperature-invariant routing — that coupling is genuinely
separate structure. Per the hard rule it is **surfaced for Dhruv to organize**, not invented/self-split
here; the MuxCascade-side co-fibering (this lemma + KU2★/KU3★/KU4★) is landed in full. -/
theorem KU6_measurabilityAsBase {d L k : ℕ} (C : MuxCascade d L) {β : Fin L → ℝ}
    (hβ : ∀ ℓ, 0 < β ℓ) (x : Fin d → ℝ)
    (routeScores : Fin k → AffineFunctional d) (hk : 0 < k) :
    -- route fiber, T-invariant (no dependence on `β` beyond positivity):
    softMuxTrace C β x = MuxCascade.trace C x ∧
      softPieceCount C β = C.pieceCount ∧
      softPieceCount C β ≤ ∏ i, C.arity i ∧
      softCascadeRoute C β routeScores hk ∈ muxCascadeGrade d k L hk :=
  ⟨KU2_softMuxTrace_eq C hβ x, KU4_softPieceCount_eq C hβ, KU4_capacity_T_invariant C hβ,
    KU4_expressivity_T_invariant C hβ routeScores hk⟩

end TLT.TemperedDesignLaw
