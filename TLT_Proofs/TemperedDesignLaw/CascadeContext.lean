/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.CascadePolyFunctor
import TLT_Proofs.TemperedDesignLaw.DecisionCascade
import TLT_Proofs.TemperedDesignLaw.MuxDepthLadder

/-!
# The depth-`L` cascade's "prior typed layers as context" as a CONTEXT-EXTENSION TELESCOPE (R4)

A depth-`L` cascade is not a flat product of independent layers: layer `i`'s route is computed on the
STATE PRODUCED BY THE PRECEDING LAYERS. The route at layer `i` therefore depends on the prefix of
prior layers — it is a TERM read off a CONTEXT that GROWS with depth. This module makes that precise in
the category-with-families (CwF) idiom:

* a CONTEXT at depth `i` (`cascadeContext`): the dependent type carrying the prior-layer route data,
  `Γ_i = ∀ j : Fin i, Fin (arity j)` — the prefix of route addresses for the layers `< i`. It GROWS:
  depth-`(i+1)` context is depth-`i` context EXTENDED by the layer-`i` route type;
* the CONTEXT EXTENSION (`cascadeContext_extend`): the CwF comprehension `Γ_{i+1} ≅ Γ_i ▷ A_i`, an
  equivalence `Γ_{i+1} ≃ Σ (γ : Γ_i), A_i γ` — a genuine dependent `Σ`, not a constant/unit extension;
* the route as a TERM-IN-CONTEXT (`cascadeRoute_term_in_context`): layer `i`'s active branch is a
  function of the depth-`i` state `runUpTo i`, i.e. an element of `Tm(Γ_i, A_i)` once the state is
  located over the context;
* the telescoped composition (`cascadeContext_telescope` / `cascadeRegionMap_telescope`): the full
  context at depth `L` is the iterated extension `Γ_0 ▷ A_0 ▷ … ▷ A_{L-1}` (a telescope), and the
  cascade's exact region map factors as the telescoped composition, reusing
  `regionMap_exact_telescope` (`DecisionCascade.lean`).

## Generality (LOCKED)

Everything below is general in the depth `L`, the carrier dimension `d`, and the **per-layer arities**
`arity : ℕ → ℕ` / `Fin L → ℕ`, **which may VARY across layers** — this is exactly the
varying-arity dependent generalization that the single uniform `PFunctor` W-type of R3a
(`CascadePolyFunctor.lean`) could not express: there the branching `Fin k` was a FIXED `k` at every
node, whereas the telescope's extension type `A_i = Fin (arity i)` is allowed to differ at each depth.

## A5 split

A FULLY ABSTRACT category-with-families (an actual `CwF` structure: a category of contexts, a presheaf
of types, the comprehension functor with its universal property as a representability witness) is NOT
constructed here: Mathlib has no CwF / category-with-families library, and building one is a separate
dependency. That abstract leg is A5-split to task **R8 (abstract CwF for the cascade telescope)**. The
cascade-SPECIFIC context-extension telescope (the comprehension equivalence, the term-in-context, and
the telescoped region map) is closed below at full generality.
-/

open scoped BigOperators

noncomputable section

namespace TLT.TemperedDesignLaw

universe u

/-! ## (R4.1) The dependent context: the prefix of prior-layer route types -/

/-- **The depth-`i` cascade CONTEXT.** `cascadeContext arity i = ∀ j : Fin i, Fin (arity j)`: the
prefix of *route addresses* (active branch indices) for the first `i` layers. This is the dependent
type carrying the data the next layer's route depends on. It is the CwF *context* `Γ_i`; the per-layer
extension type is `Fin (arity j)`, with `arity : ℕ → ℕ` the (possibly VARYING) per-layer mux arity. As
a special case of the `cascadePath` route space, restricted to the prefix `< i`. -/
def cascadeContext (arity : ℕ → ℕ) (i : ℕ) : Type :=
  ∀ j : Fin i, Fin (arity j)

instance (arity : ℕ → ℕ) (i : ℕ) : Fintype (cascadeContext arity i) := by
  unfold cascadeContext; infer_instance

/-- **The layer-`i` extension type `A_i`.** In the CwF picture `Γ_{i+1} = Γ_i ▷ A_i`; here the type
being appended at depth `i` is the layer-`i` route type `Fin (arity i)`. In full generality `A_i` may
DEPEND on the context `γ : Γ_i` (a dependent CwF type-in-context `Tm`-codomain); for the cascade the
route alphabet of a layer is its fixed arity, so `A_i` is the constant family `fun _ : Γ_i => Fin
(arity i)`. Keeping it as a family `Γ_i → Type` records the dependent shape. -/
def cascadeExtType (arity : ℕ → ℕ) (i : ℕ) : cascadeContext arity i → Type :=
  fun _ => Fin (arity i)

/-! ## (R4.2) The context extension `Γ_{i+1} = Γ_i ▷ A_i` (CwF comprehension) -/

/-- **The CONTEXT-EXTENSION EQUIVALENCE (CwF comprehension).** The depth-`(i+1)` context is the
depth-`i` context EXTENDED by the layer-`i` route type: `Γ_{i+1} ≃ Σ (γ : Γ_i), A_i γ`. This is the
CwF comprehension `Hom(Δ, Γ.A) ≅ Σ (σ : Δ → Γ), Tm(Δ, A[σ])` specialised to `Δ = Γ_i = ·` (identity
substitution): a map into `Γ_{i+1}` is a map into `Γ_i` paired with a term of `A_i`. Concretely a
prefix of length `i+1` is a prefix of length `i` together with the `i`-th branch — `Fin.snoc` /
`Fin.lastCases`. General in `arity` (varying), `i`. -/
def cascadeContext_extend (arity : ℕ → ℕ) (i : ℕ) :
    cascadeContext arity (i + 1) ≃ Σ γ : cascadeContext arity i, cascadeExtType arity i γ where
  toFun γ := ⟨fun j => γ j.castSucc, γ (Fin.last i)⟩
  invFun p := Fin.lastCases p.2 p.1
  left_inv γ := by
    funext j
    refine Fin.lastCases ?_ ?_ j
    · simp [Fin.lastCases_last]
    · intro j; simp [Fin.lastCases_castSucc]
  right_inv p := by
    cases p with
    | mk γ a =>
      have hfst : (fun j : Fin i =>
          (Fin.lastCases a γ : ∀ j : Fin (i + 1), Fin (arity j)) (Fin.castSucc j))
          = γ := by funext j; simp [Fin.lastCases_castSucc]
      simp only [Fin.lastCases_last]
      exact Sigma.ext hfst (by rw [hfst])

/-- **Non-degeneracy of the extension: the context GROWS.** The depth-`(i+1)` context has cardinality
`arity i` times the depth-`i` context — `Fintype.card Γ_{i+1} = (arity i) * Fintype.card Γ_i`. With
`arity i ≥ 2` (a genuine ≥ 2-way mux layer) the extension is STRICT (`Fintype.card Γ_i <
Fintype.card Γ_{i+1}`): the telescope is not a constant/unit context. This is the load-bearing
non-vacuity check. General in `arity`, `i`. -/
theorem cascadeContext_card (arity : ℕ → ℕ) (i : ℕ) :
    Fintype.card (cascadeContext arity i) = ∏ j : Fin i, arity j := by
  show Fintype.card (∀ j : Fin i, Fin (arity j)) = ∏ j : Fin i, arity j
  rw [Fintype.card_pi]; simp [Fintype.card_fin]

theorem cascadeContext_card_succ (arity : ℕ → ℕ) (i : ℕ) :
    Fintype.card (cascadeContext arity (i + 1))
      = arity i * Fintype.card (cascadeContext arity i) := by
  rw [cascadeContext_card, cascadeContext_card, Fin.prod_univ_castSucc]
  simp [mul_comm]

/-- **The context strictly grows under a genuine (≥ 2-way) layer.** Given the cascade positivity
`harity : ∀ j, 0 < arity j` (every layer has at least one branch — exactly the `MuxCascade.harity`
field) and a genuine ≥ 2-way layer at depth `i` (`2 ≤ arity i`), the depth-`i` context is STRICTLY
smaller than the depth-`(i+1)` context. This rules out the hollowing failure mode (a degenerate
constant/unit context): each genuine mux layer enlarges the telescope. The positivity hypothesis is
load-bearing — without it an earlier zero-arity layer would empty the context and the cardinalities
would both be `0`. -/
theorem cascadeContext_card_lt_succ (arity : ℕ → ℕ) (harity : ∀ j, 0 < arity j) (i : ℕ)
    (hi : 2 ≤ arity i) :
    Fintype.card (cascadeContext arity i) < Fintype.card (cascadeContext arity (i + 1)) := by
  rw [cascadeContext_card_succ]
  have hpos : 0 < Fintype.card (cascadeContext arity i) := by
    rw [Fintype.card_pos_iff]
    exact ⟨fun j => ⟨0, harity j⟩⟩
  calc Fintype.card (cascadeContext arity i)
      = 1 * Fintype.card (cascadeContext arity i) := (one_mul _).symm
    _ < arity i * Fintype.card (cascadeContext arity i) :=
        Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl _) hpos

/-! ## (R4.3) The route at layer `i` is a TERM over the depth-`i` context -/

/-- **The layer-`i` route TERM (the gate as a section over the state).** A function
`(Fin d → ℝ) → Fin (C.arity i)` reading the layer-`i` active branch off a state. This is the
type-in-context's *term* `Tm(Γ_i, A_i)` realised semantically: the context `Γ_i` is carried by the
depth-`i` STATE `runUpTo i`, and `cascadeLayerTerm C i` is the function that, given that state, returns
the route. General in `d`, `L`, the cascade `C` (hence varying arity). -/
def cascadeLayerTerm {d L : ℕ} (C : MuxHierarchy.MuxCascade d L) (i : Fin L) :
    (Fin d → ℝ) → Fin (C.arity i) :=
  fun s => (C.layers i).gate (C.harity i) s

/-- **(R4.3) THE ROUTE IS A TERM OVER THE DEPTH-`i` CONTEXT.** Layer `i`'s active branch
`C.trace x i` is the layer-`i` term `cascadeLayerTerm C i` applied to the depth-`i` STATE
`C.runUpTo i x` — the state produced by running the PRIOR layers. So the route is not a free choice: it
is a TERM-IN-CONTEXT, a function of the prefix of prior layers carried by `runUpTo i`. This is the CwF
term `Tm(Γ_i, A_i)` for the cascade. (`rfl`: it is the definition of `MuxCascade.trace`.) General in
`d`, `L`, `C`, `x`, `i`. -/
theorem cascadeRoute_term_in_context {d L : ℕ} (C : MuxHierarchy.MuxCascade d L)
    (x : Fin d → ℝ) (i : Fin L) :
    C.trace x i = cascadeLayerTerm C i (C.runUpTo i.val x) := rfl

/-- **(R4.3) THE TERM FACTORS THROUGH THE PRIOR-LAYER CONTEXT (the substitution lemma).** The
depth-`i` state — hence the layer-`i` route — depends on the input only through the prefix of prior
routes: on the trace-fiber of any base point `x₀` (same branch chosen at every prior layer), the
depth-`i` state is the FIXED affine map `C.prefixMap x₀ i` (determined entirely by `x₀`'s prefix
trace). This is the CwF substitution `A_i[σ]`: the term lives over the context `Γ_i`, and the context
is exactly the prior-layer route data. Reuses `runUpTo_eq_prefixMap_on_fiber`. General in `d`, `L`. -/
theorem cascadeRoute_factors_through_context {d L : ℕ} (C : MuxHierarchy.MuxCascade d L)
    (x₀ y : Fin d → ℝ) (hfib : C.trace y = C.trace x₀) (i : Fin L) :
    C.trace y i = cascadeLayerTerm C i ((C.prefixMap x₀ i.val).apply y) := by
  rw [cascadeRoute_term_in_context]
  rw [C.runUpTo_eq_prefixMap_on_fiber x₀ y hfib i.val]

/-! ## (R4.4) The telescoped region map: the cascade trace factors over the growing context -/

/-- **The full depth-`L` cascade context is the route space.** The context at the END of the telescope,
`cascadeContext C.arity L`, is exactly the cascade's route/leaf-address space `cascadePath L C.arity`
(`CascadePolyFunctor.lean`): the iterated extension `Γ_0 ▷ A_0 ▷ … ▷ A_{L-1}` collects all `L`
per-layer route types (both unfold to `∀ i : Fin L, Fin (arity i)`, matching componentwise). The
context-extension telescope's terminal object is the polynomial-functor leaf space. -/
def cascadeContext_L_equiv_cascadePath {d L : ℕ} (C : MuxHierarchy.MuxCascade d L) :
    cascadeContext (fun n => if h : n < L then C.arity ⟨n, h⟩ else 1) L ≃ cascadePath L C.arity :=
  Equiv.piCongrRight (fun j => by
    show Fin (if h : (j : ℕ) < L then C.arity ⟨j, h⟩ else 1) ≃ Fin (C.arity j)
    rw [dif_pos j.isLt])

/-- **The single-layer (guarded) executed step.** At index `j`, if `j < L` apply the layer-`j` mux map,
else the identity. The cascade's forward execution is the head-first composition of these. -/
def cascadeStep {d L : ℕ} (C : MuxHierarchy.MuxCascade d L) (j : ℕ) :
    (Fin d → ℝ) → (Fin d → ℝ) :=
  fun s => if h : j < L then (C.layers ⟨j, h⟩).applyLayer (C.harity ⟨j, h⟩) s else s

/-- **The cascade region layers as a telescope (one `RegionMapLayer` per cascade layer).** The depth-`L`
cascade is a `List (RegionMapLayer (Fin d → ℝ))` of length `L`, one entry per layer index `j < L`, with
ideal = exec = the layer-`j` executed mux map (`cascadeStep`) and region = `univ`. Read input-first,
this list's executed composition is the cascade run (`cascadeRegionLayers_rmExecComp`). The list realises
the *telescope of contexts*: composing the first `i` entries lands the state in the depth-`i` context.
General in `d`, `L`, the cascade `C`. -/
def cascadeRegionLayers {d L : ℕ} (C : MuxHierarchy.MuxCascade d L) :
    List (RegionMapLayer (Fin d → ℝ)) :=
  (List.range L).map (fun j =>
    { ideal := cascadeStep C j
      exec := cascadeStep C j
      region := Set.univ })

/-- `rmExecComp` of a `map`'d list equals the left fold applying each step head-first. -/
private theorem rmExecComp_map {d : ℕ} (g : ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (l : List ℕ) (x : Fin d → ℝ) :
    rmExecComp (l.map (fun j =>
        ({ ideal := g j, exec := g j, region := Set.univ } : RegionMapLayer (Fin d → ℝ)))) x
      = l.foldl (fun s j => g j s) x := by
  induction l generalizing x with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, rmExecComp, List.foldl_cons]; exact ih _

/-- `runUpTo m` over the cascade is the left fold of the guarded `cascadeStep` over `range m`: the
forward execution of the first `m` layers, head-first. Proved by induction on `m` using
`List.range_succ` (`range (m+1) = range m ++ [m]`). -/
private theorem runUpTo_eq_foldl {d L : ℕ} (C : MuxHierarchy.MuxCascade d L) :
    ∀ (m : ℕ) (x : Fin d → ℝ),
      C.runUpTo m x = (List.range m).foldl (fun s j => cascadeStep C j s) x := by
  intro m
  induction m with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih]
      rw [MuxHierarchy.MuxCascade.runUpTo, cascadeStep]

/-- **The executed composition of the cascade region layers IS the cascade run.** Folding the
region-layer telescope head-first reproduces `C.run`. The bridge: `rmExecComp` over the `map`'d list is
the left fold of `cascadeStep`, which by `runUpTo_eq_foldl` is `C.runUpTo L = C.run`. General in `d`,
`L`, `C`, `x`. -/
theorem cascadeRegionLayers_rmExecComp {d L : ℕ} (C : MuxHierarchy.MuxCascade d L)
    (x : Fin d → ℝ) :
    rmExecComp (cascadeRegionLayers C) x = C.run x := by
  rw [cascadeRegionLayers, rmExecComp_map, ← runUpTo_eq_foldl]
  rfl

/-- The cascade region layers are *trivially exact* (ideal = exec by construction), and their executed
trajectory stays in the regions (every region is `univ`). The hypotheses of
`regionMap_exact_telescope` are met unconditionally. -/
theorem cascadeRegionLayers_exact {d L : ℕ} (C : MuxHierarchy.MuxCascade d L) :
    ∀ R ∈ cascadeRegionLayers C, ∀ y ∈ R.region, R.exec y = R.ideal y := by
  intro R hR y _
  simp only [cascadeRegionLayers, List.mem_map] at hR
  obtain ⟨j, _, rfl⟩ := hR
  rfl

theorem cascadeRegionLayers_trajInRegions {d L : ℕ} (C : MuxHierarchy.MuxCascade d L)
    (x : Fin d → ℝ) : rmTrajInRegions (cascadeRegionLayers C) x := by
  rw [cascadeRegionLayers]
  generalize List.range L = l
  induction l generalizing x with
  | nil => exact trivial
  | cons a as ih =>
      refine ⟨Set.mem_univ _, ?_⟩
      exact ih _

/-- **(R4.4) THE CASCADE REGION MAP FACTORS AS THE TELESCOPED COMPOSITION.** The depth-`L` cascade's
region map `C.run` equals the metric-free telescoped composition (`regionMap_exact_telescope`,
`DecisionCascade.lean`) over the per-layer region-layer telescope `cascadeRegionLayers C`:
`C.run x = rmExecComp (cascadeRegionLayers C) x = rmIdealComp (cascadeRegionLayers C) x`. Each entry of
the telescope is one cascade layer; composing the prefix of the first `i` entries carries the state
into the depth-`i` context `Γ_i`, on which the layer-`i` route is read as a term
(`cascadeRoute_term_in_context`). This is the telescope identity connecting the context-extension
telescope to the existing exact telescope. General in `d`, `L`, `C`, `x`. -/
theorem cascadeRegionMap_telescope {d L : ℕ} (C : MuxHierarchy.MuxCascade d L) (x : Fin d → ℝ) :
    C.run x = rmIdealComp (cascadeRegionLayers C) x := by
  rw [← cascadeRegionLayers_rmExecComp C x]
  exact regionMap_exact_telescope (cascadeRegionLayers C) x
    (cascadeRegionLayers_trajInRegions C x) (cascadeRegionLayers_exact C)

/-- **(R4.4) THE TELESCOPE STEP REACHES THE DEPTH-`i` CONTEXT.** Composing exactly the first `i` entries
of the region-layer telescope yields the depth-`i` state `C.runUpTo i` (for `i ≤ L`), on which (by
`cascadeRoute_term_in_context`) every later route is a term. So the telescope's `i`-th stage IS the
depth-`i` context `Γ_i`: the prefix composition produces the state carrying the prior `i` layers' route
data. This is the link "telescope prefix = growing context". General in `d`, `L`, `C`, `i`, `x`. -/
theorem cascadeRegionLayers_take_eq_runUpTo {d L : ℕ} (C : MuxHierarchy.MuxCascade d L)
    (i : ℕ) (x : Fin d → ℝ) :
    rmExecComp ((cascadeRegionLayers C).take i) x = C.runUpTo (min i L) x := by
  rw [cascadeRegionLayers, ← List.map_take, List.take_range, rmExecComp_map, ← runUpTo_eq_foldl]

end TLT.TemperedDesignLaw

