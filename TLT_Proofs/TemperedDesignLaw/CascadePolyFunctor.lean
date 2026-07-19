/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Data.PFunctor.Univariate.Basic
import TLT_Proofs.TemperedDesignLaw.MuxHierarchy

/-!
# The depth-`L` argmax cascade route/region structure as the unfold of a polynomial functor (R3a)

This module exhibits the depth-`L` affine-mux argmax cascade's **route/region structure** as an element
of the W-type of a **polynomial functor** (`Mathlib.Data.PFunctor.Univariate.Basic`), establishing the
generator-as-polynomial-functor identity. The framing:

* The cascade's region map is generated layer by layer: each layer is an arity-`k` mux gate, so the
  region structure unfolds as a `k`-ary tree whose internal nodes are the per-layer *cells/symbols* and
  whose branchings are the *arity positions*. This is exactly the data of a polynomial functor `P`:
  - `A` = the SHAPE at each node: either an internal cell carrying a symbol `s : S`, or a terminal leaf;
  - `B a` = the POSITIONS below that node: `Fin k` (the `k`-way mux branching) at an internal cell, and
    `Fin 0 = Empty` at a leaf.
* `PFunctor.W P` is an inductive type, so **strict positivity, well-foundedness and decidability of the
  region tree hold BY CONSTRUCTION** (no extra side condition imposed).
* The depth-`L` route addresses `∀ i : Fin L, Fin (arity i)` — the trace codomain of `MuxHierarchy`'s
  `MuxCascade.trace`, whose cardinality is the `∏ arity` region-count bound (`muxCascade_pieces_le_prod`)
  — are exactly the *root-to-leaf paths* of the depth-`L` cascade tree.

## The polynomial functor

* `CascadeShape S k`: the head/shape type — `cell s` (an internal node carrying symbol `s : S`, with
  `k` arity positions) or `leaf` (a terminal node, no positions).
* `cascadePFunctor S k`: `A := CascadeShape S k`, `B := positions` (`Fin k` at a cell, `Fin 0` at a
  leaf). `PFunctor.W (cascadePFunctor S k)` is a well-founded `k`-ary `S`-labeled tree.

## (R3a.1) The depth-`L` region tree as a bounded W-type element

* `cascadeTree label L`: the full depth-`L` `k`-ary tree (every internal node labeled by the symbol of
  the partial route address reaching it, leaves at depth `L`), built as a `PFunctor.W` element. General
  in `S` (symbol type), `k` (arity), `L` (depth).
* `cascadeTree_depth_le`: `(cascadeTree label L).depth ≤ L + 1` — structural depth bound BY CONSTRUCTION
  (depth counts `L` cell layers plus the terminal leaf layer).
* `leafCount`: the number of leaves of a W-tree (a structural fold via `WType.elim`).
* `cascadeTree_leafCount`: `leafCount (cascadeTree label L) = k ^ L` — the genuine leaf-count identity.

## (R3a.2) The generator-as-polynomial-functor identity: routes = leaf paths

* `cascadePath L arity := ∀ i : Fin L, Fin (arity i)`, definitionally the codomain of
  `MuxCascade.trace` (the region-count carrier).
* `cascadePath_card`: `Fintype.card (cascadePath L arity) = ∏ i, arity i`, the `MuxCascade` region count
  (`MuxCascade.trace_codomain_card` restated structurally). Under uniform arity `k` this is
  `k ^ L = leafCount (cascadeTree label L)`: the cascade's `∏ arity` region count EQUALS the
  polynomial-functor tree's leaf count.
* `cascadeTrace_mem_cascadePath`: `MuxCascade.trace C x` is, for each `x`, an element of
  `cascadePath L C.arity`; the cascade region map IS a map into the polynomial-functor leaf-address
  space. This is the type-theoretic carrier `O` of the discovery pathway.

## A4 status

All decls below are `sorry`/`admit`/`native_decide`-free and axiom-clean
(`{propext, Classical.choice, Quot.sound}`). The R3b leg (equivalence with finite-copying
MSO-definable tree transductions, Engelfriet–Maneth) is A5-SPLIT to task R7: Mathlib has no MSO /
tree-automata machinery, so that equivalence needs a new dependency and is NOT stated here.
-/

open scoped BigOperators

namespace TLT.TemperedDesignLaw

universe u

/-! ## The polynomial functor of the cascade: shapes = cells/symbols, positions = arity -/

/-- **The cascade node SHAPE.** Either an internal `cell` carrying a generated symbol `s : S` (with `k`
arity positions below it) or a terminal `leaf` (no positions). This is the head type `A` of the cascade
polynomial functor. -/
inductive CascadeShape (S : Type u) (k : ℕ) : Type u
  | cell : S → CascadeShape S k
  | leaf : CascadeShape S k

/-- **The POSITIONS below a node**: the `k`-way mux branching `Fin k` at an internal cell, and `Fin 0`
(no children) at a leaf. This is the child family `B` of the cascade polynomial functor; it is the
*arity* of each node. -/
def CascadeShape.positions {S : Type u} {k : ℕ} : CascadeShape S k → Type
  | .cell _ => Fin k
  | .leaf => Fin 0

/-- **The cascade polynomial functor.** `A := CascadeShape S k` (shapes = cells carrying symbols, plus a
terminal leaf); `B := CascadeShape.positions` (positions = arity, `Fin k` at a cell, `Fin 0` at a leaf).
A `PFunctor.W (cascadePFunctor S k)` is a well-founded `k`-ary `S`-labeled tree: the carrier of the
depth-`L` cascade's route/region structure. Strict positivity, well-foundedness and decidability are
properties of the inductive `PFunctor.W`, hence hold BY CONSTRUCTION. -/
def cascadePFunctor (S : Type u) (k : ℕ) : PFunctor.{u, 0} where
  A := CascadeShape S k
  B := CascadeShape.positions

@[simp] theorem cascadePFunctor_A (S : Type u) (k : ℕ) :
    (cascadePFunctor S k).A = CascadeShape S k := rfl

@[simp] theorem cascadePFunctor_B (S : Type u) (k : ℕ) (a : CascadeShape S k) :
    (cascadePFunctor S k).B a = a.positions := rfl

/-- Every node has finitely many positions (`Fin k` or `Fin 0`), so the W-type `depth` and structural
folds are available. -/
instance instFintypePositions {S : Type u} {k : ℕ} (a : CascadeShape S k) :
    Fintype a.positions := by
  cases a <;> · unfold CascadeShape.positions; infer_instance

instance instFintypeB (S : Type u) (k : ℕ) (a : (cascadePFunctor S k).A) :
    Fintype ((cascadePFunctor S k).B a) :=
  instFintypePositions a

/-! ## (R3a.1) The depth-`L` region tree as a bounded `PFunctor.W` element -/

/-- **The depth-`L` cascade region tree.** A `PFunctor.W (cascadePFunctor S k)` element: the full
depth-`L` `k`-ary tree, in which the internal node reached by a partial route address `p : List (Fin k)`
(the positions chosen so far) is labeled by the cell symbol `label p : S` it generates, and at depth `L`
every node is a terminal `leaf`. At depth `m + 1` the root is a `cell (label [])` whose `Fin k` children
are the depth-`m` subtrees, recursing with the chosen position `i` prepended to the address. This is the
**unfold** of the polynomial functor to depth `L`. General in `S`, `k`, `L`. -/
def cascadeTree {S : Type u} {k : ℕ} :
    (List (Fin k) → S) → (L : ℕ) → PFunctor.W (cascadePFunctor S k)
  | _label, 0 =>
      PFunctor.W.mk ⟨(CascadeShape.leaf : CascadeShape S k), fun i => (i : Fin 0).elim0⟩
  | label, (m + 1) =>
      PFunctor.W.mk ⟨(CascadeShape.cell (label []) : CascadeShape S k),
        fun (i : Fin k) => cascadeTree (fun p => label (i :: p)) m⟩

/-- `WType.depth` of a node, unfolded. `PFunctor.W.mk ⟨a, f⟩` is `WType.mk a f`, whose depth is
`(⨆ i, depth (f i)) + 1`. -/
private theorem depth_mk {S : Type u} {k : ℕ} (a : CascadeShape S k)
    (f : (cascadePFunctor S k).B a → PFunctor.W (cascadePFunctor S k)) :
    (PFunctor.W.mk (P := cascadePFunctor S k) ⟨a, f⟩).depth
      = (Finset.univ.sup fun i => (f i).depth) + 1 := rfl

/-- **(R3a.1) STRUCTURAL DEPTH BOUND, BY CONSTRUCTION.** The depth-`L` cascade region tree has
`WType.depth ≤ L + 1`: it consists of `L` cell layers (one per cascade layer) capped by the terminal
leaf layer, so its well-founded depth is bounded by `L + 1`. The bound is structural — `cascadeTree` is
an element of the inductive `PFunctor.W`, and the depth function is the height of that tree. General in
`S`, `k`, `L`. -/
theorem cascadeTree_depth_le {S : Type u} {k : ℕ} (label : List (Fin k) → S) (L : ℕ) :
    (cascadeTree label L).depth ≤ L + 1 := by
  induction L generalizing label with
  | zero =>
      -- depth of a leaf is `(sup over Fin 0) + 1 = 1 ≤ 0 + 1`
      rw [cascadeTree, depth_mk]
      have hempty : (Finset.univ : Finset ((cascadePFunctor S k).B CascadeShape.leaf)) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro i; exact (i : Fin 0).elim0
      rw [hempty, Finset.sup_empty]; simp
  | succ m ih =>
      rw [cascadeTree, depth_mk]
      -- each child subtree has depth ≤ m + 1, so the sup is ≤ m + 1, hence +1 ≤ m + 2
      have hchild : (Finset.univ.sup fun i : (cascadePFunctor S k).B (CascadeShape.cell (label [])) =>
          (cascadeTree (fun p => label (i :: p)) m).depth) ≤ m + 1 := by
        apply Finset.sup_le
        intro i _
        exact ih (fun p => label (i :: p))
      omega

/-! ### The leaf count via a structural fold (`WType.elim`) -/

/-- **The leaf count of a W-tree.** A structural fold: a node with positions `pos` and children
`children : pos → ℕ` (already-folded leaf counts) contributes `∑ i, children i` if it has children, and
`1` if it is childless (a leaf). Implemented with `WType.elim`. -/
def leafCount {S : Type u} {k : ℕ} (t : PFunctor.W (cascadePFunctor S k)) : ℕ :=
  WType.elim ℕ
    (fun ⟨a, children⟩ =>
      match a, children with
      | CascadeShape.leaf, _ => 1
      | CascadeShape.cell _, children => ∑ i : Fin k, children i) t

@[simp] theorem leafCount_leaf {S : Type u} {k : ℕ}
    (f : (CascadeShape.leaf : CascadeShape S k).positions → PFunctor.W (cascadePFunctor S k)) :
    leafCount (PFunctor.W.mk ⟨CascadeShape.leaf, f⟩) = 1 := rfl

@[simp] theorem leafCount_cell {S : Type u} {k : ℕ} (s : S)
    (f : (CascadeShape.cell s : CascadeShape S k).positions → PFunctor.W (cascadePFunctor S k)) :
    leafCount (PFunctor.W.mk ⟨CascadeShape.cell s, f⟩) = ∑ i : Fin k, leafCount (f i) := rfl

/-- **(R3a.1) THE LEAF-COUNT IDENTITY.** The depth-`L` cascade region tree has exactly `k ^ L` leaves:
each of the `L` cell layers branches `k` ways, so the number of root-to-leaf paths is `k ^ L`. This is
the polynomial-functor face of `MuxHierarchy`'s region count: under uniform per-layer arity `k`, the
cascade's `∏ arity` region bound is `∏_{i : Fin L} k = k ^ L`, which is exactly this leaf count. General
in `S`, `k`, `L`. -/
theorem cascadeTree_leafCount {S : Type u} {k : ℕ} (label : List (Fin k) → S) (L : ℕ) :
    leafCount (cascadeTree label L) = k ^ L := by
  induction L generalizing label with
  | zero => rw [cascadeTree]; rfl
  | succ m ih =>
      rw [cascadeTree, leafCount_cell]
      have : ∀ i : Fin k, leafCount (cascadeTree (fun p => label (i :: p)) m) = k ^ m :=
        fun i => ih (fun p => label (i :: p))
      simp only [this]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, pow_succ]
      ring

/-! ## (R3a.2) The generator-as-polynomial-functor identity: route addresses = leaf paths -/

/-- **The cascade route-address (leaf-path) type.** `∀ i : Fin L, Fin (arity i)`: a choice of mux
position at each of the `L` layers — definitionally the codomain of `MuxHierarchy.MuxCascade.trace`. In
the polynomial-functor picture these are exactly the root-to-leaf paths of the depth-`L` cascade tree
(one position chosen per cell layer). General in `L` and the per-layer arity `arity`. -/
def cascadePath (L : ℕ) (arity : Fin L → ℕ) : Type :=
  ∀ i : Fin L, Fin (arity i)

instance (L : ℕ) (arity : Fin L → ℕ) : Fintype (cascadePath L arity) := by
  unfold cascadePath; infer_instance

/-- **(R3a.2) THE REGION-COUNT IDENTITY.** The number of cascade route addresses (leaf paths) is the
`∏ arity` region count: `Fintype.card (cascadePath L arity) = ∏ i, arity i`. This is exactly the bound
`muxCascade_pieces_le_prod`/`MuxCascade.trace_codomain_card`: the polynomial-functor leaf-address space
has the cascade's region count as its cardinality. General in `L`, `arity`. -/
theorem cascadePath_card (L : ℕ) (arity : Fin L → ℕ) :
    Fintype.card (cascadePath L arity) = ∏ i, arity i := by
  show Fintype.card (∀ i : Fin L, Fin (arity i)) = ∏ i, arity i
  rw [Fintype.card_pi]
  simp [Fintype.card_fin]

/-- **(R3a.2) UNIFORM-ARITY: REGION COUNT = LEAF COUNT.** Under uniform per-layer arity `k`, the
cascade's `∏ arity` region count equals the polynomial-functor tree's leaf count `k ^ L`:
`Fintype.card (cascadePath L (fun _ => k)) = leafCount (cascadeTree label L)`. This is the genuine
generator-as-polynomial-functor identity: the cascade's region/route count IS the leaf count of the
unfolded polynomial functor. General in `S`, `k`, `L`, `label`. -/
theorem cascadePath_card_eq_leafCount {S : Type u} (k L : ℕ) (label : List (Fin k) → S) :
    Fintype.card (cascadePath L (fun _ => k)) = leafCount (cascadeTree label L) := by
  rw [cascadePath_card, cascadeTree_leafCount]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **(R3a.2) THE CASCADE TRACE IS A MAP INTO THE LEAF-ADDRESS SPACE.** For any depth-`L` affine-mux
cascade `C` (`MuxHierarchy.MuxCascade`) and input `x`, the active-branch trace `MuxCascade.trace C x` —
the route/region structure of the cascade at `x` — is, by its very type, an element of
`cascadePath L C.arity`, the polynomial-functor leaf-address space. The cascade's generator IS a map
`X → cascadePath L C.arity`, i.e. into the leaf addresses of the unfolded polynomial functor; this is
the type-theoretic carrier `O` of the discovery pathway. (`rfl`: the trace's codomain is definitionally
the path type.) -/
theorem cascadeTrace_mem_cascadePath {d L : ℕ} (C : MuxHierarchy.MuxCascade d L)
    (x : Fin d → ℝ) :
    (MuxHierarchy.MuxCascade.trace C x : cascadePath L C.arity)
      = fun i => (C.layers i).gate (C.harity i) (C.runUpTo i.val x) := rfl

/-- **(R3a.2) The cascade region count is bounded by the polynomial-functor leaf-address cardinality.**
Restating `muxCascade_pieces_le_prod` through the path/leaf-address identity: the cascade's `pieceCount`
(distinct realized region traces) is at most `Fintype.card (cascadePath L C.arity)`, the cardinality of
the polynomial-functor leaf-address space. General in `d`, `L`, the cascade `C`. -/
theorem muxCascade_pieceCount_le_cascadePath_card {d L : ℕ} (C : MuxHierarchy.MuxCascade d L) :
    C.pieceCount ≤ Fintype.card (cascadePath L C.arity) := by
  rw [cascadePath_card]
  exact MuxHierarchy.muxCascade_pieces_le_prod C

end TLT.TemperedDesignLaw
