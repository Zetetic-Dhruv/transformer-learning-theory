/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Fp32.RelativeUlpAndSummation
import NN.Floats.IEEEExec.Exec32
import NN.Spec.Core.TensorReductionShape
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Range

/-!
# fp32 sequential summation: the left-fold envelope and its bridges

The transformer's reductions (matrix-multiply dot products, layer-normalization sums) accumulate
left-to-right. This file gives the **left-fold** fp32 summation `fp32Foldl` (matching that accumulator
order — the counterpart to `FP32Channel.fp32Sum`'s right fold), its affine error envelope on the
binary32 normal range, and two bridges that connect it to the literal execution:

- `toReal_foldl_add` — the `toReal` of the literal `IEEE32Exec` left-fold equals `fp32Foldl` of the
  `toReal`-mapped entries (finite branch), so the executed reduction *is* the real-valued `fp32Foldl`.
- `tensorFoldlSpec_vec_eq_foldl` — the spec tensor reduction `tensorFoldlSpec` over a vector equals the
  `List.foldl` of its entries, so the layer-normalization reduction reuses `toReal_foldl_add`.

## Main results

- `fp32Foldl` / `fp32FoldlErrorBudget` / `fp32Foldl_error_le` — the left-fold and its normal-range
  affine error envelope.
- `toReal_foldl_add` — the literal `IEEE32Exec` reduction equals `fp32Foldl ∘ toReal`.
- `tensorFoldlSpec_vec_eq_foldl` — the spec vector reduction is a `List.foldl`.
- `fp32FoldlErrorBudget_closed_form` — the closed-form (backward-error) bound on the budget,
  `≤ u·(n·|acc| + (n+1)·∑ᵢ|xᵢ|) / (1 − n·u)`.
- `ie32_foldl_envelope` / `tensorFoldlSpec_ie32_envelope` / `ie32_foldl_closed_envelope` — the executed
  reduction is enveloped by the rounding budget, and by the closed-form input-magnitude bound.
-/

/-!
## References
- [43] §4 sequential-summation backward error (`γₙ=nu/(1−nu)`); [44] ulp; [50] format; [53]
  IEEE32Exec reduction.
- Provenance: Classical-instantiation (closed-form backward error = [43]); the `toReal_foldl_add` /
  `tensorFoldlSpec_vec_eq_foldl` execution/spec bridges are TLT glue to the literal kernel.
-/

open TorchLean.Floats (neuralMagnitude neuralBpow binaryRadix)
open TorchLean.Floats.IEEE754
open TorchLean.Floats.IEEE754.IEEE32Exec

/-- The fp32 (round-to-nearest) **left**-fold sum: each partial sum is rounded, accumulating
left-to-right — the order in which the literal forward reduces. -/
noncomputable def fp32Foldl : ℝ → List ℝ → ℝ
  | acc, [] => acc
  | acc, x :: xs => fp32Foldl (fp32Round (acc + x)) xs

/-- Every accumulation step `acc + x` of the left fold lands in the binary32 normal range. -/
def Fp32FoldlNormal : ℝ → List ℝ → Prop
  | _, [] => True
  | acc, x :: xs => (acc + x ≠ 0 ∧ (-125 : ℤ) ≤ neuralMagnitude binaryRadix (acc + x))
                    ∧ Fp32FoldlNormal (fp32Round (acc + x)) xs

/-- The accumulated rounding-error budget of the fp32 left fold. -/
noncomputable def fp32FoldlErrorBudget : ℝ → List ℝ → ℝ
  | _, [] => 0
  | acc, x :: xs => neuralBpow binaryRadix (-24) * (|acc| + |x|)
                    + fp32FoldlErrorBudget (fp32Round (acc + x)) xs

/-- **Left-fold normal-range summation enclosure.** When every accumulation step stays in the binary32
normal range, the fp32 left fold differs from the exact running sum `acc + xs.sum` by at most the
accumulated rounding-error budget. -/
theorem fp32Foldl_error_le :
    ∀ (acc : ℝ) (xs : List ℝ), Fp32FoldlNormal acc xs →
      |fp32Foldl acc xs - (acc + xs.sum)| ≤ fp32FoldlErrorBudget acc xs := by
  intro acc xs
  induction xs generalizing acc with
  | nil => intro _; simp [fp32Foldl, fp32FoldlErrorBudget]
  | cons x xs ih =>
    intro h
    obtain ⟨⟨hne, hnorm⟩, htail⟩ := h
    calc |fp32Foldl acc (x :: xs) - (acc + (x :: xs).sum)|
        = |(fp32Foldl (fp32Round (acc + x)) xs - (fp32Round (acc + x) + xs.sum))
            + (fp32Round (acc + x) - (acc + x))| := by
          simp only [fp32Foldl, List.sum_cons]; congr 1; ring
      _ ≤ |fp32Foldl (fp32Round (acc + x)) xs - (fp32Round (acc + x) + xs.sum)|
            + |fp32Round (acc + x) - (acc + x)| := abs_add_le _ _
      _ ≤ fp32FoldlErrorBudget (fp32Round (acc + x)) xs
            + neuralBpow binaryRadix (-24) * (|acc| + |x|) := by
          gcongr
          · exact ih (fp32Round (acc + x)) htail
          · exact fp32_addBound_on_normal acc x hne hnorm
      _ = fp32FoldlErrorBudget acc (x :: xs) := by
          simp only [fp32FoldlErrorBudget]; ring

/-- Every accumulation step of the literal `IEEE32Exec` left fold stays finite. -/
def IE32FoldlFinite : IEEE32Exec → List IEEE32Exec → Prop
  | _, [] => True
  | acc, x :: xs => isFinite (acc + x) = true ∧ IE32FoldlFinite (acc + x) xs

/-- **The fp32 reduction bridge.** When every step stays finite, the `toReal` of the literal
`IEEE32Exec` left-fold sum equals the fp32-rounded real left fold of the `toReal` entries — binding the
executable reduction to the real-valued `fp32Foldl` model (hence to its envelope `fp32Foldl_error_le`). -/
theorem toReal_foldl_add :
    ∀ (acc : IEEE32Exec) (xs : List IEEE32Exec), IE32FoldlFinite acc xs →
      toReal (xs.foldl (· + ·) acc) = fp32Foldl (toReal acc) (xs.map toReal) := by
  intro acc xs
  induction xs generalizing acc with
  | nil => intro _; simp [fp32Foldl]
  | cons x xs ih =>
    intro h
    obtain ⟨hfin, htail⟩ := h
    have hstep : toReal (acc + x) = fp32Round (toReal acc + toReal x) :=
      toReal_add_eq_fp32Round_of_isFinite acc x hfin
    simp only [List.foldl_cons, List.map_cons, fp32Foldl]
    rw [ih (acc + x) htail, hstep]

section TensorFold

open Spec Spec.Tensor

variable {α : Type} [Add α]

/-- Folding over a scalar tensor adds its value. -/
private lemma tfold_scalar (acc : α) (s : Tensor α .scalar) :
    tensorFoldlSpec (· + ·) acc s = acc + Tensor.toScalar s := by
  cases s with
  | scalar v => simp [tensorFoldlSpec, Tensor.toScalar]

/-- The inner loop of `tensorFoldlSpec` over a scalar-vector is a `List.foldl` of the entries. -/
private lemma go_foldl {n : ℕ} (cols : Fin n → Tensor α .scalar) :
    ∀ (fuel i : ℕ) (acc : α), n - i ≤ fuel →
      tensorFoldlSpec.go (· + ·) n .scalar cols i acc
        = (((List.finRange n).drop i).map (fun j => Tensor.toScalar (cols j))).foldl (· + ·) acc := by
  intro fuel
  induction fuel with
  | zero =>
    intro i acc hi
    have hni : ¬ i < n := by grind
    rw [tensorFoldlSpec.go]
    simp only [hni, dif_neg, not_false_iff]
    rw [List.drop_eq_nil_of_le (by rw [List.length_finRange]; grind)]
    simp
  | succ f ih =>
    intro i acc hi
    by_cases h : i < n
    · rw [tensorFoldlSpec.go]
      simp only [h, dif_pos]
      rw [tfold_scalar, ih (i + 1) (acc + Tensor.toScalar (cols ⟨i, h⟩)) (by grind)]
      conv_rhs => rw [List.drop_eq_getElem_cons (by rw [List.length_finRange]; exact h)]
      simp [List.getElem_finRange]
    · rw [tensorFoldlSpec.go]
      simp only [h, dif_neg, not_false_iff]
      rw [List.drop_eq_nil_of_le (by rw [List.length_finRange]; grind)]
      simp

/-- The spec tensor reduction `tensorFoldlSpec` (= `sumSpec` accumulator order) of a scalar-vector
equals the `List.foldl` of its entries — bridging the layer-normalization reduction order to the
real-valued `fp32Foldl` model (via `toReal_foldl_add`). -/
theorem tensorFoldlSpec_vec_eq_foldl {n : ℕ} (cols : Fin n → Tensor α .scalar) (acc : α) :
    tensorFoldlSpec (· + ·) acc (Tensor.dim cols)
      = (List.ofFn (fun j => Tensor.toScalar (cols j))).foldl (· + ·) acc := by
  rw [show tensorFoldlSpec (· + ·) acc (Tensor.dim cols)
        = tensorFoldlSpec.go (· + ·) n .scalar cols 0 acc by simp [tensorFoldlSpec]]
  rw [go_foldl cols n 0 acc (by grind), List.drop_zero, List.ofFn_eq_map]

end TensorFold

section ClosedFormBudget

/-! ### Closed-form (input-magnitude) bound on the rounding budget

The error budget `fp32FoldlErrorBudget` is recursive: a sum over steps of `u·(|accₖ| + |xₖ|)`, where
`accₖ` is the running fp32 partial sum. The classic backward-error argument bounds it by a closed form
in the input magnitudes alone: with `u = β^(-24)` the unit roundoff, `n` the length and `S = ∑ᵢ|xᵢ|`,

`fp32FoldlErrorBudget acc xs ≤ u·(n·|acc| + (n+1)·S) / (1 − n·u)`  (when `n·u < 1`).

The crux is the running-sum bound `|accₖ| ≤ |acc| + S + budget` (each fp32 partial sum is within the
exact running sum plus the accumulated error), which closes a self-referential inequality on the
budget. -/

/-- The rounding budget is nonnegative. -/
private lemma fp32FoldlErrorBudget_nonneg (acc : ℝ) (xs : List ℝ) :
    0 ≤ fp32FoldlErrorBudget acc xs := by
  induction xs generalizing acc with
  | nil => simp [fp32FoldlErrorBudget]
  | cons x xs ih =>
    simp only [fp32FoldlErrorBudget]
    have hu : 0 ≤ neuralBpow binaryRadix (-24) := neuralBpow.nonneg binaryRadix (-24)
    have h1 : 0 ≤ neuralBpow binaryRadix (-24) * (|acc| + |x|) := by positivity
    linarith [ih (fp32Round (acc + x))]

/-- The budget splits additively along list concatenation (the second piece accumulates from the fp32
running sum of the first). -/
private lemma fp32FoldlErrorBudget_append (acc : ℝ) (xs ys : List ℝ) :
    fp32FoldlErrorBudget acc (xs ++ ys)
      = fp32FoldlErrorBudget acc xs + fp32FoldlErrorBudget (fp32Foldl acc xs) ys := by
  induction xs generalizing acc with
  | nil => simp [fp32FoldlErrorBudget, fp32Foldl]
  | cons x xs ih =>
    simp only [List.cons_append, fp32FoldlErrorBudget, fp32Foldl]
    rw [ih (fp32Round (acc + x))]; ring

/-- The budget of a prefix is at most the budget of the whole list. -/
private lemma fp32FoldlErrorBudget_take_le (acc : ℝ) (xs : List ℝ) (k : ℕ) :
    fp32FoldlErrorBudget acc (xs.take k) ≤ fp32FoldlErrorBudget acc xs := by
  conv_rhs => rw [← List.take_append_drop k xs, fp32FoldlErrorBudget_append]
  linarith [fp32FoldlErrorBudget_nonneg (fp32Foldl acc (xs.take k)) (xs.drop k)]

/-- The normal-range condition is inherited by a left segment. -/
private lemma fp32FoldlNormal_append_left (acc : ℝ) (xs ys : List ℝ) :
    Fp32FoldlNormal acc (xs ++ ys) → Fp32FoldlNormal acc xs := by
  induction xs generalizing acc with
  | nil => intro _; trivial
  | cons x xs ih =>
    intro h
    rw [List.cons_append] at h
    obtain ⟨hcond, htail⟩ := h
    exact ⟨hcond, ih (fp32Round (acc + x)) htail⟩

/-- The normal-range condition is inherited by every prefix. -/
private lemma fp32FoldlNormal_take (acc : ℝ) (xs : List ℝ) (k : ℕ) :
    Fp32FoldlNormal acc xs → Fp32FoldlNormal acc (xs.take k) := by
  intro h
  apply fp32FoldlNormal_append_left acc (xs.take k) (xs.drop k)
  rwa [List.take_append_drop]

/-- The magnitude of a list sum is at most the sum of magnitudes. -/
private lemma abs_list_sum_le (l : List ℝ) : |l.sum| ≤ (l.map (fun x => |x|)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons, List.map_cons]
    calc |x + xs.sum| ≤ |x| + |xs.sum| := abs_add_le _ _
      _ ≤ |x| + (xs.map (fun x => |x|)).sum := by linarith

/-- The magnitude-sum of a prefix is at most the magnitude-sum of the whole list. -/
private lemma map_abs_sum_take_le (l : List ℝ) (k : ℕ) :
    ((l.take k).map (fun x => |x|)).sum ≤ (l.map (fun x => |x|)).sum := by
  conv_rhs => rw [← List.take_append_drop k l, List.map_append, List.sum_append]
  have h0 : 0 ≤ ((l.drop k).map (fun x => |x|)).sum := by
    apply List.sum_nonneg; intro y hy
    simp only [List.mem_map] at hy; obtain ⟨z, _, rfl⟩ := hy; exact abs_nonneg z
  linarith

/-- **The running-sum bound.** Every fp32 partial sum is within `|acc| + S + budget` of the origin:
it stays within the exact running sum (magnitude `≤ |acc| + S`) plus the accumulated rounding error
(`≤ budget`). -/
private lemma fp32Foldl_take_abs_le (acc : ℝ) (xs : List ℝ) (hnorm : Fp32FoldlNormal acc xs) (k : ℕ) :
    |fp32Foldl acc (xs.take k)|
      ≤ |acc| + (xs.map (fun x => |x|)).sum + fp32FoldlErrorBudget acc xs := by
  have herr := fp32Foldl_error_le acc (xs.take k) (fp32FoldlNormal_take acc xs k hnorm)
  have hbud := fp32FoldlErrorBudget_take_le acc xs k
  have hsum : |acc + (xs.take k).sum| ≤ |acc| + (xs.map (fun x => |x|)).sum := by
    calc |acc + (xs.take k).sum| ≤ |acc| + |(xs.take k).sum| := abs_add_le _ _
      _ ≤ |acc| + ((xs.take k).map (fun x => |x|)).sum := by linarith [abs_list_sum_le (xs.take k)]
      _ ≤ |acc| + (xs.map (fun x => |x|)).sum := by linarith [map_abs_sum_take_le xs k]
  calc |fp32Foldl acc (xs.take k)|
      = |(fp32Foldl acc (xs.take k) - (acc + (xs.take k).sum)) + (acc + (xs.take k).sum)| := by ring_nf
    _ ≤ |fp32Foldl acc (xs.take k) - (acc + (xs.take k).sum)| + |acc + (xs.take k).sum| := abs_add_le _ _
    _ ≤ |acc| + (xs.map (fun x => |x|)).sum + fp32FoldlErrorBudget acc xs := by linarith

/-- The budget is at most `u·n·C + u·S` whenever `C` uniformly bounds every fp32 partial sum. -/
private lemma fp32FoldlErrorBudget_le_of_bound (acc : ℝ) (xs : List ℝ) (C : ℝ)
    (hC : ∀ k, |fp32Foldl acc (xs.take k)| ≤ C) :
    fp32FoldlErrorBudget acc xs
      ≤ neuralBpow binaryRadix (-24) * ((xs.length : ℝ) * C)
        + neuralBpow binaryRadix (-24) * (xs.map (fun x => |x|)).sum := by
  induction xs generalizing acc with
  | nil => simp [fp32FoldlErrorBudget]
  | cons x xs ih =>
    simp only [fp32FoldlErrorBudget, List.length_cons, List.map_cons, List.sum_cons, Nat.cast_add,
      Nat.cast_one]
    have hu : 0 ≤ neuralBpow binaryRadix (-24) := neuralBpow.nonneg binaryRadix (-24)
    have hacc : |acc| ≤ C := by have h0 := hC 0; simpa [fp32Foldl] using h0
    have hCtail : ∀ k, |fp32Foldl (fp32Round (acc + x)) (xs.take k)| ≤ C := by
      intro k; have hk := hC (k + 1); simpa [List.take_succ_cons, fp32Foldl] using hk
    have htail := ih (fp32Round (acc + x)) hCtail
    have hxC : neuralBpow binaryRadix (-24) * (|acc| + |x|)
             ≤ neuralBpow binaryRadix (-24) * (C + |x|) :=
      mul_le_mul_of_nonneg_left (by linarith) hu
    nlinarith [htail, hxC]

/-- **Closed-form rounding-budget bound (backward error).** When `n·u < 1` (`u = β^(-24)`, `n = length`),
the recursive error budget is bounded by a closed form in the input magnitudes:
`budget ≤ u·(n·|acc| + (n+1)·∑ᵢ|xᵢ|) / (1 − n·u)`. Solves the self-referential inequality obtained
from the running-sum bound. -/
theorem fp32FoldlErrorBudget_closed_form (acc : ℝ) (xs : List ℝ)
    (hnorm : Fp32FoldlNormal acc xs)
    (hun : neuralBpow binaryRadix (-24) * (xs.length : ℝ) < 1) :
    fp32FoldlErrorBudget acc xs
      ≤ neuralBpow binaryRadix (-24)
          * ((xs.length : ℝ) * |acc| + ((xs.length : ℝ) + 1) * (xs.map (fun x => |x|)).sum)
        / (1 - neuralBpow binaryRadix (-24) * (xs.length : ℝ)) := by
  have hbound := fp32FoldlErrorBudget_le_of_bound acc xs _
    (fun k => fp32Foldl_take_abs_le acc xs hnorm k)
  have hpos : 0 < 1 - neuralBpow binaryRadix (-24) * (xs.length : ℝ) := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith [hbound, neuralBpow.nonneg binaryRadix (-24)]

end ClosedFormBudget

section ExecutedEnvelope

open Spec Spec.Tensor

/-- **The executed reduction envelope.** The literal `IEEE32Exec` left-fold reduction differs from the
exact real sum of its `toReal` entries by at most the accumulated rounding budget — the execution
bridge `toReal_foldl_add` composed with the affine envelope `fp32Foldl_error_le`. This is the form that
supplies the rounding envelope for a single transformer reduction (a dot product or a layer-norm sum). -/
theorem ie32_foldl_envelope (acc : IEEE32Exec) (xs : List IEEE32Exec)
    (hfin : IE32FoldlFinite acc xs)
    (hnorm : Fp32FoldlNormal (toReal acc) (xs.map toReal)) :
    |toReal (xs.foldl (· + ·) acc) - (toReal acc + (xs.map toReal).sum)|
      ≤ fp32FoldlErrorBudget (toReal acc) (xs.map toReal) := by
  rw [toReal_foldl_add acc xs hfin]
  exact fp32Foldl_error_le (toReal acc) (xs.map toReal) hnorm

/-- **The executed spec-reduction envelope.** The literal `IEEE32Exec` spec vector reduction
`tensorFoldlSpec` (the layer-normalization / matrix-multiply accumulator order) differs from the exact
real sum of its entries by at most the accumulated rounding budget — `tensorFoldlSpec_vec_eq_foldl`
composed with `ie32_foldl_envelope`. -/
theorem tensorFoldlSpec_ie32_envelope {n : ℕ} (cols : Fin n → Tensor IEEE32Exec .scalar)
    (acc : IEEE32Exec)
    (hfin : IE32FoldlFinite acc (List.ofFn (fun j => Tensor.toScalar (cols j))))
    (hnorm : Fp32FoldlNormal (toReal acc)
      ((List.ofFn (fun j => Tensor.toScalar (cols j))).map toReal)) :
    |toReal (tensorFoldlSpec (· + ·) acc (Tensor.dim cols))
        - (toReal acc + ((List.ofFn (fun j => Tensor.toScalar (cols j))).map toReal).sum)|
      ≤ fp32FoldlErrorBudget (toReal acc)
          ((List.ofFn (fun j => Tensor.toScalar (cols j))).map toReal) := by
  rw [tensorFoldlSpec_vec_eq_foldl]
  exact ie32_foldl_envelope acc _ hfin hnorm

/-- **The executed reduction within a closed-form input-magnitude envelope.** Combining the executed
reduction envelope with the backward-error bound: the literal `IEEE32Exec` reduction differs from the
exact real sum by at most `u·(n·|acc| + (n+1)·∑ᵢ|xᵢ|) / (1 − n·u)` — a concrete bound in the input
magnitudes, hence a usable rounding envelope `ε` for `executed_risk_transfer`. -/
theorem ie32_foldl_closed_envelope (acc : IEEE32Exec) (xs : List IEEE32Exec)
    (hfin : IE32FoldlFinite acc xs)
    (hnorm : Fp32FoldlNormal (toReal acc) (xs.map toReal))
    (hun : neuralBpow binaryRadix (-24) * (xs.length : ℝ) < 1) :
    |toReal (xs.foldl (· + ·) acc) - (toReal acc + (xs.map toReal).sum)|
      ≤ neuralBpow binaryRadix (-24)
          * ((xs.length : ℝ) * |toReal acc|
              + ((xs.length : ℝ) + 1) * ((xs.map toReal).map (fun x => |x|)).sum)
        / (1 - neuralBpow binaryRadix (-24) * (xs.length : ℝ)) := by
  refine (ie32_foldl_envelope acc xs hfin hnorm).trans ?_
  have h := fp32FoldlErrorBudget_closed_form (toReal acc) (xs.map toReal) hnorm
    (by rwa [List.length_map])
  rwa [List.length_map] at h

end ExecutedEnvelope
