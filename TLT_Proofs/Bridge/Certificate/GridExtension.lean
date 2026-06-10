/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# A measurable grid extension carrying a per-input error verbatim

`gridExt` extends an arbitrary `ideal` map by a finite correction supported exactly on the
pre-images, under `clamp`, of a finite family of `read` values: it equals an executed `kernel`
on each such pre-image and the clamped `ideal` everywhere else. Written as `ideal ∘ clamp` plus a
finite sum of constant-valued indicators, it is measurable termwise, agrees with `kernel` on the
matching pre-image, and stays within the per-input error bound `rnd` of `ideal ∘ clamp` everywhere.

This is the abstract measure-theoretic skeleton: `V` is the value space (a normed group, with
measurable singletons for the measurability statements) and `ι` indexes the finite family.
-/

open MeasureTheory

namespace TLT.GridExt

/-- The grid-extended map: the executed `kernel` on the pre-image, under `clamp`, of each `read i`
for `i` in the finite family `inputs`, and the clamped `ideal` elsewhere — written as `ideal ∘ clamp`
plus a finite correction supported on those pre-images. -/
noncomputable def gridExt {V ι : Type*} [NormedAddCommGroup V]
    (ideal clamp : V → V) (inputs : Finset ι) (read kernel : ι → V) (y : V) : V :=
  ideal (clamp y)
    + ∑ i ∈ inputs, Set.indicator {z | read i = clamp z} (fun _ => kernel i - ideal (read i)) y

/-- The grid extension carries the per-input error verbatim: given the bound `rnd` between `kernel i`
and `ideal (read i)` on every index (`hregime`) and distinct reads (`hinj`), `gridExt` is within `rnd`
of the clamped ideal at every input — `rnd` on the pre-images, `0` off them. -/
theorem gridExt_exec_close {V ι : Type*} [NormedAddCommGroup V]
    (ideal clamp : V → V) (inputs : Finset ι) (read kernel : ι → V) {rnd : ℝ} (hrnd : 0 ≤ rnd)
    (hregime : ∀ i ∈ inputs, dist (kernel i) (ideal (read i)) ≤ rnd)
    (hinj : ∀ i ∈ inputs, ∀ i' ∈ inputs, read i = read i' → i = i') :
    ∀ y, dist (gridExt ideal clamp inputs read kernel y) (ideal (clamp y)) ≤ rnd := by
  intro y
  rw [dist_eq_norm]
  have hg : gridExt ideal clamp inputs read kernel y - ideal (clamp y)
      = ∑ i ∈ inputs, Set.indicator {z | read i = clamp z}
          (fun _ => kernel i - ideal (read i)) y := by
    simp only [gridExt, add_sub_cancel_left]
  rw [hg]
  by_cases h : ∃ i ∈ inputs, read i = clamp y
  · obtain ⟨i0, hi0, heq0⟩ := h
    have hmem0 : y ∈ {z | read i0 = clamp z} := heq0
    have hsingle : (∑ i ∈ inputs, Set.indicator {z | read i = clamp z}
          (fun _ => kernel i - ideal (read i)) y)
        = kernel i0 - ideal (read i0) := by
      rw [Finset.sum_eq_single_of_mem i0 hi0]
      · rw [Set.indicator_of_mem hmem0]
      · intro i' hi' hne
        apply Set.indicator_of_notMem
        intro hmem
        exact hne (hinj i' hi' i0 hi0
          ((hmem : read i' = clamp y).trans heq0.symm))
    rw [hsingle, ← dist_eq_norm]
    exact hregime i0 hi0
  · have hz : (∑ i ∈ inputs, Set.indicator {z | read i = clamp z}
          (fun _ => kernel i - ideal (read i)) y) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Set.indicator_of_notMem
      intro hmem
      exact h ⟨i, hi, hmem⟩
    rw [hz, norm_zero]
    exact hrnd

/-- On the pre-image, `gridExt` IS the executed `kernel`: at any input `y` whose clamp equals a family
read `read i`, the grid-extended map equals `kernel i`. -/
theorem gridExt_eq_kernel_of_mem {V ι : Type*} [NormedAddCommGroup V]
    (ideal clamp : V → V) (inputs : Finset ι) (read kernel : ι → V)
    (hinj : ∀ i ∈ inputs, ∀ i' ∈ inputs, read i = read i' → i = i')
    {i : ι} (hi : i ∈ inputs) {y : V} (heq : read i = clamp y) :
    gridExt ideal clamp inputs read kernel y = kernel i := by
  have hmem : y ∈ {z | read i = clamp z} := heq
  have hsingle : (∑ i' ∈ inputs, Set.indicator {z | read i' = clamp z}
        (fun _ => kernel i' - ideal (read i')) y)
      = kernel i - ideal (read i) := by
    rw [Finset.sum_eq_single_of_mem i hi]
    · rw [Set.indicator_of_mem hmem]
    · intro i' hi' hne
      apply Set.indicator_of_notMem
      intro hmem'
      exact hne (hinj i' hi' i hi
        ((hmem' : read i' = clamp y).trans heq.symm))
  simp only [gridExt, hsingle, ← heq]
  abel

/-- `gridExt` is measurable: the ideal precomposed with `clamp`, plus a finite sum of indicators of
the measurable pre-images `clamp ⁻¹' {read i}` carrying constant values. -/
theorem gridExt_measurable {V ι : Type*} [NormedAddCommGroup V]
    [MeasurableSpace V] [MeasurableSingletonClass V] [MeasurableAdd₂ V]
    (ideal clamp : V → V) (inputs : Finset ι) (read kernel : ι → V)
    (hidclamp : Measurable (fun y => ideal (clamp y))) (hclamp : Measurable clamp) :
    Measurable (gridExt ideal clamp inputs read kernel) := by
  unfold gridExt
  refine Measurable.add hidclamp ?_
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.indicator measurable_const ?_
  have hset : {z : V | read i = clamp z} = clamp ⁻¹' {read i} := by
    ext z; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, eq_comm]
  rw [hset]
  exact hclamp (measurableSet_singleton _)

/-- Under full support on the union of pre-images (`hsupp`), `gridExt` agrees `P`-almost-everywhere
with the executed `kernel` on the matching read: for `P`-a.e. `y` there is a family index `i` with
`read i = clamp y` and `gridExt … y = kernel i`. -/
theorem gridExt_ae_eq_kernel {V ι : Type*} [NormedAddCommGroup V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (ideal clamp : V → V) (inputs : Finset ι) (read kernel : ι → V)
    (hclamp : Measurable clamp)
    (hinj : ∀ i ∈ inputs, ∀ i' ∈ inputs, read i = read i' → i = i')
    (P : Measure V) [IsProbabilityMeasure P]
    (hsupp : P {y | ∃ i ∈ inputs, read i = clamp y} = 1) :
    ∀ᵐ y ∂P, ∃ i ∈ inputs, read i = clamp y
      ∧ gridExt ideal clamp inputs read kernel y = kernel i := by
  have hSmeas : MeasurableSet {y : V | ∃ i ∈ inputs, read i = clamp y} := by
    have heq : {y : V | ∃ i ∈ inputs, read i = clamp y}
        = ⋃ i ∈ inputs, clamp ⁻¹' {read i} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, eq_comm,
        exists_prop]
    rw [heq]
    exact Finset.measurableSet_biUnion inputs
      (fun i _ => hclamp (measurableSet_singleton _))
  have hae : ∀ᵐ y ∂P, ∃ i ∈ inputs, read i = clamp y := by
    rw [Filter.eventually_iff, mem_ae_iff_prob_eq_one hSmeas]
    exact hsupp
  filter_upwards [hae] with y hy
  obtain ⟨i, hi, heq⟩ := hy
  exact ⟨i, hi, heq, gridExt_eq_kernel_of_mem ideal clamp inputs read kernel hinj hi heq⟩

end TLT.GridExt
