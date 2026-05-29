/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Tame.SigmaCompactParam
import FLT_Proofs.Theorem.BorelAnalyticSeparation

/-!
# Tame bad-event Borelness: the singleton bad event is Borel iff the set is

The wild half (`singleton_badEvent_not_measurable`) shows the singleton-class bad event
`singletonBadEvent A` is **non**-Borel when `A` is non-Borel.  This file proves the **tame
converse**: when `A` is Borel, `singletonBadEvent A` is Borel — closing the sharp
characterization `MeasurableSet (singletonBadEvent A) ↔ MeasurableSet A`.

Composed with the σ-compact range reflection
(`measurableSet_range_of_continuous_of_sigmaCompact`), this upgrades the tame side of the
measurability dichotomy from a *score-range* statement to the genuine *bad-event* statement:
**over a σ-compact parameter space the singleton-class empirical-process bad event is Borel**
(`singletonBadEvent_measurable_of_sigmaCompact`).  The wild pathology therefore strictly
requires a non-σ-compact parameter space — at the bad-event level, not merely the score range.

## Grounding: Krapp–Wirth (2024)

*Measurability in the Fundamental Theorem of Statistical Learning* (L. S. Krapp, with an
appendix by L. Wirth), arXiv:2410.10243.  Krapp and Wirth isolate the measurability
assumption tacit in every proof of the Fundamental Theorem of Statistical Learning: the
uniform-convergence map `U : Zᵐ → [0,1]`, `z ↦ sup_{h ∈ H} |er_D(h) − êr_z(h)|`, must be
measurable, so that the empirical-process bad event `U⁻¹([0,ε]) ∈ Σ_Zᵐ` (their Def. 2.4).
They stress this is **not** automatic — `U` can fail to be measurable (their Example A.13) —
and call a class *well-behaved* exactly when it holds (§A.2).

Our `singletonBadEvent A` is such a bad event (at `m = 1`).  The wild
`singleton_badEvent_not_measurable` is a concrete instance of their Example A.13 (the
requirement fails); the tame theorems above are the converse guarantee.  Their sufficient
conditions for well-behavedness — countability (Rmk A.4), *universal separability* via a
countable pointwise-dense `H₀ ⊆ H` (Def. A.5 / Lemma A.6, after Dudley), and *permissibility*
(Pollard) — all fail for `singletonClassOn` over a non-Borel range, which is *why* its bad
event escapes measurability; over a Borel range it is recovered.  We sharpen their
qualitative "well-behaved" into the exact equivalence
`MeasurableSet (singletonBadEvent A) ↔ MeasurableSet A` (`singletonBadEvent_measurableSet_iff`).

The general argmax / `FiniteCellScoreRouter` ("AK") direction grounds in their §A.3 (*Cells*):
in an o-minimal structure every definable set is a finite union of cells, and **every cell is
Borel** (their Lemma A.9).  The proof is an induction on dimension — points `{r}` and intervals
`(a,b)` are Borel; for definable continuous `f, g` the graph `Γ(f) = T_f⁻¹{0}` and the band
`(f,g)_X = T_g⁻¹(−∞,0) ∩ T_h⁻¹(0,∞)` are Borel, where `T_f(x,r) = f(x) − r`.  A finite-head
argmax router partitions inputs into finitely many such cells, so its routing — and hence its
bad event — is Borel; this is the proof template for `FiniteCellScoreRouter` tame Borelness
(their Thm 4.7 covers ReLU/sigmoid networks over o-minimal expansions of ℝ).
-/

namespace TLT.Tame

open MeasureTheory Set

/-- `planarWitnessEvent A` is the intersection of `Prod.snd ⁻¹' A` with the off-diagonal. -/
private lemma planarWitnessEvent_eq_inter (A : Set ℝ) :
    planarWitnessEvent A = (Prod.snd ⁻¹' A) ∩ {q : ℝ × ℝ | q.1 ≠ q.2} := by
  ext q; simp [planarWitnessEvent, and_comm]

/-- **Tame planar witness.**  If `A` is measurable, so is `planarWitnessEvent A` — the exact
positive-direction counterpart of `planarWitnessEvent_not_measurable`. -/
theorem planarWitnessEvent_measurable (A : Set ℝ) (hA : MeasurableSet A) :
    MeasurableSet (planarWitnessEvent A) := by
  rw [planarWitnessEvent_eq_inter]
  exact (measurable_snd hA).inter
    ((isClosed_eq continuous_fst continuous_snd).measurableSet.compl)

/-- **Tame singleton bad event.**  If `A` is measurable, the singleton-class bad event is
Borel — the preimage of the (now Borel) planar witness under the measurable
`samplePair1ToPlane`.  Converse of `singleton_badEvent_not_measurable`. -/
theorem singletonBadEvent_measurable (A : Set ℝ) (hA : MeasurableSet A) :
    MeasurableSet (singletonBadEvent A) := by
  rw [singleton_badEvent_eq_preimage_planar A]
  exact (planarWitnessEvent_measurable A hA).preimage
    (Measurable.prod ((measurable_pi_apply 0).comp measurable_fst)
      ((measurable_pi_apply 0).comp measurable_snd))

/-- **Sharp characterization.**  The singleton-class bad event is Borel **iff** the underlying
set is Borel.  The `←` direction is the tame result above; the `→` direction is the
contrapositive of the wild `singleton_badEvent_not_measurable`. -/
theorem singletonBadEvent_measurableSet_iff (A : Set ℝ) :
    MeasurableSet (singletonBadEvent A) ↔ MeasurableSet A := by
  refine ⟨fun h => ?_, singletonBadEvent_measurable A⟩
  by_contra hA
  exact singleton_badEvent_not_measurable A hA h

/-- **Tame bad-event Borelness over a σ-compact parameter space.**  For a continuous score
map `g : β → ℝ` over a σ-compact `β`, the singleton-class empirical-process bad event on
`Set.range g` is Borel.  This is the genuine tame counterpart of the wild non-Borel witness
*at the bad-event level* (not merely the score range): the wild pathology strictly requires a
non-σ-compact parameter space. -/
theorem singletonBadEvent_measurable_of_sigmaCompact
    {β : Type*} [TopologicalSpace β] [SigmaCompactSpace β] {g : β → ℝ} (hg : Continuous g) :
    MeasurableSet (singletonBadEvent (Set.range g)) :=
  singletonBadEvent_measurable (Set.range g)
    (measurableSet_range_of_continuous_of_sigmaCompact hg)

end TLT.Tame
