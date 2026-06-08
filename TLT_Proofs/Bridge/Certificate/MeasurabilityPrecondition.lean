/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Forward.ExecutedForward
import TLT_Proofs.Boundary.MeasurabilityCliff

/-!
# Measurability is the executed certificate's hinge

The executed generalization certificate `certified_executed_generalization_dudley` carries a
load-bearing hypothesis `hFmeas : ∀ θ, Measurable (F θ)`: the risk functional must be measurable for
the empirical-process bad event `{S | ¬ bound}` to be a measurable set, hence for the probability
bound to be a statement at all. This file exhibits the two faces of that one hypothesis on the
library's own objects, making explicit that the positive certificate and the negative cliff are not
two unrelated results but the satisfied and the violated side of measurability.

* **Satisfied (the certificate side).** The IEEE-executed transformer forward map is measurable
  (`transformerForwardMap_executed_measurable`, built on `measurable_fp32Round` — round-to-nearest is
  measurable because it is piecewise constant on Borel cells). So an honest measurable risk functional
  exists, `hFmeas` holds, and the certificate applies to the model the hardware runs.
* **Violated (the cliff side).** For the argmax-routed non-Borel witness, **no** measurable function
  has the bad event as a superlevel set (the third conjunct of the measurability cliff). So `hFmeas`
  is not merely unverified but *unsatisfiable* there: the certificate provably cannot apply.

Measurability is therefore the precondition that decides whether the guarantee exists and transfers to
hardware. The certificate lives exactly where it holds; the cliff is where it fails.

## Main results

- `executedCertificate_precondition_satisfied_and_violated` — the executed forward is measurable
  (the certificate's `hFmeas` holds) while the argmax cascade admits no measurable representing
  functional (`hFmeas` is unsatisfiable): the two faces of the certificate's measurability hinge.
-/

/-!
## References
- [57] FLT empirical-process bad event / measurability of the symmetrization interface; [51] IEEE
  binary32 round-to-nearest; [Vaswani 2017] softmax/argmax attention routing.
- Provenance: Innovation — identifying measurability as the shared precondition whose satisfaction is
  the executed certificate and whose failure is the measurability cliff.
- TLT contribution (Dhruv Gupta), `executedCertificate_precondition_satisfied_and_violated`: a single
  statement exhibiting the executed certificate's measurability hypothesis as satisfied by the rounded
  forward and unsatisfiable at the argmax cascade. Method: pair `transformerForwardMap_executed_measurable`
  with the non-representability of the non-Borel bad event (`cascadeNonInvariance`).
-/

open MeasureTheory Set
open TLT.Boundary

namespace TLT

/-- **Measurability is the executed certificate's hinge.** The certificate
`certified_executed_generalization_dudley` requires a measurable risk functional (`hFmeas`). On the
library's own objects that one precondition is:

* **satisfied** — the IEEE-executed transformer forward `T` is measurable
  (`transformerForwardMap_executed_measurable`, via `measurable_fp32Round`), so a measurable risk
  functional exists and the certificate applies; and
* **violated** — for the argmax-routed non-Borel witness `g` at every depth `L`, *no* measurable
  function `G` has the cascade bad event as its `½`-superlevel set, so `hFmeas` is unsatisfiable and no
  executed certificate is even statable there.

The positive certificate and the negative cliff are the two faces of measurability: the bound exists
exactly where the precondition holds, and the cliff is exactly where it fails. -/
theorem executedCertificate_precondition_satisfied_and_violated
    (T : RealTransformer)
    {β : Type} [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β]
    [StandardBorelSpace β] [Nonempty β] (g : β → ℝ) (hg : Continuous g)
    (h_non_borel : ¬ MeasurableSet (Set.range g)) (L : ℕ) :
    -- SATISFIED: the executed forward is measurable — the certificate's `hFmeas` holds
    ForwardMapExecutedMeasurable T ∧
    -- VIOLATED: no measurable functional represents the argmax bad event — `hFmeas` is unsatisfiable
    ¬ ∃ G : GhostPairs1 → ℝ, Measurable G ∧
        cascadeBadEvent (witnessCascade g hg) L = G ⁻¹' Set.Ici (1 / 2) := by
  refine ⟨transformerForwardMap_executed_measurable T, ?_⟩
  rintro ⟨G, hG, hEq⟩
  refine (cascadeNonInvariance (witnessCascade g hg) L h_non_borel).2 ?_
  rw [hEq]
  exact hG measurableSet_Ici

end TLT
