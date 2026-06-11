/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.HardeningCascadeDepth
import TLT_Proofs.TemperedDesignLaw.RegionForwardSlack

/-!
# Depth-`L` hardening on the ideal-side condition (cascade assembly)

The depth-`L` envelope, the `trajInRegions` discharge, and the homogeneous-replicate collapse now compose
into one statement whose only hypothesis is the *ideal-side* slack `idealDeep`:

* `hardeningCascade_depth_of_idealDeep` — for a non-expansive region-exec layer repeated `L` times, if the
  ideal trajectory stays deep in the regions (`idealDeep`), the executed/ideal composition gap is at most
  `L · rnd`.

This is the cascade-to-depth-`L` object the literal binding instantiates: with the layer the tempered
hardening layer, `rnd = (k−1)·exp(−β·g)·D`, and `idealDeep` reduced (via `marginInterior_of_margin_slack`)
to the ideal trajectory's routing margins exceeding `g` by the envelope's slack, the gap between the soft
mixture cascade and the hard route cascade is `≤ L·(k−1)·exp(−β·g)·D`. The proof is the composition of the
two real lemmas — the forward-error discharge and the homogeneous depth collapse — and carries no new
content beyond them. -/

noncomputable section

namespace TLT.TemperedDesignLaw

variable {V : Type*} [PseudoMetricSpace V]

/-- **Depth-`L` hardening from the ideal-side slack.** A non-expansive layer (`lip ≤ 1`, `rnd ≥ 0`) repeated
`L` times: if the ideal trajectory stays deep in the regions, the executed/ideal composition gap is at most
`L · rnd`. Composition of `regionForward_slack` (discharge `trajInRegions` from `idealDeep`) and
`rExecComp_replicate_le` (homogeneous depth collapse). -/
theorem hardeningCascade_depth_of_idealDeep {hl : RegionExecLayer V} (hlip : hl.lip ≤ 1)
    (hrnd0 : 0 ≤ hl.rnd) (L : ℕ) (x : V) (hdeep : idealDeep (List.replicate L hl) x 0) :
    dist (rExecComp (List.replicate L hl) x) (rIdealComp (List.replicate L hl) x) ≤ L * hl.rnd :=
  rExecComp_replicate_le hlip hrnd0 L x
    (regionForward_slack (List.replicate L hl) x x 0 (le_of_eq (dist_self x)) hdeep)

end TLT.TemperedDesignLaw
