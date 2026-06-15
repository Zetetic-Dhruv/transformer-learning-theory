/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.HardeningCascade

/-!
# The depth-`L` envelope of a homogeneous region cascade (TD3-depth, named)

Specialising the non-expansive region telescope to a *homogeneous* stack (depth `L` of one repeated
region-exec layer) collapses the envelope to `L · rnd`:

* `rExecComp_replicate_le`: for a non-expansive layer (`lip ≤ 1`, `rnd ≥ 0`), if the executed trajectory
  stays in the per-copy regions, then `dist (execComp …) (idealComp …) ≤ L · rnd`.

**TD3-depth** is the instantiation at the tempered hardening layer: with
`layer := temperedHardeningRegionLayer A hk ρ val g D Lsoft …` (so `layer.rnd = (k−1)·exp(−β·g)·D` and
`layer.lip = Lsoft`), whenever the soft maps are non-expansive (`Lsoft ≤ 1`) and the executed (hard-route)
trajectory stays in the margin interiors `{γ ≥ g}`, the depth-`L` hardening envelope reads

> `dist (hardCascade x) (softCascade x) ≤ L · (k−1)·exp(−β·g)·D`,

linear in depth and margin-exponential in the sharpness `β`, the `β`-edge twin of the depth-linear rounding
envelope `length · ρ` at the `u`-edge.
-/

noncomputable section

namespace TLT.TemperedDesignLaw

variable {V : Type*} [PseudoMetricSpace V]

/-- **The homogeneous depth-`L` region envelope.** For a non-expansive region-exec layer repeated `L`
times, if the executed trajectory stays in the regions, the executed/ideal composition gap is at most
`L · rnd`. The depth-linear collapse of the region telescope; TD3-depth is the tempered instantiation. -/
theorem rExecComp_replicate_le {layer : RegionExecLayer V} (hlip : layer.lip ≤ 1)
    (hrnd0 : 0 ≤ layer.rnd) (L : ℕ) (x : V)
    (htraj : trajInRegions (List.replicate L layer) x) :
    dist (rExecComp (List.replicate L layer) x) (rIdealComp (List.replicate L layer) x)
      ≤ L * layer.rnd := by
  have h := regionEnvelope_telescope_linear (Ls := List.replicate L layer) hrnd0
    (fun L' hL' => by rw [(List.mem_replicate.mp hL').2]; exact hlip)
    (fun L' hL' => le_of_eq (by rw [(List.mem_replicate.mp hL').2])) x htraj
  rwa [List.length_replicate] at h

end TLT.TemperedDesignLaw
