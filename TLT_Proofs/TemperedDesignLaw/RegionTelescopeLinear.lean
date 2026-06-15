/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.RegionTelescope

/-!
# The non-expansive region telescope (the clean depth bound)

The region telescope `regionEnvelope_telescope` bounds the executed/ideal gap by `rEnvBound`, the full
`∑ₖ rndₖ·∏_{j>k} lipⱼ` envelope. In the **non-expansive** regime (every ideal map `lip ≤ 1`, every local
rounding bound `rnd ≤ ρ`), that envelope collapses to `length · ρ`, exactly as the shipped global telescope
does (`execComp_envelope_linear`). This is the form both region-restricted edges cite: a depth-linear bound
with an explicit per-layer budget.

* `rLipProd_le_one` / `rEnvBound_le_length_mul_of_nonexpansive`: the non-expansive collapse of the envelope.
* `regionEnvelope_telescope_linear`: under `trajInRegions` and the non-expansive budget, the executed/ideal
  gap is at most `length · ρ`.
-/

noncomputable section

namespace TLT.TemperedDesignLaw

variable {V : Type*} [PseudoMetricSpace V]

/-- The ideal-Lipschitz product of a non-expansive stack is at most one. -/
lemma rLipProd_le_one : ∀ {Ls : List (RegionExecLayer V)}, (∀ L ∈ Ls, L.lip ≤ 1) → rLipProd Ls ≤ 1
  | [], _ => by simp [rLipProd]
  | L :: Ls, hlip => by
      rw [rLipProd]
      have hL : L.lip ≤ 1 := hlip L (List.mem_cons.mpr (Or.inl rfl))
      have htail : rLipProd Ls ≤ 1 := rLipProd_le_one (fun L' h => hlip L' (List.mem_cons.mpr (Or.inr h)))
      calc L.lip * rLipProd Ls ≤ 1 * 1 := mul_le_mul hL htail (rLipProd_nonneg Ls) (by norm_num)
        _ = 1 := by norm_num

/-- **The non-expansive envelope collapse.** When every ideal map is non-expansive (`lip ≤ 1`) and every
local rounding bound is at most `ρ`, the accumulated envelope is at most depth times `ρ`. -/
lemma rEnvBound_le_length_mul_of_nonexpansive {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ {Ls : List (RegionExecLayer V)}, (∀ L ∈ Ls, L.lip ≤ 1) → (∀ L ∈ Ls, L.rnd ≤ ρ) →
      rEnvBound Ls ≤ Ls.length * ρ
  | [], _, _ => by simp [rEnvBound]
  | L :: Ls, hlip, hrnd => by
      rw [rEnvBound, List.length_cons]
      push_cast
      have hL : L.rnd ≤ ρ := hrnd L (List.mem_cons.mpr (Or.inl rfl))
      have hlp : rLipProd Ls ≤ 1 := rLipProd_le_one (fun L' h => hlip L' (List.mem_cons.mpr (Or.inr h)))
      have htail : rEnvBound Ls ≤ (Ls.length : ℝ) * ρ :=
        rEnvBound_le_length_mul_of_nonexpansive hρ
          (fun L' h => hlip L' (List.mem_cons.mpr (Or.inr h)))
          (fun L' h => hrnd L' (List.mem_cons.mpr (Or.inr h)))
      have h1 : L.rnd * rLipProd Ls ≤ ρ :=
        (mul_le_mul hL hlp (rLipProd_nonneg Ls) hρ).trans (le_of_eq (mul_one ρ))
      calc L.rnd * rLipProd Ls + rEnvBound Ls ≤ ρ + (Ls.length : ℝ) * ρ := add_le_add h1 htail
        _ = ((Ls.length : ℝ) + 1) * ρ := by ring

/-- **The non-expansive region telescope.** Under `trajInRegions` and the non-expansive per-layer budget
(`lip ≤ 1`, `rnd ≤ ρ`), the executed/ideal composition gap is at most `length · ρ`, the depth-linear
bound both region-restricted edges consume. -/
theorem regionEnvelope_telescope_linear {Ls : List (RegionExecLayer V)} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hlip : ∀ L ∈ Ls, L.lip ≤ 1) (hrnd : ∀ L ∈ Ls, L.rnd ≤ ρ) (x : V) (htraj : trajInRegions Ls x) :
    dist (rExecComp Ls x) (rIdealComp Ls x) ≤ Ls.length * ρ :=
  (regionEnvelope_telescope Ls x htraj).trans (rEnvBound_le_length_mul_of_nonexpansive hρ hlip hrnd)

end TLT.TemperedDesignLaw
