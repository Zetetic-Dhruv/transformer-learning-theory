/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.Bridge.Certificate.CertifiedRiskBound
import TLT_Proofs.Bridge.Spec.TransformerObjectVocabulary

/-!
# The certified executed-risk bound, as a discharged resolution

For the executed (IEEE binary32) forward pass presented as a composition of `ExecLayer`s `Ls`, the
executed true risk is bounded by the executed empirical risk plus a statistical `capacity` term plus
`2·L·envBound` — every additional term computable from the layer data. The statistical capacity is the
generalization bound of the ideal (real-arithmetic) forward map; the rounding envelope carries the
bound from the ideal to the executed model.

This file states the executed certificate as a property and discharges it from the ideal-side capacity
bound via the rounding-transfer assembly (`certifiedRiskBound_of_idealRisk`). The capacity bound for
the ideal forward map is the input of the chaining (Dudley entropy-integral) analysis; here it is the
explicit hypothesis `hCapacity`, so that the certificate is a theorem about the *executed* model — the
distinctive content — relative to that ideal-side analysis.

## Main results

- `CertifiedExecutedRiskBound` — the executed risk certificate as a property of the executed forward.
- `certifiedExecutedRiskBound_holds` — the certificate holds given the ideal-side capacity bound.
- `certifiedExecutedRiskBound_resolution` — the certificate packaged as a discharged `Resolution`.
-/

/-!
## References
- [22] Lipschitz-loss transfer; [36][54] ideal capacity; [56] verified-ML context.
- Provenance: Innovation (packaging) — names the executed-certificate property + discharged
  Resolution; same executed-transfer content as `CertifiedRiskBound`.
-/

open MeasureTheory

namespace TLT

variable {V : Type*} [PseudoMetricSpace V]

/-- **The certified executed-risk bound.** For the executed forward presented by the layer list `Ls`
and an `L`-Lipschitz loss `ℓ`, the executed true risk is within `capacity + 2·L·envBound Ls` of the
executed empirical risk over a size-`n` sample. -/
def CertifiedExecutedRiskBound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Ls : List (ExecLayer V)) (input : Ω → V) {n : ℕ} (xs : Fin n → V) (ℓ : V → ℝ)
    (L capacity : ℝ) : Prop :=
  (∫ x, ℓ (execComp Ls (input x)) ∂μ)
    ≤ (1 / (n : ℝ)) * ∑ i, ℓ (execComp Ls (xs i)) + capacity + 2 * (L * envBound Ls)

/-- The executed risk certificate holds given the **ideal-side** generalization (capacity) bound. The
proof is the rounding-transfer assembly: the executed true and empirical risks are each within
`L·envBound` of their ideal counterparts, so the ideal capacity bound transfers with a `2·L·envBound`
correction. The capacity term `capacity` is supplied by the chaining (Dudley entropy-integral)
analysis of the ideal forward map and may be taken to be its tight value `12√2·σ·entropyIntegral`. -/
theorem certifiedExecutedRiskBound_holds {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Ls : List (ExecLayer V)) (input : Ω → V) {n : ℕ} (hn : 0 < n)
    (xs : Fin n → V) (ℓ : V → ℝ) {L capacity : ℝ} (hL0 : 0 ≤ L)
    (hLip : ∀ p q, |ℓ p - ℓ q| ≤ L * dist p q)
    (hintF : Integrable (fun x => ℓ (idealComp Ls (input x))) μ)
    (hintG : Integrable (fun x => ℓ (execComp Ls (input x))) μ)
    (hCapacity : (∫ x, ℓ (idealComp Ls (input x)) ∂μ)
        ≤ (1 / (n : ℝ)) * ∑ i, ℓ (idealComp Ls (xs i)) + capacity) :
    CertifiedExecutedRiskBound μ Ls input xs ℓ L capacity :=
  certifiedRiskBound_of_idealRisk Ls input hn xs ℓ hL0 hLip hintF hintG hCapacity

/-- The certified executed-risk bound, packaged as a discharged `Resolution` of the executed-model
presentation `Ls`. -/
noncomputable def certifiedExecutedRiskBound_resolution {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Ls : List (ExecLayer V)) (input : Ω → V) {n : ℕ}
    (hn : 0 < n) (xs : Fin n → V) (ℓ : V → ℝ) {L capacity : ℝ} (hL0 : 0 ≤ L)
    (hLip : ∀ p q, |ℓ p - ℓ q| ≤ L * dist p q)
    (hintF : Integrable (fun x => ℓ (idealComp Ls (input x))) μ)
    (hintG : Integrable (fun x => ℓ (execComp Ls (input x))) μ)
    (hCapacity : (∫ x, ℓ (idealComp Ls (input x)) ∂μ)
        ≤ (1 / (n : ℝ)) * ∑ i, ℓ (idealComp Ls (xs i)) + capacity) :
    Resolution Ls (fun Ls => CertifiedExecutedRiskBound μ Ls input xs ℓ L capacity) :=
  Resolution.discharged
    (certifiedExecutedRiskBound_holds Ls input hn xs ℓ hL0 hLip hintF hintG hCapacity)

end TLT
