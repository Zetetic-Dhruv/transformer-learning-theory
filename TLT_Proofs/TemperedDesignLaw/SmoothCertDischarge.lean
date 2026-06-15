/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MixtureCapacityDudley
import TLT_Proofs.TemperedDesignLaw.RootContractInhabitation

/-!
# The smooth (Dudley) certificate of the tempered stack

The smooth-side bound `empiricalCapacity(stack β) ≤ dudleyCapBound(stack β)` is already present
in general form as `paramStack_empiricalCapacity_le_dudley` (any `ParamLayer` stack's empirical capacity
is bounded by the Dudley entropy integral at its parameter-Lipschitz constant) together with
`temperedStack_dudleyCapBound_mono` (the bound is β-monotone). This file names the **tempered-stack
specialisation**: the smooth certificate `empiricalCapacity(stack β) ≤ dudleyCapBound(stack β)`
for the depth-`n` replicated tempered mixture layer.

## The affine/super-affine boundary
This certificate bounds the gap by the Dudley object `dudleyCapBound d m R b (Lℓ · paramLipBound
(replicate n (temperedParamLayer β …)))`. It does **not** discharge `CapacityProfile.smooth_cert` against
the *affine* `smoothWitness base slope = fun β => base + slope·β`: for depth `n > 1` the parameter-Lipschitz
constant grows like `(2βKsP+Kv)^n`, so the Dudley bound is **super-affine in β** and no global affine
`smoothWitness` dominates it. Binding the certificate to the affine field requires a
*window-restricted* affine over-bound on `[0, betaMax R.S]`; the abstract-`gap`
identification is S2. This file carries the
(super-affine) smooth certificate: the Dudley object the certificate's `smoothBound` should carry.
-/

noncomputable section

namespace TLT.TemperedDesignLaw

open TLT.Capacity

/-- **The tempered stack's smooth (Dudley) certificate.** The depth-`n` replicated tempered mixture
layer's empirical capacity on the radius-`R` weight ball is bounded by the Dudley entropy integral at
parameter-Lipschitz constant `Lℓ · paramLipBound (replicate n (temperedParamLayer β …))`. This is
the tempered specialisation of `paramStack_empiricalCapacity_le_dudley`, the named smooth certificate
TD9 requires. Its bound is the (super-affine in β) Dudley object, not the affine `smoothWitness`
(see the module note). -/
def temperedStack_smooth_cert
    {k : ℕ} [NeZero k] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d m : ℕ} [Nonempty (Fin d)] (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R)
    (score : ParamSpace d → V → Fin k → ℝ) (val : ParamSpace d → V → Fin k → V)
    (Ksθ Kvθ Ksy Kvy P : ℝ)
    (hKsθ : 0 ≤ Ksθ) (hKvθ : 0 ≤ Kvθ) (hKsy : 0 ≤ Ksy) (hKvy : 0 ≤ Kvy) (hP : 0 ≤ P)
    (hScoreθ : ∀ y θ θ', dist (score θ y) (score θ' y) ≤ Ksθ * dist θ θ')
    (hValθ : ∀ y θ θ', dist (val θ y) (val θ' y) ≤ Kvθ * dist θ θ')
    (hScorey : ∀ θ a c, dist (score θ a) (score θ c) ≤ Ksy * dist a c)
    (hValy : ∀ θ a c, dist (val θ a) (val θ c) ≤ Kvy * dist a c)
    (hValbd : ∀ θ y, (∑ i, ‖val θ y i‖) ≤ P)
    (n : ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (ℓ : V → ℝ) {Lℓ : ℝ} (hLℓ : 0 ≤ Lℓ) (hℓ : ∀ a b, |ℓ a - ℓ b| ≤ Lℓ * dist a b)
    {b : ℝ} (hb : 0 < b)
    (hFb : ∀ θ x, |ℓ (paramComp (List.replicate n (temperedParamLayer β score val
      Ksθ Kvθ Ksy Kvy P hβ hKsθ hKvθ hKsy hKvy hP hScoreθ hValθ hScorey hValy hValbd)) θ x)| ≤ b)
    (S : Fin m → V)
    (hL : 0 < Lℓ * paramLipBound (List.replicate n (temperedParamLayer β score val
      Ksθ Kvθ Ksy Kvy P hβ hKsθ hKvθ hKsy hKvy hP hScoreθ hValθ hScorey hValy hValbd))) :=
  paramStack_empiricalCapacity_le_dudley hm hR
    (List.replicate n (temperedParamLayer β score val
      Ksθ Kvθ Ksy Kvy P hβ hKsθ hKvθ hKsy hKvy hP hScoreθ hValθ hScorey hValy hValbd))
    ℓ hLℓ hℓ hb hFb S hL

/-! ## A5-1: the affine smooth-witness over-bound on the certified window

The affine `smoothWitness base slope = base + slope·β` cannot dominate the *super-affine* (depth-`n`)
Dudley bound **globally**. The resolution is to restrict to the certified window `[0, betaMax]`: any
β-**monotone** bound `g` (which the Dudley bound is, by `temperedStack_dudleyCapBound_mono`) admits an
affine `smoothWitness` over-bound there, namely the constant `g(βmax)`, since `g β ≤ g βmax` for
`β ≤ βmax`. The constant (slope `0`) witness is the resulting affine domination on the window; a tighter
*chord* witness (via convexity of the Dudley bound in β) is an optional refinement. -/

/-- **Affine `smoothWitness` over-bound of any β-monotone bound on `[0, βmax]`.** For a bound `g`
monotone on `β ≥ 0`, the affine `smoothWitness (g βmax) 0` (the constant `g βmax`) dominates `g` on the
window `[0, βmax]`. Applied to `g β := dudleyCapBound … (Lℓ · paramLipBound (replicate n
(temperedParamLayer β …)))`, monotone by `temperedStack_dudleyCapBound_mono`, this gives the affine
smooth certificate the `CapacityProfile.smoothBound` field expects on the certified window. -/
theorem dudley_window_smoothWitness {g : ℝ → ℝ} {βmax : ℝ} (hβmax : 0 ≤ βmax)
    (hg : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ≤ b → g a ≤ g b)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβwin : β ≤ βmax) :
    g β ≤ smoothWitness (g βmax) 0 β := by
  simp only [smoothWitness, zero_mul, add_zero]
  exact hg β βmax hβ0 hβmax hβwin

end TLT.TemperedDesignLaw
