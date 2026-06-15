/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MixtureCapacityDudley
import TLT_Proofs.TemperedDesignLaw.RootContractInhabitation

/-!
# The smooth (Dudley) certificate of the tempered stack (the S1 discharge, smooth side)

The smooth-side "discharge functor" — `landed capacity bound ⟹ smooth certificate` — is already present
in general form as `paramStack_empiricalCapacity_le_dudley` (any `ParamLayer` stack's empirical capacity
is bounded by the Dudley entropy integral at its parameter-Lipschitz constant) together with
`temperedStack_dudleyCapBound_mono` (the bound is β-monotone). This file names the **tempered-stack
specialisation**: the genuine smooth certificate `empiricalCapacity(stack β) ≤ dudleyCapBound(stack β)`
for the depth-`n` replicated tempered mixture layer.

## A4 note — the affine/super-affine boundary (a Pl-kill, recorded honestly)
This certificate bounds the gap by the *genuine* Dudley object `dudleyCapBound d m R b (Lℓ · paramLipBound
(replicate n (temperedParamLayer β …)))`. It does **not** discharge `CapacityProfile.smooth_cert` against
the *affine* `smoothWitness base slope = fun β => base + slope·β`: for depth `n > 1` the parameter-Lipschitz
constant grows like `(2βKsP+Kv)^n`, so the Dudley bound is **super-affine in β** and no global affine
`smoothWitness` dominates it. Binding the certificate to the affine field therefore requires a
*window-restricted* affine over-bound on `[0, betaMax R.S]` (an open obligation), and the abstract-`gap`
identification is S2. Both are marked INPUT in `s_closure_map.md`; this file lands the genuine
(super-affine) smooth certificate, the real object the certificate's `smoothBound` should carry.
-/

noncomputable section

namespace TLT.TemperedDesignLaw

open TLT.Capacity

/-- **The tempered stack's smooth (Dudley) certificate.** The depth-`n` replicated tempered mixture
layer's empirical capacity on the radius-`R` weight ball is bounded by the Dudley entropy integral at
parameter-Lipschitz constant `Lℓ · paramLipBound (replicate n (temperedParamLayer β …))` — the genuine
smooth-side discharge, the tempered specialisation of `paramStack_empiricalCapacity_le_dudley`. This is
the named smooth certificate TD9 requires; its bound is the *genuine* (super-affine in β) Dudley object,
not the affine `smoothWitness` (see the module A4 note). -/
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

/-! ## A5-1 — the affine smooth-witness over-bound on the certified window (resolves the S1 Pl-kill)

The S1 review found a genuine Pl-kill: the affine `smoothWitness base slope = base + slope·β` cannot
dominate the *super-affine* (depth-`n`) Dudley bound **globally**. The resolution is not to stop but to
**add the structure** that closes it on the certified window `[0, betaMax]`: any β-**monotone** bound `g`
(which the Dudley bound is, by `temperedStack_dudleyCapBound_mono`) admits an affine `smoothWitness`
over-bound there — the *constant* `g(βmax)`, since `g β ≤ g βmax` for `β ≤ βmax`. So an affine
`smoothWitness` genuinely dominates the super-affine bound on the window; the Pl-kill is resolved (the
global obstruction becomes a window over-bound). The constant (slope `0`) witness is the loose-but-honest
closure; a tighter *chord* witness (via convexity of the Dudley bound in β) is an optional refinement,
not required to discharge the affine-domination obligation. -/

/-- **Affine `smoothWitness` over-bound of any β-monotone bound on `[0, βmax]` (A5-1).** For a bound `g`
monotone on `β ≥ 0`, the affine `smoothWitness (g βmax) 0` (the constant `g βmax`) dominates `g` on the
window `[0, βmax]`. Applied to `g β := dudleyCapBound … (Lℓ · paramLipBound (replicate n
(temperedParamLayer β …)))` — monotone by `temperedStack_dudleyCapBound_mono` — this gives the affine
smooth certificate the `CapacityProfile.smoothBound` field expects, resolving the S1 affine/super-affine
Pl-kill on the certified window. -/
theorem dudley_window_smoothWitness {g : ℝ → ℝ} {βmax : ℝ} (hβmax : 0 ≤ βmax)
    (hg : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ≤ b → g a ≤ g b)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβwin : β ≤ βmax) :
    g β ≤ smoothWitness (g βmax) 0 β := by
  simp only [smoothWitness, zero_mul, add_zero]
  exact hg β βmax hβ0 hβmax hβwin

end TLT.TemperedDesignLaw
