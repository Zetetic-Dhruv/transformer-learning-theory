/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import TLT_Proofs.TemperedDesignLaw.MixtureOutput

/-!
# Route-factored losses (TD0.5)

The two-channel risk decomposition (TD12) and the two-certificate generalization bound (TD11) need the loss
to *factor* through the routing: the loss of a soft mixture's output is the loss attributable to the hard
route plus a penalty controlled by how far the mixture sits from the route's one-hot payload.

`RouteFactoredLoss` packages the cleanest sufficient condition: the loss is `Lℓ`-Lipschitz in the output.
Then `mixture_le_route` gives the factored bound with the route loss the loss at the route's payload and the
penalty `Lℓ · ‖mixtureOutput − payload(route)‖`, which the hardening envelope (TD3/TD2) bounds by
`Lℓ · (k−1)·exp(−βγ)·D`. Two instances (`distLoss`, `scaledDistLoss`) witness non-vacuity.

This is the *output-Lipschitz* factorization: it admits clipped and Lipschitz regression losses but
not the 0-1 routing loss, which is discontinuous in the output. Admitting the 0-1 symbol-channel loss
requires the weaker form where the route loss lives on `Fin k` (the symbol) and the penalty absorbs
the off-route mass.
-/

noncomputable section

namespace TLT.TemperedDesignLaw

/-- **A route-factored loss.** A loss on outputs that is `Lℓ`-Lipschitz in the output (uniformly in the
target). This is the sufficient structure for the two-channel risk decomposition: it lets the loss of a soft
mixture be bounded by the loss at the route's payload plus a Lipschitz penalty in the mixture deviation. -/
structure RouteFactoredLoss (V : Type*) [NormedAddCommGroup V] (Y : Type*) where
  /-- The output loss. -/
  loss : V → Y → ℝ
  /-- The output-Lipschitz constant. -/
  Lℓ : ℝ
  /-- The Lipschitz constant is nonnegative. -/
  Lℓ_nonneg : 0 ≤ Lℓ
  /-- The loss is `Lℓ`-Lipschitz in the output, uniformly in the target. -/
  loss_lipschitz : ∀ (y : Y) (p q : V), |loss p y - loss q y| ≤ Lℓ * ‖p - q‖

/-- **The route-factored bound.** The loss of a soft mixture's output is at most the loss at the route's
payload plus the Lipschitz penalty `Lℓ · ‖mixtureOutput − payload(route)‖`. Composed with the hardening
envelope (the mixture deviation `≤ (k−1)·exp(−βγ)·D`), this is the mixture-channel term of the three-source
risk decomposition. -/
theorem RouteFactoredLoss.mixture_le_route {V : Type*} [NormedAddCommGroup V] [Module ℝ V] {Y : Type*}
    (Φ : RouteFactoredLoss V Y) {k : ℕ} (w : Fin k → ℝ) (val : Fin k → V) (route : Fin k) (y : Y) :
    Φ.loss (mixtureOutput w val) y
      ≤ Φ.loss (val route) y + Φ.Lℓ * ‖mixtureOutput w val - val route‖ := by
  have h := abs_le.mp (Φ.loss_lipschitz y (mixtureOutput w val) (val route))
  linarith [h.2]

/-- **Instance: the distance loss `‖output − y‖`** (regression target in `V`), `1`-Lipschitz in the output. -/
def distLoss (V : Type*) [NormedAddCommGroup V] : RouteFactoredLoss V V where
  loss p y := ‖p - y‖
  Lℓ := 1
  Lℓ_nonneg := zero_le_one
  loss_lipschitz y p q := by
    have h := abs_norm_sub_norm_le (p - y) (q - y)
    rw [sub_sub_sub_cancel_right] at h
    rwa [one_mul]

/-- **Instance: the scaled distance loss `c·‖output − y‖`** (`c ≥ 0`), `c`-Lipschitz, a second witness
with a tunable modulus. -/
def scaledDistLoss (V : Type*) [NormedAddCommGroup V] {c : ℝ} (hc : 0 ≤ c) : RouteFactoredLoss V V where
  loss p y := c * ‖p - y‖
  Lℓ := c
  Lℓ_nonneg := hc
  loss_lipschitz y p q := by
    have h := abs_norm_sub_norm_le (p - y) (q - y)
    rw [sub_sub_sub_cancel_right] at h
    calc |c * ‖p - y‖ - c * ‖q - y‖|
        = c * |‖p - y‖ - ‖q - y‖| := by rw [← mul_sub, abs_mul, abs_of_nonneg hc]
      _ ≤ c * ‖p - q‖ := mul_le_mul_of_nonneg_left h hc

end TLT.TemperedDesignLaw
