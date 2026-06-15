/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import FLT_Proofs.Complexity.Rademacher
import FLT_Proofs.Complexity.IndependentVC.Growth

/-!
# Massart's finite-class lemma for the empirical Rademacher complexity

The crux of the TLT hard-generalization arm: the empirical Rademacher complexity of a Bool
concept class `C` on a sample `xs : Fin m → X` is bounded by `√(2 log N / m)`, where `N` is the
number of labelling patterns `C` realizes on the (de-duplicated) sample, i.e. the cardinality of
the restriction set `restrictionSet C (Finset.univ.image xs)`.

The proof:
1. The correlation `rademacherCorrelation h σ xs` depends on `h` only through its labelling
   pattern `fun i => h (xs i)`, so the `sSup` over `C` collapses to a `Finset.sup'` over the
   finite set of realized patterns `dpats : Finset (Fin m → Bool)`.
2. Each pattern's normalized ±1 correlation is sub-Gaussian with proxy `σ = 1/√m` (the Hoeffding
   cgf, `rademacher_mgf_bound`); the finite-class maximal inequality (`finite_massart_lemma`) gives
   `EmpRad ≤ (1/√m) · √(2 log (dpats.card))`.
3. Each realized pattern over `Fin m` is determined by its restriction to the de-duplicated sample
   `S = Finset.univ.image xs`, so `dpats.card ≤ (restrictionSet C S).ncard = N`, and `√` / `log`
   monotonicity finishes.
-/

open MeasureTheory

namespace TLT.TemperedDesignLaw

universe u

/-- **Massart's finite-class lemma for the empirical Rademacher complexity.**

For a nonempty Bool concept class `C` and a sample `xs : Fin m → X` with `m > 0`,
the empirical Rademacher complexity is controlled by the log of the restriction cardinality:
`EmpRad ≤ √(2 · log N / m)`, where `N = (restrictionSet C (Finset.univ.image xs)).ncard` is the
number of distinct labellings `C` induces on the sample points. -/
theorem empiricalRademacherComplexity_le_massart
    {X : Type u} [DecidableEq X] (C : ConceptClass X Bool) {m : ℕ} (hm : 0 < m)
    (hC : C.Nonempty) (xs : Fin m → X) :
    EmpiricalRademacherComplexity X C xs ≤
      Real.sqrt (2 * Real.log ((restrictionSet C (Finset.univ.image xs)).ncard) / m) := by
  classical
  -- Positivity facts
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  have hcard_pos : (0 : ℝ) < (Fintype.card (SignVector m) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := SignVector m)
  have h1card_pos : (0 : ℝ) < 1 / (Fintype.card (SignVector m) : ℝ) := by positivity
  obtain ⟨h₀, hh₀⟩ := hC
  set Sset := Finset.univ.image xs with hSset
  set Nset := (restrictionSet C Sset).ncard with hNset
  -- The correlation depends on h only through the labelling pattern `fun i => h (xs i)`.
  let dpats : Finset (Fin m → Bool) :=
      Finset.univ.filter (fun p => ∃ h ∈ C, ∀ i, h (xs i) = p i)
  have hdpats_ne : dpats.Nonempty := by
    refine ⟨fun i => h₀ (xs i), ?_⟩
    simp only [dpats, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h₀, hh₀, fun _ => rfl⟩
  set cf : SignVector m → (Fin m → Bool) → ℝ :=
    fun σ p => (1 / (m : ℝ)) * ∑ i : Fin m, boolToSign (σ i) * boolToSign (p i) with hcf
  have h_corr_eq : ∀ (h : Concept X Bool) (σ : SignVector m),
      rademacherCorrelation h σ xs = cf σ (fun i => h (xs i)) := by
    intro h σ; unfold rademacherCorrelation
    rw [dif_neg (Nat.pos_iff_ne_zero.mp hm)]
  have h_mem_dpats : ∀ h ∈ C, (fun i => h (xs i)) ∈ dpats := by
    intro h hh
    simp only [dpats, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h, hh, fun _ => rfl⟩
  have h_ssup_le_sup' : ∀ σ : SignVector m,
      sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } ≤
      dpats.sup' hdpats_ne (cf σ) := by
    intro σ
    apply csSup_le
    · exact ⟨rademacherCorrelation h₀ σ xs, h₀, hh₀, rfl⟩
    · rintro r ⟨h, hh, rfl⟩
      rw [h_corr_eq]
      exact Finset.le_sup' (cf σ) (h_mem_dpats h hh)
  have h_empRad_le : EmpiricalRademacherComplexity X C xs ≤
      (1 / (Fintype.card (SignVector m) : ℝ)) *
        ∑ σ : SignVector m, dpats.sup' hdpats_ne (cf σ) := by
    unfold EmpiricalRademacherComplexity
    rw [dif_neg (Nat.pos_iff_ne_zero.mp hm)]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt h1card_pos)
    exact Finset.sum_le_sum (fun σ _ => h_ssup_le_sup' σ)
  set N := dpats.card with hN_card
  have hN_pos : 0 < N := Finset.Nonempty.card_pos hdpats_ne
  have hcard_dpats : Fintype.card { p // p ∈ dpats } = N := Fintype.card_coe dpats
  let e : { p // p ∈ dpats } ≃ Fin N :=
    hcard_dpats ▸ Fintype.equivFin _
  let Z : Fin N → SignVector m → ℝ :=
    fun j σ => cf σ (e.symm j).val
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN_pos
  have h_sup'_eq : ∀ σ : SignVector m,
      dpats.sup' hdpats_ne (cf σ) =
      Finset.univ.sup' Finset.univ_nonempty (fun j => Z j σ) := by
    intro σ
    apply le_antisymm
    · rw [Finset.sup'_le_iff]
      intro p hp
      exact Finset.le_sup'_of_le (f := fun j => Z j σ) (Finset.mem_univ (e ⟨p, hp⟩))
        (by show cf σ p ≤ cf σ (e.symm (e ⟨p, hp⟩)).val; simp [Equiv.symm_apply_apply])
    · rw [Finset.sup'_le_iff]
      intro j _
      exact Finset.le_sup' (cf σ) (e.symm j).prop
  have h_empRad_le2 : EmpiricalRademacherComplexity X C xs ≤
      (1 / (Fintype.card (SignVector m) : ℝ)) *
        ∑ σ : SignVector m, Finset.univ.sup' Finset.univ_nonempty (fun j => Z j σ) := by
    calc EmpiricalRademacherComplexity X C xs
        ≤ (1 / (Fintype.card (SignVector m) : ℝ)) *
            ∑ σ, dpats.sup' hdpats_ne (cf σ) := h_empRad_le
      _ = _ := by
          congr 1; apply Finset.sum_congr rfl; intro σ _; exact h_sup'_eq σ
  -- MGF bound for each Z_j (sub-Gaussianity, Hoeffding cgf)
  set σ_param := (1 : ℝ) / Real.sqrt m with hσ_param
  have hσ_pos : 0 < σ_param := by positivity
  have h_mgf_Z : ∀ j : Fin N, ∀ t : ℝ, 0 ≤ t →
      (1 / (Fintype.card (SignVector m) : ℝ)) *
        ∑ sv : SignVector m, Real.exp (t * Z j sv) ≤
      Real.exp (t ^ 2 * σ_param ^ 2 / 2) := by
    intro j t ht
    set p := (e.symm j).val with hp_def
    have h_bound := rademacher_mgf_bound hm (fun i => boolToSign (p i)) 1 (by norm_num)
      (fun i => le_of_eq (boolToSign_abs_eq_one (p i))) t ht
    have h_Z_rewrite : ∀ sv, Z j sv =
        (1 / (m : ℝ)) * ∑ i, (fun i => boolToSign (p i)) i * boolToSign (sv i) := by
      intro sv
      show cf sv p = _
      simp only [cf]
      congr 1; apply Finset.sum_congr rfl; intro i _; ring
    have h_lhs_eq : ∀ sv, Real.exp (t * Z j sv) =
        Real.exp (t * ((1 / (m : ℝ)) * ∑ i, (fun i => boolToSign (p i)) i * boolToSign (sv i))) := by
      intro sv; rw [h_Z_rewrite]
    simp_rw [h_lhs_eq]
    have h_rhs_eq : t ^ 2 * σ_param ^ 2 / 2 = t ^ 2 * 1 ^ 2 / (2 * ↑m) := by
      rw [one_pow, mul_one, show σ_param = 1 / Real.sqrt ↑m from rfl]
      rw [one_div, inv_pow, Real.sq_sqrt (le_of_lt hm_pos)]
      ring
    rw [h_rhs_eq]
    exact h_bound
  -- Apply finite_massart_lemma: EmpRad ≤ σ_param · √(2 log N)
  have h_massart := finite_massart_lemma hm hN_pos Z σ_param hσ_pos h_mgf_Z
  -- Each realized pattern over `Fin m` is determined by its restriction to `S = image xs`.
  have h_dpats_card_le_ncard : (N : ℝ) ≤ (Nset : ℝ) := by
    set R := { f : ↥Sset → Bool | ∃ c ∈ C, ∀ x : ↥Sset, c ↑x = f x } with hR_def
    -- restrictionSet C Sset = R (definitionally, modulo the membership predicate shape)
    have hR_fin : R.Finite := Set.Finite.subset (Set.finite_univ) (Set.subset_univ _)
    have h_dpats_mem : ∀ p ∈ dpats, ∃ c ∈ C, ∀ i, c (xs i) = p i := by
      intro p hp
      have := Finset.mem_filter.mp hp
      exact this.2
    have h_inj_card : N ≤ R.toFinset.card := by
      apply Finset.card_le_card_of_injOn
        (fun (p : Fin m → Bool) (x : ↥Sset) =>
          p ((Finset.mem_image.mp x.prop).choose))
        (fun p hp => by
          obtain ⟨c, hcC, hc_agree⟩ := h_dpats_mem p hp
          have : (fun (x : ↥Sset) => p ((Finset.mem_image.mp x.prop).choose)) ∈ R := by
            exact ⟨c, hcC, fun ⟨x, hx⟩ => by
              have hcs := (Finset.mem_image.mp hx).choose_spec
              show c x = p ((Finset.mem_image.mp hx).choose)
              conv_lhs => rw [← hcs.2]
              exact hc_agree _⟩
          exact Set.mem_toFinset.mpr this)
        (fun p₁ hp₁ p₂ hp₂ heq => by
          obtain ⟨c₁, _, hc₁⟩ := h_dpats_mem p₁ hp₁
          obtain ⟨c₂, _, hc₂⟩ := h_dpats_mem p₂ hp₂
          funext i
          have hxi_in : xs i ∈ Sset := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
          have hcs := (Finset.mem_image.mp hxi_in).choose_spec
          have h_at := congr_fun heq ⟨xs i, hxi_in⟩
          rw [← hc₁ i, ← hc₂ i]
          rw [← hcs.2]
          rw [hc₁, hc₂]
          exact h_at)
    have hR_eq : R = restrictionSet C Sset := by
      ext f
      simp only [hR_def, restrictionSet, Set.mem_setOf_eq]
    have hR_ncard : R.ncard = Nset := by rw [hR_eq]
    calc (N : ℝ)
        ≤ ↑R.toFinset.card := by exact_mod_cast h_inj_card
      _ = ↑R.ncard := by rw [Set.ncard_eq_toFinset_card']
      _ = (Nset : ℝ) := by rw [hR_ncard]
  have hN_real_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
  have hNset_pos : (0 : ℝ) < Nset := lt_of_lt_of_le hN_real_pos h_dpats_card_le_ncard
  have h_log_N_le : Real.log ↑N ≤ Real.log (Nset : ℝ) :=
    Real.log_le_log hN_real_pos h_dpats_card_le_ncard
  have h_log_N_nonneg : 0 ≤ Real.log (↑N : ℝ) := Real.log_natCast_nonneg N
  have hfinal : EmpiricalRademacherComplexity X C xs ≤
      Real.sqrt (2 * Real.log ((restrictionSet C Sset).ncard) / m) := by
    calc EmpiricalRademacherComplexity X C xs
        ≤ (1 / (Fintype.card (SignVector m) : ℝ)) *
            ∑ σ, Finset.univ.sup' Finset.univ_nonempty (fun j => Z j σ) := h_empRad_le2
      _ ≤ σ_param * Real.sqrt (2 * Real.log ↑N) := h_massart
      _ ≤ σ_param * Real.sqrt (2 * Real.log (Nset : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hσ_pos)
          apply Real.sqrt_le_sqrt; nlinarith [h_log_N_le]
      _ = Real.sqrt (2 * Real.log ((restrictionSet C Sset).ncard) / m) := by
          rw [show σ_param = 1 / Real.sqrt ↑m from rfl]
          rw [one_div, ← Real.sqrt_inv, ← Real.sqrt_mul (inv_nonneg.mpr (le_of_lt hm_pos))]
          congr 1; rw [inv_mul_eq_div, hNset]
  exact hfinal

end TLT.TemperedDesignLaw

