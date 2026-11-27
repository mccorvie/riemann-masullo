module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

private lemma large_mass_factor {x : ℝ} (hx : 256 ≤ x) :
    (1 - x⁻¹)⁻¹ ^ 6 ≤ 1 + (Real.sqrt x)⁻¹ := by
  have hx₀ : 0 < x := by linarith
  have hinv : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hs : 16 ≤ Real.sqrt x := (Real.le_sqrt' (by norm_num)).2 (by norm_num; exact hx)
  have hs₀ : 0 < Real.sqrt x := Real.sqrt_pos.2 hx₀
  have hBernoulli : 1 - 6 * x⁻¹ ≤ (1 - x⁻¹) ^ 6 := by
    simpa [sub_eq_add_neg] using one_add_mul_le_pow (a := -x⁻¹) (by linarith) 6
  rw [inv_pow, inv_le_iff_one_le_mul₀' (pow_pos (sub_pos.mpr hinv) 6)]
  calc
    1 ≤ (1 - 6 * x⁻¹) * (1 + (Real.sqrt x)⁻¹) := by
      field_simp
      nlinarith [Real.sq_sqrt hx₀.le, sq_nonneg (Real.sqrt x - 16)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hBernoulli (by positivity)

private lemma prod_one_add_inv_sqrt_le {r : ℕ} (hr : r ≠ 0) :
    (∏ p ∈ r.primeFactors, (1 + (Real.sqrt p)⁻¹)) ≤ ∑ d ∈ r.divisors, (Real.sqrt d)⁻¹ := by
  classical
  rw [Finset.prod_one_add]
  calc
    _ = ∑ d ∈ r.divisors with Squarefree d, (Real.sqrt d)⁻¹ := by
      rw [Nat.sum_divisors_filter_squarefree hr, Nat.factors_eq]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.prod_val, Nat.cast_prod, Real.sqrt_prod _ (fun _ _ ↦ Nat.cast_nonneg _),
        Finset.prod_inv_distrib]
      rfl
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
      intros; positivity)

/-- Card 12. The sixth power of the Euler product for r is bounded by a constant times the sum of
the reciprocal square roots of the divisors of r.
Titchmarsh, §10.14, p. 273, last display, with exponent six. -/
theorem mass_majorant : ∃ C > (0 : ℝ), ∀ r : ℕ, 0 < r →
    (smoothMass r)^6 ≤ C * ∑ d ∈ r.divisors, (Real.sqrt d)⁻¹ := by
  let factor (p : ℕ) := (1 - (p : ℝ)⁻¹)⁻¹ ^ 6
  let small := Nat.primesBelow 256
  have factor_nonneg (p : ℕ) : 0 ≤ factor p := Even.pow_nonneg (by decide : Even 6) _
  have hfactor (p : ℕ) (hp : p ∈ small) : 1 ≤ factor p := by
    have hp' : 1 < (p : ℝ) := by exact_mod_cast Nat.one_lt_of_mem_primesBelow hp
    exact one_le_pow₀ ((one_le_inv₀ (sub_pos.mpr (inv_lt_one_of_one_lt₀ hp'))).2
      (sub_le_self _ (by positivity)))
  have hC : 0 < ∏ p ∈ small, factor p := zero_lt_one.trans_le (Finset.one_le_prod₀ hfactor)
  refine ⟨_, hC, fun r hr ↦ ?_⟩
  have hsmall : (∏ p ∈ r.primeFactors ∩ small, factor p) ≤ ∏ p ∈ small, factor p := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ Finset.inter_subset_right
    · exact fun p _ ↦ factor_nonneg p
    · intro p hp _; exact hfactor p hp
  have hlarge : (∏ p ∈ r.primeFactors \ small, factor p) ≤
      ∏ p ∈ r.primeFactors, (1 + (Real.sqrt p)⁻¹) := by
    apply Finset.prod_mono_of_subset_of_one_le₀ Finset.sdiff_subset
    · exact fun p _ ↦ factor_nonneg p
    · intro p hp
      obtain ⟨hpr, hps⟩ := Finset.mem_sdiff.mp hp
      have hp' : 256 ≤ p := le_of_not_gt fun h ↦
        hps (Nat.mem_primesBelow.mpr ⟨h, Nat.prime_of_mem_primeFactors hpr⟩)
      exact large_mass_factor (by exact_mod_cast hp')
    · intros; exact le_add_of_nonneg_right (by positivity)
  calc
    (smoothMass r)^6 = (∏ p ∈ r.primeFactors ∩ small, factor p) *
        ∏ p ∈ r.primeFactors \ small, factor p := by
      rw [Finset.prod_inter_mul_prod_sdiff, smoothMass, ← Finset.prod_pow]
    _ ≤ _ := mul_le_mul hsmall (hlarge.trans (prod_one_add_inv_sqrt_le hr.ne'))
      (Finset.prod_nonneg fun p _ ↦ factor_nonneg p) hC.le

end RiemannMasullo.Selberg
