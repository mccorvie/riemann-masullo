module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Orders of vanishing of reciprocal gamma factors

The reciprocal of Euler's gamma function vanishes to order at most one, and so does the
reciprocal of the archimedean factors `Γℝ(s + c)` and `Γℂ(s + c)/2`, whose zeros are the
points `-c - k` with `k` natural. The reciprocal of a product of `n` such factors vanishes to
order at most `n`.
-/

public section

namespace RiemannMasullo

/-- The reciprocal Gamma function vanishes to order at most one everywhere, by the
recursion `1/Γ(s) = s · 1/Γ(s + 1)`. -/
theorem analyticOrderAt_inv_Gamma_le_one (w : ℂ) :
    analyticOrderAt (fun s ↦ (Complex.Gamma s)⁻¹) w ≤ 1 := by
  have han (z : ℂ) : AnalyticAt ℂ (fun s ↦ (Complex.Gamma s)⁻¹) z :=
    Complex.differentiable_one_div_Gamma.analyticAt z
  by_cases hw : (Complex.Gamma w)⁻¹ = 0
  · obtain ⟨n, rfl⟩ := (Complex.Gamma_eq_zero_iff w).mp (inv_eq_zero.mp hw)
    induction n with
    | zero =>
      have hrec : (fun s ↦ (Complex.Gamma s)⁻¹) =
          (fun s : ℂ ↦ s - 0) * ((fun s ↦ (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ ↦ s + 1)) := by
        funext s
        simp [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s]
      rw [hrec, analyticOrderAt_mul (by fun_prop) ((han _).comp (by fun_prop)),
        analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
      simp only [Nat.cast_zero, neg_zero]
      rw [analyticOrderAt_id_sub_const_self, zero_add,
        ((han 1).analyticOrderAt_eq_zero).mpr (by simp)]
      simp
    | succ n ih =>
      have hrec : (fun s ↦ (Complex.Gamma s)⁻¹) =
          (fun s : ℂ ↦ s) * ((fun s ↦ (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ ↦ s + 1)) := by
        funext s
        simp [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s]
      rw [hrec, analyticOrderAt_mul (by fun_prop) ((han _).comp (by fun_prop)),
        analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
      have h0 : analyticOrderAt (fun s : ℂ ↦ s) (-((n + 1 : ℕ) : ℂ)) = 0 :=
        (analyticAt_id.analyticOrderAt_eq_zero).mpr (by
          show -(((n + 1 : ℕ) : ℂ)) ≠ 0
          rw [neg_ne_zero, Nat.cast_ne_zero]
          exact Nat.succ_ne_zero n)
      have h1 : -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) := by push_cast; ring
      rw [h0, zero_add, h1]
      exact ih (by
        rw [inv_eq_zero]
        exact Complex.Gamma_neg_nat_eq_zero n)
  · rw [((han w).analyticOrderAt_eq_zero).mpr hw]
    exact zero_le

/-- A nonvanishing analytic factor times the reciprocal Gamma function at an affine
argument vanishes to order at most one. -/
theorem analyticOrderAt_mul_inv_Gamma_affine_le_one (u : ℂ → ℂ) (a c z : ℂ) (ha : a ≠ 0)
    (hu : AnalyticAt ℂ u z) (hu0 : u z ≠ 0) :
    analyticOrderAt (fun s ↦ u s * (Complex.Gamma (a * s + c))⁻¹) z ≤ 1 := by
  have hg : AnalyticAt ℂ (fun s : ℂ ↦ a * s + c) z := by fun_prop
  have hΓ : AnalyticAt ℂ ((fun s ↦ (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ ↦ a * s + c)) z :=
    (Complex.differentiable_one_div_Gamma.analyticAt _).comp hg
  change analyticOrderAt (u * ((fun s ↦ (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ ↦ a * s + c))) z ≤ 1
  rw [analyticOrderAt_mul hu hΓ, (hu.analyticOrderAt_eq_zero).mpr hu0, zero_add,
    analyticOrderAt_comp_of_deriv_ne_zero hg (by
      rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'']
      simpa using ha)]
  exact analyticOrderAt_inv_Gamma_le_one _

/-- The reciprocal of an archimedean Gamma factor is entire, vanishes to order at most
one, and vanishes only at `-c - k` for natural `k`. -/
theorem analyticOrderAt_inv_Gammaℝℂ_le_one (f : ℂ → ℂ) (c : ℂ)
    (hf : (∀ s, f s = Complex.Gammaℝ (s + c)) ∨ (∀ s, f s = Complex.Gammaℂ (s + c) / 2))
    (z : ℂ) :
    AnalyticAt ℂ (fun s ↦ (f s)⁻¹) z ∧ analyticOrderAt (fun s ↦ (f s)⁻¹) z ≤ 1 ∧
      ((f z)⁻¹ = 0 → ∃ k : ℕ, z = -c - k) := by
  rcases hf with hf | hf
  · have he : (fun s ↦ (f s)⁻¹) = fun s ↦ ((Real.pi : ℂ) ^ (-(s + c) / 2))⁻¹ *
        (Complex.Gamma ((1 / 2 : ℂ) * s + c / 2))⁻¹ := by
      funext s
      rw [hf, Complex.Gammaℝ_def, mul_inv, show (s + c) / 2 = 1 / 2 * s + c / 2 by ring]
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hu : Differentiable ℂ fun s : ℂ ↦ ((Real.pi : ℂ) ^ (-(s + c) / 2))⁻¹ :=
      fun s ↦ ((((differentiable_id.add_const c).neg.div_const 2) s).const_cpow
        (Or.inl hπ)).inv (Complex.cpow_ne_zero_iff.mpr (Or.inl hπ))
    refine ⟨?_, ?_, fun h0 ↦ ?_⟩
    · rw [he]
      exact (hu.analyticAt z).mul ((Complex.differentiable_one_div_Gamma.analyticAt _).comp
        (by fun_prop))
    · rw [he]
      exact analyticOrderAt_mul_inv_Gamma_affine_le_one _ _ _ z (by norm_num) (hu.analyticAt z)
        (inv_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)))
    · rw [hf] at h0
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp (inv_eq_zero.mp h0)
      exact ⟨2 * n, by push_cast; linear_combination hn⟩
  · have he : (fun s ↦ (f s)⁻¹) = fun s ↦ (2 * (2 * (2 * Real.pi : ℂ) ^ (-(s + c)))⁻¹) *
        (Complex.Gamma (1 * s + c))⁻¹ := by
      funext s
      rw [hf, Complex.Gammaℂ_def, one_mul]
      simp only [div_eq_mul_inv, mul_inv, inv_inv]
      ring
    have h2π : (2 * Real.pi : ℂ) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hpow (s : ℂ) : (2 * Real.pi : ℂ) ^ (-(s + c)) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl h2π)
    have hu : Differentiable ℂ fun s : ℂ ↦ 2 * (2 * (2 * Real.pi : ℂ) ^ (-(s + c)))⁻¹ :=
      fun s ↦ ((((differentiable_id.add_const c).neg s).const_cpow (Or.inl h2π)).const_mul
        2).inv (mul_ne_zero two_ne_zero (hpow s)) |>.const_mul 2
    refine ⟨?_, ?_, fun h0 ↦ ?_⟩
    · rw [he]
      exact (hu.analyticAt z).mul ((Complex.differentiable_one_div_Gamma.analyticAt _).comp
        (by fun_prop))
    · rw [he]
      exact analyticOrderAt_mul_inv_Gamma_affine_le_one _ _ _ z one_ne_zero (hu.analyticAt z)
        (mul_ne_zero two_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero (hpow z))))
    · rw [hf, inv_eq_zero, div_eq_zero_iff, Complex.Gammaℂ_def] at h0
      have hΓ : Complex.Gamma (z + c) = 0 := by
        rcases h0 with h0 | h0
        · rcases mul_eq_zero.mp h0 with h | h
          · exact absurd h (mul_ne_zero two_ne_zero (hpow z))
          · exact h
        · exact absurd h0 two_ne_zero
      obtain ⟨n, hn⟩ := (Complex.Gamma_eq_zero_iff _).mp hΓ
      exact ⟨n, by linear_combination hn⟩

/-- The reciprocal of a finite product of archimedean Gamma factors vanishes to order at
most the number of factors, and only at points `-c i - k`. -/
theorem analyticOrderAt_inv_prod_Gammaℝℂ_le {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ)
    (c : ι → ℂ) (hf : ∀ i, (∀ s, f i s = Complex.Gammaℝ (s + c i)) ∨
      (∀ s, f i s = Complex.Gammaℂ (s + c i) / 2)) (z : ℂ) :
    analyticOrderAt (fun s ↦ (∏ i, f i s)⁻¹) z ≤ Fintype.card ι ∧
      ((∏ i, f i z)⁻¹ = 0 → ∃ i, ∃ k : ℕ, z = -c i - k) := by
  classical
  have hinv : (fun s ↦ (∏ i, f i s)⁻¹) = fun s ↦ ∏ i, (f i s)⁻¹ := by
    funext s
    rw [Finset.prod_inv_distrib]
  refine ⟨?_, fun h0 ↦ ?_⟩
  · rw [hinv, ← Finset.card_univ]
    have key : ∀ s : Finset ι, AnalyticAt ℂ (fun w ↦ ∏ i ∈ s, (f i w)⁻¹) z ∧
        analyticOrderAt (fun w ↦ ∏ i ∈ s, (f i w)⁻¹) z ≤ s.card := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        refine ⟨by simpa using analyticAt_const, ?_⟩
        simp only [Finset.prod_empty, Finset.card_empty, Nat.cast_zero]
        exact ((analyticAt_const).analyticOrderAt_eq_zero.mpr one_ne_zero).le
      | insert a s ha ih =>
        obtain ⟨hfa, hoa, -⟩ := analyticOrderAt_inv_Gammaℝℂ_le_one (f a) (c a) (hf a) z
        have he : (fun w ↦ ∏ i ∈ insert a s, (f i w)⁻¹) =
            (fun w ↦ (f a w)⁻¹) * fun w ↦ ∏ i ∈ s, (f i w)⁻¹ := by
          funext w
          rw [Finset.prod_insert ha]
          rfl
        rw [he]
        refine ⟨hfa.mul ih.1, ?_⟩
        rw [analyticOrderAt_mul hfa ih.1, Finset.card_insert_of_notMem ha, Nat.cast_add,
          Nat.cast_one, add_comm (s.card : ℕ∞)]
        exact add_le_add hoa ih.2
    exact (key Finset.univ).2
  · rw [← Finset.prod_inv_distrib, Finset.prod_eq_zero_iff] at h0
    obtain ⟨i, -, hi⟩ := h0
    obtain ⟨k, hk⟩ := (analyticOrderAt_inv_Gammaℝℂ_le_one (f i) (c i) (hf i) z).2.2 hi
    exact ⟨i, k, hk⟩

end RiemannMasullo
