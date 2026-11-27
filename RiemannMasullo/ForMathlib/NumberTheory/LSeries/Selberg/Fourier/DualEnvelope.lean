module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.KernelSymmetry
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.KernelBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

public section

namespace RiemannMasullo.Selberg

private theorem angle_bounds {N : ℕ} (hN : 2 ≤ N) :
    |angle N| < Real.pi / 4 ∧
      1 + (Real.sqrt (Real.cos (2 * angle N)))⁻¹ ≤ 3 * (N : ℝ)^50 := by
  let x := (N : ℝ)^50
  let δ := 1 / x^2
  have hx : 1 ≤ x := one_le_pow₀ (by exact_mod_cast (show 1 ≤ N by omega))
  have hxpos : 0 < x := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ₁ : δ ≤ 1 := (div_le_one (sq_pos_of_pos hxpos)).2 (one_le_pow₀ hx)
  have hH : (H N : ℝ) = x^2 := by simp [H, x, ← pow_mul]
  have ha : angle N = Real.pi / 4 - δ / 2 := by
    rw [angle, hH]
    dsimp [δ]
    ring
  have hstrip : |angle N| < Real.pi / 4 := by
    rw [ha, abs_lt]
    constructor <;> linarith [Real.two_le_pi]
  have hcos : Real.cos (2 * angle N) = Real.sin δ := by
    rw [ha, show 2 * (Real.pi / 4 - δ / 2) = Real.pi / 2 - δ by ring,
      Real.cos_pi_div_two_sub]
  have hsin : δ / 2 ≤ Real.sin δ := calc
    δ / 2 = (1 / 2) * δ := by ring
    _ ≤ 2 / Real.pi * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      apply (le_div_iff₀ Real.pi_pos).2
      linarith [Real.pi_le_four]
    _ ≤ Real.sin δ := Real.mul_le_sin hδ.le (by linarith [Real.two_le_pi])
  have hsqrt : (2 * x)⁻¹ ≤ Real.sqrt (Real.sin δ) := by
    apply Real.le_sqrt_of_sq_le
    apply le_trans _ hsin
    dsimp [δ]
    field_simp
    linarith
  have hinv := inv_anti₀ (show 0 < (2 * x)⁻¹ by positivity) hsqrt
  rw [inv_inv] at hinv
  refine ⟨hstrip, ?_⟩
  rw [hcos]
  change 1 + _ ≤ 3 * x
  linarith

private theorem translated_decay {k l n : ℝ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hl : 1 ≤ l) (hln : l ≤ n) (y : ℝ) :
    Real.exp (-|y + Real.log (k / l)| / 2) ≤ n * Real.exp (-|y| / 2) := by
  have hk₀ : 0 < k := by linarith
  have hl₀ : 0 < l := by linarith
  have hlog : |Real.log (k / l)| ≤ Real.log n := by
    rw [Real.log_div hk₀.ne' hl₀.ne', abs_sub_le_iff]
    constructor <;> linarith [Real.log_nonneg hk, Real.log_nonneg hl,
      Real.log_le_log hk₀ hkn, Real.log_le_log hl₀ hln]
  have htri : |y| ≤ |y + Real.log (k / l)| + |Real.log (k / l)| := by
    simpa using abs_add_le (y + Real.log (k / l)) (-Real.log (k / l))
  calc
    _ ≤ Real.exp (Real.log n + -|y| / 2) := by
      apply Real.exp_le_exp.mpr
      linarith [abs_nonneg (Real.log (k / l))]
    _ = _ := by rw [Real.exp_add, Real.exp_log (hk₀.trans_le hkn)]

/-- Card 22. For coefficients bounded by one and N ≥ 2, the dual is continuous and its norm is
bounded by a constant times N⁵³ exp(−|y|/2).
Titchmarsh, §§10.10, 10.18, pp. 269, 276–277, polynomial tail envelope. -/
theorem dual_envelope : ∃ C > (0 : ℝ), ∀ N : ℕ, 2 ≤ N → ∀ b : ℕ → ℝ, bd N b →
    Continuous (dual N b) ∧ ∀ y : ℝ, ‖dual N b y‖ ≤ C*(N : ℝ)^53*Real.exp (-|y|/2) := by
  obtain ⟨C, hC, hK⟩ := kernel_bound
  refine ⟨3 * C, by positivity, fun N hN b hb ↦ ?_⟩
  obtain ⟨hstrip, hangle⟩ := angle_bounds hN
  have him (u : ℝ) : |((u : ℂ) + Complex.I * (angle N : ℂ)).im| < Real.pi / 4 := by
    simpa [Complex.mul_im] using hstrip
  constructor
  · unfold dual
    refine continuous_finsetSum _ fun k _ ↦ continuous_finsetSum _ fun l _ ↦
      continuous_const.mul (continuous_iff_continuousAt.mpr fun y ↦ ?_)
    exact (kernel_symmetry (him (y + Real.log ((k : ℝ) / l)))).2.2.continuousAt.comp
      (f := fun t : ℝ ↦ ((t + Real.log ((k : ℝ) / l) : ℝ) : ℂ) + Complex.I * (angle N : ℂ))
      (by fun_prop)
  · intro y
    calc
      ‖dual N b y‖ ≤ ∑ _k ∈ D N, ∑ _l ∈ D N,
          3 * C * (N : ℝ)^51 * Real.exp (-|y| / 2) := by
        unfold dual
        refine norm_sum_le_of_le _ fun k hk ↦ norm_sum_le_of_le _ fun l hl ↦ ?_
        have hmem (j : ℕ) (hj : j ∈ D N) : 1 ≤ (j : ℝ) ∧ (j : ℝ) ≤ N := by
          exact_mod_cast Finset.mem_Icc.mp hj
        obtain ⟨hk₁, hkN⟩ := hmem k hk
        obtain ⟨hl₁, hlN⟩ := hmem l hl
        have hden : 1 ≤ Real.sqrt ((k : ℝ) * l) := Real.one_le_sqrt.mpr
          (one_le_mul_of_one_le_of_one_le hk₁ hl₁)
        have hcoef : |b k * b l / Real.sqrt ((k : ℝ) * l)| ≤ 1 := by
          rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _), div_le_one (by linarith),
            abs_mul]
          calc
            _ ≤ 1 * 1 := mul_le_mul (hb k hk) (hb l hl) (abs_nonneg _) zero_le_one
            _ ≤ _ := by simpa using hden
        let u := y + Real.log ((k : ℝ) / l)
        have hkernel := hK _ (him u)
        simp [Complex.mul_im, Complex.mul_re] at hkernel
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc
          _ ≤ 1 * (C * (3 * (N : ℝ)^50) * ((N : ℝ) * Real.exp (-|y| / 2))) := by
            apply mul_le_mul hcoef _ (norm_nonneg _) zero_le_one
            apply hkernel.trans
            gcongr
            exact translated_decay hk₁ hkN hl₁ hlN y
          _ = _ := by ring
      _ = _ := by simp [D, nsmul_eq_mul]; ring

end RiemannMasullo.Selberg
