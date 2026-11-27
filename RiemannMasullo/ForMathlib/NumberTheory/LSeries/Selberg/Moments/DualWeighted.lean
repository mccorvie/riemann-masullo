module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.TaperSpec
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.DualFormula
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Gaussian.GaussianExpansion
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Gaussian.WeightedGaussian
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

public section

open MeasureTheory Set

namespace RiemannMasullo.Selberg

private lemma constTerm_bound (N : ℕ) (b : ℕ → ℝ) (hb : bd N b) :
    |constTerm N b| ≤ (N : ℝ)^2 := by
  have sum_bound (f : ℕ → ℝ) (hf : ∀ n ∈ D N, |f n| ≤ 1) : |∑ n ∈ D N, f n| ≤ N := by
    calc
      _ ≤ ∑ n ∈ D N, |f n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ D N, (1 : ℝ) := Finset.sum_le_sum hf
      _ = N := by simp [D]
  rw [constTerm, abs_mul, sq]
  refine mul_le_mul (sum_bound _ fun n hn ↦ ?_) (sum_bound _ hb) (abs_nonneg _) (by positivity)
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [abs_div, abs_of_nonneg (zero_le_one.trans hn')]
  exact (div_le_self (abs_nonneg _) hn').trans (hb n hn)

private lemma weighted_sub_sq_le (u a : ℂ) {x q : ℝ} (hx : 1 < x) (hq : 0 ≤ q) :
    ‖u - a / (2 * (x : ℂ))‖^2 * x^(-q) ≤
      2 * (‖u‖^2 * x^(-q)) + ‖a‖^2 / 2 * x^(-2 : ℝ) := by
  have hx₀ := zero_lt_one.trans hx
  let v := a / (2 * (x : ℂ))
  have hsq : ‖u - v‖^2 ≤ 2 * (‖u‖^2 + ‖v‖^2) := by
    calc
      _ ≤ (‖u‖ + ‖v‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) _
      _ ≤ _ := by nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  have hw := Real.rpow_le_one_of_one_le_of_nonpos hx.le (neg_nonpos.mpr hq)
  calc
    _ ≤ 2 * (‖u‖^2 + ‖v‖^2) * x^(-q) := mul_le_mul_of_nonneg_right hsq (by positivity)
    _ ≤ 2 * (‖u‖^2 * x^(-q)) + 2 * ‖v‖^2 := by
      nlinarith [mul_le_mul_of_nonneg_left hw (sq_nonneg ‖v‖)]
    _ = _ := by
      simp only [v, norm_div, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hx₀, Real.rpow_neg hx₀.le, Real.rpow_two]
      field_simp

private lemma dualMass_le (N : ℕ) (hN : 2 ≤ N) (q : ℝ) (hq : 0 ≤ q) :
    dualMass N q ≤ 4 * J N (beta N) q + (constTerm N (beta N))^2 := by
  let b := beta N
  let a : ℂ := osc (-angle N) * (constTerm N b : ℂ)
  let G := fun x : ℝ ↦ ‖g N b x‖^2 * x^(-q)
  let F := fun x : ℝ ↦ ‖g N b x - a / (2 * (x : ℂ))‖^2 * x^(-q)
  have hosc (t : ℝ) : ‖osc t‖ = 1 := Complex.norm_exp_I_mul_ofReal t
  have hsym (y : ℝ) : ‖dual N b |y|‖ = ‖dual N b y‖ := by
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]
    · rw [abs_of_nonpos hy, (dual_formula N hN b y).1, norm_star]
  have hmass : dualMass N q = 2 * ∫ x in Ioi (1 : ℝ), F x := by
    calc
      _ = ∫ y : ℝ, Real.exp (-q * |y|) * ‖dual N b |y|‖^2 := by simp only [dualMass, hsym, b]
      _ = 2 * ∫ y in Ioi (0 : ℝ), Real.exp (-q * y) * ‖dual N b y‖^2 :=
        integral_comp_abs (f := fun y ↦ Real.exp (-q * y) * ‖dual N b y‖^2)
      _ = 2 * ∫ y in Ioi (0 : ℝ), Real.exp y • F (Real.exp y) := by
        congr 1
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y _
        dsimp only
        rw [(dual_formula N hN b y).2, norm_mul, norm_mul, hosc, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
        have hs : Real.exp (y / 2)^2 = Real.exp y := by
          rw [sq, ← Real.exp_add]
          congr 1
          ring
        rw [hs, mul_comm (-q) y, Real.exp_mul]
        dsimp [F, a]
        ring
      _ = _ := by rw [integral_comp_exp_Ioi, Real.exp_zero]
  have hG : IntegrableOn G (Ioi 1) := (gaussian_expansion N hN b q hq).1
  have hR := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) zero_lt_one
  have hint : (∫ x in Ioi (1 : ℝ), F x) ≤
      ∫ x in Ioi (1 : ℝ), 2 * G x + ‖a‖^2 / 2 * x^(-2 : ℝ) := by
    refine integral_mono_of_nonneg ?_ ((hG.const_mul 2).add (hR.const_mul _)) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      dsimp [F]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans hx).le _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact weighted_sub_sq_le _ _ hx hq
  rw [integral_add (hG.const_mul 2) (hR.const_mul _), integral_const_mul, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one] at hint
  have ha : ‖a‖^2 = (constTerm N b)^2 := by
    simp [a, hosc, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hmass]
  change 2 * _ ≤ 4 * (∫ x in Ioi (1 : ℝ), G x) + (constTerm N b)^2
  rw [ha, Real.one_rpow] at hint
  linarith

/-- Card 35. The squared norm integral of the tapered dual with weight exp(−q|y|) is bounded by a
constant times N⁵⁰/(q log N) for 0 < q ≤ 1/2.
Titchmarsh, §§10.10, 10.17, pp. 269–270, 275–276. -/
theorem dual_weighted : ∃ C > (0 : ℝ), ∀ N : ℕ, 2 ≤ N → ∀ q : ℝ, 0 < q → q ≤ 1/2 →
    dualMass N q ≤ C*(N : ℝ)^50/(q*Real.log N) := by
  obtain ⟨C, hC, hJ⟩ := weighted_gaussian
  refine ⟨4 * C + 1, by positivity, fun N hN q hq hq' ↦ ?_⟩
  have hN' : 1 < (N : ℝ) := by exact_mod_cast hN
  have hden := mul_pos hq (Real.log_pos hN')
  have hden_le : q * Real.log N ≤ N := by
    calc
      _ ≤ 1 * Real.log N := mul_le_mul_of_nonneg_right (by linarith) (Real.log_pos hN').le
      _ ≤ N := by linarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans hN')]
  have hconst := constTerm_bound N (beta N) (taper_spec N hN).2
  have hs : (constTerm N (beta N))^2 ≤ (N : ℝ)^4 := by
    simpa [sq_abs, ← pow_mul] using pow_le_pow_left₀ (abs_nonneg _) hconst 2
  have hpow : (N : ℝ)^4 ≤ (N : ℝ)^50 / (q * Real.log N) := by
    apply (le_div_iff₀ hden).mpr
    calc
      _ ≤ (N : ℝ)^4 * N := mul_le_mul_of_nonneg_left hden_le (by positivity)
      _ = (N : ℝ)^5 := by ring
      _ ≤ _ := pow_le_pow_right₀ hN'.le (by decide)
  calc
    _ ≤ 4 * J N (beta N) q + (constTerm N (beta N))^2 := dualMass_le N hN q hq.le
    _ ≤ 4 * (C * (N : ℝ)^50 / (q * Real.log N)) + (N : ℝ)^50 / (q * Real.log N) := by
      gcongr
      · exact hJ N hN q hq hq'
      · exact hs.trans hpow
    _ = _ := by ring

end RiemannMasullo.Selberg
