module

public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.PSeries

/-! # Fourier series of smooth functions on a short interval, with weighted summable coefficients

A smooth function on the line that vanishes outside `(-1/2, 1/2)` is, on `[-1/2, 1/2]`, the sum
of a Fourier series with period one whose coefficients are summable against every power of
`1 + |n|`. This is Poisson's summation formula for the Schwartz function it defines: the
coefficients are the values of its Fourier transform at the integers.

Hence every smooth function on the line agrees on a bounded interval `[-R, R]` with such a
series of period `4 R` (`exists_fourierSeries_on_Icc`), and so does each monomial on
`[-1/4, 1/4]` with period one (`exists_fourierSeries_pow`). -/

@[expose] public section

open Complex MeasureTheory Real Set
open scoped ContDiff FourierTransform SchwartzMap

namespace RiemannMasullo

/-- The exponential `exp (2 π i n y)` has norm one. -/
theorem norm_cexp_two_pi_I_mul (n : ℤ) (y : ℝ) : ‖cexp (2 * π * I * n * y)‖ = 1 := by
  rw [show (2 * π * I * n * y : ℂ) = ((2 * π * n * y : ℝ) : ℂ) * I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

/-- A smooth function that vanishes outside `(-1/2, 1/2)` is on `[-1/2, 1/2]` the sum of a
Fourier series of period one whose coefficients are summable against every power of
`1 + |n|`. The coefficients are the values at the integers of the Fourier transform of the
function, and the expansion is Poisson's summation formula. -/
theorem exists_fourierSeries_of_contDiff_of_support {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hsupp : ∀ y : ℝ, 1 / 2 ≤ |y| → f y = 0) :
    ∃ a : ℤ → ℂ, (∀ p : ℕ, Summable fun n : ℤ ↦ ‖a n‖ * (1 + |(n : ℝ)|) ^ p) ∧
      ∀ y : ℝ, |y| ≤ 1 / 2 → HasSum (fun n : ℤ ↦ a n * cexp (2 * π * I * n * y)) (f y) := by
  have hcs : HasCompactSupport f := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) (1 / 2)) ?_
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    by_contra h
    exact hy (hsupp y (not_le.mp h).le)
  let F : 𝓢(ℝ, ℂ) := hcs.toSchwartzMap hf
  have hF (y : ℝ) : F y = f y := rfl
  let a (n : ℤ) : ℂ := 𝓕 F (n : ℝ)
  have hdecay (p : ℕ) : ∃ C : ℝ, ∀ x : ℝ, (1 + |x|) ^ p * ‖𝓕 F x‖ ≤ C := by
    refine ⟨2 ^ p * (Finset.Iic (p, 0)).sup (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) (𝓕 F),
      fun x ↦ ?_⟩
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (p, 0)) (k := p) (n := 0)
      le_rfl le_rfl (𝓕 F) x
    simpa [norm_iteratedFDeriv_zero] using h
  have hsum (p : ℕ) : Summable fun n : ℤ ↦ ‖a n‖ * (1 + |(n : ℝ)|) ^ p := by
    obtain ⟨C, hC⟩ := hdecay (p + 2)
    have hC0 : 0 ≤ C :=
      (by positivity : (0 : ℝ) ≤ (1 + |(0 : ℝ)|) ^ (p + 2) * ‖𝓕 F 0‖).trans (hC 0)
    have hbase : Summable fun n : ℤ ↦ C * (1 / (n : ℝ) ^ 2 + if n = 0 then 1 else 0) :=
      ((Real.summable_one_div_int_pow.mpr one_lt_two).add
        (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable).mul_left C
    refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) hbase
    have hpos : (0 : ℝ) < 1 + |(n : ℝ)| := by positivity
    have h1 : ‖a n‖ * (1 + |(n : ℝ)|) ^ p ≤ C / (1 + |(n : ℝ)|) ^ 2 := by
      rw [le_div_iff₀ (pow_pos hpos 2)]
      calc ‖a n‖ * (1 + |(n : ℝ)|) ^ p * (1 + |(n : ℝ)|) ^ 2
          = (1 + |(n : ℝ)|) ^ (p + 2) * ‖𝓕 F (n : ℝ)‖ := by
            rw [pow_add]
            ring
        _ ≤ C := hC n
    refine h1.trans ?_
    rw [div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ hC0
    by_cases hn : n = 0
    · subst hn
      simp
    · rw [ite_eq_right hn, add_zero]
      have hn' : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
      rw [← sq_abs (n : ℝ)]
      exact one_div_le_one_div_of_le (pow_pos hn' 2) (pow_le_pow_left₀ hn'.le (by linarith) 2)
  refine ⟨a, hsum, fun y hy ↦ ?_⟩
  have hpoisson := SchwartzMap.tsum_eq_tsum_fourier F y
  have hleft : ∑' n : ℤ, F (y + n) = f y := by
    rw [tsum_eq_single 0 fun n hn ↦ ?_]
    · simp [hF]
    · rw [hF]
      apply hsupp
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      have h2 : |(n : ℝ)| ≤ |y + n| + |y| := by
        have := abs_sub (y + n) y
        simpa using this
      linarith
  have hs0 : Summable fun n : ℤ ↦ ‖a n‖ := by simpa using hsum 0
  have hright : Summable fun n : ℤ ↦ a n * cexp (2 * π * I * n * y) :=
    Summable.of_norm (by simpa [norm_cexp_two_pi_I_mul] using hs0)
  have hval : ∑' n : ℤ, a n * cexp (2 * π * I * n * y) = f y := by
    rw [← hleft, hpoisson]
    refine tsum_congr fun n ↦ ?_
    rw [fourier_coe_apply]
    simp [a]
  exact hval ▸ hright.hasSum

/-- Every smooth function on the line agrees on `[-R, R]` with a Fourier series of period `4 R`
whose coefficients are summable against every power of `1 + |n|`. -/
theorem exists_fourierSeries_on_Icc {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) {R : ℝ} (hR : 0 < R) :
    ∃ a : ℤ → ℂ, (∀ p : ℕ, Summable fun n : ℤ ↦ ‖a n‖ * (1 + |(n : ℝ)|) ^ p) ∧
      ∀ r : ℝ, |r| ≤ R →
        HasSum (fun n : ℤ ↦ a n * cexp (2 * π * I * n * (r / (4 * R) : ℝ))) (h r) := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let f (y : ℝ) : ℂ := (b y : ℂ) * h (4 * R * y)
  have hf : ContDiff ℝ ∞ f :=
    (Complex.ofRealCLM.contDiff.comp b.contDiff).mul (hh.comp (contDiff_const.mul contDiff_id))
  obtain ⟨a, ha, hsum⟩ := exists_fourierSeries_of_contDiff_of_support hf fun y hy ↦ by
    have h0 : b y = 0 := b.zero_of_le_dist (by
      rw [Real.dist_eq, sub_zero]
      exact hy)
    simp [f, h0]
  refine ⟨a, ha, fun r hr ↦ ?_⟩
  have hy : |r / (4 * R)| ≤ 1 / 4 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * R), div_le_iff₀ (by positivity)]
    linarith
  have h1 : b (r / (4 * R)) = 1 := b.one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact hy)
  have h2 := hsum (r / (4 * R)) (hy.trans (by norm_num))
  have h3 : f (r / (4 * R)) = h r := by
    change (b (r / (4 * R)) : ℂ) * h (4 * R * (r / (4 * R))) = h r
    rw [h1, mul_div_cancel₀ r (by positivity : (4 * R) ≠ 0)]
    simp
  rwa [h3] at h2

/-- Each monomial agrees on `[-1/4, 1/4]` with a Fourier series of period one whose coefficients
are summable against every power of `1 + |n|`. -/
theorem exists_fourierSeries_pow (e : ℕ) :
    ∃ a : ℤ → ℂ, (∀ p : ℕ, Summable fun n : ℤ ↦ ‖a n‖ * (1 + |(n : ℝ)|) ^ p) ∧
      ∀ y : ℝ, |y| ≤ 1 / 4 →
        HasSum (fun n : ℤ ↦ a n * cexp (2 * π * I * n * y)) ((y : ℂ) ^ e) := by
  have hh : ContDiff ℝ ∞ (fun r : ℝ ↦ ((r : ℂ)) ^ e) :=
    (Complex.ofRealCLM.contDiff).pow e
  obtain ⟨a, ha, hsum⟩ := exists_fourierSeries_on_Icc hh (R := 1 / 4) (by norm_num)
  refine ⟨a, ha, fun y hy ↦ ?_⟩
  have h := hsum y hy
  have h1 : y / (4 * (1 / 4)) = y := by ring
  rwa [h1] at h

end RiemannMasullo
