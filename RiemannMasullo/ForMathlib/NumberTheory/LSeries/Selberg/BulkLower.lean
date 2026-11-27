module

public import RiemannMasullo.External.HardyCriticalLine.HardyFunctionNormalization
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import RiemannMasullo.External.HardyCriticalLine.LowerIntegralBound
import RiemannMasullo.External.HardyCriticalLine.UpperIntegralBound
import Mathlib.Analysis.Real.Pi.Bounds

public section

open HardyCriticalLine MeasureTheory Set

namespace RiemannMasullo

local notation "mode(" n ", " t ")" => (((n : ℕ) : ℂ) ^ (-criticalLinePoint t))
local notation "poly(" N ", " b ", " t ")" =>
  (∑ n ∈ Finset.Icc 1 N, ((b n : ℝ) : ℂ) * mode(n, t))

/-- The contribution of one mode to a dyadic mean after removing its constant term. -/
private theorem spectralLineJet_centered_mode {n : ℕ} (hn : 0 < n) (T : ℝ) :
    ‖(∫ t in T..2 * T, mode(n, t)) - (if n = 1 then (T : ℂ) else 0)‖ ≤
      4 / Real.sqrt n := by
  by_cases h : n = 1
  · subst n
    simp [two_mul, sub_eq_add_neg]
  · simpa [h] using norm_integral_cpow_neg_criticalLinePoint_le (n := n) (by omega) T

/-- Uniform pointwise control for all coefficient choices of a finite mollifier. -/
theorem spectralLineJet_mollifier_norm (N : ℕ) (b : ℕ → ℝ)
    (hb : ∀ n ∈ Finset.Icc 1 N, |b n| ≤ 1) (t : ℝ) :
    ‖poly(N, b, t)‖ ≤ 2 * Real.sqrt N := by
  calc _ ≤ ∑ n ∈ Finset.Icc 1 N, ‖((b n : ℝ) : ℂ) * mode(n, t)‖ := norm_sum_le _ _
       _ ≤ ∑ n ∈ Finset.Icc 1 N, 1 / Real.sqrt n := by
         refine Finset.sum_le_sum fun n h ↦ ?_
         rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp h).1]
         exact mul_le_of_le_one_left (by positivity) (hb n h)
       _ ≤ _ := sum_Icc_one_div_sqrt_le_two_mul_sqrt N

/-- Integrating a Dirichlet polynomial against a second polynomial squared leaves its
constant coefficient, with error controlled by the three elementary inverse-square-root sums. -/
private theorem spectralLineJet_cutoff_mollified_mean (M N : ℕ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (b : ℕ → ℝ) (hb₁ : b 1 = 1) (hb : ∀ n ∈ Finset.Icc 1 N, |b n| ≤ 1) (T : ℝ) :
    ‖(∫ t in T..2 * T, (∑ k ∈ Finset.Icc 1 M, mode(k, t)) * poly(N, b, t) ^ 2) - (T : ℂ)‖ ≤
      32 * Real.sqrt M * N := by
  classical
  let S := (Finset.Icc 1 M ×ˢ Finset.Icc 1 N) ×ˢ Finset.Icc 1 N
  let n (p : (ℕ × ℕ) × ℕ) := p.1.1 * p.1.2 * p.2
  let B (p : (ℕ × ℕ) × ℕ) : ℂ := (b p.1.2 : ℂ) * (b p.2 : ℂ)
  have hparts {p} (hp : p ∈ S) :=
    (Finset.mem_product.mp (Finset.mem_product.mp hp).1).1
  have hn (p) (hp : p ∈ S) : 0 < n p :=
    Nat.mul_pos (Nat.mul_pos (Finset.mem_Icc.mp (hparts hp)).1
      (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_product.mp hp).1).2).1)
      (Finset.mem_Icc.mp (Finset.mem_product.mp hp).2).1
  have hnorm (p) (hp : p ∈ S) : ‖B p‖ ≤ 1 := by
    dsimp only [B]
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hb _ (Finset.mem_product.mp hp).2)).trans
      (hb _ (Finset.mem_product.mp (Finset.mem_product.mp hp).1).2)
  have hexp (t : ℝ) : (∑ k ∈ Finset.Icc 1 M, mode(k, t)) * poly(N, b, t) ^ 2 =
      ∑ p ∈ S, B p * mode(n p, t) := by
    dsimp only [S, B, n]
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp only [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun d _ ↦
      Finset.sum_congr rfl fun e _ ↦ ?_
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  have hint : (∫ t in T..2 * T, (∑ k ∈ Finset.Icc 1 M, mode(k, t)) * poly(N, b, t) ^ 2) =
      ∑ p ∈ S, B p * ∫ t in T..2 * T, mode(n p, t) := by
    simp_rw [hexp]
    rw [intervalIntegral.integral_finsetSum]
    · exact Finset.sum_congr rfl fun p _ ↦ intervalIntegral.integral_const_mul _ _
    · exact fun p hp ↦ (continuous_const.mul (continuous_cpow_neg_criticalLinePoint (hn p hp))).intervalIntegrable ..
  have hdiag : ∑ p ∈ S, B p * (if n p = 1 then (T : ℂ) else 0) = T := by
    rw [Finset.sum_eq_single ((1, 1), 1)]
    · simp [B, n, hb₁]
    · rintro ⟨⟨k, d⟩,e⟩ _ hne
      have h : k * d * e ≠ 1 := by
        intro he
        have split {i j : ℕ} (h : i * j = 1) : i = 1 ∧ j = 1 :=
          ⟨Nat.eq_one_of_dvd_one ⟨j, h.symm⟩, Nat.eq_one_of_dvd_one ⟨i, by simpa [Nat.mul_comm] using h.symm⟩⟩
        obtain ⟨hkd, he⟩ := split he
        obtain ⟨hk, hd⟩ := split hkd
        exact hne (by simp [hk, hd, he])
      simp [n, h]
    · simp [S, hM, hN]
  rw [hint, ← hdiag, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ S, ‖B p * (∫ t in T..2 * T, mode(n p, t)) -
        B p * (if n p = 1 then (T : ℂ) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ S, 4 / Real.sqrt (n p) := by
      refine Finset.sum_le_sum fun p hp ↦ ?_
      rw [← mul_sub, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hnorm p hp)).trans
        (spectralLineJet_centered_mode (hn p hp) T)
    _ = 4 * (∑ k ∈ Finset.Icc 1 M, 1 / Real.sqrt k) *
        (∑ d ∈ Finset.Icc 1 N, 1 / Real.sqrt d) ^ 2 := by
      dsimp only [S, n]
      rw [sq, mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum]
      simp only [Finset.sum_product, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun d _ ↦
        Finset.sum_congr rfl fun e _ ↦ ?_
      rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
      ring
    _ ≤ 4 * (2 * Real.sqrt M) * (2 * Real.sqrt N) ^ 2 := by
      gcongr <;> apply sum_Icc_one_div_sqrt_le_two_mul_sqrt
    _ = _ := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]; ring

/-- On dyadic intervals the critical-line mean of ζ times the square of any normalized
finite Dirichlet mollifier of length `N` is `T + O(N √T)`, uniformly in the bounded
coefficients. This is the bulk first-moment step for Selberg's mollified Hardy function,
which enters the classical count supporting the refutation of (10.3.1.18), p. 451. -/
theorem spectralLineJet_mollified_zeta_dyadic_mean :
    ∃ C > (0 : ℝ), ∃ T₀ ≥ (2 : ℝ), ∀ T ≥ T₀, ∀ (N : ℕ) (b : ℕ → ℝ),
      1 ≤ N → b 1 = 1 → (∀ n ∈ Finset.Icc 1 N, |b n| ≤ 1) →
      ‖(∫ t in T..2 * T, riemannZeta (criticalLinePoint t) * poly(N, b, t) ^ 2) - (T : ℂ)‖ ≤
        C * N * Real.sqrt T := by
  obtain ⟨K, hK, T₀, hT₀, happrox⟩ := exists_uniform_zetaFirstApproximation
  refine ⟨4 * K + 32, by positivity, T₀, hT₀, ?_⟩
  intro T hT N b hN hb₁ hb
  have hT₂ := hT₀.trans hT
  have hTpos : 0 < T := by linarith
  have hroot : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  let M := zetaFirstApproximationCutoff T
  let D (t : ℝ) := ∑ k ∈ Finset.Icc 1 M, mode(k, t)
  let P (t : ℝ) := poly(N, b, t)
  let Z (t : ℝ) := riemannZeta (criticalLinePoint t)
  have hD : Continuous D := continuous_finsetSum _ fun k hk ↦
    continuous_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp hk).1
  have hP : Continuous P := continuous_finsetSum _ fun k hk ↦
    continuous_const.mul (continuous_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp hk).1)
  have hZ : Continuous Z := continuous_riemannZeta_criticalLine
  have hR : ‖∫ t in T..2 * T, (Z t - D t) * P t ^ 2‖ ≤ (4 * K) * N * Real.sqrt T := by
    have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := 2 * T)
      (C := (K / Real.sqrt T) * (2 * Real.sqrt N) ^ 2)
      (f := fun t ↦ (Z t - D t) * P t ^ 2) (fun t ht ↦ by
        rw [uIoc_of_le (by linarith)] at ht
        rw [norm_mul, norm_pow]
        apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) (spectralLineJet_mollifier_norm N b hb t) 2)
          (by positivity) (by positivity)
        have H₀ := happrox T t hT ht.1.le ht.2
        norm_num [Z, D, M, criticalLinePoint] at H₀ ⊢
        exact H₀)
    refine H.trans_eq ?_
    rw [abs_of_pos (by linarith), mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    field_simp [hroot.ne']
    nlinarith [Real.sq_sqrt hTpos.le]
  have hmain := spectralLineJet_cutoff_mollified_mean M N (one_le_zetaFirstApproximationCutoff hT₂)
    hN b hb₁ hb T
  have hadd : (∫ t in T..2 * T, Z t * P t ^ 2) -
      (∫ t in T..2 * T, D t * P t ^ 2) = ∫ t in T..2 * T, (Z t - D t) * P t ^ 2 := by
    rw [← intervalIntegral.integral_sub (f := fun t ↦ Z t * P t ^ 2) (g := fun t ↦ D t * P t ^ 2)
      ((hZ.mul (hP.pow 2)).intervalIntegrable ..) ((hD.mul (hP.pow 2)).intervalIntegrable ..)]
    simp only [sub_mul]
  change ‖(∫ t in T..2 * T, Z t * P t ^ 2) - (T : ℂ)‖ ≤ _
  calc
    _ ≤ ‖(∫ t in T..2 * T, Z t * P t ^ 2) - (∫ t in T..2 * T, D t * P t ^ 2)‖ +
        ‖(∫ t in T..2 * T, D t * P t ^ 2) - (T : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ (4 * K) * N * Real.sqrt T + 32 * Real.sqrt M * N := by rw [hadd]; exact add_le_add hR hmain
    _ ≤ (4 * K) * N * Real.sqrt T + 32 * Real.sqrt T * N := by
      gcongr
      exact zetaFirstApproximationCutoff_le_height hTpos.le
    _ = _ := by ring

/-- Selberg's gamma-exponential weight on a dyadic interval has a positive uniform
lower bound at its natural height scale. -/
private theorem spectralLineJet_selberg_gamma_dyadic_lower :
    ∃ c > (0 : ℝ), ∀ T ≥ (2 : ℝ), ∀ t ∈ Icc T (2 * T),
      c * (2 * T) ^ (-(1 / 4) : ℝ) ≤ ‖Complex.Gamma (criticalLineGammaArgument t)‖ *
        Real.exp ((Real.pi / 4 - 1 / (4 * T)) * t) := by
  obtain ⟨c, hc, hanchor⟩ := exists_pos_gammaBinetExponentialRatio_at_one
  let A := -(1 / 4) - (1 / 4) * Real.log Real.pi - 2
  refine ⟨c * Real.exp A, by positivity, ?_⟩
  intro T hT t ht
  let z := criticalLineGammaArgument t
  have ht₀ : 0 < t := by linarith [ht.1]
  have hz : 0 < z.re := by rw [criticalLineGammaArgument_re]; norm_num
  have hn : z ≠ 0 := fun h ↦ by rw [h] at hz; exact lt_irrefl _ hz
  have hlog : Real.log ‖z‖ ≤ Real.log (2 * T) := by
    apply Real.log_le_log (norm_pos_iff.mpr hn)
    calc ‖z‖ ≤ ‖(1 / 4 : ℂ)‖ + ‖((t / 2 : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
         _ ≤ _ := by
           rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
             abs_of_nonneg (by positivity)]
           norm_num
           linarith [ht.2]
  have harg := Complex.arg_le_pi_div_two_iff.mpr (Or.inl hz.le)
  have hrem : -1 ≤ (gammaBinetLogRemainder z).re := by
    have h₁ := norm_gammaBinetLogRemainder_criticalLine_le ht₀
    have h₂ := Complex.abs_re_le_norm (gammaBinetLogRemainder z)
    have h₃ : 1 / (2 * t) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [ht.1])
    exact (neg_le_of_abs_le (h₂.trans (h₁.trans h₃)))
  have hmain : (gammaRStirlingLogMain z).re =
      -(1 / 4) * Real.log ‖z‖ - (t / 2) * Complex.arg z - 1 / 4 - (1 / 4) * Real.log Real.pi := by
    simp only [gammaRStirlingLogMain, Complex.sub_re, Complex.mul_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.log_re, Complex.log_im, z,
      criticalLineGammaArgument_re, criticalLineGammaArgument_im]
    norm_num
  have hratio := gammaBinetExponentialRatio_eq_at_one hz
  rw [hanchor, div_eq_iff (Complex.exp_ne_zero _)] at hratio
  have hfac := congrArg norm hratio
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, Complex.norm_exp] at hfac
  have hpi : ‖(Real.pi : ℂ) ^ (-z)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.neg_re, criticalLineGammaArgument_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt (by linarith [Real.pi_gt_three])) (by norm_num)
  have hcancel : t / (4 * T) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith [ht.2])
  have hweight : A + Real.log (2 * T) * (-(1 / 4)) ≤
      (gammaRStirlingLogMain z + gammaBinetLogRemainder z).re + (Real.pi / 4 - 1 / (4 * T)) * t := by
    rw [Complex.add_re, hmain]
    have har := mul_le_mul_of_nonneg_left harg (show 0 ≤ t / 2 by positivity)
    dsimp [A]
    rw [sub_mul, show 1 / (4 * T) * t = t / (4 * T) by ring]
    linarith only [hlog, har, hrem, hcancel]
  rw [Real.rpow_def_of_pos (by linarith : 0 < 2 * T), mul_assoc, ← Real.exp_add]
  calc
    _ ≤ c * Real.exp ((gammaRStirlingLogMain z + gammaBinetLogRemainder z).re +
        (Real.pi / 4 - 1 / (4 * T)) * t) := by gcongr
    _ = (‖(Real.pi : ℂ) ^ (-z)‖ * ‖Complex.Gamma z‖) * Real.exp ((Real.pi / 4 - 1 / (4 * T)) * t) := by
      rw [Real.exp_add, ← mul_assoc, ← hfac]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) hpi) (Real.exp_pos _).le

/-- The critical-line Dirichlet polynomial is the explicit exponential sum in the
Selberg weight, with the same real coefficients. -/
private theorem spectralLineJet_mollifier_as_phases (N : ℕ) (b : ℕ → ℝ) (t : ℝ) :
    poly(N, b, t) = ∑ n ∈ Finset.Icc 1 N, ((b n / Real.sqrt n : ℝ) : ℂ) *
      Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I) := by
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn₀ : 0 < n := (Finset.mem_Icc.mp hn).1
  have hnℝ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmode0 : mode(n, 0) = ((1 / Real.sqrt n : ℝ) : ℂ) := by
    change (n : ℂ) ^ (-(1 / 2 + ((0 : ℝ) : ℂ) * Complex.I)) = _
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    rw [show (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by norm_num, ← Complex.ofReal_natCast,
      ← Complex.ofReal_cpow hnℝ, Real.rpow_neg hnℝ, ← Real.sqrt_eq_rpow, one_div]
  rw [cpow_neg_criticalLinePoint_eq_mode hn₀ t, hmode0,
    show Complex.log (n : ℂ) = (Real.log n : ℂ) by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hnℝ]]
  push_cast
  rw [show -Complex.I * Complex.log (n : ℂ) * (t : ℂ) = -(t * Complex.log (n : ℂ)) * Complex.I by ring]
  ring


/-- The dyadic absolute bulk moment used by Selberg's short-interval method. There are
absolute positive constants `c, η` such that the gamma-weighted integral of
`|Z(t)| |∑ bₙ n^(-1/2-it)|²` on `[T,2T]` (and hence on `[h,2T]` for every `h ≤ T`) is at least `c(2T)^(3/4)` whenever
the mollifier has length at most `η √T`, constant coefficient one, and real
coefficients of absolute value at most one. No zero-count assumption is used. -/
theorem spectralLineJet_selberg_mollified_bulk_lower :
    ∃ c > (0 : ℝ), ∃ η > (0 : ℝ), ∃ T₀ ≥ (2 : ℝ), ∀ T ≥ T₀, ∀ (N : ℕ) (b : ℕ → ℝ),
      1 ≤ N → N ≤ η * Real.sqrt T → b 1 = 1 → (∀ n ∈ Finset.Icc 1 N, |b n| ≤ 1) →
      ∀ h ≤ T, c * (2 * T) ^ (3 / 4 : ℝ) ≤
        ∫ t in h..2 * T, ‖Complex.Gamma (1 / 4 + ((t / 2 : ℝ) : ℂ) * Complex.I)‖ *
          Real.exp ((Real.pi / 4 - 1 / (4 * T)) * t) *
          ‖∑ n ∈ Finset.Icc 1 N, ((b n / Real.sqrt n : ℝ) : ℂ) *
            Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ^ 2 * |hardyZ t| := by
  obtain ⟨C, hC, T₀, hT₀, hm⟩ := spectralLineJet_mollified_zeta_dyadic_mean
  obtain ⟨c, hc, hg⟩ := spectralLineJet_selberg_gamma_dyadic_lower
  refine ⟨c / 4, by positivity, 1 / (2 * C), by positivity, T₀, hT₀, ?_⟩
  intro T hT N b hN hlen hb₁ hb h hh
  have hT₂ := hT₀.trans hT
  have hTpos : 0 < T := by linarith
  have h2T : 0 < 2 * T := by positivity
  let P (t : ℝ) := poly(N, b, t)
  let Z (t : ℝ) := riemannZeta (criticalLinePoint t)
  let W (t : ℝ) := ‖Complex.Gamma (criticalLineGammaArgument t)‖ * Real.exp ((Real.pi / 4 - 1 / (4 * T)) * t)
  have hP : Continuous P := continuous_finsetSum _ fun k hk ↦
    continuous_const.mul (continuous_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp hk).1)
  have hZ : Continuous Z := continuous_riemannZeta_criticalLine
  have hW : Continuous W := by
    apply Continuous.mul _ (by fun_prop)
    apply Continuous.norm
    apply continuous_iff_continuousAt.mpr
    intro t
    apply ContinuousAt.comp (g := Complex.Gamma) (f := criticalLineGammaArgument)
    · apply Complex.continuousAt_Gamma
      intro n he
      have H := congrArg Complex.re he
      rw [criticalLineGammaArgument_re] at H
      norm_num at H
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · unfold criticalLineGammaArgument
      fun_prop
  let U := ∫ t in T..2 * T, Z t * P t ^ 2
  have herror : ‖U - (T : ℂ)‖ ≤ T / 2 := by
    refine (hm T hT N b hN hb₁ hb).trans ?_
    calc C * N * Real.sqrt T ≤ C * (1 / (2 * C) * Real.sqrt T) * Real.sqrt T := by gcongr
         _ = T / 2 := by field_simp [hC.ne']; nlinarith [Real.sq_sqrt hTpos.le]
  have hbulk : T / 2 ≤ ∫ t in T..2 * T, ‖Z t * P t ^ 2‖ := by
    have hN := norm_sub_le_norm_sub_add_norm_sub (T : ℂ) U 0
    rw [sub_zero, sub_zero, norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTpos] at hN
    exact (by linarith : T / 2 ≤ ‖U‖).trans (intervalIntegral.norm_integral_le_integral_norm (by linarith))
  simp_rw [← spectralLineJet_mollifier_as_phases]
  change _ ≤ ∫ t in h..2 * T, W t * ‖P t‖ ^ 2 * |hardyZ t|
  calc
    c / 4 * (2 * T) ^ (3 / 4 : ℝ) = (c * (2 * T) ^ (-(1 / 4) : ℝ)) * (T / 2) := by
      rw [show (3 / 4 : ℝ) = -(1 / 4) + 1 by norm_num, Real.rpow_add_one h2T.ne']
      ring
    _ ≤ (c * (2 * T) ^ (-(1 / 4) : ℝ)) * ∫ t in T..2 * T, ‖Z t * P t ^ 2‖ :=
      mul_le_mul_of_nonneg_left hbulk (by positivity)
    _ = ∫ t in T..2 * T, (c * (2 * T) ^ (-(1 / 4) : ℝ)) * ‖Z t * P t ^ 2‖ :=
      (intervalIntegral.integral_const_mul ..).symm
    _ ≤ ∫ t in T..2 * T, W t * ‖P t‖ ^ 2 * |hardyZ t| := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((continuous_const.mul (hZ.mul (hP.pow 2)).norm).intervalIntegrable ..)
        (((hW.mul (hP.norm.pow 2)).mul continuous_hardyZ.abs).intervalIntegrable ..)
      intro t ht
      change (c * (2 * T) ^ (-(1 / 4) : ℝ)) * ‖Z t * P t ^ 2‖ ≤ W t * ‖P t‖ ^ 2 * |hardyZ t|
      rw [norm_mul, norm_pow, abs_hardyZ]
      change _ ≤ W t * ‖P t‖ ^ 2 * ‖Z t‖
      calc _ ≤ W t * (‖Z t‖ * ‖P t‖ ^ 2) := mul_le_mul_of_nonneg_right
             (hg T hT₂ t ht) (by positivity)
           _ = _ := by ring
    _ ≤ _ := intervalIntegral.integral_mono_interval hh (by linarith) le_rfl
      (Filter.Eventually.of_forall (fun t ↦ by dsimp [W]; positivity))
      (((hW.mul (hP.norm.pow 2)).mul continuous_hardyZ.abs).intervalIntegrable ..)

end RiemannMasullo
