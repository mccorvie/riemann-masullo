module

public import RiemannMasullo.Ch01_Introduction.Sec4_PoissonCertificate
public import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.HorizontalLogNorm
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

/-! # An arithmetic upper bound for the rational Poisson mass at ordinate fourteen

The logarithmic derivative of ζ is bounded on `Re s = 2` by separating the
von Mangoldt terms through ten from a telescoping logarithmic tail. The
horizontal Γ secants and digamma recurrence bound the archimedean contribution
at fourteen. These two explicit estimates give the upper bound `31 / 25`.
-/

@[expose] public noncomputable section

namespace RiemannMasullo.HeckePoisson

open ArithmeticFunction Finset
open scoped BigOperators LSeries.notation

private def lambdaSquareTerm (n : ℕ) : ℝ := Λ n / (n : ℝ)^2
private def tailPotential (n : ℕ) : ℝ := (Real.log (n : ℝ) + 1) / n

private theorem log_step {x : ℝ} (hx : 10 ≤ x) :
    Real.log (x + 1) / (x + 1)^2 + (Real.log (x + 1) + 1) / (x + 1) ≤
      (Real.log x + 1) / x := by
  have hx0 : 0 < x := by linarith
  have hy : 0 < x + 1 := by linarith
  have hex : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_three]
  have hanti := Real.log_div_self_antitoneOn (show x ∈ Set.Ici (Real.exp 1) from hex)
    (show x + 1 ∈ Set.Ici (Real.exp 1) by change _ ≤ _; linarith) (by linarith : x ≤ x + 1)
  have hlog : (Real.log (x + 1) - Real.log x) * x ≤ 1 := by
    apply (le_div_iff₀ hx0).mp
    have h := Real.log_le_sub_one_of_pos (div_pos hy hx0)
    rw [Real.log_div hy.ne' hx0.ne'] at h
    convert h using 1
    field_simp
    ring
  have hfirst : Real.log (x + 1) / (x + 1)^2 ≤ (Real.log x / x) / (x + 1) := by
    calc
      _ = (Real.log (x + 1) / (x + 1)) / (x + 1) := by rw [div_div, sq]
      _ ≤ _ := div_le_div_of_nonneg_right hanti hy.le
  apply (add_le_add hfirst (le_refl _)).trans
  field_simp
  nlinarith [hlog]

private theorem lambdaSquareTerm_step {n : ℕ} (hn : 10 ≤ n) :
    lambdaSquareTerm (n+1) + tailPotential (n+1) ≤ tailPotential n := by
  have hlog := log_step (x := (n : ℝ)) (by exact_mod_cast hn)
  have hΛ : Λ (n+1) ≤ Real.log (↑(n+1 : ℕ) : ℝ) := vonMangoldt_le_log
  unfold lambdaSquareTerm tailPotential
  push_cast at hΛ ⊢
  exact (add_le_add (div_le_div_of_nonneg_right hΛ (sq_nonneg _)) (le_refl _)).trans hlog

private theorem lambdaSquareTerm_tail : (∑' n : ℕ, lambdaSquareTerm (n+11)) ≤ tailPotential 10 := by
  have bound (N : ℕ) : (∑ n ∈ range N, lambdaSquareTerm (n+11)) + tailPotential (N+10) ≤
      tailPotential 10 := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      have hn := lambdaSquareTerm_step (n := N+10) (by omega)
      change lambdaSquareTerm (N+11) + tailPotential (N+11) ≤ tailPotential (N+10) at hn
      change _ + tailPotential (N+11) ≤ _
      linarith
  refine Real.tsum_le_of_sum_range_le (f := fun n : ℕ ↦ lambdaSquareTerm (n+11))
    (fun _ ↦ div_nonneg vonMangoldt_nonneg (sq_nonneg _)) ?_
  intro N
  have hp : 0 ≤ tailPotential (N+10) :=
    div_nonneg (by linarith [Real.log_natCast_nonneg (N+10)]) (Nat.cast_nonneg _)
  linarith [bound N]

private theorem lambdaSquareTerm_finite_bound :
    (∑ n ∈ range 11, lambdaSquareTerm n) + tailPotential 10 ≤ 81/100 := by
  have h₂ : Λ 2 = Real.log 2 := vonMangoldt_apply_prime (by decide)
  have h₃ : Λ 3 = Real.log 3 := vonMangoldt_apply_prime (by decide)
  have h₅ : Λ 5 = Real.log 5 := vonMangoldt_apply_prime (by decide)
  have h₇ : Λ 7 = Real.log 7 := vonMangoldt_apply_prime (by decide)
  have h₄ : Λ 4 = Real.log 2 := by
    rw [show (4 : ℕ) = 2^2 by decide, vonMangoldt_apply_pow (by decide), h₂]
  have h₈ : Λ 8 = Real.log 2 := by
    rw [show (8 : ℕ) = 2^3 by decide, vonMangoldt_apply_pow (by decide), h₂]
  have h₉ : Λ 9 = Real.log 3 := by
    rw [show (9 : ℕ) = 3^2 by decide, vonMangoldt_apply_pow (by decide), h₃]
  have h₆ : Λ 6 = 0 := vonMangoldt_eq_zero_iff.mpr (by decide)
  have h₁₀ : Λ 10 = 0 := vonMangoldt_eq_zero_iff.mpr (by decide)
  have hl₃ := Real.log_le_log (show 0 < (3 : ℝ)^5 by norm_num) (by norm_num : (3 : ℝ)^5 ≤ 2^8)
  have hl₅ := Real.log_le_log (show 0 < (5 : ℝ)^3 by norm_num) (by norm_num : (5 : ℝ)^3 ≤ 2^7)
  have hl₇ := Real.log_le_log (show 0 < (7 : ℝ) by norm_num) (by norm_num : (7 : ℝ) ≤ 2^3)
  rw [Real.log_pow, Real.log_pow] at hl₃ hl₅
  rw [Real.log_pow] at hl₇
  have hl₁₀ : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
    norm_num
  norm_num [Finset.sum_range_succ, lambdaSquareTerm, tailPotential, h₂, h₃, h₄, h₅, h₆, h₇,
    h₈, h₉, h₁₀, hl₁₀] at hl₃ hl₅ hl₇ ⊢
  linarith [Real.log_two_lt_d9]

/-- An explicit von Mangoldt majorant for the logarithmic derivative of the
Riemann zeta function on the full line of real part two. -/
theorem norm_logDeriv_riemannZeta_re_two_le {s : ℂ} (hs : s.re = 2) :
    ‖logDeriv riemannZeta s‖ ≤ (81/100 : ℝ) := by
  have hs1 : 1 < s.re := by linarith
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hs1
  have hnorm (n : ℕ) : ‖LSeries.term (fun k : ℕ ↦ (Λ k : ℂ)) s n‖ = lambdaSquareTerm n := by
    rw [LSeries.norm_term_eq, hs]
    by_cases hn : n = 0
    · simp [hn, lambdaSquareTerm]
    · simp [hn, lambdaSquareTerm, Real.norm_of_nonneg vonMangoldt_nonneg]
  have hsummable : Summable lambdaSquareTerm := by simpa only [hnorm] using hsum.norm
  have hid := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1
  calc
    ‖logDeriv riemannZeta s‖ = ‖LSeries (fun n : ℕ ↦ (Λ n : ℂ)) s‖ := by
      rw [hid, neg_div, norm_neg, logDeriv_apply]
    _ ≤ ∑' n : ℕ, lambdaSquareTerm n := by
      simpa only [LSeries, hnorm] using norm_tsum_le_tsum_norm hsum.norm
    _ = (∑ n ∈ range 11, lambdaSquareTerm n) + ∑' n : ℕ, lambdaSquareTerm (n+11) :=
      (hsummable.sum_add_tsum_nat_add 11).symm
    _ ≤ 81/100 := (add_le_add (le_refl _) lambdaSquareTerm_tail).trans lambdaSquareTerm_finite_bound

end RiemannMasullo.HeckePoisson

namespace RiemannMasullo.HeckePoisson

open Complex Filter NumberField Set
open scoped Topology

local notation "χ₀" => (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ))
local notation "s₁₄" => (2 + 14 * I : ℂ)
local notation "w₇" => (1 + 7 * I : ℂ)

/-- On the half-plane of absolute convergence, the rational principal
completion consists of the real gamma factor and the Riemann zeta function. -/
theorem rational_principal_completed_eq {s : ℂ} (hs : 1 < s.re) :
    continuedCompletedHeckeL χ₀ s = Complex.Gammaℝ s * riemannZeta s := by
  have hr : InfinitePlace.nrRealPlaces ℚ = 1 :=
    InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ)
  have hc : InfinitePlace.nrComplexPlaces ℚ = 0 :=
    InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ)
  rw [(continuedCompletedHeckeL_spec _).2 ⟨s, hs⟩, completedHeckeL_one_eq_dedekindZeta,
    hr, hc, pow_one, pow_zero, mul_one, dedekindZeta_rat_eq_riemannZeta hs]

/-- The logarithmic derivative of the real gamma factor, including the power of π. -/
private theorem gammaR_differentiable_logDeriv {s : ℂ} (h : 0 < (s / 2).re) :
    DifferentiableAt ℂ Complex.Gammaℝ s ∧
      logDeriv Complex.Gammaℝ s = (Complex.digamma (s / 2) - (Real.log Real.pi : ℂ)) / 2 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpower := ((hasDerivAt_id s).neg.div_const 2).const_cpow (Or.inl hπ)
  have hgamma := (Complex.hasDerivAt_Gamma_of_re_pos h).differentiableAt.hasDerivAt.comp s
    ((hasDerivAt_id s).div_const 2)
  have hp : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)
  have hg := Complex.Gamma_ne_zero_of_re_pos h
  have hd : HasDerivAt Complex.Gammaℝ _ s := hpower.mul hgamma
  refine ⟨hd.differentiableAt, ?_⟩
  rw [logDeriv_apply, hd.deriv, Complex.Gammaℝ_def, Complex.digamma_def, logDeriv_apply,
    ← Complex.ofReal_log Real.pi_pos.le]
  dsimp
  field_simp [hp, hg]
  ring

/-- Split the logarithmic derivative of the completed principal rational character. -/
theorem rational_principal_completed_logDeriv {s : ℂ} (hs : 1 < s.re) :
    logDeriv (continuedCompletedHeckeL χ₀) s = logDeriv riemannZeta s +
      (Complex.digamma (s / 2) - (Real.log Real.pi : ℂ)) / 2 := by
  have he : continuedCompletedHeckeL χ₀ =ᶠ[𝓝 s] fun z ↦ Complex.Gammaℝ z * riemannZeta z := by
    filter_upwards [Complex.continuous_re.continuousAt (Ioi_mem_nhds hs)] with z hz
    exact rational_principal_completed_eq hz
  have hz : s ≠ 1 := by rintro rfl; norm_num at hs
  have hg := gammaR_differentiable_logDeriv (s := s) (by
    rw [Complex.div_ofNat_re]
    linarith)
  rw [(logDeriv_congr_nhds he).eq_of_nhds,
    logDeriv_fun_mul (f := Complex.Gammaℝ) (g := riemannZeta) s
      (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)) (riemannZeta_ne_zero_of_one_lt_re hs)
      hg.1 (differentiableAt_riemannZeta hz), hg.2, add_comm]

/-- Arithmetic form of the mass at the center `2 + 14i` for the principal rational character. -/
theorem rational_normalizedLogDerivative_fourteen :
    normalizedLogDerivative χ₀ 14 = (logDeriv riemannZeta s₁₄).re +
      (1 / s₁₄ + 1 / (s₁₄ - 1)).re +
      ((Complex.digamma w₇).re - Real.log Real.pi) / 2 := by
  have h := rational_principal_completed_logDeriv (s := s₁₄) (by norm_num)
  rw [show s₁₄ / 2 = w₇ by ring] at h
  simp [normalizedLogDerivative, heckeLogDiscriminantConductor_one, h,
    Complex.add_re, Complex.div_ofNat_re, Complex.sub_re]
  ring

/-- Sum of the two rational polar corrections at the first positive center. -/
private theorem firstCell_poles :
    (1 / s₁₄ + 1 / (s₁₄ - 1)).re = 297 / 19700 := by
  norm_num [one_div, Complex.inv_re, Complex.normSq_apply, Complex.add_re,
    Complex.sub_re, Complex.add_im, Complex.sub_im]

/-- Shift the digamma from `1+7i` to `24+7i`, whose modulus is exactly 25.
The twenty-three return terms have real part at least 5/4 in total. -/
private theorem firstCell_digamma_upper :
    (Complex.digamma w₇).re ≤ Real.log 25 - 5 / 4 := by
  have hh := (gammaLine_digamma_secants 7 24 (by norm_num)).2
  have hn : ‖gammaLine 7 24‖ = 25 := by
    have hsq : ‖gammaLine 7 24‖^2 = 625 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      norm_num [gammaLine, Complex.add_re, Complex.add_im]
    nlinarith [norm_nonneg (gammaLine 7 24)]
  have he : w₇ + (23 : ℂ) = gammaLine 7 24 := by norm_num [gammaLine]; ring
  have hc := congrArg Complex.re (Complex.digamma_apply_add_nat (s := w₇) (fun m h ↦ by
    have := congrArg Complex.im h
    norm_num at this) 23)
  norm_num only [Nat.cast_ofNat] at hc
  rw [he, Complex.add_re, Complex.re_sum] at hc
  have hs : (5 : ℝ)/4 ≤ ∑ j ∈ Finset.range 23, ((w₇ + (j : ℂ))⁻¹).re := by
    norm_num [Finset.sum_range_succ, Complex.inv_re, Complex.normSq_apply, Complex.add_re,
      Complex.add_im]
  rw [hn] at hh
  linarith

/-- Fully rational bound for the poles and the real archimedean factor of
the principal zeta function at `2+14i`. -/
theorem firstCell_arch_polar_upper :
    (1 / s₁₄ + 1 / (s₁₄ - 1)).re +
      ((Complex.digamma w₇).re - Real.log Real.pi) / 2 ≤ 43 / 100 := by
  have hratio : (25 : ℝ) / Real.pi ≤ 8 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_gt_d2]
  have hlog := Real.log_le_log (by positivity : 0 < (25 : ℝ) / Real.pi) hratio
  rw [Real.log_div (by norm_num) Real.pi_ne_zero, show (8 : ℝ) = 2^3 by norm_num,
    Real.log_pow] at hlog
  norm_num at hlog
  rw [firstCell_poles]
  linarith [Real.log_two_lt_d9, firstCell_digamma_upper]

/-- The full pole-cleared rational arithmetic scalar at `2 + 14i` is at most `31/25`. -/
theorem rational_normalizedLogDerivative_fourteen_le : normalizedLogDerivative χ₀ 14 ≤ 31 / 25 := by
  have hfin := (Complex.re_le_norm (logDeriv riemannZeta s₁₄)).trans
    (norm_logDeriv_riemannZeta_re_two_le (s := s₁₄) (by norm_num))
  rw [rational_normalizedLogDerivative_fourteen]
  linarith [firstCell_arch_polar_upper]

end RiemannMasullo.HeckePoisson
