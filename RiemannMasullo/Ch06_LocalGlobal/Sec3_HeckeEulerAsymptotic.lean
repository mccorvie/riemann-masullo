module

public import RiemannMasullo.Ch06_LocalGlobal.Sec3
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.HeckeLFunction
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Injectivity
public import Mathlib.Analysis.Calculus.LogDeriv

/-! # The finite Hecke logarithmic derivative far to the right

At an expanding real abscissa the second Dirichlet coefficient gives the first possible
nonconstant term. In particular the difference between the completed and archimedean
logarithmic derivatives is negligible even after multiplying by the abscissa.
-/

public noncomputable section

open Filter NumberField
open scoped Topology

namespace RiemannMasullo.HeckePoisson

variable {F : Type*} [Field F] [NumberField F]

private theorem first_coefficient (ψ : HeckeCharacter (𝓞 F) F) : ψ.LFunction 1 = 1 := by
  classical
  obtain ⟨S, hS⟩ := (heckeLocalEulerFactor_eventually_prod_eq ψ 1).exists
  rw [← hS]
  clear hS
  induction S using Finset.induction_on with
  | empty => simp
  | insert v S hv ih =>
    rw [Finset.prod_insert hv, ArithmeticFunction.mul_apply_one, ih, mul_one]
    simp [HeckeCharacter.localEulerFactor, HeckeCharacter.localPowerSeries,
      ArithmeticFunction.ofPowerSeries_apply_one, PowerSeries.constantCoeff_invOfUnit]

/-- The leading exponential term of the finite logarithmic derivative on the real axis
is the second Hecke coefficient times the negative logarithm of two. -/
theorem tendsto_two_cpow_mul_finiteHecke_logDeriv (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    Tendsto (fun σ : ℝ ↦ (2 : ℂ) ^ (σ : ℂ) * logDeriv (ideleClassNormTwist χ 0).LSeries σ)
      atTop (𝓝 (-(Complex.log 2 * (ideleClassNormTwist χ 0).LFunction 2))) := by
  let ψ := ideleClassNormTwist χ 0
  let c : ℕ → ℂ := ψ.LFunction
  have ha : LSeries.abscissaOfAbsConv c ≤ (2 : ℝ) :=
    (finiteHeckeL_seriesSummable χ ⟨2, by change 1 < (2 : ℂ).re; norm_num⟩).abscissaOfAbsConv_le
  have ht : LSeries.abscissaOfAbsConv c < ⊤ := ha.trans_lt (EReal.coe_lt_top _)
  have hden : Tendsto (fun σ : ℝ ↦ LSeries c σ) atTop (𝓝 1) := by
    simpa only [c, first_coefficient] using LSeries.tendsto_atTop ht
  have hz (m : ℕ) (hm : m ≤ 1) : LSeries.logMul c m = 0 := by
    interval_cases m <;> simp [LSeries.logMul]
  have hnum : Tendsto (fun σ : ℝ ↦ (2 : ℂ) ^ (σ : ℂ) * LSeries (LSeries.logMul c) σ)
      atTop (𝓝 (Complex.log 2 * c 2)) := by
    simpa only [Nat.cast_one, one_add_one_eq_two, LSeries.logMul, Nat.cast_ofNat] using
      LSeries.tendsto_cpow_mul_atTop hz (by simpa only [LSeries.abscissaOfAbsConv_logMul] using ht)
  have h := hnum.neg.div hden one_ne_zero
  rw [div_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with σ hσ
  have hs : LSeries.abscissaOfAbsConv c < ((σ : ℂ).re : EReal) :=
    ha.trans_lt (by exact_mod_cast hσ)
  change -(_ * _) / _ = _ * logDeriv (LSeries c) _
  rw [logDeriv_apply, LSeries_deriv hs, mul_div_assoc']
  ring

/-- After the half-unit shift used for the Poisson width, the scaled finite Euler
term tends to zero. -/
theorem tendsto_mul_re_finiteHecke_logDeriv (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    Tendsto (fun a : ℝ ↦ a * (logDeriv (ideleClassNormTwist χ 0).LSeries ((a + 1 / 2 : ℝ) : ℂ)).re)
      atTop (𝓝 0) := by
  have hsmall : Tendsto (fun a : ℝ ↦ a / (2 : ℝ) ^ (a + 1 / 2)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (Real.log 2)
      (Real.log_pos (by norm_num))).mul_const (Real.exp (-(Real.log 2 / 2)))
    rw [zero_mul] at h
    apply h.congr'
    filter_upwards with a
    rw [Real.rpow_one, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), div_eq_mul_inv a _,
      ← Real.exp_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hshift : Tendsto (fun a : ℝ ↦ a + 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 / 2 : ℝ) tendsto_id
  have he := (tendsto_two_cpow_mul_finiteHecke_logDeriv χ).comp hshift
  have h := hsmall.mul (Complex.continuous_re.continuousAt.tendsto.comp he)
  rw [zero_mul] at h
  apply h.congr'
  filter_upwards with a
  dsimp only [Function.comp_apply]
  have hpow (x : ℝ) : (2 : ℂ) ^ (x : ℂ) = ((2 : ℝ) ^ x : ℝ) := by
    simpa only [Complex.ofReal_ofNat] using (Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2) x).symm
  rw [hpow, Complex.re_ofReal_mul]
  have hne : (2 : ℝ) ^ (a + 1 / 2) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  field_simp

/-- The difference between the real logarithmic derivatives of the actual completed
continuation and its archimedean factor tends to zero after multiplication by the width. -/
theorem tendsto_mul_re_completed_sub_gamma_logDeriv (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    Tendsto (fun a : ℝ ↦ a * ((logDeriv (continuedCompletedHeckeL χ) ((a + 1 / 2 : ℝ) : ℂ)).re -
      (logDeriv (heckeGammaFactor χ) ((a + 1 / 2 : ℝ) : ℂ)).re)) atTop (𝓝 0) := by
  apply (tendsto_mul_re_finiteHecke_logDeriv χ).congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with a ha
  let s : ℂ := (a + 1 / 2 : ℝ)
  have hs : 1 < s.re := by dsimp [s]; linarith
  have hEq : continuedCompletedHeckeL χ =ᶠ[𝓝 s]
      fun z ↦ heckeGammaFactor χ z * (ideleClassNormTwist χ 0).LSeries z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact (continuedCompletedHeckeL_spec χ).2 ⟨z, hz⟩
  have hσ : LSeries.abscissaOfAbsConv (ideleClassNormTwist χ 0).LFunction < (s.re : EReal) := by
    apply (finiteHeckeL_seriesSummable χ ⟨2, by change 1 < (2 : ℂ).re; norm_num⟩).abscissaOfAbsConv_le.trans_lt
    apply EReal.coe_lt_coe_iff.mpr
    dsimp [s]
    linarith
  have h := (logDeriv_congr_nhds hEq).eq_of_nhds.trans (logDeriv_fun_mul s
    (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hs))
    (finiteHeckeL_ne_zero_of_one_lt_re χ ⟨s, hs⟩)
    (differentiableAt_heckeGammaFactor_of_re_pos χ (zero_lt_one.trans hs))
    (LSeries_hasDerivAt hσ).differentiableAt)
  change _ = a * ((logDeriv (continuedCompletedHeckeL χ) s).re - _)
  rw [h, Complex.add_re, add_sub_cancel_left]

end RiemannMasullo.HeckePoisson
