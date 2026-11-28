module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.CauchyKernelBand
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Pairing the band-limited part of `q / (x - p)` with an exponential

For `u` supported in `[-Y, Y]` write `bandEval u w = ∫ u σ * exp (-2πi w σ)`, the value at `w`
of the transform `q` of `u`. Dividing `q` by `x - p` is, on the frequency side, convolution with
the one-sided exponential. The transform of the part of that convolution carried by the band
`(-Y, Y]`, evaluated at `z`, is

`(q p * exp (2πi (p - z) Y) - q z) / (2πi (p - z))`.

This is the Paley–Wiener projection of `q / (x - p)` evaluated at `z`: the value `q z / (x - p)`
at `x = z`, corrected by the single number `q p`.
-/

open MeasureTheory Complex Set Function
open scoped Real

@[expose] public noncomputable section

namespace RiemannMasullo

variable {u : ℝ → ℂ} {Y : ℝ}

/-- The transform of `u` at the complex point `w`. -/
def bandEval (u : ℝ → ℂ) (w : ℂ) : ℂ := ∫ σ, u σ * cexp (-(2 * π * I * w * σ))

/-- For `u` integrable and supported in `[-Y, Y]`, the integrand of `bandEval u w` is
integrable, for every complex `w`. -/
theorem integrable_mul_cexp_of_support (hu : Integrable u)
    (hsupp : ∀ σ, σ ∉ Icc (-Y) Y → u σ = 0) (w : ℂ) :
    Integrable fun σ : ℝ ↦ u σ * cexp (-(2 * π * I * w * σ)) := by
  refine (hu.norm.const_mul (Real.exp (2 * π * (|w.im| * |Y|)))).mono'
    (hu.aestronglyMeasurable.mul
      (by fun_prop : Continuous fun σ : ℝ ↦ cexp (-(2 * π * I * w * σ))).aestronglyMeasurable)
    (.of_forall fun σ ↦ ?_)
  by_cases hσ : σ ∈ Icc (-Y) Y
  · have hre : (-(2 * π * I * w * σ)).re = 2 * π * (w.im * σ) := by
      simp
      ring
    have h1 : w.im * σ ≤ |w.im| * |Y| := by
      have h2 : |σ| ≤ |Y| := (abs_le.mpr ⟨hσ.1, hσ.2⟩).trans (le_abs_self Y)
      calc w.im * σ ≤ |w.im * σ| := le_abs_self _
        _ = |w.im| * |σ| := abs_mul _ _
        _ ≤ |w.im| * |Y| := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    rw [norm_mul, Complex.norm_exp, hre, mul_comm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have := Real.pi_pos
    nlinarith
  · simp [hsupp σ hσ]

/-- The transform at `z` of the band part of the convolution of `u` with the one-sided
exponential of parameter `p`. -/
theorem integral_Ioc_convolution_indicator_Ioi_cexp (hu : Integrable u)
    (hsupp : ∀ σ, σ ∉ Icc (-Y) Y → u σ = 0) {p z : ℂ} (hp : 0 ≤ p.im) (hpz : p ≠ z) :
    ∫ τ in Ioc (-Y) Y,
        (∫ σ, u σ * indicator (Ioi (0 : ℝ)) (fun t : ℝ ↦ cexp (2 * π * I * p * t)) (τ - σ)) *
          cexp (-(2 * π * I * z * τ)) =
      (bandEval u p * cexp (2 * π * I * (p - z) * Y) - bandEval u z) /
        (2 * π * I * (p - z)) := by
  set E : ℝ → ℂ := indicator (Ioi (0 : ℝ)) fun t : ℝ ↦ cexp (2 * π * I * p * t) with hE
  set K : ℂ := cexp (2 * π * I * (p - z) * Y) with hK
  have hD : 2 * π * I * (p - z) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero)
      (sub_ne_zero.mpr hpz)
  have hEm : Measurable E :=
    (by fun_prop : Measurable fun t : ℝ ↦ cexp (2 * π * I * p * t)).indicator measurableSet_Ioi
  have hEn (t : ℝ) : ‖E t‖ ≤ 1 := by
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [hE, indicator_of_mem ht, Complex.norm_exp]
      have hre : (2 * π * I * p * t).re = -(2 * π * (p.im * t)) := by
        simp
        ring
      rw [hre]
      refine Real.exp_le_one_iff.mpr ?_
      have := Real.pi_pos
      have := mul_nonneg hp (le_of_lt ht)
      nlinarith
    · rw [hE, indicator_of_notMem ht, norm_zero]
      exact zero_le_one
  -- the inner integral in `τ`, for fixed `σ`
  have hin (σ : ℝ) : ∫ τ in Ioc (-Y) Y, u σ * E (τ - σ) * cexp (-(2 * π * I * z * τ)) =
      u σ * cexp (-(2 * π * I * p * σ)) * ((K - cexp (2 * π * I * (p - z) * σ)) /
        (2 * π * I * (p - z))) := by
    by_cases hσ : σ ∈ Icc (-Y) Y
    · have h1 (τ : ℝ) : u σ * E (τ - σ) * cexp (-(2 * π * I * z * τ)) =
          indicator (Ioi σ) (fun τ : ℝ ↦ u σ * cexp (-(2 * π * I * p * σ)) *
            cexp (2 * π * I * (p - z) * τ)) τ := by
        by_cases hτ : τ ∈ Ioi σ
        · have hpos : τ - σ ∈ Ioi (0 : ℝ) := sub_pos.mpr hτ
          rw [hE, indicator_of_mem hpos, indicator_of_mem hτ, mul_assoc (u σ) (cexp _) (cexp _),
            mul_assoc (u σ) (cexp _) (cexp _), ← Complex.exp_add, ← Complex.exp_add]
          congr 2
          push_cast
          ring
        · have hneg : τ - σ ∉ Ioi (0 : ℝ) := by
            simp only [mem_Ioi, not_lt, sub_nonpos]
            exact not_lt.mp hτ
          rw [hE, indicator_of_notMem hneg, indicator_of_notMem hτ, mul_zero, zero_mul]
      have hset : Ioc (-Y) Y ∩ Ioi σ = Ioc σ Y := by
        ext τ
        simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
        exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨lt_of_le_of_lt hσ.1 h.1, h.2⟩, h.1⟩⟩
      simp_rw [h1]
      rw [setIntegral_indicator measurableSet_Ioi, hset, ← intervalIntegral.integral_of_le hσ.2,
        intervalIntegral.integral_const_mul, integral_exp_mul_complex hD]
    · rw [hsupp σ hσ]
      simp
  -- Fubini
  have hF : Integrable (uncurry fun (τ σ : ℝ) ↦ u σ * E (τ - σ) * cexp (-(2 * π * I * z * τ)))
      ((volume.restrict (Ioc (-Y) Y)).prod volume) := by
    have hb : Integrable (fun q : ℝ × ℝ ↦ Real.exp (2 * π * (|z.im| * |q.1|)) * ‖u q.2‖)
        ((volume.restrict (Ioc (-Y) Y)).prod volume) :=
      Integrable.mul_prod
        ((by fun_prop : Continuous fun τ : ℝ ↦ Real.exp (2 * π * (|z.im| * |τ|))).integrableOn_Ioc)
        hu.norm
    refine hb.mono' ((hu.aestronglyMeasurable.comp_snd.mul
      (hEm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable).mul
      (by fun_prop : Continuous fun q : ℝ × ℝ ↦
        cexp (-(2 * π * I * z * q.1))).aestronglyMeasurable) (.of_forall fun q ↦ ?_)
    have hre : (-(2 * π * I * z * q.1)).re = 2 * π * (z.im * q.1) := by
      simp
      ring
    have h1 : z.im * q.1 ≤ |z.im| * |q.1| := (le_abs_self _).trans (abs_mul _ _).le
    have h2 : ‖cexp (-(2 * π * I * z * q.1))‖ ≤ Real.exp (2 * π * (|z.im| * |q.1|)) := by
      rw [Complex.norm_exp, hre]
      refine Real.exp_le_exp.mpr ?_
      have := Real.pi_pos
      nlinarith
    simp only [uncurry]
    rw [norm_mul, norm_mul, mul_comm]
    calc ‖cexp (-(2 * π * I * z * q.1))‖ * (‖u q.2‖ * ‖E (q.1 - q.2)‖)
        ≤ Real.exp (2 * π * (|z.im| * |q.1|)) * (‖u q.2‖ * 1) := by
          gcongr
          exact hEn _
      _ = Real.exp (2 * π * (|z.im| * |q.1|)) * ‖u q.2‖ := by rw [mul_one]
  have hx (σ : ℝ) : cexp (-(2 * π * I * p * σ)) * cexp (2 * π * I * (p - z) * σ) =
      cexp (-(2 * π * I * z * σ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have he (σ : ℝ) : u σ * cexp (-(2 * π * I * p * σ)) * ((K - cexp (2 * π * I * (p - z) * σ)) /
      (2 * π * I * (p - z))) =
      K / (2 * π * I * (p - z)) * (u σ * cexp (-(2 * π * I * p * σ))) -
        (2 * π * I * (p - z))⁻¹ * (u σ * cexp (-(2 * π * I * z * σ))) := by
    rw [← hx σ]
    ring
  calc ∫ τ in Ioc (-Y) Y, (∫ σ, u σ * E (τ - σ)) * cexp (-(2 * π * I * z * τ))
      = ∫ τ in Ioc (-Y) Y, ∫ σ, u σ * E (τ - σ) * cexp (-(2 * π * I * z * τ)) := by
        simp_rw [← integral_mul_const]
    _ = ∫ σ, ∫ τ in Ioc (-Y) Y, u σ * E (τ - σ) * cexp (-(2 * π * I * z * τ)) :=
        integral_integral_swap hF
    _ = ∫ σ, (K / (2 * π * I * (p - z)) * (u σ * cexp (-(2 * π * I * p * σ))) -
          (2 * π * I * (p - z))⁻¹ * (u σ * cexp (-(2 * π * I * z * σ)))) := by
        simp_rw [hin, he]
    _ = (bandEval u p * K - bandEval u z) / (2 * π * I * (p - z)) := by
        rw [integral_sub ((integrable_mul_cexp_of_support hu hsupp p).const_mul _)
          ((integrable_mul_cexp_of_support hu hsupp z).const_mul _), integral_const_mul,
          integral_const_mul]
        unfold bandEval
        field_simp

end RiemannMasullo
