module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The normalized one-dimensional Bessel potential kernel

For `θ > 1/2`, the positive heat integral defines the continuous Green kernel for the
fractional Sobolev weight `(1 + ξ²)^θ`, normalized to have value one at the origin.
We prove its exact Fourier multiplier and the global envelope
`2^(θ - 1/2) * exp (-|x|/2)` directly, including absolute integrability for Fubini.

The heat representation and Fourier multiplier are classical: Aronszajn–Smith,
*Theory of Bessel potentials I*, Ann. Inst. Fourier 11 (1961), §4, pp. 416–417.
The estimates here are inputs for the fractional-order geometric-block argument in #7406.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter Real
open scoped Topology
namespace RiemannMasullo

/-- The one-dimensional Bessel potential kernel, normalized to equal one at the origin.
The integral is the heat-kernel representation, with its constant canceled in the ratio. -/
def normalizedBesselKernel (θ x : ℝ) : ℝ :=
  (∫ u : ℝ in Ioi 0, u ^ (θ - 3 / 2) * Real.exp (-u - x ^ 2 / (4 * u))) /
    Real.Gamma (θ - 1 / 2)

private theorem bessel_base_integrable {θ b : ℝ} (hθ : 1 / 2 < θ) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ ↦ u ^ (θ - 3 / 2) * Real.exp (-(b * u))) (Ioi 0) := by
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := θ - 3 / 2) (p := 1)
      (by linarith) zero_lt_one hb)

private theorem bessel_integrand_nonneg {θ u : ℝ} (hu : 0 ≤ u) (x : ℝ) :
    0 ≤ u ^ (θ - 3 / 2) * Real.exp (-u - x ^ 2 / (4 * u)) :=
  mul_nonneg (Real.rpow_nonneg hu _) (Real.exp_pos _).le

private theorem bessel_integrand_le {θ u : ℝ} (hu : 0 < u) (x : ℝ) :
    u ^ (θ - 3 / 2) * Real.exp (-u - x ^ 2 / (4 * u)) ≤
      u ^ (θ - 3 / 2) * Real.exp (-u) := by
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hu.le _)
  apply Real.exp_le_exp.mpr
  exact sub_le_self _ (by positivity)

/-- The heat integral defining the normalized Bessel kernel exists at every point. -/
theorem integrableOn_normalizedBesselKernel_integrand {θ : ℝ} (hθ : 1 / 2 < θ) (x : ℝ) :
    IntegrableOn (fun u : ℝ ↦ u ^ (θ - 3 / 2) * Real.exp (-u - x ^ 2 / (4 * u)))
      (Ioi 0) := by
  have hi : IntegrableOn (fun u : ℝ ↦ u ^ (θ - 3 / 2) * Real.exp (-u)) (Ioi 0) := by
    simpa only [one_mul] using bessel_base_integrable hθ zero_lt_one
  apply hi.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (bessel_integrand_nonneg hu.le x)]
  exact bessel_integrand_le hu x

/-- The normalized Bessel kernel is positive. -/
theorem normalizedBesselKernel_pos {θ : ℝ} (hθ : 1 / 2 < θ) (x : ℝ) :
    0 < normalizedBesselKernel θ x := by
  apply div_pos _ (Real.Gamma_pos_of_pos (by linarith))
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have he : (Function.support (fun u : ℝ ↦ u ^ (θ - 3 / 2) *
        Real.exp (-u - x ^ 2 / (4 * u)))) ∩ Ioi 0 = Ioi 0 := by
      rw [inter_eq_right]
      intro u hu
      exact mul_ne_zero (Real.rpow_pos_of_pos hu _).ne' (Real.exp_pos _).ne'
    rw [he, volume_Ioi]
    exact ENNReal.zero_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact bessel_integrand_nonneg hu.le x
  · exact integrableOn_normalizedBesselKernel_integrand hθ x

private theorem integral_bessel_base {θ b : ℝ} (hθ : 1 / 2 < θ) (hb : 0 < b) :
    (∫ u : ℝ in Ioi 0, u ^ (θ - 3 / 2) * Real.exp (-(b * u))) =
      (1 / b) ^ (θ - 1 / 2) * Real.Gamma (θ - 1 / 2) := by
  convert Real.integral_rpow_mul_exp_neg_mul_Ioi (show 0 < θ - 1 / 2 by linarith) hb using 1
  congr 1
  funext u
  congr 2
  ring

/-- The normalization is exact. -/
theorem normalizedBesselKernel_zero {θ : ℝ} (hθ : 1 / 2 < θ) :
    normalizedBesselKernel θ 0 = 1 := by
  unfold normalizedBesselKernel
  simp only [zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero]
  have h := integral_bessel_base hθ zero_lt_one
  simp only [one_mul, one_div_one, Real.one_rpow, one_mul] at h
  rw [h, div_self (Real.Gamma_pos_of_pos (by linarith)).ne']

/-- Positivity and Gaussian domination bound the normalized kernel by one. -/
theorem normalizedBesselKernel_le_one {θ : ℝ} (hθ : 1 / 2 < θ) (x : ℝ) :
    normalizedBesselKernel θ x ≤ 1 := by
  rw [← normalizedBesselKernel_zero hθ]
  apply div_le_div_of_nonneg_right _ (Real.Gamma_pos_of_pos (by linarith)).le
  apply integral_mono_ae (integrableOn_normalizedBesselKernel_integrand hθ x)
    (integrableOn_normalizedBesselKernel_integrand hθ 0)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simpa only [zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero] using bessel_integrand_le hu x

/-- The normalized Bessel kernel is even. -/
theorem normalizedBesselKernel_neg (θ x : ℝ) :
    normalizedBesselKernel θ (-x) = normalizedBesselKernel θ x := by
  simp only [normalizedBesselKernel, neg_sq]

/-- A uniform exponential envelope for the normalized Bessel kernel, with no asymptotic
or Bessel-function input. It follows directly from the positive heat integral. -/
theorem normalizedBesselKernel_le_exp {θ : ℝ} (hθ : 1 / 2 < θ) (x : ℝ) :
    normalizedBesselKernel θ x ≤ (2 : ℝ) ^ (θ - 1 / 2) * Real.exp (-|x| / 2) := by
  have hb (u : ℝ) (hu : 0 < u) :
      u ^ (θ - 3 / 2) * Real.exp (-u - x ^ 2 / (4 * u)) ≤
        Real.exp (-|x| / 2) * (u ^ (θ - 3 / 2) * Real.exp (-((1 / 2 : ℝ) * u))) := by
    have hd : |x| / 2 - u / 2 ≤ x ^ 2 / (4 * u) := by
      apply (le_div_iff₀ (by positivity : 0 < 4 * u)).mpr
      nlinarith [sq_nonneg (u - |x|), sq_nonneg u, sq_abs x]
    have he : -u - x ^ 2 / (4 * u) ≤ -|x| / 2 - u / 2 := by linarith
    calc
      _ ≤ u ^ (θ - 3 / 2) * Real.exp (-|x| / 2 - u / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (Real.rpow_nonneg hu.le _)
      _ = _ := by
        rw [show -|x| / 2 - u / 2 = -|x| / 2 + -((1 / 2 : ℝ) * u) by ring,
          Real.exp_add]
        ring
  have hi := (bessel_base_integrable hθ (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
    (Real.exp (-|x| / 2))
  have hle := integral_mono_ae (integrableOn_normalizedBesselKernel_integrand hθ x) hi
    ((ae_restrict_mem measurableSet_Ioi).mono fun u hu ↦ hb u hu)
  rw [integral_const_mul, integral_bessel_base hθ (by norm_num : (0 : ℝ) < 1 / 2)] at hle
  norm_num only [one_div_div] at hle
  unfold normalizedBesselKernel
  apply (div_le_iff₀ (Real.Gamma_pos_of_pos (by linarith))).mpr
  convert hle using 1
  ring

/-- Dominated convergence gives a continuous representative of the Bessel kernel. -/
theorem continuous_normalizedBesselKernel {θ : ℝ} (hθ : 1 / 2 < θ) :
    Continuous (normalizedBesselKernel θ) := by
  unfold normalizedBesselKernel
  apply Continuous.div_const
  apply continuous_of_dominated (bound := fun u : ℝ ↦ u ^ (θ - 3 / 2) * Real.exp (-u))
  · intro x
    fun_prop
  · intro x
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (bessel_integrand_nonneg hu.le x)]
    exact bessel_integrand_le hu x
  · simpa only [IntegrableOn, one_mul] using bessel_base_integrable hθ zero_lt_one
  · exact .of_forall fun u ↦ by fun_prop

/-- The normalized Bessel kernel is integrable on the real line. -/
theorem integrable_normalizedBesselKernel {θ : ℝ} (hθ : 1 / 2 < θ) :
    Integrable (normalizedBesselKernel θ) := by
  have hi := (integrable_exp_neg_mul_abs (c := 1 / 2) (by norm_num)).const_mul
    ((2 : ℝ) ^ (θ - 1 / 2))
  apply hi.mono' (continuous_normalizedBesselKernel hθ).aestronglyMeasurable
  exact .of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (normalizedBesselKernel_pos hθ x)]
    convert normalizedBesselKernel_le_exp hθ x using 1
    congr 2
    ring

private theorem integral_bessel_gaussian {u : ℝ} (hu : 0 < u) (ξ : ℝ) :
    (∫ x : ℝ, Complex.exp (Complex.I * (ξ : ℂ) * x) *
      (Real.exp (-(x ^ 2 / (4 * u))) : ℂ)) =
      (Real.sqrt (4 * Real.pi * u) : ℂ) * (Real.exp (-(u * ξ ^ 2)) : ℂ) := by
  let b : ℝ := (4 * u)⁻¹
  have hb : 0 < b := by dsimp [b]; positivity
  have h := fourierIntegral_gaussian (b := (b : ℂ)) (by simpa using hb) (ξ : ℂ)
  have he (x : ℝ) : (Real.exp (-(x ^ 2 / (4 * u))) : ℂ) =
      Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) := by
    rw [Complex.ofReal_exp]
    congr 1
    dsimp [b]
    push_cast
    ring
  simp_rw [he]
  rw [h]
  have hq : (Real.pi : ℂ) / b = ((4 * Real.pi * u : ℝ) : ℂ) := by
    dsimp [b]
    push_cast
    field_simp
  have hx : -(ξ : ℂ) ^ 2 / (4 * (b : ℂ)) = ((-(u * ξ ^ 2) : ℝ) : ℂ) := by
    have huc : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
    dsimp [b]
    push_cast
    field_simp [huc]
  rw [hq, hx, ← Complex.ofReal_exp]
  congr 1
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
  norm_num

private theorem integral_bessel_gaussian_real (u : ℝ) :
    (∫ x : ℝ, Real.exp (-(x ^ 2 / (4 * u)))) = Real.sqrt (4 * Real.pi * u) := by
  have he : (fun x : ℝ ↦ Real.exp (-(x ^ 2 / (4 * u)))) =
      fun x ↦ Real.exp (-(4 * u)⁻¹ * x ^ 2) := by funext x; congr 1; ring
  rw [he, integral_gaussian]
  congr 1
  field_simp

private theorem bessel_gaussian_weight {θ u : ℝ} (hu : 0 < u) :
    u ^ (θ - 3 / 2) * Real.exp (-u) * Real.sqrt (4 * Real.pi * u) =
      (2 * Real.sqrt Real.pi) * (u ^ (θ - 1) * Real.exp (-u)) := by
  rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * Real.pi),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_eq_rpow u]
  rw [show Real.sqrt (4 : ℝ) = 2 from
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)]
  have hp : u ^ (θ - 3 / 2) * u ^ (1 / 2 : ℝ) = u ^ (θ - 1) := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  calc
    _ = 2 * Real.sqrt Real.pi * ((u ^ (θ - 3 / 2) * u ^ (1 / 2 : ℝ)) * Real.exp (-u)) := by ring
    _ = _ := by rw [hp]

private theorem integrable_besselHeat {θ : ℝ} (hθ : 1 / 2 < θ) :
    Integrable (fun p : ℝ × ℝ ↦ p.1 ^ (θ - 3 / 2) *
      Real.exp (-p.1 - p.2 ^ 2 / (4 * p.1))) ((volume.restrict (Ioi 0)).prod volume) := by
  apply (integrable_prod_iff (by fun_prop)).mpr
  have he (u x : ℝ) : u ^ (θ - 3 / 2) * Real.exp (-u - x ^ 2 / (4 * u)) =
      (u ^ (θ - 3 / 2) * Real.exp (-u)) * Real.exp (-(x ^ 2 / (4 * u))) := by
    rw [sub_eq_add_neg (-u), Real.exp_add]
    ring
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0 < u at hu
    have hi := (integrable_exp_neg_mul_sq (b := (4 * u)⁻¹) (by positivity)).const_mul
      (u ^ (θ - 3 / 2) * Real.exp (-u))
    apply hi.congr
    exact .of_forall fun x ↦ by dsimp; rw [he]; congr 2; ring
  · have hi : IntegrableOn (fun u : ℝ ↦ u ^ (θ - 1) * Real.exp (-u)) (Ioi 0) := by
      apply (Real.GammaIntegral_convergent (show 0 < θ by linarith)).congr
      exact .of_forall fun u ↦ mul_comm _ _
    apply (hi.const_mul (2 * Real.sqrt Real.pi)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [show (fun x : ℝ ↦ ‖u ^ (θ - 3 / 2) * Real.exp (-u - x ^ 2 / (4 * u))‖) =
        fun x ↦ (u ^ (θ - 3 / 2) * Real.exp (-u)) * Real.exp (-(x ^ 2 / (4 * u))) from
      funext fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (bessel_integrand_nonneg hu.le x), he]]
    rw [integral_const_mul, integral_bessel_gaussian_real]
    exact (bessel_gaussian_weight hu).symm

private theorem besselHeat_fourier_integrable {θ : ℝ} (hθ : 1 / 2 < θ) (ξ : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ Complex.exp (Complex.I * (ξ : ℂ) * p.2) *
      ((p.1 ^ (θ - 3 / 2) * Real.exp (-p.1 - p.2 ^ 2 / (4 * p.1)) : ℝ) : ℂ))
      ((volume.restrict (Ioi 0)).prod volume) := by
  apply (integrable_besselHeat hθ).mono' (by fun_prop)
  have hu : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi 0)).prod volume), 0 < p.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hu] with p hp
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (bessel_integrand_nonneg hp.le p.2)]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, one_mul,
    zero_add, sub_zero, Real.exp_zero]
  exact le_rfl


private theorem integral_besselHeat_fourier {θ u : ℝ} (hu : 0 < u) (ξ : ℝ) :
    (∫ x : ℝ, Complex.exp (Complex.I * (ξ : ℂ) * x) *
      ((u ^ (θ - 3 / 2) * Real.exp (-u - x ^ 2 / (4 * u)) : ℝ) : ℂ)) =
      ((2 * Real.sqrt Real.pi * (u ^ (θ - 1) * Real.exp (-((1 + ξ ^ 2) * u))) : ℝ) : ℂ) := by
  have he (x : ℝ) : Complex.exp (Complex.I * (ξ : ℂ) * x) *
      ((u ^ (θ - 3 / 2) * Real.exp (-u - x ^ 2 / (4 * u)) : ℝ) : ℂ) =
      ((u ^ (θ - 3 / 2) * Real.exp (-u) : ℝ) : ℂ) *
        (Complex.exp (Complex.I * (ξ : ℂ) * x) *
          (Real.exp (-(x ^ 2 / (4 * u))) : ℂ)) := by
    rw [sub_eq_add_neg (-u), Real.exp_add]
    push_cast
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_bessel_gaussian hu]
  rw [← mul_assoc, ← Complex.ofReal_mul, bessel_gaussian_weight hu,
    ← Complex.ofReal_mul]
  congr 1
  rw [show -((1 + ξ ^ 2) * u) = -u + -(u * ξ ^ 2) by ring, Real.exp_add]
  ring

/-- The normalized Bessel kernel has the reciprocal fractional Sobolev weight as its
Fourier multiplier (with the unnormalized `exp (i ξ x)` convention). -/
theorem bilateralLaplace_normalizedBesselKernel {θ : ℝ} (hθ : 1 / 2 < θ) (ξ : ℝ) :
    bilateralLaplace (fun x : ℝ ↦ (normalizedBesselKernel θ x : ℂ)) (Complex.I * ξ) =
      ((2 * Real.sqrt Real.pi * Real.Gamma θ / Real.Gamma (θ - 1 / 2) *
        (1 + ξ ^ 2) ^ (-θ) : ℝ) : ℂ) := by
  have he (x : ℝ) : (normalizedBesselKernel θ x : ℂ) *
      Complex.exp (Complex.I * (ξ : ℂ) * x) =
      (∫ u : ℝ in Ioi 0, Complex.exp (Complex.I * (ξ : ℂ) * x) *
        ((u ^ (θ - 3 / 2) * Real.exp (-u - x ^ 2 / (4 * u)) : ℝ) : ℂ)) /
          (Real.Gamma (θ - 1 / 2) : ℂ) := by
    rw [integral_const_mul, integral_complex_ofReal]
    simp only [normalizedBesselKernel, Complex.ofReal_div]
    ring
  unfold bilateralLaplace
  simp_rw [he]
  rw [integral_div, ← integral_integral_swap (besselHeat_fourier_integrable hθ ξ)]
  have hi : (∫ u : ℝ in Ioi 0, ∫ x : ℝ, Complex.exp (Complex.I * (ξ : ℂ) * x) *
      ((u ^ (θ - 3 / 2) * Real.exp (-u - x ^ 2 / (4 * u)) : ℝ) : ℂ)) =
      ((2 * Real.sqrt Real.pi * ((1 / (1 + ξ ^ 2)) ^ θ * Real.Gamma θ) : ℝ) : ℂ) := by
    calc
      _ = ∫ u : ℝ in Ioi 0,
          ((2 * Real.sqrt Real.pi * (u ^ (θ - 1) * Real.exp (-((1 + ξ ^ 2) * u))) : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact integral_besselHeat_fourier hu ξ
      _ = _ := by
        rw [integral_complex_ofReal, integral_const_mul,
          Real.integral_rpow_mul_exp_neg_mul_Ioi (show 0 < θ by linarith) (by positivity)]
  rw [hi, ← Complex.ofReal_div]
  congr 1
  rw [one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]
  ring


/-- The Fourier multiplier in Mathlib's `exp (-2π i ξ x)` convention. -/
theorem fourier_normalizedBesselKernel {θ : ℝ} (hθ : 1 / 2 < θ) (ξ : ℝ) :
    FourierTransform.fourier (fun x : ℝ ↦ (normalizedBesselKernel θ x : ℂ)) ξ =
      ((2 * Real.sqrt Real.pi * Real.Gamma θ / Real.Gamma (θ - 1 / 2) *
        (1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ) : ℝ) : ℂ) := by
  have he : FourierTransform.fourier (fun x : ℝ ↦ (normalizedBesselKernel θ x : ℂ)) ξ =
      bilateralLaplace (fun x : ℝ ↦ (normalizedBesselKernel θ x : ℂ))
        (Complex.I * ((-2 * Real.pi * ξ : ℝ) : ℂ)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    unfold bilateralLaplace
    apply integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [smul_eq_mul]
    rw [mul_comm (normalizedBesselKernel θ x : ℂ)]
    congr 2
    push_cast
    ring
  rw [he, bilateralLaplace_normalizedBesselKernel hθ,
    show (-2 * Real.pi * ξ) ^ 2 = (2 * Real.pi * ξ) ^ 2 by ring]

/-- The Green kernel is square-integrable as well as integrable. -/
theorem memLp_two_normalizedBesselKernel {θ : ℝ} (hθ : 1 / 2 < θ) :
    MemLp (normalizedBesselKernel θ) 2 := by
  apply (memLp_two_iff_integrable_sq
    (continuous_normalizedBesselKernel hθ).aestronglyMeasurable).mpr
  apply (integrable_normalizedBesselKernel hθ).mono'
    ((continuous_normalizedBesselKernel hθ).pow 2).aestronglyMeasurable
  exact .of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.pow_apply]
    have h0 := (normalizedBesselKernel_pos hθ x).le
    have h1 := normalizedBesselKernel_le_one hθ x
    nlinarith

/-- The reciprocal Sobolev weight is integrable above the one-dimensional evaluation
threshold. This is the `s > 1` threshold in the repository's squared-weight notation. -/
theorem integrable_reciprocal_fractionalSobolevWeight {θ : ℝ} (hθ : 1 / 2 < θ) :
    Integrable (fun ξ : ℝ ↦ (1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ)) := by
  have hi : Integrable (fun x : ℝ ↦ (1 + x ^ 2) ^ (-θ)) := by
    convert integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := (volume : Measure ℝ)) (r := 2 * θ)
      (by simpa only [Module.finrank_self, Nat.cast_one] using (show 1 < 2 * θ by linarith)) using 1
    funext x
    rw [Real.norm_eq_abs, sq_abs]
    congr 1
    ring
  exact hi.comp_mul_left' (by positivity : 2 * Real.pi ≠ 0)

end RiemannMasullo
