module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec4
public import Mathlib.Analysis.Fourier.FourierTransform

/-! # The half-density Fourier phase on the S-local idèle class quotient -/

@[expose] public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Bₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "Jₛ" => SIdeleQuotient F S
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "μₛ" => sLocalQuotientTamagawaMeasure F S
local notation "half" => (1 / 2 : ℂ)
local notation "normℂ(" x ")" => (((mₛ (x : Jₛ)).val : ℝ) : ℂ)
local notation "halfTheta(" f ")" => fun x : Jₛ ↦
  sLocalAdelicThetaOnClasses F S f x * normℂ(x) ^ half
local notation "chart(" χ ")" =>
  quasiCharacterNormTwist (G := Jₛ) mₛ (isProperMap_sIdeleQuotientNorm F S).continuous
    ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)

local instance : MeasurableSpace Jₛ := borel _

/-- Paper: (3.3.1.4), pp. 129–130.
The quotient Fourier transform of the half-density theta function is the
critical-line zeta value at the inverse unitary character. -/
theorem sLocalThetaHalfDensity_lcaFourier (f : Bₛ) (χ : PontryaginDual Jₛ) :
    lcaFourier μₛ (halfTheta(f)) χ = sLocalIdelicZFunction f (chart(χ⁻¹) half) := by
  have hhalf : 0 < (half).re := by norm_num
  have hZ : sLocalIdelicZFunction f (chart(χ⁻¹) half) =
      sLocalIdelicZetaIntegral f (chart(χ⁻¹) half) :=
    sLocalIdelicZFunction_eq_integral f ⟨χ⁻¹, half, hhalf, rfl⟩
  have hM : sLocalThetaMellinIntegral f (chart(χ⁻¹) half) =
      sLocalIdelicZetaIntegral f (chart(χ⁻¹) half) :=
    sLocalThetaMellinIntegral_eq_zeta f ⟨χ⁻¹, half, hhalf, rfl⟩
  refine Eq.trans ?_ (hM.trans hZ.symm)
  apply integral_congr_ae
  filter_upwards with x
  change (sLocalAdelicThetaOnClasses F S f x * normℂ(x) ^ half) * star (χ x : ℂ) =
    sLocalAdelicThetaOnClasses F S f x * (((χ⁻¹) x : ℂ) * normℂ(x) ^ half)
  rw [show (χ⁻¹) x = (χ x)⁻¹ from rfl, Circle.coe_inv_eq_conj, starRingEnd_apply]
  simpa only [mul_assoc] using
    mul_right_comm (sLocalAdelicThetaOnClasses F S f x) (normℂ(x) ^ half) (star (χ x : ℂ))

/-- Paper: (3.3.1.2), p. 129, and (5.4.2.1), p. 274.
In quotient Fourier coordinates at half density, additive Fourier transform
acts by inversion of the unitary character and multiplication by the inverse
critical-line Tate factor. -/
theorem sLocalThetaHalfDensity_fourier_phase (f : Bₛ) (χ : PontryaginDual Jₛ) :
    lcaFourier μₛ (halfTheta(sAdeleSchwartzFourier f)) χ =
      (sLocalRhoFactor (chart(χ) half))⁻¹ * lcaFourier μₛ (halfTheta(f)) χ⁻¹ := by
  have hFE := existsUnique_sLocalZetaPair_equation χ f half
    (show half ∈ Complex.re ⁻¹' Ioo (0 : ℝ) 1 by
      change 0 < (half).re ∧ (half).re < 1
      norm_num)
  have hreflect : 1 - half = half := by ring
  rw [hreflect] at hFE
  have hnorm := sLocalRhoFactor_norm_criticalLine χ half (by norm_num)
  have hρ : sLocalRhoFactor (chart(χ) half) ≠ 0 :=
    norm_ne_zero_iff.mp (hnorm.trans_ne one_ne_zero)
  have hinput : lcaFourier μₛ (halfTheta(f)) χ⁻¹ =
      sLocalIdelicZFunction f (chart(χ) half) :=
    (sLocalThetaHalfDensity_lcaFourier f χ⁻¹).trans
      (congrArg (fun ψ : PontryaginDual Jₛ ↦ sLocalIdelicZFunction f (chart(ψ) half))
        (inv_inv χ))
  calc
    _ = sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chart(χ⁻¹) half) :=
      sLocalThetaHalfDensity_lcaFourier _ χ
    _ = (sLocalRhoFactor (chart(χ) half))⁻¹ * sLocalIdelicZFunction f (chart(χ) half) :=
      (eq_inv_mul_iff_mul_eq₀ hρ).mpr hFE.symm
    _ = _ := congrArg ((sLocalRhoFactor (chart(χ) half))⁻¹ * ·) hinput.symm

section RadialMellinFourier

open Function
open scoped FourierTransform

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "J₁" => (mₛ).ker
local notation "restrict₁(" χ ")" => (χ : PontryaginDual Jₛ).comp
  (⟨(mₛ).ker.subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ)

private def sLocalRadialThetaExpUnit (x : ℝ) : ℝ≥0ˣ :=
  Units.mk0 (Real.exp x).toNNReal
    (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))

/-- The homogeneous theta profile on a logarithmic norm section at twist
one half. The unitary character on the section gives the Mellin chart for
an arbitrary lift of the norm-one character. -/
def sLocalRadialThetaHalfDensity (τ : ℝ≥0ˣ →ₜ* Iₛ) (χ : PontryaginDual Jₛ)
    (f : Bₛ) (x : ℝ) : ℂ :=
  let t : ℝ≥0ˣ := Units.mk0 (Real.exp x).toNNReal (by positivity)
  let q : Jₛ := QuotientGroup.mk (τ t)
  (sLocalHomogeneousAdelicThetaLinearMap F S (restrict₁(χ)) f q * (χ q : ℂ)) *
    (Real.exp (x / 2) : ℂ)

/-- The critical-line parameter corresponding to Mathlib's real Fourier
kernel `exp(-2π i x ξ)`. -/
def sLocalRadialThetaCriticalParameter (ξ : ℝ) : ℂ :=
  (1 / 2 : ℂ) - ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I

/-- Paper: (3.3.1.5), p. 129. In logarithmic norm coordinates at twist one
half, the real Fourier integral gives the S-local zeta value with the same
unitary character and the critical-line parameter of the Fourier frequency. -/
theorem sLocalRadialThetaHalfDensity_fourier
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (χ : PontryaginDual Jₛ) (f : Bₛ) (ξ : ℝ) :
    𝓕 (sLocalRadialThetaHalfDensity τ χ f) ξ =
      sLocalIdelicZFunction f (chart(χ) (sLocalRadialThetaCriticalParameter ξ)) := by
  let z := sLocalRadialThetaCriticalParameter ξ
  have hz : 0 < z.re := by
    norm_num [z, sLocalRadialThetaCriticalParameter, Complex.sub_re, Complex.mul_re]
  let q (t : ℝ≥0ˣ) : Jₛ := QuotientGroup.mk (τ t)
  let θ := sLocalHomogeneousAdelicThetaLinearMap F S (restrict₁(χ)) f
  let G (t : ℝ≥0ˣ) : ℂ := θ (q t) * chart(χ) z (q t)
  have hG : Integrable G positiveRealHaar :=
    sLocalRadialMellinIntegral_integrable τ hτ f χ z hz
  have he : Measurable sLocalRadialThetaExpUnit :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hFourier : 𝓕 (sLocalRadialThetaHalfDensity τ χ f) ξ =
      sLocalRadialMellinIntegral τ f χ z := by
    change _ = ∫ t, G t ∂positiveRealHaar
    rw [show positiveRealHaar = Measure.map sLocalRadialThetaExpUnit volume from rfl,
      integral_map he.aemeasurable hG.aestronglyMeasurable, Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    let a := q (sLocalRadialThetaExpUnit x)
    have ha : ((mₛ a).val : ℝ) = Real.exp x := by
      change ((mₛ (QuotientGroup.mk (τ (sLocalRadialThetaExpUnit x)))).val : ℝ) = Real.exp x
      rw [sIdeleQuotientNorm_mk, hτ]
      exact Real.coe_toNNReal _ (Real.exp_pos x).le
    have hcpow : ((Real.exp x : ℝ) : ℂ) ^ z = Complex.exp (z * x) := by
      rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
        Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]), mul_comm]
    have hExponent : z * (x : ℂ) = ((x / 2 : ℝ) : ℂ) +
        ((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I := by
      dsimp only [z, sLocalRadialThetaCriticalParameter]
      push_cast
      ring
    simp only [smul_eq_mul, sLocalRadialThetaHalfDensity]
    change Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) *
        ((θ a * (χ a : ℂ)) * (Real.exp (x / 2) : ℂ)) =
      θ a * ((χ a : ℂ) * (((mₛ a).val : ℝ) : ℂ) ^ z)
    rw [ha, hcpow, hExponent, Complex.exp_add, Complex.ofReal_exp]
    ring
  calc
    _ = sLocalRadialMellinIntegral τ f χ z := hFourier
    _ = sLocalThetaMellinIntegral f (chart(χ) z) :=
      sLocalRadialMellinIntegral_eq_theta τ hτ f χ z hz
    _ = sLocalIdelicZetaIntegral f (chart(χ) z) := sLocalThetaMellinIntegral_eq_zeta f ⟨χ, z, hz, rfl⟩
    _ = _ := (sLocalIdelicZFunction_eq_integral f ⟨χ, z, hz, rfl⟩).symm

/-- Paper: (3.3.1.2), p. 129. The real Fourier transform of the radial
theta profile equals the Tate factor times the Fourier transform of the
reflected radial profile of the S-adelic Fourier test. -/
theorem sLocalRadialThetaHalfDensity_fourier_reflected_phase
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (χ : PontryaginDual Jₛ) (f : Bₛ) (ξ : ℝ) :
    𝓕 (sLocalRadialThetaHalfDensity τ χ f) ξ =
      sLocalRhoFactor (chart(χ) (sLocalRadialThetaCriticalParameter ξ)) *
        𝓕 (fun x ↦ sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f) (-x)) ξ := by
  let z := sLocalRadialThetaCriticalParameter ξ
  have hz : z ∈ Complex.re ⁻¹' Ioo (0 : ℝ) 1 := by
    change 0 < z.re ∧ z.re < 1
    norm_num [z, sLocalRadialThetaCriticalParameter, Complex.sub_re, Complex.mul_re]
  have hreflect : sLocalRadialThetaCriticalParameter (-ξ) = 1 - z := by
    dsimp only [z, sLocalRadialThetaCriticalParameter]
    push_cast
    ring
  rw [sLocalRadialThetaHalfDensity_fourier τ hτ χ f ξ, ← Real.fourierInv_eq_fourier_comp_neg,
    Real.fourierInv_eq_fourier_neg,
    sLocalRadialThetaHalfDensity_fourier τ hτ χ⁻¹ (sAdeleSchwartzFourier f) (-ξ), hreflect]
  exact existsUnique_sLocalZetaPair_equation χ f z hz

end RadialMellinFourier

end RiemannMasullo
