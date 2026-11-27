module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec4

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

end RiemannMasullo
