module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedLogTransport
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_CriticalLineFourierPhase
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_UpperHalflineFactorization
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_QuotientLowerFloorTransport
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_LevelPolarComplement
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import RiemannMasullo.Ch12_TraceGeometric.Sec4_GlobalRadialTestProfile
import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import RiemannMasullo.Ch05_ThetaZSpaces.Sec4
import RiemannMasullo.AppA_AlgebraicNT.Sec3
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.Analysis.Fourier.L2Phase
import RiemannMasullo.Ch12_TraceGeometric.Sec4_ClosedLevelLogSupport
import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedTrivialMoment
import RiemannMasullo.Ch12_TraceGeometric.Sec4_LevelPolarTransport
import RiemannMasullo.Ch12_TraceGeometric.Sec4_FullReflectedExactRange
import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedOrderZeroIsometry
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3_FourierBandThetaSupport

/-! # Trace class and the lower-floor limit on the fixed S-local band -/

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal FourierTransform NNReal NumberField.AdeleRing

namespace RiemannMasullo

noncomputable section

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "N" => sIdeleQuotientNorm F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "Zₛ" => sAdelePolarSubspace F S
local notation "Bₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "W(" s ")" => CompactIntervalSobolev μJ (logSIdeleQuotientNorm F S) 0 0 s
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "expUnit" => fun x : ℝ ↦ Units.mk0 (Real.toNNReal (Real.exp x)) (by positivity)
local notation "include₁" =>
  (ContinuousMonoidHom.mk (Subgroup.subtype (MonoidHom.ker (sIdeleQuotientNorm F S)))
    continuous_subtype_val : J₁ →ₜ* Jₛ)
local notation "circleCoe" =>
  (ContinuousMonoidHom.mk Circle.coeHom continuous_subtype_val : Circle →ₜ* ℂ)
local notation "chart" =>
  quasiCharacterNormTwist (G := Jₛ) (sIdeleQuotientNorm F S)
    (IsProperMap.continuous (isProperMap_sIdeleQuotientNorm F S))

/-- Reflection fixes the value at zero, so the S-adelic Fourier transform
preserves both defining polar cancellations. -/
public theorem sAdelePolarSubspace_fourier (f : Zₛ) :
    sAdeleSchwartzFourier f.val ∈ Zₛ := by
  obtain ⟨hf, hF⟩ := (mem_sAdelePolarSubspace f.val).mp f.property
  refine (mem_sAdelePolarSubspace _).mpr ⟨hF, ?_⟩
  rw [sLocal_fourier_inversion, neg_zero, hf]

/-- At exponent one half the real logarithmic theta profile is integrable
by the norm-product Mellin integral. -/
private theorem sLocalRadialThetaHalfDensity_integrable
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (χ : PontryaginDual Jₛ) (f : Bₛ) :
    Integrable (sLocalRadialThetaHalfDensity τ χ f) := by
  let q (t : ℝ≥0ˣ) : Jₛ := QuotientGroup.mk (τ t)
  let θ := sLocalHomogeneousAdelicThetaLinearMap F S (χ.comp include₁) f
  let G (t : ℝ≥0ˣ) : ℂ :=
    θ (q t) * chart ((circleCoe).comp χ) (1 / 2 : ℂ) (q t)
  have hhalf : 0 < ((1 / 2 : ℂ)).re := by norm_num
  have hG : Integrable G positiveRealHaar :=
    sLocalRadialMellinIntegral_integrable τ hτ f χ (1 / 2) hhalf
  have he : Measurable expUnit :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hGmap : Integrable G (Measure.map expUnit (volume : Measure ℝ)) := hG
  refine (hGmap.comp_measurable he).congr (ae_of_all _ fun x ↦ ?_)
  have hN : ((N (q (expUnit x))).val : ℝ) = Real.exp x := by
    change ((N (QuotientGroup.mk (τ (expUnit x)))).val : ℝ) = _
    rw [sIdeleQuotientNorm_mk, hτ]
    exact Real.coe_toNNReal _ (Real.exp_pos x).le
  have hp : ((Real.exp x : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (Real.exp (x / 2) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (Real.exp_pos x).le, ← Real.exp_mul, mul_one_div]
  simp only [Function.comp_apply, sLocalRadialThetaHalfDensity]
  change θ (q (expUnit x)) * ((χ (q (expUnit x)) : ℂ) *
        (((N (q (expUnit x))).val : ℝ) : ℂ) ^ (1 / 2 : ℂ)) =
    (θ (q (expUnit x)) * (χ (q (expUnit x)) : ℂ)) * (Real.exp (x / 2) : ℂ)
  rw [hN, hp, mul_assoc]

private theorem realFourier_mul_const_left (d : ℂ) (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x ↦ d * f x) ξ = d * 𝓕 f ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul (fun x ↦ d * f x),
    Real.fourier_real_eq_integral_exp_smul f, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [smul_eq_mul]
  ring

/-- For an ordinary test, the normalized log coefficients of the test and its
Fourier transform admit integrable representatives related by the Tate phase. -/
private theorem exists_sLocalTheta_reflectedFourierPhase_of_coefficients
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) :
    ∃ χ : PontryaginDual Jₛ, χ.comp include₁ = ω ∧
      (∀ t : ℝ≥0ˣ, χ (QuotientGroup.mk (τ t)) = 1) ∧
      let m (ξ : ℝ) : ℂ :=
        sLocalRhoFactor (chart ((circleCoe).comp χ) (sLocalRadialThetaCriticalParameter ξ))
      AEStronglyMeasurable m volume ∧ (∀ ξ, ‖m ξ‖ = 1) ∧
      ∀ (f : Bₛ) (v w₀ : FlatL2),
        let d : ℂ := Real.sqrt (Measure.real η univ)
        let w := Lp.compMeasurePreserving (fun x : ℝ ↦ -x) (Measure.measurePreserving_neg volume) w₀
        let p (x : ℝ) := d * sLocalRadialThetaHalfDensity τ χ f x
        let r (x : ℝ) := d * sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f) (-x)
        ((v : ℝ → ℂ) =ᵐ[volume] fun x ↦ d * ((Real.exp (x / 2) : ℂ) *
          sLocalHomogeneousAdelicThetaLinearMap F S ω f (QuotientGroup.mk (τ (expUnit x))))) →
        ((w₀ : ℝ → ℂ) =ᵐ[volume] fun x ↦ d * ((Real.exp (x / 2) : ℂ) *
          sLocalHomogeneousAdelicThetaLinearMap F S ω⁻¹ (sAdeleSchwartzFourier f)
            (QuotientGroup.mk (τ (expUnit x))))) →
        Integrable p ∧ Integrable r ∧ (v : ℝ → ℂ) =ᵐ[volume] p ∧
          (w : ℝ → ℂ) =ᵐ[volume] r ∧ ∀ ξ, 𝓕 p ξ = m ξ * 𝓕 r ξ := by
  let σ : ℝ≥0ˣ →ₜ* Jₛ :=
    ⟨(QuotientGroup.mk' (sProjectedDiagonal F S)).comp τ.toMonoidHom,
      QuotientGroup.continuous_mk.comp τ.continuous⟩
  have hσ : RightInverse σ N := fun t ↦
    (sIdeleQuotientNorm_mk F S (τ t)).trans (hτ t)
  obtain ⟨χ, hχ, _⟩ := existsUnique_sLocalNormSectionCharacter σ hσ ω
  have hχinv : (χ⁻¹).comp include₁ = ω⁻¹ := by
    apply PontryaginDual.ext
    intro h
    change (χ h.val)⁻¹ = (ω h)⁻¹
    exact congrArg Inv.inv (congrArg (fun z : PontryaginDual J₁ ↦ z h) hχ.1)
  have hχσinv (t : ℝ≥0ˣ) : χ⁻¹ (σ t) = 1 := by
    change (χ (σ t))⁻¹ = 1
    rw [hχ.2 t, inv_one]
  refine ⟨χ, hχ.1, hχ.2, ?_⟩
  intro m
  have hz (ξ : ℝ) : (sLocalRadialThetaCriticalParameter ξ).re = 1 / 2 := by
    norm_num [sLocalRadialThetaCriticalParameter, Complex.sub_re, Complex.mul_re]
  have hzc : Continuous sLocalRadialThetaCriticalParameter := by
    unfold sLocalRadialThetaCriticalParameter
    fun_prop
  have hmc : Continuous m := by
    apply continuous_iff_continuousAt.mpr
    intro ξ
    let factor (z : ℂ) : ℂ := sLocalRhoFactor (chart ((circleCoe).comp χ) z)
    have hfactor : ContinuousAt factor (sLocalRadialThetaCriticalParameter ξ) :=
      (sLocalRhoFactor_analyticAt_criticalLine χ _ (hz ξ)).continuousAt
    exact hfactor.comp hzc.continuousAt
  refine ⟨hmc.aestronglyMeasurable, fun ξ ↦ sLocalRhoFactor_norm_criticalLine χ _ (hz ξ), ?_⟩
  intro f v w₀ d w p r hv hw₀
  have hprofile (ψ : PontryaginDual Jₛ) (ω' : PontryaginDual J₁)
      (hres : ψ.comp include₁ = ω') (hsec : ∀ t, ψ (σ t) = 1) (g : Bₛ) (x : ℝ) :
      (Real.exp (x / 2) : ℂ) * sLocalHomogeneousAdelicThetaLinearMap F S ω' g
        (QuotientGroup.mk (τ (expUnit x))) =
      sLocalRadialThetaHalfDensity τ ψ g x := by
    have hone : ψ (QuotientGroup.mk (τ (expUnit x))) = 1 := hsec (expUnit x)
    simp only [sLocalRadialThetaHalfDensity, hres, hone, Circle.coe_one, mul_one]
    exact mul_comm _ _
  have hvProfile : (v : ℝ → ℂ) =ᵐ[volume] p :=
    hv.trans (ae_of_all _ fun x ↦ congrArg (d * ·) (hprofile χ ω hχ.1 hχ.2 f x))
  have hwProfile : (w₀ : ℝ → ℂ) =ᵐ[volume] fun x ↦
      d * sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f) x :=
    hw₀.trans (ae_of_all _ fun x ↦
      congrArg (d * ·) (hprofile χ⁻¹ ω⁻¹ hχinv hχσinv (sAdeleSchwartzFourier f) x))
  have hn := Measure.measurePreserving_neg (volume : Measure ℝ)
  have hw : (w : ℝ → ℂ) =ᵐ[volume] r :=
    (Lp.coeFn_compMeasurePreserving w₀ hn).trans (hn.quasiMeasurePreserving.ae_eq_comp hwProfile)
  have hp : Integrable p := (sLocalRadialThetaHalfDensity_integrable τ hτ χ f).const_mul d
  have hr₀ : Integrable (fun x ↦ d * sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f) x) :=
    (sLocalRadialThetaHalfDensity_integrable τ hτ χ⁻¹ (sAdeleSchwartzFourier f)).const_mul d
  have hrMap : Integrable (fun x ↦ d * sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f) x)
      (Measure.map (fun x : ℝ ↦ -x) volume) := by
    rw [hn.map_eq]
    exact hr₀
  have hr : Integrable r := hrMap.comp_measurable hn.measurable
  refine ⟨hp, hr, hvProfile, hw, fun ξ ↦ ?_⟩
  change 𝓕 (fun x ↦ d * sLocalRadialThetaHalfDensity τ χ f x) ξ =
    m ξ * 𝓕 (fun x ↦ d * sLocalRadialThetaHalfDensity τ χ⁻¹
      (sAdeleSchwartzFourier f) (-x)) ξ
  rw [realFourier_mul_const_left, realFourier_mul_const_left,
    sLocalRadialThetaHalfDensity_fourier_reflected_phase τ hτ χ f ξ]
  change d * (m ξ * _) = m ξ * (d * _)
  exact mul_left_comm _ _ _


/-- On a polar test and its S-adelic Fourier transform, the weighted logarithmic
coefficients have integrable representatives satisfying the critical-line
Tate phase identity after reflecting the inverse-character coefficient.
Both representatives include the same square root of the norm-one mass. -/
public theorem exists_sLocalWeightedTheta_reflectedFourierPhase {s : ℝ}
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁)
    (Q : PontryaginDual J₁ → (W(s) →L[ℂ] FlatL2))
    (hQ : ∀ (ω' : PontryaginDual J₁) (u : W(s)),
      (Q ω' u : ℝ → ℂ) =ᵐ[volume] fun x ↦
        (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ *
          ∫ h : J₁, (ω' h : ℂ) * u (h.val * QuotientGroup.mk (τ (expUnit x))) ∂η) :
    ∃ χ : PontryaginDual Jₛ, χ.comp include₁ = ω ∧
      (∀ t : ℝ≥0ˣ, χ (QuotientGroup.mk (τ t)) = 1) ∧
      let m (ξ : ℝ) : ℂ :=
        sLocalRhoFactor (chart ((circleCoe).comp χ) (sLocalRadialThetaCriticalParameter ξ))
      AEStronglyMeasurable m volume ∧ (∀ ξ, ‖m ξ‖ = 1) ∧
      ∀ f : Zₛ,
        let fhat : Zₛ := ⟨sAdeleSchwartzFourier f.val, sAdelePolarSubspace_fourier f⟩
        let v := Q ω (sLocalPWThetaSobolevMap (F := F) (S := S) (s := s)
          (a := 1 / 2) (by norm_num) ω f)
        let w := Lp.compMeasurePreserving (fun x : ℝ ↦ -x) (Measure.measurePreserving_neg volume)
          (Q ω⁻¹ (sLocalPWThetaSobolevMap (F := F) (S := S) (s := s)
            (a := 1 / 2) (by norm_num) ω⁻¹ fhat))
        let d : ℂ := Real.sqrt (Measure.real η univ)
        let p (x : ℝ) := d * sLocalRadialThetaHalfDensity τ χ f.val x
        let r (x : ℝ) := d * sLocalRadialThetaHalfDensity τ χ⁻¹ fhat.val (-x)
        Integrable p ∧ Integrable r ∧ (v : ℝ → ℂ) =ᵐ[volume] p ∧
          (w : ℝ → ℂ) =ᵐ[volume] r ∧ ∀ ξ, 𝓕 p ξ = m ξ * 𝓕 r ξ := by
  obtain ⟨χ, hχ, hsec, hm, hunit, hphase⟩ :=
    exists_sLocalTheta_reflectedFourierPhase_of_coefficients τ hτ ω
  refine ⟨χ, hχ, hsec, hm, hunit, ?_⟩
  intro f fhat v w d p r
  exact hphase f.val v
    (Q ω⁻¹ (sLocalPWThetaSobolevMap (F := F) (S := S) (s := s)
      (a := 1 / 2) (by norm_num) ω⁻¹ fhat))
    (sLocalWeightedAngularLogCoefficient_onTheta τ hτ ω (Q ω) (hQ ω) f)
    (sLocalWeightedAngularLogCoefficient_onTheta τ hτ ω⁻¹ (Q ω⁻¹) (hQ ω⁻¹) fhat)

/-- The same phase-removal isometry gives the reflected generator formula on
both the full band and its polar-free subspace. -/
private theorem exists_sLocalFullWeightedTheta_reflectedLogInput_of_Q {s : ℝ}
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁)
    (Q : PontryaginDual J₁ → (W(s) →L[ℂ] FlatL2))
    (hQ : ∀ (ω' : PontryaginDual J₁) (u : W(s)),
      (Q ω' u : ℝ → ℂ) =ᵐ[volume] fun x ↦
        (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ *
          ∫ h : J₁, (ω' h : ℂ) * u (h.val * QuotientGroup.mk (τ (expUnit x))) ∂η) :
    ∃ (χ : PontryaginDual Jₛ) (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2),
      χ.comp include₁ = ω ∧ (∀ t : ℝ≥0ˣ, χ (QuotientGroup.mk (τ t)) = 1) ∧
      let m (ξ : ℝ) : ℂ :=
        sLocalRhoFactor (chart ((circleCoe).comp χ) (sLocalRadialThetaCriticalParameter ξ))
      (∀ v, (Lp.fourierTransformₗᵢ ℝ ℂ (U v) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦
        star (m ξ) * (Lp.fourierTransformₗᵢ ℝ ℂ v : FlatL2) ξ) ∧
      let T : W(s) →L[ℂ] FlatL2 := U.toLinearIsometry.toContinuousLinearMap.comp (Q ω)
      (∀ f : Bₛ,
        (T (Isolated.sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s)
          (a := 1 / 2) (by norm_num) ω f) : ℝ → ℂ) =ᵐ[volume] fun x ↦
          (Real.sqrt (Measure.real η univ) : ℂ) *
            sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f) (-x)) ∧
      (∀ f : Zₛ,
        (T (sLocalPWThetaSobolevMap (F := F) (S := S) (s := s)
          (a := 1 / 2) (by norm_num) ω f) : ℝ → ℂ) =ᵐ[volume] fun x ↦
          (Real.sqrt (Measure.real η univ) : ℂ) *
            sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f.val) (-x)) := by
  obtain ⟨χ, hχ, hsec, hm, hunit, hphase⟩ :=
    exists_sLocalTheta_reflectedFourierPhase_of_coefficients τ hτ ω
  let m (ξ : ℝ) : ℂ :=
    sLocalRhoFactor (chart ((circleCoe).comp χ) (sLocalRadialThetaCriticalParameter ξ))
  obtain ⟨U, hUFourier, _, hCancel⟩ := exists_L2FourierInversePhase m hm (ae_of_all _ hunit)
  let T : W(s) →L[ℂ] FlatL2 := U.toLinearIsometry.toContinuousLinearMap.comp (Q ω)
  have hFull (f : Bₛ) :
      (T (Isolated.sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s)
        (a := 1 / 2) (by norm_num) ω f) : ℝ → ℂ) =ᵐ[volume] fun x ↦
        (Real.sqrt (Measure.real η univ) : ℂ) *
          sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f) (-x) := by
    let v : FlatL2 := Q ω (Isolated.sLocalFullPWThetaSobolevMap
      (F := F) (S := S) (s := s) (a := 1 / 2) (by norm_num) ω f)
    let w₀ : FlatL2 := Q ω⁻¹ (Isolated.sLocalFullPWThetaSobolevMap
      (F := F) (S := S) (s := s) (a := 1 / 2) (by norm_num) ω⁻¹ (sAdeleSchwartzFourier f))
    obtain ⟨hp, hr, hv, hw, hFourier⟩ := hphase f v w₀
      (Isolated.sLocalWeightedAngularLogCoefficient_onFullTheta τ hτ ω (Q ω) (hQ ω) f)
      (Isolated.sLocalWeightedAngularLogCoefficient_onFullTheta τ hτ ω⁻¹ (Q ω⁻¹) (hQ ω⁻¹)
        (sAdeleSchwartzFourier f))
    have hU := hCancel _ _ _ _ hp hr hv hw (ae_of_all _ hFourier)
    change (U v : ℝ → ℂ) =ᵐ[volume] _
    rw [hU]
    exact hw
  refine ⟨χ, U, hχ, hsec, hUFourier, hFull, fun f ↦ ?_⟩
  simpa only [Isolated.sLocalFullPWThetaSobolevMap_polar] using hFull f.val

local notation "band(" B ")" =>
  Subtype (fun f : Zₛ ↦ Subtype.val f ∈ sLocalPWTests (F := F) (S := S) (T := S) le_rfl
    (sLocalPWProductRegion S B))

private theorem reflectedWeightedTheta_zero_lt_of_band
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (χ : PontryaginDual Jₛ) {B : ℝ} (hB : 0 < B) (f : Bₛ)
    (hf : f ∈ sLocalPWTests (F := F) (S := S) (T := S)
      le_rfl (sLocalPWProductRegion S B))
    (x : ℝ) (hx : x < -Real.log B) :
    sLocalRadialThetaHalfDensity τ χ (sAdeleSchwartzFourier f) (-x) = 0 := by
  let σ : ℝ≥0ˣ →ₜ* Jₛ :=
    ⟨(QuotientGroup.mk' (sProjectedDiagonal F S)).comp τ.toMonoidHom,
      QuotientGroup.continuous_mk.comp τ.continuous⟩
  have hσ : RightInverse σ N :=
    fun t ↦ (sIdeleQuotientNorm_mk F S (τ t)).trans (hτ t)
  let t : ℝ≥0ˣ := expUnit (-x)
  have hzero := sLocalPWTests_sameStage_fourierTheta_reflected_log_eq_zero
    σ hσ (χ.comp include₁) f hB hf x hx
  change sLocalHomogeneousAdelicThetaLinearMap F S (χ.comp include₁)
    (sAdeleSchwartzFourier f) (σ t) = 0 at hzero
  change (sLocalHomogeneousAdelicThetaLinearMap F S (χ.comp include₁)
    (sAdeleSchwartzFourier f) (σ t) * (χ (σ t) : ℂ)) *
    (Real.exp ((-x) / 2) : ℂ) = 0
  rw [hzero, zero_mul, zero_mul]

private theorem reflectedWeightedTheta_zero_lt
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (χ : PontryaginDual Jₛ) {B : ℝ} (hB : 0 < B) (f : band(B))
    (x : ℝ) (hx : x < -Real.log B) :
    sLocalRadialThetaHalfDensity τ χ (sAdeleSchwartzFourier f.val.val) (-x) = 0 :=
  reflectedWeightedTheta_zero_lt_of_band τ hτ χ hB f.val.val f.property x hx

/-- The reflected coordinate map on all ordinary order-zero generators. -/
@[expose] public def sLocalFullReflectedGenAE
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (ω : PontryaginDual J₁) (χ : PontryaginDual Jₛ)
    (T : W(0) →L[ℂ] FlatL2) : Prop :=
  ∀ f : Bₛ,
    (T (Isolated.sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := 0)
      (a := 1 / 2) (by norm_num) ω f) : ℝ → ℂ) =ᵐ[volume] fun x ↦
      (Real.sqrt (Measure.real η univ) : ℂ) *
        sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f) (-x)

/-- A single angular coefficient, lift, and inverse Tate phase give the
order-zero reflected coordinates and exact ranges at every positive
band radius. -/
public theorem exists_sLocalFullReflectedCoordinates_uniform_orderZero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) :
    ∃ (χ : PontryaginDual Jₛ) (Q : W(0) →L[ℂ] FlatL2) (L : FlatL2 →ₗᵢ[ℂ] W(0))
      (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2),
      χ.comp include₁ = ω ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧ ‖Q‖ ≤ 1 ∧
      (∀ u, (Q u : ℝ → ℂ) =ᵐ[volume] fun x ↦
        (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ *
          ∫ h : J₁, (ω h : ℂ) * u (h.val * QuotientGroup.mk (τ (expUnit x))) ∂η) ∧
      (∀ v, (L v : Jₛ → ℂ) =ᵐ[intervalSobolevMeasure μJ (logSIdeleQuotientNorm F S) 0 0 0]
        fun q ↦ (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ * (χ q : ℂ)⁻¹ *
          v (logSIdeleQuotientNorm F S q)) ∧
      let m (ξ : ℝ) : ℂ :=
        sLocalRhoFactor (chart ((circleCoe).comp χ) (sLocalRadialThetaCriticalParameter ξ))
      (∀ v, (Lp.fourierTransformₗᵢ ℝ ℂ (U v) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦
        star (m ξ) * (Lp.fourierTransformₗᵢ ℝ ℂ v : FlatL2) ξ) ∧
      let T := U.toLinearIsometry.toContinuousLinearMap.comp Q
      sLocalFullReflectedGenAE τ ω χ T ∧
      ∀ B : ℝ, 0 < B →
        let V : Submodule ℂ W(0) := Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0)
          le_rfl (a := 1 / 2) (by norm_num) ω B
        (∀ u ∈ V, L (Q u) = u) ∧
        (∀ u ∈ V, ∀ᵐ x : ℝ ∂volume, x < -Real.log B → T u x = 0) ∧
        (Set.range (fun u : V ↦ T u.val) = {r : FlatL2 | ∀ᵐ x : ℝ ∂volume, x < -Real.log B → r x = 0}) ∧
        Set.range (fun u : sLocalInvariantPWSobolev (F := F) (S := S) (s := 0) le_rfl
          (show (0 : ℝ) < 1 / 2 by norm_num) ω B ↦ T u.val) =
          {r : FlatL2 | (∀ᵐ x : ℝ ∂volume, x < -Real.log B → r x = 0) ∧
            (ω = 1 → (∫ x, (Real.exp (-x / 2) : ℂ) * r x) = 0)} := by
  classical
  let Q (ω' : PontryaginDual J₁) :=
    (exists_sLocalWeightedAngularLogCoefficient (s := 0) le_rfl τ hτ ω').choose
  have hQ := fun ω' ↦ (exists_sLocalWeightedAngularLogCoefficient (s := 0) le_rfl τ hτ ω').choose_spec.2
  have hQnorm : ‖Q ω‖ ≤ 1 :=
    (exists_sLocalWeightedAngularLogCoefficient (s := 0) le_rfl τ hτ ω).choose_spec.1
  obtain ⟨χ, U, hχ, hsec, hPhase, hFull, _⟩ :=
    exists_sLocalFullWeightedTheta_reflectedLogInput_of_Q τ hτ ω Q hQ
  obtain ⟨L, hLrep, hLeft⟩ :=
    exists_sLocalWeightedLogCharacterLift_leftInverse_of_representatives_zero τ hτ ω χ hχ hsec
  refine ⟨χ, Q ω, L, U, hχ, hsec, hQnorm, hQ ω, hLrep, hPhase, hFull, ?_⟩
  intro B hB V
  let gen : Bₛ →ₗ[ℂ] W(0) := Isolated.sLocalFullPWThetaSobolevMap
    (F := F) (S := S) (s := 0) (a := 1 / 2) (by norm_num) ω
  let P := (sLocalPWTests (F := F) (S := S) (T := S) le_rfl (sLocalPWProductRegion S B)).map gen
  let D : W(0) →L[ℂ] W(0) := L.toContinuousLinearMap.comp (Q ω) - ContinuousLinearMap.id ℂ (W(0))
  have hGen (f : Bₛ) : L (Q ω (gen f)) = gen f :=
    hLeft f (gen f) (Q ω (gen f))
      (Isolated.sLocalFullPWThetaSobolevMap_apply (F := F) (S := S) (s := 0)
        (a := 1 / 2) (by norm_num) ω f)
      (Isolated.sLocalWeightedAngularLogCoefficient_onFullTheta τ hτ ω (Q ω) (hQ ω) f)
  have hker : V ≤ D.ker := by
    change P.topologicalClosure ≤ D.ker
    refine Submodule.topologicalClosure_minimal _ ?_ D.isClosed_ker
    rintro _ ⟨f, _, rfl⟩
    exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr (hGen f))
  have hRecover (u : W(0)) (hu : u ∈ V) : L (Q ω u) = u := by
    have hz : D u = 0 := LinearMap.mem_ker.mp (hker hu)
    change (L (Q ω u) : W(0)) - u = 0 at hz
    exact sub_eq_zero.mp hz
  let T := U.toLinearIsometry.toContinuousLinearMap.comp (Q ω)
  have hSupport (u : W(0)) (hu : u ∈ V) :
      ∀ᵐ x : ℝ ∂volume, x < -Real.log B → T u x = 0 := by
    refine map_closedSpan_ae_eq_zero_lt_of_generators (P : Set (W(0))) (-Real.log B) T ?_ u ?_
    · rintro _ ⟨f, hf, rfl⟩
      filter_upwards [hFull f] with x hxEq
      intro hx
      rw [hxEq, reflectedWeightedTheta_zero_lt_of_band τ hτ χ⁻¹ hB f hf x hx, mul_zero]
    · rw [Submodule.span_eq]
      exact hu
  have hIso (u : W(0)) (hu : u ∈ V) : ‖T u‖ = ‖u‖ := by
    change ‖U (Q ω u)‖ = ‖u‖
    rw [U.norm_map, ← L.norm_map (Q ω u), hRecover u hu]
  obtain ⟨hFullRange, hPolarRange⟩ := sLocalFullAndPolarPWSobolev_reflectedRanges_orderZero_of_map
    τ hτ ω χ hχ hsec hB T hFull hIso hSupport
  exact ⟨hRecover, hSupport, hFullRange, hPolarRange⟩

/-- At Sobolev order zero the angular coefficient and inverse Tate phase
act on every generator of the full band. Their composite has reflected
half-line support, and the angular lift recovers each full-band vector. -/
public theorem exists_sLocalFullReflectedCoordinates_orderZero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) {B : ℝ} (hB : 0 < B) :
    let V : Submodule ℂ W(0) := Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0)
      le_rfl (a := 1 / 2) (by norm_num) ω B
    ∃ (χ : PontryaginDual Jₛ) (Q : W(0) →L[ℂ] FlatL2) (L : FlatL2 →ₗᵢ[ℂ] W(0))
      (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2),
      χ.comp include₁ = ω ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧ ‖Q‖ ≤ 1 ∧
      (∀ u, (Q u : ℝ → ℂ) =ᵐ[volume] fun x ↦
        (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ *
          ∫ h : J₁, (ω h : ℂ) * u (h.val * QuotientGroup.mk (τ (expUnit x))) ∂η) ∧
      (∀ v, (L v : Jₛ → ℂ) =ᵐ[intervalSobolevMeasure μJ (logSIdeleQuotientNorm F S) 0 0 0]
        fun q ↦ (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ * (χ q : ℂ)⁻¹ *
          v (logSIdeleQuotientNorm F S q)) ∧
      (∀ u ∈ V, L (Q u) = u) ∧
      let m (ξ : ℝ) : ℂ :=
        sLocalRhoFactor (chart ((circleCoe).comp χ) (sLocalRadialThetaCriticalParameter ξ))
      (∀ v, (Lp.fourierTransformₗᵢ ℝ ℂ (U v) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦
        star (m ξ) * (Lp.fourierTransformₗᵢ ℝ ℂ v : FlatL2) ξ) ∧
      let T := U.toLinearIsometry.toContinuousLinearMap.comp Q
      sLocalFullReflectedGenAE τ ω χ T ∧
      (∀ u ∈ V, ∀ᵐ x : ℝ ∂volume, x < -Real.log B → T u x = 0) ∧
      (Set.range (fun u : V ↦ T u.val) = {r : FlatL2 | ∀ᵐ x : ℝ ∂volume, x < -Real.log B → r x = 0}) ∧
      Set.range (fun u : sLocalInvariantPWSobolev (F := F) (S := S) (s := 0) le_rfl
        (show (0 : ℝ) < 1 / 2 by norm_num) ω B ↦ T u.val) =
        {r : FlatL2 | (∀ᵐ x : ℝ ∂volume, x < -Real.log B → r x = 0) ∧
          (ω = 1 → (∫ x, (Real.exp (-x / 2) : ℂ) * r x) = 0)} := by
  intro V
  obtain ⟨χ, Q, L, U, hχ, hsec, hQnorm, hQ, hL, hPhase, hGen, hBands⟩ :=
    exists_sLocalFullReflectedCoordinates_uniform_orderZero (F := F) (S := S) τ hτ ω
  obtain ⟨hRecover, hSupport, hFullRange, hPolarRange⟩ := hBands B hB
  exact ⟨χ, Q, L, U, hχ, hsec, hQnorm, hQ, hL, hRecover, hPhase, hGen,
    hSupport, hFullRange, hPolarRange⟩

private theorem exists_sLocalInvariantPW_reflectedLogInput_aux
    {s : ℝ} (hs : 0 ≤ s)
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) {B : ℝ} (hB : 0 < B) :
    let level := sLocalInvariantPWSobolev (F := F) (S := S) hs
      (show (0 : ℝ) < 1 / 2 by norm_num) ω B
    ∃ (χ : PontryaginDual Jₛ) (T : W(s) →L[ℂ] FlatL2),
      χ.comp include₁ = ω ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧ ‖T‖ ≤ 1 ∧
      (∀ f : Zₛ,
        (T (sLocalPWThetaSobolevMap (F := F) (S := S) (s := s)
          (a := 1 / 2) (by norm_num) ω f) : ℝ → ℂ) =ᵐ[volume] fun x ↦
          (Real.sqrt (Measure.real η univ) : ℂ) *
            sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f.val) (-x)) ∧
      (∀ u ∈ level, ∀ᵐ x : ℝ ∂volume, x < -Real.log B → T u x = 0) ∧
      (s = 0 → ∀ u ∈ level, ‖T u‖ = ‖u‖) := by
  classical
  intro level
  let Q (ω' : PontryaginDual J₁) :=
    (exists_sLocalWeightedAngularLogCoefficient hs τ hτ ω').choose
  have hQ := fun ω' ↦ (exists_sLocalWeightedAngularLogCoefficient hs τ hτ ω').choose_spec.2
  have hQnorm : ‖Q ω‖ ≤ 1 :=
    (exists_sLocalWeightedAngularLogCoefficient hs τ hτ ω).choose_spec.1
  obtain ⟨χ, hχ, hsec, hm, hunit, hphase⟩ :=
    exists_sLocalWeightedTheta_reflectedFourierPhase τ hτ ω Q hQ
  let m (ξ : ℝ) : ℂ :=
    sLocalRhoFactor (chart ((circleCoe).comp χ) (sLocalRadialThetaCriticalParameter ξ))
  obtain ⟨U, _, _, hCancel⟩ := exists_L2FourierInversePhase m hm (ae_of_all _ hunit)
  let T : W(s) →L[ℂ] FlatL2 := U.toLinearIsometry.toContinuousLinearMap.comp (Q ω)
  have hTnorm : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound T zero_le_one
    intro u
    change ‖U (Q ω u)‖ ≤ 1 * ‖u‖
    rw [U.norm_map]
    exact ((Q ω).le_opNorm u).trans (mul_le_mul_of_nonneg_right hQnorm (norm_nonneg u))
  have hTisometry (hs₀ : s = 0) (u : W(s)) (hu : u ∈ level) : ‖T u‖ = ‖u‖ := by
    subst s
    obtain ⟨L, hLQ⟩ := exists_sLocalWeightedAngularLogCoefficient_leftInverse_on_level_zero
      τ hτ ω χ hχ hsec B (Q ω) (hQ ω)
    change ‖U (Q ω u)‖ = ‖u‖
    calc
      ‖U (Q ω u)‖ = ‖Q ω u‖ := U.norm_map (Q ω u)
      _ = ‖L (Q ω u)‖ := (L.norm_map (Q ω u)).symm
      _ = ‖u‖ := congrArg norm (hLQ u hu)
  have hGen (f : Zₛ) :
      (T (sLocalPWThetaSobolevMap (F := F) (S := S) (s := s)
        (a := 1 / 2) (by norm_num) ω f) : ℝ → ℂ) =ᵐ[volume]
      fun x ↦ (Real.sqrt (Measure.real η univ) : ℂ) *
        sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f.val) (-x) := by
    obtain ⟨hp, hr, hv, hw, hFourier⟩ := hphase f
    have hU := hCancel _ _ _ _ hp hr hv hw (ae_of_all _ hFourier)
    change (U (Q ω (sLocalPWThetaSobolevMap (F := F) (S := S) (s := s)
      (a := 1 / 2) (by norm_num) ω f)) : ℝ → ℂ) =ᵐ[volume] _
    rw [hU]
    exact hw
  refine ⟨χ, T, hχ, hsec, hTnorm, hGen, fun u hu ↦ ?_, hTisometry⟩
  refine sLocalInvariantPWSobolev_map_ae_eq_zero_lt_of_generators hs
    (show (0 : ℝ) < 1 / 2 by norm_num) ω B (-Real.log B) T (fun f ↦ ?_) u hu
  filter_upwards [hGen f.val] with x hxEq
  intro hx
  rw [hxEq, reflectedWeightedTheta_zero_lt τ hτ χ⁻¹ hB f x hx, mul_zero]

/-- For the Chapter 11 invariant level, undoing the critical-line Tate phase
gives a contraction to flat functions supported on the reflected half-line.
Its values on the defining theta generators are the inverse-character
Fourier theta profiles with the exact norm-one Haar factor. -/
theorem exists_sLocalInvariantPW_reflectedLogInput
    {s : ℝ} (hs : 0 ≤ s)
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) {B : ℝ} (hB : 0 < B) :
    ∃ (χ : PontryaginDual Jₛ) (T : W(s) →L[ℂ] FlatL2),
      χ.comp include₁ = ω ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧ ‖T‖ ≤ 1 ∧
      (∀ f : Zₛ,
        (T (sLocalPWThetaSobolevMap (F := F) (S := S) (s := s)
          (a := 1 / 2) (by norm_num) ω f) : ℝ → ℂ) =ᵐ[volume] fun x ↦
          (Real.sqrt (Measure.real η univ) : ℂ) *
            sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f.val) (-x)) ∧
      ∀ u ∈ sLocalInvariantPWSobolev (F := F) (S := S) hs
          (show (0 : ℝ) < 1 / 2 by norm_num) ω B,
        ∀ᵐ x : ℝ ∂volume, x < -Real.log B → T u x = 0 := by
  obtain ⟨χ, T, hχ, hsec, hnorm, hGen, hSupport, _⟩ :=
    exists_sLocalInvariantPW_reflectedLogInput_aux hs τ hτ ω hB
  exact ⟨χ, T, hχ, hsec, hnorm, hGen, hSupport⟩

/-- Paper: (11.2.1.6), p. 488, and Theorem 12.4.1.1, pp. 515–517.
At order zero the reflected input is isometric on the actual half-density
level. Its generator representatives retain the Tamagawa normalization,
and for the trivial norm-one character the exponential moment vanishes. -/
public theorem exists_sLocalInvariantPW_reflectedLogInput_orderZero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) {B : ℝ} (hB : 0 < B) :
    let level := sLocalInvariantPWSobolev (F := F) (S := S) (s := 0) le_rfl
      (show (0 : ℝ) < 1 / 2 by norm_num) ω B
    ∃ (χ : PontryaginDual Jₛ) (T : W(0) →L[ℂ] FlatL2),
      χ.comp include₁ = ω ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧ ‖T‖ ≤ 1 ∧
      (∀ f : Zₛ,
        (T (sLocalPWThetaSobolevMap (F := F) (S := S) (s := 0)
          (a := 1 / 2) (by norm_num) ω f) : ℝ → ℂ) =ᵐ[volume] fun x ↦
          (Real.sqrt (Measure.real η univ) : ℂ) *
            sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f.val) (-x)) ∧
      (∀ u ∈ level, ∀ᵐ x : ℝ ∂volume, x < -Real.log B → T u x = 0) ∧
      (∀ u ∈ level, ‖T u‖ = ‖u‖) ∧
      (ω = 1 → ∀ u ∈ level,
        Integrable (fun x ↦ (Real.exp (-x / 2) : ℂ) * T u x) ∧
          (∫ x, (Real.exp (-x / 2) : ℂ) * T u x) = 0) := by
  intro level
  obtain ⟨χ, T, hχ, hsec, hnorm, hGen, hSupport, hIso⟩ :=
    exists_sLocalInvariantPW_reflectedLogInput_aux (s := 0) le_rfl τ hτ ω hB
  refine ⟨χ, T, hχ, hsec, hnorm, hGen, hSupport, hIso rfl, ?_⟩
  intro hω u hu
  subst hω
  exact sLocalInvariantPWSobolev_reflectedTrivialMoment_of_representatives
    (s := 0) le_rfl τ hτ B χ T hχ hsec hGen hSupport u hu

/-- The actual reflected operator on the closed level has vanishing
exponential moment in the trivial norm-one type. -/
public theorem exists_sLocalInvariantPW_reflectedLogInput_trivialMoment
    {s : ℝ} (hs : 0 ≤ s)
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    {B : ℝ} (hB : 0 < B) :
    ∃ (χ : PontryaginDual Jₛ) (T : W(s) →L[ℂ] FlatL2),
      χ.comp include₁ = 1 ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧ ‖T‖ ≤ 1 ∧
      (∀ f : Zₛ,
        (T (sLocalPWThetaSobolevMap (F := F) (S := S) (s := s)
          (a := 1 / 2) (by norm_num) 1 f) : ℝ → ℂ) =ᵐ[volume] fun x ↦
          (Real.sqrt (Measure.real η univ) : ℂ) *
            sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f.val) (-x)) ∧
      ∀ u ∈ sLocalInvariantPWSobolev (F := F) (S := S) hs
          (show (0 : ℝ) < 1 / 2 by norm_num) 1 B,
        (∀ᵐ x : ℝ ∂volume, x < -Real.log B → T u x = 0) ∧
        Integrable (fun x ↦ (Real.exp (-x / 2) : ℂ) * T u x) ∧
        (∫ x, (Real.exp (-x / 2) : ℂ) * T u x) = 0 := by
  obtain ⟨χ, T, hχ, hsec, hnorm, hgen, hsupport⟩ :=
    exists_sLocalInvariantPW_reflectedLogInput hs τ hτ (1 : PontryaginDual J₁) hB
  refine ⟨χ, T, hχ, hsec, hnorm, hgen, fun u hu ↦ ⟨hsupport u hu, ?_⟩⟩
  exact sLocalInvariantPWSobolev_reflectedTrivialMoment_of_representatives
    hs τ hτ B χ T hχ hsec hgen hsupport u hu

end

end RiemannMasullo


section SupportedConvolution

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap

namespace RiemannMasullo

variable {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Bounded precomposition preserves rectangular trace class. -/
public theorem comp_right_mem_traceClass (U : F →L[ℂ] G) (hU : U ∈ traceClassOperators F G)
    (P : E →L[ℂ] F) : U.comp P ∈ traceClassOperators E G := by
  have hSummable : Summable (approximationNumber U) := by
    simpa only [Real.rpow_one] using hU.2
  change IsCompactOperator (U.comp P) ∧
    Summable (fun n ↦ approximationNumber (U.comp P) n ^ (1 : ℝ))
  simp only [Real.rpow_one]
  refine ⟨hU.1.comp_clm P, (summable_nat_add_iff 1).mp ?_⟩
  refine (hSummable.mul_right (approximationNumber P 0)).of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_)
  · exact Real.sInf_nonneg fun _ ⟨_, _, hr⟩ ↦ hr ▸ norm_nonneg _
  · simpa only [Nat.add_zero] using approximationNumber_comp_le U P n 0

/-- Bounded postcomposition preserves rectangular trace class. -/
public theorem comp_left_mem_traceClass (U : E →L[ℂ] F) (hU : U ∈ traceClassOperators E F)
    (P : F →L[ℂ] G) : P.comp U ∈ traceClassOperators E G := by
  have hSummable : Summable (approximationNumber U) := by
    simpa only [Real.rpow_one] using hU.2
  change IsCompactOperator (P.comp U) ∧
    Summable (fun n ↦ approximationNumber (P.comp U) n ^ (1 : ℝ))
  simp only [Real.rpow_one]
  refine ⟨hU.1.clm_comp P, (summable_nat_add_iff 1).mp ?_⟩
  refine (hSummable.mul_left (approximationNumber P 0)).of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_)
  · exact Real.sInf_nonneg fun _ ⟨_, _, hr⟩ ↦ hr ▸ norm_nonneg _
  · simpa only [Nat.zero_add] using approximationNumber_comp_le P U 0 n

/-- A product of two Hilbert–Schmidt maps is nuclear after precomposing
with a bounded map from its target space to its source space. -/
theorem isNuclearOperator_hilbertSchmidt_comp_right (A : hilbertSchmidtOperators F G)
    (B : hilbertSchmidtOperators E F) (P : G →L[ℂ] E) :
    IsNuclearOperator ((A.val.comp B.val).comp P) :=
  (mem_traceClassOperators_iff_isNuclearOperator _).mp
    (comp_right_mem_traceClass _ (comp_mem_traceClass A B) P)

/-- A product of two Hilbert–Schmidt maps is nuclear after postcomposing
with a bounded map from its target space to its source space. -/
theorem isNuclearOperator_hilbertSchmidt_comp_left (A : hilbertSchmidtOperators F G)
    (B : hilbertSchmidtOperators E F) (P : G →L[ℂ] E) :
    IsNuclearOperator (P.comp (A.val.comp B.val)) :=
  (mem_traceClassOperators_iff_isNuclearOperator _).mp
    (comp_left_mem_traceClass _ (comp_mem_traceClass A B) P)

end RiemannMasullo

namespace RiemannMasullo

private theorem exists_complexL2RestrictIci (a : ℝ) :
    let μ := (volume : Measure ℝ).restrict (Ici a)
    ∃ R : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 μ,
      ∀ v, (R v : ℝ → ℂ) =ᵐ[μ] (v : ℝ → ℂ) := by
  intro μ
  have hle : μ ≤ (volume : Measure ℝ) := Measure.restrict_le_self
  have h₁ : μ ≤ (1 : ℝ≥0∞) • (volume : Measure ℝ) := by
    simpa only [one_smul] using hle
  let R₀ := Lp.LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) ENNReal.one_ne_top h₁
  have hR₀ (v : Lp ℂ 2 (volume : Measure ℝ)) :=
    Lp.coeFn_LpToLpOfMeasureLeSMul (E := ℂ) ENNReal.one_ne_top h₁ v
  refine ⟨{ toFun := R₀, map_add' := R₀.map_add, map_smul' := ?_, cont := R₀.continuous }, hR₀⟩
  intro c v
  exact Lp.ext ((hR₀ (c • v)).trans (Filter.EventuallyEq.trans (ae_mono hle (Lp.coeFn_smul c v))
    (((hR₀ v).symm.fun_comp (c • ·)).trans (Lp.coeFn_smul c (R₀ v)).symm)))

/-- The weighted upper-cutoff convolution is trace class on a boundedly
parametrized source with right-half-line support. It agrees with the full-line
convolution of each source vector's flat representative. -/
theorem exists_upperHalflineWeightedConvolutionOfSupportedInput
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : ℝ) (hs : 0 ≤ s) (a T : ℝ) (ρ : ℝ → ℝ) (hρm : Measurable ρ)
    (hρ : ∀ t, |ρ t| ≤ 1) (hρT : ∀ t, T < t → ρ t = 0) (q : 𝓢(ℝ, ℂ))
    (J : H →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hJ : ∀ v : H, ∀ᵐ y : ℝ ∂volume, y < a → J v y = 0) :
    let ν := intervalSobolevMeasure (volume : Measure ℝ) id 0 0 s
    ∃ U : H →L[ℂ] Lp ℂ 2 ν, U ∈ traceClassOperators H (Lp ℂ 2 ν) ∧
      (∀ L : Lp ℂ 2 ν →L[ℂ] H, IsNuclearOperator (L.comp U)) ∧
      ∀ v : H, ∀ᵐ x ∂ν,
        Integrable (fun y ↦ ((ρ x : ℂ) * q (x - y)) * J v y) volume ∧
        U v x = (ρ x : ℂ) * ∫ y, q (x - y) * J v y := by
  intro ν
  let μ := (volume : Measure ℝ).restrict (Ici a)
  obtain ⟨R, hR⟩ := exists_complexL2RestrictIci a
  obtain ⟨A, B, hAB, hApply⟩ :=
    exists_upperHalflineWeightedConvolutionFactors s hs a T ρ hρm hρ hρT q
  let U : H →L[ℂ] Lp ℂ 2 ν := (A.val.comp B.val).comp (R.comp J)
  have hU : U ∈ traceClassOperators H (Lp ℂ 2 ν) := comp_right_mem_traceClass _ hAB (R.comp J)
  refine ⟨U, hU, fun L ↦ (mem_traceClassOperators_iff_isNuclearOperator _).mp
    (comp_left_mem_traceClass U hU L), ?_⟩
  intro v
  let u := J v
  have hSupport (k : ℝ → ℂ) :
      (Ici a).indicator (fun y ↦ k y * u y) =ᵐ[volume] fun y ↦ k y * u y := by
    filter_upwards [hJ v] with y hy
    by_cases hmem : y ∈ Ici a
    · exact Set.indicator_of_mem hmem _
    · have hlt : y < a := lt_of_not_ge hmem
      exact (Set.indicator_of_notMem hmem _).trans ((mul_eq_zero_of_right (k y) (hy hlt)).symm)
  have hCompare (k : ℝ → ℂ) :
      (fun y ↦ k y * R u y) =ᵐ[μ] fun y ↦ k y * u y :=
    (hR u).mono fun y hy ↦ congrArg (k y * ·) hy
  filter_upwards [hApply (R u)] with x hx
  have hRestricted : Integrable (fun y ↦ ((ρ x : ℂ) * q (x - y)) * u y) μ :=
    hx.1.congr (hCompare (fun y ↦ (ρ x : ℂ) * q (x - y)))
  refine ⟨((integrable_indicator_iff measurableSet_Ici).2 hRestricted).congr
    (hSupport (fun y ↦ (ρ x : ℂ) * q (x - y))), ?_⟩
  change A.val (B.val (R u)) x = (ρ x : ℂ) * ∫ y, q (x - y) * u y
  rw [hx.2]
  apply congrArg ((ρ x : ℂ) * ·)
  calc
    _ = ∫ y, q (x - y) * u y ∂μ := integral_congr_ae (hCompare (fun y ↦ q (x - y)))
    _ = ∫ y, (Ici a).indicator (fun y ↦ q (x - y) * u y) y :=
      (integral_indicator measurableSet_Ici).symm
    _ = _ := integral_congr_ae (hSupport (fun y ↦ q (x - y)))

end RiemannMasullo

end

end SupportedConvolution

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing SchwartzMap

namespace RiemannMasullo

noncomputable section

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "ℓ" => logSIdeleQuotientNorm F S
local notation "ν(" s ")" => intervalSobolevMeasure μJ ℓ 0 0 s
local notation "W(" s ")" => Lp ℂ 2 ν(s)
local notation "νR(" s ")" => intervalSobolevMeasure (volume : Measure ℝ) id 0 0 s
local notation "Zₛ" => sAdelePolarSubspace F S
local notation "d" => (Real.sqrt (Measure.real η univ) : ℂ)
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "include₁" =>
  (ContinuousMonoidHom.mk (Subgroup.subtype (MonoidHom.ker (sIdeleQuotientNorm F S)))
    continuous_subtype_val : J₁ →ₜ* Jₛ)
local notation "band(" B ")" =>
  Subtype (fun f : Zₛ ↦ Subtype.val f ∈ sLocalPWTests (F := F) (S := S) (T := S) le_rfl
    (sLocalPWProductRegion S B))

/-- The reflected logarithmic input and the weighted inverse-character output
lift make the upper-half-line convolution trace class from the closed
Chapter 11 level to the weighted quotient. The displayed generator value uses the raw
norm-one mass normalization on both sides of the real convolution. -/
public theorem exists_sLocalInvariantPW_upperHalflineTraceClassModel
    {s : ℝ} (hs : 0 ≤ s) (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) {B : ℝ} (hB : 0 < B)
    (Tmax : ℝ) (ρ : ℝ → ℝ) (hρm : Measurable ρ) (hρ : ∀ t, |ρ t| ≤ 1)
    (hρT : ∀ t, Tmax < t → ρ t = 0) :
    let level : Submodule ℂ (W(s)) := sLocalInvariantPWSobolev (F := F) (S := S) hs halfPos ω B
    letI : CompleteSpace level :=
      (show IsClosed (level : Set (W(s))) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
    let gen (f : band(B)) : level :=
      ⟨sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) halfPos ω f.val,
        sLocalInvariantPWSobolev_mem (F := F) (S := S) hs halfPos ω B f.val f.property⟩
    ∃ χ : PontryaginDual Jₛ,
      χ.comp include₁ = ω ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧
      ∀ q : 𝓢(ℝ, ℂ), ∃ K : level →L[ℂ] W(s),
        K ∈ traceClassOperators level (W(s)) ∧
        ∀ f : band(B), (K (gen f) : Jₛ → ℂ) =ᵐ[ν(s)] fun g ↦
          d⁻¹ * (χ g : ℂ)⁻¹ * ((ρ (ℓ g) : ℂ) *
            ∫ y, q (ℓ g - y) *
              (d * sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f.val.val) (-y))) := by
  intro level gen
  let : CompleteSpace level :=
    (show IsClosed (level : Set (W(s))) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
  obtain ⟨χ, T, hχ, hSection, _, hGen, hSupport⟩ :=
    exists_sLocalInvariantPW_reflectedLogInput (F := F) (S := S) hs τ hτ ω hB
  obtain ⟨L, hL⟩ := exists_sLocalWeightedLogCharacterLift τ hτ 0 0 s χ
  have hlog : Measurable ℓ :=
    Real.measurable_log.comp (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (continuousSIdeleQuotientNorm F S).continuous)).measurable
  have hlogMeasure : MeasurePreserving ℓ ν(s) ((η univ) • νR(s)) :=
    ⟨hlog, sLocalLogNorm_map_intervalSobolevMeasure τ hτ 0 0 s⟩
  let J : level →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) := T.comp level.subtypeL
  have hJ (u : level) : ∀ᵐ y : ℝ ∂volume, y < -Real.log B → J u y = 0 :=
    hSupport u.val u.property
  refine ⟨χ, hχ, hSection, fun q ↦ ?_⟩
  obtain ⟨U, hUTrace, _, hU⟩ :=
    exists_upperHalflineWeightedConvolutionOfSupportedInput s hs (-Real.log B) Tmax ρ hρm hρ hρT q J hJ
  let K : level →L[ℂ] W(s) := L.toContinuousLinearMap.comp U
  refine ⟨K, ?_, fun f ↦ ?_⟩
  · exact comp_left_mem_traceClass U hUTrace L.toContinuousLinearMap
  · let r (y : ℝ) : ℂ :=
      d * sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f.val.val) (-y)
    have hJGen : (J (gen f) : ℝ → ℂ) =ᵐ[volume] r := hGen f.val
    have hUReal : (U (gen f) : ℝ → ℂ) =ᵐ[νR(s)] fun x ↦
        (ρ x : ℂ) * ∫ y, q (x - y) * r y := by
      filter_upwards [hU (gen f)] with x hx
      exact hx.2.trans (congrArg ((ρ x : ℂ) * ·)
        (integral_congr_ae (hJGen.mono fun y hy ↦ congrArg (q (x - y) * ·) hy)))
    have hPull := hlogMeasure.quasiMeasurePreserving.ae_eq_comp
      (Measure.ae_smul_measure hUReal (η univ))
    filter_upwards [hL (U (gen f)), hPull] with g hg hg'
    change U (gen f) (ℓ g) = (ρ (ℓ g) : ℂ) * ∫ y, q (ℓ g - y) * r y at hg'
    change L (U (gen f)) g = _
    rw [hg, hg']

end

end RiemannMasullo


open MeasureTheory
open scoped Convolution FourierTransform SchwartzMap

namespace RiemannMasullo

noncomputable section

private theorem schwartz_bddAbove_range_norm (k : 𝓢(ℝ, ℂ)) :
    BddAbove (Set.range fun x : ℝ ↦ ‖k x‖) := by
  refine ⟨(SchwartzMap.seminorm ℝ 0 0) k, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact k.norm_le_seminorm ℝ x

private theorem integrable_fourier_schwartz_mul_convolution
    (k : 𝓢(ℝ, ℂ)) {p : ℝ → ℂ} (hp : Integrable p) :
    Integrable (𝓕 ((k : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] p)) := by
  have hk : Integrable (k : ℝ → ℂ) := k.integrable
  have hkF : Integrable (𝓕 (k : ℝ → ℂ)) := by
    rw [← SchwartzMap.fourier_coe k]
    exact (𝓕 k).integrable
  have hpF : Continuous (𝓕 p) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hp
  have heq :
      𝓕 ((k : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] p) =
        fun ξ ↦ 𝓕 (k : ℝ → ℂ) ξ * 𝓕 p ξ :=
    funext (Real.fourier_mul_convolution_eq hk hp)
  rw [heq]
  refine (hkF.norm.mul_const (∫ x, ‖p x‖)).mono'
    (hkF.aestronglyMeasurable.mul hpF.aestronglyMeasurable) (ae_of_all _ fun ξ ↦ ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (Real.norm_fourier_le_integral_norm p ξ) (norm_nonneg _)

/-- A Fourier phase relating two integrable inputs can be transferred to
their Schwartz convolution factors. The convolutions agree pointwise. -/
public theorem schwartz_mul_convolution_eq_of_fourier_phase
    (k q : 𝓢(ℝ, ℂ)) {m p r : ℝ → ℂ}
    (hp : Integrable p) (hr : Integrable r)
    (hP : 𝓕 p =ᵐ[volume] fun ξ ↦ m ξ * 𝓕 r ξ)
    (hQ : ∀ ξ, 𝓕 (q : ℝ → ℂ) ξ = m ξ * 𝓕 (k : ℝ → ℂ) ξ) :
    ((k : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] p) =
      ((q : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] r) := by
  let L := ContinuousLinearMap.mul ℂ ℂ
  let K := (k : ℝ → ℂ) ⋆[L] p
  let Q := (q : ℝ → ℂ) ⋆[L] r
  have hk : Integrable (k : ℝ → ℂ) := k.integrable
  have hq : Integrable (q : ℝ → ℂ) := q.integrable
  have hki : Integrable K := hk.integrable_convolution L hp
  have hqi : Integrable Q := hq.integrable_convolution L hr
  have hkc : Continuous K :=
    (schwartz_bddAbove_range_norm k).continuous_convolution_left_of_integrable L k.continuous hp
  have hqc : Continuous Q :=
    (schwartz_bddAbove_range_norm q).continuous_convolution_left_of_integrable L q.continuous hr
  have hF : 𝓕 K =ᵐ[volume] 𝓕 Q := by
    filter_upwards [hP] with ξ hx
    calc
      𝓕 K ξ = 𝓕 (k : ℝ → ℂ) ξ * 𝓕 p ξ := Real.fourier_mul_convolution_eq hk hp ξ
      _ = 𝓕 (q : ℝ → ℂ) ξ * 𝓕 r ξ := by
        rw [hx, hQ ξ]
        ring
      _ = 𝓕 Q ξ := (Real.fourier_mul_convolution_eq hq hr ξ).symm
  have hKF : Integrable (𝓕 K) := integrable_fourier_schwartz_mul_convolution k hp
  have hQF : Integrable (𝓕 Q) := hKF.congr hF
  have hinv : 𝓕⁻ (𝓕 K) = 𝓕⁻ (𝓕 Q) := by
    funext x
    simpa only [Real.fourierInv_eq_fourier_neg] using (Real.fourier_congr_ae hF (-x))
  change K = Q
  exact (hkc.fourierInv_fourier_eq hki hKF).symm.trans
    (hinv.trans (hqc.fourierInv_fourier_eq hqi hQF))

/-- A temperate symbol transfers an integrable input phase to a
Schwartz convolution kernel via the inverse Fourier transform. -/
public theorem exists_schwartz_mul_convolution_fourier_transfer
    (k : 𝓢(ℝ, ℂ)) {m p r : ℝ → ℂ} (hm : m.HasTemperateGrowth)
    (hp : Integrable p) (hr : Integrable r)
    (hP : 𝓕 p =ᵐ[volume] fun ξ ↦ m ξ * 𝓕 r ξ) :
    ∃ q : 𝓢(ℝ, ℂ), (∀ ξ, 𝓕 (q : ℝ → ℂ) ξ = m ξ * 𝓕 (k : ℝ → ℂ) ξ) ∧
      ((k : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] p) =
        ((q : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] r) := by
  let g := SchwartzMap.smulLeftCLM ℂ m (𝓕 k)
  let q : 𝓢(ℝ, ℂ) := 𝓕⁻ g
  have hFg : 𝓕 q = g := FourierTransform.fourier_fourierInv_eq g
  have hQ (ξ : ℝ) : 𝓕 (q : ℝ → ℂ) ξ = m ξ * 𝓕 (k : ℝ → ℂ) ξ := by
    rw [← SchwartzMap.fourier_coe q, hFg]
    change SchwartzMap.smulLeftCLM ℂ m (𝓕 k) ξ = _
    rw [SchwartzMap.smulLeftCLM_apply_apply hm, smul_eq_mul, SchwartzMap.fourier_coe k]
  exact ⟨q, hQ, schwartz_mul_convolution_eq_of_fourier_phase k q hp hr hP hQ⟩

end

end RiemannMasullo

section CheckedCovariance

noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "N" => sIdeleQuotientNorm F S
local notation "m" => continuousSIdeleQuotientNorm F S
local notation "Bₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "expLog" => fun r : ℝ ↦ positiveRealLogEquiv.symm (Multiplicative.ofAdd r)

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1
  instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1
  instSIdeleQuotientHaarMeasureSec1

local instance instQuotientConvolutionCovarianceNormOneMeasurable : MeasurableSpace J₁ := borel _

/-- Quotient convolution preserves the norm-one character of its input. -/
private theorem lcaConvolution_sLocal_normOne_covariant
    (φ u : Jₛ → ℂ) (ω : PontryaginDual J₁)
    (hu : ∀ (h : J₁) (g : Jₛ), u (h.val⁻¹ * g) = (ω h : ℂ) * u g)
    (h : J₁) (g : Jₛ) :
    lcaConvolution μJ φ u (h.val⁻¹ * g) =
      (ω h : ℂ) * lcaConvolution μJ φ u g := by
  unfold lcaConvolution
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  change φ y * u (y⁻¹ * (h.val⁻¹ * g)) = (ω h : ℂ) * (φ y * u (y⁻¹ * g))
  have harg : y⁻¹ * (h.val⁻¹ * g) = h.val⁻¹ * (y⁻¹ * g) := by
    with_unfolding_all exact mul_left_comm (y⁻¹ : Jₛ) (h.val⁻¹ : Jₛ) g
  rw [harg, hu h, mul_left_comm]

/-- Auxiliary result for Theorem 12.4.1.1, Step II, pp. 515–517.
The half-density theta convolution on the entire quotient is the real
logarithmic convolution multiplied by the inverse character of the output.
The chosen lift of the character is trivial on the norm section. -/
theorem sLocalTrace_homogeneousThetaHalfDensity_logConvolution_at
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (Φ : BruhatCompactSupport Jₛ) (ω : PontryaginDual J₁) (χ : PontryaginDual Jₛ)
    (hχ : ∀ h : J₁, χ h.val = ω h)
    (hχτ : ∀ t : ℝ≥0ˣ, χ (QuotientGroup.mk (τ t)) = 1)
    (v : Bₛ) (k : ℝ → ℂ) :
    let j (r : ℝ) : Jₛ := QuotientGroup.mk (τ (expLog r))
    let u := modulationWeight m (1 / 2) (sLocalHomogeneousAdelicThetaLinearMap F S ω v)
    (∀ r, k r = ∫ h : J₁, Φ.val (h.val * j r) * (ω h : ℂ) ∂η) →
    ∀ g : Jₛ, lcaConvolution μJ Φ.val u g =
      (χ g : ℂ)⁻¹ * ∫ r : ℝ, k r * u (j (logSIdeleQuotientNorm F S g - r)) := by
  intro j u hk
  let θ := sLocalHomogeneousAdelicThetaLinearMap F S ω v
  have huRep : u = fun g : Jₛ ↦ (Real.sqrt ((N g).val : ℝ) : ℂ) * θ g := by
    funext g
    with_unfolding_all change
      (((((N g).val : ℝ) ^ (1 / 2 : ℝ)) : ℝ) : ℂ) * θ g = _
    rw [Real.sqrt_eq_rpow]
  have hSection (x : ℝ) :
      lcaConvolution μJ Φ.val u (j x) = ∫ r : ℝ, k r * u (j (x - r)) := by
    rw [huRep]
    exact sLocalTrace_homogeneousThetaHalfDensity_logConvolution τ hτ Φ ω v k hk x
  let : Measure.IsHaarMeasure η := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have huω (h : J₁) (z : Jₛ) : u (h.val⁻¹ * z) = (ω h : ℂ) * u z := by
    have hn : N (h.val⁻¹ * z) = N z := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp h.property, inv_one, one_mul]
    simp only [huRep, hn]
    change (Real.sqrt ((N z).val : ℝ) : ℂ) *
      sLocalHomogeneousAdelicTheta F S η ω v (h.val⁻¹ * z) =
      (ω h : ℂ) * ((Real.sqrt ((N z).val : ℝ) : ℂ) * sLocalHomogeneousAdelicTheta F S η ω v z)
    rw [sLocalHomogeneousAdelicTheta_homogeneous F S η ω v h z, mul_left_comm]
  intro g
  let x := logSIdeleQuotientNorm F S g
  have hx : Multiplicative.ofAdd x = positiveRealLogEquiv (N g) :=
    Multiplicative.toAdd.injective (positiveRealLogEquiv_apply (N g)).symm
  have he : expLog x = N g :=
    (congrArg (fun z : Multiplicative ℝ ↦ positiveRealLogEquiv.symm z) hx).trans
      (positiveRealLogEquiv.symm_apply_apply _)
  have hNj : N (j x) = N g :=
    ((sIdeleQuotientNorm_mk F S (τ (expLog x))).trans (hτ (expLog x))).trans he
  let h : J₁ := ⟨j x / g, by
    rw [MonoidHom.mem_ker, map_div, hNj, div_self']⟩
  have hg : h.val⁻¹ * j x = g := by
    change (j x / g)⁻¹ * j x = g
    calc
      _ = (g / j x) * j x := congrArg (· * j x) (inv_div (a := j x) (b := g))
      _ = g := div_mul_cancel g (j x)
  have hPhase : (ω h : ℂ) = (χ g : ℂ)⁻¹ := by
    have hχj : χ (j x) = 1 := hχτ (expLog x)
    rw [← hχ h]
    change (χ (j x / g) : ℂ) = (χ g : ℂ)⁻¹
    rw [map_div, hχj, one_div, Circle.coe_inv]
  calc
    _ = lcaConvolution μJ Φ.val u (h.val⁻¹ * j x) :=
      congrArg (lcaConvolution μJ Φ.val u) hg.symm
    _ = (ω h : ℂ) * lcaConvolution μJ Φ.val u (j x) :=
      lcaConvolution_sLocal_normOne_covariant Φ.val u ω huω h (j x)
    _ = _ := by rw [hPhase, hSection x]

end RiemannMasullo

end

end CheckedCovariance

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Convolution FourierTransform NNReal NumberField.AdeleRing SchwartzMap

namespace RiemannMasullo

noncomputable section

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1
  instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1
  instSIdeleQuotientHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "N" => sIdeleQuotientNorm F S
local notation "modulus" => continuousSIdeleQuotientNorm F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "ℓ" => logSIdeleQuotientNorm F S
local notation "ν(" s ")" => intervalSobolevMeasure μJ ℓ 0 0 s
local notation "W(" s ")" => Lp ℂ 2 ν(s)
local notation "Zₛ" => sAdelePolarSubspace F S
local notation "d" => (Real.sqrt (Measure.real η univ) : ℂ)
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "include₁" =>
  (ContinuousMonoidHom.mk (Subgroup.subtype (MonoidHom.ker (sIdeleQuotientNorm F S)))
    continuous_subtype_val : J₁ →ₜ* Jₛ)
local notation "circleCoe" => (ContinuousMonoidHom.mk Circle.coeHom continuous_subtype_val : Circle →ₜ* ℂ)
local notation "chart(" χ ")" =>
  quasiCharacterNormTwist (G := Jₛ) N (IsProperMap.continuous (isProperMap_sIdeleQuotientNorm F S))
    (ContinuousMonoidHom.comp circleCoe χ)
local notation "expLog" => fun x : ℝ ↦ positiveRealLogEquiv.symm (Multiplicative.ofAdd x)
local notation "expUnit" => fun x : ℝ ↦ Units.mk0 (Real.toNNReal (Real.exp x)) (by positivity)

local instance instReflectedGeneratorComparisonNormOneMeasurable : MeasurableSpace J₁ :=
  borel _

local notation "Bₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))

/-- One Schwartz kernel converts the real convolution for every S-adelic test
into the convolution of its reflected Fourier-test profile. -/
private theorem exists_sLocalCutoff_reflectedConvolution_pointwise
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) (χ : PontryaginDual Jₛ) (hχ : χ.comp include₁ = ω)
    (hχτ : ∀ t, χ (QuotientGroup.mk (τ t)) = 1)
    (Φ : BruhatCompactSupport Jₛ) (k : 𝓢(ℝ, ℂ))
    (hk : ∀ x : ℝ, k x =
      ∫ h : J₁, Φ.val (h.val * QuotientGroup.mk (τ (expLog x))) * (ω h : ℂ) ∂η)
    (ρ : ℝ → ℝ) :
    ∃ q : 𝓢(ℝ, ℂ),
      (∀ ξ : ℝ, 𝓕 (q : ℝ → ℂ) ξ =
        sLocalRhoFactor (chart(χ) (sLocalRadialThetaCriticalParameter ξ)) * 𝓕 (k : ℝ → ℂ) ξ) ∧
      ∀ f : Bₛ,
        let u := modulationWeight modulus (1 / 2)
          (sLocalHomogeneousAdelicThetaLinearMap F S ω f)
        ∀ g : Jₛ, (ρ (ℓ g) : ℂ) * lcaConvolution μJ Φ.val u g =
          d⁻¹ * (χ g : ℂ)⁻¹ * ((ρ (ℓ g) : ℂ) *
            ∫ y, q (ℓ g - y) *
              (d * sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f) (-y))) := by
  classical
  let phase (ξ : ℝ) : ℂ := sLocalRhoFactor (chart(χ) (sLocalRadialThetaCriticalParameter ξ))
  have hphase : phase.HasTemperateGrowth := by
    have hz (ξ : ℝ) : sLocalRadialThetaCriticalParameter ξ =
        (1 / 2 : ℂ) + (ξ : ℂ) * (((-2 * Real.pi : ℝ) : ℂ) * Complex.I) := by
      unfold sLocalRadialThetaCriticalParameter
      push_cast
      ring
    have ht := sLocalRhoFactor_hasTemperateGrowth_criticalLine χ (-2 * Real.pi)
    change Function.HasTemperateGrowth
      (fun ξ : ℝ ↦ sLocalRhoFactor
        (chart(χ) ((1 / 2 : ℂ) + (ξ : ℂ) * (((-2 * Real.pi : ℝ) : ℂ) * Complex.I)))) at ht
    simpa only [phase, hz] using ht
  let ghat := SchwartzMap.smulLeftCLM ℂ phase (𝓕 k)
  let q : 𝓢(ℝ, ℂ) := 𝓕⁻ ghat
  have hFq : 𝓕 q = ghat := FourierTransform.fourier_fourierInv_eq ghat
  have hq (ξ : ℝ) : 𝓕 (q : ℝ → ℂ) ξ = phase ξ * 𝓕 (k : ℝ → ℂ) ξ := by
    rw [← SchwartzMap.fourier_coe q, hFq]
    change SchwartzMap.smulLeftCLM ℂ phase (𝓕 k) ξ = _
    rw [SchwartzMap.smulLeftCLM_apply_apply hphase, smul_eq_mul, SchwartzMap.fourier_coe k]
  have hexp (x : ℝ) : expLog x = expUnit x := by
    apply positiveRealLogEquiv.injective
    apply Multiplicative.toAdd.injective
    rw [show positiveRealLogEquiv (expLog x) = Multiplicative.ofAdd x from
      positiveRealLogEquiv.apply_symm_apply _, positiveRealLogEquiv_apply]
    change x = Real.log ((Real.exp x).toNNReal : ℝ)
    rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]
  let j (x : ℝ) : Jₛ := QuotientGroup.mk (τ (expLog x))
  have hχPoint (h : J₁) : χ h.val = ω h :=
    congrArg (fun ψ : PontryaginDual J₁ ↦ ψ h) hχ
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
  let : Measure.IsHaarMeasure η :=
    (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : IsFiniteMeasure η := CompactSpace.isFiniteMeasure
  have hd : d ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (measureReal_univ_pos (μ := η))).ne'
  refine ⟨q, hq, fun f ↦ ?_⟩
  intro u
  let p (x : ℝ) : ℂ := d * sLocalRadialThetaHalfDensity τ χ f x
  let r (x : ℝ) : ℂ := d * sLocalRadialThetaHalfDensity τ χ⁻¹
    (sAdeleSchwartzFourier f) (-x)
  have hp : Integrable p := (sLocalRadialThetaHalfDensity_integrable τ hτ χ f).const_mul d
  have hr : Integrable r :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable
      ((sLocalRadialThetaHalfDensity_integrable τ hτ χ⁻¹ (sAdeleSchwartzFourier f)).const_mul d)
  have hpr (ξ : ℝ) : 𝓕 p ξ = phase ξ * 𝓕 r ξ := by
    dsimp only [p, r]
    rw [realFourier_mul_const_left, realFourier_mul_const_left,
      sLocalRadialThetaHalfDensity_fourier_reflected_phase τ hτ χ f ξ]
    change d * (phase ξ * _) = phase ξ * (d * _)
    exact mul_left_comm _ _ _
  have hTransfer :
      ((k : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] p) =
        ((q : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] r) :=
    schwartz_mul_convolution_eq_of_fourier_phase k q hp hr (ae_of_all _ hpr) hq
  have hTransferRow (x : ℝ) :
      (∫ y, k y * p (x - y)) = ∫ y, q (x - y) * r y := by
    calc
      _ = ((k : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] p) x := rfl
      _ = ((q : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] r) x := congrFun hTransfer x
      _ = _ := convolution_mul_swap
  have hSection (x : ℝ) : p x = d * u (j x) := by
    apply congrArg (d * ·)
    have hn : ((N (j x)).val : ℝ) = Real.exp x := by
      change ((N (QuotientGroup.mk (τ (expLog x)))).val : ℝ) = _
      rw [sIdeleQuotientNorm_mk, hτ, hexp]
      exact Real.coe_toNNReal _ (Real.exp_pos x).le
    have hc : χ (QuotientGroup.mk (τ (expLog x))) = 1 := hχτ (expLog x)
    simp only [sLocalRadialThetaHalfDensity, ← hexp x, hχ, hc, Circle.coe_one, mul_one]
    with_unfolding_all change
      sLocalHomogeneousAdelicThetaLinearMap F S ω f (j x) * (Real.exp (x / 2) : ℂ) =
        (((((N (j x)).val : ℝ) ^ (1 / 2 : ℝ)) : ℝ) : ℂ) *
          sLocalHomogeneousAdelicThetaLinearMap F S ω f (j x)
    rw [hn, Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp, mul_one_div, mul_comm]
  have hIntegral (x : ℝ) :
      (∫ y, k y * p (x - y)) = d * ∫ y, k y * u (j (x - y)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    change k y * p (x - y) = d * (k y * u (j (x - y)))
    rw [hSection, mul_left_comm]
  have hPoint (z : Jₛ) :
      (ρ (ℓ z) : ℂ) * lcaConvolution μJ Φ.val u z =
        d⁻¹ * (χ z : ℂ)⁻¹ * ((ρ (ℓ z) : ℂ) * ∫ y, q (ℓ z - y) * r y) := by
    let c := ∫ y, k y * u (j (ℓ z - y))
    let cr := ∫ y, q (ℓ z - y) * r y
    have hcov : lcaConvolution μJ Φ.val u z = (χ z : ℂ)⁻¹ * c :=
      sLocalTrace_homogeneousThetaHalfDensity_logConvolution_at
        τ hτ Φ ω χ hχPoint hχτ f k hk z
    have hc : cr = d * c := (hTransferRow (ℓ z)).symm.trans (hIntegral (ℓ z))
    change (ρ (ℓ z) : ℂ) * lcaConvolution μJ Φ.val u z =
      d⁻¹ * (χ z : ℂ)⁻¹ * ((ρ (ℓ z) : ℂ) * cr)
    calc
      _ = (ρ (ℓ z) : ℂ) * ((χ z : ℂ)⁻¹ * c) := congrArg ((ρ (ℓ z) : ℂ) * ·) hcov
      _ = (d⁻¹ * d) * ((ρ (ℓ z) : ℂ) * ((χ z : ℂ)⁻¹ * c)) := by
        rw [inv_mul_cancel₀ hd, one_mul]
      _ = d⁻¹ * (χ z : ℂ)⁻¹ * ((ρ (ℓ z) : ℂ) * (d * c)) := by ring
      _ = _ := congrArg (fun w : ℂ ↦ d⁻¹ * (χ z : ℂ)⁻¹ * ((ρ (ℓ z) : ℂ) * w)) hc.symm
  exact hPoint

private theorem exists_sLocalTheta_cutoff_testAction_reflectedConvolution_of_apply
    {s : ℝ} (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) (χ : PontryaginDual Jₛ) (hχ : χ.comp include₁ = ω)
    (hχτ : ∀ t, χ (QuotientGroup.mk (τ t)) = 1)
    (Φ : BruhatCompactSupport Jₛ) (k : 𝓢(ℝ, ℂ))
    (hk : ∀ x : ℝ, k x =
      ∫ h : J₁, Φ.val (h.val * QuotientGroup.mk (τ (expLog x))) * (ω h : ℂ) ∂η)
    (ρ : ℝ → ℝ) (A M : W(s) →L[ℂ] W(s))
    (hA : ∀ v, (A v : Jₛ → ℂ) =ᵐ[μJ] lcaConvolution μJ Φ.val v)
    (hM : ∀ v, (M v : Jₛ → ℂ) =ᵐ[ν(s)] fun z ↦ (ρ (ℓ z) : ℂ) * v z) :
    ∃ q : 𝓢(ℝ, ℂ),
      (∀ ξ : ℝ, 𝓕 (q : ℝ → ℂ) ξ =
        sLocalRhoFactor (chart(χ) (sLocalRadialThetaCriticalParameter ξ)) * 𝓕 (k : ℝ → ℂ) ξ) ∧
      ∀ (f : Bₛ) (v : W(s)),
        ((v : Jₛ → ℂ) =ᵐ[μJ] modulationWeight modulus (1 / 2)
          (sLocalHomogeneousAdelicThetaLinearMap F S ω f)) →
        (M (A v) : Jₛ → ℂ) =ᵐ[ν(s)] fun g ↦
          d⁻¹ * (χ g : ℂ)⁻¹ * ((ρ (ℓ g) : ℂ) *
            ∫ y, q (ℓ g - y) *
              (d * sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f) (-y))) := by
  obtain ⟨q, hq, hPoint⟩ := exists_sLocalCutoff_reflectedConvolution_pointwise τ hτ ω χ hχ hχτ Φ k hk ρ
  refine ⟨q, hq, fun f v hv ↦ ?_⟩
  let u := modulationWeight modulus (1 / 2) (sLocalHomogeneousAdelicThetaLinearMap F S ω f)
  have hRep (z : Jₛ) : lcaConvolution μJ Φ.val v z = lcaConvolution μJ Φ.val u z := by
    unfold lcaConvolution
    have hShift : QuasiMeasurePreserving (fun y : Jₛ ↦ y⁻¹ * z) μJ μJ :=
      (quasiMeasurePreserving_mul_right μJ z).comp (quasiMeasurePreserving_inv μJ)
    exact integral_congr_ae ((hShift.ae_eq_comp hv).mono
      fun y hy ↦ congrArg (Φ.val y * ·) hy)
  have hν : ν(s) ≪ μJ := withDensity_absolutelyContinuous _ _
  filter_upwards [hM (A v), hν.ae_eq ((hA v).trans (ae_of_all _ hRep))] with z hz hAz
  change M (A v) z = (ρ (ℓ z) : ℂ) * A v z at hz
  exact hz.trans ((congrArg ((ρ (ℓ z) : ℂ) * ·) hAz).trans (hPoint f z))


/-- A single real Schwartz kernel transfers the whole fixed character's
half-density polar theta generators to their reflected Fourier-test inputs.
The resulting formula is for the actual quotient test action followed by
the radial cutoff, before projection. -/
public theorem exists_sLocalPWTheta_cutoff_testAction_reflectedConvolution
    {s : ℝ} (hs : 0 ≤ s) (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) (χ : PontryaginDual Jₛ) (hχ : χ.comp include₁ = ω)
    (hχτ : ∀ t, χ (QuotientGroup.mk (τ t)) = 1)
    (Φ : BruhatCompactSupport Jₛ) (k : 𝓢(ℝ, ℂ))
    (hk : ∀ x : ℝ, k x =
      ∫ h : J₁, Φ.val (h.val * QuotientGroup.mk (τ (expLog x))) * (ω h : ℂ) ∂η)
    (ρ : ℝ → ℝ) (hρm : Measurable (ρ ∘ ℓ)) (hρ : ∀ t, |ρ t| ≤ 1) :
    let A : W(s) →L[ℂ] W(s) := hardySobolevTestAction μJ modulus 0 0 s le_rfl hs Φ
    let M : W(s) →L[ℂ] W(s) := lpCutoffMultiplier ν(s) (ρ ∘ ℓ) hρm (fun x ↦ hρ (ℓ x))
    ∃ q : 𝓢(ℝ, ℂ), ∀ f : Zₛ,
      let v := sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) halfPos ω f
      (M (A v) : Jₛ → ℂ) =ᵐ[ν(s)] fun g ↦
        d⁻¹ * (χ g : ℂ)⁻¹ * ((ρ (ℓ g) : ℂ) *
          ∫ y, q (ℓ g - y) *
            (d * sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f.val) (-y))) := by
  intro A M
  obtain ⟨q, -, hCompare⟩ := exists_sLocalTheta_cutoff_testAction_reflectedConvolution_of_apply
    τ hτ ω χ hχ hχτ Φ k hk ρ A M
    (hardySobolevTestAction_apply μJ modulus 0 0 s le_rfl hs Φ)
    (lpCutoffMultiplier_apply ν(s) (ρ ∘ ℓ) hρm (fun x ↦ hρ (ℓ x)))
  refine ⟨q, fun f ↦ ?_⟩
  intro v
  exact hCompare f.val v
    (sLocalPWThetaSobolevMap_apply (F := F) (S := S) (s := s) halfPos ω f)

/-- The quotient test action followed by the radial cutoff has one reflected
convolution kernel on every full-band generator. Its Fourier transform uses
the critical-line phase of the supplied character. -/
public theorem exists_sLocalFullPWTheta_cutoff_testAction_reflectedConvolution
    {s : ℝ} (hs : 0 ≤ s) (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) (χ : PontryaginDual Jₛ) (hχ : χ.comp include₁ = ω)
    (hχτ : ∀ t, χ (QuotientGroup.mk (τ t)) = 1)
    (Φ : BruhatCompactSupport Jₛ) (k : 𝓢(ℝ, ℂ))
    (hk : ∀ x : ℝ, k x =
      ∫ h : J₁, Φ.val (h.val * QuotientGroup.mk (τ (expLog x))) * (ω h : ℂ) ∂η)
    (ρ : ℝ → ℝ) (hρm : Measurable (ρ ∘ ℓ)) (hρ : ∀ t, |ρ t| ≤ 1) :
    let A : W(s) →L[ℂ] W(s) := hardySobolevTestAction μJ modulus 0 0 s le_rfl hs Φ
    let M : W(s) →L[ℂ] W(s) := lpCutoffMultiplier ν(s) (ρ ∘ ℓ) hρm (fun x ↦ hρ (ℓ x))
    ∃ q : 𝓢(ℝ, ℂ),
      (∀ ξ : ℝ, 𝓕 (q : ℝ → ℂ) ξ =
        sLocalRhoFactor (chart(χ) (sLocalRadialThetaCriticalParameter ξ)) * 𝓕 (k : ℝ → ℂ) ξ) ∧
      ∀ f : Bₛ,
        let v := Isolated.sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) halfPos ω f
        (M (A v) : Jₛ → ℂ) =ᵐ[ν(s)] fun g ↦
          d⁻¹ * (χ g : ℂ)⁻¹ * ((ρ (ℓ g) : ℂ) *
            ∫ y, q (ℓ g - y) *
              (d * sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f) (-y))) := by
  intro A M
  obtain ⟨q, hq, hCompare⟩ := exists_sLocalTheta_cutoff_testAction_reflectedConvolution_of_apply
    τ hτ ω χ hχ hχτ Φ k hk ρ A M
    (hardySobolevTestAction_apply μJ modulus 0 0 s le_rfl hs Φ)
    (lpCutoffMultiplier_apply ν(s) (ρ ∘ ℓ) hρm (fun x ↦ hρ (ℓ x)))
  refine ⟨q, hq, fun f ↦ ?_⟩
  intro v
  exact hCompare f v
    (Isolated.sLocalFullPWThetaSobolevMap_apply (F := F) (S := S) (s := s) halfPos ω f)

local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "fullBand(" ω "," B ")" =>
  Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos ω B
local notation "bandTests(" B ")" =>
  sLocalPWTests (F := F) (S := S) (T := S) le_rfl (sLocalPWProductRegion S B)
local notation "fullGen(" ω ")" =>
  Isolated.sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := 0) halfPos ω

/-- At order zero the actual quotient upper cutoff on the full band factors
through a rectangular trace-class real convolution using the same reflected
input and physical output lift. -/
public theorem exists_sLocalFullPW_upperCutoff_factor_orderZero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) (χ : PontryaginDual Jₛ) (hχ : χ.comp include₁ = ω)
    (hχτ : ∀ t, χ (QuotientGroup.mk (τ t)) = 1) (B : ℝ)
    (T : W(0) →L[ℂ] FlatL2) (L : FlatL2 →ₗᵢ[ℂ] W(0))
    (hTGen : sLocalFullReflectedGenAE τ ω χ T)
    (hSupport : ∀ u ∈ fullBand(ω,B), ∀ᵐ y : ℝ ∂volume, y < -Real.log B → T u y = 0)
    (hL : ∀ v, (L v : Jₛ → ℂ) =ᵐ[ν(0)] fun g ↦ d⁻¹ * (χ g : ℂ)⁻¹ * v (ℓ g))
    (Φ : BruhatCompactSupport Jₛ) (Tmax : ℝ) (ρ : ℝ → ℝ) (hρm : Measurable ρ)
    (hρ : ∀ x, |ρ x| ≤ 1) (hρT : ∀ x, Tmax < x → ρ x = 0) :
    let V : Submodule ℂ (W(0)) := fullBand(ω,B)
    letI : CompleteSpace V := (show IsClosed (V : Set (W(0))) from
      Submodule.isClosed_topologicalClosure _).completeSpace_coe
    let hρLog : Measurable (ρ ∘ ℓ) := hρm.comp (Real.measurable_log.comp
      (NNReal.continuous_coe.comp
        (Units.continuous_val.comp (continuousSIdeleQuotientNorm F S).continuous)).measurable)
    let A : W(0) →L[ℂ] W(0) := hardySobolevTestAction μJ modulus 0 0 0 le_rfl le_rfl Φ
    let M : W(0) →L[ℂ] W(0) := lpCutoffMultiplier ν(0) (ρ ∘ ℓ) hρLog (fun g ↦ hρ (ℓ g))
    ∃ (k q : 𝓢(ℝ, ℂ)) (K : V →L[ℂ] FlatL2),
      (∀ x : ℝ, k x =
        ∫ h : J₁, Φ.val (h.val * QuotientGroup.mk (τ (expLog x))) * (ω h : ℂ) ∂η) ∧
      (∀ ξ : ℝ, 𝓕 (q : ℝ → ℂ) ξ =
        sLocalRhoFactor (chart(χ) (sLocalRadialThetaCriticalParameter ξ)) * 𝓕 (k : ℝ → ℂ) ξ) ∧
      K ∈ traceClassOperators V FlatL2 ∧
      M.comp (A.comp V.subtypeL) = L.toContinuousLinearMap.comp K ∧
      ∀ v : V, ∀ᵐ x : ℝ ∂volume,
        K v x = (ρ x : ℂ) * ∫ y, q (x - y) * T v.val y := by
  intro V hρLog A M
  let : CompleteSpace V := (show IsClosed (V : Set (W(0))) from
    Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let quotient : Iₛ →ₜ* Jₛ :=
    ⟨QuotientGroup.mk' (sProjectedDiagonal F S), QuotientGroup.continuous_mk⟩
  let σ := quotient.comp τ
  have hσ : RightInverse σ N := fun t ↦ (sIdeleQuotientNorm_mk F S (τ t)).trans (hτ t)
  obtain ⟨k, _, hk⟩ := SLocalRadialAction.exists_normOneCharacterLogTest F S σ hσ Φ ω
  obtain ⟨q, hq, hActual⟩ := exists_sLocalFullPWTheta_cutoff_testAction_reflectedConvolution
    (s := 0) le_rfl τ hτ ω χ hχ hχτ Φ k hk ρ hρLog hρ
  let J : V →L[ℂ] FlatL2 := T.comp V.subtypeL
  have hJ (v : V) : ∀ᵐ y : ℝ ∂volume, y < -Real.log B → J v y = 0 :=
    hSupport v.val v.property
  have hνR : intervalSobolevMeasure (volume : Measure ℝ) id 0 0 0 = volume := by
    have h (x : ℝ) : intervalSobolevDensity 0 0 0 x = 1 := by simp [intervalSobolevDensity]
    change (volume : Measure ℝ).withDensity
      (fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 0 x)) = _
    simp only [h, ENNReal.ofReal_one]
    change (volume : Measure ℝ).withDensity (1 : ℝ → ℝ≥0∞) = volume
    exact withDensity_one
  let Factor (μ : Measure ℝ) : Prop := ∃ K : V →L[ℂ] Lp ℂ 2 μ,
    K ∈ traceClassOperators V (Lp ℂ 2 μ) ∧
    (∀ R : Lp ℂ 2 μ →L[ℂ] V, IsNuclearOperator (R.comp K)) ∧
    ∀ v : V, ∀ᵐ x : ℝ ∂μ,
      Integrable (fun y ↦ ((ρ x : ℂ) * q (x - y)) * J v y) volume ∧
      K v x = (ρ x : ℂ) * ∫ y, q (x - y) * J v y
  have transfer (μ : Measure ℝ) (hμ : μ = volume) (h : Factor μ) : Factor volume := by
    subst μ
    exact h
  obtain ⟨K, hK, _, hKrow⟩ := transfer _ hνR
    (exists_upperHalflineWeightedConvolutionOfSupportedInput 0 le_rfl (-Real.log B) Tmax
      ρ hρm hρ hρT q J hJ)
  let C : V →L[ℂ] W(0) := M.comp (A.comp V.subtypeL)
  let Z : V →L[ℂ] W(0) := L.toContinuousLinearMap.comp K
  let gen (f : Bₛ) (hf : f ∈ bandTests(B)) : V :=
    ⟨fullGen(ω) f, Submodule.le_topologicalClosure _ (Submodule.mem_map.mpr ⟨f, hf, rfl⟩)⟩
  have hlog : Measurable ℓ := Real.measurable_log.comp
    (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (continuousSIdeleQuotientNorm F S).continuous)).measurable
  have hLogMeasure : MeasurePreserving ℓ ν(0) ((η univ) • (volume : Measure ℝ)) :=
    ⟨hlog, by simpa only [hνR] using sLocalLogNorm_map_intervalSobolevMeasure τ hτ 0 0 0⟩
  have hGen (f : Bₛ) (hf : f ∈ bandTests(B)) : C (gen f hf) = Z (gen f hf) := by
    let v := gen f hf
    let r (y : ℝ) : ℂ := d * sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f) (-y)
    have hJrep : (J v : ℝ → ℂ) =ᵐ[volume] r := hTGen f
    have hKrep : (K v : ℝ → ℂ) =ᵐ[volume] fun x ↦ (ρ x : ℂ) * ∫ y, q (x - y) * r y := by
      filter_upwards [hKrow v] with x hx
      exact hx.2.trans (congrArg ((ρ x : ℂ) * ·)
        (integral_congr_ae (hJrep.mono fun y hy ↦ congrArg (q (x - y) * ·) hy)))
    have hPull := hLogMeasure.quasiMeasurePreserving.ae_eq_comp
      (Measure.ae_smul_measure hKrep (η univ))
    apply Lp.ext
    filter_upwards [hActual f, hL (K v), hPull] with g hAg hLg hKg
    change K v (ℓ g) = (ρ (ℓ g) : ℂ) * ∫ y, q (ℓ g - y) * r y at hKg
    change M (A (fullGen(ω) f)) g = L (K v) g
    rw [hAg, hLg, hKg]
  let P : W(0) →L[ℂ] V := V.orthogonalProjectionOnto
  let D : W(0) →L[ℂ] W(0) := (C - Z).comp P
  have hKer : V ≤ D.ker := by
    change ((bandTests(B)).map (fullGen(ω))).topologicalClosure ≤ D.ker
    refine Submodule.topologicalClosure_minimal _ ?_ D.isClosed_ker
    rintro _ ⟨f, hf, rfl⟩
    have hv : P (fullGen(ω) f) = gen f hf :=
      V.orthogonalProjectionOnto_mem_subspace_eq_self (gen f hf)
    apply LinearMap.mem_ker.mpr
    change (C - Z) (P (fullGen(ω) f)) = 0
    rw [hv, ContinuousLinearMap.sub_apply, hGen f hf, sub_self]
  have hEq : C = Z := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : D v.val = 0 := LinearMap.mem_ker.mp (hKer v.property)
    change (C - Z) (P v.val) = 0 at hv
    rw [show P v.val = v from V.orthogonalProjectionOnto_mem_subspace_eq_self v,
      ContinuousLinearMap.sub_apply] at hv
    exact sub_eq_zero.mp hv
  exact ⟨k, q, K, hk, hq, hK, hEq, fun v ↦ (hKrow v).mono fun _ h ↦ h.2⟩

end

end RiemannMasullo


open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing SchwartzMap

namespace RiemannMasullo

noncomputable section

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1
  instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1
  instSIdeleQuotientHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "modulus" => continuousSIdeleQuotientNorm F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "ℓ" => logSIdeleQuotientNorm F S
local notation "ν(" s ")" => intervalSobolevMeasure μJ ℓ 0 0 s
local notation "W(" s ")" => Lp ℂ 2 ν(s)
local notation "Zₛ" => sAdelePolarSubspace F S
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "band(" B ")" =>
  Subtype (fun f : Zₛ ↦ Subtype.val f ∈ sLocalPWTests (F := F) (S := S) (T := S) le_rfl
    (sLocalPWProductRegion S B))

local instance instActualCutoffCompressionNormOneMeasurable : MeasurableSpace J₁ := borel _

/-- Paper: Theorem 12.4.1.1, Step II, pp. 515–517. At a fixed positive band,
the actual test action followed by an upper spatial cutoff is trace class
from the half-density weighted theta level into the weighted quotient.
Deviation: Fix one norm-one character and the logarithmic Sobolev weight
with base interval `{0}`. This treats nuclearity at fixed cutoff parameters. -/
public theorem sLocalInvariantPW_upperCutoff_testAction_mem_traceClass
    {s : ℝ} (hs : 0 ≤ s) (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) {B : ℝ} (hB : 0 < B)
    (Φ : BruhatCompactSupport Jₛ) (Tmax : ℝ) (ρ : ℝ → ℝ) (hρm : Measurable ρ)
    (hρ : ∀ x, |ρ x| ≤ 1) (hρT : ∀ x, Tmax < x → ρ x = 0) :
    let level : Submodule ℂ (W(s)) := sLocalInvariantPWSobolev (F := F) (S := S) hs halfPos ω B
    letI : CompleteSpace level :=
      (show IsClosed (level : Set (W(s))) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
    let hρLog : Measurable (ρ ∘ ℓ) := hρm.comp (Real.measurable_log.comp
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (continuousSIdeleQuotientNorm F S).continuous)).measurable)
    let A : W(s) →L[ℂ] W(s) := hardySobolevTestAction μJ modulus 0 0 s le_rfl hs Φ
    let M : W(s) →L[ℂ] W(s) := lpCutoffMultiplier ν(s) (ρ ∘ ℓ) hρLog (fun g ↦ hρ (ℓ g))
    M.comp (A.comp level.subtypeL) ∈ traceClassOperators level (W(s)) := by
  intro level hρLog A M
  let : CompleteSpace level :=
    (show IsClosed (level : Set (W(s))) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let projection : W(s) →L[ℂ] level := level.orthogonalProjectionOnto
  let quotient : Iₛ →ₜ* Jₛ := ⟨QuotientGroup.mk' (sProjectedDiagonal F S), QuotientGroup.continuous_mk⟩
  let σ := quotient.comp τ
  have hσ : RightInverse σ (sIdeleQuotientNorm F S) := fun t ↦
    (sIdeleQuotientNorm_mk F S (τ t)).trans (hτ t)
  obtain ⟨k, _, hk⟩ := SLocalRadialAction.exists_normOneCharacterLogTest F S σ hσ Φ ω
  obtain ⟨χ, hχ, hχτ, hModel⟩ :=
    exists_sLocalInvariantPW_upperHalflineTraceClassModel (F := F) (S := S) hs τ hτ ω hB
      Tmax ρ hρm hρ hρT
  obtain ⟨q, hActual⟩ :=
    exists_sLocalPWTheta_cutoff_testAction_reflectedConvolution (F := F) (S := S)
      hs τ hτ ω χ hχ hχτ Φ k hk ρ hρLog hρ
  obtain ⟨K, hK, hKOnGen⟩ := hModel q
  let C : level →L[ℂ] W(s) := M.comp (A.comp level.subtypeL)
  let gen (f : band(B)) : level :=
    ⟨sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) halfPos ω f.val,
      sLocalInvariantPWSobolev_mem (F := F) (S := S) hs halfPos ω B f.val f.property⟩
  have hGen (f : band(B)) : K (gen f) = C (gen f) := by
    apply Lp.ext
    exact (hKOnGen f).trans (hActual f.val).symm
  have hProj (u : level) : projection u.val = u :=
    level.orthogonalProjectionOnto_mem_subspace_eq_self u
  let D : W(s) →L[ℂ] W(s) := (K - C).comp projection
  have hKer : level ≤ D.ker := by
    change sLocalInvariantPWSobolev (F := F) (S := S) hs halfPos ω B ≤ D.ker
    unfold sLocalInvariantPWSobolev
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) D.isClosed_ker
    rintro _ ⟨f, rfl⟩
    apply LinearMap.mem_ker.mpr
    change (K - C) (projection (gen f).val) = 0
    rw [hProj (gen f), sub_apply, hGen f, sub_self]
  have hEq : K = C := by
    apply ContinuousLinearMap.ext
    intro u
    have hu : D u.val = 0 := LinearMap.mem_ker.mp (hKer u.property)
    change (K - C) (projection u.val) = 0 at hu
    rw [hProj u, sub_apply] at hu
    exact sub_eq_zero.mp hu
  change C ∈ traceClassOperators level (W(s))
  simpa only [hEq] using hK


/-- Paper: Theorem 12.4.1.1, Step II, pp. 515–517. At a fixed positive band,
the actual test action followed by an upper spatial cutoff has nuclear
orthogonal compression to the half-density weighted theta level.
Deviation: Fix one norm-one character and the logarithmic Sobolev weight
with base interval `{0}`. This treats nuclearity at fixed cutoff parameters. -/
public theorem isNuclearOperator_sLocalInvariantPW_upperCutoff_testAction
    {s : ℝ} (hs : 0 ≤ s) (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) {B : ℝ} (hB : 0 < B)
    (Φ : BruhatCompactSupport Jₛ) (Tmax : ℝ) (ρ : ℝ → ℝ) (hρm : Measurable ρ)
    (hρ : ∀ x, |ρ x| ≤ 1) (hρT : ∀ x, Tmax < x → ρ x = 0) :
    let level : Submodule ℂ (W(s)) := sLocalInvariantPWSobolev (F := F) (S := S) hs halfPos ω B
    let projection : W(s) →L[ℂ] level := by
      letI : CompleteSpace level :=
        (show IsClosed (level : Set (W(s))) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
      exact level.orthogonalProjectionOnto
    let hρLog : Measurable (ρ ∘ ℓ) := hρm.comp (Real.measurable_log.comp
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (continuousSIdeleQuotientNorm F S).continuous)).measurable)
    let A : W(s) →L[ℂ] W(s) := hardySobolevTestAction μJ modulus 0 0 s le_rfl hs Φ
    let M : W(s) →L[ℂ] W(s) := lpCutoffMultiplier ν(s) (ρ ∘ ℓ) hρLog (fun g ↦ hρ (ℓ g))
    IsNuclearOperator (projection.comp (M.comp (A.comp level.subtypeL))) := by
  intro level projection hρLog A M
  let : CompleteSpace level :=
    (show IsClosed (level : Set (W(s))) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hT : M.comp (A.comp level.subtypeL) ∈ traceClassOperators level (W(s)) :=
    sLocalInvariantPW_upperCutoff_testAction_mem_traceClass
      (F := F) (S := S) hs τ hτ ω hB Φ Tmax ρ hρm hρ hρT
  exact (mem_traceClassOperators_iff_isNuclearOperator _).mp
    (comp_left_mem_traceClass _ hT projection)

end

end RiemannMasullo


open Filter MeasureTheory Set
open scoped Topology

namespace RiemannMasullo

noncomputable section

private theorem directLowerFloorLp_norm_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ, L2.inner_def]
  simp_rw [inner_self_eq_norm_sq_to_K]
  norm_cast

private theorem tendsto_L2_quotientLowerMask
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (ℓ : X → ℝ) (hℓ : Measurable ℓ)
    (S : ℝ → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hS : ∀ b f, (S b f : X → ℂ) =ᵐ[μ] (ℓ ⁻¹' Ici b).indicator (f : X → ℂ))
    (f : Lp ℂ 2 μ) :
    Tendsto (fun b ↦ S b f) atBot (𝓝 f) := by
  let D (b : ℝ) := (ℓ ⁻¹' Iio b).indicator (fun x : X ↦ ‖f x‖ ^ 2)
  have hSq (b : ℝ) : ‖S b f - f‖ ^ 2 = ∫ x, D b x ∂μ := by
    rw [directLowerFloorLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (S b f) f, hS b f] with x hx hmask
    change (S b f - f) x = S b f x - f x at hx
    rw [hx, hmask]
    rcases le_or_gt b (ℓ x) with h | h
    · have hk : x ∈ ℓ ⁻¹' Ici b := h
      have hd : x ∉ ℓ ⁻¹' Iio b := not_lt_of_ge h
      simp [D, indicator_of_mem hk, indicator_of_notMem hd]
    · have hk : x ∉ ℓ ⁻¹' Ici b := not_le_of_gt h
      have hd : x ∈ ℓ ⁻¹' Iio b := h
      simp [D, indicator_of_notMem hk, indicator_of_mem hd]
  have hInt : Integrable (fun x ↦ ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hDCT : Tendsto (fun b ↦ ∫ x, D b x ∂μ) atBot (𝓝 (∫ _ : X, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖f x‖ ^ 2)
      ?_ ?_ hInt ?_
    · exact .of_forall fun b ↦ hInt.aestronglyMeasurable.indicator (hℓ measurableSet_Iio)
    · refine .of_forall fun b ↦ .of_forall fun x ↦ ?_
      by_cases hx : x ∈ ℓ ⁻¹' Iio b
      · simp only [D, indicator_of_mem hx, Real.norm_of_nonneg (sq_nonneg _), le_refl]
      · simp only [D, indicator_of_notMem hx, norm_zero, sq_nonneg]
    · refine .of_forall fun x ↦ ?_
      have hZero : Tendsto (fun _ : ℝ ↦ (0 : ℝ)) atBot (𝓝 0) := tendsto_const_nhds
      refine hZero.congr' ((eventually_le_atBot (ℓ x)).mono fun b hb ↦ ?_)
      exact (indicator_of_notMem (show x ∉ ℓ ⁻¹' Iio b from not_lt_of_ge hb) _).symm
  have hTail : Tendsto (fun b ↦ ∫ x, D b x ∂μ) atBot (𝓝 0) := by
    simpa only [integral_zero] using hDCT
  have hSqrt : Tendsto (fun b ↦ √(∫ x, D b x ∂μ)) atBot (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      (Real.continuous_sqrt.tendsto 0).comp hTail
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (hSqrt.congr fun b ↦ ?_)
  rw [← hSq b, Real.sqrt_sq (norm_nonneg _)]

private theorem exists_atBot_traceClass_comp_left
    {D H : Type*}
    [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Z : traceClassOperators D H) (S : ℝ → H →L[ℂ] H)
    (hS : ∀ f : H, Tendsto (fun b ↦ S b f) atBot (𝓝 f)) :
    ∃ Zb : ℝ → traceClassOperators D H,
      (∀ b, (Zb b).val = (S b).comp Z.val) ∧
      Tendsto (fun b ↦ schattenNorm (Zb b - Z)) atBot (𝓝 0) := by
  have hmem (b : ℝ) : (S b).comp Z.val ∈ traceClassOperators D H := by
    obtain ⟨_, h, _⟩ := tendsto_schattenNorm_comp_left Z (fun _ ↦ S b) (S b)
      (fun _ ↦ tendsto_const_nhds)
    exact h
  let Zb (b : ℝ) : traceClassOperators D H := ⟨_, hmem b⟩
  refine ⟨Zb, fun _ ↦ rfl, Filter.tendsto_iff_seq_tendsto.mpr ?_⟩
  intro B hB
  let I := ContinuousLinearMap.id ℂ H
  obtain ⟨_, hlim, hconv⟩ := tendsto_schattenNorm_comp_left Z (fun j ↦ S (B j)) I
    (fun f ↦ (hS f).comp hB)
  have hI : (⟨I.comp Z.val, hlim⟩ : traceClassOperators D H) = Z :=
    Subtype.ext (ContinuousLinearMap.id_comp _)
  rw [hI] at hconv
  exact hconv.congr fun _ ↦ rfl

/-- Once the upper-cutoff operator is trace class before compression, removing
the lower cutoff converges in trace norm after any fixed bounded projection.
The lower cutoff is multiplication by the preimage of the closed half-line
under the logarithmic coordinate. -/
public theorem tendsto_schattenNorm_quotientLowerFloor_of_upperTraceClass
    {D X : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
    (μ : Measure X) (ℓ : X → ℝ) (hℓ : Measurable ℓ)
    (Z : traceClassOperators D (Lp ℂ 2 μ))
    (P : Lp ℂ 2 μ →L[ℂ] D) (A : D →L[ℂ] Lp ℂ 2 μ)
    (ρ : X → ℝ) (hρm : Measurable ρ) (hρ : ∀ x, |ρ x| ≤ 1)
    (hZ : Z.val = (lpCutoffMultiplier μ ρ hρm hρ).comp A) :
    let ρb (b : ℝ) : X → ℝ := (ℓ ⁻¹' Ici b).indicator ρ
    let hρbm (b : ℝ) : Measurable (ρb b) := hρm.indicator (hℓ measurableSet_Ici)
    let hρb (b : ℝ) (x : X) : |ρb b x| ≤ 1 := by
      by_cases hx : x ∈ ℓ ⁻¹' Ici b
      · simpa only [ρb, indicator_of_mem hx] using hρ x
      · simp only [ρb, indicator_of_notMem hx, abs_zero, zero_le_one]
    let M (b : ℝ) := lpCutoffMultiplier μ (ρb b) (hρbm b) (hρb b)
    ∃ (K : ℝ → traceClassOperators D D) (K₀ : traceClassOperators D D),
      (∀ b, (K b).val = P.comp ((M b).comp A)) ∧
      K₀.val = P.comp ((lpCutoffMultiplier μ ρ hρm hρ).comp A) ∧
      Tendsto (fun b ↦ schattenNorm (K b - K₀)) atBot (𝓝 0) := by
  intro ρb hρbm hρb M
  let e (b : ℝ) : X → ℝ := (ℓ ⁻¹' Ici b).indicator (fun _ ↦ 1)
  have hem (b : ℝ) : Measurable (e b) := measurable_const.indicator (hℓ measurableSet_Ici)
  have heb (b : ℝ) (x : X) : |e b x| ≤ 1 := by
    by_cases hx : x ∈ ℓ ⁻¹' Ici b <;> simp [e, hx]
  let S (b : ℝ) := lpCutoffMultiplier μ (e b) (hem b) (heb b)
  have hS (b : ℝ) (f : Lp ℂ 2 μ) :
      (S b f : X → ℂ) =ᵐ[μ] (ℓ ⁻¹' Ici b).indicator (f : X → ℂ) := by
    filter_upwards [lpCutoffMultiplier_apply μ (e b) (hem b) (heb b) f] with x hx
    rw [hx]
    by_cases hex : x ∈ ℓ ⁻¹' Ici b <;> simp [e, hex]
  obtain ⟨Zb, hZb, hlim⟩ := exists_atBot_traceClass_comp_left Z S
    (tendsto_L2_quotientLowerMask μ ℓ hℓ S hS)
  obtain ⟨K, K₀, hK, hK₀, hKlim⟩ := tendsto_schattenNorm_rectangularSandwich
    Zb Z (ContinuousLinearMap.id ℂ D) P hlim
  refine ⟨K, K₀, ?_, ?_, hKlim⟩
  · intro b
    rw [hK b, ContinuousLinearMap.comp_id, hZb b]
    apply congrArg (fun T : D →L[ℂ] Lp ℂ 2 μ ↦ P.comp T)
    apply ContinuousLinearMap.ext
    intro u
    change S b (Z.val u) = M b (A u)
    apply Lp.ext
    have hUpper : (Z.val u : X → ℂ) =ᵐ[μ] fun x ↦ (ρ x : ℂ) * (A u) x := by
      rw [hZ]
      exact lpCutoffMultiplier_apply μ ρ hρm hρ (A u)
    filter_upwards [hS b (Z.val u), hUpper, lpCutoffMultiplier_apply μ (ρb b) (hρbm b) (hρb b) (A u)]
      with x hxs hxu hxm
    change S b (Z.val u) x = M b (A u) x
    rw [hxs, hxm]
    by_cases hx : x ∈ ℓ ⁻¹' Ici b
    · simpa only [ρb, indicator_of_mem hx] using hxu
    · simp only [ρb, indicator_of_notMem hx, Complex.ofReal_zero, zero_mul]
  · rw [hK₀, ContinuousLinearMap.comp_id, hZ]

end

end RiemannMasullo


open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing SchwartzMap Topology

namespace RiemannMasullo

noncomputable section

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1
  instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1
  instSIdeleQuotientHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "modulus" => continuousSIdeleQuotientNorm F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "ℓ" => logSIdeleQuotientNorm F S
local notation "ν(" s ")" => intervalSobolevMeasure μJ ℓ 0 0 s
local notation "W(" s ")" => Lp ℂ 2 ν(s)
local notation "νR(" s ")" => intervalSobolevMeasure (volume : Measure ℝ) id 0 0 s
local notation "Zₛ" => sAdelePolarSubspace F S
local notation "d" => (Real.sqrt (Measure.real η univ) : ℂ)
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "band(" B ")" =>
  Subtype (fun f : Zₛ ↦ Subtype.val f ∈ sLocalPWTests (F := F) (S := S) (T := S) le_rfl
    (sLocalPWProductRegion S B))

local instance instActualLowerFloorNormOneMeasurable : MeasurableSpace J₁ := borel _

/-- Paper: Theorem 12.4.1.1, p. 514 n. 2 and pp. 516–517, Step II.
On a fixed positive band, the actual weighted test-action compression
converges in trace norm as the lower log-norm floor tends to minus infinity.
Deviation: Fix one norm-one character, the half-density, and the
Sobolev weight with base interval `{0}`. The upper log cutoff stays fixed. -/
public theorem exists_sLocalInvariantPW_testAction_lowerFloor_traceNorm
    {s : ℝ} (hs : 0 ≤ s) (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) {B : ℝ} (hB : 0 < B)
    (Φ : BruhatCompactSupport Jₛ) (Tmax : ℝ) (ρ : ℝ → ℝ) (hρm : Measurable ρ)
    (hρ : ∀ x, |ρ x| ≤ 1) (hρT : ∀ x, Tmax < x → ρ x = 0) :
    let level : Submodule ℂ (W(s)) := sLocalInvariantPWSobolev (F := F) (S := S) hs halfPos ω B
    letI : CompleteSpace level := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    let projection : W(s) →L[ℂ] level := level.orthogonalProjectionOnto
    let hlog : Measurable ℓ := Real.measurable_log.comp (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (continuousSIdeleQuotientNorm F S).continuous)).measurable
    let A : level →L[ℂ] W(s) :=
      (hardySobolevTestAction μJ modulus 0 0 s le_rfl hs Φ).comp level.subtypeL
    let M₀ := lpCutoffMultiplier ν(s) (ρ ∘ ℓ) (hρm.comp hlog) (fun g ↦ hρ (ℓ g))
    let ρb (b : ℝ) : Jₛ → ℝ := (ℓ ⁻¹' Ici b).indicator (ρ ∘ ℓ)
    let Mb (b : ℝ) : W(s) →L[ℂ] W(s) := lpCutoffMultiplier ν(s) (ρb b)
      ((hρm.comp hlog).indicator (hlog measurableSet_Ici)) (fun g ↦ by
        by_cases hg : g ∈ ℓ ⁻¹' Ici b
        · simpa only [ρb, indicator_of_mem hg, Function.comp_apply] using hρ (ℓ g)
        · simp only [ρb, indicator_of_notMem hg, abs_zero, zero_le_one])
    ∃ (K : ℝ → traceClassOperators level level) (K₀ : traceClassOperators level level),
      (∀ b, (K b).val = projection.comp ((Mb b).comp A)) ∧
      K₀.val = projection.comp (M₀.comp A) ∧
      Tendsto (fun b ↦ schattenNorm (K b - K₀)) atBot (𝓝 0) := by
  intro level projection hlog A M₀ ρb Mb
  let : CompleteSpace level :=
    (show IsClosed (level : Set (W(s))) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hUpper : M₀.comp A ∈ traceClassOperators level (W(s)) :=
    sLocalInvariantPW_upperCutoff_testAction_mem_traceClass
      (F := F) (S := S) hs τ hτ ω hB Φ Tmax ρ hρm hρ hρT
  let Z : traceClassOperators level (W(s)) := ⟨M₀.comp A, hUpper⟩
  exact tendsto_schattenNorm_quotientLowerFloor_of_upperTraceClass
    ν(s) ℓ hlog Z projection A (ρ ∘ ℓ) (hρm.comp hlog) (fun g ↦ hρ (ℓ g)) rfl

end

end RiemannMasullo
