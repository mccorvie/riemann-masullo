module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b
public import RiemannMasullo.Ch11_ShellStructure.Sec1b
import all RiemannMasullo.Ch11_ShellStructure.Sec1b

/-! # Orbital Markushevich bases on the 0-line

Masullo, §11.2 before §11.2.1, pp. 483–487.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "W(" s ")" => CompactIntervalSobolev μ𝔽 logNorm 0 0 s
local notation "W'(" s ")" => CompactIntervalSobolev μ𝔽 logNorm 0 0 s true
local notation "μ'(" s ")" => (μ𝔽).withDensity (fun g ↦
  ENNReal.ofReal (intervalSobolevDensity 0 0 (s) (logNorm g))⁻¹)
local notation "hI" => (le_rfl (a := (0 : ℝ)))
local notation "H(" a ", " hs ")" => globalThetaSobolev F a hI hs
local notation "j(" a ", " hs ")" => globalThetaSobolevInclusion F a hI hs
local notation "ρ(" hs ")" => hardySobolevTranslation μ𝔽 m𝔽 0 0 _ hI hs
local notation "Wω(" hs ", " ω ")" =>
  actionIsotype ((ρ(hs)).comp (ideleClassNorm F).ker.subtype) ω
local notation "restriction" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
local notation "ℬ₀" => ↥(adelePolarSubspace F)
local notation "jet(" χ ", " t ", " m ")" => spectralZeroJet χ 0 t m
local notation "frequency(" t ")" => ((t : ℝ) : ℂ) * Complex.I
local notation "q(" v ")" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v))

-- (11.2.0.1) is spectralSobolevPairing at the interval [0, 0].
-- (11.2.0.2) recalls the quotient operator globalThetaPrincipalValue.

local notation "pvTest(" S ", " f ")" =>
  (⟨adelePrincipalValue F S (f : ℬ₀).val, adelePrincipalValue_mem_polarSubspace S f⟩ : ℬ₀)
local notation "theta(" f ")" =>
  (Submodule.Quotient.mk (f : ℬ₀) : GlobalPolarFreeThetaSpace F)

-- TODO(paper-gap): The proof of density uses §10.2.1's passage from the
-- test-space Mellin image to an annihilator in the completed norm.
-- The cited Theorem 10.2.1.1 assumes s > 1. For 0 ≤ s ≤ 1, density in degree
-- 2 descends through the dense inclusion of weighted spaces by log-norm cutoff.

/-- Paper: Proposition 11.2.0.1, p. 484. The polar-free theta classes are norm
dense in the full global Sobolev space on the 0-line. -/
theorem denseRange_globalTheta_zeroLine {s : ℝ} (hs : 0 ≤ s) :
    DenseRange (fun u : GlobalPolarFreeThetaSpace F ↦ (j(0, hs) u : W(s))) := by sorry

/-- Paper: Definition 5.3.1.2 and Lemma 5.3.1.3, p. 241, for the proof of
Proposition 11.2.0.1(1), p. 484. The principal value at one finite place `v`, on theta
functions: theta of `PV_v f` is theta of `f` minus the normalized average over the local
integer units `u` of its translates by the idele class of `(π u)⁻¹` at `v`. On a test this is
`finitePlacePrincipalValue_spec` at `v`. The sum over `Fˣ` and the integral over the compact
unit group may be exchanged because the theta series converges absolutely and locally
uniformly. -/
private theorem globalThetaPrincipalValue_sobolevBound_formula (v : V)
    (π : (v.adicCompletion F)ˣ) (_hπ : Valued.v.IsUniformizer π.val) (f : ℬ₀) (g : C𝔽) :
    adelicTheta (adelePrincipalValue F {v} f.val) g =
      adelicTheta f.val g - ((finiteLocalMultiplicativeTamagawaMeasure F v).real
          ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ))⁻¹ *
        ∫ u in ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ),
          adelicTheta f.val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ * g)
          ∂(finiteLocalMultiplicativeTamagawaMeasure F v) := by
  sorry

/-- Cauchy–Schwarz for lower Lebesgue integrals: the square of the integral is at most the
total mass times the integral of the square. -/
private theorem globalThetaPrincipalValue_sobolevBound_average_cs {X : Type*}
    [MeasurableSpace X] (ν : Measure X) (f : X → ENNReal) (hf : AEMeasurable f ν) :
    (∫⁻ x, f x ∂ν) ^ 2 ≤ ν univ * ∫⁻ x, f x ^ 2 ∂ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hf
    (aemeasurable_const (b := (1 : ENNReal)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  calc (∫⁻ x, f x ∂ν) ^ 2
      ≤ ((∫⁻ x, f x ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) * ν univ ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ zero_le h 2
    _ = ν univ * ∫⁻ x, f x ^ 2 ∂ν := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (ν univ ^ (1 / 2 : ℝ)),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num
      rw [mul_comm]

/-- Abstract form of the bound for the unit average: on a group with a left-invariant measure
and a weight that each translate by `τ u`, `u ∈ U`, changes by at most the factor `M`, the
normalized average of the translates has weighted L² mass at most `M` times that of the
function. -/
private theorem globalThetaPrincipalValue_sobolevBound_average_abstract
    {G X : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G]
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (w : G → ENNReal) (hw : Measurable w)
    (μX : Measure X) (U : Set X) (hU : MeasurableSet U) (hUfin : μX U ≠ ⊤)
    (τ : X → G) (hτ : Continuous τ) (M : ENNReal)
    (hM : ∀ u ∈ U, ∀ g, w ((τ u)⁻¹ * g) ≤ M * w g)
    (φ : G → ℂ) (hφ : Continuous φ) :
    AEStronglyMeasurable (fun g ↦ (μX.real U)⁻¹ * ∫ u in U, φ (τ u * g) ∂μX)
        (μ.withDensity w) ∧
      ∫⁻ g, ‖(μX.real U)⁻¹ * ∫ u in U, φ (τ u * g) ∂μX‖ₑ ^ 2 ∂(μ.withDensity w) ≤
        M * ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂(μ.withDensity w) := by
  haveI : IsFiniteMeasure (μX.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hUfin⟩
  set c : ℝ := μX.real U with hcdef
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hcU : μX U = ENNReal.ofReal c := (ENNReal.ofReal_toReal hUfin).symm
  have hsm : StronglyMeasurable (fun p : G × X ↦ φ (τ p.2 * p.1)) :=
    (hφ.comp ((hτ.comp continuous_snd).mul continuous_fst)).stronglyMeasurable
  have hAsm : StronglyMeasurable (fun g ↦ ((c⁻¹ : ℝ) : ℂ) * ∫ u in U, φ (τ u * g) ∂μX) :=
    (hsm.integral_prod_right' (ν := μX.restrict U)).const_mul _
  refine ⟨hAsm.aestronglyMeasurable, ?_⟩
  let F : X → G → ENNReal := fun u g ↦ ‖φ (τ u * g)‖ₑ ^ 2
  have hF : Measurable (Function.uncurry F) :=
    ((hφ.comp ((hτ.comp continuous_fst).mul continuous_snd)).measurable.eNorm).pow_const 2
  -- Pointwise: the square of the average is at most the average of the squares.
  have hpt (g : G) : ‖((c⁻¹ : ℝ) : ℂ) * ∫ u in U, φ (τ u * g) ∂μX‖ₑ ^ 2 ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ u in U, F u g ∂μX := by
    have h1 : ‖((c⁻¹ : ℝ) : ℂ) * ∫ u in U, φ (τ u * g) ∂μX‖ₑ ≤
        ENNReal.ofReal c⁻¹ * ∫⁻ u in U, ‖φ (τ u * g)‖ₑ ∂μX := by
      rw [eNorm_mul]
      refine mul_le_mul' (le_of_eq ?_) (eNorm_integral_le_lintegral_eNorm _)
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hc0)]
    have h2 := globalThetaPrincipalValue_sobolevBound_average_cs (μX.restrict U)
      (fun u ↦ ‖φ (τ u * g)‖ₑ)
      ((hφ.comp (hτ.mul continuous_const)).measurable.eNorm.aemeasurable)
    rw [Measure.restrict_apply_univ, hcU] at h2
    have h3 : ENNReal.ofReal c⁻¹ ^ 2 * ENNReal.ofReal c ≤ ENNReal.ofReal c⁻¹ := by
      rcases hc0.eq_or_lt with h | h
      · rw [← h]; simp
      · rw [← ENNReal.ofReal_pow (inv_nonneg.mpr hc0), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        field_simp
    calc ‖((c⁻¹ : ℝ) : ℂ) * ∫ u in U, φ (τ u * g) ∂μX‖ₑ ^ 2
        ≤ (ENNReal.ofReal c⁻¹ * ∫⁻ u in U, ‖φ (τ u * g)‖ₑ ∂μX) ^ 2 :=
          pow_le_pow_left₀ zero_le h1 2
      _ = ENNReal.ofReal c⁻¹ ^ 2 * (∫⁻ u in U, ‖φ (τ u * g)‖ₑ ∂μX) ^ 2 := mul_pow _ _ _
      _ ≤ ENNReal.ofReal c⁻¹ ^ 2 * (ENNReal.ofReal c * ∫⁻ u in U, F u g ∂μX) :=
          mul_le_mul' le_rfl h2
      _ = (ENNReal.ofReal c⁻¹ ^ 2 * ENNReal.ofReal c) * ∫⁻ u in U, F u g ∂μX := by ring
      _ ≤ ENNReal.ofReal c⁻¹ * ∫⁻ u in U, F u g ∂μX := mul_le_mul' h3 le_rfl
  -- Each translate changes the weighted mass by at most `M`.
  have htr (u : X) (hu : u ∈ U) : ∫⁻ g, w g * F u g ∂μ ≤ M * ∫⁻ g, w g * ‖φ g‖ₑ ^ 2 ∂μ := by
    have he : ∫⁻ g, w g * F u g ∂μ = ∫⁻ g, w ((τ u)⁻¹ * g) * ‖φ g‖ₑ ^ 2 ∂μ := by
      rw [← lintegral_mul_left_eq_self (fun g ↦ w ((τ u)⁻¹ * g) * ‖φ g‖ₑ ^ 2) (τ u)]
      simp only [F, inv_mul_cancel_left]
    rw [he, ← lintegral_const_mul M (f := fun g ↦ w g * ‖φ g‖ₑ ^ 2)
      (hw.mul (hφ.measurable.eNorm.pow_const 2))]
    exact lintegral_mono fun g ↦ (mul_le_mul' (hM u hu g) le_rfl).trans_eq (mul_assoc _ _ _)
  have hwm : Measurable fun g ↦ ‖((c⁻¹ : ℝ) : ℂ) * ∫ u in U, φ (τ u * g) ∂μX‖ₑ ^ 2 :=
    (hAsm.measurable.eNorm).pow_const 2
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hwm,
    lintegral_withDensity_eq_lintegral_mul _ hw (hφ.measurable.eNorm.pow_const 2)]
  calc ∫⁻ g, (w * fun g ↦ ‖((c⁻¹ : ℝ) : ℂ) * ∫ u in U, φ (τ u * g) ∂μX‖ₑ ^ 2) g ∂μ
      ≤ ∫⁻ g, w g * (ENNReal.ofReal c⁻¹ * ∫⁻ u in U, F u g ∂μX) ∂μ :=
        lintegral_mono fun g ↦ mul_le_mul' le_rfl (hpt g)
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ u in U, ∫⁻ g, w g * F u g ∂μ ∂μX := by
        have hm2 : Measurable (Function.uncurry fun g u ↦ w g * F u g) :=
          (hw.comp measurable_fst).mul (hF.comp measurable_swap)
        have hin (g : G) : w g * (ENNReal.ofReal c⁻¹ * ∫⁻ u in U, F u g ∂μX) =
            ENNReal.ofReal c⁻¹ * ∫⁻ u in U, w g * F u g ∂μX := by
          rw [lintegral_const_mul (w g) (f := fun u ↦ F u g)
            (hF.comp (measurable_id.prodMk measurable_const))]
          ring
        rw [lintegral_congr hin, lintegral_const_mul (ENNReal.ofReal c⁻¹)
          (f := fun g ↦ ∫⁻ u in U, w g * F u g ∂μX) hm2.lintegral_prod_right',
          lintegral_lintegral_swap (f := fun g u ↦ w g * F u g) (μ := μ) (ν := μX.restrict U)
            hm2.aemeasurable]
    _ ≤ ENNReal.ofReal c⁻¹ * ∫⁻ u in U, M * ∫⁻ g, w g * ‖φ g‖ₑ ^ 2 ∂μ ∂μX :=
        mul_le_mul' le_rfl (setLIntegral_mono' hU htr)
    _ = (ENNReal.ofReal c⁻¹ * ENNReal.ofReal c) * (M * ∫⁻ g, w g * ‖φ g‖ₑ ^ 2 ∂μ) := by
        rw [setLIntegral_const, hcU]
        ring
    _ ≤ M * ∫⁻ g, (w * fun g ↦ ‖φ g‖ₑ ^ 2) g ∂μ := by
        refine (mul_le_mul' ?_ le_rfl).trans_eq (one_mul _)
        rcases hc0.eq_or_lt with h | h
        · rw [← h]; simp
        · rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ h.ne', ENNReal.ofReal_one]

/-- Paper: for the proof of Proposition 11.2.0.1(1), p. 484. The normalized average over the
local integer units at `v` of the translates by the classes of `(π u)⁻¹` is bounded on the
weighted L² space of the 0-line, uniformly on continuous square-integrable functions. Each
such translate moves the idelic norm by the fixed factor `q_v`, so it changes the Sobolev
weight `(1 + log² ‖g‖)^{s/2}` by at most a constant factor (Peetre's inequality). The bound
for the average then follows from Minkowski's integral inequality. -/
private theorem globalThetaPrincipalValue_sobolevBound_average (v : V)
    (π : (v.adicCompletion F)ˣ) {s : ℝ} (_hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : C𝔽 → ℂ, Continuous φ →
      MemLp φ 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) →
      let A : C𝔽 → ℂ := fun g ↦ ((finiteLocalMultiplicativeTamagawaMeasure F v).real
          ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ))⁻¹ *
        ∫ u in ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ),
          φ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ * g)
          ∂(finiteLocalMultiplicativeTamagawaMeasure F v)
      MemLp A 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) ∧
        eLpNorm A 2 ((μ𝔽).withDensity fun g ↦
            ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) ≤
          ENNReal.ofReal C * eLpNorm φ 2 ((μ𝔽).withDensity fun g ↦
            ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) := by
  letI : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  haveI : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let U : Set (v.adicCompletion F)ˣ :=
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ)
  have hUo : IsOpen U := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hUc : IsCompact U := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  haveI := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) v
  have hUfin : finiteLocalMultiplicativeTamagawaMeasure F v U ≠ ⊤ := hUc.measure_ne_top
  let τ : (v.adicCompletion F)ˣ → C𝔽 := fun u ↦ IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹
  have hτ : Continuous τ :=
    (continuous_ideleClass_ofAdicCompletion F v).comp ((continuous_const.mul continuous_id).inv)
  let w : C𝔽 → ENNReal := fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))
  have hw : Measurable w := by
    refine (Measurable.ennreal_ofReal ?_)
    simp only [intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero, max_self, one_mul]
    have hlog : Continuous (fun g : C𝔽 ↦ logNorm g) :=
      Real.continuousOn_log.comp_continuous
        (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous))
        fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    exact ((continuous_const.add (hlog.pow 2)).rpow_const fun g ↦ Or.inl (by
      change (1 : ℝ) + (logNorm g) ^ 2 ≠ 0
      positivity)).measurable
  let c₀ : ℝ := Real.log ‖(π : v.adicCompletion F)‖
  let M : ℝ := (2 * (1 + c₀ ^ 2)) ^ (s / 2)
  have hnormu (u : (v.adicCompletion F)ˣ) (hu : u ∈ U) : ‖(u : v.adicCompletion F)‖ = 1 := by
    have h1 : ‖(u : v.adicCompletion F)‖ ≤ 1 :=
      (Valued.toNormedField.norm_le_one_iff).mpr hu.1
    have h2 : ‖((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ ≤ 1 :=
      (Valued.toNormedField.norm_le_one_iff).mpr hu.2
    have h3 : ‖(u : v.adicCompletion F)‖ * ‖((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ = 1 := by
      rw [← norm_mul, Units.mul_inv, norm_one]
    nlinarith [norm_nonneg (u : v.adicCompletion F),
      norm_nonneg ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)]
  have hπ0 : 0 < ‖(π : v.adicCompletion F)‖ := norm_pos_iff.mpr π.ne_zero
  have hM : ∀ u ∈ U, ∀ g, w ((τ u)⁻¹ * g) ≤ ENNReal.ofReal M * w g := by
    intro u hu g
    have hlog : logNorm ((τ u)⁻¹ * g) = c₀ + logNorm g := by
      have hn : (((ideleClassNorm F ((τ u)⁻¹ * g)).val : ℝ≥0) : ℝ) =
          ‖(π : v.adicCompletion F)‖ * (((ideleClassNorm F g).val : ℝ≥0) : ℝ) := by
        simp only [τ, map_mul, map_inv, inv_inv, ideleClassNorm_ofAdicCompletion, Units.val_mul,
          NNReal.coe_mul]
        change ‖(π : v.adicCompletion F)‖ * ‖(u : v.adicCompletion F)‖ * _ = _
        rw [hnormu u hu, mul_one]
      change Real.log _ = Real.log ‖(π : v.adicCompletion F)‖ + Real.log _
      rw [hn, Real.log_mul hπ0.ne' (NNReal.coe_pos.mpr (Units.zero_lt _)).ne']
    simp only [w, hlog, intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero, max_self,
      one_mul]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
    nlinarith [sq_nonneg (c₀ - logNorm g), sq_nonneg (c₀ * logNorm g)]
  refine ⟨Real.sqrt M, Real.sqrt_nonneg _, fun φ hφ hφm ↦ ?_⟩
  intro A
  obtain ⟨hAsm, hAle⟩ := globalThetaPrincipalValue_sobolevBound_average_abstract μ𝔽 w hw
    (finiteLocalMultiplicativeTamagawaMeasure F v) U hUo.measurableSet hUfin τ hτ
    (ENNReal.ofReal M) hM φ hφ
  have hrpow (f : C𝔽 → ℂ) (hf : AEStronglyMeasurable f ((μ𝔽).withDensity w)) :
      eLpNorm f 2 ((μ𝔽).withDensity w) =
      (∫⁻ g, ‖f g‖ₑ ^ 2 ∂((μ𝔽).withDensity w)) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hbound : eLpNorm (fun g ↦ ((finiteLocalMultiplicativeTamagawaMeasure F v).real U)⁻¹ *
        ∫ u in U, φ (τ u * g) ∂(finiteLocalMultiplicativeTamagawaMeasure F v)) 2
        ((μ𝔽).withDensity w) ≤ ENNReal.ofReal (Real.sqrt M) * eLpNorm φ 2 ((μ𝔽).withDensity w) := by
    rw [hrpow _ hAsm, hrpow _ hφm.aestronglyMeasurable, Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg (by positivity)
      (by norm_num), ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    exact ENNReal.rpow_le_rpow hAle (by norm_num)
  exact ⟨hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφm), hbound⟩

/-- The principal value at a single finite place is bounded in the norm of the unweighted
global theta completion: by the formula on theta functions and the bound for the unit average. -/
private theorem globalThetaPrincipalValue_sobolevBound_single (v : V) {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℬ₀,
      ‖j(0, hs) (theta(pvTest({v}, f)))‖ ≤ C * ‖j(0, hs) (theta(f))‖ := by
  obtain ⟨π₀, hπ₀⟩ := (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v.adicCompletion F)ˣ := Units.mk0 π₀ hπ₀.ne_zero
  obtain ⟨C, hC, hA⟩ := globalThetaPrincipalValue_sobolevBound_average v π hs
  -- The norm of an unweighted theta class is the weighted L² norm of its theta function.
  have hθ (h : ℬ₀) : ((j(0, hs) (theta(h)) : W(s)) : C𝔽 → ℂ) =ᵐ[(μ𝔽).withDensity fun g ↦
      ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))] (adelicTheta h.val : C𝔽 → ℂ) :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (((existsUnique_globalThetaSobolevEmbedding (F := F) 0 0 0 s hI hs).exists.choose_spec.2
        h).trans (Filter.EventuallyEq.of_eq (modulationWeight_zero m𝔽 _)))
  have hmem (h : ℬ₀) : MemLp (adelicTheta h.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) :=
    (Lp.memLp _).ae_eq (hθ h)
  have hnorm (h : ℬ₀) : ‖j(0, hs) (theta(h))‖ =
      (eLpNorm (adelicTheta h.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g)))).toReal :=
    (Lp.norm_def _).trans (congrArg ENNReal.toReal (eLpNorm_congr_ae (hθ h)))
  refine ⟨1 + C, by linarith, fun f ↦ ?_⟩
  have hA' := hA _ (adelicTheta f.val).continuous (hmem f)
  let A : C𝔽 → ℂ := fun g ↦ ((finiteLocalMultiplicativeTamagawaMeasure F v).real
          ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ))⁻¹ *
        ∫ u in ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ),
          adelicTheta f.val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ * g)
          ∂(finiteLocalMultiplicativeTamagawaMeasure F v)
  have hAm : MemLp A 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) := hA'.1
  have hAle : eLpNorm A 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) ≤
      ENNReal.ofReal C * eLpNorm (adelicTheta f.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) := hA'.2
  have hpv : (adelicTheta (pvTest({v}, f)).val : C𝔽 → ℂ) =
      fun g ↦ adelicTheta f.val g - A g :=
    funext fun g ↦ globalThetaPrincipalValue_sobolevBound_formula v π hπ₀ f g
  have hfin := (hmem f).eLpNorm_ne_top
  have hle : eLpNorm (fun g ↦ adelicTheta f.val g - A g) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) ≤
      eLpNorm (adelicTheta f.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) +
        ENNReal.ofReal C * eLpNorm (adelicTheta f.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) :=
    (eLpNorm_sub_le (by norm_num : (1 : ENNReal) ≤ 2)).trans
      (add_le_add le_rfl hAle)
  have hfin' : ENNReal.ofReal C * eLpNorm (adelicTheta f.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hreal : (eLpNorm (adelicTheta f.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g))) +
      ENNReal.ofReal C * eLpNorm (adelicTheta f.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g)))).toReal =
      (1 + C) * (eLpNorm (adelicTheta f.val : C𝔽 → ℂ) 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g)))).toReal := by
    rw [ENNReal.toReal_add hfin hfin', ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]
    ring
  refine (hnorm _).trans_le ?_
  refine (congrArg (fun φ : C𝔽 → ℂ ↦ (eLpNorm φ 2 ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm g)))).toReal) hpv).trans_le ?_
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin, hfin'⟩) hle).trans_eq ?_
  exact hreal.trans (congrArg ((1 + C) * ·) (hnorm f).symm)

/-- Paper: Proposition 11.2.0.1(1), p. 484. The principal-value operator
is bounded in the norm induced on unweighted theta classes.
Deviation: The operator uses finite places as in (11.2.0.2) and the global
norm (10.1.1.6), since (10.1.1.5) is S-local. -/
theorem globalThetaPrincipalValue_sobolevBound (S : Finset V) {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℬ₀,
      ‖j(0, hs) (theta(pvTest(S, f)))‖ ≤ C * ‖j(0, hs) (theta(f))‖ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, zero_le_one, fun f ↦ ?_⟩
    have h : pvTest(∅, f) = f := by
      refine Subtype.ext ?_
      change adelePrincipalValue F ∅ f.val = f.val
      rw [sLocalUncutCarving_empty_PV]
      rfl
    rw [h, one_mul]
  | insert v T hvT ih =>
    obtain ⟨K₁, hK₁, h₁⟩ := ih
    have hsingle := globalThetaPrincipalValue_sobolevBound_single (F := F) v hs
    have hK₂ := hsingle.choose_spec.1
    have h₂ := hsingle.choose_spec.2
    refine ⟨K₁ * hsingle.choose, mul_nonneg hK₁ hK₂, fun f ↦ ?_⟩
    have hcomp : pvTest(insert v T, f) = pvTest(T, pvTest({v}, f)) := by
      refine Subtype.ext ?_
      change adelePrincipalValue F (insert v T) f.val =
        adelePrincipalValue F T (adelePrincipalValue F {v} f.val)
      rw [sLocalCutoffCarving_antitone_PV (Finset.subset_insert v T),
        Finset.insert_sdiff_cancel hvT]
      rfl
    calc ‖j(0, hs) (theta(pvTest(insert v T, f)))‖
        = ‖j(0, hs) (theta(pvTest(T, pvTest({v}, f))))‖ :=
          congrArg (fun h : ℬ₀ ↦ ‖j(0, hs) (theta(h))‖) hcomp
      _ ≤ K₁ * ‖j(0, hs) (theta(pvTest({v}, f)))‖ := h₁ _
      _ ≤ K₁ * (hsingle.choose * ‖j(0, hs) (theta(f))‖) := mul_le_mul_of_nonneg_left (h₂ f) hK₁
      _ = K₁ * hsingle.choose * ‖j(0, hs) (theta(f))‖ := (mul_assoc _ _ _).symm

/-- Paper: Proposition 11.2.0.1(2) and (11.2.0.4), pp. 484–485.
The principal value has a unique bounded extension to the global theta completion.
Deviation: Continuity, without closed range, is stated here for every
nonnegative degree and every norm twist as in the paragraph before the proposition. -/
theorem existsUnique_globalThetaSobolevPrincipalValue (S : Finset V) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    ∃! P : H(a, hs) →L[ℂ] H(a, hs), ∀ f : ℬ₀,
      P (j(a, hs) (theta(f))) = j(a, hs) (theta(pvTest(S, f))) := by sorry

variable (F) in
/-- Paper: (11.2.0.4), p. 484. The completed principal-value map is the
continuous extension of the operator on adelic tests. -/
def globalThetaSobolevPrincipalValue (S : Finset V) (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    H(a, hs) →L[ℂ] H(a, hs) :=
  (existsUnique_globalThetaSobolevPrincipalValue S a hs).exists.choose

local notation "P(" S ", " a ", " hs ")" => globalThetaSobolevPrincipalValue F S a hs

/-- Paper: (11.2.0.4), p. 484. The extended operator agrees with its test formula
on each polar-free theta class. -/
theorem globalThetaSobolevPrincipalValue_apply (S : Finset V) (a : ℝ) {s : ℝ}
    (hs : 0 ≤ s) (f : ℬ₀) :
    P(S, a, hs) (j(a, hs) (theta(f))) = j(a, hs) (theta(pvTest(S, f))) :=
  (existsUnique_globalThetaSobolevPrincipalValue S a hs).exists.choose_spec f

/-- Paper: Lead-in to (11.2.0.3), p. 484. The extended principal value is injective.
Deviation: The inverse on its range can be discontinuous. -/
theorem globalThetaSobolevPrincipalValue_injective (S : Finset V) (a : ℝ) {s : ℝ}
    (hs : 0 ≤ s) : Injective (P(S, a, hs)) := by sorry

private theorem globalThetaSobolevPrincipalValue_equivariant_val_eq {A B : Type*}
    (θ : A → B) (pv : A → A) {x x' y y' : A} (hx : x = x') (hy : y = y')
    (h : θ (pv x') = θ y') : θ (pv x) = θ y := by
  subst hx hy
  exact h

private theorem globalThetaSobolevPrincipalValue_equivariant_ker_eq {R M N : Type*}
    {instR : CommRing R} {instM : AddCommGroup M} {instModM : Module R M}
    {instN : AddCommGroup N} {instModN : Module R N}
    {θ : @LinearMap R R _ _ (RingHom.id R) M N instM.toAddCommMonoid instN.toAddCommMonoid
      instModM instModN}
    {x y : M}
    (h : @Submodule.Quotient.mk R M instR.toRing instM instModM (LinearMap.ker θ) x =
         @Submodule.Quotient.mk R M instR.toRing instM instModM (LinearMap.ker θ) y) :
    θ x = θ y := by
  let _ := instR; let _ := instM; let _ := instModM; let _ := instN; let _ := instModN
  rw [Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero] at h
  exact h

private theorem globalThetaSobolevPrincipalValue_equivariant_hcomm (S : Finset V) (hn : S.Nonempty)
    (g : IdeleGroup (𝓞 F) F) (f f₁ f₂ : ℬ₀)
    (hf₁ : f₁.val = schwartzBruhatUnitTranslate g f.val)
    (hf₂ : f₂.val = schwartzBruhatUnitTranslate g (adelePrincipalValue F S f.val)) :
    theta(pvTest(S, f₁)) = theta(f₂) :=
  (globalPolarFreeThetaSpace_mk_eq_iff (pvTest(S, f₁)) f₂).mpr
    (globalThetaSobolevPrincipalValue_equivariant_val_eq
      (adelicThetaLinearMap F) (adelePrincipalValue F S) hf₁ hf₂
      (globalThetaSobolevPrincipalValue_equivariant_ker_eq
        (globalThetaPrincipalValue_equivariant hn g f.val)))

private theorem globalThetaSobolevPrincipalValue_equivariant_val_eq_empty {α B : Type*}
    (S₀ S : α) (hS : S = S₀) (pv : α → B → B) (hpv : ∀ x, pv S₀ x = x) (tr : B → B)
    {f f₁ f₂ : B} (hf₁ : f₁ = tr f) (hf₂ : f₂ = tr (pv S f)) :
    pv S f₁ = f₂ := by
  subst hS
  rw [hpv, hf₁, hf₂, hpv]

private theorem globalThetaSobolevPrincipalValue_equivariant_id_apply {M : Type*}
    {instM : AddCommMonoid M} {instMod : @Module ℂ M _ instM}
    {f : @LinearMap ℂ ℂ _ _ (RingHom.id ℂ) M M instM instM instMod instMod}
    (hf : f = @LinearMap.id ℂ M _ instM instMod) (x : M) : f x = x := by
  subst hf
  rfl

private theorem globalThetaSobolevPrincipalValue_equivariant_conj_id {A B C ι : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    [TopologicalSpace C] (p : SeminormFamily ℂ (TensorProduct ℂ A B) ι)
    (e : WithGeneratingSeminorms (TensorProduct ℂ A B) p ≃L[ℂ] C) (g : A →ₗ[ℂ] A)
    (h : B →ₗ[ℂ] B) (hg : g = LinearMap.id) (hh : h = LinearMap.id) :
    e.toLinearMap.comp ((TensorProduct.map g h).comp e.symm.toLinearMap) = LinearMap.id := by
  subst hg hh
  rw [TensorProduct.map_id]
  ext x
  exact e.apply_symm_apply x

private theorem globalThetaSobolevPrincipalValue_equivariant_hcomm_empty
    (S : Finset V) (hn : ¬ S.Nonempty) (g : IdeleGroup (𝓞 F) F)
    (f f₁ f₂ : ℬ₀)
    (hf₁ : f₁.val = schwartzBruhatUnitTranslate g f.val)
    (hf₂ : f₂.val = schwartzBruhatUnitTranslate g (adelePrincipalValue F S f.val)) :
    theta(pvTest(S, f₁)) = theta(f₂) := by
  have key : ∀ h : (w : (∅ : Finset V)) →
      SchwartzBruhat (Multiplicative (w.val.adicCompletion F)) →ₗ[ℂ]
        SchwartzBruhat (Multiplicative (w.val.adicCompletion F)),
      PiTensorProduct.map (R := ℂ) h = LinearMap.id := fun h ↦ by
    rw [show h = fun _ ↦ LinearMap.id from funext fun w ↦ absurd w.2 (Finset.notMem_empty _)]
    exact PiTensorProduct.map_id
  have hP : sAdelePrincipalValue F (Finset.Subset.refl (∅ : Finset V)) = LinearMap.id := by
    unfold sAdelePrincipalValue
    exact globalThetaSobolevPrincipalValue_equivariant_conj_id _ _ _ _ rfl (key _)
  have hA : adelePrincipalValue F ∅ = LinearMap.id := by
    unfold adelePrincipalValue
    exact globalThetaSobolevPrincipalValue_equivariant_conj_id _ _ _ _ hP rfl
  exact congrArg (fun h : ℬ₀ ↦ theta(h))
    (Subtype.ext (globalThetaSobolevPrincipalValue_equivariant_val_eq_empty ∅ S
      (Finset.not_nonempty_iff_eq_empty.mp hn)
      (fun T x ↦ adelePrincipalValue F T x)
      (globalThetaSobolevPrincipalValue_equivariant_id_apply hA)
      (fun x ↦ schwartzBruhatUnitTranslate g x) hf₁ hf₂))

private theorem globalThetaSobolevPrincipalValue_equivariant_aux
    {C B X Y Z : Type*} [TopologicalSpace Z] [T2Space Z]
    (val : X → B) (j : Y → Z) (q : X → Y) (hi : DenseRange fun x ↦ j (q x))
    (P : Z → Z) (R : C → Z → Z) (hP : Continuous P) (k g' : C) (hg : g' = k)
    (hR : Continuous (R g'))
    (pv : X → X) (hPapp : ∀ x, P (j (q x)) = j (q (pv x)))
    {smul : ℝ → Z → Z} (c : ℝ) (hc : c = 1)
    (tr : B → B)
    (hRtr : ∀ x : X, ∃ x' : X, val x' = tr (val x) ∧ R g' (j (q x)) = smul c (j (q x')))
    (hone : ∀ z : Z, smul 1 z = z)
    (hcomm : ∀ (f f₁ f₂ : X), val f₁ = tr (val f) → val f₂ = tr (val (pv f)) →
      q (pv f₁) = q f₂)
    (u : Z) :
    P (R k u) = R k (P u) := by
  subst hg
  refine congrFun (hi.equalizer (hP.comp hR) (hR.comp hP) (funext fun x ↦ ?_)) u
  obtain ⟨x₁, hx₁, h1⟩ := hRtr x
  obtain ⟨x₂, hx₂, h2⟩ := hRtr (pv x)
  dsimp only [Function.comp_apply]
  rw [h1, hc, hone, hPapp, hPapp, h2, hc, hone, hcomm x x₁ x₂ hx₁ hx₂]

/-- Paper: Proposition 11.2.0.1(2), pp. 484–485. The extension commutes with
norm-one translations and hence preserves all norm-one isotypes.
Deviation: This compatibility is stated separately from closed range and holds
without the lower bound on the degree. -/
theorem globalThetaSobolevPrincipalValue_equivariant (S : Finset V) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) (k : C₁) (u : H(a, hs)) :
    let R := (exists_globalThetaSobolevAction (F := F) a hI hs).choose
    P(S, a, hs) (R k.val u) = R k.val (P(S, a, hs) u) := by
  intro R
  have hq : Surjective (fun f : ℬ₀ ↦ theta(f)) := Submodule.mkQ_surjective
    ((LinearMap.ker (adelicThetaLinearMap F)).comap (adelePolarSubspace F).subtype)
  have hdense : DenseRange (fun f : ℬ₀ ↦ j(a, hs) (theta(f))) :=
    (globalThetaSobolev_dense (F := F) a hI hs).comp hq.denseRange (j(a, hs)).continuous
  refine Exists.elim (QuotientGroup.mk_surjective k.val) fun g hg ↦ ?_
  have hc : (((m𝔽 (QuotientGroup.mk g)).val : ℝ) ^ (-a) : ℝ) = 1 := by
    have hk : ideleClassNorm F k.val = 1 := k.property
    change ((ideleClassNorm F (QuotientGroup.mk g)).val : ℝ) ^ (-a) = 1
    rw [hg, hk]
    simp
  exact globalThetaSobolevPrincipalValue_equivariant_aux Subtype.val (j(a, hs))
    (fun f : ℬ₀ ↦ theta(f)) hdense
    (P(S, a, hs)) (fun c v ↦ R c v) (P(S, a, hs)).continuous k.val (QuotientGroup.mk g) hg
    (R (QuotientGroup.mk g)).continuous
    (fun f ↦ pvTest(S, f)) (globalThetaSobolevPrincipalValue_apply S a hs)
    _ hc
    (fun f' ↦ schwartzBruhatUnitTranslate g f')
    ((exists_globalThetaSobolevAction (F := F) a hI hs).choose_spec.2.2 g)
    (fun z ↦ one_smul ℝ z)
    (if hn : S.Nonempty then
      globalThetaSobolevPrincipalValue_equivariant_hcomm S hn g
    else
      globalThetaSobolevPrincipalValue_equivariant_hcomm_empty S hn g)
    u

/-- Paper: Proof of Proposition 11.2.0.1, pp. 484–485. At an unramified
singleton place, the 0-line extension is the difference with the uniformizer translate.
Deviation: The difference formula applies on the local-unit-invariant summand.
Unramified norm-one isotypes lie in that summand by §5.3. -/
theorem globalThetaSobolevPrincipalValue_singleton (v : V) (π : (v.adicCompletion F)ˣ)
    (_hπ : Valued.v.IsUniformizer π.val) (χ : PontryaginDual C𝔽)
    (_hχ : (ideleClassNormTwist χ 0).IsUnramifiedAt v) {s : ℝ} (hs : 0 ≤ s)
    (u : H(0, hs)) (_hu : (u : W(s)) ∈ Wω(hs, χ.comp restriction)) :
    (P({v}, 0, hs) u : W(s)) =
      (u : W(s)) - ρ(hs) (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π) u.val := by sorry

-- TODO(paper-gap): Proposition 11.2.0.1(2) identifies the raw range with a
-- closed subspace. The singleton prime difference over ℚ has nonclosed range.
-- The kernel argument on p. 485 also requires each zero's own multiplicity.
-- For S = {2,3} and trivial χ over ℚ, 2πi/log 2 is simple. The difference
-- kills Mellin evaluation there but need not kill the first derivative.

/-- Paper: (11.2.0.3), p. 484. The closure of the extension's range agrees with
the norm closure of the principal values of the polar-free theta tests.
Deviation: The range of the extension must also be closed up. -/
theorem globalThetaSobolevPrincipalValue_range_closure (S : Finset V) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    closure (range (P(S, a, hs))) =
      closure (range fun f : ℬ₀ ↦ j(a, hs) (theta(pvTest(S, f)))) := by
  have closure_image (i : ℬ₀ → H(a, hs)) (p : H(a, hs) → H(a, hs)) (t : ℬ₀ → H(a, hs)) (hi : DenseRange i) (hp : Continuous p)
      (he : ∀ x, p (i x) = t x) : closure (range p) = closure (range t) := by
    rw [← show p ∘ i = t from funext he, Set.range_comp p i]
    exact le_antisymm (closure_minimal (hp.range_subset_closure_image_dense hi) isClosed_closure)
      (closure_mono (Set.image_subset_range _ _))
  let q : ℬ₀ → GlobalPolarFreeThetaSpace F := fun f ↦ theta(f)
  have hq : Surjective q := Submodule.mkQ_surjective
    ((LinearMap.ker (adelicThetaLinearMap F)).comap (adelePolarSubspace F).subtype)
  exact closure_image (fun f ↦ j(a, hs) (q f)) (P(S, a, hs))
    (fun f : ℬ₀ ↦ j(a, hs) (theta(pvTest(S, f))))
    ((globalThetaSobolev_dense (F := F) a hI hs).comp hq.denseRange (j(a, hs)).continuous)
    (P(S, a, hs)).continuous (globalThetaSobolevPrincipalValue_apply S a hs)

/-- Paper: Theorem 11.2.0.2(1), p. 485. The reciprocal partial Euler
product is the product of the unramified factors in the phase coordinates
of §6.3.1. The complex argument is the norm-twist parameter.
Deviation: For PV on S use the product over S on both sides. The product
over the places of S above p gives the operator for that subset. The canonical
phase in [0, 2π/log q) is given by unramifiedHeckeCharacter_existsUnique_phase. -/
theorem orbitalEulerProduct_eq_phase (χ : PontryaginDual C𝔽) (S : Finset V) (t : V → ℝ)
    (_hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (_ht : ∀ v ∈ S, (ideleClassNormTwist χ 0).localValue v = (q(v) : ℂ) ^ (-frequency(t v)))
    (z : ℂ) :
    reciprocalPartialHeckeEulerProduct χ S z =
      ∏ v ∈ S, (1 - (q(v) : ℂ) ^ (-z - frequency(t v))) := by
  classical
  exact Finset.prod_congr rfl fun v hv ↦ finiteHeckeEulerFactor_inv_eq_phase χ v
    (_hχ v hv) (t v) (by simpa only [neg_mul] using _ht v hv) z

/-- Paper: Theorem 11.2.0.2(1), p. 485. The multiplicity is the order of the
reciprocal partial Euler product at the given point. -/
def orbitalEulerMultiplicity (χ : PontryaginDual C𝔽) (S : Finset V) (z : ℂ) : ℕ :=
  (meromorphicOrderAt (reciprocalPartialHeckeEulerProduct χ S) z).untop₀.toNat

open Classical in
/-- Paper: Theorem 11.2.0.2(1), p. 485. Each vanishing local factor contributes
one to the multiplicity, including when several places lie over the same prime. -/
theorem orbitalEulerMultiplicity_eq_card (χ : PontryaginDual C𝔽) (S : Finset V) (z : ℂ) :
    orbitalEulerMultiplicity χ S z =
      (S.filter fun v ↦ (finiteHeckeEulerFactor χ v z)⁻¹ = 0).card := by
  classical
  let f (v : V) (w : ℂ) := (finiteHeckeEulerFactor χ v w)⁻¹
  have hfac (v : V) : meromorphicOrderAt (f v) z = if f v z = 0 then 1 else 0 := by
    obtain ⟨ha, ho⟩ := reciprocalEulerProduct_over_prime_order_le_factor χ v z
    change AnalyticAt ℂ (f v) z at ha
    change analyticOrderAt (f v) z ≤ 1 at ho
    rw [ha.meromorphicOrderAt_eq]
    split_ifs with hv
    · have hone : analyticOrderAt (f v) z = 1 :=
        le_antisymm ho (Order.one_le_iff_ne_zero.mpr (ha.analyticOrderAt_ne_zero.mpr hv))
      simp [hone]
    · simp [ha.analyticOrderAt_eq_zero.mpr hv]
  have horder : meromorphicOrderAt (reciprocalPartialHeckeEulerProduct χ S) z =
      ((S.filter fun v ↦ f v z = 0).card : WithTop ℤ) := by
    change meromorphicOrderAt (fun w ↦ ∏ v ∈ S, f v w) z = _
    rw [meromorphicOrderAt_fun_prod (f := f) (fun v _ ↦
      (reciprocalEulerProduct_over_prime_order_le_factor χ v z).1.meromorphicAt)]
    simp only [hfac, Finset.sum_boole]
  rw [orbitalEulerMultiplicity, horder]
  simp [f]

/-- Paper: Theorem 11.2.0.2(1), p. 485. For a unitary character unramified
at the selected places, every zero of the reciprocal product has real part zero.
The complex argument is the norm-twist parameter, independent of the Sobolev degree. -/
theorem orbitalEulerZero_re_eq_zero (χ : PontryaginDual C𝔽) (S : Finset V)
    (_hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) {z : ℂ}
    (_hz : reciprocalPartialHeckeEulerProduct χ S z = 0) : z.re = 0 := by
  classical
  have hprod : (∏ v ∈ S, (finiteHeckeEulerFactor χ v z)⁻¹) = 0 := _hz
  obtain ⟨v, hv, hzero⟩ := Finset.prod_eq_zero_iff.mp hprod
  rw [finiteHeckeEulerFactor, ite_eq_left (_hχ v hv), inv_inv, sub_eq_zero] at hzero
  have hq : 1 < (q(v) : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hn := congrArg (fun w : ℂ ↦ ‖w‖) hzero.symm
  simp only [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
    Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)),
    Complex.neg_re, norm_one] at hn
  have he : -z.re = 0 := (Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne').mp
    (hn.trans (Real.rpow_zero _).symm)
  exact neg_eq_zero.mp he

/-- Paper: Theorem 11.2.0.2(1)–(2) and (11.2.0.6), p. 485. Index jets by their
0-line ordinate and surviving log-power order.
Deviation: Use the strict reciprocal-weight integrability cutoff of §10.2,
which excludes a logarithmically divergent endpoint of the printed floor. -/
abbrev OrbitalJetIndex (χ : PontryaginDual C𝔽) (S : Finset V) (s : ℝ) :=
  {j : ℝ × ℕ //
    j.2 < spectralBoundaryMultiplicity s (orbitalEulerMultiplicity χ S (frequency(j.1)))}

private theorem OrbitalJetIndex.isZero_analyticAt (χ : PontryaginDual C𝔽) (S : Finset V)
    (z : ℂ) : AnalyticAt ℂ (reciprocalPartialHeckeEulerProduct χ S) z := by
  have h : ∀ v ∈ S, AnalyticAt ℂ (fun s ↦ (finiteHeckeEulerFactor χ v s)⁻¹) z := by
    intro v _
    have hq : (Ideal.absNorm v.asIdeal : ℂ) ∈ Complex.slitPlane :=
      Complex.natCast_mem_slitPlane.mpr ((Ideal.absNorm_eq_zero_iff).not.mpr v.ne_bot)
    classical
    by_cases hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v
    · have : (fun s ↦ (finiteHeckeEulerFactor χ v s)⁻¹) = fun s ↦
          1 - (ideleClassNormTwist χ 0).localValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) := by
        funext s
        rw [finiteHeckeEulerFactor, ite_eq_left hv, inv_inv]
      rw [this]
      exact analyticAt_const.sub
        (analyticAt_const.mul (AnalyticAt.cpow analyticAt_const analyticAt_id.neg hq))
    · have : (fun s ↦ (finiteHeckeEulerFactor χ v s)⁻¹) = fun _ ↦ 1 := by
        funext s
        rw [finiteHeckeEulerFactor, ite_eq_right hv, inv_one]
      rw [this]
      exact analyticAt_const
  have := Finset.analyticAt_prod S h
  convert this using 1
  funext s
  simp [reciprocalPartialHeckeEulerProduct]

private theorem OrbitalJetIndex.isZero_of_order_pos {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (h : 0 < (meromorphicOrderAt f z).untop₀.toNat) : f z = 0 := by
  by_contra hz
  have h0 : analyticOrderAt f z = 0 := hf.analyticOrderAt_eq_zero.mpr hz
  rw [hf.meromorphicOrderAt_eq, h0] at h
  simp at h

/-- Paper: Theorem 11.2.0.2(1)–(2), p. 485. An admitted jet has a zero of the
reciprocal Euler product at its ordinate. -/
theorem OrbitalJetIndex.isZero {χ : PontryaginDual C𝔽} {S : Finset V} {s : ℝ}
    (j : OrbitalJetIndex χ S s) :
    reciprocalPartialHeckeEulerProduct χ S (frequency(j.val.1)) = 0 :=
  OrbitalJetIndex.isZero_of_order_pos (OrbitalJetIndex.isZero_analyticAt χ S _)
    (Nat.zero_lt_of_lt (lt_of_lt_of_le j.property (min_le_left _ _)))

private theorem orbitalJet_logNorm_continuous :
    Continuous (fun g : C𝔽 ↦ logNorm g) :=
  Real.continuousOn_log.comp_continuous
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous))
    fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'

private theorem orbitalJet_log_positiveRealHaar :
    Measure.map (fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) positiveRealHaar = volume := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have hlogt : Measurable (fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) :=
    (Real.continuousOn_log.comp_continuous (NNReal.continuous_coe.comp Units.continuous_val)
      fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne').measurable
  unfold positiveRealHaar
  have hexp : Measurable (fun x : ℝ ↦
      Units.mk0 (Real.exp x).toNNReal
        (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))) :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  rw [Measure.map_map hlogt hexp]
  have hid : ((fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) ∘ fun x : ℝ ↦
      Units.mk0 (Real.exp x).toNNReal
        (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))) = id := by
    funext x
    change Real.log ((Real.exp x).toNNReal : ℝ) = x
    rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]
  rw [hid, Measure.map_id]

private theorem orbitalJet_logNorm_measurePreserving :
    MeasurePreserving (fun g : C𝔽 ↦ logNorm g)
      (canonicalModulatedHaar m𝔽
        (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽))
      volume := by
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  obtain ⟨τ, hτc, hτ⟩ := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.2.1
  let τ' : ℝ≥0ˣ →ₜ* C𝔽 := ⟨τ, hτc⟩
  let : CompactSpace (m𝔽).toMonoidHom.ker :=
    isCompact_iff_compactSpace.mp (IsModulation.isCompact_ker hm)
  let μ₁ : Measure (m𝔽).toMonoidHom.ker := Measure.haarMeasure ⊤
  let : IsProbabilityMeasure μ₁ := ⟨Measure.haarMeasure_self⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  refine ⟨orbitalJet_logNorm_continuous.measurable, ?_⟩
  rw [canonicalModulatedHaar_eq_map_prod m𝔽 hm τ' hτ μ₁ Measure.haarMeasure_self]
  have hsplit_meas : Measurable (fun z : (m𝔽).toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : C𝔽) * τ' z.2) :=
    ((continuous_subtype_val.comp continuous_fst).mul (τ'.continuous.comp continuous_snd)).measurable
  rw [Measure.map_map orbitalJet_logNorm_continuous.measurable hsplit_meas]
  have hcomp : ((fun g : C𝔽 ↦ logNorm g) ∘ fun z : (m𝔽).toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : C𝔽) * τ' z.2) =
      (fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) ∘ Prod.snd := by
    funext ⟨k, t⟩
    change Real.log ((ideleClassNorm F ((k : C𝔽) * τ t)).val : ℝ) = Real.log ((t.val : ℝ≥0) : ℝ)
    have hk : ideleClassNorm F (k : C𝔽) = 1 := k.property
    rw [map_mul, hk, one_mul, hτ t]
  have hlogt : Measurable (fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) :=
    (Real.continuousOn_log.comp_continuous (NNReal.continuous_coe.comp Units.continuous_val)
      fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne').measurable
  rw [hcomp, ← Measure.map_map hlogt measurable_snd,
    (measurePreserving_snd (μ := μ₁) (ν := positiveRealHaar)).map_eq]
  exact orbitalJet_log_positiveRealHaar

private theorem orbitalJet_pow_mul_rpow_inv_continuous (k : ℕ) (s : ℝ) :
    Continuous (fun x : ℝ ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
  (continuous_id.pow (2 * k)).mul
    (((continuous_const.add (continuous_id.pow 2)).rpow_const fun x ↦
        Or.inl (by change (1 : ℝ) + x ^ 2 ≠ 0; positivity)).inv₀ fun x ↦
      (Real.rpow_pos_of_pos (by change (0 : ℝ) < 1 + x ^ 2; positivity) _).ne')

private theorem orbitalJet_integrable_pow_mul_rpow_inv {k : ℕ} {s : ℝ}
    (h : 2 * (k : ℝ) + 1 < s) :
    Integrable (fun x : ℝ ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) volume := by
  have hr : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < s - 2 * k := by
    rw [Module.finrank_self]
    push_cast
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) hr).mono'
    (orbitalJet_pow_mul_rpow_inv_continuous k s).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  have hy : 0 < 1 + x ^ 2 := by positivity
  have h1 : x ^ (2 * k) ≤ (1 + x ^ 2) ^ k := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg x) (by linarith) k
  have h2 : (1 + x ^ 2) ^ (-(s - 2 * k) / 2) = (1 + x ^ 2) ^ k * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
    rw [← Real.rpow_natCast (1 + x ^ 2) k, ← Real.rpow_neg hy.le, ← Real.rpow_add hy]
    congr 1
    ring
  rw [Real.norm_of_nonneg (mul_nonneg (Even.pow_nonneg (even_two_mul k) x)
    (inv_nonneg.2 (Real.rpow_nonneg hy.le _))), Real.norm_eq_abs, sq_abs, h2]
  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 (Real.rpow_nonneg hy.le _))

private theorem orbitalJet_continuous (χ : PontryaginDual C𝔽) (t : ℝ) (k : ℕ) :
    Continuous (jet(χ, t, k)) :=
  (ideleClassNormTwist χ ((0 : ℂ) + (t : ℂ) * Complex.I)).continuous.mul
    ((Complex.continuous_ofReal.comp orbitalJet_logNorm_continuous).pow k)

private theorem orbitalJet_norm_sq (χ : PontryaginDual C𝔽) (t : ℝ) (k : ℕ) (g : C𝔽) :
    ‖jet(χ, t, k) g‖ ^ 2 = (logNorm g) ^ (2 * k) := by
  have htwist : ‖ideleClassNormTwist χ ((0 : ℂ) + (t : ℂ) * Complex.I) g‖ = 1 := by
    change ‖(χ g : ℂ) *
      (((ideleClassNorm F g).val : ℝ) : ℂ) ^ ((0 : ℂ) + (t : ℂ) * Complex.I)‖ = 1
    rw [norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos
        (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g)))]
    simp
  change ‖ideleClassNormTwist χ ((0 : ℂ) + (t : ℂ) * Complex.I) g *
    (logNorm g : ℂ) ^ k‖ ^ 2 = _
  rw [norm_mul, htwist, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc
    (|logNorm g| ^ k) ^ 2 = (|logNorm g| ^ 2) ^ k := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
    _ = ((logNorm g) ^ 2) ^ k := congrArg (fun y : ℝ ↦ y ^ k) (sq_abs (logNorm g))
    _ = (logNorm g) ^ (2 * k) := (pow_mul _ _ _).symm

private theorem orbitalJet_density_eq (s : ℝ) (g : C𝔽) :
    (intervalSobolevDensity 0 0 s (logNorm g))⁻¹ =
      ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹ := by
  simp only [intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero, max_self, one_mul]

private theorem orbitalJet_density_pos (s : ℝ) (g : C𝔽) :
    0 < (intervalSobolevDensity 0 0 s (logNorm g))⁻¹ := by
  rw [orbitalJet_density_eq]
  exact inv_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)

private theorem orbitalJet_density_continuous (s : ℝ) :
    Continuous (fun g : C𝔽 ↦ (intervalSobolevDensity 0 0 s (logNorm g))⁻¹) := by
  have hρ : Continuous (fun g : C𝔽 ↦ (1 + (logNorm g) ^ 2) ^ (s / 2)) :=
    ((continuous_const : Continuous (fun _ : C𝔽 ↦ (1 : ℝ))).add
      (orbitalJet_logNorm_continuous.pow 2)).rpow_const fun g ↦ Or.inl (by
        change (1 : ℝ) + (logNorm g) ^ 2 ≠ 0
        positivity)
  have heq : (fun g : C𝔽 ↦ (intervalSobolevDensity 0 0 s (logNorm g))⁻¹) =
      fun g : C𝔽 ↦ ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹ :=
    funext (orbitalJet_density_eq s)
  rw [heq]
  exact hρ.inv₀ fun g ↦ (Real.rpow_pos_of_pos (by positivity) _).ne'

private theorem orbitalJet_ae_of_ae_withDensity {s : ℝ} {p : C𝔽 → Prop}
    (h : ∀ᵐ g ∂(μ'(s)), p g) : ∀ᵐ g ∂μ𝔽, p g := by
  have h' := (ae_withDensity_iff
    ((orbitalJet_density_continuous s).measurable.ennreal_ofReal)).mp h
  filter_upwards [h'] with g hg
  exact hg (ENNReal.ofReal_pos.mpr (orbitalJet_density_pos s g)).ne'

/-- Paper: Theorem 11.2.0.2 and (11.2.0.5), p. 485. Each admitted jet gives a
reciprocal-weight Sobolev vector.
Deviation: The cutoff excludes the divergent endpoint. -/
theorem orbitalJet_memLp (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ} (_hs : 0 ≤ s)
    (j : OrbitalJetIndex χ S s) :
    MemLp (jet(χ, j.val.1, j.val.2)) 2 (μ'(s)) := by
  have horder : (j.val.2 : ℝ) < (s - 1) / 2 :=
    ((lt_spectralBoundaryMultiplicity s _ _).mp j.property).2
  have hk : 2 * (j.val.2 : ℝ) + 1 < s := by linarith
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm).exists.choose_spec.1
  have hν : Integrable (fun g : C𝔽 ↦ (logNorm g) ^ (2 * j.val.2) *
      ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹) ν :=
    orbitalJet_logNorm_measurePreserving.integrable_comp_of_integrable
      (orbitalJet_integrable_pow_mul_rpow_inv hk)
  have hμ : Integrable (fun g : C𝔽 ↦ (logNorm g) ^ (2 * j.val.2) *
      ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹) μ𝔽 := by
    rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    exact hν.smul_measure_nnreal
  apply (memLp_two_iff_integrable_sq_norm
    (orbitalJet_continuous χ j.val.1 j.val.2).aestronglyMeasurable).2
  apply (integrable_withDensity_iff
    ((orbitalJet_density_continuous s).measurable.ennreal_ofReal)
    (ae_of_all μ𝔽 fun _ ↦ ENNReal.ofReal_lt_top)).2
  refine hμ.congr (ae_of_all μ𝔽 fun g ↦ ?_)
  dsimp only
  rw [orbitalJet_norm_sq, orbitalJet_density_eq,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)]

local notation "jetLp(" χ ", " S ", " hs ", " j ")" =>
  (orbitalJet_memLp χ S hs j).toLp (jet(χ, (j).val.1, (j).val.2))

/-- Paper: Theorem 11.2.0.2, p. 485. Under left translation, each admitted jet
lies in the conjugate isotype in the negative space. -/
theorem orbitalJet_isotype (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ} (hs : 0 ≤ s)
    (j : OrbitalJetIndex χ S s) (k : C₁) :
    (fun g ↦ jetLp(χ, S, hs, j) (k.val⁻¹ * g)) =ᵐ[μ𝔽]
      fun g ↦ (χ⁻¹ k.val : ℂ) * jetLp(χ, S, hs, j) g := by
  have hae : (jetLp(χ, S, hs, j) : C𝔽 → ℂ) =ᵐ[μ𝔽] jet(χ, j.val.1, j.val.2) :=
    orbitalJet_ae_of_ae_withDensity (MemLp.coeFn_toLp _)
  have hae_tr : (fun g ↦ jetLp(χ, S, hs, j) (k.val⁻¹ * g)) =ᵐ[μ𝔽]
      fun g ↦ jet(χ, j.val.1, j.val.2) (k.val⁻¹ * g) :=
    (measurePreserving_mul_left μ𝔽 k.val⁻¹).quasiMeasurePreserving.ae_eq_comp hae
  have hpt : ∀ g : C𝔽, jet(χ, j.val.1, j.val.2) (k.val⁻¹ * g) =
      (χ⁻¹ k.val : ℂ) * jet(χ, j.val.1, j.val.2) g := by
    intro g
    have hk : ideleClassNorm F k.val = 1 := k.property
    have hnorm : ideleClassNorm F (k.val⁻¹ * g) = ideleClassNorm F g := by
      rw [map_mul, map_inv, hk, inv_one, one_mul]
    have hlog : logNorm (k.val⁻¹ * g) = logNorm g := by
      dsimp only
      rw [hnorm]
    change (χ (k.val⁻¹ * g) : ℂ) *
        (((ideleClassNorm F (k.val⁻¹ * g)).val : ℝ) : ℂ) ^ ((0 : ℂ) + (j.val.1 : ℂ) * Complex.I) *
        (logNorm (k.val⁻¹ * g) : ℂ) ^ j.val.2 =
      (χ⁻¹ k.val : ℂ) *
        ((χ g : ℂ) *
          (((ideleClassNorm F g).val : ℝ) : ℂ) ^ ((0 : ℂ) + (j.val.1 : ℂ) * Complex.I) *
          (logNorm g : ℂ) ^ j.val.2)
    rw [hnorm, hlog, map_mul, Circle.coe_mul, map_inv]
    have hχinv : (χ k.val)⁻¹ = χ⁻¹ k.val := rfl
    rw [hχinv]
    ring
  filter_upwards [hae_tr, hae] with g hg₁ hg₂
  rw [hg₁, hg₂, hpt g]

variable (F) in
/-- Paper: Theorem 11.2.0.2 and Remark 11.2.0.3, p. 485. Inside the chosen
positive Sobolev isotype, take the closed principal-value subspace.
Deviation: Close the completed principal-value range in the ambient space
before taking the isotype. -/
def orbitalSobolevSubmodule (S : Finset V) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) : Submodule ℂ Wω(hs, ω) :=
  ((((H(0, hs)).subtype.comp (P(S, 0, hs)).toLinearMap).range).topologicalClosure).comap
    (Wω(hs, ω)).subtype

local notation "N(" S ", " hs ", " ω ")" => orbitalSobolevSubmodule F S hs ω
local notation "Q(" S ", " hs ", " ω ")" => (↥(Wω(hs, ω)) ⧸ N(S, hs, ω))

/-- Paper: Remark 11.2.0.3, p. 485. The principal-value subspace is closed
in its isotype, so the quotient carries the canonical quotient norm.
Deviation: Sanity check for the closure used in the definition. -/
@[instance]
theorem instClosedOrbitalSobolevSubmoduleSec2a (S : Finset V) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) : IsClosed (N(S, hs, ω) : Set Wω(hs, ω)) :=
  (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val

/-- Conjugating the tensor product of two identity maps by a linear
equivalence out of a seminorm-generated tensor space gives the identity. -/
theorem withGeneratingSeminorms_conj_map_id {A B C ι : Type*} [AddCommGroup A]
    [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    [TopologicalSpace C] (p : SeminormFamily ℂ (TensorProduct ℂ A B) ι)
    (e : WithGeneratingSeminorms (TensorProduct ℂ A B) p ≃L[ℂ] C) (g : A →ₗ[ℂ] A)
    (h : B →ₗ[ℂ] B) (hg : g = LinearMap.id) (hh : h = LinearMap.id) :
    e.toLinearMap.comp ((TensorProduct.map g h).comp e.symm.toLinearMap) = LinearMap.id := by
  subst hg hh
  rw [TensorProduct.map_id]
  ext x
  exact e.apply_symm_apply x

/-- Pulling back the closure of a dense submodule to any submodule gives the
whole submodule. -/
theorem comap_topologicalClosure_eq_top_of_dense {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousConstSMul ℂ E] (K R : Submodule ℂ E)
    (hR : Dense (R : Set E)) : R.topologicalClosure.comap K.subtype = ⊤ := by
  rw [(Submodule.dense_iff_topologicalClosure_eq_top).1 hR, Submodule.comap_top]

/-- Paper: Theorem 11.2.0.2, p. 485. With no finite places imposed, the
principal-value subspace is the whole isotype.
Deviation: Sanity check for the empty set of places. -/
theorem orbitalSobolevSubmodule_empty {s : ℝ} (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    N(∅, hs, ω) = ⊤ := by
  have key : ∀ g : (w : (∅ : Finset V)) →
      SchwartzBruhat (Multiplicative (w.val.adicCompletion F)) →ₗ[ℂ]
        SchwartzBruhat (Multiplicative (w.val.adicCompletion F)),
      PiTensorProduct.map (R := ℂ) g = LinearMap.id := fun g ↦ by
    rw [show g = fun _ ↦ LinearMap.id from funext fun w ↦ absurd w.2 (Finset.notMem_empty _)]
    exact PiTensorProduct.map_id
  have hP : sAdelePrincipalValue F (Finset.Subset.refl (∅ : Finset V)) = LinearMap.id := by
    unfold sAdelePrincipalValue
    exact withGeneratingSeminorms_conj_map_id _ _ _ _ rfl (key _)
  have hA : adelePrincipalValue F ∅ = LinearMap.id := by
    unfold adelePrincipalValue
    exact withGeneratingSeminorms_conj_map_id _ _ _ _ hP rfl
  have hpv : ∀ f : ℬ₀, pvTest(∅, f) = f := fun f ↦ Subtype.ext (by
    simp only [hA, LinearMap.id_apply])
  have hPid : P(∅, 0, hs) = ContinuousLinearMap.id ℂ _ :=
    (existsUnique_globalThetaSobolevPrincipalValue ∅ 0 hs).unique
      (existsUnique_globalThetaSobolevPrincipalValue ∅ 0 hs).exists.choose_spec
      (fun f ↦ congrArg (fun g : ℬ₀ ↦ j(0, hs) (theta(g))) (hpv f).symm)
  unfold orbitalSobolevSubmodule
  refine comap_topologicalClosure_eq_top_of_dense _ _ ?_
  refine (denseRange_globalTheta_zeroLine hs).mono ?_
  rintro _ ⟨u, rfl⟩
  exact ⟨j(0, hs) u, congrArg
    (fun T : H(0, hs) →L[ℂ] H(0, hs) ↦ ((T (j(0, hs) u) : H(0, hs)) : W(s))) hPid⟩

-- TODO(paper-gap): The proof on p. 486 needs density of both spans for the
-- completed PV quotient. Strong approximation on the ambient space in §9.3
-- alone does not identify the annihilator of that completed image.

/-- Paper: Theorem 11.2.0.2 and Terminology 11.2.0.1, p. 485. The zero jets
constitute an orbital Markushevich basis in the strong dual of the isotypic
quotient, realized by the bilinear Sobolev pairing. The biorthogonal vectors
are written in the Hilbert predual.
Deviation: Use the conjugate isotype for the annihilator, as in the statement
of jet membership. Quotienting by the closure gives the same continuous
annihilator as the raw range. Index each zero of the product once with its
total multiplicity. The index type permits any reindexing, including the
empty family. -/
theorem orbitalMarkushevichBasis (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ}
    (hs : 0 ≤ s) (_hcard : 2 * (S.card : ℝ) ≤ s)
    (_hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) :
    let J := OrbitalJetIndex χ S s
    let ω := χ.comp restriction
    letI : IsClosed (N(S, hs, ω) : Set Wω(hs, ω)) :=
      instClosedOrbitalSobolevSubmoduleSec2a S hs ω
    let Q := Q(S, hs, ω)
    Countable J ∧
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q),
      IsSpectralMarkushevichBasis x Λ ∧ ∀ (j : J) (f : Wω(hs, ω)),
        Λ j ((N(S, hs, ω)).mkQ f) = spectralSobolevPairing f.val (jetLp(χ, S, hs, j)) :=
  by sorry

-- TODO(paper-gap): Remark 11.2.0.3 drops PV from the denominator of the quotient.

/-- Paper: Remark 11.2.0.3, p. 485. The pairing represents the quotient
strong dual isometrically as the annihilator in the negative space.
Deviation: Divide the isotype by the closed principal-value subspace. -/
theorem orbitalQuotientDual_isometry_range (S : Finset V) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :
    ∃ D : StrongDual ℂ Q(S, hs, ω) →ₗᵢ[ℂ] W'(s),
      range D = {u |
        (∀ k : C₁, (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ𝔽] fun g ↦ (ω⁻¹ k : ℂ) * u g) ∧
        ∀ f ∈ N(S, hs, ω), spectralSobolevPairing f.val u = 0} ∧
      ∀ (Λ : StrongDual ℂ Q(S, hs, ω)) (f : Wω(hs, ω)),
        spectralSobolevPairing f.val (D Λ) = Λ ((N(S, hs, ω)).mkQ f) := by sorry

local notation "E" => ModulatedExponentialDecay m𝔽 (univ : Set ℝ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "hms𝔽" => (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
local notation "ρE" => (exists_modulatedExponentialDecay_translationAction m𝔽 univ
  hm𝔽 hms𝔽 ordConnected_univ univ_nonempty).choose
local notation "Eω(" ω ")" => actionIsotype ((ρE).comp (ideleClassNorm F).ker.subtype) ω

/-- Paper: (11.2.0.7), p. 486. The continuous transpose of the test inclusion
evaluates by the Sobolev pairing. It gives the commutative square after
restriction to the homogeneous principal-value tests of every polar-free input.
Deviation: Use the equivalent isotypic presentation of the tests on idele
classes from §10.2, with the conjugate isotype on the negative side. -/
theorem orbitalSobolevPairing_pullback (S : Finset V) (a : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (u : W'(s))
    (_hu : ∀ k : C₁, (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ𝔽] fun g ↦ (ω⁻¹ k : ℂ) * u g) :
    let i := (existsUnique_spectralLineTestCompletion a hs ω).exists.choose
    let A := (existsUnique_globalThetaSobolevAverage (F := F) (a := a) hI hs ω).exists.choose
    ∃ Λ : StrongDual ℂ Eω(ω),
      (∀ φ : Eω(ω), Λ φ = spectralSobolevPairing (i φ).val u) ∧
      ∀ f : ℬ₀, ∃ φ : Eω(ω),
        (∀ g : C𝔽, φ.val.val g = homogeneousAdelicTheta ω (pvTest(S, f)).val g) ∧
        (i φ).val = (P(S, a, hs) (A (j(a, hs) (theta(f)))).val).val := by sorry

-- TODO(paper-gap): Proposition 11.2.0.4 prints the full multiplicity and
-- claims noncontainment in an open ball even when S₀ is empty.

private theorem orbitalJet_lp_norm_sq {s : ℝ} (u : Lp ℂ 2 (μ'(s))) :
    ‖u‖ ^ 2 = ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(μ'(s)) := by
  have hre : (inner ℂ u u).re = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  rw [← hre, L2.inner_def]
  have hre_int : (∫ g : C𝔽, inner ℂ (u g) (u g) ∂(μ'(s))).re =
      ∫ g : C𝔽, (inner ℂ (u g) (u g)).re ∂(μ'(s)) :=
    (Complex.reCLM.integral_comp_comm (L2.integrable_inner u u)).symm
  rw [hre_int]
  refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (u g)

private theorem orbitalJet_integral_pos {s : ℝ} (hs : 1 < s) {k : ℕ}
    (hkN : k < Nat.ceil ((s - 1) / 2)) :
    0 < ∫ g : C𝔽, (logNorm g) ^ (2 * k) * ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹ ∂μ𝔽 := by
  have hk' : (k : ℝ) < (s - 1) / 2 := Nat.lt_ceil.mp hkN
  have hk : 2 * (k : ℝ) + 1 < s := by linarith
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let fk : ℝ → ℝ := fun x ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹
  have hfk_int : Integrable fk volume := orbitalJet_integrable_pow_mul_rpow_inv hk
  have hν_eq : ∫ g : C𝔽, fk (logNorm g) ∂ν = ∫ x : ℝ, fk x ∂volume := by
    rw [← (orbitalJet_logNorm_measurePreserving (F := F)).map_eq,
      integral_map (orbitalJet_logNorm_continuous (F := F)).measurable.aemeasurable
        (orbitalJet_pow_mul_rpow_inv_continuous k s).aestronglyMeasurable]
  have hvol_pos : 0 < ∫ x : ℝ, fk x ∂volume := by
    let c : ℝ := ((5 : ℝ) ^ (s / 2))⁻¹
    have hc : 0 < c := inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
    have hind_int : Integrable ((Icc (1 : ℝ) 2).indicator fun _ ↦ c) volume :=
      (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
    have hle : ∀ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c) x ≤ fk x := by
      intro x
      by_cases hx : x ∈ Icc (1 : ℝ) 2
      · rw [indicator_of_mem hx]
        have hx1 : 1 ≤ x := hx.1
        have hx2 : x ≤ 2 := hx.2
        have hpow : (1 : ℝ) ≤ x ^ (2 * k) := one_le_pow₀ hx1
        have hbase : 1 + x ^ 2 ≤ 5 := by nlinarith
        have hrpow : (1 + x ^ 2) ^ (s / 2) ≤ (5 : ℝ) ^ (s / 2) :=
          Real.rpow_le_rpow (by positivity) hbase (by linarith)
        have hinv : c ≤ ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
          inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _) hrpow
        calc
          c = 1 * c := (one_mul c).symm
          _ ≤ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
            mul_le_mul hpow hinv hc.le (by positivity)
      · rw [indicator_of_notMem hx]
        exact mul_nonneg (Even.pow_nonneg (even_two_mul k) x)
          (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
    have hint_le : ∫ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c) x ∂volume ≤
        ∫ x : ℝ, fk x ∂volume :=
      integral_mono hind_int hfk_int hle
    have hind_val : ∫ x : ℝ, (Icc (1 : ℝ) 2).indicator (fun _ ↦ c) x ∂volume = c := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc]
      norm_num
    linarith
  have hμ_eq : (∫ g : C𝔽, fk (logNorm g) ∂μ𝔽) =
      (Measure.haarScalarFactor μ𝔽 ν : ℝ) * ∫ x : ℝ, fk x ∂volume := by
    conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, hν_eq]
  change 0 < ∫ g : C𝔽, fk (logNorm g) ∂μ𝔽
  rw [hμ_eq]
  have hfac_pos : 0 < (Measure.haarScalarFactor μ𝔽 ν : ℝ) := by
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν)
  exact mul_pos hfac_pos hvol_pos

/-- Paper: Proposition 11.2.0.4 and (11.2.0.8)–(11.2.0.9), p. 486. One
annulus bounds the norms of all admitted jets above and away from zero.
Deviation: Use the truncated multiplicity cited in (11.2.0.6) and the
conjugate isotype. The annulus condition is disjointness from the inner
open ball, which also holds for an empty family. -/
theorem orbitalJet_norm_annulus (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ}
    (hs : 1 < s) (_hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : OrbitalJetIndex χ S s,
      let u := jetLp(χ, S, (zero_lt_one.trans hs).le, j)
      C⁻¹ ≤ ‖u‖ ∧ ‖u‖ ≤ C := by
  let hs₀ : 0 ≤ s := (zero_lt_one.trans hs).le
  let N : ℕ := Nat.ceil ((s - 1) / 2)
  let I : ℕ → ℝ := fun k ↦
    ∫ g : C𝔽, (logNorm g) ^ (2 * k) * ((1 + (logNorm g) ^ 2) ^ (s / 2))⁻¹ ∂μ𝔽
  let r : ℕ → ℝ := fun k ↦ Real.sqrt (I k)
  have hnorm_sq : ∀ j : OrbitalJetIndex χ S s,
      ‖jetLp(χ, S, hs₀, j)‖ ^ 2 = I j.val.2 := by
    intro j
    let u := jetLp(χ, S, hs₀, j)
    have h1 : ‖u‖ ^ 2 = ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(μ'(s)) := orbitalJet_lp_norm_sq u
    have h2 : ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(μ'(s)) = ∫ g : C𝔽, (logNorm g) ^ (2 * j.val.2) ∂(μ'(s)) := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (orbitalJet_memLp χ S hs₀ j)] with g hg
      rw [hg, orbitalJet_norm_sq]
    have h3 : ∫ g : C𝔽, (logNorm g) ^ (2 * j.val.2) ∂(μ'(s)) = I j.val.2 := by
      rw [integral_withDensity_eq_integral_toReal_smul
        ((orbitalJet_density_continuous s).measurable.ennreal_ofReal)
        (ae_of_all μ𝔽 fun _ ↦ ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (ae_of_all μ𝔽 fun g ↦ ?_)
      dsimp only
      rw [smul_eq_mul, orbitalJet_density_eq,
        ENNReal.toReal_ofReal (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le),
        mul_comm]
    exact h1.trans (h2.trans h3)
  let C : ℝ := 1 + ∑ k ∈ Finset.range N, (r k + (r k)⁻¹)
  have hC_pos : 0 < C := by
    have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.range N, (r k + (r k)⁻¹) :=
      Finset.sum_nonneg fun k _ ↦ add_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
    linarith
  refine ⟨C, hC_pos, fun j ↦ ?_⟩
  have hjN : j.val.2 ∈ Finset.range N :=
    Finset.mem_range.mpr (lt_of_lt_of_le j.property (min_le_right _ _))
  have hr_pos : 0 < r j.val.2 :=
    Real.sqrt_pos.mpr (orbitalJet_integral_pos hs (Finset.mem_range.mp hjN))
  have hnorm_eq : ‖jetLp(χ, S, hs₀, j)‖ = r j.val.2 := by
    rw [← Real.sqrt_sq (norm_nonneg _), hnorm_sq j]
  have hterm_le : r j.val.2 + (r j.val.2)⁻¹ ≤ C := by
    have h1 : r j.val.2 + (r j.val.2)⁻¹ ≤ ∑ k ∈ Finset.range N, (r k + (r k)⁻¹) :=
      Finset.single_le_sum
        (fun k _ ↦ add_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))) hjN
    linarith
  dsimp only
  rw [hnorm_eq]
  refine ⟨?_, by linarith [inv_pos.mpr hr_pos]⟩
  have hinv_le : (r j.val.2)⁻¹ ≤ C := by linarith
  calc
    C⁻¹ ≤ ((r j.val.2)⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hr_pos) hinv_le
    _ = r j.val.2 := inv_inv _

/-- Paper: Corollary 11.2.0.5 and (11.2.0.10), pp. 486–487. The orbital
Markushevich basis is normalized in the strong-dual norm.
Deviation: Use the isotypic quotient with the closed principal-value
denominator. The degree hypothesis already admits the full multiplicity. -/
theorem orbitalMarkushevichBasis_normalized (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ}
    (hs : 1 < s) (_hcard : 2 * (S.card : ℝ) ≤ s)
    (_hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) :
    let hs₀ := (zero_lt_one.trans hs).le
    let J := OrbitalJetIndex χ S s
    let ω := χ.comp restriction
    letI : IsClosed (N(S, hs₀, ω) : Set Wω(hs₀, ω)) :=
      instClosedOrbitalSobolevSubmoduleSec2a S hs₀ ω
    let Q := Q(S, hs₀, ω)
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q),
      IsSpectralMarkushevichBasis x Λ ∧ IsNormalizedSpectralFamily Λ ∧
      ∀ (j : J) (f : Wω(hs₀, ω)),
        Λ j ((N(S, hs₀, ω)).mkQ f) = spectralSobolevPairing f.val (jetLp(χ, S, hs₀, j)) :=
  by sorry

end RiemannMasullo
