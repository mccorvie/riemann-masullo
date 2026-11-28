module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2
public import RiemannMasullo.Ch11_ShellStructure.Sec2b
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedLogCoefficient
import RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import RiemannMasullo.Ch02_AdelicTheta.Sec3
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-! # Logarithmic coordinates on the weighted S-local theta space -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1
  instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1
  instSIdeleQuotientHaarMeasureSec1

private theorem exists_normalizedCharacterPullbackL2
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : X → Y) (M : ℝ≥0∞)
    (hM : M ≠ ∞) (hMpos : 0 < M.toReal) (hf : MeasurePreserving f μ (M • ν))
    (χ : X → ℂ) (hχ : Measurable χ) (hχnorm : ∀ x, ‖χ x‖ = 1) :
    ∃ L : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ,
      ∀ v, (L v : X → ℂ) =ᵐ[μ] fun x ↦
        (Real.sqrt M.toReal : ℂ)⁻¹ * χ x * v (f x) := by
  let d := Real.sqrt M.toReal
  have hd : 0 < d := Real.sqrt_pos.mpr hMpos
  let form (v : Lp ℂ 2 ν) (x : X) : ℂ := χ x * v (f x)
  have hScaled (v : Lp ℂ 2 ν) : MemLp (v : Y → ℂ) 2 (M • ν) :=
    (Lp.memLp v).smul_measure hM
  have hPull (v : Lp ℂ 2 ν) : MemLp ((v : Y → ℂ) ∘ f) 2 μ :=
    (hScaled v).comp_measurePreserving hf
  have hnormForm (v : Lp ℂ 2 ν) (x : X) : ‖v (f x)‖ = ‖form v x‖ := by
    simp only [form, norm_mul, hχnorm, one_mul]
  have hForm (v : Lp ℂ 2 ν) : MemLp (form v) 2 μ :=
    (hPull v).congr_norm (hχ.aestronglyMeasurable.mul (hPull v).aestronglyMeasurable)
      (ae_of_all μ (hnormForm v))
  let A (v : Lp ℂ 2 ν) : Lp ℂ 2 μ := (hForm v).toLp (form v)
  have hA (v : Lp ℂ 2 ν) : (A v : X → ℂ) =ᵐ[μ] form v :=
    (hForm v).coeFn_toLp
  let T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := A
      map_add' := fun v w ↦ by
        apply Lp.ext
        filter_upwards [hA (v + w), hA v, hA w, Lp.coeFn_add (A v) (A w),
          hf.quasiMeasurePreserving.ae_eq_comp (Measure.ae_smul_measure (Lp.coeFn_add v w) M)]
          with x h₁ h₂ h₃ h₄ h₅
        change (v + w) (f x) = v (f x) + w (f x) at h₅
        simp only [h₁, h₄, Pi.add_apply, h₂, h₃, form, h₅, mul_add]
      map_smul' := fun k v ↦ by
        apply Lp.ext
        filter_upwards [hA (k • v), hA v, Lp.coeFn_smul k (A v),
          hf.quasiMeasurePreserving.ae_eq_comp (Measure.ae_smul_measure (Lp.coeFn_smul k v) M)]
          with x h₁ h₂ h₃ h₄
        change (k • v) (f x) = k * v (f x) at h₄
        change (A (k • v) : X → ℂ) x = (k • A v : Lp ℂ 2 μ) x
        simp only [h₁, h₃, Pi.smul_apply, smul_eq_mul, h₂, form, h₄]
        ring }
  have hAnorm (v : Lp ℂ 2 ν) : ‖A v‖ = d * ‖v‖ := by
    have hpow : (1 / (2 : ℝ≥0∞)).toReal = 1 / (2 : ℝ) := by
      simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    rw [Lp.norm_def, eLpNorm_congr_ae (hA v),
      ← eLpNorm_congr_norm_ae (hPull v).aestronglyMeasurable (hForm v).aestronglyMeasurable
        (ae_of_all μ (hnormForm v)),
      eLpNorm_comp_measurePreserving (hScaled v).aestronglyMeasurable hf,
      eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by simp : (2 : ℝ≥0∞) ≠ ∞),
      smul_eq_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← Lp.norm_def v,
      hpow, ← Real.sqrt_eq_rpow]
  let L : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ :=
    { toLinearMap := (d : ℂ)⁻¹ • T
      norm_map' := fun v ↦ by
        change ‖(d : ℂ)⁻¹ • A v‖ = ‖v‖
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd,
          hAnorm, inv_mul_cancel_left₀ hd.ne'] }
  refine ⟨L, fun v ↦ ?_⟩
  change (((d : ℂ)⁻¹ • A v : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] _
  filter_upwards [Lp.coeFn_smul ((d : ℂ)⁻¹) (A v), hA v] with x hx hv
  simp only [hx, Pi.smul_apply, smul_eq_mul, hv, form, mul_assoc]
  rfl

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "m" => continuousSIdeleQuotientNorm F S
local notation "μ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S

section CanonicalLogProduct

local instance instWeightedLogTransportNormOneMeasurable : MeasurableSpace J₁ := borel _
local notation "expUnit" => fun x : ℝ ↦ Units.mk0 (Real.toNNReal (Real.exp x)) (by positivity)

/-- The canonical quotient Haar measure is the product of norm-one Tamagawa
Haar measure and Lebesgue measure in logarithmic norm. -/
private theorem sLocalLogProduct_measurePreserving
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) :
    MeasurePreserving
      (fun p : J₁ × ℝ ↦ p.1.val * (QuotientGroup.mk (τ (expUnit p.2)) : Jₛ))
      ((η).prod volume) μ := by
  let : BorelSpace J₁ := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let p (z : J₁ × ℝ≥0ˣ) : Jₛ := z.1.val * QuotientGroup.mk (τ z.2)
  have hτc : Continuous (fun t : ℝ≥0ˣ ↦ (QuotientGroup.mk (τ t) : Jₛ)) :=
    QuotientGroup.continuous_mk.comp τ.continuous
  have hp : Measurable p :=
    (continuous_subtype_val.measurable.comp measurable_fst).mul (hτc.measurable.comp measurable_snd)
  have he : Measurable expUnit :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hExpMap : Measure.map expUnit volume = positiveRealHaar := rfl
  have hProdMap : Measure.map (Prod.map (id : J₁ → J₁) expUnit) ((η).prod volume) =
      (η).prod positiveRealHaar := by
    rw [← Measure.map_prod_map η volume measurable_id he, Measure.map_id, hExpMap]
  have hQuotient : ((η).prod positiveRealHaar).map p = μ :=
    (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 τ hτ
  have hProdMeasurable : Measurable (Prod.map (id : J₁ → J₁) expUnit) :=
    measurable_id.prodMap he
  change MeasurePreserving (p ∘ Prod.map id expUnit) ((η).prod volume) μ
  exact ⟨hp.comp hProdMeasurable, (Measure.map_map hp hProdMeasurable).symm.trans
    ((congrArg (Measure.map p) hProdMap).trans hQuotient)⟩

/-- The logarithmic character coefficient at the critical twist agrees with
the concrete radial theta of a Chapter 11 polar test, scaled by the square
root of the norm-one Haar mass. The equality uses the quotient Sobolev
representative from (11.2.1.1), p. 487. -/
theorem sLocalWeightedAngularLogCoefficient_onTheta {s : ℝ}
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁)
    (Q : CompactIntervalSobolev μ (logSIdeleQuotientNorm F S) 0 0 s →L[ℂ]
      Lp ℂ 2 (volume : Measure ℝ))
    (hQ : ∀ u, (Q u : ℝ → ℂ) =ᵐ[volume] fun x ↦
      (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ *
        ∫ h : J₁, (ω h : ℂ) * u (h.val * QuotientGroup.mk (τ (expUnit x))) ∂η)
    (f : sAdelePolarSubspace F S) :
    let u := sLocalPWThetaSobolevMap (F := F) (S := S) (s := s)
      (a := 1 / 2) (by norm_num) ω f
    (Q u : ℝ → ℂ) =ᵐ[volume] fun x ↦
      (Real.sqrt (Measure.real η univ) : ℂ) * ((Real.exp (x / 2) : ℂ) *
        sLocalHomogeneousAdelicThetaLinearMap F S ω f.val
          (QuotientGroup.mk (τ (expUnit x)))) := by
  intro u
  let q (x : ℝ) : Jₛ := QuotientGroup.mk (τ (expUnit x))
  let θ := sLocalHomogeneousAdelicThetaLinearMap F S ω f.val
  let U := modulationWeight m (1 / 2) θ
  have hRep : (u : Jₛ → ℂ) =ᵐ[μ] U :=
    sLocalPWThetaSobolevMap_apply (F := F) (S := S) (s := s)
      (a := 1 / 2) (by norm_num) ω f
  let : BorelSpace J₁ := ⟨rfl⟩
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : Measure.IsHaarMeasure η :=
    (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : IsFiniteMeasure η := CompactSpace.isFiniteMeasure
  have hChart := sLocalLogProduct_measurePreserving τ hτ
  have hFiber : ∀ᵐ x ∂volume, ∀ᵐ h : J₁ ∂η,
      u (h.val * q x) = U (h.val * q x) :=
    Measure.ae_ae_of_ae_prod
      (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
        (hChart.quasiMeasurePreserving.ae_eq_comp hRep))
  let c := Measure.real η univ
  let d := Real.sqrt c
  have hc : 0 < c := measureReal_univ_pos
  have hd : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hc).ne'
  have hSquare : (d : ℂ) * (d : ℂ) = (c : ℂ) := by
    rw [← Complex.ofReal_mul]
    exact congrArg Complex.ofReal (Real.mul_self_sqrt hc.le)
  have hScale : (d : ℂ)⁻¹ * (c : ℂ) = (d : ℂ) := by
    rw [← hSquare, inv_mul_cancel_left₀ hd]
  filter_upwards [hQ u, hFiber] with x hx hux
  let w : ℂ := (Real.exp (x / 2) : ℂ) * θ (q x)
  have hConst : (∫ h : J₁, (ω h : ℂ) * u (h.val * q x) ∂η) = (c : ℂ) * w := by
    calc
      _ = ∫ _ : J₁, w ∂η := by
        apply integral_congr_ae
        filter_upwards [hux] with h hh
        rw [hh]
        have hn : m (h.val * q x) = expUnit x := by
          change sIdeleQuotientNorm F S (h.val * q x) = _
          rw [map_mul, MonoidHom.mem_ker.mp h.property, one_mul]
          exact (sIdeleQuotientNorm_mk F S (τ (expUnit x))).trans (hτ _)
        have hv : ((expUnit x).val : ℝ) = Real.exp x :=
          Real.coe_toNNReal _ (Real.exp_pos _).le
        have hθ : (ω h : ℂ) * θ (h.val * q x) = θ (q x) := by
          symm
          simpa only [θ, sLocalHomogeneousAdelicThetaLinearMap, inv_mul_cancel_left] using
            (sLocalHomogeneousAdelicTheta_homogeneous F S η ω f.val h (h.val * q x))
        with_unfolding_all change (ω h : ℂ) *
          (((((m (h.val * q x)).val : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * θ (h.val * q x)) =
          (Real.exp (x / 2) : ℂ) * θ (q x)
        rw [hn, hv, ← Real.exp_mul, mul_one_div, mul_left_comm, hθ]
      _ = _ := by rw [integral_const, Complex.real_smul]
  change (Q u : ℝ → ℂ) x = (d : ℂ) * w
  calc
    _ = (d : ℂ)⁻¹ * (∫ h : J₁, (ω h : ℂ) * u (h.val * q x) ∂η) := hx
    _ = (d : ℂ)⁻¹ * ((c : ℂ) * w) := congrArg ((d : ℂ)⁻¹ * ·) hConst
    _ = ((d : ℂ)⁻¹ * (c : ℂ)) * w := (mul_assoc _ _ _).symm
    _ = _ := congrArg (· * w) hScale


private theorem sLocalLogNorm_measurable :
    Measurable (logSIdeleQuotientNorm F S) :=
  Real.measurable_log.comp
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (m).continuous)).measurable

/-- Logarithmic norm sends the S-local quotient Haar measure to Lebesgue
measure multiplied by the full norm-one Tamagawa mass. -/
theorem sLocalLogNorm_map_tamagawa
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) :
    Measure.map (logSIdeleQuotientNorm F S) μ =
      (η univ) • (volume : Measure ℝ) := by
  let p (z : J₁ × ℝ) : Jₛ :=
    z.1.val * QuotientGroup.mk (τ (expUnit z.2))
  have hp : MeasurePreserving p ((η).prod volume) μ :=
    sLocalLogProduct_measurePreserving τ hτ
  have hlog : Measurable (logSIdeleQuotientNorm F S) := sLocalLogNorm_measurable
  have hcoord : logSIdeleQuotientNorm F S ∘ p = Prod.snd := by
    funext z
    change Real.log ((sIdeleQuotientNorm F S
      (z.1.val * QuotientGroup.mk (τ (expUnit z.2)))).val : ℝ) = z.2
    rw [map_mul, MonoidHom.mem_ker.mp z.1.property, one_mul,
      sIdeleQuotientNorm_mk, hτ]
    change Real.log ((Real.exp z.2).toNNReal : ℝ) = z.2
    rw [Real.coe_toNNReal _ (Real.exp_pos _).le, Real.log_exp]
  rw [← hp.map_eq, Measure.map_map hlog hp.measurable, hcoord, Measure.map_snd_prod]

/-- The Sobolev measure on the S-idèle quotient has the same logarithmic
radial density as the real Sobolev measure, with the norm-one Haar mass. -/
theorem sLocalLogNorm_map_intervalSobolevMeasure
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) (a b s : ℝ) :
    Measure.map (logSIdeleQuotientNorm F S)
      (intervalSobolevMeasure μ (logSIdeleQuotientNorm F S) a b s) =
      (η univ) • intervalSobolevMeasure (volume : Measure ℝ) id a b s := by
  let weight (x : ℝ) := ENNReal.ofReal (intervalSobolevDensity a b s x)
  have hw : Measurable weight := by unfold weight intervalSobolevDensity; fun_prop
  have hlog : Measurable (logSIdeleQuotientNorm F S) := sLocalLogNorm_measurable
  change Measure.map (logSIdeleQuotientNorm F S)
    (Measure.withDensity μ (weight ∘ logSIdeleQuotientNorm F S)) =
      (η univ) • (volume : Measure ℝ).withDensity weight
  rw [← withDensity_smul_measure, ← sLocalLogNorm_map_tamagawa τ hτ]
  ext A hA
  rw [Measure.map_apply hlog hA, withDensity_apply _ (hlog hA), withDensity_apply _ hA]
  exact (setLIntegral_map hA hw hlog).symm

local notation "ℓ" => logSIdeleQuotientNorm F S

/-- The normalized inverse-character lift of a weighted radial function is
isometric for quotient Tamagawa measure. The normalization is the square root
of the norm-one quotient mass from Theorem 3.3.1.1(3), p. 129. -/
theorem exists_sLocalWeightedLogCharacterLift
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (a b s : ℝ) (χ : PontryaginDual Jₛ) :
    let νR := intervalSobolevMeasure (volume : Measure ℝ) id a b s
    let νJ := intervalSobolevMeasure μ ℓ a b s
    ∃ L : Lp ℂ 2 νR →ₗᵢ[ℂ] Lp ℂ 2 νJ,
      ∀ v, (L v : Jₛ → ℂ) =ᵐ[νJ] fun g ↦
        (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ * (χ g : ℂ)⁻¹ * v (ℓ g) := by
  intro νR νJ
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
  let : Measure.IsHaarMeasure η := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : IsFiniteMeasure η := CompactSpace.isFiniteMeasure
  have hM : η univ ≠ ∞ := measure_ne_top _ _
  have hMpos : 0 < Measure.real η univ := measureReal_univ_pos
  have hχ : Measurable fun g : Jₛ ↦ (χ g : ℂ)⁻¹ := by
    have hcont : Continuous (fun g : Jₛ ↦ (((χ g)⁻¹ : Circle) : ℂ)) :=
      continuous_subtype_val.comp χ.continuous.inv
    simpa only [Circle.coe_inv] using hcont.measurable
  have hχnorm (g : Jₛ) : ‖(χ g : ℂ)⁻¹‖ = 1 := by
    rw [norm_inv, Circle.norm_coe, inv_one]
  have hlog : MeasurePreserving ℓ νJ ((η univ) • νR) :=
    ⟨sLocalLogNorm_measurable, sLocalLogNorm_map_intervalSobolevMeasure τ hτ a b s⟩
  exact exists_normalizedCharacterPullbackL2 νJ νR ℓ (η univ) hM hMpos hlog _ hχ hχnorm

end CanonicalLogProduct

end RiemannMasullo
