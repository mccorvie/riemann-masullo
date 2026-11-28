module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedLogTransport
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! # Angular lifts of conjugated kernel rows -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo

/-- A product-square-integrable kernel with pointwise inverse-character
covariance of its conjugated rows has those rows in the image of the
normalized radial lift. -/
theorem ae_exists_lift_eq_star_kernel_row
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y)
    (f : X → Y) (j : Y → X) (hj : Measurable j)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (hCpos : 0 < C.toReal)
    (hf : MeasurePreserving f μ (C • ν))
    (a : X → ℂ) (ha : ∀ x, ‖a x‖ = 1)
    (L : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ)
    (hL : ∀ v, (L v : X → ℂ) =ᵐ[μ] fun x ↦
      (Real.sqrt C.toReal : ℂ)⁻¹ * a x * v (f x))
    (K : X × X → ℂ) (hKm : Measurable K) (hK : MemLp K 2 (μ.prod μ))
    (hCov : ∀ x y, star (K (x, y)) = a y * star (K (x, j (f y)))) :
    ∀ᵐ x ∂μ, ∃ v : Lp ℂ 2 ν, (L v : X → ℂ) =ᵐ[μ] fun y ↦ star (K (x, y)) := by
  let d : ℂ := Real.sqrt C.toReal
  have hd : d ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hCpos).ne'
  have hC₀ : C ≠ 0 := by
    intro hc
    exact (ne_of_gt hCpos) (by rw [hc, ENNReal.toReal_zero])
  have hSq : Integrable (fun p ↦ ‖K p‖ ^ 2) (μ.prod μ) :=
    (memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable).mp hK
  filter_upwards [hSq.prod_right_ae] with x hx
  let g (t : Y) : ℂ := star (K (x, j t))
  have hRowM : Measurable (fun y : X ↦ K (x, y)) :=
    hKm.comp (measurable_const.prodMk measurable_id)
  have hgM : Measurable g := continuous_star.measurable.comp (hRowM.comp hj)
  have hRow : MemLp (fun y : X ↦ K (x, y)) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hRowM.aestronglyMeasurable).mpr hx
  have hPull : MemLp (g ∘ f) 2 μ := hRow.congr_norm
    (hgM.comp hf.measurable).aestronglyMeasurable
    (ae_of_all _ fun y ↦ by
      have he := congrArg norm (hCov x y)
      simpa only [g, Function.comp_apply, norm_star, norm_mul, ha, one_mul] using he)
  have hScaled : MemLp g 2 (C • ν) := by
    rw [← hf.map_eq]
    exact (memLp_map_measure_iff hgM.aestronglyMeasurable hf.measurable.aemeasurable).2 hPull
  have hg : MemLp g 2 ν := by
    simpa only [smul_smul, ENNReal.inv_mul_cancel hC₀ hC, one_smul] using
      hScaled.smul_measure (ENNReal.inv_ne_top.2 hC₀)
  let r (t : Y) := d * g t
  have hr : MemLp r 2 ν := hg.const_mul d
  let v : Lp ℂ 2 ν := hr.toLp r
  have hv : (v : Y → ℂ) =ᵐ[ν] r := hr.coeFn_toLp
  have hPullRep : (fun x ↦ v (f x)) =ᵐ[μ] fun x ↦ r (f x) :=
    hf.quasiMeasurePreserving.ae_eq_comp (Measure.ae_smul_measure hv C)
  refine ⟨v, ?_⟩
  filter_upwards [hL v, hPullRep] with y hy hrep
  change v (f y) = r (f y) at hrep
  rw [hy, hrep, hCov x y]
  change d⁻¹ * a y * (d * g (f y)) = a y * g (f y)
  calc
    _ = (d⁻¹ * d) * (a y * g (f y)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hd, one_mul]

section SLocal

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "N" => sIdeleQuotientNorm F S
local notation "J₁" => MonoidHom.ker N
local notation "ℓ" => logSIdeleQuotientNorm F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "ν₀" => intervalSobolevMeasure μJ ℓ 0 0 0
local notation "W₀" => Lp ℂ 2 ν₀
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "expUnit" => fun x : ℝ ↦ Units.mk0 (Real.toNNReal (Real.exp x)) (by positivity)
local notation "include₁" => (ContinuousMonoidHom.mk (Subgroup.subtype (MonoidHom.ker N))
  continuous_subtype_val : J₁ →ₜ* Jₛ)

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1
  instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1
  instSIdeleQuotientHaarMeasureSec1

/-- On the quotient logarithmic chart, the input covariance alone places
the conjugated rows in the normalized inverse-character lift. -/
theorem sLocalTrace_ae_conjugatedRows_in_angularLift
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) (χ : PontryaginDual Jₛ)
    (hχ : χ.comp include₁ = ω) (hsec : ∀ t, χ (QuotientGroup.mk (τ t)) = 1)
    (L : FlatL2 →ₗᵢ[ℂ] W₀)
    (hL : ∀ v, (L v : Jₛ → ℂ) =ᵐ[ν₀] fun y ↦
      (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ * (χ y : ℂ)⁻¹ * v (ℓ y))
    (K : Jₛ × Jₛ → ℂ) (hKm : Measurable K) (hK : MemLp K 2 ((ν₀).prod ν₀))
    (hIn : ∀ (x y : Jₛ) (h : J₁), K (x, y * h.val) = (ω h : ℂ) * K (x, y)) :
    ∀ᵐ x ∂ν₀, ∃ v : FlatL2, (L v : Jₛ → ℂ) =ᵐ[ν₀] fun y ↦ star (K (x, y)) := by
  let j (t : ℝ) : Jₛ := QuotientGroup.mk (τ (expUnit t))
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : MeasurableSpace J₁ := borel _
  let : BorelSpace J₁ := ⟨rfl⟩
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
  let : Measure.IsHaarMeasure η := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : IsFiniteMeasure η := CompactSpace.isFiniteMeasure
  have hc : η univ ≠ ∞ := measure_ne_top _ _
  have hcpos : 0 < (η univ).toReal := measureReal_univ_pos
  have he : Measurable expUnit :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hj : Measurable j := (QuotientGroup.continuous_mk.comp τ.continuous).measurable.comp he
  have hlog : Measurable ℓ := Real.measurable_log.comp
    (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (continuousSIdeleQuotientNorm F S).continuous)).measurable
  have h0 (μ : Measure ℝ) : intervalSobolevMeasure μ id 0 0 0 = μ := by
    have h (x : ℝ) : intervalSobolevDensity 0 0 0 x = 1 := by simp [intervalSobolevDensity]
    change μ.withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 0 x)) = _
    simp only [h, ENNReal.ofReal_one]
    exact withDensity_one
  have hνMap : MeasurePreserving ℓ ν₀ ((η univ) • (volume : Measure ℝ)) :=
    ⟨hlog, by simpa only [h0] using sLocalLogNorm_map_intervalSobolevMeasure τ hτ 0 0 0⟩
  have hν₀ : (ν₀ : Measure Jₛ) = μJ := by
    have h (x : Jₛ) : intervalSobolevDensity 0 0 0 (ℓ x) = 1 := by
      simp [intervalSobolevDensity]
    change (μJ).withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 0 (ℓ x))) = _
    simp only [h, ENNReal.ofReal_one]
    exact withDensity_one
  let : SFinite ν₀ := hν₀.symm ▸ (inferInstance : SFinite μJ)
  have ha (y : Jₛ) : ‖(χ y : ℂ)⁻¹‖ = 1 := by
    rw [norm_inv, Circle.norm_coe, inv_one]
  apply ae_exists_lift_eq_star_kernel_row ν₀ volume ℓ j hj
    (η univ) hc hcpos hνMap (fun y ↦ (χ y : ℂ)⁻¹) ha L hL K hKm hK
  intro x y
  let a := j (ℓ y)
  have haN : N a = N y := by
    change N (QuotientGroup.mk (τ (expUnit (ℓ y)))) = N y
    rw [sIdeleQuotientNorm_mk, hτ]
    apply Units.ext
    apply NNReal.eq
    change ((Real.exp (Real.log ((N y).val : ℝ))).toNNReal : ℝ) = _
    rw [Real.coe_toNNReal _ (Real.exp_pos _).le,
      Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt (N y)))]
  let h : J₁ := ⟨a⁻¹ * y, MonoidHom.mem_ker.mpr (by
    rw [map_mul, map_inv, haN, inv_mul_cancel])⟩
  have hDec : a * h.val = y := by
    change a * (a⁻¹ * y) = y
    rw [mul_inv_cancel_left]
  have hχh : χ h.val = ω h :=
    congrArg (fun ψ : PontryaginDual J₁ ↦ ψ h) hχ
  have hω : ω h = χ y := by
    have hAh : χ (a * h.val) = χ h.val := by
      rw [map_mul]
      change χ (QuotientGroup.mk (τ (expUnit (ℓ y)))) * χ h.val = χ h.val
      rw [hsec, one_mul]
    exact hχh.symm.trans (hAh.symm.trans (congrArg χ hDec))
  have hKxy : K (x, y) = (ω h : ℂ) * K (x, a) :=
    (congrArg (fun z ↦ K (x, z)) hDec).symm.trans (hIn x a h)
  have hstar : star (ω h : ℂ) = (χ y : ℂ)⁻¹ := by
    rw [hω]
    exact (Circle.coe_inv_eq_conj (χ y)).symm
  rw [hKxy, star_mul', hstar]

end SLocal

end RiemannMasullo
