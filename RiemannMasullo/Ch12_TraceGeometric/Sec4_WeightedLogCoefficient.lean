module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3a
public import RiemannMasullo.Ch09_HardySobolev.Sec2
public import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Group.Integral

/-! # Angular coefficients from the weighted S-local quotient -/

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo

noncomputable section

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1
  instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1
  instSIdeleQuotientHaarMeasureSec1

private theorem transportAngularHaar {K X Y : Type*} [Group K] [TopologicalSpace K]
    [MeasurableSpace X] [MeasurableSpace Y] {m₁ m₂ : MeasurableSpace K} (hm : m₁ = m₂)
    (η : @Measure K m₁) (hη : @Measure.IsHaarMeasure K _ _ m₁ η)
    (νX : Measure X) (μ : Measure Y) (c : K × X → Y)
    (hp : @Measure.map (K × X) Y (@Prod.instMeasurableSpace K X m₁ _) _ c
      (@Measure.prod K X m₁ _ η νX) = μ) :
    ∃ η' : @Measure K m₂, (@Measure.IsHaarMeasure K _ _ m₂ η') ∧
      @Measure.map (K × X) Y (@Prod.instMeasurableSpace K X m₂ _) _ c
        (@Measure.prod K X m₂ _ η' νX) = μ ∧
      η'.real univ = η.real univ ∧
      ∀ f : K → ℂ, (∫ k, f k ∂η') = ∫ k, f k ∂η := by
  subst m₂
  exact ⟨η, hη, hp, rfl, fun _ ↦ rfl⟩

-- The complex-linear version of the weighted-to-flat restriction in Ch09/Sec3.
private theorem exists_L2_restriction_contracting {X : Type*} [MeasurableSpace X]
    (ν μ : Measure X) (h : μ ≤ ν) :
    ∃ J : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ,
      (∀ u, ‖J u‖ ≤ ‖u‖) ∧ ∀ u, (J u : X → ℂ) =ᵐ[μ] (u : X → ℂ) := by
  have hle : μ ≤ (1 : ℝ≥0∞) • ν := by simpa only [one_smul] using h
  let L := Lp.LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) ENNReal.one_ne_top hle
  have hL (u : Lp ℂ 2 ν) := Lp.coeFn_LpToLpOfMeasureLeSMul (E := ℂ) ENNReal.one_ne_top hle u
  let J : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
    { toFun := L, map_add' := L.map_add, cont := L.continuous
      map_smul' := by
        intro c u
        exact Lp.ext ((hL (c • u)).trans (Filter.EventuallyEq.trans (ae_mono h (Lp.coeFn_smul c u))
          (((hL u).symm.fun_comp (c • ·)).trans (Lp.coeFn_smul c (L u)).symm))) }
  refine ⟨J, fun u ↦ ?_, hL⟩
  change ‖L u‖ ≤ ‖u‖
  have hnorm : ‖L‖ ≤ 1 := by
    simpa only [ENNReal.toReal_one, Real.one_rpow] using
      (Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2) ENNReal.one_ne_top hle)
  exact (L.le_opNorm u).trans (mul_le_of_le_one_left (norm_nonneg _) hnorm)

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "m" => continuousSIdeleQuotientNorm F S
local notation "μ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S

/-- Construct the normalized coefficient from the isotypic transform. -/
private theorem exists_sLocalWeightedAngularLogCoefficient_aux {s : ℝ} (hs : 0 ≤ s)
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) (ω : PontryaginDual J₁) :
    let ν := intervalSobolevMeasure μ (logSIdeleQuotientNorm F S) 0 0 s
    let e (x : ℝ) := Units.mk0 (Real.exp x).toNNReal (by positivity)
    ∃ Q : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 (volume : Measure ℝ), ‖Q‖ ≤ 1 ∧
      ∀ u, (Q u : ℝ → ℂ) =ᵐ[volume] fun x ↦
        (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ *
          ∫ h : J₁, (ω h : ℂ) * u (h.val * QuotientGroup.mk (τ (e x))) ∂η := by
  intro ν e
  let q : Iₛ →ₜ* Jₛ := ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  let σ := q.comp τ
  have hσ : RightInverse σ m := fun t ↦ (sIdeleQuotientNorm_mk F S (τ t)).trans (hτ t)
  have hm : IsModulation m := by
    refine ⟨isProperMap_sIdeleQuotientNorm F S, ?_⟩
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    exact ⟨σ t, (hσ t).trans_ne ht⟩
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let p (z : J₁ × ℝ≥0ˣ) : Jₛ := z.1.val * σ z.2
  have hspace : borel J₁ = (inferInstance : MeasurableSpace J₁) := by
    change borel J₁ = (borel Jₛ).comap (Subtype.val : J₁ → Jₛ)
    exact borel_comap
  have hη := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have hp := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 τ hτ
  obtain ⟨η', hη', hp', hmass, hInt⟩ :=
    transportAngularHaar hspace η hη positiveRealHaar μ p hp
  let : η'.IsHaarMeasure := hη'
  have hprod : MeasurePreserving p (η'.prod positiveRealHaar) μ :=
    ⟨(continuous_subtype_val.measurable.comp measurable_fst).mul
      (σ.continuous.measurable.comp measurable_snd), hp'⟩
  have hw (x : ℝ) : 1 ≤ intervalSobolevDensity 0 0 s x := by
    simpa [intervalSobolevDensity] using Real.one_le_rpow
      (le_add_of_nonneg_right (sq_nonneg x)) (div_nonneg hs (by norm_num : (0 : ℝ) ≤ 2))
  have hle : μ ≤ ν :=
    calc
      μ = Measure.withDensity μ 1 := withDensity_one.symm
      _ ≤ ν := withDensity_mono (ae_of_all μ fun x ↦ by
        change 1 ≤ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logSIdeleQuotientNorm F S x))
        exact ENNReal.one_le_ofReal.mpr (hw _))
  obtain ⟨V, hVnorm, hV⟩ := exists_L2_restriction_contracting ν μ hle
  obtain ⟨T, hT⟩ := regularIsotypicTransform_continuousLinear m hm μ η' σ hσ
  let d := Real.sqrt (η'.real univ)
  have hd : 0 < d := Real.sqrt_pos.mpr measureReal_univ_pos
  have hTnorm (v : RegularL2 μ) : ‖T v‖ = d * ‖v‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hd.le (norm_nonneg _))).mp
    rw [hT, mul_pow, Real.sq_sqrt measureReal_nonneg]
    have hmap : (η'.prod positiveRealHaar).map p = (1 : ℝ≥0∞) • μ := by
      simpa only [one_smul] using hp'
    simpa only [ENNReal.toReal_one, mul_one] using
      regularIsotypicTransform_norm_sq m hm μ η' σ hσ 1 hmap v
  let eval := lp.evalCLM ℂ (fun _ : PontryaginDual J₁ ↦ RegularL2 positiveRealHaar) 2 ω
  have he : MeasurePreserving e (volume : Measure ℝ) positiveRealHaar :=
    ⟨measurable_comap_iff.mpr
      (continuous_real_toNNReal.comp Real.continuous_exp).measurable, rfl⟩
  let E := Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ e he
  let Q := (d : ℂ)⁻¹ • (E.toContinuousLinearMap.comp (eval.comp (T.comp V)))
  refine ⟨Q, ContinuousLinearMap.opNorm_le_bound Q zero_le_one ?_, ?_⟩
  · intro u
    change ‖(d : ℂ)⁻¹ • E (T (V u) ω)‖ ≤ 1 * ‖u‖
    have hdNorm : ‖(d : ℂ)⁻¹‖ = d⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    calc
      _ = d⁻¹ * ‖T (V u) ω‖ :=
        (norm_smul _ _).trans (congrArg₂ (· * ·) hdNorm (E.norm_map _))
      _ ≤ d⁻¹ * ‖T (V u)‖ :=
        mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm two_ne_zero _ ω) (inv_nonneg.mpr hd.le)
      _ = ‖V u‖ := by rw [hTnorm, inv_mul_cancel_left₀ hd.ne']
      _ ≤ 1 * ‖u‖ := (hVnorm u).trans_eq (one_mul _).symm
  · intro u
    have hFiber : ∀ᵐ t ∂positiveRealHaar, ∀ᵐ k ∂η', V u (p (k, t)) = u (p (k, t)) :=
      Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
        (hprod.quasiMeasurePreserving.ae_eq_comp (hV u)))
    have hCoeff : (T (V u) ω : ℝ≥0ˣ → ℂ) =ᵐ[positiveRealHaar]
        fun t ↦ ∫ k : J₁, (ω k : ℂ) * u (p (k, t)) ∂η' := by
      rw [hT]
      filter_upwards [regularIsotypicTransform_ae_eq m hm μ η' σ hσ ω (V u), hFiber]
        with t ht hkt
      calc
        _ = ∫ k : J₁, star (ω k : ℂ) * V u (k.val⁻¹ * σ t) ∂η' := ht
        _ = ∫ k : J₁, (ω k : ℂ) * V u (p (k, t)) ∂η' := by
          symm
          simpa [p, ← Circle.coe_inv_eq_conj] using (integral_inv_eq_self
            (fun k : J₁ ↦ star (ω k : ℂ) * V u (k.val⁻¹ * σ t)) η')
        _ = _ := integral_congr_ae (hkt.mono fun k hk ↦ congrArg ((ω k : ℂ) * ·) hk)
    filter_upwards [Lp.coeFn_smul ((d : ℂ)⁻¹) (E (T (V u) ω)),
      Lp.coeFn_compMeasurePreserving (T (V u) ω) he,
      he.quasiMeasurePreserving.ae_eq_comp hCoeff] with x hx₁ hx₂ hx₃
    change ((d : ℂ)⁻¹ • E (T (V u) ω) : Lp ℂ 2 (volume : Measure ℝ)) x = _
    simp only [Pi.smul_apply, smul_eq_mul] at hx₁
    change E (T (V u) ω) x = T (V u) ω (e x) at hx₂
    change T (V u) ω (e x) = ∫ k : J₁, (ω k : ℂ) * u (p (k, e x)) ∂η' at hx₃
    have hdEq : (d : ℂ)⁻¹ = (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ :=
      congrArg (fun a : ℝ ↦ (Real.sqrt a : ℂ)⁻¹) hmass
    calc
      _ = (d : ℂ)⁻¹ * (∫ k : J₁, (ω k : ℂ) * u (p (k, e x)) ∂η') := by
        rw [hx₁, hx₂, hx₃]
      _ = (d : ℂ)⁻¹ * (∫ k : J₁, (ω k : ℂ) * u (p (k, e x)) ∂η) :=
        congrArg ((d : ℂ)⁻¹ * ·) (hInt _)
      _ = _ := congrArg (fun a : ℂ ↦ a * (∫ k : J₁, (ω k : ℂ) * u (p (k, e x)) ∂η))
        hdEq

/-- A normalized norm-one character coefficient gives a contraction from the
weighted quotient space to flat L² in logarithmic norm coordinates. -/
public theorem exists_sLocalWeightedAngularLogCoefficient {s : ℝ} (hs : 0 ≤ s)
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) (ω : PontryaginDual J₁) :
    let ν := intervalSobolevMeasure μ (logSIdeleQuotientNorm F S) 0 0 s
    let e (x : ℝ) := Units.mk0 (Real.exp x).toNNReal (by positivity)
    ∃ Q : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 (volume : Measure ℝ), ‖Q‖ ≤ 1 ∧
      ∀ u, (Q u : ℝ → ℂ) =ᵐ[volume] fun x ↦
        (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ *
          ∫ h : J₁, (ω h : ℂ) * u (h.val * QuotientGroup.mk (τ (e x))) ∂η :=
  exists_sLocalWeightedAngularLogCoefficient_aux hs τ hτ ω

end

end RiemannMasullo
