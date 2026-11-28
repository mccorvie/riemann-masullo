module

public import RiemannMasullo.AppC_LCTVS.Sec3b
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_AnnularProjectionDefect
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Representative-preserving density change on a fixed spatial window -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace NNReal

namespace RiemannMasullo

variable {X : Type*} [MeasurableSpace X]

/-- Inclusion into the smaller measure preserves the underlying function.
Equivalent null sets make this inclusion injective. -/
theorem exists_l2Inclusion_of_measure_le {μ ν : Measure X} (hμν : μ ≤ ν) (hνμ : ν ≪ μ) :
    ∃ J : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ,
      Function.Injective J ∧ ‖J‖ ≤ 1 ∧
        ∀ f, (J f : X → ℂ) =ᵐ[μ] (f : X → ℂ) := by
  let mem (f : Lp ℂ 2 ν) : MemLp (f : X → ℂ) 2 μ := (Lp.memLp f).mono_measure hμν
  let I : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun f ↦ (mem f).toLp f
      map_add' f g :=
        (MemLp.toLp_congr (mem (f + g)) ((mem f).add (mem g))
          (ae_mono hμν (Lp.coeFn_add f g))).trans (MemLp.toLp_add (mem f) (mem g))
      map_smul' c f :=
        (MemLp.toLp_congr (mem (c • f)) ((mem f).const_smul c)
          (ae_mono hμν (Lp.coeFn_smul c f))).trans (MemLp.toLp_const_smul c (mem f)) }
  have hI (f : Lp ℂ 2 ν) : ‖I f‖ ≤ 1 * ‖f‖ := by
    change ‖(mem f).toLp f‖ ≤ 1 * ‖f‖
    rw [one_mul, Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_lt_top.ne (eLpNorm_mono_measure _ hμν)
  let J := I.mkContinuous 1 hI
  have hJ (f : Lp ℂ 2 ν) : (J f : X → ℂ) =ᵐ[μ] f := (mem f).coeFn_toLp
  refine ⟨J, ?_, I.mkContinuous_norm_le zero_le_one hI, hJ⟩
  intro f g hfg
  exact Lp.ext (hνμ.ae_eq ((hJ f).symm.trans (hfg ▸ hJ g)))

/-- The adjoint of the inclusion into flat L² divides representatives by the
original density. -/
theorem l2Inclusion_adjoint_withDensity_ae_eq
    (μ : Measure X)
    (w : X → ℝ≥0) (hw : Measurable w) (hw₁ : ∀ x, 1 ≤ w x)
    (ν : Measure X) (hν : ν = μ.withDensity (fun x ↦ (w x : ℝ≥0∞)))
    (J : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ)
    (hJ : ∀ f, (J f : X → ℂ) =ᵐ[μ] (f : X → ℂ)) (g : Lp ℂ 2 μ) :
    (J.adjoint g : X → ℂ) =ᵐ[ν] fun x ↦ g x / (w x : ℂ) := by
  subst ν
  let v : X → ℂ := fun x ↦ g x / (w x : ℂ)
  have hreal : Measurable fun x ↦ (w x : ℝ) := measurable_coe_nnreal_real.comp hw
  have hv : StronglyMeasurable v := (Lp.stronglyMeasurable g).div
    (Complex.measurable_ofReal.comp hreal).stronglyMeasurable
  have hpos (x : X) : 0 < (w x : ℝ) := by exact_mod_cast zero_lt_one.trans_le (hw₁ x)
  have hmem : MemLp v 2 (μ.withDensity (fun x ↦ (w x : ℝ≥0∞))) := by
    rw [memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable,
      integrable_withDensity_iff_integrable_smul hw]
    have hflat := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
    refine hflat.mono' (hw.stronglyMeasurable.smul (hv.norm.pow 2)).aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    simp only [v, NNReal.smul_def, smul_eq_mul, norm_mul, Real.norm_eq_abs,
      NNReal.abs_eq, norm_div, Complex.norm_real, div_pow]
    have hwR : (1 : ℝ) ≤ (w x : ℝ) := by exact_mod_cast hw₁ x
    rw [abs_of_nonneg (sq_nonneg ‖g x‖), abs_of_nonneg (sq_nonneg (w x : ℝ))]
    rw [show (w x : ℝ) * (‖g x‖ ^ 2 / (w x : ℝ) ^ 2) =
      ‖g x‖ ^ 2 / (w x : ℝ) by field_simp]
    exact div_le_self (sq_nonneg _) hwR
  have hμ : μ ≪ μ.withDensity (fun x ↦ (w x : ℝ≥0∞)) :=
    withDensity_absolutelyContinuous' hw.coe_nnreal_ennreal.aemeasurable
      (ae_of_all _ fun x ↦ by exact_mod_cast (hpos x).ne')
  have hmult (x : X) : (w x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos x).ne'
  have heq : J.adjoint g = hmem.toLp v := by
    apply ext_inner_right ℂ
    intro f
    rw [J.adjoint_inner_left, L2.inner_def, L2.inner_def,
      integral_withDensity_eq_integral_smul hw]
    apply integral_congr_ae
    filter_upwards [hJ f, hμ.ae_eq hmem.coeFn_toLp] with x hx hrep
    rw [hx, hrep]
    simp only [v, NNReal.smul_def, RCLike.inner_apply, map_div₀, Complex.conj_ofReal,
      Complex.real_smul]
    field_simp [hmult x]
  rw [heq]
  exact hmem.coeFn_toLp

/-- A region on which the density is bounded admits a bounded lift from
unweighted functions to weighted functions restricted to that region. -/
theorem exists_l2IndicatorLift_of_restrict_le {μ ν : Measure X} (hνμ : ν ≪ μ)
    {Z : Set X} (hZ : MeasurableSet Z) {C : ℝ≥0} (hBound : ν.restrict Z ≤ (C : ℝ≥0∞) • μ) :
    ∃ L : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν,
      ∀ f, (L f : X → ℂ) =ᵐ[ν] Z.indicator (f : X → ℂ) := by
  let mem (f : Lp ℂ 2 μ) : MemLp (Z.indicator (f : X → ℂ)) 2 ν :=
    (memLp_indicator_iff_restrict hZ.nullMeasurableSet).mpr
      ((Lp.memLp f).of_measure_le_smul ENNReal.coe_ne_top hBound)
  let I : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun f ↦ (mem f).toLp (Z.indicator f)
      map_add' f g := by
        refine (MemLp.toLp_congr (mem (f + g)) ((mem f).add (mem g)) ?_).trans
          (MemLp.toLp_add (mem f) (mem g))
        filter_upwards [hνμ.ae_eq (Lp.coeFn_add f g)] with x hx
        by_cases h : x ∈ Z
        · simpa only [Pi.add_apply, indicator_of_mem h] using hx
        · simp [h]
      map_smul' c f := by
        refine (MemLp.toLp_congr (mem (c • f)) ((mem f).const_smul c) ?_).trans
          (MemLp.toLp_const_smul c (mem f))
        filter_upwards [hνμ.ae_eq (Lp.coeFn_smul c f)] with x hx
        by_cases h : x ∈ Z
        · simpa only [Pi.smul_apply, indicator_of_mem h] using hx
        · simp [h] }
  let K : ℝ≥0∞ := (C : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal
  have hK : K ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.coe_ne_top
  have hI (f : Lp ℂ 2 μ) : ‖I f‖ ≤ K.toReal * ‖f‖ := by
    change ‖(mem f).toLp (Z.indicator f)‖ ≤ K.toReal * ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_indicator_eq_eLpNorm_restrict hZ.nullMeasurableSet,
      ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hK (Lp.memLp f).eLpNorm_lt_top.ne)
      (eLpNorm_le_of_measure_le_smul hBound)
  let L := I.mkContinuous K.toReal hI
  exact ⟨L, fun f ↦ (mem f).coeFn_toLp⟩

section Kernel

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [BorelSpace X]

/-- A Hilbert–Schmidt operator applies to any representatives of its kernel and input. -/
theorem integralKernelOperator_apply_representatives
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [Measure.InnerRegular ν]
    {K : X × X → ℂ} (hK : MemLp K 2 (ν.prod ν)) (U : Lp ℂ 2 ν)
    {u : X → ℂ} (hu : (U : X → ℂ) =ᵐ[ν] u) :
    let T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν := (integralKernelOperator ν (hK.toLp K)).val
    ∀ᵐ x ∂ν, Integrable (fun y ↦ K (x, y) * u y) ν ∧
      T U x = ∫ y, K (x, y) * u y ∂ν := by
  intro T
  filter_upwards [integralKernelOperator_apply ν (hK.toLp K) U,
    Measure.ae_ae_of_ae_prod hK.coeFn_toLp] with x hx hkx
  have hrow : (fun y ↦ (hK.toLp K) (x, y) * U y) =ᵐ[ν] fun y ↦ K (x, y) * u y := by
    filter_upwards [hkx, hu] with y hky huy
    rw [hky, huy]
  exact ⟨hx.1.congr hrow, hx.2.trans (integral_congr_ae hrow)⟩

/-- Under a positive density change, an annular integral operator is the
unweighted operator on the same input function followed by the bounded
annular lift. The weighted kernel divides its input coordinate by the density. -/
theorem integralKernelOperator_withDensity_eq_annularLift
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [Measure.InnerRegular μ]
    (w : X → ℝ≥0) (hw : Measurable w) (hw₀ : ∀ x, w x ≠ 0)
    {Z : Set X} (K : X × X → ℂ) (hK : MemLp K 2 (μ.prod μ))
    (hZK : ∀ x ∉ Z, ∀ y, K (x, y) = 0) :
    let ν := μ.withDensity (fun x ↦ (w x : ℝ≥0∞))
    let Kν (p : X × X) := K p / ((w p.2 : ℝ) : ℂ)
    ∀ [IsFiniteMeasureOnCompacts ν] [Measure.InnerRegular ν],
    ∀ (hKν : MemLp Kν 2 (ν.prod ν))
      (J : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) (L : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν),
      (∀ f, (J f : X → ℂ) =ᵐ[μ] (f : X → ℂ)) →
      (∀ f, (L f : X → ℂ) =ᵐ[ν] Z.indicator (f : X → ℂ)) →
      let A := (integralKernelOperator μ (hK.toLp K)).val
      (integralKernelOperator ν (hKν.toLp Kν)).val = (L.comp A).comp J := by
  intro ν Kν _ _ hKν J L hJ hL A
  let B := (integralKernelOperator ν (hKν.toLp Kν)).val
  have hνμ : ν ≪ μ := withDensity_absolutelyContinuous _ _
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  change (B f : X → ℂ) =ᵐ[ν] (L (A (J f)) : X → ℂ)
  have hRowμ := integralKernelOperator_apply_representatives μ hK (J f) (hJ f)
  have hRowν := integralKernelOperator_apply_representatives ν hKν f (EventuallyEq.rfl)
  filter_upwards [hRowν, hνμ.ae_le hRowμ, hL (A (J f))] with x hxν hxμ hxL
  have hrow : (∫ y, Kν (x, y) * f y ∂ν) = ∫ y, K (x, y) * f y ∂μ := by
    change (∫ y, Kν (x, y) * f y ∂(μ.withDensity (fun y ↦ (w y : ℝ≥0∞)))) = _
    rw [integral_withDensity_eq_integral_smul hw]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    have hwy : ((w y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by exact_mod_cast hw₀ y)
    change ((w y : ℝ) : ℂ) * (K (x, y) / ((w y : ℝ) : ℂ) * f y) = K (x, y) * f y
    field_simp
  rw [hxν.2, hrow, hxL]
  by_cases hx : x ∈ Z
  · rw [indicator_of_mem hx]
    exact hxμ.2.symm
  · rw [indicator_of_notMem hx]
    simp only [hZK x hx, zero_mul, integral_zero]

/-- The inclusion followed by the annular lift acts as the identity on the
output of an order-zero kernel supported inside the spatial window. -/
theorem integralKernelOperator_annularLift_output
    (μ ν : Measure X) [IsFiniteMeasureOnCompacts μ] [Measure.InnerRegular μ] (hμν : μ ≪ ν)
    {Z : Set X} (K : X × X → ℂ) (hK : MemLp K 2 (μ.prod μ))
    (hZK : ∀ x ∉ Z, ∀ y, K (x, y) = 0)
    (J : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) (L : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν)
    (hJ : ∀ f, (J f : X → ℂ) =ᵐ[μ] (f : X → ℂ))
    (hL : ∀ f, (L f : X → ℂ) =ᵐ[ν] Z.indicator (f : X → ℂ)) :
    let A := (integralKernelOperator μ (hK.toLp K)).val
    (J.comp L) * A = A := by
  intro A
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  change (J (L (A f)) : X → ℂ) =ᵐ[μ] (A f : X → ℂ)
  have hRow := integralKernelOperator_apply_representatives μ hK f (EventuallyEq.rfl)
  filter_upwards [hJ (L (A f)), hμν.ae_eq (hL (A f)), hRow] with x hxJ hxL hxRow
  rw [hxJ, hxL]
  by_cases hx : x ∈ Z
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, hxRow.2]
    simp only [hZK x hx, zero_mul, integral_zero]

/-- At a compact output window, a continuous density at least one admits
both a contractive inclusion and a bounded spatially restricted lift. -/
theorem exists_l2DensityInclusion_and_compactLift (μ : Measure X)
    (w : X → ℝ≥0) (hw : Continuous w) (hw₁ : ∀ x, 1 ≤ w x)
    {Z : Set X} (hZ : IsCompact Z) :
    let ν := μ.withDensity (fun x ↦ (w x : ℝ≥0∞))
    ∃ (J : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) (L : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν),
      Function.Injective J ∧ μ ≪ ν ∧ ‖J‖ ≤ 1 ∧
      (∀ f, (J f : X → ℂ) =ᵐ[μ] (f : X → ℂ)) ∧
      ∀ f, (L f : X → ℂ) =ᵐ[ν] Z.indicator (f : X → ℂ) := by
  intro ν
  have hμν : μ ≤ ν := by
    calc
      μ = μ.withDensity 1 := withDensity_one.symm
      _ ≤ ν := withDensity_mono (ae_of_all _ fun x ↦ by
        simpa only [Pi.one_apply, ENNReal.coe_one] using ENNReal.coe_le_coe.mpr (hw₁ x))
  have hνμ : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have hwR : Continuous (fun x ↦ (w x : ℝ)) := NNReal.continuous_coe.comp hw
  obtain ⟨B, hB⟩ := hZ.exists_bound_of_continuousOn hwR.continuousOn
  let C : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hBound : ν.restrict Z ≤ (C : ℝ≥0∞) • μ := by
    rw [restrict_withDensity hZ.measurableSet]
    calc
      _ ≤ (μ.restrict Z).withDensity (fun _ ↦ (C : ℝ≥0∞)) := by
        apply withDensity_mono
        filter_upwards [ae_restrict_mem hZ.measurableSet] with x hx
        apply ENNReal.coe_le_coe.mpr
        change (w x : ℝ) ≤ max B 0
        simpa only [Real.norm_eq_abs, abs_of_nonneg (w x).coe_nonneg] using
          (hB x hx).trans (le_max_left B 0)
      _ = (C : ℝ≥0∞) • μ.restrict Z := withDensity_const _
      _ ≤ (C : ℝ≥0∞) • μ := by gcongr; exact Measure.restrict_le_self
  obtain ⟨J, hJinj, hJnorm, hJ⟩ := exists_l2Inclusion_of_measure_le hμν hνμ
  obtain ⟨L, hL⟩ := exists_l2IndicatorLift_of_restrict_le hνμ hZ.measurableSet hBound
  exact ⟨J, L, hJinj, Measure.absolutelyContinuous_of_le hμν, hJnorm, hJ, hL⟩

/-- The weighted compression of a nuclear annular kernel has the original
trace plus a term measuring how the two Hilbert-space projections differ
under the representative-preserving inclusion. -/
theorem hilbertTrace_weightedAnnularKernel_compress_eq
    (μ ν : Measure X) [IsFiniteMeasureOnCompacts μ] [Measure.InnerRegular μ]
    [IsFiniteMeasureOnCompacts ν] [Measure.InnerRegular ν]
    (w : X → ℝ≥0) (hw : Continuous w) (hw₁ : ∀ x, 1 ≤ w x)
    (hν : ν = μ.withDensity (fun x ↦ (w x : ℝ≥0∞)))
    {Z : Set X} (hZ : IsCompact Z)
    (K : X × X → ℂ) (hK : MemLp K 2 (μ.prod μ))
    (hZK : ∀ x ∉ Z, ∀ y, K (x, y) = 0)
    (hA : IsNuclearOperator (integralKernelOperator μ (hK.toLp K)).val) :
    let Kν (p : X × X) := K p / ((w p.2 : ℝ) : ℂ)
    ∀ (hKν : MemLp Kν 2 (ν.prod ν))
      (P : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (_hP : P * P = P)
      (Q : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ),
      let A : nuclearEndomorphisms (Lp ℂ 2 μ) :=
        ⟨(integralKernelOperator μ (hK.toLp K)).val, hA⟩
      A.val * Q = A.val →
      let B := (integralKernelOperator ν (hKν.toLp Kν)).val
      ∃ (J : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) (L : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν)
        (hB : IsNuclearOperator B),
        (∀ f, (J f : X → ℂ) =ᵐ[μ] (f : X → ℂ)) ∧
        (∀ f, (L f : X → ℂ) =ᵐ[ν] Z.indicator (f : X → ℂ)) ∧
        let D := (J.comp P - Q.comp J).comp L
        hilbertTrace (Isolated.nuclearCompress P ⟨B, hB⟩) = hilbertTrace A +
          hilbertTrace ⟨D * A.val, mul_mem_nuclearEndomorphisms_left D A⟩ := by
  subst ν
  intro Kν hKν P hP Q A hQ B
  obtain ⟨J, L, hJinj, hμν, _, hJ, hL⟩ :=
    exists_l2DensityInclusion_and_compactLift μ w hw hw₁ hZ
  have hw₀ (x : X) : w x ≠ 0 := ne_of_gt (zero_lt_one.trans_le (hw₁ x))
  have hOutput : (J.comp L) * A.val = A.val :=
    integralKernelOperator_annularLift_output μ _ hμν K hK hZK J L hJ hL
  have hFactor : B = (L.comp A.val).comp J :=
    integralKernelOperator_withDensity_eq_annularLift μ w hw.measurable hw₀ K hK hZK hKν J L hJ hL
  obtain ⟨hN, hTrace⟩ :=
    hilbertTrace_nuclearCompress_eq_add_projectionDefect J hJinj L P hP Q A hQ hOutput
  have hB : IsNuclearOperator B := hFactor ▸ hN
  have hBundle : (⟨B, hB⟩ : nuclearEndomorphisms _) = ⟨_, hN⟩ := Subtype.ext hFactor
  refine ⟨J, L, hB, hJ, hL, ?_⟩
  rw [hBundle]
  exact hTrace

end Kernel

end RiemannMasullo
