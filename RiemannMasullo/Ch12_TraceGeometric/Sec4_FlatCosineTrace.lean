module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatPolarCutoff
public import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertSchmidtProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Finite physical and frequency cutoffs at the rational real-even place

Reconstruction: Theorem 12.4.1.1, Step II, pp. 516–517. This is the unsmoothed
two-cutoff cosine calculation of mrshu, issue #7354, comments 7152127932 and
7153272235, using the positive-ray isometry and cutoffs of PR #7608.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap

namespace RiemannMasullo.FlatPolar

local notation "ν" => volume.restrict (Ioi (0 : ℝ))
local notation "H" => Lp ℂ 2 ν


local notation "Hℝ" => Lp ℂ 2 (volume : Measure ℝ)

/-- On full-line L², inverse Fourier is Fourier followed by reflection. -/
private theorem fourierInv_eq_reflection_fourier (f : Hℝ) :
    𝓕⁻ f = FullLine.dilation (-1) (by norm_num) (𝓕 f) := by
  let P (g : Hℝ) := 𝓕⁻ g = FullLine.dilation (-1) (by norm_num) (𝓕 g)
  apply DenseRange.induction_on (p := P)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq (Lp.fourierTransformₗᵢ ℝ ℂ).symm.continuous
      ((FullLine.dilation (-1) (by norm_num)).continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous)
  intro φ
  change 𝓕⁻ (φ.toLp 2) = FullLine.dilation (-1) (by norm_num) (𝓕 (φ.toLp 2))
  rw [SchwartzMap.toLp_fourierInv_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕⁻ φ).coeFn_toLp 2 volume, FullLine.dilation_apply (-1) (by norm_num) ((𝓕 φ).toLp 2),
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
      ((𝓕 φ).coeFn_toLp 2 volume)] with x hi hd hf
  simp only [Function.comp_apply] at hf
  rw [hi, hd, neg_one_mul, hf]
  simp only [abs_neg, abs_one, Real.sqrt_one, Complex.ofReal_one, one_mul]
  rfl

/-- The normalized positive-ray inverse cosine transform is its own inverse. -/
theorem positiveRayInverseCosine_involutive : Function.Involutive positiveRayInverseCosine := by
  intro f
  apply positiveRayEvenExtension.injective
  rw [positiveRayInverseCosine_evenExtension, positiveRayInverseFourierEmbedding_apply,
    positiveRayInverseCosine_evenExtension, positiveRayInverseFourierEmbedding_apply,
    fourierInv_eq_reflection_fourier (𝓕⁻ _), FourierTransform.fourier_fourierInv_eq]
  apply Lp.ext
  filter_upwards [FullLine.dilation_apply (-1) (by norm_num) (positiveRayEvenExtension f),
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
      (positiveRayEvenExtension_apply f), positiveRayEvenExtension_apply f] with x hd hn hp
  simp only [Function.comp_apply] at hn
  simpa only [hd, abs_neg, abs_one, Real.sqrt_one, Complex.ofReal_one, neg_one_mul, one_mul, hp]
    using hn

/-- The inverse of the positive-ray cosine isometry is the same transform. -/
theorem positiveRayInverseCosineEquiv_symm_apply (f : H) :
    positiveRayInverseCosineEquiv.symm f = positiveRayInverseCosine f := by
  apply positiveRayInverseCosineEquiv.injective
  rw [LinearIsometryEquiv.apply_symm_apply, positiveRayInverseCosineEquiv_apply,
    positiveRayInverseCosine_involutive f]

/-- For integrable square-integrable inputs, inverse Plancherel has its Fourier integral
representative. -/
private theorem fourierInv_L2_coeFn_of_integrable_real (f : Hℝ) (hf : Integrable (f : ℝ → ℂ)) :
    (𝓕⁻ f : Hℝ) =ᵐ[volume] (𝓕⁻ (f : ℝ → ℂ)) := by
  rw [fourierInv_eq_reflection_fourier]
  filter_upwards [FullLine.dilation_apply (-1) (by norm_num) (𝓕 f),
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
      (fourier_L2_coeFn_of_integrable f hf)] with x hd hf'
  simp only [Function.comp_apply] at hf'
  rw [Real.fourierInv_eq_fourier_neg, hd, neg_one_mul, hf']
  simp


/-- On an integrable positive-ray input, the inverse cosine chart has kernel
`2 cos(2πxt)` against ordinary Lebesgue measure on the positive ray. -/
theorem positiveRayInverseCosine_eq_integral (f : H) (hf : Integrable (f : ℝ → ℂ) ν) :
    (positiveRayInverseCosine f : ℝ → ℂ) =ᵐ[ν]
      fun x ↦ ∫ t, (2 : ℂ) * (Real.cos (2 * Real.pi * (t * x)) : ℂ) * f t ∂ν := by
  let d : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)
  have hg : Integrable (positiveRayEvenExtension f : ℝ → ℂ) :=
    ((positiveRay_integrable_abs hf).const_mul d).congr (positiveRayEvenExtension_apply f).symm
  filter_upwards [positiveRayInverseCosine_apply f,
    ae_mono (Measure.restrict_le_self (s := Ioi (0 : ℝ)))
      (fourierInv_L2_coeFn_of_integrable_real _ hg)] with x hx hx'
  rw [hx, hx', Real.fourierInv_eq']
  let k (t : ℝ) : ℂ := Complex.exp ((2 * Real.pi * (t * x) : ℝ) * Complex.I)
  let g (t : ℝ) : ℂ := k t * (d * f |t|)
  have hk (t : ℝ) : ‖k t‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hgi : Integrable g := by
    exact ((positiveRay_integrable_abs hf).const_mul d).bdd_mul
      (by fun_prop : Continuous k).aestronglyMeasurable (.of_forall (fun t ↦ (hk t).le))
  have heq : (∫ t : ℝ, Complex.exp ((2 * Real.pi * (inner ℝ t x) : ℝ) * Complex.I) •
      positiveRayEvenExtension f t) = ∫ t, g t := by
    refine integral_congr_ae ?_
    filter_upwards [positiveRayEvenExtension_apply f] with t ht
    simp only [Real.inner_apply, ht, smul_eq_mul, g, k, d]
  rw [heq, ← intervalIntegral.integral_Iic_add_Ioi (b := 0) hgi.integrableOn hgi.integrableOn]
  have hm : (∫ t in Iic (0 : ℝ), g t) = ∫ t in Ioi (0 : ℝ), g (-t) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi 0 g).symm
  have hn : Integrable (fun t : ℝ ↦ g (-t)) :=
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp hgi.aestronglyMeasurable).mpr hgi
  rw [hm, ← integral_add hn.integrableOn hgi.integrableOn, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
  have hcos : k (-t) + k t = 2 * (Real.cos (2 * Real.pi * (t * x)) : ℂ) := by
    rw [Complex.ofReal_cos]
    simp only [k, neg_mul, mul_neg, Complex.ofReal_neg, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    ring
  have hd : (Real.sqrt 2 : ℂ) * d = 1 := by
    change (Real.sqrt 2 : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1
    rw [Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne')]
  change (Real.sqrt 2 : ℂ) * (g (-t) + g t) = _
  simp only [g, abs_neg, abs_of_pos (show 0 < t from ht), ← add_mul, hcos]
  linear_combination (2 * (Real.cos (2 * Real.pi * (t * x)) : ℂ) * f t) * hd


/-- Kernel of the cut transform `P_(h,L] C D_a P_(j,B]`, where
`D_a f(t) = √a f(at)`. -/
def cutoffCosineDilationKernel (h L j B a : ℝ) (p : ℝ × ℝ) : ℂ :=
  ((Ioc h L) ×ˢ (Ioc j B)).indicator
    (fun z : ℝ × ℝ ↦ (Real.sqrt a⁻¹ : ℂ) * 2 *
      (Real.cos (2 * Real.pi * (z.2 * (a⁻¹ * z.1))) : ℂ)) p

/-- Every finite physical and frequency rectangle gives a square-integrable cosine kernel. -/
theorem memLp_cutoffCosineDilationKernel (h L j B a : ℝ) :
    MemLp (cutoffCosineDilationKernel h L j B a) 2 ((ν).prod ν) := by
  have hb (s t : ℝ) : ν (Ioc s t) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Ioc_subset_Icc_self)
      (isCompact_Icc.measure_lt_top (μ := ν))).ne
  have hr : ((ν).prod ν) ((Ioc h L) ×ˢ (Ioc j B)) ≠ ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (hb h L) (hb j B)
  have hmeas : MeasurableSet ((Ioc h L) ×ˢ (Ioc j B)) := measurableSet_Ioc.prod measurableSet_Ioc
  refine (memLp_indicator_const (μ := (ν).prod ν) 2 hmeas.nullMeasurableSet
    (Real.sqrt a⁻¹ * 2) (.inr hr)).mono' ?_ ?_
  · exact ((by fun_prop : Continuous (fun z : ℝ × ℝ ↦ (Real.sqrt a⁻¹ : ℂ) * 2 *
      (Real.cos (2 * Real.pi * (z.2 * (a⁻¹ * z.1))) : ℂ))).measurable.indicator hmeas).aestronglyMeasurable
  · filter_upwards with z
    by_cases hz : z ∈ (Ioc h L) ×ˢ (Ioc j B)
    · simp only [cutoffCosineDilationKernel, indicator_of_mem hz, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_two]
      exact mul_le_of_le_one_right (by positivity) (abs_le.mpr
        ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    · simp [cutoffCosineDilationKernel, hz]

/-- The genuine Hilbert–Schmidt operator of the two finite cutoffs surrounding the inverse
cosine chart and a dilation. -/
def cutoffCosineDilationHS (h L j B a : ℝ) : hilbertSchmidtOperators H H :=
  integralKernelOperator ν (memLp_cutoffCosineDilationKernel h L j B a).toLp

private theorem integrable_spatialCutoff (h L : ℝ) (f : H) :
    Integrable (spatialCutoff h L f : ℝ → ℂ) ν := by
  refine ((integrable_indicator_iff measurableSet_Ioc).mpr ?_).congr (spatialCutoff_apply h L f).symm
  exact (((Lp.memLp f).locallyIntegrable one_le_two).integrableOn_isCompact isCompact_Icc).mono_set
    Ioc_subset_Icc_self

/-- The square-integrable cosine kernel realizes the actual Plancherel operator with a
physical cutoff, frequency cutoff and normalized dilation. -/
theorem cutoffCosineDilationHS_apply (h L j B a : ℝ) (ha : 0 < a) (f : H) :
    (cutoffCosineDilationHS h L j B a).val f =
      spatialCutoff h L (positiveRayInverseCosine (positiveRayDilation a ha (spatialCutoff j B f))) := by
  let W := spatialCutoff j B f
  let K := (memLp_cutoffCosineDilationKernel h L j B a).toLp
  have hK : (K : ℝ × ℝ → ℂ) =ᵐ[(ν).prod ν] cutoffCosineDilationKernel h L j B a :=
    (memLp_cutoffCosineDilationKernel h L j B a).coeFn_toLp
  have hW := positiveRayInverseCosine_eq_integral W (integrable_spatialCutoff j B f)
  have hrow := (positiveRayScale_quasiMeasurePreserving a⁻¹ (inv_pos.mpr ha)).ae_eq_comp hW
  rw [positiveRayInverseCosine_dilation]
  apply Lp.ext
  filter_upwards [integralKernelOperator_apply ν K f, Measure.ae_ae_of_ae_prod hK, hrow,
    spatialCutoff_apply h L (positiveRayDilation a⁻¹ (inv_pos.mpr ha) (positiveRayInverseCosine W)),
    positiveRayDilation_apply a⁻¹ (inv_pos.mpr ha) (positiveRayInverseCosine W)] with x hi hk hc ho hd
  change (integralKernelOperator ν K).val f x = _
  rw [hi.2, ho]
  by_cases hx : x ∈ Ioc h L
  · simp only [Function.comp_apply] at hc
    rw [indicator_of_mem hx, hd, hc, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hk, spatialCutoff_apply j B f] with t hkt hWt
    change K (x, t) * f t = (Real.sqrt a⁻¹ : ℂ) * (_ * W t)
    unfold W
    rw [hkt, hWt]
    by_cases ht : t ∈ Ioc j B <;>
      simp [cutoffCosineDilationKernel, hx, ht, mul_assoc]
  · rw [indicator_of_notMem hx]
    apply integral_eq_zero_of_ae
    filter_upwards [hk] with t ht
    simp [ht, cutoffCosineDilationKernel, hx]


/-- The full finite-band rational real-even operator before Haar integration in the
dilation parameter.

Reconstruction: Theorem 12.4.1.1, Step II, pp. 516–517, with sharp upper cutoffs on
both copies of the rational positive ray. -/
def finiteCosineTraceOperator (h L j B a : ℝ) : nuclearEndomorphisms H :=
  ⟨(cutoffCosineDilationHS h L j B 1).val.comp (cutoffCosineDilationHS j B h L a).val,
    nuclear_hilbertSchmidt_comp _ _⟩

/-- On each vector the nuclear product is the physical cutoff, inverse cosine transform,
frequency cutoff, inverse cosine transform, normalized dilation, and physical cutoff. -/
theorem finiteCosineTraceOperator_apply (h L j B a : ℝ) (ha : 0 < a) (f : H) :
    (finiteCosineTraceOperator h L j B a).val f =
      spatialCutoff h L (positiveRayInverseCosine (spatialCutoff j B
        (positiveRayInverseCosine (positiveRayDilation a ha (spatialCutoff h L f))))) := by
  have h1 (v : H) : positiveRayDilation 1 zero_lt_one v = v := by
    apply Lp.ext
    simpa using positiveRayDilation_apply 1 zero_lt_one v
  have hP (v : H) : spatialCutoff j B (spatialCutoff j B v) = spatialCutoff j B v := by
    apply Lp.ext
    filter_upwards [spatialCutoff_apply j B (spatialCutoff j B v),
      spatialCutoff_apply j B v] with x hx hv
    by_cases ht : x ∈ Ioc j B <;> simp [hx, hv, ht]
  change (cutoffCosineDilationHS h L j B 1).val ((cutoffCosineDilationHS j B h L a).val f) = _
  rw [cutoffCosineDilationHS_apply _ _ _ _ 1 zero_lt_one, cutoffCosineDilationHS_apply _ _ _ _ a ha,
    h1, hP]

/-- Identification with the adjoint-conjugated spatial cutoff used by the flat polar chart. -/
theorem finiteCosineTraceOperator_eq_chart_apply (h L j B a : ℝ) (ha : 0 < a) (f : H) :
    (finiteCosineTraceOperator h L j B a).val f =
      spatialCutoff h L (spatialCutoffInChart positiveRayInverseCosine j B
        (positiveRayDilation a ha (spatialCutoff h L f))) := by
  rw [finiteCosineTraceOperator_apply _ _ _ _ _ ha, spatialCutoffInChart_inverseCosine]
  change spatialCutoff h L (positiveRayInverseCosine _) =
    spatialCutoff h L (positiveRayInverseCosineEquiv.symm _)
  rw [positiveRayInverseCosineEquiv_symm_apply]
  rfl

/-- The full finite-band trace is the ordinary double Schur integral, with reciprocal
frequency dilation and the coefficient `4/√a`.

Reconstruction: the rational real-even finite Fourier kernel of Theorem 12.4.1.1,
Step II, pp. 516–517, as computed by mrshu in issue #7354. -/
theorem hilbertTrace_finiteCosineTraceOperator (h L j B a : ℝ) (hh : 0 ≤ h) (hj : 0 ≤ j) :
    hilbertTrace (finiteCosineTraceOperator h L j B a) =
      (4 / (Real.sqrt a : ℂ)) * ∫ x in Ioc h L, ∫ s in Ioc j B,
        (Real.cos (2 * Real.pi * (x * s)) : ℂ) * (Real.cos (2 * Real.pi * (x * s / a)) : ℂ) := by
  let A := (memLp_cutoffCosineDilationKernel h L j B 1).toLp
  let D := (memLp_cutoffCosineDilationKernel j B h L a).toLp
  let g (p : ℝ × ℝ) : ℂ := (4 / (Real.sqrt a : ℂ)) *
    ((Real.cos (2 * Real.pi * (p.1 * p.2)) : ℂ) *
      (Real.cos (2 * Real.pi * (p.1 * p.2 / a)) : ℂ))
  let R := Ioc h L ×ˢ Ioc j B
  have hR : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioc
  refine (hilbertTrace_integralKernelOperator_comp_of_hilbertSchmidt ν A D).trans ?_
  have hpoint (p : ℝ × ℝ) :
      cutoffCosineDilationKernel h L j B 1 p * cutoffCosineDilationKernel j B h L a p.swap =
        R.indicator g p := by
    by_cases hx : p.1 ∈ Ioc h L
    · by_cases hs : p.2 ∈ Ioc j B
      · have h₁ : p ∈ Ioc h L ×ˢ Ioc j B := ⟨hx, hs⟩
        have h₂ : p.swap ∈ Ioc j B ×ˢ Ioc h L := ⟨hs, hx⟩
        simp only [cutoffCosineDilationKernel, R, indicator_of_mem h₁, indicator_of_mem h₂,
          g, Prod.fst_swap, Prod.snd_swap, inv_one, Real.sqrt_one, Complex.ofReal_one, one_mul]
        have harg : p.1 * (a⁻¹ * p.2) = p.1 * p.2 / a := by ring
        rw [mul_comm p.2 p.1, harg, Real.sqrt_inv, Complex.ofReal_inv, div_eq_mul_inv]
        ring
      · simp [cutoffCosineDilationKernel, R, hs]
    · simp [cutoffCosineDilationKernel, R, hx]
  have hd := (Measure.measurePreserving_swap (μ := ν) («ν» := ν)).quasiMeasurePreserving.ae_eq_comp
    (memLp_cutoffCosineDilationKernel j B h L a).coeFn_toLp
  have heq : (fun p : ℝ × ℝ ↦ A p * D p.swap) =ᵐ[(ν).prod ν] R.indicator g := by
    filter_upwards [(memLp_cutoffCosineDilationKernel h L j B 1).coeFn_toLp, hd] with p h₁ h₂
    exact (congrArg₂ (· * ·) h₁ h₂).trans (hpoint p)
  have hg : IntegrableOn g R ((ν).prod ν) := by
    apply (integrable_indicator_iff hR).mp
    exact ((memLp_cutoffCosineDilationKernel h L j B 1).integrable_mul
      ((memLp_cutoffCosineDilationKernel j B h L a).comp_measurePreserving
        (Measure.measurePreserving_swap (μ := ν) («ν» := ν)))).congr (.of_forall hpoint)
  have hrest (j U : ℝ) (hj : 0 ≤ j) :
      (ν).restrict (Ioc j U) = volume.restrict (Ioc j U) := by
    rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr]
    exact fun x hx ↦ lt_of_le_of_lt hj hx.1
  rw [integral_congr_ae heq, integral_indicator hR, setIntegral_prod _ hg]
  simp only [hrest _ _ hh, hrest _ _ hj, g, integral_const_mul]


/-- For an outer frequency band `(0,B]` and inner physical interval `(h,L]`, the
trace of `E_B C* M_(h,L] C D_a E_B` is a real double integral in physical-first order.

Reconstruction: the physical-first specialization of the preceding finite-cutoff formula. -/
theorem hilbertTrace_finiteCosine_frequencyBand (h L B a : ℝ) (hh : 0 ≤ h) :
    hilbertTrace (finiteCosineTraceOperator 0 B h L a) =
      ((4 / Real.sqrt a * ∫ x in Ioc h L, ∫ s in Ioc (0 : ℝ) B,
        Real.cos (2 * Real.pi * (x * s)) * Real.cos (2 * Real.pi * (x * s / a)) : ℝ) : ℂ) := by
  let g (s x : ℝ) := Real.cos (2 * Real.pi * (s * x)) * Real.cos (2 * Real.pi * (s * x / a))
  have hi : Integrable (Function.uncurry g)
      ((volume.restrict (Ioc (0 : ℝ) B)).prod (volume.restrict (Ioc h L))) := by
    rw [Measure.prod_restrict]
    have hc : Continuous (Function.uncurry g) := by fun_prop
    exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hswap := integral_integral_swap hi
  calc
    _ = (4 / (Real.sqrt a : ℂ)) * ((∫ s in Ioc (0 : ℝ) B, ∫ x in Ioc h L, g s x : ℝ) : ℂ) := by
      rw [hilbertTrace_finiteCosineTraceOperator _ _ _ _ _ le_rfl hh]
      simp only [g, ← Complex.ofReal_mul, integral_complex_ofReal]
    _ = _ := by
      have hg (s x : ℝ) : g s x =
          Real.cos (2 * Real.pi * (x * s)) * Real.cos (2 * Real.pi * (x * s / a)) := by
        simp only [g, mul_comm s x]
      rw [hswap]
      simp only [hg, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]

end RiemannMasullo.FlatPolar
