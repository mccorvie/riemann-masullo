module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCosineTrace
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-!
# Compact radial tests in the finite real-even cosine trace

Reconstruction for the interval cutoffs in Step II of Theorem 12.4.1.1, pp. 516–517,
using the finite cosine trace in issue #7354 and the compact dilation representation
of PR #7608. The right-hand Hilbert–Schmidt factor is integrated in kernel L².
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology NNReal InnerProductSpace CompactlySupported

namespace RiemannMasullo.FlatPolar

local notation "ν" => volume.restrict (Ioi (0 : ℝ))
local notation "H" => Lp ℂ 2 ν
local notation "K" => Lp ℂ 2 (Measure.prod ν ν)

private theorem compactCosineRatio_pos (a : ℝ≥0ˣ) : 0 < (a.val : ℝ) :=
  NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr a.ne_zero)

private def atomLp (h L j B : ℝ) (a : ℝ≥0ˣ) : K :=
  (memLp_cutoffCosineDilationKernel h L j B a.val).toLp

/-- The kernel depends continuously on its positive dilation parameter in product L². -/
private theorem continuous_atomLp (h L j B : ℝ) : Continuous (atomLp h L j B) := by
  let : FirstCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.firstCountableTopology
  let R := Ioc h L ×ˢ Ioc j B
  let k (a : ℝ≥0ˣ) := cutoffCosineDilationKernel h L j B a.val
  let m (a : ℝ≥0ˣ) := Real.sqrt (a.val : ℝ)⁻¹ * 2
  have hinv : Continuous (fun a : ℝ≥0ˣ ↦ (a.val : ℝ)⁻¹) :=
    (NNReal.continuous_coe.comp Units.continuous_val).inv₀ (fun a ↦ (compactCosineRatio_pos a).ne')
  have hm : Continuous m := (Real.continuous_sqrt.comp hinv).mul continuous_const
  have hR : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioc
  have hfin : (ν).prod ν R ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self))
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top).ne
  have hkpt (p : ℝ × ℝ) : Continuous (fun a ↦ k a p) := by
    by_cases hp : p ∈ R
    · change p ∈ Ioc h L ×ˢ Ioc j B at hp
      simp only [k, cutoffCosineDilationKernel, indicator_of_mem hp]
      fun_prop
    · change p ∉ Ioc h L ×ˢ Ioc j B at hp
      simpa only [k, cutoffCosineDilationKernel, indicator_of_notMem hp] using
        (continuous_const : Continuous (fun _ : ℝ≥0ˣ ↦ (0 : ℂ)))
  have hbound (a : ℝ≥0ˣ) (p : ℝ × ℝ) (hp : p ∈ R) : ‖k a p‖ ≤ m a := by
    change p ∈ Ioc h L ×ˢ Ioc j B at hp
    simp only [k, cutoffCosineDilationKernel, indicator_of_mem hp, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_two, m]
    exact mul_le_of_le_one_right (by positivity) (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  rw [continuous_iff_continuousAt]
  intro a
  let d (b : ℝ≥0ˣ) (p : ℝ × ℝ) := ‖k b p - k a p‖ ^ 2
  have hI : Tendsto (fun b ↦ ∫ p, d b p ∂(ν).prod ν) (𝓝 a) (𝓝 (∫ _p : ℝ × ℝ, (0 : ℝ) ∂(ν).prod ν)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (R.indicator (fun _ ↦ (2 * m a + 1) ^ 2))
    · apply Eventually.of_forall
      intro b
      exact (((memLp_cutoffCosineDilationKernel h L j B b.val).aestronglyMeasurable.sub
        (memLp_cutoffCosineDilationKernel h L j B a.val).aestronglyMeasurable).norm.pow 2)
    · filter_upwards [hm.continuousAt.tendsto.eventually_lt_const (lt_add_one (m a))] with b hb
      filter_upwards with p
      by_cases hp : p ∈ R
      · rw [indicator_of_mem hp, Real.norm_of_nonneg (sq_nonneg _)]
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        exact (norm_sub_le _ _).trans <| (add_le_add (hbound b p hp) (hbound a p hp)).trans (by linarith)
      · rw [indicator_of_notMem hp]
        change p ∉ Ioc h L ×ˢ Ioc j B at hp
        simp [d, k, cutoffCosineDilationKernel, indicator_of_notMem hp]
    · exact (integrable_indicator_iff hR).mpr (integrableOn_const hfin)
    · filter_upwards with p
      have hc : Continuous (fun b ↦ ‖k b p - k a p‖ ^ 2) := ((hkpt p).sub continuous_const).norm.pow 2
      simpa only [d, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using hc.tendsto a
  have heq (b : ℝ≥0ˣ) : ∫ p, d b p ∂(ν).prod ν =
      ‖atomLp h L j B b - atomLp h L j B a‖ ^ 2 := by
    rw [← L2.integral_sq_norm (𝕜 := ℂ)]
    apply integral_congr_ae
    filter_upwards [(memLp_cutoffCosineDilationKernel h L j B b.val).coeFn_toLp,
      (memLp_cutoffCosineDilationKernel h L j B a.val).coeFn_toLp,
      Lp.coeFn_sub (atomLp h L j B b) (atomLp h L j B a)] with p hb ha hs
    exact congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) ((congrArg₂ (· - ·) hb ha).symm.trans hs.symm)
  simp only [heq, integral_zero] at hI
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hI)

private theorem integrable_compactCosineOrbit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (φ : C_c(ℝ≥0ˣ, ℂ)) {f : ℝ≥0ˣ → E} (hf : Continuous f) :
    Integrable (fun a ↦ φ a • f a) positiveRealHaar := by
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  exact (φ.continuous.smul hf).integrable_of_hasCompactSupport φ.hasCompactSupport.smul_right

/-- The product-L² kernel of the right-hand truncated cosine transform after compact
Haar integration in the dilation parameter. -/
def compactCosineDilationKernel (h L j B : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) : K :=
  ∫ a : ℝ≥0ˣ, φ a • (memLp_cutoffCosineDilationKernel h L j B a.val).toLp ∂positiveRealHaar

/-- The map sending a product-L² kernel to its bounded integral operator. -/
private def kernelOperatorCLM : K →L[ℂ] H →L[ℂ] H := by
  let e := (hilbertSchmidtOperators_equiv_Lp_prod ν ν).choose
  let S : K →ₗ[ℂ] K := Lp.compMeasurePreservingₗ ℂ Prod.swap (Measure.measurePreserving_swap (μ := ν) («ν» := ν))
  let T := (hilbertSchmidtOperators H H).subtype.comp (e.toLinearMap.comp S)
  refine T.mkContinuous 1 (fun k ↦ ?_)
  rw [one_mul]
  change ‖(integralKernelOperator ν k).val‖ ≤ ‖k‖
  let A := integralKernelOperator ν k
  have hA : IsCompactOperator A.val ∧ Summable (fun n ↦ approximationNumber A.val n ^ (2 : ℝ)) :=
    A.property
  have h := hA.2.le_tsum 0 (fun n _ ↦ by rw [Real.rpow_two]; positivity)
  rw [approximationNumber_zero_eq_opNorm A.val hA.1, Real.rpow_two] at h
  rw [← schattenNorm_integralKernelOperator ν k]
  change ‖A.val‖ ≤ (∑' n, approximationNumber A.val n ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq (norm_nonneg A.val)]
  exact Real.sqrt_le_sqrt h

/-- Integration of the Hilbert–Schmidt kernels realizes the prescribed integrated
dilation on every L² vector. -/
theorem integralKernelOperator_compactCosineDilationKernel_apply
    (h L j B : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) (f : H) :
    (integralKernelOperator ν (compactCosineDilationKernel h L j B φ)).val f =
      spatialCutoff h L (positiveRayInverseCosine (compactDilationAction φ (spatialCutoff j B f))) := by
  let T := ((ContinuousLinearMap.apply ℂ H) f).comp kernelOperatorCLM
  let U := (spatialCutoff h L).comp positiveRayInverseCosine.toContinuousLinearMap
  let v := spatialCutoff j B f
  let D (a : ℝ≥0ˣ) := positiveRayDilation a.val (compactCosineRatio_pos a) v
  have hD : Continuous D :=
    (positiveRayDilation_continuous v).comp
      ((NNReal.continuous_coe.comp Units.continuous_val).subtype_mk compactCosineRatio_pos)
  change T (∫ a : ℝ≥0ˣ, φ a • atomLp h L j B a ∂positiveRealHaar) =
    U (compactDilationAction φ v)
  rw [compactDilationAction_apply, ← T.integral_comp_comm
    (integrable_compactCosineOrbit φ (continuous_atomLp h L j B)),
    ← U.integral_comp_comm (integrable_compactCosineOrbit φ hD)]
  apply integral_congr_ae
  filter_upwards with a
  simp only [map_smul]
  exact congrArg (φ a • ·) (cutoffCosineDilationHS_apply h L j B a.val (compactCosineRatio_pos a) f)

/-- The nuclear product of the two Hilbert–Schmidt factors in the finite smoothed test. -/
def compactCosineTraceOperator (h L j B : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) : nuclearEndomorphisms H :=
  ⟨(cutoffCosineDilationHS h L j B 1).val.comp
    (integralKernelOperator ν (compactCosineDilationKernel j B h L φ)).val,
    nuclear_hilbertSchmidt_comp _ _⟩

private def kernelTracePair (k : K) : K →L[ℂ] ℂ :=
  (((ContinuousLinearMap.mul ℂ ℂ).lpPairing ((ν).prod ν) 2 2) k).comp
    (Lp.compMeasurePreservingₗᵢ ℂ Prod.swap (Measure.measurePreserving_swap (μ := ν) («ν» := ν))).toContinuousLinearMap

private theorem hilbertTrace_kernelProduct_eq_pair (k l : K) :
    hilbertTrace ⟨(integralKernelOperator ν k).val.comp (integralKernelOperator ν l).val,
      nuclear_hilbertSchmidt_comp _ _⟩ = kernelTracePair k l := by
  rw [hilbertTrace_integralKernelOperator_comp_of_hilbertSchmidt]
  change _ = (((ContinuousLinearMap.mul ℂ ℂ).lpPairing ((ν).prod ν) 2 2) k) _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving l
    (Measure.measurePreserving_swap (μ := ν) («ν» := ν))] with p hp
  exact congrArg (k p * ·) hp.symm

/-- On the positive multiplicative group, the genuine finite trace is continuous in
the dilation parameter. -/
theorem continuous_hilbertTrace_finiteCosineTraceOperator (h L j B : ℝ) :
    Continuous (fun a : ℝ≥0ˣ ↦ hilbertTrace (finiteCosineTraceOperator h L j B a.val)) := by
  let k : K := (memLp_cutoffCosineDilationKernel h L j B 1).toLp
  have heq : (fun a : ℝ≥0ˣ ↦ hilbertTrace (finiteCosineTraceOperator h L j B a.val)) =
      (kernelTracePair k) ∘ (atomLp j B h L) := by
    funext a
    exact hilbertTrace_kernelProduct_eq_pair k (atomLp j B h L a)
  rw [heq]
  exact (kernelTracePair k).continuous.comp (continuous_atomLp j B h L)

/-- For any two finite cutoffs, the actual trace can be integrated in the dilation
parameter against any compactly supported complex test on the positive multiplicative group. -/
theorem hilbertTrace_compactCosineTraceOperator (h L j B : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    hilbertTrace (compactCosineTraceOperator h L j B φ) =
      ∫ a : ℝ≥0ˣ, φ a * hilbertTrace (finiteCosineTraceOperator h L j B a.val) ∂positiveRealHaar := by
  let k : K := (memLp_cutoffCosineDilationKernel h L j B 1).toLp
  change hilbertTrace ⟨(integralKernelOperator ν k).val.comp
    (integralKernelOperator ν (compactCosineDilationKernel j B h L φ)).val, _⟩ = _
  rw [hilbertTrace_kernelProduct_eq_pair]
  change (kernelTracePair k) (∫ a : ℝ≥0ˣ, φ a • atomLp j B h L a ∂positiveRealHaar) = _
  rw [← (kernelTracePair k).integral_comp_comm (integrable_compactCosineOrbit φ (continuous_atomLp j B h L))]
  apply integral_congr_ae
  filter_upwards with a
  rw [map_smul, smul_eq_mul]
  exact congrArg (φ a * ·) (hilbertTrace_kernelProduct_eq_pair k (atomLp j B h L a)).symm


/-- With the outer window taken to be the frequency band, the nuclear product is
the two-sided compression of the actual compact dilation action and the
adjoint-conjugated spatial cutoff. -/
theorem compactCosineTraceOperator_frequencyBand_eq (h L B : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    (compactCosineTraceOperator 0 B h L φ).val =
      (frequencyBand B).starProjection.comp
        ((spatialCutoffInChart positiveRayInverseCosine h L).comp
          ((compactDilationAction φ).comp (frequencyBand B).starProjection)) := by
  have hE (v : H) : (frequencyBand B).starProjection v = spatialCutoff 0 B v :=
    Lp.ext ((frequencyBand_starProjection_ae_eq B v).trans (spatialCutoff_apply 0 B v).symm)
  have h1 (v : H) : positiveRayDilation 1 zero_lt_one v = v := by
    apply Lp.ext
    simpa using positiveRayDilation_apply 1 zero_lt_one v
  have hP (v : H) : spatialCutoff h L (spatialCutoff h L v) = spatialCutoff h L v := by
    apply Lp.ext
    filter_upwards [spatialCutoff_apply h L (spatialCutoff h L v), spatialCutoff_apply h L v]
      with x hx hv
    by_cases ht : x ∈ Ioc h L <;> simp [hx, hv, ht]
  ext f : 1
  change (cutoffCosineDilationHS 0 B h L 1).val
    ((integralKernelOperator ν (compactCosineDilationKernel h L 0 B φ)).val f) = _
  rw [cutoffCosineDilationHS_apply 0 B h L 1 zero_lt_one,
    integralKernelOperator_compactCosineDilationKernel_apply, h1, hP]
  simp only [ContinuousLinearMap.comp_apply, hE, spatialCutoffInChart_inverseCosine]
  change spatialCutoff 0 B (positiveRayInverseCosine _) = spatialCutoff 0 B (positiveRayInverseCosineEquiv.symm _)
  rw [positiveRayInverseCosineEquiv_symm_apply]
  rfl

/-- The two-sided real-even frequency-band compression is nuclear for every compact
complex radial test. Its Hilbert trace integrates the two ordinary real cosine kernels
against ordinary Lebesgue measure in space and frequency and multiplicative Haar in
the radial parameter. Endpoints and the zero test require no separate hypotheses. -/
theorem exists_hilbertTrace_compactDilation_cosine_frequencyBand
    (h L B : ℝ) (hh : 0 ≤ h) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    let E := (frequencyBand B).starProjection
    let T := E.comp ((spatialCutoffInChart positiveRayInverseCosine h L).comp
      ((compactDilationAction φ).comp E))
    ∃ hn : IsNuclearOperator T, hilbertTrace ⟨T, hn⟩ =
      ∫ a : ℝ≥0ˣ, φ a * ((4 / Real.sqrt a.val * ∫ x in Ioc h L, ∫ t in Ioc (0 : ℝ) B,
        Real.cos (2 * Real.pi * (x * t)) * Real.cos (2 * Real.pi * (x * t / a.val)) : ℝ) : ℂ)
        ∂positiveRealHaar := by
  dsimp only
  rw [← compactCosineTraceOperator_frequencyBand_eq]
  refine ⟨(compactCosineTraceOperator 0 B h L φ).property, ?_⟩
  change hilbertTrace (compactCosineTraceOperator 0 B h L φ) = _
  rw [hilbertTrace_compactCosineTraceOperator]
  apply integral_congr_ae
  filter_upwards with a
  rw [hilbertTrace_finiteCosine_frequencyBand _ _ _ _ hh]

end RiemannMasullo.FlatPolar
