module

public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Smooth densities from stretched exponential characteristic-function decay -/

open MeasureTheory Filter Set Real
open scoped FourierTransform Topology RealInnerProductSpace SchwartzMap

@[expose] public noncomputable section

namespace RiemannMasullo

private theorem integrable_pow_exp_neg_sqrt (c : ℝ) (hc : 0 < c) (n : ℕ) :
    Integrable (fun x : ℝ ↦ |x| ^ n * Real.exp (-c * Real.sqrt |x|)) := by
  have H : IntegrableOn (fun x : ℝ ↦ |x| ^ n * Real.exp (-c * Real.sqrt |x|)) (Ioi 0) := by
    apply (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1 / 2)
      (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by norm_num) hc).congr_fun _ measurableSet_Ioi
    intro x hx
    simp only [abs_of_pos (mem_Ioi.mp hx), Real.sqrt_eq_rpow, Real.rpow_natCast]
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ)), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, H⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa [Function.comp_def, neg_preimage, neg_Iio] using H

private theorem integrable_fourier_moments {P : ℝ → ℂ} (hP : Measurable P)
    {C c : ℝ} (hc : 0 < c) (hbd : ∀ t, ‖P t‖ ≤ C * Real.exp (-c * Real.sqrt |t|))
    (n : ℕ) : Integrable (fun t : ℝ ↦ ‖t‖ ^ n * ‖P t‖) := by
  apply ((integrable_pow_exp_neg_sqrt c hc n).const_mul C).mono'
  · fun_prop
  · filter_upwards with t
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ ‖t‖ ^ n * ‖P t‖), Real.norm_eq_abs]
    simpa [mul_left_comm, mul_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left (hbd t) (pow_nonneg (abs_nonneg t) n)

/-- The inverse density is smooth because the Fourier-side majorant has every polynomial moment. -/
theorem contDiff_fourier_of_sqrt_exp_bound {P : ℝ → ℂ} (hP : Measurable P)
    {C c : ℝ} (hc : 0 < c) (hbd : ∀ t, ‖P t‖ ≤ C * Real.exp (-c * Real.sqrt |t|)) :
    ContDiff ℝ (⊤ : ℕ∞) (𝓕 P) :=
  Real.contDiff_fourier fun n _ ↦ integrable_fourier_moments hP hc hbd n

private theorem integral_fourier_self {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ x : ℝ, 𝓕 f x * g x) = ∫ x : ℝ, f x * 𝓕 g x := by
  simpa [Algebra.smul_def, FourierTransform.fourier, Real.instFourierTransform] using
    (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ) Real.continuous_fourierChar
      continuous_inner hf hg)

private theorem integral_fourierInv_self {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ x : ℝ, 𝓕⁻ f x * g x) = ∫ x : ℝ, f x * 𝓕⁻ g x := by
  have hflip : (-innerₗ ℝ).flip = -innerₗ ℝ := by ext; simp
  simpa [Algebra.smul_def, FourierTransformInv.fourierInv, Real.instFourierTransformInv, hflip] using
    (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner.neg hf hg)

/-- Almost-everywhere inversion for an integrable function and its integrable inverse transform. -/
theorem ae_fourier_fourierInv_of_integrable {f : ℝ → ℂ} (hf : Integrable f)
    (hF : Integrable (𝓕⁻ f)) : 𝓕 (𝓕⁻ f) =ᵐ[volume] f := by
  have hcont : Continuous (𝓕 (𝓕⁻ f)) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (μ := volume) (innerSL ℝ).continuous₂ hF
  apply ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable hf.locallyIntegrable
  intro u hu huc
  let U : 𝓢(ℝ, ℂ) := (huc.comp_left (g := Complex.ofReal) Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hu)
  have huU : (U : ℝ → ℂ) = (fun x ↦ (u x : ℂ)) := rfl
  have hh := integral_fourier_self hF U.integrable
  have hh' := integral_fourierInv_self hf (𝓕 U).integrable
  have H : 𝓕⁻ (𝓕 (U : ℝ → ℂ)) = (U : ℝ → ℂ) :=
    U.continuous.fourierInv_fourier_eq U.integrable (𝓕 U).integrable
  change (∫ x : ℝ, 𝓕⁻ f x * 𝓕 (U : ℝ → ℂ) x) =
    ∫ x : ℝ, f x * 𝓕⁻ (𝓕 (U : ℝ → ℂ)) x at hh'
  rw [H] at hh'
  simpa [huU, Complex.real_smul, smul_eq_mul, mul_comm] using hh.trans hh'

private theorem scaled_charFun_eq_fourierInv_rnDeriv (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) :
    (fun t : ℝ ↦ charFun μ (2 * π * t)) =
      𝓕⁻ (fun x : ℝ ↦ ((μ.rnDeriv volume x).toReal : ℂ)) := by
  funext t
  rw [Real.fourierInv_eq', charFun_apply_real, ← integral_rnDeriv_smul hμ]
  apply integral_congr_ae
  filter_upwards with x
  simp [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]

/-- For an absolutely continuous probability on the unit interval, stretched exponential
decay of its characteristic function gives a smooth, nonnegative, compactly supported
probability density and equality with all integrals against the original law. -/
theorem exists_smooth_density_of_charFun_sqrt_exp
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    (hmass : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hbd : ∀ t : ℝ, ‖charFun μ t‖ ≤ C * Real.exp (-c * Real.sqrt |t|)) :
    ∃ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ x, 0 ≤ g x) ∧
      tsupport g ⊆ Icc (-1 : ℝ) 1 ∧ (∫ x : ℝ, g x) = 1 ∧
      volume.withDensity (fun x ↦ ENNReal.ofReal (g x)) = μ ∧
      (μ.map Neg.neg = μ → Function.Even g) ∧
      ∀ f : ℝ → ℂ, (∫ x : ℝ, (g x : ℂ) * f x) = ∫ x : ℝ, f x ∂μ := by
  let P : ℝ → ℂ := fun t ↦ charFun μ (2 * π * t)
  let F : ℝ → ℂ := fun x ↦ ((μ.rnDeriv volume x).toReal : ℂ)
  have hP : Measurable P := measurable_charFun.comp (by fun_prop)
  have hPF : P = 𝓕⁻ F := scaled_charFun_eq_fourierInv_rnDeriv μ hμ
  have hdec (t : ℝ) : ‖P t‖ ≤ C * Real.exp (-c * Real.sqrt |t|) := by
    apply (hbd (2 * π * t)).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hc.le)
    apply Real.sqrt_le_sqrt
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * π)]
    nlinarith [mul_le_mul_of_nonneg_right (by linarith [one_le_pi_div_two] : 1 ≤ 2 * π)
      (abs_nonneg t)]
  have hsm := contDiff_fourier_of_sqrt_exp_bound hP hc hdec
  let g (x : ℝ) : ℝ := (𝓕 P x).re
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := Complex.reCLM.contDiff.comp hsm
  have hPi : Integrable P := (integrable_norm_iff hP.aestronglyMeasurable).mp
    (by simpa using integrable_fourier_moments hP hc hdec 0)
  have hFi : Integrable F :=
    (integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv μ volume).aemeasurable
      (Measure.lintegral_rnDeriv_lt_top μ volume).ne).ofReal
  have haec : 𝓕 P =ᵐ[volume] F := by
    rw [hPF] at hPi ⊢
    exact ae_fourier_fourierInv_of_integrable hFi hPi
  have hae : g =ᵐ[volume] (fun x ↦ (μ.rnDeriv volume x).toReal) := by
    filter_upwards [haec] with x hx using congrArg Complex.re hx
  have hpos : (fun x ↦ max (g x) 0) = g := by
    apply Measure.eq_of_ae_eq (μ := volume) _ (hgs.continuous.max continuous_const) hgs.continuous
    filter_upwards [hae] with x hx
    simp [hx]
  have hgc : EqOn g 0 (Icc (-1 : ℝ) 1)ᶜ := by
    apply Measure.eqOn_open_of_ae_eq (μ := volume) _ isClosed_Icc.isOpen_compl
      hgs.continuous.continuousOn continuous_zero.continuousOn
    change ∀ᵐ x ∂volume.restrict (Icc (-1 : ℝ) 1)ᶜ, g x = 0
    rw [ae_restrict_iff' isClosed_Icc.isOpen_compl.measurableSet]
    filter_upwards [hae, Measure.ae_rnDeriv_ne_zero_imp_of_ae volume hmass] with x hx hx' ho
    have h0 : μ.rnDeriv volume x = 0 := by
      by_contra h
      exact ho (hx' h)
    simpa [h0] using hx
  have hsup : tsupport g ⊆ Icc (-1 : ℝ) 1 := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra h
    exact hx (hgc h)
  refine ⟨g, hgs, (fun x ↦ (le_max_right (g x) 0).trans_eq (congrFun hpos x)), hsup, ?_, ?_, ?_, ?_⟩
  · rw [integral_congr_ae hae, Measure.integral_toReal_rnDeriv hμ]
    simp
  · refine (withDensity_congr_ae ?_).trans (Measure.withDensity_rnDeriv_eq μ volume hμ)
    filter_upwards [hae, Measure.rnDeriv_lt_top μ volume] with x hx hfin
    simpa [hx] using ENNReal.ofReal_toReal hfin.ne
  · intro hsym x
    have hPem : P ∘ (LinearIsometryEquiv.neg ℝ (E := ℝ)) = P := by
      funext t
      have hneg := charFun_map_mul (μ := μ) (-1) (2 * π * t)
      simpa [P, Function.comp_def, hsym, mul_neg] using hneg.symm
    exact congrArg Complex.re
      ((Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ)) P x).symm.trans
        (congrArg (fun Q : ℝ → ℂ ↦ 𝓕 Q x) hPem))
  · intro f
    rw [← integral_rnDeriv_smul hμ]
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    simp [hx, Algebra.smul_def]

end RiemannMasullo
