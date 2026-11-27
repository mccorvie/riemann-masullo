module

public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # Smoothing sharp interval cutoffs

A fixed convolution kernel of mass one smooths the interval cutoff without changing
its pointwise limit. The error has a uniform supremum bound and an `L¹` bound
controlled by the first absolute moment of the kernel.
-/

open Filter MeasureTheory Set Topology
open scoped Convolution FourierTransform SchwartzMap

@[expose] public noncomputable section

namespace RiemannMasullo

/-- The sharp symmetric interval cutoff, as a complex-valued function. -/
def sharpIntervalMask (L : ℝ) : ℝ → ℂ := (Icc (-L) L).indicator 1

/-- The sharp interval cutoff convolved with a fixed smoothing kernel. -/
def smoothIntervalMask (η : ℝ → ℂ) (L x : ℝ) : ℂ :=
  (η ⋆[ContinuousLinearMap.mul ℂ ℂ] sharpIntervalMask L) x

/-- The sharp interval cutoff is integrable for every finite radius. -/
theorem integrable_sharpIntervalMask (L : ℝ) : Integrable (sharpIntervalMask L) := by
  rw [sharpIntervalMask, integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (by simp [Real.volume_Icc])

/-- Smoothing a finite interval by an integrable kernel is integrable. -/
theorem integrable_smoothIntervalMask (η : ℝ → ℂ) (hη : Integrable η) (L : ℝ) :
    Integrable (smoothIntervalMask η L) :=
  hη.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (integrable_sharpIntervalMask L)

/-- Smoothing a symmetric interval by an even kernel gives an even function. -/
theorem smoothIntervalMask_even (η : ℝ → ℂ) (hη : Function.Even η) (L : ℝ) :
    Function.Even (smoothIntervalMask η L) := by
  have hmask : Function.Even (sharpIntervalMask L) := by
    intro x
    have hmem : -x ∈ Icc (-L) L ↔ x ∈ Icc (-L) L := by
      simp only [mem_Icc]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    by_cases h : x ∈ Icc (-L) L <;> simp [sharpIntervalMask, h, hmem]
  intro x
  exact convolution_neg_of_neg_eq (ContinuousLinearMap.mul ℂ ℂ) (ae_of_all _ hη) (ae_of_all _ hmask)

/-- Smoothing the interval cutoff preserves the Fourier support bound of the kernel. -/
theorem fourier_smoothIntervalMask_eq_mul (η : ℝ → ℂ) (hη : Integrable η) (L ξ : ℝ) :
    𝓕 (smoothIntervalMask η L) ξ = 𝓕 η ξ * 𝓕 (sharpIntervalMask L) ξ :=
  Real.fourier_mul_convolution_eq hη (integrable_sharpIntervalMask L) ξ

/-- Every positive bandwidth admits an even Schwartz smoothing kernel of mass one.
Such a kernel has a finite first absolute moment. -/
theorem exists_evenSchwartz_smoothingKernel (c : ℝ) (hc : 0 < c) :
    ∃ η : 𝓢(ℝ, ℂ), Function.Even (η : ℝ → ℂ) ∧ (∫ x, η x) = 1 ∧
      Function.support (𝓕 (η : ℝ → ℂ)) ⊆ Icc (-c) c ∧
      Integrable (fun t ↦ |t| * ‖η t‖) := by
  let b : ContDiffBump (0 : ℝ) := ⟨c / 2, c, by positivity, by linarith⟩
  let φ₀ : ℝ → ℂ := fun x ↦ (b x : ℂ)
  have hcomp : HasCompactSupport φ₀ := b.hasCompactSupport.comp_left Complex.ofReal_zero
  let φ : 𝓢(ℝ, ℂ) := hcomp.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  let η : 𝓢(ℝ, ℂ) := 𝓕⁻ φ
  have hFourier : 𝓕 (η : ℝ → ℂ) = (φ : ℝ → ℂ) := by
    rw [← SchwartzMap.fourier_coe, show 𝓕 η = φ from FourierTransform.fourier_fourierInv_eq φ]
  refine ⟨η, ?_, ?_, ?_, ?_⟩
  · have hneg : (φ : ℝ → ℂ) ∘ (fun x ↦ -x) = (φ : ℝ → ℂ) := by
      funext x
      change (b (-x) : ℂ) = (b x : ℂ)
      rw [b.neg]
    intro x
    change ((𝓕⁻ φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (-x) = ((𝓕⁻ φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x
    rw [SchwartzMap.fourierInv_coe]
    simpa [hneg] using
      (Real.fourierInv_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) (φ : ℝ → ℂ) x).symm
  · have hval : 𝓕 (η : ℝ → ℂ) (0 : ℝ) = ∫ x, η x := by
      rw [Real.fourier_real_eq]
      simp
    rw [← hval, hFourier]
    change (b 0 : ℂ) = 1
    rw [b.one_of_mem_closedBall, Complex.ofReal_one]
    exact Metric.mem_closedBall_self b.rIn_pos.le
  · rw [hFourier]
    intro x hx
    have h₀ : x ∈ Function.support (b : ℝ → ℝ) := by
      intro hzero
      exact hx (Complex.ofReal_eq_zero.mpr hzero)
    rw [b.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at h₀
    exact abs_le.mp h₀.le
  · simpa only [Real.norm_eq_abs, pow_one] using η.integrable_pow_mul volume 1

private theorem measurable_sharpIntervalMask (L : ℝ) : Measurable (sharpIntervalMask L) :=
  measurable_const.indicator measurableSet_Icc

private theorem norm_sharpIntervalMask_le (L x : ℝ) : ‖sharpIntervalMask L x‖ ≤ 1 := by
  by_cases h : x ∈ Icc (-L) L <;> simp [sharpIntervalMask, h]

private theorem norm_sharpIntervalMask_sub_le (L x y : ℝ) :
    ‖sharpIntervalMask L x - sharpIntervalMask L y‖ ≤ 1 := by
  by_cases hx : x ∈ Icc (-L) L <;> by_cases hy : y ∈ Icc (-L) L <;>
    simp [sharpIntervalMask, hx, hy]

private theorem norm_sharpIntervalMask_sub_translate_le (L x t : ℝ) :
    ‖sharpIntervalMask L x - sharpIntervalMask L (x - t)‖ ≤
      (uIcc (-L) (-L + t)).indicator (1 : ℝ → ℝ) x +
        (uIcc L (L + t)).indicator (1 : ℝ → ℝ) x := by
  classical
  have hn (s : Set ℝ) : 0 ≤ s.indicator (1 : ℝ → ℝ) x :=
    indicator_nonneg (fun _ _ ↦ zero_le_one) _
  by_cases hx : x ∈ Icc (-L) L <;> by_cases hy : x - t ∈ Icc (-L) L
  · simpa [sharpIntervalMask, hx, hy] using add_nonneg (hn (uIcc (-L) (-L + t)))
      (hn (uIcc L (L + t)))
  · have h : x ∈ uIcc (-L) (-L + t) ∨ x ∈ uIcc L (L + t) := by
      simp only [mem_Icc, not_and_or, not_le] at hx hy
      rcases hy with hy | hy
      · exact Or.inl ⟨(min_le_left _ _).trans hx.1,
          (by linarith : x ≤ -L + t).trans (le_max_right _ _)⟩
      · exact Or.inr ⟨(min_le_right _ _).trans (by linarith : L + t ≤ x),
          hx.2.trans (le_max_left _ _)⟩
    rcases h with h | h
    · simpa [sharpIntervalMask, hx, hy, h] using hn (uIcc L (L + t))
    · simpa [sharpIntervalMask, hx, hy, h] using hn (uIcc (-L) (-L + t))
  · have h : x ∈ uIcc (-L) (-L + t) ∨ x ∈ uIcc L (L + t) := by
      simp only [mem_Icc, not_and_or, not_le] at hx hy
      rcases hx with hx | hx
      · exact Or.inl ⟨(min_le_right _ _).trans (by linarith : -L + t ≤ x),
          hx.le.trans (le_max_left _ _)⟩
      · exact Or.inr ⟨(min_le_left _ _).trans hx.le,
          (by linarith : x ≤ L + t).trans (le_max_right _ _)⟩
    rcases h with h | h
    · simpa [sharpIntervalMask, hx, hy, h] using hn (uIcc L (L + t))
    · simpa [sharpIntervalMask, hx, hy, h] using hn (uIcc (-L) (-L + t))
  · simpa [sharpIntervalMask, hx, hy] using add_nonneg (hn (uIcc (-L) (-L + t)))
      (hn (uIcc L (L + t)))

private theorem integrable_uIcc_indicator_one (a b : ℝ) :
    Integrable ((uIcc a b).indicator (1 : ℝ → ℝ)) := by
  rw [integrable_indicator_iff measurableSet_uIcc]
  exact integrableOn_const (by simp [uIcc, Real.volume_Icc])

private theorem integrable_norm_sharpIntervalMask_sub_translate (L t : ℝ) :
    Integrable (fun x ↦ ‖sharpIntervalMask L x - sharpIntervalMask L (x - t)‖) := by
  refine ((integrable_uIcc_indicator_one (-L) (-L + t)).add
    (integrable_uIcc_indicator_one L (L + t))).mono' ?_ ?_
  · have hshift : Measurable (fun x ↦ sharpIntervalMask L (x - t)) :=
      (measurable_sharpIntervalMask L).comp (measurable_id.sub measurable_const)
    exact ((measurable_sharpIntervalMask L).sub hshift).norm.aestronglyMeasurable
  · exact ae_of_all _ fun x ↦ by
      simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
        norm_sharpIntervalMask_sub_translate_le L x t

/-- Translating a sharp interval cutoff by `t` changes it in `L¹` by at most `2 * |t|`. -/
theorem integral_norm_sharpIntervalMask_sub_translate_le (L t : ℝ) :
    (∫ x, ‖sharpIntervalMask L x - sharpIntervalMask L (x - t)‖) ≤ 2 * |t| := by
  have hleft := integrable_uIcc_indicator_one (-L) (-L + t)
  have hright := integrable_uIcc_indicator_one L (L + t)
  refine (integral_mono (integrable_norm_sharpIntervalMask_sub_translate L t)
    (hleft.add hright) (fun x ↦ by
      simpa only [Pi.add_apply] using norm_sharpIntervalMask_sub_translate_le L x t)).trans ?_
  simp only [Pi.add_apply, integral_add hleft hright]
  have h (a : ℝ) : (∫ x, (uIcc a (a + t)).indicator (1 : ℝ → ℝ) x) = |t| := by
    rw [integral_indicator_one measurableSet_uIcc, measureReal_def, uIcc, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr min_le_max), max_sub_min_eq_abs]
    congr 1
    ring
  rw [h (-L), h L, two_mul]

/-- At every fixed position the convolved cutoff tends to the integral of its kernel. -/
theorem tendsto_smoothIntervalMask (η : ℝ → ℂ) (hη : Integrable η) (x : ℝ) :
    Tendsto (fun L ↦ smoothIntervalMask η L x) atTop (𝓝 (∫ t, η t)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (F := fun L t ↦ η t * sharpIntervalMask L (x - t)) (fun t ↦ ‖η t‖)
    (.of_forall fun L ↦ ?_) (.of_forall fun L ↦ ae_of_all _ fun t ↦ ?_) hη.norm
    (ae_of_all _ fun t ↦ ?_)
  · have hshift : Measurable (fun t ↦ sharpIntervalMask L (x - t)) :=
      (measurable_sharpIntervalMask L).comp (measurable_const.sub measurable_id)
    exact hη.aestronglyMeasurable.mul hshift.aestronglyMeasurable
  · change ‖η t * sharpIntervalMask L (x - t)‖ ≤ ‖η t‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_sharpIntervalMask_le L (x - t))
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop |x - t|] with L hL
    simp [sharpIntervalMask, abs_le.mp hL]

private theorem sharpIntervalMask_sub_smoothIntervalMask_eq_integral
    (η : ℝ → ℂ) (hη : Integrable η) (hmass : (∫ t, η t) = 1) (L x : ℝ) :
    sharpIntervalMask L x - smoothIntervalMask η L x =
      ∫ t, η t * (sharpIntervalMask L x - sharpIntervalMask L (x - t)) := by
  have hs : Integrable (fun t ↦ η t * sharpIntervalMask L (x - t)) := by
    have hshift : Measurable (fun t ↦ sharpIntervalMask L (x - t)) :=
      (measurable_sharpIntervalMask L).comp (measurable_const.sub measurable_id)
    refine hη.mono (hη.aestronglyMeasurable.mul hshift.aestronglyMeasurable)
      (ae_of_all _ fun t ↦ ?_)
    change ‖η t * sharpIntervalMask L (x - t)‖ ≤ ‖η t‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_sharpIntervalMask_le L (x - t))
  simp only [mul_sub, integral_sub (hη.mul_const _) hs, integral_mul_const, hmass, one_mul,
    smoothIntervalMask, convolution_mul]

/-- For a mass-one kernel the sharp-minus-smoothed error is uniformly bounded
by the integral of the absolute value of the kernel. -/
theorem norm_sharpIntervalMask_sub_smoothIntervalMask_le
    (η : ℝ → ℂ) (hη : Integrable η) (hmass : (∫ t, η t) = 1) (L x : ℝ) :
    ‖sharpIntervalMask L x - smoothIntervalMask η L x‖ ≤ ∫ t, ‖η t‖ := by
  rw [sharpIntervalMask_sub_smoothIntervalMask_eq_integral η hη hmass]
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) hη.norm
      (ae_of_all _ fun t ↦ ?_))
  change ‖η t * (sharpIntervalMask L x - sharpIntervalMask L (x - t))‖ ≤ ‖η t‖
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_sharpIntervalMask_sub_le L _ _)

/-- For a mass-one kernel the sharp-minus-smoothed error tends pointwise to zero. -/
theorem tendsto_sharpIntervalMask_sub_smoothIntervalMask
    (η : ℝ → ℂ) (hη : Integrable η) (hmass : (∫ t, η t) = 1) (x : ℝ) :
    Tendsto (fun L ↦ sharpIntervalMask L x - smoothIntervalMask η L x) atTop (𝓝 0) := by
  have hsharp : Tendsto (fun L ↦ sharpIntervalMask L x) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop |x|] with L hL
    simp [sharpIntervalMask, abs_le.mp hL]
  simpa [hmass] using hsharp.sub (tendsto_smoothIntervalMask η hη x)

/-- For a mass-one kernel of finite absolute first moment the sharp-minus-smoothed
error is integrable. Its `L¹` norm is at most twice that moment, uniformly in the
cutoff radius. -/
theorem integrable_and_integral_norm_sharpIntervalMask_sub_smoothIntervalMask
    (η : ℝ → ℂ) (hη : Integrable η) (hmass : (∫ t, η t) = 1)
    (hmoment : Integrable (fun t ↦ |t| * ‖η t‖)) (L : ℝ) :
    Integrable (fun x ↦ sharpIntervalMask L x - smoothIntervalMask η L x) ∧
      (∫ x, ‖sharpIntervalMask L x - smoothIntervalMask η L x‖) ≤
        2 * ∫ t, |t| * ‖η t‖ := by
  let errorAt : ℝ × ℝ → ℂ := fun p ↦
    η p.2 * (sharpIntervalMask L p.1 - sharpIntervalMask L (p.1 - p.2))
  have hmeas : AEStronglyMeasurable errorAt (volume.prod volume) := by
    have hmask₁ : Measurable (fun p : ℝ × ℝ ↦ sharpIntervalMask L p.1) :=
      (measurable_sharpIntervalMask L).comp measurable_fst
    have hmask₂ : Measurable (fun p : ℝ × ℝ ↦ sharpIntervalMask L (p.1 - p.2)) :=
      (measurable_sharpIntervalMask L).comp (measurable_fst.sub measurable_snd)
    exact hη.aestronglyMeasurable.comp_snd.mul (hmask₁.sub hmask₂).aestronglyMeasurable
  have hinner (t : ℝ) : Integrable (fun x ↦ ‖errorAt (x, t)‖) := by
    simpa only [errorAt, norm_mul] using
      (integrable_norm_sharpIntervalMask_sub_translate L t).const_mul ‖η t‖
  have hinner_le (t : ℝ) : (∫ x, ‖errorAt (x, t)‖) ≤ 2 * (|t| * ‖η t‖) := by
    simp only [errorAt, norm_mul, integral_const_mul]
    calc
      ‖η t‖ * (∫ x, ‖sharpIntervalMask L x - sharpIntervalMask L (x - t)‖)
          ≤ ‖η t‖ * (2 * |t|) := mul_le_mul_of_nonneg_left
            (integral_norm_sharpIntervalMask_sub_translate_le L t) (norm_nonneg _)
      _ = 2 * (|t| * ‖η t‖) := by ring
  have hbound : Integrable (fun t ↦ 2 * (|t| * ‖η t‖)) := hmoment.const_mul _
  have hnonneg (t : ℝ) : 0 ≤ ∫ x, ‖errorAt (x, t)‖ :=
    integral_nonneg fun _ ↦ norm_nonneg _
  have hint : Integrable (fun p ↦ ‖errorAt p‖) (volume.prod volume) := by
    refine (integrable_prod_iff' hmeas.norm).2 ⟨ae_of_all _ hinner, ?_⟩
    simp only [norm_norm]
    exact hbound.mono_nonneg hmeas.norm.prod_swap.integral_prod_right'
      (ae_of_all _ hnonneg) (ae_of_all _ hinner_le)
  have herror_le (x : ℝ) :
      ‖sharpIntervalMask L x - smoothIntervalMask η L x‖ ≤ ∫ t, ‖errorAt (x, t)‖ := by
    rw [sharpIntervalMask_sub_smoothIntervalMask_eq_integral η hη hmass]
    exact norm_integral_le_integral_norm _
  refine ⟨hint.integral_prod_left.mono' ?_ (ae_of_all _ herror_le), ?_⟩
  · simp_rw [sharpIntervalMask_sub_smoothIntervalMask_eq_integral η hη hmass]
    exact hmeas.integral_prod_right'
  · calc
      (∫ x, ‖sharpIntervalMask L x - smoothIntervalMask η L x‖)
          ≤ ∫ x, ∫ t, ‖errorAt (x, t)‖ := integral_mono_of_nonneg
            (ae_of_all _ fun _ ↦ norm_nonneg _) hint.integral_prod_left (ae_of_all _ herror_le)
      _ = ∫ t, ∫ x, ‖errorAt (x, t)‖ := integral_integral_swap hint
      _ ≤ ∫ t, 2 * (|t| * ‖η t‖) :=
        integral_mono_of_nonneg (ae_of_all _ hnonneg) hbound (ae_of_all _ hinner_le)
      _ = 2 * ∫ t, |t| * ‖η t‖ := integral_const_mul _ _

end RiemannMasullo
