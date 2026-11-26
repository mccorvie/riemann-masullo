module

public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
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

private theorem plateau_indicator_mass {R : ℝ} (h : 0 ≤ R) :
    (∫ x, (Icc (-R) R).indicator (fun _ : ℝ ↦ (1 : ℝ)) x) = 2 * R := by
  rw [integral_indicator measurableSet_Icc, setIntegral_const, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R), smul_eq_mul, mul_one]
  ring

private theorem plateau_indicator_integrable (R : ℝ) :
    Integrable ((Icc (-R) R).indicator (fun _ : ℝ ↦ (1 : ℝ))) := by
  rw [integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (by simp [Real.volume_Icc])

private theorem spectral_bump_energy {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ φ : 𝓢(ℝ, ℂ), Function.Even (φ : ℝ → ℂ) ∧
      EqOn (𝓕⁻ (φ : ℝ → ℂ)) 1 (Icc (-r) r) ∧
      Function.support (𝓕⁻ (φ : ℝ → ℂ)) ⊆ Ioo (-R) R ∧
      2*r ≤ (∫ x, ‖φ x‖^2) ∧ (∫ x, ‖φ x‖^2) ≤ ‖φ 0‖ ∧ ‖φ 0‖ ≤ 2*R := by
  let b : ContDiffBump (0 : ℝ) := ⟨r, R, hr, hrR⟩
  let g : ℝ → ℂ := fun x ↦ (b x : ℂ)
  have hg : HasCompactSupport g := b.hasCompactSupport.comp_left Complex.ofReal_zero
  let ψ : 𝓢(ℝ, ℂ) := hg.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  let φ : 𝓢(ℝ, ℂ) := 𝓕 ψ
  have hi : 𝓕⁻ (φ : ℝ → ℂ) = (ψ : ℝ → ℂ) := by
    rw [← SchwartzMap.fourierInv_coe, show 𝓕⁻ φ = ψ from FourierTransform.fourierInv_fourier_eq ψ]
  have hone {x : ℝ} (hx : x ∈ Icc (-r) r) : b x = 1 := by
    apply b.one_of_mem_closedBall
    simpa [Metric.mem_closedBall, Real.dist_eq] using abs_le.mpr hx
  have hs {x : ℝ} (hx : b x ≠ 0) : x ∈ Ioo (-R) R := by
    change x ∈ Function.support (b : ℝ → ℝ) at hx
    rw [b.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hx
    exact abs_lt.mp hx
  have hnorm (x : ℝ) : ‖ψ x‖ = b x := Complex.norm_of_nonneg b.nonneg
  have he : (∫ x, ‖φ x‖^2) = ∫ x, (b x)^2 := by
    change (∫ x, ‖𝓕 ψ x‖^2) = _
    rw [SchwartzMap.integral_norm_sq_fourier]; simp only [hnorm]
  have hv : ‖φ 0‖ = ∫ x, b x := by
    have hv' : φ 0 = ∫ x, ψ x := by
      change 𝓕 (ψ : ℝ → ℂ) 0 = _
      rw [Real.fourier_real_eq]; simp
    rw [hv', show (∫ x, ψ x) = ((∫ x, b x : ℝ) : ℂ) from integral_ofReal]
    exact Complex.norm_of_nonneg (integral_nonneg fun _ ↦ b.nonneg)
  have hb : Integrable (b : ℝ → ℝ) := b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
  have hb2 : Integrable (fun x ↦ (b x)^2) := by
    simpa only [hnorm] using
      (memLp_two_iff_integrable_sq_norm ψ.continuous.aestronglyMeasurable).mp (ψ.memLp 2)
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hneg : (ψ : ℝ → ℂ) ∘ (LinearIsometryEquiv.neg ℝ (E := ℝ)) = (ψ : ℝ → ℂ) := by
      funext x; change (b (-x) : ℂ) = (b x : ℂ); rw [b.neg]
    intro x
    have h := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ)) (⇑ψ) x
    rw [hneg] at h
    exact h.symm
  · rw [hi]; intro x hx; change (b x : ℂ) = 1; simp [hone hx]
  · rw [hi]; intro x hx; exact hs fun hz ↦ hx (Complex.ofReal_eq_zero.mpr hz)
  · rw [he, ← plateau_indicator_mass hr.le]
    apply integral_mono (plateau_indicator_integrable r) hb2
    intro x; by_cases hx : x ∈ Icc (-r) r <;> simp [hx, sq_nonneg, hone]
  · rw [he, hv]; apply integral_mono hb2 hb; intro x
    change (b x) ^ 2 ≤ b x
    rw [pow_two]
    exact mul_le_of_le_one_right b.nonneg b.le_one
  · rw [hv, ← plateau_indicator_mass (hr.trans hrR).le]
    apply integral_mono hb (plateau_indicator_integrable R)
    intro x; by_cases hx : x ∈ Icc (-R) R
    · simpa [hx] using (b.le_one : b x ≤ 1)
    · have hz : b x = 0 := by_contra fun hn ↦ hx (Ioo_subset_Icc_self (hs hn))
      simp [hx, hz]

/-- The inverse-transform plateau can have squared norm as close as desired
to the length of the band. -/
theorem exists_evenSchwartz_fourierInv_plateau_energy {Y δ : ℝ} (hY : 0 < Y) (hδ : 0 < δ) :
    ∃ φ : 𝓢(ℝ, ℂ), Function.Even (φ : ℝ → ℂ) ∧
      EqOn (𝓕⁻ (φ : ℝ → ℂ)) 1 (Icc (-Y) Y) ∧
      Function.support (𝓕⁻ (φ : ℝ → ℂ)) ⊆ Ioo (-(Y+δ)) (Y+δ) ∧
      (∫ x, ‖φ x‖^2) ≤ 2*(Y+δ) := by
  obtain ⟨φ, hφ, hi, hs, _, he, hv⟩ := spectral_bump_energy hY (R := Y+δ) (by linarith)
  exact ⟨φ, hφ, hi, hs, he.trans hv⟩

/-- An even, strictly band-limited Schwartz trial approaches the flat evaluation bound. -/
theorem exists_evenSchwartz_band_trial {Y ε : ℝ} (hY : 0 < Y) (hε : 0 < ε) :
    ∃ b : 𝓢(ℝ, ℂ), Function.Even (b : ℝ → ℂ) ∧
      Function.support (𝓕 (b : ℝ → ℂ)) ⊆ Ioo (-Y) Y ∧
      Y-ε < ‖b 0‖^2 / (2 * ∫ x, ‖b x‖^2) := by
  obtain ⟨r, hr, hrY⟩ := exists_between (show max 0 (Y-ε) < Y from max_lt hY (by linarith))
  obtain ⟨b, hb, _, hs, hl, he, _⟩ := spectral_bump_energy ((le_max_left _ _).trans_lt hr) hrY
  refine ⟨b, hb, ?_, ?_⟩
  · intro x hx
    have hx' : -x ∈ Function.support (𝓕⁻ (b : ℝ → ℂ)) := by
      simpa [Function.mem_support, Real.fourierInv_eq_fourier_neg] using hx
    obtain ⟨h₁,h₂⟩ := hs hx'; exact ⟨by linarith, by linarith⟩
  · have hr0 := (le_max_left _ _).trans_lt hr
    have hrε := (le_max_right _ _).trans_lt hr
    have hp : 0 < ∫ x, ‖b x‖^2 := by linarith
    apply lt_of_lt_of_le hrε
    apply (le_div_iff₀ (by positivity)).2
    calc r * (2 * ∫ x, ‖b x‖^2) = (2*r) * (∫ x, ‖b x‖^2) := by ring
         _ ≤ ‖b 0‖ * ‖b 0‖ := mul_le_mul (hl.trans he) he hp.le (norm_nonneg _)
         _ = _ := (sq _).symm

/-- An even Schwartz function whose inverse transform equals one on the closed
band and vanishes off a prescribed positive enlargement. -/
theorem exists_evenSchwartz_fourierInv_plateau (Y δ : ℝ) (hY : 0 ≤ Y) (hδ : 0 < δ) :
    ∃ φ : 𝓢(ℝ, ℂ), Function.Even (φ : ℝ → ℂ) ∧
      EqOn (𝓕⁻ (φ : ℝ → ℂ)) 1 (Icc (-Y) Y) ∧
      Function.support (𝓕⁻ (φ : ℝ → ℂ)) ⊆ Icc (-(Y + δ)) (Y + δ) := by
  obtain ⟨φ, hφ, hone, hs, _, _, _⟩ :=
    spectral_bump_energy (r := Y + δ / 2) (R := Y + δ) (by linarith) (by linarith)
  have hbands : Icc (-Y) Y ⊆ Icc (-(Y + δ / 2)) (Y + δ / 2) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact ⟨φ, hφ, hone.mono hbands, hs.trans Ioo_subset_Icc_self⟩

private theorem measurable_sharpIntervalMask (L : ℝ) : Measurable (sharpIntervalMask L) :=
  measurable_const.indicator measurableSet_Icc

private theorem norm_sharpIntervalMask_le (L x : ℝ) : ‖sharpIntervalMask L x‖ ≤ 1 := by
  by_cases h : x ∈ Icc (-L) L <;> simp [sharpIntervalMask, h]

/-- The smoothed mask is bounded by the L¹ norm of its smoothing kernel. -/
theorem norm_smoothIntervalMask_le {η : ℝ → ℂ} (hη : Integrable η) (L x : ℝ) :
    ‖smoothIntervalMask η L x‖ ≤ ∫ t, ‖η t‖ := by
  let k (t : ℝ) := η t * sharpIntervalMask L (x - t)
  have hm : AEStronglyMeasurable k volume := hη.aestronglyMeasurable.mul
    ((measurable_sharpIntervalMask L).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hb : ∀ᵐ t ∂volume, ‖k t‖ ≤ ‖η t‖ := ae_of_all _ fun t ↦ by
    change ‖η t * sharpIntervalMask L (x - t)‖ ≤ ‖η t‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_sharpIntervalMask_le L (x - t))
  change ‖∫ t, k t‖ ≤ _
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono_ae (hη.norm.mono' hm hb).norm hη.norm hb)

/-- Convolution with a Schwartz kernel gives a continuous interval mask. -/
theorem continuous_smoothIntervalMask (η : 𝓢(ℝ, ℂ)) (L : ℝ) :
    Continuous (smoothIntervalMask η L) := by
  have hb : BddAbove (Set.range fun x ↦ ‖η x‖) :=
    ⟨SchwartzMap.seminorm ℝ 0 0 η, by rintro _ ⟨x, rfl⟩; exact η.norm_le_seminorm ℝ x⟩
  exact hb.continuous_convolution_left_of_integrable
    (ContinuousLinearMap.mul ℂ ℂ) η.continuous (integrable_sharpIntervalMask L)

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
