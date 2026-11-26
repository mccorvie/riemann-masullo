module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.PaleyWiener
public import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space

/-! # Evaluation on a weighted real Paley–Wiener band -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform InnerProductSpace Topology

namespace RiemannMasullo

namespace RealPWBand

local notation "L2R" => Lp ℂ 2 (volume : Measure ℝ)

private theorem measure_le_one_smul {μ ν : Measure ℝ} (h : μ ≤ ν) :
    μ ≤ (1 : ℝ≥0∞) • ν := by simpa using h

/-- Restriction of a square-integrable function from a dominating measure to a smaller one. -/
private def restrictL2 {μ ν : Measure ℝ} (h : μ ≤ ν) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ where
  toFun := Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top (measure_le_one_smul h)
  map_add' := (Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top (measure_le_one_smul h)).map_add
  map_smul' c f := by
    apply Lp.ext
    have hμν := Measure.absolutelyContinuous_of_le h
    filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top (measure_le_one_smul h) (c • f),
      Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top (measure_le_one_smul h) f,
      hμν.ae_eq (Lp.coeFn_smul c f),
      Lp.coeFn_smul c (Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top (measure_le_one_smul h) f)]
      with x hcf hf hc hh
    rw [hcf, RingHom.id_apply, hh, hc]
    change c * f x = c * _
    rw [hf]
  cont := (Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top (measure_le_one_smul h)).continuous

private theorem restrictL2_ae {μ ν : Measure ℝ} (h : μ ≤ ν) (f : Lp ℂ 2 ν) :
    restrictL2 h f =ᵐ[μ] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top (measure_le_one_smul h) f

private theorem norm_restrictL2_le {μ ν : Measure ℝ} (h : μ ≤ ν) (f : Lp ℂ 2 ν) :
    ‖restrictL2 h f‖ ≤ ‖f‖ := by
  change ‖Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top (measure_le_one_smul h) f‖ ≤ ‖f‖
  have hn := Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2)
    ENNReal.one_ne_top (measure_le_one_smul h)
  simpa using
    ((Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top (measure_le_one_smul h)).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg f))

private def frequency (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume.restrict (Icc (-Y) Y)) :=
  (restrictL2 Measure.restrict_le_self).comp
    ((Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (restrictL2 hμ))

private def reflected : L2R →L[ℂ] L2R :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ ↦ -x)
    (Measure.measurePreserving_neg volume)).toContinuousLinearMap

private def outsideBand (Y : ℝ) : L2R →L[ℂ] Lp ℂ 2 (volume.restrict (Icc (-Y) Y)ᶜ) :=
  (restrictL2 Measure.restrict_le_self).comp
    (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap

/-- The even real Paley–Wiener band in \(L^2(\mu)\), for a measure dominating Lebesgue
measure. The Fourier support is imposed after passing to ordinary \(L^2\). -/
@[no_expose] def space (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ) : Submodule ℂ (Lp ℂ 2 μ) :=
  ((outsideBand Y).comp (restrictL2 hμ)).ker ⊓
    ((reflected - ContinuousLinearMap.id ℂ L2R).comp (restrictL2 hμ)).ker

/-- The even weighted band is closed in the ambient weighted Hilbert space. -/
theorem isClosed_space (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ) :
    IsClosed (space Y hμ : Set (Lp ℂ 2 μ)) :=
  (((outsideBand Y).comp (restrictL2 hμ)).isClosed_ker).inter
    (((reflected - ContinuousLinearMap.id ℂ L2R).comp (restrictL2 hμ)).isClosed_ker)

/-- The weighted band is a Hilbert space in the ambient weighted norm. -/
instance (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ) : CompleteSpace (space Y hμ) :=
  (isClosed_space Y hμ).completeSpace_coe

private theorem frequency_ae (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ) (f : Lp ℂ 2 μ) :
    frequency Y hμ f =ᵐ[volume.restrict (Icc (-Y) Y)] (𝓕 (restrictL2 hμ f) : L2R) :=
  restrictL2_ae Measure.restrict_le_self _

private theorem spectrum_zero_off (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ)
    (f : space Y hμ) :
    ∀ᵐ t ∂volume.restrict (Icc (-Y) Y)ᶜ, (𝓕 (restrictL2 hμ f.val) : L2R) t = 0 := by
  have h : outsideBand Y (restrictL2 hμ f.val) = 0 := f.property.1
  filter_upwards [restrictL2_ae (μ := volume.restrict (Icc (-Y) Y)ᶜ)
    Measure.restrict_le_self (𝓕 (restrictL2 hμ f.val) : L2R),
    Lp.coeFn_zero ℂ 2 (volume.restrict (Icc (-Y) Y)ᶜ)] with t ht hz
  rw [← ht]
  change outsideBand Y (restrictL2 hμ f.val) t = 0
  rw [h]
  exact hz

private instance (Y : ℝ) : IsFiniteMeasure (volume.restrict (Icc (-Y) Y)) :=
  isFiniteMeasure_restrict.mpr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

private def phase (x t : ℝ) : ℂ := Complex.exp (Complex.I * ((-(2 * Real.pi * (t * x)) : ℝ) : ℂ))

private theorem continuous_phase_left (t : ℝ) : Continuous (fun x ↦ phase x t) := by
  unfold phase
  fun_prop

private theorem continuous_phase_right (x : ℝ) : Continuous (phase x) := by
  unfold phase
  fun_prop

private theorem norm_phase (x t : ℝ) : ‖phase x t‖ = 1 := by
  rw [phase, mul_comm, Complex.norm_exp_ofReal_mul_I]

private def wave (Y x : ℝ) : Lp ℂ 2 (volume.restrict (Icc (-Y) Y)) :=
  ((memLp_const (1 : ℝ)).mono' (continuous_phase_right x).aestronglyMeasurable
    (Eventually.of_forall fun t ↦ by simp only [norm_phase, le_refl])).toLp (phase x)

private theorem wave_ae (Y x : ℝ) :
    wave Y x =ᵐ[volume.restrict (Icc (-Y) Y)] phase x :=
  MemLp.coeFn_toLp _

private theorem norm_wave (Y x : ℝ) (hY : 0 ≤ Y) : ‖wave Y x‖ = Real.sqrt (2 * Y) := by
  have hs : ‖wave Y x‖ ^ 2 = 2 * Y := by
    rw [← L2.integral_sq_norm (𝕜 := ℂ)]
    calc
      _ = ∫ _ : ℝ, (1 : ℝ) ∂volume.restrict (Icc (-Y) Y) := by
        apply integral_congr_ae
        filter_upwards [wave_ae Y x] with t ht
        rw [ht, norm_phase, one_pow]
      _ = 2 * Y := by
        simp only [integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ,
          Real.volume_Icc]
        rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ Y - -Y)]
        ring
  nlinarith [Real.sq_sqrt (show 0 ≤ 2 * Y by positivity), norm_nonneg (wave Y x),
    Real.sqrt_nonneg (2 * Y)]

private theorem continuous_wave (Y : ℝ) : Continuous (wave Y) := by
  let ν := volume.restrict (Icc (-Y) Y)
  rw [continuous_iff_continuousAt]
  intro x
  apply tendsto_iff_dist_tendsto_zero.mpr
  rw [show (fun y ↦ dist (wave Y y) (wave Y x)) =
      fun y ↦ Real.sqrt (∫ t, ‖phase y t - phase x t‖ ^ 2 ∂ν) from ?_]
  · have h := tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := 𝓝 x)
      (F := fun y t ↦ ‖phase y t - phase x t‖ ^ 2) (f := fun _ ↦ (0 : ℝ))
      (bound := fun _ ↦ (4 : ℝ))
      (Eventually.of_forall fun y ↦ (((continuous_phase_right y).sub
        (continuous_phase_right x)).norm.pow 2).aestronglyMeasurable)
      (Eventually.of_forall fun y ↦ Eventually.of_forall fun t ↦ by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have ht := norm_sub_le (phase y t) (phase x t)
        rw [norm_phase, norm_phase] at ht
        nlinarith [norm_nonneg (phase y t - phase x t)])
      (integrable_const _) (Eventually.of_forall fun t ↦ by
        have hc : Continuous (fun y ↦ ‖phase y t - phase x t‖ ^ 2) :=
          (((continuous_phase_left t).sub continuous_const).norm.pow 2)
        simpa only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
          (hc.continuousAt (x := x)).tendsto)
    have h' : Tendsto (fun y ↦ ∫ t, ‖phase y t - phase x t‖ ^ 2 ∂ν) (𝓝 x) (𝓝 0) := by
      simpa only [integral_zero] using h
    have hcomp := (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.comp h'
    rw [Real.sqrt_zero] at hcomp
    exact hcomp
  · funext y
    rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _), ← L2.integral_sq_norm (𝕜 := ℂ)]
    congr 1
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (wave Y y) (wave Y x), wave_ae Y y, wave_ae Y x]
      with t ht hy hx
    rw [ht]
    change ‖wave Y y t - wave Y x t‖ ^ 2 = _
    rw [hy, hx]

/-- The inverse Fourier evaluation functional on the even weighted band. -/
@[no_expose] def evaluation (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ) (x : ℝ) :
    space Y hμ →L[ℂ] ℂ :=
  (innerSL ℂ (wave Y x)).comp ((frequency Y hμ).comp (space Y hμ).subtypeL)

/-- The inverse Fourier evaluation functionals vary continuously in operator norm. -/
theorem continuous_evaluation (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ) :
    Continuous (evaluation Y hμ) := by
  unfold evaluation
  exact isBoundedBilinearMap_comp.continuous.comp
    (((innerSL ℂ).continuous.comp (continuous_wave Y)).prodMk continuous_const)

/-- The evaluation functional has the usual Paley–Wiener bound in the weighted norm. -/
theorem norm_evaluation_le (Y : ℝ) (hY : 0 ≤ Y) {μ : Measure ℝ} (hμ : volume ≤ μ)
    (x : ℝ) : ‖evaluation Y hμ x‖ ≤ Real.sqrt (2 * Y) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  change ‖⟪wave Y x, frequency Y hμ f.val⟫_ℂ‖ ≤ Real.sqrt (2 * Y) * ‖f‖
  refine (norm_inner_le_norm _ _).trans ?_
  rw [norm_wave Y x hY]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  calc
    ‖frequency Y hμ f.val‖ ≤ ‖(𝓕 (restrictL2 hμ f.val) : L2R)‖ :=
      norm_restrictL2_le Measure.restrict_le_self _
    _ = ‖restrictL2 hμ f.val‖ := Lp.norm_fourier_eq _
    _ ≤ ‖f‖ := norm_restrictL2_le hμ f.val

private theorem conj_phase (x t : ℝ) :
    star (phase x t) = Complex.exp ((↑(2 * Real.pi * (t * x) : ℝ)) * Complex.I) := by
  rw [phase, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal,
    Complex.ofReal_neg]
  congr 1
  ring

private theorem spectrum_integrable (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ)
    (f : space Y hμ) : Integrable ((𝓕 (restrictL2 hμ f.val) : L2R) : ℝ → ℂ) := by
  let F := (𝓕 (restrictL2 hμ f.val) : L2R)
  have hzero := spectrum_zero_off Y hμ f
  have hon : IntegrableOn (F : ℝ → ℂ) (Icc (-Y) Y) :=
    ((Lp.memLp F).mono_measure Measure.restrict_le_self).integrable one_le_two
  have hoff : IntegrableOn (F : ℝ → ℂ) (Icc (-Y) Y)ᶜ :=
    (integrable_zero ℝ ℂ _).congr (hzero.mono fun _ hx ↦ hx.symm)
  simpa only [union_compl_self, integrableOn_univ] using hon.union hoff

private theorem evaluation_eq_fourierInv (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ)
    (f : space Y hμ) (x : ℝ) :
    evaluation Y hμ x f = 𝓕⁻ ((𝓕 (restrictL2 hμ f.val) : L2R) : ℝ → ℂ) x := by
    let F := (𝓕 (restrictL2 hμ f.val) : L2R)
    have hzero := spectrum_zero_off Y hμ f
    have hF := spectrum_integrable Y hμ f
    change ⟪wave Y x, frequency Y hμ f.val⟫_ℂ = _
    rw [L2.inner_def]
    let k (t : ℝ) := Complex.exp ((↑(2 * Real.pi * (t * x) : ℝ)) * Complex.I) * F t
    have hk : Integrable k := by
      refine hF.norm.mono' ?_ ?_
      · exact (Continuous.aestronglyMeasurable (by fun_prop :
        Continuous fun t : ℝ ↦ Complex.exp ((↑(2 * Real.pi * (t * x) : ℝ)) * Complex.I))).mul
          (Lp.aestronglyMeasurable F)
      · filter_upwards with t
        change ‖Complex.exp ((↑(2 * Real.pi * (t * x) : ℝ)) * Complex.I) * F t‖ ≤ ‖F t‖
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have hoff : ∫ t in (Icc (-Y) Y)ᶜ, k t = 0 := by
      have hke : k =ᵐ[volume.restrict (Icc (-Y) Y)ᶜ] 0 := hzero.mono fun t ht ↦ by
        change k t = 0
        unfold k
        rw [show F t = 0 from ht, mul_zero]
      rw [integral_congr_ae hke]
      simp
    calc
      _ = ∫ t in Icc (-Y) Y, k t := by
        apply integral_congr_ae
        filter_upwards [wave_ae Y x, frequency_ae Y hμ f.val] with t ht hf
        rw [RCLike.inner_apply, ht, hf]
        change F t * star (phase x t) = k t
        rw [conj_phase, mul_comm]
      _ = ∫ t, k t := by rw [← integral_add_compl measurableSet_Icc hk, hoff, add_zero]
      _ = _ := by rw [Real.fourierInv_eq']; simp only [k, F, Real.inner_apply, smul_eq_mul]

/-- Evaluation on the real axis extends to an entire function for each band element. -/
theorem exists_entire_evaluation (Y : ℝ) (hY : 0 ≤ Y) {μ : Measure ℝ}
    (hμ : volume ≤ μ) (f : space Y hμ) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ x : ℝ, g x = evaluation Y hμ x f := by
  obtain ⟨g, hg, htrace⟩ := exists_entire_fourierInv_of_band hY
    (𝓕 (restrictL2 hμ f.val) : L2R) (spectrum_zero_off Y hμ f)
  exact ⟨g, hg, fun x ↦ (htrace x).trans (evaluation_eq_fourierInv Y hμ f x).symm⟩

/-- The canonical evaluation representative is real analytic at every point. -/
theorem analyticOnNhd_evaluation (Y : ℝ) (hY : 0 ≤ Y) {μ : Measure ℝ}
    (hμ : volume ≤ μ) (f : space Y hμ) :
    AnalyticOnNhd ℝ (fun x ↦ evaluation Y hμ x f) univ := by
  obtain ⟨g, hg, he⟩ := exists_entire_evaluation Y hY hμ f
  rw [← funext he]
  intro x _
  exact ((hg.analyticAt (x : ℂ)).restrictScalars (𝕜 := ℝ)).comp_of_eq
    (Complex.ofRealCLM.analyticAt x) rfl

/-- An integrable reproducing kernel works pointwise without assuming the band
vector is integrable in physical space. -/
theorem evaluation_reproduces (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ)
    (f : space Y hμ) {φ : ℝ → ℂ} (hφ : Integrable φ)
    (hone : EqOn (𝓕⁻ φ) 1 (Icc (-Y) Y)) (x : ℝ) :
    evaluation Y hμ x f = ∫ t, evaluation Y hμ (x + t) f * φ t := by
  simp_rw [evaluation_eq_fourierInv]
  apply fourierInv_reproduces (spectrum_integrable Y hμ f) hφ
  have hoff := (ae_restrict_iff' measurableSet_Icc.compl).mp (spectrum_zero_off Y hμ f)
  filter_upwards [hoff] with ξ hξ
  intro hn
  by_cases hmem : ξ ∈ Icc (-Y) Y
  · exact hone hmem
  · exact (hn (hξ hmem)).elim

private theorem evaluation_ordinary_ae (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ)
    (f : space Y hμ) :
    (fun x ↦ evaluation Y hμ x f) =ᵐ[volume] (restrictL2 hμ f.val : ℝ → ℂ) := by
  simp_rw [evaluation_eq_fourierInv]
  have hInv := fourierInv_ae_L2 _ (spectrum_integrable Y hμ f)
  simpa only [FourierTransform.fourierInv_fourier_eq] using hInv

/-- The evaluation functional gives a pointwise representative in the weighted space
when the weight measure is absolutely continuous with respect to Lebesgue measure. -/
theorem evaluation_ae (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ)
    (hμac : μ ≪ volume) (f : space Y hμ) :
    (fun x ↦ evaluation Y hμ x f) =ᵐ[μ] (f.val : ℝ → ℂ) :=
  hμac.ae_eq ((evaluation_ordinary_ae Y hμ f).trans (restrictL2_ae hμ f.val))

/-- Compact Fourier support gives a smooth pointwise representative on the weighted band. -/
theorem contDiff_evaluation (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ)
    (f : space Y hμ) (k : ℕ) : ContDiff ℝ k (fun x ↦ evaluation Y hμ x f) := by
  let F := (𝓕 (restrictL2 hμ f.val) : L2R)
  have hF := spectrum_integrable Y hμ f
  have hzero := spectrum_zero_off Y hμ f
  simp_rw [evaluation_eq_fourierInv, Real.fourierInv_eq_fourier_neg]
  have hsmooth : ContDiff ℝ k (𝓕 (F : ℝ → ℂ)) := by
    apply Real.contDiff_fourier
    intro n _
    have hmain : IntegrableOn (fun t ↦ ‖t‖ ^ n * ‖F t‖) (Icc (-Y) Y) := by
      refine ((hF.norm.const_mul (|Y| ^ n)).integrableOn).mono'
        ((continuous_norm.pow n).aestronglyMeasurable.mul hF.norm.integrableOn.aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with t ht
      rw [Real.norm_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_le.mpr ht).trans (le_abs_self Y)) _
    have htail : IntegrableOn (fun t ↦ ‖t‖ ^ n * ‖F t‖) (Icc (-Y) Y)ᶜ := by
      refine (integrable_zero ℝ ℝ _).congr (hzero.mono fun t ht ↦ ?_)
      change 0 = ‖t‖ ^ n * ‖F t‖
      rw [show F t = 0 from ht, norm_zero, mul_zero]
    simpa only [union_compl_self, integrableOn_univ] using hmain.union htail
  exact hsmooth.comp contDiff_neg

/-- The smooth representative of a vector in the even band is even pointwise. -/
theorem evaluation_even (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ)
    (f : space Y hμ) (x : ℝ) : evaluation Y hμ (-x) f = evaluation Y hμ x f := by
  let u := restrictL2 hμ f.val
  let e (t : ℝ) := evaluation Y hμ t f
  have hu : reflected u = u := by
    apply sub_eq_zero.mp
    exact f.property.2
  have hrep := evaluation_ordinary_ae Y hμ f
  have href : (fun t : ℝ ↦ u (-t)) =ᵐ[volume] (u : ℝ → ℂ) := by
    have h := Lp.coeFn_compMeasurePreserving u (Measure.measurePreserving_neg (volume : Measure ℝ))
    change (reflected u : ℝ → ℂ) =ᵐ[volume] (fun t : ℝ ↦ u (-t)) at h
    rw [hu] at h
    exact h.symm
  have hneg : (fun t : ℝ ↦ e (-t)) =ᵐ[volume] (fun t : ℝ ↦ u (-t)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp hrep
  have he : Continuous e := (contDiff_evaluation Y hμ f 0).continuous
  exact congrFun (((he.comp continuous_neg).ae_eq_iff_eq volume he).mp
    (hneg.trans (href.trans hrep.symm))) x

/-- The Riesz vector representing point evaluation on the weighted band. -/
@[no_expose] def evaluationVector (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ) (x : ℝ) :
    space Y hμ :=
  (InnerProductSpace.toDual ℂ (space Y hμ)).symm (evaluation Y hμ x)

/-- The evaluation vectors on the weighted band depend continuously on the point. -/
theorem continuous_evaluationVector (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ) :
    Continuous (evaluationVector Y hμ) :=
  (InnerProductSpace.toDual ℂ (space Y hμ)).symm.continuous.comp (continuous_evaluation Y hμ)

/-- Reflection leaves the evaluation vector of the even band unchanged. -/
theorem evaluationVector_even (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ) (x : ℝ) :
    evaluationVector Y hμ (-x) = evaluationVector Y hμ x := by
  have he : evaluation Y hμ (-x) = evaluation Y hμ x :=
    ContinuousLinearMap.ext fun f ↦ evaluation_even Y hμ f x
  simp only [evaluationVector, he]

/-- The evaluation vectors inherit the uniform operator norm bound. -/
theorem norm_evaluationVector_le (Y : ℝ) (hY : 0 ≤ Y) {μ : Measure ℝ}
    (hμ : volume ≤ μ) (x : ℝ) : ‖evaluationVector Y hμ x‖ ≤ Real.sqrt (2 * Y) := by
  simpa [evaluationVector] using norm_evaluation_le Y hY hμ x

/-- The evaluation vectors reproduce each vector of the even weighted band almost everywhere. -/
theorem evaluationVector_reproduces (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ)
    (hμac : μ ≪ volume) (f : space Y hμ) :
    (fun x ↦ ⟪evaluationVector Y hμ x, f⟫_ℂ) =ᵐ[μ] (f.val : ℝ → ℂ) := by
  simpa only [← InnerProductSpace.toDual_apply_apply (𝕜 := ℂ), evaluationVector,
    LinearIsometryEquiv.apply_symm_apply] using evaluation_ae Y hμ hμac f

end RealPWBand

end RiemannMasullo
