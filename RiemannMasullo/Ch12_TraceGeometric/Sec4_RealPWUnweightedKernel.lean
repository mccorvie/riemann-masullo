module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWUnweightedLowerTrace
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWBandDensity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Fourier.LpSpace

/-! # The reproducing kernel of the unweighted even band, in closed form

Paper: Theorem 12.4.1.1, pp. 514–517, the real term, in the fixed-bandwidth model of the real
place of `ℚ` of #7354, without weight. This is the setting of A. Connes, *Trace formula in
noncommutative geometry and the zeros of the Riemann zeta function*, §VII, Theorem 4, p. 31,
for `k = ℚ` and `S = {∞}`: the Hilbert space is the space of even functions in `L²` of
Lebesgue measure.

The evaluation vectors of `RealPWBand` are defined abstractly, by the Riesz representation.
Without weight they are given by the kernel
`Y (sinc (2πY (y - x)) + sinc (2πY (y + x)))` (`realPWBand_evaluation_evaluationVector`). With
this the diagonal integral of the cutoff of a dilation is an explicit integral of `sinc`.

Reconstruction: The paper does not state this. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology InnerProductSpace Real

namespace RiemannMasullo.Isolated

/-- The cosine wave at `x` cut off to the band `[-Y, Y]`: the Fourier transform of the
reproducing kernel of the even band at `x`. -/
def bandCos (Y x : ℝ) : ℝ → ℂ :=
  (Icc (-Y) Y).indicator fun ξ ↦ ((Real.cos (2 * π * (x * ξ)) : ℝ) : ℂ)

/-- The reproducing kernel of the even band of bandwidth `Y` in `L²` of Lebesgue measure, in
closed form: `Y (sinc (2πY (y - x)) + sinc (2πY (y + x)))`. -/
def bandKernel (Y x y : ℝ) : ℝ :=
  Y * (Real.sinc (2 * π * Y * (y - x)) + Real.sinc (2 * π * Y * (y + x)))

/-- The integral of `exp (i a ξ)` over `[-Y, Y]` is `2 Y sinc (a Y)`. -/
theorem integral_exp_mul_I_symm (a Y : ℝ) :
    ∫ ξ in (-Y)..Y, Complex.exp (((a * ξ : ℝ) : ℂ) * Complex.I) =
      ((2 * Y * Real.sinc (a * Y) : ℝ) : ℂ) := by
  by_cases ha : a = 0
  · subst ha
    simp
    ring
  by_cases hY0 : Y = 0
  · subst hY0
    simp
  have hc : (a : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr ha) Complex.I_ne_zero
  have h := integral_exp_mul_complex (a := -Y) (b := Y) hc
  have hint : (fun ξ : ℝ ↦ Complex.exp (((a * ξ : ℝ) : ℂ) * Complex.I)) =
      fun ξ : ℝ ↦ Complex.exp ((a : ℂ) * Complex.I * ξ) := by
    funext ξ
    congr 1
    push_cast
    ring
  rw [hint, h, Real.sinc_of_ne_zero (mul_ne_zero ha hY0)]
  have e1 : (a : ℂ) * Complex.I * (Y : ℂ) = ((a : ℂ) * Y) * Complex.I := by ring
  have e2 : (a : ℂ) * Complex.I * ((-Y : ℝ) : ℂ) = -((a : ℂ) * Y) * Complex.I := by
    push_cast
    ring
  have hsin : Complex.exp ((a : ℂ) * Y * Complex.I) - Complex.exp (-((a : ℂ) * Y) * Complex.I) =
      2 * Complex.I * Complex.sin ((a : ℂ) * Y) := by
    rw [Complex.sin]
    linear_combination (Complex.exp ((a : ℂ) * Y * Complex.I) -
      Complex.exp (-((a : ℂ) * Y) * Complex.I)) * Complex.I_mul_I
  rw [e1, e2, hsin]
  have hY' : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY0
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  push_cast
  field_simp

/-- The inverse Fourier transform of the cut-off cosine wave is the closed-form kernel. -/
theorem fourierInv_bandCos {Y : ℝ} (hY : 0 ≤ Y) (x y : ℝ) :
    𝓕⁻ (bandCos Y x) y = ((bandKernel Y x y : ℝ) : ℂ) := by
  rw [Real.fourierInv_eq']
  have h1 : ∀ v : ℝ, Complex.exp (((2 * π * inner ℝ v y : ℝ) : ℂ) * Complex.I) • bandCos Y x v =
      (Icc (-Y) Y).indicator (fun v : ℝ ↦ (1 / 2 : ℂ) *
        (Complex.exp ((((2 * π * (y + x)) * v : ℝ) : ℂ) * Complex.I) +
          Complex.exp ((((2 * π * (y - x)) * v : ℝ) : ℂ) * Complex.I))) v := by
    intro v
    by_cases hv : v ∈ Icc (-Y) Y
    · have hin : inner ℝ v y = y * v := by simp
      have e1 : ((((2 * π * (y + x)) * v : ℝ) : ℂ)) * Complex.I =
          ((2 * π * (y * v) : ℝ) : ℂ) * Complex.I + ((2 * π * (x * v) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      have e2 : ((((2 * π * (y - x)) * v : ℝ) : ℂ)) * Complex.I =
          ((2 * π * (y * v) : ℝ) : ℂ) * Complex.I + -((2 * π * (x * v) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [bandCos, indicator_of_mem hv, indicator_of_mem hv, smul_eq_mul, Complex.ofReal_cos,
        Complex.cos, hin, e1, e2, Complex.exp_add, Complex.exp_add]
      ring
    · rw [bandCos, indicator_of_notMem hv, indicator_of_notMem hv, smul_zero]
  have hc (a : ℝ) : Continuous fun v : ℝ ↦ Complex.exp (((a * v : ℝ) : ℂ) * Complex.I) := by
    fun_prop
  rw [integral_congr_ae (ae_of_all _ h1), integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -Y ≤ Y),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((hc _).intervalIntegrable _ _) ((hc _).intervalIntegrable _ _),
    integral_exp_mul_I_symm, integral_exp_mul_I_symm, bandKernel,
    show 2 * π * (y + x) * Y = 2 * π * Y * (y + x) by ring,
    show 2 * π * (y - x) * Y = 2 * π * Y * (y - x) by ring]
  push_cast
  ring

/-- The cut-off cosine wave is square integrable. -/
theorem bandCos_memLp (Y x : ℝ) : MemLp (bandCos Y x) 2 volume := by
  unfold bandCos
  rw [memLp_indicator_iff_restrict (s := Icc (-Y) Y) measurableSet_Icc.nullMeasurableSet]
  have : IsFiniteMeasure (volume.restrict (Icc (-Y) Y)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hc : Continuous fun ξ : ℝ ↦ ((Real.cos (2 * π * (x * ξ)) : ℝ) : ℂ) := by fun_prop
  exact MemLp.of_bound hc.aestronglyMeasurable 1
    (ae_of_all _ fun ξ ↦ by
      rw [Complex.norm_real]
      exact Real.abs_cos_le_one _)

/-- The cut-off cosine wave is integrable. -/
theorem bandCos_integrable (Y x : ℝ) : Integrable (bandCos Y x) := by
  unfold bandCos
  rw [integrable_indicator_iff measurableSet_Icc]
  exact Continuous.integrableOn_Icc (by fun_prop)

/-- The closed-form kernel is continuous in its second variable. -/
theorem continuous_bandKernel (Y x : ℝ) :
    Continuous fun y ↦ ((bandKernel Y x y : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp (continuous_const.mul
    ((Real.continuous_sinc.comp (by fun_prop)).add (Real.continuous_sinc.comp (by fun_prop))))

/-- The closed-form kernel is even in its second variable. -/
theorem bandKernel_neg (Y x y : ℝ) : bandKernel Y x (-y) = bandKernel Y x y := by
  unfold bandKernel
  rw [show 2 * π * Y * (-y - x) = -(2 * π * Y * (y + x)) by ring,
    show 2 * π * Y * (-y + x) = -(2 * π * Y * (y - x)) by ring, Real.sinc_neg, Real.sinc_neg,
    add_comm]

/-- The closed-form kernel is, almost everywhere, the inverse Fourier transform in `L²` of the
cut-off cosine wave. In particular it is square integrable. -/
theorem bandKernel_ae {Y : ℝ} (hY : 0 ≤ Y) (x : ℝ) :
    (fun y ↦ ((bandKernel Y x y : ℝ) : ℂ)) =ᵐ[volume]
      ((𝓕⁻ ((bandCos_memLp Y x).toLp (bandCos Y x)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
  let F : Lp ℂ 2 (volume : Measure ℝ) := (bandCos_memLp Y x).toLp _
  have hFae : (F : ℝ → ℂ) =ᵐ[volume] bandCos Y x := MemLp.coeFn_toLp _
  have hFi : Integrable (F : ℝ → ℂ) := (bandCos_integrable Y x).congr hFae.symm
  have h := fourierInv_ae_L2 F hFi
  have hpt : 𝓕⁻ (F : ℝ → ℂ) = fun y ↦ ((bandKernel Y x y : ℝ) : ℂ) := by
    funext y
    rw [← fourierInv_bandCos hY x y, Real.fourierInv_eq', Real.fourierInv_eq']
    exact integral_congr_ae (hFae.mono fun v hv ↦ by simp only [hv])
  rw [hpt] at h
  exact h

section Kernel

variable (Y : ℝ) (hs : (0 : ℝ) ≤ 0)

local notation "μ₀" => realPWIntervalMeasure 0 0
local notation "hμ₀" => volume_le_realPWIntervalMeasure 0 0 hs
local notation "V₀" => RealPWBand.space Y hμ₀
local notation "ev" => RealPWBand.evaluation Y hμ₀
local notation "evv" => RealPWBand.evaluationVector Y hμ₀

/-- The closed-form kernel at `x` is the pointwise representative of a vector of the unweighted
even band. -/
theorem exists_realPWBand_bandKernel (hY : 0 ≤ Y) (x : ℝ) :
    ∃ f : V₀, (fun y ↦ ev y f) = fun y ↦ ((bandKernel Y x y : ℝ) : ℂ) := by
  let F : Lp ℂ 2 (volume : Measure ℝ) := (bandCos_memLp Y x).toLp _
  have hκ2 : MemLp (fun y ↦ ((bandKernel Y x y : ℝ) : ℂ)) 2 volume :=
    (memLp_congr_ae (bandKernel_ae hY x)).mpr (Lp.memLp _)
  have hκμ : MemLp (fun y ↦ ((bandKernel Y x y : ℝ) : ℂ)) 2 μ₀ := by
    rw [realPWIntervalMeasure_zero_zero]
    exact hκ2
  refine RealPWBand.exists_evaluation_eq_of_band Y hμ₀ (continuous_bandKernel Y x)
    (fun y ↦ by rw [bandKernel_neg]) hκμ ?_
  have heq : (hκμ.mono_measure hμ₀).toLp (fun y ↦ ((bandKernel Y x y : ℝ) : ℂ)) = 𝓕⁻ F :=
    Lp.ext ((MemLp.coeFn_toLp _).trans (bandKernel_ae hY x))
  rw [heq, FourierTransform.fourier_fourierInv_eq]
  filter_upwards [ae_restrict_of_ae (MemLp.coeFn_toLp (bandCos_memLp Y x)),
    ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc.compl] with t ht hmem
  rw [ht, bandCos, indicator_of_notMem hmem]

omit hs in
/-- The cut-off cosine wave at `x` pairs with the Fourier transform of an even Schwartz
function with spectrum in the band to the value of that function at `x`: Fourier inversion. -/
theorem integral_bandCos_mul_fourier (x : ℝ) (η : 𝓢(ℝ, ℂ)) (he : Function.Even (η : ℝ → ℂ))
    (hb : ∀ ξ ∉ Icc (-Y) Y, (𝓕 η) ξ = 0) :
    ∫ ξ, (starRingEnd ℂ) (bandCos Y x ξ) * (𝓕 η) ξ = η x := by
  have h1 : ∀ ξ, (starRingEnd ℂ) (bandCos Y x ξ) * (𝓕 η) ξ =
      ((Real.cos (2 * π * (x * ξ)) : ℝ) : ℂ) * (𝓕 η) ξ := by
    intro ξ
    by_cases hξ : ξ ∈ Icc (-Y) Y
    · rw [bandCos, indicator_of_mem hξ, Complex.conj_ofReal]
    · rw [hb ξ hξ, mul_zero, mul_zero]
  have hint (w : ℝ) : Integrable (fun v : ℝ ↦
      Complex.exp (((2 * π * inner ℝ v w : ℝ) : ℂ) * Complex.I) • (𝓕 η) v) := by
    have hc : Continuous fun v : ℝ ↦
        Complex.exp (((2 * π * inner ℝ v w : ℝ) : ℂ) * Complex.I) := by fun_prop
    refine (𝓕 η).integrable.norm.mono' (hc.smul (𝓕 η).continuous).aestronglyMeasurable
      (ae_of_all _ fun v ↦ ?_)
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hinv (w : ℝ) : ∫ v, Complex.exp (((2 * π * inner ℝ v w : ℝ) : ℂ) * Complex.I) •
      (𝓕 η) v = η w := by
    have h := Real.fourierInv_eq' ((𝓕 η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) w
    have h' : 𝓕⁻ ((𝓕 η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) w = η w := by
      rw [← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_fourier_eq]
    exact h.symm.trans h'
  have h2 : ∀ ξ : ℝ, ((Real.cos (2 * π * (x * ξ)) : ℝ) : ℂ) * (𝓕 η) ξ = (1 / 2 : ℂ) *
      (Complex.exp (((2 * π * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) • (𝓕 η) ξ +
        Complex.exp (((2 * π * inner ℝ ξ (-x) : ℝ) : ℂ) * Complex.I) • (𝓕 η) ξ) := by
    intro ξ
    have hin1 : inner ℝ ξ x = x * ξ := by simp
    have hin2 : inner ℝ ξ (-x) = -(x * ξ) := by simp
    have e : ((2 * π * -(x * ξ) : ℝ) : ℂ) * Complex.I =
        -((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hin1, hin2, Complex.ofReal_cos, Complex.cos, smul_eq_mul, smul_eq_mul, e]
    ring
  rw [integral_congr_ae (ae_of_all _ h1), integral_congr_ae (ae_of_all _ h2),
    integral_const_mul, integral_add (hint x) (hint (-x)), hinv, hinv, he x]
  ring

/-- The band vector with the closed-form kernel at `x` as its values represents the evaluation
at `x`. The identity is checked on the band vectors given by Schwartz functions, by the
Plancherel identity and Fourier inversion, and these are dense (#7770). -/
theorem inner_eq_evaluation_of_bandKernel (hY : 0 < Y) (x : ℝ) (f : V₀)
    (hf : (fun y ↦ ev y f) = fun y ↦ ((bandKernel Y x y : ℝ) : ℂ)) (h : V₀) :
    ⟪f, h⟫_ℂ = ev x h := by
  have hμac := realPWIntervalMeasure_absolutelyContinuous 0 0
  have hvol : (volume : Measure ℝ) ≪ μ₀ := Measure.absolutelyContinuous_of_le hμ₀
  have hclosed : IsClosed {h : V₀ | ⟪f, h⟫_ℂ = ev x h} :=
    isClosed_eq (continuous_const.inner continuous_id) (ev x).continuous
  have hdense := dense_realPWBand_schwartz (Y := Y) (α := 0) (s := 0) le_rfl (by norm_num) hs hY
  refine (hclosed.closure_subset_iff.mpr ?_) (hdense h)
  rintro h ⟨η, he, hb, hη⟩
  change ⟪f, h⟫_ℂ = ev x h
  rw [congrFun hη x]
  let F : Lp ℂ 2 (volume : Measure ℝ) := (bandCos_memLp Y x).toLp _
  have hκ2 : MemLp (fun y ↦ ((bandKernel Y x y : ℝ) : ℂ)) 2 volume :=
    (memLp_congr_ae (bandKernel_ae hY.le x)).mpr (Lp.memLp _)
  have hκF : hκ2.toLp _ = 𝓕⁻ F := Lp.ext ((MemLp.coeFn_toLp _).trans (bandKernel_ae hY.le x))
  have h1 : ⟪f, h⟫_ℂ = ⟪hκ2.toLp _, η.toLp 2 volume⟫_ℂ := by
    change ⟪(f.val : Lp ℂ 2 μ₀), (h.val : Lp ℂ 2 μ₀)⟫_ℂ = _
    rw [L2.inner_def, L2.inner_def, integral_realPWIntervalMeasure_zero_zero]
    apply integral_congr_ae
    filter_upwards [hvol.ae_eq (RealPWBand.evaluation_ae Y hμ₀ hμac f),
      hvol.ae_eq (RealPWBand.evaluation_ae Y hμ₀ hμac h), hκ2.coeFn_toLp,
      η.coeFn_toLp 2 volume] with y a1 a2 a3 a4
    have e1 : (f.val : ℝ → ℂ) y = ((bandKernel Y x y : ℝ) : ℂ) := a1.symm.trans (congrFun hf y)
    have e2 : (h.val : ℝ → ℂ) y = η y := a2.symm.trans (congrFun hη y)
    rw [e1, e2, a3, a4]
  have h2 : ⟪hκ2.toLp _, η.toLp 2 volume⟫_ℂ = ⟪F, (𝓕 η).toLp 2 volume⟫_ℂ := by
    rw [← Lp.inner_fourier_eq, hκF, FourierTransform.fourier_fourierInv_eq,
      SchwartzMap.toLp_fourier_eq]
  have h3 : ⟪F, (𝓕 η).toLp 2 volume⟫_ℂ =
      ∫ ξ, (starRingEnd ℂ) (bandCos Y x ξ) * (𝓕 η) ξ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(bandCos_memLp Y x).coeFn_toLp, (𝓕 η).coeFn_toLp 2 volume] with ξ a b
    rw [show (F : ℝ → ℂ) ξ = bandCos Y x ξ from a, b, RCLike.inner_apply]
    ring
  rw [h1, h2, h3, integral_bandCos_mul_fourier Y x η he hb]

/-- Reconstruction: without weight, the reproducing kernel of the even band is the closed-form
kernel: the value at `y` of the evaluation vector at `x` is
`Y (sinc (2πY (y - x)) + sinc (2πY (y + x)))`. -/
theorem realPWBand_evaluation_evaluationVector (hY : 0 < Y) (x y : ℝ) :
    ev y (evv x) = ((bandKernel Y x y : ℝ) : ℂ) := by
  obtain ⟨f, hf⟩ := exists_realPWBand_bandKernel Y hs hY.le x
  have hfe : f = evv x := by
    refine ext_inner_right ℂ fun h ↦ ?_
    have h2 : ev x h = ⟪evv x, h⟫_ℂ := by
      rw [← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]
    rw [← h2]
    exact inner_eq_evaluation_of_bandKernel Y hs hY x f hf h
  rw [← hfe]
  exact congrFun hf y

end Kernel

end RiemannMasullo.Isolated
