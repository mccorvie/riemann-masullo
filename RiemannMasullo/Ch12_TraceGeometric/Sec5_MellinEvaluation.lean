module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import RiemannMasullo.Ch11_ShellStructure.Sec2a

/-! # Mellin evaluations in the order-zero strip

The reciprocal strip weight gives the exact norm of the ambient Mellin functional
on each vertical line. Left translation acts on it by the norm character.
-/

@[expose] public noncomputable section
open NumberField MeasureTheory Set Metric
open scoped NNReal

namespace RiemannMasullo

/-- The log-coordinate square mass of the order-zero Mellin evaluation at offset `b`.
It is finite and depends only on the real part of the Mellin parameter. -/
private theorem mellin_radial_mass_order_zero {b : ℝ} (hb : |b| < 1 / 2) :
    Integrable (fun x : ℝ ↦ Real.exp (2 * b * x - |x|)) ∧
    (∫ x : ℝ, Real.exp (2 * b * x - |x|)) = 2 / (1 - 4 * b ^ 2) := by
  obtain ⟨hl, hr⟩ := abs_lt.mp hb
  have h₁ : 0 < 2 * b + 1 := by linarith
  have h₂ : 2 * b - 1 < 0 := by linarith
  let f (x : ℝ) := Real.exp (2 * b * x - |x|)
  have hn : EqOn f (fun x ↦ Real.exp ((2 * b + 1) * x)) (Iic 0) := by
    intro x hx
    dsimp [f]
    rw [abs_of_nonpos hx]
    congr 1
    ring
  have hp : EqOn f (fun x ↦ Real.exp ((2 * b - 1) * x)) (Ioi 0) := by
    intro x hx
    dsimp [f]
    rw [abs_of_pos hx]
    congr 1
    ring
  have hi₁ : IntegrableOn f (Iic 0) := (integrableOn_exp_mul_Iic h₁ 0).congr_fun hn.symm measurableSet_Iic
  have hi₂ : IntegrableOn f (Ioi 0) := (integrableOn_exp_mul_Ioi h₂ 0).congr_fun hp.symm measurableSet_Ioi
  have hi : Integrable f := by simpa using hi₁.union hi₂
  refine ⟨hi, ?_⟩
  change (∫ x, f x) = _
  rw [← integral_add_compl measurableSet_Iic hi, compl_Iic, setIntegral_congr_fun measurableSet_Iic hn,
    setIntegral_congr_fun measurableSet_Ioi hp, integral_exp_mul_Iic h₁, integral_exp_mul_Ioi h₂]
  simp only [mul_zero, Real.exp_zero]
  have hden : 1 - 4 * b ^ 2 = -(2*b+1)*(2*b-1) := by ring
  rw [hden]
  field_simp [h₁.ne', h₂.ne]
  ring

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
set_option quotPrecheck false

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "ν𝔽" => canonicalModulatedHaar m𝔽 hm𝔽
local notation "ℓ" => logIdeleClassNorm F
local notation "η𝔽" => intervalSobolevMeasure μ𝔽 ℓ (-(1 / 2)) (1 / 2) 0 true
local instance mellinCanonicalHaar : (ν𝔽).IsHaarMeasure :=
  (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1

private theorem mellin_density : η𝔽 = (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (Real.exp (-|ℓ g|))) := by
  have he (x : ℝ) : intervalSobolevDensity (-(1 / 2)) (1 / 2) 0 x = Real.exp |x| := by
    unfold intervalSobolevDensity
    norm_num
    rw [← Real.exp_monotone.map_max]
    congr 1
    rw [abs_eq_max_neg, max_comm]
  simp only [intervalSobolevMeasure, ite_true, he, Real.exp_neg]

/-- Tamagawa almost-everywhere representatives can be recovered from the reciprocal
order-zero strip measure because its density is strictly positive. -/
theorem tamagawa_absolutelyContinuous_orderZeroDualMeasure : μ𝔽 ≪ η𝔽 := by
  rw [mellin_density]
  exact withDensity_absolutelyContinuous'
    (Real.continuous_exp.comp (orbitalJet_logNorm_continuous (F := F)).abs.neg).measurable.ennreal_ofReal.aemeasurable
    (.of_forall (fun g ↦ ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)))

/-- The Mellin kernel belongs to the actual reciprocal-weight L² space throughout the
open strip. Its squared mass is independent of the imaginary part of the parameter. -/
theorem orderZeroMellinKernel_square_mass (z : ℂ) (hz : |z.re| < 1 / 2) :
    MemLp (fun g : C𝔽 ↦ Complex.exp (z * ℓ g)) 2 η𝔽 ∧
    (∫ g : C𝔽, ‖Complex.exp (z * ℓ g)‖ ^ 2 ∂η𝔽) =
      (Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) * (2 / (1 - 4 * z.re ^ 2)) := by
  let f (x : ℝ) := Real.exp (2 * z.re * x - |x|)
  have hf : Continuous f := by unfold f; fun_prop
  have hweight : Measurable (fun g : C𝔽 ↦ ENNReal.ofReal (Real.exp (-|ℓ g|))) :=
    (Real.continuous_exp.comp (orbitalJet_logNorm_continuous (F := F)).abs.neg).measurable.ennreal_ofReal
  have hlog : MeasurePreserving ℓ μ𝔽 (Measure.haarScalarFactor μ𝔽 ν𝔽 • volume) := by
    conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν𝔽]
    exact (orbitalJet_logNorm_measurePreserving (F := F)).smul_measure _
  have hl (g : C𝔽) : Real.exp (-|ℓ g|) * ‖Complex.exp (z * ℓ g)‖ ^ 2 = f (ℓ g) := by
    rw [Complex.norm_exp, Complex.re_mul_ofReal, ← Real.exp_nat_mul, ← Real.exp_add]
    dsimp [f]
    congr 1
    ring
  obtain ⟨hi, hv⟩ := mellin_radial_mass_order_zero hz
  constructor
  · apply (memLp_two_iff_integrable_sq_norm (by exact
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        orbitalJet_logNorm_continuous))).aestronglyMeasurable)).mpr
    rw [mellin_density, integrable_withDensity_iff hweight (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    have hi' := hlog.integrable_comp_of_integrable
      (hi.smul_measure_nnreal (c := Measure.haarScalarFactor μ𝔽 ν𝔽))
    apply hi'.congr (.of_forall (fun g ↦ ?_))
    simpa [ENNReal.toReal_ofReal (Real.exp_pos _).le, Function.comp_apply, f, mul_comm] using (hl g).symm
  · rw [mellin_density, integral_withDensity_eq_integral_toReal_smul hweight
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    calc
      _ = ∫ g : C𝔽, f (ℓ g) ∂μ𝔽 := by
        apply integral_congr_ae (.of_forall (fun g ↦ ?_))
        simpa [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul] using hl g
      _ = ∫ x : ℝ, f x ∂(Measure.haarScalarFactor μ𝔽 ν𝔽 • volume) := by
        rw [← hlog.map_eq, integral_map hlog.measurable.aemeasurable hf.aestronglyMeasurable]
      _ = _ := by
        rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, show (∫ x : ℝ, f x) = _ from hv]

local notation "W" => CompactIntervalSobolev μ𝔽 ℓ (-(1 / 2)) (1 / 2) 0
local notation "D" => (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-(1 / 2)) (1 / 2) 0
  (by norm_num) (le_refl (0 : ℝ))).exists.choose

/-- Mellin evaluation on the order-zero strip as a continuous linear functional. -/
def orderZeroMellinEvaluation (z : ℂ) (hz : |z.re| < 1 / 2) : W →L[ℂ] ℂ :=
  (D).symm ((orderZeroMellinKernel_square_mass (F := F) z hz).1.toLp
    (fun g : C𝔽 ↦ Complex.exp (z * ℓ g)))

/-- The squared operator norm is constant on each vertical line and has first-order
poles at the strip edges. The normalization is the ratio of the Tamagawa and canonical
modulated Haar measures. -/
theorem orderZeroMellinEvaluation_norm_sq (z : ℂ) (hz : |z.re| < 1 / 2) :
    ‖orderZeroMellinEvaluation (F := F) z hz‖ ^ 2 =
      (Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) * (2 / (1 - 4 * z.re ^ 2)) := by
  let u : Lp ℂ 2 η𝔽 := (orderZeroMellinKernel_square_mass (F := F) z hz).1.toLp
    (fun g : C𝔽 ↦ Complex.exp (z * ℓ g))
  change ‖(D).symm u‖ ^ 2 = _
  rw [LinearIsometryEquiv.norm_map]
  have hsq : (inner ℂ u u).re = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  rw [← hsq, L2.inner_def, ← Complex.reCLM_apply,
    ← Complex.reCLM.integral_comp_comm (L2.integrable_inner u u)]
  refine (integral_congr_ae ?_).trans (orderZeroMellinKernel_square_mass z hz).2
  filter_upwards [(orderZeroMellinKernel_square_mass (F := F) z hz).1.coeFn_toLp] with g hg
  change (inner ℂ (u g) (u g)).re = _
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (u g)).trans (congrArg (fun w : ℂ ↦ ‖w‖ ^ 2) hg)

private theorem mellin_den_pos {b : ℝ} (hb : |b| < 1 / 2) : 0 < 1 - 4 * b ^ 2 := by
  obtain ⟨hl, hr⟩ := abs_lt.mp hb
  nlinarith [mul_pos (sub_pos.mpr hr) (show 0 < 1 / 2 + b by linarith)]

/-- Mellin evaluation is nonzero at every interior point of the critical strip. -/
theorem orderZeroMellinEvaluation_norm_pos (z : ℂ) (hz : |z.re| < 1 / 2) :
    0 < ‖orderZeroMellinEvaluation (F := F) z hz‖ := by
  have hc : 0 < (Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) := by
    exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν𝔽
  have hp := mul_pos hc (div_pos (by norm_num : (0 : ℝ) < 2) (mellin_den_pos hz))
  rw [← orderZeroMellinEvaluation_norm_sq (F := F) z hz] at hp
  nlinarith [norm_nonneg (orderZeroMellinEvaluation (F := F) z hz)]

/-- Bounding the real offsets by a fixed interior offset bounds all the evaluation norms. -/
theorem orderZeroMellinEvaluation_norm_le {z w : ℂ} (hzw : |z.re| ≤ |w.re|)
    (hw : |w.re| < 1 / 2) : ‖orderZeroMellinEvaluation (F := F) z (hzw.trans_lt hw)‖ ≤
      ‖orderZeroMellinEvaluation (F := F) w hw‖ := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (norm_nonneg _)
  rw [orderZeroMellinEvaluation_norm_sq, orderZeroMellinEvaluation_norm_sq]
  apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
  apply div_le_div_of_nonneg_left (by norm_num) (mellin_den_pos hw)
  have h := pow_le_pow_left₀ (abs_nonneg _) hzw 2
  simp only [sq_abs] at h
  linarith

/-- Mellin evaluation is integration of the original representative against the kernel
with respect to Tamagawa measure. -/
theorem orderZeroMellinEvaluation_apply (z : ℂ) (hz : |z.re| < 1 / 2) (x : W) :
    Integrable (fun g : C𝔽 ↦ x g * Complex.exp (z * ℓ g)) μ𝔽 ∧
    orderZeroMellinEvaluation z hz x = ∫ g : C𝔽, x g * Complex.exp (z * ℓ g) ∂μ𝔽 := by
  let u : Lp ℂ 2 η𝔽 := (orderZeroMellinKernel_square_mass (F := F) z hz).1.toLp
    (fun g : C𝔽 ↦ Complex.exp (z * ℓ g))
  have h := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-(1 / 2)) (1 / 2) 0 (by norm_num)
    (le_refl (0 : ℝ))).exists.choose_spec ((D).symm u) x
  change Integrable (fun g ↦ x g * (D ((D).symm u)) g) μ𝔽 ∧
    (D).symm u x = ∫ g, x g * (D ((D).symm u)) g ∂μ𝔽 at h
  rw [(D).apply_symm_apply] at h
  have hu : (u : C𝔽 → ℂ) =ᵐ[μ𝔽] (fun g ↦ Complex.exp (z * ℓ g)) :=
    (tamagawa_absolutelyContinuous_orderZeroDualMeasure (F := F)).ae_le
      ((orderZeroMellinKernel_square_mass (F := F) z hz).1.coeFn_toLp)
  have heq : (fun g : C𝔽 ↦ x g * u g) =ᵐ[μ𝔽] (fun g ↦ x g * Complex.exp (z * ℓ g)) :=
    hu.mono (fun g hg ↦ congrArg (x g * ·) hg)
  exact ⟨h.1.congr heq, h.2.trans (integral_congr_ae heq)⟩

/-- Ambient left translation multiplies the Mellin evaluation by its character value. -/
theorem orderZeroMellinEvaluation_translate (z : ℂ) (hz : |z.re| < 1 / 2) (g : C𝔽) (x : W) :
    orderZeroMellinEvaluation z hz (hardySobolevTranslation μ𝔽 m𝔽 (-(1 / 2)) (1 / 2) 0
      (by norm_num) (le_refl (0 : ℝ)) g x) = Complex.exp (z * ℓ g) * orderZeroMellinEvaluation z hz x := by
  rw [(orderZeroMellinEvaluation_apply z hz _).2, (orderZeroMellinEvaluation_apply z hz x).2]
  have hT := hardySobolevTranslation_apply μ𝔽 m𝔽 (-(1 / 2)) (1 / 2) 0 (by norm_num) (le_refl (0 : ℝ)) g x
  have hlog (y : C𝔽) : ℓ (g * y) = ℓ g + ℓ y := by
    change Real.log ((ideleClassNorm F (g * y)).val : ℝ) = _
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.mpr (ideleClassNorm F g).ne_zero)
      (NNReal.coe_ne_zero.mpr (ideleClassNorm F y).ne_zero)]
  calc
    _ = ∫ y : C𝔽, x (g⁻¹ * y) * Complex.exp (z * ℓ y) ∂μ𝔽 :=
      integral_congr_ae (hT.mono fun y hy ↦ congrArg (· * Complex.exp (z * ℓ y)) hy)
    _ = _ := by
      rw [← integral_mul_left_eq_self (fun y ↦ x (g⁻¹ * y) * Complex.exp (z * ℓ y)) g,
        ← integral_const_mul]
      apply integral_congr_ae (.of_forall (fun y ↦ ?_))
      rw [inv_mul_cancel_left, hlog, Complex.ofReal_add, mul_add, Complex.exp_add]
      ring

private theorem mellin_derivative_envelope {c r b : ℝ} (hc : 0 < c) (hb : |b| + c ≤ r) (t : ℝ) :
    |t| * Real.exp (b * t) ≤ c⁻¹ * (Real.exp (r * t) + Real.exp (-r * t)) := by
  have ht : |t| ≤ c⁻¹ * Real.exp (c * |t|) := by
    rw [← div_eq_inv_mul, le_div_iff₀ hc]
    linarith [Real.add_one_le_exp (c * |t|), mul_comm c |t|]
  have he : c * |t| + b * t ≤ r * |t| := calc
    _ ≤ c * |t| + |b| * |t| := by rw [← abs_mul]; linarith [le_abs_self (b * t)]
    _ ≤ _ := by simpa [add_mul, add_comm] using mul_le_mul_of_nonneg_right hb (abs_nonneg t)
  calc
    _ ≤ (c⁻¹ * Real.exp (c * |t|)) * Real.exp (b * t) := mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
    _ = c⁻¹ * Real.exp (c * |t| + b * t) := by rw [Real.exp_add, mul_assoc]
    _ ≤ c⁻¹ * Real.exp (r * |t|) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (inv_nonneg.mpr hc.le)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      rcases le_total 0 t with h | h
      · rw [abs_of_nonneg h]
        linarith [Real.exp_pos (-r * t)]
      · rw [abs_of_nonpos h, mul_neg, ← neg_mul]
        linarith [Real.exp_pos (r * t)]

/-- The Tamagawa Mellin integral of an order-zero Sobolev vector has derivative
given by insertion of the log idèle-class norm on the open half-strip. -/
theorem hasDerivAt_orderZeroMellinIntegral (x : W) {z : ℂ} (hz : |z.re| < 1 / 2) :
    HasDerivAt (fun w : ℂ ↦ ∫ g : C𝔽, x g * Complex.exp (w * ℓ g) ∂μ𝔽)
      (∫ g : C𝔽, x g * ((ℓ g : ℂ) * Complex.exp (z * ℓ g)) ∂μ𝔽) z := by
  let c := (1 / 2 - |z.re|) / 3
  let r := |z.re| + 2 * c
  have hc : 0 < c := by dsimp [c]; linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr' : r < 1 / 2 := by dsimp [r, c]; linarith
  have hexp (b : ℝ) (hb : |b| < 1 / 2) :
      Integrable (fun g : C𝔽 ↦ ‖x g‖ * Real.exp (b * ℓ g)) μ𝔽 := by
    have h := ((orderZeroMellinEvaluation_apply (b : ℂ) (by simpa using hb) x).1).norm
    simpa [Complex.norm_exp, Complex.re_mul_ofReal] using h
  have hbd := ((hexp r (by rwa [abs_of_nonneg hr])).add
    (hexp (-r) (by rwa [abs_neg, abs_of_nonneg hr]))).const_mul c⁻¹
  have hfm : AEStronglyMeasurable (fun g : C𝔽 ↦ x g) μ𝔽 := by
    simpa using (orderZeroMellinEvaluation_apply 0 (by norm_num) x).1.aestronglyMeasurable
  have hlog : Continuous (fun g : C𝔽 ↦ (ℓ g : ℂ)) :=
    Complex.continuous_ofReal.comp orbitalJet_logNorm_continuous
  have hce (w : ℂ) : Continuous (fun g : C𝔽 ↦ Complex.exp (w * ℓ g)) :=
    Complex.continuous_exp.comp (continuous_const.mul hlog)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (w : ℂ) (g : C𝔽) ↦ x g * Complex.exp (w * ℓ g))
    (F' := fun (w : ℂ) (g : C𝔽) ↦ x g * ((ℓ g : ℂ) * Complex.exp (w * ℓ g)))
    (ball_mem_nhds z hc) (.of_forall fun w ↦ hfm.mul (hce w).aestronglyMeasurable)
    (orderZeroMellinEvaluation_apply z hz x).1 (hfm.mul (hlog.mul (hce z)).aestronglyMeasurable)
    (.of_forall fun g w hw ↦ ?_) hbd (.of_forall fun g w _ ↦ ?_)).2
  · have h₁ : |w.re - z.re| ≤ ‖w - z‖ := by simpa using Complex.abs_re_le_norm (w - z)
    have h₂ : ‖w - z‖ < c := by simpa [dist_eq_norm] using hw
    have h₃ : |w.re| ≤ |z.re| + |w.re - z.re| := by simpa using abs_add_le z.re (w.re - z.re)
    have h := mellin_derivative_envelope (r := r) hc (b := w.re) (by dsimp [r]; linarith) (ℓ g)
    change ‖x g * ((ℓ g : ℂ) * Complex.exp (w * ℓ g))‖ ≤
      c⁻¹ * (‖x g‖ * Real.exp (r * ℓ g) + ‖x g‖ * Real.exp (-r * ℓ g))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, Complex.re_mul_ofReal]
    calc
      _ ≤ ‖x g‖ * (c⁻¹ * (Real.exp (r * ℓ g) + Real.exp (-r * ℓ g))) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = _ := by rw [mul_left_comm, mul_add]
  · have h := (((hasDerivAt_id w).mul_const (ℓ g : ℂ)).cexp).const_mul (x g)
    simpa only [id_eq, one_mul, mul_comm (Complex.exp _) (ℓ g : ℂ)] using h

/-- The actual Tamagawa Mellin integral is holomorphic on the open half-strip
for every order-zero Sobolev vector. -/
theorem analyticOnNhd_orderZeroMellinIntegral (x : W) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∫ g : C𝔽, x g * Complex.exp (z * ℓ g) ∂μ𝔽)
      {z : ℂ | |z.re| < 1 / 2} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt Complex.continuous_re.abs continuous_const)
  exact fun z hz ↦ (hasDerivAt_orderZeroMellinIntegral x hz).differentiableAt.differentiableWithinAt

end RiemannMasullo
