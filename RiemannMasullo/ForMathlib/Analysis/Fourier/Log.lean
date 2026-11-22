module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Probability.Distributions.Cauchy
import all RiemannMasullo.ForMathlib.Analysis.Fourier.AbelLimit

/-!
# Fourier transform of the logarithm on the real line

Represent the logarithm as an integral of differences of Cauchy kernels.
Fourier inversion gives the spatial kernel `1 / (2 |x|)` on tests vanishing at zero.
Subtract the two-sided exponential `exp (-2π |x|)` to evaluate the contribution
of the test value at zero.

Adapted from Neal Patel's `thatnealpatel/grh` at `e55aab2` under the MIT license.
See `RiemannMasullo/External/ATTRIBUTION.md`.
-/

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology

namespace RiemannMasullo

/-- The scale-`a` Cauchy kernel without the factor `1 / π`. -/
private noncomputable def cauchy (a x : ℝ) : ℝ := a / (a ^ 2 + x ^ 2)

private theorem cauchy_sub_integrals {x : ℝ} (hx : x ≠ 0) :
    IntegrableOn (fun a ↦ cauchy a x - cauchy a 1) (Ioi 0) ∧
      (∫ a in Ioi 0, cauchy a x - cauchy a 1) = -Real.log |x| ∧
      (∫ a in Ioi 0, |cauchy a x - cauchy a 1|) = abs (Real.log |x|) := by
  let G (a : ℝ) := Real.log ((a ^ 2 + x ^ 2) / (a ^ 2 + 1)) / 2
  have hderiv (a : ℝ) : HasDerivAt G (cauchy a x - cauchy a 1) a := by
    have ha : 0 < a ^ 2 + (1 : ℝ) := by positivity
    have hb : 0 < a ^ 2 + x ^ 2 := by positivity
    have hd (y : ℝ) : HasDerivAt (fun b : ℝ ↦ b ^ 2 + y) (2 * a) a := by
      simpa using ((hasDerivAt_id a).pow 2).add_const y
    convert (((hd _).div (hd _) ha.ne').log (div_ne_zero hb.ne' ha.ne')).div_const 2 using 1
    simp only [cauchy, one_pow, Pi.div_apply]
    field_simp
  have hlim : Tendsto G atTop (𝓝 0) := by
    have htop : Tendsto (fun a : ℝ ↦ a ^ 2 + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_pow_atTop (by decide : 2 ≠ 0))
    have hratio : Tendsto (fun a : ℝ ↦ 1 + (x ^ 2 - 1) * (a ^ 2 + 1)⁻¹) atTop (𝓝 1) := by
      simpa using (htop.inv_tendsto_atTop.const_mul (x ^ 2 - 1)).const_add 1
    have hratio' : Tendsto (fun a : ℝ ↦ (a ^ 2 + x ^ 2) / (a ^ 2 + 1)) atTop (𝓝 1) := by
      convert hratio using 1
      ext a
      have : 0 < a ^ 2 + (1 : ℝ) := by positivity
      field_simp
      ring
    simpa using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio'
      |>.div_const 2
  have hG : G 0 = Real.log |x| := by
    simp [G, Real.log_pow, Real.log_abs]
  rcases le_total (x ^ 2) (1 : ℝ) with h | h
  · have hp (a : ℝ) (ha : a ∈ Ioi (0 : ℝ)) : 0 ≤ cauchy a x - cauchy a 1 := by
      simp only [cauchy, one_pow, sub_nonneg]
      exact div_le_div_of_nonneg_left ha.out.le (by positivity) (by linarith)
    have hi := integral_Ioi_of_hasDerivAt_of_nonneg' (fun a _ ↦ hderiv a) hp hlim
    rw [hG, zero_sub] at hi
    refine ⟨integrableOn_Ioi_deriv_of_nonneg' (fun a _ ↦ hderiv a) hp hlim, hi, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi (fun a ha ↦ abs_of_nonneg (hp a ha)), hi]
    have : |x| ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
    exact (abs_of_nonpos (Real.log_nonpos (abs_nonneg x) this)).symm
  · have hp (a : ℝ) (ha : a ∈ Ioi (0 : ℝ)) : cauchy a x - cauchy a 1 ≤ 0 := by
      simp only [cauchy, one_pow, sub_nonpos]
      exact div_le_div_of_nonneg_left ha.out.le (by positivity) (by linarith)
    have hi := integral_Ioi_of_hasDerivAt_of_nonpos' (fun a _ ↦ hderiv a) hp hlim
    rw [hG, zero_sub] at hi
    refine ⟨integrableOn_Ioi_deriv_of_nonpos' (fun a _ ↦ hderiv a) hp hlim, hi, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi (fun a ha ↦ abs_of_nonpos (hp a ha)), integral_neg,
      hi, neg_neg]
    have : 1 ≤ |x| := by nlinarith [sq_abs x, abs_nonneg x]
    exact (abs_of_nonneg (Real.log_nonneg this)).symm

private theorem integrable_log_mul_schwartz (v : 𝓢(ℝ, ℂ)) :
    Integrable (fun x ↦ (Real.log |x| : ℂ) * v x) := by
  have hm : Measurable (fun x ↦ (Real.log |x| : ℂ) * v x) := by fun_prop
  let S := Ioc (-1 : ℝ) 1
  have hlocal : IntegrableOn (fun x : ℝ ↦ Real.log x) S :=
    intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num) |>.mp
      intervalIntegral.intervalIntegrable_log'
  obtain ⟨B, _, hB⟩ := v.decay 0 0
  have hv (x : ℝ) : ‖v x‖ ≤ B := by simpa using hB x
  have h₁ : IntegrableOn (fun x ↦ (Real.log |x| : ℂ) * v x) S := by
    apply (hlocal.norm.mul_const B).mono' hm.aestronglyMeasurable
    filter_upwards with x
    simp only [norm_mul, Complex.norm_real, Real.log_abs, Real.norm_eq_abs]
    gcongr
    exact hv x
  have htail : Integrable (fun x : ℝ ↦ ‖x‖ * ‖v x‖) := by
    simpa using v.integrable_pow_mul volume 1
  have h₂ : IntegrableOn (fun x ↦ (Real.log |x| : ℂ) * v x) Sᶜ := by
    apply (htail.integrableOn (s := Sᶜ)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.compl : MeasurableSet Sᶜ)] with x hx
    have hx' : 1 ≤ |x| := by
      by_contra! h
      exact hx ⟨(abs_lt.mp h).1, (abs_lt.mp h).2.le⟩
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hx')]
    gcongr
    exact Real.log_le_self (abs_nonneg x)
  simpa using (integrableOn_union.mpr ⟨h₁, h₂⟩)

/-- The logarithm is absolutely integrable against a Schwartz function. -/
private theorem log_fourier_integrable (v : 𝓢(ℝ, ℂ)) :
    Integrable (fun x ↦ (Real.log |x| : ℂ) * 𝓕 (v : ℝ → ℂ) x) := by
  simpa only [SchwartzMap.fourier_coe] using integrable_log_mul_schwartz (𝓕 v)

/-- Use a subtracted Cauchy kernel to represent the negative logarithm.
The exchange of integrations is absolute, even before imposing a zero moment. -/
private theorem log_pairing_eq_cauchy {v : ℝ → ℂ} (hv : Continuous v)
    (hlog : Integrable (fun x ↦ (Real.log |x| : ℂ) * v x)) :
    -(∫ x, (Real.log |x| : ℂ) * v x) =
      ∫ a in Ioi (0 : ℝ), ∫ x, ((cauchy a x - cauchy a 1 : ℝ) : ℂ) * v x := by
  let F (x a : ℝ) := ((cauchy a x - cauchy a 1 : ℝ) : ℂ) * v x
  have hF : Measurable (Function.uncurry F) := by unfold F cauchy Function.uncurry; fun_prop
  have hi : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff hF.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
      exact ((cauchy_sub_integrals hx).1.ofReal).mul_const (v x)
    · apply hlog.norm.congr
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
      simp only [Function.uncurry_apply_pair, F, norm_mul, Complex.norm_real, Real.norm_eq_abs, integral_mul_const,
        (cauchy_sub_integrals hx).2.2]
  rw [← integral_integral_swap hi, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
  have hcast : (∫ a in Ioi (0 : ℝ), ((cauchy a x - cauchy a 1 : ℝ) : ℂ)) =
      ((∫ a in Ioi (0 : ℝ), cauchy a x - cauchy a 1 : ℝ) : ℂ) := integral_ofReal
  simp only [F, integral_mul_const, hcast, (cauchy_sub_integrals hx).2.1,
    Complex.ofReal_neg, neg_mul]

/-- Spatial profile at a positive scale for the standard `2π` convention. -/
private noncomputable def laplaceProfile (a z : ℝ) : ℂ :=
  (Real.exp (-(2 * Real.pi * a) * |z|) : ℂ)

private theorem laplaceProfile_eq_abelTest (a : ℝ) : laplaceProfile a = halfPlaneAbelTest a 0 := by
  funext x
  simp [laplaceProfile, halfPlaneAbelTest, Complex.ofReal_exp, neg_mul]

private theorem laplaceProfile_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (laplaceProfile a) := by
  rw [laplaceProfile_eq_abelTest]
  exact (halfPlaneAbelTest_mem ha 0).1

private theorem fourier_laplaceProfile {a : ℝ} (ha : 0 < a) (x : ℝ) :
    𝓕 (laplaceProfile a) x = (cauchy a x : ℂ) / Real.pi := by
  rw [laplaceProfile_eq_abelTest, fourier_halfPlaneAbelTest ha,
    ProbabilityTheory.cauchyPDFReal_def 0 (⟨a, ha.le⟩ : NNReal) x]
  change ((Real.pi⁻¹ * a * ((x - 0) ^ 2 + a ^ 2)⁻¹ : ℝ) : ℂ) = _
  rw [← Complex.ofReal_div, sub_zero, add_comm (x ^ 2)]
  simp only [cauchy, div_eq_mul_inv]
  congr 1
  ring

/-- Bilinear Fourier exchange turns the Cauchy kernel on the frequency line
into the spatial Laplace profile, with no frequency reflection. -/
private theorem cauchy_pairing_eq_laplace {u : ℝ → ℂ} (hu : Continuous u)
    (hi : Integrable u) (huf : Integrable (𝓕 u)) {a : ℝ} (ha : 0 < a) :
    (∫ x, (cauchy a x : ℂ) * 𝓕 u x) =
      (Real.pi : ℂ) * ∫ z, laplaceProfile a z * u z := by
  have he := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner (laplaceProfile_integrable ha) huf
  have hinv (z : ℝ) : 𝓕 (𝓕 u) z = u (-z) := by
    simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using
      congrFun (hu.fourierInv_fourier_eq hi huf) (-z)
  have he' : (∫ x, 𝓕 (laplaceProfile a) x * 𝓕 u x) =
      ∫ z, laplaceProfile a z * u (-z) := by
    rw [flip_innerₗ] at he
    change (∫ x, 𝓕 (laplaceProfile a) x • 𝓕 u x) =
      (∫ z, laplaceProfile a z • 𝓕 (𝓕 u) z) at he
    simpa only [smul_eq_mul, hinv] using he
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← integral_neg_eq_self (fun z ↦ laplaceProfile a z * u z) volume]
  simp only [show ∀ z, laplaceProfile a (-z) = laplaceProfile a z from
    fun z ↦ by simp [laplaceProfile]]
  rw [← he', ← integral_const_mul]
  congr 1
  funext x
  rw [fourier_laplaceProfile ha]
  field_simp

/-- Fourier inversion at zero removes the constant subtraction at each
positive scale. The two summands are not integrated separately in scale. -/
private theorem cauchy_sub_pairing_eq_laplace {u : ℝ → ℂ} (hu : Continuous u)
    (hi : Integrable u) (huf : Integrable (𝓕 u)) (hzero : u 0 = 0)
    {a : ℝ} (ha : 0 < a) :
    (∫ x, ((cauchy a x - cauchy a 1 : ℝ) : ℂ) * 𝓕 u x) =
      (Real.pi : ℂ) * ∫ z, laplaceProfile a z * u z := by
  have hinv := congrFun (hu.fourierInv_fourier_eq hi huf) 0
  rw [Real.fourierInv_eq', hzero] at hinv
  have hmass : (∫ x, 𝓕 u x) = 0 := by simpa using hinv
  have hkc : Integrable (fun x ↦ (cauchy a x : ℂ) * 𝓕 u x) := by
    apply (huf.norm.const_mul a⁻¹).mono'
    · have h : Continuous fun x ↦ (cauchy a x : ℂ) := by
        apply Complex.continuous_ofReal.comp
        exact continuous_const.div (by fun_prop) (fun x ↦ (by positivity : 0 < a ^ 2 + x ^ 2).ne')
      exact h.aestronglyMeasurable.mul huf.aestronglyMeasurable
    · filter_upwards with x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by unfold cauchy; positivity)]
      gcongr
      unfold cauchy
      rw [div_le_iff₀ (by positivity)]
      calc
        a = a⁻¹ * a ^ 2 := by field_simp
        _ ≤ a⁻¹ * (a ^ 2 + x ^ 2) := by gcongr; exact le_add_of_nonneg_right (sq_nonneg x)
  simp only [Complex.ofReal_sub, sub_mul]
  rw [integral_sub hkc (huf.const_mul _), integral_const_mul, hmass, mul_zero, sub_zero,
    cauchy_pairing_eq_laplace hu hi huf ha]

/-- A linear bound near zero suffices for division by `|z|`; away from
zero absolute integrability of the original test suffices. -/
private theorem integrable_div_abs_of_local_bound {u : ℝ → ℂ} (hu : Continuous u)
    (hi : Integrable u) {ε C : ℝ} (hε : 0 < ε) (hbound : ∀ z, |z| < ε → ‖u z‖ ≤ C * |z|) :
    Integrable (fun z ↦ u z / ((|z| : ℝ) : ℂ)) := by
  let S := Ioo (-ε) ε
  have hm : Measurable (fun z ↦ u z / ((|z| : ℝ) : ℂ)) := hu.measurable.div (by fun_prop)
  have hlocal : IntegrableOn (fun z ↦ u z / ((|z| : ℝ) : ℂ)) S := by
    have hC : IntegrableOn (fun _ : ℝ ↦ max C 0) S :=
      integrableOn_const (by unfold S; exact measure_Ioo_lt_top.ne)
    apply hC.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_Ioo : MeasurableSet S)] with z hz
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_abs]
    by_cases hzero : z = 0
    · simp [hzero]
    · exact (div_le_iff₀ (abs_pos.mpr hzero)).2
        ((hbound z (abs_lt.mpr hz)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)))
  have htail : IntegrableOn (fun z ↦ u z / ((|z| : ℝ) : ℂ)) Sᶜ := by
    apply ((hi.norm.div_const ε).integrableOn (s := Sᶜ)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.compl : MeasurableSet Sᶜ)] with z hz
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_abs]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hε (le_of_not_gt (fun h ↦ hz (abs_lt.mp h)))
  simpa using integrableOn_union.mpr ⟨hlocal, htail⟩

private theorem laplace_scale_integral {z : ℝ} (hz : z ≠ 0) :
    let f (a : ℝ) := Real.exp (-(2 * Real.pi * a) * |z|)
    IntegrableOn f (Ioi 0) ∧ (∫ a in Ioi 0, f a) = (2 * Real.pi * |z|)⁻¹ := by
  have h : -(2 * Real.pi * |z|) < 0 := neg_neg_of_pos (by positivity)
  have he (a : ℝ) : -(2 * Real.pi * a) * |z| = -(2 * Real.pi * |z|) * a := by ring
  simp only [he]
  refine ⟨integrableOn_exp_mul_Ioi h 0, ?_⟩
  rw [integral_exp_mul_Ioi h]
  simp

/-- The positive-scale spatial integral has kernel `1 / (2 |z|)` off zero.
Its Fubini exchange needs only absolute integrability against `1 / |z|`. -/
private theorem laplace_integral_eq_half {u : ℝ → ℂ} (hu : Continuous u)
    (hi : Integrable (fun z ↦ u z / ((|z| : ℝ) : ℂ))) :
    (∫ a in Ioi (0 : ℝ), (Real.pi : ℂ) * ∫ z, laplaceProfile a z * u z) =
      (1 / 2 : ℂ) * ∫ z, u z / ((|z| : ℝ) : ℂ) := by
  let F (z a : ℝ) := (Real.pi : ℂ) * laplaceProfile a z * u z
  have hmeas : Measurable (Function.uncurry F) := by
    unfold F laplaceProfile Function.uncurry
    fun_prop
  have hFi : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz
      exact (((laplace_scale_integral hz).1.ofReal).const_mul (Real.pi : ℂ)).mul_const (u z)
    · apply (hi.norm.const_mul (1 / 2 : ℝ)).congr
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz
      simp only [Function.uncurry_apply_pair, F, laplaceProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, abs_of_pos (Real.exp_pos _), integral_mul_const,
        integral_const_mul, (laplace_scale_integral hz).2, norm_div, abs_abs]
      have : |z| ≠ 0 := abs_ne_zero.mpr hz
      field_simp [Real.pi_ne_zero]
  simp_rw [← integral_const_mul, ← mul_assoc]
  change (∫ a in Ioi (0 : ℝ), ∫ z, F z a) = ∫ z, (1 / 2 : ℂ) * (u z / ((|z| : ℝ) : ℂ))
  rw [← integral_integral_swap hFi]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz
  have hcast : (∫ a in Ioi (0 : ℝ), (Real.exp (-(2 * Real.pi * a) * |z|) : ℂ)) =
      ((∫ a in Ioi (0 : ℝ), Real.exp (-(2 * Real.pi * a) * |z|) : ℝ) : ℂ) := integral_ofReal
  simp only [F, laplaceProfile, integral_mul_const, integral_const_mul, hcast,
    (laplace_scale_integral hz).2, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hz' := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hz)
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- The ordinary density after subtracting the value at zero inside the unit ball. -/
private noncomputable def unitSubtraction (u : ℝ → ℂ) (z : ℝ) : ℂ :=
  (u z - (if |z| ≤ 1 then u 0 else 0)) / ((|z| : ℝ) : ℂ)

private theorem integrable_comp_abs' {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 0)) : Integrable (fun x ↦ f |x|) := by
  have hp : IntegrableOn (fun x ↦ f |x|) (Ioi 0) :=
    hf.congr_fun (fun x hx ↦ by rw [abs_of_pos hx]) measurableSet_Ioi
  have hn : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ ↦ -x) :=
      (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hp
  simpa using hp.union hn

private theorem abs_log_cauchy :
    Integrable (fun x : ℝ ↦ Real.log |x| / (1 + x ^ 2)) ∧
      (∫ x : ℝ, Real.log |x| / (1 + x ^ 2)) = 0 := by
  let f (x : ℝ) := Real.log x / (1 + x ^ 2)
  -- In log coordinates inversion of the positive frequency becomes reflection.
  let g (s : ℝ) := s / (Real.exp s + Real.exp (-s))
  have hchange (s : ℝ) : Real.exp s • f (Real.exp s) = g s := by
    have h : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    dsimp [f, g]
    rw [Real.log_exp]
    field_simp
    calc
      _ = s * (Real.exp s ^ 2 + Real.exp s * Real.exp (-s)) := by ring
      _ = _ := by rw [h]; ring
  have hmajor : Integrable (fun s : ℝ ↦ |s| * Real.exp (-|s|)) := by
    apply integrable_comp_abs' (f := fun s ↦ s * Real.exp (-s))
    simpa only [Real.rpow_one, neg_one_mul] using
      (integrableOn_rpow_mul_exp_neg_rpow (p := 1) (s := 1) (by norm_num) one_pos)
  have hg : Integrable g := by
    have hm : Measurable g := by unfold g; fun_prop
    refine hmajor.mono' hm.aestronglyMeasurable (.of_forall fun s ↦ ?_)
    rw [Real.norm_eq_abs]
    dsimp [g]
    rw [abs_div, abs_of_pos (by positivity : 0 < Real.exp s + Real.exp (-s))]
    have h : Real.exp |s| ≤ Real.exp s + Real.exp (-s) := by
      rcases le_total 0 s with hs | hs
      · rw [abs_of_nonneg hs]; linarith [Real.exp_pos (-s)]
      · rw [abs_of_nonpos hs]; linarith [Real.exp_pos s]
    rw [Real.exp_neg |s|, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (Real.exp_pos _) h
  have hfold (x : ℝ) : f |x| = Real.log |x| / (1 + x ^ 2) := by simp [f, sq_abs]
  refine ⟨by simpa only [hfold] using
    integrable_comp_abs' ((integrable_comp_exp f).mp (by simpa only [hchange] using hg)), ?_⟩
  simp_rw [← hfold]
  rw [integral_comp_abs, ← integral_comp_exp f]
  simp_rw [hchange]
  have hodd (s : ℝ) : g (-s) = -(g s) := by simp [g, add_comm, neg_div]
  have hz : (∫ s, g s) = 0 := by
    have h := integral_neg_eq_self g (μ := (volume : Measure ℝ))
    simp_rw [hodd, integral_neg] at h
    linarith
  rw [hz, mul_zero]

/-- The scale-one exponential has an absolutely convergent, zero logarithmic Fourier moment. -/
private theorem laplace_log_fourier_contact :
    Integrable (𝓕 (laplaceProfile 1)) ∧
      Integrable (fun ξ ↦ (Real.log |ξ| : ℂ) * 𝓕 (laplaceProfile 1) ξ) ∧
      (∫ ξ, (Real.log |ξ| : ℂ) * 𝓕 (laplaceProfile 1) ξ) = 0 := by
  have ht (x : ℝ) : 𝓕 (laplaceProfile 1) x = ((1 + x ^ 2)⁻¹ : ℝ) / (Real.pi : ℂ) := by
    rw [fourier_laplaceProfile one_pos]
    simp [cauchy]
  rw [show 𝓕 (laplaceProfile 1) = _ from funext ht]
  have h (x : ℝ) : (Real.log |x| : ℂ) * (((1 + x ^ 2)⁻¹ : ℝ) : ℂ) / Real.pi =
      ((Real.log |x| / (1 + x ^ 2) : ℝ) : ℂ) / Real.pi := by
    push_cast
    rw [div_eq_mul_inv (Real.log |x| : ℂ)]
  simp_rw [← mul_div_assoc, h]
  refine ⟨(integrable_inv_one_add_sq.ofReal).div_const _, abs_log_cauchy.1.ofReal.div_const _, ?_⟩
  have hc : (∫ x : ℝ, ((Real.log |x| / (1 + x ^ 2) : ℝ) : ℂ)) =
      ((∫ x : ℝ, Real.log |x| / (1 + x ^ 2) : ℝ) : ℂ) := integral_ofReal
  rw [integral_div, hc, abs_log_cauchy.2, Complex.ofReal_zero, zero_div]

private theorem log_exp_weight (b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun t ↦ b * Real.exp (-b * t) * Real.log t) (Ioi 0) ∧
    (∫ t in Ioi 0, b * Real.exp (-b * t) * Real.log t) =
      -Real.log b - Real.eulerMascheroniConstant := by
  have hunit : IntegrableOn (fun t ↦ Real.exp (-t) * Real.log t) (Ioi 0) := by
    have hlocal : IntegrableOn Real.log (Ioc (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        intervalIntegral.intervalIntegrable_log'
    have h₁ : IntegrableOn (fun t ↦ Real.exp (-t) * Real.log t) (Ioc (0 : ℝ) 1) := by
      refine hlocal.norm.mono' (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by linarith [ht.1]))
    have htail : IntegrableOn (fun t : ℝ ↦ t * Real.exp (-t)) (Ioi 1) := by
      apply IntegrableOn.mono_set _ (Ioi_subset_Ioi zero_le_one)
      simpa only [Real.rpow_one, neg_one_mul] using
        (integrableOn_rpow_mul_exp_neg_rpow (p := 1) (s := 1) (by norm_num) one_pos)
    have h₂ : IntegrableOn (fun t ↦ Real.exp (-t) * Real.log t) (Ioi 1) := by
      refine htail.mono' (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht' : 1 < t := ht
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.log_nonneg ht'.le))]
      rw [mul_comm t]
      exact mul_le_mul_of_nonneg_left (Real.log_le_self (by linarith)) (Real.exp_pos _).le
    simpa [Ioc_union_Ioi_eq_Ioi zero_le_one] using h₁.union h₂
  have hshift : IntegrableOn (fun s ↦ Real.exp (-s) * (Real.log s - Real.log b)) (Ioi 0) := by
    rw [show (fun s ↦ Real.exp (-s) * (Real.log s - Real.log b)) =
      (fun t ↦ Real.exp (-t) * Real.log t) - (fun s ↦ Real.exp (-s) * Real.log b) by
        ext s; exact mul_sub _ _ _]
    exact hunit.sub ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).mul_const (Real.log b) |>.congr (by simp))
  let g (s : ℝ) := Real.exp (-s) * (Real.log s - Real.log b)
  have hg (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : b * Real.exp (-b * t) * Real.log t = b * g (b * t) := by
    have ht' : 0 < t := ht
    simp only [g, Real.log_mul hb.ne' ht'.ne', add_sub_cancel_left, neg_mul, mul_assoc]
  have hcomp : IntegrableOn (fun t ↦ g (b * t)) (Ioi 0) := by
    have hgi : Integrable ((Ioi (0 : ℝ)).indicator g) :=
      (integrable_indicator_iff measurableSet_Ioi).2 hshift
    refine (hgi.comp_mul_left' hb.ne').integrableOn.congr_fun ?_ measurableSet_Ioi
    intro t ht
    exact indicator_of_mem (mem_Ioi.mpr (mul_pos hb ht)) _
  have hscaled : IntegrableOn (fun t ↦ b * g (b * t)) (Ioi 0) := hcomp.const_mul b
  refine ⟨hscaled.congr_fun (fun t ht ↦ (hg t ht).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hg, integral_const_mul]
  have hs := integral_comp_mul_left_Ioi' g 0 hb
  rw [mul_zero, smul_eq_mul] at hs
  rw [hs]
  change (∫ s in Ioi (0 : ℝ), Real.exp (-s) * (Real.log s - Real.log b)) = _
  simp_rw [mul_sub]
  have he : IntegrableOn (fun s : ℝ ↦ Real.exp (-s)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  have heq : (∫ s in Ioi (0 : ℝ), Real.exp (-s)) = 1 := by
    simpa using integral_exp_mul_Ioi (a := -1) (by norm_num) 0
  rw [integral_sub hunit (he.mul_const _), integral_mul_const, heq, one_mul]
  have hγ := Real.eulerMascheroniConstant_eq_neg_integral_log
  simp_rw [mul_comm (Real.log _) (Real.exp _)] at hγ
  linarith

private theorem signed_tail_slice (a : ℝ) :
    let d (s : ℝ) := (if s ≤ a then (1 : ℝ) else 0) - if s ≤ 0 then 1 else 0
    Integrable d ∧ (∫ s, d s) = a ∧ (∫ s, ‖d s‖) = |a| := by
  dsimp
  rcases le_total 0 a with ha | ha
  · have he (s : ℝ) : (if s ≤ a then (1 : ℝ) else 0) - (if s ≤ 0 then 1 else 0) =
        (Ioc 0 a).indicator (fun _ ↦ 1) s := by
      by_cases hs : s ≤ 0
      · simp [hs, hs.trans ha, not_lt.mpr hs]
      · by_cases h : s ≤ a <;> simp [hs, h, lt_of_not_ge hs]
    have hi : Integrable ((Ioc 0 a).indicator (fun _ ↦ (1 : ℝ))) :=
      (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const measure_Ioc_lt_top.ne)
    simp_rw [he]
    refine ⟨hi, ?_, ?_⟩
    · simp [integral_indicator measurableSet_Ioc, ha]
    · have hp (s : ℝ) : 0 ≤ (Ioc 0 a).indicator (fun _ ↦ (1 : ℝ)) s := by
        by_cases hs : s ∈ Ioc 0 a <;> simp [hs]
      simp [abs_of_nonneg (hp _), integral_indicator measurableSet_Ioc, ha, abs_of_nonneg ha]
  · have he (s : ℝ) : (if s ≤ a then (1 : ℝ) else 0) - (if s ≤ 0 then 1 else 0) =
        -((Ioc a 0).indicator (fun _ ↦ 1) s) := by
      by_cases hs : s ≤ a
      · simp [hs, hs.trans ha, not_lt.mpr hs]
      · by_cases hs' : s ≤ 0 <;> simp [hs, hs', lt_of_not_ge hs]
    have hi : Integrable ((Ioc a 0).indicator (fun _ ↦ (1 : ℝ))) :=
      (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const measure_Ioc_lt_top.ne)
    simp_rw [he]
    refine ⟨hi.neg, ?_, ?_⟩
    · simp [integral_neg, integral_indicator measurableSet_Ioc, ha]
    · have hp (s : ℝ) : 0 ≤ (Ioc a 0).indicator (fun _ ↦ (1 : ℝ)) s := by
        by_cases hs : s ∈ Ioc a 0 <;> simp [hs]
      simp [abs_of_nonneg (hp _), integral_indicator measurableSet_Ioc, ha, abs_of_nonpos ha]

private theorem exp_subtraction {b : ℝ} (hb : 0 < b) :
    let p (x : ℝ) := (Real.exp (-b * x) - (if x ≤ 1 then 1 else 0)) / x
    IntegrableOn p (Ioi 0) ∧ (∫ x in Ioi 0, p x) = -Real.log b - Real.eulerMascheroniConstant := by
  let W (t : ℝ) := b * Real.exp (-b * t)
  -- The difference of tails has signed length `log t` and absolute length `|log t|`.
  let D (t s : ℝ) := (if s ≤ Real.log t then (1 : ℝ) else 0) - (if s ≤ 0 then 1 else 0)
  let F (t s : ℝ) := W t * D t s
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  have hFi : Integrable (Function.uncurry F) (μ.prod volume) := by
    have hw : Measurable (fun p : ℝ × ℝ ↦ W p.1) := by unfold W; fun_prop
    have h₁ : Measurable (fun p : ℝ × ℝ ↦ if p.2 ≤ Real.log p.1 then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le measurable_snd (Real.measurable_log.comp measurable_fst))
        measurable_const measurable_const
    have h₂ : Measurable (fun p : ℝ × ℝ ↦ if p.2 ≤ 0 then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le measurable_snd measurable_const) measurable_const measurable_const
    have hm : Measurable (Function.uncurry F) := hw.mul (h₁.sub h₂)
    apply (integrable_prod_iff hm.aestronglyMeasurable).2
    refine ⟨.of_forall fun t ↦ (signed_tail_slice (Real.log t)).1.const_mul (W t), ?_⟩
    apply (log_exp_weight b hb).1.norm.congr
    filter_upwards with t
    have hs : (∫ s : ℝ, ‖D t s‖) = |Real.log t| := (signed_tail_slice _).2.2
    simp only [Function.uncurry_apply_pair, F, norm_mul, integral_const_mul, hs, Real.norm_eq_abs (Real.log t)]
    simp only [W, norm_mul]
  have htail (x : ℝ) (hx : 0 < x) : (∫ t in Ioi (0 : ℝ), W t * (if x ≤ t then 1 else 0)) =
      Real.exp (-b * x) := by
    calc
      _ = ∫ t in Ici x, W t := by
        have he (t : ℝ) : W t * (if x ≤ t then 1 else 0) = (Ici x).indicator W t := by
          by_cases ht : x ≤ t <;> simp [ht]
        simp_rw [he, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
          inter_eq_left.mpr (Ici_subset_Ioi.mpr hx)]
      _ = ∫ t in Ioi x, W t := integral_Ici_eq_integral_Ioi
      _ = _ := by
        unfold W
        rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hb)]
        field_simp
  have hslice (s : ℝ) : (∫ t, F t s ∂μ) = Real.exp (-b * Real.exp s) - (if s ≤ 0 then 1 else 0) := by
    have hW : Integrable W μ := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) 0).const_mul b
    have h₁ : Integrable (fun t ↦ W t * (if Real.exp s ≤ t then 1 else 0)) μ := by
      refine (hW.indicator (measurableSet_Ici (a := Real.exp s))).congr (.of_forall fun t ↦ ?_)
      by_cases ht : Real.exp s ≤ t <;> simp [ht]
    change (∫ t, W t * D t s ∂μ) = _
    simp only [D, mul_sub]
    rw [integral_sub]
    · rw [integral_mul_const, show (∫ t, W t ∂μ) = 1 by
        dsimp [μ, W]; rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hb)]; simp [hb.ne'], one_mul]
      congr 1
      rw [← htail _ (Real.exp_pos s)]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [Real.le_log_iff_exp_le (show 0 < t from ht)]
    · apply h₁.congr
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
      simp only [Real.le_log_iff_exp_le (show 0 < t from ht)]
    · exact hW.mul_const _
  let q (s : ℝ) := Real.exp (-b * Real.exp s) - (if s ≤ 0 then 1 else 0)
  have hq : Integrable q := by
    exact hFi.integral_prod_right.congr (.of_forall hslice)
  have hqeq : (∫ s, q s) = -Real.log b - Real.eulerMascheroniConstant := by
    simp_rw [q, ← hslice]
    rw [← integral_integral_swap (μ := μ) (ν := volume) (f := F) hFi]
    have hs (t : ℝ) : (∫ s : ℝ, D t s) = Real.log t := (signed_tail_slice _).2.1
    simpa only [F, W, integral_const_mul, hs] using (log_exp_weight b hb).2
  have he (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      x⁻¹ • q (Real.log x) = (Real.exp (-b * x) - (if x ≤ 1 then 1 else 0)) / x := by
    rw [smul_eq_mul, div_eq_inv_mul]
    simp [q, Real.exp_log (show 0 < x from hx), Real.log_nonpos_iff (show 0 < x from hx).le]
  exact ⟨((integrableOn_comp_log_Ioi_zero q).mpr hq).congr_fun he measurableSet_Ioi,
    (setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ (he x hx).symm)).trans
      ((integral_comp_log_Ioi_zero q).trans hqeq)⟩

/-- The scale-one exponential calibrates the unit-radius spatial subtraction. -/
private theorem laplace_unitSubtraction_contact :
    Integrable (unitSubtraction (laplaceProfile 1)) ∧
      (1 / 2 : ℂ) * (∫ z, unitSubtraction (laplaceProfile 1) z) =
        ((-Real.log (2 * Real.pi) - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
  have h := exp_subtraction (b := 2 * Real.pi) (by positivity)
  dsimp at h
  have he (z : ℝ) : unitSubtraction (laplaceProfile 1) z =
      (((Real.exp (-(2 * Real.pi) * |z|) - (if |z| ≤ 1 then 1 else 0)) / |z| : ℝ) : ℂ) := by
    simp only [unitSubtraction, laplaceProfile, mul_one, abs_zero, mul_zero, Real.exp_zero,
      Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_sub]
    split <;> simp_all
  rw [show unitSubtraction (laplaceProfile 1) = _ from funext he]
  refine ⟨(integrable_comp_abs' h.1).ofReal, ?_⟩
  let p (x : ℝ) := (Real.exp (-(2 * Real.pi) * x) - (if x ≤ 1 then 1 else 0)) / x
  change (1 / 2 : ℂ) * (∫ x : ℝ, ((p |x| : ℝ) : ℂ)) = _
  have hc : (∫ x : ℝ, ((p |x| : ℝ) : ℂ)) = ((∫ x : ℝ, p |x| : ℝ) : ℂ) := integral_ofReal
  rw [hc, integral_comp_abs]
  change (1 / 2 : ℂ) * ((2 * ∫ x in Ioi (0 : ℝ), p x : ℝ) : ℂ) = _
  rw [show (∫ x in Ioi (0 : ℝ), p x) = _ from h.2]
  push_cast
  ring

/-- Subtract the cusp comparator using only a first-order estimate at the origin. -/
private theorem remainder_div_integrable {u : ℝ → ℂ} (hc : Continuous u)
    (hd : DifferentiableAt ℝ u 0) (hu : Integrable u) :
    Integrable (fun z ↦ (u z - u 0 * laplaceProfile 1 z) / ((|z| : ℝ) : ℂ)) := by
  have hG : Continuous (laplaceProfile 1) := by unfold laplaceProfile; fun_prop
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hd.hasDerivAt.isBigO_sub
  obtain ⟨ε, hε, hεC⟩ := Metric.eventually_nhds_iff.mp hC
  apply integrable_div_abs_of_local_bound (hc.sub (hG.const_mul _))
    (hu.sub ((laplaceProfile_integrable one_pos).const_mul _)) hε (C := C + ‖u 0‖ * (2 * Real.pi))
  intro z hz
  have hz' : ‖u z - u 0‖ ≤ C * |z| := by
    simpa [Real.dist_eq] using hεC (y := z) (by simpa [Real.dist_eq] using hz)
  have hGz : ‖(1 : ℂ) - laplaceProfile 1 z‖ ≤ (2 * Real.pi) * |z| := by
    have h : 0 ≤ (2 * Real.pi) * |z| := by positivity
    rw [laplaceProfile, mul_one, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))]
    linarith [Real.add_one_le_exp (-(2 * Real.pi) * |z|)]
  change ‖u z - u 0 * laplaceProfile 1 z‖ ≤ _
  rw [show u z - u 0 * laplaceProfile 1 z = (u z - u 0) + u 0 * (1 - laplaceProfile 1 z) by ring]
  calc
    _ ≤ ‖u z - u 0‖ + ‖u 0 * (1 - laplaceProfile 1 z)‖ := norm_add_le _ _
    _ ≤ C * |z| + ‖u 0‖ * ((2 * Real.pi) * |z|) := by
      rw [norm_mul]
      exact add_le_add hz' (mul_le_mul_of_nonneg_left hGz (norm_nonneg _))
    _ = _ := by ring

/-- Fourier linearity for the continuous, integrable remainder and the comparator. -/
private theorem fourier_remainder_add {u r : ℝ → ℂ} (hr : Integrable r)
    (he : ∀ z, u z = r z + u 0 * laplaceProfile 1 z) (ξ : ℝ) :
    𝓕 u ξ = 𝓕 r ξ + u 0 * 𝓕 (laplaceProfile 1) ξ := by
  let c : ℂ := u 0
  have ha : 𝓕 (r + c • laplaceProfile 1) = 𝓕 r + 𝓕 (c • laplaceProfile 1) :=
    VectorFourier.fourierIntegral_add Real.continuous_fourierChar (innerSL ℝ).continuous₂
      hr ((laplaceProfile_integrable one_pos).const_mul c)
  have hs : 𝓕 (c • laplaceProfile 1) = c • 𝓕 (laplaceProfile 1) :=
    VectorFourier.fourierIntegral_const_smul Real.fourierChar volume (innerₗ ℝ) (laplaceProfile 1) c
  have he' : u = r + c • laplaceProfile 1 := funext he
  have he'' := congrArg (fun v : ℝ → ℂ ↦ 𝓕 v) he'
  rw [ha, hs] at he''
  exact congrFun he'' ξ

/-- Spatial subtraction separates into the zero-value remainder and the calibrated comparator. -/
private theorem unitSubtraction_eq_remainder (u : ℝ → ℂ) (z : ℝ) :
    unitSubtraction u z = (u z - u 0 * laplaceProfile 1 z) / ((|z| : ℝ) : ℂ) +
      u 0 * unitSubtraction (laplaceProfile 1) z := by
  have hG0 : laplaceProfile 1 0 = 1 := by simp [laplaceProfile]
  simp only [unitSubtraction, hG0, ← mul_div_assoc, ← add_div]
  congr 1
  split <;> ring

/-- A positive deleted radius bounds the reciprocal kernel by `1 / ε`. -/
private theorem integrableOn_div_abs_cutoff {u : ℝ → ℂ} (hu : Integrable u)
    {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun z ↦ u z / ((|z| : ℝ) : ℂ)) {z | ε ≤ |z|} := by
  have hm : MeasurableSet {z : ℝ | ε ≤ |z|} := measurableSet_le measurable_const continuous_abs.measurable
  have hf := hu.aestronglyMeasurable.mono_measure (Measure.restrict_le_self (s := {z | ε ≤ |z|}))
  refine (hu.norm.div_const ε).integrableOn.mono' (hf.div₀ (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem hm] with z hz
  have hz' : ε ≤ |z| := hz
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_abs]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hε hz'

private theorem annulus_integral_inv_abs {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    (∫ z in {z : ℝ | ε ≤ |z|}, if |z| ≤ 1 then |z|⁻¹ else 0) = -2 * Real.log ε := by
  have hm : MeasurableSet {z : ℝ | ε ≤ |z|} := measurableSet_le measurable_const continuous_abs.measurable
  let g := (Icc ε 1).indicator (fun x : ℝ ↦ x⁻¹)
  have hg (x : ℝ) : g |x| =
      ({z : ℝ | ε ≤ |z|}).indicator (fun z ↦ if |z| ≤ 1 then |z|⁻¹ else 0) x := by
    by_cases h₁ : ε ≤ |x| <;> by_cases h₂ : |x| ≤ 1 <;>
      simp [g, indicator, h₁, h₂]
  rw [← integral_indicator hm, ← (funext hg), integral_comp_abs]
  have hsub : Icc ε 1 ⊆ Ioi 0 := fun x hx ↦ hε.trans_le hx.1
  rw [show g = _ from rfl, setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr hsub,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hε₁,
    integral_inv_of_pos hε one_pos, one_div, Real.log_inv]
  ring

/-- On a finite-radius cutoff the unit subtraction is precisely the logarithmic correction. -/
private theorem cutoff_eq_unitSubtraction {u : ℝ → ℂ} (hu : Integrable u)
    (hs : Integrable (unitSubtraction u)) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    (1 / 2 : ℂ) * (∫ z in {z | ε ≤ |z|}, u z / ((|z| : ℝ) : ℂ)) +
      (Real.log ε : ℂ) * u 0 =
      (1 / 2 : ℂ) * ∫ z in {z | ε ≤ |z|}, unitSubtraction u z := by
  let A : Set ℝ := {z | ε ≤ |z|}
  let k (z : ℝ) : ℝ := if |z| ≤ 1 then |z|⁻¹ else 0
  have he (z : ℝ) : u z / ((|z| : ℝ) : ℂ) - unitSubtraction u z = u 0 * (k z : ℂ) := by
    by_cases hz : |z| ≤ 1 <;> simp [unitSubtraction, k, hz, div_eq_mul_inv, sub_mul]
  have hf : IntegrableOn (fun z ↦ u z / ((|z| : ℝ) : ℂ)) A := integrableOn_div_abs_cutoff hu hε
  have hdiff : (∫ z in A, u z / ((|z| : ℝ) : ℂ)) - (∫ z in A, unitSubtraction u z) =
      u 0 * ((-2 * Real.log ε : ℝ) : ℂ) := by
    rw [← integral_sub hf hs.integrableOn, show _ = _ from funext he, integral_const_mul,
      integral_complex_ofReal, annulus_integral_inv_abs hε hε₁]
  push_cast at hdiff
  change (1 / 2 : ℂ) * (∫ z in A, u z / ((|z| : ℝ) : ℂ)) + (Real.log ε : ℂ) * u 0 =
    (1 / 2 : ℂ) * ∫ z in A, unitSubtraction u z
  linear_combination hdiff / 2

/-- Deleting a neighborhood of shrinking radius does not change the limit of an
absolutely integrable spatial pairing. -/
private theorem tendsto_integral_abs_cutoff {v : ℝ → ℂ} (hv : Integrable v) :
    Tendsto (fun ε : ℝ ↦ ∫ z in {z | ε ≤ |z|}, v z) (𝓝[Ioi 0] 0) (𝓝 (∫ z, v z)) := by
  let A (ε : ℝ) : Set ℝ := {z | ε ≤ |z|}
  have hm (ε : ℝ) : MeasurableSet (A ε) := measurableSet_le measurable_const continuous_abs.measurable
  change Tendsto (fun ε ↦ ∫ z in A ε, v z) _ _
  simp_rw [← integral_indicator (hm _)]
  apply tendsto_integral_filter_of_dominated_convergence (fun z ↦ ‖v z‖)
  · exact .of_forall fun ε ↦ hv.aestronglyMeasurable.indicator (hm ε)
  · refine .of_forall fun ε ↦ .of_forall fun z ↦ ?_
    by_cases hz : z ∈ A ε <;> simp [hz]
  · exact hv.norm
  · have hne : ∀ᵐ z : ℝ ∂volume, z ∈ ({0} : Set ℝ)ᶜ :=
      ae_iff.mpr (by simp)
    filter_upwards [hne] with z hz
    have hz' : z ≠ 0 := by simpa using hz
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds (abs_pos.mpr hz'))] with ε hε
    exact indicator_of_mem hε.le _ |>.symm

/-- For a test vanishing at zero, the Fourier pairing reduces to ordinary
integration against the reciprocal kernel whenever both pairings converge absolutely. -/
private theorem real_log_fourier_of_zero {u : ℝ → ℂ} (hu : Continuous u)
    (hzero : u 0 = 0) (hi : Integrable u) (huf : Integrable (𝓕 u))
    (hlog : Integrable (fun ξ ↦ (Real.log |ξ| : ℂ) * 𝓕 u ξ))
    (hright : Integrable (fun z ↦ u z / ((|z| : ℝ) : ℂ))) :
    -(∫ ξ, (Real.log |ξ| : ℂ) * 𝓕 u ξ) = (1 / 2 : ℂ) * ∫ z, u z / ((|z| : ℝ) : ℂ) := by
  have hv : Continuous (𝓕 u) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi
  -- Represent the logarithm by a subtracted Cauchy kernel with absolute Fubini.
  calc
    _ = ∫ a in Ioi (0 : ℝ), ∫ ξ,
          ((cauchy a ξ - cauchy a 1 : ℝ) : ℂ) * 𝓕 u ξ :=
        log_pairing_eq_cauchy hv hlog
    -- Fourier inversion at zero cancels the constant in each scale slice.
    _ = ∫ a in Ioi (0 : ℝ), (Real.pi : ℂ) * ∫ z, laplaceProfile a z * u z :=
        setIntegral_congr_fun measurableSet_Ioi fun a ha ↦
          cauchy_sub_pairing_eq_laplace hu hi huf hzero ha
    -- In space, integrating the Laplace kernel in scale produces the half factor.
    _ = _ := laplace_integral_eq_half hu hright

/-- Subtracting the test value at zero inside the unit ball gives an absolutely
integrable density and a correction of `(log (2π) + γ) u(0)` for the negative logarithm. -/
private theorem real_log_fourier_unit_subtraction (u : 𝓢(ℝ, ℂ)) :
    Integrable (fun ξ ↦ (Real.log |ξ| : ℂ) * 𝓕 (u : ℝ → ℂ) ξ) ∧
      Integrable (unitSubtraction u) ∧
      -(∫ ξ, (Real.log |ξ| : ℂ) * 𝓕 (u : ℝ → ℂ) ξ) =
        (1 / 2 : ℂ) * (∫ z, unitSubtraction u z) +
          ((Real.log (2 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ) * u 0 := by
  let G := laplaceProfile 1
  let r (z : ℝ) := u z - u 0 * G z
  have hG : Integrable G := laplaceProfile_integrable one_pos
  have hGcont : Continuous G := by unfold G laplaceProfile; fun_prop
  have hrcont : Continuous r := u.continuous.sub (hGcont.const_mul _)
  have hr : Integrable r := u.integrable.sub (hG.const_mul _)
  have hrzero : r 0 = 0 := by simp [r, G, laplaceProfile]
  obtain ⟨hGfourier, hGlog, hGlog0⟩ := laplace_log_fourier_contact
  have huf : Integrable (𝓕 (u : ℝ → ℂ)) := (𝓕 u).integrable
  have hlog := log_fourier_integrable u
  have hf (ξ : ℝ) : 𝓕 r ξ = 𝓕 (u : ℝ → ℂ) ξ - u 0 * 𝓕 G ξ := by
    apply eq_sub_of_add_eq
    exact (fourier_remainder_add hr (fun z ↦ by dsimp [r]; ring) ξ).symm
  have hf' (ξ : ℝ) : (Real.log |ξ| : ℂ) * 𝓕 r ξ =
      (Real.log |ξ| : ℂ) * 𝓕 (u : ℝ → ℂ) ξ - u 0 * ((Real.log |ξ| : ℂ) * 𝓕 G ξ) := by
    rw [hf]; ring
  have hrlog := (hlog.sub (hGlog.const_mul (u 0))).congr (.of_forall fun x ↦ (hf' x).symm)
  have hrdiv := remainder_div_integrable u.continuous u.differentiable.differentiableAt
    u.integrable
  -- The zero-value theorem applies even though the comparator has a cusp.
  have hremain := real_log_fourier_of_zero hrcont hrzero hr
    ((huf.sub (hGfourier.const_mul (u 0))).congr (.of_forall fun x ↦ (hf x).symm)) hrlog hrdiv
  have hT : (∫ ξ, (Real.log |ξ| : ℂ) * 𝓕 r ξ) = ∫ ξ, (Real.log |ξ| : ℂ) * 𝓕 (u : ℝ → ℂ) ξ := by
    simp_rw [hf']
    rw [integral_sub hlog (hGlog.const_mul (u 0)), integral_const_mul, hGlog0, mul_zero, sub_zero]
  obtain ⟨hPG, hPGval⟩ := laplace_unitSubtraction_contact
  -- The scale-one exponential has zero logarithmic Fourier moment and spatial
  -- finite part `-log(2π)-γ`.
  have hp (z : ℝ) := unitSubtraction_eq_remainder (u : ℝ → ℂ) z
  refine ⟨hlog, (hrdiv.add (hPG.const_mul (u 0))).congr (.of_forall fun z ↦ (hp z).symm), ?_⟩
  rw [← hT, hremain]
  simp_rw [hp]
  rw [integral_add hrdiv (hPG.const_mul (u 0)), integral_const_mul]
  rw [mul_add, mul_left_comm (1 / 2 : ℂ), hPGval]
  push_cast
  ring

/-- The Fourier pairing with the real logarithm is the finite part of the
negative half-weighted reciprocal absolute value, with contact term
`-(log (2π) + γ) u(0)`. The Fourier integral and each cutoff integral converge absolutely. -/
public theorem real_log_fourier_cutoff (u : 𝓢(ℝ, ℂ)) :
    Integrable (fun ξ ↦ (Real.log |ξ| : ℂ) * 𝓕 (u : ℝ → ℂ) ξ) ∧
      (∀ ε : ℝ, 0 < ε → IntegrableOn (fun z ↦ u z / ((|z| : ℝ) : ℂ)) {z | ε ≤ |z|}) ∧
      Tendsto (fun ε : ℝ ↦ (1 / 2 : ℂ) * (∫ z in {z | ε ≤ |z|}, u z / ((|z| : ℝ) : ℂ)) +
        (Real.log ε : ℂ) * u 0) (𝓝[Ioi 0] 0)
        (𝓝 (-(∫ ξ, (Real.log |ξ| : ℂ) * 𝓕 (u : ℝ → ℂ) ξ) -
          ((Real.log (2 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ) * u 0)) := by
  obtain ⟨hlog, hsub, hvalue⟩ := real_log_fourier_unit_subtraction u
  refine ⟨hlog, fun ε hε ↦ integrableOn_div_abs_cutoff u.integrable hε, ?_⟩
  rw [hvalue, add_sub_cancel_right]
  -- The removed part of the absolute density tends to zero.
  refine ((tendsto_integral_abs_cutoff hsub).const_mul (1 / 2 : ℂ)).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds zero_lt_one)]
    with ε hε hε₁
  -- The inverse-radius integral on the annulus is `-2 log ε`.
  exact (cutoff_eq_unitSubtraction u.integrable hsub hε hε₁.le).symm

end RiemannMasullo
