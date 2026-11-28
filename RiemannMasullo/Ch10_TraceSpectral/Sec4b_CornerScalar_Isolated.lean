module

public import RiemannMasullo.Ch09_HardySobolev.Sec2
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The `max`-weight corner at positive width and the `Θ(α / T²)` lower bound on `#7406`

This file formalizes the positive-width (`α > 0`, `s > 1`) corner obstruction on `#7406`
(`Ch10_TraceSpectral/Sec4b_Isolated.lean`) and contrasts it with the smooth equivalent density
`2 * cosh (2 * α * x) * (1 + x ^ 2) ^ (s / 2)`:

1. Equivalence of `intervalSobolevDensity (-α) α s` and `coshSobolevDensity α s`
   (`intervalSobolevDensity_le_coshSobolevDensity`, `coshSobolevDensity_le_two_mul`).
2. Scalar corner asymptotic and lower bound: for `0 < α`, `1 < s`, `σ ∈ [-α, α]`, and `η ≠ 0`,
   `∫ x : ℝ, (exp (σ * x) / intervalSobolevDensity (-α) α s x) * exp (-I * η * x) = 4 * α / η ^ 2 + O(|η|⁻³)`,
   while the same transform with `coshSobolevDensity α s` decays faster than every power of `|η|`.
3. Adelic Hilbert-space corner asymptotic and `Θ(α / T²)` lower bound on `G_a (A(φ) r_z)` for the
   Riesz representer `r_z` of a strip jet at `z = (ω, σ, T)` (`|T| → ∞`).
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal Topology

namespace RiemannMasullo.Isolated

section Weights

/-- The smooth hyperbolic-cosine weight `2 * cosh (2 * α * x) * (1 + x ^ 2) ^ (s / 2)` replacing
`max (exp (-2 * α * x)) (exp (2 * α * x))` in `intervalSobolevDensity (-α) α s x`. -/
def coshSobolevDensity (α s x : ℝ) : ℝ :=
  2 * Real.cosh (2 * α * x) * (1 + x ^ 2) ^ (s / 2)

theorem coshSobolevDensity_pos (α s x : ℝ) : 0 < coshSobolevDensity α s x := by
  unfold coshSobolevDensity
  positivity [Real.cosh_pos (2 * α * x)]

theorem continuous_coshSobolevDensity (α s : ℝ) : Continuous (coshSobolevDensity α s) := by
  unfold coshSobolevDensity
  refine (continuous_const.mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).mul ?_
  exact (continuous_const.add (continuous_id.pow 2)).rpow_const fun x ↦
    Or.inl (by positivity : (1 : ℝ) + x ^ 2 ≠ 0)

theorem contDiff_coshSobolevDensity (α s : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (coshSobolevDensity α s) := by
  unfold coshSobolevDensity
  have hbase : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ ↦ (1 : ℝ) + x ^ 2) :=
    contDiff_const.add (contDiff_id.pow 2)
  have hrpow : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ ↦ (1 + x ^ 2) ^ (s / 2)) :=
    hbase.rpow_const_of_ne fun x ↦ by positivity
  have heq_cosh : (fun x : ℝ ↦ Real.cosh (2 * α * x)) =
      fun x ↦ (Real.exp (2 * α * x) + Real.exp (-(2 * α * x))) / 2 :=
    funext fun x ↦ Real.cosh_eq _
  have hcosh : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ ↦ Real.cosh (2 * α * x)) := by
    rw [heq_cosh]
    exact ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).add
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg)).div_const 2
  exact (contDiff_const.mul hcosh).mul hrpow

/-- The smooth `cosh` density dominates `intervalSobolevDensity (-α) α s` pointwise. -/
theorem intervalSobolevDensity_le_coshSobolevDensity {α : ℝ} (_hα : 0 ≤ α) (s x : ℝ) :
    intervalSobolevDensity (-α) α s x ≤ coshSobolevDensity α s x := by
  unfold intervalSobolevDensity coshSobolevDensity
  have hpoly : 0 ≤ (1 + x ^ 2) ^ (s / 2) := by positivity
  refine mul_le_mul_of_nonneg_right ?_ hpoly
  have hsum : 2 * Real.cosh (2 * α * x) = Real.exp (2 * α * x) + Real.exp (-(2 * α * x)) := by
    rw [Real.cosh_eq]
    ring
  rw [hsum]
  have he1 : 0 < Real.exp (2 * (-α) * x) := Real.exp_pos _
  have he2 : 0 < Real.exp (2 * α * x) := Real.exp_pos _
  have heq : 2 * (-α) * x = -(2 * α * x) := by ring
  rw [heq]
  exact max_le (le_add_of_nonneg_left he2.le) (le_add_of_nonneg_right (Real.exp_pos _).le)

/-- The smooth `cosh` density is bounded by twice `intervalSobolevDensity (-α) α s`. -/
theorem coshSobolevDensity_le_two_mul {α : ℝ} (_hα : 0 ≤ α) (s x : ℝ) :
    coshSobolevDensity α s x ≤ 2 * intervalSobolevDensity (-α) α s x := by
  unfold intervalSobolevDensity coshSobolevDensity
  have hpoly : 0 ≤ (1 + x ^ 2) ^ (s / 2) := by positivity
  rw [mul_assoc (2 : ℝ)]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hpoly) (by positivity)
  rw [Real.cosh_eq]
  have h1 : Real.exp (2 * α * x) ≤ max (Real.exp (2 * (-α) * x)) (Real.exp (2 * α * x)) :=
    le_max_right _ _
  have h2 : Real.exp (-(2 * α * x)) ≤ max (Real.exp (2 * (-α) * x)) (Real.exp (2 * α * x)) := by
    rw [show -(2 * α * x) = 2 * (-α) * x by ring]
    exact le_max_left _ _
  linarith

end Weights

section ScalarCornerIBP

/-- An integrable complex function on `Ioi 0` whose derivative is also integrable on `Ioi 0`
tends to `0` at `+∞`, and satisfies half-line integration by parts against `exp (-I * η * x)`. -/
theorem fourier_ibp_Ioi {f f' : ℝ → ℂ} {η : ℝ} (hη : η ≠ 0)
    (hcont : ContinuousWithinAt f (Ici 0) 0)
    (hderiv : ∀ x ∈ Ioi 0, HasDerivAt f (f' x) x)
    (hf_int : IntegrableOn f (Ioi 0)) (hf'_int : IntegrableOn f' (Ioi 0)) :
    (∫ x in Ioi (0 : ℝ), f x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) =
      f 0 / (Complex.I * (η : ℂ)) +
        (1 / (Complex.I * (η : ℂ))) *
          ∫ x in Ioi (0 : ℝ), f' x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ)) := by
  have hlim : Tendsto f atTop (𝓝 0) :=
    MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hderiv hf'_int hf_int
  let c : ℂ := -Complex.I * (η : ℂ)
  have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hη)
  have hprod_deriv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun t ↦ f t * Complex.exp (c * (t : ℂ)))
        ((f' x + c * f x) * Complex.exp (c * (x : ℂ))) x := by
    intro x hx
    have hof : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 x := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_id x)
    have h1 : HasDerivAt (fun t : ℝ ↦ c * (t : ℂ)) c x := (hof.const_mul c).congr_deriv (mul_one c)
    have h2 : HasDerivAt (fun t : ℝ ↦ Complex.exp (c * (t : ℂ))) (c * Complex.exp (c * (x : ℂ))) x :=
      ((Complex.hasDerivAt_exp (c * (x : ℂ))).comp x h1).congr_deriv (mul_comm _ _)
    exact ((hderiv x hx).mul h2).congr_deriv (by ring)
  have hexp_norm (t : ℝ) : ‖Complex.exp (c * (t : ℂ))‖ = 1 := by
    have heq : c * (t : ℂ) = ((-η * t : ℝ) : ℂ) * Complex.I := by
      simp only [c, Complex.ofReal_mul, Complex.ofReal_neg]
      ring
    rw [heq]
    exact Complex.norm_exp_ofReal_mul_I _
  have hi_exp : IntegrableOn (fun x : ℝ ↦ (f' x + c * f x) * Complex.exp (c * (x : ℂ))) (Ioi 0) := by
    refine ((hf'_int.add (hf_int.const_mul c)).norm).mono'
      (((hf'_int.1.add (hf_int.1.const_mul c)).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable))
      (ae_of_all _ fun x ↦ ?_)
    simp [hexp_norm]
  have hlim_prod : Tendsto (fun t : ℝ ↦ f t * Complex.exp (c * (t : ℂ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun t ↦ ?_) (by simpa only [norm_zero] using hlim.norm)
    rw [norm_mul, hexp_norm, mul_one]
  have hcont_prod : ContinuousWithinAt (fun t : ℝ ↦ f t * Complex.exp (c * (t : ℂ))) (Ici 0) 0 :=
    hcont.mul ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousWithinAt)
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont_prod hprod_deriv hi_exp hlim_prod
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hftc
  have hint1 : IntegrableOn (fun x : ℝ ↦ f' x * Complex.exp (c * (x : ℂ))) (Ioi 0) := by
    refine hf'_int.norm.mono'
      (hf'_int.1.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
      (ae_of_all _ fun x ↦ ?_)
    rw [norm_mul, hexp_norm, mul_one]
  have hint2 : IntegrableOn (fun x : ℝ ↦ f x * Complex.exp (c * (x : ℂ))) (Ioi 0) := by
    refine hf_int.norm.mono'
      (hf_int.1.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
      (ae_of_all _ fun x ↦ ?_)
    rw [norm_mul, hexp_norm, mul_one]
  have hsplit : (∫ x in Ioi (0 : ℝ), (f' x + c * f x) * Complex.exp (c * (x : ℂ))) =
      (∫ x in Ioi (0 : ℝ), f' x * Complex.exp (c * (x : ℂ))) +
        c * ∫ x in Ioi (0 : ℝ), f x * Complex.exp (c * (x : ℂ)) := by
    have hcongr : (fun x : ℝ ↦ (f' x + c * f x) * Complex.exp (c * (x : ℂ))) =
        (fun x : ℝ ↦ f' x * Complex.exp (c * (x : ℂ)) + c * (f x * Complex.exp (c * (x : ℂ)))) := by
      funext x; ring
    rw [hcongr, integral_add hint1 (hint2.const_mul c), integral_const_mul]
  rw [hsplit] at hftc
  have heq_neg : -c = Complex.I * (η : ℂ) := by simp [c]
  change (∫ x in Ioi (0 : ℝ), f x * Complex.exp (c * (x : ℂ))) = _
  rw [← heq_neg]
  have hsolve : (-c) * (∫ x in Ioi (0 : ℝ), f x * Complex.exp (c * (x : ℂ))) =
      f 0 + ∫ x in Ioi (0 : ℝ), f' x * Complex.exp (c * (x : ℂ)) := by
    linear_combination -hftc
  calc ∫ x in Ioi (0 : ℝ), f x * Complex.exp (c * (x : ℂ))
      = ((-c)⁻¹) * ((-c) * ∫ x in Ioi (0 : ℝ), f x * Complex.exp (c * (x : ℂ))) := by
        rw [← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr hc), one_mul]
    _ = (-c)⁻¹ * (f 0 + ∫ x in Ioi (0 : ℝ), f' x * Complex.exp (c * (x : ℂ))) := by rw [hsolve]
    _ = f 0 / (-c) + (1 / (-c)) * ∫ x in Ioi (0 : ℝ), f' x * Complex.exp (c * (x : ℂ)) := by
        ring

/-- Half-line integration by parts on `Iio 0` obtained by reflecting `x ↦ -x` into `Ioi 0`. -/
theorem fourier_ibp_Iio {f f' : ℝ → ℂ} {η : ℝ} (hη : η ≠ 0)
    (hcont : ContinuousWithinAt f (Iic 0) 0)
    (hderiv : ∀ x ∈ Iio 0, HasDerivAt f (f' x) x)
    (hf_int : IntegrableOn f (Iio 0)) (hf'_int : IntegrableOn f' (Iio 0)) :
    (∫ x in Iio (0 : ℝ), f x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) =
      -f 0 / (Complex.I * (η : ℂ)) +
        (1 / (Complex.I * (η : ℂ))) *
          ∫ x in Iio (0 : ℝ), f' x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ)) := by
  let g (x : ℝ) : ℂ := f (-x)
  let g' (x : ℝ) : ℂ := -f' (-x)
  have hg_cont : ContinuousWithinAt g (Ici 0) 0 := by
    have hmaps : MapsTo (fun x : ℝ ↦ -x) (Ici (0 : ℝ)) (Iic (0 : ℝ)) := fun x hx ↦ neg_nonpos.mpr hx
    have hcont0 : ContinuousWithinAt f (Iic 0) (-0) := by simpa only [neg_zero] using hcont
    exact ContinuousWithinAt.comp (g := f) (f := fun x : ℝ ↦ -x) hcont0
      continuous_neg.continuousWithinAt hmaps
  have hg_deriv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g (g' x) x := by
    intro x hx
    have hx' : -x ∈ Iio (0 : ℝ) := neg_lt_zero.mpr hx
    have hc : HasDerivAt (f ∘ Neg.neg) ((-1 : ℝ) • f' (-x)) x :=
      HasDerivAt.scomp x (hderiv (-x) hx') (hasDerivAt_neg x)
    exact hc.congr_deriv (by simp [g'])
  have hIio_eq : ∀ φ : ℝ → ℂ,
      (∫ x in Iio (0 : ℝ), φ x) = ∫ x in Ioi (0 : ℝ), φ (-x) := fun φ ↦ by
    rw [← integral_Iic_eq_integral_Iio]
    simpa only [neg_zero] using (integral_comp_neg_Ioi (0 : ℝ) φ).symm
  have hIio_int : ∀ {φ : ℝ → ℂ}, IntegrableOn φ (Iio 0) → IntegrableOn (fun x ↦ φ (-x)) (Ioi 0) := by
    intro φ hφ
    have hm : MeasurePreserving (Neg.neg : ℝ → ℝ) volume volume := Measure.measurePreserving_neg volume
    have hcomp := (hm.integrableOn_comp_preimage (Homeomorph.neg ℝ).measurableEmbedding).mpr hφ
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Iio (0 : ℝ) = Ioi 0 := by ext x; simp
    rwa [hpre] at hcomp
  have hg_int : IntegrableOn g (Ioi 0) := hIio_int hf_int
  have hg'_int : IntegrableOn g' (Ioi 0) := (hIio_int hf'_int).neg
  have hrec := fourier_ibp_Ioi (η := -η) (neg_ne_zero.mpr hη) hg_cont hg_deriv hg_int hg'_int
  have hlhs : (∫ x in Ioi (0 : ℝ), g x * Complex.exp (-Complex.I * ((-η : ℝ) : ℂ) * (x : ℂ))) =
      ∫ x in Iio (0 : ℝ), f x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ)) := by
    rw [hIio_eq]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [g, Complex.ofReal_neg]
    ring_nf
  have hrhs : (∫ x in Ioi (0 : ℝ), g' x * Complex.exp (-Complex.I * ((-η : ℝ) : ℂ) * (x : ℂ))) =
      -∫ x in Iio (0 : ℝ), f' x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ)) := by
    rw [← integral_neg, hIio_eq]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [g', Complex.ofReal_neg]
    ring_nf
  rw [hlhs, hrhs] at hrec
  rw [hrec]
  simp only [g, neg_zero, Complex.ofReal_neg]
  ring

private theorem integrableOn_mul_fourier {s : Set ℝ} {φ : ℝ → ℂ} {η : ℝ}
    (hφ : IntegrableOn φ s) :
    IntegrableOn (fun x : ℝ ↦ φ x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) s := by
  refine hφ.norm.mono'
    (hφ.1.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
    (ae_of_all _ fun x ↦ ?_)
  have hn : ‖Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))‖ = 1 := by
    rw [show -Complex.I * (η : ℂ) * (x : ℂ) = ((-η * x : ℝ) : ℂ) * Complex.I by simp; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [norm_mul, hn, mul_one]

/-- Two-sided integration by parts three times for a function continuous at `0` whose positive
and negative half-line pieces extend smoothly across `0`. -/
theorem fourier_corner_three_ibp
    {H Hp Hm Hp1 Hm1 Hp2 Hm2 Hp3 Hm3 : ℝ → ℂ} {η : ℝ} (hη : η ≠ 0)
    (hHp_eq : ∀ x ∈ Ici (0 : ℝ), Hp x = H x) (hHm_eq : ∀ x ∈ Iic (0 : ℝ), Hm x = H x)
    (hHp0 : ContinuousWithinAt Hp (Ici 0) 0) (hHm0 : ContinuousWithinAt Hm (Iic 0) 0)
    (hHp1 : ContinuousWithinAt Hp1 (Ici 0) 0) (hHm1 : ContinuousWithinAt Hm1 (Iic 0) 0)
    (hHp2 : ContinuousWithinAt Hp2 (Ici 0) 0) (hHm2 : ContinuousWithinAt Hm2 (Iic 0) 0)
    (hd1p : ∀ x ∈ Ioi 0, HasDerivAt Hp (Hp1 x) x) (hd1m : ∀ x ∈ Iio 0, HasDerivAt Hm (Hm1 x) x)
    (hd2p : ∀ x ∈ Ioi 0, HasDerivAt Hp1 (Hp2 x) x) (hd2m : ∀ x ∈ Iio 0, HasDerivAt Hm1 (Hm2 x) x)
    (hd3p : ∀ x ∈ Ioi 0, HasDerivAt Hp2 (Hp3 x) x) (hd3m : ∀ x ∈ Iio 0, HasDerivAt Hm2 (Hm3 x) x)
    (hi0p : IntegrableOn Hp (Ioi 0)) (hi0m : IntegrableOn Hm (Iio 0))
    (hi1p : IntegrableOn Hp1 (Ioi 0)) (hi1m : IntegrableOn Hm1 (Iio 0))
    (hi2p : IntegrableOn Hp2 (Ioi 0)) (hi2m : IntegrableOn Hm2 (Iio 0))
    (hi3p : IntegrableOn Hp3 (Ioi 0)) (hi3m : IntegrableOn Hm3 (Iio 0)) :
    ‖(∫ x : ℝ, H x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) -
        (-(Hp1 0 - Hm1 0) / ((η : ℂ) ^ 2))‖ ≤
      (‖Hp2 0 - Hm2 0‖ + (∫ x in Ioi (0 : ℝ), ‖Hp3 x‖) + ∫ x in Iio (0 : ℝ), ‖Hm3 x‖) /
        |η| ^ 3 := by
  have hint_pos := integrableOn_mul_fourier (η := η) hi0p
  have hint_neg := integrableOn_mul_fourier (η := η) hi0m
  have hH_pos : (∫ x in Ioi (0 : ℝ), H x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) =
      ∫ x in Ioi (0 : ℝ), Hp x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ)) :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ by rw [hHp_eq x (le_of_lt hx)]
  have hH_neg : (∫ x in Iio (0 : ℝ), H x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) =
      ∫ x in Iio (0 : ℝ), Hm x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ)) :=
    setIntegral_congr_fun measurableSet_Iio fun x hx ↦ by rw [hHm_eq x (le_of_lt hx)]
  have hH_split : (∫ x : ℝ, H x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) =
      (∫ x in Iio (0 : ℝ), H x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) +
        ∫ x in Ioi (0 : ℝ), H x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ)) := by
    have hIio_H : IntegrableOn (fun x : ℝ ↦ H x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) (Iio 0) :=
      hint_neg.congr_fun (fun x hx ↦ by simp only [hHm_eq x (le_of_lt hx)]) measurableSet_Iio
    have hIoi_H : IntegrableOn (fun x : ℝ ↦ H x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) (Ioi 0) :=
      hint_pos.congr_fun (fun x hx ↦ by simp only [hHp_eq x (le_of_lt hx)]) measurableSet_Ioi
    have hIci_H : IntegrableOn (fun x : ℝ ↦ H x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) (Ici 0) :=
      hIoi_H.congr_set_ae Ioi_ae_eq_Ici.symm
    have h0 : (∫ x : ℝ, H x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) =
        ∫ x in Iio (0 : ℝ) ∪ Ici 0, H x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ)) := by
      rw [Iio_union_Ici, Measure.restrict_univ]
    rw [h0, setIntegral_union (Iio_disjoint_Ici le_rfl) measurableSet_Ici hIio_H hIci_H,
      integral_Ici_eq_integral_Ioi]
  rw [hH_split, hH_pos, hH_neg]
  have hp0 := fourier_ibp_Ioi hη hHp0 hd1p hi0p hi1p
  have hm0 := fourier_ibp_Iio hη hHm0 hd1m hi0m hi1m
  have hp1 := fourier_ibp_Ioi hη hHp1 hd2p hi1p hi2p
  have hm1 := fourier_ibp_Iio hη hHm1 hd2m hi1m hi2m
  have hp2 := fourier_ibp_Ioi hη hHp2 hd3p hi2p hi3p
  have hm2 := fourier_ibp_Iio hη hHm2 hd3m hi2m hi3m
  have hzero : Hp 0 = Hm 0 := (hHp_eq 0 le_rfl).trans (hHm_eq 0 le_rfl).symm
  have hIη : (Complex.I * (η : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hη)
  have hI2 : (Complex.I * (η : ℂ)) ^ 2 = -((η : ℂ) ^ 2) := by
    rw [mul_pow, Complex.I_sq]; ring
  have hstep1 :
      (∫ x in Iio (0 : ℝ), Hm x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) +
        (∫ x in Ioi (0 : ℝ), Hp x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) =
      (1 / (Complex.I * (η : ℂ))) *
        ((∫ x in Iio (0 : ℝ), Hm1 x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) +
          ∫ x in Ioi (0 : ℝ), Hp1 x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) := by
    rw [hm0, hp0, hzero]; ring
  have hstep2 :
      (∫ x in Iio (0 : ℝ), Hm1 x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) +
        (∫ x in Ioi (0 : ℝ), Hp1 x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) =
      (Hp1 0 - Hm1 0) / (Complex.I * (η : ℂ)) + (1 / (Complex.I * (η : ℂ))) *
        ((∫ x in Iio (0 : ℝ), Hm2 x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) +
          ∫ x in Ioi (0 : ℝ), Hp2 x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) := by
    rw [hm1, hp1]; ring
  have hstep3 :
      (∫ x in Iio (0 : ℝ), Hm2 x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) +
        (∫ x in Ioi (0 : ℝ), Hp2 x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) =
      (Hp2 0 - Hm2 0) / (Complex.I * (η : ℂ)) + (1 / (Complex.I * (η : ℂ))) *
        ((∫ x in Iio (0 : ℝ), Hm3 x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) +
          ∫ x in Ioi (0 : ℝ), Hp3 x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) := by
    rw [hm2, hp2]; ring
  have hrem :
      (∫ x in Iio (0 : ℝ), Hm x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) +
        (∫ x in Ioi (0 : ℝ), Hp x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) -
        (-(Hp1 0 - Hm1 0) / ((η : ℂ) ^ 2)) =
      (1 / (Complex.I * (η : ℂ)) ^ 3) * ((Hp2 0 - Hm2 0) +
        (∫ x in Ioi (0 : ℝ), Hp3 x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) +
        ∫ x in Iio (0 : ℝ), Hm3 x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) := by
    rw [hstep1, hstep2, hstep3]
    have hneg_sq : -(Hp1 0 - Hm1 0) / ((η : ℂ) ^ 2) =
        (Hp1 0 - Hm1 0) / (Complex.I * (η : ℂ)) ^ 2 := by
      rw [hI2, div_neg, neg_div]
    rw [hneg_sq]
    field_simp [hIη]
    ring
  rw [hrem, norm_mul]
  have hden : ‖(1 : ℂ) / (Complex.I * (η : ℂ)) ^ 3‖ = (|η| ^ 3)⁻¹ := by
    rw [one_div, norm_inv, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
  rw [hden, inv_mul_eq_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hint_norm : ∀ {s : Set ℝ} {φ : ℝ → ℂ}, IntegrableOn φ s →
      ‖∫ x in s, φ x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))‖ ≤ ∫ x in s, ‖φ x‖ := by
    intro s φ hφ
    refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (.of_forall fun x ↦ ?_))
    have hn : ‖Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))‖ = 1 := by
      rw [show -Complex.I * (η : ℂ) * (x : ℂ) = ((-η * x : ℝ) : ℂ) * Complex.I by simp; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    simp only [norm_mul, hn, mul_one]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add le_rfl (hint_norm hi3p))) (hint_norm hi3m))

/-- Smooth `N`-fold integration by parts on `ℝ`: if all derivatives of order `k ≤ N` are
integrable, the Fourier transform at `η ≠ 0` is bounded by `‖H^{(N)}‖₁ / |η|^N`. -/
theorem fourier_smooth_rapid_decay
    (N : ℕ) (H : ℝ → ℂ) (hH : ContDiff ℝ N H)
    (hint : ∀ k ≤ N, Integrable (fun x : ℝ ↦ iteratedDeriv k H x))
    {η : ℝ} (hη : η ≠ 0) :
    ‖∫ x : ℝ, H x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))‖ ≤
      (∫ x : ℝ, ‖iteratedDeriv N H x‖) / |η| ^ N := by
  induction N generalizing H with
  | zero =>
    simp only [pow_zero, div_one, iteratedDeriv_zero]
    refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (.of_forall fun x ↦ ?_))
    have hn : ‖Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))‖ = 1 := by
      rw [show -Complex.I * (η : ℂ) * (x : ℂ) = ((-η * x : ℝ) : ℂ) * Complex.I by simp; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    simp only [norm_mul, hn, mul_one]
  | succ n ih =>
    have hH1 : ContDiff ℝ n (deriv H) := (contDiff_succ_iff_deriv.mp hH).2.2
    have hH0 : ContDiff ℝ 1 H := hH.of_le (by norm_cast; omega)
    have hd : ∀ x : ℝ, HasDerivAt H (deriv H x) x := fun x ↦
      ((contDiff_one_iff_deriv.mp hH0).1 x).hasDerivAt
    have hint' : ∀ k ≤ n, Integrable (fun x : ℝ ↦ iteratedDeriv k (deriv H) x) := by
      intro k hk
      simpa only [← iteratedDeriv_succ'] using hint (k + 1) (by omega)
    have hcontH : Continuous H := hH0.continuous
    have hp := fourier_ibp_Ioi hη hcontH.continuousWithinAt
      (fun x _ ↦ hd x) (hint 0 (Nat.zero_le _)).integrableOn
      (by simpa [iteratedDeriv_one] using (hint 1 (by omega)).integrableOn)
    have hm := fourier_ibp_Iio hη hcontH.continuousWithinAt
      (fun x _ ↦ hd x) (hint 0 (Nat.zero_le _)).integrableOn
      (by simpa [iteratedDeriv_one] using (hint 1 (by omega)).integrableOn)
    have hsplit : ∀ φ : ℝ → ℂ, Integrable φ →
        (∫ x : ℝ, φ x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) =
          (∫ x in Iio (0 : ℝ), φ x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) +
            ∫ x in Ioi (0 : ℝ), φ x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ)) := by
      intro φ hφ
      have h1 := integrableOn_mul_fourier (η := η) (hφ.integrableOn (s := Iio 0))
      have h2 := integrableOn_mul_fourier (η := η) (hφ.integrableOn (s := Ici 0))
      have h0 : (∫ x : ℝ, φ x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) =
          ∫ x in Iio (0 : ℝ) ∪ Ici 0, φ x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ)) := by
        rw [Iio_union_Ici, Measure.restrict_univ]
      rw [h0, setIntegral_union (Iio_disjoint_Ici le_rfl) measurableSet_Ici h1 h2, integral_Ici_eq_integral_Ioi]
    have hstep : (∫ x : ℝ, H x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) =
        (1 / (Complex.I * (η : ℂ))) *
          ∫ x : ℝ, deriv H x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ)) := by
      rw [hsplit H (by simpa using hint 0 (Nat.zero_le _)),
        hsplit (deriv H) (by simpa [iteratedDeriv_one] using hint 1 (by omega)), hm, hp]
      ring
    rw [hstep, norm_mul]
    have hinv : ‖(1 : ℂ) / (Complex.I * (η : ℂ))‖ = |η|⁻¹ := by
      simp [Complex.norm_I, Complex.norm_real]
    rw [hinv]
    have hrec := ih (deriv H) hH1 hint'
    have heq_int : (∫ x : ℝ, ‖iteratedDeriv (n + 1) H x‖) =
        ∫ x : ℝ, ‖iteratedDeriv n (deriv H) x‖ := by
      refine integral_congr_ae (.of_forall fun x ↦ ?_)
      rw [iteratedDeriv_succ']
    rw [heq_int, pow_succ, ← div_div, div_eq_mul_inv ( _ / |η| ^ n), mul_comm |η|⁻¹]
    exact mul_le_mul_of_nonneg_right hrec (by positivity)

end ScalarCornerIBP

section ScalarCornerTheorems

/-- Real derivatives of `(1 + x^2)^(-s/2)`: every `k`-th derivative is a polynomial of degree at
most `k` times `(1 + x^2)^(-s/2 - k)`. -/
private theorem iteratedDeriv_one_add_sq_rpow (s : ℝ) (k : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ ↦ (1 + x ^ 2) ^ (-s / 2 - k)) ∧
      ∃ P : Polynomial ℝ, P.natDegree ≤ k ∧ ∀ x : ℝ,
        iteratedDeriv k (fun t : ℝ ↦ (1 + t ^ 2) ^ (-s / 2)) x =
          P.eval x * (1 + x ^ 2) ^ (-s / 2 - k) := by
  have hsmooth (m : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ ↦ (1 + x ^ 2) ^ (-s / 2 - m)) := by
    have hbase : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ ↦ (1 : ℝ) + x ^ 2) :=
      contDiff_const.add (contDiff_id.pow 2)
    exact hbase.rpow_const_of_ne fun x ↦ by positivity
  refine ⟨hsmooth k, ?_⟩
  induction k with
  | zero =>
    refine ⟨1, by simp, fun x ↦ by simp⟩
  | succ n ih =>
    obtain ⟨P, hdeg, hP⟩ := ih
    let Q : Polynomial ℝ :=
      P.derivative * (1 + Polynomial.X ^ 2) - (Polynomial.C (s + 2 * n) * Polynomial.X) * P
    have hdegQ : Q.natDegree ≤ n + 1 := by
      have h1 : (P.derivative * (1 + Polynomial.X ^ 2)).natDegree ≤ n + 1 := by
        rcases eq_or_ne P.derivative 0 with hd | hd
        · simp [hd]
        · have hPd : P.derivative.natDegree ≤ n - 1 :=
            (Polynomial.natDegree_derivative_le (p := P)).trans (Nat.sub_le_sub_right hdeg 1)
          have hn1 : 1 ≤ n := by
            by_contra hlt
            have hn0 : n = 0 := by omega
            have hc : P.natDegree = 0 := Nat.eq_zero_of_le_zero (hdeg.trans_eq hn0)
            rw [Polynomial.eq_C_of_natDegree_eq_zero hc, Polynomial.derivative_C] at hd
            exact hd rfl
          calc (P.derivative * (1 + Polynomial.X ^ 2)).natDegree
              ≤ P.derivative.natDegree + (1 + Polynomial.X ^ 2 : Polynomial ℝ).natDegree :=
                Polynomial.natDegree_mul_le
            _ ≤ (n - 1) + 2 := by
                refine add_le_add hPd ?_
                have : (1 + Polynomial.X ^ 2 : Polynomial ℝ).natDegree = 2 := by compute_degree!
                linarith
            _ = n + 1 := by omega
      have h2 : ((Polynomial.C (s + 2 * n) * Polynomial.X) * P).natDegree ≤ n + 1 := by
        calc ((Polynomial.C (s + 2 * n) * Polynomial.X) * P).natDegree
            ≤ (Polynomial.C (s + 2 * n) * Polynomial.X).natDegree + P.natDegree :=
              Polynomial.natDegree_mul_le
          _ ≤ 1 + n := add_le_add (by compute_degree!) hdeg
          _ = n + 1 := by omega
      exact (Polynomial.natDegree_sub_le _ _).trans (max_le h1 h2)
    refine ⟨Q, hdegQ, fun x ↦ ?_⟩
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv n (fun t : ℝ ↦ (1 + t ^ 2) ^ (-s / 2)) =
        fun t : ℝ ↦ P.eval t * (1 + t ^ 2) ^ (-s / 2 - n) := funext hP
    rw [hfun]
    have hpos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity
    have hd1 : HasDerivAt (fun t ↦ P.eval t) (P.derivative.eval x) x :=
      P.hasDerivAt x
    have hd2 : HasDerivAt (fun t : ℝ ↦ (1 + t ^ 2) ^ (-s / 2 - (n : ℝ)))
        ((-s / 2 - (n : ℝ)) * (1 + x ^ 2) ^ (-s / 2 - (n : ℝ) - 1) * (2 * x)) x := by
      have hinner : HasDerivAt (fun t : ℝ ↦ 1 + t ^ 2) (2 * x) x := by
        simpa using (hasDerivAt_id x |>.pow 2).const_add 1
      exact (HasDerivAt.rpow_const hinner (Or.inl (hpos x).ne')).congr_deriv (by ring)
    have hprod := hd1.mul hd2
    have hder : deriv (fun t : ℝ ↦ P.eval t * (1 + t ^ 2) ^ (-s / 2 - (n : ℝ))) x =
        P.derivative.eval x * (1 + x ^ 2) ^ (-s / 2 - (n : ℝ)) +
          P.eval x * ((-s / 2 - (n : ℝ)) * (1 + x ^ 2) ^ (-s / 2 - (n : ℝ) - 1) * (2 * x)) :=
      hprod.deriv
    rw [hder]
    have hpow : (1 + x ^ 2) ^ (-s / 2 - ((n + 1 : ℕ) : ℝ)) =
        (1 + x ^ 2) ^ (-s / 2 - (n : ℝ) - 1) := by
      push_cast; ring_nf
    have hpow' : (1 + x ^ 2) ^ (-s / 2 - (n : ℝ)) =
        (1 + x ^ 2) * (1 + x ^ 2) ^ (-s / 2 - (n : ℝ) - 1) := by
      calc (1 + x ^ 2) ^ (-s / 2 - (n : ℝ))
          = (1 + x ^ 2) ^ ((1 : ℝ) + (-s / 2 - (n : ℝ) - 1)) := by ring_nf
        _ = (1 + x ^ 2) ^ (1 : ℝ) * (1 + x ^ 2) ^ (-s / 2 - (n : ℝ) - 1) :=
            Real.rpow_add (hpos x) _ _
        _ = (1 + x ^ 2) * (1 + x ^ 2) ^ (-s / 2 - (n : ℝ) - 1) := by rw [Real.rpow_one]
    rw [hpow]
    calc P.derivative.eval x * (1 + x ^ 2) ^ (-s / 2 - (n : ℝ)) +
          P.eval x * ((-s / 2 - (n : ℝ)) * (1 + x ^ 2) ^ (-s / 2 - (n : ℝ) - 1) * (2 * x))
        = (P.derivative.eval x * (1 + x ^ 2) - (s + 2 * (n : ℝ)) * x * P.eval x) *
            (1 + x ^ 2) ^ (-s / 2 - (n : ℝ) - 1) := by rw [hpow']; ring
      _ = Q.eval x * (1 + x ^ 2) ^ (-s / 2 - (n : ℝ) - 1) := by
          simp [Q, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
            Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one]

/-- Integrability of `(1 + x^2)^(-s/2)` on `ℝ` for `s > 1`. -/
theorem integrable_one_add_sq_neg_rpow {s : ℝ} (hs : 1 < s) :
    Integrable (fun x : ℝ ↦ (1 + x ^ 2) ^ (-s / 2)) volume := by
  have hcont : Continuous (fun x : ℝ ↦ (1 + x ^ 2) ^ (-s / 2)) :=
    (continuous_const.add (continuous_id.pow 2)).rpow_const fun x ↦
      Or.inl (by positivity : (1 : ℝ) + x ^ 2 ≠ 0)
  have hint1 : IntegrableOn (fun x : ℝ ↦ (1 + x ^ 2) ^ (-s / 2)) (Icc (-1) 1) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hint_top : IntegrableOn (fun x : ℝ ↦ (1 + x ^ 2) ^ (-s / 2)) (Ioi 1) := by
    have hpow : IntegrableOn (fun x : ℝ ↦ x ^ (-s)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine hpow.mono' hcont.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 < x := hx
    have hx0 : 0 < x := zero_lt_one.trans hx1
    rw [Real.norm_of_nonneg (by positivity)]
    have hle : x ^ 2 ≤ 1 + x ^ 2 := le_add_of_nonneg_left zero_le_one
    calc (1 + x ^ 2) ^ (-s / 2) ≤ (x ^ 2) ^ (-s / 2) :=
          Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hx0) hle (by linarith)
      _ = x ^ (2 * (-s / 2)) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
      _ = x ^ (-s) := by ring_nf
  have hint_bot : IntegrableOn (fun x : ℝ ↦ (1 + x ^ 2) ^ (-s / 2)) (Iio (-1)) := by
    have hm := ((Measure.measurePreserving_neg volume).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mpr hint_top
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Ioi (1 : ℝ) = Iio (-1) := by
      ext x; simp [lt_neg]
    rw [hpre] at hm
    refine hm.congr_fun (fun x _ ↦ ?_) measurableSet_Iio
    simp
  have hunion : (univ : Set ℝ) = Iio (-1) ∪ (Icc (-1) 1 ∪ Ioi 1) := by
    ext x
    simp only [mem_univ, mem_union, mem_Iio, mem_Icc, mem_Ioi, true_iff]
    rcases lt_or_ge x (-1) with h | h
    · exact Or.inl h
    · rcases le_or_gt x 1 with h1 | h1
      · exact Or.inr (Or.inl ⟨h, h1⟩)
      · exact Or.inr (Or.inr h1)
  rw [← integrableOn_univ, hunion]
  exact hint_bot.union (hint1.union hint_top)

/-- Pointwise bound on every `k`-th derivative of `(1 + x^2)^(-s/2)` by a constant multiple of
`(1 + x^2)^(-s/2)`. -/
theorem iteratedDeriv_one_add_sq_rpow_le (s : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      |iteratedDeriv k (fun t : ℝ ↦ (1 + t ^ 2) ^ (-s / 2)) x| ≤ C * (1 + x ^ 2) ^ (-s / 2) := by
  obtain ⟨P, hdeg, hP⟩ := (iteratedDeriv_one_add_sq_rpow s k).2
  let M : ℝ := ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i|
  refine ⟨M, Finset.sum_nonneg fun _ _ ↦ abs_nonneg _, fun x ↦ ?_⟩
  rw [hP x, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
  have hPx : |P.eval x| ≤ M * (1 + x ^ 2) ^ (k : ℝ) := by
    rw [Polynomial.eval_eq_sum_range]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    rw [abs_mul, abs_pow]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hik : i ≤ k := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hdeg
    have h1x : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    have hxi : |x| ^ i ≤ (1 + x ^ 2) ^ i := by
      have hsq : |x| ≤ 1 + x ^ 2 := by nlinarith [sq_abs x, sq_nonneg (|x| - 1 / 2)]
      exact pow_le_pow_left₀ (abs_nonneg x) hsq i
    calc |x| ^ i ≤ (1 + x ^ 2) ^ i := hxi
      _ ≤ (1 + x ^ 2) ^ k := pow_le_pow_right₀ h1x hik
      _ = (1 + x ^ 2) ^ (k : ℝ) := (Real.rpow_natCast _ k).symm
  have hpos : 0 < 1 + x ^ 2 := by positivity
  calc |P.eval x| * (1 + x ^ 2) ^ (-s / 2 - (k : ℝ))
      ≤ (M * (1 + x ^ 2) ^ (k : ℝ)) * (1 + x ^ 2) ^ (-s / 2 - (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hPx (by positivity)
    _ = M * ((1 + x ^ 2) ^ (k : ℝ) * (1 + x ^ 2) ^ (-s / 2 - (k : ℝ))) := by ring
    _ = M * (1 + x ^ 2) ^ (-s / 2) := by
        rw [← Real.rpow_add hpos]
        ring_nf

/-- Pointwise equality between `iteratedDeriv k (fun x ↦ (f x : ℂ))` and `(iteratedDeriv k f x : ℂ)`. -/
theorem iteratedDeriv_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun t : ℝ ↦ (f t : ℂ)) x = Complex.ofReal (iteratedDeriv k f x) := by
  induction k generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun t : ℝ ↦ (f t : ℂ)) = fun t ↦ Complex.ofReal (iteratedDeriv n f t) :=
      funext ih
    rw [heq]
    have hd : HasDerivAt (iteratedDeriv n f) (deriv (iteratedDeriv n f) x) x :=
      (hf.differentiable_iteratedDeriv n (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top n)) x).hasDerivAt
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hd).deriv

/-- Every `k`-th derivative of `t ↦ Real.exp (c * t)` is `c ^ k * Real.exp (c * t)`. -/
private theorem iteratedDeriv_exp_const_mul (c : ℝ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun u : ℝ ↦ Real.exp (c * u)) t = c ^ k * Real.exp (c * t) := by
  induction k generalizing t with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ]
    have hfn : iteratedDeriv m (fun u : ℝ ↦ Real.exp (c * u)) = fun u ↦ c ^ m * Real.exp (c * u) :=
      funext ih
    rw [hfn]
    have hd : HasDerivAt (fun u : ℝ ↦ Real.exp (c * u)) (c * Real.exp (c * t)) t := by
      have hi : HasDerivAt (fun u : ℝ ↦ c * u) c t := by simpa using (hasDerivAt_id t).const_mul c
      exact ((Real.hasDerivAt_exp (c * t)).comp t hi).congr_deriv (mul_comm _ _)
    rw [(hd.const_mul (c ^ m)).deriv]; ring

/-- For `c ≤ 0`, every `k`-th derivative of `t ↦ Real.exp (c * t) * (1 + t^2)^(-s/2)` is
bounded on `Ici 0` by `C_k * (1 + t^2)^(-s/2)`, hence is integrable on `Ioi 0` when `s > 1`. -/
private theorem exp_mul_rpow_iteratedDeriv_Ioi {c s : ℝ} (hc : c ≤ 0) (hs : 1 < s) (k : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ ↦ Real.exp (c * t) * (1 + t ^ 2) ^ (-s / 2)) ∧
      IntegrableOn (fun t : ℝ ↦ iteratedDeriv k (fun u : ℝ ↦
        ((Real.exp (c * u) * (1 + u ^ 2) ^ (-s / 2) : ℝ) : ℂ)) t) (Ioi 0) := by
  let g (t : ℝ) : ℝ := (1 + t ^ 2) ^ (-s / 2)
  have hbase : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ ↦ (1 : ℝ) + x ^ 2) :=
    contDiff_const.add (contDiff_id.pow 2)
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g :=
    hbase.rpow_const_of_ne fun x ↦ by positivity
  have he : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ ↦ Real.exp (c * t)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  refine ⟨he.mul hg, ?_⟩
  let Fc : ℝ → ℂ := fun t ↦ ((Real.exp (c * t) * g t : ℝ) : ℂ)
  have hint_real : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioi (0 : ℝ),
      |iteratedDeriv n (fun u : ℝ ↦ Real.exp (c * u) * g u) t| ≤ C * g t := by
    intro n
    have hn : iteratedDeriv n (fun u : ℝ ↦ Real.exp (c * u) * g u) =
        fun t ↦ ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * iteratedDeriv i (fun u : ℝ ↦ Real.exp (c * u)) t *
            iteratedDeriv (n - i) g t := by
      funext t
      exact iteratedDeriv_mul (he.contDiffAt.of_le (by exact mod_cast le_top))
        (hg.contDiffAt.of_le (by exact mod_cast le_top))
    rw [hn]
    choose Cg hCg0 hCg using fun m ↦ iteratedDeriv_one_add_sq_rpow_le s m
    refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |c| ^ i * Cg (n - i),
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (hCg0 _),
      fun t ht ↦ ?_⟩
    have hsum := Finset.abs_sum_le_sum_abs
      (fun i ↦ (n.choose i : ℝ) * iteratedDeriv i (fun u : ℝ ↦ Real.exp (c * u)) t *
        iteratedDeriv (n - i) g t) (Finset.range (n + 1))
    refine hsum.trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), iteratedDeriv_exp_const_mul c i t,
      abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    have hexp_le : Real.exp (c * t) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hc (le_of_lt ht))
    calc (n.choose i : ℝ) * (|c| ^ i * Real.exp (c * t)) * |iteratedDeriv (n - i) g t|
        ≤ (n.choose i : ℝ) * (|c| ^ i * 1) * (Cg (n - i) * g t) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp_le (by positivity))
            (Nat.cast_nonneg _)) (hCg (n - i) t) (abs_nonneg _) (by positivity)
      _ = (n.choose i : ℝ) * |c| ^ i * Cg (n - i) * g t := by ring
  obtain ⟨Ck, _, hCk⟩ := hint_real k
  have hcont_c : Continuous (iteratedDeriv k Fc) :=
    (Complex.ofRealCLM.contDiff.comp (he.mul hg)).continuous_iteratedDeriv k (by exact mod_cast le_top)
  refine ((integrable_one_add_sq_neg_rpow hs).const_mul Ck).integrableOn.mono'
    hcont_c.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖iteratedDeriv k Fc t‖ ≤ _
  rw [iteratedDeriv_ofReal (he.mul hg) k t, Complex.norm_real, Real.norm_eq_abs]
  exact hCk t ht

/-- Corner Fourier asymptotic for `exp (σ * x) / intervalSobolevDensity (-α) α s x` (`0 < α`, `1 < s`,
`σ ∈ [-α, α]`, `η ≠ 0`). -/
theorem intervalSobolevDensity_inv_fourier_asymptotic {α s σ : ℝ} (hα : 0 < α) (hs : 1 < s)
    (hσ : σ ∈ Icc (-α) α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, η ≠ 0 →
      ‖(∫ x : ℝ, ((Real.exp (σ * x) / intervalSobolevDensity (-α) α s x : ℝ) : ℂ) *
            Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) -
          ((4 * α / η ^ 2 : ℝ) : ℂ)‖ ≤ C / |η| ^ 3 := by
  let cp : ℝ := -(2 * α - σ)
  let cm : ℝ := 2 * α + σ
  have hcp : cp ≤ 0 := by linarith [hσ.1, hσ.2]
  have hcm : cm ≤ 0 → cm = 0 := fun h ↦ by linarith [hσ.1, hσ.2]
  have hcm0 : 0 ≤ cm := by linarith [hσ.1, hσ.2]
  let g (t : ℝ) : ℝ := (1 + t ^ 2) ^ (-s / 2)
  let Hp_r (t : ℝ) : ℝ := Real.exp (cp * t) * g t
  let Hm_r (t : ℝ) : ℝ := Real.exp (cm * t) * g t
  let H (t : ℝ) : ℂ := ((Real.exp (σ * t) / intervalSobolevDensity (-α) α s t : ℝ) : ℂ)
  let Hp (t : ℝ) : ℂ := (Hp_r t : ℂ)
  let Hm (t : ℝ) : ℂ := (Hm_r t : ℂ)
  have hHp_eq : ∀ x ∈ Ici (0 : ℝ), Hp x = H x := by
    intro x (hx : 0 ≤ x)
    simp only [Hp, Hp_r, H, intervalSobolevDensity, g]
    have hmax : max (Real.exp (2 * (-α) * x)) (Real.exp (2 * α * x)) = Real.exp (2 * α * x) :=
      max_eq_right (Real.exp_le_exp.mpr (by nlinarith))
    rw [hmax, Complex.ofReal_inj]
    have h1 : (1 + x ^ 2) ^ (-s / 2) = ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
      rw [← Real.rpow_neg (by positivity)]
      congr 1; ring
    have hsub : cp * x = σ * x - 2 * α * x := by simp [cp]; ring
    rw [h1, hsub, Real.exp_sub]
    ring
  have hHm_eq : ∀ x ∈ Iic (0 : ℝ), Hm x = H x := by
    intro x (hx : x ≤ 0)
    simp only [Hm, Hm_r, H, intervalSobolevDensity, g]
    have hmax : max (Real.exp (2 * (-α) * x)) (Real.exp (2 * α * x)) = Real.exp (2 * (-α) * x) :=
      max_eq_left (Real.exp_le_exp.mpr (by nlinarith))
    rw [hmax, Complex.ofReal_inj]
    have h1 : (1 + x ^ 2) ^ (-s / 2) = ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
      rw [← Real.rpow_neg (by positivity)]
      congr 1; ring
    have hsub : cm * x = σ * x - 2 * (-α) * x := by simp [cm]; ring
    rw [h1, hsub, Real.exp_sub]
    ring
  -- Smoothness and integrability on Ioi 0 for Hp, and on Iio 0 for Hm (via reflection x ↦ -x)
  have hHp_prop := fun k ↦ exp_mul_rpow_iteratedDeriv_Ioi hcp hs k
  have hHm_neg_prop := fun k ↦ exp_mul_rpow_iteratedDeriv_Ioi (c := -cm) (neg_nonpos.mpr hcm0) hs k
  let Hp1 := iteratedDeriv 1 Hp
  let Hp2 := iteratedDeriv 2 Hp
  let Hp3 := iteratedDeriv 3 Hp
  let Hm1 := iteratedDeriv 1 Hm
  let Hm2 := iteratedDeriv 2 Hm
  let Hm3 := iteratedDeriv 3 Hm
  have hHp_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) Hp := Complex.ofRealCLM.contDiff.comp (hHp_prop 0).1
  have hHm_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) Hm := by
    have hbase : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ ↦ (1 : ℝ) + x ^ 2) :=
      contDiff_const.add (contDiff_id.pow 2)
    have hg_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) g :=
      hbase.rpow_const_of_ne fun x ↦ by positivity
    have hrm : ContDiff ℝ (↑(⊤ : ℕ∞)) Hm_r :=
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul hg_cd
    exact Complex.ofRealCLM.contDiff.comp hrm
  have hHm_refl_int (k : ℕ) : IntegrableOn Hm (Iio 0) ∧ IntegrableOn (iteratedDeriv k Hm) (Iio 0) := by
    have hcomp_deriv (x : ℝ) :
        iteratedDeriv k (fun u : ℝ ↦ ((Real.exp (-cm * u) * (1 + u ^ 2) ^ (-s / 2) : ℝ) : ℂ)) x =
          (-1 : ℂ) ^ k * iteratedDeriv k Hm (-x) := by
      have heq : (fun u : ℝ ↦ ((Real.exp (-cm * u) * (1 + u ^ 2) ^ (-s / 2) : ℝ) : ℂ)) =
          fun u ↦ Hm (-u) := funext fun u ↦ by simp [Hm, Hm_r, g]
      rw [heq, iteratedDeriv_comp_neg k Hm x]
      simp
    have hi_pos := (hHm_neg_prop k).2
    have hi0 : IntegrableOn Hm (Iio 0) := by
      have hi_pos0 := (hHm_neg_prop 0).2
      have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Ioi (0 : ℝ) = Iio 0 := by ext x; simp
      have hic : IntegrableOn
          ((fun u : ℝ ↦ ((Real.exp (-cm * u) * (1 + u ^ 2) ^ (-s / 2) : ℝ) : ℂ)) ∘ Neg.neg)
          (Neg.neg ⁻¹' Ioi (0 : ℝ)) :=
        ((Measure.measurePreserving_neg volume).integrableOn_comp_preimage
          (Homeomorph.neg ℝ).measurableEmbedding).mpr hi_pos0
      rw [hpre] at hic
      exact hic.congr_fun (fun x _ ↦ by simp [Hm, Hm_r, g]) measurableSet_Iio
    have hik : IntegrableOn (iteratedDeriv k Hm) (Iio 0) := by
      have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Ioi (0 : ℝ) = Iio 0 := by ext x; simp
      have hic : IntegrableOn
          ((fun x : ℝ ↦ (-1 : ℂ) ^ (-k : ℤ) *
            iteratedDeriv k (fun u : ℝ ↦ ((Real.exp (-cm * u) * (1 + u ^ 2) ^ (-s / 2) : ℝ) : ℂ)) x) ∘ Neg.neg)
          (Neg.neg ⁻¹' Ioi (0 : ℝ)) :=
        ((Measure.measurePreserving_neg volume).integrableOn_comp_preimage
          (Homeomorph.neg ℝ).measurableEmbedding).mpr (hi_pos.const_mul ((-1 : ℂ) ^ (-k : ℤ)))
      rw [hpre] at hic
      refine hic.congr_fun (fun x _ ↦ ?_) measurableSet_Iio
      have hcd : iteratedDeriv k (fun u : ℝ ↦ ((Real.exp (-cm * u) * (1 + u ^ 2) ^ (-s / 2) : ℝ) : ℂ)) (-x) =
          (-1 : ℂ) ^ k * iteratedDeriv k Hm x := by
        simpa only [neg_neg] using hcomp_deriv (-x)
      dsimp only [Function.comp_def]
      rw [hcd]
      have hpow : (-1 : ℂ) ^ (-k : ℤ) * (-1 : ℂ) ^ k = 1 := by
        rw [← zpow_natCast (-1 : ℂ) k, ← zpow_add₀ (by norm_num), neg_add_cancel, zpow_zero]
      rw [← mul_assoc, hpow, one_mul]
    exact ⟨hi0, hik⟩
  have hjump1 : -(Hp1 0 - Hm1 0) = ((4 * α : ℝ) : ℂ) := by
    have hd_exp_g : ∀ c : ℝ, deriv (fun t : ℝ ↦ ((Real.exp (c * t) * g t : ℝ) : ℂ)) 0 = (c : ℂ) := by
      intro c
      have hg0 : g 0 = 1 := by simp [g]
      have he0 : HasDerivAt (fun t : ℝ ↦ Real.exp (c * t)) c 0 := by
        have hi : HasDerivAt (fun t : ℝ ↦ c * t) c 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
        exact ((Real.hasDerivAt_exp (c * (0 : ℝ))).comp 0 hi).congr_deriv (by simp)
      have hgd : HasDerivAt g 0 0 := by
        have hinner : HasDerivAt (fun t : ℝ ↦ 1 + t ^ 2) 0 0 := by
          simpa using (hasDerivAt_id (0 : ℝ) |>.pow 2).const_add 1
        exact (HasDerivAt.rpow_const hinner (Or.inl (by positivity : (1 : ℝ) + 0 ^ 2 ≠ 0))).congr_deriv (by simp)
      have hprod := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (he0.mul hgd))
      simpa only [hg0, mul_zero, mul_one, Real.exp_zero, Function.comp_def,
        Complex.ofRealCLM_apply, add_zero, Pi.mul_apply] using hprod.deriv
    have hp1_val : Hp1 0 = (cp : ℂ) := by simpa [Hp1, Hp, Hp_r, iteratedDeriv_one] using hd_exp_g cp
    have hm1_val : Hm1 0 = (cm : ℂ) := by simpa [Hm1, Hm, Hm_r, iteratedDeriv_one] using hd_exp_g cm
    rw [hp1_val, hm1_val]
    simp only [cp, cm, Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  refine ⟨‖Hp2 0 - Hm2 0‖ + (∫ x in Ioi (0 : ℝ), ‖Hp3 x‖) + ∫ x in Iio (0 : ℝ), ‖Hm3 x‖,
    by positivity, fun η hη ↦ ?_⟩
  have hderiv_step : ∀ (f : ℝ → ℂ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (k : ℕ) (x : ℝ),
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := by
    intro f hf k x
    rw [iteratedDeriv_succ]
    exact (hf.differentiable_iteratedDeriv k (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top k)) x).hasDerivAt
  have hibp := fourier_corner_three_ibp hη hHp_eq hHm_eq
    (hHp_cd.continuous.continuousWithinAt) (hHm_cd.continuous.continuousWithinAt)
    ((hHp_cd.continuous_iteratedDeriv 1 (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt)
    ((hHm_cd.continuous_iteratedDeriv 1 (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt)
    ((hHp_cd.continuous_iteratedDeriv 2 (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt)
    ((hHm_cd.continuous_iteratedDeriv 2 (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt)
    (fun x _ ↦ hderiv_step Hp hHp_cd 0 x)
    (fun x _ ↦ hderiv_step Hm hHm_cd 0 x)
    (fun x _ ↦ hderiv_step Hp hHp_cd 1 x)
    (fun x _ ↦ hderiv_step Hm hHm_cd 1 x)
    (fun x _ ↦ hderiv_step Hp hHp_cd 2 x)
    (fun x _ ↦ hderiv_step Hm hHm_cd 2 x)
    (by simpa [Hp, Hp_r, g] using (hHp_prop 0).2) (hHm_refl_int 0).1
    (hHp_prop 1).2 (hHm_refl_int 1).2
    (hHp_prop 2).2 (hHm_refl_int 2).2
    (hHp_prop 3).2 (hHm_refl_int 3).2
  have hgoal : -(Hp1 0 - Hm1 0) / (η : ℂ) ^ 2 = ((4 * α / η ^ 2 : ℝ) : ℂ) := by
    rw [hjump1]
    push_cast
    rfl
  rwa [hgoal] at hibp

/-- Corner Fourier lower bound: for `0 < α`, `1 < s`, and `σ ∈ [-α, α]`, for all sufficiently large `|η|`,
`2 * α / η ^ 2 ≤ ‖∫ x, (exp (σ * x) / intervalSobolevDensity (-α) α s x) * exp (-I * η * x)‖`. -/
theorem intervalSobolevDensity_inv_fourier_lower_bound {α s σ : ℝ} (hα : 0 < α) (hs : 1 < s)
    (hσ : σ ∈ Icc (-α) α) :
    ∃ M : ℝ, 0 < M ∧ ∀ η : ℝ, M ≤ |η| →
      2 * α / η ^ 2 ≤
        ‖∫ x : ℝ, ((Real.exp (σ * x) / intervalSobolevDensity (-α) α s x : ℝ) : ℂ) *
          Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))‖ := by
  obtain ⟨C, hC, hasy⟩ := intervalSobolevDensity_inv_fourier_asymptotic hα hs hσ
  refine ⟨max 1 (C / (2 * α)), by positivity, fun η hη ↦ ?_⟩
  have h1 : 1 ≤ |η| := (le_max_left _ _).trans hη
  have hη0 : η ≠ 0 := abs_pos.mp (lt_of_lt_of_le zero_lt_one h1)
  have hCη : C ≤ 2 * α * |η| := by
    have hle := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * α)).mp ((le_max_right (1 : ℝ) (C / (2 * α))).trans hη)
    linarith
  have hrem := hasy η hη0
  have hmain : ‖((4 * α / η ^ 2 : ℝ) : ℂ)‖ = 4 * α / η ^ 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have htri : 4 * α / η ^ 2 -
      ‖∫ x : ℝ, ((Real.exp (σ * x) / intervalSobolevDensity (-α) α s x : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))‖ ≤ C / |η| ^ 3 := by
    rw [← hmain]
    exact (norm_sub_norm_le _ _).trans (by rw [norm_sub_rev]; exact hrem)
  have hbound : C / |η| ^ 3 ≤ 2 * α / η ^ 2 := by
    have hη2 : |η| ^ 2 = η ^ 2 := sq_abs η
    calc C / |η| ^ 3 ≤ (2 * α * |η|) / |η| ^ 3 :=
          div_le_div_of_nonneg_right hCη (by positivity)
      _ = 2 * α / |η| ^ 2 := by
          have ha0 : |η| ≠ 0 := abs_ne_zero.mpr hη0
          field_simp [ha0]
      _ = 2 * α / η ^ 2 := by rw [hη2]
  have h42 : 4 * α / η ^ 2 - 2 * α / η ^ 2 = 2 * α / η ^ 2 := by ring
  linarith

/-- Strong-induction bound on all derivatives of `u^{(j)} / u` and `u⁻¹`. -/
theorem iteratedDeriv_inv_bounded_of_dom {u : ℝ → ℝ} (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (h1 : ∀ x : ℝ, 1 ≤ u x) (hdom : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |iteratedDeriv j u x| ≤ C * u x) :
    ∀ n : ℕ, (∀ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |iteratedDeriv n (fun t ↦ iteratedDeriv j u t / u t) x| ≤ M) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |iteratedDeriv n (fun t ↦ (u t)⁻¹) x| ≤ M := by
  have hupos (x : ℝ) : 0 < u x := lt_of_lt_of_le zero_lt_one (h1 x)
  have hu_cd : ∀ j : ℕ, ContDiff ℝ (↑(⊤ : ℕ∞)) (iteratedDeriv j u) := fun j ↦ by
    rw [iteratedDeriv_eq_iterate]
    exact hu.iterate_deriv j
  have hq_cd : ∀ j : ℕ, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t ↦ iteratedDeriv j u t / u t) := fun j ↦
    (hu_cd j).div hu fun x ↦ (hupos x).ne'
  have hi_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t ↦ (u t)⁻¹) := hu.inv fun x ↦ (hupos x).ne'
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      refine ⟨fun j ↦ ?_, ⟨1, zero_le_one, fun x ↦ ?_⟩⟩
      · obtain ⟨C, hC0, hC⟩ := hdom j
        refine ⟨C, hC0, fun x ↦ ?_⟩
        rw [iteratedDeriv_zero, abs_div, abs_of_pos (hupos x)]
        exact (div_le_iff₀ (hupos x)).mpr (hC x)
      · rw [iteratedDeriv_zero, abs_inv, abs_of_pos (hupos x)]
        exact inv_le_one_of_one_le₀ (h1 x)
    | succ m =>
      have hm_le : ∀ i ≤ m,
          (∀ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |iteratedDeriv i (fun t ↦ iteratedDeriv j u t / u t) x| ≤ M) ∧
          ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |iteratedDeriv i (fun t ↦ (u t)⁻¹) x| ≤ M :=
        fun i hi ↦ ih i (Nat.lt_succ_of_le hi)
      have hprod_bound : ∀ {f g : ℝ → ℝ}, ContDiff ℝ (↑(⊤ : ℕ∞)) f → ContDiff ℝ (↑(⊤ : ℕ∞)) g →
          (∀ i ≤ m, ∃ Mf : ℝ, 0 ≤ Mf ∧ ∀ x : ℝ, |iteratedDeriv i f x| ≤ Mf) →
          (∀ i ≤ m, ∃ Mg : ℝ, 0 ≤ Mg ∧ ∀ x : ℝ, |iteratedDeriv i g x| ≤ Mg) →
          ∃ Mp : ℝ, 0 ≤ Mp ∧ ∀ x : ℝ, |iteratedDeriv m (fun t ↦ f t * g t) x| ≤ Mp := by
        intro f g hf hg hfb hgb
        choose Mf hMf0 hMf using hfb
        choose Mg hMg0 hMg using hgb
        let bound (i : ℕ) : ℝ :=
          if hi : i ≤ m then (m.choose i : ℝ) * Mf i hi * Mg (m - i) (Nat.sub_le m i) else 0
        refine ⟨∑ i ∈ Finset.range (m + 1), bound i,
          Finset.sum_nonneg fun i _ ↦ ?_, fun x ↦ ?_⟩
        · by_cases hi : i ≤ m
          · simp only [bound, dite_eq_left, hi]
            exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hMf0 i hi)) (hMg0 _ _)
          · simp [bound, hi]
        · rw [show (fun t ↦ f t * g t) = f * g from rfl,
            iteratedDeriv_mul (hf.contDiffAt.of_le (by exact mod_cast le_top))
              (hg.contDiffAt.of_le (by exact mod_cast le_top))]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi_mem ↦ ?_)
          have hi : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi_mem)
          have hch : |(m.choose i : ℝ)| = (m.choose i : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
          simp only [bound, dite_eq_left, hi, abs_mul, hch, mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (hMf i hi x) (hMg (m - i) (Nat.sub_le m i) x) (abs_nonneg _) (hMf0 i hi))
            (Nat.cast_nonneg _)
      have hq_step : ∀ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ,
          |iteratedDeriv (m + 1) (fun t ↦ iteratedDeriv j u t / u t) x| ≤ M := by
        intro j
        have hderiv_eq : deriv (fun t ↦ iteratedDeriv j u t / u t) =
            fun t ↦ iteratedDeriv (j + 1) u t / u t -
              (iteratedDeriv j u t / u t) * (iteratedDeriv 1 u t / u t) := by
          funext t
          have hd1 : HasDerivAt (fun r ↦ iteratedDeriv j u r) (iteratedDeriv (j + 1) u t) t := by
            rw [iteratedDeriv_succ]
            exact (hu.differentiable_iteratedDeriv j
              (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top j)) t).hasDerivAt
          have hd2 : HasDerivAt u (iteratedDeriv 1 u t) t := by
            rw [iteratedDeriv_one]
            exact (hu.differentiable (by simp) t).hasDerivAt
          have hq := (hd1.div hd2 (hupos t).ne').deriv
          change deriv (fun r ↦ iteratedDeriv j u r / u r) t = _
          rw [show (fun r ↦ iteratedDeriv j u r / u r) = (fun r ↦ iteratedDeriv j u r) / u from rfl, hq]
          field_simp [(hupos t).ne']
        obtain ⟨M1, hM10, hM1⟩ := (hm_le m le_rfl).1 (j + 1)
        obtain ⟨M2, hM20, hM2⟩ := hprod_bound (hq_cd j) (hq_cd 1)
          (fun i hi ↦ (hm_le i hi).1 j) (fun i hi ↦ (hm_le i hi).1 1)
        refine ⟨M1 + M2, add_nonneg hM10 hM20, fun x ↦ ?_⟩
        rw [iteratedDeriv_succ', hderiv_eq]
        change |iteratedDeriv m ((fun t ↦ iteratedDeriv (j + 1) u t / u t) -
            fun t ↦ (iteratedDeriv j u t / u t) * (iteratedDeriv 1 u t / u t)) x| ≤ M1 + M2
        rw [iteratedDeriv_sub ((hq_cd (j + 1)).contDiffAt.of_le (by exact mod_cast le_top))
          (((hq_cd j).mul (hq_cd 1)).contDiffAt.of_le (by exact mod_cast le_top))]
        exact (abs_sub _ _).trans (add_le_add (hM1 x) (hM2 x))
      have hi_step : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |iteratedDeriv (m + 1) (fun t ↦ (u t)⁻¹) x| ≤ M := by
        have hderiv_eq : deriv (fun t ↦ (u t)⁻¹) =
            fun t ↦ -((iteratedDeriv 1 u t / u t) * (u t)⁻¹) := by
          funext t
          have hd2 : HasDerivAt u (iteratedDeriv 1 u t) t := by
            rw [iteratedDeriv_one]
            exact (hu.differentiable (by simp) t).hasDerivAt
          have hq := (hd2.inv (hupos t).ne').deriv
          change deriv (fun r ↦ (u r)⁻¹) t = _
          rw [show (fun r ↦ (u r)⁻¹) = u⁻¹ from rfl, hq]
          field_simp [(hupos t).ne']
        obtain ⟨Mp, hMp0, hMp⟩ := hprod_bound (hq_cd 1) hi_cd
          (fun i hi ↦ (hm_le i hi).1 1) (fun i hi ↦ (hm_le i hi).2)
        refine ⟨Mp, hMp0, fun x ↦ ?_⟩
        rw [iteratedDeriv_succ', hderiv_eq]
        change |iteratedDeriv m (-(fun t ↦ iteratedDeriv 1 u t / u t * (u t)⁻¹)) x| ≤ Mp
        rw [iteratedDeriv_neg, abs_neg]
        exact hMp x
      exact ⟨hq_step, hi_step⟩

/-- Under the smooth `cosh` density `2 * cosh (2 * α * x) * (1 + x ^ 2) ^ (s / 2)`, the same
Fourier integral decays faster than every power of `|η|`. -/
theorem coshSobolevDensity_inv_fourier_rapid_decay {α s σ : ℝ} (_hα : 0 ≤ α) (hs : 1 < s)
    (hσ : σ ∈ Icc (-α) α) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, η ≠ 0 →
      ‖∫ x : ℝ, ((Real.exp (σ * x) / coshSobolevDensity α s x : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))‖ ≤ C / |η| ^ N := by
  let a : ℝ := 2 * α - σ
  let b : ℝ := -(2 * α + σ)
  have ha : 0 ≤ a := by linarith [hσ.1, hσ.2]
  have hb : b ≤ 0 := by linarith [hσ.1, hσ.2]
  let u (x : ℝ) : ℝ := Real.exp (a * x) + Real.exp (b * x)
  have hu_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) u :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).add
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  have hu_ge1 : ∀ x : ℝ, 1 ≤ u x := fun x ↦ by
    rcases le_total 0 x with hx | hx
    · exact le_add_of_le_of_nonneg (Real.one_le_exp (mul_nonneg ha hx)) (Real.exp_pos _).le
    · exact le_add_of_nonneg_of_le (Real.exp_pos _).le (Real.one_le_exp (mul_nonneg_of_nonpos_of_nonpos hb hx))
  have hu_deriv : ∀ j : ℕ, ∀ x : ℝ,
      iteratedDeriv j u x = a ^ j * Real.exp (a * x) + b ^ j * Real.exp (b * x) := by
    intro j x
    have hca : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ ↦ Real.exp (a * t)) :=
      Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
    have hcb : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ ↦ Real.exp (b * t)) :=
      Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
    rw [show u = (fun t ↦ Real.exp (a * t)) + (fun t ↦ Real.exp (b * t)) from rfl,
      iteratedDeriv_add (hca.contDiffAt.of_le (by exact mod_cast le_top))
        (hcb.contDiffAt.of_le (by exact mod_cast le_top)),
      iteratedDeriv_exp_const_mul a j x, iteratedDeriv_exp_const_mul b j x]
  have hu_dom : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |iteratedDeriv j u x| ≤ C * u x := by
    intro j
    refine ⟨|a| ^ j + |b| ^ j, by positivity, fun x ↦ ?_⟩
    rw [hu_deriv j x]
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    have ha0 : 0 ≤ Real.exp (a * x) := (Real.exp_pos _).le
    have hb0 : 0 ≤ Real.exp (b * x) := (Real.exp_pos _).le
    have hab : 0 ≤ |a| ^ j * Real.exp (b * x) + |b| ^ j * Real.exp (a * x) := by positivity
    calc |a| ^ j * Real.exp (a * x) + |b| ^ j * Real.exp (b * x)
        ≤ |a| ^ j * Real.exp (a * x) + |b| ^ j * Real.exp (b * x) +
            (|a| ^ j * Real.exp (b * x) + |b| ^ j * Real.exp (a * x)) := le_add_of_nonneg_right hab
      _ = (|a| ^ j + |b| ^ j) * u x := by simp [u]; ring
  have hinv_bd : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |iteratedDeriv k (fun t ↦ (u t)⁻¹) x| ≤ M :=
    fun k ↦ (iteratedDeriv_inv_bounded_of_dom hu_cd hu_ge1 hu_dom k).2
  let g (x : ℝ) : ℝ := (1 + x ^ 2) ^ (-s / 2)
  have hbase : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ ↦ (1 : ℝ) + x ^ 2) :=
    contDiff_const.add (contDiff_id.pow 2)
  have hg_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) g :=
    hbase.rpow_const_of_ne fun x ↦ by positivity
  have huinv_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t ↦ (u t)⁻¹) :=
    hu_cd.inv fun x ↦ (lt_of_lt_of_le zero_lt_one (hu_ge1 x)).ne'
  let H_r (x : ℝ) : ℝ := (u x)⁻¹ * g x
  have hH_eq : ∀ x : ℝ, Real.exp (σ * x) / coshSobolevDensity α s x = H_r x := by
    intro x
    simp only [H_r, u, g, coshSobolevDensity]
    have hcosh : 2 * Real.cosh (2 * α * x) = Real.exp (2 * α * x) + Real.exp (-(2 * α * x)) := by
      rw [Real.cosh_eq]; ring
    have h1 : (1 + x ^ 2) ^ (-s / 2) = ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
      rw [← Real.rpow_neg (by positivity)]; congr 1; ring
    have h2 : Real.exp (σ * x) * (Real.exp (a * x) + Real.exp (b * x)) =
        2 * Real.cosh (2 * α * x) := by
      rw [hcosh, mul_add, ← Real.exp_add, ← Real.exp_add]
      congr 2 <;> [simp [a]; simp [b]] <;> ring
    rw [← h2, h1]
    field_simp [(Real.exp_pos (σ * x)).ne',
      (show 0 < Real.exp (a * x) + Real.exp (b * x) by positivity).ne',
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2) (s / 2)).ne']
  let H : ℝ → ℂ := fun x ↦ (H_r x : ℂ)
  have hH_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) H := Complex.ofRealCLM.contDiff.comp (huinv_cd.mul hg_cd)
  have hint_H : ∀ k : ℕ, Integrable (fun x : ℝ ↦ iteratedDeriv k H x) := by
    intro k
    choose Mi hMi0 hMi using fun i ↦ hinv_bd i
    choose Mg hMg0 hMg using fun i ↦ iteratedDeriv_one_add_sq_rpow_le s i
    let Ck : ℝ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Mi i * Mg (k - i)
    have hdom : ∀ x : ℝ, ‖iteratedDeriv k H x‖ ≤ Ck * g x := by
      intro x
      rw [iteratedDeriv_ofReal (huinv_cd.mul hg_cd) k x, Complex.norm_real, Real.norm_eq_abs,
        show (fun t ↦ (u t)⁻¹ * g t) = (fun t ↦ (u t)⁻¹) * g from rfl,
        iteratedDeriv_mul (huinv_cd.contDiffAt.of_le (by exact mod_cast le_top))
          (hg_cd.contDiffAt.of_le (by exact mod_cast le_top))]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hch (i : ℕ) : |(k.choose i : ℝ)| = (k.choose i : ℝ) :=
        abs_of_nonneg (Nat.cast_nonneg _)
      simp only [abs_mul, hch]
      calc (k.choose i : ℝ) * |iteratedDeriv i (fun t ↦ (u t)⁻¹) x| * |iteratedDeriv (k - i) g x|
          ≤ (k.choose i : ℝ) * Mi i * (Mg (k - i) * g x) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hMi i x) (Nat.cast_nonneg _)) (hMg (k - i) x)
              (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hMi0 i))
        _ = (k.choose i : ℝ) * Mi i * Mg (k - i) * g x := by ring
    exact ((integrable_one_add_sq_neg_rpow hs).const_mul Ck).mono'
      (hH_cd.continuous_iteratedDeriv k (by exact mod_cast le_top)).aestronglyMeasurable
      (.of_forall hdom)
  refine ⟨∫ x : ℝ, ‖iteratedDeriv N H x‖, integral_nonneg fun _ ↦ norm_nonneg _, fun η hη ↦ ?_⟩
  have heq_int : (∫ x : ℝ, ((Real.exp (σ * x) / coshSobolevDensity α s x : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ))) =
      ∫ x : ℝ, H x * Complex.exp (-Complex.I * (η : ℂ) * (x : ℂ)) :=
    integral_congr_ae (.of_forall fun x ↦ by simp only [H, hH_eq x])
  rw [heq_int]
  exact fourier_smooth_rapid_decay N H (hH_cd.of_le (by exact mod_cast le_top)) (fun k _ ↦ hint_H k) hη

end ScalarCornerTheorems

end RiemannMasullo.Isolated
