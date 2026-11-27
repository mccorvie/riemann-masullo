module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWSineIntegral
public import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.ExpDecay

/-! # The constant of the logarithm term is `π` times Euler's constant

Paper: (12.4.1.1), p. 514, the term of the real place, in the model of `Sec4_RealPWSineIntegral`
and `Sec4_RealPWUnweightedLogTerm`. A. Connes, *Trace formula in noncommutative geometry and the
zeros of the Riemann zeta function*, §VII, Theorem 4, p. 31.

`Sec4_RealPWSineIntegral` shows that `∫₀^T 2 Si(t) / t dt - π log T` converges, where `Si` is the
sine integral, and calls the limit `sincLogConstant`. The trace of the cutoff of the action of a
test function `ψ` with `ψ 1 ≠ 0` grows like `ψ 1 log (2πYL)`, and its constant term is
`ψ 1 sincLogConstant / π` plus a finite part (`Sec4_RealPWUnweightedLogTerm`). This file proves
`sincLogConstant = π γ`, with `γ` Euler's constant (`sincLogConstant_eq`), so the constant term
is `ψ 1 γ` plus the finite part.

The proof takes Abel means. For `ε > 0`, the mean `∫₀^∞ ε e^{-εT} g(T) dT` of a function with a
limit at infinity tends to that limit as `ε` decreases to zero (`tendsto_integral_abelMean`).
For `g(T) = sincMeanInt T - π log T` the mean is computed exactly.

* `integral_mul_exp_neg_mul_log`. The mean of `log T` is `-γ - log ε`. This is Mathlib's
  `γ = -∫₀^∞ log t e^{-t} dt` after the substitution `t = ε T`.
* `integral_mul_exp_neg_mul_sincMeanInt`. The mean of `sincMeanInt` is `2 ∫₀^{1/ε} arctan w / w dw`.
  Integration by parts turns it into the Laplace transform of `sincMean`. Writing `sinc` as an
  integral of cosines and using `∫₀^∞ e^{-εt} cos (a t) dt = ε / (ε² + a²)` gives the arctangent.
* `arcTanInt_sub_arcTanInt_inv`. `∫₀^R arctan w / w dw - ∫₀^{1/R} arctan w / w dw = π / 2 log R`,
  from `arctan x + arctan x⁻¹ = π / 2`.

Together the mean is `π γ + 2 ∫₀^ε arctan w / w dw`, which tends to `π γ`. Every integral in the
proof converges absolutely.

Reconstruction: The paper does not compute the constant. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set Real
open scoped ENNReal Topology

namespace RiemannMasullo.Isolated

section Elementary

/-- The Laplace transform of the cosine: `∫₀^∞ e^{-εt} cos (a t) dt = ε / (ε² + a²)`. -/
theorem integral_exp_neg_mul_cos {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    ∫ t in Ioi (0 : ℝ), exp (-(ε * t)) * cos (a * t) = ε / (ε ^ 2 + a ^ 2) := by
  let z : ℂ := ⟨-ε, a⟩
  have hz : z.re < 0 := by simpa [z] using hε
  have h := integral_exp_mul_complex_Ioi hz 0
  have hint := integrableOn_exp_mul_complex_Ioi hz 0
  have hre := integral_re hint
  rw [h] at hre
  have hpt : ∀ t : ℝ, RCLike.re (Complex.exp (z * t)) = exp (-(ε * t)) * cos (a * t) := by
    intro t
    change (Complex.exp (z * t)).re = _
    rw [Complex.exp_re]
    simp [z, Complex.mul_re, Complex.mul_im, neg_mul]
  simp only [hpt] at hre
  rw [hre]
  have hn : Complex.normSq z = ε ^ 2 + a ^ 2 := by
    simp [z, Complex.normSq_apply]
    ring
  change (-Complex.exp (z * ((0 : ℝ) : ℂ)) / z).re = _
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.div_re, hn]
  simp [z]

/-- `sinc x = ∫₀¹ cos (x u) du`. -/
theorem sinc_eq_integral_cos (x : ℝ) : sinc x = ∫ u in (0 : ℝ)..1, cos (x * u) := by
  by_cases hx : x = 0
  · simp [hx, sinc_zero]
  · rw [intervalIntegral.integral_comp_mul_left (fun u ↦ cos u) hx, integral_cos, mul_zero,
      mul_one, sin_zero, sub_zero, sinc_of_ne_zero hx, smul_eq_mul, div_eq_inv_mul]

/-- `∫₀¹ ε / (ε² + (s u)²) du = arctan (s / ε) / s` for `s ≠ 0`. -/
theorem integral_div_sq_add_sq {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : s ≠ 0) :
    ∫ u in (0 : ℝ)..1, ε / (ε ^ 2 + (s * u) ^ 2) = arctan (s / ε) / s := by
  have hc : s / ε ≠ 0 := div_ne_zero hs hε.ne'
  have hpt : ∀ u : ℝ, ε / (ε ^ 2 + (s * u) ^ 2) = ε⁻¹ * (1 / (1 + ((s / ε) * u) ^ 2)) := by
    intro u
    field_simp
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun v ↦ 1 / (1 + v ^ 2)) hc,
    integral_one_div_one_add_sq, mul_zero, mul_one, arctan_zero, sub_zero, smul_eq_mul]
  field_simp

/-- The function `w ↦ arctan w / w`, bounded by one. -/
theorem abs_arctan_div_le_one (w : ℝ) : |arctan w / w| ≤ 1 := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · rw [abs_div, div_le_one (abs_pos.mpr hw)]
    exact abs_arctan_le_abs

theorem measurable_arctan_div : Measurable fun w : ℝ ↦ arctan w / w :=
  continuous_arctan.measurable.div measurable_id

theorem intervalIntegrable_arctan_div (a b : ℝ) :
    IntervalIntegrable (fun w : ℝ ↦ arctan w / w) volume a b :=
  (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    measurable_arctan_div.aestronglyMeasurable
    (ae_of_all _ fun w ↦ by
      change ‖arctan w / w‖ ≤ 1
      rw [Real.norm_eq_abs]
      exact abs_arctan_div_le_one w)

/-- `arcTanInt R = ∫₀^R arctan w / w dw`. -/
def arcTanInt (R : ℝ) : ℝ := ∫ w in (0 : ℝ)..R, arctan w / w

theorem abs_arcTanInt_le (R : ℝ) : |arcTanInt R| ≤ |R| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := R)
    (f := fun w : ℝ ↦ arctan w / w) (C := 1)
    (fun w _ ↦ by rw [Real.norm_eq_abs]; exact abs_arctan_div_le_one w)
  rw [Real.norm_eq_abs, sub_zero, one_mul] at h
  exact h

/-- The inversion identity: `arcTanInt R - arcTanInt R⁻¹ = π / 2 * log R` for `R > 0`. It
comes from `arctan x + arctan x⁻¹ = π / 2` and the substitution `w = x⁻¹`. -/
theorem arcTanInt_sub_arcTanInt_inv {R : ℝ} (hR : 0 < R) :
    arcTanInt R - arcTanInt R⁻¹ = π / 2 * log R := by
  have hpos : ∀ x ∈ uIcc (1 : ℝ) R, 0 < x := fun x hx ↦
    lt_of_lt_of_le (lt_min one_pos hR) hx.1
  have hsub : ∫ x in (1 : ℝ)..R, (fun w : ℝ ↦ arctan w / w) (x⁻¹) * (-(x ^ 2)⁻¹) =
      ∫ w in (1 : ℝ)⁻¹..R⁻¹, arctan w / w := by
    refine intervalIntegral.integral_comp_mul_deriv' (f := fun x : ℝ ↦ x⁻¹)
      (g := fun w : ℝ ↦ arctan w / w)
      (fun x hx ↦ hasDerivAt_inv (hpos x hx).ne')
      (fun x hx ↦ ((continuous_pow 2).continuousAt.inv₀
        (pow_ne_zero 2 (hpos x hx).ne')).neg.continuousWithinAt) ?_
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hw
    have hx0 : x⁻¹ ≠ 0 := inv_ne_zero (hpos x hx).ne'
    exact (continuous_arctan.continuousAt.div continuousAt_id hx0).continuousWithinAt
  rw [inv_one] at hsub
  have hcongr : ∫ x in (1 : ℝ)..R, (fun w : ℝ ↦ arctan w / w) (x⁻¹) * (-(x ^ 2)⁻¹) =
      ∫ x in (1 : ℝ)..R, -(arctan x⁻¹ / x) := by
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    have hx0 : x ≠ 0 := (hpos x hx).ne'
    field_simp
  have hsum : ∫ x in (1 : ℝ)..R, (arctan x / x + arctan x⁻¹ / x) =
      ∫ x in (1 : ℝ)..R, π / 2 * x⁻¹ := by
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [arctan_inv_of_pos (hpos x hx)]
    field_simp
    ring
  have hI : ∀ a b : ℝ, IntervalIntegrable (fun w : ℝ ↦ arctan w / w) volume a b :=
    intervalIntegrable_arctan_div
  have hI' : IntervalIntegrable (fun x : ℝ ↦ arctan x⁻¹ / x) volume 1 R := by
    refine ContinuousOn.intervalIntegrable fun x hx ↦ ?_
    have hx0 : x ≠ 0 := (hpos x hx).ne'
    exact ((continuous_arctan.continuousAt.comp (continuousAt_inv₀ hx0)).div continuousAt_id
      hx0).continuousWithinAt
  rw [intervalIntegral.integral_add (hI 1 R) hI', intervalIntegral.integral_const_mul,
    integral_inv_of_pos one_pos hR, div_one] at hsum
  rw [hcongr, intervalIntegral.integral_neg] at hsub
  unfold arcTanInt
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI 0 1) (hI 1 R),
    ← intervalIntegral.integral_add_adjacent_intervals (hI 0 1) (hI 1 R⁻¹), ← hsum,
    ← hsub]
  ring

end Elementary

section Laplace

/-- The Laplace transform of a dilated `sinc`:
`∫₀^∞ e^{-εt} sinc (t s) dt = ∫₀¹ ε / (ε² + (s u)²) du`. -/
theorem integral_exp_neg_mul_sinc {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    ∫ t in Ioi (0 : ℝ), exp (-(ε * t)) * sinc (t * s) =
      ∫ u in (0 : ℝ)..1, ε / (ε ^ 2 + (s * u) ^ 2) := by
  let f : ℝ → ℝ → ℝ := fun t u ↦ exp (-(ε * t)) * cos (s * u * t)
  have hexp : IntegrableOn (fun t : ℝ ↦ exp (-(ε * t))) (Ioi 0) := by
    have h := exp_neg_integrableOn_Ioi 0 hε
    simpa only [neg_mul] using h
  have hf : Integrable (Function.uncurry f)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    have hprod := hexp.mul_prod (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) 1)
      (C := (1 : ℝ)) (by simp))
    refine hprod.mono' ?_ (ae_of_all _ fun q ↦ ?_)
    · exact (((continuous_exp.comp (continuous_const.mul continuous_fst).neg).mul
        (continuous_cos.comp ((continuous_const.mul continuous_snd).mul
          continuous_fst)))).aestronglyMeasurable
    · change ‖exp (-(ε * q.1)) * cos (s * q.2 * q.1)‖ ≤ exp (-(ε * q.1)) * 1
      rw [norm_mul, Real.norm_of_nonneg (exp_pos _).le]
      exact mul_le_mul_of_nonneg_left (by simpa using abs_cos_le_one _) (exp_pos _).le
  have h1 : ∀ t : ℝ, exp (-(ε * t)) * sinc (t * s) = ∫ u in Ioc (0 : ℝ) 1, f t u := by
    intro t
    rw [sinc_eq_integral_cos, intervalIntegral.integral_of_le zero_le_one,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ ↦ ?_
    change exp (-(ε * t)) * cos (t * s * u) = exp (-(ε * t)) * cos (s * u * t)
    ring_nf
  have h2 : ∀ u : ℝ, ∫ t in Ioi (0 : ℝ), f t u = ε / (ε ^ 2 + (s * u) ^ 2) :=
    fun u ↦ integral_exp_neg_mul_cos hε (s * u)
  rw [intervalIntegral.integral_of_le zero_le_one, integral_congr_ae (ae_of_all _ h1),
    integral_integral_swap hf]
  exact integral_congr_ae (ae_of_all _ h2)

/-- The Laplace transform of `sincMean` as a double integral. -/
theorem integral_exp_neg_mul_sincMean {ε : ℝ} (hε : 0 < ε) :
    ∫ t in Ioi (0 : ℝ), exp (-(ε * t)) * sincMean t =
      ∫ s in Ioc (-1 : ℝ) 1, ∫ u in (0 : ℝ)..1, ε / (ε ^ 2 + (s * u) ^ 2) := by
  let f : ℝ → ℝ → ℝ := fun t s ↦ exp (-(ε * t)) * sinc (t * s)
  have hexp : IntegrableOn (fun t : ℝ ↦ exp (-(ε * t))) (Ioi 0) := by
    have h := exp_neg_integrableOn_Ioi 0 hε
    simpa only [neg_mul] using h
  have hf : Integrable (Function.uncurry f)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (-1 : ℝ) 1))) := by
    have hprod := hexp.mul_prod (integrableOn_const (μ := volume) (s := Ioc (-1 : ℝ) 1)
      (C := (1 : ℝ)) (by simp))
    refine hprod.mono' ?_ (ae_of_all _ fun q ↦ ?_)
    · exact ((continuous_exp.comp (continuous_const.mul continuous_fst).neg).mul
        (continuous_sinc.comp (continuous_fst.mul continuous_snd))).aestronglyMeasurable
    · change ‖exp (-(ε * q.1)) * sinc (q.1 * q.2)‖ ≤ exp (-(ε * q.1)) * 1
      rw [norm_mul, Real.norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (abs_sinc_le_one _) (exp_pos _).le
  have h1 : ∀ t : ℝ, exp (-(ε * t)) * sincMean t = ∫ s in Ioc (-1 : ℝ) 1, f t s := by
    intro t
    rw [sincMean, intervalIntegral.integral_of_le (by norm_num), ← integral_const_mul]
  rw [integral_congr_ae (ae_of_all _ h1), integral_integral_swap hf]
  exact integral_congr_ae (ae_of_all _ fun s ↦ integral_exp_neg_mul_sinc hε s)

/-- The Laplace transform of `sincMean` is `2 arcTanInt ε⁻¹`. -/
theorem integral_exp_neg_mul_sincMean_eq {ε : ℝ} (hε : 0 < ε) :
    ∫ t in Ioi (0 : ℝ), exp (-(ε * t)) * sincMean t = 2 * arcTanInt ε⁻¹ := by
  rw [integral_exp_neg_mul_sincMean hε]
  let k : ℝ → ℝ := fun s ↦ arctan (s / ε) / s
  have hne : ∀ᵐ s ∂(volume.restrict (Ioc (-1 : ℝ) 1)),
      ∫ u in (0 : ℝ)..1, ε / (ε ^ 2 + (s * u) ^ 2) = k s := by
    have h0 : ({0}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) :=
      compl_mem_ae_iff.mpr (measure_singleton 0)
    filter_upwards [ae_restrict_of_ae h0] with s hs
    exact integral_div_sq_add_sq hε hs
  rw [integral_congr_ae hne, ← intervalIntegral.integral_of_le (by norm_num)]
  have hk : ∀ s : ℝ, k s = ε⁻¹ * (arctan (ε⁻¹ * s) / (ε⁻¹ * s)) := by
    intro s
    change arctan (s / ε) / s = _
    rcases eq_or_ne s 0 with rfl | hs
    · simp
    · rw [div_eq_inv_mul s ε]
      field_simp
  have hkI : ∀ a b : ℝ, IntervalIntegrable k volume a b := by
    intro a b
    refine (intervalIntegrable_const (c := ε⁻¹)).mono_fun'
      ((continuous_arctan.measurable.comp (measurable_id.div_const ε)).div
        measurable_id).aestronglyMeasurable (ae_of_all _ fun s ↦ ?_)
    change ‖k s‖ ≤ ε⁻¹
    rw [hk, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le), Real.norm_eq_abs]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hε.le) (abs_arctan_div_le_one _)
  have heven : ∫ s in (-1 : ℝ)..0, k s = ∫ s in (0 : ℝ)..1, k s := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := 1) k
    rw [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun s _ ↦ ?_
    change arctan (-s / ε) / -s = arctan (s / ε) / s
    rw [neg_div, arctan_neg, neg_div_neg_eq]
  have hhalf : ∫ s in (0 : ℝ)..1, k s = arcTanInt ε⁻¹ := by
    simp_rw [hk]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun w ↦ arctan w / w) (inv_ne_zero hε.ne'),
      mul_zero, mul_one, inv_inv, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
    rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals (hkI (-1) 0) (hkI 0 1), heven, hhalf]
  ring

end Laplace

section Abel

theorem integrableOn_exp_neg_mul {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ ↦ exp (-(ε * t))) (Ioi 0) := by
  have h := exp_neg_integrableOn_Ioi 0 hε
  simpa only [neg_mul] using h

theorem integral_mul_exp_neg_mul {ε : ℝ} (hε : 0 < ε) :
    ∫ t in Ioi (0 : ℝ), ε * exp (-(ε * t)) = 1 := by
  rw [integral_const_mul, integral_comp_mul_left_Ioi (fun u ↦ exp (-u)) 0 hε, mul_zero,
    integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one, mul_inv_cancel₀ hε.ne']

/-- Reconstruction: the Abel mean of a function with a limit at infinity has the same limit. If
`g` is measurable, integrable on every `(0, T]` and tends to `C`, then
`∫₀^∞ ε e^{-εT} g(T) dT` tends to `C` as `ε` decreases to zero. -/
theorem tendsto_integral_abelMean {g : ℝ → ℝ} {C : ℝ} (hm : Measurable g)
    (hloc : ∀ T, 0 ≤ T → IntegrableOn g (Ioc 0 T)) (hlim : Tendsto g atTop (𝓝 C)) :
    Tendsto (fun ε ↦ ∫ T in Ioi (0 : ℝ), ε * exp (-(ε * T)) * g T) (𝓝[>] 0) (𝓝 C) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (η / 2) (half_pos hη)
  set T₀ := max N 1 with hT₀def
  have hT₀ : 0 ≤ T₀ := zero_le_one.trans (le_max_right _ _)
  have hgC : IntegrableOn (fun T ↦ |g T - C|) (Ioc 0 T₀) :=
    ((hloc T₀ hT₀).sub (integrableOn_const (μ := volume) (by simp))).abs
  set K := ∫ T in Ioc 0 T₀, |g T - C| with hKdef
  have hK : 0 ≤ K := integral_nonneg fun _ ↦ abs_nonneg _
  refine ⟨η / (2 * (K + 1)), by positivity, fun {ε} hε hεd ↦ ?_⟩
  have hε0 : 0 < ε := hε
  rw [dist_zero_right, Real.norm_of_nonneg hε0.le] at hεd
  have hfar : ∀ T ∈ Ioi T₀, |g T - C| ≤ η / 2 := fun T hT ↦
    (hN T ((le_max_left _ _).trans (le_of_lt hT))).le
  have hker : IntegrableOn (fun T : ℝ ↦ ε * exp (-(ε * T))) (Ioi 0) :=
    (integrableOn_exp_neg_mul hε0).const_mul ε
  let h : ℝ → ℝ := fun T ↦ ε * exp (-(ε * T)) * (g T - C)
  have hmeas : AEStronglyMeasurable h (volume.restrict (Ioi 0)) :=
    (((continuous_const.mul (continuous_exp.comp (continuous_const.mul
      continuous_id).neg)).measurable).mul (hm.sub_const C)).aestronglyMeasurable
  have hnear : IntegrableOn h (Ioc 0 T₀) := by
    refine (hgC.const_mul ε).mono' (hmeas.mono_set Ioc_subset_Ioi_self)
      ((ae_restrict_mem measurableSet_Ioc).mono fun T hT ↦ ?_)
    change ‖ε * exp (-(ε * T)) * (g T - C)‖ ≤ ε * |g T - C|
    rw [norm_mul, norm_mul, Real.norm_of_nonneg hε0.le, Real.norm_of_nonneg (exp_pos _).le,
      Real.norm_eq_abs]
    have he : exp (-(ε * T)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [hT.1])
    calc ε * exp (-(ε * T)) * |g T - C| = ε * (exp (-(ε * T)) * |g T - C|) := by ring
      _ ≤ ε * (1 * |g T - C|) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right he (abs_nonneg _)) hε0.le
      _ = ε * |g T - C| := by ring
  have hfarI : IntegrableOn h (Ioi T₀) := by
    refine ((hker.mono_set (Ioi_subset_Ioi hT₀)).mul_const (η / 2)).mono'
      (hmeas.mono_set (Ioi_subset_Ioi hT₀))
      ((ae_restrict_mem measurableSet_Ioi).mono fun T hT ↦ ?_)
    change ‖ε * exp (-(ε * T)) * (g T - C)‖ ≤ ε * exp (-(ε * T)) * (η / 2)
    rw [norm_mul, norm_mul, Real.norm_of_nonneg hε0.le, Real.norm_of_nonneg (exp_pos _).le,
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hfar T hT) (by positivity)
  have hunion : Ioc 0 T₀ ∪ Ioi T₀ = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi hT₀
  have hI : IntegrableOn h (Ioi 0) := by
    rw [← hunion]
    exact hnear.union hfarI
  have hGI : IntegrableOn (fun T ↦ ε * exp (-(ε * T)) * g T) (Ioi 0) := by
    refine (hI.add (hker.mul_const C)).congr_fun (fun T _ ↦ ?_) measurableSet_Ioi
    change ε * exp (-(ε * T)) * (g T - C) + ε * exp (-(ε * T)) * C = _
    ring
  have hdiff : (∫ T in Ioi (0 : ℝ), ε * exp (-(ε * T)) * g T) - C =
      ∫ T in Ioi (0 : ℝ), h T := by
    have h1 : ∫ T in Ioi (0 : ℝ), h T = (∫ T in Ioi (0 : ℝ), ε * exp (-(ε * T)) * g T) -
        ∫ T in Ioi (0 : ℝ), ε * exp (-(ε * T)) * C := by
      rw [← integral_sub hGI (hker.mul_const C)]
      refine integral_congr_ae (ae_of_all _ fun T ↦ ?_)
      change ε * exp (-(ε * T)) * (g T - C) = _
      ring
    rw [h1, integral_mul_const, integral_mul_exp_neg_mul hε0, one_mul]
  have hsplit : ∫ T in Ioi (0 : ℝ), h T =
      (∫ T in Ioc 0 T₀, h T) + ∫ T in Ioi T₀, h T := by
    rw [← hunion, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hnear hfarI]
  have hb1 : |∫ T in Ioc 0 T₀, h T| ≤ ε * K := by
    rw [hKdef, ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on hnear.abs
      (hgC.const_mul ε) measurableSet_Ioc fun T hT ↦ ?_)
    change |ε * exp (-(ε * T)) * (g T - C)| ≤ ε * |g T - C|
    rw [abs_mul, abs_mul, abs_of_pos hε0, abs_of_pos (exp_pos _)]
    have he : exp (-(ε * T)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [hT.1])
    calc ε * exp (-(ε * T)) * |g T - C| = ε * (exp (-(ε * T)) * |g T - C|) := by ring
      _ ≤ ε * (1 * |g T - C|) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right he (abs_nonneg _)) hε0.le
      _ = ε * |g T - C| := by ring
  have hb2 : |∫ T in Ioi T₀, h T| ≤ η / 2 := by
    have hmono : ∫ T in Ioi T₀, ε * exp (-(ε * T)) ≤ 1 := by
      rw [← integral_mul_exp_neg_mul hε0]
      exact setIntegral_mono_set hker (ae_of_all _ fun T ↦ by positivity)
        (ae_of_all _ (Ioi_subset_Ioi hT₀))
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ T in Ioi T₀, |h T| ≤ ∫ T in Ioi T₀, ε * exp (-(ε * T)) * (η / 2) := by
          refine setIntegral_mono_on hfarI.abs
            ((hker.mono_set (Ioi_subset_Ioi hT₀)).mul_const _) measurableSet_Ioi fun T hT ↦ ?_
          change |ε * exp (-(ε * T)) * (g T - C)| ≤ _
          rw [abs_mul, abs_mul, abs_of_pos hε0, abs_of_pos (exp_pos _)]
          exact mul_le_mul_of_nonneg_left (hfar T hT) (by positivity)
      _ = (∫ T in Ioi T₀, ε * exp (-(ε * T))) * (η / 2) := integral_mul_const _ _
      _ ≤ 1 * (η / 2) := mul_le_mul_of_nonneg_right hmono (by positivity)
      _ = η / 2 := one_mul _
  rw [Real.dist_eq, hdiff, hsplit]
  have hεK : ε * K < η / 2 := by
    have h1 : ε * K ≤ η / (2 * (K + 1)) * K := mul_le_mul_of_nonneg_right hεd.le hK
    have h2 : η / (2 * (K + 1)) * K < η / 2 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    exact lt_of_le_of_lt h1 h2
  calc |(∫ T in Ioc 0 T₀, h T) + ∫ T in Ioi T₀, h T|
      ≤ |∫ T in Ioc 0 T₀, h T| + |∫ T in Ioi T₀, h T| := abs_add_le _ _
    _ < η := by linarith

end Abel

section Constant

/-- `log t e^{-t}` is integrable on the positive half-line. -/
theorem integrableOn_log_mul_exp_neg : IntegrableOn (fun t : ℝ ↦ log t * exp (-t)) (Ioi 0) := by
  refine Integrable.mono' (g := fun x ↦ (2 * x ^ (-(1 : ℝ) / 2) + x) * exp (-1 * x)) ?_ ?_ ?_
  · simp only [add_mul, mul_assoc]
    refine (Integrable.const_mul ?_ _).add ?_
    · simpa [IntegrableOn] using integrableOn_rpow_mul_exp_neg_mul_rpow
        (by norm_num : -1 < (-1 : ℝ) / 2) one_pos one_pos
    · simpa [IntegrableOn] using integrableOn_rpow_mul_exp_neg_mul_rpow
        (by norm_num : -1 < (1 : ℝ)) one_pos one_pos
  · exact (measurable_log.mul (continuous_exp.comp continuous_neg).measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (exp_pos _).le, neg_one_mul]
    refine mul_le_mul_of_nonneg_right ?_ (exp_pos _).le
    have h1 := neg_rpow_div_le_log hx.le one_half_pos
    have h2 := log_le_self hx.le
    have h3 : 0 ≤ x ^ (-(1 : ℝ) / 2) := rpow_nonneg hx.le _
    have h4 : -x ^ (-(1 / 2 : ℝ)) / (1 / 2) = -(2 * x ^ (-(1 : ℝ) / 2)) := by
      rw [show (-(1 / 2 : ℝ)) = -(1 : ℝ) / 2 by norm_num]
      ring
    rw [h4] at h1
    rw [abs_le]
    constructor <;> linarith

/-- `∫₀^∞ ε e^{-εT} log T dT = -γ - log ε`, from `γ = -∫₀^∞ log t e^{-t} dt`. -/
theorem integral_mul_exp_neg_mul_log {ε : ℝ} (hε : 0 < ε) :
    ∫ T in Ioi (0 : ℝ), ε * exp (-(ε * T)) * log T =
      -eulerMascheroniConstant - log ε := by
  let φ : ℝ → ℝ := fun u ↦ log u * exp (-u) - log ε * exp (-u)
  have hφI : IntegrableOn φ (Ioi 0) :=
    integrableOn_log_mul_exp_neg.sub ((integrableOn_exp_neg_Ioi 0).const_mul (log ε))
  have hpt : ∀ T ∈ Ioi (0 : ℝ), ε * exp (-(ε * T)) * log T = ε * φ (ε * T) := by
    intro T hT
    change _ = ε * (log (ε * T) * exp (-(ε * T)) - log ε * exp (-(ε * T)))
    rw [log_mul hε.ne' (ne_of_gt hT)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_comp_mul_left_Ioi φ 0 hε, mul_zero, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hε.ne', one_mul, integral_sub integrableOn_log_mul_exp_neg
      ((integrableOn_exp_neg_Ioi 0).const_mul (log ε)), integral_const_mul,
    integral_exp_neg_Ioi_zero, mul_one, eulerMascheroniConstant_eq_neg_integral_log, neg_neg]

theorem integrableOn_mul_exp_neg_mul_log {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun T : ℝ ↦ ε * exp (-(ε * T)) * log T) (Ioi 0) := by
  let φ : ℝ → ℝ := fun u ↦ log u * exp (-u) - log ε * exp (-u)
  have hφI : IntegrableOn φ (Ioi (ε * 0)) := by
    rw [mul_zero]
    exact integrableOn_log_mul_exp_neg.sub ((integrableOn_exp_neg_Ioi 0).const_mul (log ε))
  have h : IntegrableOn (fun T : ℝ ↦ ε * φ (ε * T)) (Ioi 0) :=
    ((integrableOn_Ioi_comp_mul_left_iff φ 0 hε).mpr hφI).const_mul ε
  refine h.congr_fun (fun T hT ↦ ?_) measurableSet_Ioi
  change ε * (log (ε * T) * exp (-(ε * T)) - log ε * exp (-(ε * T))) = _
  rw [log_mul hε.ne' (ne_of_gt hT)]
  ring

theorem abs_sincMean_le_two (t : ℝ) : |sincMean t| ≤ 2 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -1) (b := 1)
    (f := fun s : ℝ ↦ sinc (t * s)) (C := 1)
    (fun s _ ↦ by rw [Real.norm_eq_abs]; exact abs_sinc_le_one _)
  rw [Real.norm_eq_abs] at h
  unfold sincMean
  convert h using 1
  norm_num

theorem hasDerivAt_sincMeanInt (T : ℝ) : HasDerivAt sincMeanInt (sincMean T) T :=
  (continuous_sincMean.integral_hasStrictDerivAt 0 T).hasDerivAt

theorem continuous_sincMeanInt : Continuous sincMeanInt :=
  continuous_iff_continuousAt.mpr fun T ↦ (hasDerivAt_sincMeanInt T).continuousAt

theorem abs_sincMeanInt_le {T : ℝ} (hT : 0 ≤ T) : |sincMeanInt T| ≤ 2 * T := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T)
    (f := sincMean) (C := 2) (fun t _ ↦ by rw [Real.norm_eq_abs]; exact abs_sincMean_le_two t)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT] at h
  exact h

/-- The Abel weight times `sincMeanInt` is integrable, since `|sincMeanInt T| ≤ 2 T`. -/
theorem integrableOn_mul_exp_neg_mul_sincMeanInt {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun T : ℝ ↦ ε * exp (-(ε * T)) * sincMeanInt T) (Ioi 0) := by
  have hpow : IntegrableOn (fun T : ℝ ↦ T * exp (-(ε * T))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num : -1 < (1 : ℝ)) one_pos hε
    refine h.congr_fun (fun T _ ↦ ?_) measurableSet_Ioi
    simp [rpow_one, neg_mul]
  refine (hpow.const_mul (2 * ε)).mono' ((continuous_const.mul (continuous_exp.comp
    (continuous_const.mul continuous_id).neg)).mul
      continuous_sincMeanInt).aestronglyMeasurable
    ((ae_restrict_mem measurableSet_Ioi).mono fun T (hT : 0 < T) ↦ ?_)
  rw [norm_mul, norm_mul, Real.norm_of_nonneg hε.le, Real.norm_of_nonneg (exp_pos _).le,
    Real.norm_eq_abs]
  have h := abs_sincMeanInt_le hT.le
  have he := (exp_pos (-(ε * T))).le
  calc ε * exp (-(ε * T)) * |sincMeanInt T| ≤ ε * exp (-(ε * T)) * (2 * T) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * ε * (T * exp (-(ε * T))) := by ring

/-- `∫₀^∞ ε e^{-εT} sincMeanInt T dT = 2 arcTanInt ε⁻¹`: integration by parts and
`integral_exp_neg_mul_sincMean_eq`. -/
theorem integral_mul_exp_neg_mul_sincMeanInt {ε : ℝ} (hε : 0 < ε) :
    ∫ T in Ioi (0 : ℝ), ε * exp (-(ε * T)) * sincMeanInt T = 2 * arcTanInt ε⁻¹ := by
  have hexp := integrableOn_exp_neg_mul hε
  have hA := integrableOn_mul_exp_neg_mul_sincMeanInt hε
  have hB : IntegrableOn (fun T : ℝ ↦ exp (-(ε * T)) * sincMean T) (Ioi 0) := by
    refine (hexp.const_mul 2).mono' ((continuous_exp.comp (continuous_const.mul
      continuous_id).neg).mul continuous_sincMean).aestronglyMeasurable (ae_of_all _ fun T ↦ ?_)
    rw [norm_mul, Real.norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_sincMean_le_two T) (exp_pos _).le
  let f : ℝ → ℝ := fun T ↦ -(exp (-(ε * T)) * sincMeanInt T)
  have hderiv : ∀ T : ℝ, HasDerivAt f
      (ε * exp (-(ε * T)) * sincMeanInt T - exp (-(ε * T)) * sincMean T) T := by
    intro T
    have h1 : HasDerivAt (fun T : ℝ ↦ exp (-(ε * T))) (exp (-(ε * T)) * -ε) T := by
      have h := ((hasDerivAt_id T).const_mul ε).neg.exp
      simpa using h
    have h2 := (h1.mul (hasDerivAt_sincMeanInt T)).neg
    convert h2 using 1
    ring
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h0 : Tendsto (fun T : ℝ ↦ (ε * T) ^ 1 * exp (-(ε * T))) atTop (𝓝 0) :=
      (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_id.const_mul_atTop hε)
    have h1 : Tendsto (fun T : ℝ ↦ 2 * ε⁻¹ * ((ε * T) ^ 1 * exp (-(ε * T)))) atTop (𝓝 0) := by
      simpa using h0.const_mul (2 * ε⁻¹)
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    change ‖-(exp (-(ε * T)) * sincMeanInt T)‖ ≤ _
    rw [norm_neg, norm_mul, Real.norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs, pow_one]
    have h := abs_sincMeanInt_le hT
    calc exp (-(ε * T)) * |sincMeanInt T| ≤ exp (-(ε * T)) * (2 * T) :=
          mul_le_mul_of_nonneg_left h (exp_pos _).le
      _ = 2 * ε⁻¹ * (ε * T * exp (-(ε * T))) := by
          field_simp
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (hderiv 0).continuousAt.continuousWithinAt (fun T _ ↦ hderiv T) (hA.sub hB) hlim
  have hf0 : f 0 = 0 := by
    change -(exp (-(ε * 0)) * sincMeanInt 0) = 0
    simp [sincMeanInt]
  rw [hf0, sub_zero, integral_sub hA hB, sub_eq_zero] at hFTC
  rw [hFTC, integral_exp_neg_mul_sincMean_eq hε]

/-- Paper: (12.4.1.1), p. 514, the constant of the real place, and A. Connes, *Trace formula in
noncommutative geometry and the zeros of the Riemann zeta function*, §VII, Theorem 4, p. 31.
The constant of the logarithm term is `π` times Euler's constant:
`∫₀^T 2 Si(t) / t dt - π log T → π γ`.
Reconstruction: The paper does not compute it. The proof takes Abel means: for `ε > 0` the mean
`∫₀^∞ ε e^{-εT} (sincMeanInt T - π log T) dT` equals `π γ + 2 ∫₀^ε arctan w / w dw`, and it
tends to `sincLogConstant` as `ε` decreases to zero. -/
theorem sincLogConstant_eq : sincLogConstant = π * eulerMascheroniConstant := by
  let g : ℝ → ℝ := fun T ↦ sincMeanInt T - π * log T
  have hm : Measurable g := continuous_sincMeanInt.measurable.sub
    (measurable_const.mul measurable_log)
  have hloc : ∀ T, 0 ≤ T → IntegrableOn g (Ioc 0 T) := by
    intro T hT
    exact continuous_sincMeanInt.integrableOn_Ioc.sub
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
        intervalIntegral.intervalIntegrable_log').const_mul π)
  have h1 := tendsto_integral_abelMean hm hloc tendsto_sincMeanInt_sub_log
  have hformula : ∀ ε : ℝ, 0 < ε → ∫ T in Ioi (0 : ℝ), ε * exp (-(ε * T)) * g T =
      π * eulerMascheroniConstant + 2 * arcTanInt ε := by
    intro ε hε
    have hA := integrableOn_mul_exp_neg_mul_sincMeanInt hε
    have hsplit : ∫ T in Ioi (0 : ℝ), ε * exp (-(ε * T)) * g T =
        (∫ T in Ioi (0 : ℝ), ε * exp (-(ε * T)) * sincMeanInt T) -
          π * ∫ T in Ioi (0 : ℝ), ε * exp (-(ε * T)) * log T := by
      rw [← integral_const_mul, ← integral_sub hA
        ((integrableOn_mul_exp_neg_mul_log hε).const_mul π)]
      refine integral_congr_ae (ae_of_all _ fun T ↦ ?_)
      change ε * exp (-(ε * T)) * (sincMeanInt T - π * log T) = _
      ring
    have hinv := arcTanInt_sub_arcTanInt_inv (inv_pos.mpr hε)
    rw [inv_inv, log_inv] at hinv
    rw [hsplit, integral_mul_exp_neg_mul_sincMeanInt hε, integral_mul_exp_neg_mul_log hε]
    linarith
  have h2 : Tendsto (fun ε ↦ ∫ T in Ioi (0 : ℝ), ε * exp (-(ε * T)) * g T) (𝓝[>] 0)
      (𝓝 (π * eulerMascheroniConstant)) := by
    have harc : Tendsto arcTanInt (𝓝[>] 0) (𝓝 0) := by
      have habs : Tendsto (fun ε : ℝ ↦ |ε|) (𝓝[>] 0) (𝓝 0) := by
        have h := (continuous_abs.tendsto (0 : ℝ))
        rw [abs_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      exact squeeze_zero_norm (fun ε ↦ by
        rw [Real.norm_eq_abs]; exact abs_arcTanInt_le ε) habs
    have h3 := (harc.const_mul 2).const_add (π * eulerMascheroniConstant)
    rw [mul_zero, add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (hformula ε hε).symm
  exact tendsto_nhds_unique h1 h2

/-- The constant `sincLogConstant / π` of the logarithm term is Euler's constant. -/
theorem sincLogConstant_div_pi : sincLogConstant / π = eulerMascheroniConstant := by
  rw [sincLogConstant_eq, mul_div_cancel_left₀ _ pi_ne_zero]

end Constant

end RiemannMasullo.Isolated
