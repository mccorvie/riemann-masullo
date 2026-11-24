module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Powers of a fixed theta approximation on the negative half-line

The indicator in the one-target criterion for Theorem 12.5.1.1, pp. 519–520, is
`exp(x/2)` on nonpositive log norm. For a nonzero Schwartz profile supported there,
divide its Fourier transform by that of the indicator. The weighted squared error of
the powers of the resulting residual grows exponentially. This rules out this
specific geometric iteration of a single supported smooth approximation.
-/

open Set Filter Function MeasureTheory
open scoped FourierTransform SchwartzMap Topology LineDeriv InnerProductSpace

public noncomputable section
namespace RiemannMasullo

private theorem thetaPower_fourier_mean (g : 𝓢(ℝ, ℂ)) : ∫ t : ℝ, (𝓕 g) t = g 0 := by
  have h := congrArg (fun f : 𝓢(ℝ, ℂ) ↦ f 0) (FourierTransform.fourierInv_fourier_eq (F := 𝓢(ℝ, ℂ)) g)
  change (𝓕⁻ (𝓕 g)) (0 : ℝ) = g 0 at h
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg] at h
  simpa [Real.fourier_real_eq] using h

private theorem thetaPower_exists_frequency (g : 𝓢(ℝ, ℂ)) (h0 : g 0 = 0) (hg : g ≠ 0) :
    ∃ t : ℝ, 1 < ‖1 - (𝓕 g) t‖ := by
  let G := 𝓕 g
  by_contra! h
  have hbd (t : ℝ) : ‖G t‖ ^ 2 ≤ 2 * (G t).re := by
    have hl := pow_le_pow_left₀ (norm_nonneg _) (h t) 2
    rw [@norm_sub_sq ℂ, RCLike.inner_apply] at hl
    simp only [norm_one, one_pow, map_one, mul_one, RCLike.re_to_complex] at hl
    change ‖(𝓕 g) t‖ ^ 2 ≤ 2 * ((𝓕 g) t).re
    linarith
  have hpos (t : ℝ) : 0 ≤ (G t).re := by linarith [hbd t, sq_nonneg ‖G t‖]
  have hi : Integrable (fun t : ℝ ↦ (G t).re) := G.integrable.re
  have hmean : (∫ t : ℝ, (G t).re) = 0 := by
    change (∫ t : ℝ, RCLike.re (G t)) = 0
    rw [integral_re G.integrable]
    change (∫ t : ℝ, (𝓕 g) t).re = 0
    rw [thetaPower_fourier_mean, h0, Complex.zero_re]
  have hall : (fun t : ℝ ↦ (G t).re) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hpos hi).mp hmean
  have hre : (fun t : ℝ ↦ (G t).re) = 0 :=
    (Continuous.ae_eq_iff_eq volume (Complex.continuous_re.comp G.continuous) continuous_zero).mp hall
  have hz : G = 0 := by
    ext t
    have hh := hbd t
    have hrt := congrFun hre t
    change (G t).re = 0 at hrt
    rw [hrt, mul_zero] at hh
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (G t)])
  apply hg
  simpa [G] using congrArg (fun f : 𝓢(ℝ, ℂ) ↦ 𝓕⁻ f) hz

private theorem thetaPower_weighted_growth (g : 𝓢(ℝ, ℂ)) (h0 : g 0 = 0) (hg : g ≠ 0)
    (w : ℝ → ℝ) (hwi : Integrable w) (hw : ∀ t, 0 < w t) :
    ∃ a > 0, ∃ q > 1, ∀ n : ℕ, a * q ^ (2 * n) ≤
      ∫ t : ℝ, w t * ‖1 - (𝓕 g) t‖ ^ (2 * n) := by
  let G := 𝓕 g
  obtain ⟨t, ht⟩ := thetaPower_exists_frequency g h0 hg
  obtain ⟨q, hq, hqt⟩ := exists_between ht
  let A : Set ℝ := {x | q < ‖1 - G x‖}
  have hA : IsOpen A := isOpen_lt continuous_const ((continuous_const.sub G.continuous).norm)
  have hweight : 0 < ∫ x in A, w x := by
    apply (integral_pos_iff_support_of_nonneg (fun x ↦ (hw x).le) hwi.integrableOn).2
    have hsupp : Function.support w = univ := Set.eq_univ_of_forall fun x ↦ (hw x).ne'
    rw [hsupp, Measure.restrict_apply_univ]
    exact hA.measure_pos volume ⟨t, hqt⟩
  let M := 1 + SchwartzMap.seminorm ℝ 0 0 G
  have hbound (x : ℝ) : ‖1 - G x‖ ≤ M := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖G x‖ := norm_sub_le _ _
      _ ≤ M := by simpa [M] using add_le_add (le_refl (1 : ℝ)) (SchwartzMap.norm_le_seminorm ℝ G x)
  refine ⟨_, hweight, q, hq, fun n ↦ ?_⟩
  have hfull : Integrable (fun x : ℝ ↦ w x * ‖1 - G x‖ ^ (2 * n)) := by
    apply (hwi.mul_const (M ^ (2 * n))).mono'
      (hwi.aestronglyMeasurable.mul (((continuous_const.sub G.continuous).norm.pow _).aestronglyMeasurable))
    filter_upwards with x
    change ‖w x * ‖1 - G x‖ ^ (2 * n)‖ ≤ w x * M ^ (2 * n)
    rw [Real.norm_of_nonneg (mul_nonneg (hw x).le (by positivity))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound x) _) (hw x).le
  calc
    _ = ∫ x in A, w x * q ^ (2 * n) := (integral_mul_const _ _).symm
    _ ≤ ∫ x in A, w x * ‖1 - G x‖ ^ (2 * n) := by
      apply setIntegral_mono_on (hwi.integrableOn.mul_const _) hfull.integrableOn hA.measurableSet
      intro x hx
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_lt_one.trans hq).le (le_of_lt hx) _) (hw x).le
    _ ≤ _ := setIntegral_le_integral hfull (Eventually.of_forall (fun x ↦ mul_nonneg (hw x).le (by positivity)))

/-- Every positive integrable frequency weight sees exponential growth of the powered residual
of a nonzero Schwartz approximation supported on nonpositive log norm. -/
theorem halfLineThetaResidual_exponential_lower_bound (u : 𝓢(ℝ, ℂ)) (hu : u ≠ 0) (hs : ∀ x > 0, u x = 0)
    (w : ℝ → ℝ) (hwi : Integrable w) (hw : ∀ t, 0 < w t) :
    ∃ a > 0, ∃ q > 1, ∀ n : ℕ, a * q ^ (2 * n) ≤
      ∫ t : ℝ, w t * ‖1 - (1 / 2 - 2 * (Real.pi : ℂ) * Complex.I * t) * (𝓕 u) t‖ ^ (2 * n) := by
  let g : 𝓢(ℝ, ℂ) := (1 / 2 : ℂ) • u - ∂_{(1 : ℝ)} u
  have huz : EqOn (u : ℝ → ℂ) 0 (Ioi (0 : ℝ)) := hs
  have hgz : EqOn (g : ℝ → ℂ) 0 (Ioi (0 : ℝ)) := by
    intro t ht
    have hder := (huz.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds ht)).fderiv_eq (𝕜 := ℝ)
    change (1 / 2 : ℂ) * u t - fderiv ℝ u t 1 = 0
    rw [hs t ht, hder]
    simp
  have h0 : g 0 = 0 := hgz.closure g.continuous continuous_zero (by simp)
  have hFourier (t : ℝ) : (𝓕 g) t = (1 / 2 - 2 * (Real.pi : ℂ) * Complex.I * t) * (𝓕 u) t := by
    have hot : (fun x : ℝ ↦ inner ℝ x 1).HasTemperateGrowth := ((innerSL ℝ).flip 1).hasTemperateGrowth
    have hmul : (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ inner ℝ x 1) (𝓕 u)) t =
        (t : ℂ) * (𝓕 u) t := by
      rw [SchwartzMap.smulLeftCLM_apply hot]
      simp [Complex.real_smul]
    simp only [g, FourierTransform.fourier_sub, FourierTransform.fourier_smul,
      SchwartzMap.fourier_lineDerivOp_eq, sub_apply, smul_apply, smul_eq_mul, hmul]
    ring
  have hg : g ≠ 0 := by
    intro hz
    have hFu : 𝓕 u = (0 : 𝓢(ℝ, ℂ)) := by
      ext t
      have h := hFourier t
      rw [hz, FourierTransform.fourier_zero] at h
      have hn : (1 / 2 - 2 * (Real.pi : ℂ) * Complex.I * t) ≠ 0 := by
        intro he
        have hreal := congrArg Complex.re he
        norm_num [Complex.mul_re, Complex.mul_im] at hreal
      exact (mul_eq_zero.mp h.symm).resolve_left hn
    exact hu (by simpa using congrArg (fun f : 𝓢(ℝ, ℂ) ↦ 𝓕⁻ f) hFu)
  simpa only [hFourier] using thetaPower_weighted_growth g h0 hg w hwi hw

private theorem thetaPower_centered_tendsto (u : 𝓢(ℝ, ℂ)) (hu : u ≠ 0) (hs : ∀ x > 0, u x = 0) :
    Tendsto (fun n : ℕ ↦ ∫ t : ℝ,
      (1 / 4 + (2 * Real.pi * t) ^ 2)⁻¹ *
        ‖1 - (1 / 2 - 2 * (Real.pi : ℂ) * Complex.I * t) * (𝓕 u) t‖ ^ (2 * n))
      atTop atTop := by
  let w (t : ℝ) := (1 / 4 + (2 * Real.pi * t) ^ 2)⁻¹
  have hi : Integrable w := by
    have h := (integrable_inv_one_add_mul_sq (by positivity : (4 * Real.pi) ≠ 0)).const_mul (4 : ℝ)
    apply h.congr
    filter_upwards with t
    dsimp only [w]
    field_simp
    ring
  obtain ⟨a, ha, q, hq, h⟩ := halfLineThetaResidual_exponential_lower_bound u hu hs w hi (fun t ↦ by dsimp [w]; positivity)
  apply Filter.tendsto_atTop_mono h
  have hq' : 1 < q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
  simpa only [pow_mul] using (tendsto_pow_atTop_atTop_of_one_lt hq').const_mul_atTop ha

private theorem thetaPower_indicator_transform (t : ℝ) :
    𝓕 ((Iic (0 : ℝ)).indicator (fun x : ℝ ↦ Complex.exp ((x : ℂ) / 2))) t =
      (1 / 2 - 2 * (Real.pi : ℂ) * Complex.I * t)⁻¹ := by
  let z : ℂ := 1 / 2 - 2 * (Real.pi : ℂ) * Complex.I * t
  have hr : 0 < z.re := by norm_num [z, Complex.mul_re, Complex.mul_im]
  rw [Real.fourier_real_eq]
  have h (x : ℝ) : Real.fourierChar (-(x * t)) •
      (Iic (0 : ℝ)).indicator (fun v : ℝ ↦ Complex.exp ((v : ℂ) / 2)) x =
      (Iic (0 : ℝ)).indicator (fun v : ℝ ↦ Complex.exp (z * v)) x := by
    by_cases hx : x ∈ Iic (0 : ℝ)
    · simp only [indicator_of_mem hx, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, ← Complex.exp_add]
      congr 1
      push_cast
      dsimp only [z]
      ring
    · simp [indicator_of_notMem hx]
  simp only [h, integral_indicator measurableSet_Iic]
  change (∫ x : ℝ in Iic 0, Complex.exp (z * x)) = z⁻¹
  rw [integral_exp_mul_complex_Iic hr 0]
  simp

/-- If `H` is the Fourier transform of the centered half-line indicator, the squared error
of the geometric correction after `n` steps tends to infinity for every fixed nonzero
supported Schwartz profile. The frequency convention here is Mathlib’s real Fourier transform. -/
theorem halfLineThetaResidual_powers_tendsto_atTop (u : 𝓢(ℝ, ℂ)) (hu : u ≠ 0) (hs : ∀ x > 0, u x = 0) :
    let H := 𝓕 ((Iic (0 : ℝ)).indicator (fun x : ℝ ↦ Complex.exp ((x : ℂ) / 2)))
    Tendsto (fun n : ℕ ↦ ∫ t : ℝ, ‖H t * (1 - (𝓕 u) t / H t) ^ n‖ ^ 2) atTop atTop := by
  intro H
  have h (n : ℕ) (t : ℝ) : ‖H t * (1 - (𝓕 u) t / H t) ^ n‖ ^ 2 =
      (1 / 4 + (2 * Real.pi * t) ^ 2)⁻¹ *
        ‖1 - (1 / 2 - 2 * (Real.pi : ℂ) * Complex.I * t) * (𝓕 u) t‖ ^ (2 * n) := by
    let z : ℂ := 1 / 2 - 2 * (Real.pi : ℂ) * Complex.I * t
    have hn : ‖z‖ ^ 2 = 1 / 4 + (2 * Real.pi * t) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      norm_num [z, Complex.mul_re, Complex.mul_im]
      ring
    change ‖H t * (1 - (𝓕 u) t / H t) ^ n‖ ^ 2 = _ * ‖1 - z * (𝓕 u) t‖ ^ (2 * n)
    rw [show H t = z⁻¹ from thetaPower_indicator_transform t, div_inv_eq_mul]
    have hc : (𝓕 u) t * z = z * (𝓕 u) t := mul_comm _ _
    simp only [hc, norm_mul, mul_pow, norm_inv, inv_pow, hn, norm_pow, ← pow_mul,
      Nat.mul_comm n 2]
  simpa only [h] using thetaPower_centered_tendsto u hu hs

end RiemannMasullo
