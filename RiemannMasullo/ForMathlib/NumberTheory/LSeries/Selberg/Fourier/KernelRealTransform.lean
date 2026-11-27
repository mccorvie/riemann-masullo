module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

public section

namespace RiemannMasullo.Selberg

open Complex HurwitzZeta MeasureTheory Set

private theorem psi_real_eq_evenKernel (y : ℝ) :
    psi (exp y) = ((evenKernel 0 (Real.exp (2 * y)) : ℂ) - 1) / 2 := by
  let x := Real.exp (2 * y)
  have hx : 0 < (I * (x : ℂ)).im := by
    rw [I_mul_im, ofReal_re]
    exact Real.exp_pos _
  have hθ : (evenKernel 0 x : ℂ) = jacobiTheta (I * x) := by
    simpa [jacobiTheta_eq_jacobiTheta₂] using evenKernel_def 0 x
  change psi (exp y) = ((evenKernel 0 x : ℂ) - 1) / 2
  rw [hθ, ← (hasSum_nat_jacobiTheta hx).tsum_eq]
  apply tsum_congr
  intro n
  congr 1
  simp only [x, ofReal_exp, ofReal_mul, ofReal_ofNat, Nat.cast_add, Nat.cast_one,
    two_mul (y : ℂ), exp_add]
  linear_combination -(Real.pi : ℂ) * ((n : ℂ) + 1)^2 * (exp y)^2 * I_sq

/-- Above one, the Mellin transform of the constant function contributes the pole at zero
when the Mellin parameter has negative real part. -/
private theorem hasMellin_one_Ioi {z : ℂ} (hz : z.re < 0) :
    HasMellin ((Ioi (1 : ℝ)).indicator (fun _ ↦ (1 : ℂ))) z (-1 / z) := by
  have h : (z - 1).re < -1 := by simp only [sub_re, one_re]; linarith
  simp_rw [HasMellin, mellin, MellinConvergent, ← indicator_smul, smul_eq_mul, mul_one,
    IntegrableOn, integrable_indicator_iff measurableSet_Ioi, integral_indicator measurableSet_Ioi,
    IntegrableOn, Measure.restrict_restrict_of_subset (Ioi_subset_Ioi zero_le_one)]
  exact ⟨integrableOn_Ioi_cpow_of_lt h one_pos,
    by simpa using integral_Ioi_cpow_of_lt h (c := 1) one_pos⟩

/-- In the critical strip, subtracting both constant terms globally realizes the meromorphic
FE-pair transform as one convergent integral. -/
private theorem mellin_corrected_theta {a : ℂ} (h₀ : 0 < a.re) (h₁ : a.re < 1 / 2) :
    mellin (fun x : ℝ ↦ (evenKernel 0 x : ℂ) - 1 - (x : ℂ) ^ (-(1 / 2) : ℂ)) a =
      (hurwitzEvenFEPair 0).Λ a := by
  let P := hurwitzEvenFEPair 0
  let lo := (Ioc (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℂ))
  let hi := (Ioi (1 : ℝ)).indicator (fun _ ↦ (1 : ℂ))
  let tail (x : ℝ) := (x : ℂ) ^ (-(1 / 2) : ℂ) • hi x
  have hmod : MellinConvergent P.f_modif a := (P.isStrongFEPair_toStrongFEPair.hasMellin a).1
  have hlo : HasMellin lo a (1 / a) := hasMellin_one_Ioc h₀
  have hhi : HasMellin hi (a + -(1 / 2)) (-1 / (a + -(1 / 2))) :=
    hasMellin_one_Ioi (by simp [add_re, neg_re]; linarith)
  have htail : MellinConvergent tail a := MellinConvergent.cpow_smul.mpr hhi.1
  have hsub := hasMellin_sub hmod hlo.1
  calc
    _ = mellin (fun x ↦ P.f_modif x - lo x - tail x) a := by
      apply setIntegral_congr_ae measurableSet_Ioi
      filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx
      intro hx₀
      congr 1
      rcases lt_or_gt_of_ne hx with h | h
      · simp [P, WeakFEPair.f_modif, hurwitzEvenFEPair, lo, tail, hi, h.not_gt,
          show x ∈ Ioo 0 1 from ⟨hx₀, h⟩, show x ∈ Ioc 0 1 from ⟨hx₀, h.le⟩,
          ofReal_cpow (le_of_lt hx₀)]
        ring
      · simp [P, WeakFEPair.f_modif, hurwitzEvenFEPair, lo, tail, hi, h, h.not_gt, h.not_ge]
    _ = mellin P.f_modif a - 1 / a - (-1 / (a + -(1 / 2))) := by
      rw [(hasMellin_sub hsub.1 htail).2, hsub.2, hlo.2]
      simp only [tail, mellin_cpow_smul, hhi.2]
    _ = P.Λ a := by
      simp [WeakFEPair.Λ, WeakFEPair.Λ₀, P, hurwitzEvenFEPair, ← sub_eq_add_neg]
      rw [show a - 2⁻¹ = -(2⁻¹ - a) by ring, div_neg, neg_div, neg_neg, one_div]

/-- After the substitution `x = exp (2y)`, the Mellin density in logarithmic
coordinates is twice the Fourier integrand. -/
private theorem theta_density (t y : ℝ) :
    let s : ℂ := 1 / 2 + t * I
    let x := Real.exp (2 * y)
    x • ((x : ℂ) ^ (s / 2 - 1) •
      ((evenKernel 0 x : ℂ) - 1 - (x : ℂ) ^ (-(1 / 2) : ℂ))) =
        2 * (K y * osc (t * y)) := by
  dsimp only
  let x := Real.exp (2 * y)
  have hx : 0 < x := Real.exp_pos _
  have hpow (b : ℂ) : (x : ℂ) ^ b = exp ((2 * y : ℂ) * b) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ← ofReal_log hx.le]
    simp only [x, Real.log_exp, ofReal_mul, ofReal_ofNat]
  have htheta : (evenKernel 0 x : ℂ) - 1 = 2 * psi (exp y) := by
    rw [psi_real_eq_evenKernel]
    dsimp only [x]
    ring
  change x • ((x : ℂ) ^ _ • ((evenKernel 0 x : ℂ) - 1 - (x : ℂ) ^ _)) = _
  rw [real_smul, smul_eq_mul, htheta, hpow, hpow, K, osc, ofReal_mul,
    ← mul_assoc, show (x : ℂ) = exp (2 * y : ℂ) by simp [x], ← exp_add]
  rw [show (2 * y : ℂ) + 2 * y * ((1 / 2 + t * I) / 2 - 1) =
      y / 2 + I * (t * y) by ring,
    show (2 * y : ℂ) * -(1 / 2) = -y by ring]
  have he : exp (y / 2 + I * (t * y) : ℂ) * exp (-y : ℂ) =
      exp (-y / 2 : ℂ) * exp (I * (t * y)) := by
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  rw [mul_sub, he, exp_add]
  ring

/-- Card 17. The angular Fourier transform of the real-axis kernel at t equals half the completed
zeta function at 1/2 + it.
Titchmarsh, §10.1, p. 254, first unnumbered display, and §10.10 p. 269. -/
theorem kernel_real_transform (t : ℝ) :
    ft (fun y ↦ K (y : ℂ)) t = completedRiemannZeta (1/2+(t : ℂ)*Complex.I)/2 := by
  let s : ℂ := 1 / 2 + t * I
  let F (x : ℝ) := (x : ℂ) ^ (s / 2 - 1) •
    ((evenKernel 0 x : ℂ) - 1 - (x : ℂ) ^ (-(1 / 2) : ℂ))
  let g (u : ℝ) := Real.exp u • F (Real.exp u)
  have hM : (∫ u, g u) = (hurwitzEvenFEPair 0).Λ (s / 2) := by
    rw [show (∫ u, g u) = ∫ x in Ioi 0, F x from integral_comp_exp F]
    apply mellin_corrected_theta <;> norm_num [s, add_re, mul_I_re]
  have hscale := Measure.integral_comp_mul_left g 2
  have hpt (y : ℝ) : g (2 * y) = 2 * (K y * osc (t * y)) := theta_density t y
  simp_rw [hpt] at hscale
  rw [integral_const_mul, hM, real_smul] at hscale
  change (∫ y : ℝ, K y * osc (t * y)) = (hurwitzEvenFEPair 0).Λ (s / 2) / 2 / 2
  norm_num at hscale
  linear_combination hscale / 2

end RiemannMasullo.Selberg
