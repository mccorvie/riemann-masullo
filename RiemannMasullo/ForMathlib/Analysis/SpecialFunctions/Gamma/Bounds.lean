module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Bounds for the gamma function on vertical strips
-/

@[expose] public section

open Filter Function MeasureTheory Set
open scoped Asymptotics Topology

namespace RiemannMasullo

local notation "atHeight" => comap (abs ∘ Complex.im) atTop

/-- On the right half-plane the norm of Euler's gamma integral is bounded by
the gamma integral at the real part. -/
theorem norm_Gamma_le_real_Gamma {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz, Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]

/-- On any fixed strip, the reciprocal gamma function is bounded by a constant
times `exp (π * |im z|)` at absolute heights at least one. -/
theorem exists_norm_inv_Gamma_le_exp_mul_abs_im (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b → 1 ≤ |z.im| →
      ‖(Complex.Gamma z)⁻¹‖ ≤ C * Real.exp (Real.pi * |z.im|) := by
  obtain ⟨n, hn⟩ := exists_nat_gt b
  have hCont : ContinuousOn Real.Gamma (Icc (1 - b + n) (1 - a + n)) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono fun x hx ↦
      show 0 < x from lt_of_lt_of_le (by linarith) hx.1
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hCont
  refine ⟨max M 0 / Real.pi, by positivity, fun z hz ht ↦ ?_⟩
  have hShift (w : ℂ) (hw : 1 ≤ |w.im|) (k : ℕ) :
      ‖Complex.Gamma w‖ ≤ ‖Complex.Gamma (w + k)‖ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc]
      exact ih.trans (Complex.norm_Gamma_le_norm_Gamma_add_one
        ((show 1 ≤ |(w + k).im| by simpa using hw).trans (Complex.abs_im_le_norm _)))
  have hRe : (1 - z + (n : ℂ)).re ∈ Icc (1 - b + n) (1 - a + n) := by
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.natCast_re, mem_Icc]
    exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hGamma : ‖Complex.Gamma (1 - z)‖ ≤ max M 0 := by
    refine (hShift (1 - z) (by simpa using ht) n).trans ?_
    refine (norm_Gamma_le_real_Gamma (lt_of_lt_of_le (by linarith) hRe.1)).trans ?_
    exact (le_abs_self _).trans ((hM _ hRe).trans (le_max_left _ _))
  have hSin (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
    have h := norm_sub_le (Complex.exp (-w * Complex.I)) (Complex.exp (w * Complex.I))
    have he := congrArg (fun z : ℂ ↦ ‖z‖) (Complex.two_sin w)
    simp only [norm_mul, Complex.norm_I, mul_one] at he
    norm_num [Complex.norm_exp, Complex.mul_re] at he h
    have h₁ := Real.exp_le_exp.mpr (le_abs_self w.im)
    have h₂ := Real.exp_le_exp.mpr (neg_le_abs w.im)
    linarith
  have him : z.im ≠ 0 := by
    intro he
    norm_num [he] at ht
  have hGne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero fun k he ↦ him (by
    rw [he]
    simp)
  have hSne : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k he
    have him' := congrArg Complex.im he
    have hprod : Real.pi * z.im = 0 := by
      simpa only [Complex.im_ofReal_mul, ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
        Complex.ofReal_im] using him'
    exact (mul_ne_zero Real.pi_ne_zero him) hprod
  have hReflect : (Complex.Gamma z)⁻¹ =
      Complex.Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ) := by
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).2
    calc
      _ = (Complex.Gamma z)⁻¹ * ((Complex.Gamma z * Complex.Gamma (1 - z)) *
          Complex.sin ((Real.pi : ℂ) * z)) := by
        rw [Complex.Gamma_mul_Gamma_one_sub, div_mul_cancel₀ _ hSne]
      _ = _ := by rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hGne, one_mul]
  rw [hReflect, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  refine mul_le_mul hGamma ?_ (norm_nonneg _) (le_max_right _ _)
  simpa only [Complex.im_ofReal_mul, abs_mul, abs_of_pos Real.pi_pos] using
    hSin ((Real.pi : ℂ) * z)

/-- Shifting a real archimedean gamma factor contributes a constant to its reciprocal
exponential bound on a fixed strip. -/
theorem inv_Gammaℝ_add_isBigO_exp (a b : ℝ) (w : ℂ) :
    (fun s : ℂ ↦ (Complex.Gammaℝ (s + w))⁻¹) =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)]
      fun s ↦ Real.exp ((Real.pi / 2) * |s.im|) := by
  let A := (a + w.re) / 2
  let B := (b + w.re) / 2
  obtain ⟨C, hC, hΓ⟩ := exists_norm_inv_Gamma_le_exp_mul_abs_im A B
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := A) (b := B)).exists_bound_of_continuousOn
    (f := fun x ↦ Real.pi ^ x) (by fun_prop)
  have hHeight : Tendsto (fun s : ℂ ↦ |s.im|) (atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)) atTop :=
    tendsto_inf_left tendsto_comap
  have hStrip : ∀ᶠ s : ℂ in atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b), s.re ∈ Icc a b :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ hs ↦ hs)
  refine Asymptotics.IsBigO.of_bound (max M 0 * C * Real.exp ((Real.pi / 2) * |w.im|)) ?_
  filter_upwards [hStrip, hHeight.eventually_ge_atTop (2 + |w.im|)] with s hs ht
  let z := (s + w) / 2
  have hz : z.re ∈ Icc A B := by
    simp only [z, A, B, Complex.div_ofNat_re, Complex.add_re, mem_Icc]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hiz : |z.im| = |s.im + w.im| / 2 := by
    simp [z, Complex.div_ofNat_im, abs_div]
  have hzLower : 1 ≤ |z.im| := by
    rw [hiz]
    have hTriangle := abs_sub_abs_le_abs_sub s.im (-w.im)
    rw [abs_neg, sub_neg_eq_add] at hTriangle
    linarith
  have hzUpper : |z.im| ≤ (|s.im| + |w.im|) / 2 := by
    rw [hiz]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  rw [Complex.Gammaℝ_def, mul_inv_rev, neg_div, ← Complex.cpow_neg,
    neg_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  change ‖(Complex.Gamma z)⁻¹‖ * Real.pi ^ z.re ≤ _
  calc
    _ ≤ (C * Real.exp (Real.pi * |z.im|)) * max M 0 :=
      mul_le_mul (hΓ z hz hzLower) ((le_abs_self _).trans ((hM _ hz).trans (le_max_left _ _)))
        (Real.rpow_nonneg Real.pi_pos.le _) (by positivity)
    _ ≤ (C * Real.exp ((Real.pi / 2) * (|s.im| + |w.im|))) * max M 0 := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC)
        (le_max_right _ _)
      linarith [mul_le_mul_of_nonneg_left hzUpper Real.pi_pos.le]
    _ = _ := by rw [mul_add, Real.exp_add]; ring

end RiemannMasullo
