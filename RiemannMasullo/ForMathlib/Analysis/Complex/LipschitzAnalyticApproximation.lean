module

public import RiemannMasullo.ForMathlib.Analysis.Complex.SzegoPrediction
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Analytic polynomial majorants with angular derivative control

A short angular average smooths the real part of a polynomial approximation. The endpoint
difference controls the real angular derivative independently of the approximating degree.
-/

@[expose] public noncomputable section

open Complex Metric MeasureTheory Set Real
open scoped Interval

namespace HardySzego

private def rot (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * I)

private lemma rot_zero : rot 0 = 1 := by simp [rot]

private lemma norm_rot (t : ℝ) : ‖rot t‖ = 1 := by simp [rot, Complex.norm_exp]

private lemma continuous_rot : Continuous rot := by unfold rot; fun_prop

private lemma circle_rot (t : ℝ) : circleMap 0 1 t = rot t := by simp [circleMap_zero, rot]

private lemma sphere_rot {z : ℂ} (hz : z ∈ sphere 0 1) (t : ℝ) : rot t * z ∈ sphere 0 1 := by
  simpa only [mem_sphere_zero_iff_norm, norm_mul, norm_rot, one_mul] using hz

private def arcPolynomial (p : Polynomial ℂ) (h : ℝ) : Polynomial ℂ :=
  ∑ k ∈ p.support, Polynomial.monomial k
    (p.coeff k * (∫ t in 0..h, rot t ^ k) / (h : ℂ))

private lemma arc_eval (p : Polynomial ℂ) (h : ℝ) (z : ℂ) :
    (arcPolynomial p h).eval z = (∫ t in 0..h, p.eval (rot t * z)) / (h : ℂ) := by
  simp only [arcPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def, mul_pow]
  have hk (k : ℕ) : IntervalIntegrable (fun t ↦ p.coeff k*(rot t^k*z^k)) volume 0 h :=
    ((continuous_const.mul ((continuous_rot.pow k).mul continuous_const))).intervalIntegrable ..
  rw [intervalIntegral.integral_finsetSum (fun k _ ↦ hk k), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
  ring

private lemma rot_pow_primitive (h : ℝ) (k : ℕ) :
    ((∫ t in 0..h, rot t ^ k) * ((k : ℂ) * I)) = rot h ^ k - 1 := by
  have hr (t : ℝ) : HasDerivAt rot (rot t * I) t := by
    simpa [rot] using! (((hasDerivAt_id (t:ℂ)).mul_const I).cexp.comp_ofReal)
  have hd (t : ℝ) : HasDerivAt (fun s ↦ rot s^k) (rot t^k*((k:ℂ)*I)) t := by
    convert (hr t).pow k using 1
    cases k with
    | zero => simp
    | succ k => simp only [Nat.succ_sub_one, pow_succ]; ring
  rw [← intervalIntegral.integral_mul_const]
  simpa only [rot_zero, one_pow] using intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := h) (fun t _ ↦ hd t)
    (((continuous_rot.pow k).mul continuous_const).intervalIntegrable ..)

private lemma arc_derivative (p : Polynomial ℂ) {h : ℝ} (hh : 0 < h) (z : ℂ) :
    I*z*(arcPolynomial p h).derivative.eval z =
      (p.eval (rot h*z) - p.eval z) / (h : ℂ) := by
  simp only [arcPolynomial, Polynomial.derivative_sum, Polynomial.eval_finsetSum,
    Polynomial.derivative_monomial, Polynomial.eval_monomial]
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def, mul_pow]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hi := rot_pow_primitive h k
  have h0 : (h:ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  field_simp
  cases k with
  | zero => simp
  | succ k =>
    simp only [Nat.succ_sub_one]
    linear_combination (p.coeff (k+1)*z^(k+1)) * hi

private lemma arc_real_eval (p : Polynomial ℂ) (h : ℝ) (z : ℂ) :
    ((arcPolynomial p h).eval z).re = (∫ t in 0..h, (p.eval (rot t*z)).re) / h := by
  have hc : IntervalIntegrable (fun t ↦ p.eval (rot t*z)) volume 0 h :=
    (p.continuous.comp (continuous_rot.mul continuous_const)).intervalIntegrable
    (μ := volume) 0 h
  rw [arc_eval, Complex.div_ofReal_re]
  exact congrArg (fun x : ℝ ↦ x/h) (Complex.reCLM.intervalIntegral_comp_comm hc).symm


private lemma rot_chord {z : ℂ} (hz : z ∈ sphere 0 1) (t : ℝ) :
    ‖rot t*z-z‖ ≤ |t| := by
  rw [← sub_one_mul, norm_mul, mem_sphere_zero_iff_norm.mp hz, mul_one]
  simpa only [rot, mul_comm (t:ℂ) I, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t))

/-- A Lipschitz real circle function has one-sided analytic polynomial approximations.
The real angular derivative is bounded independently of the error and the polynomial degree. -/
theorem exists_polynomial_re_majorant {g : ℂ → ℝ} (hg : ContinuousOn g (sphere 0 1))
    {L ε : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ z ∈ sphere (0:ℂ) 1, ∀ w ∈ sphere (0:ℂ) 1, |g z-g w| ≤ L*‖z-w‖)
    (hε : 0 < ε) :
    ∃ Q : Polynomial ℂ, ∀ z ∈ sphere (0:ℂ) 1,
      g z ≤ (Q.eval z).re ∧ (Q.eval z).re ≤ g z+ε ∧
      |(I*z*Q.derivative.eval z).re| ≤ L+1 := by
  let h := ε/(4*(L+1))
  have hh : 0 < h := by dsimp [h]; positivity
  have hprod : h*(4*(L+1)) = ε := by dsimp [h]; field_simp
  obtain ⟨p,hp⟩ := exists_polynomial_re_approx g hg (half_pos hh)
  let A := arcPolynomial p h
  have hu (z : ℂ) (hz : z ∈ sphere 0 1) (t : ℝ) (ht : t ∈ Icc 0 h) :
      |(p.eval (rot t*z)).re-g z| ≤ ε/2 := by
    have hq := (hp _ (sphere_rot hz t)).le
    have hs := (hLip _ (sphere_rot hz t) z hz).trans
      (mul_le_mul_of_nonneg_left (rot_chord hz t) hL)
    rw [abs_of_nonneg ht.1] at hs
    have htL := mul_le_mul_of_nonneg_left ht.2 hL
    have ha := abs_sub_le (p.eval (rot t*z)).re (g (rot t*z)) (g z)
    nlinarith
  have hav (z : ℂ) (hz : z ∈ sphere 0 1) :
      g z-ε/2 ≤ (A.eval z).re ∧ (A.eval z).re ≤ g z+ε/2 := by
    let v (t : ℝ) := (p.eval (rot t*z)).re
    have hv : Continuous v := Complex.continuous_re.comp (p.continuous.comp (continuous_rot.mul continuous_const))
    have hl := intervalIntegral.integral_mono_on hh.le
      (continuous_const.intervalIntegrable (μ := volume) 0 h) (hv.intervalIntegrable ..)
      (f := fun _ ↦ g z-ε/2) (fun t ht ↦ by dsimp [v]; linarith [(abs_le.mp (hu z hz t ht)).1])
    have hr := intervalIntegral.integral_mono_on hh.le (hv.intervalIntegrable ..)
      (continuous_const.intervalIntegrable (μ := volume) 0 h)
      (g := fun _ ↦ g z+ε/2) (fun t ht ↦ by dsimp [v]; linarith [(abs_le.mp (hu z hz t ht)).2])
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hl hr
    rw [show (A.eval z).re = (∫ t in 0..h, v t)/h from arc_real_eval p h z]
    exact ⟨(le_div_iff₀ hh).mpr (by linarith only [hl]), (div_le_iff₀ hh).mpr (by linarith only [hr])⟩
  refine ⟨A + Polynomial.C ((ε/2:ℝ):ℂ), fun z hz ↦ ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_C, Complex.add_re, Complex.ofReal_re,
    Polynomial.derivative_add, Polynomial.derivative_C, add_zero]
  refine ⟨by linarith [(hav z hz).1], by linarith [(hav z hz).2], ?_⟩
  rw [show I*z*A.derivative.eval z = _ from arc_derivative p hh z, Complex.div_ofReal_re,
    Complex.sub_re, abs_div, abs_of_pos hh, div_le_iff₀ hh]
  have h1 := (hp _ (sphere_rot hz h)).le
  have h2 := (hp z hz).le
  have h3 := (hLip _ (sphere_rot hz h) z hz).trans
    (mul_le_mul_of_nonneg_left (rot_chord hz h) hL)
  rw [abs_of_pos hh] at h3
  apply abs_le.mpr
  have hlow1 := (abs_le.mp h1).1
  have hupp1 := (abs_le.mp h1).2
  have hlow2 := (abs_le.mp h2).1
  have hupp2 := (abs_le.mp h2).2
  have hlow3 := (abs_le.mp h3).1
  have hupp3 := (abs_le.mp h3).2
  constructor <;> linarith


/-- For a disk-algebra function vanishing at zero, the real part carries half the boundary
square norm. This is the mean value property applied to the holomorphic square. -/
theorem circleAverage_norm_sq_eq_two_re_sq {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 1)) (h0 : f 0 = 0) :
    circleAverage (fun z ↦ ‖f z‖^2) 0 1 =
      2*circleAverage (fun z ↦ (f z).re^2) 0 1 := by
  have hc := hf.continuousOn
  rw [closure_ball _ one_ne_zero] at hc
  have hr : ContinuousOn (fun z ↦ (f z).re^2) (closedBall 0 1) :=
    (Complex.continuous_re.comp_continuousOn hc).pow 2
  have hs : ContinuousOn (fun z ↦ (f z)^2) (closedBall 0 1) := hc.pow 2
  have hi : CircleIntegrable (fun z ↦ (f z)^2) 0 1 :=
    (hs.mono sphere_subset_closedBall).circleIntegrable zero_le_one
  have hri := (hr.mono sphere_subset_closedBall).circleIntegrable zero_le_one
  have hsi := ((Complex.continuous_re.comp_continuousOn hs).mono sphere_subset_closedBall).circleIntegrable zero_le_one
  have hm : circleAverage (fun z ↦ ((f z)^2).re) 0 1 = 0 := by
    have hd : DiffContOnCl ℂ (fun z ↦ (f z)^2) (ball 0 |(1:ℝ)|) := by
      rw [abs_one]
      exact ⟨hf.differentiableOn.pow 2, hf.continuousOn.pow 2⟩
    exact (Complex.reCLM.circleAverage_comp_comm hi).trans (by simp [hd.circleAverage, h0])
  have he (w : ℂ) : ‖w‖^2 = (2:ℝ) • w.re^2-(w^2).re := by
    rw [Complex.sq_norm]
    simp only [smul_eq_mul, Complex.normSq_apply, pow_two, Complex.mul_re]
    ring
  simp_rw [he]
  have h2 : CircleIntegrable (fun z ↦ (2:ℝ) • (f z).re^2) 0 1 := hri.const_smul (a := (2:ℝ))
  have hr2 : CircleIntegrable (fun z ↦ ((f z)^2).re) 0 1 := hsi
  rw [circleAverage_fun_sub h2 hr2, circleAverage_fun_smul, hm, sub_zero, smul_eq_mul]

/-- An analytic polynomial with bounded real angular derivative has a degree-independent
boundary square mean for its full complex derivative. -/
theorem circleAverage_derivative_sq_le (Q : Polynomial ℂ) {L : ℝ}
    (h : ∀ z ∈ sphere (0:ℂ) 1, |(I*z*Q.derivative.eval z).re| ≤ L) :
    circleAverage (fun z ↦ ‖Q.derivative.eval z‖^2) 0 1 ≤ 2*L^2 := by
  let K (z : ℂ) := I*z*Q.derivative.eval z
  have hd : Differentiable ℂ K :=
    ((differentiable_const I).mul differentiable_id).mul (fun z ↦ (Q.derivative.hasDerivAt z).differentiableAt)
  have hnorm : circleAverage (fun z ↦ ‖Q.derivative.eval z‖^2) 0 1 =
      circleAverage (fun z ↦ ‖K z‖^2) 0 1 := by
    apply circleAverage_congr_sphere
    intro z hz
    have hnorm : ‖z‖ = 1 := by simpa using hz
    simp [K, hnorm]
  rw [hnorm, circleAverage_norm_sq_eq_two_re_sq hd.diffContOnCl (by simp [K])]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply circleAverage_mono_on_of_le_circle
    ((Complex.continuous_re.comp hd.continuous).pow 2).continuousOn.circleIntegrable'
  intro z hz
  have ha := abs_le.mp (h z (by simpa using hz))
  exact sq_le_sq' ha.1 ha.2

end HardySzego
