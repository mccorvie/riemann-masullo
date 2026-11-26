module
public import RiemannMasullo.ForMathlib.Analysis.Fourier.AbelLimit
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Abs

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RiemannMasullo

/-- The angular Fourier integral of a reciprocal quadratic at arbitrary positive scale. -/
theorem integral_cexp_mul_inv_scale_add_sq {a : ℝ} (ha : 0 < a) (d : ℝ) :
    (∫ x : ℝ, Complex.exp (↑(d * x) * Complex.I) * (((a ^ 2 + x ^ 2)⁻¹ : ℝ) : ℂ)) =
      ((Real.pi / a * Real.exp (-a * |d|) : ℝ) : ℂ) := by
  let g (x : ℝ) := Complex.exp (↑((d * a) * x) * Complex.I) * (((1 + x ^ 2)⁻¹ : ℝ) : ℂ)
  have he (x : ℝ) : Complex.exp (↑(d * x) * Complex.I) * (((a ^ 2 + x ^ 2)⁻¹ : ℝ) : ℂ) =
      (((a ^ 2)⁻¹ : ℝ) : ℂ) * g (a⁻¹ * x) := by
    have harg : (d * a) * (a⁻¹ * x) = d * x := by field_simp
    have hweight : (a ^ 2 + x ^ 2)⁻¹ = (a ^ 2)⁻¹ * (1 + (a⁻¹ * x) ^ 2)⁻¹ := by
      field_simp
    dsimp [g]
    rw [harg, hweight]
    push_cast
    ring
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_mul_left, inv_inv, abs_of_pos ha,
    Complex.real_smul, show (∫ x, g x) = _ from integral_cexp_mul_inv_one_add_sq (d * a)]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [abs_mul, abs_of_pos ha, mul_comm |d| a, neg_mul]
  field_simp

/-- The angular Fourier integral of the reciprocal quartic Sobolev weight. -/
theorem integral_cexp_mul_inv_one_add_sq_sq (d : ℝ) :
    (∫ x : ℝ, Complex.exp (↑(d * x) * Complex.I) * ((((1 + x ^ 2) ^ 2)⁻¹ : ℝ) : ℂ)) =
      ((Real.pi / 2 * (1 + |d|) * Real.exp (-|d|) : ℝ) : ℂ) := by
  let F (a x : ℝ) := Complex.exp (↑(d * x) * Complex.I) * (((a ^ 2 + x ^ 2)⁻¹ : ℝ) : ℂ)
  let F' (a x : ℝ) := Complex.exp (↑(d * x) * Complex.I) * ((-(2 * a) / (a ^ 2 + x ^ 2) ^ 2 : ℝ) : ℂ)
  have hdiff (a x : ℝ) (ha : 0 < a) : HasDerivAt (fun b ↦ F b x) (F' a x) a := by
    have h : HasDerivAt (fun b : ℝ ↦ (b ^ 2 + x ^ 2)⁻¹)
        (-(2 * a) / (a ^ 2 + x ^ 2) ^ 2) a := by
      have hp : HasDerivAt (fun b : ℝ ↦ b ^ 2 + x ^ 2) (2 * a) a := by
        simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using
          ((hasDerivAt_id a).pow 2).add_const (x ^ 2)
      exact hp.inv (by positivity)
    exact h.ofReal_comp.const_mul _
  have hnorm (a x : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) (3 / 2)) :
      ‖F' a x‖ ≤ 64 * (1 + x ^ 2)⁻¹ := by
    have ha0 : 0 < a := by linarith [ha.1]
    have hd : 0 < a ^ 2 + x ^ 2 := by positivity
    have hq : 1 + x ^ 2 ≤ 16 * (a ^ 2 + x ^ 2) ^ 2 := by
      have hbase : 1 / 4 + x ^ 2 ≤ a ^ 2 + x ^ 2 := by nlinarith [ha.1]
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (a ^ 2 + x ^ 2 - (1 / 4 + x ^ 2)), sq_nonneg x]
    dsimp only [F']
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_self, Real.exp_zero, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (mul_pos two_pos ha0), abs_of_pos (sq_pos_of_pos hd)]
    rw [div_le_iff₀ (sq_pos_of_pos hd)]
    have hr : 1 ≤ 16 * (a ^ 2 + x ^ 2) ^ 2 / (1 + x ^ 2) := by
      apply (le_div_iff₀ (by positivity : 0 < 1 + x ^ 2)).mpr
      simpa using hq
    rw [div_eq_mul_inv] at hr
    nlinarith [ha.2]
  have hint : Integrable (F 1) := by
    apply integrable_inv_one_add_sq.mono' (by dsimp [F]; fun_prop)
    exact .of_forall fun x ↦ by
      dsimp [F]
      rw [norm_mul, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_self, Real.exp_zero, one_mul, one_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (1 + x ^ 2)⁻¹)]
      exact le_rfl
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := (1 : ℝ)) (bound := fun x ↦ 64 * (1 + x ^ 2)⁻¹)
    (s := Ioo (1 / 2 : ℝ) (3 / 2))
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (.of_forall fun a ↦ by dsimp [F]; fun_prop)
    hint
    (by dsimp [F']; fun_prop)
    (.of_forall fun x a ha ↦ hnorm a x ha)
    (integrable_inv_one_add_sq.const_mul 64)
    (.of_forall fun x a ha ↦ hdiff a x (by linarith [ha.1]))
  have he : (fun a : ℝ ↦ ∫ x, F a x) =ᶠ[𝓝 1]
      (fun a : ℝ ↦ ((Real.pi / a * Real.exp (-a * |d|) : ℝ) : ℂ)) := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with a ha
    exact integral_cexp_mul_inv_scale_add_sq ha d
  have hright : HasDerivAt (fun a : ℝ ↦ ((Real.pi / a * Real.exp (-a * |d|) : ℝ) : ℂ))
      ((-Real.pi * (1 + |d|) * Real.exp (-|d|) : ℝ) : ℂ) 1 := by
    convert (((hasDerivAt_const (1 : ℝ) Real.pi).div (hasDerivAt_id 1) (by norm_num)).mul
      ((((hasDerivAt_id 1).neg).mul_const |d|).exp)).ofReal_comp using 1 <;> norm_num [Pi.div_apply, Pi.mul_apply, id]; ring
  have hd := (h.2.congr_of_eventuallyEq he.symm).unique hright
  have hi : (∫ x, F' 1 x) = (-2 : ℂ) *
      ∫ x : ℝ, Complex.exp (↑(d * x) * Complex.I) * ((((1 + x ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae (.of_forall fun x ↦ ?_)
    dsimp [F']
    push_cast
    ring
  rw [hi] at hd
  have heq : (-2 : ℂ) * ((Real.pi / 2 * (1 + |d|) * Real.exp (-|d|) : ℝ) : ℂ) =
      ((-Real.pi * (1 + |d|) * Real.exp (-|d|) : ℝ) : ℂ) := by push_cast; ring
  exact mul_left_cancel₀ (by norm_num : (-2 : ℂ) ≠ 0) (hd.trans heq.symm)


private theorem quartic_phase_norm (d x : ℝ) : ‖Complex.exp (↑(d * x) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- The first absolute moment of the reciprocal quartic weight is integrable. -/
theorem integrable_abs_mul_inv_one_add_sq_sq :
    Integrable (fun x : ℝ ↦ |x| * ((1 + x ^ 2) ^ 2)⁻¹) := by
  apply integrable_inv_one_add_sq.mono' (by fun_prop)
  refine .of_forall fun x ↦ ?_
  rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, inv_eq_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hx : |x| ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  nlinarith [sq_nonneg x, mul_le_mul_of_nonneg_right hx (by positivity : 0 ≤ 1 + x ^ 2)]

/-- Away from zero, the first log moment of the quartic kernel is explicit. -/
theorem integral_cexp_mul_id_mul_inv_one_add_sq_sq {d : ℝ} (hd : d ≠ 0) :
    (∫ x : ℝ, Complex.exp (↑(d * x) * Complex.I) * (x : ℂ) *
      ((((1 + x ^ 2) ^ 2)⁻¹ : ℝ) : ℂ)) =
      Complex.I * ((Real.pi / 2 * d * Real.exp (-|d|) : ℝ) : ℂ) := by
  let F (a x : ℝ) := Complex.exp (↑(a * x) * Complex.I) * ((((1 + x ^ 2) ^ 2)⁻¹ : ℝ) : ℂ)
  let F' (a x : ℝ) := Complex.I * (Complex.exp (↑(a * x) * Complex.I) * (x : ℂ) *
    ((((1 + x ^ 2) ^ 2)⁻¹ : ℝ) : ℂ))
  have hnorm (a x : ℝ) : ‖F' a x‖ = |x| * ((1 + x ^ 2) ^ 2)⁻¹ := by
    dsimp only [F']
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, quartic_phase_norm, one_mul, one_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_of_nonneg (by positivity)]
  have hint : Integrable (F d) := by
    apply integrable_inv_one_add_sq.mono' (by dsimp [F]; fun_prop)
    refine .of_forall fun x ↦ ?_
    dsimp only [F]
    rw [norm_mul, quartic_phase_norm, one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    apply inv_anti₀ (by positivity)
    nlinarith [sq_nonneg x]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := d)
    (bound := fun x : ℝ ↦ |x| * ((1 + x ^ 2) ^ 2)⁻¹) (s := univ)
    (by simp)
    (.of_forall fun a ↦ by dsimp [F]; fun_prop) hint
    (by dsimp [F']; fun_prop)
    (.of_forall fun x a _ ↦ (hnorm a x).le) integrable_abs_mul_inv_one_add_sq_sq
    (.of_forall fun x a _ ↦ by
      convert ((((hasDerivAt_id a).mul_const x).ofReal_comp.mul_const Complex.I).cexp).mul_const
        (((((1 + x ^ 2) ^ 2)⁻¹ : ℝ) : ℂ)) using 1 <;>
        simp only [F, F', id_eq, one_mul]
      ring)
  have hr : HasDerivAt (fun a : ℝ ↦ ((Real.pi / 2 * (1 + |a|) * Real.exp (-|a|) : ℝ) : ℂ))
      ((-(Real.pi / 2) * d * Real.exp (-|d|) : ℝ) : ℂ) d := by
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · convert (((hasDerivAt_abs_neg hneg).const_add 1).const_mul (Real.pi / 2) |>.mul
        (hasDerivAt_abs_neg hneg).neg.exp).ofReal_comp using 1
      ·
        simp only [Pi.neg_apply, abs_of_neg hneg, neg_neg]
        push_cast
        ring
    · convert (((hasDerivAt_abs_pos hpos).const_add 1).const_mul (Real.pi / 2) |>.mul
        (hasDerivAt_abs_pos hpos).neg.exp).ofReal_comp using 1
      ·
        simp only [Pi.neg_apply, abs_of_pos hpos]
        push_cast
        ring
  have heq : (fun a ↦ ∫ x, F a x) =
      (fun a ↦ ((Real.pi / 2 * (1 + |a|) * Real.exp (-|a|) : ℝ) : ℂ)) :=
    funext integral_cexp_mul_inv_one_add_sq_sq
  rw [heq] at h
  have hd' := h.2.unique hr
  change (∫ x : ℝ, Complex.I * (Complex.exp (↑(d * x) * Complex.I) * (x : ℂ) *
    ((((1 + x ^ 2) ^ 2)⁻¹ : ℝ) : ℂ))) = _ at hd'
  rw [integral_const_mul] at hd'
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [hd', ← mul_assoc, Complex.I_mul_I, neg_one_mul]
  push_cast
  ring

end RiemannMasullo
