module

public import RiemannMasullo.ForMathlib.Analysis.Complex.DiskFiniteFourier
public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Measured Taylor sections on expanding disks

The observed polynomial at stage `n` has degree at most `n³`. Its inputs are the
Taylor coefficients through that degree with a uniform dyadic error. The proof uses
Cauchy's estimate and the disk Harnack inequality (Axler, Bourdon and Ramey,
*Harmonic Function Theory*, Theorem 3.4).
-/

@[expose] public noncomputable section

open Complex Filter Finset Function InnerProductSpace MeasureTheory Metric Real Set
open scoped Topology

namespace RiemannMasullo.ExpandingTaylor

/-- The radius tested at stage n. Only stages n ≥ 2 enter the estimates. -/
def radius (n : ℕ) : ℝ := 1 - 1 / (n : ℝ)

/-- The coefficient estimate uses the larger radius halfway to the unit circle. -/
def outerRadius (n : ℕ) : ℝ := 1 - 1 / (2 * (n : ℝ))

/-- A single ordinary polynomial assembled from the row with cutoff n³. -/
def sectionPoly (u : ℕ → ℕ → ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ j ∈ range (n ^ 3 + 1), Polynomial.C (u (n ^ 3) j) * Polynomial.X ^ j

theorem sectionPoly_eval (u : ℕ → ℕ → ℂ) (n : ℕ) (z : ℂ) :
    (sectionPoly u n).eval z = ∑ j ∈ range (n ^ 3 + 1), u (n ^ 3) j * z ^ j := by
  simp [sectionPoly, Polynomial.eval_finsetSum]

/-- The measured row contributes coefficients only through degree `n³`. -/
theorem sectionPoly_natDegree_le (u : ℕ → ℕ → ℂ) (n : ℕ) :
    (sectionPoly u n).natDegree ≤ n^3 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ (mem_range.mp hj))

/-- Sharp upper Harnack bound on a closed disk, from the Poisson formula. -/
theorem harnack_closed {H : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hh : HarmonicOnNhd H (closedBall 0 R)) (hn : ∀ x ∈ sphere (0 : ℂ) R, 0 ≤ H x)
    {z : ℂ} (hz : ‖z‖ < R) :
    H z ≤ ((R + ‖z‖) / (R - ‖z‖)) * H 0 := by
  let K := Complex.re ∘ herglotzRieszKernel 0 z
  let c := (R + ‖z‖) / (R - ‖z‖)
  have hzR : z ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr hz
  have hC : ContinuousOn H (sphere 0 |R|) := by
    rw [abs_of_pos hR]
    exact hh.continuousOn.mono sphere_subset_closedBall
  have hK : ContinuousOn K (sphere 0 |R|) := by
    apply Complex.continuous_re.comp_continuousOn
    apply continuousOn_herglotzRieszKernel_sphere
    simpa [mem_sphere, abs_of_pos hR] using hz.ne
  have hav : circleAverage (K • H) 0 R ≤ circleAverage (c • H) 0 R := by
    apply circleAverage_mono (hK.smul hC).circleIntegrable' (continuousOn_const.smul hC).circleIntegrable'
    intro x hx
    have hxs : x ∈ sphere (0 : ℂ) R := by simpa [abs_of_pos hR] using hx
    exact mul_le_mul_of_nonneg_right (by
      simpa [K, c, herglotzRieszKernel_def] using re_herglotzRieszKernel_le hxs hzR) (hn x hxs)
  calc
    H z = _ := (hh.circleAverage_re_herglotzRieszKernel_smul hzR).symm
    _ ≤ _ := hav
    _ = _ := by
      rw [circleAverage_smul, InnerProductSpace.HarmonicOnNhd.circleAverage_eq (by simpa [abs_of_pos hR] using hh)]
      rfl

/-- Harnack's lower bound for the logarithm of the modulus on a zero-free disk. -/
theorem log_modulus_lower {f : ℂ → ℂ} {R B : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hne : ∀ w ∈ closedBall (0:ℂ) R, f w ≠ 0)
    (hb : ∀ w ∈ closedBall (0:ℂ) R, Real.log ‖f w‖ ≤ B) {z : ℂ} (hz : ‖z‖ < R) :
    B - (R+‖z‖)/(R-‖z‖) * (B-Real.log ‖f 0‖) ≤ Real.log ‖f z‖ := by
  let H : ℂ → ℝ := fun w ↦ B - Real.log ‖f w‖
  have hh : HarmonicOnNhd H (closedBall 0 R) := fun w hw ↦
    (harmonicAt_const B).sub ((hf w hw).harmonicAt_log_norm (hne w hw))
  have h := harnack_closed hR hh (fun w hw ↦ sub_nonneg.mpr (hb w (sphere_subset_closedBall hw))) hz
  dsimp [H] at h
  linarith

/-- Quantitative lower modulus bound for a zero-free analytic function. The same inequality
will be applied to the target function and to a zero-free measured polynomial. -/
theorem lower_modulus {f : ℂ → ℂ} {x R : ℝ} (hx : 0 < x) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hne : ∀ z ∈ closedBall (0 : ℂ) R, f z ≠ 0)
    (hb : ∀ z ∈ closedBall (0 : ℂ) R, ‖f z‖ ≤ Real.exp (x / 128))
    (h0 : -(x / 128) ≤ Real.log ‖f 0‖) {z : ℂ}
    (hz : ‖z‖ < R) (hr : (R + ‖z‖) / (R - ‖z‖) ≤ 4*x) :
    Real.exp (-x^2 / 8) < ‖f z‖ := by
  have hB (w : ℂ) (hw : w ∈ closedBall (0:ℂ) R) : Real.log ‖f w‖ ≤ x/128 := by
    simpa using Real.log_le_log (norm_pos_iff.mpr (hne w hw)) (hb w hw)
  have hh := log_modulus_lower hR hf hne hB hz
  have hB0 := hB 0 (by simpa using hR.le)
  have h1 := mul_le_mul_of_nonneg_right hr (sub_nonneg.mpr hB0)
  have h2 : x/128 - Real.log ‖f 0‖ ≤ x/64 := by linarith
  have he := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 4*x)
  rw [← Real.exp_log (norm_pos_iff.mpr (hne z (mem_closedBall_zero_iff.mpr hz.le))), Real.exp_lt_exp]
  nlinarith [sq_nonneg x]

/-- A polynomial radial bound is eventually smaller than any fixed positive exponential. -/
theorem eventually_poly_le_exp (C : ℝ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ k ≤ Real.exp ((n : ℝ) / 128) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k:ℝ) (1/128:ℝ) (by norm_num)).comp
    tendsto_natCast_atTop_atTop
  have ht := (h.const_mul C).eventually_lt_const (show C*0 < 1 by norm_num)
  filter_upwards [ht] with n hn
  simp only [Function.comp_def, Real.rpow_natCast] at hn
  have he : - (1/128:ℝ) * n = - ((n:ℝ)/128) := by ring
  rw [he, Real.exp_neg, ← mul_assoc, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)] at hn
  exact hn.le

/-- Relations between the measurement radius and the radius of the Cauchy estimate. -/
theorem radius_bounds (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ radius n ∧ radius n < outerRadius n ∧ outerRadius n < 1 ∧
    radius n ≤ (outerRadius n)^2 := by
  have hx : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hx1 : 1 ≤ (n:ℝ) := by exact_mod_cast (by omega : 1≤n)
  have h1 : 0 < 1/(2*(n:ℝ)) := by positivity
  have hr : 1/(n:ℝ) = 2*(1/(2*(n:ℝ))) := by field_simp
  unfold radius outerRadius
  refine ⟨sub_nonneg.mpr ((div_le_one hx).mpr hx1), ?_, ?_, ?_⟩
  · linarith
  · linarith
  · nlinarith [sq_nonneg (1/(2*(n:ℝ)))]

/-- The spatial Taylor remainder and the coefficient perturbation on the closed inner disk. -/
theorem section_error {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1)) (u : ℕ → ℕ → ℂ)
    (n : ℕ) (hn : 2 ≤ n) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ z, ‖z‖ ≤ outerRadius n → ‖f z‖ ≤ B)
    (he : ∀ j ≤ n^3, ‖u (n^3) j - DiskFiniteFourier.coeff f j‖ ≤ (1/2:ℝ)^(2*n^3))
    {z : ℂ} (hz : ‖z‖ ≤ radius n) :
    ‖(sectionPoly u n).eval z - f z‖ ≤ (2*(n:ℝ)*B + ((n:ℝ)^3 + 1)) * Real.exp (-(n:ℝ)^2/2) := by
  obtain ⟨hr0, hr, hR1, hrq⟩ := radius_bounds n hn
  have hR : 0 < outerRadius n := hr0.trans_lt hr
  have hx : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx1 : 1 ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  let q := ‖z‖ / outerRadius n
  have hq : 0 ≤ q := div_nonneg (norm_nonneg _) hR.le
  have hqu : q ≤ outerRadius n := (div_le_iff₀ hR).mpr (by rw [← sq]; exact hz.trans hrq)
  have hq1 : q < 1 := hqu.trans_lt hR1
  have hpow : q^(n^3+1) ≤ Real.exp (-(n:ℝ)^2/2) := by
    have hbase : q ≤ Real.exp (-(1/(2*(n:ℝ)))) := hqu.trans (by
      simpa only [outerRadius, sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(1/(2*(n:ℝ)))))
    calc
      _ ≤ q^(n^3) := pow_le_pow_of_le_one hq hq1.le (by omega)
      _ ≤ (Real.exp (-(1/(2*(n:ℝ)))))^(n^3) := pow_le_pow_left₀ hq hbase _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  have hden : (1-q)⁻¹ ≤ 2*(n:ℝ) := by
    rw [inv_le_iff_one_le_mul₀ (sub_pos.mpr hq1)]
    have hfrac : 1/(2*(n:ℝ)) ≤ 1-q := by unfold outerRadius at hqu; linarith
    have ht := mul_le_mul_of_nonneg_right hfrac (show 0 ≤ 2*(n:ℝ) by positivity)
    rw [div_mul_cancel₀ _ (by positivity)] at ht
    simpa only [mul_comm] using ht
  have ht := FiniteTaylor.norm_sub_partial_le (c := 0) (z := z) hR
    (hf.mono (closedBall_subset_ball hR1)) (fun w hw ↦ hb w (by simpa [mem_sphere] using le_of_eq (mem_sphere.mp hw))) (by simpa using hz.trans_lt hr) (n^3+1)
  simp only [sub_zero] at ht
  have ht' : ‖f z - FiniteTaylor.taylorSum f 0 z (n^3+1)‖ ≤
      (2*(n:ℝ)*B)*Real.exp (-(n:ℝ)^2/2) := by
    calc
      _ ≤ B*q^(n^3+1)*(1-q)⁻¹ := by simpa only [q, div_eq_mul_inv] using ht
      _ ≤ B*Real.exp (-(n:ℝ)^2/2)*(2*(n:ℝ)) := mul_le_mul
        (mul_le_mul_of_nonneg_left hpow hB) hden (by positivity) (by positivity)
      _ = _ := by ring
  have hbase : (1/2:ℝ) ≤ Real.exp (-(1/2:ℝ)) := by linarith [Real.add_one_le_exp (-(1/2:ℝ))]
  have hdy : (1/2:ℝ)^(2*n^3) ≤ Real.exp (-(n:ℝ)^2/2) := by
    calc
      _ ≤ (Real.exp (-(1/2:ℝ)))^(2*n^3) := pow_le_pow_left₀ (by norm_num) hbase _
      _ ≤ _ := by
        rw [← Real.exp_nat_mul, Real.exp_le_exp]
        push_cast
        nlinarith [mul_nonneg (sq_nonneg (n:ℝ)) (sub_nonneg.mpr hx1)]
  have hp : ‖(sectionPoly u n).eval z - FiniteTaylor.taylorSum f 0 z (n^3+1)‖ ≤
      ((n:ℝ)^3+1)*Real.exp (-(n:ℝ)^2/2) := by
    rw [sectionPoly_eval, FiniteTaylor.taylorSum, ← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j ∈ range (n^3+1), Real.exp (-(n:ℝ)^2/2) := Finset.sum_le_sum fun j hj ↦ by
        rw [show u (n^3) j*z^j - FiniteTaylor.term f 0 z j = (u (n^3) j - DiskFiniteFourier.coeff f j)*z^j by simp [FiniteTaylor.term, DiskFiniteFourier.coeff]; ring, norm_mul, norm_pow]
        exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hz.trans (hr.trans hR1).le))).trans ((he j (by have := mem_range.mp hj; omega)).trans hdy)
      _ = _ := by simp
  have htri := norm_sub_le_norm_sub_add_norm_sub (sectionPoly u n |>.eval z) (FiniteTaylor.taylorSum f 0 z (n^3+1)) (f z)
  rw [norm_sub_rev (FiniteTaylor.taylorSum f 0 z (n^3+1))] at htri
  linarith

/-- The tested polynomial has no zero in the entire closed disk of the stated radius. -/
def zeroFreeThrough (P : Polynomial ℂ) (R : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ R → P.eval z ≠ 0

/-- A finite root-multiset formulation that also handles the zero polynomial. -/
theorem zeroFreeThrough_iff_roots (P : Polynomial ℂ) {R : ℝ} (hR : 0 ≤ R) :
    zeroFreeThrough P R ↔ P ≠ 0 ∧ ∀ z ∈ P.roots, R < ‖z‖ := by
  constructor
  · intro h
    have hp : P ≠ 0 := by
      intro hz
      exact h 0 (by simpa using hR) (by simp [hz])
    exact ⟨hp, fun z hz ↦ lt_of_not_ge (fun hle ↦ h z hle ((Polynomial.mem_roots hp).mp hz))⟩
  · rintro ⟨hp, h⟩ z hz hzero
    exact (h z ((Polynomial.mem_roots hp).mpr hzero)).not_ge hz

/-- Uniform exponential approximation on the expanding closed disks. -/
theorem eventually_section_error {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (u : ℕ → ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C) {k : ℕ}
    (hg : ∀ᶠ n : ℕ in atTop, ∀ z, ‖z‖ ≤ outerRadius n → ‖f z‖ ≤ C * (n : ℝ)^k)
    (ha : ∀ᶠ m : ℕ in atTop, ∀ j ≤ m, ‖u m j - DiskFiniteFourier.coeff f j‖ ≤ (1/2:ℝ)^(2*m)) :
    ∀ᶠ n : ℕ in atTop, ∀ z, ‖z‖ ≤ radius n →
      ‖(sectionPoly u n).eval z - f z‖ ≤ Real.exp (-(n:ℝ)^2/4) := by
  have hcub : Tendsto (fun n : ℕ ↦ n^3) atTop atTop := tendsto_pow_atTop (by decide)
  filter_upwards [eventually_ge_atTop 2, hg, hcub.eventually ha,
    eventually_poly_le_exp (2*C+2) (k+3)] with n hn hgn han hexp
  have hx : 1 ≤ (n:ℝ) := by exact_mod_cast (by omega : 1≤n)
  have hk := pow_le_pow_right₀ hx (show k+1 ≤ k+3 by omega)
  have h3 := pow_le_pow_right₀ hx (show 3 ≤ k+3 by omega)
  have h1 := one_le_pow₀ hx (n := k+3)
  have hcoef : 2*(n:ℝ)*(C*(n:ℝ)^k)+((n:ℝ)^3+1) ≤ (2*C+2)*(n:ℝ)^(k+3) := by
    calc
      _ = (2*C)*(n:ℝ)^(k+1)+(n:ℝ)^3+1 := by rw [pow_succ]; ring
      _ ≤ (2*C)*(n:ℝ)^(k+3)+(n:ℝ)^(k+3)+(n:ℝ)^(k+3) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hk (by positivity)) h3) h1
      _ = _ := by ring
  intro z hz
  calc
    _ ≤ _ := section_error hf u n hn (by positivity) hgn han hz
    _ ≤ Real.exp ((n:ℝ)/128) * Real.exp (-(n:ℝ)^2/2) :=
      mul_le_mul_of_nonneg_right (hcoef.trans hexp) (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith [mul_nonneg (sub_nonneg.mpr hx) (show 0≤(n:ℝ) by positivity)]

private theorem ratio {x R t : ℝ} (hx : 0 < x) (hR : R ≤ 1) (ht : t ≤ 1)
    (hd : 1/(2*x) ≤ R-t) : t < R ∧ (R+t)/(R-t) ≤ 4*x := by
  have hpos : 0 < 1/(2*x) := by positivity
  have hd' : 0 < R-t := hpos.trans_le hd
  refine ⟨sub_pos.mp hd', (div_le_iff₀ hd').mpr ?_⟩
  calc
    R+t ≤ 2 := by linarith only [hR, ht]
    _ = 4*x*(1/(2*x)) := by field_simp; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)

private theorem outer_ratio (n : ℕ) (hn : 2 ≤ n) {z : ℂ} (hz : ‖z‖ ≤ radius n) :
    ‖z‖ < outerRadius n ∧ (outerRadius n+‖z‖)/(outerRadius n-‖z‖) ≤ 4*(n:ℝ) := by
  obtain ⟨_, hro, ho1, _⟩ := radius_bounds n hn
  have hx : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
  apply ratio hx ho1.le (hz.trans (hro.trans ho1).le)
  have hid : 1/(n:ℝ) = 2*(1/(2*(n:ℝ))) := by field_simp
  unfold radius at hz
  unfold outerRadius
  linarith

/-- With a radial bound `‖f‖ ≤ C n^k`, the choice `B = log (C n^k)` yields an explicit
lower bound of order `-n log n` for the logarithm of the modulus on the test disk. -/
theorem log_modulus_lower_on_radius {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hne : ∀ w : ℂ, ‖w‖ < 1 → f w ≠ 0) (n : ℕ) (hn : 2 ≤ n) {B : ℝ}
    (hb : ∀ w, ‖w‖ ≤ outerRadius n → Real.log ‖f w‖ ≤ B) {z : ℂ} (hz : ‖z‖ ≤ radius n) :
    B - 4*(n:ℝ)*(B - Real.log ‖f 0‖) ≤ Real.log ‖f z‖ := by
  obtain ⟨hr0, hro, ho1, _⟩ := radius_bounds n hn
  have hR := hr0.trans_lt hro
  have hrat := outer_ratio n hn hz
  have hlog := log_modulus_lower hR (hf.mono (closedBall_subset_ball ho1))
    (fun w hw ↦ hne w ((mem_closedBall_zero_iff.mp hw).trans_lt ho1))
    (fun w hw ↦ hb w (mem_closedBall_zero_iff.mp hw)) hrat.1
  have hcenter := hb 0 (by simpa using hR.le)
  linarith [mul_le_mul_of_nonneg_right hrat.2 (sub_nonneg.mpr hcenter)]

private theorem eventually_control {f : ℂ → ℂ} {C : ℝ} {k : ℕ}
    (hg : ∀ᶠ n : ℕ in atTop, ∀ z, ‖z‖ ≤ outerRadius n → ‖f z‖ ≤ C * (n : ℝ)^k) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧
      (-(n:ℝ)/128 ≤ Real.log (‖f 0‖/2)) ∧
      (∀ z, ‖z‖ ≤ outerRadius n → ‖f z‖+1 ≤ Real.exp ((n:ℝ)/128)) := by
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    (-128*Real.log (‖f 0‖/2))
  filter_upwards [eventually_ge_atTop 2, ht, hg, eventually_poly_le_exp (C+1) k]
    with n hn hlog hgn hexp
  refine ⟨hn, by linarith, fun z hz ↦ ?_⟩
  have hx : 1 ≤ (n:ℝ) := by exact_mod_cast (by omega : 1≤n)
  calc
    ‖f z‖+1 ≤ C*(n:ℝ)^k+(n:ℝ)^k := add_le_add (hgn z hz) (one_le_pow₀ hx)
    _ = (C+1)*(n:ℝ)^k := by ring
    _ ≤ _ := hexp

private theorem error_vs_lower {x : ℝ} (hx : 1 ≤ x) :
    Real.exp (-x^2/4) ≤ Real.exp (-x^2/8) ∧
    Real.exp (-x^2/4) ≤ Real.exp (-x/128) ∧ Real.exp (-x^2/4) ≤ 1 := by
  rw [Real.exp_le_exp, Real.exp_le_exp, Real.exp_le_one_iff]
  have hsq := mul_nonneg (sub_nonneg.mpr hx) (by linarith : 0≤x)
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg x]

/-- A holomorphic disk function with nonzero center and polynomial growth is zero-free if and
only if all sufficiently large measured sections are zero-free on their respective disks, or
equivalently if that single-stage test succeeds at arbitrarily large indices. -/
theorem zeroFree_iff_sections {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (h0 : f 0 ≠ 0) (u : ℕ → ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C) {k : ℕ}
    (hg : ∀ᶠ n : ℕ in atTop, ∀ z, ‖z‖ ≤ outerRadius n → ‖f z‖ ≤ C * (n : ℝ)^k)
    (ha : ∀ᶠ m : ℕ in atTop, ∀ j ≤ m, ‖u m j - DiskFiniteFourier.coeff f j‖ ≤ (1/2:ℝ)^(2*m)) :
    ((∀ z : ℂ, ‖z‖ < 1 → f z ≠ 0) ↔
      ∀ᶠ n : ℕ in atTop, zeroFreeThrough (sectionPoly u n) (radius n)) ∧
    ((∀ z : ℂ, ‖z‖ < 1 → f z ≠ 0) ↔
      ∀ N : ℕ, ∃ n ≥ N, zeroFreeThrough (sectionPoly u n) (radius n)) := by
  have herr := eventually_section_error hf u hC hg ha
  have hcontrol := eventually_control hg
  have h0pos : 0 < ‖f 0‖/2 := by positivity
  have forward (hfne : ∀ z : ℂ, ‖z‖ < 1 → f z ≠ 0) :
      ∀ᶠ n : ℕ in atTop, zeroFreeThrough (sectionPoly u n) (radius n) := by
    filter_upwards [herr, hcontrol] with n he hc
    obtain ⟨hn, hlog, hb⟩ := hc
    obtain ⟨hr0, hro, ho1, _⟩ := radius_bounds n hn
    have hx : 1 ≤ (n:ℝ) := by exact_mod_cast (by omega : 1≤n)
    have hxp : 0 < (n:ℝ) := by positivity
    intro z hz hP
    have hrat := outer_ratio n hn hz
    have hlo := lower_modulus hxp (hr0.trans_lt hro)
      (hf.mono (closedBall_subset_ball ho1))
      (fun w hw ↦ hfne w ((mem_closedBall_zero_iff.mp hw).trans_lt ho1))
      (fun w hw ↦ by have := hb w (mem_closedBall_zero_iff.mp hw); linarith)
      (by have := Real.log_le_log h0pos (show ‖f 0‖/2 ≤ ‖f 0‖ by linarith); linarith)
      hrat.1 hrat.2
    have hh := he z hz
    rw [hP, zero_sub, norm_neg] at hh
    linarith [(error_vs_lower hx).1]
  have cofinal (h : ∀ᶠ n : ℕ in atTop, zeroFreeThrough (sectionPoly u n) (radius n)) :
      ∀ N : ℕ, ∃ n ≥ N, zeroFreeThrough (sectionPoly u n) (radius n) :=
    fun N ↦ ((eventually_ge_atTop N).and h).exists
  have reverse (hc : ∀ N : ℕ, ∃ n ≥ N, zeroFreeThrough (sectionPoly u n) (radius n)) :
      ∀ z : ℂ, ‖z‖ < 1 → f z ≠ 0 := by
    intro z hz hzero
    have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2/(1-‖z‖))
    obtain ⟨N, hN⟩ := eventually_atTop.1 (herr.and (hcontrol.and ht))
    obtain ⟨n, hnN, hp⟩ := hc N
    obtain ⟨he, ⟨hn, hlog, hb⟩, hcut⟩ := hN n hnN
    obtain ⟨hr0, hro, ho1, _⟩ := radius_bounds n hn
    have hx : 1 ≤ (n:ℝ) := by exact_mod_cast (by omega : 1≤n)
    have hxp : 0 < (n:ℝ) := by positivity
    have hg : 2/(n:ℝ) ≤ 1-‖z‖ := (div_le_iff₀ hxp).mpr (by
      have ht' := (div_le_iff₀ (sub_pos.mpr hz)).mp hcut
      linarith)
    have hrat := ratio hxp (hro.trans ho1).le hz.le (by
      have h1 : 1/(n:ℝ)=2*(1/(2*(n:ℝ))) := by field_simp
      have h2 : 2/(n:ℝ)=4*(1/(2*(n:ℝ))) := by field_simp; norm_num
      have h3 : 0 ≤ 1/(2*(n:ℝ)) := by positivity
      unfold radius
      linarith)
    have hz0 : ‖(0:ℂ)‖ ≤ radius n := by simpa using hr0
    have he0 := he 0 hz0
    have hexp0 : Real.exp (-(n:ℝ)^2/4) ≤ ‖f 0‖/2 := calc
      _ ≤ Real.exp (-(n:ℝ)/128) := (error_vs_lower hx).2.1
      _ ≤ Real.exp (Real.log (‖f 0‖/2)) := Real.exp_le_exp.mpr hlog
      _ = _ := Real.exp_log h0pos
    have hcenter : ‖f 0‖/2 ≤ ‖(sectionPoly u n).eval 0‖ := by
      have htri := norm_le_norm_sub_add (f 0) ((sectionPoly u n).eval 0)
      rw [norm_sub_rev] at htri
      linarith
    have hpA : AnalyticOnNhd ℂ (fun w ↦ (sectionPoly u n).eval w) (closedBall 0 (radius n)) :=
      fun _ _ ↦ Complex.analyticAt_iff_eventually_differentiableAt.mpr
        (Eventually.of_forall fun _ ↦ (sectionPoly u n).differentiableAt)
    have hrpos : 0 < radius n := (norm_nonneg z).trans_lt hrat.1
    have hlo := lower_modulus hxp hrpos hpA
      (fun w hw ↦ hp w (mem_closedBall_zero_iff.mp hw))
      (fun w hw ↦ by
        have hw' := mem_closedBall_zero_iff.mp hw
        have hb' := hb w (hw'.trans hro.le)
        have he' := he w hw'
        have htri := norm_le_norm_sub_add ((sectionPoly u n).eval w) (f w)
        linarith [(error_vs_lower hx).2.2])
      (by have := Real.log_le_log h0pos hcenter; linarith) hrat.1 hrat.2
    have hh := he z hrat.1.le
    rw [hzero, sub_zero] at hh
    linarith [(error_vs_lower hx).1]
  exact ⟨⟨forward, reverse ∘ cofinal⟩, ⟨cofinal ∘ forward, reverse⟩⟩

end RiemannMasullo.ExpandingTaylor
