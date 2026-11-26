module

public import RiemannMasullo.ForMathlib.Analysis.Complex.LogDerivativeCoefficients
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-! # Carathéodory bounds for logarithmic Taylor coefficients on a zero-free disk -/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory Metric Set
open scoped Topology ComplexConjugate

namespace RiemannMasullo.DiskLogCoefficient

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

private theorem argument_norm {r : ℝ} (hr : 0 < r) (x : AddCircle (1 : ℝ)) :
    ‖(r : ℂ) * fourier 1 x‖ = r := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    show ‖fourier 1 x‖ = 1 from Circle.norm_coe _, mul_one]

private def radial (g : ℂ → ℂ) (r : ℝ) (x : AddCircle (1 : ℝ)) : ℂ :=
  g ((r : ℂ)*fourier 1 x)

private def radii (g : ℂ → ℂ) (r : ℝ) : ℤ → ℂ :=
  Int.rec (fun k ↦ coeff g k * (r : ℂ)^k) (fun _ ↦ 0)

private theorem radial_fourier {g : ℂ → ℂ} {r R : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hr : 0 < r) (hu : r < R) :
    fourierCoeff (radial g r) = radii g r := by
  apply fourierCoeff_eq_of_hasSum
  intro x
  have hpow (j : ℕ) : fourier (j : ℤ) x = (fourier 1 x)^j := by
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.cast_succ, fourier_add, ih, pow_succ]
  have hz : (r : ℂ)*fourier 1 x ∈ ball (0 : ℂ) R :=
    mem_ball_zero_iff.mpr ((argument_norm hr x).trans_lt hu)
  have hp : HasSum (fun j : ℕ ↦ fourier (j : ℤ) x • radii g r j) (radial g r x) := by
    apply (Complex.hasSum_taylorSeries_on_ball hg hz).congr_fun
    intro j
    change fourier (j : ℤ) x * (coeff g j * (r : ℂ)^j) = _
    simp [coeff, smul_eq_mul, hpow, mul_pow, div_eq_mul_inv]
    ring
  have hn : HasSum (fun j : ℕ ↦ fourier (-(j + 1) : ℤ) x • radii g r (-(j+1) : ℤ)) 0 := by
    convert hasSum_zero (β := ℕ) (α := ℂ) using 1
    funext j
    change fourier (Int.negSucc j) x • (0 : ℂ) = 0
    simp
  simpa using hp.of_nat_of_neg_add_one (f := fun i : ℤ ↦ fourier i x • radii g r i) hn

private theorem conj_fourier (v : AddCircle (1 : ℝ) → ℂ) (j : ℤ) :
    fourierCoeff (fun x ↦ conj (v x)) j = conj (fourierCoeff v (-j)) := by
  unfold fourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [neg_neg, smul_eq_mul, map_mul, fourier_neg]

private theorem caratheodory_inner {g : ℂ → ℂ} {r R : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hpos : ∀ z ∈ ball 0 R, 0 ≤ (g z).re)
    (hr : 0 < r) (hu : r < R) (k : ℕ) :
    ‖coeff g (k+1)‖ * r^(k+1) ≤ 2 * (g 0).re := by
  let v := radial g r
  let μ : Measure (AddCircle (1 : ℝ)) := AddCircle.haarAddCircle
  have hz (x : AddCircle (1:ℝ)) : (r : ℂ)*fourier 1 x ∈ ball (0:ℂ) R :=
    mem_ball_zero_iff.mpr ((argument_norm hr x).trans_lt hu)
  have hc : Continuous v :=
    hg.continuousOn.comp_continuous (continuous_const.mul (fourier (T := 1) 1).continuous) hz
  have hv : Integrable v μ := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ha := radial_fourier hg hr hu
  have hzero : ∫ x, v x ∂μ = g 0 := by
    have h := congrFun ha (0 : ℤ)
    change fourierCoeff (radial g r) 0 = coeff g 0 * (r : ℂ)^0 at h
    simpa [fourierCoeff, coeff, v, μ] using h
  have hneg : fourierCoeff v (-(k+1):ℤ) = 0 := congrFun ha _
  have hp : fourierCoeff v ((k+1 : ℕ) : ℤ) = coeff g (k+1)*(r : ℂ)^(k+1) := congrFun ha _
  let h : AddCircle (1 : ℝ) → ℂ := fun x ↦ 2 * ((v x).re : ℂ)
  have he : h = v + (fun x ↦ conj (v x)) := by
    funext x
    simpa only [h, Pi.add_apply, Complex.ofReal_mul, Complex.ofReal_ofNat] using (Complex.add_conj (v x)).symm
  have hcj : Integrable (fun x ↦ conj (v x)) μ :=
    (continuous_conj.comp hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc0 : fourierCoeff h ((k+1 : ℕ) : ℤ) = coeff g (k+1)*(r:ℂ)^(k+1) := by
    rw [he, fourierCoeff.add hv hcj, Pi.add_apply, conj_fourier, hp]
    simp only [Nat.cast_add, Nat.cast_one, hneg, map_zero, add_zero]
  have hn : ‖fourierCoeff h ((k+1 : ℕ) : ℤ)‖ ≤ ∫ x, 2*(v x).re ∂μ := by
    change ‖∫ x, fourier _ x • h x ∂μ‖ ≤ _
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    apply integral_congr_ae
    filter_upwards with x
    rw [norm_smul, show ‖fourier _ x‖=1 from Circle.norm_coe _, one_mul]
    have hx : 0 ≤ (v x).re := hpos _ (hz x)
    simp [h, abs_of_nonneg hx]
  rw [hc0, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hn
  have hinter : (∫ x, (v x).re ∂μ) = (g 0).re := (integral_re hv).trans (congrArg Complex.re hzero)
  rw [integral_const_mul, hinter] at hn
  exact hn

/-- The sharp Carathéodory estimate for the positive Taylor coefficients on an open disk. -/
theorem coeff_mul_radius_le_two_re {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hpos : ∀ z ∈ ball 0 R, 0 ≤ (g z).re) (k : ℕ) :
    ‖coeff g (k+1)‖ * R^(k+1) ≤ 2 * (g 0).re := by
  apply le_of_tendsto (f := fun u : ℝ ↦ ‖coeff g (k+1)‖ * u^(k+1))
    (x := 𝓝[<] R) ((show Continuous (fun u : ℝ ↦ ‖coeff g (k+1)‖ * u^(k+1)) by fun_prop).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [Ioo_mem_nhdsLT_of_mem (show R ∈ Ioc 0 R from ⟨hR, le_rfl⟩)] with u hu
  exact caratheodory_inner hg hpos hu.1 hu.2 k

private theorem coeff_derivative (p : ℂ → ℂ) (k : ℕ) :
    coeff (deriv p) k = ((k+1 : ℕ) : ℂ) * coeff p (k+1) := by
  rw [coeff, coeff, iteratedDeriv_succ', Nat.factorial_succ, Nat.cast_mul]
  have hk : ((k+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  field_simp

/-- A bounded zero-free function controls the Taylor coefficients of its logarithmic derivative
by its norm bound divided by the norm of its center value. -/
theorem norm_logDeriv_coeff_le {f : ℂ → ℂ} {R B : ℝ} (hR : 0 < R)
    (ha : AnalyticOnNhd ℂ f (ball 0 R)) (hn : ∀ z ∈ ball 0 R, f z ≠ 0)
    (hb : ∀ z ∈ ball 0 R, ‖f z‖ ≤ B) (k : ℕ) :
    ‖coeff (logDeriv f) k‖ * R^(k+1) ≤
      2 * ((k+1 : ℕ) : ℝ) * Real.log (B / ‖f 0‖) := by
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hfn := norm_pos_iff.mpr (hn 0 h0)
  have hB : 0 < B := hfn.trans_le (hb 0 h0)
  have hd : DifferentiableOn ℂ (logDeriv f) (ball 0 R) :=
    fun z hz ↦ ((ha z hz).deriv.div (ha z hz) (hn z hz)).differentiableAt.differentiableWithinAt
  obtain ⟨p, hp0, hp⟩ := hd.isExactOn_ball.with_val_at 0 0
  let e (z : ℂ) := Complex.exp (p z)
  have hed : DifferentiableOn ℂ e (ball 0 R) :=
    fun z hz ↦ (hp z hz).cexp.differentiableAt.differentiableWithinAt
  have heq : EqOn (logDeriv f) (logDeriv e) (ball 0 R) := by
    intro z hz
    change logDeriv f z = deriv (fun z ↦ Complex.exp (p z)) z / Complex.exp (p z)
    rw [(hp z hz).cexp.deriv]
    field_simp [Complex.exp_ne_zero]
  obtain ⟨c, _, hc⟩ := (logDeriv_eqOn_iff ha.differentiableOn hed isOpen_ball
    (convex_ball (0 : ℂ) R).isPreconnected (fun z _ ↦ Complex.exp_ne_zero (p z)) hn).mp heq
  have hc0 : f 0 = c := by simpa [e, hp0] using hc h0
  let M := Real.log (B / ‖f 0‖)
  have hupper (z : ℂ) (hz : z ∈ ball 0 R) : (p z).re ≤ M := by
    apply (Real.le_log_iff_exp_le (div_pos hB hfn)).mpr
    rw [← Complex.norm_exp]
    apply (le_div_iff₀ hfn).mpr
    have hh : ‖f z‖ = ‖f 0‖ * ‖Complex.exp (p z)‖ := by
      simpa only [e, Pi.smul_apply, smul_eq_mul, norm_mul, ← hc0] using congrArg norm (hc hz)
    rw [mul_comm, ← hh]
    exact hb z hz
  let g (z : ℂ) := (M : ℂ) - p z
  have hg : DifferentiableOn ℂ g (ball 0 R) := fun z hz ↦
    ((hp z hz).differentiableAt.const_sub (M : ℂ)).differentiableWithinAt
  have hh := coeff_mul_radius_le_two_re hR hg
    (fun z hz ↦ by simpa only [g, sub_re, ofReal_re, sub_nonneg] using hupper z hz) k
  have hcoef : coeff g (k+1) = -coeff p (k+1) := by
    simp only [coeff, g, iteratedDeriv_const_sub (Nat.zero_lt_succ k), iteratedDeriv_neg, neg_div]
  rw [hcoef, norm_neg, show (g 0).re = M by simp [g, hp0]] at hh
  have hder : logDeriv f =ᶠ[𝓝 0] deriv p := by
    filter_upwards [isOpen_ball.mem_nhds h0] with z hz
    exact (hp z hz).deriv.symm
  have hcoef' : coeff (logDeriv f) k = coeff (deriv p) k :=
    congrArg (fun v : ℂ ↦ v / k.factorial) (hder.iteratedDeriv_eq k)
  rw [hcoef', coeff_derivative, norm_mul, Complex.norm_natCast, mul_assoc]
  calc
    ((k+1 : ℕ) : ℝ) * (‖coeff p (k+1)‖ * R^(k+1)) ≤ ((k+1 : ℕ) : ℝ) * (2*M) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = 2 * ((k+1 : ℕ) : ℝ) * M := by ring

/-- Multiplication by `1-z` subtracts exactly one from each positive logarithmic moment.
A uniform bound for this product gives a signed estimate for the original function. -/
theorem abs_logDeriv_coeff_re_sub_one_le {g : ℂ → ℂ} {R B : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (ha : AnalyticOnNhd ℂ g (ball 0 R)) (hn : ∀ z ∈ ball 0 R, g z ≠ 0)
    (hb : ∀ z ∈ ball 0 R, ‖(1-z)*g z‖ ≤ B) (k : ℕ) :
    |(coeff (logDeriv g) k).re - 1| * R^(k+1) ≤
      2 * ((k+1 : ℕ) : ℝ) * Real.log (B / ‖g 0‖) := by
  let u (z : ℂ) := 1-z
  let f := u*g
  have hu : ∀ z ∈ ball 0 R, u z ≠ 0 := by
    intro z hz h
    have hz1 : z=1 := (sub_eq_zero.mp h).symm
    have hzt := (mem_ball_zero_iff.mp hz).trans_le hR1
    simp [hz1] at hzt
  have hau : AnalyticOnNhd ℂ u (ball 0 R) := fun _ _ ↦ analyticAt_const.sub analyticAt_id
  have he := norm_logDeriv_coeff_le hR (hau.mul ha) (fun z hz ↦ mul_ne_zero (hu z hz) (hn z hz)) hb k
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hd : logDeriv f =ᶠ[𝓝 0] (fun z : ℂ ↦ 1/(z-1) + logDeriv g z) := by
    filter_upwards [isOpen_ball.mem_nhds h0] with z hz
    rw [logDeriv_mul z (hu z hz) (hn z hz) (hau z hz).differentiableAt (ha z hz).differentiableAt]
    congr 1
    change deriv (fun z : ℂ ↦ 1-z) z / (1-z) = 1/(z-1)
    have hder : HasDerivAt (fun y : ℂ ↦ 1-y) (0-1) z := (hasDerivAt_const z 1).sub (hasDerivAt_id z)
    rw [hder.deriv, ← neg_sub 1 z, div_neg]
    ring
  have hpa : AnalyticAt ℂ (fun z : ℂ ↦ 1/(z-1)) 0 :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (by norm_num)
  have hga := (ha 0 h0).deriv.div (ha 0 h0) (hn 0 h0)
  have hcalc : coeff (logDeriv f) k = coeff (logDeriv g) k - 1 := by
    rw [coeff, hd.iteratedDeriv_eq k, iteratedDeriv_fun_add hpa.contDiffAt
      (show AnalyticAt ℂ (logDeriv g) 0 from hga).contDiffAt, add_div]
    change coeff (fun z : ℂ ↦ 1/(z-1)) k + coeff (logDeriv g) k = _
    rw [coeff_pole]
    ring
  change ‖coeff (logDeriv f) k‖ * R^(k+1) ≤ 2 * ((k+1 : ℕ) : ℝ) * Real.log (B/‖u 0*g 0‖) at he
  rw [hcalc, show u 0=1 by simp [u], one_mul] at he
  exact (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm (coeff (logDeriv g) k-1)) (by positivity)).trans he

end RiemannMasullo.DiskLogCoefficient
