module

public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.Topology.Algebra.Support

/-!
# A signed prime profile and Chebyshev's function

For a `C¹` test supported in a bounded positive log interval, the degree-one sum
`∑_p (log p) p^{-1/2} H(log p - y)` equals `e^{y/2} ∫ H(u) e^{u/2} du` minus the
integral of the profile's derivative against `θ(t) - t`. The prime number theorem
then gives
`e^{-y/2} ∑_p (log p) p^{-1/2} H(log p - y) → ∫ H(u) e^{u/2} du`.
This is the partial-summation step for the rational local terms of Theorem 12.5.1.1,
pp. 519–520. When the half-moment of `H` vanishes, the same identity says that the
degree-one sum is the integral against Chebyshev's error `θ(t) - t`, and the prime
number theorem makes it `o(e^{y/2})`. Mathlib's prime number theorem has no rate, so
no power saving is claimed.
-/

@[expose] public section

open Chebyshev Finset Filter MeasureTheory Set Topology intervalIntegral
open scoped Interval

namespace RiemannMasullo

/-- `log p` on primes and `0` elsewhere, so the partial sums are Chebyshev's `θ`. -/
noncomputable def chebyshevCoeff (k : ℕ) : ℝ :=
  if k.Prime then Real.log k else 0

theorem sum_chebyshevCoeff_eq_theta (t : ℝ) :
    ∑ k ∈ Icc 0 ⌊t⌋₊, chebyshevCoeff k = θ t := by
  simp [chebyshevCoeff, theta_eq_sum_Icc, sum_filter]

/-- `t^{-1/2} H(log t - y)`, written so its derivative stays away from the branch of `rpow`. -/
noncomputable def halfProfile (H : ℝ → ℝ) (y t : ℝ) : ℝ :=
  Real.exp (-(1 / 2) * Real.log t) * H (Real.log t - y)

theorem halfProfile_hasDerivAt {H : ℝ → ℝ} {y t : ℝ} (ht : 0 < t)
    (hH : HasDerivAt H (deriv H (Real.log t - y)) (Real.log t - y)) :
    HasDerivAt (halfProfile H y)
      (Real.exp (-(1 / 2) * Real.log t) * t⁻¹ *
        (-(1 / 2) * H (Real.log t - y) + deriv H (Real.log t - y))) t := by
  have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht.ne'
  have harg : HasDerivAt (fun s : ℝ => Real.log s - y) t⁻¹ t := hlog.sub_const y
  have hcoeff : HasDerivAt (fun s : ℝ => -(1 / 2) * Real.log s) (-(1 / 2) * t⁻¹) t :=
    hlog.const_mul (-(1 / 2))
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(1 / 2) * Real.log s))
      (Real.exp (-(1 / 2) * Real.log t) * (-(1 / 2) * t⁻¹)) t :=
    hcoeff.exp
  have hHcomp : HasDerivAt (fun s : ℝ => H (Real.log s - y))
      (deriv H (Real.log t - y) * t⁻¹) t :=
    hH.comp t harg
  refine (hexp.mul hHcomp).congr_deriv ?_
  ring

theorem halfProfile_eq_zero_of_argument {H : ℝ → ℝ} {b y t : ℝ}
    (hsupp : tsupport H ⊆ Ioo 0 b)
    (hu : Real.log t - y ∉ Ioo 0 b) : halfProfile H y t = 0 := by
  have hH : H (Real.log t - y) = 0 := by
    by_contra hne
    have : Real.log t - y ∈ tsupport H :=
      subset_closure (Function.mem_support.mpr hne)
    exact hu (hsupp this)
  simp [halfProfile, hH]

/-- The degree-one signed prime sum at scale `e^y`. Primes outside the support of `H`
contribute nothing. -/
noncomputable def radialPrimeProfile (H : ℝ → ℝ) (b y : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Real.exp (y + b)⌋₊,
    Real.log (p : ℝ) * (p : ℝ) ^ (-(1 / 2 : ℝ)) * H (Real.log (p : ℝ) - y)

private theorem halfProfile_mul_chebyshevCoeff (H : ℝ → ℝ) (y : ℝ) (k : ℕ) (hk : 0 < k) :
    halfProfile H y k * chebyshevCoeff k =
      if k.Prime then Real.log (k : ℝ) * (k : ℝ) ^ (-(1 / 2 : ℝ)) * H (Real.log (k : ℝ) - y)
      else 0 := by
  by_cases hprime : k.Prime
  · have hpos : (0 : ℝ) < k := by exact_mod_cast hk
    simp [chebyshevCoeff, hprime, halfProfile, Real.rpow_def_of_pos hpos]
    rw [mul_comm (2⁻¹) (Real.log (k : ℝ))]
    ring
  · simp [chebyshevCoeff, hprime]

private theorem radialPrimeProfile_eq_sum {H : ℝ → ℝ} {b y : ℝ} (_hy : 0 ≤ y) (_hb : 0 < b)
    (hsupp : tsupport H ⊆ Ioo 0 b) :
    radialPrimeProfile H b y =
      ∑ k ∈ Ioc ⌊Real.exp y⌋₊ ⌊Real.exp (y + b)⌋₊,
        halfProfile H y k * chebyshevCoeff k := by
  classical
  set A := Real.exp y
  set B := Real.exp (y + b)
  have hA : (0 : ℝ) < A := Real.exp_pos _
  have hAB : A ≤ B := Real.exp_le_exp.mpr (by linarith)
  have hfloor : ⌊A⌋₊ ≤ ⌊B⌋₊ := Nat.floor_le_floor hAB
  have hbelow (k : ℕ) (hk : k ∈ Finset.Icc 0 ⌊A⌋₊) :
      halfProfile H y k * chebyshevCoeff k = 0 := by
    by_cases hk0 : k = 0
    · simp [hk0, chebyshevCoeff]
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hkreal : 0 < (k : ℝ) := by exact_mod_cast hkpos
    have hlog : Real.log (k : ℝ) - y ≤ 0 := by
      have hkle : (k : ℝ) ≤ A :=
        (by exact_mod_cast (Finset.mem_Icc.mp hk).2 : (k : ℝ) ≤ ⌊A⌋₊).trans (Nat.floor_le hA.le)
      simpa [Real.log_exp, A] using sub_nonpos.mpr (Real.log_le_log hkreal hkle)
    have hu : Real.log (k : ℝ) - y ∉ Ioo 0 b := fun h => not_le.mpr h.1 hlog
    simp [halfProfile_eq_zero_of_argument hsupp hu]
  have hupper :
      ∑ k ∈ Finset.Icc 0 ⌊B⌋₊, halfProfile H y k * chebyshevCoeff k = radialPrimeProfile H b y := by
    rw [radialPrimeProfile, Nat.primesLE_eq_filter_Icc_zero, sum_filter]
    refine sum_congr rfl fun k _hk => ?_
    by_cases hk0 : k = 0
    · simp [hk0, chebyshevCoeff]
    exact halfProfile_mul_chebyshevCoeff H y k (Nat.pos_of_ne_zero hk0)
  have hlower : ∑ k ∈ Finset.Icc 0 ⌊A⌋₊, halfProfile H y k * chebyshevCoeff k = 0 :=
    sum_eq_zero hbelow
  have hdisj : Disjoint (Finset.Icc 0 ⌊A⌋₊) (Finset.Ioc ⌊A⌋₊ ⌊B⌋₊) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk hk'
    omega
  have hunion : Finset.Icc 0 ⌊A⌋₊ ∪ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊ = Finset.Icc 0 ⌊B⌋₊ := by
    ext k
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hsplit := sum_union (f := fun (k : ℕ) => halfProfile H y (k : ℝ) * chebyshevCoeff k) hdisj
  rw [hunion, hlower, zero_add, hupper] at hsplit
  exact hsplit

/-- Abel summation, with the profile vanishing at both ends of its log window:
the signed prime sum is minus the integral of its derivative against `θ`. -/
theorem radialPrimeProfile_eq_neg_integral_theta {H : ℝ → ℝ} {b y : ℝ}
    (hy : 1 ≤ y) (hb : 0 < b) (hsupp : tsupport H ⊆ Set.Ioo 0 b) (hH : ContDiff ℝ 1 H) :
    radialPrimeProfile H b y =
      - ∫ t in Real.exp y..Real.exp (y + b), deriv (halfProfile H y) t * θ t := by
  classical
  set A := Real.exp y
  set B := Real.exp (y + b)
  have hy0 : 0 ≤ y := hy.trans' (by norm_num)
  have hA0 : 0 < A := Real.exp_pos _
  have hAB : A ≤ B := Real.exp_le_exp.mpr (by linarith)
  have hHderiv (x : ℝ) : HasDerivAt H (deriv H x) x :=
    ((hH.differentiable one_ne_zero).differentiableAt).hasDerivAt
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc A B) :
      HasDerivAt (halfProfile H y)
        (Real.exp (-(1 / 2) * Real.log t) * t⁻¹ *
          (-(1 / 2) * H (Real.log t - y) + deriv H (Real.log t - y))) t :=
    halfProfile_hasDerivAt (lt_of_lt_of_le hA0 ht.1) (hHderiv _)
  have hboundA : halfProfile H y A = 0 := by
    apply halfProfile_eq_zero_of_argument (t := A) hsupp
    simp [A, Real.log_exp, Set.Ioo]
  have hboundB : halfProfile H y B = 0 := by
    apply halfProfile_eq_zero_of_argument (t := B) hsupp
    simp [B, Real.log_exp, Set.Ioo]
  have hdiff (t : ℝ) (ht : t ∈ Set.Icc A B) : DifferentiableAt ℝ (halfProfile H y) t :=
    (hderiv t ht).differentiableAt
  have hint : IntegrableOn (deriv (halfProfile H y)) (Set.Icc A B) := by
    let φ (t : ℝ) : ℝ := Real.exp (-(1 / 2) * Real.log t) * t⁻¹ *
      (-(1 / 2) * H (Real.log t - y) + deriv H (Real.log t - y))
    have hcont : ContinuousOn φ (Set.Icc A B) := by
      have hlog : ContinuousOn Real.log (Set.Icc A B) :=
        Real.continuousOn_log.mono fun t ht => (lt_of_lt_of_le hA0 ht.1).ne'
      have hexp : ContinuousOn (fun t => Real.exp (-(1 / 2) * Real.log t)) (Set.Icc A B) :=
        Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hlog)
      have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc A B) :=
        continuousOn_inv₀.mono fun t ht => (lt_of_lt_of_le hA0 ht.1).ne'
      have hHcont : ContinuousOn (fun t => H (Real.log t - y)) (Set.Icc A B) :=
        hH.continuous.comp_continuousOn (hlog.sub continuousOn_const)
      have hH' : ContinuousOn (fun t => deriv H (Real.log t - y)) (Set.Icc A B) :=
        (hH.continuous_deriv le_rfl).comp_continuousOn (hlog.sub continuousOn_const)
      exact hexp.mul hinv |>.mul ((continuousOn_const.mul hHcont).add hH')
    refine (hcont.integrableOn_compact isCompact_Icc).congr_fun (fun t ht => ?_) measurableSet_Icc
    exact (hderiv t ht).deriv.symm
  have hsum := radialPrimeProfile_eq_sum (H := H) (b := b) (y := y) hy0 hb hsupp
  have habel := sum_mul_eq_sub_sub_integral_mul chebyshevCoeff hA0.le hAB hdiff hint
  simp_rw [sum_chebyshevCoeff_eq_theta] at habel
  rw [← hsum, hboundA, hboundB, zero_mul, zero_mul, sub_zero, zero_sub, ← integral_of_le hAB] at habel
  exact habel

private theorem continuousOn_halfProfile_Ioi {H : ℝ → ℝ} {y : ℝ} (hH : Continuous H) :
    ContinuousOn (halfProfile H y) (Ioi 0) := by
  have hlog : ContinuousOn Real.log (Ioi 0) :=
    Real.continuousOn_log.mono fun t ht => ne_of_gt ht
  exact (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hlog)).mul
    (hH.comp_continuousOn (hlog.sub continuousOn_const))

private theorem halfProfile_exp_mul {H : ℝ → ℝ} {y u : ℝ} :
    halfProfile H y (Real.exp (u + y)) * Real.exp (u + y) =
      H u * Real.exp ((u + y) / 2) := by
  have hexp : Real.exp (-(1 / 2) * (u + y)) * Real.exp (u + y) = Real.exp ((u + y) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    halfProfile H y (Real.exp (u + y)) * Real.exp (u + y)
      = Real.exp (-(1 / 2) * (u + y)) * H u * Real.exp (u + y) := by
        simp [halfProfile, Real.log_exp]
    _ = H u * (Real.exp (-(1 / 2) * (u + y)) * Real.exp (u + y)) := by ring
    _ = H u * Real.exp ((u + y) / 2) := by rw [hexp]

private theorem exp_add_div {u y : ℝ} :
    Real.exp ((u + y) / 2) = Real.exp (y / 2) * Real.exp (u / 2) := by
  rw [← Real.exp_add]
  congr 1
  ring

private theorem integral_halfProfile_eq_moment {H : ℝ → ℝ} {b y : ℝ} (_hy : 0 ≤ y) (hb : 0 ≤ b)
    (hH : Continuous H) :
    ∫ t in Real.exp y..Real.exp (y + b), halfProfile H y t =
      Real.exp (y / 2) * ∫ u in (0 : ℝ)..b, H u * Real.exp (u / 2) := by
  have hAB : Real.exp y ≤ Real.exp (y + b) := Real.exp_le_exp.mpr (by linarith)
  have hderiv (u : ℝ) (_hu : u ∈ uIcc 0 b) :
      HasDerivAt (Real.exp ∘ fun v => v + y) (Real.exp (u + y)) u := by
    simpa using ((Real.hasDerivAt_exp (u + y)).comp u
      ((hasDerivAt_id u).add_const y)).congr_deriv (mul_one _)
  have hchange := integral_comp_mul_deriv' (a := (0 : ℝ)) (b := b)
    (f := Real.exp ∘ fun v => v + y) (f' := fun u => Real.exp (u + y))
    (g := halfProfile H y) hderiv
    ((Real.continuous_exp.comp (continuous_id.add continuous_const)).continuousOn)
    ((continuousOn_halfProfile_Ioi hH).mono fun t ht => ?_)
  rotate_left
  · obtain ⟨u, -, rfl⟩ := ht
    exact Real.exp_pos _
  have hchange' :
      ∫ x in (0 : ℝ)..b, (halfProfile H y ∘ Real.exp ∘ fun v => v + y) x * Real.exp (x + y) =
        ∫ t in Real.exp y..Real.exp (y + b), halfProfile H y t := by
    have haux := hchange
    simp only [Function.comp_apply, zero_add] at haux
    rwa [add_comm b y] at haux
  rw [← hchange']
  have hpoint : ∀ u ∈ [[(0 : ℝ), b]],
      (halfProfile H y ∘ Real.exp ∘ fun v => v + y) u * Real.exp (u + y) =
        Real.exp (y / 2) * (H u * Real.exp (u / 2)) := by
    intro u _
    simpa [Function.comp_apply] using (halfProfile_exp_mul (H := H) (y := y) (u := u)).trans
      (by rw [exp_add_div, mul_left_comm])
  rw [integral_congr hpoint, intervalIntegral.integral_const_mul]

private theorem halfProfile_window_zero {H : ℝ → ℝ} {b y : ℝ}
    (hsupp : tsupport H ⊆ Set.Ioo 0 b) :
    halfProfile H y (Real.exp y) = 0 ∧ halfProfile H y (Real.exp (y + b)) = 0 := by
  constructor
  · apply halfProfile_eq_zero_of_argument (t := Real.exp y) hsupp
    simp [Real.log_exp, Set.Ioo]
  · apply halfProfile_eq_zero_of_argument (t := Real.exp (y + b)) hsupp
    simp [Real.log_exp, Set.Ioo]

private theorem continuousOn_deriv_halfProfile {H : ℝ → ℝ} {y A B : ℝ}
    (hA : 0 < A) (_hAB : A ≤ B) (hH : ContDiff ℝ 1 H) :
    ContinuousOn (deriv (halfProfile H y)) (Set.Icc A B) := by
  let φ (t : ℝ) : ℝ := Real.exp (-(1 / 2) * Real.log t) * t⁻¹ *
    (-(1 / 2) * H (Real.log t - y) + deriv H (Real.log t - y))
  have hlog : ContinuousOn Real.log (Set.Icc A B) :=
    Real.continuousOn_log.mono fun t ht => (lt_of_lt_of_le hA ht.1).ne'
  have hexp : ContinuousOn (fun t => Real.exp (-(1 / 2) * Real.log t)) (Set.Icc A B) :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hlog)
  have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc A B) :=
    continuousOn_inv₀.mono fun t ht => (lt_of_lt_of_le hA ht.1).ne'
  have hHcont : ContinuousOn (fun t => H (Real.log t - y)) (Set.Icc A B) :=
    hH.continuous.comp_continuousOn (hlog.sub continuousOn_const)
  have hH' : ContinuousOn (fun t => deriv H (Real.log t - y)) (Set.Icc A B) :=
    (hH.continuous_deriv le_rfl).comp_continuousOn (hlog.sub continuousOn_const)
  have hφ : ContinuousOn φ (Set.Icc A B) :=
    hexp.mul hinv |>.mul ((continuousOn_const.mul hHcont).add hH')
  have hHderiv (x : ℝ) : HasDerivAt H (deriv H x) x :=
    ((hH.differentiable one_ne_zero).differentiableAt).hasDerivAt
  refine hφ.congr fun t ht => ?_
  exact (halfProfile_hasDerivAt (lt_of_lt_of_le hA ht.1) (hHderiv _)).deriv

private theorem integral_deriv_halfProfile_mul_id {H : ℝ → ℝ} {b y : ℝ}
    (_hy : 1 ≤ y) (hb : 0 < b) (hsupp : tsupport H ⊆ Set.Ioo 0 b) (hH : ContDiff ℝ 1 H) :
    ∫ t in Real.exp y..Real.exp (y + b), deriv (halfProfile H y) t * t =
      -∫ t in Real.exp y..Real.exp (y + b), halfProfile H y t := by
  set A := Real.exp y
  set B := Real.exp (y + b)
  have hA0 : 0 < A := Real.exp_pos _
  have hAB : A ≤ B := Real.exp_le_exp.mpr (by linarith)
  have hHderiv (x : ℝ) : HasDerivAt H (deriv H x) x :=
    ((hH.differentiable one_ne_zero).differentiableAt).hasDerivAt
  have hderiv (t : ℝ) (ht : t ∈ [[A, B]]) :
      HasDerivAt (halfProfile H y) (deriv (halfProfile H y) t) t := by
    rw [uIcc_of_le hAB] at ht
    exact (halfProfile_hasDerivAt (lt_of_lt_of_le hA0 ht.1) (hHderiv _)).congr_deriv
      ((halfProfile_hasDerivAt (lt_of_lt_of_le hA0 ht.1) (hHderiv _)).deriv).symm
  obtain ⟨hAzero, hBzero⟩ := halfProfile_window_zero (y := y) (b := b) hsupp
  have hcont : ContinuousOn (deriv (halfProfile H y)) [[A, B]] := by
    rw [uIcc_of_le hAB]
    exact continuousOn_deriv_halfProfile (y := y) hA0 hAB hH
  have hprof : ContinuousOn (halfProfile H y) [[A, B]] := by
    rw [uIcc_of_le hAB]
    exact (continuousOn_halfProfile_Ioi hH.continuous).mono fun t ht => lt_of_lt_of_le hA0 ht.1
  have hparts := integral_deriv_mul_eq_sub (a := A) (b := B)
    (u := halfProfile H y) (u' := deriv (halfProfile H y)) (v := id) (v' := fun _ : ℝ => (1 : ℝ))
    hderiv (fun _ _ => hasDerivAt_id _)
    (ContinuousOn.intervalIntegrable (μ := volume) hcont)
    (ContinuousOn.intervalIntegrable (μ := volume)
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) [[A, B]]))
  have hderMul := (ContinuousOn.intervalIntegrable (μ := volume) hcont).mul_continuousOn
    continuousOn_id
  have hsumInt :
      (∫ x in A..B, (deriv (halfProfile H y) x * x + halfProfile H y x)) =
        (∫ x in A..B, deriv (halfProfile H y) x * x) +
          (∫ x in A..B, halfProfile H y x) :=
    integral_add hderMul (ContinuousOn.intervalIntegrable (μ := volume) hprof)
  have hzero :
      (∫ x in A..B, (deriv (halfProfile H y) x * id x + halfProfile H y x * 1)) = 0 := by
    simpa [A, B, hAzero, hBzero, id] using hparts
  have hsame :
      (∫ x in A..B, (deriv (halfProfile H y) x * id x + halfProfile H y x * 1)) =
        (∫ x in A..B, (deriv (halfProfile H y) x * x + halfProfile H y x)) := by
    refine integral_congr fun x _ => ?_
    simp [id]
  rw [hsame, hsumInt] at hzero
  linarith

/-- The signed prime sum is the scaled moment of `H`, corrected by Chebyshev's error `θ(t) - t`. -/
theorem radialPrimeProfile_eq_moment_sub_chebyshev {H : ℝ → ℝ} {b y : ℝ}
    (hy : 1 ≤ y) (hb : 0 < b) (hsupp : tsupport H ⊆ Set.Ioo 0 b) (hH : ContDiff ℝ 1 H) :
    radialPrimeProfile H b y =
      Real.exp (y / 2) * (∫ u in (0 : ℝ)..b, H u * Real.exp (u / 2)) -
        (∫ t in Real.exp y..Real.exp (y + b), deriv (halfProfile H y) t * (θ t - t)) := by
  set A := Real.exp y
  set B := Real.exp (y + b)
  have hA0 : 0 < A := Real.exp_pos _
  have hAB : A ≤ B := Real.exp_le_exp.mpr (by linarith)
  have htheta := radialPrimeProfile_eq_neg_integral_theta hy hb hsupp hH
  have hmoment := integral_halfProfile_eq_moment (le_trans (by norm_num) hy) hb.le hH.continuous
  have hparts := integral_deriv_halfProfile_mul_id hy hb hsupp hH
  have hcont : ContinuousOn (deriv (halfProfile H y)) [[A, B]] := by
    rw [uIcc_of_le hAB]
    exact continuousOn_deriv_halfProfile (y := y) hA0 hAB hH
  have hderInt : IntervalIntegrable (deriv (halfProfile H y)) volume A B := hcont.intervalIntegrable
  have hθInt : IntervalIntegrable (fun t => θ t) volume A B := theta_mono.intervalIntegrable
  have herrInt : IntervalIntegrable (fun t => θ t - t) volume A B :=
    hθInt.sub (continuous_id.intervalIntegrable A B)
  have hidInt : IntervalIntegrable (fun t => deriv (halfProfile H y) t * t) volume A B :=
    hderInt.mul_continuousOn continuousOn_id
  have hsplit :
      (∫ t in A..B, deriv (halfProfile H y) t * θ t) =
        (∫ t in A..B, deriv (halfProfile H y) t * (θ t - t)) +
          (∫ t in A..B, deriv (halfProfile H y) t * t) := by
    rw [← integral_add (herrInt.continuousOn_mul hcont) hidInt]
    refine integral_congr fun t _ => ?_
    ring
  set Iθ : ℝ := ∫ t in A..B, deriv (halfProfile H y) t * θ t
  set Ierr : ℝ := ∫ t in A..B, deriv (halfProfile H y) t * (θ t - t)
  set Iid : ℝ := ∫ t in A..B, deriv (halfProfile H y) t * t
  set Iprof : ℝ := ∫ t in A..B, halfProfile H y t
  set moment : ℝ := ∫ u in (0 : ℝ)..b, H u * Real.exp (u / 2)
  have hIθ : Iθ = Ierr + Iid := by simpa [Iθ, Ierr, Iid] using hsplit
  have hIid : Iid = -Iprof := by simpa [Iid, Iprof] using hparts
  have hIprof : Iprof = Real.exp (y / 2) * moment := by simpa [Iprof, moment] using hmoment
  have hP : radialPrimeProfile H b y = -Iθ := by simpa [Iθ] using htheta
  calc
    radialPrimeProfile H b y = -Iθ := hP
    _ = -(Ierr + Iid) := by rw [hIθ]
    _ = -Ierr - Iid := by ring
    _ = -Ierr - (-Iprof) := by rw [hIid]
    _ = -Ierr + Iprof := by ring
    _ = -Ierr + Real.exp (y / 2) * moment := by rw [hIprof]
    _ = Real.exp (y / 2) * moment - Ierr := by ring

/-- The weight `t^{-1/2} |F(log t - y)|` pulls back to a moment of `|F|`. -/
private theorem integral_abs_logWeight {F : ℝ → ℝ} {b y : ℝ} (_hy : 0 ≤ y) (_hb : 0 ≤ b)
    (hF : Continuous F) :
    (∫ t in Real.exp y..Real.exp (y + b),
        Real.exp (-(1 / 2) * Real.log t) * |F (Real.log t - y)|) =
      Real.exp (y / 2) * ∫ u in (0 : ℝ)..b, Real.exp (u / 2) * |F u| := by
  let g (t : ℝ) : ℝ := Real.exp (-(1 / 2) * Real.log t) * |F (Real.log t - y)|
  have hderiv (u : ℝ) (_hu : u ∈ uIcc 0 b) :
      HasDerivAt (Real.exp ∘ fun v => v + y) (Real.exp (u + y)) u := by
    simpa using ((Real.hasDerivAt_exp (u + y)).comp u
      ((hasDerivAt_id u).add_const y)).congr_deriv (mul_one _)
  have hg : ContinuousOn g (Ioi 0) := by
    have hlog : ContinuousOn Real.log (Ioi 0) :=
      Real.continuousOn_log.mono fun t ht => ne_of_gt ht
    exact (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hlog)).mul
      ((hF.comp_continuousOn (hlog.sub continuousOn_const)).abs)
  have hchange := integral_comp_mul_deriv' (a := (0 : ℝ)) (b := b)
    (f := Real.exp ∘ fun v => v + y) (f' := fun u => Real.exp (u + y)) (g := g) hderiv
    ((Real.continuous_exp.comp (continuous_id.add continuous_const)).continuousOn)
    (hg.mono fun t ht => by obtain ⟨_, -, rfl⟩ := ht; exact Real.exp_pos _)
  have hchange' :
      ∫ x in (0 : ℝ)..b, (g ∘ Real.exp ∘ fun v => v + y) x * Real.exp (x + y) =
        ∫ t in Real.exp y..Real.exp (y + b), g t := by
    have haux := hchange
    simp only [Function.comp_apply, zero_add] at haux
    rwa [add_comm b y] at haux
  rw [← hchange']
  have hpoint : ∀ u ∈ [[(0 : ℝ), b]],
      (g ∘ Real.exp ∘ fun v => v + y) u * Real.exp (u + y) =
        Real.exp (y / 2) * (Real.exp (u / 2) * |F u|) := by
    intro u _
    have hexp : Real.exp (-(1 / 2) * (u + y)) * Real.exp (u + y) = Real.exp ((u + y) / 2) := by
      rw [← Real.exp_add]; ring_nf
    simp only [Function.comp_apply, g, Real.log_exp, add_sub_cancel_right]
    rw [mul_assoc, mul_comm |F u| (Real.exp (u + y)), ← mul_assoc, hexp, exp_add_div, mul_assoc]
  rw [integral_congr hpoint, intervalIntegral.integral_const_mul]

/-- After scaling by `e^{-y/2}`, the signed prime sum tends to the moment of `H`. -/
theorem tendsto_exp_neg_mul_radialPrimeProfile {H : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hsupp : tsupport H ⊆ Set.Ioo 0 b) (hH : ContDiff ℝ 1 H) :
    Tendsto (fun y : ℝ => Real.exp (-y / 2) * radialPrimeProfile H b y)
      atTop (𝓝 (∫ u in (0 : ℝ)..b, H u * Real.exp (u / 2))) := by
  classical
  let coeff (u : ℝ) : ℝ := -(1 / 2) * H u + deriv H u
  let moment : ℝ := ∫ u in (0 : ℝ)..b, H u * Real.exp (u / 2)
  let C : ℝ := ∫ u in (0 : ℝ)..b, Real.exp (u / 2) * |coeff u|
  have hCnonneg : 0 ≤ C := by
    refine intervalIntegral.integral_nonneg hb.le fun u hu => ?_
    exact mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  set δ : ℝ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hθ : ∀ᶠ x : ℝ in atTop, |θ x - x| ≤ δ * |x| := by
    have hlittle := isEquivalent_theta_id.isLittleO.def hδ
    simpa [Real.norm_eq_abs, Pi.sub_apply, id] using hlittle
  rw [eventually_atTop] at hθ
  obtain ⟨T, hT⟩ := hθ
  refine ⟨max 1 (Real.log (max T 2)), fun y hy => ?_⟩
  have hy1 : 1 ≤ y := le_trans (le_max_left _ _) hy
  have hAy : max T 2 ≤ Real.exp y :=
    (Real.log_le_iff_le_exp (by positivity)).mp (le_trans (le_max_right _ _) hy)
  have hAB : Real.exp y ≤ Real.exp (y + b) := Real.exp_le_exp.mpr (by linarith)
  have hid := radialPrimeProfile_eq_moment_sub_chebyshev hy1 hb hsupp hH
  have hdiff :
      Real.exp (-y / 2) * radialPrimeProfile H b y - moment =
        -Real.exp (-y / 2) *
          (∫ t in Real.exp y..Real.exp (y + b), deriv (halfProfile H y) t * (θ t - t)) := by
    set Imoment : ℝ := ∫ u in (0 : ℝ)..b, H u * Real.exp (u / 2)
    set Ierr : ℝ := ∫ t in Real.exp y..Real.exp (y + b),
      deriv (halfProfile H y) t * (θ t - t)
    have hImoment : Imoment = moment := by simp [Imoment, moment]
    have hid' : radialPrimeProfile H b y = Real.exp (y / 2) * Imoment - Ierr := by
      simpa [Imoment, Ierr] using hid
    have hcancel : Real.exp (-y / 2) * (Real.exp (y / 2) * Imoment) = moment := by
      rw [← mul_assoc, ← Real.exp_add, hImoment]
      have : -y / 2 + y / 2 = 0 := by ring
      rw [this, Real.exp_zero, one_mul]
    calc
      Real.exp (-y / 2) * radialPrimeProfile H b y - moment
        = Real.exp (-y / 2) * (Real.exp (y / 2) * Imoment - Ierr) - moment := by rw [hid']
      _ = Real.exp (-y / 2) * (Real.exp (y / 2) * Imoment) - Real.exp (-y / 2) * Ierr - moment := by
        ring
      _ = moment - Real.exp (-y / 2) * Ierr - moment := by rw [hcancel]
      _ = -Real.exp (-y / 2) * Ierr := by ring
  have hbound : |Real.exp (-y / 2) * radialPrimeProfile H b y - moment| ≤ δ * C := by
    rw [hdiff, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
    set A := Real.exp y
    set B := Real.exp (y + b)
    have hHderiv (x : ℝ) : HasDerivAt H (deriv H x) x :=
      ((hH.differentiable one_ne_zero).differentiableAt).hasDerivAt
    have hderivAbs (t : ℝ) (ht : t ∈ Set.Icc A B) :
        |deriv (halfProfile H y) t| * t =
          Real.exp (-(1 / 2) * Real.log t) * |coeff (Real.log t - y)| := by
      have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht.1
      rw [(halfProfile_hasDerivAt ht0 (hHderiv _)).deriv, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos _), abs_of_pos (inv_pos.mpr ht0)]
      have hinv : t⁻¹ * t = 1 := by rw [mul_comm, mul_inv_cancel₀ ht0.ne']
      calc
        Real.exp (-(1 / 2) * Real.log t) * t⁻¹ *
            |-(1 / 2) * H (Real.log t - y) + deriv H (Real.log t - y)| * t
          = Real.exp (-(1 / 2) * Real.log t) *
              |-(1 / 2) * H (Real.log t - y) + deriv H (Real.log t - y)| * (t⁻¹ * t) := by ring
        _ = Real.exp (-(1 / 2) * Real.log t) * |coeff (Real.log t - y)| := by
          rw [hinv, mul_one]
    have herr : |∫ t in A..B, deriv (halfProfile H y) t * (θ t - t)| ≤
        δ * ∫ t in A..B, Real.exp (-(1 / 2) * Real.log t) * |coeff (Real.log t - y)| := by
      have habs := abs_integral_le_integral_abs (μ := volume) hAB
        (f := fun t => deriv (halfProfile H y) t * (θ t - t))
      refine habs.trans ?_
      have herrFun : IntervalIntegrable
          (fun t => deriv (halfProfile H y) t * (θ t - t)) volume A B := by
        have hcont : ContinuousOn (deriv (halfProfile H y)) [[A, B]] := by
          rw [uIcc_of_le hAB]
          exact continuousOn_deriv_halfProfile (y := y) (Real.exp_pos _) hAB hH
        have hsub : IntervalIntegrable (fun t => θ t - t) volume A B :=
          theta_mono.intervalIntegrable.sub (continuous_id.intervalIntegrable A B)
        exact hsub.continuousOn_mul hcont
      have hweightFun : IntervalIntegrable (fun t =>
          δ * (Real.exp (-(1 / 2) * Real.log t) * |coeff (Real.log t - y)|)) volume A B := by
        have hlog : ContinuousOn Real.log (Set.Icc A B) :=
          Real.continuousOn_log.mono fun t ht => (lt_of_lt_of_le (Real.exp_pos _) ht.1).ne'
        have hF : Continuous coeff :=
          (hH.continuous.const_mul (-(1 / 2))).add (hH.continuous_deriv le_rfl)
        have hcont : ContinuousOn (fun t =>
            δ * (Real.exp (-(1 / 2) * Real.log t) * |coeff (Real.log t - y)|)) [[A, B]] := by
          rw [uIcc_of_le hAB]
          exact continuousOn_const.mul
            ((Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hlog)).mul
              ((hF.comp_continuousOn (hlog.sub continuousOn_const)).abs))
        exact ContinuousOn.intervalIntegrable (μ := volume) hcont
      have hmono : (∫ t in A..B, |deriv (halfProfile H y) t * (θ t - t)|) ≤
          ∫ t in A..B, δ * (Real.exp (-(1 / 2) * Real.log t) * |coeff (Real.log t - y)|) := by
        refine integral_mono_on (μ := volume) hAB herrFun.abs hweightFun fun t ht => ?_
        have hcheb : |θ t - t| ≤ δ * t := by
          have htT : T ≤ t := le_trans (le_max_left T 2) (le_trans hAy ht.1)
          simpa [abs_of_pos (lt_of_lt_of_le (Real.exp_pos _) ht.1)] using hT t htT
        calc
          |deriv (halfProfile H y) t * (θ t - t)|
            = |deriv (halfProfile H y) t| * |θ t - t| := abs_mul _ _
          _ ≤ |deriv (halfProfile H y) t| * (δ * t) :=
            mul_le_mul_of_nonneg_left hcheb (abs_nonneg _)
          _ = δ * (|deriv (halfProfile H y) t| * t) := by ring
          _ = δ * (Real.exp (-(1 / 2) * Real.log t) * |coeff (Real.log t - y)|) := by
            rw [hderivAbs t ht]
      have hpull : (∫ t in A..B,
          δ * (Real.exp (-(1 / 2) * Real.log t) * |coeff (Real.log t - y)|)) =
          δ * ∫ t in A..B, Real.exp (-(1 / 2) * Real.log t) * |coeff (Real.log t - y)| := by
        simp [intervalIntegral.integral_const_mul]
      exact hmono.trans (by rw [hpull])
    have hweight := integral_abs_logWeight (F := coeff) (b := b) (y := y)
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) hy1) hb.le
      ((hH.continuous.const_mul (-(1 / 2))).add (hH.continuous_deriv le_rfl))
    -- `coeff` is continuous, so the weight integral is `e^{y/2} * C`.
    have hCeq : (∫ t in A..B, Real.exp (-(1 / 2) * Real.log t) * |coeff (Real.log t - y)|) =
        Real.exp (y / 2) * C := by
      simpa [A, B, C, mul_comm] using hweight
    calc
      Real.exp (-y / 2) * |∫ t in A..B, deriv (halfProfile H y) t * (θ t - t)|
        ≤ Real.exp (-y / 2) * (δ * (Real.exp (y / 2) * C)) := by gcongr; exact herr.trans (by rw [hCeq])
      _ = δ * C := by
        calc
          Real.exp (-y / 2) * (δ * (Real.exp (y / 2) * C))
            = δ * ((Real.exp (-y / 2) * Real.exp (y / 2)) * C) := by ring
          _ = δ * (Real.exp (-y / 2 + y / 2) * C) := by rw [← Real.exp_add]
          _ = δ * C := by
            have : -y / 2 + y / 2 = 0 := by ring
            rw [this, Real.exp_zero, one_mul]
  have hδC : δ * C < ε := by
    have hδdef : δ = ε / (C + 1) := rfl
    rw [hδdef]
    have hlt : C / (C + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    calc
      ε / (C + 1) * C = ε * (C / (C + 1)) := by field_simp
      _ < ε * 1 := mul_lt_mul_of_pos_left hlt hε
      _ = ε := by ring
  exact lt_of_le_of_lt hbound hδC

/-- With a vanishing half-moment, the degree-one sum is exactly the integral against
`θ(t) - t`. For a radial test on the idèles of `ℚ`, this moment is the main term at
the pole `|·|^{1/2}` of (12.5.1.2)–(12.5.1.3), pp. 519–520. -/
theorem radialPrimeProfile_eq_neg_chebyshev_error_of_moment_zero {H : ℝ → ℝ} {b y : ℝ}
    (hy : 1 ≤ y) (hb : 0 < b) (hsupp : tsupport H ⊆ Set.Ioo 0 b) (hH : ContDiff ℝ 1 H)
    (hmoment : ∫ u in (0 : ℝ)..b, H u * Real.exp (u / 2) = 0) :
    radialPrimeProfile H b y =
      -∫ t in Real.exp y..Real.exp (y + b),
        deriv (halfProfile H y) t * (θ t - t) := by
  have h := radialPrimeProfile_eq_moment_sub_chebyshev hy hb hsupp hH
  simpa [hmoment] using h

/-- With a vanishing half-moment, scaling by `e^{-y/2}` sends the signed prime sum to zero.
This is `o(e^{y/2})`. Mathlib's prime number theorem gives no rate. -/
theorem tendsto_exp_neg_mul_radialPrimeProfile_of_moment_zero {H : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hsupp : tsupport H ⊆ Set.Ioo 0 b) (hH : ContDiff ℝ 1 H)
    (hmoment : ∫ u in (0 : ℝ)..b, H u * Real.exp (u / 2) = 0) :
    Tendsto (fun y : ℝ => Real.exp (-y / 2) * radialPrimeProfile H b y) atTop (𝓝 0) := by
  simpa [hmoment] using tendsto_exp_neg_mul_radialPrimeProfile hb hsupp hH

end RiemannMasullo
