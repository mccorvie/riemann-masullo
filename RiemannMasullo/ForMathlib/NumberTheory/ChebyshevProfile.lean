module

public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Algebra.Support

/-!
# A signed prime profile and Chebyshev's function

For a test supported in a bounded positive log interval, the degree-one sum
`∑_p (log p) p^{-1/2} H(log p - y)` equals minus the integral of that profile's derivative
against Chebyshev's `θ`. This is the Abel step in the endpoint description of the rational
local terms of Theorem 12.5.1.1, pp. 519–520. Splitting `θ(t) - t` from the main term
`∫ H(u) e^{u/2} du` is the next step; it is not claimed here.
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

end RiemannMasullo
