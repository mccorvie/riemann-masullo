module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Taylor coefficient energy on the unit disk

Taylor summation on each inner circle identifies the nonnegative angular Fourier
coefficients, and the negative coefficients vanish. Parseval for angular Haar
probability bounds all finite coefficient energies. Passing each finite sum to radius
one gives the full square sum; applying the same argument to the derivative gives
the weight j² on the j-th Taylor coefficient.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory Metric Set
open scoped NNReal Topology
namespace RiemannMasullo.DiskCoefficientEnergy

/-- The actual complex Taylor coefficient at the origin. -/
def coeff (g : ℂ → ℂ) (j : ℕ) : ℂ := (j.factorial:ℂ)⁻¹ * iteratedDeriv j g 0

theorem hasSum_coeff {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    {z : ℂ} (hz : ‖z‖ < 1) : HasSum (fun j ↦ coeff g j * z^j) (g z) := by
  have h := Complex.hasSum_taylorSeries_on_ball hg (show z ∈ ball (0:ℂ) 1 by simpa using hz)
  apply h.congr_fun
  intro j
  simp [coeff, smul_eq_mul]
  ring

private theorem fourier_nat (x : AddCircle (1:ℝ)) (j : ℕ) :
    fourier (j:ℤ) x = (fourier 1 x)^j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.cast_succ, fourier_add, ih, pow_succ]

local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

/-- Evaluation on an inner circle, parametrized by additive-circle Haar probability. -/
def radialValue (g : ℂ → ℂ) (r : ℝ) (x : AddCircle (1:ℝ)) : ℂ :=
  g ((r:ℂ) * fourier 1 x)

/-- Taylor coefficients scaled by r to the frequency, with zero negative frequencies. -/
def radialCoefficients (g : ℂ → ℂ) (r : ℝ) : ℤ → ℂ :=
  Int.rec (fun j ↦ coeff g j * (r:ℂ)^j) (fun _ ↦ 0)

private theorem argument_norm {r : ℝ} (hr : 0 < r) (x : AddCircle (1:ℝ)) :
    ‖(r:ℂ)*fourier 1 x‖ = r := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    show ‖fourier 1 x‖=1 from Circle.norm_coe _, mul_one]

/-- The nonnegative angular Fourier coefficients are the actual Taylor coefficients times r^j. -/
theorem fourierCoeff_radial {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1)) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    fourierCoeff (radialValue g r) = radialCoefficients g r := by
  apply fourierCoeff_eq_of_hasSum
  intro x
  have hnat : HasSum (fun j : ℕ ↦ fourier (j:ℤ) x • radialCoefficients g r j) (radialValue g r x) := by
    apply (hasSum_coeff hg ((argument_norm hr x).trans_lt hr1)).congr_fun
    intro j
    change fourier (j:ℤ) x * (coeff g j * (r:ℂ)^j) = coeff g j * ((r:ℂ)*fourier 1 x)^j
    rw [fourier_nat, mul_pow]
    ring
  have hneg : HasSum (fun j : ℕ ↦ fourier (-(j + 1):ℤ) x • radialCoefficients g r (-(j + 1):ℤ)) 0 := by
    convert hasSum_zero (β:=ℕ) (α:=ℂ) using 1
    funext j
    change fourier (Int.negSucc j) x • (0:ℂ) = 0
    simp
  simpa using (hnat.of_nat_of_neg_add_one (f:=fun i : ℤ ↦ fourier i x • radialCoefficients g r i) hneg)

/-- Parseval on each inner circle uses Haar probability on AddCircle 1. -/
theorem radial_parseval {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1)) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    HasSum (fun j : ℕ ↦ ‖coeff g j‖^2 * r^(2*j))
      (∫ x : AddCircle (1:ℝ), ‖radialValue g r x‖^2 ∂AddCircle.haarAddCircle) := by
  have hwb (x : AddCircle (1:ℝ)) : (r:ℂ)*fourier 1 x ∈ ball (0:ℂ) 1 := by
    simpa using (argument_norm hr x).trans_lt hr1
  let G : C(AddCircle (1:ℝ),ℂ) := ⟨radialValue g r,
    hg.continuousOn.comp_continuous (continuous_const.mul (fourier (T:=1) 1).continuous) hwb⟩
  let μ : Measure (AddCircle (1:ℝ)) := AddCircle.haarAddCircle
  let G₂ := ContinuousMap.toLp (E:=ℂ) 2 μ ℂ G
  have hcf (i : ℤ) : fourierCoeff (G₂ : Lp ℂ 2 μ) i = radialCoefficients g r i :=
    (fourierCoeff_toLp G i).trans (congrFun (fourierCoeff_radial hg hr hr1) i)
  have hpos (j : ℕ) : fourierCoeff G₂ (j:ℤ) = coeff g j * (r:ℂ)^j := hcf j
  have hneg (j : ℕ) : fourierCoeff G₂ (-(j + 1):ℤ) = 0 := hcf _
  have hI : (∫ x, ‖G₂ x‖^2 ∂μ) = ∫ x, ‖radialValue g r x‖^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p:=2) μ (𝕜:=ℂ) G] with x hx
    rw [show G₂ x = radialValue g r x from hx]
  rw [←hI]
  apply (hasSum_sq_fourierCoeff G₂).nat_add_neg_add_one.congr_fun
  intro j
  rw [hpos, hneg, norm_zero, zero_pow (by norm_num : (2:ℕ)≠0), add_zero, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, mul_pow,←pow_mul, Nat.mul_comm j 2]

private theorem radial_partial {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ z : ℂ, ‖z‖ < 1 → ‖g z‖ ≤ D)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (S : Finset ℕ) :
    ∑ j ∈ S, ‖coeff g j‖^2 * r^(2*j) ≤ D^2 := by
  have hs := radial_parseval hg hr hr1
  let μ : Measure (AddCircle (1:ℝ)) := AddCircle.haarAddCircle
  have hgb : ∀ᵐ x ∂μ, ‖radialValue g r x‖^2 ≤ D^2 :=
    Eventually.of_forall fun x ↦ (sq_le_sq₀ (norm_nonneg _) hD).mpr (hb _ ((argument_norm hr x).trans_lt hr1))
  have hI : (∫ x, ‖radialValue g r x‖^2 ∂μ) ≤ D^2 := by
    have h := integral_mono_of_nonneg (Eventually.of_forall fun x ↦ sq_nonneg ‖radialValue g r x‖)
      (integrable_const (μ:=μ) (D^2)) hgb
    simpa [μ] using h
  exact (hs.summable.sum_le_tsum S (fun j _ ↦ by positivity)).trans (hs.tsum_eq.trans_le hI)

/-- The squared Taylor coefficient sum of a bounded disk function is at most its squared bound. -/
theorem bounded_coefficients {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ z : ℂ, ‖z‖ < 1 → ‖g z‖ ≤ D) :
    Summable (fun j : ℕ ↦ ‖coeff g j‖^2) ∧ ∑' j : ℕ, ‖coeff g j‖^2 ≤ D^2 := by
  have hS (S : Finset ℕ) : ∑ j ∈ S, ‖coeff g j‖^2 ≤ D^2 := by
    have hc : Continuous (fun r : ℝ ↦ ∑ j ∈ S, ‖coeff g j‖^2 * r^(2*j)) := by fun_prop
    have ht := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s:=Iio (1:ℝ)))
    have hpos : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
      (eventually_gt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
    have hbd : ∀ᶠ r : ℝ in 𝓝[<] 1, ∑ j ∈ S, ‖coeff g j‖^2 * r^(2*j) ≤ D^2 := by
      filter_upwards [hpos, self_mem_nhdsWithin] with r hri hr1 using radial_partial hg hD hb hri hr1 S
    simpa using le_of_tendsto ht hbd
  have hs := summable_of_sum_le (fun j : ℕ ↦ sq_nonneg ‖coeff g j‖) hS
  exact ⟨hs, hs.tsum_le_of_sum_le hS⟩

theorem derivative_coeff (f : ℂ → ℂ) (j : ℕ) :
    coeff (deriv f) j = ((j + 1:ℕ):ℂ) * coeff f (j + 1) := by
  have hn : ((j + 1:ℕ):ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  rw [coeff, coeff, Nat.factorial_succ, Nat.cast_mul, iteratedDeriv_succ']
  field_simp

/-- Parseval on inner circles, followed by the finite-partial-sum limit at radius one, bounds the
derivative-weighted square sum of the actual Taylor coefficients. -/
theorem derivative_energy {f : ℂ → ℂ} (ha : AnalyticOnNhd ℂ f (ball 0 1)) {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ z : ℂ, ‖z‖ < 1 → ‖deriv f z‖ ≤ D) :
    Summable (fun j : ℕ ↦ (j:ℝ)^2 * ‖coeff f j‖^2) ∧
      ∑' j : ℕ, (j:ℝ)^2 * ‖coeff f j‖^2 ≤ D^2 := by
  have hg : DifferentiableOn ℂ (deriv f) (ball 0 1) :=
    fun z hz ↦ (ha z hz).deriv.differentiableAt.differentiableWithinAt
  obtain ⟨hs, hb'⟩ := bounded_coefficients hg hD hb
  have hid (j : ℕ) : ((j + 1:ℕ):ℝ)^2 * ‖coeff f (j + 1)‖^2 = ‖coeff (deriv f) j‖^2 := by
    rw [derivative_coeff, norm_mul, mul_pow, Complex.norm_natCast]
  have hfin (m : ℕ) : ∑ j∈Finset.range m, (j:ℝ)^2 * ‖coeff f j‖^2 ≤ D^2 := by
    cases m with
    | zero => simp [sq_nonneg]
    | succ m =>
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_pow (by decide : (2:ℕ)≠0), zero_mul, add_zero, hid]
      exact (hs.sum_le_tsum (Finset.range m) (fun _ _ ↦ sq_nonneg _)).trans hb'
  have hs' := summable_of_sum_range_le (fun j : ℕ ↦ show 0≤(j:ℝ)^2*‖coeff f j‖^2 by positivity) hfin
  exact ⟨hs', hs'.tsum_le_of_sum_range_le hfin⟩

end RiemannMasullo.DiskCoefficientEnergy
