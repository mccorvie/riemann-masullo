module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public noncomputable section

namespace RiemannMasullo

open scoped ContDiff FourierTransform SchwartzMap

/-- The periodization of a Schwartz function over the integer lattice is smooth. -/
theorem schwartz_contDiff_periodization (f : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (fun x : ℝ ↦ ∑' n : ℤ, f (x + n)) := by
  let a (u : ℝ) : ℂ := 2 * Real.pi * Complex.I * u
  let b (k : ℕ) (n : ℤ) := a n ^ k * (𝓕 f) n
  let t (n : ℤ) (x : ℝ) := (𝓕 f) n * fourier n (x : AddCircle (1 : ℝ))
  have hd (n : ℤ) (k : ℕ) :
      iteratedDeriv k (t n) = fun x : ℝ ↦ b k n * fourier n (x : AddCircle (1 : ℝ)) := by
    induction k with
    | zero => simp [b, t]
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      convert ((hasDerivAt_fourier 1 n x).const_mul (b k n)).deriv using 1
      simp [b, a, pow_succ]
      ring
  have hb (k : ℕ) : Summable fun n : ℤ ↦ ‖b k n‖ := by
    have hg : (fun u : ℝ ↦ a u ^ k).HasTemperateGrowth := by
      dsimp [a]
      fun_prop
    let F := SchwartzMap.smulLeftCLM ℂ (fun u : ℝ ↦ a u ^ k) (𝓕 f)
    have hs : Summable (fun n : ℤ ↦ ‖F n‖) :=
      summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
        ((F.isBigO_cocompact_rpow (-2)).norm_left.comp_tendsto Int.tendsto_coe_cofinite)
    simpa only [F, b, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul] using hs
  simp_rw [f.tsum_eq_tsum_fourier]
  apply contDiff_tsum (f := t) (v := fun k n ↦ ‖b k n‖)
  · intro n
    have hcoe : ContDiff ℝ ∞ ((↑) : ℝ → ℂ) := Complex.ofRealCLM.contDiff
    simp only [t, fourier_coe_apply]
    fun_prop
  · exact fun k _ ↦ hb k
  · intro k n x _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hd, norm_mul]
    simp only [fourier_apply, Circle.norm_coe, mul_one, le_rfl]

open ContinuousMap Filter MeasureTheory Set in
open scoped Asymptotics in
/-- If a continuously differentiable function and its derivative both decay at least as
fast as the inverse square, its Fourier samples on the integer lattice are absolutely summable. -/
theorem summable_norm_fourier_int_of_isBigO {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g)
    (h : g =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-2 : ℝ)))
    (h' : deriv g =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-2 : ℝ))) :
    Summable (fun m : ℤ ↦ ‖𝓕 g (m : ℝ)‖) := by
  have hs (v : C(ℝ, ℂ)) (hv : (v : ℝ → ℂ) =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-2 : ℝ)))
      (K : TopologicalSpace.Compacts ℝ) :
      Summable (fun m : ℤ ↦ ‖(v.comp (ContinuousMap.addRight m)).restrict K‖) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((isBigO_norm_restrict_cocompact v (by norm_num) hv K).comp_tendsto Int.tendsto_coe_cofinite)
  -- Periodize the derivative and use Parseval to get square-summable samples.
  let v : C(ℝ, ℂ) := ⟨deriv g, hg.continuous_deriv (by simp)⟩
  let V : C(UnitAddCircle, ℂ) :=
    ⟨(v.periodic_tsum_comp_add_zsmul 1).lift,
      continuous_coinduced_dom.mpr (map_continuous _)⟩
  have hv (m : ℤ) : fourierCoeff V m = 𝓕 (deriv g) (m : ℝ) :=
    Real.fourierCoeff_tsum_comp_add (hs v h') m
  have hsq : Summable (fun m : ℤ ↦ ‖𝓕 (deriv g) (m : ℝ)‖ ^ 2) := by
    simpa only [fourierCoeff_toLp, hv] using
      (hasSum_sq_fourierCoeff (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ V)).summable
  let u : C(ℝ, ℂ) := ⟨g, hg.continuous⟩
  let K : TopologicalSpace.Compacts ℝ := ⟨Icc 0 1, isCompact_Icc⟩
  have hi : Integrable g := Real.integrable_of_summable_norm_Icc (f := u) (hs u h K)
  have hi' : Integrable (deriv g) := Real.integrable_of_summable_norm_Icc (f := v) (hs v h' K)
  -- On nonzero modes the derivative contributes a factor of `2 * π * |m|`.
  have hpow : Summable (fun m : ℤ ↦ (|(m : ℝ)|⁻¹) ^ (2 : ℝ)) := by
    simpa only [Real.inv_rpow (abs_nonneg _), Real.rpow_neg (abs_nonneg _)] using
      Real.summable_abs_int_rpow one_lt_two
  have hprod := Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two
    (fun m : ℤ ↦ norm_nonneg (𝓕 (deriv g) (m : ℝ)))
    (fun m : ℤ ↦ inv_nonneg.mpr (abs_nonneg (m : ℝ)))
    (by simpa only [Real.rpow_two] using hsq) hpow
  apply (hprod.mul_left ((2 * Real.pi)⁻¹)).of_norm_bounded_eventually
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with m hm
  have hm' : |(m : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hm)
  rw [Real.fourier_deriv hi (hg.differentiable (by simp)) hi', norm_smul]
  simp only [Complex.norm_mul, Complex.norm_ofNat 2, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one, abs_of_nonneg (norm_nonneg _)]
  field_simp [Real.pi_ne_zero, hm']
  exact le_rfl

section SymmetricPoissonSummation

open Filter MeasureTheory Set
open scoped Topology

local notation "twoPiI" => (2 * (Real.pi : ℂ) * Complex.I)

/-- Integration over a fundamental interval unfolds the integer periodization of an integrable
function against any integer frequency. -/
theorem integral_periodization_mul_exp_int {g : ℝ → ℂ} (hg : Integrable g) (k : ℤ) :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ),
        Complex.exp (twoPiI * (k : ℂ) * (x : ℂ)) * (∑' n : ℤ, g (x + n))) =
      ∫ x : ℝ, Complex.exp (twoPiI * (k : ℂ) * (x : ℂ)) * g x := by
  let e (x : ℝ) := Complex.exp (twoPiI * (k : ℂ) * (x : ℂ))
  have he : Continuous e := by dsimp [e]; fun_prop
  have hen (x : ℝ) : ‖e x‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have headd (x : ℝ) (n : ℤ) : e (x + n) = e x := by
    have heint : Complex.exp (twoPiI * (k : ℂ) * (n : ℂ)) = 1 := by
      simpa [Int.cast_mul, mul_assoc, mul_left_comm, mul_comm] using
        Complex.exp_int_mul_two_pi_mul_I (k * n)
    simp [e, Complex.ofReal_add, mul_add, Complex.exp_add, heint]
  let G (x : ℝ) := e x * g x
  have hG : Integrable G := hg.bdd_mul he.aestronglyMeasurable (Eventually.of_forall (fun x ↦ (hen x).le))
  let a : ℝ := -(1 / 2)
  let b : ℝ := 1 / 2
  have hab : a ≤ b := by norm_num [a, b]
  have hshift {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {F : ℝ → E} (hF : Integrable F) :
      HasSum (fun n : ℤ ↦ ∫ x in a..b, F (x + n)) (∫ x, F x) := by
    convert hF.hasSum_intervalIntegral a using 1
    ext n
    rw [intervalIntegral.integral_comp_add_right]
    congr 1
    dsimp [a, b]
    ring
  have hGi (n : ℤ) : IntegrableOn (fun x : ℝ ↦ G (x + n)) (Ioc a b) :=
    (hG.comp_add_right (n : ℝ)).integrableOn
  have hnorm : Summable (fun n : ℤ ↦ ∫ x in Ioc a b, ‖G (x + n)‖) := by
    simpa only [intervalIntegral.integral_of_le hab] using (hshift hG.norm).summable
  change (∫ x in a..b, e x * (∑' n : ℤ, g (x + n))) = ∫ x, G x
  have hterm (x : ℝ) (n : ℤ) : e x * g (x + n) = G (x + n) := by
    change e x * g (x + n) = e (x + n) * g (x + n)
    rw [headd]
  simp_rw [intervalIntegral.integral_of_le hab, ← tsum_mul_left, hterm]
  rw [← integral_tsum_of_summable_integral_norm hGi hnorm]
  simpa only [intervalIntegral.integral_of_le hab] using (hshift hG).tsum_eq

/-- Multiplying the Dirichlet kernel by one exponential difference telescopes. -/
private theorem sum_exp_int_mul_sub_one (N : ℕ) (x : ℝ) :
    (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Complex.exp (twoPiI * m * (x : ℂ))) *
      (Complex.exp (twoPiI * (x : ℂ)) - 1) =
    Complex.exp (twoPiI * (N + 1 : ℕ) * (x : ℂ)) -
      Complex.exp (twoPiI * (-(N : ℤ)) * (x : ℂ)) := by
  let e (m : ℤ) := Complex.exp (twoPiI * m * (x : ℂ))
  have he (m : ℤ) :
      e m * (Complex.exp (twoPiI * (x : ℂ)) - 1) = e (m + 1) - e m := by
    simp only [mul_sub, mul_one, e, ← Complex.exp_add, Int.cast_add, Int.cast_one]
    congr 2
    ring
  rw [Finset.sum_mul]
  change (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), e m * _) = _
  simp_rw [he]
  have hsum :
      ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (e (m + 1) - e m) =
        ∑ i ∈ Finset.range (2 * N + 1), (e ((i : ℤ) - N + 1) - e ((i : ℤ) - N)) := by
    symm
    apply Finset.sum_bij (fun (i : ℕ) _ ↦ (i : ℤ) - N)
    · intro i hi
      simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢
      omega
    · intro i _ j _ hij
      omega
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      refine ⟨(m + N).toNat, Finset.mem_range.mpr (by omega), by omega⟩
    · intro i _
      rfl
  rw [hsum]
  let E (i : ℕ) := e ((i : ℤ) - N)
  have hstep (i : ℕ) : (i : ℤ) - N + 1 = ((i + 1 : ℕ) : ℤ) - N := by omega
  simp_rw [hstep]
  change (∑ i ∈ Finset.range (2 * N + 1), (E (i + 1) - E i)) = _
  rw [Finset.sum_range_sub]
  have hlast : ((2 * N + 1 : ℕ) : ℤ) - N = (N : ℤ) + 1 := by omega
  change e ((↑(2 * N + 1) : ℤ) - ↑N) - e ((0 : ℤ) - ↑N) = _
  rw [hlast, zero_sub]
  simp [e]

private theorem fourier_indicator_eq_integral_exp (Q : ℝ → ℂ) (b w : ℝ) :
    𝓕 ((Ioc 0 b).indicator Q) w =
      ∫ x in Ioc 0 b, Complex.exp (twoPiI * (-(w : ℂ)) * (x : ℂ)) * Q x := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ioc 0 b
  · simp only [indicator_of_mem hx, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    congr 2
    ring
  · simp [hx]

/-- A Riemann–Lebesgue argument for symmetric Fourier sums at a jump. The quotient
hypothesis measures how fast the even part approaches its limiting value at zero. -/
theorem tendsto_symmetric_fourier_integrals_of_integrable_quotient
    {F : ℝ → ℂ} (hF : IntervalIntegrable F volume (-(1 / 2)) (1 / 2)) {L : ℂ}
    (hquot : IntegrableOn
      (fun x : ℝ ↦ (F x + F (-x) - 2 * L) / (Complex.exp (twoPiI * (x : ℂ)) - 1))
      (Ioc 0 (1 / 2))) :
    Tendsto (fun N : ℕ ↦ ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), Complex.exp (twoPiI * (m : ℂ) * (x : ℂ)) * F x)
      atTop (𝓝 L) := by
  let b : ℝ := 1 / 2
  have hb : 0 ≤ b := by norm_num [b]
  let e (m : ℤ) (x : ℝ) := Complex.exp (twoPiI * (m : ℂ) * (x : ℂ))
  let D (N : ℕ) (x : ℝ) := ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), e m x
  have he (m : ℤ) : Continuous (e m) := by dsimp [e]; fun_prop
  have hD (N : ℕ) : Continuous (D N) := continuous_finsetSum _ fun m _ ↦ he m
  have hDeven (N : ℕ) (x : ℝ) : D N (-x) = D N x := by
    unfold D
    apply Finset.sum_bij (fun m _ ↦ -m)
    · intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    · intro m _ n _ h
      omega
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      exact ⟨-m, Finset.mem_Icc.mpr (by omega), by simp⟩
    · intro m _
      simp [e]
  have hmass (N : ℕ) : (∫ x in -b..b, D N x) = 1 := by
    rw [show (fun x ↦ D N x) = fun x ↦ ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), e m x from rfl,
      intervalIntegral.integral_finsetSum (fun m _ ↦ (he m).intervalIntegrable _ _)]
    have heint (m : ℤ) (hm : m ≠ 0) : (∫ x in -b..b, e m x) = 0 := by
      have hconst : twoPiI * (m : ℂ) ≠ 0 := by
        have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
        exact mul_ne_zero
          (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
            Complex.I_ne_zero) hm'
      rw [show (fun x ↦ e m x) = _ from rfl, integral_exp_mul_complex hconst]
      have hends : e m b = e m (-b) := by
        have hperiod := Complex.exp_int_mul_two_pi_mul_I m
        have harg : twoPiI * (m : ℂ) * (b : ℂ) =
            twoPiI * (m : ℂ) * ((-b : ℝ) : ℂ) + (m : ℂ) * twoPiI := by
          simp [b]
          ring
        simp only [e, harg, Complex.exp_add, hperiod, mul_one]
      change (e m b - e m (-b)) / _ = _
      rw [hends, sub_self, zero_div]
    rw [Finset.sum_eq_single 0 (fun m _ hm ↦ heint m hm)]
    · norm_num [e, b, intervalIntegral.integral_const, smul_eq_mul]
    · simp
  let Q (x : ℝ) := (F x + F (-x) - 2 * L) / (Complex.exp (twoPiI * (x : ℂ)) - 1)
  have hnonzero (x : ℝ) (hx : x ∈ Ioc 0 b) : Complex.exp (twoPiI * (x : ℂ)) - 1 ≠ 0 := by
    have hx' : 0 < Real.pi * x := mul_pos Real.pi_pos hx.1
    have hx'' : Real.pi * x < Real.pi := by
      have : x < 1 := hx.2.trans_lt (by norm_num [b])
      nlinarith [mul_pos Real.pi_pos (sub_pos.mpr this)]
    have heq : twoPiI * (x : ℂ) = Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) := by
      push_cast
      ring
    rw [← norm_ne_zero_iff, heq, Complex.norm_exp_I_mul_ofReal_sub_one]
    have hs : 0 < Real.sin (2 * Real.pi * x / 2) := by
      rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring]
      exact Real.sin_pos_of_pos_of_lt_pi hx' hx''
    exact norm_ne_zero_iff.mpr (mul_ne_zero two_ne_zero hs.ne')
  have hfold (H : ℝ → ℂ) (hH : IntervalIntegrable H volume (-b) b) (N : ℕ) :
      (∫ x in -b..b, D N x * H x) =
        ∫ x in (0 : ℝ)..b, D N x * (H x + H (-x)) := by
    have hi : IntervalIntegrable (fun x ↦ D N x * H x) volume (-b) b := by
      simpa only [mul_comm] using hH.mul_continuousOn (hD N).continuousOn
    have hleft : IntervalIntegrable (fun x ↦ D N x * H x) volume (-b) 0 := by
      apply hi.mono_set
      rw [uIcc_of_le (neg_nonpos.mpr hb), uIcc_of_le (by linarith : -b ≤ b)]
      exact Icc_subset_Icc_right hb
    have hright : IntervalIntegrable (fun x ↦ D N x * H x) volume 0 b := by
      apply hi.mono_set
      rw [uIcc_of_le hb, uIcc_of_le (by linarith : -b ≤ b)]
      exact Icc_subset_Icc_left (neg_nonpos.mpr hb)
    have hreflect : IntervalIntegrable (fun x ↦ D N x * H (-x)) volume 0 b := by
      have := (IntervalIntegrable.iff_comp_neg).mp hleft
      simpa only [hDeven, neg_neg, neg_zero] using this.symm
    have hneg : (∫ x in (0 : ℝ)..b, D N x * H (-x)) = ∫ x in -b..0, D N x * H x := by
      simpa only [hDeven, neg_zero] using
        (intervalIntegral.integral_comp_neg (f := fun x ↦ D N x * H x) (a := 0) (b := b))
    simp_rw [mul_add]
    rw [intervalIntegral.integral_add hright hreflect, hneg, add_comm,
      intervalIntegral.integral_add_adjacent_intervals hleft hright]
  let q := (Ioc 0 b).indicator Q
  have hfreq (N : ℕ) :
      (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∫ x in -b..b, e m x * F x) - L =
        (𝓕 q (-(N : ℝ) - 1)) - (𝓕 q (N : ℝ)) := by
    have hsum :
        (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∫ x in -b..b, e m x * F x) =
          ∫ x in -b..b, D N x * F x := by
      rw [← intervalIntegral.integral_finsetSum]
      · simp_rw [D, Finset.sum_mul]
      · intro m _
        simpa only [mul_comm] using hF.mul_continuousOn (he m).continuousOn
    have hsub :
        (∫ x in -b..b, D N x * F x) - L = ∫ x in -b..b, D N x * (F x - L) := by
      simp_rw [mul_sub]
      have hprod : IntervalIntegrable (fun x ↦ D N x * F x) volume (-b) b := by
        simpa only [mul_comm] using hF.mul_continuousOn (hD N).continuousOn
      rw [intervalIntegral.integral_sub hprod ((hD N).intervalIntegrable _ _ |>.mul_const L),
        intervalIntegral.integral_mul_const, hmass N, one_mul]
    have hQ : Integrable Q (volume.restrict (Ioc 0 b)) := hquot
    let A (x : ℝ) := Complex.exp (twoPiI * (N + 1 : ℕ) * (x : ℂ))
    let B (x : ℝ) := e (-(N : ℤ)) x
    have hA : Continuous A := by dsimp [A]; fun_prop
    have hB : Continuous B := he _
    have hAnorm (x : ℝ) : ‖A x‖ ≤ 1 := by simp [A, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
    have hBnorm (x : ℝ) : ‖B x‖ ≤ 1 := by
      simp [B, e, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
    rw [hsum, hsub, hfold _ (hF.sub intervalIntegrable_const), intervalIntegral.integral_of_le hb]
    calc
      _ = ∫ x in Ioc 0 b, A x * Q x - B x * Q x := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        have hDformula :
            D N x * (Complex.exp (twoPiI * (x : ℂ)) - 1) = A x - B x := by
          simpa only [D, e, A, B, Int.cast_neg, Int.cast_natCast] using
            sum_exp_int_mul_sub_one N x
        change D N x * (F x - L + (F (-x) - L)) = A x * Q x - B x * Q x
        rw [← sub_mul, ← hDformula]
        dsimp only [Q]
        field_simp [hnonzero x hx]
        ring
      _ = (∫ x in Ioc 0 b, A x * Q x) - (∫ x in Ioc 0 b, B x * Q x) :=
        integral_sub (hQ.bdd_mul hA.aestronglyMeasurable (Eventually.of_forall hAnorm))
          (hQ.bdd_mul hB.aestronglyMeasurable (Eventually.of_forall hBnorm))
      _ = _ := by
        change _ = 𝓕 ((Ioc 0 b).indicator Q) (-(N : ℝ) - 1) -
          𝓕 ((Ioc 0 b).indicator Q) (N : ℝ)
        rw [fourier_indicator_eq_integral_exp, fourier_indicator_eq_integral_exp]
        have hAeq (x : ℝ) : A x = Complex.exp
            (twoPiI * (-((-(N : ℝ) - 1 : ℝ) : ℂ)) * (x : ℂ)) := by
          simp [A, Complex.ofReal_sub, add_comm]
        have hBeq (x : ℝ) : B x = Complex.exp
            (twoPiI * (-(N : ℂ)) * (x : ℂ)) := by
          simp [B, e]
        simp_rw [hAeq, hBeq, Complex.ofReal_natCast]
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun n : ℕ ↦ -(n : ℝ) - 1) atTop atBot :=
    (tendsto_atBot_add_const_right _ (-1) (tendsto_neg_atTop_atBot.comp hn)).congr (fun _ ↦ (sub_eq_add_neg ..).symm)
  have hRL := Real.zero_at_infty_fourier q
  have hlim := (hRL.comp (hp.mono_right atBot_le_cocompact)).sub
    (hRL.comp (hn.mono_right atTop_le_cocompact))
  simp only [sub_self] at hlim
  have hadd := (hlim.congr (fun n ↦ (hfreq n).symm)).add_const L
  simpa [e, b] using hadd


/-- A small punctured neighborhood of every integer avoids a fixed finite set. -/
private theorem exists_radius_avoiding_shifted_finite {S : Set ℝ} (hS : S.Finite) :
    ∃ δ ∈ Ioc (0 : ℝ) 1, ∀ (n : ℤ) (x : ℝ), x ≠ 0 → |x| < δ → x + n ∉ S := by
  obtain ⟨M, hM⟩ := hS.isCompact.isBounded.exists_norm_le
  let B := {n : ℤ | (n : ℝ) ∈ Icc (-(M + 1)) (M + 1)}
  have hB : B.Finite := by
    have he := Int.tendsto_coe_cofinite.eventually
      (isCompact_Icc (a := -(M + 1)) (b := M + 1)).compl_mem_cocompact
    simpa only [eventually_cofinite, mem_compl_iff, not_not, B, mem_ofPred_eq] using he
  have hne (n : ℤ) : ∀ᶠ x in 𝓝 (0 : ℝ), x ≠ 0 → x + (n : ℝ) ∉ S := by
    let T := ((fun x : ℝ ↦ x + (n : ℝ)) ⁻¹' S) \ {(0 : ℝ)}
    have hT : T.Finite :=
      (hS.preimage (add_left_injective (n : ℝ)).injOn).subset sdiff_subset
    have hT₀ : 0 ∈ Tᶜ := fun hx ↦ hx.2 (mem_singleton _)
    filter_upwards [hT.isClosed.isOpen_compl.mem_nhds hT₀] with x hx hx₀ hxS
    exact hx ⟨hxS, hx₀⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hB.eventually_all.mpr (fun n _ ↦ hne n))
  refine ⟨min r 1, ⟨lt_min hr zero_lt_one, min_le_right _ _⟩, ?_⟩
  intro n x hx hxr hxS
  have hx1 : |x| ≤ 1 := (hxr.trans_le (min_le_right _ _)).le
  have hn : n ∈ B := by
    change (n : ℝ) ∈ Icc (-(M + 1)) (M + 1)
    apply abs_le.mp
    calc
      |(n : ℝ)| = |x + (n : ℝ) - x| := by ring_nf
      _ ≤ |x + (n : ℝ)| + |x| := abs_sub _ _
      _ ≤ M + 1 := add_le_add (by simpa only [Real.norm_eq_abs] using hM _ hxS) hx1
  exact hball (by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using
      hxr.trans_le (min_le_left _ _)) n hn hx hxS

/-- Uniform exponential bounds for a profile and its derivative give a Lipschitz
estimate for the symmetric part of its periodization at a lattice point. -/
theorem periodization_bounds_of_exp_decay
    {g : ℝ → ℂ} {S : Set ℝ} (hS : S.Finite) {A b : ℝ} (hA : 0 < A) (hb : 0 < b)
    (hg : ∀ x, ‖g x‖ ≤ A * Real.exp (-b * |x|))
    (hderiv : ∀ x ∉ S, DifferentiableAt ℝ g x ∧ ‖deriv g x‖ ≤ A * Real.exp (-b * |x|))
    {u v : ℤ → ℂ}
    (hu : ∀ n : ℤ, Tendsto (fun x : ℝ ↦ g (x + n)) (𝓝[>] 0) (𝓝 (u n)))
    (hv : ∀ n : ℤ, Tendsto (fun x : ℝ ↦ g (-x + n)) (𝓝[>] 0) (𝓝 (v n))) :
    let F (x : ℝ) := ∑' n : ℤ, g (x + n)
    let L := ∑' n : ℤ, (u n + v n) / 2
    ∃ C ≥ (0 : ℝ),
      (∀ x ∈ Icc (-(1 / 2) : ℝ) (1 / 2), ‖F x‖ ≤ C) ∧
      ∀ x ∈ Ioc (0 : ℝ) (1 / 2), ‖F x + F (-x) - 2 * L‖ ≤ C * x := by
  dsimp only
  let F (x : ℝ) := ∑' n : ℤ, g (x + n)
  let B (n : ℤ) := (A * Real.exp b) * Real.exp (|(n : ℝ)| * -b)
  have hB₀ (n : ℤ) : 0 ≤ B n := by dsimp [B]; positivity
  have hBs : Summable B := by
    have hgeom := Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hb)
    apply Summable.mul_left
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor <;> simpa [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using hgeom
  let M := ∑' n : ℤ, B n
  have hM : 0 ≤ M := tsum_nonneg hB₀
  have hmaj (n : ℤ) {x : ℝ} (hx : |x| ≤ 1) : A * Real.exp (-b * |x + n|) ≤ B n := by
    have htri : |(n : ℝ)| ≤ |x + n| + |x| := by
      simpa only [add_sub_cancel_left] using (abs_sub (x + (n : ℝ)) x)
    dsimp [B]
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hA.le
    nlinarith only [mul_le_mul_of_nonneg_left htri hb.le, mul_le_mul_of_nonneg_left hx hb.le]
  have hnorm {x : ℝ} (hx : |x| ≤ 1) :
      Summable (fun n : ℤ ↦ ‖g (x + n)‖) :=
    .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ (hg _).trans (hmaj n hx)) hBs
  have hF (x : ℝ) (hx : |x| ≤ 1) : ‖F x‖ ≤ M := by
    exact (norm_tsum_le_tsum_norm (hnorm hx)).trans
      ((hnorm hx).tsum_le_tsum (fun n ↦ (hg _).trans (hmaj n hx)) hBs)
  have hside {w : ℤ → ℂ} {e : ℝ} (he : |e| = 1)
      (hw : ∀ n : ℤ, Tendsto (fun x : ℝ ↦ g (e * x + n)) (𝓝[>] 0) (𝓝 (w n))) :
      ∀ n : ℤ, ‖w n‖ ≤ B n := by
    intro n
    apply le_of_tendsto (hw n).norm
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one)] with x hx
    exact (hg _).trans (hmaj n (by simpa [abs_mul, he, abs_of_pos hx.1] using hx.2.le))
  have hule := hside (e := 1) (by norm_num) (by simpa using hu)
  have hvle := hside (e := -1) (by norm_num) (by simpa using hv)
  have hus : Summable (fun n ↦ ‖u n‖) := .of_nonneg_of_le (fun _ ↦ norm_nonneg _) hule hBs
  have hvs : Summable (fun n ↦ ‖v n‖) := .of_nonneg_of_le (fun _ ↦ norm_nonneg _) hvle hBs
  have huSum : ‖∑' n, u n‖ ≤ M :=
    (norm_tsum_le_tsum_norm hus).trans (hus.tsum_le_tsum hule hBs)
  have hvSum : ‖∑' n, v n‖ ≤ M :=
    (norm_tsum_le_tsum_norm hvs).trans (hvs.tsum_le_tsum hvle hBs)
  obtain ⟨δ, hδ, hnoCut⟩ := exists_radius_avoiding_shifted_finite hS
  have hδpos : 0 < δ := hδ.1
  have hlarge : 0 ≤ 4 * M / δ := div_nonneg (mul_nonneg (by norm_num) hM) hδpos.le
  have hslope {w : ℤ → ℂ} {e : ℝ} (he : |e| = 1)
      (hw : ∀ n : ℤ, Tendsto (fun x : ℝ ↦ g (e * x + n)) (𝓝[>] 0) (𝓝 (w n)))
      (n : ℤ) {x : ℝ} (hx : x ∈ Ioo 0 δ) :
      ‖g (e * x + n) - w n‖ ≤ B n * x := by
    let p (y : ℝ) := g (e * y + n)
    have hdiff (y : ℝ) (hy : y ∈ Ioo 0 δ) :
        HasDerivAt p (e • deriv g (e * y + n)) y := by
      have hnormE : |e * y| = y := by rw [abs_mul, he, one_mul, abs_of_pos hy.1]
      have hcut := hnoCut n (e * y) (abs_pos.mp (hnormE.symm ▸ hy.1)) (hnormE.symm ▸ hy.2)
      simpa [p, Function.comp_def] using
        ((hderiv _ hcut).1.hasDerivAt.scomp y (((hasDerivAt_id y).const_mul e).add_const (n : ℝ)))
    have hbound (y : ℝ) (hy : y ∈ Ioo 0 δ) : ‖e • deriv g (e * y + n)‖ ≤ B n := by
      have hnormE : |e * y| = y := by rw [abs_mul, he, one_mul, abs_of_pos hy.1]
      have hcut := hnoCut n (e * y) (abs_pos.mp (hnormE.symm ▸ hy.1)) (hnormE.symm ▸ hy.2)
      simpa only [norm_smul, Real.norm_eq_abs, he, one_mul] using
        ((hderiv _ hcut).2.trans (hmaj n (hnormE.symm ▸ hy.2.le.trans hδ.2)))
    have hxlim : Tendsto (fun y : ℝ ↦ B n * ‖x - y‖) (𝓝[>] 0) (𝓝 (B n * x)) := by
      have h₀ : Tendsto (fun y : ℝ ↦ y) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
      simpa [Real.norm_eq_abs, abs_of_pos hx.1] using (h₀.const_sub x).norm.const_mul (B n)
    apply le_of_tendsto_of_tendsto ((hw n).const_sub (p x)).norm hxlim
    filter_upwards [Ioo_mem_nhdsGT hδ.1] with y hy
    exact (convex_Ioo (0 : ℝ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz ↦ (hdiff z hz).hasDerivWithinAt) hbound hy hx
  have hlimit (x : ℝ) (hx : x ∈ Ioo 0 δ) :
      ‖F x - ∑' n, u n‖ ≤ M * x ∧ ‖F (-x) - ∑' n, v n‖ ≤ M * x := by
    have hx₁ : |x| ≤ 1 := by rw [abs_of_pos hx.1]; exact hx.2.le.trans hδ.2
    have ht (e : ℝ) (he : |e| = 1) (w : ℤ → ℂ) (hs : Summable fun n ↦ ‖w n‖)
        (hw : ∀ n : ℤ, Tendsto (fun y : ℝ ↦ g (e * y + n)) (𝓝[>] 0) (𝓝 (w n))) :
        ‖F (e * x) - ∑' n, w n‖ ≤ M * x := by
      have hBxs := hBs.mul_right x
      have h := hslope he hw (x := x)
      have hr : Summable (fun n : ℤ ↦ ‖g (e * x + n) - w n‖) :=
        .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ h n hx) hBxs
      have hgs := hnorm (x := e * x) (by simpa [abs_mul, he] using hx₁)
      rw [show F (e * x) - ∑' n, w n = ∑' n : ℤ, (g (e * x + n) - w n) from
        (hgs.of_norm.tsum_sub hs.of_norm).symm, ← hBs.tsum_mul_right x]
      exact (norm_tsum_le_tsum_norm hr).trans (hr.tsum_le_tsum (fun n ↦ h n hx) hBxs)
    exact ⟨by simpa using ht 1 (by norm_num) u hus (by simpa using hu),
      by simpa using ht (-1) (by norm_num) v hvs (by simpa using hv)⟩
  let C := M + 2 * M + 4 * M / δ
  have hCM : M ≤ C := by
    dsimp [C]
    linarith only [hM, hlarge]
  refine ⟨C, hM.trans hCM, ?_, ?_⟩
  · intro x hx
    have hx₁ : |x| ≤ 1 := (abs_le.mpr hx).trans (by norm_num)
    exact (hF x hx₁).trans hCM
  · intro x hx
    have hx₁ : |x| ≤ 1 := by rw [abs_of_pos hx.1]; exact hx.2.trans (by norm_num)
    have hrewrite :
        2 * (∑' n, (u n + v n) / 2) = (∑' n, u n) + (∑' n, v n) := by
      rw [← tsum_mul_left]
      have htwo (n : ℤ) : (2 : ℂ) * ((u n + v n) / 2) = u n + v n := by ring
      simp_rw [htwo]
      exact hus.of_norm.tsum_add hvs.of_norm
    simp only [hrewrite]
    rw [show F x + F (-x) - ((∑' n, u n) + ∑' n, v n) =
      (F x - ∑' n, u n) + (F (-x) - ∑' n, v n) by ring]
    apply (norm_add_le _ _).trans
    by_cases h : x < δ
    · obtain ⟨h₁, h₂⟩ := hlimit x ⟨hx.1, h⟩
      exact (add_le_add h₁ h₂).trans (by
        dsimp [C]
        nlinarith [mul_nonneg hM hx.1.le, mul_nonneg hlarge hx.1.le])
    · have h₁ := (norm_sub_le _ _).trans (add_le_add (hF x hx₁) huSum)
      have h₂ := (norm_sub_le _ _).trans (add_le_add (hF (-x) (by rwa [abs_neg])) hvSum)
      have hbig : 4 * M ≤ (4 * M / δ) * x := by
        calc
          4 * M = (4 * M / δ) * δ := by field_simp [hδ.1.ne']
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_of_not_gt h) hlarge
      exact (add_le_add h₁ h₂).trans (by
        dsimp [C]
        nlinarith [mul_nonneg hM hx.1.le])

end SymmetricPoissonSummation

end RiemannMasullo
