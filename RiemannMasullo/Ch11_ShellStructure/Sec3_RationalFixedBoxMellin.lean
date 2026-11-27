module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxDivision
public import RiemannMasullo.ForMathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! # The actual rational theta Mellin rows of a fixed-box stage

Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496. Real Poisson summation unfolds
the polar even theta source into the archimedean Mellin integral and
`2 ζ(1−z)` to the left of the imaginary line. A dominated limit and the
zeta residue give the actual boundary samples including the removable
value at zero. These are the samples that feed the smaller-box division,
not an abstract replacement for the theta source. -/

public noncomputable section

open Filter MeasureTheory Set FourierTransform
open scoped Asymptotics FourierTransform SchwartzMap Topology

namespace RiemannMasullo.RationalPacket

private theorem arch_top {U : ℝ} (h : 𝓢(ℝ, ℂ))
    (hb : ∀ r, U < |r| → h r = 0) (a : ℝ) :
    (⇑h) =O[atTop] (fun r : ℝ ↦ r ^ (-a)) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop U] with r hr
  simp [hb r (hr.trans_le (le_abs_self r))]

private theorem arch_bot (h : 𝓢(ℝ, ℂ)) :
    (⇑h) =O[𝓝[>] 0] (fun r : ℝ ↦ r ^ (-(0 : ℝ))) := by
  apply Asymptotics.IsBigO.of_bound (SchwartzMap.seminorm ℂ 0 0 h)
  exact Eventually.of_forall fun r ↦ by simpa using h.norm_le_seminorm ℂ r

private theorem arch_exp_subst (h : 𝓢(ℝ, ℂ)) (s : ℂ) (y : ℝ) :
    Real.exp y • (((Real.exp y : ℝ) : ℂ) ^ (s-1) • h (Real.exp y)) =
      Complex.exp (s * y) * h (Real.exp y) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos y).ne'),
    ← Complex.ofReal_log (Real.exp_pos y).le, Real.log_exp]
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2; ring

private theorem archLogMellin_integrable {U : ℝ} (h : 𝓢(ℝ, ℂ))
    (hb : ∀ r, U < |r| → h r = 0) {z : ℂ} (hz : z.re < 1) :
    Integrable (fun y : ℝ ↦ Complex.exp ((1-z) * y) * h (Real.exp y)) := by
  have hc : MellinConvergent (⇑h) (1-z) := mellinConvergent_of_isBigO_rpow
    (h.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (arch_top h hb ((1-z).re+1)) (lt_add_one _) (arch_bot h) (by simpa using sub_pos.mpr hz)
  simpa only [arch_exp_subst] using (integrable_comp_exp _).2 hc

private theorem integral_archLogMellin (h : 𝓢(ℝ, ℂ)) (z : ℂ) :
    (∫ y : ℝ, Complex.exp ((1-z) * y) * h (Real.exp y)) = mellin (⇑h) (1-z) := by
  simpa only [mellin, arch_exp_subst] using
    (integral_comp_exp (fun t : ℝ ↦ (t : ℂ) ^ ((1-z)-1) • h t))

private theorem archMellin_hasDerivAt {U : ℝ} (h : 𝓢(ℝ, ℂ))
    (hb : ∀ r, U < |r| → h r = 0) {z : ℂ} (hz : z.re < 1) :
    HasDerivAt (fun w : ℂ ↦ mellin (⇑h) (1-w))
      (-mellin (fun r ↦ Real.log r • h r) (1-z)) z := by
  have hd := (mellin_hasDerivAt_of_isBigO_rpow (s := 1-z)
    (h.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (arch_top h hb ((1-z).re+1)) (lt_add_one (1-z).re) (arch_bot h)
    (by simpa using sub_pos.mpr hz)).2
  simpa [Function.comp_def] using hd.comp z ((hasDerivAt_id z).const_sub (1 : ℂ))

private theorem arch_even_fold {g : ℝ → ℂ} (hi : Integrable g) (he : ∀ r, g (-r) = g r) :
    (∫ r, g r) = 2 * ∫ r in Ioi 0, g r := by
  have hneg := integral_comp_neg_Ioi 0 g
  simp only [he, neg_zero] at hneg
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ)) hi.integrableOn hi.integrableOn,
    ← hneg, two_mul]

private theorem archMellin_mass (h : 𝓢(ℝ, ℂ)) (he : ∀ r, h (-r) = h r) :
    (∫ r, h r) = 2 * mellin (⇑h) 1 := by
  simpa [mellin] using arch_even_fold h.integrable he

private theorem arch_logMoment_integrable {U : ℝ} (hU : 0 < U) (h : 𝓢(ℝ, ℂ))
    (hb : ∀ r, U < |r| → h r = 0) : Integrable (fun r ↦ (Real.log r : ℂ) * h r) := by
  have hl : IntegrableOn Real.log (Icc (-U) U) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1 intervalIntegral.intervalIntegrable_log'
  have hi : IntegrableOn (fun r ↦ (Real.log r : ℂ) * h r) (Icc (-U) U) volume := by
    apply (hl.norm.const_mul (SchwartzMap.seminorm ℂ 0 0 h)).mono'
      ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).mul h.continuous.measurable).aestronglyMeasurable
    filter_upwards with r
    change ‖(Real.log r : ℂ) * h r‖ ≤ _
    rw [norm_mul, Complex.norm_real, mul_comm]
    exact mul_le_mul_of_nonneg_right (h.norm_le_seminorm ℂ r) (norm_nonneg _)
  apply hi.integrable_of_forall_notMem_eq_zero
  intro r hr
  rw [hb r (lt_of_not_ge (fun hle ↦ hr (abs_le.mp hle))), mul_zero]

private theorem archMellin_zero_logMoment {U : ℝ} (hU : 0 < U) (h : 𝓢(ℝ, ℂ))
    (hb : ∀ r, U < |r| → h r = 0) (he : ∀ r, h (-r) = h r) :
    -2 * deriv (fun z : ℂ ↦ mellin (⇑h) (1-z)) 0 = ∫ r, (Real.log r : ℂ) * h r := by
  rw [(archMellin_hasDerivAt h hb (z := 0) (by norm_num)).deriv,
    arch_even_fold (arch_logMoment_integrable hU h hb) (fun r ↦ by simp [he])]
  simp [mellin, Complex.real_smul, smul_eq_mul]

private theorem empty_poisson_positive (f : 𝓢(ℝ, ℂ)) {U : ℝ}
    (he : ∀ r : ℝ, (𝓕 f) (-r) = (𝓕 f) r) (h0 : (𝓕 f) 0 = 0)
    (hb : ∀ r : ℝ, U < |r| → (𝓕 f) r = 0) (x : ℝ) :
    dampedStage ∅ f x = ((Real.exp x)⁻¹ : ℝ) •
      (2 * ∑' n : ℕ, (𝓕 f) (((n : ℝ) + 1) / Real.exp x)) := by
  have hx := Real.exp_pos x
  let a (n : ℤ) := (𝓕 f) ((n : ℝ) / Real.exp x)
  have hpos : Summable (fun n : ℕ ↦ a n) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (U * Real.exp x)
    apply (summable_nat_add_iff N).mp
    have hz (n : ℕ) : a ((n : ℤ) + (N : ℤ)) = 0 := by
      apply hb
      simp only [Int.cast_add, Int.cast_natCast]
      rw [abs_of_nonneg (by positivity), lt_div_iff₀ hx]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    simp [hz]
  have hn (n : ℕ) : a (-(n + 1)) = a ((n + 1 : ℕ) : ℤ) := by
    dsimp only [a]
    push_cast
    rw [neg_div, he]
  have hneg : Summable (fun n : ℕ ↦ a (-(n + 1))) := by
    simpa only [hn] using ((summable_nat_add_iff 1).mpr hpos)
  have hsum := tsum_of_nat_of_neg_add_one (f := a) hpos hneg
  rw [hpos.tsum_eq_zero_add] at hsum
  simp only [hn] at hsum
  have ht : dampedStage ∅ f x = theta f (Real.exp x) := by
    simp [dampedStage_eq_sum]
  rw [ht, theta_eq_poisson f hx]
  congr 1
  simpa [a, h0, two_mul] using hsum

/-- Exact left-half-plane unfolding of the untwisted empty theta stage. -/
theorem thetaMellin_eq_zeta_mul_archLog (f : 𝓢(ℝ, ℂ)) {U : ℝ} {z : ℂ}
    (he : ∀ r : ℝ, (𝓕 f) (-r) = (𝓕 f) r) (h0 : (𝓕 f) 0 = 0)
    (hb : ∀ r : ℝ, U < |r| → (𝓕 f) r = 0) (hz : z.re < 0)
    (hQ : Integrable (fun y : ℝ ↦ Complex.exp ((1-z)*(y:ℂ)) * (𝓕 f) (Real.exp y))) :
    (∫ x : ℝ, Complex.exp (z * (x : ℂ)) * dampedStage ∅ f x) =
      2 * riemannZeta (1-z) * ∫ y : ℝ, Complex.exp ((1-z)*(y:ℂ)) * (𝓕 f) (Real.exp y) := by
  let Q (y : ℝ) := Complex.exp ((1-z)*(y:ℂ)) * (𝓕 f) (Real.exp y)
  let k (n : ℕ) : ℝ := n + 1
  have hk (n : ℕ) : 0 < k n := by dsimp [k]; positivity
  let c (n : ℕ) := 1 / (k n : ℂ) ^ (1-z)
  let F (n : ℕ) (x : ℝ) := c n * Q (Real.log (k n) - x)
  have hc (n : ℕ) : c n = Complex.exp (-((Real.log (k n) : ℂ) * (1-z))) := by
    dsimp only [c]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hk n).ne'),
      ← Complex.ofReal_log (hk n).le, Complex.exp_neg, one_div]
  have hterm (n : ℕ) (x : ℝ) : F n x = Complex.exp ((z-1)*(x:ℂ)) *
      (𝓕 f) (k n / Real.exp x) := by
    dsimp only [F, Q]
    rw [hc, Real.exp_sub, Real.exp_log (hk n), Complex.ofReal_sub, ← mul_assoc, ← Complex.exp_add]
    congr 2; ring
  have hp (x : ℝ) : Complex.exp (z * (x : ℂ)) * dampedStage ∅ f x =
      2 * ∑' n : ℕ, F n x := by
    rw [empty_poisson_positive f he h0 hb, Complex.real_smul]
    simp_rw [hterm]
    rw [tsum_mul_left]
    have hx : Complex.exp ((z-1)*(x:ℂ)) = Complex.exp (z*(x:ℂ)) *
        (((Real.exp x)⁻¹ : ℝ) : ℂ) := by
      rw [sub_mul, one_mul, sub_eq_add_neg, Complex.exp_add, Complex.exp_neg,
        ← Complex.ofReal_exp, Complex.ofReal_inv]
    rw [hx]; dsimp only [k]; ring
  have hi (n : ℕ) : Integrable (F n) :=
    ((integrable_comp_sub_left Q (Real.log (k n))).2 hQ).const_mul _
  have hcn (n : ℕ) : ‖c n‖ = 1 / |(n:ℝ)+1| ^ (1-z.re) := by
    dsimp only [c]
    rw [norm_div, norm_one, Complex.norm_cpow_eq_rpow_re_of_pos (hk n), abs_of_pos (hk n)]
    simp [k]
  have hs : Summable (fun n : ℕ ↦ ‖c n‖) := by
    simp_rw [hcn]
    exact (Real.summable_one_div_nat_add_rpow 1 _).2 (by linarith)
  have hnorm (n : ℕ) : (∫ x : ℝ, ‖F n x‖) = ‖c n‖ * ∫ y : ℝ, ‖Q y‖ := by
    simp only [F, norm_mul, integral_const_mul]
    rw [integral_sub_left_eq_self (fun y ↦ ‖Q y‖) volume]
  have hfi (n : ℕ) : (∫ x : ℝ, F n x) = c n * ∫ y : ℝ, Q y := by
    simp only [F, integral_const_mul]
    rw [integral_sub_left_eq_self Q volume]
  have hs' : Summable (fun n : ℕ ↦ ∫ x : ℝ, ‖F n x‖) := by
    simp_rw [hnorm]; exact hs.mul_right _
  have hζ : riemannZeta (1-z) = ∑' n : ℕ, c n := by
    simpa [c, k] using zeta_eq_tsum_one_div_nat_add_one_cpow
      (s := 1-z) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  simp_rw [hp]
  rw [integral_const_mul, ← integral_tsum_of_summable_integral_norm hi hs']
  simp_rw [hfi]
  rw [tsum_mul_right, ← hζ, mul_assoc]

/-- Approach the imaginary axis from the open left half-plane. -/
private def thetaLeftPoint (t : ℝ) (n : ℕ) : ℂ :=
  (t : ℂ) * Complex.I - ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)

private theorem leftPoint_lim (t : ℝ) :
    Tendsto (thetaLeftPoint t) atTop (𝓝 ((t : ℂ) * Complex.I)) := by
  have hs : Tendsto (fun n : ℕ ↦ ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 0) := by
    change Tendsto (Complex.ofReal ∘ (fun n : ℕ ↦ 1 / ((n : ℝ) + 1))) atTop (𝓝 0)
    simpa only [Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  change Tendsto (fun n : ℕ ↦ (t : ℂ) * Complex.I - ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) _ _
  simpa only [sub_zero] using (tendsto_const_nhds (x := (t : ℂ) * Complex.I)).sub hs

private theorem leftPoint_re (t : ℝ) (n : ℕ) : (thetaLeftPoint t n).re < 0 := by
  have h : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  rw [thetaLeftPoint, Complex.sub_re, Complex.ofReal_re,
    show ((t : ℂ) * Complex.I).re = 0 by simp [Complex.mul_re], zero_sub]
  exact neg_lt_zero.mpr h

/-- The empty-stage theta transform with the positive exponential convention. -/
def thetaBoundaryMellin (f : 𝓢(ℝ, ℂ)) (z : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (z * (x : ℂ)) * dampedStage ∅ f x

private theorem tendsto_thetaMellin_fromLeft {f : 𝓢(ℝ, ℂ)} {U : ℝ} (hU : 0 < U)
    (hf : f 0 = 0) (h0 : (𝓕 f) 0 = 0)
    (hbox : ∀ y : ℝ, U < |y| → (𝓕 f) y = 0) (t : ℝ) :
    Tendsto (fun n ↦ thetaBoundaryMellin f (thetaLeftPoint t n)) atTop
      (𝓝 (thetaBoundaryMellin f ((t : ℂ) * Complex.I))) := by
  have hi := (stage_memLp_and_dampedStage_integrable hU ∅ (by simp) hf h0
    (by simpa using hbox)).2
  apply tendsto_integral_of_dominated_convergence
    (fun x : ℝ ↦ Real.exp (max 0 (Real.log U)) * ‖dampedStage ∅ f x‖)
  · intro n
    exact (show Continuous (fun x : ℝ ↦ Complex.exp (thetaLeftPoint t n * (x : ℂ))) by
      fun_prop).aestronglyMeasurable.mul hi.aestronglyMeasurable
  · exact hi.norm.const_mul _
  · intro n
    apply Eventually.of_forall
    intro x
    by_cases hx : x < -Real.log U
    · have hz : theta f (Real.exp x) = 0 :=
        theta_eq_zero_of_lt (Real.exp_pos x) h0 hbox (by
          rw [← lt_div_iff₀ hU, one_div, ← Real.exp_log hU, ← Real.exp_neg]
          exact Real.exp_lt_exp.mpr hx)
      simp [dampedStage_eq_sum, hz]
    · rw [norm_mul, Complex.norm_exp]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      simp only [thetaLeftPoint, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
        zero_sub, mul_one]
      have ha : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      have hb : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).2 (by
        linarith [Nat.cast_nonneg (α := ℝ) n])
      by_cases h : 0 ≤ x
      · exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) h).trans (le_max_left ..)
      · have hh := mul_le_mul_of_nonneg_right hb (neg_nonneg.mpr (le_of_not_ge h))
        exact (show -(1 / ((n : ℝ) + 1)) * x ≤ Real.log U by linarith).trans (le_max_right ..)
  · apply Eventually.of_forall
    intro x
    exact ((Complex.continuous_exp.tendsto _).comp ((leftPoint_lim t).mul
      (tendsto_const_nhds (x := (x : ℂ))))).mul tendsto_const_nhds

/-- Boundary values of a left factorization. The off-pole coefficient never vanishes;
    at zero its residue pairs with the derivative, not the value, of the vanishing factor. -/
private theorem theta_boundary_factor_and_pole {M A : ℂ → ℂ} {a : ℂ}
    (hM : ∀ t : ℝ, Tendsto (fun n ↦ M (thetaLeftPoint t n)) atTop
      (𝓝 (M ((t : ℂ) * Complex.I))))
    (hfac : ∀ z : ℂ, z.re < 0 → M z = 2 * riemannZeta (1-z) * A z)
    (hcont : ∀ t : ℝ, t ≠ 0 → ContinuousAt A ((t : ℂ) * Complex.I))
    (hA : A 0 = 0) (hd : HasDerivAt A a 0) :
    (∀ t : ℝ, t ≠ 0 → M ((t : ℂ)*Complex.I) =
      2 * riemannZeta (1-(t : ℂ)*Complex.I) * A ((t : ℂ)*Complex.I) ∧
      riemannZeta (1-(t : ℂ)*Complex.I) ≠ 0) ∧ M 0 = -2*a := by
  constructor
  · intro t ht
    have hw : (t : ℂ)*Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero
    have hs : 1-(t : ℂ)*Complex.I ≠ 1 := by intro h; apply hw; linear_combination -h
    constructor
    · apply tendsto_nhds_unique (hM t)
      simp_rw [hfac _ (leftPoint_re t _)]
      exact (tendsto_const_nhds.mul ((differentiableAt_riemannZeta hs).continuousAt.tendsto.comp
        (tendsto_const_nhds.sub (leftPoint_lim t)))).mul ((hcont t ht).tendsto.comp (leftPoint_lim t))
    · apply riemannZeta_ne_zero_of_one_le_re
      simp [Complex.mul_re]
  · let z := thetaLeftPoint 0
    have hz : Tendsto z atTop (𝓝 (0 : ℂ)) := by simpa [z] using leftPoint_lim 0
    have hn (n : ℕ) : z n ≠ 0 := by
      intro h
      have hh := leftPoint_re 0 n
      change (z n).re < 0 at hh
      simp [h] at hh
    have hz' : Tendsto z atTop (𝓝[≠] 0) := tendsto_nhdsWithin_iff.mpr
      ⟨hz, Eventually.of_forall hn⟩
    have hs : Tendsto (fun n ↦ 1-z n) atTop (𝓝[≠] (1 : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨by simpa using (tendsto_const_nhds (x := (1 : ℂ))).sub hz, ?_⟩
      apply Eventually.of_forall
      intro n h
      change 1-z n = 1 at h
      apply hn n
      linear_combination -h
    have hlim := ((tendsto_const_nhds (x := (-2 : ℂ))).mul
      (riemannZeta_residue_one.comp hs)).mul (hd.tendsto_slope.comp hz')
    have hm : Tendsto (fun n ↦ M (z n)) atTop (𝓝 (M 0)) := by simpa [z] using hM 0
    apply tendsto_nhds_unique hm
    apply (show Tendsto _ atTop (𝓝 (-2*a)) by simpa only [mul_one] using hlim).congr'
    apply Eventually.of_forall
    intro n
    change -2 * ((1-z n-1)*riemannZeta (1-z n)) * slope A 0 (z n) = M (z n)
    rw [hfac _ (leftPoint_re 0 n), slope_def_field, hA, sub_zero, sub_zero]
    field_simp [hn n]; ring

private theorem archMass_zero_of_source {f : 𝓢(ℝ, ℂ)} (hf : f 0 = 0)
    (he : ∀ r, (𝓕 f) (-r) = (𝓕 f) r) : mellin (⇑(𝓕 f : 𝓢(ℝ, ℂ))) 1 = 0 := by
  have hi : (𝓕⁻ (𝓕 f)) 0 = 0 := by rw [fourierInv_fourier_eq, hf]
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_zero, Real.fourier_real_eq] at hi
  have hz : (∫ r : ℝ, (𝓕 f) r) = 0 := by simpa using hi
  rw [archMellin_mass (𝓕 f) he] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

private theorem thetaBoundary_fourier_eq (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    thetaBoundaryMellin f (((-2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) =
      𝓕 (dampedStage ∅ f) ξ := by
  rw [thetaBoundaryMellin, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  rw [smul_eq_mul]
  congr 2
  push_cast
  ring

private theorem archMellin_eq_log_fourier {p U : ℝ} (hp : 1 < p) (hU : 0 < U)
    (h : 𝓢(ℝ, ℂ)) (hb : ∀ r, U < |r| → h r = 0) (ξ : ℝ) :
    mellin (⇑h) (1 - (((2 * Real.pi * ξ / Real.log p : ℝ) : ℂ) * Complex.I)) =
      (Real.log p : ℂ) * (𝓕 (rationalLogSchwartzLift hp hU h hb)) ξ := by
  let L := Real.log p
  have hL : 0 < L := Real.log_pos hp
  let z : ℂ := ((2 * Real.pi * ξ / L : ℝ) : ℂ) * Complex.I
  let Q (y : ℝ) := Complex.exp ((1-z) * y) * h (Real.exp y)
  change mellin (⇑h) (1-z) = (L : ℂ) * (𝓕 (rationalLogSchwartzLift hp hU h hb)) ξ
  rw [← integral_archLogMellin, SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  change (∫ y, Q y) = (L : ℂ) * ∫ x : ℝ, _
  have hscale (x : ℝ) : Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) •
      rationalLogSchwartzLift hp hU h hb x = Q (L * x) := by
    rw [rationalLogSchwartzLift_apply]
    change Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) •
      (Real.exp (L*x) • h (Real.exp (L*x))) = Q (L*x)
    dsimp only [Q, z]
    simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp [hL.ne']; ring
  simp_rw [hscale]
  rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hL), Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul, mul_inv_cancel₀ hL.ne', Complex.ofReal_one, one_mul]

/-- The actual empty-stage theta transform has the zeta factor on the full
imaginary line off the pole. Its value at the pole is the real log moment. -/
theorem thetaBoundaryMellin_factor_and_zero {U : ℝ} (hU : 0 < U) (f : 𝓢(ℝ, ℂ))
    (hf : f 0 = 0) (hF0 : (𝓕 f) 0 = 0) (he : ∀ r, (𝓕 f) (-r) = (𝓕 f) r)
    (hb : ∀ r, U < |r| → (𝓕 f) r = 0) :
    (∀ t : ℝ, t ≠ 0 → thetaBoundaryMellin f ((t : ℂ) * Complex.I) =
      2 * riemannZeta (1-(t : ℂ)*Complex.I) *
        mellin (⇑(𝓕 f : 𝓢(ℝ, ℂ))) (1-(t : ℂ)*Complex.I) ∧
      riemannZeta (1-(t : ℂ)*Complex.I) ≠ 0) ∧
    thetaBoundaryMellin f 0 = ∫ r, (Real.log r : ℂ) * (𝓕 f) r := by
  let A (z : ℂ) := mellin (⇑(𝓕 f : 𝓢(ℝ, ℂ))) (1-z)
  have hA : A 0 = 0 := by simpa [A] using archMass_zero_of_source hf he
  have hd (z : ℂ) (hz : z.re < 1) := archMellin_hasDerivAt (𝓕 f) hb hz
  have hz0 : (0 : ℂ).re < 1 := by norm_num
  have h := theta_boundary_factor_and_pole
    (fun t ↦ tendsto_thetaMellin_fromLeft hU hf hF0 hb t)
    (fun z hz ↦ by
      rw [thetaBoundaryMellin, thetaMellin_eq_zeta_mul_archLog f he hF0 hb hz
        (archLogMellin_integrable (𝓕 f) hb (hz.trans zero_lt_one)), integral_archLogMellin])
    (fun t _ ↦ (hd ((t : ℂ) * Complex.I) (by simp [Complex.mul_re])).continuousAt)
    hA (hd 0 hz0)
  refine ⟨h.1, h.2.trans ?_⟩
  rw [← (hd 0 hz0).deriv]
  exact archMellin_zero_logMoment hU (𝓕 f) hb he

private theorem integrable_dampedStage_subsets {U : ℝ} (hU : 0 < U) (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime) (f : 𝓢(ℝ, ℂ)) (hf : f 0 = 0) (hF0 : (𝓕 f) 0 = 0)
    (hb : ∀ r, U < |r| → (𝓕 f) r = 0) (S : Finset ℕ) (hS : S ⊆ T) :
    Integrable (dampedStage S f) := by
  have hprod : 0 < ∏ q ∈ S, (q : ℝ) := Finset.prod_pos fun q hq ↦ by
    exact_mod_cast (hT q (hS hq)).pos
  exact (stage_memLp_and_dampedStage_integrable (X := U * ∏ q ∈ S, (q : ℝ))
    (mul_pos hU hprod) S (fun q hq ↦ (hT q (hS hq)).one_lt.le) hf hF0
    (by simpa only [mul_div_cancel_right₀ _ hprod.ne'] using hb)).2

/-- Source division from the actual earlier-stage nonzero mesh and the
empty-stage value at zero (the leading normalized row, not an earlier-stage value). -/
theorem exists_smaller_box_stage_of_theta_rows {p : ℕ} (hp : p.Prime) (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime) (hmem : p ∉ T) {U : ℝ} (hU : 0 < U)
    (f : 𝓢(ℝ, ℂ)) (hf : f 0 = 0) (hF0 : (𝓕 f) 0 = 0)
    (he : ∀ r, (𝓕 f) (-r) = (𝓕 f) r) (hb : ∀ r, U < |r| → (𝓕 f) r = 0)
    (hrows : ∀ j : ℤ, j ≠ 0 → 𝓕 (dampedStage T f) ((j : ℝ) / Real.log p) = 0)
    (hzero : thetaBoundaryMellin f 0 = 0) :
    ∃ g : 𝓢(ℝ, ℂ), g 0 = 0 ∧ (𝓕 g) 0 = 0 ∧
      (∀ r, U / (p : ℝ) < |r| → (𝓕 g) r = 0) ∧
      ∀ x, stage T f x = stage (insert p T) g x := by
  have hT1 (q : ℕ) (hq : q ∈ T) : 1 ≤ q := (hT q hq).one_lt.le
  have hi := integrable_dampedStage_subsets hU T hT f hf hF0 hb
  obtain ⟨hfac, hz⟩ := thetaBoundaryMellin_factor_and_zero hU f hf hF0 he hb
  apply exists_smaller_box_stage hp.one_lt T hT1 hmem hU f he hF0 hb _ (hz.symm.trans hzero)
  intro j
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hL := Real.log_pos hpR
  let t : ℝ := 2 * Real.pi * (j : ℝ) / Real.log p
  have ha : mellin (⇑(𝓕 f : 𝓢(ℝ, ℂ))) (1 - (t : ℂ) * Complex.I) = 0 := by
    by_cases hj : j = 0
    · simpa [t, hj] using archMass_zero_of_source hf he
    · have ht : t ≠ 0 := by
        dsimp only [t]
        exact div_ne_zero (mul_ne_zero (by positivity) (by exact_mod_cast hj)) hL.ne'
      have hmesh := (fourier_dampedStage_prime_mesh_eq_zero_iff T hp hmem hT f hi (neg_ne_zero.mpr hj)).mp
        (hrows (-j) (neg_ne_zero.mpr hj))
      have hm : thetaBoundaryMellin f ((t : ℂ) * Complex.I) = 0 := by
        rw [show t = -2 * Real.pi * ((↑(-j) : ℝ) / Real.log p) by dsimp [t]; push_cast; ring,
          thetaBoundary_fourier_eq]
        exact hmesh
      rw [(hfac t ht).1] at hm
      exact (mul_eq_zero.mp hm).resolve_left (mul_ne_zero (by norm_num) (hfac t ht).2)
  rw [archMellin_eq_log_fourier hpR hU (𝓕 f) hb (j : ℝ)] at ha
  exact (mul_eq_zero.mp ha).resolve_left (Complex.ofReal_ne_zero.mpr hL.ne')

private theorem tendsto_fourierChar_sub_quotient (a : ℝ) :
    Tendsto (fun x : ℝ ↦ (1 - (Real.fourierChar (a * x) : ℂ)) / (x : ℂ))
      (𝓝[≠] 0) (𝓝 (-(2 * (Real.pi : ℂ) * Complex.I * a))) := by
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * a
  have hx : HasDerivAt (fun x : ℝ ↦ (x : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hd : HasDerivAt (fun x : ℝ ↦ 1 - Complex.exp (c * x)) (-c) 0 := by
    change HasDerivAt ((fun _ : ℝ ↦ (1 : ℂ)) - fun x : ℝ ↦ Complex.exp (c * ↑x)) (-c) 0
    simpa using (hasDerivAt_const (0 : ℝ) (1 : ℂ)).sub ((hx.const_mul c).cexp)
  apply hd.tendsto_slope_zero.congr
  intro x
  simp only [zero_add, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self, sub_zero,
    Complex.real_smul, Complex.ofReal_inv, Real.fourierChar_apply, Complex.ofReal_mul,
    show ((2 : ℝ) : ℂ) = 2 by norm_num, div_eq_mul_inv]
  dsimp only [c]
  ring_nf

/-- The leading coefficient at the origin of the actual earlier-stage Fourier transform. -/
theorem tendsto_fourier_dampedStage_leading (T : Finset ℕ) (f : 𝓢(ℝ, ℂ))
    (hT : ∀ q ∈ T, q.Prime) (hi : ∀ U ⊆ T, Integrable (dampedStage U f)) :
    Tendsto (fun ξ : ℝ ↦ 𝓕 (dampedStage T f) ξ / (ξ : ℂ) ^ T.card) (𝓝[≠] 0)
      (𝓝 ((∏ q ∈ T, -(2 * (Real.pi : ℂ) * Complex.I * Real.log q)) *
        𝓕 (dampedStage ∅ f) 0)) := by
  have hc : Continuous (𝓕 (dampedStage ∅ f)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (hi ∅ (Finset.empty_subset T))
  apply ((tendsto_finsetProd T (fun q _ ↦ tendsto_fourierChar_sub_quotient (Real.log q))).mul
    (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).congr
  intro ξ
  rw [fourier_dampedStage_prod T f ξ (fun q hq ↦ (hT q hq).pos) hi,
    Finset.prod_div_distrib, Finset.prod_const]
  ring

/-- The normalized zero row vanishes exactly when the empty-stage Fourier value vanishes. -/
theorem tendsto_fourier_dampedStage_leading_zero_iff (T : Finset ℕ) (f : 𝓢(ℝ, ℂ))
    (hT : ∀ q ∈ T, q.Prime) (hi : ∀ U ⊆ T, Integrable (dampedStage U f)) :
    Tendsto (fun ξ : ℝ ↦ 𝓕 (dampedStage T f) ξ / (ξ : ℂ) ^ T.card) (𝓝[≠] 0) (𝓝 0) ↔
      𝓕 (dampedStage ∅ f) 0 = 0 := by
  have ht := tendsto_fourier_dampedStage_leading T f hT hi
  have hn : (∏ q ∈ T, -(2 * (Real.pi : ℂ) * Complex.I * Real.log q)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have hl := Real.log_pos (show (1 : ℝ) < q by exact_mod_cast (hT q hq).one_lt)
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr hl.ne'))
  constructor
  · intro hz
    exact (mul_eq_zero.mp (tendsto_nhds_unique ht hz)).resolve_left hn
  · intro hz
    simpa only [hz, mul_zero] using ht

/-- An actual representative at the next stage kills every row of the previous
representative on the new mesh. Away from zero the empty-stage row vanishes too. -/
theorem mesh_rows_of_stage_eq_insert (T : Finset ℕ) {p : ℕ} (hp : p.Prime)
    (hpT : p ∉ T) (hT : ∀ q ∈ T, q.Prime) (f g : 𝓢(ℝ, ℂ))
    (hf : ∀ U ⊆ T, Integrable (dampedStage U f)) (hg : Integrable (dampedStage T g))
    (h : ∀ x, stage T f x = stage (insert p T) g x) (j : ℤ) :
    𝓕 (dampedStage T f) ((j : ℝ) / Real.log p) = 0 ∧
      (j ≠ 0 → 𝓕 (dampedStage ∅ f) ((j : ℝ) / Real.log p) = 0) := by
  have hz := fourier_dampedStage_zero_on_mesh T hp.one_lt hpT g hg j
  rw [← dampedStage_congr h] at hz
  exact ⟨hz, fun hj ↦ (fourier_dampedStage_prime_mesh_eq_zero_iff T hp hpT hT f hf hj).mp hz⟩

private theorem euler_prod_ne_zero_ae (T : Finset ℕ) (hT : ∀ q ∈ T, 1 < q) :
    ∀ᵐ ξ : ℝ, (∏ q ∈ T, (1 - (Real.fourierChar (Real.log q * ξ) : ℂ))) ≠ 0 := by
  let mesh : ℕ × ℤ → ℝ := fun a ↦ (a.2 : ℝ) / Real.log a.1
  filter_upwards [(Set.countable_range mesh).ae_notMem volume] with ξ hξ
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq hz
  have hc : Real.fourierChar (Real.log q * ξ) = 1 := Subtype.ext (sub_eq_zero.mp hz).symm
  rw [Real.fourierChar_apply', Circle.exp_eq_one] at hc
  obtain ⟨k, hk⟩ := hc
  have hx : Real.log q * ξ = k := by
    apply mul_left_cancel₀ (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
    simpa only [mul_comm (k : ℝ)] using hk
  apply hξ
  refine ⟨(q,k), ?_⟩
  change (k : ℝ) / Real.log q = ξ
  exact (div_eq_iff (Real.log_pos (show (1 : ℝ) < q by exact_mod_cast hT q hq)).ne').mpr
    (by simpa only [mul_comm ξ] using hx.symm)

private theorem continuous_damped_fourier {T : Finset ℕ} {f : 𝓢(ℝ, ℂ)}
    (hi : Integrable (dampedStage T f)) : Continuous (𝓕 (dampedStage T f)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi

/-- Cancel the earlier factors off their countable exceptional set and extend
by continuity. This identifies the two actual empty-stage Fourier profiles
at every frequency, including at the common zero of all earlier factors. -/
theorem empty_fourier_of_stage_eq_insert (T : Finset ℕ) {p : ℕ} (hp : 0 < p)
    (hpT : p ∉ T) (hT : ∀ q ∈ T, 1 < q) (f g : 𝓢(ℝ, ℂ))
    (hf : ∀ U ⊆ T, Integrable (dampedStage U f)) (hg : ∀ U ⊆ T, Integrable (dampedStage U g))
    (h : ∀ x, stage T f x = stage (insert p T) g x) :
    𝓕 (dampedStage ∅ f) = fun ξ ↦ (1 - (Real.fourierChar (Real.log p * ξ) : ℂ)) *
      𝓕 (dampedStage ∅ g) ξ := by
  have ht : ∀ q ∈ T, 0 < q := fun q hq ↦ zero_lt_one.trans (hT q hq)
  have hc : Continuous (fun ξ : ℝ ↦ 1 - (Real.fourierChar (Real.log p * ξ) : ℂ)) :=
    continuous_const.sub (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (continuous_const.mul continuous_id)))
  refine Measure.eq_of_ae_eq (μ := volume) ?_ (continuous_damped_fourier (hf ∅ (Finset.empty_subset T)))
    (hc.mul (continuous_damped_fourier (hg ∅ (Finset.empty_subset T))))
  filter_upwards [euler_prod_ne_zero_ae T hT] with ξ hξ
  have hh := congrArg (fun v : ℝ → ℂ ↦ 𝓕 v ξ) (dampedStage_congr h)
  change 𝓕 (dampedStage T f) ξ = 𝓕 (dampedStage (insert p T) g) ξ at hh
  rw [fourier_dampedStage_insert T hp hpT g (hg T (Finset.Subset.refl T)),
    fourier_dampedStage_prod T f ξ ht hf, fourier_dampedStage_prod T g ξ ht hg,
    mul_left_comm (1 - _)] at hh
  exact mul_left_cancel₀ hξ hh

/-- The empty theta zero row, not merely the earlier stage's automatic zero. -/
theorem empty_zero_row_of_stage_eq_insert (T : Finset ℕ) {p : ℕ} (hp : 0 < p)
    (hpT : p ∉ T) (hT : ∀ q ∈ T, 1 < q) (f g : 𝓢(ℝ, ℂ))
    (hf : ∀ U ⊆ T, Integrable (dampedStage U f)) (hg : ∀ U ⊆ T, Integrable (dampedStage U g))
    (h : ∀ x, stage T f x = stage (insert p T) g x) : 𝓕 (dampedStage ∅ f) 0 = 0 := by
  simpa using congrFun (empty_fourier_of_stage_eq_insert T hp hpT hT f g hf hg h) 0

/-- The actual first nonzero normalized row is tested by a punctured
Fourier limit, not the automatic earlier-stage value at frequency zero.
Together with the nonzero fresh-prime samples it is exactly the criterion
for having a polar Schwartz representative in the next smaller box. -/
theorem smaller_box_stage_iff_normalized_theta_rows {p : ℕ} (hp : p.Prime) (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime) (hmem : p ∉ T) {U : ℝ} (hU : 0 < U)
    (f : 𝓢(ℝ, ℂ)) (hf : f 0 = 0) (hF0 : (𝓕 f) 0 = 0)
    (he : ∀ r, (𝓕 f) (-r) = (𝓕 f) r) (hb : ∀ r, U < |r| → (𝓕 f) r = 0) :
    (∃ g : 𝓢(ℝ, ℂ), g 0 = 0 ∧ (𝓕 g) 0 = 0 ∧
      (∀ r, U/(p : ℝ) < |r| → (𝓕 g) r = 0) ∧
      ∀ x, stage T f x = stage (insert p T) g x) ↔
    (∀ j : ℤ, j ≠ 0 → 𝓕 (dampedStage T f) ((j : ℝ) / Real.log p) = 0) ∧
      Tendsto (fun ξ : ℝ ↦ 𝓕 (dampedStage T f) ξ / (ξ : ℂ)^T.card) (𝓝[≠] 0) (𝓝 0) := by
  have hi := integrable_dampedStage_subsets hU T hT f hf hF0 hb
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [tendsto_fourier_dampedStage_leading_zero_iff T f hT hi]
  constructor
  · rintro ⟨g, hg, hgF0, hgb, hfg⟩
    have hj := integrable_dampedStage_subsets (div_pos hU hp0) T hT g hg hgF0 hgb
    exact ⟨fun j _ ↦ (mesh_rows_of_stage_eq_insert T hp hmem hT f g hi (hj T (fun _ hx ↦ hx)) hfg j).1,
      empty_zero_row_of_stage_eq_insert T hp.pos hmem (fun q hq ↦ (hT q hq).one_lt) f g hi hj hfg⟩
  · rintro ⟨hrows, hzero⟩
    apply exists_smaller_box_stage_of_theta_rows hp T hT hmem hU f hf hF0 he hb hrows
    simpa using (thetaBoundary_fourier_eq f 0).trans hzero

end RiemannMasullo.RationalPacket
