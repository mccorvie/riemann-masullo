module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBox
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Exact smaller-box division of a rational Schwartz source

Paper: (11.3.1.3)–(11.3.1.4), p. 494. Once the full mesh of the real
logarithmic Fourier profile vanishes, the bounded inward geometric series
becomes an actual Schwartz profile with band reduced by `p`. At zero the
logarithmic moment, rather than another ordinary value, is the additional
condition which keeps the divided test polar. The theorem starts at these
real profile conditions. The earlier Euler factors are canceled separately
on the nonzero mesh; the passage from empty-stage theta rows to the real
profile and the full cardinal decomposition are not asserted here. -/

public noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped Topology SchwartzMap FourierTransform

namespace RiemannMasullo.RationalPacket

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def logRay (a : ℝ) (g : ℝ → E) (x : ℝ) : E :=
  Real.exp (a * x) • g (Real.exp (a * x))

/-- Each logarithmic derivative still contains one full exponential factor;
its other factor is smooth even at the endpoint `r = 0`. -/
private theorem iteratedDeriv_logRay (a : ℝ) {f : ℝ → E}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (n : ℕ) :
    ∃ g : ℝ → E, ContDiff ℝ (↑(⊤ : ℕ∞)) g ∧ iteratedDeriv n (logRay a f) = logRay a g := by
  induction n with
  | zero => exact ⟨f, hf, iteratedDeriv_zero⟩
  | succ n ih =>
    obtain ⟨g, hg, heq⟩ := ih
    have hgd := (contDiff_infty_iff_deriv.mp hg).2
    refine ⟨fun r => (r * a) • deriv g r + a • g r, by fun_prop, ?_⟩
    rw [iteratedDeriv_succ, heq]
    funext x
    let e := fun t : ℝ => Real.exp (a * t)
    have he : HasDerivAt e (e x * a) x := by
      simpa [e] using (((hasDerivAt_id x).const_mul a).exp)
    have hc := ((contDiff_infty_iff_deriv.mp hg).1 (e x)).hasDerivAt.scomp x he
    change deriv (e • (g ∘ e)) x = e x • ((e x * a) • deriv g (e x) + a • g (e x))
    simpa only [Function.comp_apply, smul_add, smul_smul] using (he.smul hc).deriv

/-- The polynomially weighted Jacobian is bounded on every left half-line. -/
private theorem logRay_weight_bound {a : ℝ} (ha : 0 < a) (T : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≤ T, |x| ^ k * Real.exp (a*x) ≤ C := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) a ha
  obtain ⟨R, hR⟩ := eventually_atTop.1 (ht.eventually_lt_const zero_lt_one)
  let w := fun x : ℝ => |x| ^ k * Real.exp (a*x)
  have hw : Continuous w := by dsimp [w]; fun_prop
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -(max R 0)) (b := T)).exists_bound_of_continuousOn
    hw.continuousOn
  refine ⟨max 1 B, zero_le_one.trans (le_max_left _ _), fun x hx => ?_⟩
  by_cases h : -(max R 0) ≤ x
  · exact (le_abs_self (w x)).trans ((hB x ⟨h, hx⟩).trans (le_max_right _ _))
  · have hx0 : x ≤ 0 := by linarith [le_max_right R (0 : ℝ)]
    have hRx : R ≤ -x := by linarith [le_max_left R (0 : ℝ)]
    have hh := (hR (-x) hRx).le
    simp only [Real.rpow_natCast, neg_mul_neg] at hh
    rw [abs_of_nonpos hx0]
    exact hh.trans (le_max_left _ _)

/-- The actual logarithmic pullback, including the multiplicative Jacobian, is
Schwartz. No lower bound away from zero is needed for the source support. -/
@[expose] def rationalLogSchwartzLift {p X : ℝ} (hp : 1 < p) (hX : 0 < X) (f : 𝓢(ℝ, E))
    (hsupp : ∀ r : ℝ, X < |r| → f r = 0) : 𝓢(ℝ, E) where
  toFun x := Real.exp (Real.log p * x) • f (Real.exp (Real.log p * x))
  smooth' := by fun_prop
  decay' := by
    intro k n
    let a := Real.log p
    have ha : 0 < a := Real.log_pos hp
    let T := Real.log X / a
    obtain ⟨C, hC, hweight⟩ := logRay_weight_bound ha T k
    obtain ⟨g, hg, heq⟩ := iteratedDeriv_logRay a f.smooth' n
    change iteratedDeriv n (logRay a (⇑f)) = logRay a g at heq
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := X)).exists_bound_of_continuousOn
      hg.continuous.continuousOn
    have hB0 : 0 ≤ B := (norm_nonneg (g 0)).trans (hB 0 ⟨le_rfl, hX.le⟩)
    refine ⟨C * B, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    change ‖x‖ ^ k * ‖iteratedDeriv n (logRay a (⇑f)) x‖ ≤ C * B
    by_cases hx : x ≤ T
    · have hax : a*x ≤ Real.log X := by
        simpa [mul_comm] using (le_div_iff₀ ha).1 hx
      have hrX : Real.exp (a*x) ≤ X := by
        simpa [Real.exp_log hX] using Real.exp_le_exp.mpr hax
      rw [heq, logRay, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), ← mul_assoc]
      exact mul_le_mul (hweight x hx) (hB _ ⟨(Real.exp_pos _).le, hrX⟩) (norm_nonneg _) hC
    · have hevt : logRay a (⇑f) =ᶠ[𝓝 x] (fun _ => (0 : E)) := by
        filter_upwards [lt_mem_nhds (lt_of_not_ge hx)] with y hy
        have hay : Real.log X < a*y := by simpa [mul_comm] using (div_lt_iff₀ ha).1 hy
        have hr := (Real.log_lt_iff_lt_exp hX).1 hay
        simp [logRay, hsupp _ (by simpa [abs_of_pos (Real.exp_pos _)] using hr :
          X < |Real.exp (a*y)|)]
      rw [hevt.iteratedDeriv_eq n]
      simpa [iteratedDeriv_const] using mul_nonneg hC hB0

@[simp] theorem rationalLogSchwartzLift_apply {p X : ℝ} (hp : 1 < p) (hX : 0 < X)
    (f : 𝓢(ℝ, E)) (hsupp : ∀ r : ℝ, X < |r| → f r = 0) (x : ℝ) :
    rationalLogSchwartzLift hp hX f hsupp x = Real.exp (Real.log p * x) •
      f (Real.exp (Real.log p * x)) := rfl

namespace OneStep

/-- The inward half of the multiplicative orbit (including the base point). -/
private def term (p : ℝ) (h : ℝ → ℂ) (n : ℕ) (r : ℝ) : ℂ :=
  (p⁻¹ ^ n) • h (r / p ^ n)

private def quotient (p : ℝ) (h : ℝ → ℂ) (r : ℝ) : ℂ := ∑' n : ℕ, term p h n r

variable {p C X : ℝ} {h : ℝ → ℂ}

private theorem majorant (hp : 1 < p) (C : ℝ) : Summable (fun n : ℕ => p⁻¹ ^ n * C) :=
  (summable_geometric_of_lt_one (inv_nonneg.mpr (zero_le_one.trans hp.le))
    (inv_lt_one_of_one_lt₀ hp)).mul_right C

private theorem norm_term_le (hp : 1 < p) (hb : ∀ x, ‖h x‖ ≤ C) (n : ℕ) (r : ℝ) :
    ‖term p h n r‖ ≤ p⁻¹ ^ n * C := by
  have hp' : 0 ≤ p⁻¹ ^ n := pow_nonneg (inv_nonneg.mpr (zero_le_one.trans hp.le)) _
  rw [term, norm_smul, Real.norm_eq_abs, abs_of_nonneg hp']
  exact mul_le_mul_of_nonneg_left (hb _) hp'

private theorem summable_term (hp : 1 < p) (hb : ∀ x, ‖h x‖ ≤ C) (r : ℝ) :
    Summable (fun n => term p h n r) :=
  (majorant hp C).of_norm_bounded fun n => norm_term_le hp hb n r

/-- The same exact inward quotient is smooth to every order for a smooth
profile with uniformly bounded derivatives. -/
private theorem contDiff_quotient (hp : 1 < p) (hs : ContDiff ℝ (↑(⊤ : ℕ∞)) h) (C : ℕ → ℝ)
    (hC : ∀ k x, ‖iteratedFDeriv ℝ k h x‖ ≤ C k) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (quotient p h) := by
  have hp0 := zero_lt_one.trans hp
  have hre (n : ℕ) :
      term p h n = fun x : ℝ ↦ (p⁻¹ ^ n : ℝ) • h ((p⁻¹ ^ n : ℝ) • x) := by
    funext x
    simp [term, div_eq_mul_inv, inv_pow, mul_comm]
  have hcd (n : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ ↦ h ((p⁻¹ ^ n : ℝ) • x)) :=
    hs.comp (contDiff_id.const_smul (p⁻¹ ^ n : ℝ))
  apply contDiff_tsum (N := (⊤ : ℕ∞)) (v := fun k n => p⁻¹ ^ n * C k)
  · intro n
    rw [hre]
    exact (hcd n).const_smul (p⁻¹ ^ n : ℝ)
  · intro k _
    exact majorant hp (C k)
  · intro k n x _
    have hn0 : 0 ≤ p⁻¹ ^ n := pow_nonneg (inv_nonneg.mpr hp0.le) _
    have hn1 : p⁻¹ ^ n ≤ 1 := pow_le_one₀ (inv_nonneg.mpr hp0.le) (inv_lt_one_of_one_lt₀ hp).le
    have hk : (k : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) := WithTop.coe_le_coe.mpr le_top
    rw [hre, iteratedFDeriv_const_smul_apply' ((hcd n).of_le hk).contDiffAt,
      iteratedFDeriv_comp_const_smul _ (hs.of_le hk), norm_smul, norm_smul]
    simp only [Real.norm_eq_abs, abs_of_nonneg hn0, abs_of_nonneg (pow_nonneg hn0 _)]
    apply mul_le_mul_of_nonneg_left _ hn0
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hn0 hn1)).trans (hC k _)

private theorem quotient_zero (h0 : h 0 = 0) : quotient p h 0 = 0 := by
  simp [quotient, term, h0]

private theorem quotient_even (he : ∀ x, h (-x) = h x) (r : ℝ) :
    quotient p h (-r) = quotient p h r := by
  simp only [quotient, term, neg_div, he]

private theorem term_succ (p : ℝ) (h : ℝ → ℂ) (n : ℕ) (r : ℝ) :
    term p h (n + 1) r = p⁻¹ • term p h n (r / p) := by
  simp only [term, pow_succ, smul_smul, div_div, mul_comm p (p ^ n),
    mul_comm p⁻¹ (p⁻¹ ^ n)]

private theorem one_step_division (hp : 1 < p) (hb : ∀ x, ‖h x‖ ≤ C) (r : ℝ) :
    h r = quotient p h r - p⁻¹ • quotient p h (r / p) := by
  apply eq_sub_iff_add_eq.mpr
  unfold quotient
  rw [(summable_term hp hb r).tsum_eq_zero_add, ← (summable_term hp hb (r / p)).tsum_const_smul p⁻¹]
  simp only [term_succ]
  simp [term]

/-- Exact split periodization on the positive ray, after dividing the logarithmic
periodization by r. The outward half omits the base point. `HasSum` explicitly
requires convergence; the inward half converges by `summable_term`. -/
private def VanishingPeriodization (p : ℝ) (h : ℝ → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → HasSum (fun n : ℕ => (p ^ (n + 1)) • h (r * p ^ (n + 1)))
    (-quotient p h r)

private theorem quotient_vanishes_outside (hp : 1 < p) (hX : 0 ≤ X)
    (he : ∀ x, h (-x) = h x) (hs : ∀ r, X < |r| → h r = 0)
    (hv : VanishingPeriodization p h) {r : ℝ} (hr : X / p < |r|) : quotient p h r = 0 := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have ha : 0 < |r| := (div_nonneg hX hp0.le).trans_lt hr
  have hbase : X < |r| * p := (div_lt_iff₀ hp0).mp hr
  have hz (n : ℕ) : h (|r| * p ^ (n + 1)) = 0 := by
    apply hs
    rw [abs_of_nonneg (mul_nonneg ha.le (pow_nonneg hp0.le _)), pow_succ]
    calc X < |r| * p := hbase
         _ ≤ (|r| * p) * p ^ n := le_mul_of_one_le_right (mul_nonneg ha.le hp0.le) (one_le_pow₀ hp.le)
         _ = |r| * (p ^ n * p) := by ring
  have habs : quotient p h |r| = 0 := by
    apply neg_eq_zero.mp
    simpa only [hz, smul_zero, tsum_zero] using (hv |r| ha).tsum_eq.symm
  rcases le_or_gt 0 r with hr0 | hr0
  · simpa [abs_of_nonneg hr0] using habs
  · simpa [abs_of_neg hr0, quotient_even he] using habs

/-- Poisson on the actual logarithmic ray gives exact division once the ordinary
Fourier samples of its scaled smooth profile vanish at every integer. -/
private theorem vanishingPeriodization_of_log_fourier_samples (hp : 1 < p)
    (hb : ∀ x, ‖h x‖ ≤ C) (hbox : ∀ x, X < |x| → h x = 0)
    (f : 𝓢(ℝ, ℂ)) (hf : ∀ x, f x = Real.exp (Real.log p * x) • h (Real.exp (Real.log p * x)))
    (hz : ∀ j : ℤ, (𝓕 f) (j : ℝ) = 0) : VanishingPeriodization p h := by
  intro r hr
  have hp0 := zero_lt_one.trans hp
  let t := Real.log r / Real.log p
  have ht : Real.log p * t = Real.log r := by
    dsimp only [t]
    field_simp [(Real.log_pos hp).ne']
  have hpow (n : ℕ) : Real.exp (Real.log p * (n : ℝ)) = p ^ n := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log hp0]
  let a (n : ℤ) := f (t - (n : ℝ))
  let out (n : ℕ) := (p ^ (n+1)) • h (r * p ^ (n+1))
  have hn : (fun n : ℕ ↦ a n) = fun n : ℕ ↦ r • term p h n r := by
    funext n
    dsimp only [a]
    rw [Int.cast_natCast, hf, mul_sub, ht, Real.exp_sub, Real.exp_log hr, hpow, term, smul_smul,
      div_eq_mul_inv, inv_pow]
  have hneg : (fun n : ℕ ↦ a (-(n+1 : ℤ))) = fun n : ℕ ↦ r • out n := by
    funext n
    dsimp only [a, out]
    rw [Int.cast_neg, sub_neg_eq_add, hf, mul_add, ht, Real.exp_add, Real.exp_log hr, ← Nat.cast_succ,
      Int.cast_natCast, hpow, smul_smul]
  have hout : Summable out := by
    have hlim : Tendsto (fun n : ℕ ↦ r * p ^ (n+1)) atTop atTop := by
      simpa only [Function.comp_apply, mul_comm r] using
        ((tendsto_pow_atTop_atTop_of_one_lt hp).comp (tendsto_add_atTop_nat 1)).atTop_mul_const hr
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (eventually_gt_atTop X))
    apply (summable_nat_add_iff N).1
    refine summable_zero.congr (fun n ↦ ?_)
    have he := hbox (r*p^(n+N+1)) (by rw [abs_of_pos (by positivity)]; exact hN _ (by omega))
    simp [out, he]
  have hA (n : ℤ) : a ((Equiv.neg ℤ) n) = f (t+(n : ℝ)) := by
    simp [a, sub_eq_add_neg]
  have hsum : (∑' n : ℤ, a n) = 0 := by
    rw [← (Equiv.neg ℤ).tsum_eq a, tsum_congr hA, f.tsum_eq_tsum_fourier]
    simp [hz]
  have h1 : Summable (fun n : ℕ ↦ a n) := by
    rw [hn]
    exact (summable_term hp hb r).const_smul r
  have h2 : Summable (fun n : ℕ ↦ a (-(n+1 : ℤ))) := by
    rw [hneg]
    exact hout.const_smul r
  rw [tsum_of_nat_of_neg_add_one h1 h2, hn, hneg, (summable_term hp hb r).tsum_const_smul,
    hout.tsum_const_smul, ← smul_add] at hsum
  have htotal : quotient p h r + ∑' n, out n = 0 := (smul_eq_zero.mp hsum).resolve_left hr.ne'
  have he : (∑' n, out n) = -quotient p h r := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact htotal
  rw [← he]
  exact hout.hasSum

private theorem log_profile_integrable {g : ℝ → ℂ} {C U : ℝ} (hg : Continuous g)
    (hC : ∀ x, ‖g x‖ ≤ C) (hU : 0 ≤ U) (hout : ∀ x, U < |x| → g x = 0) :
    Integrable (fun x : ℝ ↦ (Real.log x : ℂ) * g x) volume := by
  have hl : IntegrableOn Real.log (Icc (-U) U) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1 intervalIntegral.intervalIntegrable_log'
  have hi : IntegrableOn (fun x : ℝ ↦ (Real.log x : ℂ) * g x) (Icc (-U) U) volume := by
    have hm : Measurable (fun x : ℝ ↦ (Real.log x : ℂ) * g x) :=
      (Complex.continuous_ofReal.measurable.comp Real.measurable_log).mul hg.measurable
    apply (hl.norm.const_mul C).mono' hm.aestronglyMeasurable
    filter_upwards with x
    rw [norm_mul, Complex.norm_real, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  apply hi.integrable_of_forall_notMem_eq_zero
  intro x hx
  have hx' : U < |x| := lt_of_not_ge (fun hh ↦ hx (abs_le.mp hh))
  rw [hout x hx', mul_zero]

/-- Polar defect of real Fourier-profile division. The logarithmic moment is
the missing zero-row constraint; vanishing of the mass alone does not encode it. -/
theorem logMoment_of_dilation_difference {k : ℝ → ℂ} (hp : 0 < p)
    (hk : Integrable k volume) (hklog : Integrable (fun r : ℝ ↦ (Real.log r : ℂ) * k r) volume)
    (hhlog : Integrable (fun r : ℝ ↦ (Real.log r : ℂ) * h r) volume)
    (hrec : ∀ r, h r = k r - p⁻¹ • k (r / p)) :
    (∫ r, (Real.log r : ℂ) * h r) = -(Real.log p : ℂ) * ∫ r, k r := by
  have hi : Integrable (fun r : ℝ ↦ (Real.log r : ℂ) * (p⁻¹ • k (r/p))) volume := by
    apply (hklog.sub hhlog).congr
    filter_upwards with r
    simp only [Pi.sub_apply, hrec r, mul_sub, sub_sub_cancel]
  let F (t : ℝ) : ℂ := (Real.log (p*t) : ℂ) * k t
  have hcalc : (fun r : ℝ ↦ (Real.log r : ℂ) * (p⁻¹ • k (r/p))) =
      fun r ↦ p⁻¹ • F (p⁻¹*r) := by
    funext r
    dsimp only [F]
    rw [show p*(p⁻¹*r) = r by field_simp, show p⁻¹ * r = r / p by ring_nf]
    simp only [Complex.real_smul, mul_left_comm]
  have hscale : (∫ r, (Real.log r : ℂ) * (p⁻¹ • k (r/p))) = ∫ t, F t := by
    rw [hcalc, integral_smul, Measure.integral_comp_mul_left]
    rw [inv_inv, abs_of_pos hp, smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
  have hae : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ 0 := by
    rw [ae_iff]
    simp
  have hF : (∫ r, F r) = (Real.log p : ℂ) * (∫ r, k r) + ∫ r, (Real.log r : ℂ) * k r := by
    calc
      _ = ∫ r, ((Real.log p : ℂ) * k r + (Real.log r : ℂ) * k r) := by
        apply integral_congr_ae
        filter_upwards [hae] with r hr
        dsimp only [F]
        rw [Real.log_mul hp.ne' hr, Complex.ofReal_add, add_mul]
      _ = _ := by rw [integral_add (hk.const_mul _) hklog, integral_const_mul]
  simp_rw [hrec, mul_sub]
  rw [integral_sub hklog hi, hscale, hF]
  ring

/-- The exact fixed-box division returns an actual Schwartz source in the
smaller box, preserving both polar conditions when the normalized zero row vanishes. -/
private theorem exists_polar_schwartz_division (p X : ℝ) (hp : 1 < p) (hX : 0 ≤ X)
    (f : 𝓢(ℝ, ℂ)) (he : ∀ x, f (-x) = f x) (hzero : f 0 = 0)
    (hbox : ∀ x, X < |x| → f x = 0) (hper : VanishingPeriodization p f)
    (hmoment : (∫ r : ℝ, (Real.log r : ℂ) * f r) = 0) :
    ∃ g : 𝓢(ℝ, ℂ), g 0 = 0 ∧ (∫ r : ℝ, g r) = 0 ∧ (∀ r, g (-r) = g r) ∧
      (∀ r, X/p < |r| → g r = 0) ∧ ∀ r, f r = g r - p⁻¹ • g (r/p) := by
  let k := quotient p f
  have hkbox : ∀ r, X/p < |r| → k r = 0 :=
    fun _ hr ↦ quotient_vanishes_outside hp hX he hbox hper hr
  have hkcompact : HasCompactSupport k := by
    refine (isCompact_Icc (a := -(X/p)) (b := X/p)).of_isClosed_subset isClosed_closure ?_
    apply closure_minimal _ isClosed_Icc
    intro r hr
    exact abs_le.mp (le_of_not_gt fun h ↦ hr (hkbox r h))
  have hks : ContDiff ℝ (↑(⊤ : ℕ∞)) k := contDiff_quotient hp (f.smooth ⊤)
    (fun j ↦ SchwartzMap.seminorm ℝ 0 j f) (fun j r ↦ f.norm_iteratedFDeriv_le_seminorm ℝ j r)
  let g := hkcompact.toSchwartzMap hks
  have hgbox (r : ℝ) (hr : X/p < |r|) : g r = 0 := hkbox r hr
  have hrec (r : ℝ) : f r = g r - p⁻¹ • g (r/p) :=
    one_step_division hp (f.norm_le_seminorm ℝ) r
  have hi := logMoment_of_dilation_difference (zero_lt_one.trans hp) g.integrable
    (log_profile_integrable g.continuous (g.norm_le_seminorm ℝ) (div_nonneg hX (zero_lt_one.trans hp).le) hgbox)
    (log_profile_integrable f.continuous (f.norm_le_seminorm ℝ) hX hbox) hrec
  rw [hmoment] at hi
  have hpLog : (Real.log p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hp).ne'
  refine ⟨g, quotient_zero hzero, (mul_eq_zero.mp hi.symm).resolve_left (neg_ne_zero.mpr hpLog),
    fun r ↦ quotient_even he r, hgbox, hrec⟩

end OneStep

/-- Exact division returns a genuine real Schwartz lift with both polar values
zero. The log Fourier samples and the normalized logarithmic zero row are
separate inputs; no numerator identity for the earlier prime factors is assumed. -/
theorem exists_polar_source_dilation_difference {p X : ℝ} (hp : 1 < p) (hX : 0 < X)
    (f : 𝓢(ℝ, ℂ)) (he : ∀ r, (𝓕 f) (-r) = (𝓕 f) r) (hzero : (𝓕 f) 0 = 0)
    (hbox : ∀ r, X < |r| → (𝓕 f) r = 0)
    (hrows : ∀ j : ℤ, (𝓕 (rationalLogSchwartzLift hp hX (𝓕 f) hbox)) (j : ℝ) = 0)
    (hzeroRow : (∫ r : ℝ, (Real.log r : ℂ) * (𝓕 f) r) = 0) :
    ∃ g : 𝓢(ℝ, ℂ), g 0 = 0 ∧ (𝓕 g) 0 = 0 ∧
      (∀ r, X/p < |r| → (𝓕 g) r = 0) ∧
      f = g - dilate p (zero_lt_one.trans hp) g := by
  have hper := OneStep.vanishingPeriodization_of_log_fourier_samples hp
    ((𝓕 f).norm_le_seminorm ℝ) hbox _ (rationalLogSchwartzLift_apply hp hX (𝓕 f) hbox) hrows
  obtain ⟨k, hk0, hi, -, hkbox, hrec⟩ :=
    OneStep.exists_polar_schwartz_division p X hp hX.le (𝓕 f) he hzero hbox hper hzeroRow
  let g : 𝓢(ℝ, ℂ) := 𝓕⁻ k
  have hg : 𝓕 g = k := fourier_fourierInv_eq k
  refine ⟨g, ?_, by rw [hg, hk0], ?_, ?_⟩
  · rw [show g = (𝓕⁻ k : 𝓢(ℝ, ℂ)) from rfl, SchwartzMap.fourierInv_coe,
      Real.fourierInv_eq_fourier_neg, neg_zero, Real.fourier_real_eq]
    simpa using hi
  · intro r hr
    rw [hg]
    exact hkbox r hr
  · apply (FourierTransform.fourierCLE ℂ (𝓢(ℝ, ℂ))).injective
    change (𝓕 f : 𝓢(ℝ, ℂ)) = 𝓕 (g - dilate p (zero_lt_one.trans hp) g)
    ext r
    change (𝓕 f) r = SchwartzMap.fourierTransformCLM ℂ (g - dilate p (zero_lt_one.trans hp) g) r
    rw [map_sub, sub_apply]
    change (𝓕 f) r = (𝓕 g) r - (𝓕 (dilate p (zero_lt_one.trans hp) g)) r
    rw [fourier_dilate (zero_lt_one.trans hp), hg]
    exact hrec r

/-- The divided source realizes the next genuine fixed-box rational stage,
not just an equality of orbital Mellin values. -/
theorem exists_smaller_box_stage {p : ℕ} (hp : 1 < p) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 1 ≤ q) (hmem : p ∉ T) {X : ℝ} (hX : 0 < X)
    (f : 𝓢(ℝ, ℂ)) (he : ∀ r, (𝓕 f) (-r) = (𝓕 f) r) (hzero : (𝓕 f) 0 = 0)
    (hbox : ∀ r, X < |r| → (𝓕 f) r = 0)
    (hrows : ∀ j : ℤ, (𝓕 (rationalLogSchwartzLift (p := p) (by exact_mod_cast hp)
      hX (𝓕 f) hbox)) (j : ℝ) = 0)
    (hzeroRow : (∫ r : ℝ, (Real.log r : ℂ) * (𝓕 f) r) = 0) :
    ∃ g : 𝓢(ℝ, ℂ), g 0 = 0 ∧ (𝓕 g) 0 = 0 ∧
      (∀ r, X/(p : ℝ) < |r| → (𝓕 g) r = 0) ∧
      ∀ x, stage T f x = stage (insert p T) g x := by
  obtain ⟨g, hg0, hgF0, hgbox, hfg⟩ := exists_polar_source_dilation_difference
    (by exact_mod_cast hp) hX f he hzero hbox hrows hzeroRow
  refine ⟨g, hg0, hgF0, hgbox, fun x ↦ ?_⟩
  rw [hfg]
  exact stage_difference_dilate T hT (zero_lt_one.trans hp) hmem g hg0 x

/-- Iterating the actual logarithmic translation identity, not a formal Euler product. -/
theorem fourier_dampedStage_prod (T : Finset ℕ) (f : 𝓢(ℝ, ℂ)) (ξ : ℝ)
    (hT : ∀ q ∈ T, 0 < q) (hi : ∀ U ⊆ T, Integrable (dampedStage U f)) :
    𝓕 (dampedStage T f) ξ = (∏ q ∈ T, (1 - (Real.fourierChar (Real.log q * ξ) : ℂ))) *
      𝓕 (dampedStage ∅ f) ξ := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert q T hq ih =>
    have hsub : T ⊆ insert q T := Finset.subset_insert _ _
    rw [fourier_dampedStage_insert T (hT q (Finset.mem_insert_self ..)) hq f (hi T hsub),
      ih (fun r hr => hT r (hsub hr)) (fun U hU => hi U (hU.trans hsub)),
      Finset.prod_insert hq, mul_assoc]

/-- Distinct prime meshes meet only at the origin. Absolute values remove both
integer signs before exponentiation, leaving ordinary natural prime powers. -/
theorem prime_mesh_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {j : ℤ} (hj : j ≠ 0) (k : ℤ) : (j : ℝ) / Real.log p ≠ (k : ℝ) / Real.log q := by
  have lp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have lq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  intro h
  have ha := congrArg abs ((div_eq_div_iff lp.ne' lq.ne').mp h)
  have he : (j.natAbs : ℝ) * Real.log q = (k.natAbs : ℝ) * Real.log p := by
    simpa only [Nat.cast_natAbs, Int.cast_abs, abs_mul, abs_of_pos lp, abs_of_pos lq] using ha
  have hpow : (q : ℝ) ^ j.natAbs = (p : ℝ) ^ k.natAbs := by
    simpa only [Real.exp_nat_mul, Real.exp_log (show (0 : ℝ) < p by exact_mod_cast hp.pos),
      Real.exp_log (show (0 : ℝ) < q by exact_mod_cast hq.pos)] using congrArg Real.exp he
  have hn : q ^ j.natAbs = p ^ k.natAbs := by exact_mod_cast hpow
  have hd : q ∣ p ^ k.natAbs := hn ▸ dvd_pow_self q (by simpa using hj : j.natAbs ≠ 0)
  exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hd)).symm

/-- The earlier Euler factor has no zero at a nonzero mesh point of a fresh prime. -/
theorem prime_mesh_euler_prod_ne_zero (T : Finset ℕ) {p : ℕ} (hp : p.Prime) (hpT : p ∉ T)
    (hT : ∀ q ∈ T, q.Prime) {j : ℤ} (hj : j ≠ 0) :
    (∏ q ∈ T, (1 - (Real.fourierChar (Real.log q * ((j : ℝ) / Real.log p)) : ℂ))) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq hz
  let x := Real.log q * ((j : ℝ) / Real.log p)
  have hc : Real.fourierChar x = 1 := Subtype.ext (sub_eq_zero.mp hz).symm
  rw [Real.fourierChar_apply', Circle.exp_eq_one] at hc
  obtain ⟨k, hk⟩ := hc
  have hx : x = k := by
    apply mul_left_cancel₀ (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
    simpa only [mul_comm (k : ℝ)] using hk
  apply prime_mesh_ne hp (hT q hq) (by rintro rfl; exact hpT hq) hj k
  apply (eq_div_iff (Real.log_pos (show (1 : ℝ) < q by exact_mod_cast (hT q hq).one_lt)).ne').mpr
  simpa only [x, mul_comm (Real.log (q : ℝ))] using hx

/-- At a fresh nonzero mesh point, vanishing of the actual earlier-stage row
is equivalent to vanishing of the empty-stage row. -/
theorem fourier_dampedStage_prime_mesh_eq_zero_iff (T : Finset ℕ) {p : ℕ} (hp : p.Prime)
    (hpT : p ∉ T) (hT : ∀ q ∈ T, q.Prime) (f : 𝓢(ℝ, ℂ))
    (hi : ∀ U ⊆ T, Integrable (dampedStage U f)) {j : ℤ} (hj : j ≠ 0) :
    𝓕 (dampedStage T f) ((j : ℝ) / Real.log p) = 0 ↔
      𝓕 (dampedStage ∅ f) ((j : ℝ) / Real.log p) = 0 := by
  rw [fourier_dampedStage_prod T f _ (fun q hq => (hT q hq).pos) hi,
    mul_eq_zero, or_iff_right (prime_mesh_euler_prod_ne_zero T hp hpT hT hj)]

end RiemannMasullo.RationalPacket
