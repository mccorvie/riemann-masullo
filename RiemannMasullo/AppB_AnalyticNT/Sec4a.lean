module

public import Mathlib.Analysis.Complex.IntegerCompl
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import RiemannMasullo.AppB_AnalyticNT.Sec2
public import RiemannMasullo.Ch03_IdelicZeta.Sec2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import RiemannMasullo.ForMathlib.Analysis.Fourier.PoissonSummation
import RiemannMasullo.ForMathlib.Analysis.MellinTransform
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Complements on Poisson summation and Cauchy integrals

Masullo, §B.4.1, pp. 606–614. As in §B.2, a test function on the positive
reals is represented by its profile in the coordinate `x = log t`.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain NumberField Set
open scoped BigOperators ContDiff SchwartzMap Topology

namespace RiemannMasullo

local notation "logMellin" =>
  (fun (f : ℝ → ℂ) ↦ mellin (fun t ↦ f (Real.log t)))
local notation "twoPiI" => (2 * (Real.pi : ℂ) * Complex.I)

/-- Paper: Lemma B.4.1.1(1)–(2), p. 607. The logarithmic profile is smooth
off a finite set and all its derivatives have finite one-sided limits there.
The profile and its first derivative decay faster than every exponential on
both tails, as in (B.4.1.1). -/
def IsPiecewiseSmoothMellinTest (f : ℝ → ℂ) : Prop :=
  (∃ S : Finset ℝ, ContDiffOn ℝ ∞ f (S : Set ℝ)ᶜ ∧
    ∀ (j : ℕ) (x : ℝ), x ∈ S →
      (∃ l : ℂ, Tendsto (iteratedDeriv j f) (𝓝[<] x) (𝓝 l)) ∧
      (∃ r : ℂ, Tendsto (iteratedDeriv j f) (𝓝[>] x) (𝓝 r))) ∧
  ∀ N : ℕ, ∃ C > (0 : ℝ), ∃ T > (0 : ℝ), ∀ x : ℝ, T < |x| →
    ‖f x‖ < C * Real.exp (-(N : ℝ) * |x|) ∧
    ‖deriv f x‖ < C * Real.exp (-(N : ℝ) * |x|)

/-- Paper: Lemma B.4.1.1, p. 607. The indicator of the interval from one to
two satisfies the jump and decay hypotheses in logarithmic coordinates.
Deviation: Sanity check, using the test function from Remark B.4.1.4. -/
theorem isPiecewiseSmoothMellinTest_indicator :
    IsPiecewiseSmoothMellinTest ((Icc 0 (Real.log 2)).indicator (fun _ ↦ (1 : ℂ))) := by
  let f := (Icc 0 (Real.log 2)).indicator (fun _ ↦ (1 : ℂ))
  change IsPiecewiseSmoothMellinTest f
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hzero : EqOn f (fun _ ↦ 0) (Icc 0 (Real.log 2))ᶜ :=
    fun _ hx ↦ indicator_of_notMem hx _
  have hone : EqOn f (fun _ ↦ 1) (Ioo 0 (Real.log 2)) :=
    fun _ hx ↦ indicator_of_mem (mem_Icc_of_Ioo hx) _
  have hlimit (j : ℕ) {s : Set ℝ} {L : Filter ℝ} {c : ℂ} (hs : IsOpen s)
      (heq : EqOn f (fun _ ↦ c) s) (hmem : s ∈ L) :
      ∃ l, Tendsto (iteratedDeriv j f) L (𝓝 l) := by
    refine ⟨if j = 0 then c else 0, EventuallyEq.tendsto ?_⟩
    filter_upwards [hmem] with x hx
    rw [(eventuallyEq_of_mem (hs.mem_nhds hx) heq).iteratedDeriv_eq j, iteratedDeriv_const]
  constructor
  · refine ⟨{0, Real.log 2}, ?_, ?_⟩
    · intro x hx
      have hends : x ≠ 0 ∧ x ≠ Real.log 2 := by simpa using hx
      apply ContDiffAt.contDiffWithinAt
      by_cases hxI : x ∈ Icc 0 (Real.log 2)
      · have hx' : x ∈ Ioo 0 (Real.log 2) :=
          ⟨lt_of_le_of_ne hxI.1 hends.1.symm, lt_of_le_of_ne hxI.2 hends.2⟩
        exact contDiffAt_const.congr_of_eventuallyEq
          (eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx') hone)
      · exact contDiffAt_const.congr_of_eventuallyEq
          (eventuallyEq_of_mem (isClosed_Icc.isOpen_compl.mem_nhds hxI) hzero)
    · intro j x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨hlimit j isOpen_Iio (hzero.mono fun _ hy ↦ fun h ↦ hy.not_ge h.1)
          self_mem_nhdsWithin, hlimit j isOpen_Ioo hone (Ioo_mem_nhdsGT hlog)⟩
      · exact ⟨hlimit j isOpen_Ioo hone (Ioo_mem_nhdsLT hlog),
          hlimit j isOpen_Ioi (hzero.mono fun _ hy ↦ fun h ↦ hy.not_ge h.2)
            self_mem_nhdsWithin⟩
  · intro N
    refine ⟨1, one_pos, Real.log 2, hlog, ?_⟩
    intro x hx
    have hxI : x ∈ (Icc 0 (Real.log 2))ᶜ :=
      fun h ↦ hx.not_ge (by simpa only [abs_of_nonneg h.1] using h.2)
    have heq := eventuallyEq_of_mem (isClosed_Icc.isOpen_compl.mem_nhds hxI) hzero
    rw [heq.self_of_nhds, heq.deriv_eq]
    simpa only [deriv_const, norm_zero, one_mul] using
      And.intro (Real.exp_pos (-(N : ℝ) * |x|)) (Real.exp_pos (-(N : ℝ) * |x|))

open MeasureTheory in
/-- Paper: Lemma B.4.1.1, p. 607. The Mellin integral (B.4.1.2) of a test
function with finitely many jumps converges absolutely for every exponent. -/
theorem mellinConvergent_of_piecewiseSmoothMellinTest
    {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) (s : ℂ) :
    MellinConvergent (fun t ↦ f (Real.log t)) s := by
  obtain ⟨⟨S, hsmooth, hlimits⟩, hdecay⟩ := hf
  apply mellinConvergent_of_integrable_logWeight
  let w (x : ℝ) : ℂ := Real.exp (s.re * x)
  let g (x : ℝ) := w x * f x
  change Integrable g
  have hw : Continuous w := by
    dsimp [w]
    fun_prop
  have hcont : ContinuousOn g (S : Set ℝ)ᶜ :=
    hw.continuousOn.mul hsmooth.continuousOn
  have hmeas : Measurable g :=
    measurable_of_measurable_on_compl_finite _ S.finite_toSet
      (continuousOn_iff_continuous_domRestrict.mp hcont).measurable
  -- The weighted profile is locally integrable even at the jumps.
  have hloc : LocallyIntegrable g := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨⟨l, hl⟩, ⟨r, hr⟩⟩ := hlimits 0 x hx
      simp only [iteratedDeriv_zero] at hl hr
      rw [← nhdsNE_sup_pure x, ← nhdsLT_sup_nhdsGT x, IntegrableAtFilter.sup_iff,
        IntegrableAtFilter.sup_iff]
      have hside {u : Set ℝ} {a : ℂ} (hu : MeasurableSet u)
          (ha : Tendsto f (𝓝[u] x) (𝓝 a)) : IntegrableAtFilter g (𝓝[u] x) volume := by
        have := hu.nhdsWithin_isMeasurablyGenerated x
        exact ((hw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul ha).integrableAtFilter
          hmeas.aestronglyMeasurable.stronglyMeasurableAtFilter (volume.finiteAt_nhdsWithin x u)
      exact ⟨⟨hside measurableSet_Iio hl, hside measurableSet_Ioi hr⟩,
        ⟨{x}, by simp, integrableOn_singleton (hx := measure_singleton_lt_top)⟩⟩
    · have hx' : (S : Set ℝ)ᶜ ∈ 𝓝 x :=
        S.finite_toSet.isClosed.isOpen_compl.mem_nhds hx
      exact ((hcont x hx).continuousAt hx').integrableAtFilter
        hmeas.aestronglyMeasurable.stronglyMeasurableAtFilter (volume.finiteAt_nhds x)
  -- Dominate both tails by a constant times exp (-|x|).
  obtain ⟨N, hN⟩ := exists_nat_gt (|s.re| + 1)
  obtain ⟨C, hC, T, hT, htail⟩ := hdecay N
  have hbound (x : ℝ) (hx : T < |x|) : ‖g x‖ ≤ C * Real.exp (-|x|) := by
    have hprod : s.re * x ≤ |s.re| * |x| := by
      rw [← abs_mul]
      exact le_abs_self _
    have hrate : (|s.re| + 1) * |x| ≤ (N : ℝ) * |x| :=
      mul_le_mul_of_nonneg_right hN.le (abs_nonneg x)
    rw [show ‖g x‖ = Real.exp (s.re * x) * ‖f x‖ by
      simp only [g, w, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]]
    calc
      _ ≤ Real.exp (s.re * x) * (C * Real.exp (-(N : ℝ) * |x|)) :=
        mul_le_mul_of_nonneg_left (htail x hx).1.le (Real.exp_pos _).le
      _ = C * Real.exp (s.re * x + -(N : ℝ) * |x|) := by rw [Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hprod, hrate])) hC.le
  refine integrable_iff_integrableAtFilter_atBot_atTop.mpr ⟨⟨?_, ?_⟩, hloc⟩
  · refine ⟨Iio (-T), Iio_mem_atBot _, ?_⟩
    refine (((integrableOn_exp_Iic (-T)).mono_set Iio_subset_Iic_self).const_mul C).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    have hx' : x < -T := hx
    have hneg : x < 0 := hx'.trans (neg_neg_of_pos hT)
    have hTx : T < -x := by linarith only [hx']
    simpa only [abs_of_neg hneg, neg_neg] using
      hbound x (by rwa [abs_of_neg hneg])
  · refine ⟨Ioi T, Ioi_mem_atTop _, ?_⟩
    refine ((integrableOn_exp_neg_Ioi T).const_mul C).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hpos : 0 < x := hT.trans hx
    simpa [abs_of_pos hpos] using hbound x (by simpa [abs_of_pos hpos] using hx)

open MeasureTheory in
open scoped Asymptotics in
/-- Paper: Lemma B.4.1.1, p. 607. The Mellin transform of a test function
with finitely many jumps is entire. -/
theorem differentiable_mellin_of_piecewiseSmoothMellinTest
    {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) :
    Differentiable ℂ (logMellin f) := by
  obtain ⟨⟨S, hsmooth, hlimits⟩, hdecay⟩ := hf
  have hcont := hsmooth.continuousOn
  have hmeas : Measurable f :=
    hcont.measurable_of_countable_compl (by simpa using S.finite_toSet.countable)
  have hbounded (x : ℝ) : (𝓝 x).IsBoundedUnder (· ≤ ·) (fun y ↦ ‖f y‖) := by
    by_cases hx : x ∈ S
    · obtain ⟨⟨l, hl⟩, ⟨r, hr⟩⟩ := hlimits 0 x hx
      simp only [iteratedDeriv_zero] at hl hr
      rw [← nhdsNE_sup_pure x, ← nhdsLT_sup_nhdsGT x, IsBoundedUnder, Filter.map_sup, Filter.map_sup]
      exact isBounded_sup (isBounded_sup hl.norm.isBoundedUnder_le hr.norm.isBoundedUnder_le)
        ⟨‖f x‖, by simp⟩
    · have hfx := (hcont x hx).continuousAt (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hx)
      exact hfx.tendsto.norm.isBoundedUnder_le
  have hloc : LocallyIntegrableOn (fun t ↦ f (Real.log t)) (Ioi 0) := by
    intro t ht
    have ht' : 0 < t := ht
    have hlog := (Real.continuousAt_log ht'.ne').tendsto
    exact ((volume.finiteAt_nhds t).integrableAtFilter
      (hmeas.comp Real.measurable_log).aestronglyMeasurable.stronglyMeasurableAtFilter
      (hlog.isBoundedUnder_comp (hbounded (Real.log t)))).filter_mono nhdsWithin_le_nhds
  intro s
  obtain ⟨N, hN⟩ := exists_nat_gt |s.re|
  obtain ⟨C, _, T, hT, hbound⟩ := hdecay N
  have htop : f =O[atTop] (fun x ↦ Real.exp (-(N : ℝ) * x)) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [eventually_gt_atTop T] with x hx
    have hx' := hT.trans hx
    simpa only [abs_of_pos hx', Real.norm_of_nonneg (Real.exp_pos _).le]
      using (hbound x (by simpa only [abs_of_pos hx'] using hx)).1.le
  have hbot : f =O[atBot] (fun x ↦ Real.exp ((N : ℝ) * x)) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [eventually_lt_atBot (-T)] with x hx
    have hx' : x < 0 := hx.trans (neg_lt_zero.mpr hT)
    have hTx : T < |x| := by rw [abs_of_neg hx']; linarith
    simpa only [abs_of_neg hx', neg_mul_neg, Real.norm_of_nonneg (Real.exp_pos _).le]
      using (hbound x hTx).1.le
  exact mellin_differentiableAt_of_isBigO_rpow hloc
    (isBigO_comp_log_rpow_of_isBigO_exp htop Real.tendsto_log_atTop (eventually_gt_atTop 0))
    ((le_abs_self _).trans_lt hN)
    (isBigO_comp_log_rpow_of_isBigO_exp (by simpa only [neg_neg] using hbot)
      Real.tendsto_log_nhdsGT_zero self_mem_nhdsWithin)
    (neg_lt.mp ((neg_le_abs _).trans_lt hN))

-- TODO(paper-gap): (B.4.1.4)–(B.4.1.5) have the wrong sign for the jump
-- defined as the right limit minus the left limit at one.

open MeasureTheory in
/-- Paper: Lemma B.4.1.1, p. 607. The Mellin transform satisfies the bound
(B.4.1.3) of order one over the modulus, uniformly on each bounded-width strip. -/
theorem mellin_inverseNormBound_of_piecewiseSmoothMellinTest
    {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) (a b : ℝ) :
    ∃ C > (0 : ℝ), ∃ R > (0 : ℝ), ∀ s : ℂ, s.re ∈ Icc a b → R < ‖s‖ →
      ‖logMellin f s‖ ≤ C / ‖s‖ := by
  classical
  obtain ⟨⟨S, hsmooth, hlimits⟩, hdecay⟩ := hf
  have hopen : IsOpen (S : Set ℝ)ᶜ := S.finite_toSet.isClosed.isOpen_compl
  have hcont := hsmooth.continuousOn
  have hcont' := hsmooth.continuousOn_deriv_of_isOpen hopen (by simp)
  have hlim₀ x (hx : x ∈ S) :
      (∃ l, Tendsto f (𝓝[<] x) (𝓝 l)) ∧ (∃ r, Tendsto f (𝓝[>] x) (𝓝 r)) := by
    simpa only [iteratedDeriv_zero] using hlimits 0 x hx
  have hlim₁ x (hx : x ∈ S) :
      (∃ l, Tendsto (deriv f) (𝓝[<] x) (𝓝 l)) ∧
        (∃ r, Tendsto (deriv f) (𝓝[>] x) (𝓝 r)) := by
    simpa only [iteratedDeriv_one] using hlimits 1 x hx
  let M := max |a| |b|
  have hM : 0 ≤ M := (abs_nonneg a).trans (le_max_left _ _)
  obtain ⟨N, hN⟩ := exists_nat_gt (M + 1)
  obtain ⟨C, hC, T, _, htail⟩ := hdecay N
  -- One-sided limits bound both profiles on the compact interval between the tails.
  have hcompact {g : ℝ → ℂ} (hg : ContinuousOn g (S : Set ℝ)ᶜ)
      (hlim : ∀ x ∈ S, (∃ l, Tendsto g (𝓝[<] x) (𝓝 l)) ∧
        (∃ r, Tendsto g (𝓝[>] x) (𝓝 r))) :
      ∃ B : ℝ, ∀ x ∈ Icc (-T) T, ‖g x‖ ≤ B := by
    have hloc (x : ℝ) : (𝓝 x).IsBoundedUnder (· ≤ ·) (fun y ↦ ‖g y‖) := by
      by_cases hx : x ∈ S
      · obtain ⟨⟨l, hl⟩, ⟨r, hr⟩⟩ := hlim x hx
        rw [← nhdsNE_sup_pure x, ← nhdsLT_sup_nhdsGT x, IsBoundedUnder, map_sup, map_sup]
        exact isBounded_sup (isBounded_sup hl.norm.isBoundedUnder_le hr.norm.isBoundedUnder_le)
          ⟨‖g x‖, by simp⟩
      · exact ((hg x hx).continuousAt (hopen.mem_nhds hx)).tendsto.norm.isBoundedUnder_le
    have hbounded : Bornology.IsBounded (g '' Icc (-T) T) := by
      apply Bornology.isBounded_image_of_isLocallyBounded_of_isCompact isCompact_Icc
      intro x
      obtain ⟨B, hB⟩ := hloc x
      exact ⟨{y | ‖g y‖ ≤ B}, eventually_map.mp hB,
        isBounded_iff_forall_norm_le.mpr ⟨B, forall_mem_image.mpr fun _ hy ↦ hy⟩⟩
    obtain ⟨B, hB⟩ := hbounded.exists_norm_le
    exact ⟨B, fun x hx ↦ hB _ (mem_image_of_mem g hx)⟩
  obtain ⟨U, hU⟩ := hcompact hcont hlim₀
  obtain ⟨V, hV⟩ := hcompact hcont' hlim₁
  let A := C + (|U| + |V|) * Real.exp ((M + 1) * T)
  have hCA : C ≤ A :=
    le_add_of_nonneg_right (mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (Real.exp_pos _).le)
  have hA := hC.trans_le hCA
  have hdecay' (x y : ℝ) (hy₀ : x ∈ Icc (-T) T → y ≤ |U| + |V|)
      (hy₁ : T < |x| → y ≤ C * Real.exp (-(N : ℝ) * |x|)) :
      y ≤ A * Real.exp (-(M + 1) * |x|) := by
    by_cases hx : T < |x|
    · exact (hy₁ hx).trans (mul_le_mul hCA
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hN.le) (abs_nonneg x)))
        (Real.exp_pos _).le hA.le)
    · have hx' := le_of_not_gt hx
      -- Multiply by the reciprocal of the desired exponential factor.
      rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
      calc
        _ ≤ (|U| + |V|) * Real.exp ((M + 1) * T) :=
          mul_le_mul (hy₀ (abs_le.mp hx'))
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx' (by positivity)))
            (Real.exp_pos _).le (by positivity)
        _ ≤ A := le_add_of_nonneg_left hC.le
  -- This majorant absorbs every exponential weight in the strip.
  let B (x : ℝ) := A * Real.exp (-|x|)
  have hB : Integrable B := by
    apply Integrable.const_mul (f := fun x : ℝ ↦ Real.exp (-|x|)) _ A
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    exact ⟨(integrableOn_exp_Iic 0).congr_fun
      (fun x hx ↦ by rw [abs_of_nonpos hx, neg_neg]) measurableSet_Iic,
      (integrableOn_exp_neg_Ioi 0).congr_fun
        (fun x hx ↦ by rw [abs_of_pos hx]) measurableSet_Ioi⟩
  let K : ℝ := (∫ x, B x) + (S.card : ℝ) * (A + A)
  have hK : 0 ≤ K := add_nonneg (integral_nonneg (fun _ ↦ by positivity)) (by positivity)
  refine ⟨K + 1, by positivity, 1, one_pos, fun s hs hsnorm ↦ ?_⟩
  apply (le_div_iff₀ (zero_lt_one.trans hsnorm)).mpr
  let w (x : ℝ) := Complex.exp (s * x)
  let F (x : ℝ) := w x * f x
  let G (x : ℝ) := w x * deriv f x
  have hw : Continuous w := by
    dsimp [w]
    fun_prop
  have hweight (x : ℝ) : ‖w x‖ ≤ Real.exp (M * |x|) := by
    have hsM : |s.re| ≤ M := abs_le.mpr
      ⟨(neg_le_neg (le_max_left |a| |b|)).trans ((neg_abs_le a).trans hs.1),
        hs.2.trans ((le_abs_self b).trans (le_max_right |a| |b|))⟩
    simp only [w, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    exact Real.exp_le_exp.mpr ((le_abs_self (s.re * x)).trans
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hsM (abs_nonneg x)))
  have hweighted (x : ℝ) {z : ℂ} (hz : ‖z‖ ≤ A * Real.exp (-(M + 1) * |x|)) :
      ‖w x * z‖ ≤ B x := by
    rw [norm_mul]
    calc
      _ ≤ Real.exp (M * |x|) * (A * Real.exp (-(M + 1) * |x|)) :=
        mul_le_mul (hweight x) hz (norm_nonneg _) (Real.exp_pos _).le
      _ = B x := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
  have hFbound x : ‖F x‖ ≤ B x := hweighted x (hdecay' x _
    (fun hx ↦ (hU x hx).trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))))
    (fun hx ↦ (htail x hx).1.le))
  have hGbound x : ‖G x‖ ≤ B x := hweighted x (hdecay' x _
    (fun hx ↦ (hV x hx).trans ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))))
    (fun hx ↦ (htail x hx).2.le))
  have hint {g : ℝ → ℂ} (hg : ContinuousOn g (S : Set ℝ)ᶜ) (hbound : ∀ x, ‖g x‖ ≤ B x) :
      Integrable g :=
    hB.mono' (hg.measurable_of_countable_compl (by simpa using S.finite_toSet.countable)
      |>.aestronglyMeasurable) (Eventually.of_forall hbound)
  have hF : Integrable F := hint (hw.continuousOn.mul hcont) hFbound
  have hG : Integrable G := hint (hw.continuousOn.mul hcont') hGbound
  have hFtop : Tendsto F atTop (𝓝 0) := squeeze_zero_norm hFbound <| by
    apply (by simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul A :
      Tendsto (fun x : ℝ ↦ A * Real.exp (-x)) atTop (𝓝 0)).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp [B, abs_of_nonneg hx]
  have hFbot : Tendsto F atBot (𝓝 0) := squeeze_zero_norm hFbound <| by
    apply (by simpa using Real.tendsto_exp_atBot.const_mul A :
      Tendsto (fun x : ℝ ↦ A * Real.exp x) atBot (𝓝 0)).congr'
    filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
    simp [B, abs_of_nonpos hx]
  let l (x : ℝ) := limUnder (𝓝[<] x) f
  let r (x : ℝ) := limUnder (𝓝[>] x) f
  have hl x (hx : x ∈ S) : Tendsto F (𝓝[<] x) (𝓝 (w x * l x)) := by
    obtain ⟨v, hv⟩ := (hlim₀ x hx).1
    simpa only [l, hv.limUnder_eq] using (hw.continuousAt.continuousWithinAt.tendsto.mul hv)
  have hr x (hx : x ∈ S) : Tendsto F (𝓝[>] x) (𝓝 (w x * r x)) := by
    obtain ⟨v, hv⟩ := (hlim₀ x hx).2
    simpa only [r, hv.limUnder_eq] using (hw.continuousAt.continuousWithinAt.tendsto.mul hv)
  have hderiv x (hx : x ∉ S) : HasDerivAt F (s * F x + G x) x := by
    have hw' : HasDerivAt w (w x * s) x := by
      simpa [w, mul_comm] using
        ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul s).cexp
    have hf' := ((hsmooth x hx).contDiffAt (hopen.mem_nhds hx)).differentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0)
    convert hw'.mul hf'.hasDerivAt using 1
    dsimp [F, G]
    ring
  have heq := integral_deriv_eq_sub_add_sum_jumps S ((hF.const_mul s).add hG)
    hderiv hl hr hFbot hFtop
  change (∫ x, s * F x + G x) = (0 : ℂ) - 0 + _ at heq
  rw [sub_self, zero_add, integral_add (hF.const_mul s) hG, integral_const_mul] at heq
  have htransform : logMellin f s = ∫ x, F x := by
    change mellin (fun t ↦ f (Real.log t)) s = _
    rw [mellin, ← integral_comp_exp]
    apply integral_congr_ae
    filter_upwards with x
    simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
    simp only [F, w, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hFle (x : ℝ) : ‖F x‖ ≤ A := (hFbound x).trans
    (mul_le_of_le_one_right hA.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg x))))
  have hjump : ‖∑ x ∈ S, (w x * l x - w x * r x)‖ ≤ (S.card : ℝ) * (A + A) := by
    calc
      _ ≤ ∑ x ∈ S, ‖w x * l x - w x * r x‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ S, (A + A) := Finset.sum_le_sum fun x hx ↦
        (norm_sub_le _ _).trans (add_le_add
          (le_of_tendsto (hl x hx).norm (Eventually.of_forall hFle))
          (le_of_tendsto (hr x hx).norm (Eventually.of_forall hFle)))
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  rw [htransform, mul_comm, ← norm_mul, eq_sub_of_add_eq heq]
  exact ((norm_sub_le _ _).trans (add_le_add hjump
    (norm_integral_le_of_norm_le hB (Eventually.of_forall hGbound)))).trans (by
      dsimp [K]
      linarith)

/-- Paper: Proposition B.4.1.2, p. 608. At a point with both one-sided limits,
the sample used for Poisson summation is their arithmetic mean. -/
def mellinJumpMidpoint (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (limUnder (𝓝[<] x) f + limUnder (𝓝[>] x) f) / 2

/-- Paper: Proposition B.4.1.2, p. 608. When the two one-sided limits are
given, the midpoint sample is their average.
Deviation: Sanity check for the normalization of the midpoint. -/
theorem mellinJumpMidpoint_eq_average {f : ℝ → ℂ} {x : ℝ} {l r : ℂ}
    (hl : Tendsto f (𝓝[<] x) (𝓝 l)) (hr : Tendsto f (𝓝[>] x) (𝓝 r)) :
    mellinJumpMidpoint f x = (l + r) / 2 := by
  rw [mellinJumpMidpoint, hl.limUnder_eq, hr.limUnder_eq]

/-- Paper: Proposition B.4.1.2, p. 608. The unitary character's weighted
midpoint samples on the multiplicative lattice are absolutely summable.
The value `c` on the generator determines the character. -/
theorem summable_mellinJumpMidpoint_lattice
    {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ ≠ 1) (c : Circle) :
    Summable (fun m : ℤ ↦ (c : ℂ) ^ m * mellinJumpMidpoint f ((m : ℝ) * Real.log θ)) := by
  obtain ⟨⟨S, hsmooth, _⟩, hdecay⟩ := hf
  obtain ⟨C, _, T, _, htail⟩ := hdecay 1
  have hlog := Real.log_ne_zero_of_pos_of_ne_one hθ hθ₁
  have hgeom : Summable (fun n : ℕ ↦ Real.exp ((n : ℝ) * -|Real.log θ|)) :=
    Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr (abs_pos.mpr hlog))
  have hsum : Summable (fun m : ℤ ↦ Real.exp (|(m : ℝ)| * -|Real.log θ|)) := by
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor <;> simpa [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using hgeom
  apply (hsum.mul_left C).of_norm_bounded_eventually
  have hlattice : Tendsto (fun m : ℤ ↦ (m : ℝ) * Real.log θ) cofinite (cocompact ℝ) := by
    have h : Tendsto (fun m : ℤ ↦ zmultiplesHom ℝ (Real.log θ) m) cofinite (cocompact ℝ) :=
      Int.tendsto_zmultiplesHom_cofinite hlog
    simpa only [zmultiplesHom_apply, zsmul_eq_mul] using h
  have habs : Tendsto (fun m : ℤ ↦ |(m : ℝ) * Real.log θ|) cofinite atTop := by
    simpa only [Function.comp_def, Real.norm_eq_abs] using
      tendsto_norm_cocompact_atTop.comp hlattice
  filter_upwards [hlattice.eventually S.finite_toSet.isCompact.compl_mem_cocompact,
    habs.eventually_gt_atTop T] with m hmS hmT
  have hcont := hsmooth.continuousOn.continuousAt
    (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hmS)
  rw [mellinJumpMidpoint_eq_average (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    (hcont.tendsto.mono_left nhdsWithin_le_nhds), add_self_div_two,
    Complex.norm_mul, Complex.norm_zpow, Circle.norm_coe, one_zpow, one_mul]
  simpa only [Nat.cast_one, neg_one_mul, abs_mul, mul_neg] using
    (htail ((m : ℝ) * Real.log θ) hmT).1.le

-- TODO(paper-gap): (B.4.1.7) has the wrong sign for 0 < θ < 1.
-- With θ = 1/2, the trivial character and the indicator of [1, 2],
-- its two sides are -log 2 and log 2.
-- TODO(paper-gap): The exponent ix called log χ(θ) on p. 607 must be
-- multiplied by log θ to give the complex logarithm in (B.4.1.7).
-- TODO(paper-gap): (B.4.1.15) drops the character twist at the translated point,
-- and (B.4.1.17) omits the midpoint contributions from |m| ≤ N₀.

/-- Paper: Proposition B.4.1.2, p. 608. The symmetric frequency sums converge
to the weighted midpoint sum times the logarithmic lattice spacing. The limit
is the same for every complex logarithm of the character value on the generator.
Deviation: Uses `|log θ|` in (B.4.1.7) and takes the ordinary complex logarithm
of `χ(θ)` in its numerator. -/
theorem tendsto_mellinPoissonSum_of_piecewiseSmooth
    {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ ≠ 1) (c : Circle) (ℓ : ℂ) (hℓ : Complex.exp ℓ = (c : ℂ)) :
    Tendsto (fun N : ℕ ↦
      ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        logMellin f ((ℓ + twoPiI * (m : ℂ)) / (Real.log θ : ℂ))) atTop
      (𝓝 (((|Real.log θ| : ℝ) : ℂ) *
        ∑' m : ℤ, (c : ℂ) ^ m * mellinJumpMidpoint f ((m : ℝ) * Real.log θ))) := by sorry

/-- Paper: Remark B.4.1.3, p. 608. The midpoint agrees with the original
sample at all but finitely many integer powers of the lattice generator. -/
theorem finite_mellinJumpMidpoint_ne_lattice
    {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ ≠ 1) :
    {m : ℤ | mellinJumpMidpoint f ((m : ℝ) * Real.log θ) ≠ f ((m : ℝ) * Real.log θ)}.Finite := by
  obtain ⟨⟨S, hS, -⟩, -⟩ := hf
  have hlog : Real.log θ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hθ hθ₁
  have hinj : Function.Injective (fun m : ℤ ↦ (m : ℝ) * Real.log θ) := fun m n h ↦ by
    simpa [hlog] using h
  refine ((S.finite_toSet.preimage hinj.injOn)).subset fun m hm ↦ ?_
  by_contra hmS
  apply hm
  have hopen : IsOpen ((S : Set ℝ)ᶜ) := S.finite_toSet.isClosed.isOpen_compl
  have hcont : ContinuousAt f ((m : ℝ) * Real.log θ) :=
    (hS.continuousOn.continuousAt (hopen.mem_nhds hmS))
  rw [mellinJumpMidpoint_eq_average (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    (hcont.tendsto.mono_left nhdsWithin_le_nhds), add_self_div_two]

-- TODO(paper-gap): Footnote 12 asks for a non-absolutely convergent example.
-- The example at θ = 2 has only one nonzero frequency sample.

open MeasureTheory in
open scoped Asymptotics FourierTransform in
/-- Paper: Remark B.4.1.4, p. 608. If the test function is globally smooth,
the Mellin samples in the Poisson identity are absolutely summable. -/
theorem summable_mellinPoissonSamples_of_smooth
    {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) (hsmooth : ContDiff ℝ ∞ f)
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ ≠ 1) (c : Circle) (ℓ : ℂ)
    (hℓ : Complex.exp ℓ = (c : ℂ)) :
    Summable (fun m : ℤ ↦
      ‖logMellin f ((ℓ + twoPiI * (m : ℂ)) / (Real.log θ : ℂ))‖) := by
  let a := Real.log θ
  have ha : a ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hθ hθ₁
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  let w (x : ℝ) := Complex.exp (ℓ * (x : ℂ))
  let g (x : ℝ) := w x * f (a * x)
  have hw : ContDiff ℝ 1 w := (contDiff_const.mul (Complex.ofRealCLM.contDiff (n := 1))).cexp
  have hg : ContDiff ℝ 1 g :=
    hw.mul ((hsmooth.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp (contDiff_const.mul contDiff_id))
  have hw_norm (x : ℝ) : ‖w x‖ = 1 := by
    have hre : ℓ.re = 0 :=
      (Real.exp_eq_one_iff ℓ.re).mp (by rw [← Complex.norm_exp, hℓ, Circle.norm_coe])
    simp [w, Complex.norm_exp, Complex.mul_re, hre]
  have hderiv (x : ℝ) : deriv g x = w x *
      (ℓ * f (a * x) + (a : ℂ) * deriv f (a * x)) := by
    have hw' := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul ℓ).cexp
    have hf' := (hsmooth.differentiable (by simp) (a * x)).hasDerivAt.scomp x
      ((hasDerivAt_id x).const_mul a)
    convert (hw'.mul hf').deriv using 1
    · rfl
    · simp [w, Complex.real_smul]
      ring
  -- The twist is unitary, so the profile and its derivative retain exponential decay.
  obtain ⟨C, _, T, _, htail⟩ := hf.2 1
  have ht : Tendsto (fun x : ℝ ↦ |a * x|) (cocompact ℝ) atTop := by
    simpa only [abs_mul, Function.comp_def, Real.norm_eq_abs] using
      (tendsto_const_mul_atTop_of_pos (abs_pos.mpr ha)).mpr
        (tendsto_norm_cocompact_atTop (E := ℝ))
  have hexp : (fun x : ℝ ↦ Real.exp (-|a * x|)) =O[cocompact ℝ]
      (fun x : ℝ ↦ |x| ^ (-2 : ℝ)) := by
    simpa only [Function.comp_def, abs_mul, neg_mul, Real.norm_eq_abs] using
      (isLittleO_exp_neg_mul_rpow_atTop (abs_pos.mpr ha) (-2)).isBigO.comp_tendsto
        (tendsto_norm_cocompact_atTop (E := ℝ))
  have hg_decay : g =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-2 : ℝ)) := by
    refine (Asymptotics.IsBigO.of_bound (g := fun x : ℝ ↦ Real.exp (-|a * x|)) C ?_).trans hexp
    filter_upwards [ht.eventually_gt_atTop T] with x hx
    simpa only [g, norm_mul, hw_norm, one_mul, Real.norm_eq_abs, Real.abs_exp, Nat.cast_one,
      neg_one_mul] using (htail (a * x) hx).1.le
  have hg'_decay : deriv g =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-2 : ℝ)) := by
    refine (Asymptotics.IsBigO.of_bound (g := fun x : ℝ ↦ Real.exp (-|a * x|))
      ((‖ℓ‖ + |a|) * C) ?_).trans hexp
    filter_upwards [ht.eventually_gt_atTop T] with x hx
    obtain ⟨hfx, hdfx⟩ := htail (a * x) hx
    simp only [Nat.cast_one, neg_one_mul] at hfx hdfx
    rw [hderiv, norm_mul, hw_norm, one_mul, Real.norm_eq_abs, Real.abs_exp]
    calc
      _ ≤ ‖ℓ‖ * ‖f (a * x)‖ + |a| * ‖deriv f (a * x)‖ := by
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
          norm_add_le (ℓ * f (a * x)) ((a : ℂ) * deriv f (a * x))
      _ ≤ ‖ℓ‖ * (C * Real.exp (-|a * x|)) + |a| * (C * Real.exp (-|a * x|)) :=
        add_le_add (mul_le_mul_of_nonneg_left hfx.le (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hdfx.le (abs_nonneg _))
      _ = _ := by ring
  have hsum := (summable_norm_fourier_int_of_isBigO hg hg_decay hg'_decay).comp_injective
    (neg_injective : Function.Injective (fun m : ℤ ↦ -m))
  refine (hsum.mul_left |a|).congr fun m ↦ ?_
  -- Substitute t = exp(a * x) to identify the rescaled Mellin sample.
  let s := (ℓ + twoPiI * (m : ℂ)) / (a : ℂ)
  let F (y : ℝ) := Complex.exp (s * y) * f y
  have hmellin : logMellin f s = ∫ y, F y := by
    change mellin (fun t ↦ f (Real.log t)) s = _
    rw [mellin, ← integral_comp_exp]
    apply integral_congr_ae
    filter_upwards with y
    simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos y).ne'),
      ← Complex.ofReal_log (Real.exp_pos y).le, Real.log_exp]
    simp only [F, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hFourier : 𝓕 g ((-m : ℤ) : ℝ) = |a⁻¹| • logMellin f s := by
    rw [hmellin, ← Measure.integral_comp_mul_left F, Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [g, w, F, smul_eq_mul, ← mul_assoc, ← Complex.exp_add, Int.cast_neg,
      Complex.ofReal_neg, Complex.ofReal_intCast, Complex.ofReal_mul]
    congr 2
    dsimp [s]
    field_simp
    ring
  change |a| * ‖𝓕 g ((-m : ℤ) : ℝ)‖ = ‖logMellin f s‖
  rw [hFourier, norm_smul, Real.norm_eq_abs, abs_abs, abs_inv, ← mul_assoc,
    mul_inv_cancel₀ (abs_ne_zero.mpr ha), one_mul]

/-- Paper: Remark B.4.1.4, p. 608. The Mellin transform of the indicator of
the interval from one to two is (B.4.1.9), with its removable value at zero. -/
theorem mellin_indicator_one_two (s : ℂ) :
    mellin ((Icc (1 : ℝ) 2).indicator (fun _ ↦ (1 : ℂ))) s =
      if s = 0 then (Real.log 2 : ℂ) else ((2 : ℂ) ^ s - 1) / s := by
  have hint : mellin ((Icc (1 : ℝ) 2).indicator (fun _ ↦ (1 : ℂ))) s =
      ∫ t in (1 : ℝ)..2, (t : ℂ) ^ (s - 1) := by
    have heq : (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • (Icc (1 : ℝ) 2).indicator (fun _ ↦ (1 : ℂ)) t) =
        (Icc (1 : ℝ) 2).indicator (fun t : ℝ ↦ (t : ℂ) ^ (s - 1)) := by
      ext t
      by_cases ht : t ∈ Icc (1 : ℝ) 2 <;> simp [ht]
    rw [mellin, heq, MeasureTheory.setIntegral_indicator measurableSet_Icc,
      inter_eq_right.mpr (fun t (ht : t ∈ Icc (1 : ℝ) 2) ↦
        show (0 : ℝ) < t from zero_lt_one.trans_le ht.1),
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
  have h0 : (0 : ℝ) ∉ uIcc (1 : ℝ) 2 := by
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]; norm_num
  rw [hint]
  split_ifs with hs
  · subst hs
    have : (fun t : ℝ ↦ (t : ℂ) ^ ((0 : ℂ) - 1)) = fun t : ℝ ↦ ((t⁻¹ : ℝ) : ℂ) := by
      ext t; simp [Complex.cpow_neg_one]
    rw [this, intervalIntegral.integral_ofReal, integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  · rw [integral_cpow (Or.inr ⟨fun (h : s - 1 = -1) ↦ hs (by linear_combination h), h0⟩)]
    simp

section LocalFactor

variable {F : Type*} [Field F] [NumberField F]

local notation "q(" v ")" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ)
local notation "χ₀(" χ ")" => ideleClassNormTwist χ 0
local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "combWeight" =>
  (fun (c : ℂ) (q σ : ℝ) (m : ℕ) ↦ c ^ (m + 1) * (q ^ ((m + 1 : ℕ) * σ) : ℝ))
local notation "combTerm" =>
  (fun (c : ℂ) (q σ : ℝ) (m : ℕ) ↦ combWeight c q σ m • TemperedDistribution.delta (q ^ (m + 1)))

/-- Paper: Equation (B.4.1.18), p. 610. The local Dirac comb sums the
weighted Dirac distributions at the strictly positive powers of the prime norm.
Mathlib's tempered distributions carry the weak topology of pointwise convergence. -/
def localDiracComb (χ : U[F]) (v : HeightOneSpectrum (𝓞 F))
    (_hχ : χ₀(χ).IsUnramifiedAt v) (σ : ℝ) : 𝓢'(ℝ, ℂ) :=
  ∑' m : ℕ, combTerm (χ₀(χ).localValue v) q(v) σ m

-- TODO(paper-gap): The geometric majorant on p. 611 after (B.4.1.18)
-- is missing the index m in the exponent -2m.

/-- Paper: Equation (B.4.1.18), p. 611. Evaluation of the local Dirac comb on
a Schwartz function is the sum of its weighted values at the positive powers.
Deviation: Sanity check for the support, weights and normalization of the comb. -/
theorem hasSum_localDiracComb_apply (χ : U[F]) (v : HeightOneSpectrum (𝓞 F))
    (hχ : χ₀(χ).IsUnramifiedAt v) (σ : ℝ) (f : 𝓢(ℝ, ℂ)) :
    HasSum (fun m : ℕ ↦ combWeight (χ₀(χ).localValue v) q(v) σ m * f (q(v) ^ (m + 1)))
      (localDiracComb χ v hχ σ f) := by
  let q : ℝ := q(v)
  let term := combTerm (χ₀(χ).localValue v) q σ
  obtain ⟨k, hk⟩ := exists_nat_gt σ
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₀ := zero_lt_one.trans hq
  let r : ℝ := q ^ (σ - k)
  have hr₀ : 0 ≤ r := Real.rpow_nonneg hq₀.le _
  have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (sub_neg.mpr hk)
  have hgeom : Summable (fun m : ℕ ↦ r ^ (m + 1)) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hr₀ hr₁)
  have hfactor : r * q ^ k = q ^ σ := by
    dsimp only [r]
    rw [← Real.rpow_natCast q k, ← Real.rpow_add hq₀, sub_add_cancel]
  have hbound (g : 𝓢(ℝ, ℂ)) (m : ℕ) :
      ‖term m g‖ ≤ r ^ (m + 1) * SchwartzMap.seminorm ℂ k 0 g := by
    have hg := SchwartzMap.norm_pow_mul_le_seminorm ℂ g k (q ^ (m + 1))
    rw [Real.norm_of_nonneg (pow_nonneg hq₀.le _)] at hg
    change ‖(χ₀(χ).localValue v ^ (m + 1) * (q ^ ((m + 1 : ℕ) * σ) : ℝ)) *
      g (q ^ (m + 1))‖ ≤ _
    rw [norm_mul, norm_mul, norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow,
      one_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq₀.le _),
      mul_comm ((m + 1 : ℕ) : ℝ) σ, Real.rpow_mul_natCast hq₀.le, ← hfactor, mul_pow,
      ← pow_mul, Nat.mul_comm k (m + 1), pow_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hg (pow_nonneg hr₀ _)
  have hsum (g : 𝓢(ℝ, ℂ)) : Summable (fun m ↦ term m g) :=
    (hgeom.mul_right _).of_norm_bounded (hbound g)
  -- The same seminorm bounds the pointwise sum, so it defines a tempered distribution.
  let L : 𝓢(ℝ, ℂ) →L[ℂ] ℂ := SchwartzMap.mkCLMtoNormedSpace
    (fun g ↦ ∑' m, term m g)
    (fun g h ↦ by simp only [map_add, (hsum g).tsum_add (hsum h)])
    (fun a g ↦ by simp only [map_smul, RingHom.id_apply, (hsum g).tsum_const_smul a])
    (by
      refine ⟨{(k, 0)}, ∑' m : ℕ, r ^ (m + 1), tsum_nonneg (fun _ ↦ pow_nonneg hr₀ _), ?_⟩
      intro g
      rw [Finset.sup_singleton]
      exact tsum_of_norm_bounded (hgeom.hasSum.mul_right _) (hbound g))
  let T : 𝓢'(ℝ, ℂ) := ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _ L
  have hT : HasSum term T := by
    apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr
    intro g
    rw [show T g = ∑' m, term m g from rfl]
    simpa only [HasSum, sum_apply] using (hsum g).hasSum
  have hcomb : localDiracComb χ v hχ σ = T := hT.tsum_eq
  rw [hcomb]
  exact (hsum f).hasSum

/-- Paper: Equation (B.4.1.18), p. 611. The weighted Dirac series converges
to the local comb in the weak topology. -/
theorem hasSum_localDiracComb (χ : U[F]) (v : HeightOneSpectrum (𝓞 F))
    (hχ : χ₀(χ).IsUnramifiedAt v) (σ : ℝ) :
    HasSum (combTerm (χ₀(χ).localValue v) q(v) σ) (localDiracComb χ v hχ σ) := by sorry

local notation "toStrongSchwartzDual" =>
  (WeakDual.toStrongDual ∘ PointwiseConvergenceCLM.equivWeakDual ℂ 𝓢(ℝ, ℂ))

/-- Paper: Remark B.4.1.6, p. 611. The partial sums of the local Dirac comb
also converge in the strong dual, uniformly on bounded sets of Schwartz functions. -/
theorem tendsto_localDiracComb_strongDual (χ : U[F]) (v : HeightOneSpectrum (𝓞 F))
    (hχ : χ₀(χ).IsUnramifiedAt v) (σ : ℝ) :
    Tendsto (fun n : ℕ ↦
      ∑ m ∈ Finset.range n, toStrongSchwartzDual (combTerm (χ₀(χ).localValue v) q(v) σ m))
      atTop (𝓝 (toStrongSchwartzDual (localDiracComb χ v hχ σ))) := by sorry

variable (χ : U[F]) (v : HeightOneSpectrum (𝓞 F)) (hχ : χ₀(χ).IsUnramifiedAt v)
variable (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f)

include hχ hf

/-- Paper: Lemma B.4.1.7, p. 611. The two-sided series of weighted values
at the integer powers of the prime norm converges absolutely. -/
theorem summable_localEulerFactor_lattice :
    Summable (fun m : ℤ ↦ (χ₀(χ).localValue v) ^ m * f ((m : ℝ) * Real.log q(v))) :=
  by sorry

/-- Paper: Lemma B.4.1.7, p. 611. The Mellin frequency samples sum
absolutely to the two-sided local lattice sum multiplied by the logarithm of the norm.
This is the first equality in (B.4.1.20). -/
theorem hasSum_localEulerFactor_mellinSamples (ℓ : ℂ)
    (hℓ : Complex.exp ℓ = χ₀(χ).localValue v) :
    HasSum (fun m : ℤ ↦ logMellin f ((ℓ + twoPiI * (m : ℂ)) / (Real.log q(v) : ℂ)))
      ((Real.log q(v) : ℂ) *
        ∑' m : ℤ, (χ₀(χ).localValue v) ^ m * f ((m : ℝ) * Real.log q(v))) := by sorry

local notation "eulerIntegrand" =>
  (fun (s : ℂ) ↦ logMellin f s * logDeriv (finiteHeckeEulerFactor χ v) s)

/-- Paper: Lemma B.4.1.7, p. 611. The Mellin transform times the logarithmic
derivative of the unramified Euler factor is integrable on the right vertical line. -/
theorem verticalIntegrable_localEulerFactor_mellin (a : ℝ) (ha : 0 < a) :
    Complex.VerticalIntegrable eulerIntegrand a := by sorry

-- TODO(paper-gap): The second equality in (B.4.1.20) and (B.4.1.35) omit
-- the left vertical integral needed for the full residue sum. The right
-- vertical line alone gives only the strictly positive powers of the prime norm.
-- On p. 614 the dropped integral of Φ is 2πi times the test function at one.

/-- Paper: Lemma B.4.1.7, p. 611. The negative normalized right-line
integral is the logarithm of the norm times the local Dirac sum at weight zero.
Deviation: The single right-line integral in (B.4.1.20) gives only strictly
positive powers, as follows from the Euler expansion (B.4.2.7) and Mellin inversion. -/
theorem hasSum_localEulerFactor_cauchyIntegral (a : ℝ) (ha : 0 < a) :
    HasSum (fun m : ℕ ↦ (Real.log q(v) : ℂ) * (χ₀(χ).localValue v) ^ (m + 1) *
      f ((m + 1 : ℕ) * Real.log q(v))) (-verticalLineIntegral eulerIntegrand a / twoPiI) :=
  by sorry

end LocalFactor

set_option quotPrecheck false in
local notation "poleTerm" =>
  (fun (m : {m : ℤ // m ≠ 0}) (z : ℂ) ↦
    let n : ℂ := (Subtype.val m : ℤ)
    1 / (z - n) + 1 / n)

/-- Paper: Lemma B.4.1.9, p. 612. The sum of the norms of the regularized
pole terms in (B.4.1.21) converges locally uniformly off the integers. -/
theorem summableLocallyUniformlyOn_expPoleTerms :
    SummableLocallyUniformlyOn (fun m z ↦ ‖poleTerm m z‖) Complex.integerComplement := by sorry

/-- Paper: Lemma B.4.1.9, p. 612. The reciprocal of one minus the
exponential has the regularized partial-fraction expansion (B.4.1.21). -/
theorem inv_one_sub_exp_eq_mittagLeffler {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    (1 - Complex.exp (twoPiI * z))⁻¹ =
      1 / 2 - 1 / (twoPiI * z) - (1 / twoPiI) * ∑' m, poleTerm m z := by sorry

/-- Paper: Lemma B.4.1.9, p. 612. The norm of the sum of the regularized
pole terms is bounded on each horizontal line of nonzero height, as in (B.4.1.22). -/
theorem norm_tsum_expPoleTerms_le (a : ℝ) (ha : a ≠ 0) :
    ∃ C > (0 : ℝ), ∀ z : ℂ, z.im = a → ‖∑' m, poleTerm m z‖ ≤ C := by sorry

-- TODO(paper-gap): The squared reciprocal sum in the proof of (B.4.1.23)
-- omits the index zero, so it is only bounded above by the full periodic sum.

/-- Paper: Lemma B.4.1.9, p. 612. On a horizontal line of nonzero height,
the sum of the norms of the pole terms grows at most linearly in the modulus,
as in (B.4.1.23). -/
theorem tsum_norm_expPoleTerms_le (a : ℝ) (ha : a ≠ 0) :
    ∃ C > (0 : ℝ), ∀ z : ℂ, z.im = a → (∑' m, ‖poleTerm m z‖) ≤ C * ‖z‖ := by sorry

-- TODO(paper-gap): The left side of (B.4.1.33) is positive at t = 0, so
-- the asserted majorant needs a constant term.

end RiemannMasullo
