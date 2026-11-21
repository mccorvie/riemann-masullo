module

public import Mathlib.Analysis.Complex.IntegerCompl
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import RiemannMasullo.AppB_AnalyticNT.Sec2
public import RiemannMasullo.Ch03_IdelicZeta.Sec2
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
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

open MeasureTheory in
/-- The Mellin samples in the logarithmic coordinate are the Fourier integrals of the
rescaled, twisted profile, with the absolute Jacobian of the rescaling. -/
private theorem logMellin_eq_mul_integral_twist (f : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0)
    (ℓ : ℂ) (m : ℤ) :
    mellin (fun t ↦ f (Real.log t)) ((ℓ + twoPiI * (m : ℂ)) / (a : ℂ)) =
      ((|a| : ℝ) : ℂ) *
        ∫ x : ℝ, Complex.exp (twoPiI * (m : ℂ) * (x : ℂ)) *
          (Complex.exp (ℓ * (x : ℂ)) * f (a * x)) := by
  let s := (ℓ + twoPiI * (m : ℂ)) / (a : ℂ)
  let F (y : ℝ) := Complex.exp (s * y) * f y
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hmellin : mellin (fun t ↦ f (Real.log t)) s = ∫ y, F y := by
    rw [mellin, ← integral_comp_exp]
    apply integral_congr_ae
    filter_upwards with y
    simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos y).ne'),
      ← Complex.ofReal_log (Real.exp_pos y).le, Real.log_exp]
    simp only [F, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have heq (x : ℝ) :
      Complex.exp (twoPiI * (m : ℂ) * (x : ℂ)) *
        (Complex.exp (ℓ * (x : ℂ)) * f (a * x)) = F (a * x) := by
    simp only [F, Complex.ofReal_mul, ← mul_assoc, ← Complex.exp_add]
    congr 2
    dsimp [s]
    field_simp
    ring
  simp_rw [heq, Measure.integral_comp_mul_left, abs_inv, Complex.real_smul, Complex.ofReal_inv,
    ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr ha)), one_mul]
  exact hmellin

/-- The finite one-sided limits extend the tail estimate to a global bound. -/
private theorem mellinTest_global_exp_bound {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) :
    ∃ A > (0 : ℝ), ∀ x, ‖f x‖ ≤ A * Real.exp (-|x|) ∧
      ‖deriv f x‖ ≤ A * Real.exp (-|x|) := by
  obtain ⟨⟨S, hs, hlimits⟩, hdecay⟩ := hf
  obtain ⟨C, hC, T, _, htail⟩ := hdecay 1
  have hopen : IsOpen (S : Set ℝ)ᶜ := S.finite_toSet.isClosed.isOpen_compl
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
  obtain ⟨U, hU⟩ := hcompact hs.continuousOn (by simpa only [iteratedDeriv_zero] using hlimits 0)
  obtain ⟨V, hV⟩ := hcompact (hs.continuousOn_deriv_of_isOpen hopen (by simp))
    (by simpa only [iteratedDeriv_one] using hlimits 1)
  let A := C + (|U| + |V|) * Real.exp T
  have hCA : C ≤ A := le_add_of_nonneg_right (by positivity)
  refine ⟨A, hC.trans_le hCA, fun x ↦ ?_⟩
  by_cases hx : T < |x|
  · obtain ⟨h₀, h₁⟩ := htail x hx
    simp only [Nat.cast_one, neg_one_mul] at h₀ h₁
    exact ⟨h₀.le.trans (mul_le_mul_of_nonneg_right hCA (Real.exp_pos _).le),
      h₁.le.trans (mul_le_mul_of_nonneg_right hCA (Real.exp_pos _).le)⟩
  · have hTx : |x| ≤ T := le_of_not_gt hx
    have hx' := abs_le.mp hTx
    have hcalc (y : ℝ) (hy : y ≤ |U| + |V|) : y ≤ A * Real.exp (-|x|) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
      exact (mul_le_mul hy (Real.exp_le_exp.mpr hTx) (Real.exp_pos _).le (by positivity)).trans
        (le_add_of_nonneg_left hC.le)
    exact ⟨hcalc _ ((hU x hx').trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))),
      hcalc _ ((hV x hx').trans ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))))⟩

/-- A unitary twist and a nonzero rescaling preserve exponential bounds off the jumps. -/
private theorem mellinTest_twisted_deriv_bound {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f)
    {a : ℝ} (ha : a ≠ 0) {ℓ : ℂ} (hunit : ℓ.re = 0) :
    let w (x : ℝ) := Complex.exp (ℓ * (x : ℂ))
    let g (x : ℝ) := w x * f (a * x)
    ∃ S : Set ℝ, S.Finite ∧ ∃ A > (0 : ℝ),
      (∀ x, ‖g x‖ ≤ A * Real.exp (-|a| * |x|)) ∧
      ∀ x ∉ S, DifferentiableAt ℝ g x ∧ ‖deriv g x‖ ≤ A * Real.exp (-|a| * |x|) := by
  dsimp only
  obtain ⟨A, hA, hbound⟩ := mellinTest_global_exp_bound hf
  obtain ⟨S, hs, _⟩ := hf.1
  let w (x : ℝ) := Complex.exp (ℓ * (x : ℂ))
  let g (x : ℝ) := w x * f (a * x)
  have hwnorm (x : ℝ) : ‖w x‖ = 1 := by simp [w, Complex.norm_exp, Complex.mul_re, hunit]
  let M := (1 + ‖ℓ‖ + |a|) * A
  have hM : A ≤ M := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 1 + ‖ℓ‖ + |a| by
        linarith [norm_nonneg ℓ, abs_nonneg a]) hA.le
  refine ⟨(fun x : ℝ ↦ a * x) ⁻¹' (S : Set ℝ), ?_, M, hA.trans_le hM, ?_, ?_⟩
  · exact S.finite_toSet.preimage (mul_right_injective₀ ha).injOn
  · intro x
    change ‖w x * f (a * x)‖ ≤ _
    rw [norm_mul, hwnorm, one_mul, neg_mul, ← abs_mul]
    exact (hbound _).1.trans (mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le)
  · intro x hx
    have hf' := ((hs (a * x) hx).contDiffAt
      (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hx)).differentiableAt (by simp)
    have hw' := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul ℓ).cexp
    have hcom := hf'.hasDerivAt.scomp x ((hasDerivAt_id x).const_mul a)
    have hderiv : HasDerivAt g (w x * (ℓ * f (a * x) + (a : ℂ) * deriv f (a * x))) x := by
      convert hw'.mul hcom using 1
      · rfl
      · simp [w, Complex.real_smul]
        ring
    refine ⟨hderiv.differentiableAt, ?_⟩
    rw [hderiv.deriv, norm_mul, hwnorm, one_mul, neg_mul, ← abs_mul]
    calc
      _ ≤ ‖ℓ‖ * ‖f (a * x)‖ + |a| * ‖deriv f (a * x)‖ := by
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
          norm_add_le (ℓ * f (a * x)) ((a : ℂ) * deriv f (a * x))
      _ ≤ ‖ℓ‖ * (A * Real.exp (-|a * x|)) + |a| * (A * Real.exp (-|a * x|)) :=
        add_le_add (mul_le_mul_of_nonneg_left (hbound _).1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (hbound _).2 (abs_nonneg _))
      _ = (‖ℓ‖ + |a|) * A * Real.exp (-|a * x|) := by ring
      _ ≤ _ := by
        dsimp [M]
        gcongr
        linarith


/-- The one-sided limits at a lattice point give the midpoint multiplied by the character value. -/
private theorem mellinTwist_tendsto_lattice {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f)
    {a : ℝ} (ha : a ≠ 0) (c : Circle) {ℓ : ℂ} (hℓ : Complex.exp ℓ = (c : ℂ)) (n : ℤ) :
    let g (x : ℝ) := Complex.exp (ℓ * (x : ℂ)) * f (a * x)
    ∃ u v : ℂ, Tendsto (fun x : ℝ ↦ g (x + n)) (𝓝[>] 0) (𝓝 u) ∧
      Tendsto (fun x : ℝ ↦ g (-x + n)) (𝓝[>] 0) (𝓝 v) ∧
      (u + v) / 2 = (c : ℂ) ^ n * mellinJumpMidpoint f ((n : ℝ) * a) := by
  dsimp only
  have hlimits (x : ℝ) : ∃ l r : ℂ, Tendsto f (𝓝[<] x) (𝓝 l) ∧ Tendsto f (𝓝[>] x) (𝓝 r) := by
    obtain ⟨S, hS, hlim⟩ := hf.1
    by_cases hx : x ∈ S
    · obtain ⟨⟨l, hl⟩, ⟨r, hr⟩⟩ := hlim 0 x hx
      exact ⟨l, r, by rwa [iteratedDeriv_zero] at hl, by rwa [iteratedDeriv_zero] at hr⟩
    · have h := hS.continuousOn.continuousAt (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hx)
      exact ⟨f x, f x, h.tendsto.mono_left nhdsWithin_le_nhds, h.tendsto.mono_left nhdsWithin_le_nhds⟩
  obtain ⟨l, r, hl, hr⟩ := hlimits ((n : ℝ) * a)
  let w (x : ℝ) := Complex.exp (ℓ * (x : ℂ))
  have h₀ : Tendsto (fun x : ℝ ↦ x) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hw : Continuous w := by dsimp [w]; fun_prop
  have he : w (n : ℝ) = (c : ℂ) ^ n := by
    rw [show w (n : ℝ) = Complex.exp ((n : ℂ) * ℓ) by
      simp [w, mul_comm], Complex.exp_int_mul, hℓ]
  have hright : Tendsto (fun x : ℝ ↦ w (x + n)) (𝓝[>] 0) (𝓝 ((c : ℂ) ^ n)) := by
    rw [← he]
    exact (hw.tendsto (n : ℝ)).comp (by simpa only [zero_add] using h₀.add_const (n : ℝ))
  have hleft : Tendsto (fun x : ℝ ↦ w (-x + n)) (𝓝[>] 0) (𝓝 ((c : ℂ) ^ n)) := by
    rw [← he]
    exact (hw.tendsto (n : ℝ)).comp
      (by simpa only [neg_zero, zero_add] using h₀.neg.add_const (n : ℝ))
  have hrescale (d : ℝ) :
      Tendsto (fun x : ℝ ↦ (n : ℝ) * a + d * x) (𝓝[>] 0) (𝓝 ((n : ℝ) * a)) := by
    simpa only [mul_zero, add_zero] using (h₀.const_mul d).const_add ((n : ℝ) * a)
  have hrescale_pos (d : ℝ) (hd : 0 < d) :
      Tendsto (fun x : ℝ ↦ (n : ℝ) * a + d * x) (𝓝[>] 0) (𝓝[>] ((n : ℝ) * a)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrescale d, by
      filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with x hx
      exact lt_add_of_pos_right _ (mul_pos hd hx)⟩
  have hrescale_neg (d : ℝ) (hd : d < 0) :
      Tendsto (fun x : ℝ ↦ (n : ℝ) * a + d * x) (𝓝[>] 0) (𝓝[<] ((n : ℝ) * a)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrescale d, by
      filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with x hx
      exact add_lt_of_neg_right _ (mul_neg_of_neg_of_pos hd hx)⟩
  have hplus (x : ℝ) : a * (x + (n : ℝ)) = (n : ℝ) * a + a * x := by ring
  have hminus (x : ℝ) : a * (-x + (n : ℝ)) = (n : ℝ) * a + (-a) * x := by ring
  rw [mellinJumpMidpoint_eq_average hl hr]
  rcases lt_or_gt_of_ne ha with ha' | ha'
  · refine ⟨(c : ℂ) ^ n * l, (c : ℂ) ^ n * r, ?_, ?_, by ring⟩
    · simpa only [w, hplus, Function.comp_def] using hright.mul (hl.comp (hrescale_neg a ha'))
    · simpa only [w, hminus, Function.comp_def] using hleft.mul (hr.comp (hrescale_pos (-a) (by linarith)))
  · refine ⟨(c : ℂ) ^ n * r, (c : ℂ) ^ n * l, ?_, ?_, by ring⟩
    · simpa only [w, hplus, Function.comp_def] using hright.mul (hr.comp (hrescale_pos a ha'))
    · simpa only [w, hminus, Function.comp_def] using hleft.mul (hl.comp (hrescale_neg (-a) (by linarith)))

/-- Paper: Proposition B.4.1.2, p. 609. The twisted periodization is bounded on a
fundamental interval. Its even part approaches the weighted midpoint sum at least
linearly at the center of that interval. -/
private theorem mellinTwistedPeriodization_bounds {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f)
    {a : ℝ} (ha : a ≠ 0) (c : Circle) {ℓ : ℂ} (hℓ : Complex.exp ℓ = (c : ℂ)) :
    let F (x : ℝ) := ∑' n : ℤ, Complex.exp (ℓ * ((x + (n : ℝ) : ℝ) : ℂ)) * f (a * (x + n))
    let L := ∑' n : ℤ, (c : ℂ) ^ n * mellinJumpMidpoint f ((n : ℝ) * a)
    ∃ C ≥ (0 : ℝ),
      (∀ x ∈ Icc (-(1 / 2) : ℝ) (1 / 2), ‖F x‖ ≤ C) ∧
      ∀ x ∈ Ioc (0 : ℝ) (1 / 2), ‖F x + F (-x) - 2 * L‖ ≤ C * x := by
  dsimp only
  have hunit : ℓ.re = 0 :=
    (Real.exp_eq_one_iff ℓ.re).mp (by rw [← Complex.norm_exp, hℓ, Circle.norm_coe])
  obtain ⟨S, hS, A, hA, hg, hderiv⟩ := mellinTest_twisted_deriv_bound hf ha hunit
  choose u v hu hv hmean using fun n : ℤ ↦ mellinTwist_tendsto_lattice hf ha c hℓ n
  simpa only [hmean] using periodization_bounds_of_exp_decay hS hA (abs_pos.mpr ha)
    hg hderiv hu hv

open MeasureTheory in
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
        ∑' m : ℤ, (c : ℂ) ^ m * mellinJumpMidpoint f ((m : ℝ) * Real.log θ))) := by
  let a := Real.log θ
  have ha : a ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hθ hθ₁
  let w (x : ℝ) := Complex.exp (ℓ * (x : ℂ))
  let g (x : ℝ) := w x * f (a * x)
  let F (x : ℝ) := ∑' n : ℤ, g (x + n)
  let L := ∑' n : ℤ, (c : ℂ) ^ n * mellinJumpMidpoint f ((n : ℝ) * a)
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hw_norm (x : ℝ) : ‖w x‖ = 1 := by
    have hre : ℓ.re = 0 :=
      (Real.exp_eq_one_iff ℓ.re).mp (by rw [← Complex.norm_exp, hℓ, Circle.norm_coe])
    simp [w, Complex.norm_exp, Complex.mul_re, hre]
  have hfi : Integrable f := by
    apply (integrableOn_comp_log_Ioi_zero f).mp
    simpa [MellinConvergent, Complex.cpow_neg_one, Complex.real_smul] using
      mellinConvergent_of_piecewiseSmoothMellinTest hf 0
  have hg : Integrable g :=
    (hfi.comp_mul_left' ha).bdd_mul hw.aestronglyMeasurable (Eventually.of_forall fun x ↦ (hw_norm x).le)
  have hmeas : Measurable f := by
    obtain ⟨⟨S, hS, -⟩, -⟩ := hf
    exact hS.continuousOn.measurable_of_countable_compl (by simpa using S.finite_toSet.countable)
  have hgm : Measurable g :=
    hw.measurable.mul (hmeas.comp (measurable_const.mul measurable_id))
  have hFm : Measurable F :=
    Measurable.tsum (fun n : ℤ ↦ hgm.comp (measurable_id.add_const (n : ℝ)))
  obtain ⟨C, hC, hFbound, hresidual⟩ := mellinTwistedPeriodization_bounds hf ha c hℓ
  change ∀ x ∈ Icc (-(1 / 2) : ℝ) (1 / 2), ‖F x‖ ≤ C at hFbound
  change ∀ x ∈ Ioc (0 : ℝ) (1 / 2), ‖F x + F (-x) - 2 * L‖ ≤ C * x at hresidual
  have hF : IntervalIntegrable F volume (-(1 / 2)) (1 / 2) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
    refine (integrable_const C).mono' hFm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hFbound x (Ioc_subset_Icc_self hx)
  have hquot : IntegrableOn
      (fun x : ℝ ↦ (F x + F (-x) - 2 * L) / (Complex.exp (twoPiI * (x : ℂ)) - 1))
      (Ioc 0 (1 / 2)) := by
    have hm : Measurable (fun x : ℝ ↦
        (F x + F (-x) - 2 * L) / (Complex.exp (twoPiI * (x : ℂ)) - 1)) := by
      fun_prop
    refine (integrable_const C).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx' : 0 < x := hx.1
    have hs : 2 * x ≤ Real.sin (Real.pi * x) := by
      have hs₀ := Real.mul_le_sin (mul_nonneg Real.pi_pos.le hx'.le)
        (by nlinarith only [mul_le_mul_of_nonneg_left hx.2 Real.pi_pos.le] :
          Real.pi * x ≤ Real.pi / 2)
      have heq : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
      rwa [heq] at hs₀
    have hnorm : 4 * x ≤ ‖Complex.exp (twoPiI * (x : ℂ)) - 1‖ := by
      have heq : twoPiI * (x : ℂ) = Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) := by
        push_cast
        ring
      rw [heq, Complex.norm_exp_I_mul_ofReal_sub_one,
        show 2 * Real.pi * x / 2 = Real.pi * x by ring]
      exact (by linarith : 4 * x ≤ 2 * Real.sin (Real.pi * x)).trans (le_abs_self _)
    rw [norm_div, div_le_iff₀ ((by positivity : 0 < 4 * x).trans_le hnorm)]
    exact (hresidual x hx).trans (mul_le_mul_of_nonneg_left (by linarith) hC |>.trans
      (mul_le_mul_of_nonneg_left hnorm hC))
  have hlim := (tendsto_symmetric_fourier_integrals_of_integrable_quotient hF hquot).const_mul
    ((|a| : ℝ) : ℂ)
  convert hlim using 1
  ext N
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  change mellin (fun t ↦ f (Real.log t)) ((ℓ + twoPiI * (m : ℂ)) / (a : ℂ)) = _
  rw [logMellin_eq_mul_integral_twist f ha ℓ m]
  congr 1
  exact (integral_periodization_mul_exp_int hg m).symm

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

/-- Paper: Equation (B.4.1.18), p. 611. Each weighted Dirac evaluation is bounded
by a summable geometric factor times a fixed Schwartz seminorm. -/
private theorem exists_localDiracComb_majorant (χ : U[F]) (v : HeightOneSpectrum (𝓞 F))
    (σ : ℝ) :
    ∃ (k : ℕ) (u : ℕ → ℝ), Summable u ∧ (∀ m, 0 ≤ u m) ∧
      ∀ (g : 𝓢(ℝ, ℂ)) (m : ℕ),
        ‖combTerm (χ₀(χ).localValue v) q(v) σ m g‖ ≤ u m * SchwartzMap.seminorm ℂ k 0 g := by
  let q : ℝ := q(v)
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
  refine ⟨k, (fun m ↦ r ^ (m + 1)), hgeom, (fun _ ↦ pow_nonneg hr₀ _), fun g m ↦ ?_⟩
  have hg := SchwartzMap.norm_pow_mul_le_seminorm ℂ g k (q ^ (m + 1))
  rw [Real.norm_of_nonneg (pow_nonneg hq₀.le _)] at hg
  change ‖(χ₀(χ).localValue v ^ (m + 1) * (q ^ ((m + 1 : ℕ) * σ) : ℝ)) *
    g (q ^ (m + 1))‖ ≤ _
  rw [norm_mul, norm_mul, norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow,
    one_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq₀.le _),
    mul_comm ((m + 1 : ℕ) : ℝ) σ, Real.rpow_mul_natCast hq₀.le, ← hfactor, mul_pow,
    ← pow_mul, Nat.mul_comm k (m + 1), pow_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left hg (pow_nonneg hr₀ _)

/-- Paper: Equation (B.4.1.18), p. 611. Evaluation of the local Dirac comb on
a Schwartz function is the sum of its weighted values at the positive powers.
Deviation: Sanity check for the support, weights and normalization of the comb. -/
theorem hasSum_localDiracComb_apply (χ : U[F]) (v : HeightOneSpectrum (𝓞 F))
    (hχ : χ₀(χ).IsUnramifiedAt v) (σ : ℝ) (f : 𝓢(ℝ, ℂ)) :
    HasSum (fun m : ℕ ↦ combWeight (χ₀(χ).localValue v) q(v) σ m * f (q(v) ^ (m + 1)))
      (localDiracComb χ v hχ σ f) := by
  let term := combTerm (χ₀(χ).localValue v) q(v) σ
  obtain ⟨k, u, hu, hu₀, hbound⟩ := exists_localDiracComb_majorant χ v σ
  have hsum (g : 𝓢(ℝ, ℂ)) : Summable (fun m ↦ term m g) :=
    (hu.mul_right _).of_norm_bounded (hbound g)
  -- The same seminorm bounds the pointwise sum, so it defines a tempered distribution.
  let L : 𝓢(ℝ, ℂ) →L[ℂ] ℂ := SchwartzMap.mkCLMtoNormedSpace
    (fun g ↦ ∑' m, term m g)
    (fun g h ↦ by simp only [map_add, (hsum g).tsum_add (hsum h)])
    (fun a g ↦ by simp only [map_smul, RingHom.id_apply, (hsum g).tsum_const_smul a])
    (by
      refine ⟨{(k, 0)}, ∑' m, u m, tsum_nonneg hu₀, ?_⟩
      intro g
      rw [Finset.sup_singleton]
      exact tsum_of_norm_bounded (hu.hasSum.mul_right _) (hbound g))
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
    HasSum (combTerm (χ₀(χ).localValue v) q(v) σ) (localDiracComb χ v hχ σ) := by
  apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr
  intro f
  simpa only [HasSum, sum_apply, smul_apply, TemperedDistribution.delta_apply, smul_eq_mul]
    using hasSum_localDiracComb_apply χ v hχ σ f

local notation "toStrongSchwartzDual" =>
  (WeakDual.toStrongDual ∘ PointwiseConvergenceCLM.equivWeakDual ℂ 𝓢(ℝ, ℂ))

/-- Paper: Remark B.4.1.6, p. 611. The partial sums of the local Dirac comb
also converge in the strong dual, uniformly on bounded sets of Schwartz functions. -/
theorem tendsto_localDiracComb_strongDual (χ : U[F]) (v : HeightOneSpectrum (𝓞 F))
    (hχ : χ₀(χ).IsUnramifiedAt v) (σ : ℝ) :
    Tendsto (fun n : ℕ ↦
      ∑ m ∈ Finset.range n, toStrongSchwartzDual (combTerm (χ₀(χ).localValue v) q(v) σ m))
      atTop (𝓝 (toStrongSchwartzDual (localDiracComb χ v hχ σ))) := by
  let term := combTerm (χ₀(χ).localValue v) q(v) σ
  rw [(ContinuousLinearMap.isUniformEmbedding_toUniformOnFun (σ := RingHom.id ℂ)
    (E := 𝓢(ℝ, ℂ)) (F := ℂ)).isEmbedding.tendsto_nhds_iff,
    UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  intro s hs
  obtain ⟨k, u, hu, hu₀, hbound⟩ := exists_localDiracComb_majorant χ v σ
  obtain ⟨C, _, hC⟩ :=
    ((schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp hs) (k, 0)
  have hmajor (m : ℕ) (g : 𝓢(ℝ, ℂ)) (hg : g ∈ s) : ‖term m g‖ ≤ u m * C :=
    (hbound g m).trans (mul_le_mul_of_nonneg_left (hC g hg).le (hu₀ m))
  have hlim := (tendstoUniformlyOn_tsum_nat (hu.mul_right C) hmajor).congr_right
    (show EqOn (fun g ↦ ∑' m, term m g) (localDiracComb χ v hχ σ) s from
      fun g _ ↦ (hasSum_localDiracComb_apply χ v hχ σ g).tsum_eq)
  change TendstoUniformlyOn (fun n g ↦ (∑ m ∈ Finset.range n,
    toStrongSchwartzDual (term m)) g) (localDiracComb χ v hχ σ) atTop s
  simp only [sum_apply]
  exact hlim

variable (χ : U[F]) (v : HeightOneSpectrum (𝓞 F)) (hχ : χ₀(χ).IsUnramifiedAt v)
variable (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f)

include hχ hf

/-- Paper: Lemma B.4.1.7, p. 611. The two-sided series of weighted values
at the integer powers of the prime norm converges absolutely. -/
theorem summable_localEulerFactor_lattice :
    Summable (fun m : ℤ ↦ (χ₀(χ).localValue v) ^ m * f ((m : ℝ) * Real.log q(v))) := by
  have hq : 1 < q(v) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  let e := (LinearEquiv.smulOfNeZero ℝ ℝ (Real.log q(v))
    (Real.log_pos hq).ne').toContinuousLinearEquiv
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have hsum : Summable (fun m : ℤ ↦ ‖g (m : ℝ)‖) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((g.isBigO_cocompact_rpow (-2)).norm_left.comp_tendsto Int.tendsto_coe_cofinite)
  refine hsum.of_norm_bounded fun m ↦ ?_
  rw [norm_mul, norm_zpow, norm_ideleClassNormTwist_zero_localValue, one_zpow, one_mul]
  change ‖f ((m : ℝ) * Real.log q(v))‖ ≤ ‖f (Real.log q(v) * (m : ℝ))‖
  rw [mul_comm (m : ℝ)]

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

omit hχ hf in
/-- In the right half-plane a unimodular multiple of `q ^ (-s)` stays away from one. -/
private lemma one_sub_le_norm_one_sub_mul_cpow {c : ℂ} {q : ℕ} (hq : 1 < q) (hc : ‖c‖ = 1)
    (s : ℂ) : 1 - (q : ℝ) ^ (-s.re) ≤ ‖1 - c * (q : ℂ) ^ (-s)‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (c * (q : ℂ) ^ (-s))
  rwa [norm_one, norm_mul, hc, one_mul,
    Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans hq), Complex.neg_re] at h

omit hχ hf in
/-- The logarithmic derivative of the Euler factor `(1 - c q ^ (-s))⁻¹` on the
right half-plane. -/
private lemma logDeriv_inv_one_sub_mul_cpow {c : ℂ} {q : ℕ} (hq : 1 < q) (hc : ‖c‖ = 1)
    {s : ℂ} (hs : 0 < s.re) :
    logDeriv (fun z : ℂ ↦ (1 - c * (q : ℂ) ^ (-z))⁻¹) s =
      -(c * ((q : ℂ) ^ (-s) * Complex.log q)) / (1 - c * (q : ℂ) ^ (-s)) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (zero_lt_one.trans hq).ne'
  have hr : (q : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq) (neg_neg_of_pos hs)
  have hne : 1 - c * (q : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have hle := one_sub_le_norm_one_sub_mul_cpow hq hc s
    rw [h, norm_zero] at hle
    linarith
  have hpow : HasDerivAt (fun z : ℂ ↦ (q : ℂ) ^ (-z))
      ((q : ℂ) ^ (-s) * Complex.log q * (-1)) s :=
    (hasDerivAt_neg' s).const_cpow (Or.inl hq0)
  have hd : HasDerivAt (fun z : ℂ ↦ 1 - c * (q : ℂ) ^ (-z))
      (c * ((q : ℂ) ^ (-s) * Complex.log q)) s := by
    convert (hpow.const_mul c).const_sub 1 using 1
    ring
  have hinv : HasDerivAt (fun z : ℂ ↦ (1 - c * (q : ℂ) ^ (-z))⁻¹)
      (-(c * ((q : ℂ) ^ (-s) * Complex.log q)) / (1 - c * (q : ℂ) ^ (-s)) ^ 2) s := hd.inv hne
  rw [logDeriv_apply, hinv.deriv, div_inv_eq_mul, sq, div_mul_eq_mul_div,
    mul_div_mul_right _ _ hne]

open MeasureTheory in
omit hχ in
/-- The Mellin transform of an exponentially decaying profile is integrable on
every vertical line. -/
private lemma verticalIntegrable_logMellin (a : ℝ) :
    Complex.VerticalIntegrable (logMellin f) a := by
  have hΦ : Continuous (logMellin f) := (differentiable_mellin_of_exponentialDecay f hf).continuous
  have hline : Continuous (fun y : ℝ ↦ (a : ℂ) + (y : ℂ) * Complex.I) := by fun_prop
  obtain ⟨C, hC, hBound⟩ :=
    mellin_heightBound_of_exponentialDecay f hf a (a + 1) (by linarith) 2 one_le_two
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-1 : ℝ) 1)
    (hΦ.comp hline).continuousOn
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 ⟨by norm_num, by norm_num⟩)
  refine (integrable_inv_one_add_sq.const_mul (2 * C + 2 * D)).mono'
    (hΦ.comp hline).aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
  have hy2 : (0 : ℝ) < 1 + y ^ 2 := by positivity
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ‖logMellin f ((a : ℂ) + (y : ℂ) * Complex.I)‖ := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by
    rw [hN]
    exact norm_nonneg _
  change ‖logMellin f ((a : ℂ) + (y : ℂ) * Complex.I)‖ ≤ (2 * C + 2 * D) * (1 + y ^ 2)⁻¹
  rw [← hN, ← div_eq_mul_inv, le_div_iff₀ hy2]
  by_cases hy : |y| ≤ 1
  · have h1 : y ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg y) hy
    have h2 : N ≤ D := by
      rw [hN]
      exact hD y (abs_le.mp hy)
    nlinarith [mul_nonneg hN0 (sub_nonneg.mpr h1)]
  · have hy1 : 1 < |y| := not_le.mp hy
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, abs_zero] at hy1
      linarith
    have h1 : 1 ≤ y ^ 2 := by
      rw [← sq_abs]
      exact one_le_pow₀ hy1.le
    have hysq : (0 : ℝ) < y ^ 2 := by positivity
    have h2 : N * y ^ 2 ≤ C := by
      have h := hBound a (left_mem_Icc.mpr (by linarith)) y hy0
      rw [sq_abs] at h
      rw [hN]
      exact (le_div_iff₀ hysq).mp h
    nlinarith [mul_nonneg hN0 (sub_nonneg.mpr h1)]

open MeasureTheory in
/-- Paper: Lemma B.4.1.7, p. 611. The Mellin transform times the logarithmic
derivative of the unramified Euler factor is integrable on the right vertical line. -/
theorem verticalIntegrable_localEulerFactor_mellin (a : ℝ) (ha : 0 < a) :
    Complex.VerticalIntegrable eulerIntegrand a := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = χ₀(χ).localValue v := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = Ideal.absNorm v.asIdeal := ⟨_, rfl⟩
  have hc : ‖c‖ = 1 := by
    rw [hcdef]
    exact norm_ideleClassNormTwist_zero_localValue χ v
  have hq : 1 < q := by
    rw [hqdef]
    exact NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (zero_lt_one.trans hq).ne'
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hEuler : finiteHeckeEulerFactor χ v = fun z : ℂ ↦ (1 - c * (q : ℂ) ^ (-z))⁻¹ := by
    funext z
    rw [finiteHeckeEulerFactor, ite_eq_left hχ, hcdef, hqdef]
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = (q : ℝ) ^ (-a) := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by
    rw [hrdef]
    exact Real.rpow_nonneg (zero_le_one.trans hqR.le) _
  have hr1 : r < 1 := by
    rw [hrdef]
    exact Real.rpow_lt_one_of_one_lt_of_neg hqR (neg_neg_of_pos ha)
  have hre (y : ℝ) : ((a : ℂ) + (y : ℂ) * Complex.I).re = a := by simp
  have hs (y : ℝ) : 0 < ((a : ℂ) + (y : ℂ) * Complex.I).re := by
    rw [hre]
    exact ha
  have hline : Continuous (fun y : ℝ ↦ (a : ℂ) + (y : ℂ) * Complex.I) := by fun_prop
  have hΦint : Integrable (fun y : ℝ ↦ logMellin f ((a : ℂ) + (y : ℂ) * Complex.I)) :=
    verticalIntegrable_logMellin f hf a
  -- The logarithmic derivative of the Euler factor is continuous and bounded on the line.
  have hden (y : ℝ) : 1 - r ≤ ‖1 - c * (q : ℂ) ^ (-((a : ℂ) + (y : ℂ) * Complex.I))‖ := by
    have h := one_sub_le_norm_one_sub_mul_cpow hq hc ((a : ℂ) + (y : ℂ) * Complex.I)
    rwa [hre, ← hrdef] at h
  have hden0 (y : ℝ) : 1 - c * (q : ℂ) ^ (-((a : ℂ) + (y : ℂ) * Complex.I)) ≠ 0 := by
    intro h
    have hle := hden y
    rw [h, norm_zero] at hle
    linarith
  have hpow : Continuous (fun y : ℝ ↦ (q : ℂ) ^ (-((a : ℂ) + (y : ℂ) * Complex.I))) :=
    hline.neg.const_cpow (Or.inl hq0)
  have hLcont : Continuous (fun y : ℝ ↦
      -(c * ((q : ℂ) ^ (-((a : ℂ) + (y : ℂ) * Complex.I)) * Complex.log q)) /
        (1 - c * (q : ℂ) ^ (-((a : ℂ) + (y : ℂ) * Complex.I)))) :=
    ((continuous_const.mul (hpow.mul continuous_const)).neg).div
      (continuous_const.sub (continuous_const.mul hpow)) hden0
  have hLbound (y : ℝ) :
      ‖-(c * ((q : ℂ) ^ (-((a : ℂ) + (y : ℂ) * Complex.I)) * Complex.log q)) /
        (1 - c * (q : ℂ) ^ (-((a : ℂ) + (y : ℂ) * Complex.I)))‖ ≤
        r * ‖Complex.log q‖ / (1 - r) := by
    rw [norm_div, norm_neg, norm_mul, norm_mul, hc, one_mul,
      Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans hq), Complex.neg_re, hre, ← hrdef]
    exact div_le_div_of_nonneg_left (mul_nonneg hr0 (norm_nonneg _)) (sub_pos.mpr hr1) (hden y)
  refine (hΦint.mul_bdd hLcont.aestronglyMeasurable (Eventually.of_forall hLbound)).congr
    (Eventually.of_forall fun y ↦ ?_)
  change _ = logMellin f _ * logDeriv (finiteHeckeEulerFactor χ v) _
  rw [hEuler, logDeriv_inv_one_sub_mul_cpow hq hc (hs y)]

omit hχ hf in
/-- Powers of `q ^ (-s)` are the values at `-s` of the powers of `q`. -/
private lemma natCast_cpow_neg_pow (q : ℕ) (s : ℂ) (n : ℕ) :
    ((q : ℂ) ^ (-s)) ^ n = (((q : ℝ) ^ n : ℝ) : ℂ) ^ (-s) := by
  rw [← Complex.cpow_nat_mul, Complex.natCast_cpow_natCast_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast]

open MeasureTheory in
omit hχ hf in
/-- Termwise integration of the geometric expansion of the logarithmic derivative
of an Euler factor against an integrable function. -/
private lemma hasSum_integral_mul_geometric {Ψ w : ℝ → ℂ} {c L : ℂ} {r : ℝ}
    (hΨ : Integrable Ψ) (hw : Continuous w) (hc : ‖c‖ = 1) (hr : r < 1)
    (hwr : ∀ y, ‖w y‖ = r) :
    HasSum (fun m : ℕ ↦ ∫ y : ℝ, -L * (c ^ (m + 1) * (Ψ y * w y ^ (m + 1))))
      (∫ y : ℝ, Ψ y * (-(c * (w y * L)) / (1 - c * w y))) := by
  have hr0 : 0 ≤ r := by
    rw [← hwr 0]
    exact norm_nonneg _
  have hint (m : ℕ) :
      Integrable (fun y : ℝ ↦ -L * (c ^ (m + 1) * (Ψ y * w y ^ (m + 1)))) := by
    have hbdd : ∀ y : ℝ, ‖w y ^ (m + 1)‖ ≤ r ^ (m + 1) := fun y ↦ by
      rw [norm_pow, hwr]
    exact ((hΨ.mul_bdd (hw.pow _).aestronglyMeasurable
      (Eventually.of_forall hbdd)).const_mul _).const_mul _
  have hnorm (m : ℕ) : (∫ y : ℝ, ‖-L * (c ^ (m + 1) * (Ψ y * w y ^ (m + 1)))‖) =
      ‖L‖ * (∫ y : ℝ, ‖Ψ y‖) * r ^ (m + 1) := by
    have hfun : (fun y : ℝ ↦ ‖-L * (c ^ (m + 1) * (Ψ y * w y ^ (m + 1)))‖) =
        fun y : ℝ ↦ ‖L‖ * r ^ (m + 1) * ‖Ψ y‖ := by
      funext y
      rw [norm_mul, norm_neg, norm_mul, norm_pow, hc, one_pow, one_mul, norm_mul, norm_pow,
        hwr]
      ring
    rw [hfun, integral_const_mul]
    ring
  have hsum : Summable
      (fun m : ℕ ↦ ∫ y : ℝ, ‖-L * (c ^ (m + 1) * (Ψ y * w y ^ (m + 1)))‖) := by
    rw [funext hnorm]
    exact ((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hr0 hr)).mul_left _
  have hpt (y : ℝ) : ∑' m : ℕ, -L * (c ^ (m + 1) * (Ψ y * w y ^ (m + 1))) =
      Ψ y * (-(c * (w y * L)) / (1 - c * w y)) := by
    have hξ : ‖c * w y‖ < 1 := by
      rw [norm_mul, hc, one_mul, hwr]
      exact hr
    have hgeo := (hasSum_geometric_of_norm_lt_one hξ).mul_left (-L * Ψ y * (c * w y))
    have hfun : (fun m : ℕ ↦ -L * (c ^ (m + 1) * (Ψ y * w y ^ (m + 1)))) =
        fun m : ℕ ↦ -L * Ψ y * (c * w y) * (c * w y) ^ m := by
      funext m
      ring
    rw [hfun, hgeo.tsum_eq, div_eq_mul_inv]
    ring
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  rwa [funext hpt] at h

open MeasureTheory in
omit hχ hf in
/-- A value of the inverse Mellin transform read as an integral over the vertical line. -/
private lemma integral_mul_cpow_of_mellinInv_eq {Φ : ℂ → ℂ} {a x : ℝ} {b : ℂ}
    (h : mellinInv a Φ x = b) :
    ∫ y : ℝ, Φ ((a : ℂ) + (y : ℂ) * Complex.I) *
      (x : ℂ) ^ (-((a : ℂ) + (y : ℂ) * Complex.I)) = 2 * (Real.pi : ℂ) * b := by
  have hcomm : (fun y : ℝ ↦ Φ ((a : ℂ) + (y : ℂ) * Complex.I) *
      (x : ℂ) ^ (-((a : ℂ) + (y : ℂ) * Complex.I))) =
      fun y : ℝ ↦ (x : ℂ) ^ (-((a : ℂ) + (y : ℂ) * Complex.I)) •
        Φ ((a : ℂ) + (y : ℂ) * Complex.I) := by
    funext y
    rw [smul_eq_mul, mul_comm]
  have hpi : 2 * (Real.pi : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 := by
    push_cast
    exact mul_one_div_cancel
      (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  rw [hcomm, ← h]
  unfold mellinInv
  rw [Complex.real_smul, ← mul_assoc, hpi, one_mul]

-- TODO(paper-gap): The second equality in (B.4.1.20) and (B.4.1.35) omit
-- the left vertical integral needed for the full residue sum. The right
-- vertical line alone gives only the strictly positive powers of the prime norm.
-- On p. 614 the dropped integral of Φ is 2πi times the test function at one.

open MeasureTheory in
/-- Paper: Lemma B.4.1.7, p. 611. The negative normalized right-line
integral is the logarithm of the norm times the local Dirac sum at weight zero.
Deviation: The single right-line integral in (B.4.1.20) gives only strictly
positive powers, as follows from the Euler expansion (B.4.2.7) and Mellin inversion. -/
theorem hasSum_localEulerFactor_cauchyIntegral (a : ℝ) (ha : 0 < a) :
    HasSum (fun m : ℕ ↦ (Real.log q(v) : ℂ) * (χ₀(χ).localValue v) ^ (m + 1) *
      f ((m + 1 : ℕ) * Real.log q(v))) (-verticalLineIntegral eulerIntegrand a / twoPiI) :=
  by
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = χ₀(χ).localValue v := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = Ideal.absNorm v.asIdeal := ⟨_, rfl⟩
  rw [← hcdef, ← hqdef]
  have hc : ‖c‖ = 1 := by
    rw [hcdef]
    exact norm_ideleClassNormTwist_zero_localValue χ v
  have hq : 1 < q := by
    rw [hqdef]
    exact NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (zero_lt_one.trans hq).ne'
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hEuler : finiteHeckeEulerFactor χ v = fun z : ℂ ↦ (1 - c * (q : ℂ) ^ (-z))⁻¹ := by
    funext z
    rw [finiteHeckeEulerFactor, ite_eq_left hχ, hcdef, hqdef]
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = (q : ℝ) ^ (-a) := ⟨_, rfl⟩
  have hr1 : r < 1 := by
    rw [hrdef]
    exact Real.rpow_lt_one_of_one_lt_of_neg hqR (neg_neg_of_pos ha)
  have hre (y : ℝ) : ((a : ℂ) + (y : ℂ) * Complex.I).re = a := by simp
  have hs (y : ℝ) : 0 < ((a : ℂ) + (y : ℂ) * Complex.I).re := by
    rw [hre]
    exact ha
  have hline : Continuous (fun y : ℝ ↦ (a : ℂ) + (y : ℂ) * Complex.I) := by fun_prop
  have hΦint : Integrable (fun y : ℝ ↦ logMellin f ((a : ℂ) + (y : ℂ) * Complex.I)) :=
    verticalIntegrable_logMellin f hf a
  have hw : Continuous (fun y : ℝ ↦ (q : ℂ) ^ (-((a : ℂ) + (y : ℂ) * Complex.I))) :=
    hline.neg.const_cpow (Or.inl hq0)
  have hwr (y : ℝ) : ‖(q : ℂ) ^ (-((a : ℂ) + (y : ℂ) * Complex.I))‖ = r := by
    rw [Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans hq), Complex.neg_re, hre, ← hrdef]
  -- Expand the logarithmic derivative geometrically and integrate term by term.
  have hS := hasSum_integral_mul_geometric (L := Complex.log q) hΦint hw hc hr1 hwr
  have hlim : (∫ y : ℝ, logMellin f ((a : ℂ) + (y : ℂ) * Complex.I) *
      (-(c * ((q : ℂ) ^ (-((a : ℂ) + (y : ℂ) * Complex.I)) * Complex.log q)) /
        (1 - c * (q : ℂ) ^ (-((a : ℂ) + (y : ℂ) * Complex.I))))) =
      ∫ y : ℝ, eulerIntegrand ((a : ℂ) + (y : ℂ) * Complex.I) := by
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    change _ = logMellin f _ * logDeriv (finiteHeckeEulerFactor χ v) _
    rw [hEuler, logDeriv_inv_one_sub_mul_cpow hq hc (hs y)]
  -- Mellin inversion evaluates each term at a power of the prime norm.
  have hterm (m : ℕ) : (∫ y : ℝ, -Complex.log q * (c ^ (m + 1) *
      (logMellin f ((a : ℂ) + (y : ℂ) * Complex.I) *
        ((q : ℂ) ^ (-((a : ℂ) + (y : ℂ) * Complex.I))) ^ (m + 1)))) =
      -(2 * (Real.pi : ℂ)) *
        ((Real.log q : ℂ) * c ^ (m + 1) * f ((m + 1 : ℕ) * Real.log q)) := by
    have hx : (0 : ℝ) < (q : ℝ) ^ (m + 1) := pow_pos (zero_lt_one.trans hqR) _
    have hinv : mellinInv a (logMellin f) ((q : ℝ) ^ (m + 1)) =
        f (Real.log ((q : ℝ) ^ (m + 1))) :=
      mellinInv_mellin_eq a (fun t : ℝ ↦ f (Real.log t)) hx
        (mellinConvergent_of_exponentialDecay f hf a) hΦint
        (f.continuous.continuousAt.comp (Real.continuousAt_log hx.ne'))
    have hM := integral_mul_cpow_of_mellinInv_eq hinv
    simp_rw [natCast_cpow_neg_pow]
    rw [integral_const_mul, integral_const_mul, hM, Real.log_pow, Complex.natCast_log]
    ring
  rw [hlim, funext hterm] at hS
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  convert hS.mul_left (-(2 * (Real.pi : ℂ))⁻¹) using 1
  · funext m
    rw [← mul_assoc, neg_mul_neg, inv_mul_cancel₀ hpi, one_mul]
  · obtain ⟨J, hJ⟩ : ∃ J : ℂ, J = ∫ y : ℝ, eulerIntegrand ((a : ℂ) + (y : ℂ) * Complex.I) :=
      ⟨_, rfl⟩
    change -(Complex.I * ∫ y : ℝ, eulerIntegrand ((a : ℂ) + (y : ℂ) * Complex.I)) / twoPiI = _
    rw [← hJ, neg_div, mul_comm Complex.I J, mul_div_mul_right _ _ Complex.I_ne_zero, neg_mul,
      inv_mul_eq_div]

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

/-- The products `n * (z - n)` over the integers have summable reciprocals. -/
theorem summable_inv_intCast_mul_sub (z : ℂ) :
    Summable fun n : ℤ ↦ ((n : ℂ) * (z - n))⁻¹ := by
  apply EisensteinSeries.summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_num)
  have h1 : (fun n : ℤ ↦ ((n : ℂ))⁻¹) =O[cofinite] fun n ↦ ((n : ℝ))⁻¹ :=
    Asymptotics.isBigO_of_le _ fun n ↦ by simp
  have h2 : (fun n : ℤ ↦ (z - n)⁻¹) =O[cofinite] fun n ↦ ((n : ℝ))⁻¹ := by
    simpa [sub_eq_add_neg] using (EisensteinSeries.linear_inv_isBigO_right 1 z).comp_neg_int
  refine ((h1.mul h2).trans (Asymptotics.isBigO_of_le _ fun n ↦ ?_)).congr_left fun n ↦ ?_
  · rw [Real.rpow_two, sq_abs, ← mul_inv, ← pow_two]
  · rw [mul_inv]

/-- Each regularized pole term equals `z / (n * (z - n))` off the integers. -/
theorem poleTerm_eq {z : ℂ} (hz : z ∈ Complex.integerComplement) (m : {m : ℤ // m ≠ 0}) :
    poleTerm m z = z * (((m.val : ℤ) : ℂ) * (z - (m.val : ℤ)))⁻¹ := by
  have h1 : ((m.val : ℤ) : ℂ) ≠ 0 := by exact_mod_cast m.2
  have h2 : z - ((m.val : ℤ) : ℂ) ≠ 0 := by
    simpa [sub_eq_add_neg] using Complex.integerComplement_add_ne_zero hz (-m.val)
  simp only
  field_simp
  ring

/-- The regularized pole terms sum to the Mittag-Leffler remainder of `π cot (π z)`. -/
theorem tsum_poleTerm_eq {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    ∑' m, poleTerm m z = Real.pi * Complex.cot (Real.pi * z) - 1 / z := by
  set f : ℤ → ℂ := fun n ↦ z * ((n : ℂ) * (z - n))⁻¹ with hf
  have hs : Summable f := (summable_inv_intCast_mul_sub z).mul_left z
  have hsupp : Function.support f ⊆ {m : ℤ | m ≠ 0} := by
    intro n hn
    by_contra h0
    simp only [Set.mem_ofPred_eq, not_not] at h0
    exact hn (by simp [f, h0])
  have e1 : ∑' m, poleTerm m z = ∑' n : ℤ, f n := by
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    exact tsum_congr fun m ↦ poleTerm_eq hz m
  rw [e1, cot_series_rep' hz]
  have h0 : f 0 = 0 := by simp [f]
  have hnat := hs.hasSum.nat_add_neg
  rw [h0, add_zero] at hnat
  rw [← hnat.tsum_eq]
  have hsn : Summable fun n : ℕ ↦ f n + f (-n) := hnat.summable
  rw [hsn.tsum_eq_zero_add]
  simp only [Nat.cast_zero, neg_zero, h0, add_zero, zero_add]
  refine tsum_congr fun n ↦ ?_
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h2 : z - ((n : ℂ) + 1) ≠ 0 := by
    simpa [sub_eq_add_neg] using Complex.integerComplement_add_ne_zero hz (-((n : ℤ) + 1))
  have h3 : z + ((n : ℂ) + 1) ≠ 0 := by
    simpa using Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
  have h4 : (-((n : ℂ) + 1)) ≠ 0 := neg_ne_zero.mpr hn
  have h5 : z - -((n : ℂ) + 1) ≠ 0 := by rwa [sub_neg_eq_add]
  simp only [f, Nat.cast_succ, Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_neg,
    Int.cast_natCast]
  rw [mul_inv, mul_inv, sub_neg_eq_add]
  field_simp
  ring

/-- Paper: Lemma B.4.1.9, p. 612. The reciprocal of one minus the
exponential has the regularized partial-fraction expansion (B.4.1.21). -/
theorem inv_one_sub_exp_eq_mittagLeffler {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    (1 - Complex.exp (twoPiI * z))⁻¹ =
      1 / 2 - 1 / (twoPiI * z) - (1 / twoPiI) * ∑' m, poleTerm m z := by
  rw [tsum_poleTerm_eq hz, Complex.cot_pi_eq_exp_ratio]
  have hz0 : z ≠ 0 := Complex.integerComplement.ne_zero hz
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have he : 1 - Complex.exp (2 * Real.pi * Complex.I * z) ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (sub_eq_zero.mp h).symm
    apply hz
    refine ⟨n, ?_⟩
    have : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [hπ, Complex.I_ne_zero]
    apply mul_left_cancel₀ this
    rw [hn]; ring
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

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
