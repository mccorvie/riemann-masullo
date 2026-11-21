module

public import Mathlib.Analysis.Complex.IntegerCompl
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import RiemannMasullo.AppB_AnalyticNT.Sec2
public import RiemannMasullo.Ch03_IdelicZeta.Sec2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import RiemannMasullo.ForMathlib.Analysis.MellinTransform

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

/-- Paper: Lemma B.4.1.1, p. 607. The Mellin transform satisfies the bound
(B.4.1.3) of order one over the modulus, uniformly on each bounded-width strip. -/
theorem mellin_inverseNormBound_of_piecewiseSmoothMellinTest
    {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) (a b : ℝ) :
    ∃ C > (0 : ℝ), ∃ R > (0 : ℝ), ∀ s : ℂ, s.re ∈ Icc a b → R < ‖s‖ →
      ‖logMellin f s‖ ≤ C / ‖s‖ := by sorry

/-- Paper: Proposition B.4.1.2, p. 608. At a point with both one-sided limits,
the sample used for Poisson summation is their arithmetic mean. -/
def mellinJumpMidpoint (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (limUnder (𝓝[<] x) f + limUnder (𝓝[>] x) f) / 2

/-- Paper: Proposition B.4.1.2, p. 608. When the two one-sided limits are
given, the midpoint sample is their average.
Deviation: Sanity check for the normalization of the midpoint. -/
theorem mellinJumpMidpoint_eq_average {f : ℝ → ℂ} {x : ℝ} {l r : ℂ}
    (hl : Tendsto f (𝓝[<] x) (𝓝 l)) (hr : Tendsto f (𝓝[>] x) (𝓝 r)) :
    mellinJumpMidpoint f x = (l + r) / 2 := by sorry

/-- Paper: Proposition B.4.1.2, p. 608. The unitary character's weighted
midpoint samples on the multiplicative lattice are absolutely summable.
The value `c` on the generator determines the character. -/
theorem summable_mellinJumpMidpoint_lattice
    {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ ≠ 1) (c : Circle) :
    Summable (fun m : ℤ ↦ (c : ℂ) ^ m * mellinJumpMidpoint f ((m : ℝ) * Real.log θ)) :=
  by sorry

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
    {m : ℤ | mellinJumpMidpoint f ((m : ℝ) * Real.log θ) ≠ f ((m : ℝ) * Real.log θ)}.Finite :=
  by sorry

-- TODO(paper-gap): Footnote 12 asks for a non-absolutely convergent example.
-- The example at θ = 2 has only one nonzero frequency sample.

/-- Paper: Remark B.4.1.4, p. 608. If the test function is globally smooth,
the Mellin samples in the Poisson identity are absolutely summable. -/
theorem summable_mellinPoissonSamples_of_smooth
    {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) (hsmooth : ContDiff ℝ ∞ f)
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ ≠ 1) (c : Circle) (ℓ : ℂ)
    (hℓ : Complex.exp ℓ = (c : ℂ)) :
    Summable (fun m : ℤ ↦
      ‖logMellin f ((ℓ + twoPiI * (m : ℂ)) / (Real.log θ : ℂ))‖) := by sorry

/-- Paper: Remark B.4.1.4, p. 608. The Mellin transform of the indicator of
the interval from one to two is (B.4.1.9), with its removable value at zero. -/
theorem mellin_indicator_one_two (s : ℂ) :
    mellin ((Icc (1 : ℝ) 2).indicator (fun _ ↦ (1 : ℂ))) s =
      if s = 0 then (Real.log 2 : ℂ) else ((2 : ℂ) ^ s - 1) / s := by sorry

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
      (localDiracComb χ v hχ σ f) := by sorry

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
