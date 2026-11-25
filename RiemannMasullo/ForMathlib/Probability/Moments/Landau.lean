module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Landau's theorem for positive measures and signed Laplace transforms

For a nonnegative observable, a finite endpoint of exponential integrability is a real
singularity. The proof expands the transform at an interior point and uses the nonnegative
moment coefficients. For a signed Laplace integral with a meromorphic continuation regular
on the real segment crossed, exponential integrability of either sign suffices for the other.
This applies to the accumulated first-prime error in the rational comparison for Theorem
12.5.1.1 (pp. 519–520) with ordinary Lebesgue measure on the nonnegative half-line.
-/

open Complex Set Filter Metric MeasureTheory ProbabilityTheory
open scoped Topology
@[expose] public noncomputable section
namespace RiemannMasullo

private theorem landauMoment_integrable_of_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : 0 ≤ᵐ[μ] X) {c d : ℝ}
    (hc : c ∈ interior (integrableExpSet X μ)) (hd : 0 ≤ d)
    (hs : Summable fun n : ℕ ↦ (d ^ n / n.factorial) *
      ∫ ω, X ω ^ n * Real.exp (c * X ω) ∂μ) :
    c + d ∈ integrableExpSet X μ := by
  by_cases hμ : μ = 0
  · simp [hμ, integrableExpSet]
  let _ : NeZero μ := ⟨hμ⟩
  let f (n : ℕ) (ω : Ω) := (d ^ n / n.factorial) * (X ω ^ n * Real.exp (c * X ω))
  have hf (n : ℕ) : Integrable (f n) μ :=
    (integrable_pow_mul_exp_of_mem_interior_integrableExpSet hc n).const_mul _
  have hpos (n : ℕ) : 0 ≤ᵐ[μ] f n := by
    filter_upwards [hX] with ω hω
    change 0 ≤ X ω at hω
    dsimp [f]
    positivity
  have hsum : Summable fun n ↦ ∫ ω, ‖f n ω‖ ∂μ := by
    convert hs using 1
    funext n
    rw [← integral_const_mul]
    exact integral_congr_ae <| (hpos n).mono fun ω hω ↦ Real.norm_of_nonneg hω
  have hfull := hasSum_integral_of_summable_integral_norm hf hsum
  have hseries (ω : Ω) : HasSum (fun n ↦ f n ω) (Real.exp ((c + d)*X ω)) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp (d * X ω)).mul_right (Real.exp (c * X ω))
    rw [← Real.exp_eq_exp_ℝ] at h
    rw [add_mul, Real.exp_add, mul_comm]
    convert h using 1
    funext n
    dsimp [f]
    rw [mul_pow]
    ring
  simp_rw [(hseries _).tsum_eq] at hfull
  change Integrable _ _
  apply mgf_pos_iff.mp
  calc
    0 < mgf X μ c := mgf_pos' hμ (interior_subset hc)
    _ = ∫ ω, f 0 ω ∂μ := by simp [mgf, f]
    _ ≤ mgf X μ (c + d) := le_hasSum hfull 0 fun n _ ↦ integral_nonneg_of_ae (hpos n)

/-- An analytic disc centered in the convergence interval of a positive exponential moment
forces convergence at every real point of the disc to the right of the center. -/
theorem landauMoment_integrable_of_analytic_disc {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : 0 ≤ᵐ[μ] X) {c t r : ℝ}
    (hc : c ∈ interior (integrableExpSet X μ)) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball (c : ℂ) r)) (he : F =ᶠ[𝓝 (c : ℂ)] complexMGF X μ)
    (ht : c ≤ t) (hball : (t : ℂ) ∈ ball (c : ℂ) r) :
    t ∈ integrableExpSet X μ := by
  have hc' : (c : ℂ).re ∈ interior (integrableExpSet X μ) := hc
  have hser := (Complex.hasSum_re (Complex.hasSum_taylorSeries_on_ball hF hball)).summable
  have hm (n : ℕ) : iteratedDeriv n F (c : ℂ) =
      ((∫ ω, X ω ^ n * Real.exp (c * X ω) ∂μ : ℝ) : ℂ) := by
    rw [he.iteratedDeriv_eq n, iteratedDeriv_complexMGF hc', ← integral_complex_ofReal]
    congr 1
    funext ω
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp]
  have h := landauMoment_integrable_of_moments hX hc (sub_nonneg.mpr ht) (d := t - c) (by
    convert hser using 1
    funext n
    rw [hm]
    rw [show (n.factorial : ℂ) = ((n.factorial : ℝ) : ℂ) by norm_cast]
    simp only [smul_eq_mul, ← Complex.ofReal_inv, ← Complex.ofReal_sub, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    ring)
  simpa only [add_sub_cancel] using h

/-- Landau's singularity theorem for a nonnegative observable on an arbitrary positive
measure. If the real exponential moments stop at b, no analytic germ at b can agree
with the transform from the convergent side. -/
theorem landauMoment_not_analyticAt_boundary {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : 0 ≤ᵐ[μ] X) {b : ℝ}
    (hin : Iio b ⊆ integrableExpSet X μ) (hout : ∀ t > b, t ∉ integrableExpSet X μ)
    {F : ℂ → ℂ} (he : F =ᶠ[𝓝[{z : ℂ | z.re < b}] (b : ℂ)] complexMGF X μ) :
    ¬ AnalyticAt ℂ F (b : ℂ) := by
  intro hF
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.mp
    (hF.eventually_analyticAt.and (eventually_nhdsWithin_iff.mp he))
  let c := b - r / 4
  let t := b + r / 4
  have hdist (x y : ℝ) : dist (x : ℂ) (y : ℂ) = |x - y| := by
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hcb : c < b := by dsimp [c]; linarith
  have hbt : b < t := by dsimp [t]; linarith
  have hc : dist (c : ℂ) (b : ℂ) = r / 4 := by
    rw [hdist, abs_of_nonpos (sub_nonpos.mpr hcb.le)]
    dsimp [c]
    ring
  have hU : ball (c : ℂ) (3 * r / 4) ⊆ ball (b : ℂ) r := by
    intro z hz
    apply mem_ball.mpr
    calc
      dist z (b : ℂ) ≤ dist z (c : ℂ) + dist (c : ℂ) (b : ℂ) := dist_triangle ..
      _ < r := by rw [hc]; linarith [mem_ball.mp hz]
  have hG : F =ᶠ[𝓝 (c : ℂ)] complexMGF X μ := by
    filter_upwards [isOpen_ball.mem_nhds (show (c : ℂ) ∈ ball (b : ℂ) r from
      mem_ball.mpr (by rw [hc]; linarith)), (isOpen_lt Complex.continuous_re continuous_const).mem_nhds
        (show (c : ℂ).re < b from hcb)] with z hz hz'
    exact (h (mem_ball.mp hz)).2 hz'
  apply hout t hbt
  apply landauMoment_integrable_of_analytic_disc hX (interior_maximal hin isOpen_Iio hcb)
    (fun z hz ↦ (h (mem_ball.mp (hU hz))).1.differentiableAt.differentiableWithinAt) hG
    (hcb.trans hbt).le
  rw [mem_ball, hdist t c, abs_of_nonneg (sub_nonneg.mpr (hcb.trans hbt).le)]
  dsimp [t, c]
  linarith

private theorem landauMoment_germ_left {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {a x b : ℝ} (hax : a ≤ x) (hxb : x < b)
    (hin : Iio x ⊆ integrableExpSet X μ) {F : ℂ → ℂ}
    (hF : MeromorphicOn F {z | z.re < b})
    (he : ∀ z : ℂ, z.re < a → F z = complexMGF X μ z) :
    F =ᶠ[𝓝[{z : ℂ | z.re < x}] (x : ℂ)] complexMGF X μ := by
  let U := {z : ℂ | z.re < x}
  have hA : AnalyticOnNhd ℂ (complexMGF X μ) U := fun z hz ↦
    analyticAt_complexMGF (interior_maximal hin isOpen_Iio hz)
  have hM : MeromorphicOn (F - complexMGF X μ) U :=
    fun z hz ↦ (hF z (lt_trans hz hxb)).sub (hA z hz).meromorphicAt
  let w : ℂ := (a : ℂ) - 1
  have hw : w.re < a := by simp [w]
  have hp : meromorphicOrderAt (F - complexMGF X μ) w = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have h : ∀ᶠ z in 𝓝 w, z.re < a := (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hw
    filter_upwards [h.filter_mono (nhdsWithin_le_nhds (s := {w}ᶜ))] with z hz
    exact sub_eq_zero.mpr (he z hz)
  have hsub : U ⊆ {(x : ℂ)}ᶜ := fun z hz e ↦ by
    change z = x at e
    simp [U, e] at hz
  filter_upwards [((hF x hxb).eventually_analyticAt).filter_mono (nhdsWithin_mono _ hsub),
    self_mem_nhdsWithin] with z hH (hz : z ∈ U)
  have h := meromorphicOrderAt_eq_top_iff.mp
    (hM.meromorphicOrderAt_eq_top_of_isPreconnected (convex_halfSpace_re_lt x).isPreconnected
      (hw.trans_le hax) hz hp)
  have hh : F =ᶠ[𝓝[≠] z] complexMGF X μ := h.mono fun _ e ↦ sub_eq_zero.mp e
  exact tendsto_nhds_unique_of_eventuallyEq hH.continuousAt.continuousWithinAt
    (hA _ hz).continuousAt.continuousWithinAt hh

/-- A meromorphic continuation of a positive exponential moment, regular at the real
points it crosses, forces absolute convergence throughout the open half-plane. -/
theorem landauMoment_integrable_of_real_regular {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : 0 ≤ᵐ[μ] X) {a b : ℝ}
    (hstart : Iio a ⊆ integrableExpSet X μ) {F : ℂ → ℂ}
    (hF : MeromorphicOn F {z | z.re < b}) (he : ∀ z : ℂ, z.re < a → F z = complexMGF X μ z)
    (hreal : ∀ u : ℝ, a ≤ u → u < b → AnalyticAt ℂ F (u : ℂ)) :
    Iio b ⊆ integrableExpSet X μ := by
  let E := integrableExpSet X μ
  have hbase : a - 1 < a := by linarith
  have hne : E.Nonempty := ⟨a - 1, hstart hbase⟩
  have hXm := aemeasurable_of_mem_interior_integrableExpSet (interior_maximal hstart isOpen_Iio hbase)
  have hdown {u v : ℝ} (huv : u ≤ v) (hv : v ∈ E) : u ∈ E := by
    apply (integrable_of_mem_integrableExpSet hv).mono'
      (Real.measurable_exp.comp_aemeasurable (hXm.const_mul u)).aestronglyMeasurable
    filter_upwards [hX] with ω hω
    change ‖Real.exp (u * X ω)‖ ≤ Real.exp (v * X ω)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right huv hω)
  intro t ht
  change t < b at ht
  by_contra hfail
  have hupper : t ∈ upperBounds E := fun v hv ↦ le_of_not_gt (fun h ↦ hfail (hdown h.le hv))
  have hbdd : BddAbove E := ⟨t, hupper⟩
  let x := sSup E
  have hxb : x < b := (csSup_le hne hupper).trans_lt ht
  have hax : a ≤ x := by
    by_contra! h
    obtain ⟨v,hv,hv'⟩ := exists_between h
    exact hv.not_ge (le_csSup hbdd (hstart hv'))
  have hin : Iio x ⊆ E := by
    intro v hv
    obtain ⟨u, hu, hvu⟩ := exists_lt_of_lt_csSup hne hv
    exact hdown hvu.le hu
  have hout (u : ℝ) (hu : x < u) : u ∉ E := fun hh ↦ hu.not_ge (le_csSup hbdd hh)
  exact landauMoment_not_analyticAt_boundary hX hin hout (landauMoment_germ_left hax hxb hin hF he)
    (hreal x hax hxb)

/-- If the difference of two positive transforms admits a meromorphic continuation
regular at every real point crossed, convergence of the first throughout the larger
half-plane forces convergence of the second. Their difference then gives a holomorphic
representative of the original signed transform on the whole half-plane. -/
theorem landauMoment_signed_extension {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ}
    (hY : 0 ≤ᵐ[ν] Y) {a b : ℝ} (hμ : Iio b ⊆ integrableExpSet X μ)
    (hν : Iio a ⊆ integrableExpSet Y ν) {F : ℂ → ℂ}
    (hF : MeromorphicOn F {z | z.re < b})
    (he : ∀ z : ℂ, z.re < a → F z = complexMGF X μ z - complexMGF Y ν z)
    (hreal : ∀ u : ℝ, a ≤ u → u < b → AnalyticAt ℂ F (u : ℂ)) :
    Iio b ⊆ integrableExpSet Y ν ∧
      AnalyticOnNhd ℂ (complexMGF X μ - complexMGF Y ν) {z | z.re < b} := by
  have hA : AnalyticOnNhd ℂ (complexMGF X μ) {z : ℂ | z.re < b} :=
    fun z hz ↦ analyticAt_complexMGF (interior_maximal hμ isOpen_Iio hz)
  have hB : Iio b ⊆ integrableExpSet Y ν :=
    landauMoment_integrable_of_real_regular hY hν (F := complexMGF X μ - F)
      (fun z hz ↦ (hA z hz).meromorphicAt.sub (hF z hz))
      (fun z hz ↦ by simp [he z hz]) (fun u hu hu' ↦ (hA u hu').sub (hreal u hu hu'))
  exact ⟨hB, hA.sub (fun z hz ↦ analyticAt_complexMGF (interior_maximal hB isOpen_Iio hz))⟩

private theorem landauLaplace_density_mem {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (T : Ω → ℝ) {g : Ω → ℝ} (hg : Measurable g) (u : ℝ) :
    u ∈ integrableExpSet T (μ.withDensity fun ω ↦ (g ω).toNNReal) ↔
      Integrable (fun ω ↦ max (g ω) 0 * Real.exp (u * T ω)) μ := by
  change Integrable _ _ ↔ _
  rw [integrable_withDensity_iff_integrable_coe_smul hg.real_toNNReal]
  simp only [Real.coe_toNNReal', smul_eq_mul]

private theorem landauLaplace_density_sub {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T f : Ω → ℝ} (hT : Measurable T) (hf : Measurable f) (z : ℂ)
    (hp : (-z).re ∈ integrableExpSet T (μ.withDensity fun ω ↦ (f ω).toNNReal))
    (hn : (-z).re ∈ integrableExpSet T (μ.withDensity fun ω ↦ (-f ω).toNNReal)) :
    (∫ ω, (f ω : ℂ) * Complex.exp (-z * T ω) ∂μ) =
      complexMGF T (μ.withDensity fun ω ↦ (f ω).toNNReal) (-z) -
      complexMGF T (μ.withDensity fun ω ↦ (-f ω).toNNReal) (-z) := by
  have hInt (g : Ω → ℝ) (hg : Measurable g)
      (hi : (-z).re ∈ integrableExpSet T (μ.withDensity fun ω ↦ (g ω).toNNReal)) :
      Integrable (fun ω ↦ (g ω).toNNReal • Complex.exp (-z * T ω)) μ :=
    (integrable_withDensity_iff_integrable_smul hg.real_toNNReal).mp
      (integrable_cexp_mul_of_re_mem_integrableExpSet hT.aemeasurable hi)
  have hnf : Measurable (fun ω ↦ -f ω) := hf.neg
  rw [complexMGF, complexMGF, integral_withDensity_eq_integral_smul hf.real_toNNReal,
    integral_withDensity_eq_integral_smul hnf.real_toNNReal,
    ← integral_sub (hInt f hf hp) (hInt _ hnf hn)]
  apply integral_congr_ae
  filter_upwards with ω
  change (f ω : ℂ) * _ = ((f ω).toNNReal : ℂ) * _ - ((-f ω).toNNReal : ℂ) * _
  rw [← sub_mul]
  congr 1
  change (f ω : ℂ) = (((f ω).toNNReal : ℝ) : ℂ) - (((-f ω).toNNReal : ℝ) : ℂ)
  norm_cast
  simp [Real.coe_toNNReal', max_zero_sub_max_neg_zero_eq_self]

/-- One-sided Landau criterion for the ordinary Laplace integral of a signed real
density. Integrability of its positive part on the larger half-plane suffices for
absolute integrability of both signs and analyticity of the actual integral there,
provided the signed continuation is regular on the real segment crossed. Taking
the negative of the density gives the same test for its negative part. -/
theorem landauLaplace_one_sided {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T f : Ω → ℝ} (hT : Measurable T) (hT0 : 0 ≤ᵐ[μ] T) (hf : Measurable f)
    {b B : ℝ} (hbB : b ≤ B)
    (hpos : ∀ d > b, Integrable (fun ω ↦ max (f ω) 0 * Real.exp (-d * T ω)) μ)
    (hneg : ∀ d > B, Integrable (fun ω ↦ max (-f ω) 0 * Real.exp (-d * T ω)) μ)
    {F : ℂ → ℂ} (hm : MeromorphicOn F {z | b < z.re})
    (he : ∀ z : ℂ, B < z.re → F z = ∫ ω, (f ω : ℂ) * Complex.exp (-z * T ω) ∂μ)
    (hr : ∀ x : ℝ, b < x → x ≤ B → AnalyticAt ℂ F (x : ℂ)) :
    (∀ d > b, Integrable (fun ω ↦ max (-f ω) 0 * Real.exp (-d * T ω)) μ) ∧
      AnalyticOnNhd ℂ (fun z ↦ ∫ ω, (f ω : ℂ) * Complex.exp (-z * T ω) ∂μ)
        {z | b < z.re} := by
  let P := μ.withDensity fun ω ↦ (f ω).toNNReal
  let N := μ.withDensity fun ω ↦ (-f ω).toNNReal
  have hP : Iio (-b) ⊆ integrableExpSet T P := by
    intro u hu
    change u < -b at hu
    exact (landauLaplace_density_mem T hf u).2 (by simpa using hpos (-u) (by linarith))
  have hN : Iio (-B) ⊆ integrableExpSet T N := by
    intro u hu
    change u < -B at hu
    exact (landauLaplace_density_mem T hf.neg u).2 (by simpa using hneg (-u) (by linarith))
  have hN0 : 0 ≤ᵐ[N] T := hT0.filter_mono (withDensity_absolutelyContinuous _ _).ae_le
  obtain ⟨hN', hA⟩ := landauMoment_signed_extension hN0 hP hN (F := fun z ↦ F (-z))
    (fun z hz ↦ by
      change z.re < -b at hz
      have hz' : b < (-z).re := by change b < -z.re; linarith
      exact (hm (-z) hz').comp_analyticAt (g := fun w : ℂ ↦ -w) (by fun_prop))
    (fun z hz ↦ by
      rw [he (-z) (by change _ < -z.re; linarith)]
      simpa using landauLaplace_density_sub hT hf (-z) (by simpa using hP (hz.trans_le (neg_le_neg hbB)))
        (by simpa using hN hz))
    (fun u hu hu' ↦ by
      have ha := hr (-u) (by linarith) (by linarith)
      rw [Complex.ofReal_neg] at ha
      exact ha.comp (show AnalyticAt ℂ (fun z : ℂ ↦ -z) (u : ℂ) by fun_prop))
  constructor
  · exact fun d hd ↦ (landauLaplace_density_mem T hf.neg (-d)).1 (hN' (neg_lt_neg hd))
  · intro z hz
    change b < z.re at hz
    have hloc : -z ∈ {w : ℂ | w.re < -b} := by simpa using neg_lt_neg hz
    have h := (hA (-z) hloc).comp (show AnalyticAt ℂ (fun w : ℂ ↦ -w) z by fun_prop)
    apply h.congr
    have hnear : ∀ᶠ w in 𝓝 z, b < w.re := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    filter_upwards [hnear] with w hw
    have hw' : (-w).re < -b := neg_lt_neg hw
    exact (landauLaplace_density_sub hT hf w (hP hw') (hN' hw')).symm

/-- Suppose a signed Laplace integral converges on a smaller half-plane and has a
meromorphic continuation regular on the real segment crossed. Exponential integrability
on the larger half-plane is then equivalent for the two signs of the density. -/
theorem landauLaplace_pos_iff_neg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T f : Ω → ℝ} (hT : Measurable T) (hT0 : 0 ≤ᵐ[μ] T) (hf : Measurable f)
    {b B : ℝ} (hbB : b ≤ B)
    (hstart : ∀ d > B, Integrable (fun ω ↦ f ω * Real.exp (-d * T ω)) μ)
    {F : ℂ → ℂ} (hm : MeromorphicOn F {z | b < z.re})
    (he : ∀ z : ℂ, B < z.re → F z = ∫ ω, (f ω : ℂ) * Complex.exp (-z * T ω) ∂μ)
    (hr : ∀ x : ℝ, b < x → x ≤ B → AnalyticAt ℂ F (x : ℂ)) :
    (∀ d > b, Integrable (fun ω ↦ max (f ω) 0 * Real.exp (-d * T ω)) μ) ↔
      ∀ d > b, Integrable (fun ω ↦ max (-f ω) 0 * Real.exp (-d * T ω)) μ := by
  have hp {g : Ω → ℝ} {d : ℝ} (h : Integrable (fun ω ↦ g ω * Real.exp (-d * T ω)) μ) :
      Integrable (fun ω ↦ max (g ω) 0 * Real.exp (-d * T ω)) μ := by
    have hm := h.sup (show Integrable (0 : Ω → ℝ) μ from integrable_zero ..)
    change Integrable (fun ω ↦ max (g ω * Real.exp (-d * T ω)) 0) μ at hm
    simpa only [max_mul_of_nonneg _ _ (Real.exp_pos _).le, zero_mul] using hm
  constructor
  · intro hpos
    apply (landauLaplace_one_sided hT hT0 hf hbB hpos ?_ hm he hr).1
    intro d hd
    apply hp (g := fun ω ↦ -f ω)
    simpa using (hstart d hd).neg
  · intro hneg
    have hn : Measurable (fun ω ↦ -f ω) := hf.neg
    have h := landauLaplace_one_sided hT hT0 hn hbB hneg (fun d hd ↦ by simpa using hp (hstart d hd))
      (F := -F) (fun z hz ↦ (hm z hz).neg)
      (fun z hz ↦ by simp [he z hz, ← integral_neg]) (fun x ha hb ↦ (hr x ha hb).neg)
    simpa using h.1

end RiemannMasullo
