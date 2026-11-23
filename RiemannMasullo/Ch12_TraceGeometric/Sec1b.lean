module

public import RiemannMasullo.Ch12_TraceGeometric.Sec1a
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3b

/-!
# Localization along the global diagonal

Masullo, Theorem 12.1.1.3 and Remark 12.1.1.4, pp. 502–504. The product averages
use Haar measure and a chosen Borel D′-sequence on the idele class group. The
operators whose traces are computed act on the weighted Sobolev space.

The kernels are those of Definition 10.4.3.2, the case `I = {0}`, which in Lean
are `globalLineSpectralKernel` and `globalLineGeometricKernel`: they belong to
spectral projection after convolution, `P^spec_a ∘ A(φ)`, the operator of
(12.1.1.21). The strip kernels of Definition 10.4.3.7 belong to convolution after
projection and are not used here.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 900000

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "W(" s ")" => CompactIntervalSobolev μ𝔽 logNorm (-(0 : ℝ)) 0 s
local notation "hline" => (le_refl (0 : ℝ))
local notation "hbase" => ((neg_nonpos.mpr hline).trans hline)
local notation "hs₀(" hs ")" => (le_trans (by norm_num : (0 : ℝ) ≤ 3) hs)
local notation "hs₁(" hs ")" => (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hs)
local notation "convKernel(" φ ")" =>
  (fun p : C𝔽 × C𝔽 ↦ (φ : BruhatCompactSupport C𝔽).val (p.1 * p.2⁻¹))
local notation "innerBand(" Λ ", " ε ")" => (0 < Λ⁻¹ + ε ∧ Λ⁻¹ + ε < Λ - ε)

-- TODO(paper-gap): The printed standard sequence on the idele class group
-- need not shrink to the identity. Use a Borel D′-sequence as in §12.1a.
variable {U : ℕ → Set (IdeleClassGroup (𝓞 F) F)}
  (hU : IsDPrimeSequence (ideleClassTamagawaMeasure F) U) (hBorel : ∀ n, MeasurableSet (U n))

local notation "regular(" k ")" =>
  dSequenceRegularSet ((μ𝔽).prod μ𝔽) (fun n ↦ U n ×ˢ U n) k
local notation "diagonal(" k ")" => (fun x ↦ dSequenceKernelSmoothening μ𝔽 U k (x, x))

include hU hBorel

omit hU hBorel in
open scoped Pointwise ENNReal in
/-- The convolution kernel is eventually integrable on the averaging neighborhoods,
and its averages on the diagonal converge to the test value at the identity. -/
private theorem diagonal_mem_convolutionKernelRegularSet_averages
    {F : Type*} [Field F] [NumberField F]
    {U : ℕ → Set (IdeleClassGroup (𝓞 F) F)}
    (hU : IsDPrimeSequence (ideleClassTamagawaMeasure F) U)
    (hBorel : ∀ n, MeasurableSet (U n))
    (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))
    (x : IdeleClassGroup (𝓞 F) F) :
    (∀ᶠ n in atTop, IntegrableOn
      (fun p : (IdeleClassGroup (𝓞 F) F) × (IdeleClassGroup (𝓞 F) F) ↦ φ.val (p.1 * p.2⁻¹))
      ((x, x) • (U n ×ˢ U n))
      ((ideleClassTamagawaMeasure F).prod (ideleClassTamagawaMeasure F))) ∧
      Tendsto (fun n ↦ dSequenceAverage
        ((ideleClassTamagawaMeasure F).prod (ideleClassTamagawaMeasure F)) (U n ×ˢ U n)
        (fun p : (IdeleClassGroup (𝓞 F) F) × (IdeleClassGroup (𝓞 F) F) ↦ φ.val (p.1 * p.2⁻¹))
        (x, x)) atTop (𝓝 (φ.val 1)) := by
  let G := IdeleClassGroup (𝓞 F) F
  let μ : Measure G := ideleClassTamagawaMeasure F
  let f : G × G → ℂ := fun p ↦ φ.val (p.1 * p.2⁻¹)
  have hc : Continuous φ.val :=
    schwartzBruhat_continuous
      (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat G)
  have hg : Continuous f := hc.comp (continuous_fst.mul continuous_snd.inv)
  have rectSeq [m : MeasurableSpace (G × G)] (hm : m = borel _)
      (η : Measure (G × G)) [η.IsHaarMeasure]
      (hrect : ∀ v w : Set G, MeasurableSet v → MeasurableSet w →
        η (v ×ˢ w) = μ v * μ w) :
      IsDPrimeSequence η (fun n ↦ U n ×ˢ U n) := by
    subst m
    exact IsDPrimeSequence.prod hrect hU hU
  have hseq : IsDPrimeSequence (μ.prod μ) (fun n ↦ U n ×ˢ U n) :=
    rectSeq BorelSpace.measurable_eq _ (fun v w _ _ ↦ Measure.prod_prod v w)
  have hshrink {W : Set (G × G)} (hW : W ∈ 𝓝 (x, x)) :
      ∀ᶠ n in atTop, (x, x) • (U n ×ˢ U n) ⊆ W := by
    have hpre : (fun y : G × G ↦ (x, x) * y) ⁻¹' W ∈ 𝓝 1 :=
      (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW)
    obtain ⟨N, hN⟩ := hseq.2 _ hpre
    filter_upwards [eventually_ge_atTop N] with n hn
    exact Set.smul_set_subset_iff.mpr fun _ hy ↦ hN (hseq.1.2.1 hn hy)
  obtain ⟨W, hW, hiW⟩ := hg.locallyIntegrable (μ := μ.prod μ) (x, x)
  have hint : ∀ᶠ n in atTop,
      IntegrableOn f ((x, x) • (U n ×ˢ U n)) (μ.prod μ) :=
    (hshrink hW).mono fun _ hn ↦ hiW.mono_set hn
  refine ⟨hint, ?_⟩
  have hvalue : f (x, x) = φ.val 1 := congrArg φ.val (mul_inv_cancel x)
  rw [← hvalue]
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have hnear : f ⁻¹' Metric.ball (f (x, x)) (ε / 2) ∈
      𝓝 (x, x) :=
    hg.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hε))
  filter_upwards [hshrink hnear, hint] with n hn hi
  let S := (x, x) • (U n ×ˢ U n)
  have hzero : (μ.prod μ) S ≠ 0 := by
    simpa only [S, measure_smul] using (hseq.1.1 n).2.2.1.ne'
  have hfin : (μ.prod μ) S ≠ ∞ := by
    simpa only [S, measure_smul] using (hseq.1.1 n).2.2.2.ne
  have havg : (⨍ y in S, f y - f (x, x) ∂(μ.prod μ)) =
      dSequenceAverage (μ.prod μ) (U n ×ˢ U n) f (x, x) -
        f (x, x) := by
    change (⨍ y in S, f y - f (x, x) ∂(μ.prod μ)) =
      (⨍ y in S, f y ∂(μ.prod μ)) - f (x, x)
    rw [setAverage_fun_sub hi (integrableOn_const (C := f (x, x)) hfin),
      setAverage_const hzero hfin]
  rw [dist_eq_norm, ← ENNReal.ofReal_lt_ofReal_iff hε, ofReal_norm, ← havg]
  calc
    ‖⨍ y in S, f y - f (x, x) ∂(μ.prod μ)‖ₑ ≤
        ⨍⁻ y in S, ‖f y - f (x, x)‖ₑ ∂(μ.prod μ) := by
      rw [setAverage_eq', setLAverage_eq']
      exact eNorm_integral_le_lintegral_eNorm _
    _ ≤ ⨍⁻ _ in S, ENNReal.ofReal (ε / 2) ∂(μ.prod μ) := by
      rw [setLAverage_eq', setLAverage_eq']
      apply lintegral_mono_ae
      have hS := (ae_restrict_mem (μ := μ.prod μ)
        (((hBorel n).prod (hBorel n)).const_smul (x, x))).filter_mono
        (Measure.ae_smul_measure_le ((μ.prod μ) S)⁻¹)
      filter_upwards [hS] with y hy
      have hy' : dist (f y) (f (x, x)) < ε / 2 := hn hy
      rw [← ofReal_norm, ← dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal hy'.le
    _ < ENNReal.ofReal ε := by
      rw [setLAverage_const hzero hfin, ENNReal.ofReal_lt_ofReal_iff hε]
      exact half_lt_self hε

/-- Paper: Theorem 12.1.1.3(1), p. 502. The diagonal points of the convolution
kernel are regular for the Haar product averages.
Deviation: A valid Borel D′-sequence is explicit throughout. -/
theorem diagonal_mem_convolutionKernelRegularSet (φ : BruhatCompactSupport C𝔽) (x : C𝔽) :
    (x, x) ∈ regular(convKernel(φ)) := by
  exact ⟨φ.val 1, (diagonal_mem_convolutionKernelRegularSet_averages hU hBorel φ x).2⟩

section GlobalKernels

variable (a : ℝ) {s : ℝ} (hs : 3 ≤ s)
  (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))

local notation "Tspec" => (spectralProjection (F := F) a hline hs₀(hs)).comp
  (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ hbase hs₀(hs) φ)
local notation "Tgeom(" hρ ")" => geometricTruncatedConvolution (F := F) a hline hs₀(hs) hρ φ

local notation "kspec" =>
  (globalLineSpectralKernel (F := F) a hs₁(hs) φ : C𝔽 × C𝔽 → ℂ)
local notation "kgeom" => globalLineGeometricKernel (F := F) a hs₁(hs) φ

-- TODO(paper-gap): On p. 503 the proof applies the weighted L² trace theorem
-- to the Haar kernels directly. The actual Hilbert-Schmidt representatives
-- in Theorem 10.4.3.4 carry the reciprocal input weight. Its effect on the
-- diagonal smoothening must be justified for Haar-almost every center.

/-- Paper: Theorem 12.1.1.3(1), p. 502. The diagonal of the global spectral
kernel is regular for Haar-almost every center.
Deviation: The kernel is the mixed-weight class of Definition 10.4.3.2 in Lean,
whose Haar integral gives spectral projection after convolution. Regularity does
not depend on the representative of that class. -/
theorem ae_diagonal_mem_globalLineSpectralKernelRegularSet (_ha : 0 < a) :
    ∀ᵐ x ∂μ𝔽, (x, x) ∈ regular(kspec) := by sorry

/-- Paper: Theorem 12.1.1.3(1), p. 502. The diagonal of the global geometric
kernel is regular for Haar-almost every center. -/
theorem ae_diagonal_mem_globalLineGeometricKernelRegularSet (_ha : 0 < a) :
    ∀ᵐ x ∂μ𝔽, (x, x) ∈ regular(kgeom) := by sorry

/-- Paper: Theorem 12.1.1.3(2), p. 502. In (12.1.1.20), geometric
truncation after convolution is trace class. Its trace is the Haar integral
of the cutoff times the smoothened geometric diagonal.
Deviation: The cutoff is any real cutoff of Definition 9.3.3.1, smooth or not,
as Theorem 12.1.1.2(2) allows bounded symbols; this is the form the limit
(12.1.1.22) and the sharp band of Remark 12.1.1.4 use. Absolute integrability
of the trace integrand is explicit. -/
theorem geometricTruncatedConvolution_trace_eq_integral_globalDiagonal (_ha : 0 < a)
    {Λ ε : ℝ} {ρ : C𝔽 → ℝ} (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (_hband : innerBand(Λ, ε)) :
    let T := Tgeom(hρ)
    ∃ hT : IsNuclearOperator T,
      Integrable (fun x ↦ (ρ x : ℂ) * diagonal(kgeom) x) μ𝔽 ∧
      hilbertTrace (H := W(s)) ⟨T, hT⟩ =
        ∫ x, (ρ x : ℂ) * diagonal(kgeom) x ∂μ𝔽 := by sorry

/-- Paper: Theorem 12.1.1.3(2), p. 503. In (12.1.1.21), spectral
projection after convolution is trace class. Its trace is the Haar integral
of the smoothened spectral diagonal.
Deviation: Absolute integrability of the smoothened diagonal is explicit. -/
theorem spectralProjection_convolution_trace_eq_integral_globalDiagonal (_ha : 0 < a) :
    let T := Tspec
    ∃ hT : IsNuclearOperator T,
      Integrable diagonal(kspec) μ𝔽 ∧
      hilbertTrace (H := W(s)) ⟨T, hT⟩ = ∫ x, diagonal(kspec) x ∂μ𝔽 := by sorry

-- TODO(paper-gap): The citation of Theorem 10.4.3.1(4) for integrability
-- points to an enumeration condition. Theorem 10.4.3.4(4), cited in the
-- following remark for the same assertion, has no part (4).

omit hU hBorel in
open scoped Pointwise in
/-- When the convolution part has zero diagonal average, the geometric and spectral
smoothenings are opposite, including at irregular points where both are defined to be zero. -/
private theorem integrable_globalLineGeometricKernel_diagonal_eq_neg_spectral
    {F : Type*} [Field F] [NumberField F]
    {U : ℕ → Set (IdeleClassGroup (𝓞 F) F)}
    (hU : IsDPrimeSequence (ideleClassTamagawaMeasure F) U)
    (hBorel : ∀ n, MeasurableSet (U n))
    (a : ℝ) {s : ℝ} (hs : 3 ≤ s)
    (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))
    (hφ : φ.val 1 = 0) (x : IdeleClassGroup (𝓞 F) F) :
    dSequenceKernelSmoothening (ideleClassTamagawaMeasure F) U
      (globalLineGeometricKernel (F := F) a hs₁(hs) φ) (x, x) =
      -dSequenceKernelSmoothening (ideleClassTamagawaMeasure F) U
        (globalLineSpectralKernel (F := F) a hs₁(hs) φ :
          (IdeleClassGroup (𝓞 F) F) × (IdeleClassGroup (𝓞 F) F) → ℂ) (x, x) := by
  classical
  let G := IdeleClassGroup (𝓞 F) F
  let μ : Measure (G × G) :=
    (ideleClassTamagawaMeasure F).prod (ideleClassTamagawaMeasure F)
  let V : ℕ → Set (G × G) := fun n ↦ U n ×ˢ U n
  let f : G × G → ℂ := fun y ↦ φ.val (y.1 * y.2⁻¹)
  let g : G × G → ℂ := globalLineSpectralKernel (F := F) a hs₁(hs) φ
  let p : G × G := (x, x)
  change dSequenceSmootheningOrZero μ V (fun y ↦ f y - g y) p =
    -dSequenceSmootheningOrZero μ V g p
  obtain ⟨hf, hlim⟩ := diagonal_mem_convolutionKernelRegularSet_averages hU hBorel φ x
  change ∀ᶠ n in atTop, IntegrableOn f (p • V n) μ at hf
  change Tendsto (fun n ↦ dSequenceAverage μ (V n) f p) atTop (𝓝 (φ.val 1)) at hlim
  rw [hφ] at hlim
  have hsum : Tendsto (fun n ↦
      dSequenceAverage μ (V n) (fun y ↦ f y - g y) p +
        dSequenceAverage μ (V n) g p) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa only [norm_zero] using hlim.norm)
    filter_upwards [hf] with n hn
    by_cases hg : IntegrableOn g (p • V n) μ
    · change ‖(⨍ y in p • V n, f y - g y ∂μ) +
          (⨍ y in p • V n, g y ∂μ)‖ ≤ ‖⨍ y in p • V n, f y ∂μ‖
      rw [setAverage_fun_sub hn hg, sub_add_cancel]
    · -- If the spectral integral is undefined, both totalized averages vanish.
      have hfg : ¬ IntegrableOn (fun y ↦ f y - g y) (p • V n) μ := by
        intro h
        apply hg
        simpa only [Pi.sub_def, sub_sub_cancel] using hn.sub h
      have hzero : dSequenceAverage μ (V n) g p = 0 := by
        rw [dSequenceAverage, setAverage_eq, integral_undef hg, smul_zero]
      have hsubzero : dSequenceAverage μ (V n) (fun y ↦ f y - g y) p = 0 := by
        rw [dSequenceAverage, setAverage_eq, integral_undef hfg, smul_zero]
      rw [hzero, hsubzero, zero_add, norm_zero]
      exact norm_nonneg _
  by_cases hg : p ∈ dSequenceRegularSet μ V g
  · obtain ⟨v, hv⟩ := hg
    have hgreg : p ∈ dSequenceRegularSet μ V g := ⟨v, hv⟩
    have hsub : Tendsto (fun n ↦ dSequenceAverage μ (V n) (fun y ↦ f y - g y) p)
        atTop (𝓝 (-v)) := by
      simpa only [add_sub_cancel_right, zero_sub] using hsum.sub hv
    have hreg : p ∈ dSequenceRegularSet μ V (fun y ↦ f y - g y) := ⟨-v, hsub⟩
    simp only [dSequenceSmootheningOrZero, dite_eq_left hreg, dite_eq_left hgreg,
      dSequenceSmoothening, hsub.limUnder_eq, hv.limUnder_eq]
  · have hreg : p ∉ dSequenceRegularSet μ V (fun y ↦ f y - g y) := by
      rintro ⟨v, hv⟩
      apply hg
      refine ⟨-v, ?_⟩
      simpa only [add_sub_cancel_left, zero_sub] using hsum.sub hv
    simp only [dSequenceSmootheningOrZero, dite_eq_right hreg, dite_eq_right hg, neg_zero]

/-- Paper: Theorem 12.1.1.3(3), p. 503. When the test vanishes at the
identity, the smoothened geometric diagonal is absolutely Haar integrable. -/
theorem integrable_globalLineGeometricKernel_diagonal (_ha : 0 < a) (_hφ : φ.val 1 = 0) :
    Integrable diagonal(kgeom) μ𝔽 := by
  obtain ⟨_, hi, _⟩ :=
    spectralProjection_convolution_trace_eq_integral_globalDiagonal hU hBorel a hs φ _ha
  have heq : diagonal(kgeom) = fun x ↦ -diagonal(kspec) x := by
    funext x
    exact integrable_globalLineGeometricKernel_diagonal_eq_neg_spectral hU hBorel a hs φ _hφ x
  rw [heq]
  exact hi.neg

/-- Paper: Theorem 12.1.1.3(3), p. 503. In (12.1.1.22), as the radius
tends to infinity and the width times the radius tends to zero, the
geometric truncation traces tend to the Haar mass of the smoothened diagonal.
Deviation: A filter represents the joint limit, with real cutoffs and their
traces specified eventually. The same limit holds for the sharp band in
Remark 12.1.1.4. -/
theorem geometricTruncatedConvolution_trace_tendsto_integral_globalDiagonal (_ha : 0 < a)
    (_hφ : φ.val 1 = 0) {ι : Type*} {l : Filter ι} (Λ ε : ι → ℝ) (ρ : ι → C𝔽 → ℝ)
    (_hΛ : Tendsto Λ l atTop) (_hε : Tendsto (fun i ↦ ε i * Λ i) l (𝓝 0))
    (_hρ : ∀ᶠ i in l, IsModulatedCutoff m𝔽 (Λ i) (ε i) (ρ i) ∧ innerBand(Λ i, ε i)) :
    ∃ traces : ι → ℂ,
      (∀ᶠ i in l, ∃ hcut : IsModulatedCutoff m𝔽 (Λ i) (ε i) (ρ i),
        let T := Tgeom(hcut)
        ∃ hT : IsNuclearOperator T, traces i = hilbertTrace (H := W(s)) ⟨T, hT⟩) ∧
      Tendsto traces l (𝓝 (∫ x, diagonal(kgeom) x ∂μ𝔽)) := by sorry

/-- Paper: (12.1.1.23), p. 503. If the test vanishes at the identity, the
smoothened geometric diagonal is the negative of the spectral diagonal.
The smoothening uses the zero extension from Definition 12.1.1.1. -/
theorem globalLineGeometricKernel_diagonal_eq_neg_spectral (_hφ : φ.val 1 = 0) (x : C𝔽) :
    diagonal(kgeom) x = -diagonal(kspec) x := by
  exact integrable_globalLineGeometricKernel_diagonal_eq_neg_spectral hU hBorel a hs φ _hφ x

/-- Paper: (12.1.1.24), p. 503. If the test vanishes at the identity, the
cutoff integrals of the smoothened geometric diagonal converge to its full Haar integral.
Deviation: A filter expresses the joint limit for the radius and width. The
plateau estimate also applies to the two-sided absolute cutoff of Remark 12.1.1.4. -/
theorem tendsto_integral_cutoff_globalLineGeometricKernel_diagonal (_ha : 0 < a)
    (_hφ : φ.val 1 = 0) {ι : Type*} {l : Filter ι} (Λ ε : ι → ℝ) (ρ : ι → C𝔽 → ℝ)
    (_hΛ : Tendsto Λ l atTop) (_hε : Tendsto (fun i ↦ ε i * Λ i) l (𝓝 0))
    (_hρ : ∀ᶠ i in l, IsModulatedCutoff m𝔽 (Λ i) (ε i) (ρ i) ∧ innerBand(Λ i, ε i)) :
    Tendsto (fun i ↦ ∫ x, (ρ i x : ℂ) * diagonal(kgeom) x ∂μ𝔽) l
      (𝓝 (∫ x, diagonal(kgeom) x ∂μ𝔽)) := by sorry

-- TODO(paper-gap): The end of the proof cites (10.4.3.31) as its conclusion.
-- The intended conclusion is (12.1.1.22). The geometric kernel formula is
-- (10.4.3.31), while (10.4.3.32) starts a computation of the kernel action.

/-- Paper: Remark 12.1.1.4, pp. 503–504. For a test vanishing at the identity,
the sharp and smooth cutoff masses of the geometric diagonal differ by a
quantity tending to zero in the joint limit of (12.1.1.22). -/
theorem tendsto_absolute_sub_smooth_globalLineGeometricKernel_diagonal (_ha : 0 < a)
    (_hφ : φ.val 1 = 0)
    {ι : Type*} {l : Filter ι} (Λ ε : ι → ℝ) (ρ : ι → C𝔽 → ℝ)
    (_hΛ : Tendsto Λ l atTop) (_hε : Tendsto (fun i ↦ ε i * Λ i) l (𝓝 0))
    (_hρ : ∀ᶠ i in l, IsSmoothModulatedCutoff m𝔽 (Λ i) (ε i) (ρ i) ∧ innerBand(Λ i, ε i)) :
    Tendsto (fun i ↦ (∫ x, (modulatedAbsoluteCutoff m𝔽 (Icc (Λ i)⁻¹ (Λ i)) x : ℂ) *
        diagonal(kgeom) x ∂μ𝔽) - ∫ x, (ρ i x : ℂ) * diagonal(kgeom) x ∂μ𝔽) l (𝓝 0) := by
  let D : C𝔽 → ℂ := diagonal(kgeom)
  have hD : Integrable D μ𝔽 :=
    integrable_globalLineGeometricKernel_diagonal hU hBorel a hs φ _ha _hφ
  have hsharp :
      Tendsto (fun R : ℝ ↦ ∫ x,
        (modulatedAbsoluteCutoff m𝔽 (Icc R⁻¹ R) x : ℂ) * D x ∂μ𝔽)
        atTop (𝓝 (∫ x, D x ∂μ𝔽)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖D x‖)
    · exact .of_forall fun R ↦
        ((modulatedAbsoluteCutoff_measurable_bounded m𝔽 (Icc R⁻¹ R)
          measurableSet_Icc).1.complex_ofReal.aestronglyMeasurable).mul
            hD.aestronglyMeasurable
    · refine .of_forall fun R ↦ .of_forall fun x ↦ ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right
        ((modulatedAbsoluteCutoff_measurable_bounded m𝔽 (Icc R⁻¹ R)
          measurableSet_Icc).2 x) (norm_nonneg _)).trans_eq (one_mul _)
    · exact hD.norm
    · refine .of_forall fun x ↦ ?_
      have hx : 0 < ((m𝔽 x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
      have hlo : ∀ᶠ R : ℝ in atTop, R⁻¹ ≤ ((m𝔽 x).val : ℝ) :=
        (tendsto_inv_atTop_zero (𝕜 := ℝ)).eventually (eventually_le_nhds hx)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlo, eventually_ge_atTop ((m𝔽 x).val : ℝ)] with R hl hr
      simp [modulatedAbsoluteCutoff, show ((m𝔽 x).val : ℝ) ∈ Icc R⁻¹ R from ⟨hl, hr⟩]
  have hsmooth := tendsto_integral_cutoff_globalLineGeometricKernel_diagonal
    hU hBorel a hs φ _ha _hφ Λ ε ρ _hΛ _hε
    (_hρ.mono fun _ h ↦ ⟨h.1.1, h.2⟩)
  simpa only [D, Function.comp_def, sub_self] using (hsharp.comp _hΛ).sub hsmooth

local notation "wline" =>
  (fun g : C𝔽 ↦ intervalSobolevDensity (-(0 : ℝ)) 0 s (logNorm g))
local notation "νline" => ((μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (wline g)))

omit hU hBorel in
/-- Paper: Remark 12.1.1.4, p. 503. The spectral kernel divided by its input
weight is square integrable for the positive Sobolev measure in both variables.
Deviation: The remark asserts the opposite; the square integrability is
Theorem 10.4.3.4(2). The kernel of `P^geom_a ∘ A(φ)`, which the remark is
about, is `k^geom`; see `globalLineGeometricKernel_weighted_not_memLp`. -/
theorem globalLineSpectralKernel_weighted_memLp (ha : 0 < a) :
    MemLp (fun p : C𝔽 × C𝔽 ↦ ((wline p.2)⁻¹ : ℝ) • kspec p) 2 ((νline).prod νline) :=
  (spectralLineKernel_hilbertSchmidt (F := F) a hs₁(hs) φ ha).1

omit hU hBorel in
/-- Paper: Remark 12.1.1.4, p. 503. For a nonzero test vanishing at the identity,
the geometric kernel divided by its input weight is not square integrable for
the positive Sobolev measure in both variables.
Deviation: The print writes `k^spec` here, for which the claim is false
(`Sec1b_Printed.lean`); the kernel of `P^geom_a ∘ A(φ)` is `k^geom`. The zero
test must be excluded. -/
theorem globalLineGeometricKernel_weighted_not_memLp
    (_ha : 0 < a) (_hφ : φ.val 1 = 0) (_hne : φ ≠ 0) :
    ¬ MemLp (fun p : C𝔽 × C𝔽 ↦ ((wline p.2)⁻¹ : ℝ) • kgeom p) 2 ((νline).prod νline) := by
  sorry

omit hU hBorel in
/-- Paper: Remark 12.1.1.4, p. 503. Convolution by a nonzero test is not
Hilbert–Schmidt on the weighted Sobolev space, hence not nuclear.
Deviation: The zero test must be excluded. -/
theorem hardySobolevTestAction_not_hilbertSchmidt (_hne : φ ≠ 0) :
    hardySobolevTestAction μ𝔽 m𝔽 _ _ _ hbase hs₀(hs) φ ∉
      hilbertSchmidtOperators (W(s)) (W(s)) := by sorry

omit hU hBorel in
/-- Paper: Remark 12.1.1.4, pp. 503–504. For a nonzero test vanishing at the
identity, untruncated geometric convolution fails to be Hilbert–Schmidt.
Deviation: The obstruction comes from the full convolution kernel, and the
zero test must be excluded. -/
theorem geometricProjection_convolution_not_hilbertSchmidt
    (_ha : 0 < a) (_hφ : φ.val 1 = 0) (_hne : φ ≠ 0) :
    (geometricProjection (F := F) a hline hs₀(hs)).comp
      (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ hbase hs₀(hs) φ) ∉
        hilbertSchmidtOperators (W(s)) (W(s)) := by
  let A : W(s) →L[ℂ] W(s) := hardySobolevTestAction μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hbase hs₀(hs) φ
  let M := globalThetaSobolev F a (α := -(0 : ℝ)) (β := 0) hbase hs₀(hs)
  have hspec : Tspec ∈ hilbertSchmidtOperators (W(s)) (W(s)) := by
    let : IsLocallyFiniteMeasure νline := sobolevKernelWeight_locallyFinite (F := F) 0 s
    let K : C𝔽 × C𝔽 → ℂ := fun p ↦ (wline p.2)⁻¹ • kspec p
    have hK := spectralLineKernel_hilbertSchmidt (F := F) a hs₁(hs) φ _ha
    let T := integralKernelOperator νline (hK.choose.toLp K)
    have he : T.val = Tspec := hK.choose_spec
    have hmem : T.val ∈ hilbertSchmidtOperators (W(s)) (W(s)) := T.property
    exact (congrArg (fun L : W(s) →L[ℂ] W(s) ↦ L ∈ hilbertSchmidtOperators (W(s)) (W(s))) he).mp hmem
  intro hgeom
  have hsum : M.starProjection.comp A + M.orthogonal.starProjection.comp A = A := by
    ext1 u
    exact M.starProjection_add_starProjection_orthogonal (A u)
  refine (hardySobolevTestAction_not_hilbertSchmidt (F := F) (hs := hs) (φ := φ) _hne :
    A ∉ hilbertSchmidtOperators (W(s)) (W(s))) ?_
  exact Eq.subst (motive := fun B ↦ B ∈ hilbertSchmidtOperators (W(s)) (W(s))) hsum
    ((hilbertSchmidtOperators (W(s)) (W(s))).add_mem hgeom hspec)

-- TODO(later): needs §12.5. The proof of Theorem 12.5.1.1, p. 520, integrates the
-- smoothened strip kernel of Definition 10.4.3.7 along the diagonal. The paper
-- states (12.1.1.21)–(12.1.1.23) for the line kernels only.

end GlobalKernels

end RiemannMasullo
