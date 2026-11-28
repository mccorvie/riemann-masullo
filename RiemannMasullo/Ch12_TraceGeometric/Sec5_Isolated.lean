module
public import RiemannMasullo.ForMathlib.Analysis.Fourier.QuadraticBoxProfile
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import RiemannMasullo.AppB_AnalyticNT.Sec2
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import RiemannMasullo.AppB_AnalyticNT.Sec6
import RiemannMasullo.Ch13_ZerosHecke.Targets
public import RiemannMasullo.ForMathlib.Analysis.Complex.ExpSumLogarithmicRegion
import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace

public import RiemannMasullo.Ch12_TraceGeometric.Sec5_FirstPrimeAbel
public import RiemannMasullo.ForMathlib.Analysis.Fourier.QuadraticBoxProfile
import Mathlib.Geometry.Manifold.PartitionOfUnity
import RiemannMasullo.Ch10_TraceSpectral.Sec4b_ProjectedKernels
public import RiemannMasullo.Ch12_TraceGeometric.Sec5

/-! # Isolated statements of §12.5

The projective strip kernel and its consequences for the smoothened geometric diagonal.

## The projective strip kernel needed for (12.5.1.4)

The first theorem supplies the kernel hypothesis of the smoothened diagonal formula in §12.5.
The second theorem specializes that formula to this kernel.
-/

@[expose] public noncomputable section

/-! ## A physical zero criterion at a fixed positive threshold

For the all-zero identity of Theorem B.4.4.7 (p. 623), the shifted first-prime
observable detects the same genuine zeros whose omission is at issue in
Theorem 12.5.1.1 (pp. 519–520). Its smallness at an unproved rate is an additional
arithmetic assertion. The criterion below also detects a zero exactly on the line.
-/

namespace RiemannMasullo.Isolated

open Classical Filter Function MeasureTheory NumberField Set
open scoped ContDiff ENNReal NNReal Topology

set_option quotPrecheck false

/-- The common complex-valued profile for the degree-one prime test, supported in `[2,4]`. -/
def thresholdProfile (x : ℝ) : ℂ := (exists_translatedGevreyPolarProfile.choose x : ℂ)

/-- The detector has both polar moments zero and sees each point strictly right of the axis
in the open centered strip, with the positive bilateral Laplace convention of §12.5. -/
theorem thresholdProfile_spec :
    ContDiff ℝ ∞ thresholdProfile ∧ tsupport thresholdProfile ⊆ Icc 2 4 ∧
    (bilateralLaplace thresholdProfile (1 / 2) = 0 ∧ bilateralLaplace thresholdProfile (-(1 / 2)) = 0) ∧
    ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → bilateralLaplace thresholdProfile s ≠ 0 := by
  let g := exists_translatedGevreyPolarProfile.choose
  obtain ⟨_, hg, hsupport, ⟨hneg, _, hpos⟩, hdetect, _⟩ := exists_translatedGevreyPolarProfile.choose_spec
  have hs : Function.support thresholdProfile ⊆ Function.support g := fun x hx he ↦
    hx (show (g x : ℂ) = 0 by simp [he])
  refine ⟨Complex.ofRealCLM.contDiff.comp hg, (closure_mono hs).trans hsupport, ⟨hpos, hneg⟩, ?_⟩
  intro s h h'
  exact hdetect s (abs_pos_of_pos h) (by simpa only [abs_of_pos h] using h')

variable {F : Type*} [Field F] [NumberField F]
local notation "G" => IdeleClassGroup (𝓞 F) F
local notation "U" => PontryaginDual G
local notation "ord(" χ "," ρ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ ρ
local notation "sites(" χ ")" => {ρ : ℂ // 0 < ord(χ, ρ)}
local notation "energy(" ψ "," c ")" =>
  AbelEdge.weightedSquareAbelMean (fun y ↦ firstPrimeDegreeOneSum (ψ)⁻¹ thresholdProfile y 4) (c)

/-- Every positive divisor site right of the central line has nonzero detector moment. -/
theorem thresholdProfile_detects_right_zero (ψ : U) (ρ : sites(ψ⁻¹)) (hr : 1 / 2 < ρ.val.re) :
    bilateralLaplace thresholdProfile (ρ.val - 1 / 2) ≠ 0 := by
  obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec (F := F) ψ⁻¹
  have hz := ρ.property
  rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _)] at hz
  have ho : 0 < meromorphicOrderAt (continuedCompletedHeckeL ψ⁻¹) ρ.val := by
    cases he : meromorphicOrderAt (continuedCompletedHeckeL ψ⁻¹) ρ.val with
    | top => simp
    | coe k => rw [he, WithTop.untop₀_coe] at hz; exact_mod_cast hz
  have hlt := completedHeckeL_continuation_zeros ψ⁻¹ _ hL heq (by linarith : 0 < ρ.val.re) ho
  apply thresholdProfile_spec.2.2.2 <;>
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] <;> linarith

private theorem thresholdProfile_polarTerm (ψ : U) (y : ℝ) :
    firstPrimePolarMoment ψ thresholdProfile y (1 / 2) = 0 := by
  have h : (∫ x : ℝ, thresholdProfile x * Complex.exp ((1 / 2 : ℂ) * x)) = 0 :=
    thresholdProfile_spec.2.2.1.1
  rw [firstPrimePolarMoment, h, mul_zero, ite_self]

variable (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 F) F) (hτ : RightInverse τ (ideleClassNorm F))
  (ψ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (hψ : ∀ t, ψ (τ t) = 1)
include hτ hψ

/-- One weighted square-integrability bound for the signed degree-one prime sum excludes
every completed-divisor site strictly beyond its damping line. -/
theorem firstPrime_zero_re_le_of_integrableOn_square {q : ℝ} (hq : 0 ≤ q)
    (hL : IntegrableOn (fun y : ℝ ↦ ‖firstPrimeDegreeOneSum ψ⁻¹ thresholdProfile y 4‖ ^ 2 *
      Real.exp (-(2 * q) * y)) (Ici 0)) :
    ∀ ρ : ℂ, 0 < ord(ψ⁻¹, ρ) → ρ.re - 1 / 2 ≤ q := by
  intro ρ hρ
  apply le_of_not_gt
  intro hgap
  apply thresholdProfile_detects_right_zero ψ ⟨ρ, hρ⟩ (by change 1 / 2 < ρ.re; linarith)
  apply firstPrime_moment_eq_zero_of_integrableOn_square τ hτ ψ hψ thresholdProfile thresholdProfile_spec.1
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 4) thresholdProfile_spec.2.1 hq _ ρ hρ hgap
  simpa only [thresholdProfile_polarTerm, sub_zero] using hL

/-- A strictly exterior site makes the energy infinite throughout the explicit open
damping interval. The offset may be zero. -/
theorem firstPrime_weightedSquareAbelMean_eq_top_of_zero {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    {ρ : ℂ} (hρ : 0 < ord(ψ⁻¹, ρ)) (hgap : ε < 2 * (ρ.re - 1 / 2 - c)) : energy(ψ, c) ε = ⊤ := by
  by_contra hQ
  have hm := firstPrimeDegreeOneSum_measurable ψ⁻¹ thresholdProfile
    thresholdProfile_spec.1.continuous.measurable 4
  have hi := (AbelEdge.weightedSquareAbelMean_ne_top_iff_integrableOn_sq_mul_exp hm c hε).mp hQ
  have h := firstPrime_zero_re_le_of_integrableOn_square τ hτ ψ hψ (q := c + ε / 2) (by linarith) hi ρ hρ
  linarith

/-- If all divisor sites lie on or left of the edge, the limit of the uncentered prime
observable is the sum of the squared full-multiplicity coefficients on that edge. -/
theorem firstPrime_tendsto_abelBoundaryMass {c : ℝ} (hc : 0 < c)
    (hr : ∀ ρ : ℂ, 0 < ord(ψ⁻¹, ρ) → ρ.re - 1 / 2 ≤ c) :
    Tendsto (energy(ψ, c)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (firstPrimeBoundaryMass ψ⁻¹ thresholdProfile c))) := by
  simpa only [thresholdProfile_polarTerm, sub_zero] using
    firstPrime_centered_tendsto_abelBoundaryMass τ hτ ψ hψ thresholdProfile thresholdProfile_spec.1
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 4) thresholdProfile_spec.2.1 hc hr

/-- The energy always has an extended-real limit. A strictly exterior site gives infinity,
and otherwise the limit is the full boundary mass. -/
theorem firstPrime_abel_tendsto_dichotomy {c : ℝ} (hc : 0 < c) :
    Tendsto (energy(ψ, c)) (𝓝[>] 0)
      (𝓝 (if ∃ ρ : ℂ, 0 < ord(ψ⁻¹, ρ) ∧ c < ρ.re - 1 / 2 then (⊤ : ℝ≥0∞)
        else ENNReal.ofReal (firstPrimeBoundaryMass ψ⁻¹ thresholdProfile c))) := by
  split_ifs with he
  · obtain ⟨ρ, hρ, hgap⟩ := he
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT (by linarith : 0 < 2 * (ρ.re - 1 / 2 - c))] with ε hε
    exact (firstPrime_weightedSquareAbelMean_eq_top_of_zero τ hτ ψ hψ hc.le hε.1 hρ hε.2).symm
  · exact firstPrime_tendsto_abelBoundaryMass τ hτ ψ hψ hc fun ρ hρ ↦
      le_of_not_gt fun h ↦ he ⟨ρ, hρ, h⟩

private theorem thresholdProfile_mass_zero_iff {c : ℝ} (hc : 0 < c) :
    ENNReal.ofReal (firstPrimeBoundaryMass ψ⁻¹ thresholdProfile c) = 0 ↔
      ∀ z : sites(ψ⁻¹), z.val.re - 1 / 2 ≠ c := by
  let b (z : sites(ψ⁻¹)) := firstPrimeFullCoefficient ψ⁻¹ thresholdProfile z.val
  let d (z : sites(ψ⁻¹)) := if z.val.re - 1 / 2 = c then ‖b z‖ ^ 2 else 0
  have hb : Summable (fun z ↦ ‖b z‖) := (firstPrime_fullSeries_bounded_error τ hτ ψ hψ
    thresholdProfile thresholdProfile_spec.1 (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 4)
    thresholdProfile_spec.2.1).1
  have hn (z) : 0 ≤ d z := by dsimp [d]; split_ifs <;> positivity
  have hd : Summable d := (hb.mul_right (∑' z, ‖b z‖)).of_nonneg_of_le hn (fun z ↦ by
    dsimp [d]
    split_ifs
    · rw [pow_two]
      exact mul_le_mul_of_nonneg_left (hb.le_tsum z (fun j _ ↦ norm_nonneg _)) (norm_nonneg _)
    · exact mul_nonneg (norm_nonneg _) (tsum_nonneg (fun z ↦ norm_nonneg (b z))))
  rw [ENNReal.ofReal_eq_zero]
  constructor
  · intro hm z hz
    change (∑' z, d z) ≤ 0 at hm
    have hne : b z ≠ 0 := mul_ne_zero (by exact_mod_cast z.property.ne')
      (thresholdProfile_detects_right_zero ψ z (by linarith))
    have hp : 0 < d z := by simpa only [d, ite_eq_left hz] using sq_pos_of_pos (norm_pos_iff.mpr hne)
    exact hp.not_ge ((hd.le_tsum z (fun j _ ↦ hn j)).trans hm)
  · intro h
    have hzero (z : sites(ψ⁻¹)) : d z = 0 := ite_eq_right (h z)
    change (∑' z, d z) ≤ 0
    simp only [hzero, tsum_zero, le_refl]

/-- The energy of the fixed signed prime observable tends to zero exactly when the closed
right half-plane at the given positive offset contains no divisor site.
Reconstruction: This criterion for #5571 combines the translated §12.5 identity with the
compact detector. Proving vanishing of the arithmetic energy remains open. -/
theorem firstPrime_tendsto_zero_iff_no_closed_exterior {c : ℝ} (hc : 0 < c) :
    Tendsto (energy(ψ, c)) (𝓝[>] 0) (𝓝 0) ↔ ∀ ρ : ℂ, 0 < ord(ψ⁻¹, ρ) → ρ.re < 1 / 2 + c := by
  have hd := firstPrime_abel_tendsto_dichotomy τ hτ ψ hψ hc
  have hz : Tendsto (energy(ψ, c)) (𝓝[>] 0) (𝓝 0) ↔ _ :=
    ⟨fun h ↦ tendsto_nhds_unique hd h, fun h ↦ h ▸ hd⟩
  rw [hz]
  split_ifs with he
  · obtain ⟨ρ, hρ, hgap⟩ := he
    simp only [ENNReal.top_ne_zero, false_iff]
    intro h
    linarith [h ρ hρ]
  · rw [thresholdProfile_mass_zero_iff τ hτ ψ hψ hc]
    constructor
    · intro hn ρ hρ
      have hle : ρ.re - 1 / 2 ≤ c := le_of_not_gt fun h ↦ he ⟨ρ, hρ, h⟩
      have hlt := lt_of_le_of_ne hle (hn ⟨ρ, hρ⟩)
      linarith
    · intro h z hz
      linarith [h z.val z.property]

/-- The same criterion follows from the lower limit of the energy. -/
theorem firstPrime_liminf_zero_iff_no_closed_exterior {c : ℝ} (hc : 0 < c) :
    Filter.liminf (energy(ψ, c)) (𝓝[>] 0) = 0 ↔ ∀ ρ : ℂ, 0 < ord(ψ⁻¹, ρ) → ρ.re < 1 / 2 + c := by
  have hd := firstPrime_abel_tendsto_dichotomy τ hτ ψ hψ hc
  rw [← firstPrime_tendsto_zero_iff_no_closed_exterior τ hτ ψ hψ hc, hd.liminf_eq]
  exact ⟨fun h ↦ h ▸ hd, fun h ↦ tendsto_nhds_unique hd h⟩

/-- Any prescribed approach from the right gives the same criterion. -/
theorem firstPrime_sampled_abel_zero_iff_no_closed_exterior {c : ℝ} (hc : 0 < c)
    {T : Type*} {l : Filter T} [l.NeBot] {e : T → ℝ} (he : Tendsto e l (𝓝[>] (0 : ℝ))) :
    Tendsto (fun t ↦ energy(ψ, c) (e t)) l (𝓝 0) ↔ ∀ ρ : ℂ, 0 < ord(ψ⁻¹, ρ) → ρ.re < 1 / 2 + c := by
  have hd := firstPrime_abel_tendsto_dichotomy τ hτ ψ hψ hc
  rw [← firstPrime_tendsto_zero_iff_no_closed_exterior τ hτ ψ hψ hc]
  exact ⟨fun h ↦ (tendsto_nhds_unique (hd.comp he) h) ▸ hd, fun h ↦ h.comp he⟩

section AllCharacters

omit hτ hψ

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : G →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "exteriorZeros(" τ ", " c ")" =>
  {z : {χ : U // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < ord(z.1.val, z.2) ∧ c ≤ |z.2.re - 1 / 2|}
local notation "zeroTerm(" φ ", " z ")" =>
  (ord((z).val.1.val, (z).val.2) : ℂ) * modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽
    (φ : BruhatCompactSupport G).val (ideleClassNormTwist (F := F) (z).val.1.val ((z).val.2 - 1 / 2))

/-- The completed divisors agree at `z` and `1 - z` after character inversion.
The proof follows Michael Lyle (mlyle), PR #7586. -/
private theorem firstPrime_ord_reflection (χ : U) (z : ℂ) : ord(χ⁻¹, 1 - z) = ord(χ, z) := by
  obtain ⟨hL, hl⟩ := continuedCompletedHeckeL_spec χ
  obtain ⟨hD, hd⟩ := continuedCompletedHeckeL_spec χ⁻¹
  obtain ⟨ε, hε, hne, hfe⟩ := completedHeckeL_continuation_functionalEquation χ _ _ hL hl hD hd
  have he : meromorphicOrderAt (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) z =
      meromorphicOrderAt (continuedCompletedHeckeL χ⁻¹) (1 - z) := by
    simpa [Function.comp_def] using meromorphicOrderAt_comp_of_deriv_ne_zero
      (f := continuedCompletedHeckeL χ⁻¹) (show AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) z by fun_prop)
      (show deriv (fun s : ℂ ↦ 1 - s) z ≠ 0 by simp)
  rw [show (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) =
      ε * continuedCompletedHeckeL χ from funext hfe,
    meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt z) (hne z)] at he
  rw [MeromorphicOn.divisor_apply hD.meromorphicOn (mem_univ _),
    MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _), ← he]

private theorem firstPrime_isEmpty_exterior_iff_all_right (τ : ℝ≥0ˣ →ₜ* G) (c : ℝ) :
    IsEmpty exteriorZeros(τ, c) ↔ ∀ (ψ : U), (∀ t, ψ (τ t) = 1) →
      ∀ ρ : ℂ, 0 < ord(ψ⁻¹, ρ) → ρ.re < 1 / 2 + c := by
  have hinv (χ : U) (hχ : ∀ t, χ (τ t) = 1) (t : ℝ≥0ˣ) : χ⁻¹ (τ t) = 1 := by
    change (χ (τ t))⁻¹ = 1
    rw [hχ, inv_one]
  constructor
  · intro he ψ hψ ρ hρ
    apply lt_of_not_ge
    intro hr
    apply he.false
    exact ⟨(⟨ψ⁻¹, hinv ψ hψ⟩, ρ), hρ, le_trans (by linarith : c ≤ ρ.re - 1 / 2) (le_abs_self _)⟩
  · intro h
    refine ⟨fun z ↦ ?_⟩
    obtain ⟨⟨⟨χ, hχ⟩, ρ⟩, hρ, hout⟩ := z
    change 0 < ord(χ, ρ) at hρ
    change c ≤ |ρ.re - 1 / 2| at hout
    have hright := h χ⁻¹ (hinv χ hχ) ρ (by simpa only [inv_inv] using hρ)
    have hleft := h χ hχ (1 - ρ) (by rwa [firstPrime_ord_reflection])
    rw [Complex.sub_re, Complex.one_re] at hleft
    exact (abs_lt.mpr ⟨by linarith, by linarith⟩).not_ge hout

/-- The exterior zero sum of Theorem 12.5.1.1 (pp. 519–520) vanishes for every admissible
Bruhat test at a given positive width exactly when the fixed first-prime test has squared
Abel limit zero for every character trivial on the norm section. -/
theorem hasSum_exteriorZeros_iff_all_firstPrime_abel (τ : ℝ≥0ˣ →ₜ* G)
    (hτ : RightInverse τ (ideleClassNorm F)) {c : ℝ} (hc : 0 < c) :
    (∀ φ : BruhatCompactSupport G, (∀ g : C₁, φ.val g = 0) →
      HasSum (fun z : exteriorZeros(τ, c) ↦ zeroTerm(φ, z)) 0) ↔
      ∀ (ψ : U), (∀ t, ψ (τ t) = 1) → Tendsto (energy(ψ, c)) (𝓝[>] 0) (𝓝 0) := by
  rw [hasSum_exteriorZeros_iff_isEmpty τ hτ c, firstPrime_isEmpty_exterior_iff_all_right]
  exact forall_congr' fun ψ ↦ forall_congr' fun hψ ↦
    (firstPrime_tendsto_zero_iff_no_closed_exterior τ hτ ψ hψ hc).symm

/-- The damping parameters can be prescribed once for all normalized characters. -/
theorem hasSum_exteriorZeros_iff_all_firstPrime_sampled_abel (τ : ℝ≥0ˣ →ₜ* G)
    (hτ : RightInverse τ (ideleClassNorm F)) {c : ℝ} (hc : 0 < c)
    {T : Type*} {l : Filter T} [l.NeBot] {e : T → ℝ} (he : Tendsto e l (𝓝[>] (0 : ℝ))) :
    (∀ φ : BruhatCompactSupport G, (∀ g : C₁, φ.val g = 0) →
      HasSum (fun z : exteriorZeros(τ, c) ↦ zeroTerm(φ, z)) 0) ↔
      ∀ (ψ : U), (∀ t, ψ (τ t) = 1) → Tendsto (fun t ↦ energy(ψ, c) (e t)) l (𝓝 0) := by
  rw [hasSum_exteriorZeros_iff_isEmpty τ hτ c, firstPrime_isEmpty_exterior_iff_all_right]
  exact forall_congr' fun ψ ↦ forall_congr' fun hψ ↦
    (firstPrime_sampled_abel_zero_iff_no_closed_exterior τ hτ ψ hψ hc he).symm

end AllCharacters

end RiemannMasullo.Isolated

open MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hs₁(" hs ")" => (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hs)
local notation "hs₀(" hs ")" => (zero_lt_one.trans hs₁(hs)).le

/-- Paper: (12.5.1.4), p. 520. For a test vanishing on the norm-one classes, a projective
Sobolev tensor represents convolution by the test after spectral projection at twist 1/2.
Reconstruction: Definition 10.4.3.7(2), p. 473, subtracts the spectral kernel. Using this
subtraction on p. 520 presupposes a tensor for the operator in (10.4.3.45).
Deviation: We ask for any representing tensor, restricted to the positive half-widths and
tests of Theorem 12.5.1.1. We impose no finite-rank expansion on the tensor.
Quotient nuclearity and a finite decomposition into weighted adjoints give the representing
tensor. The paper uses it on pp. 520, 522. -/
theorem exists_projectiveKernel_stripTestAction_spectralProjection
    (φ : BruhatCompactSupport C𝔽) (_hφ : ∀ g : C₁, φ.val g = 0)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) :
    ∃ K, sobolevProjectiveKernelOperator (F := F) hα.le hs₀(hs) K =
      (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα.le).trans hα.le) hs₀(hs) φ).comp
        (spectralProjection (F := F) (1 / 2) hα.le hs₀(hs)) := by
  exact stripTestAction_spectralProjection_has_projectiveKernel (1 / 2) hα.le hs₀(hs) φ

section PositiveTranslations

/-! ### Endpoint estimates for signed positive translates

The expansion of #7518 uses the inverse of the chosen normalized character.
The norm-one volume multiplies the local principal values in the full
functional of Theorem B.4.4.7, p. 623. The endpoint estimates below apply
for each fixed field and character, including the principal character.

mlyle observed a fixed square-root saving from the classical zero-free region
in [#5571](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7147625073).
Here arbitrary smoothness gives every fixed multiple of the square root.
The smoothed rational prime-shell asymptotic is in #7527, and a sharper
estimate for the principal rational Fabius profile is in [the endpoint discussion](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7149346245).
mlyle’s earlier rational theta probes used quadratically decreasing interval
widths. The last estimate accepts a transform bound for a profile on the centered strip.
-/

open Filter Function IsDedekindDomain
open scoped Asymptotics ContDiff Topology

attribute [local instance] instFiniteCompletionUnitsLocallyCompactSec4b

local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "zeros(" χ ")" =>
  {s : ℂ // 0 < MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ s}

/-- The log-coordinate coefficient of Proposition B.2.1.9, p. 598, with a
polynomial weight valid also on the real axis of a closed vertical strip. -/
private theorem bilateralLaplace_rapidDecay_on_closedStrip
    (H : ℝ → ℂ) (hs : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    {a b : ℝ} (hab : a < b) (n : ℕ) :
    ∃ C > (0 : ℝ), ∀ w : ℂ, w.re ∈ Icc a b →
      ‖bilateralLaplace H w‖ * (1 + |w.im|) ^ n ≤ C := by
  let f : _root_.SchwartzMap ℝ ℂ := hc.toSchwartzMap hs
  have hz (j : ℕ) : iteratedDeriv j H =ᶠ[cocompact ℝ] 0 := by
    have hh := hc.iteratedFDeriv (𝕜 := ℝ) j
    rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact] at hh
    filter_upwards [hh] with x hx
    rw [iteratedDeriv_eq_iteratedFDeriv, hx]
    rfl
  have hf : ExponentialDecay f :=
    ⟨fun j _ _ ↦ ((hz j).filter_mono atTop_le_cocompact).trans_isBigO
      (Asymptotics.isBigO_zero _ _), fun j _ _ ↦ ((hz j).filter_mono atBot_le_cocompact).trans_isBigO
      (Asymptotics.isBigO_zero _ _)⟩
  let Φ := mellin (fun t ↦ H (Real.log t))
  have heq (w : ℂ) : Φ w = bilateralLaplace H w := by
    change mellin (fun t ↦ H (Real.log t)) w = _
    rw [mellin, ← integral_comp_exp]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp,
      ← mul_assoc, ← Complex.exp_add, mul_comm]
    congr 1
    ring_nf
  obtain ⟨A, hA, hlarge⟩ := mellin_heightBound_of_exponentialDecay f hf a b hab
    (n + 1) (Nat.succ_pos _)
  have hΦ : Continuous Φ := (differentiable_mellin_of_exponentialDecay f hf).continuous
  obtain ⟨B, hsmall⟩ := (isCompact_Icc.reProdIm isCompact_Icc :
    IsCompact (Complex.reProdIm (Icc a b) (Icc (-1 : ℝ) 1))).exists_bound_of_continuousOn
      hΦ.continuousOn
  refine ⟨max A B * 2 ^ n, mul_pos (hA.trans_le (le_max_left _ _)) (by positivity), ?_⟩
  intro w hw
  rw [← heq]
  by_cases ht : 1 ≤ |w.im|
  · have hpos : 0 < |w.im| := zero_lt_one.trans_le ht
    have hd := hlarge w.re hw w.im (abs_pos.mp hpos)
    simp only [Complex.re_add_im] at hd
    have hwgt : (1 + |w.im|) ^ n ≤ 2 ^ n * |w.im| ^ (n + 1) := by
      calc (1 + |w.im|) ^ n ≤ (2 * |w.im|) ^ n :=
             pow_le_pow_left₀ (by positivity) (by linarith) n
        _ ≤ _ := by rw [mul_pow]; gcongr; exact Nat.le_succ n
    calc
      ‖Φ w‖ * (1 + |w.im|) ^ n ≤ ‖Φ w‖ * (2 ^ n * |w.im| ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left hwgt (norm_nonneg _)
      _ = (‖Φ w‖ * |w.im| ^ (n + 1)) * 2 ^ n := by ring
      _ ≤ max A B * 2 ^ n := mul_le_mul_of_nonneg_right
        (((le_div_iff₀ (pow_pos hpos _)).mp hd).trans (le_max_left _ _)) (by positivity)
  · have hmem : w ∈ Complex.reProdIm (Icc a b) (Icc (-1 : ℝ) 1) :=
      Complex.mem_reProdIm.mpr ⟨hw, abs_le.mp (not_le.mp ht).le⟩
    apply mul_le_mul ((hsmall w hmem).trans (le_max_right _ _))
      (pow_le_pow_left₀ (by positivity) (by linarith [not_le.mp ht]) n) (by positivity)
    exact (le_of_lt hA).trans (le_max_left _ _)

private theorem translatedLocalTerms_characterZero_order (χ : U) (z : zeros(χ)) :
    0 < meromorphicOrderAt (continuedCompletedHeckeL χ) z.val := by
  have hz := z.property
  rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec χ).1.meromorphicOn
    (mem_univ _)] at hz
  cases he : meromorphicOrderAt (continuedCompletedHeckeL χ) z.val with
  | top => simp
  | coe k =>
    rw [he, WithTop.untop₀_coe] at hz
    exact_mod_cast hz

/-- Replacing the scaled logarithm of Proposition B.6.1.1 by 1 + log(1 + |t|)
costs only a constant depending on the field and character. -/
private theorem translatedLocalTerms_logarithmicZeroGap (χ : U) :
    ∃ c > (0 : ℝ), ∀ z : zeros(χ),
      z.val.re ≤ 1 - c / (1 + Real.log (1 + |z.val.im|)) := by
  obtain ⟨A, hA, hF⟩ := finiteHeckeL_zeroFreeRegion
  obtain ⟨B, hB, hregion⟩ := hF F χ
  obtain ⟨L, hL, hseries⟩ := finiteHeckeL_exists_continuation χ
  let D := (Module.finrank ℚ F : ℝ) ^ 4
  let C := 1 + Real.log (3 * B)
  have hBpos : 0 < B := by linarith
  have hD : 0 < D := pow_pos (by exact_mod_cast Module.finrank_pos) _
  have hLB : 0 < Real.log (3 * B) := Real.log_pos (by linarith)
  have hC : 0 < C := by dsimp [C]; linarith
  let c := min 1 (A / (D * C))
  refine ⟨c, lt_min zero_lt_one (div_pos hA (mul_pos hD hC)), ?_⟩
  intro z
  let t := |z.val.im|
  have ht : 0 ≤ t := abs_nonneg _
  have hu : 0 < B * (t + 3) := by positivity
  have hv : 0 < 1 + t := by positivity
  have hr : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  have hlog : 0 < Real.log (B * (t + 3)) :=
    Real.log_pos (by nlinarith [mul_nonneg hBpos.le ht])
  have hcomp : Real.log (B * (t + 3)) ≤ C * (1 + Real.log (1 + t)) := by
    calc
      Real.log (B * (t + 3)) ≤ Real.log ((3 * B) * (1 + t)) :=
        Real.log_le_log hu (by nlinarith [mul_nonneg hBpos.le ht])
      _ = Real.log (3 * B) + Real.log (1 + t) := Real.log_mul (by positivity) hv.ne'
      _ ≤ C * (1 + Real.log (1 + t)) := by
        dsimp only [C]
        nlinarith [mul_nonneg hLB.le hr]
  have hrpos : 0 < 1 + Real.log (1 + t) := by linarith
  by_cases hs : 0 < z.val.re
  case neg =>
    have hquot : c / (1 + Real.log (1 + t)) ≤ 1 :=
      (div_le_iff₀ hrpos).mpr (by rw [one_mul]; exact (min_le_left _ _).trans (by linarith))
    change z.val.re ≤ 1 - c / (1 + Real.log (1 + t))
    linarith
  have hleft : z.val.re < 1 - A / (D * Real.log (B * (t + 3))) := by
    apply lt_of_not_ge
    intro hz
    have hn := hregion L hL hseries z.val hz
    rw [meromorphicOrderAt_finiteHeckeL_continuation χ hL.meromorphicOn hseries hs] at hn
    exact hn.not_gt (translatedLocalTerms_characterZero_order χ z)
  refine hleft.le.trans (sub_le_sub_left ?_ 1)
  refine (div_le_div_of_nonneg_right (min_le_right 1 (A / (D * C))) hrpos.le).trans ?_
  change A / (D * C) / (1 + Real.log (1 + t)) ≤ A / (D * Real.log (B * (t + 3)))
  rw [div_div, mul_assoc]
  exact div_le_div_of_nonneg_left hA.le (mul_pos hD hlog) (mul_le_mul_of_nonneg_left hcomp hD.le)

/-- Classical input: M. D. Coleman, *A zero-free region for the Hecke L-functions*,
Mathematika 37 (1990), Theorem 2, pp. 287–304. See I. Petrow, *The Weyl law for
algebraic tori*, (1.12) and Lemma 2.12, p. 20. This is the large-ordinate
zero-free region of a fixed unitary Hecke character, expressed for the
meromorphic continuation of its finite Euler product. The constants may depend
on the field and character. -/
theorem finiteHeckeL_colemanRegion_atLarge (χ : U) :
    ∃ c > (0 : ℝ), ∃ T ≥ (0 : ℝ), ∀ L : ℂ → ℂ, MeromorphicNFOn L univ →
      (∀ s : {s : ℂ // 1 < s.re}, L s = finiteHeckeL χ s) →
      ∀ s : ℂ, T ≤ |s.im| → 0 < s.re → 0 < meromorphicOrderAt L s →
        s.re ≤ 1 - c / colemanLogWeight 3 |s.im| := by
  sorry

/-- Coleman's large-ordinate region extends to every positive completed divisor
site for a fixed character. The logarithmic region on the remaining compact
height range allows the constant to absorb a possible exceptional real zero. -/
theorem continuedCompletedHeckeL_colemanZeroGap (χ : U) :
    ∃ c > (0 : ℝ), ∀ z : zeros(χ),
      z.val.re ≤ 1 - c / colemanLogWeight 3 |z.val.im| := by
  obtain ⟨c, hc, T, hT, hreg⟩ := finiteHeckeL_colemanRegion_atLarge χ
  obtain ⟨b, hb, hlow⟩ := translatedLocalTerms_logarithmicZeroGap χ
  obtain ⟨L, hL, hseries⟩ := finiteHeckeL_exists_continuation χ
  let B := 1 + Real.log (1 + T)
  have hB : 0 < B := by
    have := Real.log_nonneg (show 1 ≤ 1 + T by linarith)
    dsimp only [B]
    linarith
  let d := min c (min (1 / 2) ((b / B) / 2))
  have hd : 0 < d := lt_min hc (lt_min (by norm_num) (half_pos (div_pos hb hB)))
  refine ⟨d, hd, fun z ↦ ?_⟩
  let t := |z.val.im|
  have ht : 0 ≤ t := abs_nonneg _
  have hW := half_le_colemanLogWeight (a := 3) (by norm_num) ht
  have hp : 0 < colemanLogWeight 3 t := lt_of_lt_of_le (by norm_num) hW
  by_cases hr : 0 < z.val.re
  · by_cases hlarge : T ≤ t
    · have ho : 0 < meromorphicOrderAt L z.val := by
        rw [meromorphicOrderAt_finiteHeckeL_continuation χ hL.meromorphicOn hseries hr]
        exact translatedLocalTerms_characterZero_order χ z
      exact (hreg L hL hseries z.val hlarge hr ho).trans
        (sub_le_sub_left (div_le_div_of_nonneg_right (min_le_left _ _) hp.le) _)
    · have hpos : 0 < 1 + Real.log (1 + t) := by
        linarith [Real.log_nonneg (show 1 ≤ 1 + t by linarith)]
      have hB' : 1 + Real.log (1 + t) ≤ B := by
        have hh : Real.log (1 + t) ≤ Real.log (1 + T) :=
          Real.log_le_log (by positivity) (by linarith [lt_of_not_ge hlarge])
        dsimp only [B]
        linarith
      have hstep : d / colemanLogWeight 3 t ≤ b / B := by
        apply (div_le_iff₀ hp).mpr
        calc
          d ≤ (b / B) / 2 := (min_le_right _ _).trans (min_le_right _ _)
          _ = (b / B) * (1 / 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hW (div_nonneg hb.le hB.le)
      exact (hlow z).trans (sub_le_sub_left
        (hstep.trans (div_le_div_of_nonneg_left hb.le hpos hB')) _)
  · have hdW : d ≤ colemanLogWeight 3 t :=
      ((min_le_right _ _).trans (min_le_left _ _)).trans hW
    have hquot := (div_le_one hp).mpr hdW
    change z.val.re ≤ 1 - d / colemanLogWeight 3 t
    linarith

local notation "V" => IsDedekindDomain.HeightOneSpectrum (𝓞 F)
local notation "M(" φ ", " c ")" =>
  modulatedFourierMellin m𝔽 univ ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
    μ𝔽 (φ : BruhatCompactSupport C𝔽).val c
local notation "twist(" χ ", " s ")" => ideleClassNormTwist (F := F) χ s
local notation "ord(" χ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "vol₁" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : V) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "archRestricts(" φ ", " a ")" =>
  (∀ (w : InfinitePlace F) (u : w.Completionˣ), (a w).val u =
    (φ : BruhatCompactSupport C𝔽).val (IdeleClassGroup.ofCompletion (𝓞 F) F w u))
local notation "finiteRestricts(" φ ", " b ")" =>
  (∀ (v : V) (u : (v.adicCompletion F)ˣ), (b v).val u =
    (φ : BruhatCompactSupport C𝔽).val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u))
local notation "finiteTerm(" v ", " b ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) /
    (finiteLocalMultiplicativeTamagawaMeasure F v
      ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v 1 b
local notation "localTerms(" φ ", " a ", " b ")" =>
  (M(φ, twist(1, 1 / 2)) + M(φ, twist(1, -1 / 2)) -
    vol₁ * ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
      ∑' v : V, finiteTerm(v, b v)))
local notation "coef(" χ ", " H ", " z ")" =>
  ((ord(χ, (z : ℂ)) : ℤ) : ℂ) * (vol₁ * bilateralLaplace H ((z : ℂ) - 1 / 2))
local notation "mass(" χ ", " z ")" =>
  (ord(χ, (z : ℂ)) : ℝ) / (1 + |(z : ℂ).im|) ^ 2

private theorem translatedLocalTerms_coef_bound (χ : U) (H : ℝ → ℂ)
    (hs : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) (n : ℕ) :
    ∃ B > (0 : ℝ), ∀ z : zeros(χ),
      ‖coef(χ, H, z)‖ * (1 + |z.val.im|) ^ n ≤ B * mass(χ, z) := by
  obtain ⟨A, hA, h⟩ := bilateralLaplace_rapidDecay_on_closedStrip H hs hc
    (a := -(1 / 2)) (b := 1 / 2) (by norm_num) (n + 2)
  refine ⟨(‖vol₁‖ + 1) * A, mul_pos (by positivity) hA, ?_⟩
  intro z
  let x := 1 + |z.val.im|
  have hx : 0 < x := by dsimp only [x]; positivity
  have hz := explicitFormulaCompletedHeckeL_zero_re_mem χ z.property
  have hre : (z.val - 1 / 2).re ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    constructor <;> linarith [hz.1, hz.2]
  have hb : ‖bilateralLaplace H (z.val - 1 / 2)‖ * x ^ (n + 2) ≤ A := by
    simpa [x] using h (z.val - 1 / 2) hre
  have hm : (0 : ℝ) ≤ (ord(χ, z.val) : ℝ) := by exact_mod_cast z.property.le
  rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hm, norm_mul]
  change _ ≤ _ * (_ / x ^ 2)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (pow_pos hx _)).mpr
  calc
    _ = (ord(χ, z.val) : ℝ) * ‖vol₁‖ * (‖bilateralLaplace H (z.val - 1 / 2)‖ * x ^ (n + 2)) := by
      rw [pow_add]
      change (ord(χ, z.val) : ℝ) * (_ * _) * x ^ n * x ^ 2 = _
      ring
    _ ≤ (ord(χ, z.val) : ℝ) * ‖vol₁‖ * A := mul_le_mul_of_nonneg_left hb (mul_nonneg hm (norm_nonneg _))
    _ ≤ _ := by nlinarith [mul_nonneg hm hA.le]

/-- Paper: Theorem B.4.4.7, p. 623, and Proposition B.6.1.1, p. 636, for
the positive log translations of Theorem 12.5.1.1, pp. 519–520.
For each fixed normalized character and compact smooth radial profile, the full
signed local functional admits every fixed root-exponential saving at the
horizontal exponent one half. It includes both polar Mellin terms and the
negative of the norm-one volume times the sum of local principal values. -/
theorem translatedLocalTerms_norm_le_exp_sub_sqrt (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (ψ : PontryaginDual C𝔽) (hψ : ∀ t, ψ (τ t) = 1)
    (H : ℝ → ℂ) (hs : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) (K : ℝ) :
    ∃ D ≥ (0 : ℝ), ∀ (y : ℝ), 0 ≤ y → ∀ (φ : BruhatCompactSupport C𝔽),
      (∀ x, φ.val x = (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y)) →
      ∀ (a : archTest) (b : finiteTest), archRestricts(φ, a) → finiteRestricts(φ, b) →
        ‖localTerms(φ, a, b)‖ ≤ D * Real.exp (y / 2 - K * Real.sqrt y) := by
  obtain ⟨c, hc', hgap⟩ := translatedLocalTerms_logarithmicZeroGap (ψ⁻¹)
  have hat := expSum_norm_le_exp_sub_sqrt
    (fun z : zeros(ψ⁻¹) ↦ z.val) (fun z ↦ coef(ψ⁻¹, H, z)) (fun z ↦ mass(ψ⁻¹, z))
    (explicitFormulaCompletedHeckeL_summable_divisor_div_sq _)
    (fun z ↦ div_nonneg (by exact_mod_cast z.property.le) (by positivity))
    hc' hgap (translatedLocalTerms_coef_bound (ψ⁻¹) H hs hc) K
  obtain ⟨D, hD, hbound⟩ := hat
  exact ⟨D, hD, fun y hy φ hφ a b ha hb ↦ hbound hy (translatedLocalTerms_hasSum τ hτ ψ hψ H hs hc y φ hφ a b ha hb)⟩

/-- For any fixed real k, the endpoint weight permits the further factor
exp(k √y). This holds for every choice of actual Bruhat representatives of the
positive translates and their finite and archimedean restrictions. -/
theorem translatedLocalTerms_integrableOn_exp_sqrt (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (ψ : PontryaginDual C𝔽) (hψ : ∀ t, ψ (τ t) = 1)
    (H : ℝ → ℂ) (hs : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    (φ : ℝ → BruhatCompactSupport C𝔽)
    (hφ : ∀ y : ℝ, 0 ≤ y → ∀ x, (φ y).val x =
      (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y))
    (a : ℝ → archTest) (b : ℝ → finiteTest)
    (ha : ∀ y : ℝ, 0 ≤ y → archRestricts(φ y, a y))
    (hb : ∀ y : ℝ, 0 ≤ y → finiteRestricts(φ y, b y)) (k : ℝ) :
    IntegrableOn (fun y : ℝ ↦ ‖localTerms(φ y, a y, b y)‖ *
      Real.exp (-y / 2 + k * Real.sqrt y)) (Ici 0) := by
  apply integrableOn_expSum_exp_sqrt_of_bounds (fun z : zeros(ψ⁻¹) ↦ z.val)
    (fun z ↦ coef(ψ⁻¹, H, z)) (fun y ↦ localTerms(φ y, a y, b y))
    (fun z ↦ (explicitFormulaCompletedHeckeL_zero_re_mem (ψ⁻¹) z.property).2) ?_ ?_ ?_ k
  · have h := (translatedLocalTerms_hasSum τ hτ ψ hψ H hs hc 0 (φ 0) (hφ 0 le_rfl)
      (a 0) (b 0) (ha 0 le_rfl) (hb 0 le_rfl)).summable.norm
    simpa only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, bilateralLaplace] using h
  · intro y hy
    exact translatedLocalTerms_hasSum τ hτ ψ hψ H hs hc y (φ y) (hφ y hy)
      (a y) (b y) (ha y hy) (hb y hy)
  · intro K
    obtain ⟨D, hD, h⟩ := translatedLocalTerms_norm_le_exp_sub_sqrt τ hτ ψ hψ H hs hc K
    exact ⟨D, hD, fun y hy ↦ h y hy (φ y) (hφ y hy) (a y) (b y) (ha y hy) (hb y hy)⟩

private theorem translatedLocalTerms_gevreyCoef (χ : U) (H : ℝ → ℂ)
    {κ A : ℝ} (hA : 0 < A)
    (hH : ∀ w : ℂ, w.re ∈ Icc (-(1 / 2) : ℝ) (1 / 2) →
      ‖∫ x : ℝ, H x * Complex.exp (w * x)‖ ≤ A * Real.exp (-κ * Real.sqrt |w.im|))
    (z : zeros(χ)) : ‖coef(χ, H, z)‖ ≤ ((‖vol₁‖ + 1) * A) * mass(χ, z) * (1 + |z.val.im|) ^ 2 *
      Real.exp (-κ * Real.sqrt |z.val.im|) := by
  let m : ℝ := ord(χ, z.val)
  let x := 1 + |z.val.im|
  let E := Real.exp (-κ * Real.sqrt |z.val.im|)
  have hx : 0 < x := by dsimp [x]; positivity
  have hm : 0 ≤ m := by dsimp only [m]; exact_mod_cast z.property.le
  have he : 0 ≤ E := (Real.exp_pos _).le
  have hz := explicitFormulaCompletedHeckeL_zero_re_mem χ z.property
  have hre : (z.val - 1 / 2).re ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    constructor <;> linarith [hz.1, hz.2]
  have hcoeff : ‖bilateralLaplace H (z.val - 1 / 2)‖ ≤ A * E := by
    simpa [bilateralLaplace, E] using hH _ hre
  rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hm, norm_mul]
  change m * (‖vol₁‖ * _) ≤ ((‖vol₁‖ + 1) * A) * (m / x ^ 2) * x ^ 2 * E
  calc
    _ ≤ m * (‖vol₁‖ * (A * E)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcoeff (norm_nonneg _)) hm
    _ ≤ m * ((‖vol₁‖ + 1) * (A * E)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hA.le he)) hm
    _ = _ := by field_simp [hx.ne']

/-- A square-root exponential height bound on the bilateral Laplace transform
improves the positive-translate saving to d*y/log(2+y) for the same local
functional. The constant d depends on the fixed field, character and profile. -/
theorem translatedLocalTerms_norm_le_exp_sub_div_log (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (ψ : PontryaginDual C𝔽) (hψ : ∀ t, ψ (τ t) = 1)
    (H : ℝ → ℂ) (hs : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    {κ A : ℝ} (hκ : 0 < κ) (hA : 0 < A)
    (hH : ∀ w : ℂ, w.re ∈ Icc (-(1 / 2) : ℝ) (1 / 2) →
      ‖∫ x : ℝ, H x * Complex.exp (w * x)‖ ≤ A * Real.exp (-κ * Real.sqrt |w.im|)) :
    ∃ d > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ (y : ℝ), 0 ≤ y → ∀ (φ : BruhatCompactSupport C𝔽),
      (∀ x, φ.val x = (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y)) →
      ∀ (a : archTest) (b : finiteTest), archRestricts(φ, a) → finiteRestricts(φ, b) →
        ‖localTerms(φ, a, b)‖ ≤ C * Real.exp (y / 2 - d * y / Real.log (2 + y)) := by
  obtain ⟨c, hc', hgap⟩ := translatedLocalTerms_logarithmicZeroGap (ψ⁻¹)
  obtain ⟨d, hd, C, hC, h⟩ := expSum_norm_le_exp_sub_div_log (fun z : zeros(ψ⁻¹) ↦ z.val)
    (fun z ↦ coef(ψ⁻¹, H, z)) (fun z ↦ mass(ψ⁻¹, z))
    (explicitFormulaCompletedHeckeL_summable_divisor_div_sq _)
    (fun z ↦ div_nonneg (by exact_mod_cast z.property.le) (by positivity))
    hc' hκ (mul_pos (by positivity) hA) hgap (translatedLocalTerms_gevreyCoef _ H hA hH)
  exact ⟨d, hd, C, hC, fun y hy φ hφ a b ha hb ↦ h y hy _
    (translatedLocalTerms_hasSum τ hτ ψ hψ H hs hc y φ hφ a b ha hb)⟩

/-- The Coleman region and square-root exponential transform decay yield a savings
of order `y / colemanLogWeight 2 y` for the genuine signed local terms of each
positive translate. The divisor is that of the inverse normalized character. -/
theorem translatedLocalTerms_norm_le_exp_sub_coleman (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (ψ : PontryaginDual C𝔽) (hψ : ∀ t, ψ (τ t) = 1)
    (H : ℝ → ℂ) (hs : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    {κ A : ℝ} (hκ : 0 < κ) (hA : 0 < A)
    (hH : ∀ w : ℂ, w.re ∈ Icc (-(1 / 2) : ℝ) (1 / 2) →
      ‖∫ x : ℝ, H x * Complex.exp (w * x)‖ ≤ A * Real.exp (-κ * Real.sqrt |w.im|)) :
    ∃ d > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ (y : ℝ), 0 ≤ y → ∀ (φ : BruhatCompactSupport C𝔽),
      (∀ x, φ.val x = (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y)) →
      ∀ (a : archTest) (b : finiteTest), archRestricts(φ, a) → finiteRestricts(φ, b) →
        ‖localTerms(φ, a, b)‖ ≤ C * Real.exp (y / 2 - d * y / colemanLogWeight 2 y) := by
  obtain ⟨c, hc', hgap⟩ := continuedCompletedHeckeL_colemanZeroGap (ψ⁻¹)
  obtain ⟨d, hd, C, hC, h⟩ := expSum_norm_le_exp_sub_coleman (fun z : zeros(ψ⁻¹) ↦ z.val)
    (fun z ↦ coef(ψ⁻¹, H, z)) (fun z ↦ mass(ψ⁻¹, z))
    (explicitFormulaCompletedHeckeL_summable_divisor_div_sq _)
    (fun z ↦ div_nonneg (by exact_mod_cast z.property.le) (by positivity))
    hc' hκ (mul_nonneg (by positivity) hA.le) hgap (translatedLocalTerms_gevreyCoef _ H hA hH)
  exact ⟨d, hd, C, hC, fun y hy φ hφ a b ha hb ↦ h y hy _
    (translatedLocalTerms_hasSum τ hτ ψ hψ H hs hc y φ hφ a b ha hb)⟩

/-- For each fixed normalized character and Gevrey profile, every positive
integral moment of the actual signed geometric expression is integrable at
each strictly smaller Coleman tilt. No regularity of the chosen families
of local restrictions is required. -/
theorem translatedLocalTerms_integrableOn_exp_coleman (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (ψ : PontryaginDual C𝔽) (hψ : ∀ t, ψ (τ t) = 1)
    (H : ℝ → ℂ) (hs : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    {κ A : ℝ} (hκ : 0 < κ) (hA : 0 < A)
    (hH : ∀ w : ℂ, w.re ∈ Icc (-(1 / 2) : ℝ) (1 / 2) →
      ‖∫ x : ℝ, H x * Complex.exp (w * x)‖ ≤ A * Real.exp (-κ * Real.sqrt |w.im|)) :
    ∃ d > (0 : ℝ), ∀ (φ : ℝ → BruhatCompactSupport C𝔽)
      (_hφ : ∀ y ≥ (0 : ℝ), ∀ x, (φ y).val x =
        (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y))
      (a : ℝ → archTest) (b : ℝ → finiteTest)
      (_ha : ∀ y ≥ (0 : ℝ), archRestricts(φ y, a y)) (_hb : ∀ y ≥ (0 : ℝ), finiteRestricts(φ y, b y))
      (n : ℕ), 0 < n → ∀ k : ℝ, k < d →
        IntegrableOn (fun y : ℝ ↦ ‖localTerms(φ y, a y, b y)‖ ^ n *
          Real.exp ((n : ℝ) * (-y / 2 + k * y / colemanLogWeight 2 y))) (Ici 0) := by
  obtain ⟨d, hd, C, hC, hbound⟩ := translatedLocalTerms_norm_le_exp_sub_coleman τ hτ ψ hψ H hs hc hκ hA hH
  refine ⟨d, hd, ?_⟩
  intro φ hφ a b ha hb n hn k hk
  let g (y : ℝ) := ‖localTerms(φ y, a y, b y)‖
  have hbase := (translatedLocalTerms_integrableOn_exp_sqrt τ hτ ψ hψ H hs hc φ hφ a b ha hb 0).aestronglyMeasurable
  have hm : AEStronglyMeasurable g (volume.restrict (Ici 0)) := by
    have hx : Measurable (fun y : ℝ ↦ Real.exp (y / 2)) := by fun_prop
    apply (hbase.mul hx.aestronglyMeasurable).congr (.of_forall fun y ↦ ?_)
    change (g y * Real.exp (-y / 2 + 0 * Real.sqrt y)) * Real.exp (y / 2) = g y
    rw [mul_assoc, ← Real.exp_add, zero_mul, add_zero, neg_div, neg_add_cancel, Real.exp_zero, mul_one]
  exact integrableOn_pow_mul_exp_coleman_of_bound hm (fun y ↦ norm_nonneg _)
    (fun y hy ↦ hbound y hy (φ y) (hφ y hy) (a y) (b y) (ha y hy) (hb y hy)) n hn k hk

/-- At half shift, every fixed smooth profile on a compact positive log interval
with zero positive polar moment has finite square energy and an exact first-order
Abel law for its genuine signed degree-one prime sum. The ordinary logarithmic
region already suffices for this conclusion. -/
theorem firstPrime_polarFree_half_abel_firstOrder (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (ψ : U) (hψ : ∀ t, ψ (τ t) = 1)
    (H : ℝ → ℂ) (hH : ContDiff ℝ ∞ H) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (ht : tsupport H ⊆ Icc u v) (hpolar : bilateralLaplace H (1/2) = 0) :
    let P := fun y : ℝ ↦ firstPrimeDegreeOneSum ψ⁻¹ H y v
    let E := ∫ y in Ici (0 : ℝ), ‖P y‖ ^ 2 * Real.exp (-y)
    IntegrableOn (fun y : ℝ ↦ ‖P y‖ ^ 2 * Real.exp (-y)) (Ici 0) ∧
      (∀ ε > (0 : ℝ), AbelEdge.weightedSquareAbelMean P (1/2) ε ≤ ENNReal.ofReal ε * ENNReal.ofReal E) ∧
      Tendsto (fun ε : ℝ ↦ AbelEdge.weightedSquareAbelMean P (1/2) ε / ENNReal.ofReal ε)
        (𝓝[>] 0) (𝓝 (ENNReal.ofReal E)) := by
  let P := fun y : ℝ ↦ firstPrimeDegreeOneSum ψ⁻¹ H y v
  have hc : HasCompactSupport H := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) ht
  obtain ⟨C, hC, hlocal⟩ := translatedLocalTerms_norm_le_exp_sub_sqrt τ hτ ψ hψ H hH hc 1
  obtain ⟨D, _, hprime⟩ := firstPrime_centered_exp_sub_sqrt_of_localTerms τ hτ ψ hψ H hH hu huv ht 1
    ⟨C, hC, fun y hy φ hφ a b ha hb ↦ hlocal y hy φ hφ a b ha hb⟩
  have hP (y : ℝ) (hy : 0 ≤ y) : ‖P y‖ ≤ D * Real.exp (y / 2 - Real.sqrt y) := by
    change (∫ x : ℝ, H x * Complex.exp ((1/2 : ℂ) * x)) = 0 at hpolar
    simpa only [P, firstPrimePolarMoment, hpolar, mul_zero, ite_self, sub_zero, one_mul] using hprime y hy
  have hm : Measurable P := firstPrimeDegreeOneSum_measurable ψ⁻¹ H hH.continuous.measurable v
  have hgauss : IntegrableOn (fun y : ℝ ↦ Real.exp (-(2 : ℝ) * Real.sqrt y)) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    simpa only [Real.rpow_zero, one_mul, ← Real.sqrt_eq_rpow] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (p := (1/2 : ℝ)) (b := 2)
        (by norm_num) (by norm_num) (by norm_num)
  have hi : IntegrableOn (fun y : ℝ ↦ ‖P y‖ ^ 2 * Real.exp (-y)) (Ici 0) := by
    have hm' : Measurable (fun y : ℝ ↦ ‖P y‖ ^ 2 * Real.exp (-y)) := by fun_prop
    apply (hgauss.const_mul (D ^ 2)).mono' hm'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ici] with y hy
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    calc
      _ ≤ (D * Real.exp (y / 2 - Real.sqrt y)) ^ 2 * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hP y hy) _) (Real.exp_pos _).le
      _ = _ := by
        rw [mul_pow, pow_two (Real.exp _), mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
  refine ⟨hi, ?_⟩
  have h := AbelEdge.weightedSquareAbelMean_firstOrder hm (1/2)
    (by simpa only [show (2 * (1/2 : ℝ)) = 1 by norm_num, neg_one_mul] using hi)
  simpa only [show (2 * (1/2 : ℝ)) = 1 by norm_num, neg_one_mul] using h

section UniversalGevrey

/-! The field is an explicit argument of the following local notations because
the same real profile is selected before the number field. The quadratic
interval construction and its quantitative transform bound are in
`exists_translatedGevreyPolarProfile`. -/

universe u

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "N(" F ", " x ")" => ((ideleClassNorm F x : ℝ≥0) : ℝ)
local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "μ𝔽(" F ")" => ideleClassTamagawaMeasure F
local notation "m𝔽(" F ")" => (continuousIdeleClassNorm F : C𝔽(F) →ₜ* ℝ≥0ˣ)
local notation "vol₁(" F ")" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "mom(" F ", " φ ", " η ", " z ")" =>
  modulatedFourierMellin m𝔽(F) univ ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
    μ𝔽(F) (φ : BruhatCompactSupport C𝔽(F)).val (ideleClassNormTwist (F := F) η z)
local notation "archTest(" F ")" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest(" F ")" => ((v : V(F)) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "archRestricts(" F ", " φ ", " a ")" =>
  (∀ (w : InfinitePlace F) (t : w.Completionˣ), (a w).val t =
    (φ : BruhatCompactSupport C𝔽(F)).val (IdeleClassGroup.ofCompletion (𝓞 F) F w t))
local notation "finiteRestricts(" F ", " φ ", " b ")" =>
  (∀ (v : V(F)) (t : (v.adicCompletion F)ˣ), (b v).val t =
    (φ : BruhatCompactSupport C𝔽(F)).val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v t))
local notation "localPVs(" F ", " a ", " b ")" =>
  ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
    ∑' v : V(F), ((Real.log (v.asIdeal.absNorm : ℝ) /
      (finiteLocalMultiplicativeTamagawaMeasure F v
        ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal : ℝ) : ℂ) *
      finiteConnesWeilPrincipalValue v 1 (b v))
local notation "localTerms(" F ", " φ ", " a ", " b ")" =>
  (mom(F, φ, 1, 1 / 2) + mom(F, φ, 1, -1 / 2) - vol₁(F) * localPVs(F, a, b))
local notation "matches(" F ", " φ ", " ψ ", " G ", " y ")" =>
  (∀ x : C𝔽(F), (φ : BruhatCompactSupport C𝔽(F)).val x = (ψ x : ℂ) * G (Real.log N(F, x) - y))
local notation "polarSites" => ({-(1 / 2), 0, 1 / 2} : Finset ℂ)

private theorem jointDetector_classVolume_ne_zero : vol₁(F) ≠ 0 := by
  rw [normOneIdeleClassTamagawaMeasure_volume]
  have := NumberField.Units.regulator_pos F
  have := NumberField.classNumber_pos F
  have := NumberField.Units.torsionOrder_pos F
  have : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr F) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F))
  exact Complex.ofReal_ne_zero.mpr
    (ENNReal.toReal_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top).ne'

open Classical in
private theorem jointDetector_moment (τ : ℝ≥0ˣ →ₜ* C𝔽(F)) (hτ : RightInverse τ (ideleClassNorm F))
    (ψ η : PontryaginDual C𝔽(F)) (hψ : ∀ t, ψ (τ t) = 1) (hη : ∀ t, η (τ t) = 1)
    (G : ℝ → ℂ) (hs : ContDiff ℝ ∞ G) (hc : HasCompactSupport G)
    (y : ℝ) (φ : BruhatCompactSupport C𝔽(F)) (hφ : matches(F, φ, ψ, G, y)) (w : ℂ) :
    mom(F, φ, η, w) = (if η * ψ = 1 then vol₁(F) else 0) *
      (Complex.exp (w * y) * bilateralLaplace G w) := by
  let g := fun x : ℝ ↦ G (x - y)
  have hgs : ContDiff ℝ ∞ g := hs.comp (contDiff_id.sub contDiff_const)
  have hgc : HasCompactSupport g := hc.comp_homeomorph (Homeomorph.subRight y)
  obtain ⟨φr, hr⟩ := exists_normTest (F := F) g hgs hgc
  have e : mom(F, φ, η, w) = mom(F, φr, η * ψ, w) := by
    simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
    apply integral_congr_ae
    filter_upwards with x
    change φ.val x * ((η x : ℂ) * ((N(F, x) : ℂ) ^ w)) =
      φr.val x * ((((η * ψ) x : Circle) : ℂ) * ((N(F, x) : ℂ) ^ w))
    rw [hφ, hr, show (((η * ψ) x : Circle) : ℂ) = (η x : ℂ) * (ψ x : ℂ) from Circle.coe_mul _ _]
    dsimp only [g]
    ring
  rw [e, normTest_mellin g hgs.continuous φr hr (η * ψ) w]
  by_cases he : η * ψ = 1
  · rw [ite_eq_left he, ite_eq_left (fun t ↦ by rw [he]; rfl)]
    congr 1
    exact grh_shift_integral G hs.continuous _ (fun t ↦ by rw [he]; rfl) y w
  · have hker : ¬ ∀ t : C₁(F), (η * ψ) t.val = 1 := by
      intro h
      apply he
      refine ContinuousMonoidHom.ext fun x ↦ ?_
      let t := ideleClassNorm F x
      have hmem : (τ t)⁻¹ * x ∈ C₁(F) := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hτ t, inv_mul_cancel]
      have hsection : (η * ψ) (τ t) = 1 := by change η _ * ψ _ = 1; rw [hη, hψ, one_mul]
      have hv := h ⟨_, hmem⟩
      change (η * ψ) ((τ t)⁻¹ * x) = 1 at hv
      rw [map_mul, map_inv, hsection, inv_one, one_mul] at hv
      exact hv
    rw [ite_eq_right he, ite_eq_right hker, zero_mul, zero_mul]

/-- Paper: Theorem B.4.4.7, p. 623 and Proposition B.6.1.1, p. 636. One fixed
real profile works for every number field and every section-normalized character.
All positive translates vanish on the norm-one group and kill the three centered
moments in every normalized character. Their signed principal values have a
uniform positive-translate bound, and their selected Mellin transform detects
each site strictly right of the critical line. -/
theorem exists_universalGevrey_signedLocalTerms :
    ∃ H : ℝ → ℝ, let G := fun x : ℝ ↦ (H x : ℂ)
      bilateralLaplace G = translatedIntervalMultiplier quadraticBoxLaplace ∧
      ContDiff ℝ ∞ H ∧ tsupport H ⊆ Icc 2 4 ∧
      (∀ w ∈ polarSites, bilateralLaplace G w = 0) ∧
      (∀ w : ℂ, 0 < |w.re| → |w.re| < 1/2 → bilateralLaplace G w ≠ 0) ∧
      (∀ B : ℝ, 0 ≤ B → ∃ A > (0 : ℝ), ∀ w : ℂ, |w.re| ≤ B →
        ‖bilateralLaplace G w‖ ≤ A * Real.exp (-(Real.log 2 / 4) * Real.sqrt |w.im|)) ∧
      ∀ (F : Type u) [Field F] [NumberField F] (τ : ℝ≥0ˣ →ₜ* C𝔽(F))
        (_hτ : RightInverse τ (ideleClassNorm F)) (ψ : PontryaginDual C𝔽(F)) (_hψ : ∀ t, ψ (τ t) = 1),
        ∃ d > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ y : ℝ, 0 ≤ y →
          (∃ (φ : BruhatCompactSupport C𝔽(F)) (a : archTest(F)) (b : finiteTest(F)),
            matches(F, φ, ψ, G, y) ∧ archRestricts(F, φ, a) ∧ finiteRestricts(F, φ, b)) ∧
          ∀ φ : BruhatCompactSupport C𝔽(F), matches(F, φ, ψ, G, y) →
            (∀ g : C₁(F), φ.val g = 0) ∧
            (∀ η : PontryaginDual C𝔽(F), (∀ t, η (τ t) = 1) →
              ∀ w ∈ polarSites, mom(F, φ, η, w) = 0) ∧
            (∀ ρ : ℂ, 1/2 < ρ.re → ρ.re < 1 → mom(F, φ, ψ⁻¹, ρ - 1/2) ≠ 0) ∧
            ∀ (a : archTest(F)) (b : finiteTest(F)), archRestricts(F, φ, a) → finiteRestricts(F, φ, b) →
              localTerms(F, φ, a, b) = -(vol₁(F) * localPVs(F, a, b)) ∧
              ‖localTerms(F, φ, a, b)‖ ≤ C * Real.exp (y / 2 - d * y / Real.log (2 + y)) := by
  classical
  obtain ⟨H, hMform, hs, ht, hm, hn, he⟩ := exists_translatedGevreyPolarProfile
  let G := fun x : ℝ ↦ (H x : ℂ)
  have hp : ∀ w ∈ polarSites, bilateralLaplace G w = 0 := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    exacts [hm.1, hm.2.1, hm.2.2]
  refine ⟨H, hMform, hs, ht, hp, hn, he, ?_⟩
  intro F _ _ τ hτ ψ hψ
  have hG : ContDiff ℝ ∞ G := Complex.ofRealCLM.contDiff.comp hs
  have hc : HasCompactSupport H := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) ht
  have hGc : HasCompactSupport G := hc.comp_left Complex.ofReal_zero
  obtain ⟨A, hA, hfast⟩ := he (1/2) (by norm_num)
  have hk : 0 < Real.log 2 / 4 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  obtain ⟨d, hd, C, hC, hbound⟩ := translatedLocalTerms_norm_le_exp_sub_div_log τ hτ ψ hψ G hG hGc
    hk hA (fun w hw ↦ hfast w (abs_le.mpr hw))
  refine ⟨d, hd, C, hC, ?_⟩
  intro y hy
  constructor
  · obtain ⟨φ, hφ⟩ := exists_characterNormTest (F := F) ψ (fun x ↦ G (x - y))
      (hG.comp (contDiff_id.sub contDiff_const)) (hGc.comp_homeomorph (Homeomorph.subRight y))
    obtain ⟨a, b, ha, hb, _⟩ := traceFormula_of_half_le τ hτ φ (le_refl (1/2 : ℝ))
    exact ⟨φ, a, b, hφ, ha, hb⟩
  intro φ hφ
  have hM := jointDetector_moment τ hτ ψ
  have hzero (η : PontryaginDual C𝔽(F)) (hη : ∀ t, η (τ t) = 1) (w : ℂ) (hw : w ∈ polarSites) :
      mom(F, φ, η, w) = 0 := by
    rw [hM η hψ hη G hG hGc y φ hφ w, hp w hw, mul_zero, mul_zero]
  refine ⟨?_, hzero, ?_, ?_⟩
  · intro g
    have hx : H (-y) = 0 := image_eq_zero_of_notMem_tsupport (fun hx ↦ by linarith [(ht hx).1])
    simp only [hφ, show ideleClassNorm F g.val = 1 from g.property,
      Units.val_one, NNReal.coe_one, Real.log_one, zero_sub, hx, Complex.ofReal_zero, mul_zero]
  · intro ρ hρ₁ hρ₂
    have hinv (t) : ψ⁻¹ (τ t) = 1 := by change (ψ (τ t))⁻¹ = 1; rw [hψ, inv_one]
    rw [hM ψ⁻¹ hψ hinv G hG hGc y φ hφ _, inv_mul_cancel, ite_eq_left rfl]
    have hr : (ρ - 1/2).re = ρ.re - 1/2 := by simp
    have hpos : 0 < (ρ - 1/2).re := by rw [hr]; linarith
    have hlt : |(ρ - 1/2).re| < 1/2 := by rw [abs_of_pos hpos, hr]; linarith
    exact mul_ne_zero (jointDetector_classVolume_ne_zero (F := F))
      (mul_ne_zero (Complex.exp_ne_zero _) (hn _ (abs_pos.mpr hpos.ne') hlt))
  · intro a b ha hb
    refine ⟨?_, hbound y hy φ hφ a b ha hb⟩
    rw [show (-1/2 : ℂ) = -(1/2) by ring, hzero 1 (by simp) (1/2) (by simp),
      hzero 1 (by simp) (-(1/2)) (by simp)]
    simp

/-- The fixed real profile of `exists_universalGevrey_signedLocalTerms` has the
Coleman rate for every fixed number field and normalized character. The tests,
their vanishing polar moments and their nonvanishing off the centered line
are the same witnesses as in that theorem. -/
theorem exists_universalGevrey_signedLocalTerms_coleman :
    ∃ H : ℝ → ℝ, let G := fun x : ℝ ↦ (H x : ℂ)
      bilateralLaplace G = translatedIntervalMultiplier quadraticBoxLaplace ∧
      ContDiff ℝ ∞ H ∧ tsupport H ⊆ Icc 2 4 ∧
      (∀ w ∈ polarSites, bilateralLaplace G w = 0) ∧
      (∀ w : ℂ, 0 < |w.re| → |w.re| < 1/2 → bilateralLaplace G w ≠ 0) ∧
      (∀ B : ℝ, 0 ≤ B → ∃ A > (0 : ℝ), ∀ w : ℂ, |w.re| ≤ B →
        ‖bilateralLaplace G w‖ ≤ A * Real.exp (-(Real.log 2 / 4) * Real.sqrt |w.im|)) ∧
      ∀ (F : Type u) [Field F] [NumberField F] (τ : ℝ≥0ˣ →ₜ* C𝔽(F))
        (_hτ : RightInverse τ (ideleClassNorm F)) (ψ : PontryaginDual C𝔽(F)) (_hψ : ∀ t, ψ (τ t) = 1),
        ∃ d > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ y : ℝ, 0 ≤ y →
          (∃ (φ : BruhatCompactSupport C𝔽(F)) (a : archTest(F)) (b : finiteTest(F)),
            matches(F, φ, ψ, G, y) ∧ archRestricts(F, φ, a) ∧ finiteRestricts(F, φ, b)) ∧
          ∀ φ : BruhatCompactSupport C𝔽(F), matches(F, φ, ψ, G, y) →
            (∀ g : C₁(F), φ.val g = 0) ∧
            (∀ η : PontryaginDual C𝔽(F), (∀ t, η (τ t) = 1) →
              ∀ w ∈ polarSites, mom(F, φ, η, w) = 0) ∧
            (∀ ρ : ℂ, 1/2 < ρ.re → ρ.re < 1 → mom(F, φ, ψ⁻¹, ρ - 1/2) ≠ 0) ∧
            ∀ (a : archTest(F)) (b : finiteTest(F)), archRestricts(F, φ, a) → finiteRestricts(F, φ, b) →
              localTerms(F, φ, a, b) = -(vol₁(F) * localPVs(F, a, b)) ∧
              ‖localTerms(F, φ, a, b)‖ ≤ C * Real.exp (y / 2 - d * y / colemanLogWeight 2 y) := by
  obtain ⟨H, hform, hs, ht, hp, hn, he, hold⟩ := exists_universalGevrey_signedLocalTerms.{u}
  let G := fun x : ℝ ↦ (H x : ℂ)
  have hG : ContDiff ℝ ∞ G := Complex.ofRealCLM.contDiff.comp hs
  have hc : HasCompactSupport H := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) ht
  obtain ⟨A, hA, hfast⟩ := he (1/2) (by norm_num)
  refine ⟨H, hform, hs, ht, hp, hn, he, ?_⟩
  intro F _ _ τ hτ ψ hψ
  obtain ⟨d, hd, C, hC, hbound⟩ := translatedLocalTerms_norm_le_exp_sub_coleman τ hτ ψ hψ G hG
    (hc.comp_left Complex.ofReal_zero) (div_pos (Real.log_pos (by norm_num)) (by norm_num)) hA
    (fun w hw ↦ hfast w (abs_le.mpr hw))
  obtain ⟨_, _, _, _, htests⟩ := hold F τ hτ ψ hψ
  refine ⟨d, hd, C, hC, fun y hy ↦ ⟨(htests y hy).1, fun φ hφ ↦ ?_⟩⟩
  obtain ⟨hker, hpolar, hdet, hlocal⟩ := (htests y hy).2 φ hφ
  exact ⟨hker, hpolar, hdet, fun a b ha hb ↦
    ⟨(hlocal a b ha hb).1, hbound y hy φ hφ a b ha hb⟩⟩

/-- For the same fixed polar-free profile, the signed residue-degree-one sum of
the inverse normalized character obeys the Coleman pointwise bound and has every
positive integral moment at each smaller tilt. At half shift, its unaveraged
square energy is the exact first-order coefficient of its Abel mean. -/
theorem exists_universalGevrey_firstPrime_coleman :
    ∃ H : ℝ → ℝ, let G := fun x : ℝ ↦ (H x : ℂ)
      bilateralLaplace G = translatedIntervalMultiplier quadraticBoxLaplace ∧
      ContDiff ℝ ∞ H ∧ tsupport H ⊆ Icc 2 4 ∧
      (∀ w ∈ polarSites, bilateralLaplace G w = 0) ∧
      (∀ w : ℂ, 0 < |w.re| → |w.re| < 1/2 → bilateralLaplace G w ≠ 0) ∧
      ∀ (F : Type u) [Field F] [NumberField F] (τ : ℝ≥0ˣ →ₜ* C𝔽(F))
        (_hτ : RightInverse τ (ideleClassNorm F)) (ψ : PontryaginDual C𝔽(F)) (_hψ : ∀ t, ψ (τ t) = 1),
        let P := fun y : ℝ ↦ firstPrimeDegreeOneSum ψ⁻¹ G y 4
        let E := ∫ y in Ici (0 : ℝ), ‖P y‖ ^ 2 * Real.exp (-y)
        ∃ d > (0 : ℝ), ∃ C ≥ (0 : ℝ),
          (∀ y ≥ (0 : ℝ), ‖P y‖ ≤ C * Real.exp (y / 2 - d * y / colemanLogWeight 2 y)) ∧
          (∀ (n : ℕ), 0 < n → ∀ k : ℝ, k < d →
            IntegrableOn (fun y : ℝ ↦ ‖P y‖ ^ n *
              Real.exp ((n : ℝ) * (-y / 2 + k * y / colemanLogWeight 2 y))) (Ici 0)) ∧
          (∀ ε > (0 : ℝ), AbelEdge.weightedSquareAbelMean P (1 / 2) ε ≤
            ENNReal.ofReal ε * ENNReal.ofReal E) ∧
          Tendsto (fun ε : ℝ ↦ AbelEdge.weightedSquareAbelMean P (1 / 2) ε / ENNReal.ofReal ε)
            (𝓝[>] 0) (𝓝 (ENNReal.ofReal E)) := by
  obtain ⟨H, hform, hs, ht, hp, hn, _, hfamilies⟩ := exists_universalGevrey_signedLocalTerms_coleman.{u}
  let G := fun x : ℝ ↦ (H x : ℂ)
  have hG : ContDiff ℝ ∞ G := Complex.ofRealCLM.contDiff.comp hs
  have hGt : tsupport G ⊆ Icc 2 4 := (tsupport_comp_subset Complex.ofReal_zero H).trans ht
  have hhalf : bilateralLaplace G (1/2) = 0 := hp _ (by simp)
  refine ⟨H, hform, hs, ht, hp, hn, ?_⟩
  intro F _ _ τ hτ ψ hψ
  obtain ⟨b, hb, C, hC, hlocal⟩ := hfamilies F τ hτ ψ hψ
  let d := min b (1/4)
  have hd : 0 < d := lt_min hb (by norm_num)
  let W (y : ℝ) := Real.exp (y / 2 - d * y / colemanLogWeight 2 y)
  have hW (y : ℝ) (hy : 0 ≤ y) : 1 ≤ W y := by
    have hh := half_le_colemanLogWeight (a := 2) (by norm_num) hy
    have hpos : 0 < colemanLogWeight 2 y := lt_of_lt_of_le (by norm_num) hh
    have hdw : d / colemanLogWeight 2 y ≤ 1/2 :=
      (div_le_iff₀ hpos).mpr ((min_le_right _ _).trans (by linarith))
    have hmul := mul_le_mul_of_nonneg_right hdw hy
    rw [div_mul_eq_mul_div] at hmul
    exact Real.one_le_exp (by linarith)
  obtain ⟨D, hD, hprime⟩ := firstPrime_centered_bound_of_localTerms τ hτ ψ hψ G hG
    (u := 2) (v := 4) (by norm_num) (by norm_num) hGt W zero_lt_one hC hW
    (fun y hy φ hφ a b ha hb ↦ by
      obtain ⟨_, _, _, hbound⟩ := (hlocal y hy).2 φ hφ
      exact ((hbound a b ha hb).2).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (sub_le_sub_left (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hy)
          ((by norm_num : (0 : ℝ) ≤ 1/2).trans (half_le_colemanLogWeight (by norm_num) hy))) _)) hC))
  let P := fun y : ℝ ↦ firstPrimeDegreeOneSum ψ⁻¹ G y 4
  have hP (y : ℝ) (hy : 0 ≤ y) : ‖P y‖ ≤ D * W y := by
    have hmoment : (∫ x : ℝ, G x * Complex.exp ((1/2 : ℂ) * x)) = 0 := hhalf
    simpa only [P, firstPrimePolarMoment, hmoment, mul_zero, ite_self, sub_zero] using hprime y hy
  have hmP : Measurable P := firstPrimeDegreeOneSum_measurable ψ⁻¹ G hG.continuous.measurable 4
  have hpow := integrableOn_pow_mul_exp_coleman_of_bound hmP.norm.aestronglyMeasurable
    (fun y ↦ norm_nonneg (P y)) hP
  have hfirst := firstPrime_polarFree_half_abel_firstOrder τ hτ ψ hψ G hG
    (u := 2) (v := 4) (by norm_num) (by norm_num) hGt hhalf
  exact ⟨d, hd, D, hD, hP, hpow, hfirst.2⟩

end UniversalGevrey

end PositiveTranslations

/-- Paper: (12.5.1.4), p. 520. The smoothened geometric diagonal is Haar-integrable, and the
strip zero terms sum absolutely to its negative integral.
Deviation: As in §12.5 of the library, a measurable D′-sequence specifies the smoothening,
and the sum uses the closed strip with strict reciprocal-weight multiplicities on its edges.
It agrees with the printed interior sum when both edges are zero-free.
The projective kernel above supplies the witness in the smoothened diagonal formula. -/
theorem hasSum_stripZeros_neg_integral_smoothenedDiagonal_of_vanishing
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s)
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    let hK := exists_projectiveKernel_stripTestAction_spectralProjection φ hφ hα hs
    let diagonal (x : C𝔽) := dSequenceKernelSmoothening μ𝔽 U
      (globalStripGeometricKernel (F := F) (1 / 2) hα.le hs₁(hs) φ hK) (x, x)
    let shift (b t : ℝ) := (b : ℂ) + (t : ℂ) * Complex.I
    let order (η : PontryaginDual C𝔽) := meromorphicOrderAt (continuedCompletedHeckeL η)
    let Z := {z : PontryaginDual C₁ × ℝ × ℝ //
      z.2.1 ∈ Icc (-α) α ∧ 0 < order (χ z.1) (shift (1 / 2 + z.2.1) z.2.2)}
    let term (z : Z) := ((spectralStripMultiplicity α s z.val.2.1
      (order (χ z.val.1) (shift (1 / 2 + z.val.2.1) z.val.2.2)).untop₀.toNat : ℕ) : ℂ) *
      modulatedFourierMellin m𝔽 univ ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
        μ𝔽 φ.val (ideleClassNormTwist (χ z.val.1) (shift z.val.2.1 z.val.2.2))
    Integrable diagonal μ𝔽 ∧ Summable (fun z ↦ ‖term z‖) ∧
      HasSum term (-(∫ x, diagonal x ∂μ𝔽)) :=
  hasSum_stripZeros_neg_integral_smoothenedDiagonal φ hφ χ hχ hα hs
    (exists_projectiveKernel_stripTestAction_spectralProjection φ hφ hα hs) U hU hBorel

/-! ## Localizing the kernel condition

Tests supported in any prescribed nonempty open set of log norms suffice to check the kernel condition.
-/

section KernelLocalization

open scoped ContDiff

local notation "ℓ" => logIdeleClassNorm F
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 ℓ (-α) α s
local notation "A(" ha ", " hs ", " φ ")" =>
  hardySobolevTestAction μ𝔽 m𝔽 _ _ _ ((neg_nonpos.mpr ha).trans ha) hs φ
local notation "T(" ha ", " hs ", " g ")" =>
  hardySobolevTranslation μ𝔽 m𝔽 _ _ _ ((neg_nonpos.mpr ha).trans ha) hs g
local notation "kerExists(" ha ", " hs ", " P ", " φ ")" =>
  (∃ K, sobolevProjectiveKernelOperator (F := F) ha hs K = (A(ha, hs, φ)).comp P)

private theorem kernelLocalization_exists_translate (g : C𝔽) (φ : BruhatCompactSupport C𝔽) :
    ∃ ψ : BruhatCompactSupport C𝔽, ∀ x, ψ.val x = φ.val (g⁻¹ * x) := by
  have hφ := modulationWeight_mem_schwartzBruhat m𝔽 univ ⟨0, mem_univ _⟩
    ⟨φ.val, bruhatCompactSupport_le_modulatedExponentialDecay m𝔽 univ
      ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
      (fun t ↦ ⟨QuotientGroup.mk (canonicalIdeleNormSection F t),
        canonicalIdeleNormSection_rightInverse F t⟩) φ.property⟩
  rw [modulationWeight_zero] at hφ
  let f : SchwartzBruhat C𝔽 := ⟨φ.val, hφ⟩
  have hsm := schwartzBruhat_isBruhatSmooth (schwartzBruhatTranslate g f)
  have hc := (show HasCompactSupport φ.val from φ.property.2).comp_homeomorph
    (Homeomorph.mulLeft g⁻¹)
  exact ⟨⟨_, (mem_bruhatSmoothSubmodule_iff _).mpr hsm, hc⟩, fun _ ↦ rfl⟩

/-- Left translating a test postcomposes its weighted strip convolution with the same
translation. -/
theorem stripTestAction_translate {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (g : C𝔽) (φ ψ : BruhatCompactSupport C𝔽) (hψ : ∀ x, ψ.val x = φ.val (g⁻¹ * x)) :
    A(ha, hs, ψ) = (T(ha, hs, g)).comp (A(ha, hs, φ)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
  have hφ := hardySobolevTestAction_apply μ𝔽 m𝔽 _ _ _ ((neg_nonpos.mpr ha).trans ha) hs φ u
  have htr := (measurePreserving_mul_left μ𝔽 g⁻¹).quasiMeasurePreserving.ae_eq_comp hφ
  have ht := hardySobolevTranslation_apply μ𝔽 m𝔽 _ _ _ ((neg_nonpos.mpr ha).trans ha) hs g
    (A(ha, hs, φ) u)
  filter_upwards [hardySobolevTestAction_apply μ𝔽 m𝔽 _ _ _ ((neg_nonpos.mpr ha).trans ha) hs ψ u,
    htr, ht] with x hx hy hz
  refine hx.trans ((?_ : lcaConvolution μ𝔽 ψ.val u x =
    lcaConvolution μ𝔽 φ.val u (g⁻¹ * x)).trans (hy.symm.trans hz.symm))
  unfold lcaConvolution
  rw [← integral_mul_left_eq_self (fun y ↦ ψ.val y * u (y⁻¹ * x)) g]
  apply integral_congr_ae (.of_forall fun y ↦ ?_)
  rw [hψ, inv_mul_cancel_left, mul_inv_rev, mul_assoc]

private theorem kernelLocalization_nuclear_iff {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (B : W(α, s) →L[ℂ] W(α, s)) :
    (∃ K, sobolevProjectiveKernelOperator (F := F) ha hs K = B) ↔ IsNuclearOperator B := by
  refine ⟨fun ⟨K, hK⟩ ↦ (existsUnique_sobolevProjectiveKernel_iff_nuclear ha hs B).mp
    ⟨K, hK, fun L hL ↦ sobolevProjectiveKernelOperator_injective ha hs (hL.trans hK.symm)⟩,
    fun h ↦ ((existsUnique_sobolevProjectiveKernel_iff_nuclear ha hs B).mpr h).exists⟩

/-- Translating a test preserves projective kernel existence after any fixed input
operator on the strip. The inverse translation gives the converse. -/
theorem stripTestAction_projectiveKernel_translate_iff {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (P : W(α, s) →L[ℂ] W(α, s)) (g : C𝔽) (φ ψ : BruhatCompactSupport C𝔽)
    (hψ : ∀ x, ψ.val x = φ.val (g⁻¹ * x)) :
    kerExists(ha, hs, P, ψ) ↔ kerExists(ha, hs, P, φ) := by
  have h (g : C𝔽) (f k : BruhatCompactSupport C𝔽) (hk : ∀ x, k.val x = f.val (g⁻¹ * x))
      (hK : kerExists(ha, hs, P, f)) : kerExists(ha, hs, P, k) := by
    apply (kernelLocalization_nuclear_iff ha hs _).mpr
    rw [stripTestAction_translate ha hs g f k hk]
    exact mul_mem_nuclearEndomorphisms_left _ ⟨_, (kernelLocalization_nuclear_iff ha hs _).mp hK⟩
  exact ⟨h g⁻¹ ψ φ (fun x ↦ by simp only [inv_inv, hψ, inv_mul_cancel_left]), h g φ ψ hψ⟩

/-- For a translated test the trace norm on the strip is bounded by the endpoint
exponential times the Sobolev polynomial. This applies to any fixed input operator. -/
theorem stripTestAction_translate_traceNorm_le {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (P : W(α, s) →L[ℂ] W(α, s)) (g : C𝔽) (φ ψ : BruhatCompactSupport C𝔽)
    (hψ : ∀ x, ψ.val x = φ.val (g⁻¹ * x)) (N : nuclearEndomorphisms (W(α, s)))
    (hN : N.val = (A(ha, hs, φ)).comp P) :
    ∃ M : nuclearEndomorphisms (W(α, s)), M.val = (A(ha, hs, ψ)).comp P ∧
      traceNorm M ≤ Real.exp (α * |ℓ g|) * (1 + |ℓ g|) ^ (s / 2) * traceNorm N := by
  let T := T(ha, hs, g)
  refine ⟨⟨T * N.val, mul_mem_nuclearEndomorphisms_left T N⟩, ?_, ?_⟩
  · change T * N.val = _
    rw [hN, stripTestAction_translate ha hs g φ ψ hψ]
    rfl
  · have hn : 0 ≤ traceNorm N := by
      let : Norm (nuclearEndomorphisms (W(α, s))) := ⟨traceNorm⟩
      exact (traceNorm_normedSpaceCore (H := W(α, s))).norm_nonneg N
    refine (traceNorm_mul_left_le T N).trans (mul_le_mul_of_nonneg_right ?_ hn)
    apply (norm_hardySobolevTranslation_le μ𝔽 m𝔽 (-α) α s _ hs g).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    apply max_le <;> apply Real.exp_le_exp.mpr
    · calc -α * ℓ g = α * (-ℓ g) := by ring
           _ ≤ α * |ℓ g| := mul_le_mul_of_nonneg_left (neg_le_abs _) ha
    · exact mul_le_mul_of_nonneg_left (le_abs_self _) ha

private theorem kernelLocalization_continuous_log : Continuous (ℓ : C𝔽 → ℝ) :=
  (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).log
    fun g ↦ NNReal.coe_ne_zero.mpr (m𝔽 g).ne_zero

private theorem kernelLocalization_log_mul (g x : C𝔽) : ℓ (g * x) = ℓ g + ℓ x := by
  change Real.log ((ideleClassNorm F (g * x)).val : ℝ) = _
  rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
    (NNReal.coe_ne_zero.mpr (ideleClassNorm F g).ne_zero)
    (NNReal.coe_ne_zero.mpr (ideleClassNorm F x).ne_zero)]

private theorem kernelLocalization_log_surjective : Function.Surjective (ℓ : C𝔽 → ℝ) := by
  intro t
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let g : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F (e t))
  refine ⟨g, ?_⟩
  change Real.log ((ideleClassNorm F g).val : ℝ) = _
  rw [show ideleClassNorm F g = e t from canonicalIdeleNormSection_rightInverse F (e t)]
  exact Real.log_exp _


open scoped Manifold in
private theorem kernelLocalization_real_partition {K U : Set ℝ} (hc : IsCompact K)
    (ho : IsOpen U) {u : ℝ} (hu : u ∈ U) :
    ∃ (S : Finset ℝ) (ρ : S → ℝ → ℝ), (∀ i, ContDiff ℝ ∞ (ρ i)) ∧
      (∀ i t, t ∈ tsupport (ρ i) → (u - i.val) + t ∈ U) ∧
      ∀ t ∈ K, ∑ i, ρ i t = 1 := by
  classical
  let V (t : ℝ) := (fun x : ℝ ↦ (u - t) + x) ⁻¹' U
  have hV (t : ℝ) : IsOpen (V t) := ho.preimage (continuous_const.add continuous_id)
  obtain ⟨S, hS⟩ := hc.elim_finite_subcover V hV fun t _ ↦
    mem_iUnion.mpr ⟨t, by simpa only [V, mem_preimage, sub_add_cancel] using hu⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℝ) hc.isClosed
    (fun i : S ↦ V i.val) (fun i ↦ hV i.val) (by simpa only [iUnion_subtype] using hS)
  refine ⟨S, fun i t ↦ ρ i t, fun i ↦ contMDiff_iff_contDiff.mp (ρ i).contMDiff,
    fun i _ ht ↦ hρ i ht, fun t ht ↦ ?_⟩
  rw [← finsum_eq_sum_of_fintype]
  exact ρ.sum_eq_one ht

private def kernelLocalization_profile (φ : BruhatCompactSupport C𝔽) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) : BruhatCompactSupport C𝔽 :=
  ⟨fun x ↦ (r (ℓ x) : ℂ) * φ.val x, (mem_bruhatSmoothSubmodule_iff _).mpr fun p ↦
    isBruhatContDiff_mul (isBruhatSmooth_logProfile m𝔽 (Complex.ofRealCLM.contDiff.comp hr) p)
      ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1 p),
    (show HasCompactSupport φ.val from φ.property.2).mul_left⟩

private theorem kernelLocalization_profile_support (φ : BruhatCompactSupport C𝔽)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) :
    tsupport (kernelLocalization_profile φ r hr).val ⊆ ℓ ⁻¹' tsupport r :=
  tsupport_mul_subset_left.trans ((tsupport_comp_subset_preimage
    (fun t : ℝ ↦ (r t : ℂ)) kernelLocalization_continuous_log).trans
    (preimage_mono (tsupport_comp_subset Complex.ofReal_zero r)))

private theorem kernelLocalization_profile_sum {ι : Type*} [Fintype ι] (φ : BruhatCompactSupport C𝔽)
    (r : ι → ℝ → ℝ) (hr : ∀ i, ContDiff ℝ ∞ (r i))
    (h1 : ∀ t ∈ ℓ '' tsupport φ.val, ∑ i, r i t = 1) :
    φ = ∑ i, kernelLocalization_profile φ (r i) (hr i) := by
  classical
  apply Subtype.ext
  funext x
  let ev : BruhatCompactSupport C𝔽 →+ ℂ :=
    { toFun k := k.val x, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  change φ.val x = ev (∑ i, kernelLocalization_profile φ (r i) (hr i))
  rw [map_sum]
  change φ.val x = ∑ i, (r i (ℓ x) : ℂ) * φ.val x
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  by_cases hx : x ∈ tsupport φ.val
  · rw [h1 _ (mem_image_of_mem ℓ hx), Complex.ofReal_one, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

private theorem kernelLocalization_shift_support {U : Set ℝ} (d : ℝ) (f : BruhatCompactSupport C𝔽)
    (hf : ∀ x ∈ tsupport f.val, d + ℓ x ∈ U) :
    ∃ (g : C𝔽) (ψ : BruhatCompactSupport C𝔽), tsupport ψ.val ⊆ ℓ ⁻¹' U ∧
      ∀ x, f.val x = ψ.val (g⁻¹ * x) := by
  obtain ⟨g, hg⟩ := kernelLocalization_log_surjective (F := F) d
  obtain ⟨ψ, hψ⟩ := kernelLocalization_exists_translate g f
  refine ⟨g⁻¹, ψ, ?_, fun x ↦ by simp only [inv_inv, hψ, inv_mul_cancel_left]⟩
  intro x hx
  have he : ψ.val = f.val ∘ (fun y ↦ g⁻¹ * y) := funext hψ
  have hy := hf (g⁻¹ * x) (tsupport_comp_subset_preimage f.val
    (continuous_const.mul continuous_id) (he ▸ hx))
  rwa [← hg, ← kernelLocalization_log_mul, mul_inv_cancel_left] at hy

/-- A compact Bruhat test is a finite sum of translates of tests supported in any
prescribed nonempty open log-norm set. The summands and translations depend only on
the test and the set, so the same decomposition works at every strip width. -/
theorem bruhatCompactSupport_finite_sum_translates_of_logNorm {U : Set ℝ} (ho : IsOpen U)
    (hne : U.Nonempty) (φ : BruhatCompactSupport C𝔽) :
    ∃ (S : Finset ℝ) (f ψ : S → BruhatCompactSupport C𝔽) (g : S → C𝔽),
      φ = ∑ i, f i ∧ (∀ i, tsupport (ψ i).val ⊆ ℓ ⁻¹' U) ∧
      ∀ i x, (f i).val x = (ψ i).val ((g i)⁻¹ * x) := by
  classical
  obtain ⟨u, hu⟩ := hne
  have hc : IsCompact (ℓ '' tsupport φ.val) :=
    (show HasCompactSupport φ.val from φ.property.2).image kernelLocalization_continuous_log
  obtain ⟨S, ρ, hr, hsup, hsum⟩ := kernelLocalization_real_partition hc ho hu
  let f (i : S) := kernelLocalization_profile φ (ρ i) (hr i)
  have piece (i : S) := kernelLocalization_shift_support (u - i.val) (f i)
    (fun x hx ↦ hsup i (ℓ x) (kernelLocalization_profile_support φ (ρ i) (hr i) hx))
  choose g ψ hψ he using piece
  exact ⟨S, f, ψ, g, kernelLocalization_profile_sum φ ρ hr hsum, hψ, he⟩

private theorem kernelLocalization_sum {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (P : W(α, s) →L[ℂ] W(α, s)) {ι : Type*} [Fintype ι] (f : ι → BruhatCompactSupport C𝔽)
    (h : ∀ i, kerExists(ha, hs, P, f i)) : kerExists(ha, hs, P, ∑ i, f i) := by
  classical
  choose kernels hk using h
  refine ⟨∑ i, kernels i, ?_⟩
  rw [map_sum, map_sum]
  change ∑ i, sobolevProjectiveKernelOperator (F := F) ha hs (kernels i) =
    (∑ i, (A(ha, hs, f i) : W(α, s) →L[ℂ] W(α, s))).comp P
  apply ContinuousLinearMap.ext
  intro v
  simp only [sum_apply, hk]
  change ∑ i, A(ha, hs, f i) (P v) =
    (∑ i, (A(ha, hs, f i) : W(α, s) →L[ℂ] W(α, s))) (P v)
  rw [sum_apply]

/-- At fixed strip and input operator, it suffices to test a single prescribed nonempty
open set of log norms. -/
theorem stripTestAction_projectiveKernel_iff_support_in_open {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (P : W(α, s) →L[ℂ] W(α, s)) {U : Set ℝ} (ho : IsOpen U) (hne : U.Nonempty) :
    (∀ φ : BruhatCompactSupport C𝔽, kerExists(ha, hs, P, φ)) ↔
      ∀ φ : BruhatCompactSupport C𝔽, tsupport φ.val ⊆ ℓ ⁻¹' U → kerExists(ha, hs, P, φ) := by
  refine ⟨fun h φ _ ↦ h φ, ?_⟩
  intro h φ
  obtain ⟨S, f, ψ, g, hsum, hsup, htr⟩ := bruhatCompactSupport_finite_sum_translates_of_logNorm ho hne φ
  rw [hsum]
  exact kernelLocalization_sum ha hs P f fun i ↦
    (stripTestAction_projectiveKernel_translate_iff ha hs P (g i) (ψ i) (f i) (htr i)).mpr (h _ (hsup i))

/-- Paper: (12.5.1.4), p. 520. The kernel assertion for all tests vanishing on the
norm-one classes is equivalent to testing any nonempty open set of log norms. In
particular a fixed short interval, or an arbitrary far half-line, suffices. -/
theorem exists_projectiveKernel_stripTestAction_spectralProjection_iff_support_in_open
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) {U : Set ℝ} (ho : IsOpen U) (hne : U.Nonempty) :
    let hs' : 0 ≤ s := (by norm_num : (0 : ℝ) ≤ 3).trans hs
    let P := spectralProjection (F := F) (1 / 2) hα.le hs'
    (∀ φ : BruhatCompactSupport C𝔽, (∀ g : C₁, φ.val g = 0) → kerExists(hα.le, hs', P, φ)) ↔
      ∀ φ : BruhatCompactSupport C𝔽, tsupport φ.val ⊆ ℓ ⁻¹' U → kerExists(hα.le, hs', P, φ) := by
  intro hs' P
  apply Iff.trans _ (stripTestAction_projectiveKernel_iff_support_in_open hα.le hs' P ho hne)
  refine ⟨fun h ↦ ?_, fun h φ _ ↦ h φ⟩
  apply (stripTestAction_projectiveKernel_iff_support_in_open hα.le hs' P isOpen_Ioi
    (nonempty_Ioi : (Ioi (0 : ℝ)).Nonempty)).mpr
  intro φ hφ
  apply h φ
  intro g
  apply image_eq_zero_of_notMem_tsupport
  intro hg
  have hx : 0 < ℓ g.val := hφ hg
  change 0 < Real.log ((ideleClassNorm F g.val).val : ℝ) at hx
  rw [g.property] at hx
  simp at hx

end KernelLocalization

end RiemannMasullo.Isolated
