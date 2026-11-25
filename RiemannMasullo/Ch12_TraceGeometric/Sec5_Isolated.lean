module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5_FirstPrimeAbel
public import RiemannMasullo.ForMathlib.Analysis.Fourier.QuadraticBoxProfile
import Mathlib.Geometry.Manifold.PartitionOfUnity
public import RiemannMasullo.Ch12_TraceGeometric.Sec5

/-! # Isolated statements of §12.5

Statements of the section that are neither proved nor refuted and that nothing else in Lean
uses, with what follows from them (`AGENTS.md`, "False statements and gaps"). Nothing imports
this file.

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
Gap: The projective norm estimate for the geometric component of the output is missing.
Nothing in the Lean uses this statement, and it is not known how it connects with the rest of
the proof in Lean; in the paper it is used on pp. 520, 522. -/
theorem exists_projectiveKernel_stripTestAction_spectralProjection
    (φ : BruhatCompactSupport C𝔽) (_hφ : ∀ g : C₁, φ.val g = 0)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) :
    ∃ K, sobolevProjectiveKernelOperator (F := F) hα.le hs₀(hs) K =
      (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα.le).trans hα.le) hs₀(hs) φ).comp
        (spectralProjection (F := F) (1 / 2) hα.le hs₀(hs)) := by
  sorry

/-- Paper: (12.5.1.4), p. 520. The smoothened geometric diagonal is Haar-integrable, and the
strip zero terms sum absolutely to its negative integral.
Deviation: As in §12.5 of the library, a measurable D′-sequence specifies the smoothening,
and the sum uses the closed strip with strict reciprocal-weight multiplicities on its edges.
It agrees with the printed interior sum when both edges are zero-free.
It is proved from the kernel existence statement above, which is open, so it is no more
established than that statement. Nothing in the Lean uses it. -/
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
