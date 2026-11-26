module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5_SharpOrbitalDiagonal
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_TraceClass
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # Signed trace comparison at moving and averaged strip widths

Fix a compact Bruhat test and subtract the identity logarithm and both polar
moments from its sharp local orbital masses. The signed discrepancy with the
global quotient trace tends to zero as the half-width tends to one half.

At fixed thin widths this discrepancy can retain exterior zeros and partial
boundary multiplicities. Its integral over (u, v] has an absolutely convergent
formula: each zero contributes its full complex Mellin weight times the length
of the widths in the interval below its absolute offset. The Sobolev order may
vary arbitrarily above one.
-/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b
  instSpectralQuotientPolynormableSec3 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSIdeleLocallyCompactSec1
  instSIdeleT2Sec4

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => continuousIdeleClassNorm F
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Hₛ" => sProjectedDiagonal F S
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "volS" => (((sLocalNormOneQuotientMeasure F S) univ).toReal : ℂ)
local notation "volF" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "normR(" g ")" => (((ideleClassNorm F g).val : ℝ))
local notation "rootS(" g ")" => (Real.sqrt (((sIdeleNorm F S g).val : ℝ)) : ℂ)
local notation "classAtS(" g ")" => (QuotientGroup.mk (sIdeleInsertion F S g) : C𝔽)
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "stripQ(" hα ", " hs ")" =>
  spectralSobolevQuotient F (1 / 2) (hStrip(hα)) (le_of_lt (zero_lt_one.trans hs))
local notation "stripAction(" hα ", " hs ", " φ ")" =>
  spectralConvolution (F := F) (1 / 2) (hStrip(hα)) (le_of_lt (zero_lt_one.trans hs)) φ

local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" ψ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) ψ) z
local notation "Sites(" χ ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  0 < order(χ z.1, shift(1 / 2 + z.2.1, z.2.2))}
local notation "mult(" χ ", " z ")" =>
  (order(χ (z).val.1, shift(1 / 2 + (z).val.2.1, (z).val.2.2))).untop₀.toNat
local notation "sample(" φ ", " χ ", " z ")" => modulatedFourierMellin m𝔽 univ
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽
  (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (χ (z).val.1)
    (shift((z).val.2.1, (z).val.2.2)))

/-- Hilbert trace of the actual nuclear strip convolution at the half twist. -/
def halfTwistStripTrace {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽) : ℂ :=
  hilbertTrace (H := stripQ(hα, hs)) ⟨stripAction(hα, hs, φ),
    spectralStripConvolution_nuclear_of_summable_clusterTraceNorms (1 / 2) hα
      (zero_lt_one.trans hs).le φ⟩

/-- Identify the canonical trace with any nuclear representative of its convolution. -/
theorem halfTwistStripTrace_eq_hilbertTrace {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s)
    (φ : BruhatCompactSupport C𝔽) (T : nuclearEndomorphisms stripQ(ha,hs))
    (hT : T.val = stripAction(ha,hs,φ)) : halfTwistStripTrace (F := F) ha hs φ = hilbertTrace T := by
  apply congrArg hilbertTrace
  exact Subtype.ext hT.symm

private theorem site_interior (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (z : Sites(χ)) :
    |z.val.2.1| < (1 / 2 : ℝ) := by
  let ψ := χ z.val.1
  let w := shift(1 / 2 + z.val.2.1, z.val.2.2)
  have hz : 0 < order(ψ, w) := z.property
  have upper (η : PontryaginDual C𝔽) (u : ℂ) (hu : 0 < order(η, u)) : u.re < 1 := by
    rcases le_or_gt u.re 0 with h | h
    · exact h.trans_lt zero_lt_one
    obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec η
    exact completedHeckeL_continuation_zeros η _ hL heq h hu
  obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec ψ
  obtain ⟨hD, hd⟩ := continuedCompletedHeckeL_spec ψ⁻¹
  obtain ⟨ε, hε, hne, hfe⟩ := completedHeckeL_continuation_functionalEquation ψ _ _ hL heq hD hd
  have hcomp : meromorphicOrderAt (fun s ↦ continuedCompletedHeckeL ψ⁻¹ (1 - s)) w =
      order(ψ⁻¹,1 - w) := by
    simpa [Function.comp_def] using meromorphicOrderAt_comp_of_deriv_ne_zero
      (f := continuedCompletedHeckeL ψ⁻¹) (show AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) w by fun_prop)
      (show deriv (fun s : ℂ ↦ 1 - s) w ≠ 0 by simp)
  rw [show (fun s ↦ continuedCompletedHeckeL ψ⁻¹ (1 - s)) = ε * continuedCompletedHeckeL ψ
    from funext hfe, meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt w) (hne w)] at hcomp
  have hu := upper ψ w hz
  have hl := upper ψ⁻¹ (1 - w) (hcomp ▸ hz)
  have hw : w.re = 1 / 2 + z.val.2.1 := by simp [w]
  rw [Complex.sub_re, Complex.one_re, hw] at hl
  rw [hw] at hu
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

private theorem hasSum_width (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (φ : BruhatCompactSupport C𝔽) :
    HasSum (fun z : Sites(χ) ↦ (spectralStripMultiplicity α s z.val.2.1 (mult(χ, z)) : ℂ) *
      sample(φ, χ, z)) (halfTwistStripTrace hα hs φ) := by
  let Z := {z : PontryaginDual C₁ × ℝ × ℝ // z.2.1 ∈ Icc (-α) α ∧
    0 < order(χ z.1, shift(1 / 2 + z.2.1, z.2.2))}
  let e : Z → Sites(χ) := fun z ↦ ⟨z.val, z.property.2⟩
  have he : Injective e := fun _ _ h ↦ Subtype.ext (congrArg (fun z : Sites(χ) ↦ z.val) h)
  apply (he.hasSum_iff (fun z hz ↦ ?_)).mp
  · exact (spectralStripConvolution_trace (F := F) (1 / 2) χ hχ hα hs φ
      ⟨_, spectralStripConvolution_nuclear_of_summable_clusterTraceNorms (1 / 2) hα
        (zero_lt_one.trans hs).le φ⟩ rfl).2
  · have hout : z.val.2.1 ∉ Icc (-α) α :=
      fun h ↦ hz ⟨⟨z.val, h, z.property⟩, Subtype.ext rfl⟩
    have hi : ¬ (-α < z.val.2.1 ∧ z.val.2.1 < α) := fun h ↦ hout ⟨h.1.le, h.2.le⟩
    have hb : ¬ (z.val.2.1 = -α ∨ z.val.2.1 = α) := by
      rintro (h | h) <;> apply hout <;> rw [h] <;> constructor <;> linarith
    simp [spectralStripMultiplicity, hi, hb]

private theorem hasSum_full (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (φ : BruhatCompactSupport C𝔽) :
    HasSum (fun z : Sites(χ) ↦ (mult(χ, z) : ℂ) * sample(φ, χ, z))
      (halfTwistStripTrace (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) < 3) φ) :=
  (hasSum_width χ hχ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) < 3) φ).congr_fun
    (fun z ↦ by rw [spectralStripMultiplicity_interior (abs_lt.mp (site_interior χ z))])

private theorem multiplicity_le (a s b : ℝ) (n : ℕ) : spectralStripMultiplicity a s b n ≤ n := by
  unfold spectralStripMultiplicity spectralBoundaryMultiplicity
  split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _

/-- Paper: §12.3, p. 514, as used on p. 520. At a fixed half-width, the signed
wide-minus-narrow quotient trace counts exactly the missing multiplicity at
each zero, including a possible partial loss on the boundary. -/
theorem hasSum_halfTwistStripTrace_defect (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (φ : BruhatCompactSupport C𝔽)
    {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s) :
    HasSum (fun z : Sites(χ) ↦
      ((mult(χ, z) - spectralStripMultiplicity a s z.val.2.1 (mult(χ, z)) : ℕ) : ℂ) * sample(φ, χ, z))
      (halfTwistStripTrace (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) < 3) φ -
        halfTwistStripTrace ha hs φ) :=
  ((hasSum_full χ hχ φ).sub (hasSum_width χ hχ ha hs φ)).congr_fun
    (fun z ↦ by rw [Nat.cast_sub (multiplicity_le ..), sub_mul])

/-- Integrating the exterior indicator over widths in (u, v] gives the length
of its intersection with the interval below the site's offset. -/
private theorem integrate_width_tail {κ : Type*} (b : κ → ℝ) (w : κ → ℂ)
    (hw : Summable (fun k ↦ ‖w k‖)) (u v : ℝ) :
    let D := fun a ↦ ∑' k, (Iic (b k)).indicator (fun _ : ℝ ↦ w k) a
    IntegrableOn D (Ioc u v) ∧
      HasSum (fun k ↦ max (min v (b k) - u) 0 • w k) (∫ a in Ioc u v, D a) := by
  classical
  intro D
  let S := Function.support w
  have hS : S.Countable := hw.of_norm.countable_support
  let : Countable S := hS.to_subtype
  let μ := volume.restrict (Ioc u v)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by simp)
  let g (k : S) := (Iic (b k.val)).indicator (fun _ : ℝ ↦ w k.val)
  have hnorm (k : S) (a : ℝ) : ‖g k a‖ ≤ ‖w k.val‖ := by
    by_cases ha : a ∈ Iic (b k.val) <;> simp [g, ha]
  have hrepr (a : ℝ) : (∑' k : S, g k a) = D a := by
    apply tsum_subtype_eq_of_support_subset (f := fun k ↦ (Iic (b k)).indicator (fun _ : ℝ ↦ w k) a) (s := S)
    intro k hk
    contrapose hk
    simp [S, Function.mem_support] at hk
    simp [Function.mem_support, hk]
  have hm (k : S) : Measurable (g k) := measurable_const.indicator measurableSet_Iic
  have hbound (a : ℝ) : ‖D a‖ ≤ ∑' k : S, ‖w k.val‖ := by
    rw [← hrepr]
    have hj := (hw.subtype _).of_nonneg_of_le (fun k ↦ norm_nonneg _) (fun k ↦ hnorm k a)
    exact (norm_tsum_le_tsum_norm hj).trans (hj.tsum_le_tsum (fun k ↦ hnorm k a) (hw.subtype _))
  have hmeas : Measurable D := (funext hrepr) ▸ Measurable.tsum hm
  have hint : Integrable D μ :=
    (integrable_const _).mono' hmeas.aestronglyMeasurable (ae_of_all _ hbound)
  refine ⟨hint, ?_⟩
  have hg := hasSum_integral_of_dominated_convergence (μ := μ) (F := g) (f := D) (fun (k : S) (_ : ℝ) ↦ ‖w k.val‖)
    (fun k ↦ (hm k).aestronglyMeasurable) (fun k ↦ ae_of_all _ (hnorm k))
    (ae_of_all _ (fun _ ↦ hw.subtype (· ∈ S))) (integrable_const _)
    (ae_of_all _ (fun a ↦ hrepr a ▸ ((hw.subtype (· ∈ S)).of_norm_bounded fun k ↦ hnorm k a).hasSum))
  refine (hasSum_subtype_iff_of_support_subset (s := S) ?_).mp (hg.congr_fun fun k ↦ ?_)
  · intro k hk
    contrapose hk
    simp [S, Function.mem_support] at hk
    simp [Function.mem_support, hk]
  · simp [g, μ, integral_indicator_const, measureReal_restrict_apply measurableSet_Iic,
      inter_comm (Iic _), Ioc_inter_Iic]

/-- Paper: §12.3, p. 514, and (12.5.1.4), p. 520.
Reconstruction: Integrating the signed trace deficit over any interval of
nonnegative half-widths weights each zero by the length of that interval
lying below its absolute offset. Even a nonmeasurable choice of Sobolev
orders changes only boundary values on a null set for this test. -/
theorem hasSum_integral_halfTwistStripTrace_defect
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (φ : BruhatCompactSupport C𝔽) {u : ℝ} (hu : 0 ≤ u) (v : ℝ)
    (s : ℝ → ℝ) (hs : ∀ a, 1 < s a) :
    let D := fun a ↦ halfTwistStripTrace (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) < 3) φ - halfTwistStripTrace (le_max_left 0 a) (hs a) φ
    IntegrableOn D (Ioc u v) ∧ HasSum (fun z : Sites(χ) ↦
      max (min v |z.val.2.1| - u) 0 • ((mult(χ, z) : ℂ) * sample(φ, χ, z))) (∫ a in Ioc u v, D a) := by
  classical
  intro D
  let w (z : Sites(χ)) := (mult(χ, z) : ℂ) * sample(φ, χ, z)
  let b (z : Sites(χ)) := |z.val.2.1|
  have hw : Summable w := (hasSum_full χ hχ φ).summable
  have ht := integrate_width_tail b w hw.norm u v
  let E := Function.support w
  let : Countable E := hw.countable_support.to_subtype
  let μ := volume.restrict (Ioc u v)
  have hEdge : ∀ᵐ a ∂μ, ∀ z : E, a ≠ b z.val :=
    ae_all_iff.mpr (fun z ↦ ae_restrict_of_ae (volume.ae_ne _))
  have heq : (fun a ↦ ∑' z, (Iic (b z)).indicator (fun _ : ℝ ↦ w z) a) =ᵐ[μ] D := by
    filter_upwards [hEdge, ae_restrict_mem measurableSet_Ioc] with a hne ha
    have hpos := hu.trans ha.1.le
    refine (hasSum_halfTwistStripTrace_defect χ hχ φ (le_max_left 0 a) (hs a)).congr_fun
      (fun z ↦ ?_) |>.tsum_eq
    rw [max_eq_right hpos]
    by_cases hz : z ∈ E
    · rcases lt_or_gt_of_ne (hne ⟨z, hz⟩) with h | h
      · have hn : ¬ (-a < z.val.2.1 ∧ z.val.2.1 < a) := fun hh ↦
          (not_lt_of_gt h) (abs_lt.mpr hh)
        have hb : ¬ (z.val.2.1 = -a ∨ z.val.2.1 = a) := by
          rintro (he | he) <;> have := h.ne <;> simp [b, he, abs_of_nonneg hpos] at *
        simp [spectralStripMultiplicity, hn, hb, w, h.le]
      · simp [spectralStripMultiplicity_interior (abs_lt.mp h), not_le.mpr h]
    · have hwz : w z = 0 := not_ne_iff.mp hz
      have hor := mul_eq_zero.mp hwz
      rcases hor with hm | hz'
      · have hm' : mult(χ, z) = 0 := Nat.cast_eq_zero.mp hm
        rw [hm']
        simp [hwz]
      · simp [hwz, hz']
  exact ⟨ht.1.congr heq, (integral_congr_ae heq) ▸ ht.2⟩

/-- Paper: §12.3, p. 514, and Theorem 12.5.1.1, p. 520.
Reconstruction: For a probe with nonnegative real Mellin weights, one signed
upper comparison averaged over any interval (u,v] of positive length detects
all nonzero real weights beyond u, even at offsets above v. -/
theorem integral_halfTwistStripTrace_defect_nonpos_iff
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (φ : BruhatCompactSupport C𝔽)
    (hpos : ∀ z : Sites(χ), 0 ≤ ((mult(χ, z) : ℂ) * sample(φ, χ, z)).re)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (s : ℝ → ℝ) (hs : ∀ a, 1 < s a) :
    let D := fun a ↦ halfTwistStripTrace (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) < 3) φ - halfTwistStripTrace (le_max_left 0 a) (hs a) φ
    (∫ a in Ioc u v, D a).re ≤ 0 ↔
      ∀ z : Sites(χ), u < |z.val.2.1| → ((mult(χ, z) : ℂ) * sample(φ, χ, z)).re = 0 := by
  intro D
  let w (z : Sites(χ)) := ((mult(χ, z) : ℂ) * sample(φ, χ, z)).re
  let c (z : Sites(χ)) := max (min v |z.val.2.1| - u) 0
  have h : HasSum (fun z ↦ c z * w z) (∫ a in Ioc u v, D a).re := by
    simpa only [Complex.smul_re, smul_eq_mul] using
      Complex.hasSum_re (hasSum_integral_halfTwistStripTrace_defect χ hχ φ hu v s hs).2
  rw [← h.tsum_eq]
  constructor
  · intro hle z hz
    have hc : 0 < c z := lt_of_lt_of_le (sub_pos.mpr (lt_min huv hz)) (le_max_left _ _)
    have ht := h.summable.le_tsum z (fun j _ ↦ mul_nonneg (le_max_right _ _) (hpos j))
    apply le_antisymm _ (hpos z)
    by_contra! hpositive
    exact (not_lt_of_ge (ht.trans hle)) (mul_pos hc hpositive)
  · intro hz
    have hzero (z : Sites(χ)) : c z * w z = 0 := by
      by_cases hb : u < |z.val.2.1|
      · exact mul_eq_zero_of_right _ (hz z hb)
      · have hn := sub_nonpos.mpr ((min_le_right v _).trans (le_of_not_gt hb))
        simp [c, max_eq_right hn]
    simp only [hzero, tsum_zero, le_refl]

/-- Paper: Theorem 12.5.1.1, pp. 519–520. The complex trace converges to
its wide-strip value as the half-width tends to one half. The Sobolev
order may vary arbitrarily above one. -/
theorem halfTwistStripTrace_tendsto_half {ι : Type*} {l : Filter ι}
    (φ : BruhatCompactSupport C𝔽) (a s : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hs : ∀ i, 1 < s i) (hlim : Tendsto a l (𝓝 (1 / 2 : ℝ))) :
    Tendsto (fun i ↦ halfTwistStripTrace (ha i) (hs i) φ) l
      (𝓝 (halfTwistStripTrace (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) < 3) φ)) := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice F
  let v (z : Sites(χ)) := sample(φ, χ, z)
  let m (z : Sites(χ)) := mult(χ, z)
  have full := hasSum_full χ hχ φ
  let u (i : ι) (z : Sites(χ)) := (spectralStripMultiplicity (a i) (s i) z.val.2.1 (m z) : ℂ) * v z
  have hseries := tendsto_tsum_of_dominated_convergence (f := u) full.summable.norm
    (fun z ↦ (tendsto_const_nhds (x := (m z : ℂ) * v z)).congr' (by
      filter_upwards [hlim.eventually (lt_mem_nhds (site_interior χ z))] with i hi
      simp only [u, spectralStripMultiplicity_interior (abs_lt.mp hi)]))
    (Eventually.of_forall (fun i z ↦ by
      have hle := multiplicity_le (a i) (s i) z.val.2.1 (m z)
      simp only [u, norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (norm_nonneg _)))
  rw [full.tsum_eq] at hseries
  exact hseries.congr (fun i ↦ (hasSum_width χ hχ (ha i) (hs i) φ).tsum_eq)

local notation "corrected(" f ", " φ ", " R ")" => volF / volS *
  ((∑' ξ : Hₛ, sLocalTraceSharpMass (F := F) (S := S) f ξ R) - volS * (φ).val 1 * (Real.log R : ℂ) -
    ((∫ g : Iₛ, (f).val g * rootS(g) ∂μₛ) + ∫ g : Iₛ, (f).val g / rootS(g) ∂μₛ))

private theorem corrected_sharp_limit
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRam : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    {B : ℝ} (hB : ∀ g ∈ tsupport φ.val, normR(g) < B ∧ (normR(g))⁻¹ < B)
    (hS : ∀ v : V, v ∉ S → B ≤ (v.asIdeal.absNorm : ℝ))
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g)))) :
    Tendsto (fun R : ℝ ↦ corrected(f, φ, R)) atTop
      (𝓝 (-halfTwistStripTrace (F := F) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) < 3) φ)) :=
  sLocalTraceSharpMass_logSubtracted_tendsto_neg_spectralTrace_of_half_le
    φ hPic hRam hOutside hB hS f hLift (le_refl (1 / 2 : ℝ)) (by norm_num : (1 : ℝ) < 3)
    ⟨_, spectralStripConvolution_nuclear_of_summable_clusterTraceNorms (1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 3) φ⟩ rfl

/-- Paper: §12.3, p. 514, and (12.5.1.4), p. 520.
Reconstruction: At any fixed half-width, the negative corrected local sharp
expression minus the quotient trace converges to the signed Mellin sum with
the omitted multiplicities. Zeros on the two edges retain their actual
Sobolev boundary correction. -/
theorem sLocalTraceSharpMass_stripTrace_defect_tendsto
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRam : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    {B : ℝ} (hB : ∀ g ∈ tsupport φ.val, normR(g) < B ∧ (normR(g))⁻¹ < B)
    (hS : ∀ v : V, v ∉ S → B ≤ (v.asIdeal.absNorm : ℝ))
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s) :
    Tendsto (fun R ↦ -corrected(f, φ, R) - halfTwistStripTrace (F := F) ha hs φ) atTop
      (𝓝 (∑' z : Sites(χ),
        ((mult(χ, z) - spectralStripMultiplicity a s z.val.2.1 (mult(χ, z)) : ℕ) : ℂ) *
          sample(φ, χ, z))) := by
  rw [(hasSum_halfTwistStripTrace_defect χ hχ φ ha hs).tsum_eq]
  simpa only [neg_neg] using
    (corrected_sharp_limit φ hPic hRam hOutside hB hS f hLift).neg.sub_const
      (halfTwistStripTrace (F := F) ha hs φ)

/-- Paper: §12.3, p. 514, and (12.5.1.4), p. 520.
Reconstruction: The signed difference between the pole-corrected sharp local
expression and the negative global quotient trace tends to zero as the local
cutoff tends to infinity and the strip half-width tends to one half. -/
theorem sLocalTraceSharpMass_add_stripTrace_tendsto_zero
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRam : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    {B : ℝ} (hB : ∀ g ∈ tsupport φ.val, normR(g) < B ∧ (normR(g))⁻¹ < B)
    (hS : ∀ v : V, v ∉ S → B ≤ (v.asIdeal.absNorm : ℝ))
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    {ι : Type*} {l : Filter ι} (R a s : ι → ℝ) (hR : Tendsto R l atTop)
    (ha : ∀ i, 0 ≤ a i) (hs : ∀ i, 1 < s i) (hlim : Tendsto a l (𝓝 (1 / 2 : ℝ))) :
    Tendsto (fun i ↦ corrected(f, φ, R i) + halfTwistStripTrace (F := F) (ha i) (hs i) φ) l (𝓝 0) := by
  have hlocal := corrected_sharp_limit φ hPic hRam hOutside hB hS f hLift
  have hglobal := halfTwistStripTrace_tendsto_half φ a s ha hs hlim
  simpa only [Function.comp_apply, neg_add_cancel] using (hlocal.comp hR).add hglobal

/-- Paper: §12.3, p. 514, and the comparison required on pp. 519–520.
Reconstruction: Over an interval of thin widths, subtract the genuine quotient
trace from the negative pole-corrected sharp orbital expression. Its limiting
integral is the signed first moment of the omitted zeros across those widths.
A zero with absolute offset between the two endpoints contributes the distance
of that offset from the lower endpoint. -/
theorem sLocalTraceSharpMass_integrated_stripTrace_defect
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRam : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    {B : ℝ} (hB : ∀ g ∈ tsupport φ.val, normR(g) < B ∧ (normR(g))⁻¹ < B)
    (hS : ∀ v : V, v ∉ S → B ≤ (v.asIdeal.absNorm : ℝ))
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {u : ℝ} (hu : 0 ≤ u) (v : ℝ) (s : ℝ → ℝ) (hs : ∀ a, 1 < s a) :
    Tendsto (fun R ↦ ∫ a in Ioc u v, -corrected(f, φ, R) - halfTwistStripTrace (F := F) (le_max_left 0 a) (hs a) φ)
      atTop (𝓝 (∑' z : Sites(χ), max (min v |z.val.2.1| - u) 0 •
        ((mult(χ, z) : ℂ) * sample(φ, χ, z)))) := by
  let W := halfTwistStripTrace (F := F) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) < 3) φ
  let D := fun a ↦ W - halfTwistStripTrace (F := F) (le_max_left 0 a) (hs a) φ
  have hi := hasSum_integral_halfTwistStripTrace_defect χ hχ φ hu v s hs
  have hL := corrected_sharp_limit φ hPic hRam hOutside hB hS f hLift
  have h0 : Tendsto (fun R ↦ -corrected(f, φ, R) - W) atTop (𝓝 0) := by
    simpa only [W, neg_neg, sub_self] using hL.neg.sub_const W
  have hI : Tendsto (fun R ↦ volume.real (Ioc u v) • (-corrected(f, φ, R) - W) + ∫ a in Ioc u v, D a)
      atTop (𝓝 (∫ a in Ioc u v, D a)) := by
    simpa only [smul_zero, zero_add] using
      (h0.const_smul (volume.real (Ioc u v))).add_const (∫ a in Ioc u v, D a)
  rw [hi.2.tsum_eq]
  refine hI.congr fun R ↦ ?_
  rw [← setIntegral_const, ← integral_add]
  · apply integral_congr_ae
    exact ae_of_all _ fun a ↦ by dsimp [D]; abel
  · exact integrableOn_const (by simp)
  · exact hi.1

/-- A positive divisor site has centered real offset strictly below one half in absolute value. -/
theorem spectralStrip_zero_offset_lt_half (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (z : Sites(χ)) :
    |z.val.2.1| < (1 / 2 : ℝ) :=
  site_interior χ z

/-- The full-width Hilbert trace is the unordered sum over all positive-order sites. -/
theorem hasSum_halfTwistStripTrace_full (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (φ : BruhatCompactSupport C𝔽) :
    HasSum (fun z : Sites(χ) ↦ (mult(χ, z) : ℂ) * sample(φ, χ, z))
      (halfTwistStripTrace (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) < 3) φ) :=
  hasSum_full χ hχ φ

/-- The finite-cutoff sharp orbital mass, with the logarithmic divergence and the
two polar Mellin integrals subtracted, in the global Tamagawa normalization. -/
@[expose] def correctedSLocalTraceSharpMass (φ : BruhatCompactSupport C𝔽)
    (f : BruhatCompactSupport Iₛ) (R : ℝ) : ℂ := corrected(f, φ, R)

/-- The corrected sharp orbital mass tends to minus the full-width quotient trace. -/
theorem sLocalTraceSharpMass_tendsto_neg_halfTwistStripTrace
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRam : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    {B : ℝ} (hB : ∀ g ∈ tsupport φ.val, normR(g) < B ∧ (normR(g))⁻¹ < B)
    (hS : ∀ v : V, v ∉ S → B ≤ (v.asIdeal.absNorm : ℝ))
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g)))) :
    Tendsto (fun R : ℝ ↦ correctedSLocalTraceSharpMass φ f R) atTop
      (𝓝 (-halfTwistStripTrace (F := F) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) < 3) φ)) :=
  corrected_sharp_limit φ hPic hRam hOutside hB hS f hLift

end RiemannMasullo
