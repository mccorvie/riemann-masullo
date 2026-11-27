module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import RiemannMasullo.AppC_LCTVS.Sec3a
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3a
public import RiemannMasullo.ForMathlib.MeasureTheory.Function.PositiveRayDilation
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-!
# The polar contribution in the flat rational frequency model

Reconstruction: Theorem 12.4.1.1, pp. 515–517, in the positive-frequency chart of
the real even block at Sobolev order zero. The band projection cuts off `(0, B]`. Its
polar-free subprojection subtracts the normalized Lebesgue mean on that band.

The gate in (12.4.1.8) precedes the dilation. For every bounded measurable complex gate
the resulting polar matrix coefficient is `a⁻¹ᐟ² ∫₀^{min(1, a)} Q(u) du`. A sharp gate
of relative radius `0 ≤ r ≤ 1` gives `min(a, r)/√a`. The two-sided compression
difference is nuclear. Its Hilbert trace is the negative of the integral of the
coefficient against the compact test and the multiplicative Haar measure.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped CompactlySupported ComplexConjugate InnerProductSpace NNReal

namespace RiemannMasullo.FlatPolar

/-- The constant band profile on the positive ray, with Lebesgue normalization. -/
def bandProfile (B t : ℝ) : ℂ :=
  (Ioc 0 B).indicator (fun _ ↦ (Real.sqrt B : ℂ)⁻¹) t

private theorem rayVolume_band (B : ℝ) :
    volume.restrict (Ioi (0 : ℝ)) (Ioc 0 B) = ENNReal.ofReal B := by
  rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self,
    Real.volume_Ioc, sub_zero]

/-- The band profile is square-integrable for every real endpoint. -/
theorem bandProfile_memLp (B : ℝ) :
    MemLp (bandProfile B) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet _
    (.inr (by rw [rayVolume_band]; exact ENNReal.ofReal_ne_top))

/-- The positive-ray Lebesgue `L²` vector represented by the band profile. -/
def bandVector (B : ℝ) : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (bandProfile_memLp B).toLp (bandProfile B)

/-- The band vector agrees almost everywhere with its defining profile. -/
theorem bandVector_ae_eq (B : ℝ) :
    ⇑(bandVector B) =ᵐ[volume.restrict (Ioi (0 : ℝ))] bandProfile B :=
  MemLp.coeFn_toLp (bandProfile_memLp B)

/-- Every band of positive length has unit norm. -/
theorem norm_bandVector {B : ℝ} (hB : 0 < B) : ‖bandVector B‖ = 1 := by
  have hfin : volume.restrict (Ioi (0 : ℝ)) (Ioc 0 B) ≠ ⊤ := by
    rw [rayVolume_band]
    exact ENNReal.ofReal_ne_top
  change ‖indicatorConstLp 2 measurableSet_Ioc hfin (Real.sqrt B : ℂ)⁻¹‖ = 1
  rw [norm_indicatorConstLp (by norm_num) (by norm_num), measureReal_def, rayVolume_band,
    ENNReal.toReal_ofReal hB.le]
  norm_num [← Real.sqrt_eq_rpow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg B), (Real.sqrt_pos.2 hB).ne']

/-- In the coordinate `u = a t / B`, both band conditions hold precisely on
`(0, min 1 a]`. -/
private theorem band_integrand_eq {a B : ℝ} (ha : 0 < a) (hB : 0 < B) (Q : ℝ → ℂ) (t : ℝ) :
    star (bandProfile B t) * ((Real.sqrt a : ℂ) * (Q (a * t / B) * bandProfile B (a * t))) =
      ((Real.sqrt a : ℂ) / B) * (Ioc 0 (min 1 a)).indicator Q ((a / B) * t) := by
  rw [show a / B * t = a * t / B by ring]
  have hu : a * t / B ∈ Ioc 0 (min 1 a) ↔ t ∈ Ioc 0 B ∧ a * t ∈ Ioc 0 B := by
    simp only [mem_Ioc, le_min_iff]
    simp only [div_pos_iff_of_pos_right hB, mul_pos_iff_of_pos_left ha,
      div_le_iff₀ hB, one_mul, mul_le_mul_iff_right₀ ha]
    tauto
  by_cases ht : t ∈ Ioc 0 B
  · by_cases hat : a * t ∈ Ioc 0 B
    · rw [indicator_of_mem (hu.mpr ⟨ht, hat⟩)]
      simp only [bandProfile, indicator_of_mem ht, indicator_of_mem hat, star_inv₀,
        Complex.star_def, Complex.conj_ofReal]
      have hs : (Real.sqrt B : ℂ) ^ 2 = B := by exact_mod_cast Real.sq_sqrt hB.le
      have hs0 : (Real.sqrt B : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hB).ne'
      rw [← hs]
      field_simp
    · simp [bandProfile, ht, hat, indicator_of_notMem (fun h ↦ hat (hu.mp h).2)]
  · simp [bandProfile, ht, indicator_of_notMem (fun h ↦ ht (hu.mp h).1)]

/-- Bounded measurable gates give an integrable pairing. A bound on the band
overlap alone suffices. -/
theorem integrableOn_bandProfile_gate {a B : ℝ} (ha : 0 < a) (hB : 0 < B) (Q : ℝ → ℂ)
    (hQ : Measurable Q) {C : ℝ} (hC : ∀ u ∈ Ioc 0 (min 1 a), ‖Q u‖ ≤ C) :
    IntegrableOn (fun t ↦ star (bandProfile B t) *
      ((Real.sqrt a : ℂ) * (Q (a * t / B) * bandProfile B (a * t)))) (Ioi (0 : ℝ)) := by
  have hreg : IntegrableOn Q (Ioc 0 (min 1 a)) := by
    apply IntegrableOn.of_bound (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
      hQ.aestronglyMeasurable C
    exact (ae_restrict_mem measurableSet_Ioc).mono hC
  have hF := (integrable_indicator_iff measurableSet_Ioc).mpr hreg
  simp_rw [band_integrand_eq ha hB Q]
  exact ((hF.comp_mul_left' (div_pos ha hB).ne').const_mul ((Real.sqrt a : ℂ) / B)).integrableOn

/-- Exact dilation pairing for every complex gate. For a bounded measurable gate
the preceding lemma supplies integrability. -/
theorem bandProfile_gate_integral {a B : ℝ} (ha : 0 < a) (hB : 0 < B) (Q : ℝ → ℂ) :
    (∫ t in Ioi (0 : ℝ), star (bandProfile B t) *
      ((Real.sqrt a : ℂ) * (Q (a * t / B) * bandProfile B (a * t)))) =
        (Real.sqrt a : ℂ)⁻¹ * ∫ u in Ioc 0 (min 1 a), Q u := by
  simp_rw [band_integrand_eq ha hB Q]
  rw [integral_const_mul, integral_comp_mul_left_Ioi _ 0 (div_pos ha hB), mul_zero,
    setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr Ioc_subset_Ioi_self,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_div, ← mul_assoc]
  congr 1
  have hs : (Real.sqrt a : ℂ) ^ 2 = a := by exact_mod_cast Real.sq_sqrt ha.le
  have hs0 : (Real.sqrt a : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 ha).ne'
  have hB0 : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  rw [← hs]
  field_simp

/-- A sharp gate on the closed band `[0, r]` cuts the overlap to length
`min a r`, including the degenerate endpoint `r = 0`. -/
theorem sharpGate_integral {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (∫ u in Ioc 0 (min 1 a), (Icc 0 r).indicator (fun _ ↦ (1 : ℂ)) u) =
      (min a r : ℝ) := by
  have hi : Ioc 0 (min 1 a) ∩ Icc 0 r = Ioc 0 (min a r) := by
    ext u
    simp only [mem_inter_iff, mem_Ioc, mem_Icc, le_min_iff]
    constructor
    · rintro ⟨⟨hu, _, hua⟩, _, hur⟩
      exact ⟨hu, hua, hur⟩
    · rintro ⟨hu, hua, hur⟩
      exact ⟨⟨hu, hur.trans hr1, hua⟩, hu.le, hur⟩
  rw [setIntegral_indicator measurableSet_Icc, hi, setIntegral_const,
    Real.volume_real_Ioc_of_le (le_min ha hr), sub_zero, Complex.real_smul, mul_one]

/-- The sharp-gated pairing is `min a r / sqrt a` for all `0 ≤ r ≤ 1`. -/
theorem bandProfile_sharp_integral {a B r : ℝ} (ha : 0 < a) (hB : 0 < B)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (∫ t in Ioi (0 : ℝ), star (bandProfile B t) *
      ((Real.sqrt a : ℂ) * ((Icc 0 r).indicator (fun _ ↦ (1 : ℂ)) (a * t / B) *
        bandProfile B (a * t)))) = (Real.sqrt a : ℂ)⁻¹ * (min a r : ℝ) := by
  rw [bandProfile_gate_integral ha hB, sharpGate_integral ha.le hr hr1]

section BandProjection

local notation "ν" => volume.restrict (Ioi (0 : ℝ))
local notation "H" => Lp ℂ 2 ν

/-- The subspace of positive-ray functions vanishing almost everywhere outside `(0, B]`. -/
def frequencyBand (B : ℝ) : Submodule ℂ H where
  carrier := {f | ∀ᵐ t ∂ν, t ∉ Ioc 0 B → f t = 0}
  zero_mem' := (Lp.coeFn_zero ℂ 2 ν).mono fun _ ht _ ↦ ht
  add_mem' {f g} hf hg := by
    change ∀ᵐ t ∂ν, t ∉ Ioc 0 B → f t = 0 at hf
    change ∀ᵐ t ∂ν, t ∉ Ioc 0 B → g t = 0 at hg
    change ∀ᵐ t ∂ν, t ∉ Ioc 0 B → (f + g) t = 0
    filter_upwards [Lp.coeFn_add f g, hf, hg] with t ht hft hgt h
    rw [ht, Pi.add_apply, hft h, hgt h, add_zero]
  smul_mem' c f hf := by
    change ∀ᵐ t ∂ν, t ∉ Ioc 0 B → f t = 0 at hf
    change ∀ᵐ t ∂ν, t ∉ Ioc 0 B → (c • f) t = 0
    filter_upwards [Lp.coeFn_smul c f, hf] with t ht hft h
    rw [ht, Pi.smul_apply, hft h, smul_zero]

/-- Membership imposes the support condition on positive-ray representatives. -/
theorem mem_frequencyBand_iff (B : ℝ) (f : H) :
    f ∈ frequencyBand B ↔ ∀ᵐ t ∂ν, t ∉ Ioc 0 B → f t = 0 := Iff.rfl

private def bandCut (B : ℝ) (f : H) : H :=
  ((Lp.memLp f).indicator measurableSet_Ioc.nullMeasurableSet).toLp ((Ioc 0 B).indicator f)

private theorem bandCut_ae_eq (B : ℝ) (f : H) :
    ⇑(bandCut B f) =ᵐ[ν] (Ioc 0 B).indicator f := MemLp.coeFn_toLp _

private theorem bandCut_mem (B : ℝ) (f : H) : bandCut B f ∈ frequencyBand B :=
  (bandCut_ae_eq B f).mono fun _ ht h ↦ ht.trans (indicator_of_notMem h _)

private theorem sub_bandCut_mem_orthogonal (B : ℝ) (f : H) :
    f - bandCut B f ∈ (frequencyBand B)ᗮ := by
  intro g hg
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [Lp.coeFn_sub f (bandCut B f), bandCut_ae_eq B f,
    (mem_frequencyBand_iff B g).mp hg] with t hf hcut hg
  change inner ℂ (g t) ((f - bandCut B f) t) = 0
  by_cases ht : t ∈ Ioc 0 B
  · rw [hf, Pi.sub_apply, hcut, indicator_of_mem ht, sub_self, inner_zero_right]
  · rw [hg ht, inner_zero_left]

instance instHasOrthogonalProjectionFrequencyBand (B : ℝ) : (frequencyBand B).HasOrthogonalProjection where
  exists_orthogonal f := ⟨bandCut B f, bandCut_mem B f, sub_bandCut_mem_orthogonal B f⟩

/-- The frequency band is closed in radial Lebesgue `L²`. -/
theorem isClosed_frequencyBand (B : ℝ) : IsClosed (frequencyBand B : Set H) := by
  simpa only [Submodule.orthogonal_orthogonal] using ((frequencyBand B)ᗮ).isClosed_orthogonal

/-- The original band projection multiplies by the indicator of `(0, B]`. -/
theorem frequencyBand_starProjection_ae_eq (B : ℝ) (f : H) :
    ⇑((frequencyBand B).starProjection f) =ᵐ[ν] (Ioc 0 B).indicator f := by
  rw [Submodule.eq_starProjection_of_mem_orthogonal (bandCut_mem B f)
    (sub_bandCut_mem_orthogonal B f)]
  exact bandCut_ae_eq B f

/-- The normalized band profile belongs to the original band. -/
theorem bandVector_mem_frequencyBand (B : ℝ) : bandVector B ∈ frequencyBand B :=
  (bandVector_ae_eq B).mono fun _ ht h ↦ ht.trans (indicator_of_notMem h _)

/-- Projecting the normalized band profile onto the band fixes it. -/
theorem frequencyBand_starProjection_bandVector (B : ℝ) :
    (frequencyBand B).starProjection (bandVector B) = bandVector B :=
  Submodule.starProjection_eq_self_iff.mpr (bandVector_mem_frequencyBand B)

private theorem rayVolume_band_ne_top (B : ℝ) : ν (Ioc 0 B) ≠ ⊤ := by
  rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self,
    Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

/-- Every positive-ray square-integrable function has an ordinary Lebesgue integral
on each finite band. -/
theorem integrableOn_band (B : ℝ) (f : H) : IntegrableOn (fun t ↦ f t) (Ioc 0 B) := by
  simpa only [IntegrableOn, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr Ioc_subset_Ioi_self] using
    integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim (rayVolume_band_ne_top B)

/-- The coefficient of a vector along the constant profile is its unconjugated
Lebesgue integral over the band, times `1 / sqrt B`. -/
theorem inner_bandVector_eq_bandIntegral (B : ℝ) (f : H) :
    inner ℂ (bandVector B) f = (Real.sqrt B : ℂ)⁻¹ * ∫ t in Ioc 0 B, f t := by
  change inner ℂ (indicatorConstLp 2 measurableSet_Ioc (rayVolume_band_ne_top B)
    (Real.sqrt B : ℂ)⁻¹) f = _
  rw [L2.inner_indicatorConstLp_eq_inner_setIntegral, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr Ioc_subset_Ioi_self, RCLike.inner_apply']
  simp

/-- The vectors in the frequency band orthogonal to its constant profile. -/
def meanZeroFrequencyBand (B : ℝ) : Submodule ℂ H :=
  frequencyBand B ⊓ (ℂ ∙ bandVector B)ᗮ

instance instCompleteSpaceMeanZeroFrequencyBand (B : ℝ) : CompleteSpace (meanZeroFrequencyBand B) :=
  ((isClosed_frequencyBand B).inter (ℂ ∙ bandVector B).isClosed_orthogonal).completeSpace_coe

/-- A vector in the mean-zero band vanishes almost everywhere outside the band
and has zero ordinary Lebesgue integral over the band. -/
theorem mem_meanZeroFrequencyBand_iff {B : ℝ} (hB : 0 < B) (f : H) :
    f ∈ meanZeroFrequencyBand B ↔
      (∀ᵐ t ∂ν, t ∉ Ioc 0 B → f t = 0) ∧ (∫ t in Ioc 0 B, f t) = 0 := by
  change (f ∈ frequencyBand B ∧ f ∈ (ℂ ∙ bandVector B)ᗮ) ↔ _
  rw [mem_frequencyBand_iff, Submodule.mem_orthogonal_singleton_iff_inner_right,
    inner_bandVector_eq_bandIntegral]
  have hs : (Real.sqrt B : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hB).ne'
  simp [hs]

/-- Removing the line of the constant band profile from the original projection
gives the orthogonal projection onto the mean-zero band. -/
theorem frequencyBand_starProjection_sub_line (B : ℝ) :
    (frequencyBand B).starProjection - (ℂ ∙ bandVector B).starProjection =
      (meanZeroFrequencyBand B).starProjection := by
  let K := frequencyBand B
  let L := ℂ ∙ bandVector B
  let M := meanZeroFrequencyBand B
  have hLK : L ≤ K := (Submodule.span_singleton_le_iff_mem _ _).mpr (bandVector_mem_frequencyBand B)
  have hMK : M ≤ K := inf_le_left
  have hML : M ≤ Lᗮ := inf_le_right
  apply ContinuousLinearMap.ext
  intro f
  change K.starProjection f - L.starProjection f = M.starProjection f
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · refine ⟨K.sub_mem (K.starProjection_apply_mem f) (hLK (L.starProjection_apply_mem f)), ?_⟩
    have hsame : L.starProjection (K.starProjection f) = L.starProjection f :=
      congrArg Subtype.val (Submodule.orthogonalProjectionOnto_starProjection_of_le hLK f)
    rw [← hsame]
    exact L.sub_starProjection_mem_orthogonal _
  · have hK : f - K.starProjection f ∈ Mᗮ :=
      Submodule.orthogonal_le hMK (K.sub_starProjection_mem_orthogonal f)
    have hL : L.starProjection f ∈ Mᗮ :=
      Submodule.orthogonal_le hML (L.le_orthogonal_orthogonal (L.starProjection_apply_mem f))
    rw [show f - (K.starProjection f - L.starProjection f) =
      (f - K.starProjection f) + L.starProjection f by abel]
    exact Mᗮ.add_mem hK hL

/-- Pointwise on the band, the polar-free projection subtracts the Lebesgue
average of the input. Its output vanishes off the band. -/
theorem meanZeroFrequencyBand_starProjection_ae_eq {B : ℝ} (hB : 0 < B) (f : H) :
    ⇑((meanZeroFrequencyBand B).starProjection f) =ᵐ[ν]
      (Ioc 0 B).indicator (fun t ↦ f t - (B : ℂ)⁻¹ * ∫ u in Ioc 0 B, f u) := by
  rw [← frequencyBand_starProjection_sub_line, sub_apply,
    Submodule.starProjection_unit_singleton ℂ (norm_bandVector hB)]
  have hconst (z : ℂ) : (Real.sqrt B : ℂ)⁻¹ * z * (Real.sqrt B : ℂ)⁻¹ = (B : ℂ)⁻¹ * z := by
    have hs : (Real.sqrt B : ℂ) ^ 2 = B := by exact_mod_cast Real.sq_sqrt hB.le
    rw [← hs, ← inv_pow]
    ring
  filter_upwards [Lp.coeFn_sub ((frequencyBand B).starProjection f)
    (inner ℂ (bandVector B) f • bandVector B), frequencyBand_starProjection_ae_eq B f,
    Lp.coeFn_smul (inner ℂ (bandVector B) f) (bandVector B), bandVector_ae_eq B]
      with t hsub hproj hsmul he
  rw [hsub, Pi.sub_apply, hproj, hsmul, Pi.smul_apply, smul_eq_mul, he,
    inner_bandVector_eq_bandIntegral]
  by_cases ht : t ∈ Ioc 0 B
  · simp only [bandProfile, indicator_of_mem ht, hconst]
  · simp [bandProfile, ht]

end BandProjection

section Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Restrict the input of `T` to the normalized polar vector `e`. -/
def polarRankOne (T : H →L[ℂ] H) (e : H) : nuclearEndomorphisms H :=
  ⟨(innerSL ℂ e).smulRight (T e), smulRight_mem_nuclearEndomorphisms _ _⟩

/-- For a unit vector the input restriction is its literal Hilbert-space orthogonal projection. -/
theorem polarRankOne_eq_comp_starProjection (T : H →L[ℂ] H) {e : H} (he : ‖e‖ = 1) :
    (polarRankOne T e).val = T.comp (ℂ ∙ e).starProjection := by
  ext v
  simp [polarRankOne, Submodule.starProjection_unit_singleton ℂ he]

/-- The Hilbert trace is linear in the output slot, including for complex tests. -/
private theorem hilbertTrace_polarRankOne (T : H →L[ℂ] H) (e : H) :
    hilbertTrace (polarRankOne T e) = ⟪e, T e⟫_ℂ :=
  hilbertTrace_smulRight _ _

/-- Removing one polar direction from both sides of an orthogonal compression changes its
trace by minus the polar matrix coefficient. The finite-rank difference is nuclear for any
bounded `T`, even when the two individual compressions do not have traces. -/
theorem polarFree_compression_difference (T : H →L[ℂ] H) (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] {e : H} (he : ‖e‖ = 1) (hK : e ∈ K) :
    let P := K.starProjection
    let p := (ℂ ∙ e).starProjection
    ∃ R : nuclearEndomorphisms H, R.val =
      (P - p).comp (T.comp (P - p)) - P.comp (T.comp P) ∧
      hilbertTrace R = -⟪e, T e⟫_ℂ := by
  let P := K.starProjection
  let d := innerSL ℂ e
  let U : nuclearEndomorphisms H := ⟨(d.comp (T.comp P)).smulRight e,
    smulRight_mem_nuclearEndomorphisms _ _⟩
  let V := polarRankOne (P.comp T) e
  let Z : nuclearEndomorphisms H := ⟨d.smulRight ((d (T e)) • e),
    smulRight_mem_nuclearEndomorphisms _ _⟩
  refine ⟨Z - U - V, ?_, ?_⟩
  · ext x
    simp only [Z, U, V, P, d, polarRankOne, Submodule.coe_sub, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      Submodule.starProjection_unit_singleton ℂ he, map_sub, map_smul, smul_smul]
    module
  · have heP : P e = e := Submodule.starProjection_eq_self_iff.mpr hK
    have hee : ⟪e, e⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, he]
    obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
    rw [← htr, map_sub, map_sub, htr, htr, htr, hilbertTrace_polarRankOne,
      show hilbertTrace U = d (T (P e)) from hilbertTrace_smulRight _ _,
      show hilbertTrace Z = d (d (T e) • e) from hilbertTrace_smulRight _ _]
    simp only [heP, d, innerSL_apply_apply, inner_smul_right, hee, mul_one,
      ContinuousLinearMap.comp_apply, P, ← K.inner_starProjection_left_eq_right e]
    abel

end Operator

section Integrated

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem integrable_weightedOrbit (μ : Measure X) (D : X → H ≃ₗᵢ[ℂ] H)
    (hD : ∀ v, AEStronglyMeasurable (fun a ↦ D a v) μ) {φ : X → ℂ} (hφ : Integrable φ μ)
    (v : H) : Integrable (fun a ↦ φ a • D a v) μ :=
  hφ.smul_bdd ‖v‖ (hD v) (.of_forall fun a ↦ (D a).norm_map v |>.le)

/-- Integrate the strongly measurable orbits of a unitary family against an integrable test. -/
private def integratedUnitary (μ : Measure X) (D : X → H ≃ₗᵢ[ℂ] H)
    (hD : ∀ v, AEStronglyMeasurable (fun a ↦ D a v) μ) (φ : X → ℂ) (hφ : Integrable φ μ) :
    H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun v ↦ ∫ a, φ a • D a v ∂μ
      map_add' := fun v w ↦ by
        simpa only [map_add, smul_add] using
          integral_add (integrable_weightedOrbit μ D hD hφ v)
            (integrable_weightedOrbit μ D hD hφ w)
      map_smul' := fun c v ↦ by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        exact integral_congr_ae (.of_forall fun a ↦ smul_comm _ _ _) }
    (∫ a, ‖φ a‖ ∂μ) fun v ↦ by
      change ‖∫ a, φ a • D a v ∂μ‖ ≤ (∫ a, ‖φ a‖ ∂μ) * ‖v‖
      simpa only [norm_smul, LinearIsometryEquiv.norm_map, integral_mul_const] using
        (norm_integral_le_integral_norm (μ := μ) (fun a ↦ φ a • D a v))

end Integrated

section PositiveRay

local notation "ν" => volume.restrict (Ioi (0 : ℝ))
local notation "H" => Lp ℂ 2 ν

section Gate

variable (Q : ℝ → ℂ) (hQ : Measurable Q) (C : ℝ) (hC : 0 ≤ C) (hQC : ∀ t, ‖Q t‖ ≤ C)

/-- The matrix coefficient for (12.4.1.8), p. 517, in the flat positive-frequency chart.
The frequency multiplier is applied inside the original band, before the unitary dilation. -/
theorem inner_bandVector_dilation_multiplier {a B : ℝ} (ha : 0 < a) (hB : 0 < B) :
    ⟪bandVector B, positiveRayDilation a ha
      (positiveRayMultiplier Q hQ C hC hQC B (bandVector B))⟫_ℂ =
      (Real.sqrt a : ℂ)⁻¹ * ∫ u in Ioc 0 (min 1 a), Q u := by
  let M := positiveRayMultiplier Q hQ C hC hQC B
  rw [L2.inner_def, ← bandProfile_gate_integral ha hB Q]
  apply integral_congr_ae
  have hp := positiveRayScale_quasiMeasurePreserving a ha
  filter_upwards [bandVector_ae_eq B, positiveRayDilation_apply a ha (M (bandVector B)),
    hp.ae_eq_comp (positiveRayMultiplier_apply Q hQ C hC hQC B (bandVector B)),
    hp.ae_eq_comp (bandVector_ae_eq B)] with t he hD hM he'
  change M (bandVector B) (a * t) = Q (a * t / B) * bandVector B (a * t) at hM
  change bandVector B (a * t) = bandProfile B (a * t) at he'
  rw [RCLike.inner_apply', he, hD, hM, he']
  rfl

/-- The same number is the nuclear trace of the gated dilation restricted to its polar input. -/
theorem hilbertTrace_dilation_multiplier_polar {a B : ℝ} (ha : 0 < a) (hB : 0 < B) :
    hilbertTrace (polarRankOne (((positiveRayDilation a ha : H →L[ℂ] H)).comp
      (positiveRayMultiplier Q hQ C hC hQC B)) (bandVector B)) =
      (Real.sqrt a : ℂ)⁻¹ * ∫ u in Ioc 0 (min 1 a), Q u :=
  (hilbertTrace_polarRankOne _ _).trans (inner_bandVector_dilation_multiplier Q hQ C hC hQC ha hB)

end Gate

/-- The sharp input frequency gate on `[0, r B]` for a positive band endpoint `B`. -/
def sharpMultiplier (r B : ℝ) : H →L[ℂ] H :=
  positiveRayMultiplier ((Icc 0 r).indicator (fun _ ↦ (1 : ℂ)))
    (measurable_const.indicator measurableSet_Icc) 1 zero_le_one
    (fun t ↦ by by_cases h : t ∈ Icc 0 r <;> simp [h]) B

/-- Exact sharp-gate rank-one nuclear trace for any dilation ratio, including the transition
at `a = r` and both endpoint gates. The polar projection stays at the original `B`. -/
theorem hilbertTrace_dilation_sharp_polar {a B r : ℝ} (ha : 0 < a) (hB : 0 < B)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    hilbertTrace (polarRankOne ((positiveRayDilation a ha : H →L[ℂ] H).comp
      (sharpMultiplier r B)) (bandVector B)) = (Real.sqrt a : ℂ)⁻¹ * (min a r : ℝ) := by
  rw [sharpMultiplier, hilbertTrace_dilation_multiplier_polar _ _ _ _ _ ha hB,
    sharpGate_integral ha.le hr hr1]

private theorem positiveNormRatio (a : ℝ≥0ˣ) : 0 < (a.val : ℝ) :=
  NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr a.ne_zero)

private def normDilation (a : ℝ≥0ˣ) : H ≃ₗᵢ[ℂ] H :=
  positiveRayDilation a.val (positiveNormRatio a)

private theorem normDilation_measurable (v : H) :
    AEStronglyMeasurable (fun a ↦ normDilation a v) positiveRealHaar := by
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let ratio : ℝ≥0ˣ → Ioi (0 : ℝ) := fun a ↦ ⟨a.val, positiveNormRatio a⟩
  have hc : Continuous ratio :=
    (NNReal.continuous_coe.comp Units.continuous_val).subtype_mk _
  change AEStronglyMeasurable ((fun b : Ioi (0 : ℝ) ↦ positiveRayDilation b.1 b.2 v) ∘ ratio) _
  exact ((positiveRayDilation_continuous v).stronglyMeasurable.comp_measurable hc.measurable).aestronglyMeasurable

private theorem integrable_compactDilationTest (φ : C_c(ℝ≥0ˣ, ℂ)) :
    Integrable φ positiveRealHaar := by
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport

section Smoothed

/-- Every compact test gives a bounded integral operator for the strong unitary dilation
representation. -/
theorem exists_compactDilationAction (φ : C_c(ℝ≥0ˣ, ℂ)) :
    ∃ T : H →L[ℂ] H, ∀ v, T v = ∫ a : ℝ≥0ˣ, φ a • positiveRayDilation a.val
      (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr a.ne_zero)) v ∂positiveRealHaar :=
  ⟨integratedUnitary positiveRealHaar normDilation normDilation_measurable φ
    (integrable_compactDilationTest φ), fun _ ↦ rfl⟩

/-- The Bochner integral of normalized dilations against the project's multiplicative Haar
measure `da/a`, acting on each input vector. -/
def compactDilationAction (φ : C_c(ℝ≥0ˣ, ℂ)) : H →L[ℂ] H :=
  (exists_compactDilationAction φ).choose

/-- Applying the compact dilation action integrates the actual positive-frequency unitaries. -/
theorem compactDilationAction_apply (φ : C_c(ℝ≥0ˣ, ℂ)) (v : H) :
    compactDilationAction φ v = ∫ a : ℝ≥0ˣ, φ a • positiveRayDilation a.val
      (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr a.ne_zero)) v ∂positiveRealHaar :=
  (exists_compactDilationAction φ).choose_spec v

/-- The polar trace of the compactly smoothed gated dilation. All tests and gates may be
complex. The Haar integral retains the original band vector on both sides. -/
theorem hilbertTrace_compactDilation_multiplier_polar (φ : C_c(ℝ≥0ˣ, ℂ))
    (Q : ℝ → ℂ) (hQ : Measurable Q) (C : ℝ) (hC : 0 ≤ C) (hQC : ∀ t, ‖Q t‖ ≤ C)
    {B : ℝ} (hB : 0 < B) :
    hilbertTrace (polarRankOne ((compactDilationAction φ).comp
      (positiveRayMultiplier Q hQ C hC hQC B)) (bandVector B)) =
      ∫ a : ℝ≥0ˣ, φ a * ((Real.sqrt a.val : ℂ)⁻¹ * ∫ u in Ioc 0 (min 1 (a.val : ℝ)), Q u)
        ∂positiveRealHaar := by
  let e := bandVector B
  let v := positiveRayMultiplier Q hQ C hC hQC B e
  have hi := integrable_weightedOrbit positiveRealHaar normDilation normDilation_measurable
    (integrable_compactDilationTest φ) v
  rw [hilbertTrace_polarRankOne, ContinuousLinearMap.comp_apply, compactDilationAction_apply]
  change (innerSL ℂ e) (∫ a : ℝ≥0ˣ, φ a • normDilation a v ∂positiveRealHaar) = _
  rw [← (innerSL ℂ e).integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards with a
  rw [map_smul, smul_eq_mul]
  exact congrArg (φ a * ·)
    (inner_bandVector_dilation_multiplier Q hQ C hC hQC (positiveNormRatio a) hB)

/-- The sharp-cutoff correction before its minus sign, under the actual compactly smoothed
dilation operator. The weight is `min(a, r) / sqrt(a)` against the multiplicative Haar measure. -/
theorem hilbertTrace_compactDilation_sharp_polar (φ : C_c(ℝ≥0ˣ, ℂ))
    {B r : ℝ} (hB : 0 < B) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    hilbertTrace (polarRankOne ((compactDilationAction φ).comp (sharpMultiplier r B))
      (bandVector B)) =
      ∫ a : ℝ≥0ˣ, φ a * ((Real.sqrt a.val : ℂ)⁻¹ * (min (a.val : ℝ) r : ℝ))
        ∂positiveRealHaar := by
  rw [sharpMultiplier, hilbertTrace_compactDilation_multiplier_polar _ _ _ _ _ _ hB]
  apply integral_congr_ae
  filter_upwards with a
  rw [sharpGate_integral (positiveNormRatio a).le hr hr1]

/-- Keeping the original band while removing its flat mean changes the compactly smoothed
sharp-gate compression by a nuclear operator with the indicated negative trace.

Reconstruction: the relative polar trace in the zero-order real even model of (12.4.1.8),
p. 517, with the frequency gate inside the original band. -/
theorem compactDilation_sharp_compression_difference (φ : C_c(ℝ≥0ˣ, ℂ))
    {B r : ℝ} (hB : 0 < B) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    let T := (compactDilationAction φ).comp (sharpMultiplier r B)
    let E := (frequencyBand B).starProjection
    let P := (meanZeroFrequencyBand B).starProjection
    ∃ R : nuclearEndomorphisms H, R.val = P.comp (T.comp P) - E.comp (T.comp E) ∧
      hilbertTrace R = -(∫ a : ℝ≥0ˣ, φ a * ((Real.sqrt a.val : ℂ)⁻¹ * (min (a.val : ℝ) r : ℝ))
        ∂positiveRealHaar) := by
  let T := (compactDilationAction φ).comp (sharpMultiplier r B)
  obtain ⟨R, hR, htr⟩ := polarFree_compression_difference T (frequencyBand B)
    (norm_bandVector hB) (bandVector_mem_frequencyBand B)
  refine ⟨R, ?_, ?_⟩
  · simpa only [frequencyBand_starProjection_sub_line] using hR
  · rw [htr, ← hilbertTrace_polarRankOne, hilbertTrace_compactDilation_sharp_polar φ hB hr hr1]

/-- If the test vanishes below the gate, the trace reads off its negative half-moment,
multiplied by the gate radius. -/
theorem hilbertTrace_compactDilation_sharp_polar_of_support (φ : C_c(ℝ≥0ˣ, ℂ))
    {B r : ℝ} (hB : 0 < B) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hφ : ∀ a : ℝ≥0ˣ, (a.val : ℝ) < r → φ a = 0) :
    hilbertTrace (polarRankOne ((compactDilationAction φ).comp (sharpMultiplier r B))
      (bandVector B)) =
      (r : ℂ) * ∫ a : ℝ≥0ˣ, φ a * (Real.sqrt a.val : ℂ)⁻¹ ∂positiveRealHaar := by
  rw [hilbertTrace_compactDilation_sharp_polar φ hB hr hr1, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with a
  by_cases ha : r ≤ (a.val : ℝ)
  · rw [min_eq_right ha]
    ring
  · simp [hφ a (lt_of_not_ge ha)]

end Smoothed

end PositiveRay

end RiemannMasullo.FlatPolar
