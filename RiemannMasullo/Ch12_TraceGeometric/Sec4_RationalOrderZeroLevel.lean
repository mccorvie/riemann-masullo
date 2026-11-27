module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalRayEquiv
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWPositiveRay

/-!
# Normalization of the rational order-zero Paley–Wiener isometry

The representative formula of thierryaaron’s #7651 and the isometry property
determine the full-line map and its positive constant. The resulting projection identity
holds for each norm-one character. Mrshu’s #7667 gives the normalized space comparison
directly from the two-sign test generators.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing SchwartzMap Topology

namespace RiemannMasullo.AnnularBand

open FlatPolar

set_option quotPrecheck false
attribute [local instance] RiemannMasullo.instSIdeleQuotientMeasurableSpaceSec1

local notation "J" => SIdeleQuotient ℚ ∅
local notation "m" => continuousSIdeleQuotientNorm ℚ ∅
local notation "ν₀" => (sLocalQuotientTamagawaMeasure ℚ ∅).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 0 (Real.log (((m g).val : ℝ)))))
local notation "Hq" => Lp ℂ 2 ν₀
local notation "Hr" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
local notation "Hl" => Lp ℂ 2 (volume : Measure ℝ)
local notation "N" => sIdeleQuotientNorm ℚ ∅
local notation "V(" ω "," B ")" => sLocalInvariantPWSobolev (F := ℚ) (S := ∅)
  (s := 0) le_rfl (a := 1 / 2) (by norm_num) ω B

/-- The even embedding of the rational order-zero quotient with its canonical
Tamagawa normalization. -/
def orderZeroEvenExtension : Hq →ₗᵢ[ℂ] Hl :=
  positiveRayEvenExtension.comp orderZeroHalfTwist.symm.toLinearIsometry

/-- Every lift of absolute value gives the same almost-everywhere formula for
the normalized quotient isometry. -/
theorem orderZeroEvenExtension_coeFn (κ : ℝ → J)
    (hκ : ∀ x : ℝ, x ≠ 0 → (((N (κ x)).val : ℝ)) = |x|) (F : Hq) :
    (orderZeroEvenExtension F : ℝ → ℂ) =ᵐ[volume] fun x ↦
      ((((Real.sqrt 2)⁻¹ * |x| ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)) * F (κ x) := by
  obtain ⟨u, rfl⟩ := orderZeroHalfTwist.surjective F
  have ht := (quasiMeasurePreserving_ratEmpty_normLift κ hκ).ae
    (orderZeroHalfTwist_coeFn_of_ae_eq u u (Lp.stronglyMeasurable u).measurable .rfl)
  change (positiveRayEvenExtension (orderZeroHalfTwist.symm (orderZeroHalfTwist u)) : ℝ → ℂ) =ᵐ[volume] _
  rw [orderZeroHalfTwist.symm_apply_apply]
  filter_upwards [positiveRayEvenExtension_apply u, ht, (volume : Measure ℝ).ae_ne (0 : ℝ)]
    with x hExt hHalf hx
  change orderZeroHalfTwist u (κ x) = (Real.sqrt (((m (κ x)).val : ℝ)) : ℂ) * u (((m (κ x)).val : ℝ)) at hHalf
  rw [show ((m (κ x)).val : ℝ) = |x| from hκ x hx] at hHalf
  rw [hExt, hHalf, Real.rpow_neg (abs_nonneg _) (1 / 2), ← Real.sqrt_eq_rpow]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (abs_pos.mpr hx)).ne']

/-- The isometry and positive scalar in the arithmetic level theorem are
unique, independently of the value of the norm lift at zero. -/
theorem orderZeroEvenExtension_unique (U : Hq →ₗᵢ[ℂ] Hl) (κ : ℝ → J) (c : ℝ)
    (hc : 0 < c) (hκ : ∀ x : ℝ, x ≠ 0 → (((N (κ x)).val : ℝ)) = |x|)
    (hU : ∀ F, (U F : ℝ → ℂ) =ᵐ[volume] fun x ↦
      ((c * |x| ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * F (κ x)) :
    U = orderZeroEvenExtension ∧ c = (Real.sqrt 2)⁻¹ := by
  have htwo : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hscale (F : Hq) : U F = ((c * Real.sqrt 2 : ℝ) : ℂ) • orderZeroEvenExtension F := by
    apply Lp.ext
    filter_upwards [hU F, orderZeroEvenExtension_coeFn κ hκ F,
      Lp.coeFn_smul ((c * Real.sqrt 2 : ℝ) : ℂ) (orderZeroEvenExtension F)] with x hU hE hs
    rw [hU, hs]
    change _ = ((c * Real.sqrt 2 : ℝ) : ℂ) * orderZeroEvenExtension F x
    rw [hE]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr htwo.ne']
  have hn := congrArg norm (hscale (orderZeroHalfTwist (bandVector 1)))
  rw [U.norm_map, norm_smul, orderZeroEvenExtension.norm_map, orderZeroHalfTwist.norm_map,
    norm_bandVector (by norm_num : (0 : ℝ) < 1), mul_one, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg hc.le htwo.le)] at hn
  refine ⟨?_, ?_⟩
  · apply LinearIsometry.ext
    intro F
    simpa only [← hn, Complex.ofReal_one, one_smul] using hscale F
  · rw [inv_eq_one_div]
    exact (eq_div_iff htwo.ne').mpr hn.symm

/-- The arithmetic level maps onto the full-line level by this single fixed
isometry for every character of the norm-one quotient and every positive band. -/
theorem map_invariantOrderZeroLevel_evenExtension (ω : PontryaginDual (N).ker) {B : ℝ} (hB : 0 < B) :
    (V(ω,B)).map orderZeroEvenExtension.toLinearMap = realPWLevel B := by
  obtain ⟨U, κ, c, hc, hκ, hU, hlev⟩ := exists_linearIsometry_map_sLocalInvariantPWSobolev_rat ω hB
  rw [← (orderZeroEvenExtension_unique U κ c hc hκ hU).1]
  tauto

/-- In the half-twist coordinates the named arithmetic level is the ray
physical mean-zero subspace. -/
theorem invariantOrderZeroLevel_eq_physicalBand (ω : PontryaginDual (N).ker) {B : ℝ} (hB : 0 < B) :
    V(ω,B) = ((meanZeroFrequencyBand B).map
      (positiveRayInverseCosineEquiv.toLinearEquiv : Hr →ₗ[ℂ] Hr)).map
        (orderZeroHalfTwist.toLinearEquiv : Hr →ₗ[ℂ] Hq) := by
  apply Submodule.map_injective_of_injective (f := orderZeroEvenExtension.toLinearMap)
    orderZeroEvenExtension.injective
  rw [map_invariantOrderZeroLevel_evenExtension ω hB, ← Submodule.map_comp]
  have he : orderZeroEvenExtension.toLinearMap.comp (orderZeroHalfTwist.toLinearEquiv : Hr →ₗ[ℂ] Hq) =
      positiveRayEvenExtension.toLinearMap := by
    apply LinearMap.ext
    intro f
    exact congrArg positiveRayEvenExtension (orderZeroHalfTwist.symm_apply_apply f)
  rw [he, map_physicalMeanZeroBand_positiveRayEvenExtension hB]

/-- The arithmetic projection becomes the actual positive-ray physical
projection after removing the half-twist. -/
theorem invariantOrderZeroLevel_starProjection_halfTwist (ω : PontryaginDual (N).ker)
    {B : ℝ} (hB : 0 < B) (f : Hr) :
    letI : IsClosed (V(ω,B) : Set Hq) := Submodule.isClosed_topologicalClosure _
    (V(ω,B)).starProjection (orderZeroHalfTwist f) =
      orderZeroHalfTwist (physicalMeanZeroBandProjection B f) := by
  let : IsClosed (V(ω,B) : Set Hq) := Submodule.isClosed_topologicalClosure _
  let K := (meanZeroFrequencyBand B).map (positiveRayInverseCosineEquiv.toLinearEquiv : Hr →ₗ[ℂ] Hr)
  have h (V : Submodule ℂ Hq) [V.HasOrthogonalProjection]
      (he : V = K.map (orderZeroHalfTwist.toLinearEquiv : Hr →ₗ[ℂ] Hq)) :
      V.starProjection (orderZeroHalfTwist f) = orderZeroHalfTwist (K.starProjection f) := by
    subst V
    simpa only [LinearIsometryEquiv.symm_apply_apply] using
      Submodule.starProjection_map_apply orderZeroHalfTwist K (orderZeroHalfTwist f)
  exact h _ (invariantOrderZeroLevel_eq_physicalBand ω hB)

/-- The orthogonal projection onto the rational arithmetic order-zero level. -/
def orderZeroLevelProjection (B : ℝ) : Hq →L[ℂ] Hq := by
  let : IsClosed (V(1,B) : Set Hq) := Submodule.isClosed_topologicalClosure _
  exact (V(1,B)).starProjection

/-- The native projection on the trivial angular block acts on every ray vector. -/
theorem orderZeroLevelProjection_halfTwist {B : ℝ} (hB : 0 < B) (u : Hr) :
    orderZeroLevelProjection B (orderZeroHalfTwist u) =
      orderZeroHalfTwist (physicalMeanZeroBandProjection B u) :=
  invariantOrderZeroLevel_starProjection_halfTwist 1 hB u

/-- Each completed arithmetic level contains a Schwartz profile with nonzero physical integral. -/
theorem exists_invariantOrderZeroLevel_profile_integral_ne_zero
    (ω : PontryaginDual (N).ker) {B : ℝ} (hB : 0 < B) :
    ∃ u ∈ V(ω,B), ∃ F : 𝓢(ℝ, ℂ), orderZeroEvenExtension u = F.toLp 2 volume ∧ (∫ x, F x) ≠ 0 := by
  obtain ⟨F, hF, hi⟩ := exists_mem_realPWLevel_integral_ne_zero hB
  rw [← map_invariantOrderZeroLevel_evenExtension ω hB] at hF
  obtain ⟨u, hu, he⟩ := hF
  exact ⟨u, hu, F, he, hi⟩

/-- The full-line sinc projection restricts on the even chart to the actual arithmetic projection. -/
theorem orderZeroEvenExtension_levelProjection {B : ℝ} (hB : 0 < B) (u : Hq) :
    letI : CompleteSpace (realPWLevel B) := (isClosed_realPWLevel B).completeSpace_coe
    orderZeroEvenExtension (orderZeroLevelProjection B u) =
      (realPWLevel B).starProjection (orderZeroEvenExtension u) := by
  let : CompleteSpace (realPWLevel B) := (isClosed_realPWLevel B).completeSpace_coe
  obtain ⟨f, rfl⟩ := orderZeroHalfTwist.surjective u
  rw [orderZeroLevelProjection_halfTwist hB]
  change positiveRayEvenExtension (orderZeroHalfTwist.symm (orderZeroHalfTwist _)) =
    (realPWLevel B).starProjection (positiveRayEvenExtension (orderZeroHalfTwist.symm (orderZeroHalfTwist f)))
  simp only [LinearIsometryEquiv.symm_apply_apply]
  exact (realPWLevel_starProjection_positiveRayEvenExtension hB f).symm

end RiemannMasullo.AnnularBand
