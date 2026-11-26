module

public import RiemannMasullo.AppA_AlgebraicNT.Sec3_PositiveHaarHalfDensity
public import RiemannMasullo.Ch03_IdelicZeta.RatEmptyNormHaar
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelBridge
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-!
# The order-zero half-density on the rational idèle quotient

The quotient norm preserves the Tamagawa measure at the empty finite stage. Pulling
mrshu's positive-Haar half-density back along this norm identifies the positive
Lebesgue ray with the order-zero Sobolev ambient.
-/

public noncomputable section

open Function MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false
attribute [local instance] RiemannMasullo.instSIdeleQuotientMeasurableSpaceSec1
local instance : BorelSpace (SIdeleQuotient ℚ ∅) := ⟨rfl⟩
local instance : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _

local notation "J" => SIdeleQuotient ℚ ∅
local notation "N" => sIdeleQuotientNorm ℚ ∅
local notation "m" => continuousSIdeleQuotientNorm ℚ ∅
local notation "R(" g ")" => ((m g).val : ℝ)
local notation "μ" => sLocalQuotientTamagawaMeasure ℚ ∅
local notation "ν₀" => (μ).withDensity (fun g ↦ ENNReal.ofReal
  (intervalSobolevDensity 0 0 0 (Real.log (R(g)))))
local notation "ray" => volume.restrict (Ioi (0 : ℝ))

/-- The quotient norm is injective at the empty rational finite stage. -/
theorem sIdeleQuotientNorm_ratEmpty_injective : Function.Injective (sIdeleQuotientNorm ℚ ∅) :=
  ratEmptyLevel_norm_injective

/-- Every absolute-norm lift takes quotient null sets to Lebesgue null preimages. -/
theorem quasiMeasurePreserving_ratEmpty_normLift (κ : ℝ → J)
    (hκ : ∀ x : ℝ, x ≠ 0 → ((N (κ x) : ℝ≥0) : ℝ) = |x|) :
    QuasiMeasurePreserving κ volume ν₀ := by
  obtain ⟨_, κ₀, _, _, hκ₀, _, hμ, _⟩ :=
    exists_linearIsometry_map_sLocalInvariantPWSobolev_rat (1 : PontryaginDual (N).ker) (Y := 1) one_pos
  apply hμ.congr
  filter_upwards [(volume : Measure ℝ).ae_ne (0 : ℝ)] with x hx
  exact sIdeleQuotientNorm_ratEmpty_injective (Units.ext (NNReal.eq ((hκ₀ x hx).trans (hκ x hx).symm)))

namespace AnnularBand

private def normCoordinate : J ≃ᵐ ℝ≥0ˣ :=
  let σ := Classical.choose (sIdeleQuotientNorm_exists_section ℚ ∅)
  let hσ := Classical.choose_spec (sIdeleQuotientNorm_exists_section ℚ ∅)
  { toFun := N
    invFun := σ
    left_inv := fun g ↦ sIdeleQuotientNorm_ratEmpty_injective (hσ (N g))
    right_inv := hσ
    measurable_toFun := (m).continuous.measurable
    measurable_invFun := σ.continuous.measurable }

private theorem normCoordinate_preserving : MeasurePreserving normCoordinate ν₀ positiveRealHaar := by
  have hμ : ν₀ = μ := by simp [intervalSobolevDensity]
  refine ⟨normCoordinate.measurable, ?_⟩
  rw [hμ]
  exact RatEmptyNormHaar.map_norm

private def haarPullback : Lp ℂ 2 positiveRealHaar ≃ₗᵢ[ℂ] Lp ℂ 2 ν₀ := by
  let L := Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ normCoordinate normCoordinate_preserving
  apply LinearIsometryEquiv.ofSurjective L
  intro v
  refine ⟨Lp.compMeasurePreserving normCoordinate.symm (normCoordinate_preserving.symm normCoordinate) v, ?_⟩
  change Lp.compMeasurePreserving normCoordinate normCoordinate_preserving _ = _
  rw [← Lp.compMeasurePreserving_comp_apply]
  simpa only [MeasurableEquiv.symm_comp_self] using Lp.compMeasurePreserving_id_apply v

/-- The half-density isometry from positive Lebesgue measure onto the actual rational
quotient at order zero. -/
def orderZeroHalfTwist : Lp ℂ 2 ray ≃ₗᵢ[ℂ] Lp ℂ 2 ν₀ :=
  RatEmptyHaarHalfDensity.halfDensity.symm.trans haarPullback

/-- The representative of the order-zero half-twist is `sqrt(r) f(r)` at quotient norm `r`. -/
theorem orderZeroHalfTwist_coeFn_of_ae_eq (u : Lp ℂ 2 ray) (f : ℝ → ℂ)
    (_hf : Measurable f) (hu : (u : ℝ → ℂ) =ᵐ[ray] f) :
    (orderZeroHalfTwist u : J → ℂ) =ᵐ[ν₀] fun q ↦ (Real.sqrt (R(q)) : ℂ) * f (R(q)) := by
  let z := RatEmptyHaarHalfDensity.halfDensity.symm u
  have hz : (orderZeroHalfTwist u : J → ℂ) =ᵐ[ν₀] z ∘ normCoordinate :=
    Lp.coeFn_compMeasurePreserving z normCoordinate_preserving
  have hval := RatEmptyHaarHalfDensity.halfDensity_symm_apply_ae u
  have hrep := RatEmptyHaarHalfDensity.rad_ae (P := fun x ↦ u x = f x) hu
  filter_upwards [hz, normCoordinate_preserving.quasiMeasurePreserving.ae hval,
    normCoordinate_preserving.quasiMeasurePreserving.ae hrep] with q hq hv hr
  exact hq.trans (hv.trans (congrArg (fun a : ℂ ↦ (Real.sqrt (R(q)) : ℂ) * a) hr))

end AnnularBand
end RiemannMasullo
