module

public import RiemannMasullo.Ch03_IdelicZeta.RatEmptyNormHaar
public import RiemannMasullo.Ch11_ShellStructure.Sec2b_RatEmptyBandChart
public import RiemannMasullo.Ch06_LocalGlobal.Sec2
public import RiemannMasullo.Ch11_ShellStructure.Sec2b_Printed
public import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! # The actual order-zero rational local invariant level

The reflexive Fourier test box and the normalized quotient measure are
transported to the positive norm coordinate. At the half twist every actual
generator comes from a real polar Schwartz source through the two signs. -/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology
namespace RiemannMasullo.RatEmptyMeasureCoordinate

local notation "S₀" => (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
local notation "J" => SIdeleQuotient ℚ S₀
local notation "N" => sIdeleQuotientNorm ℚ S₀
local notation "ν" => sLocalQuotientTamagawaMeasure ℚ S₀
local instance : MeasurableSpace J := borel _
local instance : BorelSpace J := ⟨rfl⟩
local instance : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _

/-- Use the projected canonical norm section, not a choice of a representative of a norm fibre. -/
def normHomeomorph : J ≃ₜ ℝ≥0ˣ := by
  let p := Units.map (adeleProjection ℚ S₀).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S₀ ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let τ := fun t ↦ (QuotientGroup.mk (p (canonicalIdeleNormSection ℚ t)) : J)
  have hr : RightInverse τ N := fun t ↦ (sIdeleQuotientNorm_mk ℚ S₀ _).trans
    (sIdeleNorm_project_canonicalSection ℚ S₀ t)
  exact { toFun := N, invFun := τ, left_inv := fun x ↦ ratEmpty_sIdeleQuotientNorm_injective (hr (N x)),
          right_inv := hr, continuous_toFun := (isProperMap_sIdeleQuotientNorm ℚ S₀).continuous,
          continuous_invFun := QuotientGroup.continuous_mk.comp (hp.comp (canonicalIdeleNormSection_continuous ℚ)) }

abbrev normEquiv := normHomeomorph.toMeasurableEquiv

theorem normEquiv_apply (g : J) : normEquiv g = N g := by rfl

theorem norm_preserving : MeasurePreserving normEquiv ν positiveRealHaar :=
  ⟨normEquiv.measurable, RatEmptyNormHaar.map_norm⟩

theorem zero_density (x : ℝ) : intervalSobolevDensity 0 0 0 x = 1 := by
  simp [intervalSobolevDensity]

local notation "ν₀" => Measure.withDensity ν (fun g ↦ ENNReal.ofReal
  (intervalSobolevDensity 0 0 0 (Real.log ((Units.val (N g) : ℝ≥0) : ℝ))))

theorem zero_measure : ν₀ = ν := by simp [zero_density]

/-- Pullback from Haar norm coordinates onto the actual order-zero ambient. Its inverse
puts an ambient vector in norm coordinates. -/
def haarAmbient : Lp ℂ 2 positiveRealHaar ≃ₗᵢ[ℂ] Lp ℂ 2 ν₀ := by
  have hw : MeasurePreserving normEquiv ν₀ positiveRealHaar := by
    rw [zero_measure]
    exact norm_preserving
  let L := Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ normEquiv hw
  apply LinearIsometryEquiv.ofSurjective L
  intro v
  refine ⟨Lp.compMeasurePreserving normEquiv.symm (hw.symm normEquiv) v, ?_⟩
  change Lp.compMeasurePreserving normEquiv hw _ = _
  rw [← Lp.compMeasurePreserving_comp_apply]
  simpa only [MeasurableEquiv.symm_comp_self] using Lp.compMeasurePreserving_id_apply v

/-- Pointwise interpretation of the isometry for transporting generators, only up to AE. -/
theorem haarAmbient_apply (u : Lp ℂ 2 positiveRealHaar) :
    haarAmbient u =ᵐ[ν₀] u ∘ normEquiv :=
  Lp.coeFn_compMeasurePreserving _ _

end RiemannMasullo.RatEmptyMeasureCoordinate

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped FourierTransform NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.RatEmptyGenuineLevel

local instance : MeasurableSpace (SIdeleQuotient ℚ ∅) := borel _
local notation "S₀" => (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
local notation "J" => SIdeleQuotient ℚ S₀
local notation "N" => sIdeleQuotientNorm ℚ S₀
local notation "ν" => sLocalQuotientTamagawaMeasure ℚ S₀
local notation "r₀(" g ")" => ((Units.val (N g) : ℝ≥0) : ℝ)
local notation "W" => Lp ℂ 2 (Measure.withDensity ν (fun g ↦ ENNReal.ofReal
  (intervalSobolevDensity 0 0 0 (Real.log r₀(g)))))
local notation "halfPos" => (by norm_num : (0 : ℝ) < 1 / 2)
local notation "polar" => sAdelePolarSubspace ℚ S₀
local notation "inBand(" B ")" => sLocalPWTests (S := S₀) (T := S₀) le_rfl
  (sLocalPWProductRegion (F := ℚ) S₀ B)
local notation "π₀" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace

/-- The source conditions concern the full test, before taking its even part. -/
def RealPolarBand (B : ℝ) (φ : SchwartzMap ℝ ℂ) : Prop :=
  φ 0 = 0 ∧ (𝓕 φ : SchwartzMap ℝ ℂ) 0 = 0 ∧
    tsupport ⇑(𝓕 φ : SchwartzMap ℝ ℂ) ⊆ Icc (-B) B

def profile (φ : SchwartzMap ℝ ℂ) (r : ℝ) : ℂ :=
  ((r ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (φ r + φ (-r))

private theorem generator_ae (ω : PontryaginDual (N).ker) (f : polar) (φ : SchwartzMap ℝ ℂ)
    (hf : ∀ x : SAdeleRing ℚ S₀, f.val (Multiplicative.ofAdd x) = φ (π₀ (x.1 Rat.infinitePlace))) :
    (sLocalPWThetaSobolevMap (s := 0) halfPos ω f : J → ℂ) =ᵐ[ν] fun g ↦ profile φ r₀(g) := by
  apply (sLocalPWThetaSobolevMap_apply (s := 0) halfPos ω f).trans
  apply ae_of_all
  intro g
  change (↑(r₀(g) ^ (1 / 2 : ℝ)) : ℂ) *
    sLocalHomogeneousAdelicThetaLinearMap ℚ S₀ ω f.val g = _
  rw [ratEmpty_homogeneousTheta_real ω φ f.val hf g]
  have hm : (sLocalNormOneQuotientMeasure ℚ S₀).real univ = 1 := by
    simp [Measure.real, RatEmptyNormHaar.norm_one_mass]
  simp only [hm, Complex.ofReal_one, one_mul, profile]

/-- Exact range of the family whose closed span defines the local invariant level. -/
theorem generators_eq (ω : PontryaginDual (N).ker) (B : ℝ) :
    range (fun f : {f : polar // f.val ∈ inBand(B)} ↦
      sLocalPWThetaSobolevMap (s := 0) halfPos ω f.val) =
      {v : W | ∃ φ : SchwartzMap ℝ ℂ, RealPolarBand B φ ∧
        (v : J → ℂ) =ᵐ[ν] fun g ↦ profile φ r₀(g)} := by
  obtain ⟨E, hE⟩ := ratTrivialHomogeneousTheta_quotient_realEquiv
  ext v
  constructor
  · rintro ⟨⟨f, hb⟩, rfl⟩
    let φ := E.symm f.val
    have hf : ∀ x : SAdeleRing ℚ S₀, f.val (Multiplicative.ofAdd x) = φ (π₀ (x.1 Rat.infinitePlace)) := by
      intro x
      simpa only [φ, E.apply_symm_apply] using hE φ x
    exact ⟨φ, (ratEmpty_polar_product_tests_iff φ f.val hf B).mp ⟨f.property, hb⟩,
      generator_ae ω f φ hf⟩
  · rintro ⟨φ, hb, hv⟩
    obtain ⟨hp, hband⟩ := (ratEmpty_polar_product_tests_iff φ (E φ) (hE φ) B).mpr hb
    let f : polar := ⟨E φ, hp⟩
    refine ⟨⟨f, hband⟩, Lp.ext ?_⟩
    exact (withDensity_absolutelyContinuous _ _).ae_le ((generator_ae ω f φ (hE φ)).trans hv.symm)

/-- The genuine arithmetic level, still on the quotient and before Hilbert-space transport. -/
theorem invariant_level_eq (ω : PontryaginDual (N).ker) (B : ℝ) :
    sLocalInvariantPWSobolev (F := ℚ) (S := S₀) (s := 0) le_rfl halfPos ω B =
      (Submodule.span ℂ {v : W | ∃ φ : SchwartzMap ℝ ℂ, RealPolarBand B φ ∧
        (v : J → ℂ) =ᵐ[ν] fun g ↦ profile φ r₀(g)}).topologicalClosure := by
  exact congrArg (fun s : Set W ↦ (Submodule.span ℂ s).topologicalClosure) (generators_eq ω B)

end RiemannMasullo.RatEmptyGenuineLevel
