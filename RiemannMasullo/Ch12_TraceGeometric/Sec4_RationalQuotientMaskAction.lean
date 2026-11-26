module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalRayEquiv
public import RiemannMasullo.Ch03_IdelicZeta.RatEmptyNormHaar
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatPhysicalDilation
public import RiemannMasullo.Ch09_HardySobolev.Sec3
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The rational quotient norm window and inverse dilation at order zero

In the order-zero rational model on pp. 516–517, the norm multiplier and
the left regular action act on the quotient Haar space. The positive-Haar
half-density of #7667 compares them with the spatial cutoff and physical
reciprocal dilation from #7646. The exact Haar normalization of #7657
identifies the compact test integrals on the quotient and on the positive ray.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped CompactlySupported NumberField.AdeleRing NNReal ENNReal Topology

namespace RiemannMasullo.AnnularBand

set_option maxSynthPendingDepth 8
set_option quotPrecheck false
attribute [local instance] RiemannMasullo.instSIdeleQuotientMeasurableSpaceSec1

local notation "J" => SIdeleQuotient ℚ ∅
local notation "m" => continuousSIdeleQuotientNorm ℚ ∅
local notation "R(" g ")" => (((m g).val : ℝ))
local notation "μ" => sLocalQuotientTamagawaMeasure ℚ ∅
local notation "ν₀" => (μ).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 0 (Real.log (R(g)))))
local notation "Hq" => Lp ℂ 2 ν₀
local notation "ν₊" => volume.restrict (Ioi (0 : ℝ))
local notation "H₊" => Lp ℂ 2 ν₊
local notation "posR(" g ")" => NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m g).ne_zero)

local instance : BorelSpace J := ⟨rfl⟩
local instance : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
local instance : T2Space J := by
  have := isClosed_sProjectedDiagonal (F := ℚ) (S := ∅)
  exact inferInstanceAs (T2Space (_ ⧸ _))
local instance : SecondCountableTopology J := by
  let (v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) : ProperSpace (v.val.adicCompletion ℚ) :=
    properSpace_adicCompletion v.val
  let (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology (SAdeleRing ℚ ∅) := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) → v.val.adicCompletion ℚ)))
  let : SecondCountableTopology (SAdeleRing ℚ ∅)ˣ := (sIdeleGroup_description ℚ ∅).1.secondCountableTopology
  infer_instance
local instance : LocallyCompactSpace J := by
  let : LocallyCompactSpace (SAdeleRing ℚ ∅)ˣ := (sIdeleGroup_description ℚ ∅).2.2.1
  exact inferInstanceAs (LocallyCompactSpace (_ ⧸ _))
local instance : (μ).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := ∅)).1

/-- A radial norm window acts through the ordinary spatial cutoff under the
rational order-zero half-density chart. -/
theorem quotientCutoff_orderZeroHalfTwist
    (h L : ℝ) (u : H₊) :
    modulatedAbsoluteCutoffOperator m ν₀ (Ioc h L) measurableSet_Ioc (orderZeroHalfTwist u) =
      orderZeroHalfTwist (FlatPolar.spatialCutoff h L u) := by
  apply Lp.ext
  filter_upwards [modulatedAbsoluteCutoffOperator_apply m ν₀ (Ioc h L) measurableSet_Ioc (orderZeroHalfTwist u),
    orderZeroHalfTwist_coeFn_of_ae_eq u u (Lp.stronglyMeasurable u).measurable .rfl,
    orderZeroHalfTwist_coeFn_of_ae_eq _ _ ((Lp.stronglyMeasurable u).measurable.indicator measurableSet_Ioc)
      (FlatPolar.spatialCutoff_apply h L u)] with q hcut hu hout
  rw [hcut, hu, hout]
  by_cases hq : R(q) ∈ Ioc h L
  · simp [modulatedAbsoluteCutoff, hq]
  · simp [modulatedAbsoluteCutoff, hq]

/-- Left translation by an idèle-quotient element of norm `a` acts through the
flat dilation of scale `1/a`, including the square-root multiplier. -/
theorem quotientTranslation_orderZeroHalfTwist
    (g : J) (u : H₊) :
    hardySobolevTranslation μ m 0 0 0 le_rfl le_rfl g (orderZeroHalfTwist u) =
      orderZeroHalfTwist (FlatPolar.positiveRayDilation R(g)⁻¹ (inv_pos.mpr (posR(g))) u) := by
  let a : ℝ := R(g)⁻¹
  have ha : 0 < a := inv_pos.mpr (posR(g))
  have hu := orderZeroHalfTwist_coeFn_of_ae_eq u u (Lp.stronglyMeasurable u).measurable .rfl
  have hμ : μ ≤ ν₀ := by simp [intervalSobolevDensity]
  have huμ := hμ.absolutelyContinuous.ae_eq hu
  have htr := (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae_eq_comp huμ
  have hreg := hardySobolevTranslation_apply μ m 0 0 0 le_rfl le_rfl g (orderZeroHalfTwist u)
  have hout := orderZeroHalfTwist_coeFn_of_ae_eq (FlatPolar.positiveRayDilation a ha u)
    (fun t : ℝ ↦ (Real.sqrt a : ℂ) * u (a * t))
    (measurable_const.mul ((Lp.stronglyMeasurable u).measurable.comp (measurable_const.mul measurable_id)))
    (FlatPolar.positiveRayDilation_apply a ha u)
  have houtμ := hμ.absolutelyContinuous.ae_eq hout
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ _).ae_eq
  filter_upwards [hreg, htr, houtμ] with q hq ht ho
  change (orderZeroHalfTwist u) (g⁻¹ * q) = (Real.sqrt (R(g⁻¹ * q)) : ℂ) * u (R(g⁻¹ * q)) at ht
  rw [hq, ht, ho]
  have hval : R(g⁻¹ * q) = a * R(q) := by simp [a, Units.val_inv_eq_inv_val]
  simp only [hval, Real.sqrt_mul ha.le, Complex.ofReal_mul]
  ring

/-- The rational quotient norm preserves Tamagawa measure and ray Haar. -/
private theorem normMeasurePreserving :
    MeasurePreserving (sIdeleQuotientNorm ℚ ∅) μ positiveRealHaar :=
  ⟨(isProperMap_sIdeleQuotientNorm ℚ ∅).continuous.measurable, RatEmptyNormHaar.map_norm⟩

private theorem integral_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ≥0ˣ → E) :
    (∫ g : J, f (m g) ∂μ) = ∫ a : ℝ≥0ˣ, f a ∂positiveRealHaar := by
  have hp := isProperMap_sIdeleQuotientNorm ℚ ∅
  have he : Topology.IsClosedEmbedding (sIdeleQuotientNorm ℚ ∅) :=
    .of_continuous_injective_isClosedMap hp.continuous sIdeleQuotientNorm_ratEmpty_injective hp.isClosedMap
  exact normMeasurePreserving.integral_comp he.measurableEmbedding f

/-- The negative half-moment of a native quotient test in Tamagawa measure equals its ray half-moment. -/
theorem rationalQuotient_negativeHalfMoment_eq_ray (ψ : J → ℂ) (φ : ℝ≥0ˣ → ℂ)
    (hφ : ∀ g : J, φ (m g) = ψ g) :
    (∫ g : J, ψ g / (Real.sqrt (R(g)) : ℂ) ∂μ) =
      ∫ a : ℝ≥0ˣ, φ a / (Real.sqrt a.val : ℂ) ∂positiveRealHaar := by
  simp_rw [← hφ]
  exact integral_norm (fun a : ℝ≥0ˣ ↦ φ a / (Real.sqrt a.val : ℂ))

/-- The quotient symbol for a compact complex test on positive ratios. Properness
of the quotient norm ensures its pullback still has compact support. -/
def rationalQuotientRadialTest (φ : C_c(ℝ≥0ˣ, ℂ)) : C_c(J, ℂ) :=
  φ.comp ⟨⟨m, (m).continuous⟩, (isProperMap_iff_tendsto_cocompact.mp
    (isProperMap_sIdeleQuotientNorm ℚ ∅)).2⟩

@[simp] theorem rationalQuotientRadialTest_apply (φ : C_c(ℝ≥0ˣ, ℂ)) (q : J) :
    rationalQuotientRadialTest φ q = φ (m q) := rfl

/-- The Chapter 9 Haar convolution by the norm pullback of a compact radial
test, on the genuine rational quotient at order zero. -/
def rationalQuotientRadialConvolution (φ : C_c(ℝ≥0ˣ, ℂ)) : Hq →L[ℂ] Hq :=
  let ψ := rationalQuotientRadialTest φ
  hardySobolevConvolution μ m 0 0 0 le_rfl le_rfl ψ ψ.continuous.aemeasurable ψ.hasCompactSupport
    ⟨‖ψ.toBoundedContinuousFunction‖, fun g ↦ ψ.toBoundedContinuousFunction.norm_coe_le_norm g⟩

/-- The actual quotient convolution is the Haar integral of inverse group
translations with the pulled-back scalar test. -/
theorem rationalQuotientRadialConvolution_eq_integral (φ : C_c(ℝ≥0ˣ, ℂ)) (u : Hq) :
    rationalQuotientRadialConvolution φ u =
      ∫ g : J, φ (m g) • hardySobolevTranslation μ m 0 0 0 le_rfl le_rfl g u ∂μ := by
  let ψ := rationalQuotientRadialTest φ
  have hb : ∃ C : ℝ, ∀ g, ‖ψ g‖ ≤ C :=
    ⟨‖ψ.toBoundedContinuousFunction‖, fun g ↦ ψ.toBoundedContinuousFunction.norm_coe_le_norm g⟩
  exact hardySobolev_eq_integral_translation_of_convolution μ m 0 0 0 le_rfl le_rfl
    (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport) ψ.hasCompactSupport _
    (fun v ↦ (hardySobolevConvolution_apply μ m 0 0 0 le_rfl le_rfl ψ
      ψ.continuous.aemeasurable ψ.hasCompactSupport hb v).mono fun _ hx ↦ hx.2) u

/-- Integrating the exact quotient translations gives the physical reciprocal
dilation action with the original test and original multiplicative ray Haar. -/
theorem quotientRadialConvolution_orderZeroHalfTwist
    (φ : C_c(ℝ≥0ˣ, ℂ)) (u : H₊) :
    rationalQuotientRadialConvolution φ (orderZeroHalfTwist u) =
      orderZeroHalfTwist (FlatPolar.compactInverseDilationAction φ u) := by
  let F (a : ℝ≥0ˣ) := FlatPolar.positiveRayDilation (a.val : ℝ)⁻¹
    (inv_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr a.ne_zero))) u
  let U : H₊ →L[ℂ] Hq := orderZeroHalfTwist
  let K (a : ℝ≥0ˣ) := U (φ a • F a)
  rw [rationalQuotientRadialConvolution_eq_integral]
  calc
    (∫ g : J, φ (m g) • hardySobolevTranslation μ m 0 0 0 le_rfl le_rfl g (orderZeroHalfTwist u) ∂μ)
        = ∫ g : J, K (m g) ∂μ := by
            apply integral_congr_ae
            filter_upwards with g
            rw [quotientTranslation_orderZeroHalfTwist]
            exact (map_smul U _ _).symm
    _ = ∫ a : ℝ≥0ˣ, K a ∂positiveRealHaar := by
          exact integral_norm K
    _ = orderZeroHalfTwist (FlatPolar.compactInverseDilationAction φ u) := by
          rw [FlatPolar.compactInverseDilationAction_apply]
          exact U.integral_comp_comm (FlatPolar.integrable_compactInverseDilation φ u)

/-- Every quotient test in the rational case is pulled back from a compact
continuous test on the norm ray. -/
theorem rationalQuotientRadialTest_surjective :
    Surjective rationalQuotientRadialTest := by
  intro ψ
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section ℚ ∅
  let e : J ≃ₜ ℝ≥0ˣ :=
    ⟨⟨m, σ, fun q ↦ sIdeleQuotientNorm_ratEmpty_injective (hσ _), hσ⟩, (m).continuous, σ.continuous⟩
  refine ⟨ψ.comp e.symm.toCocompactMap, ?_⟩
  ext q
  change ψ (e.symm (e q)) = ψ q
  rw [e.symm_apply_apply]

set_option maxHeartbeats 900000 in
/-- The genuine Chapter 9 regularized test action on any compact Bruhat quotient
test is the physical integral of the corresponding reciprocal dilations. -/
theorem exists_rayTest_hardySobolevTestAction_orderZeroHalfTwist
    (ψ : BruhatCompactSupport J) :
    ∃ φ : C_c(ℝ≥0ˣ, ℂ), (∀ g : J, φ (m g) = ψ.val g) ∧
      ∀ u : H₊, hardySobolevTestAction μ m 0 0 0 le_rfl le_rfl ψ (orderZeroHalfTwist u) =
        orderZeroHalfTwist (FlatPolar.compactInverseDilationAction φ u) := by
  have hψ : Continuous ψ.val := continuous_of_bruhatSmooth
    ((mem_bruhatSmoothSubmodule_iff ψ.val).1 ψ.property.1)
  let ψc : C_c(J, ℂ) := ⟨⟨ψ.val, hψ⟩, ψ.property.2⟩
  have hex : ∃ φ : C_c(ℝ≥0ˣ, ℂ), rationalQuotientRadialTest φ = ψc :=
    rationalQuotientRadialTest_surjective ψc
  obtain ⟨φ, hφ⟩ := hex
  have hp (g : J) : φ (m g) = ψ.val g := congrArg (fun f : C_c(J, ℂ) ↦ f g) hφ
  refine ⟨φ, hp, fun u ↦ ?_⟩
  have hA := hardySobolev_eq_integral_translation_of_convolution μ m 0 0 0 le_rfl le_rfl
    (hψ.integrable_of_hasCompactSupport ψ.property.2) ψ.property.2 _
    (hardySobolevTestAction_apply μ m 0 0 0 le_rfl le_rfl ψ) (orderZeroHalfTwist u)
  have hi : (∫ g : J, ψ.val g • hardySobolevTranslation μ m 0 0 0 le_rfl le_rfl g (orderZeroHalfTwist u) ∂μ)
      = ∫ g : J, φ (m g) • hardySobolevTranslation μ m 0 0 0 le_rfl le_rfl g (orderZeroHalfTwist u) ∂μ :=
    integral_congr_ae (.of_forall fun g ↦ congrArg (fun z : ℂ ↦ z • _) (hp g).symm)
  exact hA.trans (hi.trans ((rationalQuotientRadialConvolution_eq_integral φ _).symm.trans
    (quotientRadialConvolution_orderZeroHalfTwist φ u)))

set_option maxHeartbeats 900000 in
/-- Every genuine Bruhat test supported in a closed norm window gives the same native
convolution as a compact ray test whose support lies in that window. -/
theorem exists_rayTest_support_hardySobolevTestAction_eq
    (ψ : BruhatCompactSupport J) (K : Set ℝ) (hK : IsClosed K)
    (hψ : ∀ g : J, ψ.val g ≠ 0 → R(g) ∈ K) :
    ∃ φ : C_c(ℝ≥0ˣ, ℂ), (∀ g : J, φ (m g) = ψ.val g) ∧
      (∀ a ∈ tsupport φ, (a.val : ℝ) ∈ K) ∧
      hardySobolevTestAction μ m 0 0 0 le_rfl le_rfl ψ = rationalQuotientRadialConvolution φ := by
  obtain ⟨φ, hφ, hact⟩ := exists_rayTest_hardySobolevTestAction_orderZeroHalfTwist ψ
  refine ⟨φ, hφ, ?_, ?_⟩
  · obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section ℚ ∅
    change closure (support φ) ⊆ (fun a : ℝ≥0ˣ ↦ (a.val : ℝ)) ⁻¹' K
    apply closure_minimal _ (hK.preimage (NNReal.continuous_coe.comp Units.continuous_val))
    intro a ha
    have hnorm : m (σ a) = a := hσ a
    have hva : φ a = ψ.val (σ a) := by simpa only [hnorm] using hφ (σ a)
    exact hnorm ▸ hψ (σ a) (hva ▸ (show φ a ≠ 0 from ha))
  · apply ContinuousLinearMap.ext
    intro f
    obtain ⟨u, rfl⟩ := orderZeroHalfTwist.surjective f
    exact (hact u).trans (quotientRadialConvolution_orderZeroHalfTwist φ u).symm

/-- The product appearing in the finite arithmetic operator acts on a lifted
ray vector by first taking physical reciprocal dilations and then the spatial
cutoff. -/
theorem quotientCutoff_radialConvolution_orderZeroHalfTwist
    (h L : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) (u : H₊) :
    modulatedAbsoluteCutoffOperator m ν₀ (Ioc h L) measurableSet_Ioc
      (rationalQuotientRadialConvolution φ (orderZeroHalfTwist u)) =
      orderZeroHalfTwist (FlatPolar.spatialCutoff h L (FlatPolar.compactInverseDilationAction φ u)) := by
  rw [quotientRadialConvolution_orderZeroHalfTwist, quotientCutoff_orderZeroHalfTwist]

end RiemannMasullo.AnnularBand
