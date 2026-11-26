module

public import RiemannMasullo.Ch11_ShellStructure.Sec2b
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelClosure
import RiemannMasullo.Ch03_IdelicZeta.RatEmptyFourier
import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3a
import RiemannMasullo.Ch06_LocalGlobal.Sec2
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # The invariant level over `ℚ` with no finite place is the real Paley–Wiener level

Paper: Definition 11.2.1.3(1) and (11.2.1.6), p. 488, as used in Theorem 12.4.1.1, pp. 514–519.

`Sec4_RealPWLevelClosure` and `Sec4_RealPWLevelOperator` work in a model: even functions of
`L²(ℝ)` with Fourier transform in `[-Y, Y]` that vanish at the origin. This file proves that the
model is the object of the project. For `F = ℚ`, `S = ∅`, order `s = 0` and twist `a = 1/2`,
the level `sLocalInvariantPWSobolev` of `Ch11_ShellStructure/Sec2b` is carried onto
`realPWLevel Y` by an explicit linear isometry.

* `exists_linearIsometry_map_sLocalInvariantPWSobolev_rat`: there are a linear isometry `U` from
  the weighted space `L²` of the quotient `(SAdeleRing ℚ ∅)ˣ / {±1}` into `L²(ℝ)`, a map `κ`
  from `ℝ` to the quotient with `κ x` of norm `|x|`, and a constant `c > 0`, such that
  `(U F) (x) = c |x|^(-1/2) F (κ x)` for almost every `x`, and the image under `U` of
  `sLocalInvariantPWSobolev` with parameter `Y` is `realPWLevel Y`.

The steps of the proof.

* The norm identifies the quotient with the positive reals, and it carries the quotient measure
  to a positive multiple of `dt / t` by uniqueness of Haar measure. The map `x ↦ |x|` carries
  `dx / |x|` on the real line to twice `dt / t`. So composition with `κ` and multiplication by
  the square root of the density is an isometry into `L²(ℝ)`.
* A Schwartz–Bruhat test on `SAdeleRing ℚ ∅` is a Schwartz function `φ` on `ℝ`. Its weighted
  theta function at twist `1/2` is `|x|^(1/2)` times the mass of the norm-one group times
  `φ x + φ (-x)`, so `U` sends its class to a positive multiple of the class of the even part
  of `φ`.
* The polar conditions and the Fourier support condition on the test are `φ 0 = 0`, `∫ φ = 0`
  and `𝓕 φ` supported in `[-Y, Y]`. Hence the image of the spanning set of the level and the
  polar-free core `realPWPolarFreeCore Y` span the same subspace, and
  `topologicalClosure_span_realPWPolarFreeCore` gives the closure.

The lemmas on units, norms and theta functions over `ℚ` with `S = ∅` are those of
`Ch11_ShellStructure/Sec2b_Printed`, which are private there. The lemma that removes a density
from a weighted `L²` space is the private one of `Ch10_TraceSpectral/Sec4a`.

**Not formalized.** The traces are not transported: the statement is about the level as a
subspace. Under `U` the translation by a class of norm `t` becomes the dilation
`f ↦ t^(-1/2) f (· / t)` and the cutoff to classes of norm at most `L` becomes the cutoff to
`[-L, L]`. Both follow from the formula for `U` and are not stated here. Order zero and the
field `ℚ` with no finite place only.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal ENNReal NumberField.AdeleRing Topology FourierTransform SchwartzMap

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSIdeleQuotientMeasurableSpaceSec1

local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "mₛ(" F ", " S ")" =>
  (continuousSIdeleQuotientNorm F S :
    SIdeleQuotient F S →ₜ* ℝ≥0ˣ)
local notation "μₛ(" F ", " S ")" => sLocalQuotientTamagawaMeasure F S
local notation "localMeasure(" F ", " S ", " s ")" =>
  (μₛ(F, S)).withDensity (fun g ↦
    ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (((mₛ(F, S)) g).val : ℝ))))
local notation "localTheta(" F ", " S ", " a ", " ω ", " f ")" =>
  modulationWeight (mₛ(F, S)) a (sLocalHomogeneousAdelicThetaLinearMap F S ω f)

private theorem ratEmptyLevel_units (ξ : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ) :
    ξ = 1 ∨ ξ = -1 := by
  have hmem : ∀ x : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ),
      ∃ y : 𝓞 ℚ, algebraMap (𝓞 ℚ) ℚ y = (x : ℚ) := by
    intro x
    have he : ((∅ : Finset V(ℚ)) : Set V(ℚ)).integer ℚ = ⊥ := by
      rw [Finset.coe_empty, integer_empty]
    have hx : (x : ℚ) ∈ (⊥ : Subalgebra (𝓞 ℚ) ℚ) := he ▸ x.property
    exact Algebra.mem_bot.mp hx
  obtain ⟨a, ha⟩ := hmem ξ.val
  obtain ⟨b, hb⟩ := hmem (ξ⁻¹).val
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (𝓞 ℚ) ℚ
    rw [map_mul, ha, hb, map_one]
    have h := congrArg Subtype.val ξ.mul_inv
    exact h
  have hu : IsUnit (Rat.ringOfIntegersEquiv a) := (IsUnit.of_mul_eq_one b hab).map _
  rcases Int.isUnit_iff.mp hu with h | h
  · left
    have ha1 : a = 1 := Rat.ringOfIntegersEquiv.injective (h.trans (map_one _).symm)
    apply Units.ext
    apply Subtype.ext
    rw [← ha, ha1, map_one]
    rfl
  · right
    have ha1 : a = -1 := Rat.ringOfIntegersEquiv.injective (h.trans (by simp))
    apply Units.ext
    apply Subtype.ext
    rw [← ha, ha1, map_neg, map_one]
    rfl

private theorem ratEmptyLevel_one_ne_neg_one :
    (1 : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ) ≠ -1 := by
  intro h
  have h' := congrArg (fun u : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ ↦
    Subtype.val (Units.val u)) h
  norm_num at h'

private theorem ratEmptyLevel_norm (x : (SAdeleRing ℚ ∅)ˣ) :
    ((sIdeleNorm ℚ ∅ x : ℝ≥0) : ℝ) = ‖x.val.1 Rat.infinitePlace‖ := by
  simp [sIdeleNorm]
  rw [Unique.eq_default Rat.infinitePlace]

private theorem ratEmptyLevel_abs (z : Rat.infinitePlace.Completion) :
    |InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace z| = ‖z‖ := by
  rw [← Real.norm_eq_abs, ← dist_zero_right, ← dist_zero_right z,
    ← map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)]
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).dist_eq z 0

private theorem ratEmptyLevel_thetaClasses (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (φ : ℝ → ℂ) (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace)))
    (x : (SAdeleRing ℚ ∅)ˣ) :
    sLocalAdelicThetaOnClasses ℚ ∅ f (QuotientGroup.mk x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.val.1 Rat.infinitePlace)) +
      φ (-(InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.val.1 Rat.infinitePlace))) := by
  have hU : (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection ℚ ∅)
      (Subring.subtype (integralAdelesOutside ℚ ∅)))))
      (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal ℚ ∅)) (-1)) = -1 := by
    apply Units.ext
    change ((adeleProjection ℚ ∅).comp (integralAdelesOutside ℚ ∅).subtype)
      (integralAdeleDiagonal ℚ ∅
        (-1 : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ).val) =
      (-1 : (SAdeleRing ℚ ∅)ˣ).val
    simp
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
  dsimp only
  rw [tsum_eq_sum (s := {1, -1}) (fun ξ hξ ↦ ?_)]
  · rw [Finset.sum_pair ratEmptyLevel_one_ne_neg_one]
    simp only [MonoidHom.comp_apply, hU, map_one, one_mul, hf]
    simp only [Units.val_neg, neg_mul, one_mul]
    rw [show ((-(x : SAdeleRing ℚ ∅)).1 Rat.infinitePlace) =
      -((x : SAdeleRing ℚ ∅).1 Rat.infinitePlace) from rfl, map_neg]
  · rcases ratEmptyLevel_units ξ with h | h <;> simp_all

private theorem ratEmptyLevel_normOne_trivial (h : (sIdeleQuotientNorm ℚ ∅).ker) : h = 1 := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  apply Subtype.ext
  change (QuotientGroup.mk x : SIdeleQuotient ℚ ∅) = 1
  rw [sIdeleQuotient_mk_eq_one]
  have hn : ‖x.val.1 Rat.infinitePlace‖ = 1 := by
    rw [← ratEmptyLevel_norm]
    have h1 : sIdeleNorm ℚ ∅ x = 1 := hg
    rw [h1]
    simp
  rw [← ratEmptyLevel_abs] at hn
  rcases (abs_eq zero_le_one).mp hn with h1 | h1
  · refine ⟨1, ?_⟩
    simp only [map_one]
    apply Units.ext
    refine Prod.ext (funext fun w ↦ ?_) (Subsingleton.elim _ _)
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    apply (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).injective
    exact h1.trans (map_one _).symm
  · refine ⟨-1, ?_⟩
    apply Units.ext
    change (x : SAdeleRing ℚ ∅) = ((adeleProjection ℚ ∅).comp (integralAdelesOutside ℚ ∅).subtype)
      (integralAdeleDiagonal ℚ ∅
        (-1 : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ).val)
    simp only [Units.val_neg, Units.val_one, map_neg, map_one]
    refine Prod.ext (funext fun w ↦ ?_) (Subsingleton.elim _ _)
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    apply (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).injective
    exact h1.trans ((map_neg _ _).trans (congrArg Neg.neg (map_one _))).symm

/-- The norm-one quotient over ℚ with `S = ∅` is a point of positive finite mass. -/
private theorem ratEmptyLevel_mass_pos : 0 < (sLocalNormOneQuotientMeasure ℚ ∅).real univ := by
  have := (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := ∅)).1
  have : Subsingleton (sIdeleQuotientNorm ℚ ∅).ker :=
    ⟨fun a b ↦ (ratEmptyLevel_normOne_trivial a).trans (ratEmptyLevel_normOne_trivial b).symm⟩
  have : Finite (sIdeleQuotientNorm ℚ ∅).ker := Finite.of_subsingleton
  have : CompactSpace (sIdeleQuotientNorm ℚ ∅).ker := Finite.compactSpace
  exact ENNReal.toReal_pos (isOpen_univ.measure_pos _ ⟨1, trivial⟩).ne'
    isCompact_univ.measure_lt_top.ne

/-- Over ℚ with `S = ∅` the homogeneous theta function is the theta function on classes
times the total norm-one mass. -/
private theorem ratEmptyLevel_homTheta (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))) (g : SIdeleQuotient ℚ ∅) :
    sLocalHomogeneousAdelicThetaLinearMap ℚ ∅ ω f g =
      ((sLocalNormOneQuotientMeasure ℚ ∅).real univ : ℂ) * sLocalAdelicThetaOnClasses ℚ ∅ f g := by
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply,
    integral_congr_ae (g := fun _ ↦ sLocalAdelicThetaOnClasses ℚ ∅ f g) (ae_of_all _ fun h ↦ ?_)]
  · rw [integral_const, Complex.real_smul]
  · have := ratEmptyLevel_normOne_trivial h
    subst this
    simp


/-- The transition from `∅` to itself is the identity. -/
private theorem ratEmptyLevel_transition (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))) :
    sAdeleSchwartzTransition ℚ (le_refl (∅ : Finset V(ℚ))) f = f := by
  refine Subtype.ext (funext fun x ↦ ?_)
  change sAdeleSchwartzTransition ℚ (le_refl (∅ : Finset V(ℚ))) f
    (Multiplicative.ofAdd (Multiplicative.toAdd x)) = f x
  rw [sAdeleSchwartzTransition_apply, ite_eq_left (fun w ↦ absurd w.2 (Finset.notMem_empty _))]
  rfl


/-- The test of the counterexample lies in the polar subspace. -/
private theorem ratEmptyLevel_polar (φ : SchwartzMap ℝ ℂ) (hφ0 : φ 0 = 0)
    (hFφ0 : (FourierTransform.fourier φ : SchwartzMap ℝ ℂ) 0 = 0)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace))) :
    sAdeleSchwartzTransition ℚ (le_refl (∅ : Finset V(ℚ))) f ∈ sAdelePolarSubspace ℚ ∅ := by
  rw [ratEmptyLevel_transition, mem_sAdelePolarSubspace,
    sAdeleSchwartzFourier_ratEmpty_apply φ f hf, hf]
  exact ⟨by rw [show ((0 : SAdeleRing ℚ ∅).1 Rat.infinitePlace) = 0 from rfl, map_zero, hφ0],
    by rw [show ((0 : SAdeleRing ℚ ∅).1 Rat.infinitePlace) = 0 from rfl, map_zero]; exact hFφ0⟩

/-! ### The measure on the quotient -/

/-- Over ℚ with `S = ∅` the norm is injective on the quotient. -/
private theorem ratEmptyLevel_norm_injective :
    Function.Injective (sIdeleQuotientNorm ℚ ∅) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  exact congrArg Subtype.val (ratEmptyLevel_normOne_trivial ⟨g, MonoidHom.mem_ker.mpr hg⟩)

/-- The exponential parametrization of the positive reals, whose pushforward of Lebesgue measure
is `positiveRealHaar`. -/
private def ratEmptyLevel_exp (t : ℝ) : ℝ≥0ˣ :=
  Units.mk0 (Real.exp t).toNNReal
    (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos t)))

private theorem ratEmptyLevel_exp_val (t : ℝ) :
    ((ratEmptyLevel_exp t).val : ℝ) = Real.exp t := by
  simp [ratEmptyLevel_exp, Real.coe_toNNReal _ (Real.exp_pos t).le]

private theorem ratEmptyLevel_measurable_exp : Measurable ratEmptyLevel_exp :=
  measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable

private theorem ratEmptyLevel_positiveRealHaar :
    positiveRealHaar = Measure.map ratEmptyLevel_exp volume := rfl

/-- The pushforward of the quotient measure along the norm is a positive multiple of `dt/t`. -/
private theorem ratEmptyLevel_map_norm :
    ∃ d : ℝ≥0, 0 < d ∧
      (μₛ(ℚ, ∅)).map (mₛ(ℚ, ∅)) = (d : ℝ≥0∞) • positiveRealHaar := by
  let : BorelSpace (SIdeleQuotient ℚ ∅) := ⟨rfl⟩
  let : (μₛ(ℚ, ∅)).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := ∅)).1
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  let : LocallyCompactSpace (SIdeleQuotient ℚ ∅) := by
    let : LocallyCompactSpace (SAdeleRing ℚ ∅)ˣ := (sIdeleGroup_description ℚ ∅).2.2.1
    let : IsClosed (_ : Set (SAdeleRing ℚ ∅)ˣ) := isClosed_sProjectedDiagonal (F := ℚ) (S := ∅)
    exact inferInstanceAs (LocallyCompactSpace ((SAdeleRing ℚ ∅)ˣ ⧸ _))
  have hsec := (sIdeleQuotientNorm_exists_section (F := ℚ) (S := ∅)).choose_spec
  have hproper := isProperMap_sIdeleQuotientNorm ℚ ∅
  let ζ := (μₛ(ℚ, ∅)).map (mₛ(ℚ, ∅))
  let : ζ.IsHaarMeasure := Measure.isHaarMeasure_map (μₛ(ℚ, ∅)) (mₛ(ℚ, ∅)).toMonoidHom
    (mₛ(ℚ, ∅)).continuous hsec.surjective ((isProperMap_iff_tendsto_cocompact.mp hproper).2)
  let d := Measure.haarScalarFactor ζ positiveRealHaar
  have hζ : ζ = d • positiveRealHaar := Measure.isMulLeftInvariant_eq_smul _ _
  have hd : 0 < d := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  refine ⟨d, hd, ?_⟩
  change ζ = _
  rw [hζ]
  rfl

/-- **Change of variables.** The map `x ↦ log |x|` carries `dx / |x|` on the real line to twice
Lebesgue measure. -/
private theorem ratEmptyLevel_lintegral_log_abs (G : ℝ → ℝ≥0∞) :
    ∫⁻ x : ℝ, ENNReal.ofReal |x|⁻¹ * G (Real.log |x|) = 2 * ∫⁻ t : ℝ, G t := by
  set h : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal |x|⁻¹ * G (Real.log |x|) with hh
  have hpos : ∫⁻ x in Ioi (0 : ℝ), h x = ∫⁻ t : ℝ, G t := by
    have hcv := lintegral_image_eq_lintegral_abs_deriv_mul (s := (univ : Set ℝ))
      (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
      (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn h
    rw [image_univ, Real.range_exp, Measure.restrict_univ] at hcv
    rw [hcv]
    refine lintegral_congr fun t ↦ ?_
    have he : 0 < Real.exp t := Real.exp_pos t
    simp only [hh, abs_of_pos he, Real.log_exp]
    rw [← mul_assoc, ← ENNReal.ofReal_mul he.le, mul_inv_cancel₀ he.ne', ENNReal.ofReal_one,
      one_mul]
  have hneg : ∫⁻ x in Iio (0 : ℝ), h x = ∫⁻ x in Ioi (0 : ℝ), h x := by
    have hcv := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi (0 : ℝ))
      (f := fun x : ℝ ↦ -x) (f' := fun _ ↦ -1) measurableSet_Ioi
      (fun x _ ↦ (hasDerivAt_neg x).hasDerivWithinAt) neg_injective.injOn h
    have him : (fun x : ℝ ↦ -x) '' Ioi (0 : ℝ) = Iio 0 := by
      ext y
      simp only [mem_image, mem_Ioi, mem_Iio]
      exact ⟨fun ⟨x, hx, hxy⟩ ↦ by linarith, fun hy ↦ ⟨-y, by linarith, by ring⟩⟩
    rw [him] at hcv
    rw [hcv]
    refine lintegral_congr fun x ↦ ?_
    simp [hh]
  have hsplit := lintegral_add_compl (μ := volume) h
    (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))
  rw [compl_Ioi, setLIntegral_congr (Iio_ae_eq_Iic (a := (0 : ℝ))).symm, hneg, hpos] at hsplit
  rw [← hsplit, two_mul]

/-- The positive real number of absolute value `|x|`, for `x ≠ 0`. -/
private def ratEmptyLevel_absUnit (x : ℝ) : ℝ≥0ˣ := ratEmptyLevel_exp (Real.log |x|)

private theorem ratEmptyLevel_absUnit_val {x : ℝ} (hx : x ≠ 0) :
    ((ratEmptyLevel_absUnit x).val : ℝ) = |x| := by
  rw [ratEmptyLevel_absUnit, ratEmptyLevel_exp_val, Real.exp_log (abs_pos.mpr hx)]

private theorem ratEmptyLevel_measurable_log_abs : Measurable fun x : ℝ ↦ Real.log |x| :=
  Real.measurable_log.comp continuous_abs.measurable

private theorem ratEmptyLevel_measurable_absUnit : Measurable ratEmptyLevel_absUnit :=
  ratEmptyLevel_measurable_exp.comp ratEmptyLevel_measurable_log_abs

private theorem ratEmptyLevel_measurable_inv_abs :
    Measurable fun x : ℝ ↦ ENNReal.ofReal |x|⁻¹ :=
  (continuous_abs.measurable.inv).ennreal_ofReal

/-- The absolute value carries `dx / |x|` on the real line to twice `dt / t`. -/
private theorem ratEmptyLevel_map_absUnit :
    Measure.map ratEmptyLevel_absUnit (volume.withDensity fun x : ℝ ↦ ENNReal.ofReal |x|⁻¹) =
      (2 : ℝ≥0∞) • positiveRealHaar := by
  have h1 : Measure.map (fun x : ℝ ↦ Real.log |x|)
      (volume.withDensity fun x : ℝ ↦ ENNReal.ofReal |x|⁻¹) = (2 : ℝ≥0∞) • volume := by
    refine Measure.ext_of_lintegral _ fun G hG ↦ ?_
    have hw := lintegral_withDensity_eq_lintegral_mul (volume : Measure ℝ)
      ratEmptyLevel_measurable_inv_abs (hG.comp ratEmptyLevel_measurable_log_abs)
    simp only [Function.comp_apply, Pi.mul_apply] at hw
    rw [lintegral_map hG ratEmptyLevel_measurable_log_abs, hw, lintegral_smul_measure]
    exact ratEmptyLevel_lintegral_log_abs G
  have h2 : Measure.map ratEmptyLevel_exp ((2 : ℝ≥0∞) • (volume : Measure ℝ)) =
      (2 : ℝ≥0∞) • Measure.map ratEmptyLevel_exp volume :=
    Measure.map_smul _ ratEmptyLevel_measurable_exp.aemeasurable
  rw [ratEmptyLevel_positiveRealHaar, ← h2, ← h1,
    Measure.map_map ratEmptyLevel_measurable_exp ratEmptyLevel_measurable_log_abs]
  rfl

/-- A continuous homomorphic section of the norm. -/
private def ratEmptyLevel_section : ℝ≥0ˣ →ₜ* SIdeleQuotient ℚ ∅ :=
  (sIdeleQuotientNorm_exists_section (F := ℚ) (S := ∅)).choose

private theorem ratEmptyLevel_norm_section (t : ℝ≥0ˣ) :
    sIdeleQuotientNorm ℚ ∅ (ratEmptyLevel_section t) = t :=
  (sIdeleQuotientNorm_exists_section (F := ℚ) (S := ∅)).choose_spec t

private theorem ratEmptyLevel_section_norm (g : SIdeleQuotient ℚ ∅) :
    ratEmptyLevel_section (sIdeleQuotientNorm ℚ ∅ g) = g :=
  ratEmptyLevel_norm_injective (ratEmptyLevel_norm_section _)

/-- The class in the quotient of norm `|x|`, for `x ≠ 0`. -/
private def ratEmptyLevel_class (x : ℝ) : SIdeleQuotient ℚ ∅ :=
  ratEmptyLevel_section (ratEmptyLevel_absUnit x)

private theorem ratEmptyLevel_norm_class {x : ℝ} (hx : x ≠ 0) :
    ((sIdeleQuotientNorm ℚ ∅ (ratEmptyLevel_class x) : ℝ≥0) : ℝ) = |x| := by
  rw [ratEmptyLevel_class, ratEmptyLevel_norm_section, ratEmptyLevel_absUnit_val hx]

/-- The constant by which the quotient measure differs from `dt / t`. -/
private def ratEmptyLevel_const : ℝ≥0 := ratEmptyLevel_map_norm.choose

private theorem ratEmptyLevel_const_pos : 0 < ratEmptyLevel_const :=
  ratEmptyLevel_map_norm.choose_spec.1

private theorem ratEmptyLevel_map_norm_eq :
    (μₛ(ℚ, ∅)).map (mₛ(ℚ, ∅)) = (ratEmptyLevel_const : ℝ≥0∞) • positiveRealHaar :=
  ratEmptyLevel_map_norm.choose_spec.2

/-- The density on the real line that the class map carries to the quotient measure:
`(d / 2) / |x|`, and one at the origin. -/
private def ratEmptyLevel_weight (x : ℝ) : ℝ≥0 :=
  if x = 0 then 1 else Real.toNNReal ((ratEmptyLevel_const : ℝ) / 2 * |x|⁻¹)

private theorem ratEmptyLevel_weight_pos (x : ℝ) : 0 < ratEmptyLevel_weight x := by
  unfold ratEmptyLevel_weight
  split_ifs with hx
  · exact one_pos
  · have hd : (0 : ℝ) < ratEmptyLevel_const := NNReal.coe_pos.mpr ratEmptyLevel_const_pos
    exact Real.toNNReal_pos.mpr (by have := abs_pos.mpr hx; positivity)

private theorem ratEmptyLevel_measurable_weight : Measurable ratEmptyLevel_weight := by
  unfold ratEmptyLevel_weight
  refine Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const ?_
  exact (measurable_const.mul continuous_abs.measurable.inv).real_toNNReal

private theorem ratEmptyLevel_withDensity_weight :
    (volume : Measure ℝ).withDensity (fun x ↦ (ratEmptyLevel_weight x : ℝ≥0∞)) =
      ENNReal.ofReal ((ratEmptyLevel_const : ℝ) / 2) •
        (volume : Measure ℝ).withDensity (fun x ↦ ENNReal.ofReal |x|⁻¹) := by
  rw [← withDensity_smul _ ratEmptyLevel_measurable_inv_abs]
  refine withDensity_congr_ae ?_
  have h0 : ∀ᵐ x : ℝ, x ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  filter_upwards [h0] with x hx
  have hd : (0 : ℝ) ≤ (ratEmptyLevel_const : ℝ) / 2 := by positivity
  simp only [ratEmptyLevel_weight, hx, ite_false, Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul hd]
  rfl

private theorem ratEmptyLevel_localMeasure_zero :
    localMeasure(ℚ, ∅, 0) = μₛ(ℚ, ∅) := by
  conv_rhs => rw [← withDensity_one (μ := μₛ(ℚ, ∅))]
  congr 1
  funext g
  simp [intervalSobolevDensity]

/-- The class map carries the weighted Lebesgue measure to the measure of the weighted space of
the project at order zero. -/
private theorem ratEmptyLevel_measurePreserving_class :
    MeasurePreserving ratEmptyLevel_class
      ((volume : Measure ℝ).withDensity (fun x ↦ (ratEmptyLevel_weight x : ℝ≥0∞)))
      (localMeasure(ℚ, ∅, 0)) := by
  have : BorelSpace (SIdeleQuotient ℚ ∅) := ⟨rfl⟩
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have hτ : Measurable (ratEmptyLevel_section : ℝ≥0ˣ → SIdeleQuotient ℚ ∅) :=
    ratEmptyLevel_section.continuous.measurable
  have hN : Measurable (mₛ(ℚ, ∅) : SIdeleQuotient ℚ ∅ → ℝ≥0ˣ) :=
    (mₛ(ℚ, ∅)).continuous.measurable
  refine ⟨hτ.comp ratEmptyLevel_measurable_absUnit, ?_⟩
  have hd : (0 : ℝ) ≤ (ratEmptyLevel_const : ℝ) / 2 := by positivity
  have hc : ENNReal.ofReal ((ratEmptyLevel_const : ℝ) / 2) * 2 = (ratEmptyLevel_const : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul hd, div_mul_cancel₀ _ (two_ne_zero),
      ENNReal.ofReal_coe_nnreal]
  have hcomp : (ratEmptyLevel_section : ℝ≥0ˣ → SIdeleQuotient ℚ ∅) ∘ (mₛ(ℚ, ∅)) = id :=
    funext fun g ↦ ratEmptyLevel_section_norm g
  have hfun : ratEmptyLevel_class =
      (ratEmptyLevel_section : ℝ≥0ˣ → SIdeleQuotient ℚ ∅) ∘ ratEmptyLevel_absUnit := rfl
  have h3 : Measure.map ratEmptyLevel_absUnit (ENNReal.ofReal ((ratEmptyLevel_const : ℝ) / 2) •
      (volume : Measure ℝ).withDensity (fun x ↦ ENNReal.ofReal |x|⁻¹)) =
      ENNReal.ofReal ((ratEmptyLevel_const : ℝ) / 2) • Measure.map ratEmptyLevel_absUnit
        ((volume : Measure ℝ).withDensity (fun x ↦ ENNReal.ofReal |x|⁻¹)) :=
    Measure.map_smul _ ratEmptyLevel_measurable_absUnit.aemeasurable
  rw [ratEmptyLevel_localMeasure_zero, ratEmptyLevel_withDensity_weight, hfun,
    ← Measure.map_map hτ ratEmptyLevel_measurable_absUnit, h3,
    ratEmptyLevel_map_absUnit, smul_smul, hc, ← ratEmptyLevel_map_norm_eq,
    Measure.map_map hτ hN, hcomp, Measure.map_id]

/-- Multiplication by the positive square root of a density sends its weighted L² space
unitarily onto unweighted L², with the pointwise formula for Haar representatives. -/
private theorem ratEmptyLevel_exists_unweight_L2 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (w : X → ℝ≥0) (hw : Measurable w) (hp : ∀ x, 0 < w x) :
    ∃ U : Lp ℂ 2 (μ.withDensity (fun x ↦ (w x : ℝ≥0∞))) ≃ₗᵢ[ℂ] Lp ℂ 2 μ,
      ∀ v, (U v : X → ℂ) =ᵐ[μ] fun x ↦ (Real.sqrt (w x) : ℂ) * v x := by
  let ν := μ.withDensity (fun x ↦ (w x : ℝ≥0∞))
  let c (x : X) : ℂ := Real.sqrt (w x)
  have hμ : μ ≪ ν := withDensity_absolutelyContinuous' hw.coe_nnreal_ennreal.aemeasurable
    (.of_forall fun x ↦ by simpa using (hp x).ne')
  have hc : StronglyMeasurable c := (Complex.measurable_ofReal.comp
    (Real.continuous_sqrt.measurable.comp (measurable_coe_nnreal_real.comp hw))).stronglyMeasurable
  have hc0 (x : X) : c x ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp x)).ne'
  have hc2 (x : X) : ‖c x‖ ^ 2 = (w x : ℝ) := by
    simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (NNReal.coe_nonneg _)]
  have hmem (g : X → ℂ) (hg : StronglyMeasurable g) :
      MemLp g 2 ν ↔ MemLp (fun x ↦ c x * g x) 2 μ := by
    have hcg : StronglyMeasurable (fun x ↦ c x * g x) := hc.mul hg
    rw [memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable,
      memLp_two_iff_integrable_sq_norm hcg.aestronglyMeasurable]
    change Integrable _ (μ.withDensity _) ↔ _
    rw [integrable_withDensity_iff_integrable_smul hw]
    exact integrable_congr (.of_forall fun x ↦ by
      simp only [NNReal.smul_def, smul_eq_mul, norm_mul, mul_pow, hc2])
  let L (v : Lp ℂ 2 ν) := ((hmem v (Lp.stronglyMeasurable v)).mp (Lp.memLp v)).toLp _
  have hL (v : Lp ℂ 2 ν) : (L v : X → ℂ) =ᵐ[μ] fun x ↦ c x * v x := MemLp.coeFn_toLp _
  let J : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := L
      map_add' := fun v u ↦ by
        apply Lp.ext
        filter_upwards [hL (v + u), hL v, hL u, hμ.ae_le (Lp.coeFn_add v u),
          Lp.coeFn_add (L v) (L u)]
          with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h4, Pi.add_apply, h2, h3, mul_add]
      map_smul' := fun k v ↦ by
        apply Lp.ext
        filter_upwards [hL (k • v), hL v, hμ.ae_le (Lp.coeFn_smul k v), Lp.coeFn_smul k (L v)]
          with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h3, Pi.smul_apply, h2, smul_eq_mul,
          smul_eq_mul]
        ring }
  have hnorm (v : Lp ℂ 2 ν) : ‖J v‖ = ‖v‖ := by
    have hi : inner ℂ (J v) (J v) = inner ℂ v v := by
      rw [L2.inner_def, L2.inner_def]
      change _ = ∫ x, inner ℂ (v x) (v x) ∂μ.withDensity _
      rw [integral_withDensity_eq_integral_smul hw]
      refine integral_congr_ae ?_
      filter_upwards [hL v] with x hx
      change inner ℂ (L v x) (L v x) = (w x) • inner ℂ (v x) (v x)
      rw [hx, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
      simp only [norm_mul, NNReal.smul_def, Complex.real_smul]
      have h := congrArg Complex.ofReal
        (show (‖c x‖ * ‖v x‖) ^ 2 = (w x : ℝ) * ‖v x‖ ^ 2 by rw [mul_pow, hc2])
      change (Complex.ofReal (‖c x‖ * ‖v x‖)) ^ 2 =
        Complex.ofReal (w x : ℝ) * Complex.ofReal ‖v x‖ ^ 2
      rw [Complex.ofReal_mul]
      simpa only [Complex.ofReal_mul, Complex.ofReal_pow] using h
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hi
    have hsq : ‖J v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast hi
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  let S : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ := ⟨J, hnorm⟩
  have hsurj : Function.Surjective S := by
    intro v
    let g (x : X) := v x / c x
    have heq (x : X) : c x * g x = v x := by dsimp only [g]; field_simp [hc0 x]
    have hg : MemLp g 2 ν := (hmem g ((Lp.stronglyMeasurable v).div hc)).mpr
      (funext heq ▸ Lp.memLp v)
    refine ⟨hg.toLp g, Lp.ext ?_⟩
    filter_upwards [hL (hg.toLp g), hμ.ae_le hg.coeFn_toLp] with x hx hy
    change L (hg.toLp g) x = v x
    rw [hx, hy, heq]
  exact ⟨LinearIsometryEquiv.ofSurjective S hsurj, hL⟩

/-- **The isometry.** Composition with the class map and multiplication by the square root of
the density send the weighted space of the project at order zero isometrically into `L²(ℝ)`. -/
private theorem ratEmptyLevel_exists_isometry :
    ∃ U : Lp ℂ 2 (localMeasure(ℚ, ∅, 0)) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      ∀ F, (U F : ℝ → ℂ) =ᵐ[volume] fun x ↦
        (Real.sqrt (ratEmptyLevel_weight x) : ℂ) * F (ratEmptyLevel_class x) := by
  obtain ⟨U₂, hU₂⟩ := ratEmptyLevel_exists_unweight_L2 (volume : Measure ℝ) ratEmptyLevel_weight
    ratEmptyLevel_measurable_weight ratEmptyLevel_weight_pos
  let U₁ : Lp ℂ 2 (localMeasure(ℚ, ∅, 0)) →ₗᵢ[ℂ]
      Lp ℂ 2 ((volume : Measure ℝ).withDensity (fun x ↦ (ratEmptyLevel_weight x : ℝ≥0∞))) :=
    Lp.compMeasurePreservingₗᵢ ℂ ratEmptyLevel_class ratEmptyLevel_measurePreserving_class
  have hac : (volume : Measure ℝ) ≪
      (volume : Measure ℝ).withDensity (fun x ↦ (ratEmptyLevel_weight x : ℝ≥0∞)) :=
    withDensity_absolutelyContinuous'
      ratEmptyLevel_measurable_weight.coe_nnreal_ennreal.aemeasurable
      (.of_forall fun x ↦ by simpa using (ratEmptyLevel_weight_pos x).ne')
  refine ⟨U₂.toLinearIsometry.comp U₁, fun F ↦ ?_⟩
  filter_upwards [hU₂ (U₁ F), hac.ae_le
    (Lp.coeFn_compMeasurePreserving F ratEmptyLevel_measurePreserving_class)] with x h1 h2
  change (U₂ (U₁ F) : ℝ → ℂ) x = _
  rw [h1]
  congr 1

/-! ### The theta vectors -/

local notation "r∞" => fun x : SAdeleRing ℚ ∅ ↦
  InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace (x.1 Rat.infinitePlace)

private theorem ratEmptyLevel_sqrt_weight_mul {x : ℝ} (hx : x ≠ 0) :
    Real.sqrt (ratEmptyLevel_weight x) * |x| ^ (1 / 2 : ℝ) =
      Real.sqrt ((ratEmptyLevel_const : ℝ) / 2) := by
  have hd : (0 : ℝ) ≤ (ratEmptyLevel_const : ℝ) / 2 := by positivity
  have hpos : 0 < |x| := abs_pos.mpr hx
  have hw : ((ratEmptyLevel_weight x : ℝ≥0) : ℝ) = (ratEmptyLevel_const : ℝ) / 2 * |x|⁻¹ := by
    simp only [ratEmptyLevel_weight, hx, ite_false]
    exact Real.coe_toNNReal _ (by positivity)
  rw [hw, Real.sqrt_mul hd, ← Real.sqrt_eq_rpow, mul_assoc, ← Real.sqrt_mul (by positivity),
    inv_mul_cancel₀ hpos.ne', Real.sqrt_one, mul_one]

/-- The weighted theta function of a test, at the class of norm `|x|`. -/
private theorem ratEmptyLevel_theta_class (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))) (φ : ℝ → ℂ)
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) = φ (r∞ x)) (a : ℝ) {x : ℝ}
    (hx : x ≠ 0) :
    localTheta(ℚ, ∅, a, ω, f) (ratEmptyLevel_class x) =
      ((|x| ^ a : ℝ) : ℂ) * (((sLocalNormOneQuotientMeasure ℚ ∅).real univ : ℂ) *
        (φ x + φ (-x))) := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (ratEmptyLevel_class x)
  have hnorm : ((sIdeleQuotientNorm ℚ ∅ (QuotientGroup.mk u) : ℝ≥0) : ℝ) = |x| := by
    rw [hu]
    exact ratEmptyLevel_norm_class hx
  have habs : |r∞ u.val| = |x| := by
    rw [ratEmptyLevel_abs, ← hnorm]
    exact (ratEmptyLevel_norm u).symm
  rw [← hu]
  change ((((sIdeleQuotientNorm ℚ ∅ (QuotientGroup.mk u) : ℝ≥0) : ℝ) ^ a : ℝ) : ℂ) *
    sLocalHomogeneousAdelicThetaLinearMap ℚ ∅ ω f (QuotientGroup.mk u) = _
  rw [hnorm, ratEmptyLevel_homTheta, ratEmptyLevel_thetaClasses f φ hf u]
  rcases abs_eq_abs.mp habs with h | h
  · simp only [h]
  · simp only [h, neg_neg, add_comm]

private theorem ratEmptyLevel_const_mass_pos :
    0 < Real.sqrt ((ratEmptyLevel_const : ℝ) / 2) *
      (sLocalNormOneQuotientMeasure ℚ ∅).real univ := by
  have hd : (0 : ℝ) < ratEmptyLevel_const := NNReal.coe_pos.mpr ratEmptyLevel_const_pos
  exact mul_pos (Real.sqrt_pos.mpr (by positivity)) ratEmptyLevel_mass_pos

/-- The isometry carries the weighted theta vector at twist `1/2` of a test to a positive
multiple of the class of `x ↦ φ x + φ (-x)`. -/
private theorem ratEmptyLevel_isometry_theta
    (U : Lp ℂ 2 (localMeasure(ℚ, ∅, 0)) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hU : ∀ F, (U F : ℝ → ℂ) =ᵐ[volume] fun x ↦
      (Real.sqrt (ratEmptyLevel_weight x) : ℂ) * F (ratEmptyLevel_class x))
    (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker) (f : sAdelePolarSubspace ℚ ∅)
    (φ : ℝ → ℂ) (hf : ∀ x : SAdeleRing ℚ ∅, f.val (Multiplicative.ofAdd x) = φ (r∞ x)) :
    (U (sLocalPWThetaSobolevMap (F := ℚ) (S := ∅) (s := 0) (a := 1 / 2) (by norm_num) ω f) :
      ℝ → ℂ) =ᵐ[volume] fun x ↦
      ((Real.sqrt ((ratEmptyLevel_const : ℝ) / 2) *
        (sLocalNormOneQuotientMeasure ℚ ∅).real univ : ℝ) : ℂ) * (φ x + φ (-x)) := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  have h2 := sLocalPWThetaSobolevMap_apply (F := ℚ) (S := ∅) (s := 0) ha ω f
  have h2' : (sLocalPWThetaSobolevMap (F := ℚ) (S := ∅) (s := 0) ha ω f :
      SIdeleQuotient ℚ ∅ → ℂ) =ᵐ[localMeasure(ℚ, ∅, 0)] localTheta(ℚ, ∅, 1 / 2, ω, f.val) :=
    (withDensity_absolutelyContinuous _ _).ae_le h2
  have hac : (volume : Measure ℝ) ≪
      (volume : Measure ℝ).withDensity (fun x ↦ (ratEmptyLevel_weight x : ℝ≥0∞)) :=
    withDensity_absolutelyContinuous'
      ratEmptyLevel_measurable_weight.coe_nnreal_ennreal.aemeasurable
      (.of_forall fun x ↦ by simpa using (ratEmptyLevel_weight_pos x).ne')
  have h3 := hac.ae_le
    (ratEmptyLevel_measurePreserving_class.quasiMeasurePreserving.ae_eq_comp h2')
  have h0 : ∀ᵐ x : ℝ, x ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  filter_upwards [hU _, h3, h0] with x e1 e2 hx
  rw [e1]
  have e2' : (sLocalPWThetaSobolevMap (F := ℚ) (S := ∅) (s := 0) ha ω f :
      SIdeleQuotient ℚ ∅ → ℂ) (ratEmptyLevel_class x) =
      localTheta(ℚ, ∅, 1 / 2, ω, f.val) (ratEmptyLevel_class x) := e2
  rw [e2', ratEmptyLevel_theta_class ω f.val φ hf (1 / 2) hx,
    ← ratEmptyLevel_sqrt_weight_mul hx]
  push_cast
  ring

/-! ### The tests of the project and the polar-free core -/

private theorem ratEmptyLevel_region_iff (Y : ℝ) (x : SAdeleRing ℚ ∅) :
    x ∈ sLocalPWProductRegion (F := ℚ) ∅ Y ↔ ‖x.1 Rat.infinitePlace‖ ≤ Y := by
  simp [sLocalPWProductRegion]
  rw [Unique.eq_default Rat.infinitePlace]

/-- A test whose real Fourier transform is supported in `[-Y, Y]` has compact Fourier support in
the product region of size `Y`. -/
private theorem ratEmptyLevel_inBand (φ : SchwartzMap ℝ ℂ) {Y : ℝ}
    (hts : tsupport ⇑(FourierTransform.fourier φ : SchwartzMap ℝ ℂ) ⊆ Icc (-Y) Y)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) = φ (r∞ x)) :
    HasCompactSupport (sAdeleSchwartzFourier f).val ∧
      tsupport (sAdeleSchwartzFourier f).val ⊆
        Multiplicative.toAdd ⁻¹' sLocalPWProductRegion (F := ℚ) ∅ Y := by
  let r : Multiplicative (SAdeleRing ℚ ∅) → ℝ := fun y ↦
    InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
      ((Multiplicative.toAdd y).1 Rat.infinitePlace)
  have hr : Continuous r :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous.comp
      ((continuous_apply _).comp (continuous_fst.comp continuous_toAdd))
  have hsub : tsupport (sAdeleSchwartzFourier f).val ⊆
      r ⁻¹' tsupport ⇑(FourierTransform.fourier φ : SchwartzMap ℝ ℂ) := by
    refine closure_minimal (fun y hy ↦ ?_) ((isClosed_tsupport _).preimage hr)
    refine subset_tsupport _ ?_
    rw [mem_support] at hy ⊢
    rwa [← sAdeleSchwartzFourier_ratEmpty_apply φ f hf]
  have hsub' : tsupport (sAdeleSchwartzFourier f).val ⊆
      Multiplicative.toAdd ⁻¹' {x : SAdeleRing ℚ ∅ | ‖x.1 Rat.infinitePlace‖ ≤ Y} := by
    intro y hy
    have h := hts (hsub hy)
    change ‖(Multiplicative.toAdd y).1 Rat.infinitePlace‖ ≤ Y
    rw [← ratEmptyLevel_abs]
    exact abs_le.mpr h
  refine ⟨?_, fun y hy ↦ (ratEmptyLevel_region_iff Y _).mpr (hsub' hy)⟩
  refine (isCompact_sLocalPWBox (F := ℚ) (S := ∅) Y).of_isClosed_subset (isClosed_tsupport _)
    (fun y hy ↦ ⟨fun w ↦ ?_, fun v ↦ absurd v.2 (Finset.notMem_empty _)⟩)
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  rw [Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  exact hsub' hy

/-- Every real number is the real coordinate of an adele. -/
private theorem ratEmptyLevel_coord_surjective (ξ : ℝ) : ∃ y : SAdeleRing ℚ ∅, r∞ y = ξ := by
  by_cases hξ : ξ = 0
  · exact ⟨0, by rw [hξ]; exact map_zero _⟩
  · obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (ratEmptyLevel_class ξ)
    have hnorm : ((sIdeleQuotientNorm ℚ ∅ (QuotientGroup.mk u) : ℝ≥0) : ℝ) = |ξ| := by
      rw [hu]
      exact ratEmptyLevel_norm_class hξ
    have habs : |r∞ u.val| = |ξ| := by
      rw [ratEmptyLevel_abs, ← hnorm]
      exact (ratEmptyLevel_norm u).symm
    rcases abs_eq_abs.mp habs with h | h
    · exact ⟨u.val, h⟩
    · refine ⟨-u.val, ?_⟩
      change InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (-(u.val.1 Rat.infinitePlace)) = ξ
      rw [map_neg]
      change -(r∞ u.val) = ξ
      rw [h, neg_neg]

/-- The reflection of a Schwartz function. -/
private def ratEmptyLevel_reflect (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) φ

private theorem ratEmptyLevel_reflect_apply (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ratEmptyLevel_reflect φ x = φ (-x) := rfl

private theorem ratEmptyLevel_fourier_reflect (φ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (ratEmptyLevel_reflect φ : ℝ → ℂ) ξ = 𝓕 (φ : ℝ → ℂ) (-ξ) := by
  have h : (ratEmptyLevel_reflect φ : ℝ → ℂ) = fun x ↦ φ (-x) := rfl
  rw [h, ← Real.fourierInv_eq_fourier_comp_neg, Real.fourierInv_eq_fourier_neg]

private theorem ratEmptyLevel_fourier_zero (φ : 𝓢(ℝ, ℂ)) : 𝓕 (φ : ℝ → ℂ) 0 = ∫ x, φ x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp

/-- The even part `x ↦ (φ x + φ (-x)) / 2` of a polar-free test of the band is in the polar-free
core. -/
private theorem ratEmptyLevel_evenPart_mem_core {Y : ℝ} (φ : 𝓢(ℝ, ℂ)) (h0 : φ 0 = 0)
    (hF0 : 𝓕 (φ : ℝ → ℂ) 0 = 0) (hsupp : ∀ ξ, 𝓕 (φ : ℝ → ℂ) ξ ≠ 0 → ξ ∈ Icc (-Y) Y) :
    (((1 / 2 : ℂ) • (φ + ratEmptyLevel_reflect φ)).toLp 2 volume : Lp ℂ 2 (volume : Measure ℝ)) ∈
      realPWPolarFreeCore Y := by
  refine ⟨(1 / 2 : ℂ) • (φ + ratEmptyLevel_reflect φ), rfl, fun x ↦ ?_, ?_, ?_, ?_⟩
  · simp only [smul_apply, add_apply, ratEmptyLevel_reflect_apply,
      neg_neg]
    rw [add_comm]
  · refine closure_minimal (fun ξ hξ ↦ ?_) isClosed_Icc
    rw [mem_support] at hξ
    have hF : 𝓕 (((1 / 2 : ℂ) • (φ + ratEmptyLevel_reflect φ) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ =
        (1 / 2 : ℂ) * (𝓕 (φ : ℝ → ℂ) ξ + 𝓕 (φ : ℝ → ℂ) (-ξ)) := by
      rw [← SchwartzMap.fourier_coe, FourierSMul.fourier_smul, FourierAdd.fourier_add]
      simp only [smul_apply, add_apply, smul_eq_mul,
        SchwartzMap.fourier_coe, ratEmptyLevel_fourier_reflect]
    rw [hF] at hξ
    by_contra hmem
    have h1 : 𝓕 (φ : ℝ → ℂ) ξ = 0 := by
      by_contra h
      exact hmem (hsupp ξ h)
    have h2 : 𝓕 (φ : ℝ → ℂ) (-ξ) = 0 := by
      by_contra h
      have := hsupp (-ξ) h
      exact hmem ⟨by linarith [this.2], by linarith [this.1]⟩
    exact hξ (by rw [h1, h2]; simp)
  · simp [ratEmptyLevel_reflect_apply, h0]
  · have hi : ∫ x, φ x = 0 := by rw [← ratEmptyLevel_fourier_zero, hF0]
    have hr : ∫ x, ratEmptyLevel_reflect φ x = 0 := by
      have := integral_neg_eq_self (fun x ↦ φ x) (volume : Measure ℝ)
      simp only [ratEmptyLevel_reflect_apply]
      rw [this, hi]
    simp only [smul_apply, add_apply, smul_eq_mul]
    rw [integral_const_mul, integral_add φ.integrable (ratEmptyLevel_reflect φ).integrable, hi, hr]
    simp

local notation "thetaVector(" ω ", " f ")" =>
  sLocalPWThetaSobolevMap (F := ℚ) (S := ∅) (s := 0) (a := 1 / 2) (by norm_num) ω f

/-- The image of a weighted theta vector of the level is in the span of the polar-free core. -/
private theorem ratEmptyLevel_isometry_theta_mem_span
    (U : Lp ℂ 2 (localMeasure(ℚ, ∅, 0)) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hU : ∀ F, (U F : ℝ → ℂ) =ᵐ[volume] fun x ↦
      (Real.sqrt (ratEmptyLevel_weight x) : ℂ) * F (ratEmptyLevel_class x))
    (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker) {Y : ℝ} (f : sAdelePolarSubspace ℚ ∅)
    (hfb : f.val ∈ sLocalPWTests (F := ℚ) (S := ∅) (T := ∅) le_rfl
      (sLocalPWProductRegion (F := ℚ) ∅ Y)) :
    U (thetaVector(ω, f)) ∈ Submodule.span ℂ (realPWPolarFreeCore Y) := by
  obtain ⟨E, hE⟩ := ratTrivialHomogeneousTheta_quotient_realEquiv
  set φ : 𝓢(ℝ, ℂ) := E.symm f.val with hφ
  have hf : ∀ x : SAdeleRing ℚ ∅, f.val (Multiplicative.ofAdd x) = φ (r∞ x) := fun x ↦ by
    rw [← hE φ x, hφ, ContinuousLinearEquiv.apply_symm_apply]
  have hpol := (mem_sAdelePolarSubspace f.val).mp f.property
  have hr0 : InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
      ((0 : SAdeleRing ℚ ∅).1 Rat.infinitePlace) = 0 := map_zero _
  have h0 : φ 0 = 0 := by
    have h := hpol.1
    rw [hf] at h
    simpa only [hr0] using h
  have hF0 : 𝓕 (φ : ℝ → ℂ) 0 = 0 := by
    have h := hpol.2
    rw [sAdeleSchwartzFourier_ratEmpty_apply φ f.val hf] at h
    rw [← SchwartzMap.fourier_coe]
    simpa only [hr0] using h
  obtain ⟨g, hg, -, hgs⟩ := (mem_sLocalPWTests le_rfl _ f.val).mp hfb
  rw [ratEmptyLevel_transition] at hg
  subst hg
  have hsupp : ∀ ξ, 𝓕 (φ : ℝ → ℂ) ξ ≠ 0 → ξ ∈ Icc (-Y) Y := by
    intro ξ hξ
    obtain ⟨y, hy⟩ := ratEmptyLevel_coord_surjective ξ
    have hne : (sAdeleSchwartzFourier f.val).val (Multiplicative.ofAdd y) ≠ 0 := by
      have h := sAdeleSchwartzFourier_ratEmpty_apply φ f.val hf y
      rw [← SchwartzMap.fourier_coe] at hξ
      intro hz
      apply hξ
      rw [← hy]
      exact h.symm.trans hz
    have hmem := hgs (subset_tsupport _ (mem_support.mpr hne))
    have hle := (ratEmptyLevel_region_iff Y y).mp hmem
    rw [← ratEmptyLevel_abs] at hle
    rw [← hy]
    exact abs_le.mp hle
  have hcore := ratEmptyLevel_evenPart_mem_core φ h0 hF0 hsupp
  have heq : U (thetaVector(ω, f)) =
      ((2 * (Real.sqrt ((ratEmptyLevel_const : ℝ) / 2) *
        (sLocalNormOneQuotientMeasure ℚ ∅).real univ) : ℝ) : ℂ) •
      (((1 / 2 : ℂ) • (φ + ratEmptyLevel_reflect φ)).toLp 2 volume :
        Lp ℂ 2 (volume : Measure ℝ)) := by
    refine Lp.ext ?_
    filter_upwards [ratEmptyLevel_isometry_theta U hU ω f φ hf,
      Lp.coeFn_smul ((2 * (Real.sqrt ((ratEmptyLevel_const : ℝ) / 2) *
        (sLocalNormOneQuotientMeasure ℚ ∅).real univ) : ℝ) : ℂ)
        (((1 / 2 : ℂ) • (φ + ratEmptyLevel_reflect φ)).toLp 2 volume :
          Lp ℂ 2 (volume : Measure ℝ)),
      ((1 / 2 : ℂ) • (φ + ratEmptyLevel_reflect φ)).coeFn_toLp 2 volume] with x e1 e2 e3
    rw [e1, e2, Pi.smul_apply, e3]
    simp only [smul_apply, add_apply, ratEmptyLevel_reflect_apply, smul_eq_mul]
    push_cast
    ring
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hcore)

/-- A vector of the polar-free core is a multiple of the image of a weighted theta vector of the
level. -/
private theorem ratEmptyLevel_core_mem_span
    (U : Lp ℂ 2 (localMeasure(ℚ, ∅, 0)) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hU : ∀ F, (U F : ℝ → ℂ) =ᵐ[volume] fun x ↦
      (Real.sqrt (ratEmptyLevel_weight x) : ℂ) * F (ratEmptyLevel_class x))
    (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker) {Y : ℝ}
    (F : Lp ℂ 2 (volume : Measure ℝ)) (hF : F ∈ realPWPolarFreeCore Y) :
    ∃ f : sAdelePolarSubspace ℚ ∅, f.val ∈ sLocalPWTests (F := ℚ) (S := ∅) (T := ∅) le_rfl
      (sLocalPWProductRegion (F := ℚ) ∅ Y) ∧ ∃ c : ℂ, F = c • U (thetaVector(ω, f)) := by
  obtain ⟨h, rfl, heven, hsupp, h0, hint⟩ := hF
  obtain ⟨E, hE⟩ := ratTrivialHomogeneousTheta_quotient_realEquiv
  have hf := hE h
  have hF0 : (𝓕 h : 𝓢(ℝ, ℂ)) 0 = 0 := by
    rw [SchwartzMap.fourier_coe, ratEmptyLevel_fourier_zero, hint]
  have hpol : E h ∈ sAdelePolarSubspace ℚ ∅ := by
    have hp := ratEmptyLevel_polar h h0 hF0 (E h) hf
    rwa [ratEmptyLevel_transition] at hp
  have hts : tsupport ⇑(𝓕 h : 𝓢(ℝ, ℂ)) ⊆ Icc (-Y) Y := by
    rw [SchwartzMap.fourier_coe]
    exact hsupp
  have hband : E h ∈ sLocalPWTests (F := ℚ) (S := ∅) (T := ∅) le_rfl
      (sLocalPWProductRegion (F := ℚ) ∅ Y) :=
    (mem_sLocalPWTests le_rfl _ _).mpr
      ⟨E h, ratEmptyLevel_transition _, ratEmptyLevel_inBand h hts (E h) hf⟩
  have hc := ratEmptyLevel_const_mass_pos
  refine ⟨⟨E h, hpol⟩, hband, (((2 * (Real.sqrt ((ratEmptyLevel_const : ℝ) / 2) *
    (sLocalNormOneQuotientMeasure ℚ ∅).real univ))⁻¹ : ℝ) : ℂ), Lp.ext ?_⟩
  filter_upwards [ratEmptyLevel_isometry_theta U hU ω ⟨E h, hpol⟩ h hf,
    Lp.coeFn_smul (((2 * (Real.sqrt ((ratEmptyLevel_const : ℝ) / 2) *
      (sLocalNormOneQuotientMeasure ℚ ∅).real univ))⁻¹ : ℝ) : ℂ)
      (U (thetaVector(ω, (⟨E h, hpol⟩ : sAdelePolarSubspace ℚ ∅)))),
    h.coeFn_toLp 2 volume] with x e1 e2 e3
  rw [e3, e2, Pi.smul_apply, e1, heven x, smul_eq_mul]
  have hne : ((Real.sqrt ((ratEmptyLevel_const : ℝ) / 2) *
      (sLocalNormOneQuotientMeasure ℚ ∅).real univ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hc.ne'
  generalize (Real.sqrt ((ratEmptyLevel_const : ℝ) / 2) *
    (sLocalNormOneQuotientMeasure ℚ ∅).real univ) = c at hne ⊢
  push_cast
  field_simp
  ring

/-! ### The level -/

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), p. 488. **Over `ℚ` with no finite place, at
order zero and twist `1/2`, the invariant level of the project is the real Paley–Wiener level.**
There is a linear isometry `U` from the weighted space `L²` of the quotient `(ℚ ⊗ ℝ)ˣ / {±1}`
into `L²(ℝ)`, given by `(U F) (x) = c |x|^(-1/2) F (κ x)` with `κ x` the class of norm `|x|`,
that carries `sLocalInvariantPWSobolev` with parameter `Y` onto `realPWLevel Y`.
Reconstruction: the paper does not state this. It identifies the object of Definition 11.2.1.3
in the simplest case with the model of `Sec4_RealPWLevelClosure` and `Sec4_RealPWLevelOperator`.
Under `U` the translation of `F` by a class of norm `t` becomes the dilation
`f ↦ t^(-1/2) f (· / t)`, and the restriction to classes of norm at most `L` becomes the
restriction to `[-L, L]`. -/
theorem exists_linearIsometry_map_sLocalInvariantPWSobolev_rat
    (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker) {Y : ℝ} (hY : 0 < Y) :
    ∃ (U : Lp ℂ 2 (localMeasure(ℚ, ∅, 0)) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ))
      (κ : ℝ → SIdeleQuotient ℚ ∅) (c : ℝ), 0 < c ∧
      (∀ x : ℝ, x ≠ 0 → ((sIdeleQuotientNorm ℚ ∅ (κ x) : ℝ≥0) : ℝ) = |x|) ∧
      (∀ F, (U F : ℝ → ℂ) =ᵐ[volume] fun x ↦
        ((c * |x| ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * F (κ x)) ∧
      (sLocalInvariantPWSobolev (F := ℚ) (S := ∅) (s := 0) le_rfl (a := 1 / 2) (by norm_num)
        ω Y).map U.toLinearMap = realPWLevel Y := by
  obtain ⟨U, hU⟩ := ratEmptyLevel_exists_isometry
  have hd : (0 : ℝ) < ratEmptyLevel_const := NNReal.coe_pos.mpr ratEmptyLevel_const_pos
  have h0 : ∀ᵐ x : ℝ, x ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  refine ⟨U, ratEmptyLevel_class, Real.sqrt ((ratEmptyLevel_const : ℝ) / 2),
    Real.sqrt_pos.mpr (by positivity), fun x hx ↦ ratEmptyLevel_norm_class hx, fun F ↦ ?_, ?_⟩
  · filter_upwards [hU F, h0] with x e hx
    have hpos : 0 < |x| := abs_pos.mpr hx
    have hw : Real.sqrt (ratEmptyLevel_weight x) =
        Real.sqrt ((ratEmptyLevel_const : ℝ) / 2) * |x| ^ (-(1 / 2) : ℝ) := by
      rw [← ratEmptyLevel_sqrt_weight_mul hx, mul_assoc, ← Real.rpow_add hpos]
      norm_num
    rw [e, hw]
  · have hcl : ∀ S : Submodule ℂ (Lp ℂ 2 (localMeasure(ℚ, ∅, 0))),
        S.topologicalClosure.map U.toLinearMap = (S.map U.toLinearMap).topologicalClosure := by
      intro S
      refine SetLike.coe_injective ?_
      simp only [Submodule.map_coe, Submodule.topologicalClosure_coe,
        LinearIsometry.coe_toLinearMap]
      exact (U.isometry.isClosedEmbedding.closure_image_eq _).symm
    rw [sLocalInvariantPWSobolev, hcl, Submodule.map_span,
      ← topologicalClosure_span_realPWPolarFreeCore hY]
    congr 1
    refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
    · rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
      exact ratEmptyLevel_isometry_theta_mem_span U hU ω f.val f.property
    · intro F hF
      obtain ⟨f, hfb, c, rfl⟩ := ratEmptyLevel_core_mem_span U hU ω F hF
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨⟨f, hfb⟩, rfl⟩, rfl⟩)

end RiemannMasullo
