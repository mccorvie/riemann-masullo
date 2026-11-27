module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Count
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Absolute orbit unfolding for the S-local trace kernel -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "Hₛ" => sProjectedDiagonal F S
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S

local instance (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
local instance (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
local instance : MeasurableSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
local instance : MeasurableSpace Aₛ :=
  inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
local instance : MeasurableSpace Jₛ := borel _

local instance : T2Space Iₛ := (sIdeleGroup_description F S).2.1
local instance : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
local instance : BorelSpace Iₛ := sIdeleGroup_borelSpace

local instance : SecondCountableTopology Iₛ := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  exact (sIdeleGroup_description F S).1.secondCountableTopology

local instance : (μₛ).IsHaarMeasure := sMultiplicativeTamagawaMeasure_isHaarMeasure
local instance : (μₛ).Regular := sMultiplicativeTamagawaMeasure_regular
local instance : DiscreteTopology Hₛ := discreteTopology_sProjectedDiagonal
local instance : Countable Hₛ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
local instance : (Measure.count : Measure Hₛ).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
local instance : (Measure.count : Measure Hₛ).Regular := count_regular_of_discreteTopology

/-- An auxiliary form of Weil unfolding for the quotient kernel in
Theorem 12.4.1.1, Steps II–III, pp. 516–518. A quotient function given by a
nonnegative orbit sum is measurable and has the same total mass as the
integrand on the S-ideles. -/
theorem sLocalQuotient_lintegral_orbitSum
    (a : Iₛ → ℝ≥0∞) (ha : Measurable a) (A : Jₛ → ℝ≥0∞)
    (horbit : ∀ y : Iₛ, A (QuotientGroup.mk y) = ∑' ξ : Hₛ, a (ξ.val * y)) :
    Measurable A ∧ (∫⁻ q, A q ∂μJ) = ∫⁻ y, a y ∂μₛ := by
  let tr (q : Jₛ) (ξ : Hₛ) : Iₛ := q.out * ξ.val
  let κ (q : Jₛ) : Measure Iₛ := Measure.count.map (tr q)
  have hκ : Measurable κ ∧ (μJ).bind κ = μₛ :=
    weilMeasure_eq_bind Hₛ isClosed_sProjectedDiagonal μₛ Measure.count μJ
      sLocalQuotientTamagawaMeasure_isWeil
  have htr (q : Jₛ) : Measurable (tr q) :=
    (continuous_const.mul continuous_subtype_val).measurable
  have hA (q : Jₛ) : (∫⁻ y, a y ∂κ q) = A q := by
    rw [show κ q = Measure.count.map (tr q) from rfl, lintegral_map ha (htr q), lintegral_count]
    calc
      _ = ∑' ξ : Hₛ, a (ξ.val * q.out) := tsum_congr fun ξ ↦ by
        dsimp only [tr]
        rw [mul_comm]
      _ = A (QuotientGroup.mk q.out) := (horbit q.out).symm
      _ = A q := congrArg A (QuotientGroup.out_eq' q)
  have hmeas : Measurable (fun q : Jₛ ↦ ∫⁻ y, a y ∂κ q) :=
    (Measure.measurable_lintegral ha).comp hκ.1
  rw [funext hA] at hmeas
  refine ⟨hmeas, ?_⟩
  rw [← hκ.2, Measure.lintegral_bind hκ.1.aemeasurable ha.aemeasurable]
  exact lintegral_congr fun q ↦ (hA q).symm

/-- Finite absolute quotient mass guarantees integrability on the S-ideles.
The complex orbit sum then gives the same integral against quotient Haar measure. -/
theorem sLocalQuotient_integral_orbitSum_of_absolute
    (g : Iₛ → ℂ) (hg : Measurable g) (A : Jₛ → ℝ≥0∞) (G : Jₛ → ℂ)
    (hA : ∀ y : Iₛ, A (QuotientGroup.mk y) = ∑' ξ : Hₛ, ‖g (ξ.val * y)‖ₑ)
    (hG : ∀ y : Iₛ, G (QuotientGroup.mk y) = ∑' ξ : Hₛ, g (ξ.val * y))
    (hfin : (∫⁻ q, A q ∂μJ) < ⊤) :
    Integrable g μₛ ∧ Integrable G μJ ∧ (∫ y, g y ∂μₛ) = ∫ q, G q ∂μJ := by
  have hAbs := (sLocalQuotient_lintegral_orbitSum (fun y ↦ ‖g y‖ₑ) hg.eNorm A hA).2
  have hInt : Integrable g μₛ := by
    refine ⟨hg.aestronglyMeasurable, hasFiniteIntegral_iff_eNorm.mpr ?_⟩
    rw [← hAbs]
    exact hfin
  have h := weilQuotientIntegral_L1 Hₛ isClosed_sProjectedDiagonal μₛ Measure.count μJ
    sLocalQuotientTamagawaMeasure_isWeil hInt
  have hCon : lcaCosetIntegral Hₛ Measure.count g =ᵐ[μJ] G := by
    filter_upwards [h.1] with q hq
    calc
      lcaCosetIntegral Hₛ Measure.count g q = ∑' ξ : Hₛ, g (q.out * ξ.val) := by
        simpa only [lcaCosetIntegral, count_real_singleton, one_smul] using integral_countable hq
      _ = ∑' ξ : Hₛ, g (ξ.val * q.out) := tsum_congr fun ξ ↦ by rw [mul_comm]
      _ = G (QuotientGroup.mk q.out) := (hG q.out).symm
      _ = G q := congrArg G (QuotientGroup.out_eq' q)
  exact ⟨hInt, h.2.1.congr hCon, h.2.2.trans (integral_congr_ae hCon)⟩

/-- The absolute half-density of a Schwartz–Bruhat test is integrable on
the S-ideles. This auxiliary bound uses the positive zeta integral at
twist one half for the orbit sums in Theorem 12.4.1.1, pp. 516–518. -/
theorem sLocalSchwartzBruhat_norm_sqrt_integrable
    (f : SchwartzBruhat (Multiplicative Aₛ)) :
    Integrable (fun y : Iₛ ↦ Real.sqrt ((sIdeleNorm F S y).val : ℝ) *
      ‖f (Multiplicative.ofAdd y.val)‖) μₛ := by
  let circleToComplex : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  let c := quasiCharacterNormTwist (sIdeleQuotientNorm F S)
    (isProperMap_sIdeleQuotientNorm F S).continuous
    (circleToComplex.comp (1 : PontryaginDual Jₛ)) (1 / 2)
  have h := sLocalIdelicZetaIntegral_integrable f c ⟨1, 1 / 2, by norm_num, rfl⟩
  refine h.norm.congr (ae_of_all _ fun y ↦ ?_)
  have hn : ‖c (QuotientGroup.mk y)‖ = Real.sqrt ((sIdeleNorm F S y).val : ℝ) := by
    change ‖((1 : PontryaginDual Jₛ) (QuotientGroup.mk y) : ℂ) *
      (((sIdeleQuotientNorm F S (QuotientGroup.mk y)).val : ℝ) : ℂ) ^ (1 / 2 : ℂ)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, sIdeleQuotientNorm_mk,
      Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)),
      Real.sqrt_eq_rpow]
    norm_num
  change ‖f (Multiplicative.ofAdd y.val) * c (QuotientGroup.mk y)‖ = _
  rw [norm_mul, hn, mul_comm]

private theorem mul_orbitBound_le_sqrt {t A C : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (hsmall : t ≤ 1 → A ≤ C * t ^ (-(1 / 4 : ℝ)))
    (hlarge : 1 ≤ t → A ≤ C * t⁻¹) : t * A ≤ C * Real.sqrt t := by
  rw [Real.sqrt_eq_rpow]
  rcases le_total t 1 with hs | hl
  · calc
      t * A ≤ t * (C * t ^ (-(1 / 4 : ℝ))) := mul_le_mul_of_nonneg_left (hsmall hs) ht.le
      _ = C * (t ^ (1 : ℝ) * t ^ (-(1 / 4 : ℝ))) := by rw [Real.rpow_one]; ring
      _ = C * t ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add ht]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge ht hs (by norm_num)) hC
  · calc
      t * A ≤ t * (C * t⁻¹) := mul_le_mul_of_nonneg_left (hlarge hl) ht.le
      _ = C * t ^ (0 : ℝ) := by rw [Real.rpow_zero, mul_left_comm, mul_inv_cancel₀ ht.ne', mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hl (by norm_num)) hC

/-- An auxiliary absolute convergence estimate for the kernel action in
Theorem 12.4.1.1, Steps II–III, pp. 516–518. The two radial bounds on a
kernel's absolute input-orbit sum dominate its product with the absolute
theta series after conversion to multiplicative Haar measure. A constant
measure factor can be included in the kernel bound. -/
theorem sLocalQuotient_lintegral_radial_mul_absTheta_lt_top
    (f : SchwartzBruhat (Multiplicative Aₛ)) (A : Jₛ → ℝ≥0∞)
    (hA : ∀ y : Iₛ, A (QuotientGroup.mk y) =
      ∑' ξ : Hₛ, ‖f (Multiplicative.ofAdd (ξ.val * y).val)‖ₑ)
    (k : Jₛ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ q : Jₛ, ((sIdeleQuotientNorm F S q).val : ℝ) ≤ 1 →
      k q ≤ C * ((sIdeleQuotientNorm F S q).val : ℝ) ^ (-(1 / 4 : ℝ)))
    (hlarge : ∀ q : Jₛ, 1 ≤ ((sIdeleQuotientNorm F S q).val : ℝ) →
      k q ≤ C * ((sIdeleQuotientNorm F S q).val : ℝ)⁻¹) :
    (∫⁻ q, ENNReal.ofReal (((sIdeleQuotientNorm F S q).val : ℝ) * k q) * A q ∂μJ) < ⊤ := by
  let N (q : Jₛ) : ℝ := (sIdeleQuotientNorm F S q).val
  let n (y : Iₛ) : ℝ := (sIdeleNorm F S y).val
  let V (q : Jₛ) := ENNReal.ofReal (Real.sqrt (N q)) * A q
  let v (y : Iₛ) := Real.sqrt (n y) * ‖f (Multiplicative.ofAdd y.val)‖
  let a (y : Iₛ) := ENNReal.ofReal (v y)
  have hNmk (y : Iₛ) : N (QuotientGroup.mk y) = n y := by
    simp only [N, n, sIdeleQuotientNorm_mk]
  have hN : Continuous N := NNReal.continuous_coe.comp (Units.continuous_val.comp
    (isProperMap_sIdeleQuotientNorm F S).continuous)
  have hm : Continuous (QuotientGroup.mk : Iₛ → Jₛ) := continuous_quotient_mk'
  have hn : Continuous n := (hN.comp hm).congr hNmk
  have hf : Continuous (fun y : Iₛ ↦ f (Multiplicative.ofAdd y.val)) :=
    (continuous_schwartzBruhat_apply f).comp (continuous_ofAdd.comp Units.continuous_val)
  have ha : Measurable a :=
    ((Real.continuous_sqrt.comp hn).mul hf.norm).measurable.ennreal_ofReal
  have hform (y : Iₛ) :
      a y = ENNReal.ofReal (Real.sqrt (n y)) * ‖f (Multiplicative.ofAdd y.val)‖ₑ := by
    simp only [a, v, ENNReal.ofReal_mul (Real.sqrt_nonneg _), ofReal_norm]
  have hV (y : Iₛ) : V (QuotientGroup.mk y) = ∑' ξ : Hₛ, a (ξ.val * y) := by
    dsimp only [V]
    rw [hA, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro ξ
    have hclass : (QuotientGroup.mk (ξ.val * y) : Jₛ) = QuotientGroup.mk y := by
      rw [mul_comm, QuotientGroup.mk_mul_of_mem y ξ.property]
    rw [hform, ← hNmk, hclass]
  have hmass := sLocalQuotient_lintegral_orbitSum a ha V hV
  have hv : Integrable v μₛ := sLocalSchwartzBruhat_norm_sqrt_integrable f
  have hnv (y : Iₛ) : ‖v y‖ₑ = a y :=
    Real.eNorm_eq_ofReal (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  have hfinA : (∫⁻ y, a y ∂μₛ) < ⊤ := by
    have h := hasFiniteIntegral_iff_eNorm.mp hv.hasFiniteIntegral
    simpa only [hnv] using h
  have hfinV : (∫⁻ q, V q ∂μJ) < ⊤ := hmass.2 ▸ hfinA
  calc
    _ ≤ ∫⁻ q, ENNReal.ofReal C * V q ∂μJ := by
      apply lintegral_mono
      intro q
      change ENNReal.ofReal (N q * k q) * A q ≤
        ENNReal.ofReal C * (ENNReal.ofReal (Real.sqrt (N q)) * A q)
      rw [← mul_assoc, ← ENNReal.ofReal_mul hC]
      have ht : 0 < N q := NNReal.coe_pos.mpr (Units.zero_lt (sIdeleQuotientNorm F S q))
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_orbitBound_le_sqrt ht hC (hsmall q) (hlarge q))) le_rfl
    _ = ENNReal.ofReal C * (∫⁻ q, V q ∂μJ) := lintegral_const_mul _ hmass.1
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinV

private theorem theta_projected_tsum (f : SchwartzBruhat (Multiplicative Aₛ)) (y : Iₛ) :
    sLocalAdelicThetaOnClasses F S f (QuotientGroup.mk y) =
      ∑' ξ : Hₛ, f (Multiplicative.ofAdd (ξ.val * y).val) := by
  let d := sUnitEmbedding F S
  have hd : Injective d := fun _ _ h ↦ Units.ext
    ((sAdele_additive_quotient F S).1 (congrArg Units.val h))
  have hr : d.range = Hₛ := by
    change _ = Subgroup.map _ _
    rw [MonoidHom.map_range]
  let e := (MonoidHom.ofInjective hd).toEquiv.trans (MulEquiv.subgroupCongr hr).toEquiv
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
  exact e.tsum_eq (fun ξ : Hₛ ↦ f (Multiplicative.ofAdd (ξ.val * y).val))

/-- A kernel row with the two radial bounds can be paired with the S-local theta
series by Weil unfolding. The input-radius factor is the one used to convert
additive to multiplicative measure in Theorem 12.4.1.1, pp. 516–518. -/
theorem sLocalQuotient_integral_radial_mul_theta
    (f : SchwartzBruhat (Multiplicative Aₛ)) (k : Jₛ → ℂ) (hk : Measurable k)
    {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ q : Jₛ, ((sIdeleQuotientNorm F S q).val : ℝ) ≤ 1 →
      ‖k q‖ ≤ C * ((sIdeleQuotientNorm F S q).val : ℝ) ^ (-(1 / 4 : ℝ)))
    (hlarge : ∀ q : Jₛ, 1 ≤ ((sIdeleQuotientNorm F S q).val : ℝ) →
      ‖k q‖ ≤ C * ((sIdeleQuotientNorm F S q).val : ℝ)⁻¹) :
    let N (q : Jₛ) : ℝ := (sIdeleQuotientNorm F S q).val
    let g (y : Iₛ) := (N (QuotientGroup.mk y) : ℂ) * k (QuotientGroup.mk y) *
      f (Multiplicative.ofAdd y.val)
    let G (q : Jₛ) := (N q : ℂ) * k q * sLocalAdelicThetaOnClasses F S f q
    Integrable g μₛ ∧ Integrable G μJ ∧ (∫ y, g y ∂μₛ) = ∫ q, G q ∂μJ := by
  intro N g G
  let A (q : Jₛ) : ℝ≥0∞ := ∑' ξ : Hₛ, ‖f (Multiplicative.ofAdd (ξ.val * q.out).val)‖ₑ
  have hA (y : Iₛ) : A (QuotientGroup.mk y) =
      ∑' ξ : Hₛ, ‖f (Multiplicative.ofAdd (ξ.val * y).val)‖ₑ := by
    let z := (QuotientGroup.mk y : Jₛ).out
    have hz : (QuotientGroup.mk z : Jₛ) = QuotientGroup.mk y := QuotientGroup.out_eq' _
    let η : Hₛ := ⟨z / y, QuotientGroup.eq_iff_div_mem.mp hz⟩
    have hη : η.val * y = z := div_mul_cancel _ _
    let a (ξ : Hₛ) := ‖f (Multiplicative.ofAdd (ξ.val * y).val)‖ₑ
    change (∑' ξ : Hₛ, ‖f (Multiplicative.ofAdd (ξ.val * z).val)‖ₑ) = ∑' ξ, a ξ
    calc
      _ = ∑' ξ : Hₛ, a (ξ * η) := tsum_congr fun ξ ↦ by
        simp only [a, Subgroup.coe_mul, mul_assoc, hη]
      _ = _ := (Equiv.mulRight η).tsum_eq a
  have hN : Continuous N := NNReal.continuous_coe.comp (Units.continuous_val.comp
    (isProperMap_sIdeleQuotientNorm F S).continuous)
  let : BorelSpace Jₛ := ⟨rfl⟩
  have hm : Continuous (QuotientGroup.mk : Iₛ → Jₛ) := continuous_quotient_mk'
  have hf : Continuous (fun y : Iₛ ↦ f (Multiplicative.ofAdd y.val)) :=
    (continuous_schwartzBruhat_apply f).comp (continuous_ofAdd.comp Units.continuous_val)
  have hg : Measurable g :=
    (((Complex.continuous_ofReal.comp (hN.comp hm)).measurable.mul
      (hk.comp hm.measurable)).mul hf.measurable)
  have hclass (y : Iₛ) (ξ : Hₛ) :
      (QuotientGroup.mk (ξ.val * y) : Jₛ) = QuotientGroup.mk y := by
    rw [mul_comm, QuotientGroup.mk_mul_of_mem y ξ.property]
  let absMass (q : Jₛ) := ENNReal.ofReal (N q * ‖k q‖) * A q
  have habs (y : Iₛ) : absMass (QuotientGroup.mk y) = ∑' ξ : Hₛ, ‖g (ξ.val * y)‖ₑ := by
    dsimp only [absMass]
    rw [hA, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro ξ
    have hN₀ : 0 ≤ N (QuotientGroup.mk y) := NNReal.coe_nonneg _
    simp only [g, hclass y ξ, ← ofReal_norm, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hN₀]
    rw [ENNReal.ofReal_mul (mul_nonneg hN₀ (norm_nonneg (k (QuotientGroup.mk y))))]
  have hG (y : Iₛ) : G (QuotientGroup.mk y) = ∑' ξ : Hₛ, g (ξ.val * y) := by
    dsimp only [G]
    rw [theta_projected_tsum, ← tsum_mul_left]
    exact tsum_congr fun ξ ↦ by simp only [g, hclass y ξ]
  have hfin : (∫⁻ q, absMass q ∂μJ) < ⊤ :=
    sLocalQuotient_lintegral_radial_mul_absTheta_lt_top f A hA
      (fun q ↦ ‖k q‖) hC hsmall hlarge
  exact sLocalQuotient_integral_orbitSum_of_absolute g hg absMass G habs hG hfin

/-- The multiplicative input form of the periodized kernel action.
The absolute radial bounds on a row justify interchanging the output orbit
sum with the integrals. Simultaneous S-unit covariance turns the output
translates into the input orbit defining the quotient kernel. -/
theorem sLocalQuotient_integral_outputOrbit_radial_theta
    (f : SchwartzBruhat (Multiplicative Aₛ)) (K : Iₛ → Iₛ → ℂ) (x : Iₛ)
    (hK : Measurable (K x))
    (hcov : ∀ (ξ : Hₛ) (y : Iₛ), K (ξ.val * x) (ξ.val * y) = K x y)
    (κ : Jₛ → ℂ) (hκ : Measurable κ)
    (hrep : ∀ y : Iₛ, κ (QuotientGroup.mk y) = ∑' ξ : Hₛ, K x (ξ.val * y))
    (hsum : ∀ y : Iₛ, Summable fun ξ : Hₛ ↦ ‖K x (ξ.val * y)‖)
    {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ y : Iₛ, ((sIdeleNorm F S y).val : ℝ) ≤ 1 →
      (∑' ξ : Hₛ, ‖K x (ξ.val * y)‖) ≤ C * ((sIdeleNorm F S y).val : ℝ) ^ (-(1 / 4 : ℝ)))
    (hlarge : ∀ y : Iₛ, 1 ≤ ((sIdeleNorm F S y).val : ℝ) →
      (∑' ξ : Hₛ, ‖K x (ξ.val * y)‖) ≤ C * ((sIdeleNorm F S y).val : ℝ)⁻¹) :
    let N (q : Jₛ) : ℝ := (sIdeleQuotientNorm F S q).val
    let v (y : Iₛ) := f (Multiplicative.ofAdd y.val)
    let G (q : Jₛ) := (N q : ℂ) * κ q * sLocalAdelicThetaOnClasses F S f q
    Integrable G μJ ∧
      (∑' ξ : Hₛ, ∫ y : Iₛ, (N (QuotientGroup.mk y) : ℂ) * K (ξ.val * x) y * v y ∂μₛ) =
        ∫ q, G q ∂μJ := by
  intro N v G
  let π : Iₛ → Jₛ := QuotientGroup.mk
  let h (y : Iₛ) := ∑' ξ : Hₛ, ‖K x (ξ.val * y)‖
  let T (ξ : Hₛ) (y : Iₛ) := (N (π y) : ℂ) * K x (ξ.val * y) * v y
  have hπn (y : Iₛ) : N (QuotientGroup.mk y) = ((sIdeleNorm F S y).val : ℝ) := by
    simp only [N, sIdeleQuotientNorm_mk]
  have hN₀ (y : Iₛ) : 0 ≤ N (π y) := NNReal.coe_nonneg _
  have hNc : Continuous N := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_sIdeleQuotientNorm F S).continuous)
  have hπc : Continuous π := continuous_quotient_mk'
  have hv : Continuous v :=
    (continuous_schwartzBruhat_apply f).comp (continuous_ofAdd.comp Units.continuous_val)
  let : BorelSpace Jₛ := ⟨rfl⟩
  have hT (ξ : Hₛ) : Measurable (T ξ) :=
    (((Complex.continuous_ofReal.comp (hNc.comp hπc)).measurable.mul
      (hK.comp (continuous_const (y := ξ.val) |>.mul continuous_id).measurable)).mul hv.measurable)
  have hmass (y : Iₛ) : (∑' ξ : Hₛ, ‖T ξ y‖ₑ) =
      ENNReal.ofReal (N (π y) * h y * ‖v y‖) := by
    have he (ξ : Hₛ) : ‖T ξ y‖ₑ = ENNReal.ofReal (N (π y) * ‖K x (ξ.val * y)‖ * ‖v y‖) := by
      rw [← ofReal_norm]
      simp only [T, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hN₀ y)]
    have nonneg (ξ : Hₛ) : 0 ≤ N (π y) * ‖K x (ξ.val * y)‖ * ‖v y‖ :=
      mul_nonneg (mul_nonneg (hN₀ y) (norm_nonneg _)) (norm_nonneg _)
    have hweighted := ((hsum y).mul_left (N (π y))).mul_right ‖v y‖
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg nonneg hweighted, tsum_mul_right, tsum_mul_left]
  let V (y : Iₛ) := C * Real.sqrt (N (π y)) * ‖v y‖
  have hV : Integrable V μₛ := by
    simpa only [V, π, hπn, v, mul_assoc] using (sLocalSchwartzBruhat_norm_sqrt_integrable f).const_mul C
  have hV₀ (y : Iₛ) : 0 ≤ V y :=
    mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) (norm_nonneg _)
  have hfin : (∑' ξ : Hₛ, ∫⁻ y, ‖T ξ y‖ₑ ∂μₛ) < ⊤ := by
    rw [← lintegral_tsum (fun ξ ↦ (hT ξ).eNorm.aemeasurable)]
    calc
      _ = ∫⁻ y, ENNReal.ofReal (N (π y) * h y * ‖v y‖) ∂μₛ := lintegral_congr hmass
      _ ≤ ∫⁻ y, ENNReal.ofReal (V y) ∂μₛ := by
        apply lintegral_mono
        intro y
        have hp : 0 < N (π y) := NNReal.coe_pos.mpr (Units.zero_lt _)
        have hs : N (π y) ≤ 1 → h y ≤ C * (N (π y)) ^ (-(1 / 4 : ℝ)) := by
          simpa only [h, π, hπn] using hsmall y
        have hl : 1 ≤ N (π y) → h y ≤ C * (N (π y))⁻¹ := by
          simpa only [h, π, hπn] using hlarge y
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (mul_orbitBound_le_sqrt hp hC hs hl) (norm_nonneg (v y)))
      _ = ENNReal.ofReal (∫ y, V y ∂μₛ) :=
        (ofReal_integral_eq_lintegral_ofReal hV (ae_of_all _ hV₀)).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hκNorm (y : Iₛ) : ‖κ (π y)‖ ≤ h y := by
    change ‖κ (QuotientGroup.mk y)‖ ≤ h y
    rw [hrep]
    exact norm_tsum_le_tsum_norm (hsum y)
  have hκsmall (q : Jₛ) (hq : N q ≤ 1) : ‖κ q‖ ≤ C * (N q) ^ (-(1 / 4 : ℝ)) := by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact (hκNorm y).trans (by simpa only [h, π, hπn] using hsmall y (by simpa only [hπn] using hq))
  have hκlarge (q : Jₛ) (hq : 1 ≤ N q) : ‖κ q‖ ≤ C * (N q)⁻¹ := by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact (hκNorm y).trans (by simpa only [h, π, hπn] using hlarge y (by simpa only [hπn] using hq))
  obtain ⟨_, hG, hWeil⟩ := sLocalQuotient_integral_radial_mul_theta f κ hκ hC hκsmall hκlarge
  refine ⟨hG, ?_⟩
  have hInv (ξ : Hₛ) (y : Iₛ) : K (ξ.val * x) y = K x ((ξ⁻¹).val * y) := by
    simpa only [Subgroup.coe_inv, mul_inv_cancel_left] using hcov ξ ((ξ⁻¹).val * y)
  have hpoint (y : Iₛ) : (∑' ξ : Hₛ, T ξ y) = (N (π y) : ℂ) * κ (π y) * v y := by
    dsimp only [T, π]
    rw [tsum_mul_right, tsum_mul_left, hrep]
  calc
    _ = ∑' ξ : Hₛ, ∫ y, T ξ⁻¹ y ∂μₛ := tsum_congr fun ξ ↦ by
      simp only [T, π, hInv]
    _ = ∑' ξ : Hₛ, ∫ y, T ξ y ∂μₛ :=
      (Equiv.inv Hₛ).tsum_eq (fun ξ : Hₛ ↦ ∫ y, T ξ y ∂μₛ)
    _ = ∫ y, ∑' ξ : Hₛ, T ξ y ∂μₛ :=
      (integral_tsum (fun ξ ↦ (hT ξ).aestronglyMeasurable) hfin.ne).symm
    _ = ∫ y, (N (π y) : ℂ) * κ (π y) * v y ∂μₛ := integral_congr_ae (ae_of_all _ hpoint)
    _ = ∫ q, G q ∂μJ := hWeil

end RiemannMasullo
