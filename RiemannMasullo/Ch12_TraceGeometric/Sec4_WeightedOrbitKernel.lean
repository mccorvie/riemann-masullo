module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Weighted product estimates for the S-local cutoff kernel

The norm-product decomposition of quotient Haar measure integrates the radial
tails after converting to the half-density kernel of the Hardy–Sobolev space.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "μJ" => sLocalQuotientTamagawaMeasure F S

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSIdeleQuotientT2Sec1
  instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1

local instance instSIdeleQuotientBorelWeightedOrbitKernel : BorelSpace Jₛ := ⟨rfl⟩

/-- Exponential decay in both directions of the log norm is integrable for
the S-local quotient Tamagawa measure. -/
private theorem integrable_sLocalQuotient_exp_neg_abs_logNorm {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : Jₛ ↦ Real.exp (-a * |Real.log ((sIdeleQuotientNorm F S y).val : ℝ)|))
      μJ := by
  let V (x : ℝ) := Real.exp (-a * |x|)
  have hIic : IntegrableOn V (Iic (0 : ℝ)) :=
    (integrableOn_exp_mul_Iic ha 0).congr_fun (fun x hx ↦ by
      change Real.exp (a * x) = Real.exp (-a * |x|)
      rw [abs_of_nonpos hx, neg_mul_neg]) measurableSet_Iic
  have hIoi : IntegrableOn V (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0).congr_fun (fun x hx ↦ by
      change Real.exp (-a * x) = Real.exp (-a * |x|)
      rw [abs_of_nonneg (le_of_lt hx)]) measurableSet_Ioi
  have hV : Integrable V := by
    simpa only [Iic_union_Ioi, integrableOn_univ] using hIic.union hIoi
  let : BorelSpace J₁ := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let e (x : ℝ) : ℝ≥0ˣ := Units.mk0 (Real.exp x).toNNReal
    (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))
  have he : Measurable e :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hev (x : ℝ) : ((e x).val : ℝ) = Real.exp x :=
    Real.coe_toNNReal _ (Real.exp_pos x).le
  have hVc : Continuous V := Real.continuous_exp.comp (continuous_const.mul continuous_abs)
  have hlog : Continuous (fun t : ℝ≥0ˣ ↦ Real.log (t.val : ℝ)) :=
    (NNReal.continuous_coe.comp Units.continuous_val).log
      (fun t ↦ (NNReal.coe_pos.mpr (Units.zero_lt t)).ne')
  have hpos : Integrable (fun t : ℝ≥0ˣ ↦ V (Real.log (t.val : ℝ))) positiveRealHaar := by
    change Integrable (fun t : ℝ≥0ˣ ↦ V (Real.log (t.val : ℝ))) (Measure.map e volume)
    rw [integrable_map_measure (g := fun t : ℝ≥0ˣ ↦ V (Real.log (t.val : ℝ)))
      (hVc.comp hlog).aestronglyMeasurable he.aemeasurable]
    exact hV.congr (ae_of_all _ fun x ↦ by
      change V x = V (Real.log ((e x).val : ℝ))
      rw [hev, Real.log_exp])
  let π := Units.map (adeleProjection F S).toMonoidHom
  have hπ : Continuous π := Continuous.units_map _ (continuous_adeleProjection F S)
  let τ : ℝ≥0ˣ →ₜ* Iₛ := ⟨π.comp (canonicalIdeleNormSection F),
    hπ.comp (canonicalIdeleNormSection_continuous F)⟩
  have hτ : RightInverse τ (sIdeleNorm F S) := sIdeleNorm_project_canonicalSection F S
  let P (p : J₁ × ℝ≥0ˣ) : Jₛ := (p.1 : Jₛ) * QuotientGroup.mk (τ p.2)
  have hquot : Continuous (QuotientGroup.mk : Iₛ → Jₛ) := continuous_quotient_mk'
  have hP : Continuous P := (continuous_subtype_val.comp continuous_fst).mul
    (hquot.comp (τ.continuous.comp continuous_snd))
  have hPN (p : J₁ × ℝ≥0ˣ) : sIdeleQuotientNorm F S (P p) = p.2 := by
    change sIdeleQuotientNorm F S ((p.1 : Jₛ) * QuotientGroup.mk (τ p.2)) = p.2
    rw [map_mul, MonoidHom.mem_ker.mp p.1.property, one_mul, sIdeleQuotientNorm_mk, hτ]
  let η := sLocalNormOneQuotientMeasure F S
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : η.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : IsFiniteMeasure η := CompactSpace.isFiniteMeasure
  have hmap : (η.prod positiveRealHaar).map P = μJ :=
    (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 τ hτ
  let f (y : Jₛ) := V (Real.log ((sIdeleQuotientNorm F S y).val : ℝ))
  have hfc : Continuous f := hVc.comp (hlog.comp (isProperMap_sIdeleQuotientNorm F S).continuous)
  change Integrable f μJ
  rw [← hmap, integrable_map_measure hfc.aestronglyMeasurable hP.measurable.aemeasurable]
  change Integrable (fun p : J₁ × ℝ≥0ˣ ↦ V (Real.log ((sIdeleQuotientNorm F S (P p)).val : ℝ)))
    (η.prod positiveRealHaar)
  simp_rw [hPN]
  exact hpos.comp_snd η

/-- A squared-kernel estimate after absorbing the input density gives a
weighted product `L²` kernel. The output weight stays in the output measure,
where compact support gives finite mass. -/
private theorem sLocalQuotient_memLp_weighted_kernel_of_exp_logNorm_bound
    {w : Jₛ → ℝ≥0} (hw : Continuous w) {Z : Set Jₛ} (hZ : IsCompact Z)
    {K : Jₛ × Jₛ → ℂ} (hK : Measurable K) {a C : ℝ} (ha : 0 < a)
    (hbound : ∀ p : Jₛ × Jₛ, (w p.2 : ℝ) * ‖K p‖ ^ 2 ≤
      C * Z.indicator (fun _ : Jₛ ↦ (1 : ℝ)) p.1 *
        Real.exp (-a * |Real.log ((sIdeleQuotientNorm F S p.2).val : ℝ)|)) :
    let ν := (μJ).withDensity (fun y ↦ (w y : ℝ≥0∞))
    MemLp K 2 (ν.prod ν) := by
  intro ν
  let : (μJ).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1
  let : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_coe hw
  let out : Jₛ → ℝ := Z.indicator (fun _ ↦ 1)
  let rad (y : Jₛ) := Real.exp (-a * |Real.log ((sIdeleQuotientNorm F S y).val : ℝ)|)
  have hout : Integrable out ν :=
    (integrable_indicator_iff hZ.measurableSet).mpr (integrableOn_const hZ.measure_ne_top)
  have hrad : Integrable rad μJ := integrable_sLocalQuotient_exp_neg_abs_logNorm ha
  have hmaj : Integrable (fun p : Jₛ × Jₛ ↦ C * (out p.1 * rad p.2)) (ν.prod μJ) :=
    (hout.mul_prod hrad).const_mul C
  have hwm : Measurable (fun p : Jₛ × Jₛ ↦ w p.2) := hw.measurable.comp measurable_snd
  have hm : Measurable (fun p : Jₛ × Jₛ ↦ (w p.2 : ℝ) * ‖K p‖ ^ 2) :=
    (NNReal.continuous_coe.measurable.comp hwm).mul (hK.norm.pow_const 2)
  have hsq : Integrable (fun p : Jₛ × Jₛ ↦ (w p.2 : ℝ) * ‖K p‖ ^ 2) (ν.prod μJ) :=
    hmaj.mono_nonneg hm.aestronglyMeasurable
      (ae_of_all _ fun p ↦ mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _))
      (ae_of_all _ fun p ↦ by simpa only [out, rad, mul_assoc] using hbound p)
  have hdens : Measurable (fun y : Jₛ ↦ (w y : ℝ≥0∞)) :=
    ENNReal.continuous_coe.measurable.comp hw.measurable
  have hprod : ν.prod ν = (ν.prod μJ).withDensity (fun p : Jₛ × Jₛ ↦ (w p.2 : ℝ≥0∞)) :=
    prod_withDensity_right (μ := ν) (ν := μJ) hdens
  apply (memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable).mpr
  rw [hprod]
  exact (integrable_withDensity_iff_integrable_smul hwm).mpr
    (by simpa only [NNReal.smul_def, smul_eq_mul] using hsq)

/-- The input half-density turns the two radial size estimates into one
integrable majorant for the squared kernel. -/
private theorem cutoffRadialSquareMajorant_bound {t u C : ℝ} (ht : 0 < t) (hu : 0 ≤ u)
    (hsmall : t ≤ 1 → u ≤ C * t ^ (-(1 / 4 : ℝ)))
    (hlarge : 1 ≤ t → u ≤ C * t⁻¹) :
    t * u ^ 2 ≤ C ^ 2 * Real.exp (-|Real.log t| / 2) := by
  rcases le_total t 1 with h | h
  · have hp : (t ^ (-(1 / 4 : ℝ))) ^ (2 : ℕ) = t ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul ht.le]
      norm_num
    have hq : t ^ (1 / 2 : ℝ) = Real.exp (-|Real.log t| / 2) := by
      rw [Real.rpow_def_of_pos ht, abs_of_nonpos (Real.log_nonpos ht.le h), neg_neg]
      congr 1
      ring
    calc
      t * u ^ 2 ≤ t * (C * t ^ (-(1 / 4 : ℝ))) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu (hsmall h) 2) ht.le
      _ = C ^ 2 * (t ^ (1 : ℝ) * t ^ (-(1 / 2 : ℝ))) := by
        rw [mul_pow, hp, Real.rpow_one]
        ring
      _ = C ^ 2 * t ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add ht]; norm_num
      _ = _ := by rw [hq]
  · calc
      t * u ^ 2 ≤ t * (C * t⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu (hlarge h) 2) ht.le
      _ = C ^ 2 * t⁻¹ := by field_simp [ht.ne']
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
        rw [← Real.rpow_neg_one t, Real.rpow_def_of_pos ht, abs_of_nonneg (Real.log_nonneg h)]
        exact Real.exp_le_exp.mpr (by nlinarith [Real.log_nonneg h])

/-- An auxiliary analytic estimate for the quotient-kernel construction in
Theorem 12.4.1.1, Step II, pp. 516–517. For compact output support, as in a fixed
positive annulus, the two input-radius bounds imply square-integrability of the
half-density kernel in the local order-`s` Sobolev measure.

The normalization uses (12.4.1.17), p. 518, to convert the additive input measure.
-/
theorem sLocalTrace_halfDensityKernel_memLp_of_radial_bounds
    {Z : Set Jₛ} (hZ : IsCompact Z) {κ : Jₛ × Jₛ → ℂ} (hκ : Measurable κ)
    (hzero : ∀ p : Jₛ × Jₛ, p.1 ∉ Z → κ p = 0)
    {s C : ℝ} (hs : 0 ≤ s)
    (hsmall : ∀ p : Jₛ × Jₛ, p.1 ∈ Z → ((sIdeleQuotientNorm F S p.2).val : ℝ) ≤ 1 →
      ‖κ p‖ ≤ C * ((sIdeleQuotientNorm F S p.2).val : ℝ) ^ (-(1 / 4 : ℝ)))
    (hlarge : ∀ p : Jₛ × Jₛ, p.1 ∈ Z → 1 ≤ ((sIdeleQuotientNorm F S p.2).val : ℝ) →
      ‖κ p‖ ≤ C * (((sIdeleQuotientNorm F S p.2).val : ℝ))⁻¹) :
    let N (y : Jₛ) : ℝ := (sIdeleQuotientNorm F S y).val
    let ℓ := logSIdeleQuotientNorm F S
    let ν := intervalSobolevMeasure μJ ℓ 0 0 s
    let K (p : Jₛ × Jₛ) :=
      (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p /
        ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 s (ℓ p.2) : ℂ))
    MemLp K 2 (ν.prod ν) := by
  intro N ℓ ν K
  let w (y : Jₛ) := intervalSobolevDensity 0 0 s (ℓ y)
  let wNN (y : Jₛ) := (w y).toNNReal
  let c := sLocalTraceMeasureFactor S
  have hc : 0 < c := by
    unfold c sLocalTraceMeasureFactor
    refine Finset.prod_pos fun v _ ↦ ?_
    have hv : 1 < (v.asIdeal.absNorm : ℝ) := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    exact div_pos (zero_lt_one.trans hv) (sub_pos.mpr hv)
  have hN₀ (y : Jₛ) : 0 < N y := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hN : Continuous N := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_sIdeleQuotientNorm F S).continuous)
  have hℓ : Continuous ℓ := hN.log fun y ↦ (hN₀ y).ne'
  have hwForm (y : Jₛ) : w y = (1 + (ℓ y) ^ 2) ^ (s / 2) := by
    simp [w, intervalSobolevDensity]
  have hw₁ (y : Jₛ) : 1 ≤ w y := by
    rw [hwForm]
    apply Real.one_le_rpow _ (div_nonneg hs (by norm_num))
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hw₀ (y : Jₛ) : 0 < w y := zero_lt_one.trans_le (hw₁ y)
  have hw : Continuous w := by
    have hbase : Continuous (fun y : Jₛ ↦ 1 + (ℓ y) ^ 2) := continuous_const.add (hℓ.pow 2)
    exact (hbase.rpow_const (p := s / 2) fun _ ↦ Or.inr (div_nonneg hs (by norm_num))).congr
      (fun y ↦ (hwForm y).symm)
  have hwNN : Continuous wNN := continuous_real_toNNReal.comp hw
  have hwCoE (y : Jₛ) : (wNN y : ℝ) = w y := Real.coe_toNNReal _ (hw₀ y).le
  have hK : Measurable K := by
    have hroot : Continuous (fun p : Jₛ × Jₛ ↦ (Real.sqrt (N p.1 * N p.2) : ℂ)) :=
      Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
        ((hN.comp continuous_fst).mul (hN.comp continuous_snd)))
    apply (hroot.measurable.mul hκ).div
    exact measurable_const.mul (Complex.measurable_ofReal.comp (hw.measurable.comp measurable_snd))
  obtain ⟨B, hB⟩ := (hZ.image hN).bddAbove
  let boundNorm := max 1 B
  have hB₀ : 0 ≤ boundNorm := zero_le_one.trans (le_max_left _ _)
  have hNx (x : Jₛ) (hx : x ∈ Z) : N x ≤ boundNorm :=
    (hB (mem_image_of_mem N hx)).trans (le_max_right _ _)
  change MemLp K 2 (((μJ).withDensity fun y ↦ (wNN y : ℝ≥0∞)).prod
    ((μJ).withDensity fun y ↦ (wNN y : ℝ≥0∞)))
  apply sLocalQuotient_memLp_weighted_kernel_of_exp_logNorm_bound hwNN hZ hK
    (a := 1 / 2) (C := (boundNorm / c ^ 2) * C ^ 2) (by norm_num)
  intro p
  rw [hwCoE]
  by_cases hp : p.1 ∈ Z
  · rw [indicator_of_mem hp, mul_one]
    have hrad := cutoffRadialSquareMajorant_bound (hN₀ p.2) (norm_nonneg (κ p))
      (hsmall p hp) (hlarge p hp)
    have hbase : 0 ≤ N p.1 * N p.2 := mul_nonneg (hN₀ p.1).le (hN₀ p.2).le
    have hval : ‖K p‖ = Real.sqrt (N p.1 * N p.2) * ‖κ p‖ / (c * w p.2) := by
      change ‖(Real.sqrt (N p.1 * N p.2) : ℂ) * κ p / ((c : ℂ) * (w p.2 : ℂ))‖ = _
      simp only [norm_div, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg hc.le,
        Real.norm_of_nonneg (hw₀ p.2).le]
    calc
      w p.2 * ‖K p‖ ^ 2 = (N p.1 / c ^ 2) * (N p.2 * ‖κ p‖ ^ 2) / w p.2 := by
        rw [hval, div_pow, mul_pow, Real.sq_sqrt hbase]
        field_simp [hc.ne', (hw₀ p.2).ne']
      _ ≤ (N p.1 / c ^ 2) * (N p.2 * ‖κ p‖ ^ 2) :=
        div_le_self (by positivity) (hw₁ p.2)
      _ ≤ (boundNorm / c ^ 2) * (C ^ 2 * Real.exp (-|Real.log (N p.2)| / 2)) :=
        mul_le_mul (div_le_div_of_nonneg_right (hNx p.1 hp) (sq_nonneg c)) hrad
          (by positivity) (div_nonneg hB₀ (sq_nonneg c))
      _ = _ := by
        rw [show -|Real.log (N p.2)| / 2 = -(1 / 2 : ℝ) * |Real.log (N p.2)| by ring]
        ring
  · rw [indicator_of_notMem hp]
    simp [K, hzero p hp]

end RiemannMasullo
