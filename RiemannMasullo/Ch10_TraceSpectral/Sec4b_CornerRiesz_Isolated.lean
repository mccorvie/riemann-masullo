module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_CornerScalar_Isolated
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch09_HardySobolev.Sec3
import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import RiemannMasullo.AppD_SchwartzBruhat.Sec2a
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Real

/-!
# Norm-section factorization and weighted `L²` Riesz representers

This module provides the shared adelic coordinate splitting and parameterized weighted-`L²` Riesz
jet infrastructure used by `Sec4b_CornerOrbit_Isolated` and `Sec4b_CornerLowerBound_Isolated`:
1. `canonicalNormFlow F`, `exists_normFlow_freq`, `tamagawaNormFactor`, and `splitCoordEquiv F`
   factoring `ideleClassTamagawaMeasure F` over `ℝ × (ideleClassNorm F).ker`.
2. Parameterized `weightedSobolevMeasure F w`, `weightedRieszJet`, `weightedRieszJet_inner`, and
   `weightedRieszJet_norm_sq` valid uniformly for both `intervalSobolevDensity (-α) α s` and
   `coshSobolevDensity α s`.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.Isolated

section NormFlow

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => logIdeleClassNorm F

/-- The exponential one-parameter subgroup `Multiplicative ℝ →ₜ* ℝ≥0ˣ`. -/
def expUnitHom : Multiplicative ℝ →ₜ* ℝ≥0ˣ where
  toFun x := (Nonneg.unitsHomeomorphPos ℝ).symm ⟨Real.exp x.toAdd, Real.exp_pos x.toAdd⟩
  map_one' := Units.ext (NNReal.coe_injective (by
    change (((Nonneg.unitsHomeomorphPos ℝ).symm ⟨Real.exp 0, _⟩ : ℝ≥0ˣ).val : ℝ) = 1
    simp [Real.exp_zero]))
  map_mul' x y := Units.ext (NNReal.coe_injective (by
    change Real.exp (x.toAdd + y.toAdd) = Real.exp x.toAdd * Real.exp y.toAdd
    exact Real.exp_add _ _))
  continuous_toFun := (Nonneg.unitsHomeomorphPos ℝ).symm.continuous.comp
    (Continuous.subtype_mk (Real.continuous_exp.comp continuous_toAdd) _)

/-- The canonical norm-section one-parameter subgroup `LCATopologicalLie (IdeleClassGroup (𝓞 F) F)` lifting `ℝ → C𝔽`. -/
def canonicalNormFlow (F : Type*) [Field F] [NumberField F] :
    LCATopologicalLie (IdeleClassGroup (𝓞 F) F) :=
  (⟨QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F),
    QuotientGroup.continuous_mk⟩ : IdeleGroup (𝓞 F) F →ₜ* IdeleClassGroup (𝓞 F) F).comp
    ((⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩ :
      ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F).comp expUnitHom)

theorem canonicalNormFlow_coe (x : ℝ) :
    canonicalNormFlow F (Multiplicative.ofAdd x) =
      QuotientGroup.mk (canonicalIdeleNormSection F (expUnitHom (Multiplicative.ofAdd x))) := rfl

theorem ideleClassNorm_canonicalNormFlow (x : ℝ) :
    ideleClassNorm F (canonicalNormFlow F (Multiplicative.ofAdd x)) =
      expUnitHom (Multiplicative.ofAdd x) := by
  rw [canonicalNormFlow_coe]
  exact canonicalIdeleNormSection_rightInverse F _

theorem logNorm_canonicalNormFlow (x : ℝ) :
    logIdeleClassNorm F (canonicalNormFlow F (Multiplicative.ofAdd x)) = x := by
  change Real.log ((ideleClassNorm F (canonicalNormFlow F (Multiplicative.ofAdd x))).val : ℝ) = x
  rw [ideleClassNorm_canonicalNormFlow]
  exact Real.log_exp x

/-- Every unitary character `ψ : PontryaginDual C𝔽` restricts along `canonicalNormFlow F`
to a pure exponential `x ↦ exp (I * τ * x)` for a real frequency `τ`. -/
theorem exists_normFlow_freq (ψ : PontryaginDual C𝔽) :
    ∃ τ : ℝ, ∀ x : ℝ, (ψ (canonicalNormFlow F (Multiplicative.ofAdd x)) : ℂ) =
      Complex.exp (Complex.I * (τ : ℂ) * (x : ℂ)) := by
  obtain ⟨e, he⟩ := RiemannMasullo.exists_realPontryaginDualEquiv
  let ψℝ : PontryaginDual (Multiplicative ℝ) := ψ.comp (canonicalNormFlow F)
  let r : ℝ := (e.symm ψℝ).toAdd
  refine ⟨2 * Real.pi * r, fun x ↦ ?_⟩
  have hcircle : ψ (canonicalNormFlow F (Multiplicative.ofAdd x)) =
      Circle.exp (2 * Real.pi * (r * x)) := by
    rw [← he r x]
    change ψℝ (Multiplicative.ofAdd x) = e (Multiplicative.ofAdd r) (Multiplicative.ofAdd x)
    have hmr : Multiplicative.ofAdd r = e.symm ψℝ := rfl
    rw [hmr, e.apply_symm_apply]
  rw [hcircle, Circle.coe_exp]
  congr 1
  push_cast
  ring

/-- The positive real factor `(normOneIdeleClassTamagawaMeasure F) univ` relating `μ𝔽` to
`canonicalModulatedHaar` (Remark 9.2.0.1). -/
def tamagawaNormFactor (F : Type*) [Field F] [NumberField F] : ℝ :=
  ((normOneIdeleClassTamagawaMeasure F) univ).toReal

theorem tamagawaNormFactor_pos : 0 < tamagawaNormFactor F := by
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hμ := ideleClassTamagawaMeasure_eq_smul_canonical (F := F)
  have : (μ𝔽).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm
  have : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm).exists.choose_spec.1
  obtain ⟨K, hK_cpt, hK_nhds⟩ := exists_compact_mem_nhds (1 : C𝔽)
  obtain ⟨U, hUK, hU_open, hU1⟩ := mem_nhds_iff.mp hK_nhds
  have hν_pos : 0 < ν K := (hU_open.measure_pos ν ⟨1, hU1⟩).trans_le (measure_mono hUK)
  have hμ_pos : 0 < μ𝔽 K := (hU_open.measure_pos μ𝔽 ⟨1, hU1⟩).trans_le (measure_mono hUK)
  have hμ_lt : μ𝔽 K < ⊤ := hK_cpt.measure_lt_top
  have hmul : μ𝔽 K = (normOneIdeleClassTamagawaMeasure F) univ * ν K := by
    rw [hμ]
    simp [ν]
  have hne0 : (normOneIdeleClassTamagawaMeasure F) univ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact hμ_pos.ne' hmul
  have hne_top : (normOneIdeleClassTamagawaMeasure F) univ ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.top_mul hν_pos.ne'] at hmul
    exact hμ_lt.ne hmul
  exact ENNReal.toReal_pos hne0 hne_top

theorem tamagawaNormFactor_ne_top : (normOneIdeleClassTamagawaMeasure F) univ ≠ ⊤ :=
  (ENNReal.toReal_pos_iff.mp (tamagawaNormFactor_pos (F := F))).2.ne

/-- Canonical product map `(x, k) ↦ (k : IdeleClassGroup (𝓞 F) F) * canonicalNormFlow F (ofAdd x)`. -/
def splitCoordEquiv (F : Type*) [Field F] [NumberField F] :
    ℝ × (ideleClassNorm F).ker ≃ₜ IdeleClassGroup (𝓞 F) F where
  toFun p := (p.2 : IdeleClassGroup (𝓞 F) F) * canonicalNormFlow F (Multiplicative.ofAdd p.1)
  invFun g := (logIdeleClassNorm F g,
    ⟨g / canonicalNormFlow F (Multiplicative.ofAdd (logIdeleClassNorm F g)), by
    change ideleClassNorm F (g / canonicalNormFlow F (Multiplicative.ofAdd (logIdeleClassNorm F g))) = 1
    rw [map_div, ideleClassNorm_canonicalNormFlow]
    apply div_eq_one.mpr
    apply Units.ext; apply NNReal.coe_injective
    change ((ideleClassNorm F g).val : ℝ) = Real.exp (Real.log ((ideleClassNorm F g).val : ℝ))
    exact (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt _))).symm⟩)
  left_inv p := by
    apply Prod.ext
    · have hk : ideleClassNorm F (p.2 : IdeleClassGroup (𝓞 F) F) = 1 := p.2.property
      change Real.log ((ideleClassNorm F ((p.2 : IdeleClassGroup (𝓞 F) F) *
        canonicalNormFlow F (Multiplicative.ofAdd p.1))).val : ℝ) = p.1
      rw [map_mul, hk, one_mul, ideleClassNorm_canonicalNormFlow]
      exact Real.log_exp p.1
    · apply Subtype.ext
      have hk : ideleClassNorm F (p.2 : IdeleClassGroup (𝓞 F) F) = 1 := p.2.property
      have hL : logIdeleClassNorm F ((p.2 : IdeleClassGroup (𝓞 F) F) *
          canonicalNormFlow F (Multiplicative.ofAdd p.1)) = p.1 := by
        change Real.log ((ideleClassNorm F ((p.2 : IdeleClassGroup (𝓞 F) F) *
          canonicalNormFlow F (Multiplicative.ofAdd p.1))).val : ℝ) = p.1
        rw [map_mul, hk, one_mul, ideleClassNorm_canonicalNormFlow]
        exact Real.log_exp p.1
      change (p.2 : IdeleClassGroup (𝓞 F) F) * canonicalNormFlow F (Multiplicative.ofAdd p.1) /
          canonicalNormFlow F (Multiplicative.ofAdd (logIdeleClassNorm F _)) = (p.2 : IdeleClassGroup (𝓞 F) F)
      rw [hL, mul_div_cancel_right]
  right_inv g := by
    change (g / canonicalNormFlow F (Multiplicative.ofAdd (logIdeleClassNorm F g))) *
      canonicalNormFlow F (Multiplicative.ofAdd (logIdeleClassNorm F g)) = g
    exact div_mul_cancel _ _
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_snd).mul
      ((canonicalNormFlow F).continuous.comp (continuous_ofAdd.comp continuous_fst))
  continuous_invFun := by
    have hLc : Continuous (logIdeleClassNorm F) :=
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (continuousIdeleClassNorm F).continuous)).log
        fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    refine hLc.prodMk (Continuous.subtype_mk ?_ _)
    exact continuous_id.mul ((canonicalNormFlow F).continuous.comp (continuous_ofAdd.comp hLc)).inv

/-- Normalized Haar probability measure on `(ideleClassNorm F).ker`. -/
def normOneProbHaar (F : Type*) [Field F] [NumberField F] : Measure (ideleClassNorm F).ker :=
  have : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  Measure.haarMeasure ⊤

lemma normOneProbHaar_univ : normOneProbHaar F univ = 1 := by
  have : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  exact Measure.haarMeasure_self

lemma normOneProbHaar_isHaar : (normOneProbHaar F).IsHaarMeasure := by
  have : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  unfold normOneProbHaar
  infer_instance

lemma normOneProbHaar_isFinite : IsFiniteMeasure (normOneProbHaar F) :=
  ⟨by rw [normOneProbHaar_univ]; exact ENNReal.one_lt_top⟩

lemma canonicalModulatedHaar_eq_map_splitCoord :
    canonicalModulatedHaar m𝔽 ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ =
      (volume.prod (normOneProbHaar F)).map (splitCoordEquiv F) := by
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  have : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  have : (normOneProbHaar F).IsHaarMeasure := normOneProbHaar_isHaar
  have : IsFiniteMeasure (normOneProbHaar F) := normOneProbHaar_isFinite
  let hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  let τ : ℝ≥0ˣ →ₜ* C𝔽 :=
    (⟨QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F),
      QuotientGroup.continuous_mk⟩ : IdeleGroup (𝓞 F) F →ₜ* C𝔽).comp
      ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ m𝔽 := canonicalIdeleNormSection_rightInverse F
  have hcan := canonicalModulatedHaar_eq_map_prod m𝔽 hm τ hτ (normOneProbHaar F) normOneProbHaar_univ
  let expE : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have hexp_mp : MeasurePreserving expE volume positiveRealHaar := by
    refine ⟨expE.continuous.measurable, ?_⟩
    unfold positiveRealHaar
    congr 1
    funext x
    exact Units.ext (Subtype.ext (Real.coe_toNNReal _ (Real.exp_pos x).le).symm)
  let d : ℝ × (ideleClassNorm F).ker ≃ₜ (ideleClassNorm F).ker × ℝ≥0ˣ :=
    (Homeomorph.prodComm ℝ _).trans ((Homeomorph.refl _).prodCongr expE)
  have hd_mp : MeasurePreserving d (volume.prod (normOneProbHaar F))
      ((normOneProbHaar F).prod positiveRealHaar) :=
    ((MeasurePreserving.id (normOneProbHaar F)).prod hexp_mp).comp Measure.measurePreserving_swap
  have hcomp : (fun p : ℝ × (ideleClassNorm F).ker ↦ ((d p).1 : C𝔽) * τ (d p).2) = splitCoordEquiv F := by
    funext p
    rfl
  rw [hcan, ← hd_mp.map_eq, Measure.map_map (by fun_prop) d.continuous.measurable]
  congr 1

lemma measurePreserving_splitCoord :
    MeasurePreserving (splitCoordEquiv F) (volume.prod (normOneProbHaar F))
      (canonicalModulatedHaar m𝔽 ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩) :=
  ⟨(splitCoordEquiv F).continuous.measurable, canonicalModulatedHaar_eq_map_splitCoord.symm⟩

lemma integral_tamagawa_eq_splitCoord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : C𝔽 → E) :
    ∫ h : C𝔽, Φ h ∂μ𝔽 =
      tamagawaNormFactor F • ∫ p : ℝ × (ideleClassNorm F).ker, Φ (splitCoordEquiv F p)
        ∂(volume.prod (normOneProbHaar F)) := by
  rw [ideleClassTamagawaMeasure_eq_smul_canonical, integral_smul_measure]
  congr 1
  exact (measurePreserving_splitCoord.integral_comp (splitCoordEquiv F).toMeasurableEquiv.measurableEmbedding Φ).symm

lemma integrable_tamagawa_iff_splitCoord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : C𝔽 → E) :
    Integrable Φ μ𝔽 ↔ Integrable (fun p : ℝ × (ideleClassNorm F).ker ↦ Φ (splitCoordEquiv F p))
      (volume.prod (normOneProbHaar F)) := by
  rw [ideleClassTamagawaMeasure_eq_smul_canonical, integrable_smul_measure
    (fun h0 ↦ absurd h0 (ENNReal.toReal_pos_iff.mp tamagawaNormFactor_pos).1.ne')
    (tamagawaNormFactor_ne_top (F := F))]
  exact (measurePreserving_splitCoord.integrable_comp_emb
    (splitCoordEquiv F).toMeasurableEquiv.measurableEmbedding).symm

lemma integrable_one_add_sq_neg_rpow_logNorm {s : ℝ} (hs : 1 < s) :
    Integrable (fun g : C𝔽 ↦ (1 + (logNorm g) ^ 2) ^ (-s / 2)) μ𝔽 := by
  rw [integrable_tamagawa_iff_splitCoord]
  have hlog : (fun p : ℝ × (ideleClassNorm F).ker ↦ (1 + (logNorm (splitCoordEquiv F p)) ^ 2) ^ (-s / 2)) =
      fun p : ℝ × (ideleClassNorm F).ker ↦ (1 + p.1 ^ 2) ^ (-s / 2) * (1 : ℝ) := by
    funext p
    have hk : ideleClassNorm F (p.2 : C𝔽) = 1 := p.2.property
    have hL : logNorm (splitCoordEquiv F p) = p.1 := by
      change Real.log ((ideleClassNorm F ((p.2 : C𝔽) * canonicalNormFlow F (Multiplicative.ofAdd p.1))).val : ℝ) = p.1
      rw [map_mul, hk, one_mul, ideleClassNorm_canonicalNormFlow]
      exact Real.log_exp p.1
    rw [hL, mul_one]
  rw [hlog]
  have : IsFiniteMeasure (normOneProbHaar F) := normOneProbHaar_isFinite
  exact (integrable_one_add_sq_neg_rpow hs).mul_prod (integrable_const (1 : ℝ))

end NormFlow

section DensityAndRiesz

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => logIdeleClassNorm F

/-- Weighted measure on `IdeleClassGroup (𝓞 F) F` associated to a density `w : ℝ → ℝ` on `logIdeleClassNorm F`. -/
def weightedSobolevMeasure (F : Type*) [Field F] [NumberField F] (w : ℝ → ℝ) :
    Measure (IdeleClassGroup (𝓞 F) F) :=
  (ideleClassTamagawaMeasure F).withDensity fun g ↦ ENNReal.ofReal (w (logIdeleClassNorm F g))

lemma measurable_logNorm : Measurable (logIdeleClassNorm F) :=
  (NNReal.continuous_coe.comp (Units.continuous_val.comp (continuousIdeleClassNorm F).continuous)).measurable.log

lemma continuous_logNorm : Continuous (logIdeleClassNorm F) :=
  (NNReal.continuous_coe.comp (Units.continuous_val.comp (continuousIdeleClassNorm F).continuous)).log
    fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'

lemma weightedSobolevMeasure_absCont (w : ℝ → ℝ) :
    weightedSobolevMeasure F w ≪ μ𝔽 :=
  withDensity_absolutelyContinuous _ _

lemma tamagawa_absCont_weightedSobolevMeasure {w : ℝ → ℝ} (hw_cont : Continuous w)
    (hw_pos : ∀ x, 0 < w x) :
    μ𝔽 ≪ weightedSobolevMeasure F w :=
  withDensity_absolutelyContinuous' (hw_cont.measurable.comp measurable_logNorm).ennreal_ofReal.aemeasurable
    (ae_of_all _ fun _ ↦ (ENNReal.ofReal_pos.mpr (hw_pos _)).ne')

lemma continuous_intervalSobolevDensity (a b s : ℝ) : Continuous (intervalSobolevDensity a b s) := by
  unfold intervalSobolevDensity
  refine ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).max
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul ?_
  exact (continuous_const.add (continuous_id.pow 2)).rpow_const fun x ↦
    Or.inl (by positivity : (1 : ℝ) + x ^ 2 ≠ 0)

lemma intervalSobolevDensity_pos (a b s x : ℝ) : 0 < intervalSobolevDensity a b s x := by
  unfold intervalSobolevDensity
  exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)

lemma intervalSobolevDensity_shift_bound {α s R : ℝ} (_hα : 0 ≤ α) (hs : 0 ≤ s) (_hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, |x - y| ≤ R →
      intervalSobolevDensity (-α) α s x ≤ C * intervalSobolevDensity (-α) α s y := by
  refine ⟨Real.exp (2 * α * R) * (2 + 2 * R ^ 2) ^ (s / 2), by positivity, fun x y hxy ↦ ?_⟩
  unfold intervalSobolevDensity
  have h1 : Real.exp (2 * (-α) * x) ≤ Real.exp (2 * α * R) * Real.exp (2 * (-α) * y) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [abs_le.mp hxy])
  have h2 : Real.exp (2 * α * x) ≤ Real.exp (2 * α * R) * Real.exp (2 * α * y) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [abs_le.mp hxy])
  have hmax : max (Real.exp (2 * (-α) * x)) (Real.exp (2 * α * x)) ≤
      Real.exp (2 * α * R) * max (Real.exp (2 * (-α) * y)) (Real.exp (2 * α * y)) :=
    max_le (h1.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.exp_pos _).le))
      (h2.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.exp_pos _).le))
  have hpoly_base : 1 + x ^ 2 ≤ (2 + 2 * R ^ 2) * (1 + y ^ 2) := by
    have hxy_sq : (x - y) ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs (x - y), abs_le.mp hxy]
    have hx_sq : x ^ 2 ≤ 2 * y ^ 2 + 2 * R ^ 2 := by nlinarith [sq_nonneg (x - 2 * y)]
    nlinarith [sq_nonneg y]
  have hpoly : (1 + x ^ 2) ^ (s / 2) ≤ (2 + 2 * R ^ 2) ^ (s / 2) * (1 + y ^ 2) ^ (s / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hpoly_base (by linarith)
  calc max (Real.exp (2 * (-α) * x)) (Real.exp (2 * α * x)) * (1 + x ^ 2) ^ (s / 2)
      ≤ (Real.exp (2 * α * R) * max (Real.exp (2 * (-α) * y)) (Real.exp (2 * α * y))) *
          ((2 + 2 * R ^ 2) ^ (s / 2) * (1 + y ^ 2) ^ (s / 2)) :=
        mul_le_mul hmax hpoly (by positivity) (by positivity)
    _ = (Real.exp (2 * α * R) * (2 + 2 * R ^ 2) ^ (s / 2)) *
          (max (Real.exp (2 * (-α) * y)) (Real.exp (2 * α * y)) * (1 + y ^ 2) ^ (s / 2)) := by ring

lemma coshSobolevDensity_shift_bound {α s R : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, |x - y| ≤ R →
      coshSobolevDensity α s x ≤ C * coshSobolevDensity α s y := by
  obtain ⟨C, hC, h⟩ := intervalSobolevDensity_shift_bound hα hs hR
  refine ⟨2 * C, by positivity, fun x y hxy ↦ ?_⟩
  calc coshSobolevDensity α s x
      ≤ 2 * intervalSobolevDensity (-α) α s x := coshSobolevDensity_le_two_mul hα s x
    _ ≤ 2 * (C * intervalSobolevDensity (-α) α s y) := mul_le_mul_of_nonneg_left (h x y hxy) zero_le_two
    _ ≤ 2 * (C * coshSobolevDensity α s y) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (intervalSobolevDensity_le_coshSobolevDensity hα s y) hC.le) zero_le_two
    _ = (2 * C) * coshSobolevDensity α s y := by ring

lemma exp_div_intervalSobolevDensity_dom {α s σ : ℝ} (_hα : 0 ≤ α) (hσ : σ ∈ Icc (-α) α) (x : ℝ) :
    Real.exp (2 * σ * x) / intervalSobolevDensity (-α) α s x ≤ (1 + x ^ 2) ^ (-s / 2) := by
  have hexp : Real.exp (2 * σ * x) ≤ max (Real.exp (2 * (-α) * x)) (Real.exp (2 * α * x)) := by
    rcases le_total 0 x with hx | hx
    · exact (Real.exp_le_exp.mpr (by nlinarith [hσ.2])).trans (le_max_right _ _)
    · exact (Real.exp_le_exp.mpr (by nlinarith [hσ.1])).trans (le_max_left _ _)
  have h1 : (1 + x ^ 2) ^ (-s / 2) = ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
    rw [← Real.rpow_neg (by positivity)]; congr 1; ring
  have hmax_pos : 0 < max (Real.exp (2 * (-α) * x)) (Real.exp (2 * α * x)) :=
    lt_max_of_lt_left (Real.exp_pos _)
  have hdiv1 : Real.exp (2 * σ * x) / max (Real.exp (2 * (-α) * x)) (Real.exp (2 * α * x)) ≤ 1 :=
    (div_le_one hmax_pos).mpr hexp
  unfold intervalSobolevDensity
  rw [h1, div_mul_eq_div_mul_one_div, one_div]
  exact (mul_le_mul_of_nonneg_right hdiv1 (by positivity)).trans_eq (one_mul _)

lemma exp_div_coshSobolevDensity_dom {α s σ : ℝ} (hα : 0 ≤ α) (hσ : σ ∈ Icc (-α) α) (x : ℝ) :
    Real.exp (2 * σ * x) / coshSobolevDensity α s x ≤ (1 + x ^ 2) ^ (-s / 2) :=
  (div_le_div_of_nonneg_left (Real.exp_pos _).le
    (mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _))
    (intervalSobolevDensity_le_coshSobolevDensity hα s x)).trans
    (exp_div_intervalSobolevDensity_dom hα hσ x)

/-- Square-integrability of the explicit Riesz representer for `ψ |·|^{σ + i T}` in
`Lp ℂ 2 (weightedSobolevMeasure F w)`. -/
lemma weightedRieszJet_memLp {w : ℝ → ℝ} (hw_cont : Continuous w) (hw_pos : ∀ x, 0 < w x)
    {s σ : ℝ} (hs : 1 < s) (hw_dom : ∀ x, Real.exp (2 * σ * x) / w x ≤ (1 + x ^ 2) ^ (-s / 2))
    (ψ : PontryaginDual C𝔽) (T : ℝ) :
    MemLp (fun g : C𝔽 ↦ star (ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g) / (w (logNorm g) : ℂ))
      2 (weightedSobolevMeasure F w) := by
  let fn : C𝔽 → ℂ := fun g ↦
    star (ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g) / (w (logNorm g) : ℂ)
  have hfn_cont : Continuous fn := by
    refine Continuous.div (continuous_star.comp ?_) (Complex.continuous_ofReal.comp (hw_cont.comp continuous_logNorm))
      fun g ↦ Complex.ofReal_ne_zero.mpr (hw_pos _).ne'
    exact (ideleClassNormTwist ψ (↑σ + ↑T * Complex.I)).continuous
  refine (memLp_two_iff_integrable_sq_norm hfn_cont.aestronglyMeasurable).mpr ?_
  refine (integrable_withDensity_iff_integrable_smul'
    (hw_cont.measurable.comp measurable_logNorm).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mpr ?_
  refine (integrable_one_add_sq_neg_rpow_logNorm hs).mono'
    ((Measurable.smul (ENNReal.measurable_toReal.comp (hw_cont.measurable.comp measurable_logNorm).ennreal_ofReal)
      (hfn_cont.measurable.norm.pow_const 2)).aestronglyMeasurable)
    (ae_of_all _ fun g ↦ ?_)
  have hnorm_tw : ‖ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g‖ = Real.exp (σ * logNorm g) := by
    have hpos : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    change ‖((ψ g : Circle) : ℂ) * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ ((σ : ℂ) + (T : ℂ) * Complex.I))‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos,
      show ((σ : ℂ) + (T : ℂ) * Complex.I).re = σ by simp, Real.rpow_def_of_pos hpos, mul_comm]
  dsimp only [Function.comp_def, fn]
  rw [Real.norm_of_nonneg (smul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)),
    smul_eq_mul, ENNReal.toReal_ofReal (hw_pos _).le, norm_div, norm_star,
    hnorm_tw, Complex.norm_real, Real.norm_of_nonneg (hw_pos _).le, div_pow]
  calc w (logNorm g) * (Real.exp (σ * logNorm g) ^ 2 / w (logNorm g) ^ 2)
      = Real.exp (2 * σ * logNorm g) / w (logNorm g) := by
        have hw0 : w (logNorm g) ≠ 0 := (hw_pos _).ne'
        have hexp2 : Real.exp (σ * logNorm g) ^ 2 = Real.exp (2 * σ * logNorm g) := by
          rw [sq, ← Real.exp_add]; congr 1; ring
        rw [hexp2]
        field_simp [hw0]
    _ ≤ (1 + (logNorm g) ^ 2) ^ (-s / 2) := hw_dom (logNorm g)

def weightedRieszJet {w : ℝ → ℝ} (hw_cont : Continuous w) (hw_pos : ∀ x, 0 < w x)
    {s σ : ℝ} (hs : 1 < s) (hw_dom : ∀ x, Real.exp (2 * σ * x) / w x ≤ (1 + x ^ 2) ^ (-s / 2))
    (ψ : PontryaginDual C𝔽) (T : ℝ) : Lp ℂ 2 (weightedSobolevMeasure F w) :=
  (weightedRieszJet_memLp hw_cont hw_pos hs hw_dom ψ T).toLp _

lemma weightedRieszJet_inner {w : ℝ → ℝ} (hw_cont : Continuous w) (hw_pos : ∀ x, 0 < w x)
    {s σ : ℝ} (hs : 1 < s) (hw_dom : ∀ x, Real.exp (2 * σ * x) / w x ≤ (1 + x ^ 2) ^ (-s / 2))
    (ψ : PontryaginDual C𝔽) (T : ℝ) (u : Lp ℂ 2 (weightedSobolevMeasure F w)) :
    Integrable (fun g : C𝔽 ↦ u g * ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g) μ𝔽 ∧
      @inner ℂ (Lp ℂ 2 (weightedSobolevMeasure F w)) _
        (weightedRieszJet hw_cont hw_pos hs hw_dom ψ T) u =
        ∫ g : C𝔽, u g * ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g ∂μ𝔽 := by
  let r := weightedRieszJet hw_cont hw_pos hs hw_dom ψ T
  have hi_w : Integrable (fun g : C𝔽 ↦ @inner ℂ ℂ _ (r g) (u g)) (weightedSobolevMeasure F w) :=
    L2.integrable_inner (𝕜 := ℂ) r u
  have hwd : Measurable (fun g : C𝔽 ↦ ENNReal.ofReal (w (logNorm g))) :=
    (hw_cont.measurable.comp measurable_logNorm).ennreal_ofReal
  have hi_smul : Integrable (fun g : C𝔽 ↦ w (logNorm g) • @inner ℂ ℂ _ (r g) (u g)) μ𝔽 := by
    have h1 := (integrable_withDensity_iff_integrable_smul' hwd
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mp hi_w
    refine h1.congr (ae_of_all _ fun g ↦ ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (hw_pos _).le]
  have habs := tamagawa_absCont_weightedSobolevMeasure (F := F) hw_cont hw_pos
  have hrep : (r : C𝔽 → ℂ) =ᵐ[μ𝔽] fun g ↦
      star (ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g) / (w (logNorm g) : ℂ) :=
    habs.ae_le (MemLp.coeFn_toLp _)
  have hcongr : (fun g : C𝔽 ↦ w (logNorm g) • @inner ℂ ℂ _ (r g) (u g)) =ᵐ[μ𝔽]
      fun g : C𝔽 ↦ u g * ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g := by
    filter_upwards [hrep] with g hg
    rw [hg]
    simp only [RCLike.inner_apply, Complex.real_smul, Complex.star_def, map_div₀,
      Complex.conj_ofReal, starRingEnd_self_apply]
    have hw0 : (w (logNorm g) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hw_pos _).ne'
    field_simp [hw0]
  refine ⟨hi_smul.congr hcongr, ?_⟩
  rw [L2.inner_def]
  have hwd_int : ∫ x : C𝔽, @inner ℂ ℂ _ (r x) (u x) ∂(weightedSobolevMeasure F w) =
      ∫ x : C𝔽, (ENNReal.ofReal (w (logNorm x))).toReal • @inner ℂ ℂ _ (r x) (u x) ∂μ𝔽 :=
    integral_withDensity_eq_integral_toReal_smul (μ := μ𝔽) hwd
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) (fun g : C𝔽 ↦ @inner ℂ ℂ _ (r g) (u g))
  rw [hwd_int]
  calc ∫ g : C𝔽, (ENNReal.ofReal (w (logNorm g))).toReal • @inner ℂ ℂ _ (r g) (u g) ∂μ𝔽
      = ∫ g : C𝔽, w (logNorm g) • @inner ℂ ℂ _ (r g) (u g) ∂μ𝔽 :=
        integral_congr_ae (ae_of_all _ fun g ↦ by dsimp only; rw [ENNReal.toReal_ofReal (hw_pos _).le])
    _ = ∫ g : C𝔽, u g * ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g ∂μ𝔽 :=
        integral_congr_ae hcongr

lemma weightedRieszJet_norm_sq {w : ℝ → ℝ} (hw_cont : Continuous w) (hw_pos : ∀ x, 0 < w x)
    {s σ : ℝ} (hs : 1 < s) (hw_dom : ∀ x, Real.exp (2 * σ * x) / w x ≤ (1 + x ^ 2) ^ (-s / 2))
    (ψ : PontryaginDual C𝔽) (T : ℝ) :
    0 < ‖weightedRieszJet hw_cont hw_pos hs hw_dom ψ T‖ ^ 2 ∧
      ‖weightedRieszJet hw_cont hw_pos hs hw_dom ψ T‖ ^ 2 =
        tamagawaNormFactor F * ∫ x : ℝ, Real.exp (2 * σ * x) / w x := by
  have : IsFiniteMeasure (normOneProbHaar F) := normOneProbHaar_isFinite
  let r := weightedRieszJet hw_cont hw_pos hs hw_dom ψ T
  have hinner := (weightedRieszJet_inner hw_cont hw_pos hs hw_dom ψ T r).2
  have hsq : ((‖r‖ ^ 2 : ℝ) : ℂ) = @inner ℂ (Lp ℂ 2 (weightedSobolevMeasure F w)) _ r r := by
    simp [Complex.ofReal_pow]
  have habs := tamagawa_absCont_weightedSobolevMeasure (F := F) hw_cont hw_pos
  have hrep : (r : C𝔽 → ℂ) =ᵐ[μ𝔽] fun g ↦
      star (ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g) / (w (logNorm g) : ℂ) :=
    habs.ae_le (MemLp.coeFn_toLp _)
  have hint_eq : (∫ g : C𝔽, r g * ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g ∂μ𝔽) =
      ∫ g : C𝔽, ((Real.exp (2 * σ * logNorm g) / w (logNorm g) : ℝ) : ℂ) ∂μ𝔽 := by
    refine integral_congr_ae (hrep.mono fun g hg ↦ ?_)
    dsimp only
    rw [hg, div_mul_eq_mul_div]
    have hnorm : ‖ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g‖ = Real.exp (σ * logNorm g) := by
      have hpos : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
      change ‖((ψ g : Circle) : ℂ) * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ ((σ : ℂ) + (T : ℂ) * Complex.I))‖ = _
      rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos,
        show ((σ : ℂ) + (T : ℂ) * Complex.I).re = σ by simp, Real.rpow_def_of_pos hpos, mul_comm]
    have hconj_mul : star (ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g) *
        ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g =
        ((Real.exp (2 * σ * logNorm g) : ℝ) : ℂ) := by
      rw [mul_comm, Complex.star_def, Complex.mul_conj', hnorm, ← Complex.ofReal_pow, sq, ← Real.exp_add]
      congr 2; ring
    rw [hconj_mul]
    push_cast; rfl
  have hr_split : (∫ p : ℝ × (ideleClassNorm F).ker, Real.exp (2 * σ * logNorm (splitCoordEquiv F p)) /
        w (logNorm (splitCoordEquiv F p)) ∂(volume.prod (normOneProbHaar F))) =
      ∫ x : ℝ, Real.exp (2 * σ * x) / w x := by
    have heq : (fun p : ℝ × (ideleClassNorm F).ker ↦ Real.exp (2 * σ * logNorm (splitCoordEquiv F p)) /
          w (logNorm (splitCoordEquiv F p))) =
        fun p : ℝ × (ideleClassNorm F).ker ↦ (Real.exp (2 * σ * p.1) / w p.1) * (1 : ℝ) := by
      funext p
      have hk : ideleClassNorm F (p.2 : C𝔽) = 1 := p.2.property
      have hL : logNorm (splitCoordEquiv F p) = p.1 := by
        change Real.log ((ideleClassNorm F ((p.2 : C𝔽) * canonicalNormFlow F (Multiplicative.ofAdd p.1))).val : ℝ) = p.1
        rw [map_mul, hk, one_mul, ideleClassNorm_canonicalNormFlow]
        exact Real.log_exp p.1
      rw [hL, mul_one]
    rw [heq, integral_prod_mul (f := fun x : ℝ ↦ Real.exp (2 * σ * x) / w x)
        (g := fun _ : (ideleClassNorm F).ker ↦ (1 : ℝ)),
      show ∫ _k : (ideleClassNorm F).ker, (1 : ℝ) ∂(normOneProbHaar F) = 1 by
        rw [integral_const, smul_eq_mul, mul_one, Measure.real_def, normOneProbHaar_univ, ENNReal.toReal_one]]
    ring
  have hint_pos : Integrable (fun x : ℝ ↦ Real.exp (2 * σ * x) / w x) volume := by
    refine (integrable_one_add_sq_neg_rpow hs).mono'
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).div hw_cont
        fun x ↦ (hw_pos x).ne').aestronglyMeasurable)
      (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le (hw_pos _).le)]
    exact hw_dom x
  have heq_norm : ‖r‖ ^ 2 = tamagawaNormFactor F * ∫ x : ℝ, Real.exp (2 * σ * x) / w x := by
    apply Complex.ofReal_injective
    have hint_g : Integrable (fun g : C𝔽 ↦ Real.exp (2 * σ * logNorm g) / w (logNorm g)) μ𝔽 := by
      refine (integrable_one_add_sq_neg_rpow_logNorm hs).mono'
        (((Real.continuous_exp.comp (continuous_const.mul continuous_logNorm)).div
          (hw_cont.comp continuous_logNorm) fun g ↦ (hw_pos _).ne').aestronglyMeasurable)
        (ae_of_all _ fun g ↦ ?_)
      rw [Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le (hw_pos _).le)]
      exact hw_dom (logNorm g)
    rw [hsq, hinner, hint_eq, show (∫ g : C𝔽, ((Real.exp (2 * σ * logNorm g) / w (logNorm g) : ℝ) : ℂ) ∂μ𝔽) =
        Complex.ofRealCLM (∫ g : C𝔽, Real.exp (2 * σ * logNorm g) / w (logNorm g) ∂μ𝔽) from
      ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hint_g,
      Complex.ofRealCLM_apply]
    congr 1
    rw [integral_tamagawa_eq_splitCoord (fun g ↦ Real.exp (2 * σ * logNorm g) / w (logNorm g)),
      smul_eq_mul, hr_split]
  refine ⟨?_, heq_norm⟩
  rw [heq_norm]
  refine mul_pos (tamagawaNormFactor_pos (F := F)) ?_
  rw [integral_pos_iff_support_of_nonneg (fun x ↦ div_nonneg (Real.exp_pos _).le (hw_pos _).le) hint_pos]
  rw [show Function.support (fun x : ℝ ↦ Real.exp (2 * σ * x) / w x) = Set.univ from by
    ext x; simp [(hw_pos x).ne']]
  simp

end DensityAndRiesz

end RiemannMasullo.Isolated
