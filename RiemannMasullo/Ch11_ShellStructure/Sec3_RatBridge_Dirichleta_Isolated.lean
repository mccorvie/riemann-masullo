module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RatBridge_Isotypicb_Isolated
public import RiemannMasullo.Ch11_ShellStructure.Sec3_RatBridge_NextStage_Isolated

/-!
# The bridge over ℚ: stage spaces and the quotient isomorphism

Workstream B for #7351, stage 5: for a primitive Dirichlet character `χ` of conductor `N > 1`,
the closed stage spaces of (11.3.1.3), p. 494, built from `homogeneousAdelicTheta`,
`adelePrincipalValue` and `primaryDivisorialAbsolutePWTests` over `ℚ`, are identified with the
rational stage spaces `dirichletStageSpace` of `Sec3_DirichletFixedBox_Isolated`.

* `ratStripEmbed ω`: the embedding of the rational strip space `CompactIntervalSobolev volume id`
  into the strip space on the idele classes, `U ↦ (g ↦ ω(g / τ|g|)⁻¹ U(log |g|))`; it multiplies
  inner products by the norm-one mass.
* `ratBridge_stage_eq`: the closure of the half-twisted theta images of the principal values of
  box tests is the image of `dirichletStageSpace χ T' X_rat` (deliverable 1), and the same for the
  denominator `D'` of `primaryDivisorialAbsolutePW_quotient_bounds` and the next stage.
* `ratProjQuot`: the separated completion of the box tests for the seminorm `stage`, realized
  in the strip space; `ratBridge_dirichlet_quotient_iso` identifies it with
  `dirichletStageQuotient` (deliverable 2).

Nothing imports this module; all declarations live in `namespace RiemannMasullo.Isolated`.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField Set Topology IsDedekindDomain
open scoped NNReal ENNReal SchwartzMap FourierTransform NumberField.AdeleRing TensorProduct

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

open NumberFieldKB.Chebotarev.RatIdele

set_option maxSynthPendingDepth 8

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleMeasurableSpaceSec1a

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "C₁ℚ" => (ideleClassNorm ℚ).ker
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "Lℚ" => (fun g : Cℚ ↦ Real.log (((ideleClassNorm ℚ g).val : ℝ)))
local notation "massℝ" => (normOneIdeleClassTamagawaMeasure ℚ Set.univ).toReal
local notation "massNN" => (normOneIdeleClassTamagawaMeasure ℚ Set.univ).toNNReal
local notation "RStrip(" α ", " s ")" => CompactIntervalSobolev volume id (-α) α s
local notation "QStrip(" α ", " s ")" => CompactIntervalSobolev μℚ Lℚ (-α) α s
local notation "νR(" α ", " s ")" => intervalSobolevMeasure volume id (-α) α s
local notation "νQ(" α ", " s ")" => intervalSobolevMeasure μℚ Lℚ (-α) α s

/-! ### The norm-one part and the log norm -/

section Embed

theorem ratExpUnit_log (t : ℝ≥0ˣ) : ratExpUnit (Real.log ((t : ℝ≥0) : ℝ)) = t :=
  Units.ext (NNReal.eq (by
    rw [ratExpUnit_coe]
    exact Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt t))))

private theorem continuous_ideleClassNorm_ℚ : Continuous (ideleClassNorm ℚ) :=
  (isProperMap_ideleClassNorm ℚ).continuous

/-- The norm-one part `g · τ(|g|)⁻¹` of a rational idele class. -/
def ratNormOnePart (g : Cℚ) : C₁ℚ :=
  ⟨g * (ratNormSection (ideleClassNorm ℚ g))⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ideleClassNorm_ratNormSection, mul_inv_cancel]⟩

theorem ratNormOnePart_mul (g : Cℚ) :
    (ratNormOnePart g).val * ratNormSection (ratExpUnit (Lℚ g)) = g := by
  rw [ratExpUnit_log]
  simp [ratNormOnePart]

theorem ratNormOnePart_section (k : C₁ℚ) (t : ℝ≥0ˣ) :
    ratNormOnePart (k.val * ratNormSection t) = k := by
  have hn : ideleClassNorm ℚ (k.val * ratNormSection t) = t := by
    rw [map_mul, MonoidHom.mem_ker.mp k.property, ideleClassNorm_ratNormSection, one_mul]
  apply Subtype.ext
  simp [ratNormOnePart, hn]

theorem log_ideleClassNorm_section (k : C₁ℚ) (x : ℝ) :
    Lℚ (k.val * ratNormSection (ratExpUnit x)) = x := by
  simp only [map_mul, MonoidHom.mem_ker.mp k.property, ideleClassNorm_ratNormSection, one_mul,
    ratExpUnit_coe, Real.log_exp]

theorem continuous_ratNormOnePart : Continuous ratNormOnePart :=
  (continuous_id.mul (ratNormSection.continuous.comp continuous_ideleClassNorm_ℚ).inv).subtype_mk _

private theorem measurable_logNormℚ : Measurable Lℚ :=
  Real.measurable_log.comp (NNReal.continuous_coe.comp
    (Units.continuous_val.comp continuous_ideleClassNorm_ℚ)).measurable

/-- In logarithmic norm coordinates the Tamagawa measure of the rational idele classes is the
norm-one mass times Lebesgue measure (re-derived from the private lemma of stage 1). -/
private theorem ratClassTamagawa_map_log_norm' :
    (μℚ).map Lℚ = massNN • volume := by
  let ν := normOneIdeleClassTamagawaMeasure ℚ
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let : CompactSpace (ideleClassNorm ℚ).ker := (ideleClassGroup_finiteness ℚ).2.1
  let : ν.IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  let σ (t : ℝ≥0ˣ) : Cℚ := ratNormSection t
  have hσ : Continuous σ := ratNormSection.continuous
  have hr : RightInverse σ (ideleClassNorm ℚ) := ideleClassNorm_ratNormSection
  let j (p : ℝ≥0ˣ × (ideleClassNorm ℚ).ker) := σ p.1 * p.2.val
  have hj : Measurable j :=
    ((hσ.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).measurable
  let l (t : ℝ≥0ˣ) := Real.log (t.val : ℝ)
  have hl : Measurable l :=
    Real.measurable_log.comp (NNReal.continuous_coe.comp Units.continuous_val).measurable
  have hmap : positiveRealHaar.map l = volume := by
    let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    have hE : positiveRealHaar = volume.map E := by
      apply congrArg (fun h : ℝ → ℝ≥0ˣ ↦ volume.map h)
      funext y
      exact Units.ext (NNReal.eq (Real.coe_toNNReal _ (Real.exp_pos y).le))
    rw [hE, Measure.map_map hl E.continuous.measurable]
    have hcomp : l ∘ E = id := funext fun y ↦ Real.log_exp y
    rw [hcomp, Measure.map_id]
  have hcomp : (l ∘ ideleClassNorm ℚ) ∘ j = l ∘ Prod.fst := by
    funext p
    change l (ideleClassNorm ℚ (σ p.1 * p.2.val)) = l p.1
    rw [map_mul, hr, MonoidHom.mem_ker.mp p.2.property, mul_one]
  change (ideleClassTamagawaMeasure ℚ).map (l ∘ ideleClassNorm ℚ) = (ν univ).toNNReal • volume
  rw [← classTamagawa_normProduct σ hσ hr, Measure.map_map
    (hl.comp continuous_ideleClassNorm_ℚ.measurable) hj, hcomp,
    ← Measure.map_map hl measurable_fst, Measure.map_fst_prod, Measure.map_smul, hmap,
    ← Measure.coe_nnreal_smul, ENNReal.coe_toNNReal (measure_ne_top ν univ)]
  exact hl.aemeasurable

private theorem intervalSobolevDensity_pos (a b s x : ℝ) : 0 < intervalSobolevDensity a b s x := by
  simp only [intervalSobolevDensity]
  exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _)) (by positivity)

private theorem measurable_intervalSobolevDensity (a b s : ℝ) :
    Measurable (intervalSobolevDensity a b s) := by
  unfold intervalSobolevDensity
  fun_prop

/-- The weighted strip measure on the idele classes pushes forward to the norm-one mass times the
weighted strip measure on the line. -/
theorem ratStrip_map_log (α s : ℝ) : (νQ(α, s)).map Lℚ = massNN • νR(α, s) := by
  have hd : Measurable fun y ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s y) :=
    ENNReal.measurable_ofReal.comp (measurable_intervalSobolevDensity _ _ _)
  ext A hA
  rw [Measure.map_apply measurable_logNormℚ hA, smul_apply]
  change ((ideleClassTamagawaMeasure ℚ).withDensity fun g ↦
      ENNReal.ofReal (intervalSobolevDensity (-α) α s (Lℚ g)))
      (Lℚ ⁻¹' A) = massNN • (volume.withDensity fun y ↦
        ENNReal.ofReal (intervalSobolevDensity (-α) α s (id y))) A
  rw [withDensity_apply _ (measurable_logNormℚ hA), withDensity_apply _ hA,
    ← setLIntegral_map hA hd measurable_logNormℚ, ratClassTamagawa_map_log_norm',
    Measure.restrict_smul, lintegral_smul_measure]
  rfl

private theorem ratStrip_qmp (α s : ℝ) :
    QuasiMeasurePreserving Lℚ (νQ(α, s)) (νR(α, s)) :=
  ⟨measurable_logNormℚ.aemeasurable, by
    rw [ratStrip_map_log]; exact Measure.smul_absolutelyContinuous⟩

private theorem ratStrip_mp (α s : ℝ) :
    MeasurePreserving Lℚ (νQ(α, s)) (massNN • νR(α, s)) :=
  ⟨measurable_logNormℚ, ratStrip_map_log α s⟩

/-- The function `g ↦ ω(g / τ|g|)⁻¹ U(log |g|)` on the idele classes. -/
def ratStripFun (ω : PontryaginDual C₁ℚ) (U : ℝ → ℂ) (g : Cℚ) : ℂ :=
  ((ω (ratNormOnePart g) : ℂ))⁻¹ * U (Lℚ g)

private theorem continuous_ratStripWeight (ω : PontryaginDual C₁ℚ) :
    Continuous fun g : Cℚ ↦ ((ω (ratNormOnePart g) : ℂ))⁻¹ := by
  have h : Continuous fun g : Cℚ ↦ ((ω (ratNormOnePart g) : ℂ)) :=
    continuous_subtype_val.comp (ω.continuous.comp continuous_ratNormOnePart)
  exact h.inv₀ fun g ↦ Circle.coe_ne_zero _

private theorem norm_ratStripWeight (ω : PontryaginDual C₁ℚ) (g : Cℚ) :
    ‖((ω (ratNormOnePart g) : ℂ))⁻¹‖ = 1 := by
  rw [norm_inv, Circle.norm_coe, inv_one]

theorem memLp_ratStripFun (ω : PontryaginDual C₁ℚ) {α s : ℝ} {U : ℝ → ℂ}
    (hU : MemLp U 2 (νR(α, s))) : MemLp (ratStripFun ω U) 2 (νQ(α, s)) := by
  have h1 : MemLp (U ∘ Lℚ) 2 (νQ(α, s)) :=
    (hU.smul_measure ENNReal.coe_ne_top).comp_measurePreserving (ratStrip_mp α s)
  refine h1.of_le ?_ (.of_forall fun g ↦ ?_)
  · exact (continuous_ratStripWeight ω).aestronglyMeasurable.mul h1.aestronglyMeasurable
  · simp only [ratStripFun, Function.comp, norm_mul, norm_ratStripWeight, one_mul, le_refl]

private theorem inner_ratStripFun (ω : PontryaginDual C₁ℚ) (u v : ℝ → ℂ) (g : Cℚ) :
    inner ℂ (ratStripFun ω u g) (ratStripFun ω v g) = inner ℂ (u (Lℚ g)) (v (Lℚ g)) := by
  simp only [ratStripFun, RCLike.inner_apply]
  set w : ℂ := ((ω (ratNormOnePart g) : ℂ))⁻¹
  have hw : w * (starRingEnd ℂ) w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_ratStripWeight ω g, one_pow,
      Complex.ofReal_one]
  rw [map_mul]
  linear_combination (v (Lℚ g) * (starRingEnd ℂ) (u (Lℚ g))) * hw

/-- The norm-one mass of the rational idele classes is positive. -/
theorem ratMass_pos : 0 < massℝ := by
  let : CompactSpace (ideleClassNorm ℚ).ker := (ideleClassGroup_finiteness ℚ).2.1
  let : (normOneIdeleClassTamagawaMeasure ℚ).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  exact ENNReal.toReal_pos (isOpen_univ.measure_pos _ univ_nonempty).ne'
    (isCompact_univ.measure_lt_top).ne

private theorem ratStripFun_add (ω : PontryaginDual C₁ℚ) {α s : ℝ} (U V : RStrip(α, s)) :
    ratStripFun ω ⇑(U + V) =ᵐ[νQ(α, s)] ratStripFun ω ⇑U + ratStripFun ω ⇑V := by
  filter_upwards [(Lp.coeFn_add U V).comp_tendsto (ratStrip_qmp α s).tendsto_ae] with g hg
  simp only [Function.comp, Pi.add_apply] at hg
  simp only [ratStripFun, Pi.add_apply, hg, mul_add]

private theorem ratStripFun_smul (ω : PontryaginDual C₁ℚ) {α s : ℝ} (c : ℂ) (U : RStrip(α, s)) :
    ratStripFun ω ⇑(c • U) =ᵐ[νQ(α, s)] c • ratStripFun ω ⇑U := by
  filter_upwards [(Lp.coeFn_smul c U).comp_tendsto (ratStrip_qmp α s).tendsto_ae] with g hg
  simp only [Function.comp, Pi.smul_apply, smul_eq_mul] at hg
  simp only [ratStripFun, Pi.smul_apply, hg, smul_eq_mul]
  ring

/-- The embedding as a linear map. -/
def ratStripEmbedₗ (ω : PontryaginDual C₁ℚ) (α s : ℝ) : RStrip(α, s) →ₗ[ℂ] QStrip(α, s) where
  toFun U := (memLp_ratStripFun ω (Lp.memLp U)).toLp _
  map_add' U V := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (ratStripFun_add ω U V)
  map_smul' c U := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (ratStripFun_smul ω c U)

theorem ratStripEmbedₗ_ae (ω : PontryaginDual C₁ℚ) {α s : ℝ} (U : RStrip(α, s)) :
    ⇑(ratStripEmbedₗ ω α s U) =ᵐ[νQ(α, s)] ratStripFun ω ⇑U :=
  MemLp.coeFn_toLp (memLp_ratStripFun ω (Lp.memLp U))

/-- The embedding multiplies inner products by the norm-one mass. -/
theorem inner_ratStripEmbedₗ (ω : PontryaginDual C₁ℚ) {α s : ℝ} (U V : RStrip(α, s)) :
    inner ℂ (ratStripEmbedₗ ω α s U) (ratStripEmbedₗ ω α s V) = (massℝ : ℂ) * inner ℂ U V := by
  rw [L2.inner_def, L2.inner_def]
  have h1 : ∫ g, inner ℂ (ratStripEmbedₗ ω α s U g) (ratStripEmbedₗ ω α s V g) ∂(νQ(α, s)) =
      ∫ g, (fun y ↦ inner ℂ (U y) (V y)) (Lℚ g) ∂(νQ(α, s)) := by
    refine integral_congr_ae ?_
    filter_upwards [ratStripEmbedₗ_ae ω U, ratStripEmbedₗ_ae ω V] with g hU hV
    rw [hU, hV, inner_ratStripFun]
  have hm : AEStronglyMeasurable (fun y ↦ inner ℂ (U y) (V y)) ((νQ(α, s)).map Lℚ) := by
    rw [ratStrip_map_log]
    exact ((Lp.aestronglyMeasurable U).inner (Lp.aestronglyMeasurable V)).smul_measure _
  rw [h1, ← integral_map (ratStrip_qmp α s).aemeasurable hm, ratStrip_map_log,
    integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  rfl

/-- The embedding multiplies norms by the square root of the norm-one mass. -/
theorem norm_ratStripEmbedₗ (ω : PontryaginDual C₁ℚ) {α s : ℝ} (U : RStrip(α, s)) :
    ‖ratStripEmbedₗ ω α s U‖ = Real.sqrt massℝ * ‖U‖ := by
  have h := inner_ratStripEmbedₗ ω U U
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖ratStripEmbedₗ ω α s U‖ ^ 2 = massℝ * ‖U‖ ^ 2 := by
    have h2 : ((‖ratStripEmbedₗ ω α s U‖ ^ 2 : ℝ) : ℂ) = ((massℝ * ‖U‖ ^ 2 : ℝ) : ℂ) := by
      push_cast; exact h
    exact_mod_cast h2
  rw [← Real.sqrt_sq (norm_nonneg (ratStripEmbedₗ ω α s U)), h', Real.sqrt_mul ratMass_pos.le,
    Real.sqrt_sq (norm_nonneg U)]

/-- **The strip embedding.** `U ↦ (g ↦ ω(g / τ|g|)⁻¹ U(log |g|))` from the rational strip space to
the strip space on the idele classes; it multiplies inner products by the norm-one mass
(`inner_ratStripEmbed`). -/
def ratStripEmbed (ω : PontryaginDual C₁ℚ) (α s : ℝ) : RStrip(α, s) →L[ℂ] QStrip(α, s) :=
  (ratStripEmbedₗ ω α s).mkContinuous (Real.sqrt massℝ) fun U ↦ (norm_ratStripEmbedₗ ω U).le

theorem ratStripEmbed_apply (ω : PontryaginDual C₁ℚ) {α s : ℝ} (U : RStrip(α, s)) :
    ratStripEmbed ω α s U = ratStripEmbedₗ ω α s U := rfl

theorem ratStripEmbed_ae (ω : PontryaginDual C₁ℚ) {α s : ℝ} (U : RStrip(α, s)) :
    ⇑(ratStripEmbed ω α s U) =ᵐ[νQ(α, s)] ratStripFun ω ⇑U :=
  ratStripEmbedₗ_ae ω U

theorem inner_ratStripEmbed (ω : PontryaginDual C₁ℚ) {α s : ℝ} (U V : RStrip(α, s)) :
    inner ℂ (ratStripEmbed ω α s U) (ratStripEmbed ω α s V) = (massℝ : ℂ) * inner ℂ U V :=
  inner_ratStripEmbedₗ ω U V

theorem norm_ratStripEmbed (ω : PontryaginDual C₁ℚ) {α s : ℝ} (U : RStrip(α, s)) :
    ‖ratStripEmbed ω α s U‖ = Real.sqrt massℝ * ‖U‖ :=
  norm_ratStripEmbedₗ ω U

theorem ratStripEmbed_injective (ω : PontryaginDual C₁ℚ) (α s : ℝ) :
    Injective (ratStripEmbed ω α s) := by
  refine (injective_iff_map_eq_zero _).mpr fun U hU ↦ ?_
  have h := norm_ratStripEmbed ω U
  rw [hU, norm_zero] at h
  exact norm_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left
    (Real.sqrt_pos.mpr ratMass_pos).ne')

/-- The image of a closed subspace under the strip embedding is closed. -/
theorem isClosed_map_ratStripEmbed (ω : PontryaginDual C₁ℚ) {α s : ℝ}
    (E : Submodule ℂ (RStrip(α, s))) (hE : IsClosed (E : Set (RStrip(α, s)))) :
    IsClosed ((E.map (ratStripEmbed ω α s).toLinearMap : Submodule ℂ (QStrip(α, s))) :
      Set (QStrip(α, s))) := by
  have hc : 0 < Real.sqrt massℝ := Real.sqrt_pos.mpr ratMass_pos
  have hanti : AntilipschitzWith (Real.toNNReal (Real.sqrt massℝ)⁻¹) (ratStripEmbed ω α s) :=
    AntilipschitzWith.of_le_mul_dist fun x y ↦ by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_ratStripEmbed,
        Real.coe_toNNReal _ (inv_nonneg.mpr hc.le), ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  have := (hanti.isUniformEmbedding (ratStripEmbed ω α s).uniformContinuous).isClosedEmbedding
  exact this.isClosedMap _ hE

end Embed


/-! ### Half-twisted theta maps and principal values -/

section HalfTheta

local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "P₀ℚ" => ↥(adelePolarSubspace ℚ)

/-- `j` is a half-twisted homogeneous theta map into the strip space, as in
`PrimaryDivisorialAbsolutePWSeparated`: `j g = r^{1/2} Θ_ω(g)` almost everywhere. -/
def IsRatHalfThetaMap (ω : PontryaginDual C₁ℚ) {α s : ℝ} (j : P₀ℚ →ₗ[ℂ] QStrip(α, s)) : Prop :=
  ∀ g : P₀ℚ, ((j g : QStrip(α, s)) : Cℚ → ℂ) =ᵐ[μℚ] fun x ↦
    (((((ideleClassNorm ℚ x).val : ℝ)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * homogeneousAdelicTheta ω g.val x

/-- A half-twisted theta map exists on every strip (re-derived from the private
`primaryDivisorialAbsolutePW_stripMap` of `Sec3_FixedBox`). -/
theorem exists_isRatHalfThetaMap (ω : PontryaginDual C₁ℚ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    ∃ j : P₀ℚ →ₗ[ℂ] QStrip(α, s), IsRatHalfThetaMap ω j := by
  have hI : -α ≤ α := by linarith
  let q := (homogeneousAdelicThetaLinearMap ℚ ω).ker.mkQ
  let Q := (q.comp (adelePolarSubspace ℚ).subtype).codRestrict
    (globalPolarFreeThetaSubmodule (F := ℚ) ω) fun f ↦ ⟨f.val, f.property, rfl⟩
  obtain ⟨j, -, -, hj⟩ :=
    exists_globalHomogeneousThetaSobolevInclusion (F := ℚ) (a := 1 / 2) hI hs ω
  let intoAmbient (U : Submodule ℂ (QStrip(α, s))) (A : Submodule ℂ U) :=
    U.subtype.comp A.subtype
  exact ⟨(intoAmbient _ _).comp (j.toLinearMap.comp Q), fun f ↦ (hj f (Q f) rfl).2⟩

private theorem ae_congr_of_rep {X Y : Type*} {μ : Measure Cℚ} (E : Y → X) (c : X → Cℚ → ℂ)
    (Θ : Y → Cℚ → ℂ) (hE : ∀ g, c (E g) =ᵐ[μ] Θ g) (M : X → X) (P : Y → Y)
    (hM : ∀ g, M (E g) = E (P g)) (hinj : ∀ x y, c x =ᵐ[μ] c y → x = y) (f f' : Y)
    (h : Θ f =ᵐ[μ] Θ f') : Θ (P f) =ᵐ[μ] Θ (P f') := by
  have h1 : E f = E f' := hinj _ _ (((hE f).trans h).trans (hE f').symm)
  have h4 : E (P f) = E (P f') := by rw [← hM, ← hM, h1]
  have h5 : c (E (P f)) = c (E (P f')) := congrArg c h4
  exact ((hE _).symm.trans (EventuallyEq.of_eq h5)).trans (hE _)

/-- The homogeneous theta of a principal value depends only on the homogeneous theta of the
test: through main's `globalThetaSobolevPrincipalValue_homogeneous_apply` on the zero line. -/
theorem homTheta_principalValue_congr_ae (ω : PontryaginDual C₁ℚ) (T : Finset Vℚ)
    (f f' : P₀ℚ) (h : homogeneousAdelicTheta ω f.val =ᵐ[μℚ] homogeneousAdelicTheta ω f'.val) :
    homogeneousAdelicTheta ω (adelePolarPrincipalValue T f).val =ᵐ[μℚ]
      homogeneousAdelicTheta ω (adelePolarPrincipalValue T f').val := by
  have hs : (0 : ℝ) ≤ 0 := le_rfl
  let E := fun g : P₀ℚ ↦ ((existsUnique_globalThetaSobolevAverage (F := ℚ)
      (a := 0) (le_refl (0 : ℝ)) hs ω).exists.choose (globalThetaSobolevInclusion ℚ 0
        (le_refl (0 : ℝ)) hs (Submodule.Quotient.mk g))).val
  have hM : ∀ g, globalThetaSobolevPrincipalValue ℚ T 0 hs (E g) =
      E (adelePolarPrincipalValue T g) :=
    fun g ↦ globalThetaSobolevPrincipalValue_homogeneous_apply (F := ℚ) T 0 hs ω g
  have hinj : ∀ x y : ↥(globalThetaSobolev ℚ 0 (le_refl (0 : ℝ)) hs),
      (⇑(x.val) : Cℚ → ℂ) =ᵐ[μℚ] ⇑(y.val) → x = y :=
    fun x y hxy ↦ Subtype.ext (Lp.ext (hxy.filter_mono
      (withDensity_absolutelyContinuous _ _).ae_le))
  obtain ⟨j, -, -, hj⟩ :=
    exists_globalHomogeneousThetaSobolevInclusion (F := ℚ) (a := 0) (le_refl (0 : ℝ)) hs ω
  have hE : ∀ g : P₀ℚ, (⇑((E g).val) : Cℚ → ℂ) =ᵐ[μℚ] homogeneousAdelicTheta ω g.val := by
    intro g
    obtain ⟨h0, h1⟩ := hj g ⟨Submodule.Quotient.mk g.val, ⟨g.val, g.property, rfl⟩⟩ rfl
    refine EventuallyEq.trans (EventuallyEq.of_eq ?_)
      (h1.trans (EventuallyEq.of_eq (modulationWeight_zero _ _)))
    rw [h0]
  exact ae_congr_of_rep E (fun x ↦ ⇑(x.val)) (fun g : P₀ℚ ↦ homogeneousAdelicTheta ω g.val) hE
    (globalThetaSobolevPrincipalValue ℚ T 0 hs) (adelePolarPrincipalValue T) hM hinj f f' h


end HalfTheta


/-! ### Profiles of principal values -/

section Profiles

local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "P₀ℚ" => ↥(adelePolarSubspace ℚ)
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "ι" => IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ

private theorem half_rpow_mul_exp (g : Cℚ) :
    (((((ideleClassNorm ℚ g).val : ℝ)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      (Real.exp (-(Lℚ g / 2)) : ℂ) = 1 := by
  have hpos : (0 : ℝ) < ((ideleClassNorm ℚ g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  rw [Real.rpow_def_of_pos hpos, ← Complex.ofReal_mul, ← Real.exp_add]
  beta_reduce
  rw [show Real.log ((ideleClassNorm ℚ g).val : ℝ) * (1 / 2) +
    -(Real.log ((ideleClassNorm ℚ g).val : ℝ) / 2) = 0 by ring, Real.exp_zero, Complex.ofReal_one]

/-- **Profile lemma.** If the homogeneous theta of a polar test is `ω(k)⁻¹ M e^{-x/2} D(x)` at the
class `k τ(eˣ)` (almost everywhere), then its half-twisted image is the strip embedding of
`M • D`. -/
theorem halfThetaMap_eq_embed (ω : PontryaginDual C₁ℚ) {α s : ℝ} {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)}
    (hj : IsRatHalfThetaMap ω j) (φ : P₀ℚ) (M : ℂ) {D : ℝ → ℂ} (hD : MemLp D 2 (νR(α, s)))
    (hΘ : homogeneousAdelicTheta ω φ.val =ᵐ[μℚ] fun g ↦
      ((ω (ratNormOnePart g) : ℂ))⁻¹ * M * ((Real.exp (-(Lℚ g / 2)) : ℂ) * D (Lℚ g))) :
    j φ = ratStripEmbed ω α s (M • hD.toLp D) := by
  have hac : νQ(α, s) ≪ μℚ := withDensity_absolutelyContinuous _ _
  have h4 : (⇑(M • hD.toLp D) ∘ Lℚ) =ᵐ[νQ(α, s)] (M • D) ∘ Lℚ :=
    ((Lp.coeFn_smul M (hD.toLp D)).trans (hD.coeFn_toLp.const_smul M)).comp_tendsto
      (ratStrip_qmp α s).tendsto_ae
  refine Lp.ext ?_
  filter_upwards [(hj φ).filter_mono hac.ae_le, hΘ.filter_mono hac.ae_le,
    ratStripEmbed_ae ω (M • hD.toLp D), h4] with g h1 h2 h3 h4
  rw [h1, h2, h3]
  simp only [Function.comp, Pi.smul_apply, smul_eq_mul] at h4
  simp only [ratStripFun, h4]
  linear_combination ((ω (ratNormOnePart g) : ℂ))⁻¹ * M * D (Lℚ g) * half_rpow_mul_exp g

/-- Tests of an absolute Paley–Wiener level are invariant under the local units outside `S`. -/
theorem isLocalUnitInvariant_of_mem_absolutePWTests {S : Finset Vℚ} {X : ℝ} (g : P₀ℚ)
    (hg : g ∈ primaryDivisorialAbsolutePWTests (F := ℚ) S X) {v : Vℚ} (hv : v ∉ S) :
    IsLocalUnitInvariant v g.val := by
  classical
  obtain ⟨k, -, hk⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hg)
  have hk' : sAdeleSchwartzToGlobal ℚ S k = g.val := hk
  intro u hu x
  have hu1 : Valued.v (u : v.adicCompletion ℚ) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hu
  have hsnd (w : Vℚ) (hw : w ≠ v) : (x * (ι v u : 𝔸)).2 w = x.2 w := by
    change x.2 w * Pi.mulSingle v (u : v.adicCompletion ℚ) w = _
    rw [Pi.mulSingle_eq_of_ne hw, mul_one]
  have hself : (x * (ι v u : 𝔸)).2 v = x.2 v * u := by
    change x.2 v * Pi.mulSingle v (u : v.adicCompletion ℚ) v = _
    rw [Pi.mulSingle_eq_same]
  have hc (w : Vℚ) : (x * (ι v u : 𝔸)).2 w ∈ w.adicCompletionIntegers ℚ ↔
      x.2 w ∈ w.adicCompletionIntegers ℚ := by
    by_cases hw : w = v
    · subst hw
      rw [hself, HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hu1, mul_one]
    · rw [hsnd w hw]
  have hproj : adeleProjection ℚ S (x * (ι v u : 𝔸)) = adeleProjection ℚ S x := by
    refine Prod.ext (mul_one x.1) (funext fun w ↦ ?_)
    exact hsnd w.val (fun h ↦ hv (h ▸ w.property))
  rw [← hk', sAdeleSchwartzToGlobal_apply, sAdeleSchwartzToGlobal_apply, hproj]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd (fun w hw ↦ (hc w).mp (h₁ w hw)) h₂
  · exact absurd (fun w hw ↦ (hc w).mpr (h₂ w hw)) h₁
  · rfl

/-- An almost-everywhere identity on the idele classes in the log norm gives one on the line. -/
theorem ae_line_of_ae_class {F : ℝ → ℂ} (hF : Continuous F)
    (h : ∀ᵐ g ∂μℚ, F (Lℚ g) = 0) : F = 0 := by
  have hm : MeasurableSet {y : ℝ | F y = 0} := (isClosed_eq hF continuous_const).measurableSet
  have h1 : ∀ᵐ y ∂((ideleClassTamagawaMeasure ℚ).map Lℚ), F y = 0 :=
    (ae_map_iff measurable_logNormℚ.aemeasurable hm).mpr h
  rw [ratClassTamagawa_map_log_norm'] at h1
  have hne : (massNN : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.coe_ne_zero]
    intro h0
    have := ratMass_pos
    rw [← ENNReal.coe_toNNReal_eq_toReal, h0, NNReal.coe_zero] at this
    exact lt_irrefl _ this
  have h2 : ∀ᵐ y ∂(volume : Measure ℝ), F y = 0 := by
    rw [← Measure.coe_nnreal_smul] at h1
    exact (Measure.absolutelyContinuous_smul hne).ae_le h1
  exact (hF.ae_eq_iff_eq volume continuous_const).mp h2

end Profiles


/-! ### Deliverable 1: the stage spaces -/

section Stage

local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "P₀ℚ" => ↥(adelePolarSubspace ℚ)

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

set_option hygiene false in
local notation "ω" => ratDirichletNormOneChar hχ
local notation "Sχ" => ratDirichletS N
local notation "mass" => ((normOneIdeleClassTamagawaMeasure ℚ Set.univ).toReal : ℂ)
local notation "Wℚ(" X ")" => primaryDivisorialAbsolutePWTests (F := ℚ) (ratDirichletS N) X

theorem pos_of_ratBoxHyp (hN : 1 < N) {X : ℝ}
    (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X) : 0 < X := by
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hN
  exact lt_of_lt_of_le (pow_pos (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos) _)
    (hX p hp)

theorem ratDirichletBoxShift_pos (hN : 1 < N) {X : ℝ}
    (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X) :
    0 < ratDirichletBoxShift N X := by
  unfold ratDirichletBoxShift
  exact mul_pos (pos_of_ratBoxHyp hN hX) (Finset.prod_pos fun q hq ↦
    pow_pos (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hq).pos) _)

/-- The primes of a finite set of places coprime to `N`. -/
theorem ratPrimes_spec (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) :
    ∀ q ∈ T.image pr, q.Prime ∧ q.Coprime N := by
  intro q hq
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
  exact ⟨pr_prime v, hT v hv⟩

theorem ratPrimes_prod_pos (T : Finset Vℚ) : 0 < ∏ q ∈ T.image pr, (q : ℝ) :=
  Finset.prod_pos fun q hq ↦ by
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hq
    exact Nat.cast_pos.mpr (pr_prime v).pos

/-- The homogeneous theta of the principal value of a test of an absolute Paley–Wiener level
whose theta is that of a Dirichlet test `dirTest f₀`, everywhere. -/
theorem homTheta_principalValue_of_mem (hχ : χ.IsPrimitive) (hN : 1 < N) (T : Finset Vℚ)
    (hT : ∀ v ∈ T, (pr v).Coprime N) {X : ℝ} (g : P₀ℚ) (hg : g ∈ Wℚ(X)) (f₀ : 𝓢(ℝ, ℂ))
    (hgf : ∀ (t : ℝ≥0ˣ) (k : C₁ℚ), homogeneousAdelicTheta ω g.val (k.val * ratNormSection t) =
      homogeneousAdelicTheta ω (dirTest hχ f₀) (k.val * ratNormSection t))
    (k : C₁ℚ) (x : ℝ) :
    homogeneousAdelicTheta ω (adelePrincipalValue ℚ T g.val)
        (k.val * ratNormSection (ratExpUnit x)) =
      (ω k : ℂ)⁻¹ * mass * ((Real.exp (-(x / 2)) : ℂ) *
        dirichletDeplete χ (T.image pr) (twistedHalfLogProfile χ f₀) x) :=
  ratBridge_principalValue_general hχ T hT g.val (fun v hv ↦
    isLocalUnitInvariant_of_mem_absolutePWTests g hg (notMem_ratDirichletS_of_coprime (hT v hv)))
    _ (twistedRadialTheta χ f₀)
    (fun t k ↦ (hgf t k).trans (ratBridge_dirichletTest_theta hχ hN f₀ t k))
    k x

/-- The same as a function on the idele classes. -/
theorem homTheta_principalValue_of_mem' (hχ : χ.IsPrimitive) (hN : 1 < N) (T : Finset Vℚ)
    (hT : ∀ v ∈ T, (pr v).Coprime N) {X : ℝ} (g : P₀ℚ) (hg : g ∈ Wℚ(X)) (f₀ : 𝓢(ℝ, ℂ))
    (hgf : ∀ (t : ℝ≥0ˣ) (k : C₁ℚ), homogeneousAdelicTheta ω g.val (k.val * ratNormSection t) =
      homogeneousAdelicTheta ω (dirTest hχ f₀) (k.val * ratNormSection t)) :
    homogeneousAdelicTheta ω (adelePolarPrincipalValue T g).val = fun x ↦
      ((ω (ratNormOnePart x) : ℂ))⁻¹ * mass * ((Real.exp (-(Lℚ x / 2)) : ℂ) *
        dirichletDeplete χ (T.image pr) (twistedHalfLogProfile χ f₀) (Lℚ x)) := by
  funext x
  have h := homTheta_principalValue_of_mem hχ hN T hT g hg f₀ hgf (ratNormOnePart x) (Lℚ x)
  rw [ratNormOnePart_mul] at h
  exact h

/-- The homogeneous theta of the principal value of a Dirichlet test, as a function. -/
theorem homTheta_principalValue_dirTest' (hχ : χ.IsPrimitive) (hN : 1 < N) (T : Finset Vℚ)
    (hT : ∀ v ∈ T, (pr v).Coprime N) (f : 𝓢(ℝ, ℂ)) :
    homogeneousAdelicTheta ω (adelePrincipalValue ℚ T (dirTest hχ f)) = fun x ↦
      ((ω (ratNormOnePart x) : ℂ))⁻¹ * mass * ((Real.exp (-(Lℚ x / 2)) : ℂ) *
        dirichletDeplete χ (T.image pr) (twistedHalfLogProfile χ f) (Lℚ x)) := by
  funext x
  have h := ratBridge_principalValue hχ hN T hT f (ratNormOnePart x) (Lℚ x)
  rw [ratNormOnePart_mul] at h
  exact h

/-- **Core identity.** The half-twisted theta image of the principal value of a box test is the
strip embedding of `mass` times the depleted profile of its Dirichlet test. -/
theorem halfThetaMap_principalValue_of_mem (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j) (T : Finset Vℚ)
    (hT : ∀ v ∈ T, (pr v).Coprime N) {X : ℝ} (g : P₀ℚ) (hg : g ∈ Wℚ(X)) (f₀ : 𝓢(ℝ, ℂ))
    (hgf : ∀ (t : ℝ≥0ˣ) (k : C₁ℚ), homogeneousAdelicTheta ω g.val (k.val * ratNormSection t) =
      homogeneousAdelicTheta ω (dirTest hχ f₀) (k.val * ratNormSection t))
    (hmem : MemLp (dirichletDeplete χ (T.image pr) (twistedHalfLogProfile χ f₀)) 2 (νR(α, s))) :
    j (adelePolarPrincipalValue T g) =
      ratStripEmbed ω α s (mass • toDirichletStrip α s _ hmem) :=
  halfThetaMap_eq_embed ω hj _ mass hmem
    (EventuallyEq.of_eq (homTheta_principalValue_of_mem' hχ hN T hT g hg f₀ hgf))

private theorem map_topologicalClosure_le' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f : E →L[ℂ] F) (s : Submodule ℂ E) :
    s.topologicalClosure.map f.toLinearMap ≤ (s.map f.toLinearMap).topologicalClosure := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Submodule.topologicalClosure_coe] at hx
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact map_mem_closure f.continuous hx fun y hy ↦ ⟨y, hy, rfl⟩

/-- The closed project stage space: the closure of the half-twisted theta images of the
principal values `PV_T` of the tests of the absolute Paley–Wiener level `X` at `S`. -/
def ratProjStage (S : Finset Vℚ) {α s : ℝ} (j : P₀ℚ →ₗ[ℂ] QStrip(α, s)) (T : Finset Vℚ) (X : ℝ) :
    Submodule ℂ (QStrip(α, s)) :=
  ((primaryDivisorialAbsolutePWTests (F := ℚ) S X).map
    (j.comp (adelePolarPrincipalValue T))).topologicalClosure

private theorem mass_ne_zero' : mass ≠ 0 := Complex.ofReal_ne_zero.mpr ratMass_pos.ne'

/-- Paper: (11.3.1.3), p. 494, over `ℚ`.
**Deliverable 1, first part.** For a primitive `χ` mod `N > 1`, a box `X ≥ q^{e_q}` and a finite set
`T` of places `p ∤ N` (primes `T'`), the closure of the half-twisted theta images
`r^{1/2} Θ_ω(PV_T g)` of the tests `g` of the absolute Paley–Wiener level `X` is the image of the
rational stage space `dirichletStageSpace χ T' X_rat`, `X_rat = R(X) ∏_{q ∈ T'} q`, under the
strip embedding; on generators the image of `U` is reached as `j(PV_T g) = ι(mass • U)`.
Deviation: the factor `mass` is absorbed (a subspace is invariant under a nonzero scalar); the
identification of spaces is `ratStripEmbed ω`, which multiplies inner products by `mass`. -/
theorem ratBridge_stage_eq_first (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ} (hα : 0 ≤ α)
    (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j) (T : Finset Vℚ)
    (hT : ∀ v ∈ T, (pr v).Coprime N) {X : ℝ}
    (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X) :
    ratProjStage Sχ j T X =
      (dirichletStageSpace χ (T.image pr) (ratDirichletBoxShift N X * ∏ q ∈ T.image pr, (q : ℝ))
        α s hα hs).map (ratStripEmbed ω α s).toLinearMap := by
  have hprod := ratPrimes_prod_pos T
  have hR := ratDirichletBoxShift_pos hN hX
  have hTpos : ∀ q ∈ T.image pr, 0 < q := fun q hq ↦ (ratPrimes_spec T hT q hq).1.pos
  have hdiv : (ratDirichletBoxShift N X * ∏ q ∈ T.image pr, (q : ℝ)) / ∏ q ∈ T.image pr, (q : ℝ) =
      ratDirichletBoxShift N X := mul_div_cancel_right₀ _ hprod.ne'
  apply le_antisymm
  · refine Submodule.topologicalClosure_minimal _ ?_
      (isClosed_map_ratStripEmbed ω _ (isClosed_dirichletStageSpace χ _ _ α s hα hs))
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨f₀, hbox, hgf⟩ := ratBridge_dirichlet_isotypic hχ hN hX g hg
    have hmem := dirichletDeplete_memLp hχ hN (T.image pr) hTpos hR hα hs hbox (α := α) (s := s)
    have hbox' : IsDirichletFixedBoxTest χ
        ((ratDirichletBoxShift N X * ∏ q ∈ T.image pr, (q : ℝ)) / ∏ q ∈ T.image pr, (q : ℝ))
        f₀ := by
      rw [hdiv]; exact hbox
    exact ⟨mass • toDirichletStrip α s _ hmem, Submodule.smul_mem _ _
      (mem_dirichletStageSpace_of_test _ hα hs hbox' hmem),
      (halfThetaMap_principalValue_of_mem hχ hN hj T hT g hg f₀ hgf hmem).symm⟩
  · refine (map_topologicalClosure_le' (ratStripEmbed ω α s) _).trans
      (Submodule.topologicalClosure_mono ?_)
    refine (Submodule.map_span_le _ _ _).mpr ?_
    rintro _ ⟨f₀, hbox', hmem, rfl⟩
    have hbox : IsDirichletFixedBoxTest χ (ratDirichletBoxShift N X) f₀ := by
      rw [← hdiv]; exact hbox'
    obtain ⟨g, hg, hgf⟩ := ratBridge_dirichlet_isotypic_converse hχ hN hX f₀ hbox.2
    refine ⟨mass⁻¹ • g, Submodule.smul_mem _ _ hg, ?_⟩
    change j (adelePolarPrincipalValue T (mass⁻¹ • g)) = ratStripEmbed ω α s _
    rw [map_smul, map_smul, halfThetaMap_principalValue_of_mem hχ hN hj T hT g hg f₀ hgf hmem,
      map_smul, smul_smul, inv_mul_cancel₀ mass_ne_zero', one_smul]

/-- Two principal-value representatives agree in the theta quotient iff the homogeneous thetas
agree. -/
theorem divisorialThetaRepresentative_eq_iff (ω₁ : PontryaginDual C₁ℚ) (T T₂ : Finset Vℚ)
    (a b : P₀ℚ) :
    divisorialThetaRepresentative ω₁ T a = divisorialThetaRepresentative ω₁ T₂ b ↔
      homogeneousAdelicTheta ω₁ (adelePolarPrincipalValue T a).val =
        homogeneousAdelicTheta ω₁ (adelePolarPrincipalValue T₂ b).val := by
  unfold divisorialThetaRepresentative
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq, LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.coe_sub,
    map_sub, sub_eq_zero]
  rfl

private theorem toDirichletStrip_congr' {α s : ℝ} {U V : ℝ → ℂ} (h : U = V)
    (hU : MemLp U 2 (νR(α, s))) (hV : MemLp V 2 (νR(α, s))) :
    toDirichletStrip α s U hU = toDirichletStrip α s V hV := by
  subst h
  rfl

/-- The next-stage denominator `D'` of `primaryDivisorialAbsolutePW_quotient_bounds`: box tests
whose `T`-principal-value class lies in the theta stage of `Tp`. -/
def ratProjDenom (S : Finset Vℚ) (ω₁ : PontryaginDual C₁ℚ) (T Tp : Finset Vℚ) (X : ℝ) :
    Submodule ℂ (primaryDivisorialAbsolutePWTests (F := ℚ) S X) :=
  (divisorialThetaStage ω₁ Tp).comap
    ((divisorialThetaRepresentative ω₁ T).domRestrict
      (primaryDivisorialAbsolutePWTests (F := ℚ) S X))

/-- The closed project next-stage space: the closure of the half-twisted theta images of the
principal values `PV_T` of the denominator `D'`. -/
def ratProjNextStage (S : Finset Vℚ) (ω₁ : PontryaginDual C₁ℚ) {α s : ℝ}
    (j : P₀ℚ →ₗ[ℂ] QStrip(α, s)) (T Tp : Finset Vℚ) (X : ℝ) : Submodule ℂ (QStrip(α, s)) :=
  ((ratProjDenom S ω₁ T Tp X).map ((j.comp (adelePolarPrincipalValue T)).comp
    (primaryDivisorialAbsolutePWTests (F := ℚ) S X).subtype)).topologicalClosure

private theorem deplete_step_insert (χ : DirichletCharacter ℂ N) (T : Finset ℕ) {p : ℕ}
    (hp : 0 < p) (hpT : p ∉ T) (g₀ : 𝓢(ℝ, ℂ)) :
    dirichletDeplete χ T (twistedHalfLogProfile χ (testDepleteStep χ p g₀)) =
      dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀) := by
  have hstepU : twistedHalfLogProfile χ (testDepleteStep χ p g₀) =
      depleteStepFun χ p (twistedHalfLogProfile χ g₀) := by
    have h1 := twistedHalfLogProfile_dirichletTestDeplete χ {p} (fun q hq ↦ by
      rw [Finset.mem_singleton.mp hq]; exact hp) g₀
    rw [show dirichletTestDeplete χ {p} = testDepleteStep χ p from
      Finset.noncommProd_singleton _ _] at h1
    rw [h1, show ({p} : Finset ℕ) = insert p ∅ from rfl, dirichletDeplete_insert χ
      (Finset.notMem_empty p), dirichletDeplete_empty, LinearMap.comp_id]
  have hcomm : Commute (depleteStepFun χ p) (dirichletDeplete χ T) :=
    Finset.noncommProd_commute _ _ _ _ fun q _ ↦ depleteStepFun_comm χ p q
  rw [hstepU, dirichletDeplete_insert χ hpT, LinearMap.comp_apply, ← mul_apply_eq_comp,
    ← hcomm.eq, mul_apply_eq_comp]

open Classical in
/-- Paper: (11.3.1.3), p. 494, over `ℚ`.
**Deliverable 1, second part.** With `Tp = insert v T` (`v ∉ T`, `p = pr v ∤ N`), the closure of
the half-twisted theta images of `PV_T` of the denominator `D'` (box tests whose `PV_T` class lies
in the theta stage of `Tp`) is the image of the next rational stage space
`dirichletStageSpace χ (insert p T') X_rat` under the strip embedding.
Deviation: as in the first part, `mass` is absorbed and the identification is `ratStripEmbed ω`. -/
theorem ratBridge_stage_eq_next (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ} (hα : 0 ≤ α)
    (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j) (T : Finset Vℚ)
    (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T) (hv : (pr v).Coprime N) {X : ℝ}
    (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X) :
    ratProjNextStage Sχ ω j T (insert v T) X =
      (dirichletStageSpace χ (insert (pr v) (T.image pr))
        (ratDirichletBoxShift N X * ∏ q ∈ T.image pr, (q : ℝ)) α s hα hs).map
          (ratStripEmbed ω α s).toLinearMap := by
  have hprod := ratPrimes_prod_pos T
  have hR := ratDirichletBoxShift_pos hN hX
  have hT' := ratPrimes_spec T hT
  have hTpos : ∀ q ∈ T.image pr, 0 < q := fun q hq ↦ (hT' q hq).1.pos
  have hpT : pr v ∉ T.image pr := fun h ↦ by
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp h
    exact hvT (pr_injective hwv ▸ hw)
  have hTp : ∀ w ∈ insert v T, (pr w).Coprime N := fun w hw ↦ by
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hv
    · exact hT w hw
  have himg : (insert v T).image pr = insert (pr v) (T.image pr) := Finset.image_insert _ _ _
  have hXr : 0 < ratDirichletBoxShift N X * ∏ q ∈ T.image pr, (q : ℝ) := mul_pos hR hprod
  have hdiv : (ratDirichletBoxShift N X * ∏ q ∈ T.image pr, (q : ℝ)) / ∏ q ∈ T.image pr, (q : ℝ) =
      ratDirichletBoxShift N X := mul_div_cancel_right₀ _ hprod.ne'
  have hstage : divisorialThetaStage ω (insert v T) =
      (divisorialThetaRepresentative ω (insert v T)).range :=
    Submodule.span_eq (divisorialThetaRepresentative ω (insert v T)).range
  apply le_antisymm
  · refine Submodule.topologicalClosure_minimal _ ?_
      (isClosed_map_ratStripEmbed ω _ (isClosed_dirichletStageSpace χ _ _ α s hα hs))
    rintro _ ⟨f, hf, rfl⟩
    have hf' : divisorialThetaRepresentative ω T f.val ∈ divisorialThetaStage ω (insert v T) := hf
    rw [hstage] at hf'
    obtain ⟨h, hh⟩ := hf'
    have hΘ := (divisorialThetaRepresentative_eq_iff ω _ _ h f.val).mp hh
    obtain ⟨f₀, hbox, hgf⟩ := ratBridge_dirichlet_isotypic hχ hN hX f.val f.property
    obtain ⟨g₁, -, hg₁⟩ := ratBridge_dirichlet_isotypic_unrestricted hχ hN h.val
    have hmem := dirichletDeplete_memLp hχ hN (T.image pr) hTpos hR hα hs hbox (α := α) (s := s)
    have hbox' : IsDirichletFixedBoxTest χ
        ((ratDirichletBoxShift N X * ∏ q ∈ T.image pr, (q : ℝ)) / ∏ q ∈ T.image pr, (q : ℝ))
        f₀ := by
      rw [hdiv]; exact hbox
    -- the thetas of `h` and `dirTest g₁` agree, hence a.e. those of their principal values
    have hhg : homogeneousAdelicTheta ω h.val =ᵐ[μℚ]
        homogeneousAdelicTheta ω
          (⟨dirTest hχ g₁, dirTest_mem_polarSubspace hχ hN g₁⟩ : P₀ℚ).val := by
      refine EventuallyEq.of_eq (funext fun x ↦ ?_)
      rw [← ratNormOnePart_mul x]
      exact hg₁ _ _
    have hpv := homTheta_principalValue_congr_ae ω (insert v T) h _ hhg
    -- the two explicit profiles agree almost everywhere on the idele classes
    let D₁ := dirichletDeplete χ (T.image pr) (twistedHalfLogProfile χ f₀)
    let D₂ := dirichletDeplete χ (insert (pr v) (T.image pr)) (twistedHalfLogProfile χ g₁)
    have hae : ∀ᵐ x ∂μℚ, (D₁ - D₂) (Lℚ x) = 0 := by
      have e1 := homTheta_principalValue_of_mem' hχ hN T hT f.val f.property f₀ hgf
      have e2 := homTheta_principalValue_dirTest' hχ hN (insert v T) hTp g₁
      rw [himg] at e2
      filter_upwards [hpv] with x hx
      change homogeneousAdelicTheta ω (adelePolarPrincipalValue (insert v T) h).val x =
        homogeneousAdelicTheta ω (adelePrincipalValue ℚ (insert v T) (dirTest hχ g₁)) x at hx
      rw [hΘ, e1, e2] at hx
      have hne : ((ω (ratNormOnePart x) : ℂ))⁻¹ * mass * (Real.exp (-(Lℚ x / 2)) : ℂ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (inv_ne_zero (Circle.coe_ne_zero _)) mass_ne_zero')
          (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
      have hx' : ((ω (ratNormOnePart x) : ℂ))⁻¹ * mass * (Real.exp (-(Lℚ x / 2)) : ℂ) *
          (D₁ (Lℚ x) - D₂ (Lℚ x)) = 0 := by
        linear_combination hx
      exact (mul_eq_zero.mp hx').resolve_left hne
    have hc₁ : Continuous D₁ :=
      And.left (isFullLineRapid_dirichletDeplete hχ hN (T.image pr) hTpos f₀)
    have hc₂ : Continuous D₂ :=
      And.left (isFullLineRapid_dirichletDeplete hχ hN (insert (pr v) (T.image pr))
        (fun q hq ↦ by
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact (pr_prime v).pos
          · exact hTpos q hq) g₁)
    have hD := ae_line_of_ae_class (hc₁.sub hc₂) hae
    have hfg : ∀ x, D₁ x = D₂ x := fun x ↦ sub_eq_zero.mp (congrFun hD x)
    have hnext := ratBridge_nextStage_mem_stageSpace hχ hN (T.image pr) hT' (pr_prime v) hv hpT
      hXr hα hs hbox' g₁ hfg hmem
    exact ⟨mass • toDirichletStrip α s _ hmem, Submodule.smul_mem _ _ hnext,
      (halfThetaMap_principalValue_of_mem hχ hN hj T hT f.val f.property f₀ hgf hmem).symm⟩
  · refine (map_topologicalClosure_le' (ratStripEmbed ω α s) _).trans
      (Submodule.topologicalClosure_mono ?_)
    refine (Submodule.map_span_le _ _ _).mpr ?_
    rintro _ ⟨g₀, hbox₀, hmem₀, rfl⟩
    have hp := pr_prime v
    have hbox₁ :
        IsDirichletFixedBoxTest χ (ratDirichletBoxShift N X / ∏ q ∈ {pr v}, (q : ℝ)) g₀ := by
      rw [Finset.prod_singleton]
      rw [Finset.prod_insert hpT] at hbox₀
      rwa [show (ratDirichletBoxShift N X * ∏ q ∈ T.image pr, (q : ℝ)) /
        ((pr v : ℝ) * ∏ q ∈ T.image pr, (q : ℝ)) = ratDirichletBoxShift N X / (pr v : ℝ) by
          field_simp] at hbox₀
    have hbox := isDirichletFixedBoxTest_dirichletTestDeplete {pr v}
      (fun q hq ↦ by rw [Finset.mem_singleton.mp hq]; exact hp.pos) hR.le hbox₁
    rw [show dirichletTestDeplete χ {pr v} = testDepleteStep χ (pr v) from
      Finset.noncommProd_singleton _ _] at hbox
    set f₀ := testDepleteStep χ (pr v) g₀ with hf₀
    have heq := deplete_step_insert χ (T.image pr) hp.pos hpT g₀
    obtain ⟨g, hg, hgf⟩ := ratBridge_dirichlet_isotypic_converse hχ hN hX f₀ hbox.2
    have hmem := dirichletDeplete_memLp hχ hN (T.image pr) hTpos hR hα hs hbox (α := α) (s := s)
    -- `g` lies in the denominator: its class is that of `PV_{Tp} (dirTest g₀)`
    have hgD : (⟨g, hg⟩ : primaryDivisorialAbsolutePWTests (F := ℚ) Sχ X) ∈
        ratProjDenom Sχ ω T (insert v T) X := by
      change divisorialThetaRepresentative ω T g ∈ divisorialThetaStage ω (insert v T)
      rw [hstage]
      refine ⟨⟨dirTest hχ g₀, dirTest_mem_polarSubspace hχ hN g₀⟩,
        (divisorialThetaRepresentative_eq_iff ω _ _ _ _).mpr ?_⟩
      apply ContinuousMap.ext
      intro x
      have e1 := homTheta_principalValue_of_mem' hχ hN T hT g hg f₀ hgf
      have e2 := homTheta_principalValue_dirTest' hχ hN (insert v T) hTp g₀
      rw [himg] at e2
      change homogeneousAdelicTheta ω (adelePrincipalValue ℚ (insert v T) (dirTest hχ g₀)) x =
        homogeneousAdelicTheta ω (adelePolarPrincipalValue T g).val x
      rw [e1, e2, heq]
    refine ⟨mass⁻¹ • ⟨g, hg⟩, Submodule.smul_mem _ _ hgD, ?_⟩
    change j (adelePolarPrincipalValue T (mass⁻¹ • g)) = ratStripEmbed ω α s _
    rw [map_smul, map_smul, halfThetaMap_principalValue_of_mem hχ hN hj T hT g hg f₀ hgf hmem,
      map_smul, smul_smul, inv_mul_cancel₀ mass_ne_zero', one_smul,
      toDirichletStrip_congr' heq hmem hmem₀]

end Stage


/-! ### Deliverable 2: the completed quotient and the isomorphism -/

section Quotient

local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "P₀ℚ" => ↥(adelePolarSubspace ℚ)

private theorem norm_sq_Lp_eq_integral {β : Type*} [MeasurableSpace β] {ν : Measure β}
    (u : Lp ℂ 2 ν) : ‖u‖ ^ 2 = ∫ a, ‖u a‖ ^ 2 ∂ν := by
  rw [← @real_inner_self_eq_norm_sq (Lp ℂ 2 ν), L2.inner_def]
  exact integral_congr_ae (.of_forall fun a ↦ real_inner_self_eq_norm_sq _)

/-- The half-twisted strip norm `primaryDivisorialStripNorm (1/2 - α) (1/2 + α) s` of
`Sec3_FixedBox` is the norm of the half-twisted theta image. -/
theorem stripNorm_eq_norm_halfThetaMap (ω₁ : PontryaginDual C₁ℚ) {α s : ℝ}
    {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω₁ j) (φ : P₀ℚ) :
    primaryDivisorialStripNorm (1 / 2 - α) (1 / 2 + α) s ω₁ φ = ‖j φ‖ := by
  have hdm : Measurable fun x : Cℚ ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (Lℚ x)) :=
    ENNReal.measurable_ofReal.comp ((measurable_intervalSobolevDensity _ _ _).comp
      measurable_logNormℚ)
  have key : ‖j φ‖ ^ 2 = ∫ x, ‖homogeneousAdelicTheta ω₁ φ.val x‖ ^ 2 *
      intervalSobolevDensity (1 / 2 - α) (1 / 2 + α) s (logIdeleClassNorm ℚ x) ∂μℚ := by
    rw [norm_sq_Lp_eq_integral]
    change ∫ a, ‖(j φ : QStrip(α, s)) a‖ ^ 2 ∂((ideleClassTamagawaMeasure ℚ).withDensity
      fun x ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (Lℚ x))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hdm (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    refine integral_congr_ae ?_
    filter_upwards [hj φ] with x hx
    have hpos : (0 : ℝ) < ((ideleClassNorm ℚ x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    rw [hx, ENNReal.toReal_ofReal (intervalSobolevDensity_pos _ _ _ _).le, smul_eq_mul, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _), mul_pow,
      Real.rpow_def_of_pos hpos, sub_eq_add_neg (1 / 2 : ℝ) α,
      ← globalThetaSobolev_norm_density (1 / 2) (-α) α s]
    simp only [logIdeleClassNorm]
    rw [show Real.log ((ideleClassNorm ℚ x).val : ℝ) * (1 / 2) =
      1 / 2 * Real.log ((ideleClassNorm ℚ x).val : ℝ) by ring]
    ring
  rw [primaryDivisorialStripNorm, ← key, Real.sqrt_sq (norm_nonneg _)]

/-- The completed project quotient, realized in the strip space: the orthogonal complement of the
closed next-stage space `ratProjNextStage` inside the closed stage space `ratProjStage`. -/
def ratProjQuot (S : Finset Vℚ) (ω₁ : PontryaginDual C₁ℚ) {α s : ℝ}
    (j : P₀ℚ →ₗ[ℂ] QStrip(α, s)) (T Tp : Finset Vℚ) (X : ℝ) : Submodule ℂ (QStrip(α, s)) :=
  ratProjStage S j T X ⊓ (ratProjNextStage S ω₁ j T Tp X)ᗮ

instance instHasOrthogonalProjectionRatProjNextStage (S : Finset Vℚ) (ω₁ : PontryaginDual C₁ℚ)
    {α s : ℝ} (j : P₀ℚ →ₗ[ℂ] QStrip(α, s)) (T Tp : Finset Vℚ) (X : ℝ) :
    (ratProjNextStage S ω₁ j T Tp X).HasOrthogonalProjection := by
  unfold ratProjNextStage
  infer_instance

/-- The map from box tests to the completed quotient: project the half-twisted theta image of the
principal value orthogonally away from the next stage. -/
def ratProjQuotMap (S : Finset Vℚ) (ω₁ : PontryaginDual C₁ℚ) {α s : ℝ}
    (j : P₀ℚ →ₗ[ℂ] QStrip(α, s)) (T Tp : Finset Vℚ) (X : ℝ)
    (f : primaryDivisorialAbsolutePWTests (F := ℚ) S X) : QStrip(α, s) :=
  (ratProjNextStage S ω₁ j T Tp X)ᗮ.starProjection (j (adelePolarPrincipalValue T f.val))

theorem ratProjNextStage_le (S : Finset Vℚ) (ω₁ : PontryaginDual C₁ℚ) {α s : ℝ}
    (j : P₀ℚ →ₗ[ℂ] QStrip(α, s)) (T Tp : Finset Vℚ) (X : ℝ) :
    ratProjNextStage S ω₁ j T Tp X ≤ ratProjStage S j T X := by
  refine Submodule.topologicalClosure_mono ?_
  rintro _ ⟨g, -, rfl⟩
  exact ⟨g.val, g.property, rfl⟩

theorem ratProjQuotMap_mem (S : Finset Vℚ) (ω₁ : PontryaginDual C₁ℚ) {α s : ℝ}
    (j : P₀ℚ →ₗ[ℂ] QStrip(α, s)) (T Tp : Finset Vℚ) (X : ℝ)
    (f : primaryDivisorialAbsolutePWTests (F := ℚ) S X) :
    ratProjQuotMap S ω₁ j T Tp X f ∈ ratProjQuot S ω₁ j T Tp X := by
  refine ⟨?_, Submodule.starProjection_apply_mem _ _⟩
  rw [ratProjQuotMap, Submodule.starProjection_orthogonal_val]
  refine Submodule.sub_mem _ (Submodule.le_topologicalClosure _ ⟨f.val, f.property, rfl⟩) ?_
  exact ratProjNextStage_le S ω₁ j T Tp X (Submodule.starProjection_apply_mem _ _)

/-- Paper: (11.3.1.3), p. 494, over `ℚ`.
**The seminorm `stage` is the norm in the completed quotient.** The seminorm `stage` of
`primaryDivisorialAbsolutePW_quotient_bounds` (the infimum over the denominator `D'` of the
half-twisted strip norm of `PV_T (f - g)`) equals the norm of `ratProjQuotMap f`. -/
theorem ratProjQuotMap_norm (S : Finset Vℚ) (ω₁ : PontryaginDual C₁ℚ) {α s : ℝ}
    {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω₁ j) (T Tp : Finset Vℚ) (X : ℝ)
    (f : primaryDivisorialAbsolutePWTests (F := ℚ) S X) :
    (⨅ g : ratProjDenom S ω₁ T Tp X, primaryDivisorialStripNorm (1 / 2 - α) (1 / 2 + α) s ω₁
      (adelePolarPrincipalValue T (f - g.val).val)) = ‖ratProjQuotMap S ω₁ j T Tp X f‖ := by
  set K := ratProjNextStage S ω₁ j T Tp X
  set x := j (adelePolarPrincipalValue T f.val)
  let J := (j.comp (adelePolarPrincipalValue T)).comp
    (primaryDivisorialAbsolutePWTests (F := ℚ) S X).subtype
  have hterm (g : ratProjDenom S ω₁ T Tp X) :
      primaryDivisorialStripNorm (1 / 2 - α) (1 / 2 + α) s ω₁
        (adelePolarPrincipalValue T (f - g.val).val) = ‖x - J g.val‖ := by
    rw [stripNorm_eq_norm_halfThetaMap ω₁ hj, Submodule.coe_sub, map_sub, map_sub]
    rfl
  simp_rw [hterm]
  rw [ratProjQuotMap, Submodule.starProjection_orthogonal_val, Submodule.starProjection_minimal]
  have hbdd : BddBelow (Set.range fun g : ratProjDenom S ω₁ T Tp X ↦ ‖x - J g.val‖) :=
    ⟨0, by rintro _ ⟨i, rfl⟩; exact norm_nonneg _⟩
  have hbdd' : BddBelow (Set.range fun w : K ↦ ‖x - (w : QStrip(α, s))‖) :=
    ⟨0, by rintro _ ⟨i, rfl⟩; exact norm_nonneg _⟩
  apply le_antisymm
  · refine le_ciInf fun w ↦ ?_
    refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
    have hw : (w : QStrip(α, s)) ∈ closure
        (((ratProjDenom S ω₁ T Tp X).map J : Submodule ℂ _) : Set (QStrip(α, s))) := by
      rw [← Submodule.topologicalClosure_coe]
      exact w.property
    obtain ⟨b, ⟨g, hg, rfl⟩, hb⟩ := Metric.mem_closure_iff.mp hw ε hε
    have h0 : (⨅ g : ratProjDenom S ω₁ T Tp X, ‖x - J g.val‖) ≤ ‖x - J g‖ :=
      ciInf_le hbdd ⟨g, hg⟩
    have h1 := norm_sub_le_norm_sub_add_norm_sub x (w : QStrip(α, s)) (J g)
    have h2 : ‖(w : QStrip(α, s)) - J g‖ < ε := by rw [← dist_eq_norm]; exact hb
    linarith
  · refine le_ciInf fun g ↦ ?_
    exact ciInf_le hbdd' ⟨J g.val, Submodule.le_topologicalClosure _ ⟨g, g.property, rfl⟩⟩

/-- Paper: (11.3.1.3), p. 494, over `ℚ`. The image of the box tests is dense in the completed
quotient; with `ratProjQuotMap_norm`, `ratProjQuot` is the separated completion of the box tests
for the seminorm `stage`. -/
theorem ratProjQuotMap_dense (S : Finset Vℚ) (ω₁ : PontryaginDual C₁ℚ) {α s : ℝ}
    (j : P₀ℚ →ₗ[ℂ] QStrip(α, s)) (T Tp : Finset Vℚ) (X : ℝ) (y : QStrip(α, s))
    (hy : y ∈ ratProjQuot S ω₁ j T Tp X) :
    y ∈ closure (Set.range (ratProjQuotMap S ω₁ j T Tp X)) := by
  set K := ratProjNextStage S ω₁ j T Tp X
  have hyK : Kᗮ.starProjection y = y := (Submodule.starProjection_eq_self_iff).mpr hy.2
  have hy1 : y ∈ closure (((primaryDivisorialAbsolutePWTests (F := ℚ) S X).map
      (j.comp (adelePolarPrincipalValue T)) : Submodule ℂ _) : Set (QStrip(α, s))) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hy.1
  have h2 := image_closure_subset_closure_image (Kᗮ.starProjection.continuous) ⟨y, hy1, hyK⟩
  refine closure_mono ?_ h2
  rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

end Quotient


/-! ### The isomorphism with the rational quotient -/

section QuotIso

local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "P₀ℚ" => ↥(adelePolarSubspace ℚ)

private theorem ratStripEmbed_mem_orthogonal (ω₁ : PontryaginDual C₁ℚ) {α s : ℝ}
    {E : Submodule ℂ (RStrip(α, s))} {b : RStrip(α, s)} (hb : b ∈ Eᗮ) :
    ratStripEmbed ω₁ α s b ∈ (E.map (ratStripEmbed ω₁ α s).toLinearMap)ᗮ := by
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨c, hc, rfl⟩
  change inner ℂ (ratStripEmbed ω₁ α s c) (ratStripEmbed ω₁ α s b) = 0
  rw [inner_ratStripEmbed, Submodule.inner_right_of_mem_orthogonal hc hb, mul_zero]

private theorem mem_orthogonal_of_ratStripEmbed (ω₁ : PontryaginDual C₁ℚ) {α s : ℝ}
    {E : Submodule ℂ (RStrip(α, s))} {U : RStrip(α, s)}
    (h : ratStripEmbed ω₁ α s U ∈ (E.map (ratStripEmbed ω₁ α s).toLinearMap)ᗮ) : U ∈ Eᗮ := by
  rw [Submodule.mem_orthogonal]
  intro c hc
  have h1 := Submodule.inner_right_of_mem_orthogonal
    (⟨c, hc, rfl⟩ : ratStripEmbed ω₁ α s c ∈ E.map (ratStripEmbed ω₁ α s).toLinearMap) h
  rw [inner_ratStripEmbed] at h1
  exact (mul_eq_zero.mp h1).resolve_left (Complex.ofReal_ne_zero.mpr ratMass_pos.ne')

/-- The strip embedding intertwines the orthogonal projections away from a subspace and away from
its image. -/
theorem starProjection_orthogonal_ratStripEmbed (ω₁ : PontryaginDual C₁ℚ) {α s : ℝ}
    (E : Submodule ℂ (RStrip(α, s))) [E.HasOrthogonalProjection] (K : Submodule ℂ (QStrip(α, s)))
    [K.HasOrthogonalProjection] (hK : K = E.map (ratStripEmbed ω₁ α s).toLinearMap)
    (V : RStrip(α, s)) :
    Kᗮ.starProjection (ratStripEmbed ω₁ α s V) = ratStripEmbed ω₁ α s (Eᗮ.starProjection V) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal'
    (z := ratStripEmbed ω₁ α s (E.starProjection V)) ?_ ?_ ?_
  · rw [hK]
    exact ratStripEmbed_mem_orthogonal ω₁ (Submodule.starProjection_apply_mem _ _)
  · refine K.le_orthogonal_orthogonal ?_
    rw [hK]
    exact ⟨_, Submodule.starProjection_apply_mem _ _, rfl⟩
  · rw [← map_add, add_comm, Submodule.starProjection_add_starProjection_orthogonal]

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

set_option hygiene false in
local notation "ω" => ratDirichletNormOneChar hχ
local notation "Sχ" => ratDirichletS N
local notation "mass" => ((normOneIdeleClassTamagawaMeasure ℚ Set.univ).toReal : ℂ)
local notation "Xr(" X ", " T ")" => ratDirichletBoxShift N X * ∏ q ∈ Finset.image pr T, (q : ℝ)

open Classical in
/-- The scaled strip embedding maps the rational quotient into the completed project quotient. -/
theorem ratBridge_quot_mem (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ} (hα : 0 ≤ α)
    (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j) (T : Finset Vℚ)
    (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T) (hv : (pr v).Coprime N) {X : ℝ}
    (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X) (U : RStrip(α, s))
    (hU : U ∈ dirichletStageQuotient χ (T.image pr) (pr v) Xr(X, T) α s hα hs) :
    mass • ratStripEmbed ω α s U ∈ ratProjQuot Sχ ω j T (insert v T) X := by
  refine Submodule.smul_mem _ _ ⟨?_, ?_⟩
  · rw [ratBridge_stage_eq_first hχ hN hα hs hj T hT hX]
    exact ⟨U, hU.1, rfl⟩
  · rw [ratBridge_stage_eq_next hχ hN hα hs hj T hT hvT hv hX]
    exact ratStripEmbed_mem_orthogonal ω hU.2

open Classical in
private theorem ratBridge_quot_surj (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ} (hα : 0 ≤ α)
    (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j) (T : Finset Vℚ)
    (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T) (hv : (pr v).Coprime N) {X : ℝ}
    (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X) (y : QStrip(α, s))
    (hy : y ∈ ratProjQuot Sχ ω j T (insert v T) X) :
    ∃ U ∈ dirichletStageQuotient χ (T.image pr) (pr v) Xr(X, T) α s hα hs,
      mass • ratStripEmbed ω α s U = y := by
  obtain ⟨hy1, hy2⟩ := hy
  rw [ratBridge_stage_eq_first hχ hN hα hs hj T hT hX] at hy1
  rw [ratBridge_stage_eq_next hχ hN hα hs hj T hT hvT hv hX] at hy2
  obtain ⟨U, hU, rfl⟩ := hy1
  refine ⟨mass⁻¹ • U, Submodule.smul_mem _ _ ⟨hU, mem_orthogonal_of_ratStripEmbed ω hy2⟩, ?_⟩
  change mass • ratStripEmbed ω α s (mass⁻¹ • U) = ratStripEmbed ω α s U
  rw [map_smul, smul_smul, mul_inv_cancel₀ mass_ne_zero', one_smul]

open Classical in
/-- The scaled strip embedding `U ↦ mass • ι U` from the rational quotient onto the completed
project quotient, as a linear map. -/
def ratBridgeQuotLinearMap (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ} (hα : 0 ≤ α)
    (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j) (T : Finset Vℚ)
    (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T) (hv : (pr v).Coprime N) {X : ℝ}
    (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X) :
    dirichletStageQuotient χ (T.image pr) (pr v) Xr(X, T) α s hα hs →ₗ[ℂ]
      ratProjQuot Sχ ω j T (insert v T) X :=
  ((mass • (ratStripEmbed ω α s).toLinearMap).comp
    (dirichletStageQuotient χ (T.image pr) (pr v) Xr(X, T) α s hα hs).subtype).codRestrict _
    fun U ↦ ratBridge_quot_mem hχ hN hα hs hj T hT hvT hv hX U.1 U.2

open Classical in
/-- The scaled strip embedding is a bijection between the quotients. -/
theorem ratBridgeQuotLinearMap_bijective (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j)
    (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T)
    (hv : (pr v).Coprime N) {X : ℝ} (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X) :
    Bijective (ratBridgeQuotLinearMap hχ hN hα hs hj T hT hvT hv hX) := by
  refine ⟨fun U U' h ↦ ?_, fun y ↦ ?_⟩
  · have h' : mass • ratStripEmbed ω α s U.1 = mass • ratStripEmbed ω α s U'.1 :=
      congrArg Subtype.val h
    exact Subtype.ext (ratStripEmbed_injective ω α s (smul_right_injective _ mass_ne_zero' h'))
  · obtain ⟨U, hU, hUy⟩ := ratBridge_quot_surj hχ hN hα hs hj T hT hvT hv hX y.1 y.2
    exact ⟨⟨U, hU⟩, Subtype.ext hUy⟩

open Classical in
/-- The scaled strip embedding multiplies norms by `mass^{3/2}`. -/
theorem norm_ratBridgeQuotLinearMap (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j)
    (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T)
    (hv : (pr v).Coprime N) {X : ℝ} (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X)
    (U : dirichletStageQuotient χ (T.image pr) (pr v) Xr(X, T) α s hα hs) :
    ‖ratBridgeQuotLinearMap hχ hN hα hs hj T hT hvT hv hX U‖ =
      massℝ * Real.sqrt massℝ * ‖U‖ := by
  change ‖mass • ratStripEmbed ω α s U.1‖ = _
  rw [norm_smul, norm_ratStripEmbed, Complex.norm_real, Real.norm_of_nonneg ratMass_pos.le,
    mul_assoc]
  rfl

open Classical in
/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496, over `ℚ`.
**Deliverable 2: the quotient isomorphism.** The completed project quotient `ratProjQuot` (the
separated completion of the box tests for the seminorm `stage`, see `ratProjQuotMap_norm` and
`ratProjQuotMap_dense`) is isomorphic to `dirichletStageQuotient χ T' p X_rat`; the inverse is
`U ↦ mass • ratStripEmbed ω U`, and the isomorphism divides norms by `mass^{3/2}`
(`norm_ratBridge_dirichlet_quotient_iso`). -/
def ratBridge_dirichlet_quotient_iso (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j)
    (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T)
    (hv : (pr v).Coprime N) {X : ℝ} (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X) :
    ratProjQuot Sχ ω j T (insert v T) X ≃L[ℂ]
      dirichletStageQuotient χ (T.image pr) (pr v) Xr(X, T) α s hα hs :=
  let e := LinearEquiv.ofBijective _
    (ratBridgeQuotLinearMap_bijective hχ hN hα hs hj T hT hvT hv hX)
  have hc : 0 < massℝ * Real.sqrt massℝ := mul_pos ratMass_pos (Real.sqrt_pos.mpr ratMass_pos)
  have he (U : dirichletStageQuotient χ (T.image pr) (pr v) Xr(X, T) α s hα hs) :
      ‖e U‖ = massℝ * Real.sqrt massℝ * ‖U‖ :=
    norm_ratBridgeQuotLinearMap hχ hN hα hs hj T hT hvT hv hX U
  (e.toContinuousLinearEquivOfBounds (massℝ * Real.sqrt massℝ) (massℝ * Real.sqrt massℝ)⁻¹
    (fun U ↦ (he U).le) (fun y ↦ by
      have h1 := he (e.symm y)
      rw [LinearEquiv.apply_symm_apply] at h1
      rw [h1, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul])).symm

open Classical in
/-- The inverse of the quotient isomorphism is the scaled strip embedding. -/
theorem ratBridge_dirichlet_quotient_iso_symm_apply (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j)
    (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T)
    (hv : (pr v).Coprime N) {X : ℝ} (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X)
    (U : dirichletStageQuotient χ (T.image pr) (pr v) Xr(X, T) α s hα hs) :
    ((ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX).symm U : QStrip(α, s)) =
      mass • ratStripEmbed ω α s U :=
  rfl

open Classical in
/-- The quotient isomorphism divides norms by `mass^{3/2}`. -/
theorem norm_ratBridge_dirichlet_quotient_iso (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j)
    (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T)
    (hv : (pr v).Coprime N) {X : ℝ} (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X)
    (y : ratProjQuot Sχ ω j T (insert v T) X) :
    ‖y‖ = massℝ * Real.sqrt massℝ *
      ‖ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX y‖ := by
  set Φ := ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX
  have h := norm_ratBridgeQuotLinearMap hχ hN hα hs hj T hT hvT hv hX (Φ y)
  have h2 : ratBridgeQuotLinearMap hχ hN hα hs hj T hT hvT hv hX (Φ y) = y := Φ.symm_apply_apply y
  rw [h2] at h
  exact h

open Classical in
/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496, over `ℚ`. On a box test `f` whose theta is that
of the Dirichlet test `dirTest f₀` (`f₀` in the box `R(X)`), the quotient isomorphism sends the
class of `f` to the rational quotient class of the depleted profile of `f₀`. -/
theorem ratBridge_dirichlet_quotient_iso_quotMap (hχ : χ.IsPrimitive) (hN : 1 < N) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) {j : P₀ℚ →ₗ[ℂ] QStrip(α, s)} (hj : IsRatHalfThetaMap ω j)
    (T : Finset Vℚ) (hT : ∀ v ∈ T, (pr v).Coprime N) {v : Vℚ} (hvT : v ∉ T)
    (hv : (pr v).Coprime N) {X : ℝ} (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X)
    (f : primaryDivisorialAbsolutePWTests (F := ℚ) Sχ X) (f₀ : 𝓢(ℝ, ℂ))
    (hgf : ∀ (t : ℝ≥0ˣ) (k : C₁ℚ), homogeneousAdelicTheta ω f.val.val (k.val * ratNormSection t) =
      homogeneousAdelicTheta ω (dirTest hχ f₀) (k.val * ratNormSection t))
    (hmem : MemLp (dirichletDeplete χ (T.image pr) (twistedHalfLogProfile χ f₀)) 2 (νR(α, s)))
    (hE : toDirichletStrip α s _ hmem ∈ dirichletStageSpace χ (T.image pr) Xr(X, T) α s hα hs) :
    ratBridge_dirichlet_quotient_iso hχ hN hα hs hj T hT hvT hv hX
        ⟨ratProjQuotMap Sχ ω j T (insert v T) X f, ratProjQuotMap_mem _ _ _ _ _ _ f⟩ =
      dirichletStageQuotMap hχ hN (T.image pr) (ratPrimes_spec T hT) (pr_prime v)
        (fun h ↦ by
          obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp h
          exact hvT (pr_injective hwv ▸ hw))
        (mul_pos (ratDirichletBoxShift_pos hN hX) (ratPrimes_prod_pos T)) hα hs
        ⟨toDirichletStrip α s _ hmem, hE⟩ := by
  refine (ContinuousLinearEquiv.eq_symm_apply _).mp (Subtype.ext ?_)
  rw [ratBridge_dirichlet_quotient_iso_symm_apply, coe_dirichletStageQuotMap]
  change ratProjQuotMap Sχ ω j T (insert v T) X f = _
  rw [ratProjQuotMap,
    halfThetaMap_principalValue_of_mem hχ hN hj T hT f.val f.property f₀ hgf hmem, map_smul,
    map_smul, starProjection_orthogonal_ratStripEmbed ω _ _
      (ratBridge_stage_eq_next hχ hN hα hs hj T hT hvT hv hX)]

end QuotIso

end RiemannMasullo.Isolated
