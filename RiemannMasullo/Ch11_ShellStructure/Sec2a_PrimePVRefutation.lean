module

public import RiemannMasullo.Ch11_ShellStructure.Sec2a
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-! # Approximate invariants for the printed principal-value range claims -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal ENNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "RatC" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "RatC₁" => (ideleClassNorm ℚ).ker
local notation "RatV" => HeightOneSpectrum (𝓞 ℚ)
local notation "ratμ" => ideleClassTamagawaMeasure ℚ
local notation "ratLogNorm" => (fun g : RatC ↦ Real.log ((ideleClassNorm ℚ g).val : ℝ))
local notation "RatW" => CompactIntervalSobolev ratμ ratLogNorm 0 0 2
local notation "ratTranslation(" hs ")" =>
  hardySobolevTranslation ratμ
    (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ : RatC →ₜ* ℝ≥0ˣ)
    0 0 2 (le_rfl (a := (0 : ℝ))) hs
local notation "RatE(" hs ")" =>
  actionIsotype ((ratTranslation(hs)).comp (ideleClassNorm ℚ).ker.subtype)
    (1 : PontryaginDual RatC₁)
local notation "hI" => (le_rfl (a := (0 : ℝ)))
local notation "RatH(" hs ")" => globalThetaSobolev ℚ 0 (le_rfl (a := (0 : ℝ))) hs

local notation "ratNormMap" =>
  (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ : RatC →ₜ* ℝ≥0ˣ)

-- The normalization is the one used for the orbital jets in §11.2.0.
private theorem ratPrimePV_logNorm_continuous :
    Continuous (fun g : RatC ↦ ratLogNorm g) :=
  Real.continuousOn_log.comp_continuous
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (ratNormMap).continuous))
    fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'

private theorem ratPrimePV_log_positiveRealHaar :
    Measure.map (fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) positiveRealHaar = volume := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have hlogt : Measurable (fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) :=
    (Real.continuousOn_log.comp_continuous (NNReal.continuous_coe.comp Units.continuous_val)
      fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne').measurable
  unfold positiveRealHaar
  have hexp : Measurable (fun x : ℝ ↦
      Units.mk0 (Real.exp x).toNNReal
        (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))) :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  rw [Measure.map_map hlogt hexp]
  have hid : ((fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) ∘ fun x : ℝ ↦
      Units.mk0 (Real.exp x).toNNReal
        (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))) = id := by
    funext x
    change Real.log ((Real.exp x).toNNReal : ℝ) = x
    rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]
  rw [hid, Measure.map_id]

private theorem ratPrimePV_logNorm_measurePreserving :
    MeasurePreserving (fun g : RatC ↦ ratLogNorm g)
      (canonicalModulatedHaar ratNormMap
        (⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩ : IsModulation ratNormMap))
      volume := by
  have hm : IsModulation ratNormMap := ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
  obtain ⟨τ, hτc, hτ⟩ := (ideleGroup_quotient.{_, 0} ℚ).2.2.2.2.2.2.2.2.2.2.1
  let τ' : ℝ≥0ˣ →ₜ* RatC := ⟨τ, hτc⟩
  let : CompactSpace (ratNormMap).toMonoidHom.ker :=
    isCompact_iff_compactSpace.mp (IsModulation.isCompact_ker hm)
  let μ₁ : Measure (ratNormMap).toMonoidHom.ker := Measure.haarMeasure ⊤
  let : IsProbabilityMeasure μ₁ := ⟨Measure.haarMeasure_self⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  refine ⟨ratPrimePV_logNorm_continuous.measurable, ?_⟩
  rw [canonicalModulatedHaar_eq_map_prod ratNormMap hm τ' hτ μ₁ Measure.haarMeasure_self]
  have hsplit_meas : Measurable (fun z : (ratNormMap).toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : RatC) * τ' z.2) :=
    ((continuous_subtype_val.comp continuous_fst).mul (τ'.continuous.comp continuous_snd)).measurable
  rw [Measure.map_map ratPrimePV_logNorm_continuous.measurable hsplit_meas]
  have hcomp : ((fun g : RatC ↦ ratLogNorm g) ∘ fun z : (ratNormMap).toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : RatC) * τ' z.2) =
      (fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) ∘ Prod.snd := by
    funext ⟨k, t⟩
    change Real.log ((ideleClassNorm ℚ ((k : RatC) * τ t)).val : ℝ) = Real.log ((t.val : ℝ≥0) : ℝ)
    have hk : ideleClassNorm ℚ (k : RatC) = 1 := k.property
    rw [map_mul, hk, one_mul, hτ t]
  have hlogt : Measurable (fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) :=
    (Real.continuousOn_log.comp_continuous (NNReal.continuous_coe.comp Units.continuous_val)
      fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne').measurable
  rw [hcomp, ← Measure.map_map hlogt measurable_snd,
    (measurePreserving_snd (μ := μ₁) (ν := positiveRealHaar)).map_eq]
  exact ratPrimePV_log_positiveRealHaar

/-- The log-radial exponential is square-integrable for the degree-two weight. -/
private theorem pvApprox_exp_integrable {ε : ℝ} (he : 0 < ε) :
    Integrable (fun x : ℝ ↦ Real.exp (-2 * ε * |x|) * (1 + x ^ 2)) := by
  let p (x : ℝ) := Real.exp (-2 * ε * x) * (1 + x ^ 2)
  have h₀ := integrableOn_exp_mul_Ioi (show -2 * ε < 0 by linarith) 0
  have h₂ := integrableOn_rpow_mul_exp_neg_mul_rpow (show -1 < (2 : ℝ) by norm_num)
    (show 0 < (1 : ℝ) by norm_num) (show 0 < 2 * ε by positivity)
  have hp : IntegrableOn p (Ioi 0) := by
    refine (h₀.add h₂).congr_fun (fun x _ ↦ ?_) measurableSet_Ioi
    simp only [Pi.add_apply, Real.rpow_two, Real.rpow_one, p, neg_mul]
    ring
  have hpos : IntegrableOn (fun x ↦ p |x|) (Ioi 0) :=
    hp.congr_fun (fun x hx ↦ by rw [abs_of_pos hx]) measurableSet_Ioi
  have hneg : IntegrableOn (fun x ↦ p |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ ↦ -x) := (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, neg_preimage, neg_Iic, neg_zero]
    apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
    exact hpos.congr_fun (fun x _ ↦ congrArg p (abs_neg x).symm) measurableSet_Ioi
  simpa [p, sq_abs] using hpos.union hneg

/-- The relative change of the log-radial exponential is uniformly small under a fixed translation. -/
private theorem pvApprox_exp_translate (ε a x : ℝ) (he : 0 ≤ ε) :
    |Real.exp (-ε * |x|) - Real.exp (-ε * |x - a|)| ≤
      (Real.exp (ε * |a|) - 1) * Real.exp (-ε * |x|) := by
  have ha : abs (|x| - |x - a|) ≤ |a| := by simpa using abs_abs_sub_abs_le_abs_sub x (x - a)
  have h1 : Real.exp (-ε * |x|) ≤ Real.exp (ε * |a|) * Real.exp (-ε * |x - a|) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_left (abs_le.mp ha).1 he]
  have h2 : Real.exp (-ε * |x - a|) ≤ Real.exp (ε * |a|) * Real.exp (-ε * |x|) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_left (abs_le.mp ha).2 he]
  have h3 : 0 ≤ Real.exp (ε * |a|) - 1 := sub_nonneg.mpr (Real.one_le_exp (mul_nonneg he (abs_nonneg _)))
  rcases le_total (Real.exp (-ε * |x|)) (Real.exp (-ε * |x - a|)) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact (show _ ≤ (Real.exp (ε * |a|) - 1) * Real.exp (-ε * |x - a|) by linarith).trans
      (mul_le_mul_of_nonneg_left h h3)

/-- The degree-two space contains nonzero, norm-one invariant vectors with arbitrarily small relative translation error. -/
private theorem pvApprox_radial (hs : (0 : ℝ) ≤ 2) (ε : ℝ) (he : 0 < ε) (a : RatC) :
    ∃ u : RatW, u ≠ 0 ∧ u ∈ RatE(hs) ∧
      ‖u - ratTranslation(hs) a u‖ ≤ (Real.exp (ε * |ratLogNorm a|) - 1) * ‖u‖ := by
  let m : RatC →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩
  let hm : IsModulation m := ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
  let ν := canonicalModulatedHaar m hm
  have : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m hm).exists.choose_spec.1
  let l := ratLogNorm
  let f (x : RatC) : ℂ := Real.exp (-ε * |l x|)
  let d (x : RatC) := intervalSobolevDensity 0 0 2 (l x)
  let μw := (ratμ).withDensity (fun x ↦ ENNReal.ofReal (d x))
  have hd (x : RatC) : d x = 1 + l x ^ 2 := by norm_num [d, intervalSobolevDensity]
  have hdc : Continuous d := by
    simp_rw [show d = fun x ↦ 1 + l x ^ 2 from funext hd]
    exact continuous_const.add ((ratPrimePV_logNorm_continuous).pow 2)
  have hfc : Continuous f := Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul (ratPrimePV_logNorm_continuous).abs))
  have hν : Integrable (fun g ↦ Real.exp (-2 * ε * |l g|) * (1 + l g ^ 2)) ν :=
    (ratPrimePV_logNorm_measurePreserving).integrable_comp_of_integrable
      (pvApprox_exp_integrable he)
  have hμ : Integrable (fun g ↦ Real.exp (-2 * ε * |l g|) * (1 + l g ^ 2)) (ratμ) := by
    rw [Measure.isMulLeftInvariant_eq_smul (ratμ) ν]
    exact hν.smul_measure_nnreal
  have hmem : MemLp f 2 μw := by
    apply (memLp_two_iff_integrable_sq_norm hfc.aestronglyMeasurable).2
    apply (integrable_withDensity_iff hdc.measurable.ennreal_ofReal (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).2
    refine hμ.congr (.of_forall fun x ↦ ?_)
    change _ = ‖(Real.exp (-ε * |l x|) : ℂ)‖ ^ 2 * (ENNReal.ofReal (d x)).toReal
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, sq, ← Real.exp_add, hd,
      ENNReal.toReal_ofReal (by positivity)]
    change Real.exp (-2 * ε * |l x|) * _ = _
    rw [show -2 * ε * |l x| = -ε * |l x| + -ε * |l x| by ring]
  let u : RatW := hmem.toLp f
  have hu : (u : RatC → ℂ) =ᵐ[μw] f := MemLp.coeFn_toLp _
  have hpos (x : RatC) : 0 < d x := hd x ▸ by positivity
  have hbase : (u : RatC → ℂ) =ᵐ[ratμ] f := by
    have h := (ae_withDensity_iff hdc.measurable.ennreal_ofReal).mp hu
    filter_upwards [h] with x hx using hx (ENNReal.ofReal_pos.mpr (hpos x)).ne'
  have htr (g : RatC) : (ratTranslation(hs) g u : RatC → ℂ) =ᵐ[μw] fun x ↦ f (g⁻¹ * x) :=
    (withDensity_absolutelyContinuous _ _).ae_le
      ((hardySobolevTranslation_apply (ratμ) m 0 0 2 le_rfl hs g u).trans
        ((measurePreserving_mul_left (ratμ) g⁻¹).quasiMeasurePreserving.ae_eq_comp hbase))
  have hlog (g x : RatC) : l (g⁻¹ * x) = l x - l g := by
    dsimp only [l]
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv,
      Real.log_mul (inv_ne_zero (NNReal.coe_pos.mpr (Units.zero_lt _)).ne') (NNReal.coe_pos.mpr (Units.zero_lt _)).ne', Real.log_inv]
    ring
  refine ⟨u, ?_, ?_, ?_⟩
  · intro h
    have hzero : (u : RatC → ℂ) =ᵐ[μw] 0 := Lp.eq_zero_iff_ae_eq_zero.mp h
    have hzero' := (ae_withDensity_iff hdc.measurable.ennreal_ofReal).mp hzero
    have hboth : ∀ᵐ x ∂(ratμ), f x = 0 := by
      filter_upwards [hbase, hzero'] with x hx hy using hx.symm.trans (hy (ENNReal.ofReal_pos.mpr (hpos x)).ne')
    obtain ⟨x, hx⟩ := hboth.exists
    exact (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') hx
  · apply (mem_actionIsotype _ _ _).mpr
    intro k
    change ratTranslation(hs) k.val u = (1 : ℂ) • u
    rw [one_smul]
    apply Lp.ext
    filter_upwards [htr k.val, hu] with x hx hy
    rw [hx, hy]
    change ((Real.exp (-ε * |l (k.val⁻¹ * x)|) : ℝ) : ℂ) = _
    rw [hlog, show l k.val = 0 by simp [l, MonoidHom.mem_ker.mp k.property], sub_zero]
  · apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub u (ratTranslation(hs) a u), htr a, hu] with x h₁ h₂ h₃
    rw [h₁]
    change ‖u x - ratTranslation(hs) a u x‖ ≤ _
    rw [h₂, h₃]
    change ‖(Real.exp (-ε * |l x|) : ℂ) - (Real.exp (-ε * |l (a⁻¹ * x)|) : ℂ)‖ ≤ _
    rw [hlog, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    change _ ≤ (Real.exp (ε * |l a|) - 1) * ‖((Real.exp (-ε * |l x|) : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact pvApprox_exp_translate ε (l a) (l x) he.le

/-- The zero-line ambient vectors all belong to the global theta completion. -/
private theorem pvApprox_global_eq_top (hs : (0 : ℝ) ≤ 2) :
    globalThetaSobolev ℚ 0 hI hs = ⊤ := by
  apply (Submodule.dense_iff_topologicalClosure_eq_top).mp
  refine (denseRange_globalTheta_zeroLine (F := ℚ) hs).mono ?_
  rintro _ ⟨u, rfl⟩
  exact ⟨u, rfl⟩


open Filter in
open scoped Topology in
/-- Choose a positive exponent so that the relative norm error is small. -/
private theorem pvApprox_choose_exponent (K L : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ K * (Real.exp (ε * |L|) - 1) < 1 := by
  let c (ε : ℝ) := Real.exp (ε * |L|) - 1
  have hc_lim : Tendsto (fun ε : ℝ ↦ K * c ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun ε : ℝ ↦ K * c ε) := by
      unfold c
      fun_prop
    apply (hcont.tendsto' 0 0 ?_).mono_left nhdsWithin_le_nhds
    simp [c]
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hsmall_eventually : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), K * c ε < 1 :=
    hc_lim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  exact (hpos.and hsmall_eventually).exists


/-- The rational trivial isotype at degree two contains nonzero approximate
invariants for each fixed translation. -/
private theorem exists_ratDegreeTwo_approxInvariant (hs : (0 : ℝ) ≤ 2) (a : RatC)
    (K : ℝ≥0) :
    ∃ u : RatW, u ∈ RatE(hs) ∧
      (K : ℝ) * ‖u - ratTranslation(hs) a u‖ < ‖u‖ := by
  let c (ε : ℝ) := Real.exp (ε * |ratLogNorm a|) - 1
  obtain ⟨ε, hε, hsmall⟩ := pvApprox_choose_exponent (K : ℝ) (ratLogNorm a)
  obtain ⟨u, hu, hω, hdiff⟩ := pvApprox_radial hs ε hε a
  refine ⟨u, hω, ?_⟩
  calc (K : ℝ) * ‖u - ratTranslation(hs) a u‖ ≤ (K : ℝ) * (c ε * ‖u‖) :=
        mul_le_mul_of_nonneg_left hdiff K.coe_nonneg
    _ < ‖u‖ := by
      rw [← mul_assoc]
      exact mul_lt_of_lt_one_left (norm_pos_iff.mpr hu) hsmall

private theorem rat_trivial_unramified (w : RatV) :
    (ideleClassNormTwist (1 : PontryaginDual RatC) 0).IsUnramifiedAt w := by
  have hone : ideleClassNormTwist (1 : PontryaginDual RatC) 0 = 1 := by
    ext a
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  rw [hone, HeckeCharacter.isUnramifiedAt_iff]
  simp

private theorem rat_theta0_eq_top (hs : (0 : ℝ) ≤ 2) : RatH(hs) = ⊤ := by
    apply (Submodule.dense_iff_topologicalClosure_eq_top).1
    refine (denseRange_globalTheta_zeroLine (F := ℚ) hs).mono ?_
    rintro _ ⟨w, rfl⟩
    exact ⟨w, rfl⟩

private theorem rat_primePV_small_at_uniformizer
    (v : RatV) (π : (v.adicCompletion ℚ)ˣ) (hπ : Valued.v.IsUniformizer π.val)
    (hs : (0 : ℝ) ≤ 2) (K : ℝ≥0) :
    ∃ z : RatH(hs), z.val ∈ RatE(hs) ∧
      (K : ℝ) * ‖globalThetaSobolevPrincipalValue ℚ {v} 0 hs z‖ < ‖z‖ := by
  let g := IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π
  obtain ⟨u, hu, hsmall⟩ := exists_ratDegreeTwo_approxInvariant hs g K
  let z : RatH(hs) := ⟨u, by rw [rat_theta0_eq_top hs]; trivial⟩
  refine ⟨z, hu, ?_⟩
  change (K : ℝ) * ‖(globalThetaSobolevPrincipalValue ℚ {v} 0 hs z).val‖ < ‖u‖
  have heq := globalThetaSobolevPrincipalValue_singleton v π hπ 1 (rat_trivial_unramified v) hs z hu
  exact (congrArg (fun w ↦ (K : ℝ) * ‖w‖) heq).symm ▸ hsmall

/-- A singleton principal value at degree two has vectors of arbitrarily small
relative output norm in the rational trivial norm-one isotype. -/
theorem exists_ratPrimePrincipalValue_small_norm
    (v : RatV) (hs : (0 : ℝ) ≤ 2) (K : ℝ≥0) :
    ∃ z : RatH(hs), z.val ∈ RatE(hs) ∧
      (K : ℝ) * ‖globalThetaSobolevPrincipalValue ℚ {v} 0 hs z‖ < ‖z‖ := by
  obtain ⟨π₀, hπ⟩ := (Valued.v : Valuation (v.adicCompletion ℚ)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v.adicCompletion ℚ)ˣ := Units.mk0 π₀ hπ.ne_zero
  exact rat_primePV_small_at_uniformizer v π hπ hs K

end RiemannMasullo
