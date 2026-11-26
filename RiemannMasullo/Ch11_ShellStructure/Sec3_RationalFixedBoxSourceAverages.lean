module
public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxEigenvectors
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3b
public import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Montel
public import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.ChangeOfVariables

/-! # Source-preserving averages in rational fixed boxes

Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496. The polar even sources in one Fourier
box form a complete locally convex subspace of Schwartz space. Positive dilation
orbits are continuous in its Schwartz topology. Compact averages remain in that
same source space, and an explicit seminorm bound makes their actual theta stages
commute with the Hilbert-space integral. These are source statements before closure.
-/

public noncomputable section
open Filter MeasureTheory Set Function FourierTransform
open scoped FourierTransform SchwartzMap Topology NNReal
namespace RiemannMasullo.RationalPacket

private def sourceEval (x : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ x).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)

private theorem sourceEval_apply (x : ℝ) (f : 𝓢(ℝ, ℂ)) : sourceEval x f = f x := by rfl

/-- The complete space of polar even Schwartz sources in one real Fourier box. -/
def fixedBoxEvenSources (U : ℝ) : ClosedSubmodule ℂ 𝓢(ℝ, ℂ) :=
  ((⊥ : ClosedSubmodule ℂ ℂ).comap (sourceEval 0)) ⊓
  ((⊥ : ClosedSubmodule ℂ ℂ).comap ((sourceEval 0).comp (SchwartzMap.fourierTransformCLM ℂ))) ⊓
  (⨅ r : ℝ, (⊥ : ClosedSubmodule ℂ ℂ).comap
    (((sourceEval (-r)) - sourceEval r).comp (SchwartzMap.fourierTransformCLM ℂ))) ⊓
  (⨅ r : ℝ, ⨅ _ : U < |r|, (⊥ : ClosedSubmodule ℂ ℂ).comap
    ((sourceEval r).comp (SchwartzMap.fourierTransformCLM ℂ)))

/-- The source space retains both polar equations, parity, and the exact input box. -/
theorem mem_fixedBoxEvenSources (U : ℝ) (f : 𝓢(ℝ, ℂ)) :
    f ∈ fixedBoxEvenSources U ↔ f 0 = 0 ∧ (𝓕 f) 0 = 0 ∧
      (∀ r, (𝓕 f) (-r) = (𝓕 f) r) ∧ (∀ r, U < |r| → (𝓕 f) r = 0) := by
  simp only [fixedBoxEvenSources, ClosedSubmodule.mem_inf, ClosedSubmodule.mem_comap,
    ClosedSubmodule.mem_bot, ContinuousLinearMap.comp_apply, sourceEval_apply,
    ClosedSubmodule.mem_iInf, sub_apply, sub_eq_zero]
  tauto

private theorem dilate_mem_fixedBoxEvenSources (U : ℝ) {h : ℝ} (hh : 0 ≤ h)
    {f : 𝓢(ℝ, ℂ)} (hf : f ∈ fixedBoxEvenSources U) :
    dilate (Real.exp (-h)) (Real.exp_pos _) f ∈ fixedBoxEvenSources U := by
  obtain ⟨hf0, hF0, he, hb⟩ := (mem_fixedBoxEvenSources U f).mp hf
  let r := Real.exp (-h)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hh)
  apply (mem_fixedBoxEvenSources U _).mpr
  refine ⟨by simp [dilate_apply, hf0], by simp [fourier_dilate, hF0], ?_, ?_⟩
  · intro y
    rw [fourier_dilate, fourier_dilate, neg_div, he]
  · intro y hy
    rw [fourier_dilate, hb, smul_zero]
    rw [abs_div, abs_of_pos hr]
    exact hy.trans_le (le_div_self (abs_nonneg y) hr hr1)

/-- Positive physical source dilations vary continuously in the full Schwartz topology. -/
theorem continuous_dilate_exp (f : 𝓢(ℝ, ℂ)) :
    Continuous (fun h : ℝ ↦ dilate (Real.exp (-h)) (Real.exp_pos _) f) := by
  let : MontelSpace ℂ 𝓢(ℝ, ℂ) := schwartzMap_real_montel
  let A (h : ℝ) : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.equivOfInverse
    ((Real.exp (-h)) • ContinuousLinearMap.id ℝ ℝ)
    ((Real.exp h) • ContinuousLinearMap.id ℝ ℝ)
    (fun x ↦ by simp [← mul_assoc, ← Real.exp_add])
    (fun x ↦ by simp [← mul_assoc, ← Real.exp_add])
  have ha : Continuous (fun h ↦ (A h).toContinuousLinearMap) :=
    (Real.continuous_exp.comp continuous_neg).smul continuous_const
  have hb : Continuous (fun h ↦ (A h).symm.toContinuousLinearMap) :=
    Real.continuous_exp.smul continuous_const
  refine (continuous_schwartz_comp_family A ha hb f).congr ?_
  intro h
  ext x
  rw [dilate_apply]
  rfl

private theorem exists_compact_pettisIntegral {Y B : Type*}
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [AddCommGroup B] [Module ℂ B] [UniformSpace B] [IsUniformAddGroup B]
    [T2Space B] [ContinuousSMul ℂ B] [LocallyConvexSpace ℝ B] [CompleteSpace B]
    (μ : Measure Y) [IsFiniteMeasure μ] {K : Set Y} (hK : IsCompact K)
    (hμ : ∀ᵐ y ∂μ, y ∈ K) (f : Y → B) (hf : Continuous f) :
    ∃ v : B, HasPettisIntegral (.positive μ) f v := by
  let : ContinuousSMul ℝ B := IsScalarTower.continuousSMul ℂ
  let C := closure (convexHull ℝ (insert 0 (f '' K)))
  have hi : PettisWeaklyIntegrable (.positive μ) f := by
    intro φ
    have hc := φ.continuous.comp hf
    obtain ⟨r, hr⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
    exact (integrable_const (μ := μ) r).mono' hc.aestronglyMeasurable (hμ.mono hr)
  have hc : IsCompact C :=
    ((hK.image hf).insert 0).totallyBounded.convexHull.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨v, _, hv⟩ := exists_hasPettisIntegral_mem_smul_of_isCompact_convex μ hi hc
    (convex_convexHull ..).closure
    (subset_closure (subset_convexHull _ _ (mem_insert _ _)))
    (hμ.mono fun y hy ↦ subset_closure (subset_convexHull _ _
      (mem_insert_of_mem _ ⟨y, hy, rfl⟩)))
  exact ⟨v, hv⟩

/-- Compactly supported averages of forward dilations stay in the genuine
polar even source box, with all continuous Schwartz moments preserved. -/
theorem exists_fixedBox_source_average (U L : ℝ)
    (w : ℝ → ℂ) (hw : Continuous w) (f : (fixedBoxEvenSources U).toSubmodule) :
    ∃ g : (fixedBoxEvenSources U).toSubmodule, ∀ φ : 𝓢(ℝ, ℂ) →L[ℂ] ℂ,
      φ (g : 𝓢(ℝ, ℂ)) = ∫ t in Icc 0 L,
        w t * φ (dilate (Real.exp (-t)) (Real.exp_pos _) (f : 𝓢(ℝ, ℂ))) := by
  let : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  let B := (fixedBoxEvenSources U).toSubmodule
  let : IsClosed (B : Set 𝓢(ℝ, ℂ)) := (fixedBoxEvenSources U).isClosed
  let : IsUniformAddGroup B :=
    IsUniformInducing.isUniformAddGroup B.subtype.toAddMonoidHom ⟨rfl⟩
  let : LocallyConvexSpace ℝ B := inferInstanceAs (LocallyConvexSpace ℝ (B.restrictScalars ℝ))
  let a (t : ℝ) : B := ⟨w t • dilate (Real.exp (-max t 0)) (Real.exp_pos _) (f : 𝓢(ℝ, ℂ)),
    B.smul_mem _ (dilate_mem_fixedBoxEvenSources U (le_max_right t 0) f.property)⟩
  have ha : Continuous a :=
    (hw.smul ((continuous_dilate_exp (f : 𝓢(ℝ, ℂ))).comp (continuous_id.max continuous_const))).subtype_mk _
  let μ := volume.restrict (Icc 0 L)
  have hμ : ∀ᵐ t ∂μ, t ∈ Icc 0 L := ae_restrict_mem measurableSet_Icc
  obtain ⟨g, hg⟩ := exists_compact_pettisIntegral (B := ↥B) μ isCompact_Icc hμ a ha
  refine ⟨g, fun φ ↦ ?_⟩
  have he := congrArg (fun z : PettisWeakCompletion B ↦
    (show Module.Dual ℂ (StrongDual ℂ B) from z) (φ.comp B.subtypeL)) hg.2
  change φ (g : 𝓢(ℝ, ℂ)) = ∫ t, φ (a t : 𝓢(ℝ, ℂ)) ∂μ at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [hμ] with t ht
  simp only [a, map_smul, smul_eq_mul, max_eq_left ht.1]

private theorem stageEnvelope_memLp (a : ℝ) :
    MemLp ((Ici a).indicator (fun x : ℝ ↦ (Real.exp (-(3/2)*x) : ℂ))) 2 volume := by
  have hm : Measurable ((Ici a).indicator (fun x : ℝ ↦ (Real.exp (-(3/2)*x) : ℂ))) :=
    (by fun_prop : Continuous (fun x : ℝ ↦ (Real.exp (-(3/2)*x) : ℂ))).measurable.indicator measurableSet_Ici
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have hi : IntegrableOn (fun x : ℝ ↦ Real.exp (-3*x)) (Ici a) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr (integrableOn_exp_mul_Ioi (by norm_num) a)
  apply (hi.integrable_indicator measurableSet_Ici).congr
  filter_upwards with x
  by_cases hx : x ∈ Ici a
  · simp only [indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  · simp [hx]

private theorem source_stage_memLp {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 1 ≤ q)
    (f : (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule) :
    MemLp (stage T (f : 𝓢(ℝ, ℂ))) 2 volume :=
  (stage_memLp_and_dampedStage_integrable hX T hT
    ((mem_fixedBoxEvenSources _ f).mp f.property).1
    ((mem_fixedBoxEvenSources _ f).mp f.property).2.1
    ((mem_fixedBoxEvenSources _ f).mp f.property).2.2.2).1

private def sourceStageLinearMap {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 1 ≤ q) :
    (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule →ₗ[ℂ] LogL2 where
  toFun f := (source_stage_memLp hX T hT f).toLp (stage T f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(source_stage_memLp hX T hT (f+g)).coeFn_toLp,
      (source_stage_memLp hX T hT f).coeFn_toLp,
      (source_stage_memLp hX T hT g).coeFn_toLp,
      Lp.coeFn_add ((source_stage_memLp hX T hT f).toLp (stage T f))
        ((source_stage_memLp hX T hT g).toLp (stage T g))] with x hfg hf hg hs
    rw [hfg, hs, Pi.add_apply, hf, hg]
    exact stage_add T hT f g ((mem_fixedBoxEvenSources _ f).mp f.property).1
      ((mem_fixedBoxEvenSources _ g).mp g.property).1 x
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(source_stage_memLp hX T hT (c • f)).coeFn_toLp,
      (source_stage_memLp hX T hT f).coeFn_toLp,
      Lp.coeFn_smul c ((source_stage_memLp hX T hT f).toLp (stage T f))] with x hcf hf hs
    rw [hcf, hs, Pi.smul_apply, hf]
    exact stage_smul T c f x

private theorem sourceStageLinearMap_ae {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 1 ≤ q)
    (f : (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule) :
    sourceStageLinearMap hX T hT f =ᵐ[volume] stage T f := (source_stage_memLp hX T hT f).coeFn_toLp

private theorem sourceStageLinearMap_bound {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f, ‖sourceStageLinearMap hX T hT f‖ ≤
      C * SchwartzMap.seminorm ℝ 2 0 (f : 𝓢(ℝ, ℂ)) := by
  let a := -Real.log X
  let e := (Ici a).indicator (fun x : ℝ ↦ (Real.exp (-(3/2)*x) : ℂ))
  let H := (stageEnvelope_memLp a).toLp e
  let c : ℝ := (T.powerset.card : ℝ) * (∑' n : ℤ, 1 / (n : ℝ)^2)
  have hc : 0 ≤ c := mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg fun _ ↦ by positivity)
  refine ⟨c * ‖H‖, mul_nonneg hc (norm_nonneg _), fun f ↦ ?_⟩
  have hb : ∀ᵐ x ∂volume, ‖sourceStageLinearMap hX T hT f x‖ ≤
      (c * SchwartzMap.seminorm ℝ 2 0 (f : 𝓢(ℝ, ℂ))) * ‖H x‖ := by
    filter_upwards [sourceStageLinearMap_ae hX T hT f, (stageEnvelope_memLp a).coeFn_toLp] with x hx he
    rw [hx, he]
    obtain ⟨hf0, hF0, _, hband⟩ := (mem_fixedBoxEvenSources _ f).mp f.property
    by_cases ha : a ≤ x
    · rw [indicator_of_mem (show x ∈ Ici a from ha),
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact norm_stage_le_schwartzSeminorm T hT f hf0 x
    · rw [indicator_of_notMem (show x ∉ Ici a from ha), norm_zero, mul_zero,
        stage_eq_zero_before_box hX T hT hF0 hband (lt_of_not_ge ha), norm_zero]
  exact (Lp.norm_le_mul_norm_of_ae_le_mul hb).trans_eq (by ring)

/-- The actual theta-stage map from the complete fixed-box source space to
logarithmic Hilbert space is continuous and complex linear. -/
def fixedBoxSourceStage {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 1 ≤ q) :
    (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule →L[ℂ] LogL2 where
  toLinearMap := sourceStageLinearMap hX T hT
  cont := by
    let B := (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule
    let A := sourceStageLinearMap hX T hT
    obtain ⟨C, hC, hb⟩ := sourceStageLinearMap_bound hX T hT
    let q : Seminorm ℝ B := (SchwartzMap.seminorm ℝ 2 0).comp (B.subtype.restrictScalars ℝ)
    have hq : Continuous q :=
      ((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (2,0)).comp continuous_subtype_val
    apply (norm_withSeminorms ℝ LogL2).continuous_of_continuous_comp (A.restrictScalars ℝ)
    intro i
    let c : ℝ≥0 := ⟨C, hC⟩
    apply Seminorm.continuous_of_le (q := c • q) ?_ ?_
    · exact hq.const_smul _
    · exact hb

/-- The continuous source map has the required actual theta representative. -/
theorem fixedBoxSourceStage_ae {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 1 ≤ q)
    (f : (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule) :
    fixedBoxSourceStage hX T hT f =ᵐ[volume] stage T f := sourceStageLinearMap_ae hX T hT f

/-- Compact averages of forward dilations commute with the actual theta-stage
map and retain a polar even representative in precisely the original source box. -/
theorem exists_fixedBox_stage_average {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 1 ≤ q) (L : ℝ) (w : ℝ → ℂ) (hw : Continuous w)
    (f : (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule) :
    ∃ g : (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule,
      fixedBoxSourceStage hX T hT g = ∫ t in Icc 0 L,
        w t • halfShift t (fixedBoxSourceStage hX T hT f) := by
  let : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  let U := X / (∏ q ∈ T, (q : ℝ))
  let B := (fixedBoxEvenSources U).toSubmodule
  let : IsClosed (B : Set 𝓢(ℝ, ℂ)) := (fixedBoxEvenSources U).isClosed
  let : IsUniformAddGroup B :=
    IsUniformInducing.isUniformAddGroup B.subtype.toAddMonoidHom ⟨rfl⟩
  let : LocallyConvexSpace ℝ B := inferInstanceAs (LocallyConvexSpace ℝ (B.restrictScalars ℝ))
  let b (t : ℝ) : B := ⟨dilate (Real.exp (-max t 0)) (Real.exp_pos _) (f : 𝓢(ℝ, ℂ)),
    dilate_mem_fixedBoxEvenSources U (le_max_right t 0) f.property⟩
  let a (t : ℝ) : B := w t • b t
  have hbcont : Continuous b :=
    ((continuous_dilate_exp (f : 𝓢(ℝ, ℂ))).comp (continuous_id.max continuous_const)).subtype_mk _
  have ha : Continuous a := hw.smul hbcont
  let μ := volume.restrict (Icc 0 L)
  have hμ : ∀ᵐ t ∂μ, t ∈ Icc 0 L := ae_restrict_mem measurableSet_Icc
  obtain ⟨g, hg⟩ := exists_compact_pettisIntegral (B := ↥B) μ isCompact_Icc hμ a ha
  let A := fixedBoxSourceStage hX T hT
  have hAb (t : ℝ) : A (b t) = halfShift (max t 0) (A f) := by
    apply Lp.ext
    exact (fixedBoxSourceStage_ae hX T hT (b t)).trans
      (halfShift_stage_ae (max t 0) T f (A f) (fixedBoxSourceStage_ae hX T hT f)).symm
  have hAg : HasPettisIntegral (.positive μ) (fun t ↦ A (a t)) (A g) := by
    refine ⟨fun φ ↦ hg.1 (φ.comp A), LinearMap.ext fun φ ↦ ?_⟩
    exact congrArg (fun z : PettisWeakCompletion B ↦
      (show Module.Dual ℂ (StrongDual ℂ B) from z) (φ.comp A)) hg.2
  have hi : Integrable (fun t ↦ A (a t)) μ := (A.continuous.comp ha).integrableOn_Icc
  refine ⟨g, hAg.unique (RiemannMasullo.Integrable.hasPettisIntegral hi) |>.trans ?_⟩
  apply integral_congr_ae
  filter_upwards [hμ] with t ht
  change A (w t • b t) = _
  rw [map_smul, hAb, max_eq_left ht.1]

end RiemannMasullo.RationalPacket
