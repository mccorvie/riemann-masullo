module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxFiniteTower

/-! # Unitary changes of the total rational Fourier box

Exact rescaling of genuine Fourier witnesses passes to the closed theta stages.
The resulting unitary conjugates the full finite relative-level test action.
-/

public noncomputable section
open Set Filter Function MeasureTheory
open scoped Topology SchwartzMap FourierTransform
namespace RiemannMasullo.RationalPacket

/-- Translation of the logarithmic coordinate with its scalar half-density removed. -/
def fixedBoxTranslation (h : ℝ) : LogL2 →ₗᵢ[ℂ] LogL2 where
  toLinearMap := ((Real.exp (-h/2) : ℂ) • halfShift h).toLinearMap
  norm_map' F := by
    change ‖(Real.exp (-h/2) : ℂ) • halfShift h F‖ = ‖F‖
    rw [norm_smul, norm_halfShift, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), ← mul_assoc, ← Real.exp_add]
    ring_nf
    simp

theorem fixedBoxTranslation_apply (h : ℝ) (F : LogL2) :
    fixedBoxTranslation h F = (Real.exp (-h/2) : ℂ) • halfShift h F := by rfl

theorem fixedBoxTranslation_add (h k : ℝ) (F : LogL2) :
    fixedBoxTranslation (h+k) F = fixedBoxTranslation h (fixedBoxTranslation k F) := by
  simp only [fixedBoxTranslation_apply, map_smul, smul_smul, halfShift_add]
  congr 1
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem fixedBoxTranslation_zero (F : LogL2) : fixedBoxTranslation 0 F = F := by
  simp only [fixedBoxTranslation_apply, neg_zero, zero_div, Real.exp_zero,
    Complex.ofReal_one, one_smul, halfShift_zero]

/-- The Fourier-box change is implemented by a unitary on the ambient logarithmic L². -/
def fixedBoxTranslationEquiv (h : ℝ) : LogL2 ≃ₗᵢ[ℂ] LogL2 :=
  LinearIsometryEquiv.ofSurjective (fixedBoxTranslation h) (fun F ↦
    ⟨fixedBoxTranslation (-h) F, by rw [← fixedBoxTranslation_add, add_neg_cancel, fixedBoxTranslation_zero]⟩)

theorem fixedBoxTranslationEquiv_apply (h : ℝ) (F : LogL2) :
    fixedBoxTranslationEquiv h F = fixedBoxTranslation h F := by
  exact congrFun (LinearIsometryEquiv.coe_ofSurjective _ _) F

theorem fixedBoxTranslationEquiv_symm (h : ℝ) (F : LogL2) :
    (fixedBoxTranslationEquiv h).symm F = fixedBoxTranslation (-h) F := by
  apply (fixedBoxTranslationEquiv h).injective
  rw [LinearIsometryEquiv.apply_symm_apply, fixedBoxTranslationEquiv_apply,
    ← fixedBoxTranslation_add, add_neg_cancel, fixedBoxTranslation_zero]

/-- Dilation of the Fourier witness moves the total Fourier box by the exact
logarithmic translation factor. -/
theorem halfShift_mem_scaled_stageGenerators (X : ℝ) (T : Finset ℕ) (h : ℝ)
    {F : LogL2} (hF : F ∈ stageGenerators X T) :
    halfShift h F ∈ stageGenerators (X * Real.exp (-h)) T := by
  obtain ⟨f, hf0, hfF0, hband, hrep⟩ := (mem_stageGenerators_iff _ _ _).mp hF
  let r := Real.exp (-h)
  have hr : 0 < r := Real.exp_pos _
  let g := dilate r hr f
  apply (mem_stageGenerators_iff _ _ _).mpr
  refine ⟨g, by simp [g, hf0], by simp [g, fourier_dilate, hfF0], ?_, ?_⟩
  · intro y hy
    dsimp only [g]
    rw [fourier_dilate, hband, smul_zero]
    rw [abs_div, abs_of_pos hr]
    apply (lt_div_iff₀ hr).mpr
    convert hy using 1; ring
  · have ht := (measurePreserving_add_right volume (-h)).quasiMeasurePreserving.ae_eq_comp hrep
    filter_upwards [halfShift_ae h F, ht] with x hx htx
    change F (x - h) = stage T f (x - h) at htx
    rw [hx, htx]
    simp only [g, stage_dilate_real, r, Real.log_exp, neg_neg, sub_eq_add_neg]

/-- Exact Fourier-box rescaling holds after completion of the genuine theta stage. -/
theorem halfShift_mem_scaled_closedStage (X : ℝ) (T : Finset ℕ)
    (hT1 : ∀ q ∈ T, 1 ≤ q) (h : ℝ)
    {F : LogL2} (hF : F ∈ closedStageSubmodule X T hT1) :
    halfShift h F ∈ closedStageSubmodule (X * Real.exp (-h)) T hT1 := by
  have hm : MapsTo (halfShift h) (stageGenerators X T)
      (stageGenerators (X * Real.exp (-h)) T) :=
    fun _ hF ↦ halfShift_mem_scaled_stageGenerators X T h hF
  exact (mem_closedStageSubmodule_iff _ T hT1 _).mpr
    (hm.closure (halfShift h).continuous ((mem_closedStageSubmodule_iff X T hT1 _).mp hF))


/-- The unitary translation carries each completed stage to its rescaled box. -/
theorem fixedBoxTranslation_mem_scaled_closedStage (X : ℝ) (T : Finset ℕ)
    (hT1 : ∀ q ∈ T, 1 ≤ q) (h : ℝ)
    {F : LogL2} (hF : F ∈ closedStageSubmodule X T hT1) :
    fixedBoxTranslation h F ∈ closedStageSubmodule (X * Real.exp (-h)) T hT1 := by
  rw [fixedBoxTranslation_apply]
  exact (closedStageSubmodule _ T hT1).smul_mem _
    (halfShift_mem_scaled_closedStage X T hT1 h hF)

/-- Membership of the genuine closed stage is transported in both directions. -/
theorem fixedBoxTranslationEquiv_mem_iff (X : ℝ) (T : Finset ℕ)
    (hT1 : ∀ q ∈ T, 1 ≤ q) (h : ℝ) (F : LogL2) :
    fixedBoxTranslationEquiv h F ∈ closedStageSubmodule (X * Real.exp (-h)) T hT1 ↔
      F ∈ closedStageSubmodule X T hT1 := by
  rw [fixedBoxTranslationEquiv_apply]
  constructor
  · intro hF
    have hb := fixedBoxTranslation_mem_scaled_closedStage (X * Real.exp (-h)) T hT1 (-h) hF
    rw [← fixedBoxTranslation_add, neg_add_cancel, fixedBoxTranslation_zero] at hb
    have he : X * Real.exp (-h) * Real.exp (- -h) = X := by
      rw [neg_neg, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    simpa only [he] using hb
  · exact fixedBoxTranslation_mem_scaled_closedStage X T hT1 h

/-- Exact subspace equality under the unitary Fourier-box rescaling. -/
theorem closedStageSubmodule_map_translation (X : ℝ) (T : Finset ℕ)
    (hT1 : ∀ q ∈ T, 1 ≤ q) (h : ℝ) :
    (closedStageSubmodule X T hT1).toSubmodule.map
      (fixedBoxTranslationEquiv h).toLinearEquiv.toLinearMap =
      (closedStageSubmodule (X * Real.exp (-h)) T hT1).toSubmodule := by
  apply le_antisymm
  · rintro F ⟨G, hG, rfl⟩
    exact (fixedBoxTranslationEquiv_mem_iff X T hT1 h G).mpr hG
  · intro F hF
    refine ⟨(fixedBoxTranslationEquiv h).symm F, ?_, (fixedBoxTranslationEquiv h).apply_symm_apply F⟩
    apply (fixedBoxTranslationEquiv_mem_iff X T hT1 h _).mp
    simpa only [LinearIsometryEquiv.apply_symm_apply] using! hF

local instance (M : ClosedSubmodule ℂ LogL2) : IsClosed (M.toSubmodule : Set LogL2) := M.isClosed

/-- Orthogonal projection onto a genuine completed stage transforms unitarily
under a change of Fourier box. -/
theorem closedStageProjection_translation (X : ℝ) (T : Finset ℕ)
    (hT1 : ∀ q ∈ T, 1 ≤ q) (h : ℝ) (F : LogL2) :
    (closedStageSubmodule (X * Real.exp (-h)) T hT1).toSubmodule.starProjection F =
      fixedBoxTranslationEquiv h ((closedStageSubmodule X T hT1).toSubmodule.starProjection
        ((fixedBoxTranslationEquiv h).symm F)) := by
  have he := Submodule.starProjection_map_apply (fixedBoxTranslationEquiv h)
    (closedStageSubmodule X T hT1).toSubmodule F
  simpa only [closedStageSubmodule_map_translation] using! he

/-- Translation commutes with the genuine half-density shift group. -/
theorem fixedBoxTranslation_halfShift (h t : ℝ) (F : LogL2) :
    fixedBoxTranslationEquiv h (halfShift t F) = halfShift t (fixedBoxTranslationEquiv h F) := by
  simp only [fixedBoxTranslationEquiv_apply, fixedBoxTranslation_apply, map_smul,
    ← halfShift_add, add_comm h t]

/-- The actual integrated compact test action commutes with change of Fourier box. -/
theorem fixedBoxTranslation_ambientTest (h : ℝ) (f : PositiveTimeTest) (F : LogL2) :
    fixedBoxTranslationEquiv h (fixedBoxAmbientTestAction f F) =
      fixedBoxAmbientTestAction f (fixedBoxTranslationEquiv h F) := by
  simp only [fixedBoxAmbientTestAction_apply]
  calc
    _ = ∫ t : ℝ, fixedBoxTranslationEquiv h (f t • halfShift (t.toNNReal : ℝ) F) := by
      exact ((fixedBoxTranslationEquiv h).toLinearIsometry.integral_comp_comm
        (fun t : ℝ ↦ f t • halfShift (t.toNNReal : ℝ) F)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [map_smul, fixedBoxTranslation_halfShift]


private theorem relativeProjection_translation (X : ℝ) (S : Finset ℕ)
    (hS1 : ∀ q ∈ S, 1 ≤ q) (h : ℝ) (F : LogL2) :
    ((closedStageSubmodule (X * Real.exp (-h)) ∅ (by simp)).toSubmodule.starProjection -
      (closedStageSubmodule (X * Real.exp (-h)) S hS1).toSubmodule.starProjection)
      (fixedBoxTranslationEquiv h F) =
    fixedBoxTranslationEquiv h (((closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection -
      (closedStageSubmodule X S hS1).toSubmodule.starProjection) F) := by
  simp only [sub_apply, closedStageProjection_translation,
    LinearIsometryEquiv.symm_apply_apply, map_sub]

/-- The actual finite relative-level action intertwines with the unitary change
of total Fourier box. -/
theorem fixedBoxFiniteTestAction_translation (X : ℝ) (S : Finset ℕ)
    (hS1 : ∀ q ∈ S, 1 ≤ q) (h : ℝ) (f : PositiveTimeTest) (F : LogL2) :
    fixedBoxFiniteTestAction (X := X * Real.exp (-h)) S hS1 f (fixedBoxTranslationEquiv h F) =
      fixedBoxTranslationEquiv h (fixedBoxFiniteTestAction (X := X) S hS1 f F) := by
  simp only [fixedBoxFiniteTestAction_def, closedLayerCompression_def, ContinuousLinearMap.comp_apply]
  rw [relativeProjection_translation, ← fixedBoxTranslation_ambientTest, relativeProjection_translation]

/-- Changing the Fourier box conjugates the full actual finite-level operator
by a unitary of the original logarithmic Hilbert space. -/
theorem fixedBoxFiniteTestAction_unitary_conjugate (X : ℝ) (S : Finset ℕ)
    (hS1 : ∀ q ∈ S, 1 ≤ q) (h : ℝ) (f : PositiveTimeTest) :
    fixedBoxFiniteTestAction (X := X * Real.exp (-h)) S hS1 f =
      (fixedBoxTranslationEquiv h).toLinearIsometry.toContinuousLinearMap.comp
        ((fixedBoxFiniteTestAction (X := X) S hS1 f).comp
          (fixedBoxTranslationEquiv h).symm.toLinearIsometry.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro F
  have he := fixedBoxFiniteTestAction_translation X S hS1 h f ((fixedBoxTranslationEquiv h).symm F)
  simpa only [LinearIsometryEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry] using! he

end RiemannMasullo.RationalPacket
