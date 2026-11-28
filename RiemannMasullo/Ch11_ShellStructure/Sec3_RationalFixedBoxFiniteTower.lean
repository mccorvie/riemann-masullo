module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxLayer
public import RiemannMasullo.ForMathlib.Analysis.Distribution.ForwardTestAction
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.InvariantCompression
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.NuclearForwardExtension

/-! # Nuclear compact test actions on finite rational relative levels

Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496. The actual orthogonal compression
to the difference of the empty-factor and finite-factor theta stages is nuclear
for every smooth test compactly supported in positive time. The proof uses the
proved prime-packet actions and positive-time convolution factorization.

This is the rational, trivial-angular, unweighted logarithmic model.
-/

public noncomputable section
open Set MeasureTheory
open scoped Topology SchwartzMap NNReal
namespace RiemannMasullo.RationalPacket

private def positiveHalfShift (t : ℝ) : LogL2 →L[ℂ] LogL2 := halfShift (t.toNNReal : ℝ)
private theorem continuous_positiveHalfShift (F : LogL2) :
    Continuous (fun t : ℝ ↦ positiveHalfShift t F) :=
  (continuous_halfShift F).comp (by fun_prop)
private theorem positiveHalfShift_bound (t : ℝ) :
    ‖positiveHalfShift t‖ ≤ Real.exp ((t.toNNReal : ℝ) / 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro F
  exact (norm_halfShift _ F).le

/-- The actual positive-time compact test action on logarithmic L². -/
def fixedBoxAmbientTestAction (f : PositiveTimeTest) : LogL2 →L[ℂ] LogL2 :=
  forwardTestOperator positiveHalfShift continuous_positiveHalfShift
    (fun t ↦ Real.exp ((t.toNNReal : ℝ) / 2)) (by fun_prop) positiveHalfShift_bound f

theorem fixedBoxAmbientTestAction_apply (f : PositiveTimeTest) (F : LogL2) :
    fixedBoxAmbientTestAction f F = ∫ t : ℝ, f t • halfShift (t.toNNReal : ℝ) F := by
  exact forwardTestOperator_apply positiveHalfShift continuous_positiveHalfShift
    (fun t ↦ Real.exp ((t.toNNReal : ℝ) / 2)) (by fun_prop) positiveHalfShift_bound f F

theorem fixedBoxAmbientTestAction_add (f g : PositiveTimeTest) :
    fixedBoxAmbientTestAction (f+g) = fixedBoxAmbientTestAction f + fixedBoxAmbientTestAction g :=
  forwardTestOperator_add _ _ _ _ _ f g

theorem fixedBoxAmbientTestAction_convolution (f g : PositiveTimeTest) :
    fixedBoxAmbientTestAction (positiveTestConvolution f g) =
      (fixedBoxAmbientTestAction f).comp (fixedBoxAmbientTestAction g) := by
  apply forwardTestOperator_convolution
  intro s t hs ht
  apply ContinuousLinearMap.ext
  intro F
  simp only [positiveHalfShift, Real.coe_toNNReal _ hs, Real.coe_toNNReal _ ht,
    Real.coe_toNNReal _ (add_nonneg hs ht), ContinuousLinearMap.comp_apply, halfShift_add]

variable {X : ℝ} (hX : 0 < X)
local instance (M : ClosedSubmodule ℂ LogL2) : IsClosed (M.toSubmodule : Set LogL2) := M.isClosed

include hX in
theorem fixedBoxAmbientTestAction_mem (S : Finset ℕ) (hS1 : ∀ q ∈ S, 1 ≤ q)
    (f : PositiveTimeTest) (F : LogL2) (hF : F ∈ closedStageSubmodule X S hS1) :
    fixedBoxAmbientTestAction f F ∈ closedStageSubmodule X S hS1 := by
  let M := closedStageSubmodule X S hS1
  apply Submodule.starProjection_eq_self_iff.mp
  rw [fixedBoxAmbientTestAction_apply]
  have hi : Integrable (fun t : ℝ ↦ f t • halfShift (t.toNNReal : ℝ) F) volume :=
    forwardTest_integrable positiveHalfShift continuous_positiveHalfShift f F
  rw [← (closedStageSubmodule X S hS1).toSubmodule.starProjection.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards with t
  apply Submodule.starProjection_eq_self_iff.mpr
  exact M.smul_mem (f t) (halfShift_mem_closedStage hX S hS1 (NNReal.coe_nonneg _) hF)

include hX in
/-- Every finite factor stage lies in the original empty-factor stage. -/
theorem fixedBox_stage_le_empty (S : Finset ℕ) (hS1 : ∀ q ∈ S, 1 ≤ q) :
    closedStageSubmodule X S hS1 ≤ closedStageSubmodule X ∅ (by simp) := by
  induction S using Finset.induction_on with
  | empty => exact le_rfl
  | @insert p T hp ih =>
    have hT1 : ∀ q ∈ T, 1 ≤ q := fun q hq ↦ hS1 q (Finset.mem_insert_of_mem hq)
    exact (fixedBox_nextStage_le T hT1 p hS1 hX).trans (ih hT1)

/-- The actual compression to the finite relative theta level in the original L². -/
def fixedBoxFiniteTestAction (S : Finset ℕ) (hS1 : ∀ q ∈ S, 1 ≤ q)
    (f : PositiveTimeTest) : LogL2 →L[ℂ] LogL2 :=
  closedLayerCompression (closedStageSubmodule X ∅ (by simp))
    (closedStageSubmodule X S hS1) (fixedBoxAmbientTestAction f)

theorem fixedBoxFiniteTestAction_def (S : Finset ℕ) (hS1 : ∀ q ∈ S, 1 ≤ q)
    (f : PositiveTimeTest) :
    fixedBoxFiniteTestAction (X := X) S hS1 f =
      closedLayerCompression (closedStageSubmodule X ∅ (by simp))
        (closedStageSubmodule X S hS1) (fixedBoxAmbientTestAction f) := by rfl

theorem fixedBoxFiniteTestAction_add (S : Finset ℕ) (hS1 : ∀ q ∈ S, 1 ≤ q)
    (f g : PositiveTimeTest) :
    fixedBoxFiniteTestAction (X := X) S hS1 (f+g) =
      fixedBoxFiniteTestAction (X := X) S hS1 f + fixedBoxFiniteTestAction (X := X) S hS1 g := by
  simp only [fixedBoxFiniteTestAction_def, fixedBoxAmbientTestAction_add, closedLayerCompression_add]

include hX in
theorem fixedBoxFiniteTestAction_convolution (S : Finset ℕ) (hS1 : ∀ q ∈ S, 1 ≤ q)
    (f g : PositiveTimeTest) :
    fixedBoxFiniteTestAction (X := X) S hS1 (positiveTestConvolution f g) =
      (fixedBoxFiniteTestAction (X := X) S hS1 f).comp (fixedBoxFiniteTestAction (X := X) S hS1 g) := by
  simp only [fixedBoxFiniteTestAction_def, fixedBoxAmbientTestAction_convolution]
  exact closedLayerCompression_comp _ _ (fixedBox_stage_le_empty hX S hS1) _ _
    (fixedBoxAmbientTestAction_mem hX S hS1 f)
    (fixedBoxAmbientTestAction_mem hX ∅ (by simp) g)
    (fixedBoxAmbientTestAction_mem hX S hS1 g)

/-- The consecutive finite-level compression is exactly the previously constructed
actual orthogonal packet action. -/
theorem fixedBoxLayerTestAction_eq_compression (T : Finset ℕ) (hT1 : ∀ q ∈ T, 1 ≤ q)
    (p : ℕ) (hTp1 : ∀ q ∈ insert p T, 1 ≤ q) (hp : p.Prime) (hpT : p ∉ T)
    (f : PositiveTimeTest) :
    fixedBoxLayerTestAction T hT1 p hTp1 hX hp hpT (positiveTestToSchwartz f) =
      closedLayerCompression (closedStageSubmodule X T hT1)
        (closedStageSubmodule X (insert p T) hTp1) (fixedBoxAmbientTestAction f) := by
  have hw : Function.support (positiveTestToSchwartz f) ⊆ Ici 0 := by
    intro t ht
    have ht' : f t ≠ 0 := by simpa only [Function.mem_support, positiveTestToSchwartz_apply] using ht
    exact (show 0 < t from f.tsupport_subset (subset_tsupport f ht')).le
  rw [closedLayerCompression_def, ← fixedBoxLayerProjection_eq_difference T hT1 p hTp1 hX]
  apply ContinuousLinearMap.ext
  intro F
  rw [fixedBoxLayerTestAction_apply_forward T hT1 p hTp1 hX hp hpT _ hw]
  simp only [ContinuousLinearMap.comp_apply, fixedBoxAmbientTestAction_apply]
  have hi : Integrable (fun t : ℝ ↦ f t • halfShift (t.toNNReal : ℝ)
      (fixedBoxLayerProjection (X := X) T hT1 p hTp1 F)) volume :=
    forwardTest_integrable positiveHalfShift continuous_positiveHalfShift f _
  rw [← (fixedBoxLayerProjection (X := X) T hT1 p hTp1).integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards with t
  rw [positiveTestToSchwartz_apply, map_smul]


include hX in
/-- Paper: (11.3.1.3)–(11.3.1.4), p. 494. Every compact positive-time smooth
convolution action on an actual finite relative rational theta level is nuclear.
Deviation: This is the unweighted logarithmic, trivial-angular model. Positive-time
factorization proves nuclearity of the full triangular operator, including its
off-diagonal blocks; no separation estimate between logarithmic prime lattices is assumed. -/
theorem fixedBoxFiniteTestAction_nuclear (S : Finset ℕ) (hS1 : ∀ q ∈ S, 1 ≤ q)
    (hS : ∀ q ∈ S, q.Prime) (f : PositiveTimeTest) :
    IsNuclearOperator (fixedBoxFiniteTestAction (X := X) S hS1 f) := by
  induction S using Finset.induction_on generalizing f with
  | empty =>
    have he : fixedBoxFiniteTestAction (X := X) ∅ hS1 f = 0 := by
      simp only [fixedBoxFiniteTestAction_def, closedLayerCompression_def, sub_self,
        ContinuousLinearMap.zero_comp]
    rw [he]
    exact (nuclearEndomorphisms LogL2).zero_mem
  | @insert p T hpT ih =>
    have hT1 : ∀ q ∈ T, 1 ≤ q := fun q hq ↦ hS1 q (Finset.mem_insert_of_mem hq)
    have hT : ∀ q ∈ T, q.Prime := fun q hq ↦ hS q (Finset.mem_insert_of_mem hq)
    have hp := hS p (Finset.mem_insert_self p T)
    let M := closedStageSubmodule X ∅ (by simp)
    let B := closedStageSubmodule X T hT1
    let D := closedStageSubmodule X (insert p T) hS1
    have hDB : D ≤ B := fixedBox_nextStage_le T hT1 p hS1 hX
    have hBM : B ≤ M := fixedBox_stage_le_empty hX T hT1
    apply nuclear_positiveTest_extension
      (fixedBoxFiniteTestAction (X := X) (insert p T) hS1)
      (fixedBoxFiniteTestAction_add _ _)
      (fixedBoxFiniteTestAction_convolution hX _ _)
      (B.toSubmodule.starProjection - D.toSubmodule.starProjection)
      (M.toSubmodule.starProjection - B.toSubmodule.starProjection)
      (M.toSubmodule.starProjection - D.toSubmodule.starProjection)
    · abel
    · intro g
      exact closedLayerCompression_right M D (hDB.trans hBM) (fixedBoxAmbientTestAction g)
    · intro g
      rw [fixedBoxFiniteTestAction_def, closedLayerCompression_deep_right M B D hDB hBM _
        (fixedBoxAmbientTestAction_mem hX T hT1 g)
        (fixedBoxAmbientTestAction_mem hX (insert p T) hS1 g)]
      rw [← fixedBoxLayerTestAction_eq_compression hX T hT1 p hS1 hp hpT g]
      have hn := fixedBoxLayerTestAction_nuclear_trace T hT1 p hS1 hX hp hpT hT
        (positiveTestToSchwartz g)
      exact hn.choose
    · intro g
      rw [fixedBoxFiniteTestAction_def, closedLayerCompression_shallow_left M B D hDB hBM _
        (fixedBoxAmbientTestAction_mem hX T hT1 g)
        (fixedBoxAmbientTestAction_mem hX (insert p T) hS1 g)]
      exact ih hT1 hT g

end RiemannMasullo.RationalPacket
