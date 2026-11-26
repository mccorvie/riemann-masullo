module

public import RiemannMasullo.ForMathlib.Analysis.Distribution.PositiveFactorization
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! # The convolution algebra of positive-time smooth compact tests -/

public noncomputable section
open Set Function MeasureTheory TopologicalSpace
open scoped ContDiff SchwartzMap Pointwise
namespace RiemannMasullo

scoped notation "PositiveTimeTest" =>
  TestFunction (TopologicalSpace.Opens.mk (Set.Ioi (0 : ℝ)) isOpen_Ioi) ℂ ⊤

/-- A positive-time compact smooth test, viewed in Schwartz space. -/
def positiveTestToSchwartz : PositiveTimeTest →ₗ[ℂ] 𝓢(ℝ, ℂ) where
  toFun f := f.hasCompactSupport.toSchwartzMap f.contDiff
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

theorem positiveTestToSchwartz_apply (f : PositiveTimeTest) (x : ℝ) :
    positiveTestToSchwartz f x = f x := by rfl

/-- Convolution stays compactly supported strictly inside positive time. -/
def positiveTestConvolution (f g : PositiveTimeTest) : PositiveTimeTest := by
  let L := ContinuousLinearMap.mul ℝ ℂ
  let h := MeasureTheory.convolution f g L volume
  have hc : HasCompactSupport h := f.hasCompactSupport.convolution L g.hasCompactSupport
  have hd : ContDiff ℝ (⊤ : ℕ∞) h :=
    g.hasCompactSupport.contDiff_convolution_right L f.continuous.locallyIntegrable g.contDiff
  have hs : tsupport h ⊆ tsupport f + tsupport g := by
    apply closure_minimal _ (f.hasCompactSupport.isCompact.add g.hasCompactSupport).isClosed
    exact (support_convolution_subset L).trans (add_subset_add subset_closure subset_closure)
  refine ⟨h, hd, hc, fun x hx ↦ ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := hs hx
  change 0 < a + b
  exact add_pos (show 0 < a from f.tsupport_subset ha) (show 0 < b from g.tsupport_subset hb)

theorem positiveTestConvolution_apply (f g : PositiveTimeTest) (x : ℝ) :
    positiveTestConvolution f g x = ∫ t : ℝ, f t * g (x - t) := by rfl

/-- Two positive-time convolution products suffice for every positive-time test. -/
theorem exists_positiveTest_factorization (f : PositiveTimeTest) :
    ∃ u v r s : PositiveTimeTest,
      f = positiveTestConvolution u v + positiveTestConvolution r s := by
  have hh := positive_compact_schwartz_factorization (positiveTestToSchwartz f)
    f.hasCompactSupport f.tsupport_subset
  rcases hh with ⟨u, v, r, s, hu, hv, hr, hs, hf⟩
  refine ⟨⟨u, u.smooth _, hu.1, hu.2⟩, ⟨v, v.smooth _, hv.1, hv.2⟩,
    ⟨r, r.smooth _, hr.1, hr.2⟩, ⟨s, s.smooth _, hs.1, hs.2⟩, ?_⟩
  apply TestFunction.ext
  intro x
  simpa only [positiveTestToSchwartz_apply, add_apply, positiveTestConvolution_apply, TestFunction.coe_mk] using! hf x

end RiemannMasullo
