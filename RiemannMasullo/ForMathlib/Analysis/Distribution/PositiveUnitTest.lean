module

public import RiemannMasullo.ForMathlib.Analysis.Distribution.PositiveTests
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # Unit-mass smooth tests with short positive-time support -/

public noncomputable section
open Set Function MeasureTheory
namespace RiemannMasullo

/-- A positive-time unit-mass test can be supported strictly before any prescribed positive time. -/
theorem exists_positiveTest_unit_mass {L : ℝ} (hL : 0 < L) :
    ∃ f : PositiveTimeTest, tsupport f ⊆ Ioo 0 L ∧ (∫ t : ℝ, f t) = 1 := by
  let b : ContDiffBump (L / 2) := ⟨L / 8, L / 4, by positivity, by linarith⟩
  let g (t : ℝ) : ℂ := (b.normed volume t : ℂ)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := Complex.ofRealCLM.contDiff.comp b.contDiff_normed
  have hs : tsupport g = Metric.closedBall (L / 2) (L / 4) := by
    have he : Function.support g = Function.support (b.normed volume) := by
      ext t
      simp [mem_support, g]
    rw [tsupport, he, ← tsupport, b.tsupport_normed_eq]
  have hc : HasCompactSupport g := by
    rw [HasCompactSupport, hs]
    exact isCompact_closedBall _ _
  have hpos : tsupport g ⊆ Ioo 0 L := by
    intro t ht
    rw [hs, Metric.mem_closedBall, Real.dist_eq, abs_le] at ht
    constructor <;> linarith
  refine ⟨⟨g, hg, hc, fun t ht ↦ (hpos ht).1⟩, hpos, ?_⟩
  change (∫ t : ℝ, (b.normed volume t : ℂ)) = 1
  rw [integral_complex_ofReal, b.integral_normed, Complex.ofReal_one]

end RiemannMasullo
