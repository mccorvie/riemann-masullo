module

public import RiemannMasullo.ForMathlib.Analysis.FunctionalSpaces.RealJumpEnergy
import Mathlib.MeasureTheory.Group.Integral

/-! # Translation invariance of positive jump energies

Simultaneously translating both endpoints preserves the jump-pair measure. Thus the
energy domain and its pairing translate together, including singular jump measures.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace RiemannMasullo

/-- Simultaneous translation of both jump endpoints preserves the jump-pair measure. -/
theorem measurePreserving_realJumpPair_translation (κ : Measure ℝ) [SFinite κ] (z : ℝ) :
    MeasurePreserving (fun p : ℝ × ℝ ↦ (p.1 + z, p.2 + z))
      (realJumpPairMeasure κ) (realJumpPairMeasure κ) := by
  refine ⟨by fun_prop, ?_⟩
  unfold realJumpPairMeasure
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun p : ℝ × ℝ ↦ (p.1 + z, p.2 + z)) ∘
      (fun p : ℝ × ℝ ↦ (p.2 + p.1, p.2)) =
    (fun p : ℝ × ℝ ↦ (p.2 + p.1, p.2)) ∘
      Prod.map id (fun x : ℝ ↦ x + z) := by
    funext ⟨r, x⟩
    change (x + r + z, x + z) = (x + z + r, x + z)
    congr 1
    ring
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop),
    ((MeasurePreserving.id κ).prod (measurePreserving_add_right volume z)).map_eq]

/-- Translating a function preserves square-integrability of its jump differences. -/
theorem memLp_jump_translation (κ : Measure ℝ) [SFinite κ] {f : ℝ → ℝ}
    (hf : MemLp (fun p : ℝ × ℝ ↦ f p.1 - f p.2) 2 (realJumpPairMeasure κ)) (z : ℝ) :
    MemLp (fun p : ℝ × ℝ ↦ f (p.1 + z) - f (p.2 + z)) 2 (realJumpPairMeasure κ) :=
  hf.comp_measurePreserving (measurePreserving_realJumpPair_translation κ z)

/-- The real jump pairing is invariant under simultaneous translation of its functions. -/
theorem realNonlocalPairing_translation (κ : Measure ℝ) [SFinite κ]
    (f g : ℝ → ℝ) (z : ℝ) :
    realNonlocalPairing volume (realJumpPairMeasure κ)
      (fun x ↦ f (x + z)) (fun x ↦ g (x + z)) =
      realNonlocalPairing volume (realJumpPairMeasure κ) f g := by
  unfold realNonlocalPairing
  rw [integral_add_right_eq_self (fun x ↦ f x * g x) z]
  congr 2
  have hm := measurePreserving_realJumpPair_translation κ z
  have he : MeasurableEmbedding (fun p : ℝ × ℝ ↦ (p.1 + z, p.2 + z)) := by
    exact (Homeomorph.addRight (z, z)).toMeasurableEquiv.measurableEmbedding
  exact hm.integral_comp he (fun p : ℝ × ℝ ↦ (f p.1 - f p.2) * (g p.1 - g p.2))

/-- Moving a Green kernel to `z` transfers the translation to its test function. -/
theorem realNonlocalPairing_sub_translation (κ : Measure ℝ) [SFinite κ]
    (f g : ℝ → ℝ) (z : ℝ) :
    realNonlocalPairing volume (realJumpPairMeasure κ) (fun x ↦ f (x - z)) g =
      realNonlocalPairing volume (realJumpPairMeasure κ) f (fun x ↦ g (x + z)) := by
  have he := realNonlocalPairing_translation κ (fun x ↦ f (x - z)) g z
  simpa only [add_sub_cancel_right] using he.symm

end RiemannMasullo
