module

public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.Bochner.JumpEnergy
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Measure

/-! # Representatives and normal contractions for the tempered jump energy -/

public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RiemannMasullo

private theorem measurable_jumpCoordinates :
    Measurable (fun hx : ℝ × ℝ ↦ (hx.2 + hx.1, hx.2)) := by fun_prop

/-- The first endpoint avoids every volume-null set, even if the displacement measure
has infinite mass. Fubini reduces this to invariance of volume under each translation. -/
theorem temperedJumpPairMeasure_quasiMeasurePreserving_fst (s : ℝ) :
    QuasiMeasurePreserving Prod.fst (temperedJumpPairMeasure s) volume := by
  have h : QuasiMeasurePreserving (fun hx : ℝ × ℝ ↦ hx.2 + hx.1)
      ((temperedJumpMeasure s).prod volume) volume :=
    QuasiMeasurePreserving.prod_of_right (measurable_snd.add measurable_fst).aemeasurable
      (ae_of_all _ fun h ↦ (measurePreserving_add_right volume h).quasiMeasurePreserving)
  refine ⟨measurable_fst.aemeasurable, ?_⟩
  rw [temperedJumpPairMeasure_eq_map, Measure.map_map measurable_fst measurable_jumpCoordinates]
  exact h.absolutelyContinuous

/-- The second endpoint likewise avoids every volume-null set. -/
theorem temperedJumpPairMeasure_quasiMeasurePreserving_snd (s : ℝ) :
    QuasiMeasurePreserving Prod.snd (temperedJumpPairMeasure s) volume := by
  refine ⟨measurable_snd.aemeasurable, ?_⟩
  rw [temperedJumpPairMeasure_eq_map, Measure.map_map measurable_snd measurable_jumpCoordinates]
  exact (Measure.quasiMeasurePreserving_snd (μ := temperedJumpMeasure s)
    (ν := (volume : Measure ℝ))).absolutelyContinuous

/-- No measurability of the null set itself is needed. -/
theorem temperedJumpPairMeasure_null_preimages (s : ℝ) {N : Set ℝ} (hN : volume N = 0) :
    temperedJumpPairMeasure s (Prod.fst ⁻¹' N) = 0 ∧
      temperedJumpPairMeasure s (Prod.snd ⁻¹' N) = 0 :=
  ⟨(temperedJumpPairMeasure_quasiMeasurePreserving_fst s).preimage_null hN,
    (temperedJumpPairMeasure_quasiMeasurePreserving_snd s).preimage_null hN⟩

/-- The jump difference is independent of the choice of volume-a.e. representative. -/
theorem temperedJumpPairMeasure_sub_congr_ae {E : Type*} [Sub E] (s : ℝ)
    {u v : ℝ → E} (huv : u =ᵐ[volume] v) :
    (fun z : ℝ × ℝ ↦ u z.1 - u z.2) =ᵐ[temperedJumpPairMeasure s]
      (fun z ↦ v z.1 - v z.2) :=
  ((temperedJumpPairMeasure_quasiMeasurePreserving_fst s).ae_eq_comp huv).sub
    ((temperedJumpPairMeasure_quasiMeasurePreserving_snd s).ae_eq_comp huv)

/-- Extended-valued energy: no convention about divergent Bochner integrals enters. -/
def temperedJumpExtendedEnergy {E : Type*} [NormedAddCommGroup E] (s : ℝ) (u : ℝ → E) : ℝ≥0∞ :=
  (∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2)) + (2 : ℝ≥0∞)⁻¹ *
    ∫⁻ z, ENNReal.ofReal (‖u z.1 - u z.2‖ ^ 2) ∂temperedJumpPairMeasure s

/-- A normal contraction decreases the full energy with constant exactly one. The output
may be *any* representative of the pointwise composition. -/
theorem temperedJumpExtendedEnergy_contraction {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] (s : ℝ) {u : ℝ → E} {v : ℝ → F}
    {C : E → F} (hC : LipschitzWith 1 C) (h0 : C 0 = 0) (hv : v =ᵐ[volume] C ∘ u) :
    temperedJumpExtendedEnergy s v ≤ temperedJumpExtendedEnergy s u := by
  unfold temperedJumpExtendedEnergy
  apply add_le_add
  · apply lintegral_mono_ae
    filter_upwards [hv] with x hx
    apply ENNReal.ofReal_le_ofReal
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simpa [hx, Function.comp_apply, h0] using hC.norm_sub_le (u x) 0
  · refine mul_le_mul_right ?_ _
    apply lintegral_mono_ae
    filter_upwards [temperedJumpPairMeasure_sub_congr_ae s hv] with z hz
    apply ENNReal.ofReal_le_ofReal
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simpa [hz, Function.comp_apply] using hC.norm_sub_le (u z.1) (u z.2)

/-- Normal contractions preserve square integrability of both the function and its jumps,
including when the contracted representative is changed on a volume-null set. -/
theorem temperedJump_memLp_contraction {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] (s : ℝ) {u : ℝ → E} {v : ℝ → F}
    {C : E → F} (hC : LipschitzWith 1 C) (h0 : C 0 = 0) (hv : v =ᵐ[volume] C ∘ u)
    (hu : MemLp u 2 volume)
    (hj : MemLp (fun z : ℝ × ℝ ↦ u z.1 - u z.2) 2 (temperedJumpPairMeasure s)) :
    MemLp v 2 volume ∧ MemLp (fun z : ℝ × ℝ ↦ v z.1 - v z.2) 2 (temperedJumpPairMeasure s) := by
  have hm := (memLp_congr_ae hv).2 (hC.comp_memLp h0 hu)
  refine ⟨hm, hj.of_le ?_ ?_⟩
  · exact (hm.aestronglyMeasurable.comp_quasiMeasurePreserving
      (temperedJumpPairMeasure_quasiMeasurePreserving_fst s)).sub
      (hm.aestronglyMeasurable.comp_quasiMeasurePreserving
        (temperedJumpPairMeasure_quasiMeasurePreserving_snd s))
  · filter_upwards [temperedJumpPairMeasure_sub_congr_ae s hv] with z hz
    simpa [hz, Function.comp_apply] using hC.norm_sub_le (u z.1) (u z.2)

/-- In particular the positive part contracts the real energy on its finite domain. -/
theorem temperedJumpExtendedEnergy_posPart_le (s : ℝ) (u : ℝ → ℝ) :
    temperedJumpExtendedEnergy s (fun x ↦ max (u x) 0) ≤ temperedJumpExtendedEnergy s u := by
  have h : LipschitzWith 1 (fun x : ℝ ↦ max x 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [Real.dist_eq] using abs_max_sub_max_le_abs x y 0
  exact temperedJumpExtendedEnergy_contraction s h (by simp) (Filter.EventuallyEq.rfl)

end RiemannMasullo
