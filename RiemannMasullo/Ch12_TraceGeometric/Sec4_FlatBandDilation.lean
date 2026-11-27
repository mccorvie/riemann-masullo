module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatLogHeat
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatPolarCutoff
import RiemannMasullo.Ch10_TraceSpectral.Sec4a

/-!
# Logarithmic dilation inside a sharp frequency band

A heat average of a bounded band compression uses the smaller of two dilated
frequency cutoffs. Trace cyclicity identifies its exact interval for each shift.
-/

open Filter MeasureTheory Set
open scoped CompactlySupported InnerProductSpace NNReal Topology
@[expose] public noncomputable section
namespace RiemannMasullo.FlatPolar

local notation "ν" => volume.restrict (Ioi (0 : ℝ))
local notation "H" => Lp ℂ 2 ν

private theorem bandCut_inter (B b : ℝ) (f : H) :
    spatialCutoff 0 B (spatialCutoff 0 b f) = spatialCutoff 0 (min B b) f := by
  apply Lp.ext
  filter_upwards [spatialCutoff_apply 0 B (spatialCutoff 0 b f),
    spatialCutoff_apply 0 b f, spatialCutoff_apply 0 (min B b) f] with x h₁ h₂ h₃
  rw [h₁, h₃]
  by_cases hx : x ∈ Ioc 0 B
  · rw [indicator_of_mem hx, h₂]
    by_cases hxb : x ∈ Ioc 0 b
    · have hm : x ∈ Ioc 0 (min B b) := ⟨hx.1, le_min hx.2 hxb.2⟩
      rw [indicator_of_mem hxb, indicator_of_mem hm]
    · have hm : x ∉ Ioc 0 (min B b) := fun h ↦ hxb ⟨h.1, h.2.trans (min_le_right _ _)⟩
      rw [indicator_of_notMem hxb, indicator_of_notMem hm]
  · have hm : x ∉ Ioc 0 (min B b) := fun h ↦ hx ⟨h.1, h.2.trans (min_le_left _ _)⟩
    rw [indicator_of_notMem hx, indicator_of_notMem hm]

/-- Compressing a normalized dilation on both sides cuts its input down to
the exact smaller band. This cutoff identity holds at every finite bandwidth. -/
theorem frequencyBand_dilation_compression (B r : ℝ) (hr : 0 < r) (f : H) :
    spatialCutoff 0 B (positiveRayDilation r hr (spatialCutoff 0 B f)) =
      positiveRayDilation r hr (spatialCutoff 0 (min B (r * B)) f) := by
  rw [spatialCutoff_positiveRayDilation, mul_zero, bandCut_inter, min_comm]

/-- The trace of a compressed bounded operator followed by a dilation is exactly the
trace of the dilated operator on the overlap band. Each side uses the actual nuclear
operator represented by its specified Hilbert-space map. -/
theorem hilbertTrace_frequencyBand_comp_dilation (B r : ℝ) (hr : 0 < r)
    (T : H →L[ℂ] H) (A A' : nuclearEndomorphisms H)
    (hA : ∀ f, A.val f = spatialCutoff 0 B (T (spatialCutoff 0 B f)))
    (hA' : ∀ f, A'.val f = spatialCutoff 0 (min B (r * B))
      (T (positiveRayDilation r hr (spatialCutoff 0 (min B (r * B)) f)))) :
    let D : H →L[ℂ] H := positiveRayDilation r hr
    hilbertTrace ⟨A.val * D, mul_mem_nuclearEndomorphisms_right D A⟩ = hilbertTrace A' := by
  let D : H →L[ℂ] H := positiveRayDilation r hr
  let E := spatialCutoff 0 B
  let E' := spatialCutoff 0 (min B (r * B))
  let U : nuclearEndomorphisms H := ⟨A.val * D, mul_mem_nuclearEndomorphisms_right D A⟩
  let V : nuclearEndomorphisms H := ⟨U.val * E, mul_mem_nuclearEndomorphisms_right E U⟩
  have hEU : (⟨E * U.val, mul_mem_nuclearEndomorphisms_left E U⟩ : nuclearEndomorphisms H) = U := by
    apply Subtype.ext
    ext f : 1
    change E (A.val (D f)) = A.val (D f)
    rw [hA]
    exact (bandCut_inter B B _).trans (by rw [min_self])
  have hV (f : H) : V.val f = E (T (D (E' f))) := by
    change A.val (positiveRayDilation r hr (spatialCutoff 0 B f)) = _
    rw [hA, frequencyBand_dilation_compression]
    rfl
  have hVE' : (⟨V.val * E', mul_mem_nuclearEndomorphisms_right E' V⟩ : nuclearEndomorphisms H) = V := by
    apply Subtype.ext
    ext f : 1
    change V.val (E' f) = V.val f
    rw [hV, hV]
    simp [E', bandCut_inter]
  have hE'V : (⟨E' * V.val, mul_mem_nuclearEndomorphisms_left E' V⟩ : nuclearEndomorphisms H) = A' := by
    apply Subtype.ext
    ext f : 1
    change E' (V.val f) = A'.val f
    rw [hV, hA']
    simp [E', E, D, bandCut_inter]
  calc
    hilbertTrace U = hilbertTrace ⟨E * U.val, mul_mem_nuclearEndomorphisms_left E U⟩ := congrArg _ hEU.symm
    _ = hilbertTrace V := spectralRestriction_cyclic E U
    _ = hilbertTrace ⟨V.val * E', mul_mem_nuclearEndomorphisms_right E' V⟩ := congrArg _ hVE'.symm
    _ = hilbertTrace ⟨E' * V.val, mul_mem_nuclearEndomorphisms_left E' V⟩ := (spectralRestriction_cyclic E' V).symm
    _ = hilbertTrace A' := congrArg _ hE'V

end RiemannMasullo.FlatPolar
