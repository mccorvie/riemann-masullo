module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public noncomputable section

open Set MeasureTheory
open scoped CompactlySupported

namespace RiemannMasullo

/-- A real linear functional on the range of a family of continuous functions on a nonempty
compact Hausdorff space is represented by a positive Radon measure of mass at most one
if it is bounded above by the pointwise supremum. The kernel condition needed to descend
to the range follows by applying the bound to a vector and its negative. -/
theorem exists_radon_of_le_iSup {K X : Type*} [TopologicalSpace K] [T2Space K]
    [CompactSpace K] [Nonempty K] [MeasurableSpace K] [BorelSpace K]
    [AddCommGroup X] [Module ℝ X] (J : X →ₗ[ℝ] C_c(K, ℝ)) (L : X →ₗ[ℝ] ℝ)
    (hL : ∀ x, L x ≤ ⨆ k, J x k) :
    ∃ μ : Measure K, μ.Regular ∧ μ.InnerRegular ∧ μ univ ≤ 1 ∧
      ∀ x, L x = ∫ k, J x k ∂μ := by
  let N (f : C_c(K, ℝ)) := ⨆ k, f k
  have hbdd (f : C_c(K, ℝ)) : BddAbove (range f) :=
    (isCompact_range f.continuous).bddAbove
  have hker : J.ker ≤ L.ker := by
    intro x hx
    have hx' := LinearMap.mem_ker.mp hx
    have hp := hL x
    have hn := hL (-x)
    simp [hx'] at hp hn
    exact LinearMap.mem_ker.mpr (le_antisymm hp hn)
  let l := (J.ker.liftQ L hker).comp J.quotKerEquivRange.symm.toLinearMap
  have hl (x : X) : l (J.rangeRestrict x) = L x := by
    have hx : J.quotKerEquivRange (Submodule.Quotient.mk x) = J.rangeRestrict x :=
      Subtype.ext (J.quotKerEquivRange_apply_mk x)
    simp [l, ← hx]
  obtain ⟨g, hg, hgN⟩ := exists_extension_of_le_sublinear ⟨J.range, l⟩ N
    (fun c hc f ↦ by
      change (⨆ k, c * f k) = c * (⨆ k, f k)
      apply le_antisymm
      · exact ciSup_le fun k ↦ mul_le_mul_of_nonneg_left (le_ciSup (hbdd f) k) hc.le
      · rw [mul_comm c, ← le_div_iff₀ hc]
        exact ciSup_le fun k ↦ (le_div_iff₀ hc).mpr
          ((mul_comm (f k) c).trans_le (le_ciSup (hbdd (c • f)) k)))
    (fun f g ↦ ciSup_le fun k ↦ add_le_add (le_ciSup (hbdd f) k) (le_ciSup (hbdd g) k))
    (fun ⟨_, x, rfl⟩ ↦ by
      change l (J.rangeRestrict x) ≤ N (J x)
      rw [hl]
      exact hL x)
  let Λ : C_c(K, ℝ) →ₚ[ℝ] ℝ :=
    { g with
      monotone' := fun f f' hff' ↦ by
        change g f ≤ g f'
        have hn := (hgN (f - f')).trans (ciSup_le fun k ↦ sub_nonpos.mpr (hff' k))
        exact sub_nonpos.mp (by simpa only [map_sub] using hn) }
  let μ := RealRMK.rieszMeasure Λ
  refine ⟨μ, inferInstance, inferInstance, ?_, fun x ↦ ?_⟩
  · let o : C_c(K, ℝ) := ⟨1, HasCompactSupport.of_compactSpace 1⟩
    exact (RealRMK.rieszMeasure_le_of_eq_one Λ (f := o) (fun _ ↦ zero_le_one)
      isCompact_univ (fun _ _ ↦ rfl)).trans (ENNReal.ofReal_le_one.mpr
        ((hgN o).trans (ciSup_le fun _ ↦ le_rfl)))
  · exact (hl x).symm.trans ((hg (J.rangeRestrict x)).symm.trans
      (RealRMK.integral_rieszMeasure Λ (J x)).symm)

end RiemannMasullo
