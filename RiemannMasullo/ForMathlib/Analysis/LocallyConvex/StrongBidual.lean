module

public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.LocallyConvex.Montel
public import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.Complex.Convex
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.HahnBanach

/-! # Evaluation into the strong bidual and compact absolutely convex disks -/

public section

namespace RiemannMasullo
open Bornology Filter Function Metric Set Topology
open scoped ComplexOrder

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
  [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]

/-- In a Hausdorff barrelled polynormable space, evaluation is a topological
embedding into the strong bidual. -/
theorem isEmbedding_strongBidual_eval [BarrelledSpace ℂ E] :
    IsEmbedding (ContinuousLinearMap.applyₗ (E := E) ℂ (RingHom.id ℂ)) := by
  let j := ContinuousLinearMap.applyₗ (E := E) ℂ (RingHom.id ℂ)
  apply IsInducing.isEmbedding
  apply IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr
  apply le_antisymm
  · apply Tendsto.le_comap
    apply (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_ball).tendsto_right_iff.mpr
    rintro ⟨A, ε⟩ ⟨hA, hε⟩
    have hb (x : E) : IsVonNBounded ℂ (range fun φ : A ↦ φ.val x) := by
      change IsVonNBounded ℂ (range ((j x) ∘ (Subtype.val : A → StrongDual ℂ E)))
      rw [range_comp, Subtype.range_coe]
      exact hA.image (j x)
    have he := (PolynormableSpace.banach_steinhaus (𝓕 := fun φ : A ↦ φ.val) hb).equicontinuous (0 : E)
    filter_upwards [Metric.equicontinuousAt_iff_right.mp he ε hε] with x hx
    intro φ hφ
    simpa [dist_comm] using hx ⟨φ, hφ⟩
  · apply (PolynormableSpace.hasBasis_zero_ball ℂ E).ge_iff.mpr
    intro p hp
    let A := {φ : StrongDual ℂ E | ∀ x, ‖φ x‖ ≤ p x}
    have hA : IsVonNBounded ℂ A := by
      apply ContinuousLinearMap.isVonNBounded_iff.mpr
      intro S hS
      obtain ⟨C, _, hC⟩ := (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bounded.mp
        hS ⟨p, hp⟩
      apply (NormedSpace.isVonNBounded_iff ℂ).mpr
      refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
      rintro _ ⟨φ, hφ, x, hx, rfl⟩
      exact (hφ x).trans (hC x hx).le
    have hU := ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hA
      (ball_mem_nhds (0 : ℂ) zero_lt_one)
    apply mem_of_superset (preimage_mem_comap hU)
    intro x hx
    obtain ⟨φ, hφ, heq⟩ := exists_dual_norm_eq_seminorm p hp x
    rw [Seminorm.mem_ball_zero, ← heq]
    exact mem_ball_zero_iff.mp (hx hφ)

/-- In a polynormable space with the Heine–Borel property, each bounded set is
contained in a compact absolutely convex set containing zero. -/
theorem exists_compact_absConvex_superset [MontelSpace ℂ E] {S : Set E} (hS : IsVonNBounded ℂ S) :
    ∃ K : Set E, IsCompact K ∧ AbsConvex ℂ K ∧ insert 0 S ⊆ K := by
  let K := absConvexHull ℂ (insert 0 S)
  refine ⟨closure K, MontelSpace.isCompact_of_isClosed_of_isVonNBounded ℂ isClosed_closure ?_,
    absConvex_absConvexHull.closure, subset_absConvexHull.trans subset_closure⟩
  apply IsVonNBounded.closure
  apply (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bddAbove.mpr
  intro ⟨p, hp⟩
  obtain ⟨r, _, hr⟩ := (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bounded.mp
    (hS.insert 0) ⟨p, hp⟩
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  have hK : K ⊆ p.closedBall 0 r := absConvexHull_min
    (fun x hx ↦ p.mem_closedBall_zero.mpr (hr x hx).le)
    ⟨p.balanced_closedBall_zero r, convex_RCLike_iff_convex_real.mpr (p.convex_closedBall 0 r)⟩
  exact ⟨r, forall_mem_image.mpr fun x hx ↦ p.mem_closedBall_zero.mp (hK hx)⟩

end RiemannMasullo
