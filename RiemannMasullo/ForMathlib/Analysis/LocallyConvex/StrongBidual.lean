module

public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.LocallyConvex.Montel
public import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.LocallyConvex.WeakDual
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

/-- In a Hausdorff polynormable Montel space, every continuous linear functional
on the strong dual is evaluation at a vector of the original space. -/
theorem surjective_strongBidual_eval [MontelSpace ℂ E] :
    Surjective (ContinuousLinearMap.applyₗ (E := E) ℂ (RingHom.id ℂ)) := by
  let D := StrongDual ℂ E
  let j := ContinuousLinearMap.applyₗ (E := E) ℂ (RingHom.id ℂ)
  let B := topDualPairing ℂ D
  intro l
  have hnear : l ⁻¹' Metric.ball 0 1 ∈ 𝓝 (0 : D) :=
    l.continuous.continuousAt.preimage_mem_nhds (by simpa using ball_mem_nhds (0 : ℂ) zero_lt_one)
  obtain ⟨⟨S, r⟩, ⟨hS, hr⟩, hsub⟩ :=
    (ContinuousLinearMap.hasBasis_nhds_zero_of_basis
      (σ := RingHom.id ℂ) (Metric.nhds_basis_ball (x := (0 : ℂ)))).mem_iff.mp hnear
  let c : ℂ := ((r / 2)⁻¹ : ℝ)
  obtain ⟨K, hK, habs, hSK⟩ :=
    exists_compact_absConvex_superset (hS.image (c • ContinuousLinearMap.id ℂ E))
  let jWeak (x : E) : WeakBilin B := j x
  let C := jWeak '' K
  have hj : Continuous jWeak :=
    WeakBilin.continuous_of_continuous_eval B fun φ ↦ φ.continuous
  have hC : IsClosed C :=
    letI : T2Space (WeakBilin B) :=
      (WeakBilin.isEmbedding (B := B) ContinuousLinearMap.coe_injective).t2Space
    (hK.image hj).isClosed
  have haC : AbsConvex ℂ C := ⟨habs.1.image j, habs.2.linear_image j⟩
  have hzC : 0 ∈ C := ⟨0, hSK (mem_insert _ _), map_zero j⟩
  by_contra hl
  have hnot : l ∉ C := fun ⟨x, _, hx⟩ ↦ hl ⟨x, hx⟩
  let : PolynormableSpace ℂ (WeakBilin B) := B.weakBilin_withSeminorms.toPolynormableSpace
  obtain ⟨f, hf, hfl⟩ := exists_dual_norm_le_one_lt_of_notMem hC haC hzC hnot
  obtain ⟨φ, rfl⟩ := LinearMap.dualEmbedding_surjective B f
  have hsmall : φ ∈ {g : D | ∀ x ∈ S, g x ∈ Metric.ball 0 r} := by
    intro x hx
    have hKx : c • x ∈ K := hSK (mem_insert_of_mem _ (mem_image_of_mem _ hx))
    have hφ := hf _ (mem_image_of_mem jWeak hKx)
    change ‖φ (c • x)‖ ≤ 1 at hφ
    rw [map_smul, norm_smul, show ‖c‖ = (r / 2)⁻¹ from
      Complex.norm_of_nonneg (inv_nonneg.mpr (half_pos hr).le),
      ← div_eq_inv_mul, div_le_iff₀ (half_pos hr), one_mul] at hφ
    exact mem_ball_zero_iff.mpr (hφ.trans_lt (half_lt_self hr))
  exact (not_lt_of_ge (mem_ball_zero_iff.mp (hsub hsmall)).le) hfl

end RiemannMasullo
