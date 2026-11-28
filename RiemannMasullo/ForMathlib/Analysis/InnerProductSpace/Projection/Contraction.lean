module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith

/-! # Orthogonal projection through a contraction isometric on a subspace -/

public noncomputable section

namespace RiemannMasullo

variable {𝕜 H G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- A contraction's adjoint recovers any vector whose norm the contraction
preserves. -/
theorem adjoint_apply_apply_eq_of_norm_preserved
    (T : H →L[𝕜] G) (hT : ‖T‖ ≤ 1) (v : H) (hv : ‖T v‖ = ‖v‖) :
    T.adjoint (T v) = v := by
  have hPair : inner 𝕜 (T.adjoint (T v)) v = inner 𝕜 v v := by
    rw [T.adjoint_inner_left]
    simp only [inner_self_eq_norm_sq_to_K, hv]
  have hNorm : ‖T.adjoint (T v)‖ ≤ ‖v‖ := by
    calc
      _ ≤ ‖T.adjoint‖ * ‖T v‖ := (T.adjoint).le_opNorm (T v)
      _ = ‖T‖ * ‖T v‖ := congrArg (· * ‖T v‖) (ContinuousLinearMap.adjoint.norm_map T)
      _ ≤ ‖T v‖ := mul_le_of_le_one_left (norm_nonneg _) hT
      _ = ‖v‖ := hv
  have hSqLe := pow_le_pow_left₀ (norm_nonneg _) hNorm 2
  have hExpand := norm_sub_sq (𝕜 := 𝕜) (T.adjoint (T v)) v
  rw [hPair, ← norm_sq_eq_re_inner (𝕜 := 𝕜) v] at hExpand
  have hZero : ‖T.adjoint (T v) - v‖ ^ 2 = 0 := by
    have hNonneg := sq_nonneg ‖T.adjoint (T v) - v‖
    linarith only [hExpand, hSqLe, hNonneg]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hZero))

/-- If a contraction is isometric on a subspace, pulling the projection onto
its image back through the adjoint gives the original projection. -/
theorem starProjection_eq_adjoint_comp_of_isometric_image
    (T : H →L[𝕜] G) (hT : ‖T‖ ≤ 1)
    (V : Submodule 𝕜 H) (R : Submodule 𝕜 G)
    [V.HasOrthogonalProjection] [R.HasOrthogonalProjection]
    (hIso : ∀ v ∈ V, ‖T v‖ = ‖v‖) (hR : R = V.map T.toLinearMap) :
    V.starProjection = T.adjoint.comp (R.starProjection.comp T) := by
  have hFix (v : H) (hv : v ∈ V) : T.adjoint (T v) = v :=
    adjoint_apply_apply_eq_of_norm_preserved T hT v (hIso v hv)
  apply ContinuousLinearMap.ext
  intro x
  let r := R.starProjection (T x)
  change V.starProjection x = T.adjoint r
  have hr : r ∈ V.map T.toLinearMap := by
    rw [← hR]
    exact R.starProjection_apply_mem (T x)
  obtain ⟨v, hv, hTv⟩ := Submodule.mem_map.mp hr
  change T v = r at hTv
  have hInv : T.adjoint r = v := hTv ▸ hFix v hv
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := V) (hInv.symm ▸ hv) ?_
  intro w hw
  have hTw : T w ∈ R := by
    rw [hR]
    exact Submodule.mem_map_of_mem (f := T.toLinearMap) hw
  have hPair : inner 𝕜 x w = inner 𝕜 (T x) (T w) := by
    rw [← T.adjoint_inner_right, hFix w hw]
  rw [inner_sub_left, hPair, T.adjoint_inner_left, ← inner_sub_left]
  exact Submodule.starProjection_inner_eq_zero (K := R) (T x) (T w) hTw

/-- The contraction intertwines the projections onto the subspace and its
exact isometric image. -/
theorem starProjection_comp_eq_comp_starProjection_of_isometric_image
    (T : H →L[𝕜] G) (hT : ‖T‖ ≤ 1)
    (V : Submodule 𝕜 H) (R : Submodule 𝕜 G)
    [V.HasOrthogonalProjection] [R.HasOrthogonalProjection]
    (hIso : ∀ v ∈ V, ‖T v‖ = ‖v‖) (hR : R = V.map T.toLinearMap) :
    R.starProjection.comp T = T.comp V.starProjection := by
  rw [starProjection_eq_adjoint_comp_of_isometric_image T hT V R hIso hR]
  apply ContinuousLinearMap.ext
  intro x
  let r := R.starProjection (T x)
  change r = T (T.adjoint r)
  have hr : r ∈ V.map T.toLinearMap := by
    rw [← hR]
    exact R.starProjection_apply_mem (T x)
  obtain ⟨v, hv, hTv⟩ := Submodule.mem_map.mp hr
  change T v = r at hTv
  rw [← hTv, adjoint_apply_apply_eq_of_norm_preserved T hT v (hIso v hv)]

/-- In the projection formula the adjoint may be replaced by any bounded map
that recovers vectors in the original subspace from their images. -/
theorem starProjection_eq_recovery_comp_of_isometric_image
    (T : H →L[𝕜] G) (J : G →L[𝕜] H) (hT : ‖T‖ ≤ 1)
    (V : Submodule 𝕜 H) (R : Submodule 𝕜 G)
    [V.HasOrthogonalProjection] [R.HasOrthogonalProjection]
    (hIso : ∀ v ∈ V, ‖T v‖ = ‖v‖) (hR : R = V.map T.toLinearMap)
    (hRecover : ∀ v ∈ V, J (T v) = v) :
    V.starProjection = J.comp (R.starProjection.comp T) := by
  rw [starProjection_eq_adjoint_comp_of_isometric_image T hT V R hIso hR]
  apply ContinuousLinearMap.ext
  intro x
  let r := R.starProjection (T x)
  change T.adjoint r = J r
  have hr : r ∈ V.map T.toLinearMap := by
    rw [← hR]
    exact R.starProjection_apply_mem (T x)
  obtain ⟨v, hv, hTv⟩ := Submodule.mem_map.mp hr
  change T v = r at hTv
  rw [← hTv, adjoint_apply_apply_eq_of_norm_preserved T hT v (hIso v hv), hRecover v hv]

end RiemannMasullo
