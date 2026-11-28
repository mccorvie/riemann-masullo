module

public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.QuotientLayer
public import Mathlib.Tactic.NoncommRing

/-! # Compression along invariant closed-subspace towers -/

public noncomputable section
namespace RiemannMasullo

private theorem invariant_above {R : Type*} [Ring R] (P Q A : R)
    (hPQ : P * Q = Q) (hQA : Q * (A * Q) = A * Q) : P * (A * Q) = A * Q := by
  calc
    _ = P * (Q * (A * Q)) := by rw [hQA]
    _ = (P * Q) * (A * Q) := (mul_assoc _ _ _).symm
    _ = _ := by rw [hPQ, hQA]

private theorem difference_idempotent {R : Type*} [Ring R] (C D : R)
    (hCC : C * C = C) (hDD : D * D = D) (hCD : C * D = D) (hDC : D * C = D) :
    (C - D) * (C - D) = C - D := by
  simp only [sub_mul, mul_sub, hCC, hDD, hCD, hDC]
  noncomm_ring

private theorem compression_product {R : Type*} [Ring R] (C D A B : R)
    (hCC : C * C = C) (hDD : D * D = D) (hCD : C * D = D) (hDC : D * C = D)
    (hAD : D * (A * D) = A * D) (hBC : C * (B * C) = B * C)
    (hBD : D * (B * D) = B * D) :
    ((C-D)*A*(C-D))*((C-D)*B*(C-D)) = (C-D)*(A*B)*(C-D) := by
  let Q := C - D
  have hQQ : Q * Q = Q := difference_idempotent C D hCC hDD hCD hDC
  have hCAD := invariant_above C D A hCD hAD
  have hCBD := invariant_above C D B hCD hBD
  have hAC : Q * A * Q = Q * A * C := by
    dsimp only [Q]
    simp only [sub_mul, mul_sub, mul_assoc, hCAD, hAD]
    noncomm_ring
  have hBQ : C * (B * Q) = B * Q := by
    simp only [Q, mul_sub, hBC, hCBD]
  change (Q*A*Q)*(Q*B*Q) = Q*(A*B)*Q
  calc
    _ = (Q*A)*(Q*Q)*(B*Q) := by noncomm_ring
    _ = (Q*A)*Q*(B*Q) := by rw [hQQ]
    _ = (Q*A)*C*(B*Q) := by rw [hAC]
    _ = (Q*A)*(B*Q) := by rw [mul_assoc (Q*A) C, hBQ]
    _ = _ := by noncomm_ring

private theorem compression_deep {R : Type*} [Ring R] (C B D A : R)
    (hDD : D*D=D)
    (hCB : C*B=B) (hCD : C*D=D) (hDB : D*B=D) (hBD : B*D=D)
    (hAB : B*(A*B)=A*B) (hAD : D*(A*D)=A*D) :
    ((C-D)*A*(C-D))*(B-D) = (B-D)*A*(B-D) := by
  have hRP : (C-D)*(B-D)=B-D := by
    simp only [sub_mul, mul_sub, hCB, hCD, hDB, hDD]
    noncomm_ring
  have hCAB := invariant_above C B A hCB hAB
  have hCAD := invariant_above C D A hCD hAD
  have hBAD := invariant_above B D A hBD hAD
  calc
    _ = (C-D)*A*(B-D) := by rw [mul_assoc, hRP]
    _ = _ := by
      simp only [sub_mul, mul_sub, mul_assoc, hCAB, hCAD, hAB, hBAD]

private theorem compression_shallow {R : Type*} [Ring R] (C B D A : R)
    (hCC : C*C=C) (hBC : B*C=B) (hCD : C*D=D) (hBD : B*D=D)
    (hCB : C*B=B) (hAB : B*(A*B)=A*B) (hAD : D*(A*D)=A*D) :
    (C-B)*((C-D)*A*(C-D)) = (C-B)*A*(C-B) := by
  have hQR : (C-B)*(C-D)=C-B := by
    simp only [sub_mul, mul_sub, hCC, hCD, hBC, hBD]
    noncomm_ring
  have hCAB := invariant_above C B A hCB hAB
  have hCAD := invariant_above C D A hCD hAD
  have hBAD := invariant_above B D A hBD hAD
  calc
    _ = (C-B)*A*(C-D) := by rw [← mul_assoc, ← mul_assoc, hQR]
    _ = _ := by
      simp only [sub_mul, mul_sub, mul_assoc, hCAB, hCAD, hAB, hBAD]
      noncomm_ring

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance (M : ClosedSubmodule ℂ H) : IsClosed (M.toSubmodule : Set H) := M.isClosed

private theorem projection_above (M V : ClosedSubmodule ℂ H) (hVM : V ≤ M) :
    M.toSubmodule.starProjection * V.toSubmodule.starProjection = V.toSubmodule.starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.starProjection_eq_self_iff.mpr
  exact hVM (V.toSubmodule.orthogonalProjectionOnto x).property

private theorem projection_invariant (M : ClosedSubmodule ℂ H) (A : H →L[ℂ] H)
    (hA : ∀ x ∈ M, A x ∈ M) :
    M.toSubmodule.starProjection * (A * M.toSubmodule.starProjection) = A * M.toSubmodule.starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  exact Submodule.starProjection_eq_self_iff.mpr
    (hA _ (M.toSubmodule.orthogonalProjectionOnto x).property)

/-- Two-sided compression to the orthogonal difference of two nested closed spaces. -/
def closedLayerCompression (M V : ClosedSubmodule ℂ H) (A : H →L[ℂ] H) : H →L[ℂ] H :=
  (M.toSubmodule.starProjection - V.toSubmodule.starProjection) * A *
    (M.toSubmodule.starProjection - V.toSubmodule.starProjection)

theorem closedLayerCompression_def (M V : ClosedSubmodule ℂ H) (A : H →L[ℂ] H) :
    closedLayerCompression M V A =
      (M.toSubmodule.starProjection - V.toSubmodule.starProjection).comp
        (A.comp (M.toSubmodule.starProjection - V.toSubmodule.starProjection)) := by
  simp only [closedLayerCompression, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

theorem closedLayerCompression_add (M V : ClosedSubmodule ℂ H) (A B : H →L[ℂ] H) :
    closedLayerCompression M V (A+B) = closedLayerCompression M V A + closedLayerCompression M V B := by
  simp only [closedLayerCompression, mul_add, add_mul]

/-- Compression preserves products when both operators preserve the denominator
and the second preserves the numerator. -/
theorem closedLayerCompression_comp (M V : ClosedSubmodule ℂ H) (hVM : V ≤ M)
    (A B : H →L[ℂ] H) (hAV : ∀ x ∈ V, A x ∈ V)
    (hBM : ∀ x ∈ M, B x ∈ M) (hBV : ∀ x ∈ V, B x ∈ V) :
    closedLayerCompression M V (A.comp B) =
      (closedLayerCompression M V A).comp (closedLayerCompression M V B) := by
  exact (compression_product _ _ A B
    (Submodule.isIdempotentElem_starProjection M.toSubmodule)
    (Submodule.isIdempotentElem_starProjection V.toSubmodule)
    (projection_above M V hVM) (Submodule.starProjection_comp_starProjection_of_le hVM)
    (projection_invariant V A hAV) (projection_invariant M B hBM)
    (projection_invariant V B hBV)).symm

/-- In a three-stage tower, the new layer is invariant under the total compression. -/
theorem closedLayerCompression_deep_right (M B D : ClosedSubmodule ℂ H)
    (hDB : D ≤ B) (hBM : B ≤ M) (A : H →L[ℂ] H)
    (hAB : ∀ x ∈ B, A x ∈ B) (hAD : ∀ x ∈ D, A x ∈ D) :
    (closedLayerCompression M D A).comp
      (B.toSubmodule.starProjection - D.toSubmodule.starProjection) = closedLayerCompression B D A := by
  exact compression_deep _ _ _ A
    (Submodule.isIdempotentElem_starProjection D.toSubmodule)
    (projection_above M B hBM) (projection_above M D (hDB.trans hBM))
    (Submodule.starProjection_comp_starProjection_of_le hDB) (projection_above B D hDB)
    (projection_invariant B A hAB) (projection_invariant D A hAD)

/-- Projection onto the preceding relative level gives its original compression. -/
theorem closedLayerCompression_shallow_left (M B D : ClosedSubmodule ℂ H)
    (hDB : D ≤ B) (hBM : B ≤ M) (A : H →L[ℂ] H)
    (hAB : ∀ x ∈ B, A x ∈ B) (hAD : ∀ x ∈ D, A x ∈ D) :
    (M.toSubmodule.starProjection - B.toSubmodule.starProjection).comp
      (closedLayerCompression M D A) = closedLayerCompression M B A := by
  exact compression_shallow _ _ _ A
    (Submodule.isIdempotentElem_starProjection M.toSubmodule)
    (Submodule.starProjection_comp_starProjection_of_le hBM)
    (projection_above M D (hDB.trans hBM)) (projection_above B D hDB)
    (projection_above M B hBM) (projection_invariant B A hAB) (projection_invariant D A hAD)

/-- The compressed operator is supported on the relative layer on the right. -/
theorem closedLayerCompression_right (M D : ClosedSubmodule ℂ H) (hDM : D ≤ M)
    (A : H →L[ℂ] H) :
    (closedLayerCompression M D A).comp
      (M.toSubmodule.starProjection - D.toSubmodule.starProjection) = closedLayerCompression M D A := by
  have hR := difference_idempotent _ _ (Submodule.isIdempotentElem_starProjection M.toSubmodule)
    (Submodule.isIdempotentElem_starProjection D.toSubmodule) (projection_above M D hDM)
    (Submodule.starProjection_comp_starProjection_of_le hDM)
  change (_ * A * _) * _ = _ * A * _
  rw [mul_assoc, hR]

end Hilbert
end RiemannMasullo
