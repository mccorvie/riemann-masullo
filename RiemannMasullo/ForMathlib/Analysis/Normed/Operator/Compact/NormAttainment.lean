module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Norm attainment for compact operators on Hilbert spaces
-/

public section

namespace RiemannMasullo

open scoped InnerProductSpace

/-- A compact operator on a nontrivial complex Hilbert space attains its norm at a
unit eigenvector of its adjoint composed with itself. -/
theorem exists_unit_norm_eq_opNorm_of_isCompactOperator
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [Nontrivial E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (hT : IsCompactOperator T) :
    ∃ x : E, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖ ∧
      T.adjoint (T x) = (↑‖T‖ ^ 2 : ℂ) • x := by
  by_cases hzero : T = 0
  · obtain ⟨x, hx⟩ := exists_ne (0 : E)
    refine ⟨(↑‖x‖ : ℂ)⁻¹ • x, norm_smul_inv_norm hx, ?_, ?_⟩ <;> simp [hzero]
  let B := T.adjoint ∘L T
  have hB : IsCompactOperator B := hT.clm_comp T.adjoint
  have hBnorm : ‖B‖ = ‖T‖ ^ 2 := by
    simpa only [B, pow_two] using T.norm_adjoint_comp_self
  have hBpos : 0 ≤ B :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr T.isPositive_adjoint_comp_self
  have hspec : (↑‖B‖ : ℂ) ∈ spectrum ℂ B :=
    spectrum.algebraMap_mem ℂ (CStarAlgebra.norm_mem_spectrum_of_nonneg B hBpos)
  have hμ : (↑‖B‖ : ℂ) ≠ 0 := by
    simp [hBnorm, hzero]
  obtain ⟨y, hy⟩ := ((hB.hasEigenvalue_iff_mem_spectrum hμ).mpr hspec).exists_hasEigenvector
  obtain ⟨hy, hy0⟩ := Module.End.hasEigenvector_iff.mp hy
  let x : E := (↑‖y‖ : ℂ)⁻¹ • y
  have hx : ‖x‖ = 1 := norm_smul_inv_norm hy0
  have heig : B x = (↑‖T‖ ^ 2 : ℂ) • x := by
    have hy' : B y = (↑‖B‖ : ℂ) • y := Module.End.mem_eigenspace_iff.mp hy
    dsimp only [x]
    rw [map_smul, hy', smul_comm, hBnorm, Complex.ofReal_pow]
  refine ⟨x, hx, ?_, heig⟩
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hinner : RCLike.re ⟪x, B x⟫_ℂ = ‖T x‖ ^ 2 := by
    change RCLike.re ⟪x, T.adjoint (T x)⟫_ℂ = _
    rw [T.adjoint_inner_right, ← norm_sq_eq_re_inner]
  rw [← hinner, heig, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x, hx]
  simp [← Complex.ofReal_pow]

end RiemannMasullo
