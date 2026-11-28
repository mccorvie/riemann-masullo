module

public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.NuclearFiniteQuotient
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! # Distance from compact operators forced by finite quotient traces -/

public noncomputable section
open Set Function Module Metric
namespace RiemannMasullo
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Compact Hilbert operators admit nuclear approximants in operator norm. -/
theorem exists_nuclear_opNorm_approximation (A : H →L[ℂ] H) (hA : IsCompactOperator A)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : H →L[ℂ] H, IsNuclearOperator F ∧ ‖A - F‖ ≤ ε := by
  classical
  let K := closure (A '' closedBall 0 1)
  have hK : IsCompact K := hA.isCompact_closure_image_closedBall 1
  obtain ⟨s, hs, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded ε hε
  let V := Submodule.span ℂ s
  let : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ hs
  let b := stdOrthonormalBasis ℂ V
  have hP : IsNuclearOperator V.starProjection := by
    rw [b.starProjection_eq_sum_rankOne]
    exact (nuclearEndomorphisms H).sum_mem (fun i _ ↦ isNuclearOperator_smulRight _ _)
  refine ⟨V.starProjection.comp A, ?_, ?_⟩
  · exact mul_mem_nuclearEndomorphisms_right A ⟨V.starProjection,hP⟩
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
    intro x hx
    have hxK : A x ∈ K := subset_closure ⟨x, by simp only [mem_closedBall, dist_zero_right, hx, le_refl], rfl⟩
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hxK)
    change ‖A x - V.starProjection (A x)‖ ≤ ε
    rw [← dist_eq_norm, V.dist_starProjection_eq_infDist]
    exact (Metric.infDist_le_dist_of_mem (Submodule.subset_span hy : y ∈ V)).trans hxy.le

/-- Arbitrarily large finite quotients with a fixed diagonal obstruct approximation
by compact operators in the original operator norm. -/
theorem norm_sub_compact_ge_of_finite_quotient_diagonal
    (A : H →L[ℂ] H) (c : ℂ)
    (L : ∀ m : ℕ, H →L[ℂ] (Fin m → ℂ)) (hL : ∀ m, Surjective (L m))
    (B : ∀ m : ℕ, (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hAB : ∀ m x, L m (A x) = B m (L m x))
    (hdiag : ∀ m (i : Fin m), B m (Pi.single i 1) i = c)
    (K : H →L[ℂ] H) (hK : IsCompactOperator K) :
    ‖c‖ ≤ ‖A-K‖ := by
  by_contra hb
  have hpos : 0 < (‖c‖ - ‖A-K‖) / 2 := by linarith
  obtain ⟨F,hF,hKF⟩ := exists_nuclear_opNorm_approximation K hK _ hpos
  have hAF : ‖A-F‖ ≤ ‖A-K‖ + (‖c‖ - ‖A-K‖) / 2 :=
    (norm_sub_le_norm_sub_add_norm_sub A K F).trans (add_le_add le_rfl hKF)
  have hgap : 0 < ‖c‖ - ‖A-F‖ := by linarith
  obtain ⟨m,hm⟩ := exists_nat_gt (traceNorm ⟨F,hF⟩ / (‖c‖ - ‖A-F‖))
  have hbound := finite_quotient_diagonal_le_nuclear_approximation m (L m) (hL m)
    A F hF (B m) (hAB m) c (hdiag m)
  have hmul := (div_lt_iff₀ hgap).mp hm
  rw [mul_sub] at hmul
  linarith

end RiemannMasullo
