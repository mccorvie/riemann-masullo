module

public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Analysis.Complex.Basic

/-! # Surjectivity of finite continuous jet maps from triangular witnesses -/

public noncomputable section
namespace RiemannMasullo
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A triangular family of witnesses realizes every finite collection of continuous jets. -/
theorem exists_prescribed_finite_jets (L : ℕ → E →L[ℂ] ℂ)
    (hv : ∀ j : ℕ, ∃ v : E, L j v ≠ 0 ∧ ∀ i < j, L i v = 0)
    (m : ℕ) (y : ℕ → ℂ) : ∃ x : E, ∀ i < m, L i x = y i := by
  induction m with
  | zero => exact ⟨0, fun i hi ↦ (Nat.not_lt_zero i hi).elim⟩
  | succ m ih =>
    obtain ⟨x, hx⟩ := ih
    obtain ⟨v, hvm, hv0⟩ := hv m
    let c := (y m - L m x) / L m v
    refine ⟨x + c • v, fun i hi ↦ ?_⟩
    by_cases him : i = m
    · subst i
      simp only [map_add, map_smul, smul_eq_mul, c]
      rw [div_mul_cancel₀ _ hvm]
      rw [add_comm, sub_add_cancel]
    · have him' : i < m := lt_of_le_of_ne (Nat.le_of_lt_succ hi) him
      simp only [map_add, map_smul, smul_eq_mul, hv0 i him', mul_zero, add_zero, hx i him']

/-- The finite jet-coordinate map is onto when its rows have triangular witnesses. -/
theorem finiteJetMap_surjective (L : ℕ → E →L[ℂ] ℂ)
    (hv : ∀ j : ℕ, ∃ v : E, L j v ≠ 0 ∧ ∀ i < j, L i v = 0) (m : ℕ) :
    Function.Surjective (ContinuousLinearMap.pi (fun i : Fin m ↦ L i)) := by
  intro y
  let z (i : ℕ) : ℂ := if h : i < m then y ⟨i,h⟩ else 0
  obtain ⟨x,hx⟩ := exists_prescribed_finite_jets L hv m z
  refine ⟨x, funext fun i ↦ ?_⟩
  change L i x = y i
  simpa only [z, dite_eq_left i.isLt] using! hx i i.isLt

end RiemannMasullo
