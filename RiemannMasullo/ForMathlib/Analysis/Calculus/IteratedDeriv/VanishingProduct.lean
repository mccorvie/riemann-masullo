module
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.Basic

public noncomputable section
open Function
open scoped ContDiff
namespace RiemannMasullo

private theorem iteratedDeriv_mul_vanishing {f g : ℝ → ℂ} {r : ℕ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hf0 : f 0 = 0)
    (hgz : ∀ k : ℕ, k < r → iteratedDeriv k g 0 = 0) :
    (∀ k : ℕ, k < r + 1 → iteratedDeriv k (fun x ↦ f x * g x) 0 = 0) ∧
      iteratedDeriv (r + 1) (fun x ↦ f x * g x) 0 =
        (r + 1 : ℕ) * deriv f 0 * iteratedDeriv r g 0 := by
  constructor
  · intro k hk
    rw [iteratedDeriv_fun_mul (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt]
    apply Finset.sum_eq_zero
    intro i hi
    have hiLe := Finset.mem_range.mp hi
    by_cases hi0 : i = 0
    · subst i
      simp [hf0]
    · have hkr : k - i < r := by omega
      rw [hgz _ hkr, mul_zero]
  · rw [iteratedDeriv_fun_mul (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt]
    rw [Finset.sum_eq_single 1]
    · simp only [Nat.choose_one_right, iteratedDeriv_one, Nat.add_sub_cancel]
    · intro i hi hi1
      have hiLe := Finset.mem_range.mp hi
      by_cases hi0 : i = 0
      · subst i
        simp [hf0]
      · have hkr : r + 1 - i < r := by omega
        rw [hgz _ hkr, mul_zero]
    · intro hi
      exact (hi (Finset.mem_range.mpr (by omega))).elim

/-- A finite product of functions vanishing at the origin has the expected
zero jet and first nonzero Leibniz coefficient, even with a smooth extra factor. -/
theorem iteratedDeriv_finset_prod_zero {ι : Type*} (T : Finset ι)
    (f : ι → ℝ → ℂ) (g : ℝ → ℂ)
    (hf : ∀ i ∈ T, ContDiff ℝ ∞ (f i)) (hg : ContDiff ℝ ∞ g)
    (hz : ∀ i ∈ T, f i 0 = 0) :
    (∀ k : ℕ, k < T.card → iteratedDeriv k (fun x ↦ (∏ i ∈ T, f i x) * g x) 0 = 0) ∧
      iteratedDeriv T.card (fun x ↦ (∏ i ∈ T, f i x) * g x) 0 =
        (T.card.factorial : ℂ) * (∏ i ∈ T, deriv (f i) 0) * g 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    have hsub := Finset.subset_insert i T
    have hft : ContDiff ℝ ∞ (fun x ↦ (∏ j ∈ T, f j x) * g x) :=
      (contDiff_prod (fun j hj ↦ hf j (hsub hj))).mul hg
    obtain ⟨hlower, htop⟩ := ih (fun j hj ↦ hf j (hsub hj)) (fun j hj ↦ hz j (hsub hj))
    obtain ⟨hl, ht⟩ := iteratedDeriv_mul_vanishing (hf i (Finset.mem_insert_self ..)) hft
      (hz i (Finset.mem_insert_self ..)) hlower
    have heq : (fun x ↦ (∏ j ∈ insert i T, f j x) * g x) =
        (fun x ↦ f i x * ((∏ j ∈ T, f j x) * g x)) := by
      ext x
      rw [Finset.prod_insert hi, mul_assoc]
    rw [heq, Finset.card_insert_of_notMem hi]
    refine ⟨hl, ?_⟩
    rw [ht, htop, Finset.prod_insert hi, Nat.factorial_succ]
    push_cast
    ring

end RiemannMasullo
