module

public import RiemannMasullo.Ch12_TraceGeometric.ThetaPrimitiveLargeSieve
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Primitive character averages of complete rational Jacobi cells

At a fixed cutoff the four Jacobi sign cells have disjoint support. Applying the primitive
Dirichlet large sieve to each and adding charges the von Mangoldt energy only once.
The auxiliary integers can be arbitrary, including values whose Jacobi symbols vanish.
-/

open Finset ArithmeticFunction
open scoped Classical

public noncomputable section

namespace RiemannMasullo

/-- The complex rational Riesz sum over one complete Jacobi sign cell, with its factor four.
The sign selected by `true` is positive. The integer sum includes every prime power. -/
@[expose] def dirichletJacobiCellRow {m : ℕ} (χ : DirichletCharacter ℂ m)
    (T : ℕ) (x : ℝ) (u v : ℕ) (a b : Bool) : ℂ :=
  4 * dirichletThetaRow χ ((Ioc 0 T).filter (fun n ↦
      (jacobiSym u n : ℝ) = (if a then 1 else -1) ∧
      (jacobiSym v n : ℝ) = (if b then 1 else -1)))
    (fun n ↦ ((vonMangoldt n * max (x - n) 0 : ℝ) : ℂ))

private theorem dirichletJacobiCell_weight_energy (T : ℕ) (hT : 1 ≤ T) (x : ℝ) (hx : x ≤ T) :
    (∑ n ∈ Ioc 0 T, ‖((vonMangoldt n * max (x - n) 0 : ℝ) : ℂ)‖ ^ 2) ≤
      7 * (T : ℝ)^3 * Real.log (2 * T) := by
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  have hpsi : ∑ n ∈ Ioc 0 T, vonMangoldt n ≤ 7 * (T : ℝ) := by
    have h := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg T : 0 ≤ (T : ℝ))
    rw [Chebyshev.psi, Nat.floor_natCast] at h
    apply h.trans (mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg T))
    linarith [Real.log_le_sub_one_of_pos (show 0 < (4 : ℝ) by norm_num)]
  calc
    _ ≤ ∑ n ∈ Ioc 0 T, vonMangoldt n * (Real.log (2 * T) * (T : ℝ)^2) := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hn0, hnT⟩ := mem_Ioc.mp hn
      have hw : 0 ≤ max (x - (n : ℝ)) 0 := le_max_right _ _
      have hcut : max (x - (n : ℝ)) 0 ≤ T :=
        max_le ((sub_le_self _ (Nat.cast_nonneg n)).trans hx) (Nat.cast_nonneg T)
      have hnT' : (n : ℝ) ≤ T := by exact_mod_cast hnT
      have hm : vonMangoldt n ≤ Real.log (2 * T) :=
        vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast hn0) (by linarith))
      rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg vonMangoldt_nonneg hw), mul_pow,
        ← mul_assoc]
      exact mul_le_mul (by simpa only [pow_two] using mul_le_mul_of_nonneg_left hm vonMangoldt_nonneg)
        (pow_le_pow_left₀ hw hcut 2) (sq_nonneg _) (mul_nonneg vonMangoldt_nonneg hlog)
    _ = (∑ n ∈ Ioc 0 T, vonMangoldt n) * (Real.log (2 * T) * (T : ℝ)^2) :=
      (sum_mul ..).symm
    _ ≤ (7 * T) * (Real.log (2 * T) * (T : ℝ)^2) :=
      mul_le_mul_of_nonneg_right hpsi (mul_nonneg hlog (sq_nonneg _))
    _ = _ := by ring

/-- For any two auxiliary integers, the sum of the squared complete Jacobi rows over the
four signs and every primitive Dirichlet character of conductor at most `C`. -/
theorem dirichletJacobiCellRow_primitive_sum_sq
    (C T : ℕ) (hC : 0 < C) (hT : 1 ≤ T) (x : ℝ) (hx : x ≤ T) (u v : ℕ) :
    (∑ m ∈ range C, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (m + 1))).filter (·.IsPrimitive),
      ∑ s : Bool × Bool, ‖dirichletJacobiCellRow χ T x u v s.1 s.2‖ ^ 2) ≤
      112 * ((C : ℝ)^2 + Real.pi * T) * (T : ℝ)^3 * Real.log (2 * T) := by
  let P (m : ℕ) := (univ : Finset (DirichletCharacter ℂ (m + 1))).filter (·.IsPrimitive)
  let sign (a : Bool) : ℝ := if a then 1 else -1
  let cell (s : Bool × Bool) := (Ioc 0 T).filter fun n ↦
    (jacobiSym u n : ℝ) = sign s.1 ∧ (jacobiSym v n : ℝ) = sign s.2
  let f (n : ℕ) : ℂ := (vonMangoldt n * max (x - n) 0 : ℝ)
  let A := (C : ℝ)^2 + Real.pi * T
  have hA : 0 ≤ A := add_nonneg (sq_nonneg _) (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg T))
  have hsieve (s : Bool × Bool) :
      (∑ m ∈ range C, ∑ χ ∈ P m, ‖dirichletThetaRow χ (cell s) f‖ ^ 2) ≤
        A * ∑ n ∈ cell s, ‖f n‖ ^ 2 := by
    have h := dirichletThetaRow_primitive_large_sieve C hC (cell s) f (Nat.zero_le T)
      (fun n hn ↦ ⟨Nat.zero_le n, (mem_Ioc.mp (mem_filter.mp hn).1).2⟩)
    apply le_trans _ (by simpa only [Nat.cast_zero, sub_zero, P, A] using h)
    apply sum_le_sum
    intro m _
    apply le_mul_of_one_le_left (sum_nonneg (fun χ _ ↦ sq_nonneg _))
    exact (one_le_div (by exact_mod_cast Nat.totient_pos.mpr (Nat.succ_pos m))).mpr
      (by exact_mod_cast Nat.totient_le (m + 1))
  have hrow (s : Bool × Bool) :
      (∑ m ∈ range C, ∑ χ ∈ P m, ‖dirichletJacobiCellRow χ T x u v s.1 s.2‖ ^ 2) ≤
        (16 * A) * ∑ n ∈ cell s, ‖f n‖ ^ 2 := by
    change (∑ m ∈ range C, ∑ χ ∈ P m, ‖(4 : ℂ) * dirichletThetaRow χ (cell s) f‖ ^ 2) ≤ _
    simp only [norm_mul, Complex.norm_ofNat, mul_pow, ← mul_sum]
    calc _ ≤ 4 ^ 2 * (A * ∑ n ∈ cell s, ‖f n‖ ^ 2) :=
              mul_le_mul_of_nonneg_left (hsieve s) (by norm_num)
         _ = _ := by ring
  have hinj : Function.Injective sign := by
    intro a b h
    cases a <;> cases b <;> norm_num [sign] at *
  have hdis : Set.PairwiseDisjoint (↑(univ : Finset (Bool × Bool))) cell := by
    intro s _ t _ hst
    apply Finset.disjoint_left.mpr
    intro n hs ht
    obtain ⟨hs₁, hs₂⟩ := (mem_filter.mp hs).2
    obtain ⟨ht₁, ht₂⟩ := (mem_filter.mp ht).2
    exact hst (Prod.ext (hinj (hs₁.symm.trans ht₁)) (hinj (hs₂.symm.trans ht₂)))
  have hpartition : (∑ s : Bool × Bool, ∑ n ∈ cell s, ‖f n‖ ^ 2) ≤
      ∑ n ∈ Ioc 0 T, ‖f n‖ ^ 2 := by
    rw [← sum_biUnion hdis]
    apply sum_le_sum_of_subset_of_nonneg _ (fun n _ _ ↦ sq_nonneg _)
    intro n hn
    obtain ⟨s, _, hs⟩ := mem_biUnion.mp hn
    exact (mem_filter.mp hs).1
  calc
    _ = ∑ m ∈ range C, ∑ s : Bool × Bool, ∑ χ ∈ P m,
        ‖dirichletJacobiCellRow χ T x u v s.1 s.2‖ ^ 2 :=
      sum_congr rfl (fun m _ ↦ sum_comm)
    _ = ∑ s : Bool × Bool, ∑ m ∈ range C, ∑ χ ∈ P m,
        ‖dirichletJacobiCellRow χ T x u v s.1 s.2‖ ^ 2 := sum_comm
    _ ≤ ∑ s : Bool × Bool, (16 * A) * ∑ n ∈ cell s, ‖f n‖ ^ 2 :=
      sum_le_sum (fun s _ ↦ hrow s)
    _ = (16 * A) * ∑ s : Bool × Bool, ∑ n ∈ cell s, ‖f n‖ ^ 2 := (mul_sum ..).symm
    _ ≤ (16 * A) * (7 * (T : ℝ)^3 * Real.log (2 * T)) :=
      mul_le_mul_of_nonneg_left (hpartition.trans (dirichletJacobiCell_weight_energy T hT x hx))
        (mul_nonneg (by norm_num) hA)
    _ = _ := by dsimp only [A]; ring

end RiemannMasullo
