module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.JordanSum

public section

namespace RiemannMasullo.Selberg

private theorem gcd_rpow_eq_sum (p : ℝ) (hp : 0 < p) {a c M : ℕ} (ha : 0 < a)
    (haM : a ≤ M) :
    (a.gcd c : ℝ) ^ p = ∑ r ∈ D M, if r ∣ a ∧ r ∣ c then jordan p r else 0 := by
  have hg := Nat.gcd_pos_of_pos_left c ha
  rw [← (jordan_sum p hp _ hg).1, ← Finset.sum_filter]
  congr 1
  ext r
  simp only [Nat.mem_divisors, Nat.dvd_gcd_iff, Finset.mem_filter, D, Finset.mem_Icc]
  exact ⟨fun ⟨h, _⟩ ↦ ⟨⟨Nat.pos_of_dvd_of_pos h.1 ha, (Nat.le_of_dvd ha h.1).trans haM⟩, h⟩,
    fun h ↦ ⟨h.2, hg.ne'⟩⟩

private theorem fourSum_pair_mul (N : ℕ) (f : ℕ → ℕ → ℝ) :
    (fourSum N fun k l m v ↦ f k v * f m l) = (∑ k ∈ D N, ∑ v ∈ D N, f k v)^2 := by
  have swap : (∑ l ∈ D N, ∑ m ∈ D N, f m l) = ∑ m ∈ D N, ∑ l ∈ D N, f m l :=
    Finset.sum_comm
  simp only [fourSum, ← Finset.sum_mul, ← Finset.mul_sum, swap, pow_two]

/-- Card 11. At each positive power the four-index energy is the sum of the squared divisor rows
through N², weighted by the Jordan totient.
Titchmarsh, §10.11, p. 271, square of the row. -/
theorem energy_rows (N : ℕ) (b : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    energy N b p = ∑ r ∈ D (N*N), jordan p r * (row N b p r)^2 := by
  let rowTerm (r k v : ℕ) := if r ∣ k * v then b k * b v / ((k : ℝ) ^ p * v) else 0
  calc
    energy N b p = fourSum N (fun k l m v ↦
        ∑ r ∈ D (N*N), jordan p r * (rowTerm r k v * rowTerm r m l)) := by
      unfold energy fourSum
      refine Finset.sum_congr rfl fun k hk ↦ Finset.sum_congr rfl fun l _ ↦
        Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun v hv ↦ ?_
      obtain ⟨hk₁, hkN⟩ := Finset.mem_Icc.mp hk
      obtain ⟨hv₁, hvN⟩ := Finset.mem_Icc.mp hv
      dsimp only [ratio]
      rw [Nat.mul_comm l m, Real.div_rpow (by positivity) (by positivity) p,
        Real.mul_rpow (Nat.cast_nonneg k) (Nat.cast_nonneg m),
        gcd_rpow_eq_sum p hp (Nat.mul_pos hk₁ hv₁) (Nat.mul_le_mul hkN hvN),
        Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      by_cases h₁ : r ∣ k * v <;> by_cases h₂ : r ∣ m * l <;>
        simp [h₁, h₂, rowTerm, coef, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = ∑ r ∈ D (N*N), jordan p r * fourSum N (fun k l m v ↦ rowTerm r k v * rowTerm r m l) := by
      simp only [fourSum, Finset.mul_sum, Finset.sum_comm (s := D N) (t := D (N*N))]
    _ = _ := by simp only [fourSum_pair_mul, row, Finset.sum_filter, rowTerm]

end RiemannMasullo.Selberg
