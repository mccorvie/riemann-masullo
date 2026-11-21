module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Rescaling summable real series -/

public section

open Filter Topology

namespace RiemannMasullo

/-- A nonnegative summable sequence stays summable after division by a suitable
positive null sequence. -/
theorem exists_pos_tendsto_zero_summable_div {a : ℕ → ℝ} (ha : Summable a)
    (ha₀ : ∀ n, 0 ≤ a n) :
    ∃ d : ℕ → ℝ, (∀ n, 0 < d n) ∧ Tendsto d atTop (𝓝 0) ∧
      Summable (fun n ↦ a n / d n) := by
  -- Adding a geometric series ensures that the tails are strictly positive.
  let b (n : ℕ) := a n + (1 / 2 : ℝ) ^ n
  have hb : Summable b := ha.add (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hb₀ (n : ℕ) : 0 < b n := add_pos_of_nonneg_of_pos (ha₀ n) (by positivity)
  let t (n : ℕ) := ∑' k : ℕ, b (k + n)
  have ht (n : ℕ) : 0 < t n :=
    ((summable_nat_add_iff n).mpr hb).tsum_pos (fun k ↦ (hb₀ (k + n)).le) 0 (hb₀ (0 + n))
  have ht_add (n : ℕ) : t n = b n + t (n + 1) := by
    simpa only [t, zero_add, Nat.add_right_comm, Nat.add_assoc] using
      ((summable_nat_add_iff n).mpr hb).tsum_eq_zero_add
  let s (n : ℕ) := Real.sqrt (t n)
  have hs : Tendsto s atTop (𝓝 0) := by
    simpa only [s, t, Real.sqrt_zero] using (tendsto_sum_nat_add b).sqrt
  let d (n : ℕ) := s n + s (n + 1)
  have hd (n : ℕ) : 0 < d n := add_pos (Real.sqrt_pos_of_pos (ht _)) (Real.sqrt_pos_of_pos (ht _))
  refine ⟨d, hd, ?_, ?_⟩
  · simpa only [d, Function.comp_apply, zero_add] using hs.add (hs.comp (tendsto_add_atTop_nat 1))
  · refine summable_of_sum_range_le (c := s 0) (fun n ↦ div_nonneg (ha₀ n) (hd n).le) fun N ↦ ?_
    calc
      _ ≤ ∑ n ∈ Finset.range N, (s n - s (n + 1)) := by
        refine Finset.sum_le_sum fun n _ ↦ (div_le_iff₀ (hd n)).mpr ?_
        dsimp [d, s]
        nlinarith [Real.mul_self_sqrt (ht n).le, Real.mul_self_sqrt (ht (n + 1)).le,
          ht_add n, show a n ≤ b n from le_add_of_nonneg_right (by positivity)]
      _ ≤ s 0 := by
        rw [Finset.sum_range_sub']
        exact sub_le_self _ (Real.sqrt_nonneg _)

end RiemannMasullo
