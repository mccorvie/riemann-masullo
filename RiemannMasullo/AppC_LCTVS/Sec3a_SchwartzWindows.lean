module
public import RiemannMasullo.AppC_LCTVS.Sec3a_FiniteRank
public import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Cutoff
import Mathlib.Analysis.PSeries

@[expose] public noncomputable section
open Filter Function Set
open scoped SchwartzMap Topology BigOperators
namespace RiemannMasullo
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A continuous Schwartz family of Hilbert-space operators is nuclear at every
profile if compact frequency windows have a uniform quadratic rank bound.
No spacing hypothesis on the spectral points is needed. -/
theorem isNuclearOperator_schwartz_of_quadratic_window_rank
    (T : 𝓢(ℝ, ℂ) →L[ℝ] (H →L[ℂ] H))
    (C : ℝ) (hC : 0 ≤ C)
    (hrank : ∀ (R : ℝ), 0 ≤ R → ∀ p : 𝓢(ℝ, ℂ),
      (∀ t, p t ≠ 0 → |t| < R) →
      FiniteDimensional ℂ (T p).toLinearMap.range ∧
        (Module.finrank ℂ (T p).toLinearMap.range : ℝ) ≤ C * (1 + R) ^ 2)
    (f : 𝓢(ℝ, ℂ)) : IsNuclearOperator (T f) := by
  obtain ⟨q, hq, hlim, hrapid⟩ := schwartz_exists_rapid_compact_cutoffs f T
  obtain ⟨D, hD, herr⟩ := hrapid 6
  let A (n : ℕ) := T (q n)
  let B (n : ℕ) := A (n + 1) - A n
  have hb (n : ℕ) : FiniteDimensional ℂ (B n).toLinearMap.range ∧
      (Module.finrank ℂ (B n).toLinearMap.range : ℝ) ≤ 25 * C * ((n : ℝ) + 1) ^ 2 := by
    have hsupp (t : ℝ) (ht : (q (n + 1) - q n) t ≠ 0) : |t| < 2 * ((n : ℝ) + 2) := by
      by_cases hn : q (n + 1) t = 0
      · have ht' : q n t ≠ 0 := by intro hz; simp [hn, hz] at ht
        exact (hq n t ht').trans (by linarith)
      · have hh := hq (n + 1) t hn
        push_cast at hh
        linarith
    have h := hrank (2 * ((n : ℝ) + 2)) (by positivity) (q (n + 1) - q n) hsupp
    rw [show T (q (n + 1) - q n) = B n from map_sub T _ _] at h
    refine ⟨h.1, h.2.trans ?_⟩
    have hx : 1 + 2 * ((n : ℝ) + 2) ≤ 5 * ((n : ℝ) + 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    calc
      C * (1 + 2 * ((n : ℝ) + 2)) ^ 2 ≤ C * (5 * ((n : ℝ) + 1)) ^ 2 := by gcongr
      _ = _ := by ring
  have hn (n : ℕ) : ‖B n‖ ≤ 2 * D / ((n : ℝ) + 1) ^ 6 := by
    have hident : B n = T (q (n + 1) - f) - T (q n - f) := by
      dsimp [B, A]
      rw [map_sub, map_sub]
      abel
    rw [hident]
    have hmon : D / ((n + 1 : ℕ) + 1 : ℝ) ^ 6 ≤ D / ((n : ℝ) + 1) ^ 6 := by
      gcongr
      norm_num
    calc
      _ ≤ ‖T (q (n + 1) - f)‖ + ‖T (q n - f)‖ := norm_sub_le _ _
      _ ≤ D / ((n : ℝ) + 1) ^ 6 + D / ((n : ℝ) + 1) ^ 6 :=
        add_le_add ((herr (n + 1)).trans hmon) (herr n)
      _ = _ := by ring
  have hp (k : ℕ) (hk : 1 < k) : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ k) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr hk)
  have hsNorm : Summable (fun n ↦ ‖B n‖) := by
    apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) ((hp 6 (by norm_num)).mul_left (2 * D))
    simpa only [mul_one_div] using hn n
  have hcost : Summable (fun n ↦ (Module.finrank ℂ (B n).toLinearMap.range : ℝ) * ‖B n‖) := by
    apply Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_)
      ((hp 4 (by norm_num)).mul_left (50 * C * D))
    calc
      _ ≤ (25 * C * ((n : ℝ) + 1) ^ 2) * (2 * D / ((n : ℝ) + 1) ^ 6) :=
        mul_le_mul (hb n).2 (hn n) (norm_nonneg _) (by positivity)
      _ = (50 * C * D) * (1 / ((n : ℝ) + 1) ^ 4) := by
        field_simp
        ring
  have hs : HasSum B (T f - A 0) := by
    apply (hasSum_iff_tendsto_nat_of_summable_norm hsNorm).mpr
    simpa only [B, Finset.sum_range_sub] using hlim.sub_const (A 0)
  have htail := isNuclearOperator_of_hasSum_finiteRank B (fun n ↦ (hb n).1) _ hs hcost
  have hzero := (finiteRank_nuclear_traceNorm_le (A 0)
    (hrank 2 (by norm_num) (q 0) (fun t ht ↦ by simpa using hq 0 t ht)).1).choose
  have hadd : IsNuclearOperator (A 0 + (T f - A 0)) :=
    (nuclearEndomorphisms H).add_mem hzero htail
  rwa [show A 0 + (T f - A 0) = T f by abel] at hadd

end RiemannMasullo
