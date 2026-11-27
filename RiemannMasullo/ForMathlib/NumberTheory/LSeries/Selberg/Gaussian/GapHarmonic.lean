module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import Mathlib.NumberTheory.Harmonic.Bounds

public section

open Classical

namespace RiemannMasullo.Selberg

private theorem inv_sq_gap_le {N k l m v i j : ℕ} (hk : k ∈ D N) (hl : l ∈ D N)
    (hv : v ∈ D N) (hj : (j+1)*l*m < (i+1)*k*v) :
    let d := (i+1)*k*v - (j+1)*l*m
    |(freq i k l)^2 - (freq j m v)^2|⁻¹ ≤ (N : ℝ)^3 / (i+1) * (d : ℝ)⁻¹ := by
  intro d
  obtain ⟨hk₁, _⟩ := Finset.mem_Icc.mp hk
  obtain ⟨hl₁, hlN⟩ := Finset.mem_Icc.mp hl
  obtain ⟨hv₁, hvN⟩ := Finset.mem_Icc.mp hv
  have hl₀ : 0 < (l : ℝ) := by exact_mod_cast hl₁
  have hv₀ : 0 < (v : ℝ) := by exact_mod_cast hv₁
  have hN : 0 < (N : ℝ) := by exact_mod_cast hl₁.trans hlN
  have hd : 0 < (d : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hj
  have hdiff : freq i k l - freq j m v = (d : ℝ) / (l * v) := by
    simp only [freq, d, Nat.cast_sub hj.le, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  have hsum : ((i : ℝ)+1) / N ≤ freq i k l + freq j m v := calc
    _ ≤ ((i : ℝ)+1) / l := by gcongr
    _ ≤ freq i k l := by
      unfold freq
      exact div_le_div_of_nonneg_right
        (le_mul_of_one_le_right (by positivity) (by exact_mod_cast hk₁)) hl₀.le
    _ ≤ _ := le_add_of_nonneg_right (by unfold freq; positivity)
  have hden : (l : ℝ) * v ≤ (N : ℝ)^2 := by
    rw [sq]
    exact mul_le_mul (by exact_mod_cast hlN) (by exact_mod_cast hvN) hv₀.le hN.le
  have hsq : ((i : ℝ)+1) / N * ((d : ℝ) / (N : ℝ)^2) ≤
      |(freq i k l)^2 - (freq j m v)^2| := calc
    _ ≤ (freq i k l + freq j m v) * ((d : ℝ) / (l * v)) := by
      gcongr
      unfold freq
      positivity
    _ = _ := by rw [sq_sub_sq, hdiff, abs_of_nonneg (by unfold freq; positivity)]
  have hpos : 0 < ((i : ℝ)+1) / N * ((d : ℝ) / (N : ℝ)^2) := by positivity
  calc
    _ ≤ (((i : ℝ)+1) / N * ((d : ℝ) / (N : ℝ)^2))⁻¹ :=
      (inv_le_inv₀ (hpos.trans_le hsq) hpos).2 hsq
    _ = _ := by rw [mul_inv_rev, inv_div, inv_div]; ring

/-- Card 31. With the first frequency fixed, the reciprocal gaps between its square and lower
squared frequencies sum to at most N³(1 + log((i+1)kv))/(i+1).
Titchmarsh, §10.16, p. 274, reciprocal differences. -/
theorem gap_harmonic (N k l m v i : ℕ) (hk : k ∈ D N) (hl : l ∈ D N)
    (hm : m ∈ D N) (hv : v ∈ D N) :
    let M := (i+1)*k*v
    (∑ j ∈ (Finset.range M).filter (fun j ↦ (j+1)*l*m < M),
      |(freq i k l)^2-(freq j m v)^2|⁻¹) ≤
      (N : ℝ)^3 / ((i : ℝ)+1) * (1+Real.log M) := by
  intro M
  let rowIndices := (Finset.range M).filter (fun j ↦ (j+1)*l*m < M)
  let d (j : ℕ) := M - (j+1)*l*m
  have lower {j} (hj : j ∈ rowIndices) : (j+1)*l*m < M := (Finset.mem_filter.mp hj).2
  have hinj : Set.InjOn d (↑rowIndices) := by
    intro a ha b hb heq
    have ha' := lower ha
    have hb' := lower hb
    change M - (a+1)*l*m = M - (b+1)*l*m at heq
    have hab : (a+1)*l*m = (b+1)*l*m := by omega
    exact Nat.succ.inj (Nat.mul_right_cancel (Finset.mem_Icc.mp hl).1
      (Nat.mul_right_cancel (Finset.mem_Icc.mp hm).1 hab))
  calc
    _ ≤ ∑ t ∈ Finset.Icc 1 M, (N : ℝ)^3 / ((i : ℝ)+1) * (t : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_injOn d hinj
      · intro t ht
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
        exact Finset.mem_Icc.mpr ⟨Nat.sub_pos_of_lt (lower hj), Nat.sub_le ..⟩
      · exact fun j hj ↦ inv_sq_gap_le hk hl hv (lower hj)
      · intros
        positivity
    _ = (N : ℝ)^3 / ((i : ℝ)+1) * harmonic M := by
      simp only [← Finset.mul_sum, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log M) (by positivity)

end RiemannMasullo.Selberg
