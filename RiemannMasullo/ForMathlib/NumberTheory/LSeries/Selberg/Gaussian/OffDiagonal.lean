module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Gaussian.DiagonalSplit
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Gaussian.OscillatoryPair
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Gaussian.GapHarmonic
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Gaussian.GaussianHarmonic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

public section

namespace RiemannMasullo.Selberg

private noncomputable def decay (N i : ℕ) : ℝ :=
  Real.exp (-((i : ℝ) + 1)^2 / (2 * (N : ℝ)^102))

private noncomputable def harmonicTerm (N i : ℕ) : ℝ :=
  decay N i * (1 + Real.log (((i : ℝ) + 1) * (N : ℝ)^2)) / ((i : ℝ) + 1)

private lemma freq_lower {N k l : ℕ} (hk : k ∈ D N) (hl : l ∈ D N) (i : ℕ) :
    ((i : ℝ) + 1) / N ≤ freq i k l := calc
  _ ≤ ((i : ℝ) + 1) / l := by
    have hl₀ : (0 : ℝ) < l := by exact_mod_cast (Finset.mem_Icc.mp hl).1
    gcongr
    exact_mod_cast (Finset.mem_Icc.mp hl).2
  _ ≤ _ := div_le_div_of_nonneg_right
    (le_mul_of_one_le_right (by positivity) (by exact_mod_cast (Finset.mem_Icc.mp hk).1))
    (Nat.cast_nonneg l)

/-- Retain the Gaussian decay from either frequency and the full reciprocal gap. -/
private lemma pairInt_le_gap {N i : ℕ} (hN : 2 ≤ N) {A B q : ℝ} (hq : 0 ≤ q)
    (hfreq : (((i : ℝ) + 1) / N)^2 ≤ A^2 + B^2) (hne : A^2 ≠ B^2) :
    ‖pairInt (Real.pi * Real.sin (1/(H N : ℝ)) * (A^2 + B^2))
      (Real.pi * Real.cos (1/(H N : ℝ)) * (B^2 - A^2)) q‖ ≤
      2 * decay N i * |A^2 - B^2|⁻¹ := by
  let δ := 1 / (H N : ℝ)
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hH : (1 : ℝ) ≤ H N := by simpa only [H, Nat.cast_pow] using one_le_pow₀ hN₁ (n := 100)
  have hδ : 0 < δ := div_pos zero_lt_one (zero_lt_one.trans_le hH)
  have hδ₁ : δ ≤ 1 := (div_le_one (zero_lt_one.trans_le hH)).2 hH
  have hsin : δ / 2 ≤ Real.pi * Real.sin δ := calc
    _ ≤ Real.pi * (2 / Real.pi * δ) := by field_simp; linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.mul_le_sin hδ.le (by linarith [Real.two_le_pi])) Real.pi_pos.le
  have hcos : 1 ≤ Real.pi * Real.cos δ := calc
    1 = 2 * (1 / 2 : ℝ) := by norm_num
    _ ≤ _ := by
      have hsq : δ^2 ≤ 1 := by simpa using pow_le_pow_left₀ hδ.le hδ₁ 2
      have hc : 1 / 2 ≤ Real.cos δ := by linarith [Real.one_sub_sq_div_two_le_cos (x := δ)]
      exact mul_le_mul Real.two_le_pi hc (by norm_num) Real.pi_pos.le
  have hP : ((i : ℝ) + 1)^2 / (2 * (N : ℝ)^102) ≤
      Real.pi * Real.sin δ * (A^2 + B^2) := calc
    _ = (δ / 2) * (((i : ℝ) + 1) / N)^2 := by
      simp only [δ, H, Nat.cast_pow]
      ring
    _ ≤ _ := mul_le_mul hsin hfreq (sq_nonneg _) (by linarith)
  have hpos : 0 < ((i : ℝ) + 1)^2 / (2 * (N : ℝ)^102) := by
    have : (0 : ℝ) < N := zero_lt_one.trans_le hN₁
    positivity
  have hc₀ : 0 < Real.pi * Real.cos δ := zero_lt_one.trans_le hcos
  have hQ := mul_ne_zero hc₀.ne' (sub_ne_zero.mpr hne.symm)
  refine (oscillatory_pair _ _ _ (hpos.trans_le hP) hQ hq).trans ?_
  rw [abs_mul, abs_of_pos hc₀, abs_sub_comm (B^2), ← div_eq_mul_inv]
  apply div_le_div₀ (by unfold decay; positivity) _ (abs_pos.mpr (sub_ne_zero.mpr hne)) _
  · unfold decay
    gcongr
    simpa only [neg_div] using neg_le_neg hP
  · exact le_mul_of_one_le_left (abs_nonneg _) hcos

/-- The majorant on the half of the pair series with larger first frequency. -/
private noncomputable def lowerMajorant (N k l m v : ℕ) (ij : ℕ × ℕ) : ℝ :=
  if freq ij.2 m v < freq ij.1 k l then
    2 * decay N ij.1 * |(freq ij.1 k l)^2 - (freq ij.2 m v)^2|⁻¹ else 0

private lemma lowerMajorant_nonneg (N k l m v : ℕ) (ij : ℕ × ℕ) :
    0 ≤ lowerMajorant N k l m v ij := by
  unfold lowerMajorant decay
  split <;> positivity

/-- Each lower-frequency row is finite. Summing its gaps leaves a Gaussian harmonic term. -/
private lemma lowerMajorant_row {N k l m v : ℕ} (hk : k ∈ D N) (hl : l ∈ D N)
    (hm : m ∈ D N) (hv : v ∈ D N) (i : ℕ) :
    Summable (fun j ↦ lowerMajorant N k l m v (i, j)) ∧
      ∑' j, lowerMajorant N k l m v (i, j) ≤ 2 * (N : ℝ)^3 * harmonicTerm N i := by
  let M := (i + 1) * k * v
  let s := (Finset.range M).filter (fun j ↦ (j+1)*l*m < M)
  have hl₀ : (0 : ℝ) < l := by exact_mod_cast (Finset.mem_Icc.mp hl).1
  have hv₀ : (0 : ℝ) < v := by exact_mod_cast (Finset.mem_Icc.mp hv).1
  have hmem (j : ℕ) : j ∈ s ↔ freq j m v < freq i k l := by
    simp only [s, Finset.mem_filter, Finset.mem_range, freq, div_lt_div_iff₀ hv₀ hl₀,
      mul_right_comm (((j : ℝ) + 1)) (m : ℝ) (l : ℝ)]
    constructor
    · intro ⟨_, h⟩
      exact_mod_cast h
    · intro h
      have hj : (j+1)*l*m < M := by exact_mod_cast h
      refine ⟨lt_of_lt_of_le (Nat.lt_succ_self j) (le_trans ?_ hj.le), hj⟩
      exact le_trans (Nat.le_mul_of_pos_right _ (Finset.mem_Icc.mp hl).1)
        (Nat.le_mul_of_pos_right _ (Finset.mem_Icc.mp hm).1)
  have hout (j : ℕ) (hj : j ∉ s) : lowerMajorant N k l m v (i, j) = 0 :=
    ite_eq_right (fun h ↦ hj ((hmem j).2 h))
  refine ⟨summable_of_ne_finset_zero hout, ?_⟩
  have hdec : 0 ≤ 2 * decay N i := by unfold decay; positivity
  have hlog : Real.log (M : ℝ) ≤ Real.log (((i : ℝ) + 1) * (N : ℝ)^2) := by
    have hM : 0 < M := Nat.mul_pos (Nat.mul_pos (Nat.succ_pos i) (Finset.mem_Icc.mp hk).1)
      (Finset.mem_Icc.mp hv).1
    apply Real.log_le_log (by exact_mod_cast hM)
    simp only [M, Nat.cast_mul, Nat.cast_add, Nat.cast_one, sq, mul_assoc]
    gcongr
    · exact_mod_cast (Finset.mem_Icc.mp hk).2
    · exact_mod_cast (Finset.mem_Icc.mp hv).2
  calc
    _ = ∑ j ∈ s, lowerMajorant N k l m v (i, j) := tsum_eq_sum hout
    _ = 2 * decay N i * ∑ j ∈ s, |(freq i k l)^2 - (freq j m v)^2|⁻¹ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j hj ↦ ite_eq_left ((hmem j).1 hj)
    _ ≤ 2 * decay N i * ((N : ℝ)^3 / ((i : ℝ)+1) * (1 + Real.log M)) :=
      mul_le_mul_of_nonneg_left (gap_harmonic N k l m v i hk hl hm hv) hdec
    _ ≤ 2 * decay N i *
        ((N : ℝ)^3 / ((i : ℝ)+1) * (1 + Real.log (((i : ℝ)+1) * (N : ℝ)^2))) := by gcongr
    _ = _ := by unfold harmonicTerm; ring

private lemma lowerMajorant_sum {N k l m v : ℕ} (hk : k ∈ D N) (hl : l ∈ D N)
    (hm : m ∈ D N) (hv : v ∈ D N) (ht : Summable (harmonicTerm N)) :
    Summable (lowerMajorant N k l m v) ∧ ∑' ij, lowerMajorant N k l m v ij ≤
      2 * (N : ℝ)^3 * ∑' i, harmonicTerm N i := by
  have hrow := lowerMajorant_row hk hl hm hv
  have hmajor := ht.mul_left (2 * (N : ℝ)^3)
  have hrows := hmajor.of_nonneg_of_le
    (fun i ↦ tsum_nonneg fun j ↦ lowerMajorant_nonneg N k l m v (i, j)) (fun i ↦ (hrow i).2)
  have hs := (summable_prod_of_nonneg (lowerMajorant_nonneg N k l m v)).2
    ⟨fun i ↦ (hrow i).1, hrows⟩
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod, ← ht.tsum_mul_left]
  exact hrows.tsum_le_tsum (fun i ↦ (hrow i).2) hmajor

private lemma pair_le_majorants {N k l m v : ℕ} (hN : 2 ≤ N) (hk : k ∈ D N)
    (hl : l ∈ D N) (hm : m ∈ D N) (hv : v ∈ D N) {q : ℝ} (hq : 0 ≤ q) (ij : ℕ × ℕ) :
    ‖if freq ij.1 k l = freq ij.2 m v then 0 else pair N k l m v q ij‖ ≤
      lowerMajorant N k l m v ij + lowerMajorant N m v k l ij.swap := by
  obtain ⟨i, j⟩ := ij
  let A := freq i k l
  let B := freq j m v
  change ‖if A = B then 0 else pair N k l m v q (i, j)‖ ≤
    (if B < A then 2 * decay N i * |A^2 - B^2|⁻¹ else 0) +
    (if A < B then 2 * decay N j * |B^2 - A^2|⁻¹ else 0)
  by_cases heq : A = B
  · simp [heq]
  have hA : 0 ≤ A := by unfold A freq; positivity
  have hB : 0 ≤ B := by unfold B freq; positivity
  have hsq := (sq_eq_sq₀ hA hB).not.mpr heq
  rw [ite_eq_right heq]
  rcases lt_or_gt_of_ne heq with h | h
  · simp only [h, h.not_gt, ite_true, ite_false, zero_add, abs_sub_comm (B^2)]
    apply pairInt_le_gap hN hq _ hsq
    exact (pow_le_pow_left₀ (by positivity) (freq_lower hm hv j) 2).trans
      (le_add_of_nonneg_left (sq_nonneg A))
  · simp only [h, h.not_gt, ite_true, ite_false, add_zero]
    apply pairInt_le_gap hN hq _ hsq
    exact (pow_le_pow_left₀ (by positivity) (freq_lower hk hl i) 2).trans
      (le_add_of_nonneg_right (sq_nonneg B))

/-- Add the two strictly ordered halves, swapping the two natural indices in the second. -/
private lemma off_pair_series_le {N k l m v : ℕ} (hN : 2 ≤ N) (hk : k ∈ D N)
    (hl : l ∈ D N) (hm : m ∈ D N) (hv : v ∈ D N) {q : ℝ} (hq : 0 ≤ q)
    (ht : Summable (harmonicTerm N)) :
    |(∑' ij : ℕ × ℕ, if freq ij.1 k l = freq ij.2 m v then 0
        else pair N k l m v q ij).re| ≤ 4 * (N : ℝ)^3 * ∑' i, harmonicTerm N i := by
  obtain ⟨h₁, b₁⟩ := lowerMajorant_sum hk hl hm hv ht
  obtain ⟨h₂, b₂⟩ := lowerMajorant_sum hm hv hk hl ht
  have hs := h₁.hasSum.add ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr h₂.hasSum)
  refine (Complex.abs_re_le_norm _).trans ((tsum_of_norm_bounded hs
    (pair_le_majorants hN hk hl hm hv hq)).trans ?_)
  linarith only [b₁, b₂]

private lemma abs_coef_le_one {N k l m v : ℕ} {b : ℕ → ℝ} (hb : bd N b)
    (hk : k ∈ D N) (hl : l ∈ D N) (hm : m ∈ D N) (hv : v ∈ D N) :
    |coef b k l m v| ≤ 1 := by
  rw [coef, abs_div, abs_of_nonneg (by positivity : 0 ≤ (l : ℝ) * v)]
  simp only [abs_mul]
  apply div_le_one_of_le₀ _ (by positivity)
  calc
    _ ≤ 1 * 1 * 1 * (1 : ℝ) := by gcongr <;> apply hb <;> assumption
    _ ≤ _ := by
      simpa using one_le_mul_of_one_le_of_one_le
        (show 1 ≤ (l : ℝ) by exact_mod_cast (Finset.mem_Icc.mp hl).1)
        (show 1 ≤ (v : ℝ) by exact_mod_cast (Finset.mem_Icc.mp hv).1)

private lemma abs_sum_D_le {N : ℕ} {f : ℕ → ℝ} {B : ℝ} (hf : ∀ i ∈ D N, |f i| ≤ B) :
    |∑ i ∈ D N, f i| ≤ (N : ℝ) * B := calc
  _ ≤ ∑ i ∈ D N, |f i| := Finset.abs_sum_le_sum_abs ..
  _ ≤ ∑ _i ∈ D N, B := Finset.sum_le_sum hf
  _ = _ := by simp [D, Nat.card_Icc, nsmul_eq_mul]

/-- Card 33. For every sequence bounded by one, the total contribution to J from unequal
frequencies has absolute value at most a constant times N²², uniformly for q ≥ 0.
Weaker power-saving substitute for Titchmarsh (10.16.1), pp. 274–275. -/
theorem off_diagonal : ∃ C > (0 : ℝ), ∀ N : ℕ, 2 ≤ N → ∀ b : ℕ → ℝ, bd N b →
    ∀ q : ℝ, 0 ≤ q → |J N b q - diag N b q| ≤ C*(N : ℝ)^22 := by
  obtain ⟨C, hC, hgauss⟩ := gaussian_harmonic
  refine ⟨4 * C, by positivity, ?_⟩
  intro N hN b hb q hq
  obtain ⟨ht, hbound⟩ : Summable (harmonicTerm N) ∧
      ∑' i, harmonicTerm N i ≤ C * (N : ℝ)^14 := hgauss N hN
  rw [diagonal_split N hN b q hq, add_sub_cancel_left, fourSum]
  calc
    _ ≤ (N : ℝ) * (N * (N * (N * (4 * N^3 * (C * N^14))))) := by
      apply abs_sum_D_le
      intro k hk
      apply abs_sum_D_le
      intro l hl
      apply abs_sum_D_le
      intro m hm
      apply abs_sum_D_le
      intro v hv
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (abs_coef_le_one hb hk hl hm hv)).trans
        ((off_pair_series_le hN hk hl hm hv hq ht).trans (mul_le_mul_of_nonneg_left hbound
          (by positivity)))
    _ = 4 * C * (N : ℝ)^21 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀
      (by exact_mod_cast (show 1 ≤ N by omega)) (by decide : 21 ≤ 22)) (by positivity)

end RiemannMasullo.Selberg
