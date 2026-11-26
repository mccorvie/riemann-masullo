module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! # Shrinking kernels for a divisor with a polynomial height count

A height count of order `T^q log(2T)^k` gives each inverse real moment
of degree strictly greater than `q`. The resulting bound for a shrinking kernel
uses only one power of decay in its scaled height.
-/

public section

open Filter
open scoped BigOperators Topology

namespace RiemannMasullo

private theorem summable_shifted_pow_mul_geometric {d : ℝ} (hd : 0 < d) (hd' : d < 1) (k : ℕ) :
    Summable (fun n : ℕ ↦ ((n : ℝ) + 2) ^ k * d ^ n) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one k
    (show ‖d‖ < 1 by rwa [Real.norm_eq_abs, abs_of_pos hd])
  have ht := hs.comp_injective (show Function.Injective (fun n : ℕ ↦ n + 2) from
    fun _ _ h ↦ Nat.add_right_cancel h)
  refine (ht.mul_right (d ^ 2)⁻¹).congr fun n ↦ ?_
  simp [pow_add, hd.ne', mul_assoc]

/-- A finite-subset bound for the cumulative mass up to height `T` gives every inverse
height moment of degree `r > q`. The polynomial logarithmic factor may have any natural degree.
The index need not be enumerated, and weights already include multiplicity. -/
theorem summable_height_moment_of_log_count {ι : Type*} (h m : ι → ℝ)
    (hm : ∀ i, 0 ≤ m i) {q r C : ℝ} (hr : 0 ≤ r) (hqr : q < r) (hC : 0 ≤ C) (k : ℕ)
    (hcount : ∀ T : ℝ, 2 ≤ T → ∀ S : Finset ι, (∀ i ∈ S, |h i| ≤ T) →
      ∑ i ∈ S, m i ≤ C * T ^ q * Real.log (2 * T) ^ k) :
    Summable (fun i ↦ m i / (1 + |h i|) ^ r) := by
  classical
  choose b hb using fun i : ι ↦ exists_nat_pow_near (show 1 ≤ 1 + |h i| from le_add_of_nonneg_right (abs_nonneg _))
    (show (1 : ℝ) < 2 by norm_num)
  let d : ℝ := 2 ^ (q - r)
  have hd : 0 < d := Real.rpow_pos_of_pos (by norm_num) _
  have hd' : d < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hqr)
  let A := C * (2 : ℝ) ^ q * Real.log 2 ^ k
  let u := fun n : ℕ ↦ A * (((n : ℝ) + 2) ^ k * d ^ n)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hu : Summable u := (summable_shifted_pow_mul_geometric hd hd' k).mul_left A
  have hpow (n : ℕ) (p : ℝ) : ((2 : ℝ) ^ n) ^ p = ((2 : ℝ) ^ p) ^ n := by
    rw [← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast ((2 : ℝ) ^ p) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
  have hlog (n : ℕ) : Real.log (2 * (2 : ℝ) ^ (n + 1)) = ((n : ℝ) + 2) * Real.log 2 := by
    rw [show 2 * (2 : ℝ) ^ (n + 1) = 2 ^ (n + 2) by ring, Real.log_pow]
    norm_num
  have hshell (n : ℕ) : C * ((2 : ℝ) ^ (n + 1)) ^ q *
      Real.log (2 * (2 : ℝ) ^ (n + 1)) ^ k / ((2 : ℝ) ^ n) ^ r = u n := by
    rw [hlog, hpow, hpow, pow_succ, mul_pow]
    dsimp [u, A, d]
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), div_pow]
    ring
  have hf (S : Finset ι) (n : ℕ) :
      ∑ i ∈ S with b i = n, m i / (1 + |h i|) ^ r ≤ u n := by
    let Sₙ := S.filter (fun i ↦ b i = n)
    have hb' (i : ι) (hi : i ∈ Sₙ) := (Finset.mem_filter.mp hi).2
    have hlo (i : ι) (hi : i ∈ Sₙ) : (2 : ℝ) ^ n ≤ 1 + |h i| := hb' i hi ▸ (hb i).1
    have hhi (i : ι) (hi : i ∈ Sₙ) : |h i| ≤ (2 : ℝ) ^ (n + 1) := by
      have hupper := (hb i).2
      rw [hb' i hi] at hupper
      linarith
    have h2 : 2 ≤ (2 : ℝ) ^ (n + 1) := by
      rw [pow_succ]
      nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := n)]
    calc
      _ ≤ ∑ i ∈ Sₙ, m i / ((2 : ℝ) ^ n) ^ r := Finset.sum_le_sum fun i hi ↦
        div_le_div_of_nonneg_left (hm i) (by positivity)
          (Real.rpow_le_rpow (by positivity) (hlo i hi) hr)
      _ = (∑ i ∈ Sₙ, m i) / ((2 : ℝ) ^ n) ^ r := by simp only [div_eq_mul_inv, Finset.sum_mul]
      _ ≤ _ := (div_le_div_of_nonneg_right (hcount _ h2 Sₙ hhi) (by positivity)).trans (hshell n).le
  apply summable_of_sum_le (fun i ↦ div_nonneg (hm i) (Real.rpow_nonneg (by positivity) _))
  intro S
  calc
    _ = ∑ n ∈ S.image b, ∑ i ∈ S with b i = n, m i / (1 + |h i|) ^ r :=
      (Finset.sum_fiberwise_of_maps_to (fun i hi ↦ Finset.mem_image_of_mem b hi) _).symm
    _ ≤ ∑ n ∈ S.image b, u n := Finset.sum_le_sum (fun n _ ↦ hf S n)
    _ ≤ ∑' n, u n := hu.sum_le_tsum _ (fun n _ ↦ by dsimp [u]; positivity)

/-- Below height `1/η` the kernel is bounded and above that height a single inverse
power suffices to extract any fractional moment of order `r ∈ [0,1]`. -/
theorem shrinking_height_kernel_le {η r : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1)
    (hr : 0 ≤ r) (hr₁ : r ≤ 1) (t : ℝ) :
    η / (1 + η * |t|) ≤ η ^ (1 - r) / (1 + |t|) ^ r := by
  have hpos : 0 < 1 + η * |t| := by positivity
  have h1 : 1 ≤ 1 + η * |t| := by nlinarith [mul_nonneg hη.le (abs_nonneg t)]
  have hmul : η * (1 + |t|) ≤ 1 + η * |t| := by linarith
  have hrpow : (η * (1 + |t|)) ^ r ≤ 1 + η * |t| :=
    (Real.rpow_le_rpow (by positivity) hmul hr).trans
      ((Real.rpow_le_rpow_of_exponent_le h1 hr₁).trans_eq (Real.rpow_one _))
  rw [Real.mul_rpow hη.le (by positivity)] at hrpow
  have hfac : η ^ (1 - r) * η ^ r = η := by
    rw [← Real.rpow_add hη, sub_add_cancel, Real.rpow_one]
  apply (div_le_div_iff₀ hpos (Real.rpow_pos_of_pos (by positivity) _)).mpr
  calc
    η * (1 + |t|) ^ r = η ^ (1 - r) * (η ^ r * (1 + |t|) ^ r) := by rw [← mul_assoc, hfac]
    _ ≤ _ := mul_le_mul_of_nonneg_left hrpow (Real.rpow_nonneg hη.le _)

/-- A cumulative count of exponent `q < 1` turns a uniform shrinking transform
bound into an absolute total mass `O(η^ν)` for every `0 < ν < 1-q`.
One constant works for every transform satisfying the given pointwise bound. -/
theorem exists_shrinking_sum_le_of_log_count {ι : Type*} (h m : ι → ℝ)
    (hm : ∀ i, 0 ≤ m i) {q ν C K : ℝ} (hq : 0 ≤ q) (hν : 0 < ν) (hqν : ν < 1 - q)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (k : ℕ)
    (hcount : ∀ T : ℝ, 2 ≤ T → ∀ S : Finset ι, (∀ i ∈ S, |h i| ≤ T) →
      ∑ i ∈ S, m i ≤ C * T ^ q * Real.log (2 * T) ^ k) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ a : ι → ℂ,
      (∀ i, ‖a i‖ ≤ K * (η / (1 + η * |h i|))) →
      Summable (fun i ↦ m i * ‖a i‖) ∧ ∑' i, m i * ‖a i‖ ≤ D * η ^ ν := by
  have hr : 0 ≤ 1 - ν := by linarith
  have hbase := summable_height_moment_of_log_count h m hm hr (by linarith : q < 1 - ν) hC k hcount
  let B := ∑' i, m i / (1 + |h i|) ^ (1 - ν)
  refine ⟨K * B, mul_nonneg hK (tsum_nonneg fun i ↦ by positivity [hm i]), ?_⟩
  intro η hη hη₁ a ha
  have hmaj (i : ι) : m i * ‖a i‖ ≤ (m i / (1 + |h i|) ^ (1 - ν)) * (K * η ^ ν) := by
    have hk := shrinking_height_kernel_le hη hη₁ hr (by linarith : 1 - ν ≤ 1) (h i)
    rw [sub_sub_cancel] at hk
    calc
      _ ≤ m i * (K * (η ^ ν / (1 + |h i|) ^ (1 - ν))) :=
        mul_le_mul_of_nonneg_left ((ha i).trans (mul_le_mul_of_nonneg_left hk hK)) (hm i)
      _ = _ := by ring
  have hs := hbase.mul_right (K * η ^ ν)
  have ha' : Summable (fun i ↦ m i * ‖a i‖) := Summable.of_nonneg_of_le
    (fun i ↦ mul_nonneg (hm i) (norm_nonneg _)) hmaj hs
  refine ⟨ha', (ha'.tsum_le_tsum hmaj hs).trans_eq ?_⟩
  rw [tsum_mul_right]
  dsimp [B]
  ring

end RiemannMasullo
