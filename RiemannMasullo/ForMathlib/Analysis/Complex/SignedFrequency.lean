module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-! # Two signs in bounded windows of finite unit-frequency sums -/

@[expose] public noncomputable section

open Finset Filter Set Topology
open scoped Asymptotics ComplexConjugate

namespace RiemannMasullo.SignedFrequency

/-- A cosine wave represented by a complex unit frequency. -/
def wave (z : ℂ) (n : ℕ) : ℝ := (z ^ n).re

/-- Finite real parts of power sums; the indexing may repeat phases. -/
def cosineSum {ι : Type*} (s : Finset ι) (w : ι → ℝ) (z : ι → ℂ) (n : ℕ) : ℝ :=
  ∑ i ∈ s, w i * wave (z i) n

/-- The sum of a sequence on the integers from `m` to `m+K-1`. -/
def block (f : ℕ → ℝ) (m K : ℕ) : ℝ := ∑ k ∈ range K, f (m+k)

/-- A geometric sum error bound. Lean's division convention gives zero at `z=1`,
where the constant contribution is accounted for separately. -/
def geometricError (z : ℂ) : ℝ := 2 / ‖z-1‖

private theorem abs_wave_le_one {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) : |wave z n| ≤ 1 := by
  simpa only [wave, norm_pow, hz, one_pow] using Complex.abs_re_le_norm (z^n)

private theorem block_wave_one (m K : ℕ) : block (wave 1) m K = (K : ℝ) := by
  simp [block, wave]

/-- The error in each geometric block is independent of its starting point and length. -/
theorem abs_block_wave_le {z : ℂ} (hz : ‖z‖ = 1) (hn : z ≠ 1) (m K : ℕ) :
    |block (wave z) m K| ≤ geometricError z := by
  have he : (∑ k ∈ range K, z^(m+k)) = z^m * ((z^K-1)/(z-1)) := by
    simp_rw [pow_add]
    rw [← Finset.mul_sum, geom_sum_eq hn]
  have hr : block (wave z) m K = (∑ k ∈ range K, z^(m+k)).re := by
    simp [block, wave, Complex.re_sum]
  have hb : ‖z^K-1‖ ≤ 2 := by
    simpa only [norm_pow, hz, one_pow, norm_one, one_add_one_eq_two] using (norm_sub_le (z^K) (1 : ℂ))
  rw [hr]
  apply (Complex.abs_re_le_norm _).trans
  rw [he, norm_mul, norm_pow, hz, one_pow, one_mul, norm_div, geometricError]
  exact div_le_div_of_nonneg_right hb (norm_nonneg _)

private theorem lower_block_wave {z : ℂ} (hz : ‖z‖ = 1) (m K : ℕ) :
    -geometricError z ≤ block (wave z) m K := by
  by_cases hn : z = 1
  · subst z
    simp [block_wave_one, geometricError]
  · exact (abs_le.mp (abs_block_wave_le hz hn m K)).1

private theorem twice_block_cross (u v : ℂ) (m K : ℕ) :
    2 * block (fun n ↦ wave u n * wave v n) m K =
      block (wave (u*v)) m K + block (wave (u*conj v)) m K := by
  simp only [block, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [wave, mul_pow, ← map_pow, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem cross_lower {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (m K : ℕ) :
    (if u = v then (K : ℝ) else 0) - (geometricError (u*v) + geometricError (u*conj v)) ≤
      2 * block (fun n ↦ wave u n * wave v n) m K := by
  rw [twice_block_cross]
  have h₁ := lower_block_wave (z := u*v) (by simp [hu, hv]) m K
  by_cases h : u = v
  · subst u
    have hunit : v*conj v = 1 := by simpa [hv] using Complex.mul_conj' v
    rw [ite_eq_left rfl, hunit, block_wave_one]
    have he : 0 ≤ geometricError (1 : ℂ) := by simp [geometricError]
    linarith
  · have h₂ := lower_block_wave (z := u*conj v) (by simp [hu, hv]) m K
    rw [ite_eq_right h]
    linarith

private theorem block_cosineSum {ι : Type*} (s : Finset ι) (w : ι → ℝ) (z : ι → ℂ) (m K : ℕ) :
    block (cosineSum s w z) m K = ∑ i ∈ s, w i * block (wave (z i)) m K := by
  unfold block cosineSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem abs_block_cosineSum {ι : Type*} {s : Finset ι} {w : ι → ℝ} {z : ι → ℂ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hu : ∀ i ∈ s, ‖z i‖ = 1) (hn : ∀ i ∈ s, z i ≠ 1) (m K : ℕ) :
    |block (cosineSum s w z) m K| ≤ ∑ i ∈ s, w i * geometricError (z i) := by
  rw [block_cosineSum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul, abs_of_nonneg (hw i hi)]
  exact mul_le_mul_of_nonneg_left (abs_block_wave_le (hu i hi) (hn i hi) m K) (hw i hi)

/-- A pointwise bound for a finite nonnegative-weight power sum. -/
theorem abs_cosineSum_le {ι : Type*} {s : Finset ι} {w : ι → ℝ} {z : ι → ℂ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hu : ∀ i ∈ s, ‖z i‖ = 1) (n : ℕ) :
    |cosineSum s w z n| ≤ ∑ i ∈ s, w i := by
  unfold cosineSum
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul, abs_of_nonneg (hw i hi)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (abs_wave_le_one (hu i hi) n) (hw i hi)

/-- Testing by one actual phase gives a positive linear correlation even when
several frequencies coincide or are conjugates. -/
theorem block_correlation_lower {ι : Type*} {s : Finset ι} {w : ι → ℝ} {z : ι → ℂ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hu : ∀ i ∈ s, ‖z i‖ = 1) {i₀ : ι} (hi₀ : i₀ ∈ s) (m K : ℕ) :
    w i₀ * K - (∑ i ∈ s, w i * (geometricError (z i * z i₀) + geometricError (z i * conj (z i₀)))) ≤
      2 * block (fun n ↦ cosineSum s w z n * wave (z i₀) n) m K := by
  classical
  let v := z i₀
  let e (i : ι) := geometricError (z i*v) + geometricError (z i*conj v)
  let r (i : ι) : ℝ := if z i = v then (K : ℝ) else 0
  have hi : w i₀ * (K : ℝ) ≤ ∑ i ∈ s, w i * r i := by
    have hr : r i₀ = (K : ℝ) := by simp [r,v]
    rw [← hr]
    apply Finset.single_le_sum _ hi₀
    intro i h
    apply mul_nonneg (hw i h)
    dsimp [r]
    split_ifs <;> positivity
  have lower := Finset.sum_le_sum (s := s) (f := fun i ↦ w i * (r i - e i))
    (g := fun i ↦ w i * (2 * block (fun n ↦ wave (z i) n * wave v n) m K))
    (fun i h ↦ mul_le_mul_of_nonneg_left (cross_lower (hu i h) (hu i₀ hi₀) m K) (hw i h))
  have heq : (∑ i ∈ s, w i * (2 * block (fun n ↦ wave (z i) n * wave v n) m K)) =
      2 * block (fun n ↦ cosineSum s w z n * wave v n) m K := by
    simp only [block, cosineSum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [mul_sub, Finset.sum_sub_distrib] at lower
  rw [heq] at lower
  change w i₀ * (K : ℝ) - (∑ i ∈ s, w i * e i) ≤ _
  linarith

private theorem positive_hit {f v : ℕ → ℝ} {K m : ℕ} {w D C : ℝ}
    (hw : 0 < w) (hv : ∀ n, |v n| ≤ 1) (hm : -D ≤ block f m K)
    (hc : w*K-C ≤ 2 * block (fun n ↦ f n * v n) m K)
    (hK : 2*D+C < w/2*K) : ∃ k < K, w/8 < f (m+k) := by
  by_contra! h
  have hp (k : ℕ) (hk : k ∈ range K) :
      f (m+k)*v (m+k) + f (m+k) ≤ 2*(w/8) := by
    obtain ⟨hL, hU⟩ := abs_le.mp (hv (m+k))
    calc _ = f (m+k)*(1+v (m+k)) := by ring
         _ ≤ (w/8)*(1+v (m+k)) :=
           mul_le_mul_of_nonneg_right (h k (mem_range.mp hk)) (by linarith)
         _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ w/8 by positivity) (sub_nonneg.mpr hU)]
  have ht := Finset.sum_le_sum hp
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at ht
  unfold block at hm hc
  nlinarith

/-- Any block satisfying this explicit length inequality contains values strictly
above and below one eighth of the chosen positive coefficient. -/
theorem both_signs_of_length {ι : Type*} {s : Finset ι} {w : ι → ℝ} {z : ι → ℂ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hu : ∀ i ∈ s, ‖z i‖ = 1) (hn : ∀ i ∈ s, z i ≠ 1)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hpos : 0 < w i₀) {K : ℕ}
    (hK : 2*(∑ i ∈ s, w i * geometricError (z i)) +
      (∑ i ∈ s, w i * (geometricError (z i*z i₀) + geometricError (z i*conj (z i₀)))) <
      w i₀/2*K) (m : ℕ) :
    (∃ k < K, w i₀/8 < cosineSum s w z (m+k)) ∧
    (∃ k < K, cosineSum s w z (m+k) < -(w i₀/8)) := by
  have hv := abs_wave_le_one (hu i₀ hi₀)
  have hm := abs_le.mp (abs_block_cosineSum hw hu hn m K)
  have hc := block_correlation_lower hw hu hi₀ m K
  refine ⟨positive_hit hpos hv hm.1 hc hK, ?_⟩
  have hm' : -(∑ i ∈ s, w i * geometricError (z i)) ≤
      block (fun n ↦ -(cosineSum s w z n)) m K := by
    simpa only [block, Finset.sum_neg_distrib] using neg_le_neg hm.2
  have hc' : w i₀ * K - (∑ i ∈ s, w i * (geometricError (z i*z i₀) + geometricError (z i*conj (z i₀)))) ≤
      2 * block (fun n ↦ (-(cosineSum s w z n)) * (-(wave (z i₀) n))) m K := by
    simpa only [neg_mul_neg] using hc
  obtain ⟨k, hk, h⟩ := positive_hit hpos (f := fun n ↦ -(cosineSum s w z n))
    (v := fun n ↦ -(wave (z i₀) n)) (fun n ↦ by simpa only [abs_neg] using hv n) hm' hc' hK
  exact ⟨k, hk, by linarith⟩

/-- Uniformly bounded gaps for each strict sign. No distinctness assumption on
the frequencies or symmetry under conjugation is required. -/
theorem exists_length_both_signs {ι : Type*} {s : Finset ι} {w : ι → ℝ} {z : ι → ℂ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hu : ∀ i ∈ s, ‖z i‖ = 1) (hn : ∀ i ∈ s, z i ≠ 1)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hpos : 0 < w i₀) :
    ∃ K : ℕ, 0 < K ∧ ∀ m : ℕ,
      (∃ k < K, w i₀/8 < cosineSum s w z (m+k)) ∧
      (∃ k < K, cosineSum s w z (m+k) < -(w i₀/8)) := by
  let T := 2*(∑ i ∈ s, w i * geometricError (z i)) +
    ∑ i ∈ s, w i * (geometricError (z i*z i₀) + geometricError (z i*conj (z i₀)))
  obtain ⟨j, hj⟩ := exists_nat_gt (T/(w i₀/2))
  refine ⟨j+1, Nat.succ_pos _, fun m ↦ both_signs_of_length hw hu hn hi₀ hpos ?_ m⟩
  change T < _
  have h := (div_lt_iff₀ (show 0 < w i₀/2 by positivity)).mp hj
  push_cast
  nlinarith

/-- One plus the positive-part sum on the integer indices from one through `N`. -/
def positivePrefix (x : ℕ → ℝ) (N : ℕ) : ℝ := 1 + ∑ k ∈ range N, max 0 (x (k+1))

theorem positivePrefix_eq_sum_Icc (x : ℕ → ℝ) (N : ℕ) :
    positivePrefix x N = 1 + ∑ k ∈ Finset.Icc 1 N, max 0 (x k) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [positivePrefix, Nat.add_comm]

theorem one_le_positivePrefix (x : ℕ → ℝ) (N : ℕ) : 1 ≤ positivePrefix x N := by
  unfold positivePrefix
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ ↦ le_max_left _ _))

private theorem le_positivePrefix (x : ℕ → ℝ) {n N : ℕ} (hn : 0 < n) (hN : n ≤ N) :
    x n ≤ positivePrefix x N := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h : max 0 (x (k+1)) ≤ ∑ j ∈ range N, max 0 (x (j+1)) :=
    Finset.single_le_sum (f := fun j ↦ max 0 (x (j+1))) (fun j _ ↦ le_max_left _ _)
      (mem_range.mpr (by omega : k < N))
  unfold positivePrefix
  linarith [le_max_right 0 (x (k+1))]

private theorem prefix_upper {x : ℕ → ℝ} {A B : ℝ} (hA : 1 < A) (hB : 0 ≤ B)
    (hx : ∀ n, x n ≤ B*A^n) (N : ℕ) :
    positivePrefix x N ≤ (1+B*A/(A-1))*A^N := by
  have hA₀ := zero_lt_one.trans hA
  have hge : 1 ≤ A^N := one_le_pow₀ hA.le
  have hb : ∑ k ∈ range N, max 0 (x (k+1)) ≤ ∑ k ∈ range N, B*A^(k+1) := by
    apply Finset.sum_le_sum
    intro k hk
    exact max_le (by positivity) (hx _)
  have hs : (∑ k ∈ range N, B*A^(k+1)) = B*A*((A^N-1)/(A-1)) := by
    simp_rw [pow_succ', ← mul_assoc]
    rw [← Finset.mul_sum, geom_sum_eq hA.ne']
  rw [hs] at hb
  unfold positivePrefix
  have hpos : 0 ≤ B*A/(A-1) := by positivity
  have he : B*A*((A^N-1)/(A-1)) = (B*A/(A-1))*(A^N-1) := by ring
  rw [he] at hb
  nlinarith

/-- A positive excursion in every fixed window survives a relative error tending
to zero. The complete prefix is uniformly comparable to `A^N`, with the displayed
lower constant; no pointwise rate for the perturbation is required. -/
theorem positivePrefix_bounds_of_windows {x v : ℕ → ℝ} {A B c : ℝ} (hA : 1 < A)
    (hc : 0 < c) (hv : ∀ n, |v n| ≤ B) {K : ℕ}
    (hwin : ∀ m : ℕ, ∃ j < K, c ≤ v (m+j))
    (he : Tendsto (fun n ↦ x n/A^n - v n) atTop (𝓝 0)) :
    ∃ U : ℝ, 0 < U ∧ ∀ᶠ N : ℕ in atTop,
      (c/2/A^K)*A^N ≤ positivePrefix x N ∧ positivePrefix x N ≤ U*A^N := by
  have hA₀ := zero_lt_one.trans hA
  obtain ⟨D, hD⟩ := (Metric.isBounded_range_of_tendsto _ he).exists_norm_le
  let T := 1+|B|+|D|
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hx n : x n ≤ T*A^n := by
    apply (div_le_iff₀ (pow_pos hA₀ n)).mp
    have hd : |x n/A^n - v n| ≤ D := by
      simpa only [Real.norm_eq_abs] using hD _ ⟨n, rfl⟩
    dsimp [T]
    linarith [(abs_le.mp hd).2, (abs_le.mp (hv n)).2, le_abs_self B, le_abs_self D]
  refine ⟨1+T*A/(A-1), by positivity, ?_⟩
  have close : ∀ᶠ n : ℕ in atTop, |x n/A^n - v n| < c/2 := by
    simpa only [Real.dist_eq, sub_zero] using (Metric.tendsto_nhds.mp he (c/2) (by positivity))
  obtain ⟨m, hm⟩ := eventually_atTop.mp close
  filter_upwards [eventually_ge_atTop (m+K)] with N hN
  obtain ⟨j, hj, hvj⟩ := hwin (N-K+1)
  let n := N-K+1+j
  have hmn : m ≤ n := by dsimp [n]; omega
  have hnN : n ≤ N := by dsimp [n]; omega
  have h0n : 0 < n := by dsimp [n]; omega
  have hdist : N ≤ n + K := by dsimp [n]; omega
  have hu : c/2*A^n ≤ x n := by
    apply (le_div_iff₀ (pow_pos hA₀ n)).mp
    have hnear := (abs_lt.mp (hm n hmn)).1
    change c ≤ v n at hvj
    linarith
  have hp : A^N ≤ A^n * A^K := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hA.le hdist
  refine ⟨?_, prefix_upper hA hT hx N⟩
  calc (c/2/A^K)*A^N ≤ (c/2/A^K)*(A^n*A^K) := mul_le_mul_of_nonneg_left hp (by positivity)
       _ = c/2*A^n := by field_simp
       _ ≤ x n := hu
       _ ≤ positivePrefix x N := le_positivePrefix x h0n hnN

private theorem tendsto_log_const_mul_pow {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    Tendsto (fun N : ℕ ↦ Real.log (c*A^N)/(N:ℝ)) atTop (𝓝 (Real.log A)) := by
  have h : Tendsto (fun N : ℕ ↦ Real.log c/(N:ℝ) + Real.log A) atTop (𝓝 (Real.log A)) := by
    simpa only [zero_add] using (tendsto_const_div_atTop_nhds_zero_nat (Real.log c)).add_const (Real.log A)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [Real.log_mul hc.ne' (pow_pos hA N).ne', Real.log_pow]
  field_simp

/-- Ordinary logarithmic growth from two-sided constant multiples of the
exponential. -/
theorem tendsto_log_positivePrefix_of_bounds {x : ℕ → ℝ} {A l U : ℝ}
    (hA : 0 < A) (hl : 0 < l) (hU : 0 < U)
    (h : ∀ᶠ N : ℕ in atTop, l*A^N ≤ positivePrefix x N ∧ positivePrefix x N ≤ U*A^N) :
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix x N)/(N:ℝ)) atTop (𝓝 (Real.log A)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_log_const_mul_pow hA hl)
    (tendsto_log_const_mul_pow hA hU)
  · filter_upwards [h] with N hN
    exact div_le_div_of_nonneg_right (Real.log_le_log (by positivity) hN.1) (Nat.cast_nonneg N)
  · filter_upwards [h] with N hN
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (zero_lt_one.trans_le (one_le_positivePrefix x N)) hN.2) (Nat.cast_nonneg N)

/-- Both signed prefixes are eventually bounded above and below by fixed
multiples of the same exponential, for a leading negative cosine sum. -/
theorem both_positivePrefix_bounds {ι : Type*} {s : Finset ι} {w : ι → ℝ} {z : ι → ℂ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hu : ∀ i ∈ s, ‖z i‖ = 1) (hn : ∀ i ∈ s, z i ≠ 1)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hpos : 0 < w i₀) {A : ℝ} (hA : 1 < A) {x : ℕ → ℝ}
    (he : Tendsto (fun n ↦ x n/A^n + cosineSum s w z n) atTop (𝓝 0)) :
    ∃ K : ℕ, 0 < K ∧ ∃ U : ℝ, 0 < U ∧ ∀ᶠ N : ℕ in atTop,
      (w i₀/16/A^K)*A^N ≤ min (positivePrefix x N) (positivePrefix (fun n ↦ -x n) N) ∧
      max (positivePrefix x N) (positivePrefix (fun n ↦ -x n) N) ≤ U*A^N := by
  obtain ⟨K, hK, hwin⟩ := exists_length_both_signs hw hu hn hi₀ hpos
  let f := cosineSum s w z
  have hsize := abs_cosineSum_le hw hu
  have hc : 0 < w i₀/8 := by positivity
  have hp m : ∃ j < K, w i₀/8 ≤ -f (m+j) := by
    obtain ⟨j, hj, hj'⟩ := (hwin m).2
    exact ⟨j, hj, by dsimp [f]; linarith⟩
  have hm m : ∃ j < K, w i₀/8 ≤ f (m+j) := by
    obtain ⟨j, hj, hj'⟩ := (hwin m).1
    exact ⟨j, hj, hj'.le⟩
  have herrp : Tendsto (fun n ↦ x n/A^n - (-f n)) atTop (𝓝 0) := by simpa only [sub_neg_eq_add] using he
  have herrm : Tendsto (fun n ↦ (-x n)/A^n - f n) atTop (𝓝 0) := by
    have h := he.neg
    simp only [neg_zero] at h
    apply h.congr
    intro n
    dsimp [f]
    ring
  have hnegsize (n : ℕ) : |-(f n)| ≤ ∑ i ∈ s, w i := by
    rw [abs_neg]
    exact hsize n
  obtain ⟨P, hP, hP'⟩ := positivePrefix_bounds_of_windows (x := x) (v := fun n ↦ -f n)
    hA hc hnegsize hp herrp
  obtain ⟨Q, hQ, hQ'⟩ := positivePrefix_bounds_of_windows (x := fun n ↦ -x n) (v := f)
    hA hc hsize hm herrm
  refine ⟨K, hK, max P Q, hP.trans_le (le_max_left _ _), ?_⟩
  filter_upwards [hP',hQ'] with N h₁ h₂
  rw [show w i₀/16 = w i₀/8/2 by ring]
  refine ⟨le_min h₁.1 h₂.1, max_le ?_ ?_⟩
  · exact h₁.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (zero_lt_one.trans hA).le _))
  · exact h₂.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (zero_lt_one.trans hA).le _))

/-- The ordinary logarithmic growth exponent of each signed prefix is `log A`. -/
theorem tendsto_both_log_prefixes {ι : Type*} {s : Finset ι} {w : ι → ℝ} {z : ι → ℂ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hu : ∀ i ∈ s, ‖z i‖ = 1) (hn : ∀ i ∈ s, z i ≠ 1)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hpos : 0 < w i₀) {A : ℝ} (hA : 1 < A) {x : ℕ → ℝ}
    (he : Tendsto (fun n ↦ x n/A^n + cosineSum s w z n) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix x N)/(N:ℝ)) atTop (𝓝 (Real.log A)) ∧
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ -x n) N)/(N:ℝ)) atTop (𝓝 (Real.log A)) := by
  obtain ⟨K, _, U, hU, h⟩ := both_positivePrefix_bounds hw hu hn hi₀ hpos hA he
  have hA₀ := zero_lt_one.trans hA
  have hl : 0 < w i₀/16/A^K := by positivity
  constructor
  · apply tendsto_log_positivePrefix_of_bounds hA₀ hl hU
    filter_upwards [h] with N hN
    exact ⟨(le_min_iff.mp hN.1).1, (max_le_iff.mp hN.2).1⟩
  · apply tendsto_log_positivePrefix_of_bounds hA₀ hl hU
    filter_upwards [h] with N hN
    exact ⟨(le_min_iff.mp hN.1).2, (max_le_iff.mp hN.2).2⟩

/-- A smaller exponential error gives the required vanishing relative error. -/
theorem tendsto_relative_error_of_geometric {x f : ℕ → ℝ} {A B C : ℝ} (hA : 0 < A)
    (hB : 0 ≤ B) (hBA : B < A) (he : ∀ᶠ n : ℕ in atTop, |x n+A^n*f n| ≤ C*B^n) :
    Tendsto (fun n ↦ x n/A^n + f n) atTop (𝓝 0) := by
  have hratio : B/A < 1 := (div_lt_one hA).mpr hBA
  have ht : Tendsto (fun n : ℕ ↦ C*(B/A)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hB hA.le) hratio).const_mul C
  apply squeeze_zero_norm' _ ht
  filter_upwards [he] with n hn
  rw [Real.norm_eq_abs, show x n/A^n + f n = (x n+A^n*f n)/A^n by field_simp,
    abs_div, abs_of_pos (pow_pos hA n), div_pow]
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hn (pow_nonneg hA.le n)

/-- The no-interior-pole case: coefficients bounded at every exponential rate
greater than one have ordinary signed-prefix rate zero. -/
theorem tendsto_log_positivePrefix_of_subexponential {x : ℕ → ℝ}
    (h : ∀ A : ℝ, 1 < A → ∃ B : ℝ, 0 ≤ B ∧ ∀ n, x n ≤ B*A^n) :
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix x N)/(N:ℝ)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun N ↦ ha.trans_le (div_nonneg
      (Real.log_nonneg (one_le_positivePrefix x N)) (Nat.cast_nonneg N))
  · intro b hb
    let A := Real.exp (b/2)
    have hA : 1 < A := Real.one_lt_exp_iff.mpr (by positivity)
    obtain ⟨B, hB, hB'⟩ := h A hA
    let U := 1+B*A/(A-1)
    have hU : 0 < U := by dsimp [U]; positivity
    have hlim := tendsto_log_const_mul_pow (zero_lt_one.trans hA) hU
    have hlog : Real.log A < b := by dsimp [A]; rw [Real.log_exp]; linarith
    filter_upwards [hlim.eventually_lt_const hlog] with N hN
    apply lt_of_le_of_lt _ hN
    exact div_le_div_of_nonneg_right (Real.log_le_log (zero_lt_one.trans_le (one_le_positivePrefix x N))
      (prefix_upper hA hB hB' N)) (Nat.cast_nonneg N)

/-- The concrete smaller-radius input: a finite nearest circle with positive
multiplicities and a remainder bounded at the larger radius `R₂`. -/
theorem tendsto_both_log_prefixes_of_nearest_circle {ι : Type*} {s : Finset ι} {m : ι → ℕ}
    {z : ι → ℂ} (hu : ∀ i ∈ s, ‖z i‖ = 1) (hn : ∀ i ∈ s, z i ≠ 1) {i₀ : ι}
    (hi₀ : i₀ ∈ s) (hm : 0 < m i₀) {R R₂ C : ℝ} (hR : 0 < R) (hR₁ : R < 1) (hgap : R < R₂)
    {x : ℕ → ℝ} (he : ∀ᶠ n : ℕ in atTop,
      |x n + R⁻¹^n * (∑ i ∈ s, (m i : ℝ)*(z i^n).re)| ≤ C*R₂⁻¹^n) :
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix x N)/(N:ℝ)) atTop (𝓝 (Real.log R⁻¹)) ∧
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ -x n) N)/(N:ℝ)) atTop (𝓝 (Real.log R⁻¹)) := by
  apply tendsto_both_log_prefixes (s := s) (w := fun i ↦ (m i : ℝ)) (z := z)
    (fun i _ ↦ Nat.cast_nonneg _) hu hn hi₀ (Nat.cast_pos.mpr hm) ((one_lt_inv₀ hR).mpr hR₁)
  exact tendsto_relative_error_of_geometric (inv_pos.mpr hR) (inv_nonneg.mpr (hR.trans hgap).le)
    ((inv_lt_inv₀ (hR.trans hgap) hR).mpr hgap) he

/-- The nearest-circle conclusion in Mathlib's asymptotic notation. -/
theorem tendsto_both_log_prefixes_of_nearest_circle_isBigO {ι : Type*} {s : Finset ι}
    {m : ι → ℕ} {z : ι → ℂ} (hu : ∀ i ∈ s, ‖z i‖ = 1) (hn : ∀ i ∈ s, z i ≠ 1)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hm : 0 < m i₀) {R R₂ : ℝ} (hR : 0 < R) (hR₁ : R < 1)
    (hgap : R < R₂) {x : ℕ → ℝ}
    (he : (fun n : ℕ ↦ x n + R⁻¹^n * (∑ i ∈ s, (m i : ℝ)*(z i^n).re))
      =O[atTop] (fun n : ℕ ↦ R₂⁻¹^n)) :
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix x N)/(N:ℝ)) atTop (𝓝 (Real.log R⁻¹)) ∧
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ -x n) N)/(N:ℝ))
      atTop (𝓝 (Real.log R⁻¹)) := by
  obtain ⟨C, hC⟩ := he.bound
  apply tendsto_both_log_prefixes_of_nearest_circle hu hn hi₀ hm hR hR₁ hgap (C := C)
  filter_upwards [hC] with n h
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (hR.trans hgap).le) n)] using h

/-- Both signs of an everywhere subexponential absolute envelope have rate zero. -/
theorem tendsto_both_log_prefixes_of_subexponential {x : ℕ → ℝ}
    (h : ∀ A : ℝ, 1 < A → ∃ B : ℝ, 0 ≤ B ∧ ∀ n, |x n| ≤ B*A^n) :
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix x N)/(N:ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ -x n) N)/(N:ℝ)) atTop (𝓝 0) := by
  constructor <;> apply tendsto_log_positivePrefix_of_subexponential <;> intro A hA
  · obtain ⟨B, hB, hv⟩ := h A hA
    exact ⟨B, hB, fun n ↦ (le_abs_self _).trans (hv n)⟩
  · obtain ⟨B, hB, hv⟩ := h A hA
    exact ⟨B, hB, fun n ↦ (neg_le_abs _).trans (hv n)⟩

/-- Conversion to the ordinary real phases used by a disk-zero expansion. -/
theorem wave_exp_mul_I (θ : ℝ) (n : ℕ) :
    wave (Complex.exp ((θ : ℂ)*Complex.I)) n = Real.cos ((n:ℝ)*θ) := by
  rw [wave, ← Complex.exp_nat_mul,
    show (n:ℂ)*((θ:ℂ)*Complex.I) = (((n:ℝ)*θ : ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

theorem exists_length_both_cosine_signs {ι : Type*} {s : Finset ι} {w θ : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hn : ∀ i ∈ s, Complex.exp ((θ i : ℂ)*Complex.I) ≠ 1)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hpos : 0 < w i₀) :
    ∃ K : ℕ, 0 < K ∧ ∀ b : ℕ,
      (∃ k < K, w i₀/8 < ∑ i ∈ s, w i * Real.cos (((b+k : ℕ):ℝ)*θ i)) ∧
      (∃ k < K, (∑ i ∈ s, w i * Real.cos (((b+k : ℕ):ℝ)*θ i)) < -(w i₀/8)) := by
  simpa only [cosineSum, wave_exp_mul_I] using exists_length_both_signs hw
    (z := fun i ↦ Complex.exp ((θ i : ℂ)*Complex.I)) (fun i _ ↦ by simp) hn hi₀ hpos

private theorem prefix_triangle {x y e : ℕ → ℝ} (h : ∀ n, x n ≤ y n + e n) (N : ℕ) :
    positivePrefix x N ≤ positivePrefix y N * positivePrefix e N := by
  have hsum : ∑ k ∈ range N, max 0 (x (k+1)) ≤
      ∑ k ∈ range N, max 0 (y (k+1)) + ∑ k ∈ range N, max 0 (e (k+1)) := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro i _
    exact max_le (add_nonneg (le_max_left _ _) (le_max_left _ _))
      ((h _).trans (add_le_add (le_max_right _ _) (le_max_right _ _)))
  have hy : 0 ≤ ∑ k ∈ range N, max 0 (y (k+1)) := sum_nonneg fun _ _ ↦ le_max_left _ _
  have he : 0 ≤ ∑ k ∈ range N, max 0 (e (k+1)) := sum_nonneg fun _ _ ↦ le_max_left _ _
  dsimp [positivePrefix]
  nlinarith [mul_nonneg hy he]

private theorem log_prefix_triangle {x y e : ℕ → ℝ} (h : ∀ n, x n ≤ y n + e n) (N : ℕ) :
    Real.log (positivePrefix x N)/(N:ℝ) ≤
      Real.log (positivePrefix y N)/(N:ℝ)+Real.log (positivePrefix e N)/(N:ℝ) := by
  have hp (u : ℕ → ℝ) := zero_lt_one.trans_le (one_le_positivePrefix u N)
  have hh := Real.log_le_log (hp x) (prefix_triangle h N)
  rw [Real.log_mul (hp y).ne' (hp e).ne'] at hh
  rw [←add_div]
  exact div_le_div_of_nonneg_right hh (Nat.cast_nonneg _)

/-- Errors with subexponential positive prefixes preserve the ordinary logarithmic rate.
The same error envelope works after changing the signs of both measured sequences. -/
theorem tendsto_log_prefix_of_error {x y e : ℕ → ℝ} {l : ℝ} (herr : ∀ n, |y n-x n| ≤ e n)
    (he : Tendsto (fun N : ℕ ↦ Real.log (positivePrefix e N)/(N:ℝ)) atTop (𝓝 0))
    (hx : Tendsto (fun N : ℕ ↦ Real.log (positivePrefix x N)/(N:ℝ)) atTop (𝓝 l)) :
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix y N)/(N:ℝ)) atTop (𝓝 l) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa only [sub_zero] using hx.sub he)
    (by simpa only [add_zero] using hx.add he)
  · intro N
    exact sub_le_iff_le_add.mpr (log_prefix_triangle (x := x) (y := y) (e := e)
      (fun n ↦ by have hh := (abs_le.mp (herr n)).1; linarith) N)
  · exact log_prefix_triangle (fun n ↦ by have hh := (abs_le.mp (herr n)).2; linarith)

/-- A linear error in each Taylor coefficient preserves the rate, even on a sparse subsequence
of prefix cutoffs. The constants can depend on the measured function. -/
theorem tendsto_log_prefix_of_linear_error {x y : ℕ → ℝ} {l C : ℝ} (hC : 0≤C)
    (herr : ∀ n : ℕ, |y n-x n| ≤ C*n)
    (hx : Tendsto (fun N : ℕ ↦ Real.log (positivePrefix x N)/(N:ℝ)) atTop (𝓝 l)) :
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix y N)/(N:ℝ)) atTop (𝓝 l) := by
  apply tendsto_log_prefix_of_error herr _ hx
  apply tendsto_log_positivePrefix_of_subexponential
  intro A hA
  have hA' : 0<A-1 := by linarith
  refine ⟨C/(A-1), div_nonneg hC hA'.le, fun n ↦ ?_⟩
  have hpow := one_add_mul_le_pow (a := A-1) (by linarith : -2≤A-1) n
  rw [show 1+(A-1)=A from by ring] at hpow
  rw [div_mul_eq_mul_div, le_div_iff₀ hA']
  calc C * (n:ℝ) * (A-1) = C*((n:ℝ)*(A-1)) := by ring
       _ ≤ C*A^n := mul_le_mul_of_nonneg_left (by linarith) hC

/-- A sign can be selected independently at each prefix cutoff. The positive noise and the
negative noise have the same exponent because every sufficiently long block contains both
signs of the first pole circle. -/
def chosenPrefix (x : ℕ → ℝ) (negative : ℕ → Bool) (N : ℕ) : ℝ :=
  if negative N then positivePrefix (fun n ↦ -x n) N else positivePrefix x N

theorem tendsto_chosenPrefix {x : ℕ → ℝ} {l : ℝ} (neg : ℕ → Bool)
    (hp : Tendsto (fun N : ℕ ↦ Real.log (positivePrefix x N)/(N:ℝ)) atTop (𝓝 l))
    (hn : Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ -x n) N)/(N:ℝ)) atTop (𝓝 l)) :
    Tendsto (fun N : ℕ ↦ Real.log (chosenPrefix x neg N)/(N:ℝ)) atTop (𝓝 l) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hp ε hε,Metric.tendsto_nhds.mp hn ε hε] with n h₁ h₂
  by_cases h : neg n <;> simp [chosenPrefix, h, h₁, h₂]


/-- Every positive upper threshold occurs at arbitrarily large cutoffs. -/
def cofinalUpperZero (a : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ J : ℕ, ∃ N ≥ J, a N ≤ ε

theorem cofinalUpperZero_of_tendsto {a : ℕ → ℝ} (h : Tendsto a atTop (𝓝 0)) :
    cofinalUpperZero a := by
  intro ε hε J
  obtain ⟨N,hN⟩ := eventually_atTop.mp (h.eventually_lt_const hε)
  exact ⟨max J N,le_max_left _ _,(hN _ (le_max_right _ _)).le⟩

theorem not_cofinalUpperZero_of_positive_limit {a : ℕ → ℝ} {l : ℝ} (hl : 0<l)
    (h : Tendsto a atTop (𝓝 l)) : ¬ cofinalUpperZero a := by
  intro hs
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (h.eventually_const_lt (show l/2<l by linarith))
  obtain ⟨n,hn,hval⟩ := hs (l/2) (by positivity) J
  exact (hJ n hn).not_ge hval

end RiemannMasullo.SignedFrequency
