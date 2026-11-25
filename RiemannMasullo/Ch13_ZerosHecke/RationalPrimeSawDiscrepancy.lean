module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic

/-! # Signed prime rounding from finite phase counts

The centered square-root rounding term in a prime prefix is approximated by the signed
average of finite phase counts. Using `H` equally spaced thresholds costs at most half
of one grid interval times the total mass.
-/

public noncomputable section

open Finset

namespace RiemannMasullo

private theorem primeSaw_grid_count {H : ℕ} (hH : 0 < H) {t : ℝ} (ht : t ≤ 1) :
    (∑ j ∈ range H, if (j : ℝ)/H < t then (1 : ℝ) else 0) = (⌈t*H⌉₊ : ℝ) := by
  have hp : (0 : ℝ) < H := by exact_mod_cast hH
  have hceil : ⌈t*H⌉₊ ≤ H := Nat.ceil_le.mpr (by nlinarith)
  have hr : (range H).filter (fun j : ℕ ↦ (j : ℝ)/H < t) = range ⌈t*H⌉₊ := by
    ext j
    simp only [mem_filter, mem_range, div_lt_iff₀ hp, ← Nat.lt_ceil]
    omega
  rw [← sum_filter, hr]
  simp


private theorem primeSaw_grid_mean {H : ℕ} (hH : 0 < H) :
    (∑ j ∈ range H, (1 - (j : ℝ)/H)) = ((H : ℝ)+1)/2 := by
  have hp : (0 : ℝ) < H := by exact_mod_cast hH
  have hsum : (∑ j ∈ range H, (j : ℝ))*2 = (H : ℝ)*((H : ℝ)-1) := by
    have h := congrArg ((↑) : ℕ → ℝ) (sum_range_id_mul_two H)
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_two, Nat.cast_sub (by omega : 1 ≤ H),
      Nat.cast_one] using h
  rw [sum_sub_distrib, ← sum_div]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  field_simp
  linarith



private theorem primeSaw_grid_error {H : ℕ} (hH : 0 < H) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    |t - 1/2 - (∑ j ∈ range H, ((if (j : ℝ)/H < t then 1 else 0) - (1-(j : ℝ)/H))) / H| ≤
      1 / (2 * (H : ℝ)) := by
  have hp : (0 : ℝ) < H := by exact_mod_cast hH
  have h₁ := Nat.le_ceil (t*H)
  have h₂ := Nat.ceil_lt_add_one (mul_nonneg ht hp.le)
  rw [sum_sub_distrib, primeSaw_grid_count hH ht', primeSaw_grid_mean hH, abs_le]
  constructor
  · field_simp
    rw [mul_comm t (H : ℝ)] at h₂
    linarith
  · field_simp
    linarith



private theorem primeSaw_weighted_grid {ι : Type*} (S : Finset ι) (a r : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hr : ∀ i ∈ S, r i ∈ Set.Icc 0 1) {H : ℕ} (hH : 0 < H) :
    let M := ∑ i ∈ S, a i
    let D (j : ℕ) := (∑ i ∈ S with (j : ℝ)/H < r i, a i) - (1-(j : ℝ)/H)*M
    |(∑ i ∈ S, (r i - 1/2)*a i) - (∑ j ∈ range H, D j)/H| ≤ M/(2*H) := by
  classical
  intro M D
  let g (i : ι) (j : ℕ) : ℝ := (if (j : ℝ)/H < r i then 1 else 0) - (1-(j : ℝ)/H)
  have heq (j : ℕ) : D j = ∑ i ∈ S, g i j * a i := by
    dsimp only [D, M]
    rw [sum_filter, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [g]
    split_ifs <;> ring
  have havg : (∑ j ∈ range H, D j)/H =
      ∑ i ∈ S, ((∑ j ∈ range H, g i j)/H) * a i := by
    simp_rw [heq]
    rw [sum_comm, sum_div]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← sum_mul]
    ring
  rw [havg, ← sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ S, |(r i - 1/2)*a i - ((∑ j ∈ range H, g i j)/H)*a i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, (1/(2*(H : ℝ))) * a i := by
      refine sum_le_sum fun i hi ↦ ?_
      rw [← sub_mul, abs_mul, abs_of_nonneg (ha i hi)]
      exact mul_le_mul_of_nonneg_right (primeSaw_grid_error hH (hr i hi).1 (hr i hi).2) (ha i hi)
    _ = _ := by rw [← mul_sum]; change _ = (∑ i ∈ S, a i)/_; ring



/-- The excess log-weighted prime mass above one square-root phase threshold.
The phase is the upward rounding error, which lies in the half-open unit interval. -/
@[expose] def rationalPrimeSquareGridDiscrepancy (w : ℝ → ℝ) (N H j : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE N with (j : ℝ)/H < (⌈Real.sqrt (p : ℕ)⌉₊ : ℝ) - Real.sqrt p,
    Real.log p * w (Real.log p)) -
  (1-(j : ℝ)/H) * ∑ p ∈ Nat.primesLE N, Real.log p * w (Real.log p)



/-- The signed average of the measured grid discrepancies approximates the actual
centered first-prime saw sum with an error at most the total mass divided by `2H`. -/
theorem rationalPrimeSquareSaw_grid (w : ℝ → ℝ) (hw : ∀ x, 0 ≤ w x) (N H : ℕ) (hH : 0 < H) :
    |(∑ p ∈ Nat.primesLE N, ((⌈Real.sqrt (p : ℕ)⌉₊ : ℝ) - Real.sqrt p - 1/2) *
        (Real.log p * w (Real.log p))) - (∑ j ∈ range H, rationalPrimeSquareGridDiscrepancy w N H j)/H| ≤
      (∑ p ∈ Nat.primesLE N, Real.log p * w (Real.log p))/(2*H) := by
  apply primeSaw_weighted_grid (Nat.primesLE N) (fun p ↦ Real.log p * w (Real.log p))
    (fun p ↦ (⌈Real.sqrt (p : ℕ)⌉₊ : ℝ) - Real.sqrt p) _ _ hH
  · intro p hp
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)) (hw _)
  · intro p _
    exact ⟨sub_nonneg.mpr (Nat.le_ceil _), by linarith [Nat.ceil_lt_add_one (Real.sqrt_nonneg (p : ℝ))]⟩



/-- A uniform bound on the finitely many log-weighted prime count discrepancies gives a
bound for the signed saw sum, with a separate mesh error. -/
theorem rationalPrimeSquareSaw_le_of_grid_bound (w : ℝ → ℝ) (hw : ∀ x, 0 ≤ w x)
    {N H : ℕ} (hH : 0 < H) {D : ℝ}
    (hD : ∀ j < H, |rationalPrimeSquareGridDiscrepancy w N H j| ≤ D) :
    |∑ p ∈ Nat.primesLE N, ((⌈Real.sqrt (p : ℕ)⌉₊ : ℝ) - Real.sqrt p - 1/2) *
        (Real.log p * w (Real.log p))| ≤
      D + (∑ p ∈ Nat.primesLE N, Real.log p * w (Real.log p))/(2*H) := by
  let G := (∑ j ∈ range H, rationalPrimeSquareGridDiscrepancy w N H j)/(H : ℝ)
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hg : |G| ≤ D := by
    dsimp only [G]
    rw [abs_div, abs_of_pos hHr, div_le_iff₀ hHr]
    calc
      _ ≤ ∑ j ∈ range H, |rationalPrimeSquareGridDiscrepancy w N H j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ range H, D := sum_le_sum fun j hj ↦ hD j (mem_range.mp hj)
      _ = _ := by simp [mul_comm]
  set A := ∑ p ∈ Nat.primesLE N, ((⌈Real.sqrt (p : ℕ)⌉₊ : ℝ) - Real.sqrt p - 1/2) *
    (Real.log p * w (Real.log p))
  have hA : |A| ≤ |A-G| + |G| := by simpa using abs_sub_le A G 0
  linarith only [hA, hg, rationalPrimeSquareSaw_grid w hw N H hH]

private theorem primeSaw_mass_le (w : ℝ → ℝ) {C : ℝ} (hw : ∀ x, w x ∈ Set.Icc 0 C) (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, Real.log p * w (Real.log p)) ≤ C * Real.log 4 * N := by
  have hC : 0 ≤ C := (hw 0).1.trans (hw 0).2
  calc
    _ ≤ ∑ p ∈ Nat.primesLE N, C * Real.log p := by
      refine sum_le_sum fun p hp ↦ ?_
      rw [mul_comm C]
      exact mul_le_mul_of_nonneg_left (hw _).2
        (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le))
    _ = C * Chebyshev.theta N := by rw [← mul_sum, Chebyshev.theta_eq_sum_primesLE_log]
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N)) hC



/-- Signed first-prime rounding is sublinear if, at every fixed resolution, the
signed mean of the phase-count discrepancies is sublinear. The bounded weight and
Chebyshev's theorem provide the mass bound for passage to fine resolutions. -/
theorem rationalPrimeSquareSaw_tendsto_zero_of_grid (w : ℝ → ℝ) {C : ℝ}
    (hw : ∀ x, w x ∈ Set.Icc 0 C)
    (hgrid : ∀ H : ℕ, 0 < H → Filter.Tendsto
      (fun N : ℕ ↦ (∑ j ∈ range H, rationalPrimeSquareGridDiscrepancy w N H j)/H/N)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N : ℕ ↦ (∑ p ∈ Nat.primesLE N,
      ((⌈Real.sqrt (p : ℕ)⌉₊ : ℝ) - Real.sqrt p - 1/2) * (Real.log p * w (Real.log p)))/N)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let B := C * Real.log 4
  have hC : 0 ≤ C := (hw 0).1.trans (hw 0).2
  have hB : 0 ≤ B := mul_nonneg hC (Real.log_nonneg (by norm_num))
  obtain ⟨H, hH⟩ := exists_nat_gt (B/ε)
  have hHr : (0 : ℝ) < H := (div_nonneg hB hε.le).trans_lt hH
  have hHn : 0 < H := by exact_mod_cast hHr
  have hsmall : B/(2*H) < ε/2 := by
    have hb := (div_lt_iff₀ hε).mp hH
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.1 (hgrid H hHn)) (ε/2) (half_pos hε)
  refine ⟨max N₀ 1, fun N hN ↦ ?_⟩
  have hn : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N₀ 1).trans hN))
  let A := ∑ p ∈ Nat.primesLE N,
    ((⌈Real.sqrt (p : ℕ)⌉₊ : ℝ) - Real.sqrt p - 1/2) * (Real.log p * w (Real.log p))
  let G := (∑ j ∈ range H, rationalPrimeSquareGridDiscrepancy w N H j)/(H : ℝ)
  have hg : |G/N| < ε/2 := by
    simpa only [Real.dist_eq, sub_zero] using hN₀ N ((le_max_left N₀ 1).trans hN)
  have hdiff : |A/N - G/N| ≤ B/(2*H) := by
    rw [← sub_div, abs_div, abs_of_pos hn, div_le_iff₀ hn]
    calc
      |A-G| ≤ _ := rationalPrimeSquareSaw_grid w (fun x ↦ (hw x).1) N H hHn
      _ ≤ (B*N)/(2*H) := div_le_div_of_nonneg_right (primeSaw_mass_le w hw N) (by positivity)
      _ = _ := by ring
  change dist (A/N) 0 < ε
  rw [Real.dist_eq, sub_zero]
  calc
    _ ≤ |A/N-G/N| + |G/N| := by simpa using abs_sub_le (A/N) (G/N) 0
    _ < ε := by linarith



private theorem primeSaw_near_grid (t : ℝ) (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℕ, L < H ∧ ∃ m : ℤ, |t*H-m| < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1/ε)
  have hn' : 0 < n := by exact_mod_cast ((by positivity : 0 < 1/ε).trans hn)
  obtain ⟨k, hk, _, h⟩ := Real.exists_nat_abs_mul_sub_round_le (((L+1 : ℕ) : ℝ)*t) hn'
  refine ⟨k*(L+1), by nlinarith [Nat.succ_le_of_lt hk], round ((k : ℝ)*((L+1 : ℕ)*t)), ?_⟩
  have hsmall : 1/((n : ℝ)+1) < ε := by
    apply (div_lt_iff₀ (by positivity)).2
    have h' := (div_lt_iff₀ hε).mp hn
    nlinarith
  convert h.trans_lt hsmall using 1
  push_cast
  ring_nf

private theorem primeSaw_half_integer (x : ℝ) (m k : ℤ) :
    1/2 - |x-m| ≤ |x-k+1/2| := by
  have hsep : (1/2 : ℝ) ≤ |(m : ℝ)-k+1/2| := by
    rcases le_or_gt k m with h|h
    · have h' : (k : ℝ) ≤ m := by exact_mod_cast h
      exact le_trans (by linarith) (le_abs_self _)
    · have h' : (m : ℝ)+1 ≤ k := by exact_mod_cast (show m+1 ≤ k by omega)
      exact le_trans (by linarith) (neg_le_abs _)
  have htri := abs_add_le (x-k+1/2) ((m : ℝ)-x)
  rw [show x-k+1/2+(m-x)=(m : ℝ)-k+1/2 by ring, abs_sub_comm (m : ℝ) x] at htri
  linarith





/-- Even for the actual single prime at cutoff two, arbitrarily fine grids approach
the constant `1/2` in the mass-normalized mesh error. -/
theorem rationalPrimeSquareSaw_grid_sharp_at_two (w : ℝ → ℝ) (hw : 0 < w (Real.log 2))
    {ε : ℝ} (hε : 0 < ε) (L : ℕ) :
    let a := Real.log 2 * w (Real.log 2)
    let t := (⌈Real.sqrt 2⌉₊ : ℝ) - Real.sqrt 2
    ∃ H : ℕ, L < H ∧ (1/2 - ε)*a <
      H * |(t - 1/2)*a - (∑ j ∈ range H, rationalPrimeSquareGridDiscrepancy w 2 H j)/H| := by
  intro a t
  obtain ⟨H, hHL, m, hm⟩ := primeSaw_near_grid t L hε
  have hH : 0 < H := by omega
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have ha : 0 < a := mul_pos (Real.log_pos (by norm_num)) hw
  have ht : t ≤ 1 := by
    dsimp [t]
    linarith [Nat.ceil_lt_add_one (Real.sqrt_nonneg (2 : ℝ))]
  have hD (j : ℕ) : rationalPrimeSquareGridDiscrepancy w 2 H j =
      ((if (j : ℝ)/H < t then 1 else 0) - (1-(j : ℝ)/H)) * a := by
    dsimp only [rationalPrimeSquareGridDiscrepancy, t, a]
    rw [show Nat.primesLE 2 = {2} by decide, sum_filter]
    simp only [sum_singleton, Nat.cast_ofNat]
    split_ifs <;> ring
  have hscale : (H : ℝ)*((t-1/2) -
      (∑ j ∈ range H, ((if (j : ℝ)/H < t then 1 else 0) - (1-(j : ℝ)/H)))/H) =
      t*H - (⌈t*H⌉₊ : ℝ) + 1/2 := by
    rw [sum_sub_distrib, primeSaw_grid_count hH ht, primeSaw_grid_mean hH]
    field_simp
    ring
  refine ⟨H, hHL, ?_⟩
  simp_rw [hD]
  rw [← sum_mul, show ∀ b : ℝ, b*a/(H : ℝ) = (b/H)*a by intro b; ring,
    ← sub_mul, abs_mul, abs_of_pos ha, ← mul_assoc (H : ℝ) _ a]
  have habs (z : ℝ) : (H : ℝ)*|z| = |(H : ℝ)*z| := by rw [abs_mul, abs_of_pos hHr]
  rw [habs, hscale]
  apply mul_lt_mul_of_pos_right _ ha
  have h := primeSaw_half_integer (t*H) m (⌈t*H⌉₊ : ℕ)
  push_cast at h
  linarith


end RiemannMasullo
