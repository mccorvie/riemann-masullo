module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-! # Multiplicative convolution of the rational prime Riesz sum

Multiplying the cutoff by a positive integer and inserting the matching
Dirichlet character regroups the prime terms by the prime divisors of the
product. For the full von Mangoldt coefficient this leaves an ordinary
character sum with logarithmic weight. Bounded character partial sums and
the Chebyshev estimate for proper prime powers give an unconditional
bound of order `(q + 1) * X * √X` for the complete first-prime convolution.
-/

public noncomputable section

open Finset

namespace RiemannMasullo

private theorem primeConvolution_regroup (X : ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ n ∈ Icc 1 X, ∑ b ∈ Icc 1 (X / n), f (n * b) b) =
      ∑ m ∈ Icc 1 X, ∑ b ∈ m.divisors, f m b := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun a : Σ _ : ℕ, ℕ => ⟨a.1 * a.2, a.2⟩)
    (fun a : Σ _ : ℕ, ℕ => ⟨a.1 / a.2, a.2⟩)
  · rintro ⟨n, b⟩ h
    obtain ⟨hn, hb⟩ := Finset.mem_sigma.mp h
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hnX⟩
    rcases Finset.mem_Icc.mp hb with ⟨hb1, hbn⟩
    dsimp at hn1 hnX hb1 hbn ⊢
    have he := (Nat.le_div_iff_mul_le (by omega : 0 < n)).mp hbn
    rw [Nat.mul_comm] at he
    apply Finset.mem_sigma.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), he⟩,
      Nat.mem_divisors.mpr ⟨dvd_mul_left b n, by positivity⟩⟩
  · rintro ⟨m, b⟩ h
    obtain ⟨hm, hb⟩ := Finset.mem_sigma.mp h
    rcases Finset.mem_Icc.mp hm with ⟨hm1, hmX⟩
    rcases Nat.mem_divisors.mp hb with ⟨hd, hm0⟩
    dsimp at hm1 hmX hd hm0 ⊢
    have hb0 : 0 < b := Nat.pos_of_dvd_of_pos hd (by omega)
    have hq := Nat.div_pos (Nat.le_of_dvd (by omega) hd) hb0
    have he := Nat.div_mul_cancel hd
    apply Finset.mem_sigma.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hq, (Nat.div_le_self m b).trans hmX⟩,
      Finset.mem_Icc.mpr ⟨hb0, (Nat.le_div_iff_mul_le hq).mpr (by simpa [Nat.mul_comm] using he.le.trans hmX)⟩⟩
  · rintro ⟨n, b⟩ h
    have hb := (Finset.mem_Icc.mp (Finset.mem_sigma.mp h).2).1
    dsimp at hb ⊢
    simp [Nat.mul_comm n b, Nat.mul_div_cancel_left n (by omega : 0 < b)]
  · rintro ⟨m, b⟩ h
    have hd := (Nat.mem_divisors.mp (Finset.mem_sigma.mp h).2).1
    exact congrArg (fun k : ℕ => (⟨k, b⟩ : Σ _ : ℕ, ℕ)) (Nat.div_mul_cancel hd)
  · intro a _
    rfl

/-- A complete character dilation of a Riesz sum regroups by divisors of the product. -/
theorem dirichletRiesz_mulConvolution {q : ℕ} (χ : DirichletCharacter ℂ q)
    (b : ℕ → ℂ) (x : ℝ) (X : ℕ) :
    (∑ n ∈ Icc 1 X, χ (n : ZMod q) *
      ∑ k ∈ Icc 1 (X / n), χ (k : ZMod q) * b k * ((x : ℂ) - (n * k : ℕ))) =
      ∑ m ∈ Icc 1 X, χ (m : ZMod q) * ((x : ℂ) - m) *
        ∑ k ∈ m.divisors, b k := by
  simp only [Finset.mul_sum]
  rw [← primeConvolution_regroup X (fun m k => χ (m : ZMod q) * ((x : ℂ) - m) * b k)]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Nat.cast_mul, map_mul]
  ring

/-- For actual primes, each prime divisor of the product contributes exactly once. -/
theorem dirichletPrimeRiesz_convolution_eq_primeFactors {q : ℕ}
    (χ : DirichletCharacter ℂ q) (x : ℝ) (X : ℕ) :
    (∑ n ∈ Icc 1 X, χ (n : ZMod q) *
      ∑ p ∈ (Icc 1 (X / n)).filter Nat.Prime,
        χ (p : ZMod q) * (Real.log p : ℂ) * ((x : ℂ) - (n * p : ℕ))) =
      ∑ m ∈ Icc 1 X, χ (m : ZMod q) * ((x : ℂ) - m) *
        ∑ p ∈ m.primeFactors, (Real.log p : ℂ) := by
  have h := dirichletRiesz_mulConvolution χ
    (fun k => if k.Prime then (Real.log k : ℂ) else 0) x X
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, ← Finset.sum_filter] at h
  convert h using 3
  rename_i m hm
  have he : m.divisors.filter Nat.Prime = m.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.mem_primeFactors]
    tauto
  rw [he]

/-- With all prime powers retained, the divisor sum is the logarithm of the product. -/
theorem dirichletVonMangoldtRiesz_convolution_eq_log {q : ℕ}
    (χ : DirichletCharacter ℂ q) (x : ℝ) (X : ℕ) :
    (∑ n ∈ Icc 1 X, χ (n : ZMod q) *
      ∑ k ∈ Icc 1 (X / n), χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ) *
        ((x : ℂ) - (n * k : ℕ))) =
      ∑ m ∈ Icc 1 X, χ (m : ZMod q) * ((x : ℂ) - m) * (Real.log m : ℂ) := by
  simpa only [← Complex.ofReal_sum, ArithmeticFunction.vonMangoldt_sum] using
    dirichletRiesz_mulConvolution χ (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) x X

private theorem primeConvolution_prefix_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℕ) :
    ‖∑ i ∈ range t, χ (i : ZMod q)‖ ≤ (q : ℝ) := by
  let S (n : ℕ) := ∑ i ∈ range n, χ (i : ZMod q)
  have hzero : S q = 0 := by
    rw [show S q = ∑ i : Fin q, χ (i.val : ZMod q) from
      (Fin.sum_univ_eq_sum_range (fun i : ℕ => χ (i : ZMod q)) q).symm]
    have he (i : Fin q) : (i.val : ZMod q) = ZMod.finEquiv q i := by
      rw [← ZMod.natCast_zmod_val (ZMod.finEquiv q i)]
      cases q with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ q => rfl
    simp_rw [he]
    exact ((ZMod.finEquiv q).toEquiv.sum_comp χ).trans (χ.sum_eq_zero_of_ne_one hχ)
  have hper : Function.Periodic S q := by
    intro n
    change (∑ i ∈ range (n + q), χ (i : ZMod q)) = S n
    rw [add_comm n q, Finset.sum_range_add]
    change S q + _ = _
    simp [hzero, S]
  have he := (hper.nat_mul (t / q)) (t % q)
  change S (t % q + t / q * q) = S (t % q) at he
  rw [Nat.mul_comm (t / q) q, Nat.mod_add_div] at he
  change ‖S t‖ ≤ _
  rw [he]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _ => χ.norm_le_one _)).trans
    (by simpa using (Nat.cast_le.mpr (Nat.mod_lt t (NeZero.pos q)).le : (t % q : ℕ) ≤ (q : ℝ))))

private theorem primeConvolution_abel {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (w : ℕ → ℝ) (hw : Monotone w)
    (hw0 : w 0 = 0) (X : ℕ) :
    ‖∑ i ∈ range (X + 1), w i • χ (i : ZMod q)‖ ≤ 2 * q * w X := by
  rw [Finset.sum_range_by_parts]
  simp only [Nat.add_sub_cancel]
  have hnon (i : ℕ) : 0 ≤ w i := hw0 ▸ hw (Nat.zero_le i)
  have hdiff (i : ℕ) : 0 ≤ w (i + 1) - w i := sub_nonneg.mpr (hw (Nat.le_succ i))
  have hsum : (∑ i ∈ range X, (w (i + 1) - w i)) = w X := by
    simpa [hw0] using Finset.sum_range_sub w X
  calc
    _ ≤ ‖w X • ∑ i ∈ range (X + 1), χ (i : ZMod q)‖ +
        ∑ i ∈ range X, ‖(w (i + 1) - w i) • ∑ j ∈ range (i + 1), χ (j : ZMod q)‖ :=
      (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ w X * q + ∑ i ∈ range X, (w (i + 1) - w i) * q := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnon X), abs_of_nonneg (hdiff _)]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (primeConvolution_prefix_bound χ hχ _) (hnon X)
      · exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (primeConvolution_prefix_bound χ hχ _) (hdiff i)
    _ = _ := by rw [← Finset.sum_mul, hsum]; ring

private theorem primeConvolution_riesz_log_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (X : ℕ) :
    ‖∑ m ∈ Icc 1 X, χ (m : ZMod q) * ((X : ℂ) - m) * (Real.log m : ℂ)‖ ≤
      4 * q * X * Real.log X := by
  have hl : Monotone (fun i : ℕ => Real.log i) := by
    intro i j hij
    by_cases hi : i = 0
    · simpa [hi] using Real.log_natCast_nonneg j
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hi) (by exact_mod_cast hij)
  have hm : Monotone (fun i : ℕ => (i : ℝ) * Real.log i) :=
    (fun i j hij => mul_le_mul (by exact_mod_cast hij) (hl hij)
      (Real.log_natCast_nonneg _) (by positivity))
  have h₁ := primeConvolution_abel χ hχ _ hl (by simp) X
  have h₂ := primeConvolution_abel χ hχ _ hm (by simp) X
  have he : (∑ m ∈ Icc 1 X, χ (m : ZMod q) * ((X : ℂ) - m) * (Real.log m : ℂ)) =
      (X : ℂ) * (∑ i ∈ range (X + 1), Real.log (i : ℝ) • χ (i : ZMod q)) -
        ∑ i ∈ range (X + 1), ((i : ℝ) * Real.log i) • χ (i : ZMod q) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Nat.range_succ_eq_Icc_zero,
      ← Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le X), Finset.sum_insert (by simp)]
    simp only [Nat.cast_zero, Real.log_zero, zero_smul, mul_zero, sub_zero, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_natCast]
    ring
  rw [he]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ X * (2 * q * Real.log X) + 2 * q * (X * Real.log X) := by
      rw [norm_mul, Complex.norm_natCast]
      exact add_le_add (mul_le_mul_of_nonneg_left h₁ (by positivity)) h₂
    _ = _ := by ring

/-- A nonprincipal character gives a uniform bound for the complete all-power convolution. -/
theorem norm_dirichletVonMangoldtRiesz_convolution_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (X : ℕ) :
    ‖∑ n ∈ Icc 1 X, χ (n : ZMod q) *
      ∑ k ∈ Icc 1 (X / n), χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ) *
        ((X : ℂ) - (n * k : ℕ))‖ ≤ 4 * q * X * Real.log X := by
  simpa only [Complex.ofReal_natCast, dirichletVonMangoldtRiesz_convolution_eq_log χ X X]
    using (dirichletVonMangoldtRiesz_convolution_eq_log χ X X).symm ▸
      primeConvolution_riesz_log_bound χ hχ X

private theorem primeConvolution_outer {q : ℕ} (χ : DirichletCharacter ℂ q)
    (b : ℕ → ℂ) (x : ℝ) (X : ℕ) :
    (∑ k ∈ Icc 1 X, χ (k : ZMod q) * b k * ∑ n ∈ Icc 1 (X / k),
      χ (n : ZMod q) * ((x : ℂ) - (k * n : ℕ))) =
      ∑ m ∈ Icc 1 X, χ (m : ZMod q) * ((x : ℂ) - m) * ∑ k ∈ m.divisors, b k := by
  simp only [Finset.mul_sum]
  conv_rhs => enter [2, m]; rw [← Nat.sum_div_divisors m
    (fun k => χ (m : ZMod q) * ((x : ℂ) - m) * b k)]
  rw [← primeConvolution_regroup X (fun m n => χ (m : ZMod q) * ((x : ℂ) - m) * b (m / n))]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := (Finset.mem_Icc.mp hn).1
  simp only [Nat.mul_div_left k hn', Nat.cast_mul, map_mul]
  ring

private theorem primeConvolution_ramp_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (X k : ℕ) (hk : 0 < k) :
    ‖∑ n ∈ Icc 1 (X / k), χ (n : ZMod q) * ((X : ℂ) - (k * n : ℕ))‖ ≤
      (q + 1 : ℝ) * X := by
  have hp (t : ℕ) : ‖∑ n ∈ Icc 1 t, χ (n : ZMod q)‖ ≤ (q + 1 : ℝ) := by
    have he := primeConvolution_prefix_bound χ hχ (t + 1)
    rw [Nat.range_succ_eq_Icc_zero, ← Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le t),
      Finset.sum_insert (by simp)] at he
    have he' : (∑ n ∈ Icc 1 t, χ (n : ZMod q)) =
        (χ (0 : ZMod q) + ∑ n ∈ Icc 1 t, χ (n : ZMod q)) - χ 0 := by abel
    rw [he']
    exact (norm_sub_le _ _).trans (add_le_add (by simpa using he) (χ.norm_le_one _))
  have he : (∑ n ∈ Icc 1 (X / k), χ (n : ZMod q) * ((X : ℂ) - (k * n : ℕ))) =
      ∑ u ∈ range X, ∑ n ∈ Icc 1 (u / k), χ (n : ZMod q) := by
    calc
      _ = ∑ n ∈ Icc 1 (X / k), ∑ u ∈ range X,
          if k * n ≤ u then χ (n : ZMod q) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        have hkn : k * n ≤ X := by
          simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hk).mp (Finset.mem_Icc.mp hn).2
        have hs : (range X).filter (fun u => k * n ≤ u) = Ico (k * n) X := by
          ext u
          simp [and_comm]
        rw [← Finset.sum_filter, hs]
        simp [Nat.cast_sub hkn, mul_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u hu
        rw [← Finset.sum_filter]
        congr 1
        ext n
        have huX := (Finset.mem_range.mp hu).le
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.le_div_iff_mul_le hk,
          Nat.mul_comm n k]
        omega
  rw [he]
  calc
    _ ≤ ∑ u ∈ range X, ‖∑ n ∈ Icc 1 (u / k), χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _u ∈ range X, (q + 1 : ℝ) := Finset.sum_le_sum (fun u _ => hp (u / k))
    _ = _ := by simp; ring

/-- The proper prime powers in the complete convolution cost the Chebyshev difference
times a linearly bounded character ramp, uniformly in the cutoff. -/
theorem norm_dirichletPrimeRiesz_convolution_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (X : ℕ) :
    ‖∑ n ∈ Icc 1 X, χ (n : ZMod q) *
      ∑ p ∈ (Icc 1 (X / n)).filter Nat.Prime,
        χ (p : ZMod q) * (Real.log p : ℂ) * ((X : ℂ) - (n * p : ℕ))‖ ≤
      4 * q * X * Real.log X + (q + 1 : ℝ) * X * (Chebyshev.psi X - Chebyshev.theta X) := by
  let b (k : ℕ) : ℂ := if k.Prime then (Real.log k : ℂ) else 0
  let r (k : ℕ) : ℂ := ∑ n ∈ Icc 1 (X / k), χ (n : ZMod q) * ((X : ℂ) - (k * n : ℕ))
  let A (k : ℕ) : ℂ := χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ) * r k
  have houter (c : ℕ → ℂ) :
      (∑ n ∈ Icc 1 X, χ (n : ZMod q) * ∑ k ∈ Icc 1 (X / n),
        χ (k : ZMod q) * c k * ((X : ℂ) - (n * k : ℕ))) =
        ∑ k ∈ Icc 1 X, χ (k : ZMod q) * c k * r k := by
    simpa only [Complex.ofReal_natCast, r] using
      (dirichletRiesz_mulConvolution χ c X X).trans (primeConvolution_outer χ c X X).symm
  have hfull : ‖∑ k ∈ Icc 1 X, A k‖ ≤ 4 * q * X * Real.log X := by
    rw [show (∑ k ∈ Icc 1 X, A k) = _ from (houter (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))).symm]
    exact norm_dirichletVonMangoldtRiesz_convolution_le χ hχ X
  have hprime := houter b
  simp only [b, mul_ite, ite_mul, mul_zero, zero_mul, ← Finset.sum_filter] at hprime
  rw [hprime]
  have hsame : (∑ k ∈ (Icc 1 X).filter Nat.Prime, χ (k : ZMod q) * (Real.log k : ℂ) * r k) =
      ∑ k ∈ (Icc 1 X).filter Nat.Prime, A k := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [A, ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hk).2]
  rw [hsame, eq_sub_of_add_eq (Finset.sum_filter_add_sum_filter_not (Icc 1 X) Nat.Prime A)]
  apply (norm_sub_le _ _).trans (add_le_add hfull ?_)
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast,
    show Ioc 0 X = Icc 1 X from by ext k; simp; omega, Finset.mul_sum]
  apply (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro k hk
  have hk' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
  have hv := ArithmeticFunction.vonMangoldt_nonneg (n := k)
  simp only [A, norm_mul, Complex.norm_real, Real.norm_of_nonneg hv]
  calc
    _ ≤ (1 * ArithmeticFunction.vonMangoldt k) * ((q + 1 : ℝ) * X) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right (χ.norm_le_one _) hv)
        (primeConvolution_ramp_bound χ hχ X k hk') (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The genuine prime convolution is of square-root order relative to its Riesz weight,
with an absolute constant and explicit linear dependence on the modulus. -/
theorem exists_bound_dirichletPrimeRiesz_convolution :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ X : ℕ, ‖∑ n ∈ Icc 1 X, χ (n : ZMod q) *
        ∑ p ∈ (Icc 1 (X / n)).filter Nat.Prime,
          χ (p : ZMod q) * (Real.log p : ℂ) * ((X : ℂ) - (n * p : ℕ))‖ ≤
        C * (q + 1 : ℝ) * X * Real.sqrt X := by
  obtain ⟨A, hA⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨8 + max 0 A, by positivity, ?_⟩
  intro q inst χ hχ X
  have hlog : Real.log (X : ℝ) ≤ 2 * Real.sqrt X := by
    simpa [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm] using
      Real.log_natCast_le_rpow_div X (show (0 : ℝ) < 1 / 2 by norm_num)
  apply (norm_dirichletPrimeRiesz_convolution_le χ hχ X).trans
  calc
    _ ≤ 4 * (q + 1 : ℝ) * X * (2 * Real.sqrt X) +
        (q + 1 : ℝ) * X * (max 0 A * Real.sqrt X) := by
      apply add_le_add
      · gcongr
        · linarith
      · exact mul_le_mul_of_nonneg_left ((hA X).trans
          (mul_le_mul_of_nonneg_right (le_max_right 0 A) (Real.sqrt_nonneg _))) (by positivity)
    _ = _ := by ring

end RiemannMasullo
