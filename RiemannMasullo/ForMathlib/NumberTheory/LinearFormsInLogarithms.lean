module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Transcendental.Liouville.Basic

/-! # Separation of the exponential lattices of two integer logarithms -/

@[expose] public section

namespace RiemannMasullo

/-- A rational ratio even allows degree zero, with explicit constant. -/
private theorem baker_two_logarithms_dependent_degree_zero (p q k l : ℕ) (hq : 1 < q) (hk : 0 < k) (he : p ^ k = q ^ l) :
    ∀ m n : ℤ, (m : ℝ) * Real.log p + n * Real.log q ≠ 0 →
      1 ≤ ((k : ℝ) / Real.log q) * |(m : ℝ) * Real.log p + n * Real.log q| := by
  intro m n h
  have hQ : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hlogs := congrArg (fun a : ℕ ↦ Real.log (a : ℝ)) he
  simp only [Nat.cast_pow, Real.log_pow] at hlogs
  have hlin : ((k : ℝ) / Real.log q) * ((m : ℝ) * Real.log p + n * Real.log q) =
      ((m * l + n * k : ℤ) : ℝ) := by
    push_cast
    field_simp
    linear_combination (m : ℝ) * hlogs
  have hn : m * l + n * k ≠ (0 : ℤ) := by
    intro h0
    rw [h0, Int.cast_zero] at hlin
    exact (mul_ne_zero (div_pos hk' hQ).ne' h) hlin
  have hi : (1 : ℤ) ≤ |m * l + n * k| := by exact Int.add_one_le_iff.mpr (abs_pos.mpr hn)
  have hh := congrArg abs hlin
  rw [abs_mul, abs_of_pos (div_pos hk' hQ)] at hh
  rw [hh]
  exact_mod_cast hi

/-- The non-Liouville estimate on a single ratio gives the exact target, including zero
coefficients and both signs. Doubling denominators puts every nonzero integer slope
in the range of Mathlib's definition. -/
private theorem baker_two_logarithms_of_not_liouville {P Q : ℝ} (hQ : 0 < Q) (h : ¬ Liouville (P / Q)) :
    (∃ d : ℕ, ∃ B ≥ (0 : ℝ), ∀ m n : ℤ, (m : ℝ) * P + n * Q ≠ 0 →
      1 ≤ B * (1 + |(m : ℝ)| + |(n : ℝ)|) ^ d * |(m : ℝ) * P + n * Q|) := by
  simp only [Liouville, not_forall, not_exists, not_and, not_lt] at h
  obtain ⟨d, hd⟩ := h
  refine ⟨d, 2 ^ d / Q, by positivity, ?_⟩
  have H (m n : ℤ) (hm : 0 < m) (hn : (m : ℝ) * P + n * Q ≠ 0) :
      1 ≤ 2 ^ d / Q * (1 + |(m : ℝ)| + |(n : ℝ)|) ^ d * |(m : ℝ) * P + n * Q| := by
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
    have he : P / Q - ((-2 * n : ℤ) : ℝ) / ((2 * m : ℤ) : ℝ) =
        ((m : ℝ) * P + n * Q) / (m * Q) := by push_cast; field_simp; ring
    have hx : P / Q ≠ ((-2 * n : ℤ) : ℝ) / ((2 * m : ℤ) : ℝ) := by
      rw [← sub_ne_zero, he]
      exact div_ne_zero hn (mul_pos hm' hQ).ne'
    have hh := hd (-2 * n) (2 * m) (by omega) hx
    rw [he, abs_div, abs_of_pos (mul_pos hm' hQ)] at hh
    push_cast at hh
    have hpos : 0 < (2 * (m : ℝ)) ^ d := by positivity
    have step : (m : ℝ) * Q ≤ (2 * (m : ℝ)) ^ d * |(m : ℝ) * P + n * Q| := by
      apply (div_le_div_iff₀ hpos (mul_pos hm' hQ)).mp at hh
      simpa [mul_comm] using hh
    have hbase : (m : ℝ) ≤ 1 + |(m : ℝ)| + |(n : ℝ)| := by linarith [le_abs_self (m : ℝ), abs_nonneg (n : ℝ)]
    have hpow : (2 * (m : ℝ)) ^ d ≤ 2 ^ d * (1 + |(m : ℝ)| + |(n : ℝ)|) ^ d := by
      rw [← mul_pow]
      gcongr
    have hi := (le_mul_of_one_le_left hQ.le hm1).trans (step.trans (mul_le_mul_of_nonneg_right hpow (abs_nonneg _)))
    convert (one_le_div hQ).mpr hi using 1; ring
  intro m n hne
  rcases lt_trichotomy 0 m with hm | rfl | hm
  · exact H m n hm hne
  · simp only [Int.cast_zero, zero_mul, zero_add, abs_zero, add_zero] at hne ⊢
    have hn : n ≠ 0 := by intro he; simp [he] at hne
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast (Int.add_one_le_iff.mpr (abs_pos.mpr hn))
    rw [abs_mul, abs_of_pos hQ]
    calc 1 ≤ 2 ^ d * (1 + |(n : ℝ)|) ^ d * |(n : ℝ)| := by
           exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
             (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by linarith [abs_nonneg (n : ℝ)]))) hn1
         _ = 2 ^ d / Q * (1 + |(n : ℝ)|) ^ d * (|(n : ℝ)| * Q) := by field_simp
  · have e : ((-m : ℤ) : ℝ) * P + ((-n : ℤ) : ℝ) * Q = -((m : ℝ) * P + n * Q) := by push_cast; ring
    have h' := H (-m) (-n) (by omega) (e ▸ neg_ne_zero.mpr hne)
    rw [e, abs_neg] at h'
    simpa only [Int.cast_neg, abs_neg] using h'

/-- Classical input: for multiplicatively independent integers `1 < p < q`, the
ratio of their real logarithms has finite irrationality measure. This is the
non-effective two-logarithm consequence of A. Baker and G. Wüstholz,
*Logarithmic forms and group varieties*, J. reine angew. Math. 442 (1993), 19–62. -/
private theorem baker_two_logarithms_not_liouville_of_independent (p q : ℕ)
    (hp : 1 < p) (hpq : p < q) (hind : ¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ p ^ k = q ^ l) :
    ¬ Liouville (Real.log p / Real.log q) := by
  sorry

/-- The Baker–Wüstholz theorem on linear forms in logarithms, for two fixed integers:
A. Baker and G. Wüstholz, *Logarithmic forms and group varieties*, J. reine angew.
Math. 442 (1993), 19–62. For two fixed integers greater than one, the reciprocal
of a nonzero integral linear form in their real logarithms grows at most
polynomially in the coefficients. Proved here (#7362) from the classical input
`baker_two_logarithms_not_liouville_of_independent`, the case of multiplicatively independent
integers, which is not proved in Lean. -/
private theorem baker_two_logarithms (p q : ℕ) (hp : 1 < p) (hq : 1 < q) :
    ∃ d : ℕ, ∃ B ≥ (0 : ℝ), ∀ m n : ℤ,
      (m : ℝ) * Real.log p + n * Real.log q ≠ 0 →
      1 ≤ B * (1 + |(m : ℝ)| + |(n : ℝ)|) ^ d *
        |(m : ℝ) * Real.log p + n * Real.log q| := by
  wlog hpq : p ≤ q generalizing p q
  · obtain ⟨d, B, hB, h⟩ := this q p hq hp (by omega)
    refine ⟨d, B, hB, fun m n hn ↦ ?_⟩
    simpa only [add_assoc, add_left_comm, add_comm] using
      h n m (by rwa [add_comm])
  by_cases hdep : ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ p ^ k = q ^ l
  · obtain ⟨k, l, hk, _, he⟩ := hdep
    refine ⟨0, (k : ℝ) / Real.log q, div_nonneg (by positivity)
      (Real.log_pos (by exact_mod_cast hq)).le, ?_⟩
    simpa only [pow_zero, mul_one] using baker_two_logarithms_dependent_degree_zero p q k l hq hk he
  have hlt : p < q := lt_of_le_of_ne hpq fun h ↦ hdep ⟨1, 1, by decide, by decide, by simpa using h⟩
  exact baker_two_logarithms_of_not_liouville (Real.log_pos (by exact_mod_cast hq))
    (baker_two_logarithms_not_liouville_of_independent p q hp hlt hdep)

/-- Fix a positive common order `N`. At a zero of the first exponential
denominator, every `N`th root of the second exponential has polynomially
bounded totalized reciprocal distance from one. -/
theorem polynomial_bound_inv_one_sub_of_exp_eq_one (p q N : ℕ)
    (hp : 1 < p) (hq : 1 < q) (hN : 0 < N) :
    ∃ d : ℕ, ∃ C ≥ (0 : ℝ), ∀ s z : ℂ,
      Complex.exp (N * (-(Real.log p : ℂ) * s)) = 1 →
      z ^ N = Complex.exp (N * (-(Real.log q : ℂ) * s)) →
      ‖(1 - z)⁻¹‖ ≤ C * (1 + ‖s‖) ^ d := by
  obtain ⟨d, B, hB, hbak⟩ := baker_two_logarithms p q hp hq
  let P := Real.log (p : ℝ)
  let Q := Real.log (q : ℝ)
  have hP : 0 < P := Real.log_pos (by exact_mod_cast hp)
  have hQ : 0 < Q := Real.log_pos (by exact_mod_cast hq)
  let U : ℂ := 2 * Real.pi * Complex.I
  have hU : 1 ≤ ‖U‖ := by
    simp only [U, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_I, mul_one, Complex.norm_ofNat]
    linarith [Real.pi_gt_three]
  let K : ℝ := 1 + N * (1 + P + Q)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let C := max 2 (B * K ^ d * (2 * N * P))
  have hC : 2 ≤ C := le_max_left _ _
  refine ⟨d, C, by linarith, fun s z h₁ h₂ ↦ ?_⟩
  have hweight : 1 ≤ (1 + ‖s‖) ^ d := one_le_pow₀ (by linarith [norm_nonneg s])
  have hmajor : 2 ≤ C * (1 + ‖s‖) ^ d :=
    hC.trans (le_mul_of_one_le_right (by linarith) hweight)
  by_cases heq : z = 1
  · simpa [heq] using (show 0 ≤ C * (1 + ‖s‖) ^ d by linarith)
  have hdist : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm heq))
  rw [norm_inv]
  by_cases hnear : ‖1 - z‖ ≤ 1 / 2
  · have hlog : ‖Complex.log z‖ ≤ 2 * ‖1 - z‖ := by
      have h := Complex.norm_log_one_add_half_le_self (z := z - 1) (by rwa [norm_sub_rev])
      rw [add_sub_cancel, norm_sub_rev] at h
      linarith
    have hz : z ≠ 0 := by
      rintro rfl
      norm_num at hnear
    -- Take logarithms of both powered equations and eliminate the height.
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h₁
    change (N : ℂ) * (-(P : ℂ) * s) = n * U at hn
    have hexp : Complex.exp (N * Complex.log z) =
        Complex.exp (N * (-(Q : ℂ) * s)) := by
      rw [Complex.exp_nat_mul, Complex.exp_log hz]
      exact h₂
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    change (N : ℂ) * Complex.log z = N * (-(Q : ℂ) * s) + m * U at hm
    let L : ℝ := m * P + n * Q
    have hform : (P : ℂ) * N * Complex.log z = (L : ℂ) * U := by
      dsimp only [L]
      push_cast
      linear_combination (P : ℂ) * hm + (Q : ℂ) * hn
    have hL : L ≠ 0 := by
      intro h
      have hzero := hform
      rw [h, Complex.ofReal_zero, zero_mul] at hzero
      have hzlog : Complex.log z = 0 := (mul_eq_zero.mp hzero).resolve_left
        (mul_ne_zero (by exact_mod_cast hP.ne') (by exact_mod_cast hN.ne'))
      exact heq (by rw [← Complex.exp_log hz, hzlog, Complex.exp_zero])
    have norm_turn (k : ℤ) : |(k : ℝ)| ≤ ‖(k : ℂ) * U‖ := by
      rw [norm_mul, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      exact le_mul_of_one_le_right (abs_nonneg _) hU
    have hn' := norm_turn n
    rw [← hn, norm_mul, norm_mul, norm_neg, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hP] at hn'
    have hm' := (norm_turn m).trans ((congrArg norm (eq_sub_of_add_eq' hm.symm)).le.trans
      (norm_sub_le _ _))
    simp only [norm_mul, norm_neg, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hQ] at hm'
    have hheight : 1 + |(m : ℝ)| + |(n : ℝ)| ≤ K * (1 + ‖s‖) := by
      dsimp only [K]
      have := mul_le_mul_of_nonneg_left (show ‖Complex.log z‖ ≤ 1 by linarith)
        (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      nlinarith [norm_nonneg s, mul_nonneg (Nat.cast_nonneg N) (norm_nonneg s),
        mul_nonneg (Nat.cast_nonneg N) hP.le, mul_nonneg (Nat.cast_nonneg N) hQ.le]
    have hsize : |L| ≤ (2 * N * P) * ‖1 - z‖ := by
      have h := congrArg norm hform
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hP,
        Complex.norm_natCast] at h
      calc
        |L| ≤ |L| * ‖U‖ := le_mul_of_one_le_right (abs_nonneg _) hU
        _ = P * N * ‖Complex.log z‖ := h.symm
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ P * N)]
    have hb := hbak m n hL
    change 1 ≤ B * _ * |L| at hb
    apply (inv_le_iff_one_le_mul₀ hdist).mpr
    calc
      1 ≤ B * (1 + |(m : ℝ)| + |(n : ℝ)|) ^ d * |L| := hb
      _ ≤ B * (K * (1 + ‖s‖)) ^ d * ((2 * N * P) * ‖1 - z‖) := by gcongr
      _ = ((B * K ^ d * (2 * N * P)) * (1 + ‖s‖) ^ d) * ‖1 - z‖ := by rw [mul_pow]; ring
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · apply le_trans _ hmajor
    apply (inv_le_iff_one_le_mul₀ hdist).mpr
    linarith [lt_of_not_ge hnear]

/-- If the two residue cardinalities have equal positive powers, the possible
values at the second uniformizer lie among the roots of one fixed binomial.
Consequently its totalized Euler values form a finite set, for arbitrary phases. -/
theorem finite_euler_values_of_residue_pow_eq
    (p q : ℕ) (a b : ℂ) (hb : b ≠ 0) (k l : ℕ) (hk : 0 < k) (hpow : q ^ k = p ^ l) :
    ∃ K : Finset ℂ, ∀ s : ℂ, b * Complex.exp (-(Real.log p : ℂ) * s) = 1 →
      (1 - a * Complex.exp (-(Real.log q : ℂ) * s))⁻¹ ∈ K := by
  classical
  let R := Polynomial.nthRootsFinset k (a ^ k / b ^ l)
  refine ⟨R.image (fun z ↦ (1 - z)⁻¹), fun s hs ↦ Finset.mem_image_of_mem _ ?_⟩
  apply (Polynomial.mem_nthRootsFinset hk _).mpr
  apply (eq_div_iff (pow_ne_zero l hb)).mpr
  have hlog := congrArg (fun x : ℕ ↦ Real.log (x : ℝ)) hpow
  simp only [Nat.cast_pow, Real.log_pow] at hlog
  have he : Complex.exp (-(Real.log q : ℂ) * s) ^ k =
      Complex.exp (-(Real.log p : ℂ) * s) ^ l := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    have hc := congrArg Complex.ofReal hlog
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hc
    linear_combination -s * hc
  rw [mul_pow, he, mul_assoc, mul_comm _ (b ^ l), ← mul_pow, hs, one_pow, mul_one]

end RiemannMasullo
