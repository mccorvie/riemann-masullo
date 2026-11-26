module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.AbelLimit
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! # The vertical mean square of a finite Dirichlet polynomial -/

@[expose] public noncomputable section

open Classical Complex Filter MeasureTheory Set
open scoped Topology ComplexConjugate

namespace RiemannMasullo

private theorem integer_exp_summable : Summable (fun k : ℤ ↦ Real.exp (-|(k : ℝ)|)) := by
  have h : Summable (fun n : ℕ ↦ Real.exp (-1) ^ n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simp)
  apply Summable.of_nat_of_neg <;> simpa [← Real.exp_nat_mul] using h

private noncomputable def packet (B : ℕ → ℂ) (S : Finset ℕ) (ω : ℕ → ℝ) (u : ℝ) : ℂ :=
  ∑ m ∈ S, B m * Complex.exp ((ω m * u : ℝ) * Complex.I)

/-- Cauchy weighting evaluates the entire quadratic form, with no discarded
cross terms. Frequencies are in angular units. -/
private theorem cauchy_packet_energy (B : ℕ → ℂ) (S : Finset ℕ) (ω : ℕ → ℝ) :
    ((∫ t : ℝ, ‖packet B S ω t‖ ^ 2 * (1+t^2)⁻¹ : ℝ) : ℂ) =
      ∑ m ∈ S, ∑ n ∈ S, (B m * conj (B n)) *
        ((Real.pi * Real.exp (-|ω m - ω n|) : ℝ) : ℂ) := by
  let F (m n : ℕ) (t : ℝ) := (B m * conj (B n)) *
    (Complex.exp (↑((ω m - ω n)*t) * Complex.I) * ((((1+t^2)⁻¹ : ℝ)) : ℂ))
  have hF (m n : ℕ) : Integrable (F m n) := by
    apply Integrable.const_mul
    apply Integrable.mono' integrable_inv_one_add_sq (by fun_prop)
    filter_upwards with t
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    simp [Complex.norm_exp, Complex.mul_re]
  have he (t : ℝ) : (((‖packet B S ω t‖ ^ 2 * (1+t^2)⁻¹ : ℝ)) : ℂ) =
      ∑ m ∈ S, ∑ n ∈ S, F m n t := by
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [packet, map_sum, Finset.sum_mul, map_mul, ← Complex.exp_conj, F]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun n _ ↦ ?_
    simp only [Complex.conj_ofReal, Complex.conj_I]
    rw [show ∀ a b c d e : ℂ, a*b*(c*d)*e=(a*c)*((b*d)*e) from fun _ _ _ _ _ ↦ by ring,
      ← Complex.exp_add]
    push_cast
    ring_nf
  rw [← integral_complex_ofReal, integral_congr_ae (.of_forall he),
    integral_finsetSum S (fun m _ ↦ integrable_finsetSum S fun n _ ↦ hF m n)]
  apply Finset.sum_congr rfl fun m _ ↦ ?_
  rw [integral_finsetSum S (fun n _ ↦ hF m n)]
  apply Finset.sum_congr rfl fun n _ ↦ ?_
  rw [show (∫ t, F m n t) = _ from integral_const_mul _ _, integral_cexp_mul_inv_one_add_sq]

private theorem row_exp_le (S : Finset ℕ) (m : ℕ) :
    (∑ n ∈ S, Real.exp (-|(n : ℝ) - m|)) ≤ ∑' k : ℤ, Real.exp (-|(k : ℝ)|) := by
  let e : ℕ ↪ ℤ := ⟨fun n ↦ (n : ℤ) - (m : ℤ), fun a b h ↦ Int.ofNat_inj.mp (sub_left_inj.mp h)⟩
  let g (k : ℤ) := Real.exp (-|(k : ℝ)|)
  have hz : Summable g := integer_exp_summable
  have h : (∑ j ∈ S.map e, g j) ≤ ∑' j : ℤ, g j :=
    hz.sum_le_tsum _ (fun j _ ↦ (Real.exp_pos _).le)
  rw [Finset.sum_map] at h
  apply le_trans _ h
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro n _
  change Real.exp (-|(n:ℝ)-m|) = Real.exp (-|(((n : ℤ)-(m : ℤ) : ℤ) : ℝ)|)
  push_cast
  rfl

private theorem packet_energy_le (B : ℕ → ℂ) (S : Finset ℕ) (ω : ℕ → ℝ)
    (hω : ∀ m ∈ S, ∀ n ∈ S, |(m:ℝ)-n| ≤ |ω m-ω n|) :
    (∫ t : ℝ, ‖packet B S ω t‖^2 * (1+t^2)⁻¹) ≤
      Real.pi * (∑' k : ℤ, Real.exp (-|(k:ℝ)|)) * ∑ m ∈ S, ‖B m‖^2 := by
  let w (m n : ℕ) := Real.exp (-|(m:ℝ)-n|)
  let D := ∑' k : ℤ, Real.exp (-|(k:ℝ)|)
  have hrow (m : ℕ) : ∑ n ∈ S, w m n ≤ D := by
    simpa only [w, abs_sub_comm (m:ℝ)] using row_exp_le S m
  have hcol (m n : ℕ) : w n m = w m n := by dsimp only [w]; rw [abs_sub_comm]
  let Q := ∑ m ∈ S, ∑ n ∈ S, ‖B m‖^2 * w m n
  have hQ : Q ≤ (∑ m ∈ S, ‖B m‖^2)*D := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun m _ ↦ by rw [← Finset.mul_sum]; gcongr; exact hrow _
  have hboth : (∑ m ∈ S, ∑ n ∈ S, (‖B m‖^2+‖B n‖^2) * w m n) = Q + Q := by
    simp only [add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun n _ ↦ by rw [hcol]
  calc _ ≤ ‖((∫ t : ℝ, ‖packet B S ω t‖ ^ 2 * (1+t^2)⁻¹ : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
       _ ≤ ∑ m ∈ S, ∑ n ∈ S, ‖(B m * conj (B n)) * ((Real.pi * Real.exp (-|ω m-ω n|) : ℝ) : ℂ)‖ := by
            rw [cauchy_packet_energy]
            exact (norm_sum_le ..).trans (Finset.sum_le_sum fun m _ ↦ norm_sum_le ..)
       _ ≤ (Real.pi / 2) * (Q+Q) := by
            rw [← hboth, Finset.mul_sum]
            apply Finset.sum_le_sum fun m hm ↦ ?_
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum fun n hn ↦ ?_
            simp only [norm_mul, norm_conj, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
              Real.norm_of_nonneg (Real.exp_pos _).le]
            have e : Real.exp (-|ω m-ω n|) ≤ w m n := Real.exp_le_exp.mpr (neg_le_neg (hω m hm n hn))
            calc _ ≤ ‖B m‖ * ‖B n‖ * (Real.pi * w m n) := by gcongr
                 _ ≤ _ := by
                   have hnon : 0 ≤ Real.pi * w m n := mul_nonneg Real.pi_pos.le (Real.exp_pos _).le
                   nlinarith [mul_nonneg (sq_nonneg (‖B m‖ - ‖B n‖)) hnon]
       _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hQ Real.pi_pos.le]
private theorem log_distance {X m n : ℕ} (hm : m ∈ Finset.Icc 1 X) (hn : n ∈ Finset.Icc 1 X) :
    |(m:ℝ)-n| ≤ X * |Real.log m - Real.log n| := by
  wlog h : n ≤ m generalizing m n
  · simpa only [abs_sub_comm (m:ℝ), abs_sub_comm (Real.log m)] using this hn hm (le_of_not_ge h)
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hm₀ : 0 < (m:ℝ) := hn₀.trans_le (Nat.cast_le.mpr h)
  have hl := Real.log_le_sub_one_of_pos (div_pos hn₀ hm₀)
  rw [Real.log_div hn₀.ne' hm₀.ne'] at hl
  have hp := sub_nonneg.mpr (Real.log_le_log hn₀ (Nat.cast_le.mpr h))
  rw [abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h)), abs_of_nonneg hp]
  have hb := (le_div_iff₀ hm₀).mp (show 1+(Real.log n-Real.log m) ≤ (n:ℝ)/m by linarith)
  exact le_trans (by nlinarith : (m:ℝ)-n ≤ m*(Real.log m-Real.log n))
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2) hp)

private theorem unweighted_unit_mean (B : ℕ → ℂ) (S : Finset ℕ) (ω : ℕ → ℝ)
    (hω : ∀ m ∈ S, ∀ n ∈ S, |(m:ℝ)-n| ≤ |ω m-ω n|) :
    (∫ t in (0:ℝ)..1, ‖packet B S ω t‖^2) ≤
      (2 * Real.pi * ∑' k : ℤ, Real.exp (-|(k:ℝ)|)) * ∑ m ∈ S, ‖B m‖^2 := by
  let E (t : ℝ) := ‖packet B S ω t‖^2 * (1+t^2)⁻¹
  have hb (t : ℝ) : ‖packet B S ω t‖ ≤ ∑ m ∈ S, ‖B m‖ := by
    apply (norm_sum_le ..).trans
    apply Finset.sum_le_sum fun m _ ↦ ?_
    simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, Real.exp_zero, mul_one, le_rfl]
  have hi : Integrable E := by
    refine (integrable_inv_one_add_sq.const_mul ((∑ m ∈ S, ‖B m‖)^2)).mono' (by dsimp [E, packet]; fun_prop) ?_
    filter_upwards with t
    rw [Real.norm_of_nonneg (show 0 ≤ E t by dsimp [E]; positivity)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb t) _) (by positivity)
  have he (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) : ‖packet B S ω t‖^2 ≤ 2 * E t := by
    have ht' : 1+t^2 ≤ 2 := by nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2)]
    have hpos : 0 < 1+t^2 := by positivity
    have h : (1:ℝ) ≤ 2 / (1+t^2) := (one_le_div hpos).mpr ht'
    have h' := mul_le_mul_of_nonneg_left h (sq_nonneg ‖packet B S ω t‖)
    dsimp [E]
    rw [div_eq_mul_inv] at h'
    linarith
  calc _ = ∫ t in Ioc (0:ℝ) 1, ‖packet B S ω t‖^2 := intervalIntegral.integral_of_le zero_le_one
       _ ≤ ∫ t in Ioc (0:ℝ) 1, 2 * E t := by
         apply setIntegral_mono_on _ (hi.const_mul _).integrableOn measurableSet_Ioc he
         exact (show Continuous (fun t ↦ ‖packet B S ω t‖^2) by dsimp [packet]; fun_prop).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
       _ ≤ ∫ t : ℝ, 2 * E t := setIntegral_le_integral (hi.const_mul _)
          (.of_forall fun t ↦ by dsimp [E]; positivity)
       _ = 2 * ∫ t : ℝ, E t := integral_const_mul _ _
       _ ≤ _ := by linarith [packet_energy_le B S ω hω]

/-- A mean square estimate for arbitrary finite Dirichlet polynomials on an
arbitrary real interval. The loss in the coefficient diagonal is linear in
the length of the largest frequency index, uniformly over complex coefficients. -/
theorem dirichletPolynomial_integral_norm_sq_le :
    ∃ C > (0:ℝ), ∀ (X : ℕ) (_hX : 0 < X) (S : Finset ℕ), S ⊆ Finset.Icc 1 X →
    ∀ (B : ℕ → ℂ) {a b : ℝ}, a ≤ b →
      (∫ t in a..b, ‖∑ m ∈ S, B m * Complex.exp (↑(-Real.log m*t) * Complex.I)‖^2) ≤
        C * max (b-a) (X:ℝ) * ∑ m ∈ S, ‖B m‖^2 := by
  let C := 2 * Real.pi * ∑' k : ℤ, Real.exp (-|(k:ℝ)|)
  have hC : 0 < C := by
    have h := integer_exp_summable.tsum_pos (fun _ ↦ (Real.exp_pos _).le) (0:ℤ) (Real.exp_pos _)
    exact mul_pos (by positivity) h
  refine ⟨C, hC, fun X hX S hS B a b hab ↦ ?_⟩
  let Y : ℝ := max (b-a) X
  have hY : 0 < Y := (Nat.cast_pos.mpr hX).trans_le (le_max_right ..)
  let A (m : ℕ) := B m * Complex.exp (↑(-Real.log m*a) * Complex.I)
  let ω (m : ℕ) := -Real.log m * Y
  let P (t : ℝ) := ‖packet B S (fun m ↦ -Real.log m) t‖^2
  have hP : Continuous P := by dsimp [P,packet]; fun_prop
  have hnorm (m : ℕ) : ‖A m‖ = ‖B m‖ := by
    rw [show A m = _ from rfl, norm_mul, Complex.norm_exp]; simp only [Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, Real.exp_zero, mul_one]
  have hsep (m) (hm : m ∈ S) (n) (hn : n ∈ S) : |(m:ℝ)-n| ≤ |ω m-ω n| := by
    rw [show ω m-ω n = -(Real.log m-Real.log n)*Y by dsimp [ω]; ring, abs_mul, abs_neg, abs_of_pos hY, mul_comm]
    exact (log_distance (hS hm) (hS hn)).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (abs_nonneg _))
  have ht (t : ℝ) : P (Y*t+a) = ‖packet A S ω t‖^2 := by
    apply congrArg (fun z : ℂ ↦ ‖z‖^2)
    apply Finset.sum_congr rfl fun m _ ↦ ?_
    simp only [A,ω,mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  change (∫ t in a..b, P t) ≤ _
  calc _ ≤ ∫ t in a..Y+a, P t := intervalIntegral.integral_mono_interval le_rfl hab
            (by dsimp [Y]; linarith [le_max_left (b-a) (X:ℝ)]) (.of_forall fun _ ↦ sq_nonneg _) (hP.intervalIntegrable ..)
       _ = Y * ∫ t in (0:ℝ)..1, ‖packet A S ω t‖^2 := by
           have h := intervalIntegral.smul_integral_comp_mul_add (f := P) (a := (0:ℝ)) (b := 1) Y a
           simpa only [mul_zero, zero_add, mul_one, smul_eq_mul, ht] using h.symm
       _ ≤ _ := by
           have h := unweighted_unit_mean A S ω hsep
           simp only [hnorm] at h
           exact (mul_le_mul_of_nonneg_left h hY.le).trans_eq (by dsimp only [C,Y]; ring)

end RiemannMasullo
