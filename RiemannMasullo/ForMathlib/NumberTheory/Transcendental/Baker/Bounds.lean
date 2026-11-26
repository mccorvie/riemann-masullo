module

public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.Auxiliary
public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.IntPoly
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Exp-form bounds for the auxiliary function and the Liouville bound

Ported from HOL Light, Baker/bounds.ml (jrh13/hol-light, commit 1a0c0e6), with
`REAL_TWO_POW_LE_EXP` and `REAL_LE_1_MUL` from Baker/lemmas.ml.

`baker_aux_exp_bound` and `baker_approx_exp_bound` restate `baker_aux_bound` and
`baker_aux_alg_approx` with all factors bounded by exponentials. `liouville_exp_lower` bounds the
left-hand side of `intpoly_liouville` below by an exponential, and `liouville_exp_lower_mono`
gives the monotonicity of that exponential in `b`, `nn` and `H`.

Products and sums are bracketed as HOL Light parses them (to the right). -/

@[expose] public section

namespace RiemannMasullo.Baker

/-! ### Elementary bounds -/

/-- HOL Light: Baker/lemmas.ml, REAL_LE_1_MUL. A product of two reals that are at least `1` is at
least `1`. -/
theorem real_le_1_mul (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) : 1 ≤ x * y :=
  one_le_mul_of_one_le_of_one_le hx hy

/-- HOL Light: Baker/lemmas.ml, REAL_TWO_POW_LE_EXP. `2 ^ a ≤ exp a`. -/
theorem real_two_pow_le_exp (a : ℕ) : (2 : ℝ) ^ a ≤ Real.exp (a : ℝ) := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc (2 : ℝ) ^ a ≤ Real.exp 1 ^ a := pow_le_pow_left₀ (by norm_num) h a
    _ = Real.exp (a : ℝ) := by rw [← Real.exp_nat_mul, mul_one]

/-- HOL Light: Baker/bounds.ml, REAL_LE_EXP_SELF. `x ≤ exp x`. -/
theorem real_le_exp_self (x : ℝ) : x ≤ Real.exp x := by
  linarith [Real.add_one_le_exp x]

/-- HOL Light: Baker/bounds.ml, FACT_LE_SELF_EXP. `n ! ≤ n ^ n`. -/
theorem fact_le_self_exp (n : ℕ) : n.factorial ≤ n ^ n :=
  fact_le_pow n n le_rfl

/-- HOL Light: Baker/bounds.ml, PRODUCT_GE_1. A finite product of reals that are at least `1` is
at least `1`.

Deviation: HOL's hypothesis `FINITE s` is dropped, `s` being a `Finset`. -/
theorem product_ge_1 {A : Type*} (f : A → ℝ) (s : Finset A) (hf : ∀ x ∈ s, 1 ≤ f x) :
    1 ≤ ∏ x ∈ s, f x := by
  calc (1 : ℝ) = ∏ _x ∈ s, (1 : ℝ) := by simp
    _ ≤ ∏ x ∈ s, f x := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) hf

/-! ### The factors of the auxiliary bounds -/

/-- HOL Light: Baker/bounds.ml, CARD_BAKER_INDEX_EXP_BOUND. The number of indices of the
auxiliary function is at most `exp h * exp ((n + 1) * L)`. -/
theorem card_baker_index_exp_bound (h L n : ℕ) :
    ((bakerIndex h L n).card : ℝ) ≤ Real.exp (h : ℝ) * Real.exp (((n + 1 : ℕ) : ℝ) * (L : ℝ)) := by
  have hL : ((L : ℝ) + 1) ≤ Real.exp (L : ℝ) := Real.add_one_le_exp _
  have h1 : ((L : ℝ) + 1) * ((L : ℝ) + 1) ^ n ≤ Real.exp (((n + 1 : ℕ) : ℝ) * (L : ℝ)) := by
    rw [Real.exp_nat_mul, pow_succ']
    gcongr
  rw [card_baker_index]
  push_cast
  have h2 := real_le_exp_self (h : ℝ)
  push_cast at h1
  gcongr

/-- HOL Light: Baker/bounds.ml, BAKER_POWERS_EXP_BOUND. -/
private theorem bounds_baker_powers_exp_bound (n L k : ℕ) (beta lg : ℕ → ℂ) (m : ℕ → ℕ)
    (Bb Lam : ℝ) (hn : 1 ≤ n) (hL : 1 ≤ L) (hLk : L ≤ k) (hBb : 1 ≤ Bb) (hLam : 1 ≤ Lam)
    (hbeta : ∀ j, j < n → ‖beta j‖ ≤ Bb) (hlg : ∀ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam)
    (hm : ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ k) :
    ((m 0 : ℝ) + L * ‖beta 0‖) ^ m 0 *
        ∏ r ∈ Finset.Icc 1 (n - 1), (L * ((1 + ‖beta r‖) * ‖lg r‖)) ^ m r ≤
      Real.exp (((2 * k : ℕ) : ℝ) * Real.log (2 * (k * (Bb * Lam)))) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hL.trans hLk
  have hLk' : (L : ℝ) ≤ k := by exact_mod_cast hLk
  have hBL : 1 ≤ Bb * Lam := real_le_1_mul _ _ hBb hLam
  have hBBL : Bb ≤ Bb * Lam := le_mul_of_one_le_right (by linarith) hLam
  have hkBL : (k : ℝ) ≤ k * (Bb * Lam) := le_mul_of_one_le_right (by linarith) hBL
  have hkB : (k : ℝ) * Bb ≤ k * (Bb * Lam) := by gcongr
  have hc1 : 1 ≤ 2 * ((k : ℝ) * (Bb * Lam)) := by linarith
  have hI : Finset.Ico (0 + 1) (n - 1 + 1) = Finset.Icc 1 (n - 1) := by
    ext r
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), hI] at hm
  rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
  have hm0 : (m 0 : ℝ) ≤ k := by exact_mod_cast (Nat.le_add_right _ _).trans hm
  have hA : (m 0 : ℝ) + L * ‖beta 0‖ ≤ 2 * ((k : ℝ) * (Bb * Lam)) := by
    have h1 : (L : ℝ) * ‖beta 0‖ ≤ k * Bb :=
      mul_le_mul hLk' (hbeta 0 (by omega)) (norm_nonneg _) (by linarith)
    linarith
  have hB : ∀ r ∈ Finset.Icc 1 (n - 1),
      (L : ℝ) * ((1 + ‖beta r‖) * ‖lg r‖) ≤ 2 * ((k : ℝ) * (Bb * Lam)) := by
    intro r hr
    have hr' := Finset.mem_Icc.mp hr
    have h1 : ‖beta r‖ ≤ Bb := hbeta r (by omega)
    have h2 : ‖lg r‖ ≤ Lam := hlg r (Finset.mem_Icc.mpr ⟨hr'.1, by omega⟩)
    have h3 : (1 + ‖beta r‖) * ‖lg r‖ ≤ (2 * Bb) * Lam :=
      mul_le_mul (by linarith) h2 (norm_nonneg _) (by linarith)
    calc (L : ℝ) * ((1 + ‖beta r‖) * ‖lg r‖) ≤ k * ((2 * Bb) * Lam) :=
          mul_le_mul hLk' h3 (by positivity) (by linarith)
      _ = 2 * ((k : ℝ) * (Bb * Lam)) := by ring
  calc ((m 0 : ℝ) + L * ‖beta 0‖) ^ m 0 *
        ∏ r ∈ Finset.Icc 1 (n - 1), (L * ((1 + ‖beta r‖) * ‖lg r‖)) ^ m r
      ≤ (2 * ((k : ℝ) * (Bb * Lam))) ^ m 0 *
        ∏ r ∈ Finset.Icc 1 (n - 1), (2 * ((k : ℝ) * (Bb * Lam))) ^ m r := by
        refine mul_le_mul (pow_le_pow_left₀ (by positivity) hA _)
          (Finset.prod_le_prod₀ (fun r _ => by positivity) fun r hr =>
            pow_le_pow_left₀ (by positivity) (hB r hr) _)
          (Finset.prod_nonneg fun r _ => by positivity) (by positivity)
    _ = (2 * ((k : ℝ) * (Bb * Lam))) ^ (m 0 + ∑ r ∈ Finset.Icc 1 (n - 1), m r) := by
        rw [Finset.prod_pow_eq_pow_sum, pow_add]
    _ ≤ (2 * ((k : ℝ) * (Bb * Lam))) ^ (2 * k) := pow_le_pow_right₀ hc1 (by omega)

/-- HOL Light: Baker/bounds.ml, BAKER_AUX_BOUND_POS. -/
private theorem bounds_baker_aux_bound_pos (n h L : ℕ) (beta lg : ℕ → ℂ) (m : ℕ → ℕ) (N : ℕ)
    (P X : ℝ) (hP : 0 ≤ P) :
    0 ≤ ((bakerIndex h L n).card : ℝ) *
      (P * (2 ^ ((L + 2) * (N + h)) *
        (((m 0 : ℝ) + L * ‖beta 0‖) ^ m 0 *
          ((∏ r ∈ Finset.Icc 1 (n - 1), (L * ((1 + ‖beta r‖) * ‖lg r‖)) ^ m r) *
            Real.exp X)))) := by
  have h1 : 0 ≤ ∏ r ∈ Finset.Icc 1 (n - 1), ((L : ℝ) * ((1 + ‖beta r‖) * ‖lg r‖)) ^ m r :=
    Finset.prod_nonneg fun r _ => by positivity
  positivity

/-- HOL Light: Baker/bounds.ml, BAKER_AUX_EXP_COMMON (with BAKER_EXP_BOUND_ARITH). -/
private theorem bounds_baker_aux_exp_common (n h L k : ℕ) (beta lg : ℕ → ℂ) (m : ℕ → ℕ) (N : ℕ)
    (P Bb Lam X Y : ℝ) (hn : 1 ≤ n) (hL : 1 ≤ L) (hLk : L ≤ k) (hBb : 1 ≤ Bb) (hLam : 1 ≤ Lam)
    (hP : 0 ≤ P) (hbeta : ∀ j, j < n → ‖beta j‖ ≤ Bb)
    (hlg : ∀ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam)
    (hm : ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ k) (hXY : X ≤ Y) :
    ((bakerIndex h L n).card : ℝ) *
      (P * (2 ^ ((L + 2) * (N + h)) *
        (((m 0 : ℝ) + L * ‖beta 0‖) ^ m 0 *
          ((∏ r ∈ Finset.Icc 1 (n - 1), (L * ((1 + ‖beta r‖) * ‖lg r‖)) ^ m r) *
            Real.exp X)))) ≤
      P * Real.exp ((h : ℝ) + (((n + 1 : ℕ) : ℝ) * (L : ℝ) +
        (((L + 2 : ℕ) : ℝ) * ((N + h : ℕ) : ℝ) +
          (((2 * k : ℕ) : ℝ) * Real.log (2 * (k * (Bb * Lam))) + Y)))) := by
  have hc := card_baker_index_exp_bound h L n
  have h2 : (2 : ℝ) ^ ((L + 2) * (N + h)) ≤
      Real.exp (((L + 2 : ℕ) : ℝ) * ((N + h : ℕ) : ℝ)) := by
    have := real_two_pow_le_exp ((L + 2) * (N + h))
    rwa [Nat.cast_mul] at this
  have h3 := bounds_baker_powers_exp_bound n L k beta lg m Bb Lam hn hL hLk hBb hLam hbeta hlg hm
  have h4 : Real.exp X ≤ Real.exp Y := Real.exp_le_exp.mpr hXY
  have hpr : 0 ≤ ∏ r ∈ Finset.Icc 1 (n - 1), ((L : ℝ) * ((1 + ‖beta r‖) * ‖lg r‖)) ^ m r :=
    Finset.prod_nonneg fun r _ => by positivity
  have hA : 0 ≤ ((m 0 : ℝ) + L * ‖beta 0‖) ^ m 0 := by positivity
  have h34 : ((m 0 : ℝ) + L * ‖beta 0‖) ^ m 0 *
      (∏ r ∈ Finset.Icc 1 (n - 1), (L * ((1 + ‖beta r‖) * ‖lg r‖)) ^ m r) * Real.exp X ≤
      Real.exp (((2 * k : ℕ) : ℝ) * Real.log (2 * (k * (Bb * Lam)))) * Real.exp Y :=
    mul_le_mul h3 h4 (Real.exp_nonneg _) (Real.exp_nonneg _)
  have h234 : (2 : ℝ) ^ ((L + 2) * (N + h)) * (((m 0 : ℝ) + L * ‖beta 0‖) ^ m 0 *
      (∏ r ∈ Finset.Icc 1 (n - 1), (L * ((1 + ‖beta r‖) * ‖lg r‖)) ^ m r) * Real.exp X) ≤
      Real.exp (((L + 2 : ℕ) : ℝ) * ((N + h : ℕ) : ℝ)) *
        (Real.exp (((2 * k : ℕ) : ℝ) * Real.log (2 * (k * (Bb * Lam)))) * Real.exp Y) :=
    mul_le_mul h2 h34 (mul_nonneg (mul_nonneg hA hpr) (Real.exp_nonneg _)) (Real.exp_nonneg _)
  have hall := mul_le_mul hc h234
    (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hA hpr) (Real.exp_nonneg _)))
    (by positivity)
  have hfin := mul_le_mul_of_nonneg_left hall hP
  rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
  refine le_trans (le_of_eq ?_) (hfin.trans (le_of_eq ?_)) <;> ring

/-! ### Exp-form bounds for the auxiliary function -/

/-- HOL Light: Baker/bounds.ml, BAKER_AUX_EXP_BOUND. The upper bound for the auxiliary function
on the disc `‖z‖ + 1 ≤ N` with every factor bounded by an exponential.

Deviation: the coefficient family `p` is integer-valued, as in `bakerAux` (HOL: real-valued). -/
theorem baker_aux_exp_bound (n h L k : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ)
    (m : ℕ → ℕ) (z : ℂ) (N : ℕ) (P Bb Lam : ℝ)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (hLk : L ≤ k) (hBb : 1 ≤ Bb) (hLam : 1 ≤ Lam) (hP : 0 ≤ P)
    (hp : ∀ x ∈ bakerIndex h L n, |(p x : ℝ)| ≤ P)
    (hbeta : ∀ j, j < n → ‖beta j‖ ≤ Bb)
    (hlg : ∀ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam)
    (hsum : ∑ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam)
    (hlin : ‖beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n‖ ≤ 1)
    (hm : ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ k) (hz : ‖z‖ + 1 ≤ N) :
    ‖bakerAux n h L p beta lg m z‖ ≤
      P * Real.exp ((h : ℝ) + (((n + 1 : ℕ) : ℝ) * (L : ℝ) +
        (((L + 2 : ℕ) : ℝ) * ((N + h : ℕ) : ℝ) +
          (((2 * k : ℕ) : ℝ) * Real.log (2 * (k * (Bb * Lam))) +
            (N : ℝ) * ((L : ℝ) * (Lam + 1)))))) := by
  refine (baker_aux_bound n h L p beta lg m z N P hn hp hz).trans ?_
  refine bounds_baker_aux_exp_common n h L k beta lg m N P Bb Lam _ _ hn hL hLk hBb hLam hP
    hbeta hlg hm ?_
  gcongr

/-- HOL Light: Baker/bounds.ml, BAKER_APPROX_EXP_BOUND. The bound for the difference between the
auxiliary function and `∏ lg r ^ m r` times its algebraic counterpart, with every factor bounded
by an exponential.

Deviation: the coefficient family `p` is integer-valued, as in `bakerAux` (HOL: real-valued). -/
theorem baker_approx_exp_bound (n h L k : ℕ) (p : ℕ × ℕ × (ℕ → ℕ) → ℤ) (beta lg : ℕ → ℂ)
    (m : ℕ → ℕ) (z : ℂ) (N : ℕ) (P Bb Lam d0 : ℝ)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (hLk : L ≤ k) (hBb : 1 ≤ Bb) (hLam : 1 ≤ Lam) (hP : 0 ≤ P)
    (hp : ∀ x ∈ bakerIndex h L n, |(p x : ℝ)| ≤ P)
    (hbeta : ∀ j, j < n → ‖beta j‖ ≤ Bb)
    (hlg : ∀ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam)
    (hsum : ∑ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam) (hd0 : 0 ≤ d0)
    (hlin : ‖beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n‖ ≤ d0)
    (hm : ∑ r ∈ Finset.range (n - 1 + 1), m r ≤ k) (hz : ‖z‖ + 1 ≤ N) :
    ‖bakerAux n h L p beta lg m z -
        (∏ r ∈ Finset.Icc 1 (n - 1), lg r ^ m r) * bakerAlg n h L p beta lg m z‖ ≤
      P * (Real.exp ((h : ℝ) + (((n + 1 : ℕ) : ℝ) * (L : ℝ) +
        (((L + 2 : ℕ) : ℝ) * ((N + h : ℕ) : ℝ) +
          (((2 * k : ℕ) : ℝ) * Real.log (2 * (k * (Bb * Lam))) +
            (N : ℝ) * ((L : ℝ) * Lam))))) *
        ((N : ℝ) * ((L : ℝ) * (d0 * Real.exp ((N : ℝ) * ((L : ℝ) * d0)))))) := by
  refine (baker_aux_alg_approx n h L p beta lg m z N P hn hp hz).trans ?_
  have hX : (N : ℝ) * ((L : ℝ) * ∑ r ∈ Finset.Icc 1 n, ‖lg r‖) ≤ (N : ℝ) * ((L : ℝ) * Lam) := by
    gcongr
  have h2 : (N : ℝ) * ((L : ℝ) *
      (‖beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n‖ * Real.exp ((N : ℝ) *
        ((L : ℝ) * ‖beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n‖)))) ≤
      (N : ℝ) * ((L : ℝ) * (d0 * Real.exp ((N : ℝ) * ((L : ℝ) * d0)))) := by
    gcongr
  have key := mul_le_mul
    (bounds_baker_aux_exp_common n h L k beta lg m N P Bb Lam _ _ hn hL hLk hBb hLam hP
      hbeta hlg hm hX) h2 (by positivity) (by positivity)
  refine (le_of_eq ?_).trans (key.trans (le_of_eq ?_)) <;> ring

/-! ### The Liouville bound in exp form -/

/-- HOL Light: Baker/bounds.ml, LIOUVILLE_PRODUCT_BOUND (with LIOUVILLE_HEIGHT_ARITH). -/
private theorem bounds_liouville_product_bound (v : Finset ℕ) (d : ℕ → ℕ) (H : ℕ → ℝ)
    (nn : ℕ → ℕ) (hH : ∀ r ∈ v, 1 ≤ H r) :
    1 ≤ ∏ r ∈ v, H r ^ nn r ∧
      1 ≤ ∏ r ∈ v, (H r * (1 + (d r : ℝ) * H r)) ^ nn r ∧
      (∏ r ∈ v, H r ^ nn r) * ∏ r ∈ v, (H r * (1 + (d r : ℝ) * H r)) ^ nn r ≤
        ∏ r ∈ v, (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ^ nn r := by
  refine ⟨product_ge_1 _ _ fun r hr => one_le_pow₀ (hH r hr),
    product_ge_1 _ _ fun r hr => one_le_pow₀ ?_, ?_⟩
  · have h1 := hH r hr
    have h2 : (0 : ℝ) ≤ (d r : ℝ) * H r := by positivity
    exact real_le_1_mul _ _ h1 (by linarith)
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun r hr => ?_) fun r hr => ?_
    · have h1 := hH r hr
      have h0 : 0 ≤ H r := by linarith
      positivity
    · have h1 := hH r hr
      have h0 : 0 ≤ H r := by linarith
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      push_cast
      have h3 : 0 ≤ H r * H r * (H r - 1) := mul_nonneg (by positivity) (by linarith)
      nlinarith [h3]

/-- HOL Light: Baker/bounds.ml, LIOUVILLE_EXP_ARITH. -/
private theorem bounds_liouville_exp_arith (D : ℕ) (b Q R W : ℝ) (hD : 1 ≤ D) (hb : 1 ≤ b)
    (hQ : 1 ≤ Q) (hR : 1 ≤ R) (hW : b * (Q * R) ≤ W) :
    0 < (D.factorial : ℝ) * (max 1 (b * (Q * R)) ^ (D - 1) * Q) ∧
      (D.factorial : ℝ) * (max 1 (b * (Q * R)) ^ (D - 1) * Q) ≤ ((D : ℝ) * W) ^ D := by
  have hQR : 1 ≤ Q * R := real_le_1_mul _ _ hQ hR
  have hbQR : 1 ≤ b * (Q * R) := real_le_1_mul _ _ hb hQR
  have hQle : Q ≤ Q * R := le_mul_of_one_le_right (by linarith) hR
  have hQRle : Q * R ≤ b * (Q * R) := le_mul_of_one_le_left (by linarith) hb
  have hQW : Q ≤ W := by linarith
  rw [max_eq_right hbQR]
  have hfac : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
  refine ⟨by positivity, ?_⟩
  have hf : (D.factorial : ℝ) ≤ (D : ℝ) ^ D := by exact_mod_cast fact_le_self_exp D
  have hpow : (b * (Q * R)) ^ (D - 1) ≤ W ^ (D - 1) := pow_le_pow_left₀ (by linarith) hW _
  have hW0 : 0 ≤ W := by linarith
  calc (D.factorial : ℝ) * ((b * (Q * R)) ^ (D - 1) * Q)
      ≤ (D : ℝ) ^ D * (W ^ (D - 1) * W) :=
        mul_le_mul hf (mul_le_mul hpow hQW (by linarith) (by positivity)) (by positivity)
          (by positivity)
    _ = ((D : ℝ) * W) ^ D := by
        rw [← pow_succ, Nat.sub_add_cancel hD, mul_pow]

/-- HOL Light: Baker/bounds.ml, LIOUVILLE_EXP_IDENTITY. -/
private theorem bounds_liouville_exp_identity (v : Finset ℕ) (d : ℕ → ℕ) (H : ℕ → ℝ)
    (nn : ℕ → ℕ) (b : ℝ) (D : ℕ) (hH : ∀ r ∈ v, 1 ≤ H r) (hb : 1 ≤ b) (hD : 1 ≤ D) :
    Real.exp ((D : ℝ) * (Real.log (D : ℝ) + (Real.log b +
        ∑ r ∈ v, (nn r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3)))) =
      ((D : ℝ) * (b * ∏ r ∈ v, (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ^ nn r)) ^ D := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  rw [Real.exp_nat_mul, Real.exp_add, Real.exp_add, Real.exp_log hD0, Real.exp_log (by linarith),
    Real.exp_sum]
  congr 3
  refine Finset.prod_congr rfl fun r hr => ?_
  have h1 := hH r hr
  have h0 : 0 < H r := by linarith
  rw [Real.exp_nat_mul, Real.exp_log (by positivity)]

/-- HOL Light: Baker/bounds.ml, LIOUVILLE_EXP_LOWER. The lower bound of `intpoly_liouville` is at
least `exp (-(D * (log D + log b + ∑ r, nn r * log ((d r + 1) * H r ^ 3))))` with
`D = ∏ r ∈ v, d r`.

Deviation: HOL's hypothesis `FINITE v` is dropped, `v` being a `Finset`. -/
theorem liouville_exp_lower (v : Finset ℕ) (d : ℕ → ℕ) (H : ℕ → ℝ) (nn : ℕ → ℕ) (b : ℝ)
    (hdH : ∀ r ∈ v, 1 ≤ d r ∧ 1 ≤ H r) (hb : 1 ≤ b) :
    Real.exp (-(((∏ r ∈ v, d r : ℕ) : ℝ) *
        (Real.log ((∏ r ∈ v, d r : ℕ) : ℝ) + (Real.log b +
          ∑ r ∈ v, (nn r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3))))) ≤
      (((∏ r ∈ v, d r).factorial : ℝ) *
        (max 1 (b * ((∏ r ∈ v, H r ^ nn r) *
            ∏ r ∈ v, (H r * (1 + (d r : ℝ) * H r)) ^ nn r)) ^ ((∏ r ∈ v, d r) - 1) *
          ∏ r ∈ v, H r ^ nn r))⁻¹ := by
  have hD : 1 ≤ ∏ r ∈ v, d r := Finset.one_le_prod fun r hr => (hdH r hr).1
  have hH : ∀ r ∈ v, 1 ≤ H r := fun r hr => (hdH r hr).2
  obtain ⟨hQ, hR, hQRW⟩ := bounds_liouville_product_bound v d H nn hH
  obtain ⟨hpos, hle⟩ := bounds_liouville_exp_arith (∏ r ∈ v, d r) b _ _
    (b * ∏ r ∈ v, (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ^ nn r) hD hb hQ hR
    (mul_le_mul_of_nonneg_left hQRW (by linarith))
  rw [Real.exp_neg, bounds_liouville_exp_identity v d H nn b _ hH hb hD]
  exact inv_anti₀ hpos hle

/-- HOL Light: Baker/bounds.ml, LIOUVILLE_EXP_LOWER_MONO. The exp-form Liouville bound decreases
when `b`, the degrees `nn` and the heights `H` increase. The hypothesis `_hd` is HOL's and is
not used.

Deviation: HOL's hypothesis `FINITE v` is dropped, `v` being a `Finset`. -/
theorem liouville_exp_lower_mono (v : Finset ℕ) (d : ℕ → ℕ) (H H' : ℕ → ℝ) (nn nn' : ℕ → ℕ)
    (b b' : ℝ) (_hd : ∀ r ∈ v, 1 ≤ d r) (hb : 1 ≤ b) (hbb' : b ≤ b')
    (hnH : ∀ r ∈ v, nn r ≤ nn' r ∧ 1 ≤ H r ∧ H r ≤ H' r) :
    Real.exp (-(((∏ r ∈ v, d r : ℕ) : ℝ) *
        (Real.log ((∏ r ∈ v, d r : ℕ) : ℝ) + (Real.log b' +
          ∑ r ∈ v, (nn' r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * H' r ^ 3))))) ≤
      Real.exp (-(((∏ r ∈ v, d r : ℕ) : ℝ) *
        (Real.log ((∏ r ∈ v, d r : ℕ) : ℝ) + (Real.log b +
          ∑ r ∈ v, (nn r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3))))) := by
  have hlogb : Real.log b ≤ Real.log b' := Real.log_le_log (by linarith) hbb'
  have hs : ∑ r ∈ v, (nn r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤
      ∑ r ∈ v, (nn' r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * H' r ^ 3) := by
    refine Finset.sum_le_sum fun r hr => ?_
    obtain ⟨h1, h2, h3⟩ := hnH r hr
    have h0 : 0 ≤ H r := by linarith
    have hd1 : (1 : ℝ) ≤ ((d r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 (d r)
    have hx : 1 ≤ ((d r + 1 : ℕ) : ℝ) * H r ^ 3 := real_le_1_mul _ _ hd1 (one_le_pow₀ h2)
    have hxx : ((d r + 1 : ℕ) : ℝ) * H r ^ 3 ≤ ((d r + 1 : ℕ) : ℝ) * H' r ^ 3 := by gcongr
    exact mul_le_mul (by exact_mod_cast h1) (Real.log_le_log (by linarith) hxx)
      (Real.log_nonneg hx) (by positivity)
  rw [Real.exp_le_exp, neg_le_neg_iff]
  gcongr

end RiemannMasullo.Baker
