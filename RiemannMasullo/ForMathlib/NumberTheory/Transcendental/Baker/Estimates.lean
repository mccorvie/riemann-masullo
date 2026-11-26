module

public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.CoreBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Explicit logarithmic estimates for the bound functions of the parametric core

Ported from HOL Light, Baker/estimates.ml (jrh13/hol-light, commit 1a0c0e6).

`M` bounds `n`, the degree product `∏ r ∈ V, d r`, `Lam`, `log (1 / lmin)` and the height sum
`∑ r ∈ Icc 1 n, log ((d r + 1) * H r ^ 3)`; `h` bounds `M`, `log k`, `log G`, `log Bb`, `log Gn`
and `∑ r ∈ V, e r * log ((d r + 1) * H r ^ 3)`. The bound functions of `CoreBounds.lean` are
compared with exponentials of `bakerLu`, `bakerLw` and `bakerL7`, explicit polynomials in the
parameters, so that the numeric layer (`Param.lean`) chooses the parameters by elementary
comparisons. -/

@[expose] public section

namespace RiemannMasullo.Baker

/-! ### The explicit exponents -/

/-- HOL Light: Baker/estimates.ml, baker_lu. The explicit exponent bounding `log (bakerUb …)`. -/
noncomputable def bakerLu (M : ℝ) (L k h N : ℕ) : ℝ :=
  51 * (h : ℝ) * (k : ℝ) + (3 * M + 15) * (L : ℝ) * (h : ℝ) + (M + 4) * (L : ℝ) * (N : ℝ)

/-- HOL Light: Baker/estimates.ml, baker_lw. The explicit exponent of the Liouville bound of
Lemma 5, divided by the common multiple and the denominator power. -/
noncomputable def bakerLw (M : ℝ) (D L k h R : ℕ) : ℝ :=
  ((D : ℝ) + 1) * (k : ℝ) * (h : ℝ) * (19 + Real.log (((R : ℝ) + (h : ℝ)) / (h : ℝ))) +
    (50 * (D : ℝ) + 2) * (h : ℝ) * (k : ℝ) + (D : ℝ) * (3 * M + 12) * (L : ℝ) * (h : ℝ) +
    (D : ℝ) * (M + 9) * (L : ℝ) * (R : ℝ)

/-- HOL Light: Baker/estimates.ml, baker_l7. The explicit exponent of the Liouville bound of
Lemma 7; `lk` stands for an upper bound of `log k`. -/
noncomputable def bakerL7 (M : ℝ) (D n L k h X7 lmax : ℕ) (lk : ℝ) : ℝ :=
  (D : ℝ) * (k : ℝ) ^ n *
    (((n : ℝ) + 1) * (h : ℝ) + (3 * M + 12) * (L : ℝ) * (h : ℝ) + 43 * (h : ℝ) * (k : ℝ) +
      6 * (h : ℝ) * (L : ℝ) * lk + 6 * (L : ℝ) * (X7 : ℝ) +
      (L : ℝ) * (lmax : ℝ) * ((n : ℝ) * (lk + 1) + M))

/-! ### Elementary facts about `log`, products and sums -/

/-- HOL Light: Baker/estimates.ml, LOG_LE_SELF. The logarithm of a positive real is at most the
real. -/
theorem log_le_self (x : ℝ) (hx : 0 < x) : Real.log x ≤ x := by
  have := Real.log_le_sub_one_of_pos hx
  linarith

private theorem estimates_log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

private theorem estimates_log_num_suc_le (k : ℕ) (hk : 1 ≤ k) :
    Real.log ((k : ℝ) + 1) ≤ 1 + Real.log k := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : Real.log ((k : ℝ) + 1) ≤ Real.log (2 * k) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [Real.log_mul (by norm_num) (ne_of_gt (by linarith))] at h1
  linarith [estimates_log_two_le_one]

private theorem estimates_log_pow4 (a b c w : ℝ) (x y z t : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hw : 0 < w) :
    Real.log (a ^ x * b ^ y * c ^ z * w ^ t) =
      (x : ℝ) * Real.log a + (y : ℝ) * Real.log b + (z : ℝ) * Real.log c +
        (t : ℝ) * Real.log w := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow]

private theorem estimates_pow4_ge_one (a b c w : ℝ) (x y z t : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hw : 1 ≤ w) : 1 ≤ a ^ x * b ^ y * c ^ z * w ^ t :=
  one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ ha) (one_le_pow₀ hb)) (one_le_pow₀ hc))
    (one_le_pow₀ hw)

private theorem estimates_prod_pos (s : Finset ℕ) (d : ℕ → ℕ) (hd : ∀ r ∈ s, 1 ≤ d r) :
    1 ≤ ∏ r ∈ s, d r :=
  Nat.succ_le_of_lt (Finset.prod_pos fun r hr => Nat.lt_of_lt_of_le Nat.zero_lt_one (hd r hr))

private theorem estimates_prod_subset_le (V : Finset ℕ) (n : ℕ) (d : ℕ → ℕ)
    (hV : Finset.Icc 1 n ⊆ V) (hd : ∀ r ∈ V, 1 ≤ d r) :
    ∏ r ∈ Finset.Icc 1 n, d r ≤ ∏ r ∈ V, d r := by
  rw [← Finset.prod_sdiff hV]
  exact Nat.le_mul_of_pos_left _
    (estimates_prod_pos _ d fun r hr => hd r (Finset.mem_sdiff.1 hr).1)

/-! ### The common multiple bound `bakerNmax` -/

/-- HOL Light: Baker/estimates.ml, BAKER_NMAX_LOG. The common multiple bound is at least `1` and
its logarithm is `h * (19 + log ((R + h) / h))`. -/
theorem baker_nmax_log (h R : ℕ) (hh : 1 ≤ h) :
    1 ≤ bakerNmax h R ∧
      Real.log (bakerNmax h R) = (h : ℝ) * (19 + Real.log (((R : ℝ) + (h : ℝ)) / (h : ℝ))) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have h1 : 1 ≤ ((R : ℝ) + h) / h := by
    rw [le_div_iff₀ hh0]; linarith
  have h2 : (1 : ℝ) ≤ Real.exp 19 := Real.one_le_exp (by norm_num)
  have h3 : Real.exp 19 * ((R : ℝ) + h) / h = Real.exp 19 * (((R : ℝ) + h) / h) := by ring
  rw [bakerNmax, h3]
  refine ⟨one_le_pow₀ (one_le_mul_of_one_le_of_one_le h2 h1), ?_⟩
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' (ne_of_gt (by linarith)), Real.log_exp]

/-! ### Estimates shared by the bounds -/

private theorem estimates_hnl_le (h L n : ℕ) (M : ℝ) (hh : 1 ≤ h) (hL : 1 ≤ L)
    (hn : (n : ℝ) ≤ M) : (h : ℝ) + ((n + 1 : ℕ) : ℝ) * (L : ℝ) ≤ (M + 2) * (L : ℝ) * (h : ℝ) := by
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  nlinarith [mul_nonneg (sub_nonneg.2 hL') (by linarith : (0 : ℝ) ≤ h),
    mul_nonneg (sub_nonneg.2 hn) (by linarith : (0 : ℝ) ≤ L),
    mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ M) (by linarith : (0 : ℝ) ≤ L))
      (sub_nonneg.2 hh'),
    mul_nonneg (by linarith : (0 : ℝ) ≤ L) (sub_nonneg.2 hh')]

private theorem estimates_log_card_le (h L n : ℕ) (M : ℝ) (hh : 1 ≤ h) (hL : 1 ≤ L)
    (hn : (n : ℝ) ≤ M) :
    1 ≤ ((bakerIndex h L n).card : ℝ) ∧
      Real.log ((bakerIndex h L n).card : ℝ) ≤ (M + 2) * (L : ℝ) * (h : ℝ) := by
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hc : ((bakerIndex h L n).card : ℝ) = (h : ℝ) * ((L : ℝ) + 1) ^ (n + 1) := by
    rw [card_baker_index]; push_cast; ring
  rw [hc]
  constructor
  · exact one_le_mul_of_one_le_of_one_le hh' (one_le_pow₀ (by linarith))
  · rw [Real.log_mul (ne_of_gt (by linarith)) (ne_of_gt (pow_pos (by linarith) _)),
      Real.log_pow]
    have h1 : Real.log (h : ℝ) ≤ h := log_le_self _ (by linarith)
    have h2 : Real.log ((L : ℝ) + 1) ≤ L := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < L + 1 by linarith)
      linarith
    have h3 : ((n + 1 : ℕ) : ℝ) * Real.log ((L : ℝ) + 1) ≤ ((n + 1 : ℕ) : ℝ) * L :=
      mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    linarith [estimates_hnl_le h L n M hh hL hn]

private theorem estimates_log_x_bound (h L k : ℕ) (G : ℝ) (R : ℕ) (hh : 1 ≤ h) (hR : h ≤ R)
    (hL : 1 ≤ L) (hLk : L ≤ k) (hG : 1 ≤ G) (hlG : Real.log G ≤ h) (hlk : Real.log k ≤ h) :
    (((L + 2) * ((R + 1) + h) : ℕ) : ℝ) * Real.log 2 + (k : ℝ) * Real.log ((k : ℝ) + 1) +
      (k : ℝ) * Real.log (2 * (L : ℝ) * G) ≤ 9 * (L : ℝ) * (R : ℝ) + 5 * (h : ℝ) * (k : ℝ) := by
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hR' : (h : ℝ) ≤ R := by exact_mod_cast hR
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLk' : (L : ℝ) ≤ k := by exact_mod_cast hLk
  have hk : 1 ≤ k := hL.trans hLk
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : Real.log ((k : ℝ) + 1) ≤ 1 + h := by linarith [estimates_log_num_suc_le k hk]
  have h2 : Real.log (2 * (L : ℝ) * G) ≤ 1 + 2 * h := by
    rw [Real.log_mul (ne_of_gt (by linarith)) (ne_of_gt (by linarith)),
      Real.log_mul (by norm_num) (ne_of_gt (by linarith))]
    have : Real.log (L : ℝ) ≤ Real.log k := Real.log_le_log (by linarith) hLk'
    linarith [estimates_log_two_le_one]
  have h3 : (((L + 2) * ((R + 1) + h) : ℕ) : ℝ) ≤ 9 * (L : ℝ) * (R : ℝ) := by
    push_cast
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * L - 2)
        (by linarith : (0 : ℝ) ≤ (R : ℝ) + 1 + h),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * (L : ℝ)) (by linarith : (0 : ℝ) ≤ 2 * (R : ℝ) - 1 - h)]
  have h4 : (((L + 2) * ((R + 1) + h) : ℕ) : ℝ) * Real.log 2 ≤
      (((L + 2) * ((R + 1) + h) : ℕ) : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left estimates_log_two_le_one (Nat.cast_nonneg _)
  have h5 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ k)
  have h6 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ k)
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ k) (sub_nonneg.2 hh')]

private theorem estimates_log_2h_le (d : ℕ) (x : ℝ) (hd : 1 ≤ d) (hx : 1 ≤ x) :
    0 ≤ Real.log (2 * x) ∧ Real.log (2 * x) ≤ Real.log (((d + 1 : ℕ) : ℝ) * x ^ 3) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨Real.log_nonneg (by linarith), Real.log_le_log (by linarith) ?_⟩
  push_cast
  have h1 : x ≤ x ^ 3 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x)
      (mul_nonneg (sub_nonneg.2 hx) (by linarith : (0 : ℝ) ≤ x + 1))]
  nlinarith [mul_nonneg (sub_nonneg.2 hd') (by linarith : (0 : ℝ) ≤ x ^ 3)]

private theorem estimates_sum_if_split (V : Finset ℕ) (n c k : ℕ) (e : ℕ → ℕ) (w : ℕ → ℝ)
    (hV : Finset.Icc 1 n ⊆ V) :
    ∑ r ∈ V, (((if r ∈ Finset.Icc 1 n then c else 0) + k * e r : ℕ) : ℝ) * w r =
      (c : ℝ) * ∑ r ∈ Finset.Icc 1 n, w r + (k : ℝ) * ∑ r ∈ V, (e r : ℝ) * w r := by
  have h1 : ∀ r ∈ V, (((if r ∈ Finset.Icc 1 n then c else 0) + k * e r : ℕ) : ℝ) * w r =
      (if r ∈ Finset.Icc 1 n then (c : ℝ) * w r else 0) + (k : ℝ) * ((e r : ℝ) * w r) := by
    intro r _
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_mem,
    Finset.inter_eq_right.2 hV, ← Finset.mul_sum]

private theorem estimates_sum_if_le (V : Finset ℕ) (n c k : ℕ) (e : ℕ → ℕ) (w : ℕ → ℝ) (M : ℝ)
    (h : ℕ) (hV : Finset.Icc 1 n ⊆ V) (hM : ∑ r ∈ Finset.Icc 1 n, w r ≤ M)
    (hh : ∑ r ∈ V, (e r : ℝ) * w r ≤ h) :
    ∑ r ∈ V, (((if r ∈ Finset.Icc 1 n then c else 0) + k * e r : ℕ) : ℝ) * w r ≤
      (c : ℝ) * M + (k : ℝ) * (h : ℝ) := by
  rw [estimates_sum_if_split V n c k e w hV]
  exact add_le_add (mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg c))
    (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg k))

private theorem estimates_log_pi_le (V : Finset ℕ) (n : ℕ) (d : ℕ → ℕ) (H : ℕ → ℝ) (e : ℕ → ℕ)
    (c k : ℕ) (M : ℝ) (h : ℕ) (hV : Finset.Icc 1 n ⊆ V) (hd : ∀ r ∈ V, 1 ≤ d r ∧ 1 ≤ H r)
    (hM : ∑ r ∈ Finset.Icc 1 n, Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤ M)
    (hh : ∑ r ∈ V, (e r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤ h) :
    1 ≤ ∏ r ∈ V, (2 * H r) ^ ((if r ∈ Finset.Icc 1 n then c else 0) + k * e r) ∧
      Real.log (∏ r ∈ V, (2 * H r) ^ ((if r ∈ Finset.Icc 1 n then c else 0) + k * e r)) ≤
        (c : ℝ) * M + (k : ℝ) * (h : ℝ) := by
  constructor
  · refine Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
      (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl ?_
    intro r hr
    exact one_le_pow₀ (by linarith [(hd r hr).2])
  · rw [Real.log_prod fun r hr => ne_of_gt (pow_pos (by linarith [(hd r hr).2]) _)]
    refine le_trans (Finset.sum_le_sum fun r hr => ?_)
      (estimates_sum_if_le V n c k e _ M h hV hM hh)
    rw [Real.log_pow]
    exact mul_le_mul_of_nonneg_left (estimates_log_2h_le (d r) (H r) (hd r hr).1 (hd r hr).2).2
      (Nat.cast_nonneg _)

private theorem estimates_log_kd_le (k d : ℕ) (x lk : ℝ) (hk : 1 ≤ k) (hx : 1 ≤ x)
    (hlk : Real.log k ≤ lk) :
    Real.log (((k * d + 1 : ℕ) : ℝ) * x ^ 3) ≤
      (lk + 1) + Real.log (((d + 1 : ℕ) : ℝ) * x ^ 3) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hx3 : 0 < x ^ 3 := pow_pos (by linarith) 3
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hkd : (0 : ℝ) < ((k * d + 1 : ℕ) : ℝ) := by positivity
  have hd1 : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  have h1 : Real.log (((k * d + 1 : ℕ) : ℝ) * x ^ 3) ≤
      Real.log (((k : ℝ) + 1) * (((d + 1 : ℕ) : ℝ) * x ^ 3)) := by
    apply Real.log_le_log (mul_pos hkd hx3)
    push_cast
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ k + d) hx3.le]
  rw [Real.log_mul (ne_of_gt (by linarith)) (mul_pos hd1 hx3).ne'] at h1
  linarith [estimates_log_num_suc_le k hk]

/-! ### The Siegel height bound `bakerPbound` -/

/-- HOL Light: Baker/estimates.ml, BAKER_PBOUND_LOG_LE. The Siegel bound is at least `1` and its
logarithm is at most `43 h k + (2 M + 10) L h`.

Deviation: HOL's hypothesis `FINITE V` is dropped, `V` being a `Finset`. -/
theorem baker_pbound_log_le (n h L k : ℕ) (V : Finset ℕ) (G : ℝ) (H : ℕ → ℝ) (e d : ℕ → ℕ)
    (M : ℝ) (_ : 1 ≤ n) (hh : 1 ≤ h) (hL : 1 ≤ L) (hLk : L ≤ k) (hV : Finset.Icc 1 n ⊆ V)
    (hd : ∀ r ∈ V, 1 ≤ d r ∧ 1 ≤ H r) (hG : 1 ≤ G) (hnM : (n : ℝ) ≤ M)
    (hM : ∑ r ∈ Finset.Icc 1 n, Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤ M)
    (hlG : Real.log G ≤ h) (hlk : Real.log k ≤ h)
    (hsum : ∑ r ∈ V, (e r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤ h) :
    1 ≤ bakerPbound n h L k V G H e ∧
      Real.log (bakerPbound n h L k V G H e) ≤
        43 * (h : ℝ) * (k : ℝ) + (2 * M + 10) * (L : ℝ) * (h : ℝ) := by
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLk' : (L : ℝ) ≤ k := by exact_mod_cast hLk
  have hk : 1 ≤ k := hL.trans hLk
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2LG : 1 ≤ 2 * (L : ℝ) * G := by nlinarith
  have hxb := estimates_log_x_bound h L k G h hh le_rfl hL hLk hG hlG hlk
  obtain ⟨hC1, hC⟩ := estimates_log_card_le h L n M hh hL hnM
  obtain ⟨hQ1, hQ⟩ := estimates_log_pi_le V n d H e (L * h) k M h hV hd hM hsum
  have he36 : 1 ≤ Real.exp (36 * (h : ℝ)) := Real.one_le_exp (by linarith)
  have hX1 := estimates_pow4_ge_one (Real.exp (36 * (h : ℝ))) 2 ((k : ℝ) + 1) (2 * (L : ℝ) * G)
    k ((L + 2) * ((h + 1) + h)) k k he36 (by norm_num) (by linarith) h2LG
  have hX := estimates_log_pow4 (Real.exp (36 * (h : ℝ))) 2 ((k : ℝ) + 1) (2 * (L : ℝ) * G)
    k ((L + 2) * ((h + 1) + h)) k k (Real.exp_pos _) (by norm_num) (by linarith) (by linarith)
  rw [Real.log_exp] at hX
  rw [bakerPbound]
  have hXQ := one_le_mul_of_one_le_of_one_le hX1 hQ1
  rw [max_eq_right hXQ]
  refine ⟨one_le_mul_of_one_le_of_one_le hC1 hXQ, ?_⟩
  rw [Real.log_mul (ne_of_gt (by linarith)) (ne_of_gt (by linarith)),
    Real.log_mul (ne_of_gt (by linarith)) (ne_of_gt (by linarith)), hX]
  push_cast at hQ hxb ⊢
  nlinarith [mul_le_mul_of_nonneg_right hLk' (by linarith : (0 : ℝ) ≤ h)]

/-! ### The bounds `bakerUb` and `bakerErr` for the auxiliary function -/

/-- HOL Light: Baker/estimates.ml, BAKER_UB_LOG_LE. The logarithm of `bakerUb` is at most
`bakerLu`. -/
theorem baker_ub_log_le (n h L k : ℕ) (P Bb Lam : ℝ) (N : ℕ) (M : ℝ)
    (_ : 1 ≤ n) (hh : 1 ≤ h) (hL : 1 ≤ L) (hLk : L ≤ k) (hP : 1 ≤ P) (hBb : 1 ≤ Bb)
    (hLam : 1 ≤ Lam) (hLamM : Lam ≤ M) (hnM : (n : ℝ) ≤ M) (hMh : M ≤ h)
    (hlk : Real.log k ≤ h) (hlBb : Real.log Bb ≤ h)
    (hlP : Real.log P ≤ 43 * (h : ℝ) * (k : ℝ) + (2 * M + 10) * (L : ℝ) * (h : ℝ)) :
    Real.log (bakerUb n h L k P Bb Lam N) ≤ bakerLu M L k h N := by
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLk' : (L : ℝ) ≤ k := by exact_mod_cast hLk
  have hk' : (1 : ℝ) ≤ k := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlog : Real.log (2 * (k : ℝ) * Bb * Lam) ≤ 1 + 3 * h := by
    rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by linarith)),
      Real.log_mul (ne_of_gt (by linarith)) (ne_of_gt (by linarith)),
      Real.log_mul (by norm_num) (ne_of_gt (by linarith))]
    linarith [estimates_log_two_le_one, log_le_self Lam (by linarith)]
  have h1 : ((2 * k : ℕ) : ℝ) * Real.log (2 * (k : ℝ) * Bb * Lam) ≤
      ((2 * k : ℕ) : ℝ) * (1 + 3 * h) :=
    mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
  have h2 := estimates_hnl_le h L n M hh hL hnM
  have h3 : ((L + 2 : ℕ) : ℝ) * ((N + h : ℕ) : ℝ) ≤ 3 * (L : ℝ) * N + 3 * (L : ℝ) * h := by
    push_cast
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * L - 2) (by linarith : (0 : ℝ) ≤ (N : ℝ) + h)]
  have h4 : (N : ℝ) * (L : ℝ) * (Lam + 1) ≤ (N : ℝ) * (L : ℝ) * (M + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [bakerUb, bakerLu, Real.log_mul (ne_of_gt (by linarith)) (Real.exp_pos _).ne', Real.log_exp]
  push_cast at h1 h2 h3 ⊢
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ k) (sub_nonneg.2 hh')]

/-- HOL Light: Baker/estimates.ml, BAKER_ERR_LE_UB. If `N L d0 ≤ 1` then `bakerErr` is at most
`exp 1 * (N L d0) * bakerUb`. -/
theorem baker_err_le_ub (n h L k : ℕ) (P Bb Lam d0 : ℝ) (N : ℕ) (hP : 0 ≤ P) (hd0 : 0 ≤ d0)
    (hNL : (N : ℝ) * (L : ℝ) * d0 ≤ 1) :
    bakerErr n h L k P Bb Lam d0 N ≤
      Real.exp 1 * ((N : ℝ) * (L : ℝ) * d0) * bakerUb n h L k P Bb Lam N := by
  rw [bakerErr, bakerUb]
  set A : ℝ := (h : ℝ) + ((n + 1 : ℕ) : ℝ) * (L : ℝ) + ((L + 2 : ℕ) : ℝ) * ((N + h : ℕ) : ℝ) +
    ((2 * k : ℕ) : ℝ) * Real.log (2 * (k : ℝ) * Bb * Lam) with hA
  have hE : Real.exp (A + (N : ℝ) * (L : ℝ) * (Lam + 1)) =
      Real.exp (A + (N : ℝ) * (L : ℝ) * Lam) * Real.exp ((N : ℝ) * (L : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hE]
  have h1 : Real.exp ((N : ℝ) * (L : ℝ) * d0) ≤ Real.exp 1 * Real.exp ((N : ℝ) * (L : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have h2 : 0 ≤ P * Real.exp (A + (N : ℝ) * (L : ℝ) * Lam) * ((N : ℝ) * (L : ℝ) * d0) := by
    positivity
  calc P * Real.exp (A + (N : ℝ) * (L : ℝ) * Lam) *
        ((N : ℝ) * (L : ℝ) * d0 * Real.exp ((N : ℝ) * (L : ℝ) * d0))
      = P * Real.exp (A + (N : ℝ) * (L : ℝ) * Lam) * ((N : ℝ) * (L : ℝ) * d0) *
          Real.exp ((N : ℝ) * (L : ℝ) * d0) := by ring
    _ ≤ P * Real.exp (A + (N : ℝ) * (L : ℝ) * Lam) * ((N : ℝ) * (L : ℝ) * d0) *
          (Real.exp 1 * Real.exp ((N : ℝ) * (L : ℝ))) := mul_le_mul_of_nonneg_left h1 h2
    _ = _ := by ring

/-! ### The Liouville bound of Lemma 5 -/

private theorem estimates_exp_ratio_lower (D Y lmin : ℝ) (k : ℕ) (nm Gn W : ℝ) (hl : 0 < lmin)
    (hnm : 0 < nm) (hGn : 0 < Gn)
    (hW : D * Y + (k : ℝ) * Real.log lmin⁻¹ + (k : ℝ) * Real.log nm + (k : ℝ) * Real.log Gn ≤ W) :
    Real.exp (-W) ≤ lmin ^ k * Real.exp (-(D * Y)) / (nm ^ k * Gn ^ k) := by
  rw [Real.log_inv] at hW
  have h1 : lmin ^ k * Real.exp (-(D * Y)) / (nm ^ k * Gn ^ k) =
      Real.exp ((k : ℝ) * Real.log lmin + -(D * Y) -
        ((k : ℝ) * Real.log nm + (k : ℝ) * Real.log Gn)) := by
    rw [Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_nat_mul, Real.exp_log hl, Real.exp_log hnm, Real.exp_log hGn]
  rw [h1]
  apply Real.exp_le_exp.2
  linarith

private theorem estimates_liou5_log_le (n h L k : ℕ) (V : Finset ℕ) (G : ℝ) (H : ℕ → ℝ)
    (e d : ℕ → ℕ) (P : ℝ) (R : ℕ) (M : ℝ)
    (_ : 1 ≤ n) (hh : 1 ≤ h) (hR : h ≤ R) (hL : 1 ≤ L) (hLk : L ≤ k)
    (hV : Finset.Icc 1 n ⊆ V) (hd : ∀ r ∈ V, 1 ≤ d r ∧ 1 ≤ H r) (hG : 1 ≤ G) (hP : 1 ≤ P)
    (hnM : (n : ℝ) ≤ M) (hDM : ((∏ r ∈ V, d r : ℕ) : ℝ) ≤ M)
    (hM : ∑ r ∈ Finset.Icc 1 n, Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤ M)
    (hMh : M ≤ h) (hlG : Real.log G ≤ h) (hlk : Real.log k ≤ h)
    (hsum : ∑ r ∈ V, (e r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤ h)
    (hlP : Real.log P ≤ 43 * (h : ℝ) * (k : ℝ) + (2 * M + 10) * (L : ℝ) * (h : ℝ)) :
    Real.log ((∏ r ∈ V, d r : ℕ) : ℝ) +
        Real.log (((bakerIndex h L n).card : ℝ) * P *
          (bakerNmax h R ^ k * 2 ^ ((L + 2) * ((R + 1) + h)) * ((k : ℝ) + 1) ^ k *
            (2 * (L : ℝ) * G) ^ k)) +
        ∑ r ∈ V, (((if r ∈ Finset.Icc 1 n then L * R else 0) + k * e r : ℕ) : ℝ) *
          Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤
      (k : ℝ) * Real.log (bakerNmax h R) + 50 * (h : ℝ) * (k : ℝ) +
        (3 * M + 12) * (L : ℝ) * (h : ℝ) + (M + 9) * (L : ℝ) * (R : ℝ) := by
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLk' : (L : ℝ) ≤ k := by exact_mod_cast hLk
  have hk' : (1 : ℝ) ≤ k := by linarith
  have hnm1 := (baker_nmax_log h R hh).1
  have h2LG : 1 ≤ 2 * (L : ℝ) * G := by nlinarith
  obtain ⟨hC1, hC⟩ := estimates_log_card_le h L n M hh hL hnM
  have hxb := estimates_log_x_bound h L k G R hh hR hL hLk hG hlG hlk
  have hS := estimates_sum_if_le V n (L * R) k e
    (fun r => Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3)) M h hV hM hsum
  have hD1 : (1 : ℝ) ≤ ((∏ r ∈ V, d r : ℕ) : ℝ) := by
    exact_mod_cast estimates_prod_pos V d fun r hr => (hd r hr).1
  have hlD : Real.log ((∏ r ∈ V, d r : ℕ) : ℝ) ≤ h :=
    le_trans (log_le_self _ (by linarith)) (by linarith)
  have hX1 := estimates_pow4_ge_one (bakerNmax h R) 2 ((k : ℝ) + 1) (2 * (L : ℝ) * G)
    k ((L + 2) * ((R + 1) + h)) k k hnm1 (by norm_num) (by linarith) h2LG
  have hX := estimates_log_pow4 (bakerNmax h R) 2 ((k : ℝ) + 1) (2 * (L : ℝ) * G)
    k ((L + 2) * ((R + 1) + h)) k k (by linarith) (by norm_num) (by linarith) (by linarith)
  rw [Real.log_mul (ne_of_gt (by nlinarith)) (ne_of_gt (by linarith)),
    Real.log_mul (ne_of_gt (by linarith)) (ne_of_gt (by linarith)), hX]
  push_cast at hS hxb hlD ⊢
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ h) (sub_nonneg.2 hk')]

/-- HOL Light: Baker/estimates.ml, BAKER_LIOU5_EXP_LOWER. The Liouville bound of Lemma 5, divided
by `(bakerNmax h R * Gn) ^ k` and multiplied by `lmin ^ k`, is at least `exp (-bakerLw …)`.

Deviation: HOL's hypothesis `FINITE V` is dropped, `V` being a `Finset`. -/
theorem baker_liou5_exp_lower (n h L k : ℕ) (V : Finset ℕ) (G : ℝ) (H : ℕ → ℝ)
    (e d : ℕ → ℕ) (P Gn lmin : ℝ) (R : ℕ) (M : ℝ)
    (_ : 1 ≤ n) (hh : 1 ≤ h) (hR : h ≤ R) (hL : 1 ≤ L) (hLk : L ≤ k)
    (hV : Finset.Icc 1 n ⊆ V) (hd : ∀ r ∈ V, 1 ≤ d r ∧ 1 ≤ H r) (hG : 1 ≤ G) (hP : 1 ≤ P)
    (hGn : 1 ≤ Gn) (hlmin : 0 < lmin) (_ : lmin ≤ 1)
    (hnM : (n : ℝ) ≤ M) (hDM : ((∏ r ∈ V, d r : ℕ) : ℝ) ≤ M)
    (hM : ∑ r ∈ Finset.Icc 1 n, Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤ M)
    (hllmin : Real.log lmin⁻¹ ≤ M) (hMh : M ≤ h)
    (hlG : Real.log G ≤ h) (hlk : Real.log k ≤ h) (hlGn : Real.log Gn ≤ h)
    (hsum : ∑ r ∈ V, (e r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤ h)
    (hlP : Real.log P ≤ 43 * (h : ℝ) * (k : ℝ) + (2 * M + 10) * (L : ℝ) * (h : ℝ)) :
    Real.exp (-(bakerLw M (∏ r ∈ V, d r) L k h R)) ≤
      lmin ^ k * bakerLiou5 n h L k V G H e d P R / (bakerNmax h R ^ k * Gn ^ k) := by
  obtain ⟨hnm1, hnml⟩ := baker_nmax_log h R hh
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hD0 : (0 : ℝ) ≤ ((∏ r ∈ V, d r : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlog := estimates_liou5_log_le n h L k V G H e d P R M ‹_› hh hR hL hLk hV hd hG hP hnM hDM
    hM hMh hlG hlk hsum hlP
  have hDY := mul_le_mul_of_nonneg_left hlog hD0
  have h1 := mul_le_mul_of_nonneg_left (hllmin.trans hMh) hk0
  have h2 := mul_le_mul_of_nonneg_left hlGn hk0
  rw [bakerLiou5]
  apply estimates_exp_ratio_lower _ _ _ _ _ _ _ hlmin (by linarith) (by linarith)
  rw [bakerLw, hnml] at *
  nlinarith

/-! ### The Liouville bound of Lemma 7 -/

private theorem estimates_liou7_log_le (n h L k : ℕ) (d : ℕ → ℕ) (H : ℕ → ℝ) (P : ℝ)
    (X7 lmax : ℕ) (lk : ℝ) (V : Finset ℕ) (M : ℝ)
    (_ : 1 ≤ n) (hh : 1 ≤ h) (hX7 : h ≤ X7) (hL : 1 ≤ L) (hLk : L ≤ k)
    (hV : Finset.Icc 1 n ⊆ V) (hd : ∀ r ∈ V, 1 ≤ d r ∧ 1 ≤ H r) (hP : 1 ≤ P)
    (hnM : (n : ℝ) ≤ M) (hDM : ((∏ r ∈ V, d r : ℕ) : ℝ) ≤ M)
    (hM : ∑ r ∈ Finset.Icc 1 n, Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤ M)
    (hMh : M ≤ h) (hlk : Real.log k ≤ h) (hlk' : Real.log k ≤ lk)
    (hlP : Real.log P ≤ 43 * (h : ℝ) * (k : ℝ) + (2 * M + 10) * (L : ℝ) * (h : ℝ)) :
    Real.log ((∏ r ∈ Finset.Icc 1 n, k * d r : ℕ) : ℝ) +
        Real.log (((bakerIndex h L n).card : ℝ) *
          (P * (k : ℝ) ^ (2 * h * (L + 2)) * 2 ^ ((L + 2) * (X7 + h)))) +
        ∑ r ∈ Finset.Icc 1 n, ((L * lmax : ℕ) : ℝ) *
          Real.log (((k * d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤
      ((n : ℝ) + 1) * (h : ℝ) + (3 * M + 12) * (L : ℝ) * (h : ℝ) + 43 * (h : ℝ) * (k : ℝ) +
        6 * (h : ℝ) * (L : ℝ) * lk + 6 * (L : ℝ) * (X7 : ℝ) +
        (L : ℝ) * (lmax : ℝ) * ((n : ℝ) * (lk + 1) + M) := by
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hX7' : (h : ℝ) ≤ X7 := by exact_mod_cast hX7
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLk' : (L : ℝ) ≤ k := by exact_mod_cast hLk
  have hk : 1 ≤ k := hL.trans hLk
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlk0 : 0 ≤ Real.log k := Real.log_nonneg hk'
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlmax0 : (0 : ℝ) ≤ lmax := Nat.cast_nonneg lmax
  -- the first logarithm
  have hprod : (∏ r ∈ Finset.Icc 1 n, k * d r) = k ^ n * ∏ r ∈ Finset.Icc 1 n, d r := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  have hDn1 : (1 : ℝ) ≤ ((∏ r ∈ Finset.Icc 1 n, d r : ℕ) : ℝ) := by
    exact_mod_cast estimates_prod_pos _ d fun r hr => (hd r (hV hr)).1
  have hDnV : ((∏ r ∈ Finset.Icc 1 n, d r : ℕ) : ℝ) ≤ ((∏ r ∈ V, d r : ℕ) : ℝ) := by
    exact_mod_cast estimates_prod_subset_le V n d hV fun r hr => (hd r hr).1
  have hA : Real.log ((∏ r ∈ Finset.Icc 1 n, k * d r : ℕ) : ℝ) ≤ ((n : ℝ) + 1) * (h : ℝ) := by
    rw [hprod, Nat.cast_mul, Nat.cast_pow,
      Real.log_mul (ne_of_gt (pow_pos (by linarith) _)) (ne_of_gt (by linarith)), Real.log_pow]
    have h1 := mul_le_mul_of_nonneg_left hlk hn0
    have h2 := log_le_self ((∏ r ∈ Finset.Icc 1 n, d r : ℕ) : ℝ) (by linarith)
    linarith
  -- the second logarithm
  obtain ⟨hC1, hC⟩ := estimates_log_card_le h L n M hh hL hnM
  have hkp : (0 : ℝ) < (k : ℝ) ^ (2 * h * (L + 2)) := pow_pos (by linarith) _
  have h2p : (0 : ℝ) < 2 ^ ((L + 2) * (X7 + h)) := by positivity
  have hB : Real.log (((bakerIndex h L n).card : ℝ) *
      (P * (k : ℝ) ^ (2 * h * (L + 2)) * 2 ^ ((L + 2) * (X7 + h)))) =
      Real.log ((bakerIndex h L n).card : ℝ) + Real.log P +
        ((2 * h * (L + 2) : ℕ) : ℝ) * Real.log k +
        (((L + 2) * (X7 + h) : ℕ) : ℝ) * Real.log 2 := by
    rw [Real.log_mul (ne_of_gt (by linarith))
        (ne_of_gt (mul_pos (mul_pos (by linarith) hkp) h2p)),
      Real.log_mul (ne_of_gt (mul_pos (by linarith) hkp)) h2p.ne',
      Real.log_mul (ne_of_gt (by linarith)) hkp.ne', Real.log_pow, Real.log_pow]
    ring
  have hB1 : ((2 * h * (L + 2) : ℕ) : ℝ) * Real.log k ≤ 6 * (h : ℝ) * (L : ℝ) * lk := by
    have h1 : ((2 * h * (L + 2) : ℕ) : ℝ) ≤ 6 * (h : ℝ) * (L : ℝ) := by
      push_cast
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ h) (sub_nonneg.2 hL')]
    calc ((2 * h * (L + 2) : ℕ) : ℝ) * Real.log k
        ≤ ((2 * h * (L + 2) : ℕ) : ℝ) * lk := mul_le_mul_of_nonneg_left hlk' (Nat.cast_nonneg _)
      _ ≤ 6 * (h : ℝ) * (L : ℝ) * lk := mul_le_mul_of_nonneg_right h1 (by linarith)
  have hB2 : (((L + 2) * (X7 + h) : ℕ) : ℝ) * Real.log 2 ≤ 6 * (L : ℝ) * (X7 : ℝ) := by
    have h1 : (((L + 2) * (X7 + h) : ℕ) : ℝ) ≤ 6 * (L : ℝ) * (X7 : ℝ) := by
      push_cast
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * L - 2)
          (by linarith : (0 : ℝ) ≤ (X7 : ℝ) + h),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * (L : ℝ)) (sub_nonneg.2 hX7')]
    calc (((L + 2) * (X7 + h) : ℕ) : ℝ) * Real.log 2
        ≤ (((L + 2) * (X7 + h) : ℕ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left estimates_log_two_le_one (Nat.cast_nonneg _)
      _ ≤ 6 * (L : ℝ) * (X7 : ℝ) := by linarith
  -- the sum
  have hS : ∑ r ∈ Finset.Icc 1 n, ((L * lmax : ℕ) : ℝ) *
      Real.log (((k * d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤
      (L : ℝ) * (lmax : ℝ) * ((n : ℝ) * (lk + 1) + M) := by
    rw [← Finset.mul_sum, Nat.cast_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ∑ r ∈ Finset.Icc 1 n, Real.log (((k * d r + 1 : ℕ) : ℝ) * H r ^ 3)
        ≤ ∑ r ∈ Finset.Icc 1 n, ((lk + 1) + Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3)) :=
          Finset.sum_le_sum fun r hr =>
            estimates_log_kd_le k (d r) (H r) lk hk (hd r (hV hr)).2 hlk'
      _ ≤ (n : ℝ) * (lk + 1) + M := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
            nsmul_eq_mul]
          linarith
  rw [hB]
  linarith

/-- HOL Light: Baker/estimates.ml, BAKER_LIOU7_EXP_LOWER. The Liouville bound of Lemma 7 is at
least `exp (-bakerL7 …)`.

Deviation: HOL's hypothesis `FINITE V` is dropped, `V` being a `Finset`. -/
theorem baker_liou7_exp_lower (n h L k : ℕ) (d : ℕ → ℕ) (H : ℕ → ℝ) (P : ℝ)
    (X7 lmax : ℕ) (lk : ℝ) (V : Finset ℕ) (M : ℝ)
    (_ : 1 ≤ n) (hh : 1 ≤ h) (hX7 : h ≤ X7) (hL : 1 ≤ L) (hLk : L ≤ k)
    (hV : Finset.Icc 1 n ⊆ V) (hd : ∀ r ∈ V, 1 ≤ d r ∧ 1 ≤ H r) (hP : 1 ≤ P)
    (hnM : (n : ℝ) ≤ M) (hDM : ((∏ r ∈ V, d r : ℕ) : ℝ) ≤ M)
    (hM : ∑ r ∈ Finset.Icc 1 n, Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤ M)
    (hMh : M ≤ h) (hlk : Real.log k ≤ h) (hlk' : Real.log k ≤ lk)
    (hlP : Real.log P ≤ 43 * (h : ℝ) * (k : ℝ) + (2 * M + 10) * (L : ℝ) * (h : ℝ)) :
    Real.exp (-(bakerL7 M (∏ r ∈ V, d r) n L k h X7 lmax lk)) ≤
      bakerLiou7 n h L k d H P X7 lmax := by
  have hlog := estimates_liou7_log_le n h L k d H P X7 lmax lk V M ‹_› hh hX7 hL hLk hV hd hP hnM
    hDM hM hMh hlk hlk' hlP
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hL.trans hLk
  have hlk0 : 0 ≤ lk := le_trans (Real.log_nonneg hk') hlk'
  have hM0 : 0 ≤ M := le_trans (Nat.cast_nonneg n) hnM
  rw [bakerLiou7, bakerL7]
  set B : ℝ := ((n : ℝ) + 1) * (h : ℝ) + (3 * M + 12) * (L : ℝ) * (h : ℝ) +
    43 * (h : ℝ) * (k : ℝ) + 6 * (h : ℝ) * (L : ℝ) * lk + 6 * (L : ℝ) * (X7 : ℝ) +
    (L : ℝ) * (lmax : ℝ) * ((n : ℝ) * (lk + 1) + M) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hprod : ((∏ r ∈ Finset.Icc 1 n, k * d r : ℕ) : ℝ) ≤
      ((∏ r ∈ V, d r : ℕ) : ℝ) * (k : ℝ) ^ n := by
    have h1 : (∏ r ∈ Finset.Icc 1 n, k * d r) = (∏ r ∈ Finset.Icc 1 n, d r) * k ^ n := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, mul_comm]
    rw [h1]
    exact_mod_cast Nat.mul_le_mul_right _
      (estimates_prod_subset_le V n d hV fun r hr => (hd r hr).1)
  apply Real.exp_le_exp.2
  apply neg_le_neg
  calc _ ≤ ((∏ r ∈ Finset.Icc 1 n, k * d r : ℕ) : ℝ) * B :=
        mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
    _ ≤ ((∏ r ∈ V, d r : ℕ) : ℝ) * (k : ℝ) ^ n * B := mul_le_mul_of_nonneg_right hprod hB0

end RiemannMasullo.Baker
