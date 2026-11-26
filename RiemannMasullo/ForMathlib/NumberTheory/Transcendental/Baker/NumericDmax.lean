module

public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.Param
public import Mathlib.Algebra.Order.Floor.Semiring

/-! # The numeric core for an upper bound of the degree product

Ported from HOL Light, Baker/numeric_dmax.ml (jrh13/hol-light, commit 1a0c0e6).

`baker_core_numeric` is stated for the exact degree product `D = ∏ r ∈ V, d r`. All requirements
on the base `q` are monotone in `D`, so the same conclusion holds for every upper bound `Dm` of
`D`; this is the form used by the core lower bounds of Baker/explicit.ml. -/

@[expose] public section

namespace RiemannMasullo.Baker

/-- HOL Light: Baker/numeric_dmax.ml, BAKER_PARAMS_MONO. The parameters `c`, `J`, `e1` and `k`
are monotone in the degree product. -/
theorem baker_params_mono (n D Dm q : ℕ) (hD : D ≤ Dm) (hq : 1 ≤ q) :
    bakerC D ≤ bakerC Dm ∧ bakerJ n D ≤ bakerJ n Dm ∧ bakerE1 n D ≤ bakerE1 n Dm ∧
      bakerKpar n D q ≤ bakerKpar n Dm q := by
  have hc : bakerC D ≤ bakerC Dm := by rw [bakerC, bakerC]; omega
  have hJ : bakerJ n D ≤ bakerJ n Dm := by
    rw [bakerJ, bakerJ]; exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) 2
  refine ⟨hc, hJ, ?_, ?_⟩
  · rw [bakerE1, bakerE1]
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_right _ hc) hJ) 4
  · rw [bakerKpar, bakerKpar]
    exact Nat.pow_le_pow_right hq (Nat.mul_le_mul_right _ hc)

/-- HOL Light: Baker/numeric_dmax.ml, BAKER_LPAR_MONO. The parameter `L` is monotone in the degree
product. -/
theorem baker_lpar_mono (n D Dm q : ℕ) (hD : D ≤ Dm) (hq : 1 ≤ q) :
    bakerLpar n D q ≤ bakerLpar n Dm q := by
  have hc : bakerC D ≤ bakerC Dm := (baker_params_mono n D Dm q hD hq).1
  rw [bakerLpar, bakerLpar]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hD)
    (Nat.pow_le_pow_right hq (Nat.mul_le_mul_right _ hc))

/-- HOL Light: Baker/numeric_dmax.ml, SMALL_INDEPENDENT_MONO. If there is no relation with
coefficients of size at most `Y`, there is none with coefficients of size at most `X ≤ Y`.

Deviation: the integer-constrained reals `b r` are `ℤ`-valued, as in `baker_core_parametric`. -/
theorem small_independent_mono (n : ℕ) (lg : ℕ → ℂ) (X Y : ℝ) (hXY : X ≤ Y)
    (h : ∀ b : ℕ → ℤ, (∀ r ∈ Finset.Icc 1 n, |(b r : ℝ)| ≤ Y) →
      ∑ r ∈ Finset.Icc 1 n, (b r : ℂ) * lg r = 0 → ∀ r ∈ Finset.Icc 1 n, b r = 0) :
    ∀ b : ℕ → ℤ, (∀ r ∈ Finset.Icc 1 n, |(b r : ℝ)| ≤ X) →
      ∑ r ∈ Finset.Icc 1 n, (b r : ℂ) * lg r = 0 → ∀ r ∈ Finset.Icc 1 n, b r = 0 :=
  fun b hb hs => h b (fun r hr => (hb r hr).trans hXY) hs

/-- HOL Light: Baker/numeric_dmax.ml, BAKER_CORE_NUMERIC_DMAX. The numeric core
`baker_core_numeric` for an upper bound `Dm` of the degree product `∏ r ∈ V, d r`.

Deviation: HOL's hypothesis `FINITE V` is dropped, `V` being a `Finset`; the integer-constrained
reals `a r j` and `b r` are `ℤ`-valued, as in `baker_core_parametric`. -/
theorem baker_core_numeric_dmax (n : ℕ) (lg theta : ℕ → ℂ) (V : Finset ℕ)
    (g : ℕ → (ℕ → ℂ) → ℂ) (e : ℕ → ℕ) (G : ℝ) (a : ℕ → ℕ → ℤ) (d : ℕ → ℕ) (H : ℕ → ℝ)
    (beta : ℕ → ℂ) (Bb Lam d0 lmin Gn M : ℝ) (q h Dm : ℕ)
    (hn : 1 ≤ n) (hG : 1 ≤ G) (hV : Finset.Icc 1 n ⊆ V)
    (htheta : ∀ r ∈ Finset.Icc 1 n, theta r = Complex.exp (lg r))
    (hg : ∀ j, j ≤ n → intpoly V e G (g j))
    (hgn : g n theta ≠ 0) (hGn : ‖g n theta‖ ≤ Gn) (hGn1 : 1 ≤ Gn)
    (hbeta : ∀ j, j < n → beta j * g n theta = -(g j theta))
    (ha : ∀ r ∈ V, 1 ≤ d r ∧ 1 ≤ H r ∧ (∀ j, |(a r j : ℝ)| ≤ H r) ∧ a r (d r) ≠ 0 ∧
      ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * theta r ^ j = 0)
    (hind : ∀ b : ℕ → ℤ, (∀ r ∈ Finset.Icc 1 n, |(b r : ℝ)| ≤ bakerLpar n Dm q) →
      ∑ r ∈ Finset.Icc 1 n, (b r : ℂ) * lg r = 0 → ∀ r ∈ Finset.Icc 1 n, b r = 0)
    (hBb : 1 ≤ Bb) (hbetaB : ∀ j, j < n → ‖beta j‖ ≤ Bb)
    (hLam : 1 ≤ Lam) (hlgLam : ∀ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam)
    (hsumLam : ∑ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam)
    (hlmin : 0 < lmin) (hlmin1 : lmin ≤ 1) (hlglmin : ∀ r ∈ Finset.Icc 1 n, lmin ≤ ‖lg r‖)
    (hnM : (n : ℝ) ≤ M) (hDDm : ∏ r ∈ V, d r ≤ Dm) (hDmM : (Dm : ℝ) ≤ M) (hLamM : Lam ≤ M)
    (hM : ∑ r ∈ Finset.Icc 1 n, Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤ M)
    (hllmin : Real.log lmin⁻¹ ≤ M)
    (hlq : 112 ≤ Real.log q)
    (hq1 : 2176 * M ^ 3 * 2 ^ bakerJ n Dm ≤ (q : ℝ))
    (hq2 : ((bakerC Dm * (n + 1) : ℕ) : ℝ) * (8 * M + 75) * (6 * M) ^ (n + 3) *
      2 ^ (bakerJ n Dm + 1) ≤ (q : ℝ))
    (hh : 1 ≤ h) (hMh : M ≤ h)
    (hlk : Real.log (bakerKpar n Dm q) ≤ h)
    (hlG : Real.log G ≤ h) (hlBb : Real.log Bb ≤ h) (hlGn : Real.log Gn ≤ h)
    (hsum : ∑ r ∈ V, (e r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤ h)
    (hdelta : ‖beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n‖ ≤ d0)
    (hd0 : d0 ≤ Real.exp (-((q : ℝ) ^ (bakerE1 n Dm + 1) * (h : ℝ)))) : False := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM1 : 1 ≤ M := hn'.trans hnM
  have hM0 : 0 ≤ M := by linarith
  have hq16' : (16 : ℝ) ≤ q := by
    have h1 : (1 : ℝ) ≤ M ^ 3 * 2 ^ bakerJ n Dm :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1) (one_le_pow₀ (by norm_num))
    linarith
  have hq16 : 16 ≤ q := by exact_mod_cast hq16'
  have hq1' : 1 ≤ q := by omega
  have hqr : (1 : ℝ) ≤ q := by linarith
  obtain ⟨hc, hJ, he1, hkk⟩ := baker_params_mono n (∏ r ∈ V, d r) Dm q hDDm hq1'
  have hLL : ((bakerLpar n (∏ r ∈ V, d r) q : ℕ) : ℝ) ≤ ((bakerLpar n Dm q : ℕ) : ℝ) := by
    exact_mod_cast baker_lpar_mono n _ Dm q hDDm hq1'
  have hDM : ((∏ r ∈ V, d r : ℕ) : ℝ) ≤ M :=
    le_trans (by exact_mod_cast hDDm) hDmM
  have h2J : (2 : ℝ) ^ bakerJ n (∏ r ∈ V, d r) ≤ 2 ^ bakerJ n Dm :=
    pow_le_pow_right₀ (by norm_num) hJ
  have hq1D : 2176 * M ^ 3 * 2 ^ bakerJ n (∏ r ∈ V, d r) ≤ (q : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left h2J (by positivity)) hq1
  have hq2D : ((bakerC (∏ r ∈ V, d r) * (n + 1) : ℕ) : ℝ) * (8 * M + 75) * (6 * M) ^ (n + 3) *
      2 ^ (bakerJ n (∏ r ∈ V, d r) + 1) ≤ (q : ℝ) := by
    have h1 : ((bakerC (∏ r ∈ V, d r) * (n + 1) : ℕ) : ℝ) ≤ ((bakerC Dm * (n + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right _ hc
    have h2 : (2 : ℝ) ^ (bakerJ n (∏ r ∈ V, d r) + 1) ≤ 2 ^ (bakerJ n Dm + 1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hJ 1)
    exact le_trans (mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1
      (by positivity)) (by positivity)) h2 (by positivity) (by positivity)) hq2
  have hlkD : Real.log (bakerKpar n (∏ r ∈ V, d r) q) ≤ h := by
    have hk0 : 0 < bakerKpar n (∏ r ∈ V, d r) q := by
      rw [bakerKpar]; exact pow_pos (show 0 < q from hq1') _
    exact le_trans (Real.log_le_log (by exact_mod_cast hk0) (by exact_mod_cast hkk)) hlk
  have hd0D : d0 ≤ Real.exp (-((q : ℝ) ^ (bakerE1 n (∏ r ∈ V, d r) + 1) * (h : ℝ))) := by
    refine hd0.trans (Real.exp_le_exp.2 (neg_le_neg ?_))
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hqr (Nat.add_le_add_right he1 1)) (Nat.cast_nonneg h)
  exact baker_core_numeric n lg theta V g e G a d H beta Bb Lam d0 lmin Gn M q h hn hG hV htheta
    hg hgn hGn hGn1 hbeta ha (small_independent_mono n lg _ _ hLL hind) hBb hbetaB hLam hlgLam
    hsumLam hlmin hlmin1 hlglmin hnM hDM hLamM hM hllmin hlq hq1D hq2D hh hMh hlkD hlG hlBb
    hlGn hsum hdelta hd0D

/-- HOL Light: Baker/numeric_dmax.ml, REAL_NUM_CEIL. A nonnegative real has a natural ceiling. -/
theorem real_num_ceil (x : ℝ) (hx : 0 ≤ x) : ∃ n : ℕ, x ≤ n ∧ (n : ℝ) < x + 1 :=
  ⟨⌈x⌉₊, Nat.le_ceil x, Nat.ceil_lt_add_one hx⟩

end RiemannMasullo.Baker
