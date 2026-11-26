module

public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.Estimates
public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.ParametricCore
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The numeric layer of the Baker method: explicit parameters

Ported from HOL Light, Baker/param.ml (jrh13/hol-light, commit 1a0c0e6).

Parameters for `baker_core_parametric` and the verification of all its numeric hypotheses. With
`D = ∏ r ∈ V, d r`, `a = 8 D + 8`, `c = a + 2`, a base `q` (natural, huge) and `h` (natural, of
the size of the logarithm of the heights):
`k = q ^ (c (n + 1))`, `L = 2 D q ^ (c n)`, `R K = h q ^ K`, `S K = k / 2 ^ K`,
`rho K = 4 q ^ a R (K + 1)`, `J = c (2 n ^ 2 + 2 n) + 2`, `X7 = h (L + 2) ^ (n + 1)`,
`rhoX = 4 q ^ a R J`, `eps = exp (-(q ^ e1 h))` with `e1 = c (n + 1) + J + 4`.

The main result is `baker_core_numeric`. -/

@[expose] public section

namespace RiemannMasullo.Baker

/-! ### The parameters -/

/-- HOL Light: Baker/param.ml, baker_a. The exponent `a = 8 D + 8` of the radius ratio. -/
def bakerA (D : ℕ) : ℕ := 8 * D + 8

/-- HOL Light: Baker/param.ml, baker_c. The exponent `c = 8 D + 10`. -/
def bakerC (D : ℕ) : ℕ := 8 * D + 10

/-- HOL Light: Baker/param.ml, baker_kpar. The parameter `k = q ^ (c (n + 1))`. -/
def bakerKpar (n D q : ℕ) : ℕ := q ^ (bakerC D * (n + 1))

/-- HOL Light: Baker/param.ml, baker_Lpar. The parameter `L = 2 D q ^ (c n)`. -/
def bakerLpar (n D q : ℕ) : ℕ := 2 * D * q ^ (bakerC D * n)

/-- HOL Light: Baker/param.ml, baker_J. The number `J = c (2 n n + 2 n) + 2` of extrapolation
steps. -/
def bakerJ (n D : ℕ) : ℕ := bakerC D * (2 * n * n + 2 * n) + 2

/-- HOL Light: Baker/param.ml, baker_e1. The exponent `e1 = c (n + 1) + J + 4` of `eps`. -/
def bakerE1 (n D : ℕ) : ℕ := bakerC D * (n + 1) + bakerJ n D + 4

/-! ### Elementary facts about the parameters and powers of `q` -/

/-- HOL Light: Baker/param.ml, BAKER_C_EQ. `c = a + 2`. -/
theorem baker_c_eq (D : ℕ) : bakerC D = bakerA D + 2 := by
  rw [bakerC, bakerA]

private theorem param_log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

private theorem param_pow_count_le (K : ℕ) : ((K : ℝ) + 2) * 2 ^ K ≤ 2 * 4 ^ K := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    have h1 : (2 : ℝ) ^ K ≤ 4 ^ K := pow_le_pow_left₀ (by norm_num) (by norm_num) K
    have h2 : (0 : ℝ) < 2 ^ K := by positivity
    push_cast
    rw [pow_succ, pow_succ]
    linarith

private theorem param_div_suc_le (k m : ℕ) (hm : m ≠ 0) :
    (k : ℝ) / (m : ℝ) ≤ ((k / m + 1 : ℕ) : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  rw [div_le_iff₀ hm']
  have h1 := Nat.lt_div_mul_add (a := k) (Nat.pos_of_ne_zero hm)
  have h2 : k ≤ (k / m + 1) * m := by rw [Nat.add_mul, Nat.one_mul]; omega
  exact_mod_cast h2

private theorem param_log_pow_add1_le (q K : ℕ) (hq : 1 ≤ q) :
    Real.log ((q : ℝ) ^ (K + 1) + 1) ≤ 1 + ((K : ℝ) + 1) * Real.log q := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (1 : ℝ) ≤ (q : ℝ) ^ (K + 1) := one_le_pow₀ hq'
  have h2 : Real.log ((q : ℝ) ^ (K + 1) + 1) ≤ Real.log (2 * (q : ℝ) ^ (K + 1)) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [Real.log_mul (by norm_num) (ne_of_gt (by linarith)), Real.log_pow] at h2
  push_cast at h2
  linarith [param_log_two_le_one]

/-- HOL Light: Baker/param.ml, BAKER_KPAR_REAL. `k = q ^ (c n) * q ^ a * q ^ 2` as a real. -/
theorem baker_kpar_real (n D q : ℕ) :
    (bakerKpar n D q : ℝ) = (q : ℝ) ^ (bakerC D * n) * (q : ℝ) ^ bakerA D * (q : ℝ) ^ 2 := by
  rw [bakerKpar, baker_c_eq]
  push_cast
  ring

/-- HOL Light: Baker/param.ml, BAKER_LPAR_REAL. `L = 2 D q ^ (c n)` as a real. -/
theorem baker_lpar_real (n D q : ℕ) :
    (bakerLpar n D q : ℝ) = 2 * (D : ℝ) * (q : ℝ) ^ (bakerC D * n) := by
  rw [bakerLpar]
  push_cast
  ring

/-- HOL Light: Baker/param.ml, BAKER_PAR_POS. The parameters `L` and `k` are positive. -/
theorem baker_par_pos (n D q : ℕ) (hD : 1 ≤ D) (hq : 1 ≤ q) :
    1 ≤ bakerLpar n D q ∧ 1 ≤ bakerKpar n D q := by
  have hq0 : 0 < q := hq
  constructor
  · rw [bakerLpar]; exact Nat.mul_pos (Nat.mul_pos (by norm_num) hD) (pow_pos hq0 _)
  · rw [bakerKpar]; exact pow_pos hq0 _

/-- HOL Light: Baker/param.ml, BAKER_C_POS. `1 ≤ c`. -/
theorem baker_c_pos (D : ℕ) : 1 ≤ bakerC D := by
  rw [bakerC]; omega

/-! ### The extrapolation step (Lemma 6) -/

private theorem param_step_core (M Dr hr Q A B QK T l lg Kr : ℝ) (hD1 : 1 ≤ Dr) (hDM : Dr ≤ M)
    (hh : 1 ≤ hr) (hQ : 4 ≤ Q) (hA : 1 ≤ A) (hB : 1 ≤ B) (hQK : 1 ≤ QK) (hT : 0 < T)
    (hl : 112 ≤ l) (hTQ : T ≤ QK) (hKr : (Kr + 2) * T ≤ 2 * QK) (hlg : lg ≤ 1 + (Kr + 1) * l)
    (hbig : 2176 * M ^ 3 * T ≤ Q) :
    51 * hr * (B * A * Q ^ 2) + (3 * M + 15) * (2 * Dr * B) * hr +
          (M + 4) * (2 * Dr * B) * (4 * A * hr * Q * QK + 1) +
        ((Dr + 1) * (B * A * Q ^ 2) * hr * (19 + lg) + (50 * Dr + 2) * hr * (B * A * Q ^ 2) +
          Dr * (3 * M + 12) * (2 * Dr * B) * hr +
          Dr * (M + 9) * (2 * Dr * B) * (hr * Q * QK)) + 3 ≤
      hr * QK * (B * A * Q ^ 2 / (2 * T)) * (8 * (Dr + 1)) * l := by
  have hM1 : 1 ≤ M := hD1.trans hDM
  have hD0 : 0 < Dr := by linarith
  have hM0 : 0 < M := by linarith
  have hh0 : 0 < hr := by linarith
  have hQ0 : 0 < Q := by linarith
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hQK0 : 0 < QK := by linarith
  have hl0 : 0 < l := by linarith
  have hT' : T ≠ 0 := hT.ne'
  obtain ⟨k, hk⟩ : ∃ k, k = B * A * Q ^ 2 := ⟨_, rfl⟩
  rw [← hk]
  have hk1 : 1 ≤ k := by
    rw [hk]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hB hA)
      (one_le_pow₀ (by linarith))
  have hk0 : 0 < k := by linarith
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = hr * QK * (k / (2 * T)) * (8 * (Dr + 1)) * l := ⟨_, rfl⟩
  rw [← hZ]
  have c1 : (Dr + 1) * k * hr * (19 + lg) ≤ Z / 2 := by
    have h1 : 19 + lg ≤ (Kr + 2) * l := by linarith
    have h2 : Kr + 2 ≤ 2 * QK / T := by rw [le_div_iff₀ hT]; exact hKr
    have h3 : (Kr + 2) * l ≤ 2 * QK / T * l := mul_le_mul_of_nonneg_right h2 hl0.le
    have h4 : (Dr + 1) * k * hr * (19 + lg) ≤ (Dr + 1) * k * hr * (2 * QK / T * l) :=
      mul_le_mul_of_nonneg_left (h1.trans h3) (by positivity)
    have h5 : (Dr + 1) * k * hr * (2 * QK / T * l) = Z / 2 := by
      rw [hZ]; field_simp; ring
    linarith
  have c2 : 51 * hr * k + (50 * Dr + 2) * hr * k + 3 ≤ Z / 8 := by
    have h1 : 1 / 2 ≤ QK / (2 * T) := by rw [le_div_iff₀ (by linarith)]; linarith
    have h2 : 56 ≤ l * (QK / (2 * T)) := by
      linarith [mul_nonneg (sub_nonneg.2 hl) (sub_nonneg.2 h1)]
    have h3 : 1 ≤ hr * k := one_le_mul_of_one_le_of_one_le hh hk1
    have h4 : (Dr + 1) * (hr * k) * 56 ≤ (Dr + 1) * (hr * k) * (l * (QK / (2 * T))) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : (Dr + 1) * (hr * k) * (l * (QK / (2 * T))) = Z / 8 := by
      rw [hZ]; field_simp
    linarith [mul_nonneg hD0.le (by linarith : (0 : ℝ) ≤ hr * k)]
  have c3 : (3 * M + 15) * (2 * Dr * B) * hr +
      (M + 4) * (2 * Dr * B) * (4 * A * hr * Q * QK + 1) +
      Dr * (3 * M + 12) * (2 * Dr * B) * hr +
      Dr * (M + 9) * (2 * Dr * B) * (hr * Q * QK) ≤ Z / 8 := by
    obtain ⟨U, hU⟩ : ∃ U, U = hr * A * Q * QK := ⟨_, rfl⟩
    have hQQK : 1 ≤ Q * QK := one_le_mul_of_one_le_of_one_le (by linarith) hQK
    have hU1 : 1 ≤ U := by
      have h1 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hh hA) hQQK
      rw [hU]; linarith
    have hhU : hr ≤ U := by
      have h1 := mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hA hQQK) hh0.le
      rw [hU]; linarith
    have hRU : hr * Q * QK ≤ U := by
      have h1 := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ hr * Q * QK)
      rw [hU]; linarith
    have hNU : 4 * A * hr * Q * QK + 1 ≤ 5 * U := by
      rw [hU] at hU1 ⊢; linarith
    have hDB0 : 0 ≤ 2 * Dr * B := by positivity
    have hU0 : 0 < U := by linarith
    obtain ⟨Y, hY⟩ : ∃ Y, Y = 2 * Dr * B * U := ⟨_, rfl⟩
    have y1 : 2 * Dr * B * hr ≤ Y := by rw [hY]; exact mul_le_mul_of_nonneg_left hhU hDB0
    have y2 : 2 * Dr * B * (4 * A * hr * Q * QK + 1) ≤ 5 * Y := by
      have h1 := mul_le_mul_of_nonneg_left hNU hDB0
      rw [hY]; linarith
    have y3 : 2 * Dr * B * (hr * Q * QK) ≤ Y := by
      rw [hY]; exact mul_le_mul_of_nonneg_left hRU hDB0
    have hY0 : 0 ≤ Y := by rw [hY]; positivity
    have s1 := mul_le_mul_of_nonneg_left y1 (by linarith : (0 : ℝ) ≤ 3 * M + 15)
    have s2 := mul_le_mul_of_nonneg_left y2 (by linarith : (0 : ℝ) ≤ M + 4)
    have s3 := mul_le_mul_of_nonneg_left y1 (by positivity : (0 : ℝ) ≤ Dr * (3 * M + 12))
    have s4 := mul_le_mul_of_nonneg_left y3 (by positivity : (0 : ℝ) ≤ Dr * (M + 9))
    have s5 : 8 * M + 35 + Dr * (4 * M + 21) ≤ 68 * M ^ 2 := by
      linarith [mul_le_mul_of_nonneg_right hDM (by linarith : (0 : ℝ) ≤ 4 * M + 21),
        mul_nonneg (sub_nonneg.2 hM1) hM0.le,
        mul_nonneg (sub_nonneg.2 hM1) (by linarith : (0 : ℝ) ≤ M + 1)]
    have s6 := mul_le_mul_of_nonneg_right s5 hY0
    have s7 : 272 * (M ^ 2 * T) * Dr ≤ Q := by
      have h1 : M ^ 2 * T * Dr ≤ M ^ 2 * T * M := mul_le_mul_of_nonneg_left hDM (by positivity)
      linarith [mul_nonneg (pow_nonneg hM0.le 3) hT.le]
    have s8 : 272 * (M ^ 2 * T) * Dr * Q ≤ (Dr + 1) * l * (Q * Q) := by
      have h1 := mul_le_mul_of_nonneg_right s7 hQ0.le
      have h2 : 1 ≤ (Dr + 1) * l := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
      have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ Q * Q)
      linarith
    have s9 : 68 * M ^ 2 * Y ≤ Z / 8 := by
      have e1 : 68 * M ^ 2 * Y = hr * B * A * QK * (136 * M ^ 2 * Dr * Q) := by
        rw [hY, hU]; ring
      have e2 : Z / 8 = hr * B * A * QK * ((Dr + 1) * (Q * Q) * l / (2 * T)) := by
        rw [hZ, hk]; field_simp
      rw [e1, e2]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [le_div_iff₀ (by linarith)]
      linarith
    linarith
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  linarith

/-- HOL Light: Baker/param.ml, BAKER_STEP_NUM. At the extrapolation step `K` the exponents
`bakerLu` and `bakerLw` are small against `R K * (S (K + 1) + 1) * a * log q`. -/
theorem baker_step_num (M : ℝ) (D n q h K : ℕ) (_ : 1 ≤ n) (hD : 1 ≤ D) (hDM : (D : ℝ) ≤ M)
    (hh : 1 ≤ h) (hq : 4 ≤ q) (hlq : 112 ≤ Real.log q)
    (hbig : 2176 * M ^ 3 * 2 ^ K ≤ (q : ℝ)) :
    bakerLu M (bakerLpar n D q) (bakerKpar n D q) h (4 * q ^ bakerA D * (h * q ^ (K + 1)) + 1) +
        bakerLw M D (bakerLpar n D q) (bakerKpar n D q) h (h * q ^ (K + 1)) + 3 ≤
      ((h * q ^ K : ℕ) : ℝ) * ((bakerKpar n D q / 2 ^ (K + 1) + 1 : ℕ) : ℝ) * (bakerA D : ℝ) *
        Real.log q := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hq' : (4 : ℝ) ≤ q := by exact_mod_cast hq
  have hA : (1 : ℝ) ≤ (q : ℝ) ^ bakerA D := one_le_pow₀ (by linarith)
  have hB : (1 : ℝ) ≤ (q : ℝ) ^ (bakerC D * n) := one_le_pow₀ (by linarith)
  have hQK : (1 : ℝ) ≤ (q : ℝ) ^ K := one_le_pow₀ (by linarith)
  have hT : (0 : ℝ) < 2 ^ K := by positivity
  have hTQ : (2 : ℝ) ^ K ≤ (q : ℝ) ^ K := pow_le_pow_left₀ (by norm_num) (by linarith) K
  have hKr : ((K : ℝ) + 2) * 2 ^ K ≤ 2 * (q : ℝ) ^ K := by
    have h1 := param_pow_count_le K
    have h4 : (4 : ℝ) ^ K ≤ (q : ℝ) ^ K := pow_le_pow_left₀ (by norm_num) hq' K
    linarith
  have hh0 : (h : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hRh : (((h * q ^ (K + 1) : ℕ) : ℝ) + (h : ℝ)) / (h : ℝ) = (q : ℝ) ^ (K + 1) + 1 := by
    push_cast; field_simp
  have hlg := param_log_pow_add1_le q K (by omega)
  have core := param_step_core M D h q ((q : ℝ) ^ bakerA D) ((q : ℝ) ^ (bakerC D * n))
    ((q : ℝ) ^ K) (2 ^ K) (Real.log q) (Real.log ((q : ℝ) ^ (K + 1) + 1)) K hD' hDM hh' hq' hA hB
    hQK hT hlq hTQ hKr hlg hbig
  have hk := baker_kpar_real n D q
  have hL := baker_lpar_real n D q
  have ha : (bakerA D : ℝ) = 8 * ((D : ℝ) + 1) := by rw [bakerA]; push_cast; ring
  have hs := param_div_suc_le (bakerKpar n D q) (2 ^ (K + 1)) (by positivity)
  have hZ : (h : ℝ) * (q : ℝ) ^ K *
        ((q : ℝ) ^ (bakerC D * n) * (q : ℝ) ^ bakerA D * (q : ℝ) ^ 2 / (2 * 2 ^ K)) *
        (8 * ((D : ℝ) + 1)) * Real.log q ≤
      ((h * q ^ K : ℕ) : ℝ) * ((bakerKpar n D q / 2 ^ (K + 1) + 1 : ℕ) : ℝ) * (bakerA D : ℝ) *
        Real.log q := by
    have h1 : ((bakerKpar n D q : ℕ) : ℝ) / (2 * 2 ^ K) ≤
        ((bakerKpar n D q / 2 ^ (K + 1) + 1 : ℕ) : ℝ) := by
      have h2 : (2 : ℝ) * 2 ^ K = ((2 ^ (K + 1) : ℕ) : ℝ) := by push_cast; ring
      rw [h2]; exact hs
    rw [ha, ← hk, show ((h * q ^ K : ℕ) : ℝ) = (h : ℝ) * (q : ℝ) ^ K by push_cast; ring]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)) (by linarith)
  refine le_trans (le_of_eq_of_le ?_ core) hZ
  rw [bakerLu, bakerLw, hk, hL, hRh]
  push_cast
  ring

/-! ### Lemma 7: the exponent `bakerL7` against the extrapolation exponent at the last step -/

private theorem param_l7_core (M Dr nr hr Lr kr X lm lk P3 Ln1 kn : ℝ)
    (hD : 1 ≤ Dr) (hDM : Dr ≤ M) (hn0 : 0 ≤ nr) (hnM : nr ≤ M) (hh : 1 ≤ hr) (hL : 1 ≤ Lr)
    (hk : 1 ≤ kr) (hkL : kr ≤ Lr * Ln1) (hlk : 1 ≤ lk) (hP3 : 1 ≤ P3) (hLn1 : 1 ≤ Ln1)
    (hkn : 1 ≤ kn) (_ : 0 ≤ X) (_ : 0 ≤ lm)
    (hX : X ≤ hr * P3 * Ln1) (hlm : lm ≤ hr * P3 * Ln1) :
    Dr * kn * ((nr + 1) * hr + (3 * M + 12) * Lr * hr + 43 * hr * kr + 6 * hr * Lr * lk +
          6 * Lr * X + Lr * lm * (nr * (lk + 1) + M)) + 6 * hr * Lr * lk + 2 ≤
      (8 * M + 75) * Dr * kn * P3 * hr * (Lr * Ln1) * lk := by
  have hM1 : 1 ≤ M := hD.trans hDM
  have hM0 : 0 < M := by linarith
  have hD0 : 0 < Dr := by linarith
  have hh0 : 0 < hr := by linarith
  have hL0 : 0 < Lr := by linarith
  have hk0 : 0 < kr := by linarith
  have hlk0 : 0 < lk := by linarith
  have hP30 : 0 < P3 := by linarith
  have hLn10 : 0 < Ln1 := by linarith
  have hkn0 : 0 < kn := by linarith
  obtain ⟨Ln2, hLn2⟩ : ∃ Ln2, Ln2 = Lr * Ln1 := ⟨_, rfl⟩
  rw [← hLn2] at hkL ⊢
  have hLL : Lr ≤ Ln2 := by rw [hLn2]; exact le_mul_of_one_le_right hL0.le hLn1
  have hLn20 : 0 < Ln2 := by linarith
  obtain ⟨G, hG⟩ : ∃ G, G = hr * Ln2 * lk * P3 := ⟨_, rfl⟩
  have hlkP : 1 ≤ lk * P3 := one_le_mul_of_one_le_of_one_le hlk hP3
  have g0 : hr * Ln2 ≤ G := by
    rw [hG]; linarith [mul_le_mul_of_nonneg_left hlkP (by positivity : 0 ≤ hr * Ln2)]
  have g1 : hr ≤ G := by
    linarith [mul_le_mul_of_nonneg_left (hL.trans hLL) hh0.le]
  have g2 : Lr * hr ≤ G := by
    linarith [mul_le_mul_of_nonneg_left hLL hh0.le]
  have g3 : hr * kr ≤ G := by
    linarith [mul_le_mul_of_nonneg_left hkL hh0.le]
  have g4 : hr * Lr * lk ≤ G := by
    rw [hG]
    linarith [mul_le_mul_of_nonneg_left hLL (by positivity : 0 ≤ hr * lk),
      mul_le_mul_of_nonneg_left hP3 (by positivity : 0 ≤ hr * Ln2 * lk)]
  have g5 : hr * P3 * Ln2 ≤ G := by
    rw [hG]; linarith [mul_le_mul_of_nonneg_left hlk (by positivity : 0 ≤ hr * P3 * Ln2)]
  have g6 : Lr * X ≤ hr * P3 * Ln2 := by
    rw [hLn2]; linarith [mul_le_mul_of_nonneg_left hX hL0.le]
  have g7 : Lr * lm ≤ hr * P3 * Ln2 := by
    rw [hLn2]; linarith [mul_le_mul_of_nonneg_left hlm hL0.le]
  have g8 : nr * (lk + 1) + M ≤ 3 * M * lk := by
    linarith [mul_le_mul_of_nonneg_right hnM hlk0.le, mul_le_mul_of_nonneg_left hlk hM0.le]
  have g9 : Lr * lm * (nr * (lk + 1) + M) ≤ 3 * M * G := by
    have h1 := mul_le_mul g7 g8 (by positivity) (by positivity)
    rw [hG]; linarith
  have hG0 : 0 ≤ G := by linarith
  have b1 : (nr + 1) * hr ≤ 2 * M * G := mul_le_mul (by linarith) g1 hh0.le (by linarith)
  have b2 := mul_le_mul_of_nonneg_left g2 (by linarith : (0 : ℝ) ≤ 3 * M + 12)
  have hB : (nr + 1) * hr + (3 * M + 12) * Lr * hr + 43 * hr * kr + 6 * hr * Lr * lk +
      6 * Lr * X + Lr * lm * (nr * (lk + 1) + M) ≤ (8 * M + 67) * G := by
    linarith
  have h1 := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ Dr * kn)
  have hDk : 1 ≤ Dr * kn := one_le_mul_of_one_le_of_one_le hD hkn
  have h2 := mul_le_mul_of_nonneg_right hDk (by linarith : (0 : ℝ) ≤ 8 * G)
  subst hG
  linarith

/-- HOL Light: Baker/param.ml, BAKER_L7_BOUND. A crude bound for the exponent `bakerL7`. -/
theorem baker_l7_bound (M : ℝ) (D n L k h X7 lmax : ℕ) (lk : ℝ) (_ : 1 ≤ n) (hD : 1 ≤ D)
    (hDM : (D : ℝ) ≤ M) (hnM : (n : ℝ) ≤ M) (hh : 1 ≤ h) (hL : 1 ≤ L) (hk : 1 ≤ k)
    (hkL : (k : ℝ) ≤ (L : ℝ) ^ (n + 2)) (hlk : 1 ≤ lk)
    (hX7 : (X7 : ℝ) ≤ (h : ℝ) * 3 ^ (n + 1) * (L : ℝ) ^ (n + 1))
    (hlmax : (lmax : ℝ) ≤ (h : ℝ) * 3 ^ (n + 1) * (L : ℝ) ^ (n + 1)) :
    bakerL7 M D n L k h X7 lmax lk + 6 * (h : ℝ) * (L : ℝ) * lk + 2 ≤
      (8 * M + 75) * (D : ℝ) * (k : ℝ) ^ n * 3 ^ (n + 1) * (h : ℝ) * (L : ℝ) ^ (n + 2) * lk := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkL' : (k : ℝ) ≤ (L : ℝ) * (L : ℝ) ^ (n + 1) := by rw [← pow_succ']; exact hkL
  have core := param_l7_core M D n h L k X7 lmax lk (3 ^ (n + 1)) ((L : ℝ) ^ (n + 1))
    ((k : ℝ) ^ n) hD' hDM (Nat.cast_nonneg n) hnM hh' hL' hk' hkL' hlk
    (one_le_pow₀ (by norm_num)) (one_le_pow₀ hL') (one_le_pow₀ hk') (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hX7 hlmax
  rw [bakerL7]
  refine le_trans (le_of_eq ?_) (core.trans (le_of_eq ?_)) <;> ring

/-- HOL Light: Baker/param.ml, BAKER_J_EXP. The exponent identity behind Lemma 7. -/
theorem baker_j_exp (n D : ℕ) :
    bakerJ n D + bakerC D * (n + 1) =
      bakerC D * (n + 1) * n + bakerC D * n * (n + 2) + (bakerC D + 2) := by
  rw [bakerJ]; ring

private theorem param_pow6_le (M : ℝ) (D n : ℕ) (hD : 1 ≤ D) (hDM : (D : ℝ) ≤ M) :
    (D : ℝ) * 3 ^ (n + 1) * 2 ^ (n + 2) * (D : ℝ) ^ (n + 2) ≤ (6 * M) ^ (n + 3) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hM1 : 1 ≤ M := hD'.trans hDM
  have hM0 : 0 ≤ M := by linarith
  have h3 : (3 : ℝ) ^ (n + 1) ≤ 3 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hDn : (D : ℝ) ^ (n + 2) ≤ M ^ (n + 2) := pow_le_pow_left₀ (by linarith) hDM _
  have e : (6 * M) ^ (n + 3) = 6 * M * (3 ^ (n + 2) * 2 ^ (n + 2) * M ^ (n + 2)) := by
    rw [pow_succ, show (6 : ℝ) * M = 3 * 2 * M by ring, mul_pow, mul_pow]; ring
  rw [e]
  have h1 : (D : ℝ) * 3 ^ (n + 1) ≤ M * 3 ^ (n + 2) := mul_le_mul hDM h3 (by positivity) hM0
  have h2 : (D : ℝ) * 3 ^ (n + 1) * 2 ^ (n + 2) ≤ M * 3 ^ (n + 2) * 2 ^ (n + 2) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have h4 : (D : ℝ) * 3 ^ (n + 1) * 2 ^ (n + 2) * (D : ℝ) ^ (n + 2) ≤
      M * 3 ^ (n + 2) * 2 ^ (n + 2) * M ^ (n + 2) :=
    mul_le_mul h2 hDn (by positivity) (by positivity)
  have h5 : 0 ≤ M * 3 ^ (n + 2) * 2 ^ (n + 2) * M ^ (n + 2) := by positivity
  linarith

/-- HOL Light: Baker/param.ml, BAKER_KL_LE. `k ≤ L ^ (n + 2)`. -/
theorem baker_kl_le (n D q : ℕ) (hn : 1 ≤ n) (hD : 1 ≤ D) (hq : 1 ≤ q) :
    (bakerKpar n D q : ℝ) ≤ (bakerLpar n D q : ℝ) ^ (n + 2) := by
  have h1 : bakerKpar n D q ≤ bakerLpar n D q ^ (n + 2) := by
    rw [bakerKpar, bakerLpar]
    have h2 : n + 1 ≤ n * (n + 2) := by nlinarith
    calc q ^ (bakerC D * (n + 1)) ≤ q ^ (bakerC D * n * (n + 2)) :=
          Nat.pow_le_pow_right hq (by rw [mul_assoc]; exact Nat.mul_le_mul_left _ h2)
      _ = (q ^ (bakerC D * n)) ^ (n + 2) := pow_mul _ _ _
      _ ≤ (2 * D * q ^ (bakerC D * n)) ^ (n + 2) :=
          Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (by omega)) _
  exact_mod_cast h1

/-- HOL Light: Baker/param.ml, BAKER_X7_LE. A bound for `X7 = h (L + 2) ^ (n + 1)`. -/
theorem baker_x7_le (h L n : ℕ) (hL : 1 ≤ L) :
    ((h * (L + 2) ^ (n + 1) : ℕ) : ℝ) ≤ (h : ℝ) * 3 ^ (n + 1) * (L : ℝ) ^ (n + 1) := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h1 : ((L : ℝ) + 2) ^ (n + 1) ≤ (3 * (L : ℝ)) ^ (n + 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  rw [mul_pow] at h1
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg h : (0 : ℝ) ≤ h)]

/-- HOL Light: Baker/param.ml, BAKER_LMAX_LE. A bound for `lmax = h (L + 2) (L + 1) ^ n`. -/
theorem baker_lmax_le (h L n : ℕ) (hL : 1 ≤ L) :
    ((h * (L + 2) * (L + 1) ^ n : ℕ) : ℝ) ≤ (h : ℝ) * 3 ^ (n + 1) * (L : ℝ) ^ (n + 1) := by
  have h1 : h * (L + 2) * (L + 1) ^ n ≤ h * (L + 2) ^ (n + 1) :=
    calc h * (L + 2) * (L + 1) ^ n ≤ h * (L + 2) * (L + 2) ^ n :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = h * (L + 2) ^ (n + 1) := by ring
  exact le_trans (by exact_mod_cast h1) (baker_x7_le h L n hL)

/-- HOL Light: Baker/param.ml, BAKER_LW_POS. The exponent `bakerLw` is nonnegative. -/
theorem baker_lw_pos (M : ℝ) (D L k h R : ℕ) (hM : 0 ≤ M) (hh : 1 ≤ h) :
    0 ≤ bakerLw M D L k h R := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hlog : 0 ≤ Real.log (((R : ℝ) + (h : ℝ)) / (h : ℝ)) :=
    Real.log_nonneg (by rw [le_div_iff₀ hh0]; linarith)
  rw [bakerLw]
  positivity

private theorem param_l7_power_core (M κ W Tj C ar hr l A B s Kq P : ℝ) (_ : 0 ≤ M)
    (_ : 0 ≤ κ) (_ : 0 ≤ W) (hT : 0 < Tj) (hh : 0 ≤ hr) (hl : 0 ≤ l) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hP : 0 ≤ P) (har : 0 ≤ ar)
    (hmain : (8 * M + 75) * κ * W * (2 * Tj) ≤ C * ar) (hPK : P * Kq = A * B * C)
    (hKs : Kq ≤ s * Tj) :
    (8 * M + 75) * κ * W * (hr * l * A * B) ≤ hr * P * s * ar * l / 2 := by
  have h1 := mul_le_mul_of_nonneg_right hmain (by positivity : 0 ≤ hr * l * A * B)
  have h2 := mul_le_mul_of_nonneg_left hKs (by positivity : 0 ≤ hr * l * ar * P)
  have h4 : C * ar * (hr * l * A * B) = hr * l * ar * P * Kq := by
    rw [show C * ar * (hr * l * A * B) = hr * l * ar * (A * B * C) by ring, ← hPK]; ring
  have h3 : (2 * ((8 * M + 75) * κ * W * (hr * l * A * B))) * Tj ≤ (hr * P * s * ar * l) * Tj := by
    linarith
  have h5 := le_of_mul_le_mul_right h3 hT
  linarith

/-- HOL Light: Baker/param.ml, BAKER_L7_POWER_NUM. The crude bound of `baker_l7_bound` is at
most half of the extrapolation exponent at the last step. -/
theorem baker_l7_power_num (M : ℝ) (D n q h : ℕ) (_ : 1 ≤ n) (hD : 1 ≤ D) (hDM : (D : ℝ) ≤ M)
    (_ : 1 ≤ h) (hq : 4 ≤ q) (hlq : 1 ≤ Real.log q)
    (hq2 : ((bakerC D * (n + 1) : ℕ) : ℝ) * (8 * M + 75) * (6 * M) ^ (n + 3) *
      2 ^ (bakerJ n D + 1) ≤ (q : ℝ)) :
    (8 * M + 75) * (D : ℝ) * (bakerKpar n D q : ℝ) ^ n * 3 ^ (n + 1) * (h : ℝ) *
        (bakerLpar n D q : ℝ) ^ (n + 2) * (((bakerC D * (n + 1) : ℕ) : ℝ) * Real.log q) ≤
      ((h * q ^ bakerJ n D : ℕ) : ℝ) * ((bakerKpar n D q / 2 ^ bakerJ n D + 1 : ℕ) : ℝ) *
        (bakerA D : ℝ) * Real.log q / 2 := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hM1 : 1 ≤ M := hD'.trans hDM
  have hM0 : 0 ≤ M := by linarith
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hκ0 : (0 : ℝ) ≤ ((bakerC D * (n + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hW := param_pow6_le M D n hD hDM
  have hT : (0 : ℝ) < 2 ^ bakerJ n D := by positivity
  have ha1 : (1 : ℝ) ≤ (bakerA D : ℝ) := by
    exact_mod_cast (by rw [bakerA]; omega : 1 ≤ bakerA D)
  have hC : (q : ℝ) ≤ (q : ℝ) ^ (bakerC D + 2) := le_self_pow₀ hq' (by omega)
  have hmain : (8 * M + 75) * ((bakerC D * (n + 1) : ℕ) : ℝ) *
      ((D : ℝ) * 3 ^ (n + 1) * 2 ^ (n + 2) * (D : ℝ) ^ (n + 2)) * (2 * 2 ^ bakerJ n D) ≤
      (q : ℝ) ^ (bakerC D + 2) * (bakerA D : ℝ) := by
    have h1 : (8 * M + 75) * ((bakerC D * (n + 1) : ℕ) : ℝ) * (2 * 2 ^ bakerJ n D) *
        ((D : ℝ) * 3 ^ (n + 1) * 2 ^ (n + 2) * (D : ℝ) ^ (n + 2)) ≤
        (8 * M + 75) * ((bakerC D * (n + 1) : ℕ) : ℝ) * (2 * 2 ^ bakerJ n D) *
          (6 * M) ^ (n + 3) := mul_le_mul_of_nonneg_left hW (by positivity)
    have h2 : (q : ℝ) ^ (bakerC D + 2) * 1 ≤ (q : ℝ) ^ (bakerC D + 2) * (bakerA D : ℝ) :=
      mul_le_mul_of_nonneg_left ha1 (by positivity)
    rw [pow_succ 2 (bakerJ n D)] at hq2
    linarith
  have hPK : (q : ℝ) ^ bakerJ n D * (q : ℝ) ^ (bakerC D * (n + 1)) =
      (q : ℝ) ^ (bakerC D * (n + 1) * n) * (q : ℝ) ^ (bakerC D * n * (n + 2)) *
        (q : ℝ) ^ (bakerC D + 2) := by
    rw [← pow_add, ← pow_add, ← pow_add, baker_j_exp]
  have hk : (bakerKpar n D q : ℝ) = (q : ℝ) ^ (bakerC D * (n + 1)) := by
    rw [bakerKpar]; exact Nat.cast_pow q _
  have hKs : (q : ℝ) ^ (bakerC D * (n + 1)) ≤
      ((bakerKpar n D q / 2 ^ bakerJ n D + 1 : ℕ) : ℝ) * 2 ^ bakerJ n D := by
    have h1 := param_div_suc_le (bakerKpar n D q) (2 ^ bakerJ n D) (by positivity)
    have h2 : ((2 ^ bakerJ n D : ℕ) : ℝ) = 2 ^ bakerJ n D := by simp
    rw [h2, div_le_iff₀ hT] at h1
    rw [← hk]; exact h1
  have core := param_l7_power_core M ((bakerC D * (n + 1) : ℕ) : ℝ)
    ((D : ℝ) * 3 ^ (n + 1) * 2 ^ (n + 2) * (D : ℝ) ^ (n + 2)) (2 ^ bakerJ n D)
    ((q : ℝ) ^ (bakerC D + 2)) (bakerA D) h (Real.log q) ((q : ℝ) ^ (bakerC D * (n + 1) * n))
    ((q : ℝ) ^ (bakerC D * n * (n + 2))) ((bakerKpar n D q / 2 ^ bakerJ n D + 1 : ℕ) : ℝ)
    ((q : ℝ) ^ (bakerC D * (n + 1))) ((q : ℝ) ^ bakerJ n D) hM0 hκ0 (by positivity) hT
    (by positivity) (by linarith) (by positivity) (by positivity) (by positivity) (by positivity)
    hmain hPK hKs
  rw [hk, baker_lpar_real]
  refine le_trans (le_of_eq ?_) (core.trans (le_of_eq ?_))
  · ring
  · push_cast; ring

/-- HOL Light: Baker/param.ml, BAKER_LEMMA7_NUM. At the last step `J` the exponents `bakerLu` and
`bakerL7` are small against `R J * (S J + 1) * a * log q`. -/
theorem baker_lemma7_num (M : ℝ) (D n q h : ℕ) (hn : 1 ≤ n) (hD : 1 ≤ D) (hDM : (D : ℝ) ≤ M)
    (hnM : (n : ℝ) ≤ M) (hh : 1 ≤ h) (hq : 4 ≤ q) (hlq : 112 ≤ Real.log q)
    (hq1 : 2176 * M ^ 3 * 2 ^ bakerJ n D ≤ (q : ℝ))
    (hq2 : ((bakerC D * (n + 1) : ℕ) : ℝ) * (8 * M + 75) * (6 * M) ^ (n + 3) *
      2 ^ (bakerJ n D + 1) ≤ (q : ℝ)) :
    bakerLu M (bakerLpar n D q) (bakerKpar n D q) h
          (4 * q ^ bakerA D * (h * q ^ bakerJ n D) + 1) + 1 +
        (bakerL7 M D n (bakerLpar n D q) (bakerKpar n D q) h
            (h * (bakerLpar n D q + 2) ^ (n + 1))
            (h * (bakerLpar n D q + 2) * (bakerLpar n D q + 1) ^ n)
            (((bakerC D * (n + 1) : ℕ) : ℝ) * Real.log q) +
          6 * (h : ℝ) * (bakerLpar n D q : ℝ) * (((bakerC D * (n + 1) : ℕ) : ℝ) * Real.log q) +
          2) ≤
      ((h * q ^ bakerJ n D : ℕ) : ℝ) * ((bakerKpar n D q / 2 ^ bakerJ n D + 1 : ℕ) : ℝ) *
        (bakerA D : ℝ) * Real.log q := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hM1 : 1 ≤ M := hD'.trans hDM
  have hM0 : 0 ≤ M := by linarith
  have hq1' : 1 ≤ q := by omega
  have hq' : (4 : ℝ) ≤ q := by exact_mod_cast hq
  have hl0 : 0 ≤ Real.log q := by linarith
  obtain ⟨hL1, hk1⟩ := baker_par_pos n D q hD hq1'
  have hκ1 : (1 : ℝ) ≤ ((bakerC D * (n + 1) : ℕ) : ℝ) := by
    exact_mod_cast (by rw [bakerC]; exact Nat.mul_pos (by omega) (by omega) :
      1 ≤ bakerC D * (n + 1))
  have hlk1 : 1 ≤ ((bakerC D * (n + 1) : ℕ) : ℝ) * Real.log q :=
    one_le_mul_of_one_le_of_one_le hκ1 (by linarith)
  have hl7 := baker_l7_bound M D n (bakerLpar n D q) (bakerKpar n D q) h
    (h * (bakerLpar n D q + 2) ^ (n + 1))
    (h * (bakerLpar n D q + 2) * (bakerLpar n D q + 1) ^ n)
    (((bakerC D * (n + 1) : ℕ) : ℝ) * Real.log q) hn hD hDM hnM hh hL1 hk1
    (baker_kl_le n D q hn hD hq1') hlk1 (baker_x7_le h _ n hL1) (baker_lmax_le h _ n hL1)
  have hpow := baker_l7_power_num M D n q h hn hD hDM hh hq (by linarith) hq2
  obtain ⟨J', hJ'⟩ : ∃ J', bakerJ n D = J' + 1 := ⟨bakerJ n D - 1, by rw [bakerJ]; omega⟩
  have hbig : 2176 * M ^ 3 * 2 ^ J' ≤ (q : ℝ) := by
    rw [hJ', pow_succ 2 J'] at hq1
    linarith [mul_nonneg (pow_nonneg hM0 3) (by positivity : (0 : ℝ) ≤ 2 ^ J')]
  have hstep := baker_step_num M D n q h J' hn hD hDM hh hq hlq hbig
  have hlw := baker_lw_pos M D (bakerLpar n D q) (bakerKpar n D q) h (h * q ^ (J' + 1)) hM0 hh
  rw [hJ'] at hpow ⊢
  have hRJ : ((h * q ^ (J' + 1) : ℕ) : ℝ) = (q : ℝ) * ((h * q ^ J' : ℕ) : ℝ) := by
    push_cast; ring
  rw [hRJ] at hpow ⊢
  have hYX0 : 0 ≤ ((h * q ^ J' : ℕ) : ℝ) * ((bakerKpar n D q / 2 ^ (J' + 1) + 1 : ℕ) : ℝ) *
      (bakerA D : ℝ) * Real.log q := by positivity
  have hq4 := mul_le_mul_of_nonneg_right hq' hYX0
  linarith

/-! ### Exponential bounds for the error terms of the extrapolation -/

private theorem param_two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
  linarith [Real.add_one_le_exp (1 : ℝ)]

private theorem param_exp_neg_one_le : Real.exp (-1) ≤ 1 / 2 := by
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by norm_num) param_two_le_exp_one

private theorem param_exp_neg_three_le : Real.exp (-3) ≤ 1 / 16 := by
  have h1 : (16 : ℝ) ≤ Real.exp 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    calc (16 : ℝ) ≤ 2.7 ^ 3 := by norm_num
      _ ≤ Real.exp 1 ^ 3 :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 3
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by norm_num) h1

private theorem param_exp_neg_two_lt : Real.exp (-2) < 1 / 3 := by
  have h1 : (3 : ℝ) < Real.exp 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    calc (3 : ℝ) < 2 ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) param_two_le_exp_one 2
  rw [Real.exp_neg, one_div]
  exact inv_strictAnti₀ (by norm_num) h1

private theorem param_nat_le_exp (x : ℕ) : (x : ℝ) ≤ Real.exp x := by
  linarith [Real.add_one_le_exp (x : ℝ)]

private theorem param_two_pow_le_exp (s : ℕ) : (2 : ℝ) ^ s ≤ Real.exp s := by
  rw [← mul_one (s : ℝ), Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) param_two_le_exp_one s

private theorem param_num_mul_16_pow_le_exp (y : ℕ) :
    (y : ℝ) * 16 ^ y ≤ Real.exp (5 * (y : ℝ)) := by
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) param_two_le_exp_one 4
  have h1 : (16 : ℝ) ^ y ≤ Real.exp ((y : ℝ) * 4) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (by norm_num) h16 y
  calc (y : ℝ) * 16 ^ y ≤ Real.exp y * Real.exp ((y : ℝ) * 4) :=
        mul_le_mul (param_nat_le_exp y) h1 (by positivity) (Real.exp_pos _).le
    _ = Real.exp (5 * (y : ℝ)) := by rw [← Real.exp_add]; congr 1; ring

private theorem param_term2_exp_le (x y s n : ℕ) :
    2 * (x : ℝ) * 2 ^ s * Real.exp n * ((y : ℝ) * 16 ^ y) ^ (s + 1) ≤
      Real.exp (1 + (x : ℝ) + (s : ℝ) + (n : ℝ) + 5 * (y : ℝ) * ((s : ℝ) + 1)) := by
  have h5 : ((y : ℝ) * 16 ^ y) ^ (s + 1) ≤ Real.exp (5 * (y : ℝ)) ^ (s + 1) :=
    pow_le_pow_left₀ (by positivity) (param_num_mul_16_pow_le_exp y) _
  calc 2 * (x : ℝ) * 2 ^ s * Real.exp n * ((y : ℝ) * 16 ^ y) ^ (s + 1)
      ≤ Real.exp 1 * Real.exp x * Real.exp s * Real.exp n * Real.exp (5 * (y : ℝ)) ^ (s + 1) :=
        mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul param_two_le_exp_one (param_nat_le_exp x)
          (by positivity) (by positivity)) (param_two_pow_le_exp s) (by positivity)
          (by positivity)) le_rfl (by positivity) (by positivity)) h5 (by positivity)
          (by positivity)
    _ = Real.exp (1 + (x : ℝ) + (s : ℝ) + (n : ℝ) + 5 * (y : ℝ) * ((s : ℝ) + 1)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1; push_cast; ring

private theorem param_term12_exp_le (k x s n : ℕ) :
    2 * (k : ℝ) * (x : ℝ) * (2 * (k : ℝ)) ^ s * Real.exp n * ((x : ℝ) * 16 ^ x) ^ (s + 1) ≤
      Real.exp (1 + (k : ℝ) + (x : ℝ) + (s : ℝ) * (1 + (k : ℝ)) + (n : ℝ) +
        5 * (x : ℝ) * ((s : ℝ) + 1)) := by
  have h2k : 2 * (k : ℝ) ≤ Real.exp (1 + (k : ℝ)) := by
    rw [Real.exp_add]
    exact mul_le_mul param_two_le_exp_one (param_nat_le_exp k) (by positivity) (by positivity)
  have h5 : ((x : ℝ) * 16 ^ x) ^ (s + 1) ≤ Real.exp (5 * (x : ℝ)) ^ (s + 1) :=
    pow_le_pow_left₀ (by positivity) (param_num_mul_16_pow_le_exp x) _
  have h2ks : (2 * (k : ℝ)) ^ s ≤ Real.exp (1 + (k : ℝ)) ^ s :=
    pow_le_pow_left₀ (by positivity) h2k s
  calc 2 * (k : ℝ) * (x : ℝ) * (2 * (k : ℝ)) ^ s * Real.exp n * ((x : ℝ) * 16 ^ x) ^ (s + 1)
      ≤ Real.exp (1 + (k : ℝ)) * Real.exp x * Real.exp (1 + (k : ℝ)) ^ s * Real.exp n *
          Real.exp (5 * (x : ℝ)) ^ (s + 1) :=
        mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h2k (param_nat_le_exp x)
          (by positivity) (by positivity)) h2ks (by positivity)
          (by positivity)) le_rfl (by positivity) (by positivity)) h5 (by positivity)
          (by positivity)
    _ = Real.exp (1 + (k : ℝ) + (x : ℝ) + (s : ℝ) * (1 + (k : ℝ)) + (n : ℝ) +
          5 * (x : ℝ) * ((s : ℝ) + 1)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add,
          ← Real.exp_add, ← Real.exp_add]
        congr 1; push_cast; ring

/-! ### The simple conditions -/

/-- HOL Light: Baker/param.ml, BAKER_L_LE_K. `L ≤ k`. -/
theorem baker_l_le_k (n D q : ℕ) (_ : 1 ≤ q) (h2 : 2 * D ≤ q) :
    bakerLpar n D q ≤ bakerKpar n D q := by
  have hc : bakerC D ≠ 0 := by have := baker_c_pos D; omega
  rw [bakerLpar, bakerKpar, show bakerC D * (n + 1) = bakerC D + bakerC D * n by ring, pow_add]
  exact Nat.mul_le_mul_right _ (h2.trans (Nat.le_self_pow hc q))

/-- HOL Light: Baker/param.ml, BAKER_SIEGEL_NUM. The counting condition of Siegel's lemma. -/
theorem baker_siegel_num (n D q : ℕ) (_ : 1 ≤ n) (hD : 1 ≤ D) (hq : 1 ≤ q) :
    2 * D * (bakerKpar n D q + 1) ^ n ≤ (bakerLpar n D q + 1) * (bakerLpar n D q + 1) ^ n := by
  obtain ⟨-, hk1⟩ := baker_par_pos n D q hD hq
  have h1 : (bakerKpar n D q + 1) ^ n ≤ (2 * bakerKpar n D q) ^ n :=
    Nat.pow_le_pow_left (by omega) _
  have h2 : D ≤ D ^ (n + 1) := Nat.le_self_pow (by omega) D
  calc 2 * D * (bakerKpar n D q + 1) ^ n ≤ 2 * D * (2 * bakerKpar n D q) ^ n :=
        Nat.mul_le_mul_left _ h1
    _ = 2 ^ (n + 1) * q ^ (bakerC D * n * (n + 1)) * D := by rw [bakerKpar]; ring
    _ ≤ 2 ^ (n + 1) * q ^ (bakerC D * n * (n + 1)) * D ^ (n + 1) := Nat.mul_le_mul_left _ h2
    _ = bakerLpar n D q * bakerLpar n D q ^ n := by rw [bakerLpar]; ring
    _ ≤ (bakerLpar n D q + 1) * (bakerLpar n D q + 1) ^ n :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) _)

/-- HOL Light: Baker/param.ml, BAKER_LLAM_LT. `L * Lam < 2 π k`. -/
theorem baker_llam_lt (n D q : ℕ) (Lam : ℝ) (hq : 1 ≤ q) (_ : 0 ≤ Lam)
    (h : 2 * (D : ℝ) * Lam ≤ (q : ℝ)) :
    (bakerLpar n D q : ℝ) * Lam < 2 * Real.pi * (bakerKpar n D q : ℝ) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hB : (0 : ℝ) < (q : ℝ) ^ (bakerC D * n) := pow_pos (by linarith) _
  have hc : bakerC D ≠ 0 := by have := baker_c_pos D; omega
  have hqc : (q : ℝ) ≤ (q : ℝ) ^ bakerC D := le_self_pow₀ hq' hc
  have hk : (bakerKpar n D q : ℝ) = (q : ℝ) ^ bakerC D * (q : ℝ) ^ (bakerC D * n) := by
    rw [bakerKpar]; push_cast; ring
  rw [baker_lpar_real, hk]
  have h1 := mul_le_mul_of_nonneg_right (h.trans hqc) hB.le
  have h2 : (0 : ℝ) < (q : ℝ) ^ bakerC D * (q : ℝ) ^ (bakerC D * n) :=
    mul_pos (pow_pos (by linarith) _) hB
  nlinarith [mul_le_mul_of_nonneg_right Real.two_le_pi h2.le]

/-- HOL Light: Baker/param.ml, BAKER_X7_LE_R. `X7 ≤ R J`. -/
theorem baker_x7_le_r (n D q h : ℕ) (_ : 1 ≤ n) (hD : 1 ≤ D) (hq : 6 * D ≤ q) :
    h * (bakerLpar n D q + 2) ^ (n + 1) ≤ h * q ^ bakerJ n D := by
  have hq1 : 1 ≤ q := by omega
  apply Nat.mul_le_mul_left
  have hx : 0 < q ^ (bakerC D * n) := pow_pos (show 0 < q from hq1) _
  have h1 : bakerLpar n D q + 2 ≤ q ^ (bakerC D * n + 1) := by
    rw [bakerLpar, pow_succ]
    have h2 : 1 ≤ D * q ^ (bakerC D * n) := Nat.mul_pos hD hx
    calc 2 * D * q ^ (bakerC D * n) + 2 ≤ 6 * D * q ^ (bakerC D * n) := by nlinarith
      _ ≤ q ^ (bakerC D * n) * q := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hq
  have hexp : (bakerC D * n + 1) * (n + 1) ≤ bakerJ n D := by
    rw [bakerJ]
    have hc := baker_c_pos D
    generalize bakerC D = c at hc ⊢
    nlinarith [Nat.mul_le_mul_right n hc, Nat.zero_le (c * n * n), Nat.zero_le (c * n)]
  calc (bakerLpar n D q + 2) ^ (n + 1) ≤ (q ^ (bakerC D * n + 1)) ^ (n + 1) :=
        Nat.pow_le_pow_left h1 _
    _ = q ^ ((bakerC D * n + 1) * (n + 1)) := (pow_mul _ _ _).symm
    _ ≤ q ^ bakerJ n D := Nat.pow_le_pow_right hq1 hexp

/-- HOL Light: Baker/param.ml, BAKER_S_HALF. `2 * S (K + 1) ≤ S K`. -/
theorem baker_s_half (k K : ℕ) : 2 * (k / 2 ^ (K + 1)) ≤ k / 2 ^ K := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.mul_div_le _ 2

/-- HOL Light: Baker/param.ml, BAKER_ZBOUND. The extrapolation exponents are at most the unit
`U = h q ^ (c (n + 1) + J + 3)`. -/
theorem baker_zbound (D n q h K m : ℕ) (_ : 1 ≤ D) (hq : 8 * D + 8 ≤ q)
    (hK : K ≤ bakerJ n D) :
    ((h * q ^ K : ℕ) : ℝ) * ((bakerKpar n D q / 2 ^ m + 1 : ℕ) : ℝ) * (bakerA D : ℝ) *
        Real.log q ≤
      (h : ℝ) * (q : ℝ) ^ (bakerC D * (n + 1) + bakerJ n D + 3) := by
  have hq1 : 1 ≤ q := by omega
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast (by omega : 2 ≤ q)
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hqJ : (0 : ℝ) < (q : ℝ) ^ bakerJ n D := pow_pos (by linarith) _
  have hqk : (0 : ℝ) < (q : ℝ) ^ (bakerC D * (n + 1)) := pow_pos (by linarith) _
  have h1 : ((h * q ^ K : ℕ) : ℝ) ≤ (h : ℝ) * (q : ℝ) ^ bakerJ n D := by
    push_cast
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hK) hh0
  have hk1 : 1 ≤ bakerKpar n D q := (baker_par_pos n D q ‹_› hq1).2
  have h2 : ((bakerKpar n D q / 2 ^ m + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ (bakerC D * (n + 1)) := by
    have h3 : bakerKpar n D q / 2 ^ m + 1 ≤ 2 * bakerKpar n D q := by
      have := Nat.div_le_self (bakerKpar n D q) (2 ^ m); omega
    calc ((bakerKpar n D q / 2 ^ m + 1 : ℕ) : ℝ) ≤ ((2 * bakerKpar n D q : ℕ) : ℝ) := by
          exact_mod_cast h3
      _ = 2 * (q : ℝ) ^ (bakerC D * (n + 1)) := by rw [bakerKpar]; push_cast; ring
  have h3 : (bakerA D : ℝ) ≤ q := by exact_mod_cast (by rw [bakerA]; exact hq : bakerA D ≤ q)
  have h4 : Real.log q ≤ q := log_le_self _ (by linarith)
  have hl0 : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  calc ((h * q ^ K : ℕ) : ℝ) * ((bakerKpar n D q / 2 ^ m + 1 : ℕ) : ℝ) * (bakerA D : ℝ) *
        Real.log q
      ≤ (h : ℝ) * (q : ℝ) ^ bakerJ n D * (2 * (q : ℝ) ^ (bakerC D * (n + 1))) * q * q :=
        mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3
          (by positivity) (by positivity)) h4 hl0 (by positivity)
    _ ≤ (h : ℝ) * (q : ℝ) ^ bakerJ n D * ((q : ℝ) * (q : ℝ) ^ (bakerC D * (n + 1))) * q * q := by
        have h5 : 2 * (q : ℝ) ^ (bakerC D * (n + 1)) ≤ (q : ℝ) * (q : ℝ) ^ (bakerC D * (n + 1)) :=
          mul_le_mul_of_nonneg_right hq' hqk.le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h5 (by positivity)) (by linarith)) (by linarith)
    _ = (h : ℝ) * (q : ℝ) ^ (bakerC D * (n + 1) + bakerJ n D + 3) := by ring

/-! ### The exponent `e1` of `eps` and the unit `U = h q ^ (c (n + 1) + J + 3)` -/

private theorem param_inv_pow_exp (q a m : ℕ) (hq : 1 ≤ q) :
    (((q : ℝ) ^ a)⁻¹) ^ m = Real.exp (-((m : ℝ) * (a : ℝ) * Real.log q)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : (q : ℝ) ^ a = Real.exp ((a : ℝ) * Real.log q) := by
    rw [Real.exp_nat_mul, Real.exp_log hq0]
  rw [h1, ← Real.exp_neg, ← Real.exp_nat_mul]
  congr 1; ring

private theorem param_ratio (q a R : ℕ) (hR : 1 ≤ R) (hq : 1 ≤ q) :
    4 * (R : ℝ) / ((4 * q ^ a * R : ℕ) : ℝ) = ((q : ℝ) ^ a)⁻¹ := by
  have hR' : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hqa : (q : ℝ) ^ a ≠ 0 := pow_ne_zero _ hq'
  push_cast
  rw [inv_eq_one_div, div_eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) hqa) hR') hqa]
  ring

private theorem param_kpow_le (k h L : ℕ) (hk : 1 ≤ k) (hL : 1 ≤ L) :
    (k : ℝ) ^ (2 * h * (L + 2)) ≤ Real.exp (6 * (h : ℝ) * (L : ℝ) * Real.log k) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hl0 : 0 ≤ Real.log k := Real.log_nonneg hk'
  have h1 : (k : ℝ) ^ (2 * h * (L + 2)) =
      Real.exp (((2 * h * (L + 2) : ℕ) : ℝ) * Real.log k) := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
  rw [h1]
  apply Real.exp_le_exp.2
  apply mul_le_mul_of_nonneg_right _ hl0
  push_cast
  nlinarith [mul_nonneg (Nat.cast_nonneg h : (0 : ℝ) ≤ h) (sub_nonneg.2 hL')]

/-- HOL Light: Baker/param.ml, BAKER_KAP_LE_J. `c (n + 1) ≤ J`. -/
theorem baker_kap_le_j (n D : ℕ) (hn : 1 ≤ n) : bakerC D * (n + 1) ≤ bakerJ n D := by
  rw [bakerJ]
  have h1 : n + 1 ≤ 2 * n * n + 2 * n := by nlinarith
  exact (Nat.mul_le_mul_left _ h1).trans (Nat.le_add_right _ _)

private theorem param_units_core (hr A B C Q : ℝ) (hh : 1 ≤ hr) (hA : 1 ≤ A) (hAB : A ≤ B)
    (hC : 4096 ≤ C) (hQ : 16 ≤ Q) :
    1 ≤ hr * (A * B * C) ∧ 16 * (hr * (A * B * C)) ≤ A * B * C * Q * hr ∧
      hr * B ≤ hr * (A * B * C) ∧ A ≤ hr * (A * B * C) ∧
      5 * (hr * B) * (A + 1) ≤ hr * (A * B * C) ∧ 2 * (hr * B) * A ≤ hr * (A * B * C) ∧
      A * (1 + A) ≤ hr * (A * B * C) := by
  have hB : 1 ≤ B := hA.trans hAB
  have hhB : 1 ≤ hr * B := one_le_mul_of_one_le_of_one_le hh hB
  have hW1 : 1 ≤ hr * B * A := one_le_mul_of_one_le_of_one_le hhB hA
  have hWC := mul_le_mul_of_nonneg_left hC (by linarith : (0 : ℝ) ≤ hr * B * A)
  have hAW := mul_le_mul_of_nonneg_right hhB (by linarith : (0 : ℝ) ≤ A)
  have hBW := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ hr * B)
  have hAA := mul_le_mul_of_nonneg_left hAB (by linarith : (0 : ℝ) ≤ A)
  have hAB' := mul_le_mul_of_nonneg_right hh (by nlinarith : (0 : ℝ) ≤ A * B)
  have hWCQ := mul_le_mul_of_nonneg_left hQ (by nlinarith : (0 : ℝ) ≤ hr * B * A * C)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- HOL Light: Baker/param.ml, BAKER_UNITS. The crude bounds by the unit
`U = h q ^ (c (n + 1) + J + 3)`, which is at most `q ^ e1 h / 16`. -/
theorem baker_units (n D q h : ℕ) (hn : 1 ≤ n) (hq : 16 ≤ q) (hh : 1 ≤ h) :
    1 ≤ (h : ℝ) * (q : ℝ) ^ (bakerC D * (n + 1) + bakerJ n D + 3) ∧
      16 * ((h : ℝ) * (q : ℝ) ^ (bakerC D * (n + 1) + bakerJ n D + 3)) ≤
        (q : ℝ) ^ bakerE1 n D * (h : ℝ) ∧
      (∀ K, K ≤ bakerJ n D → ((h * q ^ K : ℕ) : ℝ) ≤
        (h : ℝ) * (q : ℝ) ^ (bakerC D * (n + 1) + bakerJ n D + 3)) ∧
      (bakerKpar n D q : ℝ) ≤ (h : ℝ) * (q : ℝ) ^ (bakerC D * (n + 1) + bakerJ n D + 3) ∧
      5 * ((h * q ^ bakerJ n D : ℕ) : ℝ) * ((bakerKpar n D q : ℝ) + 1) ≤
        (h : ℝ) * (q : ℝ) ^ (bakerC D * (n + 1) + bakerJ n D + 3) ∧
      2 * ((h * q ^ bakerJ n D : ℕ) : ℝ) * (bakerKpar n D q : ℝ) ≤
        (h : ℝ) * (q : ℝ) ^ (bakerC D * (n + 1) + bakerJ n D + 3) ∧
      (bakerKpar n D q : ℝ) * (1 + (bakerKpar n D q : ℝ)) ≤
        (h : ℝ) * (q : ℝ) ^ (bakerC D * (n + 1) + bakerJ n D + 3) := by
  have hκJ := baker_kap_le_j n D hn
  have hq' : (16 : ℝ) ≤ q := by exact_mod_cast hq
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hA : (1 : ℝ) ≤ (q : ℝ) ^ (bakerC D * (n + 1)) := one_le_pow₀ (by linarith)
  have hAB : (q : ℝ) ^ (bakerC D * (n + 1)) ≤ (q : ℝ) ^ bakerJ n D :=
    pow_le_pow_right₀ (by linarith) hκJ
  have hC : (4096 : ℝ) ≤ (q : ℝ) ^ 3 :=
    calc (4096 : ℝ) = 16 ^ 3 := by norm_num
      _ ≤ (q : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hq' 3
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := param_units_core h ((q : ℝ) ^ (bakerC D * (n + 1)))
    ((q : ℝ) ^ bakerJ n D) ((q : ℝ) ^ 3) q hh' hA hAB hC hq'
  have hU : (q : ℝ) ^ (bakerC D * (n + 1) + bakerJ n D + 3) =
      (q : ℝ) ^ (bakerC D * (n + 1)) * (q : ℝ) ^ bakerJ n D * (q : ℝ) ^ 3 := by
    rw [pow_add, pow_add]
  have hE : (q : ℝ) ^ bakerE1 n D =
      (q : ℝ) ^ (bakerC D * (n + 1)) * (q : ℝ) ^ bakerJ n D * (q : ℝ) ^ 3 * q := by
    rw [bakerE1, pow_add, pow_add]; ring
  have hk : (bakerKpar n D q : ℝ) = (q : ℝ) ^ (bakerC D * (n + 1)) := by
    rw [bakerKpar]; exact Nat.cast_pow q _
  have hRJ : ((h * q ^ bakerJ n D : ℕ) : ℝ) = (h : ℝ) * (q : ℝ) ^ bakerJ n D := by push_cast; ring
  rw [hU, hE, hk, hRJ]
  refine ⟨c1, c2, ?_, c4, c5, c6, c7⟩
  intro K hK
  have h1 : ((h * q ^ K : ℕ) : ℝ) ≤ (h : ℝ) * (q : ℝ) ^ bakerJ n D := by
    push_cast
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hK) (by linarith)
  exact h1.trans c3

/-! ### The numeric core -/

private theorem param_step_assemble (ub lu lw Z E vb r : ℝ) (x y s n m : ℕ)
    (hub : ub ≤ Real.exp lu) (hZ : lu + lw + 3 ≤ Z) (hr : r ^ m = Real.exp (-Z))
    (hvb : Real.exp (-lw) / 2 ≤ vb)
    (hE : 1 + (x : ℝ) + (s : ℝ) + (n : ℝ) + 5 * (y : ℝ) * ((s : ℝ) + 1) + lw + 3 ≤ E) :
    2 * ub * r ^ m + Real.exp (-E) * 2 * (x : ℝ) * 2 ^ s * Real.exp n *
        ((y : ℝ) * 16 ^ y) ^ (s + 1) ≤ vb / 2 := by
  have hw : 0 < Real.exp (-lw) := Real.exp_pos _
  have he3 := param_exp_neg_three_le
  have t1 : 2 * ub * r ^ m ≤ 2 * (Real.exp (-lw) * Real.exp (-3)) := by
    rw [hr, ← Real.exp_add]
    have h1 : ub * Real.exp (-Z) ≤ Real.exp lu * Real.exp (-Z) :=
      mul_le_mul_of_nonneg_right hub (Real.exp_pos _).le
    rw [← Real.exp_add] at h1
    have h2 : Real.exp (lu + -Z) ≤ Real.exp (-lw + -3) := Real.exp_le_exp.2 (by linarith)
    linarith
  have t2 : Real.exp (-E) * 2 * (x : ℝ) * 2 ^ s * Real.exp n * ((y : ℝ) * 16 ^ y) ^ (s + 1) ≤
      Real.exp (-lw) * Real.exp (-3) := by
    have h1 := param_term2_exp_le x y s n
    calc Real.exp (-E) * 2 * (x : ℝ) * 2 ^ s * Real.exp n * ((y : ℝ) * 16 ^ y) ^ (s + 1)
        = Real.exp (-E) * (2 * (x : ℝ) * 2 ^ s * Real.exp n * ((y : ℝ) * 16 ^ y) ^ (s + 1)) := by
          ring
      _ ≤ Real.exp (-E) *
            Real.exp (1 + (x : ℝ) + (s : ℝ) + (n : ℝ) + 5 * (y : ℝ) * ((s : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp (-E + (1 + (x : ℝ) + (s : ℝ) + (n : ℝ) + 5 * (y : ℝ) * ((s : ℝ) + 1))) :=
          (Real.exp_add _ _).symm
      _ ≤ Real.exp (-lw + -3) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp (-lw) * Real.exp (-3) := Real.exp_add _ _
  nlinarith [mul_le_mul_of_nonneg_left he3 hw.le]

private theorem param_lem7_assemble (ub lu l7 T6 Z E err liou r kp : ℝ) (kk x s n m : ℕ)
    (hub : ub ≤ Real.exp lu) (hZ : lu + 1 + (l7 + T6 + 2) ≤ Z)
    (hr : r ^ m = Real.exp (-Z)) (hkp0 : 0 ≤ kp) (hkp : kp ≤ Real.exp T6)
    (hE : 1 + (kk : ℝ) + (x : ℝ) + (s : ℝ) * (1 + (kk : ℝ)) + (n : ℝ) +
      5 * (x : ℝ) * ((s : ℝ) + 1) + (l7 + T6 + 2) ≤ E)
    (herr : err ≤ Real.exp (-E)) (hliou : Real.exp (-l7) ≤ liou) :
    kp * (2 * ub * r ^ m + Real.exp (-E) * 2 * (kk : ℝ) * (x : ℝ) * (2 * (kk : ℝ)) ^ s *
        Real.exp n * ((x : ℝ) * 16 ^ x) ^ (s + 1) + err) < liou := by
  obtain ⟨T, hT⟩ : ∃ T, T = l7 + T6 + 2 := ⟨_, rfl⟩
  rw [← hT] at hZ hE
  have heT : 0 < Real.exp (-T) := Real.exp_pos _
  have t1 : 2 * ub * r ^ m ≤ Real.exp (-T) := by
    rw [hr]
    have h1 : ub * Real.exp (-Z) ≤ Real.exp lu * Real.exp (-Z) :=
      mul_le_mul_of_nonneg_right hub (Real.exp_pos _).le
    rw [← Real.exp_add] at h1
    have h2 : Real.exp (lu + -Z) ≤ Real.exp (-T + -1) := Real.exp_le_exp.2 (by linarith)
    have h3 : Real.exp (-T + -1) = Real.exp (-T) * Real.exp (-1) := Real.exp_add _ _
    linarith [mul_le_mul_of_nonneg_left param_exp_neg_one_le heT.le]
  have t2 : Real.exp (-E) * 2 * (kk : ℝ) * (x : ℝ) * (2 * (kk : ℝ)) ^ s * Real.exp n *
      ((x : ℝ) * 16 ^ x) ^ (s + 1) ≤ Real.exp (-T) := by
    have h1 := param_term12_exp_le kk x s n
    calc Real.exp (-E) * 2 * (kk : ℝ) * (x : ℝ) * (2 * (kk : ℝ)) ^ s * Real.exp n *
          ((x : ℝ) * 16 ^ x) ^ (s + 1)
        = Real.exp (-E) * (2 * (kk : ℝ) * (x : ℝ) * (2 * (kk : ℝ)) ^ s * Real.exp n *
            ((x : ℝ) * 16 ^ x) ^ (s + 1)) := by ring
      _ ≤ Real.exp (-E) * Real.exp (1 + (kk : ℝ) + (x : ℝ) + (s : ℝ) * (1 + (kk : ℝ)) + (n : ℝ) +
            5 * (x : ℝ) * ((s : ℝ) + 1)) := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp (-E + (1 + (kk : ℝ) + (x : ℝ) + (s : ℝ) * (1 + (kk : ℝ)) + (n : ℝ) +
            5 * (x : ℝ) * ((s : ℝ) + 1))) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-T) := Real.exp_le_exp.2 (by linarith)
  have p1 : (0 : ℝ) ≤ (s : ℝ) * (1 + (kk : ℝ)) := by positivity
  have p2 : (0 : ℝ) ≤ 5 * (x : ℝ) * ((s : ℝ) + 1) := by positivity
  have p3 : (0 : ℝ) ≤ (kk : ℝ) := Nat.cast_nonneg _
  have p4 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg _
  have p5 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have t3 : err ≤ Real.exp (-T) := herr.trans (Real.exp_le_exp.2 (by linarith))
  have hsum := add_le_add (add_le_add t1 t2) t3
  refine lt_of_le_of_lt ((mul_le_mul_of_nonneg_left hsum hkp0).trans
    (mul_le_mul_of_nonneg_right hkp (by positivity))) ?_
  have h2 : Real.exp T6 * Real.exp (-T) = Real.exp (-l7) * Real.exp (-2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [hT]; ring
  have h3 := param_exp_neg_two_lt
  have h4 : 0 < Real.exp (-l7) := Real.exp_pos _
  nlinarith [mul_lt_mul_of_pos_left h3 h4]

private theorem param_err_bound (err ub NL d0 U E E' : ℝ) (hub0 : 0 ≤ ub)
    (hd00 : 0 ≤ d0) (herr : NL * d0 ≤ 1 → err ≤ Real.exp 1 * (NL * d0) * ub)
    (hub : ub ≤ Real.exp U) (hNL : NL ≤ U) (hU1 : 1 ≤ U) (hUE : 16 * U ≤ E)
    (hEE : 16 * E ≤ E') (hd0 : d0 ≤ Real.exp (-E')) : err ≤ Real.exp (-E) := by
  have hNLe : NL ≤ Real.exp U := hNL.trans (by linarith [Real.add_one_le_exp U])
  have hUE' : Real.exp U ≤ Real.exp E' := Real.exp_le_exp.2 (by linarith)
  have h1 : NL * d0 ≤ Real.exp U * Real.exp (-E') :=
    mul_le_mul hNLe hd0 hd00 (Real.exp_pos _).le
  have h2 : NL * d0 ≤ 1 := by
    have h : Real.exp E' * Real.exp (-E') = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith [mul_le_mul_of_nonneg_right hUE' (Real.exp_pos (-E')).le]
  have h3 := herr h2
  have h4 : Real.exp 1 * (NL * d0) * ub ≤
      Real.exp 1 * (Real.exp U * Real.exp (-E')) * Real.exp U :=
    mul_le_mul (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le) hub hub0 (by positivity)
  have h5 : Real.exp 1 * (Real.exp U * Real.exp (-E')) * Real.exp U =
      Real.exp (1 + (U + -E') + U) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add]
  have h6 : Real.exp (1 + (U + -E') + U) ≤ Real.exp (-E) := Real.exp_le_exp.2 (by linarith)
  linarith

/-- HOL Light: Baker/param.ml, BAKER_CORE_NUMERIC. The numeric core of the Baker method: for the
explicit parameters all numeric hypotheses of `baker_core_parametric` hold, so data as in
`baker_core_parametric` with `M` bounding `n`, the degree product, `Lam`, the heights of the
`theta r` and `log (1 / lmin)`, `q` large in terms of `M`, `n`, the degree product, and `h`
bounding `M`, `log k`, `log G`, `log Bb`, `log Gn` and the heights of the extra variables, cannot
have `‖beta 0 + ∑ beta r * lg r - lg n‖ ≤ exp (-(q ^ (e1 + 1) * h))`.

Deviation: HOL's hypothesis `FINITE V` is dropped, `V` being a `Finset`; the integer-constrained
reals `a r j` and `b r` are `ℤ`-valued, as in `baker_core_parametric`. -/
theorem baker_core_numeric (n : ℕ) (lg theta : ℕ → ℂ) (V : Finset ℕ)
    (g : ℕ → (ℕ → ℂ) → ℂ) (e : ℕ → ℕ) (G : ℝ) (a : ℕ → ℕ → ℤ) (d : ℕ → ℕ) (H : ℕ → ℝ)
    (beta : ℕ → ℂ) (Bb Lam d0 lmin Gn M : ℝ) (q h : ℕ)
    (hn : 1 ≤ n) (hG : 1 ≤ G) (hV : Finset.Icc 1 n ⊆ V)
    (htheta : ∀ r ∈ Finset.Icc 1 n, theta r = Complex.exp (lg r))
    (hg : ∀ j, j ≤ n → intpoly V e G (g j))
    (hgn : g n theta ≠ 0) (hGn : ‖g n theta‖ ≤ Gn) (hGn1 : 1 ≤ Gn)
    (hbeta : ∀ j, j < n → beta j * g n theta = -(g j theta))
    (ha : ∀ r ∈ V, 1 ≤ d r ∧ 1 ≤ H r ∧ (∀ j, |(a r j : ℝ)| ≤ H r) ∧ a r (d r) ≠ 0 ∧
      ∑ j ∈ Finset.range (d r + 1), (a r j : ℂ) * theta r ^ j = 0)
    (hind : ∀ b : ℕ → ℤ,
      (∀ r ∈ Finset.Icc 1 n, |(b r : ℝ)| ≤ bakerLpar n (∏ r ∈ V, d r) q) →
      ∑ r ∈ Finset.Icc 1 n, (b r : ℂ) * lg r = 0 → ∀ r ∈ Finset.Icc 1 n, b r = 0)
    (hBb : 1 ≤ Bb) (hbetaB : ∀ j, j < n → ‖beta j‖ ≤ Bb)
    (hLam : 1 ≤ Lam) (hlgLam : ∀ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam)
    (hsumLam : ∑ r ∈ Finset.Icc 1 n, ‖lg r‖ ≤ Lam)
    (hlmin : 0 < lmin) (hlmin1 : lmin ≤ 1) (hlglmin : ∀ r ∈ Finset.Icc 1 n, lmin ≤ ‖lg r‖)
    (hnM : (n : ℝ) ≤ M) (hDM : ((∏ r ∈ V, d r : ℕ) : ℝ) ≤ M) (hLamM : Lam ≤ M)
    (hM : ∑ r ∈ Finset.Icc 1 n, Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤ M)
    (hllmin : Real.log lmin⁻¹ ≤ M)
    (hlq : 112 ≤ Real.log q)
    (hq1 : 2176 * M ^ 3 * 2 ^ bakerJ n (∏ r ∈ V, d r) ≤ (q : ℝ))
    (hq2 : ((bakerC (∏ r ∈ V, d r) * (n + 1) : ℕ) : ℝ) * (8 * M + 75) * (6 * M) ^ (n + 3) *
      2 ^ (bakerJ n (∏ r ∈ V, d r) + 1) ≤ (q : ℝ))
    (hh : 1 ≤ h) (hMh : M ≤ h)
    (hlk : Real.log (bakerKpar n (∏ r ∈ V, d r) q) ≤ h)
    (hlG : Real.log G ≤ h) (hlBb : Real.log Bb ≤ h) (hlGn : Real.log Gn ≤ h)
    (hsum : ∑ r ∈ V, (e r : ℝ) * Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3) ≤ h)
    (hdelta : ‖beta 0 + ∑ r ∈ Finset.Icc 1 (n - 1), beta r * lg r - lg n‖ ≤ d0)
    (hd0 : d0 ≤ Real.exp (-((q : ℝ) ^ (bakerE1 n (∏ r ∈ V, d r) + 1) * (h : ℝ)))) : False := by
  have hdr : ∀ r ∈ V, 1 ≤ d r ∧ 1 ≤ H r := fun r hr => ⟨(ha r hr).1, (ha r hr).2.1⟩
  have hD1 : 1 ≤ ∏ r ∈ V, d r :=
    Nat.succ_le_of_lt (Finset.prod_pos fun r hr => Nat.lt_of_lt_of_le Nat.zero_lt_one (ha r hr).1)
  set D := ∏ r ∈ V, d r with hDdef
  have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hM1 : 1 ≤ M := hD1'.trans hDM
  have hM0 : 0 ≤ M := by linarith
  have hJpow : (1 : ℝ) ≤ 2 ^ bakerJ n D := one_le_pow₀ (by norm_num)
  have hM3 : M ≤ M ^ 3 := by
    nlinarith [mul_nonneg hM0 (mul_nonneg (sub_nonneg.2 hM1) (by linarith : (0 : ℝ) ≤ M + 1))]
  have hMM3 : M * M ≤ M ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg hM0 hM0) (sub_nonneg.2 hM1)]
  have hM3J : M ^ 3 ≤ M ^ 3 * 2 ^ bakerJ n D := le_mul_of_one_le_right (by positivity) hJpow
  have hqr : 16 * (D : ℝ) + 16 ≤ q := by linarith
  have hq16D : 16 * D + 16 ≤ q := by exact_mod_cast hqr
  have hq16 : 16 ≤ q := by omega
  have hq8 : 8 * D + 8 ≤ q := by omega
  have hq6 : 6 * D ≤ q := by omega
  have hq2D : 2 * D ≤ q := by omega
  have hq1' : 1 ≤ q := by omega
  have hq0 : 0 < q := hq1'
  have hq4 : 4 ≤ q := by omega
  have hq16' : (16 : ℝ) ≤ q := by exact_mod_cast hq16
  have hLam2 : 2 * (D : ℝ) * Lam ≤ q := by
    have h1 : (D : ℝ) * Lam ≤ M * M := mul_le_mul hDM hLamM (by linarith) hM0
    linarith
  obtain ⟨hL1, hk1⟩ := baker_par_pos n D q hD1 hq1'
  have hLk := baker_l_le_k n D q hq1' hq2D
  have hcount := baker_siegel_num n D q hn hD1 hq1'
  have hd00 : 0 ≤ d0 := le_trans (norm_nonneg _) hdelta
  have hd01 : d0 ≤ 1 := hd0.trans (Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity)))
  obtain ⟨hU1, hUE, hRU, hkU, h5U, h2U, hkkU⟩ := baker_units n D q h hn hq16 hh
  have hlem7num := baker_lemma7_num M D n q h hn hD1 hDM hnM hh hq4 hlq hq1 hq2
  have hstepnum : ∀ K, K < bakerJ n D →
      bakerLu M (bakerLpar n D q) (bakerKpar n D q) h (4 * q ^ bakerA D * (h * q ^ (K + 1)) + 1) +
          bakerLw M D (bakerLpar n D q) (bakerKpar n D q) h (h * q ^ (K + 1)) + 3 ≤
        ((h * q ^ K : ℕ) : ℝ) * ((bakerKpar n D q / 2 ^ (K + 1) + 1 : ℕ) : ℝ) * (bakerA D : ℝ) *
          Real.log q := fun K hK => by
    apply baker_step_num M D n q h K hn hD1 hDM hh hq4 hlq
    have h1 : (2 : ℝ) ^ K ≤ 2 ^ bakerJ n D := pow_le_pow_right₀ (by norm_num) hK.le
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2176 * M ^ 3)
    linarith
  have hlogk : Real.log (bakerKpar n D q : ℝ) =
      ((bakerC D * (n + 1) : ℕ) : ℝ) * Real.log q := by
    rw [bakerKpar, Nat.cast_pow, Real.log_pow]
  have hlq0 : 0 ≤ Real.log q := by linarith
  have hE16 : 16 * ((q : ℝ) ^ bakerE1 n D * (h : ℝ)) ≤
      (q : ℝ) ^ (bakerE1 n D + 1) * (h : ℝ) := by
    have h1 : (q : ℝ) ^ (bakerE1 n D + 1) * (h : ℝ) =
        (q : ℝ) * ((q : ℝ) ^ bakerE1 n D * (h : ℝ)) := by rw [pow_succ]; ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right hq16' (by positivity)
  have hhU : (h : ℝ) ≤ (h : ℝ) * (q : ℝ) ^ (bakerC D * (n + 1) + bakerJ n D + 3) := by
    simpa using hRU 0 (Nat.zero_le _)
  have hZU : ∀ K m, K ≤ bakerJ n D →
      ((h * q ^ K : ℕ) : ℝ) * ((bakerKpar n D q / 2 ^ m + 1 : ℕ) : ℝ) * (bakerA D : ℝ) *
          Real.log q ≤
        (h : ℝ) * (q : ℝ) ^ (bakerC D * (n + 1) + bakerJ n D + 3) :=
    fun K m hK => baker_zbound D n q h K m hD1 hq8 hK
  -- abbreviations
  set L := bakerLpar n D q with hLdef
  set k := bakerKpar n D q with hkdef
  set J := bakerJ n D with hJdef
  set U : ℝ := (h : ℝ) * (q : ℝ) ^ (bakerC D * (n + 1) + J + 3) with hUdef
  set E : ℝ := (q : ℝ) ^ bakerE1 n D * (h : ℝ) with hEdef
  set lk : ℝ := ((bakerC D * (n + 1) : ℕ) : ℝ) * Real.log q with hlkdef
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hnU : (n : ℝ) ≤ U := by linarith
  obtain ⟨hP1, hlP⟩ := baker_pbound_log_le n h L k V G H e d M hn hh hL1 hLk hV hdr hG hnM hM hlG
    hlk hsum
  set P := bakerPbound n h L k V G H e with hPdef
  have hub0 : ∀ N, 0 < bakerUb n h L k P Bb Lam N := fun N => by
    rw [bakerUb]; exact mul_pos (by linarith) (Real.exp_pos _)
  have hub : ∀ N, bakerUb n h L k P Bb Lam N ≤ Real.exp (bakerLu M L k h N) := fun N =>
    (Real.le_exp_log _).trans (Real.exp_le_exp.2
      (baker_ub_log_le n h L k P Bb Lam N M hn hh hL1 hLk hP1 hBb hLam hLamM hnM hMh hlk hlBb hlP))
  have hlu0 : ∀ N, 0 ≤ bakerLu M L k h N := fun N => by rw [bakerLu]; positivity
  have hlw0 : ∀ R, 0 ≤ bakerLw M D L k h R := fun R => baker_lw_pos M D L k h R hM0 hh
  have hlk0 : 0 ≤ lk := by rw [hlkdef]; positivity
  have hl70 : 0 ≤ bakerL7 M D n L k h (h * (L + 2) ^ (n + 1)) (h * (L + 2) * (L + 1) ^ n) lk := by
    rw [bakerL7]; positivity
  have hT60 : 0 ≤ 6 * (h : ℝ) * (L : ℝ) * lk := by positivity
  have hZJ := hZU J J le_rfl
  have hRK : ∀ K, h ≤ h * q ^ K := fun K => Nat.le_mul_of_pos_right _ (pow_pos hq0 _)
  have hRK1 : ∀ K, 1 ≤ h * q ^ K := fun K => hh.trans (hRK K)
  have hqa : 0 < 4 * q ^ bakerA D := Nat.mul_pos (by norm_num) (pow_pos hq0 _)
  -- the error term is at most `eps`
  have herrN : ∀ N, N ≤ h * q ^ J + 1 → bakerErr n h L k P Bb Lam d0 N ≤ Real.exp (-E) := by
    intro N hN
    have hluN : bakerLu M L k h N ≤ U := by
      have hNN : (N : ℝ) ≤ ((4 * q ^ bakerA D * (h * q ^ J) + 1 : ℕ) : ℝ) := by
        exact_mod_cast hN.trans (Nat.add_le_add_right (Nat.le_mul_of_pos_left _ hqa) 1)
      have h1 : bakerLu M L k h N ≤ bakerLu M L k h (4 * q ^ bakerA D * (h * q ^ J) + 1) := by
        rw [bakerLu, bakerLu]
        have h2 := mul_le_mul_of_nonneg_left hNN (by positivity : (0 : ℝ) ≤ (M + 4) * (L : ℝ))
        linarith
      linarith
    have hNL : (N : ℝ) * (L : ℝ) ≤ U := by
      have h1 : (N : ℝ) ≤ 2 * ((h * q ^ J : ℕ) : ℝ) := by
        exact_mod_cast (by have := hRK1 J; omega : N ≤ 2 * (h * q ^ J))
      have h2 : (L : ℝ) ≤ k := by exact_mod_cast hLk
      exact (mul_le_mul h1 h2 (by positivity) (by positivity)).trans h2U
    exact param_err_bound _ _ ((N : ℝ) * (L : ℝ)) d0 U E _ (hub0 N).le hd00
      (fun h1 => baker_err_le_ub n h L k P Bb Lam d0 N (by linarith) hd00 h1)
      ((hub N).trans (Real.exp_le_exp.2 hluN)) hNL hU1 hUE hE16 hd0
  have herr0 : bakerErr n h L k P Bb Lam d0 (h + 1) ≤ Real.exp (-E) :=
    herrN _ (Nat.add_le_add_right (hRK J) 1)
  have herr : ∀ K, K < J → bakerErr n h L k P Bb Lam d0 (h * q ^ (K + 1) + 1) ≤ Real.exp (-E) :=
    fun K hK => herrN _ (Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq1' hK)) 1)
  have hlwU : ∀ K, K < J → bakerLw M D L k h (h * q ^ (K + 1)) ≤ U := fun K hK => by
    have h1 := hstepnum K hK
    have h2 := hlu0 (4 * q ^ bakerA D * (h * q ^ (K + 1)) + 1)
    have h3 := hZU K (K + 1) hK.le
    linarith
  -- the gap of the dichotomy
  have hvb : ∀ K, K < J → Real.exp (-(bakerLw M D L k h (h * q ^ (K + 1)))) / 2 ≤
      bakerVb n h L k V G H e d P Bb Lam d0 lmin Gn (h * q ^ (K + 1)) := by
    intro K hK
    have h1 : Real.exp (-(bakerLw M D L k h (h * q ^ (K + 1)))) ≤
        lmin ^ k * bakerLiou5 n h L k V G H e d P (h * q ^ (K + 1)) /
          (bakerNmax h (h * q ^ (K + 1)) ^ k * Gn ^ k) :=
      baker_liou5_exp_lower n h L k V G H e d P Gn lmin (h * q ^ (K + 1)) M hn hh (hRK _)
        hL1 hLk hV hdr hG hP1 hGn1 hlmin hlmin1 hnM hDM hM hllmin hMh hlG hlk hlGn hsum hlP
    have h2 := herr K hK
    have h3 := hlwU K hK
    have h4 : Real.exp (-E) ≤ Real.exp (-(bakerLw M D L k h (h * q ^ (K + 1)))) / 2 := by
      calc Real.exp (-E) ≤ Real.exp (-(bakerLw M D L k h (h * q ^ (K + 1))) + -1) :=
            Real.exp_le_exp.2 (by linarith)
        _ = Real.exp (-(bakerLw M D L k h (h * q ^ (K + 1)))) * Real.exp (-1) :=
            Real.exp_add _ _
        _ ≤ Real.exp (-(bakerLw M D L k h (h * q ^ (K + 1)))) * (1 / 2) :=
            mul_le_mul_of_nonneg_left param_exp_neg_one_le (Real.exp_pos _).le
        _ = Real.exp (-(bakerLw M D L k h (h * q ^ (K + 1)))) / 2 := by ring
    rw [bakerVb]
    linarith
  have hvbpos : ∀ K, K < J →
      0 < bakerVb n h L k V G H e d P Bb Lam d0 lmin Gn (h * q ^ (K + 1)) := fun K hK =>
    lt_of_lt_of_le (by positivity) (hvb K hK)
  -- the extrapolation steps
  have hstep : ∀ K, K < J →
      2 * bakerUb n h L k P Bb Lam (4 * q ^ bakerA D * (h * q ^ (K + 1)) + 1) *
          (4 * ((h * q ^ (K + 1) : ℕ) : ℝ) / ((4 * q ^ bakerA D * (h * q ^ (K + 1)) : ℕ) : ℝ)) ^
            (h * q ^ K * (k / 2 ^ (K + 1) + 1)) +
        Real.exp (-E) * 2 * ((h * q ^ K : ℕ) : ℝ) * 2 ^ (k / 2 ^ (K + 1)) * Real.exp n *
          (((h * q ^ (K + 1) : ℕ) : ℝ) * 16 ^ (h * q ^ (K + 1))) ^ (k / 2 ^ (K + 1) + 1) ≤
        bakerVb n h L k V G H e d P Bb Lam d0 lmin Gn (h * q ^ (K + 1)) / 2 := by
    intro K hK
    refine param_step_assemble _ _ (bakerLw M D L k h (h * q ^ (K + 1))) _ E _ _ (h * q ^ K)
      (h * q ^ (K + 1)) (k / 2 ^ (K + 1)) n _ (hub _) (hstepnum K hK) ?_ (hvb K hK) ?_
    · rw [param_ratio q (bakerA D) _ (hRK1 _) hq1', param_inv_pow_exp q _ _ hq1']
      congr 1; push_cast; ring
    · have h1 := hRU K hK.le
      have h2 : ((k / 2 ^ (K + 1) : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.div_le_self _ _
      have h3 : ((h * q ^ (K + 1) : ℕ) : ℝ) ≤ ((h * q ^ J : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq1' hK)
      have h4 : 5 * ((h * q ^ (K + 1) : ℕ) : ℝ) * (((k / 2 ^ (K + 1) : ℕ) : ℝ) + 1) ≤ U :=
        le_trans (mul_le_mul (mul_le_mul_of_nonneg_left h3 (by norm_num)) (by linarith)
          (by positivity) (by positivity)) h5U
      have h5 := hlwU K hK
      linarith
  -- Lemma 7
  have hX7R : h * (L + 2) ^ (n + 1) ≤ h * q ^ J := baker_x7_le_r n D q h hn hD1 hq6
  have hX7h : h ≤ h * (L + 2) ^ (n + 1) := Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
  have hlem7 : (k : ℝ) ^ (2 * h * (L + 2)) *
      (2 * bakerUb n h L k P Bb Lam (4 * q ^ bakerA D * (h * q ^ J) + 1) *
          (4 * ((h * q ^ J : ℕ) : ℝ) / ((4 * q ^ bakerA D * (h * q ^ J) : ℕ) : ℝ)) ^
            (h * q ^ J * (k / 2 ^ J + 1)) +
        Real.exp (-E) * 2 * (k : ℝ) * ((h * q ^ J : ℕ) : ℝ) * (2 * (k : ℝ)) ^ (k / 2 ^ J) *
          Real.exp n * (((h * q ^ J : ℕ) : ℝ) * 16 ^ (h * q ^ J)) ^ (k / 2 ^ J + 1) +
        bakerErr n h L k P Bb Lam d0 (h * (L + 2) ^ (n + 1) + 1)) <
      bakerLiou7 n h L k d H P (h * (L + 2) ^ (n + 1)) (h * (L + 2) * (L + 1) ^ n) := by
    have hliou : Real.exp (-(bakerL7 M D n L k h (h * (L + 2) ^ (n + 1))
        (h * (L + 2) * (L + 1) ^ n) lk)) ≤
        bakerLiou7 n h L k d H P (h * (L + 2) ^ (n + 1)) (h * (L + 2) * (L + 1) ^ n) :=
      baker_liou7_exp_lower n h L k d H P (h * (L + 2) ^ (n + 1)) (h * (L + 2) * (L + 1) ^ n) lk
        V M hn hh hX7h hL1 hLk hV hdr hP1 hnM hDM hM hMh hlk (le_of_eq hlogk) hlP
    refine param_lem7_assemble _ _ _ (6 * (h : ℝ) * (L : ℝ) * lk) _ E _ _ _ _ k (h * q ^ J)
      (k / 2 ^ J) n _ (hub _) hlem7num ?_ (by positivity) ?_ ?_
      (herrN _ (Nat.add_le_add_right hX7R 1)) hliou
    · rw [param_ratio q (bakerA D) _ (hRK1 _) hq1', param_inv_pow_exp q _ _ hq1']
      congr 1; push_cast; ring
    · have h1 := param_kpow_le k h L hk1 hL1
      rw [hlogk] at h1; exact h1
    · have h1 := hRU J le_rfl
      have h2 : ((k / 2 ^ J : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.div_le_self _ _
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have h3 : ((k / 2 ^ J : ℕ) : ℝ) * (1 + (k : ℝ)) ≤ U :=
        le_trans (mul_le_mul_of_nonneg_right h2 (by linarith)) hkkU
      have h4 : 5 * ((h * q ^ J : ℕ) : ℝ) * (((k / 2 ^ J : ℕ) : ℝ) + 1) ≤ U :=
        le_trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) h5U
      have h5 := hlu0 (4 * q ^ bakerA D * (h * q ^ J) + 1)
      linarith
  -- the remaining simple conditions
  have hX7 : h * (L + 2) * (L + 1) ^ n ≤ k * (h * (L + 2) ^ (n + 1)) :=
    calc h * (L + 2) * (L + 1) ^ n ≤ h * (L + 2) * (L + 2) ^ n :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = h * (L + 2) ^ (n + 1) := by ring
      _ ≤ k * (h * (L + 2) ^ (n + 1)) := Nat.le_mul_of_pos_left _ hk1
  have hLLam : (L : ℝ) * Lam < 2 * Real.pi * (k : ℝ) :=
    baker_llam_lt n D q Lam hq1' (by linarith) hLam2
  exact baker_core_parametric n lg theta V g e G a d H beta h L k (fun K => h * q ^ K)
    (fun K => k / 2 ^ K) (fun K => 4 * q ^ bakerA D * (h * q ^ (K + 1))) J
    (h * (L + 2) ^ (n + 1)) (4 * q ^ bakerA D * (h * q ^ J)) (Real.exp (-E)) Bb Lam d0 lmin Gn
    hn hL1 hLk hh hG hV htheta hg hgn hGn hGn1 hbeta ha hind hBb hbetaB hLam hlgLam hsumLam
    hlmin hlmin1 hlglmin hd00 hd01 hdelta hcount herr0 (by simp) (by simp)
    (fun K _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq1' (Nat.le_succ K)))
    (fun K _ => baker_s_half k K)
    (fun K _ => Nat.le_of_eq (by ring) |>.trans (Nat.mul_le_mul_right _
      (Nat.le_mul_of_pos_right 4 (pow_pos hq0 (bakerA D)))))
    herr hvbpos hstep hX7 hX7R
    (Nat.le_of_eq (by ring) |>.trans (Nat.mul_le_mul_right _
      (Nat.le_mul_of_pos_right 4 (pow_pos hq0 (bakerA D)))))
    hlem7 hLLam

end RiemannMasullo.Baker
