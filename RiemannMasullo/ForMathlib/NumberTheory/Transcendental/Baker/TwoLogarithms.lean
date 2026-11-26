module

public import Mathlib.NumberTheory.Transcendental.Liouville.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.Explicit

/-! # The ratio of two independent integer logarithms is not a Liouville number

An application of the core lower bound `baker_core_exists` (ported from HOL Light,
Baker/explicit.ml, jrh13/hol-light, commit 1a0c0e6) to the two logarithms `log q`, `log p` of
multiplicatively independent integers `1 < p < q`, with the two integer coefficients of the
linear form as extra algebraic coordinates of degree one: there is `C` with
`(B ^ C)⁻¹ ≤ |b * log p - a * log q|` for all integers `|a|, |b| ≤ B`, `b ≠ 0`. Hence
`log p / log q` is not a Liouville number. -/

@[expose] public section

namespace RiemannMasullo.Baker

/-- For multiplicatively independent integers `p, q > 1` the logarithms `log q`, `log p` have no
nontrivial integer relation. -/
private theorem twolog_rel (p q : ℕ) (hp : 1 < p) (hq : 1 < q)
    (hind : ¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ p ^ k = q ^ l) (u v : ℤ)
    (h : (u : ℝ) * Real.log q + (v : ℝ) * Real.log p = 0) : u = 0 ∧ v = 0 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have h1 : (v : ℝ) * Real.log p = -((u : ℝ) * Real.log q) := by linarith
  have h2 : |(v : ℝ)| * Real.log p = |(u : ℝ)| * Real.log q := by
    have h3 := congrArg abs h1
    rwa [abs_neg, abs_mul, abs_mul, abs_of_pos hlp, abs_of_pos hlq] at h3
  have habs : (v.natAbs : ℝ) * Real.log p = (u.natAbs : ℝ) * Real.log q := by
    rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
    exact h2
  have hpow : p ^ v.natAbs = q ^ u.natAbs := by
    have h3 : Real.log ((p : ℝ) ^ v.natAbs) = Real.log ((q : ℝ) ^ u.natAbs) := by
      rw [Real.log_pow, Real.log_pow]
      exact habs
    have h4 := Real.log_injOn_pos (Set.mem_Ioi.2 (pow_pos hp0 _)) (Set.mem_Ioi.2 (pow_pos hq0 _)) h3
    exact_mod_cast h4
  rcases Nat.eq_zero_or_pos v.natAbs with hv | hv
  · have hv0 : v = 0 := Int.natAbs_eq_zero.mp hv
    have h3 : (u : ℝ) * Real.log q = 0 := by
      rw [hv0] at h
      simpa using h
    have hu0 : (u : ℝ) = 0 := (mul_eq_zero.mp h3).resolve_right hlq.ne'
    exact ⟨by exact_mod_cast hu0, hv0⟩
  · rcases Nat.eq_zero_or_pos u.natAbs with hu | hu
    · have hu0 : u = 0 := Int.natAbs_eq_zero.mp hu
      have h3 : (v : ℝ) * Real.log p = 0 := by
        rw [hu0] at h
        simpa using h
      have hv0 : (v : ℝ) = 0 := (mul_eq_zero.mp h3).resolve_right hlp.ne'
      exact ⟨hu0, by exact_mod_cast hv0⟩
    · exact absurd ⟨_, _, hv, hu, hpow⟩ hind

private theorem twolog_Icc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by
  ext r
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Baker's lower bound for linear forms in the logarithms of two multiplicatively independent
integers `1 < p < q`: there is `C` with `(B ^ C)⁻¹ ≤ |b * log p - a * log q|` for all integers
`a`, `b` of absolute value at most `B`, `B ≥ 2`, with `b ≠ 0`. -/
theorem baker_two_logarithms (p q : ℕ) (hp : 1 < p) (hpq : p < q)
    (hind : ¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ p ^ k = q ^ l) :
    ∃ C : ℕ, ∀ (B : ℝ) (a b : ℤ), 2 ≤ B → |(a : ℝ)| ≤ B → |(b : ℝ)| ≤ B → b ≠ 0 →
      (B ^ C)⁻¹ ≤ |(b : ℝ) * Real.log p - (a : ℝ) * Real.log q| := by
  have hq : 1 < q := hp.trans hpq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq.le
  obtain ⟨lg, hlg1, hlg2⟩ : ∃ lg : ℕ → ℂ, lg 1 = (Real.log q : ℂ) ∧ lg 2 = (Real.log p : ℂ) :=
    ⟨fun r => if r = 1 then (Real.log q : ℂ) else (Real.log p : ℂ), by simp, by simp⟩
  obtain ⟨c, hc10, hc11, hc20, hc21, hcb⟩ : ∃ c : ℕ → ℕ → ℤ, c 1 0 = -(q : ℤ) ∧ c 1 1 = 1 ∧
      c 2 0 = -(p : ℤ) ∧ c 2 1 = 1 ∧ ∀ r j, |(c r j : ℝ)| ≤ q := by
    refine ⟨fun r j => if j = 0 then (if r = 1 then -(q : ℤ) else -(p : ℤ))
      else if j = 1 then 1 else 0, by simp, by simp, by simp, by simp, fun r j => ?_⟩
    by_cases hj : j = 0
    · by_cases hr : r = 1
      · simp [hj, hr]
      · simpa [hj, hr] using hpqR
    · by_cases hj1 : j = 1
      · simpa [hj1] using hq1
      · simp [hj, hj1]
  have hexpq : Complex.exp (Real.log q : ℂ) = (q : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hq0, Complex.ofReal_natCast]
  have hexpp : Complex.exp (Real.log p : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hp0, Complex.ofReal_natCast]
  have hmem : ∀ r ∈ Finset.Icc 1 2, r = 1 ∨ r = 2 := fun r hr => by
    have h1 := Finset.mem_Icc.mp hr
    omega
  have ha : ∀ r ∈ Finset.Icc 1 2, 1 ≤ 1 ∧ (1 : ℝ) ≤ q ∧ (∀ j, |(c r j : ℝ)| ≤ q) ∧
      c r 1 ≠ 0 ∧ ∑ j ∈ Finset.range (1 + 1), (c r j : ℂ) * Complex.exp (lg r) ^ j = 0 := by
    intro r hr
    rcases hmem r hr with rfl | rfl
    · refine ⟨le_rfl, hq1, hcb 1, by rw [hc11]; exact one_ne_zero, ?_⟩
      rw [Finset.sum_range_succ, Finset.sum_range_one, hc10, hc11, hlg1, hexpq]
      push_cast
      ring
    · refine ⟨le_rfl, hq1, hcb 2, by rw [hc21]; exact one_ne_zero, ?_⟩
      rw [Finset.sum_range_succ, Finset.sum_range_one, hc20, hc21, hlg2, hexpp]
      push_cast
      ring
  have hrel : ∀ b : ℕ → ℤ, ∑ r ∈ Finset.Icc 1 2, (b r : ℂ) * lg r = 0 →
      ∀ r ∈ Finset.Icc 1 2, b r = 0 := by
    intro b hb r hr
    rw [twolog_Icc, Finset.sum_pair (by norm_num), hlg1, hlg2] at hb
    have hb' : ((b 1 : ℤ) : ℝ) * Real.log q + ((b 2 : ℤ) : ℝ) * Real.log p = 0 := by
      exact_mod_cast hb
    obtain ⟨h1, h2⟩ := twolog_rel p q hp hq hind (b 1) (b 2) hb'
    rcases hmem r hr with rfl | rfl
    · exact h1
    · exact h2
  obtain ⟨C, hC⟩ := baker_core_exists 2 2 lg c (fun _ => 1) (fun _ => (q : ℝ)) (fun _ => 1) 1 1
    (by norm_num) le_rfl le_rfl ha hrel
  refine ⟨C, fun B a b hB haB hbB hb0 => ?_⟩
  obtain ⟨theta, hth1, hth2, hth3, hth4⟩ : ∃ theta : ℕ → ℂ, theta 1 = (q : ℂ) ∧
      theta 2 = (p : ℂ) ∧ theta 3 = -(a : ℂ) ∧ theta 4 = (b : ℂ) :=
    ⟨fun r => if r = 1 then (q : ℂ) else if r = 2 then (p : ℂ) else if r = 3 then -(a : ℂ)
      else (b : ℂ), by simp, by simp, by simp, by simp⟩
  obtain ⟨g, hg0, hg1, hg2⟩ : ∃ g : ℕ → (ℕ → ℂ) → ℂ, g 0 = (fun _ => ((0 : ℤ) : ℂ)) ∧
      g 1 = (fun x => x 3) ∧ g 2 = (fun x => x 4) :=
    ⟨fun j => if j = 0 then (fun _ => ((0 : ℤ) : ℂ)) else if j = 1 then (fun x => x 3)
      else (fun x => x 4), by simp, by simp, by simp⟩
  have hB0 : 0 ≤ B := by linarith
  obtain ⟨ax, hax30, hax31, hax40, hax41, haxb⟩ : ∃ ax : ℕ → ℕ → ℤ, ax 3 0 = a ∧ ax 3 1 = 1 ∧
      ax 4 0 = -b ∧ ax 4 1 = 1 ∧ ∀ r j, |(ax r j : ℝ)| ≤ B := by
    refine ⟨fun r j => if j = 0 then (if r = 3 then a else -b)
      else if j = 1 then 1 else 0, by simp, by simp, by simp, by simp, fun r j => ?_⟩
    by_cases hj : j = 0
    · by_cases hr : r = 3
      · simpa [hj, hr] using haB
      · simpa [hj, hr] using hbB
    · by_cases hj1 : j = 1
      · simpa [hj1] using (show (1 : ℝ) ≤ B by linarith)
      · simpa [hj, hj1] using hB0
  have hmain := hC B theta g (fun _ => 1) ax hB
    (fun r hr => by
      rcases hmem r hr with rfl | rfl
      · rw [hth1, hlg1, hexpq]
      · rw [hth2, hlg2, hexpp])
    (fun r hr => by
      have h1 := Finset.mem_Icc.mp hr
      have h2 : r = 3 ∨ r = 4 := by omega
      rcases h2 with rfl | rfl
      · refine ⟨le_rfl, le_rfl, haxb 3, by rw [hax31]; exact one_ne_zero, ?_⟩
        rw [Finset.sum_range_succ, Finset.sum_range_one, hax30, hax31, hth3]
        push_cast
        ring
      · refine ⟨le_rfl, le_rfl, haxb 4, by rw [hax41]; exact one_ne_zero, ?_⟩
        rw [Finset.sum_range_succ, Finset.sum_range_one, hax40, hax41, hth4]
        push_cast
        ring)
    (fun j hj => by
      have h2 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases h2 with rfl | rfl | rfl
      · rw [hg0]
        exact intpoly_const _ _ 0 (by simp)
      · rw [hg1]
        exact intpoly_var (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩) le_rfl le_rfl
      · rw [hg2]
        exact intpoly_var (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩) le_rfl le_rfl)
    (by
      rw [hg2]
      simp only [hth4]
      exact_mod_cast hb0)
  have hval : g 0 theta + ∑ r ∈ Finset.Icc 1 2, g r theta * lg r =
      (((b : ℝ) * Real.log p - (a : ℝ) * Real.log q : ℝ) : ℂ) := by
    rw [twolog_Icc, Finset.sum_pair (by norm_num), hg0, hg1, hg2, hlg1, hlg2]
    simp only [hth3, hth4]
    push_cast
    ring
  rwa [hval, Complex.norm_real, Real.norm_eq_abs] at hmain

/-- For multiplicatively independent integers `1 < p < q`, the ratio of their real logarithms
is not a Liouville number. -/
theorem not_liouville_log_div_log_of_independent (p q : ℕ)
    (hp : 1 < p) (hpq : p < q) (hind : ¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ p ^ k = q ^ l) :
    ¬ Liouville (Real.log p / Real.log q) := by
  intro hLiou
  obtain ⟨C, hC⟩ := baker_two_logarithms p q hp hpq hind
  have hq1 : 1 < q := hp.trans hpq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq1)
  have hlpq : Real.log p < Real.log q :=
    Real.log_lt_log (by exact_mod_cast (by omega : 0 < p)) (by exact_mod_cast hpq)
  obtain ⟨a, b, hb, -, hlt⟩ := hLiou (2 * C + 1 + q)
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.log p / Real.log q := ⟨_, rfl⟩
  rw [← hx] at hlt
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hx1 : x < 1 := by rw [hx]; exact (div_lt_one hlq).2 hlpq
  have hx0 : 0 < x := by rw [hx]; exact div_pos hlp hlq
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = |x - (a : ℝ) / (b : ℝ)| := ⟨_, rfl⟩
  rw [← ht] at hlt
  have ht0 : 0 ≤ t := by rw [ht]; exact abs_nonneg _
  have hkey : (b : ℝ) * Real.log p - (a : ℝ) * Real.log q =
      Real.log q * (b : ℝ) * (x - (a : ℝ) / (b : ℝ)) := by
    rw [hx]
    field_simp
  have hbx : (b : ℝ) * x - (a : ℝ) = (b : ℝ) * (x - (a : ℝ) / (b : ℝ)) := by
    field_simp
  have hpowpos : (0 : ℝ) < (b : ℝ) ^ (2 * C + 1 + q) := pow_pos hb0 _
  have hlt' : t * (b : ℝ) ^ (2 * C + 1 + q) < 1 := by
    rwa [lt_div_iff₀ hpowpos] at hlt
  have htb : (b : ℝ) * t < 1 := by
    have h1 : (b : ℝ) ≤ (b : ℝ) ^ (2 * C + 1 + q) := le_self_pow₀ hbR.le (by omega)
    have h2 := mul_le_mul_of_nonneg_left h1 ht0
    linarith
  have ha : |(a : ℝ)| ≤ 2 * (b : ℝ) := by
    have h1 : |(b : ℝ) * x - (a : ℝ)| < 1 := by
      rw [hbx, abs_mul, abs_of_pos hb0, ← ht]
      exact htb
    rw [abs_lt] at h1
    have h2 : (b : ℝ) * x < (b : ℝ) := by
      have h3 := mul_lt_mul_of_pos_left hx1 hb0
      linarith
    have h3 : 0 < (b : ℝ) * x := mul_pos hb0 hx0
    rw [abs_le]
    constructor <;> linarith
  have hbne : b ≠ 0 := by omega
  have hB := hC (2 * (b : ℝ)) a b (by linarith) ha (by rw [abs_of_pos hb0]; linarith) hbne
  rw [hkey, abs_mul, abs_mul, abs_of_pos hlq, abs_of_pos hb0, ← ht] at hB
  have hWpos : 0 < (2 * (b : ℝ)) ^ C := pow_pos (by linarith) _
  have hB' : 1 ≤ (2 * (b : ℝ)) ^ C * (Real.log q * (b : ℝ) * t) := by
    have h1 := mul_le_mul_of_nonneg_left hB hWpos.le
    rwa [mul_inv_cancel₀ hWpos.ne'] at h1
  have hlogq : Real.log q ≤ (2 : ℝ) ^ q :=
    (log_le_self _ hq0).trans (by exact_mod_cast Nat.lt_two_pow_self.le)
  have h2C : (2 : ℝ) ^ C ≤ (b : ℝ) ^ C := pow_le_pow_left₀ (by norm_num) hb2 C
  have h2q : (2 : ℝ) ^ q ≤ (b : ℝ) ^ q := pow_le_pow_left₀ (by norm_num) hb2 q
  have hbC : (0 : ℝ) < (b : ℝ) ^ C := pow_pos hb0 _
  have h6 : (2 * (b : ℝ)) ^ C * (Real.log q * (b : ℝ)) ≤ (b : ℝ) ^ (2 * C + 1 + q) := by
    have hpow : (b : ℝ) ^ (2 * C + 1 + q) =
        (b : ℝ) ^ C * (b : ℝ) * ((b : ℝ) ^ q * (b : ℝ) ^ C) := by ring
    have h1 : Real.log q * (2 : ℝ) ^ C ≤ (b : ℝ) ^ q * (b : ℝ) ^ C :=
      mul_le_mul (hlogq.trans h2q) h2C (by positivity) (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_pos hbC hb0).le
    rw [hpow, mul_pow]
    calc (2 : ℝ) ^ C * (b : ℝ) ^ C * (Real.log q * (b : ℝ))
        = (b : ℝ) ^ C * (b : ℝ) * (Real.log q * (2 : ℝ) ^ C) := by ring
      _ ≤ (b : ℝ) ^ C * (b : ℝ) * ((b : ℝ) ^ q * (b : ℝ) ^ C) := h2
  -- `N ≤ N * (W * t) = W * (t * N) < W ≤ N`
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (b : ℝ) ^ (2 * C + 1 + q) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (2 * (b : ℝ)) ^ C * (Real.log q * (b : ℝ)) := ⟨_, rfl⟩
  rw [← hN] at hlt' h6 hpowpos
  rw [← hW] at h6
  have hW0 : 0 < W := by rw [hW]; exact mul_pos hWpos (mul_pos hlq hb0)
  have hB'' : 1 ≤ W * t := by
    rw [hW]
    calc (1 : ℝ) ≤ (2 * (b : ℝ)) ^ C * (Real.log q * (b : ℝ) * t) := hB'
      _ = (2 * (b : ℝ)) ^ C * (Real.log q * (b : ℝ)) * t := by ring
  have h7 : N * 1 ≤ N * (W * t) := mul_le_mul_of_nonneg_left hB'' hpowpos.le
  have h8 : W * (t * N) < W * 1 := mul_lt_mul_of_pos_left hlt' hW0
  have h9 : N * (W * t) = W * (t * N) := by ring
  linarith

end RiemannMasullo.Baker
