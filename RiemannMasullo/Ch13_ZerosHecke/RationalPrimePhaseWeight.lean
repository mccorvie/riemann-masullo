module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Order.Round
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic

/-! # Lower bounds for the rational two-cosine prime weight

The quadratic irrationality of `√2` controls the simultaneous return of the two
cosines to one. This gives an explicit inverse bound at every rational prime.
-/

public noncomputable section

open Real

namespace RiemannMasullo

private theorem weight_round (x : ℝ) :
    8 * (x - (round x : ℝ)) ^ 2 ≤ 1 - Real.cos (2 * Real.pi * x) := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hr : |2 * Real.pi * (x - (round x : ℝ))| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos hp]
    have h := mul_le_mul_of_nonneg_left (abs_sub_round x) hp.le
    linarith
  have h := Real.cos_le_one_sub_mul_cos_sq hr
  rw [mul_sub, mul_comm (2 * Real.pi) (round x : ℝ), Real.cos_sub_int_mul_two_pi] at h
  have hq : 2 / Real.pi ^ 2 * (2 * Real.pi * x - (round x : ℝ) * (2 * Real.pi)) ^ 2 =
      8 * (x - (round x : ℝ)) ^ 2 := by
    field_simp
    ring
  linarith

private theorem weight_norm {m : ℤ} (hm : m ≠ 0) (n : ℤ) :
    (1 : ℝ) ≤ |(Real.sqrt 2 * m - n) * (Real.sqrt 2 * m + n)| := by
  have irr := irrational_sqrt_two.mul_intCast hm
  have hsub : Real.sqrt 2 * (m : ℝ) - n ≠ 0 := sub_ne_zero.mpr (irr.ne_int n)
  have hadd : Real.sqrt 2 * (m : ℝ) + n ≠ 0 := by
    simpa only [Int.cast_neg, sub_neg_eq_add] using sub_ne_zero.mpr (irr.ne_int (-n))
  have hid : (Real.sqrt 2 * (m : ℝ) - n) * (Real.sqrt 2 * m + n) =
      ((2*m^2-n^2 : ℤ) : ℝ) := by
    push_cast
    ring_nf
    simp [mul_comm]
  have hnz := mul_ne_zero hsub hadd
  rw [hid] at hnz ⊢
  have hz : (2*m^2-n^2 : ℤ) ≠ 0 := by
    exact_mod_cast hnz
  have hZ : 1 ≤ |2 * m ^ 2 - n ^ 2| := Int.add_one_le_iff.mpr (abs_pos.mpr hz)
  exact_mod_cast hZ

/-- Uniform arithmetic lower bound for the rational two-frequency prime weight. -/
theorem rationalTwoCosineWeight_diophantineLower {t : ℝ} (ht : 1 ≤ t) :
    1 / (4 * (1 + t)^2) ≤ 2 - Real.cos t - Real.cos (Real.sqrt 2 * t) := by
  let x := t / (2 * Real.pi)
  let m := round x
  let n := round (Real.sqrt 2 * x)
  have hπ : 0 < 2 * Real.pi := by positivity
  have ht₀ : 0 < t := by linarith
  have hx₀ : 0 ≤ x := by dsimp [x]; positivity
  have he : 2 * Real.pi * x = t := by dsimp [x]; field_simp
  have he₂ : 2 * Real.pi * (Real.sqrt 2 * x) = Real.sqrt 2 * t := by rw [← he]; ring
  have h₁ := weight_round x
  have h₂ := weight_round (Real.sqrt 2 * x)
  rw [he] at h₁
  rw [he₂] at h₂
  change 8 * (x - (m : ℝ))^2 ≤ _ at h₁
  change 8 * (Real.sqrt 2 * x - (n : ℝ))^2 ≤ _ at h₂
  have hs : Real.sqrt 2 ≤ 2 := by norm_num
  by_cases hm : m = 0
  · rw [hm] at h₁
    simp only [Int.cast_zero, sub_zero] at h₁
    have ht8 : t ≤ 8*x := he ▸ mul_le_mul_of_nonneg_right
      (by linarith [Real.pi_lt_four] : 2 * Real.pi ≤ 8) hx₀
    have hx8 : (1/8 : ℝ) ≤ x := by linarith
    have hlo : (1/16 : ℝ) ≤ 8*x^2 := by
      nlinarith [pow_le_pow_left₀ (by norm_num) hx8 2]
    have hcoef : 1 / (4 * (1+t)^2) ≤ (1/16 : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (t-1)]
    linarith [Real.cos_le_one (Real.sqrt 2 * t)]
  · have hx4 : x ≤ t / 4 := by
      have h := mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three] : 4 ≤ 2*Real.pi) hx₀
      linarith
    have hmabs : |(m : ℝ)| ≤ x+1/2 := by
      obtain ⟨h,h'⟩ := abs_le.mp (abs_sub_round x)
      exact abs_le.mpr ⟨by change -(x+1/2) ≤ (round x : ℝ); linarith,
        by change (round x : ℝ) ≤ x+1/2; linarith⟩
    have hnabs : |(n : ℝ)| ≤ Real.sqrt 2*x+1/2 := by
      have h₀ : 0 ≤ Real.sqrt 2*x := by positivity
      obtain ⟨h,h'⟩ := abs_le.mp (abs_sub_round (Real.sqrt 2*x))
      change |(round (Real.sqrt 2*x) : ℝ)| ≤ _
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hsize : |Real.sqrt 2 * (m : ℝ) + n| ≤ 2*(1+t) := by
      calc
        _ ≤ |Real.sqrt 2 * (m : ℝ)| + |(n : ℝ)| := abs_add_le _ _
        _ ≤ 2 * (x+1/2) + (Real.sqrt 2*x+1/2) := by
          rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
          exact add_le_add (mul_le_mul hs hmabs (abs_nonneg _) (by norm_num)) hnabs
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hs hx₀]
    have hz := weight_norm hm n
    rw [abs_mul] at hz
    have hgap : 1 / (2*(1+t)) ≤ |Real.sqrt 2 * (m : ℝ) - n| := by
      rw [div_le_iff₀ (by positivity)]
      exact hz.trans (mul_le_mul_of_nonneg_left hsize (abs_nonneg _))
    have hc (a b : ℝ) : (b - Real.sqrt 2*a)^2 ≤ 3*(a^2+b^2) := by
      have hh : 3*(a^2+b^2) - (b-Real.sqrt 2*a)^2 = (a+Real.sqrt 2*b)^2 := by
        ring_nf
        simp
        ring
      linarith [sq_nonneg (a+Real.sqrt 2*b)]
    have h := hc (x-(m:ℝ)) (Real.sqrt 2*x-(n:ℝ))
    rw [show Real.sqrt 2*x-(n:ℝ)-Real.sqrt 2*(x-(m:ℝ)) =
      Real.sqrt 2*(m:ℝ)-n by ring] at h
    have hsquare := pow_le_pow_left₀ (by positivity) hgap 2
    rw [sq_abs] at hsquare
    have hden : 1 / (4*(1+t)^2) = (1/(2*(1+t)))^2 := by
      rw [div_pow, mul_pow]
      norm_num
    rw [hden]
    nlinarith [sq_nonneg (x-(m:ℝ)), sq_nonneg (Real.sqrt 2*x-(n:ℝ))]

/-- Every rational prime retains a positive fraction of its logarithmic weight. -/
theorem rationalTwoCosineWeight_primeLower {p : ℕ} (hp : p.Prime) :
    1 / (4 * (1 + Real.log p)^2) ≤
      2 - Real.cos (Real.log p) - Real.cos (Real.sqrt 2 * Real.log p) := by
  by_cases ht : 1 ≤ Real.log p
  · exact rationalTwoCosineWeight_diophantineLower ht
  have hl : (2/3 : ℝ) ≤ Real.log p :=
    (by linarith [Real.log_two_gt_d9] : (2/3 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le))
  have h₂ : 0 ≤ Real.sqrt 2 * Real.log p := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hu : |Real.sqrt 2 * Real.log p| ≤ Real.pi := by
    rw [abs_of_nonneg h₂]
    nlinarith [mul_le_mul_of_nonneg_right (by norm_num : Real.sqrt 2 ≤ 2) (by linarith : 0 ≤ Real.log p),
      Real.pi_gt_three]
  have hcos := Real.cos_le_one_sub_mul_cos_sq hu
  have hdπ : (1/8 : ℝ) ≤ 2 / Real.pi^2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [(pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le 2)]
  have hq := mul_le_mul_of_nonneg_right hdπ (sq_nonneg (Real.sqrt 2 * Real.log p))
  rw [mul_pow, Real.sq_sqrt (by norm_num)] at hq
  rw [mul_pow, Real.sq_sqrt (by norm_num)] at hcos
  have hlo : (1/9 : ℝ) ≤ 1-Real.cos (Real.sqrt 2 * Real.log p) := by
    nlinarith [pow_le_pow_left₀ (by norm_num) hl 2]
  have hden : 1/(4*(1+Real.log p)^2) ≤ (1/9 : ℝ) := by
    have hlog₀ : 0 ≤ Real.log p := by linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Real.log p)]
  linarith [Real.cos_le_one (Real.log p)]

/-- At every scale a simultaneous return has the matching inverse-square order
throughout a neighborhood of radius `1 / (N + 1)`. -/
theorem rationalTwoCosineWeight_nearReturn (N : ℕ) (hN : 0 < N) :
    ∃ k : ℕ, 0 < k ∧ k ≤ N ∧ N ≤ 4*k ∧ ∀ u : ℝ, |u| ≤ 1 / ((N : ℝ)+1) →
      2 - Real.cos (2 * Real.pi * k + u) - Real.cos (Real.sqrt 2 * (2 * Real.pi * k + u))
        ≤ 51 / ((N : ℝ)+1)^2 := by
  obtain ⟨k, hk, hkN, he⟩ := Real.exists_nat_abs_mul_sub_round_le (Real.sqrt 2) hN
  let n := round ((k : ℝ) * Real.sqrt 2)
  let a := 1 / ((N : ℝ)+1)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha₁ : a ≤ 1 := by dsimp [a]; apply (div_le_iff₀ (by positivity)).mpr; simp
  have he' : |Real.sqrt 2 * k - n| ≤ a := by simpa only [mul_comm (Real.sqrt 2)] using he
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hn : |Real.sqrt 2 * k + n| ≤ 4*k+1 := by
    apply abs_le.mpr
    obtain ⟨hl, hr⟩ := abs_le.mp he'
    have hs := mul_le_mul_of_nonneg_right (by norm_num : Real.sqrt 2 ≤ 2) hk'.le
    have hpos : 0 ≤ Real.sqrt 2 * (k : ℝ) := by positivity
    constructor <;> linarith
  have hz := weight_norm (m := (k : ℤ)) (by exact_mod_cast hk.ne') n
  simp only [Int.cast_natCast, abs_mul] at hz
  have hprod := hz.trans (mul_le_mul he' hn (abs_nonneg _) ha.le)
  have hNk : N ≤ 4*k := by
    change (1 : ℝ) ≤ (1 / ((N : ℝ)+1)) * (4*k+1) at hprod
    field_simp at hprod
    exact_mod_cast (show (N:ℝ) ≤ 4*k by linarith)
  refine ⟨k, hk, hkN, hNk, ?_⟩
  intro u hu
  let v := 2 * Real.pi * (Real.sqrt 2 * k - n) + Real.sqrt 2 * u
  have hv : |v| ≤ 10*a := calc
    _ ≤ |2 * Real.pi * (Real.sqrt 2 * k - n)| + |Real.sqrt 2 * u| := abs_add_le _ _
    _ ≤ (2*Real.pi)*a + Real.sqrt 2*a := by
      rw [abs_mul (2*Real.pi), abs_mul (Real.sqrt 2) u, abs_of_pos (by positivity : 0 < 2*Real.pi),
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact add_le_add (mul_le_mul_of_nonneg_left he' (by positivity))
        (mul_le_mul_of_nonneg_left hu (by positivity))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right Real.pi_lt_four.le ha.le,
      mul_le_mul_of_nonneg_right (by norm_num : Real.sqrt 2 ≤ 2) ha.le]
  have hcos₁ : Real.cos (2 * Real.pi * k + u) = Real.cos u := by
    convert Real.cos_add_int_mul_two_pi u (k : ℤ) using 2
    push_cast
    ring
  have hcos₂ : Real.cos (Real.sqrt 2 * (2 * Real.pi * k + u)) = Real.cos v := by
    convert Real.cos_add_int_mul_two_pi v n using 2
    dsimp [v]
    ring
  rw [hcos₁, hcos₂]
  have hu₂ := pow_le_pow_left₀ (abs_nonneg u) hu 2
  have hv₂ := pow_le_pow_left₀ (abs_nonneg v) hv 2
  rw [sq_abs] at hu₂ hv₂
  change u^2 ≤ a^2 at hu₂
  have hc₁ := Real.one_sub_sq_div_two_le_cos (x := u)
  have hc₂ := Real.one_sub_sq_div_two_le_cos (x := v)
  have hid : 51/((N:ℝ)+1)^2 = 51*a^2 := by dsimp [a]; rw [div_pow]; ring
  rw [hid]
  nlinarith [sq_nonneg a]

/-- The two-cosine weight controls every finite nonnegative prime sum, with
a loss quadratic in the logarithm of the cutoff. -/
theorem rationalTwoCosineWeight_primeSum_lower (N : ℕ) (a : ℕ → ℝ)
    (ha : ∀ p ∈ Nat.primesLE N, 0 ≤ a p) :
    ∑ p ∈ Nat.primesLE N, a p ≤ 4 * (1 + Real.log N)^2 *
      ∑ p ∈ Nat.primesLE N, a p * (2 - Real.cos (Real.log p) -
        Real.cos (Real.sqrt 2 * Real.log p)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp ↦ ?_
  obtain ⟨hpN, hprime⟩ := Nat.mem_primesLE.mp hp
  have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
  have hlog := Real.log_le_log (by exact_mod_cast hprime.pos : (0 : ℝ) < p)
    (by exact_mod_cast hpN : (p : ℝ) ≤ N)
  let w := 2 - Real.cos (Real.log p) - Real.cos (Real.sqrt 2 * Real.log p)
  have hw : 1 ≤ w*(4*(1+Real.log p)^2) :=
    (div_le_iff₀ (by positivity)).mp (rationalTwoCosineWeight_primeLower hprime)
  have hw₀ : 0 ≤ w := by
    dsimp [w]
    linarith [Real.cos_le_one (Real.log p), Real.cos_le_one (Real.sqrt 2 * Real.log p)]
  have hmono := pow_le_pow_left₀ (by linarith : 0 ≤ 1+Real.log p) (by linarith : 1+Real.log p ≤ 1+Real.log N) 2
  have h' : 1 ≤ w*(4*(1+Real.log N)^2) :=
    hw.trans (mul_le_mul_of_nonneg_left (by linarith) hw₀)
  calc
    a p = a p*1 := (mul_one _).symm
    _ ≤ a p*(w*(4*(1+Real.log N)^2)) := mul_le_mul_of_nonneg_left h' (ha p hp)
    _ = _ := by change _ = _*(a p*w); ring

/-- Prime gaps of size at most `1 / (1+t)` in the logarithmic coordinate
transfer the simultaneous returns to rational primes at every sufficiently
large scale. Dusart's Proposition 6.8 supplies the stated gap hypothesis. -/
theorem rationalTwoCosineWeight_primeUpper_of_logGap
    (hgap : ∀ᶠ t : ℝ in Filter.atTop, ∃ p : ℕ, p.Prime ∧ |Real.log p - t| ≤ 1 / (1+t)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∃ p : ℕ, p.Prime ∧ N ≤ Real.log p ∧ Real.log p ≤ 10*N ∧
      2 - Real.cos (Real.log p) - Real.cos (Real.sqrt 2 * Real.log p) ≤ 51 / ((N:ℝ)+1)^2 := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hgap
  obtain ⟨M, hM⟩ := exists_nat_ge T
  filter_upwards [Filter.eventually_ge_atTop (max M 4)] with N hN
  have h₄ : 4 ≤ N := (le_max_right _ _).trans hN
  have hN' : (4:ℝ) ≤ N := by exact_mod_cast h₄
  obtain ⟨k, hk, hkN, hNk, h⟩ := rationalTwoCosineWeight_nearReturn N (by omega)
  let t := 2*Real.pi*k
  have hkn : (k:ℝ) ≤ N := by exact_mod_cast hkN
  have hnk : (N:ℝ) ≤ 4*k := by exact_mod_cast hNk
  have ht₁ : (N:ℝ)+1 ≤ t := by
    dsimp [t]
    nlinarith [mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by positivity : (0:ℝ) ≤ k)]
  have ht₂ : t ≤ 8*(N:ℝ) := by
    dsimp [t]
    nlinarith [mul_le_mul_of_nonneg_right Real.pi_lt_four.le (by positivity : (0:ℝ) ≤ k)]
  have hTN : T ≤ N := hM.trans (by exact_mod_cast (le_max_left M 4).trans hN)
  obtain ⟨p, hp, hu⟩ := hT t (by linarith)
  have hsize : 1/(1+t) ≤ 1 / ((N:ℝ)+1) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    linarith
  have hu' := hu.trans hsize
  have hsmall : 1/((N:ℝ)+1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  obtain ⟨hl, hr⟩ := abs_le.mp (hu'.trans hsmall)
  refine ⟨p, hp, by linarith, by linarith, ?_⟩
  have he := h (Real.log p - t) hu'
  simpa only [show 2*Real.pi*k+(Real.log p - t)=Real.log p by dsimp [t]; ring] using he

end RiemannMasullo
