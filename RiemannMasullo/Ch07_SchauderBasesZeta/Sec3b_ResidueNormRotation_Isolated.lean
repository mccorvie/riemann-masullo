module

public import RiemannMasullo.ForMathlib.NumberTheory.LinearFormsInLogarithms
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Complex.SeparatedChords
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Near returns on a lattice of residue norms

At consecutive primary poles, the outside phase is multiplied by the rotation through
`-log V / log W` turns. For multiplicatively independent residue norms, the two-logarithm
bound controls the number of visits to any disk. In each finite window, removing at most one
index also bounds the sum of all remaining inverse Euler denominators. Both estimates are
uniform in the initial phase and starting index (Theorems 7.1.2.3, pp. 317–323, and 7.3.3.4,
pp. 360–363, with the coefficient change on p. 349). -/

public noncomputable section

namespace RiemannMasullo.Isolated

/-- The rotation between successive poles of residue norm `W`, as observed at norm `V`. -/
def residueNormRotation (W V : ℕ) : Circle :=
  AddCircle.toCircle ((-(Real.log V / Real.log W) : ℝ) : AddCircle (1 : ℝ))

private theorem residueNormRotation_eq_exp (W V : ℕ) :
    residueNormRotation W V = Circle.exp (-(2 * Real.pi) * (Real.log V / Real.log W)) := by
  rw [residueNormRotation, AddCircle.toCircle_apply_mk, div_one, neg_mul, mul_neg]

private theorem residueNormRotation_pow_ne_one (W V : ℕ) (hW : 1 < W) (hV : 1 < V)
    (hind : ¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ V ^ k = W ^ l) (k : ℤ) (hk : k ≠ 0) :
    residueNormRotation W V ^ k ≠ 1 := by
  intro he
  have hL : 0 < Real.log (W : ℝ) := Real.log_pos (by exact_mod_cast hW)
  have hQ : 0 < Real.log (V : ℝ) := Real.log_pos (by exact_mod_cast hV)
  rw [residueNormRotation_eq_exp, ← Circle.exp_zsmul, zsmul_eq_mul, Circle.exp_eq_one] at he
  obtain ⟨l, he⟩ := he
  have hlog : (k : ℝ) * Real.log V = -(l : ℝ) * Real.log W := by
    field_simp [hL.ne'] at he
    linear_combination -he
  have hl : l ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero, neg_zero, zero_mul] at hlog
    exact (mul_ne_zero (Int.cast_ne_zero.mpr hk) hQ.ne') hlog
  have ha := congrArg abs hlog
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos hL, abs_of_pos hQ] at ha
  apply hind ⟨k.natAbs, l.natAbs, Int.natAbs_pos.mpr hk, Int.natAbs_pos.mpr hl, ?_⟩
  have hpow : (V : ℝ) ^ k.natAbs = (W : ℝ) ^ l.natAbs := by
    apply Real.log_injOn_pos (show 0 < (V : ℝ) ^ k.natAbs by positivity)
      (show 0 < (W : ℝ) ^ l.natAbs by positivity)
    simpa [Real.log_pow] using ha
  exact_mod_cast hpow

/-- Distinct iterates of the residue-norm rotation are polynomially separated in their
index difference. The constants depend only on the two residue norms. -/
theorem residueNormRotation_power_separation (W V : ℕ) (hW : 1 < W) (hV : 1 < V)
    (hind : ¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ V ^ k = W ^ l) :
    ∃ d : ℕ, ∃ C ≥ (0 : ℝ), ∀ k : ℤ, k ≠ 0 →
      1 ≤ C * (1 + |(k : ℝ)|) ^ d * ‖1 - (residueNormRotation W V : ℂ) ^ k‖ := by
  obtain ⟨d, B, hB, hb⟩ := polynomial_bound_inv_one_sub_of_exp_eq_one W V 1 hW hV (by decide)
  have hL : 0 < Real.log (W : ℝ) := Real.log_pos (by exact_mod_cast hW)
  have hLc : (Real.log (W : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  let c := 2 * Real.pi / Real.log W
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨d, B * (1 + c) ^ d, by positivity, fun k hk ↦ ?_⟩
  let s : ℂ := (k : ℂ) * (2 * Real.pi * Complex.I) / Real.log W
  let z : ℂ := (residueNormRotation W V : ℂ) ^ k
  have hperiod : Complex.exp (-(Real.log W : ℂ) * s) = 1 := by
    apply Complex.exp_eq_one_iff.mpr ⟨-k, ?_⟩
    dsimp only [s]
    simp only [Int.cast_neg]
    field_simp [hLc]
  have hphase : z = Complex.exp (-(Real.log V : ℂ) * s) := by
    dsimp only [z, s]
    rw [residueNormRotation_eq_exp, Circle.coe_exp, ← Complex.exp_int_mul]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    field_simp [hLc]
  have hz : z ≠ 1 := by
    intro h
    apply residueNormRotation_pow_ne_one W V hW hV hind k hk
    exact Circle.ext h
  have hbound := hb s z (by simpa using hperiod) (by simpa using hphase)
  rw [norm_inv, inv_le_iff_one_le_mul₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hz.symm))] at hbound
  have hs : ‖s‖ = |(k : ℝ)| * c := by
    dsimp only [s, c]
    rw [norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hL, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    ring
  have hsize : 1 + ‖s‖ ≤ (1 + c) * (1 + |(k : ℝ)|) := by
    rw [hs]
    nlinarith [abs_nonneg (k : ℝ)]
  calc
    1 ≤ B * (1 + ‖s‖) ^ d * ‖1 - z‖ := hbound
    _ ≤ B * ((1 + c) * (1 + |(k : ℝ)|)) ^ d * ‖1 - z‖ := by gcongr
    _ = _ := by rw [mul_pow]; ring

private theorem rotated_point_distance (a r : Circle) (m n : ℤ) :
    ‖1 - (r : ℂ) ^ (m - n)‖ = ‖(a : ℂ) * (r : ℂ) ^ m - (a : ℂ) * (r : ℂ) ^ n‖ := by
  rw [norm_sub_rev (1 : ℂ)]
  have hunit : ‖(a : ℂ) * (r : ℂ) ^ n‖ = 1 := by
    rw [← Circle.coe_zpow, ← Circle.coe_mul, Circle.norm_coe]
  calc
    ‖(r : ℂ) ^ (m - n) - 1‖ =
        ‖((r : ℂ) ^ (m - n) - 1) * ((a : ℂ) * (r : ℂ) ^ n)‖ := by rw [norm_mul, hunit, mul_one]
    _ = _ := by
      congr 1
      rw [sub_mul, one_mul, mul_left_comm, ← zpow_add₀ (Circle.coe_ne_zero r), sub_add_cancel]

private theorem count_separated_returns (z : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C) (d : ℕ)
    (hsep : ∀ m n : ℕ, m ≠ n → 1 ≤ C * (1 + |(m : ℝ) - (n : ℝ)|) ^ d * ‖z m - z n‖)
    (center : ℂ) (ε : ℝ) (H K : ℕ) (hK : 0 < K)
    (hthreshold : C * (K : ℝ) ^ d * (2 * ε) < 1) :
    ((Finset.range (H + 1)).filter fun n : ℕ ↦ ‖z n - center‖ ≤ ε).card ≤ H / K + 1 := by
  classical
  rw [← Finset.card_range (H / K + 1)]
  apply Finset.card_le_card_of_injOn (fun n : ℕ ↦ n / K)
  · intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right
      (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hn).1))))
  · intro m hm n hn hblock
    by_contra hne
    have hsep' := hsep m n hne
    have hm' := Nat.mod_add_div m K
    have hn' := Nat.mod_add_div n K
    change m / K = n / K at hblock
    rw [hblock] at hm'
    have hgap : 1 + |(m : ℤ) - n| ≤ (K : ℤ) := by
      have hmK := Nat.mod_lt m hK
      have hnK := Nat.mod_lt n hK
      by_cases hmn : (m : ℤ) ≤ n
      · rw [abs_of_nonpos (by omega)]
        omega
      · rw [abs_of_nonneg (by omega)]
        omega
    have hreal : 1 + |(m : ℝ) - n| ≤ (K : ℝ) := by exact_mod_cast hgap
    have hchord : ‖z m - z n‖ ≤ 2 * ε := by
      have htri := norm_sub_le (z m - center) (z n - center)
      rw [sub_sub_sub_cancel_right] at htri
      linarith [(Finset.mem_filter.mp hm).2, (Finset.mem_filter.mp hn).2]
    apply (not_lt_of_ge hsep') (lt_of_le_of_lt ?_ hthreshold)
    gcongr

/-- In any `H + 1` successive indices, at most `⌊H / K⌋ + 1` iterates can lie in the
same closed disk of radius `ε` if `2 C K ^ d ε < 1`. The constants are uniform in the
initial phase, center and starting index. -/
theorem residueNormRotation_close_returns_card (W V : ℕ) (hW : 1 < W) (hV : 1 < V)
    (hind : ¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ V ^ k = W ^ l) :
    ∃ d : ℕ, ∃ C ≥ (0 : ℝ), ∀ (a : Circle) (center : ℂ) (t : ℤ)
      (ε : ℝ) (H K : ℕ), 0 < K → C * (K : ℝ) ^ d * (2 * ε) < 1 →
      ((Finset.range (H + 1)).filter fun n : ℕ ↦
        ‖(a : ℂ) * (residueNormRotation W V : ℂ) ^ (t + n) - center‖ ≤ ε).card ≤ H / K + 1 := by
  obtain ⟨d, C, hC, hsep⟩ := residueNormRotation_power_separation W V hW hV hind
  refine ⟨d, C, hC, fun a center t ε H K hK hthr ↦
    count_separated_returns _ C hC d ?_ center ε H K hK hthr⟩
  intro m n hmn
  have h := hsep ((t + m) - (t + n)) (by omega)
  rw [rotated_point_distance a] at h
  simpa only [Int.cast_sub, Int.cast_add, Int.cast_natCast, add_sub_add_left_eq_sub] using h

/-- In a window of `H + 1` consecutive primary poles, all but at most one outside Euler
denominator have total reciprocal norm bounded by a degree-`d` polynomial times
`1 + log (H + 1)`. Both constants depend only on the two residue norms. -/
theorem residueNormRotation_sum_inv_except_one (W V : ℕ) (hW : 1 < W) (hV : 1 < V)
    (hind : ¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ V ^ k = W ^ l) :
    ∃ d : ℕ, ∃ C > (0 : ℝ), ∀ (a : Circle) (t : ℤ) (H : ℕ),
      ∃ E ⊆ Finset.range (H + 1), E.card ≤ 1 ∧
        (∀ n ∈ Finset.range (H + 1), (a : ℂ) * (residueNormRotation W V : ℂ) ^ (t + n) = 1 →
          n ∈ E) ∧
        ∑ n ∈ Finset.range (H + 1) \ E,
          ‖1 - (a : ℂ) * (residueNormRotation W V : ℂ) ^ (t + n)‖⁻¹ ≤
            C * (1 + (H : ℝ)) ^ d * (1 + Real.log (H + 1)) := by
  obtain ⟨d, B, hB, hsep⟩ := residueNormRotation_power_separation W V hW hV hind
  refine ⟨d, 2 * Real.pi * (B + 1), by positivity, fun a t H ↦ ?_⟩
  let z (n : ℕ) := a * residueNormRotation W V ^ (t + n)
  let M := (B + 1) * (1 + (H : ℝ)) ^ d
  have hM : 0 < M := by dsimp [M]; positivity
  have hgap (i) (hi : i ∈ Finset.range (H + 1)) (j) (hj : j ∈ Finset.range (H + 1))
      (hne : i ≠ j) : 1 / M ≤ ‖(z i : ℂ) - z j‖ := by
    have hi' : (i : ℝ) ≤ H := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hj' : (j : ℝ) ≤ H := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hab : |(i : ℝ) - (j : ℝ)| ≤ H :=
      abs_le.mpr ⟨by linarith [Nat.cast_nonneg (α := ℝ) i],
        by linarith [Nat.cast_nonneg (α := ℝ) j]⟩
    have h := hsep ((t + i) - (t + j)) (by omega)
    rw [rotated_point_distance a] at h
    simp only [Int.cast_sub, Int.cast_natCast, add_sub_add_left_eq_sub] at h
    rw [div_le_iff₀ hM, mul_comm]
    change 1 ≤ (B + 1) * (1 + (H : ℝ)) ^ d * _
    apply h.trans
    simp only [z, Circle.coe_mul, Circle.coe_zpow]
    gcongr
    linarith
  obtain ⟨E, hE, hcard, hhit, hsum⟩ := Circle.exists_card_le_one_sum_inv_chord_le
    (Finset.range (H + 1)) z (one_div_pos.mpr hM) hgap
  refine ⟨E, hE, hcard, fun n hn hit ↦ hhit n hn ?_, ?_⟩
  · simpa only [z, Circle.coe_mul, Circle.coe_zpow] using hit
  simp only [z, Circle.coe_mul, Circle.coe_zpow, Finset.card_range, div_div_eq_mul_div,
    div_one] at hsum
  simp only [norm_sub_rev (1 : ℂ)]
  refine hsum.trans ?_
  have hhar := harmonic_le_one_add_log (H + 1)
  push_cast at hhar
  calc
    _ ≤ (2 * Real.pi * M) * (1 + Real.log (H + 1)) :=
      mul_le_mul_of_nonneg_left hhar (by positivity)
    _ = _ := by dsimp [M]; ring

/-- From each block of length `2^j` remove at most one index. For every positive
`σ` the remaining reciprocal Euler denominators, weighted by `(2^j)^(-d-σ)`, have
summable block totals. The exceptional indices are independent of `σ`. The starting
indices can in particular give the positive or the negative dyadic shells. -/
theorem residueNormRotation_dyadic_sum_inv_except_one (W V : ℕ) (hW : 1 < W) (hV : 1 < V)
    (hind : ¬ ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ V ^ k = W ^ l) :
    ∃ d : ℕ, ∀ (a : Circle) (t : ℕ → ℤ), ∃ E : ℕ → Finset ℕ,
      (∀ j, E j ⊆ Finset.range (2 ^ j) ∧ (E j).card ≤ 1 ∧
        ∀ n ∈ Finset.range (2 ^ j), (a : ℂ) * (residueNormRotation W V : ℂ) ^ (t j + n) = 1 →
          n ∈ E j) ∧
      ∀ σ : ℝ, 0 < σ → Summable (fun j : ℕ ↦
        ((2 : ℝ) ^ j) ^ (-(d : ℝ) - σ) *
          ∑ n ∈ Finset.range (2 ^ j) \ E j,
            ‖1 - (a : ℂ) * (residueNormRotation W V : ℂ) ^ (t j + n)‖⁻¹) := by
  obtain ⟨d, C, hC, h⟩ := residueNormRotation_sum_inv_except_one W V hW hV hind
  refine ⟨d, fun a t ↦ ?_⟩
  let mass (j : ℕ) (E : Finset ℕ) := ∑ n ∈ Finset.range (2 ^ j) \ E,
    ‖1 - (a : ℂ) * (residueNormRotation W V : ℂ) ^ (t j + n)‖⁻¹
  have hblock (j : ℕ) : ∃ E ⊆ Finset.range (2 ^ j), E.card ≤ 1 ∧
      (∀ n ∈ Finset.range (2 ^ j), (a : ℂ) * (residueNormRotation W V : ℂ) ^ (t j + n) = 1 →
        n ∈ E) ∧
      mass j E ≤ C * ((2 : ℝ) ^ j) ^ d * (1 + j * Real.log 2) := by
    have hlen : 2 ^ j - 1 + 1 = (2 : ℕ) ^ j := Nat.sub_add_cancel (one_le_pow₀ (by decide : 1 ≤ (2 : ℕ)))
    have hreal : ((2 ^ j - 1 : ℕ) : ℝ) + 1 = (2 : ℝ) ^ j := by exact_mod_cast hlen
    obtain ⟨E, hE, hcard, hhit, hb⟩ := h a (t j) (2 ^ j - 1)
    rw [hlen] at hE hhit hb
    rw [add_comm 1 _, hreal, Real.log_pow] at hb
    exact ⟨E, hE, hcard, hhit, hb⟩
  choose E hE hcard hhit hmass using hblock
  refine ⟨E, fun j ↦ ⟨hE j, hcard j, hhit j⟩, fun σ hσ ↦ ?_⟩
  let r := (2 : ℝ) ^ (-σ)
  have hr₀ : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hσ)
  have hlin : Summable (fun j : ℕ ↦ (j : ℝ) * r ^ j) := by
    have hr : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr₀]
    simpa [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hr₀] using
      summable_norm_pow_mul_geometric_of_norm_lt_one 1 hr
  have hmaj : Summable (fun j : ℕ ↦ C * r ^ j * (1 + j * Real.log 2)) := by
    convert ((summable_geometric_of_lt_one hr₀ hr₁).add (hlin.mul_right (Real.log 2))).mul_left C using 1
    ext j
    ring
  refine Summable.of_nonneg_of_le (fun j ↦ by positivity) (fun j ↦ ?_) hmaj
  have hweight : ((2 : ℝ) ^ j) ^ (-(d : ℝ) - σ) * ((2 : ℝ) ^ j) ^ d = r ^ j := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ j) d,
      ← Real.rpow_add (by positivity : 0 < (2 : ℝ) ^ j),
      show -(d : ℝ) - σ + d = -σ by ring,
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm (j : ℝ),
      Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ ((2 : ℝ) ^ j) ^ (-(d : ℝ) - σ) *
        (C * ((2 : ℝ) ^ j) ^ d * (1 + j * Real.log 2)) :=
      mul_le_mul_of_nonneg_left (hmass j) (by positivity)
    _ = C * r ^ j * (1 + j * Real.log 2) := by rw [← hweight]; ring

end RiemannMasullo.Isolated
