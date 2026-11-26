module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # A Chebyshev lower bound for the rational prime-cube Riesz contribution

At prime norm cutoff `U ^ 3`, the two-cosine weight and the square-root Riesz
kernel give a nonnegative finite sum over actual primes at most `U`.
An interval on which the first cosine is nonpositive supplies a fixed fraction
of the order `U ^ (5 / 2)` by Chebyshev's elementary bounds.
-/

public noncomputable section

open Finset Filter Real

namespace RiemannMasullo

/-- Prime-cube part of the compensated first-prime Riesz sum at the norm cutoff
`U ^ 3`. The density compensation does not enter this positive prime-power term. -/
@[expose] def rationalPrimeCubeRiesz (U : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p *
    (2 - Real.cos (3 * Real.log p) - Real.cos (Real.sqrt 2 * (3 * Real.log p))) *
    (U * Real.sqrt U - p * Real.sqrt p)

private theorem cubeRiesz_phase {U : ℝ} (hU : 0 < U) :
    ∃ B : ℝ, 0 < B ∧ Real.exp (-(2 * Real.pi / 3)) * (U / 2) ≤ B ∧ B ≤ U / 2 ∧
      ∀ v : ℝ, B * Real.exp (-(Real.pi / 3)) ≤ v → v ≤ B → Real.cos (3 * Real.log v) ≤ 0 := by
  let x := (3 * Real.log (U / 2) - 3 * Real.pi / 2) / (2 * Real.pi)
  let n : ℤ := ⌊x⌋
  let h := (3 * Real.pi / 2 + (n : ℝ) * (2 * Real.pi)) / 3
  have hπ : 0 < 2 * Real.pi := by positivity
  have hl : (n : ℝ) * (2 * Real.pi) ≤ 3 * Real.log (U / 2) - 3 * Real.pi / 2 :=
    (le_div_iff₀ hπ).mp (Int.floor_le x)
  have hu : 3 * Real.log (U / 2) - 3 * Real.pi / 2 < ((n : ℝ) + 1) * (2 * Real.pi) :=
    (div_lt_iff₀ hπ).mp (Int.lt_floor_add_one x)
  refine ⟨Real.exp h, Real.exp_pos _, ?_, ?_, ?_⟩
  · nth_rw 1 [← Real.exp_log (by positivity : 0 < U / 2)]
    rw [← Real.exp_add, Real.exp_le_exp]
    dsimp [h]
    linarith
  · rw [← Real.exp_log (by positivity : 0 < U / 2), Real.exp_le_exp]
    dsimp [h]
    linarith
  · intro v hv₁ hv₂
    have hv : 0 < v := (mul_pos (Real.exp_pos _) (Real.exp_pos _)).trans_le hv₁
    have hvlo := Real.log_le_log (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hv₁
    have hvhi := Real.log_le_log hv hv₂
    rw [← Real.exp_add, Real.log_exp] at hvlo
    rw [Real.log_exp] at hvhi
    dsimp [h] at hvlo hvhi
    rw [show 3 * Real.log v = (3 * Real.log v - (n : ℝ) * (2 * Real.pi)) +
      (n : ℝ) * (2 * Real.pi) by ring, Real.cos_add_int_mul_two_pi]
    exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)

private theorem cubeRiesz_shell {U A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (hB : B ≤ U / 2) (hcos : ∀ v : ℝ, A ≤ v → v ≤ B → Real.cos (3 * Real.log v) ≤ 0) :
    U * Real.sqrt U * (1 - 1 / (2 * Real.sqrt 2)) * (Chebyshev.theta B - Chebyshev.theta A) ≤
      rationalPrimeCubeRiesz U := by
  have hU : 0 ≤ U := by linarith
  have hB₀ : 0 ≤ B := hA.trans hAB
  let L := U * Real.sqrt U * (1 - 1 / (2 * Real.sqrt 2))
  let w (p : ℕ) := 2 - Real.cos (3 * Real.log p) - Real.cos (Real.sqrt 2 * (3 * Real.log p))
  let f (p : ℕ) := Real.log p * w p * (U * Real.sqrt U - p * Real.sqrt p)
  let I := Nat.primesLE ⌊B⌋₊ \ Nat.primesLE ⌊A⌋₊
  have hL : 0 ≤ L := by
    dsimp [L]
    have hs : 1 ≤ Real.sqrt 2 := by simp
    apply mul_nonneg (mul_nonneg hU (Real.sqrt_nonneg _)) (sub_nonneg.mpr ?_)
    rw [div_le_one (by positivity)]
    linarith
  have hAB' : Nat.primesLE ⌊A⌋₊ ⊆ Nat.primesLE ⌊B⌋₊ :=
    Nat.primesLE_mono (Nat.floor_le_floor hAB)
  have heq : Chebyshev.theta B - Chebyshev.theta A = ∑ p ∈ I, Real.log p := by
    rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
    exact (Finset.sum_sdiff_eq_sub hAB').symm
  have hmem {p : ℕ} {x : ℝ} (hx : 0 ≤ x) (hp : p ∈ Nat.primesLE ⌊x⌋₊) : (p : ℝ) ≤ x :=
    (Nat.cast_le.mpr (Nat.le_of_mem_primesLE hp)).trans (Nat.floor_le hx)
  have hlog {p n : ℕ} (hp : p ∈ Nat.primesLE n) : 0 ≤ Real.log p :=
    Real.log_nonneg (by exact_mod_cast (Nat.one_lt_of_mem_primesLE hp).le)
  change L * _ ≤ ∑ p ∈ Nat.primesLE ⌊U⌋₊, f p
  rw [heq, Finset.mul_sum]
  calc
    _ ≤ ∑ p ∈ I, f p := by
      refine Finset.sum_le_sum fun p hp ↦ ?_
      obtain ⟨hpB, hpA⟩ := Finset.mem_sdiff.mp hp
      have hpU := (hmem hB₀ hpB).trans hB
      have hpA' : A ≤ p := by
        by_contra! hh
        exact hpA (Nat.mem_primesLE.mpr ⟨Nat.le_floor hh.le, Nat.prime_of_mem_primesLE hpB⟩)
      have hw : 1 ≤ w p := by
        dsimp [w]
        linarith [hcos _ hpA' (hmem hB₀ hpB), Real.cos_le_one (Real.sqrt 2 * (3 * Real.log p))]
      have hkp := mul_le_mul hpU (Real.sqrt_le_sqrt hpU) (Real.sqrt_nonneg _) (by positivity)
      rw [Real.sqrt_div hU] at hkp
      have he : U / 2 * (Real.sqrt U / Real.sqrt 2) = U * Real.sqrt U * (1 / (2 * Real.sqrt 2)) := by
        field_simp
      rw [he] at hkp
      have hk : L ≤ U * Real.sqrt U - p * Real.sqrt p := by dsimp [L]; linarith
      have hweight : Real.log p ≤ Real.log p * w p := by
        simpa only [mul_one] using (mul_le_mul_of_nonneg_left hw (hlog hpB))
      dsimp [f]
      rw [mul_comm L]
      exact mul_le_mul hweight hk hL (mul_nonneg (hlog hpB) (by linarith))
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.sdiff_subset.trans (Nat.primesLE_mono (Nat.floor_le_floor (by linarith : B ≤ U)))
      · intro p hp _
        dsimp [f]
        have hw : 0 ≤ w p := by
          dsimp [w]
          linarith [Real.cos_le_one (3 * Real.log p), Real.cos_le_one (Real.sqrt 2 * (3 * Real.log p))]
        exact mul_nonneg (mul_nonneg (hlog hp) hw) (sub_nonneg.mpr
          (mul_le_mul (hmem hU hp) (Real.sqrt_le_sqrt (hmem hU hp)) (Real.sqrt_nonneg _) hU))

private theorem cubeRiesz_theta_shell {d : ℝ}
    (hd : d < Real.log 2 * (1 - 2 * Real.exp (-(Real.pi / 3)))) :
    ∀ᶠ B : ℝ in atTop, d * B ≤ Chebyshev.theta B -
      Chebyshev.theta (B * Real.exp (-(Real.pi / 3))) := by
  let c := Real.log 2 * (1 - 2 * Real.exp (-(Real.pi / 3)))
  have hlog : Tendsto (fun x : ℝ ↦ Real.log x / Real.sqrt x) atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).tendsto_div_nhds_zero
  have herr : Tendsto (fun x : ℝ ↦ (Real.log 2 + Real.log 3) / x + 3 * (Real.log x / Real.sqrt x))
      atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds (x := Real.log 2 + Real.log 3)).div_atTop
      (show Tendsto (fun x : ℝ ↦ x) atTop atTop from tendsto_id)).add (hlog.const_mul 3)
  have hgap : 0 < c - d := sub_pos.mpr hd
  filter_upwards [eventually_ge_atTop (1 : ℝ), herr.eventually_lt_const hgap] with B hB he
  have hB₀ : 0 < B := by linarith
  have hs : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB₀
  have hs₁ : 1 ≤ Real.sqrt B := by simpa using Real.sqrt_le_sqrt hB
  have hl := Chebyshev.theta_ge' hB
  have hu := Chebyshev.theta_le_log4_mul_x (x := B * Real.exp (-(Real.pi / 3))) (by positivity)
  have h4 : Real.log 4 = 2 * Real.log 2 := Real.log_four_eq
  rw [h4] at hu
  have hlB : Real.log (B + 2) ≤ Real.log 3 + Real.log B := by
    rw [← Real.log_mul (by norm_num) hB₀.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have hsmall := mul_lt_mul_of_pos_right he hB₀
  have hx : (Real.log B / Real.sqrt B) * B = Real.sqrt B * Real.log B := by
    field_simp
    nlinarith [congrArg (fun x : ℝ ↦ x * Real.log B) (Real.sq_sqrt hB₀.le)]
  rw [add_mul, div_mul_cancel₀ _ hB₀.ne', mul_assoc, hx] at hsmall
  have hlogB := mul_le_mul_of_nonneg_right hs₁ (Real.log_nonneg hB)
  dsimp [c] at hsmall
  linarith

/-- An explicit positive lower coefficient for the prime-cube contribution. -/
@[expose] def rationalPrimeCubeRieszLowerConstant : ℝ :=
  (Real.exp (-(2 * Real.pi / 3)) / 2 * (1 - 1 / (2 * Real.sqrt 2))) *
    (Real.log 2 * (1 - 2 * Real.exp (-(Real.pi / 3))))

private theorem cubeRiesz_factors_pos :
    0 < 1 - 1 / (2 * Real.sqrt 2) ∧
    0 < Real.log 2 * (1 - 2 * Real.exp (-(Real.pi / 3))) := by
  have hs : 1 ≤ Real.sqrt 2 := by simp
  have he : 2 < Real.exp (Real.pi / 3) :=
    Real.exp_one_gt_two.trans (Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_three]))
  rw [Real.exp_neg]
  constructor
  · apply sub_pos.mpr ((div_lt_one (by positivity)).mpr (by linarith))
  · apply mul_pos (Real.log_pos (by norm_num))
    rw [← div_eq_mul_inv, sub_pos, div_lt_one (Real.exp_pos _)]
    exact he

/-- Positivity of the uniform lower coefficient furnished by the phase interval. -/
theorem rationalPrimeCubeRieszLowerConstant_pos : 0 < rationalPrimeCubeRieszLowerConstant :=
  mul_pos (mul_pos (by positivity) cubeRiesz_factors_pos.1) cubeRiesz_factors_pos.2

private theorem cubeRiesz_index_lower {d : ℝ} (hd : d < rationalPrimeCubeRieszLowerConstant) :
    ∀ᶠ U : ℝ in atTop, d * (U ^ 2 * Real.sqrt U) ≤ rationalPrimeCubeRiesz U := by
  let e := Real.exp (-(2 * Real.pi / 3)) / 2
  let a := 1 - 1 / (2 * Real.sqrt 2)
  let c := Real.log 2 * (1 - 2 * Real.exp (-(Real.pi / 3)))
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨ha, hc⟩ := cubeRiesz_factors_pos
  change 0 < a at ha
  change 0 < c at hc
  change d < (e * a) * c at hd
  have hquot : d / (e * a) < c := (div_lt_iff₀ (mul_pos he ha)).mpr (by linarith)
  obtain ⟨q, hq, hqc⟩ := exists_between (max_lt hc hquot)
  have hq₀ : 0 < q := (le_max_left _ _).trans_lt hq
  have hdq : d < q * (e * a) :=
    (div_lt_iff₀ (mul_pos he ha)).mp ((le_max_right _ _).trans_lt hq)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (cubeRiesz_theta_shell hqc)
  filter_upwards [eventually_ge_atTop (max 1 (N / e))] with U hU
  have hU₀ : 0 < U := zero_lt_one.trans_le ((le_max_left _ _).trans hU)
  obtain ⟨B, hB₀, hBu, hB, hcos⟩ := cubeRiesz_phase hU₀
  have hEB : e * U ≤ B := by dsimp [e]; linarith
  have hNB : N ≤ B := ((div_le_iff₀' he).mp ((le_max_right _ _).trans hU)).trans hEB
  have hθ := hN B hNB
  have hAB : B * Real.exp (-(Real.pi / 3)) ≤ B := mul_le_of_le_one_right hB₀.le
    (Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos]))
  calc
    _ ≤ (q * (e * a)) * (U ^ 2 * Real.sqrt U) :=
      mul_le_mul_of_nonneg_right hdq.le (by positivity)
    _ = (U * Real.sqrt U * a) * (q * (e * U)) := by ring
    _ ≤ (U * Real.sqrt U * a) * (Chebyshev.theta B - Chebyshev.theta (B * Real.exp (-(Real.pi / 3)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (mul_le_mul_of_nonneg_left hEB hq₀.le).trans hθ
    _ ≤ _ := cubeRiesz_shell (mul_nonneg hB₀.le (Real.exp_pos _).le) hAB hB hcos

/-- At every sufficiently large norm cutoff, the actual weighted sum over prime
cubes exceeds any coefficient below the explicit Chebyshev constant times `X ^ (5 / 6)`. -/
theorem rationalPrimeCubeRiesz_eventually_ge {d : ℝ} (hd : d < rationalPrimeCubeRieszLowerConstant) :
    ∀ᶠ X : ℝ in atTop, d * X ^ (5 / 6 : ℝ) ≤
      ∑ p ∈ Nat.primesLE ⌊X ^ (1 / 3 : ℝ)⌋₊, Real.log p *
        (2 - Real.cos (3 * Real.log p) - Real.cos (Real.sqrt 2 * (3 * Real.log p))) *
        (Real.sqrt X - p * Real.sqrt p) := by
  have H := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually
    (cubeRiesz_index_lower hd)
  filter_upwards [H, eventually_gt_atTop (0 : ℝ)] with X h hX
  let U := X ^ (1 / 3 : ℝ)
  have hU : 0 < U := Real.rpow_pos_of_pos hX _
  have hp (c : ℝ) : U ^ c = X ^ ((1 / 3 : ℝ) * c) := (Real.rpow_mul hX.le _ _).symm
  have he : U ^ 2 * Real.sqrt U = X ^ (5 / 6 : ℝ) := by
    calc
      _ = U ^ ((2 : ℝ) + 1 / 2) := by rw [Real.rpow_add hU, Real.rpow_two, Real.sqrt_eq_rpow]
      _ = _ := by rw [hp]; norm_num
  have hk : U * Real.sqrt U = Real.sqrt X := by
    calc
      _ = U ^ ((1 : ℝ) + 1 / 2) := by rw [Real.rpow_add hU, Real.rpow_one, Real.sqrt_eq_rpow]
      _ = _ := by rw [hp, Real.sqrt_eq_rpow]; norm_num
  change d * (U ^ 2 * Real.sqrt U) ≤ rationalPrimeCubeRiesz U at h
  rw [he] at h
  simpa only [rationalPrimeCubeRiesz, hk] using h

/-- A rational coefficient available without evaluating the exponential or logarithm. -/
theorem rationalPrimeCubeRieszLowerConstant_gt_one_div_twoHundred :
    (1 / 200 : ℝ) < rationalPrimeCubeRieszLowerConstant := by
  have he₁ : Real.exp 1 < 11 / 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he₂ : Real.exp (1 / 8) < 6 / 5 := by
    by_contra! h
    have hh : (6 / 5 : ℝ) ^ 8 ≤ Real.exp (1 / 8) ^ 8 :=
      pow_le_pow_left₀ (by norm_num) h 8
    rw [← Real.exp_nat_mul] at hh
    norm_num at hh
    linarith [Real.exp_one_lt_three]
  have hten : Real.exp (2 * Real.pi / 3) < 10 := by
    calc
      _ < Real.exp (2 + 1 / 8) := Real.exp_strictMono (by linarith [Real.pi_lt_d2])
      _ = (Real.exp 1 * Real.exp 1) * Real.exp (1 / 8) := by
        rw [Real.exp_add, show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      _ < ((11 / 4) * (11 / 4)) * (6 / 5) := by gcongr
      _ < _ := by norm_num
  have he : (1 / 20 : ℝ) < Real.exp (-(2 * Real.pi / 3)) / 2 := by
    rw [Real.exp_neg]
    have h : (1 / 10 : ℝ) < (Real.exp (2 * Real.pi / 3))⁻¹ := by
      rw [← one_div, lt_div_iff₀ (Real.exp_pos _)]
      linarith
    linarith
  have hs : 5 / 4 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have ha : (3 / 5 : ℝ) < 1 - 1 / (2 * Real.sqrt 2) := by
    have h : 1 / (2 * Real.sqrt 2) < 2 / 5 := (div_lt_iff₀ (by positivity)).mpr (by linarith)
    linarith
  have hb : (2 / 3 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hc : (1 / 4 : ℝ) < 1 - 2 * Real.exp (-(Real.pi / 3)) := by
    have h : (8 / 3 : ℝ) < Real.exp (Real.pi / 3) :=
      lt_trans (by linarith [Real.exp_one_gt_d9])
        (Real.exp_strictMono (by linarith [Real.pi_gt_three] : (1 : ℝ) < Real.pi / 3))
    rw [Real.exp_neg, ← div_eq_mul_inv]
    have hh : 2 / Real.exp (Real.pi / 3) < 3 / 4 :=
      (div_lt_iff₀ (Real.exp_pos _)).mpr (by linarith)
    linarith
  calc
    (1 / 200 : ℝ) = (1 / 20 * (3 / 5)) * (2 / 3 * (1 / 4)) := by norm_num
    _ < rationalPrimeCubeRieszLowerConstant := by
      unfold rationalPrimeCubeRieszLowerConstant
      gcongr

end RiemannMasullo
