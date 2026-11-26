module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-! # Local curvature of the rational first-prime Riesz sum

A mean - preserving change of the cutoff leaves each affine prime contribution
unchanged in expectation. Only primes between the two cutoffs enter the
remainder. The quadratic principal term contributes its signed variance.
-/

public noncomputable section

open Finset MeasureTheory

namespace RiemannMasullo

/-- The first-prime Riesz sum with a real prime coefficient and a quadratic
pole correction. Taking the coefficient equal to one and the pole equal to
one gives the centered principal rational sum. -/
@[expose] def rationalFirstPrimeRiesz (χ : ℕ → ℝ) (pole x : ℝ) : ℝ :=
  (∑ p ∈ (range (⌈x⌉₊ + 1)).filter Nat.Prime,
    χ p * Real.log p * max (x - p) 0) - pole * x ^ 2 / 2

/-- The slope at the original cutoff, using the left derivative when the
cutoff is a prime. -/
@[expose] def rationalFirstPrimeSlope (χ : ℕ → ℝ) (pole x : ℝ) : ℝ :=
  (∑ p ∈ (range (⌈x⌉₊ + 1)).filter Nat.Prime,
    if (p : ℝ) < x then χ p * Real.log p else 0) - pole * x

/-- The signed prime curvature. The ramp is zero unless the prime lies
between the original and perturbed cutoffs. -/
@[expose] def rationalFirstPrimeCurvature (χ : ℕ → ℝ) (x y : ℝ) : ℝ :=
  ∑ p ∈ (range (⌈max x y⌉₊ + 1)).filter Nat.Prime,
    χ p * Real.log p *
      (if (p : ℝ) < x then max (p - y) 0 else max (y - p) 0)

private theorem firstPrime_extend {s : ℝ} {n : ℕ} (h : ⌈s⌉₊ ≤ n)
    (f : ℕ → ℝ) (hf : ∀ p : ℕ, s < p → f p = 0) :
    (∑ p ∈ (range (⌈s⌉₊ + 1)).filter Nat.Prime, f p) =
      ∑ p ∈ (range (n + 1)).filter Nat.Prime, f p := by
  apply Finset.sum_subset
  · intro p hp
    obtain ⟨hp, hp'⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hp; omega), hp'⟩
  · intro p hp hn
    apply hf
    have hceil : ⌈s⌉₊ < p := by
      by_contra! hh
      exact hn (mem_filter.mpr ⟨mem_range.mpr (by omega), (mem_filter.mp hp).2⟩)
    exact lt_of_le_of_lt (Nat.le_ceil s) (by exact_mod_cast hceil)

/-- Exact tangent remainder for the centered first-prime sum, including cutoffs
that are themselves primes and either order of the two real cutoffs. -/
theorem rationalFirstPrimeRiesz_tangent (χ : ℕ → ℝ) (pole x y : ℝ) :
    rationalFirstPrimeRiesz χ pole y =
      rationalFirstPrimeRiesz χ pole x + (y - x) * rationalFirstPrimeSlope χ pole x +
      rationalFirstPrimeCurvature χ x y - pole * (y - x) ^ 2 / 2 := by
  let n := ⌈max x y⌉₊
  let P := (range (n + 1)).filter Nat.Prime
  let w (p : ℕ) := χ p * Real.log p
  have hy : ⌈y⌉₊ ≤ n := Nat.ceil_mono (le_max_right x y)
  have hx : ⌈x⌉₊ ≤ n := Nat.ceil_mono (le_max_left x y)
  have hext (s : ℝ) (hs : ⌈s⌉₊ ≤ n) :
      rationalFirstPrimeRiesz χ pole s =
        (∑ p ∈ P, w p * max (s - p) 0) - pole * s ^ 2 / 2 := by
    unfold rationalFirstPrimeRiesz
    congr 1
    apply firstPrime_extend hs
    intro p hp
    simp [max_eq_right (sub_nonpos.mpr hp.le)]
  have hslope : rationalFirstPrimeSlope χ pole x =
        (∑ p ∈ P, if (p : ℝ) < x then w p else 0) - pole * x := by
    unfold rationalFirstPrimeSlope
    congr 1
    apply firstPrime_extend hx
    intro p hp
    simp [not_lt.mpr hp.le]
  have hsum : (∑ p ∈ P, w p * max (y - p) 0) =
      (∑ p ∈ P, w p * max (x - p) 0) +
      (y - x) * (∑ p ∈ P, if (p : ℝ) < x then w p else 0) + rationalFirstPrimeCurvature χ x y := by
    unfold rationalFirstPrimeCurvature
    change _ = _ + _ * _ + ∑ p ∈ P, w p * _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hx' : (p : ℝ) < x
    · simp only [ite_eq_left hx', max_eq_left (sub_nonneg.mpr hx'.le)]
      cases le_total (p : ℝ) y with
      | inl h => rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]; ring
      | inr h => rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]; ring
    · simp [hx', max_eq_right (sub_nonpos.mpr (le_of_not_gt hx'))]
  rw [hext y hy, hext x hx, hslope, hsum]
  ring

/-- The exact signed smoothing identity on a probability space. Centering
cancels the prime slope and the pole contributes the second central moment. -/
theorem rationalFirstPrimeRiesz_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (χ : ℕ → ℝ) (pole x : ℝ) (U : Ω → ℝ)
    (hU : Integrable U μ) (hmean : ∫ ω, U ω ∂μ = x)
    (hV : Integrable (fun ω => (U ω - x) ^ 2) μ)
    (hC : Integrable (fun ω => rationalFirstPrimeCurvature χ x (U ω)) μ) :
    (∫ ω, rationalFirstPrimeRiesz χ pole (U ω) ∂μ) =
      rationalFirstPrimeRiesz χ pole x + (∫ ω, rationalFirstPrimeCurvature χ x (U ω) ∂μ) -
      pole / 2 * (∫ ω, (U ω - x) ^ 2 ∂μ) := by
  let s := rationalFirstPrimeSlope χ pole x
  let b := rationalFirstPrimeRiesz χ pole x
  have hl : Integrable (fun ω => (U ω - x) * s) μ := (hU.sub (integrable_const x)).mul_const s
  have hlin : (∫ ω, (U ω - x) * s ∂μ) = 0 := by
    rw [integral_mul_const, integral_sub hU (integrable_const x), hmean]
    simp
  have heq (ω : Ω) : rationalFirstPrimeRiesz χ pole (U ω) =
      b + (U ω - x) * s + rationalFirstPrimeCurvature χ x (U ω) - (pole / 2) * (U ω - x) ^ 2 := by
    rw [rationalFirstPrimeRiesz_tangent χ pole x (U ω)]
    dsimp only [b, s]
    ring
  simp_rw [heq]
  have hb : Integrable (fun ω => b + (U ω - x) * s) μ := (integrable_const b).add hl
  have hbc : Integrable (fun ω => b + (U ω - x) * s + rationalFirstPrimeCurvature χ x (U ω)) μ :=
    hb.add hC
  rw [integral_sub hbc (hV.const_mul (pole / 2)),
    integral_add hb hC, integral_add (integrable_const b) hl,
    hlin, integral_const_mul]
  simp [b]

/-- A one-sided estimate for the unsmoothed signed prime sum. Only positive
prime coefficients enter the curvature majorant. The quadratic pole keeps its
negative variance correction in the upper bound on the deficit. -/
theorem rationalFirstPrimeRiesz_neg_le_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (χ : ℕ → ℝ) (pole x : ℝ) (U : Ω → ℝ)
    (hU : Integrable U μ) (hmean : ∫ ω, U ω ∂μ = x)
    (hV : Integrable (fun ω => (U ω - x) ^ 2) μ)
    (hC : Integrable (fun ω => rationalFirstPrimeCurvature χ x (U ω)) μ)
    (hP : Integrable (fun ω => rationalFirstPrimeCurvature (fun p => max (χ p) 0) x (U ω)) μ) :
    -rationalFirstPrimeRiesz χ pole x ≤ -(∫ ω, rationalFirstPrimeRiesz χ pole (U ω) ∂μ) +
      (∫ ω, rationalFirstPrimeCurvature (fun p => max (χ p) 0) x (U ω) ∂μ) -
      pole / 2 * (∫ ω, (U ω - x) ^ 2 ∂μ) := by
  have hle : (∫ ω, rationalFirstPrimeCurvature χ x (U ω) ∂μ) ≤
      ∫ ω, rationalFirstPrimeCurvature (fun p => max (χ p) 0) x (U ω) ∂μ := by
    apply integral_mono hC hP
    intro ω
    unfold rationalFirstPrimeCurvature
    apply Finset.sum_le_sum
    intro p hp
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_lt.le)
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog)
    split <;> exact le_max_right _ _
  rw [rationalFirstPrimeRiesz_integral μ χ pole x U hU hmean hV hC]
  linarith

/-- Apply the one-sided prime-curvature inequality to every physical fourth
power before taking its negative part. The mean - one multiplier can have
unbounded support. Its second centered moment is shared by all samples. -/
theorem rationalFirstPrimeRiesz_fourthPower_deficit_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (χ : ℕ → ℝ) (pole : ℝ) (J : ℕ) (Y : Ω → ℝ)
    (hY : Integrable Y μ) (hmean : ∫ ω, Y ω ∂μ = 1)
    (hV : Integrable (fun ω => (Y ω - 1) ^ 2) μ)
    (hC : ∀ j ∈ Icc 1 J, Integrable
      (fun ω => rationalFirstPrimeCurvature χ ((j : ℝ) ^ 4) ((j : ℝ) ^ 4 * Y ω)) μ)
    (hP : ∀ j ∈ Icc 1 J, Integrable (fun ω =>
      rationalFirstPrimeCurvature (fun p => max (χ p) 0) ((j : ℝ) ^ 4) ((j : ℝ) ^ 4 * Y ω)) μ) :
    (∑ j ∈ Icc 1 J, max (-rationalFirstPrimeRiesz χ pole ((j : ℝ) ^ 4)) 0) ≤
      ∑ j ∈ Icc 1 J, max (-(∫ ω, rationalFirstPrimeRiesz χ pole ((j : ℝ) ^ 4 * Y ω) ∂μ) +
        (∫ ω, rationalFirstPrimeCurvature (fun p => max (χ p) 0) ((j : ℝ) ^ 4) ((j : ℝ) ^ 4 * Y ω) ∂μ) -
        pole / 2 * (j : ℝ) ^ 8 * (∫ ω, (Y ω - 1) ^ 2 ∂μ)) 0 := by
  apply Finset.sum_le_sum
  intro j hj
  apply max_le_max_right
  let x := (j : ℝ) ^ 4
  have hcenter : (∫ ω, x * Y ω ∂μ) = x := by rw [integral_const_mul, hmean, mul_one]
  have heq (ω : Ω) : (x * Y ω - x) ^ 2 = x ^ 2 * (Y ω - 1) ^ 2 := by ring
  have hv : Integrable (fun ω => (x * Y ω - x) ^ 2) μ := by
    simp_rw [heq]
    exact hV.const_mul _
  have h := rationalFirstPrimeRiesz_neg_le_integral μ χ pole x (fun ω => x * Y ω)
    (hY.const_mul x) hcenter hv (hC j hj) (hP j hj)
  simp_rw [heq] at h
  rw [integral_const_mul] at h
  convert h using 1
  dsimp [x]
  ring

/-- For the actual primitive character of conductor four the positive prime
curvature is supported exactly on the progression one modulo four. -/
theorem rationalFirstPrimeCurvature_chiFour_positive (x y : ℝ) :
    rationalFirstPrimeCurvature (fun p => max (ZMod.χ₄ (p : ZMod 4) : ℝ) 0) x y =
      ∑ p ∈ ((range (⌈max x y⌉₊ + 1)).filter Nat.Prime).filter (fun p => p % 4 = 1),
        Real.log p * (if (p : ℝ) < x then max (p - y) 0 else max (y - p) 0) := by
  unfold rationalFirstPrimeCurvature
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [ZMod.χ₄_nat_eq_if_mod_four]
  by_cases hm : p % 4 = 1
  · have h2 : p % 2 ≠ 0 := by omega
    simp [hm, h2]
  · by_cases h2 : p % 2 = 0 <;> simp [hm, h2]

private theorem firstPrime_spaced_tents (P : Finset ℕ) (r : ℕ → ℝ) {d q : ℝ}
    (hq : 0 < q) (hd : 0 ≤ d)
    (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p ≤ d)
    (hs : ∀ p ∈ P, ∀ k ∈ P, p ≠ k → q ≤ |r p - r k|) :
    ∑ p ∈ P, (d - r p) ≤ d + d ^ 2 / (2 * q) := by
  let k (p : ℕ) := ⌊r p / q⌋₊
  let n := ⌊d / q⌋₊
  have hlo (p : ℕ) (hp : p ∈ P) : (k p : ℝ) * q ≤ r p :=
    (le_div_iff₀ hq).mp (Nat.floor_le (div_nonneg (hr p hp).1 hq.le))
  have hhi (p : ℕ) : r p < ((k p : ℝ) + 1) * q :=
    (div_lt_iff₀ hq).mp (Nat.lt_floor_add_one (r p / q))
  have hinj : Set.InjOn k (P : Set ℕ) := by
    intro p hp b hb h
    by_contra hn
    have ht := hs p hp b hb hn
    have hpl := hlo p hp
    have hbl := hlo b hb
    have hpu := hhi p
    have hbu := hhi b
    rw [h] at hpl hpu
    rw [le_abs] at ht
    rcases ht with h | h <;> nlinarith
  have hsub : P.image k ⊆ range (n + 1) := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hb
    apply mem_range.mpr
    have hk : k p ≤ n := Nat.floor_mono ((div_le_div_iff_of_pos_right hq).mpr ((hr p hp).2))
    omega
  have hn : (n : ℝ) * q ≤ d := (le_div_iff₀ hq).mp (Nat.floor_le (div_nonneg hd hq.le))
  have hcount : (∑ i ∈ range (n + 1), (i : ℝ)) * 2 = (n + 1) * (n : ℝ) := by
    have h := Finset.sum_range_id_mul_two (n + 1)
    simp only [Nat.add_sub_cancel] at h
    have hh := congrArg (fun v : ℕ => (v : ℝ)) h
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_add, Nat.cast_one] using hh
  calc
    _ ≤ ∑ p ∈ P, (d - (k p : ℝ) * q) := Finset.sum_le_sum (fun p hp => by linarith [hlo p hp])
    _ = ∑ i ∈ P.image k, (d - (i : ℝ) * q) := (Finset.sum_image (f := fun i : ℕ => d - (i : ℝ) * q) hinj).symm
    _ ≤ ∑ i ∈ range (n + 1), (d - (i : ℝ) * q) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro i hi _
      have hle : i ≤ n := by have := mem_range.mp hi; omega
      exact sub_nonneg.mpr ((mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hq.le).trans hn)
    _ ≤ _ := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      rw [← sub_le_iff_le_add']
      apply (le_div_iff₀ (by positivity : 0 < 2 * q)).mpr <| by
        nlinarith [sq_nonneg (d - (n : ℝ) * q), mul_nonneg (by exact_mod_cast (Nat.zero_le n) : (0 : ℝ) ≤ n) (sq_nonneg q),
          congrArg (fun x : ℝ => x * q ^ 2) hcount]

private theorem firstPrime_class_gap {p b q : ℕ} (h : p % q = b % q) (hne : p ≠ b) :
    (q : ℝ) ≤ |(p : ℝ) - b| := by
  have aux {m n : ℕ} (hmn : m < n) (hc : m % q = n % q) : (q : ℝ) ≤ (n : ℝ) - m := by
    have hdiv := (Nat.modEq_iff_dvd' hmn.le).mp hc
    have hu := Nat.le_of_dvd (Nat.sub_pos_of_lt hmn) hdiv
    have hh : q + m ≤ n := by omega
    have hr : (q : ℝ) + (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hh
    linarith
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hlt.le))]
    linarith [aux hlt h]
  · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hgt.le))]
    exact aux hgt h.symm

/-- An unconditional arithmetic bound on the local prime curvature in one
progression. A cutoff displacement of length d costs at most
log(max(2, x, y)) times d + d²/(2q), uniformly in both real endpoints. -/
theorem rationalFirstPrimeCurvature_residue_le (w : ℕ → ℝ) {q : ℕ} (hq : 0 < q) (a : ℕ)
    (hw : ∀ p, w p ≤ 1)
    (ha : ∀ p, Nat.Prime p → w p ≠ 0 → p % q = a) (x y : ℝ) :
    rationalFirstPrimeCurvature w x y ≤ Real.log (max 2 (max x y)) *
      (|y - x| + |y - x|^2 / (2 * (q : ℝ))) := by
  let P := (range (⌈max x y⌉₊ + 1)).filter Nat.Prime
  let A := P.filter (fun p => w p ≠ 0 ∧ min x y ≤ (p : ℝ) ∧ (p : ℝ) ≤ max x y)
  let K (p : ℕ) := if (p : ℝ) < x then max (p - y) 0 else max (y - p) 0
  let L := Real.log (max 2 (max x y))
  let r (p : ℕ) := |(p : ℝ) - x|
  let d := |y - x|
  have hL : 0 ≤ L := Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _))
  have inside {p : ℕ} (hp : p ∈ A) : min x y ≤ (p : ℝ) ∧ (p : ℝ) ≤ max x y :=
    (mem_filter.mp hp).2.2
  have geometry (p : ℕ) (hp : p ∈ A) : K p ≤ d - r p ∧ r p ≤ d := by
    rcases inside hp with ⟨hl, hu⟩
    dsimp only [K, d, r]
    rcases le_total x y with h | h
    · rw [min_eq_left h] at hl
      rw [max_eq_right h] at hu
      rw [ite_eq_right (not_lt.mpr hl), abs_of_nonneg (sub_nonneg.mpr h),
        abs_of_nonneg (sub_nonneg.mpr hl), max_eq_left (sub_nonneg.mpr hu)]
      constructor <;> linarith
    · rw [min_eq_right h] at hl
      rw [max_eq_left h] at hu
      rw [abs_of_nonpos (sub_nonpos.mpr h), abs_of_nonpos (sub_nonpos.mpr hu)]
      by_cases ht : (p : ℝ) < x
      · rw [ite_eq_left ht, max_eq_left (sub_nonneg.mpr hl)]
        constructor <;> linarith
      · rw [ite_eq_right ht, max_eq_right (sub_nonpos.mpr hl)]
        constructor <;> linarith
  have hsep (p : ℕ) (hp : p ∈ A) (b : ℕ) (hb : b ∈ A) (hne : p ≠ b) :
      (q : ℝ) ≤ |r p - r b| := by
    have hmod (k : ℕ) (hk : k ∈ A) : k % q = a :=
      ha k (mem_filter.mp (mem_filter.mp hk).1).2 (mem_filter.mp hk).2.1
    have hg := firstPrime_class_gap ((hmod p hp).trans (hmod b hb).symm) hne
    dsimp only [r]
    rcases le_total x y with h | h
    · have h1 := (inside hp).1
      have h2 := (inside hb).1
      rw [min_eq_left h] at h1 h2
      simpa [abs_of_nonneg (sub_nonneg.mpr h1), abs_of_nonneg (sub_nonneg.mpr h2)] using hg
    · have h1 := (inside hp).2
      have h2 := (inside hb).2
      rw [max_eq_left h] at h1 h2
      rw [abs_of_nonpos (sub_nonpos.mpr h1), abs_of_nonpos (sub_nonpos.mpr h2)]
      convert hg using 1
      rw [← abs_neg]
      congr 1
      ring
  have hcut : rationalFirstPrimeCurvature w x y = ∑ p ∈ A, w p * Real.log p * K p := by
    unfold rationalFirstPrimeCurvature
    change (∑ p ∈ P, w p * Real.log p * K p) = _
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    by_cases hw0 : w p = 0
    · simp [hw0]
    · have hout : ¬ (min x y ≤ (p : ℝ) ∧ (p : ℝ) ≤ max x y) :=
        fun ht => hn (mem_filter.mpr ⟨hp, hw0, ht⟩)
      have hk : K p = 0 := by
        dsimp [K]
        by_cases ht : (p : ℝ) < x
        · rw [ite_eq_left ht, max_eq_right]
          by_contra! hf
          exact hout ⟨(min_le_right x y).trans (by linarith), ht.le.trans (le_max_left _ _)⟩
        · rw [ite_eq_right ht, max_eq_right]
          by_contra! hf
          exact hout ⟨(min_le_left x y).trans (le_of_not_gt ht), (by linarith : (p : ℝ) ≤ y).trans (le_max_right _ _)⟩
      simp [hk]
  have hs := firstPrime_spaced_tents A r (by exact_mod_cast hq : (0 : ℝ) < q) (abs_nonneg (y - x))
    (fun p hp => ⟨abs_nonneg _, (geometry p hp).2⟩) hsep
  rw [hcut]
  calc
    _ ≤ ∑ p ∈ A, L * (d - r p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpr : Nat.Prime p := (mem_filter.mp (mem_filter.mp hp).1).2
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpr.one_lt.le
      have hlp : Real.log p ≤ L := Real.log_le_log (by linarith) ((inside hp).2.trans (le_max_right _ _))
      have hk : 0 ≤ K p := by dsimp [K]; split <;> exact le_max_right _ _
      have hcoef : w p * Real.log p ≤ L :=
        (mul_le_of_le_one_left (Real.log_nonneg hp1) (hw p)).trans hlp
      exact (mul_le_mul_of_nonneg_right hcoef hk).trans (mul_le_mul_of_nonneg_left (geometry p hp).1 hL)
    _ = L * (∑ p ∈ A, (d - r p)) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hs hL

/-- For a complex character modulo five taking the value i at two, the
positive real prime curvature has the single-progression cost with q = 5. -/
theorem rationalFirstPrimeCurvature_chiFive_le (χ : DirichletCharacter ℂ 5)
    (hχ : χ 2 = Complex.I) (x y : ℝ) :
    rationalFirstPrimeCurvature (fun p => max (χ (p : ZMod 5)).re 0) x y ≤
      Real.log (max 2 (max x y)) * (|y - x| + |y - x|^2 / 10) := by
  let : Nontrivial (ZMod 5) := ⟨⟨0,1, by decide⟩⟩
  have h3 : χ 3 = -Complex.I := by
    rw [show (3 : ZMod 5) = 2 * 2 * 2 by decide, map_mul, map_mul, hχ]
    simp
  have h4 : χ 4 = -1 := by
    rw [show (4 : ZMod 5) = 2 * 2 by decide, map_mul, hχ]
    simp
  have hv (k : ZMod 5) : max (χ k).re 0 = if k = 1 then 1 else 0 := by
    have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by decide +revert
    have hz := MulChar.map_zero χ
    rcases hc with h | h | h | h | h <;> subst k <;>
      norm_num [hz, hχ, h3, h4, show (0 : ZMod 5) ≠ 1 by decide] <;> decide
  have hw (p : ℕ) : max (χ (p : ZMod 5)).re 0 ≤ 1 := by rw [hv]; split <;> norm_num
  have ha (p : ℕ) (_ : Nat.Prime p) (hp : max (χ (p : ZMod 5)).re 0 ≠ 0) : p % 5 = 1 := by
    rw [hv] at hp
    split at hp
    · rename_i he
      simpa [show (1 : ZMod 5).val = 1 by decide] using congrArg ZMod.val he
    · contradiction
  convert rationalFirstPrimeCurvature_residue_le _ (by decide : 0 < 5) 1 hw ha x y using 1
  norm_num

end RiemannMasullo
