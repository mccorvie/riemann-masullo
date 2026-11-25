module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Centered rounding at square cutoffs

Summing a cumulative prime error at the cutoffs `1², …, K²` introduces a centered
square-root sawtooth. At a perfect square the jump is included in the prefix.
-/

public noncomputable section

open Finset MeasureTheory

namespace RiemannMasullo

/-- The centered rounding error for square sampling, equal to `-1/2` at a square. -/
@[expose] def rationalSquarePrefixSaw (x : ℝ) : ℝ :=
  (⌈Real.sqrt x⌉₊ : ℝ) - Real.sqrt x - 1 / 2

/-- A square is counted at its own cutoff, including the endpoint of the last jump. -/
@[simp] theorem rationalSquarePrefixSaw_sq (n : ℕ) :
    rationalSquarePrefixSaw ((n : ℝ)^2) = -(1/2 : ℝ) := by
  simp [rationalSquarePrefixSaw, Real.sqrt_sq (Nat.cast_nonneg n)]

/-- The centered rounding cost of an individual prime or density value is at most one half. -/
theorem abs_rationalSquarePrefixSaw_le (x : ℝ) : |rationalSquarePrefixSaw x| ≤ 1/2 := by
  obtain h₁ := Nat.le_ceil (Real.sqrt x)
  obtain h₂ := Nat.ceil_lt_add_one (Real.sqrt_nonneg x)
  rw [rationalSquarePrefixSaw, abs_le]
  constructor <;> linarith

private theorem squarePrefix_count (K : ℕ) {x : ℝ} (hx : 1 ≤ x)
    (hxK : x ≤ (K : ℝ) ^ 2) (a : ℝ) :
    (∑ k ∈ Icc 1 K, if x ≤ (k : ℝ) ^ 2 then a else 0) =
      ((K : ℝ) - Real.sqrt x + 1 / 2 - rationalSquarePrefixSaw x) * a := by
  have hpos : 1 ≤ ⌈Real.sqrt x⌉₊ := by
    have h := Nat.le_ceil (Real.sqrt x)
    have hs : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx
    exact_mod_cast hs.trans h
  have hceil (k : ℕ) : ⌈Real.sqrt x⌉₊ ≤ k ↔ x ≤ (k : ℝ)^2 := by
    rw [Nat.ceil_le, Real.sqrt_le_iff]
    simp
  have hK := (hceil K).2 hxK
  have heq : (Icc 1 K).filter (fun k : ℕ ↦ x ≤ (k : ℝ)^2) = Icc ⌈Real.sqrt x⌉₊ K := by
    ext k
    simp only [mem_filter, mem_Icc, ← hceil]
    omega
  rw [← sum_filter, heq, sum_const, Nat.card_Icc, nsmul_eq_mul,
    Nat.cast_sub (by omega), Nat.cast_add_one, rationalSquarePrefixSaw]
  ring


private theorem squarePrefix_atomic (a : ℕ → ℝ) (K : ℕ) :
    (∑ k ∈ Icc 1 K, ∑ n ∈ Icc 1 (k ^ 2), a n) =
      ∑ n ∈ Icc 1 (K ^ 2),
        ((K : ℝ) - Real.sqrt n + 1 / 2 - rationalSquarePrefixSaw n) * a n := by
  have hprefix {k : ℕ} (hk : k ∈ Icc 1 K) :
      (∑ n ∈ Icc 1 (k ^ 2), a n) =
        ∑ n ∈ Icc 1 (K ^ 2), if (n : ℝ) ≤ (k : ℝ)^2 then a n else 0 := by
    rw [← sum_filter]
    have hkk := Nat.pow_le_pow_left (mem_Icc.mp hk).2 2
    congr 1
    ext n
    have hcast : (n : ℝ) ≤ (k : ℝ)^2 ↔ n ≤ k^2 := by exact_mod_cast Iff.rfl
    simp only [mem_Icc, mem_filter, hcast]
    omega
  rw [sum_congr rfl (fun k hk ↦ hprefix hk), sum_comm]
  refine sum_congr rfl fun n hn ↦ ?_
  apply squarePrefix_count
  · exact_mod_cast (mem_Icc.mp hn).1
  · exact_mod_cast (mem_Icc.mp hn).2



private theorem squarePrefix_density {K : ℕ} (hK : 1 ≤ K) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Set.Ioc 1 ((K : ℝ)^2))) :
    (∑ k ∈ Icc 1 K, ∫ x in (1 : ℝ)..(k : ℝ)^2, f x) =
      ∫ x in (1 : ℝ)..(K : ℝ)^2,
        ((K : ℝ) - Real.sqrt x + 1 / 2 - rationalSquarePrefixSaw x) * f x := by
  have h1K : (1 : ℝ) ≤ (K : ℝ)^2 := by exact_mod_cast Nat.one_le_pow 2 K hK
  rw [intervalIntegral.integral_of_le h1K]
  let S := Set.Ioc 1 ((K : ℝ)^2)
  have hterm {k : ℕ} (hk : k ∈ Icc 1 K) :
      (∫ x in (1 : ℝ)..(k : ℝ)^2, f x) =
        ∫ x in S, (Set.Iic ((k : ℝ)^2)).indicator f x := by
    rw [intervalIntegral.integral_of_le (by exact_mod_cast Nat.one_le_pow 2 k (mem_Icc.mp hk).1),
      setIntegral_indicator measurableSet_Iic]
    have hkK : (k : ℝ)^2 ≤ (K : ℝ)^2 := by exact_mod_cast Nat.pow_le_pow_left (mem_Icc.mp hk).2 2
    have heq : S ∩ Set.Iic ((k : ℝ)^2) = Set.Ioc 1 ((k : ℝ)^2) := by
      ext x
      change (1 < x ∧ x ≤ (K : ℝ)^2) ∧ x ≤ (k : ℝ)^2 ↔ _
      simp only [Set.mem_Ioc]
      grind
    rw [heq]
  rw [sum_congr rfl (fun k hk ↦ hterm hk), ← integral_finsetSum]
  · apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    simpa only [Set.indicator_apply, Set.mem_Iic] using
      squarePrefix_count K hx.1.le hx.2 (f x)
  · exact fun k _ ↦ hf.indicator measurableSet_Iic



private theorem squarePrefix_tail_integral {K x : ℝ} (hx : 1 ≤ x) (hK : 1 ≤ K)
    (hxK : x ≤ K^2) (a : ℝ) :
    (∫ u in Set.Icc 1 K, (Set.Ici (Real.sqrt x)).indicator (fun _ ↦ a) u) =
      (K - Real.sqrt x) * a := by
  have hs : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx
  have heq : Set.Icc 1 K ∩ Set.Ici (Real.sqrt x) = Set.Icc (Real.sqrt x) K := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
    grind
  have hsK := (Real.sqrt_le_left (by linarith : 0 ≤ K)).2 hxK
  rw [setIntegral_indicator measurableSet_Ici, heq, setIntegral_const, measureReal_def,
    Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hsK), smul_eq_mul]



private theorem squarePrefix_atomic_integral (a : ℕ → ℝ) {K : ℕ} (hK : 1 ≤ K) :
    IntervalIntegrable (fun u : ℝ ↦ ∑ n ∈ Icc 1 ⌊u^2⌋₊, a n) volume 1 K ∧
      (∫ u in (1 : ℝ)..K, ∑ n ∈ Icc 1 ⌊u^2⌋₊, a n) =
        ∑ n ∈ Icc 1 (K^2), ((K : ℝ) - Real.sqrt n) * a n := by
  have hr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  let g (n : ℕ) := (Set.Ici (Real.sqrt n)).indicator (fun _ : ℝ ↦ a n)
  have hfun {u : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) K) :
      (∑ n ∈ Icc 1 ⌊u^2⌋₊, a n) = ∑ n ∈ Icc 1 (K^2), g n u := by
    have hu₀ : 0 ≤ u := zero_le_one.trans hu.1
    have hum : ⌊u^2⌋₊ ≤ K^2 := by
      apply Nat.le_of_lt_succ
      rw [Nat.floor_lt (sq_nonneg u), Nat.cast_succ, Nat.cast_pow]
      nlinarith [hu.2, sq_le_sq' (by linarith : -(K : ℝ) ≤ u) hu.2]
    simp only [g, Set.indicator_apply, Set.mem_Ici, Real.sqrt_le_left hu₀, ← Nat.le_floor_iff (sq_nonneg u)]
    rw [← sum_filter]
    congr 1
    ext n
    simp only [mem_Icc, mem_filter]
    omega
  have hint (n : ℕ) : IntegrableOn (g n) (Set.Icc 1 (K : ℝ)) := by
    apply Integrable.indicator _ measurableSet_Ici
    exact integrableOn_const (by simp)
  constructor
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hr).2
    exact (integrable_finsetSum _ fun n _ ↦ hint n).congr
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun u hu ↦ (hfun hu).symm))
  · rw [intervalIntegral.integral_of_le hr, ← integral_Icc_eq_integral_Ioc,
      setIntegral_congr_fun measurableSet_Icc (fun u hu ↦ hfun hu), integral_finsetSum _ (fun n _ ↦ hint n)]
    refine sum_congr rfl fun n hn ↦ squarePrefix_tail_integral ?_ hr ?_ (a n)
    · exact_mod_cast (mem_Icc.mp hn).1
    · exact_mod_cast (mem_Icc.mp hn).2



private theorem squarePrefix_atomic_correction (a : ℕ → ℝ) {K : ℕ} (hK : 1 ≤ K) :
    (∑ k ∈ Icc 1 K, ∑ n ∈ Icc 1 (k^2), a n) -
      (∫ u in (1 : ℝ)..K, ∑ n ∈ Icc 1 ⌊u^2⌋₊, a n) =
      1/2 * (∑ n ∈ Icc 1 (K^2), a n) -
        ∑ n ∈ Icc 1 (K^2), rationalSquarePrefixSaw n * a n := by
  rw [squarePrefix_atomic, (squarePrefix_atomic_integral a hK).2, mul_sum,
    ← sum_sub_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun _ _ ↦ by ring

/-- The discrete first-prime compensator summed at square cutoffs differs from its
Riesz mean by half of its endpoint value minus the centered rounding term. -/
theorem rationalPrimeSquarePrefix_discrete (w : ℝ → ℝ) {K : ℕ} (hK : 1 ≤ K) :
    let a (n : ℕ) := ((if n.Prime then Real.log n else 0) - 1) * w (Real.log n)
    (∑ k ∈ Icc 1 K, ∑ n ∈ Icc 1 (k^2), a n) -
      (∫ u in (1 : ℝ)..K, ∑ n ∈ Icc 1 ⌊u^2⌋₊, a n) =
      1/2 * (∑ n ∈ Icc 1 (K^2), a n) -
        ∑ n ∈ Icc 1 (K^2), rationalSquarePrefixSaw n * a n := by
  intro a
  exact squarePrefix_atomic_correction a hK



private theorem squarePrefix_density_integral {K : ℕ} (hK : 1 ≤ K) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Icc 1 ((K : ℝ)^2))) :
    IntervalIntegrable (fun u : ℝ ↦ ∫ x in (1 : ℝ)..u^2, f x) volume 1 K ∧
      (∫ u in (1 : ℝ)..K, ∫ x in (1 : ℝ)..u^2, f x) =
        ∫ x in (1 : ℝ)..(K : ℝ)^2, ((K : ℝ) - Real.sqrt x) * f x := by
  have hr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hr₂ : (1 : ℝ) ≤ (K : ℝ)^2 := by exact_mod_cast Nat.one_le_pow 2 K hK
  let μ := volume.restrict (Set.Icc 1 (K : ℝ))
  let ν := volume.restrict (Set.Icc 1 ((K : ℝ)^2))
  let g (u x : ℝ) := if Real.sqrt x ≤ u then f x else 0
  have hint : Integrable (Function.uncurry g) (μ.prod ν) := by
    change Integrable (({p : ℝ × ℝ | Real.sqrt p.2 ≤ p.1}).indicator (fun p ↦ f p.2)) _
    exact (hf.comp_snd μ).indicator (measurableSet_le (Real.continuous_sqrt.measurable.comp measurable_snd)
      measurable_fst)
  have hinner {u : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) K) :
      (∫ x, g u x ∂ν) = ∫ x in (1 : ℝ)..u^2, f x := by
    have hu₀ : 0 ≤ u := zero_le_one.trans hu.1
    have hu1 : 1 ≤ u^2 := by nlinarith [hu.1, sq_nonneg (u-1)]
    have huK : u^2 ≤ (K : ℝ)^2 := sq_le_sq' (by linarith [hu.1]) hu.2
    have hgf : g u = (Set.Iic (u^2)).indicator f := by
      funext x
      simp [g, Set.indicator_apply, Real.sqrt_le_left hu₀]
    rw [hgf, intervalIntegral.integral_of_le hu1, ← integral_Icc_eq_integral_Ioc]
    change (∫ x in Set.Icc 1 ((K : ℝ)^2), (Set.Iic (u^2)).indicator f x) = _
    rw [setIntegral_indicator measurableSet_Iic]
    have heq : Set.Icc 1 ((K : ℝ)^2) ∩ Set.Iic (u^2) = Set.Icc 1 (u^2) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
      grind
    rw [heq]
  constructor
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hr).2
    exact hint.integral_prod_left.congr
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun u hu ↦ hinner hu))
  · rw [intervalIntegral.integral_of_le hr, ← integral_Icc_eq_integral_Ioc,
      setIntegral_congr_fun measurableSet_Icc (fun u hu ↦ (hinner hu).symm)]
    change (∫ u, ∫ x, g u x ∂ν ∂μ) = _
    rw [integral_integral_swap hint, intervalIntegral.integral_of_le hr₂, ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    exact squarePrefix_tail_integral hx.1 hr hx.2 (f x)



private theorem squarePrefix_density_correction {K : ℕ} (hK : 1 ≤ K) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 1 ((K : ℝ)^2))) :
    (∑ k ∈ Icc 1 K, ∫ x in (1 : ℝ)..(k : ℝ)^2, f x) -
        (∫ u in (1 : ℝ)..K, ∫ x in (1 : ℝ)..u^2, f x) =
      1/2 * (∫ x in (1 : ℝ)..(K : ℝ)^2, f x) -
        ∫ x in (1 : ℝ)..(K : ℝ)^2, rationalSquarePrefixSaw x * f x := by
  have hr : (1 : ℝ) ≤ (K : ℝ)^2 := by exact_mod_cast Nat.one_le_pow 2 K hK
  have hi := hf.intervalIntegrable_of_Icc hr (μ := volume)
  have hs : Measurable rationalSquarePrefixSaw := by
    unfold rationalSquarePrefixSaw
    fun_prop
  have hq : IntervalIntegrable (fun x ↦ rationalSquarePrefixSaw x * f x) volume 1 ((K : ℝ)^2) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hr).2
    exact hf.integrableOn_Icc.bdd_mul hs.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ abs_rationalSquarePrefixSaw_le x)
  have hbase : IntervalIntegrable (fun x ↦ ((K : ℝ) - Real.sqrt x) * f x) volume 1 ((K : ℝ)^2) :=
    ((continuousOn_const.sub Real.continuous_sqrt.continuousOn).mul hf).intervalIntegrable_of_Icc hr
  have h := intervalIntegral.integral_add hbase ((hi.const_mul (1/2)).sub hq)
  rw [squarePrefix_density hK f hi.1, (squarePrefix_density_integral hK hf.integrableOn_Icc).2]
  have heq : (fun x ↦ ((K : ℝ) - Real.sqrt x + 1 / 2 - rationalSquarePrefixSaw x) * f x) =
      fun x ↦ ((K : ℝ) - Real.sqrt x) * f x + (1 / 2 * f x - rationalSquarePrefixSaw x * f x) := by
    funext; ring
  rw [heq, h, intervalIntegral.integral_sub (hi.const_mul (1/2)) hq,
    intervalIntegral.integral_const_mul]
  ring



/-- Exact square sampling for the first-prime sum minus its continuous density.
The variable `u` parametrizes the square-root Riesz mean by the cutoff `u²`. -/
theorem rationalPrimeSquarePrefix_integral (w : ℝ → ℝ) (hw : Continuous w) {K : ℕ} (hK : 1 ≤ K) :
    let f (x : ℝ) := w (Real.log x)
    let a (n : ℕ) := if n.Prime then Real.log n * f n else 0
    let E (X : ℝ) := (∑ n ∈ Icc 1 ⌊X⌋₊, a n) - ∫ x in (1 : ℝ)..X, f x
    (∑ k ∈ Icc 1 K, E ((k : ℝ)^2)) - (∫ u in (1 : ℝ)..K, E (u^2)) =
      1/2 * E ((K : ℝ)^2) -
        ((∑ n ∈ Icc 1 (K^2), rationalSquarePrefixSaw n * a n) -
          ∫ x in (1 : ℝ)..(K : ℝ)^2, rationalSquarePrefixSaw x * f x) := by
  intro f a E
  have hf : ContinuousOn f (Set.Icc 1 ((K : ℝ)^2)) :=
    hw.comp_continuousOn (Real.continuousOn_log.mono fun x hx ↦ ne_of_gt (zero_lt_one.trans_le hx.1))
  have hfloor (n : ℕ) : ⌊(n : ℝ)^2⌋₊ = n^2 := by rw [← Nat.cast_pow, Nat.floor_natCast]
  simp only [E, hfloor, sum_sub_distrib]
  rw [intervalIntegral.integral_sub (squarePrefix_atomic_integral a hK).1
    (squarePrefix_density_integral hK hf.integrableOn_Icc).1]
  linarith only [squarePrefix_atomic_correction a hK, squarePrefix_density_correction hK hf]


end RiemannMasullo
