module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Weighted integrability from samples on polynomial grids

For the grid of positive integer powers `j^m`, a cell has length of order
`j^(m-1)`. A bound by the two neighboring samples and an integrable error therefore
reduces a one-sided Mellin moment to a weighted series of sample sizes.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory

namespace RiemannMasullo

private theorem powerGrid_integrableOn_Ioi_of_cells {u B : ℕ → ℝ} {f : ℝ → ℝ}
    (hu : Monotone u) (htop : ¬ BddAbove (range u)) (hf : Measurable f)
    (h : ∀ n : ℕ, ∀ x ∈ Ioc (u n) (u (n+1)), ‖f x‖ ≤ B n)
    (hB : Summable fun n ↦ (u (n+1)-u n)*B n) : IntegrableOn f (Ioi (u 0)) := by
  have hu' (n : ℕ) : u n ≤ u (n+1) := hu (Nat.le_succ n)
  have hconst (n : ℕ) : IntegrableOn (fun _ : ℝ ↦ B n) (Ioc (u n) (u (n+1))) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hbound (n : ℕ) : ∀ᵐ x ∂volume.restrict (Ioc (u n) (u (n+1))), ‖f x‖ ≤ B n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx using h n x hx
  have hi (n : ℕ) : IntegrableOn f (Ioc (u n) (u (n+1))) :=
    (hconst n).mono' hf.aestronglyMeasurable (hbound n)
  rw [← show (⋃ n : ℕ, Ioc (u n) (u (n+1))) = Ioi (u 0) from
    iUnion_Ioc_map_succ_eq_Ioi (fun n ↦ hu (Nat.zero_le n)) htop]
  apply integrableOn_iUnion_of_summable_integral_norm hi
  apply Summable.of_nonneg_of_le (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) _ hB
  intro n
  calc
    _ ≤ ∫ x in Ioc (u n) (u (n+1)), B n := integral_mono_ae (hi n).norm (hconst n) (hbound n)
    _ = _ := by rw [setIntegral_const, Real.volume_real_Ioc_of_le (hu' n), smul_eq_mul]

private theorem powerGrid_cell_length {x : ℝ} (hx : 1 ≤ x) (m : ℕ) :
    (x+1)^m-x^m ≤ (m:ℝ)*2^(m-1)*x^(m-1) := by
  have h₀ : 0 ≤ x := by linarith
  have hh := abs_pow_sub_pow_le (x+1) x m
  rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ h₀ (by linarith) m)),
    add_sub_cancel_left, abs_one, one_mul, abs_of_nonneg (by linarith : 0 ≤ x+1),
    abs_of_nonneg h₀, max_eq_left (by linarith)] at hh
  rw [mul_assoc, ← mul_pow]
  exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) _) (Nat.cast_nonneg m))

private theorem powerGrid_summable_two_endpoints {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {r : ℝ} (hr : r ≤ 0) (hs : Summable fun n : ℕ ↦ a n * (n:ℝ)^r) :
    Summable fun n : ℕ ↦ (a (n+1)+a (n+2))*((n:ℝ)+1)^r := by
  have hs₁ := (summable_nat_add_iff (f := fun n : ℕ ↦ a n * (n:ℝ)^r) 1).mpr hs
  have hs₂ := (summable_nat_add_iff (f := fun n : ℕ ↦ a n * (n:ℝ)^r) 2).mpr hs
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hs₁ hs₂
  apply Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (add_nonneg (ha _) (ha _)) (Real.rpow_nonneg (by positivity) _)) _ (hs₁.add (hs₂.mul_left (2^(-r))))
  intro n
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (n:ℝ)+2)
    (show (n:ℝ)+2 ≤ 2*((n:ℝ)+1) by linarith [Nat.cast_nonneg (α := ℝ) n]) hr
  have h2 : ((n:ℝ)+1)^r ≤ 2^(-r)*((n:ℝ)+2)^r := by
    rw [Real.mul_rpow (by norm_num) hn.le] at hh
    have hhh := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-r))
    rwa [← mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2), neg_add_cancel, Real.rpow_zero, one_mul] at hhh
  change _ ≤ a (n+1)*((n:ℝ)+1)^r+2^(-r)*(a (n+2)*((n:ℝ)+2)^r)
  nlinarith only [mul_le_mul_of_nonneg_left h2 (ha (n+2))]

/-- On the grid of positive `m`-th powers, two endpoint majorants suffice for
integrability with Mellin weight `x^(-s)`. The sample series uses one endpoint only. -/
theorem integrableOn_Ioi_mul_rpow_of_powerGrid {f : ℝ → ℝ} {a : ℕ → ℝ} {s : ℝ} {m : ℕ}
    (hm : 0 < m) (hs : 1 ≤ s) (hf : Measurable f) (ha : ∀ n, 0 ≤ a n)
    (hcell : ∀ j : ℕ, 1 ≤ j → ∀ x ∈ Ioc ((j:ℝ)^m) (((j:ℝ)+1)^m), ‖f x‖ ≤ a j + a (j+1))
    (hseries : Summable fun j : ℕ ↦ a j * (j:ℝ)^((m:ℝ)*(1-s)-1)) :
    IntegrableOn (fun x : ℝ ↦ f x * x^(-s)) (Ioi 1) := by
  let r := (m:ℝ)*(1-s)-1
  let u (n : ℕ) := ((n:ℝ)+1)^m
  let A (n : ℕ) := a (n+1)+a (n+2)
  let B (n : ℕ) := A n*((n:ℝ)+1)^((m:ℝ)*(-s))
  have hr : r ≤ 0 := by dsimp only [r]; nlinarith [mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m : (0:ℝ) ≤ m) (show 1-s ≤ 0 by linarith)]
  have hu : Monotone u := fun i j hij ↦ pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1) m
  have htop : ¬ BddAbove (range u) := by
    rintro ⟨v, hv⟩
    obtain ⟨n, hn⟩ := exists_nat_gt v
    have h₁ : 1 ≤ (n:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hh : (n:ℝ)+1 ≤ u n := by simpa [u] using (pow_le_pow_right₀ h₁ hm : ((n:ℝ)+1)^1 ≤ ((n:ℝ)+1)^m)
    have := hv (mem_range_self n)
    linarith
  have hweight (n : ℕ) : (u n)^(-s) = ((n:ℝ)+1)^((m:ℝ)*(-s)) := (Real.rpow_natCast_mul (by positivity) _ _).symm
  have hB₀ (n : ℕ) : 0 ≤ B n := mul_nonneg (add_nonneg (ha _) (ha _)) (Real.rpow_nonneg (by positivity) _)
  have hbound (n : ℕ) (x : ℝ) (hx : x ∈ Ioc (u n) (u (n+1))) :
      ‖f x*x^(-s)‖ ≤ B n := by
    have h₀ : 0 < u n := by dsimp [u]; positivity
    have hh := hcell (n+1) (by omega) x (by simpa [u, Nat.cast_add, Nat.cast_one, add_assoc] using hx)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (h₀.trans hx.1).le _)]
    exact mul_le_mul hh ((Real.rpow_le_rpow_of_nonpos h₀ hx.1.le (by linarith : -s ≤ 0)).trans_eq (hweight n))
      (Real.rpow_nonneg (h₀.trans hx.1).le _) (add_nonneg (ha _) (ha _))
  have hsum := (powerGrid_summable_two_endpoints ha hr hseries).mul_left ((m:ℝ)*2^(m-1))
  have hlen (n : ℕ) : u (n+1)-u n ≤ (m:ℝ)*2^(m-1)*((n:ℝ)+1)^(m-1) := by
    simpa [u, Nat.cast_add] using powerGrid_cell_length (x := (n:ℝ)+1) (by linarith [Nat.cast_nonneg (α := ℝ) n]) m
  have hbound' : Summable fun n ↦ (u (n+1)-u n)*B n := by
    apply Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (sub_nonneg.mpr (hu (Nat.le_succ n))) (hB₀ n)) _ hsum
    intro n
    have hn : 0 < (n:ℝ)+1 := by positivity
    have hp : ((n:ℝ)+1)^(m-1)*((n:ℝ)+1)^((m:ℝ)*(-s)) = ((n:ℝ)+1)^r := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hn, Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_one]
      congr 1
      dsimp [r]
      ring
    change _ ≤ ((m:ℝ)*2^(m-1))*(A n*((n:ℝ)+1)^r)
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_right (hlen n) (hB₀ n)
      _ = _ := by dsimp only [B]; rw [← hp]; ring
  simpa [u] using powerGrid_integrableOn_Ioi_of_cells (f := fun x : ℝ ↦ f x * x^(-s)) hu htop (by fun_prop) hbound hbound'

/-- A summable series of one-sided sample sizes controls the negative Mellin moment,
allowing an arbitrary integrable error between samples. -/
theorem integrableOn_Ioi_negPart_mul_rpow_of_powerGrid {f E : ℝ → ℝ} {a : ℕ → ℝ} {s : ℝ} {m : ℕ}
    (hm : 0 < m) (hs : 1 ≤ s) (hf : Measurable f) (he : Measurable E)
    (ha : ∀ n, 0 ≤ a n) (hE : IntegrableOn (fun x : ℝ ↦ E x * x^(-s)) (Ioi 1))
    (hcell : ∀ j : ℕ, 1 ≤ j → ∀ x ∈ Ioc ((j:ℝ)^m) (((j:ℝ)+1)^m),
      -f x ≤ a j+a (j+1)+E x)
    (hseries : Summable fun j : ℕ ↦ a j * (j:ℝ)^((m:ℝ)*(1-s)-1)) :
    IntegrableOn (fun x : ℝ ↦ max (-f x) 0 * x^(-s)) (Ioi 1) := by
  let g (x : ℝ) := max (-f x-E x) 0
  have hg : Measurable g := (hf.neg.sub he).max measurable_const
  have hg₀ (x : ℝ) : 0 ≤ g x := le_max_right _ _
  have hi := integrableOn_Ioi_mul_rpow_of_powerGrid hm hs hg ha (fun j hj x hx ↦ by
    rw [Real.norm_of_nonneg (hg₀ x)]
    exact max_le (by linarith [hcell j hj x hx]) (add_nonneg (ha _) (ha _))) hseries
  apply (hi.add hE.norm).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hw : 0 ≤ x^(-s) := Real.rpow_nonneg (zero_le_one.trans (le_of_lt (show 1 < x from hx))) _
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, abs_of_nonneg (le_max_right (-f x) 0)]
  rw [← add_mul]
  apply mul_le_mul_of_nonneg_right _ hw
  exact max_le (by linarith [le_max_left (-f x-E x) 0, le_abs_self (E x)]) (add_nonneg (hg₀ x) (abs_nonneg _))

private theorem powerGrid_summable_of_sum_majorant {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {r q : ℝ} (hr : 0 ≤ r) (hq : r < q)
    (h : (fun n : ℕ ↦ ∑ j ∈ Finset.Icc 1 n, a j) =O[atTop] fun n ↦ (n:ℝ)^r) :
    Summable fun j : ℕ ↦ a j * (j:ℝ)^(-q) := by
  have hs := LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := (q:ℂ)) h ha hr hq
  change Summable (LSeries.term (fun j ↦ (a j : ℂ)) (q:ℂ)) at hs
  apply hs.norm.congr_cofinite
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_gt_atTop 0] with j hj
  rw [LSeries.term_of_ne_zero hj.ne', norm_div, Complex.norm_real, Real.norm_of_nonneg (ha _),
    Complex.norm_natCast_cpow_of_pos hj, Complex.ofReal_re,
    Real.rpow_neg (Nat.cast_nonneg j), div_eq_mul_inv]

/-- An upper growth exponent for the cumulative sample sizes suffices. Individual
samples may exceed the average by an unbounded factor. -/
theorem integrableOn_Ioi_negPart_mul_rpow_of_powerGrid_sum {f E : ℝ → ℝ} {a : ℕ → ℝ}
    {s r : ℝ} {m : ℕ} (hm : 0 < m) (hs : 1 ≤ s) (hr : 0 ≤ r) (hrt : r < (m:ℝ)*(s-1)+1)
    (hf : Measurable f) (he : Measurable E) (ha : ∀ n, 0 ≤ a n)
    (hE : IntegrableOn (fun x : ℝ ↦ E x * x^(-s)) (Ioi 1))
    (hcell : ∀ j : ℕ, 1 ≤ j → ∀ x ∈ Ioc ((j:ℝ)^m) (((j:ℝ)+1)^m),
      -f x ≤ a j+a (j+1)+E x)
    (hsum : (fun n : ℕ ↦ ∑ j ∈ Finset.Icc 1 n, a j) =O[atTop] fun n ↦ (n:ℝ)^r) :
    IntegrableOn (fun x : ℝ ↦ max (-f x) 0 * x^(-s)) (Ioi 1) := by
  apply integrableOn_Ioi_negPart_mul_rpow_of_powerGrid hm hs hf he ha hE hcell
  rw [show (m:ℝ)*(1-s)-1 = -((m:ℝ)*(s-1)+1) by ring]
  exact powerGrid_summable_of_sum_majorant ha hr hrt hsum

end RiemannMasullo
