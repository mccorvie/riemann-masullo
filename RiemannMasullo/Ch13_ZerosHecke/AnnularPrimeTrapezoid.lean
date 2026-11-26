module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact annular trapezoids for a single prime Riesz weight

The annular fourth-power dilation used in the rational arithmetic comparison for
Theorem 12.5.1.1, pp. 519–520, gives half weight to both endpoints. A truncated
affine weight has a single possible knot. Summing to its integer part measures
the exact contribution of its fractional part.
-/

open Finset

@[expose] public noncomputable section

namespace RiemannMasullo

/-- The integral of the truncated affine weight `max (1 - u*v) 0` over `1 ≤ v ≤ 2`
for nonnegative `u`, written in its three polynomial and rational pieces. -/
def annularPrimeKernel (u : ℝ) : ℝ :=
  if u ≤ 1/2 then 1 - 3*u/2 else if u ≤ 1 then (1-u)^2/(2*u) else 0

/-- The trapezoidal weight on the integers from `N` through `2*N`. -/
def annularTrapWeight (N n : ℕ) : ℝ :=
  if n = N ∨ n = 2*N then 1/2 else 1

/-- The annular kernel vanishes at and above its upper endpoint. -/
theorem annularPrimeKernel_eq_zero_of_one_le {u : ℝ} (hu : 1 ≤ u) :
    annularPrimeKernel u = 0 := by
  rcases eq_or_lt_of_le hu with h | h
  · rw [← h]
    norm_num [annularPrimeKernel]
  · rw [annularPrimeKernel, ite_eq_right (by linarith : ¬u ≤ 1/2), ite_eq_right (not_le.mpr h)]

private theorem annularTrap_sum (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ) :
    ∑ n ∈ Icc N (2*N), annularTrapWeight N n * f n =
      (∑ n ∈ Icc N (2*N), f n) - (f N + f (2*N))/2 := by
  have hne : N ≠ 2*N := by omega
  have hpoint (n : ℕ) :
      annularTrapWeight N n * f n = f n - (if n = N then f N / 2 else 0) -
        (if n = 2*N then f (2*N) / 2 else 0) := by
    rcases eq_or_ne n N with rfl | h
    · simp [annularTrapWeight, hne]; ring
    rcases eq_or_ne n (2*N) with rfl | h'
    · simp [annularTrapWeight, hne.symm]; ring
    · simp [annularTrapWeight, h, h']
  simp_rw [hpoint]
  rw [sum_sub_distrib, sum_sub_distrib, sum_ite_eq', sum_ite_eq']
  have ha : N ∈ Icc N (2*N) := mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hb : 2*N ∈ Icc N (2*N) := mem_Icc.mpr ⟨by omega, le_rfl⟩
  rw [ite_eq_left ha, ite_eq_left hb]
  ring

private theorem annular_sum_affine (A B : ℕ) (h : A ≤ B) (z : ℝ) :
    (∑ n ∈ Icc A B, (z - n)) = ((B : ℝ) + 1 - A) * (z - ((A : ℝ) + B)/2) := by
  induction B, h using Nat.le_induction with
  | base => simp
  | succ B h ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

private theorem annularTrap_ramp (N : ℕ) (hN : 0 < N) (z : ℝ) :
    ∑ n ∈ Icc N (2*N), annularTrapWeight N n * max (z - n) 0 =
      if z ≤ N then 0 else if (2*N : ℕ) ≤ z then (N : ℝ) * (z - 3*N/2)
      else (z - N)^2/2 + Int.fract z * (1 - Int.fract z)/2 := by
  by_cases hzN : z ≤ N
  · rw [ite_eq_left hzN]
    apply sum_eq_zero
    intro n hn
    have h : (N : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    rw [max_eq_right (by linarith), mul_zero]
  rw [ite_eq_right hzN, annularTrap_sum N hN]
  have hNpos : 0 < z - N := sub_pos.mpr (lt_of_not_ge hzN)
  by_cases hb : ((2*N : ℕ) : ℝ) ≤ z
  · rw [ite_eq_left hb]
    have hlin (n : ℕ) (hn : n ∈ Icc N (2*N)) : max (z - n) 0 = z - n := by
      have h : (n : ℝ) ≤ ((2*N : ℕ) : ℝ) := by exact_mod_cast (mem_Icc.mp hn).2
      exact max_eq_left (by linarith)
    rw [sum_congr rfl hlin, max_eq_left hNpos.le, max_eq_left (sub_nonneg.mpr hb),
      annular_sum_affine N (2*N) (by omega)]
    push_cast
    ring
  · rw [ite_eq_right hb]
    let L := ⌊z⌋₊
    have hz : 0 ≤ z := le_trans (Nat.cast_nonneg _) (lt_of_not_ge hzN).le
    have hNL : N ≤ L := (Nat.le_floor_iff hz).mpr (lt_of_not_ge hzN).le
    have hLM : L < 2*N := (Nat.floor_lt hz).mpr (lt_of_not_ge hb)
    have hs : (∑ n ∈ Icc N (2*N), max (z - n) 0) = ∑ n ∈ Icc N L, (z - n) := by
      calc _ = ∑ n ∈ Icc N L, max (z - n) 0 := by
               symm
               apply sum_subset (Icc_subset_Icc_right hLM.le)
               intro n hn hout
               have hLn : L < n := by
                 have hNn := (mem_Icc.mp hn).1
                 by_contra! h
                 exact hout (mem_Icc.mpr ⟨hNn, h⟩)
               exact max_eq_right (sub_nonpos.mpr ((Nat.floor_lt hz).mp hLn).le)
           _ = _ := by
             apply sum_congr rfl
             intro n hn
             have h := (Nat.le_floor_iff hz).mp (mem_Icc.mp hn).2
             exact max_eq_left (sub_nonneg.mpr h)
    have hfract : Int.fract z = z - L := by rw [Int.fract, natCast_floor_eq_intCast_floor hz]
    rw [hs, annular_sum_affine N L hNL, max_eq_left hNpos.le,
      max_eq_right (sub_nonpos.mpr (lt_of_not_ge hb).le), hfract]
    ring

/-- The trapezoidal sum of the single coefficient at `p` agrees with the
scaled annular kernel up to the exact fractional-part correction at the
interior knot. The formula includes the boundary ratios one half and one. -/
theorem annularPrimeTrapezoid_identity (j p : ℕ) (hj : 1 ≤ j) (hp : 1 ≤ p) :
    (∑ n ∈ Icc (j^3) (2*j^3), annularTrapWeight (j^3) n *
      max ((j : ℝ)^4 - (p : ℝ)*n) 0) =
      (j : ℝ)^7 * annularPrimeKernel ((p : ℝ)/j) +
        (if j < 2*p ∧ p < j then (p : ℝ)*Int.fract ((j : ℝ)^4/p)*
          (1 - Int.fract ((j : ℝ)^4/p))/2 else 0) := by
  let z := (j : ℝ)^4 / p
  have hjr : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hpr : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hscale (n : ℕ) : max ((j : ℝ)^4 - (p : ℝ)*n) 0 = (p : ℝ)* max (z - n) 0 := by
    rw [mul_max_of_nonneg _ _ hpr.le, mul_zero]
    congr 1
    dsimp [z]
    field_simp
  have hsum : (∑ n ∈ Icc (j^3) (2*j^3), annularTrapWeight (j^3) n *
      max ((j : ℝ)^4 - (p : ℝ)*n) 0) =
      (p : ℝ) * ∑ n ∈ Icc (j^3) (2*j^3), annularTrapWeight (j^3) n * max (z-n) 0 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n _
    rw [hscale]
    ring
  rw [hsum, annularTrap_ramp (j^3) (pow_pos (by omega) 3)]
  have hlarge : z ≤ ((j^3 : ℕ) : ℝ) ↔ j ≤ p := by
    dsimp [z]
    rw [div_le_iff₀ hpr, Nat.cast_pow, show (j : ℝ)^4 = (j : ℝ)^3*j by ring,
      mul_le_mul_iff_right₀ (pow_pos hjr 3), Nat.cast_le]
  have hsmall : ((2*j^3 : ℕ) : ℝ) ≤ z ↔ 2*p ≤ j := by
    dsimp [z]
    rw [le_div_iff₀ hpr, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      show (2 : ℝ)*(j : ℝ)^3*p = (j : ℝ)^3*(2*p) by ring,
      show (j : ℝ)^4 = (j : ℝ)^3*j by ring, mul_le_mul_iff_right₀ (pow_pos hjr 3)]
    exact_mod_cast Iff.rfl
  have hhalf : (p : ℝ)/j ≤ 1/2 ↔ 2*p ≤ j := by
    rw [div_le_iff₀ hjr, ← Nat.cast_le (α := ℝ) (m := 2*p) (n := j)]
    push_cast
    constructor <;> intro h <;> linarith
  by_cases hjp : j ≤ p
  · rw [ite_eq_left (hlarge.mpr hjp), annularPrimeKernel_eq_zero_of_one_le
      ((one_le_div hjr).mpr (by exact_mod_cast hjp)), ite_eq_right (by omega : ¬(j < 2*p ∧ p < j))]
    ring
  rw [ite_eq_right (mt hlarge.mp hjp), annularPrimeKernel]
  by_cases h2 : 2*p ≤ j
  · rw [ite_eq_left (hsmall.mpr h2), ite_eq_left (hhalf.mpr h2),
      ite_eq_right (by omega : ¬(j < 2*p ∧ p < j))]
    dsimp [z]
    push_cast
    field_simp
    ring
  · rw [ite_eq_right (mt hsmall.mp h2), ite_eq_right (mt hhalf.mp h2),
      ite_eq_left ((div_le_one hjr).mpr (by exact_mod_cast (lt_of_not_ge hjp).le)),
      ite_eq_left (by omega : j < 2*p ∧ p < j)]
    dsimp [z]
    push_cast
    field_simp

end RiemannMasullo
