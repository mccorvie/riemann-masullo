module

public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-! # Finite Dirichlet polynomials with an ordinary Möbius mollifier

The two truncations have independent lengths. Below their common cutoff
Möbius inversion cancels every coefficient after the first. Above the
cutoff the squared divisor bound yields a uniform tail in the half-plane.
-/

@[expose] public noncomputable section

open Classical Filter
open scoped Topology

namespace RiemannMasullo

local notation "divisorPairs(" n ")" => ({d : ℕ // d ∈ Nat.divisors (n : ℕ)} × {d : ℕ // d ∈ Nat.divisors (n : ℕ)})

private def fourFactors (i : Σ n, divisorPairs(n)) : (ℕ × ℕ) × (ℕ × ℕ) :=
  let d := i.2.1.val
  let e := i.2.2.val
  ((d.gcd e, d / d.gcd e), (e / d.gcd e, i.1 / d.lcm e))

private theorem fourFactors_spec (i : Σ n, divisorPairs(n)) :
    (fourFactors i).1.1 * (fourFactors i).1.2 = i.2.1.val ∧
    (fourFactors i).1.1 * (fourFactors i).2.1 = i.2.2.val ∧
    ((fourFactors i).1.1 * (fourFactors i).1.2) * ((fourFactors i).2.1 * (fourFactors i).2.2) = i.1 := by
  rcases i with ⟨n, ⟨d, hd⟩, ⟨e, he⟩⟩
  obtain ⟨hdn, hn⟩ := Nat.mem_divisors.mp hd
  obtain ⟨hen, _⟩ := Nat.mem_divisors.mp he
  have h₁ := Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)
  have h₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)
  have hpos := Nat.gcd_pos_of_pos_left e (Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn))
  have h₃ : d * (e / d.gcd e) = d.lcm e := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [← Nat.mul_assoc, Nat.mul_comm (d.gcd e) d, Nat.mul_assoc, h₂, Nat.gcd_mul_lcm]
  refine ⟨h₁, h₂, ?_⟩
  change (d.gcd e * (d / d.gcd e)) * ((e / d.gcd e) * (n / d.lcm e)) = n
  rw [h₁, ← mul_assoc, h₃, Nat.mul_div_cancel' (Nat.lcm_dvd hdn hen)]

private theorem fourFactors_injective : Function.Injective fourFactors := by
  intro i j h
  obtain ⟨hi, hi', hiN⟩ := fourFactors_spec i
  obtain ⟨hj, hj', hjN⟩ := fourFactors_spec j
  rw [h] at hi hi' hiN
  rcases i with ⟨n, d, e⟩
  rcases j with ⟨m, d', e'⟩
  obtain rfl : n = m := hiN.symm.trans hjN
  congr 1
  exact Prod.ext (Subtype.ext (hi.symm.trans hj)) (Subtype.ext (hi'.symm.trans hj'))

/-- The squared divisor function has an absolutely convergent Dirichlet series
throughout the open half-plane of absolute convergence of the zeta function. -/
theorem summable_card_divisors_sq_mul_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ ↦ (n.divisors.card : ℝ)^2 * (n : ℝ)^(-s)) := by
  let w (n : ℕ) := (n : ℝ)^(-s)
  have hw : Summable w := Real.summable_nat_rpow.mpr (by linarith)
  have hm (a b : ℕ) : w (a*b) = w a * w b := by simp [w, Real.mul_rpow]
  have hp := hw.mul_of_nonneg hw (fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
  let P (p : ℕ × ℕ) := w p.1 * w p.2
  have hP : Summable P := hp
  have hn (p : ℕ × ℕ) : 0 ≤ P p := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h4 := (hP.mul_of_nonneg hP hn hn).comp_injective fourFactors_injective
  have h : Summable (fun i : Σ n, divisorPairs(n) ↦ w i.1) := h4.congr (fun i ↦ by
    dsimp only [Function.comp_def, P]
    rw [← hm, ← hm, ← hm, (fourFactors_spec i).2.2])
  have H := h.sigma
  convert H using 1
  funext n
  simp [w, tsum_fintype, pow_two, mul_assoc]

end RiemannMasullo

namespace RiemannMasullo.ConductorCylinder

set_option quotPrecheck false
local notation "factorPairs" => (fun K N n : ℕ ↦
  ((Finset.Icc 1 K ×ˢ Finset.Icc 1 N).filter (fun p ↦ p.1*p.2=n)))

/-- Coefficient of the product of the length-`N` zeta truncation and the
length-`K` ordinary Möbius mollifier. -/
def mollifiedCoeff (K N n : ℕ) : ℂ := ∑ p ∈ factorPairs K N n, (ArithmeticFunction.moebius p.1 : ℂ)

private theorem pairs_subset (K N n : ℕ) : factorPairs K N n ⊆ n.divisorsAntidiagonal := by
  intro ⟨d,j⟩ h
  obtain ⟨hp,he⟩ := Finset.mem_filter.mp h
  obtain ⟨hd,hj⟩ := Finset.mem_product.mp hp
  have hd₀ := (Finset.mem_Icc.mp hd).1
  have hj₀ := (Finset.mem_Icc.mp hj).1
  exact Nat.mem_divisorsAntidiagonal.mpr ⟨he,he ▸ Nat.mul_ne_zero (by omega) (by omega)⟩

/-- Each surviving divisor contributes at most one in absolute value. -/
theorem norm_mollifiedCoeff_le (K N n : ℕ) : ‖mollifiedCoeff K N n‖ ≤ n.divisors.card := by
  apply (norm_sum_le ..).trans
  calc _ ≤ ∑ _ ∈ factorPairs K N n, (1:ℝ) := by
          apply Finset.sum_le_sum
          intro p _
          rcases ArithmeticFunction.moebius_eq_or p.1 with h | h | h <;> simp [h]
       _ ≤ _ := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          exact_mod_cast (Finset.card_le_card (pairs_subset K N n)).trans_eq (by
            rw [← Nat.map_div_right_divisors, Finset.card_map])

/-- Below both cutoffs, the product has the coefficients of the constant polynomial one. -/
theorem mollifiedCoeff_low {K N n : ℕ} (hK : n ≤ K) (hN : n ≤ N) :
    mollifiedCoeff K N n = if n=1 then 1 else 0 := by
  have he : factorPairs K N n = n.divisorsAntidiagonal := by
    apply Finset.Subset.antisymm (pairs_subset ..)
    intro p hp
    have hd := Nat.mem_divisors.mp (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
    have hj := Nat.mem_divisors.mp (Nat.snd_mem_divisors_of_mem_antidiagonal hp)
    have hd₀ := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp
    have hj₀ := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega,(Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2) hd.1).trans hK⟩,
       Finset.mem_Icc.mpr ⟨by omega,(Nat.le_of_dvd (Nat.pos_of_ne_zero hj.2) hj.1).trans hN⟩⟩,
      (Nat.mem_divisorsAntidiagonal.mp hp).1⟩
  have h := DFunLike.congr_fun (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ)) n
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h
  rw [mollifiedCoeff, he, ← h]
  apply Finset.sum_congr rfl
  intro p hp
  simp [Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp]

/-- Dirichlet polynomial for an arithmetic coefficient function at level `q`. -/
def conductorPolynomial {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (A : ℕ → ℂ) (S : Finset ℕ) : ℂ :=
  ∑ n ∈ S, A n * χ (n : ZMod q) * (n : ℂ)^(-s)

/-- The ordinary truncated Möbius sum twisted by the Dirichlet character. -/
def mobiusMollifier {q : ℕ} (χ : DirichletCharacter ℂ q) (K : ℕ) (s : ℂ) : ℂ :=
  conductorPolynomial χ s (fun n ↦ (ArithmeticFunction.moebius n : ℂ)) (Finset.Icc 1 K)

/-- The finite Dirichlet series up to the given integer cutoff. -/
def conductorTruncation {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℂ) : ℂ :=
  conductorPolynomial χ s (fun _ ↦ 1) (Finset.Icc 1 N)

/-- Finite Dirichlet convolution groups the product by its integer frequency. -/
theorem conductorTruncation_mul_mollifier {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (K N : ℕ) :
    conductorTruncation χ N s * mobiusMollifier χ K s =
      conductorPolynomial χ s (mollifiedCoeff K N) (Finset.Icc 1 (K*N)) := by
  let F (n : ℕ) := χ (n : ZMod q) * (n : ℂ)^(-s)
  have hF (a b : ℕ) : F (a*b) = F a * F b := by
    dsimp only [F]
    rw [Nat.cast_mul, Nat.cast_mul, map_mul, Complex.natCast_mul_natCast_cpow]; ring
  let S := Finset.Icc 1 K ×ˢ Finset.Icc 1 N
  let B (p : ℕ × ℕ) := (ArithmeticFunction.moebius p.1 : ℂ) * F (p.1*p.2)
  have hmem (p : ℕ × ℕ) (hp : p ∈ S) : p.1*p.2 ∈ Finset.Icc 1 (K*N) := by
    obtain ⟨hd,hj⟩ := Finset.mem_product.mp hp
    obtain ⟨h₁,h₂⟩ := Finset.mem_Icc.mp hd
    obtain ⟨h₃,h₄⟩ := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos h₁ h₃,Nat.mul_le_mul h₂ h₄⟩
  calc _ = ∑ p ∈ S, B p := by
          rw [mul_comm, Finset.sum_product]
          unfold mobiusMollifier conductorTruncation conductorPolynomial
          simp only [Finset.sum_mul, Finset.mul_sum, one_mul, B, hF, F]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
       _ = ∑ n ∈ Finset.Icc 1 (K*N), ∑ p ∈ factorPairs K N n, B p :=
          (Finset.sum_fiberwise_of_maps_to hmem B).symm
       _ = _ := by
          unfold conductorPolynomial
          apply Finset.sum_congr rfl
          intro n _
          simp only [mollifiedCoeff, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro p hp
          dsimp only [B, F]
          rw [(Finset.mem_filter.mp hp).2]
          ring

open Finset

private theorem polynomial_term_norm {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ‖(n : ℂ)^(-s)‖ = (n:ℝ)^(-s.re) := by
  exact Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn) _

/-- The length of the ordinary mollifier bounds its norm on the closed right half-plane. -/
theorem norm_mobiusMollifier_le {q : ℕ} (χ : DirichletCharacter ℂ q) (K : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖mobiusMollifier χ K s‖ ≤ K := by
  unfold mobiusMollifier conductorPolynomial
  apply (norm_sum_le ..).trans
  calc _ ≤ ∑ _ ∈ Icc 1 K, (1:ℝ) := by
          apply sum_le_sum
          intro n hn
          have hn' := (mem_Icc.mp hn).1
          have hm : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
            rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]
          simp only [norm_mul,polynomial_term_norm hn' s]
          have he := Real.rpow_le_one_of_one_le_of_nonpos (show 1 ≤ (n:ℝ) by exact_mod_cast hn') (neg_nonpos.mpr hs)
          calc _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul hm (χ.norm_le_one _) (norm_nonneg _) zero_le_one)
                 he (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by norm_num)
               _ = _ := by norm_num
       _ = _ := by simp

/-- Uniform coefficient-square tail, including both truncations. -/
theorem exists_mollifiedCoeff_sq_tail_bound {d e : ℝ} (hd : 0 < d) (he : 0 ≤ e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K N D : ℕ) (S : Finset ℕ), 0 < D → (∀ n ∈ S, D ≤ n) →
      ∀ s : ℂ, 1+d+e ≤ 2*s.re →
        ∑ n ∈ S, ‖mollifiedCoeff K N n * (n : ℂ)^(-s)‖^2 ≤ C*(D:ℝ)^(-e) := by
  let v (n : ℕ) := (n.divisors.card:ℝ)^2*(n:ℝ)^(-(1+d))
  have hv : Summable v := summable_card_divisors_sq_mul_rpow (by linarith)
  have hn (n : ℕ) : 0 ≤ v n := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨∑' n,v n,tsum_nonneg hn,?_⟩
  intro K N D S hD hS s hs
  have row (n : ℕ) (hm : n ∈ S) : ‖mollifiedCoeff K N n * (n:ℂ)^(-s)‖^2 ≤ v n*(D:ℝ)^(-e) := by
    have hn₀ := hD.trans_le (hS n hm)
    have hn₁ : 1 ≤ (n:ℝ) := by exact_mod_cast hn₀
    have hd₀ : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
    have hr : ((n:ℝ)^(-s.re))^2 ≤ (n:ℝ)^(-(1+d))*(D:ℝ)^(-e) := by
      rw [← Real.rpow_mul_natCast hd₀]
      calc _ ≤ (n:ℝ)^(-(1+d)-e) := Real.rpow_le_rpow_of_exponent_le hn₁ (by push_cast; linarith)
           _ = (n:ℝ)^(-(1+d))*(n:ℝ)^(-e) := Real.rpow_add (Nat.cast_pos.mpr hn₀) _ _
           _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr hD)
             (Nat.cast_le.mpr (hS n hm)) (neg_nonpos.mpr he)) (Real.rpow_nonneg hd₀ _)
    rw [norm_mul,polynomial_term_norm hn₀,mul_pow]
    exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_mollifiedCoeff_le K N n) 2) hr
      (sq_nonneg _) (sq_nonneg _)).trans_eq (by dsimp only [v]; ring)
  calc _ ≤ ∑ n ∈ S, v n*(D:ℝ)^(-e) := sum_le_sum row
       _ = (∑ n ∈ S,v n)*(D:ℝ)^(-e) := (sum_mul ..).symm
       _ ≤ _ := mul_le_mul_of_nonneg_right (hv.sum_le_tsum _ (fun n _ ↦ hn n)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The low Möbius coefficients cancel exactly. Split the remaining band at any intermediate cutoff. -/
theorem conductorTruncation_mul_mollifier_sub_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) {K N D : ℕ}
    (hK : 1 ≤ K) (hN : K ≤ N) (hD : K ≤ D) (hD' : D ≤ K*N) :
    conductorTruncation χ N s * mobiusMollifier χ K s - 1 =
      conductorPolynomial χ s (mollifiedCoeff K N) (Ioc K D) +
      conductorPolynomial χ s (mollifiedCoeff K N) (Ioc D (K*N)) := by
  rw [conductorTruncation_mul_mollifier]
  let g (n : ℕ) := mollifiedCoeff K N n * χ (n : ZMod q) * (n:ℂ)^(-s)
  have h1 : ∑ n ∈ Ioc 0 K, g n = 1 := by
    rw [Finset.sum_eq_single 1]
    · simp [g,mollifiedCoeff_low hK (hK.trans hN)]
    · intro n hn hne
      have hn' := (mem_Ioc.mp hn).2
      simp [g,mollifiedCoeff_low hn' (hn'.trans hN),hne]
    · simp [hK]
  have hsum {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) : (∑ n ∈ Ioc i k, g n) =
      (∑ n ∈ Ioc i j,g n) + ∑ n ∈ Ioc j k,g n := by
    rw [← Ioc_union_Ioc_eq_Ioc hij hjk, sum_union]
    exact disjoint_left.mpr (fun n hn hn' ↦ (mem_Ioc.mp hn').1.not_ge (mem_Ioc.mp hn).2)
  change (∑ n ∈ Icc 1 (K*N),g n)-1 = _
  rw [show Icc 1 (K*N)=Ioc 0 (K*N) from Icc_succ_left_eq_Ioc .., hsum (Nat.zero_le K) (hD.trans hD'),
    hsum hD hD',h1]
  change 1+((∑ n ∈ Ioc K D,g n)+∑ n ∈ Ioc D (K*N),g n)-1 =
    (∑ n ∈ Ioc K D,g n)+∑ n ∈ Ioc D (K*N),g n
  ring

end RiemannMasullo.ConductorCylinder
