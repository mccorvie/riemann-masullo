module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.SmoothMassBound

public section

open Classical

namespace RiemannMasullo.Selberg

/-- On the factor pairs of a positive integer, the positive half-zeta coefficients have
convolution square one and majorize the absolute half-Möbius coefficients. -/
private theorem sum_abs_pairs_le_inv (n : ℕ) (hn : n ≠ 0) :
    (∑ p ∈ n.divisorsAntidiagonal, |alpha p.1 * alpha p.2| / ((p.1 : ℝ) * p.2)) ≤
      (n : ℝ)⁻¹ := by
  have hmajor (d : ℕ) : |alpha d| ≤ posHalf d := spectralLineJet_selbergHalfZeta_spec.1 d
  calc
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, posHalf p.1 * posHalf p.2 / n := by
      refine Finset.sum_le_sum fun p hp ↦ ?_
      rw [abs_mul, ← Nat.cast_mul, (Nat.mem_divisorsAntidiagonal.mp hp).1]
      exact div_le_div_of_nonneg_right
        (mul_le_mul (hmajor _) (hmajor _) (abs_nonneg _) ((abs_nonneg _).trans (hmajor _)))
        (Nat.cast_nonneg n)
    _ = (spectralLineJet_selbergHalfZeta * spectralLineJet_selbergHalfZeta) n / n := by
      rw [ArithmeticFunction.mul_apply, Finset.sum_div]
      rfl
    _ = _ := by
      rw [spectralLineJet_selbergHalfZeta_spec.2.1]
      simp [ArithmeticFunction.zeta_apply_ne hn, one_div]

/-- Card 7. The absolute coefficient pairs supported on primes of r whose product is divisible by
r have reciprocal-weighted sum at most `smoothMass r / r`.
Titchmarsh, Lemma 10.13, p. 273. -/
theorem smooth_pair_bound (r N : ℕ) (hr : 0 < r) :
    (∑ d ∈ (D N).filter (smooth r), ∑ e ∈ (D N).filter (fun e ↦ smooth r e ∧ r ∣ d*e),
      |alpha d * alpha e| / ((d : ℝ)*e)) ≤ smoothMass r / r := by
  classical
  let supported := (D N).filter (smooth r)
  let pairs := (supported ×ˢ supported).filter (fun p ↦ r ∣ p.1 * p.2)
  let indices := (D (N * N)).filter (smooth r)
  let idx (p : ℕ × ℕ) := p.1 * p.2 / r
  let weight (p : ℕ × ℕ) := |alpha p.1 * alpha p.2| / ((p.1 : ℝ) * p.2)
  have hmem (p : ℕ × ℕ) : p ∈ pairs ↔ p.1 ∈ supported ∧
      p.2 ∈ (D N).filter (fun e ↦ smooth r e ∧ r ∣ p.1 * e) := by
    simp only [pairs, supported, Finset.mem_filter, Finset.mem_product, and_assoc]
  have hidx (p : ℕ × ℕ) (hp : p ∈ pairs) : idx p ∈ indices := by
    obtain ⟨hpair, hdvd⟩ := Finset.mem_filter.mp hp
    obtain ⟨hd, he⟩ := Finset.mem_product.mp hpair
    obtain ⟨hdN, hds⟩ := Finset.mem_filter.mp hd
    obtain ⟨heN, hes⟩ := Finset.mem_filter.mp he
    have hs : smooth r (idx p) := Nat.mem_factoredNumbers_of_dvd
      (Nat.mul_mem_factoredNumbers hds hes) (Nat.div_dvd_of_dvd hdvd)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_factoredNumbers hs),
       (Nat.div_le_self _ _).trans (Nat.mul_le_mul (Finset.mem_Icc.mp hdN).2
         (Finset.mem_Icc.mp heN).2)⟩, hs⟩
  calc
    _ = ∑ p ∈ pairs, weight p := (Finset.sum_finset_product pairs supported _ hmem).symm
    _ = ∑ i ∈ indices, ∑ p ∈ pairs with idx p = i, weight p :=
      (Finset.sum_fiberwise_of_maps_to hidx weight).symm
    _ ≤ ∑ i ∈ indices, (i : ℝ)⁻¹ / r := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      have hir : i * r ≠ 0 := mul_ne_zero
        (Nat.ne_zero_of_mem_factoredNumbers (Finset.mem_filter.mp hi).2) hr.ne'
      have hsub : pairs.filter (fun p ↦ idx p = i) ⊆ (i * r).divisorsAntidiagonal := by
        intro p hp
        obtain ⟨hp, hpi⟩ := Finset.mem_filter.mp hp
        exact Nat.mem_divisorsAntidiagonal.mpr
          ⟨hpi ▸ (Nat.div_mul_cancel (Finset.mem_filter.mp hp).2).symm, hir⟩
      apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦
        div_nonneg (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))).trans
      simpa [weight, div_eq_mul_inv, mul_comm] using sum_abs_pairs_le_inv (i * r) hir
    _ ≤ _ := by
      rw [← Finset.sum_div]
      exact div_le_div_of_nonneg_right (smooth_mass_bound r (N * N) hr) (Nat.cast_nonneg r)

end RiemannMasullo.Selberg
