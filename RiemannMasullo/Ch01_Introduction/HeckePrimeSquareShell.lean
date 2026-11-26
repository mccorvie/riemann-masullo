module

public import RiemannMasullo.AppB_AnalyticNT.Sec6
public import Mathlib.NumberTheory.Chebyshev

/-!
# The prime-square term in translated Hecke prime sums

On a fixed positive log window the contribution of composite rational norms is bounded.
Keeping the exact coefficients at prime squares leaves a remainder decaying as
`exp (-y/6)`, for every normalized unitary character of every number field. This applies to
the signed degree-one comparison for Theorem 12.5.1.1, pp. 519–520.
-/

@[expose] public noncomputable section

open Set NumberField ArithmeticFunction Classical

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "coeff(" χ ")" => heckeLogDerivCoefficient (ideleClassNormTwist χ 0)
local notation "PS" => fun n : ℕ ↦ ∃ p : ℕ, Nat.Prime p ∧ n = p ^ 2

private theorem sum_primeSquares_eq {M : Type*} [AddCommMonoid M] (a : ℕ → M) {x : ℝ} (hx : 0 ≤ x) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with PS n, a n) =
    ∑ p ∈ Finset.Ioc 0 ⌊Real.sqrt x⌋₊ with p.Prime, a (p ^ 2) := by
  have he : (Finset.Ioc 0 ⌊x⌋₊).filter PS =
      ((Finset.Ioc 0 ⌊Real.sqrt x⌋₊).filter Nat.Prime).image (fun p : ℕ ↦ p ^ 2) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image, Nat.le_floor_iff hx,
      Nat.le_floor_iff (Real.sqrt_nonneg _)]
    constructor
    · rintro ⟨⟨_, hle⟩, p, hp, rfl⟩
      exact ⟨p, ⟨⟨hp.pos, Real.le_sqrt_of_sq_le (by exact_mod_cast hle)⟩, hp⟩, rfl⟩
    · rintro ⟨p, ⟨⟨hp₀, hp₁⟩, hp⟩, rfl⟩
      have hh := pow_le_pow_left₀ (Nat.cast_nonneg p : 0 ≤ (p : ℝ)) hp₁ 2
      exact ⟨⟨pow_pos hp₀ _, by exact_mod_cast (hh.trans_eq (Real.sq_sqrt hx))⟩, p, hp, rfl⟩
  rw [he, Finset.sum_image]
  intro p _ q _ heq
  nlinarith

private theorem composite_sum_sub_primeSquares {M : Type*} [AddCommGroup M] (a : ℕ → M)
    {x : ℝ} (hx : 0 ≤ x) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with IsPrimePow n ∧ ¬ n.Prime, a n) -
      (∑ p ∈ Finset.Ioc 0 ⌊Real.sqrt x⌋₊ with p.Prime, a (p ^ 2)) =
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with IsPrimePow n ∧ ¬ n.Prime ∧ ¬ PS n, a n := by
  rw [← sum_primeSquares_eq a hx]
  simp only [Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : PS n
  · obtain ⟨p, hp, rfl⟩ := h
    have hpow : IsPrimePow (p ^ 2) := hp.isPrimePow.pow (by decide)
    have hnot : ¬ Nat.Prime (p ^ 2) := fun h ↦ h.prime.not_isSquare ⟨p, sq p⟩
    simp [hpow, hnot, hp]
  · simp [h]

private theorem vonMangoldt_higher_residual {x : ℝ} (hx : 0 ≤ x) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with IsPrimePow n ∧ ¬ n.Prime ∧ ¬ PS n, vonMangoldt n) =
      Chebyshev.psi x - Chebyshev.theta x - Chebyshev.theta (Real.sqrt x) := by
  rw [← composite_sum_sub_primeSquares _ hx]
  congr 1
  · rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : IsPrimePow n
    · simp [h]
    · simp [h, vonMangoldt_eq_zero_iff.mpr h]
  · apply Finset.sum_congr rfl
    intro p hp
    simp only [vonMangoldt_apply_pow (by decide : (2 : ℕ) ≠ 0),
      vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]

private theorem exists_higher_residual_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x →
      Chebyshev.psi x - Chebyshev.theta x - Chebyshev.theta (Real.sqrt x) ≤ K * x ^ (1 / 3 : ℝ) := by
  obtain ⟨B, hB⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let D := Real.log 4 + 4
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨2 * D + max B 0, by positivity, fun x hx ↦ ?_⟩
  have hx₀ := zero_le_one.trans hx
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  rw [← one_div, ← Real.sqrt_eq_rpow] at h
  have h₃ := Chebyshev.psi_le_const_mul_self (x := x ^ (3 : ℝ)⁻¹) (Real.rpow_nonneg hx₀ _)
  have h₅ := Chebyshev.psi_le_const_mul_self (x := x ^ (5 : ℝ)⁻¹) (Real.rpow_nonneg hx₀ _)
  have hu := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx
    (by norm_num : (5 : ℝ)⁻¹ ≤ (3 : ℝ)⁻¹)) hD
  have hq : Real.sqrt (Real.sqrt x) ≤ x ^ (3 : ℝ)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx₀]
    apply Real.rpow_le_rpow_of_exponent_le hx
    norm_num
  have hs := (hB (Real.sqrt x)).trans (mul_le_mul (le_max_left B 0) hq (Real.sqrt_nonneg _)
    (le_max_right B 0))
  dsimp only [D] at *
  rw [one_div]
  nlinarith only [h, h₃, h₅, hu, hs]

/-- Keeping the coefficients at the genuine rational prime squares leaves a cube-root bound,
uniform in the field and character after the degree is extracted. -/
theorem heckeLogDerivCoefficient_composite_sub_primeSquares_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Type*) [Field F] [NumberField F]
      (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) {x : ℝ}, 1 ≤ x →
      ∀ (b : ℕ → ℂ) {M : ℝ}, 0 ≤ M → (∀ n, ‖b n‖ ≤ M) →
      ‖(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with IsPrimePow n ∧ ¬ n.Prime, coeff(χ) n * b n) -
        (∑ p ∈ Finset.Ioc 0 ⌊Real.sqrt x⌋₊ with p.Prime, coeff(χ) (p ^ 2) * b (p ^ 2))‖ ≤
        (Module.finrank ℚ F : ℝ) * M * (K * x ^ (1 / 3 : ℝ)) := by
  obtain ⟨K, hK, hR⟩ := exists_higher_residual_bound
  refine ⟨K, hK, ?_⟩
  intro F _ _ χ x hx b M hM hb
  rw [composite_sum_sub_primeSquares _ (zero_le_one.trans hx)]
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with IsPrimePow n ∧ ¬ n.Prime ∧ ¬ PS n,
        (Module.finrank ℚ F : ℝ) * M * vonMangoldt n :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ by
        rw [norm_mul, mul_right_comm (Module.finrank ℚ F : ℝ) M]
        exact mul_le_mul (heckeLogDerivCoefficient_le_vonMangoldt χ n) (hb n) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) vonMangoldt_nonneg))
    _ ≤ _ := by
      rw [← Finset.mul_sum, vonMangoldt_higher_residual (zero_le_one.trans hx)]
      exact mul_le_mul_of_nonneg_left (hR x hx) (mul_nonneg (Nat.cast_nonneg _) hM)

/-- The actual coefficient of rational norm `p²` includes all prime ideals and exponents
with this norm, including first powers at places of residue degree two. -/
def heckePrimeSquareShell (χ : U) (H : ℝ → ℂ) (y v : ℝ) : ℂ :=
  ∑ p ∈ Finset.Ioc 0 ⌊Real.sqrt (Real.exp (y + v))⌋₊ with p.Prime,
    coeff(χ) (p ^ 2) * (H (2 * Real.log (p : ℝ) - y) / (p : ℂ))

private theorem heckePrimeSquareShell_eq (χ : U) (H : ℝ → ℂ) (y v : ℝ) :
    heckePrimeSquareShell χ H y v =
      ∑ p ∈ Finset.Ioc 0 ⌊Real.sqrt (Real.exp (y + v))⌋₊ with p.Prime,
        coeff(χ) (p ^ 2) * (H (Real.log ((p ^ 2 : ℕ) : ℝ) - y) / (Real.sqrt (p ^ 2 : ℕ) : ℂ)) := by
  apply Finset.sum_congr rfl
  intro p _
  simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat, Real.sqrt_sq (Nat.cast_nonneg p),
    Complex.ofReal_natCast]

/-- On a translated positive window, the composite Hecke sum differs from its prime-square
shell by at most a constant times `exp (-y/6)`. No regularity of the profile is required. -/
theorem heckeCompositeShell_sub_primeSquares_exp_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Type*) [Field F] [NumberField F]
      (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (H : ℝ → ℂ) {u v M : ℝ},
      0 < u → u ≤ v → tsupport H ⊆ Icc u v → 0 ≤ M → (∀ t ∈ tsupport H, ‖H t‖ ≤ M) →
      ∀ y ≥ (0 : ℝ),
      ‖(∑ n ∈ Finset.Ioc 0 ⌊Real.exp (y + v)⌋₊ with IsPrimePow n ∧ ¬ n.Prime,
        coeff(χ) n * (H (Real.log (n : ℝ) - y) / (Real.sqrt n : ℂ))) - heckePrimeSquareShell χ H y v‖ ≤
        (Module.finrank ℚ F : ℝ) * M * K * Real.exp (v / 3 - u / 2) * Real.exp (-y / 6) := by
  obtain ⟨K, hK, h⟩ := heckeLogDerivCoefficient_composite_sub_primeSquares_le
  refine ⟨K, hK, ?_⟩
  intro F _ _ χ H u v M hu huv hs hM hH y hy
  let b (n : ℕ) : ℂ := H (Real.log (n : ℝ) - y) / (Real.sqrt n : ℂ)
  have hb (n : ℕ) : ‖b n‖ ≤ M / Real.exp ((y + u) / 2) := by
    by_cases hz : H (Real.log (n : ℝ) - y) = 0
    · simpa [b, hz] using div_nonneg hM (Real.exp_pos _).le
    have ht := subset_tsupport H hz
    have hlo := (hs ht).1
    have hn : n ≠ 0 := by
      intro hn
      simp only [hn, Nat.cast_zero, Real.log_zero, zero_sub] at hlo
      linarith
    have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hden : Real.exp ((y + u) / 2) ≤ Real.sqrt n := by
      rw [Real.exp_half]
      exact Real.sqrt_le_sqrt ((Real.exp_le_exp.mpr (by linarith : y + u ≤ Real.log n)).trans_eq (Real.exp_log hn₀))
    dsimp only [b]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact (div_le_div_of_nonneg_right (hH _ ht) (Real.sqrt_nonneg _)).trans
      (div_le_div_of_nonneg_left hM (Real.exp_pos _) hden)
  rw [heckePrimeSquareShell_eq]
  refine (h F χ (x := Real.exp (y + v)) (Real.one_le_exp (by linarith)) b
    (div_nonneg hM (Real.exp_pos _).le) hb).trans_eq ?_
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, div_eq_mul_inv,
    ← Real.exp_neg, show (y + v) * (1 / 3 : ℝ) = (v / 3 - u / 2) + (-y / 6) + ((y + u) / 2) by ring,
    Real.exp_add, Real.exp_add]
  rw [Real.exp_neg]
  field_simp

end RiemannMasullo
