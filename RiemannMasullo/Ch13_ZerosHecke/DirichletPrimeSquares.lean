module

public import Mathlib.NumberTheory.LSeries.WeakPNT
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Prime squares in a Dirichlet character sum

For a Dirichlet character χ, write ψχ for the weighted sum over prime powers and θχ
for the sum over primes. The contribution of all even powers is ψχ²(√x). Removing it
from ψχ(x) − θχ(x) leaves an error of order at most x^(1/3), uniformly in χ and its modulus.

The prime number theorem in arithmetic progressions then determines the leading square-root
term and its Mellin limit at every point of the critical line. These estimates distinguish
the prime and prime-power observables in the rational case of Theorem 12.5.1.1, pp. 519–520.
-/

open Set Filter Function MeasureTheory Finset ArithmeticFunction Classical
open scoped Topology

public noncomputable section
namespace RiemannMasullo

/-- The Chebyshev prime-power count weighted by a Dirichlet character. -/
@[expose] def dirichletChebyshevPsi {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ (n : ZMod q) * (vonMangoldt n : ℂ)

/-- The logarithmically weighted sum over primes for a Dirichlet character. -/
@[expose] def dirichletChebyshevTheta {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, χ (n : ZMod q) * (Real.log n : ℂ)

/-- The prime number theorem for the character-weighted prime-power count. -/
theorem dirichletChebyshevPsi_div_tendsto {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Tendsto (fun x : ℝ ↦ dirichletChebyshevPsi χ x / (x : ℂ))
      atTop (𝓝 (if χ = 1 then 1 else 0)) := by
  unfold dirichletChebyshevPsi
  let A (a : ZMod q) (x : ℝ) := ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt.residueClass a n
  have ht (a : ZMod q) : Tendsto (fun x : ℝ ↦ χ a * ((A a x : ℂ) / x)) atTop
      (𝓝 (χ a * (q.totient : ℂ)⁻¹)) := by
    by_cases h : IsUnit a
    · have he := Complex.continuous_ofReal.continuousAt.tendsto.comp
        (vonMangoldt.tendsto_sum_residueClass_div_atTop h)
      simpa only [A, Function.comp_def, Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_natCast] using
        he.const_mul (χ a)
    · simp [χ.map_nonunit h]
  have hsum := tendsto_finsetSum Finset.univ (fun a _ ↦ ht a)
  have htot : ∑ a : ZMod q, χ a * (q.totient : ℂ)⁻¹ = if χ = 1 then 1 else 0 := by
    rw [← Finset.sum_mul]
    by_cases h : χ = 1
    · subst χ
      rw [MulChar.sum_one_eq_card_units]
      simp [ZMod.card_units_eq_totient, Nat.totient_pos.mpr (NeZero.pos q) |>.ne']
    · simp [h, χ.sum_eq_zero_of_ne_one h]
  rw [htot] at hsum
  apply hsum.congr
  intro x
  simp only [A, Complex.ofReal_sum, mul_div_assoc', ← Finset.sum_div]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le ⌊x⌋₊),
    ← Finset.Icc_succ_left_eq_Ioc]
  simp only [vonMangoldt.residueClass_apply_zero, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro n _
  simp [vonMangoldt.residueClass, Set.indicator_apply, eq_comm, apply_ite]

private theorem primeSquares_sum_squares {M : Type*} [AddCommMonoid M] (a : ℕ → M) {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsSquare, a n =
      ∑ m ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, a (m^2) := by
  classical
  have he : (Finset.Icc 1 ⌊x⌋₊).filter IsSquare =
      (Finset.Icc 1 ⌊Real.sqrt x⌋₊).image (fun m : ℕ ↦ m^2) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Nat.le_floor_iff hx,
      Nat.le_floor_iff (Real.sqrt_nonneg _)]
    constructor
    · rintro ⟨⟨hn,hu⟩,m,hm⟩
      rw [hm, ← sq] at hn hu ⊢
      refine ⟨m, ⟨by nlinarith, Real.le_sqrt_of_sq_le ?_⟩, rfl⟩
      exact_mod_cast hu
    · rintro ⟨m,⟨hm,hu⟩,rfl⟩
      refine ⟨⟨by nlinarith, ?_⟩, ⟨m, sq m⟩⟩
      have h := pow_le_pow_left₀ (Nat.cast_nonneg m : 0 ≤ (m:ℝ)) hu 2
      · exact_mod_cast (h.trans_eq (Real.sq_sqrt hx))
  rw [he, Finset.sum_image]
  intro m _ n _ heq
  exact Nat.pow_left_injective (by decide : 2 ≠ 0) heq

private theorem primeSquares_residual {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x) :
    let A (η : DirichletCharacter ℂ q) (y : ℝ) := ∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
      η (n : ZMod q) * (vonMangoldt n : ℂ)
    let T := ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, χ (n : ZMod q) * (Real.log n : ℂ)
    ‖A χ x - T - A (χ^2) (Real.sqrt x)‖ ≤
      Chebyshev.psi x - Chebyshev.theta x - Chebyshev.psi (Real.sqrt x) := by
  classical
  intro A T
  let S := Finset.Icc 1 ⌊x⌋₊
  let r (n : ℕ) := χ (n : ZMod q) * (vonMangoldt n : ℂ)
  have hnot {n : ℕ} (hn : n.Prime) : ¬ IsSquare n := hn.prime.not_isSquare
  have hpartition {M : Type} [AddCommGroup M] (f : ℕ → M) :
      (∑ n ∈ S, f n) - (∑ n ∈ S.filter Nat.Prime, f n) - (∑ n ∈ S.filter IsSquare, f n) =
      ∑ n ∈ S.filter (fun n ↦ ¬n.Prime ∧ ¬ IsSquare n), f n := by
    simp only [Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hp : n.Prime
    · simp [hp, hnot hp]
    · by_cases hs : IsSquare n <;> simp [hp, hs]
  have hT : T = ∑ n ∈ S.filter Nat.Prime, r n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [r, vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]
  have hsq : A (χ^2) (Real.sqrt x) = ∑ n ∈ S.filter IsSquare, r n := by
    rw [primeSquares_sum_squares _ (zero_le_one.trans hx)]
    apply Finset.sum_congr rfl
    intro n _
    simp only [r, vonMangoldt_apply_pow (by decide : (2:ℕ) ≠ 0), Nat.cast_pow, map_pow]
    simp only [pow_two, MulChar.mul_apply]
  have hψ (y : ℝ) : Chebyshev.psi y = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, vonMangoldt n := by
    rw [Chebyshev.psi, ← Finset.Icc_succ_left_eq_Ioc]; rfl
  have hθ : Chebyshev.theta x = ∑ n ∈ S.filter Nat.Prime, vonMangoldt n := by
    rw [Chebyshev.theta, ← Finset.Icc_succ_left_eq_Ioc]
    apply Finset.sum_congr rfl
    intro n hn
    exact (vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2).symm
  have hψ₂ : Chebyshev.psi (Real.sqrt x) = ∑ n ∈ S.filter IsSquare, vonMangoldt n := by
    rw [hψ, primeSquares_sum_squares _ (zero_le_one.trans hx)]
    simp only [vonMangoldt_apply_pow (by decide : (2:ℕ) ≠ 0)]
  rw [hT, hsq, hψ₂, hθ, hψ]
  change ‖(∑ n ∈ S, r n) - _ - _‖ ≤ (∑ n ∈ S, vonMangoldt n) - _ - _
  rw [hpartition r, hpartition (fun n ↦ vonMangoldt n)]
  apply (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ ?_)
  rw [show ‖r n‖ = _ from norm_mul _ _, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
  exact mul_le_of_le_one_left vonMangoldt_nonneg (χ.norm_le_one _)

/-- Removing the prime powers of even exponent leaves a cube-root remainder. The bound
is uniform in the character and the modulus. -/
theorem dirichletChebyshevPsi_sub_theta_sub_squares_bound {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x) :
    ‖dirichletChebyshevPsi χ x - dirichletChebyshevTheta χ x - dirichletChebyshevPsi (χ^2) (Real.sqrt x)‖ ≤
      (2 * (Real.log 4 + 4)) * x ^ (1/3 : ℝ) := by
  apply (primeSquares_residual χ hx).trans
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  rw [← one_div, ← Real.sqrt_eq_rpow] at h
  have h₃ := Chebyshev.psi_le_const_mul_self (x := x ^ (3 : ℝ)⁻¹) (Real.rpow_nonneg (zero_le_one.trans hx) _)
  have h₅ := Chebyshev.psi_le_const_mul_self (x := x ^ (5 : ℝ)⁻¹) (Real.rpow_nonneg (zero_le_one.trans hx) _)
  have hpow : (Real.log 4 + 4) * x ^ (5 : ℝ)⁻¹ ≤ (Real.log 4 + 4) * x ^ (3 : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by norm_num)) (by positivity)
  rw [one_div]
  linarith

/-- The difference between prime-power and prime counts has a square-root main term
exactly for characters whose square is principal. -/
theorem dirichletChebyshevPsi_sub_theta_div_sqrt_tendsto {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Tendsto (fun x : ℝ ↦ (dirichletChebyshevPsi χ x - dirichletChebyshevTheta χ x) / Real.sqrt x)
      atTop (𝓝 (if χ ^ 2 = 1 then 1 else 0)) := by
  let R (x : ℝ) := dirichletChebyshevPsi χ x - dirichletChebyshevTheta χ x -
    dirichletChebyshevPsi (χ^2) (Real.sqrt x)
  let C := 2*(Real.log 4 + 4)
  have herr : Tendsto (fun x : ℝ ↦ R x / (Real.sqrt x : ℂ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun x : ℝ ↦ C*x^(-(1/6 : ℝ)))
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx₀ := lt_of_lt_of_le zero_lt_one hx
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg x), Real.sqrt_eq_rpow]
      calc
        _ ≤ (C*x^(1/3 : ℝ))/x^(1/2 : ℝ) := div_le_div_of_nonneg_right (dirichletChebyshevPsi_sub_theta_sub_squares_bound χ hx)
          (Real.rpow_nonneg hx₀.le _)
        _ = _ := by rw [mul_div_assoc, ← Real.rpow_sub hx₀]; norm_num
    · simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/6)).const_mul C
  have hchar := (dirichletChebyshevPsi_div_tendsto (χ^2)).comp Real.tendsto_sqrt_atTop
  convert herr.add hchar using 1
  · funext x
    change _ = R x / _ + dirichletChebyshevPsi (χ^2) (Real.sqrt x) / _
    dsimp only [R]
    ring
  · simp

/-- Both character-weighted Chebyshev counts are measurable. -/
theorem dirichletChebyshevPsi_theta_measurable {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Measurable (dirichletChebyshevPsi χ) ∧ Measurable (dirichletChebyshevTheta χ) := by
  constructor
  · exact (measurable_of_countable (fun m : ℕ ↦ ∑ n ∈ Finset.Icc 1 m,
      χ (n : ZMod q) * (vonMangoldt n : ℂ))).comp measurable_id.nat_floor
  · exact (measurable_of_countable (fun m : ℕ ↦ ∑ n ∈ (Finset.Icc 1 m).filter Nat.Prime,
      χ (n : ZMod q) * (Real.log n : ℂ))).comp measurable_id.nat_floor

/-- After removing the contribution of squares, the weighted squared residual is
integrable at every real exponent strictly larger than one third. -/
theorem dirichletChebyshevPsi_sub_theta_sub_squares_integrable {q : ℕ} (χ : DirichletCharacter ℂ q) {b : ℝ} (hb : 1/3 < b) :
    IntegrableOn (fun x : ℝ ↦ ‖dirichletChebyshevPsi χ x - dirichletChebyshevTheta χ x -
      dirichletChebyshevPsi (χ^2) (Real.sqrt x)‖ ^ 2 * x ^ (-2*b-1)) (Ioi 1) := by
  let C := 2*(Real.log 4 + 4)
  have ⟨hm, ht⟩ := dirichletChebyshevPsi_theta_measurable χ
  have hs := (dirichletChebyshevPsi_theta_measurable (χ^2)).1
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : (2/3 : ℝ) - 2*b-1 < -1) zero_lt_one
  apply (hi.const_mul (C^2)).mono' (by apply Measurable.aestronglyMeasurable; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have h₀ := lt_trans zero_lt_one hx
  have h := pow_le_pow_left₀ (norm_nonneg _) (dirichletChebyshevPsi_sub_theta_sub_squares_bound χ hx.le) 2
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg h₀.le _))]
  apply (mul_le_mul_of_nonneg_right h (Real.rpow_nonneg h₀.le _)).trans_eq
  change (C*x^(1/3 : ℝ))^2 * x^(-2*b-1) = C^2 * x^(2/3-2*b-1)
  rw [mul_pow, mul_assoc, ← Real.rpow_mul_natCast h₀.le, ← Real.rpow_add h₀]
  congr 2
  push_cast
  ring

/-- The contribution from higher prime powers is bounded uniformly in the character and modulus. -/
theorem dirichletChebyshevPsi_sub_theta_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x) :
    ‖dirichletChebyshevPsi χ x - dirichletChebyshevTheta χ x‖ ≤ 3 * (Real.log 4 + 4) * Real.sqrt x := by
  have hpsi (η : DirichletCharacter ℂ q) (y : ℝ) : ‖dirichletChebyshevPsi η y‖ ≤ Chebyshev.psi y := by
    rw [Chebyshev.psi, ← Finset.Icc_succ_left_eq_Ioc]
    apply (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_left vonMangoldt_nonneg (η.norm_le_one _)
  have h := (hpsi (χ^2) (Real.sqrt x)).trans (Chebyshev.psi_le_const_mul_self (Real.sqrt_nonneg x))
  have h₃ := dirichletChebyshevPsi_sub_theta_sub_squares_bound χ hx
  have hx' : x^(1/3 : ℝ) ≤ Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hadd := norm_add_le (dirichletChebyshevPsi χ x - dirichletChebyshevTheta χ x -
    dirichletChebyshevPsi (χ^2) (Real.sqrt x)) (dirichletChebyshevPsi (χ^2) (Real.sqrt x))
  rw [sub_add_cancel] at hadd
  linarith [mul_le_mul_of_nonneg_left hx' (by positivity : 0 ≤ 2*(Real.log 4 + 4))]

private theorem primeSquares_abel_limit {B : ℝ → ℝ} (hm : Measurable B) (hB : Tendsto B atTop (𝓝 0))
    {C : ℝ} (hbd : ∀ x : ℝ, 1 ≤ x → ‖B x‖ ≤ C) :
    Tendsto (fun u : ℝ ↦ u * ∫ x in Ioi (1 : ℝ), B x * x ^ (-u-1)) (𝓝[>] 0) (𝓝 0) := by
  let F (u x : ℝ) := B (x^u⁻¹) * x ^ (-(2 : ℝ))
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : -(2 : ℝ) < -1) zero_lt_one
  have hmF (u : ℝ) : Measurable (F u) := by dsimp [F]; fun_prop
  have hb : ∀ᶠ u in 𝓝[>] (0 : ℝ), ∀ᵐ x : ℝ ∂volume.restrict (Ioi 1), ‖F u x‖ ≤ C * x ^ (-(2 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx₀ := lt_trans zero_lt_one hx
    rw [show ‖F u x‖ = _ from norm_mul .., Real.norm_of_nonneg (Real.rpow_nonneg hx₀.le _)]
    exact mul_le_mul_of_nonneg_right (hbd _ (Real.one_le_rpow hx.le (inv_pos.mpr hu).le)) (Real.rpow_nonneg hx₀.le _)
  have hlim : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 1), Tendsto (fun u : ℝ ↦ F u x) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have H := (hB.comp ((tendsto_rpow_atTop_of_base_gt_one x hx).comp tendsto_inv_nhdsGT_zero)).mul_const (x ^ (-(2 : ℝ)))
    simpa [F, Function.comp_def] using H
  have H := tendsto_integral_filter_of_dominated_convergence (fun x : ℝ ↦ C * x ^ (-(2 : ℝ)))
    (Eventually.of_forall fun u ↦ (hmF u).aestronglyMeasurable) hb (hi.const_mul C) hlim
  simp only [integral_zero] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
  have hiu := integral_comp_rpow_Ioi_of_pos' (g := fun x : ℝ ↦ u*(B x*x^(-u-1))) (inv_pos.mpr hu) (c := 1) zero_le_one
  rw [Real.one_rpow, integral_const_mul] at hiu
  rw [← hiu]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx₀ := lt_trans zero_lt_one hx
  dsimp only [F, smul_eq_mul]
  rw [← Real.rpow_mul hx₀.le]
  have he : u⁻¹ - 1 + u⁻¹ * (-u-1) = -(2 : ℝ) := by field_simp; ring
  rw [← he, Real.rpow_add hx₀]
  field_simp

/-- On the critical line, the Mellin transform of the excess prime powers has a nonzero
horizontal Abel limit exactly at the real point for characters whose square is principal. -/
theorem dirichletChebyshevPsi_sub_theta_mellin_boundary {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) (hr : ρ.re = 1/2) :
    let D (x : ℝ) := dirichletChebyshevPsi χ x - dirichletChebyshevTheta χ x
    Tendsto (fun u : ℝ ↦ (u : ℂ) * ∫ x in Ioi (1 : ℝ), D x * (x : ℂ) ^ (-(ρ+u+1)))
      (𝓝[>] 0) (𝓝 (if ρ = 1/2 ∧ χ^2 = 1 then 1 else 0)) := by
  intro D
  let c : ℂ := if χ^2 = 1 then 1 else 0
  let B (x : ℝ) := D x / (Real.sqrt x : ℂ) - c
  have hD : Measurable D := (dirichletChebyshevPsi_theta_measurable χ).1.sub (dirichletChebyshevPsi_theta_measurable χ).2
  have hm : Measurable B := by dsimp only [B]; fun_prop
  have ht : Tendsto B atTop (𝓝 0) := by
    simpa [B,c,D] using (dirichletChebyshevPsi_sub_theta_div_sqrt_tendsto χ).sub_const c
  let C := 3*(Real.log 4 + 4) + ‖c‖
  have hbd (x : ℝ) (hx : 1 ≤ x) : ‖B x‖ ≤ C := by
    have hx₀ := lt_of_lt_of_le zero_lt_one hx
    apply (norm_sub_le ..).trans
    apply add_le_add_left _ _
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      div_le_iff₀ (Real.sqrt_pos.mpr hx₀)]
    exact dirichletChebyshevPsi_sub_theta_norm_le χ hx
  have hab := primeSquares_abel_limit hm.norm (by simpa using ht.norm) (C := C) (fun x hx ↦ by simpa using hbd x hx)
  let K (u x : ℝ) := (x : ℂ) ^ ((1/2 : ℂ) - (ρ+u+1))
  have hK (u x : ℝ) (hx : 1 < x) : ‖K u x‖ = x ^ (-u-1) := by
    rw [show ‖K u x‖ = _ from Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one hx) _]
    congr 1
    simp [hr]
    ring
  have hE : Tendsto (fun u : ℝ ↦ (u : ℂ) * ∫ x in Ioi (1 : ℝ), B x * K u x) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ hab
    filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu.le]
    apply mul_le_mul_of_nonneg_left _ hu.le
    apply (norm_integral_le_integral_norm _).trans_eq
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact (norm_mul ..).trans (congrArg (‖B x‖ * ·) (hK u x hx))
  have hconst : Tendsto (fun u : ℝ ↦ c * ((u : ℂ) / (ρ - 1/2 + u)))
      (𝓝[>] 0) (𝓝 (if ρ = 1/2 ∧ χ^2 = 1 then 1 else 0)) := by
    by_cases e : ρ = 1/2
    · rw [e, sub_self]
      have heq : (fun u : ℝ ↦ c * ((u : ℂ) / (0+u))) =ᶠ[𝓝[>] 0] fun _ ↦ c := by
        filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
        simp [hu.ne']
      simpa only [true_and, c] using (tendsto_const_nhds (x := c)).congr' heq.symm
    · have h0 : Tendsto (fun u : ℝ ↦ (u : ℂ)) (𝓝[>] 0) (𝓝 0) := by
        simpa using ((Complex.continuous_ofReal.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds)
      have h := (h0.div (tendsto_const_nhds.add h0) (by simpa using sub_ne_zero.mpr e : ρ-1/2+0 ≠ 0)).const_mul c
      rw [ite_eq_right (fun he ↦ e he.1)]
      simpa using h
  have h := hE.add hconst
  rw [zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
  let w := (1/2 : ℂ) - (ρ+u+1)
  have hw : w.re < -1 := by dsimp [w]; simp [hr]; linarith
  have hki : IntegrableOn (K u) (Ioi 1) := integrableOn_Ioi_cpow_of_lt hw zero_lt_one
  have hei : IntegrableOn (fun x : ℝ ↦ B x * K u x) (Ioi 1) := by
    apply (hki.norm.const_mul C).mono' (by dsimp [K]; apply Measurable.aestronglyMeasurable; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbd x hx.le) (norm_nonneg _)
  have hid (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
      D x * (x : ℂ) ^ (-(ρ+u+1)) = B x*K u x + c*K u x := by
    have hx₀ := lt_trans zero_lt_one hx
    have hsq : (x : ℂ) ^ (1/2 : ℂ) = (Real.sqrt x : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx₀.le]; push_cast; rfl
    rw [← add_mul]
    dsimp only [B,K]
    rw [sub_add_cancel, sub_eq_add_neg, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx₀.ne'), hsq]
    field_simp [Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx₀).ne']
  have hv : (∫ x in Ioi (1 : ℝ), K u x) = 1/(ρ-1/2+u) := by
    change (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ w) = _
    rw [integral_Ioi_cpow_of_lt hw zero_lt_one, Complex.ofReal_one, Complex.one_cpow,
      show w+1 = -(ρ-1/2+u) by dsimp [w]; ring, neg_div_neg_eq]
  rw [setIntegral_congr_fun measurableSet_Ioi hid, integral_add hei (hki.const_mul c), integral_const_mul, hv]
  ring

end RiemannMasullo
