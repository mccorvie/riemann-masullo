module

public import RiemannMasullo.Ch13_ZerosHecke.DirichletJacobiCellEnergy
public import RiemannMasullo.Ch13_ZerosHecke.QuadraticPrimeTwists
public import RiemannMasullo.Ch13_ZerosHecke.RationalPrimitiveLogCoefficients
import RiemannMasullo.ForMathlib.NumberTheory.DirichletCharacter.PrimitiveCount

/-!
# Complete quadratic-cell deficits averaged over primitive conductors

For the fourth-power comparison associated with Theorem 12.5.1.1, pp. 519–520,
the base rational Dirichlet character ranges over all primitive characters of
conductor at most `C`. Each auxiliary pair is fixed throughout this average.
The signs selecting a cell may vary with the base character and sample.
-/

open Finset NumberField
open scoped Classical NNReal

@[expose] public noncomputable section

namespace RiemannMasullo

/-- A primitive rational character together with its positive conductor `i.1 + 1`. -/
abbrev RationalPrimitiveCharacter :=
  (m : ℕ) × {χ : DirichletCharacter ℂ (m + 1) // χ.IsPrimitive}

/-- Every primitive character of conductor at most `C`, counted once at its own level. -/
def rationalPrimitiveCharactersThrough (C : ℕ) : Finset RationalPrimitiveCharacter :=
  (range C).sigma (fun _ ↦ univ)

private def primitivePrincipal : RationalPrimitiveCharacter :=
  ⟨0, 1, DirichletCharacter.isPrimitive_one_level_one⟩

private theorem primitivePrincipal_iff (i : RationalPrimitiveCharacter) :
    i.2.1 = 1 ↔ i = primitivePrincipal := by
  constructor
  · rcases i with ⟨m, χ, hχ⟩
    intro h
    change χ = 1 at h
    have hlevel : m + 1 = 1 :=
      (DirichletCharacter.isPrimitive_def χ |>.mp hχ).symm.trans
        (DirichletCharacter.eq_one_iff_conductor_eq_one.mp h)
    obtain rfl : m = 0 := by omega
    subst χ
    rfl
  · rintro rfl
    rfl

private theorem primitiveCharacters_card_bound (C : ℕ) :
    (C : ℝ)^2 ≤ 1024 * (rationalPrimitiveCharactersThrough C).card := by
  unfold rationalPrimitiveCharactersThrough
  rw [card_sigma]
  simp only [card_univ, Fintype.card_subtype]
  exact_mod_cast DirichletCharacter.quadratic_le_sum_card_primitive C

private theorem selected_cell_centered_squares {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (p : ι) (J : ℕ) (R : ι → ℕ → Bool × Bool → ℂ)
    (s : ι → ℕ → Bool × Bool) {E : ℝ}
    (hE : ∀ j ∈ Ioc 0 J, (∑ i ∈ A, ∑ k : Bool × Bool, ‖R i j k‖^2) ≤ E) :
    (∑ i ∈ A, (∑ j ∈ Ioc 0 J,
      max ((if i = p then (j : ℝ)^8 / 2 else 0) - (R i j (s i j)).re) 0)^2) ≤
      (J : ℝ)^2 * (2 * E + (J : ℝ)^16) := by
  let d (i : ι) (j : ℕ) :=
    max ((if i = p then (j : ℝ)^8 / 2 else 0) - (R i j (s i j)).re) 0
  have hsample (i : ι) (j : ℕ) (hj : j ∈ Ioc 0 J) :
      d i j ^ 2 ≤ 2 * ∑ k : Bool × Bool, ‖R i j k‖^2 +
        (if i = p then (J : ℝ)^16 else 0) := by
    let z := R i j (s i j)
    let c : ℝ := if i = p then (j : ℝ)^8 / 2 else 0
    have hc : 0 ≤ c := by dsimp [c]; split_ifs <;> positivity
    have hz : max (c - z.re) 0 ≤ c + ‖z‖ :=
      max_le (by linarith [neg_le_abs z.re, Complex.abs_re_le_norm z]) (by positivity)
    have hs := pow_le_pow_left₀ (le_max_right (c - z.re) 0) hz 2
    have hnorm : ‖z‖^2 ≤ ∑ k : Bool × Bool, ‖R i j k‖^2 :=
      single_le_sum (f := fun k ↦ ‖R i j k‖^2) (fun _ _ ↦ sq_nonneg _) (mem_univ (s i j))
    change (max (c - z.re) 0)^2 ≤ _
    have hh : (max (c - z.re) 0)^2 ≤ 2*c^2 + 2*(∑ k : Bool × Bool, ‖R i j k‖^2) := by
      nlinarith only [hs, sq_nonneg (c - ‖z‖), hnorm]
    have hcen : 2*c^2 ≤ if i = p then (J : ℝ)^16 else 0 := by
      dsimp only [c]
      split_ifs
      · have hjJ : (j : ℝ)^16 ≤ (J : ℝ)^16 :=
          pow_le_pow_left₀ (by positivity) (by exact_mod_cast (mem_Ioc.mp hj).2) _
        nlinarith only [hjJ, pow_nonneg (Nat.cast_nonneg (α := ℝ) j) 16]
      · norm_num
    linarith only [hh, hcen]
  have hinner (j : ℕ) (hj : j ∈ Ioc 0 J) : ∑ i ∈ A, d i j ^ 2 ≤ 2 * E + (J : ℝ)^16 := by
    calc _ ≤ ∑ i ∈ A, (2 * ∑ k : Bool × Bool, ‖R i j k‖^2 +
             (if i = p then (J : ℝ)^16 else 0)) := sum_le_sum (fun i _ ↦ hsample i j hj)
         _ ≤ _ := by
           rw [sum_add_distrib, ← mul_sum]
           apply add_le_add (mul_le_mul_of_nonneg_left (hE j hj) (by norm_num))
           simp only [sum_ite_eq']
           split_ifs <;> first | exact le_rfl | positivity
  calc _ ≤ ∑ i ∈ A, (J : ℝ) * ∑ j ∈ Ioc 0 J, d i j ^ 2 := by
            apply sum_le_sum
            intro i _
            simpa only [Nat.card_Ioc, Nat.sub_zero] using
              (sq_sum_le_card_mul_sum_sq (s := Ioc 0 J) (f := d i))
       _ = (J : ℝ) * ∑ j ∈ Ioc 0 J, ∑ i ∈ A, d i j ^ 2 := by rw [← mul_sum, sum_comm]
       _ ≤ (J : ℝ) * ∑ _j ∈ Ioc 0 J, (2 * E + (J : ℝ)^16) :=
            mul_le_mul_of_nonneg_left (sum_le_sum hinner) (by positivity)
       _ = _ := by simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]; ring

/-- A finite-order rational Hecke lift of the indexed primitive Dirichlet character. -/
def rationalPrimitiveHeckeParameter (i : RationalPrimitiveCharacter) :
    PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ) :=
  (exists_rat_heckeLogDerivCoefficient_eq_dirichlet i.2.2).choose

/-- The lift is normalized on every norm section, has exactly the Dirichlet coefficients
at all norms, and is principal precisely at the principal Dirichlet character. -/
theorem rationalPrimitiveHeckeParameter_spec (i : RationalPrimitiveCharacter) :
    IsOfFinOrder (rationalPrimitiveHeckeParameter i) ∧
    (∀ (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ) (t : ℝ≥0ˣ),
      rationalPrimitiveHeckeParameter i (τ t) = 1) ∧
    (rationalPrimitiveHeckeParameter i = 1 ↔ i.2.1 = 1) ∧
    ∀ n : ℕ, heckeLogDerivCoefficient (ideleClassNormTwist (rationalPrimitiveHeckeParameter i) 0) n =
      i.2.1 n * (ArithmeticFunction.vonMangoldt n : ℂ) :=
  (exists_rat_heckeLogDerivCoefficient_eq_dirichlet i.2.2).choose_spec

/-- The four-times complete Hecke sum in a prescribed Jacobi cell is the real part
of the corresponding Dirichlet row, including the coefficients at conductor primes. -/
theorem rationalPrimitiveHeckeParameter_cell (i : RationalPrimitiveCharacter)
    (T : ℕ) (x : ℝ) (u v : ℕ) (a b : Bool) :
    quadraticPrimePowerCellRieszSum (rationalPrimitiveHeckeParameter i) T x u v
      (if a then 1 else -1) (if b then 1 else -1) =
      (dirichletJacobiCellRow i.2.1 T x u v a b).re := by
  simp [quadraticPrimePowerCellRieszSum, dirichletJacobiCellRow, dirichletThetaRow,
    (rationalPrimitiveHeckeParameter_spec i).2.2.2, Complex.mul_re, Complex.re_sum, mul_assoc]

/-- The sum of the positive deficits below the true pole center on the fourth powers,
using the complete Hecke coefficient sum and the two prescribed signs at each sample. -/
def rationalPrimitiveCellDeficit (i : RationalPrimitiveCharacter) (J u v : ℕ)
    (s : ℕ → Bool × Bool) : ℝ :=
  ∑ j ∈ Ioc 0 J, max ((if rationalPrimitiveHeckeParameter i = 1 then (j : ℝ)^8 / 2 else 0) -
    quadraticPrimePowerCellRieszSum (rationalPrimitiveHeckeParameter i) (J^4) ((j : ℝ)^4) u v
      (if (s j).1 then 1 else -1) (if (s j).2 then 1 else -1)) 0

private theorem centered_squares_fourth_power_bound {J C : ℝ} (hJ : 1 ≤ J) :
    J^2 * (2 * (112 * (C^2 + Real.pi * J^4) * (J^4)^3 * Real.log (2 * J^4)) + J^16) ≤
      4000 * (C^2 + J^4) * J^14 * Real.log (2 * J) := by
  have hJ₀ : 0 < J := by linarith
  have hlog : Real.log (2 * J^4) ≤ 4 * Real.log (2 * J) := by
    calc _ ≤ Real.log ((2 * J)^4) := Real.log_le_log (by positivity)
                (by nlinarith only [pow_nonneg hJ₀.le 4])
         _ = _ := Real.log_pow (2 * J) 4
  have hhalf : 1 / 2 ≤ Real.log (2 * J) := by
    have hl := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show 2 ≤ 2 * J by linarith)
    norm_num at hl
    linarith
  have hL : 0 ≤ Real.log (2 * J) := by linarith
  have hπ : C^2 + Real.pi * J^4 ≤ 4 * (C^2 + J^4) := by
    nlinarith only [sq_nonneg C, mul_le_mul_of_nonneg_right Real.pi_le_four (pow_nonneg hJ₀.le 4)]
  have hcen : J^16 ≤ (C^2 + J^4) * (J^4)^3 * (2 * Real.log (2 * J)) := by
    calc _ = J^4 * (J^4)^3 * 1 := by ring
         _ ≤ _ := by gcongr <;> linarith [sq_nonneg C]
  have he : 112 * (C^2 + Real.pi * J^4) * (J^4)^3 * Real.log (2 * J^4) ≤
      112 * (4 * (C^2 + J^4)) * (J^4)^3 * (4 * Real.log (2 * J)) := by
    have hpow : 1 ≤ J^4 := one_le_pow₀ hJ
    exact mul_le_mul (by gcongr) hlog (Real.log_nonneg (by linarith)) (by positivity)
  calc _ ≤ J^2 * (2 * (112 * (4 * (C^2 + J^4)) * (J^4)^3 * (4 * Real.log (2 * J))) +
              (C^2 + J^4) * (J^4)^3 * (2 * Real.log (2 * J))) :=
            mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left he (by norm_num)) hcen)
              (sq_nonneg _)
       _ = 3586 * (C^2 + J^4) * J^14 * Real.log (2 * J) := by ring
       _ ≤ _ := by gcongr; norm_num

private theorem rationalPrimitiveCellDeficit_sum_sq (C J : ℕ) (hC : 0 < C) (hJ : 1 ≤ J)
    (u v : ℕ) (s : RationalPrimitiveCharacter → ℕ → Bool × Bool) :
    (∑ i ∈ rationalPrimitiveCharactersThrough C, (rationalPrimitiveCellDeficit i J u v (s i))^2) ≤
      4000 * ((C : ℝ)^2 + (J : ℝ)^4) * (J : ℝ)^14 * Real.log (2 * J) := by
  let R (i : RationalPrimitiveCharacter) (j : ℕ) (k : Bool × Bool) :=
    dirichletJacobiCellRow i.2.1 (J^4) ((j : ℝ)^4) u v k.1 k.2
  have he (j : ℕ) (hj : j ∈ Ioc 0 J) :
      (∑ i ∈ rationalPrimitiveCharactersThrough C, ∑ k : Bool × Bool, ‖R i j k‖^2) ≤
        112 * ((C : ℝ)^2 + Real.pi * (J : ℝ)^4) * ((J : ℝ)^4)^3 * Real.log (2 * (J : ℝ)^4) := by
    have hx : (j : ℝ)^4 ≤ ((J^4 : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_left (mem_Ioc.mp hj).2 4
    have h := dirichletJacobiCellRow_primitive_sum_sq C (J^4) hC (one_le_pow₀ hJ) ((j : ℝ)^4)
      hx u v
    simp only [rationalPrimitiveCharactersThrough, sum_sigma]
    apply le_trans _ (by simpa only [Nat.cast_pow] using h)
    apply le_of_eq (sum_congr rfl ?_)
    intro m _
    exact (sum_subtype _ (fun χ : DirichletCharacter ℂ (m + 1) ↦ by simp)
      (fun χ ↦ ∑ k : Bool × Bool, ‖dirichletJacobiCellRow χ (J^4) ((j : ℝ)^4) u v k.1 k.2‖^2)).symm
  have h := selected_cell_centered_squares (rationalPrimitiveCharactersThrough C)
    primitivePrincipal J R s he
  have hprincipal (i : RationalPrimitiveCharacter) : rationalPrimitiveHeckeParameter i = 1 ↔
      i = primitivePrincipal := (rationalPrimitiveHeckeParameter_spec i).2.2.1.trans (primitivePrincipal_iff i)
  simpa only [rationalPrimitiveCellDeficit, rationalPrimitiveHeckeParameter_cell, hprincipal, R] using
    h.trans (centered_squares_fourth_power_bound (by exact_mod_cast hJ))

private theorem primitiveCharacters_card_pos {C : ℕ} (hC : 0 < C) :
    (0 : ℝ) < (rationalPrimitiveCharactersThrough C).card := by
  nlinarith only [primitiveCharacters_card_bound C, sq_pos_of_pos (by exact_mod_cast hC : (0 : ℝ) < C)]

/-- Fix any two auxiliary integers. The mean square of the actual, pole-centered
complete-cell deficit over primitive rational base characters is bounded uniformly in
the pair and every choice of signs, including choices made separately for each
character and each fourth-power sample. -/
theorem rationalPrimitiveCellDeficit_mean_sq (C J : ℕ) (hC : 0 < C) (hJ : 1 ≤ J)
    (u v : ℕ) (s : RationalPrimitiveCharacter → ℕ → Bool × Bool) :
    (∑ i ∈ rationalPrimitiveCharactersThrough C, (rationalPrimitiveCellDeficit i J u v (s i))^2) /
        (rationalPrimitiveCharactersThrough C).card ≤
      4096000 * (1 + (J : ℝ)^4 / (C : ℝ)^2) * (J : ℝ)^14 * Real.log (2 * J) := by
  have hc : 0 < (C : ℝ) := by exact_mod_cast hC
  have hlog : 0 ≤ Real.log (2 * J) := Real.log_nonneg
    (by linarith [show (1 : ℝ) ≤ J by exact_mod_cast hJ])
  have hscale : (C : ℝ)^2 + (J : ℝ)^4 ≤ (1 + (J : ℝ)^4 / (C : ℝ)^2) *
      (1024 * (rationalPrimitiveCharactersThrough C).card) := by
    calc _ = (1 + (J : ℝ)^4 / (C : ℝ)^2) * (C : ℝ)^2 := by field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_left (primitiveCharacters_card_bound C) (by positivity)
  apply (div_le_iff₀ (primitiveCharacters_card_pos hC)).mpr
  apply (rationalPrimitiveCellDeficit_sum_sq C J hC hJ u v s).trans
  calc _ ≤ 4000 * ((1 + (J : ℝ)^4 / (C : ℝ)^2) * (1024 * (rationalPrimitiveCharactersThrough C).card)) *
              (J : ℝ)^14 * Real.log (2 * J) := by gcongr
       _ = _ := by ring

private theorem dirichletJacobiCell_twoLevelTail {α β : Type*} (X : Finset α) (P : Finset β)
    (hP : P.Nonempty) (H : α → β → ℝ) {t δ E : ℝ} (ht : 0 ≤ t)
    (B : Finset α) (hB : B ⊆ X)
    (hbad : ∀ i ∈ B, δ * (P.card : ℝ) ≤ ((P.filter fun p ↦ t ≤ H i p).card : ℝ))
    (hbound : ∀ p ∈ P, (∑ i ∈ X, (H i p)^2) ≤ (X.card : ℝ) * E) :
    (B.card : ℝ) * δ * t^2 ≤ (X.card : ℝ) * E := by
  have hrow (i : α) (hi : i ∈ B) :
      (δ * P.card) * t^2 ≤ ∑ p ∈ P, (H i p)^2 := by
    let S := P.filter fun p ↦ t ≤ H i p
    calc
      _ ≤ (S.card : ℝ) * t^2 := mul_le_mul_of_nonneg_right (hbad i hi) (sq_nonneg _)
      _ = ∑ _p ∈ S, t^2 := by simp
      _ ≤ ∑ p ∈ S, (H i p)^2 :=
        sum_le_sum (fun p hp ↦ pow_le_pow_left₀ ht (mem_filter.mp hp).2 2)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun p _ _ ↦ sq_nonneg _)
  apply (mul_le_mul_iff_left₀ (by exact_mod_cast hP.card_pos : (0 : ℝ) < P.card)).mp
  calc
    _ = ∑ _i ∈ B, (δ * P.card) * t^2 := by simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ i ∈ B, ∑ p ∈ P, (H i p)^2 := sum_le_sum hrow
    _ = ∑ p ∈ P, ∑ i ∈ B, (H i p)^2 := sum_comm
    _ ≤ ∑ p ∈ P, ∑ i ∈ X, (H i p)^2 := sum_le_sum (fun p _ ↦
      sum_le_sum_of_subset_of_nonneg hB (fun i _ _ ↦ sq_nonneg _))
    _ ≤ ∑ _p ∈ P, (X.card : ℝ) * E := sum_le_sum hbound
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring

/-- At conductor cutoff `C ≥ J²`, take any nonempty finite collection of auxiliary
pairs and allow the two Jacobi signs to depend on the character, pair and sample.
The fraction of characters on which at least a `J^(-ε)` fraction of pairs reach
`J^(7+ε)` is at most `8192000 log(2J)/J^ε`. For positive ε this tends to zero. -/
theorem rationalPrimitiveCellDeficit_exception_proportion (C J : ℕ) (hJ : 1 ≤ J) (hsize : J^2 ≤ C)
    (P : Finset (ℕ × ℕ)) (hP : P.Nonempty) (ε : ℝ)
    (s : RationalPrimitiveCharacter → ℕ × ℕ → ℕ → Bool × Bool)
    (B : Finset RationalPrimitiveCharacter) (hB : B ⊆ rationalPrimitiveCharactersThrough C)
    (hbad : ∀ i ∈ B, (P.card : ℝ) / (J : ℝ)^ε ≤
      ((P.filter fun p ↦ (J : ℝ)^(7 + ε) ≤ rationalPrimitiveCellDeficit i J p.1 p.2 (s i p)).card : ℝ)) :
    (B.card : ℝ) / (rationalPrimitiveCharactersThrough C).card ≤
      8192000 * Real.log (2 * J) / (J : ℝ)^ε := by
  let X := rationalPrimitiveCharactersThrough C
  let H (i : RationalPrimitiveCharacter) (p : ℕ × ℕ) := rationalPrimitiveCellDeficit i J p.1 p.2 (s i p)
  let v := (J : ℝ)^ε
  have hj : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hC : 0 < C := lt_of_lt_of_le (pow_pos (by omega : 0 < J) 2) hsize
  have hX : (0 : ℝ) < X.card := primitiveCharacters_card_pos hC
  have hv : 0 < v := Real.rpow_pos_of_pos hj ε
  have hthreshold : (J : ℝ)^(7 + ε) = (J : ℝ)^7 * v := by
    rw [Real.rpow_add hj]
    norm_num [v]
  have hb (i : RationalPrimitiveCharacter) (hi : i ∈ B) :
      v⁻¹ * (P.card : ℝ) ≤ ((P.filter fun p ↦ (J : ℝ)^7 * v ≤ H i p).card : ℝ) := by
    simpa only [div_eq_inv_mul, hthreshold, H, v] using hbad i hi
  have hbounds (p : ℕ × ℕ) (_hp : p ∈ P) :
      (∑ i ∈ X, (H i p)^2) ≤ X.card * (8192000 * (J : ℝ)^14 * Real.log (2 * J)) := by
    have h := (div_le_iff₀ hX).mp
      (rationalPrimitiveCellDeficit_mean_sq C J hC hJ p.1 p.2 (fun i ↦ s i p))
    have hw : (J : ℝ)^4 ≤ (C : ℝ)^2 := by
      calc _ = ((J : ℝ)^2)^2 := by ring
           _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) (by exact_mod_cast hsize) _
    have hq := (div_le_one (pow_pos (by exact_mod_cast hC : (0 : ℝ) < C) 2)).mpr hw
    have hlog : 0 ≤ Real.log (2 * J) := Real.log_nonneg
      (by linarith [show (1 : ℝ) ≤ J by exact_mod_cast hJ])
    apply h.trans
    rw [mul_comm (X.card : ℝ)]
    gcongr
    linarith
  have hm := dirichletJacobiCell_twoLevelTail X P hP H (mul_nonneg (pow_nonneg hj.le 7) hv.le)
    B hB hb hbounds
  have hleft : (B.card : ℝ) * v⁻¹ * ((J : ℝ)^7 * v)^2 = (J : ℝ)^14 * ((B.card : ℝ) * v) := by
    field_simp
  have hright : (X.card : ℝ) * (8192000 * (J : ℝ)^14 * Real.log (2 * J)) =
      (J : ℝ)^14 * ((8192000 * Real.log (2 * J)) * X.card) := by ring
  rw [hleft, hright] at hm
  exact (div_le_div_iff₀ hX hv).mpr ((mul_le_mul_iff_right₀ (pow_pos hj 14)).mp hm)

end RiemannMasullo
