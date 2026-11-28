module

public import RiemannMasullo.ForMathlib.NumberTheory.DiophantineApproximation.SquaredHeightRecords
public import RiemannMasullo.ForMathlib.NumberTheory.DiophantineApproximation.ShrinkingTargets
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-!
# Scalar phase obstructions on the unit circle

The statements in this file assemble shrinking-target approximation and
squared-height records for actual complex unit phases. They are scalar facts;
no Hecke character is constructed and no declaration in issue #7336 is refuted.
-/

open Set Metric

public section

namespace RiemannMasullo.Isolated

/-- Superpolynomial approximation remains arbitrarily accurate after replacing
integer absolute height by any positive affine rescaling of it. -/
theorem superpolynomial_small_at_scaled_height
    (δ : ℤ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (happrox : ∀ k N : ℕ, ∃ n : ℤ, N ≤ n.natAbs ∧
      δ n < ((1 + (n.natAbs : ℝ)) ^ k)⁻¹)
    (c : ℝ) (hc : 0 < c) (A : ℝ) (hA : 0 ≤ A) (p N : ℕ) :
    ∃ n : ℤ, N ≤ n.natAbs ∧ A * (2 + c * |(n : ℝ)|) ^ p * δ n < 1 := by
  obtain ⟨M, hM⟩ := exists_nat_gt (A * (2 + c) ^ p)
  obtain ⟨n, hn, hsmall⟩ := happrox (p + 1) (max M N)
  have hMn : (M : ℝ) ≤ (n.natAbs : ℝ) := by
    exact_mod_cast (le_trans (le_max_left M N) hn)
  have hNn : N ≤ n.natAbs := le_trans (le_max_right M N) hn
  let b : ℝ := 1 + (n.natAbs : ℝ)
  have hb : 0 < b := by dsimp [b]; positivity
  have hAb : A * (2 + c) ^ p < b := by dsimp [b]; linarith
  have hnabs : |(n : ℝ)| = (n.natAbs : ℝ) := by simp
  have hheight : 2 + c * |(n : ℝ)| ≤ (2 + c) * b := by
    rw [hnabs]
    dsimp [b]
    nlinarith [show (0 : ℝ) ≤ n.natAbs by positivity]
  have hp : (2 + c * |(n : ℝ)|) ^ p ≤ ((2 + c) * b) ^ p := by
    gcongr
  have hpow : 0 < b ^ (p + 1) := pow_pos hb _
  have hs := mul_lt_mul_of_pos_right hsmall hpow
  change δ n * b ^ (p + 1) < (b ^ (p + 1))⁻¹ * b ^ (p + 1) at hs
  rw [inv_mul_cancel₀ hpow.ne'] at hs
  refine ⟨n, hNn, ?_⟩
  calc
    A * (2 + c * |(n : ℝ)|) ^ p * δ n ≤ A * ((2 + c) * b) ^ p * δ n := by
      gcongr
      exact hδ n
    _ = (A * (2 + c) ^ p) * (b ^ p * δ n) := by rw [mul_pow]; ring
    _ ≤ b * (b ^ p * δ n) :=
      mul_le_mul_of_nonneg_right hAb.le (mul_nonneg (pow_nonneg hb.le _) (hδ n))
    _ = δ n * b ^ (p + 1) := by rw [pow_succ]; ring
    _ < 1 := hs

/-- Under homogeneous polynomial separation, superpolynomially small shifted
errors occur on eligible strict squared-height records at arbitrarily large
signed integer indices. The last inequality defeats any prescribed polynomial
bound on those records. -/
theorem superpolynomial_errors_give_arbitrarily_small_records
    (z : ℤ → ℂ) (hpositive : ∀ n, 0 < ‖(1 : ℂ) - z n‖)
    (happrox : ∀ k N : ℕ, ∃ n : ℤ, N ≤ n.natAbs ∧
      ‖(1 : ℂ) - z n‖ < ((1 + (n.natAbs : ℝ)) ^ k)⁻¹)
    (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (d : ℕ)
    (hseparation : ∀ m n : ℤ, m ≠ n →
      1 ≤ C * (1 + |(m : ℝ) - (n : ℝ)|) ^ d * ‖z m - z n‖)
    (A : ℝ) (hA : 0 ≤ A) (p N : ℕ) :
    ∃ n : ℤ, N ≤ n.natAbs ∧ 0 < ‖(1 : ℂ) - z n‖ ∧ ‖(1 : ℂ) - z n‖ < 1 ∧
      (∀ m : ℤ, m ≠ n →
        2 + c * |(m : ℝ)| ≤ (2 + c * |(n : ℝ)|) ^ 2 →
        ‖(1 : ℂ) - z n‖ < ‖(1 : ℂ) - z m‖) ∧
      A * (2 + c * |(n : ℝ)|) ^ p * ‖(1 : ℂ) - z n‖ < 1 := by
  let K : ℝ := 2 * C * (1 + 2 / c) ^ d
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨n, hn, hs⟩ := superpolynomial_small_at_scaled_height
    (fun n ↦ ‖(1 : ℂ) - z n‖) (fun n ↦ norm_nonneg _) happrox c hc
    (1 + K + A) (by positivity) (2 * d + p) N
  let H : ℝ := 2 + c * |(n : ℝ)|
  have hH : 1 ≤ H := by dsimp [H]; nlinarith [mul_nonneg hc.le (abs_nonneg (n : ℝ))]
  have hp : H ^ p ≤ H ^ (2 * d + p) := pow_le_pow_right₀ hH (by omega)
  have hd : H ^ (2 * d) ≤ H ^ (2 * d + p) := pow_le_pow_right₀ hH (by omega)
  have hone : 1 ≤ H ^ (2 * d + p) := one_le_pow₀ hH
  have hδ : 0 ≤ ‖(1 : ℂ) - z n‖ := norm_nonneg _
  have hbase : (1 + K + A) * H ^ (2 * d + p) * ‖(1 : ℂ) - z n‖ < 1 := hs
  have heligible : ‖(1 : ℂ) - z n‖ < 1 := by
    have hcoef : 1 ≤ (1 + K + A) * H ^ (2 * d + p) := by
      nlinarith [mul_nonneg (show 0 ≤ K + A by positivity)
        (show 0 ≤ H ^ (2 * d + p) by positivity)]
    have hmul := mul_le_mul_of_nonneg_right hcoef hδ
    simp only [one_mul] at hmul
    exact hmul.trans_lt hbase
  have hcert : K * H ^ (2 * d) * ‖(1 : ℂ) - z n‖ < 1 := by
    have hcoef : K * H ^ (2 * d) ≤ (1 + K + A) * H ^ (2 * d + p) := by
      apply mul_le_mul (by linarith) hd (by positivity) (by positivity)
    exact (mul_le_mul_of_nonneg_right hcoef hδ).trans_lt hbase
  have hpoly : A * H ^ p * ‖(1 : ℂ) - z n‖ < 1 := by
    have hcoef : A * H ^ p ≤ (1 + K + A) * H ^ (2 * d + p) := by
      apply mul_le_mul (by linarith) hp (by positivity) (by positivity)
    exact (mul_le_mul_of_nonneg_right hcoef hδ).trans_lt hbase
  refine ⟨n, hn, hpositive n, heligible, ?_, hpoly⟩
  apply strong_approximation_is_squared_height_record z c C hc hC d hseparation n
  convert hcert using 1; dsimp [K, H]
  rw [mul_pow, ← pow_mul]
  ring

/-- A common integer power relation between a unit phase and an irrational
rotation forces the phase into the rational affine span of the rotation angle.
The assertion itself does not require irrationality. -/
theorem circle_power_eq_implies_rational_phase
    (α : ℝ) (β : Circle) (N : ℕ) (hN : 0 < N) (k : ℤ)
    (hclear : β ^ N = (AddCircle.toCircle (α : AddCircle (1 : ℝ))) ^ k) :
    ∃ q r : ℚ, β = AddCircle.toCircle
      (((q : ℝ) + (r : ℝ) * α : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨x, rfl⟩ := Circle.exp_surjective β
  rw [AddCircle.toCircle_apply_mk, div_one,
    ← Circle.exp_natCast_mul, ← Circle.exp_intCast_mul] at hclear
  obtain ⟨j, hj⟩ := Circle.exp_eq_exp.mp hclear
  refine ⟨(j : ℚ) / N, (k : ℚ) / N, ?_⟩
  rw [AddCircle.toCircle_apply_mk, div_one]
  congr 1
  push_cast
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  nlinarith [hj]

/-- The chordal denominator of a shifted phase is the ordinary metric distance
between the two points on the unit circle. -/
theorem circle_denominator_eq_dist (β r : Circle) :
    ‖(1 : ℂ) - (β : ℂ) / (r : ℂ)‖ = dist β r := by
  calc
    ‖(1 : ℂ) - (β : ℂ) / (r : ℂ)‖ = ‖((r : ℂ) - (β : ℂ)) / (r : ℂ)‖ := by
      rw [sub_div, div_self (Circle.coe_ne_zero r)]
    _ = ‖(r : ℂ) - (β : ℂ)‖ := by simp
    _ = dist β r := by rw [norm_sub_rev]; exact (dist_eq_norm (β : ℂ) (r : ℂ)).symm

/-- Every bounded absolute-height subset of the integers is finite. -/
private theorem finite_integer_height (N : ℕ) : Set.Finite {n : ℤ | n.natAbs < N} := by
  refine (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset ?_
  intro n hn
  have hc : (n.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast (Nat.le_of_lt hn)
  exact abs_le.mp (by simpa only [Int.natCast_natAbs] using hc)

/-- For any irrational rotation there is an actual complex unit phase with
superpolynomially small shifted denominators, but no common positive power
relation with the rotation. This is a scalar phase, not a Hecke character. -/
theorem exists_unit_phase_with_superpolynomial_denominators
    (α : ℝ) (hα : Irrational α) :
    ∃ β : Circle,
      (∀ N : ℕ, 0 < N → ∀ k : ℤ,
        β ^ N ≠ (AddCircle.toCircle (α : AddCircle (1 : ℝ))) ^ k) ∧
      (∀ k N : ℕ, ∃ n : ℤ, N ≤ n.natAbs ∧
        ‖(1 : ℂ) - (β : ℂ) /
          ((AddCircle.toCircle (α : AddCircle (1 : ℝ))) ^ n : Circle)‖ <
            ((1 + (n.natAbs : ℝ)) ^ k)⁻¹) := by
  let : Nontrivial Circle := ⟨⟨Circle.exp Real.pi, 1, Circle.exp_pi_ne_one⟩⟩
  let D : Set Circle := Set.range
    (fun qr : ℚ × ℚ ↦ AddCircle.toCircle
      (((qr.1 : ℝ) + (qr.2 : ℝ) * α : ℝ) : AddCircle (1 : ℝ)))
  let r : Circle := AddCircle.toCircle (α : AddCircle (1 : ℝ))
  have hu₀ : DenseRange (fun n : ℤ ↦ n • (α : AddCircle (1 : ℝ))) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using hα)
  have hu : DenseRange (fun n : ℤ ↦ r ^ n) := by
    simpa only [Function.comp_def, AddCircle.homeomorphCircle_apply,
      AddCircle.toCircle_zsmul, r] using
      (AddCircle.homeomorphCircle one_ne_zero).surjective.denseRange.comp hu₀
        (AddCircle.homeomorphCircle one_ne_zero).continuous
  obtain ⟨β, hβ⟩ := (shrinking_targets_dense_Gdelta_avoiding_countable
    (fun n : ℤ ↦ r ^ n) Int.natAbs hu finite_integer_height
    (fun k n ↦ ((1 + (n.natAbs : ℝ)) ^ k)⁻¹)
    (by intro k n; positivity) D (Set.countable_range _)).2.nonempty
  refine ⟨β, ?_, ?_⟩
  · intro N hN k hclear
    obtain ⟨q, t, heq⟩ := circle_power_eq_implies_rational_phase α β N hN k hclear
    exact hβ.2 ⟨(q, t), heq.symm⟩
  · intro k N
    obtain ⟨n, hn, hdist⟩ := hβ.1 k N
    refine ⟨n, hn, ?_⟩
    rw [circle_denominator_eq_dist]
    exact hdist

/-- The distance between two shifted orbit values is independent of the shift.
It is exactly the homogeneous denominator at the difference of the indices. -/
theorem circle_shifted_orbit_separation (β r : Circle) (m n : ℤ) :
    ‖(β : ℂ) / (r ^ m : Circle) - (β : ℂ) / (r ^ n : Circle)‖ =
      ‖(1 : ℂ) - (r ^ (m - n) : Circle)‖ := by
  have heq : (β : ℂ) / (r ^ m : Circle) - (β : ℂ) / (r ^ n : Circle) =
      ((β : ℂ) / (r ^ m : Circle)) * (1 - (r ^ (m - n) : Circle)) := by
    rw [zpow_sub, Circle.coe_mul, Circle.coe_inv]
    field_simp
  rw [heq, norm_mul]
  simp

/-- The scalar obstruction is realized by a unit complex phase with no common
clearing power. Under a homogeneous polynomial bound for an irrational rotation,
this one phase has arbitrarily large eligible strict squared-height records
violating every prescribed polynomial lower bound, at every positive height scale.
This theorem supplies no global arithmetic character realizing the phase. -/
theorem exists_unit_phase_with_superpolynomial_records
    (α : ℝ) (hα : Irrational α) (C : ℝ) (hC : 0 ≤ C) (d : ℕ)
    (hhomogeneous : ∀ q : ℤ, q ≠ 0 →
      1 ≤ C * (1 + |(q : ℝ)|) ^ d *
        ‖(1 : ℂ) - ((AddCircle.toCircle (α : AddCircle (1 : ℝ))) ^ q : Circle)‖) :
    ∃ β : Circle,
      (∀ N : ℕ, 0 < N → ∀ k : ℤ,
        β ^ N ≠ (AddCircle.toCircle (α : AddCircle (1 : ℝ))) ^ k) ∧
      ∀ c : ℝ, 0 < c → ∀ A : ℝ, 0 ≤ A → ∀ p N : ℕ,
      ∃ n : ℤ, N ≤ n.natAbs ∧
        0 < ‖(1 : ℂ) - (β : ℂ) /
          ((AddCircle.toCircle (α : AddCircle (1 : ℝ))) ^ n : Circle)‖ ∧
        ‖(1 : ℂ) - (β : ℂ) /
          ((AddCircle.toCircle (α : AddCircle (1 : ℝ))) ^ n : Circle)‖ < 1 ∧
        (∀ m : ℤ, m ≠ n →
          2 + c * |(m : ℝ)| ≤ (2 + c * |(n : ℝ)|) ^ 2 →
          ‖(1 : ℂ) - (β : ℂ) /
            ((AddCircle.toCircle (α : AddCircle (1 : ℝ))) ^ n : Circle)‖ <
          ‖(1 : ℂ) - (β : ℂ) /
            ((AddCircle.toCircle (α : AddCircle (1 : ℝ))) ^ m : Circle)‖) ∧
        A * (2 + c * |(n : ℝ)|) ^ p *
          ‖(1 : ℂ) - (β : ℂ) /
            ((AddCircle.toCircle (α : AddCircle (1 : ℝ))) ^ n : Circle)‖ < 1 := by
  obtain ⟨β, hclear, happrox⟩ := exists_unit_phase_with_superpolynomial_denominators α hα
  let r : Circle := AddCircle.toCircle (α : AddCircle (1 : ℝ))
  let z : ℤ → ℂ := fun n ↦ (β : ℂ) / (r ^ n : Circle)
  have hpositive : ∀ n, 0 < ‖(1 : ℂ) - z n‖ := by
    intro n
    change 0 < ‖(1 : ℂ) - (β : ℂ) / (r ^ n : Circle)‖
    rw [circle_denominator_eq_dist, dist_pos]
    simpa only [pow_one] using hclear 1 (by norm_num) n
  have hsep : ∀ m n : ℤ, m ≠ n →
      1 ≤ C * (1 + |(m : ℝ) - (n : ℝ)|) ^ d * ‖z m - z n‖ := by
    intro m n hmn
    have h := hhomogeneous (m - n) (sub_ne_zero.mpr hmn)
    simpa only [Int.cast_sub, z, r, circle_shifted_orbit_separation] using h
  refine ⟨β, hclear, ?_⟩
  intro c hc A hA p N
  exact superpolynomial_errors_give_arbitrarily_small_records z hpositive happrox
    c C hc hC d hsep A hA p N

/-- A dense family realizes every finite collection of strict metric conditions
that is simultaneously satisfied by a target. The chosen family member may
depend on the whole finite collection; this is not an infinite-pattern theorem. -/
theorem dense_family_realizes_finite_strict_patterns
    {X I J : Type*} [MetricSpace X] (f : I → X) (hf : DenseRange f)
    (centers : J → X) (radii : J → ℝ) (s : Finset J) (target : X)
    (htarget : ∀ j ∈ s, dist target (centers j) < radii j) :
    ∃ i : I, ∀ j ∈ s, dist (f i) (centers j) < radii j := by
  let U : Set X := ⋂ j ∈ s, Metric.ball (centers j) (radii j)
  have hopen : IsOpen U := isOpen_biInter_finset (fun _ _ ↦ Metric.isOpen_ball)
  have hmem : target ∈ U := by simpa only [U, Set.mem_iInter, Metric.mem_ball] using htarget
  obtain ⟨x, hx, i, rfl⟩ := hf.inter_open_nonempty U hopen ⟨target, hmem⟩
  exact ⟨i, by simpa only [U, Set.mem_iInter, Metric.mem_ball] using hx⟩

/-- A unit phase with no nontrivial torsion relation has dense integer powers.
This is the circle-rotation fact used when passing from one arithmetic character
to its integer powers. -/
theorem dense_circle_powers_of_no_torsion (a : Circle)
    (ha : ∀ n : ℕ, 0 < n → a ^ n ≠ 1) : DenseRange (fun k : ℤ ↦ a ^ k) := by
  let e := AddCircle.homeomorphCircle (show (1 : ℝ) ≠ 0 by norm_num)
  let θ : AddCircle (1 : ℝ) := e.symm a
  have hθ : AddCircle.toCircle θ = a := by
    rw [← AddCircle.homeomorphCircle_apply (show (1 : ℝ) ≠ 0 by norm_num)]
    exact e.apply_symm_apply a
  have hord : addOrderOf θ = 0 := by
    apply addOrderOf_eq_zero_iff'.mpr
    intro n hn hz
    apply ha n hn
    rw [← hθ, ← AddCircle.toCircle_nsmul, hz, AddCircle.toCircle_zero]
  have hd : DenseRange (fun k : ℤ ↦ k • θ) := AddCircle.denseRange_zsmul_iff.mpr hord
  simpa only [Function.comp_def, e, AddCircle.homeomorphCircle_apply,
    AddCircle.toCircle_zsmul, hθ] using e.surjective.denseRange.comp hd e.continuous

/-- Powers of one non-torsion unit phase realize every finite family of strict
chordal error bounds satisfied by a target, with the power index arbitrarily
large. The power can depend on the finite family; no assertion interchanges
these quantifiers to realize infinitely many bounds with one power. -/
theorem circle_powers_realize_finite_denominator_patterns
    (a r β : Circle) (ha : ∀ n : ℕ, 0 < n → a ^ n ≠ 1)
    (s : Finset ℤ) (radii : ℤ → ℝ) (N : ℕ)
    (hβ : ∀ n ∈ s, ‖(1 : ℂ) - (β : ℂ) / (r ^ n : Circle)‖ < radii n) :
    ∃ k : ℤ, N ≤ k.natAbs ∧ ∀ n ∈ s,
      ‖(1 : ℂ) - (a ^ k : Circle) / (r ^ n : Circle)‖ < radii n := by
  let : Nontrivial Circle := ⟨⟨Circle.exp Real.pi, 1, Circle.exp_pi_ne_one⟩⟩
  let U : Set Circle := ⋂ n ∈ s, Metric.ball (r ^ n) (radii n)
  have hopen : IsOpen U := isOpen_biInter_finset (fun _ _ ↦ Metric.isOpen_ball)
  have hmem : β ∈ U := by
    simpa only [U, Set.mem_iInter, Metric.mem_ball, circle_denominator_eq_dist] using hβ
  have hd := dense_image_height_tail (fun k : ℤ ↦ a ^ k) Int.natAbs
    (dense_circle_powers_of_no_torsion a ha) finite_integer_height N
  obtain ⟨x, hx, k, hk, rfl⟩ := hd.inter_open_nonempty U hopen ⟨β, hmem⟩
  refine ⟨k, hk, ?_⟩
  simpa only [U, Set.mem_iInter, Metric.mem_ball, circle_denominator_eq_dist] using hx

/-- The absence of a common clearing power is preserved under every nonzero
integer power of the phase, including negative powers. -/
theorem no_clearing_power_preserved_by_zpow
    {G : Type*} [Group G] (a r : G)
    (ha : ∀ N : ℕ, 0 < N → ∀ l : ℤ, a ^ N ≠ r ^ l)
    (k : ℤ) (hk : k ≠ 0) :
    ∀ N : ℕ, 0 < N → ∀ l : ℤ, (a ^ k) ^ N ≠ r ^ l := by
  have hzn : ∀ q : ℤ, q ≠ 0 → ∀ l : ℤ, a ^ q ≠ r ^ l := by
    intro q hq l hrel
    cases q with
    | ofNat n =>
        exact ha n (by exact_mod_cast (Int.ofNat_ne_zero.mp hq).bot_lt) l
          (by simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hrel)
    | negSucc n =>
        apply ha (n + 1) (by omega) (-l)
        simpa only [zpow_negSucc, inv_inv, zpow_neg] using congrArg Inv.inv hrel
  intro N hN l hrel
  apply hzn (k * (N : ℤ)) (mul_ne_zero hk (by exact_mod_cast hN.ne')) l
  simpa only [zpow_mul, zpow_natCast] using hrel

/-- If a unit phase has no common clearing power with the primary rotation,
its nonzero powers retain that exclusion and positive denominators, while
realizing every finite strict upper-bound pattern satisfied by a target.
This is the precise finite-depth statement used for powers of a Hecke character. -/
theorem nonclearing_circle_powers_realize_finite_patterns
    (a r β : Circle)
    (ha : ∀ N : ℕ, 0 < N → ∀ l : ℤ, a ^ N ≠ r ^ l)
    (s : Finset ℤ) (radii : ℤ → ℝ) (N : ℕ)
    (hβ : ∀ n ∈ s, ‖(1 : ℂ) - (β : ℂ) / (r ^ n : Circle)‖ < radii n) :
    ∃ k : ℤ, N ≤ k.natAbs ∧ k ≠ 0 ∧
      (∀ M : ℕ, 0 < M → ∀ l : ℤ, (a ^ k) ^ M ≠ r ^ l) ∧
      (∀ n : ℤ, 0 < ‖(1 : ℂ) - (a ^ k : Circle) / (r ^ n : Circle)‖) ∧
      ∀ n ∈ s, ‖(1 : ℂ) - (a ^ k : Circle) / (r ^ n : Circle)‖ < radii n := by
  have hnt : ∀ M : ℕ, 0 < M → a ^ M ≠ 1 := by
    intro M hM
    simpa only [zpow_zero] using ha M hM 0
  obtain ⟨k, hkN, hpattern⟩ := circle_powers_realize_finite_denominator_patterns
    a r β hnt s radii (max N 1) hβ
  have hk : k ≠ 0 := Int.natAbs_pos.mp (by omega)
  have hclear := no_clearing_power_preserved_by_zpow a r ha k hk
  refine ⟨k, le_trans (le_max_left N 1) hkN, hk, hclear, ?_, hpattern⟩
  intro n
  rw [circle_denominator_eq_dist, dist_pos]
  simpa only [pow_one] using hclear 1 (by norm_num) n

/-- A dense family realizes every finite collection of strict continuous real
inequalities that holds at a target. Unlike an upper-error-only statement,
this also transfers finite strict record comparisons and nonvanishing margins. -/
theorem dense_family_realizes_finite_continuous_inequalities
    {X I J : Type*} [TopologicalSpace X] (f : I → X) (hf : DenseRange f)
    (g : J → X → ℝ) (hg : ∀ j, Continuous (g j)) (s : Finset J) (target : X)
    (htarget : ∀ j ∈ s, g j target < 0) :
    ∃ i : I, ∀ j ∈ s, g j (f i) < 0 := by
  let U : Set X := ⋂ j ∈ s, {x | g j x < 0}
  have hopen : IsOpen U := isOpen_biInter_finset
    (fun j _ ↦ isOpen_lt (hg j) continuous_const)
  have hmem : target ∈ U := by simpa only [U, Set.mem_iInter, Set.mem_ofPred_eq] using htarget
  obtain ⟨x, hx, i, rfl⟩ := hf.inter_open_nonempty U hopen ⟨target, hmem⟩
  exact ⟨i, by simpa only [U, Set.mem_iInter, Set.mem_ofPred_eq] using hx⟩

/-- Cancelling the common nonzero exponential in the shifted power equation
leaves a relation between the phase power and the common shift alone. -/
theorem shifted_phase_power_iff (a L s σ : ℂ) (N : ℕ) :
    (a * Complex.exp (-s * L)) ^ N =
      Complex.exp (-(N : ℂ) * L * (s - σ)) ↔
    a ^ N = Complex.exp ((N : ℂ) * L * σ) := by
  rw [mul_pow, ← Complex.exp_nat_mul]
  have heq : -(N : ℂ) * L * (s - σ) =
      (N : ℂ) * L * σ + (N : ℂ) * (-s * L) := by ring
  rw [heq, Complex.exp_add]
  constructor
  · exact mul_right_cancel₀ (Complex.exp_ne_zero _)
  · intro h
    rw [h]

/-- For any nonempty family of primary pole centers, the existence of a common
complex clearing shift is exactly an integer phase-power relation. The primary
centers are assumed to satisfy their defining exponential equation. -/
theorem common_shift_exists_iff_phase_power_relation
    {I : Type*} [Nonempty I] (a w L : ℂ) (hw : w ≠ 0)
    (s : I → ℂ) (N : ℕ) (hN : 0 < N)
    (hprimary : ∀ i, Complex.exp (-(N : ℂ) * w * s i) = 1) :
    (∃ σ : ℂ, ∀ i,
      Complex.exp (-(N : ℂ) * w * (s i - σ)) = 1 ∧
      (a * Complex.exp (-s i * L)) ^ N =
        Complex.exp (-(N : ℂ) * L * (s i - σ))) ↔
    ∃ k : ℤ, a ^ N = Complex.exp ((k : ℂ) * (2 * Real.pi * Complex.I) * (L / w)) := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hprim (σ : ℂ) (i : I) :
      Complex.exp (-(N : ℂ) * w * (s i - σ)) =
        Complex.exp ((N : ℂ) * w * σ) := by
    have heq : -(N : ℂ) * w * (s i - σ) =
        -(N : ℂ) * w * s i + (N : ℂ) * w * σ := by ring
    rw [heq, Complex.exp_add, hprimary i, one_mul]
  constructor
  · rintro ⟨σ, hσ⟩
    let i : I := Classical.choice inferInstance
    have hp := (hσ i).1
    rw [hprim] at hp
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hp
    refine ⟨k, ?_⟩
    have ha := (shifted_phase_power_iff a L (s i) σ N).mp (hσ i).2
    rw [ha]
    congr 1
    calc
      (N : ℂ) * L * σ = ((N : ℂ) * w * σ) * (L / w) := by field_simp
      _ = (k : ℂ) * (2 * Real.pi * Complex.I) * (L / w) := by rw [hk]
  · rintro ⟨k, hk⟩
    let σ : ℂ := ((k : ℂ) * (2 * Real.pi * Complex.I)) / ((N : ℂ) * w)
    have hσw : (N : ℂ) * w * σ = (k : ℂ) * (2 * Real.pi * Complex.I) := by
      dsimp [σ]
      field_simp
    have hσL : (N : ℂ) * L * σ =
        (k : ℂ) * (2 * Real.pi * Complex.I) * (L / w) := by
      dsimp [σ]
      field_simp
    refine ⟨σ, fun i ↦ ⟨?_, ?_⟩⟩
    · rw [hprim, hσw, Complex.exp_int_mul_two_pi_mul_I]
    · apply (shifted_phase_power_iff a L (s i) σ N).mpr
      rw [hσL]
      exact hk

/-- For real logarithmic periods, the exact complex common-shift condition is
equivalent to a common power relation on the unit circle. Thus the power
exclusion in `exists_unit_phase_with_superpolynomial_records` excludes the full
complex clearing shift, not merely a real or purely imaginary guess for it. -/
theorem common_shift_exists_iff_circle_power_relation
    {I : Type*} [Nonempty I] (β : Circle) (w L : ℝ) (hw : w ≠ 0)
    (s : I → ℂ) (N : ℕ) (hN : 0 < N)
    (hprimary : ∀ i, Complex.exp (-(N : ℂ) * (w : ℂ) * s i) = 1) :
    (∃ σ : ℂ, ∀ i,
      Complex.exp (-(N : ℂ) * (w : ℂ) * (s i - σ)) = 1 ∧
      ((β : ℂ) * Complex.exp (-s i * (L : ℂ))) ^ N =
        Complex.exp (-(N : ℂ) * (L : ℂ) * (s i - σ))) ↔
    ∃ k : ℤ, β ^ N = (AddCircle.toCircle ((L / w : ℝ) : AddCircle (1 : ℝ))) ^ k := by
  have hwC : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  rw [common_shift_exists_iff_phase_power_relation (β : ℂ) (w : ℂ) (L : ℂ)
    hwC s N hN hprimary]
  apply exists_congr
  intro k
  have hexp : Complex.exp ((k : ℂ) * (2 * Real.pi * Complex.I) * ((L : ℂ) / (w : ℂ))) =
      (((AddCircle.toCircle ((L / w : ℝ) : AddCircle (1 : ℝ))) ^ k : Circle) : ℂ) := by
    simp only [AddCircle.toCircle_apply_mk, div_one, Circle.coe_zpow, Circle.coe_exp]
    rw [← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  rw [hexp, ← Circle.coe_pow, Circle.coe_inj]

/-- Simultaneously twisting a local phase and translating its pole center leaves
the Euler-factor value unchanged. In the application, `τ = I*t` is a norm twist
and `L = log (Nv)`. This algebraic identity makes no Hecke-realization claim. -/
theorem phase_twist_and_pole_translation_cancel (a τ s L : ℂ) :
    (a * Complex.exp (-τ * L)) * Complex.exp (-(s - τ) * L) =
      a * Complex.exp (-s * L) := by
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

end RiemannMasullo.Isolated
