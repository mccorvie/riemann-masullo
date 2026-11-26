module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Finite Dirichlet twists of rational theta sums

The approximation used for Theorem 12.5.1.1 (pp. 519–520) over the rationals has finite
visible sums with Möbius coefficients. Twisting by all characters of a prime modulus above
the largest visible norm cancels every term pairing different norms. The mean squared error
equals its diagonal for any common detector and physical measure. For a smaller modulus,
the exact formula groups the norms by residue class and gives an occupancy bound.

A prescribed character can carry the whole error even when the mean is small. Explicit
coefficients realize this concentration for every positive modulus. Constant coefficients on positive integer norms keep the trivial response
one as the character mean tends to zero. For primitive twists,
Gauss sums reduce the corresponding estimate to additive sampling at reduced residues.
-/

open Finset Complex MeasureTheory ArithmeticFunction
open scoped ComplexConjugate Classical

public noncomputable section

namespace RiemannMasullo

private theorem thetaAverage_character_kernel {q : ℕ} [NeZero q] (a b : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, conj (χ a) * χ b =
      if IsUnit a ∧ a = b then (q.totient : ℂ) else 0 := by
  classical
  by_cases h : IsUnit a
  · simp only [h, true_and]
    rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ h b]
    apply Finset.sum_congr rfl
    intro χ _
    have hn : χ a ≠ 0 := (h.map χ).ne_zero
    have hc : conj (χ a) * χ a = 1 := by
      change star (χ a) * χ a = 1
      rw [MulChar.star_apply', MulChar.inv_apply_eq_inv', inv_mul_cancel₀ hn]
    have hi : χ a⁻¹ * χ a = 1 := by
      rw [← map_mul, mul_comm a⁻¹ a, ZMod.mul_inv_of_unit a h, map_one]
    exact congrArg (· * χ b) (mul_right_cancel₀ hn (hc.trans hi.symm))
  · simp [h, MulChar.map_nonunit _ h]

private theorem thetaAverage_residue_parseval {q : ℕ} [NeZero q] (A : ZMod q → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ a : ZMod q, χ a * A a‖ ^ 2 =
      q.totient * ∑ a : ZMod q, if IsUnit a then ‖A a‖ ^ 2 else 0 := by
  classical
  apply Complex.ofReal_injective
  have norm' (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = conj z * z := by
    rw [Complex.sq_norm, ← Complex.mul_conj, mul_comm]
  push_cast only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, apply_ite,
    Complex.ofReal_zero]
  simp only [norm', map_sum, map_mul]
  calc
    _ = ∑ a : ZMod q, ∑ b : ZMod q, (conj (A a) * A b) *
          (∑ χ : DirichletCharacter ℂ q, conj (χ a) * χ b) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : IsUnit a
      · simp [thetaAverage_character_kernel, ha, mul_comm]
      · simp [thetaAverage_character_kernel, ha]

/-- The finite sum of coefficients on integer norms twisted by a rational Dirichlet character. -/
@[expose] def dirichletThetaRow {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ n ∈ S, χ (n : ZMod q) * f n

/-- The coefficients on integer norms in a single residue class, summed before squaring. -/
@[expose] def dirichletThetaResidueRow {q : ℕ} (a : ZMod q) (S : Finset ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ n ∈ S.filter (fun n : ℕ ↦ (n : ZMod q) = a), f n

private theorem thetaAverage_collect_residues {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (S : Finset ℕ) (f : ℕ → ℂ) :
    dirichletThetaRow χ S f = ∑ a : ZMod q, χ a * dirichletThetaResidueRow a S f := by
  unfold dirichletThetaRow dirichletThetaResidueRow
  rw [← S.sum_fiberwise (fun n : ℕ ↦ (n : ZMod q)) (fun n : ℕ ↦ χ (n : ZMod q) * f n)]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [(Finset.mem_filter.mp hn).2]

/-- The exact character second moment groups the coefficients by unit residue class. -/
theorem dirichletThetaRow_sum_sq_eq_residue_rows {q : ℕ} [NeZero q] (S : Finset ℕ) (f : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖dirichletThetaRow χ S f‖ ^ 2 =
      q.totient * ∑ a : ZMod q, if IsUnit a then ‖dirichletThetaResidueRow a S f‖ ^ 2 else 0 := by
  simpa only [thetaAverage_collect_residues] using thetaAverage_residue_parseval (q := q) (fun a ↦ dirichletThetaResidueRow a S f)

/-- A bound on the number of norms in each unit class bounds the character second moment. -/
theorem dirichletThetaRow_sum_sq_le_of_fiber_card {q H : ℕ} [NeZero q] (S : Finset ℕ) (f : ℕ → ℂ)
    (hH : ∀ a : ZMod q, IsUnit a → (S.filter (fun n : ℕ ↦ (n : ZMod q) = a)).card ≤ H) :
    ∑ χ : DirichletCharacter ℂ q, ‖dirichletThetaRow χ S f‖ ^ 2 ≤
      q.totient * ((H : ℝ) * ∑ n ∈ S, ‖f n‖ ^ 2) := by
  classical
  rw [dirichletThetaRow_sum_sq_eq_residue_rows, ← S.sum_fiberwise (fun n : ℕ ↦ (n : ZMod q)) (fun n ↦ ‖f n‖ ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : IsUnit a
  · rw [ite_eq_left ha]
    let B := S.filter fun n : ℕ ↦ (n : ZMod q) = a
    calc
      ‖dirichletThetaResidueRow a S f‖ ^ 2 ≤ (∑ n ∈ B, ‖f n‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le B f) 2
      _ ≤ B.card * ∑ n ∈ B, ‖f n‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hH a ha) (by positivity)
  · rw [ite_eq_right ha]
    positivity

/-- Distinct residues remove all pairs of unequal norms. Nonunits contribute zero. -/
theorem dirichletThetaRow_sum_sq_of_injective {q : ℕ} [NeZero q] (S : Finset ℕ) (f : ℕ → ℂ)
    (hinj : Set.InjOn (fun n : ℕ ↦ (n : ZMod q)) S) :
    ∑ χ : DirichletCharacter ℂ q, ‖dirichletThetaRow χ S f‖ ^ 2 =
      q.totient * ∑ n ∈ S, if IsUnit (n : ZMod q) then ‖f n‖ ^ 2 else 0 := by
  classical
  rw [dirichletThetaRow_sum_sq_eq_residue_rows, ← S.sum_fiberwise (fun n : ℕ ↦ (n : ZMod q))
    (fun n ↦ if IsUnit (n : ZMod q) then ‖f n‖ ^ 2 else 0)]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  let B := S.filter fun n : ℕ ↦ (n : ZMod q) = a
  rcases B.eq_empty_or_nonempty with h | ⟨n, hn⟩
  · change (if IsUnit a then ‖∑ n ∈ B, f n‖ ^ 2 else 0) = ∑ n ∈ B, _
    simp [h]
  · obtain ⟨hnS, hna⟩ := Finset.mem_filter.mp hn
    have he : B = {n} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hn, fun m hm ↦ ?_⟩
      obtain ⟨hmS, hma⟩ := Finset.mem_filter.mp hm
      exact hinj hmS hnS (hma.trans hna.symm)
    change (if IsUnit a then ‖∑ n ∈ B, f n‖ ^ 2 else 0) = ∑ n ∈ B, _
    simp [he, hna]

private theorem thetaAverage_residue_shell_card {q L U : ℕ} [NeZero q] (S : Finset ℕ) (hS : ∀ n ∈ S, L ≤ n ∧ n ≤ U)
    (a : ZMod q) :
    (S.filter (fun n : ℕ ↦ (n : ZMod q) = a)).card ≤ U / q + 1 - L / q := by
  have h := Finset.card_le_card_of_injOn (s := S.filter (fun n : ℕ ↦ (n : ZMod q) = a))
    (t := Finset.Icc (L / q) (U / q)) (fun n ↦ n / q)
    (by
      intro n hn
      have h := hS n (Finset.mem_filter.mp hn).1
      exact Finset.mem_Icc.mpr ⟨Nat.div_le_div_right h.1, Nat.div_le_div_right h.2⟩)
    (by
      intro n hn m hm hdiv
      have he := (Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hm).2.symm
      have hmod := (ZMod.natCast_eq_natCast_iff' n m q).mp he
      change n / q = m / q at hdiv
      rw [← Nat.mod_add_div n q, ← Nat.mod_add_div m q, hdiv, hmod])
  simpa only [Nat.card_Icc] using h

/-- For norms in an integer interval, each unit class meets at most the indicated number of quotient values. -/
theorem dirichletThetaRow_sum_sq_le_shell {q L U : ℕ} [NeZero q] (S : Finset ℕ) (f : ℕ → ℂ)
    (hS : ∀ n ∈ S, L ≤ n ∧ n ≤ U) :
    ∑ χ : DirichletCharacter ℂ q, ‖dirichletThetaRow χ S f‖ ^ 2 ≤
      q.totient * (((U / q + 1 - L / q : ℕ) : ℝ) * ∑ n ∈ S, ‖f n‖ ^ 2) :=
  dirichletThetaRow_sum_sq_le_of_fiber_card S f (fun a _ ↦ thetaAverage_residue_shell_card S hS a)

private theorem thetaAverage_small_norms_injective {q : ℕ} (S : Finset ℕ) (hS : ∀ n ∈ S, n < q) :
    Set.InjOn (fun n : ℕ ↦ (n : ZMod q)) S := by
  intro n hn m hm he
  simpa only [Nat.mod_eq_of_lt (hS n hn), Nat.mod_eq_of_lt (hS m hm)] using
    (ZMod.natCast_eq_natCast_iff' n m q).mp he

/-- A prime modulus above every positive norm gives exact cancellation of all unequal pairs. -/
theorem dirichletThetaRow_sum_sq_of_prime {q : ℕ} (hp : q.Prime) (S : Finset ℕ) (f : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n ∧ n < q) :
    ∑ χ : DirichletCharacter ℂ q, ‖dirichletThetaRow χ S f‖ ^ 2 =
      q.totient * ∑ n ∈ S, ‖f n‖ ^ 2 := by
  have : NeZero q := ⟨hp.ne_zero⟩
  rw [dirichletThetaRow_sum_sq_of_injective S f (thetaAverage_small_norms_injective S (fun n hn ↦ (hS n hn).2))]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have h := hS n hn
  apply ite_eq_left
  exact (ZMod.isUnit_iff_coprime n q).mpr ((hp.coprime_iff_not_dvd.mpr
    (fun hd ↦ (Nat.le_of_dvd h.1 hd).not_gt h.2)).symm)

private theorem thetaAverage_integrable_row_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {q : ℕ} (χ : DirichletCharacter ℂ q) {S : Finset ℕ} {f : ℕ → α → ℂ}
    (hf : ∀ n ∈ S, MemLp (f n) 2 μ) :
    Integrable (fun y ↦ ‖dirichletThetaRow χ S (fun n ↦ f n y)‖ ^ 2) μ := by
  have h := memLp_finsetSum S (fun n hn ↦ (hf n hn).const_smul (χ (n : ZMod q)))
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

/-- For an arbitrary physical measure, the integrated mean square of the twists equals the
diagonal when the prime modulus separates all positive norms. -/
theorem dirichletThetaRow_integral_sum_sq_of_prime {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {q : ℕ} (hp : q.Prime) (S : Finset ℕ) {f : ℕ → α → ℂ}
    (hS : ∀ n ∈ S, 0 < n ∧ n < q) (hf : ∀ n ∈ S, MemLp (f n) 2 μ) :
    ∑ χ : DirichletCharacter ℂ q, (∫ y, ‖dirichletThetaRow χ S (fun n ↦ f n y)‖ ^ 2 ∂μ) =
      q.totient * ∑ n ∈ S, ∫ y, ‖f n y‖ ^ 2 ∂μ := by
  rw [← integral_finsetSum _ (fun χ _ ↦ thetaAverage_integrable_row_sq χ hf)]
  simp_rw [dirichletThetaRow_sum_sq_of_prime hp S _ hS]
  rw [integral_const_mul, integral_finsetSum _ (fun n hn ↦
    (memLp_two_iff_integrable_sq_norm (hf n hn).aestronglyMeasurable).mp (hf n hn))]

/-- An interval of norms also gives an integrated upper bound when residue classes can overlap. -/
theorem dirichletThetaRow_integral_sum_sq_le_shell {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {q L U : ℕ} [NeZero q] (S : Finset ℕ) {f : ℕ → α → ℂ}
    (hS : ∀ n ∈ S, L ≤ n ∧ n ≤ U) (hf : ∀ n ∈ S, MemLp (f n) 2 μ) :
    ∑ χ : DirichletCharacter ℂ q, (∫ y, ‖dirichletThetaRow χ S (fun n ↦ f n y)‖ ^ 2 ∂μ) ≤
      (q.totient : ℝ) * (U / q + 1 - L / q : ℕ) * ∑ n ∈ S, ∫ y, ‖f n y‖ ^ 2 ∂μ := by
  have hi := integrable_finsetSum S (fun n hn ↦
    (memLp_two_iff_integrable_sq_norm (hf n hn).aestronglyMeasurable).mp (hf n hn))
  rw [← integral_finsetSum _ (fun χ _ ↦ thetaAverage_integrable_row_sq χ hf),
    ← integral_finsetSum S (fun n hn ↦
    (memLp_two_iff_integrable_sq_norm (hf n hn).aestronglyMeasurable).mp (hf n hn)),
    ← integral_const_mul]
  apply integral_mono (integrable_finsetSum _ (fun χ _ ↦ thetaAverage_integrable_row_sq χ hf)) (hi.const_mul _)
  intro y
  simpa only [mul_assoc] using dirichletThetaRow_sum_sq_le_shell S (fun n ↦ f n y) hS

private theorem thetaAverage_exception_count {ι : Type*} [Fintype ι] (E : ι → ℝ)
    (hE : ∀ i, 0 ≤ E i) (B : Finset ι) {δ : ℝ} (hB : ∀ i ∈ B, δ ≤ E i) :
    B.card * δ ≤ ∑ i, E i := by
  calc
    _ = ∑ _i ∈ B, δ := by simp
    _ ≤ ∑ i ∈ B, E i := Finset.sum_le_sum hB
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) (fun i _ _ ↦ hE i)

/-- The number of characters with energy at least the threshold is bounded by the integrated diagonal.
The inequality is useful for a positive threshold. -/
theorem dirichletThetaRow_exception_count {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {q : ℕ} (hp : q.Prime) (S : Finset ℕ) {f : ℕ → α → ℂ}
    (hS : ∀ n ∈ S, 0 < n ∧ n < q) (hf : ∀ n ∈ S, MemLp (f n) 2 μ)
    (B : Finset (DirichletCharacter ℂ q)) (δ : ℝ)
    (hB : ∀ χ ∈ B, δ ≤ ∫ y, ‖dirichletThetaRow χ S (fun n ↦ f n y)‖ ^ 2 ∂μ) :
    B.card * δ ≤ q.totient * ∑ n ∈ S, ∫ y, ‖f n y‖ ^ 2 ∂μ := by
  rw [← dirichletThetaRow_integral_sum_sq_of_prime hp S hS hf]
  exact thetaAverage_exception_count _ (fun χ ↦ integral_nonneg (fun y ↦ sq_nonneg _)) B hB

/-- The Möbius-weighted dilation coefficient at a rational norm, with the unit target subtracted. -/
@[expose] def thetaMoebiusErrorCoefficient (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) * w d) - if n = 1 then 1 else 0

/-- The error coefficient vanishes throughout any initial interval on which the taper is one. -/
theorem thetaMoebiusErrorCoefficient_eq_zero {w : ℕ → ℂ} {L n : ℕ} (hw : ∀ d ≤ L, w d = 1) (hn : n ≤ L) :
    thetaMoebiusErrorCoefficient w n = 0 := by
  unfold thetaMoebiusErrorCoefficient
  rw [sub_eq_zero]
  calc
    _ = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hw d ((Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.dvd_of_mem_divisors hd)).trans hn), mul_one]
    _ = _ := by
      have h : (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) = if n = 1 then 1 else 0 := by
        rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta]
        rfl
      split_ifs at h ⊢ <;> exact_mod_cast h

/-- For the visible Möbius error with common detector h(n/y), distinct-norm pairs cancel
exactly after averaging over the finite Dirichlet characters. -/
theorem thetaMoebius_visible_twist_energy {q : ℕ} (hp : q.Prime) (S : Finset ℕ) (w : ℕ → ℂ) (h : ℝ → ℂ)
    (μ : Measure ℝ) (hS : ∀ n ∈ S, 0 < n ∧ n < q)
    (hh : ∀ n ∈ S, MemLp (fun y : ℝ ↦ h (n / y)) 2 μ) :
    ∑ χ : DirichletCharacter ℂ q,
      (∫ y, ‖∑ n ∈ S, χ (n : ZMod q) * (thetaMoebiusErrorCoefficient w n * h (n / y))‖ ^ 2 ∂μ) =
      q.totient * ∑ n ∈ S, ∫ y : ℝ, ‖thetaMoebiusErrorCoefficient w n * h (n / y)‖ ^ 2 ∂μ :=
  dirichletThetaRow_integral_sum_sq_of_prime (f := fun n y ↦ thetaMoebiusErrorCoefficient w n * h (n / y)) hp S hS
    (fun n hn ↦ (hh n hn).const_smul (thetaMoebiusErrorCoefficient w n))

/-- The deviations of the remaining characters add up to the negative deviation of any one fixed character. -/
theorem dirichletThetaRow_sum_deviation_erase {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {q : ℕ} (hp : q.Prime) (S : Finset ℕ) {f : ℕ → α → ℂ}
    (hS : ∀ n ∈ S, 0 < n ∧ n < q) (hf : ∀ n ∈ S, MemLp (f n) 2 μ)
    (χ₀ : DirichletCharacter ℂ q) :
    let D := ∑ n ∈ S, ∫ y, ‖f n y‖ ^ 2 ∂μ
    let E := fun χ : DirichletCharacter ℂ q ↦ ∫ y, ‖dirichletThetaRow χ S (fun n ↦ f n y)‖ ^ 2 ∂μ
    ∑ χ ∈ Finset.univ.erase χ₀, (E χ - D) = D - E χ₀ := by
  classical
  intro D E
  have : NeZero q := ⟨hp.ne_zero⟩
  have h := Finset.sum_erase_add (s := Finset.univ) (f := fun χ ↦ E χ - D) (Finset.mem_univ χ₀)
  have ht : (∑ χ : DirichletCharacter ℂ q, E χ) = (q.totient : ℝ) * D := dirichletThetaRow_integral_sum_sq_of_prime hp S hS hf
  have he : (∑ χ : DirichletCharacter ℂ q, (E χ - D)) = 0 := by
    rw [Finset.sum_sub_distrib, ht, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, sub_self]
  rw [he] at h
  linarith

/-- A normalized conjugate character selects one prescribed character and annihilates all the others. -/
theorem dirichletThetaRow_select_character {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q) :
    ∑ a : ZMod q, χ a * (conj (χ₀ a) / q.totient) = if χ = χ₀ then 1 else 0 := by
  classical
  have hrewrite (a : ZMod q) : χ a * (conj (χ₀ a) / q.totient) = (χ * χ₀⁻¹) a / q.totient := by
    rw [← mul_div_assoc]
    change χ a * star (χ₀ a) / _ = _
    rw [MulChar.star_apply', MulChar.mul_apply]
  simp_rw [hrewrite]
  rw [← Finset.sum_div]
  by_cases h : χ = χ₀
  · subst χ
    rw [mul_inv_cancel, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
    simp [(Nat.totient_pos.mpr (NeZero.pos q)).ne']
  · have hn : χ * χ₀⁻¹ ≠ 1 := fun e ↦ h (by simpa using congrArg (· * χ₀) e)
    rw [MulChar.sum_eq_zero_of_ne_one hn, zero_div, ite_eq_right h]

/-- For this normalized choice the selected character has squared response one and the unit-residue diagonal is the reciprocal totient. -/
theorem dirichletThetaRow_select_character_diagonal {q : ℕ} [NeZero q] (χ₀ : DirichletCharacter ℂ q) :
    (∑ a : ZMod q, if IsUnit a then ‖conj (χ₀ a) / q.totient‖ ^ 2 else 0) =
      (q.totient : ℝ)⁻¹ := by
  classical
  have h := thetaAverage_residue_parseval (q := q) (fun a ↦ conj (χ₀ a) / q.totient)
  simp only [dirichletThetaRow_select_character] at h
  have hsum : (∑ χ : DirichletCharacter ℂ q, ‖(if χ = χ₀ then (1 : ℂ) else 0)‖ ^ 2) = 1 := by
    rw [Finset.sum_eq_single χ₀] <;> simp_all
  rw [hsum] at h
  have hq : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  apply mul_left_cancel₀ hq
  simpa [hq] using h.symm

/-- The additive Fourier samples of the same finite coefficients at a residue of the modulus. -/
@[expose] def dirichletThetaAdditiveRow {q : ℕ} [NeZero q] (a : ZMod q) (S : Finset ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ n ∈ S, ZMod.stdAddChar ((n : ZMod q) * a) * f n

private theorem thetaAverage_gauss_row {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (S : Finset ℕ) (f : ℕ → ℂ) :
    ∑ a : ZMod q, χ a * dirichletThetaAdditiveRow a S f = gaussSum χ ZMod.stdAddChar * dirichletThetaRow χ⁻¹ S f := by
  unfold dirichletThetaAdditiveRow dirichletThetaRow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  calc
    _ = gaussSum χ (ZMod.stdAddChar.mulShift (n : ZMod q)) * f n := by
      unfold gaussSum
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      simp only [AddChar.mulShift_apply]
      ring
    _ = _ := by rw [gaussSum_mulShift_of_isPrimitive _ hχ]; ring

/-- For primitive multiplicative twists, Gauss sums bound their squared responses by the
additive samples at the reduced residues. This permits summing over different conductors. -/
theorem dirichletThetaRow_primitive_additive_bound {q : ℕ} [NeZero q] (S : Finset ℕ) (f : ℕ → ℂ)
    (P : Finset (DirichletCharacter ℂ q)) (hP : ∀ χ ∈ P, χ.IsPrimitive) :
    (q : ℝ) * ∑ χ ∈ P, ‖dirichletThetaRow χ S f‖ ^ 2 ≤
      q.totient * ∑ a : ZMod q, if IsUnit a then ‖dirichletThetaAdditiveRow a S f‖ ^ 2 else 0 := by
  let E (χ : DirichletCharacter ℂ q) := ‖∑ a : ZMod q, χ a * dirichletThetaAdditiveRow a S f‖ ^ 2
  have h (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
      (q : ℝ) * ‖dirichletThetaRow χ S f‖ ^ 2 = E χ⁻¹ := by
    dsimp only [E]
    rw [thetaAverage_gauss_row _ hχ.inv, inv_inv, norm_mul, mul_pow, χ⁻¹.norm_gaussSum_stdAddChar hχ.inv,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    _ = ∑ χ ∈ P, E χ⁻¹ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun χ hχ ↦ h χ (hP χ hχ))
    _ ≤ ∑ χ : DirichletCharacter ℂ q, E χ⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun χ _ _ ↦ sq_nonneg _)
    _ = ∑ χ : DirichletCharacter ℂ q, E χ := by
      exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun _ ↦ rfl)
    _ = _ := thetaAverage_residue_parseval _

/-- The constant coefficients 1/N on 1 through N give response one for the fixed trivial character
of modulus one, while the exact mean squared response at every prime modulus above N is 1/N. -/
theorem dirichletThetaRow_constant_counterexample {N q : ℕ} (hN : 0 < N) (hq : q.Prime) (hNq : N < q) :
    dirichletThetaRow (1 : DirichletCharacter ℂ 1) (Finset.Icc 1 N) (fun _ ↦ (N : ℂ)⁻¹) = 1 ∧
      (∑ χ : DirichletCharacter ℂ q,
        ‖dirichletThetaRow χ (Finset.Icc 1 N) (fun _ ↦ (N : ℂ)⁻¹)‖ ^ 2) / q.totient =
        (N : ℝ)⁻¹ := by
  have hcard : (Finset.Icc 1 N).card = N := by simp
  constructor
  · have h (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
      rw [Subsingleton.elim (n : ZMod 1) 1, map_one]
    simp only [dirichletThetaRow, h, one_mul, Finset.sum_const, hcard, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast hN.ne')
  · have hS (n : ℕ) (hn : n ∈ Finset.Icc 1 N) : 0 < n ∧ n < q :=
      ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans_lt hNq⟩
    rw [dirichletThetaRow_sum_sq_of_prime hq _ _ hS]
    have hq' : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq.pos).ne'
    have hn' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [Finset.sum_const, hcard, nsmul_eq_mul, norm_inv, Complex.norm_natCast]
    field_simp

end RiemannMasullo
