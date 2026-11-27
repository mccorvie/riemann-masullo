module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.PrimitiveFourier
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-! # The full prime sum on a rational angular residue

For a fixed compactly supported radial test, averaging the primitive prime sums over
one angular residue recovers a single von Mangoldt atom as the modulus grows.
-/

@[expose] public noncomputable section

open Filter Function Set
open scoped ArithmeticFunction BigOperators Topology

namespace RiemannMasullo.RationalConductor

/-- The von Mangoldt mass of the test at the integer norm `n`. -/
def primeSample (H : ℝ → ℂ) (n : ℕ) : ℂ := (Λ n : ℂ) * H (Real.log n)

/-- At every positive prime power the coefficient is the logarithm of its prime base. -/
theorem primeSample_prime_pow (H : ℝ → ℂ) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    primeSample H (p ^ k) = (Real.log p : ℂ) * H (Real.log ((p ^ k : ℕ) : ℝ)) := by
  simp only [primeSample, ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- Integers outside the prime powers carry zero mass. -/
theorem primeSample_eq_zero (H : ℝ → ℂ) {n : ℕ} (hn : ¬ IsPrimePow n) : primeSample H n = 0 := by
  simp [primeSample, ArithmeticFunction.vonMangoldt_apply, hn]

/-- A fixed compact radial profile sees only finitely many prime powers. -/
theorem finite_primeSample {H : ℝ → ℂ} (hH : HasCompactSupport H) :
    (support (primeSample H)).Finite := by
  obtain ⟨B, hB⟩ := hH.bddAbove
  refine (finite_le_nat ⌈Real.exp B⌉₊).subset ?_
  intro n hn
  by_cases hn₀ : n = 0
  · simp [hn₀]
  have hHn : H (Real.log n) ≠ 0 := fun h ↦ hn (by simp [primeSample, h])
  have hlog : Real.log n ≤ B := hB (subset_tsupport H hHn)
  have hn' : (n : ℝ) ≤ Real.exp B := by
    rw [← Real.exp_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn₀))]
    exact Real.exp_le_exp.mpr hlog
  exact_mod_cast hn'.trans (Nat.le_ceil (Real.exp B))

/-- The literal prime side of the explicit formula for the primitive character
inducing a character of level `q`. -/
def primitivePrimeSeries {q : ℕ} (H : ℝ → ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑' n : ℕ, primeSample H n * χ.primitiveCharacter n

/-- Averaging the genuine primitive prime series applies the exact ramified weight
to each prime power. Compact support makes the exchange a finite sum. -/
theorem cylinderAverage_primitivePrimeSeries {q : ℕ} [NeZero q] (r : (ZMod q)ˣ)
    {H : ℝ → ℂ} (hH : HasCompactSupport H) :
    cylinderAverage q r (primitivePrimeSeries H) =
      ∑' n : ℕ, primeSample H n * primeWeight q r n := by
  classical
  let S := (finite_primeSample hH).toFinset
  have hzero (n : ℕ) (hn : n ∉ S) : primeSample H n = 0 := by
    simpa [S, Function.mem_support] using hn
  have hf : (primitivePrimeSeries H : DirichletCharacter ℂ q → ℂ) =
      ∑ n ∈ S, (primeSample H n) • (fun χ ↦ χ.primitiveCharacter n) := by
    funext χ
    simp only [primitivePrimeSeries, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact tsum_eq_sum (fun n hn ↦ by rw [hzero n hn, zero_mul])
  rw [hf, map_sum]
  simp only [map_smul, smul_eq_mul]
  change (∑ n ∈ S, primeSample H n * primeWeight q r n) = _
  exact (tsum_eq_sum (fun n hn ↦ by rw [hzero n hn, zero_mul])).symm

/-- The finite-conductor error in the full prime side is `O(1/q)`, through every
modulus coprime to the fixed integer `b`. The same calculation includes prime bases
that divide `q`. -/
theorem primeSeries_error_le {H : ℝ → ℂ} (hH : HasCompactSupport H) (b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (hb : b.Coprime q),
      ‖cylinderAverage q (ZMod.unitOfCoprime b hb) (primitivePrimeSeries H) - primeSample H b‖ ≤ C / q := by
  classical
  let S := insert b (finite_primeSample hH).toFinset
  let d (n : ℕ) : ℝ := 2 * ((n : ℤ) - (b : ℤ)).natAbs
  have hd (n : ℕ) : 0 ≤ d n := by dsimp [d]; positivity
  refine ⟨∑ n ∈ S, ‖primeSample H n‖ * d n,
    Finset.sum_nonneg (fun n _ ↦ mul_nonneg (norm_nonneg _) (hd n)), ?_⟩
  intro q _ hb
  let r := ZMod.unitOfCoprime b hb
  have hzero (n : ℕ) (hn : n ∉ S) : primeSample H n = 0 := by
    have hns : n ∉ (finite_primeSample hH).toFinset := fun h ↦ hn (Finset.mem_insert_of_mem h)
    simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hns
  have hsingle : (∑ n ∈ S, if n = b then primeSample H n else 0) = primeSample H b := by simp [S]
  have hrow (n : ℕ) : ‖primeSample H n * primeWeight q r n -
      (if n = b then primeSample H n else 0)‖ ≤ ‖primeSample H n‖ * d n / q := by
    by_cases h : n = b
    · subst n
      simp [r, primeWeight_of_coprime hb, d]
    · rw [ite_eq_right h, sub_zero, norm_mul, mul_div_assoc]
      by_cases hn : IsPrimePow n
      · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
        exact mul_le_mul_of_nonneg_left (norm_primeWeight_le_of_ne hp hk.ne' hb h) (norm_nonneg _)
      · have hΛ : Λ n = 0 := not_not.mp (fun he ↦ hn (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp he))
        simp [primeSample, hΛ]
  rw [cylinderAverage_primitivePrimeSeries _ hH,
    tsum_eq_sum (s := S) (fun n hn ↦ by rw [hzero n hn, zero_mul]), ← hsingle, ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun n _ ↦ hrow n)).trans_eq (Finset.sum_div _ _ _).symm)


/-- The prime and archimedean side of the positive-log primitive explicit formula
for a test with its two pole moments killed. `A` and `B` are the even and odd
archimedean integrals, respectively. -/
def primeAndArchRow {q : ℕ} (H : ℝ → ℂ) (A B : ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  -primitivePrimeSeries H χ - (if χ (-1) = 1 then A else B)

/-- The finite-level prime and archimedean factors jointly, including coincident
angular signs at moduli one and two. -/
theorem cylinderAverage_primeAndArchRow {q : ℕ} [NeZero q] (r : (ZMod q)ˣ)
    {H : ℝ → ℂ} (hH : HasCompactSupport H) (A B : ℂ) :
    cylinderAverage q r (primeAndArchRow H A B) =
      -(∑' n : ℕ, primeSample H n * primeWeight q r n) -
        ((if (r : ZMod q) = 1 then (A + B) / 2 else 0) +
        (if (r : ZMod q) = -1 then (A - B) / 2 else 0)) := by
  change cylinderAverage q r (-primitivePrimeSeries H - (fun χ ↦ if χ (-1) = 1 then A else B)) = _
  rw [map_sub, map_neg, cylinderAverage_primitivePrimeSeries _ hH, cylinderAverage_parity]

private theorem residue_ne_signs {q b : ℕ} (hb : 2 ≤ b) (hq : b + 1 < q) :
    (b : ZMod q) ≠ 1 ∧ (b : ZMod q) ≠ -1 := by
  constructor
  · intro h
    have he := (ZMod.natCast_eq_natCast_iff' b 1 q).mp (by simpa using h)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
    omega
  · intro h
    have he : ((b + 1 : ℕ) : ZMod q) = 0 := by push_cast; rw [h]; ring
    exact (Nat.not_le.mpr hq) (Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff _ _).mp he))

/-- A fixed angular cylinder around `b ≥ 2` isolates the `b`th von Mangoldt atom
with an explicit `O(1/q)` conductor error on the full primitive prime side. The
parity terms cancel exactly as soon as `q > b+1`. -/
theorem norm_primeAndArchRow_add_le {H : ℝ → ℂ} (hH : HasCompactSupport H)
    {b : ℕ} (hb : 2 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (hbq : b.Coprime q), b + 1 < q →
      ∀ A B : ℂ, ‖cylinderAverage q (ZMod.unitOfCoprime b hbq) (primeAndArchRow H A B) +
        primeSample H b‖ ≤ C / q := by
  obtain ⟨C, hC, hbound⟩ := primeSeries_error_le hH b
  refine ⟨C, hC, fun q _ hbq hq A B ↦ ?_⟩
  have hs := residue_ne_signs hb hq
  rw [cylinderAverage_primeAndArchRow _ hH, ZMod.coe_unitOfCoprime, ite_eq_right hs.1,
    ite_eq_right hs.2, add_zero, sub_zero, ← cylinderAverage_primitivePrimeSeries _ hH,
    add_comm, ← sub_eq_add_neg, norm_sub_rev]
  exact hbound q hbq

/-- For a compact radial profile and any sequence of growing moduli coprime to `b`,
the full primitive prime formula tends to the negative von Mangoldt atom. -/
theorem primeAndArchRow_tendsto {ι : Type*} {l : Filter ι} {q : ι → ℕ} [∀ i, NeZero (q i)]
    (hq : Tendsto q l atTop) {b : ℕ} (hb : 2 ≤ b) (hbq : ∀ i, b.Coprime (q i))
    {H : ℝ → ℂ} (hH : HasCompactSupport H) (A B : ℂ) :
    Tendsto (fun i ↦ cylinderAverage (q i) (ZMod.unitOfCoprime b (hbq i))
      (primeAndArchRow H A B)) l (𝓝 (-primeSample H b)) := by
  obtain ⟨C, hC, hbound⟩ := norm_primeAndArchRow_add_le hH hb
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun i ↦ norm_nonneg _)
  · filter_upwards [hq.eventually (eventually_gt_atTop (b + 1))] with i hi
    simpa only [sub_neg_eq_add] using hbound (q i) (hbq i) hi A B
  · have hq' : Tendsto (fun i ↦ (q i : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hq
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hq').const_mul C

/-- Shifting the Mellin center by `a` multiplies the individual norm `n` by
`n^(-a)` in the full atom. In particular the centered exponent is `-1/2`. -/
theorem primeSample_shift (H : ℝ → ℂ) (a : ℝ) {n : ℕ} (hn : 0 < n) :
    primeSample (fun x ↦ (Real.exp (-a * x) : ℂ) * H x) n =
      (((n : ℝ) ^ (-a) : ℝ) : ℂ) * primeSample H n := by
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hn), mul_comm (Real.log _) (-a)]
  simp only [primeSample]
  ring

end RiemannMasullo.RationalConductor
