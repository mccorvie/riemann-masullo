module

public import RiemannMasullo.Ch13_ZerosHecke.QuadraticPrimeCellMoments
public import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.GCD.BigOperators

/-! # Opposite quadratic signs on Hecke prime and prime-power sums -/

@[expose] public noncomputable section

open Finset NumberField

namespace RiemannMasullo

/-- Twice the real prime Riesz sum over the negative quadratic sign of the multiplier. -/
def quadraticParityPrimeRieszSum {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (T : ℕ) (x : ℝ) (m : ℕ) : ℝ :=
  2 * ∑ p ∈ Nat.primesLE T with (jacobiSym m p : ℝ) = -1,
    (heckeLogDerivCoefficient (ideleClassNormTwist χ 0) p).re * max (x-p) 0

/-- Twice the complete real Hecke Riesz sum over all integer norms with negative
Jacobi sign of the multiplier. -/
def quadraticParityPrimePowerRieszSum {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (T : ℕ) (x : ℝ) (m : ℕ) : ℝ :=
  2 * ∑ n ∈ Ioc 0 T with (jacobiSym m n : ℝ) = -1,
    (heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n).re * max (x-n) 0

/-- The negative quadratic parity excludes every square norm. -/
theorem quadraticParity_square_excluded (m n : ℕ) : (jacobiSym m (n^2) : ℝ) ≠ -1 := by
  rw [jacobiSym.pow_right, Int.cast_pow]
  nlinarith [sq_nonneg (jacobiSym m n : ℝ)]

/-- On prime norms coprime to the multiplier the discrepancy is exactly
the negative of the single twist by the whole multiplier. -/
theorem quadraticParityPrimeRieszSum_sub_unrestricted {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (T : ℕ) (x : ℝ) (m : ℕ)
    (hcoprime : ∀ p ∈ Nat.primesLE T, Nat.Coprime m p) :
    quadraticParityPrimeRieszSum χ T x m - degreeOnePrimeRieszSumWith χ T x 1 =
      -degreeOnePrimeRieszSumWith χ T x (fun p ↦ (jacobiSym m p : ℝ)) := by
  simp only [quadraticParityPrimeRieszSum, degreeOnePrimeRieszSumWith, Pi.one_apply, mul_one,
    sum_filter, mul_sum, ← sum_sub_distrib, ← sum_neg_distrib]
  apply sum_congr rfl
  intro p hp
  have hg : (m : ℤ).gcd p = 1 := by simpa [Int.gcd_eq_natAbs] using hcoprime p hp
  rcases jacobiSym.eq_one_or_neg_one hg with h | h <;> norm_num [h]
  ring

/-- The negative sign of qd is the disjoint union of the two opposite-sign cells.
The equality includes zero symbols and the prime two. -/
theorem quadraticParityPrimePowerRieszSum_mul {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (T : ℕ) (x : ℝ) (q d : ℕ) :
    quadraticParityPrimePowerRieszSum χ T x (q*d) =
      (quadraticPrimePowerCellRieszSum χ T x q d (-1) 1 +
        quadraticPrimePowerCellRieszSum χ T x q d 1 (-1)) / 2 := by
  let b (n : ℕ) := (heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n).re * max (x-n) 0
  have hsum :
      (∑ n ∈ Ioc 0 T with (jacobiSym (q*d : ℕ) n : ℝ) = -1, b n) =
      (∑ n ∈ Ioc 0 T with (jacobiSym q n : ℝ) = -1 ∧ (jacobiSym d n : ℝ) = 1, b n) +
      (∑ n ∈ Ioc 0 T with (jacobiSym q n : ℝ) = 1 ∧ (jacobiSym d n : ℝ) = -1, b n) := by
    simp only [sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    rw [Nat.cast_mul, jacobiSym.mul_left]
    rcases jacobiSym.trichotomy q n with hq | hq | hq <;>
      rcases jacobiSym.trichotomy d n with hd | hd | hd <;> norm_num [hq, hd]
  unfold quadraticParityPrimePowerRieszSum quadraticPrimePowerCellRieszSum
  change 2 * (∑ n ∈ Ioc 0 T with (jacobiSym (q*d : ℕ) n : ℝ) = -1, b n) = _
  rw [hsum]
  dsimp only [b]
  ring

/-- A dummy second multiplier 1 identifies the negative prime subseries with
half of the fourfold (-1,+1) cell. -/
theorem quadraticParityPrimeRieszSum_eq_half_cell {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (T : ℕ) (x : ℝ) (m : ℕ) :
    quadraticParityPrimeRieszSum χ T x m = quadraticPrimeCellRieszSum χ T x m 1 (-1) 1 / 2 := by
  simp only [quadraticParityPrimeRieszSum, quadraticPrimeCellRieszSum, Nat.cast_one,
    jacobiSym.one_left, Int.cast_one, and_true]
  ring

/-- The same exact half-cell identity holds on all integer norms. -/
theorem quadraticParityPrimePowerRieszSum_eq_half_cell {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (T : ℕ) (x : ℝ) (m : ℕ) :
    quadraticParityPrimePowerRieszSum χ T x m =
      quadraticPrimePowerCellRieszSum χ T x m 1 (-1) 1 / 2 := by
  simp only [quadraticParityPrimePowerRieszSum, quadraticPrimePowerCellRieszSum, Nat.cast_one,
    jacobiSym.one_left, Int.cast_one, and_true]
  ring

/-- The cost of completing one negative-parity prime sum has coefficient
four times the field degree and is uniform in the squarefree product. -/
theorem quadraticParityPrimePower_sub_prime_le {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) {T : ℕ} (hT : 1 ≤ T)
    {x : ℝ} (hx : x ≤ T) (m : ℕ) :
    |quadraticParityPrimePowerRieszSum χ T x m - quadraticParityPrimeRieszSum χ T x m| ≤
      4*(Module.finrank ℚ F : ℝ)*(Real.log 4+4)*T*(T : ℝ)^(3 : ℝ)⁻¹ := by
  have h := quadraticPrimePowerCell_sub_prime_le χ hT hx m 1 (e := -1) (f := 1) (Or.inl rfl)
  rw [quadraticParityPrimePowerRieszSum_eq_half_cell, quadraticParityPrimeRieszSum_eq_half_cell,
    ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith only [h]

/-- The cumulative completion cost is half the fourfold negative-cell cost.
Applying that comparison with twice the physical center preserves the positive part. -/
theorem quadraticParityPrimePower_fourthPower_deficit_sub_prime
    {F : Type*} [Field F] [NumberField F] (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    {J : ℕ} (hJ : 1 ≤ J) (m : ℕ) (c : ℕ → ℝ) :
    |(∑ j ∈ Ioc 0 J, max (c j - quadraticParityPrimePowerRieszSum χ (J^4) ((j : ℝ)^4) m) 0) -
      ∑ j ∈ Ioc 0 J, max (c j - quadraticParityPrimeRieszSum χ (J^4) ((j : ℝ)^4) m) 0| ≤
      4*(Module.finrank ℚ F : ℝ)*(Real.log 4+4)*(J : ℝ)^(19/3 : ℝ) := by
  let A (j : ℕ) := quadraticPrimePowerCellRieszSum χ (J^4) ((j : ℝ)^4) m 1 (-1) 1
  let P (j : ℕ) := quadraticPrimeCellRieszSum χ (J^4) ((j : ℝ)^4) m 1 (-1) 1
  have hscale (v : ℕ → ℝ) :
      (∑ j ∈ Ioc 0 J, max (2*c j - v j) 0) = 2 * ∑ j ∈ Ioc 0 J, max (c j - v j/2) 0 := by
    rw [mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), mul_zero]
    congr 1
    ring
  have h := quadraticPrimePowerCell_fourthPower_deficit_sub_prime χ hJ m 1 (fun j ↦ 2*c j)
    (fun _ ↦ -1) (fun _ ↦ 1) (fun _ _ ↦ Or.inl rfl)
  change |(∑ j ∈ Ioc 0 J, max (2*c j - A j) 0) - ∑ j ∈ Ioc 0 J, max (2*c j - P j) 0| ≤ _ at h
  rw [hscale A, hscale P, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  simp_rw [quadraticParityPrimePowerRieszSum_eq_half_cell, quadraticParityPrimeRieszSum_eq_half_cell]
  change |(∑ j ∈ Ioc 0 J, max (c j - A j/2) 0) - ∑ j ∈ Ioc 0 J, max (c j - P j/2) 0| ≤ _
  linarith only [h]

/-- A normalized cumulative moment of the actual twist by the product of each
unordered set in W. Each product contributes one observation at a sample. -/
def QuadraticParityProductFourthPowerMoment {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (J k : ℕ)
    (W : Finset (Finset ℕ)) (L : ℝ) : Prop :=
  ∑ s ∈ W, (∑ j ∈ Ioc 0 J, |degreeOnePrimeRieszSumWith χ (J^4) ((j : ℝ)^4)
    (fun p ↦ (jacobiSym (s.prod id : ℕ) p : ℝ))|)^k ≤ (W.card : ℝ) * L^k

/-- A uniform single-sample moment of radius R gives cumulative radius JR on
any finite family of products. -/
theorem quadraticParityProductFourthPowerMoment_of_samples
    {F : Type*} [Field F] [NumberField F] (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (J k : ℕ) (W : Finset (Finset ℕ)) (R : ℝ) (hk : 0 < k)
    (hmoment : ∀ j ∈ Ioc 0 J, ∑ s ∈ W, |degreeOnePrimeRieszSumWith χ (J^4) ((j : ℝ)^4)
      (fun p ↦ (jacobiSym (s.prod id : ℕ) p : ℝ))|^k ≤ (W.card : ℝ) * R^k) :
    QuadraticParityProductFourthPowerMoment χ J k W ((J : ℝ) * R) := by
  let v (j : ℕ) (s : Finset ℕ) := |degreeOnePrimeRieszSumWith χ (J^4) ((j : ℝ)^4)
    (fun p ↦ (jacobiSym (s.prod id : ℕ) p : ℝ))|
  have h := quadraticPrime_uniform_sum_moment W (Ioc 0 J) hk v R (fun _ _ _ _ ↦ abs_nonneg _) hmoment
  unfold QuadraticParityProductFourthPowerMoment
  simpa only [Nat.card_Ioc, Nat.sub_zero, v] using h

private theorem quadraticParity_complete_transfer {ι F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) {J k : ℕ} (hJ : 1 ≤ J) (hk : 0 < k)
    (Ω G : Finset ι) (hΩ : Ω.Nonempty) (hG : G ⊆ Ω) (m : ι → ℕ) (c : ℕ → ℝ)
    {L δ H : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) (hdensity : δ * (Ω.card : ℝ) ≤ (G.card : ℝ))
    (hmoment : ∑ w ∈ Ω, (∑ j ∈ Ioc 0 J, |degreeOnePrimeRieszSumWith χ (J^4) ((j : ℝ)^4)
      (fun p ↦ (jacobiSym (m w) p : ℝ))|)^k ≤ (Ω.card : ℝ) * L^k)
    (hcoprime : ∀ w ∈ G, ∀ p ∈ Nat.primesLE (J^4), Nat.Coprime (m w) p)
    (hcomplete : ∀ w ∈ G, ∑ j ∈ Ioc 0 J, max (c j -
      quadraticParityPrimePowerRieszSum χ (J^4) ((j : ℝ)^4) (m w)) 0 ≤ H) :
    ∑ j ∈ Ioc 0 J, max (c j - degreeOnePrimeRieszSumWith χ (J^4) ((j : ℝ)^4) 1) 0 ≤
      H + 4*(Module.finrank ℚ F : ℝ)*(Real.log 4+4)*(J : ℝ)^(19/3 : ℝ) +
        L * δ ^ (-(k : ℝ)⁻¹) := by
  let I := Ioc 0 J
  let a (w : ι) (j : ℕ) := quadraticParityPrimeRieszSum χ (J^4) ((j : ℝ)^4) (m w)
  let b (j : ℕ) := degreeOnePrimeRieszSumWith χ (J^4) ((j : ℝ)^4) 1
  let v (w : ι) := ∑ j ∈ I, |degreeOnePrimeRieszSumWith χ (J^4) ((j : ℝ)^4)
    (fun p ↦ (jacobiSym (m w) p : ℝ))|
  let D := ∑ j ∈ I, max (c j - b j) 0
  let B := 4*(Module.finrank ℚ F : ℝ)*(Real.log 4+4)*(J : ℝ)^(19/3 : ℝ)
  have hpoint (w : ι) (hw : w ∈ G) : D - H - B ≤ v w := by
    have hdiff := quadraticParityPrimePower_fourthPower_deficit_sub_prime χ hJ (m w) c
    have hsmall := hcomplete w hw
    change |(_ : ℝ) - ∑ j ∈ I, max (c j - a w j) 0| ≤ B at hdiff
    have hprime := quadraticPrime_deficit_contraction I c (a w) b
    have heq : (∑ j ∈ I, |a w j - b j|) = v w := by
      refine sum_congr rfl fun j _ ↦ ?_
      rw [show a w j - b j = _ from quadraticParityPrimeRieszSum_sub_unrestricted χ
        (J^4) ((j : ℝ)^4) (m w) (hcoprime w hw), abs_neg]
    rw [heq] at hprime
    change |(∑ j ∈ I, max (c j - a w j) 0) - D| ≤ v w at hprime
    linarith only [(abs_le.mp hdiff).1, (abs_le.mp hprime).1, hsmall]
  have h := quadraticPrime_density_loss hΩ hG hk hδ hL hdensity
    (v := v) (fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _) hmoment hpoint
  change D ≤ H + B + _
  linarith only [h]

/-- On any nonempty finite family of unordered products, small complete negative-parity
deficit on a fraction δ forces a bound on the unrestricted prime deficit. Coprimality
with the sampled primes is needed only on the selected family. -/
theorem QuadraticParityProductFourthPowerMoment.complete_deficit_transfer
    {F : Type*} [Field F] [NumberField F] {χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)}
    {J k : ℕ} {W : Finset (Finset ℕ)} {L : ℝ}
    (hmoment : QuadraticParityProductFourthPowerMoment χ J k W L) (hJ : 1 ≤ J) (hk : 0 < k)
    (hW : W.Nonempty) (hL : 0 ≤ L) (c : ℕ → ℝ) (G : Finset (Finset ℕ)) (hG : G ⊆ W)
    {δ H : ℝ} (hδ : 0 < δ) (hdensity : δ * (W.card : ℝ) ≤ (G.card : ℝ))
    (hcoprime : ∀ s ∈ G, ∀ p ∈ Nat.primesLE (J^4), Nat.Coprime (s.prod id) p)
    (hcomplete : ∀ s ∈ G, ∑ j ∈ Ioc 0 J, max (c j -
      quadraticParityPrimePowerRieszSum χ (J^4) ((j : ℝ)^4) (s.prod id)) 0 ≤ H) :
    ∑ j ∈ Ioc 0 J, max (c j - degreeOnePrimeRieszSumWith χ (J^4) ((j : ℝ)^4) 1) 0 ≤
      H + 4*(Module.finrank ℚ F : ℝ)*(Real.log 4+4)*(J : ℝ)^(19/3 : ℝ) +
        L * δ ^ (-(k : ℝ)⁻¹) :=
  quadraticParity_complete_transfer χ hJ hk W G hW hG (fun s ↦ s.prod id) c
    hL hδ hdensity hmoment hcoprime hcomplete

/-- The same transfer on unordered h-element sets of auxiliaries uses the true
population cardinality and any selected subfamily. -/
theorem QuadraticParityProductFourthPowerMoment.powersetCard_complete_deficit_transfer
    {F : Type*} [Field F] [NumberField F] {χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)}
    {J k h : ℕ} {U : Finset ℕ} {L : ℝ}
    (hmoment : QuadraticParityProductFourthPowerMoment χ J k (U.powersetCard h) L)
    (hJ : 1 ≤ J) (hk : 0 < k) (hsize : h ≤ U.card) (hL : 0 ≤ L)
    (c : ℕ → ℝ) (G : Finset (Finset ℕ)) (hG : G ⊆ U.powersetCard h)
    {δ H : ℝ} (hδ : 0 < δ) (hdensity : δ * ((U.powersetCard h).card : ℝ) ≤ (G.card : ℝ))
    (hcoprime : ∀ q ∈ U, ∀ p ∈ Nat.primesLE (J^4), Nat.Coprime q p)
    (hcomplete : ∀ s ∈ G, ∑ j ∈ Ioc 0 J, max (c j -
      quadraticParityPrimePowerRieszSum χ (J^4) ((j : ℝ)^4) (s.prod id)) 0 ≤ H) :
    ∑ j ∈ Ioc 0 J, max (c j - degreeOnePrimeRieszSumWith χ (J^4) ((j : ℝ)^4) 1) 0 ≤
      H + 4*(Module.finrank ℚ F : ℝ)*(Real.log 4+4)*(J : ℝ)^(19/3 : ℝ) +
        L * δ ^ (-(k : ℝ)⁻¹) := by
  apply hmoment.complete_deficit_transfer hJ hk (powersetCard_nonempty.mpr hsize)
    hL c G hG hδ hdensity ?_ hcomplete
  intro s hs p hp
  exact Nat.coprime_prod_left_iff.mpr (fun q hq ↦ hcoprime q ((mem_powersetCard.mp (hG hs)).1 hq) p hp)

/-- On all ordered pairs of distinct auxiliaries, every unordered two-set occurs
exactly twice. -/
private theorem quadraticParity_sum_offDiag (U : Finset ℕ) (f : Finset ℕ → ℝ) :
    ∑ w ∈ U.offDiag, f {w.1, w.2} = 2 * ∑ s ∈ U.powersetCard 2, f s := by
  let pair (w : ℕ × ℕ) : Finset ℕ := {w.1, w.2}
  have hmap (w : ℕ × ℕ) (hw : w ∈ U.offDiag) : pair w ∈ U.powersetCard 2 := by
    obtain ⟨hq, hd, hne⟩ := mem_offDiag.mp hw
    exact mem_powersetCard.mpr ⟨insert_subset hq (singleton_subset_iff.mpr hd), card_pair hne⟩
  have hfiber (s : Finset ℕ) (hs : s ∈ U.powersetCard 2) :
      (U.offDiag.filter (fun w ↦ pair w = s)).card = 2 := by
    obtain ⟨q, d, hqd, rfl⟩ := card_eq_two.mp (mem_powersetCard.mp hs).2
    have hq : q ∈ U := (mem_powersetCard.mp hs).1 (by simp)
    have hd : d ∈ U := (mem_powersetCard.mp hs).1 (by simp)
    have hpair : U.offDiag.filter (fun w ↦ pair w = {q,d}) = {(q,d), (d,q)} := by
      ext w
      rw [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨_, hset⟩
        have hsets : ({w.1,w.2} : Set ℕ) = {q,d} := by
          simpa only [pair, coe_insert, coe_singleton] using
            congrArg (fun t : Finset ℕ ↦ (t : Set ℕ)) hset
        rcases Set.pair_eq_pair_iff.mp hsets with h | h
        · exact Or.inl (Prod.ext h.1 h.2)
        · exact Or.inr (Prod.ext h.1 h.2)
      · rintro (rfl | rfl)
        · exact ⟨mem_offDiag.mpr ⟨hq,hd,hqd⟩, rfl⟩
        · exact ⟨mem_offDiag.mpr ⟨hd,hq,hqd.symm⟩, pair_comm ..⟩
    rw [hpair, card_pair (fun h ↦ hqd (congrArg Prod.fst h))]
  calc _ = ∑ s ∈ U.powersetCard 2, ∑ _w ∈ U.offDiag.filter (fun w ↦ pair w = s), f s :=
         (sum_fiberwise_of_maps_to' hmap f).symm
       _ = _ := by
         rw [mul_sum]
         apply sum_congr rfl
         intro s hs
         simp only [sum_const, nsmul_eq_mul, hfiber s hs, Nat.cast_ofNat]

/-- The complete deficit on any selected collection of ordered distinct auxiliary
pairs transfers at its ordered density. The moment comes from unordered products.
The selected set need not be closed under swapping its two coordinates. -/
theorem QuadraticParityProductFourthPowerMoment.ordered_pair_complete_deficit_transfer
    {F : Type*} [Field F] [NumberField F] {χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)}
    {J k : ℕ} {U : Finset ℕ} {L : ℝ}
    (hmoment : QuadraticParityProductFourthPowerMoment χ J k (U.powersetCard 2) L)
    (hJ : 1 ≤ J) (hk : 0 < k) (hsize : 2 ≤ U.card) (hL : 0 ≤ L)
    (c : ℕ → ℝ) (G : Finset (ℕ × ℕ)) (hG : G ⊆ U.offDiag)
    {δ H : ℝ} (hδ : 0 < δ) (hdensity : δ * (U.offDiag.card : ℝ) ≤ (G.card : ℝ))
    (hcoprime : ∀ q ∈ U, ∀ p ∈ Nat.primesLE (J^4), Nat.Coprime q p)
    (hcomplete : ∀ w ∈ G, ∑ j ∈ Ioc 0 J, max (c j -
      quadraticParityPrimePowerRieszSum χ (J^4) ((j : ℝ)^4) (w.1 * w.2)) 0 ≤ H) :
    ∑ j ∈ Ioc 0 J, max (c j - degreeOnePrimeRieszSumWith χ (J^4) ((j : ℝ)^4) 1) 0 ≤
      H + 4*(Module.finrank ℚ F : ℝ)*(Real.log 4+4)*(J : ℝ)^(19/3 : ℝ) +
        L * δ ^ (-(k : ℝ)⁻¹) := by
  let E (m : ℕ) := (∑ j ∈ Ioc 0 J, |degreeOnePrimeRieszSumWith χ (J^4) ((j : ℝ)^4)
    (fun p ↦ (jacobiSym m p : ℝ))|)^k
  have hcard : (U.offDiag.card : ℝ) = 2 * ((U.powersetCard 2).card : ℝ) := by
    simpa only [sum_const, nsmul_eq_mul, mul_one] using quadraticParity_sum_offDiag U (fun _ ↦ (1 : ℝ))
  have hpos : 0 < ((U.powersetCard 2).card : ℝ) := by
    exact_mod_cast card_pos.mpr (powersetCard_nonempty.mpr hsize)
  have hO : U.offDiag.Nonempty := by
    apply card_pos.mp
    exact_mod_cast (show 0 < (U.offDiag.card : ℝ) by rw [hcard]; positivity)
  apply quadraticParity_complete_transfer χ hJ hk U.offDiag G hO hG (fun w ↦ w.1*w.2) c
    hL hδ hdensity ?_ ?_ hcomplete
  · change ∑ w ∈ U.offDiag, E (w.1*w.2) ≤ _
    calc _ = ∑ w ∈ U.offDiag, E (({w.1,w.2} : Finset ℕ).prod id) := by
           apply sum_congr rfl
           intro w hw
           rw [Finset.prod_pair (mem_offDiag.mp hw).2.2]
           rfl
         _ = 2 * ∑ s ∈ U.powersetCard 2, E (s.prod id) :=
           quadraticParity_sum_offDiag U (fun s ↦ E (s.prod id))
         _ ≤ _ := by
           rw [hcard, mul_assoc]
           exact mul_le_mul_of_nonneg_left hmoment (by norm_num)
  · intro w hw p hp
    obtain ⟨hq, hd, _⟩ := mem_offDiag.mp (hG hw)
    exact (hcoprime w.1 hq p hp).mul_left (hcoprime w.2 hd p hp)

end RiemannMasullo
