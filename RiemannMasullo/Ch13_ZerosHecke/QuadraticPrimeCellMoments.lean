module

public import RiemannMasullo.Ch13_ZerosHecke.QuadraticPrimeTwists
public import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.MeanInequalities

/-! # Finite moments of the discrepancies in selected quadratic cells -/

@[expose] public noncomputable section

open Finset NumberField Filter

namespace RiemannMasullo

/-- A normalized k-th absolute moment bounds any common lower bound on a positive
fraction of the population. The loss at density δ is δ^(-1/k). -/
theorem quadraticPrime_density_loss {ι : Type*} {Ω G : Finset ι}
    (hΩ : Ω.Nonempty) (hG : G ⊆ Ω) {k : ℕ} (hk : 0 < k) {δ L D : ℝ}
    (hδ : 0 < δ) (hL : 0 ≤ L) (hdensity : δ * (Ω.card : ℝ) ≤ (G.card : ℝ))
    {v : ι → ℝ} (hv : ∀ i ∈ Ω, 0 ≤ v i)
    (hm : ∑ i ∈ Ω, (v i)^k ≤ Ω.card * L^k) (hD : ∀ i ∈ G, D ≤ v i) :
    D ≤ L * δ ^ (-(k : ℝ)⁻¹) := by
  have hr : 0 ≤ L * δ ^ (-(k : ℝ)⁻¹) := mul_nonneg hL (Real.rpow_nonneg hδ.le _)
  by_cases hd : 0 ≤ D
  · have hΩpos : 0 < (Ω.card : ℝ) := by exact_mod_cast card_pos.mpr hΩ
    have hprod : δ * D^k ≤ L^k := by
      apply (mul_le_mul_iff_right₀ hΩpos).mp
      calc (Ω.card : ℝ) * (δ * D^k) = (δ * Ω.card) * D^k := by ring
           _ ≤ (G.card : ℝ) * D^k := mul_le_mul_of_nonneg_right hdensity (pow_nonneg hd _)
           _ = ∑ _i ∈ G, D^k := by simp
           _ ≤ ∑ i ∈ G, (v i)^k := sum_le_sum fun i hi ↦ pow_le_pow_left₀ hd (hD i hi) _
           _ ≤ ∑ i ∈ Ω, (v i)^k :=
             sum_le_sum_of_subset_of_nonneg hG (fun i hi _ ↦ pow_nonneg (hv i hi) _)
           _ ≤ _ := hm
    apply le_of_pow_le_pow_left₀ hk.ne' hr
    rw [mul_pow, Real.rpow_neg hδ.le, inv_pow, Real.rpow_inv_natCast_pow hδ.le hk.ne',
      ← div_eq_mul_inv, le_div_iff₀ hδ, mul_comm]
    exact hprod
  · exact (le_of_not_ge hd).trans hr

/-- Taking a cumulative positive-part deficit at a common center contracts the sum of absolute pointwise differences. -/
theorem quadraticPrime_deficit_contraction {ι : Type*} (I : Finset ι)
    (c a b : ι → ℝ) :
    |(∑ j ∈ I, max (c j - a j) 0) - ∑ j ∈ I, max (c j - b j) 0| ≤
      ∑ j ∈ I, |a j - b j| := by
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun j _ ↦ ?_)
  simpa only [sub_sub_sub_cancel_left, abs_sub_comm (b j) (a j)] using
    abs_max_sub_max_le_abs (c j - a j) (c j - b j) 0

/-- Physical cell discrepancy at j⁴ and arbitrary center, signs and chosen pairs.
A k-th moment of the cumulative absolute discrepancies gives loss δ^(-1/k)
when the prime-cell deficit is small on a fraction δ of ordered pairs. -/
theorem quadraticPrimeCell_fourthPower_deficit_moment_transfer
    {F : Type*} [Field F] [NumberField F] (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (J : ℕ) {k : ℕ} (hk : 0 < k) (Ω G : Finset (ℕ × ℕ)) (hΩ : Ω.Nonempty) (hG : G ⊆ Ω)
    (c : ℕ → ℝ) (e f : ℕ → ℕ → ℕ → ℝ)
    {H δ L : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L) (hdensity : δ * (Ω.card : ℝ) ≤ (G.card : ℝ))
    (hM : ∑ w ∈ Ω, (∑ j ∈ Ioc 0 J,
      |quadraticPrimeCellRieszSum χ (J^4) ((j:ℝ)^4) w.1 w.2 (e w.1 w.2 j) (f w.1 w.2 j) -
        degreeOnePrimeRieszSumWith χ (J^4) ((j:ℝ)^4) 1|)^k ≤ Ω.card * L^k)
    (hH : ∀ w ∈ G, ∑ j ∈ Ioc 0 J, max (c j -
      quadraticPrimeCellRieszSum χ (J^4) ((j:ℝ)^4) w.1 w.2 (e w.1 w.2 j) (f w.1 w.2 j)) 0 ≤ H) :
    ∑ j ∈ Ioc 0 J, max (c j - degreeOnePrimeRieszSumWith χ (J^4) ((j:ℝ)^4) 1) 0 ≤
      H + L * δ ^ (-(k : ℝ)⁻¹) := by
  let a (w : ℕ × ℕ) (j : ℕ) :=
    quadraticPrimeCellRieszSum χ (J^4) ((j:ℝ)^4) w.1 w.2 (e w.1 w.2 j) (f w.1 w.2 j)
  let b (j : ℕ) := degreeOnePrimeRieszSumWith χ (J^4) ((j:ℝ)^4) 1
  let A := ∑ j ∈ Ioc 0 J, max (c j - b j) 0
  let v (w : ℕ × ℕ) := ∑ j ∈ Ioc 0 J, |a w j - b j|
  have hpoint (w : ℕ × ℕ) (hw : w ∈ G) : A - H ≤ v w := by
    have hlip := quadraticPrime_deficit_contraction (Ioc 0 J) c (a w) b
    have hhw := hH w hw
    change (∑ j ∈ Ioc 0 J, max (c j - a w j) 0) ≤ H at hhw
    change |(∑ j ∈ Ioc 0 J, max (c j - a w j) 0) - A| ≤ v w at hlip
    linarith [(abs_le.mp hlip).1]
  have hh := quadraticPrime_density_loss hΩ hG hk hδ hL hdensity
    (v := v) (fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _) hM hpoint
  change A ≤ _
  linarith

/-- For arbitrary selected complete cells with a negative sign, the prime-power
correction is uniform on the selected pairs. In particular the sixth moment
costs δ^(-1/6), while the J^(19/3) completion cost has no density loss. -/
theorem quadraticPrimePowerCell_fourthPower_deficit_moment_transfer
    {F : Type*} [Field F] [NumberField F] (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    {J k : ℕ} (hJ : 1 ≤ J) (hk : 0 < k) (Ω G : Finset (ℕ × ℕ)) (hΩ : Ω.Nonempty) (hG : G ⊆ Ω)
    (c : ℕ → ℝ) (e f : ℕ → ℕ → ℕ → ℝ)
    {H δ L : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L) (hdensity : δ * (Ω.card : ℝ) ≤ (G.card : ℝ))
    (hM : ∑ w ∈ Ω, (∑ j ∈ Ioc 0 J,
      |quadraticPrimeCellRieszSum χ (J^4) ((j:ℝ)^4) w.1 w.2 (e w.1 w.2 j) (f w.1 w.2 j) -
        degreeOnePrimeRieszSumWith χ (J^4) ((j:ℝ)^4) 1|)^k ≤ Ω.card * L^k)
    (hneg : ∀ w ∈ G, ∀ j ∈ Ioc 0 J, e w.1 w.2 j = -1 ∨ f w.1 w.2 j = -1)
    (hH : ∀ w ∈ G, ∑ j ∈ Ioc 0 J, max (c j -
      quadraticPrimePowerCellRieszSum χ (J^4) ((j:ℝ)^4) w.1 w.2 (e w.1 w.2 j) (f w.1 w.2 j)) 0 ≤ H) :
    ∑ j ∈ Ioc 0 J, max (c j - degreeOnePrimeRieszSumWith χ (J^4) ((j:ℝ)^4) 1) 0 ≤
      H + 8*(Module.finrank ℚ F : ℝ)*(Real.log 4+4)*(J:ℝ)^(19/3:ℝ) +
        L * δ ^ (-(k : ℝ)⁻¹) := by
  apply quadraticPrimeCell_fourthPower_deficit_moment_transfer χ J hk Ω G hΩ hG c e f hδ hL hdensity hM
  intro w hw
  have hdiff := quadraticPrimePowerCell_fourthPower_deficit_sub_prime χ hJ w.1 w.2 c
    (e w.1 w.2) (f w.1 w.2) (hneg w hw)
  linarith [(abs_le.mp hdiff).1, hH w hw]

/-- Summing a finite family of observations with one common normalized moment
radius multiplies the radius by the number of observations. -/
theorem quadraticPrime_uniform_sum_moment {ι α : Type*} (Ω : Finset α)
    (I : Finset ι) {k : ℕ} (hk : 0 < k) (x : ι → α → ℝ) (R : ℝ)
    (hx : ∀ i ∈ I, ∀ w ∈ Ω, 0 ≤ x i w)
    (hM : ∀ i ∈ I, ∑ w ∈ Ω, (x i w)^k ≤ Ω.card * R^k) :
    ∑ w ∈ Ω, (∑ i ∈ I, x i w)^k ≤ Ω.card * ((I.card : ℝ)*R)^k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hp : (1 : ℝ) ≤ (m.succ : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have hpoint (w : α) (hw : w ∈ Ω) : (∑ i ∈ I, x i w)^(m+1) ≤
      (I.card : ℝ)^m * ∑ i ∈ I, (x i w)^(m+1) := by
    have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg I hp (fun i hi ↦ hx i hi w hw)
    rw [show ((m.succ : ℕ) : ℝ) - 1 = (m : ℝ) by simp] at h
    simpa only [Real.rpow_natCast] using h
  calc _ ≤ ∑ w ∈ Ω, (I.card : ℝ)^m * ∑ i ∈ I, (x i w)^(m+1) := sum_le_sum hpoint
       _ = (I.card : ℝ)^m * ∑ i ∈ I, ∑ w ∈ Ω, (x i w)^(m+1) := by
         rw [← mul_sum]
         congr 1
         exact sum_comm
       _ ≤ (I.card : ℝ)^m * ∑ _i ∈ I, (Ω.card : ℝ) * R^(m+1) :=
         mul_le_mul_of_nonneg_left (sum_le_sum hM) (by positivity)
       _ = _ := by simp only [sum_const, nsmul_eq_mul, mul_pow, pow_succ]; ring

/-- A uniform one-twist k-th moment for the physical Riesz kernels, including
a bounded multiplier, gives the cumulative normalized (3JR)^k bound over
ordered pairs. The two signs may vary with both primes and each fourth power. -/
theorem quadraticPrimeTwist_fourthPower_cell_moment_of_oneTwist
    {F : Type*} [Field F] [NumberField F] (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (J k : ℕ) (U : Finset ℕ) (R : ℝ) (hk : 0 < k) (_hR : 0 ≤ R)
    (hc : ∀ q ∈ U, ∀ p ∈ Nat.primesLE (J^4), Nat.Coprime q p)
    (e f : ℕ → ℕ → ℕ → ℝ) (he : ∀ q d j, |e q d j| = 1) (hf : ∀ q d j, |f q d j| = 1)
    (hM : ∀ j ∈ Ioc 0 J, ∀ u : ℕ → ℝ, (∀ p ∈ Nat.primesLE (J^4), |u p| ≤ 1) →
      ∑ q ∈ U, |degreeOnePrimeRieszSumWith χ (J^4) ((j:ℝ)^4)
        (fun p ↦ u p * (jacobiSym q p : ℝ))|^k ≤ U.card * R^k) :
    ∑ w ∈ U ×ˢ U, (∑ j ∈ Ioc 0 J,
      |quadraticPrimeCellRieszSum χ (J^4) ((j:ℝ)^4) w.1 w.2 (e w.1 w.2 j) (f w.1 w.2 j) -
        degreeOnePrimeRieszSumWith χ (J^4) ((j:ℝ)^4) 1|)^k ≤
      (U.card : ℝ)^2 * (3*(J:ℝ)*R)^k := by
  let Ω := U ×ˢ U
  let x (j : ℕ) (w : ℕ × ℕ) := |quadraticPrimeCellRieszSum χ (J^4) ((j:ℝ)^4) w.1 w.2
    (e w.1 w.2 j) (f w.1 w.2 j) - degreeOnePrimeRieszSumWith χ (J^4) ((j:ℝ)^4) 1|
  have hsample (j : ℕ) (hj : j ∈ Ioc 0 J) : ∑ w ∈ Ω, (x j w)^k ≤ Ω.card*(3*R)^k := by
    let a (q : ℕ) := |degreeOnePrimeRieszSumWith χ (J^4) ((j:ℝ)^4) (fun p ↦ (jacobiSym q p : ℝ))|
    let b (q d : ℕ) := |degreeOnePrimeRieszSumWith χ (J^4) ((j:ℝ)^4)
      (fun p ↦ (jacobiSym q p : ℝ)*(jacobiSym d p : ℝ))|
    have hone : ∑ q ∈ U, (a q)^k ≤ U.card*R^k := by
      simpa only [a, one_mul] using hM j hj (fun _ ↦ 1) (by simp)
    have htwo (q : ℕ) : ∑ d ∈ U, (b q d)^k ≤ U.card*R^k := by
      apply hM j hj (fun p ↦ (jacobiSym q p : ℝ))
      intro p _
      rcases jacobiSym.trichotomy q p with h | h | h <;> simp [h]
    let X : Fin 3 → (ℕ × ℕ) → ℝ :=
      ![fun w ↦ a w.1, fun w ↦ a w.2, fun w ↦ b w.1 w.2]
    have honePair : ∑ w ∈ Ω, (a w.1)^k ≤ Ω.card*R^k := by
      calc _ = (U.card : ℝ) * ∑ q ∈ U, (a q)^k := by
             simp only [Ω, sum_product, sum_const, nsmul_eq_mul, mul_sum]
           _ ≤ _ := by
             simpa only [Ω, card_product, Nat.cast_mul, mul_assoc] using
               mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg (α := ℝ) U.card)
    have htwoPair : ∑ w ∈ Ω, (a w.2)^k ≤ Ω.card*R^k := by
      calc _ = (U.card : ℝ) * ∑ d ∈ U, (a d)^k := by
             simp only [Ω, sum_product, sum_const, nsmul_eq_mul]
           _ ≤ _ := by
             simpa only [Ω, card_product, Nat.cast_mul, mul_assoc] using
               mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg (α := ℝ) U.card)
    have hbothPair : ∑ w ∈ Ω, (b w.1 w.2)^k ≤ Ω.card*R^k := by
      calc _ = ∑ q ∈ U, ∑ d ∈ U, (b q d)^k := sum_product ..
           _ ≤ ∑ _q ∈ U, (U.card : ℝ) * R^k := sum_le_sum fun q _ ↦ htwo q
           _ = _ := by simp only [Ω, sum_const, nsmul_eq_mul, card_product, Nat.cast_mul, mul_assoc]
    have hpoint (w : ℕ × ℕ) (hw : w ∈ Ω) : x j w ≤ ∑ i, X i w := by
      obtain ⟨hq, hd⟩ := mem_product.mp hw
      have h := quadraticPrimeTwist_cell_error χ (J^4) w.1 w.2 ((j:ℝ)^4)
        (e w.1 w.2 j) (f w.1 w.2 j) (he ..) (hf ..) (hc _ hq) (hc _ hd)
      simpa [x, X, a, b, Fin.sum_univ_succ, add_assoc] using h
    calc _ ≤ ∑ w ∈ Ω, (∑ i, X i w)^k := sum_le_sum fun w hw ↦ pow_le_pow_left₀ (abs_nonneg _) (hpoint w hw) _
         _ ≤ _ := by
           have all := quadraticPrime_uniform_sum_moment Ω (univ : Finset (Fin 3)) hk X R
             (by intro i _ w _; fin_cases i <;> exact abs_nonneg _)
             (by intro i _; fin_cases i
                 · exact honePair
                 · exact htwoPair
                 · exact hbothPair)
           simpa only [card_univ, Fintype.card_fin, Nat.cast_ofNat] using all
  calc _ ≤ (Ω.card:ℝ) * (((Ioc 0 J).card:ℝ)*(3*R))^k :=
         quadraticPrime_uniform_sum_moment Ω (Ioc 0 J) hk x (3*R) (fun _ _ _ _ ↦ abs_nonneg _) hsample
       _ = _ := by
         simp only [Ω, card_product, Nat.cast_mul, Nat.card_Ioc, Nat.sub_zero, pow_two]
         rw [show (J:ℝ)*(3*R) = 3*J*R by ring]

/-- For large fourth-power samples, the auxiliary dyadic primes are odd and squarefree,
are coprime to all sample primes, and satisfy both cardinality bounds. -/
theorem quadraticPrime_fourthPower_auxiliary_data :
    ∀ᶠ J : ℕ in atTop, let U := Nat.primesLE (2 * J ^ 12) \ Nat.primesLE (J ^ 12)
      2 ≤ J ∧ U.Nonempty ∧ U ⊆ (Ioc 0 (2 * J ^ 12)).filter (fun n ↦ Odd n ∧ Squarefree n) ∧
      (∀ q ∈ U, ∀ p ∈ Nat.primesLE (J ^ 4), Nat.Coprime q p) ∧
      U.card ≤ 2 * J ^ 12 ∧
      (J : ℝ) ^ 12 ≤ 2 * (U.card : ℝ) * Real.log (2 * (J : ℝ) ^ 12) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp quadraticPrime_dyadic_card
  filter_upwards [eventually_ge_atTop (max 2 N)] with J hJ
  intro U
  have hJ2 : 2 ≤ J := by omega
  have hJ1 : 1 ≤ J := by omega
  have hJQ : J ≤ J ^ 12 := le_self_pow₀ hJ1 (by decide)
  have hTQ : J ^ 4 ≤ J ^ 12 := pow_le_pow_right₀ hJ1 (by decide)
  have hcount : (J : ℝ) ^ 12 ≤ 2 * (U.card : ℝ) * Real.log (2 * (J : ℝ) ^ 12) := by
    have h := hN (J ^ 12) (by omega)
    change ((J ^ 12 : ℕ) : ℝ) ≤ 2 * (U.card : ℝ) * Real.log (2 * ((J ^ 12 : ℕ) : ℝ)) at h
    push_cast at h
    exact h
  have bounds (q : ℕ) (hq : q ∈ U) : J ^ 12 < q ∧ q ≤ 2 * J ^ 12 ∧ q.Prime := by
    obtain ⟨hin, hout⟩ := mem_sdiff.mp hq
    obtain ⟨hhi, hp⟩ := Nat.mem_primesLE.mp hin
    exact ⟨lt_of_not_ge fun h ↦ hout (Nat.mem_primesLE.mpr ⟨h, hp⟩), hhi, hp⟩
  have hI : U ⊆ Ioc 0 (2 * J ^ 12) := fun q hq ↦
    mem_Ioc.mpr ⟨(bounds q hq).2.2.pos, (bounds q hq).2.1⟩
  refine ⟨hJ2, ?_, ?_, ?_, ?_, hcount⟩
  · apply Finset.card_pos.mp
    by_contra! hz
    rw [Nat.le_zero.mp hz, Nat.cast_zero, mul_zero, zero_mul] at hcount
    have hjpos : 0 < (J : ℝ) := by exact_mod_cast (show 0 < J by omega)
    exact (not_le_of_gt (pow_pos hjpos 12)) hcount
  · intro q hq
    obtain ⟨hlo, _, hp⟩ := bounds q hq
    exact mem_filter.mpr ⟨hI hq, hp.odd_of_ne_two (by omega), hp.squarefree⟩
  · intro q hq p hp
    obtain ⟨hlo, _, hqprime⟩ := bounds q hq
    obtain ⟨hle, hpprime⟩ := Nat.mem_primesLE.mp hp
    exact (Nat.coprime_primes hqprime hpprime).mpr (by omega)
  · simpa only [Nat.card_Ioc, Nat.sub_zero] using card_le_card hI

/-- The physical one-twist second moment on the dyadic auxiliary primes, uniform over
every real cutoff through the fourth power and every bounded real prime multiplier. -/
theorem quadraticPrimeTwist_fourthPower_hecke_secondMoment {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    ∀ᶠ J : ℕ in atTop, let U := Nat.primesLE (2 * J ^ 12) \ Nat.primesLE (J ^ 12)
      ∀ (x : ℝ), x ≤ ((J ^ 4 : ℕ) : ℝ) → ∀ u : ℕ → ℝ,
      (∀ p ∈ Nat.primesLE (J ^ 4), |u p| ≤ 1) →
      ∑ q ∈ U, |degreeOnePrimeRieszSumWith χ (J ^ 4) x
        (fun p ↦ u p * (jacobiSym q p : ℝ))| ^ 2 ≤
        (U.card : ℝ) * (100 * (Module.finrank ℚ F : ℝ) * (J : ℝ) ^ 6 * Real.log (2 + J)) ^ 2 := by
  filter_upwards [quadraticPrime_fourthPower_auxiliary_data] with J hJ
  intro U x hx u hu
  obtain ⟨hJ2, _, _, _, _, hcount⟩ := hJ
  have sub : U ⊆ range (2 * J ^ 12 + 1) := fun q hq ↦
    mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_mem_primesLE (mem_sdiff.mp hq).1))
  have hbound := quadraticPrime_fourthPower_secondMoment_bound (J := (J : ℝ))
    (n := (U.card : ℝ)) (D := (Module.finrank ℚ F : ℝ))
    (by exact_mod_cast hJ2) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hcount
  simp only [sq_abs]
  apply (sum_le_sum_of_subset_of_nonneg sub fun _ _ _ ↦ sq_nonneg _).trans
  apply le_trans ?_ hbound
  have hraw := quadraticPrimeTwist_hecke_secondMoment χ (J ^ 4) 0 (2 * J ^ 12 + 1) hx u hu
  push_cast at hraw
  simpa only [degreeOnePrimeRieszSumWith, ← mul_assoc, zero_add] using hraw

local notation "momentPrimes(" J ")" =>
  (Nat.primesLE (2 * (J : ℕ) ^ 12) \ Nat.primesLE ((J : ℕ) ^ 12))

/-- At every fourth-power sample choose one quadratic sign cell separately for each
ordered pair of dyadic auxiliary primes. The k-th moment of the cumulative absolute
difference from the unrestricted prime sum has normalized radius L. -/
def QuadraticPrimeCellFourthPowerMoment {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (J k : ℕ) (L : ℝ) : Prop :=
  let U := momentPrimes(J)
  ∀ (e f : ℕ → ℕ → ℕ → ℝ), (∀ q d j, |e q d j| = 1) → (∀ q d j, |f q d j| = 1) →
    ∑ w ∈ U ×ˢ U, (∑ j ∈ Ioc 0 J,
      |quadraticPrimeCellRieszSum χ (J ^ 4) ((j : ℝ) ^ 4) w.1 w.2
        (e w.1 w.2 j) (f w.1 w.2 j) - degreeOnePrimeRieszSumWith χ (J ^ 4) ((j : ℝ) ^ 4) 1|) ^ k ≤
      (U.card : ℝ) ^ 2 * L ^ k

/-- A uniform one-twist bound through J⁴, including a bounded extra prime weight,
gives the normalized dyadic selected-cell moment with cumulative radius 3JR. -/
theorem quadraticPrimeCellFourthPowerMoment_of_oneTwist
    {F : Type*} [Field F] [NumberField F] (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    {J k : ℕ} {R : ℝ} (_hJ : 1 ≤ J)
    (hcoprime : ∀ q ∈ momentPrimes(J), ∀ p ∈ Nat.primesLE (J ^ 4), Nat.Coprime q p)
    (hk : 0 < k) (hR : 0 ≤ R)
    (honeTwist : ∀ x : ℝ, x ≤ ((J ^ 4 : ℕ) : ℝ) → ∀ u : ℕ → ℝ,
      (∀ p ∈ Nat.primesLE (J ^ 4), |u p| ≤ 1) →
      ∑ q ∈ momentPrimes(J), |degreeOnePrimeRieszSumWith χ (J ^ 4) x
        (fun p ↦ u p * (jacobiSym q p : ℝ))| ^ k ≤ (momentPrimes(J).card : ℝ) * R ^ k) :
    QuadraticPrimeCellFourthPowerMoment χ J k (3 * (J : ℝ) * R) := by
  intro e f he hf
  apply quadraticPrimeTwist_fourthPower_cell_moment_of_oneTwist χ J k (momentPrimes(J)) R hk hR
    hcoprime e f he hf
  intro j hj
  apply honeTwist
  exact_mod_cast Nat.pow_le_pow_left (mem_Ioc.mp hj).2 4

/-- A normalized dyadic moment transfers a bound on complete negative cells to the
unrestricted fourth-power prime deficit, at density cost δ^(-1/k). -/
theorem QuadraticPrimeCellFourthPowerMoment.complete_deficit_transfer
    {F : Type*} [Field F] [NumberField F] {χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)}
    {J k : ℕ} {L : ℝ} (hmoment : QuadraticPrimeCellFourthPowerMoment χ J k L)
    (hU : momentPrimes(J).Nonempty) (hJ : 1 ≤ J) (hk : 0 < k) (hL : 0 ≤ L)
    (c : ℕ → ℝ) (e f : ℕ → ℕ → ℕ → ℝ)
    (he : ∀ q d j, |e q d j| = 1) (hf : ∀ q d j, |f q d j| = 1)
    (G : Finset (ℕ × ℕ)) (hG : G ⊆ momentPrimes(J) ×ˢ momentPrimes(J))
    {δ H : ℝ} (hδ : 0 < δ) (hdensity : δ * (momentPrimes(J).card : ℝ) ^ 2 ≤ (G.card : ℝ))
    (hnegative : ∀ w ∈ G, ∀ j ∈ Ioc 0 J, e w.1 w.2 j = -1 ∨ f w.1 w.2 j = -1)
    (hcomplete : ∀ w ∈ G, ∑ j ∈ Ioc 0 J, max (c j -
      quadraticPrimePowerCellRieszSum χ (J ^ 4) ((j : ℝ) ^ 4) w.1 w.2
        (e w.1 w.2 j) (f w.1 w.2 j)) 0 ≤ H) :
    ∑ j ∈ Ioc 0 J, max (c j - degreeOnePrimeRieszSumWith χ (J ^ 4) ((j : ℝ) ^ 4) 1) 0 ≤
      H + 8 * (Module.finrank ℚ F : ℝ) * (Real.log 4 + 4) * (J : ℝ) ^ (19 / 3 : ℝ) +
        L * δ ^ (-(k : ℝ)⁻¹) := by
  apply quadraticPrimePowerCell_fourthPower_deficit_moment_transfer χ hJ hk _ G
    (hU.product hU) hG c e f hδ hL ?_ ?_ hnegative hcomplete
  · simpa only [card_product, Nat.cast_mul, pow_two] using hdensity
  · simpa only [card_product, Nat.cast_mul, pow_two] using hmoment e f he hf

/-- For a fixed Hecke character the cumulative second moment admits the explicit radius
`300 [F:ℚ] J^7 log(2+J)`. This uses the elementary complete-period estimate. -/
theorem quadraticPrimeCell_fourthPower_secondMoment {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    ∀ᶠ J : ℕ in atTop, QuadraticPrimeCellFourthPowerMoment χ J 2
      (300*(Module.finrank ℚ F : ℝ)*(J:ℝ)^7*Real.log (2+J)) := by
  filter_upwards [quadraticPrime_fourthPower_auxiliary_data,
    quadraticPrimeTwist_fourthPower_hecke_secondMoment χ] with J hg h
  obtain ⟨hJ, _, _, hc, _, _⟩ := hg
  have hpos : 0 ≤ Real.log (2+(J:ℝ)) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) J])
  have hbound := quadraticPrimeCellFourthPowerMoment_of_oneTwist χ (by omega : 1 ≤ J) hc
    (by decide : 0 < 2) (by positivity : 0 ≤ 100*(Module.finrank ℚ F : ℝ)*J^6*Real.log (2+J)) h
  convert hbound using 1; ring

end RiemannMasullo
