module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.Finset.NatDivisors
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Möbius-weighted divisor sums on products

When the proper divisors of a multiplier lie on the constant part of the weight,
factoring the multiplier out of a weighted Möbius error introduces exactly its
Möbius sign. Four actual scalar products for two multipliers of opposite signs
therefore form one scalar product of differences of shifted columns.

These identities apply to prime and semiprime multipliers in the rational theta
comparison for Theorem 12.5.1.1, pp. 519–520. The bounds permit a common physical
cutoff and arbitrary real inner product space, including square-integrable columns.
The final uniqueness results distinguish the selected terms after reduction.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius RealInnerProductSpace

public noncomputable section

namespace MoebiusCofactor

variable {R : Type*} [Ring R]

/-- The finite divisor sum weighted by the Möbius function. -/
@[expose] def weightedSum (w : ℕ → R) (n : ℕ) : R := ∑ d ∈ n.divisors, (μ d : R) * w d

/-- The weighted Möbius divisor sum with the unit term subtracted. -/
@[expose] def error (w : ℕ → R) (n : ℕ) : R := weightedSum w n - if n = 1 then 1 else 0

private theorem sum_mu (R : Type*) [Ring R] (n : ℕ) : (∑ d ∈ n.divisors, (μ d : R)) = if n = 1 then 1 else 0 := by
  have h : (∑ d ∈ n.divisors, μ d) = if n = 1 then 1 else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply, moebius_mul_coe_zeta]
    rfl
  have he := congrArg (Int.cast (R := R)) h
  push_cast at he
  split_ifs at he ⊢ <;> simpa using he

/-- Subtracting the unit term centers the weight at one on every divisor. -/
theorem error_eq_centered (w : ℕ → R) (n : ℕ) :
    error w n = weightedSum (fun d ↦ w d - 1) n := by
  unfold error weightedSum
  simp only [mul_sub, mul_one, sum_sub_distrib, sum_mu]

/-- Factor the weighted divisor sum at coprime arguments. -/
theorem weightedSum_mul_coprime {a k : ℕ} (hc : a.Coprime k) (w : ℕ → R) :
    weightedSum w (a * k) = ∑ f ∈ a.divisors, (μ f : R) * weightedSum (fun d ↦ w (f * d)) k := by
  simp only [weightedSum]
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image (fun _ hi _ hj he ↦ hc.mul_injOn_divisors hi hj he),
    Finset.sum_product]
  apply sum_congr rfl
  intro f hf
  rw [mul_sum]
  apply sum_congr rfl
  intro d hd
  have hfd := (hc.coprime_dvd_left (Nat.dvd_of_mem_divisors hf)).coprime_dvd_right (Nat.dvd_of_mem_divisors hd)
  rw [isMultiplicative_moebius.map_mul_of_coprime hfd, Int.cast_mul, mul_assoc]

/-- Only the full multiplier survives when every proper divisor times each visible cofactor has weight one. -/
theorem error_mul_of_proper_divisors {a k : ℕ} (hc : a.Coprime k) (ha : a ≠ 0) (w : ℕ → R)
    (hw : ∀ f ∈ a.divisors, f ≠ a → ∀ d ∈ k.divisors, w (f * d) = 1) :
    error w (a * k) = (μ a : R) * error (fun d ↦ w (a * d)) k := by
  rw [error_eq_centered, weightedSum_mul_coprime hc, sum_eq_single a, error_eq_centered]
  · intro f hf hfa
    simp only [weightedSum]
    apply mul_eq_zero_of_right
    apply sum_eq_zero
    intro d hd
    rw [hw f hf hfa d hd, sub_self, mul_zero]
  · exact fun h ↦ False.elim (h (Nat.mem_divisors.mpr ⟨dvd_refl a, ha⟩))

private theorem proper_divisor_minFac {a d : ℕ} (hd : d ∈ a.divisors) (hne : d ≠ a) :
    d * a.minFac ≤ a := by
  obtain ⟨hda, ha⟩ := Nat.mem_divisors.mp hd
  obtain ⟨u, hu⟩ := hda
  have hu₀ : 0 < u := by
    by_contra! h
    simp [show u = 0 by omega] at hu
    omega
  have hu₁ : u ≠ 1 := by rintro rfl; simp_all
  have h := Nat.minFac_le_of_dvd (n := a) (by omega : 2 ≤ u) (by rw [hu]; exact dvd_mul_left ..)
  calc
    d * a.minFac ≤ d * u := Nat.mul_le_mul_left d h
    _ = a := hu.symm

/-- A cutoff by the least prime factor implies the exact signed cofactor formula. -/
theorem error_mul_of_minFac {a k L : ℕ} (hc : a.Coprime k) (ha : a ≠ 0) (w : ℕ → R)
    (hw : ∀ n ≤ L, w n = 1) (hcap : a * k / a.minFac ≤ L) :
    error w (a * k) = (μ a : R) * error (fun d ↦ w (a * d)) k := by
  apply error_mul_of_proper_divisors hc ha
  intro f hf hfa d hd
  apply hw _ (le_trans _ hcap)
  apply (Nat.le_div_iff_mul_le (Nat.minFac_pos a)).mpr
  have hdk := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.dvd_of_mem_divisors hd)
  calc
    f * d * a.minFac = (f * a.minFac) * d := by ring
    _ ≤ _ := Nat.mul_le_mul (proper_divisor_minFac hf hfa) hdk

/-- A squared prime divisor forces the error to vanish when all squarefree divisors lie on the plateau. -/
theorem error_eq_zero_of_square {p n L : ℕ} (hp : p.Prime) (hpn : p ^ 2 ∣ n)
    (w : ℕ → R) (hw : ∀ d ≤ L, w d = 1) (hcap : n / p ≤ L) : error w n = 0 := by
  rw [error_eq_centered, weightedSum]
  apply sum_eq_zero
  intro d hd
  by_cases h : Squarefree d
  · obtain ⟨⟨e, he⟩, hn⟩ := Nat.mem_divisors.mp hd
    have hpe : p ∣ e := h.dvd_of_squarefree_of_mul_dvd_mul_right (by simpa only [← sq, ← he] using hpn)
    have he₀ : 0 < e := by
      by_contra! hz
      simp [show e = 0 by omega] at he
      omega
    have hdp : d * p ≤ n := he ▸ Nat.mul_le_mul_left d (Nat.le_of_dvd he₀ hpe)
    rw [hw d (((Nat.le_div_iff_mul_le hp.pos).mpr hdp).trans hcap), sub_self, mul_zero]
  · rw [moebius_eq_zero_of_not_squarefree h, Int.cast_zero, zero_mul]

/-- A large least prime factor gives both coprimality and the signed cofactor identity through a common cutoff. -/
theorem error_mul_of_large_factors {a k X L : ℕ} (hk : k ≠ 0) (ha : 0 < a)
    (hn : a * k ≤ X) (hrough : X < a * a.minFac) (hplateau : X / a.minFac ≤ L)
    {w : ℕ → R} (hw : ∀ n ≤ L, w n = 1) :
    error w (a * k) = (μ a : R) * error (fun d ↦ w (a * d)) k := by
  have hka : k < a.minFac := Nat.lt_of_mul_lt_mul_left (hn.trans_lt hrough)
  exact error_mul_of_minFac (Nat.coprime_of_lt_minFac hk hka) ha.ne' w hw
    ((Nat.div_le_div_right hn).trans hplateau)

/-- Every positive power of a prime gives the same first difference of the weight on a coprime cofactor. -/
theorem error_prime_power {p k : ℕ} (hp : p.Prime) (hc : p.Coprime k) (i : ℕ) (w : ℕ → R) :
    error w (p ^ (i + 1) * k) = weightedSum (fun d ↦ w d - w (p * d)) k := by
  rw [error_eq_centered, weightedSum_mul_coprime (hc.pow_left _)]
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ', Finset.sum_range_succ']
  simp [moebius_apply_prime_pow, hp, moebius_apply_prime, Finset.sum_const_zero]
  simp only [weightedSum, mul_sub, mul_one, sum_sub_distrib]
  abel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The physical column at an integer norm, multiplied by its centered Möbius coefficient. -/
@[expose] def column (w : ℕ → ℝ) (h : ℕ → E) (n : ℕ) : E := error w n • h n

/-- The column obtained by evaluating the weight and the detector after a multiplicative shift. -/
@[expose] def shiftedColumn (w : ℕ → ℝ) (h : ℕ → E) (a k : ℕ) : E :=
  error (fun d ↦ w (a * d)) k • h (a * k)

private theorem column_factor {a k X L : ℕ} (hk : k ≠ 0) (ha : 0 < a) (hn : a * k ≤ X)
    (hrough : X < a * a.minFac) (hplateau : X / a.minFac ≤ L)
    {w : ℕ → ℝ} (hw : ∀ n ≤ L, w n = 1) (h : ℕ → E) :
    column w h (a * k) = (μ a : ℝ) • shiftedColumn w h a k := by
  rw [column, error_mul_of_large_factors hk ha hn hrough hplateau hw, mul_smul, shiftedColumn]

private theorem column_factor_on_support {a k X L : ℕ} (hk : k ≠ 0) (ha : 0 < a)
    (hrough : X < a * a.minFac) (hplateau : X / a.minFac ≤ L)
    {w : ℕ → ℝ} (hw : ∀ n ≤ L, w n = 1) (h : ℕ → E) (hs : ∀ n, X < n → h n = 0) :
    column w h (a * k) = (μ a : ℝ) • shiftedColumn w h a k := by
  by_cases hn : a * k ≤ X
  · exact column_factor hk ha hn hrough hplateau hw h
  · simp [column, shiftedColumn, hs _ (Nat.lt_of_not_ge hn)]

private theorem pair_gram (x X y Y : E) :
    ⟪x, y⟫ + ⟪x, Y⟫ + ⟪X, y⟫ + ⟪X, Y⟫ = ⟪x + X, y + Y⟫ := by
  simp only [inner_add_left, inner_add_right]
  abel

private theorem column_add {a b : ℕ} (hμa : μ a = -1) (hμb : μ b = 1)
    {X L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hra : X < a * a.minFac) (hrb : X < b * b.minFac)
    (hLa : X / a.minFac ≤ L) (hLb : X / b.minFac ≤ L)
    {w : ℕ → ℝ} (hw : ∀ n ≤ L, w n = 1) (h : ℕ → E) {k : ℕ} (hk : k ≠ 0)
    (hs : ∀ n, X < n → h n = 0) :
    column w h (a * k) + column w h (b * k) = shiftedColumn w h b k - shiftedColumn w h a k := by
  rw [column_factor_on_support hk ha hra hLa hw h hs, column_factor_on_support hk hb hrb hLb hw h hs, hμa, hμb]
  simp [sub_eq_add_neg, add_comm]

/-- The sum of the four physical scalar products for opposite Möbius signs equals a scalar product of two differences. -/
theorem matched_gram {a b X L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hμa : μ a = -1) (hμb : μ b = 1)
    (hra : X < a * a.minFac) (hrb : X < b * b.minFac)
    (hLa : X / a.minFac ≤ L) (hLb : X / b.minFac ≤ L)
    {w : ℕ → ℝ} (hw : ∀ n ≤ L, w n = 1) (h : ℕ → E)
    {u v : ℕ} (hu : u ≠ 0) (hv : v ≠ 0) (hs : ∀ n, X < n → h n = 0) :
    ⟪column w h (a * u), column w h (a * v)⟫ + ⟪column w h (a * u), column w h (b * v)⟫ +
        ⟪column w h (b * u), column w h (a * v)⟫ + ⟪column w h (b * u), column w h (b * v)⟫ =
      ⟪shiftedColumn w h b u - shiftedColumn w h a u, shiftedColumn w h b v - shiftedColumn w h a v⟫ := by
  rw [pair_gram, column_add hμa hμb ha hb hra hrb hLa hLb hw h hu hs,
    column_add hμa hμb ha hb hra hrb hLa hLb hw h hv hs]

/-- The total absolute error after grouping each four terms is bounded by the norms of the corresponding differences. -/
theorem sum_matched_gram_le {ι : Type*} (S : Finset ι) (u v : ι → ℕ)
    {a b X L : ℕ} (ha : 0 < a) (hb : 0 < b) (hμa : μ a = -1) (hμb : μ b = 1)
    (hra : X < a * a.minFac) (hrb : X < b * b.minFac)
    (hLa : X / a.minFac ≤ L) (hLb : X / b.minFac ≤ L)
    {w : ℕ → ℝ} (hw : ∀ n ≤ L, w n = 1) (h : ℕ → E) (hs : ∀ n, X < n → h n = 0)
    (hu : ∀ i ∈ S, u i ≠ 0) (hv : ∀ i ∈ S, v i ≠ 0) :
    ∑ i ∈ S, |⟪column w h (a * u i), column w h (a * v i)⟫ +
        ⟪column w h (a * u i), column w h (b * v i)⟫ + ⟪column w h (b * u i), column w h (a * v i)⟫ +
        ⟪column w h (b * u i), column w h (b * v i)⟫| ≤
      ∑ i ∈ S, ‖shiftedColumn w h b (u i) - shiftedColumn w h a (u i)‖ *
        ‖shiftedColumn w h b (v i) - shiftedColumn w h a (v i)‖ := by
  apply sum_le_sum
  intro i hi
  rw [matched_gram ha hb hμa hμb hra hrb hLa hLb hw h (hu i hi) (hv i hi) hs]
  exact abs_real_inner_le_norm _ _

private theorem eq_of_dvd_of_cardFactors {a b : ℕ} (hb : b ≠ 0) (hd : a ∣ b) (hΩ : cardFactors a = cardFactors b) :
    a = b := by
  obtain ⟨c, rfl⟩ := hd
  obtain ⟨ha, hc⟩ := mul_ne_zero_iff.mp hb
  rw [cardFactors_mul ha hc] at hΩ
  have h := cardFactors_eq_zero_iff_eq_zero_or_one.mp (by omega : cardFactors c = 0)
  simp [h.resolve_left hc]

private theorem factor_unique_of_le {a b j k : ℕ} (ha : a ≠ 0) (hj : j ≠ 0) (hab : cardFactors a = cardFactors b)
    (hk : k < b.minFac) (hle : j ≤ k) (he : a * j = b * k) : a = b := by
  have hc := Nat.coprime_of_lt_minFac hj (hle.trans_lt hk)
  have hba : b ∣ a := hc.dvd_of_dvd_mul_right (he ▸ dvd_mul_right b k)
  exact (eq_of_dvd_of_cardFactors ha hba hab.symm).symm

/-- Two decompositions with the same number of prime factors above their respective cofactors agree. -/
theorem unique_large_factor {a b j k : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0)
    (hab : cardFactors a = cardFactors b) (haj : j < a.minFac) (hbk : k < b.minFac)
    (he : a * j = b * k) : a = b ∧ j = k := by
  have h : a = b := (le_total j k).elim
    (fun hjk ↦ factor_unique_of_le ha hj hab hbk hjk he)
    (fun hkj ↦ (factor_unique_of_le hb hk hab.symm haj hkj he.symm).symm)
  subst b
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha) he⟩

/-- A prime cannot occur in a cluster whose two multiplier factors and remaining cofactor are all below it. -/
theorem distinct_prime_semiprime_clusters {a s t j k : ℕ} (ha : a.Prime)
    (hs : 0 < s) (ht : 0 < t) (hk : 0 < k) (hsa : s < a) (hta : t < a) (hka : k < a) :
    a * j ≠ (s * t) * k := by
  intro he
  have hd : a ∣ s * t * k := he ▸ dvd_mul_right a j
  rcases ha.dvd_mul.mp hd with hd | hd
  · rcases ha.dvd_mul.mp hd with hd | hd
    · exact hsa.not_ge (Nat.le_of_dvd hs hd)
    · exact hta.not_ge (Nat.le_of_dvd ht hd)
  · exact hka.not_ge (Nat.le_of_dvd hk hd)

/-- Two ordered pairs with the same indices have the same reduced directions and positive common cofactor. -/
theorem primitive_pair_unique {a b c d j k : ℕ} (hab : a.Coprime b) (hcd : c.Coprime d)
    (hj : 0 < j) (hk : 0 < k) (h₁ : a * j = c * k) (h₂ : b * j = d * k) :
    a = c ∧ b = d ∧ j = k := by
  have hg (u v z : ℕ) (huv : u.Coprime v) : (u * z).gcd (v * z) = z := by
    rw [Nat.gcd_mul_right, huv.gcd_eq_one]
    simp
  have he := (hg a b j hab).symm
  rw [h₁, h₂, hg c d k hcd] at he
  subst k
  exact ⟨Nat.eq_of_mul_eq_mul_right hj h₁, Nat.eq_of_mul_eq_mul_right hj h₂, rfl⟩

/-- Deleting injectively matched columns changes the full sum by at most the total shifted-column difference, for any remaining columns. -/
theorem sum_remove_matched {ι : Type*} (S : Finset ι) (T : Finset ℕ) (a b k : ι → ℕ)
    (hi : Set.InjOn (fun i ↦ a i * k i) S) (hj : Set.InjOn (fun i ↦ b i * k i) S)
    (hd : Disjoint (S.image fun i ↦ a i * k i) (S.image fun i ↦ b i * k i))
    (hT : (S.image fun i ↦ a i * k i) ∪ (S.image fun i ↦ b i * k i) ⊆ T)
    {X L : ℕ} {w : ℕ → ℝ} (hw : ∀ n ≤ L, w n = 1) (h : ℕ → E) (hs : ∀ n, X < n → h n = 0)
    (ha : ∀ i ∈ S, 0 < a i ∧ μ (a i) = -1 ∧ X < a i * (a i).minFac ∧ X / (a i).minFac ≤ L)
    (hb : ∀ i ∈ S, 0 < b i ∧ μ (b i) = 1 ∧ X < b i * (b i).minFac ∧ X / (b i).minFac ≤ L)
    (hk : ∀ i ∈ S, k i ≠ 0) :
    ‖(∑ n ∈ T, column w h n) -
        ∑ n ∈ T \ ((S.image fun i ↦ a i * k i) ∪ (S.image fun i ↦ b i * k i)), column w h n‖ ≤
      ∑ i ∈ S, ‖shiftedColumn w h (b i) (k i) - shiftedColumn w h (a i) (k i)‖ := by
  have he := Finset.sum_sdiff hT (f := column w h)
  rw [← eq_sub_iff_add_eq'.mpr he, sum_union hd, sum_image hi, sum_image hj, ← sum_add_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i hmem
  obtain ⟨ha₀, haμ, har, haL⟩ := ha i hmem
  obtain ⟨hb₀, hbμ, hbr, hbL⟩ := hb i hmem
  rw [column_add haμ hbμ ha₀ hb₀ har hbr haL hbL hw h (hk i hmem) hs]

end MoebiusCofactor
