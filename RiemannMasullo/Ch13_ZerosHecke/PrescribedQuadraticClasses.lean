module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.GCD.BigOperators

/-! # Prescribing quadratic classes on a finite rational prime range

At any fixed cutoff the two auxiliary primes can select one specified set of odd primes
in a nonidentity class. The prime number theorem for fixed progressions supplies the two
primes in the same dyadic interval and counts their available progressions.
For the rational character modulo four, one choice gives zero deficit up to the
prescribed cutoff. An integer logarithm enclosure also gives finite-cutoff sign tests.
-/

open Finset Filter
open scoped Topology

@[expose] public noncomputable section

namespace RiemannMasullo

private theorem prescribedQuadratic_residue {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (e : Bool) : ∃ r : ℕ, r.Coprime p ∧ jacobiSym r p = (if e then -1 else 1) := by
  let : Fact p.Prime := ⟨hp⟩
  cases e with
  | false => exact ⟨1, Nat.coprime_one_left _, by simp⟩
  | true =>
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod p) (by
      rwa [ZMod.ringChar_zmod_n])
    refine ⟨(a : ZMod p).val, ?_, ?_⟩
    · exact (ZMod.isUnit_iff_coprime _ _).mp (by simp)
    · simpa [← jacobiSym.legendreSym.to_jacobiSym, legendreSym] using ha

private theorem prescribedQuadratic_progression (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (e : ℕ → Bool) :
    let m := 8 * ∏ p ∈ P, p
    ∃ a : ℕ, a.Coprime m ∧ ∀ n : ℕ, n ≡ a [MOD m] →
      n ≡ 1 [MOD 8] ∧ ∀ p ∈ P, jacobiSym n p = (if e p then -1 else 1) := by
  classical
  intro m
  have hr (p : ℕ) : ∃ r : ℕ, p ∈ P → r.Coprime p ∧
      jacobiSym r p = (if e p then -1 else 1) := by
    by_cases h : p ∈ P
    · obtain ⟨r,hr⟩ := prescribedQuadratic_residue (hp p h).1 (hp p h).2 (e p)
      exact ⟨r, fun _ ↦ hr⟩
    · exact ⟨1, fun h' ↦ (h h').elim⟩
  choose r hr using hr
  let M := ∏ p ∈ P, p
  let a := Nat.chineseRemainderOfFinset r id P
    (fun p h ↦ (hp p h).1.ne_zero) (fun p h q h' hne ↦
      (Nat.coprime_primes (hp p h).1 (hp q h').1).mpr hne)
  have hc : Nat.Coprime 8 M := Nat.Coprime.prod_right fun p h ↦ by
    have h2 := (Nat.coprime_primes Nat.prime_two (hp p h).1).mpr (hp p h).2.symm
    exact h2.pow_left 3
  let b := Nat.chineseRemainder hc 1 a.val
  have h8 : b.val.Coprime 8 := b.property.1.gcd_eq.trans (Nat.coprime_one_left _)
  have hM : b.val.Coprime M := Nat.Coprime.prod_right fun p h ↦ by
    have hb := (b.property.2.of_dvd (dvd_prod_of_mem id h)).trans (a.property p h)
    exact hb.gcd_eq.trans (hr p h).1
  refine ⟨b.val, h8.mul_right hM, ?_⟩
  intro n hn
  refine ⟨(hn.of_dvd (dvd_mul_right 8 M)).trans b.property.1, ?_⟩
  intro p h
  have hnm : n ≡ a.val [MOD M] := (hn.of_dvd (dvd_mul_left M 8)).trans b.property.2
  have hnr := (hnm.of_dvd (dvd_prod_of_mem id h)).trans (a.property p h)
  exact (jacobiSym.mod_left' (by exact_mod_cast hnr)).trans (hr p h).2

/-- Primes in a dyadic interval belonging to a given residue class. -/
def dyadicPrimesInProgression (m a Y : ℕ) : Finset ℕ :=
  (Ioc Y (2*Y)).filter fun p ↦ p.Prime ∧ p ≡ a [MOD m]

/-- For a fixed reduced residue class, the number of available dyadic primes is
asymptotic to Y divided by φ(m) log(2Y). -/
theorem tendsto_dyadicPrimesInProgression_card {m a : ℕ} [NeZero m] (ha : a.Coprime m) :
    Tendsto (fun Y : ℕ ↦ ((dyadicPrimesInProgression m a Y).card:ℝ) *
      Real.log (2*Y) / Y) atTop (𝓝 (m.totient:ℝ)⁻¹) := by
  let S (n : ℕ) := (Ioc 0 n).filter fun p ↦ p.Prime ∧ p ≡ a [MOD m]
  have hs : Tendsto (fun n : ℕ ↦ ((S n).card:ℝ)*Real.log n/n) atTop (𝓝 (m.totient:ℝ)⁻¹) := by
    simpa [S, Function.comp_def] using
      (Nat.tendsto_card_prime_modEq_mul_log_div_atTop ha).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have h2 : Tendsto (fun n : ℕ ↦ 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by omega : ∀ n : ℕ, n ≤ 2*n) tendsto_id
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hr : Tendsto (fun n : ℕ ↦ Real.log 2 / Real.log n + 1) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := Real.log 2)).div_atTop hl).add_const 1
  have hlim := ((hs.comp h2).const_mul 2).sub (hs.mul hr)
  rw [show 2*(m.totient:ℝ)⁻¹ - (m.totient:ℝ)⁻¹*1 = (m.totient:ℝ)⁻¹ by ring] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hu : S n ∪ dyadicPrimesInProgression m a n = S (2*n) := by
    dsimp only [S, dyadicPrimesInProgression]
    rw [← filter_union, Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (by omega)]
  have hd : Disjoint (S n) (dyadicPrimesInProgression m a n) :=
    (Ioc_disjoint_Ioc_of_le (a := 0) (d := 2*n) (le_refl n)).mono (filter_subset ..) (filter_subset ..)
  have hc := congrArg Finset.card hu
  rw [card_union_of_disjoint hd] at hc
  have he : ((S (2*n)).card:ℝ) = (S n).card + (dyadicPrimesInProgression m a n).card := by
    exact_mod_cast hc.symm
  have hp : 1 < (n:ℝ) := by exact_mod_cast (show 1 < n by omega)
  change 2 * (((S (2*n)).card:ℝ) * Real.log ((2*n:ℕ):ℝ) / ((2*n:ℕ):ℝ)) -
    ((S n).card*Real.log (n:ℝ)/n)*(Real.log 2/Real.log n+1) = _
  push_cast
  rw [he, Real.log_mul (by norm_num) (by linarith : (n:ℝ) ≠ 0)]
  field_simp [ne_of_gt (Real.log_pos hp), ne_of_gt (zero_lt_one.trans hp)]
  ring

/-- Two auxiliary primes can prescribe two independent quadratic-sign patterns on an
arbitrary finite collection of odd primes. Both lie in fixed progressions within the
same dyadic interval, and their pairs have the stated positive asymptotic density.
The modulus depends on the whole collection of prescribed primes. -/
theorem prescribedQuadraticPrimePairs (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (s t : ℕ → Bool) :
    let m := 8*∏ p ∈ P, p
    ∃ a b : ℕ, a.Coprime m ∧ b.Coprime m ∧
      Tendsto (fun Y : ℕ ↦ (((dyadicPrimesInProgression m a Y) ×ˢ
        (dyadicPrimesInProgression m b Y)).card:ℝ)*(Real.log (2*Y)/Y)^2)
          atTop (𝓝 ((m.totient:ℝ)⁻¹^2)) ∧
      ∀ Y q d : ℕ, q ∈ dyadicPrimesInProgression m a Y → d ∈ dyadicPrimesInProgression m b Y →
        q ≡ 1 [MOD 8] ∧ d ≡ 1 [MOD 8] ∧ ∀ p ∈ P,
          jacobiSym q p = (if s p then -1 else 1) ∧
          jacobiSym d p = (if t p then -1 else 1) := by
  intro m
  have hn : m ≠ 0 := Nat.mul_ne_zero (by decide)
    (Finset.prod_ne_zero_iff.mpr fun p h ↦ (hp p h).1.ne_zero)
  let : NeZero m := ⟨hn⟩
  obtain ⟨a,ha,hqa⟩ := prescribedQuadratic_progression P hp s
  obtain ⟨b,hb,hdb⟩ := prescribedQuadratic_progression P hp t
  change a.Coprime m at ha
  change b.Coprime m at hb
  refine ⟨a,b,ha,hb,?_,?_⟩
  · have h := (tendsto_dyadicPrimesInProgression_card ha).mul
      (tendsto_dyadicPrimesInProgression_card hb)
    rw [pow_two]
    apply h.congr
    intro Y
    simp only [card_product, Nat.cast_mul]
    ring
  · intro Y q d hq hd
    have h₁ := hqa q (mem_filter.mp hq).2.2
    have h₂ := hdb d (mem_filter.mp hd).2.2
    exact ⟨h₁.1,h₂.1,fun p h ↦ ⟨h₁.2 p h,h₂.2 p h⟩⟩

/-- Four times a first Riesz sum in the quadratic class (+,−), with arbitrary
real coefficients on the positive integers. -/
def quadraticPlusMinusRiesz (T q d : ℕ) (w : ℕ → ℝ) (x : ℝ) : ℝ :=
  4*∑ n ∈ (Ioc 0 T).filter (fun n ↦ jacobiSym q n = 1 ∧ jacobiSym d n = -1),
    w n * max (x-n) 0

/-- An exactly vanishing cumulative deficit is equivalent to nonnegativity of the
signed class sum at every fourth power in the prefix. -/
theorem quadraticPlusMinusRiesz_deficit_eq_zero_iff (T q d J : ℕ) (w : ℕ → ℝ) :
    (∑ j ∈ Ioc 0 J, max (-quadraticPlusMinusRiesz T q d w ((j:ℝ)^4)) 0) = 0 ↔
      ∀ j ∈ Ioc 0 J, 0 ≤ quadraticPlusMinusRiesz T q d w ((j:ℝ)^4) := by
  rw [sum_eq_zero_iff_of_nonneg (fun j _ ↦ le_max_right _ (0:ℝ))]
  simp

private theorem prescribedQuadratic_chiFour_support {T q d : ℕ}
    (hd : d ≡ 1 [MOD 8])
    (hs : ∀ p ∈ (Nat.primesLE T).erase 2, jacobiSym q p = 1 ∧
      jacobiSym d p = (if p % 4 = 1 then -1 else 1)) :
    (∀ p ∈ Nat.primesLE T, (jacobiSym q p = 1 ∧ jacobiSym d p = -1) ↔ p % 4 = 1) ∧
    ∀ n ≤ T, IsPrimePow n → jacobiSym d n = -1 → ZMod.χ₄ (n : ZMod 4) = 1 := by
  have h2 : jacobiSym d 2 = 1 := by
    have h := hd.of_dvd (by decide : 2 ∣ 8)
    calc _ = jacobiSym 1 2 := jacobiSym.mod_left' (by exact_mod_cast h)
         _ = _ := jacobiSym.one_left _
  constructor
  · intro p hp
    by_cases h : p = 2
    · subst p
      simp [h2]
    · obtain ⟨hq,hd⟩ := hs p (mem_erase_of_ne_of_mem h hp)
      by_cases h1 : p % 4 = 1 <;> simp [hq,hd,h1]
  · intro n hn hpow hneg
    obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff n).mp hpow
    rw [jacobiSym.pow_right] at hneg
    have hp2 : p ≠ 2 := by rintro rfl; simp [h2] at hneg
    have hpt : p ≤ T := (le_self_pow₀ hp.one_le hk.ne').trans hn
    have hdp := (hs p (mem_erase_of_ne_of_mem hp2 (Nat.mem_primesLE.mpr ⟨hpt,hp⟩))).2
    have hp4 : p % 4 = 1 := by
      by_contra! h
      simp [hdp,h] at hneg
    rw [Nat.cast_pow, map_pow, ZMod.χ₄_nat_one_mod_four hp4, one_pow]

private theorem prescribedQuadratic_progression_ramp :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ, C ≤ x → ∀ T : ℕ, x ≤ T →
      x^2/2 ≤ 4*∑ p ∈ (Ioc 0 T).filter (fun p ↦ p.Prime ∧ p ≡ 1 [MOD 4]),
        Real.log p * max (x-p) 0 := by
  let P (t : ℝ) := (Ioc 0 ⌊t⌋₊).filter (fun p ↦ p.Prime ∧ p ≡ 1 [MOD 4])
  let θ (t : ℝ) := ∑ p ∈ P t, Real.log p
  have hc := Chebyshev.tendsto_sum_log_prime_modEq_div_atTop (q := 4) (a := 1) (by decide)
  have he : ∀ᶠ t : ℝ in atTop, (2/5:ℝ) < θ t / t := by
    apply hc.eventually (lt_mem_nhds ?_)
    norm_num [show (4:ℕ).totient=2 by decide]
  obtain ⟨R,hR⟩ := eventually_atTop.mp he
  refine ⟨3*max 1 R, by linarith [le_max_left 1 R], ?_⟩
  intro x hx T hT
  have hpos : 0 < x := by linarith [le_max_left 1 R]
  have hlow₁ := (lt_div_iff₀ (by positivity)).mp (hR (x/3) (by linarith [le_max_right 1 R]))
  have hlow₂ := (lt_div_iff₀ (by positivity)).mp (hR (2*x/3) (by linarith [le_max_right 1 R]))
  let A := (Ioc 0 T).filter (fun p ↦ p.Prime ∧ p ≡ 1 [MOD 4])
  have piece {t : ℝ} (ht : 0 ≤ t) (htx : t ≤ x) :
      (∑ p ∈ A, if (p:ℝ) ≤ t then Real.log p else 0) = θ t := by
    rw [← sum_filter]
    have hset : A.filter (fun p : ℕ ↦ (p:ℝ) ≤ t) = P t := by
      ext p
      simp only [A, P, mem_filter, mem_Ioc, Nat.le_floor_iff ht]
      constructor
      · rintro ⟨⟨⟨hp,_⟩,h₂⟩,ht⟩
        exact ⟨⟨hp,ht⟩,h₂⟩
      · rintro ⟨⟨hp,hp'⟩,h₂⟩
        exact ⟨⟨⟨hp,by exact_mod_cast hp'.trans (htx.trans hT)⟩,h₂⟩,hp'⟩
    rw [hset]
  have hsum : (x/3)*(θ (x/3)+θ (2*x/3)) ≤
      ∑ p ∈ A, Real.log p * max (x-p) 0 := by
    rw [← piece (t := x/3) (by positivity) (by linarith),
      ← piece (t := 2*x/3) (by positivity) (by linarith), ← sum_add_distrib, mul_sum]
    apply sum_le_sum
    intro p hp
    have hlog := Real.log_nonneg (show (1:ℝ) ≤ p by
      exact_mod_cast (mem_filter.mp hp).2.1.one_le)
    by_cases h1 : (p:ℝ) ≤ x/3
    · simp only [ite_eq_left h1, ite_eq_left (show (p:ℝ) ≤ 2*x/3 by linarith)]
      calc _ = Real.log p * (2*x/3) := by ring
           _ ≤ _ := mul_le_mul_of_nonneg_left ((by linarith : 2*x/3 ≤ x-p).trans (le_max_left ..)) hlog
    · by_cases h2 : (p:ℝ) ≤ 2*x/3
      · simp only [ite_eq_right h1, ite_eq_left h2, zero_add]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left ((by linarith : x/3 ≤ x-p).trans (le_max_left ..)) hlog
      · simp only [ite_eq_right h1, ite_eq_right h2, add_zero, mul_zero]
        exact mul_nonneg hlog (le_max_right ..)
  change x^2/2 ≤ 4*∑ p ∈ A, Real.log p * max (x-p) 0
  nlinarith only [hsum, mul_nonneg hpos.le (add_le_add hlow₁.le hlow₂.le |> sub_nonneg.mpr),
    sq_nonneg x]

open ArithmeticFunction in
private theorem prescribedQuadratic_ramp_comparison {T q d : ℕ}
    (hpr : ∀ p ∈ Nat.primesLE T, (jacobiSym q p = 1 ∧ jacobiSym d p = -1) ↔ p % 4 = 1)
    (hs : ∀ n ≤ T, IsPrimePow n → jacobiSym d n = -1 → ZMod.χ₄ (n : ZMod 4) = 1) (x : ℝ) :
    let primeWeight (n : ℕ) := if n.Prime then vonMangoldt n else 0
    let R := quadraticPlusMinusRiesz T q d
    R (fun n ↦ (ZMod.χ₄ n : ℝ)*primeWeight n) x = R primeWeight x ∧
    R (fun n ↦ (ZMod.χ₄ n : ℝ)*vonMangoldt n) x = R vonMangoldt x ∧
    0 ≤ R primeWeight x ∧ R primeWeight x ≤ R vonMangoldt x ∧
    R primeWeight x = 4*∑ p ∈ (Ioc 0 T).filter (fun p ↦ p.Prime ∧ p ≡ 1 [MOD 4]),
      Real.log p * max (x-p) 0 := by
  intro W R
  let A := (Ioc 0 T).filter (fun n ↦ jacobiSym q n = 1 ∧ jacobiSym d n = -1)
  have haux (n : ℕ) (hn : n ∈ A) : (ZMod.χ₄ n:ℝ)*vonMangoldt n = vonMangoldt n := by
    by_cases h : IsPrimePow n
    · rw [hs n (mem_Ioc.mp (mem_filter.mp hn).1).2 h (mem_filter.mp hn).2.2]
      simp
    · simp [vonMangoldt_eq_zero_iff.mpr h]
  have hWp (n : ℕ) : 0 ≤ W n ∧ W n ≤ vonMangoldt n := by
    dsimp only [W]
    split_ifs <;> simp [vonMangoldt_nonneg]
  refine ⟨?_,?_,?_,?_,?_⟩
  · dsimp only [R, quadraticPlusMinusRiesz]
    congr 1
    apply sum_congr rfl
    intro n hn
    dsimp only [W]
    split_ifs
    · rw [haux n hn]
    · simp
  · dsimp only [R, quadraticPlusMinusRiesz]
    congr 1
    exact sum_congr rfl fun n hn ↦ by rw [haux n hn]
  · exact mul_nonneg (by norm_num) (sum_nonneg fun n _ ↦ mul_nonneg (hWp n).1 (le_max_right ..))
  · exact mul_le_mul_of_nonneg_left (sum_le_sum fun n _ ↦
      mul_le_mul_of_nonneg_right (hWp n).2 (le_max_right ..)) (by norm_num)
  · let B := A.filter Nat.Prime
    have hB : B = (Ioc 0 T).filter (fun p ↦ p.Prime ∧ p ≡ 1 [MOD 4]) := by
      ext p
      simp only [B,A,mem_filter,mem_Ioc]
      constructor
      · rintro ⟨⟨hT,hq⟩,hp⟩
        exact ⟨hT,hp,(hpr p (Nat.mem_primesLE.mpr ⟨hT.2,hp⟩)).mp hq⟩
      · rintro ⟨hT,hp,h⟩
        exact ⟨⟨hT,(hpr p (Nat.mem_primesLE.mpr ⟨hT.2,hp⟩)).mpr h⟩,hp⟩
    change 4*(∑ n ∈ A, W n*max (x-n) 0) = _
    rw [← hB]
    congr 1
    dsimp only [B]
    conv_rhs => rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hp : n.Prime <;> simp [W, hp, vonMangoldt_apply_prime]

open ArithmeticFunction in
/-- On every prescribed finite prime range the same nonempty (+,−) cell can have
identically zero deficit for χ₋₄ and an eventual zero deficit for the rational
principal character. This holds for both the first-prime and complete Riesz sums.
The real starting cutoff for the principal character is absolute. The two
auxiliary progressions, and hence their densities, depend on the prescribed range. -/
theorem exists_quadraticPlusMinusRiesz_nonnegative_through :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ T : ℕ, 5 ≤ T →
      let m := 8*∏ p ∈ (Nat.primesLE T).erase 2, p
      ∃ a b : ℕ, a.Coprime m ∧ b.Coprime m ∧
      Tendsto (fun Y : ℕ ↦ (((dyadicPrimesInProgression m a Y) ×ˢ
        (dyadicPrimesInProgression m b Y)).card:ℝ)*(Real.log (2*Y)/Y)^2)
          atTop (𝓝 ((m.totient:ℝ)⁻¹^2)) ∧
      ∀ Y q d : ℕ, q ∈ dyadicPrimesInProgression m a Y → d ∈ dyadicPrimesInProgression m b Y →
        q ≠ d ∧ jacobiSym q 5 = 1 ∧ jacobiSym d 5 = -1 ∧
        (let R := quadraticPlusMinusRiesz T q d
         let W (n : ℕ) := if n.Prime then vonMangoldt n else 0
         ∀ x : ℝ,
           0 ≤ R (fun n ↦ (ZMod.χ₄ n:ℝ)*W n) x ∧
           0 ≤ R (fun n ↦ (ZMod.χ₄ n:ℝ)*vonMangoldt n) x ∧
           (C ≤ x → x ≤ T → x^2/2 ≤ R W x ∧ x^2/2 ≤ R vonMangoldt x)) := by
  obtain ⟨C,hC,hbound⟩ := prescribedQuadratic_progression_ramp
  refine ⟨C,hC,?_⟩
  intro T hT m
  let P := (Nat.primesLE T).erase 2
  have hP (p : ℕ) (h : p ∈ P) : p.Prime ∧ p ≠ 2 :=
    ⟨Nat.prime_of_mem_primesLE (mem_erase.mp h).2,(mem_erase.mp h).1⟩
  obtain ⟨a,b,ha,hb,hlim,hsel⟩ := prescribedQuadraticPrimePairs P hP (fun _ ↦ false)
    (fun p ↦ decide (p % 4 = 1))
  refine ⟨a,b,ha,hb,hlim,?_⟩
  intro Y q d hq hd
  obtain ⟨_,hd8,h⟩ := hsel Y q d hq hd
  have hs : ∀ p ∈ P, jacobiSym q p = 1 ∧ jacobiSym d p = (if p%4=1 then -1 else 1) := by
    simpa using h
  have h5 : 5 ∈ P := mem_erase_of_ne_of_mem (by decide) (Nat.mem_primesLE.mpr ⟨hT,by decide⟩)
  obtain ⟨hq5,hd5⟩ := hs 5 h5
  norm_num at hd5
  refine ⟨fun hqd ↦ by rw [hqd,hd5] at hq5; norm_num at hq5,hq5,hd5,?_⟩
  intro R W x
  obtain ⟨hpr,hpow⟩ := prescribedQuadratic_chiFour_support hd8 hs
  obtain ⟨hχp,hχf,hpos,hle,he⟩ := prescribedQuadratic_ramp_comparison hpr hpow x
  refine ⟨hpos.trans_eq hχp.symm,(hpos.trans hle).trans_eq hχf.symm,?_⟩
  intro hx hxT
  have hmain := (hbound x hx T hxT).trans_eq he.symm
  exact ⟨hmain,hmain.trans hle⟩

private theorem prescribedQuadratic_modulus_gt :
    ∀ᶠ T : ℕ in atTop, 2*T^3 < 8 * ∏ p ∈ (Nat.primesLE T).erase 2, p := by
  have hprime := Nat.tendsto_log_primorial_div_atTop.eventually
    (lt_mem_nhds (by norm_num : (1/2:ℝ)<1))
  have hlog : Tendsto (fun T : ℕ ↦ Real.log T / (T:ℝ)) atTop (𝓝 0) := by
    exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hprime, hlog.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)),
    eventually_ge_atTop 2] with T hp hl ht
  have hT : 0 < (T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have h₁ := (lt_div_iff₀ hT).mp hp
  have h₂ := (div_lt_iff₀ hT).mp hl
  have hlt : Real.log ((T:ℝ)^3) < Real.log (primorial T) := by
    rw [Real.log_pow]
    norm_num
    linarith
  have hpow : T^3 < primorial T := by
    exact_mod_cast (lt_of_not_ge fun h ↦ hlt.not_ge
      (Real.log_le_log (by exact_mod_cast primorial_pos T) h))
  have h2 : 2 ∈ Nat.primesLE T := Nat.mem_primesLE.mpr ⟨ht,Nat.prime_two⟩
  rw [primorial_eq_prod_primesLE, ← mul_prod_erase _ (fun n : ℕ ↦ n) h2] at hpow
  omega

/-- At the coupled auxiliary scale Y = T³, each pair of individual progressions
used by the finite prescription contains at most one ordered pair, eventually in T. -/
theorem prescribedQuadraticPrimePairs_card_le_one_at_cubic_scale :
    ∀ᶠ T : ℕ in atTop, let m := 8*∏ p ∈ (Nat.primesLE T).erase 2, p
      ∀ a b : ℕ, ((dyadicPrimesInProgression m a (T^3)) ×ˢ
        (dyadicPrimesInProgression m b (T^3))).card ≤ 1 := by
  filter_upwards [prescribedQuadratic_modulus_gt] with T hm
  intro m a b
  have hone (c : ℕ) : (dyadicPrimesInProgression m c (T^3)).card ≤ 1 := by
    refine card_le_one.mpr fun u hu v hv ↦ ?_
    obtain ⟨hu₁,_,hu₂⟩ := mem_filter.mp hu
    obtain ⟨hv₁,_,hv₂⟩ := mem_filter.mp hv
    exact (hu₂.trans hv₂.symm).eq_of_lt_of_lt ((mem_Ioc.mp hu₁).2.trans_lt hm)
      ((mem_Ioc.mp hv₁).2.trans_lt hm)
  rw [card_product]
  simpa using Nat.mul_le_mul (hone a) (hone b)

/-- An integer upper enclosure for a signed prime sum, measured in units of
log(2)/k. The sign of each coefficient selects the rounding direction. -/
def quadraticPlusMinusPrimeLogUpper (T q d k : ℕ) (s : ℕ → ℤ) : ℤ :=
  let A := (Ioc 0 T).filter (fun n ↦ jacobiSym q n = 1 ∧ jacobiSym d n = -1)
  ∑ p ∈ A.filter Nat.Prime, (s p * ((T:ℤ)-p)) *
    (((p^k).log2 : ℤ) + if 0 ≤ s p then 1 else 0)

private theorem prescribedQuadratic_log_enclosure {p k : ℕ} (hp : 0 < p) :
    let l := (p^k).log2
    (l:ℝ)*Real.log 2 ≤ k*Real.log p ∧
      (k:ℝ)*Real.log p ≤ (l+1)*Real.log 2 := by
  intro l
  have hl : 2^l ≤ p^k := by
    dsimp only [l]
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self _ (pow_ne_zero _ hp.ne')
  have hu : p^k ≤ 2^(l+1) := by
    dsimp only [l]
    rw [Nat.log2_eq_log_two]
    exact (Nat.lt_pow_succ_log_self Nat.one_lt_two _).le
  have h₁ := Real.log_le_log (by positivity : 0 < (2:ℝ)^l)
    (by exact_mod_cast hl : (2:ℝ)^l ≤ (p:ℝ)^k)
  have h₂ := Real.log_le_log (pow_pos (by exact_mod_cast hp) _)
    (by exact_mod_cast hu : (p:ℝ)^k ≤ (2:ℝ)^(l+1))
  simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using And.intro h₁ h₂

/-- A negative integer upper enclosure certifies failure of nonnegativity at
the cutoff. Reversing the integer weights gives an enclosure for the other sign. -/
theorem quadraticPlusMinusRiesz_le_primeLogUpper (T q d k : ℕ) (s : ℕ → ℤ) :
    k * quadraticPlusMinusRiesz T q d
      (fun p ↦ if p.Prime then (s p : ℝ)*Real.log p else 0) T ≤
      (4*Real.log 2)*(quadraticPlusMinusPrimeLogUpper T q d k s : ℝ) := by
  let A := (Ioc 0 T).filter (fun n ↦ jacobiSym q n = 1 ∧ jacobiSym d n = -1)
  let P := A.filter Nat.Prime
  have he : quadraticPlusMinusRiesz T q d
      (fun p ↦ if p.Prime then (s p : ℝ)*Real.log p else 0) T =
      4*∑ p ∈ P, ((s p:ℝ)*Real.log p)*((T:ℝ)-p) := by
    unfold quadraticPlusMinusRiesz
    congr 1
    change (∑ n ∈ A, _) = _
    dsimp only [P]
    conv_rhs => rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    have hpt : p ≤ T := (mem_Ioc.mp (mem_filter.mp hp).1).2
    by_cases h : p.Prime <;> simp [h, max_eq_left (sub_nonneg.mpr (by exact_mod_cast hpt) : 0 ≤ (T:ℝ)-p)]
  rw [he]
  change (k:ℝ)*(4*∑ p ∈ P, _) ≤ (4*Real.log 2)*((∑ p ∈ P,
    (s p*((T:ℤ)-p))*(((p^k).log2:ℤ)+if 0 ≤ s p then 1 else 0) : ℤ):ℝ)
  rw [Int.cast_sum]
  simp only [mul_sum]
  refine sum_le_sum fun p hp ↦ ?_
  have hprime := (mem_filter.mp hp).2
  have hpt : p ≤ T := (mem_Ioc.mp (mem_filter.mp (mem_filter.mp hp).1).1).2
  have hg : 0 ≤ (T:ℝ)-p := sub_nonneg.mpr (by exact_mod_cast hpt)
  obtain ⟨hlo,hhi⟩ := prescribedQuadratic_log_enclosure (k := k) hprime.pos
  have hrow : (s p:ℝ)*(k*Real.log p) ≤
      (s p:ℝ)*(((((p^k).log2:ℤ)+if 0 ≤ s p then 1 else 0):ℤ):ℝ)*Real.log 2 := by
    by_cases h : 0 ≤ s p
    · simp only [ite_eq_left h, Int.cast_add, Int.cast_natCast, Int.cast_one, mul_assoc]
      exact mul_le_mul_of_nonneg_left hhi (by exact_mod_cast h)
    · simp only [ite_eq_right h, add_zero, Int.cast_natCast, mul_assoc]
      exact mul_le_mul_of_nonpos_left hlo (by exact_mod_cast (le_of_not_ge h))
  push_cast
  convert mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrow hg) (by norm_num : (0:ℝ) ≤ 4)
    using 1 <;> push_cast <;> ring

end RiemannMasullo
