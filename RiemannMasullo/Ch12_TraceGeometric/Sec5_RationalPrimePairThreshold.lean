module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5_RationalPrimePairs
import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.Analysis.SpecialFunctions.PolynomialExp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Basic.Complex.BigOperators

/-! # A positive signed contribution at the critical prime-pair radius

On a fixed subinterval where the profile stays away from zero, the prime number
theorem gives order `exp y / y` primes. Cauchy's inequality in bins of length
`D+1` counts near pairs. Polarization treats every pair in the full prime window;
Lipschitz continuity bounds the squared variation, including outside the subinterval.
-/

@[expose] public noncomputable section

namespace RiemannMasullo.RationalPrimePairs

open Finset
open scoped BigOperators ComplexConjugate

/-- Decompose the signed real contribution from a set of ordered pairs into the sum
of their endpoint energies and the squared variation of the profile. -/
private theorem weightedPair_re_eq_sub_oscillation {ι : Type*}
    (T : Finset (ι × ι)) (w : ι × ι → ℝ) (f : ι → ℂ) :
    ∑ e ∈ T, w e * (f e.1 * conj (f e.2)).re =
      (∑ e ∈ T, w e * ((‖f e.1‖ ^ 2 + ‖f e.2‖ ^ 2) / 2)) -
        ∑ e ∈ T, w e * (‖f e.1 - f e.2‖ ^ 2 / 2) := by
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro e _
  have h := Complex.normSq_sub (f e.1) (f e.2)
  simp only [Complex.normSq_eq_norm_sq] at h
  rw [← mul_sub]
  congr 1
  linarith

/-- A good subset contributes at least its total weight times the squared lower
bound for the profile. The signed contribution from the full set of pairs loses
at most half its total weight times the squared oscillation bound. -/
private theorem weightedPair_re_lower_bound {ι : Type*}
    (T U : Finset (ι × ι)) (hU : U ⊆ T) (w : ι × ι → ℝ) (f : ι → ℂ)
    (hw : ∀ e ∈ T, 0 ≤ w e) {m d : ℝ} (hm : 0 ≤ m)
    (hgood : ∀ e ∈ U, m ≤ ‖f e.1‖ ∧ m ≤ ‖f e.2‖)
    (hosc : ∀ e ∈ T, ‖f e.1 - f e.2‖ ≤ d) :
    m ^ 2 * (∑ e ∈ U, w e) - d ^ 2 / 2 * (∑ e ∈ T, w e) ≤
      ∑ e ∈ T, w e * (f e.1 * conj (f e.2)).re := by
  have hmain : m ^ 2 * (∑ e ∈ U, w e) ≤
      ∑ e ∈ T, w e * ((‖f e.1‖ ^ 2 + ‖f e.2‖ ^ 2) / 2) := by
    rw [mul_sum]
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg hU (fun e he _ ↦
      mul_nonneg (hw e he) (by positivity)))
    apply sum_le_sum
    intro e he
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ (hw e (hU he))
    have h₁ := pow_le_pow_left₀ hm (hgood e he).1 2
    have h₂ := pow_le_pow_left₀ hm (hgood e he).2 2
    linarith
  have herror : (∑ e ∈ T, w e * (‖f e.1 - f e.2‖ ^ 2 / 2)) ≤
      d ^ 2 / 2 * ∑ e ∈ T, w e := by
    rw [mul_sum]
    apply sum_le_sum
    intro e he
    rw [mul_comm (d ^ 2 / 2)]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hosc e he) 2) (by positivity))
      (hw e he)
  rw [weightedPair_re_eq_sub_oscillation]
  exact sub_le_sub hmain herror

/-- If a finite set of points lies in a finite set of boxes, its squared cardinality
is at most the number of boxes times the number of ordered pairs in the same box.
The count includes the diagonal and allows empty boxes. -/
private theorem card_sq_le_card_mul_same_box_pairs {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (B : Finset κ) (box : ι → κ) (hm : (s : Set ι).MapsTo box B) :
    s.card ^ 2 ≤ B.card * ((s ×ˢ s).filter (fun e ↦ box e.1 = box e.2)).card := by
  let T := (s ×ˢ s).filter (fun e ↦ box e.1 = box e.2)
  have hmT : (T : Set (ι × ι)).MapsTo (fun e ↦ box e.1) B :=
    fun _ he ↦ hm (mem_product.mp (mem_filter.mp he).1).1
  have hcount (b : κ) : T.filter (fun e ↦ box e.1 = b) =
      (s.filter (fun i ↦ box i = b)) ×ˢ (s.filter (fun i ↦ box i = b)) := by
    ext ⟨i,j⟩
    simp only [T, mem_filter, mem_product]
    constructor
    · rintro ⟨⟨⟨hi,hj⟩,hij⟩,hb⟩
      exact ⟨⟨hi,hb⟩,hj,hij.symm.trans hb⟩
    · rintro ⟨⟨hi,hib⟩,hj,hjb⟩
      exact ⟨⟨⟨hi,hj⟩,hib.trans hjb.symm⟩,hib⟩
  change s.card ^ 2 ≤ B.card * T.card
  rw [card_eq_sum_card_fiberwise hm, card_eq_sum_card_fiberwise hmT]
  simp_rw [hcount, card_product, ← sq]
  simpa using sum_mul_sq_le_sq_mul_sq (R := ℕ) B 1 (fun b ↦ (s.filter (fun i ↦ box i = b)).card)

/-- Ordered pairs in a common finite set of natural numbers with gap at most `r`. -/
private def natNearPairs (s : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (s ×ˢ s).filter fun e ↦ Nat.dist e.1 e.2 ≤ r

/-- Partitioning the integers up to `N` into consecutive bins of length `r + 1`
gives a lower bound on the number of ordered pairs with gap at most `r`. -/
private theorem card_sq_le_mul_natNearPairs (s : Finset ℕ) (N r : ℕ)
    (hs : ∀ i ∈ s, i ≤ N) :
    s.card ^ 2 ≤ (N / (r + 1) + 1) * (natNearPairs s r).card := by
  let box (i : ℕ) := i / (r + 1)
  let B := range (N / (r + 1) + 1)
  have hm : (s : Set ℕ).MapsTo box B :=
    fun i hi ↦ mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (hs i hi)))
  have hsub : (s ×ˢ s).filter (fun e ↦ box e.1 = box e.2) ⊆ natNearPairs s r := by
    intro ⟨i,j⟩ h
    obtain ⟨hs',hij⟩ := mem_filter.mp h
    refine mem_filter.mpr ⟨hs',?_⟩
    change i / (r + 1) = j / (r + 1) at hij
    have hi := Nat.mod_add_div i (r + 1)
    have hj := Nat.mod_add_div j (r + 1)
    rw [hij] at hi
    have hri : i % (r + 1) < r + 1 := Nat.mod_lt _ (by omega)
    have hrj : j % (r + 1) < r + 1 := Nat.mod_lt _ (by omega)
    dsimp only
    unfold Nat.dist
    omega
  simpa [B] using (card_sq_le_card_mul_same_box_pairs s B box hm).trans
    (Nat.mul_le_mul_left B.card (card_le_card hsub))

/-- The signed near-pair sum on `s` is bounded below using a good subset `A`
with lower bounds `v` and `m` for its weights and profile norms. The loss depends
on the oscillation over all near pairs in `s`, including pairs outside `A`. -/
private theorem weighted_natNearPairs_re_lower_bound (s A : Finset ℕ) (hA : A ⊆ s)
    (N r : ℕ) (hN : ∀ i ∈ A, i ≤ N) (w : ℕ → ℝ) (f : ℕ → ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i) {v m d : ℝ} (hv : 0 ≤ v) (hm : 0 ≤ m)
    (hgood : ∀ i ∈ A, v ≤ w i ∧ m ≤ ‖f i‖)
    (hosc : ∀ e ∈ natNearPairs s r, ‖f e.1 - f e.2‖ ≤ d) :
    m ^ 2 * (v ^ 2 * ((A.card : ℝ) ^ 2 / (N / (r + 1) + 1 : ℕ))) -
        d ^ 2 / 2 * (∑ e ∈ natNearPairs s r, w e.1 * w e.2) ≤
      ∑ e ∈ natNearPairs s r, w e.1 * w e.2 * (f e.1 * conj (f e.2)).re := by
  let U := natNearPairs A r
  let T := natNearPairs s r
  have hU : U ⊆ T := by
    intro e he
    obtain ⟨hp,hd⟩ := mem_filter.mp he
    obtain ⟨h₁,h₂⟩ := mem_product.mp hp
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hA h₁,hA h₂⟩,hd⟩
  have hmass : ((U.card : ℝ) * v ^ 2) ≤ ∑ e ∈ U, w e.1 * w e.2 := by
    calc
      _ = ∑ _e ∈ U, v ^ 2 := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro e he
        obtain ⟨h₁,h₂⟩ := mem_product.mp (mem_filter.mp he).1
        rw [sq]
        exact mul_le_mul (hgood _ h₁).1 (hgood _ h₂).1 hv (hw _ (hA h₁))
  have hc : (A.card : ℝ) ^ 2 ≤ (N / (r + 1) + 1 : ℕ) * (U.card : ℝ) := by
    exact_mod_cast card_sq_le_mul_natNearPairs A N r hN
  have hden : (0 : ℝ) < (N / (r + 1) + 1 : ℕ) := by positivity
  have hcount : (A.card : ℝ) ^ 2 / (N / (r + 1) + 1 : ℕ) ≤ U.card :=
    (div_le_iff₀ hden).mpr (by simpa only [mul_comm (U.card : ℝ)] using hc)
  have hgoodmass := (mul_le_mul_of_nonneg_left hcount (sq_nonneg v)).trans
    (by simpa only [mul_comm (v ^ 2)] using hmass)
  apply le_trans (sub_le_sub_right (mul_le_mul_of_nonneg_left hgoodmass (sq_nonneg m)) _)
  apply weightedPair_re_lower_bound T U hU (fun e ↦ w e.1 * w e.2) f _ hm _ hosc
  · intro e he
    obtain ⟨h₁,h₂⟩ := mem_product.mp (mem_filter.mp he).1
    exact mul_nonneg (hw _ h₁) (hw _ h₂)
  · intro e he
    obtain ⟨h₁,h₂⟩ := mem_product.mp (mem_filter.mp he).1
    exact ⟨(hgood _ h₁).2, (hgood _ h₂).2⟩

end RiemannMasullo.RationalPrimePairs

namespace RiemannMasullo.RationalPrimePairs

open Finset
open scoped BigOperators ComplexConjugate NNReal

private theorem window_bounds {y : ℝ} {p : ℕ} (hp : p ∈ window y) :
    p ≤ ⌊Real.exp (y + 4)⌋₊ ∧ Real.exp y ≤ (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp (y + 4) ∧ Real.log p - y ∈ Set.Icc (2 : ℝ) 4 := by
  rw [window, mem_filter, mem_range] at hp
  have hN := Nat.le_of_lt_succ hp.1
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.2.1.pos
  have hu := (Nat.cast_le.mpr hN).trans (Nat.floor_le (Real.exp_pos (y + 4)).le)
  have hlog₁ := (Real.le_log_iff_exp_le hp₀).mpr hp.2.2
  have hlog₂ := (Real.log_le_iff_le_exp hp₀).mpr hu
  exact ⟨hN, (Real.exp_le_exp.mpr (show y ≤ y + 2 by linarith)).trans hp.2.2, hu,
    by constructor <;> linarith⟩

private theorem log_nat_dist_le {X : ℝ} (hX : 0 < X) {p q D : ℕ}
    (hp : X ≤ p) (hq : X ≤ q) (hD : Nat.dist p q ≤ D) :
    |Real.log p - Real.log q| ≤ (D : ℝ) / X := by
  have step {a b : ℕ} (ha : X ≤ a) (hab : a ≤ b) (hd : Nat.dist a b ≤ D) :
      Real.log b - Real.log a ≤ (D : ℝ) / X := by
    have ha₀ := hX.trans_le ha
    have hab' : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
    have hb₀ := ha₀.trans_le hab'
    rw [Nat.dist_eq_sub_of_le hab] at hd
    have hsub : (b : ℝ) - a ≤ D := by
      simpa only [Nat.cast_sub hab] using (Nat.cast_le.mpr hd : ((b - a : ℕ) : ℝ) ≤ D)
    rw [← Real.log_div hb₀.ne' ha₀.ne']
    calc
      _ ≤ (b : ℝ) / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb₀ ha₀)
      _ = ((b : ℝ) - a) / a := by rw [sub_div, div_self ha₀.ne']
      _ ≤ ((b : ℝ) - a) / X := div_le_div_of_nonneg_left (sub_nonneg.mpr hab') hX ha
      _ ≤ _ := div_le_div_of_nonneg_right hsub hX.le
  rcases le_total p q with hpq | hqp
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr
      (Real.log_le_log (hX.trans_le hp) (Nat.cast_le.mpr hpq)))]
    exact step hp hpq hD
  · rw [abs_of_nonneg (sub_nonneg.mpr
      (Real.log_le_log (hX.trans_le hq) (Nat.cast_le.mpr hqp)))]
    exact step hq hqp (by rwa [Nat.dist_comm])

private theorem sum_natNearPairs {M : Type*} [AddCommMonoid M] (g : ℕ × ℕ → M)
    (s : Finset ℕ) (D : ℕ) :
    ∑ e ∈ natNearPairs s D, g e =
      ∑ p ∈ s, ∑ q ∈ s.filter (fun q ↦ Nat.dist p q ≤ D), g (p, q) := by
  classical
  simp only [natNearPairs, sum_filter, sum_product]

/-- Signed lower bound on the actual rational prime-pair sum. The count of good
primes enters only through the cardinality of `A`; the oscillation is bounded on
the full common window. The integer radius may be zero. -/
theorem nearReal_lower_bound (H : ℝ → ℂ) {L : ℝ≥0}
    (hL : LipschitzOnWith L H (Set.Icc (2 : ℝ) 4)) {y m : ℝ} (hy : 0 ≤ y) (hm : 0 ≤ m)
    (D : ℕ) (A : Finset ℕ) (hA : A ⊆ window y)
    (hgood : ∀ p ∈ A, m ≤ ‖H (Real.log p - y)‖) :
    m ^ 2 * ((y + 2) / Real.sqrt (Real.exp (y + 4))) ^ 2 * (A.card : ℝ) ^ 2 /
        (⌊Real.exp (y + 4)⌋₊ / (D + 1) + 1 : ℕ) -
      ((L : ℝ) * ((D : ℝ) / Real.exp y)) ^ 2 / 2 *
        ((Real.exp 4 + 1) * (2 * (D : ℝ) + 1) * (y + 4) ^ 2) ≤ nearReal H y D := by
  let w (p : ℕ) := Real.log p / Real.sqrt p
  let f (p : ℕ) := H (Real.log p - y)
  let v := (y + 2) / Real.sqrt (Real.exp (y + 4))
  let d := (L : ℝ) * ((D : ℝ) / Real.exp y)
  let T := natNearPairs (window y) D
  have hv : 0 ≤ v := div_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hweight (p : ℕ) (hp : p ∈ window y) : v ≤ w p := by
    obtain ⟨_,hpx,hu,hlog,_⟩ := window_bounds hp
    exact div_le_div₀ (by linarith) (by linarith) (Real.sqrt_pos.mpr ((Real.exp_pos y).trans_le hpx))
      (Real.sqrt_le_sqrt hu)
  have hw (p : ℕ) (hp : p ∈ window y) : 0 ≤ w p := hv.trans (hweight p hp)
  have hosc (e : ℕ × ℕ) (he : e ∈ T) : ‖f e.1 - f e.2‖ ≤ d := by
    obtain ⟨hmem,hgap⟩ := mem_filter.mp he
    obtain ⟨hp,hq⟩ := mem_product.mp hmem
    obtain ⟨_,hpx,_,hpv⟩ := window_bounds hp
    obtain ⟨_,hqx,_,hqv⟩ := window_bounds hq
    have hl := hL.dist_le_mul _ hpv _ hqv
    rw [dist_eq_norm, Real.dist_eq, sub_sub_sub_cancel_right] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left (log_nat_dist_le (Real.exp_pos y) hpx hqx hgap)
      L.coe_nonneg)
  have hmass : (∑ e ∈ T, w e.1 * w e.2) ≤
      (Real.exp 4 + 1) * (2 * (D : ℝ) + 1) * (y + 4) ^ 2 := by
    have hnorm (p : ℕ) (hp : p ∈ window y) :
        ‖weight (fun _ ↦ 1) y p‖ = w p := by
      simpa only [weight, norm_smul, Real.norm_eq_abs, norm_one, mul_one, w] using
        abs_of_nonneg (hw p hp)
    calc
      _ = nearAbs (fun _ ↦ 1) y D := by
        rw [show T = natNearPairs (window y) D from rfl, sum_natNearPairs, nearAbs]
        apply sum_congr rfl
        intro p hp
        apply sum_congr rfl
        intro q hq
        simp only [hnorm p hp, hnorm q (mem_filter.mp hq).1]
      _ ≤ _ := by simpa using nearAbs_le (fun _ ↦ (1 : ℂ)) hy zero_le_one (by simp) D
  have hre : (∑ e ∈ T, w e.1 * w e.2 * (f e.1 * conj (f e.2)).re) = nearReal H y D := by
    rw [show T = natNearPairs (window y) D from rfl, sum_natNearPairs, nearReal]
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro q _
    have h : weight H y p * conj (weight H y q) =
        ((w p * w q : ℝ) : ℂ) * (f p * conj (f q)) := by
      simp only [weight, w, f, Complex.real_smul, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
      ring
    rw [h, Complex.re_ofReal_mul]
  have hlo := weighted_natNearPairs_re_lower_bound (window y) A hA ⌊Real.exp (y + 4)⌋₊ D
    (fun p hp ↦ (window_bounds (hA hp)).1) w f hw hv hm
    (fun p hp ↦ ⟨hweight p (hA hp), hgood p hp⟩) hosc
  change m ^ 2 * v ^ 2 * (A.card : ℝ) ^ 2 / _ - d ^ 2 / 2 * _ ≤ _
  rw [← hre]
  apply le_trans _ hlo
  apply sub_le_sub _ (mul_le_mul_of_nonneg_left hmass (by positivity))
  exact le_of_eq (by ring)

end RiemannMasullo.RationalPrimePairs

namespace RiemannMasullo.RationalPrimePairs

open Filter
open scoped BigOperators Topology

private theorem tendsto_theta_mul_div {d : ℝ} (hd : 0 < d) :
    Tendsto (fun x : ℝ ↦ Chebyshev.theta (d * x) / x) atTop (𝓝 d) := by
  have h := (Chebyshev.tendsto_theta_div_atTop.comp (tendsto_id.const_mul_atTop hd)).mul_const d
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp
  field_simp [hx.ne', hd.ne']

private theorem filter_prime_Ioc_eq_sdiff (l u : ℕ) :
    (Finset.Ioc l u).filter Nat.Prime = Nat.primesLE u \ Nat.primesLE l := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, Nat.mem_primesLE]
  grind

/-- In a fixed multiplicative interval, the sum of the prime logarithms divided by the
scale tends to the width of the interval. -/
private theorem tendsto_sum_log_prime_mul_Ioc_div {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun x : ℝ ↦ (∑ p ∈ (Finset.Ioc ⌊a * x⌋₊ ⌊b * x⌋₊).filter Nat.Prime,
      Real.log (p : ℝ)) / x) atTop (𝓝 (b - a)) := by
  refine ((tendsto_theta_mul_div (ha.trans hab)).sub (tendsto_theta_mul_div ha)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hsub := Nat.primesLE_mono (Nat.floor_mono (mul_le_mul_of_nonneg_right hab.le hx))
  simp only [filter_prime_Ioc_eq_sdiff, Finset.sum_sdiff_eq_sub hsub, Chebyshev.theta_eq_sum_primesLE,
    sub_div]

/-- The number of primes in the interval `(a*x,b*x]` eventually exceeds
`(b-a) * x / (4 * log x)` whenever `0 < a < b`. -/
private theorem eventually_mul_div_log_le_card_prime_mul_Ioc {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, (b - a) / 4 * x / Real.log x ≤
      (((Finset.Ioc ⌊a * x⌋₊ ⌊b * x⌋₊).filter Nat.Prime).card : ℝ) := by
  have htheta := (tendsto_sum_log_prime_mul_Ioc_div ha hab).eventually_const_lt
    (show (b - a) / 2 < b - a by linarith)
  filter_upwards [htheta, eventually_gt_atTop (1 : ℝ), eventually_ge_atTop b] with x hmass hx hbx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hb : 0 < b := ha.trans hab
  have hlog : Real.log (b * x) ≤ 2 * Real.log x := by
    rw [Real.log_mul hb.ne' hx0.ne']
    linarith [Real.log_le_log hb hbx]
  let s := (Finset.Ioc ⌊a * x⌋₊ ⌊b * x⌋₊).filter Nat.Prime
  have hbound : ∑ p ∈ s, Real.log (p : ℝ) ≤ (s.card : ℝ) * (2 * Real.log x) := by
    calc
      _ ≤ ∑ _p ∈ s, (2 * Real.log x) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpI, hprime⟩ := Finset.mem_filter.mp hp
        have hle : (p : ℝ) ≤ b * x :=
          (Nat.le_floor_iff (mul_nonneg hb.le hx0.le)).mp (Finset.mem_Ioc.mp hpI).2
        exact (Real.log_le_log (by exact_mod_cast hprime.pos) hle).trans hlog
      _ = _ := by simp
  have hlower : (b - a) / 2 * x < ∑ p ∈ s, Real.log (p : ℝ) := (lt_div_iff₀ hx0).mp hmass
  apply (div_le_iff₀ (Real.log_pos hx)).mpr
  change (b - a) / 4 * x ≤ (s.card : ℝ) * Real.log x
  nlinarith [hlower.trans_le hbound]

end RiemannMasullo.RationalPrimePairs

namespace RiemannMasullo.RationalPrimePairs

open Filter
open scoped Topology

/-- For `X = exp y` and `h = exp (2*c*y)`, every polynomial multiple of `(h/X)²`
tends to zero below the relative-width endpoint `c = 1/2`. -/
private theorem tendsto_polynomial_mul_critical_sq_ratio (P : Polynomial ℝ) {c : ℝ}
    (hc : c < 1 / 2) :
    Tendsto (fun y : ℝ ↦ P.eval y * Real.exp (2 * c * y) ^ 2 / Real.exp y ^ 2)
      atTop (𝓝 0) := by
  let b := 2 - 4 * c
  have hb : 0 < b := by dsimp [b]; linarith
  let Q := P.comp (Polynomial.C b⁻¹ * Polynomial.X)
  have hy : Tendsto (fun y : ℝ ↦ b * y) atTop atTop := tendsto_id.const_mul_atTop hb
  refine (Q.tendsto_div_exp_atTop.comp hy).congr fun y ↦ ?_
  change Q.eval (b * y) / Real.exp (b * y) = _
  have heval : Q.eval (b * y) = P.eval y := by
    simp [Q, Polynomial.eval_comp, hb.ne']
  rw [heval, mul_div_assoc]
  have hexp : Real.exp (2 * c * y) ^ 2 / Real.exp y ^ 2 = (Real.exp (b * y))⁻¹ := by
    rw [sq, sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_sub, ← Real.exp_neg]
    congr 1
    dsimp [b]
    ring
  rw [hexp, div_eq_mul_inv]

/-- The quadratic oscillation bound used on a translated compact support. -/
private theorem tendsto_shifted_sq_mul_critical_sq_ratio (K d : ℝ) {c : ℝ} (hc : c < 1 / 2) :
    Tendsto (fun y : ℝ ↦ K * (y + d) ^ 2 * Real.exp (2 * c * y) ^ 2 / Real.exp y ^ 2)
      atTop (𝓝 0) := by
  refine (tendsto_polynomial_mul_critical_sq_ratio
    (Polynomial.C K * (Polynomial.X + Polynomial.C d) ^ 2) hc).congr fun y ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

/-- Covering the integers through `⌊B*X⌋` by bins of `⌊h⌋+1` successive integers
uses at most `(B+1)*X/h` bins whenever `0 < h ≤ X`. -/
private theorem floor_box_count_le {B X h : ℝ} (hB : 0 ≤ B) (hh : 0 < h) (hhX : h ≤ X) :
    ((⌊B * X⌋₊ / (⌊h⌋₊ + 1) + 1 : ℕ) : ℝ) ≤ (B + 1) * X / h := by
  have hX : 0 ≤ X := hh.le.trans hhX
  calc
    _ ≤ (⌊B * X⌋₊ : ℝ) / ((⌊h⌋₊ : ℝ) + 1) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using add_le_add_left
        (Nat.cast_div_le (α := ℝ) (m := ⌊B * X⌋₊) (n := ⌊h⌋₊ + 1)) 1
    _ ≤ B * X / h + 1 := by
      exact add_le_add_left (div_le_div₀ (by positivity) (Nat.floor_le (mul_nonneg hB hX))
        hh (Nat.lt_floor_add_one h).le) 1
    _ ≤ _ := by
      apply (le_div_iff₀ hh).mpr
      rw [add_mul, div_mul_cancel₀ _ hh.ne', one_mul]
      nlinarith

/-- A lower count `n ≥ κX/y` turns the same-bin Cauchy term with weight
`y/√(B*X)` into an explicit positive multiple of `h`. -/
private theorem critical_good_mass_lower {B X h y κ : ℝ} {n : ℕ}
    (hB : 0 < B) (hh : 0 < h) (hhX : h ≤ X) (hy : 0 < y)
    (hκ : 0 ≤ κ) (hn : κ * X / y ≤ (n : ℝ)) :
    κ ^ 2 / (B * (B + 1)) * h ≤
      (y / Real.sqrt (B * X)) ^ 2 * ((n : ℝ) ^ 2 / (⌊B * X⌋₊ / (⌊h⌋₊ + 1) + 1 : ℕ)) := by
  have hX : 0 < X := hh.trans_le hhX
  have hbox : (0 : ℝ) < (⌊B * X⌋₊ / (⌊h⌋₊ + 1) + 1 : ℕ) := by positivity
  have hnum := pow_le_pow_left₀ (div_nonneg (mul_nonneg hκ hX.le) hy.le) hn 2
  have hratio := div_le_div₀ (sq_nonneg (n : ℝ)) hnum hbox (floor_box_count_le hB.le hh hhX)
  calc
    _ = (y / Real.sqrt (B * X)) ^ 2 * ((κ * X / y) ^ 2 / ((B + 1) * X / h)) := by
      rw [div_pow, Real.sq_sqrt (mul_nonneg hB.le hX.le)]
      field_simp [hB.ne', hX.ne', hy.ne', hh.ne', (show B + 1 ≠ 0 by positivity)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hratio (sq_nonneg _)

end RiemannMasullo.RationalPrimePairs

namespace RiemannMasullo.RationalPrimePairs

open Filter Set
open scoped Topology

/-- The primes in the good subinterval whose fixed endpoints are logarithmic. -/
private def goodWindow (u v y : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.exp u * Real.exp y⌋₊ ⌊Real.exp v * Real.exp y⌋₊).filter Nat.Prime

private theorem goodWindow_mem {u v y : ℝ} (hu : 2 ≤ u) (hv : v ≤ 4)
    {p : ℕ} (hp : p ∈ goodWindow u v y) :
    p ∈ window y ∧ Real.log (p : ℝ) - y ∈ Icc u v := by
  obtain ⟨hi, hprime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hl,hr⟩ := Finset.mem_Ioc.mp hi
  have hl' := (Nat.floor_lt (by positivity : 0 ≤ Real.exp u * Real.exp y)).mp hl
  have hr' := (Nat.le_floor_iff (by positivity : 0 ≤ Real.exp v * Real.exp y)).mp hr
  rw [← Real.exp_add] at hl' hr'
  have pp : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hu' := (Real.lt_log_iff_exp_lt pp).mpr hl'
  have hv' := (Real.log_le_iff_le_exp pp).mpr hr'
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ?_), hprime, ?_⟩,
    ⟨by linarith, by linarith⟩⟩
  · exact (Nat.le_floor_iff (Real.exp_pos _).le).mpr (hr'.trans (Real.exp_le_exp.mpr (by linarith)))
  · exact (Real.exp_le_exp.mpr (by linarith : y+2 ≤ u+y)).trans hl'.le

/-- The ordinary prime number theorem supplies the eventual cardinality of the actual good window. -/
private theorem eventually_goodWindow_count {u v : ℝ} (huv : u < v) :
    ∀ᶠ y : ℝ in atTop, (Real.exp v-Real.exp u)/4 * Real.exp y/y ≤
      ((goodWindow u v y).card : ℝ) := by
  have h := Real.tendsto_exp_atTop.eventually
    (eventually_mul_div_log_le_card_prime_mul_Ioc (Real.exp_pos u)
      (Real.exp_lt_exp.mpr huv))
  simpa [goodWindow] using h

/-- An explicit normalized bound for the loss in the polarization estimate. -/
private theorem critical_oscillation_budget {L B y X h : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hX : 0 < X) (hh : 1 ≤ h) :
    (L * ((⌊h⌋₊ : ℝ)/X))^2/2 * ((B+1)*(2*(⌊h⌋₊ : ℝ)+1)*(y+4)^2) ≤
      ((3/2)*L^2*(B+1)*(y+4)^2*h^2/X^2)*h := by
  have hr : (⌊h⌋₊ : ℝ) ≤ h := Nat.floor_le (by linarith)
  have hr' : 2*(⌊h⌋₊ : ℝ)+1 ≤ 3*h := by linarith
  calc
    _ ≤ (L*(h/X))^2/2 * ((B+1)*(3*h)*(y+4)^2) := by gcongr
    _ = _ := by ring

end RiemannMasullo.RationalPrimePairs

namespace RiemannMasullo.RationalPrimePairs

open Filter Set
open scoped Topology NNReal

/-- A lower-bound coefficient supplied by a fixed good subinterval. It is independent of
the radius exponent and the Lipschitz constant. -/
def intervalLowerConstant (u v m : ℝ) : ℝ :=
  m ^ 2 * (((Real.exp v - Real.exp u) / 4) ^ 2 / (Real.exp 4 * (Real.exp 4 + 1))) / 2

theorem intervalLowerConstant_pos {u v m : ℝ} (huv : u < v) (hm : 0 < m) :
    0 < intervalLowerConstant u v m := by
  have h := sub_pos.mpr (Real.exp_lt_exp.mpr huv)
  unfold intervalLowerConstant
  positivity

/-- At the critical radius the signed near-prime contribution eventually dominates
the explicit good-interval coefficient times the radius. -/
theorem eventually_critical_nearReal_of_subinterval (H : ℝ → ℂ) {L : ℝ≥0}
    (hL : LipschitzOnWith L H (Icc (2 : ℝ) 4)) {u v m : ℝ}
    (hu : 2 ≤ u) (huv : u < v) (hv : v ≤ 4) (hm : 0 < m)
    (hgood : ∀ x ∈ Icc u v, m ≤ ‖H x‖) {c : ℝ} (hc : 0 < c) (hc' : c < 1/2) :
    ∀ᶠ y : ℝ in atTop, intervalLowerConstant u v m * Real.exp (2*c*y) ≤
      nearReal H y ⌊Real.exp (2*c*y)⌋₊ := by
  let B : ℝ := Real.exp 4
  let κ : ℝ := (Real.exp v-Real.exp u)/4
  let M := m^2 * (κ^2 / (B*(B+1)))
  let K := (3/2 : ℝ) * (L:ℝ)^2 * (B+1)
  have hB : 0 < B := Real.exp_pos _
  have hκ : 0 < κ := div_pos (sub_pos.mpr (Real.exp_lt_exp.mpr huv)) (by norm_num)
  have hM : 0 < M := by dsimp [M]; positivity
  change ∀ᶠ y : ℝ in atTop, M/2 * Real.exp (2*c*y) ≤ nearReal H y ⌊Real.exp (2*c*y)⌋₊
  have he := (tendsto_shifted_sq_mul_critical_sq_ratio K 4 hc').eventually_lt_const
    (show 0 < M/2 by positivity)
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_goodWindow_count huv, he] with y hy hn he
  let X := Real.exp y
  let h := Real.exp (2*c*y)
  let A := goodWindow u v y
  let D := ⌊h⌋₊
  have hX : 0 < X := Real.exp_pos _
  have hh : 0 < h := Real.exp_pos _
  have h1 : 1 ≤ h := Real.one_le_exp (by positivity)
  have hhX : h ≤ X := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (show 0 ≤ 1-2*c by linarith) hy.le])
  have hcut : Real.exp (y+4) = B*X := by rw [Real.exp_add, mul_comm]
  have hcount : κ*X/y ≤ (A.card : ℝ) := hn
  have hmass := critical_good_mass_lower hB hh hhX hy hκ.le hcount
  have hv' : (y / Real.sqrt (B*X)) ^ 2 ≤ ((y+2)/Real.sqrt (B*X))^2 := by
    gcongr; linarith
  have hmain : M*h ≤ m^2 * ((y+2)/Real.sqrt (B*X))^2 * (A.card:ℝ)^2 /
      (⌊B*X⌋₊ / (D+1) + 1 : ℕ) := by
    calc
      _ = m^2*(κ^2 / (B*(B+1))*h) := by dsimp [M]; ring
      _ ≤ m^2*((y/Real.sqrt (B*X))^2 * ((A.card:ℝ)^2 / (⌊B*X⌋₊ / (D+1) + 1 : ℕ))) :=
        mul_le_mul_of_nonneg_left hmass (sq_nonneg _)
      _ ≤ m^2*(((y+2)/Real.sqrt (B*X))^2 * ((A.card:ℝ)^2 / (⌊B*X⌋₊ / (D+1) + 1 : ℕ))) := by gcongr
      _ = _ := by ring
  have herror := (critical_oscillation_budget (L := (L:ℝ)) L.coe_nonneg hB.le hX h1 (y := y)).trans
    (mul_le_mul_of_nonneg_right he.le hh.le)
  have htotal := nearReal_lower_bound H hL hy.le hm.le D A
    (fun _ hp ↦ (goodWindow_mem hu hv hp).1) (fun _ hp ↦ hgood _ (goodWindow_mem hu hv hp).2)
  rw [hcut] at htotal
  apply le_trans _ htotal
  calc
    _ = M*h - (M/2)*h := by ring
    _ ≤ _ := sub_le_sub hmain herror

/-- One positive lower-bound coefficient works simultaneously for every `0 < c < 1/2`.
The starting point of the estimate may depend on `c`. -/
theorem exists_pos_eventually_critical_nearReal (H : ℝ → ℂ) {L : ℝ≥0}
    (hL : LipschitzOnWith L H (Icc (2 : ℝ) 4)) {u v m : ℝ}
    (hu : 2 ≤ u) (huv : u < v) (hv : v ≤ 4) (hm : 0 < m)
    (hgood : ∀ x ∈ Icc u v, m ≤ ‖H x‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℝ, 0 < c → c < 1/2 →
      ∀ᶠ y : ℝ in atTop, δ * Real.exp (2*c*y) ≤ nearReal H y ⌊Real.exp (2*c*y)⌋₊ :=
  ⟨intervalLowerConstant u v m, intervalLowerConstant_pos huv hm,
    fun _ hc hc' ↦ eventually_critical_nearReal_of_subinterval H hL hu huv hv hm hgood hc hc'⟩

end RiemannMasullo.RationalPrimePairs
