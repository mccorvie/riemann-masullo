module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Nat.GCD.Basic

/-!
# The additive large sieve

A finite Fourier sum supported on the integer interval [L,U] has squared sample norm
at most (1/δ + π(U−L)) times its coefficient energy on any δ-separated set modulo one.
For reduced fractions of denominator at most Q this gives Q² + π(U−L). The integrated
version allows arbitrary square-integrable coefficient functions and a common measure.

The proof samples a nonnegative periodic function on disjoint intervals and pays only
its negative variation. Centering the Fourier frequencies at the midpoint of [L,U]
and applying Parseval to the sum and its derivative gives the stated constant. These
estimates apply to the rational character measurements of Theorem 12.5.1.1, pp. 519–520.
-/

open Set Finset Complex MeasureTheory Filter Function
open scoped ComplexConjugate Topology

public noncomputable section

namespace AdditiveLargeSieve

private theorem interval_value_le {g d m : ℝ → ℝ} (hd : Continuous d) (hm : Continuous m)
    (hm₀ : ∀ t, 0 ≤ m t) (hmD : ∀ t, -(d t) ≤ m t) (hD : ∀ t, HasDerivAt g (d t) t)
    (x : ℝ) {r : ℝ} (hr : 0 < r) :
    g x ≤ (∫ t in x..x + r, g t) / r + ∫ t in x..x + r, m t := by
  let J := ∫ t in x..x + r, m t
  have hg : Continuous g := continuous_iff_continuousAt.mpr fun t ↦ (hD t).continuousAt
  have hx : x ≤ x + r := by linarith
  have h (t : ℝ) (ht : t ∈ Icc x (x + r)) : g x ≤ g t + J := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x) (b := t)
      (fun u _ ↦ hD u) (hd.intervalIntegrable _ _)
    have h₁ := intervalIntegral.integral_mono (μ := volume) ht.1
      (hd.neg.intervalIntegrable _ _) (hm.intervalIntegrable _ _) hmD
    simp only [Pi.neg_apply] at h₁
    rw [intervalIntegral.integral_neg, he] at h₁
    have h₂ := intervalIntegral.integral_mono_interval (μ := volume) (a := x) (b := t) (c := x) (d := x + r)
      (f := m) le_rfl ht.1 ht.2 (ae_of_all _ hm₀) (hm.intervalIntegrable _ _)
    dsimp [J]
    linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) hx (continuous_const.intervalIntegrable _ _)
    ((hg.add continuous_const).intervalIntegrable _ _) h
  change (∫ _ in x..x + r, g x) ≤ ∫ t in x..x + r, g t + J at hi
  rw [intervalIntegral.integral_add (hg.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul,
    smul_eq_mul] at hi
  change g x ≤ _ / r + J
  apply (sub_le_iff_le_add).mp
  apply (le_div_iff₀ hr).mpr
  linarith

private theorem sum_disjoint_interval_integrals {ι : Type*} (S : Finset ι) (x : ι → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hbox : ∀ i ∈ S, 0 ≤ x i ∧ x i + r ≤ 1)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → r ≤ |x i - x j|)
    {f : ℝ → ℝ} (hf : Continuous f) (hn : ∀ z, 0 ≤ f z) :
    (∑ i ∈ S, ∫ u in x i..x i + r, f u) ≤ ∫ u in (0 : ℝ)..1, f u := by
  let J (i : ι) := Ioc (x i) (x i + r)
  have hdis : Set.Pairwise (↑S) (Disjoint on J) := by
    intro i hi j hj hn'
    rcases le_abs.mp (hsep i hi j hj hn') with h | h
    · exact (Set.Ioc_disjoint_Ioc_of_le (by linarith : x j + r ≤ x i)).symm
    · exact Set.Ioc_disjoint_Ioc_of_le (by linarith : x i + r ≤ x j)
  have hun : (⋃ i ∈ S, J i) ⊆ Ioc (0 : ℝ) 1 := by
    intro z hz
    obtain ⟨i, hi, h⟩ := mem_iUnion₂.mp hz
    exact ⟨(hbox i hi).1.trans_lt h.1, h.2.trans (hbox i hi).2⟩
  simp_rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  calc
    _ = ∑ i ∈ S, ∫ u in J i, f u := Finset.sum_congr rfl (fun i _ ↦ intervalIntegral.integral_of_le (by linarith))
    _ = ∫ u in ⋃ i ∈ S, J i, f u := (integral_biUnion_finset S (fun _ _ ↦ measurableSet_Ioc) hdis (fun _ _ ↦ hf.integrableOn_Ioc)).symm
    _ ≤ _ := setIntegral_mono_set hf.integrableOn_Ioc (ae_of_all _ hn) hun.eventuallySubset

private theorem sum_le_integral_add_majorant {ι : Type*} (S : Finset ι) (x : ι → ℝ) {r : ℝ} (hr : 0 < r)
    (hbox : ∀ i ∈ S, 0 ≤ x i ∧ x i + r ≤ 1)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → r ≤ |x i - x j|)
    {g d m : ℝ → ℝ} (hd : Continuous d) (hm : Continuous m)
    (hm₀ : ∀ t, 0 ≤ m t) (hmD : ∀ t, -(d t) ≤ m t) (hD : ∀ t, HasDerivAt g (d t) t) (hn : ∀ t, 0 ≤ g t) :
    ∑ i ∈ S, g (x i) ≤ (∫ t in (0 : ℝ)..1, g t) / r + ∫ t in (0 : ℝ)..1, m t := by
  have hg : Continuous g := continuous_iff_continuousAt.mpr fun t ↦ (hD t).continuousAt
  calc
    _ ≤ ∑ i ∈ S, ((∫ t in x i..x i + r, g t) / r + ∫ t in x i..x i + r, m t) :=
      Finset.sum_le_sum fun i _ ↦ interval_value_le hd hm hm₀ hmD hD (x i) hr
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div]
      exact add_le_add (div_le_div_of_nonneg_right (sum_disjoint_interval_integrals S x hr.le hbox hsep hg hn) hr.le)
        (sum_disjoint_interval_integrals S x hr.le hbox hsep hm hm₀)

private theorem sum_le_integral_add_variation {ι : Type*} (S : Finset ι) (x : ι → ℝ) {r : ℝ} (hr : 0 < r)
    (hbox : ∀ i ∈ S, 0 ≤ x i ∧ x i + r ≤ 1)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → r ≤ |x i - x j|)
    {g d : ℝ → ℝ} (hd : Continuous d) (hD : ∀ t, HasDerivAt g (d t) t)
    (hn : ∀ t, 0 ≤ g t) (he : g 1 = g 0) :
    ∑ i ∈ S, g (x i) ≤ (∫ t in (0 : ℝ)..1, g t) / r + (∫ t in (0 : ℝ)..1, |d t|) / 2 := by
  let m (t : ℝ) := (|d t| - d t) / 2
  have hm : Continuous m := (hd.abs.sub hd).div_const _
  have hmn (t : ℝ) : 0 ≤ m t := by dsimp [m]; linarith [le_abs_self (d t)]
  have hmd (t : ℝ) : -(d t) ≤ m t := by dsimp [m]; linarith [neg_abs_le (d t)]
  have hInt : (∫ t in (0 : ℝ)..1, d t) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hD t) (hd.intervalIntegrable _ _), he, sub_self]
  have hmInt : (∫ t in (0 : ℝ)..1, m t) = (∫ t in (0 : ℝ)..1, |d t|) / 2 := by
    simp only [m, div_eq_mul_inv, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub (hd.abs.intervalIntegrable _ _) (hd.intervalIntegrable _ _), hInt, sub_zero]
  rw [← hmInt]
  exact sum_le_integral_add_majorant S x hr hbox hsep hd hm hmn hmd hD hn

/-- The finite Fourier sum with complex coefficients evaluated at a real point of the unit circle. -/
@[expose] def fourierSum (S : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ S, a n * Complex.exp ((n : ℂ) * (2 * Real.pi * I) * x)

private def angularFrequency (t : ℝ) : ℂ := (t : ℂ) * (2 * Real.pi * I)

private def fourierWave (t x : ℝ) : ℂ := Complex.exp (angularFrequency t * x)

private def centeredSum (S : Finset ℕ) (c : ℝ) (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ S, a n * fourierWave ((n : ℝ) - c) x

private theorem centeredSum_zero (S : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) :
    centeredSum S 0 a x = fourierSum S a x := by simp only [centeredSum, sub_zero, fourierWave, angularFrequency, Complex.ofReal_natCast, fourierSum]

private theorem wave_mul_conj (m n : ℕ) (c x : ℝ) :
    fourierWave ((m : ℝ) - c) x * conj (fourierWave ((n : ℝ) - c) x) = fourierWave ((m : ℝ) - n) x := by
  simp only [fourierWave, angularFrequency, ← Complex.exp_conj, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    ← Complex.exp_add, Complex.ofReal_sub, Complex.ofReal_natCast, map_sub, map_natCast]
  congr 1
  ring

private theorem integral_wave (m n : ℕ) :
    (∫ x in (0 : ℝ)..1, fourierWave ((m : ℝ) - n) x) = if m = n then (1 : ℂ) else 0 := by
  by_cases h : m = n
  · simp [h, fourierWave, angularFrequency]
  · rw [ite_eq_right h]
    have hs : angularFrequency ((m : ℝ) - n) ≠ 0 := by
      unfold angularFrequency
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast h)))
        (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    unfold fourierWave
    rw [integral_exp_mul_complex hs]
    have he : Complex.exp (angularFrequency ((m : ℝ) - n)) = 1 := by
      convert Complex.exp_int_mul_two_pi_mul_I ((m : ℤ) - n) using 2
      simp [angularFrequency]
    simp [he]

private theorem centeredSum_parseval (S : Finset ℕ) (c : ℝ) (a : ℕ → ℂ) :
    (∫ x in (0 : ℝ)..1, ‖centeredSum S c a x‖ ^ 2) = ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal, Complex.ofReal_sum]
  have hn (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by rw [Complex.sq_norm, Complex.mul_conj]
  simp only [hn]
  have he (x : ℝ) : centeredSum S c a x * conj (centeredSum S c a x) =
      ∑ m ∈ S, ∑ n ∈ S, (a m * conj (a n)) * fourierWave ((m : ℝ) - n) x := by
    simp only [centeredSum, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    rw [← wave_mul_conj n m c x]
    ring
  simp_rw [he]
  have hcont (m n : ℕ) : Continuous (fun x : ℝ ↦ (a m * conj (a n)) * fourierWave ((m : ℝ) - n) x) := by
    unfold fourierWave
    fun_prop
  rw [intervalIntegral.integral_finsetSum (fun m _ ↦
    (continuous_finsetSum S (fun n _ ↦ hcont m n)).intervalIntegrable (μ := volume) 0 1)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [intervalIntegral.integral_finsetSum (fun n _ ↦ (hcont m n).intervalIntegrable (μ := volume) 0 1)]
  simp_rw [intervalIntegral.integral_const_mul, integral_wave]
  simp [mul_ite, hm]

/-- Parseval’s identity on one period for a finite Fourier sum. -/
theorem integral_norm_sq (S : Finset ℕ) (a : ℕ → ℂ) :
    (∫ x in (0 : ℝ)..1, ‖fourierSum S a x‖ ^ 2) = ∑ n ∈ S, ‖a n‖ ^ 2 := by
  simpa only [centeredSum_zero] using centeredSum_parseval S 0 a

private theorem norm_wave_eq_one (t x : ℝ) : ‖fourierWave t x‖ = 1 := by
  simp [fourierWave, angularFrequency, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private theorem wave_add_frequency (t u x : ℝ) : fourierWave (t + u) x = fourierWave t x * fourierWave u x := by
  simp only [fourierWave, angularFrequency, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem centeredSum_norm (S : Finset ℕ) (c : ℝ) (a : ℕ → ℂ) (x : ℝ) :
    ‖centeredSum S c a x‖ = ‖centeredSum S 0 a x‖ := by
  have he : centeredSum S c a x = fourierWave (-c) x * centeredSum S 0 a x := by
    simp only [centeredSum, sub_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [sub_eq_add_neg, wave_add_frequency]
    ring
  rw [he, norm_mul, norm_wave_eq_one, one_mul]

private theorem centeredSum_endpoint (S : Finset ℕ) (c : ℝ) (a : ℕ → ℂ) : ‖centeredSum S c a 1‖ = ‖centeredSum S c a 0‖ := by
  rw [centeredSum_norm S c a 1, centeredSum_norm S c a 0]
  simp [centeredSum, fourierWave, angularFrequency, Complex.exp_nat_mul_two_pi_mul_I]

private theorem centeredSum_hasDerivAt (S : Finset ℕ) (c : ℝ) (a : ℕ → ℂ) (x : ℝ) :
    HasDerivAt (centeredSum S c a) (centeredSum S c (fun n ↦ angularFrequency ((n : ℝ) - c) * a n) x) x := by
  apply HasDerivAt.fun_sum
  intro n _
  let v := angularFrequency ((n : ℝ) - c)
  have hv : HasDerivAt (fun t : ℝ ↦ Complex.exp (v * t)) (Complex.exp (v * x) * v) x := by
    apply HasDerivAt.comp_ofReal (e := fun z : ℂ ↦ Complex.exp (v * z))
    simpa only [Function.comp_def, id_eq, mul_one] using! (Complex.hasDerivAt_exp _).comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).const_mul v)
  convert hv.const_mul (a n) using 1 <;> first | rfl | dsimp [fourierWave, v]; ring

private theorem centeredSum_continuous (S : Finset ℕ) (c : ℝ) (a : ℕ → ℂ) : Continuous (centeredSum S c a) :=
  continuous_iff_continuousAt.mpr fun x ↦ (centeredSum_hasDerivAt S c a x).continuousAt

private theorem norm_angularFrequency (t : ℝ) : ‖angularFrequency t‖ = 2 * Real.pi * |t| := by
  simp only [angularFrequency, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one, abs_of_pos Real.pi_pos, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  ring

private theorem variation_bound {S : Finset ℕ} (c : ℝ) (a : ℕ → ℂ) {B : ℝ} (hB : 0 < B)
    (hs : ∀ n ∈ S, ‖angularFrequency ((n : ℝ) - c)‖ ≤ B) :
    let P := centeredSum S c a
    let P' := centeredSum S c (fun n ↦ angularFrequency ((n : ℝ) - c) * a n)
    (∫ t in (0 : ℝ)..1, |2 * inner ℝ (P t) (P' t)|) ≤
      2 * B * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  intro P P'
  let E := ∑ n ∈ S, ‖a n‖ ^ 2
  have hP : Continuous P := centeredSum_continuous S c a
  have hP' : Continuous P' := centeredSum_continuous S c _
  have h₁ : (∫ t in (0 : ℝ)..1, ‖P t‖ ^ 2) = E := centeredSum_parseval S c a
  have h₂ : (∫ t in (0 : ℝ)..1, ‖P' t‖ ^ 2) ≤ B ^ 2 * E := by
    dsimp only [E]
    rw [show (∫ t in (0 : ℝ)..1, ‖P' t‖ ^ 2) = _ from centeredSum_parseval S c _, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hs n hn) 2) (sq_nonneg _)
  have hpoint (t : ℝ) : |2 * inner ℝ (P t) (P' t)| ≤ B * ‖P t‖ ^ 2 + ‖P' t‖ ^ 2 / B := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := abs_real_inner_le_norm (P t) (P' t)
    have h' : 2 * ‖P t‖ * ‖P' t‖ ≤ B * ‖P t‖ ^ 2 + ‖P' t‖ ^ 2 / B := by
      rw [← sub_le_iff_le_add', le_div_iff₀ hB]
      nlinarith [sq_nonneg (B * ‖P t‖ - ‖P' t‖)]
    linarith
  have hm := intervalIntegral.integral_mono (μ := volume) (a := (0 : ℝ)) (b := 1) (by norm_num)
    (((continuous_const.mul (hP.inner (𝕜:= ℝ) hP')).abs).intervalIntegrable _ _)
    (((continuous_const.mul (hP.norm.pow 2)).add ((hP'.norm.pow 2).div_const B)).intervalIntegrable _ _) hpoint
  change (∫ t in (0 : ℝ)..1, |2 * inner ℝ (P t) (P' t)|) ≤
    ∫ t in (0 : ℝ)..1, B * ‖P t‖ ^ 2 + ‖P' t‖ ^ 2 / B at hm
  rw [intervalIntegral.integral_add (f := fun t ↦ B * ‖P t‖ ^ 2) (g := fun t ↦ ‖P' t‖ ^ 2 / B) ((continuous_const.mul (hP.norm.pow 2)).intervalIntegrable _ _)
    (((hP'.norm.pow 2).div_const B).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_div, h₁] at hm
  have h₂' := (div_le_iff₀ hB).mpr (by nlinarith only [h₂] : (∫ t in (0 : ℝ)..1, ‖P' t‖ ^ 2) ≤ (B * E) * B)
  change _ ≤ 2 * B * E
  linarith

private theorem sum_bound_of_angular_frequencies {ι : Type*} (T : Finset ι) (x : ι → ℝ) {r : ℝ} (hr : 0 < r)
    (hbox : ∀ i ∈ T, 0 ≤ x i ∧ x i + r ≤ 1)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → r ≤ |x i - x j|)
    (S : Finset ℕ) (a : ℕ → ℂ) (c : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hs : ∀ n ∈ S, ‖angularFrequency ((n : ℝ) - c)‖ ≤ B) :
    ∑ i ∈ T, ‖centeredSum S 0 a (x i)‖ ^ 2 ≤
      (1 / r + B) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  let P := centeredSum S c a
  let P' := centeredSum S c (fun n ↦ angularFrequency ((n : ℝ) - c) * a n)
  let d (t : ℝ) := 2 * inner ℝ (P t) (P' t)
  have hcont : Continuous d := continuous_const.mul ((centeredSum_continuous S c a).inner (𝕜:= ℝ) (centeredSum_continuous S c _))
  have hder (t : ℝ) : HasDerivAt (fun y ↦ ‖P y‖ ^ 2) (d t) t := (centeredSum_hasDerivAt S c a t).norm_sq
  have h := sum_le_integral_add_variation T x hr hbox hsep hcont hder (fun _ ↦ sq_nonneg _) (by rw [show P = centeredSum S c a from rfl, centeredSum_endpoint S c a])
  change (∑ i ∈ T, ‖centeredSum S c a (x i)‖ ^ 2) ≤ (∫ t in (0 : ℝ)..1, ‖centeredSum S c a t‖ ^ 2) / r +
    (∫ t in (0 : ℝ)..1, |d t|) / 2 at h
  rw [centeredSum_parseval] at h
  simp_rw [centeredSum_norm S c a] at h
  have hl (b : ℝ) (hb : B < b) :
      (∫ t in (0 : ℝ)..1, |d t|) ≤ 2 * b*∑ n ∈ S, ‖a n‖ ^ 2 :=
    variation_bound c a (hB.trans_lt hb) (fun n hn ↦ (hs n hn).trans hb.le)
  have ht : Tendsto (fun b : ℝ ↦ 2 * b*∑ n ∈ S, ‖a n‖ ^ 2) (𝓝[>] B) (𝓝 (2 * B*∑ n ∈ S, ‖a n‖ ^ 2)) :=
    (continuous_const.mul continuous_id |>.mul continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ b : ℝ in 𝓝[>] B, B < b := self_mem_nhdsWithin
  have hv := ge_of_tendsto ht (hev.mono (fun _ hb ↦ hl _ hb))
  calc
    _ ≤ (∑ n ∈ S, ‖a n‖ ^ 2) / r + (∫ t in (0 : ℝ)..1, |d t|) / 2 := h
    _ ≤ (∑ n ∈ S, ‖a n‖ ^ 2) / r + (2 * B*∑ n ∈ S, ‖a n‖ ^ 2) / 2 := by linarith
    _ = _ := by ring

/-- Sample points whose right intervals of length δ are disjoint within [0,1] satisfy the additive large-sieve bound. -/
theorem sum_norm_sq_le_of_disjoint_intervals {ι : Type*} (T : Finset ι) (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hbox : ∀ i ∈ T, 0 ≤ x i ∧ x i + δ ≤ 1)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → δ ≤ |x i - x j|)
    (S : Finset ℕ) (a : ℕ → ℂ) {L U : ℕ} (hLU : L ≤ U)
    (hs : ∀ n ∈ S, L ≤ n ∧ n ≤ U) :
    ∑ i ∈ T, ‖fourierSum S a (x i)‖ ^ 2 ≤
      (1 / δ + Real.pi * ((U : ℝ) - L)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  simp only [← centeredSum_zero]
  apply sum_bound_of_angular_frequencies T x hδ hbox hsep S a (((L : ℝ) + U) / 2)
    (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr (by exact_mod_cast hLU)))
  intro n hn
  obtain ⟨h₁, h₂⟩ := hs n hn
  have h₁' : (L : ℝ) ≤ n := by exact_mod_cast h₁
  have h₂' : (n : ℝ) ≤ U := by exact_mod_cast h₂
  rw [norm_angularFrequency]
  have ha : |(n : ℝ) - ((L : ℝ) + U) / 2| ≤ ((U : ℝ) - L) / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr ha)]

private theorem wave_add_argument (n x y : ℝ) : fourierWave n (x + y) = fourierWave n x * fourierWave n y := by
  simp only [fourierWave, Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem sum_bound_after_translation {ι : Type*} (T : Finset ι) (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ₁ : δ ≤ 1)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → δ ≤ |x i - x j| ∧ |x i - x j| ≤ 1 - δ)
    (S : Finset ℕ) (a : ℕ → ℂ) {L U : ℕ} (hLU : L ≤ U)
    (hs : ∀ n ∈ S, L ≤ n ∧ n ≤ U) :
    ∑ i ∈ T, ‖fourierSum S a (x i)‖ ^ 2 ≤
      (1 / δ + Real.pi * ((U : ℝ) - L)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  rcases T.eq_empty_or_nonempty with h | h
  · subst T
    apply le_trans (by simp : (∑ i ∈ (∅ : Finset ι), ‖fourierSum S a (x i)‖ ^ 2) ≤ 0)
    exact mul_nonneg (add_nonneg (by positivity) (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr (by exact_mod_cast hLU)))) (Finset.sum_nonneg fun n _ ↦ sq_nonneg _)
  obtain ⟨k, hk, hmin⟩ := T.exists_min_image x h
  let a' (n : ℕ) := a n * fourierWave n (x k)
  have hbox (i : ι) (hi : i ∈ T) : 0 ≤ x i - x k ∧ (x i - x k) + δ ≤ 1 := by
    refine ⟨sub_nonneg.mpr (hmin i hi), ?_⟩
    by_cases he : i = k
    · simpa [he] using hδ₁
    · have hh := (hsep i hi k hk he).2
      linarith [le_abs_self (x i - x k)]
  have hsep' (i : ι) (hi : i ∈ T) (j : ι) (hj : j ∈ T) (hij : i ≠ j) :
      δ ≤ |(x i - x k) - (x j - x k)| := by
    simpa only [sub_sub_sub_cancel_right] using (hsep i hi j hj hij).1
  have hval (i : ι) : fourierSum S a' (x i - x k) = fourierSum S a (x i) := by
    simp only [← centeredSum_zero, centeredSum, sub_zero]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [a']
    rw [mul_assoc, ← wave_add_argument, show x k + (x i - x k) = x i by ring]
  have hnorm (n : ℕ) : ‖a' n‖ = ‖a n‖ := by simp [a', norm_wave_eq_one]
  simpa only [hval, hnorm] using sum_norm_sq_le_of_disjoint_intervals T (fun i ↦ x i - x k) hδ hbox hsep' S a' hLU hs

private theorem wave_int_eq_one (n : ℕ) (k : ℤ) : fourierWave n k = 1 := by
  unfold fourierWave angularFrequency
  convert Complex.exp_int_mul_two_pi_mul_I ((n : ℤ) * k) using 2
  push_cast
  ring

private theorem fourierSum_fract (S : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) :
    fourierSum S a (Int.fract x) = fourierSum S a x := by
  simp only [← centeredSum_zero, centeredSum, sub_zero]
  apply Finset.sum_congr rfl
  intro n _
  have he := wave_add_argument n (Int.fract x) (⌊x⌋ : ℝ)
  rw [Int.fract_add_floor, wave_int_eq_one, mul_one] at he
  rw [he]

/-- The additive large sieve for arbitrary real lifts of points separated modulo one.
The frequency dependence is the length U−L of an interval containing the support. -/
theorem sum_norm_sq_le_of_separation_mod_one {ι : Type*} (T : Finset ι) (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ₁ : δ ≤ 1)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ∀ k : ℤ, δ ≤ |x i - x j - k|)
    (S : Finset ℕ) (a : ℕ → ℂ) {L U : ℕ} (hLU : L ≤ U)
    (hs : ∀ n ∈ S, L ≤ n ∧ n ≤ U) :
    ∑ i ∈ T, ‖fourierSum S a (x i)‖ ^ 2 ≤
      (1 / δ + Real.pi * ((U : ℝ) - L)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  let y (i : ι) := Int.fract (x i)
  have hpair (i : ι) (hi : i ∈ T) (j : ι) (hj : j ∈ T) (hij : i ≠ j) :
      δ ≤ |y i - y j| ∧ |y i - y j| ≤ 1 - δ := by
    have h (l : ℤ) : δ ≤ |y i - y j - l| := by
      have he : y i - y j - l = x i - x j - ((⌊x i⌋ - ⌊x j⌋ + l : ℤ) : ℝ) := by
        change (x i - (⌊x i⌋ : ℝ)) - (x j - (⌊x j⌋ : ℝ)) - l = _
        push_cast
        ring
      rw [he]
      exact hsep i hi j hj hij _
    have hi₀ := Int.fract_nonneg (x i)
    have hi₁ := Int.fract_lt_one (x i)
    have hj₀ := Int.fract_nonneg (x j)
    have hj₁ := Int.fract_lt_one (x j)
    change 0 ≤ y i at hi₀
    change y i < 1 at hi₁
    change 0 ≤ y j at hj₀
    change y j < 1 at hj₁
    refine ⟨by simpa using h 0, abs_le.mpr ⟨?_, ?_⟩⟩
    · have he := h (-1)
      rw [Int.cast_neg, Int.cast_one, abs_of_nonneg (by linarith)] at he
      linarith
    · have he := h 1
      rw [Int.cast_one, abs_of_nonpos (by linarith)] at he
      linarith
  simpa only [y, fourierSum_fract] using sum_bound_after_translation T y hδ hδ₁ hpair S a hLU hs

private theorem reduced_fraction_unique {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hab : a.Coprime b) (hcd : c.Coprime d) (he : a * d = c * b) : a = c ∧ b = d := by
  have hbd : b ∣ d := hab.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left _ _)
  have hdb : d ∣ b := hcd.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left _ _)
  have heq := Nat.dvd_antisymm hbd hdb
  subst d
  exact ⟨Nat.eq_of_mul_eq_mul_right hb he, rfl⟩

private theorem reduced_fraction_spacing {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hab : a.Coprime b) (hcd : c.Coprime d) (hne : a ≠ c ∨ b ≠ d) :
    1 / (b * d : ℝ) ≤ |(a : ℝ) / b - (c : ℝ) / d| := by
  have hne' : a * d ≠ c * b := by
    intro he
    obtain ⟨h, h'⟩ := reduced_fraction_unique hb hd hab hcd he
    tauto
  have hbd : (0 : ℝ) < b * d := by positivity
  have h : (a : ℝ) / b - c / d = ((a : ℝ) * d - c * b) / (b * d) := by field_simp
  rw [h, abs_div, abs_of_pos hbd]
  apply div_le_div_of_nonneg_right _ hbd.le
  rcases lt_or_gt_of_ne hne' with h | h
  · have he : (a : ℝ) * d + 1 ≤ c * b := by exact_mod_cast (show a * d + 1 ≤ c * b by omega)
    rw [abs_of_nonpos (by linarith)]; linarith
  · have he : (c : ℝ) * b + 1 ≤ a * d := by exact_mod_cast (show c * b + 1 ≤ a * d by omega)
    rw [abs_of_nonneg (by linarith)]; linarith

private theorem reduced_fraction_interval {a q Q : ℕ} (ha : a < q) (hq : q ≤ Q) :
    0 ≤ (a : ℝ) / q ∧ (a : ℝ) / q + 1 / (Q : ℝ) ^ 2 ≤ 1 := by
  have hQ : 0 < Q := by omega
  have hq₀ : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  refine ⟨by positivity, ?_⟩
  have hqQ : (q : ℝ) ≤ (Q : ℝ) ^ 2 := le_trans (by exact_mod_cast hq)
    (le_self_pow₀ (by exact_mod_cast hQ : (1 : ℝ) ≤ Q) (by decide))
  have hr := one_div_le_one_div_of_le hq₀ hqQ
  have h : (a : ℝ) / q + 1 / q ≤ 1 := by
    rw [← add_div, div_le_one hq₀]
    exact_mod_cast (show a + 1 ≤ q by omega)
  linarith

/-- Any collection of distinct reduced fractions with denominator at most Q has sampling bound Q² + π(U−L). -/
theorem sum_norm_sq_le_at_reduced_fractions {Q : ℕ} (hQ : 0 < Q) (T : Finset (ℕ × ℕ))
    (hT : ∀ u ∈ T, u.1 < u.2 ∧ u.2 ≤ Q ∧ u.1.Coprime u.2)
    (S : Finset ℕ) (a : ℕ → ℂ) {L U : ℕ} (hLU : L ≤ U) (hs : ∀ n ∈ S, L ≤ n ∧ n ≤ U) :
    ∑ u ∈ T, ‖fourierSum S a ((u.1 : ℝ) / u.2)‖ ^ 2 ≤
      ((Q : ℝ) ^ 2 + Real.pi * ((U : ℝ) - L)) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  let δ : ℝ := 1 / (Q : ℝ) ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hbox := fun u hu ↦ reduced_fraction_interval (hT u hu).1 (hT u hu).2.1
  have hsep (u : ℕ × ℕ) (hu : u ∈ T) (v : ℕ × ℕ) (hv : v ∈ T) (hne : u ≠ v) :
      δ ≤ |(u.1 : ℝ) / u.2 - (v.1 : ℝ) / v.2| := by
    obtain ⟨ha, hb, hc⟩ := hT u hu
    obtain ⟨hd, he, hf⟩ := hT v hv
    have h := reduced_fraction_spacing (Nat.zero_lt_of_lt ha) (Nat.zero_lt_of_lt hd) hc hf
      (by by_contra! h; exact hne (Prod.ext h.1 h.2))
    apply le_trans _ h
    apply one_div_le_one_div_of_le (mul_pos (by exact_mod_cast Nat.zero_lt_of_lt ha) (by exact_mod_cast Nat.zero_lt_of_lt hd))
    simpa only [sq] using mul_le_mul (by exact_mod_cast hb : (u.2 : ℝ) ≤ Q)
      (by exact_mod_cast he : (v.2 : ℝ) ≤ Q) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  simpa [δ] using sum_norm_sq_le_of_disjoint_intervals T (fun u ↦ (u.1 : ℝ) / u.2) hδ hbox hsep S a hLU hs

private theorem integrable_fourierSum_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (S : Finset ℕ) {f : ℕ → α → ℂ} (hf : ∀ n ∈ S, MemLp (f n) 2 μ) (x : ℝ) :
    Integrable (fun y ↦ ‖fourierSum S (fun n ↦ f n y) x‖ ^ 2) μ := by
  have h := memLp_finsetSum S (fun n hn ↦ (hf n hn).const_smul
    (Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I) * x)))
  have h' := (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h
  simpa only [fourierSum, Pi.smul_apply, smul_eq_mul, mul_comm] using h'

/-- The reduced-fraction large sieve integrated against any common measure, with square-integrable coefficients. -/
theorem sum_integral_norm_sq_le_at_reduced_fractions {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {Q : ℕ} (hQ : 0 < Q) (T : Finset (ℕ × ℕ))
    (hT : ∀ u ∈ T, u.1 < u.2 ∧ u.2 ≤ Q ∧ u.1.Coprime u.2)
    (S : Finset ℕ) {f : ℕ → α → ℂ} (hf : ∀ n ∈ S, MemLp (f n) 2 μ)
    {L U : ℕ} (hLU : L ≤ U) (hs : ∀ n ∈ S, L ≤ n ∧ n ≤ U) :
    ∑ u ∈ T, (∫ y, ‖fourierSum S (fun n ↦ f n y) ((u.1 : ℝ) / u.2)‖ ^ 2 ∂μ) ≤
      ((Q : ℝ) ^ 2 + Real.pi * ((U : ℝ) - L)) * ∑ n ∈ S, ∫ y, ‖f n y‖ ^ 2 ∂μ := by
  have hi (n : ℕ) (hn : n ∈ S) := (memLp_two_iff_integrable_sq_norm (hf n hn).aestronglyMeasurable).mp (hf n hn)
  rw [← integral_finsetSum _ (fun u _ ↦ integrable_fourierSum_sq S hf ((u.1 : ℝ) / u.2)),
    ← integral_finsetSum _ hi, ← integral_const_mul]
  exact integral_mono (integrable_finsetSum _ (fun u _ ↦ integrable_fourierSum_sq S hf ((u.1 : ℝ) / u.2)))
    ((integrable_finsetSum _ hi).const_mul _) (fun y ↦ sum_norm_sq_le_at_reduced_fractions hQ T hT S (fun n ↦ f n y) hLU hs)

end AdditiveLargeSieve
