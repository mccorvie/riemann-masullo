module

public import RiemannMasullo.ForMathlib.Analysis.Analytic.ZeroLattice
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Consecutive-sample counts in one unit interval

A finite set of ordinates controls the possible large increases of a function with a
Landau-type logarithmic derivative bound. Each integer-grid sample and its successor
lie in the same closed unit interval.
-/

public noncomputable section

open Filter Set Topology
open scoped RealInnerProductSpace
namespace RiemannMasullo.AnalyticLattice

/-- The passing indices with left endpoint in the half-open unit bin indexed by `j`. -/
def binIndices (f : ℝ → ℂ) (j : ℤ) (n : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Ico (j * (n : ℤ) ^ 2) ((j + 1) * (n : ℤ) ^ 2)).filter fun k : ℤ ↦
    ((n : ℝ) + 1) * ‖f ((k : ℝ) / (n : ℝ) ^ 2)‖ <
      n * ‖f (((k : ℝ) + 1) / (n : ℝ) ^ 2)‖

/-- Membership gives the half-open bin bounds and the strict sample comparison. -/
theorem mem_binIndices_iff (f : ℝ → ℂ) (j : ℤ) (n : ℕ) (k : ℤ) :
    k ∈ binIndices f j n ↔ (j * (n : ℤ)^2 ≤ k ∧ k < (j+1) * (n : ℤ)^2) ∧
      ((n : ℝ)+1) * ‖f ((k : ℝ)/(n : ℝ)^2)‖ < n * ‖f (((k : ℝ)+1)/(n : ℝ)^2)‖ := by
  classical
  simp only [binIndices, Finset.mem_filter, Finset.mem_Ico]

private lemma deriv_log_norm_le {f : ℝ → ℂ} {x : ℝ} (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    DifferentiableAt ℝ (fun t ↦ Real.log ‖f t‖) x ∧
      deriv (fun t ↦ Real.log ‖f t‖) x ≤ ‖deriv f x‖ / ‖f x‖ := by
  have hp := norm_pos_iff.mpr hx
  have h := (hf.hasDerivAt.norm_sq.log (pow_ne_zero _ hp.ne')).const_mul (1 / 2 : ℝ)
  have heq : (fun y ↦ 1 / 2 * Real.log (‖f y‖ ^ 2)) = (fun y ↦ Real.log ‖f y‖) := by
    funext y
    rw [Real.log_pow]
    push_cast
    ring
  rw [heq] at h
  refine ⟨h.differentiableAt, ?_⟩
  rw [h.deriv]
  calc
    _ = inner ℝ (f x) (deriv f x) / ‖f x‖ ^ 2 := by ring
    _ ≤ (‖f x‖ * ‖deriv f x‖) / ‖f x‖ ^ 2 :=
      div_le_div_of_nonneg_right (real_inner_le_norm _ _) (sq_nonneg _)
    _ = _ := by field_simp

private lemma log_step_lower {n : ℝ} (hn : 0 < n) :
    1 / (n+1) ≤ Real.log ((n+1) / n) := by
  convert Real.one_sub_inv_le_log_of_pos (div_pos (by positivity : 0 < n + 1) hn) using 1
  field_simp
  ring

/-- If the baseline and sum of the positive integer weights in a logarithmic derivative estimate
are at most `B`, the normalized count in that bin is bounded uniformly in the mesh. -/
theorem bin_count_le_of_logDeriv {ι : Type*} (S : Finset ι) (ord : ι → ℕ) (b : ι → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hord : ∀ i ∈ S, 0 < ord i)
    (hmass : ∑ i ∈ S, (ord i : ℝ) ≤ B) {f : ℝ → ℂ} (j : ℤ)
    (hdata : ∀ t ∈ Icc (j : ℝ) ((j : ℝ) + 1), (∀ i ∈ S, t ≠ b i) →
      f t ≠ 0 ∧ DifferentiableAt ℝ f t ∧
        ‖deriv f t‖ / ‖f t‖ ≤ B + ∑ i ∈ S, (ord i : ℝ) / |t - b i|)
    (n : ℕ) (hn : 0 < n) :
    ((binIndices f j n).card : ℝ) / n ≤ 13 * (B + 1) ^ 2 := by
  classical
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₂ := sq_pos_of_pos hn₀
  have hB₁ : 0 < B + 1 := by linarith
  have hcard : ((S.card : ℕ) : ℝ) ≤ B := by
    calc
      _ = ∑ _i ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ S, (ord i : ℝ) := Finset.sum_le_sum fun i hi ↦ by exact_mod_cast hord i hi
      _ ≤ _ := hmass
  have hbin : (binIndices f j n).card ≤ n ^ 2 := by
    apply (Finset.card_filter_le _ _).trans
    rw [Int.card_Ico]
    have heq : (j + 1) * (n : ℤ) ^ 2 - j * n ^ 2 = (n : ℤ) ^ 2 := by ring
    simp [heq]
  by_cases hsmall : (n : ℝ) ≤ 4 * (B + 1)
  · apply (div_le_iff₀ hn₀).mpr
    have hh : ((binIndices f j n).card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hbin
    have hprod := mul_le_mul_of_nonneg_right hsmall hn₀.le
    nlinarith [mul_nonneg (mul_nonneg hB (by linarith : 0 ≤ B + 1)) hn₀.le,
      mul_nonneg hB hn₀.le]
  let D := 4 * (B + 1) / (n : ℝ)
  let h := 1 / (n : ℝ) ^ 2
  have hD : 0 < D := div_pos (by positivity) hn₀
  have hh : 0 < h := one_div_pos.mpr hn₂
  let C (i : ι) := Finset.Icc ⌊(b i - (D + h)) * (n : ℝ) ^ 2⌋
    ⌈(b i + (D + h)) * (n : ℝ) ^ 2⌉
  have hcover : binIndices f j n ⊆ S.biUnion C := by
    intro k hk
    obtain ⟨hkbin, htest⟩ := Finset.mem_filter.mp hk
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hkbin
    have hlow : (j : ℝ) * (n : ℝ) ^ 2 ≤ k := by exact_mod_cast hlo
    have hupp : (k : ℝ) + 1 ≤ ((j : ℝ)+1) * (n : ℝ) ^ 2 := by exact_mod_cast Int.add_one_le_iff.mpr hhi
    let x := (k : ℝ) / (n : ℝ) ^ 2
    have hx₀ : (j : ℝ) ≤ x := (le_div_iff₀ hn₂).mpr hlow
    have hx₁ : x + h ≤ (j : ℝ) + 1 := by
      change (k : ℝ) / _ + 1 / _ ≤ _
      rw [← add_div, div_le_iff₀ hn₂]
      exact hupp
    have ht : ((n : ℝ) + 1) * ‖f x‖ < n * ‖f (x+h)‖ := by simpa only [x, h, add_div] using htest
    by_contra hno
    have hfar (t : ℝ) (htx : t ∈ Icc x (x+h)) (i : ι) (hi : i ∈ S) : D < |t - b i| := by
      by_contra! hnear
      apply hno
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hi, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
      · apply Int.le_of_lt_add_one
        apply Int.floor_lt.mpr
        have hxk : (k : ℝ) = x * (n : ℝ) ^ 2 := by dsimp [x]; field_simp
        obtain ⟨hnear₁, hnear₂⟩ := abs_le.mp hnear
        push_cast
        nlinarith [mul_le_mul_of_nonneg_right (show b i - (D+h) ≤ x by linarith [htx.2]) hn₂.le]
      · apply Int.le_of_lt_add_one
        have hle : (k : ℝ) ≤ (b i + (D+h)) * (n : ℝ) ^ 2 := (div_le_iff₀ hn₂).mp
          (show x ≤ b i + (D+h) by linarith [(abs_le.mp hnear).2, htx.1])
        have hc := Int.le_ceil ((b i + (D+h)) * (n : ℝ) ^ 2)
        exact_mod_cast (show (k : ℝ) < ⌈(b i + (D+h)) * (n : ℝ) ^ 2⌉ + 1 by linarith)
    let G (t : ℝ) := Real.log ‖f t‖
    have hreg (t : ℝ) (htx : t ∈ Icc x (x+h)) :
        f t ≠ 0 ∧ DifferentiableAt ℝ G t ∧ deriv G t ≤ (n : ℝ) / 2 := by
      have h₁ := hdata t ⟨hx₀.trans htx.1, htx.2.trans hx₁⟩ (fun i hi he ↦ by
        have hs := hfar t htx i hi
        rw [he, sub_self, abs_zero] at hs
        linarith)
      have hsum : (∑ i ∈ S, (ord i : ℝ) / |t - b i|) ≤ B / D := by
        calc
          _ ≤ ∑ i ∈ S, (ord i : ℝ) / D := Finset.sum_le_sum fun i hi ↦
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) hD (hfar t htx i hi).le
          _ ≤ B / D := by rw [← Finset.sum_div]; exact div_le_div_of_nonneg_right hmass hD.le
      have hBD : B / D ≤ n / 4 := by
        rw [div_le_iff₀ hD]
        dsimp only [D]
        field_simp
        nlinarith
      have hlog := deriv_log_norm_le h₁.2.1 h₁.1
      exact ⟨h₁.1, hlog.1, hlog.2.trans (h₁.2.2.trans (by linarith))⟩
    have he := exists_deriv_eq_slope G (show x < x+h by linarith)
      (fun t ht ↦ (hreg t ht).2.1.continuousAt.continuousWithinAt)
      (fun t ht ↦ (hreg t ⟨ht.1.le, ht.2.le⟩).2.1.differentiableWithinAt)
    obtain ⟨c, hc, he⟩ := he
    have hcder := (hreg c ⟨hc.1.le, hc.2.le⟩).2.2
    rw [he, add_sub_cancel_left, div_le_iff₀ hh] at hcder
    have hleft := norm_pos_iff.mpr (hreg x ⟨le_rfl, by linarith⟩).1
    have hright := norm_pos_iff.mpr (hreg (x+h) ⟨by linarith, le_rfl⟩).1
    have hlog := Real.log_lt_log (mul_pos (by positivity) hleft) ht
    rw [Real.log_mul (by positivity) hleft.ne', Real.log_mul hn₀.ne' hright.ne'] at hlog
    have hbottom := log_step_lower hn₀
    rw [Real.log_div (by positivity) hn₀.ne'] at hbottom
    have hslope : (n : ℝ)/2*h ≤ 1 / (n+1 : ℝ) := by
      dsimp [h]
      field_simp
      nlinarith [mul_nonneg (sub_nonneg.mpr hn₁) hn₀.le]
    dsimp only [G] at hcder
    linarith
  have hC (i : ι) : ((C i).card : ℝ) ≤ 8 * (B + 1) * n + 5 := by
    let lo := (b i - (D+h)) * (n : ℝ) ^ 2
    let hi := (b i + (D+h)) * (n : ℝ) ^ 2
    have hle : lo ≤ hi := by dsimp [lo, hi]; gcongr; linarith
    have hfloor := Int.floor_le lo
    have hceil := Int.le_ceil hi
    have hc : ((C i).card : ℝ) = (⌈hi⌉ : ℝ) + 1 - (⌊lo⌋ : ℝ) := by
      have hl : ⌊lo⌋ ≤ ⌈hi⌉ + 1 := by exact_mod_cast (show (⌊lo⌋ : ℝ) ≤ (⌈hi⌉ : ℝ) + 1 by linarith)
      exact_mod_cast Int.card_Icc_of_le _ _ hl
    rw [hc]
    have hdiff : hi - lo = 8 * (B + 1) * n + 2 := by dsimp [hi, lo, D, h]; field_simp; ring
    linarith [Int.lt_floor_add_one lo, Int.ceil_lt_add_one hi]
  have htake : ((binIndices f j n).card : ℝ) ≤ ∑ i ∈ S, ((C i).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans (Finset.card_biUnion_le (s := S) (t := C))
  have hcount : ((binIndices f j n).card : ℝ) ≤ B * (8 * (B + 1) * n + 5) := by
    calc
      _ ≤ _ := htake.trans (Finset.sum_le_sum (fun i hi ↦ hC i))
      _ = _ := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  apply (div_le_iff₀ hn₀).mpr
  nlinarith [mul_nonneg hB (by linarith : 0 ≤ (n : ℝ)-1),
    mul_nonneg (sq_nonneg B) hn₀.le, mul_nonneg hB hn₀.le]

end RiemannMasullo.AnalyticLattice
