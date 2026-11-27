module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Gaussian.GaussianExpansion
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Gaussian.PairSummable
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Gaussian.Resonance
import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

open MeasureTheory Set

namespace RiemannMasullo.Selberg

private lemma norm_pairInt_le (P Q q : ℝ) :
    ‖pairInt P Q q‖ ≤ ∫ x in Ioi (1 : ℝ), x ^ (-q) * Real.exp (-P * x ^ 2) := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx₀ : 0 ≤ x := zero_le_one.trans hx.le
  simp [Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hx₀ _),
    ← Complex.ofReal_pow, Complex.mul_re]

private lemma pairInt_zero_phase (P q : ℝ) :
    pairInt P 0 q = ((∫ x in Ioi (1 : ℝ), x ^ (-q) * Real.exp (-P * x ^ 2) : ℝ) : ℂ) := by
  rw [pairInt, ← integral_complex_ofReal]
  simp [Complex.ofReal_mul, Complex.ofReal_exp]

private lemma scale_sq {N : ℕ} (hN : 2 ≤ N) :
    scale N ^ 2 = 2 * Real.pi * Real.sin (1 / (H N : ℝ)) := by
  have hH : (1 : ℝ) ≤ H N := by exact_mod_cast Nat.one_le_pow 100 N (by omega)
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (x := 1 / (H N : ℝ)) (by positivity)
    ((div_le_one_of_le₀ hH (by positivity)).trans (one_lt_two.trans_le Real.two_le_pi).le)
  exact Real.sq_sqrt (by positivity)

private lemma pair_series_split {N k l m v : ℕ} (hN : 2 ≤ N) (hk : k ∈ D N) (hl : l ∈ D N)
    (hm : m ∈ D N) (hv : v ∈ D N) (q : ℝ) (hq : 0 ≤ q) :
    (∑' ij, pair N k l m v q ij).re =
      (∫ x in Ioi (1 : ℝ), x^(-q) * theta (scale N / ratio k l m v * x)) +
      (∑' ij : ℕ × ℕ, if freq ij.1 k l = freq ij.2 m v then 0
        else pair N k l m v q ij).re := by
  classical
  let s : Set (ℕ × ℕ) := {ij | freq ij.1 k l = freq ij.2 m v}
  let G (ij : ℕ × ℕ) (x : ℝ) := x^(-q) * Real.exp
    (-Real.pi * Real.sin (1 / (H N : ℝ)) * (freq ij.1 k l ^ 2 + freq ij.2 m v ^ 2) * x^2)
  have hG : Summable (fun ij ↦ ∫ x in Ioi (1 : ℝ), G ij x) :=
    pair_summable N k l m v hN hk hl hm hv q hq
  have hp : Summable (pair N k l m v q) := hG.of_norm_bounded fun ij ↦ by
    simpa only [pair, G, neg_mul] using (norm_pairInt_le _ _ q)
  have hpair (ij : s) :
      pair N k l m v q ij = ((∫ x in Ioi (1 : ℝ), G ij x : ℝ) : ℂ) := by
    have he : freq ij.val.1 k l = freq ij.val.2 m v := ij.property
    simp [pair, G, he, pairInt_zero_phase, neg_mul]
  have hexchange : (∑' ij : s, ∫ x in Ioi (1 : ℝ), G ij x) =
      ∫ x in Ioi (1 : ℝ), ∑' ij : s, G ij x := by
    apply integral_tsum_of_summable_integral_norm
    · exact fun ij ↦ pair_integrable N k l m v hN hk hl hm hv q hq ij.val
    · apply (hG.subtype (· ∈ s)).congr
      intro ij
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx₀ : 0 ≤ x := zero_le_one.trans hx.le
      exact (Real.norm_of_nonneg (show 0 ≤ G ij x by dsimp [G]; positivity)).symm
  have htheta (x : ℝ) : (∑' ij : s, G ij x) = x^(-q) * theta (scale N / ratio k l m v * x) := by
    let f (a : ℝ) := x^(-q) * Real.exp (-(a * scale N * x)^2)
    calc
      (∑' ij : s, G ij x) = ∑' ij : s, f (freq ij.val.1 k l) := by
        apply tsum_congr
        intro ij
        have he : freq ij.val.1 k l = freq ij.val.2 m v := ij.property
        dsimp only [G, f]
        rw [← he, mul_pow, mul_pow, scale_sq hN]
        congr 2
        ring
      _ = ∑' j : ℕ, f (((j + 1 : ℕ) : ℝ) / ratio k l m v) := by
        apply Complex.ofReal_injective
        rw [Complex.ofReal_tsum, Complex.ofReal_tsum,
          tsum_subtype s (fun ij ↦ (f (freq ij.1 k l) : ℂ))]
        exact resonance k l m v (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hl).1
          (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hv).1 (fun a ↦ (f a : ℂ))
      _ = _ := by
        rw [theta, ← tsum_mul_left]
        apply tsum_congr
        intro j
        dsimp only [f]
        congr 4
        ring
  rw [← hp.tsum_subtype_add_tsum_subtype_compl s, Complex.add_re, tsum_congr hpair,
    ← Complex.ofReal_tsum, Complex.ofReal_re, hexchange]
  simp_rw [htheta]
  rw [tsum_subtype sᶜ (pair N k l m v q)]
  simp only [indicator_apply, mem_compl_iff, mem_ofPred_eq, s, ite_not]

/-- Card 28. The weighted Gaussian integral is its equal-frequency contribution plus the series of
pairs with unequal frequencies.
Titchmarsh, §10.11, p. 270, Σ₁+Σ₂. -/
theorem diagonal_split (N : ℕ) (hN : 2 ≤ N) (b : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q) :
    J N b q = diag N b q + fourSum N (fun k l m v ↦ coef b k l m v *
      (∑' ij : ℕ × ℕ, if freq ij.1 k l = freq ij.2 m v then 0
        else pair N k l m v q ij).re) := by
  rw [(gaussian_expansion N hN b q hq).2, diag, fourSum, fourSum, fourSum]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk ↦ Finset.sum_congr rfl fun l hl ↦
    Finset.sum_congr rfl fun m hm ↦ Finset.sum_congr rfl fun v hv ↦ ?_
  rw [pair_series_split hN hk hl hm hv q hq, mul_add]

end RiemannMasullo.Selberg
