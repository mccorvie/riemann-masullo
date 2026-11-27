module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Gaussian.PairSummable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

public section

open MeasureTheory Set
open scoped ComplexConjugate

namespace RiemannMasullo.Selberg

private lemma osc_angle_sq (N : ℕ) :
    osc (angle N)^2 = (Real.sin (1/(H N : ℝ)) : ℂ) +
      Complex.I * (Real.cos (1/(H N : ℝ)) : ℂ) := by
  have hd : angle N + angle N = Real.pi / 2 - 1 / (H N : ℝ) := by
    simp only [angle, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [osc, sq, ← Complex.exp_add, ← mul_add, ← Complex.ofReal_add, mul_comm Complex.I]
  apply Complex.ext <;> simp only [hd, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, add_zero, zero_add, sub_self]

private noncomputable def rotatedTerm (N : ℕ) (A x : ℝ) : ℂ :=
  Complex.exp ((↑(-Real.pi * A^2 * x^2) : ℂ) *
    ((Real.sin (1/(H N : ℝ)) : ℂ) + Complex.I * (Real.cos (1/(H N : ℝ)) : ℂ)))

private lemma psi_rotated (N k l : ℕ) (x : ℝ) :
    psi (((x*k/l : ℝ) : ℂ)*osc (angle N)) = ∑' i, rotatedTerm N (freq i k l) x := by
  unfold psi
  apply tsum_congr
  intro i
  unfold rotatedTerm freq
  rw [mul_pow, osc_angle_sq]
  congr 1
  push_cast
  ring

private noncomputable def pairKernel (N : ℕ) (A B q x : ℝ) : ℂ :=
  (x^(-q) : ℝ) * Complex.exp
    ((-((Real.pi*Real.sin (1/(H N : ℝ))*(A^2+B^2) : ℝ) : ℂ) +
      Complex.I*((Real.pi*Real.cos (1/(H N : ℝ))*(B^2-A^2) : ℝ) : ℂ))*(x : ℂ)^2)

private lemma pairKernel_factor (N : ℕ) (A B q x : ℝ) :
    pairKernel N A B q x =
      (x^(-q) : ℝ) * (rotatedTerm N A x * conj (rotatedTerm N B x)) := by
  unfold pairKernel rotatedTerm
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 2
  simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private lemma norm_pairKernel (N : ℕ) (A B q : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ‖pairKernel N A B q x‖ =
      x^(-q) * Real.exp (-Real.pi*Real.sin (1/(H N : ℝ))*(A^2+B^2)*x^2) := by
  simp only [pairKernel, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hx _),
    Complex.norm_exp, ← Complex.ofReal_pow, Complex.mul_re, Complex.add_re, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
    sub_zero, add_zero, mul_zero, neg_mul]

private noncomputable def weightedProduct (N k l m v : ℕ) (q x : ℝ) : ℂ :=
  (x^(-q) : ℝ) * (psi (((x*k/l : ℝ) : ℂ)*osc (angle N)) *
    conj (psi (((x*m/v : ℝ) : ℂ)*osc (angle N))))

private lemma sum_pairKernel (N k l m v : ℕ) (q x : ℝ)
    (hs : Summable fun ij : ℕ × ℕ ↦ pairKernel N (freq ij.1 k l) (freq ij.2 m v) q x) :
    ∑' ij : ℕ × ℕ, pairKernel N (freq ij.1 k l) (freq ij.2 m v) q x =
      weightedProduct N k l m v q x := by
  rw [hs.tsum_prod]
  simp only [pairKernel_factor, tsum_mul_left, tsum_mul_right, weightedProduct, psi_rotated,
    Complex.conj_tsum]

/-- Absolute convergence in the integral gives both pointwise summability almost everywhere
and an integrable sum. -/
private lemma integrable_pair_series {F : ℕ × ℕ → ℝ → ℂ} {μ : Measure ℝ}
    (hi : ∀ ij, Integrable (F ij) μ) (hs : Summable fun ij ↦ ∫ x, ‖F ij x‖ ∂μ) :
    (∀ᵐ x ∂μ, Summable fun ij ↦ F ij x) ∧ Integrable (fun x ↦ ∑' ij, F ij x) μ := by
  have hm (ij) := (hi ij).aestronglyMeasurable.eNorm
  have hfin : ∫⁻ x, ∑' ij, ‖F ij x‖ₑ ∂μ ≠ ⊤ := by
    rw [lintegral_tsum hm]
    simpa only [ofReal_integral_norm_eq_lintegral_eNorm (hi _)] using hs.tsum_ofReal_ne_top
  refine ⟨(ae_lt_top' (AEMeasurable.tsum hm) hfin).mono fun x hx ↦ Summable.of_eNorm hx.ne,
    AEStronglyMeasurable.tsum (fun ij ↦ (hi ij).1), ?_⟩
  exact lt_of_le_of_lt (lintegral_mono fun _ ↦ eNorm_tsum_le_tsum_eNorm) hfin.lt_top

private lemma weightedProduct_integral {N k l m v : ℕ} (hN : 2 ≤ N) (hk : k ∈ D N)
    (hl : l ∈ D N) (hm : m ∈ D N) (hv : v ∈ D N) {q : ℝ} (hq : 0 ≤ q) :
    IntegrableOn (weightedProduct N k l m v q) (Ioi 1) ∧
      ∫ x in Ioi (1 : ℝ), weightedProduct N k l m v q x =
        ∑' ij, pair N k l m v q ij := by
  let μ := volume.restrict (Ioi (1 : ℝ))
  let F (ij : ℕ × ℕ) := pairKernel N (freq ij.1 k l) (freq ij.2 m v) q
  have hnorm (ij : ℕ × ℕ) : (fun x ↦ ‖F ij x‖) =ᵐ[μ] fun x ↦
      x^(-q)*Real.exp (-Real.pi*Real.sin (1/(H N : ℝ)) *
        ((freq ij.1 k l)^2+(freq ij.2 m v)^2)*x^2) := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (1 : ℝ)))] with x hx
    exact norm_pairKernel _ _ _ _ (zero_le_one.trans hx.le)
  have hi (ij) : Integrable (F ij) μ := by
    apply (integrable_norm_iff ?_).mp
    · exact (pair_integrable N k l m v hN hk hl hm hv q hq ij).congr (hnorm ij).symm
    · change AEStronglyMeasurable (fun x : ℝ ↦ (↑(x^(-q)) : ℂ) *
          Complex.exp (_ * (x : ℂ)^2)) μ
      fun_prop
  have hs : Summable fun ij ↦ ∫ x, ‖F ij x‖ ∂μ := by
    simpa only [integral_congr_ae (hnorm _)] using
      pair_summable N k l m v hN hk hl hm hv q hq
  obtain ⟨hae, hint⟩ := integrable_pair_series hi hs
  have heq : (fun x ↦ ∑' ij, F ij x) =ᵐ[μ] weightedProduct N k l m v q :=
    hae.mono fun x hx ↦ sum_pairKernel N k l m v q x hx
  exact ⟨hint.congr heq, (integral_congr_ae heq).symm.trans
    (hasSum_integral_of_summable_integral_norm hi hs).tsum_eq.symm⟩

private lemma norm_g_sq_expand (N : ℕ) (b : ℕ → ℝ) (q x : ℝ) :
    ‖g N b x‖^2*x^(-q) = fourSum N fun k l m v ↦
      coef b k l m v * (weightedProduct N k l m v q x).re := by
  let Z (k l : ℕ) := psi (((x*k/l : ℝ) : ℂ)*osc (angle N))
  let c (k l : ℕ) := b k * b l / l
  have term (k l m v : ℕ) :
      ((↑(c k l) * Z k l) * (↑(c m v) * conj (Z m v))).re * x^(-q) =
        coef b k l m v * (weightedProduct N k l m v q x).re := by
    rw [mul_mul_mul_comm, ← Complex.ofReal_mul, Complex.re_ofReal_mul, weightedProduct,
      Complex.re_ofReal_mul]
    change c k l * c m v * _ * _ = coef b k l m v * (_ * (Z k l * conj (Z m v)).re)
    simp only [c, coef, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq (g N b x)),
    ← Complex.mul_conj]
  change ((∑ k ∈ D N, ∑ l ∈ D N, ↑(c k l) * Z k l) *
    conj (∑ m ∈ D N, ∑ v ∈ D N, ↑(c m v) * Z m v)).re * _ = _
  simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul]
  simp only [Finset.mul_sum, Complex.re_sum, Finset.sum_mul, term, fourSum]

/-- Card 26. For q ≥ 0 and N ≥ 2, the integrand defining J is integrable on (1, ∞), and J expands
into the coefficient-weighted real parts of the Gaussian pair series.
Titchmarsh, §10.11, p. 270, expansion of J. -/
theorem gaussian_expansion (N : ℕ) (hN : 2 ≤ N) (b : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q) :
    IntegrableOn (fun x : ℝ ↦ ‖g N b x‖^2*x^(-q)) (Ioi 1) ∧
    J N b q = fourSum N (fun k l m v ↦ coef b k l m v *
      (∑' ij : ℕ × ℕ, pair N k l m v q ij).re) := by
  let μ := volume.restrict (Ioi (1 : ℝ))
  let f (k l m v : ℕ) (x : ℝ) := coef b k l m v * (weightedProduct N k l m v q x).re
  have hpair := fun k l m v hk hl hm hv ↦
    weightedProduct_integral (k := k) (l := l) (m := m) (v := v) hN hk hl hm hv hq
  have hi (k l m v) (hk : k ∈ D N) (hl : l ∈ D N) (hm : m ∈ D N) (hv : v ∈ D N) :
      Integrable (f k l m v) μ :=
    (hpair k l m v hk hl hm hv).1.re.const_mul _
  have heq : (fun x : ℝ ↦ ‖g N b x‖^2*x^(-q)) =
      fun x ↦ fourSum N fun k l m v ↦ f k l m v x := funext (norm_g_sq_expand N b q)
  unfold J
  rw [heq]
  unfold fourSum
  constructor
  · change Integrable _ μ
    iterate 4 (apply integrable_finsetSum; intro _ _)
    apply hi <;> assumption
  · iterate 4
      rw [integral_finsetSum _ (by
        intro _ _
        repeat' (apply integrable_finsetSum; intro _ _)
        apply hi <;> assumption)]
      apply Finset.sum_congr rfl
      intro _ _
    rename_i k hk l hl m hm v hv
    dsimp only [f]
    rw [integral_const_mul, ← RCLike.re_eq_complex_re, integral_re (hpair k l m v hk hl hm hv).1,
      (hpair k l m v hk hl hm hv).2]

end RiemannMasullo.Selberg
