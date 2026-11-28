module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # One-sided Abel means of absolutely summable exponential series

Damping translates of an exponential series recovers coefficients at its right edge.
The squared mean counts distinct frequencies diagonally and requires no minimum spacing.
-/

public noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace RiemannMasullo.AbelEdge

private theorem expSeries_laplace {ι : Type*} [Countable ι] (w b : ι → ℂ)
    (hw : ∀ i, (w i).re ≤ 0) (hb : Summable fun i ↦ ‖b i‖) {ε : ℝ} (hε : 0 < ε) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-(ε : ℂ) * y) * (∑' i, b i * Complex.exp (w i * y))) =
      ∑' i, b i / ((ε : ℂ) - w i) := by
  let F (i : ι) (y : ℝ) := b i * Complex.exp ((w i - ε) * y)
  have hlt (i : ι) : (w i - ε).re < 0 := by simp; linarith [hw i]
  have hint (i : ι) : IntegrableOn (F i) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (hlt i) 0).const_mul (b i)
  have hsum : Summable fun i ↦ ∫ y in Ioi (0 : ℝ), ‖F i y‖ := by
    refine (hb.mul_right (1 / ε)).of_nonneg_of_le (fun i ↦ integral_nonneg fun _ ↦ norm_nonneg _) ?_
    intro i
    calc
      _ ≤ ∫ y in Ioi (0 : ℝ), ‖b i‖ * Real.exp (-ε * y) := by
        refine integral_mono_ae (hint i).norm ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) 0).const_mul _) ?_
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
        simp only [F, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (by linarith [hw i]) (le_of_lt hy))) (norm_nonneg _)
      _ = ‖b i‖ * (1 / ε) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hε)]
        simp
  have hterm (i : ι) : (∫ y : ℝ in Ioi 0, F i y) = b i / ((ε : ℂ) - w i) := by
    rw [show (∫ y : ℝ in Ioi 0, F i y) = _ from integral_const_mul _ _,
      integral_exp_mul_complex_Ioi (hlt i)]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, ← neg_sub (ε : ℂ) (w i), div_neg]
    ring
  calc
    _ = ∫ y : ℝ in Ioi 0, ∑' i, F i y := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _
      change Complex.exp (-(ε : ℂ) * y) * (∑' i, b i * Complex.exp (w i * y)) = ∑' i, F i y
      rw [← tsum_mul_left]
      exact tsum_congr fun i ↦ by simp only [F, sub_eq_add_neg, add_mul, Complex.exp_add]; ring
    _ = _ := by
      rw [← integral_tsum_of_summable_integral_norm hint hsum]
      exact tsum_congr hterm

/-- The normalized one-sided Abel mean selects precisely the zero frequencies of an absolutely
summable exponential series whose exponents have nonpositive real parts. -/
theorem tendsto_abel_expSeries {ι : Type*} [Countable ι] (w b : ι → ℂ)
    (hw : ∀ i, (w i).re ≤ 0) (hb : Summable fun i ↦ ‖b i‖) :
    Tendsto (fun ε : ℝ ↦ (ε : ℂ) * ∫ y : ℝ in Ioi 0,
      Complex.exp (-(ε : ℂ) * y) * (∑' i, b i * Complex.exp (w i * y)))
      (𝓝[>] 0) (𝓝 (∑' i, if w i = 0 then b i else 0)) := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hcoe : Tendsto (fun ε : ℝ ↦ (ε : ℂ)) (𝓝[>] 0) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hsum : Tendsto (fun ε : ℝ ↦ ∑' i, (ε : ℂ) / ((ε : ℂ) - w i) * b i)
      (𝓝[>] 0) (𝓝 (∑' i, if w i = 0 then b i else 0)) := by
    apply tendsto_tsum_of_dominated_convergence hb
    · intro i
      by_cases hi : w i = 0
      · simp only [hi, ↓reduceIte]
        apply tendsto_const_nhds.congr'
        filter_upwards [he] with ε hε
        simp [Complex.ofReal_ne_zero.mpr hε.ne']
      · simp only [hi, ↓reduceIte]
        simpa [hi] using (hcoe.div (hcoe.sub_const (w i)) (by simpa using hi)).mul_const (b i)
    · filter_upwards [he] with ε hε i
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hε.le]
      apply mul_le_of_le_one_left (norm_nonneg _)
      have hreal : ε ≤ ‖(ε : ℂ) - w i‖ := calc
        _ ≤ ((ε : ℂ) - w i).re := by simp; linarith [hw i]
        _ ≤ _ := Complex.re_le_norm _
      exact (div_le_one (hε.trans_le hreal)).mpr hreal
  apply hsum.congr'
  filter_upwards [he] with ε hε
  rw [expSeries_laplace w b hw hb hε, ← tsum_mul_left]
  exact tsum_congr fun i ↦ by ring

/-- Demodulation at a specified boundary frequency recovers its complex coefficient. -/
theorem tendsto_abel_expSeries_atSite {ι : Type*} [Countable ι] (w b : ι → ℂ) (i₀ : ι)
    (hinj : Function.Injective w) (hw : ∀ i, (w i).re ≤ (w i₀).re)
    (hb : Summable fun i ↦ ‖b i‖) :
    Tendsto (fun ε : ℝ ↦ (ε : ℂ) * ∫ y : ℝ in Ioi 0,
      Complex.exp ((-(ε : ℂ) - w i₀) * y) * (∑' i, b i * Complex.exp (w i * y)))
      (𝓝[>] 0) (𝓝 (b i₀)) := by
  classical
  have hu (i : ι) : (w i - w i₀).re ≤ 0 := by simpa only [Complex.sub_re, sub_nonpos] using hw i
  have h := tendsto_abel_expSeries (fun i ↦ w i - w i₀) b hu hb
  simp only [sub_eq_zero, hinj.eq_iff, tsum_ite_eq] at h
  apply h.congr
  intro ε
  apply congrArg ((ε : ℂ) * ·)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  change Complex.exp (-(ε : ℂ) * y) * (∑' i, b i * Complex.exp ((w i - w i₀) * y)) =
    Complex.exp ((-(ε : ℂ) - w i₀) * y) * (∑' i, b i * Complex.exp (w i * y))
  simp_rw [sub_eq_add_neg, add_mul, Complex.exp_add]
  rw [← tsum_mul_left, ← tsum_mul_left]
  exact tsum_congr fun i ↦ by ring

/-! ## The squared norm in the one-sided Abel mean -/

open scoped ComplexConjugate

private theorem norm_expSeries_term_le {u a : ℂ} {β y : ℝ} (hu : u.re ≤ β) (hy : 0 ≤ y) :
    ‖a * Complex.exp (u * y)‖ ≤ ‖a‖ * Real.exp (β * y) := by
  rw [norm_mul, Complex.norm_exp, Complex.re_mul_ofReal]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hu hy)) (norm_nonneg _)

/-- A uniform upper bound on the real parts preserves absolute convergence at each
nonnegative translate of the coefficient series. -/
theorem summable_norm_expSeries {ι : Type*} (w b : ι → ℂ) {β : ℝ}
    (hw : ∀ i, (w i).re ≤ β) (hb : Summable fun i ↦ ‖b i‖) (y : ℝ) (hy : 0 ≤ y) :
    Summable (fun i ↦ ‖b i * Complex.exp (w i * y)‖) :=
  (hb.mul_right (Real.exp (β * y))).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun i ↦
    norm_expSeries_term_le (hw i) hy

/-- The sum of coefficient norms bounds the rightward growth of the whole series. -/
theorem norm_expSeries_le {ι : Type*} (w b : ι → ℂ) {β : ℝ}
    (hw : ∀ i, (w i).re ≤ β) (hb : Summable fun i ↦ ‖b i‖) (y : ℝ) (hy : 0 ≤ y) :
    ‖∑' i, b i * Complex.exp (w i * y)‖ ≤ (∑' i, ‖b i‖) * Real.exp (β * y) := by
  have hs := summable_norm_expSeries w b hw hb y hy
  calc
    _ ≤ _ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' i, ‖b i‖ * Real.exp (β * y) :=
      hs.tsum_le_tsum (fun i ↦ norm_expSeries_term_le (hw i) hy) (hb.mul_right _)
    _ = _ := tsum_mul_right

private theorem expSeries_pair_sum {ι : Type*} (w b : ι → ℂ) (β : ℝ)
    (hw : ∀ i, (w i).re ≤ β) (hb : Summable fun i ↦ ‖b i‖) (y : ℝ) (hy : 0 ≤ y) :
    (∑' p : ι × ι, (b p.1 * conj (b p.2)) *
      Complex.exp (((w p.1 - β) + conj (w p.2 - β)) * y)) =
      Complex.exp (-(2 * (β : ℂ)) * y) *
        ((‖∑' i, b i * Complex.exp (w i * y)‖ ^ 2 : ℝ) : ℂ) := by
  let a (i : ι) := b i * Complex.exp (w i * y)
  have ha : Summable fun i ↦ ‖a i‖ := summable_norm_expSeries w b hw hb y hy
  have hconj : Summable fun i ↦ ‖conj (a i)‖ := by
    simpa only [Complex.norm_conj] using ha
  have hterm (p : ι × ι) :
      (b p.1 * conj (b p.2)) * Complex.exp (((w p.1 - β) + conj (w p.2 - β)) * y) =
      Complex.exp (-(2 * (β : ℂ)) * y) * (a p.1 * conj (a p.2)) := by
    have hfreq : ((w p.1 - β) + conj (w p.2 - β)) * y =
        -(2 * (β : ℂ)) * y + w p.1 * y + conj (w p.2 * y) := by
      simp only [map_sub, map_mul, Complex.conj_ofReal]
      ring
    rw [hfreq, Complex.exp_add, Complex.exp_add, Complex.exp_conj]
    simp only [a, map_mul]
    ring
  rw [tsum_congr hterm, tsum_mul_left, ← tsum_mul_tsum_of_summable_norm ha hconj,
    ← Complex.conj_tsum, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The integrand of the Abel mean-square is integrable at every positive damping. -/
theorem integrableOn_abel_normSq_expSeries {ι : Type*} [Countable ι] (w b : ι → ℂ)
    (β : ℝ) (hw : ∀ i, (w i).re ≤ β) (hb : Summable fun i ↦ ‖b i‖) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun y : ℝ ↦ Real.exp (-(ε + 2 * β) * y) *
      ‖∑' i, b i * Complex.exp (w i * y)‖ ^ 2) (Ioi 0) := by
  let B := ∑' i, ‖b i‖
  have hm : Measurable (fun y : ℝ ↦ ∑' i, b i * Complex.exp (w i * y)) :=
    Measurable.tsum fun i ↦ by fun_prop
  refine ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) 0).const_mul (B ^ 2)).mono' ?_ ?_
  · exact (Measurable.mul (by fun_prop) (hm.norm.pow_const 2)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
  have hvalue := norm_expSeries_le w b hw hb y hy.le
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
  calc
    _ ≤ Real.exp (-(ε + 2 * β) * y) * (B * Real.exp (β * y)) ^ 2 := by gcongr
    _ = B ^ 2 * Real.exp (-ε * y) := by
      rw [mul_pow, mul_left_comm, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 2
      push_cast
      ring

/-- Applying the Abel limit for exponential series to all pairs of frequencies gives the
sum of the squared coefficients at the right edge. -/
theorem tendsto_abel_normSq_expSeries {ι : Type*} [Countable ι]
    (w b : ι → ℂ) (β : ℝ) (hinj : Function.Injective w)
    (hw : ∀ i, (w i).re ≤ β) (hb : Summable fun i ↦ ‖b i‖) :
    Tendsto (fun ε : ℝ ↦ ε * ∫ y : ℝ in Ioi 0,
      Real.exp (-(ε + 2 * β) * y) * ‖∑' i, b i * Complex.exp (w i * y)‖ ^ 2)
      (𝓝[>] 0) (𝓝 (∑' i, if (w i).re = β then ‖b i‖ ^ 2 else 0)) := by
  classical
  let v (p : ι × ι) := (w p.1 - β) + conj (w p.2 - β)
  let c (p : ι × ι) := b p.1 * conj (b p.2)
  have hv (p : ι × ι) : (v p).re ≤ 0 := by
    simpa only [v, Complex.add_re, Complex.conj_re, Complex.sub_re, Complex.ofReal_re] using
      add_nonpos (sub_nonpos.mpr (hw p.1)) (sub_nonpos.mpr (hw p.2))
  have hbc : Summable fun i ↦ ‖conj (b i)‖ := by simpa only [Complex.norm_conj] using hb
  have hc : Summable fun p ↦ ‖c p‖ := hb.mul_norm hbc
  have hzero (i j : ι) : v (i, j) = 0 ↔ i = j ∧ (w i).re = β := by
    constructor
    · intro h
      have hr := congrArg Complex.re h
      have hi := congrArg Complex.im h
      simp only [v, Complex.add_re, Complex.conj_re, Complex.sub_re, Complex.ofReal_re,
        Complex.zero_re] at hr
      simp only [v, Complex.add_im, Complex.conj_im, Complex.sub_im, Complex.ofReal_im,
        sub_zero, Complex.zero_im] at hi
      have hiβ : (w i).re = β := by linarith [hw i, hw j]
      have hjβ : (w j).re = β := by linarith [hw i, hw j]
      exact ⟨hinj (Complex.ext (hiβ.trans hjβ.symm) (by linarith)), hiβ⟩
    · rintro ⟨hij, hiβ⟩
      subst j
      simp only [v, Complex.add_conj, Complex.sub_re, Complex.ofReal_re, hiβ, sub_self,
        mul_zero, Complex.ofReal_zero]
  have hdiagSum : Summable fun p ↦ if v p = 0 then c p else 0 := by
    apply hc.of_norm_bounded
    intro p
    split_ifs <;> simp
  have hdiag : (∑' p, if v p = 0 then c p else 0) =
      ((∑' i, if (w i).re = β then ‖b i‖ ^ 2 else 0 : ℝ) : ℂ) := by
    rw [hdiagSum.tsum_prod, Complex.ofReal_tsum]
    apply tsum_congr
    intro i
    by_cases hi : (w i).re = β
    · simp [hzero, hi, c, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    · simp [hzero, hi]
  apply Filter.tendsto_ofReal_iff.mp
  rw [← hdiag]
  apply (tendsto_abel_expSeries v c hv hc).congr
  intro ε
  rw [Complex.ofReal_mul, ← integral_complex_ofReal]
  apply congrArg ((ε : ℂ) * ·)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  change Complex.exp (-(ε : ℂ) * y) * (∑' p, c p * Complex.exp (v p * y)) =
    ((Real.exp (-(ε + 2 * β) * y) * ‖∑' i, b i * Complex.exp (w i * y)‖ ^ 2 : ℝ) : ℂ)
  rw [show (∑' p, c p * Complex.exp (v p * y)) = _ from
    expSeries_pair_sum w b β hw hb y (le_of_lt hy), Complex.ofReal_mul, Complex.ofReal_exp,
    ← mul_assoc, ← Complex.exp_add]
  have hexp : -(ε : ℂ) * y + -(2 * (β : ℂ)) * y = ((-(ε + 2 * β) * y : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexp]

/-- The squared Abel limit as a nonnegative integral over the closed half-line. -/
theorem tendsto_abel_lintegral_normSq_expSeries {ι : Type*} [Countable ι]
    (w b : ι → ℂ) (β : ℝ) (hinj : Function.Injective w)
    (hw : ∀ i, (w i).re ≤ β) (hb : Summable fun i ↦ ‖b i‖) :
    Tendsto (fun ε : ℝ ↦ ENNReal.ofReal ε * ∫⁻ y : ℝ in Ici 0,
      ENNReal.ofReal (‖∑' i, b i * Complex.exp (w i * y)‖ ^ 2 * Real.exp (-(ε + 2 * β) * y)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (∑' i, if (w i).re = β then ‖b i‖ ^ 2 else 0))) := by
  have hl := tendsto_abel_normSq_expSeries w b β hinj hw hb
  apply ((ENNReal.continuous_ofReal.tendsto _).comp hl).congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  change ENNReal.ofReal (ε * _) = _
  rw [ENNReal.ofReal_mul hε.le, ofReal_integral_eq_lintegral_ofReal
    (integrableOn_abel_normSq_expSeries w b β hw hb hε)
      (Eventually.of_forall fun y ↦ mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
  rw [restrict_Ioi_eq_restrict_Ici]
  congr 1
  exact lintegral_congr fun y ↦ congrArg ENNReal.ofReal (mul_comm _ _)

end RiemannMasullo.AbelEdge
