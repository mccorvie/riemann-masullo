module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Derivatives of the two-sided Laplace transform

Polynomial moments give the strip derivatives of every finite order. Vertical-line
Plancherel and Tonelli then give a weighted area identity for each derivative.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Complex Set
open scoped Topology ENNReal Real

namespace RiemannMasullo

variable {f : ℝ → ℂ} {α : ℝ}

/-- Any polynomial moment retains exponential square integrability inside a smaller strip. -/
theorem memLp_exp_abs_smul_pow_mul
    (hf : MemLp (fun x : ℝ ↦ Real.exp (α * |x|) • f x) 2) (k : ℕ) {β : ℝ} (hβ : β < α) :
    MemLp (fun x : ℝ ↦ Real.exp (β * |x|) • ((x : ℂ)^k * f x)) 2 := by
  induction k generalizing β with
  | zero =>
    simp only [pow_zero, one_mul]
    have hm := aestronglyMeasurable_of_exp_abs_smul hf.aestronglyMeasurable
    refine hf.of_le_mul (c := 1)
      ((by fun_prop : Continuous fun x : ℝ ↦ Real.exp (β * |x|)).aestronglyMeasurable.smul hm)
      (.of_forall fun x ↦ ?_)
    rw [one_mul, norm_smul, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hβ.le (abs_nonneg x))) (norm_nonneg _)
  | succ k ih =>
    obtain ⟨γ, hβγ, hγα⟩ := exists_between hβ
    simpa only [pow_succ', mul_assoc] using memLp_exp_abs_smul_id_mul (ih hγα) hβγ

/-- Every derivative in the open strip is the Laplace transform of the corresponding moment. -/
theorem iteratedDeriv_bilateralLaplace_eq_moment
    (hf : MemLp (fun x : ℝ ↦ Real.exp (α * |x|) • f x) 2) (k : ℕ) {z : ℂ} (hz : |z.re| < α) :
    iteratedDeriv k (bilateralLaplace f) z = bilateralLaplace (fun x : ℝ ↦ (x : ℂ)^k * f x) z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    have hnear : ∀ᶠ w : ℂ in 𝓝 z, |w.re| < α :=
      (continuous_abs.comp Complex.continuous_re).continuousAt.eventually (Iio_mem_nhds hz)
    have he : iteratedDeriv k (bilateralLaplace f) =ᶠ[𝓝 z]
        bilateralLaplace (fun x : ℝ ↦ (x : ℂ)^k * f x) := hnear.mono fun _ hw ↦ ih hw
    obtain ⟨β, hzβ, hβα⟩ := exists_between hz
    rw [iteratedDeriv_succ, he.deriv_eq,
      deriv_bilateralLaplace (memLp_exp_abs_smul_pow_mul hf k hβα) hzβ]
    simp only [pow_succ', mul_assoc]

/-- The derivatives of a bilateral Laplace transform are continuous on its open strip. -/
theorem continuousOn_iteratedDeriv_bilateralLaplace
    (hf : MemLp (fun x : ℝ ↦ Real.exp (α * |x|) • f x) 2) (k : ℕ) :
    ContinuousOn (iteratedDeriv k (bilateralLaplace f)) {z : ℂ | |z.re| < α} := by
  intro z hz
  change |z.re| < α at hz
  obtain ⟨β, hzβ, hβα⟩ := exists_between hz
  have hnear : ∀ᶠ w : ℂ in 𝓝 z, |w.re| < α :=
    (continuous_abs.comp Complex.continuous_re).continuousAt.eventually (Iio_mem_nhds hz)
  have he : iteratedDeriv k (bilateralLaplace f) =ᶠ[𝓝 z]
      bilateralLaplace (fun x : ℝ ↦ (x : ℂ)^k * f x) :=
    hnear.mono fun _ hw ↦ iteratedDeriv_bilateralLaplace_eq_moment hf k hw
  have hc : ContinuousAt (bilateralLaplace (fun x : ℝ ↦ (x : ℂ)^k * f x)) z :=
    (hasDerivAt_bilateralLaplace (memLp_exp_abs_smul_pow_mul hf k hβα) hzβ).continuousAt
  exact (hc.congr he.symm).continuousWithinAt

/-- Plancherel's identity for derivatives of every order on an interior vertical line. -/
theorem lintegral_enorm_sq_iteratedDeriv_bilateralLaplace
    (hf : MemLp (fun x : ℝ ↦ Real.exp (α * |x|) • f x) 2) (k : ℕ) {σ : ℝ} (hσ : |σ| < α) :
    ∫⁻ t : ℝ, ‖iteratedDeriv k (bilateralLaplace f) (σ + t * I)‖ₑ ^ 2 =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ 2 *
        ENNReal.ofReal ((x^k)^2 * Real.exp (2 * σ * x)) := by
  obtain ⟨β, hσβ, hβα⟩ := exists_between hσ
  have hre (t : ℝ) : |((σ : ℂ) + t * I).re| < α := by simpa using hσ
  simp_rw [iteratedDeriv_bilateralLaplace_eq_moment hf k (hre _)]
  rw [lintegral_enorm_sq_bilateralLaplace (memLp_exp_abs_smul_pow_mul hf k hβα) hσβ]
  congr 1
  refine lintegral_congr fun x ↦ ?_
  have hx : ‖(x : ℂ)^k‖ₑ ^ 2 = ENNReal.ofReal ((x^k)^2) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), norm_pow, Complex.norm_real,
      Real.norm_eq_abs, ← abs_pow, sq_abs]
  rw [eNorm_mul, mul_pow, hx, ENNReal.ofReal_mul (sq_nonneg _)]
  ac_rfl

/-- Weighted area Plancherel for a finite collection of strip derivatives. The weight
may be unbounded, so the identity is stated for lower Lebesgue integrals. -/
theorem lintegral_strip_sum_enorm_sq_iteratedDeriv_bilateralLaplace
    (hf : MemLp (fun x : ℝ ↦ Real.exp (α * |x|) • f x) 2) (J : Finset ℕ)
    {w : ℝ → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ σ in Ioo (-α) α, w σ * ∫⁻ t : ℝ,
      ∑ k ∈ J, ‖iteratedDeriv k (bilateralLaplace f) (σ + t * I)‖ₑ ^ 2 =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ 2 *
        (ENNReal.ofReal (∑ k ∈ J, (x^k)^2) *
          ∫⁻ σ in Ioo (-α) α, w σ * ENNReal.ofReal (Real.exp (2 * σ * x))) := by
  let c := ENNReal.ofReal (2 * Real.pi)
  let A (x : ℝ) := ‖f x‖ₑ ^ 2 * ENNReal.ofReal (∑ k ∈ J, (x^k)^2)
  let B (σ x : ℝ) := ENNReal.ofReal (Real.exp (2 * σ * x))
  have hA : AEMeasurable A :=
    ((aestronglyMeasurable_of_exp_abs_smul hf.aestronglyMeasurable).eNorm.pow_const 2).mul
      (by fun_prop : Measurable fun x : ℝ ↦ ENNReal.ofReal (∑ k ∈ J, (x^k)^2)).aemeasurable
  have hB : Measurable (Function.uncurry B) := by unfold B Function.uncurry; fun_prop
  have hAB (σ : ℝ) : AEMeasurable fun x ↦ A x * B σ x :=
    hA.mul (hB.comp (measurable_const.prodMk measurable_id)).aemeasurable
  have hprod : AEMeasurable (fun p : ℝ × ℝ ↦ w p.1 * (c * (A p.2 * B p.1 p.2)))
      ((volume.restrict (Ioo (-α) α)).prod volume) :=
    (hw.comp measurable_fst).aemeasurable.mul (aemeasurable_const.mul
      ((hA.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul hB.aemeasurable))
  calc
    _ = ∫⁻ σ in Ioo (-α) α, ∫⁻ x : ℝ, w σ * (c * (A x * B σ x)) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun σ hσ ↦ ?_
      have hs : |σ| < α := abs_lt.mpr hσ
      have hm (k : ℕ) : Measurable (fun t : ℝ ↦
          ‖iteratedDeriv k (bilateralLaplace f) (σ + t * I)‖ₑ ^ 2) := by
        have hc : Continuous (fun t : ℝ ↦ (σ : ℂ) + t * I) := by fun_prop
        have ht : MapsTo (fun t : ℝ ↦ (σ : ℂ) + t * I) univ {z : ℂ | |z.re| < α} :=
          fun _ _ ↦ by simpa using hs
        have hline : Continuous (fun t : ℝ ↦ iteratedDeriv k (bilateralLaplace f) (σ + t * I)) :=
          continuousOn_univ.mp ((continuousOn_iteratedDeriv_bilateralLaplace hf k).comp hc.continuousOn ht)
        exact hline.measurable.eNorm.pow_const 2
      have hp (k : ℕ) : AEMeasurable (fun x : ℝ ↦ ‖f x‖ₑ ^ 2 *
          ENNReal.ofReal ((x^k)^2 * Real.exp (2 * σ * x))) :=
        ((aestronglyMeasurable_of_exp_abs_smul hf.aestronglyMeasurable).eNorm.pow_const 2).mul
          (by fun_prop : Measurable fun x : ℝ ↦
            ENNReal.ofReal ((x^k)^2 * Real.exp (2 * σ * x))).aemeasurable
      rw [lintegral_finsetSum J (fun k _ ↦ hm k)]
      simp_rw [lintegral_enorm_sq_iteratedDeriv_bilateralLaplace hf _ hs]
      rw [← Finset.mul_sum, ← lintegral_finsetSum' J (fun k _ ↦ hp k)]
      have hbody : (fun x : ℝ ↦ ∑ k ∈ J, ‖f x‖ₑ ^ 2 *
          ENNReal.ofReal ((x^k)^2 * Real.exp (2 * σ * x))) = fun x ↦ A x * B σ x := by
        funext x
        simp only [A, B, ENNReal.ofReal_mul (sq_nonneg _), ← mul_assoc, ← Finset.sum_mul,
          ← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ sq_nonneg (x ^ k))]
      rw [hbody, lintegral_const_mul'' (w σ) ((hAB σ).const_mul c), lintegral_const_mul'' c (hAB σ)]
    _ = ∫⁻ x : ℝ, ∫⁻ σ in Ioo (-α) α, w σ * (c * (A x * B σ x)) :=
      lintegral_lintegral_swap hprod
    _ = _ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro x
      have h (σ : ℝ) : w σ * (c * (A x * B σ x)) = (c * A x) * (w σ * B σ x) := by ac_rfl
      simp_rw [h]
      have hBx : Measurable (fun σ : ℝ ↦ B σ x) := by unfold B; fun_prop
      have hm : AEMeasurable (fun σ ↦ w σ * B σ x) (volume.restrict (Ioo (-α) α)) :=
        (hw.mul hBx).aemeasurable
      calc
        _ = (c * A x) * ∫⁻ σ in Ioo (-α) α, w σ * B σ x := lintegral_const_mul'' _ hm
        _ = _ := by simp only [A, B, c, mul_assoc]

/-- The weighted area identity for a single strip derivative. -/
theorem lintegral_strip_enorm_sq_iteratedDeriv_bilateralLaplace
    (hf : MemLp (fun x : ℝ ↦ Real.exp (α * |x|) • f x) 2) (k : ℕ)
    {w : ℝ → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ σ in Ioo (-α) α, w σ * ∫⁻ t : ℝ,
      ‖iteratedDeriv k (bilateralLaplace f) (σ + t * I)‖ₑ ^ 2 =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ 2 *
        (ENNReal.ofReal ((x^k)^2) * ∫⁻ σ in Ioo (-α) α, w σ * ENNReal.ofReal (Real.exp (2 * σ * x))) := by
  simpa only [Finset.sum_singleton] using
    lintegral_strip_sum_enorm_sq_iteratedDeriv_bilateralLaplace hf {k} hw

end RiemannMasullo
