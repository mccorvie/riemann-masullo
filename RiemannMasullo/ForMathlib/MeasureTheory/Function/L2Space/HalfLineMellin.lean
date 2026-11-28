module
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

public noncomputable section
open MeasureTheory Set Function Filter FourierTransform
open scoped Topology FourierTransform
namespace RiemannMasullo

private theorem integrableOn_pow_exp_neg (a : ℝ) (r : ℕ) :
    IntegrableOn (fun x : ℝ ↦ x ^ r * Real.exp (-x)) (Ici a) := by
  have hi : IntegrableOn (fun x : ℝ ↦ x ^ r * Real.exp (-x)) (Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one, neg_one_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (r : ℝ)) (p := 1) (b := 1)
        (by have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith) zero_lt_one zero_lt_one)
  have hc : Continuous (fun x : ℝ ↦ x ^ r * Real.exp (-x)) := by fun_prop
  apply (hc.integrableOn_Icc.union hi).mono_set
  intro x hx
  by_cases hx0 : x ≤ 0
  · exact Or.inl ⟨hx, hx0⟩
  · exact Or.inr (lt_of_not_ge hx0)

private def halfLineMomentWindow (a : ℝ) (r : ℕ) (x : ℝ) : ℂ :=
  (Ici a).indicator (fun x : ℝ ↦ ((x ^ r * Real.exp (-x/2) : ℝ) : ℂ)) x

private theorem halfLineMomentWindow_memLp (a : ℝ) (r : ℕ) :
    MemLp (halfLineMomentWindow a r) 2 (volume : Measure ℝ) := by
  have hm : Measurable (halfLineMomentWindow a r) :=
    (show Continuous (fun x : ℝ ↦ ((x ^ r * Real.exp (-x/2) : ℝ) : ℂ)) by fun_prop).measurable.indicator
      measurableSet_Ici
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply ((integrableOn_pow_exp_neg a (2*r)).integrable_indicator measurableSet_Ici).congr
  filter_upwards with x
  by_cases hx : x ∈ Ici a
  · simp only [halfLineMomentWindow, indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, mul_pow, ← Real.exp_nat_mul]
    norm_cast
    rw [show (2 : ℝ) * (-x / 2) = -x by ring, ← pow_mul]
    congr 2
    omega
  · simp [halfLineMomentWindow, hx]

private def halfLineMellinJetProfile (a ξ : ℝ) (r : ℕ) (x : ℝ) : ℂ :=
  halfLineMomentWindow a r x * (Real.fourierChar (x * ξ) : ℂ)

private theorem halfLineMellinJetProfile_memLp (a ξ : ℝ) (r : ℕ) :
    MemLp (halfLineMellinJetProfile a ξ r) 2 (volume : Measure ℝ) := by
  have hc : Continuous (fun x : ℝ ↦ (Real.fourierChar (x * ξ) : ℂ)) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_id.mul continuous_const))
  apply (halfLineMomentWindow_memLp a r).of_le
    ((halfLineMomentWindow_memLp a r).aestronglyMeasurable.mul hc.aestronglyMeasurable)
  filter_upwards with x
  change ‖halfLineMomentWindow a r x * (Real.fourierChar (x * ξ) : ℂ)‖ ≤ _
  rw [norm_mul, Circle.norm_coe, mul_one]

/-- Every polynomial Mellin row on a fixed lower half-line is a bounded
functional on the ordinary logarithmic `L²` space. -/
def halfLineMellinJet (a ξ : ℝ) (r : ℕ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] ℂ :=
  innerSL ℂ ((halfLineMellinJetProfile_memLp a ξ r).toLp (halfLineMellinJetProfile a ξ r))

/-- The Hilbert row agrees with the actual Fourier transform of the damped
polynomial moment whenever the input vanishes below the fixed support edge. -/
theorem halfLineMellinJet_apply (a ξ : ℝ) (r : ℕ) (F : Lp ℂ 2 (volume : Measure ℝ))
    (hF : ∀ᵐ x ∂volume, x < a → F x = 0) :
    halfLineMellinJet a ξ r F = 𝓕 (fun x : ℝ ↦ (x : ℂ)^r * (Real.exp (-x/2) : ℂ) * F x) ξ := by
  change inner ℂ ((halfLineMellinJetProfile_memLp a ξ r).toLp (halfLineMellinJetProfile a ξ r)) F = _
  rw [L2.inner_def, Real.fourier_real_eq]
  apply integral_congr_ae
  filter_upwards [(halfLineMellinJetProfile_memLp a ξ r).coeFn_toLp, hF] with x hx hFx
  rw [hx, RCLike.inner_apply, Circle.smul_def, smul_eq_mul]
  by_cases hxa : a ≤ x
  · have hw : halfLineMomentWindow a r x = ((x ^ r * Real.exp (-x/2) : ℝ) : ℂ) :=
      indicator_of_mem (mem_Ici.mpr hxa) _
    rw [halfLineMellinJetProfile, map_mul, hw, Complex.conj_ofReal]
    have hchar : (starRingEnd ℂ) (Real.fourierChar (x * ξ) : ℂ) =
        (Real.fourierChar (-(x * ξ)) : ℂ) := by
      simp only [Real.fourierChar_apply, ← Complex.exp_conj, map_mul,
        Complex.conj_ofReal, Complex.conj_I, mul_neg]
      congr 1
      push_cast
      ring
    rw [hchar]
    push_cast
    ring
  · rw [hFx (lt_of_not_ge hxa)]
    simp

/-- On a fixed lower half-line, exponential damping makes every polynomial
moment of an `L²` function integrable. -/
theorem halfLineMellin_moment_integrable (a : ℝ) (r : ℕ)
    (F : Lp ℂ 2 (volume : Measure ℝ))
    (hF : ∀ᵐ x ∂volume, x < a → F x = 0) :
    Integrable (fun x : ℝ ↦ (x : ℂ)^r * (Real.exp (-x/2) : ℂ) * F x) := by
  apply ((halfLineMomentWindow_memLp a r).integrable_mul (Lp.memLp F)).congr
  filter_upwards [hF] with x hx
  change halfLineMomentWindow a r x * F x = (x : ℂ)^r * (Real.exp (-x/2) : ℂ) * F x
  by_cases hxa : a ≤ x
  · rw [halfLineMomentWindow, indicator_of_mem (mem_Ici.mpr hxa)]
    push_cast
    rfl
  · rw [hx (lt_of_not_ge hxa)]
    simp

/-- Fourier derivatives of a damped lower-supported Hilbert vector are the
bounded Mellin jet rows, with the standard `-2πI` normalization. -/
theorem iteratedDeriv_fourier_halfLine (a ξ : ℝ) (r : ℕ)
    (F : Lp ℂ 2 (volume : Measure ℝ))
    (hF : ∀ᵐ x ∂volume, x < a → F x = 0) :
    iteratedDeriv r (𝓕 (fun x : ℝ ↦ (Real.exp (-x/2) : ℂ) * F x)) ξ =
      (-2 * (Real.pi : ℂ) * Complex.I)^r * halfLineMellinJet a ξ r F := by
  have hi (n : ℕ) (_ : n ≤ (⊤ : ℕ∞)) :
      Integrable (fun x : ℝ ↦ x^n • ((Real.exp (-x/2) : ℂ) * F x)) := by
    simpa only [Complex.real_smul, Complex.ofReal_pow, mul_assoc] using
      halfLineMellin_moment_integrable a n F hF
  rw [Real.iteratedDeriv_fourier hi (show r ≤ (⊤ : ℕ∞) by simp),
    halfLineMellinJet_apply a ξ r F hF]
  have heq : (fun x : ℝ ↦ (-2 * Real.pi * Complex.I * x)^r •
      ((Real.exp (-x/2) : ℂ) * F x)) =
      (-2 * (Real.pi : ℂ) * Complex.I)^r •
        (fun x : ℝ ↦ (x : ℂ)^r * (Real.exp (-x/2) : ℂ) * F x) := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    ring
  rw [heq, Real.fourier_eq, Real.fourier_eq]
  simp only [Pi.smul_apply]
  simp_rw [smul_comm _ ((-2 * (Real.pi : ℂ) * Complex.I)^r)]
  rw [integral_smul]
  rfl

/-- Lower support and exponential damping give a smooth Fourier transform for
every logarithmic `L²` vector, without any smoothness assumption on that vector. -/
theorem contDiff_fourier_halfLine (a : ℝ) (F : Lp ℂ 2 (volume : Measure ℝ))
    (hF : ∀ᵐ x ∂volume, x < a → F x = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (𝓕 (fun x : ℝ ↦ (Real.exp (-x/2) : ℂ) * F x)) := by
  apply Real.contDiff_fourier
  intro n hn
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_assoc] using
    (halfLineMellin_moment_integrable a n F hF).norm

end RiemannMasullo
