module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.QuadraticBoxLaplace
public import RiemannMasullo.ForMathlib.Analysis.Fourier.SmoothCharacteristicDensity
public import RiemannMasullo.ForMathlib.Analysis.Fourier.TranslatedPolarProfile
public import RiemannMasullo.ForMathlib.Probability.Distributions.UniformIntervalSeries

/-! # A compact Gevrey-two profile for translated Laplace tests

The law is a sum of centered independent uniform variables with total support radius one.
Its Laplace transform does not vanish off the imaginary axis and has an explicit
square-root exponential bound on each closed strip. The translated derivative prescribes
the two polar moments and the central moment.

The quadratic-width compact convolution is classical, as in A. E. Ingham, *A note on
Fourier transforms* (1934). The earlier rational theta construction for issue #5571 used
radii `1 / (64 j²)`. The field-independent translated test in the same issue used the
dyadic Fabius law. Issue #5571, comment 7150535543, gives the telescoping radii and their
signed endpoint application in prose. This file proves their simultaneous analytic properties.
-/

open MeasureTheory Set
open scoped ContDiff

@[expose] public noncomputable section

namespace RiemannMasullo

/-- The bilateral Laplace transform of the independent quadratic-width box law. -/
theorem integral_cexp_quadraticBoxLaw (z : ℂ) :
    (∫ x : ℝ, Complex.exp (z * x) ∂IntervalBoxLaw.law quadraticBoxRadius) =
      quadraticBoxLaplace z :=
  (IntervalBoxLaw.hasProd_laplace (fun n ↦ (quadraticBoxRadius_pos n).le)
    hasSum_quadraticBoxRadius z).tprod_eq.symm

private theorem quadraticBoxLaplace_bound_on_strip {B : ℝ} (z : ℂ) (hz : |z.re| ≤ B) :
    ‖quadraticBoxLaplace z‖ ≤
      2 * Real.exp B * Real.exp (-(Real.log 2 / 2) * Real.sqrt |z.im|) := by
  refine (norm_quadraticBoxLaplace_le z).trans ?_
  gcongr

/-- The explicit box product is realized by an even, nonnegative smooth probability density
supported on the unit interval centered at the origin. The identity holds for every complex
Laplace argument. -/
theorem exists_quadraticBoxDensity :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ (∀ x, 0 ≤ g x) ∧ Function.Even g ∧
      tsupport g ⊆ Icc (-1) 1 ∧ (∫ x, g x) = 1 ∧
      volume.withDensity (fun x ↦ ENNReal.ofReal (g x)) = IntervalBoxLaw.law quadraticBoxRadius ∧
      ∀ z : ℂ, bilateralLaplace (fun x ↦ (g x : ℂ)) z = quadraticBoxLaplace z := by
  let μ := IntervalBoxLaw.law quadraticBoxRadius
  have hnn (n : ℕ) := (quadraticBoxRadius_pos n).le
  have hmass : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 :=
    Filter.mem_of_superset μ.support_mem_ae
      (IntervalBoxLaw.support_law_subset hnn hasSum_quadraticBoxRadius)
  have hchar (t : ℝ) : charFun μ t = quadraticBoxLaplace ((t : ℂ) * Complex.I) := by
    rw [charFun_apply_real, ← integral_cexp_quadraticBoxLaw]
    congr 1
    funext x
    congr 1
    ring
  have hbound (t : ℝ) : ‖charFun μ t‖ ≤
      2 * Real.exp (-(Real.log 2 / 2) * Real.sqrt |t|) := by
    rw [hchar]
    simpa using norm_quadraticBoxLaplace_le ((t : ℂ) * Complex.I)
  obtain ⟨g, hg, hg₀, hgs, hg₁, hd, he, hi⟩ := exists_smooth_density_of_charFun_sqrt_exp μ
    (IntervalBoxLaw.law_absolutelyContinuous hnn hasSum_quadraticBoxRadius
      (quadraticBoxRadius_pos 0).ne') hmass (by norm_num : 0 ≤ (2 : ℝ))
    (div_pos (Real.log_pos (by norm_num : 1 < (2 : ℝ))) two_pos) hbound
  exact ⟨g, hg, hg₀, he (IntervalBoxLaw.map_neg_law _), hgs, hg₁, hd, fun z ↦
    (hi (fun x ↦ Complex.exp (z * x))).trans (integral_cexp_quadraticBoxLaw z)⟩

/-- The box product is entire as the bilateral Laplace transform of its compact density. -/
theorem differentiable_quadraticBoxLaplace : Differentiable ℂ quadraticBoxLaplace := by
  obtain ⟨g, hg, _, _, hs, _, _, hG⟩ := exists_quadraticBoxDensity
  have hc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  have hc' : HasCompactSupport (fun x ↦ (g x : ℂ)) := hc.comp_left (g := Complex.ofReal) rfl
  rw [← funext hG]
  intro z
  let α := |z.re| + 1
  have hw : Continuous (fun x : ℝ ↦ Real.exp (α * |x|)) := by fun_prop
  have hmem : MemLp (fun x : ℝ ↦ Real.exp (α * |x|) • (g x : ℂ)) 2 :=
    (hw.smul (Complex.continuous_ofReal.comp hg.continuous)).memLp_of_hasCompactSupport
      hc'.smul_left
  exact (hasDerivAt_bilateralLaplace hmem (z := z) (by dsimp [α]; linarith)).differentiableAt

/-- The transform of the translated three-moment detector has an explicit positive lower bound
on a bounded window separated from both the imaginary axis and the polar moments. -/
theorem translatedIntervalMultiplier_lower_on_box {w : ℂ} {d η R : ℝ} (hd : 0 < d)
    (hη : 0 < η) (hdw : d ≤ |w.re|) (hstrip : |w.re| ≤ 1 / 2 - η)
    (hwR : ‖w‖ ≤ R) (hR : 1 ≤ R) :
    Real.exp (-(3 / 2)) * d * (η * (1 - η)) *
      ((d / R) ^ ⌈Real.sqrt R⌉₊ * Real.exp (-(Real.sqrt R / 3))) ≤
        ‖translatedIntervalMultiplier quadraticBoxLaplace w‖ := by
  exact translatedIntervalMultiplier_norm_lower hd.le hη.le (by positivity) hdw hstrip
    (quadraticBoxLaplace_lower_on_box hd hdw hwR hR)

/-- A density realizing the explicit product yields the one translated test and its
Gevrey-two envelope, with both polar moments and the central moment annihilated. -/
theorem translatedMomentDerivative_quadraticBoxLaplace {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hs : tsupport g ⊆ Icc (-1) 1)
    (hG : ∀ z : ℂ, bilateralLaplace (fun x ↦ (g x : ℂ)) z = quadraticBoxLaplace z) :
    let H := translatedMomentDerivative g
    let M := bilateralLaplace (fun x ↦ (H x : ℂ))
    ContDiff ℝ ∞ H ∧ tsupport H ⊆ Icc 2 4 ∧
      (M (-(1/2)) = 0 ∧ M 0 = 0 ∧ M (1/2) = 0) ∧
      (∀ z : ℂ, 0 < |z.re| → |z.re| < 1/2 → M z ≠ 0) ∧
      ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, |z.re| ≤ B →
        ‖M z‖ ≤ C * Real.exp (-(Real.log 2 / 4) * Real.sqrt |z.im|) := by
  dsimp only
  have hc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  have hm : bilateralLaplace (fun x ↦ (translatedMomentDerivative g x : ℂ)) =
      translatedIntervalMultiplier quadraticBoxLaplace := by
    funext z
    rw [bilateralLaplace_translatedMomentDerivative hg hc, show bilateralLaplace
      (fun x ↦ (g x : ℂ)) = quadraticBoxLaplace from funext hG]
  rw [hm]
  exact ⟨contDiff_translatedMomentDerivative hg, tsupport_translatedMomentDerivative_subset hs,
    translatedIntervalMultiplier_polar_central _, translatedIntervalMultiplier_ne_zero _
      (fun _ hz ↦ quadraticBoxLaplace_ne_zero hz),
    fun B hB ↦ translatedIntervalMultiplier_strip_bound _ B hB quadraticBoxLaplace_bound_on_strip⟩

/-- One real smooth test on `[2,4]` annihilates all three moments, detects every off-axis
point of the open critical strip and has uniform square-root exponential decay on every
closed vertical strip. -/
theorem exists_translatedGevreyPolarProfile :
    ∃ H : ℝ → ℝ, let M := bilateralLaplace (fun x ↦ (H x : ℂ))
      M = translatedIntervalMultiplier quadraticBoxLaplace ∧
      ContDiff ℝ ∞ H ∧ tsupport H ⊆ Icc 2 4 ∧
      (M (-(1/2)) = 0 ∧ M 0 = 0 ∧ M (1/2) = 0) ∧
      (∀ z : ℂ, 0 < |z.re| → |z.re| < 1/2 → M z ≠ 0) ∧
      ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, |z.re| ≤ B →
        ‖M z‖ ≤ C * Real.exp (-(Real.log 2 / 4) * Real.sqrt |z.im|) := by
  obtain ⟨g, hg, _, _, hs, _, _, hG⟩ := exists_quadraticBoxDensity
  have hc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  refine ⟨translatedMomentDerivative g, funext fun z ↦ ?_,
    translatedMomentDerivative_quadraticBoxLaplace hg hs hG⟩
  rw [bilateralLaplace_translatedMomentDerivative hg hc, funext hG]

end RiemannMasullo
