module

public import RiemannMasullo.AppB_AnalyticNT.HeckeLogReference
public import RiemannMasullo.AppB_AnalyticNT.Sec4b_BoundaryHeckeGreen
public import RiemannMasullo.AppB_AnalyticNT.Sec4b_HeckeVerticalDisks
public import RiemannMasullo.ForMathlib.Analysis.Complex.VerticalLogTail
public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.DyadicLogTail
public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.PoissonLogTail

/-! # The finite ideal logarithmic measurement of the right-hand Green sum

The ordinary critical-line logarithm has a square-root-exponential integrated tail
for the Cauchy measure. This bounds the error of the norm-ordered finite tables
approximating the full Green sum of a fixed normalized character.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField
open scoped NNReal Topology

namespace RiemannMasullo.LogQuadrature

open HalfPlaneJensen HeckeBoundaryGreen HeckeHalfPlaneJensen PolynomialIdealSamples

variable {F : Type*} [Field F] [NumberField F]
local notation "CF" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual CF

private theorem weightedLog_eq (L : ℂ → ℂ) :
    weightedLog L = fun t ↦ poissonWeight t * Real.log ‖L (point t)‖ := by
  funext t
  have hp : (1/2 : ℂ) + (t : ℂ) * I = point t := by
    apply Complex.ext <;> simp [point, Complex.mul_re, Complex.mul_im]
  simp only [weightedLog, poissonWeight, hp]

/-- The fully finite ideal measurement converges to the genuine, pole-corrected boundary
mean for every normalized character. -/
theorem tendsto_finiteLogDifference_criticalLogDifference (τ : ℝ≥0ˣ →ₜ* CF)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) :
    Tendsto (finiteLogDifference χ) atTop (𝓝 (criticalLogDifference χ)) := by
  let L := (finiteHeckeL_exists_continuation χ).choose
  obtain ⟨hL, he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hlog := (integrable_weightedLog_and_green τ hτ χ hχ L hL he).1
  rw [weightedLog_eq] at hlog
  simpa only [criticalLogDifference, weightedLog_eq] using
    tendsto_finiteLogDifference τ hτ χ hχ hlog

/-- All right-hand completed divisor sites, with their multiplicities, sum to the limit
of the finite ideal measurement at two. -/
theorem hasSum_green_limit_finiteLogDifference (τ : ℝ≥0ˣ →ₜ* CF)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) :
    HasSum (fun z : RightSite χ ↦ (order χ z.val : ℝ) * greenKernel z.val)
      (limUnder atTop (finiteLogDifference χ)) := by
  rw [(tendsto_finiteLogDifference_criticalLogDifference τ hτ χ hχ).limUnder_eq]
  exact hasSum_green_criticalLogDifference τ hτ χ hχ


/-- A square-root-exponential tail for the true logarithm gives a rate for the signed
finite ideal measurement, including the finite Euler reference and principal correction. -/
theorem finiteLogDifference_rate_of_logTail (τ : ℝ≥0ˣ →ₜ* CF)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1)
    (htail : HasIntegratedLogTail poissonMeasure (fun t ↦ Real.log
      ‖(finiteHeckeL_exists_continuation χ).choose (point t)‖)) :
    ∃ C > 0, ∃ c > 0, ∀ n : ℕ,
      |finiteLogDifference χ n - criticalLogDifference χ| ≤
        C * Real.exp (-c * Real.sqrt (Real.log n)) := by
  classical
  let twoRight : {z : ℂ // 1 < z.re} := ⟨2, by norm_num⟩
  let L := (finiteHeckeL_exists_continuation χ).choose
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hlog := (integrable_weightedLog_and_green τ hτ χ hχ L hL he).1
  rw [weightedLog_eq] at hlog
  have hh := hasRootLogRate_heckeLogStatistic τ hτ χ hχ L hL he hlog htail
  apply HasRootLogRate.all_indices
  apply hh.of_eventually_add_inv (D := (Module.finrank ℚ F : ℝ)) (by positivity)
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hEuler := abs_eulerLogReference_sub χ hn
  have hp : L 2 = finiteHeckeL χ twoRight := he twoRight
  have hid : finiteLogDifference χ n - criticalLogDifference χ =
      (heckeLogStatistic χ n - ∫ t, poissonWeight t * Real.log ‖L (point t)‖) +
        (Real.log ‖finiteHeckeL χ twoRight‖-eulerLogReference χ n) := by
    rw [finiteLogDifference,criticalLogDifference,weightedLog_eq]
    change _ - ((∫ t, poissonWeight t * Real.log ‖L (point t)‖) - Real.log ‖L 2‖ +
      (if χ = 1 then Real.log 2 else 0)) = _
    rw [hp]
    ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add le_rfl hEuler)

/-- The true critical-line log modulus has an exponentially small Cauchy measure
above a quadratic sequence of thresholds. Both constants are for the given character. -/
theorem criticalLog_dyadic_tail (τ : ℝ≥0ˣ →ₜ* CF)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) :
    ∃ A > 0, ∃ B > 0, ∀ n : ℕ,
      poissonMeasure {t : ℝ | A * ((n : ℝ) + 1)^2 <
        |Real.log ‖(finiteHeckeL_exists_continuation χ).choose (point t)‖|} ≤
        ENNReal.ofReal (B * (1/2 : ℝ)^n) := by
  let L := (finiteHeckeL_exists_continuation χ).choose
  let g (j : ℤ) := HeckeVerticalDisk.translated χ L (j : ℝ)
  obtain ⟨K, hK, M, _, hwin⟩ := HeckeVerticalDisk.canonical_window_input τ hτ χ hχ
  have hcoord (j : ℤ) (t : ℝ) :
      (-5/6 : ℂ) + (((t-j)/(9/5) : ℝ) : ℂ) * I = HeckeVerticalDisk.criticalCoordinate j t := by
    have haxis (v : ℝ) : ((-5/6 : ℝ) : ℂ) + (v : ℂ) * I = ⟨-(5/6), v⟩ := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
      ring
    rw [show (-5/6 : ℂ) = ((-5/6 : ℝ) : ℂ) by norm_num, haxis]
    apply Complex.ext <;> norm_num [HeckeVerticalDisk.criticalCoordinate]
    ring
  obtain ⟨A, B, hA, hB, hd⟩ := LogTail.dyadic_log_tail_of_windows poissonMeasure
    (fun t ↦ Real.log ‖L (point t)‖) g (fun j ↦ M (j : ℝ)) (K := K)
    (by linarith) (by positivity) (by positivity) poissonMeasure_apply_le_volume
    poissonMeasure_abs_gt_two_pow (fun j ↦ (hwin j).2.1) (fun j ↦ (hwin j).1)
    (fun j ↦ norm_pos_iff.mp (hwin j).2.2.1) (fun j ↦ (hwin j).2.2.2.1)
    (fun j ↦ (hwin j).2.2.2.2.1) (fun j ↦ (hwin j).2.2.2.2.2.1) (by
      intro j t ht
      rw [hcoord]
      exact congrArg Real.log ((hwin j).2.2.2.2.2.2 t ht).2.symm)
  exact ⟨A, hA, B, hB, hd⟩

/-- Absolute large values of the actual boundary logarithm have a
square-root-exponential integrated tail against the reference Cauchy measure. -/
theorem hasIntegratedLogTail_criticalLog (τ : ℝ≥0ˣ →ₜ* CF)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) :
    HasIntegratedLogTail poissonMeasure
      (fun t ↦ Real.log ‖(finiteHeckeL_exists_continuation χ).choose (point t)‖) := by
  let L := (finiteHeckeL_exists_continuation χ).choose
  obtain ⟨hL, he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hd := (hecke_critical_deriv_polynomial τ hτ χ hχ L hL he).1
  have hlog := (integrable_weightedLog_and_green τ hτ χ hχ L hL he).1
  rw [weightedLog_eq] at hlog
  exact hasIntegratedLogTail_of_dyadic_sq poissonMeasure
    (Real.measurable_log.comp hd.continuous.norm.measurable) ((poisson_integrable_iff _).mpr hlog)
    (criticalLog_dyadic_tail τ hτ χ hχ)

/-- For each normalized character the error of the finite ideal logarithmic statistic
is at most `C exp (−c √(log n))` at every index. The constants may depend on the
field and the character. -/
theorem finiteLogDifference_rate (τ : ℝ≥0ˣ →ₜ* CF)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) :
    ∃ C > 0, ∃ c > 0, ∀ n : ℕ, |finiteLogDifference χ n - criticalLogDifference χ| ≤
      C * Real.exp (-c * Real.sqrt (Real.log n)) :=
  finiteLogDifference_rate_of_logTail τ hτ χ hχ (hasIntegratedLogTail_criticalLog τ hτ χ hχ)

end RiemannMasullo.LogQuadrature
