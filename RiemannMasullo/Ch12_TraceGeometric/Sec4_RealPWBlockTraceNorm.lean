module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWPrimeTrace
public import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertFamilyTraceNorm
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Trace norm of the blocks of the cutoff twisted at a prime

Paper: Theorem 12.4.1.1, pp. 514–517, the terms of the finite places, for `F = ℚ` and
`S = {∞, p}`, in the unweighted model of #7354, as in `Sec4_RealPWPrimeTrace`.

`Sec4_RealPWPrimeTrace` computes the limit of the series `primeTraceSeries` of the traces of
the blocks `Q M_X A_{ψ_c} Q`. This file shows that the blocks, with their coefficients, add up
in trace norm to one nuclear operator on the band, and that the trace of that operator is the
series.

* `exists_traceNorm_le_of_halfProfile`. Two vector families on the line, one bounded on
  `[-X, X]` and one bounded by `|x| ^ (-1/2)` there, give an operator of trace norm at most a
  constant times `√X`.
* `norm_realPWTestRightFamily_le_halfProfile`. The right family of a block has the bound
  `|x| ^ (-1/2)`, by Cauchy–Schwarz in the dilation variable. No regularity of the test function
  is used.
* `realPWTest_adjoint_comp_eq_transpose`. A block is also given by its transposed family, which
  lives on `[-X / a, X / a]` when the test function is supported in `[a, b]`.
* `exists_bandBlock_nuclear`. A block has trace norm at most a constant times `√X`, and at
  most the same constant times `√(X / a)`.
* `exists_primeTwistedCutoff_nuclear`. For `r² p ≤ 1` the blocks add up in trace norm to a
  nuclear operator whose trace is `primeTraceSeries`.
* `exists_primeTwistedCutoff_trace_limit`. The trace of that operator, less its logarithmic
  term, converges to the real-place limit plus the term of the prime.

The block of the pair `(i, j)` has cutoff `X = L p ^ (i - 1)` and scale `c = p ^ (j - i)`, and
its coefficient has size `r ^ (i + j)`. For `i ≤ j` the first bound `√X` is enough. For `i > j`
the scaled test function is supported in `[a p ^ (i - j), b p ^ (i - j)]`, the first bound is
too large, and the second bound `√(X / (a p ^ (i - j)))` is used.

Reconstruction: The paper does not state this.

Deviation: The operator is given as the sum of its blocks. That this sum is
`Q (U⁻¹ M_L U) A_ψ Q`, and that this is the cutoff operator of Connes on the sector of
`L²(X_S)`, are on paper and are not formalized here. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology InnerProductSpace Real

namespace RiemannMasullo.Isolated

section Profile

/-- The profile `|x| ^ (-1/2)` on `[-X, X]`, the pointwise product of the bounds of the two
vector families of a block. -/
def halfProfile (X x : ℝ) : ℝ := ‖sharpIntervalMask X x‖ * |x| ^ (-(1 / 2 : ℝ))

/-- The sharp mask has norm one inside the interval. -/
theorem norm_sharpIntervalMask_of_abs_le {X x : ℝ} (h : |x| ≤ X) :
    ‖sharpIntervalMask X x‖ = 1 := by
  have hx : x ∈ Icc (-X) X := abs_le.mp h
  simp [sharpIntervalMask, hx]

/-- The sharp mask is one inside the interval. -/
theorem sharpIntervalMask_of_abs_le {X x : ℝ} (h : |x| ≤ X) : sharpIntervalMask X x = 1 := by
  have hx : x ∈ Icc (-X) X := abs_le.mp h
  simp [sharpIntervalMask, hx]

/-- The sharp mask vanishes outside the interval. -/
theorem sharpIntervalMask_of_lt_abs {X x : ℝ} (h : X < |x|) : sharpIntervalMask X x = 0 := by
  have hx : x ∉ Icc (-X) X := fun hx ↦ not_le.mpr h (abs_le.mpr hx)
  simp [sharpIntervalMask, hx]

/-- The sharp mask is real. -/
theorem star_sharpIntervalMask (X x : ℝ) :
    star (sharpIntervalMask X x) = sharpIntervalMask X x := by
  by_cases hx : x ∈ Icc (-X) X <;> simp [sharpIntervalMask, hx]

/-- The norm of the sharp mask is integrable. -/
theorem integrable_norm_sharpIntervalMask (X : ℝ) :
    Integrable fun x ↦ ‖sharpIntervalMask X x‖ :=
  (((continuous_const (y := (1 : ℂ))).integrableOn_Icc (a := -X) (b := X)).integrable_indicator
    measurableSet_Icc).norm

/-- The profile `halfProfile X` has integral `4 √X`. -/
theorem integral_halfProfile {X : ℝ} (hX : 0 < X) : ∫ x, halfProfile X x = 4 * √X := by
  have h1 : (fun x ↦ halfProfile X x) =
      fun x ↦ (Iic X).indicator (fun t : ℝ ↦ t ^ (-(1 / 2 : ℝ))) |x| := by
    funext x
    rw [halfProfile]
    by_cases h : |x| ≤ X
    · rw [norm_sharpIntervalMask_of_abs_le h, one_mul, indicator_of_mem (mem_Iic.mpr h)]
    · rw [sharpIntervalMask_of_lt_abs (not_le.mp h), norm_zero, zero_mul,
        indicator_of_notMem (by simpa using h)]
  rw [h1, integral_comp_abs (f := (Iic X).indicator fun t : ℝ ↦ t ^ (-(1 / 2 : ℝ))),
    setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic,
    ← intervalIntegral.integral_of_le hX.le, integral_rpow (Or.inl (by norm_num)),
    Real.sqrt_eq_rpow]
  norm_num
  ring

/-- The profile `halfProfile X` is integrable. -/
theorem integrable_halfProfile {X : ℝ} (hX : 0 < X) : Integrable (halfProfile X) :=
  Integrable.of_integral_ne_zero (by
    rw [integral_halfProfile hX]
    exact (mul_pos (by norm_num) (Real.sqrt_pos.mpr hX)).ne')

/-- Reconstruction: two families on the line, one bounded on `[-X, X]` and the other bounded
by `|x| ^ (-1/2)` there, both vanishing outside, give an operator `A_u† A_v` of trace norm at
most a constant times `√X`. The families are rescaled by `|x| ^ (-1/4)` and its inverse, after
which both have squared norm at most a constant times `halfProfile X`. -/
theorem exists_traceNorm_le_of_halfProfile {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [Countable ι] (b : HilbertBasis ι ℂ H)
    {μ : Measure ℝ} (hμ : μ = volume) {u v : ℝ → H} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    {A B X : ℝ} (hX : 0 < X) (hub : ∀ x, ‖u x‖ ≤ A * ‖sharpIntervalMask X x‖)
    (hvb : ∀ x, x ≠ 0 → ‖v x‖ ≤ B * halfProfile X x) :
    ∃ h : IsNuclearOperator
        ((hilbertFamilyAnalysisCLM hu).adjoint.comp (hilbertFamilyAnalysisCLM hv)),
      traceNorm ⟨(hilbertFamilyAnalysisCLM hu).adjoint.comp (hilbertFamilyAnalysisCLM hv), h⟩ ≤
        2 * (A ^ 2 + B ^ 2) * √X := by
  subst hμ
  let w : ℝ → ℝ := fun x ↦ |x| ^ (-(1 / 4 : ℝ))
  have hwm : Measurable w := continuous_abs.measurable.pow_const _
  have hne : ∀ᵐ x : ℝ, x ≠ 0 := by
    have h0 : ({0}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) :=
      compl_mem_ae_iff.mpr (measure_singleton 0)
    filter_upwards [h0] with x hx using hx
  have hw : ∀ᵐ x : ℝ, w x ≠ 0 := by
    filter_upwards [hne] with x hx
    exact (Real.rpow_pos_of_pos (abs_pos.mpr hx) _).ne'
  have hq : ∀ x : ℝ, |x| ^ (-(1 / 2 : ℝ)) = w x ^ 2 := by
    intro x
    change _ = (|x| ^ (-(1 / 4 : ℝ))) ^ 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]
    norm_num
  have hm : ∀ x, ‖sharpIntervalMask X x‖ * ‖sharpIntervalMask X x‖ =
      ‖sharpIntervalMask X x‖ := by
    intro x
    rw [← norm_mul, sharpIntervalMask_mul_self]
  have hI := integrable_halfProfile hX
  have hub' : ∀ x, ‖((w x : ℝ) : ℂ) • u x‖ ^ 2 ≤ A ^ 2 * halfProfile X x := by
    intro x
    have hw0 : 0 ≤ w x := Real.rpow_nonneg (abs_nonneg x) _
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hw0, halfProfile, hq x]
    have h1 := hub x
    calc (w x * ‖u x‖) ^ 2 = w x ^ 2 * ‖u x‖ ^ 2 := by ring
      _ ≤ w x ^ 2 * (A * ‖sharpIntervalMask X x‖) ^ 2 := by gcongr
      _ = A ^ 2 * ((‖sharpIntervalMask X x‖ * ‖sharpIntervalMask X x‖) * w x ^ 2) := by ring
      _ = A ^ 2 * (‖sharpIntervalMask X x‖ * w x ^ 2) := by rw [hm x]
  have hvb' : ∀ x, x ≠ 0 → ‖(((w x)⁻¹ : ℝ) : ℂ) • v x‖ ^ 2 ≤ B ^ 2 * halfProfile X x := by
    intro x hx
    have hw0 : 0 < w x := Real.rpow_pos_of_pos (abs_pos.mpr hx) _
    have h1 := hvb x hx
    rw [halfProfile, hq x] at h1 ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hw0.le)]
    calc ((w x)⁻¹ * ‖v x‖) ^ 2 = ((w x)⁻¹) ^ 2 * ‖v x‖ ^ 2 := by ring
      _ ≤ ((w x)⁻¹) ^ 2 * (B * (‖sharpIntervalMask X x‖ * w x ^ 2)) ^ 2 := by gcongr
      _ = B ^ 2 * ((‖sharpIntervalMask X x‖ * ‖sharpIntervalMask X x‖) * w x ^ 2) := by
          field_simp
      _ = B ^ 2 * (‖sharpIntervalMask X x‖ * w x ^ 2) := by rw [hm x]
  have hum : AEStronglyMeasurable (fun x ↦ ((w x : ℝ) : ℂ) • u x) volume :=
    (Complex.measurable_ofReal.comp hwm).aestronglyMeasurable.smul hu.aestronglyMeasurable
  have hvm : AEStronglyMeasurable (fun x ↦ (((w x)⁻¹ : ℝ) : ℂ) • v x) volume :=
    (Complex.measurable_ofReal.comp hwm.inv).aestronglyMeasurable.smul hv.aestronglyMeasurable
  have hui : Integrable (fun x ↦ ‖((w x : ℝ) : ℂ) • u x‖ ^ 2) :=
    (hI.const_mul (A ^ 2)).mono' (hum.norm.pow 2) (ae_of_all _ fun x ↦ by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hub' x)
  have hvi : Integrable (fun x ↦ ‖(((w x)⁻¹ : ℝ) : ℂ) • v x‖ ^ 2) :=
    (hI.const_mul (B ^ 2)).mono' (hvm.norm.pow 2) (by
      filter_upwards [hne] with x hx
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hvb' x hx)
  obtain ⟨hn, hle⟩ := exists_traceNorm_familyAnalysis_comp_le_of_weight b hu hv hw
    ((memLp_two_iff_integrable_sq_norm hum).2 hui) ((memLp_two_iff_integrable_sq_norm hvm).2 hvi)
  refine ⟨hn, hle.trans ?_⟩
  have h1 : ∫ x, ‖((w x : ℝ) : ℂ) • u x‖ ^ 2 ≤ A ^ 2 * (4 * √X) := by
    rw [← integral_halfProfile hX, ← integral_const_mul]
    exact integral_mono_ae hui (hI.const_mul _) (ae_of_all _ hub')
  have h2 : ∫ x, ‖(((w x)⁻¹ : ℝ) : ℂ) • v x‖ ^ 2 ≤ B ^ 2 * (4 * √X) := by
    rw [← integral_halfProfile hX, ← integral_const_mul]
    refine integral_mono_ae hvi (hI.const_mul _) ?_
    filter_upwards [hne] with x hx using hvb' x hx
  linarith

end Profile

section CauchySchwarz

/-- A vector whose pairings are bounded by `K ‖f‖` has norm at most `K`. -/
theorem norm_le_of_forall_norm_inner_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {v : H} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ f : H, ‖⟪v, f⟫_ℂ‖ ≤ K * ‖f‖) : ‖v‖ ≤ K := by
  have h1 := h v
  have e : ‖⟪v, v⟫_ℂ‖ = ‖v‖ ^ 2 := by simp [inner_self_eq_norm_sq_to_K]
  rw [e] at h1
  by_contra hlt
  rw [not_le] at hlt
  nlinarith [norm_nonneg v]

/-- Cauchy–Schwarz against a test function of the dilation with the half-density weight: an
integrand bounded by `‖φ g‖ √g ‖f₂ g‖` has integral at most the product of the weighted `L²`
norm of `φ` and the `L²` norm of `f₂`. -/
theorem norm_integral_le_of_norm_le_test_mul {a b : ℝ} (ha0 : 0 < a) {φ : ℝ → ℂ}
    (hφc : Continuous φ) (hφ0 : ∀ g ∉ Icc a b, φ g = 0) {f₂ : ℝ → ℂ} (h2 : MemLp f₂ 2)
    {G : ℝ → ℂ} (hG : ∀ g, ‖G g‖ ≤ ‖φ g‖ * √g * ‖f₂ g‖) :
    ‖∫ g, G g‖ ≤ √(∫ g, ‖φ g‖ ^ 2 * g) * √(∫ g, ‖f₂ g‖ ^ 2) := by
  let f₁ : ℝ → ℂ := fun g ↦ φ g * ((√g : ℝ) : ℂ)
  have h1c : Continuous f₁ := hφc.mul (Complex.continuous_ofReal.comp Real.continuous_sqrt)
  have h1s : HasCompactSupport f₁ :=
    HasCompactSupport.intro (K := Icc a b) isCompact_Icc fun g hg ↦ by simp [f₁, hφ0 g hg]
  have h1 : MemLp f₁ 2 := h1c.memLp_of_hasCompactSupport h1s
  have he : ENNReal.ofReal 2 = 2 := by simp
  have hH := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two (he ▸ h1) (he ▸ h2)
  simp only [← Real.sqrt_eq_rpow, Real.rpow_two] at hH
  have hn1 : ∀ g, ‖f₁ g‖ = ‖φ g‖ * √g := fun g ↦ by
    simp only [f₁]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg g)]
  have hval1 : ∫ g, ‖f₁ g‖ ^ 2 = ∫ g, ‖φ g‖ ^ 2 * g := by
    refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    change ‖f₁ g‖ ^ 2 = ‖φ g‖ ^ 2 * g
    rw [hn1 g]
    by_cases hg : 0 ≤ g
    · rw [mul_pow, Real.sq_sqrt hg]
    · have : φ g = 0 := hφ0 g fun h ↦ hg (ha0.le.trans h.1)
      simp [this]
  have hprod : Integrable fun g ↦ ‖f₁ g‖ * ‖f₂ g‖ := h1.norm.integrable_mul h2.norm
  calc ‖∫ g, G g‖ ≤ ∫ g, ‖G g‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ g, ‖f₁ g‖ * ‖f₂ g‖ :=
        integral_mono_of_nonneg (ae_of_all _ fun g ↦ norm_nonneg _) hprod
          (ae_of_all _ fun g ↦ by
            change ‖G g‖ ≤ ‖f₁ g‖ * ‖f₂ g‖
            rw [hn1 g]
            exact hG g)
    _ ≤ √(∫ g, ‖f₁ g‖ ^ 2) * √(∫ g, ‖f₂ g‖ ^ 2) := hH
    _ = √(∫ g, ‖φ g‖ ^ 2 * g) * √(∫ g, ‖f₂ g‖ ^ 2) := by rw [hval1]

/-- The integral of the square of a function along the inverted dilations of a point, for the
measure `dg / g²` on the positive half-line, is at most the integral of its square divided by
the modulus of the point. -/
theorem memLp_inv_mul_comp_inv_mul {F : ℝ → ℂ} (hFc : Continuous F)
    (hF : Integrable fun y ↦ ‖F y‖ ^ 2) {x : ℝ} (hx : x ≠ 0) :
    MemLp ((Ioi (0 : ℝ)).indicator fun g ↦ ((g⁻¹ : ℝ) : ℂ) * F (g⁻¹ * x)) 2 ∧
      ∫ g, ‖(Ioi (0 : ℝ)).indicator (fun g ↦ ((g⁻¹ : ℝ) : ℂ) * F (g⁻¹ * x)) g‖ ^ 2 ≤
        |x|⁻¹ * ∫ y, ‖F y‖ ^ 2 := by
  let f₂ : ℝ → ℂ := (Ioi (0 : ℝ)).indicator fun g ↦ ((g⁻¹ : ℝ) : ℂ) * F (g⁻¹ * x)
  let Gx : ℝ → ℝ := fun t ↦ ‖F (t * x)‖ ^ 2
  have hGx : Integrable Gx := hF.comp_mul_right' hx
  have h2m : AEStronglyMeasurable f₂ :=
    (((Complex.measurable_ofReal.comp measurable_inv).mul
      (hFc.measurable.comp (measurable_inv.mul_const x))).indicator
        measurableSet_Ioi).aestronglyMeasurable
  have hnorm2 : (fun g ↦ ‖f₂ g‖ ^ 2) = (Ioi (0 : ℝ)).indicator
      fun g : ℝ ↦ (|(-1 : ℝ)| * g ^ ((-1 : ℝ) - 1)) • Gx (g ^ (-1 : ℝ)) := by
    funext g
    by_cases hg : 0 < g
    · have hgm : g ∈ Ioi (0 : ℝ) := hg
      simp only [f₂, Gx, indicator_of_mem hgm]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hg.le),
        Real.rpow_neg_one, smul_eq_mul, abs_neg, abs_one, one_mul,
        show ((-1 : ℝ) - 1) = -2 by norm_num, Real.rpow_neg hg.le, Real.rpow_two]
      ring
    · have hgm : g ∉ Ioi (0 : ℝ) := hg
      simp [f₂, indicator_of_notMem hgm]
  have hint2 : IntegrableOn
      (fun g : ℝ ↦ (|(-1 : ℝ)| * g ^ ((-1 : ℝ) - 1)) • Gx (g ^ (-1 : ℝ))) (Ioi 0) :=
    (integrableOn_Ioi_comp_rpow_iff Gx (by norm_num : (-1 : ℝ) ≠ 0)).2 hGx.integrableOn
  have h2i : Integrable fun g ↦ ‖f₂ g‖ ^ 2 := by
    rw [hnorm2]
    exact hint2.integrable_indicator measurableSet_Ioi
  refine ⟨(memLp_two_iff_integrable_sq_norm h2m).2 h2i, ?_⟩
  change ∫ g, ‖f₂ g‖ ^ 2 ≤ _
  rw [hnorm2, integral_indicator measurableSet_Ioi,
    integral_comp_rpow_Ioi Gx (by norm_num : (-1 : ℝ) ≠ 0)]
  calc ∫ t in Ioi 0, Gx t ≤ ∫ t, Gx t :=
        setIntegral_le_integral hGx (ae_of_all _ fun t ↦ sq_nonneg _)
    _ = |x⁻¹| • ∫ y, ‖F y‖ ^ 2 := Measure.integral_comp_mul_right (fun y ↦ ‖F y‖ ^ 2) x
    _ = |x|⁻¹ * ∫ y, ‖F y‖ ^ 2 := by rw [abs_inv, smul_eq_mul]

/-- The half-density factor is the product of the square root and the inverse. -/
theorem rpow_neg_half_eq_sqrt_mul_inv {g : ℝ} (hg : 0 < g) :
    g ^ (-(1 / 2 : ℝ)) = √g * g⁻¹ := by
  have hs := Real.sq_sqrt hg.le
  have hs0 : √g ≠ 0 := (Real.sqrt_pos.mpr hg).ne'
  rw [Real.rpow_neg hg.le, ← Real.sqrt_eq_rpow]
  field_simp
  exact hs.symm

/-- Reconstruction: Cauchy–Schwarz for the action of a test function at one point. For a
continuous `φ` supported in `[a, b]`, `0 < a`, a continuous square-integrable `F` and
`x ≠ 0`, the integral of `φ g g ^ (-1/2) F (x / g)` has modulus at most the weighted `L²` norm
of `φ` times `|x| ^ (-1/2)` times the `L²` norm of `F`. -/
theorem norm_integral_test_dilate_le {a b : ℝ} (ha0 : 0 < a) {φ : ℝ → ℂ}
    (hφc : Continuous φ) (hφ0 : ∀ g ∉ Icc a b, φ g = 0) {F : ℝ → ℂ} (hFc : Continuous F)
    (hF : Integrable fun y ↦ ‖F y‖ ^ 2) {x : ℝ} (hx : x ≠ 0) :
    ‖∫ g, φ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F (g⁻¹ * x))‖ ≤
      √(∫ g, ‖φ g‖ ^ 2 * g) * √(|x|⁻¹ * ∫ y, ‖F y‖ ^ 2) := by
  obtain ⟨h2, hval2⟩ := memLp_inv_mul_comp_inv_mul hFc hF hx
  refine (norm_integral_le_of_norm_le_test_mul ha0 hφc hφ0 h2 fun g ↦ ?_).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hval2) (Real.sqrt_nonneg _))
  by_cases hg : 0 < g
  · have hgm : g ∈ Ioi (0 : ℝ) := hg
    rw [indicator_of_mem hgm, rpow_neg_half_eq_sqrt_mul_inv hg, norm_mul, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg g) (inv_nonneg.mpr hg.le)),
      Real.norm_of_nonneg (inv_nonneg.mpr hg.le)]
    exact le_of_eq (by ring)
  · have : φ g = 0 := hφ0 g fun h ↦ hg (ha0.trans_le h.1)
    simp [this]

/-- Reconstruction: Cauchy–Schwarz for the transposed action of a test function at one point.
An integrand bounded by `‖φ g‖ √g ‖F (g y)‖` has integral of modulus at most the weighted `L²`
norm of `φ` times `|y| ^ (-1/2)` times the `L²` norm of `F`. -/
theorem norm_integral_test_scale_le {a b : ℝ} (ha0 : 0 < a) {φ : ℝ → ℂ}
    (hφc : Continuous φ) (hφ0 : ∀ g ∉ Icc a b, φ g = 0) {F : ℝ → ℂ} (hFc : Continuous F)
    (hF : Integrable fun t ↦ ‖F t‖ ^ 2) {y : ℝ} (hy : y ≠ 0) {G : ℝ → ℂ}
    (hG : ∀ g, ‖G g‖ ≤ ‖φ g‖ * √g * ‖F (g * y)‖) :
    ‖∫ g, G g‖ ≤ √(∫ g, ‖φ g‖ ^ 2 * g) * √(|y|⁻¹ * ∫ t, ‖F t‖ ^ 2) := by
  have h2m : AEStronglyMeasurable fun g ↦ F (g * y) :=
    (hFc.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
  have h2i : Integrable fun g ↦ ‖F (g * y)‖ ^ 2 := hF.comp_mul_right' hy
  have h2 : MemLp (fun g ↦ F (g * y)) 2 := (memLp_two_iff_integrable_sq_norm h2m).2 h2i
  have hval : ∫ g, ‖F (g * y)‖ ^ 2 = |y|⁻¹ * ∫ t, ‖F t‖ ^ 2 := by
    rw [Measure.integral_comp_mul_right (fun t ↦ ‖F t‖ ^ 2) y, abs_inv, smul_eq_mul]
  rw [← hval]
  exact norm_integral_le_of_norm_le_test_mul ha0 hφc hφ0 h2 hG

end CauchySchwarz

section Blocks

variable (Y : ℝ) (hs : (0 : ℝ) ≤ 0)

local notation "μ₀" => realPWIntervalMeasure 0 0
local notation "hμ₀" => volume_le_realPWIntervalMeasure 0 0 hs
local notation "V₀" => RealPWBand.space Y hμ₀
local notation "ev" => RealPWBand.evaluation Y hμ₀
local notation "evv" => RealPWBand.evaluationVector Y hμ₀

/-- The pointwise values of a band vector are continuous in the point. -/
theorem continuous_evaluation_apply (f : V₀) : Continuous fun y ↦ ev y f :=
  (RealPWBand.continuous_evaluation Y hμ₀).clm_apply continuous_const

/-- The squared modulus of the pointwise values of a band vector is integrable, with integral
the square of the norm. -/
theorem integral_sq_norm_evaluation (f : V₀) :
    Integrable (fun y ↦ ‖ev y f‖ ^ 2) ∧ ∫ y, ‖ev y f‖ ^ 2 = ‖f‖ ^ 2 := by
  have hae := RealPWBand.evaluation_ae Y hμ₀ (realPWIntervalMeasure_absolutelyContinuous 0 0) f
  have hI : Integrable (fun y ↦ ‖(f.val : ℝ → ℂ) y‖ ^ 2) μ₀ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp f.val)
  have hcongr : (fun y ↦ ‖ev y f‖ ^ 2) =ᵐ[μ₀] fun y ↦ ‖(f.val : ℝ → ℂ) y‖ ^ 2 := by
    filter_upwards [hae] with y hy
    rw [hy]
  have hI' : Integrable (fun y ↦ ‖ev y f‖ ^ 2) μ₀ := hI.congr hcongr.symm
  have hint : ∫ y, ‖ev y f‖ ^ 2 ∂μ₀ = ‖f‖ ^ 2 := by
    rw [integral_congr_ae hcongr]
    exact L2.integral_sq_norm (𝕜 := ℂ) f.val
  have key : ∀ G : ℝ → ℝ, Integrable G μ₀ → Integrable G ∧ ∫ y, G y = ∫ y, G y ∂μ₀ := by
    intro G hG
    rw [realPWIntervalMeasure_zero_zero] at hG ⊢
    exact ⟨hG, rfl⟩
  obtain ⟨h1, h2⟩ := key _ hI'
  exact ⟨h1, h2.trans hint⟩

/-- The weighted `L²` mass of a test function of the dilation: the integral of `|φ g|² g`. -/
def testHalfMass (φ : ℝ → ℂ) : ℝ := ∫ g, ‖φ g‖ ^ 2 * g

/-- The weighted mass of a test function supported on the positive half-line is nonnegative. -/
theorem testHalfMass_nonneg {a b : ℝ} (ha0 : 0 < a) {φ : ℝ → ℂ}
    (hφ0 : ∀ g ∉ Icc a b, φ g = 0) : 0 ≤ testHalfMass φ :=
  integral_nonneg fun g ↦ by
    by_cases hg : g ∈ Icc a b
    · exact mul_nonneg (sq_nonneg _) (ha0.le.trans hg.1)
    · simp [hφ0 g hg]

/-- The weighted mass does not change under the rescaling `scaleTest`. -/
theorem testHalfMass_scaleTest (ψ : ℝ → ℂ) {c : ℝ} (hc : 0 < c) :
    testHalfMass (scaleTest ψ c) = testHalfMass ψ := by
  have h := Measure.integral_comp_mul_left (fun w ↦ ‖ψ w‖ ^ 2 * w) c
  have hint : (fun g ↦ ‖scaleTest ψ c g‖ ^ 2 * g) =
      fun g ↦ c * (‖ψ (c * g)‖ ^ 2 * (c * g)) := by
    funext g
    rw [scaleTest, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
    ring
  rw [testHalfMass, hint, integral_const_mul, h, abs_of_pos (inv_pos.mpr hc), smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul, testHalfMass]

/-- The left family of a block is bounded by `√(2Y)` under the mask. -/
theorem norm_realPWTestLeftFamily_le (hY : 0 ≤ Y) (X x : ℝ) :
    ‖realPWTestLeftFamily Y 0 0 hs X x‖ ≤ √(2 * Y) * ‖sharpIntervalMask X x‖ := by
  change ‖sharpIntervalMask X x • evv x‖ ≤ _
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (RealPWBand.norm_evaluationVector_le Y hY hμ₀ x)
    (norm_nonneg _)

/-- Reconstruction: the right family of a block at a point `x ≠ 0` is bounded by the weighted
`L²` norm of the test function times `|x| ^ (-1/2)` under the mask. This is Cauchy–Schwarz in
the dilation variable, and it needs no regularity of the test function. -/
theorem norm_realPWTestRightFamily_le_halfProfile (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a)
    {φ : ℝ → ℂ} (hφc : Continuous φ) (hφ0 : ∀ g ∉ Icc a b, φ g = 0) (X : ℝ) {x : ℝ}
    (hx : x ≠ 0) :
    ‖realPWTestRightFamily Y 0 0 hs φ X x‖ ≤ √(testHalfMass φ) * halfProfile X x := by
  refine norm_le_of_forall_norm_inner_le (mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (abs_nonneg x) _))) fun f ↦ ?_
  obtain ⟨hI, hint⟩ := integral_sq_norm_evaluation Y hs f
  have h := norm_integral_test_dilate_le ha0 hφc hφ0 (continuous_evaluation_apply Y hs f) hI hx
  have hsq : √(|x|⁻¹ * ‖f‖ ^ 2) = |x| ^ (-(1 / 2 : ℝ)) * ‖f‖ := by
    rw [Real.sqrt_mul (inv_nonneg.mpr (abs_nonneg x)), Real.sqrt_sq (norm_nonneg f),
      Real.sqrt_inv, Real.rpow_neg (abs_nonneg x), ← Real.sqrt_eq_rpow]
  rw [hint, hsq] at h
  rw [inner_realPWTestRightFamily_eq Y 0 0 hs hY.le le_rfl ha0 hφc hφ0 X x f, norm_mul]
  calc ‖sharpIntervalMask X x‖ *
        ‖∫ g, φ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) f)‖
      ≤ ‖sharpIntervalMask X x‖ *
          (√(∫ g, ‖φ g‖ ^ 2 * g) * (|x| ^ (-(1 / 2 : ℝ)) * ‖f‖)) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = √(testHalfMass φ) * halfProfile X x * ‖f‖ := by
        rw [halfProfile, testHalfMass]
        ring

section Transpose

/-- An evaluation vector with a scalar coefficient, both depending on a pair of real
parameters. -/
def bandIntegrand (coef : ℝ × ℝ → ℂ) (pt : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : V₀ :=
  star (coef p) • evv (pt p)

/-- A family of band vectors given by integrals of evaluation vectors. -/
def bandFamily (coef : ℝ × ℝ → ℂ) (pt : ℝ × ℝ → ℝ) (y : ℝ) : V₀ :=
  ∫ g, bandIntegrand Y hs coef pt (y, g)

variable {coef : ℝ × ℝ → ℂ} {pt : ℝ × ℝ → ℝ} {κ : ℝ → ℝ}

theorem stronglyMeasurable_bandIntegrand (hc : Measurable coef) (hp : Measurable pt) :
    StronglyMeasurable (bandIntegrand Y hs coef pt) :=
  (continuous_star.measurable.comp hc).stronglyMeasurable.smul
    ((RealPWBand.continuous_evaluationVector Y hμ₀).comp_stronglyMeasurable
      hp.stronglyMeasurable)

theorem norm_bandIntegrand_le (hY : 0 ≤ Y) (hb : ∀ y g, ‖coef (y, g)‖ ≤ κ g) (y g : ℝ) :
    ‖bandIntegrand Y hs coef pt (y, g)‖ ≤ κ g * √(2 * Y) := by
  change ‖star (coef (y, g)) • evv (pt (y, g))‖ ≤ _
  rw [norm_smul, norm_star]
  exact mul_le_mul (hb y g) (RealPWBand.norm_evaluationVector_le Y hY hμ₀ _) (norm_nonneg _)
    ((norm_nonneg _).trans (hb y g))

theorem integrable_bandIntegrand (hY : 0 ≤ Y) (hc : Measurable coef) (hp : Measurable pt)
    (hκ : Integrable κ) (hb : ∀ y g, ‖coef (y, g)‖ ≤ κ g) (y : ℝ) :
    Integrable fun g ↦ bandIntegrand Y hs coef pt (y, g) :=
  (hκ.mul_const _).mono'
    ((stronglyMeasurable_bandIntegrand Y hs hc hp).comp_measurable
      measurable_prodMk_left).aestronglyMeasurable
    (ae_of_all _ fun g ↦ norm_bandIntegrand_le Y hs hY hb y g)

/-- The pairing of a member of the family with a band vector is the integral of the
coefficient against the values of the vector. -/
theorem inner_bandFamily (hI : ∀ y, Integrable fun g ↦ bandIntegrand Y hs coef pt (y, g))
    (y : ℝ) (f : V₀) :
    ⟪bandFamily Y hs coef pt y, f⟫_ℂ = ∫ g, coef (y, g) * ev (pt (y, g)) f := by
  have h1 : ⟪f, bandFamily Y hs coef pt y⟫_ℂ =
      ∫ g, ⟪f, bandIntegrand Y hs coef pt (y, g)⟫_ℂ := (integral_inner (hI y) f).symm
  rw [← inner_conj_symm, h1, ← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
  change (starRingEnd ℂ) ⟪f, star (coef (y, g)) • evv (pt (y, g))⟫_ℂ = _
  rw [inner_conj_symm, inner_smul_left, starRingEnd_apply, star_star,
    ← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]

theorem norm_bandFamily_le (hY : 0 ≤ Y) (hκ : Integrable κ)
    (hb : ∀ y g, ‖coef (y, g)‖ ≤ κ g) (y : ℝ) :
    ‖bandFamily Y hs coef pt y‖ ≤ (∫ g, κ g) * √(2 * Y) := by
  have h := norm_integral_le_of_norm_le (f := fun g ↦ bandIntegrand Y hs coef pt (y, g))
    (hκ.mul_const (√(2 * Y))) (ae_of_all _ fun g ↦ norm_bandIntegrand_le Y hs hY hb y g)
  rwa [integral_mul_const] at h

/-- The coefficient of the transposed family of a block: the conjugate of the test function
with the half-density factor, under the mask at the dilated point. -/
def transposeCoef (φ : ℝ → ℂ) (X : ℝ) (p : ℝ × ℝ) : ℂ :=
  star (φ p.2) * ((√p.2 : ℝ) : ℂ) * sharpIntervalMask X (p.2 * p.1)

/-- The transposed family of a block. Its pairing with a band vector `f` is the integral of
`conj (φ g) √g f (g y)` over the dilations with `|g y| ≤ X`: the adjoint of the action of `φ`
applied to the cutoff of `f`, evaluated at `y`. -/
def realPWTransposeFamily (φ : ℝ → ℂ) (X : ℝ) : ℝ → V₀ :=
  bandFamily Y hs (transposeCoef φ X) fun p ↦ p.2 * p.1

theorem measurable_transposeCoef {φ : ℝ → ℂ} (hφ : Measurable φ) (X : ℝ) :
    Measurable (transposeCoef φ X) :=
  ((continuous_star.measurable.comp (hφ.comp measurable_snd)).mul
    (Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp measurable_snd))).mul
    ((sharpIntervalMask_measurable X).comp (measurable_snd.mul measurable_fst))

theorem norm_transposeCoef_le (φ : ℝ → ℂ) (X y g : ℝ) :
    ‖transposeCoef φ X (y, g)‖ ≤ ‖φ g‖ * √g := by
  change ‖star (φ g) * ((√g : ℝ) : ℂ) * sharpIntervalMask X (g * y)‖ ≤ _
  rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg g)]
  exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg g))
    (sharpIntervalMask_norm_le_one X _)

/-- A point `y` with `|y| > X / a` is carried outside `[-X, X]` by every dilation of
`[a, b]`. -/
theorem lt_abs_mul_of_div_lt {a b : ℝ} (ha0 : 0 < a) {g : ℝ} (hg : g ∈ Icc a b) {X y : ℝ}
    (hy : X / a < |y|) : X < |g * y| := by
  rw [abs_mul, abs_of_pos (ha0.trans_le hg.1)]
  calc X = a * (X / a) := by field_simp
    _ < a * |y| := mul_lt_mul_of_pos_left hy ha0
    _ ≤ g * |y| := mul_le_mul_of_nonneg_right hg.1 (abs_nonneg y)

/-- For a test function supported in `[a, b]`, `0 < a`, the coefficient vanishes at the points
`y` with `|y| > X / a`. -/
theorem transposeCoef_eq_zero {a b : ℝ} (ha0 : 0 < a) {φ : ℝ → ℂ}
    (hφ0 : ∀ g ∉ Icc a b, φ g = 0) {X y : ℝ} (hy : X / a < |y|) (g : ℝ) :
    transposeCoef φ X (y, g) = 0 := by
  change star (φ g) * ((√g : ℝ) : ℂ) * sharpIntervalMask X (g * y) = 0
  by_cases hg : g ∈ Icc a b
  · rw [sharpIntervalMask_of_lt_abs (lt_abs_mul_of_div_lt ha0 hg hy), mul_zero]
  · rw [hφ0 g hg, star_zero, zero_mul, zero_mul]

/-- The weight `‖φ g‖ √g` of a continuous test function supported in `[a, b]` is
integrable. -/
theorem integrable_norm_mul_sqrt {a b : ℝ} {φ : ℝ → ℂ} (hφc : Continuous φ)
    (hφ0 : ∀ g ∉ Icc a b, φ g = 0) : Integrable fun g ↦ ‖φ g‖ * √g :=
  (hφc.norm.mul Real.continuous_sqrt).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (K := Icc a b) isCompact_Icc fun g hg ↦ by simp [hφ0 g hg])

/-- The integrand of the transposed family is integrable in the dilation. -/
theorem integrable_transposeIntegrand (hY : 0 ≤ Y) {a b : ℝ} {φ : ℝ → ℂ}
    (hφc : Continuous φ) (hφ0 : ∀ g ∉ Icc a b, φ g = 0) (X y : ℝ) :
    Integrable fun g ↦ bandIntegrand Y hs (transposeCoef φ X) (fun p ↦ p.2 * p.1) (y, g) :=
  integrable_bandIntegrand Y hs hY (measurable_transposeCoef hφc.measurable X)
    (measurable_snd.mul measurable_fst) (integrable_norm_mul_sqrt hφc hφ0)
    (norm_transposeCoef_le φ X) y

/-- The pairing of the transposed family with a band vector. -/
theorem inner_realPWTransposeFamily (hY : 0 ≤ Y) {a b : ℝ} {φ : ℝ → ℂ}
    (hφc : Continuous φ) (hφ0 : ∀ g ∉ Icc a b, φ g = 0) (X y : ℝ) (f : V₀) :
    ⟪realPWTransposeFamily Y hs φ X y, f⟫_ℂ =
      ∫ g, transposeCoef φ X (y, g) * ev (g * y) f :=
  inner_bandFamily Y hs (integrable_transposeIntegrand Y hs hY hφc hφ0 X) y f

/-- The transposed family vanishes at the points `y` with `|y| > X / a`. -/
theorem realPWTransposeFamily_eq_zero {a b : ℝ} (ha0 : 0 < a) {φ : ℝ → ℂ}
    (hφ0 : ∀ g ∉ Icc a b, φ g = 0) {X y : ℝ} (hy : X / a < |y|) :
    realPWTransposeFamily Y hs φ X y = 0 := by
  change ∫ g, star (transposeCoef φ X (y, g)) • evv (g * y) = 0
  simp [transposeCoef_eq_zero ha0 hφ0 hy]

/-- A family bounded under a sharp mask is square integrable. -/
theorem memLp_two_of_norm_le_mask {E : Type*} [NormedAddCommGroup E] {W : ℝ → E}
    (hW : AEStronglyMeasurable W (realPWIntervalMeasure 0 0)) {K X : ℝ}
    (hb : ∀ y, ‖W y‖ ≤ K * ‖sharpIntervalMask X y‖) :
    MemLp W 2 (realPWIntervalMeasure 0 0) := by
  rw [realPWIntervalMeasure_zero_zero] at hW ⊢
  refine (memLp_two_iff_integrable_sq_norm hW).2
    (((integrable_norm_sharpIntervalMask X).const_mul (K ^ 2)).mono' (hW.norm.pow 2)
      (ae_of_all _ fun y ↦ ?_))
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hm : ‖sharpIntervalMask X y‖ * ‖sharpIntervalMask X y‖ = ‖sharpIntervalMask X y‖ := by
    rw [← norm_mul, sharpIntervalMask_mul_self]
  calc ‖W y‖ ^ 2 ≤ (K * ‖sharpIntervalMask X y‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hb y) 2
    _ = K ^ 2 * (‖sharpIntervalMask X y‖ * ‖sharpIntervalMask X y‖) := by ring
    _ = K ^ 2 * ‖sharpIntervalMask X y‖ := by rw [hm]

/-- The transposed family is square integrable. -/
theorem memLp_realPWTransposeFamily (hY : 0 ≤ Y) {a b : ℝ} (ha0 : 0 < a) {φ : ℝ → ℂ}
    (hφc : Continuous φ) (hφ0 : ∀ g ∉ Icc a b, φ g = 0) (X : ℝ) :
    MemLp (realPWTransposeFamily Y hs φ X) 2 μ₀ := by
  refine memLp_two_of_norm_le_mask (K := (∫ g, ‖φ g‖ * √g) * √(2 * Y)) (X := X / a)
    ((stronglyMeasurable_bandIntegrand Y hs (measurable_transposeCoef hφc.measurable X)
      (measurable_snd.mul measurable_fst)).integral_prod_right'
        (ν := volume)).aestronglyMeasurable fun y ↦ ?_
  by_cases hy : |y| ≤ X / a
  · rw [norm_sharpIntervalMask_of_abs_le hy, mul_one]
    exact norm_bandFamily_le Y hs hY (integrable_norm_mul_sqrt hφc hφ0)
      (norm_transposeCoef_le φ X) y
  · rw [realPWTransposeFamily_eq_zero Y hs ha0 hφ0 (not_le.mp hy), norm_zero]
    exact mul_nonneg (mul_nonneg (integral_nonneg fun g ↦
      mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg g)) (Real.sqrt_nonneg _)) (norm_nonneg _)

/-- Reconstruction: the transposed family at a point `y ≠ 0` is bounded by the weighted `L²`
norm of the test function times `|y| ^ (-1/2)`, under the mask of `[-X / a, X / a]`. -/
theorem norm_realPWTransposeFamily_le_halfProfile (hY : 0 ≤ Y) {a b : ℝ} (ha0 : 0 < a)
    {φ : ℝ → ℂ} (hφc : Continuous φ) (hφ0 : ∀ g ∉ Icc a b, φ g = 0) (X : ℝ) {y : ℝ}
    (hy : y ≠ 0) :
    ‖realPWTransposeFamily Y hs φ X y‖ ≤ √(testHalfMass φ) * halfProfile (X / a) y := by
  have h0 : 0 ≤ √(testHalfMass φ) * halfProfile (X / a) y :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (abs_nonneg y) _))
  by_cases hya : |y| ≤ X / a
  · refine norm_le_of_forall_norm_inner_le h0 fun f ↦ ?_
    obtain ⟨hI, hint⟩ := integral_sq_norm_evaluation Y hs f
    have h := norm_integral_test_scale_le ha0 hφc hφ0 (continuous_evaluation_apply Y hs f) hI
      hy (G := fun g ↦ transposeCoef φ X (y, g) * ev (g * y) f) fun g ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_transposeCoef_le φ X y g) (norm_nonneg _)
    have hsq : √(|y|⁻¹ * ‖f‖ ^ 2) = |y| ^ (-(1 / 2 : ℝ)) * ‖f‖ := by
      rw [Real.sqrt_mul (inv_nonneg.mpr (abs_nonneg y)), Real.sqrt_sq (norm_nonneg f),
        Real.sqrt_inv, Real.rpow_neg (abs_nonneg y), ← Real.sqrt_eq_rpow]
    rw [hint, hsq] at h
    rw [inner_realPWTransposeFamily Y hs hY hφc hφ0 X y f, halfProfile,
      norm_sharpIntervalMask_of_abs_le hya, one_mul, testHalfMass]
    exact h.trans (le_of_eq (by ring))
  · rw [realPWTransposeFamily_eq_zero Y hs ha0 hφ0 (not_le.mp hya), norm_zero]
    exact h0

/-- Reconstruction: a block written through its transposed family. The product of the adjoint
of the analysis map of the masked evaluation vectors with the analysis map of the right family
is also the product of the adjoint of the analysis map of the transposed family with the
analysis map of the evaluation vectors on `[-X / a, X / a]`. The two expressions are the two
orders of integration of one double integral, after the substitution `x = g y`. -/
theorem realPWTest_adjoint_comp_eq_transpose (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a) {φ : ℝ → ℂ}
    (hφc : Continuous φ) (hφ0 : ∀ g ∉ Icc a b, φ g = 0) (X : ℝ)
    (hU : MemLp (realPWTestLeftFamily Y 0 0 hs X) 2 μ₀)
    (hR : MemLp (realPWTestRightFamily Y 0 0 hs φ X) 2 μ₀)
    (hΦ : MemLp (realPWTransposeFamily Y hs φ X) 2 μ₀)
    (hU' : MemLp (realPWTestLeftFamily Y 0 0 hs (X / a)) 2 μ₀) :
    (hilbertFamilyAnalysisCLM hU).adjoint.comp (hilbertFamilyAnalysisCLM hR) =
      (hilbertFamilyAnalysisCLM hΦ).adjoint.comp (hilbertFamilyAnalysisCLM hU') := by
  refine ContinuousLinearMap.ext fun f ↦ ext_inner_left ℂ fun z ↦ ?_
  change ⟪z, (hilbertFamilyAnalysisCLM hU).adjoint (hilbertFamilyAnalysisCLM hR f)⟫_ℂ =
    ⟪z, (hilbertFamilyAnalysisCLM hΦ).adjoint (hilbertFamilyAnalysisCLM hU' f)⟫_ℂ
  rw [inner_adjoint_familyAnalysis_comp, inner_adjoint_familyAnalysis_comp,
    integral_realPWIntervalMeasure_zero_zero, integral_realPWIntervalMeasure_zero_zero]
  have hφm : Measurable φ := hφc.measurable
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (K := Icc a b) isCompact_Icc hφ0)
  obtain ⟨cz, hcz0, hevz⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ x, ‖ev x z‖ ≤ c :=
    ⟨√(2 * Y) * ‖z‖, by positivity, fun x ↦ ((ev x).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (RealPWBand.norm_evaluation_le Y hY.le hμ₀ x) (norm_nonneg _))⟩
  obtain ⟨cf, hcf0, hevf⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ x, ‖ev x f‖ ≤ c :=
    ⟨√(2 * Y) * ‖f‖, by positivity, fun x ↦ ((ev x).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (RealPWBand.norm_evaluation_le Y hY.le hμ₀ x) (norm_nonneg _))⟩
  let Kz : ℝ → ℂ := fun x ↦ sharpIntervalMask X x * star (ev x z)
  have hKzm : Measurable Kz := (sharpIntervalMask_measurable X).mul
    (continuous_star.measurable.comp (continuous_evaluation_apply Y hs z).measurable)
  have hKzb : ∀ x, ‖Kz x‖ ≤ ‖sharpIntervalMask X x‖ * cz := fun x ↦ by
    change ‖sharpIntervalMask X x * star (ev x z)‖ ≤ _
    rw [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_left (hevz x) (norm_nonneg _)
  have hKz1 : ∀ x, ‖Kz x‖ ≤ cz := fun x ↦
    (hKzb x).trans (mul_le_of_le_one_left hcz0 (sharpIntervalMask_norm_le_one X x))
  have hzev : ∀ x, ⟪z, evv x⟫_ℂ = star (ev x z) := fun x ↦ by
    rw [← inner_conj_symm, ← InnerProductSpace.toDual_apply_apply,
      RealPWBand.toDual_evaluationVector]
    rfl
  let P : ℝ → ℝ → ℂ := fun x g ↦
    φ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Kz x * ev (g⁻¹ * x) f)
  let Q : ℝ → ℝ → ℂ := fun y g ↦ φ g * ((√g : ℝ) : ℂ) * (Kz (g * y) * ev y f)
  have hsupp : ∀ y g, φ g * Kz (g * y) * sharpIntervalMask (X / a) y = φ g * Kz (g * y) := by
    intro y g
    by_cases hya : |y| ≤ X / a
    · rw [sharpIntervalMask_of_abs_le hya, mul_one]
    · by_cases hg : g ∈ Icc a b
      · change φ g * (sharpIntervalMask X (g * y) * star (ev (g * y) z)) *
          sharpIntervalMask (X / a) y = φ g * (sharpIntervalMask X (g * y) * star (ev (g * y) z))
        rw [sharpIntervalMask_of_lt_abs (lt_abs_mul_of_div_lt ha0 hg (not_le.mp hya))]
        simp
      · rw [hφ0 g hg]
        simp
  have hL : ∀ x, ⟪z, realPWTestLeftFamily Y 0 0 hs X x⟫_ℂ *
      ⟪realPWTestRightFamily Y 0 0 hs φ X x, f⟫_ℂ = ∫ g, P x g := by
    intro x
    have h1 : ⟪z, realPWTestLeftFamily Y 0 0 hs X x⟫_ℂ = Kz x := by
      change ⟪z, sharpIntervalMask X x • evv x⟫_ℂ = _
      rw [inner_smul_right, hzev]
    have hk : Kz x * sharpIntervalMask X x = Kz x := by
      change sharpIntervalMask X x * star (ev x z) * sharpIntervalMask X x =
        sharpIntervalMask X x * star (ev x z)
      rw [mul_right_comm, sharpIntervalMask_mul_self]
    rw [h1, inner_realPWTestRightFamily_eq Y 0 0 hs hY.le le_rfl ha0 hφc hφ0 X x f,
      ← mul_assoc, hk, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    change Kz x * (φ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) f)) =
      φ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Kz x * ev (g⁻¹ * x) f)
    ring
  have hRr : ∀ y, ⟪z, realPWTransposeFamily Y hs φ X y⟫_ℂ *
      ⟪realPWTestLeftFamily Y 0 0 hs (X / a) y, f⟫_ℂ = ∫ g, Q y g := by
    intro y
    have h1 : ⟪z, realPWTransposeFamily Y hs φ X y⟫_ℂ =
        ∫ g, φ g * ((√g : ℝ) : ℂ) * Kz (g * y) := by
      rw [← inner_conj_symm, inner_realPWTransposeFamily Y hs hY.le hφc hφ0 X y z,
        ← integral_conj]
      refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
      change (starRingEnd ℂ) (star (φ g) * ((√g : ℝ) : ℂ) * sharpIntervalMask X (g * y) *
        ev (g * y) z) =
        φ g * ((√g : ℝ) : ℂ) * (sharpIntervalMask X (g * y) * star (ev (g * y) z))
      rw [map_mul, map_mul, map_mul, Complex.conj_ofReal, starRingEnd_apply, star_star,
        starRingEnd_apply, star_sharpIntervalMask, starRingEnd_apply]
      ring
    have h2 : ⟪realPWTestLeftFamily Y 0 0 hs (X / a) y, f⟫_ℂ =
        sharpIntervalMask (X / a) y * ev y f := by
      change ⟪sharpIntervalMask (X / a) y • evv y, f⟫_ℂ = _
      rw [inner_smul_left, starRingEnd_apply, star_sharpIntervalMask,
        ← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]
    rw [h1, h2, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    change φ g * ((√g : ℝ) : ℂ) * Kz (g * y) * (sharpIntervalMask (X / a) y * ev y f) =
      φ g * ((√g : ℝ) : ℂ) * (Kz (g * y) * ev y f)
    linear_combination ((√g : ℝ) : ℂ) * ev y f * hsupp y g
  have hPm : Measurable (Function.uncurry P) := by
    have h1 : Measurable fun p : ℝ × ℝ ↦ φ p.2 := hφm.comp measurable_snd
    have h2 : Measurable fun p : ℝ × ℝ ↦ ((p.2 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (measurable_snd.pow_const _)
    have h3 : Measurable fun p : ℝ × ℝ ↦ Kz p.1 := hKzm.comp measurable_fst
    have h4 : Measurable fun p : ℝ × ℝ ↦ ev (p.2⁻¹ * p.1) f :=
      (continuous_evaluation_apply Y hs f).measurable.comp
        (measurable_snd.inv.mul measurable_fst)
    exact (h1.mul h2).mul (h3.mul h4)
  have hPb : ∀ x g, ‖P x g‖ ≤
      (‖sharpIntervalMask X x‖ * (cz * cf)) * (‖φ g‖ * a ^ (-(1 / 2 : ℝ))) := by
    intro x g
    change ‖φ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Kz x * ev (g⁻¹ * x) f)‖ ≤ _
    by_cases hg : g ∈ Icc a b
    · have hg0 : 0 < g := ha0.trans_le hg.1
      have hρ : ‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ ≤ a ^ (-(1 / 2 : ℝ)) := by
        rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hg0.le _)]
        exact Real.rpow_le_rpow_of_nonpos ha0 hg.1 (by norm_num)
      rw [norm_mul, norm_mul, norm_mul]
      calc ‖φ g‖ * ‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * (‖Kz x‖ * ‖ev (g⁻¹ * x) f‖)
          ≤ ‖φ g‖ * a ^ (-(1 / 2 : ℝ)) * ((‖sharpIntervalMask X x‖ * cz) * cf) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hρ (norm_nonneg _))
              (mul_le_mul (hKzb x) (hevf _) (norm_nonneg _)
                (mul_nonneg (norm_nonneg _) hcz0))
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
              (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg ha0.le _))
        _ = _ := by ring
    · rw [hφ0 g hg]
      simp
  have hPint : Integrable (Function.uncurry P) ((volume : Measure ℝ).prod volume) :=
    (((integrable_norm_sharpIntervalMask X).mul_const (cz * cf)).mul_prod
      (hφi.norm.mul_const _)).mono' hPm.aestronglyMeasurable
      (ae_of_all _ fun p ↦ hPb p.1 p.2)
  have hQm : Measurable (Function.uncurry Q) := by
    have h1 : Measurable fun p : ℝ × ℝ ↦ φ p.2 := hφm.comp measurable_snd
    have h2 : Measurable fun p : ℝ × ℝ ↦ ((√p.2 : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp measurable_snd)
    have h3 : Measurable fun p : ℝ × ℝ ↦ Kz (p.2 * p.1) :=
      hKzm.comp (measurable_snd.mul measurable_fst)
    have h4 : Measurable fun p : ℝ × ℝ ↦ ev p.1 f :=
      (continuous_evaluation_apply Y hs f).measurable.comp measurable_fst
    exact (h1.mul h2).mul (h3.mul h4)
  have hQb : ∀ y g, ‖Q y g‖ ≤
      (‖sharpIntervalMask (X / a) y‖ * (cz * cf)) * (‖φ g‖ * √g) := by
    intro y g
    have e : ‖φ g‖ * ‖Kz (g * y)‖ =
        ‖φ g‖ * ‖Kz (g * y)‖ * ‖sharpIntervalMask (X / a) y‖ := by
      rw [← norm_mul, ← norm_mul, hsupp y g]
    have hA : ‖φ g‖ * ‖Kz (g * y)‖ ≤ ‖φ g‖ * cz * ‖sharpIntervalMask (X / a) y‖ := by
      rw [e]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hKz1 _) (norm_nonneg _)) (norm_nonneg _)
    calc ‖Q y g‖ = (‖φ g‖ * ‖Kz (g * y)‖) * (√g * ‖ev y f‖) := by
          change ‖φ g * ((√g : ℝ) : ℂ) * (Kz (g * y) * ev y f)‖ = _
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (Real.sqrt_nonneg g)]
          ring
      _ ≤ (‖φ g‖ * cz * ‖sharpIntervalMask (X / a) y‖) * (√g * cf) :=
          mul_le_mul hA (mul_le_mul_of_nonneg_left (hevf y) (Real.sqrt_nonneg g))
            (mul_nonneg (Real.sqrt_nonneg g) (norm_nonneg _))
            (mul_nonneg (mul_nonneg (norm_nonneg _) hcz0) (norm_nonneg _))
      _ = _ := by ring
  have hQint : Integrable (Function.uncurry Q) ((volume : Measure ℝ).prod volume) :=
    (((integrable_norm_sharpIntervalMask (X / a)).mul_const (cz * cf)).mul_prod
      (integrable_norm_mul_sqrt hφc hφ0)).mono' hQm.aestronglyMeasurable
      (ae_of_all _ fun p ↦ hQb p.1 p.2)
  have hmid : ∀ g, ∫ x, P x g = ∫ y, Q y g := by
    intro g
    by_cases hg : g ∈ Icc a b
    · have hg0 : 0 < g := ha0.trans_le hg.1
      have hsub := Measure.integral_comp_mul_left (fun x ↦ Kz x * ev (g⁻¹ * x) f) g
      simp only [inv_mul_cancel_left₀ hg0.ne'] at hsub
      change ∫ x, φ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Kz x * ev (g⁻¹ * x) f) =
        ∫ y, φ g * ((√g : ℝ) : ℂ) * (Kz (g * y) * ev y f)
      rw [integral_const_mul, integral_const_mul, hsub, abs_of_pos (inv_pos.mpr hg0),
        rpow_neg_half_eq_sqrt_mul_inv hg0, Complex.real_smul]
      push_cast
      ring
    · change ∫ x, φ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Kz x * ev (g⁻¹ * x) f) =
        ∫ y, φ g * ((√g : ℝ) : ℂ) * (Kz (g * y) * ev y f)
      simp [hφ0 g hg]
  calc ∫ x, ⟪z, realPWTestLeftFamily Y 0 0 hs X x⟫_ℂ *
        ⟪realPWTestRightFamily Y 0 0 hs φ X x, f⟫_ℂ
      = ∫ x, ∫ g, P x g := integral_congr_ae (ae_of_all _ hL)
    _ = ∫ g, ∫ x, P x g := integral_integral_swap hPint
    _ = ∫ g, ∫ y, Q y g := integral_congr_ae (ae_of_all _ hmid)
    _ = ∫ y, ∫ g, Q y g := (integral_integral_swap hQint).symm
    _ = ∫ y, ⟪z, realPWTransposeFamily Y hs φ X y⟫_ℂ *
          ⟪realPWTestLeftFamily Y 0 0 hs (X / a) y, f⟫_ℂ :=
        (integral_congr_ae (ae_of_all _ hRr)).symm

end Transpose

section Block

/-- `IsBandBlock T φ X`: the operator `T` on the band is the compression of the cutoff to
`[-X, X]` of the action of the test function `φ` of the dilation. It sends `f` to the
orthogonal projection onto the band of `x ↦ 1_[-X, X] (x) ∫ φ g g ^ (-1/2) f (x / g) dg`. -/
def IsBandBlock (T : V₀ →L[ℂ] V₀) (φ : ℝ → ℂ) (X : ℝ) : Prop :=
  ∀ f : V₀, ∃ ρ : Lp ℂ 2 μ₀,
    (∀ᵐ t ∂μ₀, ρ t = sharpIntervalMask X t *
      ∫ g, φ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * t) f)) ∧
    T f = (V₀).orthogonalProjectionOnto ρ

/-- The description `IsBandBlock` determines the operator. -/
theorem IsBandBlock.unique {T T' : V₀ →L[ℂ] V₀} {φ : ℝ → ℂ} {X : ℝ}
    (h : IsBandBlock Y hs T φ X) (h' : IsBandBlock Y hs T' φ X) : T = T' := by
  refine ContinuousLinearMap.ext fun f ↦ ?_
  obtain ⟨ρ, hρ, hT⟩ := h f
  obtain ⟨ρ', hρ', hT'⟩ := h' f
  have hρρ : ρ = ρ' := Lp.ext (by
    filter_upwards [hρ, hρ'] with t h1 h2
    rw [h1, h2])
  rw [hT, hT', hρρ]

/-- The product of the two analysis maps of a block satisfies `IsBandBlock`. -/
theorem isBandBlock_adjoint_comp (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a) {φ : ℝ → ℂ}
    (hφc : Continuous φ) (hφ0 : ∀ g ∉ Icc a b, φ g = 0) (X : ℝ)
    (hU : MemLp (realPWTestLeftFamily Y 0 0 hs X) 2 μ₀)
    (hR : MemLp (realPWTestRightFamily Y 0 0 hs φ X) 2 μ₀) :
    IsBandBlock Y hs
      ((hilbertFamilyAnalysisCLM hU).adjoint.comp (hilbertFamilyAnalysisCLM hR)) φ X := by
  intro f
  refine ⟨hilbertFamilyAnalysisCLM hR f, ?_, ?_⟩
  · filter_upwards [hilbertFamilyAnalysisCLM_apply_ae hR f] with x hx
    rw [hx]
    exact inner_realPWTestRightFamily_eq Y 0 0 hs hY.le le_rfl ha0 hφc hφ0 X x f
  · exact realPWTest_adjoint_analysis_apply Y 0 0 hs hY.le le_rfl ha0 hφc hφ0 X hU hR f

/-- The trace of the product of the two analysis maps of a block. -/
theorem hilbertTrace_adjoint_comp_block (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a) {φ : ℝ → ℂ}
    (hφc : Continuous φ) (hφ0 : ∀ g ∉ Icc a b, φ g = 0) (X : ℝ)
    (hU : MemLp (realPWTestLeftFamily Y 0 0 hs X) 2 μ₀)
    (hR : MemLp (realPWTestRightFamily Y 0 0 hs φ X) 2 μ₀)
    (hn : IsNuclearOperator
      ((hilbertFamilyAnalysisCLM hU).adjoint.comp (hilbertFamilyAnalysisCLM hR))) :
    hilbertTrace ⟨(hilbertFamilyAnalysisCLM hU).adjoint.comp (hilbertFamilyAnalysisCLM hR),
      hn⟩ = ∫ g, φ g * realPWSharpTrace Y 0 0 hs g X := by
  have hμac := realPWIntervalMeasure_absolutelyContinuous 0 0
  obtain ⟨ι, bs, _⟩ := exists_hilbertBasis ℂ V₀
  have := RealPWBand.countable_hilbertBasis Y hμ₀ hμac bs
  let A := hilbertFamilyAnalysisCLM hU
  let B := hilbertFamilyAnalysisCLM hR
  have hA (f : V₀) : A f =ᵐ[μ₀] fun x ↦ ⟪realPWTestLeftFamily Y 0 0 hs X x, f⟫_ℂ :=
    hilbertFamilyAnalysisCLM_apply_ae hU f
  have hB (f : V₀) : B f =ᵐ[μ₀] fun x ↦ ⟪realPWTestRightFamily Y 0 0 hs φ X x, f⟫_ℂ :=
    hilbertFamilyAnalysisCLM_apply_ae hR f
  let Ah : hilbertSchmidtOperators V₀ (Lp ℂ 2 μ₀) :=
    ⟨A, familyAnalysis_mem_hilbertSchmidtOperators bs hU A hA⟩
  let Bh : hilbertSchmidtOperators V₀ (Lp ℂ 2 μ₀) :=
    ⟨B, familyAnalysis_mem_hilbertSchmidtOperators bs hR B hB⟩
  have htrace := hilbertTrace_familyAnalysisProduct bs (realPWTestLeftFamily Y 0 0 hs X)
    (realPWTestRightFamily Y 0 0 hs φ X) Ah Bh (fun i ↦ hA (bs i)) (fun i ↦ hB (bs i))
  exact htrace.trans (integral_inner_realPWTestFamilies Y 0 0 hs hY.le le_rfl ha0 hφc hφ0 X)

/-- The first bound for the trace norm of a block, through the families of
`exists_realPWTestCutoff_nuclear`. -/
theorem traceNorm_adjoint_comp_block_le_sqrt (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a)
    {φ : ℝ → ℂ} (hφc : Continuous φ) (hφ0 : ∀ g ∉ Icc a b, φ g = 0) {X : ℝ} (hX : 0 < X)
    (hU : MemLp (realPWTestLeftFamily Y 0 0 hs X) 2 μ₀)
    (hR : MemLp (realPWTestRightFamily Y 0 0 hs φ X) 2 μ₀)
    (hn : IsNuclearOperator
      ((hilbertFamilyAnalysisCLM hU).adjoint.comp (hilbertFamilyAnalysisCLM hR))) :
    traceNorm ⟨(hilbertFamilyAnalysisCLM hU).adjoint.comp (hilbertFamilyAnalysisCLM hR),
      hn⟩ ≤ 2 * (2 * Y + testHalfMass φ) * √X := by
  have hμac := realPWIntervalMeasure_absolutelyContinuous 0 0
  obtain ⟨ι, bs, _⟩ := exists_hilbertBasis ℂ V₀
  have := RealPWBand.countable_hilbertBasis Y hμ₀ hμac bs
  have hsq1 : √(2 * Y) ^ 2 = 2 * Y := Real.sq_sqrt (by positivity)
  have hsq2 : √(testHalfMass φ) ^ 2 = testHalfMass φ :=
    Real.sq_sqrt (testHalfMass_nonneg ha0 hφ0)
  obtain ⟨_, hup⟩ := exists_traceNorm_le_of_halfProfile bs realPWIntervalMeasure_zero_zero
    hU hR hX (norm_realPWTestLeftFamily_le Y hs hY.le X)
    (fun x hx ↦ norm_realPWTestRightFamily_le_halfProfile Y hs hY ha0 hφc hφ0 X hx)
  exact hup.trans (le_of_eq (by rw [hsq1, hsq2]))

/-- The trace norm of the product, in the other order, of the analysis maps of the masked
evaluation vectors on `[-X / a, X / a]` and of the transposed family. -/
theorem exists_traceNorm_transpose_comp_le (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a)
    {φ : ℝ → ℂ} (hφc : Continuous φ) (hφ0 : ∀ g ∉ Icc a b, φ g = 0) {X : ℝ} (hX : 0 < X)
    (hΦ : MemLp (realPWTransposeFamily Y hs φ X) 2 μ₀)
    (hU' : MemLp (realPWTestLeftFamily Y 0 0 hs (X / a)) 2 μ₀) :
    ∃ hS : IsNuclearOperator
        ((hilbertFamilyAnalysisCLM hU').adjoint.comp (hilbertFamilyAnalysisCLM hΦ)),
      traceNorm ⟨(hilbertFamilyAnalysisCLM hU').adjoint.comp (hilbertFamilyAnalysisCLM hΦ),
        hS⟩ ≤ 2 * (2 * Y + testHalfMass φ) * √(X / a) := by
  have hμac := realPWIntervalMeasure_absolutelyContinuous 0 0
  obtain ⟨ι, bs, _⟩ := exists_hilbertBasis ℂ V₀
  have := RealPWBand.countable_hilbertBasis Y hμ₀ hμac bs
  have hsq1 : √(2 * Y) ^ 2 = 2 * Y := Real.sq_sqrt (by positivity)
  have hsq2 : √(testHalfMass φ) ^ 2 = testHalfMass φ :=
    Real.sq_sqrt (testHalfMass_nonneg ha0 hφ0)
  obtain ⟨hS, hlow⟩ := exists_traceNorm_le_of_halfProfile bs realPWIntervalMeasure_zero_zero
    hU' hΦ (div_pos hX ha0) (norm_realPWTestLeftFamily_le Y hs hY.le (X / a))
    (fun y hy ↦ norm_realPWTransposeFamily_le_halfProfile Y hs hY.le ha0 hφc hφ0 X hy)
  exact ⟨hS, hlow.trans (le_of_eq (by rw [hsq1, hsq2]))⟩

/-- The second bound for the trace norm of a block, through the transposed family. -/
theorem traceNorm_adjoint_comp_block_le_sqrt_div (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a)
    {φ : ℝ → ℂ} (hφc : Continuous φ) (hφ0 : ∀ g ∉ Icc a b, φ g = 0) {X : ℝ} (hX : 0 < X)
    (hU : MemLp (realPWTestLeftFamily Y 0 0 hs X) 2 μ₀)
    (hR : MemLp (realPWTestRightFamily Y 0 0 hs φ X) 2 μ₀)
    (hn : IsNuclearOperator
      ((hilbertFamilyAnalysisCLM hU).adjoint.comp (hilbertFamilyAnalysisCLM hR))) :
    traceNorm ⟨(hilbertFamilyAnalysisCLM hU).adjoint.comp (hilbertFamilyAnalysisCLM hR),
      hn⟩ ≤ 2 * (2 * Y + testHalfMass φ) * √(X / a) := by
  have hΦ := memLp_realPWTransposeFamily Y hs hY.le ha0 hφc hφ0 X
  have hU' := memLp_realPWTestLeftFamily Y 0 0 hs hY.le le_rfl (X / a)
  obtain ⟨hS, hlow⟩ := exists_traceNorm_transpose_comp_le Y hs hY ha0 hφc hφ0 hX hΦ hU'
  obtain ⟨hS', hSeq⟩ := traceNorm_adjoint_eq _ hS
  have hEq : (hilbertFamilyAnalysisCLM hU).adjoint.comp (hilbertFamilyAnalysisCLM hR) =
      ((hilbertFamilyAnalysisCLM hU').adjoint.comp (hilbertFamilyAnalysisCLM hΦ)).adjoint := by
    rw [realPWTest_adjoint_comp_eq_transpose Y hs hY ha0 hφc hφ0 X hU hR hΦ hU',
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  have hsub : (⟨(hilbertFamilyAnalysisCLM hU).adjoint.comp (hilbertFamilyAnalysisCLM hR),
      hn⟩ : nuclearEndomorphisms V₀) =
      ⟨((hilbertFamilyAnalysisCLM hU').adjoint.comp (hilbertFamilyAnalysisCLM hΦ)).adjoint,
        hS'⟩ := Subtype.ext hEq
  rw [hsub, hSeq]
  exact hlow

/-- Reconstruction: a block is nuclear, with two bounds for its trace norm. For a continuous
test function `φ` supported in `[a, b]`, `0 < a`, and a cutoff `X > 0`, the compression to the
band of the cutoff to `[-X, X]` of the action of `φ` has trace the integral of `φ` against the
sharp traces, and trace norm at most `2 (2Y + m) √X` and at most `2 (2Y + m) √(X / a)`, where
`m` is the integral of `|φ g|² g`. The first bound comes from the vector families of
`exists_realPWTestCutoff_nuclear`, the second from the transposed family. The second is the
smaller one when `a > 1`, where the action of `φ` only sees the values of `f` on
`[-X / a, X / a]`. -/
theorem exists_bandBlock_nuclear (hY : 0 < Y) {a b : ℝ} (ha0 : 0 < a) {φ : ℝ → ℂ}
    (hφc : Continuous φ) (hφ0 : ∀ g ∉ Icc a b, φ g = 0) {X : ℝ} (hX : 0 < X) :
    ∃ T : nuclearEndomorphisms V₀, IsBandBlock Y hs T.val φ X ∧
      hilbertTrace T = ∫ g, φ g * realPWSharpTrace Y 0 0 hs g X ∧
      traceNorm T ≤ 2 * (2 * Y + testHalfMass φ) * √X ∧
      traceNorm T ≤ 2 * (2 * Y + testHalfMass φ) * √(X / a) := by
  have hU := memLp_realPWTestLeftFamily Y 0 0 hs hY.le le_rfl X
  have hR := memLp_realPWTestRightFamily Y 0 0 hs hY.le le_rfl ha0 hφc hφ0 X
  have hμac := realPWIntervalMeasure_absolutelyContinuous 0 0
  obtain ⟨ι, bs, _⟩ := exists_hilbertBasis ℂ V₀
  have := RealPWBand.countable_hilbertBasis Y hμ₀ hμac bs
  obtain ⟨hn, -⟩ := exists_traceNorm_familyAnalysis_comp_le bs hU hR
  exact ⟨⟨_, hn⟩, isBandBlock_adjoint_comp Y hs hY ha0 hφc hφ0 X hU hR,
    hilbertTrace_adjoint_comp_block Y hs hY ha0 hφc hφ0 X hU hR hn,
    traceNorm_adjoint_comp_block_le_sqrt Y hs hY ha0 hφc hφ0 hX hU hR hn,
    traceNorm_adjoint_comp_block_le_sqrt_div Y hs hY ha0 hφc hφ0 hX hU hR hn⟩

end Block

section Sum

/-- `√(L p ^ m / D) = √(L / D) (√p) ^ m`. -/
theorem sqrt_mul_pow_div {L p D : ℝ} (hL : 0 ≤ L) (hp : 0 ≤ p) (hD : 0 < D) (m : ℕ) :
    √(L * p ^ m / D) = √(L / D) * √p ^ m := by
  have hqm : (√p ^ m) ^ 2 = p ^ m := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hp]
  rw [show L * p ^ m / D = L / D * (√p ^ m) ^ 2 by rw [hqm]; ring,
    Real.sqrt_mul (div_nonneg hL hD.le), Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg p) m)]

/-- The condition `r² p ≤ 1` with `p > 1` forces `r < 1`. -/
theorem lt_one_of_sq_mul_le {p r : ℝ} (hp : 1 < p) (hrp : r ^ 2 * p ≤ 1) : r < 1 := by
  by_contra h
  rw [not_lt] at h
  have h2 : 1 ≤ r ^ 2 := one_le_pow₀ h
  linarith [mul_le_mul_of_nonneg_right h2 (zero_le_one.trans hp.le)]

/-- The majorant of the trace norms of the blocks is summable when `r² p ≤ 1`: it is the
product of the geometric series of ratios `r` and `r² √p`. -/
theorem summable_primeTwistBound_mul_sqrt_pow {p r : ℝ} (hp : 1 < p) (hr0 : 0 < r)
    (hrp : r ^ 2 * p ≤ 1) (D : ℝ) :
    Summable fun x : ℕ × ℕ ↦ primeTwistBound r x * (D * √p ^ x.2) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hr1 := lt_one_of_sq_mul_le hp hrp
  have hq1 : 1 < √p := by
    rw [Real.lt_sqrt zero_le_one]
    simpa using hp
  have hqq : r ^ 2 * √p * √p ≤ 1 := by
    rw [mul_assoc, Real.mul_self_sqrt hp0.le]
    exact hrp
  have hq : r ^ 2 * √p < 1 := by
    by_contra h
    rw [not_lt] at h
    linarith [mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg p)]
  have h := ((summable_geometric_of_lt_one hr0.le hr1).mul_of_nonneg
    (summable_geometric_of_lt_one (by positivity) hq) (fun n ↦ pow_nonneg hr0.le n)
    (fun i ↦ pow_nonneg (by positivity) i)).mul_left (r⁻¹ ^ 2 * D)
  refine h.congr fun x ↦ ?_
  rw [primeTwistBound, mul_pow]
  ring

/-- A block of the pairs `(i, i + n)`, with the bound for its trace norm through the families
of `exists_realPWTestCutoff_nuclear`. The index is `(n, i)`. -/
theorem exists_primeUpperBlock (hY : 0 < Y) {p : ℝ} (hp : 0 < p) {a b : ℝ} (ha0 : 0 < a)
    {ψ : ℝ → ℂ} (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {L : ℝ} (hL : 0 < L)
    (x : ℕ × ℕ) :
    ∃ T : nuclearEndomorphisms V₀,
      IsBandBlock Y hs T.val (scaleTest ψ (p ^ x.1)) (L * p ^ x.2 / p) ∧
      hilbertTrace T = primeBlock Y hs ψ (p ^ x.1) (L * p ^ x.2 / p) ∧
      traceNorm T ≤ 2 * (2 * Y + testHalfMass ψ) * (√(L / p) * √p ^ x.2) := by
  have hc : 0 < p ^ x.1 := pow_pos hp _
  obtain ⟨T, h1, h2, h3, -⟩ := exists_bandBlock_nuclear Y hs hY (div_pos ha0 hc)
    (continuous_scaleTest hψc _) (fun _ hg ↦ scaleTest_eq_zero hψ0 hc hg)
    (X := L * p ^ x.2 / p) (by positivity)
  refine ⟨T, h1, h2, ?_⟩
  rwa [testHalfMass_scaleTest ψ hc, sqrt_mul_pow_div hL.le hp.le hp] at h3

/-- A block of the pairs `(j + n + 1, j)`, with the bound for its trace norm through the
transposed family. The index is `(n, j)`. The scale `p ^ (-(n + 1))` of the test function
cancels the factor `p ^ (n + 1)` of the cutoff. -/
theorem exists_primeLowerBlock (hY : 0 < Y) {p : ℝ} (hp : 0 < p) {a b : ℝ} (ha0 : 0 < a)
    {ψ : ℝ → ℂ} (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {L : ℝ} (hL : 0 < L)
    (x : ℕ × ℕ) :
    ∃ T : nuclearEndomorphisms V₀,
      IsBandBlock Y hs T.val (scaleTest ψ ((p ^ (x.1 + 1))⁻¹))
        (L * p ^ (x.2 + x.1 + 1) / p) ∧
      hilbertTrace T = primeBlock Y hs ψ ((p ^ (x.1 + 1))⁻¹) (L * p ^ (x.2 + x.1 + 1) / p) ∧
      traceNorm T ≤ 2 * (2 * Y + testHalfMass ψ) * (√(L / (p * a)) * √p ^ x.2) := by
  have hc : 0 < (p ^ (x.1 + 1))⁻¹ := inv_pos.mpr (pow_pos hp _)
  obtain ⟨T, h1, h2, -, h4⟩ := exists_bandBlock_nuclear Y hs hY (div_pos ha0 hc)
    (continuous_scaleTest hψc _) (fun _ hg ↦ scaleTest_eq_zero hψ0 hc hg)
    (X := L * p ^ (x.2 + x.1 + 1) / p) (by positivity)
  refine ⟨T, h1, h2, ?_⟩
  have e : L * p ^ (x.2 + x.1 + 1) / p / (a / (p ^ (x.1 + 1))⁻¹) = L * p ^ x.2 / (p * a) := by
    rw [add_assoc, pow_add]
    field_simp
  rwa [testHalfMass_scaleTest ψ hc, e, sqrt_mul_pow_div hL.le hp.le (mul_pos hp ha0)] at h4

/-- `IsPrimeTwistedCutoff T r p ψ L`: the operator `T` on the band is the sum, convergent in
trace norm, of the blocks of the cutoff twisted at a prime. The blocks are the compressions
`Q M_{L p ^ (i - 1)} A_{ψ_{j - i}} Q`, described by `IsBandBlock`, and the block of the pair
`(i, j)` enters with the coefficient `d i d j`, `d = primeTwistCoeff r`. The pairs with
`i ≤ j` are indexed by `(j - i, i)` and those with `i > j` by `(i - j - 1, j)`. -/
def IsPrimeTwistedCutoff (T : V₀ →L[ℂ] V₀) (r p : ℝ) (ψ : ℝ → ℂ) (L : ℝ) : Prop :=
  ∃ Tu Tl : ℕ × ℕ → nuclearEndomorphisms V₀,
    (∀ x, IsBandBlock Y hs (Tu x).val (scaleTest ψ (p ^ x.1)) (L * p ^ x.2 / p)) ∧
    (∀ x, IsBandBlock Y hs (Tl x).val (scaleTest ψ ((p ^ (x.1 + 1))⁻¹))
      (L * p ^ (x.2 + x.1 + 1) / p)) ∧
    Summable (fun x ↦ |primeUpperCoeff r x| * traceNorm (Tu x)) ∧
    Summable (fun x ↦ |primeLowerCoeff r x| * traceNorm (Tl x)) ∧
    T = (∑' x, ((primeUpperCoeff r x : ℝ) : ℂ) • (Tu x).val) +
      ∑' x, ((primeLowerCoeff r x : ℝ) : ℂ) • (Tl x).val

/-- Reconstruction: the blocks of the cutoff twisted at a prime add up to one nuclear operator
on the band, and its trace is `primeTraceSeries`. For `r² p ≤ 1` the series of the blocks with
their coefficients converges in trace norm. The blocks with `i ≤ j` are bounded through the
families of `exists_realPWTestCutoff_nuclear` and those with `i > j` through the transposed
family, and both bounds are a constant times `(√p) ^ i`, against coefficients of size
`r ^ (i + j)`. The case of the prime `p` is `r = p ^ (-1/2)`, where `r² p = 1`. -/
theorem exists_primeTwistedCutoff_nuclear (hY : 0 < Y) {p r : ℝ} (hp : 1 < p) (hr0 : 0 < r)
    (hrp : r ^ 2 * p ≤ 1) {a b : ℝ} (ha0 : 0 < a) {ψ : ℝ → ℂ} (hψc : Continuous ψ)
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {L : ℝ} (hL : 0 < L) :
    ∃ T : nuclearEndomorphisms V₀, IsPrimeTwistedCutoff Y hs T.val r p ψ L ∧
      hilbertTrace T = primeTraceSeries Y hs r p ψ L := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hr1 := lt_one_of_sq_mul_le hp hrp
  choose Tu hTu1 hTu2 hTu3 using exists_primeUpperBlock Y hs hY hp0 ha0 hψc hψ0 hL
  choose Tl hTl1 hTl2 hTl3 using exists_primeLowerBlock Y hs hY hp0 ha0 hψc hψ0 hL
  have hmu := summable_primeTwistBound_mul_sqrt_pow hp hr0 hrp
    (2 * (2 * Y + testHalfMass ψ) * √(L / p))
  have hml := summable_primeTwistBound_mul_sqrt_pow hp hr0 hrp
    (2 * (2 * Y + testHalfMass ψ) * √(L / (p * a)))
  have htn : ∀ T : nuclearEndomorphisms V₀, 0 ≤ traceNorm T := fun T ↦
    (norm_nonneg _).trans (norm_val_le_traceNorm T)
  have hbu : ∀ x, |primeUpperCoeff r x| * traceNorm (Tu x) ≤
      primeTwistBound r x * (2 * (2 * Y + testHalfMass ψ) * √(L / p) * √p ^ x.2) := fun x ↦
    mul_le_mul (abs_primeUpperCoeff_le hr0 hr1 x) ((hTu3 x).trans (le_of_eq (by ring)))
      (htn _) (primeTwistBound_nonneg hr0 x)
  have hbl : ∀ x, |primeLowerCoeff r x| * traceNorm (Tl x) ≤
      primeTwistBound r x * (2 * (2 * Y + testHalfMass ψ) * √(L / (p * a)) * √p ^ x.2) :=
    fun x ↦ mul_le_mul (abs_primeLowerCoeff_le hr0 hr1 x)
      ((hTl3 x).trans (le_of_eq (by ring))) (htn _) (primeTwistBound_nonneg hr0 x)
  obtain ⟨hnu, htru⟩ := exists_nuclear_tsum_smul
    (fun x ↦ ((primeUpperCoeff r x : ℝ) : ℂ)) Tu _ hmu (fun x ↦ by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hbu x)
  obtain ⟨hnl, htrl⟩ := exists_nuclear_tsum_smul
    (fun x ↦ ((primeLowerCoeff r x : ℝ) : ℂ)) Tl _ hml (fun x ↦ by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hbl x)
  refine ⟨⟨_, hnu⟩ + ⟨_, hnl⟩, ⟨Tu, Tl, hTu1, hTl1,
    Summable.of_nonneg_of_le (fun x ↦ mul_nonneg (abs_nonneg _) (htn _)) hbu hmu,
    Summable.of_nonneg_of_le (fun x ↦ mul_nonneg (abs_nonneg _) (htn _)) hbl hml, rfl⟩, ?_⟩
  rw [hilbertTrace_add_eq, htru, htrl, primeTraceSeries]
  congr 1
  · exact tsum_congr fun x ↦ by
      rw [hTu2 x]
      rfl
  · exact tsum_congr fun x ↦ by
      rw [hTl2 x]
      rfl

/-- Reconstruction: the trace of the cutoff twisted at a prime, in the fixed-bandwidth model.
For each cutoff `L > 0` the blocks add up, in trace norm, to a nuclear operator `T L` on the
band, and as the cutoff is removed the trace of `T L` less `ψ 1 log (2πY L)` converges to the
real-place limit plus `log p` times the sum over `n ≥ 1` of `r ^ n (φ (p ^ n) + φ (p ^ (-n)))`,
`φ g = g ψ g`. This joins `exists_primeTwistedCutoff_nuclear` and
`tendsto_primeTraceSeries_sub_log`.
Paper: for `r = p ^ (-1/2)` this is the term of the place `p` in Theorem 12.4.1.1,
(12.4.1.1), p. 514, for `F = ℚ`, and the statement is the case `k = ℚ`, `S = {∞, p}` of
A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
function*, §VII, Theorem 4, p. 31, on the functions invariant under the units of `ℚ_p`.
Deviation: the operator is given as the sum of its blocks. That this sum is
`Q U⁻¹ M_L U A_ψ Q` for the unitary `U = (1 - r T⁻¹) (1 - r T)⁻¹`, `T f (x) = √p f (p x)`,
and that this is the cutoff operator on the sector of `L²(X_S)`, is not formalized. The band
has a fixed width `Y`, where Connes cuts both variables at the same `Λ`. The test function is
assumed Lipschitz. -/
theorem exists_primeTwistedCutoff_trace_limit (hY : 0 < Y) {p r : ℝ} (hp : 1 < p)
    (hr0 : 0 < r) (hrp : r ^ 2 * p ≤ 1) {a b : ℝ} (ha0 : 0 < a) {ψ : ℝ → ℂ}
    (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {K : ℝ}
    (hK : ∀ g g', ‖ψ g - ψ g'‖ ≤ K * |g - g'|) :
    ∃ T : ℝ → nuclearEndomorphisms V₀,
      (∀ L, 0 < L → IsPrimeTwistedCutoff Y hs (T L).val r p ψ L) ∧
      Tendsto (fun L ↦ hilbertTrace (T L) -
          ψ 1 * ((Real.log (2 * π * Y * L) : ℝ) : ℂ)) atTop
        (𝓝 (ψ 1 * ((sincLogConstant / π : ℝ) : ℂ) +
          (∫ g, (ψ g - ψ 1 * ((logTermProfile g : ℝ) : ℂ)) * ((realTermDensity g : ℝ) : ℂ)) +
          ((Real.log p : ℝ) : ℂ) * ∑' n : ℕ, ((r ^ (n + 1) : ℝ) : ℂ) *
            (((p ^ (n + 1) : ℝ) : ℂ) * ψ (p ^ (n + 1)) +
              (((p ^ (n + 1))⁻¹ : ℝ) : ℂ) * ψ ((p ^ (n + 1))⁻¹)))) := by
  classical
  have hr1 := lt_one_of_sq_mul_le hp hrp
  have hex : ∀ L : ℝ, ∃ T : nuclearEndomorphisms V₀, 0 < L →
      IsPrimeTwistedCutoff Y hs T.val r p ψ L ∧
        hilbertTrace T = primeTraceSeries Y hs r p ψ L := by
    intro L
    by_cases hL : 0 < L
    · obtain ⟨T, h1, h2⟩ := exists_primeTwistedCutoff_nuclear Y hs hY hp hr0 hrp ha0 hψc hψ0 hL
      exact ⟨T, fun _ ↦ ⟨h1, h2⟩⟩
    · exact ⟨0, fun h ↦ absurd h hL⟩
  choose T hT using hex
  refine ⟨T, fun L hL ↦ (hT L hL).1, ?_⟩
  refine (tendsto_primeTraceSeries_sub_log Y hs hY hp hr0 hr1 ha0 hψc hψ0 hK).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with L hL
  rw [(hT L hL).2]

end Sum

end Blocks

end RiemannMasullo.Isolated
