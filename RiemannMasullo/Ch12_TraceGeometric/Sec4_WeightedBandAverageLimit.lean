module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedBandAverage

/-! # The level of the weighted model against a test function

Paper: Theorem 12.4.1.1, pp. 514–519, and the value used on p. 520.

`Sec4_WeightedBandLevel` proves, for one dilation `g > 1`, that the traces on the level of the
weighted model tend to `V_∞ (g) - L₋ (g) - L₊ (g)`. This file proves the same for the average of
the dilations against a test function, which is the form in which p. 520 uses the theorem.

* `norm_integral_weightedDilationMultiplier_mul_realOddBandKernel_le`: the diagonal integral
  over the odd band is bounded uniformly in the cutoff, by a continuous function of the
  dilation.
* `tendsto_integral_mul_weightedOddDiagonal`, `tendsto_integral_inner_realCutoff`: hence the
  limit in the cutoff passes under the average, for the diagonal integral and for the rank-one
  terms, by dominated convergence.
* `hilbertTrace_weightedPWLevel_average_compression`: the averaged compression to the level is
  nuclear and its trace is `weightedPWLevelAverageTrace`, the averaged diagonal integral minus
  the two rank-one terms.
* `weightedBandDilationAverage`, `weightedBandDilationAverage_apply`: the average of the
  dilations on the weighted space.
* `tendsto_hilbertTrace_weightedLevel_average_compression`: **on the weighted space, for a
  continuous `φ` on an interval `[a, b]` of `(1, ∞)`, the Hilbert traces of `P ∘ M_L ∘ A ∘ P`
  tend to `∫ φ (g) (g ^ (3/2) / (g ^ 2 - 1) - g ^ (-1/2) - g ^ (1/2)) dg / g` as `L → ∞`, at
  every fixed `Y > 0`.**

**Not formalized.** The test is supported in dilations larger than one: for `g < 1` the
dilation does not preserve the band and the proof of the rank-one terms does not apply. One
weight, `x ^ 2 + x ^ (-2)`. The sharp cutoff. The rational field with no finite place.
-/

open MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate InnerProductSpace ENNReal NNReal Interval

@[expose] public noncomputable section

namespace RiemannMasullo

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

/-! ### A bound for the diagonal integral, uniform in the cutoff and in the dilation -/

/-- The kernel of the odd band on the diagonal `(z / g, z)` is bounded by `2 |Y|`. -/
theorem abs_realOddBandKernel_le (Y u y : ℝ) : |realOddBandKernel Y u y| ≤ 2 * |Y| := by
  unfold realOddBandKernel
  have h1 := abs_realBandKernel_le Y (u - y)
  have h2 := abs_realBandKernel_le Y (u + y)
  rw [abs_div, abs_two, div_le_iff₀ two_pos]
  exact (abs_sub _ _).trans (by linarith)

/-- The symmetric integral of the band kernel along a ray is bounded uniformly in the cutoff. -/
theorem abs_integral_realBandKernel_mul_symm_le {c : ℝ} (hc : 0 < c) (Y L : ℝ) :
    |∫ z in (-L)..L, realBandKernel Y (c * z)| ≤ 2 * ((π * c)⁻¹ * (π / 2 + 2)) := by
  have hcont : Continuous fun z : ℝ ↦ realBandKernel Y (c * z) :=
    (continuous_realBandKernel Y).comp (by fun_prop)
  have h0 : ∫ z in (-L)..0, realBandKernel Y (c * z) =
      ∫ z in (0 : ℝ)..L, realBandKernel Y (c * z) := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := L)
      (fun z : ℝ ↦ realBandKernel Y (c * z))
    simp only [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun z _ ↦ ?_
    rw [mul_neg, realBandKernel_neg]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable (-L) 0)
    (hcont.intervalIntegrable 0 L), h0, integral_realBandKernel_mul hc.ne', ← two_mul, abs_mul,
    abs_two, abs_mul, abs_inv, abs_of_pos (by positivity : 0 < π * c)]
  gcongr
  exact abs_integral_sinc_le _

/-- The rational part of the multiplier is dominated by a multiple of `1 / (1 + z ^ 2)`,
uniformly for `g ≥ 1`. -/
theorem norm_weightedDilationMultiplier_sub_le {g : ℝ} (hg : 1 ≤ g) (z : ℝ) :
    ‖weightedDilationMultiplier g z - (g : ℂ)‖ ≤ g * (g ^ 2 - 1) * (√2 * (1 + z ^ 2)⁻¹) := by
  have hg0 : 0 < g := by linarith
  rw [weightedDilationMultiplier_eq hg0.ne', add_sub_cancel_left, norm_div, norm_mul, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hg0.le]
  have h1 : ‖(g : ℂ) ^ 2 - 1‖ = g ^ 2 - 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by nlinarith)]
  have h2 := norm_sq_sub_I_mul z (g ^ 2)
  rw [Complex.ofReal_pow] at h2
  have hden : (1 + z ^ 2) / √2 ≤ ‖(z : ℂ) ^ 2 - Complex.I * (g : ℂ) ^ 2‖ := by
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [h2, div_pow, Real.sq_sqrt (by norm_num)]
    have : (1 : ℝ) ≤ (g ^ 2) ^ 2 := by
      have : (1 : ℝ) ≤ g ^ 2 := by nlinarith
      nlinarith
    nlinarith [sq_nonneg (z ^ 2 - 1)]
  have hpos : 0 < (1 + z ^ 2) / √2 := by positivity
  rw [h1, div_le_iff₀ (hpos.trans_le hden)]
  calc g * (g ^ 2 - 1) = g * (g ^ 2 - 1) * (√2 * (1 + z ^ 2)⁻¹) * ((1 + z ^ 2) / √2) := by
        field_simp
    _ ≤ g * (g ^ 2 - 1) * (√2 * (1 + z ^ 2)⁻¹) * ‖(z : ℂ) ^ 2 - Complex.I * (g : ℂ) ^ 2‖ := by
        gcongr
        have : (0 : ℝ) ≤ g ^ 2 - 1 := by nlinarith
        positivity

/-- The kernel of the odd band on the diagonal `(z / g, z)`, in terms of the band kernel. -/
theorem realOddBandKernel_div_self (Y g z : ℝ) :
    realOddBandKernel Y (z / g) z =
      (realBandKernel Y ((1 - 1 / g) * z) - realBandKernel Y ((1 + 1 / g) * z)) / 2 := by
  rw [realOddBandKernel, show z / g - z = -((1 - 1 / g) * z) by ring, realBandKernel_neg,
    show z / g + z = (1 + 1 / g) * z by ring]

/-- The bound for the diagonal integral: it depends on `g` and `Y` and not on the cutoff. -/
def weightedOddDiagonalBound (Y g : ℝ) : ℝ :=
  g * (((π * (1 - 1 / g))⁻¹ + (π * (1 + 1 / g))⁻¹) * (π / 2 + 2)) +
    g * (g ^ 2 - 1) * (√2 * (2 * |Y|)) * π

/-- **The diagonal integral is bounded uniformly in the cutoff.** -/
theorem norm_integral_weightedDilationMultiplier_mul_realOddBandKernel_le {Y g L : ℝ}
    (hg : 1 < g) (hL : 0 ≤ L) :
    ‖∫ z in (-L)..L, weightedDilationMultiplier g z * (realOddBandKernel Y (z / g) z : ℂ)‖ ≤
      weightedOddDiagonalBound Y g := by
  have hg0 : 0 < g := by linarith
  have hcm : 0 < 1 - 1 / g := by
    rw [sub_pos, div_lt_one hg0]
    exact hg
  have hcp : 0 < 1 + 1 / g := by positivity
  have hLL : -L ≤ L := by linarith
  have hKc : Continuous fun z : ℝ ↦ (realOddBandKernel Y (z / g) z : ℂ) := by
    unfold realOddBandKernel
    exact Complex.continuous_ofReal.comp ((((continuous_realBandKernel Y).comp (by fun_prop)).sub
      ((continuous_realBandKernel Y).comp (by fun_prop))).div_const 2)
  have hrc := continuous_weightedDilationMultiplier hg0.ne'
  have hcont (c : ℝ) : Continuous fun z : ℝ ↦ realBandKernel Y (c * z) :=
    (continuous_realBandKernel Y).comp (by fun_prop)
  have hsplit : ∀ z : ℝ, weightedDilationMultiplier g z * (realOddBandKernel Y (z / g) z : ℂ) =
      (g : ℂ) * (realOddBandKernel Y (z / g) z : ℂ) +
        (weightedDilationMultiplier g z - (g : ℂ)) * (realOddBandKernel Y (z / g) z : ℂ) :=
    fun z ↦ by ring
  simp_rw [hsplit]
  have hi1 : IntervalIntegrable (fun z : ℝ ↦ (g : ℂ) * (realOddBandKernel Y (z / g) z : ℂ))
      volume (-L) L := (continuous_const.mul hKc).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun z : ℝ ↦ (weightedDilationMultiplier g z - (g : ℂ)) *
      (realOddBandKernel Y (z / g) z : ℂ)) volume (-L) L :=
    ((hrc.sub continuous_const).mul hKc).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hg0.le, intervalIntegral.integral_ofReal,
      Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ hg0.le
    simp_rw [realOddBandKernel_div_self]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      ((hcont _).intervalIntegrable _ _) ((hcont _).intervalIntegrable _ _), abs_div, abs_two,
      div_le_iff₀ two_pos]
    have h1 := abs_integral_realBandKernel_mul_symm_le hcm Y L
    have h2 := abs_integral_realBandKernel_mul_symm_le hcp Y L
    refine (abs_sub _ _).trans ?_
    linarith
  · refine (intervalIntegral.norm_integral_le_integral_norm hLL).trans ?_
    have hb : ∀ z : ℝ, ‖(weightedDilationMultiplier g z - (g : ℂ)) *
        (realOddBandKernel Y (z / g) z : ℂ)‖ ≤
        g * (g ^ 2 - 1) * (√2 * (2 * |Y|)) * (1 + z ^ 2)⁻¹ := fun z ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := norm_weightedDilationMultiplier_sub_le hg.le z
      have h2 := abs_realOddBandKernel_le Y (z / g) z
      have h3 : (0 : ℝ) ≤ g * (g ^ 2 - 1) * (√2 * (1 + z ^ 2)⁻¹) := by
        have : (0 : ℝ) ≤ g ^ 2 - 1 := by nlinarith
        positivity
      calc _ ≤ g * (g ^ 2 - 1) * (√2 * (1 + z ^ 2)⁻¹) * (2 * |Y|) :=
            mul_le_mul h1 h2 (abs_nonneg _) h3
        _ = _ := by ring
    have hbi : Integrable fun z : ℝ ↦ g * (g ^ 2 - 1) * (√2 * (2 * |Y|)) * (1 + z ^ 2)⁻¹ :=
      integrable_inv_one_add_sq.const_mul _
    have hmono := intervalIntegral.integral_mono_on hLL hi2.norm
      (hbi.intervalIntegrable) fun z _ ↦ hb z
    refine hmono.trans ?_
    rw [intervalIntegral.integral_of_le hLL]
    have hC : (0 : ℝ) ≤ g * (g ^ 2 - 1) * (√2 * (2 * |Y|)) := by
      have : (0 : ℝ) ≤ g ^ 2 - 1 := by nlinarith
      positivity
    refine (setIntegral_le_integral hbi (Eventually.of_forall fun z ↦ ?_)).trans_eq ?_
    · exact mul_nonneg hC (by positivity)
    · rw [integral_const_mul, integral_univ_inv_one_add_sq]

/-- The diagonal integral is a continuous function of the dilation on `g ≥ 1`. -/
theorem continuousOn_integral_weightedDilationMultiplier_mul_realOddBandKernel (Y L : ℝ) :
    ContinuousOn (fun g : ℝ ↦ ∫ z in (-L)..L,
      weightedDilationMultiplier g z * (realOddBandKernel Y (z / g) z : ℂ)) (Ici 1) := by
  have hmax : Continuous fun p : ℝ × ℝ ↦ max p.1 1 := continuous_fst.max continuous_const
  have hne : ∀ p : ℝ × ℝ, max p.1 1 ≠ 0 := fun p ↦ (zero_lt_one.trans_le (le_max_right _ _)).ne'
  have hF : Continuous (Function.uncurry fun (g z : ℝ) ↦
      weightedDilationMultiplier (max g 1) z * (realOddBandKernel Y (z / max g 1) z : ℂ)) := by
    refine Continuous.mul ?_ ?_
    · unfold weightedDilationMultiplier
      refine Continuous.div (by fun_prop) (by fun_prop) fun p ↦ ?_
      exact weightedDilationMultiplier_den_ne_zero (hne p) p.2
    · unfold realOddBandKernel
      have hd : Continuous fun p : ℝ × ℝ ↦ p.2 / max p.1 1 := continuous_snd.div hmax hne
      exact Complex.continuous_ofReal.comp
        ((((continuous_realBandKernel Y).comp (hd.sub continuous_snd)).sub
          ((continuous_realBandKernel Y).comp (hd.add continuous_snd))).div_const 2)
  have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hF (-L) L
  refine hc.continuousOn.congr fun g hg ↦ ?_
  have hmg : max g 1 = g := max_eq_left hg
  simp only [hmg]

/-- The bound for the diagonal integral is continuous in the dilation on `g > 1`. -/
theorem continuousOn_weightedOddDiagonalBound (Y : ℝ) :
    ContinuousOn (weightedOddDiagonalBound Y) (Ioi 1) := by
  unfold weightedOddDiagonalBound
  have h1 : ∀ g ∈ Ioi (1 : ℝ), π * (1 - 1 / g) ≠ 0 := fun g hg ↦ by
    have hg0 : (0 : ℝ) < g := zero_lt_one.trans hg
    have : 0 < 1 - 1 / g := by
      rw [sub_pos, div_lt_one hg0]
      exact hg
    positivity
  have h2 : ∀ g ∈ Ioi (1 : ℝ), π * (1 + 1 / g) ≠ 0 := fun g hg ↦ by
    have hg0 : (0 : ℝ) < g := zero_lt_one.trans hg
    positivity
  have h0 : ∀ g ∈ Ioi (1 : ℝ), g ≠ 0 := fun g hg ↦ (zero_lt_one.trans hg).ne'
  have hd : ContinuousOn (fun g : ℝ ↦ 1 / g) (Ioi 1) :=
    continuousOn_const.div continuousOn_id h0
  refine ContinuousOn.add (ContinuousOn.mul continuousOn_id (ContinuousOn.mul
    (ContinuousOn.add (ContinuousOn.inv₀ (continuousOn_const.mul (continuousOn_const.sub hd)) h1)
      (ContinuousOn.inv₀ (continuousOn_const.mul (continuousOn_const.add hd)) h2))
    continuousOn_const)) ?_
  exact (by fun_prop : Continuous fun g : ℝ ↦ g * (g ^ 2 - 1) * (√2 * (2 * |Y|)) * π).continuousOn

/-- **The limit of the averaged diagonal integrals.** For a continuous `φ` on an interval
`[a, b]` of `(1, ∞)`, the averages against `φ (g) dg / g` of the diagonal integrals over the odd
band tend to the average of their limits, as the cutoff is removed. -/
theorem tendsto_integral_mul_weightedOddDiagonal {Y a b : ℝ} (hY : 0 < Y) (ha : 1 < a)
    (hab : a ≤ b) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc a b)) :
    Tendsto (fun L : ℝ ↦ ∫ g in a..b, (φ g : ℂ) * ((((√g)⁻¹ : ℝ) : ℂ) *
        ∫ z in (-L)..L, weightedDilationMultiplier g z * (realOddBandKernel Y (z / g) z : ℂ)) /
        (g : ℂ)) atTop
      (𝓝 (∫ g in a..b, (φ g : ℂ) * (((g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ : ℝ) : ℂ) +
        weightedBandDefect Y g) / (g : ℂ))) := by
  have hIoc : Ι a b = Ioc a b := uIoc_of_le hab
  have hsub : Icc a b ⊆ Ioi 1 := fun g hg ↦ ha.trans_le hg.1
  have hsub' : Icc a b ⊆ Ici 1 := fun g hg ↦ ha.le.trans hg.1
  have hpos : ∀ g ∈ Icc a b, (0 : ℝ) < g := fun g hg ↦ zero_lt_one.trans (hsub hg)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun g ↦ |φ g| * weightedOddDiagonalBound Y g) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun L ↦ ?_
    rw [hIoc]
    have hc : ContinuousOn (fun g : ℝ ↦ (φ g : ℂ) * ((((√g)⁻¹ : ℝ) : ℂ) *
        ∫ z in (-L)..L, weightedDilationMultiplier g z * (realOddBandKernel Y (z / g) z : ℂ)) /
        (g : ℂ)) (Icc a b) := by
      refine ContinuousOn.div (ContinuousOn.mul (Complex.continuous_ofReal.comp_continuousOn hφ)
        (ContinuousOn.mul ?_
          ((continuousOn_integral_weightedDilationMultiplier_mul_realOddBandKernel Y L).mono
            hsub'))) Complex.continuous_ofReal.continuousOn fun g hg ↦ ?_
      · refine Complex.continuous_ofReal.comp_continuousOn (ContinuousOn.inv₀
          Real.continuous_sqrt.continuousOn fun g hg ↦ (Real.sqrt_pos.mpr (hpos g hg)).ne')
      · exact_mod_cast (hpos g hg).ne'
    exact (hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    refine Eventually.of_forall fun g hg ↦ ?_
    rw [hIoc] at hg
    have hg1 : 1 < g := ha.trans hg.1
    have hg0 : 0 < g := zero_lt_one.trans hg1
    have hb := norm_integral_weightedDilationMultiplier_mul_realOddBandKernel_le (Y := Y) hg1 hL
    have hs1 : (√g)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hg1.le)
    have hs0 : 0 ≤ (√g)⁻¹ := by positivity
    rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_of_nonneg hs0, Real.norm_of_nonneg hg0.le,
      div_le_iff₀ hg0]
    have hB0 : 0 ≤ weightedOddDiagonalBound Y g := (norm_nonneg _).trans hb
    calc |φ g| * ((√g)⁻¹ * ‖∫ z in (-L)..L, weightedDilationMultiplier g z *
          (realOddBandKernel Y (z / g) z : ℂ)‖)
        ≤ |φ g| * (1 * weightedOddDiagonalBound Y g) := by
          gcongr
      _ ≤ |φ g| * weightedOddDiagonalBound Y g * g := by
          rw [one_mul]
          exact le_mul_of_one_le_right (mul_nonneg (abs_nonneg _) hB0) hg1.le
  · refine ContinuousOn.intervalIntegrable_of_Icc hab ?_
    exact (continuous_abs.comp_continuousOn hφ).mul
      ((continuousOn_weightedOddDiagonalBound Y).mono hsub)
  · refine Eventually.of_forall fun g hg ↦ ?_
    rw [hIoc] at hg
    have hg1 : 1 < g := ha.trans hg.1
    exact ((tendsto_integral_weightedDilationMultiplier_mul_realOddBandKernel hY hg1).const_mul
      (φ g : ℂ)).div_const (g : ℂ)

/-- The cutoff does not increase the norm. -/
theorem norm_realCutoff_apply_le (L : ℝ) (f : H) : ‖realCutoff L f‖ ≤ ‖f‖ := by
  have h := (realCutoff L).le_of_opNorm_le
    (LinearMap.mkContinuous_norm_le _ zero_le_one _) f
  rwa [one_mul] at h

/-- **Removing the cutoff under an average.** For a bounded measurable family `Φ g` of vectors,
the averages of the pairings `⟪v, M_L (Φ g)⟫` tend to the average of the pairings `⟪v, Φ g⟫`. -/
theorem tendsto_integral_inner_realCutoff {a b : ℝ} (v : H) {Φ : ℝ → H}
    (hΦ : AEStronglyMeasurable Φ (volume.restrict (Ι a b))) {C : ℝ}
    (hC : ∀ g ∈ Ι a b, ‖Φ g‖ ≤ C) :
    Tendsto (fun L : ℝ ↦ ∫ g in a..b, ⟪v, realCutoff L (Φ g)⟫_ℂ) atTop
      (𝓝 (∫ g in a..b, ⟪v, Φ g⟫_ℂ)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ ↦ ‖v‖ * C) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun L ↦ ?_
    exact ((innerSL ℂ v).comp (realCutoff L)).continuous.comp_aestronglyMeasurable hΦ
  · refine Eventually.of_forall fun L ↦ Eventually.of_forall fun g hg ↦ ?_
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      ((norm_realCutoff_apply_le L _).trans (hC g hg)) (norm_nonneg _))
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun g _ ↦ tendsto_inner_realCutoff v (Φ g)

/-- The term `E (Y)` is a continuous function of the dilation on `g > 1`. -/
theorem continuousOn_weightedBandDefect (Y : ℝ) :
    ContinuousOn (weightedBandDefect Y) (Ioi 1) := by
  unfold weightedBandDefect
  have hm : ∀ g ∈ Ioi (1 : ℝ), (g : ℂ) - 1 ≠ 0 := fun g hg ↦
    sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hg))
  have hp : ∀ g ∈ Ioi (1 : ℝ), (g : ℂ) + 1 ≠ 0 := fun g hg ↦ by
    have : g + 1 ≠ 0 := by linarith [show (1 : ℝ) < g from hg]
    exact_mod_cast this
  have hs : ∀ g ∈ Ioi (1 : ℝ), 2 * √g ≠ 0 := fun g hg ↦
    mul_ne_zero two_ne_zero (Real.sqrt_pos.mpr (zero_lt_one.trans hg)).ne'
  refine ContinuousOn.mul (Complex.continuous_ofReal.comp_continuousOn
    (ContinuousOn.div (by fun_prop) (by fun_prop) hs)) (ContinuousOn.sub ?_ ?_)
  · exact ContinuousOn.div (by fun_prop) (by fun_prop) hm
  · exact ContinuousOn.div (by fun_prop) (by fun_prop) hp

/-! ### The rank-one terms under the average -/

section Average

variable {Y L a b : ℝ} {φ : ℝ → ℝ}

/-- The pairing with the cutoff of an averaged vector is the average of the pairings. -/
theorem inner_realCutoff_weightedPWDilationAverage (ha : 1 ≤ a) (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) (L : ℝ) (v w : H) :
    ⟪v, realCutoff L (weightedPWDilationAverage φ a b w)⟫_ℂ =
      ∫ g in a..b, ⟪v, realCutoff L (((φ g / g : ℝ) : ℂ) • weightedPWDilation g w)⟫_ℂ := by
  rw [weightedPWDilationAverage_apply ha hab hφ]
  exact (ContinuousLinearMap.intervalIntegral_comp_comm ((innerSL ℂ v).comp (realCutoff L))
    (intervalIntegrable_smul_weightedPWDilation ha hab hφ w)).symm

/-- **The rank-one terms under the average, as the cutoff is removed.** -/
theorem tendsto_inner_realCutoff_weightedPWDilationAverage (ha : 1 ≤ a) (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) (v w : H) :
    Tendsto (fun L : ℝ ↦ ⟪v, realCutoff L (weightedPWDilationAverage φ a b w)⟫_ℂ) atTop
      (𝓝 (∫ g in a..b, ((φ g / g : ℝ) : ℂ) * ⟪v, weightedPWDilation g w⟫_ℂ)) := by
  have hint := intervalIntegrable_smul_weightedPWDilation ha hab hφ w
  have hIoc : Ι a b = Ioc a b := uIoc_of_le hab
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  have hmeas : AEStronglyMeasurable (fun g ↦ ((φ g / g : ℝ) : ℂ) • weightedPWDilation g w)
      (volume.restrict (Ι a b)) := by
    rw [hIoc]
    exact hint.1.aestronglyMeasurable
  have hbound : ∀ g ∈ Ι a b, ‖((φ g / g : ℝ) : ℂ) • weightedPWDilation g w‖ ≤ C * ‖w‖ :=
    fun g hg ↦ by
      rw [hIoc] at hg
      have hg1 : 1 ≤ g := ha.trans hg.1.le
      have hg0 : 0 < g := by linarith
      have h1 := norm_weightedPWDilation_le hg1 w
      have h2 : |φ g| ≤ C := hC g ⟨hg.1.le, hg.2⟩
      have hC0 : 0 ≤ C := (abs_nonneg _).trans h2
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hg0]
      calc |φ g| / g * ‖weightedPWDilation g w‖ ≤ |φ g| / g * (g * ‖w‖) := by gcongr
        _ = |φ g| * ‖w‖ := by field_simp
        _ ≤ C * ‖w‖ := by gcongr
  have h := tendsto_integral_inner_realCutoff v hmeas hbound
  have hlim : ∫ g in a..b, ⟪v, ((φ g / g : ℝ) : ℂ) • weightedPWDilation g w⟫_ℂ =
      ∫ g in a..b, ((φ g / g : ℝ) : ℂ) * ⟪v, weightedPWDilation g w⟫_ℂ :=
    intervalIntegral.integral_congr fun g _ ↦ inner_smul_right _ _ _
  rw [← hlim]
  exact h.congr fun L ↦ (inner_realCutoff_weightedPWDilationAverage ha hab hφ L v w).symm

/-! ### The averaged compression in the Paley–Wiener picture -/

/-- The trace of the averaged compression to the level, in the Paley–Wiener picture, as an
explicit function of the cutoff: the averaged diagonal integral over the odd band minus the two
rank-one terms. -/
def weightedPWLevelAverageTrace (Y L : ℝ) (φ : ℝ → ℝ) (a b : ℝ) : ℂ :=
  (∫ g in a..b, (φ g : ℂ) * weightedOddDiagonal Y L g / (g : ℂ)) -
    ⟪weightedKernelVector Y,
      realCutoff L (weightedPWDilationAverage φ a b (weightedKernelVector Y))⟫_ℂ /
      (‖weightedKernelVector Y‖ : ℂ) ^ 2 -
    ⟪weightedLevelVector Y,
      realCutoff L (weightedPWDilationAverage φ a b (weightedLevelVector Y))⟫_ℂ /
      (‖weightedLevelVector Y‖ : ℂ) ^ 2

/-- The averaged compression to the weighted band, in the Paley–Wiener picture, is nuclear, and
its trace is the averaged diagonal integral minus the rank-one term of the reproducing
vector. -/
theorem hilbertTrace_weightedPWBand_average_compression (hY : 0 < Y) (hL : 0 ≤ L) (ha : 1 ≤ a)
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) :
    ∃ hn : IsNuclearOperator ((weightedPWBand Y).starProjection ∘L
        (realCutoff L ∘L weightedPWDilationAverage φ a b) ∘L (weightedPWBand Y).starProjection),
      hilbertTrace ⟨_, hn⟩ =
        (∫ g in a..b, (φ g : ℂ) * weightedOddDiagonal Y L g / (g : ℂ)) -
          ⟪weightedKernelVector Y,
            realCutoff L (weightedPWDilationAverage φ a b (weightedKernelVector Y))⟫_ℂ /
            (‖weightedKernelVector Y‖ : ℂ) ^ 2 := by
  have hinst : (realOddBand Y ⊓ (ℂ ∙ weightedKernelVector Y)ᗮ).HasOrthogonalProjection :=
    inferInstanceAs (weightedPWBand Y).HasOrthogonalProjection
  have hmain := hilbertTrace_compression_inf_orthogonal_span_singleton
    (weightedKernelVector_mem Y) (weightedKernelVector_ne_zero hY)
    (realCutoff L ∘L weightedPWDilationAverage φ a b)
    (isNuclearOperator_realOddBand_average_compression hY hL ha hab hφ)
  obtain ⟨hn', htr'⟩ := hmain
  rw [hilbertTrace_realOddBand_average_compression hY hL ha hab hφ] at htr'
  exact ⟨hn', htr'⟩

/-- The averaged compression to the level, in the Paley–Wiener picture, is nuclear, and its
trace is `weightedPWLevelAverageTrace`. -/
theorem hilbertTrace_weightedPWLevel_average_compression (hY : 0 < Y) (hL : 0 ≤ L) (ha : 1 ≤ a)
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) :
    ∃ hn : IsNuclearOperator ((weightedPWLevel Y).starProjection ∘L
        (realCutoff L ∘L weightedPWDilationAverage φ a b) ∘L (weightedPWLevel Y).starProjection),
      hilbertTrace ⟨_, hn⟩ = weightedPWLevelAverageTrace Y L φ a b := by
  have hband := hilbertTrace_weightedPWBand_average_compression hY hL ha hab hφ
  obtain ⟨hn, htr⟩ := hband
  have hinst : (weightedPWBand Y ⊓ (ℂ ∙ weightedLevelVector Y)ᗮ).HasOrthogonalProjection :=
    inferInstanceAs (weightedPWLevel Y).HasOrthogonalProjection
  have hmain := hilbertTrace_compression_inf_orthogonal_span_singleton
    (weightedLevelVector_mem Y) (weightedLevelVector_ne_zero hY)
    (realCutoff L ∘L weightedPWDilationAverage φ a b) hn
  obtain ⟨hn', htr'⟩ := hmain
  rw [htr] at htr'
  exact ⟨hn', htr'⟩

/-- **The limit of the averaged traces on the level, in the Paley–Wiener picture.** For a
continuous `φ` on an interval `[a, b]` of `(1, ∞)`, the traces tend to
`∫ φ (g) (g ^ (3/2) / (g ^ 2 - 1) - g ^ (-1/2) - g ^ (1/2)) dg / g`. -/
theorem tendsto_weightedPWLevelAverageTrace (hY : 0 < Y) (ha : 1 < a) (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) :
    Tendsto (fun L : ℝ ↦ weightedPWLevelAverageTrace Y L φ a b) atTop
      (𝓝 (((∫ g in a..b, φ g * (g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ - √g) / g : ℝ) : ℂ))) := by
  have hk0 : (‖weightedKernelVector Y‖ : ℂ) ^ 2 ≠ 0 := by
    have : (‖weightedKernelVector Y‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_pos_iff.mpr (weightedKernelVector_ne_zero hY)).ne'
    exact pow_ne_zero 2 this
  have he0 : (‖weightedLevelVector Y‖ : ℂ) ^ 2 ≠ 0 := by
    have : (‖weightedLevelVector Y‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_pos_iff.mpr (weightedLevelVector_ne_zero hY)).ne'
    exact pow_ne_zero 2 this
  have hkk : ⟪weightedKernelVector Y, weightedKernelVector Y⟫_ℂ =
      (‖weightedKernelVector Y‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
  have hee : ⟪weightedLevelVector Y, weightedLevelVector Y⟫_ℂ =
      (‖weightedLevelVector Y‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
  have h1 := tendsto_integral_mul_weightedOddDiagonal hY ha hab hφ
  have h2 := (tendsto_inner_realCutoff_weightedPWDilationAverage ha.le hab hφ
    (weightedKernelVector Y) (weightedKernelVector Y)).div_const
    ((‖weightedKernelVector Y‖ : ℂ) ^ 2)
  have h3 := (tendsto_inner_realCutoff_weightedPWDilationAverage ha.le hab hφ
    (weightedLevelVector Y) (weightedLevelVector Y)).div_const
    ((‖weightedLevelVector Y‖ : ℂ) ^ 2)
  have h := (h1.sub h2).sub h3
  have hsub : Icc a b ⊆ Ioi 1 := fun g hg ↦ ha.trans_le hg.1
  have hpos : ∀ g ∈ Icc a b, (g : ℂ) ≠ 0 := fun g hg ↦ by
    exact_mod_cast (zero_lt_one.trans (hsub hg)).ne'
  have hφc : ContinuousOn (fun g : ℝ ↦ (φ g : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn hφ
  have hid : ContinuousOn (fun g : ℝ ↦ (g : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.continuousOn
  have hVc : ContinuousOn (fun g : ℝ ↦ g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹) (Icc a b) := by
    refine ContinuousOn.sub (ContinuousOn.div
      (Real.continuous_rpow_const (by norm_num)).continuousOn (by fun_prop) fun g hg ↦ ?_)
      (ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn fun g hg ↦ ?_)
    · have : (1 : ℝ) < g := hsub hg
      nlinarith
    · exact (Real.sqrt_pos.mpr (zero_lt_one.trans (hsub hg))).ne'
  have i1 : IntervalIntegrable (fun g : ℝ ↦ (φ g : ℂ) *
      ((g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ : ℝ) : ℂ) / (g : ℂ)) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab ((hφc.mul
      (Complex.continuous_ofReal.comp_continuousOn hVc)).div hid hpos)
  have i2 : IntervalIntegrable (fun g : ℝ ↦ (φ g : ℂ) * weightedBandDefect Y g / (g : ℂ))
      volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab ((hφc.mul
      ((continuousOn_weightedBandDefect Y).mono hsub)).div hid hpos)
  have i3 : IntervalIntegrable (fun g : ℝ ↦ (φ g : ℂ) * ((√g : ℝ) : ℂ) / (g : ℂ)) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab ((hφc.mul
      (Complex.continuous_ofReal.comp_continuousOn Real.continuous_sqrt.continuousOn)).div
      hid hpos)
  have hI1 : ∫ g in a..b, (φ g : ℂ) * (((g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ : ℝ) : ℂ) +
      weightedBandDefect Y g) / (g : ℂ) =
      (∫ g in a..b, (φ g : ℂ) * ((g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ : ℝ) : ℂ) / (g : ℂ)) +
        ∫ g in a..b, (φ g : ℂ) * weightedBandDefect Y g / (g : ℂ) := by
    rw [← intervalIntegral.integral_add i1 i2]
    refine intervalIntegral.integral_congr fun g _ ↦ ?_
    ring
  have hI2 : ∫ g in a..b, ((φ g / g : ℝ) : ℂ) *
      ⟪weightedKernelVector Y, weightedPWDilation g (weightedKernelVector Y)⟫_ℂ =
      (‖weightedKernelVector Y‖ : ℂ) ^ 2 *
        ∫ g in a..b, (φ g : ℂ) * weightedBandDefect Y g / (g : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun g hg ↦ ?_
    rw [uIcc_of_le hab] at hg
    have hg1 : 1 < g := hsub hg
    rw [inner_weightedKernelVector_multiplier_dilation hY.le hg1
      (coeFn_weightedPWDilation hg1.le _), hkk]
    push_cast
    ring
  have hI3 : ∫ g in a..b, ((φ g / g : ℝ) : ℂ) *
      ⟪weightedLevelVector Y, weightedPWDilation g (weightedLevelVector Y)⟫_ℂ =
      (‖weightedLevelVector Y‖ : ℂ) ^ 2 *
        ∫ g in a..b, (φ g : ℂ) * ((√g : ℝ) : ℂ) / (g : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun g hg ↦ ?_
    rw [uIcc_of_le hab] at hg
    have hg1 : 1 < g := hsub hg
    rw [inner_weightedLevelVector_weightedPWDilation hg1.le, hee]
    push_cast
    ring
  rw [hI1, hI2, hI3, mul_div_cancel_left₀ _ hk0, mul_div_cancel_left₀ _ he0,
    add_sub_cancel_right, ← intervalIntegral.integral_sub i1 i3] at h
  have hfin : ∫ g in a..b, ((φ g : ℂ) * ((g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ : ℝ) : ℂ) /
      (g : ℂ) - (φ g : ℂ) * ((√g : ℝ) : ℂ) / (g : ℂ)) =
      ((∫ g in a..b, φ g * (g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ - √g) / g : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun g _ ↦ ?_
    push_cast
    ring
  rw [hfin] at h
  exact h

end Average

/-! ### The averaged compression on the weighted space -/

section Weighted

local notation "Hw" => Lp ℂ 2 weightedBandMeasure

variable {Y L a b : ℝ} {φ : ℝ → ℝ}

/-- The average of the dilations of the weighted space against `φ (g) dg / g`. It is defined
through the unitary, and `weightedBandDilationAverage_apply` proves that it is the integral of
the dilations. -/
def weightedBandDilationAverage (φ : ℝ → ℝ) (a b : ℝ) : Hw →L[ℂ] Hw :=
  weightedBandUnitary.symm.toLinearIsometry.toContinuousLinearMap ∘L
    weightedPWDilationAverage φ a b ∘L weightedBandUnitary.toLinearIsometry.toContinuousLinearMap

/-- The unitary carries the average on the weighted space to the average in `L²(ℝ)`. -/
theorem weightedBandUnitary_weightedBandDilationAverage (φ : ℝ → ℝ) (a b : ℝ) (f : Hw) :
    weightedBandUnitary (weightedBandDilationAverage φ a b f) =
      weightedPWDilationAverage φ a b (weightedBandUnitary f) := by
  change weightedBandUnitary (weightedBandUnitary.symm
    (weightedPWDilationAverage φ a b (weightedBandUnitary f))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

/-- The average on the weighted space is the integral of the dilations against
`φ (g) dg / g`. -/
theorem weightedBandDilationAverage_apply (ha : 1 ≤ a) (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) (f : Hw) :
    weightedBandDilationAverage φ a b f =
      ∫ g in a..b, ((φ g / g : ℝ) : ℂ) • weightedBandDilation g f := by
  change weightedBandUnitary.symm (weightedPWDilationAverage φ a b (weightedBandUnitary f)) = _
  rw [weightedPWDilationAverage_apply ha hab hφ]
  have h := ContinuousLinearMap.intervalIntegral_comp_comm
    weightedBandUnitary.symm.toLinearIsometry.toContinuousLinearMap
    (intervalIntegrable_smul_weightedPWDilation ha hab hφ (weightedBandUnitary f))
  refine h.symm.trans (intervalIntegral.integral_congr fun g _ ↦ ?_)
  change weightedBandUnitary.symm (((φ g / g : ℝ) : ℂ) •
    weightedPWDilation g (weightedBandUnitary f)) = _
  rw [map_smul]
  rfl

/-- The averaged compression to the level of the weighted model is nuclear, and its trace is
`weightedPWLevelAverageTrace`. -/
theorem hilbertTrace_weightedLevel_average_compression (hY : 0 < Y) (hL : 0 ≤ L) (ha : 1 ≤ a)
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) :
    ∃ hn : IsNuclearOperator ((weightedLevel Y).starProjection ∘L
        (weightedBandCutoff L ∘L weightedBandDilationAverage φ a b) ∘L
        (weightedLevel Y).starProjection),
      hilbertTrace ⟨_, hn⟩ = weightedPWLevelAverageTrace Y L φ a b := by
  have h := hilbertTrace_weightedPWLevel_average_compression hY hL ha hab hφ
  obtain ⟨hn, htr⟩ := h
  have h2 := hilbertTrace_compression_of_unitary weightedBandUnitary (weightedLevel Y)
    (weightedPWLevel Y) (weightedLevel_map_weightedBandUnitary Y)
    (weightedBandCutoff L ∘L weightedBandDilationAverage φ a b)
    (realCutoff L ∘L weightedPWDilationAverage φ a b)
    (fun f ↦ by
      change weightedBandUnitary (weightedBandCutoff L (weightedBandDilationAverage φ a b f)) =
        realCutoff L (weightedPWDilationAverage φ a b (weightedBandUnitary f))
      rw [weightedBandUnitary_weightedBandCutoff, weightedBandUnitary_weightedBandDilationAverage])
    hn
  obtain ⟨hn', htr'⟩ := h2
  exact ⟨hn', htr'.trans htr⟩

/-- Paper: Theorem 12.4.1.1, pp. 514–519, and the value used on p. 520. **On the level of the
weighted model, the traces against a test function tend to the real-place term minus both pole
terms.** Let `w x = x ^ 2 + x ^ (-2)`, let `P` be the orthogonal projection of `L²(ℝ, w dx)`
onto the level `weightedLevel Y`, `M_L` the multiplication by `1_[-L, L]`, and
`A f = ∫ φ (g) g^(-1/2) f (x / g) dg / g` for a continuous `φ` on an interval `[a, b]` of
`(1, ∞)`. Then `P ∘ M_L ∘ A ∘ P` is nuclear for `L ≥ 0`, and its Hilbert trace tends, as
`L → ∞` at fixed `Y > 0`, to `∫ φ (g) (g ^ (3/2) / (g ^ 2 - 1) - g ^ (-1/2) - g ^ (1/2)) dg / g`.
Reconstruction: the rational real-place model at order zero, with this weight in place of the
logarithmic weight of the paper and the sharp spatial cutoff. The test is supported in dilations
larger than one. -/
theorem tendsto_hilbertTrace_weightedLevel_average_compression (hY : 0 < Y) (ha : 1 < a)
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) :
    ∃ tr : ℝ → ℂ,
      (∀ L : ℝ, 0 ≤ L → ∃ hn : IsNuclearOperator ((weightedLevel Y).starProjection ∘L
          (weightedBandCutoff L ∘L weightedBandDilationAverage φ a b) ∘L
          (weightedLevel Y).starProjection), hilbertTrace ⟨_, hn⟩ = tr L) ∧
      Tendsto tr atTop (𝓝 (((∫ g in a..b,
        φ g * (g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ - √g) / g : ℝ) : ℂ))) :=
  ⟨fun L ↦ weightedPWLevelAverageTrace Y L φ a b,
    fun _ hL ↦ hilbertTrace_weightedLevel_average_compression hY hL ha.le hab hφ,
    tendsto_weightedPWLevelAverageTrace hY ha hab hφ⟩

end Weighted

end RiemannMasullo
