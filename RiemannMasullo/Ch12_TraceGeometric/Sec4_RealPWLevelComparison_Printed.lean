module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWIntegralLevelTrace
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # The comparison of the level trace with the sharp orbital masses in §12.4

The step of Theorem 12.4.1.1 that #7354 leaves open after #7440 and #7498 is the comparison of
the diagonal integral of the kernel on the level with the summed sharp orbital masses (errata
entry I398). This file tests that comparison in the model `F = ℚ`, `S = {∞}`, for the
compression to the polar-free level of the cutoff of the action of a test function supported
away from `g = 1`. It fails, for both choices of parameters that the paper makes.

With the weight `(1 + log² |x|) ^ (s / 2)` of the proof on p. 515, the level is the space of
band vectors vanishing at the origin. The trace on the level converges
(`exists_realPWTestCutoff_level_trace_limit`). Its limit is the real term of (12.4.1.1) minus
`∫ ψ g g ^ (-1/2) dg`, which with `ψ g = φ g / g` has the form of the Mellin value
`M(φ)(|·| ^ (-1/2))`. On the whole band the limit is the real term
(`exists_realPWTestCutoff_trace_limit`), so the difference comes from the level alone: it is
the diagonal entry at the direction that the condition `h(0) = 0` removes.

With the weight of width one half and `s > 1`, the case `a = 1/2`, `s ≥ 2 [F : ℚ]` of p. 487
that the proof of Theorem 12.5.1.1 uses on p. 520, the level is the space of band vectors of
integral zero. The trace on the level converges
(`exists_realPWTestCutoff_integralLevel_trace_limit`), and its limit is the real term minus
`∫ ψ g g ^ (-1/2) dg` minus `∫ ψ g g ^ (1/2) dg`. These have the form of the two Mellin values
`M(φ)(|·| ^ (-1/2))` and `M(φ)(|·| ^ (1/2))` that p. 520 subtracts.

The statements are the project's reconstruction of one reading of the proof, not statements
that the paper prints for this model. The reading is the one of dyknapp's fixed-level
construction in #7354: the weighted space, the level the closure of the polar-free tests, the
operator its orthogonal compression. Two things are not covered. The spatial cutoff is the
sharp indicator of `[-L, L]`, with no inner radius. The test function is supported in `g > 1`
and away from `g = 1`. The joint limit is treated for the first weight only. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology InnerProductSpace

namespace RiemannMasullo

open Isolated

/-- The density of the real term of (12.4.1.1), p. 514, summed over the two signs of the
dilation, as a function of `g > 1`. -/
def sLocalTrace_realTermDensity (g : ℝ) : ℂ :=
  ((1 / 2 * ((g - 1)⁻¹ + (g + 1)⁻¹) * g ^ (1 / 2 : ℝ) : ℝ) : ℂ)

/-- Paper: Theorem 12.4.1.1, (12.4.1.1), p. 514, with Steps II–III of its proof, pp. 516–517,
read in the model `F = ℚ`, `S = {∞}` of #7354. For a test function supported away from
`g = 1` the term `φ(1) log(λλ')` is absent, and the statement says that the trace of the
cutoff action on the polar-free invariant Paley–Wiener level tends to the real term.
Reconstruction: The paper does not state this for the model. The space is the weighted even
band with weight `(1 + log² |x|) ^ (s / 2)`, the level is the space of band vectors vanishing
at the origin, which is the closure of the polar-free core (#7770), the spatial cutoff is the
sharp indicator of `[-L, L]`, and the bandwidth `Y` is fixed. The operator is the compression
to the level of the cutoff of `f ↦ ∫ ψ g g ^ (-1/2) f (g⁻¹ x) dg`, where `ψ g = φ g / g`.
Deviation: The limit is taken in the spatial cutoff at fixed bandwidth, where the paper has a
joint limit. A joint limit, if it exists, equals the limit at fixed bandwidth. -/
def sLocalTrace_realPWLevelSharpComparison : Prop :=
  ∀ (Y s : ℝ) (hs : 0 ≤ s), 0 < Y → ∀ (a b : ℝ), 1 < a → ∀ ψ : ℝ → ℂ, Continuous ψ →
    (∀ g ∉ Icc a b, ψ g = 0) →
    ∀ T : ℝ → nuclearEndomorphisms
        (RealPWBand.space Y (volume_le_realPWIntervalMeasure 0 s hs)),
      (∀ L (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure 0 s hs)),
        ∃ r : Lp ℂ 2 (realPWIntervalMeasure 0 s),
          (∀ᵐ x ∂realPWIntervalMeasure 0 s, r x = sharpIntervalMask L x *
            ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure 0 s hs) (g⁻¹ * x)
                ((realPWZeroLevel Y 0 s hs).starProjection f))) ∧
          (T L).val f = (realPWZeroLevel Y 0 s hs).starProjection
            ((RealPWBand.space Y (volume_le_realPWIntervalMeasure 0 s hs)).orthogonalProjectionOnto
              r)) →
      Tendsto (fun L ↦ hilbertTrace (T L)) atTop
        (𝓝 (∫ g, ψ g * sLocalTrace_realTermDensity g))

/-- A nonnegative continuous test supported in `[2, 3]` whose integral against every real power
of `g` is a positive real number. -/
private theorem exists_test_integral_pos :
    ∃ ψ : ℝ → ℂ, Continuous ψ ∧ (∀ g ∉ Icc (2 : ℝ) 3, ψ g = 0) ∧
      ∀ p : ℝ, ∃ c : ℝ, 0 < c ∧ ∫ g, ψ g * ((g ^ p : ℝ) : ℂ) = (c : ℂ) := by
  let B : ContDiffBump (5 / 2 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hB0 : ∀ g ∉ Icc (2 : ℝ) 3, B g = 0 := by
    intro g hg
    apply B.zero_of_le_dist
    rw [Real.dist_eq]
    by_contra h
    have h' := abs_lt.mp (not_le.mp h)
    exact hg ⟨by norm_num [B] at h' ⊢; linarith [h'.1], by norm_num [B] at h' ⊢; linarith [h'.2]⟩
  refine ⟨fun g ↦ ((B g : ℝ) : ℂ), Complex.continuous_ofReal.comp B.continuous,
    fun g hg ↦ by
      change ((B g : ℝ) : ℂ) = 0
      rw [hB0 g hg, Complex.ofReal_zero], fun p ↦ ?_⟩
  let h : ℝ → ℝ := fun g ↦ B g * g ^ p
  have hcast : (fun g : ℝ ↦ ((B g : ℝ) : ℂ) * ((g ^ p : ℝ) : ℂ)) =
      fun g ↦ ((h g : ℝ) : ℂ) := by
    funext g
    change ((B g : ℝ) : ℂ) * ((g ^ p : ℝ) : ℂ) = ((B g * g ^ p : ℝ) : ℂ)
    rw [Complex.ofReal_mul]
  have hnn : 0 ≤ h := by
    intro g
    by_cases hg : g ∈ Icc (2 : ℝ) 3
    · exact mul_nonneg B.nonneg (Real.rpow_nonneg (by linarith [hg.1]) _)
    · change 0 ≤ B g * g ^ p
      rw [hB0 g hg, zero_mul]
  have hint : Integrable h := by
    have h1 : IntegrableOn h (Icc (2 : ℝ) 3) :=
      (B.continuous.continuousOn.mul (continuousOn_id.rpow_const fun g hg ↦
        Or.inl (by linarith [hg.1] : (0 : ℝ) < g).ne')).integrableOn_Icc
    refine (integrableOn_iff_integrable_of_support_subset fun g hg ↦ ?_).mp h1
    by_contra hgn
    exact hg (by
      change B g * g ^ p = 0
      rw [hB0 g hgn, zero_mul])
  have hpos : 0 < ∫ g, h g := by
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    refine lt_of_lt_of_le
      (Metric.measure_ball_pos volume (5 / 2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4))
      (measure_mono fun g hg ↦ ?_)
    have hg' := abs_lt.mp (by simpa [Real.dist_eq] using hg : |g - 5 / 2| < 1 / 4)
    have hB1 : B g = 1 := B.one_of_mem_closedBall (Metric.ball_subset_closedBall hg)
    have hgpos : 0 < g := by linarith [hg'.1]
    change B g * g ^ p ≠ 0
    rw [hB1, one_mul]
    exact (Real.rpow_pos_of_pos hgpos _).ne'
  refine ⟨∫ g, h g, hpos, ?_⟩
  change ∫ g, ((B g : ℝ) : ℂ) * ((g ^ p : ℝ) : ℂ) = _
  rw [hcast, integral_complex_ofReal]

/-- A nonnegative continuous test supported in `[2, 3]` whose integral against `g ^ (-1/2)` is
not zero. -/
private theorem exists_test_integral_ne_zero :
    ∃ ψ : ℝ → ℂ, Continuous ψ ∧ (∀ g ∉ Icc (2 : ℝ) 3, ψ g = 0) ∧
      ∫ g, ψ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
  obtain ⟨ψ, hψc, hψ0, hp⟩ := exists_test_integral_pos
  obtain ⟨c, hc, hce⟩ := hp (-(1 / 2 : ℝ))
  exact ⟨ψ, hψc, hψ0, by
    rw [hce]
    exact Complex.ofReal_ne_zero.mpr hc.ne'⟩

/-- Paper: Theorem 12.4.1.1, pp. 514–517. In the model the trace on the level does converge,
and its limit is the real term minus the integral of `ψ g g ^ (-1/2)`, which with `ψ g = φ g / g`
has the form of the Mellin value `M(φ)(|·| ^ (-1/2))` of p. 519. So the reconstruction
`sLocalTrace_realPWLevelSharpComparison` fails for every nonnegative nonzero test. On the whole
band, without the level, the limit is the real term (`exists_realPWTestCutoff_trace_limit` with
`realPWSharpTraceLimit_of_lt_half`). -/
theorem sLocalTrace_realPWLevelSharpComparison_false :
    ¬ sLocalTrace_realPWLevelSharpComparison := by
  intro hcomp
  obtain ⟨ψ, hψc, hψ0, hne⟩ := exists_test_integral_ne_zero
  have hs : (0 : ℝ) ≤ 0 := le_rfl
  have ha1 : (1 : ℝ) < 2 := by norm_num
  obtain ⟨T, hT1, hT2⟩ := exists_realPWTestCutoff_level_trace_limit 1 0 0 hs one_pos le_rfl
    (by norm_num) ha1 ψ hψc hψ0
  have h1 := hcomp 1 0 hs one_pos 2 3 ha1 ψ hψc hψ0 T hT1
  have heq := tendsto_nhds_unique hT2 h1
  have hlim : ∫ g, ψ g * realPWSharpTraceLimit 0 g = ∫ g, ψ g * sLocalTrace_realTermDensity g := by
    refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    by_cases hg : g ∈ Icc (2 : ℝ) 3
    · change ψ g * realPWSharpTraceLimit 0 g = ψ g * sLocalTrace_realTermDensity g
      rw [realPWSharpTraceLimit_of_lt_half (by norm_num) (by linarith [hg.1])]
      rfl
    · change ψ g * realPWSharpTraceLimit 0 g = ψ g * sLocalTrace_realTermDensity g
      rw [hψ0 g hg, zero_mul, zero_mul]
  rw [hlim] at heq
  exact hne (sub_eq_self.mp heq)

/-- Paper: Theorem 12.4.1.1, (12.4.1.1), p. 514, in the same model, with the joint limit in the
spatial cutoff `L` and the bandwidth `Y` that the paper states.
Reconstruction: As for `sLocalTrace_realPWLevelSharpComparison`. One operator is given for
each bandwidth and each cutoff, and the limit is along the product of the two filters at
infinity, as in `sLocalTrace_asymptotic_of_sharp_comparison`. -/
def sLocalTrace_realPWLevelSharpComparison_joint : Prop :=
  ∀ (s : ℝ) (hs : 0 ≤ s) (a b : ℝ), 1 < a → ∀ ψ : ℝ → ℂ, Continuous ψ →
    (∀ g ∉ Icc a b, ψ g = 0) →
    ∀ T : (Y : ℝ) → ℝ → nuclearEndomorphisms
        (RealPWBand.space Y (volume_le_realPWIntervalMeasure 0 s hs)),
      (∀ Y, 0 < Y → ∀ L (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure 0 s hs)),
        ∃ r : Lp ℂ 2 (realPWIntervalMeasure 0 s),
          (∀ᵐ x ∂realPWIntervalMeasure 0 s, r x = sharpIntervalMask L x *
            ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure 0 s hs) (g⁻¹ * x)
                ((realPWZeroLevel Y 0 s hs).starProjection f))) ∧
          (T Y L).val f = (realPWZeroLevel Y 0 s hs).starProjection
            ((RealPWBand.space Y (volume_le_realPWIntervalMeasure 0 s hs)).orthogonalProjectionOnto
              r)) →
      Tendsto (fun p : ℝ × ℝ ↦ hilbertTrace (T p.2 p.1)) (atTop ×ˢ atTop)
        (𝓝 (∫ g, ψ g * sLocalTrace_realTermDensity g))

/-- A joint limit along the product of the filters at infinity equals the limit in the first
variable at a fixed large value of the second, when that limit does not depend on it. -/
private theorem eq_of_tendsto_prod_atTop_of_fiber {f : ℝ × ℝ → ℂ} {ℓ c : ℂ}
    (hj : Tendsto f (atTop ×ˢ atTop) (𝓝 ℓ))
    (hf : ∀ᶠ Y in atTop, Tendsto (fun L ↦ f (L, Y)) atTop (𝓝 c)) : ℓ = c := by
  by_contra hne
  have hd : 0 < dist ℓ c := dist_pos.mpr hne
  have h1 := Metric.tendsto_nhds.mp hj (dist ℓ c / 2) (half_pos hd)
  obtain ⟨pa, hpa, pb, hpb, hp⟩ := Filter.eventually_prod_iff.mp h1
  obtain ⟨Y, hY1, hY2⟩ := (hpb.and hf).exists
  have h2 : ∀ᶠ L in atTop, dist (f (L, Y)) ℓ ≤ dist ℓ c / 2 :=
    hpa.mono fun L hL ↦ (hp hL hY1).le
  have h3 : dist c ℓ ≤ dist ℓ c / 2 := le_of_tendsto (hY2.dist tendsto_const_nhds) h2
  rw [dist_comm] at h3
  linarith

/-- Paper: Theorem 12.4.1.1, pp. 514–517. The joint form of the comparison fails as well: at
every fixed bandwidth the trace on the level tends to the real term minus the integral of
`ψ g g ^ (-1/2)`, so a joint limit can only be that number. -/
theorem sLocalTrace_realPWLevelSharpComparison_joint_false :
    ¬ sLocalTrace_realPWLevelSharpComparison_joint := by
  intro hcomp
  obtain ⟨ψ, hψc, hψ0, hne⟩ := exists_test_integral_ne_zero
  have hs : (0 : ℝ) ≤ 0 := le_rfl
  have ha1 : (1 : ℝ) < 2 := by norm_num
  have hex := fun (Y : ℝ) (hY : 0 < Y) ↦
    exists_realPWTestCutoff_level_trace_limit Y 0 0 hs hY le_rfl (by norm_num) ha1 ψ hψc hψ0
  let T : (Y : ℝ) → ℝ → nuclearEndomorphisms
      (RealPWBand.space Y (volume_le_realPWIntervalMeasure 0 0 hs)) :=
    fun Y ↦ if hY : 0 < Y then (hex Y hY).choose else fun _ ↦ 0
  have hTY : ∀ Y (hY : 0 < Y), T Y = (hex Y hY).choose := fun Y hY ↦ dite_eq_left hY
  have hjoint := hcomp 0 hs 2 3 ha1 ψ hψc hψ0 T (fun Y hY ↦ by
    rw [hTY Y hY]
    exact (hex Y hY).choose_spec.1)
  have hfib : ∀ᶠ Y in atTop, Tendsto (fun L ↦ hilbertTrace (T Y L)) atTop
      (𝓝 ((∫ g, ψ g * realPWSharpTraceLimit 0 g) -
        ∫ g, ψ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    rw [hTY Y hY]
    exact (hex Y hY).choose_spec.2
  have heq := eq_of_tendsto_prod_atTop_of_fiber hjoint hfib
  have hlim : ∫ g, ψ g * realPWSharpTraceLimit 0 g = ∫ g, ψ g * sLocalTrace_realTermDensity g := by
    refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    by_cases hg : g ∈ Icc (2 : ℝ) 3
    · change ψ g * realPWSharpTraceLimit 0 g = ψ g * sLocalTrace_realTermDensity g
      rw [realPWSharpTraceLimit_of_lt_half (by norm_num) (by linarith [hg.1])]
      rfl
    · change ψ g * realPWSharpTraceLimit 0 g = ψ g * sLocalTrace_realTermDensity g
      rw [hψ0 g hg, zero_mul, zero_mul]
  rw [hlim] at heq
  exact hne (sub_eq_self.mp heq.symm)

/-- Paper: Theorem 12.4.1.1, (12.4.1.1), p. 514, with Steps II–III of its proof, pp. 516–517,
read in the model `F = ℚ`, `S = {∞}` of #7354 at the parameters `a = 1/2`, `s ≥ 2 [F : ℚ]` of
p. 487, which the proof of Theorem 12.5.1.1 uses on p. 520. The statement says that the trace
of the cutoff action on the polar-free level tends to the real term.
Reconstruction: The paper does not state this for the model. The space is the weighted even
band with weight `max(|x|, |x|⁻¹) (1 + log² |x|) ^ (s / 2)` and `s > 1`. The level is the
closure of the polar-free core, given as the orthogonal complement of a band vector `e`. It is
the space of band vectors of integral zero (#7771). The spatial cutoff is the sharp indicator
of `[-L, L]`, and the bandwidth `Y` is fixed. The operator is the compression to the level of
the cutoff of `f ↦ ∫ ψ g g ^ (-1/2) f (g⁻¹ x) dg`, where `ψ g = φ g / g`.
Deviation: The limit is taken in the spatial cutoff at fixed bandwidth, where the paper has a
joint limit. -/
def sLocalTrace_realPWIntegralLevelSharpComparison : Prop :=
  ∀ (Y s : ℝ) (hs : 0 ≤ s), 0 < Y → 1 < s → ∀ (a b : ℝ), 1 < a → ∀ ψ : ℝ → ℂ, Continuous ψ →
    (∀ g ∉ Icc a b, ψ g = 0) →
    ∀ e : RealPWBand.space Y (volume_le_realPWIntervalMeasure (1 / 2) s hs),
      (((ℂ ∙ e)ᗮ : Submodule ℂ
          (RealPWBand.space Y (volume_le_realPWIntervalMeasure (1 / 2) s hs))) :
        Set (RealPWBand.space Y (volume_le_realPWIntervalMeasure (1 / 2) s hs))) =
        closure (realPWBandPolarFreeCore Y (1 / 2) hs) →
    ∀ T : ℝ → nuclearEndomorphisms
        (RealPWBand.space Y (volume_le_realPWIntervalMeasure (1 / 2) s hs)),
      (∀ L (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure (1 / 2) s hs)),
        ∃ r : Lp ℂ 2 (realPWIntervalMeasure (1 / 2) s),
          (∀ᵐ x ∂realPWIntervalMeasure (1 / 2) s, r x = sharpIntervalMask L x *
            ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure (1 / 2) s hs) (g⁻¹ * x)
                ((ℂ ∙ e)ᗮ.starProjection f))) ∧
          (T L).val f = (ℂ ∙ e)ᗮ.starProjection
            ((RealPWBand.space Y
              (volume_le_realPWIntervalMeasure (1 / 2) s hs)).orthogonalProjectionOnto r)) →
      Tendsto (fun L ↦ hilbertTrace (T L)) atTop
        (𝓝 (∫ g, ψ g * sLocalTrace_realTermDensity g))

/-- The product of a continuous test supported in `[a, b]` with a function continuous on
`[a, b]` is integrable. -/
private theorem integrable_test_mul {ψ : ℝ → ℂ} (hψc : Continuous ψ) {a b : ℝ}
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) {h : ℝ → ℂ} (hh : ContinuousOn h (Icc a b)) :
    Integrable (fun g ↦ ψ g * h g) := by
  have h1 : IntegrableOn (fun g ↦ ψ g * h g) (Icc a b) :=
    (hψc.continuousOn.mul hh).integrableOn_Icc
  refine (integrableOn_iff_integrable_of_support_subset fun g hg ↦ ?_).mp h1
  by_contra hgn
  exact hg (by
    change ψ g * h g = 0
    rw [hψ0 g hgn, zero_mul])

/-- The density of the real term is continuous on an interval to the right of `1`. -/
private theorem continuousOn_realTermDensity {a b : ℝ} (ha : 1 < a) :
    ContinuousOn sLocalTrace_realTermDensity (Icc a b) := by
  have h1 : ContinuousOn (fun g : ℝ ↦ (g - 1)⁻¹) (Icc a b) :=
    ContinuousOn.inv₀ (by fun_prop) fun g hg ↦ (by linarith [hg.1] : (0 : ℝ) < g - 1).ne'
  have h2 : ContinuousOn (fun g : ℝ ↦ (g + 1)⁻¹) (Icc a b) :=
    ContinuousOn.inv₀ (by fun_prop) fun g hg ↦ (by linarith [hg.1] : (0 : ℝ) < g + 1).ne'
  have h3 : ContinuousOn (fun g : ℝ ↦ g ^ (1 / 2 : ℝ)) (Icc a b) :=
    (Real.continuous_rpow_const (by norm_num)).continuousOn
  exact Complex.continuous_ofReal.comp_continuousOn
    ((continuousOn_const.mul (h1.add h2)).mul h3)

/-- Paper: Theorem 12.4.1.1, pp. 514–517, and the proof of Theorem 12.5.1.1, p. 520. At width
one half with `s > 1` the trace on the level converges, and its limit is the real term minus
the integrals of `ψ g g ^ (-1/2)` and `ψ g g ^ (1/2)`. So the reconstruction
`sLocalTrace_realPWIntegralLevelSharpComparison` fails for every nonnegative nonzero test. The
two integrals have the form of the Mellin values that p. 520 subtracts from the diagonal
integral. -/
theorem sLocalTrace_realPWIntegralLevelSharpComparison_false :
    ¬ sLocalTrace_realPWIntegralLevelSharpComparison := by
  intro hcomp
  obtain ⟨ψ, hψc, hψ0, hp⟩ := exists_test_integral_pos
  obtain ⟨c₁, hc₁, he₁⟩ := hp (-(1 / 2 : ℝ))
  obtain ⟨c₂, hc₂, he₂⟩ := hp (1 / 2 : ℝ)
  have hs : (0 : ℝ) ≤ 2 := by norm_num
  have ha1 : (1 : ℝ) < 2 := by norm_num
  have hint : Integrable (fun x ↦ (realPWIntervalWeight (1 / 2) 2 x)⁻¹) :=
    integrable_inv_realPWIntervalWeight_half (by norm_num)
  obtain ⟨e, hlevel, T, hT1, hT2⟩ := exists_realPWTestCutoff_integralLevel_trace_limit 1
    (1 / 2) 2 hs one_pos le_rfl (by norm_num) hint ha1 ψ hψc hψ0
  have h1 := hcomp 1 2 hs one_pos (by norm_num) 2 3 ha1 ψ hψc hψ0 e hlevel T hT1
  have heq := tendsto_nhds_unique hT2 h1
  have hP : Integrable (fun g ↦ ψ g * sLocalTrace_realTermDensity g) :=
    integrable_test_mul hψc hψ0 (continuousOn_realTermDensity ha1)
  have hq : Integrable (fun g ↦ ψ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) :=
    integrable_test_mul hψc hψ0 (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.rpow_const fun g hg ↦
        Or.inl (by linarith [hg.1] : (0 : ℝ) < g).ne'))
  have hlim : ∫ g, ψ g * realPWSharpTraceLimit (1 / 2) g =
      (∫ g, ψ g * sLocalTrace_realTermDensity g) -
        ∫ g, ψ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [← integral_sub hP hq]
    refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    change ψ g * realPWSharpTraceLimit (1 / 2) g =
      ψ g * sLocalTrace_realTermDensity g - ψ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    by_cases hg : g ∈ Icc (2 : ℝ) 3
    · rw [realPWSharpTraceLimit_of_half_le le_rfl (by norm_num) (by linarith [hg.1]), mul_sub]
      rfl
    · rw [hψ0 g hg, zero_mul, zero_mul, zero_mul, sub_zero]
  rw [hlim, he₁, he₂] at heq
  have h2 : ((c₁ + c₂ : ℝ) : ℂ) = 0 := by
    push_cast
    linear_combination -heq
  have h3 : c₁ + c₂ = 0 := Complex.ofReal_eq_zero.mp h2
  linarith

end RiemannMasullo
