module

public import RiemannMasullo.AppC_LCTVS.Sec3a_TriangularTrace
public import RiemannMasullo.ForMathlib.Analysis.Fourier.SharpIntervalSmoothing
public import RiemannMasullo.ForMathlib.Analysis.Fourier.WeightedPaleyWienerBand
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.WithDensity
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import RiemannMasullo.ForMathlib.MeasureTheory.Function.LocalL2Convergence

/-! # Fixed-bandwidth sharp cutoff in the rational real-place model

The sharp-to-smooth comparison below uses the concrete convolved interval masks. The
kernel density is integrated against ordinary Lebesgue measure. Local integrability
allows the rational interval weight to be singular at zero.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace RiemannMasullo.Isolated

/-- The sharp-minus-smoothed diagonal integral tends to zero for a locally
integrable density that decays at both ends of the line. The kernel has mass one
and finite absolute first moment. -/
theorem realPWSharpCutoff_error_tendsto
    (η d : ℝ → ℂ) (hη : Integrable η) (hmass : (∫ t, η t) = 1)
    (hmoment : Integrable (fun t ↦ |t| * ‖η t‖))
    (hd : AEStronglyMeasurable d volume)
    (hlocal : ∀ R ≥ 0, IntegrableOn d (Icc (-R) R))
    (hdecay : ∀ ε > 0, ∃ R ≥ 0, ∀ x ∉ Icc (-R) R, ‖d x‖ ≤ ε) :
    Tendsto (fun L ↦ ∫ x, (sharpIntervalMask L x - smoothIntervalMask η L x) * d x)
      atTop (𝓝 0) := by
  let gap (L x : ℝ) := sharpIntervalMask L x - smoothIntervalMask η L x
  let M := ∫ t, ‖η t‖
  let A := 2 * ∫ t, |t| * ‖η t‖
  have hA : 0 ≤ A := mul_nonneg (by norm_num)
    (integral_nonneg fun t ↦ mul_nonneg (abs_nonneg _) (norm_nonneg _))
  have hgap (L : ℝ) : Integrable (gap L) ∧ (∫ x, ‖gap L x‖) ≤ A :=
    integrable_and_integral_norm_sharpIntervalMask_sub_smoothIntervalMask η hη hmass hmoment L
  have hglob (L x : ℝ) : ‖gap L x‖ ≤ M :=
    norm_sharpIntervalMask_sub_smoothIntervalMask_le η hη hmass L x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (2 * (A + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨R, hR, hRdecay⟩ := hdecay δ hδ
  let S := Icc (-R) R
  have hS : MeasurableSet S := measurableSet_Icc
  have hmain (L : ℝ) : IntegrableOn (fun x ↦ gap L x * d x) S := by
    refine ((hlocal R hR).norm.const_mul M).mono'
      (((hgap L).1.mono_measure Measure.restrict_le_self).aestronglyMeasurable.mul
        (hlocal R hR).aestronglyMeasurable) (ae_of_all _ fun x ↦ ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hglob L x) (norm_nonneg _)
  have htail (L : ℝ) : IntegrableOn (fun x ↦ gap L x * d x) Sᶜ := by
    refine (((hgap L).1.norm.const_mul δ).mono_measure Measure.restrict_le_self).mono'
      (((hgap L).1.aestronglyMeasurable.mul hd).mono_ac Measure.absolutelyContinuous_restrict) ?_
    filter_upwards [ae_restrict_mem hS.compl] with x hx
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hRdecay x hx) (norm_nonneg _)
  have hmain_limit : Tendsto (fun L ↦ ∫ x in S, gap L x * d x) atTop (𝓝 0) := by
    simpa only [integral_zero] using
      (tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict S)
        (F := fun L x ↦ gap L x * d x) (f := fun _ ↦ (0 : ℂ))
        (fun x ↦ M * ‖d x‖)
        (Eventually.of_forall fun L ↦ (hmain L).aestronglyMeasurable)
        (Eventually.of_forall fun L ↦ ae_of_all _ fun x ↦ by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hglob L x) (norm_nonneg _))
        ((hlocal R hR).norm.const_mul M)
        (ae_of_all _ fun x ↦ by
          simpa only [zero_mul] using
            (tendsto_sharpIntervalMask_sub_smoothIntervalMask η hη hmass x).mul_const (d x)))
  have htail_bound (L : ℝ) : ‖∫ x in Sᶜ, gap L x * d x‖ ≤ δ * A := by
    calc
      _ ≤ ∫ x in Sᶜ, δ * ‖gap L x‖ := by
        refine (norm_integral_le_integral_norm _).trans (integral_mono_ae (htail L).norm
          (((hgap L).1.norm.const_mul δ).mono_measure Measure.restrict_le_self) ?_)
        filter_upwards [ae_restrict_mem hS.compl] with x hx
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hRdecay x hx) (norm_nonneg _)
      _ ≤ ∫ x, δ * ‖gap L x‖ := by
        exact setIntegral_le_integral ((hgap L).1.norm.const_mul δ)
          (ae_of_all _ fun x ↦ mul_nonneg hδ.le (norm_nonneg _))
      _ ≤ δ * A := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hgap L).2 hδ.le
  have hsmall : δ * A ≤ ε / 2 := by
    calc
      δ * A ≤ δ * (A + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
      _ = ε / 2 := by dsimp [δ]; field_simp
  filter_upwards [Metric.tendsto_nhds.mp hmain_limit (ε / 2) (by positivity)] with L hL
  have htot : Integrable (fun x ↦ gap L x * d x) := by
    simpa only [union_compl_self, integrableOn_univ] using (hmain L).union (htail L)
  rw [dist_zero_right] at hL ⊢
  change ‖∫ x, gap L x * d x‖ < ε
  rw [← integral_add_compl hS htot]
  exact (norm_add_le _ _).trans_lt (by linarith [htail_bound L, hsmall])

/-- Paper: Theorem 12.4.1.1, pp. 515–517. For a fixed rational real-place band,
the sharp spatial trace tends to the geometric sum of the surviving even
Taylor-jet diagonals.
Reconstruction: The weighted even band and its sharp spatial compression are
the fixed-bandwidth model in #7354. The smoothed operators are represented by
multiplication of a dilation on the even functions of that band.
Deviation: This implication takes diagonal decay, the trace/diagonal
identifications, and the hypotheses on the surviving Taylor jets as inputs.
The comparison of joint cutoff limits with the adelic orbital sum is separate. -/
theorem realPWSharpCutoff_trace_tendsto
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (sharp smooth : ℝ → nuclearEndomorphisms H)
    (η d : ℝ → ℂ) (hη : Integrable η) (hmass : (∫ t, η t) = 1)
    (hmoment : Integrable (fun t ↦ |t| * ‖η t‖))
    (hd : AEStronglyMeasurable d volume)
    (hlocal : ∀ R ≥ 0, IntegrableOn d (Icc (-R) R))
    (hdecay : ∀ ε > 0, ∃ R ≥ 0, ∀ x ∉ Icc (-R) R, ‖d x‖ ≤ ε)
    (htrace : ∀ L, hilbertTrace (sharp L) - hilbertTrace (smooth L) =
      ∫ x, (sharpIntervalMask L x - smoothIntervalMask η L x) * d x)
    (f : H → ℝ → ℂ) (m : ℝ → ℝ → ℂ) (a q : ℝ) (hq : ‖q‖ < 1) (n : ℕ)
    (hf : ∀ v (k : ℕ), ContDiff ℝ k (f v)) (hm : ∀ L (k : ℕ), ContDiff ℝ k (m L))
    (heven : ∀ v x, f v (-x) = f v x)
    (hzero : ∀ v k, k < 2 * n → iteratedDeriv k (f v) 0 = 0)
    (hT : ∀ L v x, f ((smooth L).val v) x = m L x * f v (q * x))
    (ℓ : ℕ → H →L[ℂ] ℂ) (hℓ : LinearIndependent ℂ ℓ)
    (hsep : ∀ v, (∀ i, ℓ i v = 0) → v = 0)
    (hjet : ∀ i v, ℓ i v = iteratedDeriv (2 * (n + i)) (f v) 0)
    (hm0 : ∀ L, m L 0 = (a : ℂ) * smoothIntervalMask η L 0) :
    Tendsto (fun L ↦ hilbertTrace (sharp L)) atTop
      (𝓝 ((a : ℂ) * (q : ℂ) ^ (2 * n) / (1 - (q : ℂ) ^ 2))) := by
  have hsm (L : ℝ) := hilbertTrace_eq_of_even_multiplier_dilation
    (smooth L) f (m L) q hq n hf (hm L) heven hzero (hT L) ℓ hℓ hsep hjet
  have hsmooth : Tendsto (fun L ↦ hilbertTrace (smooth L)) atTop
      (𝓝 ((a : ℂ) * (q : ℂ) ^ (2 * n) / (1 - (q : ℂ) ^ 2))) := by
    simp_rw [hsm, hm0]
    simpa only [hmass, mul_one] using
      ((((tendsto_smoothIntervalMask η hη 0).const_mul (a : ℂ)).mul_const
        ((q : ℂ) ^ (2 * n))).div_const (1 - (q : ℂ) ^ 2))
  have hdiff := realPWSharpCutoff_error_tendsto η d hη hmass hmoment hd hlocal hdecay
  simp_rw [← htrace] at hdiff
  simpa only [sub_add_cancel, zero_add] using hdiff.add hsmooth

/-- Paper: Definition 10.1.1.1, (10.1.1.5), p. 434. The half-twisted real-place
interval weight with strip half-width α and Sobolev order s, in additive coordinates.
Reconstruction: The real-place even model uses Lebesgue measure after removing the
half-twist, as in #7354. The value at zero is immaterial to the measure. -/
def realPWIntervalWeight (α s x : ℝ) : ℝ :=
  let t := Real.log |x|
  max (Real.exp (2 * α * t)) (Real.exp (-(2 * α * t))) *
    Real.exp (s / 2 * Real.log (1 + t ^ 2))

/-- Off zero the density is the maximum power weight times the logarithmic factor. -/
theorem realPWIntervalWeight_eq (α s : ℝ) {x : ℝ} (hx : x ≠ 0) :
    realPWIntervalWeight α s x =
      max (|x| ^ (2 * α)) (|x| ^ (-(2 * α))) * (1 + Real.log |x| ^ 2) ^ (s / 2) := by
  simp only [realPWIntervalWeight, Real.rpow_def_of_pos (abs_pos.mpr hx),
    Real.rpow_def_of_pos (by positivity : 0 < 1 + Real.log |x| ^ 2)]
  rw [mul_comm (Real.log |x|) (2 * α), mul_comm (Real.log |x|) (-(2 * α)),
    mul_comm (Real.log (1 + Real.log |x| ^ 2)) (s / 2), neg_mul]

/-- The real-place density is measurable on the entire additive line. -/
theorem measurable_realPWIntervalWeight (α s : ℝ) :
    Measurable (realPWIntervalWeight α s) := by
  have ht : Measurable (fun x : ℝ ↦ Real.log |x|) :=
    Real.measurable_log.comp continuous_abs.measurable
  have hv : Measurable (fun x : ℝ ↦ 2 * α * Real.log |x|) := ht.const_mul _
  have hu : Measurable (fun x : ℝ ↦ Real.log (1 + (Real.log |x|) ^ 2)) :=
    Real.measurable_log.comp (measurable_const.add (ht.pow_const 2))
  exact ((Real.continuous_exp.measurable.comp hv).max
    (Real.continuous_exp.measurable.comp hv.neg)).mul
    (Real.continuous_exp.measurable.comp (hu.const_mul _))

private theorem one_le_realPWIntervalWeight (α s : ℝ) (hs : 0 ≤ s) (x : ℝ) :
    1 ≤ realPWIntervalWeight α s x := by
  let t := Real.log |x|
  let u := 2 * α * t
  have hu : 1 ≤ max (Real.exp u) (Real.exp (-u)) := by
    rcases le_total (0 : ℝ) u with h | h
    · exact (Real.one_le_exp h).trans (le_max_left _ _)
    · exact (Real.one_le_exp (neg_nonneg.mpr h)).trans (le_max_right _ _)
  have ht : 1 ≤ Real.exp (s / 2 * Real.log (1 + t ^ 2)) :=
    Real.one_le_exp (mul_nonneg (by positivity) (Real.log_nonneg (by nlinarith)))
  exact one_le_mul_of_one_le_of_one_le hu ht

/-- The real-place weighted measure of the reconstructed fixed-bandwidth model. -/
def realPWIntervalMeasure (α s : ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (realPWIntervalWeight α s x))

/-- The weighted measure dominates Lebesgue measure, so every weighted vector has
an ordinary square-integrable representative. -/
theorem volume_le_realPWIntervalMeasure (α s : ℝ) (hs : 0 ≤ s) :
    volume ≤ realPWIntervalMeasure α s := by
  rw [← withDensity_one (μ := (volume : Measure ℝ))]
  exact withDensity_mono (ae_of_all _ fun x ↦ by
    simpa only [Pi.one_apply, ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (one_le_realPWIntervalWeight α s hs x))

/-- The weighted and ordinary measures have the same null sets; this is the
direction needed to identify the weighted evaluation representative. -/
theorem realPWIntervalMeasure_absolutelyContinuous (α s : ℝ) :
    realPWIntervalMeasure α s ≪ volume :=
  withDensity_absolutelyContinuous _ _

/-- The single diagonal of the real-place cutoff dilation, including the density so
that it is integrated against Lebesgue measure. -/
def realPWSharpDensity (Y α s : ℝ) (hs : 0 ≤ s) (g x : ℝ) : ℂ :=
  let hμ := volume_le_realPWIntervalMeasure α s hs
  ((realPWIntervalWeight α s x * g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    RealPWBand.evaluation Y hμ (g⁻¹ * x) (RealPWBand.evaluationVector Y hμ x)

/-- The real-place diagonal is measurable, including at the origin. -/
theorem aestronglyMeasurable_realPWSharpDensity (Y α s : ℝ) (hs : 0 ≤ s) (g : ℝ) :
    AEStronglyMeasurable (realPWSharpDensity Y α s hs g) volume := by
  let hμ := volume_le_realPWIntervalMeasure α s hs
  have he : Continuous (fun x ↦ RealPWBand.evaluation Y hμ (g⁻¹ * x)
      (RealPWBand.evaluationVector Y hμ x)) :=
    ((RealPWBand.continuous_evaluation Y hμ).comp (continuous_const.mul continuous_id)).clm_apply
      (RealPWBand.continuous_evaluationVector Y hμ)
  exact (Complex.continuous_ofReal.measurable.comp
    ((measurable_realPWIntervalWeight α s).mul_const _)).aestronglyMeasurable.mul
    he.aestronglyMeasurable

/-- The physical representative of the evaluation vector normalized to norm
one when that vector is nonzero. -/
def realPWNormalizedEval (Y α s : ℝ) (hs : 0 ≤ s) (x t : ℝ) : ℂ :=
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let e := RealPWBand.evaluationVector Y hμ x
  RealPWBand.evaluation Y hμ t (((‖e‖⁻¹ : ℝ) : ℂ) • e)

private theorem realPWNormalizedEval_sq (Y α s : ℝ) (hs : 0 ≤ s) (x : ℝ) :
    Integrable (fun t ↦ realPWIntervalWeight α s t * ‖realPWNormalizedEval Y α s hs x t‖ ^ 2) ∧
      (∫ t, realPWIntervalWeight α s t * ‖realPWNormalizedEval Y α s hs x t‖ ^ 2) ≤ 1 := by
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let e := RealPWBand.evaluationVector Y hμ x
  let z := ((‖e‖⁻¹ : ℝ) : ℂ) • e
  let μ := realPWIntervalMeasure α s
  have hzNorm : ‖z‖ ≤ 1 := by
    dsimp only [z]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg e))]
    exact inv_mul_le_one
  have hEval := RealPWBand.evaluation_ae Y hμ
    (realPWIntervalMeasure_absolutelyContinuous α s) z
  have hSq : (fun t ↦ ‖realPWNormalizedEval Y α s hs x t‖ ^ 2) =ᵐ[μ]
      (fun t ↦ ‖z.val t‖ ^ 2) :=
    hEval.mono fun _ h ↦ congrArg (fun v : ℂ ↦ ‖v‖ ^ 2) h
  have hInt : Integrable (fun t ↦ ‖realPWNormalizedEval Y α s hs x t‖ ^ 2) μ :=
    ((Lp.memLp z.val).integrable_norm_pow (by norm_num)).congr hSq.symm
  let ρ (t : ℝ) := ENNReal.ofReal (realPWIntervalWeight α s t)
  have hρ : Measurable ρ := ENNReal.measurable_ofReal.comp (measurable_realPWIntervalWeight α s)
  have hρf : ∀ᵐ t ∂volume, ρ t < ∞ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hρw (t : ℝ) : (ρ t).toReal = realPWIntervalWeight α s t :=
    ENNReal.toReal_ofReal ((zero_le_one : (0 : ℝ) ≤ 1).trans
      (one_le_realPWIntervalWeight α s hs t))
  refine ⟨?_, ?_⟩
  · simpa only [hρw, smul_eq_mul] using
      (integrable_withDensity_iff_integrable_smul' hρ hρf).mp hInt
  · have hh := integral_withDensity_eq_integral_toReal_smul hρ hρf
      (fun t ↦ ‖realPWNormalizedEval Y α s hs x t‖ ^ 2)
    simp only [hρw, smul_eq_mul] at hh
    rw [← hh]
    change (∫ t, ‖realPWNormalizedEval Y α s hs x t‖ ^ 2 ∂μ) ≤ 1
    rw [integral_congr_ae hSq, L2.integral_sq_norm (𝕜 := ℂ)]
    exact pow_le_pow_left₀ (norm_nonneg z) hzNorm 2 |>.trans_eq (one_pow _)

/-- Concentration of the normalized real-place evaluation vectors, together
with the weighted reproducing estimates, gives decay of the sharp-cutoff
diagonal at both ends of the line. -/
theorem realPWSharpDensity_decay_of_concentration
    (Y α s : ℝ) (hs : 0 ≤ s) (g : ℝ) (hg : 1 < g)
    (φ : ℝ → ℂ) (G : ℝ → ℝ) (hφ : AEStronglyMeasurable φ volume)
    (hG : MemLp G 2 volume)
    (hconcentration : ∀ ε > 0, ∃ R : ℝ, ∀ᶠ x in atTop,
      (∫ t in (Metric.closedBall x R ∪ Metric.closedBall (-x) R)ᶜ,
        realPWIntervalWeight α s t * ‖realPWNormalizedEval Y α s hs x t‖ ^ 2) < ε)
    (hreproduce : ∀ x, realPWNormalizedEval Y α s hs x (g⁻¹ * x) =
      ∫ t, realPWNormalizedEval Y α s hs x (g⁻¹ * x + t) * φ t)
    (henvelope : ∀ᶠ x in atTop, ∀ᵐ t ∂volume,
      Real.sqrt (realPWIntervalWeight α s (g⁻¹ * x)) /
        Real.sqrt (realPWIntervalWeight α s (g⁻¹ * x + t)) * ‖φ t‖ ≤ G t)
    (hnorm : ∃ A ≥ 0, ∀ᶠ x in atTop,
      |Real.sqrt (realPWIntervalWeight α s x) *
        (g ^ (-(1 / 2 : ℝ)) *
          ‖RealPWBand.evaluationVector Y (volume_le_realPWIntervalMeasure α s hs) x‖)| ≤ A)
    (hratio : ∃ B ≥ 0, ∀ᶠ x in atTop,
      Real.sqrt (realPWIntervalWeight α s x) /
        Real.sqrt (realPWIntervalWeight α s (g⁻¹ * x)) ≤ B) :
    ∀ ε > 0, ∃ R ≥ 0, ∀ x ∉ Icc (-R) R, ‖realPWSharpDensity Y α s hs g x‖ ≤ ε := by
  let w := realPWIntervalWeight α s
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let e := RealPWBand.evaluationVector Y hμ
  let a := g ^ (-(1 / 2 : ℝ))
  have hw (t : ℝ) : 0 < w t := zero_lt_one.trans_le (one_le_realPWIntervalWeight α s hs t)
  have hgpos : 0 < g := lt_trans zero_lt_one hg
  refine weighted_dilation_density_decay_of_twoWindows (q := g⁻¹) (w := w)
    (f := realPWNormalizedEval Y α s hs) (eNorm := fun x ↦ a * ‖e x‖)
    (C := 1) (d := realPWSharpDensity Y α s hs g)
    (inv_pos.mpr hgpos) ?_ hw (measurable_realPWIntervalWeight α s)
    ?_ (fun x ↦ (realPWNormalizedEval_sq Y α s hs x).2)
    hconcentration hφ hreproduce hG henvelope hnorm hratio ?_ ?_
  · rw [inv_eq_one_div]; exact (div_lt_one hgpos).mpr hg
  · intro x
    let f := realPWNormalizedEval Y α s hs x
    have hf : Continuous f :=
      (RealPWBand.contDiff_evaluation Y hμ _ 0).continuous
    apply (memLp_two_iff_integrable_sq_norm
      (((Complex.continuous_ofReal.measurable.comp
        (Real.continuous_sqrt.measurable.comp (measurable_realPWIntervalWeight α s))).mul
          hf.measurable).aestronglyMeasurable)).mpr
    convert (realPWNormalizedEval_sq Y α s hs x).1 using 1
    ext t
    change ‖(Real.sqrt (w t) : ℂ) * f t‖ ^ 2 = w t * ‖f t‖ ^ 2
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw t).le]
  · intro x
    have hwEven : w (-x) = w x := by simp only [w, realPWIntervalWeight, abs_neg]
    change ((w (-x) * a : ℝ) : ℂ) * RealPWBand.evaluation Y hμ (g⁻¹ * -x) (e (-x)) =
      ((w x * a : ℝ) : ℂ) * RealPWBand.evaluation Y hμ (g⁻¹ * x) (e x)
    rw [hwEven, mul_neg, show e (-x) = e x from RealPWBand.evaluationVector_even Y hμ x,
      RealPWBand.evaluation_even]
  · refine Eventually.of_forall fun x ↦ ?_
    by_cases hx : ‖e x‖ = 0
    · have hz : e x = 0 := norm_eq_zero.mp hx
      show (↑(w x * a) : ℂ) * RealPWBand.evaluation Y hμ (g⁻¹ * x) (e x) = _
      simp only [hz, map_zero, mul_zero, realPWNormalizedEval]
      change 0 = _ * ((↑(Real.sqrt (w (g⁻¹ * x))) : ℂ) *
        RealPWBand.evaluation Y hμ (g⁻¹ * x) (((‖e x‖⁻¹ : ℝ) : ℂ) • e x))
      simp [hz]
    · have hsy := (Real.sqrt_pos.mpr (hw (g⁻¹ * x))).ne'
      have hk : (Real.sqrt (w x) * (a * ‖e x‖)) *
          (Real.sqrt (w x) / Real.sqrt (w (g⁻¹ * x))) *
          Real.sqrt (w (g⁻¹ * x)) * ‖e x‖⁻¹ = w x * a := by
        calc
          _ = (Real.sqrt (w x) * Real.sqrt (w x)) * a *
              (‖e x‖ * ‖e x‖⁻¹) *
              ((Real.sqrt (w (g⁻¹ * x)))⁻¹ * Real.sqrt (w (g⁻¹ * x))) := by
            rw [div_eq_mul_inv]; ring
          _ = _ := by
            rw [mul_inv_cancel₀ hx, inv_mul_cancel₀ hsy, Real.mul_self_sqrt (hw x).le,
              mul_one, mul_one]
      have hkc := congrArg Complex.ofReal hk
      change ((↑(w x * a) : ℂ) * RealPWBand.evaluation Y hμ (g⁻¹ * x) (e x)) =
        _ * ((↑(Real.sqrt (w (g⁻¹ * x))) : ℂ) *
          RealPWBand.evaluation Y hμ (g⁻¹ * x) (((‖e x‖⁻¹ : ℝ) : ℂ) • e x))
      rw [map_smul, smul_eq_mul]
      push_cast [Complex.ofReal_mul] at hkc ⊢
      linear_combination -hkc * RealPWBand.evaluation Y hμ (g⁻¹ * x) (e x)

/-- Paper: Theorem 12.4.1.1, pp. 515–517. The rational real-place sharp cutoff has
the fixed-bandwidth limit once the even Taylor jets and the cutoff compressions
are identified and the weighted off-diagonal estimate is supplied.
Reconstruction: The underlying Hilbert space is the even Paley–Wiener band in
the interval weight of #7354, with the cutoffs centered at the origin.
Deviation: The trace comparison holds at one fixed bandwidth and one dilation.
The manuscript's adelic joint cutoff comparison is a separate input. -/
theorem realPWIntervalBand_sharpTrace_tendsto
    (Y α s : ℝ) (hs : 0 ≤ s) (g : ℝ) (hg : 1 < g) (n : ℕ)
    (η : ℝ → ℂ) (hη : Integrable η) (hmass : (∫ t, η t) = 1)
    (hmoment : Integrable (fun t ↦ |t| * ‖η t‖))
    (hm : ∀ L (k : ℕ), ContDiff ℝ k (smoothIntervalMask η L))
    (hlocal : ∀ R ≥ 0, IntegrableOn (realPWSharpDensity Y α s hs g) (Icc (-R) R))
    (hdecay : ∀ ε > 0, ∃ R ≥ 0, ∀ x ∉ Icc (-R) R,
      ‖realPWSharpDensity Y α s hs g x‖ ≤ ε)
    (sharp smooth : ℝ → nuclearEndomorphisms
      (RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)))
    (htrace : ∀ L, hilbertTrace (sharp L) - hilbertTrace (smooth L) =
      ∫ x, (sharpIntervalMask L x - smoothIntervalMask η L x) *
        realPWSharpDensity Y α s hs g x)
    (hT : ∀ L f x,
      RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x ((smooth L).val f) =
        ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * smoothIntervalMask η L x *
          RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) (g⁻¹ * x) f)
    (hzero : ∀ f k, k < 2 * n → iteratedDeriv k
      (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f) 0 = 0)
    (ℓ : ℕ → RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs) →L[ℂ] ℂ)
    (hℓ : LinearIndependent ℂ ℓ) (hsep : ∀ f, (∀ i, ℓ i f = 0) → f = 0)
    (hjet : ∀ i f, ℓ i f = iteratedDeriv (2 * (n + i))
      (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f) 0) :
    Tendsto (fun L ↦ hilbertTrace (sharp L)) atTop
      (𝓝 (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((g⁻¹ : ℝ) : ℂ) ^ (2 * n) /
        (1 - ((g⁻¹ : ℝ) : ℂ) ^ 2))) := by
  let hμ := volume_le_realPWIntervalMeasure α s hs
  have hgpos : 0 < g := lt_trans zero_lt_one hg
  have hq : ‖g⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hgpos.le), inv_eq_one_div]
    exact (div_lt_one hgpos).mpr hg
  exact realPWSharpCutoff_trace_tendsto sharp smooth η (realPWSharpDensity Y α s hs g)
    hη hmass hmoment (aestronglyMeasurable_realPWSharpDensity Y α s hs g)
    hlocal hdecay htrace (fun f x ↦ RealPWBand.evaluation Y hμ x f)
    (fun L x ↦ ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * smoothIntervalMask η L x) _ _ hq n
    (fun f k ↦ RealPWBand.contDiff_evaluation Y hμ f k)
    (fun L k ↦ contDiff_const.mul (hm L k))
    (RealPWBand.evaluation_even Y hμ) hzero hT ℓ hℓ hsep hjet (fun _ ↦ rfl)

end RiemannMasullo.Isolated
