module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCentralHeatChart
public import RiemannMasullo.ForMathlib.Probability.Distributions.Gaussian.HeatDisplacement
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCentralHeatLocal
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCentralHeatGlobal

/-!
# The change in the ambient order-zero heat trace

On a reciprocal window the direct phase has a logarithmic singularity at norm
one. The real profile at the shifted singularity supplies the second log
derivative in the limit of the two-sided Gaussian sandwich.
-/

@[expose] public noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Real
open scoped CompactlySupported ContDiff NNReal Topology

namespace RiemannMasullo.ThroughOneStability

open FlatPolar

/-- The real part of the shifted ambient Hilbert trace before integration in the
logarithmic heat parameter. The finite trace is real for a real radial profile. -/
def shiftedAmbientScalar (B L : ℝ) (φ : C_c(ℝ≥0ˣ,ℂ)) (z : ℝ) : ℝ :=
  (hilbertTrace (nuclearAfterLogDilation z (compactCosineTraceOperator 0 B 0 L φ))).re

theorem continuous_shiftedAmbientScalar (B L : ℝ) (φ : C_c(ℝ≥0ˣ,ℂ)) :
    Continuous (shiftedAmbientScalar B L φ) :=
  Complex.continuous_re.comp (continuous_hilbertTrace_nuclearAfterLogDilation _)

theorem shiftedAmbientScalar_eq_haarPhase (φ : C_c(ℝ≥0ˣ,ℂ)) (w : ℝ → ℝ)
    {a b B L : ℝ} (ha : 0 < a) (hab : a ≤ b) (hB : 0 < B) (hL : 0 ≤ L)
    (hφ : ∀ u : ℝ≥0ˣ, φ u = (w (u.val : ℝ) : ℂ)) (hs : ∀ g, g ∉ Icc a b → w g = 0)
    (z : ℝ) : shiftedAmbientScalar B L φ z = shiftedHaarPhase w a b ((B*L)*min 1 (exp z)) (exp z) := by
  rw [shiftedAmbientScalar,hilbertTrace_nuclearAfterLogDilation_compactCosineTraceOperator,
    shiftedAmbientTrace_eq_haarIntegral φ w ha hab hB hL hφ hs,Complex.ofReal_re,shiftedHaarPhase]
  apply intervalIntegral.integral_congr
  intro g hg
  dsimp only
  have harg : exp (-z)/g = (g*exp z)⁻¹ := by rw [exp_neg, mul_inv_rev, div_eq_mul_inv]
  have hrefl : exp (-z)/g-1+2 = (g*exp z)⁻¹+1 := by rw [harg]; ring
  rw [hrefl, harg, sqrt_inv, div_eq_mul_inv (w g/g) (sqrt (g*exp z))]

/-- The complex Hilbert trace of the actual ambient heat sandwich is the
complexification of the scalar Gaussian integral for a real compact profile. -/
theorem ambientHeat_eq_ofReal_scalar_integral (φ : C_c(ℝ≥0ˣ,ℂ)) (w : ℝ → ℝ)
    {a b B L : ℝ} (ha : 0 < a) (hab : a ≤ b) (hB : 0 < B) (hL : 0 ≤ L)
    (hφ : ∀ u : ℝ≥0ˣ, φ u = (w (u.val : ℝ) : ℂ)) (hs : ∀ g, g ∉ Icc a b → w g = 0)
    (τ : ℝ≥0) :
    hilbertTrace (logHeatSandwich τ (compactCosineTraceOperator 0 B 0 L φ)) =
      ((∫ z, shiftedAmbientScalar B L φ z ∂gaussianReal 0 (τ+τ) : ℝ) : ℂ) := by
  rw [hilbertTrace_logHeatSandwich_eq_integral_dilationTrace]
  refine Eq.trans ?_ (show (∫ z, (shiftedAmbientScalar B L φ z : ℂ) ∂gaussianReal 0 (τ+τ)) =
    ((∫ z, shiftedAmbientScalar B L φ z ∂gaussianReal 0 (τ+τ) : ℝ) : ℂ) from integral_ofReal)
  apply integral_congr_ae
  exact .of_forall fun z ↦ by
    simp only [shiftedAmbientScalar, hilbertTrace_nuclearAfterLogDilation_compactCosineTraceOperator,
      shiftedAmbientTrace_eq_phaseIntegral φ w ha hab hB hL hφ hs, Complex.ofReal_re]

/-- On the reciprocal window the scalar from the original Hilbert trace has both
moving endpoints of the reciprocal-phase integral. -/
theorem shiftedAmbientScalar_eq_moving (φ : C_c(ℝ≥0ˣ,ℂ)) {w : ℝ → ℝ}
    {δ B L : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hB : 0 < B) (hL : 0 ≤ L)
    (hφ : ∀ u : ℝ≥0ˣ, φ u = (w (u.val : ℝ) : ℂ))
    (hs : ∀ g : ℝ, g ∉ Icc (1+δ)⁻¹ (1-δ)⁻¹ → w g = 0) (z : ℝ) :
    shiftedAmbientScalar B L φ z = movingPhaseTrace δ w (B*L) z := by
  have hp : 0 < 1+δ := by linarith
  have hm : 0 < 1-δ := by linarith
  have hab : (1+δ)⁻¹ ≤ (1-δ)⁻¹ := (inv_le_inv₀ hp hm).mpr (by linarith)
  rw [shiftedAmbientScalar, hilbertTrace_nuclearAfterLogDilation_compactCosineTraceOperator,
    shiftedAmbientTrace_eq_phaseIntegral φ w (inv_pos.mpr hp) hab hB hL hφ hs,
    Complex.ofReal_re]
  simp only [movingPhaseTrace,div_inv_eq_mul]

/-- For a smooth real profile the genuine ambient heat trace minus its cold value
converges to the log curvature times the limiting scale product. -/
theorem tendsto_ambientHeat_central_displacement
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {w : ℝ → ℝ} (hw : ContDiff ℝ (∞) w)
    (hs : ∀ g : ℝ, g ∉ Icc (1+δ)⁻¹ (1-δ)⁻¹ → w g = 0)
    (φ : C_c(ℝ≥0ˣ,ℂ)) (hφ : ∀ u : ℝ≥0ˣ, φ u = (w (u.val : ℝ) : ℂ))
    {ι : Type*} {l : Filter ι} {B L : ι → ℝ} {τ : ι → ℝ≥0} {κ : ℝ}
    (hB : ∀ i, 0 < B i) (hL : ∀ i, 0 ≤ L i)
    (hBL : Tendsto (fun i ↦ B i * L i) l atTop) (hτ : Tendsto τ l (𝓝 0))
    (hκ : Tendsto (fun i ↦ (τ i : ℝ)*log (B i*L i)) l (𝓝 κ)) :
    Tendsto (fun i ↦ hilbertTrace (logHeatSandwich (τ i) (compactCosineTraceOperator 0 (B i) 0 (L i) φ)) -
      hilbertTrace (logHeatSandwich 0 (compactCosineTraceOperator 0 (B i) 0 (L i) φ))) l
      (𝓝 ((κ*(deriv w 1 + deriv (deriv w) 1) : ℝ) : ℂ)) := by
  let R (i : ι) := B i*L i
  let F (i : ι) := shiftedAmbientScalar (B i) (L i) φ
  let W (t : ℝ) := w (exp t)
  have hp : 0 < 1+δ := by linarith
  have hm : 0 < 1-δ := by linarith
  have ha := inv_pos.mpr hp
  have hab : (1+δ)⁻¹ ≤ (1-δ)⁻¹ := (inv_le_inv₀ hp hm).mpr (by linarith)
  have hw₂ : ContDiff ℝ 2 w := hw.of_le (by simp)
  obtain ⟨hW,hKW,hjet⟩ := radialProfile_log_data w hw₂ ha hs
  have hR : ∀ᶠ i in l, 1 ≤ R i := hBL.eventually_ge_atTop 1
  obtain ⟨K,hK,d,hd,hlocal⟩ := exists_movingPhaseTrace_sub_log_le hδ0 hδ1 hw₂ hs
  obtain ⟨M,hM,hglobal⟩ := exists_shiftedHaarPhase_global_bound ha hab hw.continuous.continuousOn
  have hx := tendsto_gaussian_heat_trace_displacement W hW hKW τ R (fun i ↦ F i 0) F
    hτ hκ hR hd hK hM
    (.of_forall fun i ↦ (continuous_shiftedAmbientScalar _ _ _).aestronglyMeasurable)
    (by
      filter_upwards [hR] with i hi
      intro z hz
      have he (z : ℝ) : F i z = movingPhaseTrace δ w (R i) z :=
        shiftedAmbientScalar_eq_moving φ hδ0 hδ1 (hB i) (hL i) hφ hs z
      simpa only [he,W,exp_zero] using hlocal (R i) hi z hz.le)
    (by
      filter_upwards [hR] with i hi
      intro z
      have he := shiftedAmbientScalar_eq_haarPhase φ w ha hab (hB i) (hL i) hφ hs z
      change |shiftedAmbientScalar (B i) (L i) φ z| ≤ M*(1+log (R i))
      rw [he]
      exact hglobal (R i) hi z)
  change iteratedDeriv 2 W 0 = deriv w 1 + iteratedDeriv 2 w 1 at hjet
  rw [hjet, show iteratedDeriv 2 w = deriv (deriv w) by
    rw [iteratedDeriv_succ (n := 1),iteratedDeriv_one]] at hx
  refine ((Complex.continuous_ofReal.tendsto _).comp hx).congr fun i ↦ ?_
  rw [ambientHeat_eq_ofReal_scalar_integral φ w ha hab (hB i) (hL i) hφ hs,
    ambientHeat_eq_ofReal_scalar_integral φ w ha hab (hB i) (hL i) hφ hs 0]
  change (((∫ z, F i z ∂gaussianReal 0 (τ i+τ i)) - F i 0 : ℝ) : ℂ) = _
  simp only [Complex.ofReal_sub, add_zero,gaussianReal_zero_var,integral_dirac,F]

end RiemannMasullo.ThroughOneStability
