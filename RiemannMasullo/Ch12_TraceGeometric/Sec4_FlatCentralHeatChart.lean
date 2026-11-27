module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCentralHeatBounds
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelDiagonal
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatHeatCosineTrace
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The finite shifted heat trace in reciprocal coordinates

The two phases of the cosine band kernel give the direct and reflected intervals.
The change of variable in positive Haar measure records the endpoints and overlap
band for every shift. The cold kernel calculation comes from #7602.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Real
open scoped CompactlySupported NNReal Topology

namespace RiemannMasullo.ThroughOneStability

open FlatPolar

private theorem double_cosine_row {B : ℝ} (hB : 0 ≤ B) (d x : ℝ) :
    4 * (∫ s in Ioc (0 : ℝ) B, cos (2 * π * (x * s)) * cos (2 * π * (x * s / d))) =
      realPWBandDiagonal B d x := by
  have hk (y : ℝ) : realBandKernel B y = 2 * ∫ s in (0 : ℝ)..B, cos (2 * π * y * s) := by
    rw [← integral_cos_eq_realBandKernel]
    have hi : Continuous (fun s : ℝ ↦ cos (2 * π * y * s)) := by fun_prop
    have hr := intervalIntegral.integral_comp_neg (a := 0) (b := B) (fun s : ℝ ↦ cos (2 * π * y * s))
    simp only [mul_neg, cos_neg, neg_zero] at hr
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (-B) 0)
      (hi.intervalIntegrable 0 B), ← hr]
    ring
  rw [← intervalIntegral.integral_of_le hB, realPWBandDiagonal, hk, hk, ← mul_add]
  have hi (y : ℝ) : IntervalIntegrable (fun s : ℝ ↦ cos (2 * π * y * s)) volume 0 B :=
    (by fun_prop : Continuous (fun s : ℝ ↦ cos (2 * π * y * s))).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add (hi _) (hi _), ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [show 2 * π * (x / d - x) * s = 2 * π * (x * s / d) - 2 * π * (x * s) by ring,
    show 2 * π * (x / d + x) * s = 2 * π * (x * s / d) + 2 * π * (x * s) by ring,
    ← Real.two_mul_cos_mul_cos]
  ring

/-- The genuine ambient atom equals the integral of the even band diagonal,
including the identity dilation. -/
theorem finiteCosineTrace_eq_bandDiagonal {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L) (d : ℝ) :
    hilbertTrace (finiteCosineTraceOperator 0 B 0 L d) =
      (((sqrt d)⁻¹ * (∫ x in (0 : ℝ)..L, realPWBandDiagonal B d x) : ℝ) : ℂ) := by
  rw [hilbertTrace_finiteCosine_frequencyBand 0 L B d le_rfl]
  apply congrArg Complex.ofReal
  rw [show 4 / sqrt d = (sqrt d)⁻¹ * 4 by ring, mul_assoc, ← integral_const_mul,
    ← intervalIntegral.integral_of_le hL]
  congr 1
  exact intervalIntegral.integral_congr fun x _ ↦ double_cosine_row hB d x

/-- Away from the single exceptional dilation the genuine ambient trace has
the direct and reflected sine-integral phases. -/
theorem finiteCosineTrace_eq_phaseKernels {B L d : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hd : 0 < d) (hne : d ≠ 1) :
    hilbertTrace (finiteCosineTraceOperator 0 B 0 L d) =
      (((sqrt d)⁻¹ * (phaseKernel (B * L) (d⁻¹ - 1) + phaseKernel (B * L) (d⁻¹ - 1 + 2)) : ℝ) : ℂ) := by
  rw [finiteCosineTrace_eq_bandDiagonal hB hL, integral_realPWBandDiagonal hd hne]
  simp only [realPWBandDiagonalMass, phaseKernel, one_div, show d⁻¹ - 1 + 2 = d⁻¹ + 1 by ring]

/-- Haar measure on the positive multiplicative group is `dg / g` in the real
radius, with no measurability condition needed for the Bochner integral. -/
theorem positiveRealHaar_integral_radius (F : ℝ → ℂ) :
    (∫ u : ℝ≥0ˣ, F (u.val : ℝ) ∂positiveRealHaar) =
      ∫ g in Ioi (0 : ℝ), g⁻¹ • F g := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have he : positiveRealHaar = (volume : Measure ℝ).map E := by
    unfold positiveRealHaar
    apply congrArg (fun f : ℝ → ℝ≥0ˣ ↦ volume.map f)
    funext t
    exact Units.ext (NNReal.eq (Real.coe_toNNReal _ (exp_pos t).le))
  rw [he, E.isClosedEmbedding.integral_map]
  change (∫ t : ℝ, F (exp t)) = _
  rw [← integral_comp_log_Ioi_zero (fun t ↦ F (exp t))]
  exact setIntegral_congr_fun measurableSet_Ioi fun g hg ↦ by rw [exp_log hg]

/-- Passing from the positive group integral of a window-supported test to its
ordinary Haar-weighted interval integral. -/
theorem positiveRealHaar_window (w : ℝ → ℝ) (F : ℝ → ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hs : ∀ g, g ∉ Icc a b → w g = 0) :
    (∫ u : ℝ≥0ˣ, (w (u.val : ℝ) : ℂ) * F (u.val : ℝ) ∂positiveRealHaar) =
      ∫ g in a..b, ((w g / g : ℝ) : ℂ) * F g := by
  rw [positiveRealHaar_integral_radius (fun g ↦ (w g : ℂ) * F g)]
  trans ∫ g in Ioi (0 : ℝ), (Ioc a b).indicator (fun t ↦ ((w t / t : ℝ) : ℂ) * F t) g
  · apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae ((volume : Measure ℝ).ae_ne a)] with g hga
    by_cases hg : g ∈ Ioc a b
    · rw [indicator_of_mem hg, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_inv]
      ring
    · rw [indicator_of_notMem hg, hs _ (fun h ↦ hg ⟨lt_of_le_of_ne h.1 hga.symm, h.2⟩)]
      simp
  · have hsub : Ioc a b ⊆ Ioi 0 := fun _ hg ↦ ha.trans hg.1
    rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict_of_subset hsub,
      intervalIntegral.integral_of_le hab]

/-- The reciprocal phase change, including its interval reversal and the
positive radial half-density. Both endpoints may lie on either side of zero. -/
theorem reciprocalPhaseIntegral {a b k : ℝ} (ha : 0 < a) (hab : a ≤ b) (hk : 0 < k)
    (w K : ℝ → ℝ) :
    (∫ g in a..b, (w g / g / sqrt (g / k)) * K (k / g - 1)) =
      ∫ c in (k / b - 1)..(k / a - 1), (w (k / (1 + c)) / sqrt (1 + c)) * K c := by
  let f (g : ℝ) := k / g - 1
  let f' (g : ℝ) := -(k / g ^ 2)
  let G (c : ℝ) := (w (k / (1 + c)) / sqrt (1 + c)) * K c
  have hp (g : ℝ) (hg : g ∈ Icc a b) : 0 < g := ha.trans_le hg.1
  have hf : ContinuousOn f (Icc a b) :=
    (continuousOn_const.div continuousOn_id (fun g hg ↦ (hp g hg).ne')).sub continuousOn_const
  have hd (g : ℝ) (hg : g ∈ Ioo a b) : HasDerivAt f (f' g) g := by
    have h := ((hasDerivAt_const g k).div (hasDerivAt_id g) (ha.trans hg.1).ne').sub_const 1
    convert h using 1 <;> simp [f, f', id_eq]
    ring
  have h := integral_Icc_deriv_smul_of_deriv_nonpos (g := G) hf hd
    (fun g _ ↦ neg_nonpos.mpr (div_nonneg hk.le (sq_nonneg g))) hab
  have hba : f b ≤ f a := sub_le_sub_right (div_le_div_of_nonneg_left hk.le ha hab) 1
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  change _ = ∫ c in (f b)..(f a), G c
  rw [intervalIntegral.integral_of_le hba, ← integral_Icc_eq_integral_Ioc, ← neg_inj, ← h, ← integral_neg]
  apply setIntegral_congr_fun measurableSet_Icc
  intro g hg
  have hgp := hp g hg
  have hv : 0 < k / g := div_pos hk hgp
  have hroot : (k / g) / sqrt (k / g) = sqrt (k / g) :=
    (div_eq_iff (sqrt_pos.mpr hv).ne').mpr (mul_self_sqrt hv.le).symm
  have hh : (k / g ^ 2) / sqrt (k / g) = (1 / g) / sqrt (g / k) := by
    rw [show g / k = (k / g)⁻¹ by rw [inv_div], sqrt_inv]
    calc
      _ = (k / g / sqrt (k / g)) / g := by ring
      _ = _ := by rw [hroot]; simp only [div_eq_mul_inv, inv_inv]; ring
  have hk' : k / (k / g) = g := by field_simp
  dsimp only [f, f', G, smul_eq_mul]
  rw [show 1 + (k / g - 1) = k / g by ring, hk']
  linear_combination (w g * K (k / g - 1)) * hh

/-- The compact operator on the overlap band, written as an ordinary Haar
interval average of its genuine individual nuclear traces. -/
theorem shiftedAmbientTrace_eq_haarAtomTrace (φ : C_c(ℝ≥0ˣ, ℂ)) (w : ℝ → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hφ : ∀ u : ℝ≥0ˣ, φ u = (w (u.val : ℝ) : ℂ)) (hs : ∀ g, g ∉ Icc a b → w g = 0)
    (B L z : ℝ) :
    hilbertTrace (compactCosineTraceOperator 0 (min B (exp z * B)) 0 L
      (compactRadialTranslate φ (expRadialUnit z))) =
      ∫ g in a..b, ((w g / g : ℝ) : ℂ) *
        hilbertTrace (finiteCosineTraceOperator 0 (min B (exp z * B)) 0 L (g * exp z)) := by
  rw [hilbertTrace_compactCosineTraceOperator_shift]
  refine Eq.trans ?_ (positiveRealHaar_window w (fun g ↦
    hilbertTrace (finiteCosineTraceOperator 0 (min B (exp z * B)) 0 L (g * exp z))) ha hab hs)
  exact integral_congr_ae (.of_forall fun u ↦ by dsimp only; rw [hφ]; rfl)

/-- The finite shifted ambient trace is a Haar-weighted radial average of the
direct and reflected phase kernels. The exceptional atom at radius `exp (-z)`
has zero Lebesgue mass. -/
theorem shiftedAmbientTrace_eq_haarIntegral (φ : C_c(ℝ≥0ˣ, ℂ)) (w : ℝ → ℝ)
    {a b B L : ℝ} (ha : 0 < a) (hab : a ≤ b) (hB : 0 < B) (hL : 0 ≤ L)
    (hφ : ∀ u : ℝ≥0ˣ, φ u = (w (u.val : ℝ) : ℂ)) (hs : ∀ g, g ∉ Icc a b → w g = 0)
    (z : ℝ) :
    hilbertTrace (compactCosineTraceOperator 0 (min B (exp z * B)) 0 L
      (compactRadialTranslate φ (expRadialUnit z))) =
      ((∫ g in a..b, (w g / g / sqrt (g * exp z)) *
        (phaseKernel ((B * L) * min 1 (exp z)) (exp (-z) / g - 1) +
          phaseKernel ((B * L) * min 1 (exp z)) (exp (-z) / g - 1 + 2)) : ℝ) : ℂ) := by
  rw [shiftedAmbientTrace_eq_haarAtomTrace φ w ha hab hφ hs B L z, ← intervalIntegral.integral_ofReal]
  have hcut : 0 ≤ min B (exp z * B) := le_min hB.le (mul_nonneg (exp_pos z).le hB.le)
  have hscale : min B (exp z * B) * L = (B * L) * min 1 (exp z) := by
    rcases le_total (exp z) 1 with h | h
    · rw [min_eq_right h, min_eq_right (show exp z * B ≤ B by simpa only [one_mul] using mul_le_mul_of_nonneg_right h hB.le)]
      ring
    · rw [min_eq_left h, min_eq_left (show B ≤ exp z * B by simpa only [one_mul] using mul_le_mul_of_nonneg_right h hB.le)]
      ring
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(volume : Measure ℝ).ae_ne (exp (-z))] with g hne hg
  rw [uIoc_of_le hab] at hg
  have hgpos : 0 < g := ha.trans hg.1
  have hd : g * exp z ≠ 1 := fun he ↦ hne (by
    have e := (eq_div_iff (exp_pos z).ne').mpr he
    simpa only [one_div, exp_neg] using e)
  have hphase : (g * exp z)⁻¹ = exp (-z) / g := by rw [exp_neg, mul_inv_rev, div_eq_mul_inv]
  rw [finiteCosineTrace_eq_phaseKernels hcut hL (mul_pos hgpos (exp_pos z)) hd, hscale, hphase]
  push_cast
  ring

/-- Exact reciprocal coordinates for every real log shift. The two bounds are
the reversed endpoint values of `g ↦ exp (-z) / g - 1`. -/
theorem shiftedAmbientTrace_eq_phaseIntegral (φ : C_c(ℝ≥0ˣ, ℂ)) (w : ℝ → ℝ)
    {a b B L : ℝ} (ha : 0 < a) (hab : a ≤ b) (hB : 0 < B) (hL : 0 ≤ L)
    (hφ : ∀ u : ℝ≥0ˣ, φ u = (w (u.val : ℝ) : ℂ)) (hs : ∀ g, g ∉ Icc a b → w g = 0)
    (z : ℝ) :
    hilbertTrace (compactCosineTraceOperator 0 (min B (exp z * B)) 0 L
      (compactRadialTranslate φ (expRadialUnit z))) =
      ((∫ c in (exp (-z) / b - 1)..(exp (-z) / a - 1),
        (w (exp (-z) / (1 + c)) / sqrt (1 + c)) *
          (phaseKernel ((B * L) * min 1 (exp z)) c + phaseKernel ((B * L) * min 1 (exp z)) (c + 2)) : ℝ) : ℂ) := by
  rw [shiftedAmbientTrace_eq_haarIntegral φ w ha hab hB hL hφ hs]
  apply congrArg Complex.ofReal
  simpa only [exp_neg, div_inv_eq_mul] using reciprocalPhaseIntegral ha hab (exp_pos (-z)) w
    (fun c ↦ phaseKernel ((B * L) * min 1 (exp z)) c + phaseKernel ((B * L) * min 1 (exp z)) (c + 2))

end RiemannMasullo.ThroughOneStability
