module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.WeightedPaleyWienerBand
public import RiemannMasullo.ForMathlib.Analysis.Fourier.SharpIntervalSmoothing
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.Inversion

/-! # Spatial and frequency-limited masks for real Paley–Wiener bands -/

public section

open Set Filter MeasureTheory
open scoped FourierTransform SchwartzMap Topology

namespace RiemannMasullo.RealPWBand

/-- A compact mask forces the product to vanish on a ray. If the product were
analytic, the identity theorem would make it zero everywhere. On an open set
where the mask is nonzero, this would force the dilated analytic input to vanish. -/
theorem not_analyticOnNhd_compactMask_mul_dilate {m f : ℝ → ℂ} {a : ℝ}
    (hm : Continuous m) (hc : HasCompactSupport m) (hm₀ : ∃ x, m x ≠ 0)
    (hf : AnalyticOnNhd ℝ f univ) (hf₀ : ∃ x, f x ≠ 0) (ha : a ≠ 0) :
    ¬ AnalyticOnNhd ℝ (fun x ↦ m x * f (a * x)) univ := by
  intro hp
  obtain ⟨B, hB⟩ := hc.isCompact.bddAbove
  have hz : AnalyticOnNhd ℝ (fun _ : ℝ ↦ (0 : ℂ)) univ := fun _ _ ↦ analyticAt_const
  have hzero := hp.eq_of_eventuallyEq hz (z₀ := B + 1) (by
    filter_upwards [lt_mem_nhds (show B < B + 1 by linarith)] with x hx
    have hout : x ∉ tsupport m := fun h ↦ hx.not_ge (hB h)
    simp [image_eq_zero_of_notMem_tsupport hout])
  obtain ⟨u, hu⟩ := hm₀
  have hd : AnalyticOnNhd ℝ (fun x ↦ f (a * x)) univ := fun x _ ↦
    (hf (a * x) (mem_univ _)).comp (analyticAt_const.mul analyticAt_id)
  have hdzero := hd.eq_of_eventuallyEq hz (z₀ := u) (by
    filter_upwards [hm.continuousAt.eventually_ne hu] with x hx
    exact (mul_eq_zero.mp (congrFun hzero x)).resolve_left hx)
  obtain ⟨v, hv⟩ := hf₀
  exact hv (by simpa only [mul_div_cancel₀ v ha] using congrFun hdzero (v / a))

/-- An unprojected compactly masked dilation of a nonzero band representative
cannot be the representative of another band vector. -/
theorem evaluation_ne_compactMask_mul_dilate {Y Z : ℝ} {μ : Measure ℝ}
    {hμ : volume ≤ μ} (f : space Y hμ) (g : space Z hμ) {m : ℝ → ℂ} {a : ℝ}
    (hm : Continuous m) (hc : HasCompactSupport m) (hm₀ : ∃ x, m x ≠ 0)
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hf₀ : ∃ x, evaluation Y hμ x f ≠ 0) (ha : a ≠ 0) :
    (fun x ↦ evaluation Z hμ x g) ≠ (fun x ↦ m x * evaluation Y hμ (a * x) f) := by
  intro he
  exact not_analyticOnNhd_compactMask_mul_dilate hm hc hm₀
    (analyticOnNhd_evaluation Y hY hμ f) hf₀ ha (he ▸ analyticOnNhd_evaluation Z hZ hμ g)

private theorem exists_entire_smoothIntervalMask_type (η : 𝓢(ℝ, ℂ)) {c : ℝ} (hc : 0 ≤ c)
    (hη : Function.support (𝓕 (η : ℝ → ℂ)) ⊆ Icc (-c) c) (L : ℝ) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ x : ℝ, g x = smoothIntervalMask η L x) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖g z‖ ≤ C * Real.exp (2 * Real.pi * c * ‖z‖) := by
  let m := smoothIntervalMask η L
  have hi : Integrable m := integrable_smoothIntervalMask η η.integrable L
  have hs : Function.support (𝓕 m) ⊆ Icc (-c) c := by
    intro x hx
    apply hη
    change 𝓕 (η : ℝ → ℂ) x ≠ 0
    intro hz
    apply hx
    rw [show 𝓕 m x = _ from fourier_smoothIntervalMask_eq_mul η η.integrable L x, hz, zero_mul]
  have hk : HasCompactSupport (𝓕 m) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hs isClosed_Icc)
  have hcont : Continuous (𝓕 m) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi
  have hI : Integrable (𝓕 m) := hcont.integrable_of_hasCompactSupport hk
  obtain ⟨g, hg, he, hb⟩ := exists_entire_fourierInv_of_band hc hI.integrableOn
    ((ae_restrict_iff' measurableSet_Icc.compl).2 (ae_of_all _ fun t ht ↦
      not_ne_iff.mp fun hn ↦ ht (hs hn)))
  exact ⟨g, hg, fun x ↦ (he x).trans
    (congrFun ((continuous_smoothIntervalMask η L).fourierInv_fourier_eq hi hI) x), hb⟩

/-- The actual smoothed mask has derivatives of every finite order when its
smoothing kernel is band limited. -/
theorem contDiff_smoothIntervalMask_of_fourier_support (η : 𝓢(ℝ, ℂ)) {c : ℝ} (hc : 0 ≤ c)
    (hη : Function.support (𝓕 (η : ℝ → ℂ)) ⊆ Icc (-c) c) (L : ℝ) (k : ℕ) :
    ContDiff ℝ k (smoothIntervalMask η L) := by
  obtain ⟨g, hg, he, _⟩ := exists_entire_smoothIntervalMask_type η hc hη L
  rw [← funext he]
  have H : AnalyticOnNhd ℝ (fun x : ℝ ↦ g (x : ℂ)) univ := by
    intro x _
    exact ((hg.analyticAt (x : ℂ)).restrictScalars (𝕜 := ℝ)).comp_of_eq
      (Complex.ofRealCLM.analyticAt x) rfl
  exact H.contDiff

/-- Narrow Fourier smoothing uses only the bandwidth freed by dilation.
The actual product has spectrum in the original interval without a projection. -/
theorem fourier_smoothIntervalMask_mul_dilate_evaluation_zero_off
    {Y a c : ℝ} (hY : 0 < Y) (ha : 0 ≤ a) (hc : 0 ≤ c) (hmargin : c ≤ (1 - a) * Y)
    {μ : Measure ℝ} (hμ : volume ≤ μ) (f : space Y hμ)
    (η : 𝓢(ℝ, ℂ)) (hη : Function.support (𝓕 (η : ℝ → ℂ)) ⊆ Icc (-c) c)
    (L : ℝ) (b : ℂ)
    (h₂ : MemLp (fun x : ℝ ↦ b * smoothIntervalMask η L x *
      evaluation Y hμ (a * x) f) 2 volume) :
    ∀ᵐ t ∂volume.restrict (Icc (-Y) Y)ᶜ,
      (𝓕 (h₂.toLp _) : Lp ℂ 2 (volume : Measure ℝ)) t = 0 := by
  obtain ⟨M, hM, hMr, CM, hCM, hMb⟩ := exists_entire_smoothIntervalMask_type η hc hη L
  obtain ⟨G, hG, hGr, CG, hCG, hGb⟩ := exists_entire_evaluation Y hY.le hμ f
  let P (z : ℂ) := b * M z * G ((a : ℂ) * z)
  have hp : Differentiable ℂ P := (hM.const_mul b).mul (hG.comp (differentiable_id.const_mul _))
  have he : (fun x : ℝ ↦ P x) = (fun x : ℝ ↦ b * smoothIntervalMask η L x *
      evaluation Y hμ (a * x) f) := by
    funext x
    simp only [P, ← Complex.ofReal_mul, hMr, hGr]
  have hp₂ : MemLp (fun x : ℝ ↦ P x) 2 := he.symm ▸ h₂
  have hb (z : ℂ) : ‖P z‖ ≤ (‖b‖ * CM * CG) * Real.exp (2 * Real.pi * Y * ‖z‖) := by
    have hgz := hGb ((a : ℂ) * z)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha] at hgz
    calc
      ‖P z‖ = (‖b‖ * ‖M z‖) * ‖G ((a : ℂ) * z)‖ := by simp [P]
      _ ≤ (‖b‖ * (CM * Real.exp (2 * Real.pi * c * ‖z‖))) *
          (CG * Real.exp (2 * Real.pi * Y * (a * ‖z‖))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hMb z) (norm_nonneg _)) hgz
          (norm_nonneg _) (by positivity)
      _ = (‖b‖ * CM * CG) * Real.exp ((2 * Real.pi * ‖z‖) * (c + a * Y)) := by
        rw [show (2 * Real.pi * ‖z‖) * (c + a * Y) =
          2 * Real.pi * c * ‖z‖ + 2 * Real.pi * Y * (a * ‖z‖) by ring, Real.exp_add]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        rw [show 2 * Real.pi * Y * ‖z‖ = (2 * Real.pi * ‖z‖) * Y by ring]
        exact mul_le_mul_of_nonneg_left (by linarith : c + a * Y ≤ Y) (by positivity)
  have h := fourier_trace_zero_off_interval hY.le (show 0 ≤ ‖b‖ * CM * CG by positivity) hp hb hp₂
  simpa only [he] using h

end RiemannMasullo.RealPWBand
