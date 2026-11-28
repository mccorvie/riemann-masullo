module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_SmoothMass
import Mathlib.MeasureTheory.Measure.Real

/-! # Inversion of an atomless upper-radius law -/

public noncomputable section

open Filter MeasureTheory Set

namespace RiemannMasullo

/-- Inversion takes a probability law to a probability law. -/
theorem inverseRadiusLaw_isProbabilityMeasure (σ : Measure ℝ) [IsProbabilityMeasure σ] :
    IsProbabilityMeasure (σ.map (Inv.inv : ℝ → ℝ)) :=
  (Measure.isProbabilityMeasure_map_iff measurable_inv.aemeasurable).mpr inferInstance

/-- Inverting radii supported on a positive interval inverts and swaps its endpoints. -/
theorem inverseRadiusLaw_support (σ : Measure ℝ) {a L : ℝ} (ha : 0 < a)
    (hσ : σ (Icc a L)ᶜ = 0) :
    (σ.map (Inv.inv : ℝ → ℝ)) (Icc L⁻¹ a⁻¹)ᶜ = 0 := by
  rw [Measure.map_apply measurable_inv measurableSet_Icc.compl]
  refine measure_mono_null ?_ hσ
  intro x hx hmem
  apply hx
  exact ⟨inv_anti₀ (ha.trans_le hmem.1) hmem.2, inv_anti₀ ha hmem.1⟩

/-- The survival function of the inverse law is the complementary reversed
survival function. Atomlessness permits using a closed interval at the endpoint. -/
theorem avgCutoff_inverseRadiusLaw (σ : Measure ℝ) [IsProbabilityMeasure σ]
    [NullSingletonClass σ] {a L t : ℝ} (ha : 0 < a) (hσ : σ (Icc a L)ᶜ = 0)
    (ht : 0 < t) :
    Isolated.avgCutoff (σ.map (Inv.inv : ℝ → ℝ)) t = 1 - Isolated.avgCutoff σ t⁻¹ := by
  have hpre : ((Inv.inv : ℝ → ℝ) ⁻¹' Ici t) =ᵐ[σ] Iic t⁻¹ := by
    filter_upwards [Isolated.ae_mem_of_prob_support hσ] with x hx
    change (t ≤ x⁻¹) ↔ (x ≤ t⁻¹)
    exact le_inv_comm₀ ht (ha.trans_le hx.1)
  have hIic : σ (Iic t⁻¹) = σ (Iio t⁻¹) :=
    (measure_congr (Iio_ae_eq_Iic (μ := σ) (a := t⁻¹))).symm
  unfold Isolated.avgCutoff
  calc
    (σ.map (Inv.inv : ℝ → ℝ)).real (Ici t) = σ.real (Iic t⁻¹) := by
      simp only [Measure.real, Measure.map_apply measurable_inv measurableSet_Ici, measure_congr hpre]
    _ = σ.real (Iio t⁻¹) := congrArg ENNReal.toReal hIic
    _ = _ := by
      rw [← compl_Ici, measureReal_compl measurableSet_Ici]
      simp [Measure.real]

/-- The difference of the upper survival function and its inverse-law survival
function is invariant under inversion of positive radii. -/
theorem avgCutoff_sub_inverseRadiusLaw_inv (σ : Measure ℝ) [IsProbabilityMeasure σ]
    [NullSingletonClass σ] {a L t : ℝ} (ha : 0 < a) (hσ : σ (Icc a L)ᶜ = 0)
    (ht : 0 < t) :
    Isolated.avgCutoff σ t - Isolated.avgCutoff (σ.map (Inv.inv : ℝ → ℝ)) t =
      Isolated.avgCutoff σ t⁻¹ - Isolated.avgCutoff (σ.map (Inv.inv : ℝ → ℝ)) t⁻¹ := by
  rw [avgCutoff_inverseRadiusLaw σ ha hσ ht,
    avgCutoff_inverseRadiusLaw σ ha hσ (inv_pos.mpr ht), inv_inv]
  ring

end RiemannMasullo
