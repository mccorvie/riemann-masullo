module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWProjectionConcentration
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWTaylorJets

/-! # The rational real sharp trace at fixed bandwidth -/

public noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace RiemannMasullo.Isolated

/-- Paper: Theorem 12.4.1.1, Step III, pp. 515–517. At fixed positive bandwidth
and a fixed contraction `g⁻¹`, the actual sharp weighted cutoff is nuclear and
its trace converges to the even-jet geometric sum. This is the rational real
place; neither uniformity in `g` nor the adelic joint cutoff is asserted. -/
theorem exists_realPWIntervalBand_sharpTrace_limit (Y α s : ℝ)
    (hY : 0 < Y) (ha : 0 ≤ α) (hs : 0 ≤ s) (g : ℝ) (hg : 1 < g) :
    let μ := realPWIntervalMeasure α s
    let hμ := volume_le_realPWIntervalMeasure α s hs
    let V := RealPWBand.space Y hμ
    let b := ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    let q := ((g⁻¹ : ℝ) : ℂ)
    ∃ sharp : ℝ → nuclearEndomorphisms V,
      (∀ L (f : V), ∃ r : Lp ℂ 2 μ,
        (∀ᵐ x ∂μ, r x = b * sharpIntervalMask L x * RealPWBand.evaluation Y hμ (g⁻¹ * x) f) ∧
          (sharp L).val f = V.orthogonalProjectionOnto r) ∧
      Tendsto (fun L ↦ hilbertTrace (sharp L)) atTop
        (𝓝 (b * q ^ (2 * realPWOriginJetCount α) / (1 - q ^ 2))) := by
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let n := realPWOriginJetCount α
  let ℓ (j : ℕ) := RealPWBand.evaluationJet Y hμ (2 * (n + j)) 0
  have hg₀ := zero_lt_one.trans hg
  have hq : g⁻¹ < 1 := by rw [inv_eq_one_div]; exact (div_lt_one hg₀).2 hg
  let c := (1 - g⁻¹) * Y / 2
  have hc : 0 < c := by dsimp only [c]; exact half_pos (mul_pos (sub_pos.mpr hq) hY)
  have hmargin : c ≤ (1 - g⁻¹) * Y := half_le_self (mul_nonneg (sub_nonneg.mpr hq.le) hY.le)
  obtain ⟨η, he, hm, hη, hmoment⟩ := exists_evenSchwartz_smoothingKernel c hc
  obtain ⟨sharp, smooth, hsharp, hlocal, htrace, hact⟩ :=
    exists_realPWSharpSmoothCompressions Y α s hY ha hs g hg η he hc.le hmargin hη
  have hzero (f : RealPWBand.space Y hμ) : ∀ k < 2 * n,
      iteratedDeriv k (fun x ↦ RealPWBand.evaluation Y hμ x f) 0 = 0 :=
    realPWInterval_forcedOriginJets Y α s ha hs n (fun j hj ↦ realPWOriginJetCount_min α hj) f
  refine ⟨sharp, hsharp, ?_⟩
  apply realPWIntervalBand_sharpTrace_tendsto Y α s hs g hg n η η.integrable hm hmoment
    (fun L k ↦ RealPWBand.contDiff_smoothIntervalMask_of_fourier_support η hc.le hη L k)
    hlocal (realPWSharpDensity_decay hY ha hs hg) sharp smooth htrace hact hzero ℓ
    (realPWInterval_evaluationJet_tail_linearIndependent hY ha hs) ?_ ?_
  · intro f hf
    exact RealPWBand.eq_zero_of_evaluationJet_tail Y hY.le hμ
      (realPWIntervalMeasure_absolutelyContinuous α s) n f
      (fun j hj ↦ hzero f (2 * j) (by omega)) hf
  · intro j f
    exact RealPWBand.evaluationJet_apply Y hμ (2 * (n + j)) 0 f

end RiemannMasullo.Isolated
