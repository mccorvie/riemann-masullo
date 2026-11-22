module

public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public noncomputable section

open Filter Set Topology MeasureTheory
open scoped ENNReal

namespace RiemannMasullo

/-- A pointwise continuous linear family of integrable functions on a first-countable barrelled
space has a continuous integral functional. Fatou makes the integral of its norm a lower
semicontinuous seminorm, hence a continuous one. -/
theorem exists_integralCLM_of_pointwise_continuous {X E : Type*} [MeasurableSpace X] (μ : Measure X)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [FirstCountableTopology E] [IsTopologicalAddGroup E]
    [BarrelledSpace ℂ E] (A : E →ₗ[ℂ] (X → ℂ))
    (hcont : ∀ x, Continuous (fun e ↦ A e x)) (hint : ∀ e, Integrable (A e) μ) :
    ∃ L : E →L[ℂ] ℂ, ∀ e, L e = ∫ x, A e x ∂μ := by
  let B : E →ₗ[ℂ] Lp ℂ 1 μ :=
    { toFun := fun v ↦ (hint v).toL1 (A v)
      map_add' := fun v w ↦ by
        apply Lp.ext
        filter_upwards [(hint (v+w)).coeFn_toL1,(hint v).coeFn_toL1,(hint w).coeFn_toL1,
          Lp.coeFn_add ((hint v).toL1 _) ((hint w).toL1 _)] with x hx hv hw hs
        rw [hx,hs]
        simp only [Pi.add_apply,hv,hw,A.map_add]
      map_smul' := fun c v ↦ by
        apply Lp.ext
        filter_upwards [(hint (c • v)).coeFn_toL1,(hint v).coeFn_toL1,
          Lp.coeFn_smul c ((hint v).toL1 _)] with x hx hv hs
        rw [hx,RingHom.id_apply,hs]
        simp only [Pi.smul_apply,hv,A.map_smul] }
  let p := (normSeminorm ℂ (Lp ℂ 1 μ)).comp B
  have hp (v : E) : ENNReal.ofReal (p v) = ∫⁻ x, ‖A v x‖ₑ ∂μ := by
    change ENNReal.ofReal ‖(hint v).toL1 (A v)‖ = _
    rw [Integrable.norm_toL1_eq_lintegral_eNorm,ENNReal.ofReal_toReal (hint v).2.ne]
  have hpcont : Continuous p := by
    apply p.continuous_of_lowerSemicontinuous
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro r
    apply IsSeqClosed.isClosed
    intro u v hu huv
    have hpt (x : X) : Tendsto (fun n ↦ ‖A (u n) x‖ₑ) atTop (𝓝 ‖A v x‖ₑ) :=
      (((hcont x).tendsto v).comp huv).eNorm
    obtain hr : 0 ≤ r := (apply_nonneg p (u 0)).trans (hu 0)
    rw [Set.mem_preimage, Set.mem_Iic,← ENNReal.ofReal_le_ofReal_iff hr,hp]
    calc
      _ = ∫⁻ x, liminf (fun n ↦ ‖A (u n) x‖ₑ) atTop ∂μ := lintegral_congr fun x ↦ (hpt x).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le' (fun n ↦ (hint (u n)).aestronglyMeasurable.eNorm)
      _ ≤ ENNReal.ofReal r := liminf_le_of_frequently_le' (.of_forall fun n ↦
        (hp (u n)).symm.le.trans (ENNReal.ofReal_le_ofReal (hu n)))
  let L : E →ₗ[ℂ] ℂ :=
    { toFun := fun v ↦ ∫ x, A v x ∂μ
      map_add' := fun v w ↦ by rw [A.map_add]; exact integral_add (hint v) (hint w)
      map_smul' := fun c v ↦ by rw [A.map_smul]; exact integral_smul c _ }
  have hL : Continuous L := by
    apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦ ?_
    apply Seminorm.continuous_of_le hpcont
    intro v
    change ‖∫ x, A v x ∂μ‖ ≤ ‖(hint v).toL1 _‖
    rw [Integrable.norm_toL1_eq_lintegral_eNorm,← integral_norm_eq_lintegral_eNorm (hint v).aestronglyMeasurable]
    exact norm_integral_le_integral_norm _
  exact ⟨⟨L,hL⟩,fun _ ↦ rfl⟩

end RiemannMasullo
