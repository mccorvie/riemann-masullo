module
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section

open Filter MeasureTheory Set Topology

/-- A pointwise continuous linear family of integrable functions on a first countable
barrelled space depends continuously on its parameter in the L¹ norm. -/
theorem MeasureTheory.continuous_toL1_of_continuous_eval {X α : Type*} [AddCommGroup X]
    [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X] [FirstCountableTopology X]
    [BarrelledSpace ℂ X] [MeasurableSpace α] (μ : Measure α) (L : X →ₗ[ℂ] (α → ℂ))
    (hi : ∀ x, Integrable (L x) μ) (hc : ∀ a, Continuous fun x ↦ L x a) :
    Continuous fun x ↦ (hi x).toL1 (L x) := by
  let A : X →ₗ[ℂ] (α →₁[μ] ℂ) :=
    { toFun := fun x ↦ (hi x).toL1 (L x)
      map_add' := fun x y ↦ by
        simp only [map_add]
        exact Integrable.toL1_add _ _ _ _
      map_smul' := fun c x ↦ by
        simp only [map_smul, RingHom.id_apply]
        exact Integrable.toL1_smul' _ _ _ }
  let p := (normSeminorm ℂ (α →₁[μ] ℂ)).comp A
  have hen (x : X) : ENNReal.ofReal (p x) = eLpNorm (L x) 1 μ := by
    change ENNReal.ofReal ‖(hi x).toL1 (L x)‖ = _
    exact (ofReal_norm _).trans (Lp.eNorm_toLp (memLp_one_iff_integrable.mpr (hi x)))
  have hp : LowerSemicontinuous p := by
    apply lowerSemicontinuous_iff_isClosed_preimage.mpr
    intro b
    apply IsSeqClosed.isClosed
    intro u x hu hux
    have hb : 0 ≤ b := (norm_nonneg (A (u 0))).trans (hu 0)
    apply (ENNReal.ofReal_le_ofReal_iff hb).mp
    rw [hen]
    exact Lp.eLpNorm_le_of_ae_tendsto
      (.of_forall fun n ↦ (hen (u n)).symm.trans_le (ENNReal.ofReal_le_ofReal (hu n)))
      (fun n ↦ (hi (u n)).aestronglyMeasurable) (hi x).aestronglyMeasurable
      (ae_of_all _ fun a ↦ (hc a).continuousAt.tendsto.comp hux)
  apply continuous_of_tendsto_nhds_zero A
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  change Tendsto p (𝓝 0) (𝓝 0)
  simpa only [map_zero] using (p.continuous_of_lowerSemicontinuous hp).tendsto (0 : X)

/-- The integral of a pointwise continuous linear family of integrable functions on a
first countable barrelled space is a continuous linear functional. -/
theorem MeasureTheory.linearContinuous_integral_of_continuous_eval {X α : Type*} [AddCommGroup X]
    [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X] [FirstCountableTopology X]
    [BarrelledSpace ℂ X] [MeasurableSpace α] (μ : Measure α) (F : X → α → ℂ)
    (hlin : IsLinearMap ℂ F) (hi : ∀ x, Integrable (F x) μ)
    (hc : ∀ a, Continuous fun x ↦ F x a) :
    IsLinearMap ℂ (fun u ↦ ∫ x, F u x ∂μ) ∧ Continuous (fun u ↦ ∫ x, F u x ∂μ) := by
  let L := hlin.mk' F
  have hl := MeasureTheory.continuous_toL1_of_continuous_eval μ L hi hc
  refine ⟨⟨fun f h ↦ ?_, fun c f ↦ ?_⟩, ?_⟩
  · exact (congrArg (fun v : α → ℂ ↦ ∫ x, v x ∂μ) (L.map_add f h)).trans
      (integral_add (hi f) (hi h))
  · exact (congrArg (fun v : α → ℂ ↦ ∫ x, v x ∂μ) (L.map_smul c f)).trans (integral_smul c (L f))
  · exact (continuous_integral.comp hl).congr fun x ↦ integral_congr_ae (hi x).coeFn_toL1
