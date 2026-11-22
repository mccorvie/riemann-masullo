module

public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace RiemannMasullo

variable {G : Type*} [MeasurableSpace G] (μ : Measure G)

/-- The weighted integral of the norm of a linear family of scalar functions is a seminorm. -/
theorem exists_integral_seminorm {V : Type*} [AddCommGroup V] [Module ℂ V]
    (j : V →ₗ[ℂ] (G → ℂ)) (w : G → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hi : ∀ f, Integrable (fun x ↦ ‖j f x‖ * w x) μ) :
    ∃ q : Seminorm ℂ V, ∀ f, q f = ∫ x, ‖j f x‖ * w x ∂μ := by
  let q : Seminorm ℂ V :=
    { toFun := fun f ↦ ∫ x, ‖j f x‖ * w x ∂μ
      map_zero' := by simp
      add_le' := fun f g ↦ by
        rw [← integral_add (hi f) (hi g)]
        refine integral_mono (hi (f + g)) ((hi f).add (hi g)) fun x ↦ ?_
        simp only [map_add, Pi.add_apply]
        change ‖j f x + j g x‖ * w x ≤ ‖j f x‖ * w x + ‖j g x‖ * w x
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (hw x)
      neg' := fun f ↦ by
        simp only [map_neg, Pi.neg_apply, norm_neg]
      smul' := fun c f ↦ by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact .of_forall fun x ↦ by simp [mul_assoc] }
  exact ⟨q, fun _ ↦ rfl⟩

/-- On a first-countable barrelled space, Fatou's lemma makes a finite weighted
integral seminorm continuous as soon as the point evaluations are continuous. -/
theorem continuous_integral_seminorm {V : Type*} [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] [FirstCountableTopology V] [BarrelledSpace ℂ V]
    (j : V → G → ℂ) (hj : ∀ x, Continuous fun f ↦ j f x)
    (w : G → ℝ) (hw : ∀ x, 0 ≤ w x) (hi : ∀ f, Integrable (fun x ↦ ‖j f x‖ * w x) μ)
    (q : Seminorm ℂ V) (hq : ∀ f, q f = ∫ x, ‖j f x‖ * w x ∂μ) : Continuous q := by
  apply Seminorm.continuous_of_lowerSemicontinuous
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro C
  apply isSeqClosed_iff_isClosed.mp
  intro v f hv hlim
  change q f ≤ C
  have hC : 0 ≤ C := (apply_nonneg q (v 0)).trans (hv 0)
  let F (u : V) (x : G) := ENNReal.ofReal (‖j u x‖ * w x)
  have hqI (u) : ENNReal.ofReal (q u) = ∫⁻ x, F u x ∂μ := by
    rw [hq]
    exact ofReal_integral_eq_lintegral_ofReal (hi u) (.of_forall fun x ↦ mul_nonneg (norm_nonneg _) (hw x))
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [hqI]
  have hpt (x : G) : Tendsto (fun n ↦ F (v n) x) atTop (𝓝 (F f x)) :=
    (ENNReal.continuous_ofReal.comp ((hj x).norm.mul
      (continuous_const (y := w x)))).continuousAt.tendsto.comp hlim
  calc
    ∫⁻ x, F f x ∂μ = ∫⁻ x, atTop.liminf (fun n ↦ F (v n) x) ∂μ :=
      lintegral_congr fun x ↦ (hpt x).liminf_eq.symm
    _ ≤ _ := lintegral_liminf_le' fun n ↦ (hi (v n)).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    _ ≤ ENNReal.ofReal C := liminf_le_of_frequently_le' (.of_forall fun n ↦
      (hqI _).symm.le.trans (ENNReal.ofReal_le_ofReal (hv n)))

end RiemannMasullo
