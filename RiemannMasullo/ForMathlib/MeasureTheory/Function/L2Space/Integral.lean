module

public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Prod

public section

open Filter MeasureTheory Set
open scoped ENNReal

namespace RiemannMasullo

/-- A jointly measurable family of representatives computes the Bochner integral
of a family in complex L² pointwise almost everywhere. -/
theorem integral_L2_representative {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SigmaFinite ν]
    {F : X → Lp ℂ 2 ν} (hF : Integrable F μ) {f : X × Y → ℂ}
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hrep : ∀ᵐ x ∂μ, (F x : Y → ℂ) =ᵐ[ν] fun y ↦ f (x, y)) :
    ∀ᵐ y ∂ν, Integrable (fun x ↦ f (x, y)) μ ∧
      (∫ x, F x ∂μ) y = ∫ x, f (x, y) ∂μ := by
  have hlocal (s : Set Y) (hs : MeasurableSet s) (hνs : ν s < ∞) :
      Integrable f (μ.prod (ν.restrict s)) := by
    have hm : AEStronglyMeasurable f (μ.prod (ν.restrict s)) := hf.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
    apply (integrable_prod_iff hm).2
    constructor
    · filter_upwards [hrep] with x hx
      exact (integrableOn_Lp_of_measure_ne_top (F x) (by norm_num) hνs.ne).congr (ae_restrict_of_ae hx)
    · let i := indicatorConstLp 2 hs hνs.ne (1 : ℝ)
      refine (hF.norm.const_mul ‖i‖).mono' hm.norm.integral_prod_right' ?_
      filter_upwards [hrep] with x hx
      let v := (Lp.memLp (F x)).norm.toLp _
      have hv : (v : Y → ℝ) =ᵐ[ν] fun y ↦ ‖f (x, y)‖ :=
        (Lp.memLp (F x)).norm.coeFn_toLp.trans (hx.fun_comp norm)
      rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _),
        ← integral_congr_ae (ae_restrict_of_ae hv), ← L2.inner_indicatorConstLp_one hs hνs.ne v]
      have hn : ‖v‖ = ‖F x‖ := by
        rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable _), Lp.norm_def]
      exact (real_inner_le_norm i v).trans_eq (congrArg (‖i‖ * ·) hn)
  have hsec : ∀ᵐ y ∂ν, Integrable (fun x ↦ f (x, y)) μ := by
    rw [← Measure.restrict_univ (μ := ν), ← iUnion_spanningSets ν, ae_restrict_iUnion_iff]
    exact fun n ↦ (hlocal _ (measurableSet_spanningSets ν n) (measure_spanningSets_lt_top ν n)).prod_left_ae
  refine hsec.and (ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun _ _ hs ↦ integrableOn_Lp_of_measure_ne_top _ (by norm_num) hs.ne)
    (fun s hs hn ↦ (hlocal s hs hn).integral_prod_right) ?_)
  intro s hs hνs
  let i := indicatorConstLp 2 hs hνs.ne (1 : ℂ)
  rw [← L2.inner_indicatorConstLp_one hs hνs.ne, ← integral_inner hF]
  calc (∫ x, inner ℂ i (F x) ∂μ) = ∫ x, ∫ y in s, f (x, y) ∂ν ∂μ := by
        apply integral_congr_ae
        filter_upwards [hrep] with x hx
        rw [L2.inner_indicatorConstLp_one hs hνs.ne]
        exact integral_congr_ae (ae_restrict_of_ae hx)
    _ = _ := integral_integral_swap (hlocal s hs hνs)

end RiemannMasullo
