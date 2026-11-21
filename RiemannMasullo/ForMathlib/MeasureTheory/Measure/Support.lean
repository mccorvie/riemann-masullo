module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Support

public section

open Filter Set
open scoped Topology

namespace MeasureTheory

/-- If a kernel agrees product-almost everywhere with a continuous function of
two separately measurable parameters, then the agreement holds almost everywhere on the
diagonal at which the kernel is jointly continuous. -/
theorem ae_diagonal_eq_of_ae_eq_comp_prod
    {X Y Z W : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [TopologicalSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [TopologicalSpace W] [T2Space W]
    {μ : Measure X} [SFinite μ] {a : X → Y} {b : X → Z} {φ : Y × Z → W} {k : X × X → W}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) (hφ : Continuous φ)
    (hk : k =ᵐ[μ.prod μ] fun p ↦ φ (a p.1, b p.2))
    (hcont : ∀ᵐ x ∂μ, ContinuousAt k (x, x)) :
    (fun x ↦ k (x, x)) =ᵐ[μ] fun x ↦ φ (a x, b x) := by
  let A (x : X) : X × Y := (x, a x)
  let B (x : X) : X × Z := (x, b x)
  have hA : AEMeasurable A μ := aemeasurable_id.prodMk ha
  have hB : AEMeasurable B μ := aemeasurable_id.prodMk hb
  filter_upwards [hcont, ae_of_ae_map hA (Measure.support_mem_ae (μ := μ.map A)),
    ae_of_ae_map hB (Measure.support_mem_ae (μ := μ.map B))] with x hx hxA hxB
  by_contra hne
  let f (p : (X × Y) × (X × Z)) := k (p.1.1, p.2.1)
  let g (p : (X × Y) × (X × Z)) := φ (p.1.2, p.2.2)
  have hf : ContinuousAt f (A x, B x) := by
    let coords (p : (X × Y) × (X × Z)) : X × X := (p.1.1, p.2.1)
    have hcoords : Continuous coords := continuous_fst.fst.prodMk continuous_snd.fst
    exact (show ContinuousAt k (coords (A x, B x)) from hx).comp hcoords.continuousAt
  have hg : ContinuousAt g (A x, B x) :=
    (hφ.comp (continuous_fst.snd.prodMk continuous_snd.snd)).continuousAt
  have hsep : {p | f p ≠ g p} ∈ 𝓝 (A x, B x) :=
    (hf.ne_iff_eventually_ne hg).mp hne
  obtain ⟨U, V, hU, hxU, hV, hxV, hUV⟩ := mem_nhds_prod_iff'.mp hsep
  have hμU : 0 < μ (A ⁻¹' U) := by
    rw [← Measure.map_apply_of_aemeasurable hA hU.measurableSet]
    exact (Measure.mem_support_iff_forall _).mp hxA U (hU.mem_nhds hxU)
  have hμV : 0 < μ (B ⁻¹' V) := by
    rw [← Measure.map_apply_of_aemeasurable hB hV.measurableSet]
    exact (Measure.mem_support_iff_forall _).mp hxB V (hV.mem_nhds hxV)
  have hpos : 0 < μ.prod μ ((A ⁻¹' U) ×ˢ (B ⁻¹' V)) := by
    rw [Measure.prod_prod]
    exact pos_iff_ne_zero.mpr (mul_ne_zero hμU.ne' hμV.ne')
  apply hpos.ne'
  apply measure_mono_null _ (ae_iff.mp hk)
  exact fun p hp ↦ hUV (show (A p.1, B p.2) ∈ U ×ˢ V from hp)

end MeasureTheory
