module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RatEmptyActualLevelBridge
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelOperator

public import RiemannMasullo.AppC_LCTVS.Sec3_ProjectedNuclearCompression

/-! # The genuine rational physical compression and its trace

The quotient dilation, norm cutoff, and actual invariant level are transported
together. This compares the physical compression, not a separately chosen
additive Fourier mask or the general quotient kernel. -/

public noncomputable section
open MeasureTheory Function Set Filter NumberField IsDedekindDomain
open scoped NNReal ENNReal NumberField.AdeleRing
namespace RiemannMasullo.RatEmptyRealLevelBridge
open RatEmptyMeasureCoordinate RatEmptyHaarHalfDensity FlatPolar
local notation "S₀" => (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
local notation "J" => SIdeleQuotient ℚ S₀
local notation "N" => sIdeleQuotientNorm ℚ S₀
local notation "ν" => sLocalQuotientTamagawaMeasure ℚ S₀
local instance : MeasurableSpace J := borel _
local instance : BorelSpace J := ⟨rfl⟩
local notation "rad(" g ")" => ((Units.val (N g) : ℝ≥0) : ℝ)
local notation "ν₀" => Measure.withDensity ν (fun g ↦ ENNReal.ofReal
  (intervalSobolevDensity 0 0 0 (Real.log rad(g))))
local notation "W" => Lp ℂ 2 ν₀
local notation "ray" => volume.restrict (Ioi (0 : ℝ))
local notation "val(" a ")" => ((Units.val a : ℝ≥0) : ℝ)

/-- The unique actual quotient idele of this norm. -/
def quotientElement (a : ℝ≥0ˣ) : J := normEquiv.symm a

theorem quotientElement_spec (a : ℝ≥0ˣ) : N (quotientElement a) = a :=
  normEquiv.apply_symm_apply a

theorem quotientElement_unique {a : ℝ≥0ˣ} {g : J} (h : N g = a) : g = quotientElement a :=
  normEquiv.injective (h.trans (quotientElement_spec a).symm)

private theorem scale_pos (a : ℝ≥0ˣ) : 0 < val(a) := by
  exact_mod_cast (pos_iff_ne_zero.mpr a.ne_zero : 0 < a.val)

/-- Unitary left translation, realized through the ray chart; its quotient representative
is unweighted (see `actualHaarDilation_apply`). -/
def actualHaarDilation (a : ℝ≥0ˣ) : W ≃ₗᵢ[ℂ] W :=
  (rayChart.trans (positiveRayDilation (val(a))⁻¹ (inv_pos.mpr (scale_pos a)))).trans rayChart.symm

/-- Left (not right-inverse) action: pull back along `g ↦ jₐ⁻¹ * g`. -/
theorem actualHaarDilation_apply (a : ℝ≥0ˣ) (v : W) :
    (actualHaarDilation a v : J → ℂ) =ᵐ[ν] fun g ↦ v ((quotientElement a)⁻¹ * g) := by
  let f := rayChart v
  let b := (val(a))⁻¹
  have hb : 0 < b := inv_pos.mpr (scale_pos a)
  let D := positiveRayDilation b hb
  have hf : (v : J → ℂ) =ᵐ[ν] fun g ↦ (Real.sqrt rad(g) : ℂ) * f rad(g) := by
    simpa only [f, LinearIsometryEquiv.symm_apply_apply] using rayChart_symm_ae f
  let : Measure.IsHaarMeasure ν := (sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := S₀)).1
  have hshift := (measurePreserving_mul_left ν (quotientElement a)⁻¹).quasiMeasurePreserving.ae hf
  have hD := norm_preserving.quasiMeasurePreserving.ae (rad_ae
    (P := fun r ↦ D f r = (Real.sqrt b : ℂ) * f (b * r)) (positiveRayDilation_apply b hb f))
  change (rayChart.symm (D f) : J → ℂ) =ᵐ[ν] _
  filter_upwards [rayChart_symm_ae (D f), hshift, hD] with g hg hs hd
  change v ((quotientElement a)⁻¹ * g) = _ at hs
  simp only [normEquiv_apply] at hd
  change D f rad(g) = _ at hd
  have hr : rad((quotientElement a)⁻¹ * g) = b * rad(g) := by
    simp only [b, map_mul, map_inv, quotientElement_spec, Units.val_mul,
      Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv]
  rw [hg, hs, hr, hd, Real.sqrt_mul hb.le, Complex.ofReal_mul]
  ring

/-- With the normalized even extension, left Haar translation is exactly the physical
`(√a)⁻¹ f(x / a)` dilation, without a residual scalar. -/
theorem embedding_actualHaarDilation (a : ℝ≥0ˣ) (v : W) :
    embedding (actualHaarDilation a v) = realDilation val(a) (embedding v) := by
  have ha := scale_pos a
  let b := (val(a))⁻¹
  have hb : 0 < b := inv_pos.mpr ha
  change positiveRayEvenExtension (rayChart (rayChart.symm (positiveRayDilation b hb (rayChart v)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, positiveRayEvenExtension_dilation]
  change FullLine.dilation b hb.ne' (embedding v) = _
  apply Lp.ext
  filter_upwards [FullLine.dilation_apply b hb.ne' (embedding v), coeFn_realDilation ha (embedding v)]
    with x hx hy
  rw [hx, hy, abs_of_pos hb]
  simp only [b, Real.sqrt_inv, inv_mul_eq_div]

local notation "R₂" => Lp ℂ 2 ray

private def rayWindowVec (L : ℝ) (u : R₂) : R₂ :=
  ((Lp.memLp u).indicator (measurableSet_Iic : MeasurableSet (Iic L)).nullMeasurableSet).toLp _

private theorem rayWindow_ae (L : ℝ) (u : R₂) :
    ⇑(rayWindowVec L u) =ᵐ[ray] (Iic L).indicator u := MemLp.coeFn_toLp _

private def rayWindow (L : ℝ) : R₂ →L[ℂ] R₂ :=
  LinearMap.mkContinuous
    { toFun := rayWindowVec L
      map_add' := fun f g ↦ by
        apply Lp.ext
        filter_upwards [rayWindow_ae L (f + g), rayWindow_ae L f, rayWindow_ae L g,
          Lp.coeFn_add (rayWindowVec L f) (rayWindowVec L g), Lp.coeFn_add f g]
          with x ha hf hg hs hfg
        rw [ha, hs, Pi.add_apply, hf, hg]
        by_cases hx : x ∈ Iic L
        · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx, hfg, Pi.add_apply]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx, add_zero]
      map_smul' := fun c f ↦ by
        apply Lp.ext
        filter_upwards [rayWindow_ae L (c • f), rayWindow_ae L f,
          Lp.coeFn_smul c (rayWindowVec L f), Lp.coeFn_smul c f] with x ha hf hs hcf
        by_cases hx : x ∈ Iic L <;> simp [ha, hs, hf, hx, hcf] }
    1 (fun f ↦ by
      rw [one_mul]
      change ‖rayWindowVec L f‖ ≤ ‖f‖
      rw [rayWindowVec, Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
        (eLpNorm_indicator_le _ measurableSet_Iic.nullMeasurableSet))

/-- Sharp multiplication by the quotient norm window, in the actual order-zero ambient. -/
def actualCutoff (L : ℝ) : W →L[ℂ] W :=
  rayChart.symm.toLinearIsometry.toContinuousLinearMap ∘L rayWindow L ∘L
    rayChart.toLinearIsometry.toContinuousLinearMap

/-- No Haar normalization or square-root factor survives in the cutoff multiplier. -/
theorem coeFn_actualCutoff (L : ℝ) (f : W) :
    ⇑(actualCutoff L f) =ᵐ[ν] {g : J | rad(g) ≤ L}.indicator f := by
  let u := rayChart f
  have hf := rayChart_symm_ae (rayChart f)
  rw [LinearIsometryEquiv.symm_apply_apply] at hf
  have hr := rad_ae (P := fun x ↦ rayWindowVec L u x = (Iic L).indicator (⇑u) x)
    (rayWindow_ae L u)
  filter_upwards [rayChart_symm_ae (rayWindowVec L u), hf,
    norm_preserving.quasiMeasurePreserving.ae hr] with g hc hg hw
  change rayChart.symm (rayWindowVec L u) g = _
  simp only [normEquiv_apply] at hw
  change rayWindowVec L u rad(g) = _ at hw
  rw [hc, hw]
  by_cases h : rad(g) ≤ L
  · simpa [Set.indicator, h, u] using hg.symm
  · simp [Set.indicator, h]

/-- Normalized even extension turns the norm ball into `[-L,L]`, including its boundary. -/
theorem embedding_actualCutoff (L : ℝ) (f : W) :
    embedding (actualCutoff L f) = realCutoff L (embedding f) := by
  let u := rayChart f
  change positiveRayEvenExtension (rayChart (rayChart.symm (rayWindowVec L u))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [positiveRayEvenExtension_apply (rayWindowVec L u),
    positiveRay_ae_abs (rayWindow_ae L u), coeFn_realCutoff L (embedding f),
    positiveRayEvenExtension_apply u] with x hc hw hcut hu
  change embedding f x = _ at hu
  rw [hc, hw, hcut]
  by_cases h : |x| ≤ L
  · rw [indicator_of_mem (show |x| ∈ Iic L from h),
      indicator_of_mem (show x ∈ Icc (-L) L from abs_le.mp h), hu]
  · rw [indicator_of_notMem (show |x| ∉ Iic L from h),
      indicator_of_notMem (show x ∉ Icc (-L) L from fun hx ↦ h (abs_le.mpr hx)), mul_zero]

theorem embedding_comp_actualCutoff (L : ℝ) :
    embedding.toContinuousLinearMap ∘L actualCutoff L =
      realCutoff L ∘L embedding.toContinuousLinearMap := by
  ext1 f
  exact embedding_actualCutoff L f

open RatEmptyGenuineLevel

local notation "A(" ω "," B ")" => sLocalInvariantPWSobolev (F := ℚ) (S := S₀) (s := 0)
  le_rfl (by norm_num : (0 : ℝ) < 1 / 2) ω B
local notation "D(" a ")" => LinearIsometry.toContinuousLinearMap (LinearIsometryEquiv.toLinearIsometry (actualHaarDilation a))

instance actualInvariantLevel_complete (ω : PontryaginDual (N).ker) (B : ℝ) :
    CompleteSpace (A(ω,B)) := by
  have h : IsClosed (A(ω,B) : Set W) := by
    rw [invariant_level_eq]
    exact Submodule.isClosed_topologicalClosure _
  exact h.completeSpace_coe

/-- The physical cutoff and left Haar–dilation, compressed on both sides
by the genuine order-zero adelic invariant level. -/
def actualCompression (ω : PontryaginDual (N).ker) (B L : ℝ) (a : ℝ≥0ˣ) : W →L[ℂ] W :=
  (A(ω,B)).starProjection ∘L actualCutoff L ∘L D(a) ∘L (A(ω,B)).starProjection

set_option maxHeartbeats 800000 in
/-- The exact actual physical compression is nuclear and has the existing flat
real order-zero trace. This does not claim an additive Fourier-mask descent. -/
theorem actualCompression_hilbertTrace (ω : PontryaginDual (N).ker) {B L : ℝ}
    (hB : 0 < B) (hL : 0 ≤ L) (a : ℝ≥0ˣ) :
    ∃ hn : IsNuclearOperator (actualCompression ω B L a),
      hilbertTrace ⟨actualCompression ω B L a, hn⟩ =
      (((Real.sqrt val(a))⁻¹ * ∫ x in (0 : ℝ)..L, realPWLevelDiagonal B val(a) x : ℝ) : ℂ) := by
  have ha : 0 < val(a) := by
    exact_mod_cast (pos_iff_ne_zero.mpr a.ne_zero : 0 < a.val)
  let P : Submodule ℂ W := A(ω,B)
  let U : W →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) := embedding
  let Dₐ : W →L[ℂ] W := D(a)
  let : CompleteSpace P := actualInvariantLevel_complete ω B
  have hmap : P.map U.toLinearMap = realPWLevel B := map_invariantLevel ω hB
  have hD (v : W) : U (Dₐ v) = realDilation val(a) (U v) := embedding_actualHaarDilation a v
  obtain ⟨_, hn, htr⟩ := transportProjectedNuclearCompression U P
    (realPWLevel B) hmap (actualCutoff L) Dₐ (realCutoff L)
    (realDilation val(a)) (embedding_actualCutoff L) hD
    (isNuclearOperator_realPWLevel_compression hB ha L)
  refine ⟨hn, ?_⟩
  exact htr.trans (hilbertTrace_realPWLevel_compression_eq hB ha hL)

end RiemannMasullo.RatEmptyRealLevelBridge
