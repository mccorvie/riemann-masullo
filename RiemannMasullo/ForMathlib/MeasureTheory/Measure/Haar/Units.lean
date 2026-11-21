module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.RingTheory.Complex
public import Mathlib.Topology.Algebra.IsOpenUnits

/-! # Haar measures on the units of a normed field

An additive Haar measure weighted by a negative power of the norm, restricted to the units,
is a multiplicative Haar measure as soon as the additive measure scales by that power of the
norm. The scaling laws on `ℝ` and `ℂ` are included.
-/

public section

open MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace RiemannMasullo

/-- On the units of a normed field, the additive Haar measure weighted by `‖x‖⁻ᵐ` is a
multiplicative Haar measure, provided multiplication by `a` scales the additive measure by
`‖a‖⁻ᵐ`. -/
theorem isHaarMeasure_comap_units_withDensity {K : Type*} [NormedField K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] (m : ℕ)
    (hscale : ∀ a : K, a ≠ 0 →
      μ.map (a * ·) = ((↑(‖a‖₊ ^ m) : ℝ≥0∞))⁻¹ • μ) :
    ((μ.withDensity fun x ↦ ((↑(‖x‖₊ ^ m) : ℝ≥0∞))⁻¹).comap Units.val).IsHaarMeasure := by
  set ρ : K → ℝ≥0∞ := fun x ↦ ((↑(‖x‖₊ ^ m) : ℝ≥0∞))⁻¹ with hρ
  set μ' := μ.withDensity ρ
  have hρm : Measurable ρ := by
    simp only [hρ]
    fun_prop
  have hB : BorelSpace Kˣ := by
    refine ⟨?_⟩
    rw [Units.isEmbedding_val₀.eq_induced, borel_comap, ← BorelSpace.measurable_eq]
    rfl
  have himg : ∀ s : Set Kˣ, MeasurableSet s → MeasurableSet (Units.val '' s) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Set.image_preimage_eq_inter_range]
    refine ht.inter ?_
    have : Set.range (Units.val : Kˣ → K) = {0}ᶜ := by
      ext x
      exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.ne_zero, fun h ↦ ⟨Units.mk0 x h, rfl⟩⟩
    rw [this]
    exact (measurableSet_singleton 0).compl
  -- invariance of μ' under multiplication by a nonzero scalar
  have hinv : ∀ a : K, a ≠ 0 → μ'.map (a * ·) = μ' := by
    intro a ha
    have hmeas : Measurable (a * · : K → K) := (continuous_const.mul continuous_id).measurable
    set N : ℝ≥0∞ := ↑(‖a‖₊ ^ m)
    have hN0 : N ≠ 0 := by simp [N, ha]
    have hNt : N ≠ ⊤ := ENNReal.coe_ne_top
    have hρa (x : K) : ρ x = N * ρ (a * x) := by
      simp only [hρ, N, nnNorm_mul, mul_pow, ENNReal.coe_mul]
      rw [ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top), ← mul_assoc,
        ENNReal.mul_inv_cancel (by simpa [N] using hN0) ENNReal.coe_ne_top, one_mul]
    ext t ht
    rw [Measure.map_apply hmeas ht, withDensity_apply _ (hmeas ht), withDensity_apply _ ht]
    conv_lhs => rw [show ρ = fun x ↦ N * ρ (a * x) from funext hρa]
    beta_reduce
    rw [lintegral_const_mul' _ _ hNt, ← setLIntegral_map ht hρm hmeas, hscale a ha,
      Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel hN0 hNt, one_mul]
  have hρpos : ∀ x, ρ x ≠ 0 := fun x ↦ ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
  have h1 : IsFiniteMeasureOnCompacts (μ'.comap (Units.val : Kˣ → K)) := by
    refine ⟨fun C hC ↦ ?_⟩
    rw [Measure.comap_apply _ Units.val_injective himg _ hC.measurableSet]
    rcases C.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨u₀, -, hu₀⟩ := hC.exists_isMinOn hne
      (continuous_norm.comp Units.continuous_val).continuousOn
    have hbound : ∀ x ∈ Units.val '' C, ρ x ≤ ρ u₀.val := by
      rintro _ ⟨u, hu, rfl⟩
      simp only [hρ]
      refine ENNReal.inv_le_inv.mpr (ENNReal.coe_le_coe.mpr (pow_le_pow_left₀ zero_le ?_ m))
      exact hu₀ hu
    have hfin : ρ u₀.val ≠ ⊤ := ENNReal.inv_ne_top.mpr (by simp [u₀.ne_zero])
    calc μ' (Units.val '' C) = ∫⁻ x in Units.val '' C, ρ x ∂μ :=
          withDensity_apply _ (himg _ hC.measurableSet)
      _ ≤ ∫⁻ _ in Units.val '' C, ρ u₀.val ∂μ := setLIntegral_mono measurable_const hbound
      _ = ρ u₀.val * μ (Units.val '' C) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top hfin.lt_top
          (hC.image Units.continuous_val).measure_lt_top
  have h3 : Measure.IsOpenPosMeasure (μ'.comap (Units.val : Kˣ → K)) := by
    refine ⟨fun U hU hne ↦ ?_⟩
    rw [Measure.comap_apply _ Units.val_injective himg _ hU.measurableSet]
    intro h0
    rw [withDensity_apply_eq_zero' hρm.aemeasurable] at h0
    have : {x | ρ x ≠ 0} = univ := Set.eq_univ_of_forall hρpos
    rw [this, univ_inter] at h0
    have hopen : IsOpen (Units.val '' U) := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).isOpenMap U hU
    exact (hopen.measure_pos μ (hne.image _)).ne' h0
  have h2 : Measure.IsMulLeftInvariant (μ'.comap (Units.val : Kˣ → K)) := by
    refine ⟨fun g ↦ ?_⟩
    ext s hs
    have hmeas : Measurable (g * · : Kˣ → Kˣ) := (continuous_const.mul continuous_id).measurable
    rw [Measure.map_apply hmeas hs, Measure.comap_apply _ Units.val_injective himg _ (hmeas hs),
      Measure.comap_apply _ Units.val_injective himg _ hs]
    have himage : Units.val '' ((g * ·) ⁻¹' s) = (g.val * ·) ⁻¹' (Units.val '' s) := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨g * u, hu, rfl⟩
      · rintro ⟨u, hu, hux⟩
        refine ⟨g⁻¹ * u, by simpa using hu, ?_⟩
        simp only [Units.val_mul, hux, ← mul_assoc, Units.inv_mul, one_mul]
    rw [himage, ← Measure.map_apply (measurable_const_mul g.val) (himg s hs),
      hinv g.val g.ne_zero]
  exact { toIsFiniteMeasureOnCompacts := h1, toIsMulLeftInvariant := h2, toIsOpenPosMeasure := h3 }

/-- A scaling law for multiplication on one field transports along a measurable ring
isomorphism to its pushforward. -/
theorem map_mul_left_map_ringEquiv {E K : Type*} [Field E] [Field K] [MeasurableSpace E]
    [MeasurableSpace K] [MeasurableMul E] [MeasurableMul K] (e : E ≃+* K) (he : Measurable e)
    (ν : Measure E) (c : E → ℝ≥0∞) (h : ∀ b : E, b ≠ 0 → ν.map (b * ·) = c b • ν)
    (a : K) (ha : a ≠ 0) : (ν.map e).map (a * ·) = c (e.symm a) • ν.map e := by
  have hcomp : (a * ·) ∘ e = e ∘ (e.symm a * ·) := by
    ext x
    simp
  rw [Measure.map_map (measurable_const_mul a) he, hcomp,
    ← Measure.map_map he (measurable_const_mul _), h _ (by simpa using ha), Measure.map_smul]
  exact he.aemeasurable

/-- Multiplication by `b ≠ 0` scales Lebesgue measure on the real line by `|b|⁻¹`. -/
theorem real_map_mul_left_volume (b : ℝ) (hb : b ≠ 0) :
    (volume : Measure ℝ).map (b * ·) = ((↑(‖b‖₊ ^ 1) : ℝ≥0∞))⁻¹ • volume := by
  rw [Real.map_volume_mul_left hb, pow_one, abs_inv, ENNReal.ofReal_inv_of_pos (abs_pos.mpr hb),
    ← Real.norm_eq_abs, ofReal_norm]
  rfl

/-- Multiplication by `b ≠ 0` scales Lebesgue measure on the complex plane by `|b|⁻²`. -/
theorem complex_map_mul_left_volume (b : ℂ) (hb : b ≠ 0) :
    (volume : Measure ℂ).map (b * ·) = ((↑(‖b‖₊ ^ 2) : ℝ≥0∞))⁻¹ • volume := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ b) = Complex.normSq b := by
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
    (f := LinearMap.mulLeft ℝ b) (by rw [hdet]; exact Complex.normSq_pos.mpr hb |>.ne')
  rw [hdet] at h
  change (volume : Measure ℂ).map (LinearMap.mulLeft ℝ b) = _
  rw [h, Complex.normSq_eq_norm_sq, abs_inv, abs_of_nonneg (sq_nonneg _),
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm]
  rfl

end RiemannMasullo
