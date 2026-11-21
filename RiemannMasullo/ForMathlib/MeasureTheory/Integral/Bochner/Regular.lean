module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
public import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UrysohnsLemma

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace RiemannMasullo

/-- For an integrable function, a compact subset of a measurable set carries all but an
arbitrarily small part of the integral of its norm, assuming inner regularity on finite sets. -/
theorem exists_isCompact_integral_norm_sdiff_lt
    {X E : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] {μ : Measure X} [μ.InnerRegularCompactLTTop] {f : X → E}
    (hf : Integrable f μ) {s : Set X} (hs : MeasurableSet s) {ε : ℝ} (hε : 0 < ε) :
    ∃ K ⊆ s, IsCompact K ∧ (∫ x in s \ K, ‖f x‖ ∂μ) < ε := by
  obtain ⟨t, ht, htZero, htFin⟩ := hf.aefinStronglyMeasurable.exists_set_sigmaFinite
  let : SigmaFinite (μ.restrict t) := htFin
  let A (n : ℕ) := s ∩ (spanningSets (μ.restrict t) n ∩ t)
  have hA n : MeasurableSet (A n) := hs.inter ((measurableSet_spanningSets _ _).inter ht)
  have hAμ n : μ (A n) < ∞ := by
    apply (measure_mono inter_subset_right).trans_lt
    rw [← Measure.restrict_apply (measurableSet_spanningSets _ _)]
    exact measure_spanningSets_lt_top _ _
  have hUnion : ⋃ n, A n = s ∩ t := by
    simp [A, ← iUnion_inter, ← inter_iUnion]
  have hMono : Monotone A := fun i j hij ↦
    inter_subset_inter_right _ (inter_subset_inter_left _ (monotone_spanningSets _ hij))
  have hLim := tendsto_setIntegral_of_monotone (f := fun x ↦ ‖f x‖) hA hMono hf.norm.integrableOn
  rw [hUnion] at hLim
  have hEq : (∫ x in s ∩ t, ‖f x‖ ∂μ) = ∫ x in s, ‖f x‖ ∂μ := by
    symm
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hs.nullMeasurableSet inter_subset_left ?_
    filter_upwards [ae_imp_of_ae_restrict htZero] with x hx hxS
    have hxT : x ∈ tᶜ := fun h ↦ hxS.2 ⟨hxS.1, h⟩
    simp [show f x = 0 from hx hxT]
  rw [hEq] at hLim
  have hNear : ∀ᶠ n in atTop, (∫ x in s, ‖f x‖ ∂μ) - ε / 2 < ∫ x in A n, ‖f x‖ ∂μ :=
    hLim (Ioi_mem_nhds (by linarith))
  obtain ⟨n, hn⟩ := hNear.exists
  obtain ⟨δ, hδ, hSmall⟩ := exists_pos_setLIntegral_lt_of_measure_lt hf.hasFiniteIntegral.ne
    (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
  obtain ⟨K, hKA, hK, hm⟩ := (hA n).exists_isCompact_sdiff_lt (hAμ n).ne hδ.ne'
  have hKmeas := hK.isClosed.measurableSet
  have hSmall' : (∫ x in A n \ K, ‖f x‖ ∂μ) < ε / 2 := by
    have h := hSmall (A n \ K) hm
    rw [integral_norm_eq_lintegral_eNorm hf.integrableOn.aestronglyMeasurable]
    exact (ENNReal.toReal_lt_toReal h.ne_top ENNReal.ofReal_ne_top).mpr h |>.trans_eq
      (ENNReal.toReal_ofReal (half_pos hε).le)
  have hKs : K ⊆ s := hKA.trans inter_subset_left
  have h₁ := setIntegral_sdiff hKmeas hf.norm.integrableOn hKA
  have h₂ := setIntegral_sdiff hKmeas hf.norm.integrableOn hKs
  exact ⟨K, hKs, hK, by
    change _ < (∫ x in A n, ‖f x‖ ∂μ) at hn
    linarith⟩

open scoped Pointwise in
/-- An integrable density for a regular measure vanishes if all its integrals against
a point-separating group of continuous circle-valued functions vanish. -/
theorem ae_eq_zero_of_integral_mul_circle_eq_zero
    {X D : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [Group D] {μ : Measure X} [μ.Regular] {f : X → ℂ}
    (e₀ : X → D →* Circle) (he₀ : ∀ d, Continuous (fun x ↦ e₀ x d))
    (hInj : Function.Injective e₀) (hf : Integrable f μ)
    (h : ∀ d, ∫ x, f x * (e₀ x d : ℂ) ∂μ = 0) : f =ᵐ[μ] 0 := by
  classical
  let B : Set (D → Circle) := {b | b 1 = 1 ∧ ∀ d d', b (d * d') = b d * b d'}
  have hB : IsClosed B := by
    rw [show B = {b : D → Circle | b 1 = 1} ∩
      ⋂ d, ⋂ d', {b : D → Circle | b (d * d') = b d * b d'} by ext; simp [B]]
    exact (isClosed_eq (continuous_apply 1) continuous_const).inter
      (isClosed_iInter fun d ↦ isClosed_iInter fun d' ↦
        isClosed_eq (continuous_apply (d * d')) ((continuous_apply d).mul (continuous_apply d')))
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  let e (x : X) : B := ⟨e₀ x, map_one _, map_mul _⟩
  have he : Continuous e := (continuous_pi he₀).subtype_mk _
  have heInj : Function.Injective e := fun _ _ hEq ↦
    hInj (DFunLike.coe_injective (congrArg Subtype.val hEq))
  let coord : D →* C(B, ℂ) :=
    { toFun := fun χ ↦ ⟨fun b ↦ (b.1 χ : ℂ),
        continuous_subtype_val.comp ((continuous_apply χ).comp continuous_subtype_val)⟩
      map_one' := ContinuousMap.ext fun b ↦ by
        change (b.1 1 : ℂ) = 1
        rw [b.2.1, Circle.coe_one]
      map_mul' χ ψ := ContinuousMap.ext fun b ↦ by
        change (b.1 (χ * ψ) : ℂ) = (b.1 χ : ℂ) * (b.1 ψ : ℂ)
        rw [b.2.2, Circle.coe_mul] }
  have hStar (χ : D) : star (coord χ) = coord χ⁻¹ := by
    ext b
    have hInv : b.1 χ⁻¹ = (b.1 χ)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← b.2.2, inv_mul_cancel, b.2.1]
    change star (b.1 χ : ℂ) = (b.1 χ⁻¹ : ℂ)
    rw [hInv, Circle.coe_inv_eq_conj, Complex.star_def]
  let A := StarAlgebra.adjoin ℂ (Set.range coord)
  have hSep : A.SeparatesPoints := by
    intro a b hab
    obtain ⟨χ, hχ⟩ : ∃ χ, a.1 χ ≠ b.1 χ := by
      by_contra! hEq
      exact hab (Subtype.ext (funext hEq))
    exact ⟨coord χ, ⟨coord χ, StarAlgebra.subset_adjoin _ _ (mem_range_self χ), rfl⟩,
      fun heq ↦ hχ (Circle.ext heq)⟩
  have hSpan : A.toSubalgebra.toSubmodule ≤ Submodule.span ℂ (Set.range coord) := by
    rw [StarAlgebra.adjoin_eq_span]
    apply Submodule.span_mono
    suffices Submonoid.closure (Set.range coord ∪ star (Set.range coord)) ≤
        MonoidHom.mrange coord from this
    apply Submonoid.closure_le.mpr
    rintro z (hMem | hMem)
    · exact hMem
    · obtain ⟨χ, hχ⟩ := Set.mem_star.mp hMem
      exact ⟨χ⁻¹, (hStar χ).symm.trans (by rw [hχ, star_star])⟩
  let test (u : C(B, ℂ)) (x : X) := f x * u (e x)
  have hBound (u : C(B, ℂ)) (x : X) : ‖test u x‖ ≤ ‖u‖ * ‖f x‖ := by
    change ‖f x * u (e x)‖ ≤ _
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm u _) (norm_nonneg _)
  have hInt (u : C(B, ℂ)) : Integrable (test u) μ :=
    hf.mul_bdd (u.continuous.comp he).aestronglyMeasurable
      (.of_forall fun x ↦ ContinuousMap.norm_coe_le_norm u (e x))
  let L : C(B, ℂ) →L[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := fun u ↦ ∫ x, test u x ∂μ
      map_add' := fun u v ↦ by
        simp only [test, ContinuousMap.add_apply, mul_add]
        exact integral_add (hInt u) (hInt v)
      map_smul' := fun c u ↦ by
        simp only [test, ContinuousMap.smul_apply, mul_smul_comm,
          RingHom.id_apply, integral_smul] }
    (∫ x, ‖f x‖ ∂μ) fun u ↦ by
      change ‖∫ x, test u x ∂μ‖ ≤ (∫ x, ‖f x‖ ∂μ) * ‖u‖
      rw [mul_comm, ← integral_const_mul]
      exact norm_integral_le_of_norm_le (hf.norm.const_mul ‖u‖) (.of_forall (hBound u))
  have hCoord (d : D) : L (coord d) = 0 := h d
  have hL (u : C(B, ℂ)) : L u = 0 := by
    have hDense := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hSep
    have hClosed : IsClosed {v | L v = 0} := isClosed_eq L.continuous continuous_const
    refine closure_minimal (s := (A : Set C(B, ℂ))) ?_ hClosed ?_
    · intro v hv
      have hKer : Submodule.span ℂ (Set.range coord) ≤ L.toLinearMap.ker :=
        Submodule.span_le.mpr (fun _ ⟨χ, hχ⟩ ↦ hχ ▸ hCoord χ)
      exact hKer (hSpan hv)
    · have hu : u ∈ A.topologicalClosure := hDense ▸ StarSubalgebra.mem_top
      exact hu
  apply hf.ae_eq_zero_of_forall_setIntegral_eq_zero
  intro s hs _
  have hNorm : ‖∫ x in s, f x ∂μ‖ ≤ 0 := by
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨K₁, hK₁s, hK₁, hTail₁⟩ := exists_isCompact_integral_norm_sdiff_lt hf hs (half_pos hε)
    obtain ⟨K₀, hK₀s, hK₀, hTail₀⟩ :=
      exists_isCompact_integral_norm_sdiff_lt hf hs.compl (half_pos hε)
    have hDisj : Disjoint (e '' K₀) (e '' K₁) := Set.disjoint_left.mpr <| by
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
      exact hK₀s hx (heInj heq ▸ hK₁s hy)
    obtain ⟨u, hu₀, hu₁, hu01⟩ := exists_continuous_zero_one_of_isClosed
      (hK₀.image he).isClosed (hK₁.image he).isClosed hDisj
    let v : C(B, ℂ) := ⟨fun b ↦ (u b : ℂ), Complex.continuous_ofReal.comp u.continuous⟩
    let q (x : X) := s.indicator f x - test v x
    have hEq : (∫ x, q x ∂μ) = ∫ x in s, f x ∂μ := by
      rw [show (∫ x, q x ∂μ) = (∫ x, s.indicator f x ∂μ) - L v from
        integral_sub (hf.indicator hs) (hInt v), hL, sub_zero, integral_indicator hs]
    rw [zero_add, ← hEq]
    let tail₁ := (s \ K₁).indicator (fun x ↦ ‖f x‖)
    let tail₀ := (sᶜ \ K₀).indicator (fun x ↦ ‖f x‖)
    have ht₁ := hs.diff hK₁.isClosed.measurableSet
    have ht₀ := hs.compl.diff hK₀.isClosed.measurableSet
    have hDom (x : X) : ‖q x‖ ≤ tail₁ x + tail₀ x := by
      have hBounds := hu01 (e x)
      by_cases hx : x ∈ s
      · by_cases hk : x ∈ K₁
        · simp [q, test, v, hx, hu₁ (mem_image_of_mem e hk), tail₁, tail₀, hk]
        have hDist : ‖1 - (u (e x) : ℂ)‖ ≤ 1 := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hBounds.2)]
          linarith [hBounds.1]
        have hTail : tail₁ x + tail₀ x = ‖f x‖ := by simp [tail₁, tail₀, hx, hk]
        rw [hTail]
        change ‖s.indicator f x - f x * (u (e x) : ℂ)‖ ≤ ‖f x‖
        calc
          _ = ‖f x * (1 - (u (e x) : ℂ))‖ := by rw [indicator_of_mem hx, mul_sub, mul_one]
          _ ≤ _ := by simpa only [norm_mul, mul_one] using
            mul_le_mul_of_nonneg_left hDist (norm_nonneg (f x))
      · by_cases hk : x ∈ K₀
        · simp [q, test, v, hx, hu₀ (mem_image_of_mem e hk), tail₁, tail₀, hk]
        have hNormU : ‖(u (e x) : ℂ)‖ ≤ 1 := by
          simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hBounds.1] using hBounds.2
        have hTail : tail₁ x + tail₀ x = ‖f x‖ := by simp [tail₁, tail₀, hx, hk]
        rw [hTail]
        change ‖s.indicator f x - f x * (u (e x) : ℂ)‖ ≤ ‖f x‖
        rw [indicator_of_notMem hx, zero_sub, norm_neg, norm_mul]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hNormU (norm_nonneg (f x))
    have ht₁Int : Integrable tail₁ μ := hf.norm.indicator ht₁
    have ht₀Int : Integrable tail₀ μ := hf.norm.indicator ht₀
    refine (norm_integral_le_of_norm_le (ht₁Int.add ht₀Int) (.of_forall hDom)).trans_lt ?_
    change (∫ x, tail₁ x + tail₀ x ∂μ) < ε
    rw [integral_add ht₁Int ht₀Int, show (∫ x, tail₁ x ∂μ) = _ from integral_indicator ht₁,
      show (∫ x, tail₀ x ∂μ) = _ from integral_indicator ht₀]
    linarith
  exact norm_eq_zero.mp (le_antisymm hNorm (norm_nonneg _))

end RiemannMasullo
