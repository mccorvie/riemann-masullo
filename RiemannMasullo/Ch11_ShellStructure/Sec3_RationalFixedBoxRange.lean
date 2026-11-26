module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBox
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! # The period-difference range in the completed rational fixed box

Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496. The rational trivial angular,
unweighted Hilbert space retains the half twist in its actual translations.
The forward shift by one prime period, minus the identity, has closed range
on the preceding fixed box. Its range is exactly the next stage, and every
preimage in the preceding box has an explicit norm bound. No cardinal basis
or arbitrary-width assertion is used. -/

public noncomputable section

open Filter Function MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology

namespace RiemannMasullo.RationalPacket

/-- Translation on logarithmic coordinates, including the half-density factor. -/
def halfShift (h : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] (Lp ℂ 2 (volume : Measure ℝ)) :=
  (Real.exp (h / 2) : ℂ) •
    (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ _
      (measurePreserving_add_right volume (-h))).toContinuousLinearMap

theorem halfShift_ae (h : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    ⇑(halfShift h u) =ᵐ[volume] fun x ↦ (Real.exp (h / 2) : ℂ) * u (x - h) := by
  let t := Lp.compMeasurePreserving _ (measurePreserving_add_right volume (-h)) u
  change ⇑((Real.exp (h / 2) : ℂ) • t) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_smul (Real.exp (h / 2) : ℂ) t,
    Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume (-h))] with x hs ht
  change t x = u (x + -h) at ht
  change _ = (Real.exp (h / 2) : ℂ) * t x at hs
  simpa only [ht, sub_eq_add_neg] using hs

@[simp] theorem norm_halfShift (h : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖halfShift h u‖ = Real.exp (h / 2) * ‖u‖ := by
  change ‖(Real.exp (h / 2) : ℂ) • Lp.compMeasurePreserving _
    (measurePreserving_add_right volume (-h)) u‖ = _
  rw [norm_smul, Lp.norm_compMeasurePreserving, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem halfShift_add (h k : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    halfShift (h + k) u = halfShift h (halfShift k u) := by
  apply Lp.ext
  filter_upwards [halfShift_ae (h + k) u, halfShift_ae h (halfShift k u),
    (measurePreserving_add_right volume (-h)).quasiMeasurePreserving.ae_eq_comp
      (halfShift_ae k u)] with x ha hb hc
  change halfShift k u (x - h) = (Real.exp (k / 2) : ℂ) * u (x - h - k) at hc
  rw [ha, hb, hc, add_div, Real.exp_add, Complex.ofReal_mul, mul_assoc, sub_add_eq_sub_sub]

@[simp] theorem halfShift_zero (u : Lp ℂ 2 (volume : Measure ℝ)) : halfShift 0 u = u := by
  apply Lp.ext
  simpa using halfShift_ae 0 u

/-- Strong continuity of the half-shift group. -/
theorem continuous_halfShift (u : Lp ℂ 2 (volume : Measure ℝ)) : Continuous fun h ↦ halfShift h u := by
  let g := (ContinuousMap.curry
    (⟨fun q : ℝ × ℝ ↦ q.2 + -q.1, continuous_snd.add continuous_fst.neg⟩ : C(ℝ × ℝ, ℝ)))
  have ht := continuous_const.compMeasurePreservingLp (f := fun _ : ℝ ↦ u) g.continuous
    (fun h ↦ measurePreserving_add_right volume (-h)) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have hw : Continuous fun h : ℝ ↦ (Real.exp (h / 2) : ℂ) := by fun_prop
  exact hw.smul ht

/-- The next stage is the image of the difference by one actual logarithmic period. -/
def stagePeriodDifference (p : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] (Lp ℂ 2 (volume : Measure ℝ)) :=
  halfShift (Real.log p) - ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure ℝ))

/-- Pointwise evaluation of the period difference. -/
theorem stagePeriodDifference_apply (p : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    stagePeriodDifference p u = halfShift (Real.log p) u - u := by
  simp only [stagePeriodDifference, sub_apply, ContinuousLinearMap.id_apply]

private theorem stagePeriodDifference_ae (T : Finset ℕ) {p : ℕ}
    (hp : 0 < p) (hmem : p ∉ T) {F : Lp ℂ 2 (volume : Measure ℝ)} {f : 𝓢(ℝ, ℂ)}
    (hF : (F : ℝ → ℂ) =ᵐ[volume] stage T f) :
    (stagePeriodDifference p F : ℝ → ℂ) =ᵐ[volume]
      stage (insert p T) (dilate ((p : ℝ)⁻¹) (inv_pos.mpr (by exact_mod_cast hp)) f) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  let g := dilate ((p : ℝ)⁻¹) (inv_pos.mpr hpR) f
  let L := Real.log (p : ℝ)
  have hg (x : ℝ) : stage T g x = (Real.exp (L/2) : ℂ) * stage T f (x-L) := by
    dsimp only [g]
    rw [stage_dilate_real, Real.log_inv]
    simp only [neg_neg, L, sub_eq_add_neg]
  have hback (x : ℝ) : (Real.exp (-L/2) : ℂ) * stage T g (x+L) = stage T f x := by
    rw [hg, add_sub_cancel_right, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    simp [neg_div]
  have htrans := (measurePreserving_add_right volume (-L)).quasiMeasurePreserving.ae_eq_comp hF
  change (halfShift L F - F : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume] stage (insert p T) g
  filter_upwards [Lp.coeFn_sub (halfShift L F) F, halfShift_ae L F, htrans, hF] with x hsub hhalf htx hx
  rw [hsub, Pi.sub_apply, hhalf, hx, stage_insert T hp hmem g x]
  change (Real.exp (L/2) : ℂ) * F (x-L) - stage T f x = _
  rw [show F (x-L) = stage T f (x-L) by simpa only [Function.comp_apply, sub_eq_add_neg] using htx,
    ← hg, ← hback x]

/-- Equality of the actual Schwartz generators, before taking either closure. -/
theorem stagePeriodDifference_image_generators {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q) {p : ℕ} (hp : 1 < p) (hmem : p ∉ T) :
    stagePeriodDifference p '' stageGenerators X T = stageGenerators X (insert p T) := by
  have hpN : 0 < p := zero_lt_one.trans hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpN
  apply le_antisymm
  · rintro G ⟨F, hFgen, rfl⟩
    obtain ⟨f, hf0, hfF0, hfb, hF⟩ := mem_stageGenerators_iff.mp hFgen
    apply mem_stageGenerators_iff.mpr
    let g := dilate ((p : ℝ)⁻¹) (inv_pos.mpr hpR) f
    refine ⟨g, by simp [g, hf0], by simp [g, fourier_dilate, hfF0], ?_,
      stagePeriodDifference_ae T hpN hmem hF⟩
    intro r hr
    dsimp only [g]
    rw [fourier_dilate, hfb, smul_zero]
    rw [abs_div, abs_of_pos (inv_pos.mpr hpR), div_inv_eq_mul]
    rw [Finset.prod_insert hmem, mul_comm (p : ℝ), ← div_div] at hr
    exact (div_lt_iff₀ hpR).mp hr
  · intro G hGgen
    obtain ⟨f, hf0, hfF0, hfb, hG⟩ := mem_stageGenerators_iff.mp hGgen
    let g := dilate (p : ℝ) hpR f
    have hg0 : g 0 = 0 := by simp [g, hf0]
    have hgF0 : (𝓕 g) 0 = 0 := by simp [g, fourier_dilate, hfF0]
    have hgb (r : ℝ) (hr : X / (∏ q ∈ T, (q : ℝ)) < |r|) : (𝓕 g) r = 0 := by
      dsimp only [g]
      rw [fourier_dilate, hfb, smul_zero]
      rw [Finset.prod_insert hmem, mul_comm (p : ℝ), ← div_div, abs_div, abs_of_pos hpR]
      exact div_lt_div_of_pos_right hr hpR
    have hgLp := (stage_memLp_and_dampedStage_integrable hX T hT hg0 hgF0 hgb).1
    let F := hgLp.toLp (stage T g)
    have hF : (F : ℝ → ℂ) =ᵐ[volume] stage T g := hgLp.coeFn_toLp
    refine ⟨F, mem_stageGenerators_iff.mpr ⟨g, hg0, hgF0, hgb, hF⟩, Lp.ext ?_⟩
    have hgg : dilate ((p : ℝ)⁻¹) (inv_pos.mpr hpR) g = f := by
      ext x
      simp only [g, dilate_apply]
      rw [← mul_assoc, mul_inv_cancel₀ hpR.ne', one_mul]
    have H := stagePeriodDifference_ae T hpN hmem hF
    rw [hgg] at H
    exact H.trans hG.symm

/-- The inverse of the period difference costs at most `(exp(log(p)/2)-1)⁻¹`. -/
theorem mul_norm_le_stagePeriodDifference (p : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (Real.exp (Real.log p / 2) - 1) * ‖u‖ ≤ ‖stagePeriodDifference p u‖ := by
  have h := norm_add_le (stagePeriodDifference p u) u
  rw [show stagePeriodDifference p u + u = halfShift (Real.log p) u by simp [stagePeriodDifference],
    norm_halfShift] at h
  rw [sub_mul, one_mul]
  linarith

/-- The actual closed Hilbert stage for the next prime is the range, without a
further closure, of the half-shift period difference on the previous closed stage. -/
theorem range_stagePeriodDifference_closedStage {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q) {p : ℕ} (hp : 1 < p) (hmem : p ∉ T)
    (hTp : ∀ q ∈ insert p T, 1 ≤ q) :
    range ((stagePeriodDifference p).comp (closedStageSubmodule X T hT).toSubmodule.subtypeL) =
      (closedStageSubmodule X (insert p T) hTp : Set (Lp ℂ 2 (volume : Measure ℝ))) := by
  let E := closedStageSubmodule X T hT
  let A : E →L[ℂ] (Lp ℂ 2 (volume : Measure ℝ)) := (stagePeriodDifference p).comp E.toSubmodule.subtypeL
  let c := Real.exp (Real.log (p : ℝ) / 2) - 1
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hc : 0 < c := sub_pos.mpr (Real.one_lt_exp_iff.mpr (half_pos (Real.log_pos hpR)))
  have hA : AntilipschitzWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ A :=
    A.antilipschitz_of_bound fun u ↦ by
      change ‖(u : Lp ℂ 2 (volume : Measure ℝ))‖ ≤ c⁻¹ * ‖stagePeriodDifference p u‖
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using (mul_norm_le_stagePeriodDifference p u))
  have hi := stagePeriodDifference_image_generators hX T hT hp hmem
  apply le_antisymm
  · rintro y ⟨u, rfl⟩
    apply (mem_closedStageSubmodule_iff X (insert p T) hTp _).mpr
    have hm : MapsTo (stagePeriodDifference p) (stageGenerators X T) (stageGenerators X (insert p T)) :=
      fun x hx ↦ hi ▸ mem_image_of_mem _ hx
    exact hm.closure (stagePeriodDifference p).continuous
      ((mem_closedStageSubmodule_iff X T hT _).mp u.property)
  · intro y hy
    apply closure_minimal _ (hA.isClosed_range A.uniformContinuous)
      ((mem_closedStageSubmodule_iff X (insert p T) hTp y).mp hy)
    rw [← hi]
    rintro z ⟨x, hx, rfl⟩
    exact ⟨⟨x, (mem_closedStageSubmodule_iff X T hT x).mpr (subset_closure hx)⟩, rfl⟩

/-- Every actual next-stage vector has a unique previous-stage period
difference preimage, with an explicit bound in the unweighted Hilbert norm. -/
theorem existsUnique_stagePeriodDifference_preimage {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q) {p : ℕ} (hp : 1 < p) (hmem : p ∉ T)
    (hTp : ∀ q ∈ insert p T, 1 ≤ q) {v : Lp ℂ 2 (volume : Measure ℝ)}
    (hv : v ∈ closedStageSubmodule X (insert p T) hTp) :
    ∃! u : Lp ℂ 2 (volume : Measure ℝ), u ∈ closedStageSubmodule X T hT ∧ stagePeriodDifference p u = v ∧
      ‖u‖ ≤ ‖v‖ / (Real.exp (Real.log (p : ℝ) / 2) - 1) := by
  have hh := range_stagePeriodDifference_closedStage hX T hT hp hmem hTp
  have hvr : v ∈ range ((stagePeriodDifference p).comp
      (closedStageSubmodule X T hT).toSubmodule.subtypeL) := hh.symm ▸ hv
  obtain ⟨u, hu⟩ := hvr
  change stagePeriodDifference p (u : Lp ℂ 2 (volume : Measure ℝ)) = v at hu
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hc : 0 < Real.exp (Real.log (p : ℝ) / 2) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (half_pos (Real.log_pos hpR)))
  have hbound := mul_norm_le_stagePeriodDifference p (u : Lp ℂ 2 (volume : Measure ℝ))
  rw [hu, mul_comm] at hbound
  refine ⟨(u : Lp ℂ 2 (volume : Measure ℝ)), ⟨u.property, hu, (le_div_iff₀ hc).mpr hbound⟩, ?_⟩
  rintro w ⟨-, hw, -⟩
  have hz : stagePeriodDifference p (w - (u : Lp ℂ 2 (volume : Measure ℝ))) = 0 := by
    rw [map_sub, hw, hu, sub_self]
  have hb := mul_norm_le_stagePeriodDifference p (w - (u : Lp ℂ 2 (volume : Measure ℝ)))
  rw [hz, norm_zero] at hb
  have hnot : ¬ 0 < ‖w - (u : Lp ℂ 2 (volume : Measure ℝ))‖ := fun h ↦ (not_lt_of_ge hb) (mul_pos hc h)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (le_of_not_gt hnot) (norm_nonneg _)))

/-- Forward translation dilates the Fourier witness by `exp (-h)`, so its
band shrinks and the translated generator still belongs to the same box. -/
theorem halfShift_mem_stageGenerators {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q) {h : ℝ} (hh : 0 ≤ h)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ stageGenerators X T) : halfShift h F ∈ stageGenerators X T := by
  obtain ⟨f, hf0, hfF0, hband, hrep⟩ := mem_stageGenerators_iff.mp hF
  let r := Real.exp (-h)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hh)
  let U := X / (∏ q ∈ T, (q : ℝ))
  have hU : 0 < U := div_pos hX (Finset.prod_pos fun q hq ↦ by
    exact_mod_cast zero_lt_one.trans_le (hT q hq))
  let g := dilate r hr f
  have hshrink (y : ℝ) (hy : U * r < |y|) : (𝓕 g) y = 0 := by
    dsimp only [g]
    rw [fourier_dilate, hband, smul_zero]
    rw [abs_div, abs_of_pos hr]
    exact (lt_div_iff₀ hr).mpr hy
  apply mem_stageGenerators_iff.mpr
  refine ⟨g, by simp [g, hf0], by simp [g, fourier_dilate, hfF0],
    fun y hy ↦ hshrink y ((mul_le_of_le_one_right hU.le hr1).trans_lt hy), ?_⟩
  have ht := (measurePreserving_add_right volume (-h)).quasiMeasurePreserving.ae_eq_comp hrep
  filter_upwards [halfShift_ae h F, ht] with x hx htx
  change F (x - h) = stage T f (x - h) at htx
  rw [hx, htx]
  simp only [g, stage_dilate_real, r, Real.log_exp, neg_neg, sub_eq_add_neg]

/-- Forward half-shifts preserve the actual completed fixed-box stage. -/
theorem halfShift_mem_closedStage {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q) {h : ℝ} (hh : 0 ≤ h)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ closedStageSubmodule X T hT) :
    halfShift h F ∈ closedStageSubmodule X T hT := by
  have hm : MapsTo (halfShift h) (stageGenerators X T) (stageGenerators X T) :=
    fun _ hu ↦ halfShift_mem_stageGenerators hX T hT hh hu
  exact (mem_closedStageSubmodule_iff X T hT _).mpr
    (hm.closure (halfShift h).continuous ((mem_closedStageSubmodule_iff X T hT _).mp hF))

/-- A forward half-shift on the closed box acts on its raw Mellin sample by the
ordinary Fourier translation character. -/
theorem mellinSample_halfShift {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q) {h : ℝ} (hh : 0 ≤ h)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ closedStageSubmodule X T hT)
    (ξ : ℝ) :
    mellinSample (-Real.log X) ξ (halfShift h F) =
      (𝐞 (-h * ξ) : ℂ) * mellinSample (-Real.log X) ξ F := by
  rw [mellinSample_eq_fourier_damped _ _ _
      (closedStage_ae_zero_before_box hX T hT (halfShift_mem_closedStage hX T hT hh hF)),
    mellinSample_eq_fourier_damped _ _ _ (closedStage_ae_zero_before_box hX T hT hF)]
  let f (x : ℝ) := (Real.exp (-x / 2) : ℂ) * F x
  change 𝓕 (fun x : ℝ ↦ (Real.exp (-x / 2) : ℂ) * halfShift h F x) ξ =
    (𝐞 (-h * ξ) : ℂ) * 𝓕 f ξ
  trans 𝓕 (f ∘ fun x ↦ x + -h) ξ
  · apply Real.fourier_congr_ae
    filter_upwards [halfShift_ae h F] with x hx
    rw [hx]
    change (Real.exp (-x / 2) : ℂ) * ((Real.exp (h / 2) : ℂ) * F (x - h)) =
      (Real.exp (-(x + -h) / 2) : ℂ) * F (x + -h)
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, sub_eq_add_neg]
    congr 3
    ring
  · convert congrFun (Fourier.fourierIntegral_comp_add_right 𝐞 volume f (-h)) ξ using 1 <;>
      simp [Real.fourier_eq, Fourier.fourierIntegral, VectorFourier.fourierIntegral,
        Circle.smul_def, mul_comm ξ]

end RiemannMasullo.RationalPacket
