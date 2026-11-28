module

public import RiemannMasullo.Ch06_LocalGlobal.Sec2_RatActualThetaEulerLogL2
public import Mathlib.Analysis.Normed.Group.Tannery

/-! # Sharp Hilbert operator norm of the rational standard theta Euler cone

Long normalized intervals are almost invariant under each finite logarithmic
translation. Absolute summability controls the infinitely many cone terms. -/

public noncomputable section

namespace RiemannMasullo.RatFiniteEulerLogLpSeries

open MeasureTheory NumberField IsDedekindDomain RatUnramifiedThetaLattice RatFinitePositiveUnitRep Filter Set
open scoped Classical Topology symmDiff

local notation "LogL2" => Lp ℂ 2 (volume : Measure ℝ)

private def box (a b : ℝ) : LogL2 :=
  indicatorConstLp 2 (measurableSet_Ioc (a := a) (b := b)) (by simp [Real.volume_Ioc]) (1 : ℂ)

private theorem box_ae (a b : ℝ) : ⇑(box a b) =ᵐ[volume] (Ioc a b).indicator (fun _ ↦ (1 : ℂ)) :=
  indicatorConstLp_coeFn

private theorem translate_box (a b h : ℝ) : Measure.translateLp volume 2 h (box a b) = box (a-h) (b-h) := by
  apply Lp.ext
  filter_upwards [Measure.coeFn_translateLp h (box a b), (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp (box_ae a b), box_ae (a-h) (b-h)] with x hx hy hz
  simp only [Function.comp_apply] at hx hy
  rw [hx, hy, hz]
  have hi : x + h ∈ Ioc a b ↔ x ∈ Ioc (a-h) (b-h) := by simp only [mem_Ioc]; constructor <;> rintro ⟨_, _⟩ <;> constructor <;> linarith
  by_cases hm : x + h ∈ Ioc a b
  · simp [hm, hi.mp hm]
  · simp [hm, mt hi.mpr hm]

private theorem box_diff_bound (R h : ℝ) : ‖Measure.translateLp volume 2 h (box 0 R) - box 0 R‖ ≤ Real.sqrt (4 * |h|) := by
  rw [translate_box, ← dist_eq_norm, box, box, dist_indicatorConstLp_eq_norm, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [norm_one, one_mul, ENNReal.toReal_ofNat, ← Real.sqrt_eq_rpow]
  apply Real.sqrt_le_sqrt
  let A := Ioc (-|h|) |h|
  let B := Ioc (R-|h|) (R+|h|)
  have hs : Ioc (0-h) (R-h) ∆ Ioc 0 R ⊆ A ∪ B := by
    intro x hx
    simp only [A, B, mem_union, mem_Ioc, mem_symmDiff, not_and_or, not_lt, not_le] at *
    have := neg_abs_le h
    have := le_abs_self h
    rcases hx with ⟨⟨_, _⟩, h' | h'⟩ | ⟨⟨_, _⟩, h' | h'⟩ <;> first | left; constructor <;> linarith | right; constructor <;> linarith
  refine (measureReal_mono (μ := volume) hs (by apply ne_of_lt; apply measure_union_lt_top <;> simp [A, B, Real.volume_Ioc])).trans ((measureReal_union_le A B).trans ?_)
  dsimp only [A, B]
  rw [Real.volume_real_Ioc_of_le (by linarith [abs_nonneg h]),
    Real.volume_real_Ioc_of_le (by linarith [abs_nonneg h])]
  ring_nf
  exact le_rfl

private def unitBox (R : ℝ) : LogL2 := (Real.sqrt R)⁻¹ • box 0 R

private theorem norm_unitBox {R : ℝ} (hR : 0 < R) : ‖unitBox R‖ = 1 := by
  rw [unitBox, norm_smul, box, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [norm_one, one_mul, ENNReal.toReal_ofNat, Real.volume_real_Ioc_of_le hR.le,
    sub_zero, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg R)]
  rw [← Real.sqrt_eq_rpow, inv_mul_cancel₀ (Real.sqrt_pos.mpr hR).ne']

private theorem unitBox_diff (h : ℝ) : Tendsto (fun R ↦ ‖Measure.translateLp volume 2 h (unitBox R) - unitBox R‖) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    (g := fun R : ℝ ↦ Real.sqrt (4 * |h|) / Real.sqrt R)
  · apply Eventually.of_forall
    intro R
    rw [unitBox, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), div_eq_inv_mul]
    gcongr
    exact box_diff_bound R h
  · exact tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop

/-- Sharp lower bound from almost invariant normalized intervals in the logarithmic chart. -/
theorem coneMass_le_norm_chartOperator (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    (∑' n : S → ℕ, (Real.sqrt (latticeRadius n))⁻¹) ≤ ‖chartOperator S‖ := by
  let w (n : S → ℕ) : ℝ := (Real.sqrt (latticeRadius n))⁻¹
  let U (n : S → ℕ) := Measure.translateLp (F := ℂ) volume 2 (Real.log (latticeRadius n))
  let e (R : ℝ) (n : S → ℕ) := w n * ‖U n (unitBox R) - unitBox R‖
  have hw (n) : 0 ≤ w n := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hs : Summable w := weight_summable S
  have he : Tendsto (fun R ↦ ∑' n, e R n) atTop (𝓝 0) := by
    have ht := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := e) (g := fun _ ↦ (0 : ℝ)) (hs.mul_right 2)
    suffices H : Tendsto (fun R ↦ ∑' n, e R n) atTop (𝓝 (∑' _ : S → ℕ, (0 : ℝ))) by simpa using H
    apply ht
    · intro n
      simpa [e, U] using (unitBox_diff (Real.log (latticeRadius n))).const_mul (w n)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR n
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw n) (norm_nonneg _))]
      apply mul_le_mul_of_nonneg_left _ (hw n)
      simpa only [LinearIsometryEquiv.norm_map, norm_unitBox hR, one_add_one_eq_two] using
        (norm_sub_le (U n (unitBox R)) (unitBox R))
  have hb : ∀ᶠ R : ℝ in atTop, (∑' n, w n) ≤ ‖chartOperator S‖ + ∑' n, e R n := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    let P := unitBox R
    have hp : ‖P‖ = 1 := norm_unitBox hR
    have hc (n) : coneTerm P n = w n • U n P := by
      rw [coneTerm_apply]
      apply Lp.ext
      filter_upwards [Lp.coeFn_smul ((Real.sqrt (latticeRadius n) : ℂ)⁻¹) (U n P),
        Lp.coeFn_smul (w n) (U n P)] with t h₁ h₂
      change ((Real.sqrt (latticeRadius n) : ℂ)⁻¹ • U n P) t = (w n • U n P) t
      rw [h₁, h₂]
      simp only [Pi.smul_apply, w, ← Complex.ofReal_inv, Complex.coe_smul]
    have hd := ((chartSeries_hasSum S P).sub (hs.hasSum.smul_const P))
    have hd' : HasSum (fun n ↦ w n • (U n P - P)) (chartOperator S P - (∑' n, w n) • P) := by simpa only [Pi.sub_apply, hc, smul_sub, chartOperator_apply] using hd
    have heR : Summable (e R) := Summable.of_nonneg_of_le
      (fun n ↦ mul_nonneg (hw n) (norm_nonneg _)) (fun n ↦ mul_le_mul_of_nonneg_left
        (by simpa only [LinearIsometryEquiv.norm_map, hp, one_add_one_eq_two] using norm_sub_le (U n P) P)
        (hw n)) (hs.mul_right 2)
    have hn : ‖chartOperator S P - (∑' n, w n) • P‖ ≤ ∑' n, e R n := by
      rw [← hd'.tsum_eq]
      have hh : Summable (fun n ↦ ‖w n • (U n P - P)‖) := by
        simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw _), e, P] using heR
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw _), e, P] using norm_tsum_le_tsum_norm hh
    have ht := norm_sub_le (chartOperator S P) (chartOperator S P - (∑' n, w n) • P)
    rw [sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg hw), hp, mul_one] at ht
    exact ht.trans (add_le_add (by simpa [hp] using (chartOperator S).le_opNorm P) hn)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds (by simpa using he.const_add ‖chartOperator S‖) hb

/-- The Euler product gives the exact norm of the finite-place logarithmic chart operator. -/
theorem norm_chartOperator_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ‖chartOperator S‖ = chartBound S := by
  apply le_antisymm (norm_chartOperator_le S)
  rw [← coneMass_eq]
  exact coneMass_le_norm_chartOperator S

end RiemannMasullo.RatFiniteEulerLogLpSeries
