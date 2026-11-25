module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
public import RiemannMasullo.ForMathlib.Analysis.Fourier.PolarLaplaceProbe
public import RiemannMasullo.Ch10_TraceSpectral.Sec2_PrincipalLostJets
import Mathlib.Tactic

/-! # Off-center growth on the principal theta row

The compact radial probes below have closed support strictly above norm one under
forward translation. Their principal-row Mellin values are normalized using the
actual mass of the norm-one classes.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo
set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "principalMellin(" K ", " φ ", " z ")" =>
  modulatedFourierMellin (continuousIdeleClassNorm K) univ
    (⟨isProperMap_ideleClassNorm K, ideleClassNorm_ne_one (F := K)⟩ : IsModulation _)
    (ideleClassTamagawaMeasure K) (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 K) K)).val
    (ideleClassNormTwist (F := K) 1 z)
local notation "classVolume" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)

private theorem lostJet_classVolume_ne_zero : classVolume ≠ 0 := by
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  apply Complex.ofReal_ne_zero.mpr
  apply ENNReal.toReal_ne_zero.mpr
  exact ⟨(isOpen_univ.measure_pos _ univ_nonempty).ne', isCompact_univ.measure_ne_top⟩

/-- Smooth translates in log norm have the exact principal-row Mellin multiplier
`exp (z*y)` times the bilateral Laplace transform of the single base profile. The
factor dividing the test is the mass of the genuine norm-one Tamagawa measure. -/
theorem exists_normalized_radial_translates (H : ℝ → ℂ) (hs : ContDiff ℝ (∞) H)
    (hc : HasCompactSupport H) :
    ∃ φ : ℝ → BruhatCompactSupport C𝔽,
      (∀ y x, (φ y).val x = classVolume⁻¹ * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y)) ∧
      ∀ (y : ℝ) (z : ℂ), principalMellin(F, φ y, z) = Complex.exp (z * y) * bilateralLaplace H z := by
  let g := fun x : ℝ ↦ classVolume⁻¹ * H x
  have hg : ContDiff ℝ (∞) g := contDiff_const.mul hs
  have hgc : HasCompactSupport g := hc.mul_left
  choose φ hφ using fun y : ℝ ↦ exists_normTest (F := F) (fun x ↦ g (x - y))
    (hg.comp (contDiff_id.sub contDiff_const)) (hgc.comp_homeomorph (Homeomorph.subRight y))
  refine ⟨φ, hφ, ?_⟩
  intro y z
  rw [normTest_mellin (F := F) (fun t : ℝ ↦ g (t - y))
    (hg.continuous.comp (continuous_id.sub continuous_const)) _ (hφ y) 1 z, ite_eq_left (by simp)]
  change classVolume * (∫ t : ℝ≥0ˣ, g (Real.log ((t : ℝ≥0) : ℝ) - y) * (1 : ℂ) *
    (((t : ℝ≥0) : ℝ) : ℂ) ^ z ∂positiveRealHaar) = _
  rw [grh_shift_integral g hg.continuous (fun _ ↦ (1 : ℂ)) (fun _ ↦ rfl) y z]
  have hL : (∫ x : ℝ, g x * Complex.exp (z * x)) = classVolume⁻¹ * bilateralLaplace H z := by
    rw [bilateralLaplace, ← integral_const_mul]
    congr 1
    funext x
    dsimp only [g]
    ring
  rw [hL]
  field_simp [lostJet_classVolume_ne_zero (F := F)]

/-- A forward translate of a radial profile whose closed support is positive
has closed support in the idèle classes of norm strictly greater than one. -/
private theorem supported_above_one_of_radial_translate (H : ℝ → ℂ) (hH : tsupport H ⊆ Ioi 0)
    (y : ℝ) (hy : 0 ≤ y) (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ x, φ.val x = classVolume⁻¹ * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y)) :
    tsupport φ.val ⊆ {x | 1 < ((ideleClassNorm F x : ℝ≥0) : ℝ)} := by
  let L := fun x : C𝔽 ↦ Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y
  have hnorm : Continuous (fun x : C𝔽 ↦ ((ideleClassNorm F x : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hpos (x : C𝔽) : 0 < ((ideleClassNorm F x : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (ideleClassNorm F x).ne_zero)
  have hL : Continuous L := (hnorm.log (fun x ↦ (hpos x).ne')).sub continuous_const
  intro x hx
  have he : φ.val = (fun _ : C𝔽 ↦ classVolume⁻¹) * (H ∘ L) := funext hφ
  rw [he] at hx
  have hx' : x ∈ tsupport (H ∘ L) := tsupport_mul_subset_right hx
  have hlog := hH (tsupport_comp_subset_preimage (f := L) H hL hx')
  change 0 < Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y at hlog
  exact (Real.log_pos_iff (show 0 ≤ ((ideleClassNorm F x : ℝ≥0) : ℝ) by positivity)).mp (by linarith)

/-- Paper: §12.3, p. 514, and (10.3.2.3), p. 454.
One fixed real profile gives genuine compact idèle-class tests supported strictly
above norm one. Every translate kills the prescribed real moments; the other
principal-row coefficients remain nonzero throughout the closed strip.

Deviation: the finite set may include both the physical poles `±1/2` and
the two poles `-a, 1-a` in coordinates about a chosen center `a`. -/
theorem exists_principal_polar_free_translates {B : ℝ} (hB : 0 < B) (P : Finset ℝ) :
    ∃ (H : ℝ → ℝ) (φ : ℝ → BruhatCompactSupport C𝔽),
      ContDiff ℝ (∞) H ∧ HasCompactSupport H ∧ tsupport H ⊆ Ioi 0 ∧
      (∀ y x, (φ y).val x = classVolume⁻¹ * (H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y) : ℂ)) ∧
      (∀ y : ℝ, 0 ≤ y → tsupport (φ y).val ⊆ {x | 1 < ((ideleClassNorm F x : ℝ≥0) : ℝ)}) ∧
      (∀ (y : ℝ) (z : ℂ), principalMellin(F, φ y, z) =
        Complex.exp (z * y) * bilateralLaplace (fun x ↦ (H x : ℂ)) z) ∧
      (∀ (y p : ℝ), p ∈ P → principalMellin(F, φ y, (p : ℂ)) = 0) ∧
      ∀ (y : ℝ) (z : ℂ), |z.re| ≤ B → (∀ p ∈ P, z ≠ (p : ℂ)) → principalMellin(F, φ y, z) ≠ 0 := by
  obtain ⟨H, hs, hc, hpos, hzero, hne⟩ := exists_compact_positive_support_laplace_polar_filter hB P
  let h := fun t : ℝ ↦ (H t : ℂ)
  have hhc : HasCompactSupport h := hc.comp_left Complex.ofReal_zero
  have hhs : ContDiff ℝ (∞) h := Complex.ofRealCLM.contDiff.comp hs
  have hsupport : tsupport h ⊆ Ioi 0 := (tsupport_comp_subset (g := Complex.ofReal) rfl H).trans hpos
  obtain ⟨φ, hφ, hM⟩ := exists_normalized_radial_translates (F := F) h hhs hhc
  refine ⟨H, φ, hs, hc, hpos, hφ, ?_, hM, ?_, ?_⟩
  · intro y hy
    exact supported_above_one_of_radial_translate h hsupport y hy (φ y) (hφ y)
  · intro y p hp
    rw [hM, hzero p hp, mul_zero]
  · intro y z hz hp
    rw [hM]
    exact mul_ne_zero (Complex.exp_ne_zero _) (hne z hz hp)

open PrincipalLostJets

/-- Paper: §12.3, p. 514, and (10.3.2.3), p. 454.
One fixed compact log profile gives actual above-one idèle-class tests. Any
lost principal zero outside the prescribed polar moments forces the signed
wide-minus-narrow Mellin sum to exceed every slower exponential arbitrarily late.
The center is fixed during translation and the spectral coordinate is `w = ρ - a`. -/
theorem exists_principal_lostJet_mellin_growth (a α β s : ℝ) (hα : 0 ≤ α) (hab : α < β)
    (P : Finset ℝ) :
    ∃ (H : ℝ → ℝ) (φ : ℝ → BruhatCompactSupport C𝔽),
      ContDiff ℝ (∞) H ∧ HasCompactSupport H ∧ tsupport H ⊆ Ioi 0 ∧
      (∀ y x, (φ y).val x =
        classVolume⁻¹ * (H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y) : ℂ)) ∧
      (∀ y : ℝ, 0 ≤ y → tsupport (φ y).val ⊆ {x | 1 < ((ideleClassNorm F x : ℝ≥0) : ℝ)}) ∧
      (∀ (y p : ℝ), p ∈ P → principalMellin(F, φ y, (p : ℂ)) = 0) ∧
      (∀ y : ℝ, Summable (fun j : principalSites F a β ↦
        ((retainedJets F β s j : ℂ) - retainedJets F α s j) * principalMellin(F, φ y, j.val))) ∧
      ∀ (i : principalSites F a β), 0 < jetLoss F α s i → (∀ p ∈ P, i.val ≠ (p : ℂ)) →
        ∀ (c : ℝ), c < i.val.re → ∀ C : ℝ, ∃ᶠ y : ℝ in atTop,
          C * Real.exp (c * y) < ‖∑' j : principalSites F a β,
            ((retainedJets F β s j : ℂ) - retainedJets F α s j) * principalMellin(F, φ y, j.val)‖ := by
  obtain ⟨H, φ, hs, hc, hpos, hφ, hsupp, hM, hzero, hne⟩ :=
    exists_principal_polar_free_translates (F := F) (hα.trans_lt hab) P
  let h := fun x ↦ (H x : ℂ)
  have hhs : ContDiff ℝ (∞) h := Complex.ofRealCLM.contDiff.comp hs
  have hhc : HasCompactSupport h := hc.comp_left Complex.ofReal_zero
  have hterm (y : ℝ) (j : principalSites F a β) :
      ((retainedJets F β s j : ℂ) - retainedJets F α s j) * principalMellin(F, φ y, j.val) =
        coefficient F α s (bilateralLaplace h) j * Complex.exp (j.val * y) := by
    rw [← cast_jetLoss F hα hab j, hM]
    change _ = ((jetLoss F α s j : ℂ) * bilateralLaplace h j.val) * _
    ring
  refine ⟨H, φ, hs, hc, hpos, hφ, hsupp, hzero, ?_, ?_⟩
  · intro y
    have hb := coefficient_summable F a α β s h hhs hhc
    apply (hb.norm.mul_right (Real.exp (β * |y|))).of_norm_bounded
    intro j
    rw [hterm, norm_mul, Complex.norm_exp]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact ((le_abs_self _).trans (abs_mul _ _).le).trans
      (mul_le_mul_of_nonneg_right j.property.1 (abs_nonneg y))
  · intro i hi hp c hci C
    have hK : bilateralLaplace h i.val ≠ 0 := by
      simpa only [hM, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] using
        hne 0 i.val i.property.1 hp
    refine (frequently_exp_lt_principal_lostJet_of_compact F a α h hhs hhc hi hK hci C).mono ?_
    intro y hy
    simpa only [hterm] using hy

/-- Paper: §12.3, p. 514. With center zero, a nonreal principal zero on the
critical line falls strictly between widths `1/4` and `3/4`. Its full order is lost,
so one family killing all four polar moments detects growth at every rate below
`1/2`. The same family works simultaneously for every such zero. -/
theorem exists_rational_four_moment_lostJet_growth :
    ∃ φ : ℝ → BruhatCompactSupport (IdeleClassGroup (𝓞 ℚ) ℚ),
      (∀ y : ℝ, 0 ≤ y → tsupport (φ y).val ⊆ {x | 1 < ((ideleClassNorm ℚ x : ℝ≥0) : ℝ)}) ∧
      (∀ y : ℝ, ∀ p ∈ ({-(1 / 2), 1 / 2, 0, 1} : Set ℝ),
        principalMellin(ℚ, φ y, (p : ℂ)) = 0) ∧
      (∀ y : ℝ, Summable (fun j : principalSites ℚ 0 (3 / 4) ↦
        ((retainedJets ℚ (3 / 4) 2 j : ℂ) - retainedJets ℚ (1 / 4) 2 j) *
          principalMellin(ℚ, φ y, j.val))) ∧
      ∀ (i : principalSites ℚ 0 (3 / 4)), i.val.re = 1 / 2 → i.val.im ≠ 0 →
        ∀ ε : ℝ, 0 < ε → ∀ C : ℝ, ∃ᶠ y : ℝ in atTop, C * Real.exp ((1 / 2 - ε) * y) <
          ‖∑' j : principalSites ℚ 0 (3 / 4),
            ((retainedJets ℚ (3 / 4) 2 j : ℂ) - retainedJets ℚ (1 / 4) 2 j) *
              principalMellin(ℚ, φ y, j.val)‖ := by
  classical
  let P : Finset ℝ := {-(1 / 2), 1 / 2, 0, 1}
  obtain ⟨H, φ, _, _, _, _, hsupp, hzero, hsum, hgr⟩ :=
    exists_principal_lostJet_mellin_growth (F := ℚ) 0 (1 / 4) (3 / 4) 2 (by norm_num) (by norm_num) P
  refine ⟨φ, hsupp, fun y p hp ↦ hzero y p (by simpa [P] using hp), hsum, ?_⟩
  intro i hre him ε he C
  have hi : 0 < jetLoss ℚ (1 / 4) 2 i := by
    rw [jetLoss_eq_order_of_between ℚ i (by norm_num) (by rw [hre]; norm_num) (by rw [hre]; norm_num)]
    exact (Int.toNat_lt_toNat i.property.2).mpr i.property.2
  apply hgr i hi _ _ (by rw [hre]; linarith) C
  intro p _ hz
  exact him (by rw [hz, Complex.ofReal_im])

end RiemannMasullo
