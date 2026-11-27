module

public import RiemannMasullo.Ch11_ShellStructure.Sec2b
public import RiemannMasullo.Ch09_HardySobolev.Sec3
public import RiemannMasullo.AppC_LCTVS.Sec3a
public import RiemannMasullo.Ch10_TraceSpectral.Sec1
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! # Nuclear annular compression on the local Paley–Wiener level

A logarithmic bump that equals one on the support of the spatial mask
reduces its convolution to the nuclear Hardy–Sobolev cutoff operator.
Orthogonal compression then gives nuclearity on the actual closed level.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

/-- A smooth logarithmic cutoff equals one throughout any prescribed positive
module interval and has a nonempty inner band. -/
private theorem exists_modulatedCutoff_eq_one_on_annulus
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (m : G →ₜ* ℝ≥0ˣ) {lower upper : ℝ} (hlower : 0 < lower) :
    let L := max (max 2 upper) lower⁻¹ + 2
    let d := L⁻¹ / 4
    ∃ χ : G → ℝ, IsModulatedCutoff m L d χ ∧
      (0 < L⁻¹ + d ∧ L⁻¹ + d < L - d) ∧
      EqOn χ 1 ((fun x ↦ ((m x).val : ℝ)) ⁻¹' Icc lower upper) := by
  intro L d
  have hL : 2 < L := by
    dsimp only [L]
    linarith [le_max_left (2 : ℝ) upper, le_max_left (max 2 upper) lower⁻¹]
  have hLp : 0 < L := by linarith
  have hd : 0 < d := by dsimp [d]; positivity
  have hdlt : d < L⁻¹ := by dsimp [d]; linarith [inv_pos.mpr hLp]
  have hinv : L⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hdsmall : d < 1 / 2 := by dsimp [d]; linarith
  have hplateau : 1 < L - d := by linarith
  have hplateau_pos : 0 < L - d := by linarith
  have hprod : 1 ≤ (L⁻¹ + d) * (L - d) := by
    have hh := mul_nonneg hd.le (show 0 ≤ L - L⁻¹ - d by linarith)
    nlinarith [inv_mul_cancel₀ hLp.ne']
  let B : ContDiffBump (0 : ℝ) :=
    ⟨Real.log (L - d), Real.log L, Real.log_pos hplateau,
      Real.log_lt_log hplateau_pos (sub_lt_self L hd)⟩
  let r (x : G) : ℝ := (m x).val
  have hr : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  have hpos (x : G) : 0 < r x := NNReal.coe_pos.mpr (Units.zero_lt _)
  let χ (x : G) := B (Real.log (r x))
  have hχ_one (x : G) (hlo : (L - d)⁻¹ ≤ r x) (hhi : r x ≤ L - d) :
      χ x = 1 := by
    apply B.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
    change -Real.log (L - d) ≤ _ ∧ _ ≤ Real.log (L - d)
    rw [← Real.log_inv, Real.log_le_log_iff (inv_pos.mpr hplateau_pos) (hpos x),
      Real.log_le_log_iff (hpos x) hplateau_pos]
    exact ⟨hlo, hhi⟩
  have h1 : χ 1 = 1 := by
    apply B.one_of_mem_closedBall
    simp [r, B.rIn_pos.le]
  have hcut : IsModulatedCutoff m L d χ := by
    refine ⟨hLp, hd, by linarith, by linarith, fun _ ↦ B.nonneg,
      fun x ↦ (abs_of_nonneg (B.nonneg (x := Real.log (r x)))) ▸ B.le_one,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact IsGreatest.csSup_eq ⟨⟨1, h1⟩, forall_mem_range.mpr fun _ ↦ B.le_one⟩
    · refine ⟨fun t ↦ B (Real.log t), ∅, fun _ ↦ rfl, by simp, ?_, by simp⟩
      simp only [Finset.coe_empty, sdiff_empty]
      exact B.contDiff.comp_contDiffOn
        (fun x hx ↦ (Real.contDiffAt_log.mpr (mem_Ioi.mp hx).ne').contDiffWithinAt)
    · intro x
      change B (Real.log ((m x).val : ℝ)) = B (Real.log ((m x⁻¹).val : ℝ))
      rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv, B.neg]
    · apply closure_minimal _ (isClosed_Icc.preimage hr)
      intro x hx
      have hmem : Real.log (r x) ∈ support B := hx
      rw [B.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
      obtain ⟨hl, hu⟩ := abs_lt.mp hmem
      change L⁻¹ ≤ r x ∧ r x ≤ L
      rw [← Real.log_le_log_iff (inv_pos.mpr hLp) (hpos x), Real.log_inv,
        ← Real.log_le_log_iff (hpos x) hLp]
      exact ⟨hl.le, hu.le⟩
    · intro x hx
      change L⁻¹ + d ≤ r x ∧ r x ≤ L - d at hx
      exact hχ_one x
        (((inv_le_iff_one_le_mul₀ hplateau_pos).mpr hprod).trans hx.1) hx.2
  refine ⟨χ, hcut, ⟨by positivity, by linarith⟩, ?_⟩
  have hLlower : lower⁻¹ ≤ L - d := by
    dsimp only [L]
    linarith [le_max_right (max 2 upper) lower⁻¹]
  have hLupper : upper ≤ L - d := by
    dsimp only [L]
    linarith [le_max_right (2 : ℝ) upper, le_max_left (max 2 upper) lower⁻¹]
  have hcover_lower : (L - d)⁻¹ ≤ lower := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hlower) hLlower
  intro x hx
  change lower ≤ r x ∧ r x ≤ upper at hx
  exact hχ_one x (hcover_lower.trans hx.1) (hx.2.trans hLupper)


section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- An annular envelope that equals one on the support leaves the cutoff multiplier unchanged. -/
private theorem lpCutoffMultiplier_comp_modulatedCutoffOperator
    (m : G →ₜ* ℝ≥0ˣ) (ν : Measure G) (ρ : G → ℝ)
    (hρm : Measurable ρ) (hρb : ∀ x, |ρ x| ≤ 1)
    {L d : ℝ} {χ : G → ℝ} (hχ : IsModulatedCutoff m L d χ)
    (hcover : ∀ x, ρ x ≠ 0 → χ x = 1) :
    (lpCutoffMultiplier ν ρ hρm hρb).comp (modulatedCutoffOperator m ν hχ) =
      lpCutoffMultiplier ν ρ hρm hρb := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [lpCutoffMultiplier_apply ν ρ hρm hρb (modulatedCutoffOperator m ν hχ u),
    modulatedCutoffOperator_apply m ν hχ u, lpCutoffMultiplier_apply ν ρ hρm hρb u] with x hx hxc hy
  change lpCutoffMultiplier ν ρ hρm hρb (modulatedCutoffOperator m ν hχ u) x =
    lpCutoffMultiplier ν ρ hρm hρb u x
  rw [hx, hxc, hy]
  by_cases hzero : ρ x = 0
  · simp [hzero]
  · simp [hcover x hzero]


end

private theorem annularAction_nuclear
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
    (hmSurj : Surjective m) {s : ℝ} (hs : 0 ≤ s)
    (φ : BruhatCompactSupport G) {L d : ℝ} {χ : G → ℝ}
    (hχ : IsModulatedCutoff m L d χ)
    (hplateau : 0 < L⁻¹ + d ∧ L⁻¹ + d < L - d) :
    IsNuclearOperator ((modulatedCutoffOperator m
      (intervalSobolevMeasure μ (fun x ↦ Real.log ((m x).val : ℝ)) 0 0 s) hχ).comp
      (hardySobolevTestAction μ m 0 0 s le_rfl hs φ)) := by
  have hφsmooth : IsBruhatSmooth φ.val := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hφc := continuous_of_bruhatSmooth hφsmooth
  have hφb := hφc.bounded_above_of_compact_support
    (show HasCompactSupport φ.val from φ.property.2)
  obtain ⟨hT, _, _⟩ := truncatedHardySobolevConvolution_trace μ m 0 0 s le_rfl hs φ.val
    hφc.aemeasurable φ.property.2 hφb hm hmSurj hφsmooth hχ hplateau
  rw [hardySobolevConvolution_eq_testAction μ m 0 0 s le_rfl hs φ hφc.aemeasurable hφb] at hT
  exact hT

private theorem annularMaskTestAction_nuclear
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
    (hmSurj : Surjective m) {s : ℝ} (hs : 0 ≤ s)
    (φ : BruhatCompactSupport G) (ρ : G → ℝ)
    (hρm : Measurable ρ) (hρb : ∀ x, |ρ x| ≤ 1)
    {lower upper : ℝ} (hlower : 0 < lower)
    (hρsupp : ∀ x, ρ x ≠ 0 → lower ≤ ((m x).val : ℝ) ∧ ((m x).val : ℝ) ≤ upper) :
    let ν := intervalSobolevMeasure μ (fun x ↦ Real.log ((m x).val : ℝ)) 0 0 s
    let M := lpCutoffMultiplier ν ρ hρm hρb
    let A : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν := hardySobolevTestAction μ m 0 0 s le_rfl hs φ
    IsNuclearOperator (M.comp A) := by
  intro ν M A
  obtain ⟨χ, hχ, hplateau, hχ_one⟩ :=
    exists_modulatedCutoff_eq_one_on_annulus m (upper := upper) hlower
  let C := modulatedCutoffOperator m ν hχ
  have hMC : M * C = M :=
    lpCutoffMultiplier_comp_modulatedCutoffOperator m ν ρ hρm hρb hχ
      (fun x hx ↦ hχ_one (hρsupp x hx))
  have hCA : IsNuclearOperator (C * A) :=
    annularAction_nuclear μ m hm hmSurj hs φ hχ hplateau
  have h := mul_mem_nuclearEndomorphisms_left M
    (⟨C * A, hCA⟩ : nuclearEndomorphisms (Lp ℂ 2 ν))
  change IsNuclearOperator (M * (C * A)) at h
  rwa [← mul_assoc, hMC] at h

private theorem annularCompression_nuclear
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) [CompleteSpace V] (T K : H →L[ℂ] H)
    (hT : IsNuclearOperator T) :
    IsNuclearOperator (V.orthogonalProjectionOnto.comp (T.comp (K.comp V.subtypeL))) ∧
      IsNuclearOperator (V.starProjection.comp (T.comp (K.comp V.starProjection))) := by
  constructor
  · let j := K.comp V.subtypeL
    let q := V.orthogonalProjectionOnto
    change IsNuclearOperator (q.comp (T.comp j))
    obtain ⟨c, ℓ, y, hc, hℓ, hy, hsum⟩ := (isNuclearOperator_iff_isBanachNuclear T).mp hT
    let pre := (ContinuousLinearMap.compL ℂ V H ℂ).flip j
    apply (isNuclearOperator_iff_isBanachNuclear _).mpr
    refine ⟨c, (fun n ↦ (ℓ n).comp j), q ∘ y, hc, ?_, ?_, ?_⟩
    · exact (pre.continuous.tendsto' 0 0 (map_zero pre)).comp hℓ
    · exact (q.continuous.tendsto' 0 0 (map_zero q)).comp hy
    · intro x
      simpa only [map_smul, Function.comp_apply, ContinuousLinearMap.comp_apply] using
        q.hasSum (hsum (j x))
  · change IsNuclearOperator (V.starProjection * (T * (K * V.starProjection)))
    have hright := mul_mem_nuclearEndomorphisms_right (K * V.starProjection)
      (⟨T, hT⟩ : nuclearEndomorphisms H)
    exact mul_mem_nuclearEndomorphisms_left V.starProjection
      (⟨T * (K * V.starProjection), hright⟩ : nuclearEndomorphisms H)

private theorem sLocalNorm_modulation_surjective (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsModulation (continuousSIdeleQuotientNorm F S) ∧
      Surjective (continuousSIdeleQuotientNorm F S : SIdeleQuotient F S → ℝ≥0ˣ) := by
  have hsection : ∃ σ : ℝ≥0ˣ →ₜ* SIdeleQuotient F S,
      RightInverse σ (sIdeleQuotientNorm F S) :=
    sIdeleQuotientNorm_exists_section (F := F) (S := S)
  obtain ⟨σ, hσ⟩ := hsection
  have hsurj : Surjective (sIdeleQuotientNorm F S) := hσ.surjective
  refine ⟨⟨isProperMap_sIdeleQuotientNorm F S, σ (Units.mk0 2 two_ne_zero), ?_⟩, hsurj⟩
  intro h
  change sIdeleQuotientNorm F S (σ (Units.mk0 2 two_ne_zero)) = 1 at h
  have h2 := (hσ (Units.mk0 2 two_ne_zero)).symm.trans h
  have ht := congrArg (fun t : ℝ≥0ˣ ↦ ((t : ℝ≥0) : ℝ)) h2
  norm_num at ht

set_option maxSynthPendingDepth 8

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1 instSIdeleQuotientHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "J" => SIdeleQuotient F S
local notation "N" => continuousSIdeleQuotientNorm F S
local notation "μ" => sLocalQuotientTamagawaMeasure F S
local notation "ν(" s ")" => intervalSobolevMeasure μ (logSIdeleQuotientNorm F S) 0 0 s
local notation "W(" s ")" => CompactIntervalSobolev μ (logSIdeleQuotientNorm F S) 0 0 s

/-- Paper: Theorem 12.4.1.1, Step II, pp. 515–517. A bounded measurable spatial
cutoff supported on a positive annulus gives a nuclear compression on the
actual S-local invariant Paley–Wiener level. The right-hand operator can be
any bounded endomorphism of the weighted ambient space.
Deviation: Use the compact-interval Hilbert model and take a positive inner
radius, as in the independent lower cutoff of footnote 2 on p. 514. -/
theorem sLocalInvariantPWSobolev_annularCompression_nuclear
    {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s)
    (char : PontryaginDual (sIdeleQuotientNorm F S).ker) (B : ℝ)
    (φ : BruhatCompactSupport J) (ρ : J → ℝ)
    (hρm : Measurable ρ) (hρb : ∀ x, |ρ x| ≤ 1)
    {lower upper : ℝ} (hlower : 0 < lower)
    (hρsupp : ∀ x, ρ x ≠ 0 → lower ≤ ((N x).val : ℝ) ∧ ((N x).val : ℝ) ≤ upper)
    (K : W(s) →L[ℂ] W(s)) :
    let V : Submodule ℂ W(s) := sLocalInvariantPWSobolev (F := F) (S := S) hs ha char B
    letI : CompleteSpace V := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    let M : W(s) →L[ℂ] W(s) := lpCutoffMultiplier (ν(s)) ρ hρm hρb
    let A : W(s) →L[ℂ] W(s) := hardySobolevTestAction μ N 0 0 s le_rfl hs φ
    IsNuclearOperator (V.orthogonalProjectionOnto.comp ((M.comp A).comp (K.comp V.subtypeL))) ∧
      IsNuclearOperator (V.starProjection.comp ((M.comp A).comp (K.comp V.starProjection))) := by
  intro V M A
  have hV : IsClosed (V : Set W(s)) := Submodule.isClosed_topologicalClosure _
  let : CompleteSpace V := hV.completeSpace_coe
  obtain ⟨hm, hms⟩ := sLocalNorm_modulation_surjective F S
  have hT : IsNuclearOperator (M.comp A) :=
    annularMaskTestAction_nuclear (G := J) μ N hm hms hs φ ρ hρm hρb hlower hρsupp
  exact annularCompression_nuclear V (M.comp A) K hT

end RiemannMasullo
