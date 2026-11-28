module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_CoshClustersa_Isolated
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_TraceClass
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch10_TraceSpectral.Sec3_HeckeMultipliers
import RiemannMasullo.Ch10_TraceSpectral.Sec3_Clusters
import RiemannMasullo.Ch10_TraceSpectral.Sec2
import RiemannMasullo.AppC_LCTVS.Sec3a

/-!
# Cluster blocks and positive-width `cosh`-weighted summability (`#7406`)

Assembles the cluster blocks on `CoshIntervalSobolev F α s` for any `α ≥ 0` and `s ≥ 0`:
1. `summable_wordDerivMajorant_finset_sum`: finset derivative sums of defect words remain summable
   in word length `m` and word `w` whenever `∑' ι, coshDefectDerivBound α s δ 0 ι ≤ 1 / 2`.
2. `coshSpectralClusterBlock`, `coshGeometricClusterBlock`, `coshAmbientClusterBlock`:
   cluster blocks and their nuclearity/splitting identities.
3. `exists_sectionTrivial_basepointChoice`: existence of a spectral basepoint choice `χ` trivial
   along a continuous norm section `τ : ℝ≥0ˣ →ₜ* C𝔽`.
4. `summable_inv_pow_of_encard_poly`: inverse-power summability from polynomial level-set counts.
5. `coshSpectralStripGeometricBlocks_clusters_summable_of_section`: unconditional trace-norm
   summability of both geometric and spectral cluster blocks for section-trivial basepoints.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField Set Topology
open scoped BigOperators ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo.Isolated.CoshPositiveWidth

attribute [local instance] RiemannMasullo.instIdeleClassMeasurableSpaceSec1
  RiemannMasullo.instIdeleClassBorelSpaceSec1 RiemannMasullo.instIdeleClassT2Sec1
  RiemannMasullo.instIdeleClassLocallyCompactSec1 RiemannMasullo.instIdeleClassSecondCountableSec1
  RiemannMasullo.instIdeleClassHaarMeasureSec1

section TraceAndWordHelpers

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (NumberField.RingOfIntegers F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F

private lemma traceNorm_nonneg_hilb {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : nuclearEndomorphisms H) : 0 ≤ traceNorm T := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  simpa using (traceNorm_normedSpaceCore (H := H)).norm_nonneg T

private lemma traceNorm_zero_hilb {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : traceNorm (0 : nuclearEndomorphisms H) = 0 := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  simpa using ((traceNorm_normedSpaceCore (H := H)).norm_eq_zero_iff (0 : nuclearEndomorphisms H)).mpr rfl

private lemma traceNorm_add_le_hilb {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T D : nuclearEndomorphisms H) :
    traceNorm (T + D) ≤ traceNorm T + traceNorm D := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  simpa using (traceNorm_normedSpaceCore (H := H)).norm_triangle T D

private lemma traceNorm_sum_le_hilb {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (s : Finset ι) (T : ι → nuclearEndomorphisms H) :
    traceNorm (∑ i ∈ s, T i) ≤ ∑ i ∈ s, traceNorm (T i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [traceNorm_zero_hilb]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (traceNorm_add_le_hilb _ _).trans (add_le_add le_rfl ih)

private lemma coshTestAction_sum {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) {ι : Type*}
    (K : Finset ι) (f : ι → BruhatCompactSupport C𝔽) :
    coshTestAction (F := F) hα hs (∑ i ∈ K, f i) = ∑ i ∈ K, coshTestAction (F := F) hα hs (f i) :=
  map_sum (coshTestAction_isLinear (F := F) hα hs).mk' f K

lemma summable_wordDerivMajorant_finset_sum {α s δ : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 32)
    (hS : ∑' ι : CoshDefectIndex, coshDefectDerivBound α s δ 0 ι ≤ 1 / 2) (N : ℕ) :
    (∀ m : ℕ, Summable (fun w : Fin (m + 1) → CoshDefectIndex ↦
      ∑ r ∈ Finset.range (N + 1), wordDerivMajorant α s δ r (m + 1) w)) ∧
    Summable (fun m : ℕ ↦ ∑' w : Fin (m + 1) → CoshDefectIndex,
      ∑ r ∈ Finset.range (N + 1), wordDerivMajorant α s δ r (m + 1) w) := by
  have hm (m : ℕ) : Summable (fun w : Fin (m + 1) → CoshDefectIndex ↦
      ∑ r ∈ Finset.range (N + 1), wordDerivMajorant α s δ r (m + 1) w) :=
    summable_sum fun r _ ↦ summable_wordDerivMajorant hα hs hδ0 hδ1 r (m + 1)
  refine ⟨hm, ?_⟩
  have heq (m : ℕ) : (∑' w : Fin (m + 1) → CoshDefectIndex,
      ∑ r ∈ Finset.range (N + 1), wordDerivMajorant α s δ r (m + 1) w) =
      ∑ r ∈ Finset.range (N + 1), wordDerivSum α s δ r (m + 1) := by
    rw [Summable.tsum_finsetSum (fun r _ ↦ summable_wordDerivMajorant hα hs hδ0 hδ1 r (m + 1))]
    exact Finset.sum_congr rfl fun r _ ↦ (hasSum_wordDerivMajorant hα hs hδ0 hδ1 r (m + 1)).tsum_eq
  simp_rw [heq]
  exact summable_sum fun r _ ↦
    (summable_wordDerivSum hα hs hδ0 hδ1 hS r).comp_injective (fun _ _ h ↦ Nat.succ.inj h)

private lemma ideleClassNormTwist_mul (ψ : PontryaginDual C𝔽) (w : ℂ) (h g : C𝔽) :
    ideleClassNormTwist (F := F) ψ w (h * g) =
      ideleClassNormTwist (F := F) ψ w h * ideleClassNormTwist (F := F) ψ w g := by
  change ((ψ (h * g) : Circle) : ℂ) * (((ideleClassNorm F (h * g)).val : ℝ) : ℂ) ^ w =
    (((ψ h : Circle) : ℂ) * (((ideleClassNorm F h).val : ℝ) : ℂ) ^ w) *
      (((ψ g : Circle) : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ w)
  have hpow : (((ideleClassNorm F (h * g)).val : ℝ) : ℂ) ^ w =
      ((((ideleClassNorm F h).val : ℝ) : ℂ) ^ w) * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ w) := by
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) w
  rw [map_mul, Circle.coe_mul, hpow]
  ring

private lemma integral_bruhatLeftTranslate_mul_ideleClassNormTwist (h : C𝔽)
    (φ : BruhatCompactSupport C𝔽) (ψ : PontryaginDual C𝔽) (w : ℂ) :
    ∫ g : C𝔽, (bruhatLeftTranslate (F := F) h φ).val g *
        ideleClassNormTwist (F := F) ψ w g ∂μ𝔽 =
      ideleClassNormTwist (F := F) ψ w h *
        ∫ g : C𝔽, φ.val g * ideleClassNormTwist (F := F) ψ w g ∂μ𝔽 := by
  have heq : (∫ g : C𝔽, (bruhatLeftTranslate (F := F) h φ).val g *
      ideleClassNormTwist (F := F) ψ w g ∂μ𝔽) =
      ∫ g : C𝔽, φ.val g * ideleClassNormTwist (F := F) ψ w (h * g) ∂μ𝔽 := by
    change (∫ g : C𝔽, φ.val (h⁻¹ * g) * ideleClassNormTwist (F := F) ψ w g ∂μ𝔽) = _
    rw [← MeasureTheory.integral_mul_left_eq_self (μ := μ𝔽)
      (fun g : C𝔽 ↦ φ.val (h⁻¹ * g) * ideleClassNormTwist (F := F) ψ w g) h]
    refine MeasureTheory.integral_congr_ae (.of_forall fun g ↦ ?_)
    dsimp only
    rw [inv_mul_cancel_left]
  rw [heq, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (.of_forall fun g ↦ ?_)
  change φ.val g * ideleClassNormTwist (F := F) ψ w (h * g) = _
  rw [ideleClassNormTwist_mul]
  ring

private lemma norm_ideleClassNormTwist_le (ψ : PontryaginDual C𝔽) {X : ℝ} (_hX : 0 ≤ X)
    {w : ℂ} (hw : |w.re| ≤ X) (h : C𝔽) :
    ‖ideleClassNormTwist (F := F) ψ w h‖ ≤
      max (((ideleClassNorm F h).val : ℝ) ^ X) (((ideleClassNorm F h).val : ℝ) ^ (-X)) := by
  change ‖((ψ h : Circle) : ℂ) * ((((ideleClassNorm F h).val : ℝ) : ℂ) ^ w)‖ ≤ _
  rw [norm_mul, Circle.norm_coe, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
  rcases le_total ((ideleClassNorm F h).val : ℝ) 1 with h1 | h1
  · exact (Real.rpow_le_rpow_of_exponent_ge (NNReal.coe_pos.mpr (Units.zero_lt _)) h1
      (abs_le.mp hw).1).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_exponent_le h1 (abs_le.mp hw).2).trans (le_max_left _ _)

end TraceAndWordHelpers

section ClusterBlocks

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (NumberField.RingOfIntegers F) F

/-- Spectral cluster block on `CoshIntervalSobolev F α s` for a finite cluster `K`. -/
def coshSpectralClusterBlock (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport C𝔽) (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (K : Finset (CoshStripZero (F := F) χ a α)) :
    CoshIntervalSobolev F α s →L[ℂ] CoshIntervalSobolev F α s :=
  ((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs φ)).comp
    (coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s))

/-- Geometric cluster block on `CoshIntervalSobolev F α s` for a finite cluster `K`. -/
def coshGeometricClusterBlock (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport C𝔽) (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (K : Finset (CoshStripZero (F := F) χ a α)) :
    CoshIntervalSobolev F α s →L[ℂ] CoshIntervalSobolev F α s :=
  ((coshGeometricProjection (F := F) a hα hs).comp (coshTestAction hα hs φ)).comp
    (coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s))

/-- Ambient cluster block on `CoshIntervalSobolev F α s` for a finite cluster `K`. -/
def coshAmbientClusterBlock (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport C𝔽) (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (K : Finset (CoshStripZero (F := F) χ a α)) :
    CoshIntervalSobolev F α s →L[ℂ] CoshIntervalSobolev F α s :=
  (coshTestAction (F := F) hα hs φ).comp
    (coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s))

lemma coshSpectralClusterBlock_mem_nuclear (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport C𝔽) (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (K : Finset (CoshStripZero (F := F) χ a α)) :
    IsNuclearOperator (coshSpectralClusterBlock (F := F) a hα hs φ χ x Λ K) :=
  mul_mem_nuclearEndomorphisms_left
    ((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs φ))
    ⟨_, coshClusterProj_mem_nuclear a hα hs x Λ K _ _⟩

lemma coshGeometricClusterBlock_mem_nuclear (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport C𝔽) (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (K : Finset (CoshStripZero (F := F) χ a α)) :
    IsNuclearOperator (coshGeometricClusterBlock (F := F) a hα hs φ χ x Λ K) :=
  mul_mem_nuclearEndomorphisms_left
    ((coshGeometricProjection (F := F) a hα hs).comp (coshTestAction hα hs φ))
    ⟨_, coshClusterProj_mem_nuclear a hα hs x Λ K _ _⟩

lemma coshAmbientClusterBlock_mem_nuclear (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport C𝔽) (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (K : Finset (CoshStripZero (F := F) χ a α)) :
    IsNuclearOperator (coshAmbientClusterBlock (F := F) a hα hs φ χ x Λ K) :=
  mul_mem_nuclearEndomorphisms_left (coshTestAction (F := F) hα hs φ)
    ⟨_, coshClusterProj_mem_nuclear a hα hs x Λ K _ _⟩

lemma coshAmbientClusterBlock_eq_add (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport C𝔽) (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (K : Finset (CoshStripZero (F := F) χ a α)) :
    coshAmbientClusterBlock (F := F) a hα hs φ χ x Λ K =
      coshGeometricClusterBlock (F := F) a hα hs φ χ x Λ K +
        coshSpectralClusterBlock (F := F) a hα hs φ χ x Λ K := by
  ext1 u
  dsimp only [coshAmbientClusterBlock, coshGeometricClusterBlock, coshSpectralClusterBlock,
    add_apply, ContinuousLinearMap.comp_apply]
  exact (DFunLike.congr_fun (coshSpectralProjection_add_geometric (F := F) a hα hs) _).symm

private lemma traceNorm_proj_cluster_sum_le (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (P : CoshIntervalSobolev F α s →L[ℂ] CoshIntervalSobolev F α s)
    {ι : Type*} (S : Finset ι) (f : ι → BruhatCompactSupport C𝔽)
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (K : Finset (CoshStripZero (F := F) χ a α)) :
    traceNorm ⟨(P.comp (coshTestAction hα hs (∑ i ∈ S, f i))).comp
          (coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s)),
        mul_mem_nuclearEndomorphisms_left _ ⟨_, coshClusterProj_mem_nuclear a hα hs x Λ K _ _⟩⟩ ≤
      ∑ i ∈ S, traceNorm ⟨(P.comp (coshTestAction hα hs (f i))).comp
          (coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s)),
        mul_mem_nuclearEndomorphisms_left _ ⟨_, coshClusterProj_mem_nuclear a hα hs x Λ K _ _⟩⟩ := by
  have hsub : (⟨(P.comp (coshTestAction hα hs (∑ i ∈ S, f i))).comp
        (coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s)),
        mul_mem_nuclearEndomorphisms_left _ ⟨_, coshClusterProj_mem_nuclear a hα hs x Λ K _ _⟩⟩ :
        nuclearEndomorphisms (CoshIntervalSobolev F α s)) =
      ∑ i ∈ S, ⟨(P.comp (coshTestAction hα hs (f i))).comp
        (coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s)),
        mul_mem_nuclearEndomorphisms_left _ ⟨_, coshClusterProj_mem_nuclear a hα hs x Λ K _ _⟩⟩ := by
    apply Subtype.ext; rw [Submodule.coe_sum]; ext1 u
    simp only [ContinuousLinearMap.comp_apply, coshTestAction_sum hα hs S f, sum_apply, map_sum]
  rw [hsub]; exact traceNorm_sum_le_hilb S _

end ClusterBlocks

section BasepointAndCounting

/-- There exists a continuous norm section `τ` and a spectral basepoint choice `χ` that is
trivial on `τ` and sends `1` to `1`. -/
theorem exists_sectionTrivial_basepointChoice (F : Type*) [Field F] [NumberField F] :
    ∃ (χ : PontryaginDual (ideleClassNorm F).ker →
        PontryaginDual (IdeleClassGroup (NumberField.RingOfIntegers F) F))
      (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (NumberField.RingOfIntegers F) F),
      IsSpectralBasepointChoice χ ∧ χ 1 = 1 ∧ Function.RightInverse τ (ideleClassNorm F) ∧
        ∀ ω (t : ℝ≥0ˣ), χ ω (τ t) = 1 := by
  let C := IdeleClassGroup (NumberField.RingOfIntegers F) F
  let C₁ := (ideleClassNorm F).ker
  let n : C →ₜ* ℝ≥0ˣ := continuousIdeleClassNorm F
  let q : NumberField.IdeleGroup (NumberField.RingOfIntegers F) F →ₜ* C :=
    ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ : ℝ≥0ˣ →ₜ* C := q.comp ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : Function.RightInverse τ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let P : C →ₜ* C := ContinuousMonoidHom.id C / τ.comp n
  have hP (g : C) : P g ∈ C₁ := by
    change ideleClassNorm F (g / τ (ideleClassNorm F g)) = 1; rw [map_div, hτ _, div_self']
  let r : C →ₜ* C₁ := ⟨P.toMonoidHom.codRestrict _ hP, P.continuous.subtype_mk _⟩
  let χ : PontryaginDual C₁ → PontryaginDual C := fun ω ↦ ω.comp r
  refine ⟨χ, τ, fun ω ↦ ?_, by ext1 g; rfl, hτ, fun ω t ↦ ?_⟩
  · ext1 u; change ω ⟨(u : C) / τ (ideleClassNorm F u), _⟩ = ω u
    congr 1; ext1; change (u : C) / τ (ideleClassNorm F u) = u
    rw [show ideleClassNorm F (u : C) = 1 from u.property, map_one, div_one]
  · change ω ⟨τ t / τ (ideleClassNorm F (τ t)), _⟩ = 1
    rw [show (⟨τ t / τ (ideleClassNorm F (τ t)), hP (τ t)⟩ : C₁) = 1 from
      Subtype.ext (by change τ t / τ (ideleClassNorm F (τ t)) = 1; rw [hτ t, div_self']), map_one]

section ClassicalCounting
open Classical

/-- Inverse-power summability on `Ω × ℤ` from polynomial level-set cardinality bounds for `κ`. -/
lemma summable_inv_pow_of_encard_poly {Ω : Type*} (S : Set Ω) (κ : Ω → ℝ)
    (hκ : ∀ ω ∈ S, 0 ≤ κ ω) (C d : ℕ)
    (h_cnt : ∀ T : ℕ, {ω : Ω | ω ∈ S ∧ κ ω ≤ (T : ℝ)}.encard ≤ (C * (T + 1) ^ d : ℕ)) :
    Summable (fun p : Ω × ℤ ↦
      if p.1 ∈ S then (1 + κ p.1 + |(p.2 : ℝ)|) ^ (-(d + 4 : ℤ)) else 0) := by
  let f : {ω : Ω // ω ∈ S} → ℕ := fun ω ↦ Nat.floor (κ ω.1)
  let A (ω : Ω) : ℝ := (Nat.floor (κ ω) : ℝ) + 1
  let B (k : ℤ) : ℝ := |(k : ℝ)| + 1
  have h_img_sub (n : ℕ) (U : Set {ω : Ω // ω ∈ S}) (hU : ∀ ω ∈ U, f ω = n) :
      Subtype.val '' U ⊆ {ω : Ω | ω ∈ S ∧ κ ω ≤ ((n + 1 : ℕ) : ℝ)} := by
    rintro ω ⟨⟨ω, hω⟩, hmem, rfl⟩
    have hlt : κ ω < (Nat.floor (κ ω) : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [show Nat.floor (κ ω) = n from hU ⟨ω, hω⟩ hmem] at hlt
    exact ⟨hω, by exact_mod_cast hlt.le⟩
  have hS_fib : ∀ n : ℕ, {ω : {ω : Ω // ω ∈ S} | f ω = n}.Finite := fun n ↦ by
    rw [← Set.encard_lt_top_iff, ← Subtype.val_injective.injOn.encard_image]
    exact ((Set.encard_mono (h_img_sub n _ fun _ h ↦ h)).trans (h_cnt (n + 1))).trans_lt
      (ENat.natCast_lt_top _)
  let Fset (n : ℕ) := (hS_fib n).toFinset
  have hp_inv2 : Summable (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ ^ 2) := by
    have hp0 : Summable (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) :=
      (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)).congr fun n ↦ by simp
    exact (hp0.comp_injective fun _ _ h ↦ Nat.succ.inj h).congr fun n ↦ by
      dsimp only [Function.comp_def]; rw [Nat.cast_succ, inv_pow]
  have hsum_ω : Summable (fun ω : {ω : Ω // ω ∈ S} ↦ (A ω.1)⁻¹ ^ (d + 2)) := by
    let e : (Σ n : ℕ, Fset n) ≃ {ω : Ω // ω ∈ S} :=
      { toFun := fun p ↦ p.2.1
        invFun := fun ω ↦ ⟨f ω, ⟨ω, (hS_fib (f ω)).mem_toFinset.mpr rfl⟩⟩
        left_inv := fun ⟨n, ω, hω⟩ ↦ by have hn : f ω = n := (hS_fib n).mem_toFinset.mp hω; subst hn; rfl
        right_inv := fun _ ↦ rfl }
    rw [← e.summable_iff]; dsimp only [Function.comp_def]
    rw [summable_sigma_of_nonneg (fun p ↦ pow_nonneg (inv_nonneg.mpr (by dsimp [A]; positivity)) _)]
    refine ⟨fun n ↦ (hasSum_fintype _).summable, (hp_inv2.mul_left ((C * 2 ^ d : ℕ) : ℝ)).of_nonneg_of_le
      (fun _ ↦ tsum_nonneg fun _ ↦ pow_nonneg (inv_nonneg.mpr (by positivity)) _) fun n ↦ ?_⟩
    have hcard_enat : ((Fset n).card : ℕ∞) ≤ (C * ((n + 1) + 1) ^ d : ℕ) :=
      calc ((Fset n).card : ℕ∞)
          = (Fset n : Set {ω : Ω // ω ∈ S}).encard := (Set.encard_coe_eq_coe_finsetCard _).symm
        _ = (Subtype.val '' (Fset n : Set {ω : Ω // ω ∈ S})).encard :=
            (Subtype.val_injective.injOn.encard_image).symm
        _ ≤ {ω : Ω | ω ∈ S ∧ κ ω ≤ ((n + 1 : ℕ) : ℝ)}.encard :=
            Set.encard_mono (h_img_sub n _ fun _ h ↦ (hS_fib n).mem_toFinset.mp h)
        _ ≤ (C * ((n + 1) + 1) ^ d : ℕ) := h_cnt (n + 1)
    have hcard_nat : (Fset n).card ≤ C * (n + 2) ^ d := by exact_mod_cast hcard_enat
    have hcard_r : ((Fset n).card : ℝ) ≤ (C * 2 ^ d : ℕ) * ((n : ℝ) + 1) ^ d :=
      calc ((Fset n).card : ℝ) ≤ (C : ℝ) * ((n : ℝ) + 2) ^ d := by exact_mod_cast hcard_nat
        _ ≤ (C : ℝ) * (2 * ((n : ℝ) + 1)) ^ d :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) d) (Nat.cast_nonneg C)
        _ = ((C * 2 ^ d : ℕ) : ℝ) * ((n : ℝ) + 1) ^ d := by push_cast; rw [mul_pow]; ring
    rw [tsum_fintype]
    have hne : (n : ℝ) + 1 ≠ 0 := by positivity
    calc ∑ x : Fset n, (A x.1.1)⁻¹ ^ (d + 2)
        ≤ ∑ _x : Fset n, ((n : ℝ) + 1)⁻¹ ^ (d + 2) :=
          Finset.sum_le_sum fun ⟨⟨ω, hω⟩, hmem⟩ _ ↦ by
            dsimp only [A]; rw [show Nat.floor (κ ω) = n from (hS_fib n).mem_toFinset.mp hmem]
      _ = ((Fset n).card : ℝ) * ((n : ℝ) + 1)⁻¹ ^ (d + 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ ≤ ((C * 2 ^ d : ℕ) : ℝ) * ((n : ℝ) + 1) ^ d * ((n : ℝ) + 1)⁻¹ ^ (d + 2) :=
          mul_le_mul_of_nonneg_right hcard_r (by positivity)
      _ = ((C * 2 ^ d : ℕ) : ℝ) * ((n : ℝ) + 1)⁻¹ ^ 2 := by
          rw [pow_add, mul_assoc, ← mul_assoc (((n : ℝ) + 1) ^ d), ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_mul]
  have hsum_k : Summable (fun k : ℤ ↦ (B k)⁻¹ ^ 2) :=
    summable_int_iff_summable_nat_and_neg.mpr
      ⟨hp_inv2.congr fun n ↦ by dsimp [B]; rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)],
       hp_inv2.congr fun n ↦ by dsimp [B]; rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]⟩
  have hprod := hsum_ω.mul_of_nonneg hsum_k (fun _ ↦ by positivity) (fun _ ↦ by positivity)
  let emb : {ω : Ω // ω ∈ S} × ℤ → Ω × ℤ := fun q ↦ (q.1.1, q.2)
  have hemb : Function.Injective emb := fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h ↦ by
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h; rfl
  have hzero : ∀ p : Ω × ℤ, p ∉ Set.range emb →
      (if p.1 ∈ S then (1 + κ p.1 + |(p.2 : ℝ)|) ^ (-(d + 4 : ℤ)) else 0) = 0 := fun p hp ↦ by
    by_cases hS : p.1 ∈ S
    · exact (hp ⟨(⟨p.1, hS⟩, p.2), rfl⟩).elim
    · simp only [hS, ↓reduceIte]
  rw [← Function.Injective.summable_iff hemb hzero]
  refine hprod.of_nonneg_of_le (fun ⟨⟨ω, hω⟩, k⟩ ↦ by
    dsimp only [Function.comp_def, emb]; simp only [hω, ↓reduceIte]
    exact zpow_nonneg (by linarith [hκ ω hω, abs_nonneg (k : ℝ)]) _) ?_
  intro ⟨⟨ω, hω⟩, k⟩
  dsimp only [Function.comp_def, emb]; simp only [hω, ↓reduceIte]
  have hA_le : A ω ≤ 1 + κ ω + |(k : ℝ)| := by linarith [Nat.floor_le (hκ ω hω), abs_nonneg (k : ℝ)]
  have hB_le : B k ≤ 1 + κ ω + |(k : ℝ)| := by linarith [hκ ω hω]
  have hpow : A ω ^ (d + 2) * B k ^ 2 ≤ (1 + κ ω + |(k : ℝ)|) ^ (d + 4) :=
    calc A ω ^ (d + 2) * B k ^ 2
        ≤ (1 + κ ω + |(k : ℝ)|) ^ (d + 2) * (1 + κ ω + |(k : ℝ)|) ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ (by dsimp [A]; positivity) hA_le _)
            (pow_le_pow_left₀ (by dsimp [B]; positivity) hB_le 2)
            (by dsimp [B]; positivity) (pow_nonneg (by linarith [hκ ω hω, abs_nonneg (k : ℝ)]) _)
      _ = (1 + κ ω + |(k : ℝ)|) ^ (d + 4) := by rw [← pow_add]
  have hcast : (-(↑d + 4) : ℤ) = -((d + 4 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, zpow_neg, zpow_natCast]
  calc ((1 + κ ω + |(k : ℝ)|) ^ (d + 4))⁻¹
      ≤ (A ω ^ (d + 2) * B k ^ 2)⁻¹ :=
        inv_anti₀ (mul_pos (pow_pos (by dsimp [A]; positivity) _) (pow_pos (by dsimp [B]; positivity) _)) hpow
    _ = (A ω)⁻¹ ^ (d + 2) * (B k)⁻¹ ^ 2 := by rw [mul_inv, inv_pow, inv_pow]

end ClassicalCounting

private lemma coshJetCount_le_of_closedBall {F : Type*} [Field F] [NumberField F] (a : ℝ)
    (χ : PontryaginDual (ideleClassNorm F).ker →
      PontryaginDual (IdeleClassGroup (NumberField.RingOfIntegers F) F))
    {α s : ℝ} (ω : PontryaginDual (ideleClassNorm F).ker) {τ₀ C : ℝ}
    (hC : ∀ S : Finset ℂ,
      (∀ z ∈ S, z ∈ Metric.closedBall (⟨2, τ₀ + 3 / 2⟩ : ℂ) (|a - 2| + α + 2)) →
      ∑ z ∈ S, ((meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) z).untop₀.toNat : ℝ) ≤ C)
    (K : Finset (CoshStripZero (F := F) χ a α))
    (hK : ∀ z ∈ K, z.val.1 = ω ∧ τ₀ ≤ z.val.2.2 ∧ z.val.2.2 ≤ τ₀ + 3) :
    ((∑ z ∈ K, coshStripMult χ a α s z : ℕ) : ℝ) ≤ C := by
  classical
  let pt (z : CoshStripZero (F := F) χ a α) : ℂ :=
    (((a + z.val.2.1 : ℝ) : ℂ) + (z.val.2.2 : ℂ) * Complex.I)
  have hinj : Set.InjOn pt K := fun z hz z' hz' h ↦ Subtype.ext (Prod.ext
    ((hK z hz).1.trans (hK z' hz').1.symm)
    (Prod.ext (add_left_cancel (a := a) (by simpa [pt, Complex.add_re] using congrArg Complex.re h))
      (by simpa [pt, Complex.add_im] using congrArg Complex.im h)))
  have hle (z : CoshStripZero (F := F) χ a α) (hz : z ∈ K) :
      (coshStripMult χ a α s z : ℝ) ≤
        ((meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) (pt z)).untop₀.toNat : ℝ) := by
    exact_mod_cast (by
      unfold coshStripMult spectralStripMultiplicity spectralBoundaryMultiplicity
      rw [(hK z hz).1]; split_ifs <;> [exact le_rfl; exact Nat.min_le_left _ _; exact Nat.zero_le _] :
      coshStripMult χ a α s z ≤ (meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) (pt z)).untop₀.toNat)
  have hball : ∀ w ∈ K.image pt,
      w ∈ Metric.closedBall (⟨2, τ₀ + 3 / 2⟩ : ℂ) (|a - 2| + α + 2) := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨_, h1, h2⟩ := hK z hz
    have hre_d : |(a + z.val.2.1) - 2| ≤ |a - 2| + α :=
      (show |(a + z.val.2.1) - 2| = |(a - 2) + z.val.2.1| by ring_nf).symm ▸
        (abs_add_le _ _).trans (by linarith [abs_le.mpr z.property.1])
    have him_d : |z.val.2.2 - (τ₀ + 3 / 2)| ≤ 3 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [Metric.mem_closedBall, Complex.dist_eq]
    calc ‖pt z - ⟨2, τ₀ + 3 / 2⟩‖
        ≤ |(pt z - ⟨2, τ₀ + 3 / 2⟩).re| + |(pt z - ⟨2, τ₀ + 3 / 2⟩).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |(a + z.val.2.1) - 2| + |z.val.2.2 - (τ₀ + 3 / 2)| := by simp [pt, Complex.sub_re, Complex.sub_im]
      _ ≤ |a - 2| + α + 2 := by linarith
  calc ((∑ z ∈ K, coshStripMult χ a α s z : ℕ) : ℝ)
      = ∑ z ∈ K, (coshStripMult χ a α s z : ℝ) := by push_cast; rfl
    _ ≤ ∑ z ∈ K, ((meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) (pt z)).untop₀.toNat : ℝ) :=
        Finset.sum_le_sum hle
    _ = ∑ w ∈ K.image pt, ((meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) w).untop₀.toNat : ℝ) :=
        (Finset.sum_image (f := fun w : ℂ ↦
          ((meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) w).untop₀.toNat : ℝ))
          (fun z hz z' hz' h ↦ hinj hz hz' h)).symm
    _ ≤ C := hC (K.image pt) hball

end BasepointAndCounting

section PositiveWidthSummability

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (NumberField.RingOfIntegers F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F

private lemma traceNorm_piece_inactive_eq_zero {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) χ hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 32)
    (hS_le : ∑' ι : CoshDefectIndex, coshDefectDerivBound α s δ 0 ι ≤ 1 / 2)
    (h_tr : C𝔽) (ψ₀ : BruhatCompactSupport C𝔽)
    (hψ₀ : ∀ y, ψ₀.val y ≠ 0 → |logIdeleClassNorm F y| ≤ δ)
    (ω : PontryaginDual (ideleClassNorm F).ker)
    (hvan₀ : ∀ (T : ℝ → ℂ) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (w : ℂ),
      ∫ g : C𝔽, (radialMul (F := F) T hT ψ₀).val g * ideleClassNormTwist (F := F) (χ ω) w g ∂μ𝔽 = 0)
    (K : Finset (CoshStripZero (F := F) χ a α)) (hK : ∀ z ∈ K, z.val.1 = ω) :
    traceNorm ⟨coshSpectralClusterBlock (F := F) a hα hs (bruhatLeftTranslate h_tr ψ₀) χ x Λ K,
        coshSpectralClusterBlock_mem_nuclear a hα hs _ χ x Λ K⟩ = 0 ∧
      traceNorm ⟨coshGeometricClusterBlock (F := F) a hα hs (bruhatLeftTranslate h_tr ψ₀) χ x Λ K,
        coshGeometricClusterBlock_mem_nuclear a hα hs _ χ x Λ K⟩ = 0 := by
  have aux (E : nuclearEndomorphisms (CoshIntervalSobolev F α s))
      (hE_eq : E.val = coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s)) :
      traceNorm ⟨((coshSpectralProjection (F := F) a hα hs).comp
          (coshTestAction hα hs (bruhatLeftTranslate h_tr ψ₀))).comp E.val,
          mul_mem_nuclearEndomorphisms_left _ E⟩ = 0 ∧
        traceNorm ⟨((coshGeometricProjection (F := F) a hα hs).comp
          (coshTestAction hα hs (bruhatLeftTranslate h_tr ψ₀))).comp E.val,
          mul_mem_nuclearEndomorphisms_left _ E⟩ = 0 := by
    have hr1 : radialMul (F := F) (fun _ ↦ 1) contDiff_const ψ₀ = ψ₀ :=
      Subtype.ext (funext fun g ↦ by change (1 : ℂ) * ψ₀.val g = _; simp)
    have hsp_rew : ∀ (φ₀ : BruhatCompactSupport C𝔽),
        (⟨((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs φ₀)).comp E.val,
          mul_mem_nuclearEndomorphisms_left _ E⟩ : nuclearEndomorphisms (CoshIntervalSobolev F α s)) =
        ⟨coshSpectralClusterBlock (F := F) a hα hs φ₀ χ x Λ K,
          coshSpectralClusterBlock_mem_nuclear a hα hs φ₀ χ x Λ K⟩ := fun _ ↦
      Subtype.ext (by dsimp [coshSpectralClusterBlock]; rw [hE_eq])
    have hsp_tr : traceNorm ⟨((coshSpectralProjection (F := F) a hα hs).comp
        (coshTestAction hα hs (bruhatLeftTranslate h_tr ψ₀))).comp E.val,
        mul_mem_nuclearEndomorphisms_left _ E⟩ = 0 := by
      rw [congrArg traceNorm (hsp_rew _)]
      refine traceNorm_coshSpectral_cluster_eq_zero hα hs χ x Λ hb hj
        (bruhatLeftTranslate h_tr ψ₀) ω K hK fun w ↦ ?_
      rw [integral_bruhatLeftTranslate_mul_ideleClassNormTwist, ← hr1, hvan₀, mul_zero]
    refine ⟨hsp_tr, ?_⟩
    have hsp_base : traceNorm ⟨((coshSpectralProjection (F := F) a hα hs).comp
        (coshTestAction hα hs ψ₀)).comp E.val, mul_mem_nuclearEndomorphisms_left _ E⟩ = 0 := by
      rw [congrArg traceNorm (hsp_rew _)]
      exact traceNorm_coshSpectral_cluster_eq_zero hα hs χ x Λ hb hj ψ₀ ω K hK fun w ↦ by
        simpa [hr1] using hvan₀ (fun _ ↦ 1) contDiff_const w
    have hP_E : coshSpectralProjection (F := F) a hα hs ∘SL E.val = E.val := by
      rw [hE_eq]; exact coshSpectralProjection_comp_coshClusterProj a hα hs x Λ K _ _
    have hgeom_base_zero :
        traceNorm ⟨((coshGeometricProjection (F := F) a hα hs).comp (coshTestAction hα hs ψ₀)).comp E.val,
          mul_mem_nuclearEndomorphisms_left _ E⟩ = 0 := by
      refine le_antisymm ?_ (traceNorm_nonneg_hilb _)
      have hbd := traceNorm_coshGeometric_le_of_word_bound a hα hs E hP_E hδ0 hδ1 hS_le ψ₀ hψ₀
        (fun _ _ ↦ 0) (fun _ _ ↦ le_rfl) (fun _ ↦ summable_zero) (by simp [summable_zero])
        fun m w ↦ by
          rw [congrArg traceNorm (hsp_rew (wordTest α s w ψ₀))]
          exact (traceNorm_coshSpectral_cluster_eq_zero hα hs χ x Λ hb hj _ ω K hK fun w' ↦
            hvan₀ (wordProd α s w) (contDiff_wordProd α s w) w').le
      simpa using hbd
    obtain ⟨hN, htr⟩ := traceNorm_coshGeometric_translate_le a hα hs E h_tr ψ₀
    refine le_antisymm ?_ (traceNorm_nonneg_hilb _)
    calc traceNorm ⟨_, mul_mem_nuclearEndomorphisms_left _ E⟩
        = traceNorm ⟨_, hN⟩ := congrArg traceNorm (Subtype.ext rfl)
      _ ≤ ‖coshLeftTranslate (F := F) hα hs h_tr‖ *
            (traceNorm ⟨((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs ψ₀)).comp E.val, _⟩ +
              traceNorm ⟨((coshGeometricProjection (F := F) a hα hs).comp (coshTestAction hα hs ψ₀)).comp E.val, _⟩) :=
          htr
      _ = 0 := by rw [hsp_base, hgeom_base_zero, add_zero, mul_zero]
  have h := aux ⟨coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s),
    coshClusterProj_mem_nuclear a hα hs x Λ K _ _⟩ rfl
  exact ⟨(congrArg traceNorm (Subtype.ext rfl)).trans h.1, (congrArg traceNorm (Subtype.ext rfl)).trans h.2⟩

private lemma traceNorm_piece_active_word_le {a α s β X : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hαβ : α < β) (hβX : β < X) (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) χ hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (ω : PontryaginDual (ideleClassNorm F).ker) (k : ℤ) (τ₁ τ₂ : ℝ)
    (hτ_lo : 2 * (k : ℝ) ≤ τ₁) (hτ_hi : τ₁ ≤ 2 * (k : ℝ) + 1)
    (hτ₁₂ : τ₁ + 1 ≤ τ₂) (hτ₂₁ : τ₂ ≤ τ₁ + 3) (hτ₂_hi : τ₂ ≤ 2 * (k : ℝ) + 3)
    (K : Finset (CoshStripZero (F := F) χ a α))
    (hK_in : ∀ z ∈ K, z.val.1 = ω ∧ τ₁ ≤ z.val.2.2 ∧ z.val.2.2 < τ₂)
    (hK_all : ∀ z : CoshStripZero (F := F) χ a α, z.val.1 = ω → τ₁ ≤ z.val.2.2 → z.val.2.2 < τ₂ → z ∈ K)
    (ϑ : ℂ → ℂ) (hϑd : Differentiable ℂ ϑ) (hϑ_up : ∀ u : ℂ, |u.re| ≤ X + 2 → ‖ϑ u‖ ≤ 1)
    (hϑ_ord : ∀ z : CoshStripZero (F := F) χ a α, z.val.1 = ω →
      (coshStripMult χ a α s z : ℕ∞) ≤ analyticOrderAt ϑ (z.val.2.1 + z.val.2.2 * Complex.I))
    {c_rect : ℝ} (hc_rect : 0 < c_rect) {n_rect : ℕ} {Y_ω : ℝ} (hY_ω : 1 ≤ Y_ω)
    (hϑ_low : ∀ w ∈ rectBoundary (-X) X τ₁ τ₂, c_rect / (Y_ω + |(k : ℝ)| + 1) ^ n_rect ≤ ‖ϑ w‖)
    {CJ' : ℝ} (hCJ' : 0 ≤ CJ')
    (hJ_cnt : (∑ z ∈ K, coshStripMult χ a α s z : ℝ) ≤ 6 * CJ' * (Y_ω + |(k : ℝ)| + 2))
    {κ_val : ℝ} (hκ_nn : 0 ≤ κ_val) (hY_le : Y_ω ≤ 1 + κ_val) {N_all : ℕ} (hN_le : n_rect + 3 ≤ N_all)
    {K_m : ℝ} (hK_m : 0 ≤ K_m) (φ₀ : BruhatCompactSupport C𝔽) {M_sum : ℝ} (hM_sum : 0 ≤ M_sum)
    (hmellin : ∀ w ∈ rectBoundary (-X) X τ₁ τ₂,
      (1 + ‖w‖ + κ_val) ^ N_all * ‖∫ g : C𝔽, φ₀.val g * ideleClassNormTwist (F := F) (χ ω) w g ∂μ𝔽‖ ≤
        K_m * M_sum) :
    traceNorm ⟨coshSpectralClusterBlock (F := F) a hα hs φ₀ χ x Λ K,
        coshSpectralClusterBlock_mem_nuclear a hα hs φ₀ χ x Λ K⟩ ≤
      (‖(coshQuotientEquiv (F := F) a hα hs).symm.toContinuousLinearMap‖ *
        ‖(coshQuotientEquiv (F := F) a hα hs).toContinuousLinearMap‖) *
        ((6 * CJ' * 3) * (stripKernelNormConstant α β s * (rectInterpolantGaussianConstant X β 0 *
          (c_rect⁻¹ * 2 ^ n_rect * 2 ^ 2 * 3 ^ N_all * K_m * M_sum)))) *
          (1 + κ_val + |(k : ℝ)|) ^ (-((N_all - (n_rect + 3) : ℕ) : ℤ)) := by
  have hX0 : 0 < X := (hα.trans_lt hαβ).trans hβX
  let U : ℝ := 1 + κ_val + |(k : ℝ)|
  have hU_ge1 : 1 ≤ U := by dsimp only [U]; linarith [abs_nonneg (k : ℝ)]
  have hU_pos : 0 < U := lt_of_lt_of_le zero_lt_one hU_ge1
  let ℓ : ℝ := c_rect / (Y_ω + |(k : ℝ)| + 1) ^ n_rect
  have hℓ : 0 < ℓ := div_pos hc_rect (pow_pos (by linarith [abs_nonneg (k : ℝ)]) _)
  let φb : ℝ := 3 ^ N_all * K_m * M_sum / U ^ N_all
  have hφb_bd : ∀ w ∈ rectBoundary (-X) X τ₁ τ₂,
      ‖∫ g : C𝔽, φ₀.val g * ideleClassNormTwist (F := F) (χ ω) w g ∂μ𝔽‖ ≤ φb := by
    intro w hw
    have hw_k : |(k : ℝ)| ≤ ‖w‖ + 2 := by
      have him_bd : τ₁ ≤ w.im ∧ w.im ≤ τ₂ := by
        rcases mem_rectBoundary_iff.mp hw with ⟨_, h | h⟩ | ⟨h, _⟩
        · exact ⟨h.ge, h.le.trans (by linarith)⟩
        · exact ⟨(by linarith : τ₁ ≤ τ₂).trans h.ge, h.le⟩
        · exact h
      have h1 : 2 * (k : ℝ) ≤ w.im := hτ_lo.trans him_bd.1
      have h2 : w.im ≤ 2 * (k : ℝ) + 3 := him_bd.2.trans hτ₂_hi
      have him : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
      rcases le_or_gt 0 k with hk | hk
      · have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
        rw [abs_of_nonneg hk']; linarith [le_abs_self w.im]
      · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk
        rw [abs_of_nonpos (by linarith)]; linarith [neg_abs_le w.im]
    have hpow : U ^ N_all ≤ 3 ^ N_all * (1 + ‖w‖ + κ_val) ^ N_all := by
      calc U ^ N_all ≤ (3 * (1 + ‖w‖ + κ_val)) ^ N_all :=
            pow_le_pow_left₀ hU_pos.le (by dsimp only [U]; linarith [norm_nonneg w]) N_all
        _ = 3 ^ N_all * (1 + ‖w‖ + κ_val) ^ N_all := mul_pow _ _ _
    rw [le_div_iff₀ (pow_pos hU_pos _)]
    calc ‖∫ g : C𝔽, φ₀.val g * ideleClassNormTwist (F := F) (χ ω) w g ∂μ𝔽‖ * U ^ N_all
        ≤ ‖∫ g : C𝔽, φ₀.val g * ideleClassNormTwist (F := F) (χ ω) w g ∂μ𝔽‖ *
            (3 ^ N_all * (1 + ‖w‖ + κ_val) ^ N_all) := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = 3 ^ N_all * ((1 + ‖w‖ + κ_val) ^ N_all *
            ‖∫ g : C𝔽, φ₀.val g * ideleClassNormTwist (F := F) (χ ω) w g ∂μ𝔽‖) := by ring
      _ ≤ 3 ^ N_all * (K_m * M_sum) := mul_le_mul_of_nonneg_left (hmellin w hw) (by positivity)
      _ = 3 ^ N_all * K_m * M_sum := by ring
  have hcl := traceNorm_coshSpectral_cluster_le hα hs hαβ hβX χ hχ x Λ hb hj φ₀ ω τ₁ τ₂
    hτ₁₂ hτ₂₁ K hK_in hK_all ϑ hϑd hϑ_up hϑ_ord ℓ φb hℓ hϑ_low hφb_bd
  have hJ : ((∑ z ∈ K, coshStripMult χ a α s z : ℕ) : ℝ) ≤ 6 * CJ' * 3 * U := by
    have hYU : Y_ω + |(k : ℝ)| + 2 ≤ 3 * U := by dsimp only [U]; linarith [abs_nonneg (k : ℝ)]
    have hJ0 : ((∑ z ∈ K, coshStripMult χ a α s z : ℕ) : ℝ) ≤ 6 * CJ' * (Y_ω + |(k : ℝ)| + 2) := by
      simpa only [Nat.cast_sum] using hJ_cnt
    calc ((∑ z ∈ K, coshStripMult χ a α s z : ℕ) : ℝ)
        ≤ 6 * CJ' * (Y_ω + |(k : ℝ)| + 2) := hJ0
      _ ≤ 6 * CJ' * (3 * U) := mul_le_mul_of_nonneg_left hYU (by positivity)
      _ = 6 * CJ' * 3 * U := by ring
  have h_inv_l : 1 / ℓ ≤ c_rect⁻¹ * 2 ^ n_rect * U ^ n_rect := by
    have hpow : (Y_ω + |(k : ℝ)| + 1) ^ n_rect ≤ 2 ^ n_rect * U ^ n_rect := by
      have : Y_ω + |(k : ℝ)| + 1 ≤ 2 * U := by dsimp only [U]; linarith [abs_nonneg (k : ℝ)]
      exact (pow_le_pow_left₀ (by positivity) this _).trans_eq (mul_pow _ _ _)
    dsimp only [ℓ]; rw [one_div_div, div_eq_mul_inv, mul_comm _ c_rect⁻¹]
    exact (mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hc_rect.le)).trans_eq (by ring)
  have hτ_bd : (1 + |τ₁|) ^ 2 ≤ 2 ^ 2 * U ^ 2 := by
    have h1τ : |τ₁| ≤ 2 * |(k : ℝ)| + 1 := abs_le.mpr ⟨by linarith [neg_abs_le (k : ℝ)], by linarith [le_abs_self (k : ℝ)]⟩
    exact (pow_le_pow_left₀ (by positivity) (by dsimp only [U]; linarith) 2).trans_eq (mul_pow _ _ _)
  have hstrip_nn : 0 ≤ stripKernelNormConstant α β s := stripKernelNormConstant_nonneg α β s
  have hrect_nn : 0 ≤ rectInterpolantGaussianConstant X β 0 := rectInterpolantGaussianConstant_nonneg hX0.le 0
  have hφl : φb / ℓ * (1 + |τ₁|) ^ 2 ≤
      (c_rect⁻¹ * 2 ^ n_rect * 2 ^ 2 * 3 ^ N_all * K_m * M_sum) * (U ^ (n_rect + 2) / U ^ N_all) := by
    rw [div_eq_mul_one_div φb ℓ]
    calc φb * (1 / ℓ) * (1 + |τ₁|) ^ 2
        ≤ φb * (c_rect⁻¹ * 2 ^ n_rect * U ^ n_rect) * (2 ^ 2 * U ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h_inv_l (by positivity)) hτ_bd (by positivity) (by positivity)
      _ = (c_rect⁻¹ * 2 ^ n_rect * 2 ^ 2 * 3 ^ N_all * K_m * M_sum) * (U ^ (n_rect + 2) / U ^ N_all) := by
          dsimp only [φb]; rw [pow_add]; ring
  have hprod : ((∑ z ∈ K, coshStripMult χ a α s z : ℕ) : ℝ) *
      (stripKernelNormConstant α β s * (rectInterpolantGaussianConstant X β 0 * (φb / ℓ * (1 + |τ₁|) ^ 2))) ≤
      (6 * CJ' * 3) * (stripKernelNormConstant α β s * (rectInterpolantGaussianConstant X β 0 *
        (c_rect⁻¹ * 2 ^ n_rect * 2 ^ 2 * 3 ^ N_all * K_m * M_sum))) * U ^ (-((N_all - (n_rect + 3) : ℕ) : ℤ)) := by
    have hmain := mul_le_mul hJ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hφl hrect_nn) hstrip_nn)
      (by positivity) (by positivity)
    refine hmain.trans_eq ?_
    have hsplit : N_all = (n_rect + 3) + (N_all - (n_rect + 3)) := (Nat.add_sub_cancel' hN_le).symm
    have hU_rat : U * (U ^ (n_rect + 2) / U ^ N_all) = U ^ (-((N_all - (n_rect + 3) : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_natCast, mul_div_assoc',
        show U * U ^ (n_rect + 2) = U ^ (n_rect + 3) from by rw [← pow_succ'], inv_eq_one_div,
        div_eq_div_iff (pow_ne_zero _ hU_pos.ne') (pow_ne_zero _ hU_pos.ne'), ← pow_add, ← hsplit, one_mul]
    rw [← hU_rat]; ring
  exact hcl.trans ((mul_le_mul_of_nonneg_left hprod (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring))

private lemma traceNorm_piece_active_geom_and_spec_le {a α s β X : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hαβ : α < β) (hβX : β < X) (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) χ hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 32)
    (hS_le : ∑' ι : CoshDefectIndex, coshDefectDerivBound α s δ 0 ι ≤ 1 / 2)
    (ω : PontryaginDual (ideleClassNorm F).ker) (k : ℤ) (τ₁ τ₂ : ℝ)
    (hτ_lo : 2 * (k : ℝ) ≤ τ₁) (hτ_hi : τ₁ ≤ 2 * (k : ℝ) + 1)
    (hτ₁₂ : τ₁ + 1 ≤ τ₂) (hτ₂₁ : τ₂ ≤ τ₁ + 3) (hτ₂_hi : τ₂ ≤ 2 * (k : ℝ) + 3)
    (K : Finset (CoshStripZero (F := F) χ a α))
    (hK_in : ∀ z ∈ K, z.val.1 = ω ∧ τ₁ ≤ z.val.2.2 ∧ z.val.2.2 < τ₂)
    (hK_all : ∀ z : CoshStripZero (F := F) χ a α, z.val.1 = ω → τ₁ ≤ z.val.2.2 → z.val.2.2 < τ₂ → z ∈ K)
    (ϑ : ℂ → ℂ) (hϑd : Differentiable ℂ ϑ) (hϑ_up : ∀ u : ℂ, |u.re| ≤ X + 2 → ‖ϑ u‖ ≤ 1)
    (hϑ_ord : ∀ z : CoshStripZero (F := F) χ a α, z.val.1 = ω →
      (coshStripMult χ a α s z : ℕ∞) ≤ analyticOrderAt ϑ (z.val.2.1 + z.val.2.2 * Complex.I))
    {c_rect : ℝ} (hc_rect : 0 < c_rect) {n_rect : ℕ} {Y_ω : ℝ} (hY_ω : 1 ≤ Y_ω)
    (hϑ_low : ∀ w ∈ rectBoundary (-X) X τ₁ τ₂, c_rect / (Y_ω + |(k : ℝ)| + 1) ^ n_rect ≤ ‖ϑ w‖)
    {CJ' : ℝ} (hCJ' : 0 ≤ CJ')
    (hJ_cnt : (∑ z ∈ K, coshStripMult χ a α s z : ℝ) ≤ 6 * CJ' * (Y_ω + |(k : ℝ)| + 2))
    {κ_val : ℝ} (hκ_nn : 0 ≤ κ_val) (hY_le : Y_ω ≤ 1 + κ_val) {N_all : ℕ} (hN_le : n_rect + 3 ≤ N_all)
    {K_m : ℝ} (hK_m : 0 ≤ K_m) (h_tr : C𝔽) (ψ₀ : BruhatCompactSupport C𝔽)
    (hψ₀ : ∀ y, ψ₀.val y ≠ 0 → |logIdeleClassNorm F y| ≤ δ)
    (hmellin : ∀ (T : ℝ → ℂ) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (M_b : ℕ → ℝ),
      (∀ r ≤ N_all, 0 ≤ M_b r) → (∀ r ≤ N_all, ∀ t : ℝ, |t| ≤ δ → ‖iteratedDeriv r T t‖ ≤ M_b r) →
      ∀ w : ℂ, |w.re| ≤ X →
        (1 + ‖w‖ + κ_val) ^ N_all *
            ‖∫ g : C𝔽, (radialMul (F := F) T hT ψ₀).val g * ideleClassNormTwist (F := F) (χ ω) w g ∂μ𝔽‖ ≤
          K_m * ∑ r ∈ Finset.range (N_all + 1), M_b r) :
    let H_tr := max (((ideleClassNorm F h_tr).val : ℝ) ^ X) (((ideleClassNorm F h_tr).val : ℝ) ^ (-X))
    let C₀ := (‖(coshQuotientEquiv (F := F) a hα hs).symm.toContinuousLinearMap‖ *
      ‖(coshQuotientEquiv (F := F) a hα hs).toContinuousLinearMap‖) *
      ((6 * CJ' * 3) * (stripKernelNormConstant α β s * (rectInterpolantGaussianConstant X β 0 *
        (c_rect⁻¹ * 2 ^ n_rect * 2 ^ 2 * 3 ^ N_all * K_m))))
    let W_tot := ∑' m : ℕ, ∑' w : Fin (m + 1) → CoshDefectIndex,
      ∑ r ∈ Finset.range (N_all + 1), wordDerivMajorant α s δ r (m + 1) w
    let pow_U := (1 + κ_val + |(k : ℝ)|) ^ (-((N_all - (n_rect + 3) : ℕ) : ℤ))
    traceNorm ⟨coshSpectralClusterBlock (F := F) a hα hs (bruhatLeftTranslate h_tr ψ₀) χ x Λ K,
        coshSpectralClusterBlock_mem_nuclear a hα hs _ χ x Λ K⟩ ≤ (C₀ * H_tr) * pow_U ∧
      traceNorm ⟨coshGeometricClusterBlock (F := F) a hα hs (bruhatLeftTranslate h_tr ψ₀) χ x Λ K,
        coshGeometricClusterBlock_mem_nuclear a hα hs _ χ x Λ K⟩ ≤
        (‖coshLeftTranslate (F := F) hα hs h_tr‖ * (C₀ * (1 + W_tot))) * pow_U := by
  intro H_tr C₀ W_tot pow_U
  have hX0 : 0 ≤ X := ((hα.trans_lt hαβ).trans hβX).le
  have hw_re : ∀ w ∈ rectBoundary (-X) X τ₁ τ₂, |w.re| ≤ X := fun w hw ↦ by
    rcases mem_rectBoundary_iff.mp hw with ⟨h1, _⟩ | ⟨_, h2 | h2⟩
    · exact abs_le.mpr h1
    · rw [h2, abs_neg, abs_of_nonneg hX0]
    · rw [h2, abs_of_nonneg hX0]
  have hr1 : radialMul (F := F) (fun _ ↦ 1) contDiff_const ψ₀ = ψ₀ :=
    Subtype.ext (funext fun g ↦ by change (1 : ℂ) * ψ₀.val g = _; simp)
  have hm_base : ∀ w ∈ rectBoundary (-X) X τ₁ τ₂,
      (1 + ‖w‖ + κ_val) ^ N_all * ‖∫ g : C𝔽, ψ₀.val g * ideleClassNormTwist (F := F) (χ ω) w g ∂μ𝔽‖ ≤
        K_m * 1 := fun w hw ↦ by
    have h1d (q : ℕ) : ∀ u : ℝ, iteratedDeriv q (fun _ : ℝ ↦ (1 : ℂ)) u =
        if q = 0 then 1 else 0 := fun u ↦ by
      induction q generalizing u with
      | zero => simp
      | succ q ih =>
          rw [iteratedDeriv_succ,
            show iteratedDeriv q (fun _ : ℝ ↦ (1 : ℂ)) = fun _ ↦ (if q = 0 then 1 else 0) from funext ih,
            deriv_const]; simp
    have h1 := hmellin (fun _ ↦ 1) contDiff_const (fun r ↦ if r = 0 then 1 else 0)
      (fun r _ ↦ by split_ifs <;> norm_num)
      (fun r _ t _ ↦ by rw [h1d r t]; split_ifs <;> norm_num) w (hw_re w hw)
    simpa [hr1, Finset.mem_range] using h1
  have hsp_base : traceNorm ⟨coshSpectralClusterBlock (F := F) a hα hs ψ₀ χ x Λ K,
      coshSpectralClusterBlock_mem_nuclear a hα hs ψ₀ χ x Λ K⟩ ≤ C₀ * pow_U := by
    simpa [C₀, pow_U] using traceNorm_piece_active_word_le hα hs hαβ hβX χ hχ x Λ hb hj ω k τ₁ τ₂
      hτ_lo hτ_hi hτ₁₂ hτ₂₁ hτ₂_hi K hK_in hK_all ϑ hϑd hϑ_up hϑ_ord hc_rect hY_ω hϑ_low
      hCJ' hJ_cnt hκ_nn hY_le hN_le hK_m ψ₀ zero_le_one hm_base
  have hsp_tr : traceNorm ⟨coshSpectralClusterBlock (F := F) a hα hs
      (bruhatLeftTranslate h_tr ψ₀) χ x Λ K,
      coshSpectralClusterBlock_mem_nuclear a hα hs _ χ x Λ K⟩ ≤ (C₀ * H_tr) * pow_U := by
    have hm_tr : ∀ w ∈ rectBoundary (-X) X τ₁ τ₂, (1 + ‖w‖ + κ_val) ^ N_all *
        ‖∫ g : C𝔽, (bruhatLeftTranslate (F := F) h_tr ψ₀).val g *
          ideleClassNormTwist (F := F) (χ ω) w g ∂μ𝔽‖ ≤ K_m * H_tr := fun w hw ↦ by
      rw [integral_bruhatLeftTranslate_mul_ideleClassNormTwist, norm_mul]
      calc (1 + ‖w‖ + κ_val) ^ N_all * _ = ‖ideleClassNormTwist (F := F) (χ ω) w h_tr‖ *
              ((1 + ‖w‖ + κ_val) ^ N_all *
                ‖∫ g : C𝔽, ψ₀.val g * ideleClassNormTwist (F := F) (χ ω) w g ∂μ𝔽‖) := by ring
        _ ≤ H_tr * (K_m * 1) := mul_le_mul (norm_ideleClassNormTwist_le (χ ω) hX0 (hw_re w hw) h_tr)
            (hm_base w hw) (by positivity) (by positivity)
        _ = K_m * H_tr := by ring
    have hH_nn : 0 ≤ H_tr := le_trans (Real.rpow_nonneg (NNReal.coe_nonneg _) _) (le_max_left _ _)
    simpa [C₀, pow_U, mul_assoc] using traceNorm_piece_active_word_le hα hs hαβ hβX χ hχ x Λ hb hj ω k τ₁ τ₂
      hτ_lo hτ_hi hτ₁₂ hτ₂₁ hτ₂_hi K hK_in hK_all ϑ hϑd hϑ_up hϑ_ord hc_rect hY_ω hϑ_low
      hCJ' hJ_cnt hκ_nn hY_le hN_le hK_m (bruhatLeftTranslate h_tr ψ₀) hH_nn hm_tr
  refine ⟨hsp_tr, ?_⟩
  have hgeom_aux (E : nuclearEndomorphisms (CoshIntervalSobolev F α s))
      (hE_eq : E.val = coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s)) :
      traceNorm ⟨((coshGeometricProjection (F := F) a hα hs).comp
          (coshTestAction hα hs (bruhatLeftTranslate h_tr ψ₀))).comp E.val,
          mul_mem_nuclearEndomorphisms_left _ E⟩ ≤
        (‖coshLeftTranslate (F := F) hα hs h_tr‖ * (C₀ * (1 + W_tot))) * pow_U := by
    let B (m : ℕ) (w : Fin (m + 1) → CoshDefectIndex) : ℝ :=
      C₀ * (∑ r ∈ Finset.range (N_all + 1), wordDerivMajorant α s δ r (m + 1) w) * pow_U
    have hC₀_nn : 0 ≤ C₀ := by
      have := stripKernelNormConstant_nonneg α β s
      have := rectInterpolantGaussianConstant_nonneg (β := β) hX0 0; positivity
    obtain ⟨hsw_m, hsw_tot⟩ := summable_wordDerivMajorant_finset_sum hα hs hδ0 hδ1 hS_le N_all
    have hsp_rew (φ₀ : BruhatCompactSupport C𝔽) :
        (⟨((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs φ₀)).comp E.val,
          mul_mem_nuclearEndomorphisms_left _ E⟩ : nuclearEndomorphisms (CoshIntervalSobolev F α s)) =
        ⟨coshSpectralClusterBlock (F := F) a hα hs φ₀ χ x Λ K,
          coshSpectralClusterBlock_mem_nuclear a hα hs φ₀ χ x Λ K⟩ :=
      Subtype.ext (by dsimp [coshSpectralClusterBlock]; rw [hE_eq])
    have hB_word : ∀ (m : ℕ) (w : Fin (m + 1) → CoshDefectIndex),
        traceNorm ⟨((coshSpectralProjection (F := F) a hα hs).comp
            (coshTestAction hα hs (wordTest α s w ψ₀))).comp E.val,
          mul_mem_nuclearEndomorphisms_left _ E⟩ ≤ B m w := fun m w ↦ by
      rw [congrArg traceNorm (hsp_rew (wordTest α s w ψ₀))]
      refine (traceNorm_piece_active_word_le hα hs hαβ hβX χ hχ x Λ hb hj ω k τ₁ τ₂
        hτ_lo hτ_hi hτ₁₂ hτ₂₁ hτ₂_hi K hK_in hK_all ϑ hϑd hϑ_up hϑ_ord hc_rect hY_ω hϑ_low
        hCJ' hJ_cnt hκ_nn hY_le hN_le hK_m (wordTest α s w ψ₀)
        (Finset.sum_nonneg fun r _ ↦ wordDerivMajorant_nonneg hα hδ0 r (m + 1) w)
        fun w' hw' ↦ hmellin (wordProd α s w) (contDiff_wordProd α s w)
          (fun r ↦ wordDerivMajorant α s δ r (m + 1) w) (fun r _ ↦ wordDerivMajorant_nonneg hα hδ0 r (m + 1) w)
          (fun r _ t ht ↦ norm_iteratedDeriv_wordProd_le hα hδ0 r (m + 1) w ht) w' (hw_re w' hw')).trans_eq
        (by dsimp only [B, C₀, pow_U]; ring)
    have hgeom_base := traceNorm_coshGeometric_le_of_word_bound a hα hs E
      (by rw [hE_eq]; exact coshSpectralProjection_comp_coshClusterProj a hα hs x Λ K _ _) hδ0 hδ1 hS_le ψ₀ hψ₀ B
      (fun m w ↦ mul_nonneg (mul_nonneg hC₀_nn (Finset.sum_nonneg fun r _ ↦
        wordDerivMajorant_nonneg hα hδ0 r (m + 1) w)) (zpow_nonneg (by linarith [abs_nonneg (k : ℝ)]) _))
      (fun m ↦ ((hsw_m m).mul_left C₀).mul_right pow_U)
      (by simpa [B, tsum_mul_left, tsum_mul_right] using (hsw_tot.mul_left C₀).mul_right pow_U) hB_word
    obtain ⟨hN, htr⟩ := traceNorm_coshGeometric_translate_le a hα hs E h_tr ψ₀
    calc traceNorm ⟨_, mul_mem_nuclearEndomorphisms_left _ E⟩
        = traceNorm ⟨_, hN⟩ := congrArg traceNorm (Subtype.ext rfl)
      _ ≤ ‖coshLeftTranslate (F := F) hα hs h_tr‖ *
            (traceNorm ⟨((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs ψ₀)).comp E.val, _⟩ +
              traceNorm ⟨((coshGeometricProjection (F := F) a hα hs).comp (coshTestAction hα hs ψ₀)).comp E.val, _⟩) :=
          htr
      _ ≤ ‖coshLeftTranslate (F := F) hα hs h_tr‖ * (C₀ * pow_U + C₀ * W_tot * pow_U) := by
          rw [congrArg traceNorm (hsp_rew ψ₀)]
          exact mul_le_mul_of_nonneg_left (add_le_add hsp_base (hgeom_base.trans_eq (by
            simp [B, W_tot, tsum_mul_left, tsum_mul_right]))) (norm_nonneg _)
      _ = (‖coshLeftTranslate (F := F) hα hs h_tr‖ * (C₀ * (1 + W_tot))) * pow_U := by ring
  exact (congrArg traceNorm (Subtype.ext rfl)).trans_le (hgeom_aux ⟨coshClusterProj (F := F) a hα hs x Λ K
    (coshStripMult χ a α s) (coshStripJet χ a α s), coshClusterProj_mem_nuclear a hα hs x Λ K _ _⟩ rfl)

/-- Positive-width (`α ≥ 0`, `s ≥ 0`) cluster trace-norm summability for both geometric and
spectral cluster blocks at any section-trivial spectral basepoint choice `χ`. -/
theorem coshSpectralStripGeometricBlocks_clusters_summable_of_section
    (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport C𝔽) (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (hχ1 : χ 1 = 1)
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : Function.RightInverse τ (ideleClassNorm F))
    (hχτ : ∀ ω (t : ℝ≥0ˣ), χ ω (τ t) = 1)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) χ hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    ∃ K : (PontryaginDual (ideleClassNorm F).ker × ℤ) → Finset (CoshStripZero (F := F) χ a α),
      (∀ p₁ p₂, p₁ ≠ p₂ → Disjoint (K p₁) (K p₂)) ∧
      (∀ z : CoshStripZero (F := F) χ a α, ∃ p, z ∈ K p) ∧
      (∀ p z, z ∈ K p → z.val.1 = p.1) ∧
      Summable (fun p ↦ traceNorm ⟨coshGeometricClusterBlock (F := F) a hα hs φ χ x Λ (K p),
        coshGeometricClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩) ∧
      Summable (fun p ↦ traceNorm ⟨coshSpectralClusterBlock (F := F) a hα hs φ χ x Λ (K p),
        coshSpectralClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩) := by
  classical
  obtain ⟨δ, hδ0_pos, hδ1, hS_le⟩ := exists_delta_coshDefect_tsum_le_half hα hs
  have hδ0 : 0 ≤ δ := hδ0_pos.le
  obtain ⟨M, h_tr, ψ, hψ_supp, hφ_eq, _⟩ := exists_radial_partition_bruhat φ hδ0_pos
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · let K : (PontryaginDual (ideleClassNorm F).ker × ℤ) → Finset (CoshStripZero (F := F) χ a α) :=
      fun ⟨ω, k⟩ ↦ (spectralStripComponent_finite_window a χ ω (2 * (k : ℝ)) (2 * ((k + 1 : ℤ) : ℝ))).toFinset
    have hK_mem (ω : PontryaginDual (ideleClassNorm F).ker) (k : ℤ) (z : CoshStripZero (F := F) χ a α) :
        z ∈ K (ω, k) ↔ z.val.1 = ω ∧ 2 * (k : ℝ) ≤ z.val.2.2 ∧ z.val.2.2 < 2 * ((k + 1 : ℤ) : ℝ) :=
      (spectralStripComponent_finite_window a χ ω _ _).mem_toFinset
    refine ⟨K, fun p₁ p₂ hne ↦ Finset.disjoint_left.mpr fun z hz₁ hz₂ ↦ ?_,
      fun z ↦ ⟨(z.val.1, Int.floor (z.val.2.2 / 2)), (hK_mem _ _ z).mpr
        ⟨rfl, by have := Int.floor_le (z.val.2.2 / 2); linarith,
          by have := Int.lt_floor_add_one (z.val.2.2 / 2); push_cast; linarith⟩⟩,
      fun p z hz ↦ ((hK_mem p.1 p.2 z).mp hz).1, ?_, ?_⟩
    · rcases p₁ with ⟨ω₁, k₁⟩; rcases p₂ with ⟨ω₂, k₂⟩
      obtain ⟨hω₁, _, _⟩ := (hK_mem ω₁ k₁ z).mp hz₁
      obtain ⟨hω₂, _, _⟩ := (hK_mem ω₂ k₂ z).mp hz₂
      have hωeq : ω₁ = ω₂ := hω₁.symm.trans hω₂
      subst hωeq
      rcases lt_or_gt_of_ne (fun hk ↦ hne (Prod.ext rfl hk)) with hlt | hlt
      · have hle : (2 * ((k₁ + 1 : ℤ) : ℝ)) ≤ 2 * (k₂ : ℝ) := by
          exact_mod_cast Int.mul_le_mul_of_nonneg_left (show k₁ + 1 ≤ k₂ from hlt) (by norm_num)
        linarith [(hK_mem ω₁ k₁ z).mp hz₁ |>.2.2, (hK_mem ω₁ k₂ z).mp hz₂ |>.2.1]
      · have hle : (2 * ((k₂ + 1 : ℤ) : ℝ)) ≤ 2 * (k₁ : ℝ) := by
          exact_mod_cast Int.mul_le_mul_of_nonneg_left (show k₂ + 1 ≤ k₁ from hlt) (by norm_num)
        linarith [(hK_mem ω₁ k₁ z).mp hz₁ |>.2.1, (hK_mem ω₁ k₂ z).mp hz₂ |>.2.2]
    · have hφ0 : φ = 0 := Subtype.ext (funext fun g ↦ by rw [hφ_eq]; simp)
      have hact0 : coshTestAction (F := F) hα hs φ = 0 := by
        rw [hφ0]; exact (coshTestAction_isLinear (F := F) hα hs).map_zero
      have h0 : ∀ p, traceNorm ⟨coshGeometricClusterBlock (F := F) a hα hs φ χ x Λ (K p),
          coshGeometricClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩ = 0 := fun p ↦ by
        have hsub0 : (⟨coshGeometricClusterBlock (F := F) a hα hs φ χ x Λ (K p),
            coshGeometricClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩ :
            nuclearEndomorphisms (CoshIntervalSobolev F α s)) = 0 :=
          Subtype.ext (by ext1 u; simp [coshGeometricClusterBlock, hact0])
        rw [hsub0, traceNorm_zero_hilb]
      simp_rw [h0]; exact summable_zero
    · have hφ0 : φ = 0 := Subtype.ext (funext fun g ↦ by rw [hφ_eq]; simp)
      have hact0 : coshTestAction (F := F) hα hs φ = 0 := by
        rw [hφ0]; exact (coshTestAction_isLinear (F := F) hα hs).map_zero
      have h0 : ∀ p, traceNorm ⟨coshSpectralClusterBlock (F := F) a hα hs φ χ x Λ (K p),
          coshSpectralClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩ = 0 := fun p ↦ by
        have hsub0 : (⟨coshSpectralClusterBlock (F := F) a hα hs φ χ x Λ (K p),
            coshSpectralClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩ :
            nuclearEndomorphisms (CoshIntervalSobolev F α s)) = 0 :=
          Subtype.ext (by ext1 u; simp [coshSpectralClusterBlock, hact0])
        rw [hsub0, traceNorm_zero_hilb]
      simp_rw [h0]; exact summable_zero
  · have hsp := fun j : Fin M ↦ exists_uniform_radialMul_spectralLevel τ hτ hδ0 (ψ j) (hψ_supp j)
    choose κ A₀ kg _ hκ_nn h_arch h_cnt h_van h_mellin using hsp
    choose C_cnt d_cnt hC_cnt using h_cnt
    let S_j (j : Fin M) : Set (PontryaginDual (ideleClassNorm F).ker) :=
      {ω | (∀ u ∈ kg j, χ ω u = 1) ∧ heckeLogDiscriminantConductor (χ ω) ≤ A₀ j}
    let A_all : ℝ := ∑ j : Fin M, max (A₀ j) 0
    obtain ⟨β, X, hαβ, hβX, hrect⟩ := exists_uniform_heckeMultiplier_rectBoundary F a α
    obtain ⟨c_rect, n_rect, hc_rect, hrect_all⟩ := hrect A_all
    have hρ : 0 < |a - 2| + α + 2 := by positivity
    obtain ⟨C_J1, hC_J1_nn, hC_J1⟩ := continuedCompletedHeckeL_one_closedBall_zeros_le_log F hρ
    obtain ⟨C_J, _, hC_J⟩ := continuedCompletedHeckeL_closedBall_zeros_le_log_uniform F hρ A_all
    let CJ' : ℝ := max C_J C_J1
    have hCJ'_nn : 0 ≤ CJ' := le_trans hC_J1_nn (le_max_right _ _)
    let d_max : ℕ := Finset.univ.sup d_cnt
    let N_all : ℕ := n_rect + d_max + 7
    have hX0 : 0 ≤ X := ((hα.trans_lt hαβ).trans hβX).le
    choose K_m hK_m_nn hK_m using fun j : Fin M ↦ h_mellin j X N_all
    let j0 : Fin M := ⟨0, hM⟩
    let J_ω (ω : PontryaginDual (ideleClassNorm F).ker) : Finset (Fin M) :=
      Finset.univ.filter (fun j ↦ ω ∈ S_j j)
    let hJ_ne {ω : PontryaginDual (ideleClassNorm F).ker} (h : ∃ j : Fin M, ω ∈ S_j j) :
        (J_ω ω).Nonempty :=
      let ⟨j, hj⟩ := h; ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    let Y_ω (ω : PontryaginDual (ideleClassNorm F).ker) : ℝ :=
      if h : ∃ j : Fin M, ω ∈ S_j j then 1 + (J_ω ω).inf' (hJ_ne h) (fun j ↦ κ j (χ ω))
      else 1 + κ j0 (χ ω)
    have hY_ge1 (ω : PontryaginDual (ideleClassNorm F).ker) : 1 ≤ Y_ω ω := by
      dsimp only [Y_ω]; split_ifs with h
      · obtain ⟨j', _, hj'⟩ := Finset.exists_mem_eq_inf' (hJ_ne h) (fun j ↦ κ j (χ ω))
        rw [hj']; linarith [hκ_nn j' (χ ω)]
      · linarith [hκ_nn j0 (χ ω)]
    have hY_le (ω : PontryaginDual (ideleClassNorm F).ker) (j : Fin M) (hjω : ω ∈ S_j j) :
        Y_ω ω ≤ 1 + κ j (χ ω) := by
      have hex : ∃ j', ω ∈ S_j j' := ⟨j, hjω⟩
      have hinf : (J_ω ω).inf' (hJ_ne hex) (fun j' ↦ κ j' (χ ω)) ≤ κ j (χ ω) :=
        Finset.inf'_le (fun j' ↦ κ j' (χ ω)) (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjω⟩)
      have hYeq : Y_ω ω = 1 + (J_ω ω).inf' (hJ_ne hex) (fun j' ↦ κ j' (χ ω)) := by
        dsimp only [Y_ω]; split_ifs; rfl
      linarith
    have h_arch_Y (ω : PontryaginDual (ideleClassNorm F).ker) : ∀ w : NumberField.InfinitePlace F,
        if hw : w.IsReal then ‖(realHeckeCharacter_parameters (χ ω) w hw).exists.choose.1‖ ≤ Y_ω ω
        else let p := (complexHeckeCharacter_parameters (χ ω) w
            (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
          ‖p.1‖ ≤ Y_ω ω ∧ (p.2.natAbs : ℝ) ≤ Y_ω ω := by
      dsimp only [Y_ω]; split_ifs with h
      · obtain ⟨j', _, heq⟩ := Finset.exists_mem_eq_inf' (hJ_ne h) (fun j ↦ κ j (χ ω))
        rw [heq]; exact h_arch j' (χ ω) (hχτ ω)
      · exact h_arch j0 (χ ω) (hχτ ω)
    have hrect_exists (ω : PontryaginDual (ideleClassNorm F).ker) (hω : ∃ j : Fin M, ω ∈ S_j j) :
        ∃ (ϑ : ℂ → ℂ) (T : ℤ → ℝ), Differentiable ℂ ϑ ∧
          (∀ u : ℂ, ↑(meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) (↑a + u)).untop₀.toNat ≤
            analyticOrderAt ϑ u) ∧
          (∀ u : ℂ, |u.re| ≤ X + 2 → ‖ϑ u‖ ≤ 1) ∧
          (∀ k : ℤ, T k ∈ Set.Icc (2 * (k : ℝ)) (2 * (k : ℝ) + 1)) ∧
          ∀ k : ℤ, ∀ w ∈ rectBoundary (-X) X (T k) (T (k + 1)),
            c_rect / (Y_ω ω + |(k : ℝ)| + 1) ^ n_rect ≤ ‖ϑ w‖ := by
      refine hrect_all (χ ω) ?_ (Y_ω ω) (hY_ge1 ω) (h_arch_Y ω)
      by_cases h1 : ω = 1
      · exact Or.inl (by rw [h1, hχ1])
      · obtain ⟨j, hjω⟩ := hω
        have hne1 : (χ ω).toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 := fun heq ↦ h1 (by
          rw [← hχ ω]; ext1 u; exact DFunLike.congr_fun heq u)
        exact Or.inr ⟨hne1, hjω.2.trans ((le_max_left _ _).trans
          (Finset.single_le_sum (fun _ _ ↦ le_max_right _ _) (Finset.mem_univ j)))⟩
    let T (ω : PontryaginDual (ideleClassNorm F).ker) : ℤ → ℝ :=
      if h : ∃ j : Fin M, ω ∈ S_j j then (hrect_exists ω h).choose_spec.choose else fun k ↦ 2 * (k : ℝ)
    have hT_icc (ω : PontryaginDual (ideleClassNorm F).ker) (k : ℤ) :
        T ω k ∈ Set.Icc (2 * (k : ℝ)) (2 * (k : ℝ) + 1) := by
      dsimp only [T]; split_ifs with h
      · exact (hrect_exists ω h).choose_spec.choose_spec.2.2.2.1 k
      · exact ⟨le_rfl, by linarith⟩
    let K : (PontryaginDual (ideleClassNorm F).ker × ℤ) → Finset (CoshStripZero (F := F) χ a α) :=
      fun ⟨ω, k⟩ ↦ (spectralStripComponent_finite_window a χ ω (T ω k) (T ω (k + 1))).toFinset
    have hK_mem (ω : PontryaginDual (ideleClassNorm F).ker) (k : ℤ) (z : CoshStripZero (F := F) χ a α) :
        z ∈ K (ω, k) ↔ z.val.1 = ω ∧ T ω k ≤ z.val.2.2 ∧ z.val.2.2 < T ω (k + 1) :=
      (spectralStripComponent_finite_window a χ ω _ _).mem_toFinset
    have hT_le_of_le (ω : PontryaginDual (ideleClassNorm F).ker) {k₁ k₂ : ℤ} (h : k₁ ≤ k₂) :
        T ω k₁ ≤ T ω k₂ := by
      rcases eq_or_lt_of_le h with rfl | hlt
      · exact le_rfl
      · have hk : (k₁ : ℝ) + 1 ≤ k₂ := by exact_mod_cast hlt
        linarith [(hT_icc ω k₁).2, (hT_icc ω k₂).1]
    have hpiece (j : Fin M) : ∃ D_j E_j : ℝ, 0 ≤ D_j ∧ 0 ≤ E_j ∧
        ∀ p : PontryaginDual (ideleClassNorm F).ker × ℤ,
          traceNorm ⟨coshGeometricClusterBlock (F := F) a hα hs
              (bruhatLeftTranslate (h_tr j) (ψ j)) χ x Λ (K p),
              coshGeometricClusterBlock_mem_nuclear a hα hs _ χ x Λ (K p)⟩ ≤
            (if p.1 ∈ S_j j then D_j * (1 + κ j (χ p.1) + |(p.2 : ℝ)|) ^ (-((d_cnt j + 4 : ℕ) : ℤ)) else 0) ∧
          traceNorm ⟨coshSpectralClusterBlock (F := F) a hα hs
              (bruhatLeftTranslate (h_tr j) (ψ j)) χ x Λ (K p),
              coshSpectralClusterBlock_mem_nuclear a hα hs _ χ x Λ (K p)⟩ ≤
            (if p.1 ∈ S_j j then E_j * (1 + κ j (χ p.1) + |(p.2 : ℝ)|) ^ (-((d_cnt j + 4 : ℕ) : ℤ)) else 0) := by
      let H_tr := max (((ideleClassNorm F (h_tr j)).val : ℝ) ^ X) (((ideleClassNorm F (h_tr j)).val : ℝ) ^ (-X))
      let C₀ := (‖(coshQuotientEquiv (F := F) a hα hs).symm.toContinuousLinearMap‖ *
        ‖(coshQuotientEquiv (F := F) a hα hs).toContinuousLinearMap‖) *
        ((6 * CJ' * 3) * (stripKernelNormConstant α β s * (rectInterpolantGaussianConstant X β 0 *
          (c_rect⁻¹ * 2 ^ n_rect * 2 ^ 2 * 3 ^ N_all * K_m j))))
      let W_tot := ∑' m : ℕ, ∑' w : Fin (m + 1) → CoshDefectIndex,
        ∑ r ∈ Finset.range (N_all + 1), wordDerivMajorant α s δ r (m + 1) w
      let D_j := ‖coshLeftTranslate (F := F) hα hs (h_tr j)‖ * (C₀ * (1 + W_tot))
      let E_j := C₀ * H_tr
      have hC₀_nn : 0 ≤ C₀ := by
        have := stripKernelNormConstant_nonneg α β s
        have := rectInterpolantGaussianConstant_nonneg (β := β) hX0 0; have := hK_m_nn j; positivity
      have hW_nn : 0 ≤ W_tot := tsum_nonneg fun m ↦ tsum_nonneg fun w ↦
        Finset.sum_nonneg fun r _ ↦ wordDerivMajorant_nonneg hα hδ0 r (m + 1) w
      have hH_nn : 0 ≤ H_tr := le_trans (Real.rpow_nonneg (NNReal.coe_nonneg _) _) (le_max_left _ _)
      have hD_nn : 0 ≤ D_j := mul_nonneg (norm_nonneg _) (mul_nonneg hC₀_nn (by linarith))
      refine ⟨D_j, E_j, hD_nn, mul_nonneg hC₀_nn hH_nn, fun ⟨ω, k⟩ ↦ ?_⟩
      by_cases hjω : ω ∈ S_j j
      · simp only [hjω, ↓reduceIte]
        have hex : ∃ j', ω ∈ S_j j' := ⟨j, hjω⟩
        let ϑ := (hrect_exists ω hex).choose
        have hϑ_prop := (hrect_exists ω hex).choose_spec.choose_spec
        have hT_eq : T ω = (hrect_exists ω hex).choose_spec.choose := by dsimp only [T]; split_ifs; rfl
        have hτ₂_hi : T ω (k + 1) ≤ 2 * (k : ℝ) + 3 := by
          have := (hT_icc ω (k + 1)).2; push_cast at this; linarith
        have hτ₁₂ : T ω k + 1 ≤ T ω (k + 1) := by
          have := (hT_icc ω (k + 1)).1; push_cast at this; linarith [(hT_icc ω k).2]
        have hτ₂₁ : T ω (k + 1) ≤ T ω k + 3 := by linarith [(hT_icc ω k).1]
        have hJ_cnt : ((∑ z ∈ K (ω, k), coshStripMult χ a α s z : ℕ) : ℝ) ≤
            6 * CJ' * (Y_ω ω + |(k : ℝ)| + 2) := by
          have hC_ball : ∀ S' : Finset ℂ,
              (∀ w ∈ S', w ∈ Metric.closedBall (⟨2, T ω k + 3 / 2⟩ : ℂ) (|a - 2| + α + 2)) →
              ∑ w ∈ S', ((meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) w).untop₀.toNat : ℝ) ≤
                CJ' * Real.log (Y_ω ω + |T ω k + 3 / 2| + 2) := fun S' hS' ↦ by
            have hlog0 : 0 ≤ Real.log (Y_ω ω + |T ω k + 3 / 2| + 2) :=
              Real.log_nonneg (by linarith [hY_ge1 ω, abs_nonneg (T ω k + 3 / 2)])
            by_cases h1 : ω = 1
            · rw [h1, hχ1]
              exact (hC_J1 (T 1 k + 3 / 2) S' (by simpa [h1] using hS')).trans
                (mul_le_mul (le_max_right _ _)
                  (Real.log_le_log (by linarith [abs_nonneg (T 1 k + 3 / 2)])
                    (by linarith [hY_ge1 1, h1]))
                  (Real.log_nonneg (by linarith [abs_nonneg (T 1 k + 3 / 2)])) hCJ'_nn)
            · have hne1 : (χ ω).toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 := fun heq ↦ h1 (by
                rw [← hχ ω]; ext1 u; exact DFunLike.congr_fun heq u)
              exact (hC_J (χ ω) hne1 (hjω.2.trans ((le_max_left _ _).trans
                  (Finset.single_le_sum (fun _ _ ↦ le_max_right _ _) (Finset.mem_univ j))))
                (Y_ω ω) (hY_ge1 ω) (h_arch_Y ω) (T ω k + 3 / 2) S' hS').trans
                (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0)
          have h1 := coshJetCount_le_of_closedBall (α := α) (s := s) a χ ω hC_ball (K (ω, k)) fun z hz ↦
            ⟨((hK_mem ω k z).mp hz).1, ((hK_mem ω k z).mp hz).2.1, ((hK_mem ω k z).mp hz).2.2.le.trans hτ₂₁⟩
          have hlog := Real.log_le_sub_one_of_pos (show 0 < Y_ω ω + |T ω k + 3 / 2| + 2 by
            linarith [hY_ge1 ω, abs_nonneg (T ω k + 3 / 2)])
          have hT_abs : |T ω k + 3 / 2| ≤ 2 * |(k : ℝ)| + 5 / 2 := (abs_add_le (T ω k) (3 / 2)).trans (by
            have : |T ω k| ≤ 2 * |(k : ℝ)| + 1 := abs_le.mpr
              ⟨by linarith [(hT_icc ω k).1, neg_abs_le (k : ℝ)], by linarith [(hT_icc ω k).2, le_abs_self (k : ℝ)]⟩
            rw [show |(3 / 2 : ℝ)| = 3 / 2 from abs_of_pos (by norm_num)]; linarith)
          exact h1.trans ((mul_le_mul_of_nonneg_left (show Real.log (Y_ω ω + |T ω k + 3 / 2| + 2) ≤
            6 * (Y_ω ω + |(k : ℝ)| + 2) by linarith [hY_ge1 ω, abs_nonneg (k : ℝ)]) hCJ'_nn).trans_eq (by ring))
        have hN_dec : d_cnt j + 4 ≤ N_all - (n_rect + 3) := by
          have hd : d_cnt j ≤ d_max := Finset.le_sup (Finset.mem_univ j); dsimp only [N_all]; omega
        have hact := traceNorm_piece_active_geom_and_spec_le hα hs hαβ hβX χ hχ x Λ hb hj
          hδ0 hδ1 hS_le ω k (T ω k) (T ω (k + 1)) (hT_icc ω k).1 (hT_icc ω k).2 hτ₁₂ hτ₂₁ hτ₂_hi
          (K (ω, k)) (fun z hz ↦ (hK_mem ω k z).mp hz) (fun z h1 h2 h3 ↦ (hK_mem ω k z).mpr ⟨h1, h2, h3⟩)
          ϑ hϑ_prop.1 hϑ_prop.2.2.1
          (fun z hz ↦ spectralStripMultiplicity_le_analyticOrderAt a χ z
            (fun u ↦ by rw [hz]; exact hϑ_prop.2.1 u))
          hc_rect (hY_ge1 ω) (by simpa [hT_eq] using hϑ_prop.2.2.2.2 k) hCJ'_nn
          (by simpa only [Nat.cast_sum] using hJ_cnt)
          (hκ_nn j (χ ω)) (hY_le ω j hjω) (by dsimp only [N_all]; omega) (hK_m_nn j) (h_tr j) (ψ j)
          (hψ_supp j) (fun T' hT' M_b hM1 hM2 w' hw' ↦ hK_m j T' hT' M_b hM1 hM2 (χ ω) (hχτ ω) w' hw')
        have hpow_le : (1 + κ j (χ ω) + |(k : ℝ)|) ^ (-((N_all - (n_rect + 3) : ℕ) : ℤ)) ≤
            (1 + κ j (χ ω) + |(k : ℝ)|) ^ (-((d_cnt j + 4 : ℕ) : ℤ)) :=
          zpow_le_zpow_right₀ (by linarith [hκ_nn j (χ ω), abs_nonneg (k : ℝ)])
            (Int.neg_le_neg (Int.ofNat_le.mpr hN_dec))
        exact ⟨hact.2.trans (mul_le_mul_of_nonneg_left hpow_le hD_nn),
          hact.1.trans (mul_le_mul_of_nonneg_left hpow_le (mul_nonneg hC₀_nn hH_nn))⟩
      · simp only [hjω, ↓reduceIte]
        have h0 := traceNorm_piece_inactive_eq_zero hα hs χ x Λ hb hj hδ0 hδ1 hS_le
          (h_tr j) (ψ j) (hψ_supp j) ω (fun T' hT' w' ↦ by
            by_contra hne; exact hjω (h_van j T' hT' (χ ω) w' hne))
          (K (ω, k)) (fun z hz ↦ ((hK_mem ω k z).mp hz).1)
        exact ⟨h0.2.le, h0.1.le⟩
    choose D E_b _ _ hDE_le using hpiece
    have h_piece_sum (j : Fin M) (c_j : ℝ) : Summable (fun p : PontryaginDual (ideleClassNorm F).ker × ℤ ↦
        if p.1 ∈ S_j j then c_j * (1 + κ j (χ p.1) + |(p.2 : ℝ)|) ^ (-((d_cnt j + 4 : ℕ) : ℤ))
        else 0) := by
      have h_base := summable_inv_pow_of_encard_poly (S_j j) (fun ω ↦ κ j (χ ω))
        (fun ω _ ↦ hκ_nn j (χ ω)) (C_cnt j) (d_cnt j) fun T_cnt ↦ by
        have hinj : Function.Injective (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽) :=
          fun ω₁ ω₂ h ↦ by rw [← hχ ω₁, ← hχ ω₂, h]
        have hsub : χ '' {ω : PontryaginDual (ideleClassNorm F).ker | ω ∈ S_j j ∧ κ j (χ ω) ≤ (T_cnt : ℝ)} ⊆
            {χ' : PontryaginDual C𝔽 | (∀ t : ℝ≥0ˣ, χ' (τ t) = 1) ∧ (∀ u ∈ kg j, χ' u = 1) ∧ κ j χ' ≤ (T_cnt : ℝ)} := by
          rintro _ ⟨ω, ⟨hSω, hκω⟩, rfl⟩; exact ⟨hχτ ω, hSω.1, hκω⟩
        calc {ω : PontryaginDual (ideleClassNorm F).ker | ω ∈ S_j j ∧ κ j (χ ω) ≤ (T_cnt : ℝ)}.encard
            = (χ '' _).encard := (hinj.injOn.encard_image).symm
          _ ≤ _ := (Set.encard_mono hsub).trans (hC_cnt j T_cnt)
      refine (h_base.mul_left c_j).congr fun ⟨ω, k⟩ ↦ ?_; split_ifs <;> simp [mul_zero]
    have h_proj_sum (P : CoshIntervalSobolev F α s →L[ℂ] CoshIntervalSobolev F α s) (c_fn : Fin M → ℝ)
        (hc : ∀ j p, traceNorm ⟨(P.comp (coshTestAction hα hs (bruhatLeftTranslate (h_tr j) (ψ j)))).comp
            (coshClusterProj a hα hs x Λ (K p) (coshStripMult χ a α s) (coshStripJet χ a α s)),
            mul_mem_nuclearEndomorphisms_left _ ⟨_, coshClusterProj_mem_nuclear a hα hs x Λ (K p) _ _⟩⟩ ≤
          if p.1 ∈ S_j j then c_fn j * (1 + κ j (χ p.1) + |(p.2 : ℝ)|) ^ (-((d_cnt j + 4 : ℕ) : ℤ)) else 0) :
        Summable (fun p ↦ traceNorm ⟨(P.comp (coshTestAction hα hs φ)).comp
          (coshClusterProj a hα hs x Λ (K p) (coshStripMult χ a α s) (coshStripJet χ a α s)),
          mul_mem_nuclearEndomorphisms_left _ ⟨_, coshClusterProj_mem_nuclear a hα hs x Λ (K p) _ _⟩⟩) := by
      refine (summable_sum fun j (_ : j ∈ Finset.univ) ↦ h_piece_sum j (c_fn j)).of_nonneg_of_le
        (fun _ ↦ traceNorm_nonneg_hilb _) fun p ↦ ?_
      have hsub : (⟨(P.comp (coshTestAction hα hs φ)).comp
            (coshClusterProj a hα hs x Λ (K p) (coshStripMult χ a α s) (coshStripJet χ a α s)),
            mul_mem_nuclearEndomorphisms_left _ ⟨_, coshClusterProj_mem_nuclear a hα hs x Λ (K p) _ _⟩⟩ :
            nuclearEndomorphisms (CoshIntervalSobolev F α s)) =
          ⟨(P.comp (coshTestAction hα hs (∑ j : Fin M, bruhatLeftTranslate (h_tr j) (ψ j)))).comp
            (coshClusterProj a hα hs x Λ (K p) (coshStripMult χ a α s) (coshStripJet χ a α s)),
            mul_mem_nuclearEndomorphisms_left _ ⟨_, coshClusterProj_mem_nuclear a hα hs x Λ (K p) _ _⟩⟩ := by
        apply Subtype.ext; rw [← hφ_eq]
      rw [congrArg traceNorm hsub]
      exact (traceNorm_proj_cluster_sum_le a hα hs P Finset.univ _ χ x Λ (K p)).trans
        (Finset.sum_le_sum fun j _ ↦ hc j p)
    refine ⟨K, fun p₁ p₂ hne ↦ Finset.disjoint_left.mpr fun z hz₁ hz₂ ↦ ?_,
      fun z ↦ ?_, fun p z hz ↦ ((hK_mem p.1 p.2 z).mp hz).1,
      (h_proj_sum (coshGeometricProjection (F := F) a hα hs) D fun j p ↦
        (congrArg traceNorm (Subtype.ext rfl)).trans_le (hDE_le j p).1).congr fun _ ↦ congrArg traceNorm (Subtype.ext rfl),
      (h_proj_sum (coshSpectralProjection (F := F) a hα hs) E_b fun j p ↦
        (congrArg traceNorm (Subtype.ext rfl)).trans_le (hDE_le j p).2).congr fun _ ↦ congrArg traceNorm (Subtype.ext rfl)⟩
    · rcases p₁ with ⟨ω₁, k₁⟩; rcases p₂ with ⟨ω₂, k₂⟩
      obtain ⟨hω₁, _, _⟩ := (hK_mem ω₁ k₁ z).mp hz₁
      obtain ⟨hω₂, _, _⟩ := (hK_mem ω₂ k₂ z).mp hz₂
      have hωeq : ω₁ = ω₂ := hω₁.symm.trans hω₂; subst hωeq
      rcases lt_or_gt_of_ne (fun hk ↦ hne (Prod.ext rfl hk)) with hlt | hlt
      · linarith [hT_le_of_le ω₁ hlt, (hK_mem ω₁ k₁ z).mp hz₁ |>.2.2, (hK_mem ω₁ k₂ z).mp hz₂ |>.2.1]
      · linarith [hT_le_of_le ω₁ hlt, (hK_mem ω₁ k₁ z).mp hz₁ |>.2.1, (hK_mem ω₁ k₂ z).mp hz₂ |>.2.2]
    · let k₀ : ℤ := Int.floor (z.val.2.2 / 2)
      by_cases hlt : z.val.2.2 < T z.val.1 k₀
      · exact ⟨(z.val.1, k₀ - 1), (hK_mem _ _ z).mpr ⟨rfl, by
          have h1 := Int.floor_le (z.val.2.2 / 2); have h2 := (hT_icc z.val.1 (k₀ - 1)).2; push_cast at h2; linarith,
          by simpa using hlt⟩⟩
      · exact ⟨(z.val.1, k₀), (hK_mem _ _ z).mpr ⟨rfl, not_lt.mp hlt, by
          have h1 := Int.lt_floor_add_one (z.val.2.2 / 2); have h2 := (hT_icc z.val.1 (k₀ + 1)).1; push_cast at h1 h2; linarith⟩⟩

end PositiveWidthSummability

end RiemannMasullo.Isolated.CoshPositiveWidth
