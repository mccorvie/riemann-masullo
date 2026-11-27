module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.CutoffWeak
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic

open Set Filter MeasureTheory
open scoped FourierTransform SchwartzMap Real Topology

@[expose] public noncomputable section

namespace RiemannMasullo.WeakCardinal

local notation "D" => SchwartzMap.derivCLM ℂ ℂ
local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

private def weight (ξ : ℝ) := 1+(2*Real.pi*ξ)^2

private theorem weight_pos (ξ : ℝ) : 0 < weight ξ := by unfold weight; positivity

private theorem inv_weight_temperate : (fun x ↦ (weight x)⁻¹).HasTemperateGrowth := by
  have ht : (fun x : ℝ ↦ 2*Real.pi*x).HasTemperateGrowth := by fun_prop
  have h := (Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (-1)).comp ht
  simpa only [weight, Function.comp_def, Real.rpow_neg_one, Real.norm_eq_abs, sq_abs] using h

private def weightedFourierCore : 𝓢(ℝ, ℂ) →L[ℂ] H :=
  ((Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.comp (SchwartzMap.toLpCLM ℂ ℂ 2 volume)).comp
    (ContinuousLinearMap.id ℂ _ - (SchwartzMap.derivCLM ℂ ℂ).comp D)

private theorem weightedFourierCore_eq (f : 𝓢(ℝ, ℂ)) :
    weightedFourierCore f = (𝓕 (graphH2 f)).toLp 2 volume := by
  change 𝓕 ((graphH2 f).toLp 2 volume) = _
  exact SchwartzMap.toLp_fourier_eq _

private theorem weightedFourierCore_dense : DenseRange weightedFourierCore := by
  apply (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (μ := volume) (p := 2)
    ENNReal.ofNat_ne_top).mono
  rintro _ ⟨φ, rfl⟩
  let v := SchwartzMap.smulLeftCLM ℂ (fun ξ ↦ (weight ξ)⁻¹) φ
  refine ⟨𝓕⁻ v, ?_⟩
  rw [weightedFourierCore_eq]
  change (𝓕 (graphH2 (𝓕⁻ v))).toLp 2 volume = φ.toLp 2 volume
  congr 1
  ext ξ
  rw [fourier_graphH2, FourierTransform.fourier_fourierInv_eq]
  change (weight ξ : ℂ) * v ξ = φ ξ
  rw [show v ξ = (weight ξ)⁻¹ • φ ξ from SchwartzMap.smulLeftCLM_apply_apply inv_weight_temperate _ _,
    Complex.real_smul, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀, one_mul]
  exact_mod_cast (weight_pos ξ).ne'

private def inverseWeight : H →L[ℂ] H :=
  boundedRealMultiplier (fun ξ ↦ (weight ξ)⁻¹) (by unfold weight; fun_prop) (K := 1)
    (fun ξ ↦ by
      rw [abs_of_pos (inv_pos.mpr (weight_pos ξ))]
      exact inv_le_one_of_one_le₀ (by unfold weight; nlinarith [sq_nonneg (2*Real.pi*ξ)]))

private theorem inverseWeight_iff (j f : H) :
    inverseWeight j = f ↔ (j : ℝ → ℂ) =ᵐ[volume] fun ξ ↦ weight ξ • f ξ := by
  have he : (inverseWeight j : ℝ → ℂ) =ᵐ[volume] fun ξ ↦ (weight ξ)⁻¹ • j ξ :=
    boundedRealMultiplier_apply_ae _ _ _ _
  constructor
  · rintro rfl
    filter_upwards [he] with ξ hξ
    rw [hξ, smul_smul, mul_inv_cancel₀ (weight_pos ξ).ne', one_smul]
  · intro hh
    apply Lp.ext
    filter_upwards [he, hh] with ξ hξ hξ'
    rw [hξ, hξ', smul_smul, inv_mul_cancel₀ (weight_pos ξ).ne', one_smul]

private theorem inverseWeight_injective : Function.Injective inverseWeight := by
  intro f g he
  apply Lp.ext
  exact ((inverseWeight_iff f (inverseWeight g)).mp he).trans
    ((inverseWeight_iff g (inverseWeight g)).mp rfl).symm

private theorem inverseWeight_core (φ : 𝓢(ℝ, ℂ)) :
    inverseWeight (weightedFourierCore φ) = 𝓕 (φ.toLp 2 volume) := by
  apply (inverseWeight_iff _ _).mpr
  rw [weightedFourierCore_eq, SchwartzMap.toLp_fourier_eq]
  filter_upwards [(𝓕 (graphH2 φ)).coeFn_toLp 2 volume, (𝓕 φ).coeFn_toLp 2 volume] with ξ hj hf
  rw [hj, hf, fourier_graphH2, Complex.real_smul]
  rfl

/-- Extend a compatible bound on a dense Hilbert graph to its full domain. -/
private theorem lift_closed_graph {S : Type*} [AddCommGroup S] [Module ℂ S]
    (e : S →ₗ[ℂ] H) (he : DenseRange e) (M T : H →L[ℂ] H) (hi : Function.Injective M) (B : ℝ)
    (h : ∀ s, ∃ k : H, M k = T (M (e s)) ∧ ‖k‖ ≤ B * ‖e s‖) :
    ∃ U : H →L[ℂ] H, (∀ j, M (U j) = T (M j)) ∧ ∀ j, ‖U j‖ ≤ B * ‖j‖ := by
  choose v hv hb using h
  let V : S →ₗ[ℂ] H := {
    toFun := v
    map_add' := fun x y ↦ hi (by rw [map_add, hv, hv, hv, map_add, map_add, map_add])
    map_smul' := fun c x ↦ hi (by simp only [map_smul, RingHom.id_apply, hv]) }
  let U := V.extendOfNorm e
  have hU (s : S) : U (e s) = v s := LinearMap.extendOfNorm_eq he ⟨B, hb⟩ s
  refine ⟨U, ?_, LinearMap.norm_extendOfNorm_apply_le he B hb⟩
  intro j
  exact he.induction_on (p := fun j ↦ M (U j) = T (M j)) j
    (isClosed_eq (M.continuous.comp U.continuous) (T.continuous.comp M.continuous))
    (fun s ↦ (congrArg M (hU s)).trans (hv s))

/-- The unscaled physical multiplication conjugated by the Plancherel isometry. -/
def fourierScaledCutoffQuotient (w : ℝ) {R : ℝ} (hR : 0 < R) : H →L[ℂ] H :=
  ((Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.comp (scaledCutoffQuotientL2 w hR)).comp
    (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem fourierScaledCutoffQuotient_norm_le (w : ℝ) {R : ℝ} (hR : 0 < R) :
    ‖fourierScaledCutoffQuotient w hR‖ ≤ (9/8)/R := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖(Lp.fourierTransformₗᵢ ℝ ℂ) (scaledCutoffQuotientL2 w hR ((Lp.fourierTransformₗᵢ ℝ ℂ).symm f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  convert (scaledCutoffQuotientL2 w hR).le_of_opNorm_le (scaledCutoffQuotientL2_norm_le w hR)
    ((Lp.fourierTransformₗᵢ ℝ ℂ).symm f) using 1
  rw [LinearIsometryEquiv.norm_map]

/-- For every weighted Fourier input, the `H²` output is the Fourier conjugate of
the same unweighted spatial multiplier. The weight uses angular frequency `2πξ`. -/
theorem fourierScaledCutoffQuotient_full_endpoint (w : ℝ) {R : ℝ} (hR : 0 < R) (f j : H)
    (hj : (j : ℝ → ℂ) =ᵐ[volume] fun ξ ↦ (1+(2*Real.pi*ξ)^2) • f ξ) :
    ∃ k : H, (k : ℝ → ℂ) =ᵐ[volume] (fun ξ ↦ (1+(2*Real.pi*ξ)^2) •
      fourierScaledCutoffQuotient w hR f ξ) ∧
      ‖k‖ ≤ ((9/8)/R + 2/R^2 + 6/R^3)*‖j‖ := by
  let T := fourierScaledCutoffQuotient w hR
  let B := (9/8)/R + 2/R^2 + 6/R^3
  have hcore (φ : 𝓢(ℝ, ℂ)) : ∃ k : H, inverseWeight k = T (inverseWeight (weightedFourierCore φ)) ∧
      ‖k‖ ≤ B * ‖weightedFourierCore φ‖ := by
    obtain ⟨k, hk, hn⟩ := exists_fourier_graph_scaledCutoffQuotient w hR φ
    refine ⟨k, ?_, ?_⟩
    · rw [inverseWeight_core]
      change inverseWeight k = (Lp.fourierTransformₗᵢ ℝ ℂ) (scaledCutoffQuotientL2 w hR ((Lp.fourierTransformₗᵢ ℝ ℂ).symm ((Lp.fourierTransformₗᵢ ℝ ℂ) (φ.toLp 2 volume))))
      rw [LinearIsometryEquiv.symm_apply_apply]
      exact (inverseWeight_iff _ _).mpr hk
    · change ‖k‖ ≤ B*‖𝓕 ((graphH2 φ).toLp 2 volume)‖
      simpa only [Lp.norm_fourier_eq] using hn
  obtain ⟨U, hU, hn⟩ := lift_closed_graph weightedFourierCore.toLinearMap weightedFourierCore_dense
    inverseWeight T inverseWeight_injective B hcore
  refine ⟨U j, (inverseWeight_iff _ _).mp ?_, hn j⟩
  rw [hU, (inverseWeight_iff _ _).mpr hj]

theorem fourierScaledCutoffQuotient_full_endpoint_six (w : ℝ) (f j : H)
    (hj : (j : ℝ → ℂ) =ᵐ[volume] fun ξ ↦ (1+(2*Real.pi*ξ)^2) • f ξ) :
    ∃ k : H, (k : ℝ → ℂ) =ᵐ[volume] (fun ξ ↦ (1+(2*Real.pi*ξ)^2) •
      fourierScaledCutoffQuotient w (R := 6) (by norm_num) f ξ) ∧ ‖k‖ ≤ (13/48)*‖j‖ := by
  simpa only [radius_six_multiplier_constant] using fourierScaledCutoffQuotient_full_endpoint w
    (R := 6) (by norm_num) f j hj

end RiemannMasullo.WeakCardinal
