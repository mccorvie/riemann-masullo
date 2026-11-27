module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatPolarCutoff
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatLogHeat

/-!
# Heat regularization of the flat polar correction

In the rational real-even flat block of (12.4.1.8), the full band and the
mean-zero band differ by one polar direction. For the relative trace the
heat error depends only on the motion of that direction. This is the
finite-rank part of mrshu's heat regularization of the local trace in #7354.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped CompactlySupported InnerProductSpace NNReal Topology

namespace RiemannMasullo.FlatPolar

section Relative

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Removing the projected polar line gives a difference of two explicit rank-one
operators. Both the source and target vectors in this formula are regularized by
the same self-adjoint map. -/
theorem sandwich_compressionDifference_eq_two_rows (S T : H →L[ℂ] H)
    (hS : IsSelfAdjoint S) (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    {e : H} (he : ‖e‖ = 1) :
    let E := K.starProjection
    let P := E - (ℂ ∙ e).starProjection
    let w := ⟪e, T e⟫_ℂ • e - E (T e)
    let v := E (T.adjoint e)
    S.comp ((P.comp (T.comp P) - E.comp (T.comp E)).comp S) =
      (innerSL ℂ (S e)).smulRight (S w) - (innerSL ℂ (S v)).smulRight (S e) := by
  have hs : ∀ x y : H, ⟪S x, y⟫_ℂ = ⟪x, S y⟫_ℂ :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hS
  ext x
  simp only [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, Submodule.starProjection_unit_singleton ℂ he, hs,
    K.inner_starProjection_left_eq_right, T.adjoint_inner_left, map_sub, map_smul]
  module

/-- The heat sandwich of the two-sided compression difference is nuclear. Its trace
differs from minus the polar matrix coefficient by at most the movement of the unit
polar vector under two applications of the self-adjoint operator, times `2 ‖T‖`. -/
theorem exists_sandwich_compressionDifference (S T : H →L[ℂ] H) (hS : IsSelfAdjoint S)
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] {e : H} (he : ‖e‖ = 1) (hK : e ∈ K) :
    let E := K.starProjection
    let P := E - (ℂ ∙ e).starProjection
    ∃ R : nuclearEndomorphisms H,
      R.val = S.comp ((P.comp (T.comp P) - E.comp (T.comp E)).comp S) ∧
      ‖hilbertTrace R + ⟪e, T e⟫_ℂ‖ ≤ 2 * ‖T‖ * ‖S (S e) - e‖ := by
  let E := K.starProjection
  let c := ⟪e, T e⟫_ℂ
  let w := c • e - E (T e)
  let v := E (T.adjoint e)
  let z := S (S e) - e
  let U : nuclearEndomorphisms H := ⟨(innerSL ℂ (S e)).smulRight (S w),
    smulRight_mem_nuclearEndomorphisms _ _⟩
  let V : nuclearEndomorphisms H := ⟨(innerSL ℂ (S v)).smulRight (S e),
    smulRight_mem_nuclearEndomorphisms _ _⟩
  refine ⟨U - V, (sandwich_compressionDifference_eq_two_rows S T hS K he).symm, ?_⟩
  have hs : ∀ x y : H, ⟪S x, y⟫_ℂ = ⟪x, S y⟫_ℂ :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hS
  have hEe : E e = e := Submodule.starProjection_eq_self_iff.mpr hK
  have hc : ⟪e, E (T e)⟫_ℂ = c := (K.inner_starProjection_left_eq_right _ _).symm.trans
    (congrArg (⟪·, T e⟫_ℂ) hEe)
  have hw : ⟪e, w⟫_ℂ = 0 := by
    simp only [w, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, he, hc]
    simp
  have hv : ⟪v, e⟫_ℂ = c := by
    simp only [v, E, K.inner_starProjection_left_eq_right, T.adjoint_inner_left,
      show K.starProjection e = e from hEe, c]
  have hwNorm : ‖w‖ ≤ ‖T‖ := by
    have hy := (ℂ ∙ e)ᗮ.norm_starProjection_apply_le (E (T e))
    rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_unit_singleton ℂ he, hc,
      norm_sub_rev] at hy
    exact (hy.trans (K.norm_starProjection_apply_le _)).trans (by simpa [he] using T.le_opNorm e)
  have hvNorm : ‖v‖ ≤ ‖T‖ := (K.norm_starProjection_apply_le _).trans (by
    simpa [he, ContinuousLinearMap.adjoint.norm_map] using T.adjoint.le_opNorm e)
  have htrace : hilbertTrace (U - V) + c = ⟪z, w⟫_ℂ - ⟪v, z⟫_ℂ := by
    obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
    rw [← htr, map_sub, htr, htr,
      show hilbertTrace U = ⟪S e, S w⟫_ℂ from hilbertTrace_smulRight _ _,
      show hilbertTrace V = ⟪S v, S e⟫_ℂ from hilbertTrace_smulRight _ _,
      ← hs (S e) w, hs v (S e), show S (S e) = e + z by simp [z],
      inner_add_left, inner_add_right, hw, hv]
    abel
  rw [htrace]
  calc
    _ ≤ ‖⟪z, w⟫_ℂ‖ + ‖⟪v, z⟫_ℂ‖ := norm_sub_le _ _
    _ ≤ ‖z‖ * ‖T‖ + ‖T‖ * ‖z‖ := add_le_add
      ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hwNorm (norm_nonneg _)))
      ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hvNorm (norm_nonneg _)))
    _ = _ := by change _ = 2 * ‖T‖ * ‖z‖; ring

end Relative

section Spatial

local notation "ν" => volume.restrict (Ioi (0 : ℝ))
local notation "H" => Lp ℂ 2 ν

private theorem norm_spatialCutoffInChart_le_one (V : H →ₗᵢ[ℂ] H) (h L : ℝ) :
    ‖spatialCutoffInChart V h L‖ ≤ 1 := by
  calc
    _ ≤ ‖V.toContinuousLinearMap.adjoint‖ * ‖(spatialCutoff h L).comp V.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (1 * 1) := by
      apply mul_le_mul _ _ (norm_nonneg _) zero_le_one
      · simpa only [ContinuousLinearMap.adjoint.norm_map] using V.norm_toContinuousLinearMap_le
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (norm_spatialCutoff_le _ _) V.norm_toContinuousLinearMap_le
            (norm_nonneg _) zero_le_one)
    _ = _ := by norm_num

/-- In the inverse cosine chart, it suffices to control the action of the two
regularizers on the moving polar vector. Both orthogonal projections, the spatial
cutoff, and the gated dilation action occur in the bounded operator inside the trace. -/
private theorem exists_spatialCompressionDifference_sandwich_tendsto
    {ι : Type*} {l : Filter ι} {B h L : ι → ℝ} (hB : ∀ i, 0 < B i)
    (hh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hL : Tendsto (fun i ↦ B i * L i) l atTop)
    (φ : C_c(ℝ≥0ˣ, ℂ)) (Q : ℝ → ℂ) (hQ : Measurable Q)
    (C : ℝ) (hC : 0 ≤ C) (hQC : ∀ t, ‖Q t‖ ≤ C)
    (S : ι → H →L[ℂ] H) (hS : ∀ i, IsSelfAdjoint (S i))
    (he : Tendsto (fun i ↦ ‖S i (S i (bandVector (B i))) - bandVector (B i)‖) l (𝓝 0)) :
    let T (i : ι) := (spatialCutoffInChart positiveRayInverseCosine (h i) (L i)).comp
      ((compactDilationAction φ).comp (positiveRayMultiplier Q hQ C hC hQC (B i)))
    let E (i : ι) := (frequencyBand (B i)).starProjection
    let P (i : ι) := (meanZeroFrequencyBand (B i)).starProjection
    ∃ R : ι → nuclearEndomorphisms H,
      (∀ i, (R i).val = (S i).comp
        (((P i).comp ((T i).comp (P i)) - (E i).comp ((T i).comp (E i))).comp (S i))) ∧
      Tendsto (fun i ↦ hilbertTrace (R i)) l (𝓝 (-(∫ a : ℝ≥0ˣ,
        φ a * ((Real.sqrt a.val : ℂ)⁻¹ * ∫ u in Ioc 0 (min 1 (a.val : ℝ)), Q u)
          ∂positiveRealHaar))) := by
  let M (i : ι) := positiveRayMultiplier Q hQ C hC hQC (B i)
  let T (i : ι) := (spatialCutoffInChart positiveRayInverseCosine (h i) (L i)).comp
    ((compactDilationAction φ).comp (M i))
  let e (i : ι) := bandVector (B i)
  have hT (i : ι) : ‖T i‖ ≤ ‖compactDilationAction φ‖ * C := by
    calc
      _ ≤ ‖spatialCutoffInChart positiveRayInverseCosine (h i) (L i)‖ *
          ‖(compactDilationAction φ).comp (M i)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (‖compactDilationAction φ‖ * C) := by
        apply mul_le_mul (norm_spatialCutoffInChart_le_one _ _ _) _ (norm_nonneg _) zero_le_one
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (positiveRayMultiplier_norm_le Q hQ C hC hQC (B i)) (norm_nonneg _))
      _ = _ := one_mul _
  choose R hR hm using fun i ↦ exists_sandwich_compressionDifference (S i) (T i) (hS i)
    (frequencyBand (B i)) (norm_bandVector (hB i)) (bandVector_mem_frequencyBand (B i))
  refine ⟨R, fun i ↦ by simpa only [frequencyBand_starProjection_sub_line] using hR i, ?_⟩
  have hzero : Tendsto (fun i ↦ hilbertTrace (R i) + ⟪e i, T i (e i)⟫_ℂ) l (𝓝 0) := by
    refine squeeze_zero_norm (fun i ↦ (hm i).trans <| mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hT i) (by norm_num)) (norm_nonneg _)) ?_
    simpa using he.const_mul (2 * (‖compactDilationAction φ‖ * C))
  have hp := tendsto_hilbertTrace_compactDilation_multiplier_spatial hB hh hL φ Q hQ C hC hQC
  simp only [polarRankOne, hilbertTrace_smulRight, innerSL_apply_apply] at hp
  simpa only [Pi.sub_apply, add_sub_cancel_right, zero_sub, e, T, M] using hzero.sub hp

/-- Reconstruction of the polar part of the heat trace in Theorem 12.4.1.1,
pp. 516–518, in the rational real-even block at order zero. The nuclear difference
of the heat-regularized mean-zero and full compressions has limit minus the gated
polar integral. The heat variance may shrink independently of the band and the
spatial floor and ceiling, subject to `Bh → 0` and `BL → ∞`. -/
theorem exists_logHeat_spatialCompressionDifference_tendsto
    {ι : Type*} {l : Filter ι} {B h L : ι → ℝ} {τ : ι → ℝ≥0} (hB : ∀ i, 0 < B i)
    (hh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hL : Tendsto (fun i ↦ B i * L i) l atTop)
    (hτ : Tendsto τ l (𝓝 0)) (φ : C_c(ℝ≥0ˣ, ℂ)) (Q : ℝ → ℂ) (hQ : Measurable Q)
    (C : ℝ) (hC : 0 ≤ C) (hQC : ∀ t, ‖Q t‖ ≤ C) :
    let S (i : ι) := logHeat (τ i)
    let T (i : ι) := (spatialCutoffInChart positiveRayInverseCosine (h i) (L i)).comp
      ((compactDilationAction φ).comp (positiveRayMultiplier Q hQ C hC hQC (B i)))
    let E (i : ι) := (frequencyBand (B i)).starProjection
    let P (i : ι) := (meanZeroFrequencyBand (B i)).starProjection
    ∃ R : ι → nuclearEndomorphisms H,
      (∀ i, (R i).val = (S i).comp
        (((P i).comp ((T i).comp (P i)) - (E i).comp ((T i).comp (E i))).comp (S i))) ∧
      Tendsto (fun i ↦ hilbertTrace (R i)) l (𝓝 (-(∫ a : ℝ≥0ˣ,
        φ a * ((Real.sqrt a.val : ℂ)⁻¹ * ∫ u in Ioc 0 (min 1 (a.val : ℝ)), Q u)
          ∂positiveRealHaar))) := by
  have hτ₂ : Tendsto (fun i ↦ τ i + τ i) l (𝓝 0) := by simpa only [zero_add] using hτ.add hτ
  have he := tendsto_logHeat_sub_bandVector hτ₂ B hB
  simp only [logHeat_add] at he
  exact exists_spatialCompressionDifference_sandwich_tendsto hB hh hL φ Q hQ C hC hQC
    (fun i ↦ logHeat (τ i)) (fun i ↦ isSelfAdjoint_logHeat (τ i)) he

end Spatial

end RiemannMasullo.FlatPolar
