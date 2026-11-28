module

public import RiemannMasullo.AppC_LCTVS.Sec3a
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # Removing a line from a subspace: the trace of the compression

Let `V` be a closed subspace of a Hilbert space, `k` a nonzero vector of `V`, and `V'` the
vectors of `V` orthogonal to `k`. The orthogonal projection onto `V'` is the projection onto
`V` minus the rank-one projection onto the line of `k`. Hence, for a bounded operator `T` whose
compression to `V` is nuclear, the compression to `V'` is nuclear and

`Tr (P' T P') = Tr (P T P) - ⟪k, T k⟫ / ‖k‖ ^ 2`.

* `starProjection_inf_orthogonal_span_singleton`: the projection onto `V'`.
* `hilbertTrace_compression_inf_orthogonal_span_singleton`: the trace of the compression.
-/

open scoped InnerProductSpace

@[expose] public noncomputable section

namespace RiemannMasullo

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The orthogonal projection onto the vectors of `V` orthogonal to a nonzero `k ∈ V` is the
projection onto `V` minus the rank-one projection onto the line of `k`. -/
theorem starProjection_inf_orthogonal_span_singleton {V : Submodule ℂ H}
    [V.HasOrthogonalProjection] {k : H} (hk : k ∈ V) (hk0 : k ≠ 0)
    [(V ⊓ (ℂ ∙ k)ᗮ).HasOrthogonalProjection] :
    (V ⊓ (ℂ ∙ k)ᗮ).starProjection =
      V.starProjection - (((‖k‖ : ℂ) ^ 2)⁻¹ • innerSL ℂ k).smulRight k := by
  have hn0 : (‖k‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hk0).ne'
  have hkk : ⟪k, k⟫_ℂ = (‖k‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K k
  have hPk : V.starProjection k = k := Submodule.starProjection_eq_self_iff.mpr hk
  ext1 x
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := V ⊓ (ℂ ∙ k)ᗮ)
    (Submodule.mem_inf.mpr ⟨?_, ?_⟩) ?_
  · exact V.sub_mem (Submodule.starProjection_apply_mem V x) (V.smul_mem _ hk)
  · rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp only [sub_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
      innerSL_apply_apply, smul_eq_mul, inner_sub_right, inner_smul_right]
    rw [← Submodule.inner_starProjection_left_eq_right V k x, hPk, hkk]
    field_simp
    ring
  · intro v hv
    obtain ⟨hvV, hvk⟩ := Submodule.mem_inf.mp hv
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hvk
    simp only [sub_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
      innerSL_apply_apply, smul_eq_mul]
    rw [sub_sub_eq_add_sub, add_sub_right_comm, inner_add_left, inner_smul_left, hvk, mul_zero,
      add_zero]
    exact Submodule.starProjection_inner_eq_zero x v hvV

/-- **The trace of the compression after removing a line.** If the compression of `T` to `V` is
nuclear and `k` is a nonzero vector of `V`, then the compression of `T` to the vectors of `V`
orthogonal to `k` is nuclear, and its trace is that of the compression to `V` minus
`⟪k, T k⟫ / ‖k‖ ^ 2`. -/
theorem hilbertTrace_compression_inf_orthogonal_span_singleton {V : Submodule ℂ H}
    [V.HasOrthogonalProjection] {k : H} (hk : k ∈ V) (hk0 : k ≠ 0)
    [(V ⊓ (ℂ ∙ k)ᗮ).HasOrthogonalProjection] (T : H →L[ℂ] H)
    (hn : IsNuclearOperator (V.starProjection ∘L T ∘L V.starProjection)) :
    ∃ hn' : IsNuclearOperator ((V ⊓ (ℂ ∙ k)ᗮ).starProjection ∘L T ∘L
        (V ⊓ (ℂ ∙ k)ᗮ).starProjection),
      hilbertTrace ⟨_, hn'⟩ = hilbertTrace ⟨_, hn⟩ - ⟪k, T k⟫_ℂ / (‖k‖ : ℂ) ^ 2 := by
  have hn0 : (‖k‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hk0).ne'
  have hkk : ⟪k, k⟫_ℂ = (‖k‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K k
  have hPk : V.starProjection k = k := Submodule.starProjection_eq_self_iff.mpr hk
  set c : ℂ := ((‖k‖ : ℂ) ^ 2)⁻¹ with hc
  set P := V.starProjection with hP
  -- the three rank-one corrections
  let φ₁ : H →L[ℂ] ℂ := c • (innerSL ℂ k ∘L T ∘L P)
  let φ₂ : H →L[ℂ] ℂ := c • innerSL ℂ k
  let y₂ : H := P (T k)
  let y₃ : H := (c * ⟪k, T k⟫_ℂ) • k
  have hdecomp : (V ⊓ (ℂ ∙ k)ᗮ).starProjection ∘L T ∘L (V ⊓ (ℂ ∙ k)ᗮ).starProjection =
      P ∘L T ∘L P - φ₁.smulRight k - φ₂.smulRight y₂ + φ₂.smulRight y₃ := by
    rw [starProjection_inf_orthogonal_span_singleton hk hk0]
    ext1 x
    simp only [ContinuousLinearMap.comp_apply, sub_apply, add_apply,
      ContinuousLinearMap.smulRight_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, map_sub,
      map_smul, φ₁, φ₂, y₂, y₃, ← hc, ← hP]
    module
  have hn1 : IsNuclearOperator (φ₁.smulRight k) := isNuclearOperator_smulRight φ₁ k
  have hn2 : IsNuclearOperator (φ₂.smulRight y₂) := isNuclearOperator_smulRight φ₂ y₂
  have hn3 : IsNuclearOperator (φ₂.smulRight y₃) := isNuclearOperator_smulRight φ₂ y₃
  have hmem : IsNuclearOperator (P ∘L T ∘L P - φ₁.smulRight k - φ₂.smulRight y₂ +
      φ₂.smulRight y₃) :=
    (nuclearEndomorphisms H).add_mem ((nuclearEndomorphisms H).sub_mem
      ((nuclearEndomorphisms H).sub_mem hn hn1) hn2) hn3
  refine ⟨hdecomp ▸ hmem, ?_⟩
  obtain ⟨f, hf⟩ := hilbertTrace_linear (H := H)
  have hsub : (⟨(V ⊓ (ℂ ∙ k)ᗮ).starProjection ∘L T ∘L (V ⊓ (ℂ ∙ k)ᗮ).starProjection,
      hdecomp ▸ hmem⟩ : nuclearEndomorphisms H) =
      (⟨P ∘L T ∘L P, hn⟩ : nuclearEndomorphisms H) - ⟨φ₁.smulRight k, hn1⟩ -
        ⟨φ₂.smulRight y₂, hn2⟩ + ⟨φ₂.smulRight y₃, hn3⟩ := Subtype.ext hdecomp
  rw [hsub, ← hf, map_add, map_sub, map_sub, hf, hf, hf, hf]
  have h1 := hilbertTrace_smulRight φ₁ k
  have h2 := hilbertTrace_smulRight φ₂ y₂
  have h3 := hilbertTrace_smulRight φ₂ y₃
  rw [show (⟨φ₁.smulRight k, hn1⟩ : nuclearEndomorphisms H) =
      ⟨φ₁.smulRight k, smulRight_mem_nuclearEndomorphisms φ₁ k⟩ from rfl, h1,
    show (⟨φ₂.smulRight y₂, hn2⟩ : nuclearEndomorphisms H) =
      ⟨φ₂.smulRight y₂, smulRight_mem_nuclearEndomorphisms φ₂ y₂⟩ from rfl, h2,
    show (⟨φ₂.smulRight y₃, hn3⟩ : nuclearEndomorphisms H) =
      ⟨φ₂.smulRight y₃, smulRight_mem_nuclearEndomorphisms φ₂ y₃⟩ from rfl, h3]
  simp only [φ₁, φ₂, y₂, y₃, smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul, inner_smul_right, hPk, hkk]
  rw [← Submodule.inner_starProjection_left_eq_right V k (T k), hPk, hc]
  field_simp
  ring

end RiemannMasullo
