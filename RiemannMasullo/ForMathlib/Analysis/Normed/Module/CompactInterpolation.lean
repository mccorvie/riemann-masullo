module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant

/-! # Finite linear interpolation on compact sets -/

public section

namespace RiemannMasullo

open Function Module Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-- A compact set spanning a finite-dimensional space admits a basis from the set
in which every point of the set has coordinates of norm at most one. -/
theorem exists_basis_compact_coord_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X] {S : Set X}
    (hS : IsCompact S) (hspan : Submodule.span 𝕜 S = ⊤) :
    ∃ b : Basis (Fin (finrank 𝕜 X)) 𝕜 X, (∀ i, b i ∈ S) ∧
      ∀ i x, x ∈ S → ‖b.coord i x‖ ≤ 1 := by
  classical
  obtain ⟨s, hs, hss, hli⟩ := exists_linearIndependent 𝕜 S
  let b : Basis s 𝕜 X := Basis.mk hli (by simp [hss, hspan])
  let e := b.reindex (b.indexEquiv (finBasis 𝕜 X))
  have he (i) : e i ∈ S := by
    rw [show e i = _ from Basis.reindex_apply .., show ∀ j, b j = j.val from fun j ↦ Basis.mk_apply ..]
    exact hs (b.indexEquiv (finBasis 𝕜 X) |>.symm i).property
  let A := univ.pi (fun _ : Fin (finrank 𝕜 X) ↦ S)
  have hc : Continuous (fun v ↦ ‖e.det v‖) := by
    simp only [Basis.det_apply]
    apply Continuous.norm
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (e.coord i).continuous_of_finiteDimensional.comp (continuous_apply j)
  obtain ⟨v, hv, hmax⟩ := (isCompact_univ_pi (fun _ ↦ hS)).exists_isMaxOn
    (s := A) ⟨e, fun i _ ↦ he i⟩ hc.continuousOn
  have hpos : 0 < ‖e.det v‖ := lt_of_lt_of_le (show 0 < ‖e.det e‖ by rw [e.det_self]; simp) (hmax (show (e : _ → X) ∈ A from
    fun i _ ↦ he i))
  obtain ⟨hl, ht⟩ := e.is_basis_iff_det.mpr (isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hpos))
  let c := Basis.mk hl ht.ge
  refine ⟨c, fun i ↦ (Basis.mk_apply hl ht.ge i) ▸ hv i (mem_univ i), ?_⟩
  intro i x hx
  have hdet := DFunLike.congr_fun (e.det_smul_mk_coord_eq_det_update hl ht.ge i) x
  change e.det v * c.coord i x = e.det (update v i x) at hdet
  have hmem : update v i x ∈ A := by
    intro j _
    by_cases hji : j = i
    · simpa [hji] using hx
    · simpa [Function.update_of_ne hji] using hv j (mem_univ j)
  have hh := hmax hmem
  change ‖e.det (update v i x)‖ ≤ ‖e.det v‖ at hh
  rwa [← hdet, norm_mul, mul_le_iff_le_one_right hpos] at hh

/-- Simultaneous interpolation of finitely many linear observations on a compact set. -/
theorem exists_compact_interpolant {X Y : Type*} [AddCommGroup X] [Module 𝕜 X]
    [TopologicalSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [FiniteDimensional 𝕜 Y]
    {B : Set X} (hB : IsCompact B) (J : X →L[𝕜] Y) :
    ∃ (d : ℕ) (b : Fin d → B) (c : Fin d → Y →L[𝕜] 𝕜), d ≤ finrank 𝕜 Y ∧
      (∀ i x, x ∈ B → ‖c i (J x)‖ ≤ 1) ∧
      ∀ x ∈ B, ∑ i, c i (J x) • J (b i) = J x := by
  classical
  let S := J '' B
  let V := Submodule.span 𝕜 S
  let K := (Subtype.val : V → Y) ⁻¹' S
  have hK : IsCompact K := V.isClosed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isCompact_preimage (hB.image J.continuous)
  obtain ⟨b, hb, hc⟩ := exists_basis_compact_coord_le hK (Submodule.span_span_coe_preimage)
  choose t ht hj using (fun i ↦ (show (b i).val ∈ J '' B from hb i))
  obtain ⟨π, hπ⟩ := V.subtype.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr V.subtype_injective)
  have hπ' (x : V) : π x.val = x := DFunLike.congr_fun hπ x
  let c (i) := ((b.coord i).comp π).toContinuousLinearMap
  refine ⟨_, fun i ↦ ⟨t i, ht i⟩, c, V.finrank_le, ?_, ?_⟩
  · intro i x hx
    let y : V := ⟨J x, Submodule.subset_span ⟨x, hx, rfl⟩⟩
    change ‖b.coord i (π y.val)‖ ≤ 1
    rw [hπ']
    exact hc i y ⟨x, hx, rfl⟩
  · intro x hx
    let y : V := ⟨J x, Submodule.subset_span ⟨x, hx, rfl⟩⟩
    have hh := congrArg V.subtype (b.sum_repr y)
    simp only [map_sum, map_smul, Submodule.subtype_apply] at hh
    change ∑ i, b.coord i (π y.val) • J (t i) = _
    simpa only [hπ', hj, Basis.coord_apply] using hh

end RiemannMasullo
