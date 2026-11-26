module

public import RiemannMasullo.AppC_LCTVS.Sec3a
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Transport of a nuclear trace along an isometry

* `IsNuclearOperator.clm_comp`: a nuclear operator between Banach spaces followed by a continuous
  linear map is nuclear. The proof moves the vectors of a nuclear series.
* `hilbertTrace_eq_of_isometry_intertwining`: if `U : W → H` is a linear isometry of Hilbert
  spaces, `T` is nuclear on `H` with range in the range of `U`, and `U ∘ S = T ∘ U`, then `S` is
  nuclear on `W` and has the trace of `T`. The proof applies Lemma C.3.2.2, p. 695
  (`nuclearTrace_factor_comps`), to the injection `U` and the nuclear map `U† ∘ T`.
-/

open MeasureTheory Set Filter Topology Function
open scoped InnerProductSpace

@[expose] public noncomputable section

namespace RiemannMasullo

section Banach

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

/-- A nuclear operator between Banach spaces followed by a continuous linear map is nuclear. -/
theorem IsNuclearOperator.clm_comp {A : E →L[ℂ] F} (hA : IsNuclearOperator A) (C : F →L[ℂ] G) :
    IsNuclearOperator (C ∘L A) := by
  rw [isNuclearOperator_iff_isBanachNuclear] at hA ⊢
  obtain ⟨c, φ, y, hc, hφ, hy, hsum⟩ := hA
  refine ⟨c, φ, fun n ↦ C (y n), hc, hφ, ?_, fun x ↦ ?_⟩
  · have h := (C.continuous.tendsto 0).comp hy
    simpa only [map_zero, Function.comp_def] using h
  · have h := C.hasSum (hsum x)
    simpa only [ContinuousLinearMap.comp_apply, map_smul] using h

end Banach

section Hilbert

variable {W H : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem nuclearTrace_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {A B : E →L[ℂ] E} (h : A = B) (hA : IsNuclearOperator A)
    (hB : IsNuclearOperator B) :
    nuclearTrace hilbert_approximationProperty A hA =
      nuclearTrace hilbert_approximationProperty B hB := by
  subst h
  rfl

/-- **Transport of a trace along an isometry.** Let `U : W → H` be a linear isometry of Hilbert
spaces, `T` a nuclear operator on `H` whose range lies in the range of `U`, and `S` an operator
on `W` with `U ∘ S = T ∘ U`. Then `S` is nuclear and has the trace of `T`. -/
theorem hilbertTrace_eq_of_isometry_intertwining (U : W →ₗᵢ[ℂ] H) (T : nuclearEndomorphisms H)
    (S : W →L[ℂ] W)
    (hint : U.toContinuousLinearMap ∘L S = T.val ∘L U.toContinuousLinearMap)
    (hrange : U.toContinuousLinearMap ∘L
      (ContinuousLinearMap.adjoint U.toContinuousLinearMap ∘L T.val) = T.val) :
    ∃ hS : IsNuclearOperator S, hilbertTrace ⟨S, hS⟩ = hilbertTrace T := by
  set Uc := U.toContinuousLinearMap with hUc
  set Ua := ContinuousLinearMap.adjoint Uc with hUa
  have hUU : Ua ∘L Uc = ContinuousLinearMap.id ℂ W :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self Uc).mp U.norm_map
  have hA₀ : IsNuclearOperator (Ua ∘L T.val) := IsNuclearOperator.clm_comp T.property Ua
  have hinj : Injective Uc := U.injective
  have h := isNuclearOperator_factor_comps Uc hinj (Ua ∘L T.val) hA₀
  have htr := nuclearTrace_factor_comps hilbert_approximationProperty
    hilbert_approximationProperty Uc hinj (Ua ∘L T.val) hA₀
  have e1 : (Ua ∘L T.val).comp Uc = S := by
    rw [ContinuousLinearMap.comp_assoc, ← hint, ← ContinuousLinearMap.comp_assoc, hUU,
      ContinuousLinearMap.id_comp]
  have hS : IsNuclearOperator S := e1 ▸ h.1
  refine ⟨hS, ?_⟩
  rw [hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
  rw [nuclearTrace_congr e1.symm hS h.1, htr]
  exact nuclearTrace_congr hrange h.2 T.property

end Hilbert

end RiemannMasullo
