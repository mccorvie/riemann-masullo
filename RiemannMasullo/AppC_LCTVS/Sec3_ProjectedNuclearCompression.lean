module

public import RiemannMasullo.AppC_LCTVS.Sec3a
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public noncomputable section

namespace RiemannMasullo

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Transport a projected product across an isometric embedding. Surjectivity is needed
only on the projected level: the outer flat projection puts the entire output in `range U`,
which permits cyclicity of the nuclear trace without assuming that `U` is unitary. -/
theorem transportProjectedNuclearCompression (U : E →ₗᵢ[ℂ] F)
    (P : Submodule ℂ E) (Q : Submodule ℂ F)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hmap : P.map U.toLinearMap = Q)
    (a b : E →L[ℂ] E) (A B : F →L[ℂ] F)
    (ha : ∀ x, U (a x) = A (U x)) (hb : ∀ x, U (b x) = B (U x))
    (hn : IsNuclearOperator (Q.starProjection ∘L A ∘L B ∘L Q.starProjection)) :
    let S := P.starProjection ∘L a ∘L b ∘L P.starProjection
    let T := Q.starProjection ∘L A ∘L B ∘L Q.starProjection
    S = U.toContinuousLinearMap.adjoint ∘L T ∘L U.toContinuousLinearMap ∧
      ∃ hs : IsNuclearOperator S, hilbertTrace ⟨S, hs⟩ = hilbertTrace ⟨T, hn⟩ := by
  let S := P.starProjection ∘L a ∘L b ∘L P.starProjection
  let T := Q.starProjection ∘L A ∘L B ∘L Q.starProjection
  let J := U.toContinuousLinearMap
  let C := J.adjoint ∘L T
  have hp (x : E) : U (P.starProjection x) = Q.starProjection (U x) := by
    subst Q
    exact U.map_starProjection P x
  have hleft (x : E) : J.adjoint (U x) = x :=
    DFunLike.congr_fun U.adjoint_comp_self x
  have hinter (x : E) : U (S x) = T (U x) := by
    change U (P.starProjection (a (b (P.starProjection x)))) =
      Q.starProjection (A (B (Q.starProjection (U x))))
    rw [hp, ha, hb, hp]
  have hS : S = C ∘L J := by
    ext1 x
    change S x = J.adjoint (T (U x))
    rw [← hinter, hleft]
  have hT : J ∘L C = T := by
    ext1 x
    have hx : T x ∈ Q := Q.starProjection_apply_mem _
    rw [← hmap] at hx
    obtain ⟨z, _, hz⟩ := hx
    change U z = T x at hz
    change U (J.adjoint (T x)) = T x
    rw [← hz, hleft]
  have hC : IsNuclearOperator C := by
    obtain ⟨c, φ, y, hc, hφ, hy, hsum⟩ := (isNuclearOperator_iff_isBanachNuclear T).mp hn
    refine (isNuclearOperator_iff_isBanachNuclear C).mpr
      ⟨c, φ, J.adjoint ∘ y, hc, hφ, (J.adjoint.continuous.tendsto' 0 0 (map_zero _)).comp hy,
        fun x ↦ ?_⟩
    change HasSum (fun n ↦ (c n * φ n x) • J.adjoint (y n)) (J.adjoint (T x))
    simpa only [map_smul] using J.adjoint.hasSum (hsum x)
  have h := isNuclearOperator_factor_comps J U.injective C hC
  have hs : IsNuclearOperator S := by
    rw [hS]
    exact h.1
  refine ⟨hS, hs, ?_⟩
  calc
    hilbertTrace ⟨S, hs⟩ = hilbertTrace ⟨C ∘L J, h.1⟩ :=
      congrArg hilbertTrace (Subtype.ext hS)
    _ = hilbertTrace ⟨J ∘L C, h.2⟩ := by
      rw [hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
      exact nuclearTrace_factor_comps hilbert_approximationProperty hilbert_approximationProperty
        J U.injective C hC
    _ = hilbertTrace ⟨T, hn⟩ := congrArg hilbertTrace (Subtype.ext hT)

end RiemannMasullo
