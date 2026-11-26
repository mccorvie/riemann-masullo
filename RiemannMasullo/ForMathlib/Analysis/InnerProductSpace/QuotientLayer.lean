module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Orthogonal layers of nested Hilbert subspaces

The actual quotient is embedded isometrically through its orthogonal representatives.
For nested ambient closed subspaces, the resulting projection is their difference.
-/

public noncomputable section
open Set Function
open scoped Topology
namespace RiemannMasullo
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (K : ClosedSubmodule ℂ E)
local instance : IsClosed (K.toSubmodule : Set E) := K.isClosed
local notation "N" => K.toSubmodule

/-- The orthogonal representative of a Hilbert quotient, embedded in its original space. -/
def quotientOrthogonalSection : (E ⧸ N) →ₗᵢ[ℂ] E :=
  ((N).orthogonal).subtypeₗᵢ.comp (N).quotientEquivOrthogonal.toLinearIsometry

/-- The orthogonal section is a right inverse of the actual quotient map. -/
theorem quotientOrthogonalSection_rightInverse (u : E ⧸ N) :
    (N).mkQL (quotientOrthogonalSection K u) = u := by
  have h := (N).quotientEquivOrthogonal_symm_eq_mk
    ((N).quotientEquivOrthogonal u).val ((N).quotientEquivOrthogonal u).property
  exact h.symm.trans ((N).quotientEquivOrthogonal.symm_apply_apply u)

/-- The section of a quotient class is the orthogonal projection of any representative. -/
theorem quotientOrthogonalSection_mk (x : E) :
    quotientOrthogonalSection K ((N).mkQL x) = ((N).orthogonal).starProjection x := by
  have hmk : (N).mkQL (((N).orthogonal).starProjection x) = (N).mkQL x := by
    apply (Submodule.Quotient.eq N).mpr
    rw [Submodule.starProjection_orthogonal_val]
    convert (N).neg_mem ((N).orthogonalProjectionOnto x).property using 1; abel
  rw [← hmk]
  exact congrArg Subtype.val ((N).quotientEquivOrthogonal_mk _ (((N).orthogonal).orthogonalProjectionOnto x).property)

/-- Quotient compression is ordinary orthogonal compression, even when the
orthogonal complement itself is not invariant under the upstairs operator. -/
theorem quotientOrthogonalSection_compress
    (A : E →L[ℂ] E) (B : (E ⧸ N) →L[ℂ] (E ⧸ N))
    (h : ∀ x, B ((N).mkQL x) = (N).mkQL (A x)) :
    (quotientOrthogonalSection K).toContinuousLinearMap.comp
        (B.comp (N).mkQL) = ((N).orthogonal).starProjection.comp A := by
  apply ContinuousLinearMap.ext
  intro x
  change quotientOrthogonalSection K (B ((N).mkQL x)) = ((N).orthogonal).starProjection (A x)
  rw [h, quotientOrthogonalSection_mk]

section Nested
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (M : ClosedSubmodule ℂ H) (D : ClosedSubmodule ℂ M)
local instance : IsClosed (M.toSubmodule : Set H) := M.isClosed
local instance : IsClosed (D.toSubmodule : Set M) := D.isClosed

/-- The actual quotient is embedded isometrically in the original ambient Hilbert space. -/
def nestedQuotientSection : (M ⧸ D.toSubmodule) →ₗᵢ[ℂ] H :=
  M.toSubmodule.subtypeₗᵢ.comp (quotientOrthogonalSection D)

/-- Evaluate the canonical section in the original ambient space. -/
theorem nestedQuotientSection_apply (u : M ⧸ D.toSubmodule) :
    nestedQuotientSection M D u = (quotientOrthogonalSection D u : H) := by rfl

/-- Orthogonal projection to the preceding space followed by the actual quotient map. -/
def nestedQuotientMap : H →L[ℂ] (M ⧸ D.toSubmodule) :=
  D.toSubmodule.mkQL.comp M.toSubmodule.orthogonalProjectionOnto

/-- Evaluate the quotient map on a vector already in the preceding space. -/
theorem nestedQuotientMap_subtype (u : M) :
    nestedQuotientMap M D u = D.toSubmodule.mkQL u := by
  change D.toSubmodule.mkQL (M.toSubmodule.orthogonalProjectionOnto u) = _
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

/-- The quotient map retracts its canonical isometric section. -/
theorem nestedQuotientMap_section :
    (nestedQuotientMap M D).comp (nestedQuotientSection M D).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (M ⧸ D.toSubmodule) := by
  apply ContinuousLinearMap.ext
  intro u
  change nestedQuotientMap M D (quotientOrthogonalSection D u : M) = u
  rw [nestedQuotientMap_subtype, quotientOrthogonalSection_rightInverse]

/-- The ambient quotient map is a contraction. -/
theorem norm_nestedQuotientMap_le : ‖nestedQuotientMap M D‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖D.toSubmodule.mkQL (M.toSubmodule.orthogonalProjectionOnto x)‖ ≤ 1 * ‖x‖
  rw [one_mul]
  exact (Submodule.Quotient.norm_mk_le D.toSubmodule _).trans
    (M.toSubmodule.norm_orthogonalProjectionOnto_apply_le x)

private theorem nested_projection_subtype (V : ClosedSubmodule ℂ H)
    (hNM : V.toSubmodule ≤ M.toSubmodule)
    (hD : ∀ u : M, u ∈ D ↔ (u : H) ∈ V) (u : M) :
    ((D.toSubmodule.starProjection u : M) : H) = V.toSubmodule.starProjection u := by
  let : IsClosed (V.toSubmodule : Set H) := V.isClosed
  symm
  apply V.toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact (hD _).mp (D.toSubmodule.orthogonalProjectionOnto u).property
  · intro w hw
    let wM : M := ⟨w, hNM hw⟩
    have hwD : wM ∈ D := (hD wM).mpr hw
    exact D.toSubmodule.starProjection_inner_eq_zero u wM hwD

/-- For nested closed subspaces, the quotient section composed with its
retraction is exactly the difference of their ambient orthogonal projections. -/
theorem nestedQuotientSection_map_eq_difference (V : ClosedSubmodule ℂ H)
    (hNM : V.toSubmodule ≤ M.toSubmodule)
    (hD : ∀ u : M, u ∈ D ↔ (u : H) ∈ V) :
    (nestedQuotientSection M D).toContinuousLinearMap.comp (nestedQuotientMap M D) =
      M.toSubmodule.starProjection - V.toSubmodule.starProjection := by
  let : IsClosed (V.toSubmodule : Set H) := V.isClosed
  apply ContinuousLinearMap.ext
  intro x
  change (quotientOrthogonalSection D
    (D.toSubmodule.mkQL (M.toSubmodule.orthogonalProjectionOnto x)) : H) = _
  rw [quotientOrthogonalSection_mk, Submodule.starProjection_orthogonal_val]
  change M.toSubmodule.starProjection x -
    ((D.toSubmodule.starProjection (M.toSubmodule.orthogonalProjectionOnto x) : M) : H) =
      M.toSubmodule.starProjection x - V.toSubmodule.starProjection x
  rw [nested_projection_subtype M D V hNM hD]
  have he := congrArg (fun A : H →L[ℂ] H ↦ A x)
    (Submodule.starProjection_comp_starProjection_of_le hNM)
  exact congrArg (fun y ↦ M.toSubmodule.starProjection x - y) he

end Nested

end RiemannMasullo
