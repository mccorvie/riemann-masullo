module

public import Mathlib.LinearAlgebra.Isomorphisms

/-! # An invariant-submodule intersection quotient

This abstracts the algebra behind the two-prime compatibility obstruction in
issue #7351. It allows arbitrary modules and replaces injectivity of the second
operator by the weaker assumption that its kernel is in the invariant submodule.
No rational-packet results or other unmerged contributions are imported.
-/

public noncomputable section

namespace RiemannMasullo

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- For an invariant submodule `M` containing `ker B`, the quotient
`(M ∩ range B) / B(M)` is the kernel of the induced endomorphism on `E / M`.
For commuting `A` and `B`, take `M = range A`; injectivity of `A` is unnecessary,
and injectivity of `B` is stronger than the kernel containment used here. -/
def invariantIntersectionQuotientEquiv (B : E →ₗ[R] E) (M : Submodule R E)
    (hM : M ≤ M.comap B) (hker : LinearMap.ker B ≤ M) :
    (↥(M ⊓ LinearMap.range B) ⧸
      (M.map B).comap (M ⊓ LinearMap.range B).subtype) ≃ₗ[R]
      LinearMap.ker (M.mapQ M B hM) := by
  let P := M.comap B
  let I := M ⊓ LinearMap.range B
  let D := (M.map B).comap I.subtype
  let b := M.mapQ M B hM
  let k : P →ₗ[R] LinearMap.ker b :=
    { toFun := fun x ↦ ⟨M.mkQ x, by
        change M.mkQ (B x) = 0
        exact (Submodule.Quotient.mk_eq_zero M).mpr x.property⟩
      map_add' := fun x y ↦ Subtype.ext (map_add M.mkQ (x : E) (y : E))
      map_smul' := fun c x ↦ Subtype.ext (map_smul M.mkQ c (x : E)) }
  let g : P →ₗ[R] I :=
    { toFun := fun x ↦ ⟨B x, x.property, ⟨x, rfl⟩⟩
      map_add' := fun x y ↦ Subtype.ext (map_add B (x : E) (y : E))
      map_smul' := fun c x ↦ Subtype.ext (map_smul B c (x : E)) }
  let t : P →ₗ[R] (I ⧸ D) := D.mkQ.comp g
  have hk : Function.Surjective k := by
    intro z
    obtain ⟨x, hx⟩ := M.mkQ_surjective z.val
    have hxP : x ∈ P := by
      change B x ∈ M
      apply (Submodule.Quotient.mk_eq_zero M).mp
      have hz := z.property
      rw [← hx] at hz
      exact hz
    exact ⟨⟨x, hxP⟩, Subtype.ext hx⟩
  have ht : Function.Surjective t := by
    intro z
    obtain ⟨y, rfl⟩ := D.mkQ_surjective z
    obtain ⟨x, hx⟩ := y.property.2
    have hxP : x ∈ P := by
      change B x ∈ M
      rw [hx]
      exact y.property.1
    refine ⟨⟨x, hxP⟩, ?_⟩
    change D.mkQ ⟨B x, _⟩ = D.mkQ y
    exact congrArg D.mkQ (Subtype.ext hx)
  have hKt : ∀ x : P, t x = 0 ↔ (x : E) ∈ M := by
    intro x
    change D.mkQ (g x) = 0 ↔ (x : E) ∈ M
    rw [show D.mkQ (g x) = 0 ↔ g x ∈ D from Submodule.Quotient.mk_eq_zero D]
    change B x ∈ M.map B ↔ (x : E) ∈ M
    constructor
    · rintro ⟨y, hy, he⟩
      have hxy : (x : E) - y ∈ LinearMap.ker B := by
        change B ((x : E) - y) = 0
        rw [map_sub, he, sub_self]
      have hsum := M.add_mem (hker hxy) hy
      simpa only [sub_add_cancel] using hsum
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hK : LinearMap.ker t = LinearMap.ker k := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hKt]
    change (x : E) ∈ M ↔ k x = 0
    constructor
    · intro hx
      exact Subtype.ext ((Submodule.Quotient.mk_eq_zero M).mpr hx)
    · intro hx
      exact (Submodule.Quotient.mk_eq_zero M).mp (congrArg Subtype.val hx)
  exact (t.quotKerEquivOfSurjective ht).symm.trans
    ((Submodule.quotEquivOfEq _ _ hK).trans (k.quotKerEquivOfSurjective hk))

/-- The equivalence is induced by division by `B`: the class of `B x` maps
to the class of `x`. The assumption on `ker B` makes this independent of division. -/
theorem invariantIntersectionQuotientEquiv_apply (B : E →ₗ[R] E) (M : Submodule R E)
    (hM : M ≤ M.comap B) (hker : LinearMap.ker B ≤ M) (x : E) (hx : B x ∈ M) :
    (invariantIntersectionQuotientEquiv B M hM hker
      (Submodule.Quotient.mk (⟨B x, hx, ⟨x, rfl⟩⟩ : ↥(M ⊓ LinearMap.range B))) : E ⧸ M) =
        M.mkQ x := by
  let P := M.comap B
  let I := M ⊓ LinearMap.range B
  let D := (M.map B).comap I.subtype
  let g : P →ₗ[R] I :=
    { toFun := fun y ↦ ⟨B y, y.property, ⟨y, rfl⟩⟩
      map_add' := fun y z ↦ Subtype.ext (map_add B (y : E) (z : E))
      map_smul' := fun c y ↦ Subtype.ext (map_smul B c (y : E)) }
  let t : P →ₗ[R] (I ⧸ D) := D.mkQ.comp g
  have he : (Submodule.Quotient.mk (⟨B x, hx, ⟨x, rfl⟩⟩ : I) : I ⧸ D) =
      t ⟨x, hx⟩ := rfl
  rw [he]
  simp only [invariantIntersectionQuotientEquiv, LinearEquiv.trans_apply]
  erw [LinearMap.quotKerEquivOfSurjective_symm_apply t]
  simp only [Submodule.quotEquivOfEq_mk]
  rfl

end RiemannMasullo
