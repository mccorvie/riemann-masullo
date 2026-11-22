module
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Exact.Basic

@[expose] public section

open Function Set Topology

variable {𝕜 X Y : Type*} [Ring 𝕜] [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
  [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y]

/-- A continuous linear equivalence descends to the quotients by corresponding submodules. -/
def ContinuousLinearEquiv.quotientMapEquiv (e : X ≃L[𝕜] Y) (P : Submodule 𝕜 X)
    (Q : Submodule 𝕜 Y) (h : P.map e.toLinearMap = Q) : (X ⧸ P) ≃L[𝕜] (Y ⧸ Q) where
  __ := Submodule.Quotient.equiv P Q e.toLinearEquiv h
  continuous_toFun := P.isQuotientMap_mkQL.continuous_iff.mpr (Q.mkQL.continuous.comp e.continuous)
  continuous_invFun := Q.isQuotientMap_mkQL.continuous_iff.mpr (P.mkQL.continuous.comp e.symm.continuous)

/-- The sequence of quotients for nested submodules is exact. If the larger submodule is
closed, the inclusion of its quotient is a closed embedding. -/
theorem Submodule.exists_exact_quotient_maps (M N : Submodule 𝕜 X) (h : M ≤ N)
    (hN : IsClosed (N : Set X)) :
    let K := M.comap N.subtype
    ∃ (i : (N ⧸ K) →L[𝕜] (X ⧸ M)) (q : (X ⧸ M) →L[𝕜] (X ⧸ N)),
      (∀ x : N, i (K.mkQ x) = M.mkQ x.val) ∧ (∀ x, q (M.mkQ x) = N.mkQ x) ∧
      IsClosedEmbedding i ∧ Exact i q ∧ Surjective q := by
  intro K
  let i := K.liftQL (M.mkQL.comp N.subtypeL) fun x hx ↦ (Submodule.Quotient.mk_eq_zero M).mpr hx
  let q := M.liftQL N.mkQL fun x hx ↦ (Submodule.Quotient.mk_eq_zero N).mpr (h hx)
  have hi (x : N) : i (K.mkQ x) = M.mkQ x.val := rfl
  have hq (x : X) : q (M.mkQ x) = N.mkQ x := rfl
  have lift (x : X) (y : N) (heq : M.mkQ y.val = M.mkQ x) :
      ∃ z : N, z.val = x ∧ K.mkQ z = K.mkQ y := by
    have hd : y.val - x ∈ M := (Submodule.Quotient.eq M).mp heq
    have hx : x ∈ N := by simpa using N.sub_mem y.property (h hd)
    refine ⟨⟨x, hx⟩, rfl, ?_⟩
    exact ((Submodule.Quotient.eq K).mpr hd).symm
  refine ⟨i, q, hi, hq, .of_continuous_injective_isClosedMap i.continuous ?_ ?_, ?_, ?_⟩
  · intro u v huv
    obtain ⟨x, rfl⟩ := K.mkQ_surjective u
    obtain ⟨y, rfl⟩ := K.mkQ_surjective v
    exact (Submodule.Quotient.eq K).mpr ((Submodule.Quotient.eq M).mp huv)
  · intro s hs
    apply M.isQuotientMap_mkQL.isClosed_preimage.mp
    have heq : M.mkQL ⁻¹' (i '' s) = Subtype.val '' (K.mkQL ⁻¹' s) := by
      ext x
      constructor
      · rintro ⟨u, hu, he⟩
        obtain ⟨y, rfl⟩ := K.mkQ_surjective u
        obtain ⟨z, hz, heq⟩ := lift x y he
        exact ⟨z, show K.mkQ z ∈ s from heq.symm ▸ hu, hz⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨K.mkQ y, hy, hi y⟩
    rw [heq]
    exact (N.isClosedEmbedding_subtype hN).isClosedMap _ (hs.preimage K.mkQL.continuous)
  · intro u
    obtain ⟨x, rfl⟩ := M.mkQ_surjective u
    rw [hq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hx
      exact ⟨K.mkQ ⟨x, hx⟩, rfl⟩
    · rintro ⟨z, hz⟩
      obtain ⟨y, rfl⟩ := K.mkQ_surjective z
      obtain ⟨v, rfl, -⟩ := lift x y hz
      exact v.property
  · intro u
    obtain ⟨x, rfl⟩ := N.mkQ_surjective u
    exact ⟨M.mkQ x, rfl⟩

/-- An embedding onto a linear image identifies the quotient by a submodule with
the quotient of the image by the corresponding image submodule. -/
theorem ContinuousLinearMap.exists_quotient_range_equiv (A : X →L[𝕜] Y)
    (hA : IsEmbedding A) (N : Submodule 𝕜 X) (M : Submodule 𝕜 A.range)
    (hM : ∀ x, A.rangeRestrict x ∈ M ↔ x ∈ N) :
    ∃ F : (X ⧸ N) ≃L[𝕜] (A.range ⧸ M), ∀ x, F (N.mkQ x) = M.mkQ (A.rangeRestrict x) := by
  let e : X ≃ₗ[𝕜] A.range := LinearEquiv.ofInjective A.toLinearMap hA.injective
  let E : X ≃L[𝕜] A.range :=
    { __ := e
      continuous_toFun := A.rangeRestrict.continuous
      continuous_invFun := hA.continuous_iff.mpr (by
        have heq : A ∘ e.symm = Subtype.val := funext fun y ↦
          congrArg Subtype.val (e.apply_symm_apply y)
        change Continuous (A ∘ e.symm)
        rw [heq]
        exact continuous_subtype_val) }
  have h : N.map E.toLinearMap = M := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨fun ⟨z, hz, hzx⟩ ↦ (hM x).mpr (e.injective hzx ▸ hz),
      fun hx ↦ ⟨x, (hM x).mp hx, rfl⟩⟩
  exact ⟨E.quotientMapEquiv N M h, fun _ ↦ rfl⟩

/-- A jointly continuous family of linear operators preserving a submodule acts
jointly continuously on its quotient. -/
theorem Submodule.exists_continuous_quotient_family {G : Type*} [TopologicalSpace G] [IsTopologicalAddGroup X]
    (N : Submodule 𝕜 X) (A : G → X →L[𝕜] X) (hc : Continuous fun u : G × X ↦ A u.1 u.2)
    (hN : ∀ g x, x ∈ N → A g x ∈ N) :
    ∃ ρ : G × (X ⧸ N) → (X ⧸ N), Continuous ρ ∧ ∀ g x, ρ (g, N.mkQ x) = N.mkQ (A g x) := by
  let B (g : G) := N.liftQL (N.mkQL.comp (A g)) fun x hx ↦
    (Submodule.Quotient.mk_eq_zero N).mpr (hN g x hx)
  refine ⟨fun u ↦ B u.1 u.2, ?_, fun _ _ ↦ rfl⟩
  have hq := (IsOpenQuotientMap.id (X := G)).prodMap N.isOpenQuotientMap_mkQ
  exact hq.isQuotientMap.continuous_iff.mpr (N.mkQL.continuous.comp hc)
