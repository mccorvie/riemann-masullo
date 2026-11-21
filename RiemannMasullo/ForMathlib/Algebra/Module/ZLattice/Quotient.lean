module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.LocalSubgroup

@[expose] public noncomputable section

open Module Set Topology

namespace RiemannMasullo

/-- A discrete integral submodule of a finite-dimensional real normed space is the kernel of
an open quotient map to a product of a Euclidean space and a finite-dimensional torus. -/
theorem exists_euclidean_torus_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    ∃ (m n : ℕ) (q : E →+ EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ))),
      IsOpenQuotientMap q ∧ q.ker = L.toAddSubgroup := by
  classical
  let W := Submodule.span ℝ (L : Set E)
  let M : Submodule ℤ W := L.comap (W.subtype.restrictScalars ℤ)
  let toL : M → L := fun x ↦ ⟨x.val.val, x.property⟩
  have : DiscreteTopology M := DiscreteTopology.of_continuous_injective
    (f := toL) ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    (fun _ _ h ↦ Subtype.ext (Subtype.ext (congrArg (fun y : L ↦ (y : E)) h)))
  have hRange : (M : Set W) = range (L.inclusionSpan ℝ) := by
    ext x
    exact ⟨fun hx ↦ ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.property⟩
  have : IsZLattice ℝ M := ⟨hRange ▸ L.span_range_inclusionSpan ℝ⟩
  obtain ⟨V, hVW⟩ := W.exists_isCompl
  let m := finrank ℝ V
  let n := finrank ℤ M
  let b := (finBasis ℤ M).ofZLatticeBasis ℝ
  let eV : V ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (finBasis ℝ V).equivFun.toContinuousLinearEquiv.trans (EuclideanSpace.equiv _ ℝ).symm
  let eW : W ≃L[ℝ] (Fin n → ℝ) := b.equivFun.toContinuousLinearEquiv
  let split := (V.prodEquivOfIsCompl W hVW.symm).toContinuousLinearEquiv
  let circle := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
  let qW := AddMonoidHom.pi (fun i : Fin n ↦ circle.comp (Pi.evalAddMonoidHom (fun _ ↦ ℝ) i))
  have hCircle : IsOpenQuotientMap circle := QuotientAddGroup.isOpenQuotientMap_mk
  have hqW : IsOpenQuotientMap qW :=
    ⟨Function.Surjective.piMap (fun _ ↦ hCircle.surjective),
      continuous_pi (fun i ↦ hCircle.continuous.comp (continuous_apply i)),
      IsOpenMap.piMap (fun _ ↦ hCircle.isOpenMap) (Filter.Eventually.of_forall fun _ ↦
        hCircle.surjective)⟩
  let coords := split.symm.trans (ContinuousLinearEquiv.prodCongr eV eW)
  let q := ((AddMonoidHom.id _).prodMap qW).comp coords.toLinearEquiv.toAddEquiv.toAddMonoidHom
  refine ⟨m, n, q, ?_, ?_⟩
  · exact (IsOpenQuotientMap.id.prodMap hqW).comp coords.toHomeomorph.isOpenQuotientMap
  · have hW (w : W) : qW (eW w) = 0 ↔ w ∈ M := by
      rw [← (finBasis ℤ M).ofZLatticeBasis_span ℝ, b.mem_span_iff_repr_mem ℤ]
      rw [funext_iff]
      change (∀ i, ((b.repr w i : ℝ) : AddCircle (1 : ℝ)) = 0) ↔ _
      simp only [AddCircle.coe_eq_zero_iff, zsmul_one, Set.mem_range]
      rfl
    ext x
    change (eV (split.symm x).1, qW (eW (split.symm x).2)) = (0, 0) ↔ x ∈ L
    rw [Prod.mk.injEq, hW, ← eV.map_zero, eV.injective.eq_iff]
    constructor
    · rintro ⟨hV, hM⟩
      have hx := split.apply_symm_apply x
      change (split.symm x).1.val + (split.symm x).2.val = x at hx
      rw [hV, Submodule.coe_zero, zero_add] at hx
      exact hx ▸ hM
    · intro hx
      let w : W := ⟨x, Submodule.subset_span hx⟩
      have hsplit : split.symm x = (0, w) :=
        V.prodEquivOfIsCompl_symm_apply_right W hVW.symm w
      rw [hsplit]
      exact ⟨rfl, hx⟩

open Metric in
/-- An open continuous homomorphism from a finite-dimensional real vector group
gives a real–torus presentation of its range. -/
theorem exists_real_torus_equiv_of_open_vector_range {E B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup B] [TopologicalSpace B] [T2Space B]
    (f : E →+ B) (hf : Continuous f) (hopen : IsOpenMap f) :
    ∃ m n : ℕ, Nonempty (f.range ≃ₜ+ EuclideanSpace ℝ (Fin m) ×
      (Fin n → AddCircle (1 : ℝ))) := by
  obtain ⟨V, ε, hε, _, hV⟩ := exists_subspace_ball_eq_of_localSubgroup (E := E)
    (R := 1) one_pos (isClosed_eq hf continuous_const : IsClosed (f.ker : Set E))
    f.ker.zero_mem (fun _ ↦ f.ker.neg_mem) (fun _ hx _ hy _ ↦ f.ker.add_mem hx hy)
  change (f.ker : Set E) ∩ Metric.closedBall 0 ε = _ at hV
  -- Scaling the local description of the kernel shows that it contains all of V.
  have hVK : (V : Set E) ⊆ f.ker := by
    intro x hx
    obtain ⟨N, hN⟩ := exists_nat_gt (‖x‖ / ε)
    have hNpos : (0 : ℝ) < N := (div_nonneg (norm_nonneg _) hε.le).trans_lt hN
    have hsmall : ‖(N : ℝ)⁻¹ • x‖ < ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNpos), ← div_eq_inv_mul]
      exact (div_lt_iff₀ hNpos).mpr (by
        simpa [mul_comm] using (div_lt_iff₀ hε).mp hN)
    have hk : (N : ℝ)⁻¹ • x ∈ f.ker := by
      have hm : (N : ℝ)⁻¹ • x ∈ (V : Set E) ∩ Metric.closedBall 0 ε :=
        ⟨V.smul_mem _ hx, mem_closedBall_zero_iff.mpr hsmall.le⟩
      rw [← hV] at hm
      exact hm.1
    have h := f.ker.nsmul_mem hk N
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hNpos.ne', one_smul] at h
    exact h
  -- Restrict to a complement so that the kernel is discrete.
  obtain ⟨W, hWV⟩ := V.exists_isCompl
  let e := (V.prodEquivOfIsCompl W hWV).toContinuousLinearEquiv
  let g := f.comp W.subtype.toAddMonoidHom
  have he (x : V × W) : f (e x) = g x.2 := by
    change f ((x.1 : E) + (x.2 : E)) = f x.2
    rw [map_add, (show f (x.1 : E) = 0 from hVK x.1.property), zero_add]
  let F := f.rangeRestrict.comp W.subtype.toAddMonoidHom
  have hF : IsOpenQuotientMap F := by
    refine ⟨?_, (hf.comp continuous_subtype_val).subtype_mk _, ?_⟩
    · rintro ⟨y, x, rfl⟩
      exact ⟨(e.symm x).2, Subtype.ext (show g (e.symm x).2 = f x by rw [← he, e.apply_symm_apply])⟩
    · intro U hU
      have hEq : (Subtype.val : f.range → B) '' (F '' U) =
          (f ∘ e) '' (Prod.snd ⁻¹' U) := by
        ext y
        constructor
        · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
          exact ⟨(0, w), hw, he (0, w)⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨F x.2, ⟨x.2, hx, rfl⟩, (he x).symm⟩
      rw [← Set.preimage_image_eq (F '' U) Subtype.val_injective, hEq]
      exact ((hopen.comp e.toHomeomorph.isOpenMap) _ (hU.preimage continuous_snd)).preimage
        continuous_subtype_val
  have hDiscrete : DiscreteTopology F.ker.toIntSubmodule := by
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have hball : (fun x : F.ker.toIntSubmodule ↦ ((x : W) : E)) ⁻¹'
        Metric.ball 0 ε = {0} := by
      ext x
      refine ⟨fun hx ↦ ?_, ?_⟩
      · have hxsmall : ((x : W) : E) ∈ Metric.closedBall 0 ε :=
          Metric.ball_subset_closedBall hx
        have hxK : ((x : W) : E) ∈ f.ker := congrArg Subtype.val x.property
        have hxV : ((x : W) : E) ∈ V := by
          have hx' := (show ((x : W) : E) ∈ (f.ker : Set E) ∩ Metric.closedBall 0 ε
            from ⟨hxK, hxsmall⟩)
          rw [hV] at hx'
          exact hx'.1
        exact mem_singleton_iff.mpr (Subtype.ext (Subtype.ext
          (Submodule.disjoint_def.mp hWV.disjoint _ hxV (x : W).property)))
      · rintro (rfl : x = 0)
        exact Metric.mem_ball_self hε
    exact hball ▸ Metric.isOpen_ball.preimage (continuous_subtype_val.comp continuous_subtype_val)
  obtain ⟨m, n, q, hq, hqker⟩ := exists_euclidean_torus_quotient F.ker.toIntSubmodule
  let eF := QuotientAddGroup.quotientKerEquivOfSurjective F hF.surjective
  let eq := QuotientAddGroup.quotientKerEquivOfSurjective q hq.surjective
  let r := eF.symm.trans ((QuotientAddGroup.quotientAddEquivOfEq hqker.symm).trans eq)
  have hr (x : W) : r (F x) = q x := by
    change r (eF (QuotientAddGroup.mk x)) = q x
    change eq (QuotientAddGroup.quotientAddEquivOfEq hqker.symm
      (eF.symm (eF (QuotientAddGroup.mk x)))) = _
    rw [eF.symm_apply_apply]
    rfl
  refine ⟨m, n, ⟨{r with continuous_toFun := ?_, continuous_invFun := ?_}⟩⟩
  · exact hF.continuous_comp_iff.mp ((funext hr : r ∘ F = q) ▸ hq.continuous)
  · exact hq.continuous_comp_iff.mp
      ((funext fun x ↦ r.symm_apply_eq.mpr (hr x).symm : r.symm ∘ q = F) ▸ hF.continuous)

end RiemannMasullo
