module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1c

/-!
# Pullback of Bruhat smoothness by a continuous homomorphism

For a fixed order, choose a good subgroup mapped into the target kernel.
On each compactly generated open subgroup the pullback then descends along a
continuous map between elementary quotients. This is the structural-pair
argument used for the local restriction in Chapter 12, §4.
-/

public section

open Function Set

namespace RiemannMasullo

private theorem pullback_isBruhatContDiff {G H : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
    (f : G →ₜ* H) {r : H → ℂ} {p : ℕ} (hr : IsBruhatContDiff p r) :
    IsBruhatContDiff p (r ∘ f) := by
  obtain ⟨l, hl, hinv, hdesc⟩ := hr
  obtain ⟨L, hL⟩ := exists_openCompactlyGeneratedSubgroup_contains hl.isCompact
  let a₀ : BruhatStructuralPair H := ⟨(L.val, OrderDual.toDual l), L.property.1, L.property.2, hl, hL⟩
  obtain ⟨k, hk, hkl⟩ := exists_good_subgroup_image_in_kernel f a₀
  change k.map f.toMonoidHom ≤ l at hkl
  refine ⟨k, hk, ?_, ?_⟩
  · intro t x
    exact (congrArg (fun y ↦ r y) (map_mul f t.val x)).trans
      (hinv ⟨f t.val, hkl ⟨t.val, t.property, rfl⟩⟩ (f x))
  · intro a ha
    obtain ⟨C, _, hc, hgen⟩ := a.property.2.1
    obtain ⟨M, hM⟩ := exists_openCompactlyGeneratedSubgroup_contains
      ((hc.image (f.continuous.comp continuous_subtype_val)).union hl.isCompact)
    have hsub : C ⊆ (M.val.comap (f.toMonoidHom.comp a.val.1.subtype) : Set a.val.1) :=
      fun x hx ↦ hM (Or.inl ⟨x, hx, rfl⟩)
    have htop : ⊤ ≤ M.val.comap (f.toMonoidHom.comp a.val.1.subtype) :=
      hgen ▸ (Subgroup.closure_le _).mpr hsub
    let b : BruhatStructuralPair H := ⟨(M.val, OrderDual.toDual l),
      M.property.1, M.property.2, hl, fun x hx ↦ hM (Or.inr hx)⟩
    let i : a.val.1 →* b.val.1 := (f.toMonoidHom.comp a.val.1.subtype).codRestrict M.val
      (fun x ↦ htop (Subgroup.mem_top x))
    let j : a.quotient →* b.quotient :=
      QuotientGroup.map _ _ i (fun x hx ↦ hkl ⟨x.val, ha ▸ hx, rfl⟩)
    have hi : Continuous i := (f.continuous.comp continuous_subtype_val).subtype_mk _
    have hj : Continuous j := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp hi)
    obtain ⟨r₀, hr₀, hsm⟩ := hdesc b rfl
    obtain ⟨e'⟩ := b.elementary
    refine ⟨r₀ ∘ j, fun x ↦ hr₀ (i x), fun e z d ↦ ?_⟩
    let P := AddMonoidHom.toMultiplicative.symm
      (e'.equiv.toMulEquiv.toMonoidHom.comp (j.comp e.equiv.symm.toMulEquiv.toMonoidHom))
    have hP : Continuous P := e'.equiv.continuous.comp (hj.comp e.equiv.symm.continuous)
    let φ := fun y ↦ r₀ (e'.equiv.symm (Multiplicative.ofAdd y))
    have hs := contDiff_comp_elementaryHom P hP (f := φ) (hsm e') z d
    convert hs using 1
    funext u
    change r₀ (j (e.equiv.symm _)) = r₀ (e'.equiv.symm (e'.equiv (j (e.equiv.symm _))))
    rw [e'.equiv.symm_apply_apply]

/-- Pulling a Bruhat-smooth complex function back by a continuous homomorphism
of locally compact abelian groups preserves Bruhat smoothness. -/
theorem isBruhatSmooth_comp_continuousMonoidHom.{u_2, u_3} {G : Type u_2} {H : Type u_3}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
    (π : G →ₜ* H) {f : H → ℂ} (hf : IsBruhatSmooth f) :
    IsBruhatSmooth (f ∘ π) :=
  fun p ↦ pullback_isBruhatContDiff π (hf p)

end RiemannMasullo
