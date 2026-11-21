module

public import Mathlib.Topology.Algebra.PontryaginDual
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Separation
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

namespace RiemannMasullo

open MeasureTheory Set Topology
open scoped ComplexConjugate Pointwise

/-- Restricted characters separate points of the subgroup, so their complex linear span is dense. -/
private theorem dense_span_restrictedCharacters {H K : Type*}
    [CommGroup H] [TopologicalSpace H] [CompactSpace H]
    [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K] [CompactSpace K]
    (i : H →ₜ* K) (hi : Function.Injective i)
    (r : PontryaginDual K →* C(H, ℂ)) (hr : ∀ ψ x, r ψ x = (ψ (i x) : ℂ)) :
    (Submodule.span ℂ (range r)).topologicalClosure = ⊤ := by
  let S := MonoidHom.mrange r
  let A := StarAlgebra.adjoin ℂ (S : Set C(H, ℂ))
  have hstar : star (S : Set C(H, ℂ)) ⊆ S := by
    rw [Set.star_subset]
    rintro _ ⟨ψ, rfl⟩
    refine ⟨ψ⁻¹, ContinuousMap.ext fun x ↦ ?_⟩
    change r ψ⁻¹ x = star (r ψ x)
    rw [hr, hr]
    exact Circle.coe_inv_eq_conj (ψ (i x))
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_apply_ne_one (div_ne_one.mpr (hi.ne hxy))
    refine ⟨_, ⟨r ψ, StarAlgebra.subset_adjoin ℂ (S : Set C(H, ℂ)) ⟨ψ, rfl⟩, rfl⟩, ?_⟩
    change r ψ x ≠ r ψ y
    rw [hr, hr, Ne, Circle.coe_inj]
    exact fun he ↦ hψ ((map_div ψ _ _).trans (div_eq_one.mpr he))
  have hspan : A.toSubalgebra.toSubmodule = Submodule.span ℂ (range r) := by
    rw [StarAlgebra.adjoin_eq_span, Set.union_eq_left.mpr hstar, S.closure_eq]
    rfl
  rw [← hspan]
  exact congrArg (fun S : StarSubalgebra ℂ C(H, ℂ) ↦ S.toSubalgebra.toSubmodule)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep)

/-- The complex linear span of the characters of a compact Hausdorff abelian group
is dense in its continuous functions. -/
theorem dense_span_pontryaginDual {K : Type*} [CommGroup K] [TopologicalSpace K]
    [IsTopologicalGroup K] [T2Space K] [CompactSpace K]
    (r : PontryaginDual K →* C(K, ℂ)) (hr : ∀ χ x, r χ x = (χ x : ℂ)) :
    (Submodule.span ℂ (range r)).topologicalClosure = ⊤ :=
  dense_span_restrictedCharacters (ContinuousMonoidHom.id K) Function.injective_id r hr

/-- A character of a compact subgroup of a compact Hausdorff abelian group extends to the
whole group. The subgroup is presented by an injective continuous homomorphism.
Stone–Weierstrass gives density of the span of the restricted characters. Orthogonality
on the subgroup then gives the desired restriction. -/
theorem exists_pontryaginDual_extension_of_compact {H K : Type*}
    [CommGroup H] [TopologicalSpace H] [CompactSpace H]
    [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K] [CompactSpace K]
    (i : H →ₜ* K) (hi : Function.Injective i) (χ : PontryaginDual H) :
    ∃ ψ : PontryaginDual K, ∀ x, ψ (i x) = χ x := by
  classical
  have he := i.continuous.isClosedEmbedding hi
  let : T2Space H := he.isEmbedding.t2Space
  let : IsTopologicalGroup H := he.isEmbedding.isInducing.isTopologicalGroup i
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let μ : Measure H := Measure.haar
  let r : PontryaginDual K →* C(H, ℂ) :=
    { toFun ψ := ⟨fun x ↦ (ψ (i x) : ℂ), continuous_subtype_val.comp (ψ.continuous.comp i.continuous)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let c : C(H, ℂ) := ⟨fun x ↦ (χ x : ℂ), continuous_subtype_val.comp χ.continuous⟩
  -- The Fourier coefficient at χ is a continuous linear functional on continuous functions.
  let T := ContinuousMap.toLp (E := ℂ) 2 μ ℂ
  let L := (innerSL ℂ (T c)).comp T
  by_contra! hnone
  have horth : Submodule.span ℂ (range r) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨ψ, rfl⟩
    obtain ⟨g, hg⟩ := hnone ψ
    let δ : PontryaginDual H := PontryaginDual.map i ψ * χ⁻¹
    have hδ : (δ g : ℂ) ≠ 1 := by
      change ((ψ (i g) * (χ g)⁻¹ : Circle) : ℂ) ≠ 1
      rw [← div_eq_mul_inv]
      exact fun h ↦ hg (div_eq_one.mp (Circle.ext h))
    change inner ℂ (T c) (T (r ψ)) = 0
    rw [ContinuousMap.inner_toLp]
    change (∫ x, (ψ (i x) : ℂ) * conj (χ x : ℂ) ∂μ) = 0
    simp_rw [← Circle.coe_inv_eq_conj]
    change (∫ x, (δ x : ℂ) ∂μ) = 0
    -- Translation by g fixes the integral but multiplies it by the nontrivial value δ(g).
    have ht := integral_mul_left_eq_self (μ := μ) (fun x ↦ (δ x : ℂ)) g
    simp_rw [map_mul, Circle.coe_mul, integral_const_mul] at ht
    by_contra hn
    exact hδ ((mul_eq_right₀ hn).mp ht)
  have htop := (Submodule.span ℂ (range r)).topologicalClosure_minimal horth L.isClosed_ker
  rw [dense_span_restrictedCharacters i hi r (fun _ _ ↦ rfl)] at htop
  have hc : inner ℂ (T c) (T c) = 0 := htop (Submodule.mem_top (x := c))
  have hc0 := (ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) μ)
    ((inner_self_eq_zero.mp hc).trans (map_zero T).symm)
  have : (1 : ℂ) = 0 := by simpa [c] using congrArg (fun f : C(H, ℂ) ↦ f 1) hc0
  exact one_ne_zero this

section Restriction

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- A character of a compact group embedded in an LCA group extends to the whole group.
Evaluation embeds the compact group into the compact closure of the ambient evaluation image. -/
private theorem exists_extension_of_compact_source {K : Type*} [CommGroup K]
    [TopologicalSpace K] [CompactSpace K] (i : K →ₜ* G) (hi : Function.Injective i)
    (χ : PontryaginDual K) : ∃ ψ : PontryaginDual G, ∀ x, ψ (i x) = χ x := by
  let ev : G →* (PontryaginDual G → Circle) :=
    { toFun x ψ := ψ x
      map_one' := funext fun ψ ↦ map_one ψ
      map_mul' x y := funext fun ψ ↦ map_mul ψ x y }
  have hev : Continuous ev := continuous_pi fun ψ ↦ ψ.continuous
  have hinj : Function.Injective ev := by
    intro x y h
    by_contra hxy
    obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_apply_ne_one (div_ne_one.mpr hxy)
    exact hψ (by rw [map_div, show ψ x = ψ y from congrFun h ψ, div_self'])
  let L := ev.range.topologicalClosure
  let : CompactSpace L := isCompact_iff_compactSpace.mp ev.range.isClosed_topologicalClosure.isCompact
  let j : G →ₜ* L :=
    ⟨ev.codRestrict L (fun x ↦ ev.range.le_topologicalClosure ⟨x, rfl⟩), hev.subtype_mk _⟩
  have hj : Function.Injective j := fun _ _ h ↦ hinj (congrArg Subtype.val h)
  obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_extension_of_compact (j.comp i) (hj.comp hi) χ
  exact ⟨ψ.comp j, hψ⟩

omit [T2Space G] in
/-- A character of a closed subgroup which is trivial on its intersection with a compact
subgroup extends to a character trivial on the whole compact subgroup. In the quotient of
`G × Circle` by the graph and the compact subgroup, the circle factor still embeds. -/
theorem exists_pontryaginDual_extension_trivial_on_compact (H K : Subgroup G)
    (hH : IsClosed (H : Set G)) (hK : IsCompact (K : Set G))
    (χ : PontryaginDual H) (hχ : ∀ x : H, (x : G) ∈ K → χ x = 1) :
    ∃ ψ : PontryaginDual G, (∀ x : H, ψ x = χ x) ∧ ∀ x : K, ψ x = 1 := by
  -- Quotient by the graph of χ and by the compact subgroup where the extension must vanish.
  let graph := (H.subtype.prod χ.toMonoidHom).range
  let K₀ := K.prod (⊥ : Subgroup Circle)
  let D := graph ⊔ K₀
  have hGraph : IsClosed (graph : Set (G × Circle)) := by
    rw [MonoidHom.coe_range]
    let f : H × Circle → G × Circle := Prod.map Subtype.val id
    have hf : IsClosedEmbedding f := hH.isClosedEmbedding_subtypeVal.prodMap IsClosedEmbedding.id
    have hc : IsClosed {p : H × Circle | χ p.1 = p.2} :=
      isClosed_eq (χ.continuous.comp continuous_fst) continuous_snd
    convert hf.isClosedMap _ hc using 1
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x, χ x), rfl, rfl⟩
    · rintro ⟨⟨x, z⟩, hz, rfl⟩
      exact ⟨x, Prod.ext rfl hz⟩
  have hK₀ : IsCompact (K₀ : Set (G × Circle)) := by
    simpa [K₀, Subgroup.coe_prod] using hK.prod (isCompact_singleton (x := (1 : Circle)))
  let : IsClosed (D : Set (G × Circle)) := by
    rw [Subgroup.mul_normal]
    exact hGraph.mul_right_of_isCompact hK₀
  let q : G × Circle →ₜ* (G × Circle) ⧸ D :=
    ⟨QuotientGroup.mk' D, QuotientGroup.continuous_mk⟩
  let i : Circle →ₜ* (G × Circle) ⧸ D :=
    q.comp ⟨MonoidHom.inr G Circle, continuous_const.prodMk continuous_id⟩
  have hInj : Function.Injective i := by
    apply (injective_iff_map_eq_one i.toMonoidHom).mpr
    intro z hz
    obtain ⟨_, ⟨x, rfl⟩, ⟨k, w⟩, ⟨hk, hw⟩, he⟩ :=
      Subgroup.mem_sup.mp ((QuotientGroup.eq_one_iff (1, z)).mp hz)
    have hx : (x : G) * k = 1 := congrArg Prod.fst he
    have hw' : w = 1 := Subgroup.mem_bot.mp hw
    have hxK : (x : G) ∈ K :=
      (eq_inv_of_mul_eq_one_left hx).symm ▸ K.inv_mem hk
    have hz' : χ x * w = z := congrArg Prod.snd he
    simpa [hχ x hxK, hw'] using hz'.symm
  let idχ : PontryaginDual Circle := ContinuousMonoidHom.id Circle
  obtain ⟨ψ, hψ⟩ := exists_extension_of_compact_source i hInj idχ
  let Ψ := ψ.comp q
  let ψG : PontryaginDual G :=
    (Ψ.comp ⟨MonoidHom.inl G Circle, continuous_id.prodMk continuous_const⟩)⁻¹
  have hTrivial (p : G × Circle) (hp : p ∈ D) : Ψ p = 1 := by
    change ψ (q p) = 1
    rw [show q p = 1 from (QuotientGroup.eq_one_iff p).mpr hp, map_one]
  refine ⟨ψG, fun x ↦ ?_, fun x ↦ ?_⟩
  · have hGraphMem : (↑x, χ x) ∈ graph := ⟨x, rfl⟩
    have h := hTrivial (x, χ x) ((show graph ≤ D from le_sup_left) hGraphMem)
    rw [show ((x : G), χ x) = ((x : G), 1) * (1, χ x) by simp, map_mul] at h
    change (Ψ (x, 1))⁻¹ = χ x
    exact (eq_inv_of_mul_eq_one_right (show Ψ (x, 1) * χ x = 1 from
      (hψ (χ x)) ▸ h)).symm
  · have hCompactMem : (↑x, 1) ∈ K₀ := ⟨x.property, Subgroup.one_mem _⟩
    have h := hTrivial (x, 1) ((show K₀ ≤ D from le_sup_right) hCompactMem)
    change (Ψ (x, 1))⁻¹ = 1
    simp [h]

end Restriction

end RiemannMasullo
