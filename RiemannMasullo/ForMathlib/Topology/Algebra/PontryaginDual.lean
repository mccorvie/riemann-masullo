module

public import Mathlib.Topology.Algebra.PontryaginDual
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Separation
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral

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

end RiemannMasullo
