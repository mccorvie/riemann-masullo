module

public import Mathlib.Topology.Algebra.PontryaginDual
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex

@[expose] public section

open Filter Set
open scoped Topology

namespace RiemannMasullo

/-- A continuous circle-valued character of a product of circles is a finite product
of integer powers of the coordinates. -/
theorem exists_finset_circleCharacter_eq_prod_zpow {ι : Type*}
    (χ : PontryaginDual (ι → Circle)) :
    ∃ (s : Finset ι) (n : ι → ℤ), ∀ x, χ x = ∏ i ∈ s, x i ^ n i := by
  classical
  have hArc : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
    simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  have ht : Tendsto χ (𝓝 (1 : ι → Circle)) (𝓝 (χ 1)) := χ.continuous.tendsto 1
  rw [map_one] at ht
  have hχ := ht hArc
  change χ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : ι → Circle) at hχ
  rw [nhds_pi, Filter.mem_pi'] at hχ
  obtain ⟨s, U, hU, hs⟩ := hχ
  have hTrivial (x : ι → Circle) (hx : ∀ i ∈ s, x i = 1) : χ x = 1 := by
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro k _
    rw [← map_pow]
    exact hs (fun i hi ↦ by
      change x i ^ k ∈ U i
      rw [hx i hi, one_pow]
      exact mem_of_mem_nhds (hU i))
  let coe : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  let single (i : ι) : Circle →ₜ* (ι → Circle) :=
    ⟨MonoidHom.mulSingle (fun _ ↦ Circle) i, continuous_mulSingle (A := fun _ : ι ↦ Circle) i⟩
  choose n hn using fun i ↦ (existsUnique_circleCharacter_zpow
    (coe.comp (χ.comp (single i)))).exists
  refine ⟨s, n, fun x ↦ ?_⟩
  let y : ι → Circle := ∏ i ∈ s, single i (x i)
  have hy (i : ι) (hi : i ∈ s) : y i = x i := by
    dsimp only [y]
    rw [Finset.prod_apply]
    change (∏ j ∈ s, Pi.mulSingle j (x j) i) = x i
    rw [Finset.prod_eq_single i (fun j _ hj ↦ Pi.mulSingle_eq_of_ne' hj _) (fun h ↦ (h hi).elim),
      Pi.mulSingle_eq_same]
  have h := hTrivial (x / y) (fun i hi ↦ by simp [Pi.div_apply, hy i hi])
  rw [map_div, div_eq_one] at h
  rw [h, show y = ∏ i ∈ s, single i (x i) from rfl, map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ Circle.ext ?_
  rw [Circle.coe_zpow]
  exact hn i (x i)

end RiemannMasullo
