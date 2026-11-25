module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.Topology.Algebra.Support
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import RiemannMasullo.AppA_AlgebraicNT.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
public import RiemannMasullo.Ch11_ShellStructure.Sec3

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleMeasurableSpaceSec1a

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "𝒟" => BruhatCompactSupport C𝔽

/-- Paper: §11.3.1.1(2), pp. 494–495.
Reconstruction: the finite-support assertion needed when the shell calculation is
performed after enlarging the finite base. Starting with any saturated base, one can
add all rational primes that support a nonzero local Poisson term and obtain a larger
saturated base on whose complement every such term vanishes.
Deviation: this packages the proved finite-support theorem for the arithmetic Poisson
terms. It does not identify the retained S-local term with the geometric shell weight
or supply the global-to-S-local trace comparison.
-/
theorem exists_saturated_base_superset_orbitalPlacePoissonTerm_eq_zero
    (S₀ : Finset V)
    (_hS₀ : ∀ v ∈ S₀, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S₀)
    (χ : PontryaginDual C𝔽) (φ : 𝒟)
    (_hφ : tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)})
    (π : ∀ v : V, (v.adicCompletion F)ˣ)
    (_hπ : ∀ v, Valued.v.IsUniformizer (π v : v.adicCompletion F)) :
    ∃ S : Finset V, S₀ ⊆ S ∧
      (∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) ∧
      ∀ v ∉ S, ∀ n : ℤ, orbitalPlacePoissonTerm χ φ v (π v) n = 0 := by
  classical
  let P : Set V := {v | ∃ n : ℤ, orbitalPlacePoissonTerm χ φ v (π v) n ≠ 0}
  have hP : P.Finite := by
    exact finite_support_orbitalPlacePoisson χ φ _hφ π _hπ
  let Q : Finset Vℚ := (hP.image (fun v : V => v.under (𝓞 ℚ))).toFinset
  let S₁ : Finset V := Q.biUnion
    (fun p => (finite_nuclearityPlacesAbove (F := F) p).toFinset)
  let S : Finset V := S₀ ∪ S₁
  refine ⟨S, ?_, ?_, ?_⟩
  · exact Finset.subset_union_left
  · intro v hv w h_under
    simp only [S] at hv ⊢
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (_hS₀ v hv w h_under)
    · apply Finset.mem_union_right
      simp only [S₁, Finset.mem_biUnion] at hv ⊢
      rcases hv with ⟨p, hpQ, hvp⟩
      refine ⟨p, hpQ, ?_⟩
      apply (finite_nuclearityPlacesAbove (F := F) p).mem_toFinset.mpr
      exact h_under.trans
        ((finite_nuclearityPlacesAbove (F := F) p).mem_toFinset.mp hvp)
  · intro v hvS n
    by_contra hne
    have hvP : v ∈ P := ⟨n, hne⟩
    have hvPimage : v.under (𝓞 ℚ) ∈
        (fun v : V => v.under (𝓞 ℚ)) '' P :=
      Set.mem_image_of_mem (fun v : V => v.under (𝓞 ℚ)) hvP
    have hvQ : v.under (𝓞 ℚ) ∈ Q :=
      (hP.image (fun v : V => v.under (𝓞 ℚ))).mem_toFinset.mpr hvPimage
    have hvS' : v ∈ S := by
      apply Finset.mem_union_right
      simp only [S₁, Finset.mem_biUnion]
      exact ⟨v.under (𝓞 ℚ), hvQ,
        (finite_nuclearityPlacesAbove (F := F) (v.under (𝓞 ℚ))).mem_toFinset.mpr rfl⟩
    exact hvS hvS'

end RiemannMasullo
