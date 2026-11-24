module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.RingTheory.DedekindDomain.SInteger

/-! # §7.3.1 Saturated place sets and primary places

The first part of `RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a`, split off so that modules
that need only these declarations do not wait for the rest of that file.
-/

@[expose] public noncomputable section

open Asymptotics Filter Function IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 600000
set_option Elab.async false

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "Jₛ" => SIdeleQuotient F S
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "J₁" => (mₛ).ker
local notation "Xₛ" => QuasiCharacter Jₛ
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "twistₛ" => quasiCharacterNormTwist (G := Jₛ) mₛ
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "dualₛ" => dualQuasiCharacter (G := Jₛ) mₛ
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "chart(" χ ")" => twistₛ ((circleToComplex).comp (χ))
local notation "onComponent(" c ", " ω ")" =>
  (normOneRestriction mₛ c = (circleToComplex).comp ω)
local notation "Θₛ(" ω ")" => SLocalHomogeneousThetaSpace F S ω
local notation "Kₛ(" ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)
local notation "PV(" places ", " hT ", " ω ")" =>
  (sLocalHomogeneousThetaPrincipalValue (F := F) (S := S) (T := places) hT ω).range
local notation "PicTrivial" => Subsingleton (CommRing.Pic ((S : Set V).integer F))

/-- Paper: Situation 7.3.1.1(1), p. 340.
A finite set of places is saturated if it contains the entire fiber over every
rational prime that occurs below a member. -/
def IsSaturatedPlaceSet (S : Finset V) : Prop :=
  ∀ ⦃v w : V⦄, v ∈ S → w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S

/-- Paper: Situation 7.3.1.1(1), p. 340.
The empty set of finite places is saturated. -/
theorem isSaturatedPlaceSet_empty : IsSaturatedPlaceSet (∅ : Finset V) := by
  intro v w hv _
  exact absurd hv (Finset.notMem_empty v)

open Classical in
/-- Paper: Situation 7.3.1.1(2), p. 340.
The primary part of S at p consists of its places lying over p.
Deviation: A rational prime is represented by its place in the ring of integers of ℚ. -/
def sLocalPrimaryPlaces (S : Finset V) (p : Vℚ) : Finset V :=
  S.filter fun v ↦ v.under (𝓞 ℚ) = p

/-- Paper: Situation 7.3.1.1(2), p. 340.
A place belongs to the primary part exactly when it belongs to S and lies over p. -/
theorem mem_sLocalPrimaryPlaces (p : Vℚ) (v : V) :
    v ∈ sLocalPrimaryPlaces S p ↔ v ∈ S ∧ v.under (𝓞 ℚ) = p := by
  simp [sLocalPrimaryPlaces]

/-- Paper: Situation 7.3.1.1(2), p. 340.
The primary part is a subset of the selected finite places. -/
theorem sLocalPrimaryPlaces_subset (S : Finset V) (p : Vℚ) :
    sLocalPrimaryPlaces S p ⊆ S := by
  intro v hv
  exact ((mem_sLocalPrimaryPlaces p v).1 hv).1

/-- Paper: Situation 7.3.1.1(1)–(2), p. 340.
If S is saturated and its primary part at p is nonempty, that part contains every place over p. -/
theorem mem_sLocalPrimaryPlaces_of_saturated (p : Vℚ) (_hS : IsSaturatedPlaceSet S)
    (_hp : (sLocalPrimaryPlaces S p).Nonempty) (v : V) :
    v ∈ sLocalPrimaryPlaces S p ↔ v.under (𝓞 ℚ) = p := by
  rw [mem_sLocalPrimaryPlaces]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  obtain ⟨w, hw⟩ := _hp
  rw [mem_sLocalPrimaryPlaces] at hw
  exact _hS hw.1 (h.trans hw.2.symm)


end RiemannMasullo
