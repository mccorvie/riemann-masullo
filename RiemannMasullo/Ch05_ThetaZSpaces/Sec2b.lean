module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3b

/-! # Homogeneous theta spaces and Fourier descent

Masullo, §5.2.2–5.2.4, pp. 232–239. Every S-local space includes all archimedean places.
-/

@[expose] public noncomputable section

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Topology
open scoped NumberField.AdeleRing NNReal

namespace RiemannMasullo

set_option quotPrecheck false

section MeromorphicComponents

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ) (hm : Continuous m) (ω : PontryaginDual m.ker)

local notation "Ωω(" χ ")" => {c : QuasiCharacter G // ∀ g : m.ker, c g.val = (χ g : ℂ)}

/-- Paper: (5.2.2.1), p. 232.
Twisting a quasi-character by a complex power of the norm preserves its norm-one restriction. -/
theorem quasiCharacterNormTwist_mem_component (c : Ωω(ω)) (z : ℂ) :
    ∀ g : m.ker, quasiCharacterNormTwist m hm c.val z g.val = (ω g : ℂ) := by sorry

/-- Paper: (5.2.2.2), p. 232.
The meromorphic space on a component uses the pole bounds restricted to that component.
Its topology is compact convergence on the component's regular locus. -/
def meromorphicNormOneComponent (orderBound : QuasiCharacter G → WithTop ℤ) :
    Submodule ℂ C({c : Ωω(ω) // 0 ≤ orderBound c.val}, ℂ) :=
  meromorphicWithPoleBound (X := Ωω(ω))
    (fun c z ↦ ⟨quasiCharacterNormTwist m hm c.val z,
      quasiCharacterNormTwist_mem_component m hm ω c z⟩)
    (fun c ↦ orderBound c.val)

/-- Paper: (5.2.2.2), p. 232.
Restriction to the norm-one components identifies the meromorphic space with the product
of its component spaces, with their compact-convergence topologies.
Deviation: The two idelic instances are expressed by the common norm-chart statement.
The formula on regular values specifies the restriction map. -/
theorem meromorphicWithPoleBound_equiv_components [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (hproper : IsProperMap m) (hn : ∃ g, m g ≠ 1)
    (orderBound : QuasiCharacter G → WithTop ℤ) :
    ∃ e : ↥(meromorphicWithPoleBound (quasiCharacterNormTwist m hm) orderBound) ≃L[ℂ]
        (∀ χ : PontryaginDual m.ker, ↥(meromorphicNormOneComponent m hm χ orderBound)),
      ∀ f χ c, (e f χ).val c = f.val ⟨c.val.val, c.property⟩ := by sorry

end MeromorphicComponents

variable {F : Type*} [Field F] [NumberField F]
variable {S T U : Finset (HeightOneSpectrum (𝓞 F))}

local notation "ℬ𝔽" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "ℬₛ(" S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "Θ𝔽" => GlobalAdelicThetaSpace F
local notation "Θₛ(" S ")" => SLocalAdelicThetaSpace F S
local notation "K𝔽" => LinearMap.ker (adelicThetaLinearMap F)
local notation "Kₛ(" S ")" => LinearMap.ker (sLocalAdelicTheta F S)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Jₛ(" S ")" => SIdeleQuotient F S
local notation "m𝔽" => ideleClassNorm F
local notation "mₛ(" S ")" => sIdeleQuotientNorm F S
local notation "C₁" => MonoidHom.ker m𝔽
local notation "J₁(" S ")" => MonoidHom.ker (mₛ(S))
local notation "Θ𝔽ω(" ω ")" => GlobalHomogeneousThetaSpace F ω
local notation "Θₛω(" S ", " ω ")" => SLocalHomogeneousThetaSpace F S ω
local notation "K𝔽ω(" ω ")" => LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)
local notation "Kₛω(" S ", " ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)

section StructureTheorem

-- TODO(paper-gap): Footnotes 4–6 on pp. 233–235 request revisions or flag unfinished
-- work. The proof invokes a descended stage projection through "(??)" on p. 234.
-- Equation (5.2.3.4) also omits the local Haar masses; see ERRATA I96.

/-- Paper: Theorem 5.2.3.1, p. 233.
A norm-one character is unramified outside S if it extends to an idelic quasi-character
unramified outside S. Norm twists are trivial on every local integer unit. -/
def NormOneCharacterUnramifiedOutside (ω : PontryaginDual C₁)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∃ c : unramifiedOutside F S, ∀ x : C₁, c.val x.val = (ω x : ℂ)

/-- Paper: Remark 5.2.3.3, p. 236.
Unramifiedness is equivalent to unique descent to the norm-one S-idele quotient.
Deviation: The descent identity is tested on norm-one ideles integral outside S. -/
theorem normOneCharacterUnramifiedOutside_iff (ω : PontryaginDual C₁) :
    NormOneCharacterUnramifiedOutside (F := F) ω S ↔
      ∃! χ : PontryaginDual (J₁(S)),
        ∀ (u : (integralAdelesOutside F S)ˣ) (x : C₁) (y : J₁(S)),
          let g := integralIdeleInsertion F S u
          x.val = QuotientGroup.mk g →
          y.val = QuotientGroup.mk (Units.map (adeleProjection F S).toMonoidHom g) →
          χ y = ω x := by sorry

variable (S) in
/-- Paper: Theorem 5.2.3.1, p. 233.
The descended S-local character is determined on the norm-one S-idele classes. -/
def sLocalNormOneCharacter (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) : PontryaginDual (J₁(S)) :=
  ((normOneCharacterUnramifiedOutside_iff (F := F) (S := S) ω).mp hω).exists.choose

/-- Paper: Theorem 5.2.3.1, p. 233.
The descended character agrees with the global character on representatives. -/
theorem sLocalNormOneCharacter_apply (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S)
    (u : (integralAdelesOutside F S)ˣ) (x : C₁) (y : J₁(S))
    (hx : x.val = QuotientGroup.mk (integralIdeleInsertion F S u))
    (hy : y.val = QuotientGroup.mk (Units.map (adeleProjection F S).toMonoidHom
      (integralIdeleInsertion F S u))) :
    sLocalNormOneCharacter (F := F) S ω hω y = ω x := by sorry

/-- Paper: Remark 5.2.3.3, p. 236.
The descended character agrees on norm-one classes with the S-idelic restriction
of any unramified extension from §3.1.2. -/
theorem sLocalNormOneCharacter_eq_sIdeleRestriction
    (ω : PontryaginDual C₁) (c : unramifiedOutside F S)
    (hc : ∀ x : C₁, c.val x.val = (ω x : ℂ)) (y : J₁(S)) :
    (sLocalNormOneCharacter (F := F) S ω ⟨c, hc⟩ y : ℂ) = sIdeleRestriction F S c y.val := by
  sorry

/-- Paper: Theorem 5.2.3.1, p. 233.
Unramifiedness outside S implies unramifiedness outside every larger set of places. -/
theorem NormOneCharacterUnramifiedOutside.mono {ω : PontryaginDual C₁}
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T) :
    NormOneCharacterUnramifiedOutside (F := F) ω T := by sorry

variable {ω : PontryaginDual (ideleClassNorm F).ker}

local notation "ωₛ(" S ", " h ")" => sLocalNormOneCharacter (F := F) S ω h

/-- Paper: (5.2.3.1), p. 233.
The stage map of test functions preserves the homogeneous theta kernels. -/
theorem sLocalHomogeneousThetaTransition_preserves_kernel
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T) :
    let hT := NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω hST
    Kₛω(S, ωₛ(S, hω)) ≤ (Kₛω(T, ωₛ(T, hT))).comap
      (sAdeleSchwartzTransition F hST) := by sorry

/-- Paper: (5.2.3.1), p. 233.
The homogeneous theta transition is induced by adjoining integer indicators. -/
def sLocalHomogeneousThetaTransition (hω : NormOneCharacterUnramifiedOutside (F := F) ω S)
    (hST : S ⊆ T) : Θₛω(S, ωₛ(S, hω)) →ₗ[ℂ]
      Θₛω(T, ωₛ(T, NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω hST)) :=
  let hT := NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω hST
  (Kₛω(S, ωₛ(S, hω))).mapQ (Kₛω(T, ωₛ(T, hT))) (sAdeleSchwartzTransition F hST)
    (sLocalHomogeneousThetaTransition_preserves_kernel (F := F) (ω := ω) hω hST)

/-- Paper: (5.2.3.1), p. 233.
The transition is the unique linear map induced on homogeneous theta classes
by the test function transition. -/
theorem sLocalHomogeneousThetaTransition_spec
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T) :
    let hT := NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω hST
    let descends := fun π : Θₛω(S, ωₛ(S, hω)) →ₗ[ℂ] Θₛω(T, ωₛ(T, hT)) ↦
      π.comp (Kₛω(S, ωₛ(S, hω))).mkQ =
        (Kₛω(T, ωₛ(T, hT))).mkQ.comp (sAdeleSchwartzTransition F hST)
    descends (sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST) ∧
      ∀ π, descends π → π = sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST := by sorry

/-- Paper: Theorem 5.2.3.1(1), p. 233.
Each homogeneous stage is embedded as a closed subspace of a larger stage. -/
theorem sLocalHomogeneousThetaTransition_isClosedEmbedding
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T) :
    IsClosedEmbedding (sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST) := by sorry

/-- Paper: Theorem 5.2.3.1(1), p. 233.
The S-idele quotient acts jointly continuously on each homogeneous theta quotient.
Translation by a representative induces the action on its test-function class. -/
theorem existsUnique_sLocalHomogeneousThetaAction (χ : PontryaginDual (J₁(S))) :
    ∃! ρ : Jₛ(S) →* (Θₛω(S, χ) →L[ℂ] Θₛω(S, χ)),
      Continuous (fun p : Jₛ(S) × Θₛω(S, χ) ↦ ρ p.1 p.2) ∧
      ∀ (g : (SAdeleRing F S)ˣ) (f : ℬₛ(S)),
        ρ (QuotientGroup.mk g) ((Kₛω(S, χ)).mkQ f) =
          (Kₛω(S, χ)).mkQ (schwartzBruhatUnitTranslate g f) := by sorry

/-- Paper: Theorem 5.2.3.1(1), p. 233.
The homogeneous transition intertwines the descended actions on theta classes.
Deviation: The acting class is represented by an idele integral and invertible outside S. -/
theorem sLocalHomogeneousThetaTransition_equivariant
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (hST : S ⊆ T)
    (u : (integralAdelesOutside F S)ˣ) (x : Θₛω(S, ωₛ(S, hω))) :
    let hT := NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω hST
    let ρS := (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := S) (ωₛ(S, hω))).exists.choose
    let ρT := (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T) (ωₛ(T, hT))).exists.choose
    let π := sLocalHomogeneousThetaTransition (F := F) (ω := ω) hω hST
    let g := integralIdeleInsertion F S u
    let gS := Units.map (adeleProjection F S).toMonoidHom g
    let gT := Units.map (adeleProjection F T).toMonoidHom g
    π (ρS (QuotientGroup.mk gS) x) = ρT (QuotientGroup.mk gT) (π x) := by sorry

/-- Paper: Theorem 5.2.3.1(1), pp. 233–234.
Insertion of test functions into the adeles preserves the homogeneous theta kernels. -/
theorem sLocalHomogeneousThetaToGlobal_preserves_kernel
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) :
    Kₛω(S, ωₛ(S, hω)) ≤ (K𝔽ω(ω)).comap (sAdeleSchwartzToGlobal F S) := by sorry

/-- Paper: (5.2.3.2), p. 233.
The stage insertion into the global homogeneous quotient is induced by extension
of test functions with integer indicators outside S. -/
def sLocalHomogeneousThetaToGlobal (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) :
    Θₛω(S, ωₛ(S, hω)) →ₗ[ℂ] Θ𝔽ω(ω) :=
  (Kₛω(S, ωₛ(S, hω))).mapQ (K𝔽ω(ω)) (sAdeleSchwartzToGlobal F S)
    (sLocalHomogeneousThetaToGlobal_preserves_kernel (F := F) (ω := ω) hω)

/-- Paper: (5.2.3.2), p. 233.
The global homogeneous insertion agrees with test function insertion on representatives. -/
theorem sLocalHomogeneousThetaToGlobal_mk (hω : NormOneCharacterUnramifiedOutside (F := F) ω S)
    (f : ℬₛ(S)) :
    sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) hω ((Kₛω(S, ωₛ(S, hω))).mkQ f) =
      (K𝔽ω(ω)).mkQ (sAdeleSchwartzToGlobal F S f) := by sorry

/-- Paper: Theorem 5.2.3.1(1), pp. 233–234.
The stages form a strict system under the transition maps and identify the global
homogeneous space with its locally convex inductive limit.
Deviation: The compatible closed embeddings and exhaustion realize the algebraic
colimit inside the global space. The topology is specified by the final topology. -/
theorem sLocalHomogeneousTheta_inductiveLimit (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) :
    let I := {T : Finset (HeightOneSpectrum (𝓞 F)) // S ⊆ T}
    let h := fun T : I ↦ NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω T.property
    let i := fun T : I ↦ sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) (h T)
    (∀ T, IsClosedEmbedding (i T)) ∧
    (∀ (T U : I) (hTU : T.val ⊆ U.val),
      (i U).comp (sLocalHomogeneousThetaTransition (F := F) (ω := ω) (h T) hTU) = i T) ∧
    (∀ x : Θ𝔽ω(ω), ∃ T y, i T y = x) ∧
    (inferInstance : TopologicalSpace Θ𝔽ω(ω)) = locallyConvexFinalTopology i := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
A Hausdorff space admits a countable locally convex inductive presentation whose
stages, with their own topologies, are nuclear Fréchet spaces. -/
def HasNuclearFrechetPresentation.{v,u} (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] : Prop :=
  T2Space E ∧ ∃ (X : ℕ → Type u) (_ : ∀ k, AddCommGroup (X k)) (_ : ∀ k, Module ℂ (X k))
    (_ : ∀ k, TopologicalSpace (X k)), (∀ k, IsFrechetTVS (X k) ∧ IsNuclearTVS.{v} (X k)) ∧
      ∃ (j : ∀ k, X k →L[ℂ] X (k+1)) (i : ∀ k, X k →L[ℂ] E), IsInjectiveLCLimit j i

/-- Paper: Theorem 5.2.3.1(2), p. 233.
A countable nuclear Fréchet presentation gives an LF presentation. -/
theorem HasNuclearFrechetPresentation.isLFSpace {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (h : HasNuclearFrechetPresentation E) : IsLFSpace E := by
  obtain ⟨hE, X, a, m, t, hX, hlim⟩ := h
  exact ⟨hE, X, a, m, t, fun k ↦ (hX k).1, hlim⟩

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The global homogeneous theta quotient is a locally convex inductive limit of nuclear
Fréchet spaces. The test-function stages can be quotiented by the restricted kernel. -/
theorem globalHomogeneousThetaSpace_nuclearFrechetPresentation :
    HasNuclearFrechetPresentation Θ𝔽ω(ω) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The S-local homogeneous theta quotient is a locally convex inductive limit of nuclear
Fréchet spaces. The test-function stages can be quotiented by the restricted kernel. -/
theorem sLocalHomogeneousThetaSpace_nuclearFrechetPresentation (χ : PontryaginDual (J₁(S))) :
    HasNuclearFrechetPresentation (Θₛω(S, χ)) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The global homogeneous theta space is an LF-space. -/
theorem globalHomogeneousThetaSpace_lf : IsLFSpace Θ𝔽ω(ω) := by
  have h : HasNuclearFrechetPresentation.{0} Θ𝔽ω(ω) :=
    globalHomogeneousThetaSpace_nuclearFrechetPresentation
  exact h.isLFSpace

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The S-local homogeneous theta space is an LF-space. -/
theorem sLocalHomogeneousThetaSpace_lf (χ : PontryaginDual (J₁(S))) :
    IsLFSpace (Θₛω(S, χ)) := by
  have h : HasNuclearFrechetPresentation.{0} (Θₛω(S, χ)) :=
    sLocalHomogeneousThetaSpace_nuclearFrechetPresentation χ
  exact h.isLFSpace

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The global homogeneous quotient is complete for its additive uniformity. -/
theorem globalHomogeneousThetaSpace_complete :
    @CompleteSpace Θ𝔽ω(ω) (IsTopologicalAddGroup.rightUniformSpace _) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The S-local homogeneous quotient is complete for its additive uniformity. -/
theorem sLocalHomogeneousThetaSpace_complete (χ : PontryaginDual (J₁(S))) :
    @CompleteSpace (Θₛω(S, χ)) (IsTopologicalAddGroup.rightUniformSpace _) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The global homogeneous quotient is nuclear. -/
theorem globalHomogeneousThetaSpace_nuclear : IsNuclearTVS Θ𝔽ω(ω) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The S-local homogeneous quotient is nuclear. -/
theorem sLocalHomogeneousThetaSpace_nuclear (χ : PontryaginDual (J₁(S))) :
    IsNuclearTVS (Θₛω(S, χ)) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The global homogeneous quotient is Montel. -/
theorem globalHomogeneousThetaSpace_montel :
    BarrelledSpace ℂ Θ𝔽ω(ω) ∧ MontelSpace ℂ Θ𝔽ω(ω) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The S-local homogeneous quotient is Montel. -/
theorem sLocalHomogeneousThetaSpace_montel (χ : PontryaginDual (J₁(S))) :
    BarrelledSpace ℂ (Θₛω(S, χ)) ∧ MontelSpace ℂ (Θₛω(S, χ)) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the global homogeneous quotient is complete. -/
theorem globalHomogeneousThetaSpace_strongDual_complete :
    CompleteSpace (StrongDual ℂ Θ𝔽ω(ω)) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the S-local homogeneous quotient is complete. -/
theorem sLocalHomogeneousThetaSpace_strongDual_complete (χ : PontryaginDual (J₁(S))) :
    CompleteSpace (StrongDual ℂ (Θₛω(S, χ))) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the global homogeneous quotient is nuclear. -/
theorem globalHomogeneousThetaSpace_strongDual_nuclear :
    IsNuclearTVS (StrongDual ℂ Θ𝔽ω(ω)) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the S-local homogeneous quotient is nuclear. -/
theorem sLocalHomogeneousThetaSpace_strongDual_nuclear (χ : PontryaginDual (J₁(S))) :
    IsNuclearTVS (StrongDual ℂ (Θₛω(S, χ))) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the global homogeneous quotient is Montel. -/
theorem globalHomogeneousThetaSpace_strongDual_montel :
    BarrelledSpace ℂ (StrongDual ℂ Θ𝔽ω(ω)) ∧ MontelSpace ℂ (StrongDual ℂ Θ𝔽ω(ω)) := by sorry

/-- Paper: Theorem 5.2.3.1(2), p. 233.
The strong dual of the S-local homogeneous quotient is Montel. -/
theorem sLocalHomogeneousThetaSpace_strongDual_montel (χ : PontryaginDual (J₁(S))) :
    BarrelledSpace ℂ (StrongDual ℂ (Θₛω(S, χ))) ∧ MontelSpace ℂ (StrongDual ℂ (Θₛω(S, χ))) := by sorry

/-- Paper: Theorem 5.2.3.1(3), p. 233.
There are continuous idempotents onto the stage images. The net of these idempotents
converges to the identity uniformly on von Neumann bounded sets. -/
theorem sLocalHomogeneousTheta_projections (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) :
    let I := {T : Finset (HeightOneSpectrum (𝓞 F)) // S ⊆ T}
    let E := Θ𝔽ω(ω)
    let e := UniformConvergenceCLM.ofFun (σ := RingHom.id ℂ) (F := E)
      {B : Set E | IsVonNBounded ℂ B}
    ∃ P : I → E →L[ℂ] E,
      (∀ T : I,
        let hT := NormOneCharacterUnramifiedOutside.mono (F := F) (ω := ω) hω T.property
        let i := sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) hT
        (P T).toLinearMap.comp i = i ∧ LinearMap.range (P T).toLinearMap = LinearMap.range i) ∧
      Tendsto (fun T ↦ e (P T)) atTop (𝓝 (e (ContinuousLinearMap.id ℂ E))) := by sorry

end StructureTheorem

local notation "ρ𝔽" => (existsUnique_globalThetaAction (F := F)).exists.choose
local notation "ρₛ(" S ")" => (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
local notation "ρ𝔽₁" => (ρ𝔽).comp (MonoidHom.ker m𝔽).subtype
local notation "ρₛ₁(" S ")" => (ρₛ(S)).comp (MonoidHom.ker (mₛ(S))).subtype
local notation "E𝔽ω(" ω ")" => actionIsotype ρ𝔽₁ ω
local notation "Eₛω(" S ", " ω ")" => actionIsotype (ρₛ₁(S)) ω

local notation "μ𝔽₁" => normOneIdeleClassTamagawaMeasure F
local notation "μₛ₁(" S ")" => sLocalNormOneQuotientMeasure F S

section IsotypicAverages

local instance ideleClassGroupMeasurableSpaceSec2b (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _

local instance normOneSIdeleQuotientMeasurableSpaceSec2b (F : Type*) [Field F]
    [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (MonoidHom.ker (sIdeleQuotientNorm F S)) := borel _

-- TODO(paper-gap): The proof on pp. 236–237 gives no quotient-topology argument for
-- equicontinuity. Use the jointly continuous action on the theta quotient and compactness.
-- The Tamagawa averages act on their isotypes by Haar mass.

/-- Paper: Proposition 5.2.3.2(1), p. 236.
There is a unique continuous linear global Pettis average with the norm-one
Tamagawa measure and the conjugate character weight. -/
theorem existsUnique_globalThetaIsotypicAverage (ω : PontryaginDual C₁) :
    ∃! P : Θ𝔽 →L[ℂ] Θ𝔽,
      IsPettisIsotypicAverageOn μ𝔽₁ Set.univ ρ𝔽₁ ω P := by sorry

/-- Paper: Proposition 5.2.3.2(1), p. 236.
There is a unique continuous linear S-local Pettis average with the norm-one
quotient measure and the conjugate character weight. -/
theorem existsUnique_sLocalThetaIsotypicAverage (χ : PontryaginDual (J₁(S))) :
    ∃! P : Θₛ(S) →L[ℂ] Θₛ(S),
      IsPettisIsotypicAverageOn (μₛ₁(S)) Set.univ (ρₛ₁(S)) χ P := by sorry

end IsotypicAverages

local notation "P𝔽(" ω ")" => (existsUnique_globalThetaIsotypicAverage (F := F) ω).exists.choose
local notation "Pₛ(" S ", " χ ")" =>
  (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) χ).exists.choose

/-- Paper: Proposition 5.2.3.2(1), p. 236.
The global average induces a topological linear equivalence from the homogeneous quotient
to the closed isotype. Its map on ordinary theta classes is therefore open onto the isotype.
Deviation: The continuous coinvariant quotient is identified via Definition 5.2.2.1. -/
theorem globalThetaIsotypicAverage_equiv (ω : PontryaginDual C₁) :
    IsClosed (E𝔽ω(ω) : Set Θ𝔽) ∧
      ∃ e : Θ𝔽ω(ω) ≃L[ℂ] E𝔽ω(ω), ∀ f : ℬ𝔽,
        (e ((K𝔽ω(ω)).mkQ f) : Θ𝔽) = P𝔽(ω) ((K𝔽).mkQ f) := by sorry

/-- Paper: Proposition 5.2.3.2(1), p. 236.
The S-local average induces a topological linear equivalence from the homogeneous quotient
to the closed isotype. Its map on ordinary theta classes is therefore open onto the isotype.
Deviation: The continuous coinvariant quotient is identified via Definition 5.2.2.1. -/
theorem sLocalThetaIsotypicAverage_equiv (χ : PontryaginDual (J₁(S))) :
    IsClosed (Eₛω(S, χ) : Set (Θₛ(S))) ∧
      ∃ e : Θₛω(S, χ) ≃L[ℂ] Eₛω(S, χ), ∀ f : ℬₛ(S),
        (e ((Kₛω(S, χ)).mkQ f) : Θₛ(S)) = Pₛ(S, χ) ((Kₛ(S)).mkQ f) := by sorry

-- TODO(paper-gap): The global L² argument on p. 237 fails at norm zero for
-- the rational Gaussian. Apply character uniqueness on each compact norm-one fibre.

/-- Paper: Proposition 5.2.3.2(2), p. 236.
The canonical global map to the product of homogeneous theta quotients is
continuous and injective. -/
theorem exists_globalThetaToHomogeneousProduct :
    ∃ P : Θ𝔽 →L[ℂ] (∀ ω : PontryaginDual C₁, Θ𝔽ω(ω)),
      Injective P ∧ ∀ (f : ℬ𝔽) ω, P ((K𝔽).mkQ f) ω = (K𝔽ω(ω)).mkQ f := by sorry

/-- Paper: Proposition 5.2.3.2(2), p. 236.
The canonical S-local map to the product of homogeneous theta quotients is
continuous and injective. -/
theorem exists_sLocalThetaToHomogeneousProduct :
    ∃ P : Θₛ(S) →L[ℂ] (∀ χ : PontryaginDual (J₁(S)), Θₛω(S, χ)),
      Injective P ∧ ∀ (f : ℬₛ(S)) χ, P ((Kₛ(S)).mkQ f) χ = (Kₛω(S, χ)).mkQ f := by sorry

local notation "M𝔽ω(" ω ")" => meromorphicNormOneComponent m𝔽
  (isProperMap_ideleClassNorm F).continuous ω (globalIdelicOrderBound (F := F))
local notation "Mₛω(" S ", " ω ")" => meromorphicNormOneComponent (mₛ(S))
  (isProperMap_sIdeleQuotientNorm F S).continuous ω (sLocalIdelicOrderBound (F := F) (S := S))

/-- Paper: (5.2.3.14), p. 236.
The global Mellin transform on homogeneous classes is continuous and injective.
On a representative it gives the component of the global Mellin transform in (5.2.2.2). -/
theorem exists_globalHomogeneousThetaMellin (ω : PontryaginDual C₁) :
    ∃ Z : Θ𝔽ω(ω) →L[ℂ] ↥(M𝔽ω(ω)), Injective Z ∧
      ∀ (f : ℬ𝔽) c,
        (Z ((K𝔽ω(ω)).mkQ f)).val c =
          (globalIdelicMellin (F := F) f).val ⟨c.val.val, c.property⟩ := by sorry

/-- Paper: (5.2.3.14), p. 236.
The S-local Mellin transform on homogeneous classes is continuous and injective.
On a representative it gives the component of the S-local Mellin transform in (5.2.2.2). -/
theorem exists_sLocalHomogeneousThetaMellin (χ : PontryaginDual (J₁(S))) :
    ∃ Z : Θₛω(S, χ) →L[ℂ] ↥(Mₛω(S, χ)), Injective Z ∧
      ∀ (f : ℬₛ(S)) c,
        (Z ((Kₛω(S, χ)).mkQ f)).val c =
          (sLocalIdelicMellin (F := F) (S := S) f).val ⟨c.val.val, c.property⟩ := by sorry

-- TODO(paper-gap): Ordinary insertion does not in general intertwine isotype
-- projections onto subspaces. Normalizing the averages does not fix this.

/-- Paper: (5.2.3.15), p. 236.
Global insertion commutes with passage to homogeneous theta quotients.
Deviation: The vertical arrows are the canonical quotients. The averages implement
these arrows via the respective identifications of the quotients with the isotypes. -/
theorem sLocalThetaToHomogeneous_commutes {ω : PontryaginDual C₁}
    (hω : NormOneCharacterUnramifiedOutside (F := F) ω S) (x : Θₛ(S)) :
    let P := (exists_globalThetaToHomogeneousProduct (F := F)).choose
    let Q := (exists_sLocalThetaToHomogeneousProduct (F := F) (S := S)).choose
    P (sLocalThetaToGlobal F S x) ω =
      sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) hω
        (Q x (sLocalNormOneCharacter (F := F) S ω hω)) := by sorry

section TranslationRelations

local notation "diag𝔽" => IdeleGroup.unitEmbedding (𝓞 F) F
local notation "diagₛ(" S ")" => Units.map
  (((adeleProjection F S).comp (integralAdelesOutside F S).subtype).comp
    (integralAdeleDiagonal F S)).toMonoidHom

local notation "V𝔽" => Submodule.span ℂ (Set.range (fun p : Fˣ × ℬ𝔽 ↦
  p.2 - schwartzBruhatUnitTranslate (R := 𝔸[F]) (diag𝔽 p.1) p.2))
local notation "Vₛ(" S ")" => Submodule.span ℂ (Set.range (fun
  p : ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ × ℬₛ(S) ↦
    p.2 - schwartzBruhatUnitTranslate (R := SAdeleRing F S) (diagₛ(S) p.1) p.2))

-- TODO(paper-gap): The pullback topologies below identify the whole theta kernel
-- with zero. For example, an odd rational Schwartz function with even finite part
-- is in the global kernel. The bornological closure assertion on p. 238 needs a
-- separate argument and the bornological quotient and module constructions.

/-- Paper: Remark 5.2.3.4(1), p. 237.
The S-local theta kernel is the closure of the span of S-unit translation differences
for the topology pulled back from the theta quotient.
Deviation: This topology on test functions need not be Hausdorff. -/
theorem sLocalThetaKernel_eq_induced_closure (S : Finset (HeightOneSpectrum (𝓞 F))) :
    let q : ℬₛ(S) → Θₛ(S) := (Kₛ(S)).mkQ
    let t : TopologicalSpace (ℬₛ(S)) := TopologicalSpace.induced q inferInstance
    let V := Vₛ(S)
    let K : Set (ℬₛ(S)) := (Kₛ(S) : Set (ℬₛ(S)))
    @closure _ t V.carrier = K := by sorry

/-- Paper: Remark 5.2.3.4(2), p. 237.
The global theta kernel is the closure of the span of principal translation differences
for the topology pulled back from the theta quotient.
Deviation: This topology on test functions need not be Hausdorff. -/
theorem globalThetaKernel_eq_induced_closure :
    let q : ℬ𝔽 → Θ𝔽 := (K𝔽).mkQ
    let t := TopologicalSpace.induced q inferInstance
    let V : Set ℬ𝔽 := (V𝔽).carrier
    @closure _ t V = (K𝔽 : Set ℬ𝔽) := by sorry

/-- Paper: Remark 5.2.3.4, p. 238.
The algebraic S-unit coinvariants surject canonically onto the S-local theta quotient.
Deviation: The source is the quotient by the relation span. -/
theorem exists_sLocalAlgebraicCoinvariants_to_theta (S : Finset (HeightOneSpectrum (𝓞 F))) :
    let V := Vₛ(S)
    ∃ q : (ℬₛ(S) ⧸ V) →ₗ[ℂ] Θₛ(S),
      Surjective q ∧ q.comp V.mkQ = (Kₛ(S)).mkQ := by sorry

/-- Paper: Remark 5.2.3.4, p. 238.
The algebraic principal coinvariants surject canonically onto the global theta quotient.
Deviation: The source is the quotient by the relation span. -/
theorem exists_globalAlgebraicCoinvariants_to_theta :
    let V : Submodule ℂ ℬ𝔽 := V𝔽
    ∃ q : (ℬ𝔽 ⧸ V) →ₗ[ℂ] Θ𝔽, Surjective q ∧ q.comp V.mkQ = (K𝔽).mkQ := by sorry

/-- Paper: Remark 5.2.3.4, pp. 237–238.
The S-local theta quotient is bornological. Every seminorm bounded on all of its
von Neumann bounded sets is continuous. -/
theorem sLocalTheta_bornological :
    ∀ p : Seminorm ℂ (Θₛ(S)),
      (∀ B : Set (Θₛ(S)), IsVonNBounded ℂ B → BddAbove (p '' B)) →
      Continuous p := by sorry

/-- Paper: Remark 5.2.3.4, pp. 237–238.
The global theta quotient is bornological. Every seminorm bounded on all of its
von Neumann bounded sets is continuous. -/
theorem globalTheta_bornological :
    ∀ p : Seminorm ℂ Θ𝔽, (∀ B : Set Θ𝔽, IsVonNBounded ℂ B → BddAbove (p '' B)) →
      Continuous p := by sorry

end TranslationRelations

section IsotypicMellin

attribute [local instance] ideleClassGroupMeasurableSpaceSec2b normOneSIdeleQuotientMeasurableSpaceSec2b

/-- Paper: Remark 5.2.3.5, p. 238.
On each component the global Mellin transform of the Tamagawa average equals
the Mellin transform of the original class times the norm-one Haar mass. -/
theorem globalThetaMellin_isotypicAverage (ω : PontryaginDual C₁) (x : Θ𝔽)
    (c : {c : QuasiCharacter C𝔽 // 0 ≤ globalIdelicOrderBound c})
    (hc : ∀ g : C₁, c.val g.val = (ω g : ℂ)) :
    (globalThetaMellin (F := F) (P𝔽(ω) x)).val c =
      ((μ𝔽₁).real Set.univ : ℂ) * (globalThetaMellin (F := F) x).val c := by sorry

/-- Paper: Remark 5.2.3.5, p. 238.
On each S-local component the Mellin transform of the Tamagawa average equals
the Mellin transform of the original class times the S-local norm-one Haar mass. -/
theorem sLocalThetaMellin_isotypicAverage (χ : PontryaginDual (J₁(S))) (x : Θₛ(S))
    (c : {c : QuasiCharacter (Jₛ(S)) // 0 ≤ sLocalIdelicOrderBound c})
    (hc : ∀ g : J₁(S), c.val g.val = (χ g : ℂ)) :
    (sLocalThetaMellin (F := F) (S := S) (Pₛ(S, χ) x)).val c =
      ((μₛ₁(S)).real Set.univ : ℂ) * (sLocalThetaMellin (F := F) (S := S) x).val c := by sorry

end IsotypicMellin

section Fourier

-- TODO(paper-gap): The global map is described as inversion on p. 238.
-- The identity on theta functions has a norm factor and two zero terms,
-- as in adelicTheta_riemannRoch.

/-- Paper: Theorem 5.2.4.1(1), pp. 238–239.
S-adelic Fourier transform descends to a unique continuous linear involution
on the S-local theta quotient. -/
theorem existsUnique_sLocalThetaFourier :
    ∃! e : Θₛ(S) ≃L[ℂ] Θₛ(S),
      Involutive e ∧ ∀ f : ℬₛ(S),
        e ((Kₛ(S)).mkQ f) = (Kₛ(S)).mkQ (sAdeleSchwartzFourier (F := F) (S := S) f) :=
  by sorry

/-- Paper: Theorem 5.2.4.1(2), p. 239.
Adelic Fourier transform descends to a unique continuous linear involution
on the global theta quotient.
Deviation: The descent identity is tested on global test functions, as in the proof. -/
theorem existsUnique_globalThetaFourier :
    ∃! e : Θ𝔽 ≃L[ℂ] Θ𝔽,
      Involutive e ∧ ∀ f : ℬ𝔽,
        e ((K𝔽).mkQ f) = (K𝔽).mkQ (adeleSchwartzFourier (F := F) f) :=
  by sorry

-- TODO(paper-gap): The unrestricted compatibility assertions on p. 239 fail.
-- For ℚ(i) above 2 the Fourier image of the integer indicator is half the inverse-
-- different indicator. An archimedean bump supported near 1/2 detects the difference.

set_option maxSynthPendingDepth 8 in
/-- Paper: Theorem 5.2.4.1(1), p. 239.
The S-local Fourier involutions commute with stage enlargement away from the different.
Deviation: Every added place is required to have a Fourier-fixed integer indicator. -/
theorem sLocalThetaFourier_transition (hST : S ⊆ T)
    (hgood : ∀ v : HeightOneSpectrum (𝓞 F),
      v ∈ T → v ∉ S → ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F))
    (x : Θₛ(S)) :
    let fourierS := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    let fourierT := (existsUnique_sLocalThetaFourier (F := F) (S := T)).exists.choose
    let transition := sLocalThetaTransition (F := F) (S := S) (T := T) hST
    fourierT (transition x) = transition (fourierS x) := by sorry

set_option maxSynthPendingDepth 8 in
/-- Paper: (5.2.4.4), p. 239.
The local and global Fourier involutions commute with insertion once S contains
every place dividing the different.
Deviation: The places outside S must have Fourier-fixed integer indicators. -/
theorem sLocalThetaFourier_toGlobal
    (hgood : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (x : Θₛ(S)) :
    let fourierS := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    let fourier := (existsUnique_globalThetaFourier (F := F)).exists.choose
    fourier (sLocalThetaToGlobal F S x) = sLocalThetaToGlobal F S (fourierS x) := by sorry

/-- Paper: Theorem 5.2.4.1(1), p. 239.
S-local Fourier transform exchanges each norm-one isotype with its conjugate. -/
theorem sLocalThetaFourier_mem_isotype (χ : PontryaginDual (J₁(S))) (x : Θₛ(S)) :
    let fourier := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    fourier x ∈ Eₛω(S, χ⁻¹) ↔ x ∈ Eₛω(S, χ) := by sorry

/-- Paper: Theorem 5.2.4.1(2), p. 239.
Global Fourier transform exchanges each norm-one isotype with its conjugate. -/
theorem globalThetaFourier_mem_isotype (ω : PontryaginDual C₁) (x : Θ𝔽) :
    let fourier := (existsUnique_globalThetaFourier (F := F)).exists.choose
    fourier x ∈ E𝔽ω(ω⁻¹) ↔ x ∈ E𝔽ω(ω) := by sorry

end Fourier

end RiemannMasullo
