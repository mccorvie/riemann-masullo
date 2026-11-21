module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec1d

/-! # Structure Theorem I for adelic theta spaces

Masullo, §5.2.1–5.2.2, pp. 230–232. The finite sets index the finite places.
Every S-adelic space below includes all archimedean places.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Topology
open scoped NumberField.AdeleRing NNReal

namespace RiemannMasullo

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
local notation "C₁" => MonoidHom.ker (ideleClassNorm F)
local notation "J₁(" S ")" => MonoidHom.ker (sIdeleQuotientNorm F S)

section Topology

-- TODO(paper-gap): On p. 231 the Fréchet quotients of the test-function stages
-- give an LF presentation. Strictness requires control of their induced topologies.
-- See Example C.1.4.6(4) and Corollary C.1.5.13 for the bounded-lifting issue in (5.2.1.4).

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The global theta space is a strict LF-space.
Deviation: The Fréchet stages inherit nuclearity from the separately stated
nuclearity of the whole space under `isNuclearTVS_submodule`. -/
theorem globalAdelicThetaSpace_strictLF : IsStrictLFSpace Θ𝔽 := by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The S-local theta space is a strict LF-space.
Deviation: The Fréchet stages inherit nuclearity from the separately stated
nuclearity of the whole space under `isNuclearTVS_submodule`. -/
theorem sLocalAdelicThetaSpace_strictLF : IsStrictLFSpace (Θₛ(S)) := by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The global theta quotient is complete. -/
theorem globalAdelicThetaSpace_complete :
    @CompleteSpace Θ𝔽 (IsTopologicalAddGroup.rightUniformSpace Θ𝔽) := by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The S-local theta quotient is complete. -/
theorem sLocalAdelicThetaSpace_complete :
    @CompleteSpace (Θₛ(S)) (IsTopologicalAddGroup.rightUniformSpace (Θₛ(S))) := by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The global theta quotient is nuclear. -/
theorem globalAdelicThetaSpace_nuclear : IsNuclearTVS Θ𝔽 := by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The S-local theta quotient is nuclear. -/
theorem sLocalAdelicThetaSpace_nuclear : IsNuclearTVS (Θₛ(S)) := by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The global theta quotient is barrelled. -/
theorem globalAdelicThetaSpace_barrelled : BarrelledSpace ℂ Θ𝔽 := by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
Closed bounded subsets are compact in the global theta quotient. -/
theorem globalAdelicThetaSpace_montel : MontelSpace ℂ Θ𝔽 := by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The S-local theta quotient is barrelled. -/
theorem sLocalAdelicThetaSpace_barrelled : BarrelledSpace ℂ (Θₛ(S)) := by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
Closed bounded subsets are compact in the S-local theta quotient. -/
theorem sLocalAdelicThetaSpace_montel : MontelSpace ℂ (Θₛ(S)) := by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the global theta quotient is complete. -/
theorem globalAdelicThetaSpace_strongDual_complete : CompleteSpace (StrongDual ℂ Θ𝔽) :=
  by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the S-local theta quotient is complete. -/
theorem sLocalAdelicThetaSpace_strongDual_complete : CompleteSpace (StrongDual ℂ (Θₛ(S))) :=
  by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the global theta quotient is nuclear. -/
theorem globalAdelicThetaSpace_strongDual_nuclear : IsNuclearTVS (StrongDual ℂ Θ𝔽) :=
  by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the S-local theta quotient is nuclear. -/
theorem sLocalAdelicThetaSpace_strongDual_nuclear : IsNuclearTVS (StrongDual ℂ (Θₛ(S))) :=
  by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the global theta quotient is barrelled. -/
theorem globalAdelicThetaSpace_strongDual_barrelled :
    BarrelledSpace ℂ (StrongDual ℂ Θ𝔽) := by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
Closed bounded subsets are compact in the strong dual of the global theta quotient. -/
theorem globalAdelicThetaSpace_strongDual_montel : MontelSpace ℂ (StrongDual ℂ Θ𝔽) :=
  by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the S-local theta quotient is barrelled. -/
theorem sLocalAdelicThetaSpace_strongDual_barrelled :
    BarrelledSpace ℂ (StrongDual ℂ (Θₛ(S))) := by sorry

/-- Paper: Theorem 5.2.1.1(1), p. 230.
Closed bounded subsets are compact in the strong dual of the S-local theta quotient. -/
theorem sLocalAdelicThetaSpace_strongDual_montel : MontelSpace ℂ (StrongDual ℂ (Θₛ(S))) :=
  by sorry

/-- Paper: (5.2.1.4), p. 231.
The transpose of the global theta quotient map is an embedding for the strong dual topologies. -/
theorem globalThetaQuotient_transpose_isEmbedding :
    IsEmbedding (fun l : StrongDual ℂ Θ𝔽 ↦ l.comp (K𝔽).mkQL) := by sorry

end Topology

-- TODO(paper-gap): Footnote 1 on p. 230 asks for a version with an
-- I-exponentially decaying target without giving a statement.
-- TODO(paper-gap): Footnote 2 on p. 231 asks to adjust Theorem 5.2.1.1
-- and gives no replacement. Its proof needs a stage projection preserving
-- the theta kernel. For ℚ and S = {∞}, put e = 1_{ℤ̂}. Every tail functional
-- fixing e sends f − ρ(2)f, for f = φ ⊗ e, to (φ − c φ(·/2)) ⊗ e for some c.
-- For an even bump φ supported within 1/4 of ±1 with φ(±1) = 1, this has
-- theta values 2(1−c) and −2c at real scales 1 and 2. Thus the tensor
-- projections used on p. 73 cannot descend. The assertion on p. 232 about
-- convergence on bounded sets requires a family of projections on the quotients.

section Transitions

/-- Paper: Theorem 5.2.1.1(2), p. 230.
Schwartz–Bruhat transition sends the S-local theta kernel into the T-local theta kernel. -/
theorem sLocalThetaTransition_preserves_kernel (hST : S ⊆ T) :
    Kₛ(S) ≤ (Kₛ(T)).comap (sAdeleSchwartzTransition F hST) := by sorry

/-- Paper: (5.2.1.1), p. 230.
The transition on theta quotients is induced by the Schwartz–Bruhat stage transition. -/
def sLocalThetaTransition (hST : S ⊆ T) : Θₛ(S) →ₗ[ℂ] Θₛ(T) :=
  (Kₛ(S)).mapQ (Kₛ(T)) (sAdeleSchwartzTransition F hST)
    (sLocalThetaTransition_preserves_kernel hST)

/-- Paper: Theorem 5.2.1.1(2), p. 230.
The theta transition is the unique linear map taking each class to the class of its
Schwartz–Bruhat transition. -/
theorem sLocalThetaTransition_unique (hST : S ⊆ T) :
    let descends := fun π : Θₛ(S) →ₗ[ℂ] Θₛ(T) ↦
      π.comp (Kₛ(S)).mkQ = (Kₛ(T)).mkQ.comp (sAdeleSchwartzTransition F hST)
    descends (sLocalThetaTransition hST) ∧
      ∀ π, descends π → π = sLocalThetaTransition hST := by sorry

/-- Paper: Theorem 5.2.1.1(2), p. 230.
The transition on theta quotients embeds each stage as a closed subspace of a larger stage. -/
theorem sLocalThetaTransition_isClosedEmbedding (hST : S ⊆ T) :
    IsClosedEmbedding (sLocalThetaTransition (F := F) hST) := by sorry

/-- Paper: Theorem 5.2.1.1(2), p. 230.
Two successive theta transitions agree with the direct transition. -/
theorem sLocalThetaTransition_comp (hST : S ⊆ T) (hTU : T ⊆ U) :
    (sLocalThetaTransition (F := F) hTU).comp (sLocalThetaTransition hST) =
      sLocalThetaTransition (hST.trans hTU) := by sorry

/-- Paper: Theorem 5.2.1.1(3), p. 230.
The global insertion of a test function sends the corresponding S-local theta kernel
into the global theta kernel. -/
theorem sLocalThetaToGlobal_preserves_kernel :
    Kₛ(S) ≤ (K𝔽).comap (sAdeleSchwartzToGlobal F S) := by sorry

variable (F S) in
/-- Paper: (5.2.1.3), p. 230.
The insertion of S-local theta classes into global theta classes is the map
induced by the insertion of test functions. -/
def sLocalThetaToGlobal : Θₛ(S) →ₗ[ℂ] Θ𝔽 :=
  (Kₛ(S)).mapQ K𝔽 (sAdeleSchwartzToGlobal F S) sLocalThetaToGlobal_preserves_kernel

/-- Paper: (5.2.1.3), p. 230.
Inserting the class of a local test function gives the class of its extension to the adeles. -/
theorem sLocalThetaToGlobal_mk (f : ℬₛ(S)) :
    sLocalThetaToGlobal F S (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sAdeleSchwartzToGlobal F S f) := by sorry

/-- Paper: Theorem 5.2.1.1(3), p. 230.
The S-local theta space embeds topologically in the global theta space. -/
theorem sLocalThetaToGlobal_isEmbedding : IsEmbedding (sLocalThetaToGlobal F S) := by sorry

/-- Paper: Theorem 5.2.1.1(3), p. 231.
The global stage insertion has closed range, as used in Lemma 5.3.1.5. -/
theorem sLocalThetaToGlobal_isClosed_range :
    IsClosed (Set.range (sLocalThetaToGlobal F S)) := by
  let : UniformSpace (Θₛ(S)) := IsTopologicalAddGroup.rightUniformSpace _
  let : UniformSpace Θ𝔽 := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (Θₛ(S)) := isUniformAddGroup_of_addCommGroup
  let : IsUniformAddGroup Θ𝔽 := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace (Θₛ(S)) := sLocalAdelicThetaSpace_complete
  let : T2Space Θ𝔽 := (globalAdelicThetaSpace_strictLF (F := F)).1
  exact (AddMonoidHom.isUniformInducing_of_isInducing
    (sLocalThetaToGlobal_isEmbedding (F := F) (S := S)).isInducing).isComplete_range.isClosed

/-- Paper: Theorem 5.2.1.1(2), p. 230.
The stage insertions and transitions form a compatible family in the global quotient. -/
theorem sLocalThetaToGlobal_comp (hST : S ⊆ T) :
    (sLocalThetaToGlobal F T).comp (sLocalThetaTransition hST) = sLocalThetaToGlobal F S :=
  by sorry

/-- Paper: Theorem 5.2.1.1(2), p. 230.
Every global theta class comes from a finite stage. -/
theorem sLocalThetaToGlobal_exhaustive (x : Θ𝔽) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (y : Θₛ(S)),
      sLocalThetaToGlobal F S y = x := by sorry

/-- Paper: Theorem 5.2.1.1(2), p. 230.
The global quotient has the final locally convex topology for the S-local insertions.
Deviation: The compatible embeddings and exhaustion identify the algebraic colimit
with the global space, where the assertion becomes an equality of topologies. -/
theorem sLocalThetaToGlobal_finalTopology :
    (inferInstance : TopologicalSpace Θ𝔽) = locallyConvexFinalTopology (sLocalThetaToGlobal F) :=
  by sorry

/-- Paper: Theorem 5.2.1.1(2), p. 230.
Left translation by the global idele class group induces a jointly continuous linear
action on the global theta quotient.
Deviation: The action is characterized on test functions by idele representatives. -/
theorem existsUnique_globalThetaAction :
    ∃! ρ : C𝔽 →* (Θ𝔽 →L[ℂ] Θ𝔽),
      Continuous (fun p : C𝔽 × Θ𝔽 ↦ ρ p.1 p.2) ∧
      ∀ (g : IdeleGroup (𝓞 F) F) (f : ℬ𝔽),
        ρ (QuotientGroup.mk g) (Submodule.Quotient.mk f) =
          Submodule.Quotient.mk (schwartzBruhatUnitTranslate g f) := by sorry

/-- Paper: Theorem 5.2.1.1(2), p. 230.
Left translation by the S-idele quotient induces a jointly continuous linear
action on the S-local theta quotient.
Deviation: The action is characterized on test functions by S-idele representatives. -/
theorem existsUnique_sLocalThetaAction :
    ∃! ρ : Jₛ(S) →* (Θₛ(S) →L[ℂ] Θₛ(S)),
      Continuous (fun p : Jₛ(S) × Θₛ(S) ↦ ρ p.1 p.2) ∧
      ∀ (g : (SAdeleRing F S)ˣ) (f : ℬₛ(S)),
        ρ (QuotientGroup.mk g) (Submodule.Quotient.mk f) =
          Submodule.Quotient.mk (schwartzBruhatUnitTranslate g f) := by sorry

/-- Paper: Theorem 5.2.1.1(2), p. 230.
The S-to-T theta transition intertwines the actions of the S-idele classes.
Deviation: On an integral-outside-S idele representative, the two actions are
given by projecting it to S and T, respectively. -/
theorem sLocalThetaTransition_equivariant (hST : S ⊆ T)
    (u : (integralAdelesOutside F S)ˣ) (f : ℬₛ(S)) :
    let g := integralIdeleInsertion F S u
    let gS := Units.map (adeleProjection F S).toMonoidHom g
    let gT := Units.map (adeleProjection F T).toMonoidHom g
    sLocalThetaTransition hST (Submodule.Quotient.mk (schwartzBruhatUnitTranslate gS f)) =
      Submodule.Quotient.mk
        (schwartzBruhatUnitTranslate gT (sAdeleSchwartzTransition F hST f)) := by sorry

/-- Paper: Theorem 5.2.1.1(3), p. 230.
The S-local insertion intertwines the actions of S-idele classes through their
projection to the S-idele quotient and their inclusion in the global classes.
Deviation: The equation is on representatives of the acting group and the theta quotient. -/
theorem sLocalThetaToGlobal_equivariant (u : (integralAdelesOutside F S)ˣ) (f : ℬₛ(S)) :
    let g := integralIdeleInsertion F S u
    let gS := Units.map (adeleProjection F S).toMonoidHom g
    sLocalThetaToGlobal F S (Submodule.Quotient.mk (schwartzBruhatUnitTranslate gS f)) =
      Submodule.Quotient.mk
        (schwartzBruhatUnitTranslate g (sAdeleSchwartzToGlobal F S f)) := by sorry

end Transitions

section HomogeneousQuotients

-- TODO(paper-gap): Footnote 3 on p. 232 asks to adjust the introduction
-- to §5.2.2 without specifying the adjustment.

-- Use the Borel structure and the Haar normalization in §3.3.1, as in §5.1.
local instance normOneSIdeleQuotientMeasurableSpaceSec2 (F : Type*) [Field F]
    [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (MonoidHom.ker (sIdeleQuotientNorm F S)) := borel _

local instance normOneSIdeleQuotientHaarSec2 :
    Measure.IsHaarMeasure (sLocalNormOneQuotientMeasure F S) :=
  (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1

variable (F) in
/-- Paper: Definition 5.2.2.1(1), p. 232.
The global homogeneous theta transform is the complex-linear map of §2.2.5. -/
def homogeneousAdelicThetaLinearMap (ω : PontryaginDual C₁) :
    ℬ𝔽 →ₗ[ℂ] C(C𝔽, ℂ) :=
  IsLinearMap.mk' (homogeneousAdelicTheta ω) (homogeneousAdelicTheta_isLinear ω)

/-- Paper: Definition 5.2.2.1(1), p. 232.
The linear transform evaluates to the global homogeneous theta function. -/
theorem homogeneousAdelicThetaLinearMap_apply (ω : PontryaginDual C₁) (f : ℬ𝔽) :
    homogeneousAdelicThetaLinearMap F ω f = homogeneousAdelicTheta ω f := by sorry

variable (F S) in
/-- Paper: Definition 5.2.2.1(2), p. 232.
The S-local homogeneous theta transform uses the norm-one quotient measure of §3.3.1. -/
def sLocalHomogeneousAdelicThetaLinearMap (ω : PontryaginDual (J₁(S))) :
    ℬₛ(S) →ₗ[ℂ] C(Jₛ(S), ℂ) :=
  sLocalHomogeneousAdelicTheta F S (sLocalNormOneQuotientMeasure F S) ω

/-- Paper: Definition 5.2.2.1(2), p. 232.
The linear transform evaluates to the S-local homogeneous theta function
with the norm-one Tamagawa measure of §3.3.1. -/
theorem sLocalHomogeneousAdelicThetaLinearMap_apply (ω : PontryaginDual (J₁(S)))
    (f : ℬₛ(S)) (g : Jₛ(S)) :
    sLocalHomogeneousAdelicThetaLinearMap F S ω f g =
      ∫ h : J₁(S), sLocalAdelicThetaOnClasses F S f (g * h.val) * (ω h : ℂ)
        ∂sLocalNormOneQuotientMeasure F S := by sorry

local notation "K𝔽ω(" ω ")" => LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)
local notation "Kₛω(" ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F _ ω)

variable (F) in
/-- Paper: Definition 5.2.2.1(1), p. 232.
The global homogeneous theta space is the topological quotient of Schwartz–Bruhat
functions by the kernel of the homogeneous theta transform. -/
abbrev GlobalHomogeneousThetaSpace (ω : PontryaginDual C₁) :=
  ℬ𝔽 ⧸ K𝔽ω(ω)

/-- Paper: Definition 5.2.2.1(1), p. 232.
Two test functions give the same global homogeneous theta class exactly when
their homogeneous theta functions agree. -/
theorem globalHomogeneousThetaSpace_mk_eq_iff (ω : PontryaginDual C₁) (f g : ℬ𝔽) :
    (Submodule.Quotient.mk f : GlobalHomogeneousThetaSpace F ω) = Submodule.Quotient.mk g ↔
      homogeneousAdelicTheta ω f = homogeneousAdelicTheta ω g := by sorry

variable (F S) in
/-- Paper: Definition 5.2.2.1(2), p. 232.
The S-local homogeneous theta space is the topological quotient of S-local
Schwartz–Bruhat functions by the kernel of the S-local homogeneous transform. -/
abbrev SLocalHomogeneousThetaSpace (ω : PontryaginDual (J₁(S))) :=
  ℬₛ(S) ⧸ Kₛω(ω)

/-- Paper: Definition 5.2.2.1(2), p. 232.
Two S-local test functions give the same homogeneous theta class exactly when
their homogeneous theta functions agree. -/
theorem sLocalHomogeneousThetaSpace_mk_eq_iff (ω : PontryaginDual (J₁(S))) (f g : ℬₛ(S)) :
    (Submodule.Quotient.mk f : SLocalHomogeneousThetaSpace F S ω) = Submodule.Quotient.mk g ↔
      sLocalHomogeneousAdelicThetaLinearMap F S ω f =
        sLocalHomogeneousAdelicThetaLinearMap F S ω g := by sorry

/-- Paper: Definition 5.2.2.1(1), p. 232.
The homogeneous theta quotient identifies canonically with the quotient of ordinary
theta space by the closed span of the character-twisted translation differences. -/
theorem globalHomogeneousThetaSpace_equiv_coinvariants (ω : PontryaginDual C₁) :
    let ρ := (existsUnique_globalThetaAction (F := F)).exists.choose
    let D := (Submodule.span ℂ (Set.range (fun p : C₁ × Θ𝔽 ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1.val p.2))).topologicalClosure
    ∃ e : GlobalHomogeneousThetaSpace F ω ≃L[ℂ] (Θ𝔽 ⧸ D),
      ∀ f : ℬ𝔽, e (Submodule.Quotient.mk f) = D.mkQ ((K𝔽).mkQ f) := by sorry

/-- Paper: Definition 5.2.2.1(2), p. 232.
The S-local homogeneous quotient identifies canonically with the quotient of ordinary
S-local theta space by the closed span of the twisted norm-one translation differences. -/
theorem sLocalHomogeneousThetaSpace_equiv_coinvariants (ω : PontryaginDual (J₁(S))) :
    let ρ := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
    let D := (Submodule.span ℂ (Set.range (fun p : J₁(S) × Θₛ(S) ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1.val p.2))).topologicalClosure
    ∃ e : SLocalHomogeneousThetaSpace F S ω ≃L[ℂ] (Θₛ(S) ⧸ D),
      ∀ f : ℬₛ(S), e (Submodule.Quotient.mk f) = D.mkQ ((Kₛ(S)).mkQ f) := by sorry

end HomogeneousQuotients

-- The first digest ends at Definition 5.2.2.1. The isotypic structure
-- results and the Fourier descent statements remain for a subsequent digest.
-- TODO(continuation): (5.2.2.2), Theorem 5.2.3.1, Proposition 5.2.3.2,
-- Remarks 5.2.3.3–5.2.3.5 and the individual involutions in Theorem 5.2.4.1.
-- TODO(paper-gap): The global L² argument on p. 237 fails for the rational
-- Gaussian, whose theta is asymptotic to 1/t at the origin. Character
-- uniqueness can be applied on each compact norm-one fiber instead.
-- TODO(paper-gap): On p. 234 the proof of Theorem 5.2.3.1 refers to the
-- descending idempotent as "(??)". The proof on p. 231 does not construct
-- a kernel-preserving Schwartz–Bruhat projection.
-- TODO(paper-gap): In Remark 5.2.3.4 the topology induced from the theta
-- quotient is called Hausdorff on the test space. For ℚ it identifies every
-- odd test function with zero.
-- TODO(paper-gap): The Fourier compatibility in Theorem 5.2.4.1 fails upon
-- adding a place dividing the different. For ℚ(i) at the place above 2,
-- Fourier sends the integer indicator to half the inverse-different indicator.

end RiemannMasullo
