module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b

/-!
# Chapter 5.2.3–5.2.4: statements that are false as printed

The printed claims are propositions, with separate statements of their negations.
The corresponding theta-space results are in `Sec2b.lean`, and `ERRATA.md` records the errors.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Test(" F ", " S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "GlobalTest(" F ")" => SchwartzBruhat (Multiplicative 𝔸[F])

open Classical in
/-- Paper: Theorem 5.2.3.1, (5.2.3.4), p. 233.
The displayed formula gives one geometric Euler factor per place added to S on insertion into T.
Deviation: We read the two-argument `L_T` as the test-function transform `Z_T` of §5.1 and
record (5.2.3.4) as an identity of transforms for arbitrary tests. The proof invokes it
under source-kernel vanishing on p. 233 and target-kernel vanishing on p. 234. The missing
mass affects the identity but cancels in both kernel arguments. Global extensions
parametrize the indicated local components, and equality is tested at common regular values.
See ERRATA F26 and I96. The mass correction appears in
`weilIdentity_unramifiedOutside_meromorphic`, and
`sLocalHomogeneousThetaTransition_preserves_kernel` gives the kernel implication.
-/
def Printed.sLocalIdelicMellin_transition : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S T : Finset (Places(F))) (hST : S ⊆ T)
    (f : Test(F, S)) (c : unramifiedOutside F S)
    (π : (v : Places(F)) → (v.adicCompletion F)ˣ),
    (∀ v ∈ T \ S, (Valued.v :
      Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer (π v).val) →
    let cS := sIdeleRestriction F S c
    let cT := sIdeleRestriction F T ⟨c.val, fun v hv ↦ c.property v (fun h ↦ hv (hST h))⟩
    0 ≤ sLocalIdelicOrderBound (F := F) (S := S) cS →
    0 ≤ sLocalIdelicOrderBound (F := F) (S := T) cT →
    (∀ v ∈ T \ S, finitePlaceRestriction F v c.val (π v) ≠ 1) →
    sLocalIdelicZFunction (F := F) (S := T) (sAdeleSchwartzTransition F hST f) cT =
      sLocalIdelicZFunction (F := F) (S := S) f cS *
        ∏ v ∈ T \ S, (1 - finitePlaceRestriction F v c.val (π v))⁻¹

/-- Paper: Theorem 5.2.3.1, (5.2.3.4), p. 233.
Take F = ℚ(i), S consisting of the complex place, and T adding the place v above 2.
Use the Gaussian z ↦ exp(−2π|z|²), the square of the idelic norm, and the uniformizer 1 + i
at v. The local value of the quasi-character there is 1/4. Summing the valuation shells of
the inserted integer indicator gives the claimed Euler factor times the unit mass 1/2.
The archimedean integral is positive, and the square of the norm is in the convergence region.
-/
theorem Printed.sLocalIdelicMellin_transition_false :
    ¬ Printed.sLocalIdelicMellin_transition := by
  sorry

/-- Paper: Introduction to Proposition 5.2.3.2, (5.2.3.9), pp. 235–236.
As printed: for every number field, every finite stage containing the archimedean places,
and every character of the respective norm-one group, the global and S-local Pettis averages
are projectors. This records the idempotence asserted by the word “projectors.”
The averages and their quotient identifications are given by
`existsUnique_globalThetaIsotypicAverage`, `existsUnique_sLocalThetaIsotypicAverage`,
`globalThetaIsotypicAverage_equiv` and `sLocalThetaIsotypicAverage_equiv`.
`compactActionAverage_idempotent` gives idempotence after normalization. See ERRATA F27.
-/
def Printed.thetaIsotypicAverage_idempotent : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    (∀ ω : PontryaginDual (ideleClassNorm F).ker,
      let P := (existsUnique_globalThetaIsotypicAverage (F := F) ω).exists.choose
      P.comp P = P) ∧
    (∀ χ : PontryaginDual (sIdeleQuotientNorm F S).ker,
      let P := (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) χ).exists.choose
      P.comp P = P)

/-- Paper: Introduction to Proposition 5.2.3.2, (5.2.3.9), pp. 235–236.
Take F = ℚ(i), the trivial character, and, locally, S consisting of the complex place.
The Gaussian z ↦ exp(−2π|z|²) gives a nonzero fixed theta class, with the finite integer
indicator in the global case. Since ℚ(i) has class number one, every global norm-one class
has a representative with complex modulus one and integer units at all finite places.
On fixed vectors the averages act by π/4 globally and π/2 locally, so applying either twice
multiplies the class by the square of that mass.
-/
theorem Printed.thetaIsotypicAverage_idempotent_false :
    ¬ Printed.thetaIsotypicAverage_idempotent := by
  sorry

/-- Paper: Remark 5.2.3.4(1)–(2), p. 237.
As printed: for every number field and finite stage containing the archimedean places,
the topologies on global and S-local test functions induced by the theta maps are Hausdorff.
This records the Hausdorff assertions in the two closure statements.
`globalThetaKernel_eq_induced_closure` and `sLocalThetaKernel_eq_induced_closure`
give the closure identities with the indicated pullback topologies. See ERRATA F28.
-/
def Printed.thetaInducedTopology_t2 : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    let q := (LinearMap.ker (adelicThetaLinearMap F)).mkQ
    let qS := (LinearMap.ker (sLocalAdelicTheta F S)).mkQ
    @T2Space (GlobalTest(F)) (TopologicalSpace.induced q inferInstance) ∧
    @T2Space (Test(F, S)) (TopologicalSpace.induced qS inferInstance)

/-- Paper: Remark 5.2.3.4(1)–(2), p. 237.
For F = ℚ use the odd real test x ↦ x exp(−πx²), at S consisting of the real place
and globally tensored with the indicator of the finite integer adeles. Each test is nonzero,
and the terms at opposite nonzero rational elements cancel at every global idele.
The real-stage sum pairs the terms at the two units ±1. Each theta map sends its test
and zero to the same point, so the pullback topology cannot separate them.
-/
theorem Printed.thetaInducedTopology_t2_false : ¬ Printed.thetaInducedTopology_t2 := by
  sorry

/-- Paper: §5.2.4, introduction to Theorem 5.2.4.1, p. 238.
The introduction says that the local Fourier maps tend to “the inversion automorphism”
on the global theta space. We record the existence of the named target automorphism.
Deviation: We read inversion as pullback of theta functions by `g ↦ g⁻¹` on idele classes.
`existsUnique_globalThetaFourier` gives the Fourier automorphism, whose action on theta values
is governed by `adelicTheta_riemannRoch`. See ERRATA F29.
-/
def Printed.globalTheta_inversionAutomorphism : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    let K := LinearMap.ker (adelicThetaLinearMap F)
    let theta := K.liftQ (adelicThetaLinearMap F) le_rfl
    ∃ J : GlobalAdelicThetaSpace F ≃L[ℂ] GlobalAdelicThetaSpace F,
      ∀ (f : GlobalTest(F)) (g : IdeleClassGroup (𝓞 F) F),
        theta (J (K.mkQ f)) g = adelicTheta f g⁻¹

/-- Paper: §5.2.4, introduction to Theorem 5.2.4.1, p. 238.
Take F = ℚ and the self-dual test exp(−πx²) times the indicator of the finite integer adeles.
On the idele with real component t > 0 and finite components 1, its inverted theta value
is asymptotic to t as t tends to infinity. Every global theta function decays there by
`adelicTheta_decay_large`, so the inverted function cannot represent a global theta class.
-/
theorem Printed.globalTheta_inversionAutomorphism_false :
    ¬ Printed.globalTheta_inversionAutomorphism := by
  sorry

/-- Paper: Theorem 5.2.4.1(1)–(2), (5.2.4.2) and (5.2.4.4), p. 239.
As printed: for every number field and every pair of nested finite stages containing the
archimedean places, Fourier on the theta quotients commutes with stage enlargement and
with insertion into the global theta quotient. This records the two insertion assertions.
See ERRATA F30. The repaired statements are `sLocalThetaFourier_transition` and
`sLocalThetaFourier_toGlobal`, with restrictions at places dividing the different.
-/
def Printed.thetaFourier_insertion : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    let fourierS := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    let fourier := (existsUnique_globalThetaFourier (F := F)).exists.choose
    (∀ (T : Finset (Places(F))) (hST : S ⊆ T) (x : SLocalAdelicThetaSpace F S),
      let fourierT := (existsUnique_sLocalThetaFourier (F := F) (S := T)).exists.choose
      let transition := sLocalThetaTransition (F := F) hST
      fourierT (transition x) = transition (fourierS x)) ∧
    (∀ x : SLocalAdelicThetaSpace F S,
      fourier (sLocalThetaToGlobal F S x) = sLocalThetaToGlobal F S (fourierS x))

/-- Paper: Theorem 5.2.4.1(1)–(2), (5.2.4.2) and (5.2.4.4), p. 239.
For F = ℚ(i), let S consist of the complex place and T add the place v above 2.
Choose the archimedean Fourier image to be a smooth bump equal to 1 at 1/2, with support
meeting (1/2)ℤ[i] only at 1/2. Fourier after insertion replaces the integer indicator at v
by half the indicator of (1/2)O_v, so the theta value at the identity is 1/2, from the
single term at 1/2. Insertion after Fourier uses the integer indicator and gives zero.
The same values hold after passage to the global theta space.
-/
theorem Printed.thetaFourier_insertion_false : ¬ Printed.thetaFourier_insertion := by
  sorry

/-- Paper: Theorem 5.2.4.1(1)–(2), p. 239.
As printed: for every number field, every finite stage containing the archimedean places,
and every continuous global norm-one character, the descended local character used in the
isotype assertions exists. This records the existence required by the printed scope.
The descent criterion is `normOneCharacterUnramifiedOutside_iff`, and
`sLocalThetaFourier_mem_isotype` states exchange for local characters. See ERRATA F31.
-/
def Printed.exists_sLocalNormOneCharacter : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F)))
    (ω : PontryaginDual (ideleClassNorm F).ker),
    ∃ χ : PontryaginDual (sIdeleQuotientNorm F S).ker,
      ∀ (u : (integralAdelesOutside F S)ˣ) (x : (ideleClassNorm F).ker)
        (y : (sIdeleQuotientNorm F S).ker),
        let g := integralIdeleInsertion F S u
        x.val = QuotientGroup.mk g →
        y.val = QuotientGroup.mk (Units.map (adeleProjection F S).toMonoidHom g) →
        χ y = ω x

/-- Paper: Theorem 5.2.4.1(1)–(2), p. 239.
Take F = ℚ, S consisting of the real place, and the quadratic character modulo 3.
The idele with component −1 at 3 and 1 everywhere else is a unit outside S and has norm
one. Its S-projection is the identity, while the global character takes value −1 there.
-/
theorem Printed.exists_sLocalNormOneCharacter_false :
    ¬ Printed.exists_sLocalNormOneCharacter := by
  sorry

end RiemannMasullo
