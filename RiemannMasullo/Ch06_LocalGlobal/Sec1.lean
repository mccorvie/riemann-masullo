module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2
public import RiemannMasullo.AppA_AlgebraicNT.Sec3
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Structure Theorem IV: local within global

Masullo, §6.1, pp. 287–295. The finite sets index finite places. The
archimedean places are included in every S-adelic ring.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped CompactlySupported MonoidAlgebra NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S T : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Places" => HeightOneSpectrum (𝓞 F)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "Θ𝔽" => GlobalAdelicThetaSpace F
local notation "Θₛ(" S ")" => SLocalAdelicThetaSpace F S
local notation "L(" w ")" => (HeightOneSpectrum.adicCompletion (R := 𝓞 F) F w)
local notation "ℬᵥ(" w ")" => (SchwartzBruhat (Multiplicative (L(w))))
local notation "O(" w ")" => (HeightOneSpectrum.adicCompletionIntegers (R := 𝓞 F) F w)
local notation "U(" w ")" =>
  (Submonoid.units (Subsemiring.toSubmonoid (Subring.toSubsemiring (ValuationSubring.toSubring (O(w))))))

-- TODO(paper-gap): Proposition 6.1.1.1, (6.1.1.1)–(6.1.1.2), multiplies
-- inverses of test-space endomorphisms to obtain transitions between distinct
-- quotients. On the target coinvariants every basis lift acts as the identity,
-- so the differences have no inverse. Already over ℚ, with S = {∞} and
-- S' = {∞, p}, the proposed geometric series does not converge in the target
-- quotient on a nonzero transition class. The global series has the same defect.

section Ranges

variable (F S) in
/-- Paper: (6.1.2.2), p. 288.
The complementary integral ideles are the ideles integral and invertible outside S
whose S-adelic projection is the identity.
Deviation: In (6.1.2.2) the ambient outside multiplicative factors form a restricted
product. The full product of integer units embeds in the ideles. -/
def outsideIntegralIdeleUnits : Subgroup (IdeleGroup (𝓞 F) F) :=
  (integralIdeleInsertion F S).range ⊓ (Units.map (adeleProjection F S).toMonoidHom).ker

/-- Paper: (6.1.2.2), p. 288.
An idele belongs to the complementary group exactly when its archimedean and S coordinates
are one and its other coordinates are local integer units. -/
theorem mem_outsideIntegralIdeleUnits_iff (g : IdeleGroup (𝓞 F) F) :
    g ∈ outsideIntegralIdeleUnits F S ↔
      g.val.1 = 1 ∧ (∀ w ∈ S, g.val.2 w = 1) ∧
        ∀ w ∉ S, g.val.2 w ∈ O(w) ∧ (g⁻¹).val.2 w ∈ O(w) := by sorry

variable (F S T) in
/-- Paper: (6.1.2.1), p. 288.
Projecting the complementary integral ideles to T inserts the integer units at T minus S.
Deviation: The insertion lands in the T-ideles, as required by Theorem 6.1.2.1(1). -/
def relativeIntegralIdeleUnits : Subgroup (SAdeleRing F T)ˣ :=
  (outsideIntegralIdeleUnits F S).map (Units.map (adeleProjection F T).toMonoidHom)

/-- Paper: (6.1.2.1), p. 288.
The relative group has identity coordinates on the archimedean factor and S, and
arbitrary integer-unit coordinates on T minus S. -/
theorem mem_relativeIntegralIdeleUnits_iff (g : (SAdeleRing F T)ˣ) :
    g ∈ relativeIntegralIdeleUnits F S T ↔
      g.val.1 = 1 ∧ (∀ w : T, w.val ∈ S → g.val.2 w = 1) ∧
        ∀ w : T, w.val ∉ S → g.val.2 w ∈ O(w.val) ∧ (g⁻¹).val.2 w ∈ O(w.val) := by sorry

/-- Paper: (6.1.2.2), p. 288.
The group of integral idelic units outside S is compact in the global ideles. -/
theorem outsideIntegralIdeleUnits_isCompact :
    IsCompact (outsideIntegralIdeleUnits F S : Set (IdeleGroup (𝓞 F) F)) := by sorry

/-- Paper: (6.1.2.1), p. 288.
The group of integer units inserted at the additional finite places is compact in the T-ideles. -/
theorem relativeIntegralIdeleUnits_isCompact :
    IsCompact (relativeIntegralIdeleUnits F S T : Set (SAdeleRing F T)ˣ) := by sorry

-- TODO(paper-gap): The proof of Theorem 6.1.2.1 applies its invariant-space
-- tensor identification to the full test space and has mismatched indices
-- in (6.1.2.21). The argument on pp. 294–295 assumes convergent Cauchy nets
-- have bounded tails in the strict LF topology. Equation (5.1.1.3) defines the
-- two theta spaces as quotients by the theta kernels. Remark 5.2.3.4 concerns
-- the separate comparison with closures of principal translation differences.

/-- Paper: Theorem 6.1.2.1(1), p. 288.
When the S-integers have trivial Picard group, the range of the transition is the fixed
subspace for the relative integral units in the T-local theta quotient of (5.1.1.3). -/
theorem sLocalThetaTransition_range_eq_invariants (hST : S ⊂ T)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F))) :
    let ρ := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose
    Set.range (sLocalThetaTransition (F := F) hST.le) =
      {x : Θₛ(T) | ∀ g : relativeIntegralIdeleUnits F S T,
        ρ (QuotientGroup.mk g.val) x = x} := by sorry

/-- Paper: Theorem 6.1.2.1(2), p. 288.
When the S-integers have trivial Picard group, the range of the global insertion is the fixed
subspace for the complementary integral units in the global theta quotient of (5.1.1.3). -/
theorem sLocalThetaToGlobal_range_eq_invariants
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F))) :
    let ρ := (existsUnique_globalThetaAction (F := F)).exists.choose
    Set.range (sLocalThetaToGlobal F S) =
      {x : Θ𝔽 | ∀ g : outsideIntegralIdeleUnits F S, ρ (QuotientGroup.mk g.val) x = x} := by sorry

end Ranges

section UnitRepresentation

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

local notation "translate" => fun (g : Rˣ) ↦
  ((LinearMap.funLeft ℂ ℂ (fun x : Multiplicative R ↦
    Multiplicative.ofAdd ((g⁻¹ : Rˣ).val * x.toAdd))).comp
    (schwartzBruhatSubmodule (Multiplicative R)).subtype).codRestrict
      (schwartzBruhatSubmodule (Multiplicative R)) (schwartzBruhat_unitTranslate_mem g)

/-- Paper: Remark 6.1.2.3, p. 289.
The identity unit acts by the identity on the additive Schwartz–Bruhat space. -/
theorem schwartzBruhatUnitRepresentation_map_one :
    translate (1 : Rˣ) = (1 : Module.End ℂ ℬ(R)) := by sorry

/-- Paper: Remark 6.1.2.3, p. 289.
Pullback by the inverse of a product agrees with the composition of the two translations. -/
theorem schwartzBruhatUnitRepresentation_map_mul (g h : Rˣ) :
    translate (g * h) = (translate g : Module.End ℂ ℬ(R)) * translate h := by sorry

/-- Paper: Remark 6.1.2.3, p. 289.
The inverse-multiplication pullback action on additive Schwartz–Bruhat functions,
bundled as a complex linear representation of the unit group. -/
def schwartzBruhatUnitRepresentation : Representation ℂ Rˣ ℬ(R) where
  toFun := translate
  map_one' := schwartzBruhatUnitRepresentation_map_one
  map_mul' := schwartzBruhatUnitRepresentation_map_mul

/-- Paper: Remark 6.1.2.3, p. 289.
The bundled representation acts by the existing left-translation operator. -/
theorem schwartzBruhatUnitRepresentation_apply (g : Rˣ) (f : ℬ(R)) :
    schwartzBruhatUnitRepresentation (R := R) g f = schwartzBruhatUnitTranslate g f := by sorry

end UnitRepresentation

local notation "ρ(" w ")" =>
  (schwartzBruhatUnitRepresentation (R := L(w))).comp
    (Subgroup.subtype (U(w)))

section Laurent

open Classical in
/-- Paper: Lemma 6.1.2.2(1), p. 288.
The monomial of exponent n corresponds to the indicator of the integral ball
scaled by the n-th power of the uniformizer. -/
def finitePlaceBallIndicator (w : Places) (π : (L(w))ˣ) (n : ℤ)
    (x : L(w)) : ℂ :=
  (O(w) : Set L(w)).indicator (fun _ ↦ (1 : ℂ)) ((π ^ (-n)).val * x)

/-- Paper: Lemma 6.1.2.2(1), p. 288.
The translated ball contains the m-th uniformizer power exactly when m is at least its
defining exponent n. -/
theorem finitePlaceBallIndicator_at_power (w : Places) (π : (L(w))ˣ)
    (_hπ : Valuation.IsUniformizer
      (Valued.v : Valuation (L(w)) (WithZero (Multiplicative ℤ))) π.val)
    (m n : ℤ) :
    finitePlaceBallIndicator w π n (π ^ m).val = (if n ≤ m then 1 else 0) := by sorry

/-- Paper: Lemma 6.1.2.2(1)(1), p. 288.
The integer-unit invariants form a free Laurent module on the integer-ball indicator.
Deviation: A complex linear equivalence spells out the Laurent action by the generator
and the image of the free generator, without installing an extra module instance. -/
theorem finitePlaceSchwartz_invariants_laurent_free (w : Places)
    (π : (L(w))ˣ)
    (_hπ : Valuation.IsUniformizer
      (Valued.v : Valuation (L(w)) (WithZero (Multiplicative ℤ))) π.val) :
    ∃ e : LaurentPolynomial ℂ ≃ₗ[ℂ] (Representation.invariants (ρ(w))),
      (∀ x, (e 1).val (Multiplicative.ofAdd x) = finitePlaceBallIndicator w π 0 x) ∧
      ∀ P, (e (LaurentPolynomial.T 1 * P)).val =
        schwartzBruhatUnitTranslate π (e P).val := by sorry

/-- Paper: Lemma 6.1.2.2(1)(2), p. 288.
The integer-unit invariants are closed in the local Schwartz–Bruhat space. -/
theorem finitePlaceSchwartz_invariants_isClosed (w : Places) :
    IsClosed (SetLike.coe (Representation.invariants (V := ℬᵥ(w)) (ρ(w))) : Set ℬᵥ(w)) := by sorry

/-- Paper: Lemma 6.1.2.2(1)(2), p. 288.
With the finest locally convex topology on Laurent polynomials, the monomial-to-ball
correspondence is a linear homeomorphism onto the unit invariants. -/
theorem finitePlaceSchwartz_invariants_laurent_equiv (w : Places)
    (π : (L(w))ˣ)
    (_hπ : Valuation.IsUniformizer
      (Valued.v : Valuation (L(w)) (WithZero (Multiplicative ℤ))) π.val) :
    ∃ e : FinestLocallyConvex (LaurentPolynomial ℂ) ≃L[ℂ] (Representation.invariants (ρ(w))),
      ∀ n x, (e (LaurentPolynomial.T n)).val (Multiplicative.ofAdd x) =
        finitePlaceBallIndicator w π n x := by sorry

end Laurent

section RelativeLaurent

-- TODO(paper-gap): Lemma 6.1.2.2(2), (6.1.2.5), specifies the projective
-- topology, but §2.1.4.2 uses the inductive topology on this algebraic tensor.
-- For ℚ with one new prime the invariant space is a locally convex direct sum
-- of copies of the real Schwartz space. The canonical tensor pairing into
-- this sum is separately continuous and is not jointly continuous.
-- TODO(paper-gap): After (6.1.2.9) the kernel is the image of the outside unit
-- group itself. Its intersection with the principal ideles is trivial by the
-- archimedean coordinate. The extra quotient by the S-units is unjustified.
-- TODO(paper-gap): The restriction used on p. 291 need not be compactly
-- supported on the multiplicative group, as the restriction of 1_{ℤₚ} shows.

open Classical in
/-- Paper: Lemma 6.1.2.2(2), (6.1.2.5)–(6.1.2.6), p. 289.
The larger-stage relative unit invariants have a unique linear topological identification
with the S-local test space tensored with the multivariate Laurent polynomials.
Each pure tensor with a monomial multiplies the old test function by the indicated local balls.
Deviation: The tensor topology is inductive, following Corollary 2.1.4.2 as formalized. -/
theorem sLocalSchwartz_invariants_laurent_equiv (hST : S ⊂ T)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F)))
    (π : ∀ w : ↥(T \ S), (L(w.val))ˣ)
    (_hπ : ∀ w : ↥(T \ S), Valuation.IsUniformizer
      (Valued.v : Valuation (L(w.val)) (WithZero (Multiplicative ℤ))) (π w).val) :
    ∃! e : InductiveTensor ℬ(SAdeleRing F S)
        (FinestLocallyConvex (AddMonoidAlgebra ℂ (↥(T \ S) → ℤ))) ≃L[ℂ]
        (Representation.invariants <| (schwartzBruhatUnitRepresentation (R := SAdeleRing F T)).comp
          (relativeIntegralIdeleUnits F S T).subtype),
      ∀ (f : ℬ(SAdeleRing F S)) (a : ↥(T \ S) → ℤ) (x : SAdeleRing F T),
        (e (f ⊗ₜ[ℂ] AddMonoidAlgebra.single a 1)).val (Multiplicative.ofAdd x) =
          f (Multiplicative.ofAdd (x.1, fun w : S ↦ x.2 ⟨w.val, hST.le w.property⟩)) *
            ∏ w : ↥(T \ S), finitePlaceBallIndicator w.val (π w) (a w)
              (x.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩) := by sorry

end RelativeLaurent

section Averaging

-- These Borel structures agree with the local instances in Appendix A.3.
local instance instLocalUnitMeasurableSpaceCh06Sec1 (w : Places) :
    MeasurableSpace (L(w))ˣ := borel _

local notation "μ(" w ")" => finiteLocalMultiplicativeTamagawaMeasure F w

/-- Paper: Lemma 6.1.2.4(1), p. 291.
The span of integer-unit translation differences is closed.
Consequently the algebraic and continuous coinvariant quotients use the same relations.
Deviation: The closure equality states both conclusions on the relation submodule. -/
theorem finitePlaceSchwartz_unitRelations_closure_eq (w : Places) :
    (Representation.Coinvariants.ker (ρ(w))).topologicalClosure =
      Representation.Coinvariants.ker (ρ(w)) := by sorry

/-- Paper: (6.1.2.14), p. 292.
Averaging a local test function evaluates it along the multiplicative orbit and integrates
over the integer units against the local multiplicative Tamagawa measure. -/
def finitePlaceUnitAverage (w : Places) (f : ℬᵥ(w)) (x : L(w)) : ℂ :=
  ∫ u : (L(w))ˣ, f (Multiplicative.ofAdd (x * u.val)) ∂((μ(w)).restrict (U(w)))

/-- Paper: (6.1.2.14), p. 292.
The orbit integral at zero is the value at zero times the Tamagawa mass of the integer units. -/
theorem finitePlaceUnitAverage_zero (w : Places) (f : ℬᵥ(w)) :
    finitePlaceUnitAverage w f 0 =
      ((μ(w) (U(w) : Set (L(w))ˣ)).toReal : ℂ) *
        f (Multiplicative.ofAdd 0) := by sorry

/-- Paper: (6.1.2.14), p. 292.
Each integrand of the local averaging formula is integrable on the integer units. -/
theorem finitePlaceUnitAverage_integrable (w : Places) (f : ℬᵥ(w)) (x : L(w)) :
    IntegrableOn (fun u : (L(w))ˣ ↦ f (Multiplicative.ofAdd (x * u.val)))
      (U(w) : Set (L(w))ˣ) (μ(w)) := by sorry

/-- Paper: Lemma 6.1.2.4(2), (6.1.2.13)–(6.1.2.14), p. 292.
Local unit averaging defines a linear map to compactly supported continuous functions
which is continuous for their uniform norm. -/
theorem finitePlaceUnitAverage_continuous_uniform (w : Places) :
    ∃ A : ℬᵥ(w) →ₗ[ℂ] C_c(L(w), ℂ),
      (∀ f x, A f x = finitePlaceUnitAverage w f x) ∧
        Continuous (fun f ↦ (A f).toBoundedContinuousFunction) := by sorry

/-- Paper: Lemma 6.1.2.4(2), p. 292.
Local unit averaging also defines a continuous linear map in the intrinsic
Schwartz–Bruhat topology. -/
theorem finitePlaceUnitAverage_continuous_schwartzBruhat (w : Places) :
    ∃ A : ℬᵥ(w) →L[ℂ] ℬᵥ(w),
      ∀ f x, A f (Multiplicative.ofAdd x) = finitePlaceUnitAverage w f x := by sorry

/-- Paper: Lemma 6.1.2.4(2), p. 292.
A test function averages to zero exactly when it belongs to the span of unit
translation differences. -/
theorem finitePlaceUnitAverage_eq_zero_iff (w : Places) (f : ℬᵥ(w)) :
    (∀ x, finitePlaceUnitAverage w f x = 0) ↔
      f ∈ Representation.Coinvariants.ker (ρ(w)) := by sorry

-- TODO(paper-gap): The proof on p. 292 identifies multiplicative unit averaging
-- with additive convolution and deduces vanishing of the function from unramified
-- Mellin values. For the indicator of the integer ring at the trivial character,
-- the shell integrals in (6.1.2.17) all have the same positive mass. A nonzero
-- eigendistribution annihilates every unit difference only for unramified weight.
-- The kernel assertion follows by averaging the finite unit orbit of each test function.

/-- Paper: Lemma 6.1.2.4(2), (6.1.2.15), p. 292.
Multiplicative unit averaging induces a linear homeomorphism from the algebraic
coinvariants with their quotient topology to the integer-unit invariants. -/
theorem finitePlaceUnitAverage_coinvariants_equiv (w : Places) :
    ∃ N : (ℬᵥ(w) ⧸ Representation.Coinvariants.ker (ρ(w))) ≃L[ℂ] (Representation.invariants (ρ(w))),
      ∀ (f : ℬᵥ(w)) x, (N (Submodule.Quotient.mk f)).val (Multiplicative.ofAdd x) =
        finitePlaceUnitAverage w f x := by sorry

local notation "K(" D ")" => FinitePlaceProduct F D
local notation "KUnits(" D ")" =>
  (Subgroup.pi Set.univ (fun w : D ↦ U(w.val))).comap
    (MulEquiv.piUnits (M := fun w : D ↦ L(w.val))).toMonoidHom
local notation "ρΠ(" D ")" =>
  (schwartzBruhatUnitRepresentation (R := K(D))).comp (KUnits(D)).subtype

/-- Paper: Lemma 6.1.2.4(3), p. 292.
The product of the local averages integrates the test function along its orbit
against the product of the restricted local multiplicative Tamagawa measures. -/
def finiteProductUnitAverage (D : Finset Places) (f : ℬ(K(D))) (x : K(D)) : ℂ :=
  ∫ u : ∀ v : D, (L(v.val))ˣ,
    f (Multiplicative.ofAdd (fun v ↦ x v * (u v).val))
    ∂(Measure.pi fun v : D ↦ (μ(v.val)).restrict (U(v.val)))

/-- Paper: Lemma 6.1.2.4(3), p. 292.
At the zero tuple, product averaging multiplies the value there by the product
of the local integer-unit masses. -/
theorem finiteProductUnitAverage_zero (D : Finset Places) (f : ℬ(K(D))) :
    finiteProductUnitAverage D f 0 =
      (∏ w : D, ((μ(w.val) (U(w.val) : Set (L(w.val))ˣ)).toReal : ℂ)) *
        f (Multiplicative.ofAdd 0) := by sorry

/-- Paper: Lemma 6.1.2.4(3), p. 292.
The product orbit integral is integrable against the finite product of the restricted measures. -/
theorem finiteProductUnitAverage_integrable (D : Finset Places) (f : ℬ(K(D))) (x : K(D)) :
    Integrable
      (fun u : ∀ v : D, (L(v.val))ˣ ↦
        f (Multiplicative.ofAdd (fun v ↦ x v * (u v).val)))
      (Measure.pi fun v : D ↦ (μ(v.val)).restrict (U(v.val))) := by sorry

/-- Paper: Lemma 6.1.2.4(3), p. 292.
The integer-unit invariants are closed in the Schwartz–Bruhat space on the finite product.
Deviation: The place set is written directly as the finite set of additional places. -/
theorem finiteProductSchwartz_unitInvariants_isClosed (D : Finset Places) (_hD : D.Nonempty) :
    IsClosed ((Representation.invariants (ρΠ(D))) : Set ℬ(K(D))) := by sorry

/-- Paper: Lemma 6.1.2.4(3), (6.1.2.16), p. 292.
The product of the local unit averages induces a linear homeomorphism from
coinvariants with their quotient topology to invariants on the finite product.
Deviation: The place set is written directly as the finite set of additional places. -/
theorem finiteProductUnitAverage_coinvariants_equiv (D : Finset Places) (_hD : D.Nonempty) :
    ∃ N : (ℬ(K(D)) ⧸ Representation.Coinvariants.ker (ρΠ(D))) ≃L[ℂ] (Representation.invariants (ρΠ(D))),
      ∀ (f : ℬ(K(D))) x, (N (Submodule.Quotient.mk f)).val (Multiplicative.ofAdd x) =
        finiteProductUnitAverage D f x := by sorry

end Averaging

end RiemannMasullo
