module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec2

/-! # §7.2 Claims that are false as printed -/

@[expose] public noncomputable section

open Filter IsDedekindDomain NumberField Set Topology
open scoped BigOperators NNReal NumberField.AdeleRing

namespace RiemannMasullo
namespace Printed

set_option quotPrecheck false

universe u

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Jₛ(" F ", " S ")" => SIdeleQuotient F S
local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "Xₛ(" F ", " S ")" => QuasiCharacter (Jₛ(F, S))
local notation "ℬₛ(" F ", " S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "ℬ𝔽(" F ")" => SchwartzBruhat (Multiplicative (𝔸[F]))
local notation "mₛ(" F ", " S ")" => sIdeleQuotientNorm F S
local notation "m𝔽(" F ")" => ideleClassNorm F
local notation "J₁(" F ", " S ")" => (mₛ(F, S)).ker
local notation "hmₛ(" F ", " S ")" => (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "twistₛ(" F ", " S ")" =>
  quasiCharacterNormTwist (G := Jₛ(F, S)) mₛ(F, S) hmₛ(F, S)
local notation "dualₛ(" F ", " S ")" => dualQuasiCharacter (G := Jₛ(F, S)) mₛ(F, S) hmₛ(F, S)
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "onComponent(" F ", " S ", " c ", " ω ")" =>
  (normOneRestriction mₛ(F, S) c = (circleToComplex).comp ω)
local notation "Θₛ(" F ", " S ", " ω ")" => SLocalHomogeneousThetaSpace F S ω
local notation "Kₛ(" F ", " S ", " ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)
local notation "K𝔽(" F ", " ω ")" => LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)
local notation "poleLocus(" F ", " S ")" => ({c : Xₛ(F, S) | 0 < sLocalRhoPoleOrder c})
local notation "globalUnitary(" F ", " χ ")" => ((circleToComplex).comp χ : QuasiCharacter (C𝔽(F)))
local notation "globalNormOne(" F ", " χ ")" =>
  ((χ).comp (⟨(m𝔽(F)).ker.subtype, continuous_subtype_val⟩ : (m𝔽(F)).ker →ₜ* C𝔽(F))
    : PontryaginDual (m𝔽(F)).ker)
local notation "localChart(" F ", " S ", " χ ", " h ")" =>
  twistₛ(F, S) (sIdeleRestriction F S ⟨globalUnitary(F, χ), h⟩)
local notation "outsideS(" h₀ ", " hχ ")" => (fun v hv ↦ hχ v (fun hv₀ ↦ hv (h₀ hv₀)))

/-- Paper: Definition 7.1.2.1, p. 316, and Theorem 7.2.1.1(1), p. 334.
The literal nonnegative subscript in §7.1 denotes the coefficient of the positive
power, including the constant at index zero. -/
def sLocalNonnegativeLaurentCoeff {F : Type u} [Field F] [NumberField F] {S : Finset Places(F)}
    (c : Xₛ(F, S)) (k : ℕ) : StrongDual ℂ ℬₛ(F, S) :=
  let a := fun f : ℬₛ(F, S) ↦ sLocalZLaurentCoeff f c (k : ℤ)
  let h := sLocalZLaurentCoeff_continuous_linear c (k : ℤ)
  ⟨h.2.mk' a, h.1⟩

/-- Paper: Equation (7.2.1.8), p. 334.
Every closed rectifiable contour bounding the indicated domain gives the coefficient.
Rectifiable contours are integrated in Lipschitz parametrizations, available by
arclength reparametrization. Both directions of traversal are allowed. -/
def sLocalPrincipalPartCoeff_any_contour : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (c : Xₛ(F, S)),
    c ∈ poleLocus(F, S) → ∀ (k : ℕ) (f : ℬₛ(F, S)) (γ : ℝ → ℂ),
    (∃ K : ℝ≥0, LipschitzOnWith K γ (Icc 0 1)) → γ 0 = γ 1 →
    let bounds := fun D : Set ℂ ↦ IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧
      frontier D = γ '' Icc 0 1
    ∀ D : Set ℂ, bounds D → (∀ U, bounds U → U = D) → 0 ∈ D →
      let integrand := fun t : ℝ ↦ (γ t) ^ ((k : ℤ) - 1) *
        sLocalIdelicZFunction f (twistₛ(F, S) c (γ t)) * deriv γ t
      IntervalIntegrable integrand MeasureTheory.volume 0 1 ∧
        sLocalNonnegativeLaurentCoeff c k f = (∫ t in (0 : ℝ)..1, integrand t) / (2 * (Real.pi : ℂ) * Complex.I)

/-- Paper: Equation (7.2.1.8), p. 334.
Over ℚ with only the real place, a nonnegative nonzero even bump on 2 < |x| < 3
has positive first Mellin derivative at zero and zero integral in the formula for
index one on a small circle. Independently of the subscript convention, at index
zero the Gaussian on the positive circle of center −1 and radius 3/2 picks up the
additional residue π of Γℝ(z)/z at −2. -/
theorem sLocalPrincipalPartCoeff_any_contour_false :
    ¬ sLocalPrincipalPartCoeff_any_contour := by sorry

/-- Paper: Theorem 7.2.1.1(2), p. 334.
Each coefficient descends to the homogeneous theta quotient and is an
eigendistribution of weight equal to its center. -/
def sLocalPrincipalPartCoeff_eigendistribution : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (ω : PontryaginDual J₁(F, S)) (c : Xₛ(F, S)), onComponent(F, S, c, ω) → ∀ k : ℕ,
    LinearMap.ker (sLocalAdelicTheta F S) ≤ (sLocalNonnegativeLaurentCoeff c k).ker ∧
      Kₛ(F, S, ω) ≤ (sLocalNonnegativeLaurentCoeff c k).ker ∧
      sLocalNonnegativeLaurentCoeff c k ∈ sLocalEigendistributions c

/-- Paper: Theorem 7.2.1.1(2), p. 334.
For ℚ at the real place, translate a nonzero nonnegative even bump supported in
2 < |x| < 3 by dilation by 2. At the trivial center its first Mellin derivative
increases by log(2) times the positive constant coefficient. With the polar
reading of (7.2.1.8), use the Gaussian times the integer indicator over ℚ at
∞ and p. The top coefficient is 2/log p, so translation by p changes the
residue by −2 at the trivial character. -/
theorem sLocalPrincipalPartCoeff_eigendistribution_false :
    ¬ sLocalPrincipalPartCoeff_eigendistribution := by sorry

/-- Paper: Theorem 7.2.1.1(3), p. 334.
A nonzero coefficient functional forces the corresponding pole-order bound on every test. -/
def sLocalPrincipalPartCoeff_universal_pole_bound : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (c : Xₛ(F, S)) (k : ℕ),
    sLocalNonnegativeLaurentCoeff c k ≠ 0 →
      c ∈ poleLocus(F, S) ∧ ∀ f : ℬₛ(F, S), k ≤ sLocalPolarMultiplicity f c

/-- Paper: Theorem 7.2.1.1(3), p. 334.
At the trivial character over ℚ with only the real place, an even nonnegative
nonzero bump on 2 < |x| < 3 has positive first Mellin derivative and no pole. -/
theorem sLocalPrincipalPartCoeff_universal_pole_bound_false :
    ¬ sLocalPrincipalPartCoeff_universal_pole_bound := by sorry

/-- Paper: Theorem 7.2.1.1(4), p. 334.
For every supported pole bound, its annihilator is generated in the strong dual
by the above-bound coefficients, asserted to be eigendistributions of their centers.
Deviation: The bound is extended by zero off its support in the allowed pole locus. -/
def sLocalThetaPoleBound_eigen_annihilator : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (ω : PontryaginDual J₁(F, S))
    (U : Set Xₛ(F, S)) (_hU : U ⊆ poleLocus(F, S)) (m : Xₛ(F, S) → ℕ) (_hm : ∀ c ∉ U, m c = 0),
    IsClosed (sLocalThetaPoleBound ω m : Set (Θₛ(F, S, ω))) ∧
    (sLocalThetaPoleBound ω m).dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ) =
      (Submodule.span ℂ {T : StrongDual ℂ (Θₛ(F, S, ω)) |
        ∃ (c : Xₛ(F, S)) (_hc : onComponent(F, S, c, ω)) (k : ℕ),
          c ∈ poleLocus(F, S) ∧ m c < k ∧
            ∀ f : ℬₛ(F, S), T ((Kₛ(F, S, ω)).mkQ f) = sLocalNonnegativeLaurentCoeff c k f
      }).topologicalClosure ∧
    (∀ (c : Xₛ(F, S)), onComponent(F, S, c, ω) → c ∈ poleLocus(F, S) → ∀ k : ℕ, m c < k →
      sLocalNonnegativeLaurentCoeff c k ∈ sLocalEigendistributions c)

/-- Paper: Theorem 7.2.1.1(4), p. 334.
For the zero bound over ℚ at the real place, the first positive coefficient
is among the asserted eigendistributions. On a positive even bump supported in
2 < |x| < 3, dilation by 2 changes it by log(2) times the nonzero constant term. -/
theorem sLocalThetaPoleBound_eigen_annihilator_false :
    ¬ sLocalThetaPoleBound_eigen_annihilator := by sorry

/-- Paper: Remark 7.2.1.2, p. 335, first sequence.
The coefficient map on tests descends to the indicated quotient, has the printed
kernel, and maps onto the printed product. The index set in the display ranges
over the selected divisor on the character space. -/
def sLocalThetaPoleBound_low_coefficients_exact : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (ω : PontryaginDual J₁(F, S))
    (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places(F)) (_h₀ : S₀ ⊆ S),
    let n := sLocalSelectedPoleMultiplicity SArch S₀ (F := F) (S := S)
    let I := {i : Xₛ(F, S) × ℕ // 0 < i.2 ∧ i.2 ≤ n i.1}
    ∃ A : Θₛ(F, S, ω) →ₗ[ℂ] (I → ℂ), A.ker = sLocalThetaPoleBound ω n ∧
      Function.Surjective A ∧ ∀ (f : ℬₛ(F, S)) (i : I),
        A ((Kₛ(F, S, ω)).mkQ f) i = sLocalNonnegativeLaurentCoeff i.val.1 i.val.2 f

/-- Paper: Remark 7.2.1.2, p. 335.
Over ℚ with the real place and p, select p. The product of a nonzero nonnegative
even bump supported on 2 < |x| < 3 with the indicator of integer units has entire
trivial-component transform and positive first Taylor coefficient at zero.
Under the polar reading, use a real bump equal to one near zero instead.
Its simple pole there is allowed by the selected bound and has nonzero residue. -/
theorem sLocalThetaPoleBound_low_coefficients_exact_false :
    ¬ sLocalThetaPoleBound_low_coefficients_exact := by sorry

open Classical in
/-- Paper: Remark 7.2.1.2, p. 335, second sequence.
The printed sequence of global sections is identified with the first sequence
by Mellin and the indicated principal-part coordinates. On the character surface
a divisor of multiplicity b has b Laurent coordinates in its principal-parts
stalk. Sections of that principal-parts sheaf are their product over the
discrete support. The Mellin transform of an isotype is supported on its component. -/
def sLocalThetaPoleBound_printed_mellin_sequence : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (ω : PontryaginDual J₁(F, S))
    (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places(F)) (_h₀ : S₀ ⊆ S),
    let m := sLocalRhoPoleOrder (F := F) (S := S)
    let n := sLocalSelectedPoleMultiplicity SArch S₀ (F := F) (S := S)
    let r := fun c : Xₛ(F, S) ↦ m c - n c
    let lower := fun (b : Xₛ(F, S) → ℕ) (c : Xₛ(F, S)) ↦ ((-(b c : ℤ) : ℤ) : WithTop ℤ)
    let sections := fun b : Xₛ(F, S) → ℕ ↦
      ↥(meromorphicWithPoleBound (twistₛ(F, S)) (lower b))
    let parts := fun b : Xₛ(F, S) → ℕ ↦ (c : Xₛ(F, S)) → Fin (b c) → ℂ
    ∃ (inc : sections r →ₗ[ℂ] sections m) (P : sections m →ₗ[ℂ] parts r)
        (M : Θₛ(F, S, ω) ≃ₗ[ℂ] sections m) (E : parts r ≃ₗ[ℂ] parts n),
      (∀ (g : sections r) (c : Xₛ(F, S)) (hm : 0 ≤ lower m c) (hr : 0 ≤ lower r c),
        (inc g).val ⟨c, hm⟩ = g.val ⟨c, hr⟩) ∧
      Function.Injective inc ∧ inc.range = P.ker ∧ Function.Surjective P ∧
      (∀ (f : ℬₛ(F, S)) (c : Xₛ(F, S)) (hc : 0 ≤ lower m c),
        (M ((Kₛ(F, S, ω)).mkQ f)).val ⟨c, hc⟩ =
          if onComponent(F, S, c, ω) then sLocalIdelicZFunction f c else 0) ∧
      inc.range.comap M.toLinearMap = sLocalThetaPoleBound ω n ∧
      (∀ (c : Xₛ(F, S)), 0 < n c →
        ∃ e : (Fin (r c) → ℂ) ≃ₗ[ℂ] (Fin (n c) → ℂ), ∀ y : parts r, E y c = e (y c)) ∧
      (∀ (f : ℬₛ(F, S)) (c : Xₛ(F, S)) (j : Fin (n c)),
        E (P (M ((Kₛ(F, S, ω)).mkQ f))) c j = sLocalNonnegativeLaurentCoeff c (j.val + 1) f)

/-- Paper: Remark 7.2.1.2, p. 335.
Over ℚ with the real place and p, select p. At 2πi/log p on the trivial
component the full and selected multiplicities both equal one. The last
identification would take the zero-dimensional stalk to a one-dimensional one. -/
theorem sLocalThetaPoleBound_printed_mellin_sequence_false :
    ¬ sLocalThetaPoleBound_printed_mellin_sequence := by sorry

/-- Paper: Remark 7.2.1.2, p. 335.
The middle-term surjectivity consequence on each component takes the whole
homogeneous theta space onto all meromorphic sections with the full divisor
bound. Those sections are expressed as meromorphic functions in a component chart. -/
def sLocalMellin_surjective_divisorBounded : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (χ : PontryaginDual Jₛ(F, S))
    (Z : ℂ → ℂ), Meromorphic Z →
    (∀ z : ℂ, let c : Xₛ(F, S) := twistₛ(F, S) ((circleToComplex).comp χ) z
      ((-(sLocalRhoPoleOrder c : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Z z) →
    ∃ f : ℬₛ(F, S), (fun z : ℂ ↦ sLocalIdelicZFunction f (twistₛ(F, S) ((circleToComplex).comp χ) z))
      =ᶠ[codiscrete ℂ] Z

/-- Paper: Remark 7.2.1.2, p. 335.
For ℚ with only the real place and the trivial component, the constant entire
function one satisfies the divisor bound but violates the vertical decay of
every Schwartz–Bruhat Mellin transform on the line of real part one. -/
theorem sLocalMellin_surjective_divisorBounded_false :
    ¬ sLocalMellin_surjective_divisorBounded := by sorry

/-- Paper: Remark 7.2.1.3, p. 335.
The full pole bound is identified with the closure of the homogeneous theta
image of tests vanishing to all required orders on coordinate hyperplanes. -/
def sLocalThetaPoleBound_full_eq_polarFree : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (ω : PontryaginDual J₁(F, S))
    (r : (w : {w : InfinitePlace F // w.IsReal}) →
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
    (c : (w : {w : InfinitePlace F // w.IsComplex}) →
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)}),
    sLocalThetaPoleBound ω sLocalRhoPoleOrder =
      ((sAdelePolarFree S r c).map (Kₛ(F, S, ω)).mkQ).topologicalClosure

/-- Paper: Remark 7.2.1.3, p. 335.
For ℚ with the real place and p, the real Gaussian times the indicator of ℤₚ
has a double pole at the trivial character. The coordinatewise polar-free
image has entire Mellin transform and its closure still has the zero pole bound. -/
theorem sLocalThetaPoleBound_full_eq_polarFree_false :
    ¬ sLocalThetaPoleBound_full_eq_polarFree := by sorry

open Classical in
/-- Paper: Preamble to (7.2.1.12), p. 336.
The coordinate insertions into the S-idèle quotient are closed embeddings. -/
def sLocalCoordinate_closedEmbedding : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)),
    let prod := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
      ((v : S) → v.val.adicCompletion F)
    let arch := ContinuousMulEquiv.piUnits (M := InfinitePlace.Completion (K := F))
    let fin := ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
    (∀ w : InfinitePlace F, IsClosedEmbedding (fun x : w.Completionˣ ↦
      (QuotientGroup.mk (prod.symm (arch.symm (Pi.mulSingle w x), 1)) : Jₛ(F, S)))) ∧
    (∀ v : S, IsClosedEmbedding (fun x : (v.val.adicCompletion F)ˣ ↦
      (QuotientGroup.mk (prod.symm (1, fin.symm (Pi.mulSingle v x))) : Jₛ(F, S))))

/-- Paper: Preamble to (7.2.1.12), p. 336.
For ℚ with only the real place, the two real units 1 and −1 give the same class. -/
theorem sLocalCoordinate_closedEmbedding_false : ¬ sLocalCoordinate_closedEmbedding := by sorry

/-- Paper: Chart change before Theorem 7.2.1.4, p. 336.
For two unitary base points of the same component, the new base is asserted to be
the pure imaginary norm twist specifying the chart translation. -/
def sLocalChangeOfChart_pureNormBase : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ χ' : PontryaginDual Jₛ(F, S)),
    (∀ g : J₁(F, S), χ g.val = χ' g.val) →
    ∃! t : ℝ, (circleToComplex).comp χ' = twistₛ(F, S) 1 ((t : ℂ) * Complex.I) ∧
      ∀ s : ℂ, twistₛ(F, S) ((circleToComplex).comp χ') (s - (t : ℂ) * Complex.I) =
        twistₛ(F, S) ((circleToComplex).comp χ) s

/-- Paper: Chart change before Theorem 7.2.1.4, p. 336.
For ℚ with the real place and 5, take the quadratic character on the 5-adic units,
trivial on 5 and on the real factor. It kills the S-units. Its twist by the norm
to the power i still equals −1 on the 5-adic unit 2, where every pure norm twist is one. -/
theorem sLocalChangeOfChart_pureNormBase_false : ¬ sLocalChangeOfChart_pureNormBase := by sorry

open Classical in
/-- Paper: Equation (7.2.1.13), p. 336. The unscaled formula with a specified Laurent exponent. -/
def sLocalUnscaledLeadingIdentity (exponent : ℕ → ℤ) : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (c : Xₛ(F, S)),
    c ∈ poleLocus(F, S) → ∀ f : ℬₛ(F, S),
    let arch := sLocalArchPolePlaces c
    let fin := sLocalFinitePolePlaces c
    let archEuler (w : InfinitePlace F) (z : ℂ) :=
      infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (twistₛ(F, S) c z))
    let finEuler (v : S) (z : ℂ) :=
      finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ(F, S) c z))
    sLocalZLaurentCoeff f c (exponent (sLocalRhoPoleOrder c)) =
      (∏ w ∈ arch, complexResidue (archEuler w) 0) *
      (∏ w ∈ Finset.univ \ arch, archEuler w 0) *
      (∏ v ∈ fin, complexResidue (finEuler v) 0) *
      (∏ v ∈ Finset.univ \ fin, finEuler v 0) *
      sLocalNormalizedEigendistribution (dualₛ(F, S) c) (sAdeleSchwartzFourier f)

/-- Paper: Equation (7.2.1.13), p. 336.
Reading the subscript according to Definition 7.1.2.1 gives a nonnegative exponent. -/
def sLocalPrincipalPartCoeff_leading_literal : Prop :=
  sLocalUnscaledLeadingIdentity.{u} (fun m ↦ (m : ℤ))

/-- Paper: Equation (7.2.1.13), p. 336.
For ℚ with the real place take the trivial center and an even nonzero nonnegative
bump on 2 < |x| < 3. Its first Mellin derivative is positive. The right side is
zero since the leading polar functional at the trivial character is a multiple
of the test value at zero. -/
theorem sLocalPrincipalPartCoeff_leading_literal_false :
    ¬ sLocalPrincipalPartCoeff_leading_literal := by sorry

/-- Paper: Equation (7.2.1.13), p. 336.
With the leading-pole interpretation specified in (7.2.1.19), the unscaled
product still omits the factor from Fourier and Gaussian normalization. -/
def sLocalPrincipalPartCoeff_leading_unscaled : Prop :=
  sLocalUnscaledLeadingIdentity.{u} (fun m ↦ -(m : ℤ))

/-- Paper: Equation (7.2.1.13), p. 336.
Take ℚ(i) with the complex place and the place over 2, the trivial character, and
the standard complex Gaussian times the local integer indicator. The leading
coefficient is nonzero. The finite unit mass and epsilon at the center are each
1/2, so the printed right-hand side is four times the left-hand side. -/
theorem sLocalPrincipalPartCoeff_leading_unscaled_false :
    ¬ sLocalPrincipalPartCoeff_leading_unscaled := by sorry

/-- Paper: Equation (7.2.1.14), p. 337.
The test coefficient on the left is read with Definition 7.1.2.1. The sentence
following the display explicitly specifies exponent −m+j for the rho coefficient. -/
def sLocalPrincipalPartCoeff_lower_literal : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (c : Xₛ(F, S))
    (f : ℬₛ(F, S)) (k : ℕ), k < sLocalRhoPoleOrder c →
    let m := sLocalRhoPoleOrder c
    sLocalNonnegativeLaurentCoeff c k f =
      ∑ j ∈ Finset.range (m - k + 1),
        complexResidue (fun z : ℂ ↦ sLocalRhoFactor (twistₛ(F, S) c z) *
          z ^ ((m : ℤ) - (j : ℤ) - 1)) 0 *
        (iteratedDeriv (m - k - j) (fun z ↦ sLocalIdelicZFunction
          (sAdeleSchwartzFourier f) (dualₛ(F, S) (twistₛ(F, S) c z))) 0 /
          ((m - k - j).factorial : ℂ))

/-- Paper: Equation (7.2.1.14), p. 337.
Over ℚ with the real place and p, at the trivial center m = 2. Take index one,
a nonzero nonnegative even bump supported on 2 < |x| < 3 and the finite unit
indicator. Its zeta function is entire. The convolution on the right gives its
zero residue, while its first Taylor coefficient on the left is positive. -/
theorem sLocalPrincipalPartCoeff_lower_literal_false :
    ¬ sLocalPrincipalPartCoeff_lower_literal := by sorry

/-- Paper: Equation (7.2.1.17), p. 337.
The printed functional equation inserts an additional epsilon factor in the
ratio of the original and Fourier Euler products. The two basic products use
the same normalization, so their common scalar cancels. -/
def sLocalFunctionalEquation_extra_epsilon : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (χ : PontryaginDual Jₛ(F, S))
    (f : ℬₛ(F, S)),
    (fun z : ℂ ↦ sLocalIdelicZFunction f (twistₛ(F, S) ((circleToComplex).comp χ) z))
      =ᶠ[codiscrete ℂ] fun z ↦
        let c : Xₛ(F, S) := twistₛ(F, S) ((circleToComplex).comp χ) z
        sLocalEpsilonFactor c * (sLocalHeckeL c / sLocalFourierEulerProduct c) *
          sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ(F, S) c)

/-- Paper: Equation (7.2.1.17), p. 337.
For ℚ(i) with the complex place and the place over 2, take the trivial unitary
base and its standard Gaussian tensor. At exponent 1/4 the zeta integral is
nonzero and the epsilon factor is not one. The ratio already contains epsilon,
so the proposed identity fails on a neighborhood of that exponent. -/
theorem sLocalFunctionalEquation_extra_epsilon_false :
    ¬ sLocalFunctionalEquation_extra_epsilon := by sorry

open Classical in
/-- Paper: Proposition 7.2.2.1, p. 339.
The four printed conditions include exact global zero orders, with the
one-order exception at the trivial character on the selected divisor. -/
def sLocalPrincipalValue_tfae_exact_order : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S S₀ : Finset Places(F)) (h₀ : S₀ ⊆ S)
    (_hn : S₀.Nonempty) (_hPic : Subsingleton (CommRing.Pic ((S : Set Places(F)).integer F)))
    (χ : PontryaginDual C𝔽(F)) (hχ : globalUnitary(F, χ) ∈ unramifiedOutside F S₀) (f : ℬₛ(F, S)),
    let hS : globalUnitary(F, χ) ∈ unramifiedOutside F S := outsideS(h₀, hχ)
    let ω := globalNormOne(F, χ)
    let hω : NormOneCharacterUnramifiedOutside ω S := ⟨⟨globalUnitary(F, χ), hS⟩, fun _ ↦ rfl⟩
    let ωₛ := sLocalNormOneCharacter S ω hω
    let x := (Kₛ(F, S, ωₛ)).mkQ f
    let π := sLocalHomogeneousThetaToGlobal hω
    let Z := fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s)
    List.TFAE [
      (∀ (c : Xₛ(F, S)), onComponent(F, S, c, ωₛ) → 0 < sLocalFinitePoleMultiplicity S₀ c →
        ∀ k : ℕ, sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity S₀ c < k →
          k ≤ sLocalRhoPoleOrder c → sLocalNonnegativeLaurentCoeff c k f = 0),
      (∀ s : ℂ, 0 < sLocalFinitePoleMultiplicity S₀ (localChart(F, S, χ, hS) s) →
        let n := sLocalFinitePoleMultiplicity S₀ (localChart(F, S, χ, hS) s)
        meromorphicOrderAt Z s = ((if ideleClassNormTwist χ s = 1 then n - 1 else n : ℕ) : WithTop ℤ)),
      x ∈ (sLocalHomogeneousThetaPrincipalValue h₀ ωₛ).range,
      (∃ g : ℬ𝔽(F), (K𝔽(F, ω)).mkQ (adelePrincipalValue F S₀ g) = π x)
    ]

/-- Paper: Proposition 7.2.2.1, p. 339.
Take ℚ, the real place and p, select p, and take the trivial character and the
zero test. Its local coefficients vanish and both principal-value preimages
can be zero. Its global order at the trivial character is ⊤, whereas the
printed condition requires order zero. -/
theorem sLocalPrincipalValue_tfae_exact_order_false :
    ¬ sLocalPrincipalValue_tfae_exact_order := by sorry

open Classical in
/-- Paper: Corollary 7.2.2.2, p. 340.
The four printed conditions on the two-evaluation kernel require exact global
zero orders and shift the local coefficient interval at the trivial character. -/
def sLocalPolarPrincipalValue_tfae_exact_order : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S S₀ : Finset Places(F)) (h₀ : S₀ ⊆ S)
    (_hn : S₀.Nonempty) (_hPic : Subsingleton (CommRing.Pic ((S : Set Places(F)).integer F)))
    (χ : PontryaginDual C𝔽(F)) (hχ : globalUnitary(F, χ) ∈ unramifiedOutside F S₀)
    (f : sAdelePolarSubspace F S),
    let hS : globalUnitary(F, χ) ∈ unramifiedOutside F S := outsideS(h₀, hχ)
    let ω := globalNormOne(F, χ)
    let hω : NormOneCharacterUnramifiedOutside ω S := ⟨⟨globalUnitary(F, χ), hS⟩, fun _ ↦ rfl⟩
    let ωₛ := sLocalNormOneCharacter S ω hω
    let x := (Kₛ(F, S, ωₛ)).mkQ f.val
    let π := sLocalHomogeneousThetaToGlobal hω
    let Z := fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f.val) (ideleClassNormTwist χ s)
    List.TFAE [
      (∀ (c : Xₛ(F, S)), onComponent(F, S, c, ωₛ) → 0 < sLocalFinitePoleMultiplicity S₀ c →
        let m := sLocalRhoPoleOrder c
        let n := sLocalFinitePoleMultiplicity S₀ c
        ∀ k : ℕ, (if c = 1 then m - n ≤ k ∧ k ≤ m - 1 else m - n < k ∧ k ≤ m) →
          sLocalNonnegativeLaurentCoeff c k f.val = 0),
      (∀ s : ℂ, 0 < sLocalFinitePoleMultiplicity S₀ (localChart(F, S, χ, hS) s) →
        meromorphicOrderAt Z s = (sLocalFinitePoleMultiplicity S₀ (localChart(F, S, χ, hS) s) : WithTop ℤ)),
      (∃ g : sAdelePolarSubspace F S, (Kₛ(F, S, ωₛ)).mkQ (sAdelePrincipalValue F h₀ g.val) = x),
      (∃ g : adelePolarSubspace F, (K𝔽(F, ω)).mkQ (adelePrincipalValue F S₀ g.val) = π x)
    ]

/-- Paper: Corollary 7.2.2.2, p. 340.
Take ℚ, the real place and p, select p, and take the trivial character and the
zero test. Both evaluations vanish, all local coefficients vanish, and both
principal-value preimages can be zero. The global order is ⊤ at the trivial
character, while the asserted order is one. -/
theorem sLocalPolarPrincipalValue_tfae_exact_order_false :
    ¬ sLocalPolarPrincipalValue_tfae_exact_order := by sorry

end Printed
end RiemannMasullo
