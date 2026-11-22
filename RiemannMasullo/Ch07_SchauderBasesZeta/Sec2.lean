module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec5
public import RiemannMasullo.Ch06_LocalGlobal.Sec2

/-!
# §7.2 Poles of the S-idelic zeta functions

The finite set `S` lists the finite places. Every archimedean place is included.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain NumberField Set Topology
open scoped BigOperators NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Places" => HeightOneSpectrum (𝓞 F)
local notation "Jₛ" => SIdeleQuotient F S
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Xₛ" => QuasiCharacter Jₛ
local notation "Aₛ" => SAdeleRing F S
local notation "ℬₛ" => SchwartzBruhat (Multiplicative Aₛ)
local notation "ℬ𝔽" => SchwartzBruhat (Multiplicative (𝔸[F]))
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "m𝔽" => ideleClassNorm F
local notation "hmₛ" => (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "J₁" => (mₛ).ker
local notation "twistₛ" => quasiCharacterNormTwist (G := Jₛ) mₛ hmₛ
local notation "dualₛ" => dualQuasiCharacter (G := Jₛ) mₛ hmₛ
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "onComponent(" c ", " ω ")" =>
  (normOneRestriction mₛ c = (circleToComplex).comp ω)
local notation "Θₛ(" ω ")" => SLocalHomogeneousThetaSpace F S ω
local notation "Kₛ(" ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)
local notation "coeff(" c ", " k ")" => (fun f : ℬₛ ↦ sLocalZLaurentCoeff f c (-(k : ℤ)))

-- TODO(paper-gap): The inclusions in (7.2.0.1)–(7.2.0.2) require an effective divisor.
-- This section uses the earlier meromorphic model on the character components.
-- TODO(paper-gap): (7.2.1.3)–(7.2.1.5) repeat the asymptotic expansion with
-- the missing constant term and repeated poles of Theorem 7.1.2.3. Use its
-- pole-free contour cutoff and the corrected complex pole family in §7.1.
-- At finite places the periodic lattice occurs only for unramified characters.
-- TODO(paper-gap): In (7.2.1.8) the contour needs positive orientation and
-- must isolate the chosen pole. The coefficient uses the small-circle residue of §B.3.

/-- Paper: Theorem 7.2.1.1(1), p. 334.
Taking a Laurent coefficient in the centered chart is continuous and complex linear.
Deviation: Integer exponents cover both the nonnegative indices of Definition 7.1.2.1
and the polar coefficients extracted by (7.2.1.8). -/
theorem sLocalZLaurentCoeff_continuous_linear (c : Xₛ) (j : ℤ) :
    let a := fun f : ℬₛ ↦ sLocalZLaurentCoeff f c j
    Continuous a ∧ IsLinearMap ℂ a := by sorry

/-- Paper: Theorem 7.2.1.1(1), p. 334.
Each Laurent coefficient of nonpositive exponent depends continuously and complex
linearly on the S-adelic test.
Deviation: The coefficient indexed by `k` here has exponent `-k`, as required by
the principal part formula and the Laurent convention of Definition 7.1.2.1. -/
theorem sLocalPrincipalPartCoeff_continuous_linear (c : Xₛ) (k : ℕ) :
    Continuous coeff(c, k) ∧ IsLinearMap ℂ coeff(c, k) :=
  sLocalZLaurentCoeff_continuous_linear c (-(k : ℤ))

/-- Paper: Theorem 7.2.1.1(1)–(2), p. 334.
The coefficient of exponent `-k` is a continuous linear functional on the test space. -/
def sLocalPrincipalPartCoeff (c : Xₛ) (k : ℕ) : StrongDual ℂ ℬₛ :=
  ⟨(sLocalPrincipalPartCoeff_continuous_linear c k).2.mk' coeff(c, k),
    (sLocalPrincipalPartCoeff_continuous_linear c k).1⟩

/-- Paper: Theorem 7.2.1.1(1), p. 334.
The bundled functional evaluates to the coefficient of the Laurent power `-k`. -/
theorem sLocalPrincipalPartCoeff_apply (c : Xₛ) (k : ℕ) (f : ℬₛ) :
    sLocalPrincipalPartCoeff c k f = sLocalZLaurentCoeff f c (-(k : ℤ)) := by sorry

-- TODO(paper-gap): In Theorem 7.2.1.1(2), lower coefficients at a multiple
-- pole mix with higher ones under translation. The leading coefficient has
-- the claimed weight, as stated in Theorem 7.2.1.4(1).

/-- Paper: Theorem 7.2.1.1(2), p. 334.
The coefficient annihilates the kernel of homogeneous theta on the component
of its center. This gives continuous descent through both theta quotients.
Deviation: The weight equation for the leading coefficient is stated in
Theorem 7.2.1.4(1). -/
theorem sLocalPrincipalPartCoeff_ker (ω : PontryaginDual J₁) (c : Xₛ)
    (hc : onComponent(c, ω)) (k : ℕ) :
    Kₛ(ω) ≤ (sLocalPrincipalPartCoeff c k).ker := by sorry

/-- Paper: Theorem 7.2.1.1(2), p. 334.
The coefficient acts on the homogeneous theta quotient of its norm-one character. -/
def sLocalThetaPrincipalPartCoeff (ω : PontryaginDual J₁) (c : Xₛ)
    (hc : onComponent(c, ω)) (k : ℕ) : StrongDual ℂ (Θₛ(ω)) :=
  (Kₛ(ω)).liftQL (sLocalPrincipalPartCoeff c k) (sLocalPrincipalPartCoeff_ker ω c hc k)

/-- Paper: Theorem 7.2.1.1(2), p. 334.
The descended coefficient recovers the original coefficient on a test representative. -/
theorem sLocalThetaPrincipalPartCoeff_mk (ω : PontryaginDual J₁) (c : Xₛ)
    (hc : onComponent(c, ω)) (k : ℕ) (f : ℬₛ) :
    sLocalThetaPrincipalPartCoeff ω c hc k ((Kₛ(ω)).mkQL f) =
      sLocalZLaurentCoeff f c (-(k : ℤ)) := by sorry

/-- Paper: Theorem 7.2.1.1(2), p. 334.
Translation acts on coefficients of nonpositive exponent by an upper triangular formula.
Deviation: Lower coefficients also receive terms from the higher polar coefficients.
The extra terms vanish on norm-one translations. -/
theorem sLocalPrincipalPartCoeff_translate (c : Xₛ) (k : ℕ) (hk : k ≤ sLocalRhoPoleOrder c)
    (u : Aₛˣ) (f : ℬₛ) :
    let g : Jₛ := QuotientGroup.mk u
    let logNorm : ℂ := Real.log (((mₛ g : ℝ≥0) : ℝ))
    sLocalPrincipalPartCoeff c k (schwartzBruhatUnitTranslate u f) =
      c g * ∑ j ∈ Finset.range (sLocalRhoPoleOrder c - k + 1),
        sLocalPrincipalPartCoeff c (k + j) f * logNorm ^ j / (j.factorial : ℂ) := by sorry

-- TODO(paper-gap): The universal inequality in Theorem 7.2.1.1(3)
-- fails on the zero test whenever the functional is nonzero and k > 0.

/-- Paper: Theorem 7.2.1.1(3), p. 334.
A nonvanishing polar coefficient forces a pole of the test's zeta function of at
least the indicated order, at an allowed pole of the correcting factor.
Deviation: The inequality holds for the test on which the coefficient is nonzero,
and a polar coefficient has strictly negative Laurent exponent. -/
theorem sLocalPrincipalPartCoeff_ne_zero_imp_pole (c : Xₛ) (k : ℕ) (hk : 0 < k)
    (f : ℬₛ) (hf : sLocalPrincipalPartCoeff c k f ≠ 0) :
    0 < sLocalRhoPoleOrder c ∧ k ≤ sLocalPolarMultiplicity f c := by sorry

/-- Paper: Equation (7.2.1.6), p. 334.
The subspace is spanned by homogeneous theta classes whose pole orders on the
chosen component satisfy the given bound.
Deviation: The bound is extended to all quasi-characters. Its values off the
allowed pole divisor do not affect the subspace. -/
def sLocalThetaPoleBound (ω : PontryaginDual J₁) (m : Xₛ → ℕ) : Submodule ℂ (Θₛ(ω)) :=
  Submodule.span ℂ {x | ∃ f : ℬₛ, (Kₛ(ω)).mkQ f = x ∧
    ∀ c : Xₛ, onComponent(c, ω) → sLocalPolarMultiplicity f c ≤ m c}

/-- Paper: Equation (7.2.1.9), p. 334.
Membership in the pole-bound subspace is equivalent to vanishing of every coefficient
on the component above its allowed pole order. -/
theorem mem_sLocalThetaPoleBound_iff (ω : PontryaginDual J₁) (m : Xₛ → ℕ) (x : Θₛ(ω)) :
    x ∈ sLocalThetaPoleBound ω m ↔
      ∀ (c : Xₛ) (hc : onComponent(c, ω)), 0 < sLocalRhoPoleOrder c →
        ∀ k : ℕ, m c < k → sLocalThetaPrincipalPartCoeff ω c hc k x = 0 := by sorry

/-- Paper: Theorem 7.2.1.1(4), p. 334.
The homogeneous theta classes with the prescribed bounds on pole order form a closed subspace. -/
theorem sLocalThetaPoleBound_isClosed (ω : PontryaginDual J₁) (m : Xₛ → ℕ) :
    IsClosed (sLocalThetaPoleBound ω m : Set (Θₛ(ω))) := by sorry

/-- Paper: Theorem 7.2.1.1(4), p. 334.
The annihilator of the pole-bound subspace is the strong closure of the span of the
descended coefficients above the bound.
Deviation: Uses the indices in (7.2.1.7). Lower coefficients can fail the weight
equation, and spanning here means closed linear span in the strong dual. -/
theorem sLocalThetaPoleBound_annihilator (ω : PontryaginDual J₁) (m : Xₛ → ℕ) :
    (sLocalThetaPoleBound ω m).dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ) =
      (Submodule.span ℂ {T : StrongDual ℂ (Θₛ(ω)) |
        ∃ (c : Xₛ) (hc : onComponent(c, ω)) (k : ℕ),
          0 < sLocalRhoPoleOrder c ∧ m c < k ∧ sLocalThetaPrincipalPartCoeff ω c hc k = T
      }).topologicalClosure := by sorry

local notation "archEuler(" w ", " c ")" =>
  (fun z : ℂ ↦ infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (twistₛ c z)))
local notation "finEuler(" v ", " c ")" =>
  (fun z : ℂ ↦ finiteLocalEulerFactor (v).val (sLocalFiniteRestriction v (twistₛ c z)))

-- TODO(paper-gap): The coordinate homomorphism into Jₛ can have a kernel.
-- For ℚ with only the real place it kills -1. Restriction uses the
-- homomorphisms of §3.3 without an injectivity condition.

open Classical in
/-- Paper: Equation (7.2.1.11), p. 335.
The archimedean places contributing a pole at a given character are those whose
restricted local Euler factors have a pole in the norm coordinate. -/
def sLocalArchPolePlaces (c : Xₛ) : Finset (InfinitePlace F) :=
  Finset.univ.filter (fun w ↦ meromorphicOrderAt (archEuler(w, c)) 0 < 0)

open Classical in
/-- Paper: Equation (7.2.1.11), p. 335.
The finite places contributing a pole at a given character are those whose
restricted local Euler factors have a pole in the norm coordinate. -/
def sLocalFinitePolePlaces (c : Xₛ) : Finset S :=
  Finset.univ.filter (fun v : S ↦ meromorphicOrderAt (finEuler(v, c)) 0 < 0)

/-- Paper: Equation (7.2.1.11), p. 335.
At the trivial quasi-character every archimedean and every selected finite place
contributes a pole. -/
theorem sLocalPolePlaces_one :
    sLocalArchPolePlaces (1 : Xₛ) = Finset.univ ∧
      sLocalFinitePolePlaces (1 : Xₛ) = Finset.univ := by sorry

/-- Paper: Theorem 7.2.1.4, p. 336.
The allowed pole multiplicity at a character counts the contributing places,
each of which contributes a simple pole. -/
theorem sLocalRhoPoleOrder_eq_card_polePlaces (c : Xₛ) :
    sLocalRhoPoleOrder c = (sLocalArchPolePlaces c).card + (sLocalFinitePolePlaces c).card :=
  by sorry

open Classical in
/-- Paper: Equations (7.2.2.1)–(7.2.2.2), pp. 338–339.
The multiplicity counts poles contributed by the selected finite places. The
selected pole locus consists of the points of positive multiplicity.
Deviation: Extends the multiplicity by zero outside the selected pole locus. -/
def sLocalFinitePoleMultiplicity (S₀ : Finset Places) (c : Xₛ) : ℕ :=
  ((sLocalFinitePolePlaces c).filter (fun v ↦ v.val ∈ S₀)).card

/-- Paper: Equations (7.2.2.1)–(7.2.2.2), pp. 338–339.
The selected divisor at the trivial character has multiplicity equal to the number
of selected finite places. -/
theorem sLocalFinitePoleMultiplicity_one (S₀ : Finset Places) (h₀ : S₀ ⊆ S) :
    sLocalFinitePoleMultiplicity S₀ (1 : Xₛ) = S₀.card := by
  classical
  unfold sLocalFinitePoleMultiplicity
  rw [(sLocalPolePlaces_one (F := F) (S := S)).2]
  apply Finset.card_bij (fun v _ ↦ v.val)
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro _ _ _ _ h
    exact Subtype.ext h
  · intro v hv
    exact ⟨⟨v, h₀ hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩

open Classical in
/-- Paper: Equations (7.2.2.1)–(7.2.2.2), pp. 338–339.
The selected divisor counts the contributing places from both the archimedean and the
finite selections. The multiplicity is zero off the selected pole locus. -/
def sLocalSelectedPoleMultiplicity (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places)
    (c : Xₛ) : ℕ :=
  (sLocalArchPolePlaces c ∩ SArch).card + sLocalFinitePoleMultiplicity S₀ c

/-- Paper: Equations (7.2.2.1)–(7.2.2.2), pp. 338–339.
Selecting just the finite places gives the multiplicity used for principal values. -/
theorem sLocalSelectedPoleMultiplicity_finite (S₀ : Finset Places) (c : Xₛ) :
    sLocalSelectedPoleMultiplicity ∅ S₀ c = sLocalFinitePoleMultiplicity S₀ c := by sorry

/-- Paper: Equations (7.2.2.1)–(7.2.2.2), pp. 338–339.
Selecting every place recovers the full pole order. -/
theorem sLocalSelectedPoleMultiplicity_full (c : Xₛ) :
    sLocalSelectedPoleMultiplicity Finset.univ S c = sLocalRhoPoleOrder c := by sorry

-- TODO(paper-gap): For D = U_S and E = U_{S₀}, the sheaf target in Remark 7.2.1.2
-- is O(D)/O(D-E), with stalk length mult(E), whereas the printed P_{X,D-E} has
-- stalk length mult(D-E). The Mellin image imposes strip decay. We use the
-- coefficient map on that image, with the highest coefficients on one component.
-- Already for ℚ and S = {∞, p}, residues along the nonzero points of the p-lattice
-- decay rapidly. A constant nonzero residue sequence is outside the attained range.

local notation "remainingBound(" SArch ", " S₀ ")" =>
  (fun c : Xₛ ↦ sLocalRhoPoleOrder c - sLocalSelectedPoleMultiplicity SArch S₀ c)

local notation "removedIndices(" ω ", " SArch ", " S₀ ")" =>
  {i : Xₛ × ℕ // onComponent(i.1, ω) ∧
    remainingBound(SArch, S₀) i.1 < i.2 ∧ i.2 ≤ sLocalRhoPoleOrder i.1}

/-- Paper: Remark 7.2.1.2, p. 335.
On the chosen component, collect the coefficients removed when the pole bound
is lowered by the multiplicity of the selected divisor.
Deviation: At multiplicities `m` and `n`, the index runs over `m - n < k ≤ m`. -/
def sLocalThetaRemovedPrincipalParts (ω : PontryaginDual J₁)
    (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places) :
    Θₛ(ω) →ₗ[ℂ] (removedIndices(ω, SArch, S₀) → ℂ) :=
  LinearMap.pi fun i ↦ (sLocalThetaPrincipalPartCoeff ω i.val.1 i.property.1 i.val.2).toLinearMap

/-- Paper: Remark 7.2.1.2, p. 335.
On a theta representative the removed principal parts evaluate to the corresponding
Laurent coefficients. -/
theorem sLocalThetaRemovedPrincipalParts_mk (ω : PontryaginDual J₁)
    (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places) (f : ℬₛ)
    (i : removedIndices(ω, SArch, S₀)) :
    sLocalThetaRemovedPrincipalParts ω SArch S₀ ((Kₛ(ω)).mkQ f) i =
      sLocalZLaurentCoeff f i.val.1 (-(i.val.2 : ℤ)) := by sorry

/-- Paper: Remark 7.2.1.2, p. 335.
On the Mellin image, the classes with the remaining pole bound are exactly the
kernel of the removed-coefficient map.
Deviation: The remaining bound is `m_S - m_{S₀}`. -/
theorem sLocalThetaRemovedPrincipalParts_ker (ω : PontryaginDual J₁)
    (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places) :
    (sLocalThetaRemovedPrincipalParts ω SArch S₀).ker =
      sLocalThetaPoleBound ω remainingBound(SArch, S₀) := by sorry

/-- A coefficient map identifies the quotient by its kernel with the attained values. -/
private theorem sLocalThetaRemovedPrincipalParts_quotient_of_ker {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (A : V →ₗ[ℂ] W)
    (H : Submodule ℂ V) (h : A.ker = H) :
    ∃ e : (V ⧸ H) ≃ₗ[ℂ] A.range, ∀ x, (e (H.mkQ x)).val = A x := by
  subst H
  exact ⟨A.quotKerEquivRange, fun x ↦ A.quotKerEquivRange_apply_mk x⟩

/-- Paper: Remark 7.2.1.2, p. 335.
The quotient by the remaining pole bound is identified by the coefficient map
with the principal parts attained on the chosen Mellin component.
Deviation: The surjective target is the range of the coefficient map. -/
theorem sLocalThetaRemovedPrincipalParts_quotient (ω : PontryaginDual J₁)
    (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places) :
    let H := sLocalThetaPoleBound ω remainingBound(SArch, S₀)
    let A := sLocalThetaRemovedPrincipalParts ω SArch S₀
    ∃ e : (Θₛ(ω) ⧸ H) ≃ₗ[ℂ] A.range, ∀ x : Θₛ(ω), (e (H.mkQ x)).val = A x := by
  intro H A
  have h := sLocalThetaRemovedPrincipalParts_ker (F := F) (S := S) ω SArch S₀
  let I := removedIndices(ω, SArch, S₀)
  with_reducible
    exact sLocalThetaRemovedPrincipalParts_quotient_of_ker (V := Θₛ(ω)) (W := I → ℂ) A H h

-- TODO(paper-gap): In Remark 7.2.1.3 the full bound H_{m_S} permits all poles.
-- The image of S₀₀ has no poles and corresponds to H with bound zero.
-- TODO(later): needs §7.3.1 for the claimed application of Theorem 7.3.1.2.
-- Theorem 7.3.1.2 includes the archimedean places in S₀, whereas §5.3.1
-- supplies principal values at finite places.

/-- Paper: Remark 7.2.1.3, p. 335.
The theta image of the coordinatewise polar-free tests is the subspace with
entire Mellin transform.
Deviation: The bound is zero. This is the quotient form of Proposition 5.3.4.4. -/
theorem sLocalThetaPoleBound_zero (ω : PontryaginDual J₁)
    (r : (w : {w : InfinitePlace F // w.IsReal}) →
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
    (c : (w : {w : InfinitePlace F // w.IsComplex}) →
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)}) :
    sLocalThetaPoleBound ω (fun _ ↦ 0) = (sAdelePolarFree S r c).map (Kₛ(ω)).mkQ := by sorry

/-- Paper: Remark 7.2.1.3, p. 335.
Interpreting a polar-free theta class as its theta function identifies the entire
subspace with the exponentially decreasing norm-one isotype, with its topology.
Deviation: The entire subspace is written as the zero pole bound. -/
theorem sLocalThetaPoleBound_zero_equiv_decay (ω : PontryaginDual J₁) :
    ∃ e : ↥(sLocalThetaPoleBound ω (fun _ ↦ 0)) ≃L[ℂ]
        ↥(sLocalDecayIsotype (F := F) (S := S) univ ω),
      ∀ (x : ↥(sLocalThetaPoleBound ω (fun _ ↦ 0))) (f : ℬₛ),
        x.val = (Kₛ(ω)).mkQ f →
          ∀ g : Jₛ, (e x).val.val g = sLocalHomogeneousAdelicThetaLinearMap F S ω f g := by sorry

/-- Paper: Equation (7.2.1.12), p. 336.
The Fourier-transformed Euler product is the Euler product at the dual character
divided by the local epsilon factor.
Deviation: The local tests are normalized so that their original zeta product is
the Euler product. This uses the epsilon normalization of (3.3.1.32). -/
def sLocalFourierEulerProduct (c : Xₛ) : ℂ :=
  sLocalHeckeL (dualₛ c) / sLocalEpsilonFactor c

/-- Paper: Equation (7.2.1.12), p. 336.
If an S-adelic test has the Euler product as its zeta transform on a component,
its Fourier transform on the reflected component gives the Fourier Euler product.
The equality is between meromorphic functions in the norm coordinate. -/
theorem sLocalFourierEulerProduct_eq_zeta (c : Xₛ) (f : ℬₛ)
    (hf : (fun z : ℂ ↦ sLocalIdelicZFunction f (twistₛ c z)) =ᶠ[codiscrete ℂ]
      (fun z ↦ sLocalHeckeL (twistₛ c z))) :
    (fun z : ℂ ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ (twistₛ c z)))
      =ᶠ[codiscrete ℂ] (fun z ↦ sLocalFourierEulerProduct (twistₛ c z)) := by sorry

local notation "finiteUnitMass" => (∏ v : S,
  (((finiteLocalMultiplicativeTamagawaMeasure F v.val)
    (v.val.adicCompletionIntegers F).units).toReal : ℂ))

/-- Paper: Equation (7.2.1.12), p. 336.
The Fourier transform of the tensor of the standard archimedean and finite tests
has the reflected Fourier Euler product as its Mellin transform, scaled by the
product of the integer-unit masses.
Deviation: The test is the unscaled tensor of §3.4, with its Tamagawa masses. -/
theorem sLocalFourierEulerProduct_eq_zeta_standardGaussian
    (χ : PontryaginDual Jₛ) (χArch : (w : InfinitePlace F) → PontryaginDual w.Completionˣ)
    (hχ : ∀ w, (circleToComplex).comp (χArch w) =
      sLocalInfiniteRestriction w ((circleToComplex).comp χ))
    (g : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
    (hg : ∀ x : InfiniteAdeleRing F, g (Multiplicative.ofAdd x) =
      ∏ w, infiniteStandardGaussian w (χArch w) (Multiplicative.ofAdd (x w))) :
    let c : Xₛ := (circleToComplex).comp χ
    let f := sLocalStandardThetaTensor c g
    (fun z : ℂ ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ (twistₛ c z)))
      =ᶠ[codiscrete ℂ] (fun z ↦ finiteUnitMass * sLocalFourierEulerProduct (twistₛ c z)) := by sorry

/-- Paper: Equations (7.2.1.12) and (7.2.1.17), pp. 336–337.
The ratio of the original Euler product to the Fourier Euler product gives the
local correcting factor as a meromorphic identity.
Deviation: The Fourier Euler product already incorporates the epsilon factor. -/
theorem sLocalRhoFactor_eq_div_fourierEulerProduct (c : Xₛ) :
    (fun z : ℂ ↦ sLocalRhoFactor (twistₛ c z)) =ᶠ[codiscrete ℂ]
      (fun z ↦ sLocalHeckeL (twistₛ c z) / sLocalFourierEulerProduct (twistₛ c z)) := by sorry

-- TODO(paper-gap): The change of unitary base point on p. 336 is
-- χ' = χ |·|^(it₀). The printed identity omits the original base point χ.

open Classical in
/-- Paper: Theorem 7.2.1.4(1), p. 336.
The coefficient of the highest allowed polar order is the product of local residues
and regular local Euler values times the Fourier-transformed dual eigendistribution.
Deviation: Uses the Laurent exponent `-m`. The epsilon factor and the finite
integer-unit masses account for the normalizations of §3.3 and §5.5. -/
theorem sLocalPrincipalPartCoeff_leading_formula (c : Xₛ) (hc : 0 < sLocalRhoPoleOrder c)
    (f : ℬₛ) :
    let arch := sLocalArchPolePlaces c
    let fin := sLocalFinitePolePlaces c
    sLocalPrincipalPartCoeff c (sLocalRhoPoleOrder c) f =
      (∏ w ∈ arch, complexResidue (archEuler(w, c)) 0) *
      (∏ w ∈ Finset.univ \ arch, archEuler(w, c) 0) *
      (∏ v ∈ fin, complexResidue (finEuler(v, c)) 0) *
      (∏ v ∈ Finset.univ \ fin, finEuler(v, c) 0) *
      (finiteUnitMass * sLocalEpsilonFactor c *
        sLocalNormalizedEigendistribution (dualₛ c) (sAdeleSchwartzFourier f)) := by sorry

/-- Paper: Theorem 7.2.1.4(1), p. 337.
The leading principal-part functional transforms with weight given by the center. -/
theorem sLocalPrincipalPartCoeff_leading_eigendistribution (c : Xₛ)
    (hc : 0 < sLocalRhoPoleOrder c) :
    sLocalPrincipalPartCoeff c (sLocalRhoPoleOrder c) ∈ sLocalEigendistributions c := by sorry

/-- Paper: Theorem 7.2.1.4(2), p. 337.
Each lower coefficient is a convolution of Laurent coefficients of the correcting
factor with Taylor coefficients of the reflected zeta function of the Fourier test.
Deviation: The coefficient indexed by `k` has exponent `-k`. At `k = 0`, the last
summand of (7.2.1.14) uses the constant Laurent coefficient of the correcting
factor. Differentiation in the original chart includes the sign from reflection. -/
theorem sLocalPrincipalPartCoeff_lower_formula (c : Xₛ) (f : ℬₛ) (k : ℕ)
    (hk : k < sLocalRhoPoleOrder c) :
    let m := sLocalRhoPoleOrder c
    sLocalPrincipalPartCoeff c k f =
      ∑ j ∈ Finset.range (m - k + 1),
        complexResidue (fun z : ℂ ↦ sLocalRhoFactor (twistₛ c z) *
          z ^ ((m : ℤ) - (j : ℤ) - 1)) 0 *
        (iteratedDeriv (m - k - j)
          (fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ (twistₛ c z))) 0 /
          ((m - k - j).factorial : ℂ)) := by sorry

section LocalPolesGlobalZeros

local notation "K𝔽(" ω ")" => LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)
local notation "globalUnitary(" χ ")" => ((circleToComplex).comp χ : QuasiCharacter C𝔽)
local notation "globalNormOne(" χ ")" =>
  ((χ).comp (⟨(m𝔽).ker.subtype, continuous_subtype_val⟩ : (m𝔽).ker →ₜ* C𝔽)
    : PontryaginDual (m𝔽).ker)
local notation "localChart(" χ ", " h ")" =>
  twistₛ (sIdeleRestriction F S ⟨globalUnitary(χ), h⟩)
local notation "outsideS(" h₀ ", " hχ ")" => (fun v hv ↦ hχ v (fun hv₀ ↦ hv (h₀ hv₀)))

-- TODO(paper-gap): The exact zero orders in Proposition 7.2.2.1(2) and
-- Corollary 7.2.2.2(2) fail even for the zero test. The pole cutoffs give
-- lower bounds. The proof of Proposition 7.2.2.1 also uses a factorization
-- with missing outside Fourier factors. Division by the reciprocal partial
-- Hecke Euler product in (2) implies (4) can retain both simple Tate poles
-- (at the trivial and norm characters). The meromorphic range characterization
-- in §6.3.2.1 is globalConverse_normTwist_meromorphic_exact in Ch06_LocalGlobal.Sec3.
-- For the restricted image, globalPrincipalValueConverse_normTwist_divided_exact
-- in that module detects the original two polar evaluations after division.
-- The range pullback in (4) implies (3) uses the isomorphism of §6.2.1.1(2)
-- and the principal-value commutation of §5.3.1. In the corollary, insertion scales
-- evaluation of the Fourier transform at zero by the nonzero outside additive
-- mass. Together with the unchanged value at zero this identifies the polar
-- subspaces on the trivial component. The two evaluations kill nontrivial isotypes.

open Classical in
/-- Paper: Proposition 7.2.2.1, p. 339.
Eliminating the selected highest local coefficients is equivalent to the global
zero-order bound and to membership in either homogeneous principal-value image.
Deviation: Zero orders are lower bounds on the meromorphic order. The bound drops
by one at the trivial quasi-character when it lies on the selected divisor. -/
theorem sLocalPrincipalValue_tfae {S₀ : Finset Places} (h₀ : S₀ ⊆ S) (_hn : S₀.Nonempty)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F)))
    (χ : PontryaginDual C𝔽) (hχ : globalUnitary(χ) ∈ unramifiedOutside F S₀)
    (f : ℬₛ) :
    let hS : globalUnitary(χ) ∈ unramifiedOutside F S := outsideS(h₀, hχ)
    let ω := globalNormOne(χ)
    let hω : NormOneCharacterUnramifiedOutside ω S := ⟨⟨globalUnitary(χ), hS⟩, fun _ ↦ rfl⟩
    let ωₛ := sLocalNormOneCharacter S ω hω
    let x := (Kₛ(ωₛ)).mkQ f
    let π := sLocalHomogeneousThetaToGlobal hω
    let Z := fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s)
    List.TFAE [
      (∀ (c : Xₛ), onComponent(c, ωₛ) → 0 < sLocalFinitePoleMultiplicity S₀ c →
        ∀ k : ℕ, sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity S₀ c < k →
          k ≤ sLocalRhoPoleOrder c → sLocalPrincipalPartCoeff c k f = 0),
      (∀ s : ℂ, 0 < sLocalFinitePoleMultiplicity S₀ (localChart(χ, hS) s) →
        let n := sLocalFinitePoleMultiplicity S₀ (localChart(χ, hS) s)
        ((if ideleClassNormTwist χ s = 1 then n - 1 else n : ℕ) : WithTop ℤ) ≤
          meromorphicOrderAt Z s),
      x ∈ (sLocalHomogeneousThetaPrincipalValue h₀ ωₛ).range,
      (∃ g : ℬ𝔽, (K𝔽(ω)).mkQ (adelePrincipalValue F S₀ g) = π x)
    ] := by sorry

local notation "polarValuesₛ" =>
  (fun f : ℬₛ ↦ (f (Multiplicative.ofAdd 0), sAdeleSchwartzFourier f (Multiplicative.ofAdd 0)))

/-- Paper: Equation (7.2.2.3), p. 340.
Evaluation at zero before and after S-adelic Fourier transform is complex linear. -/
theorem sAdelePolarValues_isLinear : IsLinearMap ℂ polarValuesₛ := by sorry

variable (F S) in
/-- Paper: Equation (7.2.2.3), p. 340.
The S-adelic polar subspace is the common kernel of evaluation at zero
and evaluation at zero after Fourier transform. -/
def sAdelePolarSubspace : Submodule ℂ ℬₛ :=
  LinearMap.ker ((sAdelePolarValues_isLinear (F := F) (S := S)).mk' polarValuesₛ)

/-- Paper: Equation (7.2.2.3), p. 340.
Membership requires both the test and its Fourier transform to vanish at zero. -/
theorem mem_sAdelePolarSubspace (f : ℬₛ) :
    f ∈ sAdelePolarSubspace F S ↔
      f (Multiplicative.ofAdd 0) = 0 ∧ sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0 :=
  by sorry

/-- Paper: Corollary 7.2.2.2, p. 340.
Insertion with integer indicators outside S preserves the two zero evaluations
that define the polar subspaces. -/
theorem sAdeleSchwartzToGlobal_mem_polarSubspace (f : sAdelePolarSubspace F S) :
    sAdeleSchwartzToGlobal F S f.val ∈ adelePolarSubspace F := by sorry

open Classical in
/-- Paper: Corollary 7.2.2.2, p. 340.
On tests in the common kernel of the two zero evaluations, the global bound has
no exception. At the trivial character the local coefficient range shifts down
by one. The two principal-value images use inputs in the respective polar subspaces.
Deviation: The zero-order condition is a lower bound on meromorphic order. The
homogeneous theta classes of the restricted tests are represented in the ambient quotients. -/
theorem sLocalPolarPrincipalValue_tfae {S₀ : Finset Places} (h₀ : S₀ ⊆ S) (_hn : S₀.Nonempty)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F)))
    (χ : PontryaginDual C𝔽) (hχ : globalUnitary(χ) ∈ unramifiedOutside F S₀)
    (f : sAdelePolarSubspace F S) :
    let hS : globalUnitary(χ) ∈ unramifiedOutside F S := outsideS(h₀, hχ)
    let ω := globalNormOne(χ)
    let hω : NormOneCharacterUnramifiedOutside ω S := ⟨⟨globalUnitary(χ), hS⟩, fun _ ↦ rfl⟩
    let ωₛ := sLocalNormOneCharacter S ω hω
    let x := (Kₛ(ωₛ)).mkQ f.val
    let π := sLocalHomogeneousThetaToGlobal hω
    let Z := fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f.val) (ideleClassNormTwist χ s)
    List.TFAE [
      (∀ (c : Xₛ), onComponent(c, ωₛ) → 0 < sLocalFinitePoleMultiplicity S₀ c →
        let m := sLocalRhoPoleOrder c
        let n := sLocalFinitePoleMultiplicity S₀ c
        ∀ k : ℕ, (if c = 1 then m - n ≤ k ∧ k ≤ m - 1 else m - n < k ∧ k ≤ m) →
          sLocalPrincipalPartCoeff c k f.val = 0),
      (∀ s : ℂ, 0 < sLocalFinitePoleMultiplicity S₀ (localChart(χ, hS) s) →
        (sLocalFinitePoleMultiplicity S₀ (localChart(χ, hS) s) : WithTop ℤ) ≤ meromorphicOrderAt Z s),
      (∃ g : sAdelePolarSubspace F S, (Kₛ(ωₛ)).mkQ (sAdelePrincipalValue F h₀ g.val) = x),
      (∃ g : adelePolarSubspace F, (K𝔽(ω)).mkQ (adelePrincipalValue F S₀ g.val) = π x)
    ] := by sorry

end LocalPolesGlobalZeros

end RiemannMasullo
