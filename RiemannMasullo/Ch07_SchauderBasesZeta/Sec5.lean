module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec4

import all RiemannMasullo.AppA_AlgebraicNT.Sec3

/-! # §7.5 Strong co-primality -/

@[expose] public noncomputable section

open Function IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option Elab.async false

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "C₁" => (ideleClassNorm F).ker
local notation "ω(" χ ")" => (χ : U).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "P" => adelePolarSubspace F
local notation "K(" ω ")" => LinearMap.ker ((homogeneousAdelicThetaLinearMap F ω).domRestrict P)
local notation "B" => SchwartzBergman (univ : Set ℝ)

local instance instIdeleClassT2Sec5 : T2Space C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1

local instance instIdeleClassLocallyCompactSec5 : LocallyCompactSpace C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1

local instance instIdeleClassSecondCountableSec5 : SecondCountableTopology C𝔽 :=
  letI : SecondCountableTopology I𝔽 := idele_secondCountable F
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.1.secondCountableTopology

/-- Paper: Equation (7.5.0.2), p. 374.
The pole-free homogeneous theta space is the quotient of zero-moment tests
by the kernel of their homogeneous theta transform. -/
abbrev StrongCoprimalityThetaSpace (ω : PontryaginDual C₁) := ↥P ⧸ K(ω)

/-- Paper: Equation (7.5.0.2), p. 374.
The comparison space is the norm-one isotype of the full exponential-decay space. -/
abbrev StrongCoprimalityDecaySpace (ω : PontryaginDual C₁) :=
  ↥(modulatedDecayIsotype m𝔽 univ (mem_univ (0 : ℝ)) ω)

/-- Paper: Equation (7.5.0.2), p. 374.
The topological linear embedding takes a zero-moment test class to its homogeneous theta
function, viewed in the corresponding exponentially decaying isotype. -/
theorem exists_strongCoprimalityThetaEmbedding (ω : PontryaginDual C₁) :
    ∃ j : StrongCoprimalityThetaSpace ω →L[ℂ] StrongCoprimalityDecaySpace ω,
      IsEmbedding j ∧ ∀ (f : P) (g : C𝔽),
        (j ((K(ω)).mkQ f)).val.val g = homogeneousAdelicThetaLinearMap F ω f.val g := by sorry

/-- Paper: Theorem 7.5.0.1 and Equation (7.5.0.3), pp. 374–375.
The two zero moments are preserved by the finite principal-value operator. -/
theorem strongCoprimalityPrincipalValue_mem_polar (S : Finset V) (f : P) :
    adelePrincipalValue F S f.val ∈ P := by sorry

/-- Paper: Equation (7.5.0.3), p. 375.
The denominator is the image in homogeneous theta classes of principal values of
zero-moment tests. -/
def strongCoprimalityDenominator (ω : PontryaginDual C₁) (S : Finset V) :
    Submodule ℂ (StrongCoprimalityThetaSpace ω) :=
  Submodule.span ℂ (range fun f : P ↦
    (Submodule.Quotient.mk ⟨adelePrincipalValue F S f.val,
      strongCoprimalityPrincipalValue_mem_polar S f⟩ : StrongCoprimalityThetaSpace ω))

/-- Paper: Equation (7.5.0.3), p. 375.
The global orbital quotient carries the quotient topology of the pole-free theta space. -/
abbrev StrongCoprimalityQuotient (ω : PontryaginDual C₁) (S : Finset V) :=
  StrongCoprimalityThetaSpace ω ⧸ strongCoprimalityDenominator ω S

/-- Paper: Equation (7.5.0.3), p. 375.
A theta class represents zero in the quotient exactly when a principal-value test
represents that same theta class. -/
theorem strongCoprimalityQuotient_mk_eq_zero (ω : PontryaginDual C₁) (S : Finset V)
    (f : P) :
    (strongCoprimalityDenominator ω S).mkQ ((K(ω)).mkQ f) = 0 ↔
      ∃ g : P, (K(ω)).mkQ f = (K(ω)).mkQ
        ⟨adelePrincipalValue F S g.val, strongCoprimalityPrincipalValue_mem_polar S g⟩ :=
  by sorry

/-- Paper: Theorem 7.5.0.1, p. 374.
The class norm used for the comparison is the surjective modulation of §D.2. -/
theorem strongCoprimalityNorm_isModulation_surjective :
    IsModulation (m𝔽 : C𝔽 →ₜ* ℝ≥0ˣ) ∧ Surjective (m𝔽 : C𝔽 →ₜ* ℝ≥0ˣ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hsurj, _⟩ := ideleGroup_quotient.{_, 0} F
  exact ⟨⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩, hsurj⟩

/-- Paper: Theorem 7.5.0.1, pp. 374–375.
The comparison difference composes the operators that subtract translation by
each selected inverse uniformizer. -/
def strongCoprimalityDifference (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ) (f : C𝔽 → ℂ) : C𝔽 → ℂ :=
  S.toList.foldr (fun v h g ↦
    h g - h ((IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π v))⁻¹ * g)) f

/-- Paper: Theorem 7.5.0.1, pp. 374–375.
A single-place difference subtracts the inverse uniformizer translate pointwise. -/
theorem strongCoprimalityDifference_singleton_apply
    (π : (v : V) → (v.adicCompletion F)ˣ) (v : V) (f : C𝔽 → ℂ) (g : C𝔽) :
    strongCoprimalityDifference {v} π f g =
      f g - f ((IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π v))⁻¹ * g) := by sorry

section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
/-- Paper: Equation (7.5.0.1), p. 374.
The comparison uses the range of the full-interval difference product of §4.6. -/
def fullDecayDifferenceRange (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (ω : PontryaginDual m.toMonoidHom.ker) (gs : List G) :
    Submodule ℂ ↥(modulatedDecayIsotype m univ (mem_univ (0 : ℝ)) ω) :=
  (modulatedIsotypicDifferenceProduct m hm hms ω univ ordConnected_univ
    (mem_univ (0 : ℝ)) gs).toLinearMap.range

/-- Paper: Equation (7.5.0.1), p. 374.
The span of pointwise iterated differences is the range of the continuous product
on the full decay isotype. -/
theorem fullDecayDifferenceRange_eq_span (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
    (hms : Surjective m) (ω : PontryaginDual m.toMonoidHom.ker) (gs : List G) :
    let E := ↥(modulatedDecayIsotype m univ (mem_univ (0 : ℝ)) ω)
    fullDecayDifferenceRange m hm hms ω gs = Submodule.span ℂ
      {h : E | ∃ f : E, h.val.val =
        gs.foldr (fun a (u : G → ℂ) x ↦ u x - u (a * x)) f.val.val} := by sorry
end

/-- Paper: Equation (7.5.0.1), p. 374.
The comparison denominator is the submodule generated by differences of
exponentially decaying functions of the same isotype.
Specializing fullDecayDifferenceRange_eq_span to the class norm and the list
of inverse uniformizer classes recovers this formula by List.foldr_map. -/
def strongCoprimalityDifferenceRange (ω : PontryaginDual C₁) (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ) : Submodule ℂ (StrongCoprimalityDecaySpace ω) :=
  Submodule.span ℂ {h | ∃ f : StrongCoprimalityDecaySpace ω,
    h.val.val = strongCoprimalityDifference S π f.val.val}

/-- Paper: Equation (7.5.0.1), p. 374.
Each element of the comparison denominator is a single iterated difference
of an exponentially decaying function in the given isotype. -/
theorem mem_strongCoprimalityDifferenceRange (ω : PontryaginDual C₁) (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ) (h : StrongCoprimalityDecaySpace ω) :
    h ∈ strongCoprimalityDifferenceRange ω S π ↔
      ∃ f : StrongCoprimalityDecaySpace ω,
        h.val.val = strongCoprimalityDifference S π f.val.val := by sorry

open Classical in
/-- Paper: Theorem 7.5.0.1, p. 374.
The map induced by homogeneous theta is a topological linear isomorphism from the Weil
principal-value quotient to the exponential-decay quotient.
Deviation: The comparison product uses the unramified places of the selected set.
At a ramified place Weil principal value acts as the identity on this isotype. -/
theorem strongCoprimality (χ : U) (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ)
    (_hπ : ∀ v ∈ S, Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val) :
    let ω := ω(χ)
    let j := (exists_strongCoprimalityThetaEmbedding ω).choose
    let D := strongCoprimalityDenominator ω S
    let T := S.filter (fun v ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    let E := strongCoprimalityDifferenceRange ω T π
    ∃ e : (StrongCoprimalityThetaSpace ω ⧸ D) ≃L[ℂ] (StrongCoprimalityDecaySpace ω ⧸ E),
      ∀ x : StrongCoprimalityThetaSpace ω,
        e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (j x) := by sorry

open Classical in
/-- Paper: Equation (7.5.0.4), p. 375.
Adding one place shrinks the image of principal value, so its image is a submodule
of the image for the original set of places. -/
theorem strongCoprimalityDenominator_insert_le (ω : PontryaginDual C₁) (S : Finset V) (v : V) :
    strongCoprimalityDenominator ω (insert v S) ≤ strongCoprimalityDenominator ω S := by sorry

open Classical in
/-- Paper: Equation (7.5.0.4), p. 375.
The layer for one added place is the quotient of the current principal-value image
by the image after applying principal value at that place as well. -/
abbrev StrongCoprimalityLayer (ω : PontryaginDual C₁) (S : Finset V) (v : V) :=
  let D := strongCoprimalityDenominator ω S
  D ⧸ (strongCoprimalityDenominator ω (insert v S)).comap D.subtype

open Classical in
/-- Paper: Equation (7.5.0.4), p. 375.
A vector in the current principal-value image vanishes in the layer exactly when it
belongs to the image after adding the new place. -/
theorem strongCoprimalityLayer_mk_eq_zero (ω : PontryaginDual C₁) (S : Finset V) (v : V)
    (x : strongCoprimalityDenominator ω S) :
    (Submodule.Quotient.mk x : StrongCoprimalityLayer ω S v) = 0 ↔
      x.val ∈ strongCoprimalityDenominator ω (insert v S) := by sorry

-- TODO(paper-gap): The references to (8.1.0.4), (8.1.0.5), (8.1.0.7), and
-- (8.1.0.8) in the proof point to local formulas (7.5.0.5), (7.5.0.6),
-- (7.5.0.7), and (7.5.0.11), respectively.

-- TODO(paper-gap): In the injectivity argument on pp. 375–376 the pulled-back
-- functionals must separate the source quotient. A biorthogonal family alone
-- gives no such separation. In theta space H with comparison map j the required
-- identity is j⁻¹(range Δ) = PV(H), for the product on the unramified places.

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))

/-- Paper: Equation (7.5.0.8), p. 377.
The reflected Fourier jet is the derivative evaluation of the global Mellin transform at
the original spectral point, with the sign from reflection in odd orders.
Deviation: The functional is on the zero-moment quotient from (7.5.0.1), where the
global Mellin transform is entire. -/
def strongCoprimalityFourierJet (s : ℂ) (k : ℕ) : StrongDual ℂ (StrongCoprimalityThetaSpace (ω(χ))) :=
  (-1 : ℂ) ^ k • ((entireJet s k).comp
    (schwartzBergmanEntireInclusion.comp (exists_globalPolarThetaMellin χ τ hτ).choose))

/-- Paper: Equation (7.5.0.8), p. 377.
On a zero-moment representative, the reflected jet evaluates the k-th complex derivative
of the Fourier-transformed global zeta function at 1 − s. This zeta function is entire.
Deviation: Entireness uses the two zero moments, which the Fourier transform exchanges. -/
theorem strongCoprimalityFourierJet_mk (s : ℂ) (k : ℕ) (f : P) :
    let Z := fun z ↦ globalIdelicZFunction (adeleSchwartzFourier f.val)
      (ideleClassNormTwist χ⁻¹ z)
    Differentiable ℂ Z ∧
      strongCoprimalityFourierJet χ τ hτ s k ((K(ω(χ))).mkQ f) = iteratedDeriv k Z (1 - s) := by sorry

/-- Paper: Equation (7.5.0.8), p. 377.
At each regular center on the imaginary axis the reflected jet is defined on
the full homogeneous theta space and restricts to the jet on polar tests.
Deviation: The trivial quasi-character is the exceptional center on this axis. -/
theorem exists_strongCoprimalityFourierJet_full (s : ℂ) (_hs : s.re = 0)
    (_hc : ideleClassNormTwist χ s ≠ 1) (k : ℕ) :
    let q := (LinearMap.ker (homogeneousAdelicThetaLinearMap F (ω(χ)))).mkQ
    ∃ d : StrongDual ℂ (GlobalHomogeneousThetaSpace F (ω(χ))),
      (∀ f : SchwartzBruhat (Multiplicative (𝔸[F])),
        let Z := fun z ↦ globalIdelicZFunction (adeleSchwartzFourier f)
          (ideleClassNormTwist χ⁻¹ z)
        AnalyticAt ℂ Z (1 - s) ∧ d (q f) = iteratedDeriv k Z (1 - s)) ∧
      ∀ f : P, d (q f.val) =
        strongCoprimalityFourierJet χ τ hτ s k ((K(ω(χ))).mkQ f) := by sorry

-- In the proof on pp. 376–377 one can enlarge S to contain the primes of
-- the different and all places above each rational prime occurring in S
-- (saturation in §7.3). Then the outside indicators are self-dual and
-- the outside unit masses are one. The local-to-global quotient in (7.5.0.16)
-- itself only needs the hypotheses in its statement below.

/-- Paper: Equation (7.5.0.13), p. 378.
Multiplication by a factor holomorphic at the reflected point acts on unnormalized
derivatives by an upper-triangular binomial matrix. For the regular blocks the
factor is the outside Euler product of the conjugate character when S contains
all primes of the different. Both sets of raw derivatives here use the reflected variable.
Deviation: A block of size N has indices 0 through N − 1, as in (7.5.0.11). -/
def strongCoprimalityJetMatrix (S : Finset V)
    (hS : ideleClassNormTwist χ⁻¹ 0 ∈ unramifiedOutside F S) (s : ℂ)
    (_hL : AnalyticAt ℂ (heckeEulerProductOutside S χ⁻¹ hS) (1 - s)) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  let L := heckeEulerProductOutside S χ⁻¹ hS
  fun m k ↦
    if m ≤ k then (k.val.choose m.val : ℂ) * iteratedDeriv (k.val - m.val) L (1 - s) else 0

/-- Paper: Equation (7.5.0.13), p. 378.
The diagonal entries of the derivative matrix are the value of the multiplier at the
reflected point, so the determinant is that value raised to the block size. -/
theorem strongCoprimalityJetMatrix_det (S : Finset V)
    (hS : ideleClassNormTwist χ⁻¹ 0 ∈ unramifiedOutside F S) (s : ℂ)
    (hL : AnalyticAt ℂ (heckeEulerProductOutside S χ⁻¹ hS) (1 - s)) (N : ℕ) :
    (strongCoprimalityJetMatrix χ S hS s hL N).det =
      heckeEulerProductOutside S χ⁻¹ hS (1 - s) ^ N := by sorry

/-- Paper: Equation (7.5.0.13), p. 378.
The regular block is invertible at a spectral point on the imaginary axis.
Deviation: At the exceptional pole of a norm twist the regular-block hypothesis fails. -/
theorem strongCoprimalityJetMatrix_det_ne_zero (S : Finset V)
    (hS : ideleClassNormTwist χ⁻¹ 0 ∈ unramifiedOutside F S) (s : ℂ) (_hs : s.re = 0)
    (hL : AnalyticAt ℂ (heckeEulerProductOutside S χ⁻¹ hS) (1 - s)) (N : ℕ) :
    (strongCoprimalityJetMatrix χ S hS s hL N).det ≠ 0 := by sorry

local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)

/-- Paper: Remark 7.5.0.2 and Equation (7.5.0.15), p. 378.
At the places above one rational prime the denominator agrees with the
primary denominator of §7.4. -/
theorem strongCoprimalityDenominator_primary (p : Vℚ) :
    let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    strongCoprimalityDenominator (ω(χ)) T = finiteNuclearityDenominator χ p := by sorry

/-- Paper: Remark 7.5.0.2 and Equation (7.5.0.15), p. 378.
The primary principal-value quotient is a Hausdorff nuclear Fréchet space. -/
theorem strongCoprimalityPrimaryQuotient_nuclearFrechet (ω : PontryaginDual C₁) (p : Vℚ) :
    let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    IsFrechetTVS (StrongCoprimalityQuotient ω T) ∧ IsNuclearTVS (StrongCoprimalityQuotient ω T) := by sorry

section SLocal

variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Pₛ" => sAdelePolarSubspace F S
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "Kₛ(" η ")" => LinearMap.ker ((sLocalHomogeneousAdelicThetaLinearMap F S η).domRestrict Pₛ)

local notation "twistₛ" => quasiCharacterNormTwist (sIdeleQuotientNorm F S)
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "dualₛ" => dualQuasiCharacter (sIdeleQuotientNorm F S)
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "insertPolar(" f ")" => (⟨sAdeleSchwartzToGlobal F S (f : Pₛ).val,
  sAdeleSchwartzToGlobal_mem_polarSubspace f⟩ : P)

/-- Paper: Equations (7.5.0.8)–(7.5.0.13), pp. 377–378.
On an inserted polar test, the regular change of coordinates uses the Fourier
functionals of §7.3 and their signs from differentiation before reflection.
Deviation: Taking S to contain all primes of the different makes the outside
insertion self-dual and gives every outside unit group mass one. -/
theorem strongCoprimalityFourierJet_toGlobal {T : Finset V} (_hT : T ⊆ S)
    {η : PontryaginDual J₁} (j : SLocalOrbitalIndex (F := F) (S := S) T η)
    (s : ℂ) (hS : ideleClassNormTwist χ⁻¹ 0 ∈ unramifiedOutside F S)
    (_hgood : ∀ v : V, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (_hc : dualₛ j.val.1 = twistₛ (sIdeleRestriction F S ⟨ideleClassNormTwist χ⁻¹ 0, hS⟩) (1 - s))
    (hL : AnalyticAt ℂ (heckeEulerProductOutside S χ⁻¹ hS) (1 - s)) (f : Pₛ) :
    let k := j.val.2
    let idx (i : Fin (k + 1)) : SLocalOrbitalIndex (F := F) (S := S) T η :=
      ⟨(j.val.1, i.val), j.property.1, lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) j.property.2⟩
    let x := (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S η)).mkQ f.val
    let A := strongCoprimalityJetMatrix χ S hS s hL (k + 1)
    strongCoprimalityFourierJet χ τ hτ s k ((K(ω(χ))).mkQ insertPolar(f)) =
      ∑ i : Fin (k + 1), (-1 : ℂ) ^ i.val *
        sLocalOrbitalFourierJet (F := F) (S := S) (T := T) (ω := η) (idx i) x *
          A i (Fin.last k) := by sorry

/-- Paper: Equations (7.5.0.9)–(7.5.0.14), pp. 377–378.
At a simple pole r of the outside factor L, write H for the holomorphic extension
of (z − r)L(z). The local zeta function A of the Fourier-transformed polar test vanishes at r.
The k-th global derivative uses local derivatives of orders 1 through k + 1.
Deviation: This is the pole-cancelled Leibniz rule at the exceptional point. -/
theorem strongCoprimalityFourierJet_toGlobal_at_pole (s : ℂ)
    (hS : ideleClassNormTwist χ⁻¹ 0 ∈ unramifiedOutside F S)
    (_hgood : ∀ v : V, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (_hpole : meromorphicOrderAt (heckeEulerProductOutside S χ⁻¹ hS) (1 - s) = -1)
    (f : Pₛ) (k : ℕ) :
    let r := 1 - s
    let H := toMeromorphicNFOn (fun z ↦ (z - r) * heckeEulerProductOutside S χ⁻¹ hS z) univ
    let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ⁻¹ 0, hS⟩
    let A := fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f.val) (twistₛ c z)
    AnalyticAt ℂ H r ∧ H r ≠ 0 ∧ AnalyticAt ℂ A r ∧ A r = 0 ∧
      strongCoprimalityFourierJet χ τ hτ s k ((K(ω(χ))).mkQ insertPolar(f)) =
        ∑ m ∈ Finset.range (k + 1), (k.choose m : ℂ) * iteratedDeriv (k - m) H r *
          (iteratedDeriv (m + 1) A r / (m + 1 : ℂ)) := by sorry

-- TODO(paper-gap): The basis in §7.3 is for unrestricted local tests. On the
-- polar quotient its order-zero Fourier functional at the exceptional point
-- vanishes. To use that basis in (7.5.0.14), identify a basis of the polar
-- quotient with the shifted orders above (or use another surjectivity proof).

/-- Paper: Remark 7.5.0.2 and Equation (7.5.0.16), p. 378.
The local principal-value operator preserves the common kernel of the two local polar moments. -/
theorem strongCoprimalityLocalPrincipalValue_mem_polar {T : Finset V} (hT : T ⊆ S) (f : Pₛ) :
    sAdelePrincipalValue F hT f.val ∈ Pₛ := by sorry

/-- Paper: Remark 7.5.0.2 and Equations (7.5.0.15)–(7.5.0.16), pp. 378–379.
Insertion of the outside integer indicators gives the primary quotient isomorphism
once the norm-one character is unramified outside S and the S-integer Picard group is trivial.
Deviation: S includes the selected primary places. The denominator uses the same S-adelic
space as the numerator, with all archimedean places implicit. -/
theorem strongCoprimalityPrimaryQuotient_local_equiv (ω : PontryaginDual C₁) (p : Vℚ)
    (hp : (finite_nuclearityPlacesAbove (F := F) p).toFinset ⊆ S)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hω : NormOneCharacterUnramifiedOutside ω S) :
    let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    let η : PontryaginDual J₁ := sLocalNormOneCharacter S ω hω
    let Dₛ := Submodule.span ℂ (range fun f : Pₛ ↦
      (Submodule.Quotient.mk ⟨sAdelePrincipalValue F hp f.val,
        strongCoprimalityLocalPrincipalValue_mem_polar hp f⟩ : ↥Pₛ ⧸ Kₛ(η)))
    let D := strongCoprimalityDenominator ω T
    ∃ e : ((↥Pₛ ⧸ Kₛ(η)) ⧸ Dₛ) ≃L[ℂ] (StrongCoprimalityThetaSpace ω ⧸ D),
      ∀ f : Pₛ, e (Dₛ.mkQ ((Kₛ(η)).mkQ f)) = D.mkQ ((K(ω)).mkQ
        ⟨sAdeleSchwartzToGlobal F S f.val, sAdeleSchwartzToGlobal_mem_polarSubspace f⟩) := by sorry

end SLocal

/-- Paper: Remark 7.5.0.2, p. 379.
The primary quotient is a closed subspace of a Hausdorff quotient of a finite product
of smooth periodic spaces, expressed via their rapidly decreasing Fourier sequences. -/
theorem strongCoprimalityPrimaryQuotient_sequence_subquotient (ω : PontryaginDual C₁) (p : Vℚ) :
    let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    let E := Fin T.card → RapidDecaySequence 1
    ∃ (D : Submodule ℂ E) (W : Submodule ℂ (E ⧸ D)),
      IsClosed (D : Set E) ∧ IsClosed (W : Set (E ⧸ D)) ∧
        Nonempty (StrongCoprimalityQuotient ω T ≃L[ℂ] W) := by sorry

-- TODO(prerequisite): The separate Köthe-space assertion requires a general
-- Köthe-space model. The example in §C.1.5, p. 667 is unfinished.

/-- Paper: Remark 7.5.0.2, p. 379.
The strong dual of the primary quotient is a Hausdorff quotient of a closed subspace
of the strong dual of the finite product of rapidly decreasing sequence spaces.
Deviation: The ambient sequence spaces on the dual side are strong duals. -/
theorem strongCoprimalityPrimaryQuotient_strongDual_subquotient (ω : PontryaginDual C₁) (p : Vℚ) :
    let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    let E := StrongDual ℂ (Fin T.card → RapidDecaySequence 1)
    ∃ (W : Submodule ℂ E) (D : Submodule ℂ W),
      IsClosed (W : Set E) ∧ IsClosed (D : Set W) ∧
        Nonempty (StrongDual ℂ (StrongCoprimalityQuotient ω T) ≃L[ℂ] (W ⧸ D)) := by sorry

-- TODO(later): needs §8.1 for the orbital-support and support-constrained basis claims
-- announced on p. 374 and at the start of Chapter 8 on p. 381.

open Classical in
/-- Paper: Corollary 7.5.0.3 and Equation (7.5.0.17), p. 379.
Every entire Schwartz–Bergman function is the sum of an entire multiple of the
regularized completed Hecke function and an Euler polynomial times another
Schwartz–Bergman function. The first summand is itself Schwartz–Bergman.
The sign converts the pole polynomial of §7.1.4 to the convention in (7.5.0.17). -/
theorem strongCoprimality_bezout (S : Finset V)
    (_hS : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) (φ : B) :
    let L := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
      (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
    ∃ (u : entireContinuousMapSubalgebra) (v w : B),
      (∀ s : ℂ, w.val s = (-1 : ℂ) ^ δ * L.val s * u.val s) ∧
      ∀ s : ℂ, w.val s + reciprocalPartialHeckeEulerProduct χ S s * v.val s = φ.val s := by sorry

end RiemannMasullo
