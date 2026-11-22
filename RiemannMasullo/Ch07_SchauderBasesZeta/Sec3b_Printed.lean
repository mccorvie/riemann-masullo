module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b

/-! # False printed PW-level claims in §7.3.2–7.3.3 -/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain NumberField Set Topology
open scoped BigOperators NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 600000
set_option Elab.async false

local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "m(" F ", " T ")" => sIdeleQuotientNorm F T
local notation "J₁(" F ", " T ")" => (m(F, T)).ker
local notation "Θ(" F ", " T ", " χ ")" => SLocalHomogeneousThetaSpace F T χ
local notation "q(" F ", " T ", " χ ")" =>
  (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F T χ)).mkQ
local notation "size(" P ")" => (∏ v ∈ P, (v.asIdeal.absNorm : ℝ))
local notation "count(" F ", " S ")" => (Fintype.card (InfinitePlace F) + Finset.card S)
local notation "unitTests(" F ", " S ", " T ", " h ", " K ")" =>
  (sLocalPWTests h K).map (sAdelePrincipalValue F (Finset.sdiff_subset : T \ S ⊆ T))
local notation "unitLevel(" F ", " S ", " T ", " h ", " K ", " D ", " χ ")" =>
  ((unitTests(F, S, T, h, K) ⊓ D).map (q(F, T, χ))).topologicalClosure
local notation "zeroMoments(" F ", " T ")" => sAdelePolarSubspace F T

local notation "B(" F ", " S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "unitPV(" F ", " S ", " T ")" =>
  sAdelePrincipalValue F (Finset.sdiff_subset : T \ S ⊆ T)

/-- Paper: Equations (7.3.2.2) and (7.3.2.13), pp. 351, 355.
On a test at either level the cited transition is asserted to insert unit indicators. -/
def Printed.sLocalPWTransition_eq_units : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ → Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (hST : S ⊆ T) (X : ℝ), 0 < X →
      ∀ K ∈ ({sLocalPWBox S X, sLocalPWProductRegion S X} : Set (Set (SAdeleRing F S))),
        ∀ f : B(F, S), HasCompactSupport (sAdeleSchwartzFourier f).val →
          tsupport (sAdeleSchwartzFourier f).val ⊆ Multiplicative.toAdd ⁻¹' K →
          sAdeleSchwartzTransition F hST f = unitPV(F, S, T) (sAdeleSchwartzTransition F hST f)

/-- Paper: Equations (7.3.2.2) and (7.3.2.13), pp. 351, 355.
Over the rationals add one prime and choose an inverse Fourier bump with positive
integral. At the zero tuple integer insertion gives its nonzero value at zero,
while unit insertion gives zero. -/
theorem Printed.sLocalPWTransition_eq_units_false : ¬ Printed.sLocalPWTransition_eq_units := by sorry

/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
Inside each printed test level the common kernel of the two evaluations has codimension two. -/
def Printed.sLocalPWTests_twoMoments : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ → Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (hST : S ⊆ T) (X : ℝ), 0 < X →
      ∀ K ∈ ({sLocalPWBox S X, sLocalPWProductRegion S X} : Set (Set (SAdeleRing F S))),
        let E := unitTests(F, S, T, hST, K)
        Module.finrank ℂ (E ⧸ (zeroMoments(F, T)).comap E.subtype) = 2

/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
For one added rational prime every inserted test vanishes at zero, so at most
one independent moment remains on the test space. -/
theorem Printed.sLocalPWTests_twoMoments_false : ¬ Printed.sLocalPWTests_twoMoments := by sorry

/-- Paper: Proposition 7.3.2.2(1), p. 352, with Definition 7.3.2.1, p. 351.
The absolute levels formed with the printed unit factors exhaust the homogeneous
theta space sequentially, both for unrestricted and for zero-moment tests. Applying
principal value to the inserted integer indicators realizes the printed unit factors. -/
def Printed.sLocalAbsolutePW_seqDense : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ →
    Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (ω : PontryaginDual (ideleClassNorm F).ker)
      (hu : NormOneCharacterUnramifiedOutside ω S),
      ∀ (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
        χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      ∀ (D : Submodule ℂ (SchwartzBruhat (Multiplicative (SAdeleRing F T)))),
        (D = ⊤ ∨ D = zeroMoments(F, T)) →
        ∀ x : Θ(F, T, χ), x ∈ D.map (q(F, T, χ)) →
          ∃ u : ℕ → Θ(F, T, χ),
            (∀ n, ∃ X > 0, u n ∈ unitLevel(F, S, T, hST, sLocalPWBox S X, D, χ)) ∧
            Tendsto u atTop (𝓝 x)

/-- Paper: Proposition 7.3.2.2(1), p. 352, with Definition 7.3.2.1, p. 351.
Take F = ℚ, S = {∞}, S₀ = {p}, and the trivial character. All inserted tests
vanish near 0 at p, so their Mellin transforms have no pole at 2πi/log p.
The residue there is continuous and is nonzero on the Gaussian tensored with
the integer-ring indicator, whose Mellin transform contains (1 − p^(-s))⁻¹. -/
theorem Printed.sLocalAbsolutePW_seqDense_false : ¬ Printed.sLocalAbsolutePW_seqDense := by sorry

/-- Paper: Proposition 7.3.2.4(1), pp. 355–356, with Definition 7.3.2.3, p. 355.
The invariant levels formed with the printed unit factors exhaust the homogeneous
theta space sequentially, both for unrestricted and for zero-moment tests. Applying
principal value to the inserted integer indicators realizes the printed unit factors. -/
def Printed.sLocalInvariantPW_seqDense : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ →
    Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (ω : PontryaginDual (ideleClassNorm F).ker)
      (hu : NormOneCharacterUnramifiedOutside ω S),
      ∀ (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
        χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      ∀ (D : Submodule ℂ (SchwartzBruhat (Multiplicative (SAdeleRing F T)))),
        (D = ⊤ ∨ D = zeroMoments(F, T)) →
        ∀ x : Θ(F, T, χ), x ∈ D.map (q(F, T, χ)) →
          ∃ u : ℕ → Θ(F, T, χ),
            (∀ n, ∃ X > 0, u n ∈ unitLevel(F, S, T, hST, sLocalPWProductRegion S X, D, χ)) ∧
            Tendsto u atTop (𝓝 x)

/-- Paper: Proposition 7.3.2.4(1), pp. 355–356, with Definition 7.3.2.3, p. 355.
Take F = ℚ, S = {∞}, S₀ = {p}, and the trivial character. All inserted tests
vanish near 0 at p, so their Mellin transforms have no pole at 2πi/log p.
The residue there is continuous and is nonzero on the Gaussian tensored with
the integer-ring indicator, whose Mellin transform contains (1 − p^(-s))⁻¹. -/
theorem Printed.sLocalInvariantPW_seqDense_false : ¬ Printed.sLocalInvariantPW_seqDense := by sorry

/-- Paper: Discussion after Proposition 7.3.2.2(4), p. 354.
The closed zero-moment absolute level is said to have codimension two in the full level. -/
def Printed.sLocalAbsolutePW_zeroMoment_codim : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ → Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (ω : PontryaginDual (ideleClassNorm F).ker) (hu : NormOneCharacterUnramifiedOutside ω S)
      (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
      χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      ∀ X > (0 : ℝ),
        let K := sLocalPWBox S X
        let W := unitLevel(F, S, T, hST, K, ⊤, χ)
        let W₀ := unitLevel(F, S, T, hST, K, zeroMoments(F, T), χ)
        Module.finrank ℂ (W ⧸ W₀.comap W.subtype) = 2

/-- Paper: Discussion after Proposition 7.3.2.2(4), p. 354.
Take the quadratic character modulo five over the rationals at the stage with infinity and
five, with no added places. Translation by the local unit two preserves the test band and
the moments and acts by minus one on the theta quotient. Half the difference from the
translate represents the same class and has both moments zero. The two levels coincide. -/
theorem Printed.sLocalAbsolutePW_zeroMoment_codim_false :
    ¬ Printed.sLocalAbsolutePW_zeroMoment_codim := by sorry

/-- Paper: Proposition 7.3.3.2, pp. 357–358.
The diagram of inclusions and restrictions of the continuous ambient PV operator
commutes at the printed cutoffs and is equivariant for the large-norm semigroup.
The containments define the restrictions, so both paths have the same ambient value. -/
def Printed.sLocalPW_principalValue_diagram : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T R : Finset (V(F))),
    T = S ∪ S₀ →
    Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ → R ⊆ S₀ → IsSaturatedPlaceSet (F := F) R →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (ω : PontryaginDual (ideleClassNorm F).ker)
      (hu : NormOneCharacterUnramifiedOutside ω S) (X Y : ℝ),
      0 < X → 0 < Y → X ^ count(F, S) ≤ Y →
      ∀ (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
        χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      ∀ hRT : R ⊆ T,
        let D := zeroMoments(F, T)
        let H₀ := D.map (q(F, T, χ))
        let a := unitLevel(F, S, T, hST, sLocalPWBox S X, D, χ)
        let b := unitLevel(F, S, T, hST, sLocalPWProductRegion S Y, D, χ)
        let a' := unitLevel(F, S, T, hST, sLocalPWBox S (size(R) * X), D, χ)
        let b' := unitLevel(F, S, T, hST, sLocalPWProductRegion S (size(R) * Y), D, χ)
        let P := sLocalHomogeneousThetaPrincipalValue (F := F) hRT χ
        let A := (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T) χ).exists.choose
        a ≤ b ∧ b ≤ H₀ ∧ a' ≤ b' ∧ b' ≤ H₀ ∧
        a.map P ≤ a' ∧ b.map P ≤ b' ∧ H₀.map P ≤ H₀ ∧
        ∀ g : SIdeleQuotient F T, 1 ≤ ((m(F, T) g).val : ℝ) →
          (∀ E ∈ ({a, b, a', b', H₀} : Set (Submodule ℂ (Θ(F, T, χ)))),
            ∀ x ∈ E, A g x ∈ E) ∧ ∀ x ∈ H₀, P (A g x) = A g (P x)

/-- Paper: Proposition 7.3.3.2, pp. 357–358.
Take F = ℚ, S = {∞, 2, 3}, S₀ = R = {5}, trivial character, X = 4 and Y = 64.
At the bottom absolute level 20 use a Fourier test supported at finite norms 16 and 9
and in a small even real neighborhood of ±19, with zero integral and nonzero value at 19.
Its inserted Fourier theta is nonzero at the idele (19, 1/16, 1/9, 1), of norm 2736,
whereas the bottom invariant level has Fourier theta supported in norms at most
5 · 320 = 1600, since the Fourier transform of the 5-unit indicator is supported in
5⁻¹ℤ₅. At the stated idele the only contributing S'-units are ±1. -/
theorem Printed.sLocalPW_principalValue_diagram_false :
    ¬ Printed.sLocalPW_principalValue_diagram := by sorry

local notation "primary(" F ", " T ", " p ")" => sLocalPrimaryPlaces (F := F) T p

/-- Paper: Definition 7.3.3.3(1)–(2), p. 359.
Both printed quotients require the primary principal-value image of the given
zero-moment level to lie inside the level divided by the product of residue sizes. -/
def Printed.sLocalPWOrbitalQuotients_defined : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ →
    IsSaturatedPlaceSet (F := F) S → Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (p : Vℚ) (ω : PontryaginDual (ideleClassNorm F).ker)
      (hu : NormOneCharacterUnramifiedOutside ω S) (X Y : ℝ),
      0 < X → 0 < Y →
      ∀ (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
        χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      let P := primary(F, T, p)
      P.Nonempty → P ⊆ S₀ →
        let PV := sLocalHomogeneousThetaPrincipalValue (sLocalPrimaryPlaces_subset (F := F) T p) χ
        let D := zeroMoments(F, T)
        (unitLevel(F, S, T, hST, sLocalPWBox S X, D, χ)).map PV ≤
          unitLevel(F, S, T, hST, sLocalPWBox S (X / size(P)), D, χ) ∧
        (unitLevel(F, S, T, hST, sLocalPWProductRegion S Y, D, χ)).map PV ≤
          unitLevel(F, S, T, hST, sLocalPWProductRegion S (Y / size(P)), D, χ)

/-- Paper: Definition 7.3.3.3(1)–(2), p. 359.
Take F = ℚ, S = {∞}, S₀ = {p}, and the trivial character. Take an even smooth Fourier
test h supported near ±ξ with X/p < ξ < X, h(ξ) ≠ 0 and integral zero.
The principal value replaces the base test f by f(x) − f(px). Its Fourier transform
is h(t) − h(t/p)/p. At the idele with real coordinate pξ and finite coordinate 1
the Fourier theta of the resulting unit-indicator tensor is nonzero, while any member
of the printed target level has Fourier theta supported in norms at most X. -/
theorem Printed.sLocalPWOrbitalQuotients_defined_false :
    ¬ Printed.sLocalPWOrbitalQuotients_defined := by sorry

local notation "Rₚ(" F ", " T ", " p ", " χ ")" =>
  sLocalPrimaryOrbitalSubmodule (F := F) (S := T) p χ
local notation "Iₚ(" F ", " T ", " p ", " χ ")" =>
  SLocalOrbitalIndex (F := F) (S := T) (primary(F, T, p)) χ

/-- Paper: Theorem 7.3.3.4(1)–(2), pp. 360–361.
The restricted dual basis and the lifts of its ambient biorthogonals share this enumeration. -/
def Printed.HasPWOrbitalBases {H : Type*} [AddCommGroup H] [Module ℂ H]
    [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℂ H]
    (R W : Submodule ℂ H) (K : Submodule ℂ W)
    (L : ℕ → StrongDual ℂ H) : Prop :=
  ∃ (e : ℕ → (H ⧸ R)) (d : ℕ → StrongDual ℂ (H ⧸ R))
    (eW : ℕ → (W ⧸ K)) (dW : ℕ → StrongDual ℂ (W ⧸ K))
    (ev : ℕ → StrongDual ℂ (StrongDual ℂ (W ⧸ K))),
    (∀ n (x : H), d n (R.mkQ x) = L n x) ∧ IsSchauderBasis e d ∧
    (∀ n (x : W), dW n (K.mkQ x) = L n x.val) ∧
    (∀ n, ∃ x : W, K.mkQ x = eW n ∧ R.mkQ x.val = e n) ∧
    (∀ n ℓ, ev n ℓ = ℓ (eW n)) ∧
    IsSchauderBasis dW ev ∧ SchauderBasis.IsUnconditional dW ev ∧
    IsSchauderBasis eW dW ∧ SchauderBasis.IsAbsolute eW dW

/-- Paper: Theorem 7.3.3.4(1)–(2), pp. 360–361.
For both printed quotient levels every enumeration of either restricted family gives an
unconditional strong-dual basis, and the ambient biorthogonals lift to an absolute basis.
The containment expresses existence of the quotients in (7.3.3.5)–(6). In (7.3.3.7)
the small-stage multiplicity counts contributing places in S, and the Laurent subscript
is the signed exponent of Definition 7.1.2.1. -/
def Printed.sLocalPWOrbital_bases : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ → Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (p : Vℚ) (ω : PontryaginDual (ideleClassNorm F).ker)
      (hu : NormOneCharacterUnramifiedOutside ω S)
      (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
      χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      let P := primary(F, T, p)
      P.Nonempty → P ⊆ S₀ →
      let pv := sLocalHomogeneousThetaPrincipalValue (sLocalPrimaryPlaces_subset (F := F) T p) χ
      let D := zeroMoments(F, T)
      let H := Θ(F, T, χ)
      let R := Rₚ(F, T, p, χ)
      ∃ B > (0 : ℝ), ∀ (X Y : ℝ), B ≤ X → B ≤ Y → X ^ count(F, S) ≤ Y →
        ∀ (W U : Submodule ℂ H),
          ((W = unitLevel(F, S, T, hST, sLocalPWBox S (X / size(P)), D, χ) ∧
            U = unitLevel(F, S, T, hST, sLocalPWBox S X, D, χ)) ∨
           (W = unitLevel(F, S, T, hST, sLocalPWProductRegion S (Y / size(P)), D, χ) ∧
            U = unitLevel(F, S, T, hST, sLocalPWProductRegion S Y, D, χ))) →
          U.map pv ≤ W ∧
          let K := (U.map pv).comap W.subtype
          let mS := fun c ↦ (sLocalArchPolePlaces (F := F) (S := T) c).card +
            sLocalFinitePoleMultiplicity (F := F) (S := T) S c
          ∀ fourier : Bool, ∃ L : Iₚ(F, T, p, χ) → StrongDual ℂ H,
            (∀ (j : Iₚ(F, T, p, χ)) (f : B(F, T)), L j (q(F, T, χ) f) =
              if fourier then sLocalOrbitalFourierJet (F := F) (S := T) j (q(F, T, χ) f)
              else sLocalZLaurentCoeff (F := F) (S := T) f j.val.1
                ((mS j.val.1 : ℤ) - (j.val.2 : ℤ))) ∧
            ∀ σ : ℕ ≃ Iₚ(F, T, p, χ), Printed.HasPWOrbitalBases R W K (L ∘ σ)

/-- Paper: Theorem 7.3.3.4(1)–(2), pp. 360–361.
Over the rationals with one added prime and trivial character, the index contains the
order-zero jet at the trivial center. It evaluates the Fourier zeta integral at norm
power one, a nonzero multiple of evaluation at zero by Fourier inversion. Its restriction
vanishes on each zero-moment level, contradicting the unit biorthogonal pairing.
The same obstruction persists with the proof's intersection denominator. -/
theorem Printed.sLocalPWOrbital_bases_false : ¬ Printed.sLocalPWOrbital_bases :=
  by sorry

local notation "lexLe(" e ", " a ", " b ")" =>
  ((∀ i, a (e i).val = b (e i).val) ∨
    ∃ i, a (e i).val < b (e i).val ∧ ∀ j < i, a (e j).val = b (e j).val)

/-- Paper: Notation 7.3.4.1, p. 364.
The printed lexicographic orders on the real and complex cutoff tuples make
the no-pole spaces a decreasing filtration. -/
def Printed.sLocalGammaFiltration_antitone : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (V(F)))
    (χ : PontryaginDual J₁(F, S)) (r₁ r₂ : ℕ)
    (realPlaces : Fin r₁ ≃ {w : InfinitePlace F // w.IsReal})
    (complexPlaces : Fin r₂ ≃ {w : InfinitePlace F // w.IsComplex})
    (a b : InfinitePlace F → ℕ),
    lexLe(realPlaces, a, b) → lexLe(complexPlaces, a, b) →
      sLocalGammaFiltration χ b ≤ sLocalGammaFiltration χ a

/-- Paper: Notation 7.3.4.1, p. 364.
For F = ℚ(√2) and the trivial character on the archimedean stage, (0,2) is
lexicographically below (1,0). Both real places have the poles of Γℝ. Apply
the Euler differential polynomial s²(s+2)² in the Mellin variable to the
product Gaussian. Its double pole at −4 remains, while the poles at 0 and
−2 are canceled. Its class is in the stage (1,0) and outside (0,2). -/
theorem Printed.sLocalGammaFiltration_antitone_false :
    ¬ Printed.sLocalGammaFiltration_antitone := by sorry

/-- Paper: Theorem 7.3.4.1(2), pp. 364–365.
On the signed Laurent convention of Definition 7.1.2.1, the displayed positive-index
coefficients (7.3.4.4) form a finite independent spanning family for the annihilator.
On representatives after finite PV this says the finite array is onto and its common
kernel is the no-pole stage, characterized by vanishing of the negative coefficients. -/
def Printed.sLocalGammaFiltration_dual_span : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (V(F)))
    (ω : PontryaginDual J₁(F, S)) (N : InfinitePlace F → ℕ),
    let C := sLocalGammaPoleCutoff (F := F) (S := S) ω N
    let J := {j : QuasiCharacter (SIdeleQuotient F S) × ℕ // j.1 ∈ C ∧
      0 < j.2 ∧ j.2 ≤ (sLocalArchPolePlaces (F := F) (S := S) j.1).card}
    let coeff := fun (f : B(F, S)) (j : J) (k : ℤ) ↦
      sLocalZLaurentCoeff (F := F) (S := S)
        (sAdelePrincipalValue F (Finset.Subset.refl S) f) j.val.1 k
    Finite J ∧ (∀ z : J → ℂ, ∃ f : B(F, S), ∀ j : J, coeff f j j.val.2 = z j) ∧
      (∀ f : B(F, S), (∀ j : J, coeff f j j.val.2 = 0) ↔
        ∀ j : J, coeff f j (-(j.val.2 : ℤ)) = 0)

/-- Paper: Theorem 7.3.4.1(2), pp. 364–365.
For the rational archimedean stage and trivial character take a nonnegative nonzero even
bump in the annulus two to three. Its Mellin transform is entire, and its derivative
at zero integrates the bump against a strictly positive logarithm. The coefficient
of exponent one therefore fails to annihilate the zero-cutoff stage. -/
theorem Printed.sLocalGammaFiltration_dual_span_false : ¬ Printed.sLocalGammaFiltration_dual_span :=
  by sorry

end RiemannMasullo
