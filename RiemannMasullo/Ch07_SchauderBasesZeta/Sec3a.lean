module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec2
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec6

/-! # §7.3.1 Orbital Schauder bases

The set of places in the Lean notation lists the finite places. All archimedean places
are included in the definition of the S-adeles.
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
theorem isSaturatedPlaceSet_empty : IsSaturatedPlaceSet (∅ : Finset V) := by sorry

open Classical in
/-- Paper: Situation 7.3.1.1(2), p. 340.
The primary part of S at p consists of its places lying over p.
Deviation: A rational prime is represented by its place in the ring of integers of ℚ. -/
def sLocalPrimaryPlaces (S : Finset V) (p : Vℚ) : Finset V :=
  S.filter fun v ↦ v.under (𝓞 ℚ) = p

/-- Paper: Situation 7.3.1.1(2), p. 340.
A place belongs to the primary part exactly when it belongs to S and lies over p. -/
theorem mem_sLocalPrimaryPlaces (p : Vℚ) (v : V) :
    v ∈ sLocalPrimaryPlaces S p ↔ v ∈ S ∧ v.under (𝓞 ℚ) = p := by sorry

/-- Paper: Situation 7.3.1.1(2), p. 340.
The primary part is a subset of the selected finite places. -/
theorem sLocalPrimaryPlaces_subset (S : Finset V) (p : Vℚ) :
    sLocalPrimaryPlaces S p ⊆ S := by sorry

/-- Paper: Situation 7.3.1.1(1)–(2), p. 340.
If S is saturated and its primary part at p is nonempty, that part contains every place over p. -/
theorem mem_sLocalPrimaryPlaces_of_saturated (p : Vℚ) (_hS : IsSaturatedPlaceSet S)
    (_hp : (sLocalPrimaryPlaces S p).Nonempty) (v : V) :
    v ∈ sLocalPrimaryPlaces S p ↔ v.under (𝓞 ℚ) = p := by sorry

-- The unitary lifts in Situation 7.3.1.1(3) use the norm-twist chart of §3.3 and §5.4.
-- TODO(paper-gap): Theorem 7.3.1.2 specifies that S₀ contains the archimedean places,
-- but the principal-value operator of §5.3 and the introduction on p. 340 use finite places.
-- Its proof also replaces m_S - m_{S₀} by m_{S₀} in the coefficient cutoff.

/-- Paper: Theorem 7.3.1.2, p. 341.
The indices consist of a center on the chosen component and a zero-based offset among the
highest coefficients removed by the selected finite principal values.
Deviation: The offset r selects the printed coefficient of pole order m_S(c) - r. -/
def SLocalOrbitalIndex (T : Finset V) (ω : PontryaginDual J₁) :=
  {j : Xₛ × ℕ // onComponent(j.1, ω) ∧ j.2 < sLocalFinitePoleMultiplicity T j.1}

local notation "I(" T ", " ω ")" => SLocalOrbitalIndex (F := F) (S := S) T ω

/-- Paper: Theorem 7.3.1.2, p. 341.
At the trivial character the admissible offsets are precisely those below the number
of selected finite places. -/
theorem sLocalOrbitalIndex_one_iff {T : Finset V} (_hT : T ⊆ S) (r : ℕ) :
    (∃ j : I(T, (1 : PontryaginDual J₁)), j.val = (1, r)) ↔ r < T.card := by sorry

/-- Paper: Theorem 7.3.1.2, p. 341.
The indexed functional is the selected Laurent coefficient on homogeneous theta classes. -/
def sLocalOrbitalPrincipalPart {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) : StrongDual ℂ (Θₛ(ω)) :=
  sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1
    (sLocalRhoPoleOrder j.val.1 - j.val.2)

/-- Paper: Theorem 7.3.1.2, p. 341.
Offset zero gives the coefficient of the highest allowed pole order on a test. -/
theorem sLocalOrbitalPrincipalPart_mk_top {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) (_hj : j.val.2 = 0) (f : ℬₛ) :
    sLocalOrbitalPrincipalPart j ((Kₛ(ω)).mkQL f) =
      sLocalZLaurentCoeff f j.val.1 (-(sLocalRhoPoleOrder j.val.1 : ℤ)) := by sorry

-- TODO(paper-gap): Theorem 7.2.1.1(4) describes a pole-bound subspace. The reverse
-- inclusion below requires division by the selected reciprocal Euler factors in the
-- componentwise Mellin image. Proposition 7.2.2.1 assumes unramifiedness outside T.
/-- Paper: Theorem 7.3.1.2(1), p. 341.
The principal-value range is the pole-bound subspace with the remaining multiplicity.
Deviation: The selected places are finite, as in Definition 5.3.1.4. -/
theorem sLocalOrbitalPrincipalValue_eq_poleBound {T : Finset V} (hT : T ⊆ S) (_hne : T.Nonempty)
    (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial) (ω : PontryaginDual J₁) :
    PV(T, hT, ω) = sLocalThetaPoleBound ω
      (fun c ↦ sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity T c) := by sorry

/-- Paper: Theorem 7.3.1.2(1), p. 341.
The principal-value image is the common kernel of the selected coefficients on the component.
Deviation: The selection is finite, as in the introduction and the principal-value operator
of §5.3. The cutoff is the one in the theorem statement. -/
theorem mem_sLocalOrbitalPrincipalValue_iff {T : Finset V} (h₀ : T ⊆ S) (_hne : T.Nonempty)
    (_hsat : IsSaturatedPlaceSet S) (_hclass : PicTrivial)
    (χ : PontryaginDual J₁) (x : Θₛ(χ)) :
    x ∈ PV(T, h₀, χ) ↔ ∀ j : I(T, χ),
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := χ) j x = 0 := by sorry

/-- Paper: Theorem 7.3.1.2(1), p. 341.
The finite principal-value image is closed in the homogeneous theta space.
Deviation: Uses the finite-place selection of part (1). -/
theorem sLocalOrbitalPrincipalValue_isClosed {T : Finset V} (hT : T ⊆ S) (_hTne : T.Nonempty)
    (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial) (ω : PontryaginDual J₁) :
    IsClosed (PV(T, hT, ω) : Set (Θₛ(ω))) := by sorry

/-- Paper: Theorem 7.3.1.2(2), p. 341.
The annihilator of the finite principal-value image is the closed span of the selected
coefficients in the strong dual.
Deviation: Uses the finite-place selection of part (1). Lower Laurent coefficients can mix
under translations, as in §7.2. -/
theorem sLocalOrbitalPrincipalValue_annihilator {T : Finset V} (hT : T ⊆ S) (_hTne : T.Nonempty)
    (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial) (ω : PontryaginDual J₁) :
    (PV(T, hT, ω)).dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ) =
      (Submodule.span ℂ
        (range (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω)))).topologicalClosure := by sorry

-- TODO(paper-gap): For ℚ and T = {p}, dividing an entire zeta transform by
-- 1 - p⁻ˢ produces at most a simple pole at zero. The leading orbital coefficient
-- at the trivial character has order two. Page 342 needs an interpolant starting
-- with a test attaining the full allowed order at the selected center.
open Classical in
/-- Paper: Theorem 7.3.1.2(2), p. 341.
The selected coefficients have a biorthogonal family in the quotient. The pairing is
evaluated on a representative of each quotient vector.
Deviation: Uses the finite-place selection of part (1). -/
theorem sLocalOrbitalPrincipalValue_biorthogonal {T : Finset V} (hT : T ⊆ S) (_hTne : T.Nonempty)
    (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial) (ω : PontryaginDual J₁) :
    let R := PV(T, hT, ω)
    ∃ ψ : I(T, ω) → (Θₛ(ω) ⧸ R),
      ∀ (i j : I(T, ω)) (x : Θₛ(ω)), R.mkQ x = ψ j →
        sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) i x =
          if i = j then 1 else 0 := by sorry

/-- Paper: Theorem 7.3.1.2(2), p. 341.
The selected coefficients are topologically free. Two unconditionally convergent series
with the same limit have identical coefficients.
Deviation: Uses the finite-place selection of part (1). -/
theorem sLocalOrbitalPrincipalPart_hasSum_unique {T : Finset V} (_hT : T ⊆ S) (_hTne : T.Nonempty)
    (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial) (ω : PontryaginDual J₁)
    (a b : I(T, ω) → ℂ)
    (u : StrongDual ℂ (Θₛ(ω)))
    (ha : HasSum (fun j ↦ a j • sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) j) u)
    (hb : HasSum (fun j ↦ b j • sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) j) u) :
    a = b := by sorry

local notation "Sₚ(" p ")" => sLocalPrimaryPlaces (F := F) S p
local notation "hₚ(" p ")" => sLocalPrimaryPlaces_subset (F := F) S p

/-- Paper: Definition 7.3.1.3, p. 343.
The denominator of the primary orbital quotient is the image of the corresponding
principal-value operator on the homogeneous theta space. -/
def sLocalPrimaryOrbitalSubmodule (p : Vℚ) (ω : PontryaginDual J₁) : Submodule ℂ (Θₛ(ω)) :=
  PV(Sₚ(p), hₚ(p), ω)

local notation "Rₚ(" p ", " ω ")" => sLocalPrimaryOrbitalSubmodule (F := F) (S := S) p ω

/-- Paper: Definition 7.3.1.3, p. 343.
The p-primary orbital quotient is the homogeneous theta space modulo its primary
principal-value image. It carries the quotient topology. -/
abbrev SLocalPrimaryOrbitalQuotient (p : Vℚ) (ω : PontryaginDual J₁) :=
  Θₛ(ω) ⧸ Rₚ(p, ω)

local notation "Q(" p ", " ω ")" => SLocalPrimaryOrbitalQuotient (F := F) (S := S) p ω
local notation "π(" p ", " ω ")" => (Rₚ(p, ω)).mkQ

/-- Paper: Definition 7.3.1.3, p. 343.
A theta class represents zero in the p-primary quotient exactly when its selected
highest Laurent coefficients vanish. -/
theorem sLocalPrimaryOrbitalQuotient_mk_eq_zero (p : Vℚ) (_hS : IsSaturatedPlaceSet S)
    (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial) (ω : PontryaginDual J₁) (x : Θₛ(ω)) :
    π(p, ω) x = 0 ↔ ∀ j : I(Sₚ(p), ω), sLocalOrbitalPrincipalPart j x = 0 := by sorry

/-- Paper: Definition 7.3.1.4, p. 343.
The primary multiplicity counts the places over p which contribute a simple pole.
Deviation: Uses positive pole multiplicity and extends it by zero outside the pole locus. -/
def sLocalPrimaryPoleMultiplicity (p : Vℚ) (c : Xₛ) : ℕ :=
  sLocalFinitePoleMultiplicity (Sₚ(p)) c

/-- Paper: Definition 7.3.1.4, p. 343.
Every place in the primary part contributes at the trivial character. -/
theorem sLocalPrimaryPoleMultiplicity_one (p : Vℚ) :
    sLocalPrimaryPoleMultiplicity p (1 : Xₛ) = (Sₚ(p)).card := by sorry

section QuotientTransfer

variable {E₁ E₂ : Type*} [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
variable [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
variable [IsTopologicalAddGroup E₁]
variable [ContinuousSMul ℂ E₁] [ContinuousSMul ℂ E₂]
variable (H₁ : Submodule ℂ E₁) (H₂ : Submodule ℂ E₂)
variable (A : E₁ →L[ℂ] E₂) (A₀ : (E₁ ⧸ H₁) →L[ℂ] (E₂ ⧸ H₂))
variable (x : ℕ → E₂) (d : ℕ → StrongDual ℂ (E₂ ⧸ H₂))
variable (B : Seminorm ℂ (E₂ ⧸ H₂) → ℕ → ℝ≥0) (y : ℕ → E₁)

/-- Paper: Lemma 7.3.1.5(1), p. 343.
Lifts of the absolute basis vectors give an absolute basis in the first quotient.
Their biorthogonal functionals are an unconditional basis of its strong dual. -/
theorem orbitalQuotient_lift_bases
    (_hF₁ : IsFrechetTVS E₁) (_hF₂ : IsFrechetTVS E₂)
    (_hN₁ : IsNuclearTVS E₁) (_hN₂ : IsNuclearTVS E₂)
    (_hH₁ : IsClosed (H₁ : Set E₁)) (_hH₂ : IsClosed (H₂ : Set E₂))
    (_hA : Injective A) (_hpre : H₂.comap A.toLinearMap = H₁)
    (_hA₀ : A₀.comp H₁.mkQL = H₂.mkQL.comp A) (_hsurj : Surjective A₀)
    (_hb : IsSchauderBasis (H₂.mkQL ∘ x) d) (_habs : SchauderBasis.IsAbsolute (H₂.mkQL ∘ x) d)
    (_hB : ∀ q : Seminorm ℂ (E₂ ⧸ H₂), Continuous q →
      (fun n ↦ q (H₂.mkQL (x n))) =O[atTop] (fun n ↦ (B q n : ℝ)))
    (_hy : ∀ n, A (y n) = x n) :
    let e := H₁.mkQL ∘ y
    let a := fun n ↦ (d n).comp A₀
    let ev : ℕ → StrongDual ℂ (StrongDual ℂ (E₁ ⧸ H₁)) :=
      fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (e n)
    IsSchauderBasis e a ∧ SchauderBasis.IsAbsolute e a ∧
      IsSchauderBasis a ev ∧ SchauderBasis.IsUnconditional a ev := by sorry

/-- Paper: Lemma 7.3.1.5(2), p. 344.
The estimate for each seminorm on the first quotient uses the bound for that
seminorm transported to the second quotient by the inverse induced isomorphism. -/
theorem orbitalQuotient_lift_growth
    (_hF₁ : IsFrechetTVS E₁) (_hF₂ : IsFrechetTVS E₂)
    (_hN₁ : IsNuclearTVS E₁) (_hN₂ : IsNuclearTVS E₂)
    (_hH₁ : IsClosed (H₁ : Set E₁)) (_hH₂ : IsClosed (H₂ : Set E₂))
    (_hA : Injective A) (_hpre : H₂.comap A.toLinearMap = H₁)
    (_hA₀ : A₀.comp H₁.mkQL = H₂.mkQL.comp A) (_hsurj : Surjective A₀)
    (_hb : IsSchauderBasis (H₂.mkQL ∘ x) d) (_habs : SchauderBasis.IsAbsolute (H₂.mkQL ∘ x) d)
    (_hB : ∀ q : Seminorm ℂ (E₂ ⧸ H₂), Continuous q →
      (fun n ↦ q (H₂.mkQL (x n))) =O[atTop] (fun n ↦ (B q n : ℝ)))
    (_hy : ∀ n, A (y n) = x n) :
    ∃ e : (E₁ ⧸ H₁) ≃L[ℂ] (E₂ ⧸ H₂), e.toContinuousLinearMap = A₀ ∧
      ∀ q : Seminorm ℂ (E₁ ⧸ H₁), Continuous q →
        (fun n ↦ q (H₁.mkQL (y n))) =O[atTop]
          (fun n ↦ (B (q.comp e.symm.toLinearMap) n : ℝ)) := by sorry

end QuotientTransfer

local notation "period(" v ")" => (2 * Real.pi / Real.log ((v : S).val.asIdeal.absNorm : ℝ))
local notation "lattice(" χ ", " v ", " t ", " n ")" =>
  chart(χ) ((((n : ℝ) * period(v) - t : ℝ) : ℂ) * Complex.I)
local notation "phase(" χ ", " v ", " u ", " t ")" =>
  (t ∈ Ico 0 period(v) ∧
    sLocalFiniteRestriction v (chart(χ) (-(t : ℂ) * Complex.I)) u = 1)
local notation "uniformizerNorm(" v ", " u ")" =>
  (‖(↑(u) : (v : S).val.adicCompletion F)‖ = ((v : S).val.asIdeal.absNorm : ℝ)⁻¹)

/-- Paper: Equation (7.3.1.10), p. 344.
There is a unique phase in the given interval for which the adjusted character
is trivial on the chosen local uniformizer. -/
theorem existsUnique_sLocalOrbitalPhase (χ : PontryaginDual Jₛ) (v : S)
    (u : (v.val.adicCompletion F)ˣ) (_hu : uniformizerNorm(v, u)) :
    ∃! t : ℝ, phase(χ, v, u, t) := by sorry

/-- Paper: Equation (7.3.1.11), p. 344.
At a contributing finite place, the pole on the given component has a unique lattice index. -/
theorem existsUnique_sLocalOrbitalLatticeIndex (χ : PontryaginDual Jₛ) (v : S)
    (u : (v.val.adicCompletion F)ˣ) (_hu : uniformizerNorm(v, u)) (t : ℝ)
    (_ht : phase(χ, v, u, t)) (c : Xₛ)
    (_hc : ∃ s, c = chart(χ) s) (_hv : v ∈ sLocalFinitePolePlaces c) :
    ∃! n : ℤ, c = lattice(χ, v, t, n) := by sorry

/-- Paper: Discussion after (7.3.1.11), p. 344.
At a common pole, the phase difference is an integer combination of the two local periods.
Deviation: The periods use the residue-field cardinalities of the places. The phase
difference need not be an integer multiple of the period for the rational prime. -/
theorem sLocalOrbitalPhase_sub (χ : PontryaginDual Jₛ) (p : Vℚ)
    (_hS : IsSaturatedPlaceSet S) (v w : S)
    (_hv : v.val ∈ Sₚ(p)) (_hw : w.val ∈ Sₚ(p))
    (uᵥ : (v.val.adicCompletion F)ˣ) (u_w : (w.val.adicCompletion F)ˣ)
    (_hᵥ : uniformizerNorm(v, uᵥ)) (_h_w : uniformizerNorm(w, u_w))
    (tᵥ t_w : ℝ) (_htᵥ : phase(χ, v, uᵥ, tᵥ)) (_ht_w : phase(χ, w, u_w, t_w))
    (c : Xₛ) (_hc : ∃ s, c = chart(χ) s)
    (_hvc : v ∈ sLocalFinitePolePlaces c) (_hwc : w ∈ sLocalFinitePolePlaces c) :
    ∃ a b : ℤ, tᵥ - t_w = (a : ℝ) * period(v) - (b : ℝ) * period(w) := by sorry

local notation "fourierZeta(" c ")" =>
  (fun (f : ℬₛ) (z : ℂ) ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f)
    (dualₛ (twistₛ c z)))

/-- Paper: Equation (7.3.1.14), p. 344.
The reflected Fourier zeta transform is holomorphic near each selected finite pole
of the correcting factor. Its derivatives therefore evaluate the analytic germ there. -/
theorem sLocalOrbitalFourierZeta_analyticAt {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) (f : ℬₛ) :
    AnalyticAt ℂ (fourierZeta(j.val.1) f) 0 := by sorry

/-- Paper: Equation (7.3.1.14), p. 344.
On S-adelic tests the Fourier jet is continuous and complex linear. -/
theorem sLocalOrbitalFourierJet_continuous_linear {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) :
    let D := fun f : ℬₛ ↦ iteratedDeriv j.val.2 (fourierZeta(j.val.1) f) 0
    Continuous D ∧ IsLinearMap ℂ D := by sorry

local notation "fourierJet(" j ")" =>
  (⟨(sLocalOrbitalFourierJet_continuous_linear j).2.mk' _,
    (sLocalOrbitalFourierJet_continuous_linear j).1⟩ : StrongDual ℂ ℬₛ)

/-- Paper: Equation (7.3.1.14), p. 344.
The Fourier jet annihilates the kernel of the homogeneous theta map. -/
theorem sLocalOrbitalFourierJet_ker {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) :
    Kₛ(ω) ≤ (fourierJet(j)).ker := by sorry

/-- Paper: Equations (7.3.1.13)–(7.3.1.14), p. 344.
The indexed Fourier functional is the jet of the reflected zeta transform at its center.
It differentiates in the original norm direction, as in the printed formula. -/
def sLocalOrbitalFourierJet {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) : StrongDual ℂ (Θₛ(ω)) :=
  (Kₛ(ω)).liftQL (fourierJet(j)) (sLocalOrbitalFourierJet_ker j)

/-- Paper: Equation (7.3.1.14), p. 344.
On a test representative the Fourier jet evaluates to the stated derivative. -/
theorem sLocalOrbitalFourierJet_mk {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) (f : ℬₛ) :
    sLocalOrbitalFourierJet j ((Kₛ(ω)).mkQL f) =
      iteratedDeriv j.val.2 (fourierZeta(j.val.1) f) 0 := by sorry

local notation "Idx(" p ", " ω ")" => I(Sₚ(p), ω)

section PrimaryBases

/-- Paper: Theorem 7.3.1.6(1), p. 345.
Each primary polar functional vanishes on the primary principal-value image, so
it lies in the image of the transpose of the quotient map. -/
theorem sLocalOrbitalPrincipalPart_range_le_ker
    (p : Vℚ) (ω : PontryaginDual J₁) (j : Idx(p, ω)) :
    Rₚ(p, ω) ≤
      (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j).ker := by sorry

/-- Paper: Theorem 7.3.1.6(1), p. 345.
Each primary Fourier functional vanishes on the primary principal-value image, so
it lies in the image of the transpose of the quotient map. -/
theorem sLocalOrbitalFourierJet_range_le_ker
    (p : Vℚ) (ω : PontryaginDual J₁) (j : Idx(p, ω)) :
    Rₚ(p, ω) ≤
      (sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j).ker := by sorry

/-- Paper: Theorem 7.3.1.6(2), p. 345.
The common index set either admits an enumeration by the natural numbers or is
empty and the corresponding primary quotient is zero. -/
theorem sLocalOrbitalIndex_enumerable_or_empty
    (p : Vℚ) (ω : PontryaginDual J₁)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial) :
    Nonempty (ℕ ≃ Idx(p, ω)) ∨ (IsEmpty (Idx(p, ω)) ∧ Subsingleton (Q(p, ω))) := by sorry

local notation "rhoCoeff(" c ", " r ")" =>
  complexResidue (fun z : ℂ ↦ sLocalRhoFactor (twistₛ (c) z) *
    z ^ ((sLocalRhoPoleOrder (c) : ℤ) - ((r : ℕ) : ℤ) - 1)) 0

/-- Paper: Theorem 7.3.1.6(2)–(3), p. 345.
Any enumeration of the polar functionals gives an unconditional basis of the strong dual.
With the same enumeration, its biorthogonal vectors are an absolute basis of the quotient.
Deviation: Assumes polynomial bounds on the ratios of lower to leading Laurent coefficients
of the correcting factor within each selected block. The hypothesis is vacuous at a
primary pole of multiplicity one. The general assertion on p. 349 needs uniform control
of the changes of basis across the different centers. -/
theorem sLocalPolarOrbital_bases_of_laurent_bounds
    (p : Vℚ) (ω : PontryaginDual J₁)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial) (σ : ℕ ≃ Idx(p, ω))
    (_hcoeff : ∀ χ : PontryaginDual Jₛ, ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (j : Idx(p, ω)) (s : ℂ), j.val.2 ≠ 0 → j.val.1 = chart(χ) s →
        ‖rhoCoeff(j.val.1, j.val.2)‖ ≤ C * (1 + ‖s‖) ^ d * ‖rhoCoeff(j.val.1, 0)‖) :
    ∃ (D : Idx(p, ω) → StrongDual ℂ (Q(p, ω))) (ψ : Idx(p, ω) → Q(p, ω))
      (ev : ℕ → StrongDual ℂ (StrongDual ℂ (Q(p, ω)))),
      (∀ (n : ℕ) (ℓ : StrongDual ℂ (Q(p, ω))), ev n ℓ = ℓ (ψ (σ n))) ∧
      (∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
        sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x) ∧
      let e := ψ ∘ σ
      let d := D ∘ σ
      IsSchauderBasis d ev ∧ SchauderBasis.IsUnconditional d ev ∧
        IsSchauderBasis e d ∧ SchauderBasis.IsAbsolute e d := by sorry

-- TODO(paper-gap): In (7.3.1.19) use the inverse uniformizers at the unramified
-- places above p for the generators of Chapter 4. At a ramified place Weil's
-- unit average vanishes on the isotype, and its principal value is the identity.
/-- Paper: Theorem 7.3.1.6(2)–(3), p. 345.
Any enumeration of the Fourier functionals gives an unconditional basis of the strong dual.
With the same enumeration, its biorthogonal vectors are an absolute basis of the quotient. -/
theorem sLocalFourierOrbital_bases
    (p : Vℚ) (ω : PontryaginDual J₁)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial) (σ : ℕ ≃ Idx(p, ω)) :
    ∃ (D : Idx(p, ω) → StrongDual ℂ (Q(p, ω))) (ψ : Idx(p, ω) → Q(p, ω))
      (ev : ℕ → StrongDual ℂ (StrongDual ℂ (Q(p, ω)))),
      (∀ (n : ℕ) (ℓ : StrongDual ℂ (Q(p, ω))), ev n ℓ = ℓ (ψ (σ n))) ∧
      (∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
        sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x) ∧
      let e := ψ ∘ σ
      let d := D ∘ σ
      IsSchauderBasis d ev ∧ SchauderBasis.IsUnconditional d ev ∧
        IsSchauderBasis e d ∧ SchauderBasis.IsAbsolute e d := by sorry

end PrimaryBases

local notation "restrict₁(" χ ")" => ((χ : PontryaginDual Jₛ).comp
  (⟨(mₛ).ker.subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ))

section LatticeEstimates

open Classical in
/-- Paper: Theorem 7.3.1.6(4), p. 345.
The seminorm of a biorthogonal Fourier vector grows at most polynomially along a
local pole lattice, uniformly over the derivative orders at each pole.
Deviation: A constant times a power of one plus the index norm expresses the polynomial bound.
The finite initial segment is absorbed into the constant. -/
theorem sLocalFourierOrbital_biorthogonal_growth
    (p : Vℚ) (χ : PontryaginDual Jₛ) (ω : PontryaginDual J₁)
    (v : S) (u : (v.val.adicCompletion F)ˣ) (t : ℝ)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial)
    (_hω : ω = restrict₁(χ))
    (_hv : v.val ∈ Sₚ(p)) (_hu : uniformizerNorm(v, u)) (_ht : phase(χ, v, u, t))
    (ψ : Idx(p, ω) → Q(p, ω))
    (_hψ : ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = ψ j →
      sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x = if i = j then 1 else 0)
    (q : Seminorm ℂ Q(p, ω)) (_hq : Continuous q) :
    ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℤ) (j : Idx(p, ω)), j.val.1 = lattice(χ, v, t, n) →
        v ∈ sLocalFinitePolePlaces (F := F) (S := S) j.val.1 → q (ψ j) ≤ C * (1 + |(n : ℝ)|) ^ d := by sorry

open Classical in
/-- Paper: Theorem 7.3.1.6(5), p. 345.
The Fourier jet of each test at fixed order gives a Schwartz sequence along a local
pole lattice.
Deviation: The sequence is extended by zero where the place does not contribute
a pole or the derivative order is outside the primary multiplicity. -/
theorem sLocalOrbitalFourierJet_lattice_schwartz
    (p : Vℚ) (χ : PontryaginDual Jₛ) (v : S) (u : (v.val.adicCompletion F)ˣ) (t : ℝ)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial)
    (_hv : v.val ∈ Sₚ(p)) (_hu : uniformizerNorm(v, u)) (_ht : phase(χ, v, u, t))
    (f : ℬₛ) (k : ℕ) :
    ∃ a : SchwartzBruhat (Multiplicative ℤ), ∀ n : ℤ,
      let c := lattice(χ, v, t, n)
      a (Multiplicative.ofAdd n) =
        if v ∈ sLocalFinitePolePlaces (F := F) (S := S) c ∧
          k < sLocalPrimaryPoleMultiplicity (F := F) (S := S) p c then
          iteratedDeriv k (fourierZeta(c) f) 0
        else 0 := by sorry

end LatticeEstimates

-- TODO(paper-gap): The proof of Theorem 7.3.1.6 alternates between 1+s and 1-s in
-- (7.3.1.24)–(7.3.1.25). For the displayed 1+s coordinate the multiplier is P(-s)
-- for P(s) the selected reciprocal Euler product. The remaining order at c can be
-- m_S(c) - N_p(c), which is positive when other places contribute there.
-- The pointwise triangular changes on p. 349 need a convergence argument for the polar basis.
-- The discrete oscillation assertion on p. 350 needs the estimate identified in ERRATA M8.

section OrbitalSystems

open Classical in
/-- Paper: Definition 7.3.1.7(1), p. 350.
The polar orbital system consists of the primary polar functionals in the ambient strong
dual and their biorthogonal vectors in the quotient. -/
def sLocalPolarOrbitalSystem (p : Vℚ) (ω : PontryaginDual J₁) : Set (StrongDual ℂ (Θₛ(ω))) × Set Q(p, ω) :=
  (range (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω)),
    {y : Q(p, ω) | ∃ j : Idx(p, ω), ∀ (i : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = y →
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x = if i = j then 1 else 0})

open Classical in
/-- Paper: Definition 7.3.1.7(2), p. 350.
The fourier orbital system consists of the primary fourier functionals in the ambient strong
dual and their biorthogonal vectors in the quotient. -/
def sLocalFourierOrbitalSystem (p : Vℚ) (ω : PontryaginDual J₁) : Set (StrongDual ℂ (Θₛ(ω))) × Set Q(p, ω) :=
  (range (sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω)),
    {y : Q(p, ω) | ∃ j : Idx(p, ω), ∀ (i : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = y →
      sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x = if i = j then 1 else 0})

/-- Paper: Definition 7.3.1.7(1), p. 350.
Each selected Laurent coefficient belongs to the polar orbital system's functional set. -/
theorem sLocalOrbitalPrincipalPart_mem_polarSystem (p : Vℚ) (ω : PontryaginDual J₁) (j : Idx(p, ω)) :
    sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j ∈
      (sLocalPolarOrbitalSystem (F := F) (S := S) p ω).1 := by sorry

/-- Paper: Definition 7.3.1.7(2), p. 350.
Each selected Fourier jet belongs to the Fourier orbital system's functional set. -/
theorem sLocalOrbitalFourierJet_mem_fourierSystem (p : Vℚ) (ω : PontryaginDual J₁) (j : Idx(p, ω)) :
    sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j ∈
      (sLocalFourierOrbitalSystem (F := F) (S := S) p ω).1 := by sorry

open Classical in
/-- Paper: Definition 7.3.1.7(1), p. 350.
The quotient vector paired with a specified index belongs to the system's second set. -/
theorem sLocalPolarOrbitalSystem_biorthogonal_mem (p : Vℚ) (ω : PontryaginDual J₁)
    (ψ : Idx(p, ω) → Q(p, ω))
    (hψ : ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = ψ j →
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x = if i = j then 1 else 0)
    (j : Idx(p, ω)) : ψ j ∈ (sLocalPolarOrbitalSystem (F := F) (S := S) p ω).2 :=
  ⟨j, fun i ↦ hψ i j⟩

open Classical in
/-- Paper: Definition 7.3.1.7(2), p. 350.
The quotient vector paired with a specified index belongs to the system's second set. -/
theorem sLocalFourierOrbitalSystem_biorthogonal_mem (p : Vℚ) (ω : PontryaginDual J₁)
    (ψ : Idx(p, ω) → Q(p, ω))
    (hψ : ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = ψ j →
      sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x = if i = j then 1 else 0)
    (j : Idx(p, ω)) : ψ j ∈ (sLocalFourierOrbitalSystem (F := F) (S := S) p ω).2 :=
  ⟨j, fun i ↦ hψ i j⟩

end OrbitalSystems

-- TODO(paper-gap): Corollary 7.3.1.8 cites the nonexistent Theorem 7.3.1.2(3).
-- Definition 7.3.1.7 identifies the S-local systems from Theorem 7.3.1.6.
-- The proof also mentions global systems but does not identify a global orbital quotient or basis.

section OrbitalBasisProperties

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F


/-- Paper: Corollary 7.3.1.8(1), p. 350.
The enumerated polar and Fourier systems give equicontinuous, shrinking and boundedly
complete bases of the strong dual.
Deviation: Assumes a basis in the S-local quotient. The printed reference to
Theorem 7.3.1.2(3) has no target. -/
theorem sLocalOrbitalSystem_strongDual_basis_properties
    (p : Vℚ) (χ : PontryaginDual C𝔽) (χₛ : PontryaginDual Jₛ) (ω : PontryaginDual J₁)
    (σ : ℕ ≃ Idx(p, ω)) (e : ℕ → Q(p, ω)) (d : ℕ → StrongDual ℂ (Q(p, ω)))
    (hχ : (circleToComplex).comp χ ∈ unramifiedOutside F S)
    (_hχₛ : (circleToComplex).comp χₛ = sIdeleRestriction F S ⟨(circleToComplex).comp χ, hχ⟩)
    (_hω : ω = restrict₁(χₛ))
    (_hd : (∀ (n : ℕ) (x : Θₛ(ω)), d n (π(p, ω) x) =
        sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) (σ n) x) ∨
      (∀ (n : ℕ) (x : Θₛ(ω)), d n (π(p, ω) x) =
        sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) (σ n) x))
    (_he : IsSchauderBasis e d) :
    let ev : ℕ → StrongDual ℂ (StrongDual ℂ (Q(p, ω))) :=
      fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (e n)
    SchauderBasis.IsEquicontinuous d ev ∧ SchauderBasis.IsShrinking d ev ∧
      SchauderBasis.IsBoundedlyComplete d := by sorry

/-- Paper: Corollary 7.3.1.8(2), p. 350.
The corresponding biorthogonal bases of the primary quotient are equicontinuous,
shrinking and boundedly complete.
Deviation: Assumes a basis in the S-local quotient associated to the descended character. -/
theorem sLocalOrbitalSystem_quotient_basis_properties
    (p : Vℚ) (χ : PontryaginDual C𝔽) (χₛ : PontryaginDual Jₛ) (ω : PontryaginDual J₁)
    (σ : ℕ ≃ Idx(p, ω)) (e : ℕ → Q(p, ω)) (d : ℕ → StrongDual ℂ (Q(p, ω)))
    (hχ : (circleToComplex).comp χ ∈ unramifiedOutside F S)
    (_hχₛ : (circleToComplex).comp χₛ = sIdeleRestriction F S ⟨(circleToComplex).comp χ, hχ⟩)
    (_hω : ω = restrict₁(χₛ))
    (_hd : (∀ (n : ℕ) (x : Θₛ(ω)), d n (π(p, ω) x) =
        sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) (σ n) x) ∨
      (∀ (n : ℕ) (x : Θₛ(ω)), d n (π(p, ω) x) =
        sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) (σ n) x))
    (_he : IsSchauderBasis e d) :
    SchauderBasis.IsEquicontinuous e d ∧ SchauderBasis.IsShrinking e d ∧
      SchauderBasis.IsBoundedlyComplete e := by sorry

end OrbitalBasisProperties

end RiemannMasullo
