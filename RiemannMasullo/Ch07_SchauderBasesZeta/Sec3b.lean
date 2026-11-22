module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a

/-! # §7.3.2–7.3.4 Paley–Wiener levels and archimedean principal parts

The finsets in this file list the finite places. Each S-local stage also
contains all the archimedean places. The PW constructions use the restriction
of the character to the norm-one group, which determines its theta isotype.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 600000
set_option Elab.async false

variable {F : Type*} [Field F] [NumberField F]
variable {S T R : Finset (HeightOneSpectrum (𝓞 F))}

local notation "C₁" => (ideleClassNorm F).ker
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "J(" T ")" => SIdeleQuotient F T
local notation "m(" T ")" => sIdeleQuotientNorm F T
local notation "J₁(" T ")" => (m(T)).ker
local notation "B(" T ")" => SchwartzBruhat (Multiplicative (SAdeleRing F T))
local notation "Θ(" T ", " ω ")" => SLocalHomogeneousThetaSpace F T ω
local notation "q(" T ", " ω ")" => (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F T ω)).mkQ
local notation "Z₀(" T ")" => sAdelePolarSubspace F T
local notation "Π(" h ")" => sAdeleSchwartzTransition F h
local notation "PicTrivial" => Subsingleton (CommRing.Pic ((S : Set V).integer F))
local notation "A(" T ", " ω ")" =>
  (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T) ω).exists.choose
local notation "PV(" h ", " ω ")" => sLocalHomogeneousThetaPrincipalValue (F := F) h ω
local notation "count(" S ")" => (Fintype.card (InfinitePlace F) + Finset.card S)
local notation "size(" R ")" => (∏ v ∈ R, (v.asIdeal.absNorm : ℝ))
local notation "large(" g ")" => (1 ≤ ((m(T) g).val : ℝ))
local notation "descend(" h ", " ω ", " hu ")" =>
  sLocalNormOneCharacter (F := F) T ω
    (NormOneCharacterUnramifiedOutside.mono (F := F) hu h)
local notation "onComponent(" c ", " ω ")" =>
  (normOneRestriction (m(S)) c =
    (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω)

/-- Paper: Definition 7.3.2.1(1), p. 351.
The Fourier box bounds the normalized absolute value at every selected place. -/
def sLocalPWBox (_S : Finset V) (X : ℝ) : Set (SAdeleRing F _S) :=
  {x | (∀ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult ≤ X) ∧ ∀ v : _S, ‖x.2 v‖ ≤ X}

/-- Paper: Definition 7.3.2.1(1), p. 351.
The Fourier box is compact. -/
theorem isCompact_sLocalPWBox (X : ℝ) : IsCompact (sLocalPWBox S X) := by sorry

local notation "inBand(" K ", " f ")" =>
  (HasCompactSupport (sAdeleSchwartzFourier f).val ∧
    tsupport (sAdeleSchwartzFourier f).val ⊆ Multiplicative.toAdd ⁻¹' K)

/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
The tests at the larger stage are insertions of small-stage tests with compact Fourier
support contained in the specified region.
Deviation: Uses the cited transition (2.1.4.2), which inserts integer-ring indicators,
as in the proofs on pp. 352–359. Equations (7.3.2.2) and (7.3.2.13) print unit indicators. -/
def sLocalPWTests (hST : S ⊆ T) (K : Set (SAdeleRing F S)) : Submodule ℂ (B(T)) :=
  (Submodule.span ℂ {f : B(S) | inBand(K, f)}).map (Π(hST))

/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
Every test in the Fourier level is the insertion of a single small-stage test
satisfying both Fourier-support conditions.
Deviation: The insertion uses the integer-ring indicators of (2.1.4.2). -/
theorem mem_sLocalPWTests (hST : S ⊆ T) (K : Set (SAdeleRing F S)) (f : B(T)) :
    f ∈ sLocalPWTests hST K ↔ ∃ g : B(S), Π(hST) g = f ∧ inBand(K, g) := by sorry

/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
The two moments on the inserted test space can be specified independently whenever
the Fourier region contains a neighborhood of zero, as both positive levels do.
Deviation: This uses the integer-ring transition. -/
theorem sLocalPWTests_moments_surjective (hST : S ⊆ T) (K : Set (SAdeleRing F S))
    (hK : K ∈ 𝓝 0) (a b : ℂ) :
    ∃ f ∈ sLocalPWTests hST K, f (Multiplicative.ofAdd 0) = a ∧
      sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = b := by sorry

local notation "level(" h ", " K ", " D ", " ω ")" =>
  (((sLocalPWTests h K ⊓ D).map (q(_, ω))).topologicalClosure)

/-- Paper: Definition 7.3.2.1(2), p. 351.
The absolute PW level is the closure of the theta image of box-limited tests.
The test constraint is the whole space or the common kernel of the two zero evaluations.
Deviation: Uses the integer-ring insertion of the cited transition. -/
def sLocalAbsolutePW (hST : S ⊆ T) (X : ℝ) (D : Submodule ℂ (B(T)))
    (ω : PontryaginDual J₁(T)) : Submodule ℂ (Θ(T, ω)) :=
  level(hST, sLocalPWBox S X, D, ω)

/-- Paper: Definition 7.3.2.1(2), p. 351.
The theta class of an inserted box-limited test satisfying the chosen test constraint
belongs to the absolute level.
Deviation: Uses the integer-ring insertion of the cited transition. -/
theorem sLocalAbsolutePW_mk_mem (hST : S ⊆ T) (X : ℝ) (D : Submodule ℂ (B(T)))
    (ω : PontryaginDual J₁(T)) (f : B(S)) (_hf : inBand(sLocalPWBox S X, f))
    (_hD : Π(hST) f ∈ D) : q(T, ω) (Π(hST) f) ∈ sLocalAbsolutePW hST X D ω := by sorry

section AbsoluteLevels

open Classical

/-- Paper: Proposition 7.3.2.2(1), p. 352.
Increasing the box size enlarges each of the two absolute PW levels. -/
theorem sLocalAbsolutePW_mono (hST : S ⊆ T) {X Y : ℝ} (_hXY : X ≤ Y)
    (D : Submodule ℂ (B(T))) (ω : PontryaginDual J₁(T)) :
    sLocalAbsolutePW hST X D ω ≤ sLocalAbsolutePW hST Y D ω := by sorry

/-- Paper: Proposition 7.3.2.2(1), p. 352.
The union of the absolute PW levels is sequentially dense in the full or zero-moment
homogeneous theta space, according to the chosen test constraint.
Deviation: Uses integer-ring insertion, as required by the density argument and §6.2. -/
theorem sLocalAbsolutePW_seqDense {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀)
    (_hPic : PicTrivial) (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu))
    (D : Submodule ℂ (B(T))) (_hD : D = ⊤ ∨ D = Z₀(T)) :
    ∀ (x : Θ(T, χ)), x ∈ D.map (q(T, χ)) → ∃ u : ℕ → Θ(T, χ),
      (∀ n, ∃ X > 0, u n ∈ sLocalAbsolutePW hST X D χ) ∧
        Tendsto u atTop (𝓝 x) := by sorry

/-- Paper: Proposition 7.3.2.2(2), p. 352.
At fixed finite stages, global theta of every inserted zero-moment test at this absolute
level vanishes below a uniform positive idelic norm. -/
theorem sLocalAbsolutePW_globalSupport {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀)
    (_hPic : PicTrivial) (ω : PontryaginDual C₁) (_hu : NormOneCharacterUnramifiedOutside ω S)
    (X : ℝ) (_hX : 0 < X) :
    ∃ bound > (0 : ℝ), ∀ (f : B(T)), f ∈ sLocalPWTests hST (sLocalPWBox S X) ⊓ Z₀(T) →
      tsupport (homogeneousAdelicTheta ω (sAdeleSchwartzToGlobal F T f)) ⊆
        {g | bound⁻¹ ≤ ((ideleClassNorm F g).val : ℝ)} := by sorry

/-- Paper: Proposition 7.3.2.2(3), p. 352.
The local homogeneous theta of the Fourier-transformed level tests has a uniform upper
norm bound.
Deviation: Part (3) leaves the test variable free. The Fourier support bound applies to
every band-limited input, since the product norm bounds each contributing orbit. -/
theorem sLocalAbsolutePW_localFourierSupport {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀)
    (_hPic : PicTrivial) (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu))
    (X : ℝ) (_hX : 0 < X) :
    ∃ bound > (0 : ℝ), ∀ (f : B(T)), f ∈ sLocalPWTests hST (sLocalPWBox S X) →
      tsupport (sLocalHomogeneousAdelicThetaLinearMap F T χ (sAdeleSchwartzFourier f)) ⊆
          {g | ((m(T) g).val : ℝ) ≤ bound} := by sorry

end AbsoluteLevels

/-- Paper: Proposition 7.3.2.2(4), p. 352.
Left translation by an idele class of norm at least one preserves the absolute levels,
with or without the zero-moment constraint.
Deviation: Stated directly for the local norm-one character and the inclusion of stages.
The preservation uses no class-number assumption. -/
theorem sLocalAbsolutePW_translate (hST : S ⊆ T) {X : ℝ} (_hX : 0 < X)
    (D : Submodule ℂ (B(T))) (_hD : D = ⊤ ∨ D = Z₀(T))
    (ω : PontryaginDual J₁(T)) (g : J(T)) (_hg : large(g))
    (x : Θ(T, ω)) (_hx : x ∈ sLocalAbsolutePW hST X D ω) :
    A(T, ω) g x ∈ sLocalAbsolutePW hST X D ω := by sorry

/-- Paper: Definition 7.3.2.3(1), p. 354–355.
The invariant Fourier region bounds the product of the normalized local absolute values,
including at tuples having a zero coordinate. -/
def sLocalPWProductRegion (S : Finset V) (Y : ℝ) : Set (SAdeleRing F S) :=
  {x | (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) * (∏ v : S, ‖x.2 v‖) ≤ Y}

/-- Paper: Definition 7.3.2.3(1), p. 355.
On invertible adeles the product bound is the S-idelic norm bound. -/
theorem mem_sLocalPWProductRegion_units (Y : ℝ) (u : (SAdeleRing F S)ˣ) :
    u.val ∈ sLocalPWProductRegion S Y ↔ ((sIdeleNorm F S u).val : ℝ) ≤ Y := by sorry

/-- Paper: Definition 7.3.2.3(2), p. 355.
The invariant PW level is the closure of the theta image of tests with compact Fourier
support in the product region, optionally subject to the zero-moment constraint.
Deviation: Uses the cited integer-ring insertion and the unrestricted test space for
the unrestricted level. The sentence after (7.3.2.17) repeats the zero-moment space. -/
def sLocalInvariantPW (hST : S ⊆ T) (Y : ℝ) (D : Submodule ℂ (B(T)))
    (ω : PontryaginDual J₁(T)) : Submodule ℂ (Θ(T, ω)) :=
  level(hST, sLocalPWProductRegion S Y, D, ω)

/-- Paper: Definition 7.3.2.3(2), p. 355.
An inserted test with compact Fourier support in the product region and satisfying the
chosen test constraint represents an element of the invariant level.
Deviation: Uses the integer-ring insertion of the cited transition. -/
theorem sLocalInvariantPW_mk_mem (hST : S ⊆ T) (Y : ℝ) (D : Submodule ℂ (B(T)))
    (ω : PontryaginDual J₁(T)) (f : B(S)) (_hf : inBand(sLocalPWProductRegion S Y, f))
    (_hD : Π(hST) f ∈ D) : q(T, ω) (Π(hST) f) ∈ sLocalInvariantPW hST Y D ω := by sorry

/-- Paper: Proposition 7.3.2.4(1), p. 355.
Increasing the product bound enlarges each of the two invariant PW levels. -/
theorem sLocalInvariantPW_mono (hST : S ⊆ T) {Y Y' : ℝ} (_hYY' : Y ≤ Y')
    (D : Submodule ℂ (B(T))) (ω : PontryaginDual J₁(T)) :
    sLocalInvariantPW hST Y D ω ≤ sLocalInvariantPW hST Y' D ω := by sorry

section InvariantLevels

open Classical

/-- Paper: Proposition 7.3.2.4(1), p. 356.
The union of the invariant PW levels is sequentially dense in the corresponding
full or zero-moment homogeneous theta space.
Deviation: Uses integer-ring insertion, as in the density proof. -/
theorem sLocalInvariantPW_seqDense {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀)
    (_hPic : PicTrivial) (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu))
    (D : Submodule ℂ (B(T))) (_hD : D = ⊤ ∨ D = Z₀(T)) :
    ∀ (x : Θ(T, χ)), x ∈ D.map (q(T, χ)) → ∃ u : ℕ → Θ(T, χ),
      (∀ n, ∃ Y > 0, u n ∈ sLocalInvariantPW hST Y D χ) ∧
        Tendsto u atTop (𝓝 x) := by sorry

/-- Paper: Proposition 7.3.2.4(2), p. 356.
At fixed finite stages, the global theta of the invariant zero-moment level tests has
a uniform positive lower idelic norm bound. -/
theorem sLocalInvariantPW_globalSupport {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀)
    (_hPic : PicTrivial) (ω : PontryaginDual C₁) (_hu : NormOneCharacterUnramifiedOutside ω S)
    (Y : ℝ) (_hY : 0 < Y) :
    ∃ bound > (0 : ℝ), ∀ (f : B(T)), f ∈ sLocalPWTests hST (sLocalPWProductRegion S Y) ⊓ Z₀(T) →
      tsupport (homogeneousAdelicTheta ω (sAdeleSchwartzToGlobal F T f)) ⊆
        {g | bound⁻¹ ≤ ((ideleClassNorm F g).val : ℝ)} := by sorry

end InvariantLevels

/-- Paper: Proposition 7.3.2.4(3), p. 356.
Left translation by an idele class of norm at least one preserves the invariant levels,
with or without the zero-moment constraint.
Deviation: Stated directly for the local norm-one character and the inclusion of stages. -/
theorem sLocalInvariantPW_translate (hST : S ⊆ T) {Y : ℝ} (_hY : 0 < Y)
    (D : Submodule ℂ (B(T))) (_hD : D = ⊤ ∨ D = Z₀(T))
    (ω : PontryaginDual J₁(T)) (g : J(T)) (_hg : large(g))
    (x : Θ(T, ω)) (_hx : x ∈ sLocalInvariantPW hST Y D ω) :
    A(T, ω) g x ∈ sLocalInvariantPW hST Y D ω := by sorry

/-- Paper: Proposition 7.3.2.4(4), p. 356.
The coordinate box bound implies the product bound with exponent the total number of places.
Both the unrestricted and the zero-moment level use the same comparison. -/
theorem sLocalAbsolutePW_le_invariant (hST : S ⊆ T) (X : ℝ) (_hX : 0 < X)
    (D : Submodule ℂ (B(T))) (ω : PontryaginDual J₁(T)) :
    sLocalAbsolutePW hST X D ω ≤ sLocalInvariantPW hST (X ^ count(S)) D ω := by sorry

section PrincipalValues

open Classical

local notation "absPW(" h ", " b ", " ω ")" => sLocalAbsolutePW h b (Z₀(_)) ω
local notation "invPW(" h ", " b ", " ω ")" => sLocalInvariantPW h b (Z₀(_)) ω

/-- Paper: Proposition 7.3.3.2, p. 357–358.
The finite principal value maps the zero-moment absolute level at X into the
absolute level at the product of the residue sizes times X. -/
theorem sLocalAbsolutePW_principalValue {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (hRT : R ⊆ T) (_hR : R ⊆ S₀) (_hsatR : IsSaturatedPlaceSet (F := F) R)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀) (_hPic : PicTrivial)
    (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu))
    (X : ℝ) (_hX : 0 < X) :
    (absPW(hST, X, χ)).map (PV(hRT, χ)) ≤ absPW(hST, size(R) * X, χ) := by sorry

/-- Paper: Proposition 7.3.3.2, p. 357–358.
The finite principal value maps the zero-moment invariant level at Y into the
invariant level at the product of the residue sizes times Y. -/
theorem sLocalInvariantPW_principalValue {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (hRT : R ⊆ T) (_hR : R ⊆ S₀) (_hsatR : IsSaturatedPlaceSet (F := F) R)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀) (_hPic : PicTrivial)
    (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu))
    (Y : ℝ) (_hY : 0 < Y) :
    (invPW(hST, Y, χ)).map (PV(hRT, χ)) ≤ invPW(hST, size(R) * Y, χ) := by sorry

/-- Paper: Proposition 7.3.3.2, p. 358.
There are inclusions along both rows of the PW diagram. The restrictions of the
ambient principal value are continuous and commute with the translations.
Deviation: The lower row needs its own level comparison. The commutative squares
can be read by composing the restrictions with the inclusions into the ambient space. -/
theorem sLocalPW_principalValue_diagram {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (hRT : R ⊆ T) (_hR : R ⊆ S₀) (_hsatR : IsSaturatedPlaceSet (F := F) R)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀) (_hPic : PicTrivial)
    (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu))
    (X Y : ℝ) (_hX : 0 < X) (_hY : 0 < Y) (_hXY : X ^ count(S) ≤ Y)
    (_hXY' : (size(R) * X) ^ count(S) ≤ size(R) * Y) :
    let a := absPW(hST, X, χ)
    let a' := absPW(hST, size(R) * X, χ)
    let b := invPW(hST, Y, χ)
    let b' := invPW(hST, size(R) * Y, χ)
    a ≤ b ∧ a' ≤ b' ∧ b ≤ (Z₀(T)).map (q(T, χ)) ∧ b' ≤ (Z₀(T)).map (q(T, χ)) ∧
      ∃ (P : a →L[ℂ] a') (P' : b →L[ℂ] b'),
        (∀ x : a, (P x).val = PV(hRT, χ) x.val) ∧
        (∀ x : b, (P' x).val = PV(hRT, χ) x.val) ∧
        ∀ (g : J(T)), 1 ≤ ((m(T) g).val : ℝ) →
          ∀ x : (Z₀(T)).map (q(T, χ)),
            PV(hRT, χ) (A(T, χ) g x.val) = A(T, χ) g (PV(hRT, χ) x.val) := by sorry

end PrincipalValues

section PWOrbitalQuotients

open Classical

local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "Rₚ(" p ", " ω ")" => sLocalPrimaryOrbitalSubmodule (F := F) (S := T) p ω
local notation "Qₚ(" p ", " ω ")" => SLocalPrimaryOrbitalQuotient (F := F) (S := T) p ω
local notation "Iₚ(" p ", " ω ")" => SLocalOrbitalIndex (F := F) (S := T)
  (sLocalPrimaryPlaces (F := F) T p) ω

local notation "PVₚ(" p ", " ω ")" =>
  PV((sLocalPrimaryPlaces_subset (F := F) T p), ω)
local notation "Rₚ₀(" p ", " ω ")" =>
  (((Z₀(T)).map (q(T, ω))).map (PVₚ(p, ω)))

/-- Paper: Definition 7.3.3.3(1)–(2), p. 359, and (7.3.3.18)–(7.3.3.19), p. 361.
The denominator inside the level consists of principal values with a zero-moment preimage.
Deviation: Uses the intersection from the proof on p. 361. The displayed quotients on
p. 359 require a containment that fails even for one added rational prime. -/
abbrev SLocalPWOrbitalQuotient (ω : PontryaginDual J₁(T)) (p : Vℚ)
    (W : Submodule ℂ (Θ(T, ω))) :=
  W ⧸ (Rₚ₀(p, ω)).comap W.subtype

/-- Paper: Equations (7.3.3.18)–(7.3.3.19), p. 361.
A class vanishes precisely when its vector is the principal value of a zero-moment class. -/
theorem sLocalPWOrbitalQuotient_mk_eq_zero (ω : PontryaginDual J₁(T)) (p : Vℚ)
    (W : Submodule ℂ (Θ(T, ω))) (x : W) :
    ((Rₚ₀(p, ω)).comap W.subtype).mkQ x = (0 : SLocalPWOrbitalQuotient ω p W) ↔
      ∃ y ∈ (Z₀(T)).map (q(T, ω)), PVₚ(p, ω) y = x.val := by sorry

local notation "absPW(" h ", " b ", " ω ")" => sLocalAbsolutePW h b (Z₀(_)) ω
local notation "invPW(" h ", " b ", " ω ")" => sLocalInvariantPW h b (Z₀(_)) ω

-- TODO(paper-gap): At c = 1 both the order-zero Fourier jet and the top Laurent
-- coefficient vanish on zero-moment classes. Theorem 7.3.3.4 does not supply a
-- biorthogonal system for the shifted coefficient range of Corollary 7.2.2.2.
-- A restricted quotient can also contain a nonzero class in the kernel of its
-- map to the unrestricted ambient quotient at this character.

-- TODO(paper-gap): The argument on p. 363 needs a single Fourier support bound for
-- lifts of the full compact-window quotient. Pointwise existence of test representatives
-- in Proposition 5.3.4.4 does not supply that bound.
-- The basis and growth statements in §7.3.1 assume saturation of the whole target T.
-- To use them for an unsaturated base S, their proofs must be localized to the fiber over p.

/-- Paper: Theorem 7.3.3.4 and its proof, pp. 360–363.
For sufficiently large levels the inclusion induces the isomorphism used to transfer
the two bases and the Fourier seminorm bounds.
Deviation: Uses zero-moment principal-value preimages and a nontrivial component. -/
theorem sLocalPWOrbital_eventually_equiv {S₀ : Finset V} (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀) (_hPic : PicTrivial)
    (p : Vℚ) (_hp : (sLocalPrimaryPlaces (F := F) T p).Nonempty)
    (_hp₀ : sLocalPrimaryPlaces (F := F) T p ⊆ S₀)
    (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu)) (_hω : ω ≠ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ X Y : ℝ, B ≤ X → B ≤ Y → X ^ count(S) ≤ Y →
      ∀ (W : Submodule ℂ (Θ(T, χ))), (W = absPW(hST, X, χ) ∨ W = invPW(hST, Y, χ)) →
        ∃ e : SLocalPWOrbitalQuotient χ p W ≃L[ℂ] Qₚ(p, χ),
          ∀ x : W, e (((Rₚ₀(p, χ)).comap W.subtype).mkQ x) = (Rₚ(p, χ)).mkQ x.val := by sorry

/-- Paper: Theorem 7.3.3.4(1)–(2), pp. 360–361.
For sufficiently large absolute or invariant levels, with the same enumeration
as the ambient system, the restricted functionals are an unconditional dual basis
and their biorthogonal lifts are an absolute quotient basis.
Deviation: Uses the intersections from (7.3.3.18)–(7.3.3.19) and a nontrivial
norm-one character. At the trivial character an ambient Fourier functional
restricts to zero. The pole orders use the S′-local Mellin transform and order k selects
Laurent exponent −k in the signed convention of Definition 7.1.2.1. -/
theorem sLocalPWOrbital_bases {S₀ : Finset V} (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀) (_hPic : PicTrivial)
    (p : Vℚ) (_hp : (sLocalPrimaryPlaces (F := F) T p).Nonempty)
    (_hp₀ : sLocalPrimaryPlaces (F := F) T p ⊆ S₀)
    (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu)) (_hω : ω ≠ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ X Y : ℝ, B ≤ X → B ≤ Y → X ^ count(S) ≤ Y →
      ∀ (W : Submodule ℂ (Θ(T, χ))), (W = absPW(hST, X, χ) ∨ W = invPW(hST, Y, χ)) →
      ∀ (L : Iₚ(p, χ) → StrongDual ℂ (Θ(T, χ))),
        (L = sLocalOrbitalPrincipalPart (F := F) (S := T) ∨
          L = sLocalOrbitalFourierJet (F := F) (S := T)) →
        ∀ (σ : ℕ ≃ Iₚ(p, χ)),
          ∃ (d : ℕ → StrongDual ℂ (Qₚ(p, χ))) (e : ℕ → Qₚ(p, χ))
            (dW : ℕ → StrongDual ℂ (SLocalPWOrbitalQuotient χ p W))
            (eW : ℕ → SLocalPWOrbitalQuotient χ p W)
            (ev : ℕ → StrongDual ℂ (StrongDual ℂ (SLocalPWOrbitalQuotient χ p W))),
            (∀ n x, d n ((Rₚ(p, χ)).mkQ x) = L (σ n) x) ∧ IsSchauderBasis e d ∧
            (∀ n (x : W), dW n (((Rₚ₀(p, χ)).comap W.subtype).mkQ x) = L (σ n) x.val) ∧
            (∀ n, ∃ x : W, ((Rₚ₀(p, χ)).comap W.subtype).mkQ x = eW n ∧
              (Rₚ(p, χ)).mkQ x.val = e n) ∧
            (∀ n ℓ, ev n ℓ = ℓ (eW n)) ∧
            IsSchauderBasis dW ev ∧ SchauderBasis.IsUnconditional dW ev ∧
            IsSchauderBasis eW dW ∧ SchauderBasis.IsAbsolute eW dW := by sorry

/-- Paper: Theorem 7.3.3.4(3), p. 361.
Fourier-biorthogonal vectors of either sufficiently large level satisfy a polynomial
bound for each continuous seminorm along each pole lattice, uniformly in the jet order.
Deviation: Uses the nontrivial components of the repaired basis theorem. -/
theorem sLocalPWOrbital_biorthogonal_growth {S₀ : Finset V} (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀) (_hPic : PicTrivial)
    (p : Vℚ) (_hp : (sLocalPrimaryPlaces (F := F) T p).Nonempty)
    (_hp₀ : sLocalPrimaryPlaces (F := F) T p ⊆ S₀)
    (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu)) (_hω : ω ≠ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ X Y : ℝ, B ≤ X → B ≤ Y → X ^ count(S) ≤ Y →
      ∀ (W : Submodule ℂ (Θ(T, χ))), (W = absPW(hST, X, χ) ∨ W = invPW(hST, Y, χ)) →
        ∀ (ψ : Iₚ(p, χ) → SLocalPWOrbitalQuotient χ p W),
          (∀ (i j : Iₚ(p, χ)) (x : W), ((Rₚ₀(p, χ)).comap W.subtype).mkQ x = ψ j →
            sLocalOrbitalFourierJet (F := F) (S := T) i x.val = if i = j then 1 else 0) →
          ∀ (v : T), v.val ∈ sLocalPrimaryPlaces (F := F) T p →
          ∀ (c₀ : QuasiCharacter J(T)),
            (∃ j : Iₚ(p, χ), j.val.1 = c₀ ∧ v ∈ sLocalFinitePolePlaces (F := F) (S := T) c₀) →
          ∀ q : Seminorm ℂ (SLocalPWOrbitalQuotient χ p W), Continuous q →
            ∃ d : ℕ, ∃ C > (0 : ℝ), ∀ (n : ℤ) (j : Iₚ(p, χ)),
              j.val.1 = quasiCharacterNormTwist (m(T))
                (isProperMap_sIdeleQuotientNorm F T).continuous c₀
                (((n : ℝ) * (2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)) : ℝ) * Complex.I) →
              q (ψ j) ≤ C * (1 + |(n : ℝ)|) ^ d := by sorry

open Classical in
/-- Paper: Theorem 7.3.3.4(3), p. 361.
Fourier coefficients of each class in a PW orbital quotient decay as a Schwartz
sequence along each local pole lattice at fixed derivative order.
Deviation: Uses the intersection quotient from the proof and the same zero-extension
convention as Theorem 7.3.1.6(5). The lattice is based at any pole at the chosen place. -/
theorem sLocalPWOrbital_fourier_decay (p : Vℚ) (ω : PontryaginDual J₁(T))
    (W : Submodule ℂ (Θ(T, ω)))
    (d : Iₚ(p, ω) → StrongDual ℂ (SLocalPWOrbitalQuotient ω p W))
    (_hd : ∀ j (x : W), d j (((Rₚ₀(p, ω)).comap W.subtype).mkQ x) =
      sLocalOrbitalFourierJet (F := F) (S := T) j x.val)
    (v : T) (_hv : v.val ∈ sLocalPrimaryPlaces (F := F) T p)
    (c₀ : QuasiCharacter J(T))
    (_hc₀ : ∃ j : Iₚ(p, ω), j.val.1 = c₀ ∧ v ∈ sLocalFinitePolePlaces (F := F) (S := T) c₀)
    (k : ℕ) (x : SLocalPWOrbitalQuotient ω p W) :
    let c := fun n : ℤ ↦ quasiCharacterNormTwist (m(T))
      (isProperMap_sIdeleQuotientNorm F T).continuous c₀
      (((n : ℝ) * (2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)) : ℝ) * Complex.I)
    ∃ a : SchwartzBruhat (Multiplicative ℤ), ∀ n : ℤ,
      (∀ j : Iₚ(p, ω), j.val = (c n, k) → a (Multiplicative.ofAdd n) = d j x) ∧
      ((¬ ∃ j : Iₚ(p, ω), j.val = (c n, k)) → a (Multiplicative.ofAdd n) = 0) := by sorry

/-- Paper: Equation (7.3.3.25), p. 363.
For a nontrivial norm-one character the tests with both zero moments
have the same homogeneous theta image as the unrestricted tests. -/
theorem sLocalZeroMomentTheta_eq_top (ω : PontryaginDual J₁(T)) (_hω : ω ≠ 1) :
    (Z₀(T)).map (q(T, ω)) = ⊤ := by sorry

end PWOrbitalQuotients

section ArchimedeanPoles

local notation "Xₛ" => QuasiCharacter J(S)
local notation "fullPV(" ω ")" => (PV((Finset.Subset.refl S), ω)).range
local notation "noPoles(" ω ")" => sLocalThetaPoleBound (F := F) (S := S) ω (fun _ ↦ 0)
local notation "chart(" c ")" => quasiCharacterNormTwist (m(S))
  (isProperMap_sIdeleQuotientNorm F S).continuous c
local notation "shift(" c ", " z ")" => chart(c) z
local notation "arch(" c ")" => sLocalArchPolePlaces (F := F) (S := S) c
local notation "depths" => (InfinitePlace F → ℕ)

/-- Paper: Notation 7.3.4.1, p. 364.
The selected centers on a component are among the first specified number of poles
at one or more archimedean places, starting at the rightmost pole.
Deviation: The real and complex cutoff tuples are combined into a single
place-indexed family. Local poles are ranked by positive real norm shifts, so a
cutoff of n includes n + 1 local poles. -/
def sLocalGammaPoleCutoff (ω : PontryaginDual J₁(S)) (N : depths) : Set Xₛ :=
  {c | onComponent(c, ω) ∧
    ∃ w ∈ arch(c), ({t : ℝ | 0 < t ∧ w ∈ arch(shift(c, (t : ℂ)))} : Set ℝ).encard ≤ N w}

variable (S) in
/-- Paper: Notation 7.3.4.1, p. 364.
The zero cutoff selects the trivial quasi-character on the trivial component
and excludes its shift down by two. -/
theorem sLocalGammaPoleCutoff_zero :
    (1 : Xₛ) ∈ sLocalGammaPoleCutoff (F := F) (S := S) 1 (fun _ ↦ 0) ∧
      shift((1 : Xₛ), (-2 : ℂ)) ∉ sLocalGammaPoleCutoff (F := F) (S := S) 1 (fun _ ↦ 0) := by sorry

local notation "ΓIndex(" ω ", " U ")" =>
  {j : Xₛ × ℕ // onComponent(j.1, ω) ∧ j.1 ∈ U ∧ 0 < j.2 ∧ j.2 ≤ (arch(j.1)).card}
local notation "ΓCoeff(" ω ", " j ")" =>
  ((sLocalThetaPrincipalPartCoeff (F := F) (S := S) ω (j).val.1 (j).property.1 (j).val.2).comp
    (fullPV(ω)).subtypeL)

/-- Paper: Notation 7.3.4.1, p. 364.
The filtered subspace of the full finite principal-value image has no poles at
the selected archimedean centers. It carries the induced topology.
Deviation: Cutoffs are indexed by places. Increasing all local cutoffs gives
the filtration inclusions. -/
def sLocalGammaFiltration (ω : PontryaginDual J₁(S)) (N : depths) :
    Submodule ℂ (fullPV(ω)) :=
  ⨅ j : ΓIndex(ω, sLocalGammaPoleCutoff (F := F) (S := S) ω N), (ΓCoeff(ω, j)).ker

/-- Paper: Notation 7.3.4.1, p. 364.
A class in the full finite principal-value image is in a filtered stage exactly
when its representative's Mellin transform has no poles at the selected centers. -/
theorem mem_sLocalGammaFiltration (ω : PontryaginDual J₁(S)) (N : depths)
    (x : fullPV(ω)) (f : B(S)) (_hf : q(S, ω) f = x.val) :
    x ∈ sLocalGammaFiltration ω N ↔
      ∀ c ∈ sLocalGammaPoleCutoff (F := F) (S := S) ω N,
        0 ≤ meromorphicOrderAt (fun z : ℂ ↦ sLocalIdelicZFunction f (shift(c, z))) 0 := by sorry

/-- Paper: Notation 7.3.4.1, p. 364.
The denominator of the archimedean polar quotient is the subspace with entire Mellin transform.
Deviation: Uses the equivalent zero-pole-bound model for the theta image of S₀₀ from §7.2. -/
def sLocalGammaEntireSubmodule (ω : PontryaginDual J₁(S)) : Submodule ℂ (fullPV(ω)) :=
  (noPoles(ω)).comap (fullPV(ω)).subtype

local notation "Γker(" ω ")" => sLocalGammaEntireSubmodule (F := F) (S := S) ω

/-- Paper: Notation 7.3.4.1, p. 364.
The archimedean polar quotient divides the full finite principal-value image
by the subspace with entire Mellin transform, and carries the quotient topology. -/
abbrev SLocalGammaOrbitalQuotient (ω : PontryaginDual J₁(S)) := fullPV(ω) ⧸ Γker(ω)

/-- Paper: Notation 7.3.4.1, p. 364.
A representative of the zero coset has a Mellin transform with no poles on the
component, and the entire-Mellin subspace consists of these representatives. -/
theorem mem_sLocalGammaEntireSubmodule (ω : PontryaginDual J₁(S))
    (x : fullPV(ω)) (f : B(S)) (_hf : q(S, ω) f = x.val) :
    x ∈ Γker(ω) ↔
      ∀ c : Xₛ, onComponent(c, ω) →
        0 ≤ meromorphicOrderAt (fun z : ℂ ↦ sLocalIdelicZFunction (F := F) (S := S) f (shift(c, z))) 0 :=
  by sorry

/-- Paper: Notation 7.3.4.1, p. 364.
The archimedean polar quotient is Fréchet. -/
theorem sLocalGammaOrbitalQuotient_frechet (ω : PontryaginDual J₁(S)) :
    let P := Γker(ω)
    @IsFrechetTVS _ (Submodule.Quotient.addCommGroup P) (Submodule.Quotient.module P)
      (QuotientModule.Quotient.topologicalSpace P) := by sorry

/-- Paper: Notation 7.3.4.1, p. 364.
The archimedean polar quotient is nuclear. -/
theorem sLocalGammaOrbitalQuotient_nuclear (ω : PontryaginDual J₁(S)) :
    let P := Γker(ω)
    @IsNuclearTVS _ (Submodule.Quotient.addCommGroup P) (Submodule.Quotient.module P)
      (QuotientModule.Quotient.topologicalSpace P) := by sorry

/-- Paper: Notation 7.3.4.1, p. 364.
Increasing all local cutoffs decreases the corresponding subspace.
Deviation: Uses the pointwise order. Lexicographic order need not give nested stages. -/
theorem sLocalGammaFiltration_antitone (ω : PontryaginDual J₁(S)) :
    Antitone (sLocalGammaFiltration ω) := by sorry

/-- Paper: Theorem 7.3.4.1(1), p. 364.
Each stage of the archimedean pole filtration is closed. -/
theorem sLocalGammaFiltration_isClosed (ω : PontryaginDual J₁(S)) (N : depths) :
    IsClosed (sLocalGammaFiltration ω N : Set (fullPV(ω))) := by sorry

-- TODO(paper-gap): The test list (7.3.4.9) does not separate the two coefficients
-- of a double real pole at cutoff (0,0). See ERRATA I169. Finite interpolation can
-- use translations of a test attaining the full pole order.

/-- Paper: Theorem 7.3.4.1(2), pp. 364–365.
The Laurent coefficients at the selected centers form a finite linearly independent family. -/
theorem sLocalGammaFiltration_coeff_independent (ω : PontryaginDual J₁(S)) (N : depths) :
    let U := sLocalGammaPoleCutoff (F := F) (S := S) ω N
    Finite (ΓIndex(ω, U)) ∧ LinearIndependent ℂ (fun j : ΓIndex(ω, U) ↦ ΓCoeff(ω, j)) := by sorry

/-- Paper: Theorem 7.3.4.1(2), p. 365.
The transposes of the linear functionals on the filtered quotient are precisely the
span of the selected Laurent coefficients on the principal-value space.
Deviation: The displayed positive order k in (7.3.4.4) selects Laurent exponent −k. -/
theorem sLocalGammaFiltration_dual_span (ω : PontryaginDual J₁(S)) (N : depths) :
    let stage := sLocalGammaFiltration (F := F) (S := S) ω N
    Set.range (fun ℓ : StrongDual ℂ ((fullPV(ω)) ⧸ stage) ↦ ℓ.comp stage.mkQL) =
      (Submodule.span ℂ (Set.range (fun j : ΓIndex(ω, sLocalGammaPoleCutoff (F := F) (S := S) ω N) ↦
        ΓCoeff(ω, j))) : Set (StrongDual ℂ (fullPV(ω)))) := by sorry

/-- Paper: Theorem 7.3.4.1(3), p. 365.
The intersection of all stages is the entire-Mellin subspace. -/
theorem sLocalGammaFiltration_iInf (ω : PontryaginDual J₁(S)) :
    (⨅ N : depths, sLocalGammaFiltration ω N) = Γker(ω) := by sorry

-- TODO(paper-gap): ERRATA I168 applies to the appeal to §5.4 on p. 365.
-- Finite interpolation only gives a dense coefficient image in the product topology.
-- Simultaneous realization in the original space is a separate proof obligation.

/-- Paper: Theorem 7.3.4.1(4), p. 365.
Every array of archimedean principal parts on the component is realized by one
class in the full finite principal-value range.
Deviation: States explicitly the interpolation needed for the canonical product model. -/
theorem sLocalGamma_all_coeff_surjective (ω : PontryaginDual J₁(S)) :
    Function.Surjective (fun (x : fullPV(ω)) (j : ΓIndex(ω, (Set.univ : Set Xₛ))) ↦
      ΓCoeff(ω, j) x) := by sorry

/-- Paper: Theorem 7.3.4.1(4), p. 365.
The quotient topology is induced by the family of canonical finite-cutoff quotient maps. -/
theorem sLocalGammaOrbitalQuotient_projectiveTopology (ω : PontryaginDual J₁(S)) :
    let E := ↥(fullPV(ω))
    let P := Γker(ω)
    let stage := sLocalGammaFiltration (F := F) (S := S) ω
    ∃ qN : (N : depths) → (E ⧸ P) →ₗ[ℂ] (E ⧸ stage N),
      (∀ N (x : E), qN N (P.mkQ x) = (stage N).mkQ x) ∧
      IsInducing (fun (x : E ⧸ P) (N : depths) ↦ qN N x) := by sorry

/-- Paper: Theorem 7.3.4.1(4), p. 365.
The quotient is topologically linearly isomorphic to the product of complex
lines indexed by cutoff tuples. -/
theorem sLocalGammaOrbitalQuotient_product (ω : PontryaginDual J₁(S)) :
    let E := ↥(fullPV(ω))
    let P := Γker(ω)
    Nonempty ((E ⧸ P) ≃L[ℂ] (depths → ℂ)) := by sorry

/-- Paper: Theorem 7.3.4.1(4), p. 365.
The strong dual of the quotient is topologically linearly isomorphic to the
direct sum of complex lines with its finest locally convex topology.
The quotient dual represents the annihilator via pullback along the quotient map. -/
theorem sLocalGammaOrbitalQuotient_dual_directSum (ω : PontryaginDual J₁(S)) :
    let E := ↥(fullPV(ω))
    let P := Γker(ω)
    Nonempty (StrongDual ℂ (E ⧸ P) ≃L[ℂ] FinestLocallyConvex (depths →₀ ℂ)) := by sorry

/-- Paper: Theorem 7.3.4.1(5), pp. 365–366.
The set of archimedean centers with their admissible Laurent orders admits an enumeration. -/
theorem sLocalGammaIndex_enumerable (ω : PontryaginDual J₁(S)) :
    Nonempty (ℕ ≃ ΓIndex(ω, (Set.univ : Set Xₛ))) := by sorry

/-- Paper: Theorem 7.3.4.1(5), p. 365.
In every enumeration, the archimedean Laurent coefficients descend to a
Schauder basis of the strong dual of the archimedean polar quotient.
Deviation: Uses the coefficient of exponent −k for order k in (7.3.4.8). -/
theorem sLocalGammaOrbitalQuotient_dual_basis (ω : PontryaginDual J₁(S))
    (σ : ℕ ≃ ΓIndex(ω, (Set.univ : Set Xₛ))) :
    let E := ↥(fullPV(ω))
    let P := Γker(ω)
    ∃ (a : ℕ → StrongDual ℂ (E ⧸ P)) (d : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ P))),
      (∀ n (x : E), a n (P.mkQ x) = ΓCoeff(ω, (σ n)) x) ∧
      IsSchauderBasis a d := by sorry

end ArchimedeanPoles

end RiemannMasullo
