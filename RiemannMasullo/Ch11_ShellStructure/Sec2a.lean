module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # Orbital Markushevich bases on the 0-line

Masullo, §11.2 before §11.2.1, pp. 483–487.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "W(" s ")" => CompactIntervalSobolev μ𝔽 logNorm 0 0 s
local notation "W'(" s ")" => CompactIntervalSobolev μ𝔽 logNorm 0 0 s true
local notation "μ'(" s ")" => (μ𝔽).withDensity (fun g ↦
  ENNReal.ofReal (intervalSobolevDensity 0 0 (s) (logNorm g))⁻¹)
local notation "hI" => (le_rfl (a := (0 : ℝ)))
local notation "H(" a ", " hs ")" => globalThetaSobolev F a hI hs
local notation "j(" a ", " hs ")" => globalThetaSobolevInclusion F a hI hs
local notation "ρ(" hs ")" => hardySobolevTranslation μ𝔽 m𝔽 0 0 _ hI hs
local notation "Wω(" hs ", " ω ")" =>
  actionIsotype ((ρ(hs)).comp (ideleClassNorm F).ker.subtype) ω
local notation "restriction" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
local notation "ℬ₀" => ↥(adelePolarSubspace F)
local notation "jet(" χ ", " t ", " m ")" => spectralZeroJet χ 0 t m
local notation "frequency(" t ")" => ((t : ℝ) : ℂ) * Complex.I
local notation "q(" v ")" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v))

-- (11.2.0.1) is spectralSobolevPairing at the interval [0, 0].
-- (11.2.0.2) recalls the quotient operator globalThetaPrincipalValue.

/-- Paper: (11.2.0.2), p. 484. The global principal value preserves the two
vanishing conditions on adelic tests, so it acts on the polar-free theta space. -/
theorem adelePrincipalValue_mem_polarSubspace (S : Finset V) (f : ℬ₀) :
    adelePrincipalValue F S f.val ∈ adelePolarSubspace F := by sorry

local notation "pvTest(" S ", " f ")" =>
  (⟨adelePrincipalValue F S (f : ℬ₀).val, adelePrincipalValue_mem_polarSubspace S f⟩ : ℬ₀)
local notation "theta(" f ")" =>
  (Submodule.Quotient.mk (f : ℬ₀) : GlobalPolarFreeThetaSpace F)

-- TODO(paper-gap): The proof of density uses §10.2.1's passage from the
-- test-space Mellin image to an annihilator in the completed norm.
-- The cited Theorem 10.2.1.1 assumes s > 1. For 0 ≤ s ≤ 1, density in degree
-- 2 descends through the dense inclusion of weighted spaces by log-norm cutoff.

/-- Paper: Proposition 11.2.0.1, p. 484. The polar-free theta classes are norm
dense in the full global Sobolev space on the 0-line. -/
theorem denseRange_globalTheta_zeroLine {s : ℝ} (hs : 0 ≤ s) :
    DenseRange (fun u : GlobalPolarFreeThetaSpace F ↦ (j(0, hs) u : W(s))) := by sorry

/-- Paper: Proposition 11.2.0.1(1), p. 484. The principal-value operator
is bounded in the norm induced on unweighted theta classes.
Deviation: The operator uses finite places as in (11.2.0.2) and the global
norm (10.1.1.6), since (10.1.1.5) is S-local. -/
theorem globalThetaPrincipalValue_sobolevBound (S : Finset V) {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℬ₀,
      ‖j(0, hs) (theta(pvTest(S, f)))‖ ≤ C * ‖j(0, hs) (theta(f))‖ := by sorry

/-- Paper: Proposition 11.2.0.1(2) and (11.2.0.4), pp. 484–485.
The principal value has a unique bounded extension to the global theta completion.
Deviation: Continuity, without closed range, is stated here for every
nonnegative degree and every norm twist as in the paragraph before the proposition. -/
theorem existsUnique_globalThetaSobolevPrincipalValue (S : Finset V) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    ∃! P : H(a, hs) →L[ℂ] H(a, hs), ∀ f : ℬ₀,
      P (j(a, hs) (theta(f))) = j(a, hs) (theta(pvTest(S, f))) := by sorry

variable (F) in
/-- Paper: (11.2.0.4), p. 484. The completed principal-value map is the
continuous extension of the operator on adelic tests. -/
def globalThetaSobolevPrincipalValue (S : Finset V) (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    H(a, hs) →L[ℂ] H(a, hs) :=
  (existsUnique_globalThetaSobolevPrincipalValue S a hs).exists.choose

local notation "P(" S ", " a ", " hs ")" => globalThetaSobolevPrincipalValue F S a hs

/-- Paper: (11.2.0.4), p. 484. The extended operator agrees with its test formula
on each polar-free theta class. -/
theorem globalThetaSobolevPrincipalValue_apply (S : Finset V) (a : ℝ) {s : ℝ}
    (hs : 0 ≤ s) (f : ℬ₀) :
    P(S, a, hs) (j(a, hs) (theta(f))) = j(a, hs) (theta(pvTest(S, f))) := by sorry

/-- Paper: Lead-in to (11.2.0.3), p. 484. The extended principal value is injective.
Deviation: The inverse on its range can be discontinuous. -/
theorem globalThetaSobolevPrincipalValue_injective (S : Finset V) (a : ℝ) {s : ℝ}
    (hs : 0 ≤ s) : Injective (P(S, a, hs)) := by sorry

/-- Paper: Proposition 11.2.0.1(2), pp. 484–485. The extension commutes with
norm-one translations and hence preserves all norm-one isotypes.
Deviation: This compatibility is stated separately from closed range and holds
without the lower bound on the degree. -/
theorem globalThetaSobolevPrincipalValue_equivariant (S : Finset V) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) (k : C₁) (u : H(a, hs)) :
    let R := (exists_globalThetaSobolevAction (F := F) a hI hs).choose
    P(S, a, hs) (R k.val u) = R k.val (P(S, a, hs) u) := by sorry

/-- Paper: Proof of Proposition 11.2.0.1, pp. 484–485. At an unramified
singleton place, the 0-line extension is the difference with the uniformizer translate.
Deviation: The difference formula applies on the local-unit-invariant summand.
Unramified norm-one isotypes lie in that summand by §5.3. -/
theorem globalThetaSobolevPrincipalValue_singleton (v : V) (π : (v.adicCompletion F)ˣ)
    (_hπ : Valued.v.IsUniformizer π.val) (χ : PontryaginDual C𝔽)
    (_hχ : (ideleClassNormTwist χ 0).IsUnramifiedAt v) {s : ℝ} (hs : 0 ≤ s)
    (u : H(0, hs)) (_hu : (u : W(s)) ∈ Wω(hs, χ.comp restriction)) :
    (P({v}, 0, hs) u : W(s)) =
      (u : W(s)) - ρ(hs) (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π) u.val := by sorry

-- TODO(paper-gap): Proposition 11.2.0.1(2) identifies the raw range with a
-- closed subspace. The singleton prime difference over ℚ has nonclosed range.
-- The kernel argument on p. 485 also requires each zero's own multiplicity.
-- For S = {2,3} and trivial χ over ℚ, 2πi/log 2 is simple. The difference
-- kills Mellin evaluation there but need not kill the first derivative.

/-- Paper: (11.2.0.3), p. 484. The closure of the extension's range agrees with
the norm closure of the principal values of the polar-free theta tests.
Deviation: The range of the extension must also be closed up. -/
theorem globalThetaSobolevPrincipalValue_range_closure (S : Finset V) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    closure (range (P(S, a, hs))) =
      closure (range fun f : ℬ₀ ↦ j(a, hs) (theta(pvTest(S, f)))) := by sorry

/-- Paper: Theorem 11.2.0.2(1), p. 485. The reciprocal partial Euler
product is the product of the unramified factors in the phase coordinates
of §6.3.1. The complex argument is the norm-twist parameter.
Deviation: For PV on S use the product over S on both sides. The product
over the places of S above p gives the operator for that subset. The canonical
phase in [0, 2π/log q) is given by unramifiedHeckeCharacter_existsUnique_phase. -/
theorem orbitalEulerProduct_eq_phase (χ : PontryaginDual C𝔽) (S : Finset V) (t : V → ℝ)
    (_hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (_ht : ∀ v ∈ S, (ideleClassNormTwist χ 0).localValue v = (q(v) : ℂ) ^ (-frequency(t v)))
    (z : ℂ) :
    reciprocalPartialHeckeEulerProduct χ S z =
      ∏ v ∈ S, (1 - (q(v) : ℂ) ^ (-z - frequency(t v))) := by
  classical
  exact Finset.prod_congr rfl fun v hv ↦ finiteHeckeEulerFactor_inv_eq_phase χ v
    (_hχ v hv) (t v) (by simpa only [neg_mul] using _ht v hv) z

/-- Paper: Theorem 11.2.0.2(1), p. 485. The multiplicity is the order of the
reciprocal partial Euler product at the given point. -/
def orbitalEulerMultiplicity (χ : PontryaginDual C𝔽) (S : Finset V) (z : ℂ) : ℕ :=
  (meromorphicOrderAt (reciprocalPartialHeckeEulerProduct χ S) z).untop₀.toNat

open Classical in
/-- Paper: Theorem 11.2.0.2(1), p. 485. Each vanishing local factor contributes
one to the multiplicity, including when several places lie over the same prime. -/
theorem orbitalEulerMultiplicity_eq_card (χ : PontryaginDual C𝔽) (S : Finset V) (z : ℂ) :
    orbitalEulerMultiplicity χ S z =
      (S.filter fun v ↦ (finiteHeckeEulerFactor χ v z)⁻¹ = 0).card := by sorry

/-- Paper: Theorem 11.2.0.2(1), p. 485. For a unitary character unramified
at the selected places, every zero of the reciprocal product has real part zero.
The complex argument is the norm-twist parameter, independent of the Sobolev degree. -/
theorem orbitalEulerZero_re_eq_zero (χ : PontryaginDual C𝔽) (S : Finset V)
    (_hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) {z : ℂ}
    (_hz : reciprocalPartialHeckeEulerProduct χ S z = 0) : z.re = 0 := by
  classical
  have hprod : (∏ v ∈ S, (finiteHeckeEulerFactor χ v z)⁻¹) = 0 := _hz
  obtain ⟨v, hv, hzero⟩ := Finset.prod_eq_zero_iff.mp hprod
  rw [finiteHeckeEulerFactor, ite_eq_left (_hχ v hv), inv_inv, sub_eq_zero] at hzero
  have hq : 1 < (q(v) : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hn := congrArg (fun w : ℂ ↦ ‖w‖) hzero.symm
  simp only [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
    Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)),
    Complex.neg_re, norm_one] at hn
  have he : -z.re = 0 := (Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne').mp
    (hn.trans (Real.rpow_zero _).symm)
  exact neg_eq_zero.mp he

/-- Paper: Theorem 11.2.0.2(1)–(2) and (11.2.0.6), p. 485. Index jets by their
0-line ordinate and surviving log-power order.
Deviation: Use the strict reciprocal-weight integrability cutoff of §10.2,
which excludes a logarithmically divergent endpoint of the printed floor. -/
abbrev OrbitalJetIndex (χ : PontryaginDual C𝔽) (S : Finset V) (s : ℝ) :=
  {j : ℝ × ℕ //
    j.2 < spectralBoundaryMultiplicity s (orbitalEulerMultiplicity χ S (frequency(j.1)))}

/-- Paper: Theorem 11.2.0.2(1)–(2), p. 485. An admitted jet has a zero of the
reciprocal Euler product at its ordinate. -/
theorem OrbitalJetIndex.isZero {χ : PontryaginDual C𝔽} {S : Finset V} {s : ℝ}
    (j : OrbitalJetIndex χ S s) :
    reciprocalPartialHeckeEulerProduct χ S (frequency(j.val.1)) = 0 := by sorry

/-- Paper: Theorem 11.2.0.2 and (11.2.0.5), p. 485. Each admitted jet gives a
reciprocal-weight Sobolev vector.
Deviation: The cutoff excludes the divergent endpoint. -/
theorem orbitalJet_memLp (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ} (_hs : 0 ≤ s)
    (j : OrbitalJetIndex χ S s) :
    MemLp (jet(χ, j.val.1, j.val.2)) 2 (μ'(s)) := by sorry

local notation "jetLp(" χ ", " S ", " hs ", " j ")" =>
  (orbitalJet_memLp χ S hs j).toLp (jet(χ, (j).val.1, (j).val.2))

/-- Paper: Theorem 11.2.0.2, p. 485. Under left translation, each admitted jet
lies in the conjugate isotype in the negative space. -/
theorem orbitalJet_isotype (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ} (hs : 0 ≤ s)
    (j : OrbitalJetIndex χ S s) (k : C₁) :
    (fun g ↦ jetLp(χ, S, hs, j) (k.val⁻¹ * g)) =ᵐ[μ𝔽]
      fun g ↦ (χ⁻¹ k.val : ℂ) * jetLp(χ, S, hs, j) g := by sorry

variable (F) in
/-- Paper: Theorem 11.2.0.2 and Remark 11.2.0.3, p. 485. Inside the chosen
positive Sobolev isotype, take the closed principal-value subspace.
Deviation: Close the completed principal-value range in the ambient space
before taking the isotype. -/
def orbitalSobolevSubmodule (S : Finset V) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) : Submodule ℂ Wω(hs, ω) :=
  ((((H(0, hs)).subtype.comp (P(S, 0, hs)).toLinearMap).range).topologicalClosure).comap
    (Wω(hs, ω)).subtype

local notation "N(" S ", " hs ", " ω ")" => orbitalSobolevSubmodule F S hs ω
local notation "Q(" S ", " hs ", " ω ")" => (↥(Wω(hs, ω)) ⧸ N(S, hs, ω))

/-- Paper: Remark 11.2.0.3, p. 485. The principal-value subspace is closed
in its isotype, so the quotient carries the canonical quotient norm.
Deviation: Sanity check for the closure used in the definition. -/
@[instance]
theorem instClosedOrbitalSobolevSubmoduleSec2a (S : Finset V) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) : IsClosed (N(S, hs, ω) : Set Wω(hs, ω)) := by sorry

/-- Paper: Theorem 11.2.0.2, p. 485. With no finite places imposed, the
principal-value subspace is the whole isotype.
Deviation: Sanity check for the empty set of places. -/
theorem orbitalSobolevSubmodule_empty {s : ℝ} (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    N(∅, hs, ω) = ⊤ := by sorry

-- TODO(paper-gap): The proof on p. 486 needs density of both spans for the
-- completed PV quotient. Strong approximation on the ambient space in §9.3
-- alone does not identify the annihilator of that completed image.

/-- Paper: Theorem 11.2.0.2 and Terminology 11.2.0.1, p. 485. The zero jets
constitute an orbital Markushevich basis in the strong dual of the isotypic
quotient, realized by the bilinear Sobolev pairing. The biorthogonal vectors
are written in the Hilbert predual.
Deviation: Use the conjugate isotype for the annihilator, as in the statement
of jet membership. Quotienting by the closure gives the same continuous
annihilator as the raw range. Index each zero of the product once with its
total multiplicity. The index type permits any reindexing, including the
empty family. -/
theorem orbitalMarkushevichBasis (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ}
    (hs : 0 ≤ s) (_hcard : 2 * (S.card : ℝ) ≤ s)
    (_hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) :
    let J := OrbitalJetIndex χ S s
    let ω := χ.comp restriction
    letI : IsClosed (N(S, hs, ω) : Set Wω(hs, ω)) :=
      instClosedOrbitalSobolevSubmoduleSec2a S hs ω
    let Q := Q(S, hs, ω)
    Countable J ∧
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q),
      IsSpectralMarkushevichBasis x Λ ∧ ∀ (j : J) (f : Wω(hs, ω)),
        Λ j ((N(S, hs, ω)).mkQ f) = spectralSobolevPairing f.val (jetLp(χ, S, hs, j)) :=
  by sorry

-- TODO(paper-gap): Remark 11.2.0.3 drops PV from the denominator of the quotient.

/-- Paper: Remark 11.2.0.3, p. 485. The pairing represents the quotient
strong dual isometrically as the annihilator in the negative space.
Deviation: Divide the isotype by the closed principal-value subspace. -/
theorem orbitalQuotientDual_isometry_range (S : Finset V) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :
    ∃ D : StrongDual ℂ Q(S, hs, ω) →ₗᵢ[ℂ] W'(s),
      range D = {u |
        (∀ k : C₁, (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ𝔽] fun g ↦ (ω⁻¹ k : ℂ) * u g) ∧
        ∀ f ∈ N(S, hs, ω), spectralSobolevPairing f.val u = 0} ∧
      ∀ (Λ : StrongDual ℂ Q(S, hs, ω)) (f : Wω(hs, ω)),
        spectralSobolevPairing f.val (D Λ) = Λ ((N(S, hs, ω)).mkQ f) := by sorry

local notation "E" => ModulatedExponentialDecay m𝔽 (univ : Set ℝ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "hms𝔽" => (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
local notation "ρE" => (exists_modulatedExponentialDecay_translationAction m𝔽 univ
  hm𝔽 hms𝔽 ordConnected_univ univ_nonempty).choose
local notation "Eω(" ω ")" => actionIsotype ((ρE).comp (ideleClassNorm F).ker.subtype) ω

/-- Paper: (11.2.0.7), p. 486. The continuous transpose of the test inclusion
evaluates by the Sobolev pairing. It gives the commutative square after
restriction to the homogeneous principal-value tests of every polar-free input.
Deviation: Use the equivalent isotypic presentation of the tests on idele
classes from §10.2, with the conjugate isotype on the negative side. -/
theorem orbitalSobolevPairing_pullback (S : Finset V) (a : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (u : W'(s))
    (_hu : ∀ k : C₁, (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ𝔽] fun g ↦ (ω⁻¹ k : ℂ) * u g) :
    let i := (existsUnique_spectralLineTestCompletion a hs ω).exists.choose
    let A := (existsUnique_globalThetaSobolevAverage (F := F) (a := a) hI hs ω).exists.choose
    ∃ Λ : StrongDual ℂ Eω(ω),
      (∀ φ : Eω(ω), Λ φ = spectralSobolevPairing (i φ).val u) ∧
      ∀ f : ℬ₀, ∃ φ : Eω(ω),
        (∀ g : C𝔽, φ.val.val g = homogeneousAdelicTheta ω (pvTest(S, f)).val g) ∧
        (i φ).val = (P(S, a, hs) (A (j(a, hs) (theta(f)))).val).val := by sorry

-- TODO(paper-gap): Proposition 11.2.0.4 prints the full multiplicity and
-- claims noncontainment in an open ball even when S₀ is empty.

/-- Paper: Proposition 11.2.0.4 and (11.2.0.8)–(11.2.0.9), p. 486. One
annulus bounds the norms of all admitted jets above and away from zero.
Deviation: Use the truncated multiplicity cited in (11.2.0.6) and the
conjugate isotype. The annulus condition is disjointness from the inner
open ball, which also holds for an empty family. -/
theorem orbitalJet_norm_annulus (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ}
    (hs : 1 < s) (_hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : OrbitalJetIndex χ S s,
      let u := jetLp(χ, S, (zero_lt_one.trans hs).le, j)
      C⁻¹ ≤ ‖u‖ ∧ ‖u‖ ≤ C := by sorry

/-- Paper: Corollary 11.2.0.5 and (11.2.0.10), pp. 486–487. The orbital
Markushevich basis is normalized in the strong-dual norm.
Deviation: Use the isotypic quotient with the closed principal-value
denominator. The degree hypothesis already admits the full multiplicity. -/
theorem orbitalMarkushevichBasis_normalized (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ}
    (hs : 1 < s) (_hcard : 2 * (S.card : ℝ) ≤ s)
    (_hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) :
    let hs₀ := (zero_lt_one.trans hs).le
    let J := OrbitalJetIndex χ S s
    let ω := χ.comp restriction
    letI : IsClosed (N(S, hs₀, ω) : Set Wω(hs₀, ω)) :=
      instClosedOrbitalSobolevSubmoduleSec2a S hs₀ ω
    let Q := Q(S, hs₀, ω)
    ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q),
      IsSpectralMarkushevichBasis x Λ ∧ IsNormalizedSpectralFamily Λ ∧
      ∀ (j : J) (f : Wω(hs₀, ω)),
        Λ j ((N(S, hs₀, ω)).mkQ f) = spectralSobolevPairing f.val (jetLp(χ, S, hs₀, j)) :=
  by sorry

end RiemannMasullo
