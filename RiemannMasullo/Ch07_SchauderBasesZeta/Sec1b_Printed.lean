module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b

/-! # §7.1.3–7.1.4 Statements that are false as printed -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal

namespace RiemannMasullo

set_option quotPrecheck false

universe u

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "RatPrimes" => HeightOneSpectrum (𝓞 ℚ)
local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽(" F ")" => PontryaginDual C𝔽(F)
local notation "Jₛ(" F ", " S ")" => SIdeleQuotient F S
local notation "normₛ(" F ", " S ")" => sIdeleQuotientNorm F S
local notation "twistₛ(" F ", " S ")" =>
  quasiCharacterNormTwist (G := Jₛ(F, S)) normₛ(F, S) (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "overₚ(" T "," p ")" =>
  ((T).filter (fun v ↦ HeightOneSpectrum.under (𝓞 ℚ) v = p))
local notation "Bergman" => SchwartzBergman (univ : Set ℝ)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)
local notation "Entire" => Subtype (fun f : C(ℂ, ℂ) ↦ f ∈ entireContinuousMapSubalgebra)
local notation "Zeros(" L ")" => {ρ : ℂ // 0 < meromorphicOrderAt L ρ}
local notation "Jet(" L ", " ρ ")" =>
  entireJetSpace ρ (meromorphicOrderAt L ρ).untop₀.toNat

local instance printedCh07Sec1bStrongDualTopology : TopologicalSpace (StrongDual ℂ Entire) :=
  ContinuousLinearMap.topologicalSpace (σ := RingHom.id ℂ) (E := Entire) (F := ℂ)

open Classical in
/-- Paper: Remark 7.1.3.1, equation (7.1.3.1), p. 324.
As printed: For a finite-order character twisted by an imaginary norm power, infinitely
many rational primes satisfy the product identity with unshifted exponent once the
selected places contain all places above the prime. The translated formula is
`infinite_split_primes_reciprocalEulerProduct_normTwist`. See ERRATA F95. -/
def Printed.infinite_split_primes_reciprocalEulerProduct_normTwist : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ χ₀ : U𝔽(F)),
    IsOfFinOrder χ₀ → ∀ x : ℝ,
      ideleClassNormTwist χ 0 = ideleClassNormTwist χ₀ ((x : ℂ) * Complex.I) →
      {p : RatPrimes | ∀ S₀ : Finset Places(F),
        (∀ v : Places(F), v.under (𝓞 ℚ) = p → v ∈ S₀) →
        ∀ s : ℂ, reciprocalPartialHeckeEulerProduct χ overₚ(S₀, p) s =
          (1 - (p.asIdeal.absNorm : ℂ) ^ (-s)) ^ Module.finrank ℚ F}.Infinite

/-- Paper: Remark 7.1.3.1, equation (7.1.3.1), p. 324.
Use ℚ, the trivial finite-order character, and x = 2π/log 2. At s = 0 the
identity requires p^(-ix) = 1, so the rational prime p is an integral power
of 2. Only the prime 2 can satisfy the identity. -/
theorem Printed.infinite_split_primes_reciprocalEulerProduct_normTwist_false :
    ¬ Printed.infinite_split_primes_reciprocalEulerProduct_normTwist := by sorry

open Classical in
/-- Paper: Theorem 7.1.3.2(2), p. 324.
As printed: At an archimedean point of the stated pole list whose real part is a
negative odd integer, the pole order of the correcting factor is bounded by the number
of complex places. The repaired bound is `sLocalRhoPoleOrder_le_of_re_neg_odd`.
See ERRATA F97. -/
def Printed.sLocalRhoPoleOrder_le_of_re_neg_odd : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (χ : U𝔽(F))
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (w : InfinitePlace F) (n : ℕ),
    let chart := twistₛ(F, S) (sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩)
    let c := sLocalInfiniteRestriction w (chart 0)
    let m : ℝ := -((2 * n + 1 : ℕ) : ℝ)
    let r₂ := (Finset.univ.filter (fun v : InfinitePlace F ↦ v.IsComplex)).card
    (∀ hw : w.IsReal,
      let p := (realLocalEulerParameters w hw c).exists.choose
      p.2.val = 1 → sLocalRhoPoleOrder (chart ((m : ℂ) - p.1)) ≤ r₂) ∧
    (∀ hw : w.IsComplex,
      let p := (complexLocalEulerParameters w hw c).exists.choose
      (∃ j : ℕ, m = (p.2.natAbs : ℝ) / 2 - j) →
        sLocalRhoPoleOrder (chart ((m : ℂ) - p.1)) ≤ r₂)

/-- Paper: Theorem 7.1.3.2(2), p. 324.
Use ℚ, its real place and its place above 2, and the odd Dirichlet character
modulo 4. Its real factor Γℝ(s + 1) gives a pole at −1 with a regular nonzero
denominator. The finite factor is ramified and does not cancel it. There are
zero complex places. -/
theorem Printed.sLocalRhoPoleOrder_le_of_re_neg_odd_false :
    ¬ Printed.sLocalRhoPoleOrder_le_of_re_neg_odd := by sorry

/-- Paper: Corollary 7.1.3.3, p. 326.
As printed: There is a highest positive pole order and a highest positive order
strictly below it for the continued zeta transform of every test in the setting of
the corollary. This is the clause defining the remainder exponent.
The least-bound formulation is in `sLocalHomogeneousAdelicTheta_log_bound`.
See ERRATA F98. -/
def Printed.sLocalPolarMultiplicity_greatest_smaller : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)),
    Fintype.card (InfinitePlace F) = 1 →
    ∀ (χ : PontryaginDual Jₛ(F, S)) (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))),
      let chart := twistₛ(F, S) ((circleToComplex).comp χ)
      let orders : Set ℕ := {m | 0 < m ∧ ∃ s : ℂ, sLocalPolarMultiplicity f (chart s) = m}
      ∃ M m : ℕ, IsGreatest orders M ∧ IsGreatest (orders ∩ Iio M) m

/-- Paper: Corollary 7.1.3.3, p. 326.
Use ℚ with only the real place, the trivial character and the zero test, for which
the set of pole orders is empty. The Gaussian `exp(-πx²)` gives a second example:
Γℝ(s) has only simple poles, so there is no positive order below one. -/
theorem Printed.sLocalPolarMultiplicity_greatest_smaller_false :
    ¬ Printed.sLocalPolarMultiplicity_greatest_smaller := by sorry

/-- Paper: Theorem 7.1.4.2(1), equation (7.1.4.2), p. 326.
As printed: The strong annihilator of the regularized completed Hecke ideal is linearly
and topologically isomorphic to the product of the jet spaces at the completed Hecke zeros.
The direct-sum statement is `spectralAnnihilator_directSum`. See ERRATA F99. -/
def Printed.spectralAnnihilator_product : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ : U𝔽(F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hEq : ∀ s : halfPlane, L s = completedHeckeL χ s),
    let Λ := regularizedCompletedHeckeL χ τ hτ L hL hEq
    Nonempty ((∀ ρ : Zeros(L), ↥(Jet(L, ρ.val))) ≃L[ℂ] entireIdealAnnihilator Λ)

/-- Paper: Theorem 7.1.4.2(1), equation (7.1.4.2), p. 326.
Take the trivial rational character and the meromorphic normal form of the completed
Riemann zeta function. There are countably infinitely many distinct zeros and
each jet space is nonzero and
finite-dimensional. The annihilator consists of finite-support jets and has countable
algebraic dimension. The product has uncountable dimension, as seen by embedding
complex sequences and using the independent sequences `(a^n)ₙ` for distinct a. -/
theorem Printed.spectralAnnihilator_product_false :
    ¬ Printed.spectralAnnihilator_product := by sorry

/-- Paper: Theorem 7.1.4.2(2), equation (7.1.4.6), p. 327.
As printed: The derivative functional at a completed Hecke zero is the moment of the
inverse Mellin transform in the coordinate (7.1.4.1), with exponent shifted by the
section frequency x₀. The formula of `schwartzBergman_jet_eq_mellinInv_moment`
uses the unshifted exponent. See ERRATA F100. -/
def Printed.schwartzBergman_jet_eq_mellinInv_shifted_moment : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ : U𝔽(F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (L : ℂ → ℂ) (_hL : MeromorphicNFOn L univ)
    (_hEq : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (ρ : Zeros(L)) (m : ℕ), m < (meromorphicOrderAt L ρ.val).untop₀.toNat →
    ∀ f : Bergman,
      let x₀ := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
      let φ : ℂ → ℂ := f.val
      let moment := fun t : ℝ ↦ (Real.log t : ℂ) ^ m * mellinInv 0 φ t
      iteratedDeriv m φ ρ.val = mellin moment (ρ.val + (x₀ : ℂ) * Complex.I)

/-- Paper: Theorem 7.1.4.2(2), equation (7.1.4.6), p. 327.
Take ℚ, the pure norm character with exponent i and x₀ = 1. Use the meromorphic
normal form of the shifted completed zeta, with a zero ρ obtained by shifting
a completed zeta zero by −i.
At m = 0 take `φ(s) = (s - ρ) exp(s²)`. The derivative functional is zero, while
the convergent shifted moment is `φ(ρ + i) = i exp((ρ + i)²) ≠ 0`. -/
theorem Printed.schwartzBergman_jet_eq_mellinInv_shifted_moment_false :
    ¬ Printed.schwartzBergman_jet_eq_mellinInv_shifted_moment := by sorry

/-- Paper: Theorem 7.1.4.2(4), p. 327.
As printed: The jet functionals are continuous on the ordinary Schwartz quotient.
The chosen section identifies the isotype with ordinary Schwartz norm profiles.
The denominator consists of the profiles of homogeneous theta functions of polar
tests. On every exponentially decaying profile the functional is the jet in the
Mellin coordinate (7.1.4.1). The repaired estimate
`schwartzBergman_normalizedJets` uses the exponentially decaying tests.
See ERRATA F101, also for the analogous topology in Theorem 7.1.4.3(3). -/
def Printed.schwartzBergman_jet_continuous_on_ordinary_schwartz : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ : U𝔽(F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (L : ℂ → ℂ) (_hL : MeromorphicNFOn L univ)
    (_hEq : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (ρ : Zeros(L)) (m : ℕ), m < (meromorphicOrderAt L ρ.val).untop₀.toNat →
      let x₀ := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
      let expUnit := fun s : ℝ ↦ (Nonneg.unitsHomeomorphPos ℝ).symm (Real.expOrderIso s)
      let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm F).ker →ₜ* C𝔽(F))
      let H := Submodule.span ℂ {f : SchwartzBruhat ℝ≥0ˣ | ∃ a : adelePolarSubspace F,
        ∀ t, f t = homogeneousAdelicThetaLinearMap F ω a.val (QuotientGroup.mk (τ t))}
      ∃ ℓ : (SchwartzBruhat ℝ≥0ˣ ⧸ H) →L[ℂ] ℂ,
        ∀ f : SchwartzBruhat ℝ≥0ˣ, (fun u ↦ f (expUnit u)) ∈ logExponentialDecaySubmodule univ →
          ℓ (Submodule.Quotient.mk f) =
            ∫ u : ℝ, f (expUnit u) * Complex.exp ((ρ.val + (x₀ : ℂ) * Complex.I) * u) *
              (u : ℂ) ^ m

/-- Paper: Theorem 7.1.4.2(4), p. 327.
Take the trivial rational character, a completed zeta zero ρ with a = Re ρ > 0,
and m = 0. Take a smooth nonzero nonnegative bump b supported in (0,1) and the
log-profile `h(u) = b(u) exp(-i Im(ρ) u)`. The ordinary Schwartz profiles
`exp(-an) h(u - n)` tend to zero, while their ρ-moments have the same strictly
positive modulus as the ρ-moment of h. -/
theorem Printed.schwartzBergman_jet_continuous_on_ordinary_schwartz_false :
    ¬ Printed.schwartzBergman_jet_continuous_on_ordinary_schwartz := by sorry

/-- Paper: Estimate after equation (7.1.4.22), p. 330.
As printed: The norm of the normalized derivative throughout the closed critical strip
is at most 1/(2π) times the larger of the two vertical L¹ norms. The equicontinuity
statement is `schwartzBergman_normalizedJets`. See ERRATA F102. -/
def Printed.schwartzBergman_normalizedJet_le_max : Prop :=
  ∀ (f : Bergman) (s : ℂ), s.re ∈ Icc 0 1 → ∀ k : ℕ,
    let lineNorm (σ : ℝ) :=
      ∫ y : ℝ, ‖f.val ((σ : ℂ) + (y : ℂ) * Complex.I)‖
    ‖iteratedDeriv k f.val s / (k.factorial : ℂ)‖ ≤
      (2 * Real.pi)⁻¹ * max (lineNorm (-1)) (lineNorm 2)

/-- Paper: Estimate after equation (7.1.4.22), p. 330.
Use `Φ(s) = exp(2 (s - 1/2)^2 / 9)`, s = 1/2, and k = 0. The left side is 1.
Each line norm is `3 √(π e/2)`, so the right side is `√(9 e/(8π)) < 1`. -/
theorem Printed.schwartzBergman_normalizedJet_le_max_false :
    ¬ Printed.schwartzBergman_normalizedJet_le_max := by sorry

section Orbital

variable {F : Type u} [Field F] [NumberField F]

open Classical in
/-- Paper: Equation (7.1.4.24), p. 331.
The prime block spans the derivative evaluations over all zeros of that prime's
Euler polynomial, with the order cutoff taken from that polynomial alone. -/
def Printed.orbitalPrimeJetSpace (χ : U𝔽(F)) (S₀ : Finset Places(F)) (p : RatPrimes) :
    Submodule ℂ (StrongDual ℂ Entire) :=
  let P := reciprocalPartialHeckeEulerProduct χ overₚ(S₀, p)
  Submodule.span ℂ {ℓ | ∃ (ε : ℂ) (m : ℕ),
    m < (meromorphicOrderAt P ε).untop₀.toNat ∧ ℓ = entireJet ε m}

/-- Paper: Theorem 7.1.4.3(1), equations (7.1.4.23)–(7.1.4.25), p. 331.
As printed: The orbital strong annihilator is linearly and topologically isomorphic
to the product of the separate prime blocks and the product of the completed Hecke jets.
Each prime block uses the zeros of its own Euler polynomial. The corrected decomposition
`orbitalAnnihilator_directSum` uses the order of the full generator at each point.
See ERRATA F99 and F103. -/
def Printed.orbitalAnnihilator_prime_products : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ : U𝔽(F)) (S₀ : Finset Places(F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hEq : ∀ s : halfPlane, L s = completedHeckeL χ s),
    let g := orbitalHeckeGenerator χ τ hτ L hL hEq S₀
    let primes := {p : RatPrimes // ∃ v ∈ S₀, HeightOneSpectrum.under (𝓞 ℚ) v = p}
    Nonempty (((∀ p : primes, ↥(Printed.orbitalPrimeJetSpace χ S₀ p.val)) ×
      (∀ ρ : Zeros(L), ↥(Jet(L, ρ.val)))) ≃L[ℂ] entireIdealAnnihilator g)

/-- Paper: Theorem 7.1.4.3(1), equations (7.1.4.23)–(7.1.4.25), p. 331.
Take ℚ, the trivial character and S₀ consisting of the places above 2 and 3. The
annihilator of the entire generator consists of finite-support jets at countably
many zeros, while the product of the completed zeta jets has uncountable dimension.
At the origin the regularized completed zeta is nonzero, and each prime block
contributes the same value functional. Their difference vanishes under the jet
identification, and the first derivative at the resulting double zero is missing. -/
theorem Printed.orbitalAnnihilator_prime_products_false :
    ¬ Printed.orbitalAnnihilator_prime_products := by sorry

/-- Paper: Theorem 7.1.4.3(1), equation (7.1.4.24), p. 331.
As printed: The space of all jets associated with a rational prime block is
finite-dimensional. The fixed-zero dimension is computed by `entireJetSpace_finrank`,
and `orbitalAnnihilator_directSum` uses one space per zero. See ERRATA F104. -/
def Printed.orbitalPrimeJetSpace_finite : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ : U𝔽(F)) (S₀ : Finset Places(F))
    (p : RatPrimes), (∃ v ∈ S₀, v.under (𝓞 ℚ) = p) →
      Module.Finite ℂ (Printed.orbitalPrimeJetSpace χ S₀ p)

/-- Paper: Theorem 7.1.4.3(1), equation (7.1.4.24), p. 331.
Take the trivial rational character and S₀ consisting of the place above 2.
The polynomial `1 - 2^(-s)` has a simple zero at each `2πim/log 2`. Evaluations
at these distinct points are linearly independent by interpolation with polynomials
on any finite subset. -/
theorem Printed.orbitalPrimeJetSpace_finite_false :
    ¬ Printed.orbitalPrimeJetSpace_finite := by sorry

end Orbital

end RiemannMasullo
