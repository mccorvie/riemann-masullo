module

public import RiemannMasullo.AppB_AnalyticNT.Sec3
public import RiemannMasullo.AppB_AnalyticNT.Sec5
public import RiemannMasullo.Ch03_IdelicZeta.Sec3b

/-!
# §7.1.1–7.1.2 Almost periodic functions and S-local theta asymptotics

The finite set `S` lists the finite places. All archimedean places are included.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators NNReal Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "Primes" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F

-- The Euler product, its reciprocal, and the upper density in (7.1.1.1),
-- (7.1.1.2), and (7.1.1.4) use the constructions of §B.5.3.

-- TODO(paper-gap): Lemma 7.1.1.1(1) forces T₀ = 0. The trivial character of ℚ
-- with a finite place above 2 has a pole at σ = T₀ = 0. For ramified places in S,
-- the phase in the printed product is undefined. Equation (7.1.1.3) also reverses
-- the phase sign in (7.1.1.1).

/-- Paper: Lemma 7.1.1.1, p. 313.
There are ordered heights escaping to infinity on both tails at which the finite Euler
product is uniformly bounded on the closed strip from `-δ` to `1 + δ`.
Deviation: Uses the sign convention for index zero from §B.5.3.2 and the Euler factors
of §3.2.1, with factor one at ramified places. A positive lower bound on the reciprocal
product expresses both the upper bound and avoidance of poles. -/
theorem exists_heights_reciprocalPartialHeckeEulerProduct_strip_boundedBelow
    (S : Finset Primes) (_hPic : Subsingleton (CommRing.Pic ((S : Set Primes).integer F)))
    (χ : PontryaginDual C𝔽) (_hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    {δ : ℝ} (_hδ : 0 < δ) :
    ∃ (c : ℝ) (T : ℤ → ℝ), 0 < c ∧ Monotone T ∧
      (∀ k, 0 ≤ k → 0 ≤ T k) ∧ (∀ k, k < 0 → T k ≤ 0) ∧
      Tendsto (fun k ↦ |T k|) (comap (abs : ℤ → ℤ) atTop) atTop ∧
      ∀ k : ℤ, ∀ σ ∈ Icc (-δ) (1 + δ),
        c ≤ ‖reciprocalPartialHeckeEulerProduct χ S ((σ : ℂ) + (T k : ℂ) * Complex.I)‖ := by
  sorry

-- TODO(paper-gap): The proof on p. 315 uses a different reflection for each place,
-- and positive symmetric upper density alone does not guarantee visits on both tails.
-- The zero list on p. 313 also omits the shift by -itᵥ in (7.1.1.1).

section SLocal

variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Jₛ" => SIdeleQuotient F S
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "twistₛ" => quasiCharacterNormTwist (G := Jₛ) mₛ
  (IsProperMap.continuous (isProperMap_sIdeleQuotientNorm F S))
local notation "zetaGerm(" f "," c ")" => fun z ↦ sLocalIdelicZFunction f (twistₛ c z)

-- TODO(paper-gap): The preamble's a₋ₙ ≠ 0 condition at N = 0 fails at holomorphic zeros.

/-- Paper: Definition 7.1.2.1, p. 316.
The polar S-multiplicity is the order of the pole of the continued zeta function at `c`.
It is zero at every point without a pole, including when the germ vanishes identically. -/
def sLocalPolarMultiplicity (f : ℬₛ) (c : QuasiCharacter Jₛ) : ℕ :=
  (-(meromorphicOrderAt (zetaGerm(f, c)) 0).untop₀).toNat

/-- Paper: Definition 7.1.2.1, p. 316.
The multiplicity vanishes exactly at the quasi-characters with nonnegative meromorphic order. -/
theorem sLocalPolarMultiplicity_eq_zero_iff (f : ℬₛ) (c : QuasiCharacter Jₛ) :
    sLocalPolarMultiplicity f c = 0 ↔
      0 ≤ meromorphicOrderAt (zetaGerm(f, c)) 0 := by
  unfold sLocalPolarMultiplicity
  generalize meromorphicOrderAt (zetaGerm(f, c)) 0 = o
  induction o using WithTop.recTopCoe with
  | top => simp
  | coe n => simp

/-- Paper: Definition 7.1.2.1, p. 316.
The integer-indexed Laurent coefficient is computed in the norm-twist coordinate centered
at `c`, by taking the residue after shifting the desired power to exponent minus one. -/
def sLocalZLaurentCoeff (f : ℬₛ) (c : QuasiCharacter Jₛ) (m : ℤ) : ℂ :=
  complexResidue (fun z ↦ sLocalIdelicZFunction f (twistₛ c z) / z ^ (m + 1)) 0

/-- Paper: Definition 7.1.2.1, p. 316.
The coefficient sequence gives a Laurent expansion of the centered zeta germ, with partial
sums converging uniformly on compact subsets of a punctured disc. -/
theorem sLocalZLaurentCoeff_hasLaurentSeries (f : ℬₛ) (c : QuasiCharacter Jₛ) :
    HasVectorLaurentSeriesAt (zetaGerm(f, c)) 0 (sLocalZLaurentCoeff f c) := by sorry

-- TODO(paper-gap): In Lemma 7.1.2.2(1), the complex-place shift has the wrong sign.
-- The uniqueness of the contributing place stated on p. 317 fails when poles coincide.

/-- Paper: Lemma 7.1.2.2, p. 316.
The poles of the S-local correcting factor are the union of the two archimedean families
and the periodic lattices at unramified finite places.
Deviation: As in §3.3, the complex-place abscissae start at minus half the absolute angular
weight. The union allows more than one place to contribute to the same pole. -/
theorem sLocalRhoFactor_poles_iff (χ : PontryaginDual Jₛ) (s : ℂ) :
    let χ₀ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
    let c := twistₛ χ₀ 0
    meromorphicOrderAt (fun z ↦ sLocalRhoFactor (twistₛ χ₀ z)) s < 0 ↔
      (∃ (w : InfinitePlace F) (hw : w.IsReal) (n : ℕ),
        let p := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w c)).exists.choose
        s = -p.1 - ((2 * n + p.2.val : ℕ) : ℂ)) ∨
      (∃ (w : InfinitePlace F) (hw : w.IsComplex) (n : ℕ),
        let p := (complexLocalEulerParameters w hw (sLocalInfiniteRestriction w c)).exists.choose
        s = -p.1 - (p.2.natAbs : ℂ) / 2 - (n : ℂ)) ∨
      (∃ (v : S) (m : ℤ) (t : ℝ),
        let period := 2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)
        t ∈ Ico 0 period ∧
          (∀ x : (v.val.adicCompletion F)ˣ,
            sLocalFiniteRestriction v c x =
              ((‖(x : v.val.adicCompletion F)‖ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) ∧
          s = (((m : ℝ) * period - t : ℝ) : ℂ) * Complex.I) := by sorry

open Classical in
/-- Paper: Lemma 7.1.2.2, p. 317.
At a pole of the correcting factor, its order counts all the places where the
restricted local Tate factor has a pole.
Deviation: Each local pole is simple. The count includes coincident poles. -/
theorem sLocalRhoFactor_orderAt_pole (χ : PontryaginDual Jₛ) (s : ℂ) :
    let χ₀ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
    let c := fun z : ℂ ↦ twistₛ χ₀ z
    let ρ := fun z : ℂ ↦ sLocalRhoFactor (c z)
    let arch := Finset.univ.filter (fun w : InfinitePlace F ↦
      meromorphicOrderAt (fun z ↦ infiniteLocalTateFactor w (sLocalInfiniteRestriction w (c z))) s < 0)
    let fin := Finset.univ.filter (fun v : S ↦
      meromorphicOrderAt (fun z ↦ finiteLocalTateFactor v.val (sLocalFiniteRestriction v (c z))) s < 0)
    meromorphicOrderAt ρ s < 0 →
      meromorphicOrderAt ρ s = ((-((arch.card + fin.card : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by sorry

end SLocal

-- TODO(paper-gap): Theorem 7.1.2.3 omits the real Gaussian's constant term, uses
-- a_{k-1} in place of a_{-k}, and counts coincident poles once per contributing place.
-- The strict cutoff can omit higher-order poles on Re(s) = -A, where the claimed
-- L¹ remainder constant is undefined. The bounded-set version has the same defects.
-- TODO(paper-gap): Footnote 1, p. 321, flags the missing growth control on the
-- horizontal heights for the appeal to Theorem B.3.2.1.

section Counterexample

local notation "Jℚ" => SIdeleQuotient ℚ ∅
local notation "Jℚ₁" => MonoidHom.ker (sIdeleQuotientNorm ℚ ∅)
local notation "μℚ₁" => sLocalNormOneQuotientMeasure ℚ ∅

local instance instMeasurableNormOneRatSec1a : MeasurableSpace Jℚ₁ := borel _
local instance instHaarNormOneRatSec1a : Measure.IsHaarMeasure μℚ₁ :=
  (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := ∅)).1

/-- Paper: Theorem 7.1.2.3, p. 317.
Over the rationals with only the real place and the trivial character, the square-root
bound at norm zero fails for some test function. The real Gaussian gives a witness.
Deviation: States a counterexample to (7.1.2.3) at `A = 1/2`, where both printed sums are empty. -/
theorem sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)),
      let normℝ (g : Jℚ) := ((sIdeleQuotientNorm ℚ ∅ g : ℝ≥0) : ℝ)
      ¬ Asymptotics.IsBigO (comap normℝ (𝓝[>] (0 : ℝ)))
        (sLocalHomogeneousAdelicTheta ℚ ∅ μℚ₁ (1 : PontryaginDual Jℚ₁) f : Jℚ → ℂ)
        (fun g ↦ (normℝ g) ^ (1 / 2 : ℝ)) := by sorry

end Counterexample

-- TODO(paper-gap): Remark 7.1.2.4 drops the imaginary-unit conversion in the phase
-- and reverses the phase sign in the displayed list for the saturated product.

/-- Paper: Remark 7.1.2.4, p. 318.
At an unramified finite place the poles of the Hecke Euler factor are equally spaced on
the imaginary axis. The phase is specified by the value at a local uniformizer.
Deviation: Uses the global character after extension and the phase convention
`χ(πᵥ) = qᵥ^(-it)` of Lemma 7.1.2.2. The period lattice is a subgroup of `ℂ`. -/
theorem finiteHeckeEulerFactor_poles_iff (χ : PontryaginDual C𝔽) (v : Primes)
    (_hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v) (t : ℝ)
    (_ht : (ideleClassNormTwist χ 0).localValue v =
      (v.asIdeal.absNorm : ℂ) ^ (-(t : ℂ) * Complex.I)) (s : ℂ) :
    meromorphicOrderAt (finiteHeckeEulerFactor χ v) s < 0 ↔
      ∃ m : ℤ, s = (((m : ℝ) * (2 * Real.pi / Real.log (v.asIdeal.absNorm : ℝ)) - t : ℝ) : ℂ) *
        Complex.I := by sorry

open Classical in
/-- Paper: Remark 7.1.2.4, p. 318.
At a rational prime with all places above it in `S`, the poles of the product are precisely
the poles of the individual local Euler factors at those places.
Deviation: The factors at ramified places are one, as in §3.2.1. -/
theorem finiteHeckeEulerProduct_poles_iff (χ : PontryaginDual C𝔽) (S : Finset Primes)
    (p : HeightOneSpectrum (𝓞 ℚ)) (_hsat : ∀ v : Primes, v.under (𝓞 ℚ) = p → v ∈ S)
    (s : ℂ) :
    let Sₚ := S.filter (fun v ↦ v.under (𝓞 ℚ) = p)
    meromorphicOrderAt (fun z ↦ ∏ v ∈ Sₚ, finiteHeckeEulerFactor χ v z) s < 0 ↔
      ∃ v ∈ Sₚ, meromorphicOrderAt (finiteHeckeEulerFactor χ v) s < 0 := by sorry

-- TODO(prerequisite): The induced Euler-factor identity in Remark 7.1.2.4 needs
-- global Weil groups and their induction and local L-factor constructions.
-- TODO(later): needs §7.2.1 for continuity of the Laurent coefficient operators and
-- their descent to the coinvariants (Theorem 7.2.1.1(1)–(2)).
-- TODO(paper-gap): The eigendistribution interpretation on pp. 319–321 fails for
-- general Laurent coefficients. For the real Gaussian at the trivial character,
-- scaling f(x) to f(x/r) adds log(r) * a₋₁ to a₀. At a multiple pole, lower polar
-- coefficients also mix under dilation. The leading polar coefficient transforms by
-- the character, and all coefficients have the character law on norm-one elements.
-- On p. 321 the lattice index is also used as a Laurent index. At index zero a
-- test function compactly supported in the S-ideles can have nonzero a₀.
-- TODO(paper-gap): The contour formula on p. 323 needs positive orientation and
-- exclusion of the other poles, as in Lemma C.5.3.2. Compare scalar normal forms
-- away from the distributional poles, as in infiniteLocalIdelicZFunction_distribution.

end RiemannMasullo
