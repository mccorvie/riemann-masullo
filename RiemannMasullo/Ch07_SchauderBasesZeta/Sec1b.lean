module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1a
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2
public import Mathlib.NumberTheory.NumberField.DirichletDensity
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Analysis.Complex.LocallyUniformLimit
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# §7.1.3–7.1.4 Polar multiplicities and spectral biorthogonal sequences

A finite set of finite places is used to specify an S-local space. Every infinite place is
included in the S-local space regardless of this set.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped DirectSum NNReal Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "Primes" => HeightOneSpectrum (𝓞 F)
local notation "RatPrimes" => HeightOneSpectrum (𝓞 ℚ)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽
local notation "degree" => Module.finrank ℚ F
local notation "archCount" => Fintype.card (InfinitePlace F)

section Polar

/-- Paper: §7.1.3, p. 323.
A quasi-character of Galois type is a complex norm twist of a finite-order unitary character. -/
def IsGaloisType (c : HeckeCharacter (𝓞 F) F) : Prop :=
  ∃ (χ₀ : U𝔽) (s : ℂ), IsOfFinOrder χ₀ ∧ c = ideleClassNormTwist χ₀ s

/-- Paper: §7.1.3, p. 323.
A pure norm power is of Galois type.
Deviation: States a sanity check using the trivial finite-order character. -/
theorem isGaloisType_normPower (s : ℂ) :
    IsGaloisType (ideleClassNormTwist (1 : U𝔽) s) :=
  ⟨1, s, IsOfFinOrder.one, rfl⟩

/-- Paper: Remark 7.1.3.1, p. 323.
A rational prime splits completely when every prime over it has ramification index one
and residue degree one. -/
def rationalPrimeSplitsCompletely (F : Type*) [Field F] [NumberField F] (p : RatPrimes) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), v.under (𝓞 ℚ) = p →
    v.asIdeal.ramificationIdx (𝓞 ℚ) = 1 ∧ v.asIdeal.inertiaDeg (𝓞 ℚ) = 1

/-- Paper: Remark 7.1.3.1, p. 323.
Every rational prime splits completely in the base field.
Deviation: States a sanity check for the definition of complete splitting. -/
theorem rationalPrimeSplitsCompletely_rat (p : RatPrimes) :
    rationalPrimeSplitsCompletely ℚ p := by sorry

local notation "overₚ(" T "," p ")" =>
  @Finset.filter Primes (fun v : Primes ↦ HeightOneSpectrum.under (𝓞 ℚ) v = p)
    (Classical.decPred _) T

/-- Paper: Remark 7.1.3.1, p. 323.
A zero of the reciprocal Euler product over a rational prime belongs to the phase lattice
of some unramified place over that prime. -/
theorem reciprocalEulerProduct_over_prime_zero (χ : U𝔽) (S₀ : Finset Primes)
    (p : RatPrimes) {s : ℂ}
    (hs : reciprocalPartialHeckeEulerProduct χ overₚ(S₀, p) s = 0) :
    ∃ v ∈ overₚ(S₀, p), (ideleClassNormTwist χ 0).IsUnramifiedAt v ∧
      ∃ (k : ℤ) (t : ℝ),
        let q := v.asIdeal.absNorm
        let period := 2 * Real.pi / Real.log (q : ℝ)
        t ∈ Ico 0 period ∧
        (ideleClassNormTwist χ 0).localValue v = (q : ℂ) ^ (-(t : ℂ) * Complex.I) ∧
        s = (((k : ℝ) * period - t : ℝ) : ℂ) * Complex.I := by sorry

/-- Paper: Remark 7.1.3.1, p. 323.
The zero multiplicity of a reciprocal Euler product over a single rational prime is
bounded by the degree of the number field. -/
theorem reciprocalEulerProduct_over_prime_order_le (χ : U𝔽) (S₀ : Finset Primes)
    (p : RatPrimes) (s : ℂ) :
    analyticOrderAt (reciprocalPartialHeckeEulerProduct χ overₚ(S₀, p)) s ≤
      (degree : ℕ∞) := by sorry

/-- Paper: Remark 7.1.3.1, p. 323.
At a completely split rational prime, the product of the reciprocal unramified factors
is a power of the rational Euler polynomial when all uniformizer values are one. -/
theorem reciprocalEulerProduct_over_split_prime (χ : U𝔽) (S₀ : Finset Primes)
    (p : RatPrimes) (hp : rationalPrimeSplitsCompletely F p)
    (hS₀ : ∀ v : Primes, v.under (𝓞 ℚ) = p → v ∈ S₀)
    (hχ : ∀ v : Primes, v.under (𝓞 ℚ) = p →
      (ideleClassNormTwist χ 0).IsUnramifiedAt v ∧ (ideleClassNormTwist χ 0).localValue v = 1)
    (s : ℂ) :
    reciprocalPartialHeckeEulerProduct χ overₚ(S₀, p) s =
      (1 - (p.asIdeal.absNorm : ℂ) ^ (-s)) ^ degree := by sorry

/-- Paper: Remark 7.1.3.1, p. 323.
There are infinitely many completely split rational primes at which the character
is unramified at every place above the prime. -/
theorem infinite_split_primes_unramified (χ : U𝔽) :
    {p : RatPrimes | rationalPrimeSplitsCompletely F p ∧
      ∀ v : Primes, v.under (𝓞 ℚ) = p → (ideleClassNormTwist χ 0).IsUnramifiedAt v}.Infinite :=
  by sorry

/-- Paper: Remark 7.1.3.1, p. 324.
The completely split rational primes have positive density among the rational primes.
Deviation: Uses Mathlib's Dirichlet density. -/
theorem split_rationalPrimes_pos_dirichletDensity (F : Type*) [Field F] [NumberField F] :
    ∃ δ > (0 : ℝ),
      NumberField.Set.HasDirichletDensity {p : RatPrimes | rationalPrimeSplitsCompletely F p} δ :=
  by sorry

-- TODO(paper-gap): The claim on p. 324 extending (7.1.3.1) to Galois type needs to
-- translate the exponent by ix. For ℚ and χ = |·|^i the identity fails at s = 0.

/-- Paper: Remark 7.1.3.1, p. 324.
For a Galois-type unitary character there are infinitely many completely split primes
where the full reciprocal Euler polynomial is a degree power in the translated coordinate.
Deviation: The right side uses exponent s + ix for the character χ₀ |·|^(ix). -/
theorem infinite_split_primes_reciprocalEulerProduct_normTwist
    (χ χ₀ : U𝔽) (hχ₀ : IsOfFinOrder χ₀) (x : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist χ₀ ((x : ℂ) * Complex.I)) :
    {p : RatPrimes | rationalPrimeSplitsCompletely F p ∧
      ∀ S₀ : Finset Primes, (∀ v : Primes, v.under (𝓞 ℚ) = p → v ∈ S₀) →
        ∀ s : ℂ, reciprocalPartialHeckeEulerProduct χ overₚ(S₀, p) s =
          (1 - (p.asIdeal.absNorm : ℂ) ^ (-(s + (x : ℂ) * Complex.I))) ^ degree}.Infinite :=
  by sorry

variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Jₛ" => SIdeleQuotient F S
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "twistₛ" => quasiCharacterNormTwist (G := Jₛ) mₛ
  (IsProperMap.continuous (isProperMap_sIdeleQuotientNorm F S))
local notation "chartₛ(" χ "," h ")" => twistₛ (sIdeleRestriction F S (Subtype.mk (ideleClassNormTwist χ 0) h))
local notation "rhoChart(" χ "," h ")" => fun z ↦ sLocalRhoFactor (chartₛ(χ, h) z)

/-- Paper: Lemma 7.1.2.2, p. 317 and Theorem 7.1.3.2, p. 324.
The multiplicity of the correcting factor is the order of its pole in the norm-twist
coordinate at the chosen quasi-character. It is zero at a point without a pole. -/
def sLocalRhoPoleOrder (c : QuasiCharacter (SIdeleQuotient F S)) : ℕ :=
  (-(sLocalIdelicOrderBound c).untop₀).toNat

/-- Paper: Lemma 7.1.2.2, p. 317. The pole order is the negative of the
order bound used in the target space of the S-local Mellin transform of §5.1. -/
theorem sLocalIdelicOrderBound_eq_neg_poleOrder (c : QuasiCharacter (SIdeleQuotient F S)) :
    sLocalIdelicOrderBound c = ((-(sLocalRhoPoleOrder c : ℤ) : ℤ) : WithTop ℤ) := by sorry

/-- Paper: Theorem 7.1.3.2, p. 324.
A simple pole of the correcting factor has multiplicity one in a unitary chart.
Deviation: States a sanity check comparing the centered and uncentered coordinates. -/
theorem sLocalRhoPoleOrder_eq_one_iff (χ : U𝔽)
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S) (s : ℂ) :
    sLocalRhoPoleOrder (chartₛ(χ, hχ) s) = 1 ↔
      meromorphicOrderAt rhoChart(χ, hχ) s = -1 := by sorry

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)

-- TODO(paper-gap): The common-pole observation preceding Theorem 7.1.3.2 needs
-- distinct residue characteristics. For the trivial character of ℚ(i), both
-- Euler factors over 5 have a pole at 2πi/log 5.

/-- Paper: Theorem 7.1.3.2(1), p. 324.
Two unramified finite places above different rational primes have at most one shared
pole of their local Euler factors. -/
theorem finiteHeckeEulerFactors_common_pole_subsingleton
    (_hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (v w : ↥S) (hv : (ideleClassNormTwist (F := F) χ 0).IsUnramifiedAt v.val)
    (hw : (ideleClassNormTwist (F := F) χ 0).IsUnramifiedAt w.val)
    (hp : (v.val : Primes).under (𝓞 ℚ) ≠ w.val.under (𝓞 ℚ)) :
    {s : ℂ | meromorphicOrderAt (finiteHeckeEulerFactor (F := F) χ v.val) s < 0 ∧
      meromorphicOrderAt (finiteHeckeEulerFactor (F := F) χ w.val) s < 0}.Subsingleton := by sorry

/-- Paper: Theorem 7.1.3.2(2)–(3), p. 324.
The pole order is bounded by the number of places in S, including all infinite places.
Deviation: Uses the proof's bound at every point of the component, which includes the
archimedean points of abscissa zero and all the indicated finite-place poles. -/
theorem sLocalRhoPoleOrder_le_card (s : ℂ) :
    sLocalRhoPoleOrder (chartₛ(χ, hχ) s) ≤ archCount + S.card := by sorry

/-- Paper: Theorem 7.1.3.2(2), p. 324.
In the open left half-plane the pole order is bounded by the number of infinite places.
Deviation: Includes all negative abscissae, as in the local-factor argument, and implies
the stated bounds for negative even abscissae and by the degree. -/
theorem sLocalRhoPoleOrder_le_archimedean_of_re_neg {s : ℂ} (hs : s.re < 0) :
    sLocalRhoPoleOrder (chartₛ(χ, hχ) s) ≤ archCount := by sorry

-- TODO(paper-gap): The bound by r₂ at negative odd abscissae in Theorem 7.1.3.2(2)
-- omits real sign factors. The odd Dirichlet character modulo 4 gives a pole at -1
-- over ℚ, where r₂ = 0.

open Classical in
/-- Paper: Theorem 7.1.3.2(2), p. 324. At a negative odd abscissa the order
is bounded by the number of complex places plus the number of odd real places.
Deviation: Counts the real sign characters whose gamma factors have poles at this parity. -/
theorem sLocalRhoPoleOrder_le_of_re_neg_odd (n : ℕ) {s : ℂ}
    (hs : s.re = -((2 * n + 1 : ℕ) : ℝ)) :
    sLocalRhoPoleOrder (chartₛ(χ, hχ) s) ≤
      (Finset.univ.filter (fun w : InfinitePlace F ↦ w.IsComplex ∨
        w.IsReal ∧ sLocalInfiniteRestriction w (chartₛ(χ, hχ) 0) (-1) = -1)).card := by sorry

open Classical in
/-- Paper: Theorem 7.1.3.2(3), p. 324.
Excess pole orders at finite-place poles can occur at at most the number of infinite
places plus the number of unordered pairs of unramified finite places. -/
theorem sLocalRhoPoleOrder_exceptions_encard_le :
    let S₀ := S.filter (fun v ↦ (ideleClassNormTwist (F := F) χ 0).IsUnramifiedAt v)
    {s : ℂ | degree < sLocalRhoPoleOrder (chartₛ(χ, hχ) s) ∧
      ∃ v ∈ S₀, meromorphicOrderAt (finiteHeckeEulerFactor χ v) s < 0}.encard ≤
        (archCount + S₀.card.choose 2 : ℕ) := by sorry

/-- Paper: Theorem 7.1.3.2(3)(a), p. 324.
For a finite-order character twisted by an imaginary norm power, an excess pole order
can occur only at the negative of that twist parameter. -/
theorem sLocalRhoPoleOrder_excess_eq_neg_normTwist (χ₀ : U𝔽) (hχ₀ : IsOfFinOrder χ₀) (x : ℝ)
    (hx : ideleClassNormTwist χ 0 = ideleClassNormTwist χ₀ ((x : ℂ) * Complex.I))
    {s : ℂ} (hs : degree < sLocalRhoPoleOrder (chartₛ(χ, hχ) s)) :
    s = -((x : ℂ) * Complex.I) := by sorry

-- TODO(prerequisite): Theorem 7.1.3.2(3)(b) needs the algebraic Hecke-character
-- predicate used also in §1.7 and the statement of Schanuel's Conjecture.

local instance instMeasurableSLocalNormOneSec1b :
    MeasurableSpace (MonoidHom.ker (sIdeleQuotientNorm F S)) := borel _

local instance instHaarSLocalNormOneSec1b :
    (sLocalNormOneQuotientMeasure F S).IsHaarMeasure :=
  (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1

/-- Paper: Corollary 7.1.3.3, p. 325.
With a unique infinite place, the homogeneous theta function has the stated logarithmic
upper bound near norm zero. The remainder exponent comes from the largest smaller order.
Deviation: Uses zero when there is no smaller positive order, as in the least-bound
description on p. 326. This includes test functions whose zeta function has no poles. -/
theorem sLocalHomogeneousAdelicTheta_log_bound (harch : archCount = 1) (ψ : PontryaginDual Jₛ)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    let ω := ψ.comp
      (⟨Subgroup.subtype (MonoidHom.ker mₛ), continuous_subtype_val⟩ :
        MonoidHom.ker mₛ →ₜ* Jₛ)
    let normℝ (g : Jₛ) := ((mₛ g : ℝ≥0) : ℝ)
    let poleOrder (s : ℂ) := sLocalPolarMultiplicity f
      (twistₛ ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ) s)
    ∃ (M m : ℕ) (C D : ℝ), IsGreatest (range poleOrder) M ∧
      IsLeast {k : ℕ | ∀ s, poleOrder s < M → poleOrder s ≤ k} m ∧
      m < archCount + S.card ∧ 0 < C ∧ 0 ≤ D ∧
      ∀ᶠ g in comap normℝ (𝓝[>] 0),
        ‖sLocalHomogeneousAdelicTheta F S (sLocalNormOneQuotientMeasure F S) ω f g‖ ≤
          C * |Real.log (normℝ g)| ^ (archCount + S.card - 1) +
            D * |Real.log (normℝ g)| ^ ((m : ℤ) - 1) := by sorry

end Polar

section Spectral

local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "Aℂ" => SchwartzBergman (univ : Set ℝ)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- Paper: Situation 7.1.4.1, p. 326.
The restriction of a unitary character along the chosen idelic norm section is a
purely imaginary power with a unique real frequency. -/
theorem existsUnique_ideleNormSection_character_phase (χ : U𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (_hτ : RightInverse τ (ideleNorm F)) :
    ∃! x : ℝ, ∀ t : ℝ≥0ˣ, (χ (QuotientGroup.mk (τ t)) : ℂ) =
      (((t : ℝ≥0) : ℝ) : ℂ) ^ ((x : ℂ) * Complex.I) := by
  let q : I𝔽 →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let incl : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  let c := (incl.comp χ).comp (q.comp τ)
  obtain ⟨z, ⟨hz, hval⟩, huniq⟩ := existsUnique_unitaryComplexPower c
    (fun t ↦ Circle.norm_coe (χ (q (τ t))))
  have him : (z.im : ℂ) * Complex.I = z := by
    apply Complex.ext <;> simp [hz]
  refine ⟨z.im, fun t ↦ (hval t).trans (by rw [him]), fun x hx ↦ ?_⟩
  have he := huniq ((x : ℂ) * Complex.I) ⟨by simp, hx⟩
  simpa using congrArg Complex.im he

/-- Paper: Situation 7.1.4.1, p. 326. The Mellin transform on the polar
subspace descends through homogeneous theta to the entire Schwartz–Bergman space.
On a test function it is the section integral with the weight of the chosen character. -/
theorem exists_globalPolarThetaMellin (χ : U𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (_hτ : RightInverse τ (ideleNorm F)) :
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
      (ideleClassNorm F).ker →ₜ* C𝔽)
    let P := adelePolarSubspace F
    let T := (homogeneousAdelicThetaLinearMap F ω).domRestrict P
    ∃ Z : (↥P ⧸ LinearMap.ker T) →L[ℂ] Aℂ, ∀ (f : P) (s : ℂ),
      (Z (Submodule.Quotient.mk f)).val s =
        homogeneousThetaMellinIntegral τ ω f.val (ideleClassNormTwist χ s) ∧
      (Z (Submodule.Quotient.mk f)).val s =
        globalIdelicZFunction f.val (ideleClassNormTwist χ s) := by sorry

/-- Paper: §7.1.4, p. 326.
The entire functions in the compact-open continuous function algebra are closed under
addition and multiplication and contain every constant function. -/
theorem entireContinuousMap_subalgebra_properties :
    (∀ c : ℂ, Differentiable ℂ (algebraMap ℂ C(ℂ, ℂ) c : ℂ → ℂ)) ∧
    (∀ f g : C(ℂ, ℂ), Differentiable ℂ f → Differentiable ℂ g →
      Differentiable ℂ (f + g : C(ℂ, ℂ))) ∧
    (∀ f g : C(ℂ, ℂ), Differentiable ℂ f → Differentiable ℂ g →
      Differentiable ℂ (f * g : C(ℂ, ℂ))) := by
  exact ⟨fun c ↦ differentiable_const c, fun _ _ hf hg ↦ hf.add hg,
    fun _ _ hf hg ↦ hf.mul hg⟩

/-- Paper: §7.1.4, p. 326.
The ring of entire functions carries the compact-open topology of uniform convergence
on compact sets inherited from the ambient space of continuous functions. -/
def entireContinuousMapSubalgebra : Subalgebra ℂ C(ℂ, ℂ) where
  carrier := {f | Differentiable ℂ f}
  algebraMap_mem' := entireContinuousMap_subalgebra_properties.1
  zero_mem' := entireContinuousMap_subalgebra_properties.1 0
  one_mem' := entireContinuousMap_subalgebra_properties.1 1
  add_mem' := fun hf hg ↦ entireContinuousMap_subalgebra_properties.2.1 _ _ hf hg
  mul_mem' := fun hf hg ↦ entireContinuousMap_subalgebra_properties.2.2 _ _ hf hg

/-- Paper: §7.1.4, p. 326.
Complex conjugation is excluded from the algebra of entire functions.
Deviation: States a sanity check distinguishing the entire subalgebra from the ambient space. -/
theorem conj_not_mem_entireContinuousMapSubalgebra :
    (⟨starRingEnd ℂ, Complex.continuous_conj⟩ : C(ℂ, ℂ)) ∉ entireContinuousMapSubalgebra :=
  by sorry

local notation "Entire" => Subtype (fun f : C(ℂ, ℂ) ↦ f ∈ entireContinuousMapSubalgebra)

/-- Paper: Theorem 7.1.4.2(1), p. 326.
The pole-removing multiple of the completed Hecke continuation is entire, with values
at the canceled poles supplied by meromorphic normalization. -/
theorem regularizedCompletedHeckeL_differentiable (χ : U𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (hτ : RightInverse τ (ideleNorm F)) (L : ℂ → ℂ) (_hL : MeromorphicNFOn L univ)
    (_hEq : ∀ s : halfPlane, L s = completedHeckeL χ s) :
    let x₀ := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
    let b := (x₀ : ℂ) * Complex.I
    let δ : ℕ := open Classical in
      if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
    Differentiable ℂ (toMeromorphicNFOn (fun s ↦ (s + b) ^ δ * (1 - s - b) ^ δ * L s) univ) :=
  by sorry

/-- Paper: Theorem 7.1.4.2(1), p. 326.
The generator of the spectral ideal is the completed Hecke continuation multiplied by
the indicated pole-removing polynomial.
Deviation: Takes the holomorphic values at the canceled poles by meromorphic normalization. -/
def regularizedCompletedHeckeL (χ : U𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (hτ : RightInverse τ (ideleNorm F)) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hEq : ∀ s : halfPlane, L s = completedHeckeL χ s) : Entire :=
  open Classical in
  let x₀ := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  let b := (x₀ : ℂ) * Complex.I
  let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
  let h := regularizedCompletedHeckeL_differentiable χ τ hτ L hL hEq
  ⟨⟨toMeromorphicNFOn (fun s ↦ (s + b) ^ δ * (1 - s - b) ^ δ * L s) univ, h.continuous⟩, h⟩

/-- Paper: Theorem 7.1.4.2(1), pp. 326–327.
At the two poles of a pure imaginary norm twist, the regularized generator is nonzero.
Deviation: States a sanity check safeguarding the removable values at the two poles. -/
theorem regularizedCompletedHeckeL_ne_zero_at_canceled_poles
    (χ : U𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hEq : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    let x₀ := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
    let b := (x₀ : ℂ) * Complex.I
    let Λ := regularizedCompletedHeckeL χ τ hτ L hL hEq
    Λ.val (-b) ≠ 0 ∧ Λ.val (1 - b) ≠ 0 := by sorry

/-- Paper: Equation (7.1.4.4), p. 326.
Evaluation of the m-th complex derivative at a point defines a continuous linear
functional in the compact-open topology. -/
theorem entireJet_properties (ρ : ℂ) (m : ℕ) :
    let jet (f : Entire) := iteratedDeriv m (f.val : ℂ → ℂ) ρ
    (∀ f g : Entire, jet (f + g) = jet f + jet g) ∧
      (∀ (a : ℂ) (f : Entire), jet (a • f) = a • jet f) ∧ Continuous jet := by
  dsimp only
  have hd (f : Entire) : Differentiable ℂ (f.val : ℂ → ℂ) := f.property
  refine ⟨fun f g ↦ iteratedDeriv_add (hd f).contDiff.contDiffAt (hd g).contDiff.contDiffAt,
    fun a f ↦ iteratedDeriv_const_smul_field a (f.val : ℂ → ℂ), ?_⟩
  apply continuous_iff_continuousAt.mpr
  intro f
  have hlim (n : ℕ) : TendstoLocallyUniformlyOn
      (fun g : Entire ↦ iteratedDeriv n (g.val : ℂ → ℂ))
      (iteratedDeriv n (f.val : ℂ → ℂ)) (𝓝 f) univ := by
    induction n with
    | zero =>
      exact tendstoLocallyUniformlyOn_univ.mpr
        (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp
          (show Tendsto (fun g : Entire ↦ g.val) (𝓝 f) (𝓝 f.val) from
            continuous_subtype_val.continuousAt))
    | succ n ih =>
      simpa only [iteratedDeriv_succ, Function.comp_def] using
        ih.deriv (Filter.Eventually.of_forall fun g ↦
          ((hd g).contDiff.differentiable_iteratedDeriv' n).differentiableOn) isOpen_univ
  exact (hlim m).tendsto_at (mem_univ ρ)

/-- Paper: Equation (7.1.4.4), p. 326.
The jet functional takes the m-th derivative of an entire function at the indicated point. -/
def entireJet (ρ : ℂ) (m : ℕ) : StrongDual ℂ Entire where
  toFun f := iteratedDeriv m (f.val : ℂ → ℂ) ρ
  map_add' := (entireJet_properties ρ m).1
  map_smul' := (entireJet_properties ρ m).2.1
  cont := (entireJet_properties ρ m).2.2

/-- Paper: Equation (7.1.4.4), p. 326.
The functional evaluates the prescribed complex derivative.
Deviation: Its evaluation law is the sanity check for the bundled functional. -/
theorem entireJet_apply (ρ : ℂ) (m : ℕ) (f : Entire) :
    entireJet ρ m f = iteratedDeriv m (f.val : ℂ → ℂ) ρ := rfl

/-- Paper: Equation (7.1.4.3), p. 326.
The jet space at a zero of multiplicity n is spanned by evaluations of the first n
derivatives, beginning with the value. It inherits the topology of the strong dual. -/
def entireJetSpace (ρ : ℂ) (n : ℕ) : Submodule ℂ (StrongDual ℂ Entire) :=
  Submodule.span ℂ (range fun m : Fin n ↦ entireJet ρ m.val)

/-- Paper: Equation (7.1.4.3), p. 326.
There are exactly n independent jet coordinates at a point for order n.
Deviation: States the dimension check for the span used in the definition. -/
theorem entireJetSpace_finrank (ρ : ℂ) (n : ℕ) :
    Module.finrank ℂ (entireJetSpace ρ n) = n := by sorry

/-- Paper: Theorem 7.1.4.2(1), p. 326.
The annihilator of a principal ideal consists of the continuous linear functionals
that vanish on that ideal. Its topology is inherited from the strong dual. -/
def entireIdealAnnihilator (g : Entire) : Submodule ℂ (StrongDual ℂ Entire) :=
  ((Ideal.span ({g} : Set Entire)).restrictScalars ℂ).dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ)

/-- Paper: Theorem 7.1.4.2(1), p. 326.
The annihilator for the constant unit generator is zero.
Deviation: States a sanity check for the annihilator. -/
theorem entireIdealAnnihilator_one : entireIdealAnnihilator 1 = ⊥ := by
  ext φ
  simp only [entireIdealAnnihilator, Submodule.mem_comap, Submodule.mem_dualAnnihilator, Submodule.mem_bot]
  have hmem : ∀ w : Entire, w ∈ Submodule.restrictScalars ℂ (Ideal.span ({1} : Set Entire)) := by
    intro w
    simp [Ideal.span_singleton_one]
  constructor
  · intro h
    ext w
    simpa using h w (hmem w)
  · intro h w _
    simp [h]

-- TODO(paper-gap): In (7.1.4.2) the product is the quotient's model, while the
-- continuous dual consists of finite-support jets as computed on p. 328.
-- The proof's second pole-removing factor also has the wrong sign of ix₀.

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
  (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hEq : ∀ s : halfPlane, L s = completedHeckeL χ s)

open Classical in
/-- Paper: Theorem 7.1.4.2(1), pp. 326–328.
The strong annihilator of the regularized Hecke ideal is the locally convex direct
sum of the jet spaces of the completed Hecke zeros.
Deviation: Uses the direct sum computed in the proof. A zero is detected by positive
meromorphic order, since a pole can have value zero in meromorphic normal form. -/
theorem spectralAnnihilator_directSum :
    let Λ := regularizedCompletedHeckeL χ τ hτ L hL hEq
    let Zeros := {ρ : ℂ // 0 < meromorphicOrderAt L ρ}
    let J (ρ : Zeros) := entireJetSpace ρ.val (meromorphicOrderAt L ρ.val).untop₀.toNat
    letI instJetAddSec1b : ∀ ρ : Zeros, AddCommGroup ↥(J ρ) :=
      fun ρ ↦ Submodule.addCommGroup (J ρ)
    letI instJetModuleSec1b : ∀ ρ : Zeros, Module ℂ ↥(J ρ) :=
      fun ρ ↦ Submodule.module (J ρ)
    let inclusion := DirectSum.lof ℂ Zeros (fun ρ ↦ ↥(J ρ))
    letI instJetSumTopologySec1b : TopologicalSpace (⨁ ρ : Zeros, ↥(J ρ)) :=
      locallyConvexFinalTopology inclusion
    ∃ e : (⨁ ρ : Zeros, ↥(J ρ)) ≃L[ℂ] entireIdealAnnihilator Λ,
      ∀ (ρ : Zeros) (a : ↥(J ρ)), (e (inclusion ρ a)).val = a.val := by sorry

/-- Paper: Theorem 7.1.4.2(2), p. 326.
An entire Schwartz–Bergman function includes continuously into the compact-open space
by keeping its value at each point. -/
theorem exists_schwartzBergman_entireInclusion :
    ∃ i : Aℂ →L[ℂ] Entire, ∀ (f : Aℂ) (z : ℂ), (i f).val z = f.val z := by sorry

/-- Paper: Theorem 7.1.4.2(2), pp. 326–327. The canonical map includes entire
Schwartz–Bergman functions into the compact-open space of entire functions. -/
def schwartzBergmanEntireInclusion : Aℂ →L[ℂ] Entire :=
  exists_schwartzBergman_entireInclusion.choose

/-- Paper: Theorem 7.1.4.2(2), p. 326. Inclusion preserves the value at every point. -/
theorem schwartzBergmanEntireInclusion_apply (f : Aℂ) (s : ℂ) :
    (schwartzBergmanEntireInclusion f).val s = f.val s :=
  exists_schwartzBergman_entireInclusion.choose_spec f s

/-- Paper: Theorem 7.1.4.2(2), pp. 326–327. The preimage of the entire principal
ideal consists of the Schwartz–Bergman functions divisible by its generator. -/
def schwartzBergmanDivisible (g : Entire) : Submodule ℂ Aℂ :=
  ((Ideal.span ({g} : Set Entire)).restrictScalars ℂ).comap
    schwartzBergmanEntireInclusion.toLinearMap

/-- Paper: Theorem 7.1.4.2(2), pp. 326–328. Divisibility defines a closed subspace,
so its quotient with the Schwartz–Bergman quotient topology is Hausdorff. -/
theorem schwartzBergmanDivisible_isClosed (g : Entire) :
    IsClosed (schwartzBergmanDivisible g : Set Aℂ) := by sorry

/-- Paper: Theorem 7.1.4.2(2), pp. 326–327 and Theorem 7.1.4.3(2), p. 331.
Restriction to Schwartz–Bergman functions induces an injective map with dense image
in the strong dual of the quotient by the corresponding divisibility conditions.
Deviation: States the analytic restriction map for every entire generator. -/
theorem exists_schwartzBergman_jetRestriction (g : Entire) :
    ∃ U : ↥(entireIdealAnnihilator g) →L[ℂ] StrongDual ℂ (Aℂ ⧸ schwartzBergmanDivisible g),
      Injective U ∧ DenseRange U ∧ ∀ (ℓ : entireIdealAnnihilator g) (f : Aℂ),
        U ℓ (Submodule.Quotient.mk f) = ℓ.val (schwartzBergmanEntireInclusion f) := by sorry

/-- Paper: Theorem 7.1.4.2(2), pp. 326–327. The range identification from
the global converse transports restriction to the dual of the theta Mellin quotient.
Deviation: The range equality from §6.3.2 is an explicit hypothesis. -/
theorem spectralTheta_jetRestriction_of_range_eq :
    let Z := (exists_globalPolarThetaMellin χ τ hτ).choose
    let g := regularizedCompletedHeckeL χ τ hτ L hL hEq
    LinearMap.range Z.toLinearMap = schwartzBergmanDivisible g →
      ∃ U : ↥(entireIdealAnnihilator g) →L[ℂ] StrongDual ℂ (Aℂ ⧸ LinearMap.range Z.toLinearMap),
        Injective U ∧ DenseRange U ∧ ∀ (ℓ : entireIdealAnnihilator g) (f : Aℂ),
          U ℓ (Submodule.Quotient.mk f) = ℓ.val (schwartzBergmanEntireInclusion f) := by
  intro Z g h
  rw [h]
  exact exists_schwartzBergman_jetRestriction g

-- TODO(paper-gap): In (7.1.4.6), with φ already in the Mellin coordinate, the
-- factor t^(ix₀) shifts the derivative to ρ + ix₀. The proof on p. 329 uses t^ρ.

/-- Paper: Equations (7.1.4.6) and (7.1.4.27), pp. 327, 329 and 331.
On the Schwartz–Bergman space, jet evaluation is a logarithmic moment of the inverse
Mellin transform. Both the inverse integral at positive t and the moment converge.
Deviation: Uses the exponent ρ from the derivation on p. 329 and the orbital formula. -/
theorem schwartzBergman_jet_eq_mellinInv_moment (f : Aℂ) (ρ : ℂ) (m : ℕ) :
    let φ : ℂ → ℂ := f.val
    let moment := fun t : ℝ ↦ (Real.log t : ℂ) ^ m * mellinInv 0 φ t
    Complex.VerticalIntegrable φ 0 ∧ MellinConvergent moment ρ.re ∧
      iteratedDeriv m φ ρ = mellin moment ρ := by sorry

-- TODO(paper-gap): Theorem 7.1.4.2(4) names the ordinary Schwartz quotient, whereas
-- the setup and argument use the exponentially decaying quotient. Theorem
-- 7.1.4.3(3) makes the same switch before (7.1.4.28).

/-- Paper: Theorem 7.1.4.2(4), pp. 327, 330–331. On the entire Schwartz–Bergman
space the factorial-normalized derivatives across the closed critical strip are
equicontinuous and bounded in the strong dual.
Deviation: States the estimate on the Mellin side for all derivative orders. -/
theorem schwartzBergman_normalizedJets :
    let jets := fun i : {z : ℂ // z.re ∈ Icc 0 1} × ℕ ↦
      (i.2.factorial : ℂ)⁻¹ • (entireJet i.1.val i.2).comp schwartzBergmanEntireInclusion
    Equicontinuous (fun i (f : Aℂ) ↦ jets i f) ∧
      Bornology.IsVonNBounded ℂ (range jets) := by sorry

-- TODO(paper-gap): Theorem 7.1.4.3(1) misses collisions across rational primes.
-- At s = 0 for the trivial character of ℚ with 2 and 3 removed, the orbital
-- generator has a double zero. The separate p-blocks supply only evaluation at 0.
-- Part (3) also omits the pole-removing polynomial when indexing its jets:
-- with just 2 removed, (1 - 2⁻ˢ)L(s,1) has order zero at the origin.

/-- Paper: Theorem 7.1.4.3(1), pp. 331–332.
The finite Euler correction multiplies the regularized completed L-function by the
reciprocal factors of the selected places, with factor one at ramified places. -/
theorem orbitalHeckeGenerator_differentiable (S₀ : Finset Primes) :
    Differentiable ℂ (fun s ↦
      reciprocalPartialHeckeEulerProduct χ S₀ s *
        (regularizedCompletedHeckeL χ τ hτ L hL hEq).val s) := by sorry

/-- Paper: Theorem 7.1.4.3(1), p. 331.
The entire generator of the orbital ideal is the finite Euler correction of the regularized
completed Hecke L-function. -/
def orbitalHeckeGenerator (S₀ : Finset Primes) : Entire :=
  let g := fun s ↦ reciprocalPartialHeckeEulerProduct χ S₀ s *
    (regularizedCompletedHeckeL χ τ hτ L hL hEq).val s
  let hg := orbitalHeckeGenerator_differentiable χ τ hτ L hL hEq S₀
  ⟨⟨g, hg.continuous⟩, hg⟩

/-- Paper: Theorem 7.1.4.3(1), p. 331.
Removing an empty set of Euler factors recovers the spectral generator.
Deviation: States a sanity check for the orbital ideal generator. -/
theorem orbitalHeckeGenerator_empty :
    orbitalHeckeGenerator χ τ hτ L hL hEq ∅ = regularizedCompletedHeckeL χ τ hτ L hL hEq :=
  by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  simp [orbitalHeckeGenerator, reciprocalPartialHeckeEulerProduct]

/-- Paper: Theorem 7.1.4.3(1), pp. 331–332. At the canceled pole on the
imaginary axis of a pure norm power, every removed finite place adds one jet.
Deviation: Records the total order at a point where indexing by the raw product loses a jet. -/
theorem orbitalHeckeGenerator_order_at_canceled_pole (S₀ : Finset Primes)
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    let x := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
    let g := orbitalHeckeGenerator χ τ hτ L hL hEq S₀
    analyticOrderAt (g.val : ℂ → ℂ) (-((x : ℂ) * Complex.I)) = (S₀.card : ℕ∞) := by sorry

open Classical in
/-- Paper: Theorem 7.1.4.3(1), p. 331.
The strong annihilator of the orbital ideal is a locally convex direct sum of jets.
Deviation: Counts zeros of the regularized generator of the ideal in part (1),
adding all coincident local orders even at a canceled pole of the completed L-function.
Uses the locally convex direct sum from p. 328. -/
theorem orbitalAnnihilator_directSum (S₀ : Finset Primes) :
    let g := orbitalHeckeGenerator χ τ hτ L hL hEq S₀
    let Zeros := {ρ : ℂ // 0 < analyticOrderAt (g.val : ℂ → ℂ) ρ}
    let J (ρ : Zeros) := entireJetSpace ρ.val (analyticOrderAt (g.val : ℂ → ℂ) ρ.val).toNat
    letI instJetAddSec1b : ∀ ρ : Zeros, AddCommGroup ↥(J ρ) :=
      fun ρ ↦ Submodule.addCommGroup (J ρ)
    letI instJetModuleSec1b : ∀ ρ : Zeros, Module ℂ ↥(J ρ) :=
      fun ρ ↦ Submodule.module (J ρ)
    let inclusion := DirectSum.lof ℂ Zeros (fun ρ ↦ ↥(J ρ))
    letI instJetSumTopologySec1b : TopologicalSpace (⨁ ρ : Zeros, ↥(J ρ)) :=
      locallyConvexFinalTopology inclusion
    ∃ e : (⨁ ρ : Zeros, ↥(J ρ)) ≃L[ℂ] entireIdealAnnihilator g,
      ∀ (ρ : Zeros) (a : ↥(J ρ)), (e (inclusion ρ a)).val = a.val := by sorry

open Classical in
/-- Paper: Theorem 7.1.4.2(3), p. 327 and Theorem 7.1.4.3(3), pp. 331–332.
The derivative functionals of the regularized generator have biorthogonal
Schwartz–Bergman representatives. Their classes work in the divisibility quotient.
Deviation: The empty set gives the spectral family. The indices use the total
order of the regularized generator, including at canceled poles. -/
theorem orbitalSchwartzBergman_biorthogonal (S₀ : Finset Primes) :
    let g := orbitalHeckeGenerator χ τ hτ L hL hEq S₀
    let indices := {p : ℂ × ℕ // (p.2 : ℕ∞) < analyticOrderAt (g.val : ℂ → ℂ) p.1}
    ∃ b : indices → Aℂ, ∀ i j : indices,
      iteratedDeriv i.val.2 (b j).val i.val.1 = if i = j then 1 else 0 := by sorry

-- TODO(prerequisite): Transport the analytic quotient and its jet families to
-- (7.1.4.7) by §6.3.2. The orbital identification (7.1.4.26)–(7.1.4.28)
-- also uses the global principal-value operator of §5.3.1.

end Spectral

end RiemannMasullo
