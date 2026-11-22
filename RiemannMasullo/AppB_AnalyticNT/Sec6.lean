module

public import RiemannMasullo.AppB_AnalyticNT.Sec1
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Classical zero-free regions for Hecke L-functions

Masullo, §B.6, pp. 636–643. The finite Hecke L-function is represented by a
meromorphic continuation in normal form, as in §B.1.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Asymptotics Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "𝒳[" F "]" => HeckeCharacter (𝓞 F) F
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)
local notation "atHeight" => comap (abs ∘ Complex.im) atTop
local notation "atAbsTop" => comap (abs : ℝ → ℝ) atTop

/-- Paper: Proposition B.6.1.1, p. 636. An absolute constant gives a
zero-free region for each finite Hecke L-function, with a scale depending on
the field and character. Meromorphic order distinguishes poles from zeros.
Deviation: The scale is chosen greater than `1/3` so the logarithm in the
denominator is positive at every height. It is an existential scale and may be
enlarged to exclude an exceptional zero. The separate real-zero clause is false. -/
theorem finiteHeckeL_zeroFreeRegion :
    ∃ A : ℝ, 0 < A ∧
      ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]),
        ∃ B : ℝ, 1 / 3 < B ∧
          ∀ (L : ℂ → ℂ), MeromorphicNFOn L univ →
            (∀ s : halfPlane, L s = finiteHeckeL χ s) →
            ∀ s : ℂ, 1 - A / ((Module.finrank ℚ F : ℝ) ^ 4 *
              Real.log (B * (|s.im| + 3))) ≤ s.re → meromorphicOrderAt L s ≤ 0 := by
  sorry

-- TODO(paper-gap): The paragraph after (B.6.1.1) identifies two different conductors.
-- A pure imaginary norm twist preserves the finite conductor but changes the
-- archimedean parameter. No conductor-uniform exceptional-zero assertion is made here.
-- TODO(paper-gap): The real-zero clause of Proposition B.6.1.1 is false on [1/2, 1].
-- If ζ(1/2 + iγ) = 0 with γ ≠ 0, the nonquadratic norm character |·|^(iγ)
-- over ℚ has finite L-function ζ(s + iγ), which vanishes at the real point 1/2.
-- The square of this character has finite L-function ζ(s + 2iγ), with a pole.

/-- Paper: §B.6.1.2, p. 636. The value at a nonzero integral ideal is the
product of local uniformizer values with the ideal's prime exponents. At a
ramified prime the local value used in this product is zero.
Deviation: The value at the zero ideal is set to zero. -/
def heckeIdealValue (χ : 𝒳[F]) (I : Ideal (𝓞 F)) : ℂ :=
  open Classical in
  if I = ⊥ then 0 else
    ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      (if χ.IsUnramifiedAt v then χ.localValue v else 0) ^ multiplicity v.asIdeal I

open Classical in
/-- Paper: §B.6.1.2, p. 636. The value on a positive power of a prime ideal
is the corresponding power of the local value, or zero at a ramified prime. -/
theorem heckeIdealValue_prime_pow (χ : 𝒳[F]) (v : HeightOneSpectrum (𝓞 F))
    {k : ℕ} (hk : 0 < k) :
    heckeIdealValue χ (v.asIdeal ^ k) =
      if χ.IsUnramifiedAt v then χ.localValue v ^ k else 0 := by
  sorry

/-- Paper: Equation (B.6.1.2), p. 636. To the right of one, the series indexed
by nonzero integral ideals converges absolutely to the finite Hecke L-function. -/
theorem finiteHeckeL_hasSum_ideals (χ : U[F]) (s : halfPlane) :
    HasSum (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦
      heckeIdealValue (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ) ^ (s : ℂ))
      (finiteHeckeL χ s) := by
  sorry

/-- Paper: Equation (B.6.1.3), p. 636. The summatory function adds the values
at nonzero integral ideals of norm at most `x`. -/
def heckeIdealSummatory (χ : 𝒳[F]) (x : ℝ) : ℂ :=
  ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}, heckeIdealValue χ I.val

/-- Paper: Equation (B.6.1.3), p. 636. At `x = 1` only the unit ideal contributes. -/
theorem heckeIdealSummatory_one (χ : 𝒳[F]) : heckeIdealSummatory χ 1 = 1 := by
  sorry

/-- Paper: Equation (B.6.1.4), p. 636. The coefficient at `x` sums the
values at nonzero integral ideals of norm exactly `x`. The sum is zero if
there are no such ideals. -/
def heckeNormCoefficient (χ : 𝒳[F]) (x : ℝ) : ℂ :=
  ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = x}, heckeIdealValue χ I.val

/-- Paper: Equation (B.6.1.4), p. 636. At natural numbers the coefficients
agree with the coefficients of Mathlib's formal Euler product. -/
theorem heckeNormCoefficient_natCast (χ : 𝒳[F]) (m : ℕ) :
    heckeNormCoefficient χ (m : ℝ) = χ.LFunction m := by
  sorry

/-- Paper: Equation (B.6.1.5), p. 637. Grouping the terms by their integral
norm gives the absolutely convergent Dirichlet series with coefficients `aₘ`. -/
theorem finiteHeckeL_hasSum_normCoefficients (χ : U[F]) (s : halfPlane) :
    LSeriesHasSum (fun m : ℕ ↦ heckeNormCoefficient (ideleClassNormTwist χ 0) (m : ℝ))
      (s : ℂ) (finiteHeckeL χ s) := by
  let normIndex (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) : ℕ := I.val.absNorm
  let value := heckeIdealValue (ideleClassNormTwist χ 0)
  have hs : (s : ℂ) ≠ 0 := by
    intro h
    have hr : 1 < (s : ℂ).re := s.property
    norm_num [h] at hr
  refine ((finiteHeckeL_hasSum_ideals χ s).tsum_fiberwise normIndex).congr_fun ?_
  intro n
  symm
  rw [LSeries.term_of_ne_zero' hs]
  let normFiber : Set (Ideal (𝓞 F)) := {I | I ≠ ⊥ ∧ (I.absNorm : ℝ) = (n : ℝ)}
  let e : (normIndex ⁻¹' ({n} : Set ℕ) : Set {I : Ideal (𝓞 F) // I ≠ ⊥}) ≃ normFiber :=
    { toFun := fun I ↦ ⟨I.val.val, I.val.property,
        by exact_mod_cast (show I.val.val.absNorm = n from I.property)⟩
      invFun := fun I ↦ ⟨⟨I.val, I.property.1⟩, by
        change I.val.absNorm = n
        exact_mod_cast I.property.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hnorm (I : normFiber) : I.val.absNorm = n := by exact_mod_cast I.property.2
  rw [← e.symm.tsum_eq]
  change (∑' I : normFiber, value I.val / (I.val.absNorm : ℂ) ^ (s : ℂ)) =
    heckeNormCoefficient (ideleClassNormTwist χ 0) (n : ℝ) / (n : ℂ) ^ (s : ℂ)
  let : Finite normFiber :=
    ((Ring.HasFiniteQuotients.finite_absNorm_eq n).subset
      (show normFiber ⊆ {I | I.absNorm = n} from fun I hI ↦ hnorm ⟨I, hI⟩)).to_subtype
  simp_rw [hnorm, tsum_div_const, tsum_eq_finsum (Set.toFinite _)]
  rfl

/-- Paper: Equation (B.6.1.6), p. 637. For each positive `ε`, the summatory
function is bounded by a constant times `x^(1 + ε)`, uniformly in unitary characters. -/
theorem heckeIdealSummatory_bound (F : Type*) [Field F] [NumberField F] {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ χ : U[F],
      ‖heckeIdealSummatory (ideleClassNormTwist χ 0) x‖ ≤ C * x ^ (1 + ε) := by
  sorry

-- TODO(paper-gap): Equation (B.6.1.7) multiplies the norm-one class volume by an
-- extra inverse square root of the discriminant under the normalization in §A.3.

/-- Paper: Lemma B.6.1.2(1), p. 637. For a unitary character trivial on
norm-one classes, undoing its imaginary norm twist gives the ideal-counting
limit at the residue of Dedekind zeta.
Deviation: Uses Mathlib's `dedekindZeta_residue`, the class volume in §A.3,
with the extra printed inverse square root of the discriminant removed. -/
theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    (∃! t₀ : ℝ, ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) ∧
      ∀ t₀ : ℝ, ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀) →
        Tendsto (fun x : ℝ ↦ heckeIdealSummatory (ideleClassNormTwist χ (Complex.I * t₀)) x / x)
          atTop (𝓝 (dedekindZeta_residue F : ℂ)) := by
  sorry

/-- Paper: Lemma B.6.1.2(2), p. 637. If the character is nontrivial on norm-one
classes, its summatory function divided by `x` tends to zero. -/
theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    Tendsto (fun x : ℝ ↦ heckeIdealSummatory (ideleClassNormTwist χ 0) x / x) atTop (𝓝 0) := by
  sorry

/-- Paper: Theorem B.6.1.3, p. 637. The logarithmic derivative is bounded by
a squared logarithm for large absolute heights, uniformly over the narrower
region defined by `α * η`. The Dedekind zeta continuation is the one for the
trivial character. For fixed field, character and `α`, the implied constant
works for every admissible width. Its height threshold may depend on the width.
Deviation: The width is represented by a real function restricted to `t ≥ 0`.
Decreasing is expressed as nonincreasing, and the logarithm uses absolute height.
Eventual analyticity and nonvanishing make the logarithmic derivative well-defined. -/
theorem finiteHeckeL_logDeriv_isBigO_of_zeroFree (χ : U[F]) (L Z : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hZ : MeromorphicNFOn Z univ) (hZSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hα : ∀ z : ℂ, 0 < ‖z - 1‖ → ‖z - 1‖ < α → meromorphicOrderAt Z z ≤ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ → ℝ,
      MapsTo η (Ici 0) (Ioc 0 (1 / 2)) →
      DifferentiableOn ℝ η (Ici 0) → AntitoneOn η (Ici 0) →
      Tendsto (derivWithin η (Ici 0)) atTop (𝓝 0) →
      ((fun t ↦ (η t)⁻¹) =O[atTop] Real.log) →
      (∀ s : ℂ, 1 - η |s.im| < s.re → meromorphicOrderAt L s ≤ 0) →
      let l := atHeight ⊓ 𝓟 {s : ℂ | 1 - α * η |s.im| ≤ s.re}
      (∀ᶠ s in l, AnalyticAt ℂ L s ∧ L s ≠ 0) ∧
        Asymptotics.IsBigOWith C l (logDeriv L) (fun s ↦ (Real.log |s.im|) ^ 2) := by
  sorry

/-- Paper: Equation (B.6.1.13), p. 638. The ideal von Mangoldt function is
`log (N p)` on positive powers of a nonzero prime ideal `p` and zero elsewhere. -/
def idealVonMangoldt (I : Ideal (𝓞 F)) : ℝ :=
  open Classical in
  if h : ∃ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, 0 < k ∧ I = v.asIdeal ^ k then
    Real.log (h.choose.asIdeal.absNorm : ℝ)
  else 0

/-- Paper: Equation (B.6.1.13), p. 638. The value at a positive prime-ideal
power is the logarithm of the prime's norm, independently of the exponent. -/
theorem idealVonMangoldt_prime_pow (v : HeightOneSpectrum (𝓞 F)) {k : ℕ} (hk : 0 < k) :
    idealVonMangoldt (v.asIdeal ^ k) = Real.log (v.asIdeal.absNorm : ℝ) := by
  sorry

/-- Paper: §B.6.1.2, p. 638. The twisted von Mangoldt value is the product
of the ideal character value and the ideal von Mangoldt weight. -/
def heckeIdealVonMangoldt (χ : 𝒳[F]) (I : Ideal (𝓞 F)) : ℂ :=
  heckeIdealValue χ I * (idealVonMangoldt I : ℂ)

/-- Paper: §B.6.1.2, p. 638. At a positive power of an unramified prime, the
twisted weight is the character power times the logarithm of the prime norm. -/
theorem heckeIdealVonMangoldt_prime_pow (χ : 𝒳[F]) (v : HeightOneSpectrum (𝓞 F))
    (hv : χ.IsUnramifiedAt v) {k : ℕ} (hk : 0 < k) :
    heckeIdealVonMangoldt χ (v.asIdeal ^ k) =
      χ.localValue v ^ k * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) := by
  sorry

/-- Paper: Equation (B.6.1.12), p. 638. To the right of one, the negative of
the Dirichlet series weighted by the ideal von Mangoldt function converges
absolutely to the logarithmic derivative of the finite Hecke L-function. -/
theorem finiteHeckeL_logDeriv_hasSum_ideals (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (s : halfPlane) :
    AnalyticAt ℂ L (s : ℂ) ∧ L s ≠ 0 ∧
      HasSum (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦
        -heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val /
          (I.val.absNorm : ℂ) ^ (s : ℂ)) (logDeriv L s) := by
  sorry

/-- Paper: Equation (B.6.1.14), p. 638. The coefficient `Aₘ` sums the
character-weighted von Mangoldt values over nonzero ideals of norm `m`.
Deviation: The empty sum at `m = 0` is also defined. -/
def heckeLogDerivCoefficient (χ : 𝒳[F]) (m : ℕ) : ℂ :=
  ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m}, heckeIdealVonMangoldt χ I.val

/-- Paper: Equation (B.6.1.14), p. 638. Over the rationals with trivial
character these coefficients recover the classical von Mangoldt function. -/
theorem heckeLogDerivCoefficient_trivial_rat (m : ℕ) :
    heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[ℚ]) 0) m =
      (ArithmeticFunction.vonMangoldt m : ℂ) := by
  sorry

/-- Paper: Lemma B.6.1.4, p. 638. The logarithmic-derivative coefficients are
bounded by a constant times `log m`, with the constant depending only on the field degree. -/
theorem heckeLogDerivCoefficient_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type*) [Field F] [NumberField F], Module.finrank ℚ F = d →
        ∀ᶠ m : ℕ in atTop, ∀ χ : U[F],
          ‖heckeLogDerivCoefficient (ideleClassNormTwist χ 0) m‖ ≤ C * Real.log (m : ℝ) := by
  sorry

-- TODO(paper-gap): In (B.6.1.16) a pure norm twist can have a pole in Ω.
-- Restrict the logarithm to heights above the pole. After (B.6.1.19) the
-- summand must retain the power m in N(p)^(m * (1 + αη(T))).
-- TODO(paper-gap): Substituting the radii from (B.6.1.18) into the first
-- coefficient in (B.6.1.20) gives 4(1 + 3α) / ((1 - α)^2 η(T)).

/-- Paper: Corollary B.6.1.5, p. 639. On the line `Re(s) = 1`, the logarithmic
derivative is bounded by a squared logarithm as the absolute height grows.
Deviation: The logarithm uses absolute height. Eventual analyticity and
nonvanishing make the logarithmic derivative well-defined. -/
theorem finiteHeckeL_logDeriv_isBigO_oneLine (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    (∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1, t⟩ ∧ L ⟨1, t⟩ ≠ 0) ∧
      (fun t : ℝ ↦ logDeriv L ⟨1, t⟩) =O[atAbsTop] (fun t ↦ (Real.log |t|) ^ 2) := by
  sorry

/-- Paper: Theorem B.6.1.6, p. 640. The reciprocal of the finite Hecke
L-function grows at most polynomially on `Re(s) = 1` at large absolute heights.
Deviation: Eventual analyticity and nonvanishing make the reciprocal well-defined. -/
theorem finiteHeckeL_inv_isBigO_oneLine (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    (∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1, t⟩ ∧ L ⟨1, t⟩ ≠ 0) ∧
      ∃ N : ℕ, 0 < N ∧ (fun t : ℝ ↦ (L ⟨1, t⟩)⁻¹) =O[atAbsTop] (fun t ↦ |t| ^ N) := by
  sorry

-- TODO(paper-gap): Equation (B.6.1.23) uses the finite L-factors. Its χ²
-- argument has height 2t, which (B.6.1.28) must retain.
-- TODO(paper-gap): The upper bound in (B.6.1.28) uses the critical-strip exponent
-- for σ > 1, where that exponent can be negative and the Euler factors need not decay.

section OutsideEulerProduct

variable (χ : U[F]) (L : ℂ → ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
variable (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)

-- TODO(later): needs §6.3 to compare with the S-local quotient in (6.3.1.6).
-- Compare as meromorphic germs, or after normalizing the quotient at removable
-- singularities. The factors agree via sLocalHeckeL_eq_partialEulerProduct on
-- descended characters. The finite-factor expression already occurs in §3.4.
local notation "Loutside" => (fun s : ℂ ↦ (∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹) * L s)

include hL hSeries

/-- Paper: Theorem B.6.1.7, p. 641. Each sufficiently high open unit interval
contains a height at which the Euler product outside `S` has a polynomial
lower bound on the whole horizontal segment from real part `-1` to `2`.
Deviation: The finite set records only finite places. All archimedean factors
have already been removed from `L`. -/
theorem finiteHeckeL_outside_exists_horizontal_lower_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ T : ℝ in atTop, ∃ t ∈ Ioo T (T + 1),
      ∀ σ ∈ Icc (-1 : ℝ) 2, |t| ^ (-A) < ‖Loutside ⟨σ, t⟩‖ := by
  sorry

/-- Paper: Theorem B.6.1.7, p. 641. The polynomial lower bound holds on a
closed unit interval outside a measurable set of length `1 / B`, with the
large-height threshold independent of `B > 1`.
Deviation: The finite set records only finite places. All archimedean factors
have already been removed from `L`. -/
theorem finiteHeckeL_outside_horizontal_lower_bound_off_small_set :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ T : ℝ in atTop, ∀ B : ℝ, 1 < B →
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc T (T + 1) ∧
        volume E = ENNReal.ofReal (1 / B) ∧
        ∀ t ∈ Icc T (T + 1) \ E, ∀ σ ∈ Icc (-1 : ℝ) 2,
          T ^ (-(A * B)) < ‖Loutside ⟨σ, t⟩‖ := by
  sorry

-- TODO(paper-gap): The exponent in (B.6.1.38) must account for the left edge
-- of the strip. The basepoint for the integration in (B.6.1.43) is log Loutside(2 + it).

-- TODO(paper-gap): Footnote 29 asks for details in the proof of Corollary B.6.1.8
-- that pass from horizontal lower bounds to bounds for reciprocal derivatives.
-- At the selected heights use Cauchy's estimates on a wider fixed strip for
-- derivatives of Loutside, then differentiate Loutside * (1 / Loutside) = 1.

/-- Paper: Corollary B.6.1.8, p. 643. For each derivative order there is a
nondecreasing sequence of heights tending to infinity in absolute value and
growing at most linearly in the index. The derivative of the reciprocal Euler
product is bounded by a fixed power of the height on every selected segment.
Deviation: The finite set records only finite places. All archimedean factors
have already been removed from `L`. The supremum is expressed pointwise, and
analyticity ensures the iterated derivatives are defined on the segments. The
unit intervals of Theorem B.6.1.7, reflected for the conjugate character on the
negative tail, give heights within one of the index for the application of §B.3. -/
theorem finiteHeckeL_outside_inv_iteratedDeriv_horizontal_bound (m : ℕ) :
    let l := comap (abs : ℤ → ℤ) atTop
    ∃ (A β : ℝ) (T : ℤ → ℝ), 0 < A ∧ 0 < β ∧ Monotone T ∧
      Tendsto (abs ∘ T) l atTop ∧ (T =O[l] fun k ↦ |(k : ℝ)|) ∧
      (∀ᶠ k : ℤ in l, |T k - (k : ℝ)| ≤ 1) ∧
      ∀ k : ℤ, ∀ σ ∈ Icc (-1 : ℝ) 2,
        AnalyticAt ℂ (fun s ↦ (Loutside s)⁻¹) ⟨σ, T k⟩ ∧
          ‖iteratedDeriv m (fun s ↦ (Loutside s)⁻¹) ⟨σ, T k⟩‖ ≤ A * |T k| ^ β := by
  sorry

end OutsideEulerProduct

end RiemannMasullo
