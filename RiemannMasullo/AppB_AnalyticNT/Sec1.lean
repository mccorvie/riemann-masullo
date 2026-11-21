module

public import RiemannMasullo.Ch03_IdelicZeta.Sec2
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Convexity bounds for finite Hecke L-functions

Masullo, §B.1, pp. 588–591. The estimates concern both directions on vertical
lines and are uniform in the real part when stated on a strip.
-/

@[expose] public noncomputable section

open Filter Function NumberField Set
open scoped Asymptotics ENNReal NNReal

namespace RiemannMasullo

local notation "atHeight" => comap (abs ∘ Complex.im) atTop

-- TODO(paper-gap): If the introductory critical-line estimate refers to the
-- finite L-function, its exponent 1/4 + ε omits the degree in (B.1.1.12).

/-- Paper: Equation (B.1.1.2), p. 589. The vertical growth order is the infimum
of the nonnegative exponents that bound the function along `Re(s) = σ`.
Deviation: The infimum takes values in `ℝ≥0∞`, with `⊤` when no polynomial bound exists. -/
def verticalGrowthOrder (f : ℂ → ℂ) (σ : ℝ) : ℝ≥0∞ :=
  sInf ((fun k : ℝ≥0 ↦ (k : ℝ≥0∞)) ''
    {k : ℝ≥0 | f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ (k : ℝ)})

/-- Paper: Equation (B.1.1.2), p. 589. As a check on the definition, the identity
function has growth order one on every vertical line. -/
theorem verticalGrowthOrder_id (σ : ℝ) : verticalGrowthOrder (id : ℂ → ℂ) σ = 1 := by sorry

section GrowthOrder

variable {f : ℂ → ℂ} {a : ℝ}
variable (hf : MeromorphicNFOn f (Complex.re ⁻¹' Ioi a))
  (hFinite : {s : ℂ | a < s.re ∧ meromorphicOrderAt f s < 0}.Finite)
  (hSimple : ∀ s : ℂ, a < s.re → meromorphicOrderAt f s < 0 → meromorphicOrderAt f s = -1)
  (hGrowth : ∃ ξ : ℝ, 0 < ξ ∧
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioi a)] fun s ↦ |s.im| ^ ξ)

include hf hFinite hSimple hGrowth

/-- Paper: Lemma B.1.1.1, p. 589. In the open half-plane the vertical growth
order is finite under the uniform polynomial bound.
Deviation: This and the other parts use meromorphic functions in normal form
and omit the unused parameter `b > a`. -/
theorem verticalGrowthOrder_ne_top {σ : ℝ} (hσ : a < σ) :
    verticalGrowthOrder f σ ≠ ⊤ := by sorry

-- TODO(paper-gap): The proof's equality `μ_g = μ + N` fails for `f(s) = 1/s`
-- on `Re(s) > -1`. Clearing its one pole gives `g(s) = 1`, and both orders are zero.

/-- Paper: Lemma B.1.1.1, p. 589. The finite growth order is convex as a function
of the real part in the open half-plane. -/
theorem convexOn_verticalGrowthOrder :
    ConvexOn ℝ (Ioi a) (fun σ ↦ (verticalGrowthOrder f σ).toReal) := by sorry

/-- Paper: Lemma B.1.1.1, p. 589. The finite growth order is continuous in the
open half-plane. -/
theorem continuousOn_verticalGrowthOrder :
    ContinuousOn (fun σ ↦ (verticalGrowthOrder f σ).toReal) (Ioi a) := by sorry

/-- Paper: Lemma B.1.1.1, p. 589. On each closed strip inside the half-plane,
the growth order at the real part plus any positive ε gives a uniform exponent. -/
theorem isBigO_verticalGrowthOrder_add (σ₁ σ₂ : ℝ) (h₁ : a < σ₁) (h₂ : σ₁ < σ₂)
    (ε : ℝ) (hε : 0 < ε) :
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc σ₁ σ₂)]
      fun s ↦ |s.im| ^ ((verticalGrowthOrder f s.re).toReal + ε) := by sorry

end GrowthOrder

section Hecke

variable {F : Type*} [Field F] [NumberField F]

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

-- TODO(paper-gap): In Lemma B.1.1.2 the exponent must be allowed to depend on
-- the strip. For ζ on each line σ < 0 the growth order is 1/2 - σ.

/-- Paper: Lemma B.1.1.2, p. 590. The finite L-function of a unitary Hecke
character grows at most polynomially on each fixed closed vertical strip.
Deviation: `M` is chosen after the strip endpoints, as required even for ζ. -/
theorem finiteHeckeL_continuation_isBigO_rpow (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (a b : ℝ) (hab : a < b) :
    ∃ M : ℝ, 0 < M ∧ L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun s ↦ |s.im| ^ M := by
  sorry

/-- Paper: Equation (B.1.1.10), p. 590. The reflection factor in the functional
equation satisfies the stated power bound on every fixed closed vertical strip. -/
theorem finiteHeckeReflectionFactor_isBigO_on_strip (χ : U[F]) (L Ldual ε : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hDualSeries : ∀ s : halfPlane, Ldual s = finiteHeckeL χ⁻¹ s)
    (hε : Differentiable ℂ ε) (hεNe : ∀ s, ε s ≠ 0)
    (hEq : L =ᶠ[codiscreteWithin univ]
      (fun s ↦ finiteHeckeReflectionFactor χ ε s * Ldual (1 - s)))
    (a b : ℝ) (hab : a < b) :
    finiteHeckeReflectionFactor χ ε =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)]
      fun s ↦ |s.im| ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) := by sorry

-- TODO(paper-gap): After (B.1.1.11), the displayed multiplier is called entire
-- and zero-free. For F = ℚ and χ trivial, its gamma quotient has a pole at 1
-- and a zero at 0. The explicit conductor normalization also needs an ideal conductor API.

/-- Paper: Proposition B.1.1.3, p. 591. On the closed critical strip the
convexity bound has a common constant for all positive ε and all real parts.
The height from which the estimate holds may depend on ε. -/
theorem finiteHeckeL_continuation_convexity_bound (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε > (0 : ℝ),
      Asymptotics.IsBigOWith C (atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc (0 : ℝ) 1)) L
        (fun s ↦ |s.im| ^ ((Module.finrank ℚ F : ℝ) * ((1 - s.re) / 2) + ε)) := by sorry

-- TODO(paper-gap): Footnote 2 asks for a bound on [-1, 2] without specifying
-- an exponent there. The exponent in (B.1.1.12) fails at σ = -1 even for ζ.
-- TODO(paper-gap): The bound on the dual L-factor gives an upper bound by
-- the reflection factor on fixed left-hand lines. The printed asymptotic
-- equivalence would require the dual L-factor to tend to one in absolute value.
-- TODO(paper-gap): In (B.1.1.14), the bounds on μ at 0 and 1 give an inequality
-- for the interpolation term. The printed equality needs a separate argument.

/-- Paper: Remark B.1.1.4, p. 591. On each fixed vertical line the continued
finite L-function is eventually holomorphic, and each of its holomorphic
derivatives grows at most polynomially as the absolute height tends to infinity. -/
theorem finiteHeckeL_continuation_iteratedDeriv_isBigO_rpow (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (k : ℕ) (σ : ℝ) :
    ∃ M C : ℝ, 0 < M ∧ 0 < C ∧
      ∀ᶠ s in atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ}),
        AnalyticAt ℂ L s ∧ ‖iteratedDeriv k L s‖ ≤ C * |s.im| ^ M := by sorry

-- TODO(paper-gap): Footnotes 3 and 4 leave the intended uniform derivative
-- bounds on strips open. Proposition 3.3.1.5 is stated on fixed lines with σ > 0.

end Hecke

end RiemannMasullo
