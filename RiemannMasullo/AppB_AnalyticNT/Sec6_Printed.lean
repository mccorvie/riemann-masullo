module

public import RiemannMasullo.AppB_AnalyticNT.Sec6

/-!
# Appendix B.6: statements that are false as printed

The printed claims are kept as propositions with separate refutation statements.
Nothing imports this file.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped Topology

namespace RiemannMasullo

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- Paper: Proposition B.6.1.1, real-zero clause, p. 636. As printed: for every
number field and continuous character, any zero of its finite Hecke L-function at
a real point in `[1/2, 1]` forces the square of the character to be trivial.
Positive meromorphic order expresses a genuine zero. The repaired
`finiteHeckeL_zeroFreeRegion` omits the real-zero clause. See ERRATA F23. -/
def Printed.finiteHeckeL_quadratic_of_real_zero : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]) (L : ℂ → ℂ),
    MeromorphicNFOn L univ → (∀ s : halfPlane, L s = finiteHeckeL χ s) →
      ∀ σ ∈ Icc (1 / 2 : ℝ) 1, 0 < meromorphicOrderAt L (σ : ℂ) → χ ^ 2 = 1

/-- Paper: Proposition B.6.1.1, real-zero clause, p. 636. Choose a nonreal critical-line
zero `1/2 + iγ` of the Riemann zeta function by Hardy's theorem. Over the rational
field, the unitary character `χ = |·|^(iγ)` has finite L-function `ζ(s + iγ)` on `Re s > 1`.
Take its meromorphic normal form on the plane, setting the value at `1 - iγ` to zero.
At `σ = 1/2` it has positive order. The idelic norm is onto the positive reals, so `γ ≠ 0`
implies `χ ^ 2 ≠ 1`. -/
theorem Printed.finiteHeckeL_quadratic_of_real_zero_false :
    ¬ Printed.finiteHeckeL_quadratic_of_real_zero := by
  sorry

/-- Paper: Paragraph following Proposition B.6.1.1, p. 636. As printed: for every
number field and every continuous character whose square is nontrivial, the finite Hecke
L-function of its square is entire. The note after `finiteHeckeL_zeroFreeRegion`
records the shifted pole. See ERRATA F24. -/
def Printed.finiteHeckeL_sq_entire_of_not_quadratic : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]) (L : ℂ → ℂ),
    χ ^ 2 ≠ 1 → MeromorphicNFOn L univ →
      (∀ s : halfPlane, L s = finiteHeckeL (χ ^ 2) s) → Differentiable ℂ L

/-- Paper: Paragraph following Proposition B.6.1.1, p. 636. Over the rational
field take `χ = |·|^i`. Its square is nontrivial because the idelic norm is
onto. The finite L-function of its square equals `ζ(s + 2i)` on `Re s > 1`.
Use the meromorphic normal form on the plane, setting the value at `1 - 2i` to zero.
The germ there still has a simple pole, so this continuation is not entire. -/
theorem Printed.finiteHeckeL_sq_entire_of_not_quadratic_false :
    ¬ Printed.finiteHeckeL_sq_entire_of_not_quadratic := by
  sorry

/-- Paper: Lemma B.6.1.2(1), p. 637. As printed: for every number field and
continuous character trivial on the norm-one classes, after undoing its imaginary
norm twist the ideal summatory function divided by its argument tends to the
norm-one Tamagawa volume times the inverse square root of the norm of the different.
This is the asymptotic in (B.6.1.7), for the character's norm parameter.
The repaired `heckeIdealSummatory_tendsto_of_trivial_on_normOne` uses the
Dedekind zeta residue, equal to the volume alone. See ERRATA F25. -/
def Printed.heckeIdealSummatory_tendsto_of_trivial_on_normOne : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]),
    χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 →
      ∀ t₀ : ℝ,
        ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀) →
          let d : ℝ := (differentIdeal ℤ (𝓞 F)).absNorm
          let μ := normOneIdeleClassTamagawaMeasure F
          Tendsto (fun x : ℝ ↦ heckeIdealSummatory (ideleClassNormTwist χ (Complex.I * t₀)) x / x)
            atTop (𝓝 (((Real.sqrt d)⁻¹ * μ.real univ : ℝ) : ℂ))

/-- Paper: Lemma B.6.1.2(1), p. 637. Take `F = ℚ(√5)`, `χ = 1`, and
`t₀ = 0`. With `φ = (1 + √5) / 2`, the ideal-counting limit is the zeta
residue `2 log φ / √5`, equal to the norm-one volume by (A.3.2.1). The
norm of the different is five, so the display instead gives `2 log φ / 5`. -/
theorem Printed.heckeIdealSummatory_tendsto_of_trivial_on_normOne_false :
    ¬ Printed.heckeIdealSummatory_tendsto_of_trivial_on_normOne := by
  sorry

end RiemannMasullo
