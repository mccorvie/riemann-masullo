module

public import RiemannMasullo.Ch03_IdelicZeta.Sec2

/-! # Chapter 3.2: printed residues and absolute convergence -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])

local instance printedCh03Sec2ResiduesIdeleMeasurableSpace
    (F : Type) [Field F] [NumberField F] : MeasurableSpace 𝕀[F] := borel _

local instance printedCh03Sec2ResiduesClassMeasurableSpace
    (F : Type) [Field F] [NumberField F] : MeasurableSpace C[F] := borel _

/-- Paper: Proposition 3.2.1.3(2), p. 123. As printed: for every number field and
every character χ trivial on the norm-one classes, write χ = |·|^(-it).
The residues of the Hecke L-function at it and 1 + it are minus the norm-one
class volume and that volume divided by the square root of the absolute norm
of the different, respectively. This is the residue clause of
`completedHeckeL_continuation_simplePoles`. See ERRATA F209. -/
def Printed.completedHeckeL_residues : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C[F]),
    χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 →
    ∀ (L : ℂ → ℂ), MeromorphicNFOn L univ →
      (∀ s : Complex.re ⁻¹' Ioi (1 : ℝ), L s = completedHeckeL χ s) →
      ∀ (t : ℝ),
        ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : PontryaginDual C[F])
          (-Complex.I * (t : ℂ)) →
        let z := Complex.I * (t : ℂ)
        let m : ℝ := (normOneIdeleClassTamagawaMeasure F univ).toReal
        let d : ℝ := (differentIdeal ℤ (𝓞 F)).absNorm
        Tendsto (fun s : ℂ ↦ (s - z) * L s) (𝓝[≠] z) (𝓝 (-(m : ℂ))) ∧
          Tendsto (fun s : ℂ ↦ (s - (1 + z)) * L s) (𝓝[≠] (1 + z))
            (𝓝 ((d ^ (-(1 / 2) : ℝ) * m : ℝ) : ℂ))

/-- Paper: Proposition 3.2.1.3(2), p. 123. Take F = ℚ(√5), χ = 1, t = 0 and
φ = (1 + √5)/2. The norm-one class volume is 2 log φ/√5. For the product
π^(-s) Γ(s/2)² ζ_F(s), the class number formulas give residues −2 log φ at 0
and 2 log φ/√5 at 1. The printed values are −2 log φ/√5 and 2 log φ/5. -/
theorem Printed.completedHeckeL_residues_false :
    ¬ Printed.completedHeckeL_residues := by sorry

/-- Paper: Theorem 3.2.2.1(2)(b), p. 125. As printed: for every number field
and every adelic Schwartz–Bruhat function, the theta Mellin integral (3.2.2.3)
converges absolutely at every quasi-character on a nontrivial norm-one
component. This is the pointwise absolute convergence clause. See
`globalIdelicZFunction_entire_of_nontrivial` and ERRATA F210. -/
def Printed.globalThetaMellinIntegral_integrable_of_nontrivial : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (f : ℬ[F]) (χ : PontryaginDual C[F]),
    χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 →
    ∀ s : ℂ, Integrable (fun g : C[F] ↦ adelicTheta f g * ideleClassNormTwist χ s g)
      (ideleClassTamagawaMeasure F)

/-- Paper: Theorem 3.2.2.1(2)(b), p. 125. Take F = ℚ, the standard Gaussian
at infinity, the indicator of ℤ̂ at the finite places, and χ induced by the
quadratic Dirichlet character of conductor 5. At s = 0 the character has modulus
one and takes the value −1 at the norm-one idele with component 2 at 5 and 1
elsewhere. At norm t, the theta sum is
Σ_{n ≠ 0} exp(−πn²t²) ∼ 1/t as t tends to zero, so its integral against dt/t diverges. -/
theorem Printed.globalThetaMellinIntegral_integrable_of_nontrivial_false :
    ¬ Printed.globalThetaMellinIntegral_integrable_of_nontrivial := by sorry

/-- Paper: Remark 3.2.2.2, p. 125. As printed: the domain of each truncated
idele integral with norm in [1/n, n] is compact. This is the compactness
assertion used to justify holomorphy. See `globalIdelicZetaIntegral_normBand_entire`
and ERRATA F210. -/
def Printed.ideleNormBand_isCompact : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 1 ≤ n →
    IsCompact (ideleNormBand F (n : ℝ)⁻¹ (n : ℝ))

/-- Paper: Remark 3.2.2.2, p. 125. For F = ℚ and n = 2, the norm band
contains the closed discrete subgroup of principal ideles, isomorphic to ℚˣ.
This subgroup is infinite and hence cannot be a closed subset of a compact band. -/
theorem Printed.ideleNormBand_isCompact_false :
    ¬ Printed.ideleNormBand_isCompact := by sorry

end RiemannMasullo
