module

public import RiemannMasullo.Ch11_ShellStructure.Sec1a

/-!
# Printed convergence criteria in §11.1.1

The repaired statements are in Sec1a.lean.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField.AdeleRing nonZeroDivisors

namespace RiemannMasullo

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "N[" F "]" => MonoidHom.ker (ideleNorm F)
local notation "C₁[" F "]" => MonoidHom.ker (ideleClassNorm F)
local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "Frac[" F "]" => FractionalIdeal (𝓞 F)⁰ F
local notation "principal[" F "]" => IdeleGroup.unitEmbedding (𝓞 F) F
local notation "ideleValue[" F "]" => fun (φ : ℬ[F]) (g : 𝕀[F]) ↦ φ (Multiplicative.ofAdd (Units.val g))
local notation "classOf[" F "]" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)

local instance instIdeleMeasurableSpaceSec1aPrinted (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace 𝕀[F] := borel _

-- TODO(paper-gap): Proposition 11.1.1.2, p. 476, defines f and the finite
-- value J_F(α) on Z, then evaluates both on its saturation. It does not
-- specify an arbitrary extension of f. Extending J by its ideal-series
-- formula forces all f_k to vanish on the saturation (test at 2^n g).
-- The zero sequence with a nonzero extension of f refutes the arbitrary-
-- extension interpretation only. Sec1a states the criterion on the repaired domains.

/-- Paper: Corollary 11.1.1.4, p. 478. As printed, each absolute orbit sum
has a bound depending on the orbit alone, from which the paper claims
pointwise convergence on the idele class group.
Deviation: The orbit majorant is indexed by ξ, with ξ representing ξg.
The repeated g in (2)(b) refers to the representative with these witnesses,
as in the sentence immediately following (11.1.1.10). -/
def Printed.cond_adelicTheta_pointwiseConvergence : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (e : (ℝ≥0ˣ × N[F]) ≃ₜ* 𝕀[F])
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (rep : CommRing.Pic (𝓞 F) → N[F]) (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ),
    let E₁ := ideleFundamentalDomain F b v₀ σ rep
    let Z := e '' ((Set.univ : Set ℝ≥0ˣ) ×ˢ E₁)
    (∀ t h, ideleNorm F (e (t, h)) = t) →
    (∀ h, e (1, h) = h.val) →
    rep 1 = 1 → (∀ c, ideleIdealClass F (rep c).val = c) →
    (∀ g, Tendsto (fun k ↦ ideleValue[F] (φ k) g) atTop (𝓝 (f g))) →
    (∀ g : 𝕀[F], ∃ (α : Fˣ → ℝ≥0) (I : Frac[F]),
      Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦ (α ξ.val : ℝ)) ∧
      (g ∈ Z → ∀ (_ξ : Fˣ) k, (∑' ξ : Fˣ, ‖ideleValue[F] (φ k) (principal[F] ξ * g)‖) ≤
        ∑' ξ : {ξ : Fˣ // (ξ.val : F) ∈ I}, (α ξ.val : ℝ))) →
    (∀ g ∈ Z, Summable (fun ξ : Fˣ ↦ ‖f (principal[F] ξ * g)‖)) ∧
    ∃ Θ : C[F] → ℂ, (∀ g, Θ (classOf[F] g) = ideleThetaSum f g) ∧
      ∀ c, Tendsto (fun k ↦ adelicTheta (φ k) c) atTop (𝓝 (Θ c))

/-- Paper: Corollary 11.1.1.4, p. 478. Over ℚ let the archimedean factor be
B(x − (k + 1)), for a nonnegative smooth bump bounded by 1, supported in
(−1/4, 1/4), with B(0) = 1. The finite factor is the indicator of the
finite integral adeles. These functions tend pointwise to zero. On the standard
section times the domain, the finite factor restricts the sum to nonzero
integers and the archimedean coordinates are spaced by the norm t > 0.
Use the unit ideal and the orbit majorant supported at index 1 with value
2 + 1/t. The theta series at the identity is 1 for every k. -/
theorem Printed.cond_adelicTheta_pointwiseConvergence_false :
    ¬ Printed.cond_adelicTheta_pointwiseConvergence := by sorry

/-- Paper: Corollary 11.1.1.5, p. 479. As printed, a slice-integrable
majorant on the total absolute orbit sums is assumed to imply pointwise
convergence of the homogeneous theta averages.
The approximants use the Schwartz–Bruhat operator from Definition 2.2.5.1.
Deviation: In the new limit integral the character is extended trivially on
the norm section. Slice integrability is written by pullback to the domain. -/
def Printed.cond_homogeneousTheta_pointwiseConvergence : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (e : (ℝ≥0ˣ × N[F]) ≃ₜ* 𝕀[F])
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (rep : CommRing.Pic (𝓞 F) → N[F]) (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ),
    let E₁ := ideleFundamentalDomain F b v₀ σ rep
    let Z := e '' ((Set.univ : Set ℝ≥0ˣ) ×ˢ E₁)
    let μ₁ := (normOneIdeleTamagawaMeasure F).restrict E₁
    (∀ t h, ideleNorm F (e (t, h)) = t) →
    (∀ h, e (1, h) = h.val) →
    rep 1 = 1 → (∀ c, ideleIdealClass F (rep c).val = c) →
    (∀ g, Tendsto (fun k ↦ ideleValue[F] (φ k) g) atTop (𝓝 (f g))) →
    (∃ (α : 𝕀[F] → ℝ≥0) (I : Frac[F]),
      Measurable α ∧
      (∀ g, Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦
        (α (principal[F] ξ.val * g) : ℝ))) ∧
      Measurable (fractionalIdealOrbitSum I α) ∧
      (∀ t, Integrable (fun h : N[F] ↦ fractionalIdealOrbitSum I α (e (t, h))) μ₁) ∧
      ∀ g ∈ Z, ∀ k,
        (∑' ξ : Fˣ, ‖ideleValue[F] (φ k) (principal[F] ξ * g)‖) ≤ fractionalIdealOrbitSum I α g) →
    ∀ ω : PontryaginDual C₁[F],
      (∀ g : 𝕀[F], Integrable (fun h : N[F] ↦
        let h₀ := (e.symm (g * h.val)).2
        ideleThetaSum f (g * h.val) * (ω ⟨classOf[F] h₀.val, h₀.property⟩ : ℂ)) μ₁) ∧
      ∃ (A : C[F] ⧸ C₁[F] → ℂ) (Aₖ : ℕ → C[F] ⧸ C₁[F] → ℂ),
        (∀ g, A (QuotientGroup.mk' _ (classOf[F] g)) =
          homogeneousThetaSectionAverage e v₀ σ b rep ω f g) ∧
        (∀ k g, Aₖ k (QuotientGroup.mk' _ (classOf[F] g)) =
          homogeneousAdelicTheta ω (φ k) (classOf[F] g)) ∧
        ∀ q, Tendsto (fun k ↦ Aₖ k q) atTop (𝓝 (A q))

/-- Paper: Corollary 11.1.1.5, p. 479. Use the rational bumps from the
counterexample to Corollary 11.1.1.4 and the trivial character. Take the
unit ideal and set α(g) to 2 + 1/|g|_F on the section times the domain,
and zero elsewhere. Each orbit has one representative there, so the
majorant sum has at most one nonzero term and is Borel. It is constant on
each slice of the domain. On the norm-one slice the theta sums are
identically 1, giving averages equal to the positive Haar mass of the
domain, while the average of the zero limit vanishes. -/
theorem Printed.cond_homogeneousTheta_pointwiseConvergence_false :
    ¬ Printed.cond_homogeneousTheta_pointwiseConvergence := by sorry

end RiemannMasullo
