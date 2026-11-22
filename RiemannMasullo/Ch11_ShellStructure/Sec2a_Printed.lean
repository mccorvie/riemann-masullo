module

public import RiemannMasullo.Ch11_ShellStructure.Sec2a
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a
import all RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # §11.2.0 assertions that are false as printed -/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "restriction(" F ")" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
local notation "μ(" F ")" => ideleClassTamagawaMeasure F
local notation "logNorm(" F ")" =>
  (fun g : C𝔽(F) ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "μ'(" F ", " s ")" => (μ(F)).withDensity (fun g ↦
  ENNReal.ofReal (intervalSobolevDensity 0 0 (s) (logNorm(F) g))⁻¹)
local notation "W(" F ", " s ")" => CompactIntervalSobolev (μ(F)) logNorm(F) 0 0 s
local notation "W'(" F ", " s ")" => CompactIntervalSobolev (μ(F)) logNorm(F) 0 0 s true
local notation "hI" => (le_rfl (a := (0 : ℝ)))
local notation "H(" F ", " hs ")" => globalThetaSobolev F 0 hI hs
local notation "ρ(" F ", " hs ")" =>
  hardySobolevTranslation (μ(F))
    (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽(F) →ₜ* ℝ≥0ˣ) 0 0 _ hI hs
local notation "Wω(" F ", " hs ", " ω ")" =>
  actionIsotype ((ρ(F, hs)).comp (ideleClassNorm F).ker.subtype) ω
local notation "frequency(" t ")" => ((t : ℝ) : ℂ) * Complex.I
local notation "jet(" χ ", " t ", " m ")" => spectralZeroJet χ 0 t m

/-- Paper: Proposition 11.2.0.1(2), pp. 484–485. The range of the extended
principal-value map is asserted to be closed for degree at least twice the set size. -/
def Printed.globalThetaSobolevPrincipalValue_closedRange : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset V(F)) (s : ℝ) (hs : 0 ≤ s),
    2 * (S.card : ℝ) ≤ s →
    IsClosed (range (globalThetaSobolevPrincipalValue F S 0 hs))

/-- Paper: Proposition 11.2.0.1(2), pp. 484–485. Take ℚ, S₀ = {2}, degree 2
and the trivial isotype, identified with the log-line space by zero-line density.
The prime difference is injective there since a nonzero
periodic function cannot be in weighted L². For any nonzero smooth ψ supported
in (1,2), the ratio of the norms of the difference of ψ(x/R) and of ψ(x/R)
tends to zero. The isotype projection commutes with the operator, so its
nonclosed range on this isotype also rules out closed range on the full space. -/
theorem Printed.globalThetaSobolevPrincipalValue_closedRange_false :
    ¬ Printed.globalThetaSobolevPrincipalValue_closedRange := by sorry

/-- Paper: Lead-in to (11.2.0.3), p. 484. At every twist and nonnegative
degree the completed PV map is a closed embedding whose image equals the
completion of its test image. -/
def Printed.globalThetaSobolevPrincipalValue_isClosedEmbedding : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let P := globalThetaSobolevPrincipalValue F S a hs
    let j := globalThetaSobolevInclusion F a hI hs
    Topology.IsClosedEmbedding P ∧ range P =
      closure (range fun f : ↥(adelePolarSubspace F) ↦ P (j (Submodule.Quotient.mk f)))

/-- Paper: Lead-in to (11.2.0.3), p. 484. The case a = 0, s = 2,
F = ℚ and S = {2} already has nonclosed image. -/
theorem Printed.globalThetaSobolevPrincipalValue_isClosedEmbedding_false :
    ¬ Printed.globalThetaSobolevPrincipalValue_isClosedEmbedding := by
  intro h
  apply Printed.globalThetaSobolevPrincipalValue_closedRange_false
  intro F _ _ S s hs _
  exact (h F S 0 s hs).1.isClosed_range

/-- Paper: Theorem 11.2.0.2(1), p. 485. For each represented rational prime p,
the reciprocal product over S equals the product of the local denominators
over the places of S above p. Use the reciprocal factors of §6.3.1. -/
def Printed.orbitalEulerProduct_eq_primary : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F)),
    (∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    ∀ p : HeightOneSpectrum (𝓞 ℚ), (sLocalPrimaryPlaces S p).Nonempty → ∀ z : ℂ,
      reciprocalPartialHeckeEulerProduct χ S z =
        reciprocalPartialHeckeEulerProduct χ (sLocalPrimaryPlaces S p) z

/-- Paper: Theorem 11.2.0.2(1), p. 485. Over ℚ with trivial character,
S = {2,3}, p = 2, and z = 1, the two sides are 1/3 and 1/2. -/
theorem Printed.orbitalEulerProduct_eq_primary_false :
    ¬ Printed.orbitalEulerProduct_eq_primary := by sorry

/-- Paper: Theorem 11.2.0.2 and (11.2.0.6), p. 485. Every jet admitted by
the printed floor cutoff is asserted to lie in the conjugate reciprocal-weight isotype. -/
def Printed.orbitalJet_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F)),
    (∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    ∀ (s : ℝ), 0 ≤ s → ∀ (t : ℝ) (m : ℕ),
      reciprocalPartialHeckeEulerProduct χ S (frequency(t)) = 0 →
      m < min (orbitalEulerMultiplicity χ S (frequency(t))) (Nat.floor ((s - 1) / 2 + 1)) →
      ∃ h : MemLp (jet(χ, t, m)) 2 (μ'(F, s)),
        let u := h.toLp (jet(χ, t, m))
        ∀ k : C₁(F), (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ(F)] fun g ↦ (χ⁻¹ k.val : ℂ) * u g

/-- Paper: Theorem 11.2.0.2 and (11.2.0.6), p. 485. Over ℚ with the trivial
character and S₀ = {2}, the factor 1 − 2⁻ᶻ has a simple zero at 0. At degree
1 the printed floor admits the constant jet. Its squared norm diverges
because the reciprocal weight is asymptotic to 1/|x|. -/
theorem Printed.orbitalJet_memLp_false : ¬ Printed.orbitalJet_memLp := by sorry

/-- Paper: Theorem 11.2.0.2, p. 485. The jet vectors form a Markushevich
basis of the PV annihilator taken in the full negative space with its subspace topology. -/
def Printed.orbitalJets_basis_fullAnnihilator : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F)),
    (∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    ∀ (s : ℝ) (hs : 0 ≤ s), 2 * (S.card : ℝ) ≤ s →
      let ω := χ.comp (restriction(F))
      let J := {j : ℝ × ℕ //
        j.2 < min (orbitalEulerMultiplicity χ S (frequency(j.1)))
          (Nat.floor ((s - 1) / 2 + 1))}
      ∃ A : Submodule ℂ W'(F, s),
        (A : Set W'(F, s)) = {ψ | ∀ f : H(F, hs), (f : W(F, s)) ∈ Wω(F, hs, ω) →
          spectralSobolevPairing ((globalThetaSobolevPrincipalValue F S 0 hs f).val) ψ = 0} ∧
        ∃ (u : J → A) (Λ : J → StrongDual ℂ A),
          (∀ j, ((u j).val : C𝔽(F) → ℂ) =ᵐ[μ(F)] jet(χ, j.val.1, j.val.2)) ∧
          IsSpectralMarkushevichBasis u Λ

/-- Paper: Theorem 11.2.0.2, p. 485. Over ℚ take the trivial character,
S₀ = {2}, and degree 2. Every jet is constant on the compact norm-one factor
Ẑ×. The nontrivial quadratic character modulo 3 on that factor defines a
nonzero negative-space vector annihilating the whole trivial isotype. It lies
outside its closed trivial isotype and hence outside the closed jet span. -/
theorem Printed.orbitalJets_basis_fullAnnihilator_false :
    ¬ Printed.orbitalJets_basis_fullAnnihilator := by sorry

/-- Paper: Remark 11.2.0.3, p. 485. The dual of the quotient by the entire
isotypic theta space is identified by the pairing with the PV annihilator
in the ambient negative space, with its subspace topology. -/
def Printed.orbitalQuotientDual_missingPV : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F)),
    (∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) → ∀ (s : ℝ) (hs : 0 ≤ s),
      let ω := χ.comp (restriction(F))
      let Q := spectralSobolevIsotypeQuotient F 0 hI hs ω
      let N := (globalThetaSobolev F 0 hI hs).comap (Wω(F, hs, ω)).subtype
      ∃ D : StrongDual ℂ Q →L[ℂ] W'(F, s), Topology.IsEmbedding D ∧
        range D = {ψ | ∀ f : H(F, hs), (f : W(F, s)) ∈ Wω(F, hs, ω) →
          spectralSobolevPairing (globalThetaSobolevPrincipalValue F S 0 hs f).val ψ = 0} ∧
        ∀ (Λ : StrongDual ℂ Q) (f : Wω(F, hs, ω)), spectralSobolevPairing f.val (D Λ) =
          Λ (N.mkQ f)

/-- Paper: Remark 11.2.0.3, p. 485. Take ℚ, S₀ = {2}, degree 2, and the
trivial isotype. Integration is nonzero and continuous on that positive
isotype and kills the prime difference. The quotient by the full theta
completion is zero by 0-line density. -/
theorem Printed.orbitalQuotientDual_missingPV_false :
    ¬ Printed.orbitalQuotientDual_missingPV := by sorry

/-- Paper: (11.2.0.8), p. 486. Every full-order jet must have a representative
in the specified subset of the printed negative Sobolev isotype. -/
def Printed.orbitalJetsIn {F : Type} [Field F] [NumberField F]
    (χ : PontryaginDual C𝔽(F)) (S : Finset V(F)) (s : ℝ) (B : Set W'(F, s)) : Prop :=
  ∀ (t : ℝ) (m : ℕ), reciprocalPartialHeckeEulerProduct χ S (frequency(t)) = 0 →
    m < orbitalEulerMultiplicity χ S (frequency(t)) →
    ∃ h : MemLp (jet(χ, t, m)) 2 (μ'(F, s)),
      let u := h.toLp (jet(χ, t, m))
      (∀ k : C₁(F), (fun g ↦ u (k.val⁻¹ * g)) =ᵐ[μ(F)] fun g ↦ (χ k.val : ℂ) * u g) ∧
      u ∈ B

/-- Paper: Proposition 11.2.0.4 and (11.2.0.9), p. 486. The full-multiplicity
family belongs to the annulus in the printed positive-character isotype. -/
def Printed.orbitalJet_norm_annulus : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F)),
    (∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    ∀ (s : ℝ), 1 < s → ∃ C : ℝ, 0 < C ∧
      Printed.orbitalJetsIn χ S s {u | C⁻¹ ≤ ‖u‖ ∧ ‖u‖ ≤ C}

/-- Paper: Proposition 11.2.0.4, p. 486. In ℚ(i), take the two places over 5
and the trivial character. The product (1 − 5⁻ᶻ)² has a double zero at 0.
For degree 3 the permitted jet of order 1 has squared integrand asymptotic
to 1/|x| in the log-norm coordinate, so it has no finite norm. -/
theorem Printed.orbitalJet_norm_annulus_false : ¬ Printed.orbitalJet_norm_annulus := by sorry

/-- Paper: Proposition 11.2.0.4, p. 486. The printed family lies in the annulus
and has an element outside the open ball in the same isotype, with the same C. -/
def Printed.orbitalJets_not_subset_ball : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F)),
    (∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    ∀ (s : ℝ), 1 < s → ∃ C : ℝ, 0 < C ∧
      Printed.orbitalJetsIn χ S s {u | C⁻¹ ≤ ‖u‖ ∧ ‖u‖ ≤ C} ∧
      ¬ Printed.orbitalJetsIn χ S s {u | ‖u‖ < C⁻¹}

/-- Paper: Proposition 11.2.0.4, p. 486. Take ℚ, the trivial character,
S₀ empty, and degree 2. The Euler product is one so the jet set is empty
and is contained in every open ball. -/
theorem Printed.orbitalJets_not_subset_ball_false :
    ¬ Printed.orbitalJets_not_subset_ball := by sorry

end RiemannMasullo
