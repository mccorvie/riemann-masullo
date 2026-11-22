module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
import all RiemannMasullo.Ch10_TraceSpectral.Sec1

/-!
# Printed cutoff and spectral lift claims in §§10.4.1–10.4.2

The corresponding truncation and lift declarations are in `Sec4a.lean`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped Classical NNReal Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "m[" F "]" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C[F] →ₜ* ℝ≥0ˣ)
local notation "μ[" F "]" => ideleClassTamagawaMeasure F
local notation "logNorm[" F "]" => fun g : C[F] ↦ Real.log ((ideleClassNorm F g).val : ℝ)

/-- Paper: §10.4, introduction, p. 455. As printed: on the symmetric
interval Sobolev space, multiplication by a smooth cutoff has closed range.
The multiplier used in `spectralTruncation` is bounded (ERRATA F186). -/
def Printed.smoothCutoffMultiplier_isClosedRange : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (α s : ℝ), 0 ≤ α → 1 < s →
    ∀ (Λ ε : ℝ) (ρ : C[F] → ℝ) (hρ : IsSmoothModulatedCutoff m[F] Λ ε ρ),
      let ν := (μ[F]).withDensity (fun g ↦
        ENNReal.ofReal (intervalSobolevDensity (-α) α s (logNorm[F] g)))
      IsClosed (range (modulatedCutoffOperator m[F] ν hρ.1))

/-- Paper: §10.4, introduction, p. 455. Use `F = ℚ`, `α = 0`, `s = 2`,
`Λ = 2` and `ε = 1/4`. In log norm choose an even smooth cutoff equal to
one on `|x| ≤ log(7/4)`, strictly tapering on `log(7/4) < |x| < log 2`,
and zero on `|x| ≥ log 2`. The normalized indicators of `0 < ρ < 1/n`
are unit vectors perpendicular to the kernel and their images have norm at
most `1/n`, contradicting the lower bound for an operator with closed range. -/
theorem Printed.smoothCutoffMultiplier_isClosedRange_false :
    ¬ Printed.smoothCutoffMultiplier_isClosedRange := by sorry

/-- Paper: Remark 10.4.2.3, p. 460. As printed: at each admissible radius
the cutoff is continuous on the idele class group. This is the continuity
clause following (10.4.2.10). The cutoff hypotheses of
`spectralTruncatedConvolution_trace_tendsto` allow piecewise smooth profiles (ERRATA F188). -/
def Printed.spectralCutoffFamily_continuous : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ε : ℝ → ℝ) (ρ : ℝ → C[F] → ℝ),
    Tendsto (fun Λ ↦ ε Λ * Λ) atTop (𝓝 0) →
    let admissible := fun Λ ↦ IsModulatedCutoff m[F] Λ (ε Λ) (ρ Λ) ∧
      0 < Λ⁻¹ + ε Λ ∧ Λ⁻¹ + ε Λ < Λ - ε Λ
    (∀ᶠ Λ in atTop, admissible Λ) → ∀ Λ, admissible Λ → Continuous (ρ Λ)

/-- Paper: Remark 10.4.2.3, p. 460. Over ℚ take `ε(Λ) = 1/(2Λ²)` and
let `ρ(Λ)` be the indicator of `Λ⁻¹ ≤ |g|_F ≤ Λ`. For `Λ > 2`
these are admissible cutoffs. Each jumps at both endpoints along the
continuous positive-real section of the idelic norm. -/
theorem Printed.spectralCutoffFamily_continuous_false :
    ¬ Printed.spectralCutoffFamily_continuous := by sorry

local notation "W[" F ", " α ", " s "]" =>
  CompactIntervalSobolev μ[F] logNorm[F] (-α) α s
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I

/-- Paper: Theorem 10.4.2.8, proof, (10.4.2.24), p. 463. As printed:
ambient biorthogonal lifts of the strip basis can be chosen with a common
upper bound `C + ε`. The indices and the pullback of the coefficient
functionals use `s + b + it` from (10.4.2.21) and `a + b + it` from
(10.4.2.22), respectively, with the full multiplicity displayed there.
The basis vectors belong to the quotient isotype of the fixed character.
Their coefficients pull back to Haar integration, and their ambient lifts
satisfy the upper half of (10.4.2.24) for each permitted ε.
The lemma `exists_biorthogonalBasisLift` assumes a collar for the quotient
vectors (ERRATA F191). -/
def Printed.spectralStripBasisLift_uniformUpperBound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C[F]) (a α s : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s),
    let hI := (neg_nonpos.mpr hα).trans hα
    let N := globalThetaSobolev F a hI hs
    let Q := spectralSobolevQuotient F a hI hs
    let res : (ideleClassNorm F).ker →ₜ* C[F] :=
      ⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩
    letI := instClosedSpectralIsotypeThetaSec2 (F := F) a hI hs (χ.comp res)
    let B := spectralSobolevIsotypeQuotient F a hI hs (χ.comp res)
    let incl : B →ₗ[ℂ] Q := Submodule.mapQ _ N (Submodule.subtype _) le_rfl
    let J := {j : ℝ × ℝ × ℕ // j.1 ∈ Icc (-α) α ∧ j.2.2 <
      (meromorphicOrderAt (continuedCompletedHeckeL χ) (shift(s + j.1, j.2.1))).untop₀.toNat}
    let η := fun i : J ↦ spectralZeroJet χ (a + i.val.1) i.val.2.1 i.val.2.2
    ∃ (ψ : J → B) (d : J → StrongDual ℂ B) (D : J → StrongDual ℂ Q) (C : ℝ), 0 < C ∧
      IsSpectralMarkushevichBasis ψ d ∧ (∀ i y, d i y = D i (incl y)) ∧
      (∀ (i : J) (v : W[F, α, s]), Integrable (fun g ↦ v g * η i g) μ[F] ∧
        D i (N.mkQ v) = ∫ g, v g * η i g ∂μ[F]) ∧
      ∀ ε : ℝ, 0 < ε → ε < C⁻¹ → ∃ u : J → W[F, α, s],
        ∀ j, N.mkQ (u j) = incl (ψ j) ∧ ‖u j‖ < C + ε

/-- Paper: Theorem 10.4.2.8, proof, (10.4.2.24), p. 463. Use `F = ℚ`,
`χ = 1`, `a = s = α = 2`, and the order-zero jets with `b = −3/2` at
distinct simple critical-line zeros with ordinates `t,u` arbitrarily close
together (Bui–Conrey–Young, Theorem 1.1, and the zeta zero count).
Dominated convergence in the reciprocal Sobolev weight makes
the dual norm of the difference of these jets tend to zero. On the
`t`-indexed lift the difference is one, forcing unbounded lift norms. -/
theorem Printed.spectralStripBasisLift_uniformUpperBound_false :
    ¬ Printed.spectralStripBasisLift_uniformUpperBound := by sorry

end RiemannMasullo
