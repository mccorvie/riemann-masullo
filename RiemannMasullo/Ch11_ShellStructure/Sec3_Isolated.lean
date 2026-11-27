module

public import RiemannMasullo.Ch11_ShellStructure.Sec3
public import RiemannMasullo.Ch11_ShellStructure.Sec3_Indentation
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-! # Theorem 11.3.2.1 with a normalized lift: the shell side of the omitted step

The proof of Theorem 11.3.2.1, pp. 495–496, identifies the trace of each idelic shell of the
geometric kernel with the orbital sum (11.3.2.5), through the step (11.3.1.3)–(11.3.1.4) that
p. 494 omits. This file is about that identification. Nothing imports it.

The printed weight (11.3.2.2) vanishes off a null set
(`Printed.orbitalTracesOnPaleyWienerLevels_false`), so the left side of (11.3.2.1) is
reconstructed here: the weight is replaced by a normalized lift (12.2.2.2), p. 508, built from
an indentation whose weight is invariant under simultaneous norm dilation, as the printed
weight is. Every statement of section `NormalizedLift` concerns this reconstruction, not the
printed weight. Such indentations exist (`exists_normSection_invariant_indentation`, pull
request #7415), and the statements rest on
`diagonalIndentationWeight_normSection_unit_outside_finite` of the same pull request, whose
pointwise consequence for one indentation is
`exists_indentation_divisorialKernelDifference_eq_zero`.

* Section `HalfTwistTrace`: the orbital sum (11.3.2.5) is the trace of the zero-line orbital
  convolution of Theorem 11.2.2.1 (`primeOrbitalSobolevConvolution_trace`) at the half-twisted
  test `φ |·|^(-1/2)`, and equals the Poisson side of (11.3.2.1)
  (`orbitalEulerSum_eq_poisson`). The twisted test is a hypothesis.
* Section `NormalizedLift`: for every such lift there is a finite set `T` of places such that
  the left side of (11.3.2.1), and the cut integrals (11.3.2.3)–(11.3.2.4), are zero at every
  saturated base containing `T`, and at every base for every shell whose new packet avoids `T`
  (`orbitalShell_invariantLift_integral_eq_zero`,
  `orbitalShell_invariantLift_integral_eq_zero_of_packet`). So (11.3.2.1) holds in the range
  used on p. 520, with both sides zero (`orbitalShell_invariantLift_eq_poisson_of_support`),
  and the equality of the shell trace with the zero-line trace holds there too
  (`orbitalShell_invariantLift_eq_zeroLineTrace_of_support`). Outside that range (11.3.2.1)
  fails: for a bump test at the residue size of a place the left side is zero and the right
  side is not (`orbitalShell_invariantLift_ne_poisson`,
  `orbitalShell_invariantLift_ne_poisson_of_packet`).
* Section `EqualNormSampling`: for the lift (12.2.2.2) with any real function `b`, and any
  homomorphism `τ`, the left side of (11.3.2.1) reads a kernel only at pairs of idele classes of
  equal norm, a null set of `C_F × C_F` (`sampledShell_congr_equalNorm`,
  `ideleClassTamagawaMeasure_prod_equalNorm_eq_zero`). For a test vanishing on the norm-one
  classes, as every test supported above norm one does, the convolution part `φ(x y⁻¹)` of the
  geometric kernel (10.4.3.50) contributes nothing there: the left side for `φ(x y⁻¹) − κ` is
  minus the left side for `κ`, for the values of a kernel (`sampledShell_convolution_sub`; for
  `globalStripGeometricKernel` when the strip tensor exists,
  `sampledShell_globalStripGeometricKernel_eq_neg`) and, for every Borel D′-sequence, for its
  smoothening (Definition 12.1.1.1) (`sampledShell_smoothening_convolution_sub`). Read through
  the values of a representative, (11.3.2.1) cannot hold for every representative of a spectral
  kernel that exists: at every finite place there is a radial test supported above norm one such
  that, for every kernel, the kernel made zero at the pairs of equal norm is equal to it almost
  everywhere and makes (11.3.2.1) fail for every lift
  (`sampledShell_equalNormRepresentative_ne_poisson`). Read through the smoothening, the left
  side depends only on the class of the kernel (`sampledShell_smoothening_congr_ae`). Nothing in
  this section assumes an indentation or an invariant weight.

The Paley–Wiener subquotients of (11.3.1.3) themselves, at a fixed Fourier box, are the
subject of pull request #7480 and are not treated here. -/

@[expose] public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "above(" p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset
local notation "ω(" χ ")" =>
  (χ : PontryaginDual C𝔽).comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
    C₁ →ₜ* C𝔽)
local notation "𝒟" => BruhatCompactSupport C𝔽

section HalfTwistTrace

/-- The Mellin transform of the half-twisted test is the half-shifted Mellin transform. -/
private theorem primeOrbitalSobolevConvolution_halfTwist_trace_mellin
    (χ : PontryaginDual C𝔽) (φ ψ : 𝒟)
    (hψ : ∀ g : C𝔽, ψ.val g =
      φ.val g * ((((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))))
    (z : ℂ) :
    nuclearityTestMellin χ ψ z = nuclearityTestMellin χ φ (z - 1 / 2) := by
  unfold nuclearityTestMellin
  refine integral_congr_ae (Eventually.of_forall fun g ↦ ?_)
  have hn : ((((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  change ψ.val g * (((χ g : Circle) : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ z) =
    φ.val g * (((χ g : Circle) : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (z - 1 / 2))
  rw [hψ g, sub_eq_add_neg, Complex.cpow_add _ _ hn]
  ring

/-- Paper: Theorem 11.2.2.1, p. 490, (11.3.1.4), p. 494, and (11.3.2.4)–(11.3.2.5), p. 496.
Let `ψ = φ |·|^(-1/2)`. The trace of the zero-line orbital convolution by `ψ` on the quotient
(11.2.2.1) is the sum (11.3.2.5), and it is the Poisson side of (11.3.2.1) with all places
over the prime. This rests on `primeOrbitalSobolevConvolution_trace` (Theorem 11.2.2.1),
`primeOrbitalMultiplicity_saturates` and `orbitalEulerSum_eq_poisson`.
Reconstruction: p. 496 obtains (11.3.2.5) as "the limit of the finite rank kernels from
(11.2.2.12)" after "incorporating the effect of multiplication by `|·|^(1/2)`". Conjugation
by that multiplication turns convolution by `φ` into convolution by `ψ`. So the one statement
p. 496 takes from the omitted step (11.3.1.3)–(11.3.1.4) is that the trace of the shell
equals `hilbertTrace T` below. The paper does not state this equality. For a reconstructed
left side it is `orbitalShell_invariantLift_eq_zeroLineTrace_of_support`.
Deviation: The twisted test `ψ` is a hypothesis. That `φ |·|^(-1/2)` is again a compactly
supported Bruhat test is not proved here. The degree bound `2 [F : ℚ] ≤ s` is that of
Theorem 11.2.2.1. -/
theorem primeOrbitalSobolevConvolution_halfTwist_trace
    (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (χ : PontryaginDual C𝔽) (h₁ : 1 < s)
    (hdeg : 2 * (Module.finrank ℚ F : ℝ) ≤ s)
    (hχ : ∀ v ∈ above(p), (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (φ ψ : 𝒟)
    (hψ : ∀ g : C𝔽, ψ.val g =
      φ.val g * ((((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))))
    (π : ∀ v : V, (v.adicCompletion F)ˣ)
    (hπ : ∀ v ∈ above(p), Valued.v.IsUniformizer (π v : v.adicCompletion F))
    (T : nuclearEndomorphisms
      (PrimeOrbitalSobolevQuotient F p (zero_lt_one.trans h₁).le (ω(χ))))
    (hT : T.val = primeOrbitalSobolevConvolution (F := F) p (zero_lt_one.trans h₁).le (ω(χ)) ψ) :
    HasSum (fun z : {z : ℂ // reciprocalPartialHeckeEulerProduct χ above(p) z = 0} ↦
        (orbitalEulerMultiplicity χ above(p) z.val : ℂ) *
          nuclearityTestMellin χ φ (z.val - 1 / 2)) (hilbertTrace T) ∧
      hilbertTrace T = ∑ v ∈ above(p), ∑' n : ℤ, orbitalPlacePoissonTerm χ φ v (π v) n := by
  have h := (primeOrbitalSobolevConvolution_trace (F := F) p χ h₁ hdeg hχ ψ T hT).2
  have hfun : (fun z : {z : ℂ // reciprocalPartialHeckeEulerProduct χ above(p) z = 0} ↦
      (orbitalEulerMultiplicity χ above(p) z.val : ℂ) *
        nuclearityTestMellin χ φ (z.val - 1 / 2)) =
      fun z ↦ (spectralBoundaryMultiplicity s (orbitalEulerMultiplicity χ above(p) z.val) : ℂ) *
        nuclearityTestMellin χ ψ z.val :=
    funext fun z ↦ by
      rw [primeOrbitalMultiplicity_saturates (F := F) p χ h₁ hdeg hχ z,
        primeOrbitalSobolevConvolution_halfTwist_trace_mellin χ φ ψ hψ z.val]
  have hsum : HasSum (fun z : {z : ℂ // reciprocalPartialHeckeEulerProduct χ above(p) z = 0} ↦
      (orbitalEulerMultiplicity χ above(p) z.val : ℂ) *
        nuclearityTestMellin χ φ (z.val - 1 / 2)) (hilbertTrace T) := by
    rw [hfun]
    exact h
  exact ⟨hsum, hsum.unique (orbitalEulerSum_eq_poisson χ φ p hχ π hπ)⟩

/-- Paper: §11.3.1.1(2), pp. 494–495, and the proof of Theorem 12.5.1.1, p. 520. If the test
is supported at norms strictly between one and the residue size of every place over the prime,
the trace of `primeOrbitalSobolevConvolution_halfTwist_trace` is zero, by
`orbitalPlacePoissonTerm_eq_zero`.
Deviation: The twisted test and the uniformizers are hypotheses. -/
theorem primeOrbitalSobolevConvolution_halfTwist_trace_eq_zero
    (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (χ : PontryaginDual C𝔽) (h₁ : 1 < s)
    (hdeg : 2 * (Module.finrank ℚ F : ℝ) ≤ s)
    (hχ : ∀ v ∈ above(p), (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (φ ψ : 𝒟)
    (hψ : ∀ g : C𝔽, ψ.val g =
      φ.val g * ((((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))))
    (π : ∀ v : V, (v.adicCompletion F)ˣ)
    (hπ : ∀ v ∈ above(p), Valued.v.IsUniformizer (π v : v.adicCompletion F))
    (hφ : ∀ v ∈ above(p), tsupport φ.val ⊆
      {g : C𝔽 | ((ideleClassNorm F g).val : ℝ) ∈ Ioo 1 (v.asIdeal.absNorm : ℝ)})
    (T : nuclearEndomorphisms
      (PrimeOrbitalSobolevQuotient F p (zero_lt_one.trans h₁).le (ω(χ))))
    (hT : T.val = primeOrbitalSobolevConvolution (F := F) p (zero_lt_one.trans h₁).le (ω(χ)) ψ) :
    hilbertTrace T = 0 := by
  rw [(primeOrbitalSobolevConvolution_halfTwist_trace p χ h₁ hdeg hχ φ ψ hψ π hπ T hT).2]
  refine Finset.sum_eq_zero fun v hv ↦ ?_
  rw [show (fun n : ℤ ↦ orbitalPlacePoissonTerm χ φ v (π v) n) = fun _ ↦ 0 from
    funext fun n ↦ orbitalPlacePoissonTerm_eq_zero χ φ v (π v) (hπ v hv) (hφ v hv) n]
  exact tsum_zero

end HalfTwistTrace

section NormalizedLift

attribute [local instance] instIdeleMeasurableSpaceSec1a instMeasurableSpaceAdicUnitsSec3a

local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "H𝔽" => IdeleGroup.principalSubgroup (𝓞 F) F
local notation "N𝔽" => (ideleNorm F).ker
local notation "principal" => IdeleGroup.unitEmbedding (𝓞 F) F
local notation "τ₀" => canonicalIdeleNormSection F
local notation "πclass(" v ", " π ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π
local notation "unitMass(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v).real ((v).adicCompletionIntegers F).units
local notation "W(" b ")" => diagonalIndentationWeight H𝔽 Measure.count b
local notation "shellIntegral(" S ", " k ", " b ", " K ", " E ")" =>
  (∑' ξ : Fˣ, ∫ t, ∫ g in (E : Set N𝔽),
    divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b K)
      (τ₀ t, principal ξ * g.val * τ₀ t)
    ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar)

/-- The pairs sampled in (11.3.2.1): the canonical norm section is a unit outside every base,
and its translate by a principal idele and a norm-one idele has the same norm. -/
private theorem orbitalShell_invariantLift_integral_eq_zero_sample (S : Finset V)
    (t : ℝ≥0ˣ) (ξ : Fˣ) (g : N𝔽) :
    τ₀ t ∈ sLocalDivisorialStratum F S ∧
      ideleNorm F (τ₀ t) = ideleNorm F (principal ξ * g.val * τ₀ t) := by
  refine ⟨fun v _ ↦ ?_, ?_⟩
  · rw [canonicalIdeleNormSection_finite]
    exact map_one _
  · rw [map_mul, map_mul, (ideleNorm_spec F).2 ⟨ξ, rfl⟩, MonoidHom.mem_ker.mp g.property,
      one_mul, one_mul]

/-- Paper: Theorem 11.3.2.1, (11.3.2.1)–(11.3.2.2), p. 495, with the weight (11.3.2.2)
replaced by a normalized lift (12.2.2.2), p. 508. For every normalized indentation whose
weight is invariant under simultaneous norm dilation, as the printed weight is, there is a
finite set of places such that for every saturated base containing it the shell kernel
vanishes on every pair sampled in (11.3.2.1), so the left side of (11.3.2.1) is zero: for
every shell, every quotient kernel and every domain of norm-one ideles. The same holds after
multiplying by any further factor of the sampling variables, which covers the cut integrals
(11.3.2.3)–(11.3.2.4), p. 496, and their limits.
Reconstruction: this is not the printed left side. The printed weight (11.3.2.2) vanishes
off a null set (`Printed.orbitalTracesOnPaleyWienerLevels_false`); here it is replaced by the
lift `diagonalIndentationLift` of a dilation-invariant indentation. Such indentations exist
(`exists_normSection_invariant_indentation`). The proof rests on
`diagonalIndentationWeight_normSection_unit_outside_finite` and integrates, for every such
indentation, the pointwise statement that
`exists_indentation_divisorialKernelDifference_eq_zero` gives for one of them.
Deviation: The paper does not state this. With such a left side, (11.3.2.1) holds at a large
base exactly when its right side is zero. -/
theorem orbitalShell_invariantLift_integral_eq_zero {b : I𝔽 → ℝ}
    (hb : IsIndentation H𝔽 Measure.count b)
    (hinv : ∀ (t : ℝ≥0ˣ) (x y : I𝔽), W(b) (x * τ₀ t, y * τ₀ t) = W(b) (x, y)) :
    ∃ T : Finset V, ∀ S, T ⊆ S →
      (∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) →
      ∀ (k : ℕ) (K : C𝔽 × C𝔽 → ℂ) (E : Set N𝔽),
        (∀ (ξ : Fˣ) (t : ℝ≥0ˣ) (g : N𝔽),
          divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b K)
            (τ₀ t, principal ξ * g.val * τ₀ t) = 0) ∧
        shellIntegral(S, k, b, K, E) = 0 ∧
        ∀ c : Fˣ → ℝ≥0ˣ → N𝔽 → ℂ, (∑' ξ : Fˣ, ∫ t, ∫ g in E,
          divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b K)
            (τ₀ t, principal ξ * g.val * τ₀ t) * c ξ t g
          ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) = 0 := by
  obtain ⟨T, hT⟩ := diagonalIndentationWeight_normSection_unit_outside_finite hb hinv
  refine ⟨T, fun S hTS hS k K E ↦ ?_⟩
  have hz (ξ : Fˣ) (t : ℝ≥0ˣ) (g : N𝔽) :
      divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b K)
        (τ₀ t, principal ξ * g.val * τ₀ t) = 0 := by
    obtain ⟨hx, hn⟩ := orbitalShell_invariantLift_integral_eq_zero_sample S t ξ g
    by_cases hw : W(b) (τ₀ t, principal ξ * g.val * τ₀ t) = 0
    · simp only [divisorialKernelDifference, diagonalIndentationLift, hw, Complex.ofReal_zero,
        zero_mul, mul_zero]
    · have hr : principal ξ * g.val * τ₀ t / τ₀ t ∈ sLocalDivisorialStratum F S :=
        fun v hv ↦ hT _ _ hn hw v (fun h ↦ hv (hTS h))
      have hy : principal ξ * g.val * τ₀ t ∈ sLocalDivisorialStratum F S := by
        rw [sLocalDivisorialStratum_eq_range_integralIdeleInsertion] at hx hr ⊢
        exact div_mul_cancel (principal ξ * g.val * τ₀ t) (τ₀ t) ▸
          (integralIdeleInsertion F S).range.mul_mem hr hx
      rw [← iInter_primaryDivisorialStratum S hS] at hy
      have hall := mem_iInter.mp hy
      simp only [divisorialKernelDifference, divisorialIndicator_eq_indicator,
        indicator_of_mem (hall _), sub_self, zero_mul]
  refine ⟨hz, ?_, fun c ↦ ?_⟩
  · simp only [hz, integral_zero, tsum_zero]
  · simp only [hz, zero_mul, integral_zero, tsum_zero]

/-- Paper: (11.3.1.4), p. 494, as used in the proof of Theorem 12.5.1.1, p. 520. For a
normalized indentation with dilation-invariant weight and a saturated base containing the
finite set of `orbitalShell_invariantLift_integral_eq_zero`, the lifted kernel agrees on every
sampled pair with its restriction to the ideles that are units outside the base. So in the
decomposition of p. 520 the whole diagonal mass is the `S`-local part, and every shell term is
zero.
Reconstruction: the kernel is lifted by a normalized indentation, not by the printed weight.
Deviation: The paper does not state this. It follows from the telescoping
`hasSum_divisorialKernelDifference`. -/
theorem orbitalShell_invariantLift_eq_sLocal {b : I𝔽 → ℝ}
    (hb : IsIndentation H𝔽 Measure.count b)
    (hinv : ∀ (t : ℝ≥0ˣ) (x y : I𝔽), W(b) (x * τ₀ t, y * τ₀ t) = W(b) (x, y)) :
    ∃ T : Finset V, ∀ S, T ⊆ S →
      (∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) →
      ∀ (K : C𝔽 × C𝔽 → ℂ) (ξ : Fˣ) (t : ℝ≥0ˣ) (g : N𝔽),
        (sLocalDivisorialStratum F S).indicator
          (fun _ ↦ diagonalIndentationLift H𝔽 Measure.count b K
            (τ₀ t, principal ξ * g.val * τ₀ t)) (principal ξ * g.val * τ₀ t) =
          diagonalIndentationLift H𝔽 Measure.count b K (τ₀ t, principal ξ * g.val * τ₀ t) := by
  obtain ⟨T, h⟩ := orbitalShell_invariantLift_integral_eq_zero hb hinv
  refine ⟨T, fun S hTS hS K ξ t g ↦ ?_⟩
  have hs := hasSum_divisorialKernelDifference S hS
    (diagonalIndentationLift H𝔽 Measure.count b K) (τ₀ t, principal ξ * g.val * τ₀ t)
  have hz : (fun k ↦ divisorialKernelDifference S k
      (diagonalIndentationLift H𝔽 Measure.count b K) (τ₀ t, principal ξ * g.val * τ₀ t)) =
      fun _ ↦ 0 := funext fun k ↦ (h S hTS hS k K ∅).1 ξ t g
  rw [hz] at hs
  exact sub_eq_zero.mp (hs.unique hasSum_zero)

/-- A test that vanishes on the norm-one classes and is supported at norms strictly between
the inverse residue size and the residue size vanishes at every translate of a power of the
uniformizer class by a norm-one class. -/
private theorem orbitalShell_invariantLift_eq_poisson_of_support_zero (φ : 𝒟) (v : V)
    (π : (v.adicCompletion F)ˣ) (hπ : Valued.v.IsUniformizer (π : v.adicCompletion F))
    (hφ : tsupport φ.val ⊆ {g : C𝔽 | ((ideleClassNorm F g).val : ℝ) ∈
      Ioo ((v.asIdeal.absNorm : ℝ)⁻¹) (v.asIdeal.absNorm : ℝ)})
    (h₁ : ∀ g : C₁, φ.val g.val = 0) (n : ℤ) (h : C₁) :
    φ.val (πclass(v, π) ^ n * h.val) = 0 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [zpow_zero, one_mul]
    exact h₁ h
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hm := hφ hmem
  simp only [Set.mem_ofPred_eq] at hm
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hh : ideleClassNorm F h.val = 1 := h.2
  have hn : (((ideleClassNorm F (πclass(v, π) ^ n * h.val)).val : ℝ≥0) : ℝ) =
      (v.asIdeal.absNorm : ℝ) ^ (-n) := by
    rw [map_mul, map_zpow, ideleClassNorm_ofAdicCompletion, hh, mul_one]
    rw [Units.val_zpow_eq_zpow_val, NNReal.coe_zpow, Units.coe_map]
    change ‖π.val‖ ^ n = _
    rw [norm_uniformizer_adicCompletion v _ hπ, inv_zpow', zpow_neg]
  rw [hn] at hm
  obtain ⟨hm1, hm2⟩ := hm
  rcases lt_or_gt_of_ne hn0 with h0 | h0
  · have : (v.asIdeal.absNorm : ℝ) ≤ (v.asIdeal.absNorm : ℝ) ^ (-n) := by
      calc (v.asIdeal.absNorm : ℝ) = (v.asIdeal.absNorm : ℝ) ^ (1 : ℤ) := (zpow_one _).symm
        _ ≤ _ := zpow_le_zpow_right₀ hq.le (by omega)
    linarith
  · have : (v.asIdeal.absNorm : ℝ) ^ (-n) ≤ (v.asIdeal.absNorm : ℝ) ^ (-1 : ℤ) :=
      zpow_le_zpow_right₀ hq.le (by omega)
    rw [zpow_neg_one] at this
    linarith

/-- Paper: Theorem 11.3.2.1, p. 495, in the range used in the proof of Theorem 12.5.1.1,
p. 520, with the weight (11.3.2.2) replaced by a normalized lift (12.2.2.2), p. 508. For
every normalized indentation with dilation-invariant weight, every saturated base containing
the finite set of `orbitalShell_invariantLift_integral_eq_zero`, and every test that vanishes
on the norm-one classes and is supported at norms strictly between the inverse residue size
and the residue size of a place `v`, the identity (11.3.2.1) holds at `v`: both sides are
zero.
Reconstruction: the left side is that of `orbitalShell_invariantLift_integral_eq_zero`, not
the printed one. Page 520 takes a test that vanishes on the norm-one classes and chooses the
base so large that the norms of its support lie in `(1/T, T)` with `T` below the residue size
of every place outside the base. It uses only this case. No Paley–Wiener subquotient and no
lift of an orbital basis enters.
Deviation: The paper states (11.3.2.1) with the weight (11.3.2.2), for tests supported above
norm one, without the bound by the residue size. With the printed weight it is false; with a
normalized lift and a large base its left side is always zero. -/
theorem orbitalShell_invariantLift_eq_poisson_of_support {b : I𝔽 → ℝ}
    (hb : IsIndentation H𝔽 Measure.count b)
    (hinv : ∀ (t : ℝ≥0ˣ) (x y : I𝔽), W(b) (x * τ₀ t, y * τ₀ t) = W(b) (x, y)) :
    ∃ T : Finset V, ∀ S, T ⊆ S →
      (∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) →
      ∀ (k : ℕ) (K : C𝔽 × C𝔽 → ℂ) (E : Set N𝔽) (φ : 𝒟) (v : V)
        (π : (v.adicCompletion F)ˣ), Valued.v.IsUniformizer (π : v.adicCompletion F) →
        tsupport φ.val ⊆ {g : C𝔽 | ((ideleClassNorm F g).val : ℝ) ∈
          Ioo ((v.asIdeal.absNorm : ℝ)⁻¹) (v.asIdeal.absNorm : ℝ)} →
        (∀ g : C₁, φ.val g.val = 0) →
        shellIntegral(S, k, b, K, E) =
          (Real.log (v.asIdeal.absNorm : ℝ) / unitMass(v) : ℂ) *
            ∑' n : ℤ, φ.val (πclass(v, π) ^ n) := by
  obtain ⟨T, h⟩ := orbitalShell_invariantLift_integral_eq_zero hb hinv
  refine ⟨T, fun S hTS hS k K E φ v π hπ hφ h₁ ↦ ?_⟩
  rw [(h S hTS hS k K E).2.1]
  have hz (n : ℤ) : φ.val (πclass(v, π) ^ n) = 0 := by
    have h0 := orbitalShell_invariantLift_eq_poisson_of_support_zero φ v π hπ hφ h₁ n 1
    rwa [OneMemClass.coe_one, mul_one] at h0
  simp only [hz, tsum_zero, mul_zero]

/-- Paper: the proof of Theorem 11.3.2.1, (11.3.2.4)–(11.3.2.5), p. 496, in the range used on
p. 520. For a normalized indentation with dilation-invariant weight and a large saturated
base, the left side of (11.3.2.1) at any shell equals the trace of the zero-line orbital
convolution of Theorem 11.2.2.1 at the half-twisted test `ψ = φ |·|^(-1/2)`, when the test
vanishes on the norm-one classes and is supported at norms strictly between the inverse
residue size and the residue size of every place over the prime: both are zero.
Reconstruction: this is the equality that p. 496 takes from the omitted step
(11.3.1.3)–(11.3.1.4), with the left side reconstructed by the normalized lift. Outside this
range the left side is still zero for a large base, and the trace is the Poisson sum of
`primeOrbitalSobolevConvolution_halfTwist_trace`, so the equality holds exactly when that
sum vanishes.
Deviation: The twisted test `ψ` and the uniformizers are hypotheses. -/
theorem orbitalShell_invariantLift_eq_zeroLineTrace_of_support {b : I𝔽 → ℝ}
    (hb : IsIndentation H𝔽 Measure.count b)
    (hinv : ∀ (t : ℝ≥0ˣ) (x y : I𝔽), W(b) (x * τ₀ t, y * τ₀ t) = W(b) (x, y)) :
    ∃ T : Finset V, ∀ S, T ⊆ S →
      (∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) →
      ∀ (k : ℕ) (K : C𝔽 × C𝔽 → ℂ) (E : Set N𝔽) (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ}
        (χ : PontryaginDual C𝔽) (h₁ : 1 < s) (_hdeg : 2 * (Module.finrank ℚ F : ℝ) ≤ s)
        (_hχ : ∀ v ∈ above(p), (ideleClassNormTwist χ 0).IsUnramifiedAt v) (φ ψ : 𝒟)
        (_hψ : ∀ g : C𝔽, ψ.val g =
          φ.val g * ((((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))))
        (π : ∀ v : V, (v.adicCompletion F)ˣ)
        (_hπ : ∀ v ∈ above(p), Valued.v.IsUniformizer (π v : v.adicCompletion F))
        (_hφ : ∀ v ∈ above(p), tsupport φ.val ⊆
          {g : C𝔽 | ((ideleClassNorm F g).val : ℝ) ∈
            Ioo ((v.asIdeal.absNorm : ℝ)⁻¹) (v.asIdeal.absNorm : ℝ)})
        (_h₁ : ∀ g : C₁, φ.val g.val = 0)
        (Tr : nuclearEndomorphisms
          (PrimeOrbitalSobolevQuotient F p (zero_lt_one.trans h₁).le (ω(χ))))
        (_hT : Tr.val =
          primeOrbitalSobolevConvolution (F := F) p (zero_lt_one.trans h₁).le (ω(χ)) ψ),
        shellIntegral(S, k, b, K, E) = hilbertTrace Tr := by
  obtain ⟨T, h⟩ := orbitalShell_invariantLift_integral_eq_zero hb hinv
  refine ⟨T, fun S hTS hS k K E p s χ h₁ hdeg hχ φ ψ hψ π hπ hφ hone Tr hT ↦ ?_⟩
  rw [(h S hTS hS k K E).2.1,
    (primeOrbitalSobolevConvolution_halfTwist_trace p χ h₁ hdeg hχ φ ψ hψ π hπ Tr hT).2]
  refine (Finset.sum_eq_zero fun v hv ↦ ?_).symm
  have hterm (n : ℤ) : orbitalPlacePoissonTerm χ φ v (π v) n = 0 := by
    have hz : ∀ h : C₁, φ.val (πclass(v, π v) ^ n * h.val) = 0 := fun h ↦
      orbitalShell_invariantLift_eq_poisson_of_support_zero φ v (π v) (hπ v hv) (hφ v hv)
        hone n h
    unfold orbitalPlacePoissonTerm
    simp only [hz, zero_mul, integral_zero, mul_zero]
  simp only [hterm, tsum_zero]

open scoped ContDiff in
/-- Composition with a smooth function of the complex plane keeps Bruhat smoothness. -/
private theorem orbitalShell_invariantLift_ne_poisson_comp {G : Type*} [CommGroup G]
    [TopologicalSpace G] {u : G → ℂ} (hu : IsBruhatSmooth u) {f : ℂ → ℂ}
    (hf : ContDiff ℝ (∞) f) : IsBruhatSmooth (fun x ↦ f (u x)) := by
  intro p
  obtain ⟨k, hk, hi, hdesc⟩ := hu p
  refine ⟨k, hk, fun h x ↦ congrArg f (hi h x), ?_⟩
  intro a ha
  obtain ⟨q, hq, hdiff⟩ := hdesc a ha
  exact ⟨fun y ↦ f (q y), fun x ↦ congrArg f (hq x),
    fun e z b ↦ (hf.of_le (by simp)).comp (hdiff e z b)⟩

/-- At every finite place there is a radial test supported above norm one whose values at
the powers of the uniformizer class sum to one: a bump at the residue size. -/
private theorem orbitalShell_invariantLift_ne_poisson_test (v : V)
    (π : (v.adicCompletion F)ˣ) (hπ : Valued.v.IsUniformizer (π : v.adicCompletion F)) :
    ∃ φ : 𝒟, tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)} ∧
      (∀ x y : C𝔽, ideleClassNorm F x = ideleClassNorm F y → φ.val x = φ.val y) ∧
      (∑' n : ℤ, φ.val (πclass(v, π) ^ n)) = 1 := by
  let q : ℝ := v.asIdeal.absNorm
  have hq2 : (2 : ℝ) ≤ q := by
    change (2 : ℝ) ≤ (v.asIdeal.absNorm : ℝ)
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hd : 0 < q / 2 := by positivity
  let nrm (x : C𝔽) : ℝ := ((ideleClassNorm F x).val : ℝ)
  have hnc : Continuous nrm := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hnpos (x : C𝔽) : 0 < nrm x := NNReal.coe_pos.mpr (Units.zero_lt _)
  let B : ContDiffBump (2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  let χ : QuasiCharacter C𝔽 :=
    { toFun := fun x ↦ (nrm x : ℂ)
      map_one' := by simp [nrm]
      map_mul' := fun x y ↦ by simp [nrm]
      continuous_toFun := Complex.continuous_ofReal.comp hnc }
  let f (z : ℂ) : ℂ := B (z.re / (q / 2))
  have hs : IsBruhatSmooth (fun x : C𝔽 ↦ (B (nrm x / (q / 2)) : ℂ)) := by
    apply orbitalShell_invariantLift_ne_poisson_comp (u := fun x ↦ χ x) (f := f)
      ((mem_bruhatSmoothSubmodule_iff _).1 (quasiCharacter_mem_bruhatSmooth χ))
    exact Complex.ofRealCLM.contDiff.comp
      (B.contDiff.comp (Complex.reCLM.contDiff.div_const (q / 2)))
  have hband (x : C𝔽) (hB : B (nrm x / (q / 2)) ≠ 0) :
      7 / 4 * (q / 2) ≤ nrm x ∧ nrm x ≤ 9 / 4 * (q / 2) := by
    have hm := subset_tsupport _ hB
    rw [B.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, abs_le] at hm
    change -(1 / 4 : ℝ) ≤ _ ∧ _ ≤ 1 / 4 at hm
    exact ⟨(le_div_iff₀ hd).1 (by linarith [hm.1]), (div_le_iff₀ hd).1 (by linarith [hm.2])⟩
  let unit (t : ℝ) : ℝ≥0ˣ := Units.mk0 (Real.exp t).toNNReal
    (Real.toNNReal_pos.mpr (Real.exp_pos t)).ne'
  have hu : Continuous unit := Units.continuous_iff.mpr
    ⟨continuous_real_toNNReal.comp Real.continuous_exp,
      (continuous_real_toNNReal.comp Real.continuous_exp).inv₀ fun t ↦
        (Real.toNNReal_pos.mpr (Real.exp_pos t)).ne'⟩
  have hc : HasCompactSupport (fun x : C𝔽 ↦ (B (nrm x / (q / 2)) : ℂ)) := by
    apply HasCompactSupport.intro ((isProperMap_ideleClassNorm F).isCompact_preimage
      ((isCompact_Icc (a := Real.log (7 / 4 * (q / 2)))
        (b := Real.log (9 / 4 * (q / 2)))).image hu))
    intro x hx
    by_contra hn
    have hB : B (nrm x / (q / 2)) ≠ 0 := fun h ↦
      hn (show ((B (nrm x / (q / 2)) : ℝ) : ℂ) = 0 by rw [h, Complex.ofReal_zero])
    obtain ⟨hl, hr⟩ := hband x hB
    apply hx
    refine ⟨Real.log (nrm x), ⟨Real.log_le_log (by positivity) hl,
      Real.log_le_log (hnpos x) hr⟩, ?_⟩
    apply Units.ext
    change (Real.exp (Real.log _)).toNNReal = _
    rw [Real.exp_log (hnpos x), Real.toNNReal_coe]
  let φ : 𝒟 := ⟨_, (mem_bruhatSmoothSubmodule_iff _).2 hs, hc⟩
  have hφ (x : C𝔽) : φ.val x = (B (nrm x / (q / 2)) : ℂ) := rfl
  have hnorm (n : ℤ) : nrm (πclass(v, π) ^ n) = q ^ (-n) := by
    change (((ideleClassNorm F (πclass(v, π) ^ n)).val : ℝ≥0) : ℝ) = _
    rw [map_zpow, ideleClassNorm_ofAdicCompletion, Units.val_zpow_eq_zpow_val, NNReal.coe_zpow,
      Units.coe_map]
    change ‖π.val‖ ^ n = _
    rw [norm_uniformizer_adicCompletion v _ hπ, inv_zpow', zpow_neg]
  refine ⟨φ, ?_, fun x y h ↦ ?_, ?_⟩
  · have hsub : tsupport φ.val ⊆ {x : C𝔽 | 7 / 4 * (q / 2) ≤ nrm x} := by
      refine closure_minimal (fun x hx ↦ ?_) (isClosed_le continuous_const hnc)
      have hB : B (nrm x / (q / 2)) ≠ 0 := fun h ↦
        hx (show ((B (nrm x / (q / 2)) : ℝ) : ℂ) = 0 by rw [h, Complex.ofReal_zero])
      exact (hband x hB).1
    intro x hx
    have h : 7 / 4 * (q / 2) ≤ nrm x := hsub hx
    change 1 < nrm x
    nlinarith
  · rw [hφ, hφ]
    change (B (((ideleClassNorm F x).val : ℝ) / (q / 2)) : ℂ) =
      B (((ideleClassNorm F y).val : ℝ) / (q / 2))
    rw [h]
  · rw [tsum_eq_single (-1 : ℤ)]
    · rw [hφ, hnorm]
      have h2 : q ^ (-(-1 : ℤ)) / (q / 2) = 2 := by
        rw [neg_neg, zpow_one]
        field_simp
      rw [h2]
      simp [B.one_of_mem_closedBall (Metric.mem_closedBall_self B.rIn_pos.le)]
    · intro n hn
      rw [hφ, hnorm]
      by_contra hne
      have hB : B (q ^ (-n) / (q / 2)) ≠ 0 := fun h ↦
        hne (show ((B (q ^ (-n) / (q / 2)) : ℝ) : ℂ) = 0 by rw [h, Complex.ofReal_zero])
      have hb := hband (πclass(v, π) ^ n) (by rw [hnorm]; exact hB)
      rw [hnorm] at hb
      rcases le_or_gt 0 n with hpos | hneg
      · have h1 : q ^ (-n) ≤ 1 := zpow_le_one_of_nonpos₀ (by linarith) (by omega)
        nlinarith [hb.1]
      · have h1 : q ^ (2 : ℤ) ≤ q ^ (-n) := zpow_le_zpow_right₀ (by linarith) (by omega)
        rw [zpow_ofNat] at h1
        nlinarith [hb.2]

/-- The local unit mass in the right side of (11.3.2.1) is not zero. -/
private theorem orbitalShell_invariantLift_ne_poisson_mass (v : V) : unitMass(v) ≠ 0 := by
  rw [Measure.real, finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_inv]
  refine inv_ne_zero ?_
  rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  exact (Real.sqrt_pos.mpr (pow_pos (by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)) _)).ne'

/-- Paper: Theorem 11.3.2.1, p. 495, with the weight (11.3.2.2) replaced by a normalized lift
(12.2.2.2), p. 508. No normalized indentation with dilation-invariant weight makes (11.3.2.1)
true at a large base: for every saturated base containing the finite set of
`orbitalShell_invariantLift_integral_eq_zero`, every shell, every kernel, every finite place
and every uniformizer, there is a radial test supported above norm one for which the two sides
of (11.3.2.1) differ. The left side is zero and the right side is
`log q_v / μ_v(O_v^×) ≠ 0`.
Reconstruction: the left side is the reconstructed one, not the printed one. The test is a
bump at the residue size of the place, so it is outside the range used on p. 520. A radial
test is invariant under the units outside every base.
Deviation: The paper does not state this. It shows that the identification on p. 496 of the
shell trace with the orbital sum (11.3.2.5) fails for such a lift once the base is large. -/
theorem orbitalShell_invariantLift_ne_poisson {b : I𝔽 → ℝ}
    (hb : IsIndentation H𝔽 Measure.count b)
    (hinv : ∀ (t : ℝ≥0ˣ) (x y : I𝔽), W(b) (x * τ₀ t, y * τ₀ t) = W(b) (x, y)) :
    ∃ T : Finset V, ∀ S, T ⊆ S →
      (∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) →
      ∀ (k : ℕ) (K : C𝔽 × C𝔽 → ℂ) (E : Set N𝔽) (v : V) (π : (v.adicCompletion F)ˣ),
        Valued.v.IsUniformizer (π : v.adicCompletion F) →
        ∃ φ : 𝒟, tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)} ∧
          (∀ x y : C𝔽, ideleClassNorm F x = ideleClassNorm F y → φ.val x = φ.val y) ∧
          shellIntegral(S, k, b, K, E) ≠
            (Real.log (v.asIdeal.absNorm : ℝ) / unitMass(v) : ℂ) *
              ∑' n : ℤ, φ.val (πclass(v, π) ^ n) := by
  obtain ⟨T, h⟩ := orbitalShell_invariantLift_integral_eq_zero hb hinv
  refine ⟨T, fun S hTS hS k K E v π hπ ↦ ?_⟩
  obtain ⟨φ, h1, h2, h3⟩ := orbitalShell_invariantLift_ne_poisson_test v π hπ
  refine ⟨φ, h1, h2, ?_⟩
  rw [(h S hTS hS k K E).2.1, h3, mul_one]
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  exact (div_ne_zero (Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne')
    (Complex.ofReal_ne_zero.mpr (orbitalShell_invariantLift_ne_poisson_mass v))).symm

/-- Paper: Theorem 11.3.2.1, (11.3.2.1)–(11.3.2.2), p. 495, with the weight (11.3.2.2)
replaced by a normalized lift (12.2.2.2), p. 508, at an arbitrary base. For every normalized
indentation with dilation-invariant weight there is a finite set `T` of places such that, for
every base and every shell whose new packet of places avoids `T`, the shell kernel vanishes on
every pair sampled in (11.3.2.1) and the left side of (11.3.2.1) is zero.
Reconstruction: the left side is the reconstructed one, as in
`orbitalShell_invariantLift_integral_eq_zero`. The proof rests on
`diagonalIndentationWeight_normSection_unit_outside_finite`.
Deviation: The paper does not state this. Here the base need not contain `T` and need not be
saturated. The packets of distinct shells are disjoint, so at every base all but finitely many
shells are covered (`primaryDivisorialPackets_meet_finite`). -/
theorem orbitalShell_invariantLift_integral_eq_zero_of_packet {b : I𝔽 → ℝ}
    (hb : IsIndentation H𝔽 Measure.count b)
    (hinv : ∀ (t : ℝ≥0ˣ) (x y : I𝔽), W(b) (x * τ₀ t, y * τ₀ t) = W(b) (x, y)) :
    ∃ T : Finset V, ∀ (S : Finset V) (k : ℕ),
      (∀ v ∈ above(primaryDivisorialPrime (F := F) S k), v ∉ T) →
      ∀ (K : C𝔽 × C𝔽 → ℂ) (E : Set N𝔽),
        (∀ (ξ : Fˣ) (t : ℝ≥0ˣ) (g : N𝔽),
          divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b K)
            (τ₀ t, principal ξ * g.val * τ₀ t) = 0) ∧
        shellIntegral(S, k, b, K, E) = 0 := by
  classical
  obtain ⟨T, hT⟩ := diagonalIndentationWeight_normSection_unit_outside_finite hb hinv
  refine ⟨T, fun S k hnew K E ↦ ?_⟩
  have hz (ξ : Fˣ) (t : ℝ≥0ˣ) (g : N𝔽) :
      divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b K)
        (τ₀ t, principal ξ * g.val * τ₀ t) = 0 := by
    obtain ⟨hx, hn⟩ := orbitalShell_invariantLift_integral_eq_zero_sample T t ξ g
    by_cases hw : W(b) (τ₀ t, principal ξ * g.val * τ₀ t) = 0
    · simp only [divisorialKernelDifference, diagonalIndentationLift, hw, Complex.ofReal_zero,
        zero_mul, mul_zero]
    · have hr : principal ξ * g.val * τ₀ t / τ₀ t ∈ sLocalDivisorialStratum F T :=
        hT _ _ hn hw
      have hy : principal ξ * g.val * τ₀ t ∈ sLocalDivisorialStratum F T := by
        rw [sLocalDivisorialStratum_eq_range_integralIdeleInsertion] at hx hr ⊢
        exact div_mul_cancel (principal ξ * g.val * τ₀ t) (τ₀ t) ▸
          (integralIdeleInsertion F T).range.mul_mem hr hx
      have hiff : principal ξ * g.val * τ₀ t ∈
          divisorialStratum F (primaryDivisorialPlaces F S (k + 1)) ↔
          principal ξ * g.val * τ₀ t ∈ divisorialStratum F (primaryDivisorialPlaces F S k) := by
        rw [primaryDivisorialPlaces_succ]
        exact ⟨fun h v hv ↦ h v (Finset.mem_union_left _ hv), fun h v hv ↦
          (Finset.mem_union.mp hv).elim (h v) fun h2 ↦ hy v (hnew v h2)⟩
      by_cases hm : principal ξ * g.val * τ₀ t ∈
          divisorialStratum F (primaryDivisorialPlaces F S k)
      · simp only [divisorialKernelDifference, divisorialIndicator_eq_indicator,
          indicator_of_mem (hiff.mpr hm), indicator_of_mem hm, sub_self, zero_mul]
      · simp only [divisorialKernelDifference, divisorialIndicator_eq_indicator,
          indicator_of_notMem (fun h ↦ hm (hiff.mp h)), indicator_of_notMem hm, sub_self,
          zero_mul]
  exact ⟨hz, by simp only [hz, integral_zero, tsum_zero]⟩

/-- Paper: §11.3.1.1, p. 493. For every base and every finite set of places, only finitely
many shells have a new packet that meets the set: the packets lie over distinct rational
primes.
Deviation: The paper does not state this. -/
theorem primaryDivisorialPackets_meet_finite (S T : Finset V) :
    {k : ℕ | ∃ v ∈ above(primaryDivisorialPrime (F := F) S k), v ∈ T}.Finite := by
  classical
  have hinf : {p : ℕ | p.Prime ∧
      p ∉ S.image (fun v ↦ Rat.HeightOneSpectrum.natGenerator (v.under (𝓞 ℚ)))}.Infinite := by
    refine (Nat.infinite_setOfPred_prime.sdiff (S.image (fun v ↦
      Rat.HeightOneSpectrum.natGenerator (v.under (𝓞 ℚ)))).finite_toSet).mono fun p hp ↦ ?_
    exact ⟨hp.1, by simpa using hp.2⟩
  have hinj : Function.Injective (primaryDivisorialPrime (F := F) S) := by
    intro i j hij
    unfold primaryDivisorialPrime at hij
    exact Nat.nth_injective hinf
      (congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.symm.injective hij))
  refine ((T.image (fun v ↦ v.under (𝓞 ℚ))).finite_toSet.preimage
    hinj.injOn).subset ?_
  rintro k ⟨v, hv, hvT⟩
  have hu : v.under (𝓞 ℚ) = primaryDivisorialPrime (F := F) S k := by
    simpa [Set.Finite.mem_toFinset] using hv
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨v, hvT, hu⟩)

/-- Paper: Theorem 11.3.2.1, p. 495, with the weight (11.3.2.2) replaced by a normalized lift
(12.2.2.2), p. 508, at an arbitrary base. For every normalized indentation with
dilation-invariant weight, every base, every shell whose new packet avoids the finite set of
`orbitalShell_invariantLift_integral_eq_zero_of_packet`, and every place of that packet, there
is a radial test supported above norm one for which the two sides of (11.3.2.1) differ.
Reconstruction: the left side is the reconstructed one, not the printed one.
Deviation: The paper does not state this. At every base, (11.3.2.1) with such a lift fails at
all but finitely many shells. -/
theorem orbitalShell_invariantLift_ne_poisson_of_packet {b : I𝔽 → ℝ}
    (hb : IsIndentation H𝔽 Measure.count b)
    (hinv : ∀ (t : ℝ≥0ˣ) (x y : I𝔽), W(b) (x * τ₀ t, y * τ₀ t) = W(b) (x, y)) :
    ∃ T : Finset V, ∀ (S : Finset V) (k : ℕ),
      (∀ v ∈ above(primaryDivisorialPrime (F := F) S k), v ∉ T) →
      ∀ (K : C𝔽 × C𝔽 → ℂ) (E : Set N𝔽), ∀ v ∈ above(primaryDivisorialPrime (F := F) S k),
        ∀ π : (v.adicCompletion F)ˣ, Valued.v.IsUniformizer (π : v.adicCompletion F) →
        ∃ φ : 𝒟, tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)} ∧
          (∀ x y : C𝔽, ideleClassNorm F x = ideleClassNorm F y → φ.val x = φ.val y) ∧
          shellIntegral(S, k, b, K, E) ≠
            (Real.log (v.asIdeal.absNorm : ℝ) / unitMass(v) : ℂ) *
              ∑' n : ℤ, φ.val (πclass(v, π) ^ n) := by
  obtain ⟨T, h⟩ := orbitalShell_invariantLift_integral_eq_zero_of_packet hb hinv
  refine ⟨T, fun S k hnew K E v _ π hπ ↦ ?_⟩
  obtain ⟨φ, h1, h2, h3⟩ := orbitalShell_invariantLift_ne_poisson_test v π hπ
  refine ⟨φ, h1, h2, ?_⟩
  rw [(h S k hnew K E).2, h3, mul_one]
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  exact (div_ne_zero (Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne')
    (Complex.ofReal_ne_zero.mpr (orbitalShell_invariantLift_ne_poisson_mass v))).symm

end NormalizedLift

section EqualNormSampling

/-! ### What the left side of (11.3.2.1) reads of a kernel

The left side of (11.3.2.1) evaluates the lifted kernel at the pairs `(τ t, ξ g τ t)`, with `ξ`
principal and `g` a norm-one idele. The two classes then differ by the norm-one class of `g`, so
these are pairs of idele classes of equal norm, a null set of `C_F × C_F`. Nothing in this
section assumes an indentation or an invariant weight: the statements hold for the lift
(12.2.2.2) with any real function `b`, and for any homomorphism `τ`. Two consequences:

* the convolution part `φ(x y⁻¹)` of the geometric kernel (10.4.3.50) is zero at these pairs when
  `φ` vanishes on the norm-one classes, as every test of Theorems 11.3.2.1 and 12.5.1.1 does, so
  the left side of (11.3.2.1) for `φ(x y⁻¹) − κ` is minus the same expression for `κ`. This holds
  for the values of a kernel and, for every Borel D′-sequence, for its smoothening
  (Definition 12.1.1.1, p. 498), which the paper applies along the diagonal; on the diagonal it
  is (12.1.1.23), p. 503;
* Definition 10.4.3.7(1), p. 473, gives the spectral kernel as a measurable function made from an
  element of an `L²` space, so its values on a null set, such as these pairs, are not fixed by
  it. Read through the values of a representative, as `globalStripGeometricKernel` reads the
  coercion of an `L²` class, (11.3.2.1) cannot hold for every representative of a spectral kernel
  that exists. Read through the smoothening, the left side depends only on the class of the
  kernel. -/

open scoped ENNReal Topology

attribute [local instance] instIdeleMeasurableSpaceSec1a instMeasurableSpaceAdicUnitsSec3a

local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "H𝔽" => IdeleGroup.principalSubgroup (𝓞 F) F
local notation "N𝔽" => (ideleNorm F).ker
local notation "principal" => IdeleGroup.unitEmbedding (𝓞 F) F
local notation "τ₀" => canonicalIdeleNormSection F
local notation "πclass(" v ", " π ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π
local notation "unitMass(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v).real ((v).adicCompletionIntegers F).units

/-- At a pair sampled by the left side of (11.3.2.1) the two ideles have the same norm, for any
homomorphism `τ`: a principal idele and a norm-one idele have norm one. -/
private theorem sampledPair_classNorm_eq (τ : ℝ≥0ˣ →* I𝔽) (t : ℝ≥0ˣ) (ξ : Fˣ) (g : N𝔽) :
    ideleClassNorm F (QuotientGroup.mk' H𝔽 (τ t)) =
      ideleClassNorm F (QuotientGroup.mk' H𝔽 (principal ξ * g.val * τ t)) := by
  change ideleNorm F (τ t) = ideleNorm F (principal ξ * g.val * τ t)
  rw [map_mul, map_mul, (ideleNorm_spec F).2 ⟨ξ, rfl⟩, MonoidHom.mem_ker.mp g.property,
    one_mul, one_mul]

/-- At a pair sampled by the left side of (11.3.2.1), the class of the first idele times the
inverse class of the second is the inverse class of the norm-one idele `g`. -/
private theorem sampledPair_class_quotient (τ : ℝ≥0ˣ →* I𝔽) (t : ℝ≥0ˣ) (ξ : Fˣ) (g : N𝔽) :
    QuotientGroup.mk' H𝔽 (τ t) * (QuotientGroup.mk' H𝔽 (principal ξ * g.val * τ t))⁻¹ =
      (QuotientGroup.mk' H𝔽 g.val)⁻¹ := by
  have hξ : QuotientGroup.mk' H𝔽 (principal ξ) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨ξ, rfl⟩
  rw [map_mul, map_mul, hξ, one_mul, mul_inv_rev, mul_inv_cancel_left]

/-- At a pair sampled by the left side of (11.3.2.1), the convolution kernel `φ(x y⁻¹)` of a test
vanishing on the norm-one classes is zero at the pair of classes. -/
private theorem sampledPair_convolution_eq_zero (φ : 𝒟) (hφ : ∀ g : C₁, φ.val g = 0)
    (τ : ℝ≥0ˣ →* I𝔽) (t : ℝ≥0ˣ) (ξ : Fˣ) (g : N𝔽) :
    φ.val (QuotientGroup.mk' H𝔽 (τ t) * (QuotientGroup.mk' H𝔽 (principal ξ * g.val * τ t))⁻¹) =
      0 := by
  rw [sampledPair_class_quotient τ t ξ g]
  refine hφ ⟨(QuotientGroup.mk' H𝔽 g.val)⁻¹, ?_⟩
  rw [MonoidHom.mem_ker, map_inv]
  change (ideleNorm F g.val)⁻¹ = 1
  rw [MonoidHom.mem_ker.mp g.property, inv_one]

/-- Paper: Theorem 11.3.2.1, (11.3.2.1), p. 495, with Definition 10.4.3.7(2), (10.4.3.50),
pp. 473–474. For the lift (12.2.2.2) with any function `b`, every base, shell and domain `E` of
norm-one ideles, and every homomorphism `τ` (in particular every norm section), the left side of
(11.3.2.1) for a kernel `φ(x y⁻¹) − κ(x, y)` is minus the left side for `κ`, when `φ` vanishes
on the norm-one classes. The convolution part is zero at every sampled pair, so for the
geometric kernel (10.4.3.50) it contributes nothing, and (11.3.2.1) is a statement about the
spectral kernel.
Reconstruction: the printed weight (11.3.2.2) is replaced by the lift (12.2.2.2) with function
`b`, that is, by the weight `diagonalIndentationWeight H𝔽 Measure.count b`; here `b` is any real
function.
Deviation: The paper does not state this. -/
theorem sampledShell_convolution_sub (b : I𝔽 → ℝ) (φ : 𝒟) (hφ : ∀ g : C₁, φ.val g = 0)
    (S : Finset V) (k : ℕ) (τ : ℝ≥0ˣ →* I𝔽) (E : Set N𝔽) (κ : C𝔽 × C𝔽 → ℂ) :
    (∑' ξ : Fˣ, ∫ t, ∫ g in E,
        divisorialKernelDifference S k
          (diagonalIndentationLift H𝔽 Measure.count b (fun p ↦ φ.val (p.1 * p.2⁻¹) - κ p))
          (τ t, principal ξ * g.val * τ t)
        ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) =
      -(∑' ξ : Fˣ, ∫ t, ∫ g in E,
        divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b κ)
          (τ t, principal ξ * g.val * τ t)
        ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) := by
  have h (ξ : Fˣ) (t : ℝ≥0ˣ) (g : N𝔽) :
      divisorialKernelDifference S k
          (diagonalIndentationLift H𝔽 Measure.count b (fun p ↦ φ.val (p.1 * p.2⁻¹) - κ p))
          (τ t, principal ξ * g.val * τ t) =
        -divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b κ)
          (τ t, principal ξ * g.val * τ t) := by
    simp only [divisorialKernelDifference, diagonalIndentationLift, Prod.map_fst, Prod.map_snd]
    rw [sampledPair_convolution_eq_zero φ hφ τ t ξ g]
    ring
  simp_rw [h, integral_neg, tsum_neg]

/-- Paper: Theorem 11.3.2.1, (11.3.2.1), p. 495, with Definition 10.4.3.7, (10.4.3.49)–
(10.4.3.50), pp. 473–474. For the global geometric kernel `φ(x y⁻¹) − k^spec(x, y)` of the
printed statement `Printed.orbitalTracesOnPaleyWienerLevels`, when the strip tensor exists
(hypothesis `hK`), and for the lift with any function `b`, every base, shell, homomorphism `τ`
and domain, the left side of (11.3.2.1) is minus the same expression for the global spectral
kernel `k^spec` alone, when `φ` vanishes on the norm-one classes. Both kernels read
`globalStripSpectralKernel` through the coercion of its `L²` class, that is, through one
representative.
Reconstruction: the printed weight (11.3.2.2) is replaced by the lift (12.2.2.2) with function
`b`, that is, by the weight `diagonalIndentationWeight H𝔽 Measure.count b`; here `b` is any real
function.
Deviation: The paper does not state this. -/
theorem sampledShell_globalStripGeometricKernel_eq_neg (b : I𝔽 → ℝ) (S : Finset V) (k : ℕ)
    (τ : ℝ≥0ˣ →* I𝔽) (E : Set N𝔽) {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : 𝒟)
    (hφ : ∀ g : C₁, φ.val g = 0) :
    ∀ hK, (∑' ξ : Fˣ, ∫ t, ∫ g in E,
        divisorialKernelDifference S k
          (diagonalIndentationLift H𝔽 Measure.count b
            (globalStripGeometricKernel (F := F) (1 / 2) hα hs φ hK))
          (τ t, principal ξ * g.val * τ t)
        ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) =
      -(∑' ξ : Fˣ, ∫ t, ∫ g in E,
        divisorialKernelDifference S k
          (diagonalIndentationLift H𝔽 Measure.count b
            (fun p ↦ globalStripSpectralKernel (F := F) (1 / 2) hα hs φ hK p))
          (τ t, principal ξ * g.val * τ t)
        ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) :=
  fun _ ↦ sampledShell_convolution_sub b φ hφ S k τ E _

open scoped Pointwise in
/-- At every pair of idele classes, the convolution kernel of a test is eventually integrable on
the translated product sets of a Borel D′-sequence, and its averages there converge to its value
at the pair. This is the proof of `diagonal_mem_convolutionKernelRegularSet_averages` at an
arbitrary pair in place of a diagonal one. -/
private theorem convolutionKernel_dSequenceAverage {U : ℕ → Set C𝔽}
    (hU : IsDPrimeSequence (ideleClassTamagawaMeasure F) U) (hBorel : ∀ n, MeasurableSet (U n))
    (φ : 𝒟) (p : C𝔽 × C𝔽) :
    (∀ᶠ n in atTop, IntegrableOn (fun y : C𝔽 × C𝔽 ↦ φ.val (y.1 * y.2⁻¹)) (p • (U n ×ˢ U n))
      ((ideleClassTamagawaMeasure F).prod (ideleClassTamagawaMeasure F))) ∧
      Tendsto (fun n ↦ dSequenceAverage
        ((ideleClassTamagawaMeasure F).prod (ideleClassTamagawaMeasure F)) (U n ×ˢ U n)
        (fun y : C𝔽 × C𝔽 ↦ φ.val (y.1 * y.2⁻¹)) p) atTop (𝓝 (φ.val (p.1 * p.2⁻¹))) := by
  let μ : Measure C𝔽 := ideleClassTamagawaMeasure F
  let f : C𝔽 × C𝔽 → ℂ := fun y ↦ φ.val (y.1 * y.2⁻¹)
  have hg : Continuous f :=
    (continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).1 φ.property.1)).comp
      (continuous_fst.mul continuous_snd.inv)
  have rectSeq [m : MeasurableSpace (C𝔽 × C𝔽)] (hm : m = borel _)
      (η : Measure (C𝔽 × C𝔽)) [η.IsHaarMeasure]
      (hrect : ∀ v w : Set C𝔽, MeasurableSet v → MeasurableSet w →
        η (v ×ˢ w) = μ v * μ w) :
      IsDPrimeSequence η (fun n ↦ U n ×ˢ U n) := by
    subst m
    exact IsDPrimeSequence.prod hrect hU hU
  have hseq : IsDPrimeSequence (μ.prod μ) (fun n ↦ U n ×ˢ U n) :=
    rectSeq BorelSpace.measurable_eq _ (fun v w _ _ ↦ Measure.prod_prod v w)
  have hshrink {W : Set (C𝔽 × C𝔽)} (hW : W ∈ 𝓝 p) :
      ∀ᶠ n in atTop, p • (U n ×ˢ U n) ⊆ W := by
    have hpre : (fun y : C𝔽 × C𝔽 ↦ p * y) ⁻¹' W ∈ 𝓝 1 :=
      (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW)
    obtain ⟨N, hN⟩ := hseq.2 _ hpre
    filter_upwards [eventually_ge_atTop N] with n hn
    exact Set.smul_set_subset_iff.mpr fun _ hy ↦ hN (hseq.1.2.1 hn hy)
  obtain ⟨W, hW, hiW⟩ := hg.locallyIntegrable (μ := μ.prod μ) p
  have hint : ∀ᶠ n in atTop, IntegrableOn f (p • (U n ×ˢ U n)) (μ.prod μ) :=
    (hshrink hW).mono fun _ hn ↦ hiW.mono_set hn
  refine ⟨hint, ?_⟩
  change Tendsto (fun n ↦ dSequenceAverage (μ.prod μ) (U n ×ˢ U n) f p) atTop (𝓝 (f p))
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have hnear : f ⁻¹' Metric.ball (f p) (ε / 2) ∈ 𝓝 p :=
    hg.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hε))
  filter_upwards [hshrink hnear, hint] with n hn hi
  let S := p • (U n ×ˢ U n)
  have hzero : (μ.prod μ) S ≠ 0 := by
    simpa only [S, measure_smul] using (hseq.1.1 n).2.2.1.ne'
  have hfin : (μ.prod μ) S ≠ ∞ := by
    simpa only [S, measure_smul] using (hseq.1.1 n).2.2.2.ne
  have havg : (⨍ y in S, f y - f p ∂(μ.prod μ)) =
      dSequenceAverage (μ.prod μ) (U n ×ˢ U n) f p - f p := by
    change (⨍ y in S, f y - f p ∂(μ.prod μ)) = (⨍ y in S, f y ∂(μ.prod μ)) - f p
    rw [setAverage_fun_sub hi (integrableOn_const (C := f p) hfin),
      setAverage_const hzero hfin]
  rw [dist_eq_norm, ← ENNReal.ofReal_lt_ofReal_iff hε, ofReal_norm, ← havg]
  calc
    ‖⨍ y in S, f y - f p ∂(μ.prod μ)‖ₑ ≤ ⨍⁻ y in S, ‖f y - f p‖ₑ ∂(μ.prod μ) := by
      rw [setAverage_eq', setLAverage_eq']
      exact eNorm_integral_le_lintegral_eNorm _
    _ ≤ ⨍⁻ _ in S, ENNReal.ofReal (ε / 2) ∂(μ.prod μ) := by
      rw [setLAverage_eq', setLAverage_eq']
      apply lintegral_mono_ae
      have hS := (ae_restrict_mem (μ := μ.prod μ)
        (((hBorel n).prod (hBorel n)).const_smul p)).filter_mono
        (Measure.ae_smul_measure_le ((μ.prod μ) S)⁻¹)
      filter_upwards [hS] with y hy
      have hy' : dist (f y) (f p) < ε / 2 := hn hy
      rw [← ofReal_norm, ← dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal hy'.le
    _ < ENNReal.ofReal ε := by
      rw [setLAverage_const hzero hfin, ENNReal.ofReal_lt_ofReal_iff hε]
      exact half_lt_self hε

open scoped Pointwise in
/-- At a pair of idele classes where the convolution kernel vanishes, the smoothening of a
geometric kernel `φ(x y⁻¹) − κ(x, y)` is minus the smoothening of `κ`. This is the argument of
the diagonal case in `Ch12_TraceGeometric/Sec5.lean`, at an arbitrary pair. -/
private theorem dSequenceKernelSmoothening_convolution_sub {U : ℕ → Set C𝔽}
    (hU : IsDPrimeSequence (ideleClassTamagawaMeasure F) U) (hBorel : ∀ n, MeasurableSet (U n))
    (φ : 𝒟) (κ : C𝔽 × C𝔽 → ℂ) (p : C𝔽 × C𝔽) (hp : φ.val (p.1 * p.2⁻¹) = 0) :
    dSequenceKernelSmoothening (ideleClassTamagawaMeasure F) U
        (fun y ↦ φ.val (y.1 * y.2⁻¹) - κ y) p =
      -dSequenceKernelSmoothening (ideleClassTamagawaMeasure F) U κ p := by
  let μ : Measure (C𝔽 × C𝔽) :=
    (ideleClassTamagawaMeasure F).prod (ideleClassTamagawaMeasure F)
  let rects : ℕ → Set (C𝔽 × C𝔽) := fun n ↦ U n ×ˢ U n
  let f : C𝔽 × C𝔽 → ℂ := fun y ↦ φ.val (y.1 * y.2⁻¹)
  change dSequenceSmootheningOrZero μ rects (fun y ↦ f y - κ y) p =
    -dSequenceSmootheningOrZero μ rects κ p
  obtain ⟨hf, hlim⟩ := convolutionKernel_dSequenceAverage hU hBorel φ p
  change ∀ᶠ n in atTop, IntegrableOn f (p • rects n) μ at hf
  change Tendsto (fun n ↦ dSequenceAverage μ (rects n) f p) atTop (𝓝 (φ.val (p.1 * p.2⁻¹)))
    at hlim
  rw [hp] at hlim
  have hsum : Tendsto (fun n ↦
      dSequenceAverage μ (rects n) (fun y ↦ f y - κ y) p +
        dSequenceAverage μ (rects n) κ p) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa only [norm_zero] using hlim.norm)
    filter_upwards [hf] with n hn
    by_cases hκ : IntegrableOn κ (p • rects n) μ
    · change ‖(⨍ y in p • rects n, f y - κ y ∂μ) + (⨍ y in p • rects n, κ y ∂μ)‖ ≤
        ‖⨍ y in p • rects n, f y ∂μ‖
      rw [setAverage_fun_sub hn hκ, sub_add_cancel]
    · -- If the average of `κ` is undefined, both totalized averages vanish.
      have hfκ : ¬ IntegrableOn (fun y ↦ f y - κ y) (p • rects n) μ := by
        intro h
        apply hκ
        simpa only [Pi.sub_def, sub_sub_cancel] using hn.sub h
      have hzero : dSequenceAverage μ (rects n) κ p = 0 := by
        rw [dSequenceAverage, setAverage_eq, integral_undef hκ, smul_zero]
      have hsubzero : dSequenceAverage μ (rects n) (fun y ↦ f y - κ y) p = 0 := by
        rw [dSequenceAverage, setAverage_eq, integral_undef hfκ, smul_zero]
      rw [hzero, hsubzero, zero_add, norm_zero]
      exact norm_nonneg _
  by_cases hκ : p ∈ dSequenceRegularSet μ rects κ
  · obtain ⟨w, hw⟩ := hκ
    have hκreg : p ∈ dSequenceRegularSet μ rects κ := ⟨w, hw⟩
    have hsub : Tendsto (fun n ↦ dSequenceAverage μ (rects n) (fun y ↦ f y - κ y) p)
        atTop (𝓝 (-w)) := by
      simpa only [add_sub_cancel_right, zero_sub] using hsum.sub hw
    have hreg : p ∈ dSequenceRegularSet μ rects (fun y ↦ f y - κ y) := ⟨-w, hsub⟩
    simp only [dSequenceSmootheningOrZero, dite_eq_left hreg, dite_eq_left hκreg,
      dSequenceSmoothening, hsub.limUnder_eq, hw.limUnder_eq]
  · have hreg : p ∉ dSequenceRegularSet μ rects (fun y ↦ f y - κ y) := by
      rintro ⟨w, hw⟩
      apply hκ
      refine ⟨-w, ?_⟩
      simpa only [add_sub_cancel_left, zero_sub] using hsum.sub hw
    simp only [dSequenceSmootheningOrZero, dite_eq_right hreg, dite_eq_right hκ, neg_zero]

/-- Paper: Theorem 11.3.2.1, (11.3.2.1), p. 495, read with the smoothened kernel of
Definition 12.1.1.1, p. 498, and §12.1.1, p. 499, as the proof of Theorem 12.5.1.1 reads it on
p. 520 ("the smoothened geometric kernel"). The identity of `sampledShell_convolution_sub` holds
after smoothening too: for every Borel D′-sequence `U` of the idele class group, the left side of
(11.3.2.1) for the smoothening of `φ(x y⁻¹) − κ(x, y)` is minus the left side for the smoothening
of `κ`, when `φ` vanishes on the norm-one classes. The averages of the convolution kernel
converge to its value at every pair, as in the proof of Theorem 12.1.1.3(1), p. 503, and that
value is zero at the sampled pairs. On the diagonal, with `φ(1) = 0`, this is (12.1.1.23),
p. 503.
Reconstruction: the printed weight (11.3.2.2) is replaced by the lift (12.2.2.2) with function
`b`, that is, by the weight `diagonalIndentationWeight H𝔽 Measure.count b`; here `b` is any real
function.
Deviation: The paper does not state this. The D′-sequence is a hypothesis: the library
constructs none for the idele class group, and the families of §A.5.2 to which p. 498 refers
fail the D′ conditions (ERRATA F219, F220, I36). -/
theorem sampledShell_smoothening_convolution_sub (b : I𝔽 → ℝ) {U : ℕ → Set C𝔽}
    (hU : IsDPrimeSequence (ideleClassTamagawaMeasure F) U) (hBorel : ∀ n, MeasurableSet (U n))
    (φ : 𝒟) (hφ : ∀ g : C₁, φ.val g = 0) (S : Finset V) (k : ℕ) (τ : ℝ≥0ˣ →* I𝔽)
    (E : Set N𝔽) (κ : C𝔽 × C𝔽 → ℂ) :
    (∑' ξ : Fˣ, ∫ t, ∫ g in E,
        divisorialKernelDifference S k
          (diagonalIndentationLift H𝔽 Measure.count b
            (dSequenceKernelSmoothening (ideleClassTamagawaMeasure F) U
              (fun p ↦ φ.val (p.1 * p.2⁻¹) - κ p)))
          (τ t, principal ξ * g.val * τ t)
        ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) =
      -(∑' ξ : Fˣ, ∫ t, ∫ g in E,
        divisorialKernelDifference S k
          (diagonalIndentationLift H𝔽 Measure.count b
            (dSequenceKernelSmoothening (ideleClassTamagawaMeasure F) U κ))
          (τ t, principal ξ * g.val * τ t)
        ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) := by
  have h (ξ : Fˣ) (t : ℝ≥0ˣ) (g : N𝔽) :
      divisorialKernelDifference S k
          (diagonalIndentationLift H𝔽 Measure.count b
            (dSequenceKernelSmoothening (ideleClassTamagawaMeasure F) U
              (fun p ↦ φ.val (p.1 * p.2⁻¹) - κ p)))
          (τ t, principal ξ * g.val * τ t) =
        -divisorialKernelDifference S k
          (diagonalIndentationLift H𝔽 Measure.count b
            (dSequenceKernelSmoothening (ideleClassTamagawaMeasure F) U κ))
          (τ t, principal ξ * g.val * τ t) := by
    simp only [divisorialKernelDifference, diagonalIndentationLift]
    rw [dSequenceKernelSmoothening_convolution_sub hU hBorel φ κ _
      (sampledPair_convolution_eq_zero φ hφ τ t ξ g)]
    ring
  simp_rw [h, integral_neg, tsum_neg]

/-- The smoothening of Definition 12.1.1.1 depends only on the almost-everywhere class. -/
private theorem dSequenceSmootheningOrZero_congr_ae {G : Type*} [CommGroup G]
    [MeasurableSpace G] (μ : Measure G) (U : ℕ → Set G) {f f' : G → ℂ} (h : f =ᵐ[μ] f') :
    dSequenceSmootheningOrZero μ U f = dSequenceSmootheningOrZero μ U f' := by
  have havg (W : Set G) (x : G) : dSequenceAverage μ W f x = dSequenceAverage μ W f' x :=
    average_congr (ae_restrict_of_ae h)
  have hreg : dSequenceRegularSet μ U f = dSequenceRegularSet μ U f' := by
    ext y
    exact exists_congr fun l ↦ by simp only [havg]
  funext x
  unfold dSequenceSmootheningOrZero dSequenceSmoothening
  by_cases hx : x ∈ dSequenceRegularSet μ U f
  · rw [dite_eq_left hx, dite_eq_left (hreg ▸ hx)]
    simp only [havg]
  · rw [dite_eq_right hx, dite_eq_right (hreg ▸ hx)]

/-- Paper: Theorem 11.3.2.1, (11.3.2.1), p. 495, read with the smoothened kernel of
Definition 12.1.1.1, p. 498, as on p. 520. The smoothening is a limit of averages, so the left
side of (11.3.2.1) for a smoothened kernel depends only on the class of the kernel for the product
of the class measures: two kernels equal almost everywhere give the same left side, for every
sequence `U`, every lift, base, shell, homomorphism `τ` and domain.
Reconstruction: the printed weight (11.3.2.2) is replaced by the lift (12.2.2.2) with function
`b`, that is, by the weight `diagonalIndentationWeight H𝔽 Measure.count b`; here `b` is any real
function.
Deviation: The paper does not state this. -/
theorem sampledShell_smoothening_congr_ae (b : I𝔽 → ℝ) (U : ℕ → Set C𝔽) (S : Finset V) (k : ℕ)
    (τ : ℝ≥0ˣ →* I𝔽) (E : Set N𝔽) {κ κ' : C𝔽 × C𝔽 → ℂ}
    (h : κ =ᵐ[(ideleClassTamagawaMeasure F).prod (ideleClassTamagawaMeasure F)] κ') :
    (∑' ξ : Fˣ, ∫ t, ∫ g in E,
        divisorialKernelDifference S k
          (diagonalIndentationLift H𝔽 Measure.count b
            (dSequenceKernelSmoothening (ideleClassTamagawaMeasure F) U κ))
          (τ t, principal ξ * g.val * τ t)
        ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) =
      (∑' ξ : Fˣ, ∫ t, ∫ g in E,
        divisorialKernelDifference S k
          (diagonalIndentationLift H𝔽 Measure.count b
            (dSequenceKernelSmoothening (ideleClassTamagawaMeasure F) U κ'))
          (τ t, principal ξ * g.val * τ t)
        ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) := by
  have hs : dSequenceKernelSmoothening (ideleClassTamagawaMeasure F) U κ =
      dSequenceKernelSmoothening (ideleClassTamagawaMeasure F) U κ' :=
    dSequenceSmootheningOrZero_congr_ae _ _ h
  rw [hs]

/-- Paper: Theorem 11.3.2.1, (11.3.2.1), p. 495. The left side of (11.3.2.1) depends on the
kernel only through its values at pairs of idele classes of equal norm: two kernels that agree
there give the same left side, for the lift with any function `b`, every base, shell,
homomorphism `τ` and domain.
Reconstruction: the printed weight (11.3.2.2) is replaced by the lift (12.2.2.2) with function
`b`, that is, by the weight `diagonalIndentationWeight H𝔽 Measure.count b`; here `b` is any real
function.
Deviation: The paper does not state this. -/
theorem sampledShell_congr_equalNorm (b : I𝔽 → ℝ) (S : Finset V) (k : ℕ) (τ : ℝ≥0ˣ →* I𝔽)
    (E : Set N𝔽) (κ₁ κ₂ : C𝔽 × C𝔽 → ℂ)
    (h : ∀ p : C𝔽 × C𝔽, ideleClassNorm F p.1 = ideleClassNorm F p.2 → κ₁ p = κ₂ p) :
    (∑' ξ : Fˣ, ∫ t, ∫ g in E,
        divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b κ₁)
          (τ t, principal ξ * g.val * τ t)
        ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) =
      (∑' ξ : Fˣ, ∫ t, ∫ g in E,
        divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b κ₂)
          (τ t, principal ξ * g.val * τ t)
        ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) := by
  have hpt (ξ : Fˣ) (t : ℝ≥0ˣ) (g : N𝔽) :
      divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b κ₁)
          (τ t, principal ξ * g.val * τ t) =
        divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b κ₂)
          (τ t, principal ξ * g.val * τ t) := by
    simp only [divisorialKernelDifference, diagonalIndentationLift]
    rw [h _ (sampledPair_classNorm_eq τ t ξ g)]
  simp_rw [hpt]

/-- The measure `dt/t` on the positive reals has no atoms. -/
private theorem positiveRealHaar_singleton (r : ℝ≥0ˣ) : positiveRealHaar {r} = 0 := by
  let e (x : ℝ) : ℝ≥0ˣ := Units.mk0 (Real.exp x).toNNReal (by positivity)
  have he : Measurable e :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hL : MeasurableSet {t : ℝ≥0ˣ | ((t.val : ℝ≥0) : ℝ) = ((r.val : ℝ≥0) : ℝ)} :=
    measurableSet_eq_fun (NNReal.continuous_coe.measurable.comp MeasurableSpace.le_map_comap)
      measurable_const
  refine measure_mono_null (t := {t : ℝ≥0ˣ | ((t.val : ℝ≥0) : ℝ) = ((r.val : ℝ≥0) : ℝ)})
    (fun t ht ↦ by rw [Set.mem_singleton_iff.mp ht]; rfl) ?_
  change (volume.map e) _ = 0
  rw [Measure.map_apply he hL]
  refine measure_mono_null (t := {Real.log ((r.val : ℝ≥0) : ℝ)}) (fun x hx ↦ ?_)
    Real.volume_singleton
  have hx' : ((Real.exp x).toNNReal : ℝ) = ((r.val : ℝ≥0) : ℝ) := hx
  rw [Real.coe_toNNReal _ (Real.exp_pos x).le] at hx'
  rw [Set.mem_singleton_iff, ← hx', Real.log_exp]

/-- Paper: Definition A.3.2.1, pp. 559–560, through the decomposition of the class measure
along a norm section (`classTamagawa_normProduct`). Every level set of the idele class norm is
a null set of the idele class group.
Deviation: The paper does not state this. -/
theorem ideleClassTamagawaMeasure_normLevel_eq_zero (r : ℝ≥0ˣ) :
    ideleClassTamagawaMeasure F {x : C𝔽 | ideleClassNorm F x = r} = 0 := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let σ : ℝ≥0ˣ → C𝔽 := fun t ↦ QuotientGroup.mk (τ₀ t)
  have hσ : Continuous σ := continuous_quotient_mk'.comp (canonicalIdeleNormSection_continuous F)
  have hr : Function.RightInverse σ (ideleClassNorm F) :=
    canonicalIdeleNormSection_rightInverse F
  have hj : Continuous (fun p : ℝ≥0ˣ × C₁ ↦ σ p.1 * p.2.val) :=
    (hσ.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hL : MeasurableSet {x : C𝔽 | ideleClassNorm F x = r} :=
    (isClosed_eq (isProperMap_ideleClassNorm F).continuous continuous_const).measurableSet
  rw [← classTamagawa_normProduct σ hσ hr, Measure.map_apply hj.measurable hL]
  have hpre : (fun p : ℝ≥0ˣ × C₁ ↦ σ p.1 * p.2.val) ⁻¹' {x : C𝔽 | ideleClassNorm F x = r} =
      {r} ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_singleton_iff,
      Set.mem_univ, and_true]
    rw [map_mul, hr p.1, MonoidHom.mem_ker.mp p.2.property, mul_one]
  rw [hpre, Measure.prod_prod, positiveRealHaar_singleton r, zero_mul]

/-- Paper: Theorem 11.3.2.1, (11.3.2.1), p. 495. The pairs of idele classes of equal norm, at
which the left side of (11.3.2.1) reads a kernel, form a null set of `C_F × C_F`. They contain
the diagonal, of which §12.1.1, p. 498, says that it is "a null set with respect to the product
measure".
Deviation: The paper does not state this. -/
theorem ideleClassTamagawaMeasure_prod_equalNorm_eq_zero :
    ((ideleClassTamagawaMeasure F).prod (ideleClassTamagawaMeasure F))
      {p : C𝔽 × C𝔽 | ideleClassNorm F p.1 = ideleClassNorm F p.2} = 0 := by
  have hZ : MeasurableSet {p : C𝔽 × C𝔽 | ideleClassNorm F p.1 = ideleClassNorm F p.2} :=
    (isClosed_eq ((isProperMap_ideleClassNorm F).continuous.comp continuous_fst)
      ((isProperMap_ideleClassNorm F).continuous.comp continuous_snd)).measurableSet
  rw [Measure.prod_apply hZ]
  have hx (x : C𝔽) : Prod.mk x ⁻¹' {p : C𝔽 × C𝔽 | ideleClassNorm F p.1 = ideleClassNorm F p.2} =
      {y : C𝔽 | ideleClassNorm F y = ideleClassNorm F x} := by
    ext y
    exact eq_comm
  simp_rw [hx, ideleClassTamagawaMeasure_normLevel_eq_zero, lintegral_zero]

/-- Paper: Definition 10.4.3.7(1), (10.4.3.49), p. 473, which gives the spectral kernel as a
measurable function, from a representative of a Hilbert–Schmidt kernel (Theorem 10.4.3.6(2),
p. 473). A kernel changed only at pairs of idele classes of equal norm is the same kernel almost
everywhere, for the product of any two s-finite measures absolutely continuous with respect to
the class measure. This covers the weighted measures of the Hilbert–Schmidt kernels of §10.4,
which have densities with respect to the class measure and on whose `L²` space
`globalStripSpectralKernel` is a class.
Deviation: The paper does not state this. -/
theorem ae_eq_of_eq_off_equalNorm (κ κ' : C𝔽 × C𝔽 → ℂ)
    (h : ∀ p : C𝔽 × C𝔽, ideleClassNorm F p.1 ≠ ideleClassNorm F p.2 → κ' p = κ p)
    {ν ν' : Measure C𝔽} [SFinite ν] [SFinite ν'] (hν : ν ≪ ideleClassTamagawaMeasure F)
    (hν' : ν' ≪ ideleClassTamagawaMeasure F) :
    κ' =ᵐ[ν.prod ν'] κ := by
  have hnull := (hν.prod hν') (ideleClassTamagawaMeasure_prod_equalNorm_eq_zero (F := F))
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with p hp using h p hp

/-- Paper: Theorem 11.3.2.1, (11.3.2.1), p. 495, with Definition 10.4.3.7, pp. 473–474. For every
kernel `κ`, let `κ₀` equal `κ` off the pairs of equal norm and zero at them; it is equal to `κ`
almost everywhere (`ae_eq_of_eq_off_equalNorm`). With the geometric kernel
`φ(x y⁻¹) − κ₀(x, y)`, for a test vanishing on the norm-one classes, the left side of (11.3.2.1)
is zero, for the lift with any function `b`, every base, shell, homomorphism `τ` and domain. So
with `κ₀` in place of `κ`, (11.3.2.1) holds exactly when its right side is zero.
Reconstruction: the printed weight (11.3.2.2) is replaced by the lift (12.2.2.2) with function
`b`, that is, by the weight `diagonalIndentationWeight H𝔽 Measure.count b`; here `b` is any real
function.
Deviation: The paper does not state this. -/
theorem sampledShell_equalNormRepresentative_eq_zero (b : I𝔽 → ℝ) (φ : 𝒟)
    (hφ : ∀ g : C₁, φ.val g = 0) (S : Finset V) (k : ℕ) (τ : ℝ≥0ˣ →* I𝔽) (E : Set N𝔽)
    (κ : C𝔽 × C𝔽 → ℂ) :
    (∑' ξ : Fˣ, ∫ t, ∫ g in E,
        divisorialKernelDifference S k
          (diagonalIndentationLift H𝔽 Measure.count b (fun p ↦ φ.val (p.1 * p.2⁻¹) -
            if ideleClassNorm F p.1 = ideleClassNorm F p.2 then 0 else κ p))
          (τ t, principal ξ * g.val * τ t)
        ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) = 0 := by
  rw [sampledShell_convolution_sub b φ hφ S k τ E, sampledShell_congr_equalNorm b S k τ E _
    (fun _ ↦ 0) (fun p hp ↦ ite_eq_left hp)]
  have hzero (ξ : Fˣ) (t : ℝ≥0ˣ) (g : N𝔽) :
      divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b fun _ ↦ 0)
        (τ t, principal ξ * g.val * τ t) = 0 := by
    simp only [divisorialKernelDifference, diagonalIndentationLift, mul_zero]
  simp_rw [hzero, integral_zero, tsum_zero, neg_zero]

/-- Paper: Theorem 11.3.2.1, (11.3.2.1), p. 495, with Definition 10.4.3.7, (10.4.3.49)–
(10.4.3.50), pp. 473–474. Read through the values of a representative of the spectral kernel,
(11.3.2.1) cannot hold for every representative. At every finite place and uniformizer there is
a radial test supported above norm one with the following property. For every kernel `κ`, in
particular every representative of the spectral kernel of that test when it exists, the kernel
`κ₀` equal to `κ` off the pairs of equal norm and zero at them is equal to `κ` almost everywhere,
for the product of any two s-finite measures absolutely continuous with respect to the class
measure. In Lean the spectral kernel exists when the strip tensor `hK` of
`globalStripSpectralKernel` does; for `0 < α`, `3 ≤ s` and a test vanishing on the norm-one
classes, at twist `1 / 2`, that is the open statement
`Isolated.exists_projectiveKernel_stripTestAction_spectralProjection`.
With the geometric kernel `φ(x y⁻¹) − κ₀(x, y)` the two sides of (11.3.2.1) differ for the lift
with any function `b` (in particular every normalized indentation, with no invariance assumed),
and every base, shell, homomorphism `τ` and domain: the left side is zero
(`sampledShell_equalNormRepresentative_eq_zero`) and the right side is `log q_v / μ_v(O_v^×)`.
This concerns readings through the values of a representative, such as the coercion that
`globalStripGeometricKernel` evaluates. The smoothening of Definition 12.1.1.1 does not see the
change from `κ` to `κ₀` (`sampledShell_smoothening_congr_ae`).
Reconstruction: the printed weight (11.3.2.2) is replaced by the lift (12.2.2.2) with function
`b`, that is, by the weight `diagonalIndentationWeight H𝔽 Measure.count b`; here `b` is any real
function.
Deviation: The paper does not state this. It complements `orbitalShell_invariantLift_ne_poisson`,
which holds for every kernel but only for normalized lifts with dilation-invariant weight, the
canonical norm section and large saturated bases. -/
theorem sampledShell_equalNormRepresentative_ne_poisson (v : V) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v.IsUniformizer (π : v.adicCompletion F)) :
    ∃ φ : 𝒟, tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)} ∧
      (∀ x y : C𝔽, ideleClassNorm F x = ideleClassNorm F y → φ.val x = φ.val y) ∧
      ∀ κ : C𝔽 × C𝔽 → ℂ,
        (∀ (ν ν' : Measure C𝔽) [SFinite ν] [SFinite ν'], ν ≪ ideleClassTamagawaMeasure F →
          ν' ≪ ideleClassTamagawaMeasure F →
          (fun p ↦ if ideleClassNorm F p.1 = ideleClassNorm F p.2 then 0 else κ p) =ᵐ[ν.prod ν']
            κ) ∧
        ∀ (b : I𝔽 → ℝ) (S : Finset V) (k : ℕ) (τ : ℝ≥0ˣ →* I𝔽) (E : Set N𝔽),
          (∑' ξ : Fˣ, ∫ t, ∫ g in E,
              divisorialKernelDifference S k
                (diagonalIndentationLift H𝔽 Measure.count b (fun p ↦ φ.val (p.1 * p.2⁻¹) -
                  if ideleClassNorm F p.1 = ideleClassNorm F p.2 then 0 else κ p))
                (τ t, principal ξ * g.val * τ t)
              ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) ≠
            (Real.log (v.asIdeal.absNorm : ℝ) / unitMass(v) : ℂ) *
              ∑' n : ℤ, φ.val (πclass(v, π) ^ n) := by
  obtain ⟨φ, h1, h2, h3⟩ := orbitalShell_invariantLift_ne_poisson_test v π hπ
  have hφ : ∀ g : C₁, φ.val g = 0 := fun g ↦ image_eq_zero_of_notMem_tsupport fun hg ↦ by
    have hg' : (1 : ℝ) < ((ideleClassNorm F g.val).val : ℝ) := h1 hg
    rw [MonoidHom.mem_ker.mp g.property] at hg'
    simp at hg'
  refine ⟨φ, h1, h2, fun κ ↦ ⟨?_, fun b S k τ E ↦ ?_⟩⟩
  · intro ν ν' _ _ hν hν'
    exact ae_eq_of_eq_off_equalNorm κ _ (fun p hp ↦ ite_eq_right hp) hν hν'
  rw [sampledShell_equalNormRepresentative_eq_zero b φ hφ S k τ E κ, h3, mul_one]
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  exact (div_ne_zero (Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne')
    (Complex.ofReal_ne_zero.mpr (orbitalShell_invariantLift_ne_poisson_mass v))).symm

end EqualNormSampling

end RiemannMasullo.Isolated
