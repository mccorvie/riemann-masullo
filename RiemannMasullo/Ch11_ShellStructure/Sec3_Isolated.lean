module

public import RiemannMasullo.Ch11_ShellStructure.Sec3
public import RiemannMasullo.Ch11_ShellStructure.Sec3_Indentation

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

end RiemannMasullo.Isolated
