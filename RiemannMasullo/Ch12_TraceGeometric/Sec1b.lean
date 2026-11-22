module

public import RiemannMasullo.Ch12_TraceGeometric.Sec1a
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
import all RiemannMasullo.Ch10_TraceSpectral.Sec1

/-!
# Localization along the global diagonal

Masullo, Theorem 12.1.1.3 and Remark 12.1.1.4, pp. 502–504. The product averages
use Haar measure and a chosen Borel D′-sequence on the idele class group. The
operators whose traces are computed act on the weighted Sobolev space.

The kernels are those of Definition 10.4.3.2, the case `I = {0}`, which in Lean
are `globalLineSpectralKernel` and `globalLineGeometricKernel`: they belong to
spectral projection after convolution, `P^spec_a ∘ A(φ)`, the operator of
(12.1.1.21). The strip kernels of Definition 10.4.3.7 belong to convolution after
projection and are not used here.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 900000

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "W(" s ")" => CompactIntervalSobolev μ𝔽 logNorm (-(0 : ℝ)) 0 s
local notation "hline" => (le_refl (0 : ℝ))
local notation "hbase" => ((neg_nonpos.mpr hline).trans hline)
local notation "hs₀(" hs ")" => (le_trans (by norm_num : (0 : ℝ) ≤ 3) hs)
local notation "hs₁(" hs ")" => (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hs)
local notation "convKernel(" φ ")" =>
  (fun p : C𝔽 × C𝔽 ↦ (φ : BruhatCompactSupport C𝔽).val (p.1 * p.2⁻¹))
local notation "innerBand(" Λ ", " ε ")" => (0 < Λ⁻¹ + ε ∧ Λ⁻¹ + ε < Λ - ε)

-- TODO(paper-gap): The printed standard sequence on the idele class group
-- need not shrink to the identity. Use a Borel D′-sequence as in §12.1a.
variable {U : ℕ → Set (IdeleClassGroup (𝓞 F) F)}
  (hU : IsDPrimeSequence (ideleClassTamagawaMeasure F) U) (hBorel : ∀ n, MeasurableSet (U n))

local notation "regular(" k ")" =>
  dSequenceRegularSet ((μ𝔽).prod μ𝔽) (fun n ↦ U n ×ˢ U n) k
local notation "diagonal(" k ")" => (fun x ↦ dSequenceKernelSmoothening μ𝔽 U k (x, x))

include hU hBorel

/-- Paper: Theorem 12.1.1.3(1), p. 502. The diagonal points of the convolution
kernel are regular for the Haar product averages.
Deviation: A valid Borel D′-sequence is explicit throughout. -/
theorem diagonal_mem_convolutionKernelRegularSet (φ : BruhatCompactSupport C𝔽) (x : C𝔽) :
    (x, x) ∈ regular(convKernel(φ)) := by sorry

section GlobalKernels

variable (a : ℝ) {s : ℝ} (hs : 3 ≤ s)
  (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))

local notation "Tspec" => (spectralProjection (F := F) a hline hs₀(hs)).comp
  (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ hbase hs₀(hs) φ)
local notation "Tgeom(" hρ ")" => geometricTruncatedConvolution (F := F) a hline hs₀(hs) hρ φ

local notation "kspec" =>
  (globalLineSpectralKernel (F := F) a hs₁(hs) φ : C𝔽 × C𝔽 → ℂ)
local notation "kgeom" => globalLineGeometricKernel (F := F) a hs₁(hs) φ

-- TODO(paper-gap): On p. 503 the proof applies the weighted L² trace theorem
-- to the Haar kernels directly. The actual Hilbert-Schmidt representatives
-- in Theorem 10.4.3.4 carry the reciprocal input weight. Its effect on the
-- diagonal smoothening must be justified for Haar-almost every center.

/-- Paper: Theorem 12.1.1.3(1), p. 502. The diagonal of the global spectral
kernel is regular for Haar-almost every center.
Deviation: The kernel is the mixed-weight class of Definition 10.4.3.2 in Lean,
whose Haar integral gives spectral projection after convolution. Regularity does
not depend on the representative of that class. -/
theorem ae_diagonal_mem_globalLineSpectralKernelRegularSet (_ha : 0 < a) :
    ∀ᵐ x ∂μ𝔽, (x, x) ∈ regular(kspec) := by sorry

/-- Paper: Theorem 12.1.1.3(1), p. 502. The diagonal of the global geometric
kernel is regular for Haar-almost every center. -/
theorem ae_diagonal_mem_globalLineGeometricKernelRegularSet (_ha : 0 < a) :
    ∀ᵐ x ∂μ𝔽, (x, x) ∈ regular(kgeom) := by sorry

/-- Paper: Theorem 12.1.1.3(2), p. 502. In (12.1.1.20), geometric
truncation after convolution is trace class. Its trace is the Haar integral
of the cutoff times the smoothened geometric diagonal.
Deviation: The cutoff is any real cutoff of Definition 9.3.3.1, smooth or not,
as Theorem 12.1.1.2(2) allows bounded symbols; this is the form the limit
(12.1.1.22) and the sharp band of Remark 12.1.1.4 use. Absolute integrability
of the trace integrand is explicit. -/
theorem geometricTruncatedConvolution_trace_eq_integral_globalDiagonal (_ha : 0 < a)
    {Λ ε : ℝ} {ρ : C𝔽 → ℝ} (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (_hband : innerBand(Λ, ε)) :
    let T := Tgeom(hρ)
    ∃ hT : IsNuclearOperator T,
      Integrable (fun x ↦ (ρ x : ℂ) * diagonal(kgeom) x) μ𝔽 ∧
      hilbertTrace (H := W(s)) ⟨T, hT⟩ =
        ∫ x, (ρ x : ℂ) * diagonal(kgeom) x ∂μ𝔽 := by sorry

/-- Paper: Theorem 12.1.1.3(2), p. 503. In (12.1.1.21), spectral
projection after convolution is trace class. Its trace is the Haar integral
of the smoothened spectral diagonal.
Deviation: Absolute integrability of the smoothened diagonal is explicit. -/
theorem spectralProjection_convolution_trace_eq_integral_globalDiagonal (_ha : 0 < a) :
    let T := Tspec
    ∃ hT : IsNuclearOperator T,
      Integrable diagonal(kspec) μ𝔽 ∧
      hilbertTrace (H := W(s)) ⟨T, hT⟩ = ∫ x, diagonal(kspec) x ∂μ𝔽 := by sorry

-- TODO(paper-gap): The citation of Theorem 10.4.3.1(4) for integrability
-- points to an enumeration condition. Theorem 10.4.3.4(4), cited in the
-- following remark for the same assertion, has no part (4).

/-- Paper: Theorem 12.1.1.3(3), p. 503. When the test vanishes at the
identity, the smoothened geometric diagonal is absolutely Haar integrable. -/
theorem integrable_globalLineGeometricKernel_diagonal (_ha : 0 < a) (_hφ : φ.val 1 = 0) :
    Integrable diagonal(kgeom) μ𝔽 := by sorry

/-- Paper: Theorem 12.1.1.3(3), p. 503. In (12.1.1.22), as the radius
tends to infinity and the width times the radius tends to zero, the
geometric truncation traces tend to the Haar mass of the smoothened diagonal.
Deviation: A filter represents the joint limit, with real cutoffs and their
traces specified eventually. The same limit holds for the sharp band in
Remark 12.1.1.4. -/
theorem geometricTruncatedConvolution_trace_tendsto_integral_globalDiagonal (_ha : 0 < a)
    (_hφ : φ.val 1 = 0) {ι : Type*} {l : Filter ι} (Λ ε : ι → ℝ) (ρ : ι → C𝔽 → ℝ)
    (_hΛ : Tendsto Λ l atTop) (_hε : Tendsto (fun i ↦ ε i * Λ i) l (𝓝 0))
    (_hρ : ∀ᶠ i in l, IsModulatedCutoff m𝔽 (Λ i) (ε i) (ρ i) ∧ innerBand(Λ i, ε i)) :
    ∃ traces : ι → ℂ,
      (∀ᶠ i in l, ∃ hcut : IsModulatedCutoff m𝔽 (Λ i) (ε i) (ρ i),
        let T := Tgeom(hcut)
        ∃ hT : IsNuclearOperator T, traces i = hilbertTrace (H := W(s)) ⟨T, hT⟩) ∧
      Tendsto traces l (𝓝 (∫ x, diagonal(kgeom) x ∂μ𝔽)) := by sorry

/-- Paper: (12.1.1.23), p. 503. If the test vanishes at the identity, the
smoothened geometric diagonal is the negative of the spectral diagonal.
The smoothening uses the zero extension from Definition 12.1.1.1. -/
theorem globalLineGeometricKernel_diagonal_eq_neg_spectral (_hφ : φ.val 1 = 0) (x : C𝔽) :
    diagonal(kgeom) x = -diagonal(kspec) x := by sorry

/-- Paper: (12.1.1.24), p. 503. If the test vanishes at the identity, the
cutoff integrals of the smoothened geometric diagonal converge to its full Haar integral.
Deviation: A filter expresses the joint limit for the radius and width. The
plateau estimate also applies to the two-sided absolute cutoff of Remark 12.1.1.4. -/
theorem tendsto_integral_cutoff_globalLineGeometricKernel_diagonal (_ha : 0 < a)
    (_hφ : φ.val 1 = 0) {ι : Type*} {l : Filter ι} (Λ ε : ι → ℝ) (ρ : ι → C𝔽 → ℝ)
    (_hΛ : Tendsto Λ l atTop) (_hε : Tendsto (fun i ↦ ε i * Λ i) l (𝓝 0))
    (_hρ : ∀ᶠ i in l, IsModulatedCutoff m𝔽 (Λ i) (ε i) (ρ i) ∧ innerBand(Λ i, ε i)) :
    Tendsto (fun i ↦ ∫ x, (ρ i x : ℂ) * diagonal(kgeom) x ∂μ𝔽) l
      (𝓝 (∫ x, diagonal(kgeom) x ∂μ𝔽)) := by sorry

-- TODO(paper-gap): The end of the proof cites (10.4.3.31) as its conclusion.
-- The intended conclusion is (12.1.1.22). The geometric kernel formula is
-- (10.4.3.31), while (10.4.3.32) starts a computation of the kernel action.

/-- Paper: Remark 12.1.1.4, pp. 503–504. For a test vanishing at the identity,
the sharp and smooth cutoff masses of the geometric diagonal differ by a
quantity tending to zero in the joint limit of (12.1.1.22). -/
theorem tendsto_absolute_sub_smooth_globalLineGeometricKernel_diagonal (_ha : 0 < a)
    (_hφ : φ.val 1 = 0)
    {ι : Type*} {l : Filter ι} (Λ ε : ι → ℝ) (ρ : ι → C𝔽 → ℝ)
    (_hΛ : Tendsto Λ l atTop) (_hε : Tendsto (fun i ↦ ε i * Λ i) l (𝓝 0))
    (_hρ : ∀ᶠ i in l, IsSmoothModulatedCutoff m𝔽 (Λ i) (ε i) (ρ i) ∧ innerBand(Λ i, ε i)) :
    Tendsto (fun i ↦ (∫ x, (modulatedAbsoluteCutoff m𝔽 (Icc (Λ i)⁻¹ (Λ i)) x : ℂ) *
        diagonal(kgeom) x ∂μ𝔽) - ∫ x, (ρ i x : ℂ) * diagonal(kgeom) x ∂μ𝔽) l (𝓝 0) := by sorry

local notation "wline" =>
  (fun g : C𝔽 ↦ intervalSobolevDensity (-(0 : ℝ)) 0 s (logNorm g))
local notation "νline" => ((μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (wline g)))

omit hU hBorel in
/-- Paper: Remark 12.1.1.4, p. 503. The spectral kernel divided by its input
weight is square integrable for the positive Sobolev measure in both variables.
Deviation: The remark asserts the opposite; the square integrability is
Theorem 10.4.3.4(2). The kernel of `P^geom_a ∘ A(φ)`, which the remark is
about, is `k^geom`; see `globalLineGeometricKernel_weighted_not_memLp`. -/
theorem globalLineSpectralKernel_weighted_memLp (ha : 0 < a) :
    MemLp (fun p : C𝔽 × C𝔽 ↦ ((wline p.2)⁻¹ : ℝ) • kspec p) 2 ((νline).prod νline) :=
  (spectralLineKernel_hilbertSchmidt (F := F) a hs₁(hs) φ ha).1

omit hU hBorel in
/-- Paper: Remark 12.1.1.4, p. 503. For a nonzero test vanishing at the identity,
the geometric kernel divided by its input weight is not square integrable for
the positive Sobolev measure in both variables.
Deviation: The print writes `k^spec` here, for which the claim is false
(`Sec1b_Printed.lean`); the kernel of `P^geom_a ∘ A(φ)` is `k^geom`. The zero
test must be excluded. -/
theorem globalLineGeometricKernel_weighted_not_memLp
    (_ha : 0 < a) (_hφ : φ.val 1 = 0) (_hne : φ ≠ 0) :
    ¬ MemLp (fun p : C𝔽 × C𝔽 ↦ ((wline p.2)⁻¹ : ℝ) • kgeom p) 2 ((νline).prod νline) := by
  sorry

omit hU hBorel in
/-- Paper: Remark 12.1.1.4, p. 503. Convolution by a nonzero test is not
Hilbert–Schmidt on the weighted Sobolev space, hence not nuclear.
Deviation: The zero test must be excluded. -/
theorem hardySobolevTestAction_not_hilbertSchmidt (_hne : φ ≠ 0) :
    hardySobolevTestAction μ𝔽 m𝔽 _ _ _ hbase hs₀(hs) φ ∉
      hilbertSchmidtOperators (W(s)) (W(s)) := by sorry

omit hU hBorel in
/-- Paper: Remark 12.1.1.4, pp. 503–504. For a nonzero test vanishing at the
identity, untruncated geometric convolution fails to be Hilbert–Schmidt.
Deviation: The obstruction comes from the full convolution kernel, and the
zero test must be excluded. -/
theorem geometricProjection_convolution_not_hilbertSchmidt
    (_ha : 0 < a) (_hφ : φ.val 1 = 0) (_hne : φ ≠ 0) :
    (geometricProjection (F := F) a hline hs₀(hs)).comp
      (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ hbase hs₀(hs) φ) ∉
        hilbertSchmidtOperators (W(s)) (W(s)) := by sorry

-- TODO(later): needs §12.5. The proof of Theorem 12.5.1.1, p. 520, integrates the
-- smoothened strip kernel of Definition 10.4.3.7 along the diagonal. The paper
-- states (12.1.1.21)–(12.1.1.23) for the line kernels only.

end GlobalKernels

end RiemannMasullo
