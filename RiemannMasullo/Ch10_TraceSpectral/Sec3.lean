module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import RiemannMasullo.AppC_LCTVS.Sec3a_part2
public import RiemannMasullo.Ch09_HardySobolev.Sec3
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import all RiemannMasullo.Ch10_TraceSpectral.Sec1

/-!
# Spectral nuclearity

Masullo, §10.3, pp. 447–455. Convolution acts on the spectral Sobolev quotients
from §10.2. The trace formulas use the strict boundary multiplicity from that
section and the integrated left-translation action from §9.3.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

section StrongNuclearity

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

/-- Paper: §10.3, p. 447. A strongly nuclear operator is an operator-norm sum
of rank-one terms with unit-ball vectors and functionals and rapidly decreasing
coefficients.
Deviation: The name is kept apart from `IsStronglyNuclearOperator` of §7.4
(Theorem 7.4.1.1(2), pp. 366–367), which is stated for endomorphisms of a locally
convex space through a nuclear presentation. This one is for maps between normed spaces. -/
def IsStronglyNuclearBanachOperator (A : E →L[ℂ] G) : Prop :=
  ∃ (c : ℕ → ℂ) (Λ : ℕ → StrongDual ℂ E) (y : ℕ → G),
    (∀ n, ‖Λ n‖ ≤ 1 ∧ ‖y n‖ ≤ 1) ∧
    (∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℂ) ^ k * c n) atTop (𝓝 0)) ∧
    HasSum (fun n ↦ c n • (Λ n).smulRight (y n)) A

/-- Paper: §10.3, p. 447. A rank-one operator has a strongly nuclear expansion
using a single coefficient after normalizing the factors.
Deviation: Sanity check for the strongly nuclear condition. -/
theorem isStronglyNuclearBanachOperator_smulRight (Λ : StrongDual ℂ E) (y : G) :
    IsStronglyNuclearBanachOperator (Λ.smulRight y) := by sorry

/-- Paper: §10.3, p. 448. Strong nuclearity implies nuclearity. -/
theorem IsStronglyNuclearBanachOperator.isNuclearOperator [CompleteSpace E]
    {A : E →L[ℂ] G} (_hA : IsStronglyNuclearBanachOperator A) : IsNuclearOperator A := by sorry

end StrongNuclearity

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "W(" l ", " r ", " s ")" =>
  CompactIntervalSobolev μ𝔽 (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ)) l r s
local notation "Θ(" a ", " hI ", " hs ")" => globalThetaSobolev F a hI hs
local notation "Q(" a ", " hI ", " hs ")" => spectralSobolevQuotient F a hI hs
local notation "Qω(" a ", " hI ", " hs ", " ω ")" =>
  spectralSobolevIsotypeQuotient F a hI hs ω
local notation "ρ(" l ", " r ", " s ", " hI ", " hs ")" =>
  (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).comp (ideleClassNorm F).ker.subtype
local notation "Wω(" hI ", " hs ", " ω ")" => actionIsotype (ρ(_, _, _, hI, hs)) ω
local notation "testAction(" l ", " r ", " s ", " hI ", " hs ")" =>
  hardySobolevTestAction μ𝔽 m𝔽 l r s hI hs
local notation "h₀" => le_rfl (a := (0 : ℝ))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "M(" φ ", " χ ", " z ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽
    (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (F := F) χ z)

-- Select the norm topology directly when using the locally convex nuclear ideal.
local instance instSpectralQuotientPolynormableSec3 (a : ℝ) {l r s : ℝ}
    (hI : l ≤ r) (hs : 0 ≤ s) : PolynormableSpace ℂ Q(a, hI, hs) :=
  (norm_withSeminorms ℂ Q(a, hI, hs)).toPolynormableSpace

section Convolution

variable (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)

/-- Paper: (10.3.1.2), p. 448, and (10.3.2.2), p. 454. Convolution with a
test preserves the closed weighted theta subspace, so it descends to the quotient. -/
theorem hardySobolevTestAction_preserves_globalTheta (φ : BruhatCompactSupport C𝔽) :
    Θ(a, hI, hs) ≤ ((Θ(a, hI, hs)).mkQL.comp (testAction(l, r, s, hI, hs) φ)).ker := by sorry

/-- Paper: (10.3.1.2), p. 448, and (10.3.2.2), p. 454. The spectral convolution
operator is the descended Hardy–Sobolev test action. -/
def spectralConvolution (φ : BruhatCompactSupport C𝔽) : Q(a, hI, hs) →L[ℂ] Q(a, hI, hs) :=
  (Θ(a, hI, hs)).liftQL ((Θ(a, hI, hs)).mkQL.comp (testAction(l, r, s, hI, hs) φ))
    (hardySobolevTestAction_preserves_globalTheta (F := F) a hI hs φ)

/-- Paper: (10.3.1.2), p. 448, and (10.3.2.2), p. 454. On a representative,
spectral convolution takes the quotient class of its ambient convolution. -/
theorem spectralConvolution_mkQ (φ : BruhatCompactSupport C𝔽) (v : W(l, r, s)) :
    spectralConvolution (F := F) a hI hs φ ((Θ(a, hI, hs)).mkQ v) =
      (Θ(a, hI, hs)).mkQ (testAction(l, r, s, hI, hs) φ v) := by sorry

/-- Paper: (10.3.1.2), p. 448, and (10.3.2.2), p. 454. The descended action
is complex linear in the test. -/
theorem spectralConvolution_isLinear :
    IsLinearMap ℂ (spectralConvolution (F := F) a hI hs) := by sorry

/-- Paper: Theorems 10.3.1.1(3), p. 449, and 10.3.2.1(3), p. 454.
Convolution preserves the ambient norm-one isotype. -/
theorem hardySobolevTestAction_preserves_spectralIsotype (ω : PontryaginDual C₁)
    (φ : BruhatCompactSupport C𝔽) :
    ∀ v ∈ Wω(hI, hs, ω), testAction(l, r, s, hI, hs) φ v ∈ Wω(hI, hs, ω) := by sorry

local notation "Nω(" ω ")" => (Θ(a, hI, hs)).comap (Wω(hI, hs, ω)).subtype
local notation "Aω(" ω ", " φ ")" =>
  (ContinuousLinearMap.restrict (testAction(l, r, s, hI, hs) φ)
    (hardySobolevTestAction_preserves_spectralIsotype (F := F) hI hs ω φ))

/-- Paper: Theorems 10.3.1.1(3), p. 449, and 10.3.2.1(3), p. 454.
Convolution preserves the theta intersection in each norm-one isotype. -/
theorem hardySobolevTestAction_preserves_spectralIsotypeTheta (ω : PontryaginDual C₁)
    (φ : BruhatCompactSupport C𝔽) :
    Nω(ω) ≤ ((Nω(ω)).mkQL.comp Aω(ω, φ)).ker := by sorry

/-- Paper: Theorems 10.3.1.1(3), p. 449, and 10.3.2.1(3), p. 454.
The isotype operator descends ambient convolution restricted to that isotype. -/
def spectralIsotypeConvolution (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽) :
    Qω(a, hI, hs, ω) →L[ℂ] Qω(a, hI, hs, ω) :=
  (Nω(ω)).liftQL ((Nω(ω)).mkQL.comp Aω(ω, φ))
    (hardySobolevTestAction_preserves_spectralIsotypeTheta (F := F) a hI hs ω φ)

/-- Paper: Theorems 10.3.1.1(3), p. 449, and 10.3.2.1(3), p. 454.
On an isotypic representative the restricted operator takes the class of its convolution. -/
theorem spectralIsotypeConvolution_mkQ (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (v : Wω(hI, hs, ω)) :
    spectralIsotypeConvolution (F := F) a hI hs ω φ ((Nω(ω)).mkQ v) =
      (Nω(ω)).mkQ (Aω(ω, φ) v) := by sorry

/-- Paper: Theorems 10.3.1.1(3), p. 449, and 10.3.2.1(3), p. 454.
The full quotient action of an isotypic test has range in the corresponding quotient isotype.
Deviation: For left translation φ(x) ↦ φ(k⁻¹x), the weight is ω as an
eigencharacter. Equivalently the pointwise covariance is φ(kx) = ω⁻¹(k)φ(x). -/
theorem spectralConvolution_range_isotype (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    range (spectralConvolution (F := F) a hI hs φ) ⊆
      range (fun v : Wω(hI, hs, ω) ↦ (Θ(a, hI, hs)).mkQ v.val) := by sorry

end Convolution

section FiniteSums

variable {ι Z E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Paper: (10.3.1.1), p. 448, and (10.3.2.1), p. 453. Form a finite section
by summing the rank-one contributions of all jets belonging to the selected zeros.
The functional in each term is the transpose of convolution applied to that jet. -/
def spectralConvolutionFiniteSum (A : E →L[ℂ] E) (x : ι → E) (Λ : ι → StrongDual ℂ E)
    (K : Finset Z) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → ι) : E →L[ℂ] E :=
  ∑ z ∈ K, ∑ m : Fin (N z), ((Λ (jet z m)).comp A).smulRight (x (jet z m))

/-- Paper: (10.3.1.21), p. 451. The finite section at one zero with one
surviving jet is exactly the transpose functional times its biorthogonal vector.
Deviation: Sanity check in multiplicity one. -/
theorem spectralConvolutionFiniteSum_single (A : E →L[ℂ] E) (x : ι → E) (Λ : ι → StrongDual ℂ E)
    (z : Z) (jet : Z → Fin 1 → ι) :
    spectralConvolutionFiniteSum A x Λ {z} (fun _ ↦ 1) jet =
      ((Λ (jet z 0)).comp A).smulRight (x (jet z 0)) := by sorry

end FiniteSums

section TraceNormLimits

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Paper: (10.3.1.23), p. 452. Trace-norm Cauchy tails for a rectangular
family of finite-rank operators. A trace-class witness gives the difference
its actual trace norm. -/
def SpectralRectanglesTraceCauchy (B : ℕ × ℕ → H →L[ℂ] H) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ i : ℕ × ℕ, ∀ j k, i ≤ j → i ≤ k →
    ∃ T : nuclearEndomorphisms H, T.val = B j - B k ∧ traceNorm T < ε

/-- Paper: (10.3.1.23), p. 452. Constant rectangles have zero differences.
Deviation: Sanity check for the trace-norm Cauchy condition. -/
theorem spectralRectanglesTraceCauchy_const (A : H →L[ℂ] H) :
    SpectralRectanglesTraceCauchy (fun _ ↦ A) := by
  intro ε hε
  refine ⟨(0, 0), fun _ _ _ _ ↦ ⟨0, by simp, ?_⟩⟩
  letI : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hz := ((traceNorm_normedSpaceCore (H := H)).norm_eq_zero_iff
    (0 : nuclearEndomorphisms H)).mpr rfl
  exact lt_of_eq_of_lt hz hε

/-- Paper: (10.3.1.23), p. 452. A trace-norm Cauchy family of biorthogonal
finite sections converges to the given operator in every Schatten norm.
Each coordinate of the image eventually agrees with the corresponding
coordinate of the operator. Totality of the functionals identifies the limit. -/
theorem spectralConvolutionFiniteSum_limit_of_traceCauchy {ι Z : Type*}
    (A : H →L[ℂ] H) (x : ι → H) (Λ : ι → StrongDual ℂ H)
    (e : Z ↪ ℕ × ℕ) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → ι)
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : Bijective (fun j : (z : Z) × Fin (N z) ↦ jet j.1 j.2))
    (p : ℝ) (hp : 1 ≤ p) :
    let B (ij : ℕ × ℕ) := spectralConvolutionFiniteSum A x Λ
      (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn) N jet
    let S := schattenClass H H p hp
    SpectralRectanglesTraceCauchy B →
      ∃ (hA : A ∈ S) (hB : ∀ ij, B ij ∈ S),
        Tendsto (fun ij ↦ schattenNorm (E := H) (F := H) (p := p) (hp := hp)
          (⟨B ij, hB ij⟩ - ⟨A, hA⟩ : S)) atTop (𝓝 0) := by sorry

/-- Paper: Theorem 10.3.1.1(3), p. 449. Rapid decay of the approximation
numbers gives a strongly nuclear expansion by the singular-value decomposition. -/
theorem isStronglyNuclearBanachOperator_of_rapid_approximationNumbers (A : H →L[ℂ] H)
    (_hA : ∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k * approximationNumber A n)
      atTop (𝓝 0)) : IsStronglyNuclearBanachOperator A := by sorry

end TraceNormLimits

-- TODO(paper-gap): On p. 450 an interval cannot select an arbitrary K with
-- omitted zeros between selected ordinates. The sums below use the actual
-- biorthogonal finite sections of (10.3.1.1) and (10.3.2.1).
-- TODO(paper-gap): (10.3.1.18) uses a uniform bound on paired norms, which fails
-- for close simple zeta zeros (ERRATA R5). The finite sections need another estimate.
-- The same display evaluates the entire Mellin transform at t. Its block matrix
-- in (10.3.1.17) uses i*t. A transform (t-z)H(z) separates the two points.

/-- Paper: (10.3.1.18)–(10.3.1.22), p. 451. Each individual finite section
has a singular-value bound in terms of its actual rank-one factors.
Deviation: The bound depends on the selected vectors and functionals. For a
single zero it is a local block bound, with no uniform biorthogonal constant. -/
theorem spectralConvolutionFiniteSum_approximationNumber_le {ι Z E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (x : ι → E) (Λ : ι → StrongDual ℂ E)
    (K : Finset Z) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → ι) (n : ℕ) :
    approximationNumber (spectralConvolutionFiniteSum A x Λ K N jet) n ≤
      ∑ z ∈ K, ∑ m : Fin (N z), ‖(Λ (jet z m)).comp A‖ * ‖x (jet z m)‖ := by sorry

/-- Paper: (10.3.1.17), p. 450. Compactly supported Bruhat tests have
an integrable Fourier–Mellin pairing at every norm twist. The pairing is
the unweighted integral against the twisted base character. -/
theorem spectralConvolution_mellin_integrable (φ : BruhatCompactSupport C𝔽)
    (χ : PontryaginDual C𝔽) (z : ℂ) :
    Integrable (fun g ↦ φ.val g * ideleClassNormTwist (F := F) χ z g) μ𝔽 ∧
      M(φ, χ, z) = ∫ g, φ.val g * ideleClassNormTwist (F := F) χ z g ∂μ𝔽 := by sorry

section Line

variable (a : ℝ)

local notation "Z(" χ ")" => {z : PontryaginDual C₁ × ℝ // 0 < order(χ z.1, shift(a, z.2))}
local notation "N(" χ ", " s ", " z ")" => spectralBoundaryMultiplicity s (mult(χ (z).val.1,
  shift(a, (z).val.2)))

/-- Paper: Theorem 10.3.1.1(1), p. 448. The rectangular sums have Cauchy tails in trace norm.
Gap: Trace-norm tails of the actual rectangles need an estimate allowing arbitrarily close zeros. -/
theorem spectralLineConvolution_traceCauchy (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ) ↪ ℕ × ℕ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (x : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s → Q(a, h₀, hs₀(hs)))
    (Λ : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) (fun ω ↦ χ ω) hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2)) :
    let H := Q(a, h₀, hs₀(hs))
    let A : H →L[ℂ] H := spectralConvolution (F := F) a h₀ hs₀(hs) φ
    let B (ij : ℕ × ℕ) : H →L[ℂ] H :=
      spectralConvolutionFiniteSum A x Λ
        (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn)
        (fun z ↦ N(χ, s, z))
        (fun z m ↦ ⟨(z.val.1, z.val.2, m.val), m.isLt⟩)
    SpectralRectanglesTraceCauchy B := by sorry

/-- Paper: Theorem 10.3.1.1(1) and (10.3.1.1), p. 448. The rectangular
finite-rank sums over any enumeration converge to convolution in each Schatten class.
Deviation: The injections permit finite or empty character and zero sets. Use
the strict multiplicity cutoff and the jet realization of Theorem 10.2.1.1. -/
theorem spectralLineConvolution_schatten_tendsto (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ) ↪ ℕ × ℕ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (x : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s → Q(a, h₀, hs₀(hs)))
    (Λ : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) (fun ω ↦ χ ω) hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2))
    (p : ℝ) (hp : 1 ≤ p) :
    let H := Q(a, h₀, hs₀(hs))
    let A : H →L[ℂ] H := spectralConvolution (F := F) a h₀ hs₀(hs) φ
    let S := schattenClass H H p hp
    let B (ij : ℕ × ℕ) : H →L[ℂ] H :=
      spectralConvolutionFiniteSum A x Λ
        (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn)
        (fun z ↦ N(χ, s, z))
        (fun z m ↦ ⟨(z.val.1, z.val.2, m.val), m.isLt⟩)
    ∃ (hA : A ∈ S) (hB : ∀ ij, B ij ∈ S),
      Tendsto (fun ij ↦ schattenNorm (E := H) (F := H) (p := p) (hp := hp)
        (⟨B ij, hB ij⟩ - ⟨A, hA⟩ : S)) atTop (𝓝 0) := by
  let count (z : Z(χ)) := N(χ, s, z)
  let jet (z : Z(χ)) (m : Fin (count z)) : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s :=
    ⟨(z.val.1, z.val.2, m.val), m.isLt⟩
  let index (j : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s) : (z : Z(χ)) × Fin (count z) :=
    ⟨⟨(j.val.1, j.val.2.1), SpectralLineJetIndex.order_pos j⟩, ⟨j.val.2.2, j.property⟩⟩
  let equiv : ((z : Z(χ)) × Fin (count z)) ≃ SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s :=
    ⟨fun zm ↦ jet zm.1 zm.2, index, fun _ ↦ rfl, fun _ ↦ rfl⟩
  exact spectralConvolutionFiniteSum_limit_of_traceCauchy
    (spectralConvolution (F := F) a h₀ hs₀(hs) φ) x Λ e count jet
    _hb equiv.bijective p hp
    (spectralLineConvolution_traceCauchy (F := F) a χ _hχ hs φ eχ e _he x Λ _hb _hj)

/-- Paper: Theorem 10.3.1.1(2), p. 448. Convolution on the a-line spectral
quotient is trace class for each test. -/
theorem spectralLineConvolution_nuclear {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽) :
    let H := Q(a, h₀, hs₀(hs))
    IsNuclearOperator (E := H) (F := H) (spectralConvolution (F := F) a h₀ hs₀(hs) φ) := by sorry

/-- Paper: Theorem 10.3.1.1(2) and (10.3.1.2), p. 448. The convolution
action lifts to a linear map into the trace class, continuous at zero in trace norm. -/
theorem spectralLineConvolution_traceNorm_continuous {s : ℝ} (hs : 1 < s) :
    let H := Q(a, h₀, hs₀(hs))
    ∃ T : BruhatCompactSupport C𝔽 →ₗ[ℂ] nuclearEndomorphisms H,
      (∀ φ, (T φ).val = spectralConvolution (F := F) a h₀ hs₀(hs) φ) ∧
      Tendsto (fun φ : BruhatCompactSupport C𝔽 ↦ traceNorm (H := H) (T φ)) (𝓝 0) (𝓝 0) := by sorry

/-- Paper: Theorem 10.3.1.1(2), p. 448. Taking the trace of convolution gives
a distribution on the Bruhat compactly supported test space. -/
theorem spectralLineConvolution_trace_distribution {s : ℝ} (hs : 1 < s) :
    let H := Q(a, h₀, hs₀(hs))
    ∃ D : StrongDual ℂ (BruhatCompactSupport C𝔽),
      ∀ (φ : BruhatCompactSupport C𝔽) (T : nuclearEndomorphisms H),
        T.val = spectralConvolution (F := F) a h₀ hs₀(hs) φ →
        D φ = hilbertTrace (H := H) T := by sorry

-- TODO(paper-gap): The L¹ comparison after (10.3.1.26) supplies no
-- sampling estimate at zero ordinates, and the rapid-decay claim uses arbitrary numbering.

/-- Paper: Theorem 10.3.1.1(2) and (10.3.1.3)–(10.3.1.4), p. 448. The
trace of convolution is the absolutely convergent sum of the Mellin values at
the line zeros weighted by their surviving multiplicities.
Deviation: Apply the strict cutoff of §10.2 and use positive meromorphic
order to exclude poles. The dependent double sum is expressed as one family. -/
theorem spectralLineConvolution_trace (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽) :
    let H := Q(a, h₀, hs₀(hs))
    let term (z : Z(χ)) := (N(χ, s, z) : ℂ) * M(φ, χ z.val.1, shift(0, z.val.2))
    ∀ (T : nuclearEndomorphisms H),
      T.val = spectralConvolution (F := F) a h₀ hs₀(hs) φ →
      Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace (H := H) T) := by sorry

/-- Paper: Theorem 10.3.1.1(3), p. 449. The singular values decay faster than every inverse power.
Deviation: Assume trace class for all tests. Factor the homogeneous radial profile into
finite sums of iterated convolutions of smooth compactly supported functions on ℝ.
The approximation-number product inequality then gives arbitrary polynomial decay. -/
theorem spectralLineIsotypeConvolution_rapid_approximationNumbers
    {s : ℝ} (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x)
    (_htrace : ∀ ψ : BruhatCompactSupport C𝔽,
      IsNuclearOperator (spectralConvolution (F := F) a h₀ hs₀(hs) ψ)) :
    let H := Qω(a, h₀, hs₀(hs), ω)
    let A : H →L[ℂ] H := spectralIsotypeConvolution (F := F) a h₀ hs₀(hs) ω φ
    ∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k * approximationNumber A n) atTop (𝓝 0) := by sorry

/-- Paper: Theorem 10.3.1.1(3), p. 449. Convolution by a homogeneous
test acts by a strongly nuclear operator on the corresponding quotient isotype.
Deviation: Use the left-translation eigencharacter ω. -/
theorem spectralLineIsotypeConvolution_stronglyNuclear
    {s : ℝ} (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    let H := Qω(a, h₀, hs₀(hs), ω)
    IsStronglyNuclearBanachOperator (E := H) (G := H)
      (spectralIsotypeConvolution (F := F) a h₀ hs₀(hs) ω φ) := by
  exact isStronglyNuclearBanachOperator_of_rapid_approximationNumbers _
    (spectralLineIsotypeConvolution_rapid_approximationNumbers (F := F) a hs ω φ _hφ
      (spectralLineConvolution_nuclear (F := F) a hs))

/-- Paper: Theorem 10.3.1.1(3) and (10.3.1.5), p. 449. The isotype
trace is the absolutely convergent zero sum of its base character.
Deviation: Use the strict cutoff and the left-translation eigencharacter ω
as in spectralConvolution_range_isotype. -/
theorem spectralLineIsotypeConvolution_trace (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {s : ℝ} (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    let H := Qω(a, h₀, hs₀(hs), ω)
    let term (t : {t : ℝ // 0 < order(χ ω, shift(a, t))}) :=
      (spectralBoundaryMultiplicity s (mult(χ ω, shift(a, t.val))) : ℂ) *
        M(φ, χ ω, shift(0, t.val))
    ∀ (T : nuclearEndomorphisms H),
      T.val = spectralIsotypeConvolution (F := F) a h₀ hs₀(hs) ω φ →
      Summable (fun t ↦ ‖term t‖) ∧ HasSum term (hilbertTrace (H := H) T) := by sorry

end Line

section Strip

variable (a : ℝ)

local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

-- TODO(paper-gap): The strip synthesis gap in §10.2 remains. The proof on
-- p. 455 also replaces log powers of unbounded order by a fixed Sobolev
-- weight and concludes only p > 1 for the displayed scalar sum.

/-- Paper: Theorem 10.3.2.1(1), p. 453. The rectangular sums have Cauchy tails in trace norm.
Gap: Trace-norm tails must control close zeros and high jet orders in the strip norm.
A strip component with bounded central-line frequency support vanishes by holomorphy. -/
theorem spectralStripConvolution_traceCauchy (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ, α) ↪ ℕ × ℕ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    let A : H →L[ℂ] H := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
    let B (ij : ℕ × ℕ) : H →L[ℂ] H :=
      spectralConvolutionFiniteSum A x Λ
        (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn)
        (fun z ↦ N(χ, α, s, z))
        (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)
    SpectralRectanglesTraceCauchy B := by sorry

/-- Paper: Theorem 10.3.2.1(1) and (10.3.2.1), p. 453. The rectangular
finite-rank sums over any enumeration of the strip zeros converge to convolution
in every Schatten class.
Deviation: The injections include finite or empty enumerations. The
interval is allowed to be a singleton and the jets use the strict boundary cutoff. -/
theorem spectralStripConvolution_schatten_tendsto (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ, α) ↪ ℕ × ℕ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (p : ℝ) (hp : 1 ≤ p) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    let A : H →L[ℂ] H := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
    let S := schattenClass H H p hp
    let B (ij : ℕ × ℕ) : H →L[ℂ] H :=
      spectralConvolutionFiniteSum A x Λ
        (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn)
        (fun z ↦ N(χ, α, s, z))
        (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)
    ∃ (hA : A ∈ S) (hB : ∀ ij, B ij ∈ S),
      Tendsto (fun ij ↦ schattenNorm (E := H) (F := H) (p := p) (hp := hp)
        (⟨B ij, hB ij⟩ - ⟨A, hA⟩ : S)) atTop (𝓝 0) := by
  let count (z : Z(χ, α)) := N(χ, α, s, z)
  let jet (z : Z(χ, α)) (m : Fin (count z)) : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
  let index (j : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s) : (z : Z(χ, α)) × Fin (count z) :=
    ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩, ⟨j.val.2.2.2, j.property⟩⟩
  let equiv : ((z : Z(χ, α)) × Fin (count z)) ≃ SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨fun zm ↦ jet zm.1 zm.2, index, fun _ ↦ rfl, fun _ ↦ rfl⟩
  exact spectralConvolutionFiniteSum_limit_of_traceCauchy
    (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ) x Λ e count jet
    _hb equiv.bijective p hp
    (spectralStripConvolution_traceCauchy (F := F) a χ _hχ hα hs φ eχ e _he x Λ _hb _hj)

/-- Paper: Theorem 10.3.2.1(2), p. 454. Convolution on the strip spectral
quotient is trace class for each test. -/
theorem spectralStripConvolution_nuclear {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (φ : BruhatCompactSupport C𝔽) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    IsNuclearOperator (E := H) (F := H) (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ) := by sorry

/-- Paper: Theorem 10.3.2.1(2) and (10.3.2.2), p. 454. The convolution
action lifts to a linear map into the trace class, continuous at zero in trace norm. -/
theorem spectralStripConvolution_traceNorm_continuous {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    ∃ T : BruhatCompactSupport C𝔽 →ₗ[ℂ] nuclearEndomorphisms H,
      (∀ φ, (T φ).val = spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ) ∧
      Tendsto (fun φ : BruhatCompactSupport C𝔽 ↦ traceNorm (H := H) (T φ)) (𝓝 0) (𝓝 0) := by sorry

/-- Paper: Theorem 10.3.2.1(2), p. 454. Taking the trace of convolution gives
a distribution on the Bruhat compactly supported test space. -/
theorem spectralStripConvolution_trace_distribution {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    ∃ D : StrongDual ℂ (BruhatCompactSupport C𝔽),
      ∀ (φ : BruhatCompactSupport C𝔽) (T : nuclearEndomorphisms H),
        T.val = spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ →
        D φ = hilbertTrace (H := H) T := by sorry

/-- Paper: Theorem 10.3.2.1(2) and (10.3.2.3)–(10.3.2.4), p. 454. The trace
is the absolutely convergent sum of the Mellin values at the strip zeros with
full interior multiplicities and truncated boundary multiplicities.
Deviation: Use the strict boundary cutoff and positive meromorphic order.
The dependent double sum is expressed as one family. -/
theorem spectralStripConvolution_trace (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω)) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    let term (z : Z(χ, α)) := (N(χ, α, s, z) : ℂ) * M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))
    ∀ (T : nuclearEndomorphisms H),
      T.val = spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ →
      Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace (H := H) T) := by sorry

/-- Paper: Theorem 10.3.2.1(3), p. 454. The singular values decay faster than every inverse power.
Deviation: Assume trace class for all tests. Factor the homogeneous radial profile into
finite sums of iterated convolutions of smooth compactly supported functions on ℝ.
The approximation-number product inequality then gives arbitrary polynomial decay. -/
theorem spectralStripIsotypeConvolution_rapid_approximationNumbers
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x)
    (_htrace : ∀ ψ : BruhatCompactSupport C𝔽,
      IsNuclearOperator (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) ψ)) :
    let H := Qω(a, hStrip(hα), hs₀(hs), ω)
    let A : H →L[ℂ] H := spectralIsotypeConvolution (F := F) a hStrip(hα) hs₀(hs) ω φ
    ∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k * approximationNumber A n) atTop (𝓝 0) := by sorry

/-- Paper: Theorem 10.3.2.1(3), p. 454. Convolution by a homogeneous
test acts by a strongly nuclear operator on the corresponding quotient isotype.
Deviation: Use the left-translation eigencharacter ω. -/
theorem spectralStripIsotypeConvolution_stronglyNuclear
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    let H := Qω(a, hStrip(hα), hs₀(hs), ω)
    IsStronglyNuclearBanachOperator (E := H) (G := H)
      (spectralIsotypeConvolution (F := F) a hStrip(hα) hs₀(hs) ω φ) := by
  exact isStronglyNuclearBanachOperator_of_rapid_approximationNumbers _
    (spectralStripIsotypeConvolution_rapid_approximationNumbers (F := F) a hα hs ω φ _hφ
      (spectralStripConvolution_nuclear (F := F) a hα hs))

/-- Paper: Theorem 10.3.2.1(3) and (10.3.2.5), p. 454. The isotype
trace is the absolutely convergent zero sum of its base character.
Deviation: Use the strict cutoff and the left-translation eigencharacter ω
as in spectralConvolution_range_isotype. -/
theorem spectralStripIsotypeConvolution_trace (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    let H := Qω(a, hStrip(hα), hs₀(hs), ω)
    let term (z : {z : ℝ × ℝ // z.1 ∈ Icc (-α) α ∧ 0 < order(χ ω, shift(a + z.1, z.2))}) :=
      (spectralStripMultiplicity α s z.val.1 (mult(χ ω, shift(a + z.val.1, z.val.2))) : ℂ) *
        M(φ, χ ω, shift(z.val.1, z.val.2))
    ∀ (T : nuclearEndomorphisms H),
      T.val = spectralIsotypeConvolution (F := F) a hStrip(hα) hs₀(hs) ω φ →
      Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace (H := H) T) := by sorry

end Strip

end RiemannMasullo
