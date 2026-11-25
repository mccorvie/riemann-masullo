module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3_TraceClass
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-!
# Trace class on the spectral quotients

Masullo, Theorems 10.3.1.1(2)–(3) and 10.3.2.1(2)–(3), pp. 448–449 and 454. Convolution by a
test on the line and strip spectral quotients is trace class, the action is continuous in trace
norm, its trace is a distribution, and on an isotype it is strongly nuclear with trace the sum
over the zeros of the base character.

Trace class is taken from `Sec3_TraceClass`, where the zeros are summed in clusters. So nothing
in this file rests on the recorded gap `spectralStripConvolution_traceCauchy_compact_block_series`
of `Sec3` (#7241). That gap is still what parts (1) of the two theorems rest on, the sums over
single zeros in an arbitrary order: `spectralStripConvolution_traceCauchy`,
`spectralLineConvolution_traceCauchy` and the two `schatten_tendsto` theorems of `Sec3`.

The statements are those that stood in `Sec3`, unchanged. They are placed here because
`Sec3_TraceClass` imports `Sec3`.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
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

-- Select the norm topology directly when using the locally convex nuclear ideal, as in `Sec3`.
attribute [local instance] instSpectralQuotientPolynormableSec3

section Line

variable (a : ℝ)

local notation "Z(" χ ")" => {z : PontryaginDual C₁ × ℝ // 0 < order(χ z.1, shift(a, z.2))}
local notation "N(" χ ", " s ", " z ")" => spectralBoundaryMultiplicity s (mult(χ (z).val.1,
  shift(a, (z).val.2)))

/-- Paper: Theorem 10.3.1.1(2), p. 448. Convolution on the a-line spectral
quotient is trace class for each test.
It is `spectralLineConvolution_nuclear_of_summable_clusterTraceNorms` of `Sec3_TraceClass` at
orders `s > 1`, so it does not use the recorded gap #7241. -/
theorem spectralLineConvolution_nuclear {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽) :
    let H := Q(a, h₀, hs₀(hs))
    IsNuclearOperator (E := H) (F := H) (spectralConvolution (F := F) a h₀ hs₀(hs) φ) :=
  spectralLineConvolution_nuclear_of_summable_clusterTraceNorms a hs₀(hs) φ

/-- Paper: Theorem 10.3.1.1(2) and (10.3.1.2), p. 448. The convolution
action lifts to a linear map into the trace class, continuous at zero in trace norm. -/
theorem spectralLineConvolution_traceNorm_continuous {s : ℝ} (hs : 1 < s) :
    let H := Q(a, h₀, hs₀(hs))
    ∃ T : BruhatCompactSupport C𝔽 →ₗ[ℂ] nuclearEndomorphisms H,
      (∀ φ, (T φ).val = spectralConvolution (F := F) a h₀ hs₀(hs) φ) ∧
      Tendsto (fun φ : BruhatCompactSupport C𝔽 ↦ traceNorm (H := H) (T φ)) (𝓝 0) (𝓝 0) := by
  intro H
  let A : BruhatCompactSupport C𝔽 →ₗ[ℂ] (H →L[ℂ] H) :=
    (spectralConvolution_isLinear (F := F) a h₀ hs₀(hs)).mk'
      (spectralConvolution (F := F) a h₀ hs₀(hs))
  exact spectralConvolution_traceNorm_lift bruhatCompactSupport_strictLF A
    (spectralConvolution_opNorm_continuous (F := F) a h₀ hs₀(hs))
    (spectralLineConvolution_nuclear (F := F) a hs)

/-- Paper: Theorem 10.3.1.1(2), p. 448. Taking the trace of convolution gives
a distribution on the Bruhat compactly supported test space. -/
theorem spectralLineConvolution_trace_distribution {s : ℝ} (hs : 1 < s) :
    let H := Q(a, h₀, hs₀(hs))
    ∃ D : StrongDual ℂ (BruhatCompactSupport C𝔽),
      ∀ (φ : BruhatCompactSupport C𝔽) (T : nuclearEndomorphisms H),
        T.val = spectralConvolution (F := F) a h₀ hs₀(hs) φ →
        D φ = hilbertTrace (H := H) T := by
  have traceDistribution {X : Type _} {H : Type _} [AddCommGroup X] [Module ℂ X]
      [TopologicalSpace X] [IsTopologicalAddGroup X] [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H] (A : X → H →L[ℂ] H)
      (h : ∃ T : X →ₗ[ℂ] nuclearEndomorphisms H, (∀ x, (T x).val = A x) ∧
        Tendsto (fun x : X ↦ traceNorm (H := H) (T x)) (𝓝 0) (𝓝 0)) :
      ∃ D : StrongDual ℂ X, ∀ (x : X) (U : nuclearEndomorphisms H),
        U.val = A x → D x = hilbertTrace U := by
    obtain ⟨T, hT, ht⟩ := h
    obtain ⟨L, hL⟩ := hilbertTrace_linear (H := H)
    let D : X →ₗ[ℂ] ℂ := L.comp T
    have hb (x : X) : ‖D x‖ ≤ traceNorm (T x) :=
      (congrArg (fun c : ℂ ↦ ‖c‖) (hL (T x))).le.trans (norm_hilbertTrace_le (T x))
    have hd : Continuous D := continuous_of_continuousAt_zero D <| by
      change Tendsto D (𝓝 0) (𝓝 (D 0))
      rw [D.map_zero]
      exact squeeze_zero_norm hb ht
    refine ⟨⟨D, hd⟩, fun x U hU ↦ ?_⟩
    have heq : T x = U := Subtype.ext ((hT x).trans hU.symm)
    exact (hL (T x)).trans (congrArg (hilbertTrace (H := H)) heq)
  exact traceDistribution (X := BruhatCompactSupport C𝔽) (H := Q(a, h₀, hs₀(hs)))
    (spectralConvolution (F := F) a h₀ hs₀(hs))
    (spectralLineConvolution_traceNorm_continuous (F := F) a hs)

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
      Summable (fun t ↦ ‖term t‖) ∧ HasSum term (hilbertTrace (H := H) T) := by
  intro H term D hD
  let A := spectralConvolution (F := F) a h₀ hs₀(hs) φ
  have hA : IsNuclearOperator A := spectralLineConvolution_nuclear (F := F) a hs φ
  have hfull := spectralLineConvolution_trace (F := F) a χ _hχ hs φ ⟨A, hA⟩ rfl
  have ht := spectralIsotype_trace_eq (F := F) a h₀ hs₀(hs) ω φ _hφ hA D hD
  have sub := spectralIsotype_trace_fiber ω (fun η t ↦ 0 < order(χ η, shift(a, t)))
    (fun z ↦ (N(χ, s, z) : ℂ) * M(φ, χ z.val.1, shift(0, z.val.2))) hfull.1 hfull.2
    (fun z hz ↦ by rw [spectralIsotype_mellin_eq_zero χ _hχ hz φ _hφ, mul_zero])
  exact ⟨sub.1, ht ▸ sub.2⟩

end Line

section Strip

variable (a : ℝ)

local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

/-- Paper: Theorem 10.3.2.1(2), p. 454. Convolution on the strip spectral
quotient is trace class for each test.
It is `spectralStripConvolution_nuclear_of_summable_clusterTraceNorms` of `Sec3_TraceClass` at
orders `s > 1`, so it does not use the recorded gap #7241. -/
theorem spectralStripConvolution_nuclear {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (φ : BruhatCompactSupport C𝔽) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    IsNuclearOperator (E := H) (F := H) (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ) :=
  spectralStripConvolution_nuclear_of_summable_clusterTraceNorms a hα hs₀(hs) φ

-- TODO(paper-gap): (10.3.2.2), p. 454 asks for continuity of the strip convolution action in
-- trace norm. The printed proof of Theorem 10.3.2.1 replaces the scalar series (10.3.2.6) by
-- (10.3.2.7) and shows the latter converges for p > 1; but the constants C_{N,I,s}(phi) of
-- (10.3.2.11) carry the derivatives of the test itself, so this is an estimate at a fixed test
-- and yields no seminorm bound uniform in the test. The per-zero bounds (10.3.1.19)-(10.3.1.22),
-- which the proof says carry over, rest on the single biorthogonality constant C of (10.3.1.18),
-- which is Printed.spectralLineJet_uniformBiorthogonalBound, refuted in Sec3_Printed.lean. On the
-- strip N_{I,s} is unbounded for alpha > 0 (as the proof of 10.3.2.1 notes), so the jets of one
-- character grow with s and alpha as well. What is missing is a bound on the number of strip
-- zeros of L(s, chi w) with |Im s| <= T in the number of jet orders used, together with a
-- trace-norm estimate uniform in the test. A reduction of this statement to that single
-- seminorm estimate is blocked at elaboration: the linear lift into
-- nuclearEndomorphisms (Q a (hStrip hα) (hs₀ hs)) cannot be built by the anonymous constructor
-- of LinearMap (here LinearMap extends AddHom and MulActionHom, so the field literal
-- { toFun := ..., map_add' := ..., map_smul' := ... } is rejected by the parser), and building
-- it from an abstract function via AddHom exhausts the heartbeat budget in isDefEq and whnf on
-- that quotient type; see #5398.

/-- Paper: Theorem 10.3.2.1(2) and (10.3.2.2), p. 454. The convolution
action lifts to a linear map into the trace class, continuous at zero in trace norm. -/
theorem spectralStripConvolution_traceNorm_continuous {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    ∃ T : BruhatCompactSupport C𝔽 →ₗ[ℂ] nuclearEndomorphisms H,
      (∀ φ, (T φ).val = spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ) ∧
      Tendsto (fun φ : BruhatCompactSupport C𝔽 ↦ traceNorm (H := H) (T φ)) (𝓝 0) (𝓝 0) := by
  intro H
  let A : BruhatCompactSupport C𝔽 →ₗ[ℂ] (H →L[ℂ] H) :=
    (spectralConvolution_isLinear (F := F) a hStrip(hα) hs₀(hs)).mk'
      (spectralConvolution (F := F) a hStrip(hα) hs₀(hs))
  exact spectralConvolution_traceNorm_lift bruhatCompactSupport_strictLF A
    (spectralConvolution_opNorm_continuous (F := F) a hStrip(hα) hs₀(hs))
    (spectralStripConvolution_nuclear (F := F) a hα hs)

/-- Paper: Theorem 10.3.2.1(2), p. 454. Taking the trace of convolution gives
a distribution on the Bruhat compactly supported test space. -/
theorem spectralStripConvolution_trace_distribution {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    ∃ D : StrongDual ℂ (BruhatCompactSupport C𝔽),
      ∀ (φ : BruhatCompactSupport C𝔽) (T : nuclearEndomorphisms H),
        T.val = spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ →
        D φ = hilbertTrace (H := H) T := by
  have traceDistribution {X : Type _} {H : Type _} [AddCommGroup X] [Module ℂ X]
      [TopologicalSpace X] [IsTopologicalAddGroup X] [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H] (A : X → H →L[ℂ] H)
      (h : ∃ T : X →ₗ[ℂ] nuclearEndomorphisms H, (∀ x, (T x).val = A x) ∧
        Tendsto (fun x : X ↦ traceNorm (H := H) (T x)) (𝓝 0) (𝓝 0)) :
      ∃ D : StrongDual ℂ X, ∀ (x : X) (U : nuclearEndomorphisms H),
        U.val = A x → D x = hilbertTrace U := by
    obtain ⟨T, hT, ht⟩ := h
    obtain ⟨L, hL⟩ := hilbertTrace_linear (H := H)
    let D : X →ₗ[ℂ] ℂ := L.comp T
    have hb (x : X) : ‖D x‖ ≤ traceNorm (T x) :=
      (congrArg (fun c : ℂ ↦ ‖c‖) (hL (T x))).le.trans (norm_hilbertTrace_le (T x))
    have hd : Continuous D := continuous_of_continuousAt_zero D <| by
      change Tendsto D (𝓝 0) (𝓝 (D 0))
      rw [D.map_zero]
      exact squeeze_zero_norm hb ht
    refine ⟨⟨D, hd⟩, fun x U hU ↦ ?_⟩
    have heq : T x = U := Subtype.ext ((hT x).trans hU.symm)
    exact (hL (T x)).trans (congrArg (hilbertTrace (H := H)) heq)
  exact traceDistribution (X := BruhatCompactSupport C𝔽) (H := Q(a, hStrip(hα), hs₀(hs)))
    (spectralConvolution (F := F) a hStrip(hα) hs₀(hs))
    (spectralStripConvolution_traceNorm_continuous (F := F) a hα hs)

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
      Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace (H := H) T) := by
  intro H term D hD
  let A := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
  have hA : IsNuclearOperator A := spectralStripConvolution_nuclear (F := F) a hα hs φ
  have hfull := spectralStripConvolution_trace (F := F) a χ _hχ hα hs φ ⟨A, hA⟩ rfl
  have ht := spectralIsotype_trace_eq (F := F) a hStrip(hα) hs₀(hs) ω φ _hφ hA D hD
  have sub := spectralIsotype_trace_fiber ω
    (fun η (x : ℝ × ℝ) ↦ x.1 ∈ Icc (-α) α ∧ 0 < order(χ η, shift(a + x.1, x.2)))
    (fun z ↦ (N(χ, α, s, z) : ℂ) * M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))) hfull.1 hfull.2
    (fun z hz ↦ by rw [spectralIsotype_mellin_eq_zero χ _hχ hz φ _hφ, mul_zero])
  exact ⟨sub.1, ht ▸ sub.2⟩

end Strip

end RiemannMasullo
