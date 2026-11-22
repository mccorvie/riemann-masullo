module

public import RiemannMasullo.Ch09_HardySobolev.Sec3
public import RiemannMasullo.Ch12_TraceGeometric.Sec1a
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-! # §9.3: statements that are false as printed -/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace RiemannMasullo

set_option quotPrecheck false

local notation "logMod(" m ")" => (fun x ↦ Real.log ((m x).val : ℝ))

/-- Paper: Lemma 9.3.1.5, (9.3.1.6), p. 421. As printed: For each continuous
operator seminorm and each compact base interval, the translation bound is a
constant times the maximum endpoint twist times the absolute log-module raised
to s/2. This is the bound in (9.3.1.6). The repaired operator-norm bound is
`norm_hardySobolevTranslation_le`. See ERRATA F175. -/
def Printed.hardySobolevTranslation_seminorm_le : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ), IsModulation m → Surjective m →
    ∀ (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s),
    let W := CompactIntervalSobolev μ logMod(m) a b s
    ∀ p : Seminorm ℂ (W →L[ℂ] W), Continuous p →
      ∃ C : ℝ, 0 < C ∧ ∀ g : G,
        p (hardySobolevTranslation μ m a b s hab hs g) ≤
          C * max (((m g).val : ℝ) ^ a) (((m g).val : ℝ) ^ b) * |logMod(m) g| ^ (s / 2)

/-- Paper: Lemma 9.3.1.5, (9.3.1.6), p. 421. On the positive reals with
identity module and Haar measure dt/t, take a = b = 0, s = 2 and the operator
norm seminorm. The space is nonzero, since a nonzero smooth compact log-profile
lies in it. At g = 1 the translate is the identity, so the bound reads 1 ≤ 0. -/
theorem Printed.hardySobolevTranslation_seminorm_le_false :
    ¬ Printed.hardySobolevTranslation_seminorm_le := by
  sorry

/-- Paper: Definition 9.3.1.1, p. 419. As printed: The left-translation action
used in the definition acts on the Sobolev space for every nonempty closed
interval. This is its assertion that a finite-norm exponential-decay test
still has finite norm after translation, using the supremum in (9.2.2.3).
`hardySobolevTranslation` provides the action on compact bases. See ERRATA F175. -/
def Printed.hardySobolevTranslation_preserves_finiteNorm : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ), IsModulation m → Surjective m →
    ∀ (I : Set ℝ), IsClosed I → OrdConnected I → I.Nonempty →
    ∀ s : ℝ, 0 ≤ s → ∀ (f : ModulatedExponentialDecay m univ) (g : G),
      intervalSobolevENorm μ logMod(m) I s f.val < ∞ →
      intervalSobolevENorm μ logMod(m) I s (fun x ↦ f.val (g⁻¹ * x)) < ∞

/-- Paper: Definition 9.3.1.1, p. 419. On the positive reals with identity
module and Haar measure dt/t, take I = [0, ∞), s = 0 and a nonzero smooth
bump in log coordinates supported in (−2, −1). There the endpoint twists
are uniformly bounded as the nonnegative exponent grows. The left translate
by exp 3 is supported in (1, 2) in log coordinates, where the norms for
[0, b] grow without bound as b tends to infinity. -/
theorem Printed.hardySobolevTranslation_preserves_finiteNorm_false :
    ¬ Printed.hardySobolevTranslation_preserves_finiteNorm := by
  sorry

/-- Paper: Lemma 9.3.2.1(2)–(4), p. 422. Given the extension (9.3.2.1), there is a
family indexed by the nonnegative integers and all norm-one characters. Each member is in its
indexed left isotype and its twisted Fourier transform is supported in the band
based on the chosen extension of that same character. The identity lies in the
strong closure of their images under the convolution extension (9.3.2.1).
Applying that map to B requires B to lie in its stated Schwartz domain, as
well as requiring the b-twists to be Schwartz. The band convention in
`exists_singletonDecay_isotype_approximation` uses the inverse isotype character.
See ERRATA F175. -/
def Printed.singletonDecay_approximation_isotype_band : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ), IsModulation m → Surjective m →
    ∀ (b s : ℝ) (hs : 0 ≤ s),
    let K := m.toMonoidHom.ker
    ∀ χ : PontryaginDual K → PontryaginDual G,
    (∀ (ω : PontryaginDual K) (k : K), χ ω k.val = ω k) →
    let W := CompactIntervalSobolev μ logMod(m) b b s
    ∀ A : SchwartzBruhat G →L[ℂ] (W →L[ℂ] W),
      (∀ (d : BruhatCompactSupport G) (f : SchwartzBruhat G), f.val = d.val →
        A f = hardySobolevTestAction μ m b b s le_rfl hs d) →
    ∃ φ : ℕ → PontryaginDual K → SchwartzBruhat G,
      (∀ n ω, modulationWeight m b (φ n ω).val ∈ schwartzBruhatSubmodule G) ∧
      (∀ n ω (k : K) x, (φ n ω).val (k.val⁻¹ * x) = (ω k : ℂ) * (φ n ω).val x) ∧
      (∀ n ω, tsupport (lcaFourier μ (modulationWeight m b (φ n ω).val)) ⊆
        modulatedFrequencyBand m (χ ω) (-(n : ℝ)) n) ∧
      (ContinuousLinearMap.id ℂ W : W →Lₚₜ[ℂ] W) ∈
        closure (range (fun i : ℕ × PontryaginDual K ↦ (A (φ i.1 i.2) : W →Lₚₜ[ℂ] W)))

/-- Paper: Lemma 9.3.2.1(2)–(4), pp. 422–424. Take G = ℝ_{>0} × ℤ/3 with
module the first projection, product Haar measure, and b = s = 0. Use the
convolution from `existsUnique_schwartzBruhat_zeroLineAction`. For either
nontrivial ω, the left-isotype condition puts the Fourier support over ω⁻¹.
The printed band is over ω, which is distinct, so those kernels must vanish.
The remaining trivial-channel kernels kill vectors in the two nontrivial
isotypes. For example, take a nonzero smooth compact radial profile times a
nontrivial character of ℤ/3. Strong closure still kills that vector. -/
theorem Printed.singletonDecay_approximation_isotype_band_false :
    ¬ Printed.singletonDecay_approximation_isotype_band := by
  sorry

/-- Paper: Theorem 9.3.2.6, (9.3.2.10), p. 426. As the cutoff height grows,
the orthogonal projections onto the common kernels of all indicated Mellin
jets converge strongly to the identity. The Hilbert completion is specified
by its dense test map and the norm (9.2.2.31).
Deviation: The display uses the character and test from Lemma 9.3.2.5 without
binding them again. We use those data and its interior-zero hypothesis. The
convergence assertion is made for each realization of the printed completion,
since on an unbounded base the displayed norm can be infinite. See ERRATA F144. -/
def Printed.hardySobolevJetKernelProjection_tendsto : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m), Surjective m →
    ∀ (I : Set ℝ), IsClosed I → OrdConnected I → (interior I).Nonempty →
    ∀ s : ℝ, 0 ≤ s → ∀ (χ : PontryaginDual G) (φ : ModulatedExponentialDecay m univ),
    let μ := canonicalModulatedHaar m hm
    let χ₀ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
    let M := fun (f : ModulatedExponentialDecay m univ) (z : ℂ) ↦
      modulatedFourierMellin m univ hm μ f.val (quasiCharacterNormTwist m.toMonoidHom m.continuous χ₀ z)
    (∀ z, M φ z = 0 → z.re ∈ interior I) →
    ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
      (ι : ModulatedExponentialDecay m univ →ₗ[ℂ] W), DenseRange ι →
      (∀ f, ENNReal.ofReal ‖ι f‖ = intervalSobolevENorm μ logMod(m) I s f.val) →
      let J := {i : ℂ × ℕ // M φ i.1 = 0 ∧ (i.2 : ℕ∞) < analyticOrderAt (M φ) i.1}
      ∃ (δ : J → W →L[ℂ] ℂ) (P : Ioi (0 : ℝ) → W →L[ℂ] W),
        (∀ i f, δ i (ι f) = iteratedDeriv i.val.2 (M f) i.val.1) ∧
        (∀ T, IsStarProjection (P T) ∧
          range (P T) = {u | ∀ i : J, |i.val.1.im| ≤ T.val → δ i u = 0}) ∧
        ∀ u, Tendsto (fun T ↦ P T u) atTop (𝓝 u)

/-- Paper: Theorem 9.3.2.6, p. 426. Use the positive reals with identity module,
trivial character, I = [−1,1] and s = 0. In log coordinates use
g(x) = exp(−x²/4)/√(4π) and φ = −g′. Their Mellin transforms are exp(z²) and
z exp(z²). Zero is the unique zero of the latter and is simple. The compact
interval weighted L² model realizes the completion. For every positive T the
range is the kernel of evaluation at zero. That functional takes value 1 on
the vector of g, so continuity rules out convergence of its projections to g. -/
theorem Printed.hardySobolevJetKernelProjection_tendsto_false :
    ¬ Printed.hardySobolevJetKernelProjection_tendsto := by
  sorry

/-- Paper: Theorem 9.3.3.5(3), (9.3.3.9), p. 429. On the reading that (3)
uses the bounded compactly supported symbols in (1), the integral of the
smoothed diagonal differs from 2 log(Λ) μ₁(G¹) φ(1) by o(1).
Deviation: This is the ordinary Haar L² case I = {0}, s = 0 used on p. 429.
Measurability of the symbol is implicit in the kernel integral. If (3)
inherits the smoothness assumptions of (2), the singleton symbol below is
outside its scope. See ERRATA F175 and `truncatedHardySobolevConvolution_trace_tendsto`. -/
def Printed.truncatedHardySobolevConvolution_diagonal_tendsto : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ), IsModulation m → Surjective m →
    ∀ (τ : ℝ≥0ˣ →ₜ* G), RightInverse τ m →
    ∀ (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure],
    μ = (μ₁.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2) →
    ∀ (φ : G → ℂ), AEMeasurable φ μ → HasCompactSupport φ → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) →
    ∀ (U : ℕ → Set G), IsDPrimeSequence μ U → (∀ n, MeasurableSet (U n)) →
    ∀ (ε : ℝ → ℝ) (ρ : ℝ → G → ℝ),
    Tendsto (fun Λ ↦ ε Λ * Λ) atTop (𝓝 0) →
    (∀ x, Tendsto (fun Λ ↦ ρ Λ x) atTop (𝓝 1)) →
    (∀ᶠ Λ in atTop, IsModulatedCutoff m Λ (ε Λ) (ρ Λ) ∧
      0 < Λ⁻¹ + ε Λ ∧ Λ⁻¹ + ε Λ < Λ - ε Λ) →
    let κ (Λ : ℝ) (p : G × G) := (ρ Λ p.1 : ℂ) * φ (p.1 * p.2⁻¹)
    let diagonal (Λ : ℝ) (x : G) := dSequenceKernelSmoothening μ U (κ Λ) (x, x)
    (∀ᶠ Λ in atTop, Integrable (diagonal Λ) μ) ∧
      Tendsto (fun Λ ↦ (∫ x, diagonal Λ x ∂μ) -
        (2 * Real.log Λ * μ₁.real univ : ℝ) * φ 1) atTop (𝓝 0)

/-- Paper: Theorem 9.3.3.5(3), (9.3.3.9), p. 429. Take G = ℝ_{>0}, the identity
module, Haar measure dt/t, mass one on the trivial kernel, base {0} and degree
zero. Let φ be the indicator of {1}, let Uₙ = [exp(−2⁻ⁿ), exp(2⁻ⁿ)],
and use the sharp cutoff of [Λ⁻¹, Λ] with ε = Λ⁻² for large Λ. The Haar kernel
is zero almost everywhere, since it is supported on the product diagonal,
so every average defining its smoothening vanishes. The asserted leading
term is 2 log Λ because φ(1) = 1. -/
theorem Printed.truncatedHardySobolevConvolution_diagonal_tendsto_false :
    ¬ Printed.truncatedHardySobolevConvolution_diagonal_tendsto := by
  sorry

end RiemannMasullo
