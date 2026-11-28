module

public import RiemannMasullo.Ch09_HardySobolev.Sec3_AdjointPolynomial
import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec5

/-! # Series of tests and series of convolutions on the weighted space

The convolution action of §9.3 on the weighted space of §9.2 is the Bochner integral of the
translations against the test. So tests dominated by one fixed test act with uniformly bounded
norms (`exists_hardySobolevTestAction_norm_le_of_dominated`), and a pointwise convergent series
of such tests with absolutely summable coefficients acts as the norm convergent series of the
actions (`hasSum_hardySobolevTestAction`).

A test times a smooth function of the logarithm of the modulation is a test
(`exists_bruhatCompactSupport_logProfile`); the series are applied to such products. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal InnerProductSpace Pointwise ComplexConjugate ContDiff

namespace RiemannMasullo.WeightedConvolution

section Tests

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- A compact Bruhat test times a smooth function of the logarithm of the modulation is a
compact Bruhat test. -/
theorem exists_bruhatCompactSupport_logProfile (m : G →ₜ* ℝ≥0ˣ) (φ : BruhatCompactSupport G)
    {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) :
    ∃ Ψ : BruhatCompactSupport G, ∀ g, Ψ.val g = h (Real.log ((m g).val : ℝ)) * φ.val g :=
  ⟨⟨fun g ↦ h (Real.log ((m g).val : ℝ)) * φ.val g,
    (mem_bruhatSmoothSubmodule_iff _).mpr fun p ↦
      isBruhatContDiff_mul (isBruhatSmooth_logProfile m hh p)
        ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1 p),
    (show HasCompactSupport φ.val from φ.property.2).mul_left⟩, fun _ ↦ rfl⟩

end Tests

/-- A convergent series of bounded operators converges at each vector. -/
private theorem hasSum_clm_apply {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (B : ι → E →L[ℂ] E) (S : E →L[ℂ] E) (hS : HasSum B S) (u : E) :
    HasSum (fun n ↦ (B n) u) (S u) :=
  (ContinuousLinearMap.apply ℂ E u).hasSum hS

/-- Operators given by Bochner integrals of one strongly measurable family against scalar
functions: if the scalar functions sum pointwise, with absolutely summable coefficients and an
integrable domination, the operators sum in operator norm to the operator of the sum. -/
private theorem hasSum_smul_of_integral_series {X E ι : Type*} [MeasurableSpace X]
    {μ : Measure X} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Countable ι]
    (T : X → E →L[ℂ] E) (f : ι → X → ℂ) (F : X → ℂ) (c : ι → ℂ) (A : ι → E →L[ℂ] E)
    (B : E →L[ℂ] E) (M₀ : ℝ) (hc : Summable fun n ↦ ‖c n‖) (hAn : ∀ n, ‖A n‖ ≤ M₀)
    (hA : ∀ n u, A n u = ∫ x, f n x • T x u ∂μ) (hB : ∀ u, B u = ∫ x, F x • T x u ∂μ)
    (hint : ∀ n u, Integrable (fun x ↦ f n x • T x u) μ)
    (b : E → X → ℝ) (hb : ∀ u, Integrable (b u) μ) (hdom : ∀ n u x, ‖f n x • T x u‖ ≤ b u x)
    (hF : ∀ x, HasSum (fun n ↦ c n * f n x) (F x)) :
    HasSum (fun n ↦ c n • A n) B := by
  have hsummable : Summable fun n ↦ c n • A n :=
    Summable.of_norm_bounded (hc.mul_right M₀) fun n ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hAn n) (norm_nonneg _)
  have hlimit : ∑' n, c n • A n = B := by
    apply ContinuousLinearMap.ext
    intro u
    have h1 : HasSum (fun n ↦ (c n • A n) u) ((∑' n, c n • A n) u) :=
      hasSum_clm_apply _ _ hsummable.hasSum u
    let Fn (n : ι) (x : X) : E := c n • f n x • T x u
    have hFint (n : ι) : Integrable (Fn n) μ := (hint n u).smul (c n)
    have hFsum : Summable fun n ↦ ∫ x, ‖Fn n x‖ ∂μ := by
      refine Summable.of_nonneg_of_le (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _)
        (fun n ↦ ?_) (hc.mul_right (∫ x, b u x ∂μ))
      rw [← integral_const_mul]
      refine integral_mono (hFint n).norm ((hb u).const_mul _) fun x ↦ ?_
      change ‖c n • f n x • T x u‖ ≤ ‖c n‖ * b u x
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hdom n u x) (norm_nonneg _)
    have h2 := hasSum_integral_of_summable_integral_norm hFint hFsum
    have h3 : (fun n ↦ ∫ x, Fn n x ∂μ) = fun n ↦ (c n • A n) u := by
      funext n
      change ∫ x, c n • f n x • T x u ∂μ = c n • A n u
      rw [hA n u, integral_smul]
    have h4 : ∫ x, ∑' n, Fn n x ∂μ = B u := by
      rw [hB u]
      refine integral_congr_ae (.of_forall fun x ↦ ?_)
      have h5 : HasSum (fun n ↦ Fn n x) (F x • T x u) := by
        refine ((hF x).smul_const (T x u)).congr_fun fun n ↦ ?_
        change c n • f n x • T x u = (c n * f n x) • T x u
        rw [mul_smul]
      exact h5.tsum_eq
    rw [h3, h4] at h2
    exact h1.unique h2
  exact hlimit ▸ hsummable.hasSum

section Series

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)

set_option quotPrecheck false in
local notation "L" => (fun x ↦ Real.log ((m x).val : ℝ))

/-- Convolutions by tests dominated by one fixed test have uniformly bounded norms on the
weighted space: if `‖ψ g‖ ≤ c ‖φ g‖` for all `g`, the norm of convolution by `ψ` is at most
`c` times a constant that depends only on `φ`. The convolution is the Bochner integral of the
translations, and the translations are bounded uniformly on the compact support of `φ`, by the
Banach–Steinhaus theorem. -/
theorem exists_hardySobolevTestAction_norm_le_of_dominated (a b s : ℝ) (hab : a ≤ b)
    (hs : 0 ≤ s) (φ : BruhatCompactSupport G) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ (ψ : BruhatCompactSupport G) (c : ℝ), 0 ≤ c →
      (∀ g, ‖ψ.val g‖ ≤ c * ‖φ.val g‖) →
      let A : CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s :=
        hardySobolevTestAction μ m a b s hab hs ψ
      ‖A‖ ≤ c * M₀ := by
  let τ := hardySobolevTranslation μ m a b s hab hs
  have hτ : Continuous (fun p : G × CompactIntervalSobolev μ L a b s ↦ τ p.1 p.2) :=
    (exists_hardySobolevTranslation μ m a b s hab hs).choose_spec.2
  have hφc : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hK : IsCompact (tsupport φ.val) := φ.property.2
  obtain ⟨C, hC⟩ : ∃ C, ∀ g : tsupport φ.val, ‖τ g‖ ≤ C := by
    apply banach_steinhaus
    intro u
    have hcont : Continuous (fun g : G ↦ τ g u) := hτ.comp (Continuous.prodMk_left u)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    exact ⟨C, fun g ↦ hC g g.property⟩
  have hi : Integrable φ.val μ := hφc.integrable_of_hasCompactSupport φ.property.2
  have hM₀ : 0 ≤ max C 0 * ∫ g, ‖φ.val g‖ ∂μ :=
    mul_nonneg (le_max_right _ _) (integral_nonneg fun _ ↦ norm_nonneg _)
  refine ⟨max C 0 * ∫ g, ‖φ.val g‖ ∂μ, hM₀, fun ψ c hc hdom ↦ ?_⟩
  intro A
  refine A.opNorm_le_bound (mul_nonneg hc hM₀) fun u ↦ ?_
  have hψc : Continuous ψ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp ψ.property.1)
  have hie : Integrable ψ.val μ := hψc.integrable_of_hasCompactSupport ψ.property.2
  rw [hardySobolev_eq_integral_translation_of_convolution μ m a b s hab hs hie ψ.property.2 A
    (hardySobolevTestAction_apply μ m a b s hab hs ψ) u]
  refine (norm_integral_le_of_norm_le (hi.norm.const_mul (c * max C 0 * ‖u‖))
    (.of_forall fun g ↦ ?_)).trans_eq ?_
  · by_cases hg : φ.val g = 0
    · have h0 : ψ.val g = 0 := by
        have h := hdom g
        rw [hg, norm_zero, mul_zero] at h
        exact norm_le_zero_iff.mp h
      simp [h0, hg]
    · have hmem : g ∈ tsupport φ.val := subset_tsupport _ hg
      have h2 : ‖τ g u‖ ≤ max C 0 * ‖u‖ := ((τ g).le_opNorm u).trans
        (mul_le_mul_of_nonneg_right ((hC ⟨g, hmem⟩).trans (le_max_left _ _)) (norm_nonneg _))
      rw [norm_smul]
      calc ‖ψ.val g‖ * ‖τ g u‖ ≤ (c * ‖φ.val g‖) * (max C 0 * ‖u‖) :=
            mul_le_mul (hdom g) h2 (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))
        _ = c * max C 0 * ‖u‖ * ‖φ.val g‖ := by ring
  · rw [integral_const_mul]
    ring

/-- A pointwise convergent series of tests, dominated by one test and with absolutely summable
coefficients, acts on the weighted space as the norm convergent series of the convolutions:
if `Ψ g = ∑ n, c n * ψ n g` for every `g`, with `‖ψ n g‖ ≤ ‖φ g‖` and `∑ n, ‖c n‖ < ∞`, then
convolution by `Ψ` is the sum of `c n` times convolution by `ψ n`, in operator norm. -/
theorem hasSum_hardySobolevTestAction {ι : Type*} [Countable ι] (a b s : ℝ) (hab : a ≤ b)
    (hs : 0 ≤ s) (φ Ψ : BruhatCompactSupport G) (ψ : ι → BruhatCompactSupport G) (c : ι → ℂ)
    (hc : Summable fun n ↦ ‖c n‖) (hdom : ∀ n g, ‖(ψ n).val g‖ ≤ ‖φ.val g‖)
    (hΨ : ∀ g, HasSum (fun n ↦ c n * (ψ n).val g) (Ψ.val g)) :
    HasSum (fun n ↦ c n • (hardySobolevTestAction μ m a b s hab hs (ψ n) :
        CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s))
      (hardySobolevTestAction μ m a b s hab hs Ψ :
        CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s) := by
  let τ := hardySobolevTranslation μ m a b s hab hs
  have hτ : Continuous (fun p : G × CompactIntervalSobolev μ L a b s ↦ τ p.1 p.2) :=
    (exists_hardySobolevTranslation μ m a b s hab hs).choose_spec.2
  have hcont (χ : BruhatCompactSupport G) : Continuous χ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp χ.property.1)
  have hint (χ : BruhatCompactSupport G) : Integrable χ.val μ :=
    (hcont χ).integrable_of_hasCompactSupport χ.property.2
  obtain ⟨M₀, hM₀, hbound⟩ :=
    exists_hardySobolevTestAction_norm_le_of_dominated μ m a b s hab hs φ
  have hτu (u : CompactIntervalSobolev μ L a b s) : Continuous (fun g : G ↦ τ g u) :=
    hτ.comp (Continuous.prodMk_left u)
  exact hasSum_smul_of_integral_series (μ := μ) (fun g ↦ τ g) (fun n ↦ (ψ n).val) Ψ.val c
    (fun n ↦ hardySobolevTestAction μ m a b s hab hs (ψ n))
    (hardySobolevTestAction μ m a b s hab hs Ψ) M₀ hc
    (fun n ↦ by
      have h := hbound (ψ n) 1 zero_le_one (fun g ↦ by simpa using hdom n g)
      simpa using h)
    (fun n u ↦ hardySobolev_eq_integral_translation_of_convolution μ m a b s hab hs (hint (ψ n))
      (ψ n).property.2 _ (hardySobolevTestAction_apply μ m a b s hab hs (ψ n)) u)
    (fun u ↦ hardySobolev_eq_integral_translation_of_convolution μ m a b s hab hs (hint Ψ)
      Ψ.property.2 _ (hardySobolevTestAction_apply μ m a b s hab hs Ψ) u)
    (fun n u ↦ by
      have h0 : HasCompactSupport (fun g ↦ (ψ n).val g • τ g u) :=
        (show HasCompactSupport (ψ n).val from (ψ n).property.2).smul_right
      exact ((hcont (ψ n)).smul (hτu u)).integrable_of_hasCompactSupport h0)
    (fun u g ↦ ‖φ.val g‖ * ‖τ g u‖)
    (fun u ↦ by
      have hcs : HasCompactSupport (fun g ↦ ‖φ.val g‖ * ‖τ g u‖) :=
        (show HasCompactSupport φ.val from φ.property.2).norm.mul_right
      exact ((hcont φ).norm.mul (hτu u).norm).integrable_of_hasCompactSupport hcs)
    (fun n u g ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hdom n g) (norm_nonneg _))
    hΨ

end Series

end RiemannMasullo.WeightedConvolution
