module

public import RiemannMasullo.AppB_AnalyticNT.Sec4_RealEvenUpperPV
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatPhysicalDilation
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatHeatCosineLimit

/-!
# The Gaussian trace of the rational real-even Paley–Wiener level

Reconstruction of the flat order-zero real block of Theorem 12.4.1.1,
pp. 515–519, following mrshu's issue #7354 calculation. The sharp
spatial interval is `(h,L]`, the frequency interval is `(0,B]`, and the
compact radial test has support strictly above dilation one. Its value at
one is zero. Removing the band mean subtracts its negative half-moment
from the real additive principal value.
-/

open Filter MeasureTheory NumberField Set
open scoped CompactlySupported NNReal Topology

@[expose] public noncomputable section

namespace RiemannMasullo.FlatPolar

/-- The orbital value of a compact continuous profile supported above one has the
ordinary even real-place density, including both signs of the real coordinate. -/
theorem compactCosineOrbitalValue_eq_upperDensity (φ : C_c(ℝ≥0ˣ, ℂ)) {η : ℝ} (hη : 0 < η)
    (hs : ∀ a ∈ tsupport φ, 1 + η ≤ (a.val : ℝ)) :
    compactCosineOrbitalValue φ 1 = ∫ a : ℝ≥0ˣ, φ a *
      (((a.val : ℝ) * Real.sqrt a.val / ((a.val : ℝ) ^ 2 - 1) : ℝ) : ℂ) ∂positiveRealHaar := by
  rw [compactCosineOrbitalValue]
  apply integral_congr_ae
  filter_upwards with a
  rw [mul_one]
  by_cases ha : a ∈ tsupport φ
  · rw [finiteCosineDilationValue_of_one_lt ((lt_add_of_pos_right 1 hη).trans_le (hs a ha))]
  · simp [image_eq_zero_of_notMem_tsupport ha]

/-- On a window strictly above one the real-even cosine orbital integral is the
actual ordinary real-place Connes–Weil principal value of every matching Bruhat test. -/
theorem compactCosineOrbitalValue_eq_realPrincipalValue {F : Type*} [Field F] [NumberField F]
    (w : InfinitePlace F) (hw : w.IsReal) (φ : C_c(ℝ≥0ˣ, ℂ)) {η : ℝ} (hη : 0 < η)
    (hs : ∀ a ∈ tsupport φ, 1 + η ≤ (a.val : ℝ)) (test : BruhatCompactSupport w.Completionˣ)
    (hm : ∀ (u : w.Completionˣ) (a : ℝ≥0ˣ), (a.val : ℝ) = ‖u.val‖ → test.val u = φ a) :
    compactCosineOrbitalValue φ 1 = infiniteConnesWeilPrincipalValue w test := by
  have hz (a : ℝ≥0ˣ) (ha : (a.val : ℝ) < 1 + η) : φ a = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hu ↦ (not_lt_of_ge (hs a hu)) ha)
  rw [realConnesWeilPrincipalValue_eq_upper_compactProfile w hw φ (lt_add_of_pos_right 1 hη) hz test hm,
    compactCosineOrbitalValue_eq_upperDensity φ hη hs]

/-- The *Hilbert trace* of the true mean-zero compression converges, along the
joint cutoff and heat prescription, to the orbital integral minus the negative half-moment. -/
theorem tendsto_meanZeroCompactCosine_heatTrace {ι : Type*} {l : Filter ι}
    {B h L : ι → ℝ} {τ : ι → ℝ≥0} (hB : ∀ i, 0 < B i) (hh : ∀ᶠ i in l, 0 ≤ h i)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hBL : Tendsto (fun i ↦ B i * L i) l atTop)
    (hτ : Tendsto τ l (𝓝 0))
    (hw : Tendsto (fun i ↦ (τ i : ℝ) * Real.log (B i * L i)) l (𝓝 0))
    (φ : C_c(ℝ≥0ˣ, ℂ)) {η M : ℝ} (hη : 0 < η)
    (hs : ∀ a ∈ tsupport φ, (a.val : ℝ) ∈ Icc (1 + η) M) :
    Tendsto (fun i ↦ hilbertTrace (logHeatSandwich (τ i)
      (meanZeroCompactCosineTraceOperator (h i) (L i) (B i) φ))) l
      (𝓝 (compactCosineOrbitalValue φ 1 - ∫ a : ℝ≥0ˣ, φ a / (Real.sqrt a.val : ℂ) ∂positiveRealHaar)) := by
  apply tendsto_meanZeroCompactCosine_heatTrace_of_ambient hB hBh hBL hτ φ
    (fun a ha ↦ (le_add_of_nonneg_right hη.le).trans (hs a ha).1)
  apply tendsto_hilbertTrace_logHeatSandwich_compactCosineTraceOperator φ hη hs
    (hh.mono fun i hi ↦ ⟨hi, hB i⟩) hBh hBL _ hw
  exact_mod_cast (NNReal.continuous_coe.tendsto 0).comp hτ

/-- For each compact continuous complex test supported strictly above one, the
integrated physical log-Haar diagonal of the orthogonal compression converges to
the even orbital integral minus the negative half-moment. -/
theorem tendsto_physicalHaarHeatKernel_meanZeroCompactCosineTrace
    {ι : Type*} {l : Filter ι} {B h L : ι → ℝ} {τ : ι → ℝ≥0}
    (hB : ∀ i, 0 < B i) (hh : ∀ᶠ i in l, 0 ≤ h i)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hBL : Tendsto (fun i ↦ B i * L i) l atTop)
    (hpos : ∀ᶠ i in l, 0 < τ i) (hτ : Tendsto τ l (𝓝 0))
    (hw : Tendsto (fun i ↦ (τ i : ℝ) * Real.log (B i * L i)) l (𝓝 0))
    (φ : C_c(ℝ≥0ˣ, ℂ)) {η M : ℝ} (hη : 0 < η)
    (hs : ∀ a ∈ tsupport φ, (a.val : ℝ) ∈ Icc (1 + η) M) :
    let Q (i : ι) := physicalMeanZeroBandProjection (B i)
    let T (i : ι) := (Q i).comp ((spatialCutoff (h i) (L i)).comp ((compactInverseDilationAction φ).comp (Q i)))
    Tendsto (fun i ↦ ∫ t : ℝ, haarHeatKernel (τ i) (T i) t t) l
      (𝓝 ((∫ a : ℝ≥0ˣ, φ a * (((a.val : ℝ) * Real.sqrt a.val / ((a.val : ℝ) ^ 2 - 1) : ℝ) : ℂ) ∂positiveRealHaar) -
        ∫ a : ℝ≥0ˣ, φ a / (Real.sqrt a.val : ℂ) ∂positiveRealHaar)) := by
  dsimp only
  rw [← compactCosineOrbitalValue_eq_upperDensity φ hη (fun a ha ↦ (hs a ha).1)]
  apply (tendsto_meanZeroCompactCosine_heatTrace hB hh hBh hBL hτ hw φ hη hs).congr'
  filter_upwards [hpos] with i hi
  exact (haarHeatKernel_physicalMeanZeroCompact_diagonal_trace hi _ _ _ φ).2.symm

/-- The integrated physical log-Haar diagonal of the cosine-conjugated real-even
mean-zero compression tends to the normalized principal value less the split polar
correction. Positive variances are required only eventually. -/
theorem tendsto_physicalHaarHeatKernel_meanZeroCompactCosineTrace_realPV
    {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hreal : w.IsReal)
    {ι : Type*} {l : Filter ι} {B h L : ι → ℝ} {τ : ι → ℝ≥0}
    (hB : ∀ i, 0 < B i) (hh : ∀ᶠ i in l, 0 ≤ h i)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hBL : Tendsto (fun i ↦ B i * L i) l atTop)
    (hpos : ∀ᶠ i in l, 0 < τ i) (hτ : Tendsto τ l (𝓝 0))
    (hw : Tendsto (fun i ↦ (τ i : ℝ) * Real.log (B i * L i)) l (𝓝 0))
    (φ : C_c(ℝ≥0ˣ, ℂ)) {η M : ℝ} (hη : 0 < η)
    (hs : ∀ a ∈ tsupport φ, (a.val : ℝ) ∈ Icc (1 + η) M) (test : BruhatCompactSupport w.Completionˣ)
    (hm : ∀ (u : w.Completionˣ) (a : ℝ≥0ˣ), (a.val : ℝ) = ‖u.val‖ → test.val u = φ a) :
    let Q (i : ι) := physicalMeanZeroBandProjection (B i)
    let T (i : ι) := (Q i).comp ((spatialCutoff (h i) (L i)).comp ((compactInverseDilationAction φ).comp (Q i)))
    Tendsto (fun i ↦ ∫ t : ℝ, haarHeatKernel (τ i) (T i) t t) l
      (𝓝 (infiniteConnesWeilPrincipalValue w test -
        ∫ a : ℝ≥0ˣ, φ a / (Real.sqrt a.val : ℂ) ∂positiveRealHaar)) := by
  dsimp only
  rw [← compactCosineOrbitalValue_eq_realPrincipalValue w hreal φ hη (fun a ha ↦ (hs a ha).1) test hm,
    compactCosineOrbitalValue_eq_upperDensity φ hη (fun a ha ↦ (hs a ha).1)]
  exact tendsto_physicalHaarHeatKernel_meanZeroCompactCosineTrace hB hh hBh hBL hpos hτ hw φ hη hs

end RiemannMasullo.FlatPolar
