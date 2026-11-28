module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3_FractionalLineGram
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.GramTransport
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.LpCardinal

/-! # The actual line Sobolev space in fractional Fourier coordinates

The unrestricted Mellin probes are total and have the Gram kernel of an orthogonal
sum of fractional Fourier spaces. Their Gram correspondence gives a unitary map
that preserves every real-frequency observation.

The probe-separation argument adapts the degree-two work in PR #7537
(commit `ed4192ba9dee0d5e35f3942a4d71ec9c774f3edb`) to arbitrary `s > 1`.
-/

@[expose] public noncomputable section
open Filter Function MeasureTheory NumberField Set
open scoped InnerProductSpace NNReal NumberField.AdeleRing Topology
namespace RiemannMasullo.Isolated
set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "Ω" => PontryaginDual C₁
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => continuousIdeleClassNorm F
local notation "l𝔽" => logIdeleClassNorm F
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "ν𝔽" => canonicalModulatedHaar m𝔽 hm𝔽
local notation "W(" s ")" => CompactIntervalSobolev μ𝔽 l𝔽 (-0) 0 s
local notation "hI" => (show -(0 : ℝ) ≤ 0 by norm_num)

section FourierProbes

local notation "hms𝔽" => (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
local notation "lineI" => (show -(0 : ℝ) ≤ 0 by norm_num)
local notation "A(" s ", " hs ", " φ ")" =>
  hardySobolevTestAction μ𝔽 m𝔽 (-0) 0 s lineI (zero_le_one.trans (le_of_lt hs)) φ

/-- Every zero-width Sobolev vector of degree greater than one has its own
Haar-integrable representative, through the bounded inclusion with unchanged values. -/
private theorem fractionalLine_exists_L1 {s : ℝ} (hs : 1 < s) :
    ∃ J : W(s) →L[ℂ] Lp ℂ 1 μ𝔽, Injective J ∧
      ∀ u : W(s), Integrable (u : C𝔽 → ℂ) μ𝔽 ∧ (J u : C𝔽 → ℂ) =ᵐ[μ𝔽] (u : C𝔽 → ℂ) := by
  let P (ν : Measure C𝔽) := ∃ J : Lp ℂ 2 ν →L[ℂ] Lp ℂ 1 μ𝔽, Injective J ∧
    ∀ u : Lp ℂ 2 ν, Integrable (u : C𝔽 → ℂ) μ𝔽 ∧ (J u : C𝔽 → ℂ) =ᵐ[μ𝔽] (u : C𝔽 → ℂ)
  change P ((μ𝔽).withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity (-0) 0 s (l𝔽 x)))
  rw [neg_zero]
  rw [show ((μ𝔽).withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (l𝔽 x))) =
    sobolevMeasure μ𝔽 (modulatedSobolevWeight m𝔽) s from intervalSobolev_zero_eq_sobolevMeasure m𝔽 μ𝔽 s]
  obtain ⟨J, _, hi, _, _, hrep⟩ := modulatedSobolev_toL1 m𝔽 μ𝔽 hm𝔽 hms𝔽 hs
  exact ⟨J, hi, hrep⟩

/-- Positive-character Fourier evaluations on the full unitary dual are bounded
linear probes of the actual line Sobolev space. They separate points and
diagonalize its genuine compact-test action. -/
private theorem exists_fractionalLine_fourier_probes {s : ℝ} (hs : 1 < s) :
    ∃ E : PontryaginDual C𝔽 → StrongDual ℂ W(s),
      (∀ ψ u, E ψ u = ∫ g, u g * (ψ g : ℂ) ∂μ𝔽) ∧
      (∀ u, (∀ ψ, E ψ u = 0) → u = 0) ∧
      ∀ (φ : BruhatCompactSupport C𝔽) ψ u,
        E ψ (A(s, hs, φ) u) = (∫ g, φ.val g * (ψ g : ℂ) ∂μ𝔽) * E ψ u := by
  obtain ⟨J, hiJ, hJ⟩ := fractionalLine_exists_L1 (F := F) hs
  obtain ⟨T, hT, hiT, hTnorm⟩ := lcaFourier_L1 μ𝔽
  let evalₗ (ψ : PontryaginDual C𝔽) : W(s) →ₗ[ℂ] ℂ :=
    { toFun := fun u ↦ T (J u) ψ⁻¹
      map_add' := fun u v ↦ by simp
      map_smul' := fun c u ↦ by simp }
  let E (ψ : PontryaginDual C𝔽) : StrongDual ℂ W(s) :=
    (evalₗ ψ).mkContinuous ‖J‖ fun u ↦
      ((T (J u)).toBCF.norm_coe_le_norm ψ⁻¹).trans
        ((hTnorm (J u)).trans (J.le_opNorm u))
  have hstar (ψ : PontryaginDual C𝔽) (g : C𝔽) : star (ψ⁻¹ g : ℂ) = (ψ g : ℂ) := by
    change star (((ψ g)⁻¹ : Circle) : ℂ) = _
    rw [Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
  have hF (ψ : PontryaginDual C𝔽) (u : W(s)) : E ψ u = lcaFourier μ𝔽 u ψ⁻¹ := by
    change T (J u) ψ⁻¹ = _
    rw [hT]
    exact integral_congr_ae ((hJ u).2.mul EventuallyEq.rfl)
  have hpos (u : C𝔽 → ℂ) (ψ : PontryaginDual C𝔽) :
      lcaFourier μ𝔽 u ψ⁻¹ = ∫ g, u g * (ψ g : ℂ) ∂μ𝔽 := by simp only [lcaFourier, hstar]
  refine ⟨E, fun ψ u ↦ (hF ψ u).trans (hpos u ψ), ?_, ?_⟩
  · intro u hu
    apply hiJ
    apply hiT
    apply ZeroAtInftyContinuousMap.ext
    intro ψ
    have he := hu ψ⁻¹
    change T (J u) (ψ⁻¹)⁻¹ = 0 at he
    simpa using he
  · intro φ ψ u
    have hφ : Integrable φ.val μ𝔽 :=
      (continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)).integrable_of_hasCompactSupport
        φ.property.2
    rw [hF, hF, ← hpos]
    calc
      _ = lcaFourier μ𝔽 (lcaConvolution μ𝔽 φ.val u) ψ⁻¹ :=
        integral_congr_ae ((hardySobolevTestAction_apply μ𝔽 m𝔽 (-0) 0 s lineI _ φ u).mul EventuallyEq.rfl)
      _ = _ := congrFun (lcaFourier_convolution μ𝔽 hφ (hJ u).1) ψ⁻¹

end FourierProbes

variable {s : ℝ}
local notation "hs₀(" hs ")" => (show 0 ≤ s from by linarith [hs])
local notation "T(" hs ")" => (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-0) 0 s hI hs₀(hs)).exists.choose

/-- The unrestricted Mellin observation in the physical Sobolev space. -/
def fractionalLineWaveEval (hs : 1 < s) (η : PontryaginDual C𝔽) (t : ℝ) : StrongDual ℂ W(s) :=
  (T(hs)).symm (spectralLineFractionalWave hs η t)

/-- The physical observation is the unweighted positive-character Mellin integral. -/
theorem fractionalLineWaveEval_apply (hs : 1 < s) (η : PontryaginDual C𝔽) (t : ℝ) (u : W(s)) :
    fractionalLineWaveEval hs η t u = ∫ g, u g * spectralZeroJet η 0 t 0 g ∂μ𝔽 := by
  have hp := (spectralSobolevPairing_dual hI hs₀(hs) (fractionalLineWaveEval hs η t) u).2
  change fractionalLineWaveEval hs η t u = ∫ g, u g * T(hs) ((T(hs)).symm (spectralLineFractionalWave hs η t)) g ∂μ𝔽 at hp
  rw [(T(hs)).apply_symm_apply] at hp
  exact hp.trans (integral_congr_ae (EventuallyEq.rfl.mul
    (spectralLineFractionalWave_coeFn_haar hs η t)))

/-- The chart of any chosen unitary basepoint recovers every real-frequency physical wave. -/
private theorem fractionalJetCharacter_apply_of_chart (η : PontryaginDual C𝔽) (t : ℝ)
    (e : Multiplicative ℝ ≃ₜ* lcaAnnihilator (ideleClassNorm F).ker)
    (he : ∀ (v : ℝ) (g : C𝔽), (e (Multiplicative.ofAdd v)).val g = Circle.exp (v * l𝔽 g))
    (g : C𝔽) :
    ((η * (e (Multiplicative.ofAdd t)).val) g : ℂ) = spectralZeroJet η 0 t 0 g := by
  rw [spectralZeroJet_line_phase]
  change ((η g * (e (Multiplicative.ofAdd t)).val g : Circle) : ℂ) = _
  rw [he]

/-- As an entire family, the actual real-frequency evaluations from any choice of
angular basepoints separate the ambient Sobolev vectors. -/
theorem fractionalLineWaveEval_separates (hs : 1 < s) (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (u : W(s))
    (hu : ∀ ω t, fractionalLineWaveEval hs (χ ω) t u = 0) : u = 0 := by
  obtain ⟨E, hE, hsep, _⟩ := exists_fractionalLine_fourier_probes (F := F) (s := s) hs
  obtain ⟨e, he⟩ := exists_modulatedFrequencyLine m𝔽 hm𝔽
    (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  apply hsep u
  intro ψ
  let ω : PontryaginDual (ideleClassNorm F).ker := ψ.comp
    (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* C𝔽)
  have hk : (χ ω)⁻¹ * ψ ∈ lcaAnnihilator (ideleClassNorm F).ker := by
    rw [mem_lcaAnnihilator_iff]
    intro k
    have h := DFunLike.congr_fun (hχ ω) k
    change χ ω k.val = ψ k.val at h
    change (χ ω k.val)⁻¹ * ψ k.val = 1
    rw [h, inv_mul_cancel]
  let d : lcaAnnihilator (ideleClassNorm F).ker := ⟨_, hk⟩
  obtain ⟨τ, hτ⟩ := e.surjective d
  have ht : χ ω * (e τ).val = ψ := by
    rw [hτ]
    change χ ω * ((χ ω)⁻¹ * ψ) = ψ
    group
  have hphase (g : C𝔽) : (ψ g : ℂ) = spectralZeroJet (χ ω) 0 τ.toAdd 0 g := by
    exact (congrArg (fun ρ : PontryaginDual C𝔽 ↦ (ρ g : ℂ)) ht.symm).trans
      (fractionalJetCharacter_apply_of_chart (χ ω) τ.toAdd e he g)
  rw [hE]
  simpa only [fractionalLineWaveEval_apply, hphase] using hu ω τ.toAdd

/-- Each positive Mellin phase is a genuine member of the full unitary dual in
the sign and angular-frequency normalization used by the paper. -/
private theorem exists_fractionalJetCharacter (η : PontryaginDual C𝔽) (t : ℝ) :
    ∃ ψ : PontryaginDual C𝔽, ∀ g : C𝔽, (ψ g : ℂ) = spectralZeroJet η 0 t 0 g := by
  obtain ⟨e, he⟩ := exists_modulatedFrequencyLine m𝔽 hm𝔽
    (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  exact ⟨_, fractionalJetCharacter_apply_of_chart η t e he⟩

/-- At every frequency, the physical Mellin observation of the residual that
occurs in the geometric one-jet bound factors as the difference of multipliers
times the observed cardinal lift. This holds at every real frequency. -/
theorem fractionalLineWaveEval_residual (hs : 1 < s) (η : PontryaginDual C𝔽) (t : ℝ)
    (φ : BruhatCompactSupport C𝔽) (c : ℂ) (u : W(s)) :
    fractionalLineWaveEval hs η t (hardySobolevTestAction μ𝔽 m𝔽 (-0) 0 s hI hs₀(hs) φ u - c • u) =
      ((∫ g, φ.val g * spectralZeroJet η 0 t 0 g ∂μ𝔽) - c) * fractionalLineWaveEval hs η t u := by
  obtain ⟨ψ, hψ⟩ := exists_fractionalJetCharacter η t
  obtain ⟨E, hE, _, hA⟩ := exists_fractionalLine_fourier_probes (F := F) (s := s) hs
  have heq : E ψ = fractionalLineWaveEval hs η t := ContinuousLinearMap.ext fun v ↦ by
    rw [hE, fractionalLineWaveEval_apply]
    simp only [hψ]
  have h := hA φ ψ u
  rw [heq] at h
  simp only [hψ] at h
  rw [map_sub, map_smul, h, smul_eq_mul, sub_mul]

/-- Reciprocal-space duality followed by the positive-space Riesz map conjugates
the Gram of two actual Mellin waves. -/
theorem fractionalLineWaveEval_riesz_conj (hs : 1 < s) (η θ : PontryaginDual C𝔽) (u t : ℝ) :
    ⟪(InnerProductSpace.toDual ℂ W(s)).symm (fractionalLineWaveEval hs η u),
      (InnerProductSpace.toDual ℂ W(s)).symm (fractionalLineWaveEval hs θ t)⟫_ℂ =
      star ⟪spectralLineFractionalWave hs η u, spectralLineFractionalWave hs θ t⟫_ℂ := by
  let R := Lp ℂ 2 (intervalSobolevMeasure μ𝔽 l𝔽 (-0) 0 s true)
  let U := (T(hs)).symm.trans (InnerProductSpace.toDual ℂ W(s)).symm
  let x := spectralLineFractionalWave hs η u
  let y := spectralLineFractionalWave hs θ t
  change ⟪U x, U y⟫_ℂ = star ⟪x, y⟫_ℂ
  have hre (v w : R) : (⟪U v, U w⟫_ℂ).re = (⟪v, w⟫_ℂ).re := by
    change RCLike.re (⟪U v, U w⟫_ℂ) = RCLike.re (⟪v, w⟫_ℂ)
    rw [re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
      re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← U.map_add]
    simp only [U.norm_map]
  have hI' (v : R) : U (Complex.I • v) = -Complex.I • U v := by
    rw [U.map_smulₛₗ]
    rw [show (starRingEnd ℂ) Complex.I = -Complex.I from Complex.conj_I]
  apply Complex.ext
  · exact hre x y
  · have him := hre x (Complex.I • y)
    simp only [hI', inner_smul_right, neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg] at him
    exact him



local instance fractionalLineModelCanonicalHaar : (ν𝔽).IsHaarMeasure :=
  (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1

/-- The exact scale between physical Mellin evaluations and normalized Fourier synthesis. -/
def fractionalLineFourierScale : ℝ :=
  Real.sqrt (2 * Real.pi * (Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ))

/-- The Tamagawa normalization in the Fourier model is strictly positive. -/
theorem fractionalLineFourierScale_pos : 0 < fractionalLineFourierScale (F := F) := by
  unfold fractionalLineFourierScale
  apply Real.sqrt_pos.mpr
  have hc : 0 < (Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) := by
    exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν𝔽
  positivity

/-- The squared Fourier normalization is `2π` times the Tamagawa Haar scalar. -/
theorem fractionalLineFourierScale_sq :
    fractionalLineFourierScale (F := F) ^ 2 =
      2 * Real.pi * (Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) := by
  exact Real.sq_sqrt (by positivity)

/-- Positive-space Riesz probes use the conjugate Fourier phase of the reciprocal waves. -/
theorem fractionalLineWaveEval_riesz_inner (hs : 1 < s) (η : PontryaginDual C𝔽) (u t : ℝ) :
    ⟪(InnerProductSpace.toDual ℂ W(s)).symm (fractionalLineWaveEval hs η u),
      (InnerProductSpace.toDual ℂ W(s)).symm (fractionalLineWaveEval hs η t)⟫_ℂ =
      (Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) •
        ∫ x : ℝ, Complex.exp (↑((u - t) * x) * Complex.I) *
          (((1 + x ^ 2) ^ (-s / 2) : ℝ) : ℂ) := by
  rw [fractionalLineWaveEval_riesz_conj, spectralLineFractionalWave_inner,
    star_smul, star_trivial, Complex.star_def, ← integral_conj]
  congr 1
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    dsimp only
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    congr 2
    push_cast
    ring

/-- Different angular fibers of the physical Riesz probes are orthogonal. -/
theorem fractionalLineWaveEval_riesz_orthogonal (hs : 1 < s)
    (η θ : PontryaginDual C𝔽) (u t : ℝ) (k : C₁) (hne : η k.val ≠ θ k.val) :
    ⟪(InnerProductSpace.toDual ℂ W(s)).symm (fractionalLineWaveEval hs η u),
      (InnerProductSpace.toDual ℂ W(s)).symm (fractionalLineWaveEval hs θ t)⟫_ℂ = 0 := by
  rw [fractionalLineWaveEval_riesz_conj, spectralLineFractionalWave_inner_eq_zero hs η θ u t k hne,
    star_zero]

/-- The actual line Sobolev space is unitarily identified with the orthogonal sum of
fractional Fourier models, preserving every Mellin observation with its exact scale. -/
theorem exists_fractionalLineFourierEquiv (hs : 1 < s)
    (χ : Ω → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) :
    ∃ U : W(s) ≃ₗᵢ[ℂ] lp (fun _ : Ω ↦ Lp ℂ 2 (volume : Measure ℝ)) 2,
      ∀ ω t w, fractionalLineWaveEval hs (χ ω) t w =
        fractionalLineFourierScale (F := F) • fractionalSynthesis (s / 2) (U w ω) t := by
  classical
  let c := fractionalLineFourierScale (F := F)
  have hc : 0 < c := fractionalLineFourierScale_pos
  have hθ : 1 / 2 < s / 2 := by linarith
  let E (i : Ω × ℝ) := fractionalLineWaveEval hs (χ i.1) i.2
  let q (i : Ω × ℝ) : lp (fun _ : Ω ↦ Lp ℂ 2 (volume : Measure ℝ)) 2 :=
    lp.single (E := fun _ : Ω ↦ Lp ℂ 2 (volume : Measure ℝ)) 2 i.1 (c • fractionalProbe (s / 2) hθ i.2)
  have hE : ∀ w : W(s), (∀ i, E i w = 0) → w = 0 := by
    intro w hw
    exact fractionalLineWaveEval_separates hs χ hχ w (fun ω t ↦ hw (ω, t))
  have hq : ∀ w : lp (fun _ : Ω ↦ Lp ℂ 2 (volume : Measure ℝ)) 2,
      (∀ i, ⟪q i, w⟫_ℂ = 0) → w = 0 := by
    intro w hw
    apply lp.ext
    funext ω
    change w ω = 0
    apply fractionalProbe_separates hθ
    intro t
    have he := hw (ω, t)
    change ⟪lp.single (E := fun _ : Ω ↦ Lp ℂ 2 (volume : Measure ℝ)) 2 ω (c • fractionalProbe (s / 2) hθ t), w⟫_ℂ = 0 at he
    rw [lp.inner_single_left, inner_smul_left_eq_smul, smul_eq_zero] at he
    exact he.resolve_left hc.ne'
  have hgram : ∀ i j,
      ⟪(InnerProductSpace.toDual ℂ W(s)).symm (E i),
        (InnerProductSpace.toDual ℂ W(s)).symm (E j)⟫_ℂ = ⟪q i, q j⟫_ℂ := by
    rintro ⟨ω, u⟩ ⟨ζ, t⟩
    change ⟪(InnerProductSpace.toDual ℂ W(s)).symm (fractionalLineWaveEval hs (χ ω) u),
      (InnerProductSpace.toDual ℂ W(s)).symm (fractionalLineWaveEval hs (χ ζ) t)⟫_ℂ = _
    by_cases hω : ω = ζ
    · subst ζ
      rw [fractionalLineWaveEval_riesz_inner]
      change _ = ⟪lp.single (E := fun _ : Ω ↦ Lp ℂ 2 (volume : Measure ℝ)) 2 ω (c • fractionalProbe (s / 2) hθ u),
        lp.single (E := fun _ : Ω ↦ Lp ℂ 2 (volume : Measure ℝ)) 2 ω (c • fractionalProbe (s / 2) hθ t)⟫_ℂ
      rw [lp.inner_single_left, lp.single_apply_self, inner_smul_left_eq_smul,
        inner_smul_right_eq_smul, fractionalProbe_gram_angular hθ, smul_smul, smul_smul]
      have hc₂ : c * c = 2 * Real.pi * (Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) := by
        simpa only [c, pow_two] using fractionalLineFourierScale_sq (F := F)
      rw [hc₂]
      have hscale : (2 * Real.pi * (Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ)) * (2 * Real.pi)⁻¹ =
          (Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) := by field_simp
      rw [hscale]
      congr 3
      funext x
      rw [neg_div]
    · obtain ⟨k, hk⟩ : ∃ k : C₁, ω k ≠ ζ k := by
        by_contra! h
        exact hω (ContinuousMonoidHom.ext h)
      have hres (ξ : Ω) : χ ξ k.val = ξ k := DFunLike.congr_fun (hχ ξ) k
      rw [fractionalLineWaveEval_riesz_orthogonal hs (χ ω) (χ ζ) u t k
        (by simpa only [hres] using hk)]
      change 0 = ⟪lp.single (E := fun _ : Ω ↦ Lp ℂ 2 (volume : Measure ℝ)) 2 ω (c • fractionalProbe (s / 2) hθ u),
        lp.single (E := fun _ : Ω ↦ Lp ℂ 2 (volume : Measure ℝ)) 2 ζ (c • fractionalProbe (s / 2) hθ t)⟫_ℂ
      rw [lp.inner_single_left, lp.single_apply_ne _ _ _ hω, inner_zero_right]
  obtain ⟨U, hU⟩ := exists_linearIsometryEquiv_of_total_probe_gram E q hE hq hgram
  refine ⟨U, fun ω t w ↦ ?_⟩
  have he := hU (ω, t) w
  change fractionalLineWaveEval hs (χ ω) t w =
    ⟪lp.single (E := fun _ : Ω ↦ Lp ℂ 2 (volume : Measure ℝ)) 2 ω (c • fractionalProbe (s / 2) hθ t), U w⟫_ℂ at he
  rw [lp.inner_single_left, inner_smul_left_eq_smul, fractionalProbe_inner hθ] at he
  exact he


/-- A retained quotient coordinate pulls back to its unrestricted Mellin observation. -/
theorem fractionalLine_pulledCoordinate_eq_waveEval (hs : 1 < s) (hs₃ : s ≤ 3)
    (a : ℝ) (χ : Ω → PontryaginDual C𝔽) (j : SpectralStripJetIndex χ a 0 s)
    (f : StrongDual ℂ (spectralSobolevQuotient F a hI hs₀(hs)))
    (hf : spectralSobolevDualEmbedding F a hI hs₀(hs) f =
      (spectralStripJet_memLp χ (le_refl (0 : ℝ)) hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    f.comp (globalThetaSobolev F a hI hs₀(hs)).mkQL =
      fractionalLineWaveEval hs (χ j.val.1) j.val.2.2.1 := by
  apply (T(hs)).injective
  exact (hf.trans (spectralStripJet_eq_wave_line_fractional hs hs₃ χ j)).trans
    ((T(hs)).apply_symm_apply _).symm

end RiemannMasullo.Isolated
