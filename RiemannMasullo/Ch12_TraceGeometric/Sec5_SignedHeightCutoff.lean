module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5_SignedWidthLimit
import RiemannMasullo.Ch13_ZerosHecke.RationalExteriorZeros
import RiemannMasullo.AppB_AnalyticNT.Sec6
import RiemannMasullo.Ch10_TraceSpectral.Sec2_Basepoint
import RiemannMasullo.Ch10_TraceSpectral.Sec3_MellinDecay

/-! # Uniform height cutoffs for the signed local and global traces

In the chart normalized on the norm section, differentiating the physical test
along that section multiplies a spectral sample by its complex frequency.
This controls every height moment of the actual full-width trace. The
resulting error estimates apply to all strip widths and Sobolev orders.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b
  instSpectralQuotientPolynormableSec3 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSIdeleLocallyCompactSec1
  instSIdeleT2Sec4

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => continuousIdeleClassNorm F
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" ψ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) ψ) z
local notation "Sites(" χ ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  0 < order(χ z.1, shift(1 / 2 + z.2.1, z.2.2))}
local notation "mult(" χ ", " z ")" =>
  (order(χ (z).val.1, shift(1 / 2 + (z).val.2.1, (z).val.2.2))).untop₀.toNat
local notation "sample(" φ ", " χ ", " z ")" => modulatedFourierMellin m𝔽 univ
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽
  (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (χ (z).val.1)
    (shift((z).val.2.1, (z).val.2.2)))

local notation "FM(" φ ", " ψ ", " w ")" => modulatedFourierMellin m𝔽 univ
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽
  (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (F := F) ψ w)
local notation "wide(" φ ")" => halfTwistStripTrace (F := F) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  (by norm_num : (1 : ℝ) < 3) φ
local notation "omitted(" a ", " s ", " φ ", " χ ", " z ")" =>
  (((mult(χ, z) - spectralStripMultiplicity a s (z).val.2.1 (mult(χ, z)) : ℕ) : ℂ) * sample(φ, χ, z))

private theorem mellin_integral_eq (φ : BruhatCompactSupport C𝔽)
    (ψ : PontryaginDual C𝔽) (w : ℂ) :
    FM(φ, ψ, w) = ∫ x : C𝔽, φ.val x * ideleClassNormTwist (F := F) ψ w x ∂μ𝔽 := by
  simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]

private theorem exists_normMellinDerivative (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (n : ℕ) (φ : BruhatCompactSupport C𝔽) :
    ∃ f : BruhatCompactSupport C𝔽, ∀ ψ : PontryaginDual C𝔽, (∀ t, ψ (τ t) = 1) →
      ∀ w : ℂ, FM(f, ψ, w) = (-w) ^ n * FM(φ, ψ, w) := by
  induction n with
  | zero => exact ⟨φ, fun _ _ _ ↦ by simp⟩
  | succ n ih =>
    obtain ⟨f, hf⟩ := ih
    let b := τ.comp (positiveRealLogEquiv.symm : Multiplicative ℝ →ₜ* ℝ≥0ˣ)
    obtain ⟨f', hd⟩ := exists_bruhatCompactSupport_directionalMellinDerivative μ𝔽 b f
      (continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp f.property.1))
    refine ⟨f', fun ψ hp w ↦ ?_⟩
    let c : QuasiCharacter C𝔽 := ideleClassNormTwist (F := F) ψ w
    have hv := hasDerivAt_bruhatDirectionalDeriv b
      ((mem_bruhatSmoothSubmodule_iff _).mp (quasiCharacter_mem_bruhatSmooth c) 1) (1 : C𝔽)
    simp only [one_mul] at hv
    rw [show bruhatDirectionalDeriv b (fun x ↦ (c x : ℂ)) 1 = w from
      bruhatDirectionalDeriv_ideleClassNormTwist_normSection τ hτ ψ hp w] at hv
    rw [mellin_integral_eq, hd c w hv, ← mellin_integral_eq, hf ψ hp]
    ring

/-- Paper: §12.3, p. 514. In a chart normalized on the norm section, every
natural height moment of the absolute full trace series converges, jointly
over all angular components and all completed-Hecke zeros. -/
theorem summable_stripTrace_height_moments (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (hn : ∀ ω t, χ ω (τ t) = 1)
    (φ : BruhatCompactSupport C𝔽) (n : ℕ) :
    Summable (fun z : Sites(χ) ↦ |z.val.2.2| ^ n * ((mult(χ, z) : ℝ) * ‖sample(φ, χ, z)‖)) := by
  obtain ⟨f, hf⟩ := exists_normMellinDerivative τ hτ n φ
  have hsum := (hasSum_halfTwistStripTrace_full χ hχ f).summable.norm
  apply hsum.of_nonneg_of_le (fun z ↦ by positivity)
  intro z
  let w := shift(z.val.2.1, z.val.2.2)
  change _ ≤ ‖(mult(χ, z) : ℂ) * FM(f, χ z.val.1, w)‖
  rw [hf _ (hn _) w, norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_natCast]
  have him : w.im = z.val.2.2 := by simp [w]
  have he := pow_le_pow_left₀ (abs_nonneg _) (him ▸ Complex.abs_im_le_norm w) n
  calc
    _ ≤ ‖w‖ ^ n * ((mult(χ, z) : ℝ) * ‖sample(φ, χ, z)‖) :=
      mul_le_mul_of_nonneg_right he (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    _ = _ := by ring

/-- The low-height sum contains the literal signed omitted multiplicities. The
error bound is uniform in the strip half-width and Sobolev order. -/
theorem exists_height_bound_stripTrace_defect (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (hn : ∀ ω t, χ ω (τ t) = 1)
    (φ : BruhatCompactSupport C𝔽) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y → ∀ {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s),
      ‖wide(φ) - halfTwistStripTrace (F := F) ha hs φ -
        ∑' z : Sites(χ), if |z.val.2.2| ≤ Y then omitted(a, s, φ, χ, z) else 0‖ ≤ K / Y ^ n := by
  let M (z : Sites(χ)) := |z.val.2.2| ^ n * ((mult(χ, z) : ℝ) * ‖sample(φ, χ, z)‖)
  have hM : Summable M := summable_stripTrace_height_moments τ hτ χ hχ hn φ n
  have hM₀ (z : Sites(χ)) : 0 ≤ M z := by dsimp [M]; positivity
  refine ⟨∑' z, M z, tsum_nonneg hM₀, ?_⟩
  intro Y hY a s ha hs
  let f (z : Sites(χ)) := omitted(a, s, φ, χ, z)
  let A : Set (Sites(χ)) := {z | |z.val.2.2| ≤ Y}
  have h := hasSum_halfTwistStripTrace_defect χ hχ φ ha hs
  have hsplit := h.summable.indicator A
  have hhi (z : Sites(χ)) : ‖Aᶜ.indicator f z‖ ≤ M z / Y ^ n := by
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_notMem (not_not_intro hz)]; simpa using div_nonneg (hM₀ z) (pow_nonneg hY.le n)
    · rw [Set.indicator_of_mem hz, norm_mul, Complex.norm_natCast]
      have hy : Y ≤ |z.val.2.2| := (lt_of_not_ge hz).le
      have hmult : mult(χ, z) - spectralStripMultiplicity a s z.val.2.1 (mult(χ, z)) ≤ mult(χ, z) := Nat.sub_le _ _
      rw [le_div_iff₀ (pow_pos hY n), mul_comm]
      exact mul_le_mul (pow_le_pow_left₀ hY.le hy n)
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hmult) (norm_nonneg _)) (by positivity) (by positivity)
  have hMaj : Summable (fun z ↦ M z / Y ^ n) := hM.div_const _
  have habs := hMaj.of_nonneg_of_le (fun z ↦ norm_nonneg (Aᶜ.indicator f z)) hhi
  have he : (∑' z, Aᶜ.indicator f z) = wide(φ) - halfTwistStripTrace (F := F) ha hs φ - ∑' z, A.indicator f z := by
    rw [← h.tsum_eq, ← h.summable.tsum_sub hsplit]
    apply tsum_congr
    intro z
    by_cases hz : z ∈ A <;> simp [Set.indicator, hz, f]
  change ‖wide(φ) - halfTwistStripTrace (F := F) ha hs φ - ∑' z, A.indicator f z‖ ≤ _
  rw [← he]
  exact (norm_tsum_le_tsum_norm habs).trans ((habs.tsum_le_tsum hhi hMaj).trans_eq tsum_div_const)

/-- In a finite set of unitary rows, the classical zero-free region has common
constants for the rows and their inverses. Through height Y every positive zero
is strictly inside the stated centered strip. -/
theorem finite_hecke_rows_zeroFreeWidth (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (Ω : Finset (PontryaginDual C𝔽)) :
    ∃ A > 0, ∃ B : ℝ, 1 ≤ B ∧ ∀ Y : ℝ, 0 ≤ Y → ∀ z : Sites(χ),
      χ z.val.1 ∈ Ω → |z.val.2.2| ≤ Y → |z.val.2.1| < 1 / 2 - A / Real.log (B * (Y + 3)) := by
  obtain ⟨a, ha, hf⟩ := finiteHeckeL_zeroFreeRegion
  classical
  choose b hb hreg using hf F
  let E := Ω ∪ Ω.image (fun ψ ↦ ψ⁻¹)
  let B := max 1 (∑ ψ ∈ E, b ψ)
  have hbpos (ψ : PontryaginDual C𝔽) : 0 < b ψ := by linarith [hb ψ]
  have hbB {ψ : PontryaginDual C𝔽} (hm : ψ ∈ E) : b ψ ≤ B :=
    (Finset.single_le_sum (fun θ _ ↦ (hbpos θ).le) hm).trans (le_max_right _ _)
  let d := (Module.finrank ℚ F : ℝ) ^ 4
  have hd : 0 < d := pow_pos (Nat.cast_pos.mpr Module.finrank_pos) _
  have hright (ψ : PontryaginDual C𝔽) (hψ : ψ ∈ E) (w : ℂ) (hw : 0 < w.re)
      (ho : 0 < order(ψ, w)) (Y : ℝ) (hY : |w.im| ≤ Y) :
      w.re < 1 - (a / d) / Real.log (B * (Y + 3)) := by
    obtain ⟨L, hL, hSeries⟩ := finiteHeckeL_exists_continuation ψ
    have hp : 0 < Real.log (b ψ * (|w.im| + 3)) :=
      Real.log_pos (by nlinarith [hb ψ, mul_nonneg (hbpos ψ).le (abs_nonneg w.im)])
    have hm : Real.log (b ψ * (|w.im| + 3)) ≤ Real.log (B * (Y + 3)) := by
      apply Real.log_le_log (mul_pos (hbpos ψ) (by positivity))
      exact mul_le_mul (hbB hψ) (add_le_add_left hY 3) (by positivity) ((hbpos ψ).le.trans (hbB hψ))
    have hdiv := div_le_div_of_nonneg_left (div_nonneg ha.le hd.le) hp hm
    by_contra! h
    have hz : 1 - a / (d * Real.log (b ψ * (|w.im| + 3))) ≤ w.re := by
      rw [← div_div]; linarith
    have hle := hreg ψ L hL hSeries w hz
    rw [meromorphicOrderAt_finiteHeckeL_continuation ψ hL.meromorphicOn hSeries hw] at hle
    exact (not_le_of_gt ho) hle
  refine ⟨a / d, div_pos ha hd, B, le_max_left _ _, ?_⟩
  intro Y hY z hz hYz
  let ψ := χ z.val.1
  let w := shift(1 / 2 + z.val.2.1, z.val.2.2)
  have hi := abs_lt.mp (spectralStrip_zero_offset_lt_half χ z)
  have hre : w.re = 1 / 2 + z.val.2.1 := by simp [w]
  have him : w.im = z.val.2.2 := by simp [w]
  have hzero : 0 < order(ψ, w) := z.property
  have hψ : ψ ∈ E := Finset.mem_union_left _ hz
  have hD : ψ⁻¹ ∈ E := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hz, rfl⟩)
  obtain ⟨hL, he⟩ := continuedCompletedHeckeL_spec ψ
  obtain ⟨hI, hi'⟩ := continuedCompletedHeckeL_spec ψ⁻¹
  obtain ⟨ε, hε, hne, hfe⟩ := completedHeckeL_continuation_functionalEquation ψ _ _ hL he hI hi'
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL ψ⁻¹)
    (show AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) w by fun_prop)
    (show deriv (fun s : ℂ ↦ 1 - s) w ≠ 0 by simp)
  rw [show continuedCompletedHeckeL ψ⁻¹ ∘ (fun s : ℂ ↦ 1 - s) = ε * continuedCompletedHeckeL ψ
    from funext hfe, meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt _) (hne _)] at hcomp
  have hu := hright ψ hψ w (by linarith [hi.1]) hzero Y (him ▸ hYz)
  have hl := hright ψ⁻¹ hD (1 - w) (by simp only [Complex.sub_re, Complex.one_re]; linarith [hi.2])
    (hcomp ▸ hzero) Y (by simpa [him] using hYz)
  rw [Complex.sub_re, Complex.one_re] at hl
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- A fixed finite angular support gives an inverse-logarithmic strip schedule
and arbitrary power accuracy in the height cutoff. No density bound is used. -/
theorem finite_rows_stripTrace_logWidth (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (hn : ∀ ω t, χ ω (τ t) = 1) (φ : BruhatCompactSupport C𝔽)
    (Ω : Finset (PontryaginDual C𝔽)) (hΩ : ∀ z : Sites(χ), sample(φ, χ, z) ≠ 0 → χ z.val.1 ∈ Ω) :
    ∃ A > 0, ∃ B : ℝ, 1 ≤ B ∧ ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y →
      ∀ {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s), 1 / 2 - A / Real.log (B * (Y + 3)) ≤ a →
        ‖wide(φ) - halfTwistStripTrace (F := F) ha hs φ‖ ≤ K / Y ^ n := by
  obtain ⟨A, hA, B, hB, hZ⟩ := finite_hecke_rows_zeroFreeWidth χ Ω
  refine ⟨A, hA, B, hB, ?_⟩
  intro n
  obtain ⟨K, hK, herr⟩ := exists_height_bound_stripTrace_defect τ hτ χ hχ hn φ n
  refine ⟨K, hK, ?_⟩
  intro Y hY a s ha hs hw
  have hlow (z : Sites(χ)) : (if |z.val.2.2| ≤ Y then omitted(a, s, φ, χ, z) else 0) = 0 := by
    split_ifs with h
    · by_cases hz : sample(φ, χ, z) = 0
      · simp [hz]
      · have hi := (hZ Y hY.le z (hΩ z hz) h).trans_le hw
        rw [spectralStripMultiplicity_interior (abs_lt.mp hi), Nat.sub_self, Nat.cast_zero, zero_mul]
    · rfl
  simpa only [hlow, tsum_zero, sub_zero] using herr Y hY ha hs

private theorem finiteOrder_frequency_zero {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (ψ : PontryaginDual G) (hf : IsOfFinOrder ψ)
    (b : Multiplicative ℝ →ₜ* G) : bruhatDirectionalDeriv b (fun x : G ↦ (ψ x : ℂ)) 1 = 0 := by
  obtain ⟨n, hn, he⟩ := isOfFinOrder_iff_pow_eq_one.mp hf
  have hb (t : ℝ) : ψ (b (Multiplicative.ofAdd t)) = 1 := by
    let x := Multiplicative.ofAdd (t / n)
    have hx : x ^ n = Multiplicative.ofAdd t := by
      apply Multiplicative.toAdd.injective
      change n • (t / (n : ℝ)) = t
      rw [nsmul_eq_mul]
      field_simp
    have hv := congrArg (fun η : PontryaginDual G ↦ η (b x)) he
    rw [← hx, map_pow, map_pow]
    exact (ContinuousMonoidHom.pow_apply ψ n (b x)).symm.trans hv
  simp [bruhatDirectionalDeriv, hb]

/-- Every compact Bruhat test on the rational idele classes has only finitely
many angular rows with a nonzero Mellin sample, uniformly in the spectral point.
On a normalized rational row all Lie frequencies vanish by finite order. -/
theorem rat_finite_mellin_rows (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ)
    (hτ : RightInverse τ (ideleClassNorm ℚ)) (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 ℚ) ℚ)) :
    ∃ Ω : Finset (PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)),
      ∀ ψ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ), (∀ t, ψ (τ t) = 1) →
        ∀ w : ℂ, (∫ g, φ.val g * ideleClassNormTwist (F := ℚ) ψ w g ∂(ideleClassTamagawaMeasure ℚ)) ≠ 0 →
          ψ ∈ Ω := by
  classical
  let P := PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)
  let C := {ψ : P // ∀ t, ψ (τ t) = 1}
  obtain ⟨kg, hkg, hinv, -⟩ := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1 0
  obtain ⟨r, b, _, K, d, hcount⟩ := idelicExplicitFormula_normOneFourier_count τ hτ kg hkg
  let E := {ψ : C | (∀ u : (ideleClassNorm ℚ).ker, u.val ∈ kg → ψ.val u.val = 1) ∧
    ∀ i, ‖bruhatDirectionalDeriv (b i) (fun x ↦ (ψ.val x : ℂ)) 1‖ ≤ (0 : ℕ)}
  have hE : E.Finite := Set.finite_of_encard_le_coe (hcount 0)
  refine ⟨hE.toFinset.image Subtype.val, ?_⟩
  intro ψ hψ w hw
  have hf := isOfFinOrder_rat_of_trivial_on_normSection τ hτ ψ hψ
  refine Finset.mem_image.mpr ⟨⟨ψ, hψ⟩, hE.mem_toFinset.mpr ⟨?_, ?_⟩, rfl⟩
  · intro u hu
    exact bruhatCompactSupport_mellin_eq_one_on_period_of_ne_zero φ kg hkg hinv ψ w hw u.val hu
  · intro i
    simpa only [finiteOrder_frequency_zero (G := IdeleClassGroup (𝓞 ℚ) ℚ) ψ hf (b i), norm_zero, Nat.cast_zero] using (le_refl (0 : ℝ))

/-- A single finite-place lift realizes the signed full-width limit for any
compact Bruhat test and can be chosen to contain any prescribed finite places. -/
theorem exists_correctedSharpMass_tendsto_fullTrace (φ : BruhatCompactSupport C𝔽) (S₀ : Finset V) :
    ∃ (S : Finset V) (f : BruhatCompactSupport (SAdeleRing F S)ˣ), S₀ ⊆ S ∧
      (∀ g : (SAdeleRing F S)ˣ, HasSum (fun ξ : sProjectedDiagonal F S ↦ f.val (ξ.val * g))
        (φ.val (QuotientGroup.mk (sIdeleInsertion F S g)))) ∧
      Tendsto (fun R : ℝ ↦ -correctedSLocalTraceSharpMass φ f R) atTop (𝓝 wide(φ)) := by
  obtain ⟨S, B, hS₀, hPic, hRam, hOutside, hB, hS⟩ := exists_sLocalTrace_comparison_level φ S₀
  obtain ⟨f, hf⟩ := exists_sLocalTraceLift hPic φ hOutside
  refine ⟨S, f, hS₀, hf, ?_⟩
  simpa only [neg_neg] using
    (sLocalTraceSharpMass_tendsto_neg_halfTwistStripTrace φ hPic hRam hOutside hB hS f hf).neg

/-- Paper: §12.3, p. 514. For every compact Bruhat test and every number field,
one finite-place lift works for all widths, orders and height cutoffs. Its
signed defect at large finite local cutoff equals the low-height omitted sum
up to any inverse power of the height, uniformly in the width and order. -/
theorem exists_sharpMass_stripTrace_height_bound (φ : BruhatCompactSupport C𝔽) (S₀ : Finset V)
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (hn : ∀ ω t, χ ω (τ t) = 1) :
    ∃ (S : Finset V) (f : BruhatCompactSupport (SAdeleRing F S)ˣ), S₀ ⊆ S ∧
      (∀ g : (SAdeleRing F S)ˣ, HasSum (fun ξ : sProjectedDiagonal F S ↦ f.val (ξ.val * g))
        (φ.val (QuotientGroup.mk (sIdeleInsertion F S g)))) ∧
      ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y → ∀ᶠ R : ℝ in atTop,
        ∀ {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s),
          ‖-correctedSLocalTraceSharpMass φ f R - halfTwistStripTrace (F := F) ha hs φ -
            ∑' z : Sites(χ), if |z.val.2.2| ≤ Y then omitted(a, s, φ, χ, z) else 0‖ ≤ K / Y ^ n := by
  obtain ⟨S, f, hS, hf, hlim⟩ := exists_correctedSharpMass_tendsto_fullTrace φ S₀
  refine ⟨S, f, hS, hf, fun n ↦ ?_⟩
  obtain ⟨K, hK, hb⟩ := exists_height_bound_stripTrace_defect τ hτ χ hχ hn φ n
  refine ⟨1 + K, by linarith, fun Y hY ↦ ?_⟩
  filter_upwards [Metric.tendsto_nhds.mp hlim (1 / Y ^ n) (by positivity)] with R hR
  intro a s ha hs
  rw [dist_eq_norm] at hR
  have h := (norm_add_le _ _).trans (add_le_add hR.le (hb Y hY ha hs))
  rw [add_div]
  convert h using 2
  abel

/-- Paper: §12.3, p. 514. For an arbitrary compact Bruhat test on the rational
idele classes, the signed comparison at finite cutoff has arbitrary inverse
power accuracy in Y if the half-width is at least 1/2−A/log(B(Y+3)). The
cutoff is uniform in every such width and every Sobolev order greater than one.
The finite-place lift and the logarithmic schedule are independent of the power. -/
theorem rat_exists_sharpMass_stripTrace_logWidth (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 ℚ) ℚ))
    (S₀ : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ), S₀ ⊆ S ∧
      (∀ g : (SAdeleRing ℚ S)ˣ, HasSum (fun ξ : sProjectedDiagonal ℚ S ↦ f.val (ξ.val * g))
        (φ.val (QuotientGroup.mk (sIdeleInsertion ℚ S g)))) ∧
      ∃ A > 0, ∃ B : ℝ, 1 ≤ B ∧ ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y →
        ∀ᶠ R : ℝ in atTop, ∀ {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s),
          1 / 2 - A / Real.log (B * (Y + 3)) ≤ a →
            ‖-correctedSLocalTraceSharpMass φ f R - halfTwistStripTrace (F := ℚ) ha hs φ‖ ≤ K / Y ^ n := by
  let q : IdeleGroup (𝓞 ℚ) ℚ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ := q.comp ⟨canonicalIdeleNormSection ℚ, canonicalIdeleNormSection_continuous ℚ⟩
  have hτ : RightInverse τ (ideleClassNorm ℚ) := canonicalIdeleNormSection_rightInverse ℚ
  obtain ⟨χ, hχ, hn, -⟩ := exists_spectralBasepointChoice_of_normSection τ hτ
  obtain ⟨Ω, hΩ⟩ := rat_finite_mellin_rows τ hτ φ
  obtain ⟨A, hA, B, hB, hb⟩ := finite_rows_stripTrace_logWidth τ hτ χ hχ hn φ Ω
    (fun z hz ↦ hΩ _ (hn _) _ (by rwa [← mellin_integral_eq]))
  obtain ⟨S, f, hS, hf, hlim⟩ := exists_correctedSharpMass_tendsto_fullTrace φ S₀
  refine ⟨S, f, hS, hf, A, hA, B, hB, fun n ↦ ?_⟩
  obtain ⟨K, hK, hwidth⟩ := hb n
  refine ⟨1 + K, by linarith, fun Y hY ↦ ?_⟩
  filter_upwards [Metric.tendsto_nhds.mp hlim (1 / Y ^ n) (by positivity)] with R hR
  intro a s ha hs hw
  rw [dist_eq_norm] at hR
  have h := (norm_add_le _ _).trans (add_le_add hR.le (hwidth Y hY ha hs hw))
  rw [add_div]
  convert h using 2
  abel

end RiemannMasullo
