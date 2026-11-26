module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_RadialPrimeTrace
public import RiemannMasullo.Ch12_TraceGeometric.Sec3_ShrinkingPrimePower
import RiemannMasullo.Ch12_TraceGeometric.Sec3_RationalDensityComparison
import RiemannMasullo.ForMathlib.Analysis.Fourier.SparseLaplaceProbe

/-! # Exact signed trace comparison on localized rational prime-power tests

At a fixed positive strip width, a sublinear exterior zero count allows one to
annihilate every omitted Mellin sample while prescribing the value at a physical
prime power. The pole and infinite-place functionals are killed separately.
-/

@[expose] public noncomputable section

open Classical Filter MeasureTheory Set NumberField
open scoped ArithmeticFunction ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.RationalWidthLoss

set_option quotPrecheck false

local notation "Ext(" δ ")" => {ρ : zeroSites // (δ : ℝ) ≤ |ρ.val.re - 1 / 2|}

private theorem summable_inverse_height_of_right_density {δ σ q C : ℝ}
    (hδ' : σ ≤ 1/2+δ) (hq' : q < 1) (hC : 0 ≤ C) (hd : HasRightDensity σ q C) :
    Summable (fun ρ : Ext(δ) ↦ 1 / (1 + |ρ.val.val.im|)) := by
  let m (ρ : zeroSites) : ℝ := if δ ≤ |ρ.val.re - 1 / 2| then 1 else 0
  have hm (ρ) : 0 ≤ m ρ := by dsimp [m]; split <;> norm_num
  have hcount := weighted_count_of_right_density hd m (fun ρ ↦ by
    have hp : 1 ≤ multiplicity ρ := Int.pos_iff_toNat_pos.mp ρ.property
    dsimp [m]; split
    · exact_mod_cast hp
    · positivity) (fun ρ hl hr ↦ by
      have hi : |ρ.val.re - 1 / 2| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
      exact ite_eq_right hi.not_ge)
  have hs := summable_height_moment_of_log_count (fun ρ : zeroSites ↦ ρ.val.im) m hm
    (r := 1) zero_le_one hq' (mul_nonneg (by norm_num) hC) 5 hcount
  exact (hs.subtype _).congr fun ρ ↦ by simp only [m, ite_eq_left ρ.property, Real.rpow_one, Function.comp_apply]

/-- Ingham's positive-height density estimate implies summability of inverse first
heights on both closed exterior bands, even for an arbitrarily small positive width. -/
theorem summable_exterior_inverse_height (hI : InghamDensity) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun ρ : Ext(δ) ↦ 1 / (1 + |ρ.val.val.im|)) := by
  let σ := min (3 / 4) (1 / 2 + δ)
  have hσ : 1 / 2 < σ := lt_min (by norm_num) (by linarith)
  have hσ' : σ ≤ 3 / 4 := min_le_left _ _
  have hδ' : σ ≤ 1 / 2 + δ := min_le_right _ _
  let q := 3 * (1 - σ) / (2 - σ)
  have hden : 0 < 2 - σ := by linarith
  have hq : 0 ≤ q := div_nonneg (mul_nonneg (by norm_num) (by linarith)) hden.le
  have hq' : q < 1 := (div_lt_iff₀ hden).mpr (by linarith)
  obtain ⟨C₀, hC₀, hd₀⟩ := hI σ hσ hσ'
  obtain ⟨C, hC, hd⟩ := hasRightDensity_of_positiveHeight hq hC₀ hd₀
  exact summable_inverse_height_of_right_density hδ' hq' hC hd

/-- The two closed exterior bands have summable inverse first heights at every
positive lower width. This follows from the power saving for the ordinary zeta
function and the functional equation. -/
theorem summable_exterior_inverse_height_unconditional {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun ρ : Ext(δ) ↦ 1 / (1 + |ρ.val.val.im|)) := by
  let d := min δ (1/2)
  have hd : 0 < d := lt_min hδ (by norm_num)
  obtain ⟨C,hC,h⟩ := exists_rightDensity_power hd (min_le_right _ _)
  exact summable_inverse_height_of_right_density (by dsimp [d]; linarith [min_le_left δ (1/2:ℝ)])
    (by nlinarith [sq_pos_of_pos hd]) hC h

private theorem exists_arch_probe {δ : ℝ}
    (hs : Summable (fun ρ : Ext(δ) ↦ 1 / (1 + |ρ.val.val.im|)))
    (c : ℝ) {ε : ℝ} (hε : 0 < ε) (v : Fin 4 → ℂ) :
    ∃ G : ℝ → ℂ, ContDiff ℝ (∞) G ∧ tsupport G ⊆ Icc (c - ε) (c + ε) ∧ G c = 1 ∧
      (∀ j : Fin 4, bilateralLaplace G (j.val : ℂ) = v j) ∧
      ∀ ρ : Ext(δ), bilateralLaplace G ρ.val.val = 0 ∧ bilateralLaplace G (ρ.val.val + 2) = 0 := by
  let w : Ext(δ) ⊕ Ext(δ) → ℂ := Sum.elim (fun ρ ↦ ρ.val.val) (fun ρ ↦ ρ.val.val + 2)
  let r (j : Fin 4) : ℝ := j.val
  have hsum : Summable (fun i ↦ 1 / (1 + |(w i).im|)) := by
    apply Summable.sum _ hs
    simpa [Function.comp_def, w] using hs
  have hr : Function.Injective r := fun _ _ h ↦ Fin.ext (Nat.cast_injective h)
  have hw (i) (j : Fin 4) : w i ≠ r j := by
    intro he
    have hh := congrArg Complex.re he
    rcases i with ρ | ρ <;> have ⟨hl, hu⟩ := re_mem_Ioo ρ.val <;>
      fin_cases j <;> norm_num [w, r] at hh <;> linarith
  have hne (i) : w i ≠ ((-1 : ℝ) : ℂ) := by
    rcases i with ρ | ρ <;> intro he <;> have hh := congrArg Complex.re he <;>
      simp [w] at hh <;> linarith [(re_mem_Ioo ρ.val).1]
  obtain ⟨G, hg, hb, hc, hz, hM⟩ := SparseLaplace.exists_interpolating_probe
    w hsum r hr hw (-1) hne (fun j ↦ by dsimp [r]; linarith [Nat.cast_nonneg (α := ℝ) j.val]) v c hε
  exact ⟨G, hg, hb, hc, fun j ↦ by simpa only [r, Complex.ofReal_natCast] using hM j,
    fun ρ ↦ ⟨hz (.inl ρ), hz (.inr ρ)⟩⟩

private def archFactor (x : ℝ) : ℂ := (Real.exp (x / 2) : ℂ) * ((Real.exp (2 * x) : ℂ) - 1)

private theorem archFactor_ne {x : ℝ} (hx : 0 < x) : archFactor x ≠ 0 := by
  have h : 1 < Real.exp (2 * x) := Real.one_lt_exp_iff.mpr (by positivity)
  unfold archFactor
  exact mul_ne_zero (by exact_mod_cast (Real.exp_pos _).ne') (sub_ne_zero.mpr (by exact_mod_cast h.ne'))

private theorem archFactor_smooth : ContDiff ℝ (∞) archFactor :=
  (Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ (∞) (fun x : ℝ ↦ Real.exp (x / 2)))).mul
    ((Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ (∞) (fun x : ℝ ↦ Real.exp (2 * x)))).sub
      contDiff_const)

private theorem archFactor_transform (G : ℝ → ℂ) (hg : Continuous G) (hk : HasCompactSupport G)
    (z : ℂ) : bilateralLaplace (fun x ↦ archFactor x * G x) z =
      bilateralLaplace G (z + 5 / 2) - bilateralLaplace G (z + 1 / 2) := by
  let f (u : ℂ) (x : ℝ) := G x * Complex.exp (u * x)
  have hf (u : ℂ) : Integrable (f u) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hk.mul_right
  unfold bilateralLaplace
  rw [← integral_sub (hf (z + 5 / 2)) (hf (z + 1 / 2))]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [archFactor, f, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_mul]
  rw [show (z + 5 / 2) * (x : ℂ) = (x / 2 : ℂ) + 2 * x + z * x by ring,
    show (z + 1 / 2) * (x : ℂ) = (x / 2 : ℂ) + z * x by ring]
  simp only [Complex.exp_add]
  ring

private theorem archFactor_cancels {x : ℝ} (hx : 0 < x) :
    (Real.exp (-x / 2) : ℂ) * archFactor x / ((Real.exp (2 * x) : ℂ) - 1) = 1 := by
  have hn : (Real.exp (2 * x) : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by
    exact_mod_cast (Real.one_lt_exp_iff.mpr (by positivity : 0 < 2 * x)).ne')
  rw [archFactor, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
    show -x / 2 + x / 2 = 0 by ring, Real.exp_zero, Complex.ofReal_one, one_mul, div_self hn]

/-- The physical value at a positive log site, both polar moments, and the real-place
remainder can be prescribed independently of the exterior zero samples. The one
spectral hypothesis is summability of inverse heights outside the fixed band. -/
theorem exists_exterior_annihilating_prime_probe {δ : ℝ}
    (hs : Summable (fun ρ : Ext(δ) ↦ 1 / (1 + |ρ.val.val.im|)))
    {c ε : ℝ} (hε : 0 < ε) (hc : ε < c) (P M A : ℂ) :
    ∃ H : ℝ → ℂ, ContDiff ℝ (∞) H ∧ tsupport H ⊆ Icc (c - ε) (c + ε) ∧ H c = 1 ∧
      bilateralLaplace H (1 / 2) = P ∧ bilateralLaplace H (-(1 / 2)) = M ∧
      (∫ x in Ioi (0 : ℝ), (Real.exp (-x / 2) : ℂ) * H x / ((Real.exp (2 * x) : ℂ) - 1)) = A ∧
      ∀ ρ : Ext(δ), bilateralLaplace H (ρ.val.val - 1 / 2) = 0 := by
  let B := archFactor c
  have hB : B ≠ 0 := archFactor_ne (hε.trans hc)
  let v : Fin 4 → ℂ := ![B * A, 0, B * (M + A), B * P]
  obtain ⟨G, hg, hG, hGc, hv, hz⟩ := exists_arch_probe hs c hε v
  have hk : HasCompactSupport G := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hG
  let H (x : ℝ) := B⁻¹ * (archFactor x * G x)
  have ht (z : ℂ) : bilateralLaplace H z =
      B⁻¹ * (bilateralLaplace G (z + 5 / 2) - bilateralLaplace G (z + 1 / 2)) := by
    rw [← archFactor_transform G hg.continuous hk]
    simp only [H, bilateralLaplace, mul_assoc, integral_const_mul]
  have h₀ : bilateralLaplace G 0 = B * A := by simpa [v] using hv 0
  have h₁ : bilateralLaplace G 1 = 0 := by simpa [v] using hv 1
  have h₂ : bilateralLaplace G 2 = B * (M + A) := by simpa [v] using hv 2
  have h₃ : bilateralLaplace G 3 = B * P := by simpa [v] using hv 3
  refine ⟨H, contDiff_const.mul (archFactor_smooth.mul hg),
    tsupport_mul_subset_right.trans (tsupport_mul_subset_right.trans hG), by change B⁻¹ * (B * G c) = 1; rw [hGc, mul_one, inv_mul_cancel₀ hB],
    ?_, ?_, ?_, fun ρ ↦ ?_⟩
  · rw [ht]; norm_num [h₁, h₃, ← mul_assoc, hB]
  · rw [ht]; norm_num [h₀, h₂]; field_simp; ring
  · have he : (∫ x in Ioi (0 : ℝ), (Real.exp (-x / 2) : ℂ) * H x / ((Real.exp (2 * x) : ℂ) - 1)) =
        ∫ x in Ioi (0 : ℝ), B⁻¹ * G x := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
      calc _ = B⁻¹ * G x * ((Real.exp (-x / 2) : ℂ) * archFactor x / ((Real.exp (2 * x) : ℂ) - 1)) := by
            dsimp only [H]; ring
        _ = _ := by rw [archFactor_cancels hx, mul_one]
    rw [he, integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (f := G) (fun x hx ↦
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (show 0 < x by linarith [(hG h).1])))]
    simpa [bilateralLaplace, ← mul_assoc, hB] using congrArg (fun u : ℂ ↦ B⁻¹ * u) h₀
  · rw [ht, show ρ.val.val - 1 / 2 + 5 / 2 = ρ.val.val + 2 by ring,
      sub_add_cancel, (hz ρ).1, (hz ρ).2, sub_zero, mul_zero]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instFiniteCompletionUnitsLocallyCompactSec4b instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSIdeleLocallyCompactSec1 instSIdeleT2Sec4

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Pl" => IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)
local notation "V" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "Z" => {z : ℂ // 0 < MeromorphicOn.divisor completedRiemannZeta univ z}
local notation "band(" ha ")" => (neg_nonpos.mpr ha |>.trans ha)
local notation "Q(" ha ", " hs ")" => spectralSobolevQuotient ℚ (1 / 2) (band(ha)) (zero_lt_one.trans hs).le
local notation "radial(" φ ", " H ")" => ∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x =
  (H : ℝ → ℂ) (Real.log ((ideleClassNorm ℚ x : ℝ≥0) : ℝ))
local notation "lifts(" S ", " f ", " φ ")" => ∀ g : (SAdeleRing ℚ S)ˣ,
  HasSum (fun ξ : sProjectedDiagonal ℚ S ↦ (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ).val (ξ.val * g))
    ((φ : BruhatCompactSupport Cℚ).val (QuotientGroup.mk (sIdeleInsertion ℚ S g)))
local notation "pole(" φ ", " z ")" => modulatedFourierMellin (continuousIdeleClassNorm ℚ) univ
  ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
  (ideleClassTamagawaMeasure ℚ) (φ : BruhatCompactSupport Cℚ).val (ideleClassNormTwist 1 z)
local notation "rep(" T ", " φ ", " ha ", " hs ")" =>
  (T : nuclearEndomorphisms Q(ha, hs)).val =
    spectralConvolution (F := ℚ) (1 / 2) (band(ha)) (zero_lt_one.trans hs).le φ

private theorem trace_eq_of_annihilating {δ a s : ℝ} (hδ : δ ≤ a) (ha : 0 ≤ a) (hs : 1 < s)
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0)
    (hz : ∀ ρ : Ext(δ), bilateralLaplace H (ρ.val.val - 1 / 2) = 0)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, H))
    (T : nuclearEndomorphisms Q(ha, hs)) (hT : rep(T, φ, ha, hs)) :
    hilbertTrace T = V * centeredVonMangoldtValue H := by
  have he := (hasSum_centeredVonMangoldt_sub_radialStripTrace H hH hc hp φ hφ ha hs T hT).tsum_eq
  apply Eq.symm
  apply sub_eq_zero.mp
  rw [← he]
  rw [← tsum_zero (β := Z) (α := ℂ)]
  apply tsum_congr
  intro z
  by_cases hb : δ ≤ |z.val.re - 1 / 2|
  · have hpos := z.property
    have hm : z.val ∈ zeroSites := by
      change 0 < MeromorphicOn.divisor (continuedCompletedHeckeL (F := ℚ) 1) univ z.val
      rwa [principal_divisor_eq_completedRiemannZeta]
    have hsample : bilateralLaplace H (z.val - 1 / 2) = 0 := hz ⟨⟨z.val, hm⟩, hb⟩
    rw [hsample, mul_zero, mul_zero]
  · rw [spectralStripMultiplicity_interior (abs_lt.mp ((lt_of_not_ge hb).trans_le hδ))]
    simp

/-- A rational radial test annihilating the closed exterior has its full signed trace at every larger width. -/
theorem hilbertTrace_eq_centered_of_exterior_vanishing {δ a s : ℝ} (hδ : δ ≤ a) (ha : 0 ≤ a) (hs : 1 < s)
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0)
    (hz : ∀ ρ : Ext(δ), bilateralLaplace H (ρ.val.val - 1 / 2) = 0)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, H))
    (T : nuclearEndomorphisms Q(ha, hs)) (hT : rep(T, φ, ha, hs)) :
    hilbertTrace T = V * centeredVonMangoldtValue H :=
  trace_eq_of_annihilating hδ ha hs H hH hc hp hz φ hφ T hT

private theorem radial_pole_eq (H : ℝ → ℂ) (hH : Continuous H) (φ : BruhatCompactSupport Cℚ)
    (hφ : radial(φ, H)) (z : ℂ) : pole(φ, z) = V * bilateralLaplace H z := by
  rw [normTest_mellin H hH φ hφ]
  have h := grh_shift_integral H hH (fun _ ↦ (1 : ℂ)) (fun _ ↦ rfl) 0 z
  simpa [bilateralLaplace] using congrArg (fun u : ℂ ↦ V * u) h

private theorem single_weighted_sample {n : ℕ} (hn : 0 < n) {c r : ℝ}
    (hc : c = Real.log n) (hiso : ∀ m : ℕ, 0 < m → |Real.log (m : ℝ) - c| ≤ r → Real.log m = c)
    (H : ℝ → ℂ) (hb : tsupport H ⊆ Icc (c - r) (c + r)) (hH : H c = 1) :
    (∑' m : ℕ, ((Λ m / Real.sqrt m : ℝ) : ℂ) * H (Real.log m)) = ((Λ n / Real.sqrt n : ℝ) : ℂ) := by
  rw [tsum_eq_single n, ← hc, hH, mul_one]
  intro m hm
  rcases eq_or_ne m 0 with rfl | hm₀
  · simp
  apply mul_eq_zero_of_right
  by_contra h
  obtain ⟨h₁, h₂⟩ := hb (subset_tsupport H h)
  have he := hiso m (Nat.pos_of_ne_zero hm₀) (abs_le.mpr ⟨by linarith, by linarith⟩)
  rw [hc] at he
  have he' := Real.strictMonoOn_log.injOn (show (m : ℝ) ∈ Ioi 0 by exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm₀))
    (show (n : ℝ) ∈ Ioi 0 by exact Nat.cast_pos.mpr hn) he
  exact hm (by exact_mod_cast he')

set_option maxHeartbeats 900000 in
/-- Paper: §12.3, p. 514, and pp. 519–520. Each rational prime power admits arbitrarily localized tests with
any two prescribed polar moments and any prescribed real-place remainder. A single
finite local level and a single test give the exact signed prime value simultaneously
at all strip widths above the chosen positive threshold and all Sobolev orders above
one. The cutoff on the local side tends to this same value. -/
theorem exists_exact_prime_power_sharp_strip_trace_unconditional {p j : ℕ}
    (hp : p.Prime) (hj : j ≠ 0) :
    let n := p ^ j
    let c := Real.log (n : ℝ)
    ∃ r > (0 : ℝ), ∃ S : Finset Pl, ∀ {ε δ : ℝ}, 0 < ε → ε ≤ r → 0 < δ →
      ∀ P M A : ℂ, ∃ (H : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ)
        (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ),
        ContDiff ℝ (∞) H ∧ tsupport H ⊆ Icc (c - ε) (c + ε) ∧ H c = 1 ∧ radial(φ, H) ∧
        lifts(S, f, φ) ∧ pole(φ, (1 / 2)) = V * P ∧ pole(φ, (-(1 / 2))) = V * M ∧
        let value := V * (P - ((Real.log p / Real.sqrt (n : ℝ) : ℝ) : ℂ) - A)
        Tendsto (fun R : ℝ ↦ -rationalCorrectedSharpMass f R) atTop (𝓝 value) ∧
        ∀ {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s), δ ≤ a →
          ∀ T : nuclearEndomorphisms Q(ha, hs), rep(T, φ, ha, hs) → hilbertTrace T = value := by
  intro n c
  have hn : 1 < n := Nat.one_lt_pow hj hp.one_lt
  have hc : 0 < c := Real.log_pos (by exact_mod_cast hn)
  obtain ⟨d, hd, hiso⟩ := PrimeShrink.logNat_isolation c
  let r := min d (c / 2)
  have hr : 0 < r := lt_min hd (half_pos hc)
  obtain ⟨S, hS⟩ := exists_radialSharpMass_stripTrace_comparison (c - r) (c + r)
  refine ⟨r, hr, S, ?_⟩
  intro ε δ hε hεr hδ P M A
  have hεc : ε < c := (hεr.trans (min_le_right _ _)).trans_lt (half_lt_self hc)
  obtain ⟨H, hH, hb, hHc, hP, hM, hA, hz⟩ := exists_exterior_annihilating_prime_probe
    (summable_exterior_inverse_height_unconditional hδ) hε hεc P M A
  have hk : HasCompactSupport H := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hb
  have hpos : tsupport H ⊆ Ioi 0 := fun x hx ↦ lt_of_lt_of_le (sub_pos.mpr hεc) (hb hx).1
  have hbr : tsupport H ⊆ Icc (c - r) (c + r) := hb.trans (Icc_subset_Icc (by linarith) (by linarith))
  obtain ⟨φ, f, hφ, hf, hlim, _⟩ := hS H hH hk hpos hbr
  have hprime := single_weighted_sample (n := n) (Nat.zero_lt_of_lt hn) rfl hiso H
    (hbr.trans (Icc_subset_Icc (by linarith [min_le_left d (c / 2)]) (by linarith [min_le_left d (c / 2)]))) hHc
  have hΛ : Λ n = Real.log p := by
    simp [n, ArithmeticFunction.vonMangoldt_apply_pow hj, ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hval : centeredVonMangoldtValue H = P - ((Real.log p / Real.sqrt (n : ℝ) : ℝ) : ℂ) - A := by
    rw [centeredVonMangoldtValue, hP, hA, hprime, hΛ]
  refine ⟨H, φ, f, hH, hb, hHc, hφ, hf, (radial_pole_eq H hH.continuous φ hφ _).trans
    (congrArg _ hP), (radial_pole_eq H hH.continuous φ hφ _).trans (congrArg _ hM), ?_, ?_⟩
  · simpa only [hval] using hlim
  · intro a s ha hs hδa T hT
    rw [trace_eq_of_annihilating hδa ha hs H hH hk hpos hz φ hφ T hT, hval]

set_option maxHeartbeats 900000 in
/-- Paper: §12.3, p. 514, and pp. 519–520. Assuming Ingham's stated ordinary-zeta
density estimate, each rational prime power admits arbitrarily localized tests with
any two prescribed polar moments and any prescribed real-place remainder. A single
finite local level and a single test give the exact signed prime value simultaneously
at all strip widths above the chosen positive threshold and all Sobolev orders above
one. The cutoff on the local side tends to this same value. -/
theorem exists_exact_prime_power_sharp_strip_trace (hI : InghamDensity) {p j : ℕ}
    (hp : p.Prime) (hj : j ≠ 0) :
    let n := p ^ j
    let c := Real.log (n : ℝ)
    ∃ r > (0 : ℝ), ∃ S : Finset Pl, ∀ {ε δ : ℝ}, 0 < ε → ε ≤ r → 0 < δ →
      ∀ P M A : ℂ, ∃ (H : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ)
        (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ),
        ContDiff ℝ (∞) H ∧ tsupport H ⊆ Icc (c - ε) (c + ε) ∧ H c = 1 ∧ radial(φ, H) ∧
        lifts(S, f, φ) ∧ pole(φ, (1 / 2)) = V * P ∧ pole(φ, (-(1 / 2))) = V * M ∧
        let value := V * (P - ((Real.log p / Real.sqrt (n : ℝ) : ℝ) : ℂ) - A)
        Tendsto (fun R : ℝ ↦ -rationalCorrectedSharpMass f R) atTop (𝓝 value) ∧
        ∀ {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s), δ ≤ a →
          ∀ T : nuclearEndomorphisms Q(ha, hs), rep(T, φ, ha, hs) → hilbertTrace T = value :=
  exists_exact_prime_power_sharp_strip_trace_unconditional hp hj

end RiemannMasullo.RationalWidthLoss
