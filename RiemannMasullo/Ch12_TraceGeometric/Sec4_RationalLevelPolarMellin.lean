module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalLevelComparison

/-!
# The level's polar term against the two polar Mellin values, for the rationals

The proof of Theorem 12.5.1.1 (p. 520) subtracts two polar Mellin values from the trace of
Theorem 12.4.1.1, `M(φ)(|·|^(1/2))` and `M(φ)(|·|^(-1/2))`. For `ℚ` with no finite place,
`Sec4_RationalLevelComparison` shows that the trace on the polar-free level differs from the summed
sharp orbital masses by the polar term `∫ ψ(g) min (g, 1) g ^ (-1/2) dg`, where `ψ = ratFold f` is
the folded test. This file compares the two.

* `ratMellin_eq_integral_ratFold`. The Mellin value of the S-idelic test `f` at `|·|^α`, against
  the multiplicative Tamagawa measure, is `∫ ψ(h) h ^ α dh` over the positive half-line.
* `ratPolarTerm_eq_integral_min`. The polar term is `∫ ψ(h) min (h ^ (1/2), h ^ (-1/2)) dh`. So the
  level takes, at each `h`, the smaller of the two powers that p. 520 adds.
* `ratPolarMellin_sub_ratPolarTerm`. The two polar Mellin values less the polar term are
  `∫ ψ(h) max (h ^ (1/2), h ^ (-1/2)) dh`.
* `ratPolarTerm_eq_mellin_neg_half`. For a test supported on norms at least one, which is what the
  shell theorem 11.3.2.1 (p. 495) assumes, the polar term is exactly `M(f)(|·|^(-1/2))`.
* `ratLevel_trace_add_polarMellin_tendsto` and `ratLevel_trace_add_polarMellin_tendsto_of_one_le`.
  With the two polar Mellin values subtracted as on p. 520, the trace on the level less the summed
  sharp masses tends to `∫ ψ(h) max (h ^ (1/2), h ^ (-1/2)) dh`, and for a test supported on norms
  at least one to `M(f)(|·|^(1/2))`. For a test with nonnegative real part, positive somewhere,
  that limit has positive real part (`ratMellin_re_pos`).

So in this model the level removes one polar value, `M(f)(|·|^(-1/2))`, and leaves the other.

The Mellin values here are those of the S-idelic test `f`. The paper's `M(φ)` is global. Relating
the two is the missing §12.3 (`ERRATA.md`, M25). The level is that of the even Paley–Wiener band of
`Sec4_RationalLevelComparison`, and its identification with `main`'s `sLocalInvariantPWSobolev` is
not shown here.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set NumberField IsDedekindDomain
open scoped Topology NumberField Real ENNReal InnerProductSpace

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b instMeasurableSpaceInfiniteAdeleRing_riemannMasullo
  instRatSIdeleT2 instRatSAdeleT2

local notation "Sq" => (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
local notation "Iq" => (SAdeleRing ℚ Sq)ˣ
local notation "Hq" => sProjectedDiagonal ℚ Sq
local notation "eq" => ratRealCoordEquiv
local notation "μq" => sMultiplicativeTamagawaMeasure ℚ Sq
local notation "normq(" x ")" => (((sIdeleNorm ℚ Sq x).val : ℝ))
local notation "mellin(" f ", " α ")" => ∫ g, (f).val g * ((normq(g) ^ (α : ℝ) : ℝ) : ℂ) ∂μq
local notation "μ₀" => realPWIntervalMeasure 0 0
local notation "V₀(" Y ")" => RealPWBand.space Y (volume_le_realPWIntervalMeasure 0 0 le_rfl)
local notation "ev(" Y ")" => RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure 0 0 le_rfl)
local notation "level(" Y ")" => realPWZeroLevel Y 0 0 le_rfl

/-- The lift of a test, weighted by `|t| ^ α / |t|`, is continuous on the line: away from zero
it is a product of continuous functions, and near zero it vanishes. -/
theorem continuous_ratLift_mul_rpow (f : BruhatCompactSupport Iq) (α : ℝ) :
    Continuous (fun t : ℝ ↦ ratLift f.val t * ((|t| ^ α / |t| : ℝ) : ℂ)) := by
  obtain ⟨a, b, ha, hsupp⟩ := exists_ratLift_support f
  rw [continuous_iff_continuousAt]
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · have hz : (fun t : ℝ ↦ ratLift f.val t * ((|t| ^ α / |t| : ℝ) : ℂ)) =ᶠ[𝓝 0]
        fun _ ↦ (0 : ℂ) := by
      filter_upwards [Ioo_mem_nhds (neg_lt_zero.2 ha) ha] with s hs
      have h0 : ratLift f.val s = 0 := by
        by_contra hne
        have h1 := (hsupp s hne).1
        have h2 : |s| < a := abs_lt.2 ⟨hs.1, hs.2⟩
        linarith
      rw [h0, zero_mul]
    exact continuousAt_const.congr hz.symm
  · have hab : |t| ≠ 0 := abs_ne_zero.2 ht
    refine (continuous_ratLift f).continuousAt.mul (Complex.continuous_ofReal.continuousAt.comp ?_)
    exact (continuous_abs.continuousAt.rpow_const (Or.inl hab)).div continuous_abs.continuousAt hab

/-- The folded test against a weight continuous on the positive half-line is integrable there. -/
theorem integrableOn_ratFold_mul (f : BruhatCompactSupport Iq) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Ioi 0)) :
    IntegrableOn (fun h : ℝ ↦ ratFold f h * (w h : ℂ)) (Ioi 0) := by
  obtain ⟨a, b, ha, hsupp⟩ := exists_ratFold_support f
  have hcont : ContinuousOn (fun h : ℝ ↦ ratFold f h * (w h : ℂ)) (Icc a b) :=
    (continuous_ratFold f).continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn
      (hw.mono fun h hh ↦ show h ∈ Ioi 0 from ha.trans_le hh.1))
  have hint : Integrable (fun h : ℝ ↦ ratFold f h * (w h : ℂ)) := by
    refine (integrableOn_iff_integrable_of_support_subset ?_).1
      (hcont.integrableOn_compact isCompact_Icc)
    intro h hh
    by_contra hm
    exact hh (by simp [hsupp h hm])
  exact hint.integrableOn

/-- `h ↦ h ^ α` is continuous on the positive half-line. -/
theorem continuousOn_rpow_Ioi (α : ℝ) : ContinuousOn (fun h : ℝ ↦ h ^ α) (Ioi 0) :=
  continuousOn_id.rpow_const fun h hh ↦ Or.inl (show (0 : ℝ) < h from hh).ne'

/-- Reconstruction: for a test with nonnegative real part, positive somewhere, the integral of
the folded test against a positive weight, continuous on the positive half-line, has positive real
part. -/
theorem integral_ratFold_mul_re_pos (f : BruhatCompactSupport Iq) (hf : ∀ g, 0 ≤ (f.val g).re)
    {g₀ : Iq} (hg₀ : 0 < (f.val g₀).re) {w : ℝ → ℝ} (hw : ContinuousOn w (Ioi 0))
    (hwpos : ∀ h, 0 < h → 0 < w h) :
    0 < (∫ h in Ioi 0, ratFold f h * (w h : ℂ)).re := by
  have hint := integrableOn_ratFold_mul f hw
  have hre_fun (h : ℝ) : (ratFold f h * (w h : ℂ)).re = (ratFold f h).re * w h := by
    simp [Complex.mul_re]
  have hre : (∫ h in Ioi 0, ratFold f h * (w h : ℂ)).re =
      ∫ h in Ioi 0, (ratFold f h).re * w h := by
    rw [← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hint]
    simp only [Complex.reCLM_apply, hre_fun]
  have hint' : IntegrableOn (fun h ↦ (ratFold f h).re * w h) (Ioi 0) :=
    hint.re.congr (ae_of_all _ hre_fun)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun h ↦ (ratFold f h).re * w h :=
    (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun h hh ↦
      mul_nonneg (ratFold_re_nonneg f hf h) (hwpos h hh).le)
  rw [hre, setIntegral_pos_iff_support_of_nonneg_ae hnn hint']
  have hU : IsOpen (Ioi (0 : ℝ) ∩ {h | 0 < (ratFold f h).re}) :=
    isOpen_Ioi.inter (isOpen_lt continuous_const
      (Complex.continuous_re.comp (continuous_ratFold f)))
  have hsub : Ioi (0 : ℝ) ∩ {h | 0 < (ratFold f h).re} ⊆
      Function.support (fun h ↦ (ratFold f h).re * w h) ∩ Ioi 0 :=
    fun h hh ↦ ⟨(mul_pos hh.2 (hwpos h hh.1)).ne', hh.1⟩
  have hmem : |eq g₀.val| ∈ Ioi (0 : ℝ) ∩ {h | 0 < (ratFold f h).re} :=
    ⟨abs_pos.2 ((ratMem_range_units _).1 ⟨g₀, rfl⟩), ratFold_re_pos f hf hg₀⟩
  exact (hU.measure_pos volume ⟨_, hmem⟩).trans_le (measure_mono hsub)

/-- Reconstruction: the Mellin value at `|·|^α` of an S-idelic test of `ℚ` with no finite place,
against the multiplicative Tamagawa measure, is the integral of the folded test against `h ^ α` on
the positive half-line. -/
theorem ratMellin_eq_integral_ratFold (f : BruhatCompactSupport Iq) (α : ℝ) :
    mellin(f, α) = ∫ h in Ioi 0, ratFold f h * ((h ^ α : ℝ) : ℂ) := by
  rw [ratIntegral_mul]
  have hpt (t : ℝ) : ratLift (fun g ↦ f.val g * ((normq(g) ^ α : ℝ) : ℂ)) t / ((|t| : ℝ) : ℂ) =
      ratLift f.val t * ((|t| ^ α / |t| : ℝ) : ℂ) := by
    rcases eq_or_ne t 0 with rfl | ht
    · simp [ratLift_zero]
    · simp only [ratLift_of_ne ht]
      rw [ratNormq, ratUnit_val ht, RingEquiv.apply_symm_apply]
      push_cast
      ring
  simp only [hpt]
  rw [integral_eq_integral_Ioi_add_neg
    ((continuous_ratLift_mul_rpow f α).integrable_of_hasCompactSupport
      (hasCompactSupport_ratLift f).mul_right)]
  refine setIntegral_congr_fun measurableSet_Ioi fun h (hh : 0 < h) ↦ ?_
  simp only [ratFold, indicator_of_mem (show h ∈ Ioi (0 : ℝ) from hh), abs_neg, abs_of_pos hh]
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hh.ne'
  push_cast
  field_simp

/-- For `h > 0`, `min (h, 1) h ^ (-1/2)` is the smaller of `h ^ (1/2)` and `h ^ (-1/2)`. -/
theorem min_one_mul_rpow_neg_half {h : ℝ} (hh : 0 < h) :
    min h 1 * h ^ (-(1 / 2 : ℝ)) = min (h ^ (1 / 2 : ℝ)) (h ^ (-(1 / 2 : ℝ))) := by
  have hsplit : h ^ (1 / 2 : ℝ) = h * h ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_one_add' hh.le (by norm_num)]
    norm_num
  rcases le_total h 1 with h1 | h1
  · rw [min_eq_left h1, ← hsplit,
      min_eq_left (Real.rpow_le_rpow_of_exponent_ge hh h1 (by norm_num))]
  · rw [min_eq_right h1, one_mul,
      min_eq_right (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num))]

/-- Reconstruction: the polar term of `Sec4_RationalLevelComparison` is the integral of the folded
test against the smaller of `h ^ (1/2)` and `h ^ (-1/2)`. -/
theorem ratPolarTerm_eq_integral_min (f : BruhatCompactSupport Iq) :
    ratPolarTerm f = ∫ h in Ioi 0, ratFold f h *
      ((min (h ^ (1 / 2 : ℝ)) (h ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) := by
  rw [ratPolarTerm, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ))]
  · refine setIntegral_congr_fun measurableSet_Ioi fun h (hh : 0 < h) ↦ ?_
    rw [min_one_mul_rpow_neg_half hh]
  · intro h hh
    simp [ratFold, indicator_of_notMem hh]

/-- Reconstruction: the two polar Mellin values less the polar term are the integral of the folded
test against the larger of `h ^ (1/2)` and `h ^ (-1/2)`. -/
theorem ratPolarMellin_sub_ratPolarTerm (f : BruhatCompactSupport Iq) :
    mellin(f, 1 / 2) + mellin(f, -(1 / 2)) - ratPolarTerm f =
      ∫ h in Ioi 0, ratFold f h * ((max (h ^ (1 / 2 : ℝ)) (h ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) := by
  rw [ratMellin_eq_integral_ratFold, ratMellin_eq_integral_ratFold, ratPolarTerm_eq_integral_min,
    ← integral_add (integrableOn_ratFold_mul f (continuousOn_rpow_Ioi _))
      (integrableOn_ratFold_mul f (continuousOn_rpow_Ioi _))]
  have hminc : ContinuousOn (fun h : ℝ ↦ min (h ^ (1 / 2 : ℝ)) (h ^ (-(1 / 2 : ℝ)))) (Ioi 0) :=
    continuous_min.comp_continuousOn ((continuousOn_rpow_Ioi _).prodMk (continuousOn_rpow_Ioi _))
  have hAB : IntegrableOn (fun h : ℝ ↦ ratFold f h * ((h ^ (1 / 2 : ℝ) : ℝ) : ℂ) +
      ratFold f h * ((h ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (Ioi 0) :=
    (integrableOn_ratFold_mul f (continuousOn_rpow_Ioi _)).add
      (integrableOn_ratFold_mul f (continuousOn_rpow_Ioi _))
  rw [← integral_sub hAB (integrableOn_ratFold_mul f hminc)]
  refine setIntegral_congr_fun measurableSet_Ioi fun h _ ↦ ?_
  have hm : h ^ (1 / 2 : ℝ) + h ^ (-(1 / 2 : ℝ)) - min (h ^ (1 / 2 : ℝ)) (h ^ (-(1 / 2 : ℝ))) =
      max (h ^ (1 / 2 : ℝ)) (h ^ (-(1 / 2 : ℝ))) := by
    linarith [min_add_max (h ^ (1 / 2 : ℝ)) (h ^ (-(1 / 2 : ℝ)))]
  rw [← hm]
  push_cast
  ring

/-- A test supported on norms at least one has its folded test supported on `[1, ∞)`. -/
theorem one_le_of_ratFold_ne_zero (f : BruhatCompactSupport Iq)
    (hf : ∀ g, f.val g ≠ 0 → 1 ≤ normq(g)) {h : ℝ} (hh : 0 < h) (hψ : ratFold f h ≠ 0) :
    1 ≤ h := by
  simp only [ratFold, indicator_of_mem (show h ∈ Ioi (0 : ℝ) from hh)] at hψ
  have hor : ratLift f.val h ≠ 0 ∨ ratLift f.val (-h) ≠ 0 := by
    by_contra! hc
    rw [hc.1, hc.2, add_zero, zero_div] at hψ
    exact hψ rfl
  rcases hor with h1 | h1
  · rw [ratLift_of_ne hh.ne'] at h1
    have := hf _ h1
    rwa [ratNormq, ratUnit_val hh.ne', RingEquiv.apply_symm_apply, abs_of_pos hh] at this
  · rw [ratLift_of_ne (neg_ne_zero.2 hh.ne')] at h1
    have := hf _ h1
    rwa [ratNormq, ratUnit_val (neg_ne_zero.2 hh.ne'), RingEquiv.apply_symm_apply, abs_neg,
      abs_of_pos hh] at this

/-- Paper: Theorem 11.3.2.1, p. 495, which assumes tests supported above norm one, and the
subtraction on p. 520.
Reconstruction: for a test supported on norms at least one, the polar term of the level is exactly
the Mellin value `M(f)(|·|^(-1/2))`. -/
theorem ratPolarTerm_eq_mellin_neg_half (f : BruhatCompactSupport Iq)
    (hf : ∀ g, f.val g ≠ 0 → 1 ≤ normq(g)) :
    ratPolarTerm f = mellin(f, -(1 / 2)) := by
  rw [ratPolarTerm_eq_integral_min, ratMellin_eq_integral_ratFold]
  refine setIntegral_congr_fun measurableSet_Ioi fun h (hh : 0 < h) ↦ ?_
  by_cases hψ : ratFold f h = 0
  · simp [hψ]
  · have h1 := one_le_of_ratFold_ne_zero f hf hh hψ
    rw [min_eq_right (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num))]

/-- Reconstruction: for a test with nonnegative real part, positive somewhere, every Mellin value
`M(f)(|·|^α)` has positive real part. -/
theorem ratMellin_re_pos (f : BruhatCompactSupport Iq) (hf : ∀ g, 0 ≤ (f.val g).re) {g₀ : Iq}
    (hg₀ : 0 < (f.val g₀).re) (α : ℝ) : 0 < (mellin(f, α)).re := by
  rw [ratMellin_eq_integral_ratFold]
  exact integral_ratFold_mul_re_pos f hf hg₀ (continuousOn_rpow_Ioi α)
    fun h hh ↦ Real.rpow_pos_of_pos hh α

/-- Paper: Theorem 12.4.1.1, pp. 514–519, and the subtraction of the two polar Mellin values in
the proof of Theorem 12.5.1.1, p. 520, for `ℚ` with no finite place.
Reconstruction: for the operators of `ratLevel_trace_sub_sharpMass_tendsto`, the trace on the
polar-free level less the summed sharp masses, with the two polar Mellin values subtracted as on
p. 520, tends to `∫ ψ(h) max (h ^ (1/2), h ^ (-1/2)) dh`, where `ψ` is the folded test. This is the
part of the two polar values that the level does not remove.
Deviation: The Mellin values are those of the S-idelic test `f`, not the global `M(φ)` (M25). -/
theorem ratLevel_trace_add_polarMellin_tendsto (f : BruhatCompactSupport Iq) {Y : ℝ}
    (hY : 0 < Y) :
    ∃ T : ℝ → nuclearEndomorphisms V₀(Y),
      (∀ L, 0 < L → ∀ v : V₀(Y), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ratFold f g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev(Y) (g⁻¹ * x) ((level(Y)).starProjection v))) ∧
        (T L).val v = (level(Y)).starProjection ((V₀(Y)).orthogonalProjectionOnto r)) ∧
      Tendsto (fun L ↦ hilbertTrace (T L) - ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y) +
          (mellin(f, 1 / 2) + mellin(f, -(1 / 2)))) atTop
        (𝓝 (∫ h in Ioi 0, ratFold f h *
          ((max (h ^ (1 / 2 : ℝ)) (h ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ))) := by
  obtain ⟨T, hT, hlim⟩ := ratLevel_trace_sub_sharpMass_tendsto f hY
  refine ⟨T, hT, ?_⟩
  rw [← ratPolarMellin_sub_ratPolarTerm]
  convert hlim.add_const (mellin(f, 1 / 2) + mellin(f, -(1 / 2))) using 2
  ring

/-- Paper: Theorem 12.4.1.1 and the proof of Theorem 12.5.1.1, p. 520, for `ℚ` with no finite
place and a test supported on norms at least one, as Theorem 11.3.2.1, p. 495, assumes.
Reconstruction: with the two polar Mellin values subtracted as on p. 520, the trace on the
polar-free level less the summed sharp masses tends to `M(f)(|·|^(1/2))`. The level removes the
polar value `M(f)(|·|^(-1/2))` and leaves `M(f)(|·|^(1/2))`.
Deviation: The Mellin values are those of the S-idelic test `f`, not the global `M(φ)` (M25). -/
theorem ratLevel_trace_add_polarMellin_tendsto_of_one_le (f : BruhatCompactSupport Iq)
    (hf : ∀ g, f.val g ≠ 0 → 1 ≤ normq(g)) {Y : ℝ} (hY : 0 < Y) :
    ∃ T : ℝ → nuclearEndomorphisms V₀(Y),
      (∀ L, 0 < L → ∀ v : V₀(Y), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ratFold f g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev(Y) (g⁻¹ * x) ((level(Y)).starProjection v))) ∧
        (T L).val v = (level(Y)).starProjection ((V₀(Y)).orthogonalProjectionOnto r)) ∧
      Tendsto (fun L ↦ hilbertTrace (T L) - ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y) +
          (mellin(f, 1 / 2) + mellin(f, -(1 / 2)))) atTop (𝓝 (mellin(f, 1 / 2))) := by
  obtain ⟨T, hT, hlim⟩ := ratLevel_trace_sub_sharpMass_tendsto f hY
  refine ⟨T, hT, ?_⟩
  convert hlim.add_const (mellin(f, 1 / 2) + mellin(f, -(1 / 2))) using 2
  rw [ratPolarTerm_eq_mellin_neg_half f hf]
  ring

/-- Paper: Theorem 12.4.1.1 and the proof of Theorem 12.5.1.1, p. 520, for `ℚ` with no finite
place.
Reconstruction: for a test with nonnegative real part, positive somewhere, the trace on the
polar-free level less the summed sharp masses does not tend to minus the two polar Mellin values,
which is what p. 520 needs. The difference tends to `∫ ψ(h) max (h ^ (1/2), h ^ (-1/2)) dh`, whose
real part is positive.
Deviation: The Mellin values are those of the S-idelic test `f`, not the global `M(φ)` (M25). -/
theorem ratLevel_trace_not_tendsto_polarMellin (f : BruhatCompactSupport Iq)
    (hf : ∀ g, 0 ≤ (f.val g).re) {g₀ : Iq} (hg₀ : 0 < (f.val g₀).re) {Y : ℝ} (hY : 0 < Y) :
    ∃ T : ℝ → nuclearEndomorphisms V₀(Y),
      (∀ L, 0 < L → ∀ v : V₀(Y), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ratFold f g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev(Y) (g⁻¹ * x) ((level(Y)).starProjection v))) ∧
        (T L).val v = (level(Y)).starProjection ((V₀(Y)).orthogonalProjectionOnto r)) ∧
      ¬ Tendsto (fun L ↦ hilbertTrace (T L) - ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y))
        atTop (𝓝 (-(mellin(f, 1 / 2) + mellin(f, -(1 / 2))))) := by
  obtain ⟨T, hT, hlim⟩ := ratLevel_trace_add_polarMellin_tendsto f hY
  refine ⟨T, hT, fun h0 ↦ ?_⟩
  have h1 := h0.add_const (mellin(f, 1 / 2) + mellin(f, -(1 / 2)))
  rw [neg_add_cancel] at h1
  have hmaxc : ContinuousOn (fun h : ℝ ↦ max (h ^ (1 / 2 : ℝ)) (h ^ (-(1 / 2 : ℝ)))) (Ioi 0) :=
    continuous_max.comp_continuousOn ((continuousOn_rpow_Ioi _).prodMk (continuousOn_rpow_Ioi _))
  have hpos := integral_ratFold_mul_re_pos f hf hg₀ hmaxc
    fun h hh ↦ lt_max_of_lt_left (Real.rpow_pos_of_pos hh _)
  rw [tendsto_nhds_unique hlim h1, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

end RiemannMasullo.Isolated
