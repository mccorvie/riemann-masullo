module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalRealPlace

/-!
# The level trace against the sharp orbital masses, for the rationals with no finite place

Theorem 12.4.1.1 is stated for the cutoff operator compressed to the polar-free level, and its
proof (Step III, p. 517) compares the diagonal integral there with the sum of the orbital masses
of (12.4.1.22)–(12.4.1.24), p. 518. This file makes that comparison for `F = ℚ` with no finite
place, in the terms of `Sec4.lean`.

In this case the folded test `ψ = ratFold f` acts on the even Paley–Wiener band of width `Y`.
The polar-free level is the space of band vectors vanishing at the origin (`realPWZeroLevel`).
The trace of the cutoff of the action of `ψ`, compressed to that level, is the sum of the sharp
orbital masses at radius `L Y` less a rank-one correction at the evaluation vector at the origin
(`exists_ratLevelCutoff_nuclear`). This combines `tsum_ratSharpMass` with
`exists_realPWTestCutoff_level_nuclear`.

The correction does not vanish in the limit. As `L` tends to infinity it tends to the polar term
`∫ ψ(g) min (g, 1) g ^ (-1/2) dg` (`tendsto_realPWZeroLevelCorrection_zero_zero`). So the trace on
the level minus the summed sharp masses tends to minus the polar term
(`ratLevel_trace_sub_sharpMass_tendsto`), and the comparison of Step III holds up to `o(1)` only
when the polar term is zero. For a test with nonnegative real part, positive somewhere, the polar
term has positive real part (`ratPolarTerm_re_pos`), so the comparison fails
(`ratLevel_trace_sub_sharpMass_not_tendsto_zero`). Adding the asymptotic of the masses on `main`
(`sLocalTraceSharpMass_asymptotic`) gives the conclusion of Theorem 12.4.1.1 on the level with the
polar term subtracted (`ratLevel_trace_asymptotic`).
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
local notation "Aq" => SAdeleRing ℚ Sq
local notation "Iq" => (SAdeleRing ℚ Sq)ˣ
local notation "Hq" => sProjectedDiagonal ℚ Sq
local notation "eq" => ratRealCoordEquiv
local notation "Cq" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "classAtq(" g ")" => (QuotientGroup.mk (sIdeleInsertion ℚ Sq g) : Cq)
local notation "volume₁" => ((sLocalNormOneQuotientMeasure ℚ Sq) univ).toReal
local notation "archTest" => ((w : InfinitePlace ℚ) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : Sq) → BruhatCompactSupport (v.val.adicCompletion ℚ)ˣ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v
local notation "finiteVolume(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure ℚ v
    ((HeightOneSpectrum.adicCompletionIntegers ℚ v).units : Set _)).toReal
local notation "principalValues(" a "," b ")" =>
  ((∑ w : InfinitePlace ℚ, infiniteConnesWeilPrincipalValue w (a w)) +
    ∑ v : Sq, ((Real.log (v.val.asIdeal.absNorm : ℝ) / finiteVolume(v.val) : ℝ) : ℂ) *
      finiteConnesWeilPrincipalValue v.val 1 (b v))
local notation "μ₀" => realPWIntervalMeasure 0 0
local notation "V₀(" Y ")" => RealPWBand.space Y (volume_le_realPWIntervalMeasure 0 0 le_rfl)
local notation "ev(" Y ")" => RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure 0 0 le_rfl)
local notation "evv(" Y ")" =>
  RealPWBand.evaluationVector Y (volume_le_realPWIntervalMeasure 0 0 le_rfl)
local notation "level(" Y ")" => realPWZeroLevel Y 0 0 le_rfl

/-- The polar term: the integral of the folded test against `min (g, 1) g ^ (-1/2)`. -/
def ratPolarTerm (f : BruhatCompactSupport Iq) : ℂ :=
  ∫ g, ratFold f g * ((min g 1 * g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

/-- The lift of a test with nonnegative real part has nonnegative real part. -/
theorem ratLift_re_nonneg {G : Iq → ℂ} (hG : ∀ g, 0 ≤ (G g).re) (t : ℝ) :
    0 ≤ (ratLift G t).re := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [ratLift_zero]
  · rw [ratLift_of_ne ht]
    exact hG _

/-- The folded test of a test with nonnegative real part has nonnegative real part. -/
theorem ratFold_re_nonneg (f : BruhatCompactSupport Iq) (hf : ∀ g, 0 ≤ (f.val g).re) (h : ℝ) :
    0 ≤ (ratFold f h).re := by
  by_cases hh : h ∈ Ioi (0 : ℝ)
  · simp only [ratFold, indicator_of_mem hh, Complex.div_ofReal_re, Complex.add_re]
    exact div_nonneg (add_nonneg (ratLift_re_nonneg hf h) (ratLift_re_nonneg hf (-h)))
      (le_of_lt hh)
  · simp [ratFold, indicator_of_notMem hh]

/-- If the real part of the test is positive at `g₀`, the folded test has positive real part at
`|g₀|`. -/
theorem ratFold_re_pos (f : BruhatCompactSupport Iq) (hf : ∀ g, 0 ≤ (f.val g).re) {g₀ : Iq}
    (hg₀ : 0 < (f.val g₀).re) : 0 < (ratFold f |eq g₀.val|).re := by
  have ht : eq g₀.val ≠ 0 := (ratMem_range_units _).1 ⟨g₀, rfl⟩
  have hpos : 0 < |eq g₀.val| := abs_pos.2 ht
  have hl : (ratLift f.val (eq g₀.val)).re = (f.val g₀).re := by rw [ratLift_eq]
  have hn := ratLift_re_nonneg hf (-eq g₀.val)
  have key : 0 < (ratLift f.val |eq g₀.val|).re + (ratLift f.val (-|eq g₀.val|)).re := by
    rcases abs_choice (eq g₀.val) with h | h
    · rw [h]
      linarith
    · rw [h, neg_neg]
      linarith
  simp only [ratFold, indicator_of_mem (show |eq g₀.val| ∈ Ioi 0 from hpos),
    Complex.div_ofReal_re, Complex.add_re]
  exact div_pos key hpos

/-- Reconstruction: for a test whose real part is nonnegative and somewhere positive, the polar
term has positive real part. In particular it is not zero. -/
theorem ratPolarTerm_re_pos (f : BruhatCompactSupport Iq) (hf : ∀ g, 0 ≤ (f.val g).re)
    {g₀ : Iq} (hg₀ : 0 < (f.val g₀).re) : 0 < (ratPolarTerm f).re := by
  obtain ⟨a, b, ha, hsupp⟩ := exists_ratFold_support f
  have hwpos : ∀ g : ℝ, 0 < g → 0 < min g 1 * g ^ (-(1 / 2 : ℝ)) := fun g hg ↦
    mul_pos (lt_min hg one_pos) (Real.rpow_pos_of_pos hg _)
  have hcont : ContinuousOn
      (fun g ↦ ratFold f g * ((min g 1 * g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (Icc a b) := by
    refine (continuous_ratFold f).continuousOn.mul
      (Complex.continuous_ofReal.comp_continuousOn ?_)
    refine (continuous_id.min continuous_const).continuousOn.mul ?_
    exact continuousOn_id.rpow_const fun g hg ↦ Or.inl (ha.trans_le hg.1).ne'
  have hint : Integrable (fun g ↦ ratFold f g * ((min g 1 * g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
    refine (integrableOn_iff_integrable_of_support_subset ?_).1
      (hcont.integrableOn_compact isCompact_Icc)
    intro g hg
    by_contra hgm
    exact hg (by simp [hsupp g hgm])
  have hre_fun : ∀ g : ℝ, (ratFold f g * ((min g 1 * g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).re =
      (ratFold f g).re * (min g 1 * g ^ (-(1 / 2 : ℝ))) := fun g ↦ by
    simp [Complex.mul_re]
  have hre : (ratPolarTerm f).re =
      ∫ g, (ratFold f g).re * (min g 1 * g ^ (-(1 / 2 : ℝ))) := by
    rw [ratPolarTerm, ← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hint]
    simp only [Complex.reCLM_apply, hre_fun]
  have hnn : ∀ g : ℝ, 0 ≤ (ratFold f g).re * (min g 1 * g ^ (-(1 / 2 : ℝ))) := by
    intro g
    rcases le_or_gt g 0 with hg | hg
    · have h0 : ratFold f g = 0 := by
        simp [ratFold, indicator_of_notMem (show g ∉ Ioi (0 : ℝ) from not_lt.2 hg)]
      simp [h0]
    · exact mul_nonneg (ratFold_re_nonneg f hf g) (hwpos g hg).le
  have hint' : Integrable (fun g ↦ (ratFold f g).re * (min g 1 * g ^ (-(1 / 2 : ℝ)))) :=
    hint.re.congr (Eventually.of_forall hre_fun)
  rw [hre, integral_pos_iff_support_of_nonneg hnn hint']
  have hU : IsOpen (Ioi (0 : ℝ) ∩ {g | 0 < (ratFold f g).re}) :=
    isOpen_Ioi.inter (isOpen_lt continuous_const
      (Complex.continuous_re.comp (continuous_ratFold f)))
  have hsub : Ioi (0 : ℝ) ∩ {g | 0 < (ratFold f g).re} ⊆
      Function.support fun g ↦ (ratFold f g).re * (min g 1 * g ^ (-(1 / 2 : ℝ))) :=
    fun g hg ↦ (mul_pos hg.2 (hwpos g hg.1)).ne'
  have hmem : |eq g₀.val| ∈ Ioi (0 : ℝ) ∩ {g | 0 < (ratFold f g).re} :=
    ⟨abs_pos.2 ((ratMem_range_units _).1 ⟨g₀, rfl⟩), ratFold_re_pos f hf hg₀⟩
  exact (hU.measure_pos volume ⟨_, hmem⟩).trans_le (measure_mono hsub)

/-- Paper: Theorem 12.4.1.1, Step III, p. 517, and (12.4.1.22)–(12.4.1.24), p. 518, for `ℚ` with
no finite place.
Reconstruction: the cutoff of the action of the folded test, compressed to the polar-free level
of the even Paley–Wiener band of width `Y`, is nuclear. Its trace is the sum of the sharp orbital
masses at radius `L Y`, less the diagonal entry at the normalized evaluation vector at the
origin. -/
theorem exists_ratLevelCutoff_nuclear (f : BruhatCompactSupport Iq) {L Y : ℝ} (hL : 0 < L)
    (hY : 0 < Y) :
    ∃ T : nuclearEndomorphisms V₀(Y),
      (∀ v : V₀(Y), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ratFold f g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev(Y) (g⁻¹ * x) ((level(Y)).starProjection v))) ∧
        T.val v = (level(Y)).starProjection ((V₀(Y)).orthogonalProjectionOnto r)) ∧
      hilbertTrace T = (∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y)) -
        (((‖evv(Y) 0‖ ^ 2 : ℝ) : ℂ))⁻¹ *
          realPWZeroLevelCorrection Y 0 0 le_rfl (ratFold f) L := by
  obtain ⟨a, b, ha, hsupp⟩ := exists_ratFold_support f
  obtain ⟨T, hT1, hT2⟩ := exists_realPWTestCutoff_level_nuclear Y 0 0 le_rfl hY le_rfl ha
    (ratFold f) (continuous_ratFold f) hsupp L
  refine ⟨T, hT1, ?_⟩
  rw [hT2, tsum_ratSharpMass f hL hY]

/-- Paper: Theorem 12.4.1.1, pp. 514–519, the comparison of Step III with (12.4.1.22)–(12.4.1.24),
for `ℚ` with no finite place.
Reconstruction: on the polar-free level of the even Paley–Wiener band of fixed width `Y`, the
trace of the compressed cutoff less the summed sharp orbital masses at radius `L Y` tends to
minus the polar term `∫ ψ(g) min (g, 1) g ^ (-1/2) dg`, where `ψ` is the folded test. So the
diagonal integral on the level agrees with the computed sum up to `o(1)` exactly when the polar
term vanishes. For a test with nonnegative real part, positive somewhere, it does not
(`ratLevel_trace_sub_sharpMass_not_tendsto_zero`). -/
theorem ratLevel_trace_sub_sharpMass_tendsto (f : BruhatCompactSupport Iq) {Y : ℝ}
    (hY : 0 < Y) :
    ∃ T : ℝ → nuclearEndomorphisms V₀(Y),
      (∀ L, 0 < L → ∀ v : V₀(Y), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ratFold f g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev(Y) (g⁻¹ * x) ((level(Y)).starProjection v))) ∧
        (T L).val v = (level(Y)).starProjection ((V₀(Y)).orthogonalProjectionOnto r)) ∧
      Tendsto (fun L ↦ hilbertTrace (T L) - ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y)) atTop
        (𝓝 (-ratPolarTerm f)) := by
  obtain ⟨a, b, ha, hsupp⟩ := exists_ratFold_support f
  choose T hT1 hT2 using fun L ↦ exists_realPWTestCutoff_level_nuclear Y 0 0 le_rfl hY le_rfl ha
    (ratFold f) (continuous_ratFold f) hsupp L
  refine ⟨T, fun L _ ↦ hT1 L, ?_⟩
  have h := (tendsto_realPWZeroLevelCorrection_zero_zero Y le_rfl hY ha (ratFold f)
    (continuous_ratFold f) hsupp).neg
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  rw [hT2 L, tsum_ratSharpMass f hL hY]
  ring

/-- Paper: Theorem 12.4.1.1, Step III, p. 517, for `ℚ` with no finite place.
Reconstruction: the comparison of Step III fails on the polar-free level. Take a test whose real
part is nonnegative and somewhere positive. For every family of operators with the description of
`ratLevel_trace_sub_sharpMass_tendsto`, the trace less the summed sharp orbital masses does not
tend to zero, because it tends to minus the polar term and the polar term has positive real part
(`ratPolarTerm_re_pos`). -/
theorem ratLevel_trace_sub_sharpMass_not_tendsto_zero (f : BruhatCompactSupport Iq)
    (hf : ∀ g, 0 ≤ (f.val g).re) {g₀ : Iq} (hg₀ : 0 < (f.val g₀).re) {Y : ℝ} (hY : 0 < Y)
    (T : ℝ → nuclearEndomorphisms V₀(Y))
    (hT : ∀ L, 0 < L → ∀ v : V₀(Y), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ratFold f g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev(Y) (g⁻¹ * x) ((level(Y)).starProjection v))) ∧
        (T L).val v = (level(Y)).starProjection ((V₀(Y)).orthogonalProjectionOnto r)) :
    ¬ Tendsto (fun L ↦ hilbertTrace (T L) - ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y)) atTop
      (𝓝 0) := by
  intro h0
  obtain ⟨T', hT', hlim⟩ := ratLevel_trace_sub_sharpMass_tendsto f hY
  have heq : ∀ L, 0 < L → T L = T' L := by
    intro L hL
    refine Subtype.ext (ContinuousLinearMap.ext fun v ↦ ?_)
    obtain ⟨r, hr, hTr⟩ := hT L hL v
    obtain ⟨r', hr', hTr'⟩ := hT' L hL v
    have hrr : r = r' := Lp.ext (by filter_upwards [hr, hr'] with x h1 h2; rw [h1, h2])
    rw [hTr, hTr', hrr]
  have hlim' : Tendsto (fun L ↦ hilbertTrace (T L) - ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y))
      atTop (𝓝 (-ratPolarTerm f)) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [heq L hL]
  have h := tendsto_nhds_unique hlim' h0
  have hpos := ratPolarTerm_re_pos f hf hg₀
  rw [neg_eq_zero] at h
  rw [h, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

/-- Paper: Theorem 12.4.1.1, p. 514, for `ℚ` with no finite place, read on the polar-free level.
Reconstruction: for the cutoffs compressed to the polar-free level of the even Paley–Wiener band
of fixed width `Y`, the trace less `volume₁ φ(1) log (L Y)` tends to `volume₁` times the principal
value at the real place minus the polar term `∫ ψ(g) min (g, 1) g ^ (-1/2) dg`. This is the
conclusion of Theorem 12.4.1.1 corrected by the polar term.
Deviation: The level is that of the unweighted band, where the closure of the polar-free tests
is the space of band vectors vanishing at the origin, and the bandwidth is fixed. -/
theorem ratLevel_trace_asymptotic (φ : BruhatCompactSupport Cq)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits ℚ Sq) (c : Cq),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iq)
    (hLift : ∀ g : Iq, HasSum (fun ξ : Hq ↦ f.val (ξ.val * g)) (φ.val (classAtq(g))))
    {Y : ℝ} (hY : 0 < Y) :
    ∃ T : ℝ → nuclearEndomorphisms V₀(Y),
      (∀ L, 0 < L → ∀ v : V₀(Y), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ratFold f g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev(Y) (g⁻¹ * x) ((level(Y)).starProjection v))) ∧
        (T L).val v = (level(Y)).starProjection ((V₀(Y)).orthogonalProjectionOnto r)) ∧
      ∃ (a : archTest) (b : finiteTest),
        (∀ (w : InfinitePlace ℚ) (u : w.Completionˣ), (a w).val u = φ.val (archClass(w) u)) ∧
        (∀ (v : Sq) (u : (v.val.adicCompletion ℚ)ˣ),
          (b v).val u = φ.val (finiteClass(v.val) u)) ∧
        Tendsto (fun L ↦ hilbertTrace (T L) -
            (volume₁ : ℂ) * φ.val 1 * (Real.log (L * Y) : ℂ)) atTop
          (𝓝 ((volume₁ : ℂ) * principalValues(a, b) - ratPolarTerm f)) := by
  obtain ⟨T, hT, hlim⟩ := ratLevel_trace_sub_sharpMass_tendsto f hY
  refine ⟨T, hT, ?_⟩
  obtain ⟨a, b, M, ha, hb, hsum, hM⟩ := sLocalTraceSharpMass_asymptotic (F := ℚ) (S := Sq) φ
    ratPic_subsingleton ratRamified hOutside f hLift
  refine ⟨a, b, ha, hb, ?_⟩
  have hLY : Tendsto (fun L : ℝ ↦ L * Y) atTop atTop := tendsto_id.atTop_mul_const hY
  have h := (hM.comp hLY).add hlim
  rw [← sub_eq_add_neg] at h
  refine h.congr' ?_
  filter_upwards [hLY.eventually hsum] with L hs
  simp only [Function.comp_apply]
  rw [← hs.tsum_eq]
  ring

end RiemannMasullo.Isolated
