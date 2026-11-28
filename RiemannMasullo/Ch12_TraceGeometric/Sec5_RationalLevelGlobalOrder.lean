module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5_RationalLevelGlobal
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalLevelOrder

/-!
# The level trace against the global diagonal at every Sobolev order, for the rationals

`Sec5_RationalLevelGlobal` proves, at Sobolev order zero of the local level, that for `ℚ` with no
finite place the normalized trace on `main`'s polar-free level misses the global diagonal by
`volF / volS · M(f)(|·|^(1/2))`, at every width at least one half. `Sec4_RationalLevelOrder`
identifies `main`'s level at every Sobolev order `s₀ ≥ 0` with the level of the weighted model band
and transfers the local limit. This file combines the two, so the same failure holds at every
Sobolev order `s₀ ≥ 0` of the local level.

* `ratMainLevelOrder_trace_tendsto_globalDiagonal`. The limit at order `s₀`.
* `ratMainLevelOrder_trace_tendsto_globalDiagonal_of_one_le`. For a lift also supported on norms at
  least one, the extra term is `volF / volS · M(f)(|·|^(1/2))`.
* `ratMainLevelOrder_not_tendsto_globalDiagonal`. For a nonnegative lift, positive somewhere, the
  normalized traces at order `s₀` do not tend to the global diagonal.

The lift is assumed to have folded form vanishing outside `[a, b]` with `1 < a`, which the
weighted model trace requires.
-/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology InnerProductSpace

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

section RatGlobalOrder

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b instMeasurableSpaceInfiniteAdeleRing_riemannMasullo
  instRatSIdeleT2 instRatSAdeleT2 instIdeleClassBorelSpaceSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSpectralQuotientPolynormableSec3

attribute [-instance] Quotient.instMeasurableSpace

set_option maxSynthPendingDepth 8

local notation "Sq" => (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
local notation "Iq" => (SAdeleRing ℚ Sq)ˣ
local notation "Hq" => sProjectedDiagonal ℚ Sq
local notation "μq" => sMultiplicativeTamagawaMeasure ℚ Sq
local notation "Cq" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "C₁q" => (ideleClassNorm ℚ).ker
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "volS" => (((sLocalNormOneQuotientMeasure ℚ Sq) univ).toReal : ℂ)
local notation "volF" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "rootS(" g ")" => (Real.sqrt (((sIdeleNorm ℚ Sq g).val : ℝ)) : ℂ)
local notation "classAtS(" g ")" => (QuotientGroup.mk (sIdeleInsertion ℚ Sq g) : Cq)
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v
local notation "normℚ(" c ")" => (((ideleClassNorm ℚ c : ℝ≥0ˣ) : ℝ≥0) : ℝ)
local notation "normq(" x ")" => (((sIdeleNorm ℚ Sq x).val : ℝ))
local notation "mellin(" f ", " α ")" => ∫ g, (f).val g * ((normq(g) ^ (α : ℝ) : ℝ) : ℂ) ∂μq
local notation "maxTerm(" f ")" =>
  ∫ h in Ioi 0, ratFold f h * ((max (h ^ (1 / 2 : ℝ)) (h ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ)
local notation "hs₁(" hs ")" => (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hs)
local notation "hs₀(" hs ")" => (le_of_lt (zero_lt_one.trans hs₁(hs)))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "stripK(" hα ", " hs ", " φ ")" =>
  (∃ K, sobolevProjectiveKernelOperator (F := ℚ) hα hs₀(hs) K =
    (hardySobolevTestAction μℚ (continuousIdeleClassNorm ℚ) _ _ _ (hStrip(hα)) hs₀(hs) φ).comp
      (spectralProjection (F := ℚ) (1 / 2) hα hs₀(hs)))
local notation "diag(" hα "," hs "," φ "," hK "," U ")" =>
  (fun x : Cq ↦ dSequenceKernelSmoothening μℚ U
    (globalStripGeometricKernel (F := ℚ) (1 / 2) hα hs₁(hs) φ hK) (x, x))
variable {s₀ : ℝ}

local notation "μs(" s ")" => realPWIntervalMeasure 0 s
local notation "Vs(" Y ", " hs ")" => RealPWBand.space Y (volume_le_realPWIntervalMeasure 0 _ hs)
local notation "evs(" Y ", " hs ")" =>
  RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure 0 _ hs)
local notation "mainLevels(" Y ", " χ ", " hs ")" =>
  sLocalInvariantPWSobolev (F := ℚ) (S := Sq) hs (a := 1 / 2) (by norm_num) χ Y

set_option maxHeartbeats 4000000 in
/-- Paper: Theorem 12.4.1.1 and the proof of Theorem 12.5.1.1, step (c), p. 520, on `main`'s
polar-free level for `ℚ` with no finite place, at twist `1/2`, every Sobolev order `s₀ ≥ 0` of the
local level, and a width `α ≥ 1/2`.
Reconstruction: take a global test supported on idele classes of norm strictly between one and two,
with an S-idelic lift whose folded form vanishes outside `[a, b]` with `1 < a`. The operators of
`ratMainLevelOrder_trace_tendsto` take values in `main`'s level at order `s₀`, and `volF / volS`
times their traces tends to the global diagonal plus `volF / volS` times
`∫ ψ(h) max (h ^ (1/2), h ^ (-1/2)) dh`, which is `volF / volS · M(f)(|·|^(1/2))` for these tests.
Step (c) asserts that the limit is the global diagonal.
Deviation: The bandwidth `Y` is fixed while `L` tends to infinity. The operators are the model's
cutoff operators transported to `main`'s level, not an operator printed in the paper. -/
theorem ratMainLevelOrder_trace_tendsto_globalDiagonal
    (φ : BruhatCompactSupport Cq) (hsupp : ∀ c, φ.val c ≠ 0 → normℚ(c) ∈ Ioo (1 : ℝ) 2)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits ℚ Sq) (c : Cq),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iq) {a b : ℝ} (ha1 : 1 < a)
    (hfold : ∀ g ∉ Icc a b, ratFold f g = 0)
    (hLift : ∀ g : Iq, HasSum (fun ξ : Hq ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    {α s : ℝ} (hα : 1 / 2 ≤ α) (hs : 3 ≤ s)
    (hK : stripK((one_half_pos.trans_le hα).le, hs, φ))
    (U : ℕ → Set Cq) (hU : IsDPrimeSequence μℚ U) (hBorel : ∀ n, MeasurableSet (U n))
    {Y : ℝ} (hY : 0 < Y) (hs₀ : 0 ≤ s₀) (χ : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker) :
    ∃ T : ℝ → nuclearEndomorphisms Vs(Y, hs₀),
      (∀ L (v : Vs(Y, hs₀)), ∃ r : Lp ℂ 2 μs(s₀),
        (∀ᵐ x ∂μs(s₀), r x = sharpIntervalMask L x *
          ∫ g, ratFold f g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            evs(Y, hs₀) (g⁻¹ * x) ((realPWZeroLevel Y 0 s₀ hs₀).starProjection v))) ∧
        (T L).val v =
          (realPWZeroLevel Y 0 s₀ hs₀).starProjection ((Vs(Y, hs₀)).orthogonalProjectionOnto r)) ∧
      (∀ L x, (conjNuclear (ratLevelIsometryOrder Y hs₀) (T L)).val x ∈ mainLevels(Y, χ, hs₀)) ∧
      Tendsto (fun L ↦ volF / volS * hilbertTrace (conjNuclear (ratLevelIsometryOrder Y hs₀) (T L)))
        atTop (𝓝 ((∫ x, diag((one_half_pos.trans_le hα).le, hs, φ, hK, U) x ∂μℚ) +
          volF / volS * maxTerm(f))) := by
  obtain ⟨T, hT, hmem, hloc⟩ := ratMainLevelOrder_trace_tendsto f hY hs₀ ha1 hfold χ
  exact ⟨T, hT, hmem, ratLevel_tendsto_globalDiagonal_of_local φ
    (apply_normOne_eq_zero_of_support hsupp) hOutside
    (apply_finiteClass_eq_zero_of_support hsupp) f hLift hα hs hK U hU hBorel hY _ hloc⟩

set_option maxHeartbeats 4000000 in
/-- Paper: Theorem 12.4.1.1, Theorem 11.3.2.1 (p. 495) and the proof of Theorem 12.5.1.1, step (c),
p. 520, for `ℚ` with no finite place, at every Sobolev order `s₀ ≥ 0` of the local level and a width
`α ≥ 1/2`.
Reconstruction: when the S-idelic lift is also supported on norms at least one, as in the shell
theorem, the limit of `ratMainLevelOrder_trace_tendsto_globalDiagonal` is the global diagonal plus
`volF / volS` times `M(f)(|·|^(1/2))`. The level removes `M(f)(|·|^(-1/2))` and leaves
`M(f)(|·|^(1/2))`, which p. 520 also subtracts.
Deviation: The bandwidth `Y` is fixed while `L` tends to infinity. -/
theorem ratMainLevelOrder_trace_tendsto_globalDiagonal_of_one_le
    (φ : BruhatCompactSupport Cq) (hsupp : ∀ c, φ.val c ≠ 0 → normℚ(c) ∈ Ioo (1 : ℝ) 2)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits ℚ Sq) (c : Cq),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iq) (hf : ∀ g, f.val g ≠ 0 → 1 ≤ normq(g)) {a b : ℝ} (ha1 : 1 < a)
    (hfold : ∀ g ∉ Icc a b, ratFold f g = 0)
    (hLift : ∀ g : Iq, HasSum (fun ξ : Hq ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    {α s : ℝ} (hα : 1 / 2 ≤ α) (hs : 3 ≤ s)
    (hK : stripK((one_half_pos.trans_le hα).le, hs, φ))
    (U : ℕ → Set Cq) (hU : IsDPrimeSequence μℚ U) (hBorel : ∀ n, MeasurableSet (U n))
    {Y : ℝ} (hY : 0 < Y) (hs₀ : 0 ≤ s₀) (χ : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker) :
    ∃ T : ℝ → nuclearEndomorphisms Vs(Y, hs₀),
      (∀ L x, (conjNuclear (ratLevelIsometryOrder Y hs₀) (T L)).val x ∈ mainLevels(Y, χ, hs₀)) ∧
      Tendsto (fun L ↦ volF / volS * hilbertTrace (conjNuclear (ratLevelIsometryOrder Y hs₀) (T L)))
        atTop (𝓝 ((∫ x, diag((one_half_pos.trans_le hα).le, hs, φ, hK, U) x ∂μℚ) +
          volF / volS * mellin(f, 1 / 2))) := by
  obtain ⟨T, -, hmem, hlim⟩ := ratMainLevelOrder_trace_tendsto_globalDiagonal φ hsupp hOutside f
    ha1 hfold hLift hα hs hK U hU hBorel hY hs₀ χ
  rw [← ratMainLevel_limit_eq_of_one_le f hf]
  exact ⟨T, hmem, hlim⟩

set_option maxHeartbeats 4000000 in
/-- Paper: the proof of Theorem 12.5.1.1, step (c), p. 520, for `ℚ` with no finite place, at every
Sobolev order `s₀ ≥ 0` of the local level and a width `α ≥ 1/2`.
Reconstruction: for a lift with nonnegative real part, positive somewhere, whose folded form
vanishes outside `[a, b]` with `1 < a`, the operators of `ratMainLevelOrder_trace_tendsto` on
`main`'s level at order `s₀`, normalized by `volF / volS`, have traces that do not tend to the
global diagonal. -/
theorem ratMainLevelOrder_not_tendsto_globalDiagonal
    (φ : BruhatCompactSupport Cq) (hsupp : ∀ c, φ.val c ≠ 0 → normℚ(c) ∈ Ioo (1 : ℝ) 2)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits ℚ Sq) (c : Cq),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iq) (hf : ∀ g, 0 ≤ (f.val g).re) {g₀ : Iq}
    (hg₀ : 0 < (f.val g₀).re) {a b : ℝ} (ha1 : 1 < a) (hfold : ∀ g ∉ Icc a b, ratFold f g = 0)
    (hLift : ∀ g : Iq, HasSum (fun ξ : Hq ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    {α s : ℝ} (hα : 1 / 2 ≤ α) (hs : 3 ≤ s)
    (hK : stripK((one_half_pos.trans_le hα).le, hs, φ))
    (U : ℕ → Set Cq) (hU : IsDPrimeSequence μℚ U) (hBorel : ∀ n, MeasurableSet (U n))
    {Y : ℝ} (hY : 0 < Y) (hs₀ : 0 ≤ s₀) (χ : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker) :
    ∃ T : ℝ → nuclearEndomorphisms Vs(Y, hs₀),
      (∀ L x, (conjNuclear (ratLevelIsometryOrder Y hs₀) (T L)).val x ∈ mainLevels(Y, χ, hs₀)) ∧
      ¬ Tendsto (fun L ↦ volF / volS * hilbertTrace (conjNuclear (ratLevelIsometryOrder Y hs₀) (T L)))
        atTop (𝓝 (∫ x, diag((one_half_pos.trans_le hα).le, hs, φ, hK, U) x ∂μℚ)) := by
  obtain ⟨T, -, hmem, hloc⟩ := ratMainLevelOrder_trace_tendsto f hY hs₀ ha1 hfold χ
  exact ⟨T, hmem, ratLevel_not_tendsto_globalDiagonal φ (apply_normOne_eq_zero_of_support hsupp)
    hOutside (apply_finiteClass_eq_zero_of_support hsupp) f hf hg₀ hLift hα hs hK U hU hBorel hY _
    hloc⟩

end RatGlobalOrder

end RiemannMasullo.Isolated
