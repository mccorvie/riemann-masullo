module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5_FixedSetTrace
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalLevelIdentification
import RiemannMasullo.AppA_AlgebraicNT.Sec3

/-!
# The level trace against the global diagonal, for the rationals with no finite place

The proof of Theorem 12.5.1.1 (p. 520) uses Theorem 12.4.1.1 on the polar-free level with the two
polar Mellin values subtracted, and identifies the result with the global geometric diagonal. This
file tests that identification for `ℚ` with no finite place, at every width `α ≥ 1/2`, by putting
together two results.

* The fixed-set comparison `sLocalTraceSharpMass_tendsto_globalDiagonal_sub_omitted`: the summed
  sharp orbital masses less the two S-idelic polar values, normalized by `volF / volS`, tend to the
  global diagonal less the finite places outside the chosen set.
* The level traces of `ratMainLevel_trace_tendsto`: on `main`'s polar-free level the trace less the
  summed sharp masses tends to minus the polar term `∫ ψ(h) min (h ^ (1/2), h ^ (-1/2)) dh`.

With no finite place in the set, every prime is outside it. A test supported on idele classes of
norm strictly between one and two vanishes on every finite class, because the norm of a finite
class is an integral power of the residue cardinality (`norm_finiteClass_notMem_Ioo`), and it
vanishes on the norm-one classes. The proof on p. 520 assumes the support lies in `(1/T, T)` with
`T` below the norm of every prime outside the set, which for `ℚ` with no finite place allows
`(1/2, 2)`. The tests here satisfy that condition and also vanish at norm one, which removes the
logarithmic term. For such a test the normalized level trace tends to the global
diagonal plus `volF / volS` times `∫ ψ(h) max (h ^ (1/2), h ^ (-1/2)) dh`
(`ratMainLevel_trace_tendsto_globalDiagonal`). For a lift supported on norms at least one this is
`M(f)(|·|^(1/2))`, the polar value that the level does not remove
(`ratMainLevel_trace_tendsto_globalDiagonal_of_one_le`). For a lift with nonnegative real part,
positive somewhere, the normalized level trace does not tend to the global diagonal
(`ratLevel_not_tendsto_globalDiagonal`).

So the identification on p. 520 fails for these tests at every width at least one half, where no
zero of the completed L-functions is omitted from the strip. The failure comes from the polar-free
level alone.

Not covered: other number fields and nonempty sets of places, other twists and Sobolev orders,
and widths below one half, where the omitted zeros and edge terms of
`sLocalTrace_tendsto_globalDiagonal_iff_sharp_correction` also enter. The operators on `main`'s
level are the model's cutoff operators transported by an isometry, not an operator printed in the
paper.
-/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology InnerProductSpace

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

section FiniteClasses

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "normF(" c ")" => (((ideleClassNorm F c : ℝ≥0ˣ) : ℝ≥0) : ℝ)

/-- The norm of a finite idele class is never strictly between one and two: it is an integral power
of the residue cardinality, which is at least two. -/
theorem norm_finiteClass_notMem_Ioo (v : V) (u : (v.adicCompletion F)ˣ) :
    normF(finiteClass(v) u) ∉ Ioo (1 : ℝ) 2 := by
  have hn : normF(finiteClass(v) u) = ‖u.val‖ := by
    rw [ideleClassNorm_ofAdicCompletion]
    rfl
  rw [hn, norm_adicCompletion_eq_zpow F v u.ne_zero]
  have hq : (2 : ℝ) ≤ (v.asIdeal.absNorm : ℝ) := by
    have := HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast this
  rintro ⟨h1, h2⟩
  rcases le_or_gt (WithZero.log (Valued.v u.val)) 0 with hk | hk
  · have := zpow_le_one_of_nonpos₀ (by linarith) hk (a := (v.asIdeal.absNorm : ℝ))
    linarith
  · have hk1 : (1 : ℤ) ≤ WithZero.log (Valued.v u.val) := hk
    have := zpow_le_zpow_right₀ (a := (v.asIdeal.absNorm : ℝ)) (by linarith) hk1
    rw [zpow_one] at this
    linarith

/-- A function supported on idele classes of norm strictly between one and two vanishes on every
finite idele class. -/
theorem apply_finiteClass_eq_zero_of_support {φ : C𝔽 → ℂ}
    (hφ : ∀ c, φ c ≠ 0 → normF(c) ∈ Ioo (1 : ℝ) 2) (v : V) (u : (v.adicCompletion F)ˣ) :
    φ (finiteClass(v) u) = 0 :=
  not_not.mp fun h ↦ norm_finiteClass_notMem_Ioo v u (hφ _ h)

/-- A function supported on idele classes of norm strictly between one and two vanishes on the
norm-one classes. -/
theorem apply_normOne_eq_zero_of_support {φ : C𝔽 → ℂ}
    (hφ : ∀ c, φ c ≠ 0 → normF(c) ∈ Ioo (1 : ℝ) 2) (g : (ideleClassNorm F).ker) :
    φ g = 0 := by
  by_contra h
  have h1 := (hφ _ h).1
  rw [show ideleClassNorm F g = 1 from g.property] at h1
  simp at h1

/-- The norm-one idele classes have positive Tamagawa mass. -/
theorem levelGlobal_normOneVolume_pos :
    0 < ((normOneIdeleClassTamagawaMeasure F) univ).toReal := by
  rw [normOneIdeleClassTamagawaMeasure_volume]
  have := NumberField.classNumber_pos F
  have := NumberField.Units.regulator_pos F
  have := NumberField.Units.torsionOrder_pos F
  have := Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)
  exact ENNReal.toReal_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top

end FiniteClasses

section RatGlobal

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
local notation "μ₀" => realPWIntervalMeasure 0 0
local notation "hμ₀" => volume_le_realPWIntervalMeasure 0 0 le_rfl
local notation "V₀(" Y ")" => RealPWBand.space Y hμ₀
local notation "ev(" Y ")" => RealPWBand.evaluation Y hμ₀
local notation "levelq(" Y ")" => realPWZeroLevel Y 0 0 le_rfl
local notation "mainLevel(" Y ", " χ ")" =>
  sLocalInvariantPWSobolev (F := ℚ) (S := Sq) (s := 0) le_rfl (a := 1 / 2) (by norm_num) χ Y

/-- The two S-idelic polar values of `sLocalTraceSharpMass_tendsto_globalDiagonal_sub_omitted`,
written with square roots, are the Mellin values at `|·|^(1/2)` and `|·|^(-1/2)`. -/
theorem ratPolarSum_eq_mellin (f : BruhatCompactSupport Iq) :
    (∫ g : Iq, f.val g * rootS(g) ∂μq) + (∫ g : Iq, f.val g / rootS(g) ∂μq) =
      mellin(f, 1 / 2) + mellin(f, -(1 / 2)) := by
  congr 1
  · refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    simp only [Real.sqrt_eq_rpow]
  · refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    simp only
    rw [Real.rpow_neg (NNReal.coe_nonneg _), ← Real.sqrt_eq_rpow, Complex.ofReal_inv,
      div_eq_mul_inv]

/-- Paper: Theorem 12.4.1.1 and the proof of Theorem 12.5.1.1, step (c), p. 520, for `ℚ` with no
finite place, at a width `α ≥ 1/2`.
Reconstruction: let `t L` be any traces whose difference from the summed sharp masses at radius
`L Y` tends to minus the polar term, as the level traces of `ratMainLevel_trace_tendsto` do. Take a
global test vanishing on the norm-one classes and on every finite class, with an S-idelic lift.
Then `volF / volS` times `t L` tends to the global diagonal plus `volF / volS` times
`∫ ψ(h) max (h ^ (1/2), h ^ (-1/2)) dh`, by `sLocalTraceSharpMass_tendsto_globalDiagonal_sub_omitted`.
Deviation: The bandwidth `Y` is fixed while `L` tends to infinity. -/
theorem ratLevel_tendsto_globalDiagonal_of_local
    (φ : BruhatCompactSupport Cq) (hφ : ∀ g : C₁q, φ.val g = 0)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits ℚ Sq) (c : Cq),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (hfin : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ),
      φ.val (finiteClass(v) u) = 0)
    (f : BruhatCompactSupport Iq)
    (hLift : ∀ g : Iq, HasSum (fun ξ : Hq ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    {α s : ℝ} (hα : 1 / 2 ≤ α) (hs : 3 ≤ s)
    (hK : stripK((one_half_pos.trans_le hα).le, hs, φ))
    (U : ℕ → Set Cq) (hU : IsDPrimeSequence μℚ U) (hBorel : ∀ n, MeasurableSet (U n))
    {Y : ℝ} (hY : 0 < Y) (t : ℝ → ℂ)
    (ht : Tendsto (fun L ↦ t L - ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y)) atTop
      (𝓝 (-ratPolarTerm f))) :
    Tendsto (fun L ↦ volF / volS * t L) atTop
      (𝓝 ((∫ x, diag((one_half_pos.trans_le hα).le, hs, φ, hK, U) x ∂μℚ) +
        volF / volS * maxTerm(f))) := by
  have h := sLocalTraceSharpMass_tendsto_globalDiagonal_sub_omitted φ hφ ratPic_subsingleton
    ratRamified hOutside f hLift hα hs hK U hU hBorel
  dsimp only at h
  obtain ⟨-, hglob⟩ := h
  simp only [hfin, zero_mul, zero_div, integral_zero, mul_zero, tsum_zero, sub_zero] at hglob
  have hR : Tendsto (fun L : ℝ ↦ L * Y) atTop atTop := tendsto_id.atTop_mul_const hY
  have h2 := ((ht.const_mul (volF / volS)).add (hglob.comp hR)).add_const
    (volF / volS * ((∫ g : Iq, f.val g * rootS(g) ∂μq) + ∫ g : Iq, f.val g / rootS(g) ∂μq))
  convert h2 using 1
  · funext L
    simp only [Function.comp_apply]
    ring
  · congr 1
    have key (G a P q : ℂ) : a * -q + G + a * P = G + a * (P - q) := by ring
    rw [ratPolarSum_eq_mellin, ← ratPolarMellin_sub_ratPolarTerm, key]

set_option maxHeartbeats 4000000 in
/-- Paper: Theorem 12.4.1.1 and the proof of Theorem 12.5.1.1, step (c), p. 520, on `main`'s
polar-free level for `ℚ` with no finite place, at twist `1/2`, Sobolev order zero and a width
`α ≥ 1/2`.
Reconstruction: take a global test supported on idele classes of norm strictly between one and two,
which meets the support condition of p. 520, with an S-idelic lift. The operators of `ratMainLevel_trace_tendsto` take values in `main`'s level,
and `volF / volS` times their traces tends to the global diagonal plus `volF / volS` times
`∫ ψ(h) max (h ^ (1/2), h ^ (-1/2)) dh`. Step (c) asserts that the limit is the global diagonal.
Deviation: The bandwidth `Y` is fixed while `L` tends to infinity. The operators are the model's
cutoff operators transported to `main`'s level, not an operator printed in the paper. -/
theorem ratMainLevel_trace_tendsto_globalDiagonal
    (φ : BruhatCompactSupport Cq) (hsupp : ∀ c, φ.val c ≠ 0 → normℚ(c) ∈ Ioo (1 : ℝ) 2)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits ℚ Sq) (c : Cq),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iq)
    (hLift : ∀ g : Iq, HasSum (fun ξ : Hq ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    {α s : ℝ} (hα : 1 / 2 ≤ α) (hs : 3 ≤ s)
    (hK : stripK((one_half_pos.trans_le hα).le, hs, φ))
    (U : ℕ → Set Cq) (hU : IsDPrimeSequence μℚ U) (hBorel : ∀ n, MeasurableSet (U n))
    {Y : ℝ} (hY : 0 < Y) (χ : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker) :
    ∃ T : ℝ → nuclearEndomorphisms V₀(Y),
      (∀ L, 0 < L → ∀ v : V₀(Y), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ratFold f g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev(Y) (g⁻¹ * x) ((levelq(Y)).starProjection v))) ∧
        (T L).val v = (levelq(Y)).starProjection ((V₀(Y)).orthogonalProjectionOnto r)) ∧
      (∀ L, 0 < L → ∀ x, (conjNuclear (ratLevelIsometry Y) (T L)).val x ∈ mainLevel(Y, χ)) ∧
      Tendsto (fun L ↦ volF / volS * hilbertTrace (conjNuclear (ratLevelIsometry Y) (T L))) atTop
        (𝓝 ((∫ x, diag((one_half_pos.trans_le hα).le, hs, φ, hK, U) x ∂μℚ) +
          volF / volS * maxTerm(f))) := by
  obtain ⟨T, hT, hmem, hloc, -⟩ := ratMainLevel_trace_tendsto f hY χ
  exact ⟨T, hT, hmem, ratLevel_tendsto_globalDiagonal_of_local φ
    (apply_normOne_eq_zero_of_support hsupp) hOutside
    (apply_finiteClass_eq_zero_of_support hsupp) f hLift hα hs hK U hU hBorel hY _ hloc⟩

set_option maxHeartbeats 4000000 in
/-- Paper: Theorem 12.4.1.1, Theorem 11.3.2.1 (p. 495) and the proof of Theorem 12.5.1.1, step (c),
p. 520, for `ℚ` with no finite place at a width `α ≥ 1/2`.
Reconstruction: when the S-idelic lift is supported on norms at least one, as in the shell theorem,
the limit of `ratMainLevel_trace_tendsto_globalDiagonal` is the global diagonal plus `volF / volS`
times `M(f)(|·|^(1/2))`. The level removes `M(f)(|·|^(-1/2))` and leaves `M(f)(|·|^(1/2))`, which
p. 520 also subtracts.
Deviation: The bandwidth `Y` is fixed while `L` tends to infinity. -/
theorem ratMainLevel_trace_tendsto_globalDiagonal_of_one_le
    (φ : BruhatCompactSupport Cq) (hsupp : ∀ c, φ.val c ≠ 0 → normℚ(c) ∈ Ioo (1 : ℝ) 2)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits ℚ Sq) (c : Cq),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iq) (hf : ∀ g, f.val g ≠ 0 → 1 ≤ normq(g))
    (hLift : ∀ g : Iq, HasSum (fun ξ : Hq ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    {α s : ℝ} (hα : 1 / 2 ≤ α) (hs : 3 ≤ s)
    (hK : stripK((one_half_pos.trans_le hα).le, hs, φ))
    (U : ℕ → Set Cq) (hU : IsDPrimeSequence μℚ U) (hBorel : ∀ n, MeasurableSet (U n))
    {Y : ℝ} (hY : 0 < Y) (χ : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker) :
    ∃ T : ℝ → nuclearEndomorphisms V₀(Y),
      (∀ L, 0 < L → ∀ v : V₀(Y), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ratFold f g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev(Y) (g⁻¹ * x) ((levelq(Y)).starProjection v))) ∧
        (T L).val v = (levelq(Y)).starProjection ((V₀(Y)).orthogonalProjectionOnto r)) ∧
      (∀ L, 0 < L → ∀ x, (conjNuclear (ratLevelIsometry Y) (T L)).val x ∈ mainLevel(Y, χ)) ∧
      Tendsto (fun L ↦ volF / volS * hilbertTrace (conjNuclear (ratLevelIsometry Y) (T L))) atTop
        (𝓝 ((∫ x, diag((one_half_pos.trans_le hα).le, hs, φ, hK, U) x ∂μℚ) +
          volF / volS * mellin(f, 1 / 2))) := by
  rw [← ratMainLevel_limit_eq_of_one_le f hf]
  exact ratMainLevel_trace_tendsto_globalDiagonal φ hsupp hOutside f hLift hα hs hK U hU hBorel
    hY χ

/-- Paper: the proof of Theorem 12.5.1.1, step (c), p. 520, for `ℚ` with no finite place at a width
`α ≥ 1/2`.
Reconstruction: for a lift with nonnegative real part, positive somewhere, traces as in
`ratLevel_tendsto_globalDiagonal_of_local`, in particular the level traces of
`ratMainLevel_trace_tendsto_globalDiagonal`, normalized by `volF / volS`, do not tend to the global
diagonal. So step (c) fails for these tests on `main`'s polar-free level. -/
theorem ratLevel_not_tendsto_globalDiagonal
    (φ : BruhatCompactSupport Cq) (hφ : ∀ g : C₁q, φ.val g = 0)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits ℚ Sq) (c : Cq),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (hfin : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ),
      φ.val (finiteClass(v) u) = 0)
    (f : BruhatCompactSupport Iq) (hf : ∀ g, 0 ≤ (f.val g).re) {g₀ : Iq}
    (hg₀ : 0 < (f.val g₀).re)
    (hLift : ∀ g : Iq, HasSum (fun ξ : Hq ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    {α s : ℝ} (hα : 1 / 2 ≤ α) (hs : 3 ≤ s)
    (hK : stripK((one_half_pos.trans_le hα).le, hs, φ))
    (U : ℕ → Set Cq) (hU : IsDPrimeSequence μℚ U) (hBorel : ∀ n, MeasurableSet (U n))
    {Y : ℝ} (hY : 0 < Y) (t : ℝ → ℂ)
    (ht : Tendsto (fun L ↦ t L - ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y)) atTop
      (𝓝 (-ratPolarTerm f))) :
    ¬ Tendsto (fun L ↦ volF / volS * t L) atTop
      (𝓝 (∫ x, diag((one_half_pos.trans_le hα).le, hs, φ, hK, U) x ∂μℚ)) := by
  intro h0
  have hlim := ratLevel_tendsto_globalDiagonal_of_local φ hφ hOutside hfin f hLift hα hs hK U hU
    hBorel hY t ht
  have heq := tendsto_nhds_unique hlim h0
  have hzero : volF / volS * maxTerm(f) = 0 := by
    linear_combination heq
  have hmaxc : ContinuousOn (fun h : ℝ ↦ max (h ^ (1 / 2 : ℝ)) (h ^ (-(1 / 2 : ℝ)))) (Ioi 0) :=
    continuous_max.comp_continuousOn ((continuousOn_rpow_Ioi _).prodMk (continuousOn_rpow_Ioi _))
  have hpos := integral_ratFold_mul_re_pos f hf hg₀ hmaxc
    fun h hh ↦ lt_max_of_lt_left (Real.rpow_pos_of_pos hh _)
  have hc : 0 < ((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal /
      ((sLocalNormOneQuotientMeasure ℚ Sq) univ).toReal :=
    div_pos levelGlobal_normOneVolume_pos ratNormOneMass_pos
  have hre := congrArg Complex.re hzero
  rw [← Complex.ofReal_div, Complex.re_ofReal_mul, Complex.zero_re] at hre
  exact (mul_pos hc hpos).ne' hre

/-- Paper: §12.3, p. 514, and the proof of Theorem 12.5.1.1, step (c), p. 520, for `ℚ` with no
finite place, at any positive width.
Reconstruction: at a width `α > 0`, traces as in `ratLevel_tendsto_globalDiagonal_of_local`,
normalized by `volF / volS`, tend to the global diagonal less the Mellin terms of the zeros lost
from width one half, with their edge multiplicities, plus `volF / volS` times
`∫ ψ(h) max (h ^ (1/2), h ^ (-1/2)) dh`. This uses
`sLocalTrace_tendsto_globalDiagonal_iff_sharp_correction`. The lost zeros are a spectral term, and
the last term comes from the polar-free level and does not depend on the width.
Deviation: The bandwidth `Y` is fixed while `L` tends to infinity. -/
theorem ratLevel_tendsto_globalDiagonal_of_local_width
    (φ : BruhatCompactSupport Cq) (hφ : ∀ g : C₁q, φ.val g = 0)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits ℚ Sq) (c : Cq),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (hfin : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ),
      φ.val (finiteClass(v) u) = 0)
    (f : BruhatCompactSupport Iq)
    (hLift : ∀ g : Iq, HasSum (fun ξ : Hq ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (χ : PontryaginDual C₁q → PontryaginDual Cq) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) (hK : stripK(hα.le, hs, φ))
    (U : ℕ → Set Cq) (hU : IsDPrimeSequence μℚ U) (hBorel : ∀ n, MeasurableSet (U n))
    {Y : ℝ} (hY : 0 < Y) (t : ℝ → ℂ)
    (ht : Tendsto (fun L ↦ t L - ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y)) atTop
      (𝓝 (-ratPolarTerm f))) :
    let shift (b t : ℝ) := (b : ℂ) + (t : ℂ) * Complex.I
    let order (z : PontryaginDual C₁q × ℝ × ℝ) :=
      meromorphicOrderAt (continuedCompletedHeckeL (χ z.1)) (shift (1 / 2 + z.2.1) z.2.2)
    let retained (β : ℝ) := {z | z.2.1 ∈ Icc (-β) β ∧ 0 < order z}.indicator (fun z ↦
      (spectralStripMultiplicity β s z.2.1 (order z).untop₀.toNat : ℂ) *
        modulatedFourierMellin (continuousIdeleClassNorm ℚ) univ
          ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one⟩
          μℚ φ.val (ideleClassNormTwist (χ z.1) (shift z.2.1 z.2.2)))
    let loss := fun z ↦ retained (1 / 2) z - retained α z
    Tendsto (fun L ↦ volF / volS * t L) atTop
      (𝓝 ((∫ x, diag(hα.le, hs, φ, hK, U) x ∂μℚ) - (∑' z, loss z) +
        volF / volS * maxTerm(f))) := by
  have h := sLocalTrace_tendsto_globalDiagonal_iff_sharp_correction φ hφ ratPic_subsingleton
    ratRamified hOutside f hLift χ hχ hα hs hK U hU hBorel
  dsimp only at h ⊢
  obtain ⟨-, hglob, -⟩ := h
  simp only [hfin, zero_mul, zero_div, integral_zero, mul_zero, tsum_zero, add_zero] at hglob
  have hR : Tendsto (fun L : ℝ ↦ L * Y) atTop atTop := tendsto_id.atTop_mul_const hY
  have h2 := ((ht.const_mul (volF / volS)).add (hglob.comp hR)).add_const
    (volF / volS * ((∫ g : Iq, f.val g * rootS(g) ∂μq) + ∫ g : Iq, f.val g / rootS(g) ∂μq))
  convert h2 using 1
  · funext L
    simp only [Function.comp_apply]
    ring
  · congr 1
    have key (G E a P q : ℂ) : a * -q + (G - E) + a * P = G - E + a * (P - q) := by ring
    rw [ratPolarSum_eq_mellin, ← ratPolarMellin_sub_ratPolarTerm, key]

end RatGlobal

end RiemannMasullo.Isolated
