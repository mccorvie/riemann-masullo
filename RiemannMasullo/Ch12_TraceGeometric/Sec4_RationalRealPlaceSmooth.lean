module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalRealPlace

/-!
# Smoothed cutoffs for the rationals with no finite place

The operator of Theorem 12.4.1.1 uses smooth cutoffs. In Step II (p. 516) the spatial cutoff
`ρ` smooths the indicator of `|x| ≤ λ` and the frequency cutoff `σ` smooths the indicator of
`|u| ≤ λ'`, each over a transition of width `ε`. Equation (12.4.1.22) then replaces both by the
sharp indicators. As an equality this fails (`Printed.sLocalSmoothMass_eq_sharp_real_false`), and
`Sec4.lean` states the theorem with the comparison as a hypothesis
(`sLocalTrace_asymptotic_of_sharp_comparison`). This file proves the comparison for `ℚ` with no
finite place, in the regime of p. 519, where `ε λ` and `ε λ'` tend to zero.

The cutoff kernel on the skew diagonal at the point with real coordinate `t` is
`ρ(t) ∫ ψ(s) |s| ^ (-3/2) σ̂(σ₀ t / s - t) ds`, where `σ̂` is the Fourier integral of the
frequency profile (`ratCutoffKernel_diag_profile`). Its integral over `(0, L]` is the smoothed
orbital mass `ratSmoothMass` (`ratSmoothMass_eq`), and for the sharp indicators it is the sharp
mass of `Sec4.lean` (`ratSharpMass_eq_phase`). Changing the spatial cutoff costs at most the
length `ε` of its transition times `2 Y ∫ |ψ(s)| |s| ^ (-3/2) ds`. Changing the frequency cutoff
moves its Fourier integral by at most `2 ε` everywhere, which costs at most
`2 ε L ∫ |ψ(s)| |s| ^ (-3/2) ds`. So each smoothed mass is within
`2 ε (L + Y) ∫ |ψ(s)| |s| ^ (-3/2) ds` of the sharp one (`norm_ratSmoothMass_sub_le`). With
`sLocalTraceSharpMass_asymptotic` this gives Theorem 12.4.1.1 for the smoothed masses
(`ratSmoothTrace_asymptotic`).

The cutoffs only need to be measurable, so the smooth ones of the paper are included. The bound
uses the sizes `L` and `Y` of the cutoffs and does not tend to zero for a fixed width `ε`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set NumberField IsDedekindDomain
open scoped Topology NumberField Real ENNReal

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
local notation "νq" => sAdditiveTamagawaMeasure ℚ Sq
local notation "μq" => sMultiplicativeTamagawaMeasure ℚ Sq
local notation "normq(" x ")" => (((sIdeleNorm ℚ Sq x).val : ℝ))
local notation "eq" => ratRealCoordEquiv

section PhaseIntegral

/-- The Fourier integral `∫ g(v) e^{2π i c v} dv` of a profile on the line. -/
def ratPhaseIntegral (g : ℝ → ℂ) (c : ℝ) : ℂ :=
  ∫ v, g v * (Circle.exp (2 * π * (c * v)) : ℂ)

theorem continuous_circleExp_phase (c : ℝ) :
    Continuous fun v : ℝ ↦ (Circle.exp (2 * π * (c * v)) : ℂ) :=
  continuous_subtype_val.comp (Circle.exp.continuous.comp (by fun_prop))

theorem norm_ratPhaseIntegral_le (g : ℝ → ℂ) (c : ℝ) :
    ‖ratPhaseIntegral g c‖ ≤ ∫ v, ‖g v‖ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext v
  rw [norm_mul, Circle.norm_coe, mul_one]

theorem continuous_ratPhaseIntegral {g : ℝ → ℂ} (hg : Integrable g) :
    Continuous (ratPhaseIntegral g) := by
  refine continuous_of_dominated (bound := fun v ↦ ‖g v‖)
    (fun c ↦ hg.1.mul (continuous_circleExp_phase c).aestronglyMeasurable)
    (fun c ↦ ae_of_all _ fun v ↦ by rw [norm_mul, Circle.norm_coe, mul_one]) hg.norm
    (ae_of_all _ fun v ↦ ?_)
  exact continuous_const.mul
    (continuous_subtype_val.comp (Circle.exp.continuous.comp (by fun_prop)))

theorem ratPhaseIntegral_sub {g h : ℝ → ℂ} (hg : Integrable g) (hh : Integrable h) (c : ℝ) :
    ratPhaseIntegral (g - h) c = ratPhaseIntegral g c - ratPhaseIntegral h c := by
  have hph : ∀ k : ℝ → ℂ, Integrable k →
      Integrable fun v ↦ k v * (Circle.exp (2 * π * (c * v)) : ℂ) := fun k hk ↦
    hk.mul_bdd (c := 1) (continuous_circleExp_phase c).aestronglyMeasurable
      (ae_of_all _ fun v ↦ by rw [Circle.norm_coe])
  rw [ratPhaseIntegral, ratPhaseIntegral, ratPhaseIntegral, ← integral_sub (hph g hg) (hph h hh)]
  congr 1
  funext v
  rw [Pi.sub_apply, sub_mul]

/-- The Fourier integral of the indicator of `[-Y, Y]` is the sinc kernel. -/
theorem ratPhaseIntegral_indicator {Y : ℝ} (hY : 0 ≤ Y) (c : ℝ) :
    ratPhaseIntegral ((Icc (-Y) Y).indicator fun _ ↦ (1 : ℂ)) c =
      ((2 * Y * Real.sinc (2 * π * c * Y) : ℝ) : ℂ) := by
  calc ratPhaseIntegral ((Icc (-Y) Y).indicator fun _ ↦ (1 : ℂ)) c
      = ∫ v, (Icc (-Y) Y).indicator (fun v ↦ (Circle.exp (2 * π * (c * v)) : ℂ)) v := by
        refine integral_congr_ae (ae_of_all _ fun v ↦ ?_)
        by_cases hv : v ∈ Icc (-Y) Y <;> simp [hv]
    _ = ∫ v in (-Y)..Y, Complex.exp (((2 * π * c * v : ℝ) : ℂ) * Complex.I) := by
        rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by linarith)]
        refine intervalIntegral.integral_congr fun v _ ↦ ?_
        simp only [Circle.coe_exp]
        congr 2
        push_cast
        ring
    _ = _ := by rw [integral_exp_mul_I_symm]

/-- Integrating the phase `exp (2π i c(s) v)` against an integrable profile in `v`. -/
theorem integral_mul_integral_phase {G : ℝ → ℂ} (hG : Continuous G) (hGc : HasCompactSupport G)
    (c : ℝ → ℝ) (hc : Measurable c) {g : ℝ → ℂ} (hg : Integrable g) :
    ∫ v, g v * ∫ s, G s * (Circle.exp (2 * π * (c s * v)) : ℂ) =
      ∫ s, G s * ratPhaseIntegral g (c s) := by
  have hGi : Integrable G := hG.integrable_of_hasCompactSupport hGc
  have hph : Measurable fun p : ℝ × ℝ ↦ (Circle.exp (2 * π * (c p.2 * p.1)) : ℂ) :=
    (continuous_subtype_val.comp Circle.exp.continuous).measurable.comp
      (measurable_const.mul ((hc.comp measurable_snd).mul measurable_fst))
  have hint : Integrable (Function.uncurry fun v s ↦
      g v * (G s * (Circle.exp (2 * π * (c s * v)) : ℂ))) (volume.prod volume) := by
    refine (hg.norm.mul_prod hGi.norm).mono' ?_ (ae_of_all _ fun p ↦ ?_)
    · exact hg.1.comp_fst.mul ((hG.measurable.comp measurable_snd).mul hph).aestronglyMeasurable
    · simp only [Function.uncurry, norm_mul, Circle.norm_coe, mul_one]
      rfl
  calc ∫ v, g v * ∫ s, G s * (Circle.exp (2 * π * (c s * v)) : ℂ)
      = ∫ v, ∫ s, g v * (G s * (Circle.exp (2 * π * (c s * v)) : ℂ)) := by
        congr 1
        funext v
        exact (integral_const_mul _ _).symm
    _ = ∫ s, ∫ v, g v * (G s * (Circle.exp (2 * π * (c s * v)) : ℂ)) :=
        integral_integral_swap hint
    _ = ∫ s, G s * ratPhaseIntegral g (c s) := by
        congr 1
        funext s
        rw [ratPhaseIntegral, ← integral_const_mul]
        congr 1
        funext v
        ring

end PhaseIntegral

section SmoothDiagonal

/-- A profile bounded by one and vanishing beyond `Y`, read at `|v|`, is integrable, with
integral of the norm at most `2 Y`. -/
theorem integrable_profile {σ : ℝ → ℝ} (hσm : Measurable σ) (h01 : ∀ v, 0 ≤ σ v ∧ σ v ≤ 1)
    {Y : ℝ} (hY : 0 ≤ Y) (h0 : ∀ v, Y < v → σ v = 0) :
    Integrable (fun v : ℝ ↦ (σ |v| : ℂ)) ∧ ∫ v, ‖(σ |v| : ℂ)‖ ≤ 2 * Y := by
  have hind : Integrable ((Icc (-Y) Y).indicator fun _ ↦ (1 : ℝ)) :=
    (integrableOn_const (hs := measure_Icc_lt_top.ne) (C := (1 : ℝ))).integrable_indicator
      measurableSet_Icc
  have hle (v : ℝ) : ‖(σ |v| : ℂ)‖ ≤ (Icc (-Y) Y).indicator (fun _ ↦ (1 : ℝ)) v := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h01 _).1]
    by_cases hv : v ∈ Icc (-Y) Y
    · rw [indicator_of_mem hv]
      exact (h01 _).2
    · have hY : Y < |v| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hv
        rcases hv with h | h
        · exact lt_abs.2 (Or.inr (by linarith))
        · exact lt_abs.2 (Or.inl h)
      rw [indicator_of_notMem hv, h0 _ hY]
  have hint : Integrable (fun v : ℝ ↦ (σ |v| : ℂ)) :=
    hind.mono' (Complex.measurable_ofReal.comp (hσm.comp continuous_abs.measurable)).aestronglyMeasurable
      (ae_of_all _ hle)
  refine ⟨hint, (integral_mono hint.norm hind hle).trans ?_⟩
  rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one]
  rw [Real.volume_real_Icc_of_le (by linarith)]
  linarith

/-- Paper: Step II and (12.4.1.12)–(12.4.1.15), pp. 516–518, for `ℚ` with no finite place.
Reconstruction: with a spatial cutoff `ρ` and a frequency cutoff `σ`, both functions of the
absolute value, the cutoff kernel on the skew diagonal at the point with real coordinate `t > 0`
is `ρ(t) ∫ ψ(s) |s| ^ (-3/2) σ̂(σ₀ t / s - t) ds`, where `σ̂` is the Fourier integral of
`v ↦ σ(|v|)` and `σ₀ = ±1` is the unit. -/
theorem ratCutoffKernel_diag_profile (f : BruhatCompactSupport Iq) (ξ : Hq) (ρ σ : ℝ → ℝ)
    (hσ : Integrable fun v : ℝ ↦ (σ |v| : ℂ)) {t : ℝ} (ht : 0 < t) :
    sLocalTraceCutoffKernel f (fun x ↦ (ρ normq(x) : ℂ)) (fun u ↦ (σ |eq u| : ℂ))
        (ξ.val * ratUnit t) (ratUnit t).val =
      (ρ t : ℂ) * ∫ s, ratProfile f s *
        ratPhaseIntegral (fun v ↦ (σ |v| : ℂ)) (s⁻¹ * (eq ξ.val.val * t) - t) := by
  have ht0 : t ≠ 0 := ht.ne'
  have hσ1 : |eq ξ.val.val| = 1 := by
    rcases (mem_ratProjectedDiagonal_iff _).1 ξ.property with h | h <;> simp [h]
  have hx : eq (ξ.val * ratUnit t).val = eq ξ.val.val * t := by
    rw [Units.val_mul, map_mul, eq_ratUnit ht0]
  have hn : normq(ξ.val * ratUnit t) = t := by
    rw [ratNormq, hx, abs_mul, hσ1, one_mul, abs_of_pos ht]
  simp only [sLocalTraceCutoffKernel]
  rw [hn, ratIntegral_add]
  congr 1
  have hc : Measurable fun s : ℝ ↦ s⁻¹ * (eq ξ.val.val * t) - t := by fun_prop
  refine Eq.trans ?_ (integral_mul_integral_phase (continuous_ratProfile f)
    (hasCompactSupport_ratProfile f) (fun s ↦ s⁻¹ * (eq ξ.val.val * t) - t) hc hσ)
  refine integral_congr_ae (ae_of_all _ fun v ↦ ?_)
  beta_reduce
  rw [ratDilationKernel_phase]
  simp only [hx, eq_ratUnit ht0, RingEquiv.apply_symm_apply]
  rfl

/-- Paper: (12.4.1.11)–(12.4.1.12), pp. 517–518, for `ℚ` with no finite place.
The orbital mass of the unit `ξ` for the cutoff kernel with spatial cutoff `ρ` and frequency
cutoff `σ`: the integral of the kernel on the skew diagonal over the positive reals, the S-unit
fundamental domain, against additive measure.
Deviation: The spatial integral is restricted to norm at most `L`, where the spatial cutoff of
the paper is supported. -/
def ratSmoothMass (f : BruhatCompactSupport Iq) (ξ : Hq) (ρ σ : ℝ → ℝ) (L : ℝ) : ℂ :=
  ∫ x in {x : Iq | 0 < eq x.val} ∩ {x : Iq | normq(x) ≤ L},
    sLocalTraceCutoffKernel f (fun x ↦ (ρ normq(x) : ℂ)) (fun u ↦ (σ |eq u| : ℂ))
      (ξ.val * x) x.val ∂((νq).comap Units.val)

/-- The integral over the line in the smoothed orbital mass. -/
def ratPhaseMass (f : BruhatCompactSupport Iq) (g : ℝ → ℂ) (σ₀ t : ℝ) : ℂ :=
  ∫ s, ratProfile f s * ratPhaseIntegral g (s⁻¹ * (σ₀ * t) - t)

/-- The smoothed orbital mass as an integral on the line. -/
theorem ratSmoothMass_eq (f : BruhatCompactSupport Iq) (ξ : Hq) (ρ σ : ℝ → ℝ)
    (hσ : Integrable fun v : ℝ ↦ (σ |v| : ℂ)) (L : ℝ) :
    ratSmoothMass f ξ ρ σ L = ∫ t in Ioc 0 L,
      (ρ t : ℂ) * ratPhaseMass f (fun v ↦ (σ |v| : ℂ)) (eq ξ.val.val) t := by
  rw [ratSmoothMass, ratSetIntegral_comap]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
  rw [ratLift_of_ne ht.1.ne']
  exact ratCutoffKernel_diag_profile f ξ ρ σ hσ ht.1

/-- The sharp orbital mass in the same form, with the indicator of `[-Y, Y]` as profile. -/
theorem ratSharpMass_eq_phase (f : BruhatCompactSupport Iq) (ξ : Hq) {L Y : ℝ} (hL : 0 < L)
    (hY : 0 < Y) :
    sLocalTraceSharpMass f ξ (L * Y) = ∫ t in Ioc 0 L,
      ratPhaseMass f ((Icc (-Y) Y).indicator fun _ ↦ (1 : ℂ)) (eq ξ.val.val) t := by
  rw [ratSharpMass_eq f ξ hL hY]
  simp only [ratPhaseMass, ratPhaseIntegral_indicator hY.le]

end SmoothDiagonal

section Comparison

theorem integrable_ratProfile (f : BruhatCompactSupport Iq) : Integrable (ratProfile f) :=
  (continuous_ratProfile f).integrable_of_hasCompactSupport (hasCompactSupport_ratProfile f)

theorem integrable_ratProfile_mul_phase (f : BruhatCompactSupport Iq) {g : ℝ → ℂ}
    (hg : Integrable g) (σ₀ t : ℝ) :
    Integrable fun s ↦ ratProfile f s * ratPhaseIntegral g (s⁻¹ * (σ₀ * t) - t) :=
  (integrable_ratProfile f).mul_bdd (c := ∫ v, ‖g v‖)
    ((continuous_ratPhaseIntegral hg).measurable.comp
      (by fun_prop : Measurable fun s : ℝ ↦ s⁻¹ * (σ₀ * t) - t)).aestronglyMeasurable
    (ae_of_all _ fun _ ↦ norm_ratPhaseIntegral_le _ _)

theorem norm_ratPhaseMass_le (f : BruhatCompactSupport Iq) (g : ℝ → ℂ) (σ₀ t : ℝ) :
    ‖ratPhaseMass f g σ₀ t‖ ≤ (∫ s, ‖ratProfile f s‖) * ∫ v, ‖g v‖ := by
  rw [ratPhaseMass, ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((integrable_ratProfile f).norm.mul_const _)
    (ae_of_all _ fun s ↦ ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_ratPhaseIntegral_le _ _) (norm_nonneg _)

theorem ratPhaseMass_sub (f : BruhatCompactSupport Iq) {g h : ℝ → ℂ} (hg : Integrable g)
    (hh : Integrable h) (σ₀ t : ℝ) :
    ratPhaseMass f g σ₀ t - ratPhaseMass f h σ₀ t = ratPhaseMass f (g - h) σ₀ t := by
  rw [ratPhaseMass, ratPhaseMass, ratPhaseMass,
    ← integral_sub (integrable_ratProfile_mul_phase f hg σ₀ t)
      (integrable_ratProfile_mul_phase f hh σ₀ t)]
  congr 1
  funext s
  rw [ratPhaseIntegral_sub hg hh, mul_sub]

theorem continuous_ratPhaseMass (f : BruhatCompactSupport Iq) {g : ℝ → ℂ} (hg : Integrable g)
    (σ₀ : ℝ) : Continuous fun t ↦ ratPhaseMass f g σ₀ t := by
  refine continuous_of_dominated (bound := fun s ↦ ‖ratProfile f s‖ * ∫ v, ‖g v‖)
    (fun t ↦ (integrable_ratProfile_mul_phase f hg σ₀ t).1) (fun t ↦ ae_of_all _ fun s ↦ ?_)
    ((integrable_ratProfile f).norm.mul_const _) (ae_of_all _ fun s ↦ ?_)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_ratPhaseIntegral_le _ _) (norm_nonneg _)
  · exact continuous_const.mul ((continuous_ratPhaseIntegral hg).comp (by fun_prop))

/-- A frequency profile equal to one up to `Y - ε` and vanishing beyond `Y` differs from the
indicator of `[-Y, Y]` by at most `2 ε` in `L¹`. -/
theorem integral_norm_profile_sub_le {σ : ℝ → ℝ}
    (h01 : ∀ v, 0 ≤ σ v ∧ σ v ≤ 1) {Y ε : ℝ} (hε : 0 ≤ ε) (hεY : ε ≤ Y)
    (h1 : ∀ v, 0 ≤ v → v ≤ Y - ε → σ v = 1) (h0 : ∀ v, Y < v → σ v = 0) :
    ∫ v, ‖(σ |v| : ℂ) - (Icc (-Y) Y).indicator (fun _ ↦ (1 : ℂ)) v‖ ≤ 2 * ε := by
  have hIcc : Integrable ((Icc (-Y) Y).indicator fun _ ↦ (1 : ℝ)) :=
    (integrableOn_const (hs := measure_Icc_lt_top.ne) (C := (1 : ℝ))).integrable_indicator
      measurableSet_Icc
  have hmem (v : ℝ) : v ∈ Icc (-Y) Y ↔ |v| ≤ Y := abs_le.symm
  have hbm : Measurable fun v : ℝ ↦ (Ioc (Y - ε) Y).indicator (fun _ ↦ (1 : ℝ)) |v| :=
    (measurable_const.indicator measurableSet_Ioc).comp continuous_abs.measurable
  have hbi : Integrable fun v : ℝ ↦ (Ioc (Y - ε) Y).indicator (fun _ ↦ (1 : ℝ)) |v| := by
    refine hIcc.mono' hbm.aestronglyMeasurable (ae_of_all _ fun v ↦ ?_)
    by_cases hv : |v| ∈ Ioc (Y - ε) Y
    · rw [Real.norm_eq_abs, indicator_of_mem hv, indicator_of_mem ((hmem v).2 hv.2), abs_one]
    · rw [indicator_of_notMem hv, norm_zero]
      exact indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hle (v : ℝ) : ‖(σ |v| : ℂ) - (Icc (-Y) Y).indicator (fun _ ↦ (1 : ℂ)) v‖ ≤
      (Ioc (Y - ε) Y).indicator (fun _ ↦ (1 : ℝ)) |v| := by
    rcases le_or_gt |v| (Y - ε) with h | h
    · rw [h1 _ (abs_nonneg v) h, indicator_of_mem ((hmem v).2 (by linarith)),
        indicator_of_notMem (fun hh : |v| ∈ Ioc (Y - ε) Y ↦ (not_lt.2 h) hh.1)]
      simp
    · rcases le_or_gt |v| Y with h' | h'
      · rw [indicator_of_mem ((hmem v).2 h'),
          indicator_of_mem (show |v| ∈ Ioc (Y - ε) Y from ⟨h, h'⟩), ← Complex.ofReal_one,
          ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor <;> linarith [(h01 |v|).1, (h01 |v|).2]
      · rw [h0 _ h', indicator_of_notMem (fun hh : v ∈ Icc (-Y) Y ↦ not_le.2 h' ((hmem v).1 hh)),
          indicator_of_notMem (fun hh : |v| ∈ Ioc (Y - ε) Y ↦ not_le.2 h' hh.2)]
        simp
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) hbi
    (ae_of_all _ hle)).trans (le_of_eq ?_)
  rw [integral_comp_abs (f := (Ioc (Y - ε) Y).indicator fun _ ↦ (1 : ℝ)),
    setIntegral_indicator measurableSet_Ioc,
    show Ioi (0 : ℝ) ∩ Ioc (Y - ε) Y = Ioc (Y - ε) Y from
      inter_eq_right.2 fun x hx ↦ lt_of_le_of_lt (by linarith) hx.1,
    setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioc_of_le (by linarith)]
  ring

/-- A spatial profile equal to one on `[0, L - ε]` differs from one on `(0, L]` by at most `ε`
in `L¹`. -/
theorem setIntegral_abs_cutoff_sub_one_le {ρ : ℝ → ℝ} (hρm : Measurable ρ)
    (h01 : ∀ t, 0 ≤ ρ t ∧ ρ t ≤ 1) {L ε : ℝ} (hε : 0 ≤ ε) (hεL : ε ≤ L)
    (h1 : ∀ t, 0 ≤ t → t ≤ L - ε → ρ t = 1) :
    ∫ t in Ioc 0 L, |ρ t - 1| ≤ ε := by
  have hle : ∀ t ∈ Ioc 0 L, |ρ t - 1| ≤ (Ioc (L - ε) L).indicator (fun _ ↦ (1 : ℝ)) t := by
    intro t ht
    by_cases h : t ≤ L - ε
    · rw [h1 t ht.1.le h, sub_self, abs_zero]
      exact indicator_nonneg (fun _ _ ↦ zero_le_one) _
    · rw [indicator_of_mem (show t ∈ Ioc (L - ε) L from ⟨not_le.1 h, ht.2⟩), abs_le]
      constructor <;> linarith [(h01 t).1, (h01 t).2]
  have hc : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ioc 0 L) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  have hi1 : IntegrableOn (fun t ↦ |ρ t - 1|) (Ioc 0 L) :=
    hc.mono' (continuous_abs.measurable.comp (hρm.sub measurable_const)).aestronglyMeasurable
      (ae_of_all _ fun t ↦ by
        rw [Real.norm_eq_abs, abs_abs, abs_le]
        constructor <;> linarith [(h01 t).1, (h01 t).2])
  have hi2 : IntegrableOn ((Ioc (L - ε) L).indicator fun _ ↦ (1 : ℝ)) (Ioc 0 L) :=
    hc.mono' (measurable_const.indicator measurableSet_Ioc).aestronglyMeasurable
      (ae_of_all _ fun t ↦ by
        by_cases ht : t ∈ Ioc (L - ε) L
        · rw [indicator_of_mem ht, norm_one]
        · rw [indicator_of_notMem ht, norm_zero]
          exact zero_le_one)
  refine (setIntegral_mono_on hi1 hi2 measurableSet_Ioc hle).trans (le_of_eq ?_)
  rw [setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.2 (Ioc_subset_Ioc (by linarith) le_rfl), setIntegral_const, smul_eq_mul,
    mul_one, Real.volume_real_Ioc_of_le (by linarith)]
  ring

/-- Paper: (12.4.1.22), p. 518, for `ℚ` with no finite place.
Reconstruction: replacing the cutoffs by the sharp indicators of `(0, L]` and `[-Y, Y]` changes
the orbital mass by at most `2 ε (L + Y) ∫ |ψ(s)| |s| ^ (-3/2) ds`, where `ε` is the width of
the transition of both cutoffs and `ψ` is the lift of the test to the line.
Deviation: (12.4.1.22) prints equality, which fails
(`Printed.sLocalSmoothMass_eq_sharp_real_false`). The bound tends to zero in the regime of
p. 519, `ε L → 0` and `ε Y → 0`. -/
theorem norm_ratSmoothMass_sub_le (f : BruhatCompactSupport Iq) (ξ : Hq) {ρ σ : ℝ → ℝ}
    {L Y ε : ℝ} (hL : 0 < L) (hY : 0 < Y) (hε : 0 ≤ ε) (hεL : ε ≤ L) (hεY : ε ≤ Y)
    (hρm : Measurable ρ) (hρ01 : ∀ t, 0 ≤ ρ t ∧ ρ t ≤ 1)
    (hρ1 : ∀ t, 0 ≤ t → t ≤ L - ε → ρ t = 1)
    (hσm : Measurable σ) (hσ01 : ∀ v, 0 ≤ σ v ∧ σ v ≤ 1)
    (hσ1 : ∀ v, 0 ≤ v → v ≤ Y - ε → σ v = 1) (hσ0 : ∀ v, Y < v → σ v = 0) :
    ‖ratSmoothMass f ξ ρ σ L - sLocalTraceSharpMass f ξ (L * Y)‖ ≤
      2 * ε * (L + Y) * ∫ s, ‖ratProfile f s‖ := by
  obtain ⟨hgi, hgn⟩ := integrable_profile hσm hσ01 hY.le hσ0
  have hχi : Integrable ((Icc (-Y) Y).indicator fun _ ↦ (1 : ℂ)) :=
    (integrableOn_const (hs := measure_Icc_lt_top.ne) (C := (1 : ℂ))).integrable_indicator
      measurableSet_Icc
  set g : ℝ → ℂ := fun v ↦ (σ |v| : ℂ) with hg_def
  set χ : ℝ → ℂ := (Icc (-Y) Y).indicator fun _ ↦ (1 : ℂ) with hχ_def
  set σ₀ := eq ξ.val.val
  set C := ∫ s, ‖ratProfile f s‖ with hC_def
  have hC : 0 ≤ C := integral_nonneg fun _ ↦ norm_nonneg _
  have hI1 : IntegrableOn (fun t ↦ (ρ t : ℂ) * ratPhaseMass f g σ₀ t) (Ioc 0 L) := by
    have h := ((continuous_ratPhaseMass f hgi σ₀).integrableOn_Icc (μ := volume) (a := 0)
      (b := L)).mono_set Ioc_subset_Icc_self
    exact h.bdd_mul (c := 1) (Complex.measurable_ofReal.comp hρm).aestronglyMeasurable
      (ae_of_all _ fun t ↦ by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ01 t).1]
        exact (hρ01 t).2)
  have hI2 : IntegrableOn (fun t ↦ ratPhaseMass f χ σ₀ t) (Ioc 0 L) :=
    ((continuous_ratPhaseMass f hχi σ₀).integrableOn_Icc (μ := volume) (a := 0)
      (b := L)).mono_set Ioc_subset_Icc_self
  rw [ratSmoothMass_eq f ξ ρ σ hgi L, ratSharpMass_eq_phase f ξ hL hY, ← integral_sub hI1 hI2]
  have hbound : ∀ t ∈ Ioc 0 L, ‖(ρ t : ℂ) * ratPhaseMass f g σ₀ t - ratPhaseMass f χ σ₀ t‖ ≤
      |ρ t - 1| * (C * (2 * Y)) + C * (2 * ε) := by
    intro t _
    have hsplit : (ρ t : ℂ) * ratPhaseMass f g σ₀ t - ratPhaseMass f χ σ₀ t =
        ((ρ t - 1 : ℝ) : ℂ) * ratPhaseMass f g σ₀ t + ratPhaseMass f (g - χ) σ₀ t := by
      rw [← ratPhaseMass_sub f hgi hχi]
      push_cast
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((norm_ratPhaseMass_le f g σ₀ t).trans
        (mul_le_mul_of_nonneg_left hgn hC)) (abs_nonneg _)
    · exact (norm_ratPhaseMass_le f (g - χ) σ₀ t).trans (mul_le_mul_of_nonneg_left
        (integral_norm_profile_sub_le hσ01 hε hεY hσ1 hσ0) hC)
  have hc : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ioc 0 L) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  have hi1 : IntegrableOn (fun t ↦ |ρ t - 1|) (Ioc 0 L) :=
    hc.mono' (continuous_abs.measurable.comp (hρm.sub measurable_const)).aestronglyMeasurable
      (ae_of_all _ fun t ↦ by
        rw [Real.norm_eq_abs, abs_abs, abs_le]
        constructor <;> linarith [(hρ01 t).1, (hρ01 t).2])
  have hBi : IntegrableOn (fun t ↦ |ρ t - 1| * (C * (2 * Y)) + C * (2 * ε)) (Ioc 0 L) :=
    (hi1.mul_const _).add (integrableOn_const (μ := volume) (s := Ioc 0 L)
      (C := C * (2 * ε)) (hs := measure_Ioc_lt_top.ne))
  refine (norm_integral_le_of_norm_le hBi
    (ae_restrict_of_forall_mem measurableSet_Ioc hbound)).trans ?_
  rw [integral_add (hi1.mul_const _) (integrableOn_const (μ := volume) (s := Ioc 0 L)
      (C := C * (2 * ε)) (hs := measure_Ioc_lt_top.ne)),
    integral_mul_const, setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hL.le,
    sub_zero]
  have h := setIntegral_abs_cutoff_sub_one_le hρm hρ01 hε hεL hρ1
  have hCY : 0 ≤ C * (2 * Y) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h hCY]

end Comparison

section SmoothedTheorem

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

/-- Paper: Theorem 12.4.1.1, p. 514, with the proof on pp. 516–519, for `ℚ` with no finite
place.
Reconstruction: take spatial cutoffs of radius `L` and frequency cutoffs of radius `Y`, both with
values in `[0, 1]`, equal to one up to `L - ε` and `Y - ε`, the frequency cutoff vanishing beyond
`Y`. Then the summed orbital masses of the smoothed kernel, less `volume₁ φ(1) log (L Y)`, tend to
`volume₁` times the principal value at the real place as `L` and `Y` tend to infinity with
`ε (L + Y) → 0`. This is the regime of p. 519, `ε λ = o(1)` and `ε λ' = o(1)`. The proof compares
each smoothed mass with the sharp one (`norm_ratSmoothMass_sub_le`) and uses
`sLocalTraceSharpMass_asymptotic`.
Deviation: The cutoffs are only assumed measurable, which covers the smooth cutoffs of the paper.
The smoothed masses are integrals over the S-unit fundamental domain, as in (12.4.1.11), and are
not written as the diagonal integral of a kernel on the quotient. -/
theorem ratSmoothTrace_asymptotic (φ : BruhatCompactSupport Cq)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits ℚ Sq) (c : Cq),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iq)
    (hLift : ∀ g : Iq, HasSum (fun ξ : Hq ↦ f.val (ξ.val * g)) (φ.val (classAtq(g))))
    (ρ σ : ℝ × ℝ → ℝ → ℝ) (ε : ℝ × ℝ → ℝ)
    (hρm : ∀ p, Measurable (ρ p)) (hρ01 : ∀ p t, 0 ≤ ρ p t ∧ ρ p t ≤ 1)
    (hρ1 : ∀ p t, 0 ≤ t → t ≤ p.1 - ε p → ρ p t = 1)
    (hσm : ∀ p, Measurable (σ p)) (hσ01 : ∀ p v, 0 ≤ σ p v ∧ σ p v ≤ 1)
    (hσ1 : ∀ p v, 0 ≤ v → v ≤ p.2 - ε p → σ p v = 1) (hσ0 : ∀ p v, p.2 < v → σ p v = 0)
    (hε0 : ∀ p, 0 ≤ ε p) (hε : Tendsto (fun p ↦ ε p * (p.1 + p.2)) (atTop ×ˢ atTop) (𝓝 0)) :
    ∃ (a : archTest) (b : finiteTest),
      (∀ (w : InfinitePlace ℚ) (u : w.Completionˣ), (a w).val u = φ.val (archClass(w) u)) ∧
      (∀ (v : Sq) (u : (v.val.adicCompletion ℚ)ˣ),
        (b v).val u = φ.val (finiteClass(v.val) u)) ∧
      Tendsto (fun p : ℝ × ℝ ↦ (∑' ξ : Hq, ratSmoothMass f ξ (ρ p) (σ p) p.1) -
          (volume₁ : ℂ) * φ.val 1 * (Real.log (p.1 * p.2) : ℂ))
        (atTop ×ˢ atTop) (𝓝 ((volume₁ : ℂ) * principalValues(a, b))) := by
  obtain ⟨a, b, M, ha, hb, hsum, hlim⟩ := sLocalTraceSharpMass_asymptotic (F := ℚ) (S := Sq) φ
    ratPic_subsingleton ratRamified hOutside f hLift
  refine ⟨a, b, ha, hb, ?_⟩
  have hp : Tendsto (fun p : ℝ × ℝ ↦ p.1 * p.2) (atTop ×ˢ atTop) atTop :=
    tendsto_fst.atTop_mul_atTop₀ tendsto_snd
  set C := ∫ s, ‖ratProfile f s‖
  have hD : Tendsto (fun p : ℝ × ℝ ↦ (∑' ξ : Hq, ratSmoothMass f ξ (ρ p) (σ p) p.1) -
      M (p.1 * p.2)) (atTop ×ˢ atTop) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hε.mul_const (4 * C))
    filter_upwards [tendsto_fst.eventually (eventually_ge_atTop (1 : ℝ)),
      tendsto_snd.eventually (eventually_ge_atTop (1 : ℝ)), hp.eventually hsum,
      hε.eventually (gt_mem_nhds (zero_lt_one' ℝ))] with p h1 h2 hs hεp
    have hεs : ε p ≤ ε p * (p.1 + p.2) := le_mul_of_one_le_right (hε0 p) (by linarith)
    have hεL : ε p ≤ p.1 := by linarith
    have hεY : ε p ≤ p.2 := by linarith
    have hb (ξ : Hq) := norm_ratSmoothMass_sub_le f ξ (by linarith) (by linarith) (hε0 p) hεL hεY
      (hρm p) (hρ01 p) (hρ1 p) (hσm p) (hσ01 p) (hσ1 p) (hσ0 p)
    rw [← hs.tsum_eq, tsum_ratProjectedDiagonal, tsum_ratProjectedDiagonal]
    calc ‖ratSmoothMass f 1 (ρ p) (σ p) p.1 + ratSmoothMass f ratMinusOne (ρ p) (σ p) p.1 -
          (sLocalTraceSharpMass f 1 (p.1 * p.2) +
            sLocalTraceSharpMass f ratMinusOne (p.1 * p.2))‖
        = ‖(ratSmoothMass f 1 (ρ p) (σ p) p.1 - sLocalTraceSharpMass f 1 (p.1 * p.2)) +
          (ratSmoothMass f ratMinusOne (ρ p) (σ p) p.1 -
            sLocalTraceSharpMass f ratMinusOne (p.1 * p.2))‖ := by ring_nf
      _ ≤ 2 * ε p * (p.1 + p.2) * C + 2 * ε p * (p.1 + p.2) * C :=
          (norm_add_le _ _).trans (add_le_add (hb 1) (hb ratMinusOne))
      _ = ε p * (p.1 + p.2) * (4 * C) := by ring
  have h := hD.add (hlim.comp hp)
  rw [zero_add] at h
  refine h.congr fun p ↦ ?_
  simp only [Function.comp_apply]
  ring

end SmoothedTheorem

end RiemannMasullo.Isolated
