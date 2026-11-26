module

public import RiemannMasullo.AppA_AlgebraicNT.Sec2b
public import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Covering.OneDim
import Mathlib.MeasureTheory.Measure.Haar.Extension
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated
import Mathlib.Topology.Covering.Quotient
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Integral
import RiemannMasullo.ForMathlib.Topology.Algebra.OpenSubgroup

/-!
# Maximal averages on the real line and D-sequences

Masullo, §§A.5.1–A.5.2, pp. 566–578.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal Pointwise

namespace RiemannMasullo

/-- Paper: (A.5.1.1), p. 566. Centered averages of a continuous real-valued function
converge to its value as the radius decreases to zero. -/
theorem tendsto_centeredAverage_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    Tendsto (fun r : ℝ ↦ (2 * r)⁻¹ * ∫ y in x - r..x + r, f y)
      (𝓝[>] 0) (𝓝 (f x)) := by
  have hradius : Tendsto (fun r : ℝ ↦ r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id'.2 nhdsWithin_le_nhds
  have hleft : Tendsto (fun r : ℝ ↦ x - r) (𝓝[>] 0) (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).sub hradius
  have hright : Tendsto (fun r : ℝ ↦ x + r) (𝓝[>] 0) (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).add hradius
  have herror := intervalIntegral.integral_sub_linear_isLittleO_of_tendsto_ae
    (l' := 𝓝 x) hf.aestronglyMeasurable.stronglyMeasurableAtFilter
    (hf.continuousAt.tendsto.mono_left inf_le_left) hleft hright
  have hlength (r : ℝ) : x + r - (x - r) = 2 * r := by ring
  have hquot :
      Tendsto (fun r : ℝ ↦ ((∫ y in x - r..x + r, f y) - (2 * r) * f x) / (2 * r))
        (𝓝[>] 0) (𝓝 0) := by
    simpa only [Pi.sub_apply, hlength, smul_eq_mul] using herror.tendsto_div_nhds_zero
  have hlim := hquot.add (tendsto_const_nhds (x := f x))
  rw [zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with r hr
  have hne : 2 * r ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt (mem_Ioi.mp hr))
  rw [sub_div, mul_comm (2 * r) (f x), mul_div_cancel_right₀ _ hne, sub_add_cancel,
    div_eq_mul_inv, mul_comm]

/-- Paper: (A.5.1.2), p. 566. The centered maximal function takes the supremum of
the averages of the absolute value over intervals of all positive radii.
Deviation: The supremum over all radii expresses the intended operator behind the printed
“lim sup”. Extended nonnegative integrals also define the formula on locally integrable inputs. -/
def realCenteredMaximal (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ r : Ioi (0 : ℝ), (ENNReal.ofReal (2 * (r : ℝ)))⁻¹ *
    ∫⁻ y in Ioc (x - (r : ℝ)) (x + (r : ℝ)), ‖f y‖ₑ

/-- Paper: (A.5.1.2), p. 566. The centered maximal function of a constant
is its absolute value at every point. -/
theorem realCenteredMaximal_const (c : ℂ) (x : ℝ) :
    realCenteredMaximal (fun _ ↦ c) x = ‖c‖ₑ := by
  -- Each average of the constant `‖c‖ₑ` over an interval of length `2r` is `‖c‖ₑ`.
  have h : ∀ r : Ioi (0 : ℝ), (ENNReal.ofReal (2 * (r : ℝ)))⁻¹ *
      ∫⁻ _ in Ioc (x - (r : ℝ)) (x + (r : ℝ)), ‖c‖ₑ = ‖c‖ₑ := by
    rintro ⟨r, hr⟩
    have hr' : (0 : ℝ) < r := hr
    rw [setLIntegral_const, Real.volume_Ioc, show x + r - (x - r) = 2 * r by ring,
      mul_comm, mul_assoc, ENNReal.mul_inv_cancel (by simp [hr']) ENNReal.ofReal_ne_top, mul_one]
  simp only [realCenteredMaximal, h, ciSup_const]

-- TODO(paper-gap): In Theorem A.5.1.1(1), the all-radii maximal function need not be finite
-- anywhere. For f(x) = |x| both local hypotheses hold and the averages grow without bound.

/-- Paper: Proof of Theorem A.5.1.1(1), p. 566. Local integrability makes each
fixed-radius average continuous and hence the centered maximal function measurable. -/
private theorem realCenteredMaximal_measurable_of_locallyIntegrable {f : ℝ → ℂ}
    (hlocal : LocallyIntegrable f volume) :
    Measurable (realCenteredMaximal f) := by
  have hint (a b : ℝ) : IntervalIntegrable (fun y ↦ ‖f y‖) volume a b :=
    (IntegrableOn.intervalIntegrable
      (hlocal.integrableOn_isCompact (k := uIcc a b) isCompact_uIcc)).norm
  have hprimitive := intervalIntegral.continuous_primitive hint 0
  apply LowerSemicontinuous.measurable
  unfold realCenteredMaximal
  apply lowerSemicontinuous_iSup
  intro r
  apply Continuous.lowerSemicontinuous
  have hr : 0 < (r : ℝ) := r.property
  have havg : Continuous (fun x : ℝ ↦ ∫ y in x - (r : ℝ)..x + (r : ℝ), ‖f y‖) := by
    have hright : Continuous (fun x : ℝ ↦ x + (r : ℝ)) := continuous_id.add continuous_const
    have hleft : Continuous (fun x : ℝ ↦ x - (r : ℝ)) := continuous_id.sub continuous_const
    convert (hprimitive.comp hright).sub (hprimitive.comp hleft) using 1
    ext x
    exact (intervalIntegral.integral_interval_sub_left (hint 0 _) (hint 0 _)).symm
  have hlintegral (x : ℝ) :
      (∫⁻ y in Ioc (x - (r : ℝ)) (x + (r : ℝ)), ‖f y‖ₑ) =
        ENNReal.ofReal (∫ y in x - (r : ℝ)..x + (r : ℝ), ‖f y‖) := by
    have hab : x - (r : ℝ) ≤ x + (r : ℝ) := by linarith
    rw [intervalIntegral.integral_of_le hab,
      ofReal_integral_eq_lintegral_ofReal (hint _ _).1 (Eventually.of_forall fun y ↦ norm_nonneg _)]
    simp only [ofReal_norm]
  simp only [hlintegral]
  exact (ENNReal.continuous_const_mul (by simp [hr])).comp (ENNReal.continuous_ofReal.comp havg)

set_option linter.unusedVariables false in
/-- Paper: Theorem A.5.1.1(1), p. 566. Under the two local integrability hypotheses,
the centered maximal function is measurable. Input measurability is for completed
Lebesgue measure.
Deviation: The separate almost-everywhere finiteness claim fails for the all-radii operator. -/
theorem realCenteredMaximal_measurable {f : ℝ → ℂ} (hf : AEMeasurable f volume)
    (hlocal : LocallyIntegrable f volume)
    (hlog : LocallyIntegrable (fun x ↦ (max (Real.log ‖f x‖) 0 : ℝ) • f x) volume) :
    Measurable (realCenteredMaximal f) :=
  realCenteredMaximal_measurable_of_locallyIntegrable hlocal

/-- Paper: Theorem A.5.1.1(2), p. 566. The level set of the centered maximal function
has measure at most three times the L¹ norm divided by the positive level. -/
theorem realCenteredMaximal_weak_one {f : ℝ → ℂ} (hf : AEMeasurable f volume)
    (h₁ : Integrable f volume) {a : ℝ} (ha : 0 < a) :
    volume {x | ENNReal.ofReal a < realCenteredMaximal f x} ≤
      ENNReal.ofReal (3 / a) * eLpNorm f 1 volume := by
  classical
  let ν := (volume : Measure ℝ).withDensity (fun x ↦ ‖f x‖ₑ)
  have hnorm : ν univ = eLpNorm f 1 volume := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      eLpNorm_one_eq_lintegral_eNorm hf.aestronglyMeasurable]
  have htotal : ν univ ≠ ∞ :=
    hnorm ▸ (memLp_one_iff_integrable.mpr h₁).eLpNorm_lt_top.ne
  let interval (p : ℝ × ℝ) := Ioc (p.1 - p.2) (p.1 + p.2)
  let enlarged (p : ℝ × ℝ) := Icc (p.1 - 3 * p.2) (p.1 + 3 * p.2)
  let good : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ ENNReal.ofReal (a * (2 * p.2)) < ν (interval p)}
  have hbounded (p : ℝ × ℝ) (hp : p ∈ good) : p.2 ≤ (ν univ).toReal / a := by
    have hpos := hp.1
    have hle := ENNReal.toReal_mono htotal (hp.2.le.trans (measure_mono (subset_univ _)))
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ a * (2 * p.2))] at hle
    rw [le_div_iff₀ ha]
    nlinarith [mul_nonneg ha.le hpos.le]
  obtain ⟨u, hug, hdisjoint, hintersects⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement interval good Prod.snd 2
      one_lt_two (fun p hp ↦ hp.1.le) ((ν univ).toReal / a) hbounded
      (fun p hp ↦ ⟨p.1, by
        change p.1 - p.2 < p.1 ∧ p.1 ≤ p.1 + p.2
        have := hp.1
        constructor <;> linarith⟩)
  have : Countable u := hdisjoint.countable_of_nonempty_interior (fun p hp ↦ by
    dsimp only [interval]
    rw [interior_Ioc]
    exact nonempty_Ioo.mpr (by linarith [(hug hp).1]))
  -- Only the centers need to be covered by the triple dilations.
  have hcover : {x | ENNReal.ofReal a < realCenteredMaximal f x} ⊆
      ⋃ p : u, enlarged p.val := by
    intro x hx
    obtain ⟨r, hr⟩ := lt_iSup_iff.mp (show ENNReal.ofReal a < realCenteredMaximal f x from hx)
    have hgood : (x, (r : ℝ)) ∈ good := by
      refine ⟨r.property, ?_⟩
      dsimp only [ν, interval, Prod.fst, Prod.snd]
      rw [withDensity_apply _ measurableSet_Ioc, ENNReal.ofReal_mul ha.le]
      exact ENNReal.mul_lt_of_lt_div (by rwa [ENNReal.div_eq_inv_mul])
    obtain ⟨p, hp, ⟨y, hy₁, hy₂⟩, hrad⟩ := hintersects (x, (r : ℝ)) hgood
    apply mem_iUnion.mpr
    refine ⟨⟨p, hp⟩, ?_⟩
    change x - (r : ℝ) < y ∧ y ≤ x + (r : ℝ) at hy₁
    change p.1 - p.2 < y ∧ y ≤ p.1 + p.2 at hy₂
    change (r : ℝ) ≤ 2 * p.2 at hrad
    change p.1 - 3 * p.2 ≤ x ∧ x ≤ p.1 + 3 * p.2
    constructor <;> linarith [hy₁.1, hy₁.2, hy₂.1, hy₂.2]
  have henlarged (p : u) : volume (enlarged p.val) ≤ ENNReal.ofReal (3 / a) * ν (interval p.val) := by
    have hlength : p.val.1 + 3 * p.val.2 - (p.val.1 - 3 * p.val.2) =
        (3 / a) * (a * (2 * p.val.2)) := by
      rw [← mul_assoc, div_mul_cancel₀ _ ha.ne']
      ring
    dsimp only [enlarged]
    rw [Real.volume_Icc, hlength, ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact (hug p.property).2.le
  have hsum : (∑' p : u, ν (interval p.val)) ≤ ν univ := by
    rw [← measure_iUnion (hdisjoint.on_injective Subtype.val_injective Subtype.property)
      (fun _ ↦ measurableSet_Ioc)]
    exact measure_mono (subset_univ _)
  calc
    _ ≤ volume (⋃ p : u, enlarged p.val) := measure_mono hcover
    _ ≤ ∑' p : u, volume (enlarged p.val) := measure_iUnion_le _
    _ ≤ ∑' p : u, ENNReal.ofReal (3 / a) * ν (interval p.val) := tsum_le_tsum henlarged
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_left, ← hnorm]
      gcongr

/-- Paper: (A.5.1.8), p. 567. Truncating the input below a positive level bounds the
measure of the maximal function's level set at twice that level by a weighted tail integral. -/
private theorem realCenteredMaximal_tail {f : ℝ → ℂ} (hf : AEMeasurable f volume)
    {p : ℝ} (hp : 1 < p) (hLp : MemLp f (ENNReal.ofReal p) volume) {t : ℝ} (ht : 0 < t) :
    volume {x | ENNReal.ofReal (2 * t) < realCenteredMaximal f x} ≤
      ENNReal.ofReal (3 / t) * ∫⁻ x in {x | ENNReal.ofReal t < ‖f x‖ₑ}, ‖f x‖ₑ := by
  classical
  let s : Set ℝ := {x | ENNReal.ofReal t < ‖f x‖ₑ}
  let g := s.indicator f
  have hs : NullMeasurableSet s volume :=
    nullMeasurableSet_lt aemeasurable_const hf.eNorm
  have ht₀ : ENNReal.ofReal t ≠ 0 := by simp [ht]
  have hsFin : volume s ≠ ∞ := by
    apply (measure_mono (fun x (hx : x ∈ s) ↦ (show ENNReal.ofReal t < ‖f x‖ₑ from hx).le)).trans_lt
      (hLp.meas_ge_lt_top'_eNorm (by positivity) ENNReal.ofReal_ne_top ht₀ (by simp)) |>.ne
  have hp₁ : 1 ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp.le
  have hgLp : MemLp g (ENNReal.ofReal p) volume :=
    (memLp_indicator_iff_restrict hs).2 (hLp.restrict s)
  have hg : Integrable g volume := memLp_one_iff_integrable.mp
    (hgLp.mono_exponent_of_measure_support_ne_top (fun x hx ↦ indicator_of_notMem hx f) hsFin hp₁)
  have hnorm (y : ℝ) : ‖f y‖ₑ ≤ ‖g y‖ₑ + ENNReal.ofReal t := by
    by_cases hy : y ∈ s
    · simp [g, hy]
    · simpa [g, hy] using le_of_not_gt (show ¬ ENNReal.ofReal t < ‖f y‖ₑ from hy)
  have hmax (x : ℝ) : realCenteredMaximal f x ≤ realCenteredMaximal g x + ENNReal.ofReal t := by
    unfold realCenteredMaximal
    refine iSup_le fun r ↦ ?_
    let I := Ioc (x - (r : ℝ)) (x + (r : ℝ))
    let len := ENNReal.ofReal (2 * (r : ℝ))
    have hr : 0 < (r : ℝ) := r.property
    have hlen : volume I = len := by
      dsimp only [I, len]
      rw [Real.volume_Ioc, show x + (r : ℝ) - (x - (r : ℝ)) = 2 * r by ring]
    change len⁻¹ * (∫⁻ y in I, ‖f y‖ₑ) ≤ _
    calc
      _ ≤ len⁻¹ * (∫⁻ y in I, ‖g y‖ₑ + ENNReal.ofReal t) := by
        gcongr
        exact hnorm _
      _ = len⁻¹ * (∫⁻ y in I, ‖g y‖ₑ) + ENNReal.ofReal t := by
        rw [lintegral_add_left' hg.aestronglyMeasurable.eNorm.restrict,
          setLIntegral_const, hlen, mul_add, mul_left_comm len⁻¹,
          ENNReal.inv_mul_cancel (by simp [hr]) ENNReal.ofReal_ne_top, mul_one]
      _ ≤ _ := by
        gcongr
        exact le_iSup (fun r : Ioi (0 : ℝ) ↦ (ENNReal.ofReal (2 * (r : ℝ)))⁻¹ *
          ∫⁻ y in Ioc (x - (r : ℝ)) (x + (r : ℝ)), ‖g y‖ₑ) r
  have hsubset : {x | ENNReal.ofReal (2 * t) < realCenteredMaximal f x} ⊆
      {x | ENNReal.ofReal t < realCenteredMaximal g x} := by
    intro x hx
    change ENNReal.ofReal (2 * t) < realCenteredMaximal f x at hx
    rw [two_mul, ENNReal.ofReal_add ht.le ht.le] at hx
    exact lt_of_not_ge fun h ↦
      (hx.trans_le ((hmax x).trans (add_le_add_left h (ENNReal.ofReal t)))).false
  refine (measure_mono hsubset).trans ?_
  have hweak := realCenteredMaximal_weak_one hg.aestronglyMeasurable.aemeasurable hg ht
  rwa [eLpNorm_one_eq_lintegral_eNorm hg.aestronglyMeasurable, show g = s.indicator f from rfl,
    (show (fun x ↦ ‖s.indicator f x‖ₑ) = s.indicator (fun x ↦ ‖f x‖ₑ) by
      funext x
      exact eNorm_indicator_eq_indicator_eNorm f x), lintegral_indicator₀ hs] at hweak

/-- Paper: Theorem A.5.1.1(3), p. 566. For a finite exponent p greater than one,
the p-th moment of the centered maximal function has the displayed strong-type bound. -/
theorem realCenteredMaximal_strong {f : ℝ → ℂ} (hf : AEMeasurable f volume) {p : ℝ}
    (hp : 1 < p) (hLp : MemLp f (ENNReal.ofReal p) volume) :
    (∫⁻ x, realCenteredMaximal f x ^ p) ≤
      ENNReal.ofReal ((2 : ℝ) ^ p * 3 * p / (p - 1)) * ∫⁻ x, ‖f x‖ₑ ^ p := by
  have hp₀ : 0 < p := by positivity
  have hp₁ : 0 < p - 1 := sub_pos.mpr hp
  have hloc := hLp.locallyIntegrable (by simpa using ENNReal.ofReal_le_ofReal hp.le)
  let M (x : ℝ) := realCenteredMaximal f x / 2
  have hM : Measurable M :=
    (realCenteredMaximal_measurable_of_locallyIntegrable hloc).div_const 2
  -- Layer cake for this weighted measure accounts for the factor ‖f x‖ₑ in the tail.
  let ν := (volume : Measure ℝ).withDensity (fun x ↦ ‖f x‖ₑ)
  have htail (t : ℝ) (ht : 0 < t) :
      volume {x | ENNReal.ofReal t < M x} ≤
        ENNReal.ofReal (3 / t) * ν {x | ENNReal.ofReal t < ‖f x‖ₑ} := by
    have hlevel : {x | ENNReal.ofReal t < M x} =
        {x | ENNReal.ofReal (2 * t) < realCenteredMaximal f x} := by
      ext x
      simp only [mem_ofPred_eq, M, ENNReal.lt_div_iff_mul_lt (Or.inl two_ne_zero)
        (Or.inl ENNReal.ofNat_ne_top), two_mul, ENNReal.ofReal_add ht.le ht.le, mul_two]
    rw [hlevel, withDensity_apply']
    exact realCenteredMaximal_tail hf hp hLp ht
  have hweighted :
      ENNReal.ofReal (p - 1) * (∫⁻ t in Ioi (0 : ℝ), ν {x | ENNReal.ofReal t < ‖f x‖ₑ} *
        ENNReal.ofReal (t ^ (p - 2))) = ∫⁻ x, ‖f x‖ₑ ^ p := by
    have hfNorm := hf.eNorm
    have h := lintegral_ennreal_rpow_eq_lintegral_meas_lt_mul ν
      (hfNorm.mono_ac (withDensity_absolutelyContinuous _ _)) hp₁
    rw [show p - 1 - 1 = p - 2 by ring] at h
    rw [← h, lintegral_withDensity_eq_lintegral_mul₀ hfNorm (hfNorm.pow_const _)]
    refine lintegral_congr fun x ↦ ?_
    calc
      _ = ‖f x‖ₑ ^ (1 : ℝ) * ‖f x‖ₑ ^ (p - 1) := by
        rw [Pi.mul_apply, ENNReal.rpow_one]
      _ = _ := by
        rw [← ENNReal.rpow_add_of_nonneg 1 (p - 1) zero_le_one hp₁.le,
          show 1 + (p - 1) = p by ring]
  have hrescale (x : ℝ) : realCenteredMaximal f x ^ p =
      ENNReal.ofReal ((2 : ℝ) ^ p) * M x ^ p := by
    have h : 2 * M x = realCenteredMaximal f x := by
      rw [mul_comm]
      exact ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
    calc
      _ = (2 * M x) ^ p := by rw [h]
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp₀.le,
          ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hp₀.le,
          ENNReal.ofReal_ofNat]
  simp_rw [hrescale]
  rw [lintegral_const_mul _ (hM.pow_const p),
    lintegral_ennreal_rpow_eq_lintegral_meas_lt_mul volume hM.aemeasurable hp₀, ← mul_assoc]
  calc
    _ ≤ (ENNReal.ofReal ((2 : ℝ) ^ p) * ENNReal.ofReal p) *
        (3 * ∫⁻ t in Ioi (0 : ℝ), ν {x | ENNReal.ofReal t < ‖f x‖ₑ} *
          ENNReal.ofReal (t ^ (p - 2))) := by
      gcongr
      rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
      have ht' : 0 < t := ht
      have hweight : ENNReal.ofReal (3 / t) * ENNReal.ofReal (t ^ (p - 1)) =
          (3 : ℝ≥0∞) * ENNReal.ofReal (t ^ (p - 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 3 / t), ← ENNReal.ofReal_ofNat,
          ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (3 : ℝ))]
        congr 1
        rw [show t ^ (p - 2) = t ^ (p - 1) / t by
          rw [show p - 2 = p - 1 - 1 by ring, Real.rpow_sub ht', Real.rpow_one]]
        ring
      calc
        _ ≤ (ENNReal.ofReal (3 / t) * ν {x | ENNReal.ofReal t < ‖f x‖ₑ}) *
            ENNReal.ofReal (t ^ (p - 1)) := by gcongr; exact htail t ht'
        _ = _ := by rw [mul_right_comm, hweight, mul_right_comm, mul_assoc]
    _ = _ := by
      have h := congrArg (fun a ↦ (ENNReal.ofReal (p - 1))⁻¹ * a) hweighted
      rw [ENNReal.inv_mul_cancel_left (ENNReal.ofReal_ne_zero_iff.mpr hp₁)
        ENNReal.ofReal_ne_top] at h
      rw [h, show (2 : ℝ) ^ p * 3 * p / (p - 1) =
        ((2 : ℝ) ^ p * p) * (3 * (p - 1)⁻¹) by ring,
        ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ p * p),
        ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ p),
        ENNReal.ofReal_mul (by norm_num : 0 ≤ (3 : ℝ)), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_inv_of_pos hp₁]
      simp only [mul_assoc]

/-- Paper: Theorem A.5.1.3, p. 568. Centered averages of a locally integrable
function converge to its value at almost every point of the real line. -/
theorem ae_tendsto_centeredAverage {f : ℝ → ℂ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun r : ℝ ↦ ((2 * r)⁻¹ : ℝ) • ∫ y in x - r..x + r, f y)
        (𝓝[>] 0) (𝓝 (f x)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume hf 1] with x hx
  have h := hx (fun _ : ℝ ↦ x) id tendsto_id (by
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with r hr
    have hr' : 0 < r := hr
    simp [Metric.mem_closedBall, hr'.le])
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with r hr
  have hr' : 0 < r := hr
  have hab : x - r ≤ x + r := by linarith
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  simp only [id_eq]
  rw [average_eq, measureReal_def, Measure.restrict_apply_univ, Real.volume_closedBall,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * r), Real.closedBall_eq_Icc]

section DSequences

variable {G : Type*} [CommGroup G] [MeasurableSpace G]

/-- Paper: Definition A.5.2.1, p. 569. A D-sequence consists of decreasing Haar-measurable
sets containing the identity, of positive finite measure, with a uniform strict bound
for the measure of each set multiplied by its inverse. -/
def IsDSequence (μ : Measure G) (U : ℕ → Set G) : Prop :=
  (∀ k, 1 ∈ U k ∧ NullMeasurableSet (U k) μ ∧ 0 < μ (U k) ∧ μ (U k) < ∞) ∧
    Antitone U ∧
    ∃ C : ℝ, 0 < C ∧ ∀ k, 0 < μ (U k * (U k)⁻¹) ∧
      μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k)

variable [TopologicalSpace G]

/-- Paper: Definition A.5.2.1, p. 569. A D′-sequence is a D-sequence whose
members are cofinal in the neighborhoods of the identity. -/
def IsDPrimeSequence (μ : Measure G) (U : ℕ → Set G) : Prop :=
  IsDSequence μ U ∧ ∀ W ∈ 𝓝 (1 : G), ∃ k, U k ⊆ W

/-- Paper: Remark A.5.2.2, p. 569. A D″-sequence is a D′-sequence with a specified
family of Haar-measurable sets whose difference sets fit inside the corresponding members.
Their measures control those of the original sets by one positive constant. -/
def IsDDoublePrimeSequence (μ : Measure G) (U V : ℕ → Set G) : Prop :=
  IsDPrimeSequence μ U ∧
    ∃ C : ℝ, 0 < C ∧ ∀ k, NullMeasurableSet (V k) μ ∧ V k * (V k)⁻¹ ⊆ U k ∧
      μ (U k) ≤ ENNReal.ofReal C * μ (V k)

end DSequences

section TopologicalGroups

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G)

/-- Paper: Proposition A.5.2.3(1), p. 570. A first-countable locally profinite
group has a D″-sequence of compact open subgroups. Each auxiliary set is the
pointwise square of the corresponding subgroup, and the mass comparison has constant one.
Deviation: Local profiniteness is expressed by total disconnectedness together with
the ambient Hausdorff local compactness. The stated comparison constant one is for
the D″ condition. The proof's choice of doubling constant one violates strictness. -/
theorem exists_isDDoublePrimeSequence_of_totallyDisconnected [FirstCountableTopology G]
    [TotallyDisconnectedSpace G] [μ.IsHaarMeasure] :
    ∃ K : ℕ → OpenSubgroup G,
      let U : ℕ → Set G := fun k ↦ (K k : Set G)
      let V : ℕ → Set G := fun k ↦ U k * U k
      IsDDoublePrimeSequence μ U V ∧ ∀ k, IsCompact (U k) ∧ μ (U k) ≤ μ (V k) := by
  have hbasis : (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G))
      (fun H ↦ (H : Set G)) := by
    refine ⟨fun W ↦ ⟨exists_compact_openSubgroup_sub_mem_nhds, ?_⟩⟩
    rintro ⟨H, _, hHW⟩
    exact mem_of_superset H.mem_nhds_one hHW
  obtain ⟨K, hcompact, hK⟩ := hbasis.exists_antitone_subbasis
  let U : ℕ → Set G := fun k ↦ (K k : Set G)
  have hmul (k : ℕ) : U k * U k = U k := (K k).toSubgroup.toSubmonoid.coe_mul_self_eq
  have hdiff (k : ℕ) : U k * (U k)⁻¹ = U k := by
    rw [show (U k)⁻¹ = U k from inv_coe_set, hmul]
  have hmeas (k : ℕ) : NullMeasurableSet (U k) μ :=
    (K k).isOpen.measurableSet.nullMeasurableSet
  have hpos (k : ℕ) : 0 < μ (U k) := (K k).isOpen.measure_pos μ ⟨1, (K k).one_mem⟩
  have hfin (k : ℕ) : μ (U k) < ∞ := (hcompact k).measure_lt_top
  have hD : IsDSequence μ U := by
    refine ⟨fun k ↦ ⟨(K k).one_mem, hmeas k, hpos k, hfin k⟩,
      hK.antitone, 2, two_pos, fun k ↦ ?_⟩
    rw [hdiff, ENNReal.ofReal_ofNat, two_mul]
    exact ⟨hpos k, ENNReal.lt_add_right (hfin k).ne (hpos k).ne'⟩
  refine ⟨K, ⟨⟨hD, fun _ hW ↦ hK.mem_iff.mp hW⟩, 1, one_pos, fun k ↦ ?_⟩, fun k ↦ ?_⟩
  · change NullMeasurableSet (U k * U k) μ ∧
      (U k * U k) * (U k * U k)⁻¹ ⊆ U k ∧
      μ (U k) ≤ ENNReal.ofReal 1 * μ (U k * U k)
    simp only [hmul, hdiff, ENNReal.ofReal_one, one_mul]
    exact ⟨hmeas k, Subset.rfl, le_rfl⟩
  · change IsCompact (U k) ∧ μ (U k) ≤ μ (U k * U k)
    rw [hmul]
    exact ⟨hcompact k, le_rfl⟩

variable (H : OpenSubgroup G) (U : ℕ → Set H)

local notation "inclusion" => (fun x : H ↦ (x : G))

/-- Paper: Proposition A.5.2.3(2), p. 570. A sequence in an open subgroup is a
D-sequence for the restricted Haar measure exactly when its images form one in the group. -/
theorem isDSequence_openSubgroup_iff [μ.IsHaarMeasure] :
    IsDSequence (μ.comap inclusion) U ↔ IsDSequence μ (fun k ↦ inclusion '' U k) := by
  have hH : MeasurableSet (H : Set G) := H.isOpen.measurableSet
  have hemb : MeasurableEmbedding inclusion := MeasurableEmbedding.subtype_coe hH
  have hmeas (s : Set H) : μ.comap inclusion s = μ (inclusion '' s) := hemb.comap_apply μ s
  have hnull (s : Set H) :
      NullMeasurableSet s (μ.comap inclusion) ↔ NullMeasurableSet (inclusion '' s) μ := by
    refine ⟨fun hs ↦ Measure.NullMeasurableSet.subtype_coe (s := (H : Set G)) hH.nullMeasurableSet hs,
      fun hs ↦ ?_⟩
    have hqmp : QuasiMeasurePreserving inclusion (μ.comap inclusion) μ :=
      ⟨measurable_subtype_coe.aemeasurable, by
        rw [hemb.map_comap]
        exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self⟩
    simpa only [Set.preimage_image_eq _ Subtype.val_injective] using hs.preimage hqmp
  have hone (s : Set H) : (1 : H) ∈ s ↔ (1 : G) ∈ inclusion '' s :=
    (Subtype.val_injective.mem_set_image (a := (1 : H))).symm
  have hdiff (s : Set H) :
      inclusion '' (s * s⁻¹) = inclusion '' s * (inclusion '' s)⁻¹ := by
    have h := Set.image_mul (m := (H : Subgroup G).subtype) (s := s) (t := s⁻¹)
    rw [Set.image_inv] at h
    exact h
  have hanti : Antitone U ↔ Antitone (fun k ↦ inclusion '' U k) := by
    simp only [Antitone, Set.image_subset_image_iff Subtype.val_injective]
  unfold IsDSequence
  simp only [hmeas, hnull, hone, hdiff, hanti]

/-- Paper: Proposition A.5.2.3(2), p. 570. The D′ condition transfers in both
directions under the inclusion of an open subgroup, with the restricted Haar measure. -/
theorem isDPrimeSequence_openSubgroup_iff [μ.IsHaarMeasure] :
    IsDPrimeSequence (μ.comap inclusion) U ↔
      IsDPrimeSequence μ (fun k ↦ inclusion '' U k) := by
  have hemb : IsOpenEmbedding inclusion := H.isOpen.isOpenEmbedding_subtypeVal
  refine and_congr (isDSequence_openSubgroup_iff μ H U) ⟨fun h W hW ↦ ?_, fun h W hW ↦ ?_⟩
  · obtain ⟨k, hk⟩ := h _ (continuous_subtype_val.continuousAt.preimage_mem_nhds hW)
    exact ⟨k, Set.image_subset_iff.mpr hk⟩
  · obtain ⟨k, hk⟩ := h _ (hemb.image_mem_nhds.mpr hW)
    exact ⟨k, (Set.image_subset_image_iff Subtype.val_injective).mp hk⟩

/-- Paper: Proposition A.5.2.3(2), p. 570. Openness agrees in the open subgroup
and in the ambient group. -/
theorem isOpen_sequence_openSubgroup_iff :
    (∀ k, IsOpen (U k)) ↔ ∀ k, IsOpen (inclusion '' U k) :=
  forall_congr' fun _ ↦ H.isOpen.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen

/-- Paper: Proposition A.5.2.3(2), p. 570. Inversion symmetry agrees in the open
subgroup and in the ambient group. -/
theorem inv_eq_sequence_openSubgroup_iff :
    (∀ k, (U k)⁻¹ = U k) ↔ ∀ k, (inclusion '' U k)⁻¹ = inclusion '' U k := by
  have key (s : Set H) : (inclusion '' s)⁻¹ = inclusion '' s⁻¹ := by
    ext x
    simp only [Set.mem_inv, Set.mem_image]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y⁻¹, by simpa using hy, by simp [hyx]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y⁻¹, hy, by simp⟩
  exact forall_congr' fun k ↦ by rw [key, Subtype.val_injective.image_injective.eq_iff]

/-- Paper: Remark A.5.2.4, p. 570. The constant singleton of the identity
is an open, symmetric D-sequence on a countable discrete abelian group. -/
theorem isDSequence_singleton_one [Countable G] [DiscreteTopology G] [μ.IsHaarMeasure] :
    IsDSequence μ (fun _ ↦ ({1} : Set G)) := by
  have hpos : 0 < μ ({1} : Set G) := (isOpen_discrete _).measure_pos μ (singleton_nonempty 1)
  have hfin : μ ({1} : Set G) < ∞ := isCompact_singleton.measure_lt_top
  refine ⟨fun _ ↦ ⟨rfl, (measurableSet_singleton 1).nullMeasurableSet, hpos, hfin⟩,
    antitone_const, 2, two_pos, fun _ ↦ ?_⟩
  simp only [inv_singleton, inv_one, singleton_mul_singleton, mul_one]
  refine ⟨hpos, ?_⟩
  rw [ENNReal.ofReal_ofNat, two_mul]
  exact ENNReal.lt_add_right hfin.ne hpos.ne'

/-- Paper: Remark A.5.2.4, p. 570. The constant singleton of the identity
forms a D′-sequence on a countable discrete abelian group. -/
theorem isDPrimeSequence_singleton_one [Countable G] [DiscreteTopology G] [μ.IsHaarMeasure] :
    IsDPrimeSequence μ (fun _ ↦ ({1} : Set G)) :=
  ⟨isDSequence_singleton_one μ, fun _ hW ↦ ⟨0, singleton_subset_iff.mpr (mem_of_mem_nhds hW)⟩⟩

/-- Paper: Remark A.5.2.4, p. 570. The constant singleton of the identity, paired
with itself, is a D″-sequence on a countable discrete abelian group. -/
theorem isDDoublePrimeSequence_singleton_one [Countable G] [DiscreteTopology G]
    [μ.IsHaarMeasure] :
    IsDDoublePrimeSequence μ (fun _ ↦ ({1} : Set G)) (fun _ ↦ ({1} : Set G)) := by
  refine ⟨isDPrimeSequence_singleton_one μ, 1, one_pos, fun _ ↦
    ⟨(measurableSet_singleton 1).nullMeasurableSet, ?_, ?_⟩⟩
  · simp
  · simp

end TopologicalGroups

section Products

variable {G₁ G₂ : Type*}
  [CommGroup G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [T2Space G₁]
  [LocallyCompactSpace G₁] [MeasurableSpace G₁] [BorelSpace G₁]
  [CommGroup G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [T2Space G₂]
  [LocallyCompactSpace G₂] [MeasurableSpace G₂] [BorelSpace G₂]

local instance : MeasurableSpace (G₁ × G₂) := borel _

variable {μ₁ : Measure G₁} {μ₂ : Measure G₂} {μ : Measure (G₁ × G₂)}
  [μ₁.IsHaarMeasure] [μ₂.IsHaarMeasure] [μ.IsHaarMeasure]
  {U : ℕ → Set G₁} {V : ℕ → Set G₂}

variable (hμ : ∀ (s : Set G₁) (t : Set G₂), MeasurableSet s → MeasurableSet t →
  μ (s ×ˢ t) = μ₁ s * μ₂ t)

include hμ in
/-- A measure specified by its values on Borel rectangles is bounded on any rectangle by the
product of the outer measures of the sides. -/
theorem measure_prod_le_of_rectangles (s : Set G₁) (t : Set G₂) :
    μ (s ×ˢ t) ≤ μ₁ s * μ₂ t := by
  calc μ (s ×ˢ t) ≤ μ (toMeasurable μ₁ s ×ˢ toMeasurable μ₂ t) :=
        measure_mono (Set.prod_mono (subset_toMeasurable _ _) (subset_toMeasurable _ _))
    _ = μ₁ s * μ₂ t := by
        rw [hμ _ _ (measurableSet_toMeasurable _ _) (measurableSet_toMeasurable _ _),
          measure_toMeasurable, measure_toMeasurable]

include hμ in
/-- A measure specified by its values on Borel rectangles takes the product value on a
rectangle with null-measurable sides, and such a rectangle is null-measurable. -/
theorem measure_prod_of_rectangles {s : Set G₁} {t : Set G₂} (hs : NullMeasurableSet s μ₁)
    (ht : NullMeasurableSet t μ₂) :
    μ (s ×ˢ t) = μ₁ s * μ₂ t ∧ NullMeasurableSet (s ×ˢ t) μ := by
  obtain ⟨s', hs's, hs'm, hs'e⟩ := hs.exists_measurable_subset_ae_eq
  obtain ⟨t', ht't, ht'm, ht'e⟩ := ht.exists_measurable_subset_ae_eq
  have hrect : μ (s' ×ˢ t') = μ₁ s * μ₂ t := by
    rw [hμ _ _ hs'm ht'm, measure_congr hs'e, measure_congr ht'e]
  have hsub : s' ×ˢ t' ⊆ s ×ˢ t := Set.prod_mono hs's ht't
  refine ⟨le_antisymm (measure_prod_le_of_rectangles hμ s t) (hrect ▸ measure_mono hsub), ?_⟩
  have hs0 : μ₁ (s \ s') = 0 := (ae_eq_set.mp hs'e).2
  have ht0 : μ₂ (t \ t') = 0 := (ae_eq_set.mp ht'e).2
  have hdiff : s ×ˢ t \ s' ×ˢ t' ⊆ (s \ s') ×ˢ Set.univ ∪ Set.univ ×ˢ (t \ t') := by
    rintro ⟨x, y⟩ ⟨⟨hx, hy⟩, hxy⟩
    by_cases hx' : x ∈ s'
    · exact Or.inr ⟨trivial, hy, fun hy' ↦ hxy ⟨hx', hy'⟩⟩
    · exact Or.inl ⟨⟨hx, hx'⟩, trivial⟩
  have hnull : μ (s ×ˢ t \ s' ×ˢ t') = 0 := by
    refine measure_mono_null hdiff (measure_union_null ?_ ?_)
    · exact le_zero_iff.mp ((measure_prod_le_of_rectangles hμ _ _).trans_eq
        (by rw [hs0, zero_mul]))
    · exact le_zero_iff.mp ((measure_prod_le_of_rectangles hμ _ _).trans_eq
        (by rw [ht0, mul_zero]))
  have hmeas : MeasurableSet (s' ×ˢ t') := by
    have : BorelSpace (G₁ × G₂) := ⟨rfl⟩
    exact (continuous_fst.measurable hs'm).inter (continuous_snd.measurable ht'm)
  exact hmeas.nullMeasurableSet.congr
    (ae_eq_set.mpr ⟨by rw [Set.sdiff_eq_empty.mpr hsub, measure_empty], hnull⟩)

include hμ in
/-- Paper: Lemma A.5.2.5, p. 570. The termwise Cartesian product of D-sequences is a
D-sequence for product Haar measure.
Deviation: The product Haar measure is specified by its values on Borel rectangles.
This formulation also covers groups whose Haar measure is outside the scope of
Mathlib's `Measure.prod` construction. -/
theorem IsDSequence.prod (hU : IsDSequence μ₁ U) (hV : IsDSequence μ₂ V) :
    IsDSequence μ (fun k ↦ U k ×ˢ V k) := by
  obtain ⟨hU₁, hUa, C₁, hC₁, hU₂⟩ := hU
  obtain ⟨hV₁, hVa, C₂, hC₂, hV₂⟩ := hV
  have hval (k : ℕ) := measure_prod_of_rectangles hμ (hU₁ k).2.1 (hV₁ k).2.1
  have hpos (k : ℕ) : 0 < μ (U k ×ˢ V k) := by
    rw [(hval k).1]
    exact ENNReal.mul_pos (hU₁ k).2.2.1.ne' (hV₁ k).2.2.1.ne'
  refine ⟨fun k ↦ ⟨⟨(hU₁ k).1, (hV₁ k).1⟩, (hval k).2, hpos k, ?_⟩,
    fun i j hij ↦ Set.prod_mono (hUa hij) (hVa hij), C₁ * C₂, mul_pos hC₁ hC₂, fun k ↦ ?_⟩
  · rw [(hval k).1]
    exact ENNReal.mul_lt_top (hU₁ k).2.2.2 (hV₁ k).2.2.2
  rw [Set.inv_prod, Set.prod_mul_prod_comm]
  have hone₁ : (1 : G₁) ∈ (U k)⁻¹ := by simpa using (hU₁ k).1
  have hone₂ : (1 : G₂) ∈ (V k)⁻¹ := by simpa using (hV₁ k).1
  refine ⟨(hpos k).trans_le (measure_mono (Set.prod_mono (Set.subset_mul_left _ hone₁)
    (Set.subset_mul_left _ hone₂))), ?_⟩
  calc μ ((U k * (U k)⁻¹) ×ˢ (V k * (V k)⁻¹))
      ≤ μ₁ (U k * (U k)⁻¹) * μ₂ (V k * (V k)⁻¹) := measure_prod_le_of_rectangles hμ _ _
    _ < (ENNReal.ofReal C₁ * μ₁ (U k)) * (ENNReal.ofReal C₂ * μ₂ (V k)) :=
        ENNReal.mul_lt_mul (hU₂ k).2 (hV₂ k).2
    _ = ENNReal.ofReal (C₁ * C₂) * μ (U k ×ˢ V k) := by
        rw [(hval k).1, ENNReal.ofReal_mul hC₁.le, mul_mul_mul_comm]

include hμ in
/-- Paper: Lemma A.5.2.5, p. 570. The termwise Cartesian product of D′-sequences is a
D′-sequence for product Haar measure, specified by its values on Borel rectangles. -/
theorem IsDPrimeSequence.prod (hU : IsDPrimeSequence μ₁ U) (hV : IsDPrimeSequence μ₂ V) :
    IsDPrimeSequence μ (fun k ↦ U k ×ˢ V k) := by
  refine ⟨hU.1.prod hμ hV.1, fun W hW ↦ ?_⟩
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hW
  obtain ⟨k₁, hk₁⟩ := hU.2 A hA
  obtain ⟨k₂, hk₂⟩ := hV.2 B hB
  refine ⟨max k₁ k₂, (Set.prod_mono ?_ ?_).trans hAB⟩
  · exact (hU.1.2.1 (le_max_left k₁ k₂)).trans hk₁
  · exact (hV.1.2.1 (le_max_right k₁ k₂)).trans hk₂

/-- Paper: Lemma A.5.2.5, p. 570. The product of two open members is open. -/
theorem isOpen_prod_sequence (k : ℕ) (hU : IsOpen (U k)) (hV : IsOpen (V k)) :
    IsOpen (U k ×ˢ V k) := hU.prod hV

/-- Paper: Lemma A.5.2.5, p. 570. The product of two symmetric members is symmetric. -/
theorem inv_eq_prod_sequence (k : ℕ) (hU : (U k)⁻¹ = U k) (hV : (V k)⁻¹ = V k) :
    (U k ×ˢ V k)⁻¹ = U k ×ˢ V k := by
  rw [Set.inv_prod, hU, hV]

end Products

section QuotientGroups

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)

local instance : MeasurableSpace (G ⧸ H) := borel _
local notation "q" => (QuotientGroup.mk' H)

variable [DiscreteTopology H] (hH : IsClosed (H : Set G))
  {μ : Measure G} [μ.IsHaarMeasure]
  {μH : Measure H} [μH.IsHaarMeasure] {ν : Measure (G ⧸ H)}
  (hν : IsWeilQuotientMeasure H μ μH ν) (hcount : μH {1} = 1)
  {E : Set G} (hE : MeasurableSet E) (hEc : IsCompact (closure E))
  (hE₁ : 1 ∈ interior E)
  (hbij : Bijective (fun x : E ↦ (QuotientGroup.mk' H) (x : G)))
  {U : ℕ → Set (G ⧸ H)} (hU : ∀ k, MeasurableSet (U k)) (hmono : Antitone U)

local notation "lifted" => (fun k ↦ Set.inter (q ⁻¹' U k) E)

include hH hν hcount hE hEc hbij in
/-- A precompact Borel transversal computes Weil quotient mass, also for outer measures. -/
private theorem weilQuotientMeasure_apply_of_transversal (S : Set (G ⧸ H)) :
    ν S = μ (q ⁻¹' S ∩ E) := by
  classical
  let : IsClosed (H : Set G) := hH
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let : Countable H.op := H.equivOp.symm.injective.countable
  let : ν.Regular := hν.2.1
  have hq : Continuous q := QuotientGroup.continuous_mk
  let νE := (μ.restrict E).map q
  let : IsFiniteMeasure νE := ⟨by
    rw [Measure.map_apply hq.measurable MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt hEc.measure_lt_top⟩
  have hdomain : IsFundamentalDomain H.op E μ := by
    apply IsFundamentalDomain.mk' hE.nullMeasurableSet
    intro x
    obtain ⟨y, hy⟩ := hbij.2 (q x)
    let h : H := ⟨x⁻¹ * y, QuotientGroup.eq.mp hy.symm⟩
    refine ⟨H.equivOp h, ?_, ?_⟩
    · change x * (x⁻¹ * (y : G)) ∈ E
      simp [y.property]
    · intro a ha
      apply H.equivOp.symm.injective
      apply Subtype.ext
      apply mul_left_cancel (a := x)
      change a • x = x * (x⁻¹ * (y : G))
      rw [mul_inv_cancel_left]
      have he : (⟨a • x, ha⟩ : E) = y := hbij.1
        ((QuotientGroup.mk_mul_of_mem x (H.equivOp.symm a).property).trans hy.symm)
      exact congrArg Subtype.val he
  have hsingle (h : H) : μH {h} = 1 := by
    calc
      μH {h} = μH ((fun x : H ↦ h * x) ⁻¹' {h}) := (measure_preimage_mul μH h _).symm
      _ = μH {1} := by congr 1; ext x; simp
      _ = 1 := hcount
  let ses := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  have hperiod (f : CompactlySupportedContinuousMap G ℝ) :
      QuotientGroup.automorphize (Γ := H) f = ses.pushforward μH f := by
    funext z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H z
    rw [ses.pushforward_apply_apply, integral_countable (ses.pullback f x).integrable]
    simp only [measureReal_def, hsingle, ENNReal.toReal_one, one_smul]
    exact H.equivOp.symm.tsum_eq (fun h : H ↦ f (x * (h : G)))
  have htest (f : CompactlySupportedContinuousMap G ℝ) :
      (∫ z, ses.pushforward μH f z ∂ν) = ∫ z, ses.pushforward μH f z ∂νE := by
    let fc : C(G, ℂ) := ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
    have hcoset (z : G ⧸ H) :
        lcaCosetIntegral H μH fc z = (ses.pushforward μH f z : ℂ) := by
      have hz : q z.out = z := Quotient.out_eq' z
      rw [← hz, ses.pushforward_apply_apply]
      rw [hz, lcaCosetIntegral]
      exact integral_complex_ofReal
    have hw := hν.2.2 fc (f.hasCompactSupport.comp_left Complex.ofReal_zero)
    change (∫ x, (f x : ℂ) ∂μ) = ∫ z, lcaCosetIntegral H μH fc z ∂ν at hw
    simp_rw [hcoset, integral_complex_ofReal] at hw
    have hm : AEStronglyMeasurable (QuotientGroup.automorphize (Γ := H) f) νE :=
      hperiod f ▸ (ses.pushforward μH f).continuous.aestronglyMeasurable
    exact (Complex.ofReal_injective hw).symm.trans
      (hperiod f ▸ QuotientGroup.integral_eq_integral_automorphize hdomain f.integrable hm)
  obtain ⟨b, hb, -, hbc, hb₀⟩ :=
    exists_continuous_one_zero_of_isCompact hEc isClosed_empty (disjoint_empty _)
  let b₀ : CompactlySupportedContinuousMap G ℝ := ⟨b, hbc⟩
  let c := ses.pushforward μH b₀
  have hc (z : G ⧸ H) : 0 < c z := by
    obtain ⟨x, rfl⟩ := hbij.2 z
    change 0 < ses.pushforward μH b₀ (q (x : G))
    rw [ses.pushforward_apply_apply]
    apply (integral_pos_iff_support_of_nonneg (fun _ ↦ (hb₀ _).1)
      (ses.pullback b₀ (x : G)).integrable).mpr
    have hmem : (1 : H) ∈ Function.support (ses.pullback b₀ (x : G)) := by
      rw [Function.mem_support, ses.pullback_def, Subgroup.coe_subtype,
        Subgroup.coe_one, mul_one]
      change b (x : G) ≠ 0
      exact (hb (subset_closure x.property)).trans_ne one_ne_zero
    have hle := measure_mono (μ := μH) (singleton_subset_iff.mpr hmem)
    rw [hcount] at hle
    exact zero_lt_one.trans_le hle
  have hνE : ν = νE := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro g
    let a : G → ℝ := fun x ↦ g (q x) / c (q x)
    have ha : Continuous a :=
      (g.continuous.comp hq).div (c.continuous.comp hq) fun x ↦ (hc (q x)).ne'
    let f : CompactlySupportedContinuousMap G ℝ :=
      ⟨⟨a * b₀, ha.mul b₀.continuous⟩, b₀.hasCompactSupport.mul_left⟩
    have hf : ⇑(ses.pushforward μH f) = g := by
      funext z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H z
      have hp (h : H) : ses.pullback f x h = a x * ses.pullback b₀ x h := by
        have hh : q (x * (h : G)) = q x := QuotientGroup.mk_mul_of_mem x h.property
        simp only [ses.pullback_def, Subgroup.coe_subtype]
        change a (x * h) * b₀ (x * h) = a x * b₀ (x * h)
        simp only [a, hh]
      rw [ses.pushforward_apply_apply]
      simp_rw [hp]
      rw [integral_const_mul, ← ses.pushforward_apply_apply]
      exact div_mul_cancel₀ _ (hc (q x)).ne'
    simpa only [hf] using htest f
  -- The measurable embedding extends the measure identity to arbitrary sets.
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  let : IsUniformGroup G := isUniformGroup_of_commGroup
  let : CompleteSpace G := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace G
  let : (uniformity G).IsCountablyGenerated := IsUniformGroup.uniformity_countably_generated
  let : PolishSpace G := ⟨⟩
  have hemb := ContinuousOn.measurableEmbedding hE hq.continuousOn
    (injOn_iff_injective.mpr hbij.1)
  have hcoe := MeasurableEmbedding.subtype_coe hE
  rw [hνE]
  change (μ.restrict E).map q S = _
  rw [← Subtype.range_coe (s := E), ← hcoe.map_comap μ,
    Measure.map_map hq.measurable hcoe.measurable]
  change ((μ.comap (Subtype.val : E → G)).map (E.domRestrict q)) S = _
  rw [hemb.map_apply, hcoe.comap_apply]
  congr 1
  ext x
  simp [Set.mem_inter_iff, and_comm]

include hH hν hcount hE hEc hE₁ hbij hU hmono in
/-- Paper: Proposition A.5.2.6, p. 570. A decreasing Borel family on the
quotient is a D-sequence exactly when its lifts to the fundamental domain form one. -/
theorem isDSequence_quotient_iff :
    IsDSequence ν U ↔ IsDSequence μ lifted := by
  classical
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  have hq : Continuous q := QuotientGroup.continuous_mk
  have hmass := weilQuotientMeasure_apply_of_transversal H hH hν hcount hE hEc hbij
  have hmassU (k : ℕ) : ν (U k) = μ (lifted k) := hmass (U k)
  have hone : (1 : G) ∈ E := interior_subset hE₁
  have himage (S : Set (G ⧸ H)) : q '' (q ⁻¹' S ∩ E) = S := by
    refine subset_antisymm (image_subset_iff.mpr inter_subset_left) fun x hx ↦ ?_
    obtain ⟨y, hy⟩ := hbij.2 x
    change q (y : G) = x at hy
    exact ⟨y, ⟨show q (y : G) ∈ S from hy.symm ▸ hx, y.property⟩, hy⟩
  have himageU (k : ℕ) : q '' (lifted k) = U k := himage (U k)
  let K : Set G := closure E * (closure E)⁻¹
  have hK : IsCompact K := hEc.mul hEc.inv
  have hEK : E ⊆ K :=
    subset_closure.trans (Set.subset_mul_left _ (by simpa using subset_closure hone))
  -- Sets inside K with the same quotient image cover one another by finitely many translates.
  have hfin : (Subtype.val ⁻¹' (K * K⁻¹) : Set H).Finite :=
    (hH.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.mul hK.inv)).finite_of_discrete
  let J := hfin.toFinset
  let N : ℝ := J.card + 1
  have hN : 0 < N := by dsimp [N]; positivity
  have hJ : (J.card : ℝ≥0∞) ≤ ENNReal.ofReal N := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by dsimp [N]; linarith)
  have hcompare {A B : Set G} (hA : A ⊆ K) (hB : B ⊆ K)
      (hAB : q '' A ⊆ q '' B) : μ A ≤ ENNReal.ofReal N * μ B := by
    have hcover : A ⊆ ⋃ h ∈ J, (fun x : G ↦ (h : G) * x) ⁻¹' B := by
      intro a ha
      obtain ⟨b, hb, heq⟩ := hAB (mem_image_of_mem q ha)
      let h : H := ⟨a⁻¹ * b, QuotientGroup.eq.mp heq.symm⟩
      have hh : h ∈ J := hfin.mem_toFinset.mpr <| Set.mem_mul.mpr
        ⟨b, hB hb, a⁻¹, Set.inv_mem_inv.mpr (hA ha), mul_comm _ _⟩
      exact mem_iUnion₂.mpr ⟨h, hh, by simpa [h, mul_comm] using hb⟩
    calc
      μ A ≤ μ (⋃ h ∈ J, (fun x : G ↦ (h : G) * x) ⁻¹' B) := measure_mono hcover
      _ ≤ ∑ h ∈ J, μ ((fun x : G ↦ (h : G) * x) ⁻¹' B) := measure_biUnion_finset_le _ _
      _ = (J.card : ℝ≥0∞) * μ B := by simp [measure_preimage_mul, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal N * μ B := by gcongr
  have hdiff (k : ℕ) :
      μ (lifted k * (lifted k)⁻¹) ≤ ENNReal.ofReal N * ν (U k * (U k)⁻¹) ∧
      ν (U k * (U k)⁻¹) ≤ ENNReal.ofReal N * μ (lifted k * (lifted k)⁻¹) := by
    let S := U k * (U k)⁻¹
    have hsub : lifted k * (lifted k)⁻¹ ⊆ K :=
      Set.mul_subset_mul (inter_subset_right.trans subset_closure)
        (Set.inv_subset_inv.mpr (inter_subset_right.trans subset_closure))
    have hsub' : q ⁻¹' S ∩ E ⊆ K := inter_subset_right.trans hEK
    have hqdiff : q '' (lifted k * (lifted k)⁻¹) = S := by
      rw [Set.image_mul, Set.image_inv, himageU]
    rw [hmass S]
    exact ⟨hcompare hsub hsub' (by rw [hqdiff, himage]),
      hcompare hsub' hsub (by rw [hqdiff, himage])⟩
  have hscale {a b m : ℝ≥0∞} {C : ℝ}
      (hle : a ≤ ENNReal.ofReal N * b) (hlt : b < ENNReal.ofReal C * m) :
      a < ENNReal.ofReal (N * C) * m := by
    rw [ENNReal.ofReal_mul hN.le, mul_assoc]
    exact hle.trans_lt (ENNReal.mul_lt_mul_right (by simp [hN]) ENNReal.ofReal_ne_top hlt)
  constructor
  · rintro ⟨hbase, -, C, hC, hdouble⟩
    have hbase' (k : ℕ) : 1 ∈ lifted k ∧ 0 < μ (lifted k) ∧ μ (lifted k) < ∞ := by
      refine ⟨⟨by simpa using (hbase k).1, hone⟩, ?_⟩
      rw [← hmassU k]
      exact (hbase k).2.2
    refine ⟨fun k ↦ ⟨(hbase' k).1, ((hq.measurable (hU k)).inter hE).nullMeasurableSet,
        (hbase' k).2⟩, fun _ _ hij ↦ inter_subset_inter_left _ (preimage_mono (hmono hij)),
      N * C, mul_pos hN hC, fun k ↦ ⟨?_, ?_⟩⟩
    · exact (hbase' k).2.1.trans_le
        (measure_mono (Set.subset_mul_left _ (by simpa using (hbase' k).1)))
    · rw [← hmassU k]
      exact hscale (hdiff k).1 (hdouble k).2
  · rintro ⟨hbase, -, C, hC, hdouble⟩
    have hbase' (k : ℕ) : 1 ∈ U k ∧ 0 < ν (U k) ∧ ν (U k) < ∞ := by
      refine ⟨by simpa using (hbase k).1.1, ?_⟩
      rw [hmass]
      exact (hbase k).2.2
    refine ⟨fun k ↦ ⟨(hbase' k).1, (hU k).nullMeasurableSet, (hbase' k).2⟩, hmono,
      N * C, mul_pos hN hC, fun k ↦ ⟨?_, ?_⟩⟩
    · exact (hbase' k).2.1.trans_le
        (measure_mono (Set.subset_mul_left _ (by simpa using (hbase' k).1)))
    · rw [hmass (U k)]
      exact hscale (hdiff k).2 (hdouble k).2

include hH hν hcount hE hEc hE₁ hbij hU hmono in
/-- Paper: Proposition A.5.2.6, p. 571. The D′ condition is equivalent for the
quotient sequence and for the lifts through the fundamental domain. -/
theorem isDPrimeSequence_quotient_iff :
    IsDPrimeSequence ν U ↔ IsDPrimeSequence μ lifted := by
  unfold IsDPrimeSequence
  rw [isDSequence_quotient_iff H hH hν hcount hE hEc hE₁ hbij hU hmono]
  have hopen : IsOpenMap q := QuotientGroup.isOpenMap_coe
  have hq : Continuous q := QuotientGroup.continuous_mk
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · intro h W hW
    have himage : q '' (W ∩ E) ∈ 𝓝 (1 : G ⧸ H) := by
      simpa only [map_one] using
        hopen.image_mem_nhds (inter_mem hW (mem_interior_iff_mem_nhds.mp hE₁))
    obtain ⟨k, hk⟩ := h _ himage
    refine ⟨k, fun x hx ↦ ?_⟩
    obtain ⟨y, hy, heq⟩ := hk hx.1
    have hxy : y = x := (injOn_iff_injective.mpr hbij.1) hy.2 hx.2 heq
    exact hxy ▸ hy.1
  · intro h W hW
    have hpreimage : q ⁻¹' W ∈ 𝓝 (1 : G) :=
      hq.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hW)
    obtain ⟨k, hk⟩ := h _ hpreimage
    refine ⟨k, fun y hy ↦ ?_⟩
    obtain ⟨x, rfl⟩ := hbij.2 y
    exact hk ⟨hy, x.property⟩

include hbij in
/-- Paper: Proposition A.5.2.6, p. 571. For a symmetric fundamental domain,
the quotient family is symmetric exactly when the lifted family is symmetric. -/
theorem inv_eq_sequence_quotient_iff (hEsymm : E⁻¹ = E) :
    (∀ k, (U k)⁻¹ = U k) ↔ ∀ k, (lifted k)⁻¹ = lifted k := by
  constructor
  · intro h k
    have hpre : (q ⁻¹' U k)⁻¹ = q ⁻¹' (U k)⁻¹ := by
      ext x
      simp only [Set.mem_inv, Set.mem_preimage, map_inv]
    change (q ⁻¹' U k ∩ E)⁻¹ = q ⁻¹' U k ∩ E
    rw [Set.inter_inv, hpre, h k, hEsymm]
  · intro h k
    have hsurj : q '' E = univ := by
      rw [← Set.range_domRestrict, Set.range_eq_univ]
      exact hbij.2
    have himage : q '' lifted k = U k := by
      change q '' (q ⁻¹' U k ∩ E) = U k
      rw [Set.image_preimage_inter, hsurj, inter_univ]
    simpa only [Set.image_inv, himage] using congrArg (fun s : Set G ↦ q '' s) (h k)

-- TODO(paper-gap): The D″ equivalence claimed in the proof of A.5.2.6 fails.
-- For ℤ → ℤ/3ℤ take the symmetric domain {-1, 0, 1} and U₀ = V₀ = ℤ/3ℤ.
-- The difference set of the lifts contains 2, which is outside the domain.

end QuotientGroups

/-- Paper: Theorem A.5.2.8, p. 571. A continuous map between Polish spaces sends a
Borel subset on which it is injective to a Borel set. -/
theorem measurableSet_image_of_continuous_injOn_polish {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Continuous f) {E : Set X} (hE : MeasurableSet E)
    (hinj : InjOn f E) :
    MeasurableSet (f '' E) := by
  exact hE.image_of_continuousOn_injOn hf.continuousOn hinj

/-- Paper: Lemma A.5.2.10, p. 572. A Borel partial transversal to a free proper action
of a countable discrete abelian group extends to a Borel transversal.
Deviation: The group acts on X, as specified by the quotient and proof. -/
theorem exists_borel_orbit_transversal {X H : Type*}
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [CommGroup H] [TopologicalSpace H] [DiscreteTopology H]
    [Countable H] [MulAction H X] [ProperSMul H X] [IsCancelSMul H X]
    {E : Set X} (hE : MeasurableSet E)
    (hinj : InjOn (Quotient.mk (MulAction.orbitRel H X)) E) :
    ∃ F : Set X, MeasurableSet F ∧ E ⊆ F ∧
      Bijective (fun x : F ↦ Quotient.mk (MulAction.orbitRel H X) (x : X)) := by
  classical
  let q := Quotient.mk (MulAction.orbitRel H X)
  let : ProperlyDiscontinuousSMul H X :=
    properlyDiscontinuousSMul_iff_properSMul.mpr inferInstance
  have hlocal : IsLocallyInjective q :=
    isLocalHomeomorph_quotientMk_of_properlyDiscontinuousSMul.isLocallyInjective
  let OpenInj := {s : Set X // IsOpen s ∧ InjOn q s}
  let : Nonempty OpenInj := ⟨⟨∅, isOpen_empty, injOn_empty q⟩⟩
  obtain ⟨V, hV⟩ := isLindelof_univ.indexed_countable_subcover
    (Subtype.val : OpenInj → Set X) (fun s ↦ s.property.1) (by
      intro x _
      obtain ⟨s, ho, hx, hi⟩ := hlocal x
      exact mem_iUnion.mpr ⟨⟨s, ho, hi⟩, hx⟩)
  let U : ℕ → Set X := fun
    | 0 => E
    | n + 1 => (V n).val
  have hU (n : ℕ) : MeasurableSet (U n) ∧ InjOn q (U n) := by
    cases n with
    | zero => exact ⟨hE, hinj⟩
    | succ n => exact ⟨(V n).property.1.measurableSet, (V n).property.2⟩
  let Q (n : ℕ) := q '' U n
  have hsat (n : ℕ) : MeasurableSet (q ⁻¹' Q n) := by
    rw [show q ⁻¹' Q n = ⋃ g : H, (g • ·) '' U n from
      MulAction.quotient_preimage_image_eq_union_mul (U n)]
    exact MeasurableSet.iUnion fun g ↦
      (Homeomorph.smul g).measurableEmbedding.measurableSet_image.mpr (hU n).1
  -- Use the first set meeting each orbit, with `E` in position zero.
  let F := ⋃ n, U n ∩ q ⁻¹' disjointed Q n
  have hF : MeasurableSet F := MeasurableSet.iUnion fun n ↦ (hU n).1.inter (by
    simp only [disjointed_eq_inter_compl, preimage_inter, preimage_iInter, preimage_compl]
    exact (hsat n).inter (MeasurableSet.iInter fun j ↦
      MeasurableSet.iInter fun _ ↦ (hsat j).compl))
  refine ⟨F, hF, fun x hx ↦ mem_iUnion.mpr ⟨0, hx, ?_⟩, ⟨?_, ?_⟩⟩
  · change q x ∈ disjointed Q 0
    rw [show disjointed Q 0 = Q 0 from disjointed_bot Q]
    exact mem_image_of_mem q hx
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ (hxy : q x = q y)
    obtain ⟨m, hxm, hqx⟩ := mem_iUnion.mp hx
    obtain ⟨n, hyn, hqy⟩ := mem_iUnion.mp hy
    have hmn : m = n := by
      by_contra hne
      exact (Set.disjoint_left.mp (disjoint_disjointed Q hne)) hqx (hxy.symm ▸ hqy)
    subst n
    exact Subtype.ext ((hU m).2 hxm hyn hxy)
  · intro z
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective z
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hV (mem_univ x))
    have hx : q x ∈ ⋃ n, disjointed Q n := by
      rw [iUnion_disjointed]
      exact mem_iUnion.mpr ⟨n + 1, mem_image_of_mem q hn⟩
    obtain ⟨m, hm⟩ := mem_iUnion.mp hx
    obtain ⟨y, hy, hyx⟩ := disjointed_subset Q m hm
    have hqy : q y ∈ disjointed Q m := hyx.symm ▸ hm
    exact ⟨⟨y, mem_iUnion.mpr ⟨m, hy, hqy⟩⟩, hyx⟩

section Ideles

set_option maxSynthPendingDepth 8

open NumberField InfinitePlace.Completion
open NumberField.Units.dirichletUnitTheorem
open IsDedekindDomain

variable (F : Type*) [Field F] [NumberField F]

local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)
local notation "N₁" => MonoidHom.ker (ideleNorm F)
local notation "atInfinity" => Units.map (RingHom.toMonoidHom (RingHom.fst _ _))

variable (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))

-- Equations (A.5.2.7)–(A.5.2.10) recall the domains already defined in §A.2.3.

/-- Paper: (A.5.2.11)–(A.5.2.12), p. 574. Translate the regulator
parallelotope by minus one half of the sum of its basis vectors.
Deviation: As in §A.2.3, logarithmic coordinates omit one infinite place. -/
def centeredRegulatorParallelotope : Set (logSpace F) :=
  (-∑ i, (1 / 2 : ℝ) • Units.logEmbeddingQuot F (b i)) +ᵥ regulatorParallelotope F b

/-- Paper: (A.5.2.11)–(A.5.2.12), p. 574. On one basis direction the centered
parallelotope includes coefficients from minus one half up to one half, excluding the latter. -/
theorem centeredRegulatorParallelotope_basis_line (i : Fin (Units.rank F)) (t : ℝ) :
    t • Units.logEmbeddingQuot F (b i) ∈ centeredRegulatorParallelotope F b ↔
      t ∈ Ico (-1 / 2 : ℝ) (1 / 2) := by
  classical
  obtain ⟨B, hP, hB⟩ : ∃ B : Module.Basis (Fin (Units.rank F)) ℝ (logSpace F),
      regulatorParallelotope F b = ZSpan.fundamentalDomain B ∧
        ∀ j, Units.logEmbeddingQuot F (b j) = B j := by
    refine ⟨_, rfl, fun j ↦ ?_⟩
    rw [Module.Basis.ofZLatticeBasis_apply]
    rfl
  simp only [centeredRegulatorParallelotope, hP, hB]
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, ZSpan.mem_fundamentalDomain]
  simp only [map_add, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_add,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Set.mem_Ico]
  constructor
  · intro h
    have := h i
    simp only [ite_true] at this
    constructor <;> linarith [this.1, this.2]
  · intro ht j
    split_ifs <;> constructor <;> linarith [ht.1, ht.2]

variable (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)

local notation "atPlace" => Units.map (RingHom.toMonoidHom (Pi.evalRingHom InfinitePlace.Completion v₀))

/-- Paper: (A.5.2.14), p. 575. The centered angular sector has width two pi
divided by the number of roots of unity.
Deviation: We use the principal argument, so the two intervals in the paper are one
half-open interval centered at zero. -/
def inCenteredTorsionSector (x : v₀.Completionˣ) : Prop :=
  (σ (extensionEmbedding v₀ x.val)).arg ∈
    Ico (-Real.pi / (Units.torsionOrder F : ℝ)) (Real.pi / (Units.torsionOrder F : ℝ))

/-- Paper: (A.5.2.14), p. 575. At a real place the centered angular sector
picks out the positive component. -/
theorem inCenteredTorsionSector_real (hv : v₀.IsReal) (x : v₀.Completionˣ) :
    inCenteredTorsionSector F v₀ σ x ↔ 0 < extensionEmbeddingOfIsReal hv x.val := by
  have hn : (0 : ℝ) < Units.torsionOrder F := by exact_mod_cast Units.torsionOrder_pos F
  have hr : extensionEmbeddingOfIsReal hv x.val ≠ 0 := (x.isUnit.map _).ne_zero
  have hσ : σ (extensionEmbedding v₀ x.val) = (extensionEmbeddingOfIsReal hv x.val : ℂ) := by
    rw [← extensionEmbeddingOfIsReal_apply hv]
    exact σ.commutes _
  unfold inCenteredTorsionSector
  rw [hσ]
  rcases hr.lt_or_gt with h | h
  · rw [Complex.arg_ofReal_of_neg h]
    have hle : Real.pi / Units.torsionOrder F ≤ Real.pi := by
      rw [div_le_iff₀ hn]
      have : (1 : ℝ) ≤ Units.torsionOrder F := by exact_mod_cast Units.torsionOrder_pos F
      nlinarith [Real.pi_pos]
    exact iff_of_false (fun h' ↦ absurd h'.2 (not_lt.mpr hle)) (not_lt.mpr h.le)
  · rw [Complex.arg_ofReal_of_nonneg h.le]
    refine iff_of_true ⟨?_, by positivity⟩ h
    rw [neg_div]
    exact neg_nonpos.mpr (by positivity)

/-- Paper: (A.5.2.14), p. 575. The centered archimedean domain is cut out by
the centered regulator parallelotope and the centered angular sector. -/
def centeredInfiniteIdeleDomain : Set N∞ :=
  {g | (fun w : {w : InfinitePlace F // w ≠ w₀} ↦ infiniteIdeleLog F g.val w.val) ∈
    centeredRegulatorParallelotope F b ∧ inCenteredTorsionSector F v₀ σ (atPlace g.val)}

/-- Paper: (A.5.2.13), p. 575. The norm-one integral ideles whose
archimedean component lies in the centered domain form the set B_F¹. -/
def centeredIntegralIdeleDomain : Set N₁ :=
  {g | g.val ∈ (Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom).range ∧
    atInfinity g.val ∈ (N∞).subtype '' centeredInfiniteIdeleDomain F b v₀ σ}

/-- Paper: (A.5.2.13), p. 575. The identity idele belongs to the centered integral domain. -/
theorem one_mem_centeredIntegralIdeleDomain :
    1 ∈ centeredIntegralIdeleDomain F b v₀ σ := by
  classical
  obtain ⟨B, hP, hB⟩ : ∃ B : Module.Basis (Fin (Units.rank F)) ℝ (logSpace F),
      regulatorParallelotope F b = ZSpan.fundamentalDomain B ∧
        ∀ j, Units.logEmbeddingQuot F (b j) = B j := by
    refine ⟨_, rfl, fun j ↦ ?_⟩
    rw [Module.Basis.ofZLatticeBasis_apply]
    rfl
  have hn : (0 : ℝ) < Units.torsionOrder F := by exact_mod_cast Units.torsionOrder_pos F
  have hlog : (fun w : {w : InfinitePlace F // w ≠ w₀} ↦
      infiniteIdeleLog F (1 : N∞).val w.val) = 0 := by
    funext w
    show (w.val.mult : ℝ) * Real.log ‖(1 : w.val.Completion)‖ = 0
    simp
  have hdom : (1 : N∞) ∈ centeredInfiniteIdeleDomain F b v₀ σ := by
    refine ⟨?_, ?_⟩
    · rw [hlog]
      simp only [centeredRegulatorParallelotope, hP, hB]
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, add_zero,
        ZSpan.mem_fundamentalDomain]
      intro j
      simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply,
        Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, Set.mem_Ico]
      norm_num
    · show (σ (extensionEmbedding v₀ (1 : v₀.Completion))).arg ∈ _
      rw [map_one, map_one, Complex.arg_one, Set.mem_Ico, neg_div]
      exact ⟨neg_nonpos.mpr (by positivity), by positivity⟩
  exact ⟨⟨1, map_one _⟩, 1, hdom, by simp⟩

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Oₛ(" F ", " S ")" => Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F
local notation "Nₛ" => MonoidHom.ker (sIdeleNorm F S)
local notation "sRank(" F ", " S ")" => (Fintype.card (InfinitePlace F) + Finset.card S - 1)
local notation "unitAtS" => MonoidHom.comp (Units.map (RingHom.toMonoidHom (adeleProjection F S)))
  (MonoidHom.comp (Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside F S))))
    (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S))))

variable (bₛ : Module.Basis (Fin sRank(F, S)) ℤ (Additive (Oₛ(F, S)ˣ ⧸ CommGroup.torsion Oₛ(F, S)ˣ)))

/-- Paper: (A.5.2.18), p. 575. The S-regulator parallelotope consists of sums
of the basis logarithms with coefficients in the centered half-open unit interval.
Deviation: As in §A.2.4, the integral basis is taken modulo torsion. -/
def centeredSRegulatorParallelotope : Set (InfinitePlace F ⊕ S → ℝ) :=
  {y | ∃ t : Fin sRank(F, S) → ℝ, (∀ i, t i ∈ Ico (-1 / 2 : ℝ) (1 / 2)) ∧
    y = ∑ i, t i • sIdeleLog F S (unitAtS (bₛ i).toMul.out)}

/-- The logarithm on diagonal S-units, viewed as a homomorphism to an additive space. -/
private def sUnitLogHom : Oₛ(F, S)ˣ →* Multiplicative (InfinitePlace F ⊕ S → ℝ) where
  toFun u := Multiplicative.ofAdd (sIdeleLog F S (unitAtS u))
  map_one' := by
    change sIdeleLog F S (unitAtS 1) = 0
    rw [map_one]
    funext v
    rcases v with v | v
    · change (v.mult : ℝ) * Real.log ‖(1 : v.Completion)‖ = 0
      simp
    · change Real.log ‖(1 : v.val.adicCompletion F)‖ = 0
      simp
  map_mul' u w := by
    change sIdeleLog F S (unitAtS (u * w)) =
      sIdeleLog F S (unitAtS u) + sIdeleLog F S (unitAtS w)
    rw [map_mul]
    let g := unitAtS u
    let h := unitAtS w
    change sIdeleLog F S (g * h) = sIdeleLog F S g + sIdeleLog F S h
    funext v
    rcases v with v | v
    · have hne (a : (SAdeleRing F S)ˣ) : a.val.1 v ≠ 0 :=
        ((a.isUnit.map (RingHom.fst _ _)).map (Pi.evalRingHom _ v)).ne_zero
      change (v.mult : ℝ) * Real.log ‖g.val.1 v * h.val.1 v‖ =
        v.mult * Real.log ‖g.val.1 v‖ + v.mult * Real.log ‖h.val.1 v‖
      rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hne g)) (norm_ne_zero_iff.mpr (hne h)),
        mul_add]
    · have hne (a : (SAdeleRing F S)ˣ) : a.val.2 v ≠ 0 :=
        ((a.isUnit.map (RingHom.snd _ _)).map (Pi.evalRingHom _ v)).ne_zero
      change Real.log ‖g.val.2 v * h.val.2 v‖ =
        Real.log ‖g.val.2 v‖ + Real.log ‖h.val.2 v‖
      rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hne g)) (norm_ne_zero_iff.mpr (hne h))]

/-- Diagonal S-units with logarithms in a sufficiently small ball are finite in number. -/
private theorem sUnitLog_finite_near_zero :
    {u : Oₛ(F, S)ˣ | ‖sIdeleLog F S (unitAtS u)‖ ≤ Real.log 2 / 2}.Finite := by
  let value (u : Oₛ(F, S)ˣ) : F := u.val.val
  have hinj : Injective value := fun _ _ h ↦ Units.ext (Subtype.ext h)
  let r : ℝ := Real.log 2 / 2
  refine Set.Finite.of_finite_image ?_ hinj.injOn
  refine (Embeddings.finite_of_norm_le F ℂ (Real.exp r)).subset ?_
  rintro _ ⟨u, hu, rfl⟩
  have hne : value u ≠ 0 := (u.isUnit.map (Oₛ(F, S)).val).ne_zero
  have hcoord (v : InfinitePlace F ⊕ S) : sIdeleLog F S (unitAtS u) v ≤ r :=
    (le_abs_self _).trans ((norm_le_pi_norm (sIdeleLog F S (unitAtS u)) v).trans hu)
  refine ⟨?_, (InfinitePlace.le_iff_le (value u) (Real.exp r)).mp ?_⟩
  · -- At the selected finite places a norm less than two is at most one.
    have hval (v : HeightOneSpectrum (𝓞 F)) : v.valuation F (value u) ≤ 1 := by
      by_cases hv : v ∈ S
      · let x : v.adicCompletion F := algebraMap F _ (value u)
        have hxne : x ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hne
        have hxlog : Real.log ‖x‖ ≤ r := hcoord (Sum.inr ⟨v, hv⟩)
        have hxlt : ‖x‖ < 2 := (Real.log_lt_log_iff (norm_pos_iff.mpr hxne) (by norm_num)).mp
          (hxlog.trans_lt (by dsimp [r]; linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]))
        have hx : ‖x‖ ≤ 1 := le_of_not_gt fun h ↦
          (not_le_of_gt hxlt) (FinitePlace.two_le_norm_of_one_lt_norm (K := F) (v := v) x h)
        rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        exact Valued.toNormedField.norm_le_one_iff.mp hx
      · exact u.val.property v hv
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (value u) hval
    exact ha ▸ a.isIntegral_coe
  · intro v
    have hlog : (v.mult : ℝ) * Real.log (v (value u)) ≤ r := by
      have hv := hcoord (Sum.inl v)
      change (v.mult : ℝ) * Real.log ‖algebraMap F v.Completion (value u)‖ ≤ r at hv
      rw [InfinitePlace.coe_apply]
      simpa only [AbsoluteValue.Completion.algebraMap_def, AbsoluteValue.Completion.norm_coe,
        WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply, WithAbs.ofAbs_toAbs] using hv
    have hr : 0 ≤ r := div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
    have hm : (1 : ℝ) ≤ v.mult := by exact_mod_cast v.mult_pos
    apply (Real.log_le_iff_le_exp (v.pos_iff.mpr hne)).mp
    rw [mul_comm, ← le_div_iff₀ (lt_of_lt_of_le (by norm_num) hm)] at hlog
    exact hlog.trans (div_le_self hr hm)

/-- The logarithm vectors of a ℤ-basis of the S-units modulo torsion are linearly independent
over ℝ. A private lemma with the same statement stands in `AppA_AlgebraicNT/Sec2b.lean`. -/
theorem sUnitLog_basis_linearIndependent :
    LinearIndependent ℝ (fun i ↦ sIdeleLog F S (unitAtS (bₛ i).toMul.out)) := by
  let L := sUnitLogHom F S
  have hr : 0 < Real.log 2 / 2 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hfinite := sUnitLog_finite_near_zero F S
  -- The kernel is finite, and the target has no nontrivial torsion.
  have hker : L.ker = CommGroup.torsion Oₛ(F, S)ˣ := by
    have : Finite L.ker := Set.finite_coe_iff.mpr (hfinite.subset (fun u hu ↦ by
      change sIdeleLog F S (unitAtS u) = 0 at hu
      change ‖sIdeleLog F S (unitAtS u)‖ ≤ _
      rw [hu, norm_zero]
      exact hr.le))
    ext u
    constructor
    · intro hu
      exact (CommGroup.mem_torsion _).mpr
        (L.ker.subtype.isOfFinOrder (isOfFinOrder_of_finite (⟨u, hu⟩ : L.ker)))
    · intro hu
      exact (isOfFinOrder_iff_eq_one (L u)).mp (L.isOfFinOrder hu)
  let q := (QuotientGroup.kerLift L).comp (QuotientGroup.quotientMulEquivOfEq hker.symm).toMonoidHom
  let f := q.toAdditiveLeft.toIntLinearMap
  have hf : Injective f :=
    (QuotientGroup.kerLift_injective L).comp (QuotientGroup.quotientMulEquivOfEq hker.symm).injective
  have hmk (u : Oₛ(F, S)ˣ) :
      f (Additive.ofMul (QuotientGroup.mk u)) = sIdeleLog F S (unitAtS u) := rfl
  let v (i : Fin sRank(F, S)) := sIdeleLog F S (unitAtS (bₛ i).toMul.out)
  change LinearIndependent ℝ v
  have hv : f ∘ bₛ = v := by
    funext i
    have hi := hmk (bₛ i).toMul.out
    rw [show QuotientGroup.mk (bₛ i).toMul.out = (bₛ i).toMul from Quotient.out_eq' _] at hi
    exact hi
  have hli : LinearIndependent ℤ v := by
    rw [← hv]
    exact bₛ.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  have hspan : Submodule.span ℤ (Set.range v) = f.range := by
    rw [← hv, Set.range_comp, ← Submodule.map_span, bₛ.span_eq, Submodule.map_top]
  -- The finite intersection with a neighborhood of zero makes the range discrete.
  have hdisc : DiscreteTopology (Submodule.span ℤ (Set.range v)) := by
    rw [hspan]
    refine discreteTopology_of_isOpen_singleton_zero
      (isOpen_singleton_of_finite_mem_nhds 0 (s := Metric.closedBall 0 (Real.log 2 / 2))
        (Metric.closedBall_mem_nhds _ hr) ?_)
    refine Set.Finite.of_finite_image ?_ Subtype.val_injective.injOn
    refine (hfinite.image (fun u ↦ sIdeleLog F S (unitAtS u))).subset ?_
    rintro _ ⟨⟨_, ⟨a, rfl⟩⟩, ha, rfl⟩
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective a.toMul
    have heq : f a = sIdeleLog F S (unitAtS u) := by rw [← hmk, hu]; rfl
    refine ⟨u, ?_, heq.symm⟩
    rw [Metric.mem_closedBall, dist_zero_right] at ha
    change ‖f a‖ ≤ Real.log 2 / 2 at ha
    change ‖sIdeleLog F S (unitAtS u)‖ ≤ Real.log 2 / 2
    rwa [heq] at ha
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  rw [Real.finrank_eq_int_finrank_of_discrete hdisc]
  exact linearIndependent_iff_card_eq_finrank_span.mp hli

/-- Paper: (A.5.2.18), p. 575. Each basis logarithm contributes a half-open
interval on its own line in the centered parallelotope. -/
theorem centeredSRegulatorParallelotope_basis_line (i : Fin sRank(F, S)) (t : ℝ) :
    t • sIdeleLog F S (unitAtS (bₛ i).toMul.out) ∈ centeredSRegulatorParallelotope F S bₛ ↔
      t ∈ Ico (-1 / 2 : ℝ) (1 / 2) := by
  let v (j : Fin sRank(F, S)) := sIdeleLog F S (unitAtS (bₛ j).toMul.out)
  change (∃ c : Fin sRank(F, S) → ℝ, (∀ j, c j ∈ Ico (-1 / 2 : ℝ) (1 / 2)) ∧
      t • v i = ∑ j, c j • v j) ↔ _
  have hsingle : Fintype.linearCombination ℝ v (Pi.single i t) = t • v i :=
    Fintype.linearCombination_apply_single (R := ℝ) (v := v) i t
  constructor
  · rintro ⟨c, hc, heq⟩
    have hc_eq : Pi.single i t = c :=
      (sUnitLog_basis_linearIndependent F S bₛ).fintypeLinearCombination_injective
        (hsingle.trans heq)
    simpa only [← hc_eq, Pi.single_eq_same] using hc i
  · intro ht
    refine ⟨Pi.single i t, ?_, hsingle.symm⟩
    intro j
    by_cases h : j = i
    · simpa [h] using ht
    · rw [Pi.single_eq_of_ne h]
      norm_num


/-- Paper: (A.5.2.15)–(A.5.2.18), p. 575. The centered S-local domain is cut
out by the centered S-parallelotope and the centered angular sector at the chosen place. -/
def centeredSLocalIdeleDomain : Set Nₛ :=
  {g | sIdeleLog F S g.val ∈ centeredSRegulatorParallelotope F S bₛ ∧
    inCenteredTorsionSector F v₀ σ (atPlace (atInfinity g.val))}

/-- Paper: (A.5.2.15), p. 575. The identity S-idele belongs to the centered S-local domain. -/
theorem one_mem_centeredSLocalIdeleDomain :
    1 ∈ centeredSLocalIdeleDomain F v₀ σ S bₛ := by
  have hn : (0 : ℝ) < Units.torsionOrder F := by exact_mod_cast Units.torsionOrder_pos F
  have hlog : sIdeleLog F S 1 = 0 := by
    funext v
    rcases v with v | v
    · show (v.mult : ℝ) * Real.log ‖(1 : v.Completion)‖ = 0
      simp
    · show Real.log ‖(1 : v.val.adicCompletion F)‖ = 0
      simp
  refine ⟨⟨0, fun _ ↦ by norm_num, by simp [hlog]⟩, ?_⟩
  show (σ (extensionEmbedding v₀ (1 : v₀.Completion))).arg ∈ _
  rw [map_one, map_one, Complex.arg_one, Set.mem_Ico, neg_div]
  exact ⟨neg_nonpos.mpr (by positivity), by positivity⟩

section CenteredIntegralDomain

local notation "infiniteProjection" => Units.map (RingHom.toMonoidHom
  (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
local notation "fieldUnit" => Units.map (RingHom.toMonoidHom (algebraMap (𝓞 F) F))
local notation "diagonal" => IdeleGroup.unitEmbedding (𝓞 F) F
local notation "integralUnits" =>
  MonoidHom.range (Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside F ∅))))

/-- Multiplication by a unique root of unity puts the argument in the centered sector. -/
private theorem existsUnique_torsion_translate_centered_arg (φ : F →+* ℂ) (z : ℂˣ) :
    ∃! t : Units.torsion F,
      ((Units.complexEmbedding φ t.val).val * z.val).arg ∈
        Ico (-Real.pi / (Units.torsionOrder F : ℝ)) (Real.pi / (Units.torsionOrder F : ℝ)) := by
  let n := Units.torsionOrder F
  let p : ℝ := 2 * Real.pi / n
  let a : ℝ := -Real.pi / n
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Units.torsionOrder_pos F)
  have hn₂ : (2 : ℝ) ≤ n := by
    obtain ⟨m, hm⟩ := Units.even_torsionOrder F
    have := Units.torsionOrder_pos F
    exact_mod_cast (show 2 ≤ Units.torsionOrder F by omega)
  have hp : 0 < p := div_pos Real.two_pi_pos hn
  have hap : a + p = Real.pi / n := by
    dsimp [a, p]
    ring
  let θ := toIcoMod hp a z.val.arg
  have hθ : θ ∈ Ico a (Real.pi / n) := hap ▸ toIcoMod_mem_Ico hp a z.val.arg
  have hθ' : θ ∈ Ioc (-Real.pi) Real.pi := by
    have hbound : Real.pi / n < Real.pi := by
      rw [div_lt_iff₀ hn]
      nlinarith [Real.pi_pos]
    rw [show a = -(Real.pi / n) by simp [a, neg_div]] at hθ
    exact ⟨by linarith [hθ.1], hθ.2.le.trans hbound.le⟩
  let ξ := Complex.exp (((θ - z.val.arg : ℝ) : ℂ) * Complex.I)
  have hξpow : ξ ^ n = 1 := by
    dsimp only [ξ]
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨-toIcoDiv hp a z.val.arg, ?_⟩
    have hscale : (n : ℝ) * (θ - z.val.arg) =
        (-toIcoDiv hp a z.val.arg : ℤ) * (2 * Real.pi) := by
      dsimp only [θ]
      rw [toIcoMod_sub_self, zsmul_eq_mul]
      dsimp only [p]
      field_simp
    rw [← mul_assoc, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, hscale]
    push_cast
    ring
  let ζ : ℂˣ := Units.mk0 ξ (Complex.exp_ne_zero _)
  obtain ⟨t, ht, htζ⟩ : ζ ∈ (Units.torsion F).map (Units.complexEmbedding φ) := by
    rw [Units.map_complexEmbedding_torsion, mem_rootsOfUnity]
    exact Units.ext hξpow
  have htsector : ((Units.complexEmbedding φ t).val * z.val).arg ∈ Ico a (Real.pi / n) := by
    rw [htζ]
    change (ξ * z.val).arg ∈ _
    have hrot : ξ * z.val = (‖z.val‖ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z.val]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      simp only [Complex.ofReal_sub]
      ring
    rw [hrot, Complex.arg_real_mul _ (norm_pos_iff.mpr z.ne_zero), Complex.arg_exp_mul_I,
      (toIocMod_eq_self Real.two_pi_pos).mpr (by
        simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using hθ')]
    exact hθ
  refine ⟨⟨t, ht⟩, htsector, ?_⟩
  intro s hs
  let x := (Units.complexEmbedding φ s.val).val
  let y := (Units.complexEmbedding φ t).val
  have hpow (u : Units.torsion F) : (Units.complexEmbedding φ u.val).val ^ n = 1 := by
    simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun v ↦ (Units.complexEmbedding φ v).val) (Units.pow_torsionOrder_eq_one F u.prop)
  have hx : x ^ n = 1 := hpow s
  have hy : y ^ n = 1 := hpow ⟨t, ht⟩
  have hxy : (x * z.val) ^ n = (y * z.val) ^ n := by simp only [mul_pow, hx, hy, one_mul]
  have hang : (((n : ℝ) * (x * z.val).arg : ℝ) : Real.Angle) =
      (((n : ℝ) * (y * z.val).arg : ℝ) : Real.Angle) := by
    rw [Real.Angle.natCast_mul_eq_nsmul, Real.Angle.natCast_mul_eq_nsmul,
      ← Complex.arg_pow_coe_angle, ← Complex.arg_pow_coe_angle, hxy]
  have hmem (r : ℝ) (hr : r ∈ Ico a (Real.pi / n)) :
      (n : ℝ) * r ∈ Ico (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    have h₁ := (div_le_iff₀ hn).mp hr.1
    have h₂ := (lt_div_iff₀ hn).mp hr.2
    exact ⟨by linarith, by linarith⟩
  have harg := mul_left_cancel₀ hn.ne' (AddCircle.injOn_coe_Ico _ _
    (hmem _ hs) (hmem _ htsector) hang)
  have hnorm {w : ℂ} (hw : w ^ n = 1) : ‖w‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hw (Units.torsionOrder_ne_zero F)
  have hnorm' : ‖x * z.val‖ = ‖y * z.val‖ := by
    rw [norm_mul, norm_mul, hnorm hx, hnorm hy]
  exact Subtype.ext (Units.complexEmbedding_injective φ (Units.ext
    (mul_right_cancel₀ z.ne_zero (Complex.ext_norm_arg hnorm' harg))))

/-- A unique diagonal global unit puts the infinite logarithm and argument in the centered
parallelotope and sector, respectively. -/
private theorem centeredInfiniteIdeleDomain_unit_translate (g : (InfiniteAdeleRing F)ˣ) :
    ∃! u : (𝓞 F)ˣ,
      (fun w : {w : InfinitePlace F // w ≠ w₀} ↦
        infiniteIdeleLog F (infiniteProjection (diagonal (fieldUnit u)) * g) w.val) ∈
        centeredRegulatorParallelotope F b ∧
      inCenteredTorsionSector F v₀ σ (atPlace (infiniteProjection (diagonal (fieldUnit u)) * g)) := by
  classical
  let α := MonoidHom.comp infiniteProjection (MonoidHom.comp diagonal fieldUnit)
  let L (x : (InfiniteAdeleRing F)ˣ) : logSpace F := fun w ↦ infiniteIdeleLog F x w.val
  let ℓ (u : (𝓞 F)ˣ) := Units.logEmbedding F (Additive.ofMul u)
  have hℓ_mul (u v : (𝓞 F)ˣ) : ℓ (u * v) = ℓ u + ℓ v :=
    (Units.logEmbedding F).map_add (Additive.ofMul u) (Additive.ofMul v)
  have hℓ_inv (u : (𝓞 F)ˣ) : ℓ u⁻¹ = -ℓ u :=
    (Units.logEmbedding F).map_neg (Additive.ofMul u)
  have hshift (u : (𝓞 F)ˣ) (x : (InfiniteAdeleRing F)ˣ) : L (α u * x) = ℓ u + L x := by
    funext w
    change infiniteIdeleLog F (α u * x) w.val = ℓ u w + infiniteIdeleLog F x w.val
    dsimp only [ℓ]
    rw [infiniteIdeleLog_mul, Pi.add_apply, regulator_eq_infiniteIdeleLog F u w]
    rfl
  let s := ∑ i, (1 / 2 : ℝ) • Units.logEmbeddingQuot F (b i)
  have hbox (x : logSpace F) :
      x ∈ centeredRegulatorParallelotope F b ↔ s + x ∈ regulatorParallelotope F b := by
    simp only [centeredRegulatorParallelotope, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg,
      vadd_eq_add, s]
  -- First reduce the logarithm modulo the regulator lattice.
  obtain ⟨k, hk⟩ : ∃ k : (Units.logEmbedding F).range,
      s + L g ∈ k.val +ᵥ regulatorParallelotope F b := by
    apply Set.mem_iUnion.mp
    rw [regulatorParallelotope_cover]
    exact Set.mem_univ _
  obtain ⟨y, hy, heq⟩ := Set.mem_vadd_set.mp hk
  obtain ⟨a, ha⟩ := k.prop
  let u₀ := a.toMul⁻¹
  have hu₀ : s + L (α u₀ * g) ∈ regulatorParallelotope F b := by
    have heq' : ℓ a.toMul + y = s + L g := by
      change k.val + y = s + L g at heq
      rw [← ha] at heq
      exact heq
    rw [hshift, hℓ_inv, show s + (-ℓ a.toMul + L g) = y by
      rw [show s + (-ℓ a.toMul + L g) = -ℓ a.toMul + (s + L g) by abel, ← heq']
      abel]
    exact hy
  have htors (u : (𝓞 F)ˣ) (hu : L (α u * g) ∈ centeredRegulatorParallelotope F b) :
      u * u₀⁻¹ ∈ Units.torsion F := by
    let d : (Units.logEmbedding F).range := ⟨ℓ (u * u₀⁻¹), ⟨_, rfl⟩⟩
    have hdiff : d.val + (s + L (α u₀ * g)) = s + L (α u * g) := by
      change ℓ (u * u₀⁻¹) + (s + L (α u₀ * g)) = _
      rw [hℓ_mul, hℓ_inv, hshift, hshift]
      abel
    have hd : d = 0 := by
      by_contra hne
      exact (Set.disjoint_left.mp (regulatorParallelotope_disjoint F b d hne))
        (Set.mem_vadd_set.mpr ⟨_, hu₀, hdiff⟩) ((hbox _).mp hu)
    exact logEmbedding_eq_zero_iff.mp (congrArg Subtype.val hd)
  -- The remaining freedom is a torsion unit, which is fixed by the angular condition.
  let e := σ.toRingHom.comp (extensionEmbedding v₀)
  let φ := e.comp ((Pi.evalRingHom InfinitePlace.Completion v₀).comp
    (algebraMap F (InfiniteAdeleRing F)))
  let coord := (Units.map e.toMonoidHom).comp atPlace
  have hsector (t : (𝓞 F)ˣ) (x : (InfiniteAdeleRing F)ˣ) :
      inCenteredTorsionSector F v₀ σ (atPlace (α t * x)) ↔
        ((Units.complexEmbedding φ t).val * (coord x).val).arg ∈
          Ico (-Real.pi / (Units.torsionOrder F : ℝ)) (Real.pi / (Units.torsionOrder F : ℝ)) := by
    change (coord (α t * x)).val.arg ∈ _ ↔ _
    rw [map_mul, Units.val_mul]
    rfl
  obtain ⟨t, ht, ht_unique⟩ :=
    existsUnique_torsion_translate_centered_arg F φ (coord (α u₀ * g))
  refine ⟨t.val * u₀, ⟨?_, ?_⟩, ?_⟩
  · change L (α (t.val * u₀) * g) ∈ _
    apply (hbox _).mpr
    rw [hshift, hℓ_mul, show ℓ t.val = 0 from logEmbedding_eq_zero_iff.mpr t.prop,
      zero_add, ← hshift]
    exact hu₀
  · change inCenteredTorsionSector F v₀ σ (atPlace (α (t.val * u₀) * g))
    rw [map_mul α, mul_assoc]
    exact (hsector _ _).mpr ht
  · intro u hu
    have hu' : L (α u * g) ∈ centeredRegulatorParallelotope F b ∧
        inCenteredTorsionSector F v₀ σ (atPlace (α u * g)) := hu
    let t' : Units.torsion F := ⟨u * u₀⁻¹, htors u hu'.1⟩
    have hmul : t'.val * u₀ = u := inv_mul_cancel_right _ _
    have hangle : inCenteredTorsionSector F v₀ σ (atPlace (α t'.val * (α u₀ * g))) := by
      rw [← mul_assoc, ← map_mul, hmul]
      exact hu'.2
    have ht' : t' = t := ht_unique t' ((hsector _ _).mp hangle)
    rw [← hmul, ht']

/-- A principal idele is integral and invertible at all finite places exactly when
its defining field unit comes from a global unit. -/
private theorem principal_mem_integralUnits_iff (x : Fˣ) :
    diagonal x ∈ integralUnits ↔ x ∈ (MonoidHom.range fieldUnit) := by
  have hInt (y : F) :
      algebraMap F (AdeleRing (𝓞 F) F) y ∈ integralAdelesOutside F ∅ ↔
        y ∈ (algebraMap (𝓞 F) F).range := by
    rw [diagonal_mem_integralAdelesOutside, Finset.coe_empty, integer_empty, Algebra.mem_bot]
    rfl
  constructor
  · rintro ⟨a, ha⟩
    have hval : a.val.val = algebraMap F (AdeleRing (𝓞 F) F) x.val := congrArg Units.val ha
    have hinv : a.inv.val = algebraMap F (AdeleRing (𝓞 F) F) x.inv := congrArg Units.inv ha
    obtain ⟨y, hy⟩ := (hInt x.val).mp (hval ▸ a.val.property)
    obtain ⟨z, hz⟩ := (hInt x.inv).mp (hinv ▸ a.inv.property)
    let u : (𝓞 F)ˣ := ⟨y, z,
      (IsFractionRing.injective (𝓞 F) F) (by rw [map_mul, hy, hz, x.val_inv, map_one]),
      (IsFractionRing.injective (𝓞 F) F) (by rw [map_mul, hz, hy, x.inv_val, map_one])⟩
    exact ⟨u, Units.ext hy⟩
  · rintro ⟨u, rfl⟩
    let f := ((algebraMap F (AdeleRing (𝓞 F) F)).comp (algebraMap (𝓞 F) F)).codRestrict
      (integralAdelesOutside F ∅) (fun y ↦ (hInt _).mpr ⟨y, rfl⟩)
    exact ⟨Units.map f.toMonoidHom u, Units.ext rfl⟩

/-- The archimedean projection of a norm-one integral idele has norm one. -/
private theorem atInfinity_mem_ker_of_integral (g : N₁) (hg : g.val ∈ integralUnits) :
    infiniteProjection g.val ∈ N∞ := by
  classical
  have hfin (v : HeightOneSpectrum (𝓞 F)) : ‖g.val.val.2 v‖ = 1 := by
    obtain ⟨u, hu⟩ := hg
    let eval := (RestrictedProduct.evalRingHom
      (fun w : HeightOneSpectrum (𝓞 F) ↦ w.adicCompletion F) v).comp
        (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
    have hmem (a : integralAdelesOutside F ∅) : eval a.val ∈ v.adicCompletionIntegers F := by
      have ha := a.property
      simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
        true_implies] at ha
      exact ha v
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    apply (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := Units.map eval.toMonoidHom g.val)).mp
    rw [← hu]
    exact ⟨hmem u.val, hmem u.inv⟩
  let x := Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
    (infiniteProjection g.val)
  have hxfin (v : HeightOneSpectrum (𝓞 F)) : x.val.2 v = 1 := rfl
  change infiniteIdeleNorm F (infiniteProjection g.val) = 1
  rw [infiniteIdeleNorm_eq_global]
  change ideleNorm F x = 1
  apply Units.ext
  apply NNReal.coe_injective
  have hxinf : x.val.1 = g.val.val.1 := rfl
  rw [((ideleNorm_spec F).1 x).2, hxinf]
  simp only [hxfin, norm_one, finprod_one, mul_one, Units.val_one, NNReal.coe_one]
  have h := ((ideleNorm_spec F).1 g.val).2
  rw [show ideleNorm F g.val = 1 from g.prop] at h
  simpa only [hfin, finprod_one, mul_one, Units.val_one, NNReal.coe_one] using h.symm

/-- Paper: Lemma A.5.2.12(1), p. 575. The class-representative translates of
the centered integral domain meet every principal orbit in exactly one point. -/
theorem centeredIntegralIdeleDomain_fundamental
    (r : CommRing.Pic (𝓞 F) → N₁) (hr₁ : r 1 = 1)
    (hr : ∀ c, ideleIdealClass F (r c).val = c) (g : N₁) :
    ∃! a : Fˣ, (IdeleGroup.unitEmbedding (𝓞 F) F a)⁻¹ * g.val ∈
      (N₁).subtype '' (⋃ c, r c • centeredIntegralIdeleDomain F b v₀ σ) := by
  classical
  clear hr₁
  let d := MonoidHom.codRestrict diagonal N₁
    (fun a ↦ (ideleNorm_spec F).2 (Set.mem_range_self a))
  obtain ⟨e, he⟩ := (picard_uniformization F ∅).2.2.2
  let H := (IdeleGroup.principalSubgroup (𝓞 F) F ⊔ integralUnits).comap (N₁).subtype
  let q := QuotientGroup.mk' H
  let c := e (q g)
  have hq (a : Fˣ) : q (d a) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left (Set.mem_range_self a))
  have hq_int (x : N₁) (hx : x.val ∈ integralUnits) : q x = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_right hx)
  have hq_r : q (r c) = q g := e.injective ((he (r c)).trans (hr c))
  have hker : (g / r c).val ∈ IdeleGroup.principalSubgroup (𝓞 F) F ⊔ integralUnits := by
    change g / r c ∈ H
    apply (QuotientGroup.eq_one_iff (N := H) (g / r c)).mp
    change q (g / r c) = 1
    rw [map_div, hq_r, div_self']
  obtain ⟨_, ⟨a₀, rfl⟩, k, hk, hk_eq⟩ := Subgroup.mem_sup.mp hker
  have hk_norm : k ∈ N₁ := by
    rw [← div_eq_of_eq_mul' hk_eq.symm]
    exact Subgroup.div_mem N₁ (g / r c).prop (d a₀).prop
  let k₁ : N₁ := ⟨k, hk_norm⟩
  have hg : g = r c * (d a₀ * k₁) := by
    exact (eq_mul_of_div_eq (Subtype.ext hk_eq.symm)).trans (mul_comm _ _)
  obtain ⟨u, hu, hu_unique⟩ :=
    centeredInfiniteIdeleDomain_unit_translate F b v₀ σ (infiniteProjection k)
  let a := a₀ / fieldUnit u
  let x := d (fieldUnit u) * k₁
  have hx_int : x.val ∈ integralUnits :=
    Subgroup.mul_mem integralUnits ((principal_mem_integralUnits_iff F _).mpr (Set.mem_range_self u)) hk
  have hx : x ∈ centeredIntegralIdeleDomain F b v₀ σ := by
    refine ⟨hx_int, ⟨⟨infiniteProjection x.val, atInfinity_mem_ker_of_integral F x hx_int⟩, ?_, rfl⟩⟩
    have heq : infiniteProjection x.val =
        infiniteProjection (diagonal (fieldUnit u)) * infiniteProjection k :=
      map_mul infiniteProjection _ _
    change (fun w : {w : InfinitePlace F // w ≠ w₀} ↦
      infiniteIdeleLog F (infiniteProjection x.val) w.val) ∈ centeredRegulatorParallelotope F b ∧
        inCenteredTorsionSector F v₀ σ (atPlace (infiniteProjection x.val))
    rw [heq]
    exact hu
  have htrans : (d a)⁻¹ * g = r c * x := by
    have hd : (d a)⁻¹ * d a₀ = d (fieldUnit u) := by
      dsimp only [a]
      rw [map_div, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [hg, mul_left_comm (d a)⁻¹ (r c), ← mul_assoc (d a)⁻¹, hd]
  refine ⟨a, ⟨r c * x, Set.mem_iUnion.mpr ⟨c, Set.mem_smul_set.mpr ⟨x, hx, rfl⟩⟩,
    congrArg Subtype.val htrans.symm⟩, ?_⟩
  rintro a' ⟨y, hy, hy_eq⟩
  obtain ⟨c', hc'⟩ := Set.mem_iUnion.mp hy
  obtain ⟨x', hx', rfl⟩ := Set.mem_smul_set.mp hc'
  have hy' : r c' * x' = (d a')⁻¹ * g := Subtype.ext hy_eq
  have hc_eq : c' = c := by
    have hqy := congrArg q hy'
    rw [map_mul, hq_int x' hx'.1, mul_one, map_mul, map_inv, hq, inv_one, one_mul] at hqy
    exact (hr c').symm.trans ((he (r c')).symm.trans (congrArg e hqy))
  subst c'
  have hx_eq : x' = d (a₀ / a') * k₁ := by
    apply mul_left_cancel (a := r c)
    rw [hy', hg, mul_left_comm (d a')⁻¹ (r c), ← mul_assoc (d a')⁻¹, map_div, div_eq_mul_inv,
      mul_comm (d a₀) (d a')⁻¹]
  have ha'_int : diagonal (a₀ / a') ∈ integralUnits := by
    have h : diagonal (a₀ / a') = x'.val / k := by
      rw [hx_eq]
      change _ = diagonal (a₀ / a') * k / k
      exact (mul_div_cancel_right _ _).symm
    rw [h]
    exact Subgroup.div_mem integralUnits hx'.1 hk
  obtain ⟨u', hu'⟩ := (principal_mem_integralUnits_iff F _).mp ha'_int
  have hu'_dom : d (fieldUnit u') * k₁ ∈ centeredIntegralIdeleDomain F b v₀ σ := by
    rw [hu', ← hx_eq]
    exact hx'
  obtain ⟨z, hz, hz_eq⟩ := hu'_dom.2
  have hu'_eq : u' = u := by
    apply hu_unique
    have hz_eq' : z.val = infiniteProjection (diagonal (fieldUnit u')) * infiniteProjection k :=
      hz_eq.trans (map_mul infiniteProjection _ _)
    simpa only [centeredInfiniteIdeleDomain, Set.mem_ofPred_eq, hz_eq'] using hz
  rw [hu'_eq] at hu'
  dsimp only [a]
  rw [hu']
  simp

end CenteredIntegralDomain

/-- The S-idele logarithm sends multiplication to addition. -/
private theorem sIdeleLog_mul (x y : (SAdeleRing F S)ˣ) :
    sIdeleLog F S (x * y) = sIdeleLog F S x + sIdeleLog F S y := by
  funext v
  rcases v with v | v
  · change infiniteIdeleLog F (atInfinity (x * y)) v =
      infiniteIdeleLog F (atInfinity x) v + infiniteIdeleLog F (atInfinity y) v
    rw [map_mul, infiniteIdeleLog_mul]
    rfl
  · have hne (a : (SAdeleRing F S)ˣ) : a.val.2 v ≠ 0 :=
      ((a.isUnit.map (RingHom.snd _ _)).map (Pi.evalRingHom _ v)).ne_zero
    change Real.log ‖x.val.2 v * y.val.2 v‖ =
      Real.log ‖x.val.2 v‖ + Real.log ‖y.val.2 v‖
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hne x)) (norm_ne_zero_iff.mpr (hne y))]

/-- Translating a norm-one S-idele into the centered log box determines the
translating S-unit up to torsion. -/
private theorem exists_centeredSLog_translate (g : Nₛ) :
    ∃ a : Oₛ(F, S)ˣ,
      sIdeleLog F S ((unitAtS a)⁻¹ * g.val) ∈ centeredSRegulatorParallelotope F S bₛ ∧
      ∀ u : Oₛ(F, S)ˣ,
        sIdeleLog F S ((unitAtS u)⁻¹ * g.val) ∈ centeredSRegulatorParallelotope F S bₛ →
        a⁻¹ * u ∈ CommGroup.torsion Oₛ(F, S)ˣ := by
  classical
  let L := sUnitLogHom F S
  let T := CommGroup.torsion Oₛ(F, S)ˣ
  let q := QuotientGroup.lift T L (fun _ hu ↦ (L.isOfFinOrder hu).eq_one')
  let f := q.toAdditiveLeft.toIntLinearMap
  let v (i : Fin sRank(F, S)) := sIdeleLog F S (unitAtS (bₛ i).toMul.out)
  let coord (u : Oₛ(F, S)ˣ) := bₛ.equivFun (Additive.ofMul (QuotientGroup.mk u))
  let B := Fintype.linearCombination ℝ v
  have hv (i : Fin sRank(F, S)) : f (bₛ i) = v i := by
    have h : f (Additive.ofMul (QuotientGroup.mk (bₛ i).toMul.out)) = v i := rfl
    rw [show QuotientGroup.mk (bₛ i).toMul.out = (bₛ i).toMul from Quotient.out_eq' _] at h
    exact h
  have hunit (u : Oₛ(F, S)ˣ) :
      sIdeleLog F S (unitAtS u) = B (fun i ↦ (coord u i : ℝ)) := by
    have h := congrArg f (bₛ.sum_equivFun (Additive.ofMul (QuotientGroup.mk u)))
    change f (Additive.ofMul (QuotientGroup.mk u)) =
      Fintype.linearCombination ℝ v (fun i ↦ (bₛ.equivFun (Additive.ofMul (QuotientGroup.mk u)) i : ℝ))
    simpa only [map_sum, map_zsmul, hv, Fintype.linearCombination_apply, Int.cast_smul_eq_zsmul]
      using h.symm
  have hshift (u : Oₛ(F, S)ˣ) :
      sIdeleLog F S ((unitAtS u)⁻¹ * g.val) = sIdeleLog F S g.val - sIdeleLog F S (unitAtS u) := by
    rw [← map_inv, sIdeleLog_mul]
    have h : sIdeleLog F S (unitAtS u⁻¹) = -sIdeleLog F S (unitAtS u) := map_inv L u
    rw [h, sub_eq_add_neg, add_comm]
  -- The independent basis logarithms span the hyperplane because their count is its dimension.
  let sum : (InfinitePlace F ⊕ S → ℝ) →ₗ[ℝ] ℝ := ∑ j, LinearMap.proj j
  have hsum (x : InfinitePlace F ⊕ S → ℝ) : sum x = ∑ j, x j := by
    simp [sum, LinearMap.sum_apply]
  have hzero (x : Nₛ) : sum (sIdeleLog F S x.val) = 0 := by
    rw [hsum, sIdeleLog_sum, MonoidHom.mem_ker.mp x.property]
    simp
  have hspan : B.range = sum.ker := by
    have hsurj : Surjective sum := by
      intro x
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
      refine ⟨Pi.single (Sum.inl w : InfinitePlace F ⊕ S) x, ?_⟩
      simp [hsum]
    have hdim := sum.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, Module.finrank_pi,
      Fintype.card_sum, Fintype.card_coe] at hdim
    rw [Fintype.range_linearCombination]
    apply Submodule.eq_of_le_of_finrank_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact LinearMap.mem_ker.mpr (hzero ⟨_, (sIdeleNorm_spec F S).2 ⟨_, rfl⟩⟩)
    · have hdim' : Fintype.card (Fin sRank(F, S)) =
          Module.finrank ℝ (Submodule.span ℝ (range v)) :=
        linearIndependent_iff_card_eq_finrank_span.mp (sUnitLog_basis_linearIndependent F S bₛ)
      rw [← hdim', Fintype.card_fin]
      omega
  obtain ⟨x, hx⟩ := hspan.symm ▸ (LinearMap.mem_ker.mpr (hzero g) :
    sIdeleLog F S g.val ∈ sum.ker)
  have hB : Injective B := (sUnitLog_basis_linearIndependent F S bₛ).fintypeLinearCombination_injective
  have hbox (u : Oₛ(F, S)ˣ) :
      sIdeleLog F S ((unitAtS u)⁻¹ * g.val) ∈ centeredSRegulatorParallelotope F S bₛ ↔
      ∀ i, x i - (coord u i : ℝ) ∈ Ico (-1 / 2 : ℝ) (1 / 2) := by
    rw [hshift, hunit, ← hx, ← map_sub]
    change (∃ t, (∀ i, t i ∈ Ico (-1 / 2 : ℝ) (1 / 2)) ∧
      B (x - fun i ↦ (coord u i : ℝ)) = B t) ↔ _
    constructor
    · rintro ⟨t, ht, heq⟩
      rw [← hB heq] at ht
      exact ht
    · exact fun h ↦ ⟨_, h, rfl⟩
  -- Round each coordinate into the half-open interval of length one.
  let k (i : Fin sRank(F, S)) := toIcoDiv (p := (1 : ℝ)) zero_lt_one (-1 / 2) (x i)
  have hround (u : Oₛ(F, S)ˣ) :
      sIdeleLog F S ((unitAtS u)⁻¹ * g.val) ∈ centeredSRegulatorParallelotope F S bₛ ↔
      coord u = k := by
    rw [hbox, funext_iff]
    apply forall_congr' fun i ↦ ?_
    rw [eq_comm (a := coord u i)]
    simpa only [k, zsmul_eq_mul, mul_one, show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] using
        (toIcoDiv_eq_iff (p := (1 : ℝ)) (n := coord u i) (a := -1 / 2)
          (b := x i) zero_lt_one).symm
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (bₛ.equivFun.symm k).toMul
  have hka : coord a = k := by
    change bₛ.equivFun (Additive.ofMul (QuotientGroup.mk a)) = _
    rw [ha]
    exact bₛ.equivFun.apply_symm_apply k
  refine ⟨a, (hround a).mpr hka, fun u hu ↦ QuotientGroup.eq.mp ?_⟩
  exact congrArg Additive.toMul (bₛ.equivFun.injective (hka.trans ((hround u).mp hu).symm))

/-- The centered angular sector chooses a unique torsion translation of each S-idele. -/
private theorem existsUnique_centeredSTorsion_translate (g : (SAdeleRing F S)ˣ) :
    ∃! u : CommGroup.torsion Oₛ(F, S)ˣ,
      inCenteredTorsionSector F v₀ σ (atPlace (atInfinity ((unitAtS u.val)⁻¹ * g))) := by
  let coord : (SAdeleRing F S)ˣ →* ℂˣ :=
    (Units.map (σ.toRingHom.comp (extensionEmbedding v₀)).toMonoidHom).comp
      ((atPlace).comp atInfinity)
  let φ : F →+* ℂ :=
    σ.toRingHom.comp ((extensionEmbedding v₀).comp (algebraMap F v₀.Completion))
  let e := coord.comp unitAtS
  let T := CommGroup.torsion Oₛ(F, S)ˣ
  let n := Units.torsionOrder F
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (Units.torsionOrder_pos F)
  have he : Injective e := by
    intro a b hab
    exact Units.ext (Subtype.ext (φ.injective (congrArg Units.val hab)))
  have himage : T.map e = rootsOfUnity n ℂ := by
    change (CommGroup.torsion Oₛ(F, S)ˣ).map e = _
    rw [← sUnit_torsion_eq_image F S, Subgroup.map_map,
      show e.comp (Units.map (algebraMap (𝓞 F) Oₛ(F, S)).toMonoidHom) =
        Units.complexEmbedding φ from MonoidHom.ext fun _ ↦ Units.ext rfl,
      Units.map_complexEmbedding_torsion]
  let p : ℝ := 2 * Real.pi / n
  let lower : ℝ := -Real.pi / n
  have hp : 0 < p := div_pos Real.two_pi_pos hn
  have hright : lower + p = Real.pi / n := by dsimp [lower, p]; ring
  have hbound : Real.pi / n < Real.pi := by
    have hn₂ : (2 : ℝ) ≤ n := by
      obtain ⟨m, hm⟩ := Units.even_torsionOrder F
      have := Units.torsionOrder_pos F
      exact_mod_cast (by omega : 2 ≤ Units.torsionOrder F)
    exact (div_lt_iff₀ hn).mpr (by nlinarith [Real.pi_pos])
  let z : ℂ := (coord g).val
  obtain ⟨k, hk, -⟩ := existsUnique_add_zsmul_mem_Ico hp z.arg lower
  let w := Complex.exp ((p : ℂ) * Complex.I)
  have hw : w ^ n = 1 := by
    simpa [w, p, div_mul_eq_mul_div] using
      (Complex.isPrimitiveRoot_exp n (Units.torsionOrder_ne_zero F)).pow_eq_one
  let ζ : ℂˣ := Units.mk0 w (Complex.exp_ne_zero _)
  have hζ : ζ ∈ rootsOfUnity n ℂ := (mem_rootsOfUnity' n ζ).mpr hw
  obtain ⟨u, hu, hmap⟩ := himage ▸ hζ
  let a : T := (⟨u, hu⟩ : T) ^ (-k)
  have hrotate : w ^ k * z =
      (‖z‖ : ℂ) * Complex.exp (((z.arg + k • p : ℝ) : ℂ) * Complex.I) := by
    calc
      _ = w ^ k * ((‖z‖ : ℂ) * Complex.exp ((z.arg : ℂ) * Complex.I)) :=
        congrArg (w ^ k * ·) (Complex.norm_mul_exp_arg_mul_I z).symm
      _ = _ := by
        dsimp only [w]
        rw [← Complex.exp_int_mul, zsmul_eq_mul]
        push_cast
        rw [add_mul, Complex.exp_add, mul_assoc (k : ℂ) (p : ℂ) Complex.I]
        ring
  have ha : inCenteredTorsionSector F v₀ σ (atPlace (atInfinity ((unitAtS a.val)⁻¹ * g))) := by
    change (coord ((unitAtS a.val)⁻¹ * g)).val.arg ∈ Ico lower (Real.pi / n)
    rw [← hright, map_mul, map_inv]
    change ((e (u ^ (-k)))⁻¹ * coord g).val.arg ∈ _
    rw [map_zpow, hmap, zpow_neg, inv_inv, Units.val_mul,
      Units.val_zpow_eq_zpow_val]
    change (w ^ k * z).arg ∈ _
    rw [hrotate, Complex.arg_real_mul _ (norm_pos_iff.mpr (coord g).ne_zero),
      Complex.arg_exp_mul_I, (toIocMod_eq_self Real.two_pi_pos).mpr]
    · exact hk
    · rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
      exact ⟨(neg_lt_neg hbound).trans_le (by simpa only [lower, neg_div] using hk.1),
        hk.2.le.trans (hright.trans_le hbound.le)⟩
  refine ⟨a, ha, fun b hb ↦ ?_⟩
  let x : ℂˣ := (e a.val)⁻¹ * coord g
  let y : ℂˣ := (e b.val)⁻¹ * coord g
  have hsector (t : T) :
      inCenteredTorsionSector F v₀ σ (atPlace (atInfinity ((unitAtS t.val)⁻¹ * g))) ↔
        ((e t.val)⁻¹ * coord g).val.arg ∈ Ico lower (Real.pi / n) := by
    change (coord ((unitAtS t.val)⁻¹ * g)).val.arg ∈ Ico lower (Real.pi / n) ↔ _
    rw [map_mul, map_inv]
    rfl
  -- The n-th power is constant on each torsion orbit and injective on the sector.
  have hpow (t : T) : (e t.val).val ^ n = 1 :=
    (mem_rootsOfUnity' n _).mp (himage ▸ ⟨t.val, t.property, rfl⟩)
  have hpow' (t : T) : (((e t.val)⁻¹ * coord g).val : ℂ) ^ n = z ^ n := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_pow, inv_pow, hpow, inv_one, one_mul]
  have hxy : x.val ^ n = y.val ^ n := (hpow' a).trans (hpow' b).symm
  have hnorm : ‖x.val‖ = ‖y.val‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (Units.torsionOrder_ne_zero F)).mp
      (by simpa only [norm_pow] using congrArg norm hxy)
  have hangle : (((n : ℝ) * x.val.arg : ℝ) : Real.Angle) =
      (((n : ℝ) * y.val.arg : ℝ) : Real.Angle) := by
    rw [Real.Angle.natCast_mul_eq_nsmul, Real.Angle.natCast_mul_eq_nsmul,
      ← Complex.arg_pow_coe_angle, ← Complex.arg_pow_coe_angle, hxy]
  have hmem (t : ℝ) (ht : t ∈ Ico lower (Real.pi / n)) :
      (n : ℝ) * t ∈ Ico (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
    exact ⟨by simpa only [mul_comm (n : ℝ) t] using (div_le_iff₀ hn).mp ht.1,
      by simpa only [mul_comm (n : ℝ) t] using (lt_div_iff₀ hn).mp ht.2⟩
  have harg : x.val.arg = y.val.arg :=
    mul_left_cancel₀ hn.ne' (AddCircle.injOn_coe_Ico (2 * Real.pi) (-Real.pi)
      (hmem x.val.arg ((hsector a).mp ha)) (hmem y.val.arg ((hsector b).mp hb)) hangle)
  have hxy' : x = y := Units.ext (Complex.ext_norm_arg hnorm harg)
  exact Subtype.ext (he (inv_injective (mul_right_cancel hxy'.symm)))

/-- Paper: Lemma A.5.2.12(2), p. 575. The centered S-local domain meets each
orbit of the diagonal S-units in the norm-one S-ideles in exactly one point. -/
theorem centeredSLocalIdeleDomain_fundamental
    (g : Nₛ) :
    ∃! a : Oₛ(F, S)ˣ, (unitAtS a)⁻¹ * g.val ∈
      (Nₛ).subtype '' centeredSLocalIdeleDomain F v₀ σ S bₛ := by
  let T := CommGroup.torsion Oₛ(F, S)ˣ
  let L := sUnitLogHom F S
  let move (a : Oₛ(F, S)ˣ) : (SAdeleRing F S)ˣ := (unitAtS a)⁻¹ * g.val
  let inLogBox (x : (SAdeleRing F S)ˣ) : Prop :=
    sIdeleLog F S x ∈ centeredSRegulatorParallelotope F S bₛ
  let inSector (x : (SAdeleRing F S)ˣ) : Prop :=
    inCenteredTorsionSector F v₀ σ (atPlace (atInfinity x))
  have hmem (a : Oₛ(F, S)ˣ) :
      move a ∈ (Nₛ).subtype '' centeredSLocalIdeleDomain F v₀ σ S bₛ ↔
        inLogBox (move a) ∧ inSector (move a) := by
    constructor
    · rintro ⟨x, hx, heq⟩
      change x.val = move a at heq
      change inLogBox x.val ∧ inSector x.val at hx
      exact heq ▸ hx
    · intro h
      have hn : move a ∈ Nₛ :=
        (Nₛ).mul_mem ((Nₛ).inv_mem ((sIdeleNorm_spec F S).2 ⟨a, rfl⟩)) g.property
      exact ⟨⟨move a, hn⟩, h, rfl⟩
  change ∃! a : Oₛ(F, S)ˣ, move a ∈ _
  apply (existsUnique_congr hmem).mpr
  obtain ⟨a, ha, han⟩ := exists_centeredSLog_translate F S bₛ g
  obtain ⟨t, ht, huniq⟩ := existsUnique_centeredSTorsion_translate F v₀ σ S (move a)
  have hshift (u : T) : move (a * u.val) = (unitAtS u.val)⁻¹ * move a := by
    change (unitAtS (a * u.val))⁻¹ * g.val = (unitAtS u.val)⁻¹ * ((unitAtS a)⁻¹ * g.val)
    simp only [map_mul, mul_inv_rev, mul_assoc]
  have hlog : inLogBox (move (a * t.val)) := by
    have hzero : sIdeleLog F S ((unitAtS t.val)⁻¹) = 0 := by
      rw [← map_inv]
      exact (L.isOfFinOrder (T.inv_mem t.property)).eq_one'
    change sIdeleLog F S (move (a * t.val)) ∈ _
    rw [hshift, sIdeleLog_mul, hzero, zero_add]
    exact ha
  have hsector : inSector (move (a * t.val)) := (congrArg inSector (hshift t)).mpr ht
  refine ⟨a * t.val, ⟨hlog, hsector⟩, fun b hb ↦ ?_⟩
  let u : T := ⟨a⁻¹ * b, han b hb.1⟩
  have hu : a * u.val = b := mul_inv_cancel_left a b
  have hsector' : inSector ((unitAtS u.val)⁻¹ * move a) :=
    (congrArg inSector ((hshift u).symm.trans (congrArg move hu))).mpr hb.2
  calc
    b = a * u.val := hu.symm
    _ = a * t.val := congrArg (fun x : T ↦ a * x.val) (huniq u hsector')

-- TODO(paper-gap): Lemma A.5.2.12(3) omits the outside-S unit factor from the domain.
-- For ℚ with S = {∞}, a tuple with archimedean component 1 and nontrivial outside unit
-- component cannot be moved into the embedded B_F,S¹ by a diagonal unit.
-- The prescribed ideal-class representatives also have trivial S-ideal class.

/-- Paper: Lemma A.5.2.13(1), p. 576. The interior of the centered archimedean
domain contains the identity and is therefore a neighborhood of it. -/
theorem interior_centeredInfiniteIdeleDomain_mem_nhds :
    interior (centeredInfiniteIdeleDomain F b v₀ σ) ∈ 𝓝 (1 : N∞) := by
  classical
  let B := (b.map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ (Units.unitLattice F)
  have hB (i : Fin (Units.rank F)) : Units.logEmbeddingQuot F (b i) = B i := by
    rw [Module.Basis.ofZLatticeBasis_apply]
    rfl
  let p (g : N∞) : logSpace F := fun w ↦ infiniteIdeleLog F g.val w.val
  have hp : Continuous p := continuous_pi fun w ↦
    (continuous_apply w.val).comp ((infiniteIdeleLog_continuous F).comp continuous_subtype_val)
  have hp₁ : p 1 = 0 := by
    funext w
    change (w.val.mult : ℝ) * Real.log ‖(1 : w.val.Completion)‖ = 0
    simp
  let s : logSpace F := ∑ i, (1 / 2 : ℝ) • B i
  let c (g : N∞) := B.equivFun (s + p g)
  have hc : Continuous c :=
    B.equivFun.toLinearMap.continuous_of_finiteDimensional.comp (continuous_const.add hp)
  have hc₁ (i : Fin (Units.rank F)) : c 1 i = 1 / 2 := by
    simp only [c, hp₁, add_zero, Module.Basis.equivFun_apply, s, B.repr_sum_self]
  have hlog : ∀ᶠ g in 𝓝 (1 : N∞), p g ∈ centeredRegulatorParallelotope F b := by
    let U : Set (Fin (Units.rank F) → ℝ) := Set.pi univ fun _ ↦ Ioo 0 1
    have hU : IsOpen U := isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo
    have hU₁ : c 1 ∈ U := by
      intro i _
      rw [hc₁]
      norm_num
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hU.mem_nhds hU₁)] with g hg
    simp only [centeredRegulatorParallelotope, hB]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add]
    change s + p g ∈ ZSpan.fundamentalDomain B
    rw [ZSpan.mem_fundamentalDomain, ← Module.Basis.equivFun_apply]
    exact fun i ↦ Ioo_subset_Ico_self (hg i (mem_univ i))
  let z (g : N∞) := σ (extensionEmbedding v₀ (g.val.val v₀))
  have hz : Continuous z :=
    σ.toLinearMap.continuous_of_finiteDimensional.comp
      ((isometry_extensionEmbedding v₀).continuous.comp
        ((continuous_apply v₀).comp (Units.continuous_val.comp continuous_subtype_val)))
  have hz₁ : z 1 = 1 := by
    change σ (extensionEmbedding v₀ 1) = 1
    simp
  have harg : ContinuousAt (fun g : N∞ ↦ (z g).arg) 1 :=
    (Complex.continuousAt_arg (by rw [hz₁]; exact Complex.one_mem_slitPlane)).comp
      hz.continuousAt
  let a := Real.pi / (Units.torsionOrder F : ℝ)
  have ha : 0 < a := div_pos Real.pi_pos (by exact_mod_cast Units.torsionOrder_pos F)
  have hangle : Ioo (-a) a ∈ 𝓝 ((z 1).arg) := by
    rw [hz₁, Complex.arg_one]
    exact isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr ha, ha⟩
  apply interior_mem_nhds.mpr
  filter_upwards [hlog, harg.preimage_mem_nhds hangle] with g hg hangle'
  refine ⟨hg, ?_⟩
  change (z g).arg ∈ Ico (-Real.pi / _) _
  rw [neg_div]
  exact Ioo_subset_Ico_self hangle'

/-- The norm of an infinite idele is the exponential of the sum of its logarithms. -/
private theorem infiniteIdeleNorm_eq_exp_sum_log (g : 𝕀∞) :
    ((infiniteIdeleNorm F g).val : ℝ) = Real.exp (∑ v, infiniteIdeleLog F g v) := by
  simp only [infiniteIdeleNorm, MonoidHom.finsetProd_apply, Units.coe_prod, MonoidHom.pow_apply,
    NNReal.coe_prod]
  change (∏ v : InfinitePlace F, ‖g.val v‖ ^ v.mult) = _
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro v _
  have hne : g.val v ≠ 0 := (Units.map (Pi.evalRingHom InfinitePlace.Completion v).toMonoidHom
    g).ne_zero
  rw [infiniteIdeleLog, Real.exp_nat_mul, Real.exp_log (norm_pos_iff.mpr hne)]

/-- On norm-one infinite ideles the logarithms with one place omitted form an open map. -/
private theorem isOpenMap_infiniteIdeleLog_omit :
    IsOpenMap (fun g : N∞ ↦ (fun w : {w : InfinitePlace F // w ≠ w₀} ↦
      infiniteIdeleLog F g.val w.val) : N∞ → logSpace F) := by
  classical
  let L : N∞ →* Multiplicative (logSpace F) :=
    MonoidHom.mk' (fun g ↦ Multiplicative.ofAdd (fun w ↦ infiniteIdeleLog F g.val w.val))
      (fun g h ↦ congrArg (fun l : InfinitePlace F → ℝ ↦
        Multiplicative.ofAdd (fun w : {w : InfinitePlace F // w ≠ w₀} ↦ l w.val))
        (infiniteIdeleLog_mul F g.val h.val))
  have hcont : Continuous L := continuous_pi fun w ↦
    (continuous_apply w.val).comp ((infiniteIdeleLog_continuous F).comp continuous_subtype_val)
  have hsurj : Surjective L := by
    intro x
    -- Restore the omitted coordinate so the full logarithm sums to zero.
    let y (v : InfinitePlace F) := if hv : v = w₀ then -∑ w, x.toAdd w else x.toAdd ⟨v, hv⟩
    have hy (v : {w : InfinitePlace F // w ≠ w₀}) : y v.val = x.toAdd v := dite_eq_right v.property
    obtain ⟨g, hg⟩ := infiniteIdeleLog_surjective F y
    have hs : ∑ v, y v = 0 := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
      simp only [hy]
      simp [y]
    have hn : infiniteIdeleNorm F g = 1 := by
      apply Units.ext
      apply NNReal.coe_injective
      rw [infiniteIdeleNorm_eq_exp_sum_log, hg, hs, Real.exp_zero]
      rfl
    refine ⟨⟨g, hn⟩, congrArg Multiplicative.ofAdd (funext fun v ↦ ?_)⟩
    exact (congrFun hg v.val).trans (hy v)
  have : SigmaCompactSpace 𝕀∞ :=
    ⟨⟨fun n ↦ infiniteIdeleLog F ⁻¹' compactCovering (InfinitePlace F → ℝ) n,
      fun n ↦ (infiniteIdeleLog_proper F).isCompact_preimage (isCompact_compactCovering _ n),
      by rw [← preimage_iUnion, iUnion_compactCovering, preimage_univ]⟩⟩
  have : SigmaCompactSpace N∞ := (infiniteIdeleNorm_ker_closed F).sigmaCompactSpace
  exact L.isOpenMap_of_sigmaCompact hsurj hcont

/-- Interior points of the centered domain have arguments strictly inside the angular sector. -/
private theorem arg_mem_Ioo_of_mem_interior_centeredInfiniteIdeleDomain
    (g : N∞) (hg : g ∈ interior (centeredInfiniteIdeleDomain F b v₀ σ)) :
    (σ (extensionEmbedding v₀ (g.val.val v₀))).arg ∈
      Ioo (-(Real.pi / (Units.torsionOrder F : ℝ))) (Real.pi / (Units.torsionOrder F : ℝ)) := by
  classical
  let a := Real.pi / (Units.torsionOrder F : ℝ)
  have hn : (0 : ℝ) < Units.torsionOrder F := Nat.cast_pos.mpr (Units.torsionOrder_pos F)
  have ha : 0 < a := div_pos Real.pi_pos hn
  have hπ : a < Real.pi := by
    have hn₂ : (2 : ℝ) ≤ Units.torsionOrder F := by
      obtain ⟨m, hm⟩ := Units.even_torsionOrder F
      have := Units.torsionOrder_pos F
      exact_mod_cast (show 2 ≤ Units.torsionOrder F by omega)
    exact (div_lt_iff₀ hn).mpr (by nlinarith [Real.pi_pos])
  let z (x : N∞) := σ (extensionEmbedding v₀ (x.val.val v₀))
  have hsector (x : N∞) (hx : x ∈ centeredInfiniteIdeleDomain F b v₀ σ) :
      (z x).arg ∈ Ico (-a) a := by
    have hang : (z x).arg ∈ Ico (-Real.pi / (Units.torsionOrder F : ℝ)) a := hx.2
    simpa only [neg_div] using hang
  have hangle := hsector g (interior_subset hg)
  change (z g).arg ∈ Ioo (-a) a
  by_cases hv : v₀.IsReal
  · have hpos := (inCenteredTorsionSector_real F v₀ σ hv _).mp (interior_subset hg).2
    change 0 < extensionEmbeddingOfIsReal hv (g.val.val v₀) at hpos
    have hz : (z g).arg = 0 := by
      dsimp only [z]
      rw [← extensionEmbeddingOfIsReal_apply hv]
      have hσ (y : ℝ) : σ (y : ℂ) = (y : ℂ) := σ.commutes y
      rw [hσ, Complex.arg_ofReal_of_nonneg hpos.le]
    rw [hz]
    exact ⟨neg_lt_zero.mpr ha, ha⟩
  · -- Vary the argument at the chosen place while keeping every local norm fixed.
    let e := isometryEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp hv)
    let p (t : ℝ) := (‖z g‖ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)
    let q (t : ℝ) := e.symm (σ.symm (p t))
    have hp : Continuous p := by dsimp only [p]; fun_prop
    have hq : Continuous q :=
      e.symm.isometry.continuous.comp
        (σ.symm.toLinearMap.continuous_of_finiteDimensional.comp hp)
    have hσ : Isometry σ := by
      change Isometry (σ.toAlgHom : ℂ → ℂ)
      rcases Complex.real_algHom_eq_id_or_conj σ.toAlgHom with h | h
      · rw [h]; exact isometry_id
      · rw [h]; exact Complex.isometry_conj
    have hz (t : ℝ) : σ (extensionEmbedding v₀ (q t)) = p t := by
      change σ (e (e.symm (σ.symm (p t)))) = p t
      rw [e.apply_symm_apply, AlgEquiv.apply_symm_apply]
    have hnorm (t : ℝ) : ‖q t‖ = ‖g.val.val v₀‖ := by
      have hf := hσ.comp (isometry_extensionEmbedding v₀)
      have hzero : σ (extensionEmbedding v₀ 0) = 0 := by simp
      rw [← hf.norm_map_of_map_zero hzero (q t),
        ← hf.norm_map_of_map_zero hzero (g.val.val v₀)]
      change ‖σ (extensionEmbedding v₀ (q t))‖ = ‖z g‖
      rw [hz]
      simp [p, Complex.norm_real, Complex.norm_exp_ofReal_mul_I]
    have hne (t : ℝ) : q t ≠ 0 := norm_ne_zero_iff.mp
      ((hnorm t).trans_ne (norm_ne_zero_iff.mpr (atPlace g.val).ne_zero))
    let u (t : ℝ) := Units.mk0 (q t) (hne t)
    have hu : Continuous u := Units.continuous_iff.mpr
      ⟨hq, continuousOn_inv₀.comp_continuous hq hne⟩
    let E := ContinuousMulEquiv.piUnits (M := InfinitePlace.Completion (K := F))
    let r (t : ℝ) : 𝕀∞ := E.symm (Function.update (E g.val) v₀ (u t))
    have hr : Continuous r :=
      E.symm.continuous.comp ((continuous_update v₀).comp (continuous_const.prodMk hu))
    have hrnorm (t : ℝ) (v : InfinitePlace F) : ‖(r t).val v‖ = ‖g.val.val v‖ := by
      change ‖(Function.update (E g.val) v₀ (u t) v).val‖ = _
      by_cases h : v = v₀
      · subst v
        rw [Function.update_self]
        exact hnorm t
      · rw [Function.update_of_ne h]
        rfl
    have hrone (t : ℝ) : infiniteIdeleNorm F (r t) = 1 := by
      apply Units.ext
      apply NNReal.coe_injective
      rw [infiniteIdeleNorm_eq_exp_sum_log, show infiniteIdeleLog F (r t) =
        infiniteIdeleLog F g.val from funext fun v ↦ by rw [infiniteIdeleLog, infiniteIdeleLog, hrnorm],
        infiniteIdeleLog_sum_zero, Real.exp_zero]
      rfl
    let s (t : ℝ) : N∞ := ⟨r t, hrone t⟩
    have hs : Continuous s := hr.subtype_mk _
    have hsarg (t : ℝ) (ht : t ∈ Ioo (-Real.pi) Real.pi) : (z (s t)).arg = t := by
      have hcoord : (s t).val.val v₀ = q t := by
        change (Function.update (E g.val) v₀ (u t) v₀).val = _
        rw [Function.update_self]
        rfl
      have hzp : z (s t) = p t := by
        change σ (extensionEmbedding v₀ ((s t).val.val v₀)) = p t
        rw [hcoord, hz]
      have hzg : z g ≠ 0 := (map_ne_zero σ).mpr
        ((map_ne_zero (extensionEmbedding v₀)).mpr (atPlace g.val).ne_zero)
      rw [hzp]
      change ((‖z g‖ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)).arg = t
      rw [Complex.arg_real_mul _ (norm_pos_iff.mpr hzg), ← Circle.coe_exp]
      exact Circle.arg_exp ht.1 ht.2.le
    have hsg : s ((z g).arg) = g := by
      apply Subtype.ext
      apply E.injective
      change Function.update (E g.val) v₀ (u ((z g).arg)) = _
      apply Function.update_eq_self_iff.mpr
      apply Units.ext
      apply (σ.injective.comp (isometry_extensionEmbedding v₀).injective)
      change σ (extensionEmbedding v₀ (q ((z g).arg))) = z g
      rw [hz]
      exact Complex.norm_mul_exp_arg_mul_I _
    have hev : ∀ᶠ t in 𝓝 ((z g).arg), s t ∈ centeredInfiniteIdeleDomain F b v₀ σ := by
      apply hs.continuousAt.preimage_mem_nhds
      rw [hsg]
      exact mem_interior_iff_mem_nhds.mp hg
    have hnear : Ioo (-Real.pi) Real.pi ∈ 𝓝 ((z g).arg) :=
      isOpen_Ioo.mem_nhds ⟨(neg_lt_neg hπ).trans_le hangle.1, hangle.2.trans hπ⟩
    have hIco : Ico (-a) a ∈ 𝓝 ((z g).arg) := by
      filter_upwards [hev, hnear] with t ht htπ
      simpa only [hsarg t htπ] using hsector (s t) ht
    rwa [← interior_Ico, mem_interior_iff_mem_nhds]

/-- Paper: Lemma A.5.2.13(1), p. 576. The interior of the centered archimedean
domain is invariant under inversion. -/
theorem inv_interior_centeredInfiniteIdeleDomain :
    (interior (centeredInfiniteIdeleDomain F b v₀ σ))⁻¹ =
      interior (centeredInfiniteIdeleDomain F b v₀ σ) := by
  classical
  let B := (b.map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ (Units.unitLattice F)
  have hB (i : Fin (Units.rank F)) : Units.logEmbeddingQuot F (b i) = B i := by
    rw [Module.Basis.ofZLatticeBasis_apply]
    rfl
  let p (g : N∞) : logSpace F := fun w ↦ infiniteIdeleLog F g.val w.val
  let c (g : N∞) := B.equivFun (p g)
  have hc : Continuous c :=
    B.equivFun.toLinearMap.continuous_of_finiteDimensional.comp (continuous_pi fun w ↦
      (continuous_apply w.val).comp ((infiniteIdeleLog_continuous F).comp continuous_subtype_val))
  have hcOpen : IsOpenMap c :=
    (B.equivFun.toLinearMap.isOpenMap_of_finiteDimensional B.equivFun.surjective).comp
      (isOpenMap_infiniteIdeleLog_omit F)
  let V : Set (Fin (Units.rank F) → ℝ) := Set.pi univ fun _ ↦ Ico (-(1 / 2)) (1 / 2)
  let U : Set (Fin (Units.rank F) → ℝ) := Set.pi univ fun _ ↦ Ioo (-(1 / 2)) (1 / 2)
  have hV : interior V = U := by
    simp only [V, interior_pi_set finite_univ, interior_Ico, U]
  have hlog (g : N∞) : p g ∈ centeredRegulatorParallelotope F b ↔ c g ∈ V := by
    simp only [centeredRegulatorParallelotope, hB]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add]
    change (∑ i, (1 / 2 : ℝ) • B i) + p g ∈ ZSpan.fundamentalDomain B ↔ _
    simp only [ZSpan.mem_fundamentalDomain, map_add, Finsupp.add_apply, B.repr_sum_self, V,
      Set.mem_pi, mem_univ, forall_const, mem_Ico, c, Module.Basis.equivFun_apply]
    exact forall_congr' fun i ↦ by constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hcinv (g : N∞) : c g⁻¹ = -c g := by
    let L : 𝕀∞ →* Multiplicative (InfinitePlace F → ℝ) :=
      MonoidHom.mk' (fun x ↦ Multiplicative.ofAdd (infiniteIdeleLog F x))
        (infiniteIdeleLog_mul F)
    have hinv : infiniteIdeleLog F (g.val⁻¹) = -infiniteIdeleLog F g.val := map_inv L g.val
    change B.equivFun (p g⁻¹) = _
    rw [show p g⁻¹ = -p g from funext fun w ↦ congrFun hinv w.val, map_neg]
  let z (g : N∞) := σ (extensionEmbedding v₀ (g.val.val v₀))
  have hz : Continuous z :=
    σ.toLinearMap.continuous_of_finiteDimensional.comp
      ((isometry_extensionEmbedding v₀).continuous.comp
        ((continuous_apply v₀).comp (Units.continuous_val.comp continuous_subtype_val)))
  have hzne (g : N∞) : z g ≠ 0 := (map_ne_zero σ).mpr
    ((map_ne_zero (extensionEmbedding v₀)).mpr (atPlace g.val).ne_zero)
  have hzinv (g : N∞) : z g⁻¹ = (z g)⁻¹ := by
    let f : N∞ →* ℂˣ := (Units.map (σ.toRingHom.comp
      (extensionEmbedding v₀)).toMonoidHom).comp ((atPlace).comp (N∞).subtype)
    have hf (x : N∞) : (f x).val = z x := rfl
    simpa only [Units.val_inv_eq_inv_val, hf] using congrArg Units.val (map_inv f g)
  let a := Real.pi / (Units.torsionOrder F : ℝ)
  have hle : a ≤ Real.pi := div_le_self Real.pi_pos.le (by exact_mod_cast Units.torsionOrder_pos F)
  have hkey (g : N∞) (hg : g ∈ interior (centeredInfiniteIdeleDomain F b v₀ σ)) :
      g⁻¹ ∈ interior (centeredInfiniteIdeleDomain F b v₀ σ) := by
    have hlogmem : c g ∈ U := by
      rw [← hV]
      have hsubset : centeredInfiniteIdeleDomain F b v₀ σ ⊆ c ⁻¹' V :=
        fun x hx ↦ (hlog x).mp hx.1
      exact hcOpen.interior_preimage_subset_preimage_interior (interior_mono hsubset hg)
    have hang : (z g).arg ∈ Ioo (-a) a :=
      arg_mem_Ioo_of_mem_interior_centeredInfiniteIdeleDomain F b v₀ σ g hg
    have hanginv : (z g⁻¹).arg ∈ Ioo (-a) a := by
      rw [hzinv, Complex.arg_inv, ite_eq_right (hang.2.trans_le hle).ne]
      exact ⟨neg_lt_neg hang.2, neg_lt_of_neg_lt hang.1⟩
    let W : Set N∞ := (c ⁻¹' U) ∩ (z ⁻¹' (Complex.slitPlane ∩ Complex.arg ⁻¹' Ioo (-a) a))
    have hW : IsOpen W := ((isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo).preimage hc).inter
      ((Complex.continuousOn_arg.isOpen_inter_preimage Complex.isOpen_slitPlane isOpen_Ioo).preimage hz)
    refine interior_maximal (t := W) ?_ hW ?_
    · intro x hx
      refine ⟨(hlog x).mpr (fun i hi ↦ Ioo_subset_Ico_self (hx.1 i hi)), ?_⟩
      change (z x).arg ∈ Ico (-Real.pi / _) _
      rw [neg_div]
      exact Ioo_subset_Ico_self hx.2.2
    · refine ⟨?_, Complex.mem_slitPlane_iff_arg.mpr
        ⟨(hanginv.2.trans_le hle).ne, hzne _⟩, hanginv⟩
      change c g⁻¹ ∈ U
      rw [hcinv]
      intro i hi
      exact ⟨neg_lt_neg (hlogmem i hi).2, neg_lt_of_neg_lt (hlogmem i hi).1⟩
  ext g
  exact ⟨fun hg ↦ by simpa only [inv_inv] using hkey g⁻¹ hg, hkey g⟩

/-- Paper: (A.5.2.19)–(A.5.2.20), p. 576. Pull back the shrinking open log cubes
in regulator coordinates to the norm-one archimedean ideles. -/
def infiniteIdeleLogNeighborhood (k : ℕ) : Set N∞ :=
  {g | ∃ t : Fin (Units.rank F) → ℝ,
    (∀ i, t i ∈ Ioo (-(1 / ((k : ℝ) + 1))) (1 / ((k : ℝ) + 1))) ∧
    ∀ w : {w : InfinitePlace F // w ≠ w₀},
      infiniteIdeleLog F g.val w.val = ∑ i, t i * Units.logEmbeddingQuot F (b i) w}

/-- Paper: (A.5.2.19)–(A.5.2.20), p. 576. A norm-one archimedean idele belongs
to every one of the log neighborhoods exactly when all its logarithmic coordinates vanish. -/
theorem mem_all_infiniteIdeleLogNeighborhood_iff (g : N∞) :
    (∀ k, g ∈ infiniteIdeleLogNeighborhood F b k) ↔ infiniteIdeleLog F g.val = 0 := by
  constructor
  · intro h
    have hw (w : {w : InfinitePlace F // w ≠ w₀}) : infiniteIdeleLog F g.val w.val = 0 := by
      set C := ∑ i, |Units.logEmbeddingQuot F (b i) w|
      have hbound (k : ℕ) : |infiniteIdeleLog F g.val w.val| ≤ C / ((k : ℝ) + 1) := by
        obtain ⟨t, ht, hg⟩ := h k
        rw [hg w, Finset.sum_div]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
        have hti : |t i| ≤ 1 / ((k : ℝ) + 1) := (abs_lt.mpr (ht i)).le
        rw [abs_mul]
        exact le_of_le_of_eq (mul_le_mul_of_nonneg_right hti (abs_nonneg _)) (by ring)
      by_contra hne
      have hpos : 0 < |infiniteIdeleLog F g.val w.val| := abs_pos.mpr hne
      obtain ⟨k, hk⟩ := exists_nat_gt (C / |infiniteIdeleLog F g.val w.val|)
      have h1 := hbound k
      rw [div_lt_iff₀ hpos] at hk
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith
    funext v
    show infiniteIdeleLog F g.val v = 0
    by_cases hv : v = w₀
    · rw [hv]
      have hs := infiniteIdeleLog_sum_zero F g
      rwa [Finset.sum_eq_single w₀ (fun v _ hv ↦ hw ⟨v, hv⟩) (by simp)] at hs
    · exact hw ⟨v, hv⟩
  · intro h k
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    exact ⟨0, fun _ ↦ ⟨by simpa using hk, hk⟩, fun w ↦ by rw [h]; simp⟩

/-- Paper: Lemma A.5.2.13(2), p. 576. Each shrinking log cube pulls back
to an inversion-invariant subset of the archimedean norm-one group. -/
theorem inv_infiniteIdeleLogNeighborhood (k : ℕ) :
    (infiniteIdeleLogNeighborhood F b k)⁻¹ = infiniteIdeleLogNeighborhood F b k := by
  have hlog (x : (InfiniteAdeleRing F)ˣ) : infiniteIdeleLog F x⁻¹ = -infiniteIdeleLog F x := by
    have h1 : infiniteIdeleLog F 1 = 0 := by
      funext v
      show (v.mult : ℝ) * Real.log ‖(1 : v.Completion)‖ = 0
      simp
    have := infiniteIdeleLog_mul F x⁻¹ x
    rw [inv_mul_cancel, h1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have key (g : N∞) (hg : g ∈ infiniteIdeleLogNeighborhood F b k) :
      g⁻¹ ∈ infiniteIdeleLogNeighborhood F b k := by
    obtain ⟨t, ht, hgt⟩ := hg
    refine ⟨-t, fun i ↦ ?_, fun w ↦ ?_⟩
    · have := ht i
      simp only [Set.mem_Ioo, Pi.neg_apply] at this ⊢
      constructor <;> linarith [this.1, this.2]
    · rw [InvMemClass.coe_inv, hlog, Pi.neg_apply, hgt w]
      simp [Finset.sum_neg_distrib]
  ext g
  exact ⟨fun h ↦ by simpa using key _ h, fun h ↦ key _ h⟩

-- TODO(paper-gap): The D′ and D″ assertions of Lemma A.5.2.13(2) fail. All the
-- preimages in (A.5.2.19) contain the log kernel, including the nonidentity element −1.

local notation "finiteAtS" => Units.map (RingHom.toMonoidHom (RingHom.snd _ _))
local notation "finiteGlobal" => Units.map (RingHom.toMonoidHom (RingHom.snd (InfiniteAdeleRing F)
  (FiniteAdeleRing (𝓞 F) F)))

/-- Paper: (A.5.2.21), p. 576. Take the product of the archimedean log neighborhood
and the selected finite unit set inside the norm-one S-ideles.
Deviation: The finite sets are supplied via their images in the units at the finite places of S. -/
def sLocalIdeleLogNeighborhood
    (B : ℕ → Set (((v : {v : HeightOneSpectrum (𝓞 F) // v ∈ S}) → v.val.adicCompletion F)ˣ))
    (k : ℕ) : Set Nₛ :=
  {g | atInfinity g.val ∈ (N∞).subtype '' infiniteIdeleLogNeighborhood F b k ∧
    finiteAtS g.val ∈ B k}

/-- Paper: (A.5.2.21), p. 576. The identity belongs to the product neighborhood
exactly when the selected finite set contains its identity. -/
theorem one_mem_sLocalIdeleLogNeighborhood_iff
    (B : ℕ → Set (((v : {v : HeightOneSpectrum (𝓞 F) // v ∈ S}) → v.val.adicCompletion F)ˣ)) (k : ℕ) :
    1 ∈ sLocalIdeleLogNeighborhood F b S B k ↔ 1 ∈ B k := by
  have h : (1 : N∞) ∈ infiniteIdeleLogNeighborhood F b k := by
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    refine ⟨0, fun _ ↦ ⟨by simpa using hk, hk⟩, fun w ↦ ?_⟩
    show (w.val.mult : ℝ) * Real.log ‖(1 : w.val.Completion)‖ = _
    simp
  exact and_iff_right ⟨1, h, by simp⟩

/-- Paper: Lemma A.5.2.14(1), p. 576. With a symmetric finite factor,
the product neighborhood in the norm-one S-ideles is symmetric.
Deviation: The D′ condition fails for the printed sequence. -/
theorem inv_sLocalIdeleLogNeighborhood
    (B : ℕ → Set (((v : {v : HeightOneSpectrum (𝓞 F) // v ∈ S}) → v.val.adicCompletion F)ˣ))
    (k : ℕ) (hB : (B k)⁻¹ = B k) :
    (sLocalIdeleLogNeighborhood F b S B k)⁻¹ =
      sLocalIdeleLogNeighborhood F b S B k := by
  have key (g : Nₛ) (hg : g ∈ sLocalIdeleLogNeighborhood F b S B k) :
      g⁻¹ ∈ sLocalIdeleLogNeighborhood F b S B k := by
    obtain ⟨⟨h, hh, hgh⟩, hfin⟩ := hg
    refine ⟨⟨h⁻¹, ?_, ?_⟩, ?_⟩
    · exact (Set.ext_iff.mp (inv_infiniteIdeleLogNeighborhood F b k) h⁻¹).mp
        (Set.inv_mem_inv.mpr hh)
    · rw [map_inv, hgh, InvMemClass.coe_inv, map_inv]
    · rw [InvMemClass.coe_inv, map_inv, ← hB]
      exact Set.inv_mem_inv.mpr hfin
  ext g
  exact ⟨fun h ↦ by simpa using key _ h, fun h ↦ key _ h⟩

-- TODO(paper-gap): Lemma A.5.2.14(1) inherits the nonshrinking log kernel.
-- For ℚ(i) the persistent circle also has nontrivial image in J_F,S¹ for S = S∞,
-- contradicting the D′ claim in Lemma A.5.2.14(2).
-- TODO(paper-gap): Lemma A.5.2.15 uses (A.5.2.22), which is undefined at k = 0
-- and uses intervals that are not invariant under inversion.

/-- Paper: (A.5.2.23), p. 577. Take the product of the archimedean log neighborhood
and the selected finite unit set inside the global norm-one ideles.
The finite sets are supplied as their images in the finite ideles. -/
def ideleLogNeighborhood (B : ℕ → Set (FiniteAdeleRing (𝓞 F) F)ˣ) (k : ℕ) : Set N₁ :=
  {g | atInfinity g.val ∈ (N∞).subtype '' infiniteIdeleLogNeighborhood F b k ∧
    finiteGlobal g.val ∈ B k}

/-- Paper: (A.5.2.23), p. 577. The identity belongs to the global product neighborhood
exactly when the chosen finite unit set contains its identity. -/
theorem one_mem_ideleLogNeighborhood_iff
    (B : ℕ → Set (FiniteAdeleRing (𝓞 F) F)ˣ) (k : ℕ) :
    1 ∈ ideleLogNeighborhood F b B k ↔ 1 ∈ B k := by
  have h : (1 : N∞) ∈ infiniteIdeleLogNeighborhood F b k := by
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    refine ⟨0, fun _ ↦ ⟨by simpa using hk, hk⟩, fun w ↦ ?_⟩
    show (w.val.mult : ℝ) * Real.log ‖(1 : w.val.Completion)‖ = _
    simp
  exact and_iff_right ⟨1, h, by simp⟩

/-- Paper: Lemma A.5.2.16(1), p. 577. With a symmetric finite factor,
the product neighborhood in the global norm-one ideles is symmetric.
Deviation: The D′ condition fails for the printed sequence. -/
theorem inv_ideleLogNeighborhood (B : ℕ → Set (FiniteAdeleRing (𝓞 F) F)ˣ)
    (k : ℕ) (hB : (B k)⁻¹ = B k) :
    (ideleLogNeighborhood F b B k)⁻¹ = ideleLogNeighborhood F b B k := by
  have key (g : N₁) (hg : g ∈ ideleLogNeighborhood F b B k) :
      g⁻¹ ∈ ideleLogNeighborhood F b B k := by
    obtain ⟨⟨h, hh, hgh⟩, hfin⟩ := hg
    refine ⟨⟨h⁻¹, ?_, ?_⟩, ?_⟩
    · exact (Set.ext_iff.mp (inv_infiniteIdeleLogNeighborhood F b k) h⁻¹).mp
        (Set.inv_mem_inv.mpr hh)
    · rw [map_inv, hgh, InvMemClass.coe_inv, map_inv]
    · rw [InvMemClass.coe_inv, map_inv, ← hB]
      exact Set.inv_mem_inv.mpr hfin
  ext g
  exact ⟨fun h ↦ by simpa using key _ h, fun h ↦ key _ h⟩

-- TODO(paper-gap): The D′ assertions of Lemma A.5.2.16 fail. Over ℚ(i) every set
-- contains the archimedean circle, whose images in the class groups are nontrivial.

end Ideles

/-- Paper: (A.5.2.22) and (A.5.2.24), p. 577. Multiply the image of the printed
interval under a norm section by the corresponding norm-one set in the ambient group.
Deviation: The formula is defined only at positive indices. -/
def normSectionNeighborhood {G : Type*} [Group G] (τ : ℝ≥0ˣ →* G)
    (U : ℕ → Set G) (k : ℕ+) : Set G :=
  (τ '' {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Ioo (1 - 1 / (k : ℝ)) (1 + 1 / (k : ℝ))}) * U k

/-- Paper: (A.5.2.22) and (A.5.2.24), p. 577. If the selected kernel set
contains the identity, applying the norm recovers exactly the printed interval
in the positive reals. -/
theorem norm_image_normSectionNeighborhood {G : Type*} [Group G] (n : G →* ℝ≥0ˣ)
    (τ : ℝ≥0ˣ →* G) (hτ : RightInverse τ n) (U : ℕ → Set G) (k : ℕ+)
    (hU₁ : 1 ∈ U k) (hU : U k ⊆ n.ker) :
    n '' normSectionNeighborhood τ U k =
      {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Ioo (1 - 1 / (k : ℝ)) (1 + 1 / (k : ℝ))} := by
  ext t
  simp only [normSectionNeighborhood, Set.mem_image, Set.mem_mul]
  constructor
  · rintro ⟨_, ⟨_, ⟨s, hs, rfl⟩, u, hu, rfl⟩, rfl⟩
    rwa [map_mul, hτ s, MonoidHom.mem_ker.mp (hU hu), mul_one]
  · intro ht
    exact ⟨τ t * 1, ⟨τ t, ⟨t, ht, rfl⟩, 1, hU₁, rfl⟩, by rw [mul_one, hτ t]⟩

-- TODO(paper-gap): Lemma A.5.2.17 has the same interval problems as A.5.2.15 and
-- retains the log kernel in each norm-one factor and in its class-group images.
-- TODO(paper-gap): Definition A.5.2.18 calls the affected families open symmetric
-- D′-sequences. The displayed families do not have those properties.
-- TODO(paper-gap): Remark A.5.2.19 gives constant 1 when the log rank is zero.
-- This contradicts the strict upper bound in (A.5.2.1) for any set containing 1.

end RiemannMasullo
