module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_CriticalWindowTrace
import Mathlib.Tactic

/-! # Sharp output projections on the Hardy–Sobolev strip

The two complementary indicators split the Hilbert trace. Its lower part is
integrable for translates of a fixed nuclear operator at the critical weight. -/

@[expose] public noncomputable section
open Classical Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace RiemannMasullo

set_option quotPrecheck false
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)
local notation "ℓ" => (fun x : G ↦ Real.log ((m x).val : ℝ))
local notation "W(" a ")" => CompactIntervalSobolev μ ℓ (-(a:ℝ)) a 3
local notation "ν(" a ")" => μ.withDensity (fun x : G ↦ ENNReal.ofReal (intervalSobolevDensity (-a) a 3 (ℓ x)))
local notation "L(" ha ", " g ")" => hardySobolevTranslation μ m _ _ 3 (neg_le_self ha) (by norm_num : (0:ℝ) ≤ 3) g
local notation "tr(" L ", " T ")" => hilbertTrace (⟨L * (T : nuclearEndomorphisms _).val,
  mul_mem_nuclearEndomorphisms_left L T⟩ : nuclearEndomorphisms _)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem logModule_measurable : Measurable ℓ :=
  Real.measurable_log.comp (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable

/-- Degree-three strip projection onto a measurable set in output space. -/
def degreeThreeOutputCutoff (a : ℝ) {U : Set G} (hU : MeasurableSet U) : W(a) →L[ℂ] W(a) :=
  (hardySobolevCutoff_spec (μ := ν(a)) hU).choose

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G] [μ.IsHaarMeasure] in
theorem degreeThreeOutputCutoff_apply (a : ℝ) {U : Set G} (hU : MeasurableSet U) (u : W(a)) :
    (degreeThreeOutputCutoff μ m a hU u : G → ℂ) =ᵐ[ν(a)] U.indicator u :=
  ((hardySobolevCutoff_spec (μ := ν(a)) hU).choose_spec.2 u).2.2

local notation "lo(" a ", " y ")" => degreeThreeOutputCutoff μ m a
  (measurableSet_le (logModule_measurable m) (measurable_const (a := 3*(y:ℝ)/4)))

private def lowerMask (y : ℝ) (x : G) : ℂ := if ℓ x ≤ 3*y/4 then 1 else 0

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem meas_lowerMask : Measurable (Function.uncurry (lowerMask m)) := by
  have h : MeasurableSet {p : ℝ × G | ℓ p.2 ≤ 3*p.1/4} :=
    measurableSet_le ((logModule_measurable m).comp measurable_snd) ((measurable_const.mul measurable_fst).div_const 4)
  exact Measurable.ite h measurable_const measurable_const

private theorem lowerTranslate_apply {a : ℝ} (ha : 0 ≤ a) (g : ℝ → G) (y : ℝ) (u : W(a)) :
    ((lo(a,y) * L(ha,g y)) u : G → ℂ) =ᵐ[ν(a)] (fun x ↦ lowerMask m y x * u ((g y)⁻¹*x)) := by
  have h₁ := degreeThreeOutputCutoff_apply μ m a (measurableSet_le (logModule_measurable m)
    (measurable_const (a := 3*y/4))) (L(ha,g y) u)
  have h₂ := hardySobolevTranslation_apply μ m (-a) a 3 (neg_le_self ha) (by norm_num) (g y) u
  filter_upwards [h₁,(withDensity_absolutelyContinuous μ _).ae_eq h₂] with x hx h'x
  change (lo(a,y) (L(ha,g y) u)) x = _
  rw [hx]
  by_cases h : ℓ x ≤ 3*y/4 <;> simp [lowerMask,Set.indicator,h,h'x]

/-- The sharp lower output projection following the actual Hardy–Sobolev
translation obeys the integrated nuclear trace estimate. -/
theorem integrable_lower_output_trace (g : ℝ → G) (hg : Measurable g)
    (hshift : ∀ y x, ℓ (g y*x) = ℓ x+y) {a : ℝ} (ha : 0 < a)
    (T : nuclearEndomorphisms W(a)) :
    IntegrableOn (fun y : ℝ ↦ (Real.exp (-a*y/2):ℂ)*tr(lo(a,y)*L(ha.le,g y),T)) (Ioi 0) :=
  (integrable_critical_masked_trace μ g ℓ a hg (logModule_measurable m) ha hshift (lowerMask m)
    (meas_lowerMask m) (fun y x ↦ by dsimp [lowerMask]; split_ifs <;> simp)
    (fun y x hx ↦ by simp [lowerMask,not_le.mpr hx])
    (fun y ↦ lo(a,y)*L(ha.le,g y)) (lowerTranslate_apply μ m ha.le g) T).1

local notation "hi(" a ", " y ")" => degreeThreeOutputCutoff μ m a
  (measurableSet_lt (measurable_const (a := 3*(y:ℝ)/4)) (logModule_measurable m))

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [μ.IsHaarMeasure] in
private theorem cutoff_sum (a y : ℝ) : hi(a,y) + lo(a,y) = (1 : W(a) →L[ℂ] W(a)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (hi(a,y) u) (lo(a,y) u),
    degreeThreeOutputCutoff_apply μ m a (measurableSet_lt (measurable_const (a := 3*y/4)) (logModule_measurable m)) u,
    degreeThreeOutputCutoff_apply μ m a (measurableSet_le (logModule_measurable m) (measurable_const (a := 3*y/4))) u] with x hadd hhi hlo
  change ((hi(a,y) u + lo(a,y) u : W(a)) : G → ℂ) x = u x
  rw [hadd,Pi.add_apply,hhi,hlo]
  by_cases hx : ℓ x ≤ 3*y/4
  · simp [Set.indicator,hx,not_lt.mpr hx]
  · simp [Set.indicator,hx,lt_of_not_ge hx]

/-- The exterior trace of a moving nuclear convolution differs from its total
trace by an integrable lower-window correction. The translation covariance is
an equality of operators in the ambient weighted Hilbert space. -/
theorem integrable_exterior_sub_full (g : ℝ → G) (hg : Measurable g)
    (hshift : ∀ y x, ℓ (g y*x) = ℓ x+y) {a : ℝ} (ha : 0 < a)
    (T : nuclearEndomorphisms W(a)) (S : ℝ → nuclearEndomorphisms W(a))
    (hS : ∀ y, (S y).val = L(ha.le,g y)*T.val) :
    IntegrableOn (fun y : ℝ ↦ (Real.exp (-a*y/2):ℂ) * (tr(hi(a,y),S y) - hilbertTrace (S y))) (Ioi 0) := by
  apply (integrable_lower_output_trace μ m g hg hshift ha T).neg.congr
  filter_upwards with y
  let U : nuclearEndomorphisms W(a) := ⟨hi(a,y)*(S y).val,mul_mem_nuclearEndomorphisms_left _ _⟩
  let D : nuclearEndomorphisms W(a) := ⟨(lo(a,y)*L(ha.le,g y))*T.val,mul_mem_nuclearEndomorphisms_left _ _⟩
  have hUD : U + D = S y := by
    apply Subtype.ext
    change hi(a,y)*(S y).val + (lo(a,y)*L(ha.le,g y))*T.val = (S y).val
    rw [mul_assoc,← hS y,← add_mul,cutoff_sum,one_mul]
  obtain ⟨f,hf⟩ := hilbertTrace_linear (H := W(a))
  have htr : hilbertTrace U + hilbertTrace D = hilbertTrace (S y) :=
    (congrArg₂ (·+·) (hf U).symm (hf D).symm).trans
      ((f.map_add U D).symm.trans ((congrArg f hUD).trans (hf (S y))))
  change -((Real.exp (-a*y/2):ℂ)*hilbertTrace D) = _*(hilbertTrace U-hilbertTrace (S y))
  rw [← htr]; ring


end RiemannMasullo
