module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # A compact smooth density with nonvanishing off-axis Laplace transform

The Fabius density is even, supported in `[-1,1]`, and has mass one. We construct its
distribution function from a contraction on continuous functions on the unit interval.
Its differential equation gives a dyadic recurrence for the bilateral Laplace transform.
A zero off the imaginary axis would persist under repeated halving and reach the origin
in the limit, contradicting the normalization.

See J. Arias de Reyna, *An infinitely differentiable function with compact support*,
Rev. Real Acad. Ciencias Madrid 76 (1982), 21–38, Theorem 1 and equation (9).
English translation: https://arxiv.org/abs/1702.05442.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal ContDiff

noncomputable section

namespace RiemannMasullo

namespace Fabius

private def extend (g : C(unitInterval, ℝ)) (x : ℝ) : ℝ := g (Set.projIcc 0 1 zero_le_one x)

private theorem continuous_extend (g : C(unitInterval, ℝ)) : Continuous (extend g) :=
  g.continuous.comp continuous_projIcc

private def tent (x : ℝ) := 1 - |2 * x - 1|

/-- This contraction determines the primitive of the distribution function on the unit interval. -/
private def primitiveOperator (g : C(unitInterval, ℝ)) : C(unitInterval, ℝ) where
  toFun x := max 0 ((x : ℝ) - 1 / 2) + (1 / 2) * ∫ y in 0..tent x, extend g y
  continuous_toFun := by
    have h : Continuous (fun u : ℝ ↦ ∫ y in 0..u, extend g y) :=
      intervalIntegral.continuous_primitive (fun a b ↦ (continuous_extend g).intervalIntegrable a b) 0
    exact (continuous_const.max (continuous_subtype_val.sub continuous_const)).add
      (continuous_const.mul (h.comp (by unfold tent; fun_prop)))

private theorem primitiveOperator_apply (g : C(unitInterval, ℝ)) (x : unitInterval) :
    primitiveOperator g x = max 0 ((x : ℝ) - 1 / 2) + (1 / 2) * ∫ y in 0..tent x, extend g y := rfl

private theorem tent_mem (x : unitInterval) : 0 ≤ tent x ∧ tent x ≤ 1 := by
  have hx := x.property
  dsimp [tent]
  constructor
  · have h : |2 * (x : ℝ) - 1| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    linarith
  · linarith [abs_nonneg (2 * (x : ℝ) - 1)]

private theorem primitiveOperator_contracting : ContractingWith (1 / 2 : ℝ≥0) primitiveOperator := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul (fun f g ↦ ?_)⟩
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro x
  have hb : ‖∫ y in 0..tent x, extend f y - extend g y‖ ≤ dist f g * |tent x - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun y _ ↦ by
      simpa only [Real.norm_eq_abs, ← Real.dist_eq, extend] using
        ContinuousMap.dist_apply_le_dist (f := f) (g := g) (Set.projIcc 0 1 zero_le_one y))
  have hi := intervalIntegral.integral_sub (μ := volume) ((continuous_extend f).intervalIntegrable 0 (tent x))
    ((continuous_extend g).intervalIntegrable 0 (tent x))
  rw [hi, sub_zero, abs_of_nonneg (tent_mem x).1] at hb
  rw [primitiveOperator_apply, primitiveOperator_apply]
  rw [dist_add_left, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have h := mul_le_mul_of_nonneg_left (tent_mem x).2 (dist_nonneg (x := f) (y := g))
  norm_num at hb h ⊢
  linarith

private def fixedPrimitive : C(unitInterval, ℝ) := primitiveOperator_contracting.fixedPoint primitiveOperator

private def primitive : ℝ → ℝ := extend fixedPrimitive

private theorem continuous_primitive : Continuous primitive := continuous_extend _

private theorem primitiveOperator_fixedPrimitive : primitiveOperator fixedPrimitive = fixedPrimitive :=
  primitiveOperator_contracting.fixedPoint_isFixedPt

private theorem primitive_eq {x : ℝ} (hx : x ∈ unitInterval) :
    primitive x = max 0 (x - 1 / 2) + (1 / 2) * ∫ y in 0..tent x, primitive y := by
  have h := congrArg (fun q : C(unitInterval, ℝ) ↦ q ⟨x, hx⟩) primitiveOperator_fixedPrimitive
  change _ = fixedPrimitive ⟨x, hx⟩ at h
  simpa only [primitive, extend, primitiveOperator, ContinuousMap.coe_mk, Set.projIcc_of_mem _ hx] using h.symm

private theorem primitive_zero : primitive 0 = 0 := by
  rw [primitive_eq (x := 0) (by constructor <;> norm_num), tent]; norm_num

private theorem primitive_one : primitive 1 = 1 / 2 := by
  rw [primitive_eq (x := 1) (by constructor <;> norm_num), tent]; norm_num

private theorem primitive_of_nonpos {x : ℝ} (hx : x ≤ 0) : primitive x = 0 := by
  convert primitive_zero using 1
  simp only [primitive, extend, Set.projIcc_of_le_left _ hx, Set.projIcc_left]

private theorem primitive_of_one_le {x : ℝ} (hx : 1 ≤ x) : primitive x = 1 / 2 := by
  convert primitive_one using 1
  simp only [primitive, extend, Set.projIcc_of_right_le _ hx, Set.projIcc_right]

private theorem primitiveOperator_range {f : C(unitInterval, ℝ)} (hf : ∀ y, f y ∈ Icc 0 (1 / 2)) (x : unitInterval) :
    primitiveOperator f x ∈ Icc 0 (1 / 2) := by
  have h0 := intervalIntegral.integral_nonneg (μ := volume) (f := extend f) (tent_mem x).1
    (fun u _ ↦ (hf (Set.projIcc 0 1 zero_le_one u)).1)
  have h1 := intervalIntegral.integral_mono_on (tent_mem x).1
    ((continuous_extend f).intervalIntegrable 0 (tent x) (μ := volume))
    ((continuous_const : Continuous (fun _ : ℝ ↦ (1 / 2 : ℝ))).intervalIntegrable 0 (tent x) (μ := volume))
    (fun u _ ↦ (hf (Set.projIcc 0 1 zero_le_one u)).2)
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h1
  rw [primitiveOperator_apply]
  have hx := x.property
  constructor
  · positivity
  · rcases le_total (x : ℝ) (1 / 2) with he | he
    · rw [max_eq_left (by linarith : (x : ℝ) - 1 / 2 ≤ 0)]
      linarith [(tent_mem x).2]
    · rw [max_eq_right (by linarith : 0 ≤ (x : ℝ) - 1 / 2)]
      rw [tent, abs_of_nonneg (by linarith : 0 ≤ 2 * (x : ℝ) - 1)] at h1 ⊢
      linarith [hx.2]

private theorem primitive_range (x : ℝ) : primitive x ∈ Icc 0 (1 / 2) := by
  have hi (n : ℕ) (y : unitInterval) : (primitiveOperator^[n] (0 : C(unitInterval, ℝ))) y ∈ Icc 0 (1 / 2) := by
    induction n generalizing y with
    | zero => change (0 : ℝ) ∈ Icc 0 (1 / 2); constructor <;> norm_num
    | succ n ih => rw [Function.iterate_succ_apply']; exact primitiveOperator_range ih y
  let y := Set.projIcc 0 1 zero_le_one x
  have ht := (continuous_eval_const (F := C(unitInterval, ℝ)) y).continuousAt.tendsto.comp
    (primitiveOperator_contracting.tendsto_iterate_fixedPoint (0 : C(unitInterval, ℝ)))
  exact isClosed_Icc.mem_of_tendsto ht (.of_forall fun n ↦ hi n y)

/-- Distribution function, extended by zero on the left and one on the right. -/
private def cdf (x : ℝ) := primitive (2 * x) + 1 / 2 - primitive (2 - 2 * x)

private theorem continuous_cdf : Continuous cdf := by
  unfold cdf
  exact ((continuous_primitive.comp (by fun_prop)).add continuous_const).sub (continuous_primitive.comp (by fun_prop))

private theorem cdf_symm (x : ℝ) : cdf (1 - x) = 1 - cdf x := by
  simp only [cdf, show 2 * (1 - x) = 2 - 2 * x by ring, show 2 - (2 - 2 * x) = 2 * x by ring]; ring

private theorem cdf_low {x : ℝ} (hx : x ≤ 1 / 2) : cdf x = primitive (2 * x) := by
  rw [cdf, primitive_of_one_le (x := 2 - 2 * x) (by linarith)]; ring

private theorem cdf_high {x : ℝ} (hx : 1 / 2 ≤ x) : cdf x = 1 - primitive (2 - 2 * x) := by
  rw [cdf, primitive_of_one_le (x := 2 * x) (by linarith)]; ring

private theorem cdf_of_nonpos {x : ℝ} (hx : x ≤ 0) : cdf x = 0 :=
  (cdf_low (by linarith)).trans (primitive_of_nonpos (by linarith))

private theorem cdf_of_one_le {x : ℝ} (hx : 1 ≤ x) : cdf x = 1 := by
  rw [cdf_high (by linarith), primitive_of_nonpos (x := 2 - 2 * x) (by linarith)]; ring

private theorem integral_cdf_low {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    (∫ y in 0..x, cdf y) = primitive x := by
  have hc : (∫ y in 0..x, cdf y) = ∫ y in 0..x, primitive (2 * y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hx] at hy
    exact cdf_low (hy.2.trans hx')
  rw [hc, intervalIntegral.integral_comp_mul_left primitive (by norm_num : (2 : ℝ) ≠ 0),
    primitive_eq (x := x) ⟨hx, by linarith⟩, tent, abs_of_nonpos (by linarith : 2 * x - 1 ≤ 0),
    max_eq_left (by linarith : x - 1 / 2 ≤ 0)]
  norm_num

private theorem integral_flip (a b : ℝ) :
    (∫ x in a..b, cdf x) = (b - a) - ∫ x in (1 - b)..(1 - a), cdf x := by
  calc
    _ = ∫ x in a..b, 1 - cdf (1 - x) := intervalIntegral.integral_congr (fun x _ ↦ by rw [cdf_symm]; ring)
    _ = _ := by
      rw [intervalIntegral.integral_sub (f := fun _ : ℝ ↦ (1 : ℝ)) (g := fun y : ℝ ↦ cdf (1 - y))
        (continuous_const.intervalIntegrable a b)
        ((continuous_cdf.comp (continuous_const.sub continuous_id)).intervalIntegrable a b),
        intervalIntegral.integral_const,
        intervalIntegral.integral_comp_sub_left]
      simp

private theorem integral_cdf_one : (∫ y in (0 : ℝ)..1, cdf y) = 1 / 2 := by
  have h := integral_flip 0 1
  norm_num at h
  linarith

private theorem primitive_flip {x : ℝ} (hx : x ∈ unitInterval) (hx' : 1 / 2 ≤ x) :
    primitive x = x - 1 / 2 + primitive (1 - x) := by
  have ht : tent (1 - x) = tent x := by
    unfold tent
    rw [show 2 * (1 - x) - 1 = -(2 * x - 1) by ring, abs_neg]
  have hy : 1 - x ∈ unitInterval := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [primitive_eq hx, primitive_eq hy, ht, max_eq_right (by linarith : 0 ≤ x - 1 / 2),
    max_eq_left (by linarith : 1 - x - 1 / 2 ≤ 0), zero_add]

private theorem integral_cdf_unit {x : ℝ} (hx : x ∈ unitInterval) : (∫ y in 0..x, cdf y) = primitive x := by
  rcases le_total x (1 / 2) with he | he
  · exact integral_cdf_low hx.1 he
  · have ha := intervalIntegral.integral_add_adjacent_intervals
      (continuous_cdf.intervalIntegrable 0 x (μ := volume)) (continuous_cdf.intervalIntegrable x 1 (μ := volume))
    rw [integral_cdf_one, integral_flip x 1, sub_self,
      integral_cdf_low (x := 1 - x) (by linarith [hx.2]) (by linarith)] at ha
    rw [primitive_flip hx he]
    linarith

private theorem integral_cdf_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) : (∫ y in a..b, cdf y) = 0 := by
  calc
    _ = ∫ _y in a..b, (0 : ℝ) := intervalIntegral.integral_congr (fun y hy =>
      cdf_of_nonpos (hy.2.trans (max_le ha hb)))
    _ = _ := by simp

private theorem cdf_refine_low {x : ℝ} (hx : x ≤ 1 / 2) : (∫ y in (2 * x - 1)..(2 * x), cdf y) = cdf x := by
  rcases le_total x 0 with he | he
  · rw [integral_cdf_nonpos (by linarith) (by linarith), cdf_of_nonpos he]
  · have ha := intervalIntegral.integral_add_adjacent_intervals
      (continuous_cdf.intervalIntegrable (2 * x - 1) 0 (μ := volume))
      (continuous_cdf.intervalIntegrable 0 (2 * x) (μ := volume))
    rw [integral_cdf_nonpos (by linarith) le_rfl, zero_add, integral_cdf_unit ⟨by linarith, by linarith⟩] at ha
    exact ha.symm.trans (cdf_low hx).symm

/-- The moving-average identity holds across both endpoints. -/
private theorem cdf_refine (x : ℝ) : cdf x = ∫ y in (2 * x - 1)..(2 * x), cdf y := by
  rcases le_total x (1 / 2) with he | he
  · exact (cdf_refine_low he).symm
  · have h := cdf_refine_low (x := 1 - x) (by linarith)
    rw [integral_flip]
    rw [show 1 - (2 * x - 1) = 2 * (1 - x) by ring, show 1 - 2 * x = 2 * (1 - x) - 1 by ring, h, cdf_symm]
    ring

private theorem cdf_hasDerivAt (x : ℝ) : HasDerivAt cdf (2 * (cdf (2 * x) - cdf (2 * x - 1))) x := by
  let P := fun z : ℝ ↦ ∫ y in (0 : ℝ)..z, cdf y
  have hP (z : ℝ) : HasDerivAt P (cdf z) z :=
    intervalIntegral.integral_hasDerivAt_right (continuous_cdf.intervalIntegrable 0 z)
      continuous_cdf.aestronglyMeasurable.stronglyMeasurableAtFilter continuous_cdf.continuousAt
  have he : cdf = fun z ↦ P (2 * z) - P (2 * z - 1) := by
    funext z
    rw [cdf_refine z]
    have h := intervalIntegral.integral_add_adjacent_intervals
      (continuous_cdf.intervalIntegrable 0 (2 * z - 1) (μ := volume))
      (continuous_cdf.intervalIntegrable (2 * z - 1) (2 * z) (μ := volume))
    dsimp [P]
    linarith
  have h1 : HasDerivAt (fun y : ℝ ↦ 2 * y) 2 x := by simpa using (hasDerivAt_id x).const_mul 2
  have h2 : HasDerivAt (fun y : ℝ ↦ 2 * y - 1) 2 x := h1.sub_const 1
  nth_rw 1 [he]
  convert ((hP _).comp x h1).sub ((hP _).comp x h2) using 1 <;> first | rfl | ring

private theorem cdf_smooth : ContDiff ℝ ∞ cdf := by
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr continuous_cdf
  | succ n ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x ↦ (cdf_hasDerivAt x).differentiableAt, by simp, ?_⟩
    rw [show deriv cdf = fun x ↦ 2 * (cdf (2 * x) - cdf (2 * x - 1)) by funext x; exact (cdf_hasDerivAt x).deriv]
    exact contDiff_const.mul ((ih.comp (by fun_prop)).sub (ih.comp (by fun_prop)))

/-- The difference of two translates is an even, compactly supported probability density. -/
private def density (x : ℝ) := cdf (x + 1) - cdf x

private theorem density_smooth : ContDiff ℝ ∞ density :=
  (cdf_smooth.comp (by fun_prop)).sub cdf_smooth

private theorem cdf_range (x : ℝ) : cdf x ∈ Icc 0 1 := by
  rcases le_total x (1 / 2) with he | he
  · rw [cdf_low he]
    exact ⟨(primitive_range _).1, (primitive_range _).2.trans (by norm_num)⟩
  · rw [cdf_high he]
    constructor <;> linarith [(primitive_range (2 - 2 * x)).1, (primitive_range (2 - 2 * x)).2]

private theorem density_nonneg (x : ℝ) : 0 ≤ density x := by
  rcases le_total x 0 with he | he
  · rw [density, cdf_of_nonpos he, sub_zero]; exact (cdf_range _).1
  · rw [density, cdf_of_one_le (by linarith : 1 ≤ x + 1)]; exact sub_nonneg.mpr (cdf_range x).2

private theorem density_even (x : ℝ) : density (-x) = density x := by
  rw [density, density, show -x + 1 = 1 - x by ring, cdf_symm, show -x = 1 - (x + 1) by ring, cdf_symm]; ring

private theorem density_eq_zero {x : ℝ} (hx : x ∉ Icc (-1 : ℝ) 1) : density x = 0 := by
  rw [Set.mem_Icc, not_and_or] at hx
  rcases hx with h | h
  · rw [density, cdf_of_nonpos (by linarith), cdf_of_nonpos (by linarith)]; ring
  · rw [density, cdf_of_one_le (by linarith), cdf_of_one_le (by linarith)]; ring

private theorem density_compact : HasCompactSupport density := by
  refine (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).of_isClosed_subset (isClosed_tsupport density) ?_
  exact closure_minimal (fun x hx ↦ by_contra (fun h ↦ hx (density_eq_zero h))) isClosed_Icc

private theorem density_hasDerivAt (x : ℝ) :
    HasDerivAt density (2 * (density (2 * x + 1) - density (2 * x - 1))) x := by
  have h := ((cdf_hasDerivAt (x + 1)).comp x ((hasDerivAt_id x).add_const 1)).sub (cdf_hasDerivAt x)
  convert h using 1
  · funext y; rfl
  · unfold density; ring_nf

private theorem density_integral : (∫ x : ℝ, density x) = 1 := by
  let f := fun x : ℝ ↦ cdf ((x + 1) / 2)
  have h (x : ℝ) : HasDerivAt f (density x) x := by
    have ha : HasDerivAt (fun y : ℝ ↦ (y + 1) / 2) (1 / 2) x := ((hasDerivAt_id x).add_const 1).div_const 2
    convert (cdf_hasDerivAt ((x + 1) / 2)).comp x ha using 1
    · rfl
    · unfold density; ring_nf
  have hb : Tendsto f atBot (𝓝 0) := tendsto_const_nhds.congr' (by
    filter_upwards [eventually_le_atBot (-1 : ℝ)] with x hx
    exact (cdf_of_nonpos (x := (x + 1) / 2) (by linarith)).symm)
  have ht : Tendsto f atTop (𝓝 1) := tendsto_const_nhds.congr' (by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact (cdf_of_one_le (x := (x + 1) / 2) (by linarith)).symm)
  simpa using integral_of_hasDerivAt_of_tendsto h
    (density_smooth.continuous.integrable_of_hasCompactSupport density_compact) hb ht

private def profile (x : ℝ) : ℂ := density x

private theorem profile_smooth : ContDiff ℝ ∞ profile := Complex.ofRealCLM.contDiff.comp density_smooth

private theorem profile_compact : HasCompactSupport profile :=
  density_compact.comp_left (g := fun x : ℝ ↦ (x : ℂ)) (by simp)

private theorem profile_integral : (∫ x : ℝ, profile x) = 1 := by
  change (∫ x : ℝ, (density x : ℂ)) = 1
  rw [integral_complex_ofReal, density_integral]; simp

private theorem profile_shift_compact (b : ℝ) : HasCompactSupport (fun x : ℝ ↦ profile (2 * x + b)) := by
  refine (isCompact_Icc : IsCompact (Icc (-(|b| + 1)) (|b| + 1))).of_isClosed_subset
    (isClosed_tsupport _) ?_
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra ho
  apply hx
  change (density (2 * x + b) : ℂ) = 0
  rw [density_eq_zero]; simp
  intro hm
  obtain ⟨hm₁, hm₂⟩ := hm
  apply ho
  constructor <;> linarith [abs_nonneg b, neg_abs_le b, le_abs_self b]

private theorem weighted_integrable {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) (z : ℂ) :
    Integrable (fun x : ℝ ↦ f x * Complex.exp (z * x)) :=
  (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right

/-- Substitution in the Laplace integral for an affine dilation of ratio two. -/
private theorem laplace_affine (f : ℝ → ℂ) (z : ℂ) (b : ℝ) :
    (∫ x : ℝ, f (2 * x + b) * Complex.exp (z * x)) =
      ((1 / 2 : ℂ) * Complex.exp (-z * b / 2)) * bilateralLaplace f (z / 2) := by
  let g := fun u : ℝ ↦ f u * Complex.exp ((z / 2) * u)
  have h (x : ℝ) : f (2 * x + b) * Complex.exp (z * x) = g (2 * x + b) * Complex.exp (-z * b / 2) := by
    dsimp [g]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [h]
  rw [integral_mul_const]
  have hs := MeasureTheory.Measure.integral_comp_mul_left (fun x : ℝ ↦ g (x + b)) 2
  rw [integral_add_right_eq_self g b] at hs
  change (∫ x : ℝ, g (2 * x + b)) = _ at hs
  rw [hs]
  simp only [Complex.real_smul]
  norm_num [bilateralLaplace, g]
  ring

private theorem laplace_refinement (z : ℂ) : z * bilateralLaplace profile z =
    (Complex.exp (z / 2) - Complex.exp (-z / 2)) * bilateralLaplace profile (z / 2) := by
  let v := fun x : ℝ ↦ Complex.exp (z * x)
  let d := fun x : ℝ ↦ 2 * (profile (2 * x + 1) - profile (2 * x - 1))
  have hd (x : ℝ) : HasDerivAt profile (d x) x := by
    simpa only [d, profile, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_ofNat] using!
      (density_hasDerivAt x).ofReal_comp
  have hv (x : ℝ) : HasDerivAt v (z * v x) x := by
    simpa [v, mul_comm] using (((hasDerivAt_id (x : ℂ)).const_mul z).cexp).comp_ofReal
  have hsh (b : ℝ) : Integrable (fun x : ℝ ↦ profile (2 * x + b) * v x) :=
    weighted_integrable (profile_smooth.continuous.comp (by fun_prop)) (profile_shift_compact b) z
  have hp := weighted_integrable profile_smooth.continuous profile_compact z
  have hp' : Integrable (profile * fun x ↦ z * v x) := by
    convert hp.const_mul z using 1
    funext x; dsimp [v]; ring
  have hd' : Integrable (d * v) := by
    convert ((hsh 1).sub (hsh (-1))).const_mul 2 using 1
    funext x; dsimp [d]; rw [sub_eq_add_neg (2 * x) 1]; ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ ↦ hd x)
    (fun x _ ↦ hv x) hp' hd' hp
  have hl : (∫ x : ℝ, profile x * (z * v x)) = z * bilateralLaplace profile z := by
    rw [bilateralLaplace, ← integral_const_mul]
    congr 1; funext x; dsimp [v]; ring
  have hr : (∫ x : ℝ, d x * v x) = 2 * ((∫ x : ℝ, profile (2 * x + 1) * v x) -
      ∫ x : ℝ, profile (2 * x + (-1)) * v x) := by
    rw [← integral_sub (hsh 1) (hsh (-1)), ← integral_const_mul]
    congr 1; funext x; dsimp [d]; rw [sub_eq_add_neg (2 * x) 1]; ring
  rw [hl, hr] at h
  dsimp only [v] at h
  rw [laplace_affine, laplace_affine] at h
  push_cast at h
  simp only [mul_one, mul_neg, neg_neg] at h
  linear_combination h

private theorem laplace_zero_half {z : ℂ} (hz : z.re ≠ 0) (h : bilateralLaplace profile z = 0) :
    bilateralLaplace profile (z / 2) = 0 := by
  have he : Complex.exp (z / 2) ≠ Complex.exp (-z / 2) := by
    intro he
    have hn := congrArg norm he
    simp only [Complex.norm_exp] at hn
    replace hn := Real.exp_injective hn
    apply hz
    simp only [Complex.div_ofNat_re, Complex.neg_re] at hn
    linarith
  have hr := laplace_refinement z
  rw [h, mul_zero] at hr
  exact (mul_eq_zero.mp hr.symm).resolve_left (sub_ne_zero.mpr he)

private theorem laplace_ne_zero {z : ℂ} (hz : z.re ≠ 0) : bilateralLaplace profile z ≠ 0 := by
  intro h
  have hpow (n : ℕ) : bilateralLaplace profile (z * ((1 / 2 : ℂ) ^ n)) = 0 := by
    induction n with
    | zero => simpa using h
    | succ n ih =>
      rw [pow_succ, ← mul_assoc, mul_one_div]
      apply laplace_zero_half _ ih
      have he : z * ((1 / 2 : ℂ) ^ n) = z * ((((1 / 2 : ℝ) ^ n : ℝ) : ℂ)) := by push_cast; rfl
      rw [he]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_ne_zero hz (by positivity)
  have ht : Tendsto (fun n : ℕ ↦ z * ((1 / 2 : ℂ) ^ n)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℂ)‖ < 1)).const_mul z
  have hw : MemLp (fun x : ℝ ↦ Real.exp (1 * |x|) • profile x) 2 := by
    have hc : Continuous (fun x : ℝ ↦ Real.exp (1 * |x|)) := by fun_prop
    exact (hc.smul profile_smooth.continuous).memLp_of_hasCompactSupport
      (profile_compact.smul_left (f := fun x : ℝ ↦ Real.exp (1 * |x|)))
  have hlim := ((hasDerivAt_bilateralLaplace hw (z := 0) (by norm_num)).continuousAt.tendsto).comp ht
  have hz' : bilateralLaplace profile 0 = 0 := tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (.of_forall fun n ↦ (hpow n).symm))
  simp [bilateralLaplace, profile_integral] at hz'

end Fabius

/-- The Fabius probability density on `[-1,1]`, as a complex-valued log profile. -/
public def fabiusProfile : ℝ → ℂ := Fabius.profile

/-- The Fabius profile is a real, nonnegative, even, compact smooth weight of mass one. -/
public theorem fabiusProfile_properties :
    ContDiff ℝ ∞ fabiusProfile ∧ HasCompactSupport fabiusProfile ∧
    tsupport fabiusProfile ⊆ Icc (-1 : ℝ) 1 ∧
    (∀ x, (fabiusProfile x).im = 0 ∧ 0 ≤ (fabiusProfile x).re) ∧
    (∀ x, fabiusProfile (-x) = fabiusProfile x) ∧ fabiusProfile 0 = 1 ∧
    (∫ x : ℝ, fabiusProfile x) = 1 := by
  refine ⟨Fabius.profile_smooth, Fabius.profile_compact, ?_, fun x ↦ ⟨rfl, Fabius.density_nonneg x⟩,
    fun x ↦ congrArg Complex.ofReal (Fabius.density_even x), ?_, Fabius.profile_integral⟩
  · apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra ho
    apply hx
    change (Fabius.density x : ℂ) = 0
    rw [Fabius.density_eq_zero ho, Complex.ofReal_zero]
  · change (Fabius.cdf (0 + 1) - Fabius.cdf 0 : ℝ) = (1 : ℂ)
    rw [Fabius.cdf_of_one_le (by norm_num), Fabius.cdf_of_nonpos le_rfl]
    norm_num

/-- The differential equation for the Fabius density yields a dyadic Laplace recurrence. -/
public theorem bilateralLaplace_fabiusProfile_dyadic (z : ℂ) :
    z * bilateralLaplace fabiusProfile z =
      (Complex.exp (z / 2) - Complex.exp (-z / 2)) * bilateralLaplace fabiusProfile (z / 2) :=
  Fabius.laplace_refinement z

/-- One fixed compact smooth profile has nonzero Laplace coefficient at every point off the
imaginary axis. -/
public theorem bilateralLaplace_fabiusProfile_ne_zero {z : ℂ} (hz : z.re ≠ 0) :
    bilateralLaplace fabiusProfile z ≠ 0 :=
  Fabius.laplace_ne_zero hz

end RiemannMasullo
