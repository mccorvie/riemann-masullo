module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCentralHeatBounds
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatHeatCosineLimit
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalOrderZeroHeatTrace

/-!
# Removing the spatial floor from the mean-zero real-even heat trace

For the rational order-zero model of Step II, pp. 516–517, isolate the missing
rectangle before taking limits. The ambient estimate uses the finite cosine
kernel of #7646. The polar estimate uses its physical band vector and the
uniform estimate for the displaced polar row. The quotient statements use the
actual Chapter 9 test action and the native arithmetic level projections.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped CompactlySupported InnerProductSpace NNReal Topology

@[expose] public noncomputable section

namespace RiemannMasullo.FlatPolar

local notation "ν" => volume.restrict (Ioi (0 : ℝ))
local notation "H" => Lp ℂ 2 ν

/-- The ambient heat trace on the removed rectangle is bounded uniformly at every variance. -/
theorem norm_logHeat_ambient_spatialFloor_le {B h : ℝ}
    (hB : 0 ≤ B) (hh : 0 ≤ h) (τ : ℝ≥0) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    ‖hilbertTrace (logHeatSandwich τ (compactCosineTraceOperator 0 B 0 h φ))‖ ≤
      (4 * (B * h)) * ∫ a : ℝ≥0ˣ, ‖φ a‖ / Real.sqrt a.val ∂positiveRealHaar := by
  rw [hilbertTrace_logHeatSandwich_compactCosineTraceOperator]
  refine (norm_integral_le_of_norm_le_const (C := (4 * (B * h)) *
    ∫ a : ℝ≥0ˣ, ‖φ a‖ / Real.sqrt a.val ∂positiveRealHaar) ?_).trans_eq (by simp)
  exact .of_forall fun z ↦ by
    simpa only [expRadialUnit_coe] using norm_hilbertTrace_compactCosineShift_reducedBand_le
      φ (expRadialUnit z) hB (show (0:ℝ) ≤ 0 from le_rfl) hh

private theorem ray_floorMeasure (q : ℝ) : ν (Ioc 0 q) = ENNReal.ofReal q := by
  rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self,
    Real.volume_Ioc, sub_zero]

private theorem unitBand_inverseCosine_bound :
    ∀ᵐ x ∂ν, ‖positiveRayInverseCosine (bandVector 1) x‖ ≤ 2 := by
  have hfin : ν (Ioc (0 : ℝ) 1) ≠ ⊤ := by rw [ray_floorMeasure]; exact ENNReal.ofReal_ne_top
  have hi : Integrable (fun t ↦ bandVector 1 t) ν := by
    have hc : IntegrableOn (fun _ : ℝ ↦ (Real.sqrt 1 : ℂ)⁻¹) (Ioc 0 1) ν :=
      integrableOn_const hfin
    have hp : Integrable (bandProfile 1) ν := (integrable_indicator_iff measurableSet_Ioc).mpr hc
    exact hp.congr (bandVector_ae_eq 1).symm
  filter_upwards [positiveRayInverseCosine_eq_integral (bandVector 1) hi] with x hx
  rw [hx]
  let k (t : ℝ) : ℂ := 2 * (Real.cos (2 * Real.pi * (t * x)) : ℂ)
  have he : (∫ t, k t * bandVector 1 t ∂ν) = ∫ t in Ioc 0 1, k t ∂ν := by
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [bandVector_ae_eq 1] with t ht
    by_cases h : t ∈ Ioc (0 : ℝ) 1 <;> simp [ht, bandProfile, h]
  change ‖∫ t, k t * bandVector 1 t ∂ν‖ ≤ 2
  rw [he]
  refine (norm_setIntegral_le_of_norm_le_const (C := 2) hfin.lt_top (fun t _ ↦ ?_)).trans_eq ?_
  · dsimp only [k]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (2 * Real.pi * (t*x))) (by norm_num : (0:ℝ) ≤ 2)
  · simp [Measure.real]

private theorem norm_spatialFloor_unitBand (q : ℝ) (hq : 0 ≤ q) :
    ‖spatialCutoff 0 q (positiveRayInverseCosine (bandVector 1))‖ ≤ 2 * Real.sqrt q := by
  have hf : ν (Ioc 0 q) ≠ ⊤ := by rw [ray_floorMeasure]; exact ENNReal.ofReal_ne_top
  let v : H := indicatorConstLp 2 measurableSet_Ioc hf (2 : ℂ)
  have hv : (v : ℝ → ℂ) =ᵐ[ν] (Ioc 0 q).indicator (fun _ ↦ (2 : ℂ)) :=
    indicatorConstLp_coeFn
  calc
    _ ≤ ‖v‖ := Lp.norm_le_norm_of_ae_le (by
      filter_upwards [spatialCutoff_apply 0 q (positiveRayInverseCosine (bandVector 1)), hv,
        unitBand_inverseCosine_bound] with x hc hvx hu
      rw [hc, hvx]
      by_cases hx : x ∈ Ioc 0 q
      · simpa only [indicator_of_mem hx, Complex.norm_ofNat] using hu
      · simp [hx])
    _ = _ := by
      rw [show ‖v‖ = _ from norm_indicatorConstLp (by norm_num) (by norm_num)]
      norm_num [Measure.real, ENNReal.toReal_ofReal hq, Real.sqrt_eq_rpow, one_div]

/-- The removed part of the physical normalized polar vector has norm at most
twice the square root of the area of the missing spatial-frequency rectangle. -/
theorem norm_spatialFloor_inverseCosine_bandVector_le {B h : ℝ} (hB : 0 < B) (hh : 0 ≤ h) :
    ‖spatialCutoff 0 h (positiveRayInverseCosine (bandVector B))‖ ≤ 2 * Real.sqrt (B*h) := by
  have he := (congrArg positiveRayInverseCosine (bandVector_eq_inverse_dilation B hB)).trans
    (show positiveRayInverseCosine (positiveRayDilation B⁻¹ (inv_pos.mpr hB) (bandVector 1)) =
      positiveRayDilation B hB (positiveRayInverseCosine (bandVector 1)) by
        simpa only [inv_inv] using positiveRayInverseCosine_dilation B⁻¹ (inv_pos.mpr hB) (bandVector 1))
  rw [he, spatialCutoff_positiveRayDilation, LinearIsometryEquiv.norm_map, mul_zero]
  exact norm_spatialFloor_unitBand _ (mul_nonneg hB.le hh)

private theorem logHeatSandwich_at_zero (A : nuclearEndomorphisms H) : logHeatSandwich 0 A = A := by
  have h0 (v : H) : logHeat 0 v = v := by simp [logHeat_apply, logDilation_zero]
  apply Subtype.ext
  ext v : 1
  change logHeat 0 (A.val (logHeat 0 v)) = A.val v
  rw [h0, h0]

private theorem trace_sub (A D : nuclearEndomorphisms H) :
    hilbertTrace (A - D) = hilbertTrace A - hilbertTrace D := by
  obtain ⟨f, hf⟩ := hilbertTrace_linear («H» := H)
  rw [← hf, map_sub, hf, hf]

private theorem coldCorrection_spatialFloor {B : ℝ} (hB : 0 < B) (h : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    hilbertTrace (logHeatSandwich 0 (meanZeroCompactCosineTraceOperator 0 h B φ)) -
      hilbertTrace (logHeatSandwich 0 (compactCosineTraceOperator 0 B 0 h φ)) =
      -⟪positiveRayInverseCosine (bandVector B), spatialCutoff 0 h
        (positiveRayInverseCosine (compactDilationAction φ (bandVector B)))⟫_ℂ := by
  let V := positiveRayInverseCosine
  let T := (spatialCutoffInChart V 0 h).comp (compactDilationAction φ)
  obtain ⟨Q, hQ, htr⟩ := polarFree_compression_difference T (frequencyBand B)
    (norm_bandVector hB) (bandVector_mem_frequencyBand B)
  have he : Q = meanZeroCompactCosineTraceOperator 0 h B φ -
      compactCosineTraceOperator 0 B 0 h φ := by
    apply Subtype.ext
    rw [Submodule.coe_sub, hQ, frequencyBand_starProjection_sub_line,
      meanZeroCompactCosineTraceOperator_val, compactCosineTraceOperator_frequencyBand_eq]
    rfl
  rw [logHeatSandwich_at_zero, logHeatSandwich_at_zero, ← trace_sub, ← he, htr]
  exact congrArg Neg.neg (V.toContinuousLinearMap.adjoint_inner_right (bandVector B) _)

/-- The finite-frequency, physical mean-zero heat compression of the deleted
spatial rectangle is small jointly in its area and the heat time. -/
theorem norm_meanZero_heatTrace_spatialFloor_le {B h : ℝ} (hB : 0 < B) (hh : 0 ≤ h)
    (τ : ℝ≥0) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    ‖hilbertTrace (logHeatSandwich τ (meanZeroCompactCosineTraceOperator 0 h B φ))‖ ≤
      (4 * (B * h)) * (∫ a : ℝ≥0ˣ, ‖φ a‖ / Real.sqrt a.val ∂positiveRealHaar) +
        2 * ‖compactDilationAction φ‖ * (Real.sqrt (B*h) + Real.sqrt (Real.sqrt ((τ+τ : ℝ≥0) : ℝ))) := by
  let M (s : ℝ≥0) := hilbertTrace (logHeatSandwich s (meanZeroCompactCosineTraceOperator 0 h B φ))
  let A (s : ℝ≥0) := hilbertTrace (logHeatSandwich s (compactCosineTraceOperator 0 B 0 h φ))
  have hc : ‖M 0 - A 0‖ ≤ (2 * Real.sqrt (B*h)) * ‖compactDilationAction φ‖ := by
    rw [show M 0 - A 0 = _ from coldCorrection_spatialFloor hB h φ, norm_neg, ← inner_spatialCutoff]
    refine (norm_inner_le_norm _ _).trans (mul_le_mul (norm_spatialFloor_inverseCosine_bandVector_le hB hh)
      ?_ (norm_nonneg _) (by positivity))
    rw [positiveRayInverseCosine.norm_map]
    simpa only [norm_bandVector hB, mul_one] using (compactDilationAction φ).le_opNorm (bandVector B)
  have hs := centralWindow_meanZeroHeat_cold_difference hB 0 h τ φ
  change ‖(M τ - A τ) - (M 0 - A 0)‖ ≤ _ at hs
  have ha := norm_logHeat_ambient_spatialFloor_le hB.le hh τ φ
  change ‖A τ‖ ≤ _ at ha
  change ‖M τ‖ ≤ _
  calc
    _ = ‖A τ + (M 0 - A 0) + ((M τ - A τ) - (M 0 - A 0))‖ := by congr 1; abel
    _ ≤ ‖A τ‖ + ‖M 0 - A 0‖ + ‖(M τ - A τ) - (M 0 - A 0)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := (add_le_add (add_le_add ha hc) hs).trans_eq (by ring)

private theorem spatialCutoff_split_at {h L : ℝ} (hh : 0 ≤ h) (hL : h ≤ L) (v : H) :
    spatialCutoff 0 L v = spatialCutoff h L v + spatialCutoff 0 h v := by
  apply Lp.ext
  filter_upwards [spatialCutoff_apply 0 L v, spatialCutoff_apply h L v, spatialCutoff_apply 0 h v,
    Lp.coeFn_add (spatialCutoff h L v) (spatialCutoff 0 h v)] with x hall hhi hlo hsum
  rw [hsum, Pi.add_apply, hall, hhi, hlo]
  by_cases hx : x ≤ 0
  · simp [show x ∉ Ioc 0 L from fun hx' ↦ (not_lt.mpr hx) hx'.1,
      show x ∉ Ioc h L from fun hx' ↦ (not_lt.mpr (hx.trans hh)) hx'.1,
      show x ∉ Ioc 0 h from fun hx' ↦ (not_lt.mpr hx) hx'.1]
  · have hx0 := lt_of_not_ge hx
    rcases le_or_gt x h with hxh | hxh
    · simp [show x ∈ Ioc 0 L from ⟨hx0, hxh.trans hL⟩,
        show x ∉ Ioc h L from fun hx' ↦ (not_lt.mpr hxh) hx'.1,
        show x ∈ Ioc 0 h from ⟨hx0, hxh⟩]
    · by_cases hxL : x ≤ L
      · simp [show x ∈ Ioc 0 L from ⟨hx0, hxL⟩, show x ∈ Ioc h L from ⟨hxh, hxL⟩,
          show x ∉ Ioc 0 h from fun hx' ↦ hxh.not_ge hx'.2]
      · simp [show x ∉ Ioc 0 L from fun hx' ↦ hxL hx'.2, show x ∉ Ioc h L from fun hx' ↦ hxL hx'.2,
          show x ∉ Ioc 0 h from fun hx' ↦ hxh.not_ge hx'.2]

private theorem meanZeroCompactCosineTraceOperator_spatialFloor {h L : ℝ} (hh : 0 ≤ h) (hL : h ≤ L)
    (B : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    meanZeroCompactCosineTraceOperator 0 L B φ - meanZeroCompactCosineTraceOperator h L B φ =
      meanZeroCompactCosineTraceOperator 0 h B φ := by
  apply Subtype.ext
  ext v : 1
  simp only [Submodule.coe_sub, sub_apply, meanZeroCompactCosineTraceOperator_val,
    spatialCutoffInChart, ContinuousLinearMap.comp_apply]
  rw [spatialCutoff_split_at hh hL, map_add, map_add, add_sub_cancel_left]

/-- Quantitative moving-floor estimate for the two actual finite heat traces. -/
theorem norm_meanZero_heatTrace_remove_spatialFloor_le {B h L : ℝ}
    (hB : 0 < B) (hh : 0 ≤ h) (hL : h ≤ L) (τ : ℝ≥0) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    ‖hilbertTrace (logHeatSandwich τ (meanZeroCompactCosineTraceOperator 0 L B φ)) -
      hilbertTrace (logHeatSandwich τ (meanZeroCompactCosineTraceOperator h L B φ))‖ ≤
      (4 * (B*h)) * (∫ a : ℝ≥0ˣ, ‖φ a‖ / Real.sqrt a.val ∂positiveRealHaar) +
        2 * ‖compactDilationAction φ‖ * (Real.sqrt (B*h) + Real.sqrt (Real.sqrt ((τ+τ : ℝ≥0) : ℝ))) := by
  rw [← trace_sub, ← map_sub, meanZeroCompactCosineTraceOperator_spatialFloor hh hL]
  exact norm_meanZero_heatTrace_spatialFloor_le hB hh τ φ

/-- At zero heat this is the corresponding bound for the ordinary nuclear traces. -/
theorem norm_meanZero_coldTrace_remove_spatialFloor_le {B h L : ℝ}
    (hB : 0 < B) (hh : 0 ≤ h) (hL : h ≤ L) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    ‖hilbertTrace (meanZeroCompactCosineTraceOperator 0 L B φ) -
      hilbertTrace (meanZeroCompactCosineTraceOperator h L B φ)‖ ≤
      (4 * (B*h)) * (∫ a : ℝ≥0ˣ, ‖φ a‖ / Real.sqrt a.val ∂positiveRealHaar) +
        2 * ‖compactDilationAction φ‖ * Real.sqrt (B*h) := by
  simpa only [logHeatSandwich_at_zero, add_zero, NNReal.coe_zero, Real.sqrt_zero] using
    norm_meanZero_heatTrace_remove_spatialFloor_le hB hh hL 0 φ

/-- At the actual two-sided mean-zero compression, opening the spatial floor
changes the heated trace by a quantity tending to zero for any compact complex
test. Both endpoints can move independently of the heat time. -/
theorem tendsto_meanZero_heatTrace_remove_spatialFloor {ι : Type*} {l : Filter ι}
    {B h L : ι → ℝ} {τ : ι → ℝ≥0} (hB : ∀ i, 0 < B i)
    (hbox : ∀ᶠ i in l, 0 ≤ h i ∧ h i ≤ L i)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hτ : Tendsto τ l (𝓝 0))
    (φ : C_c(ℝ≥0ˣ, ℂ)) :
    Tendsto (fun i ↦ hilbertTrace (logHeatSandwich (τ i) (meanZeroCompactCosineTraceOperator 0 (L i) (B i) φ)) -
      hilbertTrace (logHeatSandwich (τ i) (meanZeroCompactCosineTraceOperator (h i) (L i) (B i) φ))) l (𝓝 0) := by
  let C := ∫ a : ℝ≥0ˣ, ‖φ a‖ / Real.sqrt a.val ∂positiveRealHaar
  have hτ' : Tendsto (fun i ↦ ((τ i + τ i : ℝ≥0) : ℝ)) l (𝓝 0) := by
    have hreal : Tendsto (fun i ↦ (τ i : ℝ)) l (𝓝 0) := (NNReal.continuous_coe.tendsto 0).comp hτ
    simpa only [NNReal.coe_add, add_zero] using hreal.add hreal
  have hb' := ((hBh.const_mul (4:ℝ)).mul_const C).add
    ((hBh.sqrt.add hτ'.sqrt.sqrt).const_mul (2 * ‖compactDilationAction φ‖))
  have hb : Tendsto (fun i ↦ (4 * (B i * h i)) * C + 2 * ‖compactDilationAction φ‖ *
      (Real.sqrt (B i * h i) + Real.sqrt (Real.sqrt ((τ i + τ i : ℝ≥0) : ℝ)))) l (𝓝 0) := by
    simpa using hb'
  apply squeeze_zero_norm' _ hb
  filter_upwards [hbox] with i hi
  exact norm_meanZero_heatTrace_remove_spatialFloor_le (hB i) hi.1 hi.2 (τ i) φ

end RiemannMasullo.FlatPolar

namespace RiemannMasullo.AnnularBand

open FlatPolar NumberField IsDedekindDomain
open scoped NumberField.AdeleRing
attribute [local instance] RiemannMasullo.instSIdeleQuotientMeasurableSpaceSec1

local notation "J" => SIdeleQuotient ℚ ∅
local notation "μ" => sLocalQuotientTamagawaMeasure ℚ ∅

local instance : T2Space J := by
  have := isClosed_sProjectedDiagonal (F := ℚ) (S := ∅)
  exact inferInstanceAs (T2Space (_ ⧸ _))
local instance : LocallyCompactSpace J := by
  let : LocallyCompactSpace (SAdeleRing ℚ ∅)ˣ := (sIdeleGroup_description ℚ ∅).2.2.1
  exact inferInstanceAs (LocallyCompactSpace (_ ⧸ _))
local instance : BorelSpace J := ⟨rfl⟩

set_option maxHeartbeats 1400000 in
/-- For every compact quotient Bruhat test, the actual arithmetic mean-zero
heat trace has the same limit with or without the moving spatial floor. -/
theorem tendsto_quotientBruhatLevel_heatTrace_remove_spatialFloor {ι : Type*} {l : Filter ι}
    {B h L : ι → ℝ} {τ : ι → ℝ≥0} (hB : ∀ i, 0 < B i)
    (hbox : ∀ᶠ i in l, 0 ≤ h i ∧ h i ≤ L i)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hτ : Tendsto τ l (𝓝 0))
    (ψ : BruhatCompactSupport J) :
    Tendsto (fun i ↦ hilbertTrace (quotientLogHeatSandwich (τ i)
      (quotientBruhatLevelCompressionNuclear (hB i) 0 (L i) ψ)) -
      hilbertTrace (quotientLogHeatSandwich (τ i)
        (quotientBruhatLevelCompressionNuclear (hB i) (h i) (L i) ψ))) l (𝓝 0) := by
  obtain ⟨φ, -, -, hA⟩ := exists_rayTest_support_hardySobolevTestAction_eq ψ univ isClosed_univ
    (fun _ _ ↦ mem_univ _)
  have hn (i : ι) (j : ℝ) : quotientBruhatLevelCompressionNuclear (hB i) j (L i) ψ =
      quotientMeanZeroCompactNuclear (hB i) j (L i) φ := by
    apply Subtype.ext
    change quotientBruhatLevelCompression (B i) j (L i) ψ = quotientMeanZeroCompact (B i) j (L i) φ
    unfold quotientBruhatLevelCompression quotientMeanZeroCompact
    rw [hA]
  simpa only [hn, hilbertTrace_quotientLogHeatSandwich_meanZeroCompact] using
    tendsto_meanZero_heatTrace_remove_spatialFloor hB hbox hBh hτ φ

/-- At positive variances the integrated Haar heat diagonals of the same two
native compressions differ by a quantity tending to zero. -/
theorem tendsto_quotientBruhatLevel_haarDiagonal_remove_spatialFloor {ι : Type*} {l : Filter ι}
    {B h L : ι → ℝ} {τ : ι → ℝ≥0} (hB : ∀ i, 0 < B i)
    (hbox : ∀ᶠ i in l, 0 ≤ h i ∧ h i ≤ L i)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hτ : Tendsto τ l (𝓝 0))
    (hpos : ∀ᶠ i in l, 0 < τ i) (ψ : BruhatCompactSupport J) :
    Tendsto (fun i ↦ (∫ q : J, quotientLogHaarHeatKernel (τ i)
      (quotientBruhatLevelCompression (B i) 0 (L i) ψ) q q ∂μ) -
      (∫ q : J, quotientLogHaarHeatKernel (τ i)
        (quotientBruhatLevelCompression (B i) (h i) (L i) ψ) q q ∂μ)) l (𝓝 0) := by
  apply (tendsto_quotientBruhatLevel_heatTrace_remove_spatialFloor hB hbox hBh hτ ψ).congr'
  filter_upwards [hpos] with i hi
  exact congrArg₂ (fun a b : ℂ ↦ a-b)
    (quotientLogHaarHeatKernel_diagonal_trace hi (quotientBruhatLevelCompressionNuclear (hB i) 0 (L i) ψ)).2.symm
    (quotientLogHaarHeatKernel_diagonal_trace hi (quotientBruhatLevelCompressionNuclear (hB i) (h i) (L i) ψ)).2.symm

end RiemannMasullo.AnnularBand
