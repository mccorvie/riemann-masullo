module

public import RiemannMasullo.AppB_AnalyticNT.HeckeFiniteHardyGreen
public import RiemannMasullo.AppB_AnalyticNT.HeckeFiniteLogGreen
public import RiemannMasullo.ForMathlib.Analysis.Complex.ClippedPolynomialPredictor
public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.LogHeightClipping
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.HardyGridPerturbation
public import RiemannMasullo.ForMathlib.Analysis.Asymptotics.ClippedGridRate
import Mathlib.Tactic

/-! # Rate for the corrected finite-ideal Hardy residual

Use the original Gaussian-rational coefficient grid and the fixed scalar-one Cayley model
centered at two. For each normalized unitary Hecke character, every sufficiently large
fixed disk exponent gives a one-sided error of order exp(−c√log n), both for the squared
distance and for its logarithmic Green upper. The constants and onset can depend on
the field, character and fixed exponent. -/

@[expose] public noncomputable section

section

open Complex Filter Function MeasureTheory NumberField Set Real
open scoped NNReal Topology ENNReal

namespace RiemannMasullo.LogQuadrature

open HeckeDiskNormalization HalfPlaneJensen PolynomialIdealSamples HeckeBoundaryGreen
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽

private theorem half_add_ordinate (t : ℝ) : (1/2 : ℂ) + (t : ℂ) * I = point t := by
  apply Complex.ext <;> simp [point, Complex.mul_re, Complex.mul_im]

private theorem continuous_criticalLinePoint : Continuous point := by
  rw [show point = (fun t : ℝ ↦ (1/2 : ℂ) + (t : ℂ) * I) from
    funext (fun t ↦ (half_add_ordinate t).symm)]
  fun_prop

private theorem norm_point_add_one (t : ℝ) :
    1 ≤ ‖point t+1‖ ∧ ‖point t+1‖ ≤ 2+|t| := by
  have hl := Complex.abs_re_le_norm (point t+1)
  have hu := Complex.norm_le_abs_re_add_abs_im (point t+1)
  norm_num [point,Complex.add_re,Complex.add_im] at hl hu
  unfold point
  constructor <;> linarith

/-- The pole-clearing quotient has norm one on the actual critical line.
The remaining factor in the disk boundary modulus is the stated power of s+1. -/
theorem normalized_norm_inverseAngle (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1)
    (N : ℕ) (t : ℝ) :
    let L := (finiteHeckeL_exists_continuation χ).choose
    ‖normalized χ L 1 N (circleMap 0 1 (CayleyCauchy.inverseAngle (3/2) t))‖ =
      ‖L (point t)‖ / ‖point t+1‖^N := by
  let L := (finiteHeckeL_exists_continuation χ).choose
  let z := circleMap 0 1 (CayleyCauchy.inverseAngle (3/2) t)
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hcoord : toHalf z = point t := by
    have h := CayleyCauchy.two_add_div_one_sub_inverseAngle t
    change (2+z)/(1-z) = (1/2 : ℂ)+(t:ℂ)*I at h
    rw [toHalf, h, half_add_ordinate]
  have h1 : 1-z ≠ 0 := fun h ↦ by
    have hr := congrArg Complex.re hcoord
    simp [toHalf,h,point] at hr
  have hf : (1-z)/3 = (point t+1)⁻¹ := by
    rw [← hcoord,chart_add_one h1,inv_div]
  change ‖normalized χ L 1 N z‖ = ‖L (point t)‖ / ‖point t+1‖^N
  rw [normalized, hcoord, hf, Complex.ofReal_one, one_mul, norm_mul, norm_pow, norm_inv,
    HeckeVerticalDisk.norm_cleared_of_re_half τ hτ χ hχ L hL he (by norm_num [point] : (point t).re = 1/2),
    inv_pow, div_eq_inv_mul]

/-- Absolute boundary logarithms of the normalized Hecke disk model have
square-root-exponential integrated tails in the physical Cauchy coordinate. -/
theorem integrable_and_hasIntegratedLogTail_normalized_inverseAngle (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1)
    (N : ℕ) :
    let L := (finiteHeckeL_exists_continuation χ).choose
    let u := fun t ↦ Real.log ‖normalized χ L 1 N (circleMap 0 1 (CayleyCauchy.inverseAngle (3/2) t))‖
    Integrable u poissonMeasure ∧ HasIntegratedLogTail poissonMeasure u := by
  let L := (finiteHeckeL_exists_continuation χ).choose
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  let v := fun t ↦ Real.log (‖L (point t)‖ / ‖point t+1‖^N)
  have hm : (fun t ↦ Real.log
      ‖normalized χ L 1 N (circleMap 0 1 (CayleyCauchy.inverseAngle (3/2) t))‖) = v := by
    funext t
    exact congrArg Real.log (normalized_norm_inverseAngle τ hτ χ hχ N t)
  dsimp only
  rw [hm]
  have hcont := (hecke_critical_deriv_polynomial τ hτ χ hχ L hL he).1.continuous
  have hmeas : Measurable v :=
    Real.measurable_log.comp (hcont.measurable.norm.div (((continuous_criticalLinePoint.add continuous_const).norm.pow N).measurable))
  have hg : Integrable (fun t ↦ Real.log ‖L (point t)‖) poissonMeasure := by
    apply (poisson_integrable_iff _).mpr
    have hi := (integrable_weightedLog_and_green τ hτ χ hχ L hL he).1
    convert hi using 1
    funext t
    simp only [HeckeBoundaryGreen.weightedLog,poissonWeight,half_add_ordinate]
  apply integrable_and_hasIntegratedLogTail_of_logHeight_majorant N hmeas hg _ (criticalLog_dyadic_tail τ hτ χ hχ)
  intro t
  have hb := norm_point_add_one t
  have hp : 0 < ‖point t+1‖ := by linarith [hb.1]
  by_cases hz : L (point t)=0
  · simp [v,hz]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith [abs_nonneg t]))
  · rw [show v t = Real.log ‖L (point t)‖ - (N:ℝ)*Real.log ‖point t+1‖ by
      dsimp only [v]
      rw [Real.log_div (norm_ne_zero_iff.mpr hz) (pow_pos hp N).ne',Real.log_pow]]
    calc
      _ ≤ |Real.log ‖L (point t)‖| + |(N:ℝ)*Real.log ‖point t+1‖| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hb.1))]
        exact add_le_add_right (mul_le_mul_of_nonneg_left (Real.log_le_log hp hb.2) (Nat.cast_nonneg _)) _

/-- Upward clipping at a floor of exp(-Y) changes the disk average by at most
a square-root-exponential tail for every exponent in the actual Hecke model. -/
theorem normalized_clipped_boundary_mean_rate (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1)
    (N : ℕ) :
    let L := (finiteHeckeL_exists_continuation χ).choose
    let f := normalized χ L 1 N
    ∃ C > 0, ∃ c > 0, ∀ᶠ Y : ℝ in atTop,
      Real.circleAverage (fun z ↦ Real.log (max ‖f z‖ (Real.exp (-Y))) - Real.log ‖f z‖) 0 1 ≤
        C * Real.exp (-c * Real.sqrt Y) := by
  let L := (finiteHeckeL_exists_continuation χ).choose
  let f := normalized χ L 1 N
  let u := fun t ↦ ‖f (circleMap 0 1 (CayleyCauchy.inverseAngle (3/2) t))‖
  obtain ⟨hi,A,hA,c,hc,hb⟩ := integrable_and_hasIntegratedLogTail_normalized_inverseAngle τ hτ χ hχ N
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hcont := (hecke_critical_deriv_polynomial τ hτ χ hχ L hL he).1.continuous
  have hu : Measurable u := by
    have h : u = fun t ↦ ‖L (point t)‖ / ‖point t+1‖^N := funext (normalized_norm_inverseAngle τ hτ χ hχ N)
    rw [h]
    exact hcont.measurable.norm.div ((continuous_criticalLinePoint.add continuous_const).norm.pow N).measurable
  refine ⟨A,hA,c,hc,?_⟩
  filter_upwards [hb,eventually_ge_atTop (0:ℝ)] with Y hbound hY
  change Real.circleAverage (fun z ↦ Real.log (max ‖f z‖ (Real.exp (-Y))) - Real.log ‖f z‖) 0 1 ≤ _
  rw [CayleyCauchy.circleAverage_inverseAngle (by norm_num : (0:ℝ)<3/2)]
  change (∫ t, poissonWeight t * (Real.log (max (u t) (Real.exp (-Y))) - Real.log (u t))) ≤ _
  rw [←poisson_integral]
  exact (integral_log_floor_sub_le_abs_tail hu (fun t ↦ norm_nonneg _) hi hY).trans hbound

end RiemannMasullo.LogQuadrature

end

section

open Real HardyTable Filter Finset Set
open scoped Topology

open Complex NumberField Function Metric
open scoped NNReal

namespace RiemannMasullo.HeckeHardyGreen

open HeckeDiskNormalization HeckeHardyDisk FiniteHardyIdealTable HeckeBoundaryGreen
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽

/-- The finite Gaussian-rational grid differs from the true norm of any
feasible trial by at most a fixed inverse square root, uniformly in the trial. -/
theorem eventually_sqrt_gridUpperArgument_le_trial (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1)
    {N : ℕ} (hN : tableExponent τ hτ χ hχ ≤ N) :
    let f := normalized χ (finiteHeckeL_exists_continuation χ).choose 1 N
    ∃ K > 0, ∀ᶠ n : ℕ in atTop, ∀ p : Coeff n, p ∈ ellipsoid n →
      Real.sqrt (gridUpperArgument χ N n) ≤
        Real.sqrt (Real.circleAverage (fun z ↦ ‖1-f z*(HardyBoundary.tablePolynomial p).eval z‖^2) 0 1)
          + K/Real.sqrt ((n:ℝ)+1) := by
  let f := normalized χ (finiteHeckeL_exists_continuation χ).choose 1 N
  obtain ⟨hf,hc⟩ := (canonical_diskAlgebra_control τ hτ χ hχ).choose_spec.2 N ((le_max_left _ _).trans hN)
  let c := HardySzego.diskCoefficients f hf
  have hD : DerivativeBound c (16/9) := ⟨by norm_num,hc.energy_summable,hc.energy_le⟩
  have hexp := HardyBoundary.expands_of_coefficients hD hf (fun j ↦ rfl)
  have hcts := hf.continuousOn
  rw [closure_ball _ one_ne_zero] at hcts
  let A := 1+‖c‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨4*A+6, by positivity, ?_⟩
  filter_upwards [eventually_ideal_entry_error τ hτ χ hχ N] with n hn
  intro p hp
  let a := extendRow (linearRow χ N n)
  let ε := (1/2:ℝ)^(2*linearCut n)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have herr (j : ℕ) (hj : j ≤ linearCut n) : ‖a j-c j‖ ≤ ε := by
    rw [show c j = DiskCoefficientEnergy.coeff f j by rfl]
    simpa only [a,f,ε,extendRow,dite_eq_left (Nat.lt_succ_of_le hj)] using hn ⟨j,Nat.lt_succ_of_le hj⟩
  have hnorm (j : ℕ) (hj : j ≤ linearCut n) : ‖a j‖ ≤ A := by
    have hh := lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0) c j
    calc
      _ ≤ ‖a j-c j‖+‖c j‖ := norm_le_norm_sub_add _ _
      _ ≤ ε+‖c‖ := add_le_add (herr j hj) hh
      _ ≤ _ := add_le_add_left (pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)) _
  have hgrid := gridNorm_le_trial_of_row_error n a c hA hnorm hε herr p hp
  have hpval := HardyBoundary.table_residual_parseval hexp (hcts.mono sphere_subset_closedBall) p
  change Real.sqrt ((gridNorm n a + rowError n ε)^2) ≤ Real.sqrt _ + _
  rw [Real.sqrt_sq (by
    have hh : 0 ≤ gridNorm n a := (Real.sqrt_nonneg _).trans (sqrt_le_gridNorm n a)
    unfold rowError
    positivity),hpval,Real.sqrt_sq (norm_nonneg _)]
  have hd := canonical_row_visible_error_le n
  have hnpos : 0 < (n:ℝ)+1 := by positivity
  have hspos := Real.sqrt_pos.mpr hnpos
  have hsle : Real.sqrt ((n:ℝ)+1) ≤ (n:ℝ)+1 :=
    Real.sqrt_le_iff.mpr ⟨hnpos.le,by nlinarith [Nat.cast_nonneg (α:=ℝ) n, sq_nonneg (n:ℝ)]⟩
  have hround : 4*A/((n:ℝ)+1) ≤ 4*A/Real.sqrt ((n:ℝ)+1) :=
    div_le_div_of_nonneg_left (by positivity) hspos hsle
  change 2*Real.sqrt (((n:ℝ)+1)*((linearCut n:ℝ)+1))*ε ≤ _ at hd
  unfold rowError
  rw [add_div]
  have hconst : 2*(1/Real.sqrt ((n:ℝ)+1)) + 2*(16/9)/Real.sqrt ((n:ℝ)+1) ≤
      6/Real.sqrt ((n:ℝ)+1) := by
    rw [mul_div_assoc',←add_div]
    exact div_le_div_of_nonneg_right (by norm_num) hspos.le
  linarith

end RiemannMasullo.HeckeHardyGreen

end

open Complex Real Metric Set HardyTable HardyBoundary HardySzego

namespace RiemannMasullo.HeckeHardyDisk

/-- A disk function with the Hecke norm and derivative bounds has a feasible clipped
predictor as soon as its weighted coefficient budget fits the finite ellipsoid. -/
theorem HardyControl.exists_clipped_ellipsoid_predictor {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1))
    (hc : RiemannMasullo.HeckeHardyDisk.HardyControl F) {Y τ : ℝ}
    (hY : 0 ≤ Y) (ht : 0 < τ) (n : ℕ)
    (hn : (3370/81:ℝ)*Real.exp (4*Y) ≤ (n:ℝ)+1) :
    ∃ p ∈ ellipsoid n, circleAverage (fun z ↦ ‖1-F z*(tablePolynomial p).eval z‖^2) 0 1 ≤
      (1+τ)*(1-Real.exp (-2*logGap F)+2*circleAverage
        (fun z ↦ clippedLog F Y z-Real.log ‖F z‖) 0 1)+
      (1+τ⁻¹)*((3370/81:ℝ)*Real.exp (4*Y)/((n:ℝ)+1)^2) := by
  have hd (z : ℂ) (hz : z ∈ ball 0 1) : ‖deriv F z‖ ≤ 16/9 := by
    have hz' : ‖z‖ < 1 := by simpa using hz
    exact hc.deriv_le z hz'.le (fun h ↦ by simp [h] at hz')
  have hN (z : ℂ) (hz : z ∈ sphere 0 1) : ‖F z‖ ≤ 1 :=
    hc.norm_le z (mem_sphere_zero_iff_norm.mp hz).le
  have hconst : 10*(1+(16/9:ℝ)^2) = 3370/81 := by norm_num
  have h := HardySzego.exists_clipped_ellipsoid_predictor hF hc.nonzero_center (by norm_num : (0:ℝ) ≤ 16/9)
    hd hN hY ht n (by rwa [hconst])
  rw [hconst,disk_distance_sq hF hc.nonzero_center] at h
  rw [← clippingLoss_eq_circleAverage_sub hF hc.nonzero_center]
  exact h

end RiemannMasullo.HeckeHardyDisk

open Filter Function NumberField
open scoped NNReal Topology

namespace RiemannMasullo.HeckeHardyGreen

open HeckeDiskNormalization HeckeHardyDisk HeckeBoundaryGreen LogQuadrature
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽

/-- The genuine squared Hardy distance is a lower bound for every sufficiently
late finite ideal grid. Its one-sided error decays at a root-log rate. -/
theorem gridUpperArgument_rate (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) {N : ℕ} (hN : tableExponent τ hτ χ hχ ≤ N) :
    let R := 1-Real.exp (-2*criticalLogDifference χ)
    (∀ᶠ n : ℕ in atTop, R ≤ gridUpperArgument χ N n) ∧
      HasRootLogRate (fun n ↦ gridUpperArgument χ N n-R) := by
  let f := normalized χ (finiteHeckeL_exists_continuation χ).choose 1 N
  let R := 1-Real.exp (-2*criticalLogDifference χ)
  let u := gridUpperArgument χ N
  let L := fun Y ↦ Real.circleAverage (fun z ↦ clippedLog f Y z-Real.log ‖f z‖) 0 1
  obtain ⟨hf,hc⟩ := (canonical_diskAlgebra_control τ hτ χ hχ).choose_spec.2 N ((le_max_left _ _).trans hN)
  have hphysical := grid_upper_recovers_green τ hτ χ hχ hN
  have hlow : ∀ᶠ n : ℕ in atTop, R ≤ u n ∧ u n ≤ 1 := by
    filter_upwards [hphysical.1] with n hn
    have hu : u n < 1 := hn.1
    have hlog : Real.log (1-u n) ≤ -2*criticalLogDifference χ := by
      have ht := hn.2
      change criticalLogDifference χ ≤ -Real.log (1-u n)/2 at ht
      linarith
    have hh := Real.exp_monotone hlog
    rw [Real.exp_log (by linarith)] at hh
    exact ⟨by dsimp [R]; linarith,hu.le⟩
  have hgap : logGap f = criticalLogDifference χ := canonical_logGap τ hτ χ hχ N
  have hR : 0≤R := by
    have h := disk_distance_sq hf hc.nonzero_center
    rw [show logGap (normalized χ (finiteHeckeL_exists_continuation χ).choose 1 N)=criticalLogDifference χ from hgap] at h
    change 0 ≤ 1-Real.exp (-2*criticalLogDifference χ)
    rw [←h]
    exact sq_nonneg _
  have hR1 : R≤1 := by dsimp [R]; linarith [Real.exp_pos (-2*criticalLogDifference χ)]
  have hclip : ∃ A>0, ∃ c>0, ∀ᶠ Y : ℝ in atTop, L Y ≤ A*Real.exp (-c*Real.sqrt Y) := by
    simpa only [L,f,clippedLog,max_comm] using normalized_clipped_boundary_mean_rate τ hτ χ hχ N
  obtain ⟨K,hK,hrow⟩ := eventually_sqrt_gridUpperArgument_le_trial τ hτ χ hχ hN
  refine ⟨hlow.mono fun n hn ↦ hn.1,rootLogRate_of_clipped_grid (B:=(3370/81:ℝ)) hR hR1 hK.le (by norm_num) hlow hclip ?_⟩
  filter_upwards [hrow] with n hn
  intro Y θ hY hθ hsize
  obtain ⟨p,hp,he⟩ := hc.exists_clipped_ellipsoid_predictor hf hY hθ n hsize
  let v := Real.circleAverage (fun z ↦ ‖1-f z*(tablePolynomial p).eval z‖^2) 0 1
  have hv : 0≤v := Real.circleAverage_nonneg_of_nonneg (fun _ _ ↦ sq_nonneg _)
  refine ⟨v,hv,?_,hn p hp⟩
  change v ≤ (1+θ)*(1-Real.exp (-2*logGap f)+2*L Y)+_ at he
  rw [hgap] at he
  exact he

/-- The logarithmic Green upper read from the original finite grid has the same
rate for every fixed normalized character. The estimates are one-sided at all
sufficiently high indices. -/
theorem grid_log_upper_rate (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) {N : ℕ} (hN : tableExponent τ hτ χ hχ ≤ N) :
    (∀ᶠ n : ℕ in atTop, gridUpperArgument χ N n < 1 ∧
      criticalLogDifference χ ≤ -Real.log (1-gridUpperArgument χ N n)/2) ∧
    HasRootLogRate (fun n ↦ -Real.log (1-gridUpperArgument χ N n)/2-criticalLogDifference χ) := by
  let G := criticalLogDifference χ
  let R := 1-Real.exp (-2*G)
  let u := gridUpperArgument χ N
  let a := fun n ↦ -Real.log (1-u n)/2
  obtain ⟨htrue,htend⟩ := grid_upper_recovers_green τ hτ χ hχ hN
  obtain ⟨hR,A,hA,c,hc,hr⟩ := gridUpperArgument_rate τ hτ χ hχ hN
  let floor := Real.exp (-2*(G+1))
  have hfloor : 0 < floor := Real.exp_pos _
  have hB : ∀ᶠ n : ℕ in atTop, a n < G+1 := htend.eventually_lt_const (by dsimp [G]; linarith)
  refine ⟨htrue,A/(2*floor),by positivity,c,hc,?_⟩
  filter_upwards [htrue,hR,hr,hB] with n hn hRn hrate hncap
  have hpos : 0 < 1-u n := sub_pos.mpr hn.1
  have hG : G≤a n := hn.2
  have hlow : floor ≤ 1-u n := by
    rw [←Real.exp_log hpos]
    apply Real.exp_monotone
    dsimp [a] at hncap
    linarith
  have hOne : 1-R = Real.exp (-2*G) := by dsimp [R]; ring
  have hpR : 0<1-R := hOne ▸ Real.exp_pos _
  have hlog := Real.log_le_sub_one_of_pos (div_pos hpR hpos)
  rw [Real.log_div hpR.ne' hpos.ne',hOne,Real.log_exp] at hlog
  have ratio : Real.exp (-2*G)/(1-u n)-1=(u n-R)/(1-u n) := by
    rw [←hOne]
    field_simp
    ring
  rw [ratio] at hlog
  have ha : a n-G ≤ (u n-R)/(2*(1-u n)) := by
    dsimp [a]
    rw [mul_comm 2 (1-u n),←div_div]
    linarith
  change |a n-G| ≤ _
  rw [abs_of_nonneg (sub_nonneg.mpr hG)]
  have hrate' : u n-R ≤ A*Real.exp (-c*meshScale n) := (le_abs_self _).trans hrate
  calc
    a n-G ≤ (u n-R)/(2*(1-u n)) := ha
    _ ≤ (u n-R)/(2*floor) := div_le_div_of_nonneg_left (sub_nonneg.mpr hRn) (by positivity) (by linarith)
    _ ≤ A*Real.exp (-c*meshScale n)/(2*floor) := div_le_div_of_nonneg_right hrate' (by positivity)
    _ = _ := by ring

end RiemannMasullo.HeckeHardyGreen
