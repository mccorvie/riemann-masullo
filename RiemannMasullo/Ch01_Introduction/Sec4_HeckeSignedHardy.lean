module

public import RiemannMasullo.Ch01_Introduction.Sec4_HeckeSignedCoefficients
public import RiemannMasullo.ForMathlib.Analysis.Complex.RadialLogFourier
import RiemannMasullo.ForMathlib.Analysis.Complex.LogBoundaryMean
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.CayleyCauchy
import RiemannMasullo.AppB_AnalyticNT.Sec4b_BoundaryHeckeGreen
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import Mathlib.Tactic

/-!
# Hardy sums of the signed ordinary Hecke measurements at two

The rational pole-cleared Fourier factorization appears in Kunik, *Logarithmic Fourier
integrals for the Riemann Zeta Function*, equations (1.2)–(1.4) (arXiv:0804.4829).
Basiuk and Tarasyuk, *Fourier coefficients associated with the Riemann zeta-function*,
equations (4)–(7) (2016, doi:10.15330/cmp.8.1.16-20), relate the rational radial Fourier
coefficients to a logarithmic Taylor series and its disk zeros.
-/

@[expose] public noncomputable section
open MeasureTheory AddCircle Complex Filter Function Metric NumberField Set
open scoped NNReal Topology
namespace RiemannMasullo.HeckeLaguerre
open HeckeHalfPlaneJensen HalfPlaneJensen HeckeDiskNormalization DiskLogCoefficient SignedFrequency BoundaryHardy

variable {F : Type*} [Field F] [NumberField F]
local notation "CF" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual CF
local notation "𝕋" => AddCircle (2 * Real.pi)
local notation "μθ" => volume.restrict (Ioc (0:ℝ) (2*Real.pi))
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

/-- The real logarithm of the ordinary finite continuation on the boundary circle as seen from two. -/
def criticalTrace (χ : U𝔽) (x : 𝕋) : ℝ :=
  Real.log ‖(finiteHeckeL_exists_continuation χ).choose (toHalf (fourier 1 x))‖

/-- The complex logarithmic Taylor coefficient of positive order `n+1`, before taking its real part. -/
def logCoefficient (χ : U𝔽) (n : ℕ) : ℂ :=
  coeff (logDeriv (clearedDisk χ (finiteHeckeL_exists_continuation χ).choose)) n / (n+1:ℂ)

theorem logCoefficient_re (χ : U𝔽) (n : ℕ) :
    (logCoefficient χ n).re = measuredCoeff χ (n+1) / (n+1:ℝ) := by
  change (_ / (↑n + 1 : ℂ)).re = _ / _
  rw [show (↑n + 1 : ℂ) = ((n+1:ℝ):ℂ) by push_cast; rfl, div_ofReal_re]
  rfl

private theorem radial_nonzero (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (hR : IsEmpty (RightSite χ)) :
    ∀ z ∈ ball (0:ℂ) 1, clearedDisk χ (finiteHeckeL_exists_continuation χ).choose z ≠ 0 := by
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  intro z hz h0
  have hnorm := mem_ball_zero_iff.mp hz
  exact hR.false ⟨toHalf z, (clearedDisk_eq_zero_iff τ hτ χ hχ _ hL he hnorm).mp h0, toHalf_re hnorm⟩

private theorem chord_germ (z : ℂ) (_ : ‖z‖ ≤ 1) (h : z ≠ 1) :
    AnalyticAt ℂ (fun w : ℂ ↦ 1-w) z ∧ analyticOrderAt (fun w : ℂ ↦ 1-w) z ≠ ⊤ := by
  have ha : AnalyticAt ℂ (fun w : ℂ ↦ 1-w) z := by fun_prop
  have hn : 1-z ≠ 0 := sub_ne_zero.mpr h.symm
  exact ⟨ha, by rw [ha.analyticOrderAt_eq_zero.mpr hn]; simp⟩

private theorem circle_log_integrable_inner {f : ℂ → ℂ}
    (hg : ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 → AnalyticAt ℂ f z ∧ analyticOrderAt f z ≠ ⊤)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : Integrable (angleLog f r) μθ := by
  apply (show CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 r from ?_).1
  apply MeromorphicOn.circleIntegrable_log_norm
  intro z hz
  have h : ‖z‖ = r := by simpa only [abs_of_pos hr] using mem_sphere_zero_iff_norm.mp hz
  exact (hg z (h ▸ hr1.le) (fun he ↦ by rw [he,norm_one] at h; linarith)).1.meromorphicAt

private theorem log_product {u c b : ℝ} (hu : 0 < u) (hc : 0 < c) (hb : 0 < b) (N : ℕ) :
    Real.log (u*(c/3)^N*b) = Real.log u + N*(Real.log c-Real.log 3) + Real.log b := by
  rw [Real.log_mul (by positivity) hb.ne', Real.log_mul hu.ne' (by positivity), Real.log_pow,
    Real.log_div hc.ne' (by norm_num)]

/-- A sequence of radii gives L¹ convergence of the logarithm of the actual cleared function
to the ordinary critical-line trace. The vanishing normalizing factor at one cancels explicitly. -/
theorem exists_radial_L1_criticalTrace (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (hR : IsEmpty (RightSite χ)) :
    ∃ r : ℕ → ℝ, (∀ j, 0 < r j ∧ r j < 1) ∧ Tendsto r atTop (𝓝 1) ∧
      Tendsto (fun j ↦ ∫ x : 𝕋, |Real.log ‖radial (clearedDisk χ (finiteHeckeL_exists_continuation χ).choose)
        (r j) x‖ - criticalTrace χ x| ∂haarAddCircle) atTop (𝓝 0) := by
  classical
  let L := (finiteHeckeL_exists_continuation χ).choose
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  obtain ⟨N,a,hN,ha,hunit,hgerm,_,_,hp,_,hg⟩ := exists_normalized_input τ hτ χ hχ L hL he
  let G := normalized χ L a N
  let d (z : ℂ) := 1-z
  obtain ⟨hI,r,hr,ht,hm⟩ := PoissonBoundary.circleIntegrable_log_norm_and_exists_radial_limit hgerm hunit
    (fun q hq hq1 ↦ hp q (by linarith) hq1) hg
  have hreg (j) : 0 < r j ∧ r j < 1 := ⟨by linarith [(hr j).1], (hr j).2⟩
  have hG := radial_log_L1_of_means (f:=G) (B:=0) hgerm
    (fun z hz ↦ Real.log_nonpos (norm_nonneg _) (hunit z hz)) hI hreg ht hm
  have hd (t : ℝ) (h0 : 0<t) (h1 : t≤1) := HeckeBoundaryGreen.circleMean_log_one_sub h0 h1
  have hD := radial_log_L1_of_means (f:=d) (B:=Real.log 2) chord_germ
    (fun z hz ↦ by
      have hl : ‖d z‖ ≤ 2 := (norm_sub_le 1 z).trans (by rw [norm_one]; linarith)
      rcases eq_or_lt_of_le (norm_nonneg (d z)) with h|h
      · rw [← h, Real.log_zero]; exact Real.log_nonneg (by norm_num)
      · exact Real.log_le_log h hl)
    (hd 1 zero_lt_one le_rfl).1 hreg ht
    (by
      dsimp only [d]
      rw [(hd 1 zero_lt_one le_rfl).2]
      exact tendsto_const_nhds.congr (fun n ↦ (hd (r n) (hreg n).1 (hreg n).2.le).2.symm))
  let Z (t x : ℝ) := circleMap 0 t x
  let V (t x : ℝ) := Real.log ‖clearedDisk χ L (Z t x)‖
  let u (x : ℝ) := Real.log ‖L (toHalf (Z 1 x))‖
  have inside (j) (x : ℝ) : angleLog G (r j) x =
      Real.log a + N*(angleLog d (r j) x-Real.log 3) + V (r j) x := by
    let z := Z (r j) x
    have hz : ‖z‖ < 1 := by simpa [z,Z,norm_circleMap_zero,abs_of_pos (hreg j).1] using (hreg j).2
    have h1 : z ≠ 1 := fun h ↦ by rw [h,norm_one] at hz; exact hz.false
    have hA := radial_nonzero τ hτ χ hχ hR z (mem_ball_zero_iff.mpr hz)
    change Real.log ‖(a:ℂ) * ((1-z)/3)^N * clearedDisk χ L z‖ = Real.log a + N*(Real.log ‖1-z‖-Real.log 3)+Real.log ‖clearedDisk χ L z‖
    change clearedDisk χ L z ≠ 0 at hA
    simpa only [norm_mul,norm_pow,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,
      Complex.norm_ofNat] using log_product ha (norm_pos_iff.mpr (sub_ne_zero.mpr h1.symm)) (norm_pos_iff.mpr hA) N
  have edge : ∀ᵐ x ∂μθ, angleLog G 1 x =
      Real.log a + N*(angleLog d 1 x-Real.log 3) + u x := by
    filter_upwards [ae_restrict_of_ae (regular_boundary_angles hgerm)] with x hx
    let z := Z 1 x
    have hz : ‖z‖=1 := by simp [z,Z,norm_circleMap_zero]
    have hb := normalized_boundary_norm τ hτ χ hχ L hL he ha hN hz
    have hw : 0 < ‖L (toHalf z)‖ := by
      refine norm_pos_iff.mpr (fun hz0 ↦ ?_)
      rw [hz0,norm_zero,mul_zero,norm_eq_zero] at hb
      exact hx.2 hb
    change Real.log ‖normalized χ L a N z‖ = _
    rw [hb,norm_div,Complex.norm_ofNat]
    exact log_product ha (norm_pos_iff.mpr (sub_ne_zero.mpr hx.1.symm)) hw N
  have ig (j) := ((circle_log_integrable_inner hgerm (hreg j).1 (hreg j).2).sub hI.1).abs
  have id' (j) := ((hd (r j) (hreg j).1 (hreg j).2.le).1.1.sub (hd 1 zero_lt_one le_rfl).1.1).abs
  have htotal := hG.add (hD.const_mul (N:ℝ))
  have hsmall : Tendsto (fun j ↦ ∫ x, |V (r j) x - u x| ∂μθ) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _)) (fun j ↦ ?_)
      (by simpa only [mul_zero,add_zero] using htotal)
    rw [← integral_const_mul]
    rw [← integral_add (f:=fun x ↦ |angleLog G (r j) x-angleLog G 1 x|)
      (g:=fun x ↦ (N:ℝ)*|angleLog d (r j) x-angleLog d 1 x|) (ig j) ((id' j).const_mul _)]
    apply integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) ((ig j).add ((id' j).const_mul _))
    filter_upwards [edge] with x hx
    have heq : V (r j) x - u x = (angleLog G (r j) x-angleLog G 1 x)
        - (N:ℝ)*(angleLog d (r j) x-angleLog d 1 x) := by rw [inside j x,hx]; ring
    change |V (r j) x-u x| ≤ |angleLog G (r j) x-angleLog G 1 x| + (N:ℝ)*|angleLog d (r j) x-angleLog d 1 x|
    rw [heq]
    simpa only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) N)] using
      abs_sub (angleLog G (r j) x-angleLog G 1 x) ((N:ℝ)*(angleLog d (r j) x-angleLog d 1 x))
  refine ⟨r,hreg,ht,?_⟩
  have hp := hsmall.const_mul (2*Real.pi)⁻¹
  have eid (j) : (∫ x : 𝕋, |Real.log ‖radial (clearedDisk χ L) (r j) x‖-criticalTrace χ x| ∂haarAddCircle) =
      (2*Real.pi)⁻¹ * ∫ x, |V (r j) x-u x| ∂μθ := by
    rw [integral_angle]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ by
      simp only [radial,criticalTrace,fourier_one_coe,circleMap_zero,ofReal_one,one_mul,V,u,Z,L]
  rw [mul_zero] at hp
  exact hp.congr (fun j ↦ (eid j).symm)

/-- In the absence of right-hand sites, each complex Taylor coefficient is twice the matching
positive Fourier coefficient of the true boundary trace. -/
theorem logCoefficient_eq_two_mode (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (hr : IsEmpty (RightSite χ))
    (hi : Integrable (criticalTrace χ) haarAddCircle) (n : ℕ) :
    logCoefficient χ n = 2 * mode (criticalTrace χ) (n+1) := by
  obtain ⟨r,hr',ht,hl⟩ := exists_radial_L1_criticalTrace τ hτ χ hχ hr
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  exact (two_mode_eq_logDeriv_of_radial_L1 (clearedDisk_analytic τ hτ χ hχ _ hL he)
    (radial_nonzero τ hτ χ hχ hr) (fun j ↦ ⟨(hr' j).1.le,(hr' j).2⟩) ht _ hi hl n).symm

/-- Complex logarithmic energy equals twice the full variance on the critical circle. -/
theorem hasSum_logCoefficient_sq (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (hr : IsEmpty (RightSite χ))
    (hu : MemLp (criticalTrace χ) 2 haarAddCircle) :
    HasSum (fun n ↦ ‖logCoefficient χ n‖^2) (2*ProbabilityTheory.variance (criticalTrace χ) haarAddCircle) := by
  exact (hasSum_double_modes hu).congr_fun (fun n ↦ by rw [logCoefficient_eq_two_mode τ hτ χ hχ hr (hu.integrable (by norm_num))])

/-- The measured real sequence has twice the variance of the reflection-even trace. -/
theorem hasSum_measuredCoeff_div_sq (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (hr : IsEmpty (RightSite χ))
    (hu : MemLp (criticalTrace χ) 2 haarAddCircle) :
    HasSum (fun n : ℕ ↦ (measuredCoeff χ (n+1) / (n+1:ℝ))^2)
      (2*ProbabilityTheory.variance (evenPart (criticalTrace χ)) haarAddCircle) := by
  refine (hasSum_double_modes_re hu).congr_fun (fun n ↦ ?_)
  rw [← logCoefficient_re, logCoefficient_eq_two_mode τ hτ χ hχ hr (hu.integrable (by norm_num))]
  simp

/-- The literal Cauchy-weighted second moment on the real line supplies the Haar L² hypothesis. -/
theorem criticalTrace_memLp_of_weighted_sq (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1)
    (hs : Integrable (fun t : ℝ ↦ ((3/2)/(Real.pi*((3/2)^2+t^2))) *
      (Real.log ‖(finiteHeckeL_exists_continuation χ).choose ((1/2:ℂ)+t*I)‖)^2)) :
    MemLp (criticalTrace χ) 2 haarAddCircle := by
  let L := (finiteHeckeL_exists_continuation χ).choose
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  let u (t : ℝ) := criticalTrace χ (t:𝕋)
  have hraw := (HeckeBoundaryGreen.integrable_weightedLog_and_green τ hτ χ hχ L hL he).1
  have hI := (CayleyCauchy.circleIntegrable_two_add_div_one_sub_iff (fun z ↦ Real.log ‖L z‖)).mpr hraw
  have hS := (CayleyCauchy.circleIntegrable_two_add_div_one_sub_iff (fun z ↦ (Real.log ‖L z‖)^2)).mpr hs
  have hac : Integrable u μθ := by
    change IntegrableOn u (Ioc 0 (2*Real.pi)) volume
    simpa only [u,criticalTrace,fourier_one_coe,toHalf,L] using hI.1
  have hsq : Integrable (fun t ↦ (u t)^2) μθ := by
    change IntegrableOn (fun t ↦ u t^2) (Ioc 0 (2*Real.pi)) volume
    simpa only [u,criticalTrace,fourier_one_coe,toHalf,L] using hS.1
  have hu := (memLp_two_iff_integrable_sq hac.aestronglyMeasurable).2 hsq
  have hc : MemLp (fun t ↦ (u t : ℂ)) 2 (volume.restrict (Ioc 0 (0 + 2*Real.pi))) := by
    rw [zero_add]
    exact hu.ofReal
  have hl := hc.memLp_liftIoc.haarAddCircle
  have hfun : liftIoc (2*Real.pi) 0 (fun t ↦ (u t : ℂ)) = fun x ↦ (criticalTrace χ x : ℂ) := by
    funext x
    change (criticalTrace χ (((equivIoc (2*Real.pi) 0 x : Ioc _ _):ℝ):𝕋) : ℂ) = _
    rw [coe_equivIoc]
  rw [hfun] at hl
  simpa using hl.re

/-- The raw second moment in the real-line chart agrees with the normalized angular moment. -/
theorem integral_criticalTrace_sq (χ : U𝔽) :
    (∫ x, (criticalTrace χ x)^2 ∂haarAddCircle) =
      ∫ t : ℝ, ((3/2)/(Real.pi*((3/2)^2+t^2))) *
        (Real.log ‖(finiteHeckeL_exists_continuation χ).choose ((1/2:ℂ)+t*I)‖)^2 := by
  have e := CayleyCauchy.circleAverage_two_add_div_one_sub
    (fun z ↦ (Real.log ‖(finiteHeckeL_exists_continuation χ).choose z‖)^2)
  rw [integral_angle]
  simpa only [criticalTrace, fourier_one_coe, Real.circleAverage_def, toHalf, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)] using e

/-- Positive-part logarithmic energy, using coordinate `n+1`. -/
def signedSquare (y : ℕ → ℝ) (negative : Bool) (n : ℕ) : ℝ :=
  (max 0 (if negative then -y (n+1) else y (n+1)) / (n+1:ℝ))^2

private theorem positive_rate_zero_of_square {y : ℕ → ℝ} (hy : y 0 = 0)
    (hs : Summable (fun n : ℕ ↦ (max 0 (y (n+1)) / (n+1:ℝ))^2)) :
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix y N)/(N:ℝ)) atTop (𝓝 0) := by
  let D := 1 + ∑' n : ℕ, (max 0 (y (n+1)) / (n+1:ℝ))^2
  have hD : 0 ≤ D := add_nonneg zero_le_one (tsum_nonneg (fun _ ↦ sq_nonneg _))
  have hlin (m : ℕ) : y m ≤ D*m := by
    cases m with
    | zero => simp [hy]
    | succ n =>
      let v := max 0 (y (n+1))/(n+1:ℝ)
      have hsum := hs.le_tsum n (fun _ _ ↦ sq_nonneg _)
      have hb : v ≤ D := by
        have hv : v^2 ≤ D-1 := by simpa only [D,add_sub_cancel_left] using hsum
        nlinarith [sq_nonneg (v-1/2)]
      have hdiv : max 0 (y (n+1)) ≤ D*(n+1:ℝ) := (div_le_iff₀ (by positivity)).mp hb
      simpa only [Nat.cast_succ] using (le_max_right 0 (y (n+1))).trans hdiv
  apply tendsto_log_positivePrefix_of_subexponential
  intro A hA
  have hp : 0<A-1 := by linarith
  refine ⟨D/(A-1), div_nonneg hD hp.le, fun n ↦ (hlin n).trans ?_⟩
  have hn := one_add_mul_le_pow (a:=A-1) (by linarith : -2≤A-1) n
  rw [show 1+(A-1)=A by ring] at hn
  rw [div_mul_eq_mul_div, le_div_iff₀ hp]
  calc D*n*(A-1) = D*((n:ℝ)*(A-1)) := by ring
       _ ≤ D*A^n := mul_le_mul_of_nonneg_left (by linarith) hD

/-- A right-hand zero forces each fixed signed energy to diverge to positive infinity. -/
theorem tendsto_signedSquare_atTop_of_rightSite (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (w : RightSite χ) (negative : Bool) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, signedSquare (measuredCoeff χ) negative n) atTop atTop := by
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n ↦ sq_nonneg _)).mp
  obtain ⟨v,_,hp,hplus,hminus⟩ := signed_rate_measures_nearest τ hτ χ hχ w
  intro hs
  cases negative with
  | false =>
    exact hp.ne' (tendsto_nhds_unique hplus (positive_rate_zero_of_square (y:=measuredCoeff χ) rfl hs))
  | true =>
    exact hp.ne' (tendsto_nhds_unique hminus (positive_rate_zero_of_square (y:=fun n ↦ -measuredCoeff χ n)
      (by change -(0:ℝ)=0; simp) hs))

private theorem signedSquare_le (y : ℕ → ℝ) (negative : Bool) (n : ℕ) :
    signedSquare y negative n ≤ (y (n+1)/(n+1:ℝ))^2 := by
  unfold signedSquare
  rw [div_pow,div_pow]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  cases negative <;> simp only [Bool.false_eq_true, ite_false,ite_true] <;>
    rcases le_total 0 (y (n+1)) with h|h <;> simp [h,neg_nonpos.mpr,neg_nonneg.mpr,sq_nonneg]

/-- For either fixed orientation, bounded signed square sums of genuine coefficients are
equivalent to confinement of every divisor site to the critical line. -/
theorem central_iff_summable_signedSquare (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (hu : MemLp (criticalTrace χ) 2 haarAddCircle) (negative : Bool) :
    (∀ z : HeckePoisson.Site χ, z.val.re=1/2) ↔ Summable (signedSquare (measuredCoeff χ) negative) := by
  rw [← isEmpty_rightSite_iff_central]
  constructor
  · intro hR
    exact (hasSum_measuredCoeff_div_sq τ hτ χ hχ hR hu).summable.of_nonneg_of_le
      (fun _ ↦ sq_nonneg _) (signedSquare_le _ _)
  · intro hs
    refine ⟨fun w ↦ ?_⟩
    exact ((not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n ↦ sq_nonneg _)).mpr
      (tendsto_signedSquare_atTop_of_rightSite τ hτ χ hχ w negative)) hs

/-- Every one-sided finite true-value energy is bounded by twice the ordinary arithmetic
second moment if the sites are central. -/
theorem signedSquare_prefix_le_second_moment (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (hR : IsEmpty (RightSite χ))
    (hu : MemLp (criticalTrace χ) 2 haarAddCircle) (negative : Bool) (N : ℕ) :
    ∑ n ∈ Finset.range N, signedSquare (measuredCoeff χ) negative n ≤
      2*∫ t : ℝ, ((3/2)/(Real.pi*((3/2)^2+t^2))) *
        (Real.log ‖(finiteHeckeL_exists_continuation χ).choose ((1/2:ℂ)+t*I)‖)^2 := by
  have h := hasSum_logCoefficient_sq τ hτ χ hχ hR hu
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖logCoefficient χ n‖^2 := by
      apply Finset.sum_le_sum
      intro n _
      apply (signedSquare_le _ _ _).trans
      rw [← logCoefficient_re]
      exact (sq_le_sq.mpr (by simpa only [abs_of_nonneg (norm_nonneg _)] using
        (abs_re_le_norm (logCoefficient χ n))))
    _ ≤ ∑' n, ‖logCoefficient χ n‖^2 := h.summable.sum_le_tsum _ (fun _ _ ↦ sq_nonneg _)
    _ = 2*ProbabilityTheory.variance (criticalTrace χ) haarAddCircle := h.tsum_eq
    _ ≤ _ := by
      rw [← integral_criticalTrace_sq]
      exact mul_le_mul_of_nonneg_left (ProbabilityTheory.variance_le_expectation_sq hu.aestronglyMeasurable) (by norm_num)

/-- A pointwise bound for a perturbation of either sign. -/
theorem perturb_square_le (x y : ℕ → ℝ) (negative : Bool) (n : ℕ) :
    signedSquare y negative n ≤ 2*signedSquare x negative n +
      2*((y (n+1)-x (n+1))/(n+1:ℝ))^2 := by
  let a := max 0 (if negative then -y (n+1) else y (n+1))
  let b := max 0 (if negative then -x (n+1) else x (n+1))
  have hl : |a-b| ≤ |y (n+1)-x (n+1)| := by
    cases negative
    · simpa only [a,b,Bool.false_eq_true,ite_false,max_comm (0:ℝ)] using abs_max_sub_max_le_abs (y (n+1)) (x (n+1)) 0
    · simpa only [a,b,ite_true,max_comm (0:ℝ),neg_sub_neg,abs_sub_comm (x (n+1)) (y (n+1))] using
        abs_max_sub_max_le_abs (-(y (n+1))) (-(x (n+1))) 0
  have hh : a^2 ≤ 2*b^2+2*(y (n+1)-x (n+1))^2 := by nlinarith [sq_le_sq.mpr hl, sq_nonneg (a-2*b)]
  have hd := div_le_div_of_nonneg_right hh (sq_nonneg (n+1:ℝ))
  change (a/(n+1:ℝ))^2 ≤ 2*(b/(n+1:ℝ))^2 + _
  simpa only [div_pow,add_div,mul_div_assoc] using hd

/-- Square-summable errors after division by the positive index preserve each signed
square-summability criterion. -/
theorem summable_signedSquare_iff_of_error {x y : ℕ → ℝ}
    (he : Summable fun n : ℕ ↦ ((y (n+1)-x (n+1))/(n+1:ℝ))^2) (negative : Bool) :
    Summable (signedSquare y negative) ↔ Summable (signedSquare x negative) := by
  have go (u v : ℕ → ℝ) (h : Summable fun n : ℕ ↦ ((v (n+1)-u (n+1))/(n+1:ℝ))^2)
      (hs : Summable (signedSquare u negative)) : Summable (signedSquare v negative) :=
    ((hs.mul_left 2).add (h.mul_left 2)).of_nonneg_of_le (fun _ ↦ sq_nonneg _) (perturb_square_le u v negative)
  refine ⟨go y x (he.congr (fun n ↦ ?_)), go x y he⟩
  rw [← neg_sub, neg_div,neg_sq]

/-- Bounded ordinary prefixes, summability and a finite total agree for the nonnegative
one-sided square measurements. -/
theorem summable_signedSquare_iff_bounded (x : ℕ → ℝ) (negative : Bool) :
    Summable (signedSquare x negative) ↔
      ∃ C : ℝ, ∀ N : ℕ, ∑ n ∈ Finset.range N, signedSquare x negative n ≤ C := by
  exact ⟨fun hs ↦ ⟨_,fun N ↦ hs.sum_le_tsum (Finset.range N) (fun _ _ ↦ sq_nonneg _)⟩,
    fun ⟨_,h⟩ ↦ summable_of_sum_range_le (fun _ ↦ sq_nonneg _) h⟩

/-- Any approximate sequence with normalized square-summable errors gives the same
one-sided bounded-energy condition as the actual arithmetic coefficients. -/
theorem central_iff_bounded_signedSquare_of_error (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (hu : MemLp (criticalTrace χ) 2 haarAddCircle)
    (y : ℕ → ℝ) (he : Summable fun n : ℕ ↦ ((y (n+1)-measuredCoeff χ (n+1))/(n+1:ℝ))^2)
    (negative : Bool) :
    (∀ z : HeckePoisson.Site χ, z.val.re=1/2) ↔
      ∃ C : ℝ, ∀ N : ℕ, ∑ n ∈ Finset.range N, signedSquare y negative n ≤ C := by
  rw [← summable_signedSquare_iff_bounded, summable_signedSquare_iff_of_error he]
  exact central_iff_summable_signedSquare τ hτ χ hχ hu negative

end RiemannMasullo.HeckeLaguerre
