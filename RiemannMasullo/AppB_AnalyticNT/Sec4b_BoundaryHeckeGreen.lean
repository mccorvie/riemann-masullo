module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b_NormalizedHeckeDisk
public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.CayleyCauchy
import RiemannMasullo.ForMathlib.Analysis.Complex.LogBoundaryMean
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog
import Mathlib.Analysis.SpecialFunctions.Integrability.Log
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Hecke critical-line logarithmic mean at two

The circle mean of the principal-character rational factor is log r for 1/2 < r ≤ 1.
The factor at the exceptional point contributes a constant to the normalization at all
these radii, including the unit circle. Isolated zeros away from the exceptional point
have countable angular preimages. Removing both factors therefore preserves the
boundary limit. The resulting equality identifies the critical-line logarithmic Poisson
mean at two with the full right-half-plane Blaschke logarithm, including multiplicities.

The classical antecedents are Balazard, Saias and Yor, *Notes sur la fonction ζ de Riemann,
2*, Advances in Mathematics 143 (1999), 284–287, for the rational criterion at one, and
Burnol, *An adelic causality problem related to abelian L-functions*, Theorem 3.2,
pp. 14–15 of arXiv:math/0001013, for the Hecke Blaschke factor.
-/

@[expose] public noncomputable section

open Complex Filter Function IsDedekindDomain MeasureTheory Metric NumberField Set
open scoped NNReal Topology

namespace RiemannMasullo.HeckeBoundaryGreen

variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽
local notation "Hp" => (Complex.re ⁻¹' Ioi (1 : ℝ))

open HalfPlaneJensen HeckeDiskNormalization HeckeHalfPlaneJensen

/-- Logarithmic distance to a fixed complex point. -/
def logDistance (b z : ℂ) : ℝ := Real.log ‖z - b‖

private theorem logDistance_integrable (b : ℂ) (r : ℝ) : CircleIntegrable (logDistance b) 0 r :=
  MeromorphicOn.circleIntegrable_log_norm (f:=fun z : ℂ ↦ z - b) (fun _ _ ↦ by fun_prop)

theorem mean_distance_exterior {r : ℝ} (hr : 0 < r) {b : ℂ} (hb : r ≤ ‖b‖) :
    Real.circleAverage (logDistance b) 0 r = Real.log ‖b‖ := by
  have hbn := hr.trans_le hb
  have h : 1 ≤ r⁻¹ * ‖b‖ := by
    rw [←div_eq_inv_mul]
    exact (one_le_div hr).mpr hb
  change Real.circleAverage (fun z : ℂ ↦ Real.log ‖z - b‖) 0 r = _
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne', zero_sub,
    norm_neg, Real.posLog_eq_log (by simpa [abs_of_nonneg (by positivity : 0 ≤ r⁻¹*‖b‖)] using h),
    Real.log_mul (inv_ne_zero hr.ne') hbn.ne', Real.log_inv]
  ring

theorem mean_distance_interior {r : ℝ} (hr : 0 < r) {b : ℂ} (hb : ‖b‖ ≤ r) :
    Real.circleAverage (logDistance b) 0 r = Real.log r := by
  apply circleAverage_log_norm_sub_const_of_mem_closedBall
  simpa [Metric.mem_closedBall, abs_of_pos hr] using hb

/-- The zero at the boundary point one contributes zero even on the unit circle. -/
theorem circleMean_log_one_sub {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    CircleIntegrable (fun z : ℂ ↦ Real.log ‖1 - z‖) 0 r ∧
      Real.circleAverage (fun z : ℂ ↦ Real.log ‖1 - z‖) 0 r = 0 := by
  have he : (fun z : ℂ ↦ Real.log ‖1 - z‖) = logDistance 1 :=
    funext fun z ↦ congrArg Real.log (norm_sub_rev 1 z)
  rw [he]
  refine ⟨logDistance_integrable 1 r, ?_⟩
  rw [mean_distance_exterior (b := (1:ℂ)) hr (by simpa using hr1), norm_one, Real.log_one]

open scoped Classical in
/-- Logarithmic contribution of the rational pole-cancelling factor. -/
def poleLog (χ : U𝔽) (z : ℂ) : ℝ :=
  if χ = 1 then Real.log 2 + logDistance (-(1/2)) z - logDistance (-2) z else 0

/-- Sum of the logarithmic contributions from the disk normalizers. -/
def correction (χ : U𝔽) (a : ℝ) (N : ℕ) (z : ℂ) : ℝ :=
  Real.log a - (N:ℝ)*Real.log 3 + (N:ℝ)*logDistance 1 z + poleLog χ z

open scoped Classical in
theorem poleLog_mean (χ : U𝔽) {r : ℝ} (hlo : 1 / 2 < r) (hhi : r ≤ 1) :
    CircleIntegrable (poleLog χ) 0 r ∧
      Real.circleAverage (poleLog χ) 0 r = (if χ = 1 then Real.log r else 0) := by
  have hr : 0 < r := by linarith
  by_cases hc : χ = 1
  · have hfun : poleLog χ = (fun z ↦ Real.log 2 + logDistance (-(1/2)) z - logDistance (-2) z) := by
      funext z; simp [poleLog, hc]
    rw [hfun, ite_eq_left hc]
    have hnum : CircleIntegrable (fun z ↦ Real.log 2 + logDistance (-(1/2)) z) 0 r := (circleIntegrable_const (Real.log 2) 0 r).add (logDistance_integrable (-(1/2)) r)
    have hden := logDistance_integrable (-2) r
    refine ⟨hnum.sub hden, ?_⟩
    rw [Real.circleAverage_fun_sub hnum hden,
      Real.circleAverage_fun_add (circleIntegrable_const (Real.log 2) 0 r) (logDistance_integrable (-(1/2)) r),
      Real.circleAverage_const, mean_distance_interior hr (by norm_num [norm_div]; linarith : ‖(-(1/2):ℂ)‖ ≤ r),
      mean_distance_exterior hr (by norm_num; linarith : r ≤ ‖(-2:ℂ)‖)]
    norm_num
  · have hfun : poleLog χ = (fun _ ↦ (0:ℝ)) := by funext z; simp [poleLog, hc]
    simp [hfun, hc, Real.circleAverage_const]

open scoped Classical in
theorem correction_mean (χ : U𝔽) (a : ℝ) (N : ℕ) {r : ℝ} (hlo : 1 / 2 < r) (hhi : r ≤ 1) :
    CircleIntegrable (correction χ a N) 0 r ∧
      Real.circleAverage (correction χ a N) 0 r =
        Real.log a - (N:ℝ)*Real.log 3 + (if χ = 1 then Real.log r else 0) := by
  let c := Real.log a - (N:ℝ)*Real.log 3
  have hr : 0 < r := by linarith
  have hD : CircleIntegrable (fun z ↦ (N:ℝ)*logDistance 1 z) 0 r :=
    (logDistance_integrable 1 r).const_smul (a:=(N:ℝ))
  have hbase : CircleIntegrable (fun z ↦ c + (N:ℝ)*logDistance 1 z) 0 r := (circleIntegrable_const c 0 r).add hD
  obtain ⟨hP, hm⟩ := poleLog_mean χ hlo hhi
  refine ⟨hbase.add hP, ?_⟩
  change Real.circleAverage (fun z ↦ (c + (N:ℝ) * logDistance 1 z) + poleLog χ z) 0 r = _
  rw [Real.circleAverage_fun_add hbase hP, Real.circleAverage_fun_add (circleIntegrable_const c 0 r) hD,
    Real.circleAverage_const, hm]
  have hd : Real.circleAverage (fun z ↦ (N:ℝ)*logDistance 1 z) 0 r =
      (N:ℝ)*Real.circleAverage (logDistance 1) 0 r :=
    Real.circleAverage_fun_smul (a := (N:ℝ)) (f := logDistance 1) (c:=0) (R:=r)
  rw [hd, mean_distance_exterior (b := (1:ℂ)) hr (by simpa using hhi : r ≤ ‖(1:ℂ)‖), norm_one, Real.log_one, mul_zero, add_zero]

private theorem regular_angles {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hri : r ≤ 1)
    (hf : ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 → AnalyticAt ℂ f z ∧ analyticOrderAt f z ≠ ⊤) :
    ∀ᵐ θ : ℝ, circleMap 0 r θ ≠ 1 ∧ f (circleMap 0 r θ) ≠ 0 := by
  let S := closedBall (0:ℂ) 1 \ {1}
  let Z := {z : ℂ | f z = 0} ∩ S
  have hc : Z.Countable := by
    apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    apply isDiscrete_of_codiscreteWithin
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    intro z hz
    obtain ⟨hza, hzo⟩ := hf z (by simpa using hz.1) (by simpa using hz.2)
    have h := hza.eventually_eq_zero_or_eventually_ne_zero.resolve_left (fun he ↦ hzo (analyticOrderAt_eq_top.mpr he))
    filter_upwards [h] with u hu using Or.inl hu
  have hnull := (((countable_singleton (1:ℂ)).union hc).preimage_circleMap 0 hr.ne').ae_notMem volume
  filter_upwards [hnull] with θ hθ
  let z := circleMap 0 r θ
  have h1 : z ≠ 1 := fun h ↦ hθ (Or.inl h)
  have hS : z∈S := ⟨by simpa [z, norm_circleMap_zero, abs_of_pos hr] using hri, h1⟩
  exact ⟨h1, fun h ↦ hθ (Or.inr ⟨h, hS⟩)⟩

private theorem poleLog_eq_log (χ : U𝔽) {z : ℂ} (hlo : 1 / 2 < ‖z‖) (hhi : ‖z‖ ≤ 1) :
    diskFactor χ z ≠ 0 ∧ Real.log ‖diskFactor χ z‖ = poleLog χ z := by
  classical
  have hh : z ≠ -(1/2) := by intro h; norm_num [h, norm_div] at hlo
  have h2 : z ≠ -2 := by intro h; norm_num [h] at hhi
  have ha : 1 + 2 * z=2*(z-(-(1/2))) := by ring
  have hb : 2+z=z-(-2) := by ring
  have hnm : 1 + 2 * z ≠ 0 := ha.trans_ne (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hh))
  have hdn : 2+z ≠ 0 := hb.trans_ne (sub_ne_zero.mpr h2)
  refine ⟨pow_ne_zero _ (div_ne_zero hnm hdn), ?_⟩
  by_cases hc : χ = 1
  · rw [diskFactor, poleLog, ite_eq_left hc, ite_eq_left hc, pow_one, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr hnm) (norm_ne_zero_iff.mpr hdn), ha, hb, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (by norm_num : (2:ℂ)≠0)) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hh)), Complex.norm_ofNat]
    rfl
  · simp [diskFactor, poleLog, hc]

open scoped Classical in
theorem circleMean_diskFactor (χ : U𝔽) {r : ℝ} (hlo : 1 / 2 < r) (hhi : r ≤ 1) :
    CircleIntegrable (fun z ↦ Real.log ‖diskFactor χ z‖) 0 r ∧
    Real.circleAverage (fun z ↦ Real.log ‖diskFactor χ z‖) 0 r = (if χ = 1 then Real.log r else 0) := by
  have hr : 0 < r := by linarith
  have h : EqOn (fun z ↦ Real.log ‖diskFactor χ z‖) (poleLog χ) (sphere 0 |r|) := by
    intro z hz
    have hn : ‖z‖=r := by simpa [Metric.mem_sphere, abs_of_pos hr] using hz
    exact (poleLog_eq_log χ (by rwa [hn]) (by rwa [hn])).2
  obtain ⟨hi, hm⟩ := poleLog_mean χ hlo hhi
  exact ⟨(circleIntegrable_congr h).mpr hi,(Real.circleAverage_congr_sphere h).trans hm⟩

private theorem raw_log (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {a : ℝ} (ha : 0 < a) (N : ℕ) {z : ℂ}
    (hlo : 1 / 2 < ‖z‖) (hhi : ‖z‖ ≤ 1) (h1 : z ≠ 1) (hf : normalized χ L a N z ≠ 0) :
    Real.log ‖normalized χ L a N z‖ =
      correction χ a N z + Real.log ‖L (toHalf z)‖ := by
  have heq := normalized_raw_outer τ hτ χ hχ L hL he a N hhi h1 hlo
  obtain ⟨hd, hdlog⟩ := poleLog_eq_log χ hlo hhi
  have hl : L (toHalf z) ≠ 0 := by
    intro h
    exact hf (by simp [heq, raw, h])
  have hdist : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
  have hdisk : 0 < ‖diskFactor χ z‖ := norm_pos_iff.mpr hd
  have hn : 0 < ‖z - 1‖ / 3 := by positivity
  rw [heq, raw]
  simp only [norm_mul, norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, Complex.norm_ofNat]
  rw [norm_sub_rev 1 z, Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hl),
    Real.log_mul (by positivity) hdisk.ne', Real.log_mul ha.ne' (pow_ne_zero N hn.ne'),
    Real.log_pow, Real.log_div hdist.ne' (by norm_num), hdlog]
  unfold correction logDistance
  ring

theorem normalized_log_ae (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {a : ℝ} (ha : 0 < a) (N : ℕ) {r : ℝ}
    (hlo : 1 / 2 < r) (hhi : r ≤ 1) :
    ∀ᵐ θ : ℝ, Real.log ‖normalized χ L a N (circleMap 0 r θ)‖ =
      correction χ a N (circleMap 0 r θ) + Real.log ‖L (toHalf (circleMap 0 r θ))‖ := by
  have hr : 0 < r := by linarith
  have hreg := regular_angles (f:=normalized χ L a N) hr hhi
    (fun z hz h1 ↦ ⟨normalized_analytic τ hτ χ hχ L hL he a N hz h1,
      normalized_finite_order τ hτ χ hχ L hL he ha N hz h1⟩)
  filter_upwards [hreg] with θ hθ
  have hn : ‖circleMap 0 r θ‖=r := by rw [norm_circleMap_zero, abs_of_pos hr]
  exact raw_log τ hτ χ hχ L hL he ha N (by rwa [hn]) (by rwa [hn]) hθ.1 hθ.2

private theorem circleAverage_congr_angles {g h : ℂ → ℝ} {r : ℝ}
    (ha : ∀ᵐ θ : ℝ, g (circleMap 0 r θ) = h (circleMap 0 r θ)) :
    Real.circleAverage g 0 r = Real.circleAverage h 0 r := by
  unfold Real.circleAverage
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ha] with θ hθ _ using hθ

open scoped Classical in
theorem strip_mean (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {a : ℝ} (ha : 0 < a) (N : ℕ) {r : ℝ}
    (hlo : 1 / 2 < r) (hhi : r ≤ 1) (hF : CircleIntegrable (fun z ↦ Real.log ‖normalized χ L a N z‖) 0 r) :
    CircleIntegrable (fun z ↦ Real.log ‖L (toHalf z)‖) 0 r ∧
      circleMean L r = Real.circleAverage (fun z ↦ Real.log ‖normalized χ L a N z‖) 0 r -
        (Real.log a - (N:ℝ)*Real.log 3 + (if χ = 1 then Real.log r else 0)) := by
  obtain ⟨hc, hm⟩ := correction_mean χ a N hlo hhi
  let g := fun z ↦ Real.log ‖normalized χ L a N z‖
  let b := fun z ↦ Real.log ‖L (toHalf z)‖
  have hback : ∀ᵐ θ : ℝ, (g-correction χ a N) (circleMap 0 r θ)=b (circleMap 0 r θ) := by
    filter_upwards [normalized_log_ae τ hτ χ hχ L hL he ha N hlo hhi] with θ hh
    simpa only [Pi.sub_apply, g, b, add_sub_cancel_left] using (congrArg (fun x ↦ x-correction χ a N (circleMap 0 r θ)) hh)
  have hi : CircleIntegrable (g-correction χ a N) 0 r := hF.sub hc
  refine ⟨IntervalIntegrable.congr_ae hi (ae_restrict_of_ae hback), ?_⟩
  change Real.circleAverage b 0 r = _
  rw [←circleAverage_congr_angles hback, Real.circleAverage_sub hF hc, hm]

/-- Boundary integrability and one sequence of inner radii recovering the boundary mean. -/
private def BoundaryMeans (f : ℂ → ℂ) : Prop :=
  CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 1 ∧
  ∃ r : ℕ → ℝ, (∀ n, 1/2 < r n ∧ r n < 1) ∧ Tendsto r atTop (𝓝 1) ∧
    Tendsto (fun n ↦ Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 (r n)) atTop
      (𝓝 (Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 1))

/-- The critical-line logarithm with the Poisson probability density viewed from 2. -/
def weightedLog (L : ℂ → ℂ) (t : ℝ) : ℝ :=
  ((3/2) / (Real.pi * ((3/2)^2 + t^2))) * Real.log ‖L ((1/2 : ℂ) + t * I)‖

open scoped Classical in
/-- The fixed normalized disk input identifies the actual weighted boundary integral. -/
private theorem green_of_normalized_boundary (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {a : ℝ} (ha : 0 < a) (N : ℕ)
    (hb : BoundaryMeans (normalized χ L a N)) :
    Integrable (weightedLog L) ∧
      (∫ t : ℝ, weightedLog L t) - Real.log ‖L 2‖ + (if χ = 1 then Real.log 2 else 0) =
        ∑' z : RightSite χ, (order χ z.val : ℝ) * greenKernel z.val := by
  obtain ⟨hi, r, hr, hr1, hf⟩ := hb
  obtain ⟨hL1, hbound⟩ := strip_mean τ hτ χ hχ L hL he ha N (r:=1) (by norm_num) le_rfl hi
  let f := normalized χ L a N
  let c := Real.log a - (N:ℝ)*Real.log 3
  have hbd : circleMean L 1 = Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 1 - c := by
    simpa [f, c] using hbound
  have hrm (n : ℕ) : circleMean L (r n) = Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 (r n) -
      (c + if χ = 1 then Real.log (r n) else 0) := by
    apply (strip_mean τ hτ χ hχ L hL he ha N (hr n).1 (hr n).2.le ?_).2
    apply MeromorphicOn.circleIntegrable_log_norm
    intro z hz
    have hr0 : 0 < r n := by linarith [(hr n).1]
    have hz' : ‖z‖ = r n := by simpa [Metric.mem_sphere, abs_of_pos hr0] using hz
    have h1 : z ≠ 1 := by intro h; rw [h, norm_one] at hz'; linarith [(hr n).2]
    exact (normalized_analytic τ hτ χ hχ L hL he a N (hz'.le.trans (hr n).2.le) h1).meromorphicAt
  have hδ : Tendsto (fun n ↦ if χ = 1 then Real.log (r n) else 0) atTop (𝓝 0) := by
    by_cases hh : χ = 1
    · simpa [hh, Function.comp_def] using (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp hr1
    · simp [hh]
  have hraw : Tendsto (fun n ↦ circleMean L (r n)) atTop (𝓝 (circleMean L 1)) := by
    rw [hbd]
    have hh := hf.sub ((tendsto_const_nhds (x:=c)).add hδ)
    rw [add_zero] at hh
    exact hh.congr (fun n ↦ (hrm n).symm)
  have hrl : Tendsto r atTop (𝓝[<] (1:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hr1, Eventually.of_forall fun n ↦ (hr n).2⟩
  have hid := tendsto_nhds_unique ((hraw.sub_const (Real.log ‖L 2‖)).add_const
    (if χ = 1 then Real.log 2 else 0)) ((tendsto_circleMean_logTwo τ hτ χ hχ L hL he).comp hrl)
  have hchange : circleMean L 1 = ∫ t : ℝ, weightedLog L t :=
    CayleyCauchy.circleAverage_two_add_div_one_sub (fun s : ℂ ↦ Real.log ‖L s‖)
  rw [hchange] at hid
  exact ⟨(CayleyCauchy.circleIntegrable_two_add_div_one_sub_iff (fun s : ℂ ↦ Real.log ‖L s‖)).mp hL1, hid⟩

open scoped Classical in
/-- For the ordinary finite Hecke continuation agreeing with the Euler series, the critical-line
logarithm is absolutely integrable against the Cauchy density from two. Its mean, corrected by
the Euler value at two and the possible principal pole, equals the complete right-hand Green sum. -/
theorem integrable_weightedLog_and_green (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    Integrable (weightedLog L) ∧
      (∫ t : ℝ, weightedLog L t) - Real.log ‖L 2‖ + (if χ = 1 then Real.log 2 else 0) =
        ∑' z : RightSite χ, (order χ z.val : ℝ) * greenKernel z.val := by
  obtain ⟨N, a, _, ha, hunit, hgerm, _, _, hpos, _, hlim⟩ := exists_normalized_input τ hτ χ hχ L hL he
  apply green_of_normalized_boundary τ hτ χ hχ L hL he ha N
  exact PoissonBoundary.circleIntegrable_log_norm_and_exists_radial_limit hgerm hunit
    (fun q hq hq1 ↦ hpos q (by linarith) hq1) hlim

open scoped Classical in
/-- The critical-line logarithmic mean, with its Euler reference and principal-character
pole correction, evaluated on the canonical ordinary finite continuation. -/
def criticalLogDifference (χ : U𝔽) : ℝ :=
  let L := (finiteHeckeL_exists_continuation χ).choose
  (∫ t : ℝ, weightedLog L t) - Real.log ‖L 2‖ + (if χ = 1 then Real.log 2 else 0)

/-- The full right-hand divisor measure sums to the observable critical-line logarithmic mean.
The unit circle away from one maps to the physical line at real part one half. -/
theorem hasSum_green_criticalLogDifference (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) :
    HasSum (fun z : RightSite χ ↦ (order χ z.val : ℝ) * greenKernel z.val) (criticalLogDifference χ) := by
  let L := (finiteHeckeL_exists_continuation χ).choose
  obtain ⟨hL, he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  unfold criticalLogDifference
  rw [(integrable_weightedLog_and_green τ hτ χ hχ L hL he).2]
  exact (summable_greenKernel χ).hasSum

end RiemannMasullo.HeckeBoundaryGreen
