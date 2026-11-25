module
public import RiemannMasullo.Ch10_TraceSpectral.Sec2

/-! # Theta projections in moving log-norm coordinates

The strip density seen from a far positive or negative translate converges after
normalization to its corresponding endpoint exponential. The genuine theta generators
for the shifted center are dense in ordinary class-Haar L². Together these facts give
strong convergence of the geometric and spectral projections at both ends, over every
number field. The direction `d` is either `1` or `-1`, and `r` tends to positive infinity.
-/
@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped Topology NNReal NumberField.AdeleRing
namespace RiemannMasullo
variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

private theorem thetaWindow_polynomial_ratio (x : ℝ) :
    Tendsto (fun r : ℝ ↦ (1+(r+x)^2)/(1+r^2)) atTop (𝓝 1) := by
  have hi : Tendsto (fun r : ℝ ↦ r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hn := (hi.pow 2).add ((tendsto_const_nhds (x := (1:ℝ))).add (hi.const_mul x) |>.pow 2)
  have hd := (hi.pow 2).add (tendsto_const_nhds (x := (1:ℝ)))
  have hr := hn.div hd (by norm_num)
  apply (show Tendsto (fun r : ℝ ↦ (r⁻¹^2+(1+x*r⁻¹)^2)/(r⁻¹^2+1)) atTop (𝓝 1) by simpa [Pi.div_def] using hr).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  field_simp [hr.ne', show (1+r^2:ℝ) ≠ 0 by positivity, show (r^2+1:ℝ) ≠ 0 by positivity]

private theorem thetaWindow_density (α s x : ℝ) (hα : 0 ≤ α) :
    intervalSobolevDensity (-α) α s x = Real.exp (2*α*|x|)*(1+x^2)^(s/2) := by
  unfold intervalSobolevDensity
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx, max_eq_right (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hα hx]))]
  · rw [abs_of_neg hx, max_eq_left (Real.exp_le_exp.mpr (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hα hx.le]))]
    congr 2
    ring

/-- The normalized strip density seen from a point going to the right converges to
the pure exponential density at the right endpoint. -/
theorem intervalSobolevDensity_ratio_tendsto_atTop {α : ℝ} (hα : 0 ≤ α) (s x : ℝ) :
    Tendsto (fun r : ℝ ↦ intervalSobolevDensity (-α) α s (r+x) / intervalSobolevDensity (-α) α s r)
      atTop (𝓝 (Real.exp (2*α*x))) := by
  have hp := (thetaWindow_polynomial_ratio x).rpow_const (p := s/2) (Or.inl (by norm_num))
  apply (show Tendsto (fun r : ℝ ↦ Real.exp (2*α*x)*((1+(r+x)^2)/(1+r^2))^(s/2)) atTop
    (𝓝 (Real.exp (2*α*x))) by simpa using hp.const_mul (Real.exp (2*α*x))).congr'
  filter_upwards [eventually_ge_atTop (max 0 (-x))] with r hr
  have hr₀ := (le_max_left 0 (-x)).trans hr
  have hrx : 0 ≤ r+x := by linarith [(le_max_right 0 (-x)).trans hr]
  rw [thetaWindow_density _ _ _ hα, thetaWindow_density _ _ _ hα, abs_of_nonneg hr₀, abs_of_nonneg hrx,
    Real.div_rpow (by positivity) (by positivity), mul_add, Real.exp_add]
  field_simp

private theorem thetaWindow_ratio_le {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (r x : ℝ) :
    intervalSobolevDensity (-α) α s (r+x) / intervalSobolevDensity (-α) α s r ≤
      (2:ℝ)^(s/2)*intervalSobolevDensity (-α) α s x := by
  simp only [thetaWindow_density _ _ _ hα]
  apply (div_le_iff₀ (by positivity)).mpr
  have he : Real.exp (2*α*|r+x|) ≤ Real.exp (2*α*|r|)*Real.exp (2*α*|x|) := by
    rw [← Real.exp_add, ← mul_add]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_add_le r x) (by positivity))
  have hp : 1+(r+x)^2 ≤ 2*(1+r^2)*(1+x^2) := by nlinarith [sq_nonneg (r-x), sq_nonneg (r*x)]
  have hw := Real.rpow_le_rpow (show 0 ≤ 1+(r+x)^2 by positivity) hp (by positivity : 0 ≤ s/2)
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)] at hw
  exact (mul_le_mul he hw (by positivity) (by positivity)).trans_eq (by ring)

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => continuousIdeleClassNorm F
local notation "x𝔽" => logIdeleClassNorm F

private theorem thetaWindow_L2norm {X : Type*} [MeasurableSpace X] (μ : Measure X) (v : Lp ℂ 2 μ) :
    ‖v‖^2 = ∫ x, ‖v x‖^2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
  rw [integral_ofReal, RCLike.ofReal_re]

private theorem thetaWindow_haar_approx (a : ℝ) (u : C𝔽 → ℂ) (hu : MemLp u 2 μ𝔽) {ε : ℝ}
    (hε : 0 < ε) : ∃ f : adelePolarSubspace F,
      (∫ g, ‖u g - modulationWeight m𝔽 a (adelicTheta f.val) g‖^2 ∂μ𝔽) < ε := by
  let ν := intervalSobolevMeasure μ𝔽 x𝔽 0 0 0
  have hν : ν = μ𝔽 := by simp [ν, intervalSobolevMeasure, intervalSobolevDensity]
  have hu' : MemLp u 2 ν := hν ▸ hu
  let y : CompactIntervalSobolev μ𝔽 x𝔽 0 0 0 := hu'.toLp u
  let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a 0 0 0 le_rfl le_rfl).exists.choose
  have hy : y ∈ closure (E.toLinearMap.range : Set _) := by
    change y ∈ globalThetaSobolev F a (le_refl (0:ℝ)) (le_refl (0:ℝ))
    rw [globalThetaSobolev_line_eq_top_of_le_one a 0 le_rfl (by norm_num)]
    trivial
  obtain ⟨_, ⟨v, rfl⟩, hd⟩ := Metric.mem_closure_iff.mp hy (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  let z := E (Submodule.Quotient.mk f)
  have hz := (existsUnique_globalThetaSobolevEmbedding (F := F) a 0 0 0 le_rfl le_rfl).exists.choose_spec.2 f
  have hrep : (fun g ↦ (y-z : Lp ℂ 2 ν) g) =ᵐ[ν] fun g ↦ u g - modulationWeight m𝔽 a (adelicTheta f.val) g := by
    have hz' := (show (z : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a (adelicTheta f.val) from hz)
    have ht : (z : C𝔽 → ℂ) =ᵐ[ν] modulationWeight m𝔽 a (adelicTheta f.val) := (congrArg (fun m : Measure C𝔽 ↦ ∀ᵐ g ∂m, (z g = modulationWeight m𝔽 a (adelicTheta f.val) g)) hν).mpr hz'
    filter_upwards [Lp.coeFn_sub y z, hu'.coeFn_toLp, ht] with g h₁ h₂ h₃
    exact h₁.trans (by simp [Pi.sub_apply, h₂, h₃, y])
  have hsq := (thetaWindow_L2norm ν (y-z)).symm
  have hid : (∫ g, ‖u g - modulationWeight m𝔽 a (adelicTheta f.val) g‖^2 ∂μ𝔽) = ‖y-z‖^2 := by
    refine (congrArg (fun m : Measure C𝔽 ↦ ∫ g, ‖u g - modulationWeight m𝔽 a (adelicTheta f.val) g‖^2 ∂m) hν.symm).trans ?_
    exact (integral_congr_ae (hrep.mono fun g hg ↦ congrArg (fun c : ℂ ↦ ‖c‖^2) hg.symm)).trans hsq
  refine ⟨f, hid.trans_lt ?_⟩
  have hd' : ‖y-z‖ < Real.sqrt ε := (dist_eq_norm y z).symm.trans_lt hd
  nlinarith [Real.sq_sqrt hε.le, norm_nonneg (y-z), Real.sqrt_nonneg ε]

private theorem thetaWindow_modulation (a : ℝ) (f : adelePolarSubspace F) (g : C𝔽) :
    modulationWeight m𝔽 a (adelicTheta f.val) g =
      (Real.exp (a*x𝔽 g) : ℂ) * adelicTheta f.val g := by
  change (((((m𝔽 g).val : ℝ)^a : ℝ) : ℂ)) * _ = _
  rw [Real.rpow_def_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
  rw [mul_comm _ a]
  rfl

private theorem thetaWindow_reflect_density {α : ℝ} (hα : 0 ≤ α) (s r x d : ℝ)
    (hd : d = 1 ∨ d = -1) :
    intervalSobolevDensity (-α) α s (d*r+x) = intervalSobolevDensity (-α) α s (r+d*x) := by
  rcases hd with rfl | rfl
  · simp
  · simp only [thetaWindow_density _ _ _ hα, neg_one_mul]
    rw [show -r+x = -(r+-x) by ring, abs_neg, neg_sq]

set_option maxHeartbeats 700000 in
/-- In the moving log-norm chart the normalized genuine theta vectors approximate any
fixed Haar L² packet. The same polar-free adelic source works at all sufficiently distant
centers in the chosen direction. Both signs and every nonnegative strip width and Sobolev
degree are allowed. -/
theorem globalThetaSobolev_movingWindow_approx (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (d : ℝ) (hd : d = 1 ∨ d = -1) (u : C𝔽 → ℂ) (hu : MemLp u 2 μ𝔽) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : adelePolarSubspace F,
      (∀ r : ℝ, MemLp (fun g ↦ (Real.sqrt (intervalSobolevDensity (-α) α s (d*r+x𝔽 g) /
        intervalSobolevDensity (-α) α s r) : ℂ) * modulationWeight m𝔽 a (adelicTheta f.val) g) 2 μ𝔽) ∧
      ∀ᶠ r : ℝ in atTop,
      (∫ g, ‖u g - (Real.sqrt (intervalSobolevDensity (-α) α s (d*r+x𝔽 g) /
        intervalSobolevDensity (-α) α s r) : ℂ) * modulationWeight m𝔽 a (adelicTheta f.val) g‖^2 ∂μ𝔽) < ε := by
  obtain ⟨f, hclose⟩ := thetaWindow_haar_approx (a+d*α) u hu hε
  let W := intervalSobolevDensity (-α) α s
  let v : C𝔽 → ℂ := modulationWeight m𝔽 a (adelicTheta f.val)
  let D (r : ℝ) (g : C𝔽) := Real.sqrt (W (d*r+x𝔽 g)/W r)
  have hx : Continuous x𝔽 := (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).log
    (fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')
  have hW : Continuous W := by
    change Continuous (fun x ↦ intervalSobolevDensity (-α) α s x)
    simp_rw [thetaWindow_density _ _ _ hα]
    fun_prop (disch := intros; positivity)
  have hWp (x : ℝ) : 0 < W x := by dsimp [W]; rw [thetaWindow_density _ _ _ hα]; positivity
  have hD (r : ℝ) : Continuous (D r) :=
    Real.continuous_sqrt.comp ((hW.comp (continuous_const.add hx)).div_const _)
  have hv : Continuous v := by
    rw [show v = (fun g ↦ (Real.exp (a*x𝔽 g) : ℂ) * adelicTheta f.val g) from funext (thetaWindow_modulation a f)]
    exact (Complex.continuous_ofReal.comp ((continuous_const.mul hx).rexp)).mul (adelicTheta f.val).continuous
  have hvi : Integrable (fun g ↦ ‖v g‖^2 * W (x𝔽 g)) μ𝔽 := by
    apply (globalThetaSobolev_norm (F := F) a (neg_le_self hα) hs f).1.congr
    apply Filter.Eventually.of_forall
    intro g
    change ‖adelicTheta f.val g‖^2 * intervalSobolevDensity (a + -α) (a + α) s (x𝔽 g) = ‖v g‖^2 * W (x𝔽 g)
    rw [← globalThetaSobolev_norm_density a (-α) α s (x𝔽 g)]
    dsimp only [v, W]
    rw [thetaWindow_modulation, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_pow]
    ring
  have hDr (g : C𝔽) : Tendsto (fun r ↦ D r g) atTop (𝓝 (Real.exp ((d*α)*x𝔽 g))) := by
    have hh := (intervalSobolevDensity_ratio_tendsto_atTop hα s (d*x𝔽 g)).sqrt
    have hsqr : Real.exp (2*α*(d*x𝔽 g)) = Real.exp ((d*α)*x𝔽 g)^2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    simpa only [D, W, thetaWindow_reflect_density hα s _ _ d hd, hsqr,
      Real.sqrt_sq (Real.exp_pos _).le] using hh
  let K := (2:ℝ)^(s/2)
  have hDb (r : ℝ) (g : C𝔽) : D r g ^ 2 ≤ K*W (x𝔽 g) := by
    dsimp only [D, K, W]
    rw [Real.sq_sqrt (div_nonneg (hWp _).le (hWp _).le)]
    have h := thetaWindow_ratio_le hα hs r (d*x𝔽 g)
    dsimp only [W]
    rw [thetaWindow_reflect_density hα s _ _ d hd]
    rcases hd with rfl | rfl
    · simpa using h
    · simpa [thetaWindow_density _ _ _ hα] using h
  let B (g : C𝔽) := 2*‖u g‖^2 + (2*K)*(‖v g‖^2*W (x𝔽 g))
  have hbi : Integrable B μ𝔽 := ((hu.integrable_norm_pow (by norm_num : 2 ≠ 0)).const_mul 2).add (hvi.const_mul _)
  have hlim : Tendsto (fun r : ℝ ↦ ∫ g, ‖u g - (D r g : ℂ) * v g‖^2 ∂μ𝔽) atTop
      (𝓝 (∫ g, ‖u g - (Real.exp ((d*α)*x𝔽 g) : ℂ) * v g‖^2 ∂μ𝔽)) := by
    apply tendsto_integral_filter_of_dominated_convergence B _ _ hbi _
    · exact .of_forall fun r ↦ (hu.aestronglyMeasurable.sub ((Complex.continuous_ofReal.comp (hD r)).mul hv).aestronglyMeasurable).norm.pow 2
    · refine .of_forall fun r ↦ .of_forall fun g ↦ ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h₁ := norm_sub_le (u g) ((D r g : ℂ)*v g)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h₁
      have h₂ := mul_self_le_mul_self (norm_nonneg _) h₁
      have h₃ := mul_le_mul_of_nonneg_right (hDb r g) (sq_nonneg ‖v g‖)
      dsimp only [B]
      nlinarith [sq_nonneg (‖u g‖-D r g*‖v g‖)]
    · refine .of_forall fun g ↦ ?_
      exact ((tendsto_const_nhds.sub ((Complex.continuous_ofReal.continuousAt.tendsto.comp (hDr g)).mul_const (v g))).norm.pow 2)
  have he (g : C𝔽) : (Real.exp ((d*α)*x𝔽 g) : ℂ)*v g =
      modulationWeight m𝔽 (a+d*α) (adelicTheta f.val) g := by
    dsimp only [v]
    simp only [thetaWindow_modulation, add_mul, Real.exp_add, Complex.ofReal_mul]
    ring
  simp_rw [he] at hlim
  refine ⟨f, ?_, hlim.eventually_lt_const hclose⟩
  intro r
  have hmeas := ((Complex.continuous_ofReal.comp (hD r)).mul hv).aestronglyMeasurable (μ := μ𝔽)
  apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
  apply (hvi.const_mul K).mono' (hmeas.norm.pow 2)
  refine .of_forall fun g ↦ ?_
  change ‖‖(D r g : ℂ) * v g‖^2‖ ≤ K*(‖v g‖^2*W (x𝔽 g))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖(D r g : ℂ) * v g‖), norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  exact (mul_le_mul_of_nonneg_right (hDb r g) (sq_nonneg ‖v g‖)).trans_eq (by ring)

variable (F) in
/-- The closed space spanned by genuine polar-free theta sources after conjugating by the
strip weight and expressing them in Haar coordinates centered at log radius `r`. -/
abbrev globalThetaSobolevMovingWindow (a α s r : ℝ) :
    Submodule ℂ (Lp ℂ 2 (ideleClassTamagawaMeasure F)) :=
  (Submodule.span ℂ {v : Lp ℂ 2 (ideleClassTamagawaMeasure F) | ∃ f : adelePolarSubspace F,
    (v : C𝔽 → ℂ) =ᵐ[μ𝔽] fun g ↦ (Real.sqrt (intervalSobolevDensity (-α) α s (r+x𝔽 g) /
      intervalSobolevDensity (-α) α s r) : ℂ) * modulationWeight m𝔽 a (adelicTheta f.val) g}).topologicalClosure

/-- In either moving chart the genuine theta projection converges strongly to the identity
and the complementary spectral projection converges strongly to zero. -/
theorem globalThetaSobolev_movingWindow_projections (a : ℝ) {α s : ℝ} (hα : 0 ≤ α)
    (hs : 0 ≤ s) (d : ℝ) (hd : d = 1 ∨ d = -1) (u : Lp ℂ 2 μ𝔽) :
    let V (r : ℝ) := globalThetaSobolevMovingWindow F a α s (d*r)
    Tendsto (fun r ↦ (V r).starProjection u) atTop (𝓝 u) ∧
      Tendsto (fun r ↦ (V r)ᗮ.starProjection u) atTop (𝓝 0) := by
  intro V
  have hmain : Tendsto (fun r ↦ (V r).starProjection u) atTop (𝓝 u) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨f, hm, hlim⟩ := globalThetaSobolev_movingWindow_approx a hα hs d hd u (Lp.memLp u)
      (sq_pos_of_pos hε)
    filter_upwards [hlim] with r hr
    let v := (hm r).toLp _
    have he : intervalSobolevDensity (-α) α s (d*r) = intervalSobolevDensity (-α) α s r := by
      simpa using thetaWindow_reflect_density hα s r 0 d hd
    have hgen : v ∈ V r := by
      apply Submodule.le_topologicalClosure
      apply Submodule.subset_span
      refine ⟨f, ?_⟩
      simpa only [he] using (hm r).coeFn_toLp
    have hint : ‖u-v‖^2 = ∫ g, ‖(u : C𝔽 → ℂ) g -
        (Real.sqrt (intervalSobolevDensity (-α) α s (d*r+x𝔽 g) /
        intervalSobolevDensity (-α) α s r) : ℂ) * modulationWeight m𝔽 a (adelicTheta f.val) g‖^2 ∂μ𝔽 := by
      calc
        _ = ∫ g, ‖((u-v : Lp ℂ 2 μ𝔽) : C𝔽 → ℂ) g‖^2 ∂μ𝔽 := thetaWindow_L2norm _ _
        _ = _ := integral_congr_ae (by
          filter_upwards [Lp.coeFn_sub u v, (hm r).coeFn_toLp] with g hg hv
          dsimp only [Pi.sub_apply] at hg
          rw [hg, hv])
    have hdist : dist u v < ε := by rw [dist_eq_norm]; nlinarith [hint, hr, norm_nonneg (u-v)]
    rw [dist_comm, (V r).dist_starProjection_eq_infDist]
    exact (Metric.infDist_le_dist_of_mem hgen).trans_lt hdist
  refine ⟨hmain, ?_⟩
  have h := (tendsto_const_nhds (x := u) (f := atTop)).sub hmain
  simpa only [Submodule.starProjection_orthogonal', sub_apply,
    one_apply_eq_self, sub_self] using h

end RiemannMasullo
