module

public import RiemannMasullo.Ch01_Introduction.Sec4
public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# A theta-lift norm criterion for exterior-zero cancellation

For Theorem 12.5.1.1 (pp. 519–520), prescribe one compact log-norm profile and its
modulations on the visible half-line. At any completed Hecke zero, the full Mellin moment
of a polar-free theta lift vanishes. A weighted Cauchy–Schwarz estimate on the complementary
half-line gives a lower bound on its hidden norm. A sufficiently small upper bound on a
family of such lifts would imply the exterior sum identity for every positive strip width.
-/

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Asymptotics Classical NNReal NumberField.AdeleRing
@[expose] public noncomputable section

namespace RiemannMasullo

set_option quotPrecheck false
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker

/-- The homogeneous theta profile of a polar-free source along an idèle norm section,
including the character and the shift to the central line. -/
def centeredLogThetaLift (χ : PontryaginDual C𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (f : adelePolarSubspace F) (x : ℝ) : ℂ :=
  let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
  let e := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let g : C𝔽 := QuotientGroup.mk (τ (e x))
  homogeneousAdelicTheta ω f.val g * (χ g : ℂ) * Complex.exp ((x : ℂ) / 2)

/-- The weighted L² norm of the log profile below the cutoff −R. -/
def hiddenThetaCost (α s R : ℝ) (u : ℝ → ℂ) : ℝ :=
  Real.sqrt (∫ x in Iic (-R), ‖u x‖ ^ 2 * intervalSobolevDensity (-α) α s x)

private theorem hiddenThetaCost_integrable_of_decay (u : ℝ → ℂ) (hc : Continuous u)
    (hdec : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atBot, ‖u x‖ ≤ C * Real.exp (N * x))
    {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s) (R : ℝ) :
    IntegrableOn (fun x ↦ ‖u x‖ ^ 2 * intervalSobolevDensity (-α) α s x) (Iic (-R)) := by
  let d := intervalSobolevDensity (-α) α s
  have hd : Continuous d := by
    change Continuous (fun x : ℝ ↦ max (Real.exp (2 * -α * x)) (Real.exp (2 * α * x)) * (1 + x ^ 2) ^ (s / 2))
    fun_prop (disch := intros; positivity)
  have hd0 (x : ℝ) : 0 ≤ d x := mul_nonneg (le_trans (Real.exp_pos _).le (le_max_left ..)) (by positivity)
  have hbd (x : ℝ) (hx : x ≤ 0) : d x ≤ Real.exp (-(2 * α + s) * x) := by
    have hbase : 1 + x ^ 2 ≤ Real.exp (-2 * x) := by
      calc
        1 + x ^ 2 ≤ (1 - x) ^ 2 := by nlinarith
        _ ≤ (Real.exp (-x)) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-x)]) 2
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hp : (1 + x ^ 2) ^ (s / 2) ≤ Real.exp (-s * x) := by
      refine (Real.rpow_le_rpow (by positivity) hbase (by linarith : 0 ≤ s / 2)).trans_eq ?_
      rw [← Real.exp_mul]; congr 1; ring
    change max _ _ * _ ≤ _
    rw [max_eq_left (Real.exp_le_exp.mpr (by nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hx]))]
    calc _ ≤ Real.exp (2 * (-α) * x) * Real.exp (-s * x) := mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
         _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * α + s + 1)
  obtain ⟨C, hC, h⟩ := hdec N
  apply (((hc.norm.pow 2).mul hd).locallyIntegrable.locallyIntegrableOn _).integrableOn_of_isBigO_atBot (g := Real.exp)
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨C ^ 2, ?_⟩
    filter_upwards [h, eventually_le_atBot (0 : ℝ)] with x hx hx0
    change ‖‖u x‖ ^ 2 * d x‖ ≤ C ^ 2 * ‖Real.exp x‖
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hd0 _)), Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      _ ≤ (C * Real.exp (N * x)) ^ 2 * Real.exp (-(2 * α + s) * x) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx 2) (hbd x hx0) (hd0 _) (sq_nonneg _)
      _ = C ^ 2 * Real.exp ((2 * N - (2 * α + s)) * x) := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
        congr 2; push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2 * N - (2 * α + s) - 1 by linarith) hx0])) (sq_nonneg _)
  · refine ⟨Iic 0, Iic_mem_atBot _, ?_⟩
    simpa using integrableOn_exp_mul_Iic (show (0 : ℝ) < 1 by norm_num) (0 : ℝ)

private theorem centeredLogThetaLift_energy (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (f : adelePolarSubspace F) {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s) (R : ℝ) :
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
      (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)
    let e := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    let g (x : ℝ) : IdeleClassGroup (𝓞 F) F := QuotientGroup.mk (τ (e x))
    let u (x : ℝ) := homogeneousAdelicTheta ω f.val (g x) * (χ (g x) : ℂ) * Complex.exp ((x : ℂ) / 2)
    Continuous u ∧ IntegrableOn (fun x ↦ ‖u x‖ ^ 2 * intervalSobolevDensity (-α) α s x) (Iic (-R)) := by
  intro ω e g u
  have hg : Continuous g := continuous_quotient_mk'.comp (τ.continuous.comp e.continuous)
  have hcont : Continuous u := ((homogeneousAdelicTheta_continuous ω f.val).comp hg |>.mul
    (continuous_subtype_val.comp (χ.continuous.comp hg))).mul (by fun_prop)
  refine ⟨hcont, hiddenThetaCost_integrable_of_decay u hcont (fun N ↦ ?_) ha hs R⟩
  obtain ⟨C, T, hC, _, hθ⟩ := homogeneousAdelicTheta_decay_both ω f.val (Or.inl f.property) N
  refine ⟨C, hC.le, ?_⟩
  filter_upwards [eventually_lt_atBot (-T), eventually_le_atBot (0 : ℝ)] with x hx hx0
  have he : Real.log (((ideleClassNorm F (g x)).val : ℝ)) = x := by
    rw [show ideleClassNorm F (g x) = e x from hτ (e x)]; exact Real.log_exp x
  have hh := hθ (g x) (by change T < |Real.log (((ideleClassNorm F (g x)).val : ℝ))|; rw [he, abs_of_nonpos hx0]; linarith)
  change ‖homogeneousAdelicTheta ω f.val (g x)‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (((ideleClassNorm F (g x)).val : ℝ))|) at hh
  rw [he, abs_of_nonpos hx0, neg_mul_neg] at hh
  dsimp only [u]
  rw [norm_mul, norm_mul, Circle.norm_coe, mul_one]
  refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans hh
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  simpa using (show x / 2 ≤ 0 by linarith)

private theorem centeredLogThetaLift_homogeneous_zero (χ : PontryaginDual C𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (hτ : RightInverse τ (ideleNorm F)) (f : adelePolarSubspace F) {w : ℂ}
    (hz : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) w) :
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
    homogeneousThetaMellinIntegral τ ω f.val (ideleClassNormTwist χ w) = 0 := by
  intro ω
  obtain ⟨hf, hF⟩ := (mem_adelePolarSubspace _).mp f.property
  let Zf (s : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ s)
  have ho : max 0 (meromorphicOrderAt (continuedCompletedHeckeL χ) w) ≤ meromorphicOrderAt Zf w :=
    (isLeast_globalThetaMellinIntegral_orders χ w).2 ⟨f, rfl⟩
  have ha : AnalyticAt ℂ Zf w := (globalThetaMellinIntegral_entire_of_vanishing f.val hf hF χ).analyticAt w
  have hzero : Zf w = 0 := by
    by_contra hn
    exact (hz.trans_le ((le_max_right ..).trans ho)).ne (ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn).symm
  obtain ⟨hhom, hglob⟩ := (exists_globalPolarThetaMellin χ τ hτ).choose_spec f w
  have he := congrFun (globalThetaMellinIntegral_eq_continuation_of_vanishing f.val hf hF) (ideleClassNormTwist χ w)
  exact hhom.symm.trans (hglob.trans (he.symm.trans hzero))

private theorem centeredLogThetaLift_haar_exp (v : ℝ≥0ˣ → ℂ) (hi : Integrable v positiveRealHaar) :
    let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    Integrable (fun x ↦ v (e x)) ∧ ∫ x, v (e x) = ∫ t, v t ∂positiveRealHaar := by
  intro e
  let : BorelSpace ℝ≥0ˣ := by
    constructor
    change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace ℝ≥0) = _
    rw [Units.isEmbedding_val₀.eq_induced, borel_comap, BorelSpace.measurable_eq (α := ℝ≥0)]
  have he (x : ℝ) : (e x).val = (Real.exp x).toNNReal := by
    apply NNReal.eq
    exact (Real.coe_toNNReal _ (Real.exp_pos x).le).symm
  have hmap : positiveRealHaar = volume.map e := by
    apply congrArg (fun a : ℝ → ℝ≥0ˣ ↦ volume.map a)
    funext x
    exact Units.ext (he x).symm
  rw [hmap] at hi ⊢
  exact ⟨e.measurableEmbedding.integrable_map_iff.mp hi, (e.measurableEmbedding.integral_map v).symm⟩

private theorem centeredLogThetaLift_zero_moment (χ : PontryaginDual C𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (hτ : RightInverse τ (ideleNorm F)) (f : adelePolarSubspace F) {z : ℂ}
    (hz : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) (z + 1 / 2)) :
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
    let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    let g (x : ℝ) : C𝔽 := QuotientGroup.mk (τ (e x))
    let u (x : ℝ) := homogeneousAdelicTheta ω f.val (g x) * (χ (g x) : ℂ) * Complex.exp ((x : ℂ) / 2)
    Integrable (fun x ↦ u x * Complex.exp (z * (x : ℂ))) ∧
      ∫ x, u x * Complex.exp (z * (x : ℂ)) = 0 := by
  intro ω e g u
  let w := z + 1 / 2
  let v (t : ℝ≥0ˣ) := homogeneousAdelicTheta ω f.val (QuotientGroup.mk (τ t)) *
    ideleClassNormTwist χ w (QuotientGroup.mk (τ t))
  have hi : Integrable v positiveRealHaar := by
    apply homogeneousThetaMellinIntegral_integrable_on_component τ ω f.val hτ (Or.inl f.property) (ideleClassNormTwist χ w)
    refine ⟨mem_univ _, ?_⟩
    intro k
    change (χ k.val : ℂ) * ((((ideleClassNorm F k.val).val : ℝ) : ℂ) ^ w) = (χ k.val : ℂ)
    rw [MonoidHom.mem_ker.mp k.property]
    simp
  have hlog (x : ℝ) : v (e x) = u x * Complex.exp (z * (x : ℂ)) := by
    have hn : ideleClassNorm F (g x) = e x := hτ (e x)
    have hc : ideleClassNormTwist χ w (g x) = (χ (g x) : ℂ) * ((Real.exp x : ℝ) : ℂ) ^ w := by
      change (χ (g x) : ℂ) * ((((ideleClassNorm F (g x)).val : ℝ) : ℂ) ^ w) = _
      rw [hn]
      rfl
    have hp : ((Real.exp x : ℝ) : ℂ) ^ w = Complex.exp ((x : ℂ) / 2) * Complex.exp (z * (x : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
        ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, ← Complex.exp_add]
      congr 1
      dsimp [w]
      ring
    change homogeneousAdelicTheta ω f.val (g x) * ideleClassNormTwist χ w (g x) = _
    rw [hc, hp]
    simp only [u, mul_assoc]
  have hsum : ∫ t, v t ∂positiveRealHaar = 0 := centeredLogThetaLift_homogeneous_zero χ τ hτ f hz
  obtain ⟨hvi, hvs⟩ := centeredLogThetaLift_haar_exp v hi
  refine ⟨hvi.congr (ae_of_all _ hlog), ?_⟩
  exact (integral_congr_ae (ae_of_all _ fun x ↦ (hlog x).symm)).trans (hvs.trans hsum)

private theorem hiddenThetaCost_dual_weight {α β s R : ℝ} (h : 0 < α + β) (hs : 0 ≤ s) (hR : 0 ≤ R) :
    let d := intervalSobolevDensity (-α) α s
    let m (x : ℝ) := Real.exp (2 * β * x) / d x
    IntegrableOn m (Iic (-R)) ∧ ∫ x in Iic (-R), m x ≤
      Real.exp (-(2 * (α + β)) * R) / ((2 * (α + β)) * (1 + R ^ 2) ^ (s / 2)) := by
  intro d m
  let c := 2 * (α + β)
  let k := (1 + R ^ 2) ^ (s / 2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hd (x : ℝ) : 0 < d x := mul_pos (lt_of_lt_of_le (Real.exp_pos _) (le_max_left ..)) (by positivity)
  have E : IntegrableOn (fun x : ℝ ↦ Real.exp (c * x) / k) (Iic (-R)) :=
    (integrableOn_exp_mul_Iic hc _).div_const k
  have hle (x : ℝ) (hx : x ∈ Iic (-R)) : m x ≤ Real.exp (c * x) / k := by
    have hw : k ≤ (1 + x ^ 2) ^ (s / 2) :=
      Real.rpow_le_rpow (by positivity) (by
        nlinarith [mul_nonneg (show 0 ≤ -x - R by linarith [mem_Iic.mp hx])
          (show 0 ≤ -x + R by linarith [mem_Iic.mp hx])]) (by linarith)
    have hw' : Real.exp (2 * (-α) * x) * k ≤ d x :=
      mul_le_mul (le_max_left ..) hw hk.le (lt_of_lt_of_le (Real.exp_pos _) (le_max_left ..)).le
    apply (div_le_div_iff₀ (hd x) hk).mpr
    calc
      Real.exp (2 * β * x) * k = Real.exp (c * x) * (Real.exp (2 * (-α) * x) * k) := by
        rw [← mul_assoc, ← Real.exp_add]; congr 2; dsimp [c]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hw' (Real.exp_pos _).le
  have hm : IntegrableOn m (Iic (-R)) := by
    have hdm : Measurable d := by change Measurable (fun x : ℝ ↦ max (Real.exp (2 * -α * x)) (Real.exp (2 * α * x)) * (1 + x ^ 2) ^ (s / 2)); fun_prop
    apply E.mono' ((by fun_prop : Measurable (fun x : ℝ ↦ Real.exp (2 * β * x))).div hdm).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    change ‖Real.exp (2 * β * x) / d x‖ ≤ _
    rw [Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le (hd x).le)]
    exact hle x hx
  refine ⟨hm, (setIntegral_mono_on hm E measurableSet_Iic hle).trans_eq ?_⟩
  rw [integral_div, integral_exp_mul_Iic hc]
  change Real.exp (c * -R) / c / k = Real.exp (-c * R) / (c * k)
  rw [mul_neg, neg_mul, div_div]

private theorem hiddenThetaCost_tail_moment {α s R : ℝ} {z : ℂ} (h : 0 < α + z.re) (hs : 0 ≤ s) (hR : 0 ≤ R)
    (u : ℝ → ℂ) (hu : Measurable u)
    (hi : IntegrableOn (fun x ↦ ‖u x‖ ^ 2 * intervalSobolevDensity (-α) α s x) (Iic (-R))) :
    ‖∫ x in Iic (-R), u x * Complex.exp (z * (x : ℂ))‖ ≤
      Real.sqrt (∫ x in Iic (-R), ‖u x‖ ^ 2 * intervalSobolevDensity (-α) α s x) *
      Real.sqrt (Real.exp (-(2 * (α + z.re)) * R) / ((2 * (α + z.re)) * (1 + R ^ 2) ^ (s / 2))) := by
  let d := intervalSobolevDensity (-α) α s
  let F (x : ℝ) := Real.sqrt (‖u x‖ ^ 2 * d x)
  let G (x : ℝ) := Real.sqrt (Real.exp (2 * z.re * x) / d x)
  let μ := volume.restrict (Iic (-R))
  have hd (x : ℝ) : 0 < d x := mul_pos (lt_of_lt_of_le (Real.exp_pos _) (le_max_left ..)) (by positivity)
  have hdmeas : Measurable d := by
    change Measurable (fun x : ℝ ↦ max (Real.exp (2 * -α * x)) (Real.exp (2 * α * x)) * (1 + x ^ 2) ^ (s / 2))
    fun_prop
  have hF₂ (x : ℝ) : (F x) ^ 2 = ‖u x‖ ^ 2 * d x := Real.sq_sqrt (mul_nonneg (sq_nonneg _) (hd _).le)
  have hG₂ (x : ℝ) : (G x) ^ 2 = Real.exp (2 * z.re * x) / d x := Real.sq_sqrt (div_nonneg (Real.exp_pos _).le (hd _).le)
  obtain ⟨hGi, hGt⟩ := hiddenThetaCost_dual_weight (β := z.re) h hs hR
  have hF : MemLp F 2 μ :=
    (memLp_two_iff_integrable_sq (by dsimp [F]; fun_prop)).mpr
      (hi.congr (ae_of_all _ fun x ↦ (hF₂ x).symm))
  have hGm : Measurable G := Real.continuous_sqrt.measurable.comp ((by fun_prop : Measurable (fun x : ℝ ↦ Real.exp (2 * z.re * x))).div hdmeas)
  have hG : MemLp G 2 μ :=
    (memLp_two_iff_integrable_sq hGm.aestronglyMeasurable).mpr
      (hGi.congr (ae_of_all _ fun x ↦ (hG₂ x).symm))
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (f := F) (g := G) (ae_of_all _ fun x ↦ Real.sqrt_nonneg _) (ae_of_all _ fun x ↦ Real.sqrt_nonneg _)
    (by simpa using hF) (by simpa using hG)
  have he (x : ℝ) : ‖u x * Complex.exp (z * (x : ℂ))‖ = F x * G x := by
    rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    dsimp [F, G]
    rw [← Real.sqrt_mul (mul_nonneg (sq_nonneg _) (hd x).le)]
    have hp : ‖u x‖ ^ 2 * d x * (Real.exp (2 * z.re * x) / d x) = (‖u x‖*Real.exp (z.re * x)) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat, show (2 : ℝ)* (z.re * x) = 2 * z.re * x by ring]
      field_simp [(hd x).ne']
    rw [hp, Real.sqrt_sq (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
  calc
    _ ≤ ∫ x, ‖u x * Complex.exp (z * (x : ℂ))‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, F x * G x ∂μ := integral_congr_ae (ae_of_all _ he)
    _ ≤ Real.sqrt (∫ x, (F x) ^ 2 ∂μ) * Real.sqrt (∫ x, (G x) ^ 2 ∂μ) := by
      simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using hcs
    _ ≤ _ := by
      simp only [hF₂, hG₂]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hGt) (Real.sqrt_nonneg _)

private theorem hiddenThetaCost_visible_moment {α s R : ℝ} {z : ℂ} (h : 0 < α + z.re) (hs : 0 ≤ s) (hR : 0 ≤ R)
    (u : ℝ → ℂ) (hu : Measurable u)
    (hi : IntegrableOn (fun x ↦ ‖u x‖ ^ 2 * intervalSobolevDensity (-α) α s x) (Iic (-R)))
    (hm : Integrable (fun x ↦ u x * Complex.exp (z * (x : ℂ))))
    (hz : ∫ x, u x * Complex.exp (z * (x : ℂ)) = 0) :
    ‖∫ x in Ioi (-R), u x * Complex.exp (z * (x : ℂ))‖ ≤
      Real.sqrt (∫ x in Iic (-R), ‖u x‖ ^ 2 * intervalSobolevDensity (-α) α s x) *
      Real.sqrt (Real.exp (-(2 * (α + z.re)) * R) / ((2 * (α + z.re)) * (1 + R ^ 2) ^ (s / 2))) := by
  let p (x : ℝ) := u x * Complex.exp (z * (x : ℂ))
  have hsp : (∫ x in Iic (-R), p x) + (∫ x in Ioi (-R), p x) = 0 := by
    exact (by simpa only [compl_Iic] using integral_add_compl (f := p) measurableSet_Iic hm (s := Iic (-R)) : (∫ x in Iic (-R), p x) + (∫ x in Ioi (-R), p x) = ∫ x, p x).trans hz
  have hneg : ∫ x in Ioi (-R), p x = -(∫ x in Iic (-R), p x) := by linear_combination hsp
  change ‖∫ x in Ioi (-R), p x‖ ≤ _
  rw [hneg, norm_neg]
  exact hiddenThetaCost_tail_moment h hs hR u hu hi

/-- At a completed Hecke zero, the Mellin moment on the visible half-line gives a lower
bound on the weighted norm of every genuine lift on the hidden half-line. -/
theorem centeredLogThetaLift_visible_moment_le (χ : PontryaginDual C𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (hτ : RightInverse τ (ideleNorm F)) (f : adelePolarSubspace F) {α s R : ℝ} {z : ℂ}
    (ha : 0 ≤ α) (hs : 0 ≤ s) (hR : 0 ≤ R) (h : 0 < α + z.re)
    (hz : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) (z + 1 / 2)) :
    ‖∫ x in Ioi (-R), centeredLogThetaLift χ τ f x * Complex.exp (z * (x : ℂ))‖ ≤
      hiddenThetaCost α s R (centeredLogThetaLift χ τ f) *
        Real.sqrt (Real.exp (-(2 * (α + z.re)) * R) /
          ((2 * (α + z.re)) * (1 + R ^ 2) ^ (s / 2))) := by
  obtain ⟨hc, hi⟩ := centeredLogThetaLift_energy χ τ hτ f ha hs R
  obtain ⟨hm, hz⟩ := centeredLogThetaLift_zero_moment χ τ hτ f hz
  exact hiddenThetaCost_visible_moment h hs hR (centeredLogThetaLift χ τ f) hc.measurable hi hm hz

/-- A fixed nonzero visible moment cannot survive a subcritical upper exponent. -/
private theorem hiddenThetaCost_moment_eq_zero_of_upper_bound {a b ε s C : ℝ} (h : 0 < a + b) (hs : 0 ≤ s)
    (hε : ε < b) (hC : 0 ≤ C) (M : ℂ)
    (hM : ∀ᶠ n : ℕ in atTop, ∃ E : ℝ, 0 ≤ E ∧ E ≤ C * Real.exp ((a + ε) * n) ∧
      ‖M‖ ≤ E * Real.sqrt (Real.exp (-(2 * (a + b)) * n) / ((2 * (a + b)) * (1 + (n : ℝ) ^ 2) ^ (s / 2)))) :
    M = 0 := by
  let D := C / Real.sqrt (2 * (a + b))
  have ht : Tendsto (fun n : ℕ ↦ D * Real.exp (-(b - ε) * (n : ℝ))) atTop (𝓝 0) := by
    have he : Tendsto (fun x : ℝ ↦ Real.exp (-(b - ε) * x)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (Filter.Tendsto.const_mul_atTop_of_neg
        (by linarith : -(b - ε) < 0) tendsto_id)
    simpa using (he.comp tendsto_natCast_atTop_atTop).const_mul D
  have hb : ∀ᶠ n : ℕ in atTop, ‖M‖ ≤ D * Real.exp (-(b - ε) * (n : ℝ)) := by
    filter_upwards [hM] with n hn
    obtain ⟨E, hE, hE', hne⟩ := hn
    have hk : 1 ≤ (1 + (n : ℝ) ^ 2) ^ (s / 2) :=
      Real.one_le_rpow (by nlinarith [sq_nonneg (n : ℝ)]) (by linarith)
    have hc : 0 < 2 * (a + b) := by linarith
    have hexp : Real.sqrt (Real.exp (-(2 * (a + b)) * (n : ℝ))) =
        Real.exp (-(a + b) * (n : ℝ)) := by
      rw [show -(2 * (a + b)) * (n : ℝ) = 2 * (-(a + b) * (n : ℝ)) by ring,
        two_mul, Real.exp_add, ← sq, Real.sqrt_sq (Real.exp_pos _).le]
    calc
      ‖M‖ ≤ _ := hne
      _ ≤ C * Real.exp ((a + ε) * (n : ℝ)) *
          Real.sqrt (Real.exp (-(2 * (a + b)) * (n : ℝ)) / (2 * (a + b))) := by
        apply mul_le_mul hE' _ (Real.sqrt_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)
        apply Real.sqrt_le_sqrt
        exact div_le_div_of_nonneg_left (Real.exp_pos _).le hc (le_mul_of_one_le_right hc.le hk)
      _ = D * Real.exp (-(b - ε) * (n : ℝ)) := by
        rw [Real.sqrt_div (Real.exp_pos _).le, hexp]
        rw [show -(b - ε) * (n : ℝ) = (a + ε) * (n : ℝ) + (-(a + b) * (n : ℝ)) by ring, Real.exp_add]
        dsimp [D]
        ring
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto ht hb) (norm_nonneg _))

/-- Matching a fixed nonzero Mellin moment with a cheaper exponent excludes the proposed zero.
The lifts may depend on the cutoff, the test, the field and the character. -/
private theorem no_completed_zero_of_visible_moment_cost (χ : PontryaginDual C𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (hτ : RightInverse τ (ideleNorm F)) {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s) {z : ℂ}
    (hz : 0 < z.re) (M : ℂ) (hM : M ≠ 0)
    (hcost : ∃ ε : ℝ, ε < z.re ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ∃ f : adelePolarSubspace F,
        (∫ x in Ioi (-(n : ℝ)), centeredLogThetaLift χ τ f x * Complex.exp (z * (x : ℂ))) = M ∧
        hiddenThetaCost α s n (centeredLogThetaLift χ τ f) ≤ C * Real.exp ((α + ε) * n)) :
    ¬ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) (z + 1 / 2) := by
  intro hzero
  obtain ⟨ε, hε, C, hC, hcost⟩ := hcost
  apply hM
  apply hiddenThetaCost_moment_eq_zero_of_upper_bound (a := α) (b := z.re) (ε := ε) (s := s) (by linarith) hs hε hC
  filter_upwards [hcost] with n hn
  obtain ⟨f, hf, hbound⟩ := hn
  refine ⟨hiddenThetaCost α s n (centeredLogThetaLift χ τ f), Real.sqrt_nonneg _, hbound, ?_⟩
  rw [← hf]
  exact centeredLogThetaLift_visible_moment_le χ τ hτ f ha hs (Nat.cast_nonneg n) (by linarith) hzero

/-- For one positive bump, only its modulations have to be lifted at the near-baseline rate.
Constants and lifts can vary with the frequency, the slack in the exponent, and the character. -/
private theorem no_right_completed_zeros_of_modulated_bump_lifts (χ : PontryaginDual C𝔽)
    (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F)) {α s : ℝ}
    (ha : 0 ≤ α) (hs : 0 ≤ s) (b : ℝ → ℝ) (hb : Continuous b) (hbcs : HasCompactSupport b)
    (hn : 0 ≤ b) (hv : ∃ x, b x ≠ 0) (hsupp : ∀ x ≤ 0, b x = 0)
    (hlift : ∀ γ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ∃ f : adelePolarSubspace F, (∀ x : ℝ, -(n : ℝ) < x →
        centeredLogThetaLift χ τ f x = (b x : ℂ) * Complex.exp (-(γ : ℂ) * Complex.I * (x : ℂ))) ∧
        hiddenThetaCost α s n (centeredLogThetaLift χ τ f) ≤ C * Real.exp ((α + ε) * n)) :
    ∀ z : ℂ, 0 < z.re → ¬ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) (z + 1 / 2) := by
  intro z hz
  let G (x : ℝ) := b x * Real.exp (z.re * x)
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hsG : HasCompactSupport G := hbcs.mul_right
  obtain ⟨x, hx⟩ := hv
  have hM : 0 < ∫ t, G t :=
    hG.integral_pos_of_hasCompactSupport_nonneg_ne_zero hsG
      (fun t ↦ mul_nonneg (hn t) (Real.exp_pos _).le) (mul_ne_zero hx (Real.exp_pos _).ne')
  apply no_completed_zero_of_visible_moment_cost χ τ hτ ha hs hz (((∫ t, G t) : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr hM.ne')
  obtain ⟨C, hC, hl⟩ := hlift z.im (z.re / 2) (half_pos hz)
  refine ⟨z.re / 2, by linarith, C, hC, ?_⟩
  filter_upwards [hl] with n hit
  obtain ⟨f, hf, he⟩ := hit
  refine ⟨f, ?_, he⟩
  have hident (y : ℝ) (hy : -(n : ℝ) < y) :
      centeredLogThetaLift χ τ f y * Complex.exp (z * (y : ℂ)) = (G y : ℂ) := by
    rw [hf y hy, mul_assoc, ← Complex.exp_add]
    have hphase : -(z.im : ℂ) * Complex.I * (y : ℂ) + z * (y : ℂ) = (z.re : ℂ) * (y : ℂ) := by
      calc _ = ((z.re : ℂ) + (z.im : ℂ) * Complex.I - (z.im : ℂ) * Complex.I) * (y : ℂ) := by
               rw [Complex.re_add_im]; ring
           _ = _ := by ring
    rw [hphase]
    simp [G, Complex.ofReal_exp]
  calc
    _ = ∫ y in Ioi (-(n : ℝ)), (G y : ℂ) :=
      setIntegral_congr_fun measurableSet_Ioi (fun y hy ↦ hident y hy)
    _ = ∫ y, (G y : ℂ) := setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro y hy
      have h : y ≤ -(n : ℝ) := le_of_not_gt hy
      simp [G, hsupp y (h.trans (neg_nonpos.mpr (Nat.cast_nonneg _)))])
    _ = _ := integral_ofReal

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
local notation "order(" χ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)

/-- A single nonnegative bump and all its frequency modulations suffice for the exterior
sum in Theorem 12.5.1.1 (pp. 519–520) if their polar-free lifts have hidden cost of order
exp((α + ε)n) for every positive ε. The constants may depend on the character and frequency. -/
theorem exteriorCancellation_of_modulated_bump_cost (σ : ℝ≥0ˣ →ₜ* I𝔽)
    (hσ : RightInverse σ (ideleNorm F))
    {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s) (b : ℝ → ℝ) (hb : Continuous b)
    (hbcs : HasCompactSupport b) (hn : 0 ≤ b) (hv : ∃ x, b x ≠ 0) (hsupp : ∀ x ≤ 0, b x = 0)
    (hlift : ∀ (χ : PontryaginDual C𝔽) (γ ε : ℝ), 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ∃ f : adelePolarSubspace F, (∀ x : ℝ, -(n : ℝ) < x →
        centeredLogThetaLift χ σ f x = (b x : ℂ) * Complex.exp (-(γ : ℂ) * Complex.I * (x : ℂ))) ∧
        hiddenThetaCost α s n (centeredLogThetaLift χ σ f) ≤ C * Real.exp ((α + ε) * n))
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0) {a : ℝ} (hpos : 0 < a) :
    HasSum (fun z : {p : {η : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, η (τ t) = 1} × ℂ //
        0 < order(p.1.val, p.2) ∧ a ≤ |p.2.re - 1 / 2|} ↦
      ((order(z.val.1.val, z.val.2) : ℤ) : ℂ) *
        modulatedFourierMellin m𝔽 univ hm𝔽 (ideleClassTamagawaMeasure F) φ.val
          (ideleClassNormTwist z.val.1.val (z.val.2 - 1 / 2))) 0 := by
  have hr (χ : PontryaginDual C𝔽) (w : ℂ) (hw : 1 / 2 < w.re) :
      meromorphicOrderAt (continuedCompletedHeckeL χ) w ≤ 0 := by
    have h := no_right_completed_zeros_of_modulated_bump_lifts χ σ hσ ha hs b hb hbcs hn hv hsupp
      (hlift χ) (w - 1 / 2) (by rw [Complex.sub_re]; norm_num; linarith)
    simpa only [sub_add_cancel, not_lt] using h
  have h := (introTrace_exterior_cancellation_iff_all_zeros_in_window τ hτ a).mpr (by
    intro χ w _ _ ho
    have eq : w.re = 1 / 2 := le_antisymm
      (le_of_not_gt (fun hw ↦ ho.not_ge (hr χ w hw)))
      (le_of_not_gt (fun hw ↦ ho.not_ge (introTrace_completedL_no_left_zeros χ (hr χ⁻¹) w hw)))
    simpa only [eq, sub_self, abs_zero] using hpos)
  simpa only [modulatedFourierMellin, relativeVerticalStrip, Set.preimage_univ, Set.indicator_univ] using h φ hφ

end RiemannMasullo
