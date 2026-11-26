module

public import RiemannMasullo.Ch01_Introduction.Sec4
public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import RiemannMasullo.Ch11_ShellStructure.Sec1b
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.Module.Cardinality
import RiemannMasullo.ForMathlib.Analysis.MellinTransform.Weighted

/-!
# A theta-lift norm criterion for exterior-zero cancellation

For Theorem 12.5.1.1 (pp. 519–520), prescribe one compact log-norm profile and its
modulations on the visible half-line. At any completed Hecke zero, the full Mellin moment
of a polar-free theta lift vanishes. A weighted Cauchy–Schwarz estimate on the complementary
half-line gives a lower bound on its hidden norm. A sufficiently small upper bound on a
family of such lifts would imply the exterior sum identity for every positive strip width.
-/

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped ComplexConjugate InnerProductSpace Asymptotics Classical NNReal NumberField.AdeleRing
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

private theorem centeredLogThetaLift_homogeneous_mellin (χ : PontryaginDual C𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (hτ : RightInverse τ (ideleNorm F)) (f : adelePolarSubspace F) (w : ℂ) :
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
    homogeneousThetaMellinIntegral τ ω f.val (ideleClassNormTwist χ w) =
      globalThetaMellinIntegral f.val (ideleClassNormTwist χ w) := by
  intro ω
  obtain ⟨hf, hF⟩ := (mem_adelePolarSubspace _).mp f.property
  obtain ⟨hhom, hglob⟩ := (exists_globalPolarThetaMellin χ τ hτ).choose_spec f w
  have he := congrFun (globalThetaMellinIntegral_eq_continuation_of_vanishing f.val hf hF) (ideleClassNormTwist χ w)
  exact hhom.symm.trans (hglob.trans he.symm)

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
  exact (centeredLogThetaLift_homogeneous_mellin χ τ hτ f w).trans hzero

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

private theorem centeredLogThetaLift_mellin_moment (χ : PontryaginDual C𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (hτ : RightInverse τ (ideleNorm F)) (f : adelePolarSubspace F) (z : ℂ) :
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
    let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    let g (x : ℝ) : C𝔽 := QuotientGroup.mk (τ (e x))
    let u (x : ℝ) := homogeneousAdelicTheta ω f.val (g x) * (χ (g x) : ℂ) * Complex.exp ((x : ℂ) / 2)
    Integrable (fun x ↦ u x * Complex.exp (z * (x : ℂ))) ∧
      ∫ x, u x * Complex.exp (z * (x : ℂ)) = globalThetaMellinIntegral f.val (ideleClassNormTwist χ (z + 1 / 2)) := by
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
  have hsum : ∫ t, v t ∂positiveRealHaar = globalThetaMellinIntegral f.val (ideleClassNormTwist χ w) :=
    centeredLogThetaLift_homogeneous_mellin χ τ hτ f w
  obtain ⟨hvi, hvs⟩ := centeredLogThetaLift_haar_exp v hi
  refine ⟨hvi.congr (ae_of_all _ hlog), ?_⟩
  exact (integral_congr_ae (ae_of_all _ fun x ↦ (hlog x).symm)).trans (hvs.trans hsum)

private theorem centeredLogThetaLift_zero_moment (χ : PontryaginDual C𝔽) (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (hτ : RightInverse τ (ideleNorm F)) (f : adelePolarSubspace F) {z : ℂ}
    (hz : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) (z + 1 / 2)) :
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
    let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    let g (x : ℝ) : C𝔽 := QuotientGroup.mk (τ (e x))
    let u (x : ℝ) := homogeneousAdelicTheta ω f.val (g x) * (χ (g x) : ℂ) * Complex.exp ((x : ℂ) / 2)
    Integrable (fun x ↦ u x * Complex.exp (z * (x : ℂ))) ∧
      ∫ x, u x * Complex.exp (z * (x : ℂ)) = 0 := by
  obtain ⟨hi, he⟩ := centeredLogThetaLift_mellin_moment χ τ hτ f z
  exact ⟨hi, he.trans ((centeredLogThetaLift_homogeneous_mellin χ τ hτ f _).symm.trans
    (centeredLogThetaLift_homogeneous_zero χ τ hτ f hz))⟩

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

private theorem centeredLogThetaLift_profile_zeros_countable (b : ℝ → ℝ) (hb : Continuous b)
    (hc : HasCompactSupport b) (hn : 0 ≤ b) (hv : ∃ x, b x ≠ 0) :
    {z : ℂ | (∫ x : ℝ, (b x : ℂ) * Complex.exp (z * x)) = 0}.Countable := by
  let M (z : ℂ) := ∫ x : ℝ, (b x : ℂ) * Complex.exp (z * x)
  have hp (z : ℂ) (x : ℝ) : (Real.exp x : ℂ) ^ z = Complex.exp (z * x) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm]
  have ha : AnalyticOnNhd ℂ M univ := by
    have h := analyticOnNhd_integral_mul_cpow volume (fun x ↦ (b x : ℂ)) Real.exp
      (Complex.continuous_ofReal.comp hb).measurable Real.continuous_exp.measurable
      Real.exp_pos (U := univ) isOpen_univ (fun a _ ↦ ?_)
    · simpa only [preimage_univ, hp, M] using h
    · simp only [Complex.norm_real]
      apply Continuous.integrable_of_hasCompactSupport _ hc.norm.mul_right
      exact hb.norm.mul (Real.continuous_exp.rpow_const (fun x ↦ Or.inl (Real.exp_pos x).ne'))
  obtain ⟨x, hx⟩ := hv
  have hzero : M 0 ≠ 0 := by
    simp only [M, zero_mul, Complex.exp_zero, mul_one]
    rw [show (∫ x : ℝ, (b x : ℂ)) = ((∫ x : ℝ, b x : ℝ) : ℂ) from integral_ofReal]
    exact Complex.ofReal_ne_zero.mpr (hb.integral_pos_of_hasCompactSupport_nonneg_ne_zero (μ := volume) hc hn hx).ne'
  exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (compl_mem_codiscrete_iff.mp (ha.preimage_zero_mem_codiscrete hzero)).2

/-- Two real exponential tilts of a positive compact profile have no common Mellin zero.
The second tilt may be chosen in any prescribed nonempty interval. -/
private theorem exists_tilt_without_common_moment_zero (b : ℝ → ℝ) (hb : Continuous b)
    (hc : HasCompactSupport b) (hn : 0 ≤ b) (hv : ∃ x, b x ≠ 0) {l r : ℝ} (hlr : l < r) :
    ∃ t ∈ Ioo l r, ∀ z : ℂ,
      (∫ x : ℝ, (b x : ℂ) * Complex.exp (z * x)) ≠ 0 ∨
      (∫ x : ℝ, (b x : ℂ) * Complex.exp ((z + t) * x)) ≠ 0 := by
  let Z := {z : ℂ | (∫ x : ℝ, (b x : ℂ) * Complex.exp (z * x)) = 0}
  have hZ : Z.Countable := centeredLogThetaLift_profile_zeros_countable b hb hc hn hv
  let E := (fun x : ℝ ↦ (x : ℂ)) ⁻¹' ((fun p : ℂ × ℂ ↦ p.1 - p.2) '' (Z ×ˢ Z))
  have hE : E.Countable := ((hZ.prod hZ).image _).preimage Complex.ofReal_injective
  obtain ⟨t, ht, he⟩ := (hE.dense_compl ℝ).inter_open_nonempty _ isOpen_Ioo (nonempty_Ioo.mpr hlr)
  refine ⟨t, ht, fun z ↦ or_iff_not_imp_left.mpr fun hz bad ↦ he ?_⟩
  refine ⟨(z + t, z), ⟨bad, not_ne_iff.mp hz⟩, ?_⟩
  dsimp
  ring

private theorem no_right_zeros_of_tilt_moment_cost (χ : PontryaginDual C𝔽)
    (σ : ℝ≥0ˣ →ₜ* I𝔽) (hσ : RightInverse σ (ideleNorm F)) {α s : ℝ}
    (ha : 0 ≤ α) (hs : 0 ≤ s) (b : ℝ → ℝ) (hb : ∀ x ≤ 0, b x = 0)
    (t : ℝ) (z : ℂ) (hz : 0 < z.re)
    (hM : (∫ x : ℝ, (b x : ℂ) * Complex.exp ((z + t) * x)) ≠ 0)
    (hlift : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ∃ f : adelePolarSubspace F,
        (∀ x : ℝ, -(n : ℝ) < x → centeredLogThetaLift χ σ f x =
          ((b x * Real.exp (t * x) : ℝ) : ℂ)) ∧
        hiddenThetaCost α s n (centeredLogThetaLift χ σ f) ≤ C * Real.exp ((α + ε) * n)) :
    ¬ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) (z + 1 / 2) := by
  apply no_completed_zero_of_visible_moment_cost χ σ hσ ha hs hz _ hM
  obtain ⟨C, hC, hc⟩ := hlift (z.re / 2) (half_pos hz)
  refine ⟨z.re / 2, by linarith, C, hC, ?_⟩
  filter_upwards [hc] with n hn
  obtain ⟨f, hf, hcost⟩ := hn
  refine ⟨f, ?_, hcost⟩
  calc
    _ = ∫ x in Ioi (-(n : ℝ)), (b x : ℂ) * Complex.exp ((z + t) * x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change centeredLogThetaLift χ σ f x * _ = (b x : ℂ) * _
      rw [hf x hx, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_mul,
        mul_assoc, ← Complex.exp_add]
      congr 2
      ring
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro x hx
      rw [hb x ((le_of_not_gt hx).trans (neg_nonpos.mpr (Nat.cast_nonneg _)))]
      simp)

private theorem exteriorZeros_empty_of_normalized_right_bound (τ : ℝ≥0ˣ →ₜ* C𝔽)
    {a : ℝ} (ha : 0 < a)
    (hr : ∀ (χ : PontryaginDual C𝔽), (∀ u, χ (τ u) = 1) → ∀ w : ℂ, 1 / 2 < w.re →
      meromorphicOrderAt (continuedCompletedHeckeL χ) w ≤ 0) :
    IsEmpty {p : {χ : PontryaginDual C𝔽 // ∀ u : ℝ≥0ˣ, χ (τ u) = 1} × ℂ //
      0 < order(p.1.val, p.2) ∧ a ≤ |p.2.re - 1 / 2|} := by
  refine ⟨fun ⟨⟨⟨χ, hχ⟩, w⟩, hw, hedge⟩ ↦ ?_⟩
  change 0 < order(χ, w) at hw
  change a ≤ |w.re - 1 / 2| at hedge
  rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec χ).1.meromorphicOn (mem_univ _)] at hw
  have hzero : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) w := by
    cases h : meromorphicOrderAt (continuedCompletedHeckeL χ) w with
    | top => simp
    | coe k => simpa [h] using hw
  have hχinv : ∀ u, χ⁻¹ (τ u) = 1 := by
    intro u
    change (χ (τ u))⁻¹ = 1
    rw [hχ u, inv_one]
  have hline : w.re = 1 / 2 := le_antisymm
    (le_of_not_gt fun h ↦ hzero.not_ge (hr χ hχ w h))
    (le_of_not_gt fun h ↦ hzero.not_ge (introTrace_completedL_no_left_zeros χ (hr χ⁻¹ hχinv) w h))
  simp [hline, ha.not_ge] at hedge

local notation "C[" K "]" => IdeleClassGroup (𝓞 K) K
local notation "I[" K "]" => IdeleGroup (𝓞 K) K
local notation "extZeros(" K ", " τ ", " a ")" =>
  {p : {χ : PontryaginDual C[K] // ∀ u : ℝ≥0ˣ, χ (τ u) = 1} × ℂ //
    0 < MeromorphicOn.divisor (continuedCompletedHeckeL (F := K) p.1.val) univ p.2 ∧
      a ≤ |p.2.re - 1 / 2|}

/-- For a fixed positive log-norm bump, two real profiles suffice across all number fields.
The second is an arbitrarily small real exponential tilt of the first. If both have
polar-free lifts of near-baseline hidden cost for each character trivial on the chosen
norm section, there are no exterior zero indices at any positive width. -/
theorem exists_two_profiles_for_exterior_zero_exclusion
    (b : ℝ → ℝ) (hb : Continuous b) (hc : HasCompactSupport b)
    (hn : 0 ≤ b) (hv : ∃ x, b x ≠ 0) (hsupp : ∀ x ≤ 0, b x = 0) {l r : ℝ} (hlr : l < r) :
    ∃ t ∈ Ioo l r, ∀ (K : Type*) [Field K] [NumberField K]
      (σ : ℝ≥0ˣ →ₜ* I[K]), RightInverse σ (ideleNorm K) →
      ∀ (τ : ℝ≥0ˣ →ₜ* C[K]) (α s : ℝ), 0 ≤ α → 0 ≤ s →
      (∀ (χ : PontryaginDual C[K]), (∀ u, χ (τ u) = 1) →
        ∀ c ∈ ({0, t} : Set ℝ), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
          ∃ f : adelePolarSubspace K,
            (∀ x : ℝ, -(n : ℝ) < x → centeredLogThetaLift χ σ f x =
              ((b x * Real.exp (c * x) : ℝ) : ℂ)) ∧
            hiddenThetaCost α s n (centeredLogThetaLift χ σ f) ≤ C * Real.exp ((α + ε) * n)) →
      ∀ a : ℝ, 0 < a → IsEmpty extZeros(K, τ, a) := by
  obtain ⟨t, ht, hdetect⟩ := exists_tilt_without_common_moment_zero b hb hc hn hv hlr
  refine ⟨t, ht, ?_⟩
  intro K _ _ σ hσ τ α s ha hs hlift a hpos
  apply exteriorZeros_empty_of_normalized_right_bound τ hpos
  intro χ hχ w hw
  let z := w - 1 / 2
  have hz : 0 < z.re := by simp only [z, Complex.sub_re]; norm_num; linarith
  have hshift : z + 1 / 2 = w := sub_add_cancel _ _
  suffices h : ¬ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) (z + 1 / 2) by
    simpa only [hshift, not_lt] using h
  obtain h | h := hdetect z
  · apply no_right_zeros_of_tilt_moment_cost χ σ hσ ha hs b hsupp 0 z hz
      (by simpa only [Complex.ofReal_zero, add_zero] using h) (hlift χ hχ 0 (by simp))
  · exact no_right_zeros_of_tilt_moment_cost χ σ hσ ha hs b hsupp t z hz h
      (hlift χ hχ t (by simp))

private theorem thetaKernel_denominator_ne_zero {s t : ℂ} (hs : 1 / 2 < s.re) (ht : 1 / 2 < t.re) : s + conj t - 1 ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re, Complex.zero_re] at hr
  linarith

private def thetaKernelFactor (w t : ℂ) := (t - w) / (t + conj w - 1)

private def thetaKernelDeflate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : ℂ → E) (w t : ℂ) : E :=
  (conj (thetaKernelFactor w t))⁻¹ • (U t - ((w + conj w - 1) / (w + conj t - 1)) • U w)

private theorem thetaKernelDeflate_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : ℂ → E) (w s t : ℂ) (hw : 1 / 2 < w.re) (hs : 1 / 2 < s.re) (ht : 1 / 2 < t.re)
    (hsw : s ≠ w) (htw : t ≠ w)
    (hst : ⟪U s, U t⟫_ℂ = 1 / (s + conj t - 1))
    (hsw' : ⟪U s, U w⟫_ℂ = 1 / (s + conj w - 1))
    (hwt : ⟪U w, U t⟫_ℂ = 1 / (w + conj t - 1))
    (hww : ⟪U w, U w⟫_ℂ = 1 / (w + conj w - 1)) :
    ⟪thetaKernelDeflate U w s, thetaKernelDeflate U w t⟫_ℂ = 1 / (s + conj t - 1) := by
  simp only [thetaKernelDeflate, thetaKernelFactor, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
    hst, hsw', hwt, hww, map_sub, map_div₀, map_add, map_one, map_inv₀,
    starRingEnd_self_apply]
  have hconj : conj t - conj w ≠ 0 := sub_ne_zero.mpr (fun h ↦ htw ((starRingEnd ℂ).injective h))
  have hs' := thetaKernel_denominator_ne_zero hs hw
  have ht' := thetaKernel_denominator_ne_zero hw ht
  have hst' := thetaKernel_denominator_ne_zero hs ht
  have hww' := thetaKernel_denominator_ne_zero hw hw
  have hws' : conj w + s - 1 ≠ 0 := by simpa only [add_comm (conj w) s] using hs'
  have htw' : conj t + w - 1 ≠ 0 := by simpa only [add_comm (conj t) w] using ht'
  field_simp [sub_ne_zero.mpr hsw, hconj, hs', ht', hst', hww', hws', htw']
  ring

private theorem thetaKernel_inner_le_prod {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Finset ℂ) (g : E) (U : ℂ → E) (hS : ∀ w ∈ S, 1 / 2 < w.re)
    (hK : ∀ s ∈ insert 1 S, ∀ t ∈ insert 1 S, ⟪U s, U t⟫_ℂ = 1 / (s + conj t - 1))
    (hzero : ∀ w ∈ S, ⟪U w, g⟫_ℂ = 0) :
    ‖⟪U 1, g⟫_ℂ‖ ≤ ‖g‖ * ∏ w ∈ S, ‖thetaKernelFactor w 1‖ := by
  classical
  induction S using Finset.induction_on generalizing U with
  | empty =>
    have h := hK 1 (by simp) 1 (by simp)
    have hn : ‖U 1‖ ^ 2 = 1 := by
      rw [inner_self_eq_norm_sq_to_K] at h
      exact_mod_cast (show ((‖U 1‖ : ℂ) ^ 2) = 1 by simpa using h)
    have hnorm : ‖U 1‖ = 1 := by nlinarith [norm_nonneg (U 1)]
    simpa [hnorm] using norm_inner_le_norm (𝕜 := ℂ) (U 1) g
  | @insert w S hw ih =>
    have hw' := hS w (Finset.mem_insert_self ..)
    have hz := hzero w (Finset.mem_insert_self ..)
    by_cases he : w = 1
    · subst w
      rw [hz, norm_zero]
      positivity
    have hsub : insert (1 : ℂ) S ⊆ insert 1 (insert w S) := by
      intro t ht
      simp only [Finset.mem_insert] at ht ⊢
      tauto
    have hpos (t : ℂ) (ht : t ∈ insert 1 S) : 1 / 2 < t.re := by
      rcases Finset.mem_insert.mp ht with rfl | h
      · norm_num
      · exact hS t (Finset.mem_insert_of_mem h)
    have hne (t : ℂ) (ht : t ∈ insert 1 S) : t ≠ w := by
      rcases Finset.mem_insert.mp ht with rfl | h
      · exact Ne.symm he
      · exact fun ht ↦ hw (ht ▸ h)
    have hwmem : w ∈ insert (1 : ℂ) (insert w S) := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    have hstep (t : ℂ) : ⟪thetaKernelDeflate U w t, g⟫_ℂ = (thetaKernelFactor w t)⁻¹ * ⟪U t, g⟫_ℂ := by
      simp only [thetaKernelDeflate, inner_smul_left, inner_sub_left, hz, mul_zero, sub_zero, map_inv₀,
        starRingEnd_self_apply]
    have hb := ih (thetaKernelDeflate U w) (fun t ht ↦ hS t (Finset.mem_insert_of_mem ht))
      (fun s hs t ht ↦ thetaKernelDeflate_inner U w s t hw' (hpos s hs) (hpos t ht) (hne s hs) (hne t ht)
        (hK s (hsub hs) t (hsub ht)) (hK s (hsub hs) w hwmem)
        (hK w hwmem t (hsub ht)) (hK w hwmem w hwmem))
      (fun t ht ↦ by rw [hstep, hzero t (Finset.mem_insert_of_mem ht), mul_zero])
    rw [hstep, norm_mul, norm_inv] at hb
    have hp : 0 < ‖thetaKernelFactor w 1‖ := norm_pos_iff.mpr (div_ne_zero (sub_ne_zero.mpr (Ne.symm he))
      (thetaKernel_denominator_ne_zero (by norm_num : 1 / 2 < (1 : ℂ).re) hw'))
    rw [Finset.prod_insert hw]
    calc
      ‖⟪U 1, g⟫_ℂ‖ = ‖thetaKernelFactor w 1‖ * (‖thetaKernelFactor w 1‖⁻¹ * ‖⟪U 1, g⟫_ℂ‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
      _ ≤ _ := (mul_le_mul_of_nonneg_left hb hp.le).trans_eq (by ring)

private theorem thetaKernel_distance_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Finset ℂ) (g : E) (U : ℂ → E) (hS : ∀ w ∈ S, 1 / 2 < w.re)
    (hK : ∀ s ∈ insert 1 S, ∀ t ∈ insert 1 S, ⟪U s, U t⟫_ℂ = 1 / (s + conj t - 1))
    (hzero : ∀ w ∈ S, ⟪U w, g⟫_ℂ = 0) :
    1 - (∏ w ∈ S, ‖thetaKernelFactor w 1‖) ^ 2 ≤ ‖U 1 - g‖ ^ 2 := by
  let b := ∏ w ∈ S, ‖thetaKernelFactor w 1‖
  have h := thetaKernel_inner_le_prod S g U hS hK hzero
  have h1 := hK 1 (Finset.mem_insert_self ..) 1 (Finset.mem_insert_self ..)
  rw [inner_self_eq_norm_sq_to_K] at h1
  have hn : ‖U 1‖ ^ 2 = 1 := by exact_mod_cast (show ((‖U 1‖ : ℂ) ^ 2) = 1 by simpa using h1)
  rw [@norm_sub_sq ℂ]
  have hr := Complex.re_le_norm (⟪U 1, g⟫_ℂ)
  change _ ≤ ‖U 1‖ ^ 2 - 2 * (⟪U 1, g⟫_ℂ).re + ‖g‖ ^ 2
  change 1 - b ^ 2 ≤ _
  change _ ≤ ‖g‖ * b at h
  nlinarith [sq_nonneg (‖g‖ - b)]

private theorem thetaKernel_halfLine_distance (S : Finset ℂ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Iic (0 : ℝ)))) (hS : ∀ w ∈ S, 1 / 2 < w.re)
    (hz : ∀ w ∈ S, (∫ x in Iic (0 : ℝ), u x * Complex.exp ((w - 1 / 2) * x)) = 0) :
    1 - (∏ w ∈ S, (‖1 - w‖ / ‖w‖)) ^ 2 ≤
      ∫ x in Iic (0 : ℝ), ‖Complex.exp ((x : ℂ) / 2) - u x‖ ^ 2 := by
  classical
  let μ := volume.restrict (Iic (0 : ℝ))
  let φ (z : ℂ) (x : ℝ) := Complex.exp ((conj z - 1 / 2) * x)
  have hc2 : conj (2 : ℂ) = 2 := map_ofNat _ _
  have hm (z : ℂ) (hz : 1 / 2 < z.re) : MemLp (φ z) 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm (show Continuous (φ z) by dsimp [φ]; fun_prop).aestronglyMeasurable).2
    have h (x : ℝ) : ‖φ z x‖ ^ 2 = Real.exp ((2 * (z.re - 1 / 2)) * x) := by
      dsimp only [φ]
      rw [Complex.norm_exp, ← Real.exp_nat_mul]
      congr 1
      simp
      ring
    simp only [h]
    exact integrableOn_exp_mul_Iic (by linarith : 0 < 2 * (z.re - 1 / 2)) 0
  let U (z : ℂ) : Lp ℂ 2 μ := if h : 1 / 2 < z.re then (hm z h).toLp _ else 0
  have hU (z : ℂ) (h : 1 / 2 < z.re) : ⇑(U z) =ᵐ[μ] φ z := by
    simpa only [U, dite_eq_left h] using (hm z h).coeFn_toLp
  have hpos (s : ℂ) (hs : s ∈ insert 1 S) : 1 / 2 < s.re := by
    rcases Finset.mem_insert.mp hs with rfl | h
    · norm_num
    · exact hS _ h
  have hK (s : ℂ) (hs : s ∈ insert 1 S) (t : ℂ) (ht : t ∈ insert 1 S) :
      ⟪U s, U t⟫_ℂ = 1 / (s + conj t - 1) := by
    rw [L2.inner_def]
    have he : (fun x : ℝ ↦ ⟪U s x, U t x⟫_ℂ) =ᵐ[μ] fun x ↦ Complex.exp ((s + conj t - 1) * x) := by
      filter_upwards [hU s (hpos s hs), hU t (hpos t ht)] with x hx hy
      rw [hx, hy, RCLike.inner_apply']
      dsimp only [φ]
      rw [← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      simp [hc2]
      ring
    rw [integral_congr_ae he]
    have h : 0 < (s + conj t - 1).re := by
      simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re]
      linarith [hpos s hs, hpos t ht]
    simpa [μ] using integral_exp_mul_complex_Iic h 0
  let g : Lp ℂ 2 μ := hu.toLp u
  have hg : ⇑g =ᵐ[μ] u := hu.coeFn_toLp
  have hgzero (s : ℂ) (hs : s ∈ S) : ⟪U s, g⟫_ℂ = 0 := by
    rw [L2.inner_def, ← hz s hs]
    apply integral_congr_ae
    filter_upwards [hU s (hS s hs), hg] with x hx hy
    rw [hx, hy, RCLike.inner_apply]
    dsimp only [φ]
    rw [← Complex.exp_conj]
    simp [hc2]
  have hf (w : ℂ) : ‖thetaKernelFactor w 1‖ = ‖1 - w‖ / ‖w‖ := by
    simp [thetaKernelFactor]
  have h := thetaKernel_distance_sq S g U hS hK hgzero
  simp only [hf] at h
  apply h.trans_eq
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (U 1) g, hU 1 (by norm_num), hg] with x hs hx hy
  have hv : φ 1 x = Complex.exp ((x : ℂ) / 2) := by
    dsimp only [φ]
    rw [map_one]
    congr 1
    ring
  simp only [inner_self_eq_norm_sq, hs, Pi.sub_apply, hx, hy, hv]

private theorem thetaKernel_factor_defect (w : ℂ) (hw : 1 / 2 < w.re) :
    1 - (‖1 - w‖ / ‖w‖) ^ 2 = (2 * w.re - 1) / ‖w‖ ^ 2 := by
  have hw0 : w ≠ 0 := fun h ↦ by simp [h] at hw; linarith
  have hn := norm_ne_zero_iff.mpr hw0
  rw [div_pow]
  field_simp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  ring

private theorem thetaKernel_sum_defects_le (S : Finset ℂ) (e : ℝ) (he : e < 1)
    (hS : ∀ w ∈ S, 1 / 2 < w.re)
    (h : 1 - (∏ w ∈ S, (‖1 - w‖ / ‖w‖)) ^ 2 ≤ e) :
    ∑ w ∈ S, (2 * w.re - 1) / ‖w‖ ^ 2 ≤ - Real.log (1 - e) := by
  let b (w : ℂ) := (‖1 - w‖ / ‖w‖) ^ 2
  have hprod : 1 - e ≤ ∏ w ∈ S, b w := by
    simpa only [b, ← Finset.prod_pow] using (show 1 - e ≤ (∏ w ∈ S, (‖1 - w‖ / ‖w‖)) ^ 2 by linarith)
  have hp : 0 < ∏ w ∈ S, b w := (sub_pos.mpr he).trans_le hprod
  have hb (w : ℂ) (hw : w ∈ S) : 0 < b w := (sq_nonneg _).lt_of_ne' (Finset.prod_ne_zero_iff.mp hp.ne' w hw)
  have hl := Real.log_le_log (sub_pos.mpr he) hprod
  rw [Real.log_prod (fun w hw ↦ (hb w hw).ne')] at hl
  have hsum : ∑ w ∈ S, (2 * w.re - 1) / ‖w‖ ^ 2 ≤ ∑ w ∈ S, -Real.log (b w) := by
    apply Finset.sum_le_sum
    intro w hw
    rw [← thetaKernel_factor_defect w (hS w hw)]
    change 1 - b w ≤ _
    linarith [Real.log_le_sub_one_of_pos (hb w hw)]
  rw [Finset.sum_neg_distrib] at hsum
  linarith

private theorem thetaKernel_split_local_zero (F : ℂ → ℂ) (w : ℂ) (m : ℕ) (hm : 0 < m)
    (hf : AnalyticAt ℂ F w) (ho : analyticOrderAt F w = m) :
    ∃ p : Fin m → ℂ → ℂ, (∀ i, Tendsto (p i) (𝓝 0) (𝓝 w)) ∧
      ∀ᶠ c in 𝓝[≠] (0 : ℂ), Injective (fun i ↦ p i c) ∧ ∀ i, F (p i c) = c := by
  obtain ⟨A, hA, ha, hfac⟩ := hf.analyticOrderAt_eq_natCast.mp ho
  let v (z : ℂ) := (A z / A w) ^ ((m : ℂ)⁻¹)
  have hz : A w / A w = 1 := div_self ha
  have hv := ((Complex.hasStrictDerivAt_cpow_const (c := (m : ℂ)⁻¹)
    (show A w / A w ∈ Complex.slitPlane by rw [hz]; exact Complex.one_mem_slitPlane))).comp w
      (hA.hasStrictDerivAt.div_const (A w))
  let f (z : ℂ) := (z - w) * v z
  have hf' : HasStrictDerivAt f 1 w := by
    have hs : HasStrictDerivAt (fun z : ℂ ↦ z - w) 1 w := (hasStrictDerivAt_id w).sub_const w
    simpa [f, v, ha, Function.comp_def, Pi.mul_def] using hs.mul hv
  have hf0 : f w = 0 := by simp [f]
  let inv := hf'.localInverse f 1 w one_ne_zero
  have hinv : inv 0 = w := by
    have h := (hf'.eventually_left_inverse one_ne_zero).self_of_nhds
    simpa only [inv, hf0] using h
  have ht : Tendsto inv (𝓝 0) (𝓝 w) := by
    have h : Tendsto inv (𝓝 (f w)) (𝓝 (inv (f w))) := (hf'.to_localInverse one_ne_zero).hasDerivAt.continuousAt.tendsto
    simpa only [hf0, hinv] using h
  have hright : ∀ᶠ z in 𝓝 (0 : ℂ), f (inv z) = z := by
    simpa only [inv, hf0] using hf'.eventually_right_inverse one_ne_zero
  have hformula : ∀ᶠ z in 𝓝 (0 : ℂ), F (inv z) = z ^ m * A w := by
    filter_upwards [ht.eventually hfac, hright] with z hF hR
    calc
      F (inv z) = (f (inv z)) ^ m * A w := by
        rw [hF]
        simp only [f, v, mul_pow, Complex.cpow_nat_inv_pow _ hm.ne', smul_eq_mul]
        field_simp
      _ = _ := by rw [hR]
  let ζ := Complex.exp (2 * Real.pi * Complex.I / m)
  have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp _ hm.ne'
  let y (i : Fin m) (c : ℂ) := ζ ^ i.val * ((c / A w) ^ ((m : ℂ)⁻¹))
  have hmp : 0 < ((m : ℂ)⁻¹).re := by simpa using (inv_pos.mpr (Nat.cast_pos.mpr hm : 0 < (m : ℝ)))
  have ht0 (i : Fin m) : Tendsto (y i) (𝓝 0) (𝓝 0) := by
    have hv0 := (Complex.continuousAt_cpow_const_of_re_pos (z := 0) (Or.inl (by simp)) hmp).tendsto
    have hn : (m : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hm.ne')
    have hlim : Tendsto (fun c : ℂ ↦ c / A w) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_id.div_const (A w)).continuousAt (x := (0 : ℂ)) |>.tendsto
    simpa [y, Complex.zero_cpow hn] using (hv0.comp hlim).const_mul (ζ ^ i.val)
  refine ⟨fun i c ↦ inv (y i c), fun i ↦ ht.comp (ht0 i), ?_⟩
  have he : ∀ᶠ c in 𝓝 (0 : ℂ), ∀ i : Fin m, f (inv (y i c)) = y i c ∧
      F (inv (y i c)) = (y i c)^m * A w :=
    Filter.eventually_all.mpr fun i ↦ (ht0 i).eventually (hright.and hformula)
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with c hc hc0
  have hy : (c / A w) ^ ((m : ℂ)⁻¹) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero hc0 ha))
  constructor
  · intro i j h
    have hij := congrArg f h
    rw [(hc i).1, (hc j).1] at hij
    exact Fin.ext (hζ.pow_inj i.isLt j.isLt (mul_right_cancel₀ hy hij))
  · intro i
    rw [(hc i).2]
    change (ζ ^ i.val * ((c / A w) ^ ((m : ℂ)⁻¹))) ^ m * A w = c
    rw [mul_pow, ← pow_mul, Nat.mul_comm i.val m, pow_mul, hζ.pow_eq_one,
      one_pow, one_mul, Complex.cpow_nat_inv_pow _ hm.ne', div_mul_cancel₀ _ ha]

private theorem thetaKernel_split_finite_zeros {ι : Type*} [Fintype ι] (w : ι → ℂ) (hw : Injective w)
    (m : ι → ℕ) (hm : ∀ i, 0 < m i) (F : ℂ → ℂ) (hF : ∀ i, AnalyticAt ℂ F (w i))
    (htop : ∀ i, analyticOrderAt F (w i) ≠ ⊤)
    (ho : ∀ i, (m i : ℕ∞) ≤ analyticOrderAt F (w i)) :
    ∃ p : (Σ i, Fin (m i)) → ℂ → ℂ, (∀ i, Tendsto (p i) (𝓝 0) (𝓝 (w i.1))) ∧
      ∀ᶠ c in 𝓝[≠] (0 : ℂ), Injective (fun i ↦ p i c) ∧ ∀ i, F (p i c) = c := by
  let n (i : ι) := (analyticOrderAt F (w i)).toNat
  have hn (i : ι) : analyticOrderAt F (w i) = n i := (ENat.natCast_toNat (htop i)).symm
  have hmn (i : ι) : m i ≤ n i := by exact_mod_cast (ho i).trans_eq (hn i)
  choose p hp hpt using fun i ↦ thetaKernel_split_local_zero F (w i) (n i) ((hm i).trans_le (hmn i)) (hF i) (hn i)
  let q (i : Σ i, Fin (m i)) := p i.1 (Fin.castLE (hmn i.1) i.2)
  have hq (i : Σ i, Fin (m i)) : Tendsto (q i) (𝓝 0) (𝓝 (w i.1)) := hp _ _
  refine ⟨q, hq, ?_⟩
  have hsep (i j : Σ i, Fin (m i)) :
      ∀ᶠ c in 𝓝 (0 : ℂ), i.1 ≠ j.1 → q i c ≠ q j c := by
    by_cases h : i.1 = j.1
    · exact Eventually.of_forall fun _ h' ↦ (h' h).elim
    have hlim := (hq i).sub (hq j)
    have hne := hlim.eventually (eventually_ne_nhds (sub_ne_zero.mpr (hw.ne h)))
    exact hne.mono fun _ h' _ ↦ sub_ne_zero.mp h'
  have hsep' := Filter.eventually_all.mpr fun i ↦ Filter.eventually_all.mpr (hsep i)
  filter_upwards [hsep'.filter_mono nhdsWithin_le_nhds, Filter.eventually_all.mpr hpt] with c hdiff hsame
  refine ⟨?_, fun i ↦ (hsame i.1).2 _⟩
  rintro ⟨i, k⟩ ⟨j, l⟩ he
  by_cases h : i = j
  · subst j
    have he' := (hsame i).1 he
    have hkl : k = l := Fin.ext (congrArg (fun j : Fin (n i) ↦ j.val) he')
    rw [hkl]
  · exact False.elim (hdiff ⟨i,k⟩ ⟨j,l⟩ h he)

private theorem thetaKernel_multiple_distance {ι : Type*} [Fintype ι] (w : ι → ℂ) (hw : Injective w)
    (hr : ∀ i, 1 / 2 < (w i).re) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (u : ℝ → ℂ) (hu : MemLp u 2 (volume.restrict (Iic (0 : ℝ))))
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F univ) (ho : ∀ i, (m i : ℕ∞) ≤ analyticOrderAt F (w i))
    (hI : ∀ z : ℂ, 1 / 2 < z.re → IntegrableOn (fun x : ℝ ↦ u x * Complex.exp ((z - 1 / 2) * x)) (Iic 0))
    (hZ : ∀ z : ℂ, 1 / 2 < z.re → F z = z * ∫ x in Iic (0 : ℝ), u x * Complex.exp ((z - 1 / 2) * x)) :
    1 - (∏ i, (‖1 - w i‖ / ‖w i‖) ^ m i) ^ 2 ≤
      ∫ x in Iic (0 : ℝ), ‖Complex.exp ((x : ℂ) / 2) - u x‖ ^ 2 := by
  classical
  by_cases h1 : F 1 = 0
  · have h := thetaKernel_halfLine_distance {1} u hu (by simp; norm_num) (by
      intro z hz
      rw [Finset.mem_singleton.mp hz]
      simpa [hZ 1 (by norm_num)] using h1)
    simp at h
    exact (sub_le_self _ (sq_nonneg _)).trans h
  have ht (i : ι) : analyticOrderAt F (w i) ≠ ⊤ := by
    intro hz
    have he := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (w i) (fun z ↦ hF z (mem_univ z))).mp hz
    exact h1 (congrFun he 1)
  obtain ⟨p, hp, hpc⟩ := thetaKernel_split_finite_zeros w hw m hm F (fun i ↦ hF _ (mem_univ _)) ht ho
  let h (x : ℝ) := Complex.exp ((x : ℂ) / 2)
  let μ := volume.restrict (Iic (0 : ℝ))
  have hh : MemLp h 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm (show Continuous h by dsimp [h]; fun_prop).aestronglyMeasurable).2
    have he (x : ℝ) : ‖h x‖ ^ 2 = Real.exp x := by
      simp [h, Complex.norm_exp, ← Real.exp_nat_mul]
      ring
    simp only [he]
    simpa [μ, IntegrableOn] using integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1) 0
  have hnorm (v : ℝ → ℂ) (hv : MemLp v 2 μ) :
      (∫ x, ‖v x‖ ^ 2 ∂μ) = ‖hv.toLp v‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp] with x hx
    simp only [inner_self_eq_norm_sq, hx]
  let b (z : ℂ) := ‖1 - z‖ / ‖z‖
  have hb (i : Σ i, Fin (m i)) : Tendsto (fun c ↦ b (p i c)) (𝓝 0) (𝓝 (b (w i.1))) := by
    have hn : w i.1 ≠ 0 := fun he ↦ by have := hr i.1; simp [he] at this; linarith
    exact ((tendsto_const_nhds.sub (hp i)).norm.div (hp i).norm (norm_ne_zero_iff.mpr hn))
  have hl := (tendsto_finsetProd Finset.univ fun i _ ↦ hb i).pow 2
  have hl' := (tendsto_const_nhds (x := (1 : ℝ))).sub hl
  have herr : Tendsto (fun c : ℂ ↦ ‖hh.toLp h - (hu.toLp u - c • hh.toLp h)‖ ^ 2)
      (𝓝 0) (𝓝 (‖hh.toLp h - hu.toLp u‖ ^ 2)) := by
    simpa using (show Continuous (fun c : ℂ ↦ ‖hh.toLp h - (hu.toLp u - c • hh.toLp h)‖ ^ 2) by fun_prop).continuousAt (x := 0) |>.tendsto
  have hpos : ∀ᶠ c in 𝓝 (0 : ℂ), ∀ i, 1 / 2 < (p i c).re :=
    Filter.eventually_all.mpr fun i ↦ ((Complex.continuous_re.tendsto _).comp (hp i)).eventually (lt_mem_nhds (hr i.1))
  have hle : ∀ᶠ c in 𝓝[≠] (0 : ℂ), 1 - (∏ i, b (p i c)) ^ 2 ≤
      ‖hh.toLp h - (hu.toLp u - c • hh.toLp h)‖ ^ 2 := by
    filter_upwards [hpc, hpos.filter_mono nhdsWithin_le_nhds] with c hc hcp
    let e : (Σ i, Fin (m i)) ↪ ℂ := ⟨fun i ↦ p i c, hc.1⟩
    let S := Finset.univ.map e
    let v := u - c • h
    have hv : MemLp v 2 μ := hu.sub (hh.const_smul c)
    have hSr (z : ℂ) (hz : z ∈ S) : 1 / 2 < z.re := by
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
      exact hcp i
    have hSm (z : ℂ) (hz : z ∈ S) : (∫ x in Iic (0 : ℝ), v x * Complex.exp ((z - 1 / 2) * x)) = 0 := by
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
      let z := p i c
      have hrz : 0 < z.re := by linarith [hcp i]
      have hn : z ≠ 0 := fun h ↦ by simp [h] at hrz
      have he (x : ℝ) : v x * Complex.exp ((z - 1 / 2) * x) =
          u x * Complex.exp ((z - 1 / 2) * x) - c * Complex.exp (z * x) := by
        change (u x - c * Complex.exp ((x : ℂ) / 2)) * _ = _
        rw [sub_mul, mul_assoc, ← Complex.exp_add]
        congr 3
        ring
      change (∫ x in Iic (0 : ℝ), v x * Complex.exp ((z - 1 / 2) * x)) = 0
      simp only [he]
      rw [integral_sub (hI z (hcp i)) ((integrableOn_exp_mul_complex_Iic hrz 0).const_mul c),
        integral_const_mul, integral_exp_mul_complex_Iic hrz 0]
      have ha := (hc.2 i).symm.trans (hZ z (hcp i))
      change c = z * _ at ha
      rw [ha]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_div]
      field_simp
      simp
    have hbound := thetaKernel_halfLine_distance S v hv hSr hSm
    change _ ≤ ∫ x, ‖(h - v) x‖ ^ 2 ∂μ at hbound
    rw [hnorm (h - v) (hh.sub hv), MemLp.toLp_sub hh hv] at hbound
    have hvL : hv.toLp v = hu.toLp u - c • hh.toLp h := rfl
    rw [hvL] at hbound
    simpa only [S, Finset.prod_map, Function.Embedding.coeFn_mk, e, b] using hbound
  have hlim := le_of_tendsto_of_tendsto_of_frequently (hl'.mono_left nhdsWithin_le_nhds)
    (herr.mono_left nhdsWithin_le_nhds) hle.frequently
  change _ ≤ ∫ x, ‖(h - u) x‖ ^ 2 ∂μ
  rw [hnorm (h - u) (hh.sub hu), MemLp.toLp_sub hh hu]
  simpa only [Fintype.prod_sigma, Finset.prod_const, Finset.card_univ, Fintype.card_fin, b] using hlim

/-- For any finite set of distinct right-hand completed Hecke zeros, the squared half-line
error of a supported polar-free lift from the centered indicator is at least one minus the
product of their squared Blaschke factors at one. -/
theorem centeredLogThetaLift_finite_zero_distance (χ : PontryaginDual C𝔽)
    (σ : ℝ≥0ˣ →ₜ* I𝔽) (hσ : RightInverse σ (ideleNorm F)) (f : adelePolarSubspace F)
    (ho : ∀ x : ℝ, 0 < x → centeredLogThetaLift χ σ f x = 0)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, 1 / 2 < ρ.re ∧
      0 < meromorphicOrderAt (continuedCompletedHeckeL χ) ρ) :
    1 - (∏ ρ ∈ S, (‖1 - ρ‖ / ‖ρ‖)) ^ 2 ≤
      hiddenThetaCost 0 0 0 (fun x ↦ Complex.exp ((x : ℂ) / 2) - centeredLogThetaLift χ σ f x) ^ 2 := by
  let u := centeredLogThetaLift χ σ f
  obtain ⟨hc, hi⟩ := centeredLogThetaLift_energy χ σ hσ f (α := 0) (s := 0) le_rfl le_rfl 0
  have hw (x : ℝ) : intervalSobolevDensity 0 0 0 x = 1 := by simp [intervalSobolevDensity]
  have hu : MemLp u 2 (volume.restrict (Iic (0 : ℝ))) :=
    (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
      (by simpa only [IntegrableOn, u, neg_zero, hw, mul_one] using hi)
  have hm (ρ : ℂ) (hρ : ρ ∈ S) : (∫ x in Iic (0 : ℝ), u x * Complex.exp ((ρ - 1 / 2) * x)) = 0 := by
    obtain ⟨_, hz⟩ := centeredLogThetaLift_zero_moment χ σ hσ f (z := ρ - 1 / 2)
      (by simpa only [sub_add_cancel] using (hS ρ hρ).2)
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro x hx; dsimp only [u]; rw [ho x (lt_of_not_ge hx), zero_mul])]
    exact hz
  simpa only [hiddenThetaCost, neg_zero, hw, mul_one, Real.sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _))]
    using thetaKernel_halfLine_distance S u hu (fun ρ hρ ↦ (hS ρ hρ).1) hm

/-- A supported polar-free lift obeys the finite Blaschke bound with multiplicity.
Each exponent may be any positive integer up to the completed Hecke zero order. -/
theorem centeredLogThetaLift_finite_zero_distance_with_multiplicity (χ : PontryaginDual C𝔽)
    (σ : ℝ≥0ˣ →ₜ* I𝔽) (hσ : RightInverse σ (ideleNorm F)) (f : adelePolarSubspace F)
    (hsupp : ∀ x : ℝ, 0 < x → centeredLogThetaLift χ σ f x = 0)
    (S : Finset ℂ) (m : ℂ → ℕ) (hS : ∀ ρ ∈ S, 1 / 2 < ρ.re ∧ 0 < m ρ ∧
      (m ρ : WithTop ℤ) ≤ meromorphicOrderAt (continuedCompletedHeckeL χ) ρ) :
    1 - (∏ ρ ∈ S, (‖1 - ρ‖ / ‖ρ‖) ^ m ρ) ^ 2 ≤
      hiddenThetaCost 0 0 0 (fun x ↦ Complex.exp ((x : ℂ) / 2) - centeredLogThetaLift χ σ f x) ^ 2 := by
  let u := centeredLogThetaLift χ σ f
  obtain ⟨hc, hi⟩ := centeredLogThetaLift_energy χ σ hσ f (α := 0) (s := 0) le_rfl le_rfl 0
  have hw (x : ℝ) : intervalSobolevDensity 0 0 0 x = 1 := by simp [intervalSobolevDensity]
  have hu : MemLp u 2 (volume.restrict (Iic (0 : ℝ))) :=
    (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
      (by simpa only [IntegrableOn, u, neg_zero, hw, mul_one] using hi)
  let Z (s : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ s)
  let G (s : ℂ) := s * Z s
  obtain ⟨hf, hF⟩ := (mem_adelePolarSubspace _).mp f.property
  have hZa (s : ℂ) : AnalyticAt ℂ Z s :=
    (globalThetaMellinIntegral_entire_of_vanishing f.val hf hF χ).analyticAt s
  have hGa (s : ℂ) : AnalyticAt ℂ G s := analyticAt_id.fun_mul (hZa s)
  have hord (i : S) : (m i : ℕ∞) ≤ analyticOrderAt G i := by
    have hn : (i : ℂ) ≠ 0 := by
      intro h
      have hr := (hS i i.property).1
      simp [h] at hr
      linarith
    have hG : meromorphicOrderAt G i = meromorphicOrderAt Z i :=
      meromorphicOrderAt_mul_of_ne_zero (g := id) analyticAt_id hn
    have hbound : (m i : WithTop ℤ) ≤ meromorphicOrderAt G i :=
      (hS i i.property).2.2.trans (((le_max_right _ _).trans
        ((isLeast_globalThetaMellinIntegral_orders χ i).2 ⟨f, rfl⟩)).trans_eq hG.symm)
    rw [(hGa i).meromorphicOrderAt_eq] at hbound
    cases h : analyticOrderAt G i with
    | top => simp
    | coe k =>
      change (m i : WithTop ℤ) ≤ (analyticOrderAt G i).map (fun n : ℕ ↦ (n : ℤ)) at hbound
      simpa [h] using hbound
  have ht (z : ℂ) :
      Integrable (fun x : ℝ ↦ u x * Complex.exp ((z - 1 / 2) * x)) ∧
        (∫ x in Iic (0 : ℝ), u x * Complex.exp ((z - 1 / 2) * x)) = Z z := by
    obtain ⟨hit, hzt⟩ := centeredLogThetaLift_mellin_moment χ σ hσ f (z - 1 / 2)
    refine ⟨hit, ?_⟩
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro x hx; dsimp only [u]; rw [hsupp x (lt_of_not_ge hx), zero_mul])]
    change (∫ x : ℝ, u x * Complex.exp ((z - 1 / 2) * x)) =
      globalThetaMellinIntegral f.val (ideleClassNormTwist χ ((z - 1 / 2) + 1 / 2)) at hzt
    simpa only [sub_add_cancel, Z] using hzt
  have h := thetaKernel_multiple_distance (fun i : S ↦ (i : ℂ)) Subtype.val_injective
    (fun i ↦ (hS i i.property).1) (fun i ↦ m i.val) (fun i ↦ (hS i i.property).2.1)
    u hu G (fun s _ ↦ hGa s) hord (fun z _ ↦ (ht z).1.integrableOn)
    (fun z _ ↦ congrArg (z * ·) (ht z).2.symm)
  rw [Finset.prod_coe_sort S (fun ρ ↦ (‖1 - ρ‖ / ‖ρ‖) ^ m ρ)] at h
  simpa only [hiddenThetaCost, neg_zero, hw, mul_one,
    Real.sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _)), u] using h

/-- A single polar-free lift of half-line error less than one bounds the sum of normalized
real-part displacements over all distinct completed Hecke zeros to the right of the line. -/
theorem centeredLogThetaLift_right_zero_sum (χ : PontryaginDual C𝔽)
    (σ : ℝ≥0ˣ →ₜ* I𝔽) (hσ : RightInverse σ (ideleNorm F)) (f : adelePolarSubspace F)
    (ho : ∀ x : ℝ, 0 < x → centeredLogThetaLift χ σ f x = 0)
    (he : hiddenThetaCost 0 0 0 (fun x ↦ Complex.exp ((x : ℂ) / 2) - centeredLogThetaLift χ σ f x) ^ 2 < 1) :
    let Z := {ρ : ℂ // 1 / 2 < ρ.re ∧ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) ρ}
    let d (ρ : Z) := (2 * ρ.val.re - 1) / ‖ρ.val‖ ^ 2
    Summable d ∧ ∑' ρ : Z, d ρ ≤ - Real.log (1 -
      hiddenThetaCost 0 0 0 (fun x ↦ Complex.exp ((x : ℂ) / 2) - centeredLogThetaLift χ σ f x) ^ 2) := by
  intro Z d
  let e := hiddenThetaCost 0 0 0 (fun x ↦ Complex.exp ((x : ℂ) / 2) - centeredLogThetaLift χ σ f x) ^ 2
  have hfin (T : Finset Z) : ∑ ρ ∈ T, d ρ ≤ - Real.log (1 - e) := by
    let S := T.map (Function.Embedding.subtype _)
    have hS (w : ℂ) (hw : w ∈ S) : 1 / 2 < w.re ∧ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) w := by
      obtain ⟨ρ, _, rfl⟩ := Finset.mem_map.mp hw
      exact ρ.property
    have h := thetaKernel_sum_defects_le S e he (fun w hw ↦ (hS w hw).1)
      (centeredLogThetaLift_finite_zero_distance χ σ hσ f ho S hS)
    simpa [S, d] using h
  have hd (ρ : Z) : 0 ≤ d ρ := div_nonneg (by linarith [ρ.property.1]) (sq_nonneg _)
  exact ⟨summable_of_sum_le hd hfin, (summable_of_sum_le hd hfin).tsum_le_of_sum_le hfin⟩

private theorem thetaKernel_sum_multiplicities_le (S : Finset ℂ) (m : ℂ → ℕ) (e : ℝ) (he : e < 1)
    (hS : ∀ w ∈ S, 1 / 2 < w.re ∧ 0 < m w)
    (h : 1 - (∏ w ∈ S, (‖1 - w‖ / ‖w‖) ^ m w) ^ 2 ≤ e) :
    ∑ w ∈ S, (m w : ℝ) * ((2 * w.re - 1) / ‖w‖ ^ 2) ≤ - Real.log (1 - e) := by
  let b (w : ℂ) := (‖1 - w‖ / ‖w‖) ^ 2
  have hr (w : ℂ) : ((‖1 - w‖ / ‖w‖) ^ m w) ^ 2 = b w ^ m w := by
    change ((‖1 - w‖ / ‖w‖) ^ m w) ^ 2 = ((‖1 - w‖ / ‖w‖) ^ 2) ^ m w
    rw [← pow_mul, Nat.mul_comm, pow_mul]
  have hp : 1 - e ≤ ∏ w ∈ S, b w ^ m w := by
    have h' : 1 - e ≤ (∏ w ∈ S, (‖1 - w‖ / ‖w‖) ^ m w) ^ 2 := by linarith
    rwa [← Finset.prod_pow, show (fun w : ℂ ↦ ((‖1 - w‖ / ‖w‖) ^ m w) ^ 2) = _ from funext hr] at h'
  have hpos := (sub_pos.mpr he).trans_le hp
  have hb (w : ℂ) (hw : w ∈ S) : 0 < b w := by
    refine (sq_nonneg _).lt_of_ne' ?_
    intro heq
    change b w = 0 at heq
    have hz := Finset.prod_ne_zero_iff.mp hpos.ne' w hw
    exact hz (by rw [heq, zero_pow (hS w hw).2.ne'])
  have hlog := Real.log_le_log (sub_pos.mpr he) hp
  rw [Real.log_prod (fun w hw ↦ pow_ne_zero _ (hb w hw).ne')] at hlog
  simp only [Real.log_pow] at hlog
  have hsum : ∑ w ∈ S, (m w : ℝ) * ((2 * w.re - 1) / ‖w‖ ^ 2) ≤
      ∑ w ∈ S, -((m w : ℝ) * Real.log (b w)) := by
    apply Finset.sum_le_sum
    intro w hw
    rw [← thetaKernel_factor_defect w (hS w hw).1, ← mul_neg]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    change 1 - b w ≤ -Real.log (b w)
    linarith [Real.log_le_sub_one_of_pos (hb w hw)]
  rw [Finset.sum_neg_distrib] at hsum
  linarith

/-- If one supported polar-free lift has squared error below one, the normalized
displacements of right-hand completed Hecke zeros are summable with their orders.
Their total is at most the negative logarithm of one minus the squared error. -/
theorem centeredLogThetaLift_right_zero_sum_with_multiplicity (χ : PontryaginDual C𝔽)
    (σ : ℝ≥0ˣ →ₜ* I𝔽) (hσ : RightInverse σ (ideleNorm F)) (f : adelePolarSubspace F)
    (ho : ∀ x : ℝ, 0 < x → centeredLogThetaLift χ σ f x = 0)
    (he : hiddenThetaCost 0 0 0 (fun x ↦ Complex.exp ((x : ℂ) / 2) - centeredLogThetaLift χ σ f x) ^ 2 < 1) :
    let Z := {ρ : ℂ // 1 / 2 < ρ.re ∧ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) ρ}
    let m (ρ : Z) := (meromorphicOrderAt (continuedCompletedHeckeL χ) ρ.val).untop₀.toNat
    let d (ρ : Z) := (m ρ : ℝ) * ((2 * ρ.val.re - 1) / ‖ρ.val‖ ^ 2)
    Summable d ∧ ∑' ρ : Z, d ρ ≤ - Real.log (1 -
      hiddenThetaCost 0 0 0 (fun x ↦ Complex.exp ((x : ℂ) / 2) - centeredLogThetaLift χ σ f x) ^ 2) := by
  intro Z m d
  let e := hiddenThetaCost 0 0 0 (fun x ↦ Complex.exp ((x : ℂ) / 2) - centeredLogThetaLift χ σ f x) ^ 2
  let L := continuedCompletedHeckeL χ
  let n (w : ℂ) := (meromorphicOrderAt L w).untop₀.toNat
  have hmult (ρ : Z) : 0 < n ρ.val ∧ (n ρ.val : WithTop ℤ) = meromorphicOrderAt L ρ.val := by
    have hfinite : meromorphicOrderAt L ρ.val ≠ ⊤ := by
      apply (continuedCompletedHeckeL_spec χ).1.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
        isPreconnected_univ (x := 2) (mem_univ _) (mem_univ _)
      intro ht
      have hp : 0 < meromorphicOrderAt L 2 := ht ▸ WithTop.coe_lt_top (0 : ℤ)
      have hbad := completedHeckeL_continuation_zeros χ L (continuedCompletedHeckeL_spec χ).1
        (continuedCompletedHeckeL_spec χ).2 (by norm_num : 0 < (2 : ℂ).re) hp
      norm_num at hbad
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfinite
    have hk' : (0 : ℤ) < k := by exact_mod_cast (ρ.property.2.trans_eq hk.symm)
    simp only [n, ← hk, WithTop.untop₀_coe]
    exact ⟨by omega, by exact_mod_cast Int.toNat_of_nonneg hk'.le⟩
  have hfin (T : Finset Z) : ∑ ρ ∈ T, d ρ ≤ -Real.log (1 - e) := by
    let S := T.map (Function.Embedding.subtype _)
    have hs (w : ℂ) (hw : w ∈ S) : 1 / 2 < w.re ∧ 0 < n w ∧
        (n w : WithTop ℤ) ≤ meromorphicOrderAt L w := by
      obtain ⟨ρ, _, rfl⟩ := Finset.mem_map.mp hw
      exact ⟨ρ.property.1, (hmult ρ).1, (hmult ρ).2.le⟩
    have h := thetaKernel_sum_multiplicities_le S n e he (fun w hw ↦ ⟨(hs w hw).1, (hs w hw).2.1⟩)
      (centeredLogThetaLift_finite_zero_distance_with_multiplicity χ σ hσ f ho S n hs)
    simpa [S, d, m, n, L] using h
  have hd (ρ : Z) : 0 ≤ d ρ := mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by linarith [ρ.property.1]) (sq_nonneg _))
  exact ⟨summable_of_sum_le hd hfin, (summable_of_sum_le hd hfin).tsum_le_of_sum_le hfin⟩

/-- At a completed Hecke zero ρ to the right of the central line, a polar-free theta lift
supported in nonpositive log norm has L² distance at least
sqrt(2 Re ρ − 1) / |ρ| from the normalized unit-interval indicator. -/
theorem centeredLogThetaLift_halfLine_distance (χ : PontryaginDual C𝔽)
    (σ : ℝ≥0ˣ →ₜ* I𝔽) (hσ : RightInverse σ (ideleNorm F)) (f : adelePolarSubspace F)
    (ho : ∀ x : ℝ, 0 < x → centeredLogThetaLift χ σ f x = 0)
    (ρ : ℂ) (hr : 1 / 2 < ρ.re) (hz : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) ρ) :
    Real.sqrt (2 * (ρ.re - 1 / 2)) / ‖ρ‖ ≤
      hiddenThetaCost 0 0 0 (fun x ↦ Complex.exp ((x : ℂ) / 2) - centeredLogThetaLift χ σ f x) := by
  have h := centeredLogThetaLift_finite_zero_distance χ σ hσ f ho {ρ}
    (by intro w hw; simpa only [Finset.mem_singleton.mp hw] using And.intro hr hz)
  rw [Finset.prod_singleton, thetaKernel_factor_defect ρ hr] at h
  have he : 0 ≤ hiddenThetaCost 0 0 0 (fun x ↦ Complex.exp ((x : ℂ) / 2) - centeredLogThetaLift χ σ f x) :=
    Real.sqrt_nonneg _
  have hpos : 0 ≤ 2 * ρ.re - 1 := by linarith
  have hs := Real.sqrt_le_sqrt h
  rw [Real.sqrt_div hpos, Real.sqrt_sq (norm_nonneg ρ), Real.sqrt_sq he] at hs
  simpa only [show 2 * (ρ.re - 1 / 2) = 2 * ρ.re - 1 by ring] using hs

/-- Approximating the normalized unit-interval indicator arbitrarily closely by polar-free
theta lifts supported in nonpositive log norm suffices for exterior cancellation. There
is one approximation problem for each character trivial on the chosen norm section. -/
theorem exteriorCancellation_of_halfLine_approximation (σ : ℝ≥0ˣ →ₜ* I𝔽)
    (hσ : RightInverse σ (ideleNorm F)) (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (happrox : ∀ (χ : PontryaginDual C𝔽), (∀ t, χ (τ t) = 1) →
      ∀ ε : ℝ, 0 < ε → ∃ f : adelePolarSubspace F,
        (∀ x : ℝ, 0 < x → centeredLogThetaLift χ σ f x = 0) ∧
        hiddenThetaCost 0 0 0 (fun x ↦ Complex.exp ((x : ℂ) / 2) - centeredLogThetaLift χ σ f x) < ε)
    (φ : BruhatCompactSupport C𝔽) {a : ℝ} (ha : 0 < a) :
    HasSum (fun z : extZeros(F, τ, a) ↦
      ((order(z.val.1.val, z.val.2) : ℤ) : ℂ) *
        modulatedFourierMellin m𝔽 univ hm𝔽 (ideleClassTamagawaMeasure F) φ.val
          (ideleClassNormTwist z.val.1.val (z.val.2 - 1 / 2))) 0 := by
  have := exteriorZeros_empty_of_normalized_right_bound τ ha (by
    intro χ hχ ρ hρ
    apply le_of_not_gt
    intro hz
    have hρ' : ρ ≠ 0 := fun h ↦ by simp [h] at hρ; linarith
    have hε : 0 < Real.sqrt (2 * (ρ.re - 1 / 2)) / ‖ρ‖ :=
      div_pos (Real.sqrt_pos.mpr (by linarith)) (norm_pos_iff.mpr hρ')
    obtain ⟨f, ho, hdist⟩ := happrox χ hχ _ hε
    exact hdist.not_ge (centeredLogThetaLift_halfLine_distance χ σ hσ f ho ρ hρ hz))
  exact hasSum_empty


private theorem widthLift_profile (χ : PontryaginDual C𝔽)
    (hχ : ∀ t, χ (QuotientGroup.mk (canonicalIdeleNormSection F t)) = 1)
    (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F)) (R : ℝ) (g : ℝ → ℂ)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ (⊤ : ENat) g) :
    ∃ f : adelePolarSubspace F, EqOn (centeredLogThetaLift χ τ f) g (Ici (-R)) := by
  let e := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let h (x : ℝ) := g x * Complex.exp (-(x : ℂ) / 2)
  have hr : ContDiff ℝ (⊤ : ENat) (fun t : ℝ ↦ (t : ℂ)) := Complex.ofRealCLM.contDiff
  have hh : ContDiff ℝ (⊤ : ENat) h := hg.mul (by fun_prop)
  obtain ⟨f, hf⟩ := exists_homogeneousAdelicTheta_eq_profile_on_halfLine χ (Real.exp_pos (-R)) h
    (show HasCompactSupport h from hc.mul_right) hh
  refine ⟨f, fun x hx ↦ ?_⟩
  let y : C𝔽 := QuotientGroup.mk (τ (e x))
  have hy : ideleClassNorm F y = e x := hτ (e x)
  have hlog : Real.log ((ideleClassNorm F y).val : ℝ) = x := by rw [hy]; exact Real.log_exp x
  have hval := hf y (show Real.exp (-R) ≤ ((ideleClassNorm F y).val : ℝ) by
    rw [hy]; exact Real.exp_le_exp.mpr hx)
  change homogeneousAdelicTheta _ f.val y * (χ y : ℂ) * Complex.exp ((x : ℂ) / 2) = g x
  rw [hval, hχ, Circle.coe_one, mul_one, hlog]
  dsimp only [h]
  have hne : (χ y : ℂ) ≠ 0 := Circle.coe_ne_zero _
  rw [show -(x : ℂ) / 2 = -((x : ℂ) / 2) by ring, Complex.exp_neg]
  field_simp


private theorem widthEnergy_weight {a : ℝ} (ha : 0 ≤ a) (s x : ℝ) :
    intervalSobolevDensity (-a) a s x =
      Real.exp (2 * a * |x|) * (1 + x ^ 2) ^ (s / 2) := by
  unfold intervalSobolevDensity
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, max_eq_right (Real.exp_le_exp.mpr (by nlinarith))]
  · rw [abs_of_nonpos hx, max_eq_left (Real.exp_le_exp.mpr (by nlinarith)),
      show 2 * -a * x = 2 * a * -x by ring]


private theorem widthEnergy_integrable_of_profile (χ : PontryaginDual C𝔽)
    (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F)) (f : adelePolarSubspace F)
    {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (R : ℝ) {g : ℝ → ℂ}
    (hc : HasCompactSupport g) (hg : Continuous g)
    (heq : EqOn (centeredLogThetaLift χ τ f) g (Ici (-R))) :
    Integrable (fun x ↦ ‖centeredLogThetaLift χ τ f x‖ ^ 2 * intervalSobolevDensity (-a) a s x) := by
  have hi : IntegrableOn (fun x ↦ ‖centeredLogThetaLift χ τ f x‖ ^ 2 * intervalSobolevDensity (-a) a s x) (Iic (-R)) :=
    (centeredLogThetaLift_energy χ τ hτ f ha hs R).2
  have hd : Continuous (intervalSobolevDensity (-a) a s) := by
    unfold intervalSobolevDensity; fun_prop (disch := intros; positivity)
  have hp : HasCompactSupport (fun x ↦ ‖g x‖ ^ 2 * intervalSobolevDensity (-a) a s x) :=
    by simpa only [pow_two, Pi.mul_def] using (hc.norm.mul_right (f' := fun x ↦ ‖g x‖)).mul_right (f' := intervalSobolevDensity (-a) a s)
  have hir : IntegrableOn (fun x ↦ ‖g x‖ ^ 2 * intervalSobolevDensity (-a) a s x) (Ici (-R)) :=
    (((hg.norm.pow 2).mul hd).integrable_of_hasCompactSupport hp).integrableOn
  have hr : IntegrableOn (fun x ↦ ‖centeredLogThetaLift χ τ f x‖ ^ 2 * intervalSobolevDensity (-a) a s x) (Ici (-R)) := by
    apply IntegrableOn.congr_fun hir _ measurableSet_Ici
    intro x hx
    dsimp only
    rw [heq hx]
  simpa only [Iic_union_Ici, integrableOn_univ] using hi.union hr


private theorem widthEnergy_one_le {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (x : ℝ) :
    1 ≤ intervalSobolevDensity (-a) a s x := by
  rw [widthEnergy_weight ha]
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity)) (Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by positivity))


private theorem widthEnergy_tail {a b s R : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {x : ℝ} (hx : R ≤ |x|) :
    Real.exp (2 * (b - a) * R) * intervalSobolevDensity (-a) a s x ≤ intervalSobolevDensity (-b) b s x := by
  rw [widthEnergy_weight ha, widthEnergy_weight (ha.trans hab.le), ← mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hab.le) (sub_nonneg.mpr hx)])


private theorem widthEnergy_amplify {u g : ℝ → ℂ} {a b s R C : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hab : a < b) (hC : 0 ≤ C)
    (hi : ∀ c ∈ ({a,b} : Finset ℝ), Integrable (fun x ↦ ‖u x‖ ^ 2 * intervalSobolevDensity (-c) c s x))
    (hgi : Integrable (fun x ↦ ‖g x‖ ^ 2 * intervalSobolevDensity (-a) a s x))
    (he : EqOn u g (Icc (-R) R)) (hunit : ∀ x ∈ Icc (R + 3) (R + 4), u x = 1)
    (hsize : C * ((∫ x, ‖g x‖ ^ 2 * intervalSobolevDensity (-a) a s x) + 1) <
      Real.exp (2 * (b - a) * R)) :
    0 < ∫ x, ‖u x‖ ^ 2 * intervalSobolevDensity (-a) a s x
    ∧ C * (∫ x, ‖u x‖ ^ 2 * intervalSobolevDensity (-a) a s x) <
      ∫ x, ‖u x‖ ^ 2 * intervalSobolevDensity (-b) b s x := by
  let e (c x : ℝ) := ‖u x‖ ^ 2 * intervalSobolevDensity (-c) c s x
  let W := Icc (-R) R
  let D := Real.exp (2 * (b - a) * R)
  let A := ∫ x, ‖g x‖ ^ 2 * intervalSobolevDensity (-a) a s x
  have hA : 0 ≤ A := integral_nonneg (fun x ↦ mul_nonneg (sq_nonneg _) (zero_le_one.trans (widthEnergy_one_le ha hs x)))
  have hia : Integrable (e a) := hi a (by simp)
  have hib : Integrable (e b) := hi b (by simp)
  have hW : MeasurableSet W := measurableSet_Icc
  have hnn {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : 0 ≤ e c x :=
    mul_nonneg (sq_nonneg _) (zero_le_one.trans (widthEnergy_one_le hc hs x))
  have hinside : (∫ x in W, e a x) ≤ A := by
    calc
      _ = ∫ x in W, ‖g x‖ ^ 2 * intervalSobolevDensity (-a) a s x :=
        setIntegral_congr_fun hW (fun x hx ↦ by simp only [e, he hx])
      _ ≤ A := setIntegral_le_integral hgi (ae_of_all _ (fun x ↦ mul_nonneg (sq_nonneg _) (zero_le_one.trans (widthEnergy_one_le ha hs x))))
  have hmass : 1 ≤ ∫ x in Wᶜ, e a x := by
    let I := Icc (R + 3) (R + 4)
    have hI : I ⊆ Wᶜ := by
      intro x hx hWx; exact (show R < x by linarith [hx.1]).not_ge hWx.2
    calc
      1 = ∫ _ : ℝ in I, (1 : ℝ) := by
        simp [I, Measure.real, Real.volume_Icc, show R + 4 - (R + 3) = 1 by ring]
      _ ≤ ∫ x in I, e a x := by
        apply setIntegral_mono_on _ hia.integrableOn measurableSet_Icc
        · intro x hx
          simpa only [e, hunit x hx, norm_one, one_pow, one_mul] using widthEnergy_one_le ha hs x
        · exact integrableOn_const (by simp)
      _ ≤ _ := setIntegral_mono_set hia.integrableOn (ae_of_all _ (hnn ha)) (ae_of_all _ hI)
  have htail : D * (∫ x in Wᶜ, e a x) ≤ ∫ x in Wᶜ, e b x := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hia.const_mul _).integrableOn hib.integrableOn hW.compl
    intro x hx
    have hxr : R ≤ |x| := by
      by_contra! h
      exact hx ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩
    simpa only [e, D, mul_left_comm] using
      (mul_le_mul_of_nonneg_left (widthEnergy_tail (s := s) ha hab hxr) (sq_nonneg ‖u x‖))
  have hsa := integral_add_compl hW hia
  have hsb := integral_add_compl hW hib
  have h0a : 0 ≤ ∫ x in W, e a x := integral_nonneg (hnn ha)
  have h0b : 0 ≤ ∫ x in W, e b x := integral_nonneg (hnn (ha.trans hab.le))
  change C * (A + 1) < D at hsize
  change 0 < ∫ x, e a x
    ∧ C * (∫ x, e a x) < ∫ x, e b x
  constructor
  · linarith
  · have hdc : 0 ≤ D - C := by nlinarith [mul_nonneg hC hA]
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hinside), mul_nonneg hdc (sub_nonneg.mpr hmass)]


/-- For a prescribed smooth compact profile on any bounded log window, the ratio of the
squared global norms at two distinct strip widths is unbounded over *actual* polar-free
theta lifts of that profile. The character is normalized on the canonical norm section.
The profile is centered at 1/2; the squared norms use the §9.2 densities with degree s. -/
theorem exists_centeredLogThetaLift_width_amplification (χ : PontryaginDual C𝔽)
    (hχ : ∀ t, χ (QuotientGroup.mk (canonicalIdeleNormSection F t)) = 1)
    (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F))
    {a b s : ℝ} (ha : 0 ≤ a) (hab : a < b) (hs : 0 ≤ s)
    (g : ℝ → ℂ) (hc : HasCompactSupport g) (hg : ContDiff ℝ (⊤ : ENat) g)
    (K C : ℝ) (hC : 0 ≤ C) :
    ∃ f : adelePolarSubspace F,
      let u := centeredLogThetaLift χ τ f
      EqOn u g (Icc (-K) K) ∧
      (∀ c, 0 ≤ c → Integrable (fun x ↦ ‖u x‖ ^ 2 * intervalSobolevDensity (-c) c s x)) ∧
      0 < (∫ x, ‖u x‖ ^ 2 * intervalSobolevDensity (-a) a s x) ∧
      C * (∫ x, ‖u x‖ ^ 2 * intervalSobolevDensity (-a) a s x) <
        ∫ x, ‖u x‖ ^ 2 * intervalSobolevDensity (-b) b s x := by
  let A := ∫ x, ‖g x‖ ^ 2 * intervalSobolevDensity (-a) a s x
  obtain ⟨B, hB, hBg⟩ := hc.isBounded.exists_pos_norm_lt
  obtain ⟨R, hR⟩ := exists_gt (max (max K B) (C * (A + 1) / (2 * (b - a))))
  have hK : K ≤ R := (le_max_left K B).trans ((le_max_left ..).trans hR.le)
  have hBR : B < R := lt_of_le_of_lt ((le_max_right K B).trans (le_max_left ..)) hR
  have hR₀ : 0 ≤ R := hB.le.trans hBR.le
  have hsize : C * (A + 1) < Real.exp (2 * (b - a) * R) := by
    have h := (div_lt_iff₀ (by linarith : 0 < 2 * (b - a))).mp
      (lt_of_le_of_lt (le_max_right ..) hR)
    linarith [Real.add_one_le_exp (2 * (b - a) * R)]
  let Bump : ContDiffBump (R + 3) := ⟨1, 2, by norm_num, by norm_num⟩
  let p (x : ℝ) := g x + ((Bump x : ℝ) : ℂ)
  have hp : ContDiff ℝ (⊤ : ENat) p := hg.add (Complex.ofRealCLM.contDiff.comp Bump.contDiff)
  have hpc : HasCompactSupport p := hc.add (Bump.hasCompactSupport.comp_left (by simp : ((0:ℝ):ℂ) = 0))
  obtain ⟨f, hf⟩ := widthLift_profile χ hχ τ hτ R p hpc hp
  let u := centeredLogThetaLift χ τ f
  have hwin : EqOn u g (Icc (-R) R) := by
    intro x hx
    have hzero : Bump x = 0 := Bump.zero_of_le_dist (by
      change 2 ≤ dist x (R + 3)
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hx.2] : x - (R + 3) ≤ 0)]; linarith [hx.2])
    simpa only [p, hzero, Complex.ofReal_zero, add_zero] using hf (show x ∈ Ici (-R) from hx.1)
  have hunit (x : ℝ) (hx : x ∈ Icc (R + 3) (R + 4)) : u x = 1 := by
    have hzero : g x = 0 := by
      by_contra hn
      have hb := hBg x (subset_tsupport g hn)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])] at hb
      linarith [hx.1]
    have hone : Bump x = 1 := Bump.one_of_mem_closedBall (by
      change dist x (R + 3) ≤ 1
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2])
    simpa only [p, hzero, hone, Complex.ofReal_one, zero_add] using hf (show x ∈ Ici (-R) by
      change -R ≤ x; linarith [hx.1])
  have hi (c : ℝ) (hc₀ : 0 ≤ c) : Integrable (fun x ↦ ‖u x‖ ^ 2 * intervalSobolevDensity (-c) c s x) :=
    widthEnergy_integrable_of_profile χ τ hτ f hc₀ hs R hpc hp.continuous hf
  have hgi : Integrable (fun x ↦ ‖g x‖ ^ 2 * intervalSobolevDensity (-a) a s x) := by
    have hd : Continuous (intervalSobolevDensity (-a) a s) := by
      unfold intervalSobolevDensity; fun_prop (disch := intros; positivity)
    apply ((hg.continuous.norm.pow 2).mul hd).integrable_of_hasCompactSupport
    simpa only [pow_two, Pi.mul_def] using
      (hc.norm.mul_right (f' := fun x ↦ ‖g x‖)).mul_right (f' := intervalSobolevDensity (-a) a s)
  refine ⟨f, hwin.mono (Icc_subset_Icc (neg_le_neg hK) hK), hi, ?_⟩
  apply widthEnergy_amplify ha hs hab hC _ hgi hwin hunit hsize
  intro c hc'
  rcases Finset.mem_insert.mp hc' with rfl | h
  · exact hi _ ha
  · obtain rfl := Finset.mem_singleton.mp h
    exact hi _ (ha.trans hab.le)


/-- Real localized convolution numerator of a radial vector on the log-norm line.
The Haar-coordinate trace of its rank-one compression is this numerator divided by
its squared global weighted norm, with the positive norm-one Haar factor. -/
def logWindowConvolutionNumerator (a s : ℝ) (ρ : ℝ → ℝ) (H u : ℝ → ℂ) : ℝ :=
  ∫ x, ρ x * intervalSobolevDensity (-a) a s x *
    ((∫ y, H (x - y) * u y) * conj (u x)).re

private theorem logWindowConvolutionNumerator_congr (a s : ℝ) {ρ : ℝ → ℝ} {H u g : ℝ → ℂ}
    {R T : ℝ} (hT : 0 ≤ T) (hρ : ∀ x, R < |x| → ρ x = 0) (hH : ∀ x, T < |x| → H x = 0)
    (hu : EqOn u g (Icc (-(R + T)) (R + T))) :
    logWindowConvolutionNumerator a s ρ H u = logWindowConvolutionNumerator a s ρ H g := by
  apply integral_congr_ae (ae_of_all _ _)
  intro x
  by_cases hx : |x| ≤ R
  · have hx' := abs_le.mp hx
    have heqx : u x = g x := hu ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
    have heqy : (∫ y, H (x - y) * u y) = ∫ y, H (x - y) * g y := by
      apply integral_congr_ae (ae_of_all _ _)
      intro y
      by_cases hy : |x - y| ≤ T
      · obtain ⟨hl, hr⟩ := abs_le.mp hy
        rw [hu (show y ∈ Icc (-(R + T)) (R + T) from ⟨by linarith [hx'.1], by linarith [hx'.2]⟩)]
      · rw [hH _ (lt_of_not_ge hy), zero_mul, zero_mul]
    simp only [heqx, heqy]
  · simp only [hρ _ (lt_of_not_ge hx), zero_mul]


/-- At two distinct widths the absolute value of the normalized localized convolution
trace can decrease by any prescribed factor on a genuine one-dimensional theta space.
The same lift realizes a given compact smooth profile throughout the padded window;
the hypothesis asks that its narrow-width numerator be nonzero. -/
theorem exists_centeredLogThetaLift_small_wide_window_trace (χ : PontryaginDual C𝔽)
    (hχ : ∀ t, χ (QuotientGroup.mk (canonicalIdeleNormSection F t)) = 1)
    (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F))
    {a b s : ℝ} (ha : 0 ≤ a) (hab : a < b) (hs : 0 ≤ s)
    (g : ℝ → ℂ) (hc : HasCompactSupport g) (hg : ContDiff ℝ (⊤ : ENat) g)
    (ρ : ℝ → ℝ) (H : ℝ → ℂ) {R T : ℝ} (hT : 0 ≤ T)
    (hρ : ∀ x, R < |x| → ρ x = 0) (hH : ∀ x, T < |x| → H x = 0)
    (hng : logWindowConvolutionNumerator a s ρ H g ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : adelePolarSubspace F,
      let u := centeredLogThetaLift χ τ f
      let E := fun c : ℝ ↦ ∫ x, ‖u x‖ ^ 2 * intervalSobolevDensity (-c) c s x
      EqOn u g (Icc (-(R + T)) (R + T)) ∧ 0 < E a ∧ 0 < E b ∧
      |logWindowConvolutionNumerator b s ρ H u| / E b <
        ε * (|logWindowConvolutionNumerator a s ρ H u| / E a) := by
  let N := fun c ↦ |logWindowConvolutionNumerator c s ρ H g|
  have haN : 0 < N a := abs_pos.mpr hng
  have hbN : 0 ≤ N b := abs_nonneg _
  let C := N b / (ε * N a)
  have hC : 0 ≤ C := div_nonneg hbN (mul_pos hε haN).le
  obtain ⟨f, heq, _, hea, hgrowth⟩ := exists_centeredLogThetaLift_width_amplification
    χ hχ τ hτ ha hab hs g hc hg (R + T) C hC
  let u := centeredLogThetaLift χ τ f
  let E := fun c : ℝ ↦ ∫ x, ‖u x‖ ^ 2 * intervalSobolevDensity (-c) c s x
  change 0 < E a at hea
  change C * E a < E b at hgrowth
  have heb := (mul_nonneg hC hea.le).trans_lt hgrowth
  refine ⟨f, heq, hea, heb, ?_⟩
  rw [logWindowConvolutionNumerator_congr b s hT hρ hH heq, logWindowConvolutionNumerator_congr a s hT hρ hH heq]
  change N b / E b < ε * (N a / E a)
  rw [← mul_div_assoc, div_lt_div_iff₀ heb hea]
  have hcoef : C * (ε * N a) = N b := div_mul_cancel₀ _ (mul_pos hε haN).ne'
  calc
    _ = (C * E a) * (ε * N a) := by rw [← hcoef]; ring
    _ < E b * (ε * N a) := mul_lt_mul_of_pos_right hgrowth (mul_pos hε haN)
    _ = _ := mul_comm _ _


private theorem widthWindow_bump {x : ℝ} {P : ℝ → Prop} (hp : ∀ᶠ y in 𝓝 x, P y) :
    ∃ b : ContDiffBump x, ∀ y, b y ≠ 0 → P y := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hp
  let b : ContDiffBump x := ⟨δ / 2, δ, by positivity, by linarith⟩
  refine ⟨b, fun y hy ↦ hball ?_⟩
  exact b.support_eq ▸ (show y ∈ Function.support b from hy)


/-- If a visible point interacts through a nonzero complex kernel with a point beyond
the physical cutoff, smooth compact radial trial vectors realize every real localized
convolution numerator. The phase of the exterior packet aligns the cross term. -/
theorem exists_logWindowConvolutionNumerator_eq_of_cutoff_gap {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s)
    {ρ : ℝ → ℝ} {H : ℝ → ℂ} (hρ : Continuous ρ) (hH : Continuous H) (hcH : HasCompactSupport H)
    {x₀ y₀ : ℝ} (hxy : H (x₀ - y₀) ≠ 0) (hx : 0 < ρ x₀)
    (hy : ∀ᶠ y in 𝓝 y₀, ρ y = 0) (v : ℝ) :
    ∃ g : ℝ → ℂ, ContDiff ℝ (⊤ : ENat) g ∧ HasCompactSupport g ∧
      logWindowConvolutionNumerator a s ρ H g = v := by
  let c := conj (H (x₀ - y₀))
  let A (x : ℝ) := (H x).re
  let B (x : ℝ) := (c * H x).re
  have hA : Continuous A := Complex.continuous_re.comp hH
  have hB : Continuous B := Complex.continuous_re.comp (continuous_const.mul hH)
  have hcA : HasCompactSupport A := hcH.comp_left Complex.zero_re
  have hcB : HasCompactSupport B := (hcH.mul_left (f := fun _ ↦ c)).comp_left Complex.zero_re
  have hbxy : 0 < B (x₀ - y₀) := by
    dsimp only [B, c]
    rw [Complex.conj_mul']
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    exact sq_pos_of_pos (norm_pos_iff.mpr hxy)
  have hcy : Continuous (fun y ↦ B (x₀ - y)) := hB.comp (continuous_const.sub continuous_id)
  obtain ⟨d, hd⟩ := widthWindow_bump (hy.and (hcy.continuousAt.eventually (lt_mem_nhds hbxy)))
  let conv (J k : ℝ → ℝ) (x : ℝ) := ∫ y, J (x - y) * k y
  have hconv {J k : ℝ → ℝ} (hJ : Continuous J) (hJc : HasCompactSupport J) (hk : Continuous k) :
      Continuous (conv J k) := by
    have heq : conv J k = MeasureTheory.convolution k J (ContinuousLinearMap.mul ℝ ℝ) volume := by
      funext x
      simp only [conv, MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply', mul_comm]
    rw [heq]
    exact hJc.continuous_convolution_right _ hk.locallyIntegrable hJ
  have hcd : 0 < conv B d x₀ := by
    apply (hcy.mul d.continuous).integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := y₀) d.hasCompactSupport.mul_left
    · intro y
      by_cases h : d y = 0
      · simp [h]
      · exact mul_nonneg (hd y h).2.le d.nonneg
    · simpa only [Pi.mul_apply, d.one_of_mem_closedBall (Metric.mem_closedBall_self d.rIn_pos.le), mul_one] using hbxy.ne'
  obtain ⟨b, hb⟩ := widthWindow_bump ((hρ.continuousAt.eventually (lt_mem_nhds hx)).and
    ((hconv hB hcB d.continuous).continuousAt.eventually (lt_mem_nhds hcd)))
  let w (x : ℝ) := ρ x * intervalSobolevDensity (-a) a s x
  have hw : Continuous w := hρ.mul (by
    unfold intervalSobolevDensity; fun_prop (disch := intros; positivity))
  let P (J k : ℝ → ℝ) := ∫ x, w x * b x * conv J k x
  have hPint {J k : ℝ → ℝ} (hJ : Continuous J) (hJc : HasCompactSupport J) (hk : Continuous k) :
      Integrable (fun x ↦ w x * b x * conv J k x) :=
    ((hw.mul b.continuous).mul (hconv hJ hJc hk)).integrable_of_hasCompactSupport
      (b.hasCompactSupport.mul_left.mul_right)
  have hP : 0 < P B d := by
    apply integral_pos_of_integrable_nonneg_ne_zero (x := x₀)
      ((hw.mul b.continuous).mul (hconv hB hcB d.continuous)) (hPint hB hcB d.continuous)
    · intro x
      by_cases h : b x = 0
      · simp [h]
      · exact mul_nonneg (mul_nonneg (mul_nonneg (hb x h).1.le (zero_le_one.trans (widthEnergy_one_le ha hs x))) b.nonneg) (hb x h).2.le
    · have hone := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
      exact (mul_pos (mul_pos (mul_pos hx (zero_lt_one.trans_le (widthEnergy_one_le ha hs x₀))) (hone.symm ▸ zero_lt_one)) hcd).ne'
  let t := (v - P A b) / P B d
  let g (x : ℝ) : ℂ := (b x : ℝ) + ((t : ℂ) * c) * (d x : ℝ)
  have hg : ContDiff ℝ (⊤ : ENat) g := (Complex.ofRealCLM.contDiff.comp b.contDiff).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp d.contDiff))
  have hgc : HasCompactSupport g := (b.hasCompactSupport.comp_left Complex.ofReal_zero).add
    (d.hasCompactSupport.comp_left Complex.ofReal_zero).mul_left
  refine ⟨g, hg, hgc, ?_⟩
  have hlint {J k : ℝ → ℝ} (hJ : Continuous J) (hk : Continuous k) (hkc : HasCompactSupport k) (x : ℝ) :
      Integrable (fun y ↦ J (x - y) * k y) :=
    ((hJ.comp (continuous_const.sub continuous_id)).mul hk).integrable_of_hasCompactSupport hkc.mul_left
  let U (x : ℝ) := ∫ y, H (x - y) * g y
  have hreal (x : ℝ) : (U x).re = conv A b x + t * conv B d x := by
    have hi : Integrable (fun y ↦ H (x - y) * g y) :=
      ((hH.comp (continuous_const.sub continuous_id)).mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
    have hcast : (U x).re = ∫ y, (H (x - y) * g y).re := (integral_re hi).symm
    rw [hcast]
    have heq (y : ℝ) : (H (x - y) * g y).re = A (x - y) * b y + t * (B (x - y) * d y) := by
      dsimp only [g, A, B]
      simp only [mul_add, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    simp_rw [heq]
    rw [integral_add (hlint hA b.continuous b.hasCompactSupport x)
      ((hlint hB d.continuous d.hasCompactSupport x).const_mul t), integral_const_mul]
  calc
    _ = ∫ x, w x * b x * conv A b x + t * (w x * b x * conv B d x) := by
      apply integral_congr_ae (ae_of_all _ _)
      intro x
      change w x * (U x * conj (g x)).re = _
      by_cases hx : ρ x = 0
      · simp [w, hx]
      have hd₀ : d x = 0 := by
        by_contra h
        exact hx (hd x h).1
      rw [show conj (g x) = ((b x : ℝ) : ℂ) by simp [g, hd₀], Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hreal]
      ring
    _ = P A b + t * P B d := by
      rw [integral_add (hPint hA hcA b.continuous) ((hPint hB hcB d.continuous).const_mul t), integral_const_mul]
    _ = v := by dsimp [t]; field_simp; ring


private theorem widthWindow_cutoff_gap {ρ H : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : 0 ≤ ρ) (hn : ∃ x, ρ x ≠ 0) {t : ℝ} (ht : 0 < t) (hH : 0 < H (-t)) :
    ∃ x y, 0 < H (x - y) ∧ 0 < ρ x ∧ ∀ᶠ z in 𝓝 y, ρ z = 0 := by
  let S := Function.support ρ
  have hS : S.Nonempty := hn
  have hB : BddAbove S := hc.bddAbove.mono (subset_tsupport ρ)
  obtain ⟨x, hx, hx'⟩ := exists_lt_of_lt_csSup hS (show sSup S - t < sSup S by linarith)
  refine ⟨x, x + t, by simpa only [sub_add_cancel_left] using hH, lt_of_le_of_ne (hρ x) (Ne.symm hx), ?_⟩
  filter_upwards [lt_mem_nhds (show sSup S < x + t by linarith)] with z hz
  by_contra h
  exact (le_csSup hB (show z ∈ S from h)).not_gt hz


/-- Every nonnegative nonzero continuous compact physical cutoff admits genuine
one-dimensional theta compressions with either sign at the narrow width and arbitrarily
smaller absolute response at the wider one. The complex kernel needs only one nonzero
value away from the origin. Both signs are obtained by prescribing the
narrow numerator v. -/
theorem exists_centeredLogThetaLift_signed_window_trace (χ : PontryaginDual C𝔽)
    (hχ : ∀ t, χ (QuotientGroup.mk (canonicalIdeleNormSection F t)) = 1)
    (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F))
    {a b s : ℝ} (ha : 0 ≤ a) (hab : a < b) (hs : 0 ≤ s)
    {ρ : ℝ → ℝ} {H : ℝ → ℂ} (hc : Continuous ρ) (hρ : HasCompactSupport ρ) (hnn : 0 ≤ ρ)
    (hn : ∃ x, ρ x ≠ 0) (hH : Continuous H) (hcH : HasCompactSupport H)
    {t : ℝ} (ht : t ≠ 0) (hpos : H t ≠ 0) {v ε : ℝ} (hv : v ≠ 0) (hε : 0 < ε) :
    ∃ f : adelePolarSubspace F,
      let u := centeredLogThetaLift χ τ f
      let E := fun c : ℝ ↦ ∫ x, ‖u x‖ ^ 2 * intervalSobolevDensity (-c) c s x
      let N := fun c : ℝ ↦ logWindowConvolutionNumerator c s ρ H u
      0 < E a ∧ 0 < E b ∧ N a = v ∧ |N b| / E b < ε * (|v| / E a) := by
  have hpair : ∃ x y, H (x - y) ≠ 0 ∧ 0 < ρ x ∧ ∀ᶠ z in 𝓝 y, ρ z = 0 := by
    rcases lt_or_gt_of_ne ht with ht | ht
    · obtain ⟨x, y, hxy, hx, hy⟩ := widthWindow_cutoff_gap (H := fun z ↦ ‖H z‖) hρ hnn hn
        (neg_pos.mpr ht) (by simpa only [neg_neg] using norm_pos_iff.mpr hpos)
      exact ⟨x, y, norm_pos_iff.mp hxy, hx, hy⟩
    · have hrn : ∃ x : ℝ, ρ (-x) ≠ 0 := by
        obtain ⟨x, hx⟩ := hn; exact ⟨-x, by simpa only [neg_neg]⟩
      obtain ⟨x, y, hxy, hx, hy⟩ := widthWindow_cutoff_gap (H := fun z ↦ ‖H (-z)‖)
        (hρ.comp_homeomorph (Homeomorph.neg ℝ)) (fun x ↦ hnn (-x)) hrn
        ht (by simpa only [neg_neg] using norm_pos_iff.mpr hpos)
      refine ⟨-x, -y, ?_, hx, ?_⟩
      · simpa only [neg_sub, neg_sub_neg] using norm_pos_iff.mp hxy
      · have hm : Tendsto (fun z : ℝ ↦ -z) (𝓝 (-y)) (𝓝 y) := by
          simpa only [neg_neg] using continuous_neg.tendsto (-y)
        simpa only [neg_neg] using hm.eventually (show ∀ᶠ z in 𝓝 y, ρ (-z) = 0 from hy)
  obtain ⟨x, y, hxy, hx, hy⟩ := hpair
  obtain ⟨g, hg, hgc, hval⟩ := exists_logWindowConvolutionNumerator_eq_of_cutoff_gap ha hs hc hH hcH hxy hx hy v
  obtain ⟨R, _, hR⟩ := hρ.isBounded.exists_pos_norm_lt
  obtain ⟨T, hT, hT'⟩ := hcH.isBounded.exists_pos_norm_lt
  have hR₀ (x : ℝ) (hx : R < |x|) : ρ x = 0 := by
    by_contra h
    exact hx.not_ge (by simpa only [Real.norm_eq_abs] using (hR x (subset_tsupport ρ h)).le)
  have hT₀ (x : ℝ) (hx : T < |x|) : H x = 0 := by
    by_contra h
    exact hx.not_ge (by simpa only [Real.norm_eq_abs] using (hT' x (subset_tsupport H h)).le)
  obtain ⟨f, heq, hea, heb, hlt⟩ := exists_centeredLogThetaLift_small_wide_window_trace
    χ hχ τ hτ ha hab hs g hgc hg ρ H hT.le hR₀ hT₀ (hval ▸ hv) hε
  have hfa := (logWindowConvolutionNumerator_congr a s hT.le hR₀ hT₀ heq).trans hval
  exact ⟨f, hea, heb, hfa, hfa ▸ hlt⟩


attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

/-- Log-coordinate realization of an idèle-class spatial cutoff along a norm section. -/
def thetaLogWindowCutoff (τ : ℝ≥0ˣ →ₜ* I𝔽) (ρ : C𝔽 → ℝ) (x : ℝ) : ℝ :=
  let e := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  ρ (QuotientGroup.mk (τ (e x)))

private theorem thetaLogWindowCutoff_properties (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F))
    {Λ η : ℝ} {ρ : C𝔽 → ℝ} (hρ : IsSmoothModulatedCutoff (continuousIdeleClassNorm F) Λ η ρ) :
    let r := thetaLogWindowCutoff τ ρ
    Continuous r ∧ HasCompactSupport r ∧ 0 ≤ r ∧ ∃ x, r x ≠ 0 := by
  let e := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let y (x : ℝ) : C𝔽 := QuotientGroup.mk (τ (e x))
  let r := thetaLogWindowCutoff τ ρ
  have hy : Continuous y := continuous_quotient_mk'.comp (τ.continuous.comp e.continuous)
  have heq (x : ℝ) : ideleClassNorm F (y x) = e x := hτ (e x)
  have hval (x : ℝ) : ((ideleClassNorm F (y x)).val : ℝ) = Real.exp x := by rw [heq]; rfl
  have hrel : ∀ g : C𝔽, ρ g = r (Real.log ((ideleClassNorm F g).val : ℝ)) := by
    obtain ⟨q, _, hq, _⟩ := hρ.1.profile
    intro g
    change ρ g = ρ (y _)
    rw [hq g, hq (y _)]
    congr 1
    change ((ideleClassNorm F g).val : ℝ) = ((ideleClassNorm F (y _)).val : ℝ)
    rw [hval, Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt _))]
  have hnon : ∃ x, r x ≠ 0 := by
    by_contra! h
    have hzero : ρ = 0 := funext fun g ↦ (hrel g).trans (h _)
    have hsup := hρ.1.sup_eq_one
    simp [hzero] at hsup
  have hrc : HasCompactSupport r := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -Real.log Λ) (b := Real.log Λ))
    intro x hx
    have h := hρ.1.support_subset (subset_tsupport ρ (show ρ (y x) ≠ 0 from hx))
    change Λ⁻¹ ≤ ((ideleClassNorm F (y x)).val : ℝ) ∧ ((ideleClassNorm F (y x)).val : ℝ) ≤ Λ at h
    rw [hval] at h
    exact ⟨by simpa only [Real.log_inv, Real.log_exp] using Real.log_le_log (inv_pos.mpr hρ.1.radius_pos) h.1,
      by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos x) h.2⟩
  exact ⟨hρ.continuous.comp hy, hrc, fun x ↦ hρ.1.nonneg (y x), hnon⟩


/-- For any actual smooth §9.3 physical cutoff, a complex probe nonzero at any
nonzero log displacement admits both signs on genuine
one-dimensional theta subspaces. At any pair of distinct widths the wide response
can be arbitrarily small relative to the narrow response of the same subspace. -/
theorem exists_centeredLogThetaLift_signed_modulatedCutoff (χ : PontryaginDual C𝔽)
    (hχ : ∀ t, χ (QuotientGroup.mk (canonicalIdeleNormSection F t)) = 1)
    (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F))
    {a b s : ℝ} (ha : 0 ≤ a) (hab : a < b) (hs : 0 ≤ s)
    {Λ η : ℝ} {ρ : C𝔽 → ℝ} (hρ : IsSmoothModulatedCutoff (continuousIdeleClassNorm F) Λ η ρ)
    {H : ℝ → ℂ} (hc : Continuous H) (hcH : HasCompactSupport H)
    (hn : ∃ t : ℝ, t ≠ 0 ∧ H t ≠ 0)
    {v ε : ℝ} (hv : v ≠ 0) (hε : 0 < ε) :
    ∃ f : adelePolarSubspace F,
      let u := centeredLogThetaLift χ τ f
      let E := fun c : ℝ ↦ ∫ x, ‖u x‖ ^ 2 * intervalSobolevDensity (-c) c s x
      let N := fun c : ℝ ↦ logWindowConvolutionNumerator c s (thetaLogWindowCutoff τ ρ) H u
      0 < E a ∧ 0 < E b ∧ N a = v ∧ |N b| / E b < ε * (|v| / E a) := by
  obtain ⟨hr, hrc, hrn, hr₀⟩ := thetaLogWindowCutoff_properties τ hτ hρ
  obtain ⟨t, ht, ht'⟩ := hn
  exact exists_centeredLogThetaLift_signed_window_trace χ hχ τ hτ ha hab hs hr hrc hrn hr₀ hc hcH ht ht' hv hε


private theorem widthEnergy_tendsto_right {b s : ℝ} (hb : 0 < b) (hs : 0 ≤ s) {F : ℝ → ℝ}
    (hF : Continuous F) (hi : Integrable (fun x ↦ F x * intervalSobolevDensity (-b) b s x)) :
    Tendsto (fun c : ℝ ↦ ∫ x, F x * intervalSobolevDensity (-c) c s x) (𝓝[>] 0)
      (𝓝 (∫ x, F x * intervalSobolevDensity (-0) 0 s x)) := by
  let w (c : ℝ) := intervalSobolevDensity (-c) c s
  have hw (c : ℝ) : Continuous (w c) := by
    change Continuous (intervalSobolevDensity (-c) c s)
    unfold intervalSobolevDensity; fun_prop (disch := intros; positivity)
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖F x * w b x‖)
  · exact Eventually.of_forall (fun c ↦ (hF.mul (hw c)).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin (s := Ioi (0:ℝ)), nhdsWithin_le_nhds (gt_mem_nhds hb)] with c hc hb'
    filter_upwards with x
    have hc' : 0 < c := hc
    have hmono : intervalSobolevDensity (-c) c s x ≤ w b x := by
      change intervalSobolevDensity (-c) c s x ≤ intervalSobolevDensity (-b) b s x
      rw [widthEnergy_weight hc'.le, widthEnergy_weight hb.le]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hb'.le) (abs_nonneg x)])
    change ‖F x * intervalSobolevDensity (-c) c s x‖ ≤ _
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (zero_le_one.trans (widthEnergy_one_le hc'.le hs x)),
      Real.norm_of_nonneg (zero_le_one.trans (widthEnergy_one_le hb.le hs x))]
    exact mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
  · exact hi.norm
  · apply ae_of_all
    intro x
    have hwc : Continuous (fun c : ℝ ↦ F x * intervalSobolevDensity (-c) c s x) := by
      unfold intervalSobolevDensity; fun_prop
    exact hwc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds


/-- The two separated endpoints can be tested on one fixed actual theta subspace.
Its real compressed convolution response at the wide strip is strictly below the
limit of its responses on positive widths tending to zero. -/
theorem exists_centeredLogThetaLift_wide_trace_lt_center_limit (χ : PontryaginDual C𝔽)
    (hχ : ∀ t, χ (QuotientGroup.mk (canonicalIdeleNormSection F t)) = 1)
    (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F))
    {b s : ℝ} (hb : 0 < b) (hs : 0 ≤ s)
    {Λ η : ℝ} {ρ : C𝔽 → ℝ} (hρ : IsSmoothModulatedCutoff (continuousIdeleClassNorm F) Λ η ρ)
    {H : ℝ → ℂ} (hc : Continuous H) (hcH : HasCompactSupport H) (hn : ∃ t : ℝ, t ≠ 0 ∧ H t ≠ 0) :
    ∃ f : adelePolarSubspace F,
      let u := centeredLogThetaLift χ τ f
      let E := fun c : ℝ ↦ ∫ x, ‖u x‖ ^ 2 * intervalSobolevDensity (-c) c s x
      let N := fun c : ℝ ↦ logWindowConvolutionNumerator c s (thetaLogWindowCutoff τ ρ) H u
      Tendsto (fun c : ℝ ↦ N c / E c) (𝓝[>] 0) (𝓝 (N 0 / E 0)) ∧ N b / E b < N 0 / E 0 := by
  obtain ⟨f, he₀, heb, hn₀, hlt⟩ := exists_centeredLogThetaLift_signed_modulatedCutoff
    χ hχ τ hτ le_rfl hb hs hρ hc hcH hn (v := 1) one_ne_zero (ε := 1) zero_lt_one
  let u := centeredLogThetaLift χ τ f
  let E := fun c : ℝ ↦ ∫ x, ‖u x‖ ^ 2 * intervalSobolevDensity (-c) c s x
  let r := thetaLogWindowCutoff τ ρ
  let N := fun c : ℝ ↦ logWindowConvolutionNumerator c s r H u
  change 0 < E 0 at he₀
  change 0 < E b at heb
  change N 0 = 1 at hn₀
  change |N b| / E b < 1 * (|1| / E 0) at hlt
  have hlt' : N b / E b < N 0 / E 0 := by
    rw [hn₀]
    exact (div_le_div_of_nonneg_right (le_abs_self _) heb.le).trans_lt (by simpa using hlt)
  have hu : Continuous u := (centeredLogThetaLift_energy χ τ hτ f hb.le hs 0).1
  have he := widthEnergy_tendsto_right hb hs (hu.norm.pow 2) (Integrable.of_integral_ne_zero heb.ne')
  let U (x : ℝ) := ∫ y, H (x - y) * u y
  have hcU : Continuous U := by
    have hconv : U = MeasureTheory.convolution u H (ContinuousLinearMap.mul ℝ ℂ) volume := by
      funext x
      simp only [U, MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply', mul_comm]
    rw [hconv]; exact hcH.continuous_convolution_right _ hu.locallyIntegrable hc
  let P (x : ℝ) := r x * (U x * conj (u x)).re
  obtain ⟨hr, hrc, _, _⟩ := thetaLogWindowCutoff_properties τ hτ hρ
  have hcP : Continuous P := hr.mul (Complex.continuous_re.comp (hcU.mul (Complex.continuous_conj.comp hu)))
  have hN (c : ℝ) : N c = ∫ x, P x * intervalSobolevDensity (-c) c s x := by
    apply integral_congr_ae (ae_of_all _ _)
    intro x
    change r x * _ * (U x * conj (u x)).re = (r x * (U x * conj (u x)).re) * _
    ring
  have hi : Integrable (fun x ↦ P x * intervalSobolevDensity (-b) b s x) := by
    have hw : Continuous (intervalSobolevDensity (-b) b s) := by
      unfold intervalSobolevDensity; fun_prop (disch := intros; positivity)
    apply (hcP.mul hw).integrable_of_hasCompactSupport
    exact hrc.mul_right.mul_right
  have hn : Tendsto N (𝓝[>] 0) (𝓝 (N 0)) := by
    rw [hN 0]
    exact (widthEnergy_tendsto_right hb hs hcP hi).congr (fun c ↦ (hN c).symm)
  exact ⟨f, hn.div he he₀.ne', hlt'⟩

end RiemannMasullo
