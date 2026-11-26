module

public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.PoissonLogQuadrature
public import RiemannMasullo.AppB_AnalyticNT.PolynomialIdealSamples
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Topology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic

/-! # Finite ideal quadrature of the critical-line logarithm

Cauchy's derivative estimate applied to the pole-cleared function supplies a
field-degree polynomial growth bound. The finite ideal values on the fixed
mesh then measure the same weighted logarithm as the genuine critical values. -/

@[expose] public noncomputable section
open Filter MeasureTheory Set Complex Function IsDedekindDomain NumberField Metric
open scoped Topology NNReal ENNReal

namespace RiemannMasullo.LogQuadrature
open FiniteHeckeSamples PolynomialIdealSamples FiniteTaylor
variable {F : Type*} [Field F] [NumberField F]
local notation "Cᶠ" => IdeleClassGroup (𝓞 F) F
local notation "Uᶠ" => PontryaginDual Cᶠ
local notation "Hp" => Complex.re ⁻¹' Ioi (1 : ℝ)

private theorem localPolynomialLipschitz_of_deriv {f : ℝ → ℂ} {C : ℝ} {p : ℕ} (hC : 0 ≤ C)
    (hd : Differentiable ℝ f) (hb : ∀ t, ‖deriv f t‖ ≤ C*(1+|t|)^p) :
    LocalPolynomialLipschitz f C p := by
  intro x y hxy
  have hb' (z : ℝ) (hz : z ∈ Icc (x-1) (x+1)) : |z| ≤ 1+|x| := by
    exact abs_le.mpr ⟨by linarith [neg_abs_le x,hz.1],by linarith [le_abs_self x,hz.2]⟩
  have hy : y ∈ Icc (x-1) (x+1) := by
    obtain ⟨a,b⟩ := abs_le.mp hxy
    exact ⟨by linarith,by linarith⟩
  have h := (convex_Icc (x-1) (x+1)).norm_image_sub_le_of_norm_deriv_le
    (fun t _ ↦ hd t) (fun t ht ↦ (hb t).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith [hb' t ht] : 1+|t| ≤ 2+|x|) p) hC))
    (show x ∈ Icc (x-1) (x+1) by constructor <;> linarith) hy
  simpa only [Real.norm_eq_abs] using h

/-- A nonzero entire function restricts to a nonzero value at almost every height of
the vertical line. Only countability of its complex zero set enters this assertion. -/
private theorem ae_ne_zero_of_entire {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hG₂ : G 2 ≠ 0) :
    ∀ᵐ t ∂poissonMeasure, G (point t) ≠ 0 := by
  let Z := {z : ℂ | G z = 0}
  have he : ∀ᶠ z in codiscreteWithin (univ : Set ℂ), G z ≠ 0 :=
    (AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected (fun z _ ↦ hG.analyticAt z)
      isPreconnected_univ).resolve_left (fun h ↦ hG₂ (h (mem_univ 2)))
  have hc : Zᶜ ∈ codiscrete ℂ := he
  have hdisc := (compl_mem_codiscrete_iff.mp hc).2
  let : DiscreteTopology Z := isDiscrete_iff_discreteTopology.mp hdisc
  have hct : Z.Countable := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hinj : Injective point := fun x y eq ↦ congrArg Complex.im eq
  have hct' := hct.preimage hinj
  have hv : ∀ᵐ t : ℝ, G (point t) ≠ 0 := by
    rw [ae_iff]
    simp only [not_ne_iff]
    have hset : point ⁻¹' Z = {a : ℝ | G (point a) = 0} := rfl
    rw [← hset]
    exact hct'.measure_zero _
  rw [poissonMeasure,ProbabilityTheory.cauchyMeasure_of_scale_ne_zero _ (by norm_num)]
  exact (withDensity_absolutelyContinuous _ _).ae_le hv

private theorem hecke_critical_ae_ne_zero (τ : ℝ≥0ˣ →ₜ* Cᶠ) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Uᶠ) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    ∀ᵐ t ∂poissonMeasure, L (point t) ≠ 0 := by
  have h₂ : L 2 ≠ 0 := (he ⟨2,by norm_num⟩).symm ▸ finiteHeckeL_ne_zero_of_one_lt_re χ _
  have hp : polarFactor 2 ≠ 0 := by
    rw [polarFactor,polarRoot,frequency_eq_inv_cpow (by decide : (2:ℕ) ≠ 0)]
    norm_num
  filter_upwards [ae_ne_zero_of_entire (poleCleared_entire τ hτ χ hχ L hL he) (mul_ne_zero hp h₂)]
    with t h
  exact fun hz ↦ h (by rw [hz,mul_zero])

/-- The literal finite ideal table at the `2 n²` left endpoints of the critical line. -/
def heckeLogStatistic (χ : Uᶠ) (n : ℕ) : ℝ :=
  statistic poissonMeasure (frequencySample χ) n

/-- Arithmetic logarithmic quadrature assuming a critical derivative estimate. -/
private theorem heckeLogStatistic_of_deriv (τ : ℝ≥0ˣ →ₜ* Cᶠ) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Uᶠ) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {C : ℝ} {p : ℕ} (hC : 0 ≤ C)
    (hd : Differentiable ℝ (fun t ↦ L (point t)))
    (hb : ∀ t, ‖deriv (fun y ↦ L (point y)) t‖ ≤ C*(1+|t|)^p)
    (hlog : Integrable (fun t ↦ poissonWeight t * Real.log ‖L (point t)‖)) :
    Tendsto (heckeLogStatistic χ) atTop
      (𝓝 (∫ t, poissonWeight t * Real.log ‖L (point t)‖)) := by
  rw [← poisson_integral (fun t ↦ Real.log ‖L (point t)‖)]
  exact tendsto_statistic poissonMeasure _ _ hC (localPolynomialLipschitz_of_deriv hC hd hb)
    ((eventually_frequencySample_error τ hτ χ hχ L hL he).mono
      (fun n h t ht ↦ (h t ht).le)) (hecke_critical_ae_ne_zero τ hτ χ hχ L hL he)
    ((poisson_integrable_iff _).mpr hlog) poisson_logMoment

private theorem re_bounds (t : ℝ) {z : ℂ} (hz : ‖z-point t‖ ≤ 1) :
    -(1/2:ℝ) ≤ z.re ∧ z.re ≤ 2 := by
  have hh := (Complex.abs_re_le_norm (z-point t)).trans hz
  change |z.re-(1/2:ℝ)| ≤ 1 at hh
  obtain ⟨hh,hl⟩ := abs_le.mp hh
  constructor <;> linarith

/-- The half-integer functional-equation bound at `Re s = -1/2` propagates its
field-degree exponent to the fixed unit disks about all critical heights. -/
theorem hecke_poleCleared_disk_polynomial (τ : ℝ≥0ˣ →ₜ* Cᶠ) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Uᶠ) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    ∃ C > (0:ℝ), ∀ t : ℝ, ∀ z : ℂ, ‖z - point t‖ ≤ 1 →
      ‖polarFactor z * L z‖ ≤ C*(1+|t|)^(Module.finrank ℚ F) := by
  let d := Module.finrank ℚ F
  let G (w : ℂ) := polarFactor w * L w
  obtain ⟨B,K,hB,hK,hr,hl⟩ := poleCleared_boundary_bounds τ hτ χ hχ L hL he
  let h := B+4
  have hK' : 0 < K := zero_lt_one.trans_le hK
  have left (s : ℂ) (hs : s.re = -(1/2:ℝ)) :
      ‖G s‖ ≤ K^2 * (2 * ‖s+(h:ℂ)‖)^d := by
    have hu := hl 1 (by decide) s (by norm_num; exact hs)
    simp only [Nat.cast_one,Nat.reduceAdd,mul_one] at hu
    have hx := Complex.re_le_norm (s+(h:ℂ))
    have hy := Complex.abs_im_le_norm (s+(h:ℂ))
    simp only [Complex.add_re,Complex.ofReal_re,hs] at hx
    simp only [Complex.add_im,Complex.ofReal_im,add_zero] at hy
    have hb : B+3*1+|s.im| ≤ 2*‖s+(h:ℂ)‖ := by dsimp only [h] at hx; linarith
    refine hu.trans ?_
    gcongr; linarith
  refine ⟨(K^2*2^d)*(B+6)^d, by positivity, ?_⟩
  intro t z hz
  obtain ⟨ha,hb⟩ := re_bounds t hz
  have hn := weighted_vertical_strip G (poleCleared_entire τ hτ χ hχ L hL he)
    (h:=h) (b:=2) (a:= -(1/2)) (by norm_num) (by dsimp only [h]; linarith)
    (sq_nonneg K) d (poleCleared_polynomial_growth χ L hL he (by norm_num)) left
    (fun s hs ↦ (hr s hs.ge).trans (by nlinarith [mul_nonneg hK'.le (sub_nonneg.mpr hK)]))
    z ha hb
  have height : ‖z+(h:ℂ)‖ ≤ (B+6)*(1+|t|) := by
    have hj := norm_add_le (z-point t) (point t+(h:ℂ))
    rw [show z-point t+(point t+(h:ℂ)) = z+(h:ℂ) by ring] at hj
    have ht := Complex.norm_le_abs_re_add_abs_im (point t+(h:ℂ))
    change ‖point t+(h:ℂ)‖ ≤ |1/2+h|+|t+0| at ht
    rw [add_zero,abs_of_nonneg (by dsimp only [h]; linarith : 0 ≤ 1/2+h)] at ht
    dsimp only [h] at ht hj ⊢
    nlinarith [mul_nonneg (by linarith : 0 ≤ B+5) (abs_nonneg t)]
  refine hn.trans ?_
  change _ ≤ (K^2*2^d)*(B+6)^d*(1+|t|)^d
  rw [mul_assoc (K^2*2^d), ← mul_pow]
  gcongr

private theorem point_eq (t : ℝ) : (1/2:ℂ) + (t:ℂ)*I = point t := by
  apply Complex.ext <;> simp [point,Complex.mul_re,Complex.mul_im]

private theorem vertical_deriv {f : ℂ → ℂ} (hf : Differentiable ℂ f) (t : ℝ) :
    HasDerivAt (fun y : ℝ ↦ f (point y)) (deriv f (point t)*I) t := by
  have hz : HasDerivAt (fun z : ℂ ↦ (1/2:ℂ)+z*I) I (t:ℂ) := by
    simpa using (((hasDerivAt_id (t:ℂ)).mul_const I).const_add (1/2:ℂ))
  have h1 := (hf (point t)).hasDerivAt
  rw [← point_eq] at h1
  have hs := (h1.comp (t:ℂ) hz).comp_ofReal
  simpa only [Function.comp_apply,point_eq] using hs

private theorem vertical_bounds {f : ℂ → ℂ} (hf : Differentiable ℂ f) {E : ℝ} {k : ℕ}
    (hb : ∀ t : ℝ, ∀ z : ℂ, ‖z-point t‖ ≤ 1 → ‖f z‖ ≤ E*(1+|t|)^k) (t : ℝ) :
    ‖f (point t)‖ ≤ E*(1+|t|)^k ∧ ‖deriv (fun y : ℝ ↦ f (point y)) t‖ ≤ E*(1+|t|)^k := by
  refine ⟨hb t (point t) (by simp), ?_⟩
  rw [(vertical_deriv hf t).deriv,norm_mul,Complex.norm_I,mul_one]
  simpa only [div_one] using Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f:=f) (c:=point t) zero_lt_one hf.diffContOnCl (fun z hz ↦ hb t z (mem_sphere_iff_norm.mp hz).le)

/-- The derivative of the ordinary critical-line continuation has an admissible
polynomial exponent exactly equal to the field degree. -/
theorem hecke_critical_deriv_polynomial (τ : ℝ≥0ˣ →ₜ* Cᶠ) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Uᶠ) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    Differentiable ℝ (fun t ↦ L (point t)) ∧ ∃ C > (0:ℝ), ∀ t : ℝ,
      ‖deriv (fun y ↦ L (point y)) t‖ ≤ C*(1+|t|)^(Module.finrank ℚ F) := by
  let G (w : ℂ) := polarFactor w * L w
  let d := Module.finrank ℚ F
  have hG : Differentiable ℂ G := poleCleared_entire τ hτ χ hχ L hL he
  have hP : Differentiable ℂ polarFactor := by unfold polarFactor polarRoot frequency; fun_prop
  obtain ⟨A,hA,hgb⟩ := hecke_poleCleared_disk_polynomial τ hτ χ hχ L hL he
  have hpb (t : ℝ) (z : ℂ) (hz : ‖z-point t‖ ≤ 1) : ‖polarFactor z‖ ≤ 36*(1+|t|)^0 := by
    have h := polarFactor_halfInteger (m:=1) (s:=z) (by norm_num; exact (re_bounds t hz).1)
    norm_num at h ⊢
    exact h
  let c : ℝ := (Real.sqrt 2-1)^2
  have hc : 0 < c := sq_pos_of_pos (by nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),Real.sqrt_nonneg 2])
  have hp (t : ℝ) : polarFactor (point t) ≠ 0 :=
    norm_pos_iff.mp (hc.trans_le (critical_factor_lower t))
  have eqf : (fun t ↦ L (point t)) = (fun t : ℝ ↦ G (point t)/polarFactor (point t)) := by
    funext t
    exact (mul_div_cancel_left₀ (L (point t)) (hp t)).symm
  rw [eqf]
  have gd : Differentiable ℝ (fun t : ℝ ↦ G (point t)) := fun t ↦ (vertical_deriv hG t).differentiableAt
  have pd : Differentiable ℝ (fun t : ℝ ↦ polarFactor (point t)) := fun t ↦ (vertical_deriv hP t).differentiableAt
  refine ⟨gd.div pd hp, (72*A)/c^2, by positivity, fun t ↦ ?_⟩
  have hg := vertical_bounds hG hgb t
  have hb := vertical_bounds hP hpb t
  simp only [pow_zero,mul_one] at hb
  rw [deriv_fun_div (gd t) (pd t) (hp t),norm_div,norm_pow]
  have hb₁ := mul_le_mul hg.2 hb.1 (norm_nonneg _) (by positivity)
  have hb₂ := mul_le_mul hg.1 hb.2 (norm_nonneg _) (by positivity)
  have htop := norm_sub_le
    (deriv (fun y : ℝ ↦ G (point y)) t * polarFactor (point t))
    (G (point t)*deriv (fun y : ℝ ↦ polarFactor (point y)) t)
  rw [norm_mul,norm_mul] at htop
  calc _ ≤ (72*A*(1+|t|)^d) / c^2 := by
          apply div_le_div₀ (by positivity) _ (by positivity) (pow_le_pow_left₀ hc.le (critical_factor_lower t) 2)
          dsimp only [d]
          linarith
    _ = _ := by ring

/-- The sole remaining analytic hypothesis is absolute integrability of the
ordinary boundary logarithm for the Poisson density. -/
theorem tendsto_heckeLogStatistic (τ : ℝ≥0ˣ →ₜ* Cᶠ) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Uᶠ) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s)
    (hlog : Integrable (fun t ↦ poissonWeight t * Real.log ‖L (point t)‖)) :
    Tendsto (heckeLogStatistic χ) atTop (𝓝 (∫ t, poissonWeight t * Real.log ‖L (point t)‖)) := by
  obtain ⟨hd,C,hC,hb⟩ := hecke_critical_deriv_polynomial τ hτ χ hχ L hL he
  exact heckeLogStatistic_of_deriv τ hτ χ hχ L hL he hC.le hd hb hlog

/-- A formula for the statistic using only arctangents and the finite ideal table. -/
theorem heckeLogStatistic_eq_arctan (χ : Uᶠ) (n : ℕ) :
    heckeLogStatistic χ n = ∑ j ∈ Finset.range (2*n*n),
      ((Real.arctan (node n (j+1)/(3/2)) - Real.arctan (node n j/(3/2)))/Real.pi) *
        clip n (frequencySample χ n (node n j)) := by
  unfold heckeLogStatistic statistic
  apply Finset.sum_congr rfl
  intro j _
  rw [cell,poisson_Ico (by rw [node_dist]; linarith [show 0 ≤ (n:ℝ)⁻¹ by positivity])]

/-- The final logarithmic sum changes by at most (n2^{-n}) when the true table is
replaced by the finite ideal table. This estimate requires no boundary-log integrability. -/
theorem eventually_abs_heckeLogStatistic_sub_true (τ : ℝ≥0ˣ →ₜ* Cᶠ) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Uᶠ) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    ∀ᶠ n : ℕ in atTop, |heckeLogStatistic χ n - statistic poissonMeasure (fun _ t ↦ L (point t)) n| ≤
      (n:ℝ)*(1/2:ℝ)^n := by
  filter_upwards [eventually_frequencySample_error τ hτ χ hχ L hL he, eventually_gt_atTop (0:ℕ)] with n h hn
  let s := Finset.range (2*n*n)
  have hm : (∑ j ∈ s, poissonMeasure.real (cell n j)) ≤ 1 := by
    apply (sum_measureReal_le_measureReal_univ (fun j (_ : j ∈ s) ↦ (measurableSet_Ico : MeasurableSet (cell n j))) ?_).trans measureReal_le_one
    intro i hi j hj hne
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hne ((of_cell hn (Finset.mem_range.mp hi) hxi).2.symm.trans (of_cell hn (Finset.mem_range.mp hj) hxj).2)
  have ht (j : ℕ) (hj : j ∈ s) : |node n j| ≤ (n:ℝ)+1 := by
    have hnext : node n j < node n (j+1) := by rw [node_dist]; linarith [show 0 < (n:ℝ)⁻¹ by positivity]
    obtain ⟨hl,hr⟩ := (of_cell hn (Finset.mem_range.mp hj) (show node n j ∈ cell n j from ⟨le_rfl,hnext⟩)).1
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  unfold heckeLogStatistic statistic
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ j ∈ s, poissonMeasure.real (cell n j) * ((n:ℝ)*(1/2:ℝ)^n) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [← mul_sub,abs_mul,abs_of_nonneg measureReal_nonneg]
          apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
          refine (abs_clip_sub_clip hn _ _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
          rw [norm_sub_rev]
          exact (h _ (ht _ hj)).le
    _ ≤ _ := by rw [← Finset.sum_mul]; simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ (n:ℝ)*(1/2:ℝ)^n)

/-- The exact values on the same grid have the same limit. -/
theorem tendsto_trueLogStatistic (τ : ℝ≥0ˣ →ₜ* Cᶠ) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Uᶠ) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s)
    (hlog : Integrable (fun t ↦ poissonWeight t * Real.log ‖L (point t)‖)) :
    Tendsto (statistic poissonMeasure (fun _ t ↦ L (point t))) atTop
      (𝓝 (∫ t, poissonWeight t * Real.log ‖L (point t)‖)) := by
  obtain ⟨hd,C,hC,hb⟩ := hecke_critical_deriv_polynomial τ hτ χ hχ L hL he
  rw [← poisson_integral (fun t ↦ Real.log ‖L (point t)‖)]
  exact tendsto_statistic poissonMeasure _ _ hC.le (localPolynomialLipschitz_of_deriv hC.le hd hb)
    (Eventually.of_forall (fun _ _ _ ↦ by simp)) (hecke_critical_ae_ne_zero τ hτ χ hχ L hL he)
    ((poisson_integrable_iff _).mpr hlog) poisson_logMoment


/-- The actual finite critical-line table has the stated rate if the canonical
log modulus has the integrated tail bound. All arithmetic and derivative data
come from the ordinary finite Hecke continuation. -/
theorem hasRootLogRate_heckeLogStatistic (τ : ℝ≥0ˣ →ₜ* Cᶠ) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Uᶠ) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s)
    (hlog : Integrable (fun t ↦ poissonWeight t * Real.log ‖L (point t)‖))
    (htail : HasIntegratedLogTail poissonMeasure (fun t ↦ Real.log ‖L (point t)‖)) :
    HasRootLogRate (fun n ↦ heckeLogStatistic χ n -
      ∫ t, poissonWeight t * Real.log ‖L (point t)‖) := by
  obtain ⟨hd,C,hC,hb⟩ := hecke_critical_deriv_polynomial τ hτ χ hχ L hL he
  have hh := hasRootLogRate_statistic poissonMeasure (fun t ↦ L (point t)) (frequencySample χ)
    hC.le (localPolynomialLipschitz_of_deriv hC.le hd hb)
    ((eventually_frequencySample_error τ hτ χ hχ L hL he).mono (fun _ hn t ht ↦ (hn t ht).le))
    (hecke_critical_ae_ne_zero τ hτ χ hχ L hL he) hd.continuous.measurable
    ((poisson_integrable_iff _).mpr hlog) poisson_sqrtMoment htail
  simpa only [heckeLogStatistic,poisson_integral] using hh

end RiemannMasullo.LogQuadrature
