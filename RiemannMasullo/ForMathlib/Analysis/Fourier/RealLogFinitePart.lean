module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# The logarithmic Fourier transform on the real line

The Fourier transform of the exponential scale gives the Poisson kernel. Frullani integration
identifies the transform of log absolute value on a test vanishing at zero. Subtracting the
Cauchy reference function fixes the delta contribution for an arbitrary Schwartz test.
-/

public noncomputable section

section

open Set Filter MeasureTheory Real
open scoped Topology
namespace RealFourierLog
private theorem expDiffBound {α β y : ℝ} (hα : 0 < α) (hβ : 0 < β) (hy : 0 ≤ y) :
    |exp (-α * y) - exp (-β * y)| ≤ |β - α| * y * exp (-(min α β) * y) := by
  wlog h : α ≤ β generalizing α β
  · have := this hβ hα (le_of_not_ge h)
    rwa [abs_sub_comm α β, min_comm, abs_sub_comm (exp (-β * y))] at this
  rw [min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
  have h1 : exp (-β * y) ≤ exp (-α * y) := exp_le_exp.mpr (by nlinarith)
  rw [abs_of_nonneg (sub_nonneg.mpr h1)]
  -- exp(-αy) - exp(-βy) = exp(-αy) (1 - exp(-(β-α)y)) ≤ exp(-αy) (β-α) y
  have h2 : 1 - exp (-((β - α) * y)) ≤ (β - α) * y := by
    have := add_one_le_exp (-((β - α) * y)); linarith
  have h3 : exp (-β * y) = exp (-α * y) * exp (-((β - α) * y)) := by
    rw [← exp_add]; ring_nf
  rw [h3]
  have := exp_pos (-α * y)
  nlinarith

open Real in

/-- Frullani's integral for two decaying exponentials. -/
private theorem expFrullani {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IntegrableOn (fun y ↦ y⁻¹ * (exp (-α * y) - exp (-β * y))) (Ioi 0) ∧
      ∫ y in Ioi 0, y⁻¹ * (exp (-α * y) - exp (-β * y)) = log (β / α) := by
  have hint : IntegrableOn (fun y ↦ y⁻¹ * (exp (-α * y) - exp (-β * y))) (Ioi 0) := by
    have hm : 0 < min α β := lt_min hα hβ
    have hdom : IntegrableOn (fun y ↦ |β - α| * exp (-(min α β) * y)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hm).const_mul _
    refine hdom.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y (hy : 0 < y)
    rw [norm_mul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hy]
    have := expDiffBound hα hβ hy.le
    rw [inv_mul_le_iff₀ hy]
    nlinarith [this]
  refine ⟨hint, ?_⟩
  have h := Frullani.integral_Ioi_eq (f := fun x : ℝ ↦ exp (-x)) (L := 1) (R := 0)
    ((by fun_prop : Continuous fun x : ℝ ↦ exp (-x)).locallyIntegrable.locallyIntegrableOn _) hα hβ
    (by simpa using ((by fun_prop : Continuous fun x : ℝ ↦ exp (-x)).tendsto 0).mono_left nhdsWithin_le_nhds)
    (by simpa using tendsto_exp_neg_atTop_nhds_zero)
    (by simpa [smul_eq_mul, neg_mul] using hint)
  simpa [smul_eq_mul, neg_mul] using h

open Real in

/-- The Frullani integrand for exponentials has constant sign. -/
private theorem absFrullani {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ y in Ioi 0, |y⁻¹ * (exp (-α * y) - exp (-β * y))| = |log (β / α)| := by
  obtain ⟨hi, hv⟩ := expFrullani hα hβ
  rcases le_total α β with h | h
  · have hnn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ y⁻¹ * (exp (-α * y) - exp (-β * y)) := by
      intro y (hy : 0 < y)
      exact mul_nonneg (inv_nonneg.mpr hy.le)
        (sub_nonneg.mpr (exp_le_exp.mpr (by nlinarith)))
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy ↦ abs_of_nonneg (hnn y hy)), hv,
      abs_of_nonneg (log_nonneg ((one_le_div hα).mpr h))]
  · have hnp : ∀ y ∈ Ioi (0 : ℝ), y⁻¹ * (exp (-α * y) - exp (-β * y)) ≤ 0 := by
      intro y (hy : 0 < y)
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hy.le)
        (sub_nonpos.mpr (exp_le_exp.mpr (by nlinarith)))
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy ↦ abs_of_nonpos (hnp y hy)),
      integral_neg, hv, abs_of_nonpos (log_nonpos (div_nonneg hβ.le hα.le) ((div_le_one hα).mpr h))]
end RealFourierLog

end

section

open MeasureTheory Set Real Filter
open scoped FourierTransform Topology
namespace RealFourierLog

/-- The exponential weight using the self-dual character exp(−2πixξ). -/
private def exponentialWeight (a y : ℝ) : ℂ := (exp (-2*π*a*|y|) : ℝ)
private def poissonDensity (a x : ℝ) : ℂ := (a / (π*(a^2+x^2)) : ℝ)

private theorem integrable_exponentialWeight {a : ℝ} (ha : 0 < a) : Integrable (exponentialWeight a) := by
  have hp : 0 < 2*π*a := by positivity
  have hneg : EqOn (exponentialWeight a) (fun x : ℝ ↦ (exp ((2*π*a)*x) : ℂ)) (Iic 0) := by
    intro x hx; dsimp only [exponentialWeight]; rw [abs_of_nonpos hx]; push_cast; ring_nf
  have hpos : EqOn (exponentialWeight a) (fun x : ℝ ↦ (exp (-(2*π*a)*x) : ℂ)) (Ioi 0) := by
    intro x hx; dsimp only [exponentialWeight]; rw [abs_of_pos hx]; push_cast;ring_nf
  apply integrableOn_univ.mp
  rw [← Iic_union_Ioi (a := (0 : ℝ)),integrableOn_union]
  exact ⟨(integrableOn_exp_mul_Iic hp 0).ofReal.congr_fun hneg.symm measurableSet_Iic,
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hp) 0).ofReal.congr_fun hpos.symm measurableSet_Ioi⟩

/-- Direct half-line integration of the exponential yields the Cauchy density. -/
private theorem fourier_exponentialWeight {a : ℝ} (ha : 0 < a) (ξ : ℝ) : 𝓕 (exponentialWeight a) ξ = poissonDensity a ξ := by
  let M (x : ℝ) := Complex.exp (((-2*π*x*ξ : ℝ) : ℂ)*Complex.I) * exponentialWeight a x
  let u : ℂ := 2*↑π*((a : ℂ)-Complex.I*ξ)
  let v : ℂ := -2*↑π*((a : ℂ)+Complex.I*ξ)
  have hu : 0 < u.re := by simp [u,Complex.mul_re];positivity
  have hv : v.re < 0 := by simp [v,Complex.mul_re];positivity
  have hleft : EqOn M (fun x : ℝ ↦ Complex.exp (u*x)) (Iic 0) := by
    intro x hx
    dsimp only [M,exponentialWeight,u]
    rw [Complex.ofReal_exp,← Complex.exp_add,abs_of_nonpos hx]
    congr 1;push_cast;ring
  have hright : EqOn M (fun x : ℝ ↦ Complex.exp (v*x)) (Ioi 0) := by
    intro x hx
    dsimp only [M,exponentialWeight,v]
    rw [Complex.ofReal_exp,← Complex.exp_add,abs_of_pos hx]
    congr 1;push_cast;ring
  have h₁ := (integrableOn_exp_mul_complex_Iic hu 0).congr_fun hleft.symm measurableSet_Iic
  have h₂ := (integrableOn_exp_mul_complex_Ioi hv 0).congr_fun hright.symm measurableSet_Ioi
  rw [Real.fourier_real_eq_integral_exp_smul]
  change (∫ x, M x) = _
  rw [← intervalIntegral.integral_Iic_add_Ioi h₁ h₂,setIntegral_congr_fun measurableSet_Iic hleft,
    setIntegral_congr_fun measurableSet_Ioi hright,integral_exp_mul_complex_Iic hu,integral_exp_mul_complex_Ioi hv]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  have h₁ : u ≠ 0 := fun he ↦ by simp [he] at hu
  have h₂ : v ≠ 0 := fun he ↦ by simp [he] at hv
  dsimp only [poissonDensity]
  push_cast
  have hs : (a : ℂ)^2+(ξ : ℂ)^2 ≠ 0 := by exact_mod_cast (show a^2+ξ^2 ≠ 0 by positivity)
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  field_simp [h₁,h₂,hs,hπ]
  dsimp only [u,v]
  ring_nf
  simp [Complex.I_sq]

/-- One integration in the scale of the Cauchy kernel has the half-line mass 1/(2|x|). -/
private theorem scale_mass {x : ℝ} (hx : x ≠ 0) :
    IntegrableOn (fun a : ℝ ↦ (π*(a^2+x^2))⁻¹) (Ioi 0) ∧
    (∫ a : ℝ in Ioi 0, (π*(a^2+x^2))⁻¹) = 1/(2*|x|) := by
  let b := |x|⁻¹
  have hB : 0 < b := inv_pos.mpr (abs_pos.mpr hx)
  have hx2 : |x|^2 = x^2 := sq_abs x
  have hchange (a : ℝ) : (π*(a^2+x^2))⁻¹ =
      (π*|x|^2)⁻¹ * (1+(b*a)^2)⁻¹ := by
    dsimp only [b]
    field_simp [abs_ne_zero.mpr hx, pi_ne_zero]
    rw [hx2]
    ring
  simp_rw [hchange]
  refine ⟨(integrable_inv_one_add_mul_sq hB.ne').integrableOn.const_mul _,?_⟩
  rw [integral_const_mul,integral_comp_mul_left_Ioi (fun u : ℝ ↦ (1+u^2)⁻¹) 0 hB,mul_zero,
    integral_Ioi_inv_one_add_sq,Real.arctan_zero,sub_zero,smul_eq_mul]
  dsimp only [b]
  field_simp [abs_ne_zero.mpr hx,pi_ne_zero]

end RealFourierLog

end

section

open MeasureTheory Set Filter Real
open scoped FourierTransform Topology
namespace RealFourierLog

private def referenceFunction (x : ℝ) : ℂ := ((1+x^2)⁻¹ : ℝ)

private theorem integrable_referenceFunction : Integrable referenceFunction := integrable_inv_one_add_sq.ofReal

private theorem fourier_referenceFunction (ξ : ℝ) : 𝓕 referenceFunction ξ = (π : ℂ)*exponentialWeight 1 ξ := by
  have hLP (x : ℝ) : 𝓕 (exponentialWeight 1) x = (π : ℂ)⁻¹*referenceFunction x := by
    rw [fourier_exponentialWeight one_pos,poissonDensity,referenceFunction]
    simp [one_div,mul_comm]
  have hI : Integrable (𝓕 (exponentialWeight 1)) := by simp_rw [funext hLP];exact integrable_referenceFunction.const_mul _
  have hC : Continuous (exponentialWeight 1) := by unfold exponentialWeight;fun_prop
  have hi := congrFun (hC.fourierInv_fourier_eq (integrable_exponentialWeight one_pos) hI) (-ξ)
  rw [Real.fourierInv_eq_fourier_neg, neg_neg, funext hLP, Real.fourier_real_eq_integral_exp_smul] at hi
  simp only [smul_eq_mul] at hi
  have hlin (y : ℝ) : Complex.exp (((-2*π*y*ξ : ℝ) : ℂ)*Complex.I)*((π : ℂ)⁻¹*referenceFunction y) =
    (π : ℂ)⁻¹*(Complex.exp (((-2*π*y*ξ : ℝ) : ℂ)*Complex.I)*referenceFunction y) := by ring
  simp_rw [hlin] at hi
  rw [integral_const_mul,show exponentialWeight 1 (-ξ)=exponentialWeight 1 ξ by simp [exponentialWeight]] at hi
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  exact (eq_inv_mul_iff_mul_eq₀ (by exact_mod_cast pi_ne_zero)).mp hi.symm |>.symm

/-- The singular spectral constant for the Cauchy reference, by differentiating Euler's
gamma integral at one. -/
private theorem reference_log :
    Integrable (fun ξ : ℝ ↦ (log |ξ| : ℂ)*𝓕 referenceFunction ξ) ∧
    (∫ ξ : ℝ, (log |ξ| : ℂ)*𝓕 referenceFunction ξ) = -((eulerMascheroniConstant+log (2*π) : ℝ) : ℂ) := by
  let c : ℝ := 2*π
  have hc : 0<c := by dsimp [c];positivity
  have hΓ : (∫ x : ℝ in Ioi 0, log x*exp (-x)) = -eulerMascheroniConstant :=
    Real.deriv_Gamma_one_eq_integral_log.symm.trans Real.hasDerivAt_Gamma_one.deriv
  have hΓI : IntegrableOn (fun x : ℝ ↦ log x*exp (-x)) (Ioi 0) := by
    by_contra hn
    rw [integral_undef hn] at hΓ
    linarith [one_half_lt_eulerMascheroniConstant]
  let B (x : ℝ) := (log x-log c)*exp (-x)
  have hb (x : ℝ) : B x = log x*exp (-x) - log c*exp (-x) := by dsimp only [B];ring
  have hBI : IntegrableOn B (Ioi 0) := by
    rw [funext hb]
    exact hΓI.sub ((integrableOn_exp_neg_Ioi 0).const_mul _)
  have hBV : (∫ x in Ioi 0, B x) = -eulerMascheroniConstant-log c := by
    simp_rw [hb];rw [integral_sub hΓI ((integrableOn_exp_neg_Ioi 0).const_mul _),hΓ,integral_const_mul,integral_exp_neg_Ioi_zero,mul_one]
  let A (x : ℝ) := log x * exp (-c*x)
  have hA : EqOn A (fun x ↦ B (c*x)) (Ioi 0) := by
    intro x hx;dsimp only [A,B]
    rw [Real.log_mul hc.ne' (ne_of_gt hx),add_sub_cancel_left,neg_mul]
  have hAI : IntegrableOn A (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff B 0 hc).2 (by simpa using hBI) |>.congr_fun hA.symm measurableSet_Ioi
  have hAV : (∫ x in Ioi 0,A x) = c⁻¹*(-eulerMascheroniConstant-log c) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hA,integral_comp_mul_left_Ioi B 0 hc,mul_zero,hBV,smul_eq_mul]
  have hfull := integral_comp_abs (f := A)
  rw [hAV] at hfull
  have hne : -eulerMascheroniConstant-log c < 0 := by
    have hlog : 0<log c := Real.log_pos (by dsimp [c];linarith [pi_gt_three])
    linarith [one_half_lt_eulerMascheroniConstant]
  have hfullI : Integrable (fun x : ℝ ↦ A |x|) := by
    by_contra hn
    rw [integral_undef hn] at hfull
    have hlt : 2*(c⁻¹*(-eulerMascheroniConstant-log c))<0 := by
      exact mul_neg_of_pos_of_neg two_pos (mul_neg_of_pos_of_neg (inv_pos.mpr hc) hne)
    linarith
  have hf (x : ℝ) : (log |x| : ℂ)*𝓕 referenceFunction x = (π : ℂ)*(A |x| : ℝ) := by
    rw [fourier_referenceFunction];dsimp only [exponentialWeight,A,c]
    simp only [mul_one,Complex.ofReal_mul]
    ring
  simp_rw [hf]
  refine ⟨hfullI.ofReal.const_mul _,?_⟩
  rw [integral_const_mul,integral_complex_ofReal,hfull]
  dsimp only [c]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr pi_ne_zero]
  ring

end RealFourierLog

end

section

open MeasureTheory Set Filter Real
open scoped Topology
namespace RealFourierLog

set_option quotPrecheck false
local notation "A(" ε ")" => {x : ℝ | ε ≤ |x|}

private theorem cut_integrable {f : ℝ → ℂ} (hf : Integrable f) (hm : Measurable f) {ε : ℝ} (hε : 0<ε) :
    IntegrableOn (fun x ↦ f x / ((|x| : ℝ) : ℂ)) A(ε) := by
  refine (hf.norm.integrableOn.mul_const ε⁻¹).mono' (hm.div (Complex.measurable_ofReal.comp continuous_abs.measurable)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_le measurable_const continuous_abs.measurable)] with x hx
  change ε≤|x| at hx
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_abs,div_eq_mul_inv]
  gcongr

private theorem half_cut {ε : ℝ} (hε : 0<ε) :
    (∫ x in Ioi ε, (1+x^2)⁻¹/x) = log (1+(ε⁻¹)^2)/2 := by
  let F (x : ℝ) := -log (1+(x⁻¹)^2)/2
  have hder (x : ℝ) (hx : x ∈ Ici ε) : HasDerivAt F ((1+x^2)⁻¹/x) x := by
    have hpos : 0<x := hε.trans_le hx
    have hn : 1+(x⁻¹)^2 ≠0 := by positivity
    have h : HasDerivAt (fun t : ℝ ↦ 1+(t⁻¹)^2) (0+2*(x⁻¹)^(2-1)*(-(1)/x^2)) x :=
      (hasDerivAt_const x (1 : ℝ)).add (((hasDerivAt_id x).inv hpos.ne').pow 2)
    convert (h.log hn).neg.div_const 2 using 1
    · norm_num
      field_simp [hpos.ne',hn,(show 1+x^2≠0 by positivity)]
      ring
  have hi : IntegrableOn (fun x : ℝ ↦ (1+x^2)⁻¹/x) (Ioi ε) := by
    refine (integrable_inv_one_add_sq.norm.integrableOn.mul_const ε⁻¹).mono' (show Measurable (fun x : ℝ ↦ (1+x^2)⁻¹/x) by fun_prop).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x (hx : ε < x)
    rw [norm_div,Real.norm_of_nonneg (hε.trans hx).le,div_eq_mul_inv]
    gcongr
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hi := (tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 2
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add hi
    have h1 : Tendsto (fun x : ℝ ↦ 1+(x⁻¹)^2) atTop (𝓝 1) := by simpa using h
    have hl := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    simpa [F,Function.comp_def] using hl.neg.div_const 2
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hder hi hlim
  dsimp only [F] at h
  linarith

/-- The symmetrically truncated Cauchy reference has zero finite part. -/
private theorem reference_cutoff {ε : ℝ} (hε : 0<ε) :
    (∫ x in A(ε), referenceFunction x / ((|x| : ℝ) : ℂ)) + 2*(log ε : ℂ) = (log (1+ε^2) : ℂ) := by
  let F (x : ℝ) := (1+x^2)⁻¹/x
  let φ := (Ici ε).indicator F
  have hm : MeasurableSet A(ε) := measurableSet_le measurable_const continuous_abs.measurable
  have hind (x : ℝ) : A(ε).indicator (fun x : ℝ ↦ (1+x^2)⁻¹/|x|) x = φ |x| := by
    by_cases hx : ε ≤ |x|
    · simp [φ,F,indicator_of_mem (show x ∈ A(ε) from hx),indicator_of_mem (show |x| ∈ Ici ε from hx),sq_abs]
    · simp [φ,indicator_of_notMem (show x ∉ A(ε) from hx),indicator_of_notMem (show |x| ∉ Ici ε from hx)]
  have hinter : Ioi 0 ∩ Ici ε = Ici ε := inter_eq_right.mpr (fun _ hx ↦ hε.trans_le hx)
  have hhalf : (∫ t in Ioi (0 : ℝ), φ t) = ∫ t in Ioi ε, F t := by
    rw [show φ = (Ici ε).indicator F from rfl,integral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici,inter_comm,hinter,integral_Ici_eq_integral_Ioi]
  have hsc := integral_comp_abs (f := φ)
  rw [hhalf,show (∫ t in Ioi ε,F t)=_ from half_cut hε] at hsc
  have hc : (∫ x in A(ε), (1+x^2)⁻¹/|x|) = 2*(log (1+(ε⁻¹)^2)/2) := by
    rw [← integral_indicator hm]
    simpa only [hind] using hsc
  have hlog : log (1+(ε⁻¹)^2) = log (1+ε^2) - 2*log ε := by
    rw [show 1+(ε⁻¹)^2=(1+ε^2)/ε^2 by field_simp;ring,Real.log_div (by positivity) (by positivity),Real.log_pow]
    norm_num
  have hco : (∫ x in A(ε), referenceFunction x / ((|x| : ℝ) : ℂ)) = ((∫ x in A(ε),(1+x^2)⁻¹/|x| : ℝ) : ℂ) := by
    unfold referenceFunction
    simp_rw [← Complex.ofReal_div]
    exact integral_complex_ofReal
  rw [hco,hc,hlog]
  push_cast
  ring

end RealFourierLog

end

section

open MeasureTheory Set Filter Real
open scoped FourierTransform Topology
namespace RealFourierLog

private theorem scales_integral {g : ℝ → ℂ} (hg : Measurable g)
    (hd : Integrable (fun x ↦ g x / ((|x| : ℝ) : ℂ))) :
    (∫ a : ℝ in Ioi 0, ∫ x : ℝ, (((π*(a^2+x^2))⁻¹ : ℝ) : ℂ)*g x) =
      (∫ x : ℝ, g x / ((|x| : ℝ) : ℂ))/2 := by
  let J (x a : ℝ) : ℂ := (((π*(a^2+x^2))⁻¹ : ℝ) : ℂ)*g x
  have hJ : Measurable (Function.uncurry J) := by
    change Measurable (fun p : ℝ × ℝ ↦ (((π*(p.2^2+p.1^2))⁻¹ : ℝ) : ℂ)*g p.1)
    exact Measurable.mul (by fun_prop) (hg.comp measurable_fst)
  have inner (x : ℝ) (hx : x ≠ 0) :
      IntegrableOn (J x) (Ioi 0) ∧
      (∫ a : ℝ in Ioi 0, ‖J x a‖) = ‖g x / ((|x| : ℝ) : ℂ)‖/2 ∧
      (∫ a : ℝ in Ioi 0, J x a) = (g x / ((|x| : ℝ) : ℂ))/2 := by
    obtain ⟨hI,hv⟩ := scale_mass hx
    refine ⟨hI.ofReal.mul_const _,?_,?_⟩
    · have e (a : ℝ) : ‖J x a‖ = (π*(a^2+x^2))⁻¹ * ‖g x‖ := by
        dsimp only [J]
        rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
      simp_rw [e]
      rw [integral_mul_const,hv,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_abs]
      ring
    · unfold J
      rw [integral_mul_const,integral_complex_ofReal,hv]
      push_cast
      ring
  have hprod : Integrable (Function.uncurry J) (volume.prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff hJ.aestronglyMeasurable).2 ⟨?_,?_⟩
    · filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx using (inner x hx).1
    · refine (hd.norm.div_const 2).congr ?_
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx using (inner x hx).2.1.symm
  change (∫ a in Ioi 0, ∫ x : ℝ, J x a) = _
  rw [← integral_integral_swap hprod,← integral_div]
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx using (inner x hx).2.2

/-- Independent vanishing-at-zero real logarithmic Fourier identity. -/
theorem neg_integral_log_abs_mul_fourier_of_zero {g : ℝ → ℂ} (hg : Continuous g) (hgi : Integrable g)
    (hF : Integrable (𝓕 g)) (hFc : Continuous (𝓕 g)) (h0 : g 0 = 0)
    (hlog : Integrable (fun ξ : ℝ ↦ (log |ξ| : ℂ)*𝓕 g ξ))
    (hd : Integrable (fun x : ℝ ↦ g x / ((|x| : ℝ) : ℂ))) :
    -(∫ ξ : ℝ, (log |ξ| : ℂ)*𝓕 g ξ) = (∫ x : ℝ, g x / ((|x| : ℝ) : ℂ))/2 := by
  let c : ℝ := 2*π
  have hc : 0 < c := by dsimp [c];positivity
  let J (ξ a : ℝ) : ℂ := ((a⁻¹*(exp (-(c*|ξ|)*a)-exp (-c*a)) : ℝ) : ℂ)*𝓕 g ξ
  have hJ : Measurable (Function.uncurry J) := by
    unfold J Function.uncurry
    exact Measurable.mul (by fun_prop) (hFc.measurable.comp measurable_fst)
  have inner (ξ : ℝ) (hξ : ξ ≠ 0) :
      IntegrableOn (J ξ) (Ioi 0) ∧
      (∫ a : ℝ in Ioi 0, ‖J ξ a‖) = ‖(log |ξ| : ℂ)*𝓕 g ξ‖ ∧
      (∫ a : ℝ in Ioi 0, J ξ a) = -((log |ξ| : ℂ)*𝓕 g ξ) := by
    have hα : 0 < c*|ξ| := mul_pos hc (abs_pos.mpr hξ)
    obtain ⟨hI,hv⟩ := expFrullani hα hc
    have hA := absFrullani hα hc
    have hr : c/(c*|ξ|)=|ξ|⁻¹ := by field_simp
    rw [hr,Real.log_inv] at hv hA
    refine ⟨hI.ofReal.mul_const _,?_,?_⟩
    · have e (a : ℝ) : ‖J ξ a‖ = |a⁻¹*(exp (-(c*|ξ|)*a)-exp (-c*a))| *‖𝓕 g ξ‖ := by
        dsimp only [J]
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      simp_rw [e]
      rw [integral_mul_const,hA,abs_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    · unfold J
      rw [integral_mul_const,integral_complex_ofReal,hv,Complex.ofReal_neg,neg_mul]
  have hprod : Integrable (Function.uncurry J) (volume.prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff hJ.aestronglyMeasurable).2 ⟨?_,?_⟩
    · filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx using (inner x hx).1
    · refine hlog.norm.congr ?_
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx using (inner x hx).2.1.symm
  have hmass : ∫ ξ, 𝓕 g ξ = 0 := by
    have h := congrFun (hg.fourierInv_fourier_eq hgi hF) 0
    rw [Real.fourierInv_eq'] at h
    simpa [h0] using h
  have hfirst : -(∫ ξ : ℝ, (log |ξ| : ℂ)*𝓕 g ξ) = ∫ ξ, ∫ a in Ioi 0, J ξ a := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx using (inner x hx).2.2.symm
  rw [hfirst,integral_integral_swap hprod,← scales_integral hg.measurable hd]
  refine setIntegral_congr_fun measurableSet_Ioi fun a (ha : 0<a) ↦ ?_
  have hp (y : ℝ) : J y a = (a⁻¹ : ℝ) *
      (exponentialWeight a y * 𝓕 g y - (exp (-c*a) : ℂ)*𝓕 g y) := by
    dsimp only [J,exponentialWeight,c]
    rw [show -(2*π*|y|)*a = -2*π*a*|y| by ring]
    push_cast
    ring
  have hL : Integrable (fun y ↦ exponentialWeight a y * 𝓕 g y) :=
    hF.bdd_mul (f := exponentialWeight a) (c := 1) (show Continuous (exponentialWeight a) by unfold exponentialWeight; fun_prop).aestronglyMeasurable
      (.of_forall fun y ↦ by rw [exponentialWeight,Complex.norm_real,Real.norm_of_nonneg (exp_pos _).le,exp_le_one_iff];nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) pi_pos.le) ha.le) (abs_nonneg y)])
  have hdual : (∫ y : ℝ, exponentialWeight a y * 𝓕 g y) = ∫ x : ℝ, g x * poissonDensity a x := by
    have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner hgi (integrable_exponentialWeight ha)
    rw [flip_innerₗ] at h
    change (∫ ξ, 𝓕 g ξ • exponentialWeight a ξ) = ∫ x, g x • 𝓕 (exponentialWeight a) x at h
    simpa only [smul_eq_mul,mul_comm (exponentialWeight a _) _,fourier_exponentialWeight ha] using h
  simp_rw [hp]
  rw [integral_const_mul,integral_sub hL (hF.const_mul _),integral_const_mul,hmass,mul_zero,sub_zero,hdual,← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    dsimp only [poissonDensity];push_cast
    field_simp [Complex.ofReal_ne_zero.mpr ha.ne']

end RealFourierLog

end

section

open MeasureTheory Set Real Filter
open scoped Topology FourierTransform SchwartzMap
namespace RealFourierLog
set_option quotPrecheck false
local notation "A(" ε ")" => {x : ℝ | ε ≤ |x|}

private theorem bounded_tail_cover (ε : ℝ) : A(ε) ∪ Ioc (-ε-1) (ε+1) = univ := by
  ext x
  simp only [mem_union,mem_ofPred_eq,mem_Ioc,mem_univ,iff_true]
  by_cases h : ε ≤ |x|
  · exact Or.inl h
  · exact Or.inr ⟨by linarith [(abs_lt.mp (lt_of_not_ge h)).1],by linarith [(abs_lt.mp (lt_of_not_ge h)).2]⟩

private theorem log_schwartz (v : 𝓢(ℝ, ℂ)) : Integrable (fun x : ℝ ↦ (log |x| : ℂ)*v x) := by
  let C := SchwartzMap.seminorm ℝ 0 0 v
  have hm : Measurable (fun x : ℝ ↦ (log |x| : ℂ)*v x) :=
    (Complex.measurable_ofReal.comp (Real.measurable_log.comp continuous_abs.measurable)).mul v.continuous.measurable
  have ho : IntegrableOn (fun x : ℝ ↦ (log |x| : ℂ)*v x) A(1) := by
    refine (v.integrable_pow_mul volume 1).integrableOn.mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_le measurable_const continuous_abs.measurable)] with x (hx : 1 ≤ |x|)
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.log_nonneg hx),pow_one,Real.norm_eq_abs]
    gcongr
    linarith [Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hx)]
  have hn : IntegrableOn (fun x : ℝ ↦ (log |x| : ℂ)*v x) (Ioc (-1-1 : ℝ) (1+1)) := by
    have hlog := (intervalIntegral.intervalIntegrable_log' (a := -1-1) (b := 1+1)).1
    refine (hlog.norm.mul_const C).mono' hm.aestronglyMeasurable (.of_forall fun x ↦ ?_)
    rw [norm_mul,Complex.norm_real,Real.log_abs]
    exact mul_le_mul_of_nonneg_left (v.norm_le_seminorm ℝ x) (norm_nonneg _)
  exact integrableOn_univ.mp (bounded_tail_cover 1 ▸ ho.union hn)

private theorem corrected_integrable (v : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ ↦ (v x-v 0*referenceFunction x)/((|x| : ℝ) : ℂ)) := by
  let g (x : ℝ) := v x-v 0*referenceFunction x
  have hc : Continuous g := by dsimp [g,referenceFunction];fun_prop (disch := intro x;positivity)
  have hi : Integrable g := v.integrable.sub (integrable_referenceFunction.const_mul _)
  have ht : IntegrableOn (fun x ↦ g x/((|x| : ℝ) : ℂ)) A(1) := cut_integrable hi hc.measurable zero_lt_one
  let C := SchwartzMap.seminorm ℝ 0 1 v
  have lip (x : ℝ) : ‖v x-v 0‖≤C*|x| := by
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := v) (s := univ) (C := C)
      (fun z _ ↦ v.differentiableAt) (fun z _ ↦ ?_) convex_univ (mem_univ 0) (mem_univ x)
    · simpa [Real.norm_eq_abs] using h
    · rw [← norm_iteratedFDeriv_one];exact v.norm_iteratedFDeriv_le_seminorm ℝ 1 z
  have hR (x : ℝ) : ‖1-referenceFunction x‖≤|x| := by
    have h : 1-(1+x^2)⁻¹=x^2/(1+x^2) := by field_simp [show 1+x^2≠0 by positivity];ring
    change ‖(1:ℂ)-↑((1+x^2)⁻¹ : ℝ)‖≤_
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,h,Real.norm_of_nonneg (by positivity),
      div_le_iff₀ (by positivity)]
    have hx := sq_nonneg (|x|-1)
    rw [← sq_abs x]
    nlinarith [mul_nonneg (abs_nonneg x) hx,sq_nonneg |x|]
  have hn : IntegrableOn (fun x ↦ g x/((|x| : ℝ) : ℂ)) (Ioc (-1-1 : ℝ) (1+1)) := by
    refine (integrableOn_const (C := C+‖v 0‖) measure_Ioc_lt_top.ne).mono'
      (hc.measurable.div (Complex.measurable_ofReal.comp continuous_abs.measurable)).aestronglyMeasurable ?_
    exact .of_forall fun x ↦ by
      rcases eq_or_ne x 0 with rfl|hx
      · simp [C,add_nonneg (apply_nonneg _ _) (norm_nonneg _)]
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_abs,div_le_iff₀ (abs_pos.mpr hx),add_mul]
      have e : g x=(v x-v 0)+v 0*(1-referenceFunction x) := by dsimp only [g];ring
      rw [e]
      exact (norm_add_le _ _).trans (add_le_add (lip x) (by rw [norm_mul];gcongr;exact hR x))
  exact integrableOn_univ.mp (bounded_tail_cover 1 ▸ ht.union hn)

private theorem fourier_sub_scaled {f r : ℝ → ℂ} (hf : Integrable f) (hr : Integrable r) (c : ℂ) :
    𝓕 (fun x ↦ f x-c*r x) = (fun ξ ↦ 𝓕 f ξ-c*𝓕 r ξ) := by
  have ha := VectorFourier.fourierIntegral_add (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf (hr.smul (-c))
  have hs := VectorFourier.fourierIntegral_const_smul Real.fourierChar volume (innerₗ ℝ) r (-c)
  change 𝓕 (f+(-c) • r) = 𝓕 f+𝓕 ((-c) • r) at ha
  change 𝓕 ((-c) • r) = (-c) • 𝓕 r at hs
  rw [hs] at ha
  have he : (fun x ↦ f x-c*r x)=f+(-c) • r := by funext x; change _=f x+(-c)*r x;ring
  rw [he,ha];funext ξ;change 𝓕 f ξ+(-c)*𝓕 r ξ=_;ring

/-- The real finite part selected by symmetric truncation, with every integral constructed
from the ordinary Fourier transform. -/
theorem real_log_cutoff (f : 𝓢(ℝ, ℂ)) :
    Integrable (fun ξ : ℝ ↦ (log |ξ| : ℂ)*𝓕 (f : ℝ → ℂ) ξ) ∧
    (∀ ε > (0 : ℝ), IntegrableOn (fun x : ℝ ↦ f x / ((|x| : ℝ) : ℂ)) A(ε)) ∧
    Tendsto (fun ε : ℝ ↦ (1/2 : ℂ)*(∫ x in A(ε), f x / ((|x| : ℝ) : ℂ)) + f 0*(log ε : ℂ))
      (𝓝[>] 0) (𝓝 (-(∫ ξ : ℝ, (log |ξ| : ℂ)*𝓕 (f : ℝ → ℂ) ξ) -
        ((eulerMascheroniConstant+log (2*π) : ℝ) : ℂ)*f 0)) := by
  let g (x : ℝ) := f x-f 0*referenceFunction x
  let D (x : ℝ) := g x/((|x| : ℝ) : ℂ)
  let V : ℝ → ℂ := 𝓕 (f : ℝ → ℂ)
  let W : ℝ → ℂ := 𝓕 referenceFunction
  have hg : Continuous g := by dsimp [g,referenceFunction];fun_prop (disch := intro x;positivity)
  have hgi : Integrable g := f.integrable.sub (integrable_referenceFunction.const_mul _)
  have hD : Integrable D := corrected_integrable f
  have hV : Integrable (fun ξ ↦ (log |ξ| : ℂ)*V ξ) := by
    simpa only [V,SchwartzMap.fourier_coe] using log_schwartz (𝓕 f)
  have hcut (ε : ℝ) (hε : 0<ε) := cut_integrable f.integrable f.continuous.measurable hε
  refine ⟨hV,hcut,?_⟩
  have hG : 𝓕 g = fun y ↦ V y-f 0*W y := fourier_sub_scaled f.integrable integrable_referenceFunction (f 0)
  have hFi : Integrable V := by simpa only [V,SchwartzMap.fourier_coe] using (𝓕 f).integrable (μ := volume)
  have hWi : Integrable W := by
    simp_rw [show W=fun ξ ↦ (π : ℂ)*exponentialWeight 1 ξ from funext fourier_referenceFunction]
    exact (integrable_exponentialWeight one_pos).const_mul _
  have hGF : Integrable (𝓕 g) := by rw [hG]; exact hFi.sub (hWi.const_mul _)
  have hW := reference_log.1
  have hdiff (y : ℝ) : (log |y| : ℂ)*𝓕 g y = (log |y| : ℂ)*V y - f 0*((log |y| : ℂ)*W y) := by rw [hG];ring
  have hlog : Integrable (fun ξ : ℝ ↦ (log |ξ| : ℂ)*𝓕 g ξ) := by
    simp_rw [hdiff];exact hV.sub (hW.const_mul _)
  have hx := neg_integral_log_abs_mul_fourier_of_zero hg hgi hGF (VectorFourier.fourierIntegral_continuous (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hgi) (by simp [g,referenceFunction]) hlog hD
  simp_rw [hdiff] at hx
  rw [integral_sub hV (hW.const_mul _),integral_const_mul] at hx
  have hWV : (∫ ξ : ℝ, (log |ξ| : ℂ)*W ξ) = -((eulerMascheroniConstant+log (2*π) : ℝ) : ℂ) := reference_log.2
  rw [hWV] at hx
  change -(_-_) = (∫ x : ℝ, D x)/2 at hx
  have hm (ε : ℝ) : MeasurableSet A(ε) := measurableSet_le measurable_const continuous_abs.measurable
  have hlim : Tendsto (fun ε : ℝ ↦ ∫ x in A(ε), D x) (𝓝[>] 0) (𝓝 (∫ x, D x)) := by
    simp_rw [← integral_indicator (hm _)]
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖D x‖)
      (.of_forall fun ε ↦ hD.aestronglyMeasurable.indicator (hm ε))
      (.of_forall fun _ ↦ .of_forall fun _ ↦ norm_indicator_le_norm_self _ _) hD.norm
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x h
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds (abs_pos.mpr h))] with ε hε using
      (indicator_of_mem (s := A(ε)) hε.le D).symm
  have hc0 : Tendsto (fun ε : ℝ ↦ (log (1+ε^2) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h : ContinuousAt (fun ε : ℝ ↦ (log (1+ε^2) : ℂ)) 0 := by fun_prop (disch := norm_num)
    simpa using h.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have hs : Tendsto (fun ε : ℝ ↦ (1/2 : ℂ)*(∫ x in A(ε), D x) + (f 0/2)*(log (1+ε^2) : ℂ))
      (𝓝[>] 0) (𝓝 ((1/2 : ℂ)*(∫ x, D x))) := by
    simpa using (hlim.const_mul (1/2 : ℂ)).add (hc0.const_mul (f 0/2))
  change Tendsto _ _ (𝓝 (-(∫ ξ : ℝ, (log |ξ| : ℂ)*V ξ) - _))
  convert hs.congr' ?_ using 1
  · congr 1
    linear_combination hx
  · filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with ε (hε : 0<ε)
    have hRcut := cut_integrable integrable_referenceFunction (by unfold referenceFunction;fun_prop) hε
    have he (x : ℝ) : D x = f x / ((|x| : ℝ) : ℂ) - f 0*(referenceFunction x / ((|x| : ℝ) : ℂ)) := by dsimp [D,g];ring
    simp_rw [he]
    rw [integral_sub (hcut ε hε) (hRcut.const_mul _),integral_const_mul,← reference_cutoff hε]
    ring

end RealFourierLog

end
