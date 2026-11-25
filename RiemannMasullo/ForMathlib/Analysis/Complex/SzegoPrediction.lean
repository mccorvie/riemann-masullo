module

public import RiemannMasullo.ForMathlib.Analysis.Complex.HardyBoundaryLogMean
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# The Szegő prediction infimum for a disk-algebra function

Approximate a truncated continuous logarithm on the unit circle by real parts of
analytic polynomials. Exponentiating and approximating again yields polynomial
predictors of constant coefficient one. Optimal complex rescaling gives the distance
from the constant one to the polynomial multiples in boundary mean square.

Reference: G. Szegő, *Beiträge zur Theorie der Toeplitzschen Formen. I*,
Math. Z. **6** (1920), 167–202, doi:10.1007/BF01199955.
-/

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set Metric Real Finset
open scoped Topology ComplexConjugate

namespace HardySzego

private theorem fourier_nat (x : AddCircle (1:ℝ)) (n : ℕ) :
    fourier (n:ℤ) x = (fourier 1 x)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ,fourier_add,ih,pow_succ]

private theorem realPart_on_span {v : C(AddCircle (1:ℝ),ℂ)}
    (hv : v ∈ Submodule.span ℂ (Set.range (@fourier (1:ℝ)))) :
    ∀ a : ℂ, ∃ h : Polynomial ℂ, ∀ x : AddCircle (1:ℝ),
      (h.eval (fourier 1 x)).re = (a*v x).re := by
  induction hv using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨i,rfl⟩ := hu
    intro a
    cases i with
    | ofNat n =>
      refine ⟨Polynomial.C a*Polynomial.X^n,fun x ↦ ?_⟩
      change _ = (a*fourier (n:ℤ) x).re
      simp only [fourier_nat,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_pow]
    | negSucc n =>
      refine ⟨Polynomial.C (conj a)*Polynomial.X^(n+1),fun x ↦ ?_⟩
      have he : (Int.negSucc n) = -((n+1:ℕ):ℤ) := by omega
      simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,he,
        fourier_neg,fourier_nat]
      rw [← Complex.conj_re (a*conj ((fourier 1 x)^(n+1))),map_mul,starRingEnd_self_apply]
  | zero =>
    intro a
    exact ⟨0,by simp⟩
  | add u v _ _ hu hv =>
    intro a
    obtain ⟨p,hp⟩ := hu a
    obtain ⟨q,hq⟩ := hv a
    exact ⟨p+q,fun x ↦ by simp only [Polynomial.eval_add,Complex.add_re,hp,hq,ContinuousMap.add_apply,mul_add]⟩
  | smul b v _ hv =>
    intro a
    obtain ⟨h,hh⟩ := hv (a*b)
    exact ⟨h,fun x ↦ by simpa [mul_assoc] using hh x⟩

/-- Uniform approximation on the genuine boundary circle by real parts of analytic polynomials. -/
theorem exists_polynomial_re_approx (g : ℂ → ℝ) (hg : ContinuousOn g (sphere 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : Polynomial ℂ, ∀ z ∈ sphere (0:ℂ) 1, |(h.eval z).re - g z| < ε := by
  let G : C(AddCircle (1:ℝ),ℂ) := ⟨fun x ↦ (g (fourier 1 x):ℂ),
    Complex.continuous_ofReal.comp (hg.comp_continuous (fourier 1).continuous
      (fun x ↦ (mem_sphere_zero_iff_norm).mpr (Circle.norm_coe _)))⟩
  have hmem : G ∈ closure (Submodule.span ℂ (Set.range (@fourier (1:ℝ))) :
      Set C(AddCircle (1:ℝ),ℂ)) := by
    change G ∈ (Submodule.span ℂ (Set.range (@fourier (1:ℝ)))).topologicalClosure
    rw [span_fourier_closure_eq_top]
    trivial
  obtain ⟨v,hv,hG⟩ := Metric.mem_closure_iff.mp hmem ε hε
  obtain ⟨h,hh⟩ := realPart_on_span hv 1
  refine ⟨h,fun z hz ↦ ?_⟩
  let zz : Circle := ⟨z,hz⟩
  obtain ⟨x,hx⟩ := (AddCircle.homeomorphCircle (T := (1:ℝ)) one_ne_zero).surjective zz
  have hzx : fourier 1 x = z := by
    rw [fourier_one,← AddCircle.homeomorphCircle_apply (T := (1:ℝ)) one_ne_zero,hx]
  have he : (h.eval z).re = (v x).re := by simpa [hzx] using hh x
  rw [he,← hzx]
  have hd := ContinuousMap.norm_coe_le_norm (v-G) x
  have hvg : ‖v-G‖ < ε := by simpa only [dist_eq_norm,norm_sub_rev] using hG
  exact (Complex.abs_re_le_norm (v x-G x)).trans_lt (hd.trans_lt hvg)

/-- Partial Taylor sums approximate exp(Q(z)) uniformly on a compact circle. When Q(0)=0
the approximating polynomial has constant coefficient exactly one. -/
theorem exists_exp_polynomial (Q : Polynomial ℂ) (h0 : Q.eval 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, p.eval 0 = 1 ∧
      ∀ z ∈ sphere (0:ℂ) 1, ‖p.eval z - Complex.exp (Q.eval z)‖ < ε := by
  let w (j : ℕ) (z : ℂ) := Q.eval z ^ j / (j.factorial:ℂ)
  obtain ⟨B,hB⟩ := (isCompact_sphere (0:ℂ) 1).exists_bound_of_continuousOn Q.continuous.continuousOn
  have hs := (NormedSpace.expSeries_div_hasSum_exp B).summable
  have hdom (j : ℕ) (z : ℂ) (hz : z ∈ sphere (0:ℂ) 1) : ‖w j z‖ ≤ B^j/(j.factorial:ℝ) := by
    simp only [w,norm_div,norm_pow,Complex.norm_natCast]
    gcongr
    exact hB z hz
  have huni := tendstoUniformlyOn_tsum_nat hs hdom
  have he := (Metric.tendstoUniformlyOn_iff.mp huni ε hε).and (eventually_ge_atTop 1)
  obtain ⟨N,hN,hN1⟩ := he.exists
  let p : Polynomial ℂ := ∑ j ∈ range N, Polynomial.C ((j.factorial:ℂ)⁻¹)*Q^j
  have hp (z : ℂ) : p.eval z = ∑ j ∈ range N, w j z := by
    simp [p,w,Polynomial.eval_finsetSum,div_eq_mul_inv,mul_comm]
  refine ⟨p,?_,fun z hz ↦ ?_⟩
  · rw [hp,Finset.sum_eq_single 0]
    · simp [w]
    · intro j hj hj0
      simp [w,h0,zero_pow hj0]
    · simp [Nat.lt_of_lt_of_le Nat.zero_lt_one hN1]
  · rw [hp,Complex.exp_eq_exp_ℂ,← (NormedSpace.expSeries_div_hasSum_exp (Q.eval z)).tsum_eq]
    simpa only [dist_eq_norm,norm_sub_rev] using hN z hz

end HardySzego

end

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set Metric Real
open scoped Topology

namespace HardySzego

local notation "μθ" => volume.restrict (Ioc (0:ℝ) (2*Real.pi))

private def tol (n : ℕ) : ℝ := ((n:ℝ)+1)⁻¹

private theorem tol_pos (n : ℕ) : 0 < tol n := by dsimp [tol]; positivity

private theorem tol_le_one (n : ℕ) : tol n ≤ 1 := by
  dsimp [tol]; apply inv_le_one_of_one_le₀; linarith [Nat.cast_nonneg (α := ℝ) n]

private theorem tol_tendsto : Tendsto tol atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun n ↦ by linarith) tendsto_natCast_atTop_atTop)

private def clipped (F : ℂ → ℂ) (n : ℕ) (z : ℂ) := Real.log (max (tol n) ‖F z‖)

private theorem clipped_continuous {F : ℂ → ℂ} (hF : ContinuousOn F (sphere 0 1)) (n : ℕ) :
    ContinuousOn (clipped F n) (sphere 0 1) :=
  (continuousOn_const.sup hF.norm).log (fun _ _ ↦ ((tol_pos n).trans_le (le_max_left _ _)).ne')

/-- Truncating the boundary modulus from below recovers the genuine logarithmic mean.
The exceptional zero set is omitted only in the almost-everywhere application of domination. -/
private theorem clipped_tendsto {F : ℂ → ℂ} (hc : ContinuousOn F (sphere 0 1))
    (hlog : CircleIntegrable (fun z ↦ Real.log ‖F z‖) 0 1)
    (hne : ∀ᵐ θ : ℝ ∂μθ, F (circleMap 0 1 θ) ≠ 0) :
    Tendsto (fun n ↦ circleAverage (clipped F n) 0 1) atTop
      (𝓝 (circleAverage (fun z ↦ Real.log ‖F z‖) 0 1)) := by
  let f (θ : ℝ) := F (circleMap 0 1 θ)
  have hcli (n : ℕ) := (clipped_continuous hc n).comp_continuous (continuous_circleMap 0 1)
    (fun θ ↦ by simp)
  have hbi := ((intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hlog).norm
  have hD := tendsto_integral_of_dominated_convergence (μ := μθ) (fun θ ↦ ‖Real.log ‖f θ‖‖)
    (fun n ↦ (hcli n).aestronglyMeasurable) hbi (fun n ↦ hne.mono fun θ hθ ↦ by
      change ‖Real.log (max (tol n) ‖f θ‖)‖ ≤ ‖Real.log ‖f θ‖‖
      by_cases hs : tol n ≤ ‖f θ‖
      · rw [max_eq_right hs]
      · rw [max_eq_left (le_of_not_ge hs),Real.norm_eq_abs,Real.norm_eq_abs,
          abs_of_nonpos (Real.log_nonpos (tol_pos n).le (tol_le_one n)),
          abs_of_nonpos (Real.log_nonpos (norm_nonneg _) ((le_of_not_ge hs).trans (tol_le_one n)))]
        exact neg_le_neg (Real.log_le_log (norm_pos_iff.mpr hθ) (le_of_not_ge hs)))
    (hne.mono fun θ hθ ↦ by
      apply tendsto_const_nhds.congr'
      filter_upwards [tol_tendsto.eventually_lt_const (norm_pos_iff.mpr hθ)] with n hn
      exact (congrArg Real.log (max_eq_right hn.le)).symm)
  simp only [circleAverage_def,intervalIntegral.integral_of_le Real.two_pi_pos.le]
  exact tendsto_const_nhds.smul hD

private theorem mean_re_eval (h : Polynomial ℂ) :
    circleAverage (fun z ↦ (h.eval z).re) 0 1 = (h.eval 0).re := by
  have hd := (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) h).differentiableOn
  have hc : CircleIntegrable (fun z ↦ h.eval z) 0 1 :=
    (differentiableOn_univ.mp hd).continuous.continuousOn.circleIntegrable'
  have hm := ((differentiableOn_univ.mp hd).diffContOnCl (s := ball (0:ℂ) |(1:ℝ)|)).circleAverage
  exact (Complex.reCLM.circleAverage_comp_comm hc).trans (congrArg Complex.re hm)

/-- A center-normalized polynomial whose weighted modulus is small on the entire circle. -/
private theorem predictor_one_stage {F : ℂ → ℂ} (hc : ContinuousOn F (sphere 0 1))
    (B : ℝ) (hB : ∀ z ∈ sphere (0:ℂ) 1, ‖F z‖ ≤ B) (n : ℕ) :
    ∃ p : Polynomial ℂ, p.eval 0 = 1 ∧ ∀ z ∈ sphere (0:ℂ) 1, ‖F z*p.eval z‖ ≤
      Real.exp (circleAverage (clipped F n) 0 1 + 2*tol n)+B*tol n := by
  let g := clipped F n
  have hg := clipped_continuous hc n
  obtain ⟨h,hh⟩ := exists_polynomial_re_approx g hg (tol_pos n)
  have hpi : CircleIntegrable (fun z ↦ (h.eval z).re) 0 1 := (Complex.continuous_re.comp h.continuous).continuousOn.circleIntegrable'
  have hgi : CircleIntegrable g 0 1 := hg.circleIntegrable zero_le_one
  have hcenter : (h.eval 0).re ≤ circleAverage g 0 1+tol n := by
    rw [← mean_re_eval,← circleAverage_const (tol n) 0 1,← circleAverage_fun_add hgi (circleIntegrable_const _ _ _)]
    apply circleAverage_mono hpi (hgi.add (circleIntegrable_const _ _ _))
    intro z hz
    have h' := (abs_lt.mp (hh z (by simpa using hz))).2
    change (h.eval z).re ≤ g z+tol n
    linarith
  let Q := Polynomial.C (h.eval 0)-h
  have hQ z : Q.eval z = h.eval 0-h.eval z := by simp [Q]
  obtain ⟨p,hp,happrox⟩ := exists_exp_polynomial Q (by simp [Q]) (tol_pos n)
  refine ⟨p,hp,fun z hz ↦ ?_⟩
  have hre := (abs_lt.mp (hh z hz)).1
  have hdom : ‖F z‖ ≤ Real.exp (g z) := by
    change ‖F z‖ ≤ Real.exp (Real.log (max _ _))
    rw [Real.exp_log ((tol_pos n).trans_le (le_max_left _ _))]
    exact le_max_right _ _
  have hExp : ‖F z*Complex.exp (Q.eval z)‖ ≤ Real.exp (circleAverage g 0 1+2*tol n) := by
    rw [norm_mul,Complex.norm_exp]
    calc
      _ ≤ Real.exp (g z)*Real.exp (Q.eval z).re := mul_le_mul_of_nonneg_right hdom (Real.exp_pos _).le
      _ ≤ _ := by rw [← Real.exp_add,hQ,Complex.sub_re]; apply Real.exp_le_exp.mpr; linarith
  have herr : ‖F z*(p.eval z-Complex.exp (Q.eval z))‖ ≤ B*tol n := by
    rw [norm_mul]
    exact mul_le_mul (hB z hz) (happrox z hz).le (norm_nonneg _) ((norm_nonneg _).trans (hB z hz))
  calc
    _ = ‖F z*Complex.exp (Q.eval z)+F z*(p.eval z-Complex.exp (Q.eval z))‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le ..).trans (add_le_add hExp herr)

/-- Szegő predictors with pₙ(0)=1. The weighted mean-square energies approach the
geometric mean of the squared modulus, even with zeros on the boundary. -/
theorem exists_normalized_predictors {F : ℂ → ℂ} (hc : ContinuousOn F (sphere 0 1))
    (hlog : CircleIntegrable (fun z ↦ Real.log ‖F z‖) 0 1)
    (hne : ∀ᵐ θ : ℝ ∂μθ, F (circleMap 0 1 θ) ≠ 0) :
    ∃ p : ℕ → Polynomial ℂ, (∀ n, (p n).eval 0 = 1) ∧
      Tendsto (fun n ↦ circleAverage (fun z ↦ ‖F z*(p n).eval z‖^2) 0 1) atTop
        (𝓝 (Real.exp (2*circleAverage (fun z ↦ Real.log ‖F z‖) 0 1))) := by
  obtain ⟨B,hB⟩ := (isCompact_sphere (0:ℂ) 1).exists_bound_of_continuousOn hc
  choose p hp hb using fun n ↦ predictor_one_stage hc B hB n
  let m := circleAverage (fun z ↦ Real.log ‖F z‖) 0 1
  let U (n : ℕ) := Real.exp (circleAverage (clipped F n) 0 1+2*tol n)+B*tol n
  have hU : Tendsto U atTop (𝓝 (Real.exp m)) := by
    have h := ((Real.continuous_exp.tendsto _).comp ((clipped_tendsto hc hlog hne).add (tol_tendsto.const_mul 2))).add
      (tol_tendsto.const_mul B)
    simpa [U,m,Function.comp_def] using h
  have hlo (n : ℕ) : Real.exp (2*m) ≤ circleAverage (fun z ↦ ‖F z*(p n).eval z‖^2) 0 1 := by
    have hi := ((hc.mul (p n).continuous.continuousOn).norm.pow 2).circleIntegrable zero_le_one
    simpa [hp] using HardyBoundary.scale_le_product_energy one_pos F (p n) hlog hne hi
  have hhi (n : ℕ) : circleAverage (fun z ↦ ‖F z*(p n).eval z‖^2) 0 1 ≤ (U n)^2 := by
    apply circleAverage_mono_on_of_le_circle (((hc.mul (p n).continuous.continuousOn).norm.pow 2).circleIntegrable zero_le_one)
    intro z hz
    exact pow_le_pow_left₀ (norm_nonneg _) (hb n z (by simpa using hz)) 2
  have hlim : Tendsto (fun n ↦ (U n)^2) atTop (𝓝 (Real.exp (2*m))) := by
    simpa only [two_mul,Real.exp_add,sq] using hU.pow 2
  exact ⟨p,hp,tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hlo hhi⟩

/-- The scalar Szegő variational formula, expressed as an infimum over polynomials
with constant coefficient one. -/
theorem prediction_infimum {F : ℂ → ℂ} (hc : ContinuousOn F (sphere 0 1))
    (hlog : CircleIntegrable (fun z ↦ Real.log ‖F z‖) 0 1)
    (hne : ∀ᵐ θ : ℝ ∂μθ, F (circleMap 0 1 θ) ≠ 0) :
    sInf {v : ℝ | ∃ p : Polynomial ℂ, p.eval 0 = 1 ∧ v = circleAverage (fun z ↦ ‖F z*p.eval z‖^2) 0 1} =
      Real.exp (2*circleAverage (fun z ↦ Real.log ‖F z‖) 0 1) := by
  obtain ⟨p,hp,ht⟩ := exists_normalized_predictors hc hlog hne
  apply le_antisymm
  · apply ge_of_tendsto ht
    apply Eventually.of_forall
    intro n
    refine csInf_le ⟨0,?_⟩ ⟨p n,hp n,rfl⟩
    rintro _ ⟨q,hq,rfl⟩
    exact circleAverage_nonneg_of_nonneg (fun _ _ ↦ sq_nonneg _)
  · refine le_csInf ?_ ?_
    · exact ⟨_,p 0,hp 0,rfl⟩
    · rintro _ ⟨q,hq,rfl⟩
      have hi := ((hc.mul q.continuous.continuousOn).norm.pow 2).circleIntegrable zero_le_one
      simpa [hq] using HardyBoundary.scale_le_product_energy one_pos F q hlog hne hi

end HardySzego

end

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set Metric Real HardyBoundary
open scoped Topology ComplexConjugate

namespace HardySzego

private theorem optimal_scale (A : ℂ) (hA : A ≠ 0) (m : ℝ) :
    let E := Real.exp (2*m)
    let scale := conj A / (E : ℂ)
    1-2*(A*scale).re+‖scale‖^2*E = 1-Real.exp (-2*(m-Real.log ‖A‖)) := by
  let E := Real.exp (2*m)
  have he : 0 < E := Real.exp_pos _
  have heq : Real.exp (-2*(m-Real.log ‖A‖)) = ‖A‖^2/E := by
    rw [show -2*(m-Real.log ‖A‖) = (Real.log ‖A‖+Real.log ‖A‖) + -(2*m) by ring,
      Real.exp_add,Real.exp_neg,Real.exp_add,Real.exp_log (norm_pos_iff.mpr hA)]
    dsimp [E]; ring
  change 1-2*(A*(conj A/(E:ℂ))).re + ‖conj A/(E:ℂ)‖^2*E = _
  rw [← mul_div_assoc,Complex.mul_conj']
  have hreal : (((‖A‖:ℂ)^2)/(E:ℂ)).re = ‖A‖^2/E := by norm_cast
  rw [hreal,norm_div,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs,abs_of_pos he,heq]
  field_simp
  ring

private theorem energy_scale (F : ℂ → ℂ) (p : Polynomial ℂ) (a : ℂ) :
    circleAverage (fun z ↦ ‖F z*(Polynomial.C a*p).eval z‖^2) 0 1 =
      ‖a‖^2*circleAverage (fun z ↦ ‖F z*p.eval z‖^2) 0 1 := by
  have he z : F z*(Polynomial.C a*p).eval z = a*(F z*p.eval z) := by simp; ring
  simp_rw [he,norm_mul,mul_pow]
  exact Real.circleAverage_fun_smul (a := ‖a‖^2) (f := fun z ↦ ‖F z‖^2*‖p.eval z‖^2)

/-- For a disk-algebra function nonzero at the center, polynomial residuals attain the
one-sided logarithmic prediction bound in the limit. -/
theorem exists_residual_sequence {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1))
    (h0 : F 0 ≠ 0) :
    ∃ q : ℕ → Polynomial ℂ,
      Tendsto (fun n ↦ circleAverage (fun z ↦ ‖1-F z*(q n).eval z‖^2) 0 1) atTop
        (𝓝 (1-Real.exp (-2*logGap F))) := by
  have hclosed := hF.continuousOn
  rw [closure_ball _ one_ne_zero] at hclosed
  obtain ⟨hne,hi,_⟩ := disk_log_integrable hF h0
  obtain ⟨p,hp,ht⟩ := exists_normalized_predictors (hclosed.mono sphere_subset_closedBall) hi hne
  let m := circleAverage (fun z ↦ Real.log ‖F z‖) 0 1
  let a := conj (F 0) / (Real.exp (2*m) : ℂ)
  let q (n : ℕ) := Polynomial.C a * p n
  refine ⟨q,?_⟩
  have hval (n : ℕ) : circleAverage (fun z ↦ ‖1-F z*(q n).eval z‖^2) 0 1 =
      1-2*(F 0*a).re+‖a‖^2*circleAverage (fun z ↦ ‖F z*(p n).eval z‖^2) 0 1 := by
    have hdiff : Differentiable ℂ (fun z ↦ (q n).eval z) :=
      differentiableOn_univ.mp (AnalyticOnNhd.eval_polynomial (q n)).differentiableOn
    have hprod : DiffContOnCl ℂ (fun z ↦ F z*(q n).eval z) (ball 0 |(1:ℝ)|) := by
      rw [abs_one]
      exact hF.smul hdiff.diffContOnCl
    have hc := hprod.continuousOn
    rw [closure_ball _ (by norm_num : |(1:ℝ)| ≠ 0)] at hc
    have hs := hc.mono sphere_subset_closedBall
    rw [residual_energy hs.circleIntegrable' (hs.norm.pow 2).circleIntegrable',hprod.circleAverage]
    rw [show (q n).eval 0 = a by simp [q,hp]]
    exact congrArg (fun v : ℝ ↦ 1-2*(F 0*a).re+v) (energy_scale F (p n) a)
  simp_rw [hval]
  have hlim := tendsto_const_nhds (x := 1-2*(F 0*a).re) |>.add (ht.const_mul (‖a‖^2))
  exact (optimal_scale (F 0) h0 m) ▸ hlim

/-- The full disk-algebra distance in normalized boundary energy. -/
theorem boundary_infimum {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1)) (h0 : F 0 ≠ 0) :
    sInf (Set.range fun p : Polynomial ℂ ↦ circleAverage (fun z ↦ ‖1-F z*p.eval z‖^2) 0 1) =
      1-Real.exp (-2*logGap F) := by
  obtain ⟨q,ht⟩ := exists_residual_sequence hF h0
  have hb : BddBelow (Set.range fun p : Polynomial ℂ ↦ circleAverage (fun z ↦ ‖1-F z*p.eval z‖^2) 0 1) :=
    ⟨0,by rintro _ ⟨p,rfl⟩; exact circleAverage_nonneg_of_nonneg (fun _ _ ↦ sq_nonneg _)⟩
  apply le_antisymm
  · exact ge_of_tendsto ht (Eventually.of_forall fun n ↦ csInf_le hb ⟨q n,rfl⟩)
  · refine le_csInf (Set.range_nonempty _) ?_
    rintro _ ⟨p,rfl⟩
    exact (disk_boundary_lower hF h0).2 p

end HardySzego

end
