module

public import RiemannMasullo.ForMathlib.Analysis.Complex.HardyBoundaryLogMean
public import RiemannMasullo.ForMathlib.Analysis.Complex.HardyCoefficientParseval
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.HardyLeastSquares
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# A finite upper certificate for the Hardy logarithmic gap

The coefficient norm and the boundary mean give an explicit lower bound for every
polynomial residual. An upper bound below one for a corrected finite residual can
therefore be inverted to bound the boundary logarithmic gap.
-/

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set Metric HardyTable Real
open scoped Topology

namespace HardyBoundary

private theorem summable_norm_of_derivative {c : H} {D : ℝ} (hD : DerivativeBound c D) :
    Summable (fun j : ℕ ↦ ‖c j‖) := by
  have hw := (summable_nat_add_iff 1).mpr hD.2.1
  have hi := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow (p := 2) |>.mpr (by norm_num))
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ ((hw.add hi).div_const 2)
  intro j
  set v : ℝ := ‖c (j+1)‖
  set a : ℝ := ((j+1:ℕ):ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  field_simp
  nlinarith [sq_nonneg (a^2*v-1)]

/-- The continuous representative of the Hardy coefficients on the closed disk. -/
def series (c : H) (z : ℂ) : ℂ := ∑' j : ℕ, c j*z^j

private theorem series_closed {c : H} {D : ℝ} (hD : DerivativeBound c D) :
    ContinuousOn (series c) (closedBall 0 1) ∧ Expands c (series c) := by
  have hsum := summable_norm_of_derivative hD
  have hterm (j : ℕ) (z : ℂ) (hz : z ∈ closedBall 0 1) : ‖c j*z^j‖ ≤ ‖c j‖ := by
    rw [norm_mul,norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (by simpa using hz))
  have hc : ContinuousOn (series c) (closedBall 0 1) := continuousOn_tsum (fun j ↦ by fun_prop) hsum hterm
  refine ⟨hc,?_⟩
  intro z hz
  have hzb : z ∈ closedBall (0:ℂ) 1 := by simpa using hz.le
  exact (Summable.of_norm (Summable.of_nonneg_of_le (fun j ↦ norm_nonneg _) (fun j ↦ hterm j z hzb) hsum)).hasSum

/-- An interior Taylor expansion and the derivative energy give a canonical disk-algebra
representative even when the originally supplied boundary values are arbitrary. -/
theorem series_of_inner_expansion {c : H} {D : ℝ} {F : ℂ → ℂ} (hD : DerivativeBound c D)
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hi : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun j : ℕ ↦ c j*z^j) (F z)) :
    EqOn (series c) F (ball 0 1) ∧ DiffContOnCl ℂ (series c) (ball 0 1) ∧ Expands c (series c) := by
  have heq : EqOn (series c) F (ball 0 1) := fun z hz ↦ (hi z (by simpa using hz)).tsum_eq
  have hc := series_closed hD
  exact ⟨heq,⟨hF.congr heq,by simpa [closure_ball _ one_ne_zero] using hc.1⟩,hc.2⟩

/-- Square summability of the weighted derivative coefficients makes the Taylor series
absolutely convergent at every boundary point. -/
theorem expands_of_coefficients {c : H} {D : ℝ} {F : ℂ → ℂ} (hD : DerivativeBound c D)
    (hF : DiffContOnCl ℂ F (ball 0 1))
    (hcoeff : ∀ j : ℕ, c j = (j.factorial:ℂ)⁻¹ * iteratedDeriv j F 0) : Expands c F := by
  have heq : EqOn (series c) F (ball 0 1) := by
    intro z hz
    apply HasSum.tsum_eq
    apply (Complex.hasSum_taylorSeries_on_ball hF.differentiableOn hz).congr_fun
    intro j
    simp [hcoeff,smul_eq_mul]
    ring
  obtain ⟨hc,hs⟩ := series_closed hD
  have hf := hF.continuousOn
  rw [closure_ball _ one_ne_zero] at hf
  have hclosed := heq.of_subset_closure hc hf ball_subset_closedBall (by rw [closure_ball _ one_ne_zero])
  intro z hz
  exact hclosed (show z ∈ closedBall (0:ℂ) 1 by simpa using hz.le) ▸ hs z hz

/-- Every complex coefficient vector has the stated one-sided Green lower bound. -/
theorem table_energy_lower {F : ℂ → ℂ} {c : H} (hF : DiffContOnCl ℂ F (ball 0 1)) (h0 : F 0 ≠ 0)
    (hexp : Expands c F) {d : ℕ} (p : Coeff d) :
    1-Real.exp (-2*logGap F) ≤ ‖unitVector-product c p‖^2 := by
  have hc := hF.continuousOn
  rw [closure_ball _ one_ne_zero] at hc
  rw [← table_residual_parseval hexp (hc.mono sphere_subset_closedBall) p]
  exact (disk_boundary_lower hF h0).2 _

private theorem le_distance_of_energy {c : H} {K : ℝ}
    (h : ∀ d (p : Coeff d), K ≤ ‖unitVector-product c p‖^2) :
    K ≤ (distance c)^2 := by
  by_cases hK : 0 ≤ K
  · have hne : (multiples c).Nonempty := ⟨product c (0 : Coeff 0),0,0,rfl⟩
    have hdist : Real.sqrt K ≤ distance c := by
      rw [distance,Metric.infDist_closure]
      apply (Metric.le_infDist hne).mpr
      rintro _ ⟨d,p,rfl⟩
      rw [dist_eq_norm]
      exact (Real.sqrt_le_iff).mpr ⟨norm_nonneg _, h d p⟩
    simpa [Real.sq_sqrt hK] using pow_le_pow_left₀ (Real.sqrt_nonneg _) hdist 2
  · exact (le_of_not_ge hK).trans (sq_nonneg _)

/-- The actual squared distance from 1 to the closed polynomial multiples dominates
the supplied logarithmic boundary gap. -/
theorem distance_lower_of_coefficients {F : ℂ → ℂ} {c : H} {D : ℝ}
    (hF : DiffContOnCl ℂ F (ball 0 1)) (h0 : F 0 ≠ 0) (hD : DerivativeBound c D)
    (hcoeff : ∀ j : ℕ, c j = (j.factorial:ℂ)⁻¹ * iteratedDeriv j F 0) :
    0 ≤ logGap F ∧ 1-Real.exp (-2*logGap F) ≤ (distance c)^2 :=
  ⟨(disk_boundary_lower hF h0).1,le_distance_of_energy (fun _ p ↦
    table_energy_lower hF h0 (expands_of_coefficients hD hF hcoeff) p)⟩

/-- Inverting the one-sided bound when a supplied residual upper bound is strictly below one. -/
theorem logGap_le_log_of_upper {G V : ℝ} (hl : 1-Real.exp (-2*G) ≤ V) (hV : V < 1) :
    G ≤ -Real.log (1-V)/2 := by
  have h := Real.log_le_log (sub_pos.mpr hV) (show 1-V ≤ Real.exp (-2*G) by linarith)
  rw [Real.log_exp] at h
  linarith

/-- A finite upper certificate for the boundary gap from a single measured ellipsoid minimizer
and its guaranteed visible and hidden norm errors. -/
theorem finite_logGap_upper_of_expands {F : ℂ → ℂ} {c : H} {D C : ℝ} (hF : DiffContOnCl ℂ F (ball 0 1))
    (h0 : F 0 ≠ 0) (hD : DerivativeBound c D)
    (hexp : Expands c F)
    (hC : 0 ≤ C) (a : ℕ → ℕ → ℂ) (ha : Accurate c linearCut a C) (n : ℕ)
    (V e : ℝ)
    (he : 2*Real.sqrt (((n:ℝ)+1)*((linearCut n:ℝ)+1))*(C*(1/2:ℝ)^(linearCut n)) +
        2*D/Real.sqrt (n+1) ≤ e)
    (hup : (Real.sqrt (leastSquares (linearCut n) (a n) (ellipsoid n))+e)^2 ≤ V)
    (hV : V < 1) :
    logGap F ≤ -Real.log (1-V)/2 := by
  apply logGap_le_log_of_upper _ hV
  obtain ⟨p,hp,hmin,_⟩ := exists_leastSquares (M := linearCut n) (a n) (ellipsoid_compact n) (ellipsoid_nonempty n)
  have hel := ellipsoid_errors hD hC ha n p hp
  have hnorm := (abs_norm_sub_norm_le (visible (linearCut n) (a n) p) (visible (linearCut n) c p)).trans hel.2
  rw [visible_eq_head,abs_le] at hnorm
  have hsplit := le_head_add_tail (unitVector-product c p) (linearCut n)
  have htrue : ‖unitVector-product c p‖ ≤ ‖visible (linearCut n) (a n) p‖+e := by linarith [hel.1]
  rw [hmin,Real.sqrt_sq (norm_nonneg _)] at hup
  exact (table_energy_lower hF h0 hexp p).trans
    ((pow_le_pow_left₀ (norm_nonneg _) htrue 2).trans hup)

/-- The certificate with canonical Taylor coefficients and no boundary Fourier hypothesis. -/
theorem finite_logGap_upper {F : ℂ → ℂ} {c : H} {D C : ℝ} (hF : DiffContOnCl ℂ F (ball 0 1))
    (h0 : F 0 ≠ 0) (hD : DerivativeBound c D)
    (hcoeff : ∀ j : ℕ, c j = (j.factorial:ℂ)⁻¹ * iteratedDeriv j F 0)
    (hC : 0 ≤ C) (a : ℕ → ℕ → ℂ) (ha : Accurate c linearCut a C) (n : ℕ)
    (V e : ℝ)
    (he : 2*Real.sqrt (((n:ℝ)+1)*((linearCut n:ℝ)+1))*(C*(1/2:ℝ)^(linearCut n)) +
        2*D/Real.sqrt (n+1) ≤ e)
    (hup : (Real.sqrt (leastSquares (linearCut n) (a n) (ellipsoid n))+e)^2 ≤ V)
    (hV : V < 1) :
    logGap F ≤ -Real.log (1-V)/2 :=
  finite_logGap_upper_of_expands hF h0 hD (expands_of_coefficients hD hF hcoeff) hC a ha n V e he hup hV

/-- This form consumes an interior expansion directly. Its boundary function is the canonical
continuous representative, so the input function is only needed in the open unit disk. -/
theorem distance_lower_of_inner_expansion {F : ℂ → ℂ} {c : H} {D : ℝ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (h0 : F 0 ≠ 0) (hD : DerivativeBound c D)
    (hi : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun j : ℕ ↦ c j*z^j) (F z)) :
    0 ≤ logGap (series c) ∧ 1-Real.exp (-2*logGap (series c)) ≤ (distance c)^2 := by
  obtain ⟨heq,hreg,hexp⟩ := series_of_inner_expansion hD hF hi
  have hn : series c 0 ≠ 0 := (heq (mem_ball_self (by norm_num))).trans_ne h0
  exact ⟨(disk_boundary_lower hreg hn).1,le_distance_of_energy (fun _ p ↦ table_energy_lower hreg hn hexp p)⟩

end HardyBoundary

end

@[expose] public noncomputable section

open Complex Metric Real

namespace HardyBoundary

/-- A single zero at a inside the disk gives the explicit lower bound 1−‖a‖². -/
theorem affine_root_control {a : ℂ} (ha : a ≠ 0) (hb : ‖a‖ < 1) (p : Polynomial ℂ) :
    1-‖a‖^2 ≤ circleAverage (fun z ↦ ‖1-(z-a)*p.eval z‖^2) 0 1 := by
  have hf : Differentiable ℂ (fun z : ℂ ↦ z-a) := differentiable_id.sub_const _
  have hl := (disk_boundary_lower hf.diffContOnCl (by simpa using ha)).2 p
  rw [circleAverage_log_norm_sub_const₀ hb] at hl
  simp only [zero_sub,norm_neg] at hl
  rwa [show -2 * -Real.log ‖a‖ = Real.log ‖a‖ + Real.log ‖a‖ by ring,Real.exp_add,
    Real.exp_log (norm_pos_iff.mpr ha), ← sq] at hl

/-- For a nonzero complex constant the constant inverse realizes equality at zero residual. -/
theorem constant_control (A : ℂ) (hA : A ≠ 0) :
    1-Real.exp (-2*logGap (fun _ ↦ A)) =
      circleAverage (fun z ↦ ‖1-A*(Polynomial.C A⁻¹).eval z‖^2) 0 1 := by
  simp [logGap, Real.circleAverage_const,hA]

end HardyBoundary

end
