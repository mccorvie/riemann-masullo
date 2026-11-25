module

public import RiemannMasullo.ForMathlib.Analysis.Complex.HardyBoundaryDistance
public import RiemannMasullo.ForMathlib.Analysis.Complex.SzegoPrediction

/-!
# The exact Hardy distance in coefficient space

For a disk-algebra function with nonzero center the squared coefficient distance is
`1 - exp (-2 * logGap F)`. Radial Parseval identifies the boundary extremum with the
Hilbert-space distance and the finite coefficient tables recover it in the limit.
-/

@[expose] public noncomputable section

open Complex Filter MeasureTheory Set Metric Real Finset HardyBoundary HardyTable
open scoped Topology

namespace HardySzego

private theorem shift_hasSum {c : H} {z v : ℂ} (hf : HasSum (fun j : ℕ ↦ c j*z^j) v) (k : ℕ) :
    HasSum (fun j : ℕ ↦ shift c k j*z^j) (v*z^k) := by
  apply (hasSum_nat_add_iff' k).mp
  have hpre : ∑ i ∈ range k, shift c k i*z^i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [shift,not_le.mpr (Finset.mem_range.mp hi)]
  rw [hpre,sub_zero]
  convert! hf.mul_right (z^k) using 1
  funext j
  simp [shift,pow_add,mul_assoc]

private theorem residual_hasSum {c : H} {z v : ℂ} (hf : HasSum (fun j : ℕ ↦ c j*z^j) v)
    {d : ℕ} (p : Coeff d) :
    HasSum (fun j : ℕ ↦ (unitVector-product c p) j*z^j) (1-v*(tablePolynomial p).eval z) := by
  have hu : HasSum (fun j : ℕ ↦ unitVector j*z^j) 1 := by
    convert! hasSum_ite_eq (0:ℕ) (1:ℂ) using 1
    funext j
    by_cases hj : j = 0 <;> simp [unitVector_apply,hj]
  have hs (k : Fin (d+1)) := (shift_hasSum hf k).mul_left (p k)
  have hp : HasSum (fun j : ℕ ↦ product c p j*z^j) (v*(tablePolynomial p).eval z) := by
    convert! hasSum_sum (s := (univ : Finset (Fin (d+1)))) (fun k _ ↦ hs k) using 1
    · funext j
      rw [product_apply,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      change (p k*(_ : ℂ))*z^j = p k*(_*z^j)
      rw [mul_assoc]
      rfl
    · rw [tablePolynomial_eval,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
  simpa only [lp.coeFn_sub,Pi.sub_apply,sub_mul] using hu.sub hp

/-- The original coefficient-table residual has its exact boundary energy, for any
continuous extension of the open-disk power expansion. -/
theorem table_residual_of_inner {F : ℂ → ℂ} {c : H} (hc : ContinuousOn F (closedBall 0 1))
    (hi : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun j : ℕ ↦ c j*z^j) (F z))
    {d : ℕ} (p : Coeff d) :
    circleAverage (fun z ↦ ‖1-F z*(tablePolynomial p).eval z‖^2) 0 1 =
      ‖unitVector-product c p‖^2 := by
  have hsum := hasSum_sq_of_inner (b := fun j ↦ (unitVector-product c p) j)
    (continuousOn_const.sub (hc.mul (tablePolynomial p).continuous.continuousOn))
    (fun z hz ↦ residual_hasSum (hi z hz) p)
  exact hsum.tsum_eq.symm.trans (HardyTable.norm_sq _).symm

private def ofPolynomial (P : Polynomial ℂ) : Coeff P.natDegree :=
  WithLp.toLp 2 fun k ↦ P.coeff k

private theorem table_ofPolynomial (P : Polynomial ℂ) : tablePolynomial (ofPolynomial P) = P := by
  change (∑ k : Fin (P.natDegree+1), Polynomial.C (P.coeff k)*Polynomial.X^k.val) = P
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ Polynomial.C (P.coeff k)*Polynomial.X^k) (P.natDegree+1)]
  exact P.as_sum_range_C_mul_X_pow.symm

/-- Distance from the unit vector to the closed set of all polynomial multiples. -/
theorem distance_sq_of_inner {F : ℂ → ℂ} {c : H} (hF : DiffContOnCl ℂ F (ball 0 1))
    (h0 : F 0 ≠ 0) (hi : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun j : ℕ ↦ c j*z^j) (F z)) :
    (distance c)^2 = 1-Real.exp (-2*logGap F) := by
  have hc := hF.continuousOn
  rw [closure_ball _ one_ne_zero] at hc
  let E (p : Polynomial ℂ) := circleAverage (fun z ↦ ‖1-F z*p.eval z‖^2) 0 1
  have hne : (Set.range E).Nonempty := Set.range_nonempty _
  have hpos : ∀ p, 0 ≤ E p := fun p ↦ circleAverage_nonneg_of_nonneg (fun _ _ ↦ sq_nonneg _)
  have hB : BddBelow (Set.range E) := ⟨0,by rintro _ ⟨p,rfl⟩; exact hpos p⟩
  have hK : 0 ≤ sInf (Set.range E) := le_csInf hne (by rintro _ ⟨p,rfl⟩; exact hpos p)
  rw [← boundary_infimum hF h0]
  change (distance c)^2 = sInf (Set.range E)
  apply le_antisymm
  · apply le_csInf hne
    rintro _ ⟨p,rfl⟩
    let hp := ofPolynomial p
    have hm : product c hp ∈ closure (multiples c) := subset_closure ⟨p.natDegree,hp,rfl⟩
    have hd : distance c ≤ ‖unitVector-product c hp‖ := by
      simpa only [distance,dist_eq_norm] using Metric.infDist_le_dist_of_mem hm (x := unitVector)
    have he := table_residual_of_inner hc hi hp
    rw [show tablePolynomial hp = p from table_ofPolynomial p] at he
    exact (pow_le_pow_left₀ Metric.infDist_nonneg hd 2).trans he.ge
  · have hm : (multiples c).Nonempty := ⟨product c (0 : Coeff 0),0,0,rfl⟩
    have hd : Real.sqrt (sInf (Set.range E)) ≤ distance c := by
      rw [distance,Metric.infDist_closure]
      apply (Metric.le_infDist hm).mpr
      rintro _ ⟨d,p,rfl⟩
      rw [dist_eq_norm]
      apply (Real.sqrt_le_iff).mpr
      refine ⟨norm_nonneg _,?_⟩
      rw [← table_residual_of_inner hc hi p]
      exact csInf_le hB ⟨tablePolynomial p,rfl⟩
    simpa [Real.sq_sqrt hK] using pow_le_pow_left₀ (Real.sqrt_nonneg _) hd 2

private def taylor (F : ℂ → ℂ) (j : ℕ) := (j.factorial:ℂ)⁻¹ * iteratedDeriv j F 0

private theorem taylor_hasSum {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1))
    (z : ℂ) (hz : ‖z‖ < 1) : HasSum (fun j : ℕ ↦ taylor F j*z^j) (F z) := by
  apply (Complex.hasSum_taylorSeries_on_ball hF.differentiableOn (show z ∈ ball 0 1 by simpa using hz)).congr_fun
  intro j
  simp [taylor,smul_eq_mul]
  ring

/-- Every disk-algebra function has its Taylor coefficients in the actual table Hilbert space. -/
def diskCoefficients (F : ℂ → ℂ) (hF : DiffContOnCl ℂ F (ball 0 1)) : H :=
  ⟨fun j ↦ (j.factorial:ℂ)⁻¹ * iteratedDeriv j F 0,by
    have hc := hF.continuousOn
    rw [closure_ball _ one_ne_zero] at hc
    apply (memℓp_gen_iff (by norm_num : 0 < (2:ENNReal).toReal)).2
    simpa [taylor] using (hasSum_sq_of_inner hc (taylor_hasSum hF)).summable⟩

theorem diskCoefficients_apply (F : ℂ → ℂ) (hF : DiffContOnCl ℂ F (ball 0 1)) (j : ℕ) :
    diskCoefficients F hF j = (j.factorial:ℂ)⁻¹ * iteratedDeriv j F 0 := rfl

/-- Exact Hilbert-space boundary logarithm formula with no separate growth or Taylor hypotheses. -/
theorem disk_distance_sq {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1)) (h0 : F 0 ≠ 0) :
    (distance (diskCoefficients F hF))^2 = 1-Real.exp (-2*logGap F) :=
  distance_sq_of_inner hF h0 (taylor_hasSum hF)

theorem distance_sq_of_coefficients {F : ℂ → ℂ} {c : H} (hF : DiffContOnCl ℂ F (ball 0 1))
    (h0 : F 0 ≠ 0) (hcoeff : ∀ j : ℕ, c j = (j.factorial:ℂ)⁻¹ * iteratedDeriv j F 0) :
    (distance c)^2 = 1-Real.exp (-2*logGap F) := by
  apply distance_sq_of_inner hF h0
  intro z hz
  simpa only [taylor,← hcoeff] using taylor_hasSum hF z hz

/-- The measured coefficient table has the exact logarithmic limit, with its original
linear sample cutoff, ellipsoid constraint, and certified uniform entry errors. -/
theorem finiteRows_logarithmic_limit {F : ℂ → ℂ} {c : H} {D C : ℝ}
    (hF : DiffContOnCl ℂ F (ball 0 1)) (h0 : F 0 ≠ 0)
    (hi : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun j : ℕ ↦ c j*z^j) (F z))
    (hD : DerivativeBound c D) (hC : 0 ≤ C) (a : (n : ℕ) → Fin (linearCut n+1) → ℂ)
    (ha : ∀ n (j : Fin (linearCut n+1)), ‖a n j-c j‖ ≤ C*(1/2:ℝ)^(linearCut n)) :
    Tendsto (fun n ↦ leastSquares (linearCut n) (extendRow (a n)) (ellipsoid n))
      atTop (𝓝 (1-Real.exp (-2*logGap F))) := by
  rw [← distance_sq_of_inner hF h0 hi]
  exact linear_finiteRows_tendsto hD hC a ha

/-- For data initially represented only on the open disk, the derivative bound constructs
the canonical continuous boundary representative used in the logarithmic gap. -/
theorem finiteRows_logarithmic_limit_of_series {F : ℂ → ℂ} {c : H} {D C : ℝ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (h0 : F 0 ≠ 0)
    (hi : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun j : ℕ ↦ c j*z^j) (F z))
    (hD : DerivativeBound c D) (hC : 0 ≤ C) (a : (n : ℕ) → Fin (linearCut n+1) → ℂ)
    (ha : ∀ n (j : Fin (linearCut n+1)), ‖a n j-c j‖ ≤ C*(1/2:ℝ)^(linearCut n)) :
    Tendsto (fun n ↦ leastSquares (linearCut n) (extendRow (a n)) (ellipsoid n))
      atTop (𝓝 (1-Real.exp (-2*logGap (series c)))) := by
  obtain ⟨heq,hreg,_⟩ := series_of_inner_expansion hD hF hi
  have hn : series c 0 ≠ 0 := (heq (mem_ball_self (by norm_num))).trans_ne h0
  apply finiteRows_logarithmic_limit hreg hn _ hD hC a ha
  intro z hz
  rw [heq (by simpa using hz)]
  exact hi z hz

end HardySzego

end

@[expose] public noncomputable section

open Complex Metric Real HardyTable HardyBoundary

namespace HardySzego

/-- A nonzero interior root has the strictly positive residual 1−‖a‖². -/
theorem interior_root_control {a : ℂ} (ha : a ≠ 0) (hb : ‖a‖ < 1) :
    (distance (diskCoefficients (fun z : ℂ ↦ z-a) (differentiable_id.sub_const a).diffContOnCl))^2 =
      1-‖a‖^2 ∧ 0 < 1-‖a‖^2 := by
  have h0 : (fun z : ℂ ↦ z-a) 0 ≠ 0 := by simpa using ha
  constructor
  · rw [disk_distance_sq _ h0]
    simp only [logGap,circleAverage_log_norm_sub_const₀ hb,zero_sub,norm_neg]
    rw [show -2 * -Real.log ‖a‖ = Real.log ‖a‖ + Real.log ‖a‖ by ring,Real.exp_add,
      Real.exp_log (norm_pos_iff.mpr ha),sq]
  · nlinarith [mul_self_lt_mul_self (norm_nonneg a) hb]

/-- A boundary zero is permitted and the distance remains zero. -/
theorem boundary_root_control {a : ℂ} (ha : ‖a‖ = 1) :
    distance (diskCoefficients (fun z : ℂ ↦ z-a) (differentiable_id.sub_const a).diffContOnCl) = 0 := by
  have han : a ≠ 0 := by intro h; simp [h] at ha
  have h0 : (fun z : ℂ ↦ z-a) 0 ≠ 0 := by simpa using han
  have h := disk_distance_sq (F := fun z : ℂ ↦ z-a) (differentiable_id.sub_const a).diffContOnCl h0
  simp only [logGap,circleAverage_log_norm_sub_const₁ ha,zero_sub,norm_neg,ha,Real.log_one,
    mul_zero,Real.exp_zero,sub_self] at h
  exact sq_eq_zero_iff.mp h

/-- At the excluded center-zero example z, the distance is one while the totalized logarithm
would give zero on the right. Thus deleting the center hypothesis would give a false statement. -/
theorem zero_center_control :
    distance (diskCoefficients (fun z : ℂ ↦ z) differentiable_id.diffContOnCl) = 1 ∧
      1-Real.exp (-2*logGap (fun z : ℂ ↦ z)) = 0 := by
  constructor
  · apply HardyTable.distance_of_constant_zero
    simp [diskCoefficients_apply]
  · have h := circleAverage_log_norm_sub_const₀ (a := (0:ℂ)) (by norm_num)
    simp only [sub_zero] at h
    simp [logGap,h]

end HardySzego

end
