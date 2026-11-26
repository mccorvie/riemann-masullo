module

public import RiemannMasullo.ForMathlib.Analysis.Complex.ClippedOuterPredictor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Truncated clipped predictors in the finite coefficient ellipsoid

Taylor truncation has a boundary square loss bounded by its weighted coefficient budget
divided by the square of the cutoff. The estimates use normalized arclength.
-/

@[expose] public noncomputable section

open Complex Metric MeasureTheory Set Real HardyBoundary HardyTable Finset

namespace HardySzego

private lemma row_apply (b : HardyTable.H) (n : ℕ) (k : Fin (n+1)) :
    head b n k = b k.val := rfl

private lemma row_eval (b : HardyTable.H) (n : ℕ) (z : ℂ) :
    (tablePolynomial (head b n)).eval z = ∑ j ∈ range (n+1), b j*z^j := by
  rw [tablePolynomial_eval]
  simp only [row_apply]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ b j*z^j) (n+1)

/-- Every Taylor truncation obeys its full weighted coefficient budget. -/
theorem weightedEnergy_predictorRow {b : HardyTable.H}
    (hs : Summable (fun j : ℕ ↦ ((j:ℝ)+1)^2*‖b j‖^2)) (n : ℕ) :
    weightedEnergy (head b n) ≤ ∑' j : ℕ, ((j:ℝ)+1)^2*‖b j‖^2 := by
  simp only [weightedEnergy,row_apply,mul_pow]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ ((j:ℝ)+1)^2*‖b j‖^2) (n+1)]
  exact hs.sum_le_tsum _ (fun _ _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Parseval controls the squared truncation error by the weighted budget. No boundary
Taylor convergence hypothesis is needed. -/
theorem circleAverage_predictorRow_error {q : ℂ → ℂ} {b : HardyTable.H}
    (hc : ContinuousOn q (closedBall 0 1))
    (hi : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun j : ℕ ↦ b j*z^j) (q z))
    (hs : Summable (fun j : ℕ ↦ ((j:ℝ)+1)^2*‖b j‖^2)) (n : ℕ) :
    circleAverage (fun z ↦ ‖q z-(tablePolynomial (head b n)).eval z‖^2) 0 1 ≤
      (∑' j : ℕ, ((j:ℝ)+1)^2*‖b j‖^2)/((n:ℝ)+1)^2 := by
  let u (j : ℕ) := if j ≤ n then 0 else b j
  have htail : HasSum (fun j : ℕ ↦ ‖u j‖^2)
      (circleAverage (fun z ↦ ‖q z-(tablePolynomial (head b n)).eval z‖^2) 0 1) := by
    apply hasSum_sq_of_inner (hc.sub (tablePolynomial _).continuous.continuousOn)
    intro z hz
    let v (j : ℕ) := if j ≤ n then b j*z^j else 0
    have hp : HasSum v ((tablePolynomial (head b n)).eval z) := by
      rw [row_eval]
      have hp : HasSum v (∑ j ∈ range (n+1), v j) := hasSum_sum_of_ne_finset_zero
        (fun j hj ↦ by
          have hn : ¬j ≤ n := by simpa using hj
          simp [v,hn])
      convert hp using 1
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ n := by simpa using hj
      simp [v,hj']
    apply ((hi z hz).sub hp).congr_fun
    intro j
    by_cases hj : j ≤ n <;> simp [u,v,hj]
  have hle (j : ℕ) : ((n:ℝ)+1)^2*‖u j‖^2 ≤ ((j:ℝ)+1)^2*‖b j‖^2 := by
    by_cases hj : j ≤ n
    · rw [show u j = 0 by simp [u,hj],norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero]
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · rw [show u j = b j by simp [u,hj]]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast (show n+1 ≤ j+1 by omega)
  have hm := (htail.mul_left (((n:ℝ)+1)^2)).summable.tsum_le_tsum hle hs
  rw [(htail.mul_left (((n:ℝ)+1)^2)).tsum_eq] at hm
  exact (le_div_iff₀ (by positivity)).mpr (by linarith only [hm])

private lemma young_square {a b τ : ℝ} (ht : 0 < τ) :
    (a+b)^2 ≤ (1+τ)*a^2+(1+τ⁻¹)*b^2 := by
  field_simp
  nlinarith [sq_nonneg (τ*a-b)]

private lemma truncation_residual {F q : ℂ → ℂ} {P : Polynomial ℂ}
    (hF : ContinuousOn F (sphere 0 1)) (hq : ContinuousOn q (sphere 0 1))
    (hN : ∀ z ∈ sphere (0:ℂ) 1, ‖F z‖ ≤ 1) {τ : ℝ} (ht : 0 < τ) :
    circleAverage (fun z ↦ ‖1-F z*P.eval z‖^2) 0 1 ≤
      (1+τ)*circleAverage (fun z ↦ ‖1-q z*F z‖^2) 0 1+
      (1+τ⁻¹)*circleAverage (fun z ↦ ‖q z-P.eval z‖^2) 0 1 := by
  let a (z : ℂ) := ‖1-q z*F z‖^2
  let b (z : ℂ) := ‖q z-P.eval z‖^2
  have ha : CircleIntegrable a 0 1 := ((continuousOn_const.sub (hq.mul hF)).norm.pow 2).circleIntegrable zero_le_one
  have hb : CircleIntegrable b 0 1 := ((hq.sub P.continuous.continuousOn).norm.pow 2).circleIntegrable zero_le_one
  have hc : CircleIntegrable (fun z ↦ ‖1-F z*P.eval z‖^2) 0 1 :=
    ((continuousOn_const.sub (hF.mul P.continuous.continuousOn)).norm.pow 2).circleIntegrable zero_le_one
  have h1 : CircleIntegrable (fun z ↦ (1+τ) • a z) 0 1 := ha.const_smul (a := 1+τ)
  have h2 : CircleIntegrable (fun z ↦ (1+τ⁻¹) • b z) 0 1 := hb.const_smul (a := 1+τ⁻¹)
  calc
    _ ≤ circleAverage (fun z ↦ (1+τ) • a z+(1+τ⁻¹) • b z) 0 1 := by
      apply circleAverage_mono hc (h1.add h2)
      intro z hz
      change ‖1-F z*P.eval z‖^2 ≤ (1+τ)*‖1-q z*F z‖^2+(1+τ⁻¹)*‖q z-P.eval z‖^2
      apply le_trans _ (young_square ht)
      apply pow_le_pow_left₀ (norm_nonneg _)
      calc
        ‖1-F z*P.eval z‖ = ‖(1-q z*F z)+F z*(q z-P.eval z)‖ := by ring_nf
        _ ≤ ‖1-q z*F z‖+‖F z*(q z-P.eval z)‖ := norm_add_le _ _
        _ ≤ _ := by rw [norm_mul]; grw [hN z (by simpa using hz)]; simp
    _ = _ := by rw [circleAverage_fun_add h1 h2, circleAverage_fun_smul, circleAverage_fun_smul]; rfl

/-- Finite polynomial version in the literal coefficient ellipsoid. The parameter `τ`
balances the boundary residual against its Taylor-truncation loss. -/
theorem exists_clipped_polynomial {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1)) (h0 : F 0 ≠ 0)
    {D H ε τ : ℝ} (hD : 0 ≤ D) (hd : ∀ z ∈ ball (0:ℂ) 1, ‖deriv F z‖ ≤ D)
    (hN : ∀ z ∈ sphere (0:ℂ) 1, ‖F z‖ ≤ 1) (hH : 0 ≤ H) (hε : 0 < ε) (ht : 0 < τ)
    (n : ℕ) (hn : 10*(1+D^2)*Real.exp (4*H) ≤ (n:ℝ)+1) :
    ∃ p ∈ ellipsoid n, circleAverage (fun z ↦ ‖1-F z*(tablePolynomial p).eval z‖^2) 0 1 ≤
      (1+τ)*((distance (diskCoefficients F hF))^2+2*(clippingLoss F H+ε))+
      (1+τ⁻¹)*(10*(1+D^2)*Real.exp (4*H)/((n:ℝ)+1)^2) := by
  obtain ⟨q,hq,_,hs,hw,he⟩ := exists_clipped_predictor hF h0 hD (boundary_lipschitz_of_deriv hF hD hd) hH hε
  let b := diskCoefficients q hq.diffContOnCl
  have hseries := hasSum_diskCoefficients hq.diffContOnCl
  let p := head b n
  have hi := circleAverage_predictorRow_error hq.continuous.continuousOn hseries hs n
  have hc := hF.continuousOn
  rw [closure_ball _ one_ne_zero] at hc
  refine ⟨p,(weightedEnergy_predictorRow hs n).trans (hw.trans hn),?_⟩
  apply (truncation_residual (P := tablePolynomial p) (hc.mono sphere_subset_closedBall)
    hq.continuous.continuousOn hN ht).trans
  exact add_le_add (mul_le_mul_of_nonneg_left he (by positivity))
    (mul_le_mul_of_nonneg_left (hi.trans (div_le_div_of_nonneg_right hw (by positivity))) (by positivity))


/-- The finite ellipsoid is compact, so minimization removes the positive approximation
tolerance. Only the clipping loss and the explicit finite Taylor cutoff remain. -/
theorem exists_clipped_ellipsoid_predictor {F : ℂ → ℂ} (hF : DiffContOnCl ℂ F (ball 0 1))
    (h0 : F 0 ≠ 0) {D H τ : ℝ} (hD : 0 ≤ D)
    (hd : ∀ z ∈ ball (0:ℂ) 1, ‖deriv F z‖ ≤ D)
    (hN : ∀ z ∈ sphere (0:ℂ) 1, ‖F z‖ ≤ 1) (hH : 0 ≤ H) (ht : 0 < τ)
    (n : ℕ) (hn : 10*(1+D^2)*Real.exp (4*H) ≤ (n:ℝ)+1) :
    ∃ p ∈ ellipsoid n, circleAverage (fun z ↦ ‖1-F z*(tablePolynomial p).eval z‖^2) 0 1 ≤
      (1+τ)*((distance (diskCoefficients F hF))^2+2*clippingLoss F H)+
      (1+τ⁻¹)*(10*(1+D^2)*Real.exp (4*H)/((n:ℝ)+1)^2) := by
  let C := diskCoefficients F hF
  let E (p : Coeff n) := ‖unitVector-product C p‖^2
  have hc := hF.continuousOn
  rw [closure_ball _ one_ne_zero] at hc
  have he (p : Coeff n) : circleAverage (fun z ↦ ‖1-F z*(tablePolynomial p).eval z‖^2) 0 1 = E p :=
    table_residual_of_inner hc (hasSum_diskCoefficients hF) p
  have hE : Continuous E := by
    unfold E product
    fun_prop
  obtain ⟨p,hp,hmin⟩ := (ellipsoid_compact n).exists_isMinOn (ellipsoid_nonempty n) hE.continuousOn
  refine ⟨p,hp,?_⟩
  rw [he]
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε := δ/(2*(1+τ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hδ' : ε*(2*(1+τ)) = δ := by dsimp [ε]; field_simp
  obtain ⟨p',hp',hb⟩ := exists_clipped_polynomial hF h0 hD hd hN hH hε ht n hn
  rw [he] at hb
  have hm : E p ≤ E p' := hmin hp'
  nlinarith only [hδ',hm,hb]

end HardySzego
