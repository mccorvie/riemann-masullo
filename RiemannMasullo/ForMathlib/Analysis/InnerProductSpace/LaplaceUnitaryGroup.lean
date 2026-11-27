module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.L2Space
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.LaplaceSemigroup

/-! # The Laplace transforms of a strongly continuous unitary group

Let `U` be a strongly continuous one-parameter group of norm-preserving operators of a complex
Hilbert space, and for a rate `c > 0` let

* `P g = ∫ x in Ioi 0, exp (-c * x) • U x g`, the forward Laplace transform, and
* `Q g = ∫ x in Ioi 0, exp (-c * x) • U (-x) g`, the backward Laplace transform.

For the translations of `L²(ℝ)` these are the convolutions with the one-sided exponential
`exp (-c * x)`, `x > 0`, and with its reflection. Both are bounded, with norm at most `c⁻¹`
(`exists_laplace_clm_of_contraction`). Each is the adjoint of the other
(`adjoint_laplace_unitary_group`, `adjoint_backward_laplace_unitary_group`), they commute
(`laplace_unitary_group_comm`), and therefore `‖Q g‖ = ‖P g‖`
(`norm_backward_laplace_unitary_group`). With `mul_norm_sq_laplace_semigroup_le_re_inner` for
`U` and for its reflection (`mul_norm_sq_backward_laplace_unitary_group_le_re_inner`) these are
the hypotheses of `two_thirds_mul_sum_le_re_sum_inner_jet_add`. Nothing here uses the Fourier
transform or the spectral theorem. -/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace RiemannMasullo

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The Laplace transform at a rate `c > 0` of a strongly continuous family of contractions is
a bounded operator: there is a continuous linear map `P` with
`P w = ∫ x in Ioi 0, exp (-c * x) • U x w` for every `w`, and `‖P w‖ ≤ c⁻¹ * ‖w‖`. -/
theorem exists_laplace_clm_of_contraction (U : ℝ → E →L[ℂ] E)
    (hle : ∀ x, 0 ≤ x → ∀ w, ‖U x w‖ ≤ ‖w‖) (hcont : ∀ w, Continuous fun x ↦ U x w)
    {c : ℝ} (hc : 0 < c) :
    ∃ P : E →L[ℂ] E, (∀ w, P w = ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U x w) ∧
      ∀ w, ‖P w‖ ≤ c⁻¹ * ‖w‖ := by
  have hint (w : E) : IntegrableOn (fun x ↦ Real.exp (-c * x) • U x w) (Ioi 0) :=
    integrableOn_exp_smul_orbit U hle hcont hc w 0 le_rfl
  let P₀ : E →ₗ[ℂ] E :=
    { toFun := fun w ↦ ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U x w
      map_add' := fun v w ↦ by
        simp only [map_add, smul_add]
        exact integral_add (hint v) (hint w)
      map_smul' := fun a w ↦ by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        exact integral_congr_ae (.of_forall fun x ↦ smul_comm _ _ _) }
  have hbound (w : E) : ‖P₀ w‖ ≤ c⁻¹ * ‖w‖ := by
    calc ‖∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U x w‖
        ≤ ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) * ‖w‖ :=
          norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi 0 hc).mul_const ‖w‖)
            ((ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ by
              rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
              exact mul_le_mul_of_nonneg_left (hle x (le_of_lt hx) w) (Real.exp_pos _).le)
      _ = c⁻¹ * ‖w‖ := by
          rw [integral_mul_const, integral_exp_mul_Ioi (neg_lt_zero.mpr hc) 0, mul_zero,
            Real.exp_zero, neg_div_neg_eq, one_div]
  exact ⟨P₀.mkContinuous c⁻¹ hbound, fun w ↦ rfl, hbound⟩

/-- The operators of a norm-preserving one-parameter group of a Hilbert space are unitary: the
adjoint of `U x` is `U (-x)`. -/
theorem inner_unitary_group_apply_left (U : ℝ → E →L[ℂ] E) (hU₀ : ∀ w, U 0 w = w)
    (hadd : ∀ x y w, U (x + y) w = U x (U y w)) (hnorm : ∀ x w, ‖U x w‖ = ‖w‖)
    (x : ℝ) (f g : E) : ⟪U x f, g⟫_ℂ = ⟪f, U (-x) g⟫_ℂ := by
  have h : ⟪U x f, U x (U (-x) g)⟫_ℂ = ⟪f, U (-x) g⟫_ℂ :=
    (LinearMap.norm_map_iff_inner_map_map (U x)).mp (hnorm x) f (U (-x) g)
  rwa [← hadd, add_neg_cancel, hU₀] at h

/-- The pairing of the forward Laplace transform of a strongly continuous unitary group with a
vector is the pairing with the backward Laplace transform of that vector. -/
theorem inner_laplace_unitary_group_left (U : ℝ → E →L[ℂ] E) (hU₀ : ∀ w, U 0 w = w)
    (hadd : ∀ x y w, U (x + y) w = U x (U y w)) (hnorm : ∀ x w, ‖U x w‖ = ‖w‖)
    (hcont : ∀ w, Continuous fun x ↦ U x w) {c : ℝ} (hc : 0 < c) (f g : E) :
    ⟪∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U x f, g⟫_ℂ =
      ⟪f, ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U (-x) g⟫_ℂ := by
  have hf : IntegrableOn (fun x ↦ Real.exp (-c * x) • U x f) (Ioi 0) :=
    integrableOn_exp_smul_orbit U (fun x _ w ↦ (hnorm x w).le) hcont hc f 0 le_rfl
  have hg : IntegrableOn (fun x ↦ Real.exp (-c * x) • U (-x) g) (Ioi 0) :=
    integrableOn_exp_smul_orbit (fun x ↦ U (-x)) (fun x _ w ↦ (hnorm (-x) w).le)
      (fun w ↦ (hcont w).comp continuous_neg) hc g 0 le_rfl
  calc ⟪∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U x f, g⟫_ℂ
      = starRingEnd ℂ ⟪g, ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U x f⟫_ℂ :=
        (inner_conj_symm _ _).symm
    _ = starRingEnd ℂ (∫ x in Ioi (0 : ℝ), ⟪g, Real.exp (-c * x) • U x f⟫_ℂ) := by
        rw [integral_inner hf g]
    _ = ∫ x in Ioi (0 : ℝ), starRingEnd ℂ ⟪g, Real.exp (-c * x) • U x f⟫_ℂ :=
        integral_conj.symm
    _ = ∫ x in Ioi (0 : ℝ), ⟪f, Real.exp (-c * x) • U (-x) g⟫_ℂ := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        beta_reduce
        rw [inner_conj_symm, inner_smul_left_eq_smul, inner_smul_right_eq_smul,
          inner_unitary_group_apply_left U hU₀ hadd hnorm]
    _ = ⟪f, ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U (-x) g⟫_ℂ := integral_inner hg f

/-- A bounded operator that commutes with every operator of a family commutes with the Laplace
transform of the family, on every vector whose damped orbit is integrable. -/
theorem clm_apply_laplace_of_commute (U : ℝ → E →L[ℂ] E) {c : ℝ} (A : E →L[ℂ] E)
    (hA : ∀ x w, A (U x w) = U x (A w)) (g : E)
    (hint : IntegrableOn (fun x ↦ Real.exp (-c * x) • U x g) (Ioi 0)) :
    A (∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U x g) =
      ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U x (A g) := by
  rw [← A.integral_comp_comm hint]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  beta_reduce
  rw [A.map_smul_of_tower, hA]

/-- The forward Laplace transform of a strongly continuous unitary group at one rate commutes
with its backward Laplace transform at another rate. -/
theorem laplace_unitary_group_comm (U : ℝ → E →L[ℂ] E)
    (hadd : ∀ x y w, U (x + y) w = U x (U y w)) (hnorm : ∀ x w, ‖U x w‖ = ‖w‖)
    (hcont : ∀ w, Continuous fun x ↦ U x w) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (P Q : E →L[ℂ] E)
    (hP : ∀ w, P w = ∫ x in Ioi (0 : ℝ), Real.exp (-c₁ * x) • U x w)
    (hQ : ∀ w, Q w = ∫ x in Ioi (0 : ℝ), Real.exp (-c₂ * x) • U (-x) w) (g : E) :
    P (Q g) = Q (P g) := by
  have hUQ (y : ℝ) (w : E) : Q (U y w) = U y (Q w) := by
    have hcomm (x : ℝ) (v : E) : U y (U (-x) v) = U (-x) (U y v) := by
      rw [← hadd, ← hadd, add_comm]
    have h := clm_apply_laplace_of_commute (fun x ↦ U (-x)) (c := c₂) (U y) hcomm w
      (integrableOn_exp_smul_orbit (fun x ↦ U (-x)) (fun x _ v ↦ (hnorm (-x) v).le)
        (fun v ↦ (hcont v).comp continuous_neg) hc₂ w 0 le_rfl)
    rw [hQ (U y w), hQ w]
    exact h.symm
  have h := clm_apply_laplace_of_commute U (c := c₁) Q hUQ g
    (integrableOn_exp_smul_orbit U (fun x _ v ↦ (hnorm x v).le) hcont hc₁ g 0 le_rfl)
  rw [hP (Q g), hP g]
  exact h.symm

/-- The adjoint of the forward Laplace transform of a strongly continuous unitary group is its
backward Laplace transform at the same rate. -/
theorem adjoint_laplace_unitary_group (U : ℝ → E →L[ℂ] E) (hU₀ : ∀ w, U 0 w = w)
    (hadd : ∀ x y w, U (x + y) w = U x (U y w)) (hnorm : ∀ x w, ‖U x w‖ = ‖w‖)
    (hcont : ∀ w, Continuous fun x ↦ U x w) {c : ℝ} (hc : 0 < c) (P Q : E →L[ℂ] E)
    (hP : ∀ w, P w = ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U x w)
    (hQ : ∀ w, Q w = ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U (-x) w) :
    ContinuousLinearMap.adjoint P = Q := by
  have h : P = ContinuousLinearMap.adjoint Q :=
    (ContinuousLinearMap.eq_adjoint_iff P Q).mpr fun f g ↦ by
      rw [hP f, hQ g]
      exact inner_laplace_unitary_group_left U hU₀ hadd hnorm hcont hc f g
  rw [h, ContinuousLinearMap.adjoint_adjoint]

/-- The adjoint of the backward Laplace transform of a strongly continuous unitary group is its
forward Laplace transform at the same rate. -/
theorem adjoint_backward_laplace_unitary_group (U : ℝ → E →L[ℂ] E) (hU₀ : ∀ w, U 0 w = w)
    (hadd : ∀ x y w, U (x + y) w = U x (U y w)) (hnorm : ∀ x w, ‖U x w‖ = ‖w‖)
    (hcont : ∀ w, Continuous fun x ↦ U x w) {c : ℝ} (hc : 0 < c) (P Q : E →L[ℂ] E)
    (hP : ∀ w, P w = ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U x w)
    (hQ : ∀ w, Q w = ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U (-x) w) :
    ContinuousLinearMap.adjoint Q = P := by
  rw [← adjoint_laplace_unitary_group U hU₀ hadd hnorm hcont hc P Q hP hQ,
    ContinuousLinearMap.adjoint_adjoint]

/-- The forward and the backward Laplace transform of a strongly continuous unitary group at
the same rate have the same norm on every vector: each is the adjoint of the other and they
commute, so both are normal. -/
theorem norm_backward_laplace_unitary_group (U : ℝ → E →L[ℂ] E) (hU₀ : ∀ w, U 0 w = w)
    (hadd : ∀ x y w, U (x + y) w = U x (U y w)) (hnorm : ∀ x w, ‖U x w‖ = ‖w‖)
    (hcont : ∀ w, Continuous fun x ↦ U x w) {c : ℝ} (hc : 0 < c) (P Q : E →L[ℂ] E)
    (hP : ∀ w, P w = ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U x w)
    (hQ : ∀ w, Q w = ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U (-x) w) (g : E) :
    ‖Q g‖ = ‖P g‖ := by
  have hadj : ContinuousLinearMap.adjoint P = Q :=
    adjoint_laplace_unitary_group U hU₀ hadd hnorm hcont hc P Q hP hQ
  have hcomm : P (Q g) = Q (P g) :=
    laplace_unitary_group_comm U hadd hnorm hcont hc hc P Q hP hQ g
  have hinner : ⟪Q g, Q g⟫_ℂ = ⟪P g, P g⟫_ℂ :=
    calc ⟪Q g, Q g⟫_ℂ = ⟪ContinuousLinearMap.adjoint P g, Q g⟫_ℂ := by rw [hadj]
      _ = ⟪g, P (Q g)⟫_ℂ := ContinuousLinearMap.adjoint_inner_left P (Q g) g
      _ = ⟪g, ContinuousLinearMap.adjoint P (P g)⟫_ℂ := by rw [hcomm, hadj]
      _ = ⟪P g, P g⟫_ℂ := ContinuousLinearMap.adjoint_inner_right P g (P g)
  have hsq : ‖Q g‖ ^ 2 = ‖P g‖ ^ 2 := by
    have h : RCLike.re ⟪Q g, Q g⟫_ℂ = RCLike.re ⟪P g, P g⟫_ℂ := by rw [hinner]
    rwa [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The adjoint of the forward Laplace transform of a strongly continuous unitary group is no
larger than the transform on any vector. -/
theorem norm_adjoint_laplace_unitary_group_le (U : ℝ → E →L[ℂ] E) (hU₀ : ∀ w, U 0 w = w)
    (hadd : ∀ x y w, U (x + y) w = U x (U y w)) (hnorm : ∀ x w, ‖U x w‖ = ‖w‖)
    (hcont : ∀ w, Continuous fun x ↦ U x w) {c : ℝ} (hc : 0 < c) (P Q : E →L[ℂ] E)
    (hP : ∀ w, P w = ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U x w)
    (hQ : ∀ w, Q w = ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U (-x) w) (g : E) :
    ‖ContinuousLinearMap.adjoint P g‖ ≤ ‖P g‖ := by
  rw [adjoint_laplace_unitary_group U hU₀ hadd hnorm hcont hc P Q hP hQ]
  exact (norm_backward_laplace_unitary_group U hU₀ hadd hnorm hcont hc P Q hP hQ g).le

/-- The adjoint of the backward Laplace transform of a strongly continuous unitary group is no
larger than the transform on any vector. -/
theorem norm_adjoint_backward_laplace_unitary_group_le (U : ℝ → E →L[ℂ] E)
    (hU₀ : ∀ w, U 0 w = w) (hadd : ∀ x y w, U (x + y) w = U x (U y w))
    (hnorm : ∀ x w, ‖U x w‖ = ‖w‖) (hcont : ∀ w, Continuous fun x ↦ U x w) {c : ℝ}
    (hc : 0 < c) (P Q : E →L[ℂ] E)
    (hP : ∀ w, P w = ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U x w)
    (hQ : ∀ w, Q w = ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U (-x) w) (g : E) :
    ‖ContinuousLinearMap.adjoint Q g‖ ≤ ‖Q g‖ := by
  rw [adjoint_backward_laplace_unitary_group U hU₀ hadd hnorm hcont hc P Q hP hQ]
  exact (norm_backward_laplace_unitary_group U hU₀ hadd hnorm hcont hc P Q hP hQ g).ge

/-- The backward Laplace transform `Q g = ∫ x in Ioi 0, exp (-c * x) • U (-x) g` of a strongly
continuous unitary group satisfies `c * ‖Q g‖ ^ 2 ≤ re ⟪g, Q g⟫`, as the forward one does by
`mul_norm_sq_laplace_semigroup_le_re_inner`. -/
theorem mul_norm_sq_backward_laplace_unitary_group_le_re_inner (U : ℝ → E →L[ℂ] E)
    (hU₀ : ∀ w, U 0 w = w) (hadd : ∀ x y w, U (x + y) w = U x (U y w))
    (hnorm : ∀ x w, ‖U x w‖ = ‖w‖) (hcont : ∀ w, Continuous fun x ↦ U x w) {c : ℝ}
    (hc : 0 < c) (g : E) :
    c * ‖∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U (-x) g‖ ^ 2 ≤
      (⟪g, ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U (-x) g⟫_ℂ).re := by
  have h₀ (w : E) : U (-0) w = w := by rw [neg_zero, hU₀]
  have hadd' (x y : ℝ) (_ : 0 ≤ x) (_ : 0 ≤ y) (w : E) :
      U (-(x + y)) w = U (-x) (U (-y) w) := by rw [neg_add, hadd]
  exact mul_norm_sq_laplace_semigroup_le_re_inner (fun x ↦ U (-x)) h₀ hadd'
    (fun x _ w ↦ (hnorm (-x) w).le) (fun w ↦ (hcont w).comp continuous_neg) hc g

end RiemannMasullo
