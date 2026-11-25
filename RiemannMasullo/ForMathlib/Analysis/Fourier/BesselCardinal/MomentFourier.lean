module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.MomentEnergy
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! A finite centered exponential representation and its Fourier orthogonality. -/

@[expose] public noncomputable section
open Complex MeasureTheory Filter Finset
open scoped InnerProductSpace ComplexConjugate

namespace RiemannMasullo.CardinalMoment

/-- The local additive character with angular frequency `t` (no hidden factor of `2π`). -/
def wave (t x : ℝ) : ℂ := Complex.exp ((↑(t*x):ℂ)*I)

theorem norm_wave (t x : ℝ) : ‖wave t x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem hasDerivAt_wave (t x : ℝ) :
    HasDerivAt (wave t) (((t:ℂ)*I)*wave t x) x := by
  have hd : HasDerivAt (fun y : ℝ ↦ t*y) t x := by simpa using (hasDerivAt_id x).const_mul t
  have hh := (hd.ofReal_comp.mul_const I).cexp
  exact hh.congr_deriv (by dsimp [wave]; ring)

/-- A finite exponential sum in coordinates centered at `w`. -/
def centeredPolynomial (A : Finset ℝ) (w : ℝ) (c : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ z ∈ A, c z*wave (z-w) x

private def differentiatedCoeff (w : ℝ) (c : ℝ → ℂ) (z : ℝ) : ℂ :=
  c z*((↑(z-w):ℂ)*I)

private theorem polynomial_deriv (A : Finset ℝ) (w : ℝ) (c : ℝ → ℂ) (x : ℝ) :
    HasDerivAt (centeredPolynomial A w c) (centeredPolynomial A w (differentiatedCoeff w c) x) x := by
  have h := HasDerivAt.fun_sum (u := A) (fun z _ ↦ (hasDerivAt_wave (z-w) x).const_mul (c z))
  change HasDerivAt (fun y ↦ ∑ z ∈ A, c z*wave (z-w) y) _ x
  simpa only [centeredPolynomial,differentiatedCoeff,mul_assoc] using h

private theorem polynomial_continuous (A : Finset ℝ) (w : ℝ) (c : ℝ → ℂ) :
    Continuous (centeredPolynomial A w c) :=
  continuous_iff_continuousAt.mpr fun x ↦ (polynomial_deriv A w c x).continuousAt

private theorem polynomial_bound (A : Finset ℝ) (w : ℝ) (c : ℝ → ℂ) (x : ℝ) :
    ‖centeredPolynomial A w c x‖ ≤ ∑ z ∈ A, ‖c z‖ := by
  change ‖∑ z ∈ A, c z*wave (z-w) x‖ ≤ _
  simpa only [norm_mul,norm_wave,mul_one] using norm_sum_le A (fun z ↦ c z*wave (z-w) x)

private theorem integrable_bounded_inner {P U : ℝ → ℂ} {B : ℝ}
    (hP : Continuous P) (hU : Integrable U) (hB : ∀ x, ‖P x‖ ≤ B) :
    Integrable (fun x ↦ ⟪P x,U x⟫_ℝ) := by
  refine (hU.norm.const_mul B).mono'
    (continuous_inner.comp_aestronglyMeasurable (hP.aestronglyMeasurable.prodMk hU.aestronglyMeasurable))
    (.of_forall fun x ↦ ?_)
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _))

private theorem integral_polynomial_orthogonal (A : Finset ℝ) (w : ℝ) (b H : ℝ → ℂ)
    (hb : b w = 0) (hH : Integrable H)
    (hcard : ∀ z ∈ A, z ≠ w → (∫ x, conj (wave (z-w) x)*H x) = 0) :
    (∫ x, ⟪centeredPolynomial A w b x,H x⟫_ℝ) = 0 := by
  have hc (z : ℝ) : Continuous (wave (z-w)) :=
    continuous_iff_continuousAt.mpr fun x ↦ (hasDerivAt_wave _ x).continuousAt
  have hi (z : ℝ) : Integrable (fun x ↦ conj (wave (z-w) x)*H x) := by
    refine hH.norm.mono' (((Complex.continuous_conj.comp (hc z)).aestronglyMeasurable).mul
      hH.aestronglyMeasurable) (.of_forall fun x ↦ ?_)
    simp [norm_wave]
  have hj (z : ℝ) : Integrable (fun x ↦ ⟪b z*wave (z-w) x,H x⟫_ℝ) :=
    integrable_bounded_inner (B := ‖b z‖) (continuous_const.mul (hc z)) hH
      (fun x ↦ by simp [norm_wave])
  simp only [centeredPolynomial,sum_inner]
  rw [integral_finsetSum _ (fun z _ ↦ hj z)]
  apply Finset.sum_eq_zero
  intro z hz
  rcases eq_or_ne z w with rfl | hzw
  · simp [hb]
  · have he (x : ℝ) : ⟪b z*wave (z-w) x,H x⟫_ℝ =
        (conj (b z)*(conj (wave (z-w) x)*H x)).re := by
      rw [Complex.inner,map_mul]
      congr 1
      ring
    simp_rw [he]
    change (∫ x, RCLike.re (conj (b z)*(conj (wave (z-w) x)*H x))) = 0
    rw [integral_re ((hi z).const_mul (conj (b z))),integral_const_mul,hcard z hz hzw,mul_zero]
    rfl

/-- On a finite centered cardinal, the derivative of its representing numerator
is orthogonal in real pairing to the derivative of the profile. The off-center
Fourier values alone are needed. -/
theorem integral_differentiatedPolynomial_inner_eq_zero (A : Finset ℝ) (w : ℝ) (c H D : ℝ → ℂ)
    (hH : ∀ x, HasDerivAt H (D x) x) (hiH : Integrable H) (hiD : Integrable D)
    (hcard : ∀ z ∈ A, z ≠ w → (∫ x, conj (wave (z-w) x)*H x) = 0) :
    (∫ x, ⟪deriv (centeredPolynomial A w c) x,D x⟫_ℝ) = 0 := by
  let b := differentiatedCoeff w c
  let d := differentiatedCoeff w b
  have hp : deriv (centeredPolynomial A w c) = centeredPolynomial A w b :=
    funext fun x ↦ (polynomial_deriv A w c x).deriv
  have hh := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ))
    (u := centeredPolynomial A w b) (u' := centeredPolynomial A w d)
    (v := H) (v' := D) (fun x _ ↦ polynomial_deriv A w b x) (fun x _ ↦ hH x)
    (integrable_bounded_inner (polynomial_continuous A w b) hiD (polynomial_bound A w b))
    (integrable_bounded_inner (polynomial_continuous A w d) hiH (polynomial_bound A w d))
    (integrable_bounded_inner (polynomial_continuous A w b) hiH (polynomial_bound A w b))
  change (∫ x, ⟪centeredPolynomial A w b x,D x⟫_ℝ) = -∫ x, ⟪centeredPolynomial A w d x,H x⟫_ℝ at hh
  rw [hp,hh,integral_polynomial_orthogonal A w d H (by simp [d,differentiatedCoeff]) hiH hcard,neg_zero]

private theorem integrable_of_bounded_symbol {θ B : ℝ} (hθ : 1 ≤ θ) (U : ℝ → ℂ)
    (hU : Continuous U) (hB : ∀ x, symbol θ x*‖U x‖ ≤ B) :
    Integrable U ∧ Integrable (fun x ↦ symbol θ x*‖U x‖^2) := by
  have h₁ : Integrable U := by
    refine ((integrable_symbol_inv θ hθ).const_mul B).mono' hU.aestronglyMeasurable
      (.of_forall fun x ↦ ?_)
    rw [← div_eq_mul_inv,le_div_iff₀ (symbol_pos θ x),mul_comm]
    exact hB x
  refine ⟨h₁, (h₁.norm.const_mul B).mono' ?_ (.of_forall fun x ↦ ?_)⟩
  · have hc : Continuous (symbol θ) := continuous_iff_continuousAt.mpr fun x ↦
      (hasDerivAt_symbol θ x).continuousAt
    exact (hc.mul (hU.norm.pow 2)).aestronglyMeasurable
  · rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (symbol_pos θ x).le (sq_nonneg _)),pow_two,← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

/-- Finite Fourier numerators give all the regularity and integrability needed for
the first-moment calculation, uniformly in the physical coordinate. -/
theorem finite_profile_regular (A : Finset ℝ) (w θ : ℝ) (hθ : 1 ≤ θ) (c H : ℝ → ℂ)
    (hrep : ∀ x, symbol θ x • H x = centeredPolynomial A w c x) :
    Differentiable ℝ H ∧ Continuous (deriv H) ∧ Integrable H ∧ Integrable (deriv H) ∧
    Integrable (fun x ↦ symbol θ x*‖H x‖^2) ∧
    Integrable (fun x ↦ symbol θ x*‖deriv H x‖^2) ∧
    ∀ x, symbolSlope θ x • H x + symbol θ x • deriv H x = deriv (centeredPolynomial A w c) x := by
  let p := centeredPolynomial A w c
  let q := centeredPolynomial A w (differentiatedCoeff w c)
  have hp (x : ℝ) : HasDerivAt p (q x) x := polynomial_deriv A w c x
  have hm : Differentiable ℝ (symbol θ) := fun x ↦ (hasDerivAt_symbol θ x).differentiableAt
  have hm' : Continuous (symbolSlope θ) := continuous_iff_continuousAt.mpr fun x ↦
    (hasDerivAt_symbolSlope θ x).continuousAt
  have hpinv : H = fun x ↦ (symbol θ x)⁻¹ • p x := by
    funext x
    rw [show p x = symbol θ x • H x from (hrep x).symm,inv_smul_smul₀ (symbol_pos θ x).ne']
  have hdiff : Differentiable ℝ H := by
    rw [hpinv]
    exact (hm.inv fun x ↦ (symbol_pos θ x).ne').smul (fun x ↦ (hp x).differentiableAt)
  have hfun : (fun x ↦ symbol θ x • H x) = p := funext hrep
  have hsum (x : ℝ) : symbol θ x • deriv H x + symbolSlope θ x • H x = q x := by
    have hh := (hasDerivAt_symbol θ x).fun_smul (hdiff x).hasDerivAt
    rw [hfun] at hh
    exact hh.unique (hp x)
  have hiso (x : ℝ) : symbol θ x • deriv H x = q x - symbolSlope θ x • H x :=
    eq_sub_of_add_eq (hsum x)
  have hDrep : deriv H = fun x ↦ (symbol θ x)⁻¹ • (q x - symbolSlope θ x • H x) := by
    funext x
    rw [← hiso x,inv_smul_smul₀ (symbol_pos θ x).ne']
  have hDc : Continuous (deriv H) := by
    rw [hDrep]
    exact (hm.continuous.inv₀ fun x ↦ (symbol_pos θ x).ne').smul
      ((polynomial_continuous A w _).sub (hm'.smul hdiff.continuous))
  let B := ∑ z ∈ A, ‖c z‖
  let B' := ∑ z ∈ A, ‖differentiatedCoeff w c z‖
  have hb (x : ℝ) : symbol θ x*‖H x‖ ≤ B := by
    simpa only [← hrep x,norm_smul,Real.norm_eq_abs,abs_of_pos (symbol_pos θ x)] using polynomial_bound A w c x
  have hb' (x : ℝ) : symbol θ x*‖deriv H x‖ ≤ B'+(2*θ)*B := by
    have hθ₀ : 0 ≤ 2*θ := by linarith
    calc
      _ = ‖symbol θ x • deriv H x‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos (symbol_pos _ _)]
      _ ≤ ‖q x‖+‖symbolSlope θ x • H x‖ := by rw [hiso x]; exact norm_sub_le _ _
      _ ≤ B'+((2*θ)*symbol θ x)*‖H x‖ := by
        rw [norm_smul,Real.norm_eq_abs]
        exact add_le_add (polynomial_bound A w _ x)
          (mul_le_mul_of_nonneg_right (symbolSlope_abs_le θ x (by linarith)) (norm_nonneg _))
      _ ≤ _ := by rw [mul_assoc]; linarith only [mul_le_mul_of_nonneg_left (hb x) hθ₀]
  obtain ⟨hiH,hWH⟩ := integrable_of_bounded_symbol hθ H hdiff.continuous hb
  obtain ⟨hiD,hWD⟩ := integrable_of_bounded_symbol hθ (deriv H) hDc hb'
  refine ⟨hdiff,hDc,hiH,hiD,hWH,hWD,fun x ↦ ?_⟩
  rw [add_comm,hsum x,(hp x).deriv]

/-- Proposition 3 in centered physical Fourier coordinates. The hypotheses are
the finite exponential representation of the cardinal and its vanishing off the marked
site. They imply the precise moment identity and both sharp constants. -/
theorem finite_cardinal_firstMoment (A : Finset ℝ) (w θ : ℝ) (hθ : 1 ≤ θ) (c H : ℝ → ℂ)
    (hrep : ∀ x, symbol θ x • H x = centeredPolynomial A w c x)
    (hcard : ∀ z ∈ A, z ≠ w → (∫ x, conj (wave (z-w) x)*H x) = 0) :
    (∫ x, symbol θ x*‖deriv H x‖^2) = (∫ x, symbolCurvature θ x*‖H x‖^2)/2 ∧
    θ*(∫ x, symbol (θ-1) x*‖H x‖^2) ≤ ∫ x, symbol θ x*‖deriv H x‖^2 ∧
    (∫ x, symbol θ x*‖deriv H x‖^2) ≤ θ*(2*θ-1)*(∫ x, symbol (θ-1) x*‖H x‖^2) := by
  obtain ⟨hd,hc,hiH,hiD,hwH,hwD,he⟩ := finite_profile_regular A w θ hθ c H hrep
  apply firstMoment_of_stationarity hθ H (deriv H) (fun x ↦ (hd x).hasDerivAt)
    hc.aestronglyMeasurable hwH hwD
  simpa only [he] using integral_differentiatedPolynomial_inner_eq_zero A w c H (deriv H)
    (fun x ↦ (hd x).hasDerivAt) hiH hiD hcard

/-- On the width-zero one-jet range `1 ≤ θ ≤ 3/2`, the strong first moment costs
at most three times the squared weak energy. -/
theorem finite_cardinal_firstMoment_le_three (A : Finset ℝ) (w θ : ℝ) (hθ : 1 ≤ θ)
    (hθ' : θ ≤ 3/2) (c H : ℝ → ℂ)
    (hrep : ∀ x, symbol θ x • H x = centeredPolynomial A w c x)
    (hcard : ∀ z ∈ A, z ≠ w → (∫ x, conj (wave (z-w) x)*H x) = 0) :
    (∫ x, symbol θ x*‖deriv H x‖^2) ≤ 3*(∫ x, symbol (θ-1) x*‖H x‖^2) := by
  apply (finite_cardinal_firstMoment A w θ hθ c H hrep hcard).2.2.trans
  apply mul_le_mul_of_nonneg_right
  · nlinarith only [mul_nonneg (sub_nonneg.mpr hθ') (show 0 ≤ 2*θ+2 by linarith)]
  · exact integral_nonneg fun x ↦ mul_nonneg (symbol_pos _ _).le (sq_nonneg _)

end RiemannMasullo.CardinalMoment
