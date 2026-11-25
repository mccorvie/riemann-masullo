module

public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.RadiusSixCutoffLocalization

/-! The radius-six estimate is uniform over every finite enlargement of the local window. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace Matrix

namespace RiemannMasullo.WeakCardinal

/-- Weak mass from one inverse column of the finite interpolation Gram matrix. -/
def weakGramForm {ι : Type*} [Fintype ι] [DecidableEq ι] (θ : ℝ) (t : ι → ℝ) (w : ι) : ℝ :=
  let c (i : ι) := (gramMatrix θ t)⁻¹ i w
  (star c ⬝ᵥ (gramMatrix (θ+1) t) *ᵥ c).re

/-- The weak Gram form attached to a finite subset of an arbitrary ambient site type.
This definition fixes a single choice of equality on the finite index type. -/
def finiteSiteWeakForm {J : Type*} (θ : ℝ) (t : J → ℝ) (S : Finset J) (j : J) (hj : j ∈ S) : ℝ := by
  classical
  exact weakGramForm θ (fun i : S ↦ t i.val) ⟨j,hj⟩

private def finiteSiteDecEq {J : Type*} (S : Finset J) : DecidableEq S := by
  classical
  infer_instance

/-- The finite positive quadratic form is independent of the chosen decidable equality. -/
theorem finiteSiteWeakForm_eq {J : Type*} (θ : ℝ) (t : J → ℝ) (S : Finset J) (j : J) (hj : j ∈ S)
    [d : DecidableEq S] : finiteSiteWeakForm θ t S j hj = weakGramForm θ (fun i : S ↦ t i.val) ⟨j,hj⟩ := by
  have hd : d = finiteSiteDecEq S := Subsingleton.elim _ _
  subst d
  rfl

/-- Every finite enlargement containing all sites in the closed window obeys the same error
relative to the numerical local form. Only one order-`θ` multiplier is required. -/
theorem finiteWeakGram_radiusSix_of_multiplier {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {θ : ℝ} (hθ : 1 < θ) (hθ' : θ ≤ 3/2)
    (t : ι → ℝ) (q : κ → ℝ) (ht : Function.Injective t) (hq : Function.Injective q)
    (i : ι) (j : κ) (hij : q j = t i) (hwindow : range t = radiusSixSites (range q) (t i))
    (A : Lp ℂ 2 (sobolevMeasure θ) →L[ℂ] Lp ℂ 2 (sobolevMeasure θ)) (hA : ‖A‖ ≤ 13/48)
    (hAeval : ∀ (f : Lp ℂ 2 (sobolevMeasure θ)) x, x ∈ range q →
      (∫ ξ, phase x ξ * A f ξ ∂angularMeasure) =
        (scaledCutoffQuotient (t i) 6 x : ℂ) * (∫ ξ, phase x ξ * f ξ ∂angularMeasure)) :
    (1-radiusSixError)*Real.sqrt (weakGramForm θ t i) ≤ Real.sqrt (weakGramForm θ q j) ∧
      Real.sqrt (weakGramForm θ q j) ≤ (1+radiusSixError)*Real.sqrt (weakGramForm θ t i) := by
  let K := evaluationVector θ (by linarith : 1/2 < θ)
  let c (k : κ) := (gramMatrix θ q)⁻¹ k j
  let g := ∑ k, c k • K (q k)
  have hmin : IsMinimumCardinal K (range q) (t i) g := by
    apply isMinimumCardinal_of_gram_solution θ (by linarith) q (t i) c
    funext k
    rw [← hij]
    exact gramMatrix_mulVec_inverse_column θ (by linarith) hq k j
  obtain ⟨v, _, huniq, _, hlow, hupp⟩ := exists_fullMinimum_radiusSix_of_multiplier hθ hθ'
    (range q) t ht i hwindow A hA hAeval
  have he : ‖besselWeakening θ g‖ = Real.sqrt (weakGramForm θ q j) := by
    have hsq : ‖besselWeakening θ g‖ ^ 2 = weakGramForm θ q j :=
      besselWeakening_sum_norm_sq θ (by linarith) q c
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [← he, huniq g hmin]
  exact ⟨hlow, hupp⟩

end RiemannMasullo.WeakCardinal
