module

public import RiemannMasullo.Ch01_Introduction.Sec4_HeckePoisson

/-! # The Poisson kernel and logarithmic derivative mass for completed Hecke functions -/

@[expose] public noncomputable section

open NumberField

namespace RiemannMasullo.HeckePoisson

/-- The real Cauchy kernel at `σ + t i`, evaluated at the point `p`. -/
def poissonWeight (σ t : ℝ) (p : ℂ) : ℝ :=
  (σ - p.re) / ((σ - p.re) ^ 2 + (t - p.im) ^ 2)

/-- The logarithmic derivative mass of the completed Hecke function at `σ + t i`,
including half the discriminant–conductor logarithm and the principal pole terms. -/
def logDerivativeMass {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (σ t : ℝ) : ℝ := by
  classical
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  exact heckeLogDiscriminantConductor χ / 2 +
    (logDeriv (continuedCompletedHeckeL χ) s +
      (if χ = 1 then 1 / s + 1 / (s - 1) else 0)).re

/-- The kernel is the real part of the complex reciprocal displacement. -/
theorem poissonWeight_eq_re_inv (σ t : ℝ) (p : ℂ) :
    poissonWeight σ t p = ((((σ : ℂ) + (t : ℂ) * Complex.I) - p)⁻¹).re := by
  simp [poissonWeight, Complex.inv_re, Complex.normSq_apply, pow_two]

/-- At abscissa two this is the fixed Poisson weight used for the unit cells. -/
@[simp] theorem poissonWeight_two (t : ℝ) (p : ℂ) :
    poissonWeight 2 t p = weight t p := rfl

/-- Every positive divisor site contributes strictly positive weight at any abscissa
strictly to the right of one. -/
theorem poissonWeight_pos_of_site {F : Type*} [Field F] [NumberField F]
    {χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)} {σ : ℝ} (hσ : 1 < σ) (t : ℝ)
    (p : Site χ) : 0 < poissonWeight σ t p.val := by
  have hx : 0 < σ - p.val.re := sub_pos.mpr (lt_of_le_of_lt (siteStrip p).2 hσ)
  exact div_pos hx (add_pos_of_pos_of_nonneg (sq_pos_of_pos hx) (sq_nonneg _))

end RiemannMasullo.HeckePoisson
