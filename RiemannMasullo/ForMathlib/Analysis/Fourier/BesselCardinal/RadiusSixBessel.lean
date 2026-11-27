module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.AngularGram
public import RiemannMasullo.ForMathlib.MeasureTheory.Function.LpSpace.ComplexInclusion
public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.RadiusSixLocalization

/-! # The Bessel weak norm of a localized Gram cardinal

The weakening map preserves the angular Fourier representative. The finite positive form
with reciprocal exponent `θ+1` is the exact squared weak norm of the finite cardinal.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped InnerProductSpace Matrix ENNReal

namespace RiemannMasullo.WeakCardinal

private theorem measure_order_le {s t : ℝ} (hst : s ≤ t) : sobolevMeasure s ≤ sobolevMeasure t := by
  apply withDensity_mono
  exact .of_forall fun x ↦ ENNReal.ofReal_le_ofReal <|
    Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x]) hst

private theorem weak_measure_le (r : ℝ) : sobolevMeasure (r-1) ≤ sobolevMeasure r :=
  measure_order_le (by linarith)

/-- The actual complex-linear inclusion from strong to weak Bessel order. -/
@[no_expose] def besselWeakening (r : ℝ) : Lp ℂ 2 (sobolevMeasure r) →L[ℂ] Lp ℂ 2 (sobolevMeasure (r-1)) :=
  complexLpInclusionOfMeasureLE (weak_measure_le r)

/-- Weakening preserves the frequency representative. -/
theorem besselWeakening_coeFn (r : ℝ) (f : Lp ℂ 2 (sobolevMeasure r)) :
    (besselWeakening r f : ℝ → ℂ) =ᵐ[sobolevMeasure (r-1)] f :=
  complexLpInclusionOfMeasureLE_coeFn (weak_measure_le r) f

/-- Strong-to-weak comparison has constant one for the genuine weighted norms. -/
theorem besselWeakening_norm_le (r : ℝ) : ‖besselWeakening r‖ ≤ 1 :=
  complexLpInclusionOfMeasureLE_norm_le (weak_measure_le r)

/-- Positive Bessel densities give an injective weakening map. -/
theorem besselWeakening_injective (r : ℝ) : Function.Injective (besselWeakening r) := by
  intro f g hfg
  have he : (f : ℝ → ℂ) =ᵐ[sobolevMeasure (r-1)] g :=
    (besselWeakening_coeFn r f).symm.trans (hfg ▸ besselWeakening_coeFn r g)
  exact Lp.ext ((ae_sobolevMeasure_iff r _).mpr ((ae_sobolevMeasure_iff (r-1) _).mp he))

/-- The weak image of a strong Riesz vector is the very same evaluation wave bundled in the weak space. -/
theorem besselWeakening_evaluationVector (r : ℝ) (hr : 1/2 < r) (w : ℝ) :
    besselWeakening r (evaluationVector r hr w) = evaluationVectorAt r (r-1) (by linarith) w := by
  apply Lp.ext
  have h1 : (evaluationVector r hr w : ℝ → ℂ) =ᵐ[sobolevMeasure r] evaluationWave r w :=
    evaluationVectorAt_coeFn r r (by linarith) w
  have h2 : (evaluationVector r hr w : ℝ → ℂ) =ᵐ[sobolevMeasure (r-1)] evaluationWave r w :=
    ae_mono (weak_measure_le r) h1
  exact (besselWeakening_coeFn _ _).trans (h2.trans (evaluationVectorAt_coeFn r (r-1) _ w).symm)

/-- The finite weak quadratic form is the exact norm of the weakened strong linear combination. -/
theorem besselWeakening_sum_norm_sq {ι : Type*} [Fintype ι] (r : ℝ) (hr : 1/2 < r)
    (site : ι → ℝ) (c : ι → ℂ) :
    ‖besselWeakening r (∑ i, c i • evaluationVector r hr (site i))‖ ^ 2 =
      (star c ⬝ᵥ (gramMatrix (r+1) site) *ᵥ c).re := by
  rw [map_sum]
  simp_rw [map_smul, besselWeakening_evaluationVector]
  simpa only [show 2*r-(r-1) = r+1 by ring] using
    (quadraticForm_eq_norm_sq r (r-1) (by linarith) site c).symm

/-- The weakening map sends the inverse-column cardinal to the canonical weak cardinal. -/
theorem besselWeakening_finiteGramCardinal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (hr : 1/2 < r) (site : ι → ℝ) (j : ι) :
    besselWeakening r (finiteGramCardinal (fun i ↦ evaluationVector r hr (site i)) j) =
      weakGramCardinal r hr site j := by
  simp only [finiteGramCardinal, weakGramCardinal, gram_evaluationVector, map_sum, map_smul,
    besselWeakening_evaluationVector]

/-- A solution of the finite strong interpolation system is the genuine finite Bessel minimum. -/
theorem isMinimumCardinal_of_gram_solution {ι : Type*} [Fintype ι] (r : ℝ) (hr : 1/2 < r)
    (site : ι → ℝ) (w : ℝ) (c : ι → ℂ)
    (hsolve : (gramMatrix r site) *ᵥ c = fun i ↦ if site i = w then 1 else 0) :
    IsMinimumCardinal (evaluationVector r hr) (Set.range site) w
      (∑ i, c i • evaluationVector r hr (site i)) := by
  have hg (i j : ι) :
      ⟪evaluationVector r hr (site i), evaluationVector r hr (site j)⟫_ℂ = gramMatrix r site i j := by
    exact congrArg (fun A : Matrix ι ι ℂ ↦ A i j) (gram_evaluationVector r hr site)
  apply isMinimumCardinal_finite_sum
  intro i
  calc
    _ = ∑ j, c j * gramMatrix r site i j := by simp_rw [inner_sum, inner_smul_right, hg]
    _ = (gramMatrix r site *ᵥ c) i := Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    _ = _ := congrFun hsolve i

end RiemannMasullo.WeakCardinal
