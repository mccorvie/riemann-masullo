module
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open Set MeasureTheory
open scoped Topology

/-- The Mellin transform of a Gaussian on the positive real ray. -/
public theorem mellin_gaussian {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.re) :
    mellin (fun t : ℝ ↦ (Real.exp (-a * t ^ 2) : ℂ)) z =
      (2 : ℂ)⁻¹ * ((a : ℂ) ^ (-(z / 2)) * Complex.Gamma (z / 2)) := by
  let f (t : ℝ) : ℂ := Real.exp (-t)
  have he : (fun t : ℝ ↦ (Real.exp (-a * t ^ 2) : ℂ)) = fun t : ℝ ↦ f (a * t ^ (2 : ℝ)) := by
    funext t
    simp [f]
  rw [he, mellin_comp_rpow (fun r ↦ f (a * r)) z 2, mellin_comp_mul_left f _ ha,
    Complex.Gamma_eq_integral (s := z / 2) (by simpa using hz), Complex.GammaIntegral_eq_mellin]
  simp [f, Complex.real_smul]

/-- Integration of an even complex function on the real line reduces to its positive ray. -/
public theorem integral_comp_abs_complex (f : ℝ → ℂ) :
    (∫ x : ℝ, f |x|) = 2 * ∫ x in Ioi (0 : ℝ), f x := by
  let g (x : ℝ) := f |x|
  have hpos : (∫ x in Ioi (0 : ℝ), g x) = ∫ x in Ioi (0 : ℝ), f x :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ congrArg f (abs_of_pos hx)
  have hneg : (∫ x in Iic (0 : ℝ), g x) = ∫ x in Ioi (0 : ℝ), g x := by
    simpa only [g, neg_zero, abs_neg] using (integral_comp_neg_Ioi 0 g).symm
  by_cases hg : Integrable g
  · have hu := setIntegral_union (f := g) (Iic_disjoint_Ioi (a := (0 : ℝ)) le_rfl) measurableSet_Ioi
        hg.integrableOn hg.integrableOn
    rw [Iic_union_Ioi, setIntegral_univ, hneg, hpos, ← two_mul] at hu
    exact hu
  · have h : ¬ IntegrableOn g (Ioi 0) := by
      intro h
      apply hg
      have h' : IntegrableOn g (Iic 0) := by
        have m : MeasurableEmbedding (fun x : ℝ ↦ -x) := (Homeomorph.neg ℝ).measurableEmbedding
        rw [← Measure.map_neg_eq_self (volume : Measure ℝ), m.integrableOn_map_iff]
        simpa [g, Function.comp_def, neg_preimage, neg_Iic, integrableOn_Ici_iff_integrableOn_Ioi] using h
      simpa [Iic_union_Ioi] using h'.union h
    rw [← hpos, integral_undef hg, integral_undef h, mul_zero]

/-- Polar integration of a complex-valued function of the radius. -/
public theorem Complex.integral_radial (f : ℝ → ℂ) :
    (∫ z : ℂ, f ‖z‖) = (2 * (Real.pi : ℂ)) * ∫ r in Ioi (0 : ℝ), (r : ℂ) * f r := by
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  calc
    _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, ((p.1 : ℂ) * f p.1) * 1 := by
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      dsimp only
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1, Complex.real_smul, mul_one]
    _ = (∫ r in Ioi (0 : ℝ), (r : ℂ) * f r) * ∫ _ in Ioo (-Real.pi) Real.pi, (1 : ℂ) := by
      rw [← setIntegral_prod_mul, Measure.volume_eq_prod]
    _ = _ := by
      rw [integral_const, measureReal_restrict_apply MeasurableSet.univ, univ_inter,
        Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]), Complex.real_smul, mul_one]
      push_cast
      ring
