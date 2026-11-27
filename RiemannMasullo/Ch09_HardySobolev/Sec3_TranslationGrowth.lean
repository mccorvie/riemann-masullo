module

public import RiemannMasullo.Ch09_HardySobolev.Sec3
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space

/-!
# Growth of translations on the symmetric strip

In the degree-zero space on the offset interval `[-1 / 2, 1 / 2]`, the squared
norm has density `max (exp (-t)) (exp t)` in the logarithmic coordinate.
Haar invariance gives an exact asymptotic for each translated vector.
-/

public noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace RiemannMasullo.Isolated

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]
variable (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)

set_option quotPrecheck false in
local notation "ℓ" => (fun h : G ↦ Real.log ((m h).val : ℝ))
local notation "W" => CompactIntervalSobolev μ ℓ (-(1 / 2)) (1 / 2) 0
local notation "T" => hardySobolevTranslation μ m (-(1 / 2)) (1 / 2) 0 (by norm_num) le_rfl

private def stripWeight (t : ℝ) := max (Real.exp (-t)) (Real.exp t)

private theorem stripWeight_eq (t : ℝ) :
    intervalSobolevDensity (-(1 / 2)) (1 / 2) 0 t = stripWeight t := by
  norm_num [intervalSobolevDensity, stripWeight]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem measurable_log_module : Measurable ℓ := Real.measurable_log.comp
  (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable

private theorem strip_norm_sq (u : W) :
    Integrable (fun h ↦ ‖u h‖ ^ 2 * stripWeight (ℓ h)) μ ∧
      ‖u‖ ^ 2 = ∫ h, ‖u h‖ ^ 2 * stripWeight (ℓ h) ∂μ := by
  let w (h : G) := stripWeight (ℓ h)
  have hw (h : G) : 0 ≤ w h := (Real.exp_nonneg _).trans (le_max_right _ _)
  have hm := measurable_log_module m
  have hd : Measurable (fun h ↦ ENNReal.ofReal (w h)) :=
    ((Real.continuous_exp.measurable.comp hm.neg).max (Real.continuous_exp.measurable.comp hm)).ennreal_ofReal
  have hfin : ∀ᵐ h ∂μ, ENNReal.ofReal (w h) < ∞ := .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hν : intervalSobolevMeasure μ ℓ (-(1 / 2)) (1 / 2) 0 =
      μ.withDensity (fun h ↦ ENNReal.ofReal (w h)) := by
    change μ.withDensity (fun h ↦ ENNReal.ofReal (intervalSobolevDensity (-(1 / 2)) (1 / 2) 0 (ℓ h))) = _
    simp_rw [stripWeight_eq]
    rfl
  have hs := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  let f (h : G) := ‖u h‖ ^ 2
  change Integrable f _ at hs
  rw [hν] at hs
  constructor
  · apply ((integrable_withDensity_iff_integrable_smul' hd hfin).mp hs).congr
    exact .of_forall fun h ↦ by
      change (ENNReal.ofReal (w h)).toReal * f h = f h * w h
      rw [ENNReal.toReal_ofReal (hw h), mul_comm]
  · rw [← L2.integral_sq_norm (𝕜 := ℂ)]
    change (∫ h, f h ∂intervalSobolevMeasure μ ℓ (-(1 / 2)) (1 / 2) 0) = _
    refine (congrArg (fun ν : Measure G ↦ ∫ h, f h ∂ν) hν).trans ?_
    rw [integral_withDensity_eq_integral_toReal_smul hd hfin]
    apply integral_congr_ae
    exact .of_forall fun h ↦ by
      change (ENNReal.ofReal (w h)).toReal * f h = f h * w h
      rw [ENNReal.toReal_ofReal (hw h), mul_comm]

private theorem translated_strip_norm_sq (g : G) (hg : ℓ g = 1) (u : W) (n : ℕ) :
    Real.exp (-(n : ℝ)) * ‖T (g ^ n) u‖ ^ 2 =
      ∫ h, ‖u h‖ ^ 2 * max (Real.exp (-2 * (n : ℝ) - ℓ h)) (Real.exp (ℓ h)) ∂μ := by
  rw [(strip_norm_sq μ m _).2]
  let F (h : G) := ‖u ((g ^ n)⁻¹ * h)‖ ^ 2 * stripWeight (ℓ h)
  have hF : (∫ h, ‖T (g ^ n) u h‖ ^ 2 * stripWeight (ℓ h) ∂μ) = ∫ h, F h ∂μ := by
    apply integral_congr_ae
    filter_upwards [hardySobolevTranslation_apply μ m (-(1 / 2)) (1 / 2) 0 (by norm_num)
      le_rfl (g ^ n) u] with h hh
    exact congrArg (fun z : ℂ ↦ ‖z‖ ^ 2 * stripWeight (ℓ h)) hh
  rw [hF, ← integral_mul_left_eq_self F (g ^ n), ← integral_const_mul]
  apply integral_congr_ae
  refine .of_forall fun h ↦ ?_
  change Real.log ((m g).val : ℝ) = 1 at hg
  have hadd : Real.log ((m (g ^ n * h)).val : ℝ) = n + Real.log ((m h).val : ℝ) := by
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.mpr (m (g ^ n)).ne_zero) (NNReal.coe_ne_zero.mpr (m h).ne_zero),
      map_pow, Units.val_pow_eq_pow_val, NNReal.coe_pow, Real.log_pow, hg, mul_one]
  dsimp only [F]
  rw [inv_mul_cancel_left, hadd]
  rw [mul_left_comm, stripWeight, mul_max_of_nonneg _ _ (Real.exp_nonneg _),
    ← Real.exp_add, ← Real.exp_add]
  ring_nf

private theorem strip_endpoint_integrable (u : W) :
    Integrable (fun h ↦ ‖u h‖ ^ 2 * Real.exp (ℓ h)) μ := by
  have hfull := strip_norm_sq μ m u
  have hm := measurable_log_module m
  have hpos (h : G) : 0 ≤ ‖u h‖ ^ 2 * Real.exp (ℓ h) := by positivity
  apply hfull.1.mono' (((Lp.stronglyMeasurable u).measurable.norm.pow_const 2).mul
    (Real.continuous_exp.measurable.comp hm)).aestronglyMeasurable
  exact .of_forall fun h ↦ by
    change ‖‖u h‖ ^ 2 * Real.exp (ℓ h)‖ ≤ _
    rw [Real.norm_of_nonneg (hpos h)]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg _)

/-- The right endpoint mass is finite and strictly positive for every nonzero vector. -/
theorem hardySobolevTranslation_endpointMass_pos {u : W} (hu : u ≠ 0) :
    0 < ∫ h, ‖u h‖ ^ 2 * Real.exp (ℓ h) ∂μ := by
  have hfull := strip_norm_sq μ m u
  have hpart := strip_endpoint_integrable μ m u
  have hpos (h : G) : 0 ≤ ‖u h‖ ^ 2 * Real.exp (ℓ h) := by positivity
  apply lt_of_le_of_ne (integral_nonneg hpos)
  intro hz
  have he := (integral_eq_zero_iff_of_nonneg hpos hpart).mp hz.symm
  have hall : (fun h ↦ ‖u h‖ ^ 2 * stripWeight (ℓ h)) =ᵐ[μ] 0 := by
    filter_upwards [he] with h hh
    change ‖u h‖ ^ 2 * Real.exp (ℓ h) = 0 at hh
    simp only [(mul_eq_zero.mp hh).resolve_right (Real.exp_pos _).ne', zero_mul, Pi.zero_apply]
  have hn : ‖u‖ ^ 2 = 0 := hfull.2.trans ((integral_congr_ae hall).trans (by simp))
  exact hu (norm_eq_zero.mp (by nlinarith [norm_nonneg u] : ‖u‖ = 0))

/-- Every positive power has normalized squared norm between the endpoint mass
and that mass plus an exponentially small remainder. -/
theorem hardySobolevTranslation_sq_bounds (g : G) (hg : ℓ g = 1) (u : W) (n : ℕ) :
    let mass := ∫ h, ‖u h‖ ^ 2 * Real.exp (ℓ h) ∂μ
    mass ≤ Real.exp (-(n : ℝ)) * ‖T (g ^ n) u‖ ^ 2 ∧
      Real.exp (-(n : ℝ)) * ‖T (g ^ n) u‖ ^ 2 ≤ mass + Real.exp (-2 * (n : ℝ)) * ‖u‖ ^ 2 := by
  intro mass
  let c := Real.exp (-2 * (n : ℝ))
  let D (h : G) := ‖u h‖ ^ 2 * max (Real.exp (-2 * (n : ℝ) - ℓ h)) (Real.exp (ℓ h))
  let E (h : G) := ‖u h‖ ^ 2 * Real.exp (ℓ h)
  let B (h : G) := ‖u h‖ ^ 2 * stripWeight (ℓ h)
  have hE := strip_endpoint_integrable μ m u
  have hB := strip_norm_sq μ m u
  have hdom (h : G) : D h ≤ E h + c * B h := by
    dsimp only [D, E, B, c]
    rw [show -2 * (n : ℝ) - ℓ h = -2 * (n : ℝ) + (-ℓ h) by ring, Real.exp_add]
    rw [mul_left_comm (Real.exp _) (‖u h‖ ^ 2), ← mul_add]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply max_le
    · exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.exp_nonneg _)).trans
        (le_add_of_nonneg_left (Real.exp_nonneg _))
    · exact le_add_of_nonneg_right (mul_nonneg (Real.exp_nonneg _) ((Real.exp_nonneg _).trans (le_max_right _ _)))
  have hDpos (h : G) : 0 ≤ D h := mul_nonneg (sq_nonneg _) ((Real.exp_nonneg _).trans (le_max_right _ _))
  have hmajor : Integrable (fun h ↦ E h + c * B h) μ := hE.add (hB.1.const_mul c)
  have hD : Integrable D μ := by
    have hm := measurable_log_module m
    apply hmajor.mono' (by
      have hu := (Lp.stronglyMeasurable u).measurable
      dsimp [D]
      fun_prop)
    exact .of_forall fun h ↦ by rw [Real.norm_of_nonneg (hDpos h)]; exact hdom h
  rw [translated_strip_norm_sq μ m g hg u n]
  change mass ≤ ∫ h, D h ∂μ ∧ (∫ h, D h ∂μ) ≤ _
  constructor
  · exact integral_mono hE hD fun h ↦ mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg _)
  · calc
      _ ≤ ∫ h, E h + c * B h ∂μ := integral_mono hD hmajor hdom
      _ = _ := by rw [integral_add hE (hB.1.const_mul c), integral_const_mul, ← hB.2]

/-- The normalized squared norm converges to the right endpoint mass. -/
theorem hardySobolevTranslation_sq_tendsto (g : G) (hg : ℓ g = 1) (u : W) :
    Tendsto (fun n : ℕ ↦ Real.exp (-(n : ℝ)) * ‖T (g ^ n) u‖ ^ 2) atTop
      (𝓝 (∫ h, ‖u h‖ ^ 2 * Real.exp (ℓ h) ∂μ)) := by
  have hz : Tendsto (fun n : ℕ ↦ Real.exp (-2 * (n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (tendsto_const_nhds (x := ∫ h, ‖u h‖ ^ 2 * Real.exp (ℓ h) ∂μ)).add (hz.mul_const (‖u‖ ^ 2)))
  · intro n
    exact (hardySobolevTranslation_sq_bounds μ m g hg u n).1
  · intro n
    simpa only [neg_mul] using (hardySobolevTranslation_sq_bounds μ m g hg u n).2

/-- At or below the half-width, a nonzero ambient vector cannot have arbitrarily
small scaled translates, even when the translating power may depend on the tolerance. -/
theorem hardySobolevTranslation_no_ambient_returns (g : G) (hg : ℓ g = 1)
    {u : W} (hu : u ≠ 0) {α : ℝ} (hα : α ≤ 1 / 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, ε ≤ Real.exp (-α * (n : ℝ)) * ‖T (g ^ n) u‖ := by
  let C := ∫ h, ‖u h‖ ^ 2 * Real.exp (ℓ h) ∂μ
  have hC : 0 < C := hardySobolevTranslation_endpointMass_pos μ m hu
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, fun n ↦ ?_⟩
  have hsmall : Real.sqrt C ≤ Real.exp (-(n : ℝ) / 2) * ‖T (g ^ n) u‖ := by
    apply Real.sqrt_le_iff.mpr ⟨mul_nonneg (Real.exp_nonneg _) (norm_nonneg _), ?_⟩
    rw [mul_pow, ← Real.exp_nat_mul]
    convert (hardySobolevTranslation_sq_bounds μ m g hg u n).1 using 2
    congr 1
    push_cast
    ring
  exact hsmall.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
    (by nlinarith [mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg n (α := ℝ))])) (norm_nonneg _))

end RiemannMasullo.Isolated
