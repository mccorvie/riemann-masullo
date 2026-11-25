module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The Laplace transform of a contraction semigroup is accretive

Let `U` be a strongly continuous semigroup of contractions of a complex Hilbert space, and for
`c > 0` let `P g = ∫ x in Ioi 0, exp (-c * x) • U x g` be its Laplace transform, the resolvent
of its generator. Then `c * ‖P g‖ ^ 2 ≤ re ⟪g, P g⟫`
(`mul_norm_sq_laplace_semigroup_le_re_inner`). For the translations of `L²(ℝ)` this says that
convolution with the one-sided exponential `p x = exp (-c * x)`, `x > 0`, satisfies
`c * ‖p ⋆ g‖ ^ 2 ≤ re ⟪g, p ⋆ g⟫`, and it is proved here without the Fourier transform. -/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace RiemannMasullo

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The weighted orbit `x ↦ exp (-c * x) • U x g` of a strongly continuous family of
contractions is integrable on the positive half-line. -/
theorem integrableOn_exp_smul_orbit (U : ℝ → E →L[ℂ] E)
    (hle : ∀ x, 0 ≤ x → ∀ w, ‖U x w‖ ≤ ‖w‖) (hcont : ∀ w, Continuous fun x ↦ U x w)
    {c : ℝ} (hc : 0 < c) (g : E) (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun x ↦ Real.exp (-c * x) • U x g) (Ioi a) := by
  have hF : Continuous fun x : ℝ ↦ Real.exp (-c * x) • U x g :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul (hcont g)
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi a hc).mul_const ‖g‖)
    hF.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx ↦ ?_)
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_left (hle x (ha.trans (le_of_lt hx)) g) (Real.exp_pos _).le

/-- The Laplace transform `P g = ∫ x in Ioi 0, exp (-c * x) • U x g` of a strongly continuous
semigroup of contractions `U` of a Hilbert space satisfies `c * ‖P g‖ ^ 2 ≤ re ⟪g, P g⟫`. -/
theorem mul_norm_sq_laplace_semigroup_le_re_inner (U : ℝ → E →L[ℂ] E)
    (hU₀ : ∀ w, U 0 w = w)
    (hadd : ∀ x y, 0 ≤ x → 0 ≤ y → ∀ w, U (x + y) w = U x (U y w))
    (hle : ∀ x, 0 ≤ x → ∀ w, ‖U x w‖ ≤ ‖w‖) (hcont : ∀ w, Continuous fun x ↦ U x w)
    {c : ℝ} (hc : 0 < c) (g : E) :
    c * ‖∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U x g‖ ^ 2 ≤
      (⟪g, ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • U x g⟫_ℂ).re := by
  set F : ℝ → E := fun x ↦ Real.exp (-c * x) • U x g with hFdef
  set P : E := ∫ x in Ioi (0 : ℝ), F x with hPdef
  have hF : Continuous F :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul (hcont g)
  have hint : ∀ a : ℝ, 0 ≤ a → IntegrableOn F (Ioi a) := fun a ha ↦
    integrableOn_exp_smul_orbit U hle hcont hc g a ha
  -- The semigroup shifts the Laplace transform.
  have hshift : ∀ h : ℝ, 0 ≤ h → U h P = Real.exp (c * h) • ∫ x in Ioi h, F x := by
    intro h hh
    have h1 : U h P = ∫ x in Ioi (0 : ℝ), U h (F x) :=
      ((U h).integral_comp_comm (hint 0 le_rfl)).symm
    have h2 : ∀ x ∈ Ioi (0 : ℝ), U h (F x) = Real.exp (c * h) • F (x + h) := by
      intro x hx
      simp only [hFdef, (U h).map_smul_of_tower, smul_smul]
      rw [← hadd h x hh (le_of_lt hx), ← Real.exp_add, add_comm h x]
      congr 2
      ring
    rw [h1, setIntegral_congr_fun measurableSet_Ioi h2, integral_smul]
    congr 1
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
      ← integral_add_right_eq_self (fun y ↦ (Ioi h).indicator F y) h]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : 0 < x
    · have hx' : x + h ∈ Ioi h := by simpa using hx
      simp [indicator_of_mem, hx, hx']
    · have hx' : x + h ∉ Ioi h := by simpa using hx
      simp [indicator_of_notMem, hx, hx']
  -- Hence the contraction bound gives an inequality for the truncated transform.
  have hkey : ∀ h : ℝ, 0 < h →
      c * ‖P‖ ^ 2 ≤ (1 + c * h) ^ 2 * (⟪P, h⁻¹ • ∫ x in (0 : ℝ)..h, F x⟫_ℂ).re := by
    intro h hh
    set I : E := ∫ x in (0 : ℝ)..h, F x with hIdef
    have hsplit : I + ∫ x in Ioi h, F x = P :=
      intervalIntegral.integral_interval_add_Ioi (hint 0 le_rfl) (hint h hh.le)
    have htail : ∫ x in Ioi h, F x = P - I := by rw [← hsplit]; abel
    have hnorm : (1 + c * h) * ‖P - I‖ ≤ ‖P‖ := by
      have h1 : ‖U h P‖ ≤ ‖P‖ := hle h hh.le P
      rw [hshift h hh.le, htail, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le] at h1
      refine le_trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) h1
      linarith [Real.add_one_le_exp (c * h)]
    have hpos : 0 ≤ 1 + c * h := by positivity
    have hsq : (1 + c * h) ^ 2 * ‖P - I‖ ^ 2 ≤ ‖P‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (mul_nonneg hpos (norm_nonneg _)) hnorm 2
    rw [norm_sub_sq (𝕜 := ℂ)] at hsq
    have hsq' : (1 + c * h) ^ 2 * (‖P‖ ^ 2 - 2 * (⟪P, I⟫_ℂ).re + ‖I‖ ^ 2) ≤ ‖P‖ ^ 2 := hsq
    have hI :(⟪P, h⁻¹ • I⟫_ℂ).re = h⁻¹ * (⟪P, I⟫_ℂ).re := by
      rw [inner_smul_right_eq_smul, Complex.smul_re, smul_eq_mul]
    rw [hI]
    have hP2 : 0 ≤ ‖P‖ ^ 2 := sq_nonneg _
    have hc2 : 0 ≤ (1 + c * h) ^ 2 * ‖I‖ ^ 2 := by positivity
    have hmain : 2 * c * h * ‖P‖ ^ 2 ≤ 2 * (1 + c * h) ^ 2 * (⟪P, I⟫_ℂ).re := by
      nlinarith [hsq', hc2, mul_nonneg (mul_nonneg hc.le hc.le) (mul_nonneg (sq_nonneg h) hP2)]
    calc c * ‖P‖ ^ 2 = h⁻¹ * (2 * c * h * ‖P‖ ^ 2) / 2 := by
          field_simp
      _ ≤ h⁻¹ * (2 * (1 + c * h) ^ 2 * (⟪P, I⟫_ℂ).re) / 2 := by
          gcongr
      _ = (1 + c * h) ^ 2 * (h⁻¹ * (⟪P, I⟫_ℂ).re) := by ring
  -- Let the truncation tend to zero.
  have hderiv : HasDerivAt (fun u ↦ ∫ x in (0 : ℝ)..u, F x) (F 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable 0 0)
      (hF.stronglyMeasurableAtFilter _ _) hF.continuousAt
  have hF0 : F 0 = g := by simp [hFdef, hU₀]
  have hslope : Tendsto (fun h : ℝ ↦ h⁻¹ • ∫ x in (0 : ℝ)..h, F x) (𝓝[>] 0) (𝓝 g) := by
    have := hderiv.tendsto_slope_zero_right
    simpa [hF0] using this
  have hlim : Tendsto
      (fun h : ℝ ↦ (1 + c * h) ^ 2 * (⟪P, h⁻¹ • ∫ x in (0 : ℝ)..h, F x⟫_ℂ).re)
      (𝓝[>] 0) (𝓝 ((1 + c * 0) ^ 2 * (⟪P, g⟫_ℂ).re)) := by
    refine Tendsto.mul ?_ ?_
    · have hpoly : Continuous fun h : ℝ ↦ (1 + c * h) ^ 2 :=
        (continuous_const.add (continuous_const.mul continuous_id)).pow 2
      exact hpoly.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · exact (Complex.continuous_re.tendsto _).comp
        ((continuous_const.inner continuous_id).tendsto g |>.comp hslope)
  have hfinal : c * ‖P‖ ^ 2 ≤ (1 + c * 0) ^ 2 * (⟪P, g⟫_ℂ).re :=
    ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun h hh ↦ hkey h hh)
  have hsymm : (⟪g, P⟫_ℂ).re = (⟪P, g⟫_ℂ).re := inner_re_symm (𝕜 := ℂ) g P
  rw [hsymm]
  simpa using hfinal

end RiemannMasullo
