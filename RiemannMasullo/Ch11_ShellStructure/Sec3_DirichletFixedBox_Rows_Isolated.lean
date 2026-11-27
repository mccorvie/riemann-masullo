module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Mellin_Isolated
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Nontrivial primitive Dirichlet characters in fixed Fourier boxes (Rows)

Strip Sobolev space embedding and normalized row functionals for primitive `χ`.

Nothing outside the `Sec3_DirichletFixedBox*` / `Sec3_RatBridge*` isolated stack imports this module.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField RiemannMasullo Set Topology
open scoped BigOperators ContDiff FourierTransform NNReal Real SchwartzMap

namespace RiemannMasullo.Isolated

section MellinAndStripRows

theorem stripDensity_pos (a b s x : ℝ) : 0 < intervalSobolevDensity a b s x :=
  mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)

theorem stripDensity_continuous (a b s : ℝ) :
    Continuous (intervalSobolevDensity a b s) := by
  unfold intervalSobolevDensity
  refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun x ↦ Or.inl ?_)
  positivity

private theorem isHalfLineRapid_memLp_strip {U : ℝ → ℂ} (hU : IsHalfLineRapid U)
    {α s : ℝ} (_hα : 0 ≤ α) (_hs : 0 ≤ s) :
    MemLp U 2 (intervalSobolevMeasure volume id (-α) α s false) := by
  let ρ := intervalSobolevDensity (-α) α s
  have hρc : Continuous ρ := stripDensity_continuous (-α) α s
  have hρp : ∀ x, 0 < ρ x := stripDensity_pos (-α) α s
  have hmeas : AEStronglyMeasurable U (intervalSobolevMeasure volume id (-α) α s false) :=
    hU.1.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  refine (integrable_withDensity_iff hρc.measurable.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2 ?_
  have hrew : (fun x : ℝ ↦ ‖U x‖ ^ 2 * (ENNReal.ofReal (ρ x)).toReal) =
      fun x : ℝ ↦ ‖U x‖ ^ 2 * ρ x := funext fun x ↦ by
    rw [ENNReal.toReal_ofReal (hρp x).le]
  rw [hrew]
  obtain ⟨hcont, B, hsupp, hdec⟩ := hU
  let n : ℕ := Nat.ceil (s / 2)
  have hsn : s / 2 ≤ (n : ℝ) := Nat.le_ceil (s / 2)
  let M : ℝ := α + 2
  obtain ⟨C, hC, hbd⟩ := hdec M
  let C1 : ℝ := C ^ 2 * (Real.exp (2 * |B| - B) + Real.exp (-B)) *
    ((2 * n).factorial : ℝ) * (2 : ℝ) ^ n
  have hmeas_sq : AEStronglyMeasurable (fun x : ℝ ↦ ‖U x‖ ^ 2 * ρ x) volume :=
    ((hcont.norm.pow 2).mul hρc).aestronglyMeasurable
  -- Elementary bound: `(1 + x^2)^n ≤ (2 * (1 + |x|^(2n)))`? Even cleaner: `|x|^j` bound!
  -- Actually for every `x : ℝ`, `(1 + x^2)^(s/2) ≤ (1 + x^2)^n ≤ (2 * max 1 (x^2))^n = 2^n * max 1 (|x|^(2*n)) ≤ 2^n * (1 + |x|^(2*n))`,
  -- and `1 + |x|^(2*n) ≤ 1 + (2n)! * exp |x| ≤ (1 + (2n)!) * exp (x + 2 * |B|)` for `x ≥ B`.
  let C2 : ℝ := C ^ 2 * (1 + ((2 * n).factorial : ℝ)) * (2 : ℝ) ^ n *
    (Real.exp (2 * |B|) + Real.exp (2 * |B|)) * Real.exp (max (-(2 * α * B)) (2 * α * B))
  -- Wait: simpler! Since `‖U x‖ ≤ C * exp(-(α + 2) * x)` for `x ≥ B`:
  -- `‖U x‖^2 * max (exp(-2 α x)) (exp(2 α x)) = (‖U x‖ * exp(α x)) * (‖U x‖ * exp(α x))`? Not quite `-2 α x`.
  -- Notice `max (exp (-2 α x)) (exp (2 α x)) ≤ exp (-2 α x) + exp (2 α x)` and `‖U x‖ ≤ C * exp (-(α + 2) x)` gives
  -- `‖U x‖^2 * exp (±2 α x) ≤ C^2 * exp ((-2 α - 4 ± 2 α) x) ≤ C^2 * (exp(-4 x) + exp((-4 α - 4) x))`.
  -- On `x ≥ B`: `-4 α x ≤ 4 α |B|` (since `α ≥ 0` and `-x ≤ -B ≤ |B|`), and `-x ≤ -B ≤ |B|` so `exp(-4 x) ≤ exp(-x) * exp(3 |B|)`.
  -- So `‖U x‖^2 * max(exp(-2 α x), exp(2 α x)) ≤ 2 * C^2 * exp(4 α |B| + 3 |B|) * exp(-x)`!
  -- Let's check: `-3 x + (-x)` when `x ≥ B` gives `-3 x ≤ -3 B ≤ 3 |B|`, AND `1 + x^2 ≤ 1 + |x|^(2n)` gives `≤ (1 + (2n)!) * exp(x + 2|B|)` —Wait: `-4 x + x = -3 x = -2 x - x ≤ 2 |B| - x`!
  -- Even better: `M := α + 3`!! With `M = α + 3`:
  -- `-2 M + 2 α = -6` and `-2 M - 2 α = -4 α - 6`, so `-4 α x ≤ 4 α |B|`, and `+ x` leaves `-5 x ≤ 5 |B| - x`!
  obtain ⟨C', hC', hbd'⟩ := hdec (α + 3)
  let K : ℝ := C' ^ 2 * 2 * (2 : ℝ) ^ n * (1 + ((2 * n).factorial : ℝ)) *
    Real.exp (4 * α * |B| + 7 * |B|)
  have hdom_int : Integrable (fun x : ℝ ↦ Set.indicator (Set.Ici B) (fun x : ℝ ↦ K * Real.exp (-x)) x) volume :=
    IntegrableOn.integrable_indicator
      ((integrableOn_Ici_iff_integrableOn_Ioi (f := fun x : ℝ ↦ Real.exp (-x))).mpr
        (integrableOn_exp_neg_Ioi B) |>.const_mul K)
      measurableSet_Ici
  refine hdom_int.mono' hmeas_sq (Filter.Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x < B
  · rw [hsupp x hx, norm_zero, sq, zero_mul, zero_mul, Real.norm_of_nonneg le_rfl]
    exact Set.indicator_nonneg (fun _ _ ↦ by positivity) x
  · have hxB : B ≤ x := le_of_not_gt hx
    rw [Set.indicator_of_mem hxB, Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hρp x).le)]
    have h1x : (1 : ℝ) ≤ 1 + x ^ 2 := by linarith [sq_nonneg x]
    have hpow_le : (1 + x ^ 2) ^ (s / 2) ≤ (2 : ℝ) ^ n * (1 + |x| ^ (2 * n)) := by
      have h1 : (1 + x ^ 2) ^ (s / 2) ≤ (1 + x ^ 2) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le h1x hsn
      rw [Real.rpow_natCast] at h1
      have h2 : 1 + x ^ 2 ≤ 2 * max 1 (x ^ 2) := by
        have hm1 : 1 ≤ max 1 (x ^ 2) := le_max_left _ _
        have hm2 : x ^ 2 ≤ max 1 (x ^ 2) := le_max_right _ _
        linarith
      have h3 : (1 + x ^ 2) ^ n ≤ (2 * max 1 (x ^ 2)) ^ n := pow_le_pow_left₀ (by positivity) h2 n
      have h4 : (max 1 (x ^ 2)) ^ n ≤ 1 + |x| ^ (2 * n) := by
        rcases le_total 1 (x ^ 2) with hx1 | hx1
        · rw [max_eq_right hx1, ← sq_abs, ← pow_mul, mul_comm 2 n]
          linarith
        · rw [max_eq_left hx1, one_pow]
          linarith [pow_nonneg (abs_nonneg x) (2 * n)]
      nlinarith [mul_pow (2 : ℝ) (max 1 (x ^ 2)) n, h1, h3, h4, pow_pos (by positivity : (0 : ℝ) < 2) n]
    have hexp_abs : |x| ≤ x + 2 * |B| := by
      rcases le_total 0 x with hx0 | hx0
      · rw [abs_of_nonneg hx0]; linarith [abs_nonneg B]
      · rw [abs_of_nonpos hx0]; linarith [neg_le_abs B]
    have hpoly_exp : 1 + |x| ^ (2 * n) ≤ (1 + ((2 * n).factorial : ℝ)) * Real.exp (x + 2 * |B|) := by
      have hkpos : (0 : ℝ) < ((2 * n).factorial : ℝ) := by positivity
      have hfac := (div_le_iff₀ hkpos).mp (Real.pow_div_factorial_le_exp |x| (abs_nonneg x) (2 * n))
      have hfac' : |x| ^ (2 * n) ≤ ((2 * n).factorial : ℝ) * Real.exp |x| := hfac.trans_eq (mul_comm _ _)
      have h1exp : 1 ≤ Real.exp |x| := Real.one_le_exp (abs_nonneg x)
      have heab : Real.exp |x| ≤ Real.exp (x + 2 * |B|) := Real.exp_le_exp.mpr hexp_abs
      nlinarith
    have hU2 : ‖U x‖ ^ 2 ≤ C' ^ 2 * Real.exp (-(2 * (α + 3)) * x) := by
      calc ‖U x‖ ^ 2 ≤ (C' * Real.exp (-(α + 3) * x)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hbd' x hxB) 2
        _ = C' ^ 2 * Real.exp (-(2 * (α + 3)) * x) := by
            rw [mul_pow, ← Real.exp_nat_mul]
            congr 2
            push_cast
            ring
    have hexp_max : max (Real.exp (2 * (-α) * x)) (Real.exp (2 * α * x)) ≤
        Real.exp (-2 * α * x) + Real.exp (2 * α * x) := by
      have hexp_neg : Real.exp (2 * (-α) * x) = Real.exp (-2 * α * x) := by congr 1; ring
      rw [hexp_neg]
      exact max_le (le_add_of_nonneg_right (Real.exp_pos _).le) (le_add_of_nonneg_left (Real.exp_pos _).le)
    have h_neg_x : -x ≤ |B| := by linarith [neg_le_abs B]
    have hexp_ctrl : Real.exp (-(2 * (α + 3)) * x) * (Real.exp (-2 * α * x) + Real.exp (2 * α * x)) *
        Real.exp (x + 2 * |B|) ≤ 2 * Real.exp (4 * α * |B| + 7 * |B|) * Real.exp (-x) := by
      have h1 : Real.exp (-(2 * (α + 3)) * x) * Real.exp (-2 * α * x) * Real.exp (x + 2 * |B|) ≤
          Real.exp (4 * α * |B| + 7 * |B|) * Real.exp (-x) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h4x : 4 * (-x) ≤ 4 * |B| := mul_le_mul_of_nonneg_left h_neg_x (by norm_num)
        have hax : 4 * α * (-x) ≤ 4 * α * |B| := mul_le_mul_of_nonneg_left h_neg_x (by positivity)
        linarith [abs_nonneg B]
      have h2 : Real.exp (-(2 * (α + 3)) * x) * Real.exp (2 * α * x) * Real.exp (x + 2 * |B|) ≤
          Real.exp (4 * α * |B| + 7 * |B|) * Real.exp (-x) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h4x : 4 * (-x) ≤ 4 * |B| := mul_le_mul_of_nonneg_left h_neg_x (by norm_num)
        have hab : 0 ≤ 4 * α * |B| := by positivity
        linarith [abs_nonneg B]
      nlinarith
    have hρ_le : ρ x ≤ (Real.exp (-2 * α * x) + Real.exp (2 * α * x)) *
        ((2 : ℝ) ^ n * ((1 + ((2 * n).factorial : ℝ)) * Real.exp (x + 2 * |B|))) := by
      dsimp [ρ, intervalSobolevDensity]
      exact mul_le_mul hexp_max (hpow_le.trans (mul_le_mul_of_nonneg_left hpoly_exp (by positivity)))
        (by positivity) (by positivity)
    calc ‖U x‖ ^ 2 * ρ x
        ≤ (C' ^ 2 * Real.exp (-(2 * (α + 3)) * x)) *
            ((Real.exp (-2 * α * x) + Real.exp (2 * α * x)) *
              ((2 : ℝ) ^ n * ((1 + ((2 * n).factorial : ℝ)) * Real.exp (x + 2 * |B|)))) :=
          mul_le_mul hU2 hρ_le (hρp x).le (by positivity)
      _ = C' ^ 2 * (2 : ℝ) ^ n * (1 + ((2 * n).factorial : ℝ)) *
            (Real.exp (-(2 * (α + 3)) * x) * (Real.exp (-2 * α * x) + Real.exp (2 * α * x)) *
              Real.exp (x + 2 * |B|)) := by ring
      _ ≤ C' ^ 2 * (2 : ℝ) ^ n * (1 + ((2 * n).factorial : ℝ)) *
            (2 * Real.exp (4 * α * |B| + 7 * |B|) * Real.exp (-x)) := by
            gcongr
      _ = K * Real.exp (-x) := by dsimp [K]; ring

/-- Fixed-box logarithmic profiles belong to the strip-Sobolev `L²` space `CompactIntervalSobolev`. -/
theorem twistedHalfLogProfile_memLp {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {f : 𝓢(ℝ, ℂ)} (hf : IsDirichletFixedBoxTest χ X f) :
    MemLp (twistedHalfLogProfile χ f) 2 (intervalSobolevMeasure volume id (-α) α s false) :=
  isHalfLineRapid_memLp_strip (isHalfLineRapid_twistedHalfLogProfile hχ hN hX hf) hα hs

/-- Depleted fixed-box logarithmic profiles belong to `CompactIntervalSobolev`. -/
theorem dirichletDeplete_memLp {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, 0 < q)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {f : 𝓢(ℝ, ℂ)} (hf : IsDirichletFixedBoxTest χ X f) :
    MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f)) 2
      (intervalSobolevMeasure volume id (-α) α s false) :=
  isHalfLineRapid_memLp_strip
    (isHalfLineRapid_dirichletDeplete χ T hT (isHalfLineRapid_twistedHalfLogProfile hχ hN hX hf)) hα hs

theorem halfLineMellinJet_memLp (α s B : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (k : ℕ) (t : ℝ) :
    MemLp (Set.indicator (Set.Ici B) fun x : ℝ ↦
        (x : ℂ) ^ k * Complex.exp (((t : ℂ) * Complex.I - 1 / 2 : ℂ) * (x : ℂ)))
      2 (intervalSobolevMeasure volume id (-α) α s true) := by
  let g : ℝ → ℂ := Set.indicator (Set.Ici B) fun x : ℝ ↦
    (x : ℂ) ^ k * Complex.exp (((t : ℂ) * Complex.I - 1 / 2 : ℂ) * (x : ℂ))
  let ρ := intervalSobolevDensity (-α) α s
  have hρc : Continuous ρ := stripDensity_continuous (-α) α s
  have hρp : ∀ x, 0 < ρ x := stripDensity_pos (-α) α s
  have hρ_ge_one : ∀ x : ℝ, 1 ≤ ρ x := fun x ↦ by
    dsimp [ρ, intervalSobolevDensity]
    have hmax1 : 1 ≤ max (Real.exp (2 * (-α) * x)) (Real.exp (2 * α * x)) := by
      rcases le_total 0 x with hx | hx
      · exact le_max_of_le_right (Real.one_le_exp (by nlinarith))
      · exact le_max_of_le_left (Real.one_le_exp (by nlinarith))
    have hpow1 : 1 ≤ (1 + x ^ 2) ^ (s / 2) :=
      Real.one_le_rpow (by linarith [sq_nonneg x]) (by linarith)
    nlinarith
  have hm0 : Measurable g :=
    ((continuous_ofReal.pow k).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).measurable.indicator
      measurableSet_Ici
  have hmeas : AEStronglyMeasurable g (intervalSobolevMeasure volume id (-α) α s true) :=
    hm0.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  dsimp only [intervalSobolevMeasure]
  simp only [↓reduceIte]
  refine (integrable_withDensity_iff hρc.measurable.inv.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2 ?_
  have hrew : (fun x : ℝ ↦ ‖g x‖ ^ 2 * (ENNReal.ofReal (ρ⁻¹ x)).toReal) =
      fun x : ℝ ↦ ‖g x‖ ^ 2 * (ρ x)⁻¹ := funext fun x ↦ by
    change ‖g x‖ ^ 2 * (ENNReal.ofReal (ρ x)⁻¹).toReal = ‖g x‖ ^ 2 * (ρ x)⁻¹
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (hρp x).le)]
  rw [hrew]
  let K : ℝ := ((2 * k).factorial : ℝ) * (2 : ℝ) ^ (2 * k) * Real.exp |B|
  have hdom_int : Integrable (fun x : ℝ ↦ Set.indicator (Set.Ici B) (fun x : ℝ ↦ K * Real.exp (-(1 / 2 : ℝ) * x)) x) volume := by
    have hi := ((integrableOn_Ici_iff_integrableOn_Ioi (f := fun x : ℝ ↦
      K * Complex.exp (((-(1 / 2 : ℝ) : ℝ) : ℂ) * (x : ℂ)))).mpr
      ((integrableOn_exp_mul_complex_Ioi (a := ((-(1 / 2 : ℝ) : ℝ) : ℂ)) (by simp) B).const_mul K)).norm
    refine (IntegrableOn.congr_fun hi (fun x _ ↦ ?_) measurableSet_Ici).integrable_indicator measurableSet_Ici
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Complex.norm_exp]
    simp [Complex.mul_re]
  have hmeas_sq : AEStronglyMeasurable (fun x : ℝ ↦ ‖g x‖ ^ 2 * (ρ x)⁻¹) volume :=
    ((hm0.norm.pow_const 2).mul hρc.measurable.inv).aestronglyMeasurable
  refine hdom_int.mono' hmeas_sq (Filter.Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x < B
  · have hg0 : g x = 0 := Set.indicator_of_notMem (not_le.mpr hx) _
    rw [hg0, norm_zero, sq, zero_mul, zero_mul, Real.norm_of_nonneg le_rfl]
    exact Set.indicator_nonneg (fun _ _ ↦ by positivity) x
  · have hxB : B ≤ x := le_of_not_gt hx
    have hρinv : (ρ x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hρ_ge_one x)
    rw [Set.indicator_of_mem hxB, Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (hρp x).le))]
    have hgx_norm : ‖g x‖ ^ 2 = |x| ^ (2 * k) * Real.exp (-x) := by
      dsimp [g]
      rw [Set.indicator_of_mem hxB, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_exp, mul_pow, ← pow_mul, mul_comm k 2, ← Real.exp_nat_mul]
      have hre : (((t : ℂ) * Complex.I - 1 / 2 : ℂ) * (x : ℂ)).re = -(1 / 2 : ℝ) * x := by
        simp [mul_re]
      rw [hre]
      congr 2
      have harg : (2 : ℕ) * (-(1 / 2 : ℝ) * x) = -x := by push_cast; ring
      exact harg
    have hpoly_exp : |x| ^ (2 * k) ≤ ((2 * k).factorial : ℝ) * (2 : ℝ) ^ (2 * k) * Real.exp (|x| / 2) := by
      have hkpos : (0 : ℝ) < ((2 * k).factorial : ℝ) := by positivity
      have hfac := (div_le_iff₀ hkpos).mp (Real.pow_div_factorial_le_exp (|x| / 2) (by positivity) (2 * k))
      have hdiv_pow : |x| ^ (2 * k) = (2 : ℝ) ^ (2 * k) * (|x| / 2) ^ (2 * k) := by
        rw [← mul_pow]
        congr 1
        ring
      have hmul := mul_le_mul_of_nonneg_left hfac (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * k))
      rw [hdiv_pow]
      calc (2 : ℝ) ^ (2 * k) * (|x| / 2) ^ (2 * k)
          ≤ (2 : ℝ) ^ (2 * k) * (Real.exp (|x| / 2) * ((2 * k).factorial : ℝ)) := hmul
        _ = ((2 * k).factorial : ℝ) * (2 : ℝ) ^ (2 * k) * Real.exp (|x| / 2) := by ring
    have hexp_half : Real.exp (|x| / 2) * Real.exp (-x) ≤ Real.exp |B| * Real.exp (-(1 / 2 : ℝ) * x) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rcases le_total 0 x with hx0 | hx0
      · rw [abs_of_nonneg hx0]
        linarith [abs_nonneg B]
      · rw [abs_of_nonpos hx0]
        linarith [neg_le_abs B]
    calc ‖g x‖ ^ 2 * (ρ x)⁻¹ ≤ ‖g x‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hρinv (sq_nonneg _)
      _ = |x| ^ (2 * k) * Real.exp (-x) := by rw [mul_one, hgx_norm]
      _ ≤ (((2 * k).factorial : ℝ) * (2 : ℝ) ^ (2 * k) * Real.exp (|x| / 2)) * Real.exp (-x) := by
          gcongr
      _ = ((2 * k).factorial : ℝ) * (2 : ℝ) ^ (2 * k) * (Real.exp (|x| / 2) * Real.exp (-x)) := by ring
      _ ≤ ((2 * k).factorial : ℝ) * (2 : ℝ) ^ (2 * k) * (Real.exp |B| * Real.exp (-(1 / 2 : ℝ) * x)) := by
          gcongr
      _ = K * Real.exp (-(1 / 2 : ℝ) * x) := by dsimp [K]; ring

/-- Lift a `MemLp` profile to `CompactIntervalSobolev volume id (-α) α s`. -/
def toDirichletStrip (α s : ℝ) (U : ℝ → ℂ)
    (hU : MemLp U 2 (intervalSobolevMeasure volume id (-α) α s false)) :
    CompactIntervalSobolev volume id (-α) α s :=
  hU.toLp U

/-- Riesz duality isomorphism identifying `StrongDual ℂ (CompactIntervalSobolev volume id (-α) α s)`
with the dual-weighted Sobolev strip space. -/
def stripDualEquiv (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    StrongDual ℂ (CompactIntervalSobolev volume id (-α) α s) ≃ₗᵢ[ℂ]
      CompactIntervalSobolev volume id (-α) α s true :=
  (scalarIntervalSobolev_dual (-α) α s (neg_le_self hα) hs).exists.choose

private theorem stripDualEquiv_spec (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (Λ : StrongDual ℂ (CompactIntervalSobolev volume id (-α) α s))
    (f : CompactIntervalSobolev volume id (-α) α s) :
    Integrable (fun x ↦ f x * stripDualEquiv α s hα hs Λ x) volume ∧
      Λ f = ∫ x, f x * stripDualEquiv α s hα hs Λ x :=
  (scalarIntervalSobolev_dual (-α) α s (neg_le_self hα) hs).exists.choose_spec Λ f

/-- Unnormalized cutoff Mellin-jet functional on `CompactIntervalSobolev volume id (-α) α s`
supported on `[B, ∞)` of derivative order `k` at ordinate `t : ℝ`. -/
def halfLineMellinJet (α s B : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (k : ℕ) (t : ℝ) :
    StrongDual ℂ (CompactIntervalSobolev volume id (-α) α s) :=
  (stripDualEquiv α s hα hs).symm
    ((halfLineMellinJet_memLp α s B hα hs k t).toLp _)

private theorem halfLineMellinJet_norm_eq (α s B : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (k : ℕ) (t : ℝ) :
    ‖halfLineMellinJet α s B hα hs k t‖ = ‖halfLineMellinJet α s B hα hs k 0‖ := by
  let μ' := intervalSobolevMeasure volume id (-α) α s true
  let g := fun (τ : ℝ) (x : ℝ) ↦ Set.indicator (Set.Ici B) (fun x : ℝ ↦
    (x : ℂ) ^ k * Complex.exp (((τ : ℂ) * Complex.I - 1 / 2 : ℂ) * (x : ℂ))) x
  have hnorm (τ : ℝ) : ‖halfLineMellinJet α s B hα hs k τ‖ =
      ‖(halfLineMellinJet_memLp α s B hα hs k τ).toLp (g τ)‖ := by
    change ‖(stripDualEquiv α s hα hs).symm ((halfLineMellinJet_memLp α s B hα hs k τ).toLp (g τ))‖ = _
    with_reducible_and_instances
      exact (stripDualEquiv α s hα hs).symm.norm_map _
  rw [hnorm t, hnorm 0]
  have hmeas_g (τ : ℝ) : AEStronglyMeasurable (g τ) μ' :=
    (halfLineMellinJet_memLp α s B hα hs k τ).aestronglyMeasurable
  have he_norm (τ : ℝ) : eLpNorm (g τ) 2 μ' = eLpNorm (g 0) 2 μ' := by
    refine eLpNorm_congr_norm_ae (hmeas_g τ) (hmeas_g 0) (Filter.Eventually.of_forall fun x ↦ ?_)
    by_cases hx : B ≤ x
    · simp only [g, Set.indicator_of_mem (Set.mem_Ici.mpr hx), norm_mul]
      congr 1
      rw [Complex.norm_exp, Complex.norm_exp]
      simp [Complex.mul_re]
    · simp only [g, Set.indicator_of_notMem (Set.mem_Ici.not.mpr hx)]
  have h1 : ‖(halfLineMellinJet_memLp α s B hα hs k t).toLp (g t)‖ = (eLpNorm (g t) 2 μ').toReal := by
    rw [Lp.norm_toLp (g t) (halfLineMellinJet_memLp α s B hα hs k t)]
  have h2 : ‖(halfLineMellinJet_memLp α s B hα hs k 0).toLp (g 0)‖ = (eLpNorm (g 0) 2 μ').toReal := by
    rw [Lp.norm_toLp (g 0) (halfLineMellinJet_memLp α s B hα hs k 0)]
  rw [h1, h2, he_norm t]

/-- Pairing `halfLineMellinJet` with a function `U` vanishing on `(-∞, B)` yields the exact
`k`-th derivative of its half-twisted Mellin transform at `i t`. -/
theorem halfLineMellinJet_apply (α s B : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (k : ℕ) (t : ℝ)
    {U : ℝ → ℂ} (hsupp : ∀ x < B, U x = 0)
    (hU : MemLp U 2 (intervalSobolevMeasure volume id (-α) α s false)) :
    halfLineMellinJet α s B hα hs k t (toDirichletStrip α s U hU) =
      ∫ x : ℝ, (x : ℂ) ^ k * U x * Complex.exp (((t : ℂ) * Complex.I - 1 / 2 : ℂ) * (x : ℂ)) := by
  let e := stripDualEquiv α s hα hs
  have hspec := (stripDualEquiv_spec α s hα hs (halfLineMellinJet α s B hα hs k t)
    (toDirichletStrip α s U hU)).2
  rw [hspec]
  have heq_rhs : e (halfLineMellinJet α s B hα hs k t) =
      (halfLineMellinJet_memLp α s B hα hs k t).toLp _ :=
    e.apply_symm_apply ((halfLineMellinJet_memLp α s B hα hs k t).toLp _)
  rw [heq_rhs]
  have hρc := stripDensity_continuous (-α) α s
  have hρp := stripDensity_pos (-α) α s
  have hU_ae : (toDirichletStrip α s U hU : ℝ → ℂ) =ᵐ[volume] U := by
    have hcoe := hU.coeFn_toLp
    dsimp only [intervalSobolevMeasure] at hcoe
    simp only [Bool.false_eq_true, ↓reduceIte] at hcoe
    have hae := (ae_withDensity_iff hρc.measurable.ennreal_ofReal).mp hcoe
    filter_upwards [hae] with x hx
    exact hx (ENNReal.ofReal_pos.mpr (hρp x)).ne'
  have hg_ae : ((halfLineMellinJet_memLp α s B hα hs k t).toLp _ : ℝ → ℂ) =ᵐ[volume]
      Set.indicator (Set.Ici B) (fun x : ℝ ↦
        (x : ℂ) ^ k * Complex.exp (((t : ℂ) * Complex.I - 1 / 2 : ℂ) * (x : ℂ))) := by
    have hcoe := (halfLineMellinJet_memLp α s B hα hs k t).coeFn_toLp
    dsimp only [intervalSobolevMeasure] at hcoe
    simp only [↓reduceIte] at hcoe
    have hae := (ae_withDensity_iff hρc.measurable.inv.ennreal_ofReal).mp hcoe
    filter_upwards [hae] with x hx
    exact hx (ENNReal.ofReal_pos.mpr (inv_pos.mpr (hρp x))).ne'
  refine integral_congr_ae ?_
  filter_upwards [hU_ae, hg_ae] with x hxU hxg
  rw [hxU, hxg]
  by_cases hxB : B ≤ x
  · rw [Set.indicator_of_mem hxB]
    ring
  · rw [hsupp x (lt_of_not_ge hxB), zero_mul, mul_zero, zero_mul]

/-- Explicit Euler/Gauss-sum/L-function normalizing scalar for the `j`-th prime-lattice
evaluation functional at prime `p` and stage `T`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
def dirichletRowScalar {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : Finset ℕ) (p : ℕ) (j : ℤ) : ℂ :=
  let t : ℝ := dirichletPrimeFreq χ p j
  if t = 0 then
    iteratedDeriv (dirichletStageZeroOrder χ T) (dirichletStageMultiplier χ T) 0 *
      (2 * gaussSum χ ZMod.stdAddChar * DirichletCharacter.LFunction χ⁻¹ 1)
  else
    dirichletStageMultiplier χ T ((t : ℂ) * Complex.I) *
      (2 * gaussSum χ ZMod.stdAddChar * (N : ℂ) ^ (-(t : ℂ) * Complex.I) *
        DirichletCharacter.LFunction χ⁻¹ (1 - (t : ℂ) * Complex.I))

private theorem dirichletRowScalar_ne_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T) (j : ℤ) :
    dirichletRowScalar χ T p j ≠ 0 := by
  have hχinv_ne : χ⁻¹ ≠ 1 := (dirichlet_inv_isPrimitive_ne_one hχ hN).2
  have hgauss_ne : gaussSum χ ZMod.stdAddChar ≠ 0 := by
    intro h0
    have hnorm := DirichletCharacter.norm_gaussSum_stdAddChar hχ
    rw [h0, norm_zero] at hnorm
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
    linarith [Real.sqrt_pos.mpr hNpos]
  let t : ℝ := dirichletPrimeFreq χ p j
  change (if t = 0 then
      iteratedDeriv (dirichletStageZeroOrder χ T) (dirichletStageMultiplier χ T) 0 *
        (2 * gaussSum χ ZMod.stdAddChar * DirichletCharacter.LFunction χ⁻¹ 1)
    else
      dirichletStageMultiplier χ T ((t : ℂ) * Complex.I) *
        (2 * gaussSum χ ZMod.stdAddChar * (N : ℂ) ^ (-(t : ℂ) * Complex.I) *
          DirichletCharacter.LFunction χ⁻¹ (1 - (t : ℂ) * Complex.I))) ≠ 0
  by_cases ht0 : t = 0
  · simp only [ht0, ↓reduceIte]
    have hT1 : ∀ q ∈ T, 1 < q := fun q hq ↦ (hT q hq).1.one_lt
    have hB0 : iteratedDeriv (dirichletStageZeroOrder χ T) (dirichletStageMultiplier χ T) 0 ≠ 0 :=
      (dirichletStageMultiplier_iteratedDeriv_zero χ T hT1).2.2
    have hL1 : DirichletCharacter.LFunction χ⁻¹ 1 ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχinv_ne) (by simp)
    exact mul_ne_zero hB0 (mul_ne_zero (mul_ne_zero two_ne_zero hgauss_ne) hL1)
  · simp only [ht0, ↓reduceIte]
    obtain ⟨_, _, _, hbd⟩ := dirichletStageMultiplier_inv_poly_bound χ T hT hp hpN hpT
    have hBT := (hbd j ht0).1
    have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have hNpow : (N : ℂ) ^ (-(t : ℂ) * Complex.I) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hNne)
    have hL : DirichletCharacter.LFunction χ⁻¹ (1 - (t : ℂ) * Complex.I) ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχinv_ne)
        (by simp [Complex.sub_re, Complex.mul_re])
    exact mul_ne_zero hBT (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hgauss_ne) hNpow) hL)

/-- Normalized row functional extracting the `j`-th logarithmic Fourier moment `logFourierProfile f₀ (i t_j)`
from any depleted profile `toDirichletStrip (U_χ (dirichletTestDeplete χ T f₀))` inside the fixed outer
box `[-X, X]`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
def dirichletNormalizedRow {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : Finset ℕ) (p : ℕ)
    (X α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (j : ℤ) :
    StrongDual ℂ (CompactIntervalSobolev volume id (-α) α s) :=
  let t : ℝ := dirichletPrimeFreq χ p j
  let k : ℕ := if t = 0 then dirichletStageZeroOrder χ T else 0
  (dirichletRowScalar χ T p j)⁻¹ •
    halfLineMellinJet α s (-Real.log ((N : ℝ) * X)) hα hs k t

private theorem contDiff_halfTwistMellin_of_rapid {U : ℝ → ℂ} (hU : IsHalfLineRapid U) :
    ContDiff ℂ ∞ (halfTwistMellin U) := by
  have heq : (fun z : ℂ ↦ ∫ x : ℝ, (x : ℂ) ^ 0 * U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))) =
      halfTwistMellin U := by
    ext z
    simp [halfTwistMellin]
  rw [← heq]
  exact (differentiable_halfLineMoment hU 0).contDiff

/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
Evaluating `dirichletNormalizedRow χ T p X α s hα hs j` on the `T`-depleted image of any test
`f₀` in the shrunk box `X / ∏_{q ∈ T} q` recovers the exact Fourier-Mellin coordinate
`logFourierProfile f₀ (i t_j)`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem dirichletNormalizedRow_apply_depleted {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {f₀ : 𝓢(ℝ, ℂ)} (hf₀ : IsDirichletFixedBoxTest χ (X / ∏ q ∈ T, (q : ℝ)) f₀)
    (j : ℤ) :
    let hTpos : ∀ q ∈ T, 0 < q := fun q hq ↦ (hT q hq).1.pos
    let hmem : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) 2
        (intervalSobolevMeasure volume id (-α) α s false) :=
      dirichletDeplete_memLp hχ hN T hTpos
        (div_pos hX (Finset.prod_pos fun q hq ↦ by exact_mod_cast (hT q hq).1.pos)) hα hs hf₀
    dirichletNormalizedRow χ T p X α s hα hs j
        (toDirichletStrip α s _ hmem) =
      logFourierProfile f₀ ((dirichletPrimeFreq χ p j : ℂ) * Complex.I) := by
  intro hTpos hmem
  have hprod_pos : 0 < ∏ q ∈ T, (q : ℝ) := Finset.prod_pos fun q hq ↦ by exact_mod_cast (hT q hq).1.pos
  have hX' : 0 < X / ∏ q ∈ T, (q : ℝ) := div_pos hX hprod_pos
  have hfT : IsDirichletFixedBoxTest χ X (dirichletTestDeplete χ T f₀) :=
    isDirichletFixedBoxTest_dirichletTestDeplete T hTpos hX.le hf₀
  have hU_eq : dirichletDeplete χ T (twistedHalfLogProfile χ f₀) =
      twistedHalfLogProfile χ (dirichletTestDeplete χ T f₀) :=
    (twistedHalfLogProfile_dirichletTestDeplete χ T hTpos f₀).symm
  have hsupp : ∀ x < -Real.log ((N : ℝ) * X),
      dirichletDeplete χ T (twistedHalfLogProfile χ f₀) x = 0 := by
    intro x hx
    rw [hU_eq]
    exact dirichletFixedBox_support_lower_bound hχ hN hX hfT hx
  let t : ℝ := dirichletPrimeFreq χ p j
  let k : ℕ := if t = 0 then dirichletStageZeroOrder χ T else 0
  have hrow_ne : dirichletRowScalar χ T p j ≠ 0 :=
    dirichletRowScalar_ne_zero hχ hN T hT hp hpN hpT j
  have hpair := halfLineMellinJet_apply α s (-Real.log ((N : ℝ) * X)) hα hs k t hsupp hmem
  have hmellin : ∫ x : ℝ, (x : ℂ) ^ k * dirichletDeplete χ T (twistedHalfLogProfile χ f₀) x *
        Complex.exp (((t : ℂ) * Complex.I - 1 / 2 : ℂ) * (x : ℂ)) =
      dirichletRowScalar χ T p j * logFourierProfile f₀ ((t : ℂ) * Complex.I) := by
    have hU₀ := isHalfLineRapid_twistedHalfLogProfile hχ hN hX' hf₀
    have hderiv_id := iteratedDeriv_halfTwistMellin_depleted hχ hN T hTpos hX' hf₀ k ((t : ℂ) * Complex.I)
    rw [← hderiv_id]
    have hfun_mellin : halfTwistMellin (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) =
        dirichletStageMultiplier χ T * halfTwistMellin (twistedHalfLogProfile χ f₀) :=
      funext (halfTwistMellin_dirichletDeplete χ hN T hTpos hX' hf₀ hχ)
    rw [hfun_mellin]
    by_cases ht0 : t = 0
    · have hk : k = dirichletStageZeroOrder χ T := ite_eq_left_of_eq_true _ _ (eq_true ht0)
      have hsc : dirichletRowScalar χ T p j =
          iteratedDeriv (dirichletStageZeroOrder χ T) (dirichletStageMultiplier χ T) 0 *
            (2 * gaussSum χ ZMod.stdAddChar * DirichletCharacter.LFunction χ⁻¹ 1) := by
        simp [dirichletRowScalar, t, ht0]
      rw [hk, ht0, hsc, Complex.ofReal_zero, zero_mul]
      have hB_sm : ContDiffAt ℂ (dirichletStageZeroOrder χ T) (dirichletStageMultiplier χ T) 0 :=
        ((smooth_stageMultiplier χ T hTpos).contDiffAt).of_le (by simp)
      have hM_sm : ContDiffAt ℂ (dirichletStageZeroOrder χ T) (halfTwistMellin (twistedHalfLogProfile χ f₀)) 0 :=
        ((contDiff_halfTwistMellin_of_rapid hU₀).contDiffAt).of_le (by simp)
      rw [iteratedDeriv_mul hB_sm hM_sm, Finset.sum_eq_single (dirichletStageZeroOrder χ T)]
      · simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, iteratedDeriv_zero]
        rw [dirichletFixedBox_mellin_eq_zero hχ hN hX' hf₀]
        ring
      · intro i hi hik
        have hik' : i < dirichletStageZeroOrder χ T := lt_of_le_of_ne (Finset.mem_range_succ_iff.mp hi) hik
        have hvan := (dirichletStageMultiplier_iteratedDeriv_zero χ T (fun q hq ↦ (hT q hq).1.one_lt)).1
        simp [hvan i hik']
      · intro hk_not
        exfalso
        exact hk_not (Finset.mem_range_succ_iff.mpr le_rfl)
    · have hk : k = 0 := ite_eq_right_of_eq_false _ _ (eq_false ht0)
      have hsc : dirichletRowScalar χ T p j =
          dirichletStageMultiplier χ T ((t : ℂ) * Complex.I) *
            (2 * gaussSum χ ZMod.stdAddChar * (N : ℂ) ^ (-(t : ℂ) * Complex.I) *
              DirichletCharacter.LFunction χ⁻¹ (1 - (t : ℂ) * Complex.I)) := by
        simp [dirichletRowScalar, t, ht0]
      rw [hk, hsc, iteratedDeriv_zero]
      change dirichletStageMultiplier χ T ((t : ℂ) * Complex.I) *
          halfTwistMellin (twistedHalfLogProfile χ f₀) ((t : ℂ) * Complex.I) = _
      rw [dirichletFixedBox_mellin_eq_imagAxis hχ hN hX' hf₀ t]
      ring
  dsimp only [dirichletNormalizedRow]
  change (dirichletRowScalar χ T p j)⁻¹ *
      halfLineMellinJet α s (-Real.log ((N : ℝ) * X)) hα hs k t (toDirichletStrip α s _ hmem) = _
  rw [hpair, hmellin, inv_mul_cancel_left₀ hrow_ne]

/-- Evaluating `dirichletNormalizedRow χ T p` on the next stage `insert p T` vanishes identically. -/
theorem dirichletNormalizedRow_apply_next_stage_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {g₀ : 𝓢(ℝ, ℂ)} (hg₀ : IsDirichletFixedBoxTest χ (X / ((p : ℝ) * ∏ q ∈ T, (q : ℝ))) g₀)
    (j : ℤ) :
    let hTpos' : ∀ q ∈ insert p T, 0 < q := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hqT
      · exact hp.pos
      · exact (hT q hqT).1.pos
    let hg₀' : IsDirichletFixedBoxTest χ (X / ∏ q ∈ insert p T, (q : ℝ)) g₀ := by
      rwa [Finset.prod_insert hpT]
    let hmem : MemLp (dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀)) 2
        (intervalSobolevMeasure volume id (-α) α s false) :=
      dirichletDeplete_memLp hχ hN (insert p T) hTpos'
        (div_pos hX (Finset.prod_pos fun q hq ↦ by exact_mod_cast hTpos' q hq)) hα hs hg₀'
    dirichletNormalizedRow χ T p X α s hα hs j
        (toDirichletStrip α s _ hmem) = 0 := by
  intro hTpos' hg₀' hmem
  have hprod_pos : 0 < ∏ q ∈ insert p T, (q : ℝ) :=
    Finset.prod_pos fun q hq ↦ by exact_mod_cast hTpos' q hq
  have hX' : 0 < X / ∏ q ∈ insert p T, (q : ℝ) := div_pos hX hprod_pos
  have hfT : IsDirichletFixedBoxTest χ X (dirichletTestDeplete χ (insert p T) g₀) :=
    isDirichletFixedBoxTest_dirichletTestDeplete (insert p T) hTpos' hX.le hg₀'
  have hU_eq : dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀) =
      twistedHalfLogProfile χ (dirichletTestDeplete χ (insert p T) g₀) :=
    (twistedHalfLogProfile_dirichletTestDeplete χ (insert p T) hTpos' g₀).symm
  have hsupp : ∀ x < -Real.log ((N : ℝ) * X),
      dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀) x = 0 := by
    intro x hx
    rw [hU_eq]
    exact dirichletFixedBox_support_lower_bound hχ hN hX hfT hx
  let t : ℝ := dirichletPrimeFreq χ p j
  let k : ℕ := if t = 0 then dirichletStageZeroOrder χ T else 0
  have hpair := halfLineMellinJet_apply α s (-Real.log ((N : ℝ) * X)) hα hs k t hsupp hmem
  have hzero : ∫ x : ℝ, (x : ℂ) ^ k * dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀) x *
      Complex.exp (((t : ℂ) * Complex.I - 1 / 2 : ℂ) * (x : ℂ)) = 0 := by
    have hU₀ := isHalfLineRapid_twistedHalfLogProfile hχ hN hX' hg₀'
    have hderiv_id := iteratedDeriv_halfTwistMellin_depleted hχ hN (insert p T) hTpos' hX' hg₀' k ((t : ℂ) * Complex.I)
    rw [← hderiv_id]
    have hfun_mellin : halfTwistMellin (dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀)) =
        dirichletStageMultiplier χ (insert p T) *
          halfTwistMellin (twistedHalfLogProfile χ g₀) :=
      funext (halfTwistMellin_dirichletDeplete χ hN (insert p T) hTpos' hX' hg₀' hχ)
    rw [hfun_mellin]
    by_cases ht0 : t = 0
    · have hk : k = dirichletStageZeroOrder χ T := ite_eq_left_of_eq_true _ _ (eq_true ht0)
      have hχp1 : χ p = 1 := by
        have h := dirichlet_mul_cpow_primeFreq_eq_one χ hp hpN j
        change χ p * (p : ℂ) ^ (-(t : ℂ) * Complex.I) = 1 at h
        rw [ht0, Complex.ofReal_zero, neg_zero, zero_mul, Complex.cpow_zero, mul_one] at h
        exact h
      have hord_succ : dirichletStageZeroOrder χ (insert p T) = dirichletStageZeroOrder χ T + 1 := by
        unfold dirichletStageZeroOrder
        simp only [Finset.filter_insert, hχp1, ↓reduceIte]
        rw [Finset.card_insert_of_notMem (by simp [hpT])]
      have hT1' : ∀ q ∈ insert p T, 1 < q := by
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hqT
        · exact hp.one_lt
        · exact (hT q hqT).1.one_lt
      have hvan := (dirichletStageMultiplier_iteratedDeriv_zero χ (insert p T) hT1').1
      have hB_sm : ContDiffAt ℂ k (dirichletStageMultiplier χ (insert p T)) 0 :=
        ((smooth_stageMultiplier χ (insert p T) hTpos').contDiffAt).of_le (by simp)
      have hM_sm : ContDiffAt ℂ k (halfTwistMellin (twistedHalfLogProfile χ g₀)) 0 :=
        ((contDiff_halfTwistMellin_of_rapid hU₀).contDiffAt).of_le (by simp)
      rw [ht0, Complex.ofReal_zero, zero_mul, iteratedDeriv_mul hB_sm hM_sm]
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      have hik : i < dirichletStageZeroOrder χ (insert p T) := by
        have : i ≤ k := Finset.mem_range_succ_iff.mp hi
        omega
      simp [hvan i hik]
    · have hk : k = 0 := ite_eq_right_of_eq_false _ _ (eq_false ht0)
      rw [hk, iteratedDeriv_zero]
      change dirichletStageMultiplier χ (insert p T) ((t : ℂ) * Complex.I) *
          halfTwistMellin (twistedHalfLogProfile χ g₀) ((t : ℂ) * Complex.I) = 0
      rw [dirichletStageMultiplier, Finset.prod_insert hpT]
      have hfac0 : 1 - χ p * (p : ℂ) ^ (-((t : ℂ) * Complex.I)) = 0 := by
        have h := dirichlet_mul_cpow_primeFreq_eq_one χ hp hpN j
        rw [sub_eq_zero]
        simpa [t, neg_mul] using h.symm
      simp [hfac0]
  dsimp only [dirichletNormalizedRow]
  change (dirichletRowScalar χ T p j)⁻¹ *
      halfLineMellinJet α s (-Real.log ((N : ℝ) * X)) hα hs k t (toDirichletStrip α s _ hmem) = 0
  rw [hpair, hzero, mul_zero]

/-- Normalized row functionals have at most polynomial operator-norm growth in `|j|`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem dirichletNormalizedRow_norm_poly_bound {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (_hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    ∃ K : ℕ, ∃ C > (0 : ℝ), ∀ j : ℤ,
      ‖dirichletNormalizedRow χ T p X α s hα hs j‖ ≤ C * (1 + |(j : ℝ)|) ^ K := by
  obtain ⟨CL, hCL, AL, hLbd⟩ := dirichletLFunction_inv_poly_bound_oneLine hχ hN
  obtain ⟨DB, CB, hCB, hBbd⟩ := dirichletStageMultiplier_inv_poly_bound χ T hT hp hpN hpT
  have hgauss_ne : gaussSum χ ZMod.stdAddChar ≠ 0 := by
    intro h0
    have hnorm := DirichletCharacter.norm_gaussSum_stdAddChar hχ
    rw [h0, norm_zero] at hnorm
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
    linarith [Real.sqrt_pos.mpr hNpos]
  let b : ℕ := dirichletStageZeroOrder χ T
  let M_b : ℝ := ‖halfLineMellinJet α s (-Real.log ((N : ℝ) * X)) hα hs b 0‖
  let M_0 : ℝ := ‖halfLineMellinJet α s (-Real.log ((N : ℝ) * X)) hα hs 0 0‖
  let Czero : ℝ :=
    ‖(iteratedDeriv b (dirichletStageMultiplier χ T) 0 *
      (2 * gaussSum χ ZMod.stdAddChar * DirichletCharacter.LFunction χ⁻¹ 1))⁻¹‖ * M_b
  let logp : ℝ := Real.log p
  have hlogp_pos : 0 < logp := Real.log_pos (by exact_mod_cast hp.one_lt)
  let t0 : ℝ := Complex.arg (χ p) / logp
  let S : ℝ := max 1 (1 + |t0| + 2 * Real.pi / logp)
  let K : ℕ := AL + DB
  let C_nz : ℝ := CB * CL * (2 * ‖gaussSum χ ZMod.stdAddChar‖)⁻¹ * M_0 * S ^ K
  let C : ℝ := max Czero C_nz + 1
  refine ⟨K, C, by positivity, fun j ↦ ?_⟩
  let t : ℝ := dirichletPrimeFreq χ p j
  change ‖(dirichletRowScalar χ T p j)⁻¹ •
      halfLineMellinJet α s (-Real.log ((N : ℝ) * X)) hα hs
        (if t = 0 then dirichletStageZeroOrder χ T else 0) t‖ ≤ C * (1 + |(j : ℝ)|) ^ K
  rw [norm_smul]
  by_cases ht0 : t = 0
  · simp only [ht0, ↓reduceIte]
    have hsc : dirichletRowScalar χ T p j =
        iteratedDeriv b (dirichletStageMultiplier χ T) 0 *
          (2 * gaussSum χ ZMod.stdAddChar * DirichletCharacter.LFunction χ⁻¹ 1) := by
      simp [dirichletRowScalar, t, ht0, b]
    change ‖(dirichletRowScalar χ T p j)⁻¹‖ *
        ‖halfLineMellinJet α s (-Real.log ((N : ℝ) * X)) hα hs (dirichletStageZeroOrder χ T) 0‖ ≤
      C * (1 + |(j : ℝ)|) ^ K
    rw [hsc]
    have hle1 : ‖(iteratedDeriv b (dirichletStageMultiplier χ T) 0 *
          (2 * gaussSum χ ZMod.stdAddChar * DirichletCharacter.LFunction χ⁻¹ 1))⁻¹‖ * M_b ≤ C :=
      le_trans (le_max_left Czero C_nz) (by linarith)
    change ‖(iteratedDeriv b (dirichletStageMultiplier χ T) 0 *
          (2 * gaussSum χ ZMod.stdAddChar * DirichletCharacter.LFunction χ⁻¹ 1))⁻¹‖ * M_b ≤
        C * (1 + |(j : ℝ)|) ^ K
    refine hle1.trans ?_
    have hpow : 1 ≤ (1 + |(j : ℝ)|) ^ K := one_le_pow₀ (by linarith [abs_nonneg (j : ℝ)])
    exact le_mul_of_one_le_right (by positivity) hpow
  · simp only [ht0, ↓reduceIte]
    have hsc : dirichletRowScalar χ T p j =
        dirichletStageMultiplier χ T ((t : ℂ) * Complex.I) *
          (2 * gaussSum χ ZMod.stdAddChar * (N : ℂ) ^ (-(t : ℂ) * Complex.I) *
            DirichletCharacter.LFunction χ⁻¹ (1 - (t : ℂ) * Complex.I)) := by
      simp [dirichletRowScalar, t, ht0]
    rw [hsc]
    have hjet : ‖halfLineMellinJet α s (-Real.log ((N : ℝ) * X)) hα hs 0 t‖ = M_0 :=
      halfLineMellinJet_norm_eq α s (-Real.log ((N : ℝ) * X)) hα hs 0 t
    rw [hjet]
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
    have hNpow_norm : ‖(N : ℂ) ^ (-(t : ℂ) * Complex.I)‖ = 1 := by
      rw [← Complex.ofReal_natCast N, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
      simp [Real.rpow_zero]
    have hsc_inv : ‖(dirichletStageMultiplier χ T ((t : ℂ) * Complex.I) *
          (2 * gaussSum χ ZMod.stdAddChar * (N : ℂ) ^ (-(t : ℂ) * Complex.I) *
            DirichletCharacter.LFunction χ⁻¹ (1 - (t : ℂ) * Complex.I)))⁻¹‖ =
        ‖(dirichletStageMultiplier χ T ((t : ℂ) * Complex.I))⁻¹‖ *
          (2 * ‖gaussSum χ ZMod.stdAddChar‖)⁻¹ *
          ‖(DirichletCharacter.LFunction χ⁻¹ (1 - (t : ℂ) * Complex.I))⁻¹‖ := by
      simp only [norm_inv, norm_mul, Complex.norm_ofNat, hNpow_norm, mul_inv]
      ring
    rw [hsc_inv]
    have hB := (hBbd j ht0).2
    have hL := hLbd t
    have ht_lin : 1 + |t| ≤ S * (1 + |(j : ℝ)|) := by
      have ht_def : t = t0 + (2 * Real.pi / logp) * j := by
        dsimp [t, dirichletPrimeFreq, t0, logp]
        ring
      have hab : |t| ≤ |t0| + (2 * Real.pi / logp) * |(j : ℝ)| := by
        rw [ht_def]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos (div_pos (mul_pos two_pos Real.pi_pos) hlogp_pos)]
      have h1S : 1 + |t| ≤ (1 + |t0|) + (2 * Real.pi / logp) * |(j : ℝ)| := by linarith
      have hS1 : 1 + |t0| ≤ S := le_trans (by linarith [div_pos (mul_pos two_pos Real.pi_pos) hlogp_pos])
        (le_max_right _ _)
      have hS2 : 2 * Real.pi / logp ≤ S := le_trans (by linarith [abs_nonneg t0]) (le_max_right _ _)
      nlinarith [abs_nonneg (j : ℝ)]
    have hpow_le : (1 + |t|) ^ K ≤ S ^ K * (1 + |(j : ℝ)|) ^ K := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) ht_lin K
    have hpow_split : (1 + |t|) ^ DB * (1 + |t|) ^ AL = (1 + |t|) ^ K := by
      dsimp [K]
      rw [← pow_add, add_comm DB AL]
    calc ‖(dirichletStageMultiplier χ T ((t : ℂ) * Complex.I))⁻¹‖ *
            (2 * ‖gaussSum χ ZMod.stdAddChar‖)⁻¹ *
            ‖(DirichletCharacter.LFunction χ⁻¹ (1 - (t : ℂ) * Complex.I))⁻¹‖ * M_0
        ≤ (CB * (1 + |t|) ^ DB) * (2 * ‖gaussSum χ ZMod.stdAddChar‖)⁻¹ *
            (CL * (1 + |t|) ^ AL) * M_0 := by
          gcongr
      _ = CB * CL * (2 * ‖gaussSum χ ZMod.stdAddChar‖)⁻¹ * M_0 * ((1 + |t|) ^ DB * (1 + |t|) ^ AL) := by
          ring
      _ = CB * CL * (2 * ‖gaussSum χ ZMod.stdAddChar‖)⁻¹ * M_0 * (1 + |t|) ^ K := by
          rw [hpow_split]
      _ ≤ CB * CL * (2 * ‖gaussSum χ ZMod.stdAddChar‖)⁻¹ * M_0 * (S ^ K * (1 + |(j : ℝ)|) ^ K) := by
          gcongr
      _ = C_nz * (1 + |(j : ℝ)|) ^ K := by dsimp [C_nz]; ring
      _ ≤ C * (1 + |(j : ℝ)|) ^ K := by
          gcongr
          exact le_trans (le_max_right Czero C_nz) (by linarith)

end MellinAndStripRows

end RiemannMasullo.Isolated
