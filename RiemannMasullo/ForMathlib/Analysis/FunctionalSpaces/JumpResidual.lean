module

public import RiemannMasullo.ForMathlib.Analysis.FunctionalSpaces.JumpMultiplier
public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! # Spacing-independent bounds for cardinal residual energies

The exact product cancellation and an exponential envelope bound the residual energy
using only the second jump moment and a locally weighted Lipschitz constant. The final
theorem derives the multiplier test's admissibility from bounded Lipschitz regularity.
-/

@[expose] public noncomputable section
open MeasureTheory Real
namespace RiemannMasullo

private theorem integral_exp_abs_quarter (z : ℝ) :
    (∫ x : ℝ, Real.exp (-|x - z| / 4)) = 8 := by
  rw [integral_sub_right_eq_self (fun x : ℝ ↦ Real.exp (-|x| / 4)) z]
  have he (x : ℝ) : Real.exp (-|x| / 4) = Real.exp ((-1 / 4 : ℝ) * |x|) := by congr 1; ring
  simp_rw [he]
  rw [integral_comp_abs (f := fun x : ℝ ↦ Real.exp ((-1 / 4 : ℝ) * x)), integral_exp_mul_Ioi (by norm_num : (-1 / 4 : ℝ) < 0) 0]
  norm_num

private theorem integrable_exp_abs_quarter (z : ℝ) :
    Integrable (fun x : ℝ ↦ Real.exp (-|x - z| / 4)) := by
  have hi := (integrable_exp_neg_mul_abs (c := 1 / 4) (by norm_num)).comp_sub_right z
  apply hi.congr
  exact .of_forall fun x ↦ by dsimp; congr 1; ring

private theorem residual_integrand_le {h : ℝ → ℝ} {b : ℝ → ℂ} {C A z : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hpos : ∀ x, 0 ≤ h x)
    (hh : ∀ x, h x ≤ C * Real.exp (-|x - z| / 2))
    (hb : ∀ x y, ‖b x - b y‖ ≤ A * |x - y| *
      Real.exp ((|x - z| + |y - z|) / 8)) (x y : ℝ) :
    h x * h y * ‖b x - b y‖ ^ 2 ≤
      C ^ 2 * A ^ 2 * (x - y) ^ 2 * Real.exp (-|y - z| / 4) := by
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hb x y)
  have hm := mul_le_mul (mul_le_mul (hh x) (hh y) (hpos y) (by positivity)) hsq
    (sq_nonneg _) (by positivity)
  have he : (C * Real.exp (-|x - z| / 2)) * (C * Real.exp (-|y - z| / 2)) *
      (A * |x - y| * Real.exp ((|x - z| + |y - z|) / 8)) ^ 2 =
      C ^ 2 * A ^ 2 * (x - y) ^ 2 *
        Real.exp (-(|x - z| + |y - z|) / 4) := by
    rw [mul_pow, mul_pow, sq_abs, ← Real.exp_nat_mul]
    have hex : Real.exp (-|x - z| / 2) * Real.exp (-|y - z| / 2) *
        Real.exp (2 * ((|x - z| + |y - z|) / 8)) =
          Real.exp (-(|x - z| + |y - z|) / 4) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = C ^ 2 * A ^ 2 * (x - y) ^ 2 *
          (Real.exp (-|x - z| / 2) * Real.exp (-|y - z| / 2) *
            Real.exp (2 * ((|x - z| + |y - z|) / 8))) := by push_cast; ring
      _ = _ := by rw [hex]
  rw [he] at hm
  refine hm.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
  linarith [abs_nonneg (x - z)]


/-- Exponential control of the interpolant turns a locally weighted Lipschitz estimate
for the multiplier into a bound depending only on the second jump moment. -/
theorem nonlocal_residual_integrable_and_le (κ : Measure ℝ) [SFinite κ]
    {h : ℝ → ℝ} {b : ℝ → ℂ} {C A z : ℝ} (hm : Measurable h) (bm : Measurable b)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hpos : ∀ x, 0 ≤ h x)
    (hh : ∀ x, h x ≤ C * Real.exp (-|x - z| / 2))
    (hb : ∀ x y, ‖b x - b y‖ ≤ A * |x - y| *
      Real.exp ((|x - z| + |y - z|) / 8))
    (hκ : Integrable (fun r : ℝ ↦ r ^ 2) κ) :
    Integrable (fun p : ℝ × ℝ ↦ h p.1 * h p.2 * ‖b p.1 - b p.2‖ ^ 2)
      (realJumpPairMeasure κ) ∧
    (∫ p : ℝ × ℝ, h p.1 * h p.2 * ‖b p.1 - b p.2‖ ^ 2 ∂realJumpPairMeasure κ) ≤
      8 * C ^ 2 * A ^ 2 * ∫ r : ℝ, r ^ 2 ∂κ := by
  let H (p : ℝ × ℝ) := h (p.2 + p.1) * h p.2 * ‖b (p.2 + p.1) - b p.2‖ ^ 2
  let B (p : ℝ × ℝ) := (C ^ 2 * A ^ 2) * (p.1 ^ 2 * Real.exp (-|p.2 - z| / 4))
  have hBi : Integrable B (κ.prod volume) :=
    (hκ.mul_prod (integrable_exp_abs_quarter z)).const_mul (C ^ 2 * A ^ 2)
  have hHB (p : ℝ × ℝ) : H p ≤ B p := by
    simpa only [H, B, add_sub_cancel_left, mul_assoc] using
      residual_integrand_le hC hA hpos hh hb (p.2 + p.1) p.2
  have hHnonneg (p : ℝ × ℝ) : 0 ≤ H p :=
    mul_nonneg (mul_nonneg (hpos _) (hpos _)) (sq_nonneg _)
  have hHi : Integrable H (κ.prod volume) := by
    apply hBi.mono' (by dsimp [H]; apply Measurable.aestronglyMeasurable; fun_prop)
    exact .of_forall fun p ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hHnonneg p)]; exact hHB p
  constructor
  · exact (integrable_realJumpPairMeasure_iff _ _ (by fun_prop)).mpr hHi
  · unfold realJumpPairMeasure
    rw [integral_map (by fun_prop) (by fun_prop)]
    change (∫ p, H p ∂κ.prod volume) ≤ _
    refine (integral_mono hHi hBi hHB).trans_eq ?_
    dsimp [B]
    rw [integral_const_mul, integral_prod_mul (fun r : ℝ ↦ r ^ 2)
      (fun x : ℝ ↦ Real.exp (-|x - z| / 4)), integral_exp_abs_quarter]
    ring

/-- Exact cardinal cancellation and the exponential envelope give a uniform residual
energy estimate; no size of the interpolant's own energy appears on the right. -/
theorem nonlocalEnergy_mul_le_of_pairing_eq_zero (κ : Measure ℝ) [SFinite κ]
    {h : ℝ → ℝ} {b : ℝ → ℂ} {C A z : ℝ} (hm : Measurable h) (bm : Measurable b)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hpos : ∀ x, 0 ≤ h x)
    (hh : ∀ x, h x ≤ C * Real.exp (-|x - z| / 2))
    (hb : ∀ x y, ‖b x - b y‖ ≤ A * |x - y| *
      Real.exp ((|x - z| + |y - z|) / 8))
    (hκ : Integrable (fun r : ℝ ↦ r ^ 2) κ)
    (hjump : Integrable (fun p : ℝ × ℝ ↦ ‖(h p.1 : ℂ) * b p.1 - (h p.2 : ℂ) * b p.2‖ ^ 2)
      (realJumpPairMeasure κ))
    (hpair : Integrable (fun p : ℝ × ℝ ↦ (h p.1 - h p.2) *
      (‖b p.1‖ ^ 2 * h p.1 - ‖b p.2‖ ^ 2 * h p.2)) (realJumpPairMeasure κ))
    (horth : realNonlocalPairing volume (realJumpPairMeasure κ) h (fun x ↦ ‖b x‖ ^ 2 * h x) = 0) :
    nonlocalEnergy volume (realJumpPairMeasure κ) (fun x ↦ (h x : ℂ) * b x) ≤
      4 * C ^ 2 * A ^ 2 * ∫ r : ℝ, r ^ 2 ∂κ := by
  rw [nonlocalEnergy_mul_eq _ _ h b hjump hpair, horth, zero_add]
  have hi := (nonlocal_residual_integrable_and_le κ hm bm hC hA hpos hh hb hκ).2
  linarith

/-- The complete cardinal residual bound. Bounded Lipschitz multiplication supplies both
admissibility of the orthogonality test and all integrability needed for cancellation. -/
theorem nonlocal_cardinal_residual_energy_le (κ : Measure ℝ) [SFinite κ]
    (S : Set ℝ) {z C A : ℝ} {h : ℝ → ℝ} {b : ℝ → ℂ}
    (hc : Continuous h) (h₂ : MemLp h 2)
    (hJ : MemLp (fun p : ℝ × ℝ ↦ h p.1 - h p.2) 2 (realJumpPairMeasure κ))
    (hS : ∀ y ∈ S, h y = 0) (hC : 0 ≤ C) (hA : 0 ≤ A) (hpos : ∀ x, 0 ≤ h x)
    (hh : ∀ x, h x ≤ C * Real.exp (-|x - z| / 2)) {B L : NNReal}
    (hB : ∀ x, ‖b x‖ ≤ B) (hb : LipschitzWith L b) (bz : b z = 0)
    (hbw : ∀ x y, ‖b x - b y‖ ≤ A * |x - y| *
      Real.exp ((|x - z| + |y - z|) / 8))
    (hκ : Integrable (fun r : ℝ ↦ r ^ 2) κ)
    (horth : ∀ v : ℝ → ℝ, Continuous v → MemLp v 2 →
      MemLp (fun p : ℝ × ℝ ↦ v p.1 - v p.2) 2 (realJumpPairMeasure κ) →
      v z = 0 → (∀ y ∈ S, v y = 0) →
      realNonlocalPairing volume (realJumpPairMeasure κ) h v = 0) :
    nonlocalEnergy volume (realJumpPairMeasure κ) (fun x ↦ (h x : ℂ) * b x) ≤
      4 * C ^ 2 * A ^ 2 * ∫ r : ℝ, r ^ 2 ∂κ := by
  have hbc := hb.continuous
  have htest := memLp_norm_sq_mul_and_jump κ hc.measurable h₂ hB hb hκ hJ
  have hp : realNonlocalPairing volume (realJumpPairMeasure κ) h
      (fun x ↦ ‖b x‖ ^ 2 * h x) = 0 := by
    apply horth _ (by fun_prop) htest.1 htest.2
    · simp only [bz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    · intro y hy
      rw [hS y hy, mul_zero]
  have hJc : MemLp (fun p : ℝ × ℝ ↦ (h p.1 : ℂ) - (h p.2 : ℂ)) 2 (realJumpPairMeasure κ) := by
    apply (hJ.ofReal (K := ℂ)).ae_eq
    exact .of_forall fun p ↦ by dsimp only; exact RCLike.ofReal_sub _ _
  have hprod := (memLp_mul_and_jump_of_lipschitz κ (h := fun x ↦ (h x : ℂ))
    (by fun_prop) h₂.ofReal hB hb hκ hJc).2
  have hjump : Integrable (fun p : ℝ × ℝ ↦
      ‖(h p.1 : ℂ) * b p.1 - (h p.2 : ℂ) * b p.2‖ ^ 2) (realJumpPairMeasure κ) := by
    simpa only [mul_comm] using (memLp_two_iff_integrable_sq_norm hprod.aestronglyMeasurable).mp hprod
  exact nonlocalEnergy_mul_le_of_pairing_eq_zero κ hc.measurable hbc.measurable
    hC hA hpos hh hbw hκ hjump (hJ.integrable_mul htest.2) hp

end RiemannMasullo
