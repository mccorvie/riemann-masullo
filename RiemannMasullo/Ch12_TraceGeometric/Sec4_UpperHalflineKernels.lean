module

public import RiemannMasullo.Ch09_HardySobolev.Sec2
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Prod
public import RiemannMasullo.ForMathlib.Analysis.Fourier.PaleyWienerStrip

/-! # Square-integrable factors for the upper half-line cutoff -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap

namespace RiemannMasullo

/-- The intermediate polynomial weight grows to the right and decays to the left. -/
def upperHalflinePolynomialWeight (m : ℕ) (x : ℝ) : ℝ :=
  ((1 + max x 0) / (1 + max (-x) 0)) ^ m

/-- The auxiliary polynomial weight is everywhere positive. -/
theorem upperHalflinePolynomialWeight_pos (m : ℕ) (x : ℝ) :
    0 < upperHalflinePolynomialWeight m x := by
  unfold upperHalflinePolynomialWeight
  positivity

/-- The growing weight and its reciprocal have the same translation bound. -/
private theorem upperHalflinePolynomialWeight_le_translate (m : ℕ) (x y : ℝ) :
    upperHalflinePolynomialWeight m x ≤
      upperHalflinePolynomialWeight m y * (1 + |x - y|) ^ (2 * m) := by
  let p (t : ℝ) := 1 + max t 0
  let D := 1 + |x - y|
  have hp (t : ℝ) : 0 < p t := by dsimp only [p]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hpAdd (u v : ℝ) : p u ≤ p v * (1 + |u - v|) := by
    have h := (le_abs_self (max u 0 - max v 0)).trans (abs_max_sub_max_le_abs u v 0)
    have hcross : 0 ≤ max v 0 * |u - v| := mul_nonneg (le_max_right _ _) (abs_nonneg _)
    dsimp only [p]
    nlinarith
  have hn : p (-y) ≤ p (-x) * D := by
    simpa only [D, show -y - -x = x - y by ring] using hpAdd (-y) (-x)
  have hbase : p x / p (-x) ≤ p y / p (-y) * D ^ 2 := by
    calc
      _ ≤ (p y * D ^ 2) / p (-y) := by
        apply (div_le_div_iff₀ (hp (-x)) (hp (-y))).2
        calc
          p x * p (-y) ≤ (p y * D) * (p (-x) * D) :=
            mul_le_mul (hpAdd x y) hn (hp (-y)).le (mul_nonneg (hp y).le hD)
          _ = _ := by ring
      _ = _ := by ring
  change (p x / p (-x)) ^ m ≤ (p y / p (-y)) ^ m * D ^ (2 * m)
  exact (pow_le_pow_left₀ (div_nonneg (hp x).le (hp (-x)).le) hbase m).trans_eq (by
    rw [mul_pow, ← pow_mul])

/-- The square of the Green kernel absorbs each translation power. -/
private theorem integrable_upperHalflineGreenDifferenceMajorant (m : ℕ) :
    Integrable (fun u : ℝ ↦ (1 + |u|) ^ (4 * m) * Real.exp (-2 * |u|) / 4) := by
  simpa only [Real.rpow_natCast] using
    (integrable_one_add_abs_rpow_mul_exp_neg_mul_abs (c := 2) (by norm_num) ((4 * m : ℕ) : ℝ)).div_const 4

private theorem continuous_upperHalflinePolynomialWeight (m : ℕ) :
    Continuous (upperHalflinePolynomialWeight m) := by
  unfold upperHalflinePolynomialWeight
  exact ((continuous_const.add (continuous_id.max continuous_const)).div
    (continuous_const.add (continuous_neg.max continuous_const))
    (fun x : ℝ ↦ ne_of_gt (show 0 < 1 + max (-x) 0 from
      lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (le_max_right _ _))))).pow m

private theorem upperHalflinePolynomialWeight_neg (m : ℕ) (x : ℝ) :
    upperHalflinePolynomialWeight m (-x) = (upperHalflinePolynomialWeight m x)⁻¹ := by
  simp only [upperHalflinePolynomialWeight, neg_neg, ← inv_pow, inv_div]

private theorem upperHalflinePolynomialWeight_sq_of_nonpos (m : ℕ) {x : ℝ} (hx : x ≤ 0) :
    upperHalflinePolynomialWeight m x ^ 2 = (1 + |x|) ^ (-(2 * (m : ℝ))) := by
  rw [upperHalflinePolynomialWeight, max_eq_right hx, max_eq_left (neg_nonneg.mpr hx),
    add_zero, one_div, abs_of_nonpos hx, ← pow_mul, inv_pow,
    Real.rpow_neg (add_nonneg zero_le_one (neg_nonneg.mpr hx)),
    show (2 : ℝ) * m = ((m * 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]

/-- The logarithmic Sobolev weight against the squared auxiliary weight
is integrable on the half-line cut off above. -/
private theorem integrable_upperHalflineOutputMajorant (s : ℝ) (hs : 0 ≤ s) (m : ℕ)
    (hm : s + 1 < 2 * (m : ℝ)) (T : ℝ) :
    Integrable ((Iic T).indicator
      (fun t : ℝ ↦ (1 + t ^ 2) ^ (s / 2) * upperHalflinePolynomialWeight m t ^ 2)) := by
  let W (t : ℝ) := (1 + t ^ 2) ^ (s / 2)
  let F (t : ℝ) := W t * upperHalflinePolynomialWeight m t ^ 2
  have hW : Continuous W := by
    dsimp only [W]
    exact (continuous_const.add (continuous_id.pow 2)).rpow_const fun t ↦
      Or.inl (ne_of_gt (show 0 < 1 + t ^ 2 from by positivity))
  have hF : Continuous F := hW.mul ((continuous_upperHalflinePolynomialWeight m).pow 2)
  have hpow (t : ℝ) : W t ≤ (1 + |t|) ^ s := by
    have hh : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
      nlinarith [sq_abs t, abs_nonneg t]
    calc
      _ ≤ ((1 + |t|) ^ (2 : ℕ)) ^ (s / 2) :=
        Real.rpow_le_rpow (by positivity) hh (by positivity)
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        rw [show ((2 : ℕ) : ℝ) * (s / 2) = s by norm_num; ring]
  have hdecay : Integrable (fun t : ℝ ↦ (1 + |t|) ^ (s - 2 * (m : ℝ))) := by
    have hp : 1 < 2 * (m : ℝ) - s := by linarith
    simpa only [Real.norm_eq_abs, neg_sub] using
      (integrable_one_add_norm (μ := (volume : Measure ℝ)) (r := 2 * (m : ℝ) - s)
        (by simpa using hp))
  have htail : IntegrableOn F (Iic (0 : ℝ)) := by
    refine hdecay.integrableOn.mono' hF.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Iic fun t ht ↦ ?_)
    change t ≤ 0 at ht
    rw [Real.norm_of_nonneg (show 0 ≤ F t by dsimp only [F, W]; positivity)]
    calc
      F t = W t * (1 + |t|) ^ (-(2 * (m : ℝ))) := by
        change W t * upperHalflinePolynomialWeight m t ^ 2 = _
        rw [upperHalflinePolynomialWeight_sq_of_nonpos m ht]
      _ ≤ (1 + |t|) ^ s * (1 + |t|) ^ (-(2 * (m : ℝ))) :=
        mul_le_mul_of_nonneg_right (hpow t) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity), sub_eq_add_neg]
  have hcompact : IntegrableOn F (Icc (0 : ℝ) (max 0 T)) := hF.integrableOn_Icc
  apply (integrable_indicator_iff measurableSet_Iic).mpr
  refine (htail.union hcompact).mono_set fun t ht ↦ ?_
  have htT : t ≤ T := ht
  by_cases h : t ≤ 0
  · exact Or.inl h
  · exact Or.inr ⟨(lt_of_not_ge h).le, htT.trans (le_max_right _ _)⟩

/-- The reciprocal auxiliary weight is square integrable on the
half-line on which the input is supported. -/
private theorem integrable_upperHalflineInputMajorant (m : ℕ) (hm : 1 < 2 * (m : ℝ)) (a : ℝ) :
    Integrable ((Ici a).indicator (fun t : ℝ ↦ (upperHalflinePolynomialWeight m t)⁻¹ ^ 2)) := by
  have h := integrable_upperHalflineOutputMajorant 0 le_rfl m (by simpa using hm) (-a)
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable h
  convert hneg using 1
  ext t
  have ht : (-t ∈ Iic (-a)) = (t ∈ Ici a) := propext (by simp only [mem_Iic, mem_Ici, neg_le_neg_iff])
  simp only [Function.comp_apply, indicator_apply, ht, zero_div, Real.rpow_zero, one_mul,
    upperHalflinePolynomialWeight_neg]

/-- Squared Schwartz decay absorbs the polynomial power introduced by
the difference shear in the input kernel. -/
private theorem integrable_upperHalflineSchwartzDifferenceMajorant (m : ℕ) (r : 𝓢(ℝ, ℂ)) :
    Integrable (fun u : ℝ ↦ (1 + |u|) ^ (4 * m) * ‖r u‖ ^ 2) := by
  let W (u : ℝ) := (1 + ‖u‖ ^ 2) ^ (m : ℝ)
  have hW : W.HasTemperateGrowth := Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (m : ℝ)
  let g := SchwartzMap.smulLeftCLM ℂ W r
  have hg := (memLp_two_iff_integrable_sq_norm g.continuous.aestronglyMeasurable).mp (g.memLp 2 volume)
  have hgEq (u : ℝ) : ‖g u‖ ^ 2 = W u ^ 2 * ‖r u‖ ^ 2 := by
    change ‖SchwartzMap.smulLeftCLM ℂ W r u‖ ^ 2 = _
    rw [SchwartzMap.smulLeftCLM_apply_apply hW, norm_smul, mul_pow,
      Real.norm_of_nonneg (show 0 ≤ W u by dsimp only [W]; positivity)]
  refine (hg.const_mul ((2 : ℝ) ^ (2 * m))).mono'
    (((continuous_const.add continuous_abs).pow (4 * m)).mul (r.continuous.norm.pow 2)).aestronglyMeasurable
    (ae_of_all _ fun u ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), hgEq u, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hb : (1 + |u|) ^ 2 ≤ 2 * (1 + ‖u‖ ^ 2) := by
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|u| - 1)]
  calc
    (1 + |u|) ^ (4 * m) = ((1 + |u|) ^ (2 : ℕ)) ^ (2 * m) := by
      rw [← pow_mul, show 2 * (2 * m) = 4 * m by omega]
    _ ≤ (2 * (1 + ‖u‖ ^ 2)) ^ (2 * m) :=
      pow_le_pow_left₀ (by positivity) hb _
    _ = _ := by
      simp only [W, Real.rpow_natCast, mul_pow, ← pow_mul, show m * 2 = 2 * m by omega]

/-- Pointwise separated square majorant for the Green factor. -/
private theorem upperHalflineGreenRow_sq_le (s : ℝ) (m : ℕ) (T : ℝ)
    (ρ : ℝ → ℝ) (hρ : ∀ t, |ρ t| ≤ 1) (hρT : ∀ t, T < t → ρ t = 0) (t z : ℝ) :
    ‖(ρ t : ℂ) * (Real.sqrt ((1 + t ^ 2) ^ (s / 2)) : ℂ) *
      ((Real.exp (-|t - z|) : ℂ) / 2) * (upperHalflinePolynomialWeight m z : ℂ)‖ ^ 2 ≤
    (Iic T).indicator (fun t : ℝ ↦ (1 + t ^ 2) ^ (s / 2) * upperHalflinePolynomialWeight m t ^ 2) t *
      ((1 + |t - z|) ^ (4 * m) * Real.exp (-2 * |t - z|) / 4) := by
  by_cases ht : t ∈ Iic T
  · rw [indicator_of_mem ht]
    let W := (1 + t ^ 2) ^ (s / 2)
    let D := 1 + |t - z|
    let G := Real.exp (-|t - z|) / 2
    have hW : 0 ≤ W := by dsimp only [W]; positivity
    have hG : 0 ≤ G := by dsimp only [G]; positivity
    have hGcast : (Real.exp (-|t - z|) : ℂ) / 2 = (G : ℂ) := by
      simp only [G, Complex.ofReal_div, Complex.ofReal_ofNat]
    have hGsq : G ^ 2 = Real.exp (-2 * |t - z|) / 4 := by
      dsimp only [G]
      have hExp : Real.exp (-|t - z|) ^ 2 = Real.exp (-2 * |t - z|) := by
        rw [pow_two, ← Real.exp_add, show -|t - z| + -|t - z| = -2 * |t - z| by ring]
      rw [div_pow, hExp, show (2 : ℝ) ^ 2 = 4 by norm_num]
    have hw : upperHalflinePolynomialWeight m z ≤ upperHalflinePolynomialWeight m t * D ^ (2 * m) := by
      simpa only [D, abs_sub_comm z t] using upperHalflinePolynomialWeight_le_translate m z t
    have hρsq : |ρ t| ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hρ t) 2
    have h₁ : |ρ t| ^ 2 * W * G ^ 2 ≤ W * G ^ 2 :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρsq hW) (sq_nonneg G)).trans_eq
        (by rw [one_mul])
    have h₂ : upperHalflinePolynomialWeight m z ^ 2 ≤
        (upperHalflinePolynomialWeight m t * D ^ (2 * m)) ^ 2 :=
      pow_le_pow_left₀ (upperHalflinePolynomialWeight_pos m z).le hw _
    calc
      _ = |ρ t| ^ 2 * W * G ^ 2 * upperHalflinePolynomialWeight m z ^ 2 := by
        change ‖(ρ t : ℂ) * (Real.sqrt W : ℂ) * ((Real.exp (-|t - z|) : ℂ) / 2) *
          (upperHalflinePolynomialWeight m z : ℂ)‖ ^ 2 = _
        rw [hGcast]
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg hG, abs_of_pos (upperHalflinePolynomialWeight_pos m z), mul_pow,
          Real.sq_sqrt hW]
      _ ≤ W * G ^ 2 * (upperHalflinePolynomialWeight m t * D ^ (2 * m)) ^ 2 :=
        mul_le_mul h₁ h₂ (sq_nonneg _) (mul_nonneg hW (sq_nonneg G))
      _ = _ := by
        rw [mul_pow, ← pow_mul, show (2 * m) * 2 = 4 * m by omega, hGsq]
        dsimp only [W, D]
        ring
  · have ht' : T < t := lt_of_not_ge (show ¬ t ≤ T from ht)
    simp [indicator_of_notMem ht, hρT t ht']

/-- Pointwise separated square majorant for the Schwartz factor. -/
private theorem upperHalflineSchwartzRow_sq_le (m : ℕ) (a : ℝ) (r : ℝ → ℂ) (z y : ℝ) :
    ‖(upperHalflinePolynomialWeight m z : ℂ)⁻¹ * (Ici a).indicator (fun y ↦ r (z - y)) y‖ ^ 2 ≤
      (Ici a).indicator (fun y : ℝ ↦ (upperHalflinePolynomialWeight m y)⁻¹ ^ 2) y *
        ((1 + |z - y|) ^ (4 * m) * ‖r (z - y)‖ ^ 2) := by
  by_cases hy : y ∈ Ici a
  · simp only [indicator_of_mem hy]
    let D := 1 + |z - y|
    have hWz := upperHalflinePolynomialWeight_pos m z
    have hWy := upperHalflinePolynomialWeight_pos m y
    have hinv : (upperHalflinePolynomialWeight m z)⁻¹ ≤
        (upperHalflinePolynomialWeight m y)⁻¹ * D ^ (2 * m) := by
      calc
        (upperHalflinePolynomialWeight m z)⁻¹ = 1 / upperHalflinePolynomialWeight m z := (one_div _).symm
        _ ≤ D ^ (2 * m) / upperHalflinePolynomialWeight m y := by
          apply (div_le_div_iff₀ hWz hWy).mpr
          rw [one_mul, mul_comm (D ^ (2 * m))]
          simpa only [D, abs_sub_comm y z] using upperHalflinePolynomialWeight_le_translate m y z
        _ = _ := by rw [div_eq_mul_inv, mul_comm]
    calc
      _ = (upperHalflinePolynomialWeight m z)⁻¹ ^ 2 * ‖r (z - y)‖ ^ 2 := by
        simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hWz, mul_pow]
      _ ≤ ((upperHalflinePolynomialWeight m y)⁻¹ * D ^ (2 * m)) ^ 2 * ‖r (z - y)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_nonneg.mpr hWz.le) hinv _) (sq_nonneg _)
      _ = _ := by
        rw [mul_pow, ← pow_mul, show (2 * m) * 2 = 4 * m by omega, mul_assoc]
  · simp [indicator_of_notMem hy]

/- For source-first (z,t) apply upperHalflineGreenRow_sq_le ... p.2 p.1
with measurePreserving_prod_sub_swap volume volume and abs_sub_comm on
the Green difference. For source-first (y,z) apply
upperHalflineSchwartzRow_sq_le ... p.2 p.1 with
measurePreserving_prod_sub volume volume. -/

/-- A real integrable upper bound factors after a Haar-preserving shear. -/
private theorem integrable_of_preserving_product_majorant
    {σ : ℝ × ℝ → ℝ × ℝ}
    (hσ : MeasurePreserving σ ((volume : Measure ℝ).prod volume) (volume.prod volume))
    {H : ℝ × ℝ → ℝ} (hH : AEStronglyMeasurable H ((volume : Measure ℝ).prod volume))
    {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (h : ∀ p, ‖H p‖ ≤ f (σ p).1 * g (σ p).2) : Integrable H (volume.prod volume) := by
  have hprod : Integrable (fun p ↦ f (σ p).1 * g (σ p).2) ((volume : Measure ℝ).prod volume) :=
    hσ.integrable_comp_of_integrable (hf.mul_prod hg)
  exact hprod.mono' hH (ae_of_all _ h)

/-- Square-integrability with a density in the output variable is ordinary
integrability of the density times the squared kernel norm. -/
private theorem memLp_two_prod_withDensity_right
    {K : ℝ × ℝ → ℂ} (hK : AEStronglyMeasurable K ((volume : Measure ℝ).prod volume))
    {W : ℝ → ℝ} (hW : Measurable W) (hWnonneg : ∀ t, 0 ≤ W t)
    (h : Integrable (fun p : ℝ × ℝ ↦ W p.2 * ‖K p‖ ^ 2) (volume.prod volume)) :
    MemLp K 2 ((volume : Measure ℝ).prod (volume.withDensity (fun t ↦ ENNReal.ofReal (W t)))) := by
  rw [prod_withDensity_right hW.ennreal_ofReal]
  apply (memLp_two_iff_integrable_sq_norm
    (hK.mono_ac (withDensity_absolutelyContinuous _ _))).2
  apply (integrable_withDensity_iff_integrable_smul'
    (hW.ennreal_ofReal.comp measurable_snd) (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2
  refine h.congr (ae_of_all _ fun p ↦ ?_)
  change W p.2 * ‖K p‖ ^ 2 = (ENNReal.ofReal (W p.2)).toReal • ‖K p‖ ^ 2
  rw [ENNReal.toReal_ofReal (hWnonneg p.2), smul_eq_mul]

/-- A source restriction can be tested by a mask on the squared kernel norm. -/
private theorem memLp_two_restrict_prod
    {K : ℝ × ℝ → ℂ} (hK : AEStronglyMeasurable K ((volume : Measure ℝ).prod volume)) (a : ℝ)
    (h : Integrable ((Ici a ×ˢ (univ : Set ℝ)).indicator (fun p ↦ ‖K p‖ ^ 2))
      (volume.prod volume)) :
    MemLp K 2 (((volume : Measure ℝ).restrict (Ici a)).prod volume) := by
  rw [Measure.restrict_prod_eq_prod_univ]
  have hK' : AEStronglyMeasurable K
      ((volume.prod volume).restrict (Ici a ×ˢ (univ : Set ℝ))) :=
    hK.mono_ac (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  apply (memLp_two_iff_integrable_sq_norm hK').2
  exact (integrable_indicator_iff (measurableSet_Ici.prod MeasurableSet.univ)).1 h

/-- The Green factor is square integrable into the weighted real output
space for an upper cutoff. Its kernel is written in source-first order. -/
theorem memLp_upperHalflineGreenFactor
    (s : ℝ) (hs : 0 ≤ s) (m : ℕ) (hm : s + 1 < 2 * (m : ℝ)) (T : ℝ)
    (ρ : ℝ → ℝ) (hρm : Measurable ρ) (hρ : ∀ t, |ρ t| ≤ 1)
    (hρT : ∀ t, T < t → ρ t = 0) :
    MemLp (fun p : ℝ × ℝ ↦ (ρ p.2 : ℂ) *
      ((Real.exp (-|p.2 - p.1|) : ℂ) / 2) * (upperHalflinePolynomialWeight m p.1 : ℂ)) 2
      ((volume : Measure ℝ).prod (intervalSobolevMeasure (volume : Measure ℝ) id 0 0 s)) := by
  let W (t : ℝ) : ℝ := (1 + t ^ 2) ^ (s / 2)
  let G (u : ℝ) : ℂ := (Real.exp (-|u|) : ℂ) / 2
  let K (p : ℝ × ℝ) : ℂ := (ρ p.2 : ℂ) * G (p.2 - p.1) *
    (upperHalflinePolynomialWeight m p.1 : ℂ)
  have hW : Continuous W := by
    unfold W
    exact (continuous_const.add (continuous_id.pow 2)).rpow_const
      (fun t : ℝ ↦ Or.inl (ne_of_gt (show 0 < 1 + t ^ 2 from by positivity)))
  have hWnonneg (t : ℝ) : 0 ≤ W t := by unfold W; positivity
  have hG : Continuous G := by unfold G; fun_prop
  have hK : Measurable K :=
    ((Complex.continuous_ofReal.measurable.comp (hρm.comp measurable_snd)).mul
      (hG.measurable.comp (measurable_snd.sub measurable_fst))).mul
        ((Complex.continuous_ofReal.comp
          (continuous_upperHalflinePolynomialWeight m)).measurable.comp measurable_fst)
  have hν : intervalSobolevMeasure (volume : Measure ℝ) id 0 0 s =
      volume.withDensity (fun t ↦ ENNReal.ofReal (W t)) := by
    simp [intervalSobolevMeasure, intervalSobolevDensity, W]
  rw [hν]
  apply memLp_two_prod_withDensity_right hK.aestronglyMeasurable hW.measurable hWnonneg
  refine integrable_of_preserving_product_majorant
    (measurePreserving_prod_sub_swap volume volume)
    ((hW.measurable.comp measurable_snd).mul (hK.norm.pow_const 2)).aestronglyMeasurable
    (integrable_upperHalflineOutputMajorant s hs m hm T)
    (integrable_upperHalflineGreenDifferenceMajorant m) ?_
  intro p
  rw [Real.norm_of_nonneg (mul_nonneg (hWnonneg p.2) (sq_nonneg _))]
  have hScale : ‖(Real.sqrt (W p.2) : ℂ) * K p‖ ^ 2 = W p.2 * ‖K p‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt (hWnonneg _)]
  rw [← hScale]
  have hCoeff : (Real.sqrt (W p.2) : ℂ) * K p =
      (ρ p.2 : ℂ) * (Real.sqrt (W p.2) : ℂ) * G (p.2 - p.1) *
        (upperHalflinePolynomialWeight m p.1 : ℂ) := by unfold K; ring
  rw [hCoeff]
  simpa only [W, G, abs_sub_comm p.2 p.1] using
    upperHalflineGreenRow_sq_le s m T ρ hρ hρT p.2 p.1

/-- The Schwartz factor is square integrable from the right-half-line
input measure. Its kernel is written in source-first order. -/
theorem memLp_upperHalflineSchwartzFactor
    (m : ℕ) (hm : 1 < 2 * (m : ℝ)) (a : ℝ) (r : 𝓢(ℝ, ℂ)) :
    MemLp (fun p : ℝ × ℝ ↦ (upperHalflinePolynomialWeight m p.2 : ℂ)⁻¹ * r (p.2 - p.1)) 2
      (((volume : Measure ℝ).restrict (Ici a)).prod volume) := by
  let K (p : ℝ × ℝ) : ℂ :=
    (upperHalflinePolynomialWeight m p.2 : ℂ)⁻¹ * r (p.2 - p.1)
  have hw : Measurable (fun t : ℝ ↦ (upperHalflinePolynomialWeight m t : ℂ)) :=
    (Complex.continuous_ofReal.comp (continuous_upperHalflinePolynomialWeight m)).measurable
  have hK : Measurable K :=
    ((hw.comp measurable_snd).inv).mul
        (r.continuous.measurable.comp (measurable_snd.sub measurable_fst))
  apply memLp_two_restrict_prod hK.aestronglyMeasurable a
  refine integrable_of_preserving_product_majorant (measurePreserving_prod_sub volume volume)
    ((hK.norm.pow_const 2).indicator (measurableSet_Ici.prod MeasurableSet.univ)).aestronglyMeasurable
    (integrable_upperHalflineInputMajorant m hm a)
    (integrable_upperHalflineSchwartzDifferenceMajorant m r) ?_
  intro p
  by_cases hp : p.1 ∈ Ici a
  · have hmem : p ∈ Ici a ×ˢ (univ : Set ℝ) := ⟨hp, mem_univ _⟩
    rw [indicator_of_mem hmem, Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [K, indicator_of_mem hp] using
      upperHalflineSchwartzRow_sq_le m a (r : ℝ → ℂ) p.2 p.1
  · have hmem : p ∉ Ici a ×ˢ (univ : Set ℝ) := fun h ↦ hp h.1
    simp only [indicator_of_notMem hmem, norm_zero, indicator_of_notMem hp, zero_mul, le_refl]

end RiemannMasullo
