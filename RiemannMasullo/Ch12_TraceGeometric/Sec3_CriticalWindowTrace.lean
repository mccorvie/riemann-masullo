module

public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.MovingHalfLine
public import RiemannMasullo.Ch09_HardySobolev.Sec3
public import RiemannMasullo.AppC_LCTVS.Sec3a_part2
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # The lower three-quarter window of a translated nuclear trace

The two Haar orbit marginals control a pair of weighted L² legs. A single
singular expansion then gives the integrated bound for every nuclear operator. -/

@[expose] public noncomputable section

section
open Classical Filter MeasureTheory Set
open scoped ENNReal Topology
namespace RiemannMasullo

/-- Two marginal estimates along a Haar translation orbit bound its bilinear integral.
The log coordinate need only intertwine the given section and addition. -/
theorem lintegral_orbit_schur {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [MeasurableInv G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (g : ℝ → G) (hg : Measurable g) (ℓ : G → ℝ) (hℓ : Measurable ℓ)
    (hshift : ∀ y x, ℓ (g y * x) = ℓ x+y)
    (k : ℝ → ℝ → ℝ≥0∞) (hk : Measurable (Function.uncurry k)) {A B : ℝ≥0∞}
    (hout : ∀ t, (∫⁻ y : ℝ, k y t) ≤ A)
    (hin : ∀ t, (∫⁻ y : ℝ, k y (t+y)) ≤ B)
    {a b : G → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b) :
    (∫⁻ y : ℝ, ∫⁻ x : G, k y (ℓ x) * a ((g y)⁻¹*x) * b x ∂μ) ≤
      (B * ∫⁻ x, a x ^ 2 ∂μ) ^ (1/2 : ℝ) * (A * ∫⁻ x, b x ^ 2 ∂μ) ^ (1/2 : ℝ) := by
  let K (p : ℝ × G) := k p.1 (ℓ p.2)
  let D (p : ℝ × G) := a ((g p.1)⁻¹*p.2)
  have hK : Measurable K := hk.comp (measurable_fst.prodMk (hℓ.comp measurable_snd))
  have hD : Measurable D := ha.comp ((hg.comp measurable_fst).inv.mul measurable_snd)
  have marginal (k' : ℝ → G → ℝ≥0∞) (hm : Measurable (Function.uncurry k'))
      (c : G → ℝ≥0∞) (hc : Measurable c) (L : ℝ≥0∞) (h : ∀ x, (∫⁻ y, k' y x) ≤ L) :
      (∫⁻ y : ℝ, ∫⁻ x, k' y x * c x ∂μ) ≤ L * ∫⁻ x, c x ∂μ := by
    rw [lintegral_lintegral_swap (f := fun y x ↦ k' y x * c x) (hm.mul (hc.comp measurable_snd)).aemeasurable,
      ← lintegral_const_mul _ hc]
    apply lintegral_mono
    intro x
    change (∫⁻ y : ℝ, k' y x * c x) ≤ _
    rw [lintegral_mul_const (f := fun y : ℝ ↦ k' y x) (c x) (hm.comp (measurable_id.prodMk measurable_const))]
    exact mul_le_mul' (h x) le_rfl
  have hA : (∫⁻ p : ℝ × G, K p * D p ^ 2 ∂volume.prod μ) ≤ B * ∫⁻ x, a x ^ 2 ∂μ := by
    rw [lintegral_prod (fun p : ℝ × G ↦ K p * D p ^ 2) (hK.mul (hD.pow_const 2)).aemeasurable]
    calc
      _ = ∫⁻ y : ℝ, ∫⁻ x, k y (ℓ x+y) * a x ^ 2 ∂μ := by
        apply lintegral_congr
        intro y
        change (∫⁻ x, k y (ℓ x) * a ((g y)⁻¹*x)^2 ∂μ) = _
        rw [← lintegral_mul_left_eq_self (μ := μ) (fun x ↦ k y (ℓ x) * a ((g y)⁻¹*x)^2) (g y)]
        simp only [hshift,inv_mul_cancel_left]
      _ ≤ _ := marginal (fun y x ↦ k y (ℓ x+y)) (hk.comp (measurable_fst.prodMk ((hℓ.comp measurable_snd).add measurable_fst)))
        _ (ha.pow_const 2) B (fun x ↦ hin (ℓ x))
  have hB : (∫⁻ p : ℝ × G, K p * b p.2 ^ 2 ∂volume.prod μ) ≤ A * ∫⁻ x, b x ^ 2 ∂μ := by
    rw [lintegral_prod (fun p : ℝ × G ↦ K p * b p.2 ^ 2) (hK.mul ((hb.comp measurable_snd).pow_const 2)).aemeasurable]
    exact marginal (fun y x ↦ k y (ℓ x)) hK _ (hb.pow_const 2) A (fun x ↦ hout (ℓ x))
  have hprod := ENNReal.lintegral_mul_norm_pow_le (μ := volume.prod μ)
    (f := fun p : ℝ × G ↦ K p * D p ^ 2) (g := fun p : ℝ × G ↦ K p * b p.2 ^ 2)
    (hK.mul (hD.pow_const 2)).aemeasurable (hK.mul ((hb.comp measurable_snd).pow_const 2)).aemeasurable
    (p := (1/2 : ℝ)) (q := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have factor (k a b : ℝ≥0∞) : (k*a^2)^(1/2:ℝ)*(k*b^2)^(1/2:ℝ) = k*a*b := by
    simp only [ENNReal.mul_rpow_of_nonneg _ _ (show (0:ℝ) ≤ 1/2 by norm_num)]
    rw [← ENNReal.rpow_two a,← ENNReal.rpow_mul,← ENNReal.rpow_two b,← ENNReal.rpow_mul]
    rw [mul_mul_mul_comm,← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num [mul_assoc]
  simp only [factor] at hprod
  rw [← lintegral_prod (fun p : ℝ × G ↦ K p * D p * b p.2) ((hK.mul hD).mul (hb.comp measurable_snd)).aemeasurable]
  exact hprod.trans (mul_le_mul' (ENNReal.rpow_le_rpow hA (by norm_num)) (ENNReal.rpow_le_rpow hB (by norm_num)))

end RiemannMasullo
end

section
open Classical Set MeasureTheory
open scoped ENNReal Topology
namespace RiemannMasullo

/-- Square root of the strip density at Sobolev degree three. -/
def criticalStripRoot (α t : ℝ) : ℝ := Real.exp (α*|t|) * (1+t^2)^(3/4 : ℝ)

theorem criticalStripRoot_pos (α t : ℝ) : 0 < criticalStripRoot α t := by
  unfold criticalStripRoot; positivity

theorem continuous_criticalStripRoot (α : ℝ) : Continuous (criticalStripRoot α) := by
  unfold criticalStripRoot
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
    ((continuous_const.add (continuous_id.pow 2)).rpow_const fun t ↦ Or.inl (by change 1+t^2 ≠ 0; positivity))

theorem criticalStripRoot_sq {α : ℝ} (hα : 0 ≤ α) (t : ℝ) :
    criticalStripRoot α t ^ 2 = intervalSobolevDensity (-α) α 3 t := by
  have hE : max (Real.exp (2*(-α)*t)) (Real.exp (2*α*t)) = Real.exp (2*α*|t|) := by
    rcases le_or_gt 0 t with ht|ht
    · rw [abs_of_nonneg ht,max_eq_right (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hα ht]))]
    · rw [abs_of_neg ht,max_eq_left (Real.exp_le_exp.mpr (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hα ht.le]))]
      congr 1; ring
  rw [criticalStripRoot, mul_pow, sq (Real.exp _), ← Real.exp_add,intervalSobolevDensity,hE,
    ← Real.rpow_mul_natCast (by positivity : 0 ≤ 1+t^2)]
  congr 2 <;> norm_num; ring

/-- The negative-half-line coefficient, extended by zero to negative translations. -/
def negativeOrbitKernel (α y : ℝ) : ℝ := (Ioi 0).indicator (fun t ↦ Real.exp ((-3*α/2)*t)) y

theorem measurable_negativeOrbitKernel (α : ℝ) : Measurable (negativeOrbitKernel α) :=
  (Real.measurable_exp.comp (measurable_const.mul measurable_id)).indicator measurableSet_Ioi

theorem negativeOrbitKernel_nonneg (α y : ℝ) : 0 ≤ negativeOrbitKernel α y :=
  indicator_nonneg (fun _ _ ↦ (Real.exp_pos _).le) _

theorem lintegral_negativeOrbitKernel {α : ℝ} (hα : 0 < α) :
    (∫⁻ y : ℝ, ENNReal.ofReal (negativeOrbitKernel α y)) = ENNReal.ofReal (2/(3*α)) := by
  have hneg : -3*α/2 < 0 := by linarith
  have hm : Integrable (negativeOrbitKernel α) :=
    (integrableOn_exp_mul_Ioi hneg 0).integrable_indicator measurableSet_Ioi
  rw [← ofReal_integral_eq_lintegral_ofReal hm (ae_of_all _ (negativeOrbitKernel_nonneg α))]
  congr 1
  unfold negativeOrbitKernel
  rw [integral_indicator measurableSet_Ioi,integral_exp_mul_Ioi hneg]
  simp only [mul_zero,Real.exp_zero]
  field_simp

/-- The pointwise two-region majorant for the critical physical mask. -/
theorem criticalStripRoot_lower_ratio {α y t : ℝ} (hy : 0 < y)
    (ht : t ≤ 3*y/4) :
    Real.exp (-α*y/2) * criticalStripRoot α t ≤
      (negativeOrbitKernel α y + (9:ℝ)^(3/4:ℝ)*criticalWindowKernel α t (y-t)) *
        criticalStripRoot α (t-y) := by
  have hP : 0 ≤ (1+(t-y)^2)^(3/4:ℝ) := Real.rpow_nonneg (by positivity) _
  have ht' : t-y ≤ 0 := by linarith
  have hN : negativeOrbitKernel α y = Real.exp ((-3*α/2)*y) := indicator_of_mem hy _
  rcases le_or_gt t 0 with hn|hp
  · apply le_trans _ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg (by positivity)
      (criticalWindowKernel_nonneg _ _ _))) (criticalStripRoot_pos _ _).le)
    rw [hN,criticalStripRoot,criticalStripRoot,abs_of_nonpos hn,abs_of_nonpos ht',← mul_assoc,
      ← mul_assoc,← Real.exp_add,← Real.exp_add]
    apply mul_le_mul (le_of_eq (congrArg Real.exp (by ring))) _ (by positivity) (Real.exp_pos _).le
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hn hy.le,sq_nonneg y]
  · have hm : t ∈ Icc 0 (3*(y-t)) := ⟨hp.le,by linarith⟩
    apply le_trans _ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (negativeOrbitKernel_nonneg _ _))
      (criticalStripRoot_pos _ _).le)
    rw [criticalWindowKernel,indicator_of_mem hm,criticalStripRoot,criticalStripRoot,
      abs_of_pos hp,abs_of_nonpos ht']
    have hpol : (1+t^2)^(3/4:ℝ) ≤ (9:ℝ)^(3/4:ℝ)*(1+(t-y)^2)^(3/4:ℝ) := by
      rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 9) (by positivity : 0 ≤ 1+(t-y)^2)]
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      nlinarith [mul_nonneg (by linarith : 0 ≤ 3*(y-t)-t) (by linarith : 0 ≤ 3*(y-t)+t)]
    have hex : Real.exp (-α*y/2)*Real.exp (α*t) =
        Real.exp (-(α/2)*(3*(y-t)-t))*Real.exp (α* -(t-y)) := by
      rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
    calc
      _ = (Real.exp (-α*y/2)*Real.exp (α*t))*(1+t^2)^(3/4:ℝ) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hpol (by positivity : 0 ≤ Real.exp (-α*y/2)*Real.exp (α*t))).trans_eq
        (by rw [hex]; ring)

end RiemannMasullo
end

section
open Classical Filter MeasureTheory Set
open scoped ENNReal Topology
namespace RiemannMasullo

/-- A two-region majorant in translation and output log coordinates. -/
def criticalOrbitMajorant (α y t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (negativeOrbitKernel α y) +
    ENNReal.ofReal ((9:ℝ)^(3/4:ℝ)) * ENNReal.ofReal (criticalWindowKernel α t (y-t))

/-- Sum of the negative-half-line and positive-wedge Schur bounds. -/
def criticalOrbitBound (α : ℝ) : ℝ := 20 / (3 * α)

theorem criticalOrbitBound_nonneg {α : ℝ} (hα : 0 < α) : 0 ≤ criticalOrbitBound α := by
  unfold criticalOrbitBound; positivity

private theorem lintegral_add_scaled {G : Type*} [MeasurableSpace G] (μ : Measure G) [SigmaFinite μ]
    (f k : ℝ → G → ℝ≥0∞) (hf : Measurable (Function.uncurry f)) (hk : Measurable (Function.uncurry k))
    (c : ℝ≥0∞) :
    (∫⁻ y : ℝ, ∫⁻ x, f y x+c*k y x ∂μ) =
      (∫⁻ y : ℝ, ∫⁻ x, f y x ∂μ) + c*(∫⁻ y : ℝ, ∫⁻ x, k y x ∂μ) := by
  have hI (y : ℝ) : (∫⁻ x, f y x+c*k y x ∂μ) = (∫⁻ x, f y x ∂μ) + c*(∫⁻ x, k y x ∂μ) := by
    rw [lintegral_add_left (hf.of_uncurry_left (x := y)),lintegral_const_mul c (hk.of_uncurry_left (x := y))]
  simp_rw [hI]
  have hf' : Measurable (fun y : ℝ ↦ ∫⁻ x, f y x ∂μ) := hf.lintegral_prod_right'
  have hk' : Measurable (fun y : ℝ ↦ ∫⁻ x, k y x ∂μ) := hk.lintegral_prod_right'
  rw [lintegral_add_left hf',lintegral_const_mul c hk']

set_option maxHeartbeats 700000 in
/-- The two marginals have different masses. Apply Schur separately to the
negative half-line and the positive wedge to retain their geometric mean. -/
private theorem critical_schur {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [MeasurableInv G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] (g : ℝ → G)
    (hg : Measurable g) (ℓ : G → ℝ) (hℓ : Measurable ℓ) (hshift : ∀ y x, ℓ (g y*x) = ℓ x+y)
    {α : ℝ} (hα : 0 < α) {u v : G → ℝ≥0∞} (hu : Measurable u) (hv : Measurable v)
    {U V : ℝ≥0∞} (hU : (∫⁻ x, u x^2 ∂μ) = U^2) (hV : (∫⁻ x, v x^2 ∂μ) = V^2) :
    (∫⁻ y : ℝ, ∫⁻ x, criticalOrbitMajorant α y (ℓ x)*u ((g y)⁻¹*x)*v x ∂μ) ≤
      ENNReal.ofReal (20/(3*α))*U*V := by
  let d (y _t : ℝ) := ENNReal.ofReal (negativeOrbitKernel α y)
  let k (y t : ℝ) := ENNReal.ofReal (criticalWindowKernel α t (y-t))
  let c := ENNReal.ofReal ((9:ℝ)^(3/4:ℝ))
  let A := ENNReal.ofReal (2/(3*α))
  let B := ENNReal.ofReal (2/α)
  have hd : Measurable (Function.uncurry d) := ((measurable_negativeOrbitKernel α).comp measurable_fst).ennreal_ofReal
  have hk : Measurable (Function.uncurry k) := ((measurable_criticalWindowKernel α).comp
    (measurable_snd.prodMk (measurable_fst.sub measurable_snd))).ennreal_ofReal
  have hdA (t : ℝ) : (∫⁻ y : ℝ, d y t) ≤ A := (lintegral_negativeOrbitKernel hα).le
  have hdB (t : ℝ) : (∫⁻ y : ℝ, d y (t+y)) ≤ A := (lintegral_negativeOrbitKernel hα).le
  have hkA (t : ℝ) : (∫⁻ y : ℝ, k y t) ≤ A := by
    dsimp only [k]
    simp only [sub_eq_add_neg]
    rw [lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun u ↦ ENNReal.ofReal (criticalWindowKernel α t u)) (-t)]
    exact lintegral_criticalWindowKernel_row_le hα t
  have hkB (t : ℝ) : (∫⁻ y : ℝ, k y (t+y)) ≤ B := by
    dsimp only [k]
    simp only [show ∀ y : ℝ, y-(t+y) = -t by intro y; ring]
    rw [lintegral_add_left_eq_self (μ := (volume : Measure ℝ))
      (fun x ↦ ENNReal.ofReal (criticalWindowKernel α x (-t))) t]
    exact lintegral_criticalWindowKernel_column_le hα (-t)
  let J (q : ℝ → ℝ → ℝ≥0∞) (y : ℝ) (x : G) := q y (ℓ x)*u ((g y)⁻¹*x)*v x
  have hm (q : ℝ → ℝ → ℝ≥0∞) (hq : Measurable (Function.uncurry q)) : Measurable (Function.uncurry (J q)) :=
    ((hq.comp (measurable_fst.prodMk (hℓ.comp measurable_snd))).mul
      (hu.comp ((hg.comp measurable_fst).inv.mul measurable_snd))).mul (hv.comp measurable_snd)
  have hsplit : (∫⁻ y : ℝ, ∫⁻ x, criticalOrbitMajorant α y (ℓ x)*u ((g y)⁻¹*x)*v x ∂μ) =
      (∫⁻ y : ℝ, ∫⁻ x, J d y x ∂μ) + c*(∫⁻ y : ℝ, ∫⁻ x, J k y x ∂μ) := by
    have he (y : ℝ) (x : G) : criticalOrbitMajorant α y (ℓ x)*u ((g y)⁻¹*x)*v x =
        J d y x + c*J k y x := by dsimp [criticalOrbitMajorant,J,d,k,c]; ring
    simp_rw [he]
    exact lintegral_add_scaled μ (J d) (J k) (hm d hd) (hm k hk) c
  have schur (q : ℝ → ℝ → ℝ≥0∞) (hq : Measurable (Function.uncurry q)) {R C : ℝ≥0∞}
      (hr : ∀ t, (∫⁻ y : ℝ, q y t) ≤ R) (hc : ∀ t, (∫⁻ y : ℝ, q y (t+y)) ≤ C) :
      (∫⁻ y : ℝ, ∫⁻ x, J q y x ∂μ) ≤ (C*R)^(1/2:ℝ)*U*V := by
    have h := lintegral_orbit_schur μ g hg ℓ hℓ hshift q hq hr hc hu hv
    rw [hU,hV] at h
    apply h.trans_eq
    simp only [ENNReal.mul_rpow_of_nonneg _ _ (show (0:ℝ) ≤ 1/2 by norm_num)]
    rw [← ENNReal.rpow_two U,← ENNReal.rpow_mul,← ENNReal.rpow_two V,← ENNReal.rpow_mul]
    norm_num
    ring
  rw [hsplit]
  apply (add_le_add (schur d hd hdA hdB) (mul_le_mul' (le_refl c) (schur k hk hkA hkB))).trans_eq
  have hcoeff : (A*A)^(1/2:ℝ) + c*(B*A)^(1/2:ℝ) = ENNReal.ofReal (20/(3*α)) := by
    rw [← sq A,← ENNReal.rpow_two,← ENNReal.rpow_mul]
    norm_num
    have hA : 0 ≤ 2/(3*α) := by positivity
    have hB : 0 ≤ 2/α := by positivity
    have h9 : (9:ℝ)^(3/4:ℝ) = 3*Real.sqrt 3 := by
      rw [show (9:ℝ) = 3^(2:ℝ) by norm_num,← Real.rpow_mul (by norm_num)]
      rw [show (2:ℝ)*(3/4) = 1+1/2 by ring,Real.rpow_add (by norm_num),Real.rpow_one,← Real.sqrt_eq_rpow]
    have hs : Real.sqrt ((2/α)*(2/(3*α))) = 2/(Real.sqrt 3*α) := by
      apply (Real.sqrt_eq_iff_eq_sq (mul_nonneg hB hA) (by positivity)).mpr
      have h₃ := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
      have hn : Real.sqrt 3 ≠ 0 := by positivity
      field_simp
      nlinarith
    dsimp only [A,B,c]
    rw [← ENNReal.ofReal_mul hB,ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hB hA) (by norm_num),
      ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_add hA (by positivity),
      ← Real.sqrt_eq_rpow,hs,h9]
    congr 1
    have h₃ : Real.sqrt 3 ≠ 0 := by positivity
    field_simp
    ring
  rw [← hcoeff]
  ring

end RiemannMasullo
end

section
open Classical Filter MeasureTheory Set
open scoped NNReal ENNReal Topology ComplexConjugate
namespace RiemannMasullo

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]
variable (g : ℝ → G) (ℓ : G → ℝ) (α : ℝ)
local notation "ν" => μ.withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α 3 (ℓ x)))
local notation "W" => Lp ℂ 2 ν
local notation "root(" x ")" => criticalStripRoot α (ℓ (x : G))
local notation "E(" u ", " x ")" => (ENNReal.ofReal (root(x)) * ‖((u : W) x : ℂ)‖ₑ)
local notation "K(" y ", " x ")" => criticalOrbitMajorant α y (ℓ x)

private theorem continuous_orbit_density (α : ℝ) : Continuous (intervalSobolevDensity (-α) α 3) := by
  unfold intervalSobolevDensity
  refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun t ↦ Or.inl ?_)
  positivity

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μ] [μ.IsMulLeftInvariant] in
private theorem normalized_leg_energy (hℓ : Measurable ℓ) (hα : 0 ≤ α) (u : W) :
    (∫⁻ x, E(u,x)^2 ∂μ) = ‖u‖ₑ ^ 2 := by
  have hd : Measurable (fun x : G ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α 3 (ℓ x))) :=
    ((continuous_orbit_density α).measurable.comp hℓ).ennreal_ofReal
  have he := eLpNorm_nnreal_pow_eq_lintegral (p := (2:ℝ≥0)) (by norm_num) (Lp.aestronglyMeasurable u)
  norm_num only [NNReal.coe_ofNat,ENNReal.coe_ofNat,ENNReal.rpow_two] at he
  rw [Lp.eNorm_def, he,lintegral_withDensity_eq_lintegral_mul_non_measurable μ hd
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) _]
  apply lintegral_congr
  intro x
  simp only [mul_pow, Pi.mul_apply, ← ENNReal.ofReal_pow (criticalStripRoot_pos _ _).le, criticalStripRoot_sq hα]

/-- The rank-one pairing at a moving output mask in the original weighted measure. -/
def movingTracePair (m : ℝ → G → ℂ) (u v : W) (y : ℝ) : ℂ :=
  ∫ x : G, conj (v x) * (m y x * u ((g y)⁻¹*x)) ∂ν

omit [μ.IsMulLeftInvariant] in
theorem measurable_movingTracePair (hg : Measurable g)
    {m : ℝ → G → ℂ} (hm : Measurable (Function.uncurry m)) (u v : W) :
    Measurable (movingTracePair μ g ℓ α m u v) := by
  have hm' : Measurable (fun p : ℝ × G ↦ conj (v p.2) * (m p.1 p.2 * u ((g p.1)⁻¹*p.2))) :=
    (Complex.continuous_conj.measurable.comp ((Lp.stronglyMeasurable v).measurable.comp measurable_snd)).mul
      (hm.mul ((Lp.stronglyMeasurable u).measurable.comp ((hg.comp measurable_fst).inv.mul measurable_snd)))
  exact hm'.stronglyMeasurable.integral_prod_right'.measurable

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μ] [μ.IsMulLeftInvariant] in
private theorem movingPair_pointwise (hℓ : Measurable ℓ) (hα : 0 < α)
    (hshift : ∀ y x, ℓ (g y*x) = ℓ x+y)
    {m : ℝ → G → ℂ} (hb : ∀ y x, ‖m y x‖ ≤ 1)
    (hs : ∀ y x, 3*y/4 < ℓ x → m y x = 0) (u v : W) {y : ℝ} (hy : 0 < y) :
    ENNReal.ofReal (Real.exp (-α*y/2))*‖movingTracePair μ g ℓ α m u v y‖ₑ ≤
      ∫⁻ x, K(y,x) * E(u,(g y)⁻¹*x) * E(v,x) ∂μ := by
  let e := ENNReal.ofReal (Real.exp (-α*y/2))
  let F (x : G) := conj (v x) * (m y x * u ((g y)⁻¹*x))
  have hd : Measurable (fun x : G ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α 3 (ℓ x))) :=
    ((continuous_orbit_density α).measurable.comp hℓ).ennreal_ofReal
  apply (mul_le_mul' (le_refl e) (eNorm_integral_le_lintegral_eNorm (μ := ν) F)).trans
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable μ hd (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) _,
    ← lintegral_const_mul' _ _ (show e ≠ ⊤ from ENNReal.ofReal_ne_top)]
  apply lintegral_mono
  intro x
  by_cases ht : ℓ x ≤ 3*y/4
  · have hx : ℓ ((g y)⁻¹*x) = ℓ x-y := by
      have h := hshift y ((g y)⁻¹*x)
      rw [mul_inv_cancel_left] at h
      linarith
    have hroot := ENNReal.ofReal_le_ofReal (criticalStripRoot_lower_ratio (α := α) hy ht)
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_mul (add_nonneg (negativeOrbitKernel_nonneg _ _)
      (mul_nonneg (by positivity) (criticalWindowKernel_nonneg _ _ _))),
      ENNReal.ofReal_add (negativeOrbitKernel_nonneg _ _) (mul_nonneg (by positivity) (criticalWindowKernel_nonneg _ _ _)),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (9:ℝ)^(3/4:ℝ)),← hx] at hroot
    have hm : ‖m y x‖ₑ ≤ 1 := by simpa only [← ofReal_norm,← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hb y x)
    change e * (ENNReal.ofReal (intervalSobolevDensity (-α) α 3 (ℓ x)) * ‖F x‖ₑ) ≤ _
    rw [← criticalStripRoot_sq hα.le, ENNReal.ofReal_pow (criticalStripRoot_pos _ _).le]
    simp only [F, ← ofReal_norm, norm_mul, Complex.norm_conj, ENNReal.ofReal_mul (norm_nonneg _)] at *
    calc
      _ ≤ e * (ENNReal.ofReal (root(x))^2 * (ENNReal.ofReal ‖v x‖ * (1 * ENNReal.ofReal ‖u ((g y)⁻¹*x)‖))) := by gcongr
      _ = (e * ENNReal.ofReal (root(x))) *
        (ENNReal.ofReal (root(x))*ENNReal.ofReal ‖u ((g y)⁻¹*x)‖*ENNReal.ofReal ‖v x‖) := by ring
      _ ≤ _ := (mul_le_mul' hroot (le_refl _)).trans_eq (by unfold criticalOrbitMajorant; ring)
  · simp only [Pi.mul_apply,F,hs y x (lt_of_not_ge ht),zero_mul,mul_zero,eNorm_zero,zero_le]

theorem lintegral_movingTracePair_le (hg : Measurable g) (hℓ : Measurable ℓ) (hα : 0 < α)
    (hshift : ∀ y x, ℓ (g y*x) = ℓ x+y)
    {m : ℝ → G → ℂ} (hb : ∀ y x, ‖m y x‖ ≤ 1)
    (hs : ∀ y x, 3*y/4 < ℓ x → m y x = 0) (u v : W) :
    (∫⁻ y in Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-α*y/2))*‖movingTracePair μ g ℓ α m u v y‖ₑ) ≤
      ENNReal.ofReal (criticalOrbitBound α)*‖u‖ₑ*‖v‖ₑ := by
  have he (u : W) : Measurable (fun x : G ↦ E(u,x)) :=
    (((continuous_criticalStripRoot α).measurable.comp hℓ).ennreal_ofReal).mul (Lp.stronglyMeasurable u).measurable.eNorm
  have h := critical_schur μ g hg ℓ hℓ hshift hα (he u) (he v)
    (normalized_leg_energy μ ℓ α hℓ hα.le u) (normalized_leg_energy μ ℓ α hℓ hα.le v)
  have hle : (∫⁻ y in Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-α*y/2))*‖movingTracePair μ g ℓ α m u v y‖ₑ) ≤
      ∫⁻ y in Ioi (0:ℝ), ∫⁻ x, K(y,x)*E(u,(g y)⁻¹*x)*E(v,x) ∂μ :=
    lintegral_mono_ae ((ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0:ℝ)))).mono fun y hy ↦
      movingPair_pointwise μ g ℓ α hℓ hα hshift hb hs u v (y := y) hy)
  exact hle.trans ((setLIntegral_le_lintegral _ _).trans h)

end RiemannMasullo
end

section
open Classical Filter Function MeasureTheory Set InnerProductSpace
open scoped NNReal ENNReal Topology InnerProductSpace
namespace RiemannMasullo

/-- A single singular expansion of a nuclear operator computes every bounded left
product trace. Its scalar coefficient mass is exactly the trace norm. -/
theorem exists_traceNorm_legs {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) :
    ∃ (c : ℕ → ℝ) (u v : ℕ → H), (∀ n, 0 ≤ c n) ∧ HasSum c (traceNorm T) ∧
      (∀ n, ‖u n‖ ≤ 1 ∧ ‖v n‖ ≤ 1) ∧ ∀ L : H →L[ℂ] H,
      HasSum (fun n ↦ (c n : ℂ)*⟪v n,L (u n)⟫_ℂ)
        (hilbertTrace ⟨L*T.val,mul_mem_nuclearEndomorphisms_left L T⟩) := by
  have htr := (mem_traceClassOperators_iff_isNuclearOperator T.val).mpr T.property
  obtain ⟨d⟩ := (isCompactOperator_iff_nonempty_singularExpansion T.val).mp
    htr.1
  let u (n : ℕ) := if h : d.coeff n ≠ 0 then d.target ⟨n,h⟩ else 0
  let v (n : ℕ) := if h : d.coeff n ≠ 0 then d.source ⟨n,h⟩ else 0
  let c (n : ℕ) : ℝ := d.coeff n
  have hsum : Summable c := by
    change IsCompactOperator T.val ∧ Summable (fun n ↦ approximationNumber T.val n ^ (1:ℝ)) at htr
    simpa only [c,Real.rpow_one,← d.coeff_eq_approximationNumber] using htr.2
  have hmass : ∑' n, c n = traceNorm T := by
    simpa only [schattenNorm, c, Real.rpow_one, div_one,← d.coeff_eq_approximationNumber] using schattenNorm_one_eq_traceNorm T
  have huv (n) : ‖u n‖ ≤ 1 ∧ ‖v n‖ ≤ 1 := by
    by_cases h : d.coeff n ≠ 0
    · simp [u,v,h,d.orthonormal_target.norm_eq_one,d.orthonormal_source.norm_eq_one]
    · simp [u,v,not_ne_iff.mp h]
  have series (x : H) : HasSum (fun n ↦ ((c n : ℂ)*⟪v n,x⟫_ℂ) • u n) (T.val x) := by
    apply (hasSum_subtype_iff_of_support_subset (s := {n | d.coeff n ≠ 0}) ?_).mp
    · exact (d.hasSum_apply x).congr_fun fun n ↦ by simp [c,u,v,n.property]
    · intro n hn
      by_contra h
      exact hn (by simp [c,show d.coeff n = 0 by simpa using h])
  refine ⟨c,u,v,fun n ↦ (d.coeff n).coe_nonneg,hmass ▸ hsum.hasSum,huv,?_⟩
  intro L
  let B := max 1 ‖L‖
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hB' : (B:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB.ne'
  let z (n : ℕ) := (B:ℂ)⁻¹ • L (u n)
  have hz (n) : z n ∈ Metric.closedBall (0:H) 1 := by
    rw [mem_closedBall_zero_iff]
    dsimp only [z]
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hB]
    apply (inv_mul_le_iff₀ hB).mpr
    rw [mul_one]
    exact ((L.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) (huv n).1)).trans (le_max_right _ _)
  let r : NuclearPresentation (L*T.val) := {
    coeff := fun n ↦ ((c n*B : ℝ) : ℂ)
    functional := fun n ↦ innerSL ℂ (v n)
    disc := Metric.closedBall (0:H) 1
    isBanachDisc := isBanachDisc_closedUnitBall
    vector := fun n ↦ ⟨z n, Submodule.subset_span (hz n)⟩
    vector_mem := hz
    summable_coeff := by
      apply (hsum.mul_right B).congr
      intro n
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (d.coeff n).coe_nonneg hB.le)]
    equicontinuous := by
      refine (LipschitzWith.uniformEquicontinuous _ 1 fun n ↦ ?_).equicontinuous 0
      apply (innerSL ℂ (v n)).lipschitzWith.weaken
      rw [← NNReal.coe_le_coe,coe_nnNorm,NNReal.coe_one,innerSL_apply_norm]
      exact (huv n).2
    hasSum := by
      intro x
      apply (L.hasSum (series x)).congr_fun
      intro n
      simp only [z,Complex.ofReal_mul,innerSL_apply_apply,map_smul,smul_smul]
      congr 1
      field_simp }
  let hN := mul_mem_nuclearEndomorphisms_left L T
  have hh := ((exists_nuclearTrace_hasSum hilbert_approximationProperty (L*T.val) hN).exists.choose_spec r).2
  rw [hilbertTrace_eq_nuclearTrace]
  apply hh.congr_fun
  intro n
  symm
  change ((c n*B : ℝ) : ℂ) * ⟪v n,(B:ℂ)⁻¹ • L (u n)⟫_ℂ = _
  rw [Complex.ofReal_mul,inner_smul_right]
  field_simp

end RiemannMasullo
end

section
open Classical Filter MeasureTheory Set
open scoped ENNReal NNReal Topology InnerProductSpace ComplexConjugate
namespace RiemannMasullo
set_option quotPrecheck false

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]
variable (g : ℝ → G) (ℓ : G → ℝ) (α : ℝ)
local notation "ν" => μ.withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α 3 (ℓ x)))
local notation "W" => Lp ℂ 2 ν
local notation "tr(" L ", " T ")" => hilbertTrace (⟨(L : W →L[ℂ] W) * (T : nuclearEndomorphisms W).val,
  mul_mem_nuclearEndomorphisms_left L T⟩ : nuclearEndomorphisms W)

/-- At the critical slope the trace of an actual masked translation of any
nuclear operator belongs to weighted L¹. The bound is uniform over all
jointly measurable output masks supported in the lower three-quarter window. -/
theorem integrable_critical_masked_trace (hg : Measurable g) (hℓ : Measurable ℓ) (hα : 0 < α)
    (hshift : ∀ y x, ℓ (g y*x) = ℓ x+y) (m : ℝ → G → ℂ)
    (hm : Measurable (Function.uncurry m)) (hb : ∀ y x, ‖m y x‖ ≤ 1)
    (hs : ∀ y x, 3*y/4 < ℓ x → m y x = 0) (L : ℝ → W →L[ℂ] W)
    (hL : ∀ y (u : W), (L y u : G → ℂ) =ᵐ[ν] fun x ↦ m y x * u ((g y)⁻¹*x))
    (T : nuclearEndomorphisms W) :
    IntegrableOn (fun y : ℝ ↦ (Real.exp (-α*y/2) : ℂ)*tr(L y,T)) (Ioi 0) ∧
      (∫ y in Ioi (0:ℝ), Real.exp (-α*y/2)*‖tr(L y,T)‖) ≤ criticalOrbitBound α * traceNorm T := by
  obtain ⟨c,u,v,hc,hSum,hunit,htr⟩ := exists_traceNorm_legs T
  let P (n : ℕ) := movingTracePair μ g ℓ α m (u n) (v n)
  let F (y : ℝ) := tr(L y,T)
  let d (y : ℝ) := Real.exp (-α*y/2)
  have hd : Measurable d := by dsimp [d]; fun_prop
  have hP (n) : Measurable (P n) := measurable_movingTracePair μ g ℓ α hg hm _ _
  have hE (n y) : ⟪v n,L y (u n)⟫_ℂ = P n y := by
    rw [L2.inner_def]
    exact integral_congr_ae ((hL y (u n)).mono fun x hx ↦ by dsimp only; rw [RCLike.inner_apply',hx])
  have series (y : ℝ) : HasSum (fun n ↦ (c n : ℂ)*P n y) (F y) := by
    simpa only [hE] using htr (L y)
  have hF : Measurable F := measurable_of_tendsto_metrizable
    (fun n : ℕ ↦ Finset.measurable_fun_sum (Finset.range n) (fun i _ ↦ measurable_const.mul (hP i)))
    (tendsto_pi_nhds.mpr fun y ↦ (series y).tendsto_sum_nat)
  let D := ENNReal.ofReal (criticalOrbitBound α)
  have hleg (n) :
      (∫⁻ y in Ioi (0:ℝ), ENNReal.ofReal (d y)*‖P n y‖ₑ) ≤ D := by
    apply (lintegral_movingTracePair_le μ g ℓ α hg hℓ hα hshift hb hs (u n) (v n)).trans
    have hu : ‖u n‖ₑ ≤ 1 := by simpa only [ofReal_norm,ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hunit n).1
    have hv : ‖v n‖ₑ ≤ 1 := by simpa only [ofReal_norm,ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hunit n).2
    exact (mul_le_mul' (mul_le_mul' (le_refl D) hu) hv).trans_eq (by simp)
  have hbound : (∫⁻ y in Ioi (0:ℝ), ENNReal.ofReal (d y)*‖F y‖ₑ) ≤ D*ENNReal.ofReal (traceNorm T) := by
    calc
      _ ≤ ∫⁻ y in Ioi (0:ℝ), ∑' n, ENNReal.ofReal (c n)*(ENNReal.ofReal (d y)*‖P n y‖ₑ) := by
        apply lintegral_mono
        intro y
        dsimp only
        rw [← (series y).tsum_eq]
        apply (mul_le_mul' le_rfl eNorm_tsum_le_tsum_eNorm).trans
        rw [← ENNReal.tsum_mul_left]
        apply le_of_eq; apply tsum_congr; intro n
        have hn : ‖(c n : ℂ)‖ₑ = ENNReal.ofReal (c n) := by
          rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc n)]
        rw [eNorm_mul,hn]; ring
      _ = ∑' n, ENNReal.ofReal (c n)*(∫⁻ y in Ioi (0:ℝ), ENNReal.ofReal (d y)*‖P n y‖ₑ) := by
        rw [lintegral_tsum (f := fun n y ↦ ENNReal.ofReal (c n)*(ENNReal.ofReal (d y)*‖P n y‖ₑ)) (fun n ↦ (measurable_const.mul (hd.ennreal_ofReal.mul (hP n).eNorm)).aemeasurable)]
        exact tsum_congr fun n ↦ lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ∑' n, ENNReal.ofReal (c n)*D := tsum_le_tsum fun n ↦ mul_le_mul' le_rfl (hleg n)
      _ = _ := by rw [ENNReal.tsum_mul_right,← ENNReal.ofReal_tsum_of_nonneg hc hSum.summable,hSum.tsum_eq,mul_comm]
  have hdF (y : ℝ) : ‖(d y : ℂ)*F y‖ₑ = ENNReal.ofReal (d y)*‖F y‖ₑ := by
    rw [eNorm_mul,← ofReal_norm (d y : ℂ), Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hi : IntegrableOn (fun y : ℝ ↦ (d y : ℂ)*F y) (Ioi 0) := by
    refine ⟨((Complex.measurable_ofReal.comp hd).mul hF).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_eNorm]
    simp only [hdF]
    exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hn (y : ℝ) : ‖(d y : ℂ)*F y‖ = d y*‖F y‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  refine ⟨hi,?_⟩
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hbound
  have hz : 0 ≤ traceNorm T := (tsum_nonneg hc).trans_eq hSum.tsum_eq
  change (∫ y in Ioi (0:ℝ), d y*‖F y‖) ≤ _
  simp_rw [← hn]
  rw [integral_norm_eq_lintegral_eNorm hi.aestronglyMeasurable]
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hz] at hr
  simpa only [hdF,D,ENNReal.toReal_ofReal (criticalOrbitBound_nonneg hα)] using hr

end RiemannMasullo
end
