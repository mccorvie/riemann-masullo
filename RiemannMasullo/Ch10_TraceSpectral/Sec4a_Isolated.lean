module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # The spectral trace statements of §10.4.2 at orders between zero and one -/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

section DirichletWeight

open Real Set

private theorem dirichletWeight_laplace_compare {α s x : ℝ}
    (hα : 0 ≤ α) (hs₁ : s ≤ 1) (hx : 0 ≤ x) :
    let f := fun t : ℝ ↦ t ^ (1 - s) * exp (-2 * x * t)
    let g := fun t : ℝ ↦
      (exp (-2 * x * t) + exp (-2 * x * (2 * α - t))) * t ^ (1 - s)
    (∫ t in (0 : ℝ)..α, f t) ≤ (∫ t in (0 : ℝ)..α, g t) ∧
      (∫ t in (0 : ℝ)..α, g t) ≤ 2 * (∫ t in (0 : ℝ)..α, f t) := by
  intro f g
  have hp : Continuous (fun t : ℝ ↦ t ^ (1 - s)) :=
    continuous_id.rpow_const (fun _ ↦ Or.inr (sub_nonneg.mpr hs₁))
  have he : Continuous (fun t : ℝ ↦ exp (-2 * x * t)) :=
    (continuous_const.mul continuous_id).rexp
  have hf : Continuous f := hp.mul he
  have hg : Continuous g := (he.add
    ((continuous_const.mul (continuous_const.sub continuous_id)).rexp)).mul hp
  have hfI := hf.intervalIntegrable (μ := volume) 0 α
  have hgI := hg.intervalIntegrable (μ := volume) 0 α
  constructor
  · refine intervalIntegral.integral_mono_on hα hfI hgI fun t ht ↦ ?_
    dsimp [f, g]
    rw [mul_comm (t ^ (1 - s))]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (exp_pos _).le) (rpow_nonneg ht.1 _)
  · rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hα hgI (hfI.const_mul 2) fun t ht ↦ ?_
    dsimp [f, g]
    have hE : exp (-2 * x * (2 * α - t)) ≤ exp (-2 * x * t) :=
      exp_le_exp.mpr (by nlinarith [mul_nonneg hx (sub_nonneg.mpr ht.2)])
    let a := exp (-2 * x * t)
    let b := exp (-2 * x * (2 * α - t))
    let p := t ^ (1 - s)
    change (a + b) * p ≤ 2 * (p * a)
    have hp₀ : 0 ≤ p := rpow_nonneg ht.1 _
    have hab : a + b ≤ a + a := add_le_add (le_refl a) hE
    have heq : (a + a) * p = 2 * (p * a) := by ring
    exact (mul_le_mul_of_nonneg_right hab hp₀).trans_eq heq

private theorem dirichletWeight_laplace_scale {α s x : ℝ} (hα : 0 ≤ α) (hx : 0 < x) :
    let f := fun y t : ℝ ↦ t ^ (1 - s) * exp (-2 * y * t)
    x ^ 2 * (∫ t in (0 : ℝ)..α, f x t) = x ^ s * (∫ t in (0 : ℝ)..(x * α), f 1 t) := by
  intro f
  have he : (∫ t in (0 : ℝ)..α, f x t) =
      (x ^ (1 - s))⁻¹ * (∫ t in (0 : ℝ)..α, f 1 (x * t)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hα] at ht
    dsimp [f]
    rw [Real.mul_rpow hx.le ht.1]
    have hp : x ^ (1 - s) ≠ 0 := (rpow_pos_of_pos hx _).ne'
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]
    simp only [mul_one, mul_assoc]
  rw [he, intervalIntegral.integral_comp_mul_left (f 1) hx.ne', mul_zero, smul_eq_mul]
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  rw [← Real.rpow_neg hx.le, ← Real.rpow_neg_one, ← Real.rpow_natCast,
    ← Real.rpow_add hx, ← Real.rpow_add hx]
  congr 1
  push_cast
  ring

private theorem dirichletWeight_nonneg_half
    {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s) (hs₁ : s ≤ 1) :
    ∃ l u : ℝ, 0 < l ∧ 0 < u ∧ ∀ x : ℝ, 0 ≤ x →
      l * (1 + x ^ 2) ^ (s / 2) ≤
        1 + exp (-4 * α * x) + x ^ 2 * (∫ t in (0 : ℝ)..α,
          (exp (-2 * x * t) + exp (-2 * x * (2 * α - t))) * t ^ (1 - s)) ∧
      1 + exp (-4 * α * x) + x ^ 2 * (∫ t in (0 : ℝ)..α,
          (exp (-2 * x * t) + exp (-2 * x * (2 * α - t))) * t ^ (1 - s)) ≤
        u * (1 + x ^ 2) ^ (s / 2) := by
  let f (x t : ℝ) := t ^ (1 - s) * exp (-2 * x * t)
  have hfc (x : ℝ) : Continuous (f x) := by
    exact (continuous_id.rpow_const (fun _ ↦ Or.inr (by linarith))).mul
      ((continuous_const.mul continuous_id).rexp)
  have hf (x b : ℝ) : IntervalIntegrable (f x) volume 0 b :=
    (hfc x).intervalIntegrable _ _
  have hn (x t : ℝ) (ht : 0 ≤ t) : 0 ≤ f x t :=
    mul_nonneg (rpow_nonneg ht _) (exp_pos _).le
  let L := ∫ t in (0 : ℝ)..α, f 1 t
  have hL : 0 < L := by
    refine intervalIntegral.integral_pos hα (hfc 1).continuousOn
      (fun t ht ↦ hn 1 t ht.1.le) ⟨α, ⟨hα.le, le_rfl⟩, ?_⟩
    exact mul_pos (rpow_pos_of_pos hα _) (exp_pos _)
  let U := ∫ t in Ioi (0 : ℝ), f 1 t
  have hU₀ : IntegrableOn (f 1) (Ioi (0 : ℝ)) := by
    simpa only [f, mul_one, rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1 - s) (b := 2)
        (by linarith) (by norm_num) (by norm_num))
  have hcompare (b : ℝ) (hb : 0 ≤ b) : (∫ t in (0 : ℝ)..b, f 1 t) ≤ U := by
    rw [intervalIntegral.integral_of_le hb]
    exact setIntegral_mono_set hU₀
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht ↦ hn 1 t ht.le))
      (Filter.Eventually.of_forall fun _ ht ↦ ht.1)
  have hU : 0 < U := hL.trans_le (hcompare α hα.le)
  have hscale (x : ℝ) (hx : 0 < x) :
      x ^ 2 * (∫ t in (0 : ℝ)..α, f x t) = x ^ s * (∫ t in (0 : ℝ)..(x * α), f 1 t) :=
    dirichletWeight_laplace_scale hα.le hx
  let J (x : ℝ) := ∫ t in (0 : ℝ)..α,
    (exp (-2 * x * t) + exp (-2 * x * (2 * α - t))) * t ^ (1 - s)
  have hJ (x : ℝ) (hx : 0 ≤ x) :
      (∫ t in (0 : ℝ)..α, f x t) ≤ J x ∧ J x ≤ 2 * (∫ t in (0 : ℝ)..α, f x t) :=
    dirichletWeight_laplace_compare hα.le hs₁ hx
  let B := ∫ t in (0 : ℝ)..α, f 0 t
  have hB : 0 ≤ B := intervalIntegral.integral_nonneg hα.le (fun t ht ↦ hn 0 t ht.1)
  refine ⟨min (1 / 2) (L / 2), 2 + 2 * (B + U), lt_min (by norm_num) (by positivity),
    by positivity, fun x hx ↦ ?_⟩
  change _ ≤ 1 + exp (-4 * α * x) + x ^ 2 * J x ∧
    1 + exp (-4 * α * x) + x ^ 2 * J x ≤ _
  have hJ₀ : 0 ≤ J x := (intervalIntegral.integral_nonneg hα.le
    (fun t ht ↦ hn x t ht.1)).trans (hJ x hx).1
  have hExp : exp (-4 * α * x) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have hPow₀ : 1 ≤ (1 + x ^ 2) ^ (s / 2) :=
    one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith)
  by_cases hx₁ : x ≤ 1
  · have hB' : (∫ t in (0 : ℝ)..α, f x t) ≤ B := by
      refine intervalIntegral.integral_mono_on hα.le (hf x α) (hf 0 α) fun t ht ↦ ?_
      dsimp [f]
      apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (rpow_nonneg ht.1 _)
      nlinarith [mul_nonneg hx ht.1]
    have hPow : (1 + x ^ 2) ^ (s / 2) ≤ 2 := calc
      _ ≤ (2 : ℝ) ^ (s / 2) := rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := rpow_one _
    constructor
    · calc
        _ ≤ (1 / 2 : ℝ) * 2 := mul_le_mul (min_le_left ..) hPow (by positivity) (by norm_num)
        _ ≤ _ := by nlinarith [exp_pos (-4 * α * x), mul_nonneg (sq_nonneg x) hJ₀]
    · calc
        _ ≤ 2 + 2 * B := by
          have hterm := mul_le_mul (show x ^ 2 ≤ 1 by nlinarith) ((hJ x hx).2.trans
            (mul_le_mul_of_nonneg_left hB' (by norm_num))) hJ₀ (by norm_num : (0 : ℝ) ≤ 1)
          linarith
        _ ≤ (2 + 2 * (B + U)) * (1 + x ^ 2) ^ (s / 2) := by nlinarith
  · have h₁x : 1 ≤ x := le_of_not_ge hx₁
    have hx' : 0 < x := by linarith
    have hspan : α ≤ x * α := by nlinarith
    have hL' : L ≤ ∫ t in (0 : ℝ)..(x * α), f 1 t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hf 1 α)
        ((hfc 1).intervalIntegrable α (x * α))]
      exact le_add_of_nonneg_right (intervalIntegral.integral_nonneg hspan
        fun t ht ↦ hn 1 t (hα.le.trans ht.1))
    have he : (x ^ 2 : ℝ) ^ (s / 2) = x ^ s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
      congr 1
      push_cast
      ring
    have hPowL : x ^ s ≤ (1 + x ^ 2) ^ (s / 2) := by
      rw [← he]
      exact rpow_le_rpow (by positivity) (by linarith) (by positivity)
    have hPowU : (1 + x ^ 2) ^ (s / 2) ≤ 2 * x ^ s := calc
      _ ≤ (2 * x ^ 2) ^ (s / 2) := rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
      _ ≤ _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg x), he]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa using rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by linarith : s / 2 ≤ 1)
    constructor
    · calc
        _ ≤ (L / 2) * (2 * x ^ s) := mul_le_mul (min_le_right ..) hPowU (by positivity) (by positivity)
        _ = x ^ s * L := by ring
        _ ≤ x ^ 2 * (∫ t in (0 : ℝ)..α, f x t) := by
          rw [hscale x hx']; gcongr
        _ ≤ _ := by
          nlinarith [mul_le_mul_of_nonneg_left (hJ x hx).1 (sq_nonneg x),
            exp_pos (-4 * α * x)]
    · have hj := mul_le_mul_of_nonneg_left (hJ x hx).2 (sq_nonneg x)
      rw [← mul_left_comm, hscale x hx'] at hj
      have hh := mul_le_mul_of_nonneg_left (hcompare (x * α) (by positivity))
        (rpow_nonneg hx s)
      have hu := mul_le_mul_of_nonneg_left hPowL hU.le
      have hb := mul_nonneg hB (rpow_nonneg (by positivity : 0 ≤ 1 + x ^ 2) (s / 2))
      nlinarith

/-- Logarithmic-coordinate density for the sum of the two boundary energies and the
strip Dirichlet energy weighted by `(α - |σ|) ^ (1 - s)`. -/
noncomputable def stripDirichletWeight (α s x : ℝ) : ℝ :=
  exp (2 * α * x) + exp (-2 * α * x) + x ^ 2 *
    (∫ σ in -α..α, exp (2 * σ * x) * (α - |σ|) ^ (1 - s))

private theorem stripDirichletWeight_eq_factor {α s : ℝ} (hα : 0 ≤ α) (hs₁ : s ≤ 1)
    (x : ℝ) : stripDirichletWeight α s x = exp (2 * α * x) *
      (1 + exp (-4 * α * x) + x ^ 2 * (∫ t in (0 : ℝ)..α,
        (exp (-2 * x * t) + exp (-2 * x * (2 * α - t))) * t ^ (1 - s))) := by
  let g (σ : ℝ) := exp (2 * σ * x) * (α - |σ|) ^ (1 - s)
  have hg : Continuous g :=
    ((continuous_const.mul continuous_id).mul continuous_const).rexp.mul
      ((continuous_const.sub continuous_abs).rpow_const (fun _ ↦ Or.inr (by linarith)))
  have ha : (∫ σ in -α..(0 : ℝ), g σ) = ∫ t in (0 : ℝ)..α, g (t - α) := by
    rw [intervalIntegral.integral_comp_sub_right, zero_sub, sub_self]
  have hb : (∫ σ in (0 : ℝ)..α, g σ) = ∫ t in (0 : ℝ)..α, g (α - t) := by
    rw [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]
  have he₁ : exp (2 * α * x) * exp (-4 * α * x) = exp (-2 * α * x) := by
    rw [← exp_add]; congr 1; ring
  have he₂ : (∫ σ in -α..α, g σ) = exp (2 * α * x) *
      (∫ t in (0 : ℝ)..α,
        (exp (-2 * x * t) + exp (-2 * x * (2 * α - t))) * t ^ (1 - s)) := by
    have hleft : IntervalIntegrable (fun t ↦ g (t - α)) volume 0 α :=
      (hg.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
    have hright : IntervalIntegrable (fun t ↦ g (α - t)) volume 0 α :=
      (hg.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable (-α) 0)
      (hg.intervalIntegrable 0 α), ha, hb, ← intervalIntegral.integral_add hleft hright,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hα] at ht
    dsimp [g]
    rw [abs_of_nonpos (sub_nonpos.mpr ht.2), abs_of_nonneg (sub_nonneg.mpr ht.2)]
    simp only [show α - -(t - α) = t by ring, show α - (α - t) = t by ring]
    rw [← add_mul, ← mul_assoc, mul_add, ← exp_add, ← exp_add]
    have h₁ : 2 * α * x + -2 * x * t = 2 * (α - t) * x := by ring
    have h₂ : 2 * α * x + -2 * x * (2 * α - t) = 2 * (t - α) * x := by ring
    rw [h₁, h₂, add_comm]
  change exp _ + exp _ + x ^ 2 * (∫ σ in -α..α, g σ) = _
  rw [he₂, mul_add, mul_add, mul_one, he₁]
  ring

private theorem stripDirichletWeight_neg {α s : ℝ} (x : ℝ) :
    stripDirichletWeight α s (-x) = stripDirichletWeight α s x := by
  let g (σ : ℝ) := exp (2 * σ * x) * (α - |σ|) ^ (1 - s)
  have he : (∫ σ in -α..α, exp (2 * σ * (-x)) * (α - |σ|) ^ (1 - s)) =
      ∫ σ in -α..α, g σ := by
    calc
      _ = ∫ σ in -α..α, g (-σ) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp [g]
        rw [abs_neg]
        congr 2
        ring
      _ = _ := by rw [intervalIntegral.integral_comp_neg g, neg_neg]
  unfold stripDirichletWeight
  rw [he]
  simp [g, mul_neg, add_comm]

/-- The boundary-plus-Dirichlet weight of a positive-width strip is uniformly comparable
to the logarithmic Sobolev weight, including at the two endpoint orders. -/
theorem stripDirichletWeight_comparable {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s) (hs₁ : s ≤ 1) :
    ∃ l u : ℝ, 0 < l ∧ 0 < u ∧ ∀ x : ℝ,
      let w := intervalSobolevDensity (-α) α s x
      l * w ≤ stripDirichletWeight α s x ∧ stripDirichletWeight α s x ≤ u * w := by
  obtain ⟨l, u, hl, hu, h⟩ := dirichletWeight_nonneg_half hα hs hs₁
  have hpos (x : ℝ) (hx : 0 ≤ x) :
      let w := exp (2 * α * x) * (1 + x ^ 2) ^ (s / 2)
      l * w ≤ stripDirichletWeight α s x ∧ stripDirichletWeight α s x ≤ u * w := by
    dsimp only
    rw [stripDirichletWeight_eq_factor hα.le hs₁, mul_left_comm l, mul_left_comm u]
    exact ⟨mul_le_mul_of_nonneg_left (h x hx).1 (exp_pos _).le,
      mul_le_mul_of_nonneg_left (h x hx).2 (exp_pos _).le⟩
  refine ⟨l, u, hl, hu, fun x ↦ ?_⟩
  unfold intervalSobolevDensity
  dsimp only
  by_cases hx : 0 ≤ x
  · rw [max_eq_right (exp_le_exp.mpr (by nlinarith))]
    exact hpos x hx
  · rw [max_eq_left (exp_le_exp.mpr (by nlinarith)), ← stripDirichletWeight_neg x]
    have he : 2 * (-α) * x = 2 * α * (-x) := by ring
    simpa only [he, neg_sq] using hpos (-x) (neg_nonneg.mpr (le_of_not_ge hx))

end DirichletWeight

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSpectralQuotientPolynormableSec3

variable {F : Type*} [Field F] [NumberField F]
variable (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hI" => (neg_nonpos.mpr hα).trans hα
local notation "W" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s
local notation "H₀" => spectralSobolevQuotient F a hI hs
local notation "A(" φ ")" => hardySobolevTestAction μ𝔽 m𝔽 (-α) α s hI hs φ
local notation "Aq(" φ ")" => spectralConvolution (F := F) a hI hs φ
local notation "M(" hc ")" => modulatedCutoffOperator m𝔽
  ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (logIdeleClassNorm F g))) hc
local notation "band(" R ", " ε ")" => (0 < (R : ℝ)⁻¹ + ε ∧ R⁻¹ + ε < R - ε)

variable {Λ ε : ℝ} {ρ : IdeleClassGroup (𝓞 F) F → ℝ}

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). On a strip of width zero
at order at most one, quotient convolution is nuclear.
Deviation: This special case uses the density of theta at the strict endpoint cutoff of §10.2. -/
theorem spectralStripConvolution_nuclear_of_zero_width (hwidth : α = 0) (hs₁ : s ≤ 1)
    (φ : BruhatCompactSupport C𝔽) : IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ)) := by
  subst α
  have line (l : ℝ) (hl : l ≤ 0) (heq : l = 0) :
      IsNuclearOperator (E := spectralSobolevQuotient F a hl hs) (F := spectralSobolevQuotient F a hl hs)
        (spectralConvolution (F := F) a hl hs φ) := by
    subst l
    have hz (q : spectralSobolevQuotient F a hl hs) : q = 0 := by
      obtain ⟨v, rfl⟩ := (globalThetaSobolev F a hl hs).mkQ_surjective q
      apply (spectralSobolevQuotient_eq_zero a hl hs v).2
      rw [globalThetaSobolev_line_eq_top_of_le_one (F := F) a s hs hs₁]
      exact Submodule.mem_top
    have hA : spectralConvolution (F := F) a hl hs φ = 0 :=
      ContinuousLinearMap.ext fun _ ↦ hz _
    rw [hA]
    exact (nuclearEndomorphisms _).zero_mem
  exact line (-0) ((neg_nonpos.mpr hα).trans hα) neg_zero

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). Every compactly supported
Bruhat test acts by a nuclear convolution operator on the strip quotient.
Deviation: The theorems of §10.4.2 print `s ≥ 0`, while p. 455 assumes `s > 1` for
the section. This statement covers `0 ≤ s ≤ 1`.
Gap: The strip theorem 10.3.2.1 requires `s > 1`. At the orders considered here,
`spectralStripConvolution_nuclear_of_zero_width` settles width zero, leaving nuclearity
open for positive width. Nothing in the Lean uses this statement, and it is not known how
it connects with the rest of the proof in Lean; in the paper it is used on pp. 459–461,
463–464, 503, 519–520. -/
theorem spectralStripConvolution_nuclear_of_le_one (_hs₁ : s ≤ 1) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ)) := by
  sorry

/-- Paper: Theorem 10.4.2.1, p. 459. Spectral projection after convolution is nuclear.
This follows from the open statement `spectralStripConvolution_nuclear_of_le_one` by (10.4.2.5).
Deviation: This is the part of the printed range with `0 ≤ s ≤ 1`. The operator is independent
of the cutoff. -/
theorem spectralProjection_convolution_nuclear_of_le_one (_hs₁ : s ≤ 1) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator ((spectralProjection (F := F) a hα hs).comp (A(φ))) :=
  spectralProjection_convolution_nuclear a hα hs φ
    (spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ)

/-- Paper: Theorem 10.4.2.1, p. 459. Spectral projection after convolution is nuclear.
Deviation: This checks the uncut conclusion on the range `1 < s` of the strip theorem. -/
theorem spectralProjection_convolution_nuclear_of_one_lt (hs₁ : 1 < s) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator ((spectralProjection (F := F) a hα hs).comp (A(φ))) :=
  RiemannMasullo.spectralProjection_convolution_nuclear_of_one_lt a hα hs₁ φ

/-- Paper: Theorem 10.4.2.1, p. 459. At each admissible cutoff, spectral truncation
after convolution is nuclear. This follows from the open `spectralStripConvolution_nuclear_of_le_one`
by composing the projected convolution with cutoff multiplication.
Deviation: The range here is `0 ≤ s ≤ 1`. The real cutoff uses the profile of Definition 9.3.3.1. -/
theorem spectralTruncatedConvolution_nuclear_of_le_one (_hs₁ : s ≤ 1)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (_hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (spectralTruncatedConvolution a hα hs hρ φ) :=
  spectralTruncatedConvolution_nuclear a hα hs hρ φ
    (spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ)

/-- Paper: Theorem 10.4.2.1, p. 459. Spectral truncation after convolution is nuclear.
Deviation: At `1 < s` the existing theorem applies to real cutoffs even without the inner-band inequality. -/
theorem spectralTruncatedConvolution_nuclear_of_one_lt (hs₁ : 1 < s)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (spectralTruncatedConvolution a hα hs hρ φ) :=
  RiemannMasullo.spectralTruncatedConvolution_nuclear_of_one_lt a hα hs₁ hρ φ

/-- Paper: Theorem 10.4.2.1, p. 459. At each admissible cutoff, geometric truncation
after convolution is nuclear. Given the open `spectralStripConvolution_nuclear_of_le_one`,
this follows by subtracting the spectral summand from cutoff convolution.
Deviation: The range here is `0 ≤ s ≤ 1`, with the real cutoff of Definition 9.3.3.1. -/
theorem geometricTruncatedConvolution_nuclear_of_le_one (_hs₁ : s ≤ 1)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (geometricTruncatedConvolution a hα hs hρ φ) :=
  geometricTruncatedConvolution_nuclear a hα hs hρ hband φ
    (spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ)

/-- Paper: Theorem 10.4.2.1, p. 459. Geometric truncation after convolution is nuclear.
Deviation: This checks the real-cutoff conclusion at `1 < s` using the strip theorem. -/
theorem geometricTruncatedConvolution_nuclear_of_one_lt (hs₁ : 1 < s)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (geometricTruncatedConvolution a hα hs hρ φ) :=
  RiemannMasullo.geometricTruncatedConvolution_nuclear_of_one_lt a hα hs₁ hρ hband φ

local notation "traceSplit(" hρ ", " φ ")" =>
  (let T := (M(hρ)).comp (A(φ))
   let G := geometricTruncatedConvolution a hα hs hρ φ
   let S := spectralTruncatedConvolution a hα hs hρ φ
   ∃ (hT : IsNuclearOperator T) (hG : IsNuclearOperator G) (hS : IsNuclearOperator S),
     hilbertTrace (H := W) ⟨T, hT⟩ =
       hilbertTrace (H := W) ⟨G, hG⟩ + hilbertTrace (H := W) ⟨S, hS⟩)

/-- Paper: Theorem 10.4.2.1, p. 459. At an admissible cutoff the trace of cutoff convolution
is the sum of the geometric and spectral traces, as in (10.4.2.3). The open statement
`spectralStripConvolution_nuclear_of_le_one` supplies the hypothesis for the trace split.
Deviation: The order is restricted to `0 ≤ s ≤ 1` and the three nuclearity witnesses are
part of the conclusion for the real cutoff. -/
theorem truncatedConvolution_trace_split_of_le_one (_hs₁ : s ≤ 1)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    traceSplit(hρ, φ) :=
  truncatedConvolution_trace_split a hα hs hρ hband φ
    (spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ)

/-- Paper: Theorem 10.4.2.1, p. 459. The nuclear trace splits as in (10.4.2.3).
Deviation: This checks the identity with real cutoffs and all three nuclearity witnesses at `1 < s`. -/
theorem truncatedConvolution_trace_split_of_one_lt (hs₁ : 1 < s)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    traceSplit(hρ, φ) :=
  RiemannMasullo.truncatedConvolution_trace_split_of_one_lt a hα hs₁ hρ hband φ

section Limits

variable (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)) (ε : ℝ → ℝ)
  (ρ : ℝ → IdeleClassGroup (𝓞 F) F → ℝ)

local notation "traceLimit(" op ")" =>
  (∃ (hq : IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ))) (t : ℝ → ℂ),
    (∀ᶠ R in atTop, ∃ hc : IsModulatedCutoff m𝔽 R (ε R) (ρ R),
      let T := (op) a hα hs hc φ
      ∃ hT : IsNuclearOperator T, t R = hilbertTrace (H := W) ⟨T, hT⟩) ∧
    Tendsto t atTop (𝓝 (hilbertTrace (H := H₀) ⟨Aq(φ), hq⟩)))

variable (hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
  (hρ : ∀ᶠ R in atTop, IsModulatedCutoff (continuousIdeleClassNorm F) R (ε R) (ρ R) ∧ band(R, ε R))

include hε hρ

/-- Paper: Theorem 10.4.2.2, p. 460. The traces of cutoff projection after convolution tend
to the trace of convolution on the strip quotient, as in (10.4.2.9). This follows from
the open statement `spectralStripConvolution_nuclear_of_le_one`.
Deviation: At `0 ≤ s ≤ 1` this asserts quotient nuclearity along with the limit. The proof
on p. 461 uses the strip quotient. Real cutoffs and their traces need only agree with the
prescribed data eventually as the radius tends to infinity. -/
theorem spectralTruncatedConvolution_trace_tendsto_of_le_one (_hs₁ : s ≤ 1) :
    traceLimit(spectralTruncatedConvolution) := by
  have hq := spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ
  exact ⟨hq, spectralTruncatedConvolution_trace_tendsto a hα hs φ hq ε ρ hε hρ⟩

/-- Paper: Theorem 10.4.2.2, p. 460. The projection-after-convolution traces tend to the strip quotient trace.
Deviation: This checks the eventual real-cutoff formulation at `1 < s` with the nuclearity witness from §10.3. -/
theorem spectralTruncatedConvolution_trace_tendsto_of_one_lt (hs₁ : 1 < s) :
    traceLimit(spectralTruncatedConvolution) :=
  ⟨spectralStripConvolution_nuclear a hα hs₁ φ,
    RiemannMasullo.spectralTruncatedConvolution_trace_tendsto_of_one_lt a hα hs₁ φ ε ρ hε hρ⟩

/-- Paper: Theorem 10.4.2.8, p. 463. The traces of cutoff convolution after spectral
projection tend to the strip quotient trace, as in (10.4.2.20). This follows from the
open statement `spectralStripConvolution_nuclear_of_le_one`.
Deviation: At `0 ≤ s ≤ 1` this asserts quotient nuclearity along with the limit. The real
cutoff conditions and agreement with the nuclear traces are eventual. -/
theorem spectralRestriction_trace_tendsto_of_le_one (_hs₁ : s ≤ 1) :
    traceLimit(spectralRestriction) := by
  have hq := spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ
  exact ⟨hq, spectralRestriction_trace_tendsto a hα hs φ hq ε ρ hε hρ⟩

/-- Paper: Theorem 10.4.2.8, p. 463. The convolution-after-projection traces tend to the strip quotient trace.
Deviation: This checks the eventual real-cutoff formulation at `1 < s` with the nuclearity witness from §10.3. -/
theorem spectralRestriction_trace_tendsto_of_one_lt (hs₁ : 1 < s) :
    traceLimit(spectralRestriction) :=
  ⟨spectralStripConvolution_nuclear a hα hs₁ φ,
    RiemannMasullo.spectralRestriction_trace_tendsto_of_one_lt a hα hs₁ φ ε ρ hε hρ⟩

end Limits

end RiemannMasullo.Isolated
