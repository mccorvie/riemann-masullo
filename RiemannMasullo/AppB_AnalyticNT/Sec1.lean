module

public import RiemannMasullo.Ch03_IdelicZeta.Sec2
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Topology.Order.Lattice

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Convex.Continuous
import Mathlib.NumberTheory.LSeries.Injectivity
import RiemannMasullo.ForMathlib.Analysis.Complex.Hadamard
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.HeckeLFunction

/-!
# Convexity bounds for finite Hecke L-functions

Masullo, §B.1, pp. 588–591. The estimates concern both directions on vertical
lines and are uniform in the real part when stated on a strip.
-/

@[expose] public noncomputable section

open Filter Function NumberField Set
open scoped Asymptotics ENNReal NNReal Topology

namespace RiemannMasullo

local notation "atHeight" => comap (abs ∘ Complex.im) atTop

-- TODO(paper-gap): If the introductory critical-line estimate refers to the
-- finite L-function, its exponent 1/4 + ε omits the degree in (B.1.1.12).

/-- Paper: Equation (B.1.1.2), p. 589. The vertical growth order is the infimum
of the nonnegative exponents that bound the function along `Re(s) = σ`.
Deviation: The infimum takes values in `ℝ≥0∞`, with `⊤` when no polynomial bound exists. -/
def verticalGrowthOrder (f : ℂ → ℂ) (σ : ℝ) : ℝ≥0∞ :=
  sInf ((fun k : ℝ≥0 ↦ (k : ℝ≥0∞)) ''
    {k : ℝ≥0 | f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ (k : ℝ)})

/-- Paper: Equation (B.1.1.2), p. 589. As a check on the definition, the identity
function has growth order one on every vertical line. -/
theorem verticalGrowthOrder_id (σ : ℝ) : verticalGrowthOrder (id : ℂ → ℂ) σ = 1 := by
  let l := atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})
  have hHeight : Tendsto (fun z : ℂ ↦ |z.im|) l atTop := tendsto_inf_left tendsto_comap
  unfold verticalGrowthOrder
  apply le_antisymm
  · refine sInf_le ⟨1, ?_, by simp⟩
    change (id : ℂ → ℂ) =O[l] fun z ↦ |z.im| ^ ((1 : ℝ≥0) : ℝ)
    have hRe : ∀ᶠ z in l, z.re = σ :=
      eventually_inf_principal.mpr (Eventually.of_forall fun _ hz ↦ hz)
    refine Asymptotics.isBigO_iff.mpr ⟨2, ?_⟩
    filter_upwards [hRe, hHeight.eventually_ge_atTop |σ|] with z hre hσz
    simp only [id_eq, NNReal.coe_one, Real.rpow_one, Real.norm_of_nonneg (abs_nonneg _)]
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 2 * |z.im| := by
        rw [hre, two_mul]
        exact add_le_add_left hσz _
  · apply le_sInf
    rintro _ ⟨k, hk, rfl⟩
    by_contra! hlt
    have hklt : (k : ℝ) < 1 := by exact_mod_cast hlt
    have hRay : Tendsto (fun t : ℝ ↦ (⟨σ, t⟩ : ℂ)) atTop l := by
      refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr (by simp)⟩
      exact tendsto_id.congr' <| (eventually_ge_atTop (0 : ℝ)).mono fun t ht ↦
        (abs_of_nonneg ht).symm
    have : NeBot l := hRay.neBot
    change (id : ℂ → ℂ) =O[l] fun z ↦ |z.im| ^ (k : ℝ) at hk
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hk
    have hLarge : ∀ᶠ z in l, C < |z.im| ^ (1 - (k : ℝ)) :=
      ((tendsto_rpow_atTop (sub_pos.mpr hklt)).comp hHeight).eventually_gt_atTop C
    obtain ⟨z, hz, hlarge, hbound⟩ := ((hHeight.eventually_gt_atTop 0).and (hLarge.and hC)).exists
    rw [Real.rpow_sub hz, Real.rpow_one] at hlarge
    rw [id_eq, Real.norm_of_nonneg (Real.rpow_nonneg hz.le _)] at hbound
    exact (not_lt_of_ge ((Complex.abs_im_le_norm z).trans hbound))
      ((lt_div_iff₀ (Real.rpow_pos_of_pos hz _)).mp hlarge)

variable {f : ℂ → ℂ}

/-- Raising the height to a larger real power only enlarges the vertical majorant. -/
lemma isBigO_im_rpow_of_le {p q : ℝ} (hpq : p ≤ q) :
    (fun s : ℂ ↦ |s.im| ^ p) =O[atHeight] fun s : ℂ ↦ |s.im| ^ q := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [tendsto_comap.eventually_ge_atTop (1 : ℝ)] with s hs
  have hp : 0 ≤ |s.im| ^ p := Real.rpow_nonneg (abs_nonneg _) _
  have hq : 0 ≤ |s.im| ^ q := Real.rpow_nonneg (abs_nonneg _) _
  simpa [Real.norm_of_nonneg hp, Real.norm_of_nonneg hq] using
    Real.rpow_le_rpow_of_exponent_le hs hpq

/-- A vertical big-O bound places the growth order at most at that exponent. -/
lemma verticalGrowthOrder_toReal_le_of_isBigO {f : ℂ → ℂ} {σ r : ℝ} (hr : 0 ≤ r)
    (hO : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ r) :
    (verticalGrowthOrder f σ).toReal ≤ r := by
  let k : ℝ≥0 := ⟨r, hr⟩
  have hk : k ∈ {k : ℝ≥0 | f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ (k : ℝ)} :=
    hO
  have hle : verticalGrowthOrder f σ ≤ k := by
    unfold verticalGrowthOrder
    exact sInf_le (mem_image_of_mem _ hk)
  exact ENNReal.toReal_le_coe_of_le_coe hle

/-- A vertical big-O bound keeps the growth order finite. -/
lemma verticalGrowthOrder_ne_top_of_isBigO {f : ℂ → ℂ} {σ r : ℝ} (hr : 0 ≤ r)
    (hO : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ r) :
    verticalGrowthOrder f σ ≠ ⊤ := by
  let k : ℝ≥0 := ⟨r, hr⟩
  have hk : k ∈ {k : ℝ≥0 | f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ (k : ℝ)} :=
    hO
  refine ne_top_of_le_ne_top (b := (k : ℝ≥0∞)) (by simp) ?_
  unfold verticalGrowthOrder
  exact sInf_le (mem_image_of_mem _ hk)

/-- An exponent strictly above the growth order is admissible. -/
lemma isBigO_of_verticalGrowthOrder_toReal_lt {f : ℂ → ℂ} {σ r : ℝ}
    (hne : verticalGrowthOrder f σ ≠ ⊤) (hr : (verticalGrowthOrder f σ).toReal < r) :
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ r := by
  have hr0 : 0 < r := lt_of_le_of_lt ENNReal.toReal_nonneg hr
  have hlt : verticalGrowthOrder f σ < ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_toReal hne]
    exact (ENNReal.ofReal_lt_ofReal_iff hr0).2 hr
  rw [verticalGrowthOrder] at hlt
  obtain ⟨x, hx, hxlt⟩ := (sInf_lt_iff).1 hlt
  obtain ⟨k, hk, rfl⟩ := hx
  have hklt : (k : ℝ) < r := by
    have hxlt' : (k : ℝ≥0∞) < ENNReal.ofReal r := hxlt
    rw [ENNReal.coe_nnreal_eq] at hxlt'
    exact (ENNReal.ofReal_lt_ofReal_iff hr0).1 hxlt'
  exact hk.trans ((isBigO_im_rpow_of_le hklt.le).mono inf_le_left)

open Complex in
/-- Modulus of the affine-logarithmic weight used to interpolate vertical exponents. -/
lemma norm_affineLogWeight {p q eps : ℝ} {z0 s : ℂ} (hs : 0 < (s - z0).re) :
    ‖exp (((↑p + ↑q * s) * log (s - z0)) + ((↑(-eps * q * Real.pi / 2) * I) * s))‖ =
      ‖s - z0‖ ^ (p + q * s.re) *
        Real.exp (q * s.im * (eps * Real.pi / 2 - (s - z0).arg)) := by
  have hpos : 0 < ‖s - z0‖ := lt_of_lt_of_le hs ((le_abs_self _).trans (abs_re_le_norm _))
  rw [norm_exp]
  set μ : ℂ := ↑(-eps * q * Real.pi / 2) * I
  have hμre : μ.re = 0 := by simp [μ]
  have hμim : μ.im = -eps * q * Real.pi / 2 := by simp [μ]
  have hαre : (↑p + ↑q * s).re = p + q * s.re := by simp
  have hαim : (↑p + ↑q * s).im = q * s.im := by simp
  have hre :
      (((↑p + ↑q * s) * log (s - z0)) + μ * s).re =
        (p + q * s.re) * Real.log ‖s - z0‖ +
          q * s.im * (eps * Real.pi / 2 - (s - z0).arg) := by
    rw [add_re, mul_re, mul_re, log_re, log_im, hμre, hμim, hαre, hαim]
    ring
  rw [hre, Real.exp_add, mul_comm (p + q * s.re), ← Real.rpow_def_of_pos hpos]

/-- On the closed right half of a vertical line, `t · (ε π/2 - arg)` stays between `0` and the
real part. `\u03b5 = 1` is the upper half-plane and `\u03b5 = -1` the lower one. -/
lemma im_mul_halfArg_bounds {z : ℂ} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hx : 0 < z.re)
    (hy : 0 ≤ ε * z.im) :
    0 ≤ z.im * (ε * Real.pi / 2 - z.arg) ∧
      z.im * (ε * Real.pi / 2 - z.arg) ≤ z.re := by
  rcases hε with rfl | rfl
  · simp only [one_mul] at hy ⊢
    have him : 0 ≤ z.im := hy
    have harg_lt : z.arg < Real.pi / 2 := Complex.arg_lt_pi_div_two_iff.2 (Or.inl hx)
    refine ⟨mul_nonneg him (sub_nonneg.2 harg_lt.le), ?_⟩
    rcases him.eq_or_lt with him0 | him0
    · have him0' : z.im = 0 := him0.symm
      simp [him0', Complex.arg_eq_zero_iff.2 ⟨hx.le, him0'⟩, hx.le]
    · have harg_pos : 0 < z.arg := by
        refine lt_of_le_of_ne (Complex.arg_nonneg_iff.2 him) ?_
        intro hzero
        exact him0.ne' ((Complex.arg_eq_zero_iff.1 hzero.symm).2)
      have hpos : 0 < Real.pi / 2 - z.arg := sub_pos.2 harg_lt
      have hlt : Real.pi / 2 - z.arg < Real.pi / 2 := sub_lt_self _ harg_pos
      have htan : Real.tan (Real.pi / 2 - z.arg) = z.re / z.im := by
        rw [Real.tan_pi_div_two_sub, Complex.tan_arg, inv_div]
      have hle : Real.pi / 2 - z.arg ≤ z.re / z.im := by
        rw [← htan]
        exact Real.le_tan hpos.le hlt
      have : (Real.pi / 2 - z.arg) * z.im ≤ z.re := (le_div_iff₀ him0).1 hle
      simpa [mul_comm] using this
  · simp only [neg_one_mul] at hy ⊢
    have him : z.im ≤ 0 := by linarith
    rcases him.eq_or_lt with him0 | him0
    · have harg : z.arg = 0 := Complex.arg_eq_zero_iff.2 ⟨hx.le, him0⟩
      simp [him0, harg, hx.le]
    · have harg_gt : -(Real.pi / 2) < z.arg :=
        Complex.neg_pi_div_two_lt_arg_iff.2 (Or.inl hx)
      have harg_neg : z.arg < 0 := Complex.arg_neg_iff.2 him0
      have hφpos : 0 < Real.pi / 2 + z.arg := by linarith
      have hφlt : Real.pi / 2 + z.arg < Real.pi / 2 := by linarith
      have htan : Real.tan (Real.pi / 2 + z.arg) = z.re / -z.im := by
        rw [show Real.pi / 2 + z.arg = Real.pi / 2 - (-z.arg) by ring,
          Real.tan_pi_div_two_sub, Real.tan_neg, Complex.tan_arg]
        field_simp [hx.ne', him0.ne]
      have hle : Real.pi / 2 + z.arg ≤ z.re / -z.im := by
        rw [← htan]
        exact Real.le_tan hφpos.le hφlt
      have himabs : 0 < -z.im := neg_pos.2 him0
      have hmul : (Real.pi / 2 + z.arg) * -z.im ≤ z.re := (le_div_iff₀ himabs).1 hle
      constructor
      · rw [show z.im * (-Real.pi / 2 - z.arg) = -z.im * (Real.pi / 2 + z.arg) by ring]
        exact mul_nonneg himabs.le hφpos.le
      · rw [show z.im * (-Real.pi / 2 - z.arg) = (Real.pi / 2 + z.arg) * -z.im by ring]
        exact hmul

open Complex in
/-- Over a compact set of real parts, a vertical power bound for large heights and continuity
give a global bound by the same power of the distance to a real point on the left. -/
lemma exists_norm_le_mul_norm_sub_rpow {F : ℂ → ℂ} {K : Set ℝ} (hK : IsCompact K)
    (hc : ContinuousOn F (re ⁻¹' K)) {A : ℝ} (hA : 0 ≤ A)
    (hO : F =O[atHeight ⊓ 𝓟 (re ⁻¹' K)] fun s ↦ |s.im| ^ A) {x0 : ℝ}
    (hx0 : ∀ σ ∈ K, x0 + 1 ≤ σ) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ K → ‖F s‖ ≤ C * ‖s - x0‖ ^ A := by
  obtain ⟨c, hc'⟩ := Asymptotics.isBigO_iff.mp hO
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at hc'
  obtain ⟨T, hT⟩ := hc'
  obtain ⟨M, hM⟩ := (hK.reProdIm (isCompact_Icc (a := -T) (b := T))).exists_bound_of_continuousOn
    (hc.mono fun s hs ↦ hs.1)
  refine ⟨max c 0 + max M 0, by positivity, fun s hs ↦ ?_⟩
  have h1 : 1 ≤ ‖s - x0‖ := by
    have := hx0 _ hs
    calc (1:ℝ) ≤ (s - x0).re := by simp; linarith
      _ ≤ |(s - x0).re| := le_abs_self _
      _ ≤ ‖s - x0‖ := abs_re_le_norm _
  have hpow : 1 ≤ ‖s - x0‖ ^ A := Real.one_le_rpow h1 hA
  by_cases hs' : T ≤ |s.im|
  · have hb := hT _ hs' s rfl hs
    have him : |s.im| ≤ ‖s - x0‖ := by
      have := abs_im_le_norm (s - x0); simpa using this
    calc ‖F s‖ ≤ c * ‖|s.im| ^ A‖ := hb
      _ ≤ max c 0 * |s.im| ^ A := by
        rw [Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max c 0 * ‖s - x0‖ ^ A := by
        gcongr
      _ ≤ (max c 0 + max M 0) * ‖s - x0‖ ^ A := by
        gcongr; exact le_add_of_nonneg_right (le_max_right _ _)
  · replace hs' := not_le.mp hs'
    have hmem : s ∈ K ×ℂ Icc (-T) T := ⟨hs, abs_le.mp hs'.le⟩
    calc ‖F s‖ ≤ M := hM s hmem
      _ ≤ max c 0 + max M 0 := by linarith [le_max_left M 0, le_max_right c 0]
      _ ≤ (max c 0 + max M 0) * ‖s - x0‖ ^ A := le_mul_of_one_le_right (by positivity) hpow

/-- On the right half-plane, `t · (ε π / 2 - arg)` never exceeds the real part. -/
lemma im_mul_halfArg_le_re {z : ℂ} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hx : 0 < z.re) :
    z.im * (ε * Real.pi / 2 - z.arg) ≤ z.re := by
  by_cases hy : 0 ≤ ε * z.im
  · exact (im_mul_halfArg_bounds hε hx hy).2
  · replace hy := not_le.mp hy
    refine le_trans ?_ hx.le
    rcases hε with rfl | rfl
    · have him : z.im < 0 := by linarith
      have harg : z.arg < 0 := Complex.arg_neg_iff.2 him
      have := mul_nonneg (neg_nonneg.2 him.le) (by linarith [Real.pi_pos] :
        (0:ℝ) ≤ 1 * Real.pi / 2 - z.arg)
      linarith
    · have him : 0 < z.im := by linarith
      have harg : 0 ≤ z.arg := Complex.arg_nonneg_iff.2 him.le
      have := mul_nonneg him.le (by linarith [Real.pi_pos] :
        (0:ℝ) ≤ -(-1 * Real.pi / 2 - z.arg))
      linarith

/-- A positive power is dominated by the exponential of the same multiple. -/
lemma rpow_le_exp_mul {y r : ℝ} (hy : 0 < y) (hr : 0 ≤ r) : y ^ r ≤ Real.exp (r * y) := by
  rw [Real.rpow_def_of_pos hy, mul_comm r y]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Real.log_le_self hy.le) hr)

open Complex in
/-- Phragmén–Lindelöf interpolation of polynomial vertical bounds when the exponent on the right
edge is at most the one on the left edge. -/
lemma isBigO_rpow_of_verticalStrip_of_le {σ₁ σ₂ : ℝ} (h₁₂ : σ₁ < σ₂) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (re ⁻¹' Icc σ₁ σ₂)) {ξ : ℝ}
    (hpoly : F =O[atHeight ⊓ 𝓟 (re ⁻¹' Icc σ₁ σ₂)] fun s ↦ |s.im| ^ ξ)
    {A B : ℝ} (hB0 : 0 ≤ B) (hBA : B ≤ A)
    (hA : F =O[atHeight ⊓ 𝓟 (re ⁻¹' {σ₁})] fun s ↦ |s.im| ^ A)
    (hB : F =O[atHeight ⊓ 𝓟 (re ⁻¹' {σ₂})] fun s ↦ |s.im| ^ B)
    {σ : ℝ} (hσ : σ ∈ Icc σ₁ σ₂) :
    F =O[atHeight ⊓ 𝓟 (re ⁻¹' {σ})]
      fun s ↦ |s.im| ^ (((σ₂ - σ) * A + (σ - σ₁) * B) / (σ₂ - σ₁)) := by
  have hA0 : 0 ≤ A := hB0.trans hBA
  have hw : 0 < σ₂ - σ₁ := sub_pos.mpr h₁₂
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (B - A) / (σ₂ - σ₁) := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = A - q * σ₁ := ⟨_, rfl⟩
  have hq0 : q ≤ 0 := hq ▸ div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le
  have hℓ : ∀ x : ℝ, p + q * x = ((σ₂ - x) * A + (x - σ₁) * B) / (σ₂ - σ₁) := by
    intro x
    rw [hp, hq]
    field_simp
    ring
  have hℓ₁ : p + q * σ₁ = A := by rw [hℓ]; field_simp; ring
  have hℓ₂ : p + q * σ₂ = B := by rw [hℓ]; field_simp; ring
  have hℓ0 : ∀ x ∈ Icc σ₁ σ₂, 0 ≤ p + q * x := by
    intro x hx
    rw [hℓ]
    apply div_nonneg _ hw.le
    have := mul_nonneg (sub_nonneg.2 hx.2) hA0
    have := mul_nonneg (sub_nonneg.2 hx.1) hB0
    linarith
  obtain ⟨x0, hx0⟩ : ∃ x0 : ℝ, x0 = σ₁ - 1 := ⟨_, rfl⟩
  have hFc : ContinuousOn F (re ⁻¹' Icc σ₁ σ₂) := hF.continuousOn
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_le_mul_norm_sub_rpow (K := {σ₁}) isCompact_singleton
    (hFc.mono (preimage_mono (by simp [h₁₂.le]))) hA0 hA (x0 := x0)
    (by intro y hy; rw [mem_singleton_iff.mp hy]; linarith)
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_norm_le_mul_norm_sub_rpow (K := {σ₂}) isCompact_singleton
    (hFc.mono (preimage_mono (by simp [h₁₂.le]))) hB0 hB (x0 := x0)
    (by intro y hy; rw [mem_singleton_iff.mp hy]; linarith)
  have hpoly' : F =O[atHeight ⊓ 𝓟 (re ⁻¹' Icc σ₁ σ₂)] fun s ↦ |s.im| ^ (max ξ 0) :=
    hpoly.trans ((isBigO_im_rpow_of_le (le_max_left ξ 0)).mono inf_le_left)
  obtain ⟨Cξ, hCξ0, hCξ⟩ := exists_norm_le_mul_norm_sub_rpow isCompact_Icc hFc
    (le_max_right ξ 0) hpoly' (x0 := x0) (by intro y hy; linarith [hy.1])
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = σ₂ - x0 := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by rw [hR, hx0]; linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (-q * R) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = E * max C₁ C₂ := ⟨_, rfl⟩
  have hE0 : 0 < E := hE ▸ Real.exp_pos _
  set z0 : ℂ := (x0 : ℂ) with hz0
  -- basic facts about `s - z0` on the strip
  have hre : ∀ s : ℂ, (s - z0).re = s.re - x0 := by intro s; simp [z0]
  have him : ∀ s : ℂ, (s - z0).im = s.im := by intro s; simp [z0]
  have hnorm1 : ∀ s : ℂ, σ₁ ≤ s.re → 1 ≤ ‖s - z0‖ := by
    intro s hs
    calc (1:ℝ) ≤ (s - z0).re := by rw [hre, hx0]; linarith
      _ ≤ |(s - z0).re| := le_abs_self _
      _ ≤ ‖s - z0‖ := abs_re_le_norm _
  have hnormle : ∀ s : ℂ, σ₁ ≤ s.re → ‖s - z0‖ ≤ (s.re - x0) + |s.im| := by
    intro s hs
    have := norm_le_abs_re_add_abs_im (s - z0)
    rwa [hre, him, abs_of_nonneg (by rw [hx0]; linarith)] at this
  have hD0 : 0 ≤ D := by rw [hD]; exact mul_nonneg hE0.le (hC₁0.trans (le_max_left _ _))
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = Real.pi / (σ₂ - σ₁) / 2 := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hc_def]; positivity
  have hc_lt : c < Real.pi / (σ₂ - σ₁) := hc_def ▸ half_lt_self (by positivity)
  have key : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ s : ℂ, s.re ∈ Icc σ₁ σ₂ → 0 ≤ ε * s.im →
      ‖F s‖ ≤ D * ‖s - z0‖ ^ (p + q * s.re) := by
    intro ε hε
    set W : ℂ → ℂ := fun s ↦ exp (((↑(-p) + ↑(-q) * s) * log (s - z0)) +
      ((↑(-ε * -q * Real.pi / 2) * I) * s)) with hW
    have hWnorm : ∀ s : ℂ, σ₁ ≤ s.re → ‖W s‖ = (‖s - z0‖ ^ (p + q * s.re))⁻¹ *
        Real.exp (-q * (s - z0).im * (ε * Real.pi / 2 - (s - z0).arg)) := by
      intro s hs
      have hpos : 0 < (s - z0).re := by rw [hre, hx0]; linarith
      rw [hW, norm_affineLogWeight hpos, him, ← Real.rpow_neg (norm_nonneg _)]
      congr 2; ring
    have hWup : ∀ s : ℂ, s.re ∈ Icc σ₁ σ₂ → ‖W s‖ ≤ (‖s - z0‖ ^ (p + q * s.re))⁻¹ * E := by
      intro s hs
      have hpos : 0 < (s - z0).re := by rw [hre, hx0]; linarith [hs.1]
      rw [hWnorm s hs.1]
      have hX := im_mul_halfArg_le_re hε hpos
      have hle : -q * (s - z0).im * (ε * Real.pi / 2 - (s - z0).arg) ≤ -q * R := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        rw [hre] at hX
        linarith [hs.2]
      rw [hE]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (by positivity)
    have hWd : DifferentiableOn ℂ W (re ⁻¹' Icc σ₁ σ₂) := by
      intro s hs
      have hslit : s - z0 ∈ slitPlane :=
        mem_slitPlane_iff.2 (Or.inl (by rw [hre, hx0]; linarith [(show σ₁ ≤ s.re from hs.1)]))
      refine DifferentiableAt.differentiableWithinAt ?_
      exact ((((differentiableAt_const _).add ((differentiableAt_const _).mul
        differentiableAt_id)).mul ((differentiableAt_id.sub_const _).clog hslit)).add
        ((differentiableAt_const _).mul differentiableAt_id)).cexp
    have hGd : DiffContOnCl ℂ (fun s ↦ W s * F s) (re ⁻¹' Ioo σ₁ σ₂) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_preimage_re, closure_Ioo h₁₂.ne]
      exact hWd.mul hF
    have hGgrowth : (fun s ↦ W s * F s) =O[atHeight ⊓ 𝓟 (re ⁻¹' Ioo σ₁ σ₂)]
        fun s ↦ Real.exp (max ξ 0 / c * Real.exp (c * |s.im|)) := by
      refine Asymptotics.IsBigO.of_bound (E * Cξ * Real.exp (max ξ 0 * R)) ?_
      rw [eventually_inf_principal]
      refine Eventually.of_forall fun s hs ↦ ?_
      have hs' : s.re ∈ Icc σ₁ σ₂ := ⟨hs.1.le, hs.2.le⟩
      have hξ' : 0 ≤ max ξ 0 := le_max_right _ _
      have hn1 := hnorm1 s hs'.1
      have hu : 1 ≤ ‖s - z0‖ ^ (p + q * s.re) := Real.one_le_rpow hn1 (hℓ0 _ hs')
      have hW1 : ‖W s‖ ≤ E := (hWup s hs').trans
        (mul_le_of_le_one_left hE0.le (inv_le_one_of_one_le₀ hu))
      have hF1 := hCξ s hs'
      have hpow : ‖s - z0‖ ^ max ξ 0 ≤
          Real.exp (max ξ 0 * R) * Real.exp (max ξ 0 / c * Real.exp (c * |s.im|)) := by
        rw [← Real.exp_add]
        refine (rpow_le_exp_mul (by linarith) hξ').trans (Real.exp_le_exp.mpr ?_)
        have h1 : ‖s - z0‖ ≤ R + |s.im| :=
          (hnormle s hs'.1).trans (by rw [hR]; linarith [hs'.2])
        have h2 : c * |s.im| ≤ Real.exp (c * |s.im|) := by
          linarith [Real.add_one_le_exp (c * |s.im|)]
        have h3 : max ξ 0 * |s.im| ≤ max ξ 0 / c * Real.exp (c * |s.im|) := by
          calc max ξ 0 * |s.im| = max ξ 0 / c * (c * |s.im|) := by field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left h1 hξ']
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc ‖W s‖ * ‖F s‖ ≤ E * (Cξ * ‖s - z0‖ ^ max ξ 0) :=
            mul_le_mul hW1 hF1 (norm_nonneg _) (by positivity)
        _ ≤ E * (Cξ * (Real.exp (max ξ 0 * R) *
              Real.exp (max ξ 0 / c * Real.exp (c * |s.im|)))) := by gcongr
        _ = _ := by ring
    have hbound : ∀ s : ℂ, s.re ∈ Icc σ₁ σ₂ → ‖W s * F s‖ ≤ D := by
      intro s hs
      refine PhragmenLindelof.vertical_strip (a := σ₁) (b := σ₂) (f := fun s ↦ W s * F s)
        (C := D) (z := s) hGd ⟨c, hc_lt, max ξ 0 / c, hGgrowth⟩ ?_ ?_ hs.1 hs.2
      · intro z hz
        have hz' : z.re ∈ Icc σ₁ σ₂ := by rw [hz]; exact ⟨le_rfl, h₁₂.le⟩
        have hu : 0 < ‖z - z0‖ ^ A := Real.rpow_pos_of_pos (by linarith [hnorm1 z hz'.1]) _
        have hWz := hWup z hz'
        rw [hz, hℓ₁] at hWz
        rw [norm_mul]
        calc ‖W z‖ * ‖F z‖ ≤ ((‖z - z0‖ ^ A)⁻¹ * E) * (C₁ * ‖z - z0‖ ^ A) :=
              mul_le_mul hWz (hC₁ z hz) (norm_nonneg _) (by positivity)
          _ = E * C₁ := by field_simp
          _ ≤ D := by rw [hD]; gcongr; exact le_max_left _ _
      · intro z hz
        have hz' : z.re ∈ Icc σ₁ σ₂ := by rw [hz]; exact ⟨h₁₂.le, le_rfl⟩
        have hu : 0 < ‖z - z0‖ ^ B := Real.rpow_pos_of_pos (by linarith [hnorm1 z hz'.1]) _
        have hWz := hWup z hz'
        rw [hz, hℓ₂] at hWz
        rw [norm_mul]
        calc ‖W z‖ * ‖F z‖ ≤ ((‖z - z0‖ ^ B)⁻¹ * E) * (C₂ * ‖z - z0‖ ^ B) :=
              mul_le_mul hWz (hC₂ z hz) (norm_nonneg _) (by positivity)
          _ = E * C₂ := by field_simp
          _ ≤ D := by rw [hD]; gcongr; exact le_max_right _ _
    intro s hs hεs
    have hpos : 0 < (s - z0).re := by rw [hre, hx0]; linarith [hs.1]
    have hu : 0 < ‖s - z0‖ ^ (p + q * s.re) :=
      Real.rpow_pos_of_pos (by linarith [hnorm1 s hs.1]) _
    have hlow : (‖s - z0‖ ^ (p + q * s.re))⁻¹ ≤ ‖W s‖ := by
      rw [hWnorm s hs.1]
      refine le_mul_of_one_le_right (by positivity) (Real.one_le_exp ?_)
      rw [mul_assoc]
      exact mul_nonneg (by linarith) (im_mul_halfArg_bounds hε hpos (by rwa [him])).1
    have hb := hbound s hs
    rw [norm_mul] at hb
    have h' : (‖s - z0‖ ^ (p + q * s.re))⁻¹ * ‖F s‖ ≤ D :=
      (mul_le_mul_of_nonneg_right hlow (norm_nonneg _)).trans hb
    rw [inv_mul_le_iff₀ hu] at h'
    linarith
  have hσ0 : 0 ≤ p + q * σ := hℓ0 σ hσ
  rw [← hℓ σ]
  refine Asymptotics.IsBigO.of_bound (D * 2 ^ (p + q * σ)) ?_
  filter_upwards [(tendsto_comap.eventually_ge_atTop R).filter_mono inf_le_left,
    mem_inf_of_right (mem_principal_self _)] with s hsR hs
  have hs' : s.re = σ := hs
  have hsR' : R ≤ |s.im| := hsR
  have hsI : s.re ∈ Icc σ₁ σ₂ := by rw [hs']; exact hσ
  have hFs : ‖F s‖ ≤ D * ‖s - z0‖ ^ (p + q * s.re) := by
    rcases le_total 0 s.im with h | h
    · exact key 1 (Or.inl rfl) s hsI (by linarith)
    · exact key (-1) (Or.inr rfl) s hsI (by linarith)
  rw [hs'] at hFs
  have h2 : ‖s - z0‖ ≤ 2 * |s.im| := by
    have := hnormle s hsI.1
    rw [hs'] at this
    have : σ - x0 ≤ R := by rw [hR]; linarith [hσ.2]
    linarith
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖F s‖ ≤ D * ‖s - z0‖ ^ (p + q * σ) := hFs
    _ ≤ D * (2 * |s.im|) ^ (p + q * σ) := by gcongr
    _ = D * 2 ^ (p + q * σ) * |s.im| ^ (p + q * σ) := by
      rw [Real.mul_rpow (by norm_num) (abs_nonneg _)]; ring

open Complex in
/-- Under the reflection `s ↦ c - s`, vertical power bounds over one set of real parts become
bounds over the reflected set. -/
lemma isBigO_comp_const_sub {F : ℂ → ℂ} {c : ℝ} {S T : Set ℝ} (hST : ∀ x ∈ T, c - x ∈ S)
    {r : ℝ} (h : F =O[atHeight ⊓ 𝓟 (re ⁻¹' S)] fun s ↦ |s.im| ^ r) :
    (fun s ↦ F (↑c - s)) =O[atHeight ⊓ 𝓟 (re ⁻¹' T)] fun s ↦ |s.im| ^ r := by
  have ht : Tendsto (fun s : ℂ ↦ (c : ℂ) - s) (atHeight ⊓ 𝓟 (re ⁻¹' T))
      (atHeight ⊓ 𝓟 (re ⁻¹' S)) := by
    refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
    · have : (abs ∘ im) ∘ (fun s : ℂ ↦ (c : ℂ) - s) = abs ∘ im := by
        funext s; simp
      rw [this]
      exact tendsto_comap.mono_left inf_le_left
    · exact mem_inf_of_right (mem_principal.mpr fun s hs ↦ by simpa using hST _ hs)
  have := h.comp_tendsto ht
  simpa [Function.comp_def] using this

open Complex in
/-- Phragmén–Lindelöf interpolation of polynomial vertical bounds on a closed vertical strip:
a function holomorphic near the strip, polynomially bounded on it, and `O(|t|^A)`, `O(|t|^B)` on
the two edges is `O(|t|^e)` on each intermediate line, with `e` the affine interpolation. -/
lemma isBigO_rpow_of_verticalStrip {σ₁ σ₂ : ℝ} (h₁₂ : σ₁ < σ₂) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (re ⁻¹' Icc σ₁ σ₂)) {ξ : ℝ}
    (hpoly : F =O[atHeight ⊓ 𝓟 (re ⁻¹' Icc σ₁ σ₂)] fun s ↦ |s.im| ^ ξ)
    {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : F =O[atHeight ⊓ 𝓟 (re ⁻¹' {σ₁})] fun s ↦ |s.im| ^ A)
    (hB : F =O[atHeight ⊓ 𝓟 (re ⁻¹' {σ₂})] fun s ↦ |s.im| ^ B)
    {σ : ℝ} (hσ : σ ∈ Icc σ₁ σ₂) :
    F =O[atHeight ⊓ 𝓟 (re ⁻¹' {σ})]
      fun s ↦ |s.im| ^ (((σ₂ - σ) * A + (σ - σ₁) * B) / (σ₂ - σ₁)) := by
  rcases le_total B A with hBA | hAB
  · exact isBigO_rpow_of_verticalStrip_of_le h₁₂ hF hpoly hB0 hBA hA hB hσ
  · obtain ⟨c, hc⟩ : ∃ c : ℝ, c = σ₁ + σ₂ := ⟨_, rfl⟩
    have hmaps : ∀ x ∈ Icc σ₁ σ₂, c - x ∈ Icc σ₁ σ₂ := fun x hx ↦
      ⟨by rw [hc]; linarith [hx.2], by rw [hc]; linarith [hx.1]⟩
    have hG : DifferentiableOn ℂ (fun s ↦ F (↑c - s)) (re ⁻¹' Icc σ₁ σ₂) := by
      refine hF.comp ((differentiableOn_const _).sub differentiableOn_id) ?_
      intro s hs
      have := hmaps _ hs
      simpa using this
    have h := isBigO_rpow_of_verticalStrip_of_le h₁₂ hG
      (isBigO_comp_const_sub hmaps hpoly) hA0 hAB
      (isBigO_comp_const_sub (S := {σ₂}) (T := {σ₁})
        (by intro x hx; rw [mem_singleton_iff.mp hx, hc]; simp) hB)
      (isBigO_comp_const_sub (S := {σ₁}) (T := {σ₂})
        (by intro x hx; rw [mem_singleton_iff.mp hx, hc]; simp) hA)
      (hmaps σ hσ)
    have h' := isBigO_comp_const_sub (c := c) (S := {c - σ}) (T := {σ})
      (by intro x hx; rw [mem_singleton_iff.mp hx]; simp) h
    have e : ((σ₂ - (c - σ)) * B + (c - σ - σ₁) * A) / (σ₂ - σ₁) =
        ((σ₂ - σ) * A + (σ - σ₁) * B) / (σ₂ - σ₁) := by
      rw [hc]; ring
    rw [e] at h'
    simpa using h'

open Complex in
/-- Clearing finitely many simple poles over a closed strip of real parts inside the half-plane:
multiplying by the polynomial with the poles as roots and passing to normal form gives a function
holomorphic on the strip which, for large heights, equals that product, while the polynomial has
size `|t| ^ N` from above and below. -/
lemma exists_clearPoles_verticalStrip {f : ℂ → ℂ} {a : ℝ}
    (hf : MeromorphicNFOn f (re ⁻¹' Ioi a))
    (hFinite : {s : ℂ | a < s.re ∧ meromorphicOrderAt f s < 0}.Finite)
    (hSimple : ∀ s : ℂ, a < s.re → meromorphicOrderAt f s < 0 → meromorphicOrderAt f s = -1)
    {l u : ℝ} (hl : a < l) :
    ∃ g P : ℂ → ℂ, ∃ N : ℕ, DifferentiableOn ℂ g (re ⁻¹' Icc l u) ∧
      (∀ᶠ s in atHeight ⊓ 𝓟 (re ⁻¹' Icc l u), g s = P s * f s ∧ P s ≠ 0) ∧
      P =O[atHeight ⊓ 𝓟 (re ⁻¹' Icc l u)] (fun s ↦ |s.im| ^ (N : ℝ)) ∧
      (fun s ↦ (P s)⁻¹) =O[atHeight ⊓ 𝓟 (re ⁻¹' Icc l u)]
        (fun s ↦ |s.im| ^ (-(N : ℝ))) := by
  obtain ⟨Z, hZ⟩ : ∃ Z : Finset ℂ, Z = hFinite.toFinset := ⟨_, rfl⟩
  have hmemZ : ∀ x, x ∈ Z ↔ a < x.re ∧ meromorphicOrderAt f x < 0 := by
    intro x; rw [hZ, Set.Finite.mem_toFinset]; rfl
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun s ↦ ∏ ρ ∈ Z, (s - ρ) := ⟨_, rfl⟩
  have hPd : Differentiable ℂ P := by
    rw [hP]; fun_prop
  have hPa : ∀ x, AnalyticAt ℂ P x := fun x ↦ hPd.analyticAt x
  have hggm : MeromorphicOn (P * f) (re ⁻¹' Ioi a) :=
    MeromorphicOn.mul (fun x _ ↦ (hPa x).meromorphicAt) hf.meromorphicOn
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = toMeromorphicNFOn (P * f) (re ⁻¹' Ioi a) := ⟨_, rfl⟩
  have hfa : ∀ x : ℂ, a < x.re → x ∉ Z → AnalyticAt ℂ f x := by
    intro x hx hxZ
    refine (hf hx).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
    by_contra h
    exact hxZ ((hmemZ x).mpr ⟨hx, not_le.mp h⟩)
  have hga : ∀ x : ℂ, a < x.re → AnalyticAt ℂ g x := by
    intro x hx
    rw [hg]
    refine (meromorphicNFOn_toMeromorphicNFOn (P * f) _
      (show x ∈ re ⁻¹' Ioi a from hx)).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
    rw [meromorphicOrderAt_toMeromorphicNFOn hggm hx,
      meromorphicOrderAt_mul (hPa x).meromorphicAt (hf hx).meromorphicAt]
    by_cases hxZ : x ∈ Z
    · have hxp := (hmemZ x).mp hxZ
      have hfo : meromorphicOrderAt f x = -1 := hSimple x hxp.1 hxp.2
      have hPx : P x = 0 := by rw [hP]; exact Finset.prod_eq_zero hxZ (sub_self x)
      have hne : analyticOrderAt P x ≠ 0 := (hPa x).analyticOrderAt_ne_zero.mpr hPx
      rw [(hPa x).meromorphicOrderAt_eq, hfo]
      cases h : analyticOrderAt P x with
      | top => simp
      | coe n =>
        rw [h] at hne
        have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne)
        simp only [ENat.map_natCast]
        have : ((n : ℤ) : WithTop ℤ) + -1 = ((n - 1 : ℤ) : WithTop ℤ) := by
          rw [sub_eq_add_neg]; norm_cast
        rw [this]
        exact_mod_cast (by omega : (0 : ℤ) ≤ n - 1)
    · exact add_nonneg (hPa x).meromorphicOrderAt_nonneg (hfa x hx hxZ).meromorphicOrderAt_nonneg
  have hgeq : ∀ x : ℂ, a < x.re → x ∉ Z → g x = P x * f x := by
    intro x hx hxZ
    rw [hg, toMeromorphicNFOn_eq_toMeromorphicNFAt hggm hx,
      toMeromorphicNFAt_eq_self.2 (((hPa x).mul (hfa x hx hxZ)).meromorphicNFAt)]
    rfl
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ ρ ∈ Z, ‖ρ‖ := ⟨_, rfl⟩
  have hρS : ∀ ρ ∈ Z, ‖ρ‖ ≤ S := fun ρ hρ ↦
    hS ▸ Finset.single_le_sum (f := fun i ↦ ‖i‖) (fun i _ ↦ norm_nonneg i) hρ
  have hS0 : 0 ≤ S := hS ▸ Finset.sum_nonneg fun i _ ↦ norm_nonneg i
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 2 * S + |l| + |u| + 1 := ⟨_, rfl⟩
  have hfactor : ∀ s : ℂ, s.re ∈ Icc l u → T ≤ |s.im| → ∀ ρ ∈ Z,
      |s.im| / 2 ≤ ‖s - ρ‖ ∧ ‖s - ρ‖ ≤ 2 * |s.im| := by
    intro s hs hT' ρ hρ
    have h1 := hρS ρ hρ
    have hre : |s.re| ≤ |l| + |u| := abs_le.mpr
      ⟨by linarith [neg_abs_le l, abs_nonneg u, hs.1],
        by linarith [le_abs_self u, abs_nonneg l, hs.2]⟩
    constructor
    · have h4 := abs_im_le_norm (s - ρ)
      have h2 : |ρ.im| ≤ ‖ρ‖ := abs_im_le_norm ρ
      rw [sub_im] at h4
      have h3 : |s.im| - |ρ.im| ≤ |s.im - ρ.im| := abs_sub_abs_le_abs_sub _ _
      linarith [abs_nonneg l, abs_nonneg u]
    · have h4 := norm_sub_le s ρ
      have h2 := norm_le_abs_re_add_abs_im s
      linarith [abs_nonneg l, abs_nonneg u]
  have hev : ∀ᶠ s in atHeight ⊓ 𝓟 (re ⁻¹' Icc l u), T ≤ |s.im| ∧ s.re ∈ Icc l u :=
    ((tendsto_comap.eventually_ge_atTop T).filter_mono inf_le_left).and
      (mem_inf_of_right (mem_principal_self _))
  have hPnorm : ∀ s : ℂ, s.re ∈ Icc l u → T ≤ |s.im| →
      (|s.im| / 2) ^ Z.card ≤ ‖P s‖ ∧ ‖P s‖ ≤ (2 * |s.im|) ^ Z.card := by
    intro s hs hT'
    rw [hP, norm_prod]
    constructor
    · rw [← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun ρ hρ ↦ (hfactor s hs hT' ρ hρ).1
    · rw [← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun ρ hρ ↦ (hfactor s hs hT' ρ hρ).2
  refine ⟨g, P, Z.card, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (hga s (lt_of_lt_of_le hl hs.1)).differentiableAt.differentiableWithinAt
  · filter_upwards [hev] with s hs'
    obtain ⟨hT', hs⟩ := hs'
    have him0 : 0 < |s.im| := by linarith [abs_nonneg l, abs_nonneg u]
    have hsZ : s ∉ Z := by
      intro hsZ
      have h1 := hρS s hsZ
      have h2 := abs_im_le_norm s
      linarith [abs_nonneg l, abs_nonneg u]
    refine ⟨hgeq s (lt_of_lt_of_le hl hs.1) hsZ, ?_⟩
    have h1 := (hPnorm s hs hT').1
    have hpos : 0 < (|s.im| / 2) ^ Z.card := pow_pos (half_pos him0) _
    intro h0
    rw [h0, norm_zero] at h1
    linarith
  · refine Asymptotics.IsBigO.of_bound (2 ^ Z.card) ?_
    filter_upwards [hev] with s hs'
    obtain ⟨hT', hs⟩ := hs'
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_natCast, ← mul_pow]
    exact (hPnorm s hs hT').2
  · refine Asymptotics.IsBigO.of_bound (2 ^ Z.card) ?_
    filter_upwards [hev] with s hs'
    obtain ⟨hT', hs⟩ := hs'
    have him0 : 0 < |s.im| := by linarith [abs_nonneg l, abs_nonneg u]
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg him0.le, Real.rpow_natCast, norm_inv]
    have h1 := (hPnorm s hs hT').1
    have hpos : 0 < (|s.im| / 2) ^ Z.card := pow_pos (half_pos him0) _
    calc ‖P s‖⁻¹ ≤ ((|s.im| / 2) ^ Z.card)⁻¹ := inv_anti₀ hpos h1
      _ = 2 ^ Z.card * (|s.im| ^ Z.card)⁻¹ := by rw [div_pow]; field_simp

section GrowthOrder

variable {f : ℂ → ℂ} {a : ℝ}
variable (hf : MeromorphicNFOn f (Complex.re ⁻¹' Ioi a))
  (hFinite : {s : ℂ | a < s.re ∧ meromorphicOrderAt f s < 0}.Finite)
  (hSimple : ∀ s : ℂ, a < s.re → meromorphicOrderAt f s < 0 → meromorphicOrderAt f s = -1)
  (hGrowth : ∃ ξ : ℝ, 0 < ξ ∧
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioi a)] fun s ↦ |s.im| ^ ξ)

include hf hFinite hSimple hGrowth

-- Retain the meromorphicity and pole hypotheses in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Lemma B.1.1.1, p. 589. In the open half-plane the vertical growth
order is finite under the uniform polynomial bound.
Deviation: This and the other parts use meromorphic functions in normal form
and omit the unused parameter `b > a`. -/
theorem verticalGrowthOrder_ne_top {σ : ℝ} (hσ : a < σ) :
    verticalGrowthOrder f σ ≠ ⊤ := by
  obtain ⟨ξ, hξ, hBound⟩ := hGrowth
  let k : ℝ≥0 := ⟨ξ, hξ.le⟩
  have hLine : ({σ} : Set ℝ) ⊆ Ioi a := singleton_subset_iff.mpr hσ
  refine lt_top_iff_ne_top.mp (lt_of_le_of_lt ?_ (ENNReal.coe_lt_top (r := k)))
  unfold verticalGrowthOrder
  refine sInf_le ⟨k, ?_, rfl⟩
  exact hBound.mono (inf_le_inf_left _ (principal_mono.mpr (preimage_mono hLine)))

-- TODO(paper-gap): The proof's equality `μ_g = μ + N` fails for `f(s) = 1/s`
-- on `Re(s) > -1`. Clearing its one pole gives `g(s) = 1`, and both orders are zero.

omit hf hFinite hSimple hGrowth in
/-- Simple poles can be removed by factors tending to one at large absolute height.
The resulting holomorphic function has the same asymptotic size on the half-plane. -/
private theorem exists_analyticOnNhd_isTheta_atHeight {f : ℂ → ℂ} {a : ℝ}
    (hf : MeromorphicNFOn f (Complex.re ⁻¹' Ioi a))
    (hFinite : {s : ℂ | a < s.re ∧ meromorphicOrderAt f s < 0}.Finite)
    (hSimple : ∀ s : ℂ, a < s.re → meromorphicOrderAt f s < 0 → meromorphicOrderAt f s = -1) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Complex.re ⁻¹' Ioi a) ∧
      g =Θ[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioi a)] f := by
  classical
  let poles := hFinite.toFinset
  let factor (p z : ℂ) := (z - p) / (z - (a : ℂ))
  let multiplier : ℂ → ℂ := ∏ p ∈ poles, factor p
  let product : ℂ → ℂ := multiplier * f
  let U := Complex.re ⁻¹' Ioi a
  have hDen (z : ℂ) (hz : z ∈ U) : z - (a : ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hz' : a < z.re := hz
    simp [h] at hz'
  have hFactor (p : ℂ) {z : ℂ} (hz : z ∈ U) : AnalyticAt ℂ (factor p) z :=
    (show AnalyticAt ℂ (fun w : ℂ ↦ w - p) z by fun_prop).div (by fun_prop) (hDen z hz)
  have hMultiplier : AnalyticOnNhd ℂ multiplier U := fun z hz ↦
    Finset.analyticAt_prod _ (fun p _ ↦ hFactor p hz)
  have hProduct : MeromorphicOn product U := fun z hz ↦
    (hMultiplier z hz).meromorphicAt.mul (hf hz).meromorphicAt
  have hOrder (z : ℂ) (hz : z ∈ U) : 0 ≤ meromorphicOrderAt product z := by
    rw [meromorphicOrderAt_mul (hMultiplier z hz).meromorphicAt (hf hz).meromorphicAt]
    by_cases hp : meromorphicOrderAt f z < 0
    · have hmem : z ∈ poles := hFinite.mem_toFinset.mpr ⟨hz, hp⟩
      have hsum : 1 ≤ meromorphicOrderAt multiplier z := by
        change 1 ≤ meromorphicOrderAt (∏ p ∈ poles, factor p) z
        rw [meromorphicOrderAt_prod (fun p _ ↦ (hFactor p hz).meromorphicAt)]
        have hself : meromorphicOrderAt (factor z) z = 1 := by
          have hinv : AnalyticAt ℂ (fun w : ℂ ↦ (w - (a : ℂ))⁻¹) z :=
            (show AnalyticAt ℂ (fun w : ℂ ↦ w - (a : ℂ)) z by fun_prop).inv (hDen z hz)
          have h := meromorphicOrderAt_mul_of_ne_zero (f := fun w ↦ w - z)
            hinv (inv_ne_zero (hDen z hz))
          simpa only [Pi.mul_def, ← div_eq_inv_mul, factor, meromorphicOrderAt_id_sub_const] using h
        rw [← hself]
        exact Finset.single_le_sum (fun p _ ↦ (hFactor p hz).meromorphicOrderAt_nonneg) hmem
      rw [hSimple z hz hp]
      exact (by decide : (0 : WithTop ℤ) ≤ 1 + (-1)).trans (add_le_add_left hsum _)
    · exact add_nonneg (hMultiplier z hz).meromorphicOrderAt_nonneg (le_of_not_gt hp)
  let g := toMeromorphicNFOn product U
  have hg : AnalyticOnNhd ℂ g U := by
    intro z hz
    exact ((meromorphicNFOn_toMeromorphicNFOn product U) hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (by simpa only [g, meromorphicOrderAt_toMeromorphicNFOn hProduct hz] using hOrder z hz)
  have hHeight : Tendsto (fun z : ℂ ↦ |z.im|) atHeight atTop := tendsto_comap
  have hNorm : Tendsto (fun z : ℂ ↦ ‖z - (a : ℂ)‖) atHeight atTop :=
    tendsto_atTop_mono (fun z ↦ by simpa using Complex.abs_im_le_norm (z - (a : ℂ))) hHeight
  have hFactorLimit (p : ℂ) : Tendsto (factor p) atHeight (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hLimit : Tendsto (fun z : ℂ ↦ ‖(a : ℂ) - p‖ * ‖z - (a : ℂ)‖⁻¹)
        atHeight (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp hNorm).const_mul ‖(a : ℂ) - p‖
    refine hLimit.congr' ?_
    filter_upwards [hNorm.eventually_gt_atTop 0] with z hz
    have hd := norm_pos_iff.mp hz
    have hEq : factor p z - 1 = ((a : ℂ) - p) / (z - (a : ℂ)) := by
      dsimp [factor]
      field_simp
      ring
    rw [hEq, norm_div, div_eq_mul_inv]
  have hLimit : Tendsto multiplier atHeight (𝓝 1) := by
    have h := tendsto_finsetProd poles (a := fun _ ↦ (1 : ℂ)) (fun p _ ↦ hFactorLimit p)
    rw [Finset.prod_const_one] at h
    exact h.congr (fun z ↦ (Finset.prod_apply z poles factor).symm)
  let heightInU := atHeight ⊓ 𝓟 U
  have hEq : g =ᶠ[heightInU] product := by
    have hAvoid : ∀ᶠ z in atHeight, z ∉ poles := by
      have hAvoidEach : ∀ᶠ z in atHeight, ∀ p ∈ poles, z ≠ p := by
        apply (Filter.eventually_all_finset poles).2
        intro p _
        filter_upwards [hHeight.eventually_gt_atTop |p.im|] with z hz
        rintro rfl
        exact (lt_irrefl _ hz)
      exact hAvoidEach.mono fun z hz hp ↦ hz z hp rfl
    change ∀ᶠ z in atHeight ⊓ 𝓟 U, g z = product z
    rw [eventually_inf_principal]
    filter_upwards [hAvoid] with z hz hzU
    have hzNonneg : 0 ≤ meromorphicOrderAt f z :=
      le_of_not_gt (fun hp ↦ hz (hFinite.mem_toFinset.mpr ⟨hzU, hp⟩))
    have hprod : AnalyticAt ℂ product z :=
      (hMultiplier z hzU).mul ((hf hzU).meromorphicOrderAt_nonneg_iff_analyticAt.mp hzNonneg)
    dsimp only [g]
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hProduct hzU,
      toMeromorphicNFAt_eq_self.mpr hprod.meromorphicNFAt]
  have hT : multiplier =Θ[atHeight] (fun _ ↦ (1 : ℂ)) := by
    refine ⟨Asymptotics.isBigO_const_of_tendsto hLimit one_ne_zero, ?_⟩
    refine Asymptotics.IsBigO.of_bound 2 ?_
    have hclose := (tendsto_iff_norm_sub_tendsto_zero.mp hLimit).eventually_lt_const
      (show (0 : ℝ) < 1 / 2 by norm_num)
    filter_upwards [hclose] with z hz
    have H := norm_sub_norm_le (1 : ℂ) (multiplier z)
    rw [norm_sub_rev, norm_one] at H
    rw [norm_one]
    linarith
  refine ⟨g, hg, hEq.isTheta.trans ?_⟩
  have hh := (hT.mono (show heightInU ≤ atHeight from inf_le_left)).mul
    (Asymptotics.isTheta_refl f heightInU)
  exact hh.trans_eventuallyEq (Eventually.of_forall fun z ↦ one_mul (f z))

/-- Paper: Lemma B.1.1.1, p. 589. The finite growth order is convex as a function
of the real part in the open half-plane. -/
theorem convexOn_verticalGrowthOrder :
    ConvexOn ℝ (Ioi a) (fun σ ↦ (verticalGrowthOrder f σ).toReal) := by
  obtain ⟨g, hg, hgf⟩ := exists_analyticOnNhd_isTheta_atHeight hf hFinite hSimple
  obtain ⟨K, hK, hGrowth⟩ := hGrowth
  have line_le_halfPlane {x : ℝ} (hx : a < x) :
      atHeight ⊓ 𝓟 (Complex.re ⁻¹' {x}) ≤ atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioi a) :=
    inf_le_inf_left _ (Filter.principal_mono.mpr (preimage_mono (singleton_subset_iff.mpr hx)))
  have approx {x ε : ℝ} (hx : a < x) (hε : 0 < ε) :
      ∃ k : ℝ≥0, (k : ℝ) < (verticalGrowthOrder f x).toReal + ε ∧
        f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {x})] fun z ↦ |z.im| ^ (k : ℝ) := by
    let k : ℝ≥0 := ⟨K, hK.le⟩
    have hKBound : verticalGrowthOrder f x ≤ (k : ℝ≥0∞) :=
      sInf_le ⟨k, hGrowth.mono (line_le_halfPlane hx), rfl⟩
    have htop : verticalGrowthOrder f x ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top hKBound
    have hlt : verticalGrowthOrder f x < ENNReal.ofReal ((verticalGrowthOrder f x).toReal + ε) :=
      (ENNReal.lt_ofReal_iff_toReal_lt htop).mpr (lt_add_of_pos_right _ hε)
    unfold verticalGrowthOrder at hlt
    obtain ⟨_, ⟨k, hk, rfl⟩, hlt⟩ := sInf_lt_iff.mp hlt
    exact ⟨k, ENNReal.coe_lt_ofReal.mp hlt, hk⟩
  refine convexOn_iff_pairwise_pos.mpr ⟨convex_Ioi _, ?_⟩
  intro x hx y hy hne p q hp hq hpq
  change (verticalGrowthOrder f (p * x + q * y)).toReal ≤
    p * (verticalGrowthOrder f x).toReal + q * (verticalGrowthOrder f y).toReal
  wlog hxy : x < y generalizing x y p q
  · simpa only [add_comm] using this hy hx hne.symm hq hp (by rwa [add_comm])
      (lt_of_le_of_ne (le_of_not_gt hxy) hne.symm)
  have strip_sub : Complex.re ⁻¹' Icc x y ⊆ Complex.re ⁻¹' Ioi a :=
    fun _ hz ↦ hx.trans_le hz.1
  have hStrip := inf_le_inf_left atHeight (Filter.principal_mono.mpr strip_sub)
  have hInt : a < p * x + q * y := by
    have hx' : a < x := hx
    have hprod : 0 < q * (y - x) := mul_pos hq (sub_pos.mpr hxy)
    nlinarith [congrArg (fun t : ℝ ↦ t * x) hpq]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨k₀, hk₀, h₀⟩ := approx hx hε
  obtain ⟨k₁, hk₁, h₁⟩ := approx hy hε
  have hInterp := isBigO_rpow_verticalStrip_interpolate hxy hK.le k₀.coe_nonneg k₁.coe_nonneg
    hp.le hq.le hpq (hg.differentiableOn.mono strip_sub)
    ((hgf.mono hStrip).trans_isBigO (hGrowth.mono hStrip))
    ((hgf.mono (line_le_halfPlane hx)).trans_isBigO h₀)
    ((hgf.mono (line_le_halfPlane hy)).trans_isBigO h₁)
  have hBound := (hgf.symm.mono (line_le_halfPlane hInt)).trans_isBigO hInterp
  let k : ℝ≥0 := ⟨p * (k₀ : ℝ) + q * (k₁ : ℝ), by positivity⟩
  have hOrder : verticalGrowthOrder f (p * x + q * y) ≤ (k : ℝ≥0∞) :=
    sInf_le ⟨k, hBound, rfl⟩
  calc
    _ ≤ (k : ℝ) := ENNReal.toReal_mono ENNReal.coe_ne_top hOrder
    _ ≤ p * (verticalGrowthOrder f x).toReal + q * (verticalGrowthOrder f y).toReal + ε := by
      change p * (k₀ : ℝ) + q * (k₁ : ℝ) ≤ _
      nlinarith [mul_le_mul_of_nonneg_left hk₀.le hp.le, mul_le_mul_of_nonneg_left hk₁.le hq.le,
        congrArg (fun t : ℝ ↦ t * ε) hpq]

/-- The convexity inequality behind Lemma B.1.1.1: for `a < σ₁ < σ < σ₂`, the growth order at
`σ` is at most the affine interpolation of the orders at `σ₁` and `σ₂`. -/
theorem verticalGrowthOrder_toReal_le_interp {σ₁ σ σ₂ : ℝ} (h₁ : a < σ₁) (h₁σ : σ₁ < σ)
    (hσ₂ : σ < σ₂) :
    (verticalGrowthOrder f σ).toReal ≤
      ((σ₂ - σ) * (verticalGrowthOrder f σ₁).toReal +
        (σ - σ₁) * (verticalGrowthOrder f σ₂).toReal) / (σ₂ - σ₁) := by
  obtain ⟨ξ, hξ, hO⟩ := hGrowth
  have h₁₂ : σ₁ < σ₂ := h₁σ.trans hσ₂
  have hw : 0 < σ₂ - σ₁ := sub_pos.2 h₁₂
  have hsub : ∀ K : Set ℝ, K ⊆ Icc σ₁ σ₂ →
      atHeight ⊓ 𝓟 (Complex.re ⁻¹' K) ≤ atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc σ₁ σ₂) :=
    fun K hK ↦ inf_le_inf_left _ (principal_mono.2 (preimage_mono hK))
  have hIcc : atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc σ₁ σ₂) ≤
      atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioi a) :=
    inf_le_inf_left _ (principal_mono.2 (preimage_mono fun x hx ↦ lt_of_lt_of_le h₁ hx.1))
  have hne : ∀ x ∈ Icc σ₁ σ₂, verticalGrowthOrder f x ≠ ⊤ := fun x hx ↦
    verticalGrowthOrder_ne_top_of_isBigO hξ.le
      ((hO.mono hIcc).mono (hsub {x} (singleton_subset_iff.2 hx)))
  obtain ⟨g, P, N, hgd, hgeq, hPO, hPinv⟩ :=
    exists_clearPoles_verticalStrip hf hFinite hSimple (u := σ₂) h₁
  have htrans : ∀ K : Set ℝ, K ⊆ Icc σ₁ σ₂ → ∀ r : ℝ, 0 ≤ r →
      f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' K)] (fun s ↦ |s.im| ^ r) →
      g =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' K)] (fun s ↦ |s.im| ^ ((N : ℝ) + r)) := by
    intro K hK r hr hfK
    have e : (fun s : ℂ ↦ |s.im| ^ ((N : ℝ) + r)) = fun s ↦ |s.im| ^ (N : ℝ) * |s.im| ^ r :=
      funext fun s ↦ Real.rpow_add_of_nonneg (abs_nonneg _) (Nat.cast_nonneg _) hr
    rw [e]
    refine Asymptotics.IsBigO.congr' ((hPO.mono (hsub K hK)).mul hfK) ?_ EventuallyEq.rfl
    filter_upwards [hgeq.filter_mono (hsub K hK)] with s hs
    exact hs.1.symm
  have hφ₁ : 0 ≤ (verticalGrowthOrder f σ₁).toReal := ENNReal.toReal_nonneg
  have hφ₂ : 0 ≤ (verticalGrowthOrder f σ₂).toReal := ENNReal.toReal_nonneg
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  have hA := isBigO_of_verticalGrowthOrder_toReal_lt (hne σ₁ ⟨le_rfl, h₁₂.le⟩)
    (lt_add_of_pos_right (verticalGrowthOrder f σ₁).toReal hδ)
  have hB := isBigO_of_verticalGrowthOrder_toReal_lt (hne σ₂ ⟨h₁₂.le, le_rfl⟩)
    (lt_add_of_pos_right (verticalGrowthOrder f σ₂).toReal hδ)
  have hgA := htrans {σ₁} (singleton_subset_iff.2 ⟨le_rfl, h₁₂.le⟩) _ (by positivity) hA
  have hgB := htrans {σ₂} (singleton_subset_iff.2 ⟨h₁₂.le, le_rfl⟩) _ (by positivity) hB
  have hgpoly := htrans (Icc σ₁ σ₂) subset_rfl ξ hξ.le (hO.mono hIcc)
  have hgσ := isBigO_rpow_of_verticalStrip h₁₂ hgd hgpoly (by positivity) (by positivity) hgA hgB
    (σ := σ) ⟨h₁σ.le, hσ₂.le⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = ((σ₂ - σ) * (verticalGrowthOrder f σ₁).toReal +
      (σ - σ₁) * (verticalGrowthOrder f σ₂).toReal) / (σ₂ - σ₁) + δ := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by
    rw [he]
    have := mul_nonneg (sub_pos.2 hσ₂).le hφ₁
    have := mul_nonneg (sub_pos.2 h₁σ).le hφ₂
    positivity
  have hexp : ((σ₂ - σ) * ((N : ℝ) + ((verticalGrowthOrder f σ₁).toReal + δ)) +
      (σ - σ₁) * ((N : ℝ) + ((verticalGrowthOrder f σ₂).toReal + δ))) / (σ₂ - σ₁) =
      (N : ℝ) + e := by
    rw [he]; field_simp; ring
  rw [hexp] at hgσ
  have hlσ := hsub {σ} (singleton_subset_iff.2 ⟨h₁σ.le, hσ₂.le⟩)
  have hfσ : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ e := by
    refine Asymptotics.IsBigO.congr' (hgσ.mul (hPinv.mono hlσ)) ?_ ?_
    · filter_upwards [hgeq.filter_mono hlσ] with s hs
      rw [hs.1]
      field_simp [hs.2]
    · filter_upwards [(tendsto_comap.eventually_gt_atTop (0:ℝ)).filter_mono inf_le_left] with s hs
      have hs' : 0 < |s.im| := hs
      rw [← Real.rpow_add hs']
      congr 1
      ring
  rw [← he]
  exact verticalGrowthOrder_toReal_le_of_isBigO he0 hfσ

/-- Paper: Lemma B.1.1.1, p. 589. The finite growth order is continuous in the
open half-plane. -/
theorem continuousOn_verticalGrowthOrder :
    ContinuousOn (fun σ ↦ (verticalGrowthOrder f σ).toReal) (Ioi a) := by
  refine ConvexOn.continuousOn isOpen_Ioi (convexOn_of_slope_mono_adjacent (convex_Ioi a) ?_)
  intro x y z hx hz hxy hyz
  have h := verticalGrowthOrder_toReal_le_interp hf hFinite hSimple hGrowth hx hxy hyz
  rw [div_le_div_iff₀ (sub_pos.2 hxy) (sub_pos.2 hyz)]
  rw [le_div_iff₀ (by linarith)] at h
  linarith

omit hf hFinite hSimple hGrowth

/-- A height bound on a set of real parts is equivalent to a single estimate
past a common height threshold. -/
private theorem isBigO_height_iff {f : ℂ → ℂ} {S : Set ℝ} {p : ℝ → ℝ} :
    (f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' S)] fun z ↦ |z.im| ^ p z.re) ↔
      ∃ C > 0, ∃ T : ℝ, ∀ z : ℂ, z.re ∈ S → T ≤ |z.im| →
        ‖f z‖ ≤ C * |z.im| ^ p z.re := by
  simp only [Asymptotics.isBigO_iff', eventually_inf_principal, eventually_comap, eventually_atTop,
    Function.comp_apply, mem_preimage, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  constructor
  · rintro ⟨C, hC, T, hT⟩
    exact ⟨C, hC, T, fun z hz h ↦ hT _ h z rfl hz⟩
  · rintro ⟨C, hC, T, hT⟩
    exact ⟨C, hC, T, fun t ht z hz h ↦ hT z h (hz ▸ ht)⟩

/-- A nonnegative affine exponent interpolates the two vertical boundary
bounds on a strip where the function is polynomially bounded and eventually
holomorphic at large absolute height. -/
private theorem isBigO_height_affine {f : ℂ → ℂ} {u v ξ p q : ℝ} (huv : u < v)
    (hξ : 0 ≤ ξ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hAnalytic : ∃ T : ℝ, ∀ z : ℂ, z.re ∈ Icc u v → T ≤ |z.im| →
      AnalyticAt ℂ f z)
    (hGrowth : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc u v)] fun z ↦ |z.im| ^ ξ)
    (hLeft : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {u})] fun z ↦ |z.im| ^ p)
    (hRight : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {v})] fun z ↦ |z.im| ^ q) :
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc u v)]
      fun z ↦ |z.im| ^ ((1 - (z.re - u) / (v - u)) * p + (z.re - u) / (v - u) * q) := by
  obtain ⟨T, hT⟩ := hAnalytic
  obtain ⟨C₀, hC₀, T₀, hT₀⟩ := (isBigO_height_iff (p := fun _ ↦ ξ)).mp hGrowth
  obtain ⟨C₁, hC₁, T₁, hT₁⟩ := (isBigO_height_iff (p := fun _ ↦ p)).mp hLeft
  obtain ⟨C₂, hC₂, T₂, hT₂⟩ := (isBigO_height_iff (p := fun _ ↦ q)).mp hRight
  let K := max (C₀ * (3 / 2 : ℝ) ^ ξ) (max (C₁ * (3 / 2 : ℝ) ^ p) (C₂ * (3 / 2 : ℝ) ^ q))
  have hK : 0 < K := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  let A : ℂ → ℂ := fun w ↦ (1 - (w - u) / (v - u)) * p + (w - u) / (v - u) * q
  let E : ℝ → ℝ := fun x ↦ (1 - (x - u) / (v - u)) * p + (x - u) / (v - u) * q
  have hA (w : ℂ) : (A w).re = E w.re := by
    simp [A, E, ← Complex.ofReal_sub, Complex.div_ofReal_re, Complex.mul_re]
  have hAu : E u = p := by simp [E]
  have hAv : E v = q := by simp [E, sub_ne_zero.mpr huv.ne']
  have hE {x : ℝ} (hx : x ∈ Icc u v) : 0 ≤ E x := by
    have hθ₀ := div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr huv.le)
    have hθ₁ : (x - u) / (v - u) ≤ 1 := by
      rw [div_le_iff₀ (sub_pos.mpr huv), one_mul]
      exact sub_le_sub_right hx.2 _
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hθ₁) hp) (mul_nonneg hθ₀ hq)
  refine (isBigO_height_iff (p := E)).mpr ⟨K * Real.exp ((v - u) ^ 2), by positivity,
    max 1 (max (4 * ξ) (2 * max (max T T₀) (max T₁ T₂))), ?_⟩
  intro z hz hHeight
  let R := |z.im|
  have hR₁ : 1 ≤ R := (le_max_left _ _).trans hHeight
  have hR : 0 < R := zero_lt_one.trans_le hR₁
  have hRξ : 4 * ξ ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hHeight)
  have hRT : max (max T T₀) (max T₁ T₂) ≤ R / 2 := by
    have := (le_max_right _ _).trans ((le_max_right _ _).trans hHeight)
    linarith
  -- The rectangle stays at absolute heights between R / 2 and 3 * R / 2.
  let L := z.im - R / 2
  let U := z.im + R / 2
  have hLU : L < U := by dsimp [L, U]; linarith
  have hHeights {w : ℂ} (hw : w.im ∈ Icc L U) :
      R / 2 ≤ |w.im| ∧ |w.im| ≤ (3 / 2 : ℝ) * R := by
    have hlo : z.im - R / 2 ≤ w.im := hw.1
    have hhi : w.im ≤ z.im + R / 2 := hw.2
    have hclose : |w.im - z.im| ≤ R / 2 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    constructor <;> linarith [abs_sub_abs_le_abs_sub z.im w.im,
      abs_sub_abs_le_abs_sub w.im z.im, abs_sub_comm z.im w.im]
  -- The square in the exponential suppresses the polynomial bound on the horizontal edges.
  let g : ℂ → ℂ := fun w ↦ f w * Complex.exp ((w - z) ^ 2 - A w * (Real.log R : ℂ))
  have hgNorm (w : ℂ) :
      ‖g w‖ = (‖f w‖ * Real.exp (-(w.im - z.im) ^ 2) / R ^ E w.re) *
        Real.exp ((w.re - z.re) ^ 2) := by
    simp only [g, norm_mul, Complex.norm_exp, Complex.sub_re, pow_two, Complex.mul_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hA,
      Real.rpow_def_of_pos hR, div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hg : DiffContOnCl ℂ g (Complex.reProdIm (Ioo u v) (Ioo L U)) := by
    apply DifferentiableOn.diffContOnCl
    rw [Complex.closure_reProdIm, closure_Ioo huv.ne, closure_Ioo hLU.ne]
    intro w hw
    have hw' := Complex.mem_reProdIm.mp hw
    have hfw := hT w hw'.1 ((le_max_left _ _).trans ((le_max_left _ _).trans
      (hRT.trans (hHeights hw'.2).1)))
    have hA' : Differentiable ℂ A := by unfold A; fun_prop
    have hWeight : Differentiable ℂ
        (fun w ↦ Complex.exp ((w - z) ^ 2 - A w * (Real.log R : ℂ))) := by
      fun_prop
    exact (hfw.differentiableAt.mul hWeight.differentiableAt).differentiableWithinAt
  have hPower (w : ℂ) (hw : w.im ∈ Icc L U) {k : ℝ} (hk : 0 ≤ k) :
      |w.im| ^ k ≤ (3 / 2 : ℝ) ^ k * R ^ k := by
    rw [← Real.mul_rpow (by norm_num) hR.le]
    exact Real.rpow_le_rpow (abs_nonneg _) (hHeights hw).2 hk
  have hDamp : R ^ ξ * Real.exp (-(R / 2) ^ 2) ≤ 1 := by
    rw [Real.rpow_def_of_pos hR, ← Real.exp_add, ← Real.exp_zero, Real.exp_le_exp]
    have hlog : Real.log R ≤ R := (Real.log_le_sub_one_of_pos hR).trans (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hlog hξ, mul_nonneg (sub_nonneg.mpr hRξ) hR.le]
  have hFront : ∀ w ∈ frontier (Complex.reProdIm (Ioo u v) (Ioo L U)),
      ‖g w‖ ≤ K * Real.exp ((v - u) ^ 2) := by
    intro w hw
    have hw' := frontier_subset_closure hw
    rw [Complex.closure_reProdIm, closure_Ioo huv.ne, closure_Ioo hLU.ne] at hw'
    obtain ⟨hwRe, hwIm⟩ := Complex.mem_reProdIm.mp hw'
    rw [Complex.frontier_reProdIm, closure_Ioo huv.ne, closure_Ioo hLU.ne, frontier_Ioo huv,
      frontier_Ioo hLU] at hw
    rw [hgNorm]
    refine mul_le_mul ?_ ?_ (by positivity) hK.le
    · apply (div_le_iff₀ (Real.rpow_pos_of_pos hR _)).mpr
      rcases hw with hw | hw
      · have hs : w.im = L ∨ w.im = U := hw.2
        have hsq : (w.im - z.im) ^ 2 = (R / 2) ^ 2 := by
          rcases hs with h | h <;> rw [h] <;> dsimp [L, U] <;> ring
        have hBound := hT₀ w hwRe ((le_max_right _ _).trans
          ((le_max_left _ _).trans (hRT.trans (hHeights hwIm).1)))
        rw [hsq]
        calc
          _ ≤ (C₀ * ((3 / 2 : ℝ) ^ ξ * R ^ ξ)) * Real.exp (-(R / 2) ^ 2) :=
            mul_le_mul_of_nonneg_right (hBound.trans
              (mul_le_mul_of_nonneg_left (hPower w hwIm hξ) hC₀.le)) (by positivity)
          _ = (C₀ * (3 / 2 : ℝ) ^ ξ) * (R ^ ξ * Real.exp (-(R / 2) ^ 2)) := by ring
          _ ≤ K := by
            simpa only [mul_one] using mul_le_mul (le_max_left _ _) hDamp (by positivity) hK.le
          _ ≤ K * R ^ E w.re := le_mul_of_one_le_right hK.le
            (Real.one_le_rpow hR₁ (hE hwRe))
      · have hs : w.re = u ∨ w.re = v := hw.1
        have hExp : Real.exp (-(w.im - z.im) ^ 2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
        have hSide {C k : ℝ} (hC : 0 ≤ C) (hk : 0 ≤ k) (hEk : E w.re = k)
            (hB : ‖f w‖ ≤ C * |w.im| ^ k) (hCK : C * (3 / 2 : ℝ) ^ k ≤ K) :
            ‖f w‖ * Real.exp (-(w.im - z.im) ^ 2) ≤ K * R ^ E w.re := by
          rw [hEk]
          calc
            _ ≤ ‖f w‖ := mul_le_of_le_one_right (norm_nonneg _) hExp
            _ ≤ C * |w.im| ^ k := hB
            _ ≤ C * ((3 / 2 : ℝ) ^ k * R ^ k) :=
              mul_le_mul_of_nonneg_left (hPower w hwIm hk) hC
            _ = (C * (3 / 2 : ℝ) ^ k) * R ^ k := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hCK (by positivity)
        rcases hs with h | h
        · exact hSide hC₁.le hp (h ▸ hAu)
            (hT₁ w h ((le_max_left _ _).trans ((le_max_right _ _).trans
              (hRT.trans (hHeights hwIm).1)))) ((le_max_left _ _).trans (le_max_right _ _))
        · exact hSide hC₂.le hq (h ▸ hAv)
            (hT₂ w h ((le_max_right _ _).trans ((le_max_right _ _).trans
              (hRT.trans (hHeights hwIm).1)))) ((le_max_right _ _).trans (le_max_right _ _))
    · apply Real.exp_le_exp.mpr
      have hwidth : |w.re - z.re| ≤ v - u :=
        abs_le.mpr ⟨by linarith [hwRe.1, hz.2], by linarith [hwRe.2, hz.1]⟩
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hwidth 2
  have hz' : z ∈ closure (Complex.reProdIm (Ioo u v) (Ioo L U)) := by
    rw [Complex.closure_reProdIm, closure_Ioo huv.ne, closure_Ioo hLU.ne]
    exact ⟨hz, ⟨by dsimp [L]; linarith, by dsimp [U]; linarith⟩⟩
  have hMax := Complex.norm_le_of_forall_mem_frontier_norm_le
    ((Metric.isBounded_Ioo _ _).reProdIm (Metric.isBounded_Ioo _ _)) hg hFront hz'
  rw [hgNorm, sub_self, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), neg_zero,
    Real.exp_zero, mul_one, mul_one, div_le_iff₀ (Real.rpow_pos_of_pos hR _)] at hMax
  exact hMax

include hf hFinite hSimple hGrowth

/-- Paper: Lemma B.1.1.1, p. 589. On each closed strip inside the half-plane,
the growth order at the real part plus any positive ε gives a uniform exponent. -/
theorem isBigO_verticalGrowthOrder_add (σ₁ σ₂ : ℝ) (h₁ : a < σ₁) (h₂ : σ₁ < σ₂)
    (ε : ℝ) (hε : 0 < ε) :
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc σ₁ σ₂)]
      fun s ↦ |s.im| ^ ((verticalGrowthOrder f s.re).toReal + ε) := by
  classical
  let μ : ℝ → ℝ := fun x ↦ (verticalGrowthOrder f x).toReal
  have hμ₀ (x : ℝ) : 0 ≤ μ x := ENNReal.toReal_nonneg
  have hμFinite {x : ℝ} (hx : a < x) : verticalGrowthOrder f x ≠ ⊤ :=
    verticalGrowthOrder_ne_top hf hFinite hSimple hGrowth hx
  have hAnalytic : ∃ T : ℝ, ∀ z : ℂ, a < z.re → T ≤ |z.im| → AnalyticAt ℂ f z := by
    obtain ⟨T, hT⟩ := (hFinite.image (fun z ↦ |z.im|)).bddAbove
    refine ⟨T + 1, fun z hz hHeight ↦
      (hf hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_⟩
    by_contra! hPole
    have := hT ⟨z, ⟨hz, hPole⟩, rfl⟩
    linarith
  obtain ⟨ξ, hξ, hξBound⟩ := hGrowth
  have hLine {x k : ℝ} (hx : a < x) (hk : μ x < k) :
      f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {x})] fun z ↦ |z.im| ^ k := by
    let k' : ℝ≥0 := ⟨k, (lt_of_le_of_lt (hμ₀ x) hk).le⟩
    have hk' : verticalGrowthOrder f x < (k' : ℝ≥0∞) :=
      (ENNReal.toReal_lt_toReal (hμFinite hx) ENNReal.coe_ne_top).mp hk
    rw [verticalGrowthOrder, sInf_lt_iff] at hk'
    obtain ⟨_, ⟨j, hj, rfl⟩, hjk⟩ := hk'
    have hjk' : (j : ℝ) ≤ k := by
      change (j : ℝ) ≤ (k' : ℝ)
      exact NNReal.coe_le_coe.mpr (by simpa only [ENNReal.coe_le_coe] using hjk.le)
    obtain ⟨C, hC, T, hT⟩ := (isBigO_height_iff (p := fun _ ↦ (j : ℝ))).mp hj
    refine (isBigO_height_iff (p := fun _ ↦ k)).mpr
      ⟨C, hC, max T 1, fun z hz hHeight ↦ (hT z hz ((le_max_left _ _).trans hHeight)).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ((le_max_right _ _).trans hHeight) hjk') hC.le
  have hInterp {u v δ : ℝ} (hu : a < u) (huv : u < v) (hδ : 0 < δ) :
      f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc u v)]
        fun z ↦ |z.im| ^ ((1 - (z.re - u) / (v - u)) * (μ u + δ) +
          (z.re - u) / (v - u) * (μ v + δ)) := by
    obtain ⟨T, hT⟩ := hAnalytic
    refine isBigO_height_affine huv hξ.le (by linarith [hμ₀ u]) (by linarith [hμ₀ v])
      ⟨T, fun z hz ↦ hT z (hu.trans_le hz.1)⟩ (hξBound.mono ?_)
      (hLine hu (lt_add_of_pos_right _ hδ)) (hLine (hu.trans huv) (lt_add_of_pos_right _ hδ))
    exact inf_le_inf_left _ (principal_mono.mpr (preimage_mono fun _ hx ↦ hu.trans_le hx.1))
  -- Restrict the strip estimate to a single line and let the exponent slack tend to zero.
  have hChord {u v α β : ℝ} (hu : a < u) (huv : u < v) (hα : 0 < α) (hβ : 0 < β)
      (hab : α + β = 1) : μ (α * u + β * v) ≤ α * μ u + β * μ v := by
    let x := α * u + β * v
    have hx : x ∈ Icc u v := (convex_Icc u v) (left_mem_Icc.mpr huv.le)
      (right_mem_Icc.mpr huv.le) hα.le hβ.le hab
    have hθ : (x - u) / (v - u) = β := by
      apply (div_eq_iff (sub_ne_zero.mpr huv.ne')).mpr
      dsimp [x]
      linear_combination u * hab
    apply le_of_forall_pos_le_add
    intro δ hδ
    let k : ℝ≥0 := ⟨α * μ u + β * μ v + δ, by positivity⟩
    have hBound : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {x})] fun z ↦ |z.im| ^ (k : ℝ) := by
      have hSub : ({x} : Set ℝ) ⊆ Icc u v := singleton_subset_iff.mpr hx
      have hb := (hInterp hu huv hδ).mono
        (inf_le_inf_left _ (principal_mono.mpr (preimage_mono hSub)))
      refine hb.congr' Filter.EventuallyEq.rfl (eventually_inf_principal.mpr ?_)
      refine Eventually.of_forall fun z hz ↦ ?_
      have hz' : z.re = x := hz
      simp only [hz', hθ]
      congr 1
      change _ = α * μ u + β * μ v + δ
      have hα' : 1 - β = α := by linarith
      rw [hα']
      have hδsum : (α + β) * δ = δ := by rw [hab, one_mul]
      linear_combination hδsum
    exact (ENNReal.toReal_le_toReal (hμFinite (hu.trans_le hx.1)) ENNReal.coe_ne_top).mpr
      (sInf_le ⟨k, hBound, rfl⟩)
  have hConvex : ConvexOn ℝ (Ioi a) μ := by
    refine convexOn_iff_pairwise_pos.mpr ⟨convex_Ioi _, ?_⟩
    intro u hu v hv huv α β hα hβ hab
    simp only [smul_eq_mul]
    rcases lt_or_gt_of_ne huv with h | h
    · exact hChord hu h hα hβ hab
    · simpa only [add_comm] using hChord hv h hβ hα (by rwa [add_comm])
  have hCont := hConvex.continuousOn isOpen_Ioi
  -- On a small interval, both endpoint orders are close to the order at any interior point.
  let S := Icc σ₁ σ₂
  have hLocal (x : S) : ∃ r > 0, ∃ C > 0, ∃ T : ℝ, ∀ z : ℂ,
      z.re ∈ Metric.ball (x : ℝ) r → T ≤ |z.im| →
        ‖f z‖ ≤ C * |z.im| ^ (μ z.re + ε) := by
    have hx : a < (x : ℝ) := h₁.trans_le x.property.1
    have hAt := (hCont (x : ℝ) hx).continuousAt (Ioi_mem_nhds hx)
    obtain ⟨d, hd, hNear⟩ := Metric.continuousAt_iff.mp hAt (ε / 4) (by positivity)
    let r := min (d / 2) (((x : ℝ) - a) / 2)
    have hr : 0 < r := lt_min (by positivity) (by linarith)
    let u := (x : ℝ) - r
    let v := (x : ℝ) + r
    have hu : a < u := by
      have := min_le_right (d / 2) (((x : ℝ) - a) / 2)
      dsimp [u]
      linarith
    have huv : u < v := by dsimp [u, v]; linarith
    have hNear' {y : ℝ} (hy : y ∈ Icc u v) : |μ y - μ (x : ℝ)| < ε / 4 := by
      apply hNear
      rw [Real.dist_eq]
      have hDy : |y - (x : ℝ)| ≤ r := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
      exact hDy.trans_lt ((min_le_left _ _).trans_lt (by linarith))
    obtain ⟨C, hC, T, hT⟩ := (isBigO_height_iff (p := fun y ↦
      (1 - (y - u) / (v - u)) * (μ u + ε / 4) +
        (y - u) / (v - u) * (μ v + ε / 4))).mp (hInterp hu huv (by positivity))
    refine ⟨r, hr, C, hC, max T 1, fun z hz hHeight ↦ ?_⟩
    have hz' : z.re ∈ Icc u v := Ioo_subset_Icc_self (by rwa [Real.ball_eq_Ioo] at hz)
    have hNearLeft := (abs_lt.mp (hNear' (left_mem_Icc.mpr huv.le))).2
    have hNearRight := (abs_lt.mp (hNear' (right_mem_Icc.mpr huv.le))).2
    have hNearPoint := (abs_lt.mp (hNear' hz')).1
    let t := (z.re - u) / (v - u)
    have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hz'.1) (sub_nonneg.mpr huv.le)
    have ht' : t ≤ 1 := by
      dsimp [t]
      rw [div_le_iff₀ (sub_pos.mpr huv), one_mul]
      exact sub_le_sub_right hz'.2 _
    have hExponent : (1 - t) * (μ u + ε / 4) + t * (μ v + ε / 4) ≤ μ z.re + ε := by
      calc
        _ ≤ (1 - t) * (μ z.re + ε) + t * (μ z.re + ε) := add_le_add
          (mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr ht'))
          (mul_le_mul_of_nonneg_left (by linarith) ht)
        _ = _ := by ring
    exact (hT z hz' ((le_max_left _ _).trans hHeight)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ((le_max_right _ _).trans hHeight) hExponent) hC.le)
  choose r hr C hC T hT using hLocal
  obtain ⟨J, hJ⟩ := (isCompact_Icc (a := σ₁) (b := σ₂)).elim_finite_subcover
    (fun x : S ↦ Metric.ball (x : ℝ) (r x)) (fun _ ↦ Metric.isOpen_ball)
    (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩)
  obtain ⟨C', hC'⟩ := (J.finite_toSet.image C).bddAbove
  obtain ⟨T', hT'⟩ := (J.finite_toSet.image T).bddAbove
  obtain ⟨x₀, hx₀, _⟩ := mem_iUnion₂.mp (hJ (left_mem_Icc.mpr h₂.le))
  refine (isBigO_height_iff (p := fun x ↦ μ x + ε)).mpr
    ⟨C', (hC x₀).trans_le (hC' ⟨x₀, hx₀, rfl⟩), T', fun z hz hHeight ↦ ?_⟩
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp (hJ hz)
  exact (hT x z hzx ((hT' ⟨x, hx, rfl⟩).trans hHeight)).trans
    (mul_le_mul_of_nonneg_right (hC' ⟨x, hx, rfl⟩) (Real.rpow_nonneg (abs_nonneg _) _))

end GrowthOrder

section Hecke

variable {F : Type*} [Field F] [NumberField F]

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

-- TODO(paper-gap): In Lemma B.1.1.2 the exponent must be allowed to depend on
-- the strip. For ζ on each line σ < 0 the growth order is 1/2 - σ.

/-- The finite Dirichlet series is bounded on every closed half-plane strictly to the right of
one. The absolute series at the real endpoint majorizes the series throughout the half-plane. -/
private theorem finiteHeckeL_continuation_boundedOn_right (χ : U[F]) (L : ℂ → ℂ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) {r : ℝ} (hr : 1 < r) :
    ∃ C : ℝ, ∀ s : ℂ, r ≤ s.re → ‖L s‖ ≤ C := by
  let c := (ideleClassNormTwist χ 0).LFunction
  have hsum : Summable (fun n ↦ ‖LSeries.term c (r : ℂ) n‖) :=
    (finiteHeckeL_seriesSummable χ ⟨(r : ℂ), by simpa using hr⟩).norm
  refine ⟨∑' n, ‖LSeries.term c (r : ℂ) n‖, fun s hs ↦ ?_⟩
  have hs' : 1 < s.re := hr.trans_le hs
  rw [show L s = finiteHeckeL χ ⟨s, hs'⟩ from hSeries ⟨s, hs'⟩]
  change ‖∑' n, LSeries.term c s n‖ ≤ _
  have hsSum : Summable (fun n ↦ ‖LSeries.term c s n‖) :=
    (finiteHeckeL_seriesSummable χ ⟨s, hs'⟩).norm
  exact (norm_tsum_le_tsum_norm hsSum).trans
    (hsSum.tsum_le_tsum (LSeries.norm_term_le_of_re_le_re c (by simpa using hs)) hsum)

/-- On any right half-plane the finite continuation has only finitely many poles, all simple.
The completed continuation has this property, and its reciprocal gamma factor is entire. -/
private theorem exists_analyticOnNhd_isTheta_finiteHeckeL_continuation
    (χ : U[F]) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) (a : ℝ) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (Complex.re ⁻¹' Ioi a) ∧
      G =Θ[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioi a)] L := by
  obtain ⟨Λ, hΛ, hΛSeries⟩ := completedHeckeL_exists_continuation χ
  let R (s : ℂ) := (heckeGammaFactor χ s)⁻¹
  let H := Λ * R
  have hR := differentiable_inv_heckeGammaFactor χ
  have hH : MeromorphicOn H univ := fun s hs ↦
    (hΛ hs).meromorphicAt.mul (hR.analyticAt s).meromorphicAt
  have hAgree : ∀ s : halfPlane, (L - H) s = 0 := by
    intro s
    have hne := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans s.property)
    change L s - Λ s * (heckeGammaFactor χ s)⁻¹ = 0
    rw [hSeries s, hΛSeries s, completedHeckeL, finiteHeckeL]
    rw [mul_comm (heckeGammaFactor χ s), mul_assoc, mul_inv_cancel₀ hne, mul_one, sub_self]
  have hAtTwo : meromorphicOrderAt (L - H) (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono fun s hs ↦ hAgree ⟨s, hs⟩
  have hOrd (s : ℂ) :
      meromorphicOrderAt L s = meromorphicOrderAt Λ s + meromorphicOrderAt R s := by
    have ho := (hL.meromorphicOn.sub hH).meromorphicOrderAt_eq_top_of_isPreconnected
      isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) hAtTwo
    have he : L =ᶠ[𝓝[≠] s] H := (meromorphicOrderAt_eq_top_iff.mp ho).mono fun z hz ↦
      sub_eq_zero.mp hz
    rw [meromorphicOrderAt_congr he]
    exact meromorphicOrderAt_mul (hΛ (mem_univ s)).meromorphicAt (hR.analyticAt s).meromorphicAt
  have hCompare (s : ℂ) : meromorphicOrderAt Λ s ≤ meromorphicOrderAt L s := by
    rw [hOrd]
    exact le_add_of_nonneg_right (hR.analyticAt s).meromorphicOrderAt_nonneg
  have hPoles : ∃ S : Set ℂ, S.Finite ∧
      (∀ s ∉ S, AnalyticAt ℂ Λ s) ∧ ∀ s, (-1 : WithTop ℤ) ≤ meromorphicOrderAt Λ s := by
    have hNeg : (-1 : WithTop ℤ) ≤ 0 := by decide
    by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
    · obtain ⟨t, ⟨_, hp, hq, ha⟩, _⟩ :=
        completedHeckeL_continuation_simplePoles χ Λ hΛ hΛSeries hχ
      refine ⟨_, (finite_singleton (1 + Complex.I * (t : ℂ))).insert _, ha, fun s ↦ ?_⟩
      by_cases h : s = Complex.I * (t : ℂ)
      · rw [h, hp]
      by_cases h' : s = 1 + Complex.I * (t : ℂ)
      · rw [h', hq]
      exact hNeg.trans (ha s (by simp [h, h'])).meromorphicOrderAt_nonneg
    · have h := completedHeckeL_continuation_entire χ Λ hΛ hΛSeries hχ
      exact ⟨∅, finite_empty, fun s _ ↦ h.analyticAt s, fun s ↦
        hNeg.trans (h.analyticAt s).meromorphicOrderAt_nonneg⟩
  obtain ⟨S, hS, hAway, hLower⟩ := hPoles
  apply exists_analyticOnNhd_isTheta_atHeight (fun {_} _ ↦ hL (mem_univ _))
  · refine hS.subset fun s hs ↦ ?_
    by_contra h
    exact (not_lt_of_ge ((hAway s h).meromorphicOrderAt_nonneg.trans (hCompare s))) hs.2
  · intro s _ hs
    have hBound := (hLower s).trans (hCompare s)
    generalize meromorphicOrderAt L s = m at hs hBound ⊢
    cases m with
    | top => simp at hs
    | coe m =>
      have hm₁ : (-1 : ℤ) ≤ m := WithTop.coe_le_coe.mp hBound
      have hm₂ : m < (0 : ℤ) := WithTop.coe_lt_coe.mp hs
      have hm : m = -1 := by omega
      simp [hm]

/-- A preliminary exponential bound for the finite continuation on a fixed strip.
Tate's split zeta integral gives boundedness of the completed function at large height, and
reciprocal gamma factors cost at most an exponential in the absolute height. -/
theorem finiteHeckeL_continuation_isBigO_exp (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (a b : ℝ) (hab : a < b) :
    ∃ B : ℝ, 0 < B ∧ L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)]
      fun s ↦ Real.exp (B * |s.im|) := by
  sorry

/-- Paper: Equations (B.1.1.9)–(B.1.1.11), p. 590. On each negative half-integer line,
the explicit functional equation bounds the finite continuation by a power of the height.
The conductor factor has constant norm on that line, and the reflected series is absolutely
convergent. After conjugation the two gamma arguments differ by `k + 1` at real places and
`2 * (k + 1)` at complex places, so their quotients reduce in norm to finite products. -/
theorem finiteHeckeL_continuation_isBigO_pow_on_neg_halfInteger_line
    (χ : U[F]) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) (k : ℕ) :
    ∃ n : ℕ, 0 < n ∧ L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {-(k : ℝ) - 1 / 2})]
      fun s ↦ |s.im| ^ n := by
  sorry

/-- Paper: Lemma B.1.1.2, p. 590. The finite L-function of a unitary Hecke
character grows at most polynomially on each fixed closed vertical strip.
Deviation: `M` is chosen after the strip endpoints, as required even for ζ. -/
theorem finiteHeckeL_continuation_isBigO_rpow (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (a b : ℝ) (hab : a < b) :
    ∃ M : ℝ, 0 < M ∧ L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun s ↦ |s.im| ^ M := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-a)
  let l : ℝ := -(k : ℝ) - 1 / 2
  let u : ℝ := max b 2
  have hl : l ≤ a := by dsimp [l]; linarith
  have hu : b ≤ u := le_max_left _ _
  have hlu := hl.trans_lt (hab.trans_le hu)
  let strip (S : Set ℝ) := atHeight ⊓ 𝓟 (Complex.re ⁻¹' S)
  have hFilter {S₁ S₂ : Set ℝ} (h : S₁ ⊆ S₂) : strip S₁ ≤ strip S₂ :=
    inf_le_inf_left _ (principal_mono.mpr (preimage_mono h))
  have hHeight {S : Set ℝ} : Tendsto (fun s : ℂ ↦ |s.im|) (strip S) atTop :=
    tendsto_inf_left tendsto_comap
  obtain ⟨G, hG, hGL⟩ := exists_analyticOnNhd_isTheta_finiteHeckeL_continuation χ L hL hSeries (l - 1)
  have hSub : Icc l u ⊆ Ioi (l - 1) := fun _ hs ↦
    (sub_lt_self l zero_lt_one).trans_le hs.1
  have hStrip := hFilter hSub
  have hLeftFilter : strip {l} ≤ strip (Ioi (l - 1)) :=
    hFilter (singleton_subset_iff.mpr (sub_lt_self l zero_lt_one))
  have hRightFilter : strip {u} ≤ strip (Ioi (l - 1)) :=
    hFilter (singleton_subset_iff.mpr ((sub_lt_self l zero_lt_one).trans hlu))
  obtain ⟨n, hn, hLeft⟩ := finiteHeckeL_continuation_isBigO_pow_on_neg_halfInteger_line χ L hL hSeries k
  have hLeftG : G =O[strip {l}] fun s ↦ |s.im| ^ n :=
    (hGL.isBigO.mono hLeftFilter).trans hLeft
  obtain ⟨C, hC⟩ := finiteHeckeL_continuation_boundedOn_right χ L hSeries
    (r := u) (one_lt_two.trans_le (le_max_right _ _))
  have hRightG : G =O[strip {u}] fun s ↦ |s.im| ^ n := by
    apply (hGL.isBigO.mono hRightFilter).trans
    refine Asymptotics.IsBigO.of_bound (max C 0) ?_
    have hLine : ∀ᶠ s in strip {u}, s.re = u :=
      eventually_inf_principal.mpr (Eventually.of_forall fun _ hs ↦ hs)
    filter_upwards [hLine, hHeight.eventually_ge_atTop (1 : ℝ)] with s hs ht
    rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact ((hC s hs.ge).trans (le_max_left _ _)).trans
      (le_mul_of_one_le_right (le_max_right _ _) (one_le_pow₀ ht))
  obtain ⟨B, _, hExp⟩ := finiteHeckeL_continuation_isBigO_exp χ L hL hSeries l u hlu
  have hGPoly := isBigO_pow_verticalStrip_of_exp hlu
    (hG.differentiableOn.mono (preimage_mono hSub))
    ((hGL.isBigO.mono hStrip).trans hExp) hLeftG hRightG
  refine ⟨(n : ℝ), by exact_mod_cast hn, ?_⟩
  simpa only [Real.rpow_natCast] using ((hGL.symm.isBigO.mono hStrip).trans hGPoly).mono
    (hFilter (Icc_subset_Icc hl hu))

/-- Paper: Equation (B.1.1.11), p. 590. The finite functional equation has a
multiplier given by the archimedean gamma ratio and a nonzero constant times a
real-scale exponential. Deviation: The conductor and phase are absorbed into
the real exponent coefficient and the nonzero constant. -/
private theorem finiteHeckeL_functionalEquation_conductorScale (χ : U[F]) (L Ldual : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hDualSeries : ∀ s : halfPlane, Ldual s = finiteHeckeL χ⁻¹ s) :
    ∃ (c : ℂ) (r : ℝ), c ≠ 0 ∧
      L =ᶠ[codiscreteWithin univ] fun s ↦
        (c * Complex.exp ((r : ℂ) * s) *
          toMeromorphicNFOn (fun z ↦ heckeGammaFactor χ⁻¹ (1 - z) / heckeGammaFactor χ z)
            univ s) * Ldual (1 - s) := by
  sorry

/-- Paper: Equations (B.1.1.7)–(B.1.1.11), p. 590. Uniform Stirling estimates
at the real and complex places bound the normal form of the archimedean gamma
ratio by the height to the power `[F : ℚ] * (1 / 2 - Re(s))`. -/
private theorem heckeGammaRatio_isBigO_on_strip (χ : U[F]) (a b : ℝ) (hab : a < b) :
    toMeromorphicNFOn (fun z ↦ heckeGammaFactor χ⁻¹ (1 - z) / heckeGammaFactor χ z) univ
      =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)]
        fun s ↦ |s.im| ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) := by
  sorry

/-- A finite Hecke continuation is nonzero somewhere because its Dirichlet
series tends to its first coefficient, one, along the positive real axis. -/
private theorem finiteHeckeL_continuation_exists_ne_zero (χ : U[F]) (L : ℂ → ℂ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) : ∃ s, L s ≠ 0 := by
  let ψ := ideleClassNormTwist χ 0
  have hCoeff : ψ.LFunction 1 = 1 := by
    have hLocal (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : ψ.localEulerFactor v 1 = 1 := by
      simp [NumberField.HeckeCharacter.localEulerFactor, NumberField.HeckeCharacter.localPowerSeries,
        ArithmeticFunction.ofPowerSeries_apply_one, PowerSeries.constantCoeff_invOfUnit]
    obtain ⟨S, hS⟩ := (heckeLocalEulerFactor_eventually_prod_eq ψ 1).exists
    rw [← hS]
    clear hS
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | insert v S hv ih =>
        rw [Finset.prod_insert hv, ArithmeticFunction.mul_apply_one, hLocal, ih, one_mul]
  have hAbscissa : LSeries.abscissaOfAbsConv ψ.LFunction < ⊤ :=
    (finiteHeckeL_seriesSummable χ ⟨2, by change 1 < (2 : ℂ).re; norm_num⟩).abscissaOfAbsConv_le.trans_lt
      (EReal.coe_lt_top _)
  have hLimit : Tendsto (fun t : ℝ ↦ L (t : ℂ)) atTop (𝓝 1) := by
    rw [← hCoeff]
    apply (LSeries.tendsto_atTop hAbscissa).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    exact (hSeries ⟨(t : ℂ), by change 1 < (t : ℂ).re; simpa using ht⟩).symm
  by_contra! h
  exact one_ne_zero (tendsto_nhds_unique_of_eventuallyEq hLimit tendsto_const_nhds
    (Eventually.of_forall fun t ↦ h (t : ℂ)))

/-- Paper: Equation (B.1.1.10), p. 590. The reflection factor in the functional
equation satisfies the stated power bound on every fixed closed vertical strip. -/
theorem finiteHeckeReflectionFactor_isBigO_on_strip (χ : U[F]) (L Ldual ε : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hDualSeries : ∀ s : halfPlane, Ldual s = finiteHeckeL χ⁻¹ s)
    (hε : Differentiable ℂ ε) (hεNe : ∀ s, ε s ≠ 0)
    (hEq : L =ᶠ[codiscreteWithin univ]
      (fun s ↦ finiteHeckeReflectionFactor χ ε s * Ldual (1 - s)))
    (a b : ℝ) (hab : a < b) :
    finiteHeckeReflectionFactor χ ε =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)]
      fun s ↦ |s.im| ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) := by
  -- The functional equation determines the multiplier in meromorphic normal form.
  clear hε hεNe
  let G := toMeromorphicNFOn
    (fun z ↦ heckeGammaFactor χ⁻¹ (1 - z) / heckeGammaFactor χ z) univ
  obtain ⟨c, r, hc, hExplicit⟩ :=
    finiteHeckeL_functionalEquation_conductorScale χ L Ldual hL hSeries hLdual hDualSeries
  let E (s : ℂ) := c * Complex.exp ((r : ℂ) * s)
  let D (s : ℂ) := Ldual (1 - s)
  have hD : MeromorphicOn D univ := fun s _ ↦
    (hLdual (mem_univ (1 - s))).meromorphicAt.comp_analyticAt
      (analyticAt_const.sub analyticAt_id)
  obtain ⟨s₀, hs₀⟩ := finiteHeckeL_continuation_exists_ne_zero χ⁻¹ Ldual hDualSeries
  have hD₀ : meromorphicOrderAt D (1 - s₀) ≠ ⊤ := by
    have hL₀ : AnalyticAt ℂ Ldual s₀ := by
      rcases meromorphicNFAt_iff_analyticAt_or.mp (hLdual (mem_univ s₀)) with h | ⟨_, h⟩
      · exact h
      · exact (hs₀ h.2).elim
    have h : AnalyticAt ℂ D (1 - s₀) :=
      hL₀.comp_of_eq (analyticAt_const.sub analyticAt_id) (sub_sub_cancel 1 s₀)
    rw [h.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (by simpa [D] using hs₀)]
    exact WithTop.zero_ne_top
  have hDne := hD.eventually_codiscreteWithin_apply_ne_zero fun s hs ↦
    hD.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ _) hs hD₀
  have hAgree : finiteHeckeReflectionFactor χ ε =ᶠ[codiscreteWithin univ] E * G := by
    filter_upwards [hEq, hExplicit, hDne] with s hs ht hsne
    exact mul_right_cancel₀ hsne (hs.symm.trans ht)
  have hE : Differentiable ℂ E := by
    dsimp [E]
    fun_prop
  have hEG : MeromorphicNFOn (E * G) univ :=
    (meromorphicNFOn_mul_iff_right_of_analyticOnNhd (fun s _ ↦ hE.analyticAt s)
      (fun s _ ↦ mul_ne_zero hc (Complex.exp_ne_zero _))).mpr (meromorphicNFOn_toMeromorphicNFOn _ _)
  have hW : MeromorphicNFOn (finiteHeckeReflectionFactor χ ε) univ :=
    meromorphicNFOn_toMeromorphicNFOn _ _
  have hEqW : finiteHeckeReflectionFactor χ ε = E * G := by
    funext s
    have hs := (eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hAgree) s (mem_univ s)
    exact (((hW (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      (hEG (mem_univ s))).mp (hs.mono fun z hz ↦ hz (mem_univ z))).eq_of_nhds
  have hBound : E =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun _ ↦ (1 : ℝ) := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
      (f := fun x ↦ ‖c‖ * Real.exp (r * x)) (by fun_prop)
    refine Asymptotics.IsBigO.of_bound C (eventually_inf_principal.mpr (Eventually.of_forall ?_))
    intro s hs
    simpa [E, norm_mul, Complex.norm_exp, Complex.mul_re,
      Real.norm_of_nonneg (by positivity : 0 ≤ ‖c‖ * Real.exp (r * s.re))] using hC s.re hs
  rw [hEqW]
  change (fun s ↦ E s * G s) =O[_] _
  simpa only [one_mul] using hBound.mul (heckeGammaRatio_isBigO_on_strip χ a b hab)

-- TODO(paper-gap): After (B.1.1.11), the displayed multiplier is called entire
-- and zero-free. For F = ℚ and χ trivial, its gamma quotient has a pole at 1
-- and a zero at 0. The explicit conductor normalization also needs an ideal conductor API.

/-- On a line to the left of zero, the reflected Dirichlet series is bounded,
so the reflection factor determines the power of the height in the upper bound. -/
private theorem finiteHeckeL_isBigO_on_left_line (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    {u : ℝ} (hu : u < 0) :
    L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {u})]
      fun s ↦ |s.im| ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - u)) := by
  obtain ⟨Ldual, hDual, hDualSeries⟩ := finiteHeckeL_exists_continuation χ⁻¹
  obtain ⟨ε, hε, hεNe, hEq⟩ :=
    finiteHeckeL_continuation_functionalEquation χ L Ldual hL hSeries hDual hDualSeries
  have hUpper : u < u / 2 := by linarith
  let p (x : ℝ) := (Module.finrank ℚ F : ℝ) * (1 / 2 - x)
  obtain ⟨C, hC, T, hT⟩ := (isBigO_height_iff (p := p)).mp
    (finiteHeckeReflectionFactor_isBigO_on_strip χ L Ldual ε hL hSeries hDual hDualSeries
      hε hεNe hEq (u - 1) (u / 2) (by linarith))
  obtain ⟨D, hD⟩ := finiteHeckeL_continuation_boundedOn_right χ⁻¹ Ldual hDualSeries
    (r := 1 - u / 2) (by linarith)
  refine (isBigO_height_iff (p := fun _ ↦ p u)).mpr
    ⟨C * max D 1, by positivity, max T 0 + 1, fun s hs ht ↦ ?_⟩
  change s.re = u at hs
  let B (z : ℂ) := C * max D 1 * |z.im| ^ p z.re
  suffices h : ‖L s‖ ≤ B s by simpa [B, hs] using h
  -- The functional equation holds on a punctured neighborhood, so take limits at regular points.
  rcases meromorphicNFAt_iff_analyticAt_or.mp (hL (mem_univ s)) with hAnalytic | ⟨_, _, hZero⟩
  · have hB : ContinuousAt B s := by
      refine continuousAt_const.mul (ContinuousAt.rpow
        Complex.continuous_im.continuousAt.abs ?_ (Or.inl ?_))
      · dsimp [p]
        fun_prop
      · exact (show 0 < |s.im| by linarith [le_max_right T 0]).ne'
    apply le_of_tendsto_of_tendsto (b := 𝓝[≠] s)
      (hAnalytic.continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds)
      (hB.tendsto.mono_left nhdsWithin_le_nhds)
    have hre : ∀ᶠ z : ℂ in 𝓝 s, z.re ∈ Ioo (u - 1) (u / 2) :=
      Complex.continuous_re.continuousAt (Ioo_mem_nhds (by rw [hs]; linarith) (by rwa [hs]))
    have him : ∀ᶠ z : ℂ in 𝓝 s, T < |z.im| :=
      Complex.continuous_im.continuousAt.abs (Ioi_mem_nhds (by linarith [le_max_left T 0]))
    filter_upwards [hEq.filter_mono (nhdsNE_le_codiscrete s),
      hre.filter_mono nhdsWithin_le_nhds, him.filter_mono nhdsWithin_le_nhds] with z hz hzr hzi
    have hReflected : 1 - u / 2 ≤ (1 - z).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith [hzr.2]
    rw [hz, norm_mul]
    calc
      _ ≤ (C * |z.im| ^ p z.re) * max D 1 :=
        mul_le_mul (hT z (Ioo_subset_Icc_self hzr) hzi.le)
          ((hD _ hReflected).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
      _ = B z := by dsimp [B]; ring
  · rw [hZero, norm_zero]
    dsimp [B]
    positivity

/-- Paper: Proposition B.1.1.3, p. 591. On the closed critical strip the
convexity bound has a common constant for all positive ε and all real parts.
The height from which the estimate holds may depend on ε. -/
theorem finiteHeckeL_continuation_convexity_bound (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε > (0 : ℝ),
      Asymptotics.IsBigOWith C (atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc (0 : ℝ) 1)) L
        (fun s ↦ |s.im| ^ ((Module.finrank ℚ F : ℝ) * ((1 - s.re) / 2) + ε)) := by
  refine ⟨1, zero_lt_one, fun ε hε ↦ ?_⟩
  let d : ℝ := Module.finrank ℚ F
  have hd : 0 ≤ d := Nat.cast_nonneg _
  let δ := ε / (d + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hdδ : d * δ ≤ ε := by
    have h := (eq_div_iff (show d + 1 ≠ 0 by positivity)).mp (rfl : δ = ε / (d + 1))
    nlinarith
  let u := -δ
  let v := 1 + δ
  have hu : u < 0 := neg_lt_zero.mpr hδ
  have hv : 1 < v := lt_add_of_pos_right _ hδ
  have huv : u < v := hu.trans (zero_lt_one.trans hv)
  let heightIn (S : Set ℝ) := atHeight ⊓ 𝓟 (Complex.re ⁻¹' S)
  have hFilter {S S' : Set ℝ} (h : S ⊆ S') : heightIn S ≤ heightIn S' :=
    inf_le_inf_left _ (principal_mono.mpr (preimage_mono h))
  obtain ⟨G, hG, hGL⟩ :=
    exists_analyticOnNhd_isTheta_finiteHeckeL_continuation χ L hL hSeries (u - 1)
  have hSub : Icc u v ⊆ Ioi (u - 1) := fun _ hs ↦
    (sub_lt_self u zero_lt_one).trans_le hs.1
  have hLeft := finiteHeckeL_isBigO_on_left_line χ L hL hSeries hu
  obtain ⟨D, hD⟩ := finiteHeckeL_continuation_boundedOn_right χ L hSeries hv
  have hRight : L =O[heightIn {v}] fun s ↦ |s.im| ^ (0 : ℝ) := by
    refine (isBigO_height_iff (p := fun _ ↦ 0)).mpr
      ⟨max D 1, by positivity, 0, fun s hs _ ↦ ?_⟩
    simpa only [Real.rpow_zero, mul_one] using
      (hD s (le_of_eq (mem_singleton_iff.mp hs).symm)).trans (le_max_left D 1)
  obtain ⟨M, hM, hPoly⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries u v huv
  have hθ := hGL.mono (hFilter hSub)
  have hInterp := isBigO_height_affine (f := G) (p := d * (1 / 2 - u)) (q := 0) huv
    hM.le (mul_nonneg hd (by linarith)) le_rfl
    ⟨0, fun s hs _ ↦ hG s (hSub hs)⟩ (hθ.isBigO.trans hPoly)
    ((hθ.isBigO.mono (hFilter (singleton_subset_iff.mpr (left_mem_Icc.mpr huv.le)))).trans hLeft)
    ((hθ.isBigO.mono (hFilter (singleton_subset_iff.mpr (right_mem_Icc.mpr huv.le)))).trans hRight)
  have hExponent (x : ℝ) :
      (1 - (x - u) / (v - u)) * (d * (1 / 2 - u)) + (x - u) / (v - u) * 0 =
        d * ((1 + δ - x) / 2) := by
    have hWidth : v - u = 2 * (1 / 2 - u) := by dsimp [u, v]; ring
    field_simp [sub_ne_zero.mpr huv.ne']
    rw [hWidth]
    ring
  simp only [hExponent] at hInterp
  have hBound := (hθ.symm.isBigO.trans hInterp).mono (hFilter (Icc_subset_Icc hu.le hv.le))
  obtain ⟨C, _, hC⟩ := Asymptotics.isBigO_iff'.mp hBound
  have hHeight : Tendsto (fun z : ℂ ↦ |z.im|) (heightIn (Icc 0 1)) atTop :=
    tendsto_inf_left tendsto_comap
  -- The remaining ε / 2 absorbs the interpolation constant at sufficiently large height.
  apply Asymptotics.IsBigOWith.of_bound
  filter_upwards [hC, hHeight.eventually_ge_atTop 1,
    ((tendsto_rpow_atTop (show 0 < ε / 2 by positivity)).comp hHeight).eventually_ge_atTop C]
    with s hs ht hLarge
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at hs ⊢
  rw [one_mul]
  calc
    ‖L s‖ ≤ C * |s.im| ^ (d * ((1 + δ - s.re) / 2)) := hs
    _ ≤ |s.im| ^ (d * ((1 + δ - s.re) / 2)) * |s.im| ^ (ε / 2) := by
      rw [mul_comm C]
      exact mul_le_mul_of_nonneg_left hLarge (Real.rpow_nonneg (abs_nonneg _) _)
    _ ≤ _ := by
      rw [← Real.rpow_add (zero_lt_one.trans_le ht)]
      apply Real.rpow_le_rpow_of_exponent_le ht
      change d * ((1 + δ - s.re) / 2) + ε / 2 ≤ d * ((1 - s.re) / 2) + ε
      linarith only [hdδ]

-- TODO(paper-gap): Footnote 2 asks for a bound on [-1, 2] without specifying
-- an exponent there. The exponent in (B.1.1.12) fails at σ = -1 even for ζ.
-- TODO(paper-gap): The bound on the dual L-factor gives an upper bound by
-- the reflection factor on fixed left-hand lines. The printed asymptotic
-- equivalence would require the dual L-factor to tend to one in absolute value.
-- TODO(paper-gap): In (B.1.1.14), the bounds on μ at 0 and 1 give an inequality
-- for the interpolation term. The printed equality needs a separate argument.

/-- Paper: Remark B.1.1.4, p. 591. On each fixed vertical line the continued
finite L-function is eventually holomorphic, and each of its holomorphic
derivatives grows at most polynomially as the absolute height tends to infinity. -/
theorem finiteHeckeL_continuation_iteratedDeriv_isBigO_rpow (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (k : ℕ) (σ : ℝ) :
    ∃ M C : ℝ, 0 < M ∧ 0 < C ∧
      ∀ᶠ s in atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ}),
        AnalyticAt ℂ L s ∧ ‖iteratedDeriv k L s‖ ≤ C * |s.im| ^ M := by sorry

-- TODO(paper-gap): Footnotes 3 and 4 leave the intended uniform derivative
-- bounds on strips open. Proposition 3.3.1.5 is stated on fixed lines with σ > 0.

end Hecke

end RiemannMasullo
