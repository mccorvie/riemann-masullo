module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripSector
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # Compact Laplace tests positive on a discrete subset of a strip

For a set in the open strip `|re z| < B` meeting bounded-height rectangles finitely, one
compact smooth function vanishes at the physical origin, has zero transform at `±B`,
and has strictly positive real transform on the whole set. A power of a normalized
autocorrelation imposes the two polar zeros. Finite differences of translates then
annihilate the low sites in the correction of the physical value.
-/

public noncomputable section

open Complex Filter MeasureTheory Set ContinuousLinearMap
open scoped ContDiff Convolution Topology

namespace RiemannMasullo

/-- A spectral multiplier is realized by a smooth compact profile. -/
private def IsCompactLaplaceTransform (F : ℂ → ℂ) : Prop :=
  ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ ∀ z, bilateralLaplace f z = F z

/-- Multiplication of two realized transforms is realized by physical convolution. -/
private theorem realizes_mul {F G : ℂ → ℂ} (hF : IsCompactLaplaceTransform F)
    (hG : IsCompactLaplaceTransform G) : IsCompactLaplaceTransform (fun z ↦ F z * G z) := by
  obtain ⟨f, hf, hc, hF⟩ := hF
  obtain ⟨g, hg, hd, hG⟩ := hG
  refine ⟨f ⋆[ContinuousLinearMap.mul ℝ ℂ] g,
    hd.contDiff_convolution_right _ hf.continuous.locallyIntegrable hg, hc.convolution _ hd, ?_⟩
  intro z
  rw [bilateralLaplace_convolution f g hf.continuous hc hg.continuous hd, hF, hG]

/-- Each strictly positive power is an iterated convolution of the original profile. -/
private theorem realizes_pow_succ {F : ℂ → ℂ} (hF : IsCompactLaplaceTransform F)
    (n : ℕ) : IsCompactLaplaceTransform (fun z ↦ F z ^ (n+1)) := by
  induction n with
  | zero => simpa using hF
  | succ n ih =>
    simpa only [_root_.pow_succ (F _) (n+1)] using realizes_mul ih hF

/-- The multiplier exp(a z) minus a constant acts by a finite difference of translates. -/
private theorem realizes_shift_sub {F : ℂ → ℂ} (hF : IsCompactLaplaceTransform F)
    (a : ℝ) (c : ℂ) :
    IsCompactLaplaceTransform (fun z ↦ (Complex.exp (z*a)-c)*F z) := by
  obtain ⟨f, hf, hc, hF⟩ := hF
  have hsc : ContDiff ℝ ∞ (fun x : ℝ ↦ f (x-a)) := hf.comp (contDiff_id.sub contDiff_const)
  have hcc : HasCompactSupport (fun x : ℝ ↦ f (x-a)) :=
    hc.comp_homeomorph (Homeomorph.subRight a)
  refine ⟨fun x ↦ f (x-a)-c*f x, hsc.sub (contDiff_const.mul hf), hcc.sub hc.mul_left, ?_⟩
  intro z
  calc
    _ = bilateralLaplace (fun x : ℝ ↦ f (x-a)) z - c*bilateralLaplace f z := bilateralLaplace_sub_const_mul _ f hsc.continuous hcc hf.continuous hc c z
    _ = _ := by rw [bilateralLaplace_translate, hF]; ring

/-- Finite low-ordinate mask made from two translates for each site. -/
private def finiteTranslateMask (S : Finset ℂ) (w : ℂ) : ℂ :=
  ∏ u ∈ S, ((Complex.exp w - Complex.exp u) *
    (Complex.exp (-w) - starRingEnd ℂ (Complex.exp u)))

/-- Every designated site is an exact zero of the finite translate mask. -/
private theorem finiteTranslateMask_eq_zero {S : Finset ℂ} {z : ℂ} (hz : z ∈ S) :
    finiteTranslateMask S z = 0 :=
  Finset.prod_eq_zero hz (by simp)

/-- On the imaginary axis the mask is a product of real nonnegative squared norms. -/
private theorem finiteTranslateMask_axis (S : Finset ℂ) (t : ℝ) :
    finiteTranslateMask S ((t : ℂ)*I) =
      ((∏ u ∈ S, Complex.normSq (Complex.exp ((t : ℂ)*I) - Complex.exp u) : ℝ) : ℂ) := by
  have hconj : Complex.exp (-((t : ℂ)*I)) = starRingEnd ℂ (Complex.exp ((t : ℂ)*I)) := by
    rw [← Complex.exp_conj]
    simp
  have hterm (u : ℂ) :
      (Complex.exp ((t : ℂ)*I)-Complex.exp u) *
        (Complex.exp (-((t : ℂ)*I))-starRingEnd ℂ (Complex.exp u)) =
        (Complex.normSq (Complex.exp ((t : ℂ)*I)-Complex.exp u) : ℂ) := by
    rw [hconj, ← map_sub, Complex.mul_conj]
  simp only [finiteTranslateMask, hterm]
  push_cast
  rfl

/-- A finite exponential mask is bounded uniformly on every full vertical strip. -/
private theorem finiteTranslateMask_bounded (S : Finset ℂ) (B : ℝ) :
    ∃ C > (0 : ℝ), ∀ z : ℂ, |z.re| ≤ B → ‖finiteTranslateMask S z‖ ≤ C := by
  refine ⟨∏ u ∈ S, (Real.exp B + ‖Complex.exp u‖)^2,
    Finset.prod_pos (fun i _ ↦ by positivity), fun z hz ↦ ?_⟩
  simp only [finiteTranslateMask, norm_prod, norm_mul]
  apply Finset.prod_le_prod₀ (fun i _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro u hu
  have hx : ‖Complex.exp z-Complex.exp u‖ ≤ Real.exp B + ‖Complex.exp u‖ := by
    have hnorm : ‖Complex.exp z‖ ≤ Real.exp B := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr (abs_le.mp hz).2
    exact (norm_sub_le _ _).trans (add_le_add_left hnorm _)
  have hy : ‖Complex.exp (-z)-starRingEnd ℂ (Complex.exp u)‖ ≤ Real.exp B + ‖Complex.exp u‖ := by
    apply (norm_sub_le _ _).trans
    rw [Complex.norm_conj, Complex.norm_exp, Complex.neg_re]
    gcongr
    linarith [(abs_le.mp hz).1]
  rw [sq]
  exact mul_le_mul hx hy (norm_nonneg _) (by positivity)

/-- Every right neighborhood of frequency zero contains a closed interval of positive length
on which the mask is strictly positive, even when zero itself is a designated site. -/
private theorem finiteTranslateMask_positive_interval (S : Finset ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < δ ∧
      ∀ t ∈ Set.Icc a b, 0 < (finiteTranslateMask S ((t : ℂ)*I)).re := by
  classical
  let d := min δ Real.pi
  let D := Set.Ioo (0 : ℝ) d
  let E (t : ℝ) := Complex.exp ((t : ℂ)*I)
  have hd : 0 < d := lt_min hδ Real.pi_pos
  have hdπ : d ≤ Real.pi := min_le_right _ _
  have hinj : Set.InjOn E D := by
    intro x hx y hy hxy
    have hx' : 0 < x ∧ x < d := hx
    have hy' : 0 < y ∧ y < d := hy
    have he := Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (x := (x : ℂ)*I) (y := (y : ℂ)*I)
      (by simpa using (show -Real.pi < x by linarith [Real.pi_pos]))
      (by simpa using hx'.2.le.trans hdπ)
      (by simpa using (show -Real.pi < y by linarith [Real.pi_pos]))
      (by simpa using hy'.2.le.trans hdπ) hxy
    simpa using congrArg Complex.im he
  have hinf : (E '' D).Infinite := (Set.infinite_image_iff hinj).mpr (Set.Ioo_infinite hd)
  have hnot : ¬ E '' D ⊆ (↑(S.image Complex.exp) : Set ℂ) :=
    fun h ↦ hinf ((S.image Complex.exp).finite_toSet.subset h)
  obtain ⟨_, ⟨t, ht, rfl⟩, hmiss⟩ := Set.not_subset.mp hnot
  have ht' : 0 < t ∧ t < d := ht
  have hpos : 0 < (finiteTranslateMask S ((t : ℂ)*I)).re := by
    rw [finiteTranslateMask_axis, Complex.ofReal_re]
    apply Finset.prod_pos
    intro u hu
    apply Complex.normSq_pos.mpr
    exact sub_ne_zero.mpr (fun he ↦ hmiss (Finset.mem_image.mpr ⟨u, hu, he.symm⟩))
  have hcont : Continuous (fun x : ℝ ↦ (finiteTranslateMask S ((x : ℂ)*I)).re) := by
    unfold finiteTranslateMask
    fun_prop
  let U := {x : ℝ | 0 < (finiteTranslateMask S ((x : ℂ)*I)).re} ∩ Set.Ioo 0 δ
  have hU : IsOpen U := (isOpen_lt continuous_const hcont).inter isOpen_Ioo
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU t ⟨hpos, ht'.1, ht'.2.trans_le (min_le_left δ Real.pi)⟩
  have hab : t-r/2 < t+r/2 := by linarith
  have hclosed : Set.Icc (t-r/2) (t+r/2) ⊆ U := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  exact ⟨t-r/2, t+r/2, (hclosed (Set.left_mem_Icc.mpr hab.le)).2.1, hab,
    (hclosed (Set.right_mem_Icc.mpr hab.le)).2.2, fun x hx ↦ (hclosed hx).1⟩

/-- The finite mask and every positive convolution power are realized by a genuine test. -/
private theorem realizes_mask {F : ℂ → ℂ} (hF : IsCompactLaplaceTransform F)
    (S : Finset ℂ) : IsCompactLaplaceTransform (fun z ↦ finiteTranslateMask S z * F z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa [finiteTranslateMask] using hF
  | insert u S hu ih =>
    obtain ⟨f, hf, hc, he⟩ := realizes_shift_sub (realizes_shift_sub ih 1 (Complex.exp u)) (-1)
      (starRingEnd ℂ (Complex.exp u))
    refine ⟨f, hf, hc, fun z ↦ ?_⟩
    rw [he]
    simp [finiteTranslateMask, hu, mul_assoc, mul_comm, mul_left_comm]

private theorem polar_exp_moment_eq_cosh {G : ℝ → ℝ} (hg : Continuous G)
    (hc : HasCompactSupport G) (he : ∀ x, G (-x) = G x) (r : ℝ) :
    (∫ x : ℝ, G x * Real.exp (r*x)) = ∫ x : ℝ, G x * Real.cosh (r*x) := by
  let p (s x : ℝ) := G x * Real.exp (s*x)
  have hi (s : ℝ) : Integrable (p s) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  have hneg : (∫ x, p (-r) x) = ∫ x, p r x := by
    conv_rhs => rw [← integral_neg_eq_self (p r) volume]
    apply integral_congr_ae
    filter_upwards with x
    simp [p, he, mul_neg, neg_mul]
  have hsum : (∫ x, p r x) + (∫ x, p (-r) x) = 2 * ∫ x : ℝ, G x * Real.cosh (r*x) := by
    rw [← integral_add (hi _) (hi _), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [p, Real.cosh_eq, neg_mul]
    ring
  rw [hneg] at hsum
  change (∫ x, p r x) = _
  linarith

private theorem polar_norm_le_exp_moment {G : ℝ → ℝ} (hg : Continuous G)
    (hc : HasCompactSupport G) (hn : ∀ x, 0 ≤ G x) (w : ℂ) :
    ‖bilateralLaplace (fun x ↦ (G x : ℂ)) w‖ ≤ ∫ x : ℝ, G x * Real.exp (w.re*x) := by
  apply norm_integral_le_of_norm_le ((hg.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right)
  filter_upwards with x
  simp [Complex.norm_exp, Real.norm_eq_abs, abs_of_nonneg (hn x)]

private theorem polar_real_axis_eq {G : ℝ → ℝ} (hg : Continuous G) (hc : HasCompactSupport G)
    (he : ∀ x, G (-x) = G x) (r : ℝ) :
    bilateralLaplace (fun x ↦ (G x : ℂ)) (r : ℂ) = (∫ x : ℝ, G x * Real.cosh (r*x) : ℝ) := by
  rw [← polar_exp_moment_eq_cosh hg hc he, ← integral_complex_ofReal]
  unfold bilateralLaplace
  apply integral_congr_ae
  filter_upwards with x
  simp


private theorem polar_cosh_moment_strict {G : ℝ → ℝ} (hg : Continuous G)
    (hc : HasCompactSupport G) (hn : ∀ x, 0 ≤ G x)
    (hp : ∃ x₀ : ℝ, x₀ ≠ 0 ∧ 0 < G x₀) {r B : ℝ} (hr : |r| < B) :
    (∫ x : ℝ, G x * Real.cosh (r*x)) < ∫ x : ℝ, G x * Real.cosh (B*x) := by
  let p (s x : ℝ) := G x * Real.cosh (s*x)
  have hcon (s : ℝ) : Continuous (p s) := hg.mul (by fun_prop)
  have hcp (s : ℝ) : HasCompactSupport (p s) := hc.mul_right
  have hint (s : ℝ) : Integrable (p s) := (hcon s).integrable_of_hasCompactSupport (hcp s)
  have hB : 0 < B := (abs_nonneg r).trans_lt hr
  have hm (x : ℝ) : Real.cosh (r*x) ≤ Real.cosh (B*x) := by
    rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos hB]
    exact mul_le_mul_of_nonneg_right hr.le (abs_nonneg _)
  obtain ⟨x₀, hx₀, hg₀⟩ := hp
  have hlt : Real.cosh (r*x₀) < Real.cosh (B*x₀) := by
    rw [Real.cosh_lt_cosh, abs_mul, abs_mul, abs_of_pos hB]
    exact mul_lt_mul_of_pos_right hr (abs_pos.mpr hx₀)
  have hi : 0 < ∫ x, (p B - p r) x := by
    apply ((hcon B).sub (hcon r)).integral_pos_of_hasCompactSupport_nonneg_ne_zero
      ((hcp B).sub (hcp r)) (x := x₀)
    · intro x
      exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left (hm x) (hn x))
    · exact (sub_pos.mpr (mul_lt_mul_of_pos_left hlt hg₀)).ne'
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (hint B) (hint r)] at hi
  exact sub_pos.mp hi

/-- A normalized even nonnegative compact density has a common polar value larger than one,
and a strict modulus bound everywhere in the open strip. -/
private theorem normalized_even_density_polar_values {G : ℝ → ℝ} (hg : Continuous G)
    (hc : HasCompactSupport G) (he : ∀ x, G (-x) = G x) (hn : ∀ x, 0 ≤ G x)
    (hmass : (∫ x : ℝ, G x) = 1) {B : ℝ} (hB : 0 < B) :
    let j := bilateralLaplace (fun x ↦ (G x : ℂ))
    ∃ a : ℝ, 1 < a ∧ j (B : ℂ) = (a : ℂ) ∧ j (-(B : ℂ)) = (a : ℂ) ∧
      (∀ w : ℂ, |w.re| < B → ‖j w‖ < a) := by
  have hp : ∃ x : ℝ, x ≠ 0 ∧ 0 < G x := by
    by_contra! h
    have hzero : G =ᵐ[volume] (0 : ℝ → ℝ) := by
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
      exact le_antisymm (h x hx) (hn x)
    have hmass' := integral_congr_ae hzero
    simp [hmass] at hmass'
  let a := ∫ x : ℝ, G x * Real.cosh (B*x)
  refine ⟨a, ?_, polar_real_axis_eq hg hc he B, ?_, ?_⟩
  · simpa [a, hmass] using polar_cosh_moment_strict hg hc hn hp (r := 0) (by simpa using hB)
  · simpa only [Complex.ofReal_neg, neg_mul, Real.cosh_neg] using polar_real_axis_eq hg hc he (-B)
  · intro w hw
    exact (polar_norm_le_exp_moment hg hc hn w).trans_lt
      ((polar_exp_moment_eq_cosh hg hc he w.re).trans_lt (polar_cosh_moment_strict hg hc hn hp hw))

/-- A finite low-frequency set with strict pointwise inequalities, together
with a uniform high-frequency bound, gives a single strict ratio for all sites. -/
private theorem exists_uniform_polar_ratio {S : Set ℂ} {low : Finset ℂ} {j : ℂ → ℂ} {q jB : ℝ}
    (hq : 0 ≤ q) (hq₁ : q < 1) (hjB : 1 < jB)
    (hlo : ∀ w ∈ low, ‖j w‖ < jB) (hhi : ∀ w ∈ S, w ∉ low → ‖j w‖ ≤ q) :
    ∃ d : ℝ, 0 ≤ d ∧ d < 1 ∧ ∀ w ∈ S, ‖j w / (jB : ℂ)‖ ≤ d := by
  classical
  let V := insert q (low.image fun w ↦ ‖j w‖)
  have hV : V.Nonempty := ⟨q, Finset.mem_insert_self _ _⟩
  let U := V.max' hV
  have hqU : q ≤ U := V.le_max' _ (Finset.mem_insert_self _ _)
  have hUb : U < jB := by
    have hmem : U ∈ insert q (low.image fun w ↦ ‖j w‖) := V.max'_mem hV
    rcases Finset.mem_insert.mp hmem with he | hi
    · exact he ▸ hq₁.trans hjB
    · obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hi
      exact he ▸ hlo w hw
  have hB₀ : 0 < jB := zero_lt_one.trans hjB
  refine ⟨U / jB, div_nonneg (hq.trans hqU) hB₀.le, (div_lt_one hB₀).mpr hUb, ?_⟩
  intro w hw
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hB₀.le]
  apply div_le_div_of_nonneg_right _ hB₀.le
  by_cases hL : w ∈ low
  · exact V.le_max' _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hL))
  · exact (hhi w hw hL).trans hqU

/-- The two polar zeros can be imposed before correcting the physical origin.
A sufficiently high power of the normalized kernel ratio keeps the real part
positive on every site with a uniform new sector constant `4C`. The filtered
transform remains real and strictly positive along the entire imaginary axis. -/
private theorem exists_polar_filter {S : Set ℂ} {k j : ℂ → ℂ} {B jB C d : ℝ}
    {kR jR : ℝ → ℝ}
    (hC : 0 ≤ C) (hd₀ : 0 ≤ d) (hd₁ : d < 1) (hjB : 1 < jB)
    (hplus : j (B : ℂ) = (jB : ℂ)) (hminus : j (-(B : ℂ)) = (jB : ℂ))
    (hpos : ∀ w ∈ S, 0 < (k w).re) (hsector : ∀ w ∈ S, ‖k w‖ ≤ C * (k w).re)
    (hratio : ∀ w ∈ S, ‖j w / (jB : ℂ)‖ ≤ d)
    (hkaxis : ∀ t : ℝ, k ((t : ℂ) * I) = (kR t : ℂ) ∧ 0 < kR t)
    (hjaxis : ∀ t : ℝ, j ((t : ℂ) * I) = (jR t : ℂ) ∧ 0 ≤ jR t ∧ jR t ≤ 1) :
    ∃ m > 0, let W := fun w : ℂ ↦ k w * (1 - (j w / (jB : ℂ)) ^ m)
      W (B : ℂ) = 0 ∧ W (-(B : ℂ)) = 0 ∧
      (∀ w ∈ S, 0 < (W w).re ∧ ‖W w‖ ≤ 4 * C * (W w).re) ∧
      (∀ t : ℝ, 0 < (W ((t : ℂ) * I)).re ∧ W ((t : ℂ) * I) = ((W ((t : ℂ) * I)).re : ℂ)) := by
  have hlimit : Tendsto (fun m : ℕ ↦ C * d ^ m) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hd₀ hd₁).const_mul C
  obtain ⟨m, hm, hsmall⟩ := ((eventually_gt_atTop 0).and
    (hlimit.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2))).exists
  have hB₀ : 0 < jB := zero_lt_one.trans hjB
  have hBne : (jB : ℂ) ≠ 0 := by exact_mod_cast hB₀.ne'
  refine ⟨m, hm, ?_, ?_, ?_, ?_⟩
  · simp [hplus, hBne]
  · simp [hminus, hBne]
  · intro w hw
    let e := (j w / (jB : ℂ)) ^ m
    have hem : ‖e‖ ≤ d ^ m := by
      rw [show ‖e‖ = ‖j w / (jB : ℂ)‖ ^ m from norm_pow _ _]
      exact pow_le_pow_left₀ (norm_nonneg _) (hratio w hw) m
    have he₁ := hem.trans (pow_le_one₀ hd₀ hd₁.le)
    have hehalf : C * ‖e‖ < 1 / 2 := (mul_le_mul_of_nonneg_left hem hC).trans_lt hsmall
    have herr : (k w * e).re ≤ (k w).re / 2 := calc
      _ ≤ ‖k w * e‖ := Complex.re_le_norm _
      _ = ‖k w‖ * ‖e‖ := norm_mul _ _
      _ ≤ (C * (k w).re) * ‖e‖ := mul_le_mul_of_nonneg_right (hsector w hw) (norm_nonneg _)
      _ ≤ _ := by nlinarith only [mul_lt_mul_of_pos_left hehalf (hpos w hw)]
    have hlower : (k w).re / 2 ≤ (k w * (1-e)).re := by
      rw [mul_sub, mul_one, sub_re]
      linarith only [herr]
    refine ⟨by linarith only [hlower, hpos w hw], ?_⟩
    calc
      ‖k w * (1-e)‖ = ‖k w‖ * ‖1-e‖ := norm_mul _ _
      _ ≤ ‖k w‖ * 2 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have := norm_sub_le (1 : ℂ) e
        rw [norm_one] at this
        linarith only [this, he₁]
      _ ≤ (C * (k w).re) * 2 := mul_le_mul_of_nonneg_right (hsector w hw) (by norm_num)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hlower hC]
  · intro t
    let x := jR t / jB
    have hx₀ : 0 ≤ x := div_nonneg (hjaxis t).2.1 hB₀.le
    have hx₁ : x < 1 := (div_lt_one hB₀).mpr ((hjaxis t).2.2.trans_lt hjB)
    have hreal : k ((t : ℂ) * I) * (1 - (j ((t : ℂ) * I) / (jB : ℂ)) ^ m) =
        ((kR t * (1 - x ^ m) : ℝ) : ℂ) := by
      rw [(hkaxis t).1, (hjaxis t).1]
      simp only [x, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
        Complex.ofReal_pow, Complex.ofReal_div]
    change 0 < (k ((t : ℂ) * I) * (1 - (j ((t : ℂ) * I) / (jB : ℂ)) ^ m)).re ∧
      k ((t : ℂ) * I) * (1 - (j ((t : ℂ) * I) / (jB : ℂ)) ^ m) =
        ((k ((t : ℂ) * I) * (1 - (j ((t : ℂ) * I) / (jB : ℂ)) ^ m)).re : ℂ)
    rw [hreal, Complex.ofReal_re]
    exact ⟨mul_pos (hkaxis t).2 (sub_pos.mpr (pow_lt_one₀ hx₀ hx₁ hm.ne')), rfl⟩

/-- A positive interval gives an explicit geometric lower bound for a nonnegative
Fourier integral. The coefficient is the interval length times the lower bound,
times the (positive) Fourier normalization factor. -/
private theorem interval_concentration {u v : ℝ → ℝ} {a b c r τ : ℝ} {n : ℕ}
    (hab : a < b) (hc : 0 ≤ c) (hr : 0 ≤ r) (hτ : 0 ≤ τ)
    (huv : ∀ t, 0 ≤ u t * v t ^ n)
    (hinterval : ∀ t ∈ Icc a b, c ≤ u t ∧ r ≤ v t)
    (hint : Integrable (fun t ↦ u t * v t ^ n)) :
    (τ * c * (b-a)) * r ^ n ≤ τ * ∫ t, u t * v t ^ n := by
  have hbase := setIntegral_ge_of_const_le_real (μ := volume) measurableSet_Icc
    (measure_Icc_lt_top.ne) (c := c * r ^ n)
    (fun t ht ↦ mul_le_mul (hinterval t ht).1 (pow_le_pow_left₀ hr (hinterval t ht).2 n)
      (pow_nonneg hr n) (hc.trans (hinterval t ht).1)) hint.integrableOn
  rw [Real.volume_real_Icc_of_le hab.le] at hbase
  have htotal : (∫ t in Icc a b, u t * v t ^ n) ≤ ∫ t, u t * v t ^ n := by
    simpa only [setIntegral_univ] using setIntegral_mono_set (t := univ)
      hint.integrableOn (.of_forall fun t ↦ huv t) (ae_of_all _ fun _ _ ↦ mem_univ _)
  calc
    _ = τ * (c * r ^ n * (b - a)) := by ring
    _ ≤ τ * ∫ t, u t * v t ^ n := mul_le_mul_of_nonneg_left (hbase.trans htotal) hτ

/-- Multiplying a value in a rightward sector by `1-e` preserves its positive
real part when the sector constant times `‖e‖` is strictly below one. -/
private theorem re_mul_one_sub_pos {z e : ℂ} {C : ℝ}
    (hz : 0 < z.re) (hsector : ‖z‖ ≤ C * z.re) (he : C * ‖e‖ < 1) :
    0 < (z * (1 - e)).re := by
  have hsmall : (z * e).re < z.re := calc
    (z * e).re ≤ ‖z * e‖ := Complex.re_le_norm _
    _ = ‖z‖ * ‖e‖ := norm_mul _ _
    _ ≤ (C * z.re) * ‖e‖ := mul_le_mul_of_nonneg_right hsector (norm_nonneg _)
    _ < z.re := by nlinarith only [mul_lt_mul_of_pos_left he hz]
  rw [mul_sub, mul_one, sub_re]
  linarith

/-- Uniformly over the sites, the normalized correction eventually fits inside
the initial positive sector. A compact interval supplies the `r^n` lower bound
on the normalization; outside the finite exceptional set the multiplier costs
only `q^n`, where `q < r`. -/
private theorem exists_normalized_positive {S : Set ℂ} {low : Finset ℂ} {k P j : ℂ → ℂ}
    {A : ℂ} {d : ℕ → ℂ} {C M c q r : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hc : 0 < c) (hq : 0 ≤ q) (hqr : q < r)
    (hpos : ∀ w ∈ S, 0 < (k w).re) (hsector : ∀ w ∈ S, ‖k w‖ ≤ C * (k w).re)
    (hP : ∀ w ∈ S, ‖P w‖ ≤ M) (hlow : ∀ w ∈ low, P w = 0)
    (hhigh : ∀ w ∈ S, w ∉ low → ‖j w‖ ≤ q)
    (hd : ∀ n > 0, c * r ^ n ≤ ‖d n‖) :
    ∃ n > 0, d n ≠ 0 ∧ ∀ w ∈ S, 0 < (k w * (1 - A / d n * (P w * j w ^ n))).re := by
  have hr : 0 < r := hq.trans_lt hqr
  have hlim : Tendsto (fun n : ℕ ↦ (C * ‖A‖ * M) * (q / r) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg hq hr.le) ((div_lt_one hr).mpr hqr)).const_mul (C * ‖A‖ * M)
  obtain ⟨n, hn, hsmall⟩ := ((eventually_gt_atTop 0).and (hlim.eventually_lt_const hc)).exists
  have hc0 : 0 < c * r ^ n := mul_pos hc (pow_pos hr _)
  have hdn : 0 < ‖d n‖ := hc0.trans_le (hd n hn)
  refine ⟨n, hn, norm_pos_iff.mp hdn, ?_⟩
  intro w hw
  apply re_mul_one_sub_pos (hpos w hw) (hsector w hw)
  have hm : ‖P w * j w ^ n‖ ≤ M * q ^ n := by
    by_cases hL : w ∈ low
    · simp only [hlow w hL, zero_mul, norm_zero]
      positivity
    · rw [norm_mul, norm_pow]
      exact mul_le_mul (hP w hw) (pow_le_pow_left₀ (norm_nonneg _) (hhigh w hw hL) n)
        (by positivity) hM
  have hratio : ‖A‖ / ‖d n‖ ≤ ‖A‖ / (c * r ^ n) :=
    div_le_div_of_nonneg_left (norm_nonneg _) hc0 (hd n hn)
  calc
    C * ‖A / d n * (P w * j w ^ n)‖ = C * ((‖A‖ / ‖d n‖) * ‖P w * j w ^ n‖) := by
      rw [norm_mul, norm_div]
    _ ≤ C * ((‖A‖ / (c * r ^ n)) * (M * q ^ n)) := by gcongr
    _ = ((C * ‖A‖ * M) * (q / r) ^ n) / c := by rw [div_pow]; ring
    _ < 1 := (div_lt_one hc).mpr hsmall

/-- The physical value at zero is real and satisfies an explicit lower bound.
Apply the result to the actual convolution `K ⋆ Jₙ`, whose angular Fourier
transform is `u(t) v(t)^n`. The same interval works for all `n`. -/
private theorem origin_ge_of_axis_interval
    {F : ℝ → ℂ} {u v : ℝ → ℝ} {a b c r : ℝ} {n : ℕ}
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (haxis : ∀ t : ℝ, bilateralLaplace F ((t : ℂ) * I) = ((u t * v t ^ n : ℝ) : ℂ))
    (hUV : ∀ t, 0 ≤ u t * v t ^ n)
    (hab : a < b) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hI : ∀ t ∈ Icc a b, c ≤ u t ∧ r ≤ v t) :
    ((2 * Real.pi)⁻¹ * c * (b-a)) * r ^ n ≤ (F 0).re := by
  have hi := bilateralLaplace_inversion_zero hF hcF
  have hreal : Integrable fun t ↦ u t * v t ^ n := by
    simpa only [haxis, RCLike.re_eq_complex_re, Complex.ofReal_re] using hi.1.re
  have hvalue : F 0 = (((2 * Real.pi)⁻¹ * ∫ t, u t * v t ^ n : ℝ) : ℂ) := by
    rw [hi.2, Complex.ofReal_mul]
    simp_rw [haxis, integral_complex_ofReal]
  rw [hvalue, Complex.ofReal_re]
  exact interval_concentration hab hc hr (by positivity) hUV hI hreal

/-- A concentration interval for the imaginary-axis mass permits exact cancellation
of the physical value while preserving every transform zero of the initial profile. -/
private theorem correct_origin {S : Set ℂ} (low : Finset ℂ) {k j : ℂ → ℂ} {B C : ℝ}
    (hK : IsCompactLaplaceTransform k) (hG : IsCompactLaplaceTransform j)
    (hstrip : ∀ z ∈ S, |z.re| ≤ B) (hC : 0 ≤ C)
    (hsector : ∀ z ∈ S, 0 < (k z).re ∧ ‖k z‖ ≤ C * (k z).re)
    (hkaxis : ∀ t : ℝ, 0 < (k ((t : ℂ) * I)).re ∧ k ((t : ℂ) * I) = ((k ((t : ℂ) * I)).re : ℂ))
    (hjaxis : ∀ t : ℝ, j ((t : ℂ) * I) = ((j ((t : ℂ) * I)).re : ℂ) ∧ 0 ≤ (j ((t : ℂ) * I)).re)
    (hjzero : j 0 = 1) (hhigh : ∀ z ∈ S, z ∉ low → ‖j z‖ ≤ 1/2) :
    ∃ H : ℝ → ℂ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ H 0 = 0 ∧
      (∀ z ∈ S, 0 < (bilateralLaplace H z).re) ∧
      ∀ z, k z = 0 → bilateralLaplace H z = 0 := by
  classical
  obtain ⟨K, hKs, hKc, hKmom⟩ := hK
  obtain ⟨G, hGs, hGc, hGmom⟩ := hG
  have hkc : Continuous k := (funext hKmom) ▸
    (differentiable_bilateralLaplace_of_hasCompactSupport hKs.continuous hKc).continuous
  have hjc : Continuous j := (funext hGmom) ▸
    (differentiable_bilateralLaplace_of_hasCompactSupport hGs.continuous hGc).continuous
  have haxisPhase : Continuous (fun t : ℝ ↦ ((t : ℂ) * I)) := by fun_prop
  let P := finiteTranslateMask low
  obtain ⟨M, hM, hbound⟩ := finiteTranslateMask_bounded low B
  have hpR (t : ℝ) : P ((t : ℂ) * I) = ((P ((t : ℂ) * I)).re : ℂ) ∧ 0 ≤ (P ((t : ℂ) * I)).re := by
    dsimp only [P]
    rw [finiteTranslateMask_axis, Complex.ofReal_re]
    exact ⟨rfl, Finset.prod_nonneg fun u _ ↦ Complex.normSq_nonneg _⟩
  let u (t : ℝ) := (k ((t : ℂ) * I)).re * (P ((t : ℂ) * I)).re
  have hpc : Continuous (fun t : ℝ ↦ (P ((t : ℂ) * I)).re) := by
    change Continuous (fun t : ℝ ↦ (finiteTranslateMask low ((t : ℂ) * I)).re)
    simp_rw [finiteTranslateMask_axis, Complex.ofReal_re]
    fun_prop
  have hu : Continuous u := (Complex.continuous_re.comp (hkc.comp haxisPhase)).mul
    hpc
  have hv : Continuous (fun t : ℝ ↦ (j ((t : ℂ) * I)).re) := Complex.continuous_re.comp (hjc.comp haxisPhase)
  have hj0 : j 0 = 1 := hjzero
  have hjNear := (hv.tendsto 0).eventually_const_lt
    (show (3/4 : ℝ) < (j ((0 : ℂ) * I)).re by simp [hj0]; norm_num)
  obtain ⟨δ,hδ,hsmall⟩ := Metric.eventually_nhds_iff.mp hjNear
  obtain ⟨a,b,ha,hab,hb,hp⟩ := finiteTranslateMask_positive_interval low hδ
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le) hu.continuousOn
  have hI (t : ℝ) (ht : t ∈ Icc a b) : u t₀ ≤ u t ∧ 3/4 ≤ (j ((t : ℂ) * I)).re := by
    refine ⟨hmin ht, (hsmall ?_).le⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (ha.trans_le ht.1)]
    exact ht.2.trans_lt hb
  have hrG : IsCompactLaplaceTransform j := ⟨G, hGs, hGc, hGmom⟩
  have hrK : IsCompactLaplaceTransform k := ⟨K, hKs, hKc, hKmom⟩
  -- Q n realizes k · P · j^(n+1). Every positive power is an ordinary convolution.
  choose Q hQs hQc hQmom using fun n : ℕ ↦
    realizes_mul hrK (realizes_mask (realizes_pow_succ hrG n) low)
  let c := u t₀
  have hc : 0 < c := mul_pos (hkaxis t₀).1 (hp t₀ ht₀)
  let A := (2 * Real.pi)⁻¹ * c * (b-a)
  have hA : 0 < A := mul_pos (mul_pos (by positivity) hc) (sub_pos.mpr hab)
  have hQ (n : ℕ) (hn : 0 < n) (z : ℂ) :
      bilateralLaplace (Q (n-1)) z = k z * (P z * j z^n) := by
    simpa only [Nat.sub_add_cancel hn] using hQmom (n-1) z
  have hnorm (n : ℕ) (hn : 0 < n) : A * (3/4)^n ≤ ‖Q (n-1) 0‖ := by
    have haxis (t : ℝ) : bilateralLaplace (Q (n-1)) ((t : ℂ) * I) =
        ((u t * (j ((t : ℂ) * I)).re^n : ℝ) : ℂ) := by
      rw [hQ n hn]
      dsimp only [u]
      conv_lhs => rw [(hkaxis t).2, (hpR t).1, (hjaxis t).1]
      push_cast
      ring
    have huv (t : ℝ) : 0 ≤ u t * (j ((t : ℂ) * I)).re^n :=
      mul_nonneg (mul_nonneg (hkaxis t).1.le (hpR t).2) (pow_nonneg (hjaxis t).2 _)
    exact (origin_ge_of_axis_interval (hQs _) (hQc _) haxis huv
      hab hc.le (by norm_num : (0 : ℝ) ≤ 3/4) hI).trans (Complex.re_le_norm _)
  obtain ⟨n, hn, hne, hall⟩ := exists_normalized_positive
    (S := S) (low := low) (k := k) (P := P) (j := j) (A := K 0) (d := fun n ↦ Q (n-1) 0)
    hC hM.le hA (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 3/4)
    (fun w hw ↦ (hsector w hw).1) (fun w hw ↦ (hsector w hw).2)
    (fun w hw ↦ hbound w (hstrip w hw)) (fun _ hw ↦ finiteTranslateMask_eq_zero hw) hhigh hnorm
  let L := Q (n-1)
  let c₀ := K 0/L 0
  let H (x : ℝ) := K x-c₀*L x
  have he (w : ℂ) : bilateralLaplace H w = k w * (1-c₀*(P w*j w^n)) := by
    rw [show bilateralLaplace H w = _ from
      bilateralLaplace_sub_const_mul K L hKs.continuous hKc (hQs _).continuous (hQc _) c₀ w,
      hKmom, show bilateralLaplace L w = _ from hQ n hn w]
    ring
  refine ⟨H, hKs.sub (contDiff_const.mul (hQs _)), hKc.sub (hQc _).mul_left,
    by simp [H, c₀, L, div_mul_cancel₀ _ hne], ?_, ?_⟩
  · exact fun z hz ↦ (he z).symm ▸ hall z hz
  · intro z hz
    rw [he, hz, zero_mul]

/-- A compact smooth profile can satisfy the physical and two polar vanishings and
have strictly positive real Laplace transform at every point of a prescribed set
in the open strip, provided every bounded-height window meets the set finitely. -/
theorem exists_compact_polarFree_positive_on_discreteStrip {B : ℝ} (hB : 0 < B) (S : Set ℂ)
    (hstrip : ∀ w ∈ S, |w.re| < B) (hfin : ∀ T : ℝ, {w ∈ S | |w.im| ≤ T}.Finite) :
    ∃ H : ℝ → ℂ, ContDiff ℝ (∞) H ∧ HasCompactSupport H ∧ H 0 = 0 ∧
      bilateralLaplace H (B : ℂ) = 0 ∧ bilateralLaplace H (-(B : ℂ)) = 0 ∧
      ∀ w ∈ S, 0 < (bilateralLaplace H w).re := by
  classical
  obtain ⟨K, hKs, hKc, hKe, -, -, hKpos, hKsector⟩ :=
    exists_compact_smooth_strip_sector (R := 2*B) (by positivity)
  obtain ⟨G, hGs, hGc, hGn, hGe, -, hGmass, hGzero, hGaxis⟩ :=
    exists_normalized_smooth_autocorrelation
  let Kc (x : ℝ) := (K x : ℂ)
  let Gc (x : ℝ) := (G x : ℂ)
  let k := bilateralLaplace Kc
  let j := bilateralLaplace Gc
  have hKs' : ContDiff ℝ (∞) Kc := Complex.ofRealCLM.contDiff.comp hKs
  have hGs' : ContDiff ℝ (∞) Gc := Complex.ofRealCLM.contDiff.comp hGs
  have hKc' : HasCompactSupport Kc := hKc.comp_left Complex.ofReal_zero
  have hGc' : HasCompactSupport Gc := hGc.comp_left Complex.ofReal_zero
  have hkR (t : ℝ) : k ((t : ℂ) * I) = ((k ((t : ℂ) * I)).re : ℂ) ∧ 0 < (k ((t : ℂ) * I)).re := by
    refine ⟨Complex.ext (by simp) (by simpa using bilateralLaplace_im_eq_zero_of_even hKe t), ?_⟩
    exact hKpos _ (by simpa using (show (0:ℝ) < 2*B by positivity))
  have hjR (t : ℝ) : j ((t : ℂ) * I) = ((j ((t : ℂ) * I)).re : ℂ) ∧ 0 ≤ (j ((t : ℂ) * I)).re ∧ (j ((t : ℂ) * I)).re ≤ 1 := by
    obtain ⟨v,hv,hvj⟩ := hGaxis t
    change j ((t : ℂ) * I) = (v : ℂ) at hvj
    simpa only [hvj, Complex.ofReal_re, true_and] using (show 0 ≤ v ∧ v ≤ 1 from ⟨hv.1,hv.2⟩)
  obtain ⟨jB, hjB, hjp, hjm, hinside⟩ :=
    normalized_even_density_polar_values hGs.continuous hGc hGe hGn hGmass hB
  obtain ⟨T, -, htail⟩ := bilateralLaplace_tends_zero_uniform_closedStrip
    (hGs'.of_le (by simp)) hGc' B (1/2) (by norm_num)
  let low := (hfin T).toFinset
  have hlow (w : ℂ) : w ∈ low ↔ w ∈ S ∧ |w.im| ≤ T := by simp [low]
  have hlowj (w : ℂ) (hw : w ∈ low) : ‖j w‖ < jB := hinside w (hstrip w ((hlow w).mp hw).1)
  have hhigh (w : ℂ) (hw : w ∈ S) (hn : w ∉ low) : ‖j w‖ ≤ 1/2 := by
    apply (htail w (hstrip w hw).le _).le
    exact le_of_not_ge fun ht ↦ hn ((hlow w).mpr ⟨hw,ht⟩)
  have hpos (w : ℂ) (hw : w ∈ S) : 0 < (k w).re := hKpos w (by linarith [hstrip w hw])
  have hsector (w : ℂ) (hw : w ∈ S) : ‖k w‖ ≤ (5/3 : ℝ) * (k w).re := by
    have hh := hKsector B hB.le (by linarith) w.re w.im (hstrip w hw).le
    have hfrac : B / (2*B) = 1/2 := by field_simp
    rw [Complex.re_add_im, hfrac] at hh
    norm_num at hh
    exact hh
  -- Impose the polar zeros first. The origin correction preserves zeros of its input.
  obtain ⟨d, hd₀, hd₁, hrat⟩ := exists_uniform_polar_ratio
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1) hjB hlowj hhigh
  obtain ⟨m, hm, hwp, hwm, hws, hwa⟩ := exists_polar_filter
    (by norm_num : (0:ℝ) ≤ 5/3) hd₀ hd₁ hjB hjp hjm hpos hsector hrat hkR hjR
  let W (z : ℂ) := k z * (1 - (j z / (jB : ℂ))^m)
  have hrK : IsCompactLaplaceTransform k := ⟨Kc, hKs', hKc', fun _ ↦ rfl⟩
  have hrG : IsCompactLaplaceTransform j := ⟨Gc, hGs', hGc', fun _ ↦ rfl⟩
  have hrm : IsCompactLaplaceTransform (fun z ↦ j z ^ m) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    exact realizes_pow_succ hrG n
  obtain ⟨R, hRs, hRc, hRm⟩ := realizes_mul hrK hrm
  let c := ((jB : ℂ)^m)⁻¹
  have hW : IsCompactLaplaceTransform W := by
    refine ⟨fun x ↦ Kc x - c * R x, hKs'.sub (contDiff_const.mul hRs), hKc'.sub hRc.mul_left, ?_⟩
    intro z
    rw [bilateralLaplace_sub_const_mul Kc R hKs'.continuous hKc' hRs.continuous hRc, hRm]
    change k z - c * (k z * j z^m) = W z
    dsimp only [W, c]
    rw [div_pow]
    ring
  obtain ⟨H, hs, hc, h0, hpos', hz⟩ := correct_origin low hW hrG
    (fun z hz ↦ (hstrip z hz).le) (by norm_num : (0 : ℝ) ≤ 4*(5/3)) hws hwa
    (fun t ↦ ⟨(hjR t).1, (hjR t).2.1⟩) hGzero hhigh
  exact ⟨H, hs, hc, h0, hz _ hwp, hz _ hwm, hpos'⟩

end RiemannMasullo
