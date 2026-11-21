module

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.MellinInversion
import RiemannMasullo.ForMathlib.Analysis.Complex.PhragmenLindelof
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.ChangeVariables
public import RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import RiemannMasullo.ForMathlib.Analysis.Complex.VerticalCauchyIntegral
public import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Montel
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import RiemannMasullo.ForMathlib.Analysis.Distribution.ContDiffMapSupportedIn
import RiemannMasullo.ForMathlib.Analysis.MellinTransform

/-!
# Schwartz–Bergman spaces and Schwartz–Bruhat functions with exponential decay

Masullo, Appendix D, §§D.3.1–D.3.3.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Filter Function MeasureTheory Set Topology TopologicalSpace UniformSpace
open scoped ContDiff NNReal ENNReal SchwartzMap TensorProduct

section Bergman

/-- Paper: Lemma D.3.1.1, p. 797. Bounds for one polynomial weight on every
interior strip persist after taking any number of complex derivatives. -/
theorem verticalStrip_weighted_iteratedDeriv_bounded (a b : ℝ) (hab : a < b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' Ioo a b)) (N : ℕ)
    (h : ∀ c d : ℝ, a < c → c < d → d < b →
      BddAbove ((fun z : ℂ ↦ ‖z ^ N * f z‖) '' (Complex.re ⁻¹' Ioo c d)))
    (k : ℕ) (c d : ℝ) (hac : a < c) (hcd : c < d) (hdb : d < b) :
    BddAbove ((fun z : ℂ ↦ ‖z ^ N * iteratedDeriv k f z‖) '' (Complex.re ⁻¹' Ioo c d)) := by
  let r := min (c - a) (b - d) / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have ha : a < c - r := by
    dsimp [r]
    linarith [min_le_left (c - a) (b - d)]
  have hb : d + r < b := by
    dsimp [r]
    linarith [min_le_right (c - a) (b - d)]
  obtain ⟨M, hM⟩ := h (c - r) (d + r) ha (by linarith) hb
  let B := 2 ^ N * max M 0
  refine ⟨k.factorial * B / (r / 4) ^ k, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  change c < z.re ∧ z.re < d at hz
  -- Choose a circle on which the weight at the center is controlled by the boundary weight.
  obtain ⟨R, hRlo, hRhi, hweight⟩ : ∃ R : ℝ, r / 4 ≤ R ∧ R ≤ r ∧
      ∀ w ∈ Metric.sphere z R, ‖z‖ ≤ 2 * ‖w‖ := by
    by_cases hsmall : ‖z‖ ≤ r / 2
    · refine ⟨r, by linarith, le_rfl, ?_⟩
      intro w hw
      have hd := dist_le_norm_add_norm w z
      rw [Metric.mem_sphere.mp hw] at hd
      linarith [norm_nonneg w]
    · refine ⟨r / 4, le_rfl, by linarith, ?_⟩
      intro w hw
      have hd := norm_sub_norm_le z w
      rw [← dist_eq_norm, dist_comm, Metric.mem_sphere.mp hw] at hd
      linarith
  have hstrip {w : ℂ} (hw : w ∈ Metric.closedBall z R) :
      w ∈ Complex.re ⁻¹' Ioo (c - r) (d + r) := by
    have hd := (Complex.abs_re_le_norm (w - z)).trans (mem_closedBall_iff_norm.mp hw)
    rw [Complex.sub_re, abs_le] at hd
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hdiff := (hf.const_mul (z ^ N)).diffContOnCl_ball (c := z) (R := R)
    (fun w hw ↦ Ioo_subset_Ioo ha.le hb.le (hstrip hw))
  have hcircle (w : ℂ) (hw : w ∈ Metric.sphere z R) : ‖z ^ N * f w‖ ≤ B := by
    have hwM := hM (mem_image_of_mem _ (hstrip (Metric.sphere_subset_closedBall hw)))
    calc
      ‖z ^ N * f w‖ = ‖z‖ ^ N * ‖f w‖ := by rw [norm_mul, norm_pow]
      _ ≤ (2 * ‖w‖) ^ N * ‖f w‖ := by
        gcongr
        exact hweight w hw
      _ = 2 ^ N * ‖w ^ N * f w‖ := by rw [mul_pow, norm_mul, norm_pow, mul_assoc]
      _ ≤ B := by
        dsimp [B]
        gcongr
        exact hwM.trans (le_max_left _ _)
  have hest := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
    (by linarith : 0 < R) hdiff hcircle
  rw [iteratedDeriv_const_mul_field] at hest
  apply hest.trans
  exact div_le_div_of_nonneg_left (by dsimp [B]; positivity) (by positivity)
    (pow_le_pow_left₀ (by positivity) hRlo k)

-- TODO(paper-gap): The proof's displayed denominator in (D.3.1.2) uses
-- σ + Re(z), although the real part of σ + iT - z is σ - Re(z).

/-- Paper: Definition D.3.1.3, p. 800. The strip conditions are closed under
the vector space operations. -/
theorem schwartzBergman_closure (I : Set ℝ) :
    let P (f : ℂ → ℂ) :=
      EqOn f 0 (Complex.re ⁻¹' I)ᶜ ∧ DifferentiableOn ℂ f (Complex.re ⁻¹' I) ∧
      ∀ (a b : ℝ), a ≤ b → Icc a b ⊆ I → ∀ N : ℕ,
        BddAbove ((fun z : ℂ ↦ ‖z ^ N * f z‖) '' (Complex.re ⁻¹' Icc a b))
    P 0 ∧ (∀ {f g}, P f → P g → P (f + g)) ∧ (∀ c : ℂ, ∀ {f}, P f → P (c • f)) := by
  dsimp only
  refine ⟨⟨eqOn_refl _ _, differentiableOn_const 0, ?_⟩, ?_, ?_⟩
  · intro a b _ _ N
    exact ⟨0, by rintro _ ⟨z, _, rfl⟩; simp⟩
  · rintro f g ⟨hf, df, bf⟩ ⟨hg, dg, bg⟩
    refine ⟨fun z hz ↦ ?_, df.add dg, ?_⟩
    · simp [Pi.add_apply, hf hz, hg hz]
    · intro a b hab hI N
      obtain ⟨A, hA⟩ := bf a b hab hI N
      obtain ⟨B, hB⟩ := bg a b hab hI N
      refine ⟨A + B, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      change ‖z ^ N * (f z + g z)‖ ≤ _
      rw [mul_add]
      exact (norm_add_le _ _).trans (add_le_add (hA ⟨z, hz, rfl⟩) (hB ⟨z, hz, rfl⟩))
  · rintro c f ⟨hf, df, bf⟩
    refine ⟨fun z hz ↦ ?_, df.const_mul c, ?_⟩
    · simp [Pi.smul_apply, hf hz]
    · intro a b hab hI N
      obtain ⟨A, hA⟩ := bf a b hab hI N
      refine ⟨‖c‖ * A, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      change ‖z ^ N * (c * f z)‖ ≤ _
      rw [mul_left_comm, norm_mul]
      exact mul_le_mul_of_nonneg_left (hA ⟨z, hz, rfl⟩) (norm_nonneg _)

/-- Paper: Definition D.3.1.3, p. 800. These are the holomorphic functions
with rapid decay on every bounded-width strip whose real closure is contained in the interval.
Deviation: Functions are extended by zero outside their strip to give a common carrier.
Bounds are tested on closed substrips, which is equivalent on an open interval. -/
def schwartzBergmanSubmodule (I : Set ℝ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | EqOn f 0 (Complex.re ⁻¹' I)ᶜ ∧ DifferentiableOn ℂ f (Complex.re ⁻¹' I) ∧
    ∀ (a b : ℝ), a ≤ b → Icc a b ⊆ I → ∀ N : ℕ,
      BddAbove ((fun z : ℂ ↦ ‖z ^ N * f z‖) '' (Complex.re ⁻¹' Icc a b))}
  zero_mem' := (schwartzBergman_closure I).1
  add_mem' := (schwartzBergman_closure I).2.1
  smul_mem' := (schwartzBergman_closure I).2.2

/-- Paper: Definition D.3.1.3, p. 800. The Gaussian restricted to a strip
gives a nonzero example whenever the strip is nonempty.
Deviation: Sanity check in the zero-extension representation. -/
theorem gaussian_mem_schwartzBergmanSubmodule (I : Set ℝ) (hI : IsOpen I) :
    (Complex.re ⁻¹' I).indicator (fun z : ℂ ↦ Complex.exp (z ^ 2)) ∈
      schwartzBergmanSubmodule I := by
  refine ⟨fun z hz ↦ indicator_of_notMem hz _, ?_, ?_⟩
  · have h : Differentiable ℂ (fun z : ℂ ↦ Complex.exp (z ^ 2)) := by fun_prop
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply (h z).congr_of_eventuallyEq
    filter_upwards [(hI.preimage Complex.continuous_re).mem_nhds hz] with w hw
    exact indicator_of_mem hw _
  · intro a b _ hab N
    let M := max |a| |b|
    refine ⟨N.factorial * Real.exp (1 + 2 * M ^ 2), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hstrip : z.re ∈ Icc a b := hz
    have hM : |z.re| ≤ M := abs_le_max_abs_abs hstrip.1 hstrip.2
    have hsq : z.re ^ 2 ≤ M ^ 2 := by
      simpa using pow_le_pow_left₀ (abs_nonneg _) hM 2
    have hweight : ‖z‖ ^ N ≤ N.factorial * Real.exp ‖z‖ := by
      have h := (div_le_iff₀ (show 0 < (N.factorial : ℝ) by positivity)).mp
        (Real.pow_div_factorial_le_exp ‖z‖ (norm_nonneg z) N)
      simpa [mul_comm] using h
    change ‖z ^ N * (Complex.re ⁻¹' I).indicator _ z‖ ≤ _
    rw [indicator_of_mem (show z ∈ Complex.re ⁻¹' I from hab hstrip), norm_mul, norm_pow, Complex.norm_exp]
    calc
      _ ≤ (N.factorial * Real.exp ‖z‖) * Real.exp (z ^ 2).re :=
        mul_le_mul_of_nonneg_right hweight (Real.exp_pos _).le
      _ = N.factorial * Real.exp (‖z‖ + (z ^ 2).re) := by rw [Real.exp_add, mul_assoc]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        rw [pow_two, Complex.mul_re]
        nlinarith [Complex.sq_norm_sub_sq_re z, sq_nonneg (‖z‖ - 1 / 2)]

/-- Paper: (D.3.1.7), p. 799. Evaluate the polynomially weighted function on the
vertical line with real part a. -/
def weightedVerticalTrace (a : ℝ) (N : ℕ) (f : ℂ → ℂ) (x : ℝ) : ℂ :=
  let z : ℂ := (a : ℂ) + (x : ℂ) * Complex.I
  z ^ N * f z

/-- Paper: (D.3.1.7), p. 799. At zero height, the trace evaluates the weighted
function on the real axis. -/
theorem weightedVerticalTrace_zero_height (a : ℝ) (N : ℕ) (f : ℂ → ℂ) :
    weightedVerticalTrace a N f 0 = (a : ℂ) ^ N * f a := by
  simp [weightedVerticalTrace]

/-- Paper: Lemma D.3.1.2, p. 799. Each polynomially weighted trace belongs to
the indicated Lᵖ space.
Deviation: The single-line bounds also give this for an endpoint when the
carrier is used with a closed interval. -/
theorem schwartzBergman_trace_memLp (I : Set ℝ) (a : I)
    (p : ℝ≥0∞) (hp : 1 < p) (hp' : p < ⊤) (N : ℕ) (f : schwartzBergmanSubmodule I) :
    MemLp (weightedVerticalTrace a N f.val) p volume := by
  let z (x : ℝ) : ℂ := (a.val : ℂ) + x * Complex.I
  have hz (x : ℝ) : (z x).re = a := by simp [z]
  have hc : Continuous z := by
    dsimp [z]
    fun_prop
  have hf : Continuous (f.val ∘ z) :=
    f.property.2.1.continuousOn.comp_continuous hc fun x ↦ by
      simp [mem_preimage, hz]
  have bound (k : ℕ) : ∃ C : ℝ, ∀ x, ‖z x ^ k * f.val (z x)‖ ≤ C := by
    obtain ⟨C, hC⟩ := f.property.2.2 a a le_rfl (by simp) k
    exact ⟨C, fun x ↦ hC ⟨z x, by simp [mem_preimage, hz], rfl⟩⟩
  obtain ⟨A, hA⟩ := bound N
  obtain ⟨B, hB⟩ := bound (N + 1)
  have hmodel : MemLp (fun x : ℝ ↦ (1 + ‖x‖)⁻¹) p volume := by
    apply (integrable_norm_rpow_iff (by fun_prop) (zero_lt_one.trans hp).ne' hp'.ne).mp
    have hdim : 1 < p.toReal := by
      simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp'.ne).2 hp
    have hnorm (x : ℝ) : ‖(1 + ‖x‖)⁻¹‖ = (1 + ‖x‖)⁻¹ := Real.norm_of_nonneg (by positivity)
    simpa only [hnorm, Real.rpow_neg_eq_inv_rpow] using
      (integrable_one_add_norm (μ := (volume : Measure ℝ)) (r := p.toReal) (by simpa using hdim))
  apply hmodel.of_le_mul (c := A + B) ((hc.pow N).mul hf).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  change ‖z x ^ N * f.val (z x)‖ ≤ (A + B) * ‖(1 + ‖x‖)⁻¹‖
  rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  rw [mul_add, mul_one]
  apply add_le_add (hA x)
  have hx : ‖x‖ ≤ ‖z x‖ := by simpa [Real.norm_eq_abs, z] using Complex.abs_im_le_norm (z x)
  calc
    ‖z x ^ N * f.val (z x)‖ * ‖x‖ ≤ ‖z x ^ N * f.val (z x)‖ * ‖z x‖ :=
      mul_le_mul_of_nonneg_left hx (norm_nonneg _)
    _ = ‖z x ^ (N + 1) * f.val (z x)‖ := by
      rw [← norm_mul, pow_succ, mul_right_comm]
    _ ≤ B := hB x

/-- Paper: Definition D.3.1.3, p. 800. The weighted L² norm on one line
satisfies the seminorm laws. -/
theorem schwartzBergman_l2_seminorm (I : Set ℝ) (i : I × ℕ) :
    let q (f : schwartzBergmanSubmodule I) :=
      (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal
    (∀ f g, q (f + g) ≤ q f + q g) ∧ (∀ (c : ℂ) f, q (c • f) = ‖c‖ * q f) := by
  let T (f : schwartzBergmanSubmodule I) := weightedVerticalTrace i.1 i.2 f.val
  have hT (f : schwartzBergmanSubmodule I) : MemLp (T f) 2 volume :=
    schwartzBergman_trace_memLp I i.1 2 (by norm_num) (by norm_num) i.2 f
  constructor
  · intro f g
    have hadd : T (f + g) = T f + T g := by
      funext x
      simp [T, weightedVerticalTrace, mul_add]
    change lpNorm (T (f + g)) 2 volume ≤ lpNorm (T f) 2 volume + lpNorm (T g) 2 volume
    rw [hadd]
    exact lpNorm_add_le (hT f) (by norm_num)
  · intro c f
    have hsmul : T (c • f) = c • T f := by
      funext x
      simp [T, weightedVerticalTrace, smul_eq_mul, mul_left_comm]
    change lpNorm (T (c • f)) 2 volume = ‖c‖ * lpNorm (T f) 2 volume
    rw [hsmul]
    exact lpNorm_const_smul c (T f) volume

-- TODO(paper-gap): Definition D.3.1.3 specifies positive rational abscissae
-- even for intervals contained in the negative half-line. Lemma D.3.1.2
-- instead uses real abscissae tending to both ends of the interval.

/-- Paper: Definition D.3.1.3, p. 800. Equip the Schwartz–Bergman
submodule with the topology of weighted L² convergence on interior vertical lines.
Deviation: Use all lines and p = 2 to make the choice-independent topology canonical.
Lemma D.3.1.2 identifies this with each of the paper's countable families. -/
abbrev SchwartzBergman (I : Set ℝ) :=
  WithGeneratingSeminorms (schwartzBergmanSubmodule I)
    (fun i : I × ℕ ↦ Seminorm.of
      (fun f : schwartzBergmanSubmodule I ↦
        (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
      (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2)

section VerticalTraces

local notation "linePoint" => (fun (x y : ℝ) ↦ (x : ℂ) + y * Complex.I)

private theorem exists_bracketing_lines {I : Set ℝ} (hI : IsOpen I) (a : I) :
    ∃ l r : I, (l : ℝ) < a ∧ (a : ℝ) < r := by
  obtain ⟨u, v, hav, huv⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds a.property)
  obtain ⟨l, hul, hla⟩ := exists_between hav.1
  obtain ⟨r, har, hrv⟩ := exists_between hav.2
  exact ⟨⟨l, huv ⟨hul, hla.trans hav.2⟩⟩, ⟨r, huv ⟨hav.1.trans har, hrv⟩⟩, hla, har⟩

/-- Weighted values inside the strip are bounded by the two boundary trace norms. -/
private theorem bergman_interior_lp_bound {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (l r : I) (p q : ℝ≥0∞) [ENNReal.HolderTriple p q 1]
    (hp : 1 < p) (hp' : p < ⊤) (hq : 1 < q) (hq' : q < ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ D ≥ (0 : ℝ), ∀ (k : ℕ) (f : schwartzBergmanSubmodule I) (z : ℂ),
      (l : ℝ) + δ ≤ z.re → z.re ≤ (r : ℝ) - δ →
        ‖z ^ k * f.val z‖ ≤ D * (lpNorm (weightedVerticalTrace l k f.val) p volume +
          lpNorm (weightedVerticalTrace r k f.val) p volume) := by
  obtain ⟨C, hC, hkernel⟩ := verticalCauchy_lpBound p q hq hq' hδ
  refine ⟨C / (2 * Real.pi), by positivity, ?_⟩
  intro k f z hl hr
  have hlz : (l : ℝ) < z.re := by linarith
  have hzr : z.re < (r : ℝ) := by linarith
  obtain ⟨a, _, hal, _⟩ := exists_bracketing_lines hI l
  obtain ⟨_, b, _, hrb⟩ := exists_bracketing_lines hI r
  let F (w : ℂ) := w ^ k * f.val w
  have hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Ioo (a : ℝ) (b : ℝ)) :=
    (differentiableOn_id.pow k).mul (f.property.2.1.mono
      (preimage_mono (Ioo_subset_Icc_self.trans (hInt.out a.property b.property))))
  obtain ⟨M, hM⟩ := f.property.2.2 l r (hlz.trans hzr).le (hInt.out l.property r.property) (k+1)
  have hdec : ∀ᶠ y : ℝ in comap abs atTop, ∀ x ∈ Icc (l : ℝ) r, ‖F (linePoint x y)‖ ≤ max M 0 / |y| := by
    have ht : Tendsto (abs : ℝ → ℝ) (comap abs atTop) atTop := tendsto_comap
    filter_upwards [ht.eventually (eventually_gt_atTop 0)] with y hy
    intro x hx
    let w := linePoint x y
    have hw : w ∈ Complex.re ⁻¹' Icc (l : ℝ) r := by simpa [w] using hx
    have him : |y| ≤ ‖w‖ := by simpa [w] using Complex.abs_im_le_norm w
    apply (le_div_iff₀ hy).mpr
    calc ‖F w‖ * |y| ≤ ‖F w‖ * ‖w‖ := mul_le_mul_of_nonneg_left him (norm_nonneg _)
      _ = ‖w ^ (k+1) * f.val w‖ := by simp only [F, pow_succ, ← norm_mul]; congr 1; ring
      _ ≤ max M 0 := (hM ⟨w, hw, rfl⟩).trans (le_max_left _ _)
  have hL := hkernel (σ := (l : ℝ)) (z := z) (by rw [abs_of_neg (sub_neg.mpr hlz)]; linarith)
    (schwartzBergman_trace_memLp I l p hp hp' k f)
  have hR := hkernel (σ := (r : ℝ)) (z := z) (by rw [abs_of_pos (sub_pos.mpr hzr)]; linarith)
    (schwartzBergman_trace_memLp I r p hp hp' k f)
  have eq := verticalCauchyIntegral_sub_eq hF hal hrb ⟨hlz,hzr⟩ (le_max_right M 0) hdec hL.1 hR.1
  have hb := (norm_sub_le _ _).trans (add_le_add hR.2 hL.2)
  have hb' := (congrArg norm eq.symm).le.trans hb
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le] at hb'
  norm_num at hb'
  change ‖F z‖ ≤ _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show 0 < 2 * Real.pi by positivity)).mpr
  calc ‖F z‖ * (2 * Real.pi) ≤ C * lpNorm (weightedVerticalTrace r k f.val) p volume +
        C * lpNorm (weightedVerticalTrace l k f.val) p volume := by simpa only [mul_comm ‖F z‖] using hb'
    _ = _ := by ring

/-- Differentiating a holomorphic function along a vertical trace introduces a factor of i. -/
private theorem hasDerivAt_vertical_iterate {I : Set ℝ} (hI : IsOpen I) (a : I)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' I)) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Complex.I ^ n * iteratedDeriv n f (linePoint a y))
      (Complex.I ^ (n+1) * iteratedDeriv (n+1) f (linePoint a x)) x := by
  have hU := hI.preimage Complex.continuous_re
  have han : ∀ m, AnalyticOnNhd ℂ (iteratedDeriv m f) (Complex.re ⁻¹' I) := by
    intro m
    induction m with
    | zero => simpa using hf.analyticOnNhd hU
    | succ m ih => rw [iteratedDeriv_succ]; exact fun z hz ↦ (ih z hz).deriv
  have hd := (han n _ (show linePoint a x ∈ Complex.re ⁻¹' I by simp)).differentiableAt.hasDerivAt
  have hline : HasDerivAt (fun w : ℂ ↦ (a.val : ℂ) + w * Complex.I) Complex.I (x : ℂ) := by
    simpa using (((hasDerivAt_id (x : ℂ)).mul_const Complex.I).const_add (a.val : ℂ))
  have h := ((hd.comp (x : ℂ) hline).comp_ofReal).const_mul (Complex.I ^ n)
  simpa only [Function.comp_apply, iteratedDeriv_succ, pow_succ, mul_left_comm,
    mul_assoc, mul_comm (deriv _ _)] using h

private theorem iteratedDeriv_vertical {I : Set ℝ} (hI : IsOpen I) (a : I)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' I)) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ ↦ f (linePoint a y)) =
      fun y ↦ Complex.I ^ n * iteratedDeriv n f (linePoint a y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (hasDerivAt_vertical_iterate hI a hf n x).deriv

/-- Both neighboring trace norms control each Schwartz seminorm on the intermediate line. -/
private theorem bergman_line_lp_bound {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (l a r : I) (hl : (l : ℝ) < a) (hr : (a : ℝ) < r)
    (p q : ℝ≥0∞) [ENNReal.HolderTriple p q 1] (hp : 1 < p) (hp' : p < ⊤)
    (hq : 1 < q) (hq' : q < ⊤) (k n : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ (f : schwartzBergmanSubmodule I) (y : ℝ),
      |y| ^ k * ‖iteratedDeriv n (fun u : ℝ ↦ f.val (linePoint a u)) y‖ ≤
        C * (lpNorm (weightedVerticalTrace l k f.val) p volume +
          lpNorm (weightedVerticalTrace r k f.val) p volume) := by
  let d := min ((a : ℝ) - l) ((r : ℝ) - a) / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hl' : (l : ℝ) + 2 * d ≤ a := by dsimp [d]; linarith [min_le_left ((a : ℝ) - l) ((r : ℝ) - a)]
  have hr' : (a : ℝ) + 2 * d ≤ r := by dsimp [d]; linarith [min_le_right ((a : ℝ) - l) ((r : ℝ) - a)]
  obtain ⟨D, hD, hbound⟩ := bergman_interior_lp_bound hI hInt l r p q hp hp' hq hq' hd
  refine ⟨n.factorial * (2 ^ k * D) / (d/4)^n, by positivity, ?_⟩
  intro f y
  let z := linePoint a y
  have hre : z.re = a := by simp [z]
  let Q := lpNorm (weightedVerticalTrace l k f.val) p volume + lpNorm (weightedVerticalTrace r k f.val) p volume
  have hQ : 0 ≤ Q := add_nonneg lpNorm_nonneg lpNorm_nonneg
  obtain ⟨R, hRlo, hRhi, hweight⟩ : ∃ R : ℝ, d/4 ≤ R ∧ R ≤ d ∧
      ∀ w ∈ Metric.sphere z R, ‖z‖ ≤ 2 * ‖w‖ := by
    by_cases hz : ‖z‖ ≤ d/2
    · refine ⟨d, by linarith, le_rfl, ?_⟩
      intro w hw
      have ht := dist_le_norm_add_norm w z
      rw [Metric.mem_sphere.mp hw] at ht
      linarith
    · refine ⟨d/4, le_rfl, by linarith, ?_⟩
      intro w hw
      have ht := norm_sub_norm_le z w
      rw [← dist_eq_norm, dist_comm, Metric.mem_sphere.mp hw] at ht
      linarith
  have hstrip {w : ℂ} (hw : w ∈ Metric.closedBall z R) :
      (l : ℝ) + d ≤ w.re ∧ w.re ≤ (r : ℝ) - d := by
    have h := (Complex.abs_re_le_norm (w-z)).trans (mem_closedBall_iff_norm.mp hw)
    rw [Complex.sub_re, hre, abs_le] at h
    constructor <;> linarith [h.1, h.2]
  have hdiff := (f.property.2.1.const_mul (z ^ k)).diffContOnCl_ball (c := z) (R := R)
    (fun w hw ↦ hInt.out l.property r.property ⟨by linarith [(hstrip hw).1], by linarith [(hstrip hw).2]⟩)
  have hcircle (w : ℂ) (hw : w ∈ Metric.sphere z R) : ‖z ^ k * f.val w‖ ≤ 2 ^ k * (D * Q) := by
    have hs := hstrip (Metric.sphere_subset_closedBall hw)
    calc ‖z ^ k * f.val w‖ = ‖z‖ ^ k * ‖f.val w‖ := by rw [norm_mul, norm_pow]
      _ ≤ (2 * ‖w‖)^k * ‖f.val w‖ := by gcongr; exact hweight w hw
      _ = 2 ^ k * ‖w ^ k * f.val w‖ := by rw [mul_pow, norm_mul, norm_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound k f w hs.1 hs.2) (by positivity)
  have hest := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by linarith : 0 < R) hdiff hcircle
  rw [iteratedDeriv_const_mul_field, norm_mul, norm_pow] at hest
  rw [iteratedDeriv_vertical hI a f.property.2.1, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
  calc |y| ^ k * ‖iteratedDeriv n f.val z‖ ≤ ‖z‖ ^ k * ‖iteratedDeriv n f.val z‖ := by
        gcongr
        simpa [z] using Complex.abs_im_le_norm z
    _ ≤ _ := hest
    _ ≤ n.factorial * (2 ^ k * (D * Q)) / (d/4)^n := div_le_div_of_nonneg_left
      (by positivity) (by positivity) (pow_le_pow_left₀ (by positivity) hRlo n)
    _ = _ := by dsimp only [Q]; ring

/-- Paper: Lemma D.3.1.2, p. 799. Restriction to a vertical line as a real Schwartz function. -/
private def bergmanLine {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (a : I) : SchwartzBergman I →ₗ[ℂ] 𝓢(ℝ, ℂ) where
  toFun f := {
    toFun := fun x ↦ f.val (linePoint a x)
    smooth' := by
      apply contDiff_of_differentiable_iteratedDeriv
      intro n _ x
      rw [iteratedDeriv_vertical hI a f.property.2.1]
      exact (hasDerivAt_vertical_iterate hI a f.property.2.1 n x).differentiableAt
    decay' := by
      intro k n
      obtain ⟨l, r, hl, hr⟩ := exists_bracketing_lines hI a
      obtain ⟨C, _, h⟩ := bergman_line_lp_bound hI hInt l a r hl hr 2 2
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) k n
      exact ⟨_, fun x ↦ by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using h f x⟩ }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- Multiply a Schwartz function by the vertical polynomial weight and include it in Lᵖ. -/
private def weightedSchwartzLp (a : ℝ) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    𝓢(ℝ, ℂ) →L[ℂ] Lp ℂ p (volume : Measure ℝ) :=
  (SchwartzMap.toLpCLM ℂ ℂ p volume).comp (SchwartzMap.smulLeftCLM ℂ fun y : ℝ ↦ (linePoint a y)^k)

/-- Paper: (D.3.1.7), p. 799. The weighted Lᵖ norm of the trace on a single line. -/
private def bergmanLpSeminorm {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : I) (k : ℕ) : Seminorm ℂ (SchwartzBergman I) :=
  (normSeminorm ℂ _).comp ((weightedSchwartzLp a k p).toLinearMap.comp (bergmanLine hI hInt a))

private theorem bergmanLpSeminorm_apply {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : I) (k : ℕ) (f : SchwartzBergman I) :
    bergmanLpSeminorm hI hInt p a k f = lpNorm (weightedVerticalTrace a k f.val) p volume := by
  change ‖((SchwartzMap.smulLeftCLM ℂ (fun y : ℝ ↦ (linePoint a y)^k)) (bergmanLine hI hInt a f)).toLp p volume‖ = _
  rw [SchwartzMap.norm_toLp, toReal_eLpNorm]
  congr 1
  have hg : (fun y : ℝ ↦ (linePoint a y) ^ k).HasTemperateGrowth := by fun_prop
  rw [SchwartzMap.smulLeftCLM_apply hg]
  rfl

private theorem bergman_with_l2 {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I) :
    WithSeminorms (fun i : I × ℕ ↦ bergmanLpSeminorm hI hInt 2 i.1 i.2) := by
  let P : I × ℕ → Seminorm ℂ (SchwartzBergman I) := fun i ↦ Seminorm.of
      (fun f : schwartzBergmanSubmodule I ↦ (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
      (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2
  have heq : (fun i : I × ℕ ↦ bergmanLpSeminorm hI hInt 2 i.1 i.2) = P := by
    funext i
    ext f
    exact bergmanLpSeminorm_apply hI hInt 2 i.1 i.2 f
  rw [heq]
  exact withGeneratingSeminorms_spec (schwartzBergmanSubmodule I) P

private theorem continuous_bergmanLine_of_bracketing {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (a l r : I) (hl : (l : ℝ) < a) (hr : (a : ℝ) < r)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [ENNReal.HolderTriple p q 1]
    (hp : 1 < p) (hp' : p < ⊤) (hq : 1 < q) (hq' : q < ⊤)
    [t : TopologicalSpace (SchwartzBergman I)] [IsTopologicalAddGroup (SchwartzBergman I)]
    (hL : ∀ k, Continuous (bergmanLpSeminorm hI hInt p l k))
    (hR : ∀ k, Continuous (bergmanLpSeminorm hI hInt p r k)) :
    Continuous (bergmanLine hI hInt a) := by
  apply (schwartz_withSeminorms ℂ ℝ ℂ).continuous_of_continuous_comp
  rintro ⟨k,n⟩
  obtain ⟨C, hC, hb⟩ := bergman_line_lp_bound hI hInt l a r hl hr p q hp hp' hq hq' k n
  let c : ℝ≥0 := ⟨C,hC⟩
  apply Seminorm.continuous_of_le (q := c • (bergmanLpSeminorm hI hInt p l k + bergmanLpSeminorm hI hInt p r k))
    (((hL k).add (hR k)).const_smul c)
  intro f
  change SchwartzMap.seminorm ℂ k n (bergmanLine hI hInt a f) ≤
    C * (bergmanLpSeminorm hI hInt p l k f + bergmanLpSeminorm hI hInt p r k f)
  rw [bergmanLpSeminorm_apply, bergmanLpSeminorm_apply]
  apply SchwartzMap.seminorm_le_bound' _ _ _ _ (mul_nonneg hC (add_nonneg lpNorm_nonneg lpNorm_nonneg))
  exact hb f

private theorem continuous_bergmanLine {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (a : I) : Continuous (bergmanLine hI hInt a) := by
  obtain ⟨l, r, hl, hr⟩ := exists_bracketing_lines hI a
  have hc := (bergman_with_l2 hI hInt).continuous_seminorm
  exact continuous_bergmanLine_of_bracketing hI hInt a l r hl hr 2 2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun k ↦ hc (l,k)) (fun k ↦ hc (r,k))

private theorem le_topology_withSeminorms {E ι : Type*} [AddCommGroup E] [Module ℂ E]
    [t : TopologicalSpace E] [IsTopologicalAddGroup E] {u : TopologicalSpace E}
    {P : ι → Seminorm ℂ E} (hP : WithSeminorms (topology := u) P)
    (hc : ∀ i, Continuous[t, _] (P i)) : t ≤ u :=
  continuous_id_iff_le.mp (@WithSeminorms.continuous_of_continuous_comp ℂ ℂ E E ι
    _ _ _ _ _ _ (RingHom.id ℂ) _ P t _ u hP (LinearMap.id (R := ℂ)) hc)

private theorem bergman_embedding {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I) :
    IsEmbedding (fun (f : SchwartzBergman I) (a : I) ↦ bergmanLine hI hInt a f) := by
  let T := LinearMap.pi (bergmanLine hI hInt)
  change IsEmbedding T
  have hcont : Continuous T := continuous_pi (continuous_bergmanLine hI hInt)
  refine ⟨⟨le_antisymm (continuous_iff_le_induced.mp hcont) ?_⟩, ?_⟩
  · let t := TopologicalSpace.induced T inferInstance
    have hT : Continuous[t, _] T := continuous_induced_dom
    have hprod := withSeminorms_pi fun _ : I ↦ schwartz_withSeminorms ℂ ℝ ℂ
    have hsource := bergman_with_l2 hI hInt
    let : TopologicalSpace (SchwartzBergman I) := t
    let : IsTopologicalAddGroup (SchwartzBergman I) := (T.withSeminorms_induced hprod).isTopologicalAddGroup
    apply le_topology_withSeminorms (t := t) hsource
    rintro ⟨a,k⟩
    exact ((weightedSchwartzLp a k 2).continuous.comp ((continuous_apply a).comp hT)).norm
  · intro f g h
    apply Subtype.ext
    funext z
    by_cases hz : z.re ∈ I
    · have eq := congrArg (fun v : 𝓢(ℝ, ℂ) ↦ v z.im) (congrFun h ⟨z.re, hz⟩)
      change f.val (linePoint z.re z.im) = g.val (linePoint z.re z.im) at eq
      simpa only [Complex.re_add_im] using eq
    · exact (f.property.1 hz).trans (g.property.1 hz).symm

end VerticalTraces

/-- Paper: Lemma D.3.1.2, p. 799. Weighted Lᵖ norms on a sequence of lines
reaching both ends of the interval generate the Schwartz–Bergman topology.
Deviation: The endpoint condition is expressed by bracketing every real point of I. -/
theorem schwartzBergman_lp_generates (I : Set ℝ) (hI : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) (a : ℕ → I)
    (ha : ∀ x : I, (∃ n, (a n : ℝ) < x) ∧ ∃ n, (x : ℝ) < a n)
    (p : ℝ≥0∞) (hp : 1 < p) (hp' : p < ⊤) :
    GeneratesLpSeminorms volume p
      (fun (i : ℕ × ℕ) (f : SchwartzBergman I) ↦ weightedVerticalTrace (a i.1) i.2 f.val) := by
  let : Fact (1 ≤ p) := ⟨hp.le⟩
  let q := ENNReal.conjExponent p
  have hq : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp'
  have hq' : q < ⊤ := (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp
  let P : SeminormFamily ℂ (SchwartzBergman I) (ℕ × ℕ) := fun i ↦ bergmanLpSeminorm hI hInt p (a i.1) i.2
  have hmem (i : ℕ × ℕ) (f : SchwartzBergman I) := schwartzBergman_trace_memLp I (a i.1) p hp hp' i.2 f
  refine ⟨hmem, P, ?_, ?_⟩
  · have hc (i : ℕ × ℕ) : Continuous (P i) :=
      ((weightedSchwartzLp (a i.1) i.2 p).continuous.comp (continuous_bergmanLine hI hInt (a i.1))).norm
    let t : TopologicalSpace (SchwartzBergman I) := inferInstance
    let u := P.moduleFilterBasis.topology
    have hP : WithSeminorms (topology := u) P := ⟨rfl⟩
    refine WithSeminorms.mk (topology := t) ?_
    change t = u
    apply le_antisymm
    · exact le_topology_withSeminorms (t := t) hP hc
    · have h2 := bergman_with_l2 hI hInt
      let : TopologicalSpace (SchwartzBergman I) := u
      let : IsTopologicalAddGroup (SchwartzBergman I) := hP.isTopologicalAddGroup
      apply le_topology_withSeminorms (t := u) h2
      rintro ⟨s,k⟩
      obtain ⟨⟨j,hj⟩, m, hm⟩ := ha s
      have hs := continuous_bergmanLine_of_bracketing (t := u) hI hInt s (a j) (a m) hj hm p q
        hp hp' hq hq' (fun k ↦ hP.continuous_seminorm (j,k)) (fun k ↦ hP.continuous_seminorm (m,k))
      exact ((weightedSchwartzLp s k 2).continuous.comp hs).norm
  · intro i f
    dsimp only [P]
    rw [bergmanLpSeminorm_apply, ← toReal_eLpNorm, ENNReal.ofReal_toReal (hmem i f).eLpNorm_ne_top]

/-- Paper: Lemma D.3.1.2, p. 799. The topology also comes from taking the
Schwartz restriction to each vertical line. -/
theorem schwartzBergman_schwartzLine_topology (I : Set ℝ) (hI : IsOpen I)
    (hInt : OrdConnected I) (hne : I.Nonempty) :
    ∃ T : SchwartzBergman I → (I → 𝓢(ℝ, ℂ)),
      (∀ f (a : I) x, T f a x = weightedVerticalTrace a 0 f.val x) ∧ IsEmbedding T :=
  by
    refine ⟨fun f a ↦ bergmanLine hI hInt a f, ?_, bergman_embedding hI hInt⟩
    intro f a x
    simp only [weightedVerticalTrace, pow_zero, one_mul]
    rfl

/-- Paper: Lemma D.3.1.2, p. 799. The Schwartz–Bergman space is separable. -/
theorem schwartzBergman_separable (I : Set ℝ) (hI : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) : SeparableSpace (SchwartzBergman I) := by
  let : Nonempty I := hne.to_subtype
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq I
  have hbr (x : I) : (∃ n, (a n : ℝ) < x) ∧ ∃ n, (x : ℝ) < a n := by
    obtain ⟨l,r,hl,hr⟩ := exists_bracketing_lines hI x
    exact ⟨ha.exists_mem_open isOpen_Iio ⟨l,hl⟩, ha.exists_mem_open isOpen_Ioi ⟨r,hr⟩⟩
  obtain ⟨_, P, hP, hval⟩ := schwartzBergman_lp_generates I hI hInt hne a hbr 2 (by norm_num) (by norm_num)
  let L (i : ℕ × ℕ) := (weightedSchwartzLp (a i.1) i.2 2).toLinearMap.comp (bergmanLine hI hInt (a i.1))
  let T := LinearMap.pi L
  have heq (i : ℕ × ℕ) : P i = (normSeminorm ℂ _).comp (L i) := by
    ext f
    change P i f = bergmanLpSeminorm hI hInt 2 (a i.1) i.2 f
    rw [bergmanLpSeminorm_apply, ← toReal_eLpNorm]
    exact (ENNReal.toReal_ofReal (apply_nonneg (P i) f)).symm.trans (congrArg ENNReal.toReal (hval i f))
  have hprod := withSeminorms_pi fun _ : ℕ × ℕ ↦ norm_withSeminorms ℂ (Lp ℂ 2 (volume : Measure ℝ))
  have hi : IsInducing T := by
    constructor
    refine hP.topologicalSpace_eq_iInf.trans ?_
    refine Eq.trans ?_ (WithSeminorms.topologicalSpace_eq_iInf (t := TopologicalSpace.induced T inferInstance)
      (T.withSeminorms_induced hprod)).symm
    rw [iInf_sigma]
    congr 1
    funext i
    rw [heq, iInf_unique]
    rfl
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have := hi.secondCountableTopology
  infer_instance

end Bergman

section PositiveReal

/-- Paper: Definition D.3.2.1, p. 801. A real Schwartz map is viewed as a
function by the linear forgetful map. -/
def realSchwartzCoe : 𝓢(ℝ, ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Paper: Definition D.3.2.1, p. 801. Forgetting the Schwartz properties
retains the values of the function. -/
theorem realSchwartzCoe_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : realSchwartzCoe f x = f x := rfl

/-- Paper: Definition D.3.2.1, p. 801. In logarithmic coordinates, weighting
by tᵃ amounts to multiplying by exp(ax). -/
def logExponentialWeight (a : ℝ) : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) :=
  LinearMap.mulLeft ℂ (fun x : ℝ ↦ (Real.exp (a * x) : ℂ))

/-- Paper: Definition D.3.2.1, p. 801. The weight at exponent zero does not
change the function. -/
theorem logExponentialWeight_zero (f : ℝ → ℂ) : logExponentialWeight 0 f = f := by
  ext x
  simp [logExponentialWeight, LinearMap.mulLeft]

/-- Paper: Definition D.3.2.1, p. 801. A logarithmic profile belongs to the
decay submodule if each weighted profile is a real-line Schwartz function.
Deviation: The carrier is in the logarithmic coordinate x = log t. -/
def logExponentialDecaySubmodule (I : Set ℝ) : Submodule ℂ (ℝ → ℂ) :=
  ⨅ a : I, realSchwartzCoe.range.comap (logExponentialWeight a)

/-- A compactly supported smooth profile has Schwartz decay after every real exponential twist. -/
theorem mem_logExponentialDecaySubmodule_of_hasCompactSupport (I : Set ℝ) {f : ℝ → ℂ}
    (hs : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) : f ∈ logExponentialDecaySubmodule I := by
  apply (Submodule.mem_iInf _).2
  intro a
  let w (x : ℝ) : ℂ := Real.exp ((a : ℝ) * x)
  have hw : ContDiff ℝ ∞ w :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).exp)
  exact ⟨(hs.mul_left (f := w)).toSchwartzMap (hw.mul hf), rfl⟩

/-- Paper: Definition D.3.2.1, p. 801. The multiplier Tₐ is the weighted
profile, bundled as a Schwartz map. -/
theorem logExponentialDecay_weight_mem_range (I : Set ℝ)
    (a : I) (f : logExponentialDecaySubmodule I) :
    logExponentialWeight a f.val ∈ realSchwartzCoe.range := by
  exact (Submodule.mem_iInf _).mp f.property a

/-- Paper: (D.3.2.1), p. 801. This is the linear multiplier to the space
of Schwartz functions in logarithmic coordinates. -/
def logExponentialDecayTwist (I : Set ℝ) (a : I) : logExponentialDecaySubmodule I →ₗ[ℂ] 𝓢(ℝ, ℂ) :=
  (LinearEquiv.ofInjective realSchwartzCoe DFunLike.coe_injective).symm.toLinearMap.comp
    (((logExponentialWeight a).comp (logExponentialDecaySubmodule I).subtype).codRestrict
      realSchwartzCoe.range (logExponentialDecay_weight_mem_range I a))

/-- Paper: (D.3.2.1), p. 801. The bundled multiplier evaluates to
exp(ax) times the original logarithmic profile. -/
theorem logExponentialDecayTwist_apply (I : Set ℝ) (a : I)
    (f : logExponentialDecaySubmodule I) (x : ℝ) :
    logExponentialDecayTwist I a f x = (Real.exp ((a : ℝ) * x) : ℂ) * f.val x := by
  exact congrFun (LinearEquiv.ofInjective_symm_apply realSchwartzCoe
    (h := DFunLike.coe_injective)
    ⟨logExponentialWeight a f.val, logExponentialDecay_weight_mem_range I a f⟩) x

/-- Paper: Definition D.3.2.1, p. 801. The topology is induced by
all weighted Schwartz profiles, using the usual seminorms on the real Schwartz space.
Deviation: Positive real functions are represented by their logarithmic profiles. -/
abbrev PositiveRealExponentialDecay (I : Set ℝ) :=
  WithGeneratingSeminorms (logExponentialDecaySubmodule I)
    (fun i : I × ℕ × ℕ ↦
      (SchwartzMap.seminorm ℂ i.2.1 i.2.2).comp (logExponentialDecayTwist I i.1))

/-- Paper: Definition D.3.2.1, p. 801. The family of weighted profiles embeds
the decay space in a product of real Schwartz spaces. -/
theorem positiveRealExponentialDecay_isEmbedding (I : Set ℝ) (hne : I.Nonempty) :
    IsEmbedding (fun (f : PositiveRealExponentialDecay I) (a : I) ↦
      logExponentialDecayTwist I a f) := by
  let T : PositiveRealExponentialDecay I →ₗ[ℂ] (I → 𝓢(ℝ, ℂ)) :=
    LinearMap.pi (logExponentialDecayTwist I)
  have hp := withSeminorms_pi fun _ : I ↦ schwartz_withSeminorms ℂ ℝ ℂ
  have hsource := withGeneratingSeminorms_spec (logExponentialDecaySubmodule I)
    (fun i : I × ℕ × ℕ ↦
      (SchwartzMap.seminorm ℂ i.2.1 i.2.2).comp (logExponentialDecayTwist I i.1))
  change IsEmbedding T
  constructor
  · constructor
    refine hsource.topologicalSpace_eq_iInf.trans ?_
    refine Eq.trans ?_ (WithSeminorms.topologicalSpace_eq_iInf
      (t := TopologicalSpace.induced T inferInstance) (T.withSeminorms_induced hp)).symm
    rw [iInf_sigma, iInf_prod]
    rfl
  · intro f g h
    obtain ⟨a, ha⟩ := hne
    apply Subtype.ext
    funext x
    have hx := congrArg (fun F : 𝓢(ℝ, ℂ) ↦ F x) (congrFun h ⟨a, ha⟩)
    change logExponentialDecayTwist I ⟨a, ha⟩ f x = logExponentialDecayTwist I ⟨a, ha⟩ g x at hx
    rw [logExponentialDecayTwist_apply I ⟨a, ha⟩ f x,
      logExponentialDecayTwist_apply I ⟨a, ha⟩ g x] at hx
    exact mul_left_cancel₀ (by exact_mod_cast (Real.exp_pos (a * x)).ne') hx

variable (I : Set ℝ)

local notation "E" => PositiveRealExponentialDecay I
local notation "D" => StrongDual ℂ E

open scoped BoundedContinuousFunction

open scoped Distributions in
/-- A smooth test function supported in a fixed compact set includes continuously into the
space of profiles with Schwartz decay under every prescribed exponential weight. -/
def supportedToLogDecayCLM (I : Set ℝ) (hI : I.Nonempty) (K : Compacts ℝ) :
    𝓓_{K}(ℝ, ℂ) →L[ℂ] PositiveRealExponentialDecay I := by
  let J : 𝓓_{K}(ℝ, ℂ) →ₗ[ℂ] PositiveRealExponentialDecay I :=
    { toFun f := ⟨(f : ℝ → ℂ), mem_logExponentialDecaySubmodule_of_hasCompactSupport I
        f.hasCompactSupport f.contDiff⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  refine ⟨J, (positiveRealExponentialDecay_isEmbedding I hI).isInducing.continuous_iff.mpr ?_⟩
  apply continuous_pi
  intro a
  let w (x : ℝ) : ℂ := Real.exp ((a : ℝ) * x)
  have hw : ContDiff ℝ ∞ w :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).exp)
  let M : 𝓓_{K}(ℝ, ℂ) →L[ℂ] 𝓓_{K}(ℝ, ℂ) :=
    ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) hw
  convert ((supportedToSchwartzCLM ℂ K).comp M).continuous using 1
  funext f
  ext x
  change logExponentialDecayTwist I a (show logExponentialDecaySubmodule I from J f) x = f x * w x
  rw [logExponentialDecayTwist_apply I a _ x]
  exact mul_comm _ _

/-- Paper: Lemma D.3.2.3(1), p. 802. The image in the product is closed because the
compatibility equations between weighted profiles are closed pointwise conditions. -/
private theorem isClosed_range_logExponentialDecayTwist (I : Set ℝ) (a : I) :
    IsClosed (range (fun (f : PositiveRealExponentialDecay I) (b : I) ↦
      logExponentialDecayTwist I b f)) := by
  let w (b : I) (x : ℝ) : ℂ := Real.exp ((b : ℝ) * x)
  have hw (b : I) (x : ℝ) : w b x ≠ 0 := by
    dsimp [w]
    exact_mod_cast (Real.exp_pos ((b : ℝ) * x)).ne'
  have heval (b : I) (x : ℝ) : Continuous (fun g : I → 𝓢(ℝ, ℂ) ↦ g b x) :=
    (continuous_eval_const (F := ℝ →ᵇ ℂ) x).comp
      ((SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous.comp (continuous_apply b))
  have hrange : range (fun (f : PositiveRealExponentialDecay I) (b : I) ↦
      logExponentialDecayTwist I b f) =
      ⋂ (b : I) (x : ℝ), {g : I → 𝓢(ℝ, ℂ) | w a x * g b x = w b x * g a x} := by
    ext g
    simp only [mem_iInter, mem_ofPred_eq, mem_range]
    constructor
    · rintro ⟨f, rfl⟩ b x
      rw [logExponentialDecayTwist_apply I b f x, logExponentialDecayTwist_apply I a f x]
      exact mul_left_comm _ _ _
    · intro hg
      let f (x : ℝ) := g a x / w a x
      have hmatch (b : I) (x : ℝ) : w b x * f x = g b x := by
        rw [show w b x * f x = (w b x * g a x) / w a x by simp [f, mul_div_assoc]]
        exact (div_eq_iff (hw a x)).mpr ((hg b x).symm.trans (mul_comm _ _))
      have hf : f ∈ logExponentialDecaySubmodule I := by
        apply (Submodule.mem_iInf _).mpr
        intro b
        exact ⟨g b, funext fun x ↦ (hmatch b x).symm⟩
      refine ⟨⟨f, hf⟩, ?_⟩
      funext b
      ext x
      rw [logExponentialDecayTwist_apply]
      exact hmatch b x
  rw [hrange]
  exact isClosed_iInter fun b ↦ isClosed_iInter fun x ↦
    isClosed_eq (continuous_const.mul (heval b x)) (continuous_const.mul (heval a x))

/-- Paper: Lemma D.3.2.3(1), p. 802. The closed embedding into the product of complete
Schwartz spaces gives completeness for the additive uniformity. -/
private theorem positiveRealExponentialDecay_complete (I : Set ℝ) (hne : I.Nonempty) :
    CompleteSpace (PositiveRealExponentialDecay I) := by
  have : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  let T : PositiveRealExponentialDecay I →ₗ[ℂ] (I → 𝓢(ℝ, ℂ)) :=
    LinearMap.pi (logExponentialDecayTwist I)
  have hT : IsUniformInducing T := AddMonoidHom.isUniformInducing_of_isInducing
    (f := T.toAddMonoidHom) (positiveRealExponentialDecay_isEmbedding I hne).isInducing
  obtain ⟨a, ha⟩ := hne
  exact (completeSpace_iff_isComplete_range hT).mpr
    (isClosed_range_logExponentialDecayTwist I ⟨a, ha⟩).isComplete

/-- A finite sum of Schwartz seminorms controlling the derivatives of an exponential twist
on the half-line where that exponential is at most one. -/
private def exponentialTwistBound (t : ℝ) (k n : ℕ) : Seminorm ℂ 𝓢(ℝ, ℂ) :=
  ∑ i ∈ Finset.range (n + 1),
    ((n.choose i : ℝ≥0) * ‖t‖₊ ^ i) • SchwartzMap.seminorm ℂ k (n - i)

private theorem exponentialTwistBound_continuous (t : ℝ) (k n : ℕ) :
    Continuous (exponentialTwistBound t k n) := by
  apply Seminorm.continuous_finsetSum
  intro i _
  exact ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (k, n - i)).const_smul _

/-- Leibniz's formula bounds the weighted derivative wherever the exponential is at most one. -/
private theorem weighted_deriv_exp_smul_le (t x : ℝ) (hx : t * x ≤ 0) (k n : ℕ) (g : 𝓢(ℝ, ℂ)) :
    |x| ^ k * ‖iteratedDeriv n ((fun y ↦ Real.exp (t * y)) • ⇑g) x‖ ≤
      exponentialTwistBound t k n g := by
  have hexp : ContDiff ℝ n (fun y : ℝ ↦ Real.exp (t * y)) := by fun_prop
  have hderiv := iteratedDerivWithin_smul (Set.mem_univ x) uniqueDiffOn_univ
    hexp.contDiffAt.contDiffWithinAt (g.smooth n).contDiffAt.contDiffWithinAt
  simp only [iteratedDerivWithin_univ, iteratedDeriv_exp_const_mul] at hderiv
  rw [hderiv]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (abs_nonneg x) k)).trans ?_
  rw [Finset.mul_sum]
  simp only [exponentialTwistBound, FunLike.coe_sum, Finset.sum_apply, smul_apply, NNReal.smul_def,
    NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, coe_nnNorm, smul_eq_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [RCLike.norm_nsmul (K := ℝ), nsmul_eq_mul, norm_smul, norm_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le, norm_pow]
  have h := g.le_seminorm' ℂ k (n - i) x
  have hcoeff : 0 ≤ (n.choose i : ℝ) * ‖t‖ ^ i := by positivity
  calc
    _ = ((n.choose i : ℝ) * ‖t‖ ^ i) * (Real.exp (t * x) *
        (|x| ^ k * ‖iteratedDeriv (n - i) g x‖)) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hcoeff
      exact (mul_le_of_le_one_left (by positivity) (Real.exp_le_one_iff.mpr hx)).trans h

/-- Paper: Lemma D.3.2.3(1), p. 802. On each half-line the corresponding endpoint
controls the Schwartz seminorm of every intermediate twist. -/
private theorem exponentialTwist_seminorm_le {I : Set ℝ} (a b c : I) (hba : b ≤ a) (hac : a ≤ c)
    (k n : ℕ) (f : logExponentialDecaySubmodule I) :
    SchwartzMap.seminorm ℂ k n (logExponentialDecayTwist I a f) ≤
      exponentialTwistBound (a - b : ℝ) k n (logExponentialDecayTwist I b f) +
      exponentialTwistBound (a - c : ℝ) k n (logExponentialDecayTwist I c f) := by
  have changeWeight (d : I) : ⇑(logExponentialDecayTwist I a f) =
      (fun x ↦ Real.exp (((a : ℝ) - d) * x)) • ⇑(logExponentialDecayTwist I d f) := by
    funext x
    change _ = Real.exp (((a : ℝ) - d) * x) • logExponentialDecayTwist I d f x
    rw [Complex.real_smul, logExponentialDecayTwist_apply,
      logExponentialDecayTwist_apply, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  apply SchwartzMap.seminorm_le_bound' ℂ k n _ (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
  intro x
  rcases le_total x 0 with hx | hx
  · rw [changeWeight b]
    exact (weighted_deriv_exp_smul_le _ _ (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hba) hx)
      k n _).trans (le_add_of_nonneg_right (apply_nonneg _ _))
  · rw [changeWeight c]
    exact (weighted_deriv_exp_smul_le _ _ (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hac) hx)
      k n _).trans (le_add_of_nonneg_left (apply_nonneg _ _))

/-- Paper: Lemma D.3.2.3(1), p. 802. Two countable sequences of exponents bracket
every exponent of the interval and suffice to generate the topology. -/
private theorem exponentialDecay_metrizable (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty) :
    MetrizableSpace (PositiveRealExponentialDecay I) := by
  have : Nonempty I := hne.to_subtype
  obtain ⟨lo, -, hlo⟩ := exists_seq_antitone_tendsto_atTop_atBot I
  obtain ⟨hi, -, hhi⟩ := exists_seq_monotone_tendsto_atTop_atTop I
  let d : ℕ ⊕ ℕ → I := Sum.elim lo hi
  let p (i : I × ℕ × ℕ) :=
    (SchwartzMap.seminorm ℂ i.2.1 i.2.2).comp (logExponentialDecayTwist I i.1)
  let q (j : (ℕ ⊕ ℕ) × ℕ × ℕ) := p (d j.1, j.2)
  let X := WithGeneratingSeminorms (logExponentialDecaySubmodule I) q
  let Y := PositiveRealExponentialDecay I
  have hp := withGeneratingSeminorms_spec (logExponentialDecaySubmodule I) p
  have hq := withGeneratingSeminorms_spec (logExponentialDecaySubmodule I) q
  let T (a : I) : X →ₗ[ℂ] 𝓢(ℝ, ℂ) := logExponentialDecayTwist I a
  have hc (j : ℕ ⊕ ℕ) : Continuous (T (d j)) := by
    apply (schwartz_withSeminorms ℂ ℝ ℂ).continuous_of_continuous_comp
    intro i
    exact hq.continuous_seminorm (j, i)
  let toFull : X →ₗ[ℂ] Y := LinearMap.id
  have hfull : Continuous toFull := by
    apply hp.continuous_of_continuous_comp
    rintro ⟨a, k, n⟩
    obtain ⟨l, hl⟩ := (hlo.eventually (eventually_le_atBot a)).exists
    obtain ⟨r, hr⟩ := (hhi.eventually (eventually_ge_atTop a)).exists
    let B := ((exponentialTwistBound (a - lo l : ℝ) k n).comp (T (lo l))) +
      ((exponentialTwistBound (a - hi r : ℝ) k n).comp (T (hi r)))
    have hB : Continuous B :=
      ((exponentialTwistBound_continuous _ _ _).comp (hc (.inl l))).add
        ((exponentialTwistBound_continuous _ _ _).comp (hc (.inr r)))
    exact Seminorm.continuous_of_le hB (fun f ↦ exponentialTwist_seminorm_le a _ _ hl hr k n f)
  let toCountable : Y →ₗ[ℂ] X := LinearMap.id
  have hcountable : Continuous toCountable := by
    apply hq.continuous_of_continuous_comp
    intro j
    exact hp.continuous_seminorm (d j.1, j.2)
  let e : Y ≃ₜ X := ⟨Equiv.refl _, hcountable, hfull⟩
  have : FirstCountableTopology X := hq.firstCountableTopology
  have : FirstCountableTopology Y := e.isInducing.firstCountableTopology
  have : (uniformity Y).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : T2Space Y := (positiveRealExponentialDecay_isEmbedding I hne).t2Space
  exact UniformSpace.metrizableSpace

/-- Paper: Lemma D.3.2.3(1), p. 801. The positive-real decay space is Fréchet. -/
theorem positiveRealExponentialDecay_frechet (hInt : OrdConnected I) (hne : I.Nonempty) :
    IsFrechetTVS E := by
  exact ⟨inferInstance, inferInstance, exponentialDecay_metrizable I hInt hne,
    positiveRealExponentialDecay_complete I hne⟩

/-- Paper: Lemma D.3.2.3(1), p. 801. The positive-real decay space is nuclear. -/
theorem positiveRealExponentialDecay_nuclear (hInt : OrdConnected I) (hne : I.Nonempty) :
    IsNuclearTVS E := by sorry

/-- Paper: Lemma D.3.2.3(1), p. 801. The positive-real decay space has the
Montel property and is barrelled. -/
theorem positiveRealExponentialDecay_montel (hInt : OrdConnected I) (hne : I.Nonempty) :
    BarrelledSpace ℂ E ∧ MontelSpace ℂ E := by
  have : MetrizableSpace E := exponentialDecay_metrizable I hInt hne
  have : CompleteSpace E := positiveRealExponentialDecay_complete I hne
  have : (uniformity E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : MontelSpace ℂ 𝓢(ℝ, ℂ) := schwartzMap_real_montel
  refine ⟨inferInstance, ⟨fun S hclosed hS ↦ ?_⟩⟩
  let T : E →ₗ[ℂ] (I → 𝓢(ℝ, ℂ)) := LinearMap.pi (logExponentialDecayTwist I)
  have hT : IsEmbedding T := positiveRealExponentialDecay_isEmbedding I hne
  have hu := AddMonoidHom.isUniformInducing_of_isInducing (f := T.toAddMonoidHom) hT.isInducing
  let K (a : I) := closure (logExponentialDecayTwist I a '' S)
  have hK (a : I) : IsCompact (K a) := by
    let L : E →L[ℂ] 𝓢(ℝ, ℂ) := ⟨logExponentialDecayTwist I a, (continuous_apply a).comp hT.continuous⟩
    exact MontelSpace.isCompact_of_isClosed_of_isVonNBounded ℂ isClosed_closure (hS.image L).closure
  apply TotallyBounded.isCompact_of_isClosed _ hclosed
  apply (totallyBounded_image_iff hu).mp
  apply (isCompact_univ_pi hK).totallyBounded.subset
  rintro _ ⟨f, hf, rfl⟩ a _
  exact subset_closure (mem_image_of_mem _ hf)

/-- Paper: Lemma D.3.2.3(2), p. 801. The strong dual is complete. -/
theorem positiveRealExponentialDecay_strongDual_complete (hInt : OrdConnected I) (hne : I.Nonempty) :
    CompleteSpace D := by
  obtain ⟨_, _, hmetric, _⟩ := positiveRealExponentialDecay_frechet I hInt hne
  infer_instance

/-- Paper: Lemma D.3.2.3(2), p. 801. The strong dual is nuclear. -/
theorem positiveRealExponentialDecay_strongDual_nuclear (hInt : OrdConnected I) (hne : I.Nonempty) :
    IsNuclearTVS D := by sorry

/-- Paper: Lemma D.3.2.3(2), p. 801. The strong dual has the Montel
property and is barrelled. -/
theorem positiveRealExponentialDecay_strongDual_montel (hInt : OrdConnected I) (hne : I.Nonempty) :
    BarrelledSpace ℂ D ∧ MontelSpace ℂ D := by sorry

/-- Paper: Lemma D.3.2.3(3), p. 801. If zero lies in I, the zero-weight
profile is a continuous linear inclusion into the ordinary Schwartz space. -/
theorem positiveRealExponentialDecay_continuous_inclusion (h0 : 0 ∈ I) :
    ∃ T : E →L[ℂ] 𝓢(ℝ, ℂ), Injective T ∧ ∀ f x, T f x = f.val x := by
  let a : I := ⟨0, h0⟩
  have hc := (continuous_apply a).comp (positiveRealExponentialDecay_isEmbedding I ⟨0, h0⟩).continuous
  let T : E →L[ℂ] 𝓢(ℝ, ℂ) := ⟨logExponentialDecayTwist I a, hc⟩
  have hT (f : E) (x : ℝ) : T f x = f.val x := by
    change logExponentialDecayTwist I a f x = _
    rw [logExponentialDecayTwist_apply I a f x]
    simp [a]
  refine ⟨T, ?_, hT⟩
  intro f g h
  apply Subtype.ext
  funext x
  rw [← hT f x, ← hT g x, h]

-- TODO(prerequisite): Lemma D.3.2.3(4–6) needs the three independently defined
-- subspaces from §B.2.1.1, Definition B.2.1.1.

/-- Paper: Proposition D.3.2.5, p. 802. On the strip, the positive-real Mellin
integral converges absolutely. The profile is pulled back by the real logarithm. -/
theorem positiveRealExponentialDecay_mellinConvergent (f : E) (s : ℂ) (hs : s.re ∈ I) :
    MellinConvergent (fun t ↦ f.val (Real.log t)) s := by
  apply mellinConvergent_of_integrable_logWeight
  have h : Integrable (fun x : ℝ ↦ logExponentialDecayTwist I ⟨s.re, hs⟩ f x) volume :=
    (logExponentialDecayTwist I ⟨s.re, hs⟩ f).integrable
  exact h.congr (Eventually.of_forall fun x ↦ logExponentialDecayTwist_apply I ⟨s.re, hs⟩ f x)

section MellinIsomorphism

open scoped Asymptotics FourierTransform

local notation "linePoint" => (fun (a y : ℝ) ↦ (a : ℂ) + y * Complex.I)
local notation "profile" => (fun (f : ℝ → ℂ) (t : ℝ) ↦ f (Real.log t))

/-- The Fourier argument corresponding to a unit of imaginary Mellin height. -/
private def fourierFrequencyScale :=
  (LinearEquiv.smulOfNeZero ℝ ℝ (2 * Real.pi)⁻¹
    (inv_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero))).toContinuousLinearEquiv

/-- Paper: Proposition D.3.2.5, p. 802. Reflection, Fourier transform, and rescaling
turn an exponential twist into its vertical Mellin trace. -/
private def mellinLineEquiv : 𝓢(ℝ, ℂ) ≃L[ℂ] 𝓢(ℝ, ℂ) :=
  (schwartzChangeVariable ℂ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv).trans
    ((FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ)).trans (schwartzChangeVariable ℂ fourierFrequencyScale))

private theorem mellinLineEquiv_twist {I : Set ℝ} (a : I) (f : logExponentialDecaySubmodule I) (y : ℝ) :
    mellinLineEquiv (logExponentialDecayTwist I a f) y = mellin (profile f.val) (linePoint a y) := by
  let g := logExponentialDecayTwist I a f
  let r := schwartzChangeVariable ℂ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv g
  change (𝓕 r) ((2 * Real.pi)⁻¹ * y) = _
  rw [SchwartzMap.fourier_coe, mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
    neg_zero, add_zero, Complex.add_im, Complex.mul_I_im, zero_add, Real.log_exp, div_eq_inv_mul]
  apply congrArg (fun h : ℝ → ℂ ↦ 𝓕 h ((2 * Real.pi)⁻¹ * y))
  funext x
  change logExponentialDecayTwist I a f (-x) = _
  rw [logExponentialDecayTwist_apply I a f (-x)]
  simp only [Complex.real_smul, mul_neg, neg_mul]

private theorem mellinLineEquiv_symm_apply {F : ℂ → ℂ} (a : ℝ) (g : 𝓢(ℝ, ℂ))
    (hg : ∀ y, g y = F (linePoint a y)) (x : ℝ) :
    mellinLineEquiv.symm g x = (Real.exp (a * x) : ℂ) * mellinInv a F (Real.exp x) := by
  let r := (schwartzChangeVariable ℂ fourierFrequencyScale).symm g
  change (𝓕⁻ r) (-x) = _
  rw [SchwartzMap.fourierInv_coe, mellinInv_eq_fourierInv a F (Real.exp_pos x), Real.log_exp]
  have eq : ⇑r = (fun y : ℝ ↦ F (a + 2 * (Real.pi : ℂ) * y * Complex.I)) := by
    funext y
    change g (((2 * Real.pi)⁻¹)⁻¹ * y) = _
    rw [inv_inv, hg]
    push_cast
    rfl
  rw [eq, smul_eq_mul, ← mul_assoc]
  have hpow : ((Real.exp x : ℝ) : ℂ) ^ (-(a : ℂ)) = (Real.exp (-(a * x)) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hpow, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

private theorem mellinProfile_differentiable {I : Set ℝ} (hI : IsOpen I)
    (f : logExponentialDecaySubmodule I) : DifferentiableOn ℂ (mellin (profile f.val)) (Complex.re ⁻¹' I) := by
  intro z hz
  let a : I := ⟨z.re, hz⟩
  have cont : Continuous f.val := by
    have eq : f.val = (fun u : ℝ ↦ (Real.exp (-((a : ℝ) * u)) : ℂ) * logExponentialDecayTwist I a f u) := by
      funext x
      rw [logExponentialDecayTwist_apply I a f x, ← mul_assoc, ← Complex.ofReal_mul,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]
    rw [eq]
    exact (by fun_prop : Continuous (fun u : ℝ ↦ (Real.exp (-((a : ℝ) * u)) : ℂ))).mul
      (logExponentialDecayTwist I a f).continuous
  obtain ⟨l, r, hl, hr⟩ := exists_bracketing_lines hI a
  have hloc : LocallyIntegrableOn (profile f.val) (Ioi 0) volume :=
    (cont.comp_continuousOn (Real.continuousOn_log.mono (fun x hx ↦ ne_of_gt hx))).locallyIntegrableOn measurableSet_Ioi
  have bound (c : I) {L : Filter ℝ} (hL : ∀ᶠ t in L, 0 < t) :
      profile f.val =O[L] (fun t : ℝ ↦ t ^ (-(c : ℝ))) := by
    let g := logExponentialDecayTwist I c f
    apply Asymptotics.IsBigO.of_bound (SchwartzMap.seminorm ℂ 0 0 g)
    filter_upwards [hL] with t ht
    rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), Real.rpow_neg ht.le, ← div_eq_mul_inv,
      le_div_iff₀ (Real.rpow_pos_of_pos ht _), Real.rpow_def_of_pos ht, mul_comm (Real.log t)]
    simpa only [g, logExponentialDecayTwist_apply, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm] using g.norm_le_seminorm ℂ (Real.log t)
  exact (mellin_differentiableAt_of_isBigO_rpow hloc (bound r (eventually_gt_atTop 0)) hr
    (bound l self_mem_nhdsWithin) hl).differentiableWithinAt

private theorem mellinProfile_strip_bound {I : Set ℝ} (l r : I) (f : logExponentialDecaySubmodule I) :
    ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc (l : ℝ) r → ‖mellin (profile f.val) z‖ ≤ C := by
  let G (a : I) := logExponentialDecayTwist I a f
  let B (x : ℝ) := ‖G l (-x)‖ + ‖G r (-x)‖
  have hi (a : I) : Integrable (fun x : ℝ ↦ ‖G a (-x)‖) :=
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp
      ((G a).integrable (μ := volume)).norm.aestronglyMeasurable).2 (G a).integrable.norm
  refine ⟨∫ x, B x, fun z hz ↦ ?_⟩
  rw [mellin_eq_fourier]
  apply (Real.norm_fourier_le_integral_norm _ _).trans
  apply integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _) ((hi l).add (hi r))
  filter_upwards with x
  change ‖Real.exp (-z.re * x) • f.val (Real.log (Real.exp (-x)))‖ ≤ ‖G l (-x)‖ + ‖G r (-x)‖
  simp only [G, logExponentialDecayTwist_apply, norm_mul, Complex.norm_real, norm_smul, Real.log_exp,
    Real.norm_of_nonneg (Real.exp_pos _).le, mul_neg, ← neg_mul]
  rcases le_total x 0 with hx | hx
  · apply le_add_of_nonneg_of_le (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (neg_le_neg hz.2) hx)) (norm_nonneg _)
  · apply le_add_of_le_of_nonneg _ (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hz.1) hx)) (norm_nonneg _)

private theorem mellinProfile_weighted_edge {I : Set ℝ} (a : I) (k : ℕ) (f : logExponentialDecaySubmodule I) :
    ∃ C : ℝ, ∀ z : ℂ, z.re = a → ‖z ^ k * mellin (profile f.val) z‖ ≤ C := by
  let g := mellinLineEquiv (logExponentialDecayTwist I a f)
  let w := fun y : ℝ ↦ (linePoint a y)^k
  have hw : w.HasTemperateGrowth := by dsimp [w]; fun_prop
  let h := SchwartzMap.smulLeftCLM ℂ w g
  refine ⟨SchwartzMap.seminorm ℂ 0 0 h, fun z hz ↦ ?_⟩
  have heq : linePoint a z.im = z := hz ▸ Complex.re_add_im z
  have hval : h z.im = z ^ k * mellin (profile f.val) z := by
    change SchwartzMap.smulLeftCLM ℂ w g z.im = _
    rw [SchwartzMap.smulLeftCLM_apply_apply hw]
    change (linePoint a z.im)^k * mellinLineEquiv (logExponentialDecayTwist I a f) z.im = _
    rw [mellinLineEquiv_twist, heq]
  rw [← hval]
  exact h.norm_le_seminorm ℂ _

private theorem mellinProfile_mem_bergman {I : Set ℝ} (hI : IsOpen I)
    (f : logExponentialDecaySubmodule I) :
    (Complex.re ⁻¹' I).indicator (mellin (profile f.val)) ∈ schwartzBergmanSubmodule I := by
  let F := mellin (profile f.val)
  have hf := mellinProfile_differentiable hI f
  refine ⟨fun z hz ↦ indicator_of_notMem hz _, ?_, ?_⟩
  · exact hf.congr fun z hz ↦ indicator_of_mem hz _
  intro l r hlr hsub k
  let a : I := ⟨l, hsub (left_mem_Icc.mpr hlr)⟩
  let b : I := ⟨r, hsub (right_mem_Icc.mpr hlr)⟩
  obtain ⟨A, hA⟩ := mellinProfile_weighted_edge a k f
  obtain ⟨B, hB⟩ := mellinProfile_weighted_edge b k f
  refine ⟨max A B, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  change ‖z ^ k * (Complex.re ⁻¹' I).indicator F z‖ ≤ _
  rw [indicator_of_mem (show z ∈ Complex.re ⁻¹' I from hsub hz)]
  rcases hlr.eq_or_lt with heq | hlt
  · exact (hA z (show z.re = l by linarith [hz.1, hz.2])).trans (le_max_left _ _)
  have hd : DiffContOnCl ℂ F (Complex.re ⁻¹' Ioo l r) := by
    refine ⟨hf.mono (preimage_mono (Ioo_subset_Icc_self.trans hsub)), ?_⟩
    rw [Complex.closure_preimage_re, closure_Ioo hlt.ne]
    exact hf.continuousOn.mono (preimage_mono hsub)
  obtain ⟨M, hM⟩ := mellinProfile_strip_bound a b f
  exact norm_pow_mul_le_on_verticalStrip hlt hd hM k
    (fun w hw ↦ (hA w hw).trans (le_max_left _ _)) (fun w hw ↦ (hB w hw).trans (le_max_right _ _)) z hz

/-- Moving the inverse contour between two lines preserves its value at every positive argument. -/
private theorem bergmanInv_shift_lt {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (F : SchwartzBergman I) (a b : I) (hab : (a : ℝ) < b) (u : ℝ) :
    mellinInv a F.val (Real.exp u) = mellinInv b F.val (Real.exp u) := by
  let z : ℂ := ((a : ℝ) + (b : ℝ)) / 2
  have haz : (a : ℝ) < z.re := by dsimp [z]; simp; linarith
  have hzb : z.re < (b : ℝ) := by dsimp [z]; simp; linarith
  let phase (w : ℂ) := Complex.exp (-(w * u))
  let K (w : ℂ) := phase w * F.val w
  let G (w : ℂ) := (w - z) * K w
  have hphase (w : ℂ) : ‖phase w‖ = Real.exp (-w.re * u) := by simp [phase, Complex.norm_exp, Complex.mul_re]
  have hpow (w : ℂ) : ((Real.exp u : ℝ) : ℂ) ^ (-w) = phase w := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    dsimp [phase]
    ring_nf
  have line (s : I) : Integrable (fun y ↦ K (linePoint s y)) := by
    obtain ⟨T, hT, _⟩ := schwartzBergman_schwartzLine_topology I hI hInt ⟨s, s.property⟩
    have heq (y : ℝ) : T F s y = F.val (linePoint s y) := by simpa [weightedVerticalTrace] using hT F s y
    have htrace : Integrable (fun y : ℝ ↦ F.val (linePoint s y)) :=
      (T F s).integrable.congr (.of_forall heq)
    have hc : Continuous (fun y : ℝ ↦ phase (linePoint s y)) := by dsimp [phase]; fun_prop
    have hb (y : ℝ) : ‖phase (linePoint s y)‖ ≤ Real.exp (-(s : ℝ) * u) := by rw [hphase]; simp
    exact htrace.bdd_mul hc.aestronglyMeasurable (.of_forall hb)
  have eqline (s : I) (hs : (s : ℝ) ≠ z.re) (y : ℝ) : G (linePoint s y) / (linePoint s y - z) = K (linePoint s y) := by
    have hne : linePoint s y ≠ z := fun he ↦ hs (by simpa using congrArg Complex.re he)
    dsimp only [G]
    field_simp [sub_ne_zero.mpr hne]
  obtain ⟨l, _, hla, _⟩ := exists_bracketing_lines hI a
  obtain ⟨_, r, _, hbr⟩ := exists_bracketing_lines hI b
  have hG : DifferentiableOn ℂ G (Complex.re ⁻¹' Ioo (l : ℝ) r) :=
    (differentiable_id.sub_const z).differentiableOn.mul ((by dsimp [phase]; fun_prop : Differentiable ℂ phase).differentiableOn.mul
      (F.property.2.1.mono (preimage_mono (Ioo_subset_Icc_self.trans (hInt.out l.property r.property)))))
  obtain ⟨A,hA⟩ := F.property.2.2 a b hab.le (hInt.out a.property b.property) 1
  obtain ⟨B,hB⟩ := F.property.2.2 a b hab.le (hInt.out a.property b.property) 2
  obtain ⟨P,hP⟩ := (isCompact_Icc (a := (a : ℝ)) (b := (b : ℝ))).bddAbove_image
    (f := fun s : ℝ ↦ Real.exp (-s * u)) (by fun_prop)
  let C := max P 0 * (max B 0 + ‖z‖ * max A 0)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdec : ∀ᶠ y : ℝ in comap abs atTop, ∀ s ∈ Icc (a : ℝ) b, ‖G (linePoint s y)‖ ≤ C / |y| := by
    have ht : Tendsto (abs : ℝ → ℝ) (comap abs atTop) atTop := tendsto_comap
    filter_upwards [ht.eventually (eventually_gt_atTop 0)] with y hy s hs
    let w := linePoint s y
    have hw : w ∈ Complex.re ⁻¹' Icc (a : ℝ) b := by simpa [w] using hs
    have him : |y| ≤ ‖w‖ := by simpa [w] using Complex.abs_im_le_norm w
    have ha := hA (mem_image_of_mem _ hw)
    have hb := hB (mem_image_of_mem _ hw)
    simp only [pow_one, norm_mul, norm_pow] at ha hb
    have hp : ‖phase w‖ ≤ max P 0 := (hphase w).le.trans
      ((hP (mem_image_of_mem _ hw)).trans (le_max_left _ _))
    apply (le_div_iff₀ hy).mpr
    calc ‖G w‖ * |y| = ‖phase w‖ * (‖w-z‖ * |y| * ‖F.val w‖) := by simp only [G,K,norm_mul]; ring
      _ ≤ max P 0 * ((‖w‖ + ‖z‖) * ‖w‖ * ‖F.val w‖) := by gcongr; exact norm_sub_le _ _
      _ ≤ C := by
        apply mul_le_mul_of_nonneg_left _ (le_max_right P 0)
        calc _ = ‖w‖ ^ 2 * ‖F.val w‖ + ‖z‖ * (‖w‖ * ‖F.val w‖) := by ring
          _ ≤ _ := add_le_add (hb.trans (le_max_left _ _))
            (mul_le_mul_of_nonneg_left (ha.trans (le_max_left _ _)) (norm_nonneg _))
  have h := verticalCauchyIntegral_sub_eq hG hla hbr ⟨haz,hzb⟩ hC hdec
    (by simpa only [Complex.VerticalIntegrable, eqline a haz.ne] using line a)
    (by simpa only [Complex.VerticalIntegrable, eqline b hzb.ne'] using line b)
  simp only [eqline b hzb.ne', eqline a haz.ne] at h
  have hi : (∫ y : ℝ, K (linePoint b y)) = ∫ y : ℝ, K (linePoint a y) :=
    sub_eq_zero.mp (by simpa [G] using h)
  simp only [mellinInv, hpow, smul_eq_mul]
  exact congrArg (fun v : ℂ ↦ (1 / (2 * Real.pi) : ℝ) • v) hi.symm

private theorem bergmanInv_shift {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (F : SchwartzBergman I) (a b : I) (u : ℝ) :
    mellinInv a F.val (Real.exp u) = mellinInv b F.val (Real.exp u) := by
  rcases lt_trichotomy (a : ℝ) (b : ℝ) with h | h | h
  · exact bergmanInv_shift_lt hI hInt F a b h u
  · rw [h]
  · exact (bergmanInv_shift_lt hI hInt F b a h u).symm

/-- The Mellin transform of a logarithmic profile, extended by zero outside the strip. -/
private def stripMellinLinear {I : Set ℝ} (hI : IsOpen I) : PositiveRealExponentialDecay I →ₗ[ℂ] SchwartzBergman I := by
  let B (f : PositiveRealExponentialDecay I) : SchwartzBergman I :=
    ⟨(Complex.re ⁻¹' I).indicator (mellin (profile f.val)), mellinProfile_mem_bergman hI f⟩
  let L (a : I) : PositiveRealExponentialDecay I →ₗ[ℂ] 𝓢(ℝ, ℂ) :=
    mellinLineEquiv.toLinearMap.comp (logExponentialDecayTwist I a)
  have hv (f : PositiveRealExponentialDecay I) (z : ℂ) (hz : z.re ∈ I) :
      (B f).val z = L ⟨z.re, hz⟩ f z.im := by
    change (Complex.re ⁻¹' I).indicator _ z = mellinLineEquiv (logExponentialDecayTwist I _ f) z.im
    rw [indicator_of_mem (show z ∈ Complex.re ⁻¹' I from hz), mellinLineEquiv_twist ⟨z.re, hz⟩ f z.im]
    simp [Complex.re_add_im]
  refine ⟨⟨B, ?_⟩, ?_⟩
  · intro f g
    apply Subtype.ext
    funext z
    change (B (f+g)).val z = (B f).val z + (B g).val z
    by_cases hz : z.re ∈ I
    · rw [hv _ _ hz, hv f _ hz, hv g _ hz, map_add]; rfl
    · simp [B, indicator_of_notMem (show z ∉ Complex.re ⁻¹' I from hz)]
  · intro c f
    apply Subtype.ext
    funext z
    change (B (c • f)).val z = c • (B f).val z
    by_cases hz : z.re ∈ I
    · rw [hv _ _ hz, hv f _ hz, map_smul]; rfl
    · simp [B, indicator_of_notMem (show z ∉ Complex.re ⁻¹' I from hz)]

private theorem stripMellinLinear_apply {I : Set ℝ} (hI : IsOpen I)
    (f : PositiveRealExponentialDecay I) (s : ℂ) (hs : s.re ∈ I) :
    (stripMellinLinear hI f).val s = mellin (profile f.val) s :=
  indicator_of_mem (show s ∈ Complex.re ⁻¹' I from hs) _

/-- Paper: Proposition D.3.2.5, p. 802. The Mellin integral induces a unique
continuous linear equivalence with the Schwartz–Bergman space on the strip. -/
theorem existsUnique_positiveRealFourierMellin (hOpen : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) :
    ∃! M : E ≃L[ℂ] SchwartzBergman I, ∀ (f : E) (s : ℂ), s.re ∈ I →
      (M f).val s = mellin (fun t ↦ f.val (Real.log t)) s := by
  let M := stripMellinLinear hOpen
  let U := mellinLineEquiv
  obtain ⟨T, hval, hT⟩ := schwartzBergman_schwartzLine_topology I hOpen hInt hne
  have hline (F : SchwartzBergman I) (a : I) (y : ℝ) : T F a y = F.val (linePoint a y) := by
    simpa only [weightedVerticalTrace, pow_zero, one_mul] using hval F a y
  have hcomm (f : PositiveRealExponentialDecay I) (a : I) : T (M f) a = U (logExponentialDecayTwist I a f) := by
    ext y
    rw [hline, show (M f).val (linePoint a y) = _ from stripMellinLinear_apply hOpen f _ (by simp)]
    exact (mellinLineEquiv_twist a f y).symm
  have hE := positiveRealExponentialDecay_isEmbedding I hne
  have inj : Injective M := by
    intro f g h
    apply hE.injective
    funext a
    apply U.injective
    rw [← hcomm, ← hcomm, h]
  have surj : Surjective M := by
    intro F
    obtain ⟨c,hc⟩ := hne
    let f (u : ℝ) := mellinInv c F.val (Real.exp u)
    have htw (a : I) (u : ℝ) : U.symm (T F a) u = (Real.exp ((a : ℝ) * u) : ℂ) * f u := by
      rw [mellinLineEquiv_symm_apply a (T F a) (hline F a)]
      exact congrArg (_ * ·) (bergmanInv_shift hOpen hInt F a ⟨c,hc⟩ u)
    have hf : f ∈ logExponentialDecaySubmodule I := by
      apply (Submodule.mem_iInf _).mpr
      intro a
      exact ⟨U.symm (T F a), funext (htw a)⟩
    let g : PositiveRealExponentialDecay I := ⟨f,hf⟩
    have hg (a : I) : logExponentialDecayTwist I a g = U.symm (T F a) := by
      ext u
      exact (logExponentialDecayTwist_apply I a g u).trans (htw a u).symm
    refine ⟨g, hT.injective ?_⟩
    funext a
    rw [hcomm, hg, U.apply_symm_apply]
  let e := LinearEquiv.ofBijective M ⟨inj,surj⟩
  let A : PositiveRealExponentialDecay I ≃L[ℂ] SchwartzBergman I := {
    toLinearEquiv := e
    continuous_toFun := by
      apply hT.continuous_iff.mpr
      apply continuous_pi
      intro a
      exact (U.continuous.comp ((continuous_apply a).comp hE.continuous)).congr fun f ↦ (hcomm f a).symm
    continuous_invFun := by
      apply hE.continuous_iff.mpr
      apply continuous_pi
      intro a
      apply (U.symm.continuous.comp ((continuous_apply a).comp hT.continuous)).congr
      intro F
      change U.symm (T F a) = logExponentialDecayTwist I a (e.symm F)
      apply U.injective
      rw [U.apply_symm_apply, ← hcomm]
      exact congrArg (fun G ↦ T G a) (e.apply_symm_apply F).symm }
  refine ⟨A, stripMellinLinear_apply hOpen, ?_⟩
  intro A' hA'
  apply ContinuousLinearEquiv.ext
  funext f
  apply hT.injective
  funext a
  ext y
  rw [hline, hline, hA' f _ (by simp)]
  exact (stripMellinLinear_apply hOpen f _ (by simp)).symm

end MellinIsomorphism

/-- Paper: Definition D.3.2.6, p. 803. The Fourier–Mellin transform is
the continuous linear equivalence furnished by the Mellin integral. -/
def positiveRealFourierMellin (hOpen : IsOpen I) (hInt : OrdConnected I) (hne : I.Nonempty) :
    E ≃L[ℂ] SchwartzBergman I :=
  Classical.choose (existsUnique_positiveRealFourierMellin I hOpen hInt hne).exists

/-- Paper: Lemma D.3.1.2, p. 799. The Schwartz–Bergman space is Fréchet. -/
theorem schwartzBergman_frechet (I : Set ℝ) (hI : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) : IsFrechetTVS (SchwartzBergman I) := by
  let M := positiveRealFourierMellin I hI hInt hne
  obtain ⟨_, _, hmetr, hcomp⟩ := positiveRealExponentialDecay_frechet I hInt hne
  have : MetrizableSpace (PositiveRealExponentialDecay I) := hmetr
  refine ⟨inferInstance, inferInstance, M.symm.toHomeomorph.isEmbedding.metrizableSpace, ?_⟩
  exact (M.isUniformEmbedding.isUniformInducing.completeSpace_congr M.surjective).mp hcomp

/-- Paper: Definition D.3.2.6, p. 803. Evaluation of the Fourier–Mellin
transform on the strip gives the absolutely convergent Mellin integral. -/
theorem positiveRealFourierMellin_apply (hOpen : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) (f : E) (s : ℂ) (hs : s.re ∈ I) :
    (positiveRealFourierMellin I hOpen hInt hne f).val s =
      mellin (fun t ↦ f.val (Real.log t)) s := by
  exact Classical.choose_spec (existsUnique_positiveRealFourierMellin I hOpen hInt hne).exists f s hs

/-- Paper: (D.3.2.3–4), p. 803. In logarithmic coordinates the weighted
L² norm is the norm of this exponentially and polynomially weighted derivative. -/
def exponentialDecayL2Integrand (a b : ℝ) (m : ℕ) (f : PositiveRealExponentialDecay univ)
    (x : ℝ) : ℂ :=
  ((Real.exp (a * |x|) * |x| ^ b : ℝ) : ℂ) * iteratedDeriv m f.val x

/-- Paper: (D.3.2.3–4), p. 803. At b = 0 the logarithmic power disappears,
leaving the pure exponential weight. -/
theorem exponentialDecayL2Integrand_zero_log (a : ℝ) (m : ℕ)
    (f : PositiveRealExponentialDecay univ) (x : ℝ) :
    exponentialDecayL2Integrand a 0 m f x =
      (Real.exp (a * |x|) : ℂ) * iteratedDeriv m f.val x := by sorry

private def decayTwistCLM (c : ℝ) : PositiveRealExponentialDecay univ →L[ℂ] 𝓢(ℝ, ℂ) :=
  ⟨logExponentialDecayTwist univ ⟨c, mem_univ c⟩,
    (continuous_apply (⟨c, mem_univ c⟩ : (univ : Set ℝ))).comp
      (positiveRealExponentialDecay_isEmbedding univ univ_nonempty).continuous⟩

private theorem decayProfile_smooth (f : PositiveRealExponentialDecay univ) : ContDiff ℝ ∞ f.val := by
  have h : ⇑(decayTwistCLM 0 f) = f.val := by
    funext x
    change logExponentialDecayTwist univ ⟨0, _⟩ f x = _
    simpa only [Subtype.coe_mk, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] using
      logExponentialDecayTwist_apply univ ⟨0, mem_univ (0 : ℝ)⟩ f x
  rw [← h]
  exact (decayTwistCLM 0 f).smooth _

/-- Differentiate the profile before applying the exponential twist. -/
private def decayWeightedDeriv (c : ℝ) (m : ℕ) : PositiveRealExponentialDecay univ →L[ℂ] 𝓢(ℝ, ℂ) :=
  ((SchwartzMap.derivCLM ℂ ℂ - (c : ℂ) • ContinuousLinearMap.id ℂ _) ^ m).comp (decayTwistCLM c)

private theorem decayWeightedDeriv_apply (c : ℝ) (m : ℕ) (f : PositiveRealExponentialDecay univ) :
    ⇑(decayWeightedDeriv c m f) =
      fun x : ℝ ↦ (Real.exp (c * x) : ℂ) * iteratedDeriv m f.val x := by
  induction m with
  | zero =>
    funext x
    exact logExponentialDecayTwist_apply univ ⟨c, mem_univ c⟩ f x
  | succ m ih =>
    funext x
    simp only [decayWeightedDeriv, pow_succ', ContinuousLinearMap.comp_apply] at ih ⊢
    change deriv (⇑(decayWeightedDeriv c m f)) x - c * decayWeightedDeriv c m f x = _
    change ⇑(decayWeightedDeriv c m f) = _ at ih
    rw [ih, iteratedDeriv_succ]
    have he : HasDerivAt (fun x : ℝ ↦ (Real.exp (c * x) : ℂ)) ((c * Real.exp (c * x) : ℝ) : ℂ) x := by
      apply HasDerivAt.ofReal_comp
      simpa [mul_comm] using ((hasDerivAt_id x).const_mul c).exp
    have hd := ((decayProfile_smooth f).differentiable_iteratedDeriv m
      (by exact_mod_cast ENat.natCast_lt_top m)) x
    rw [(he.fun_mul hd.hasDerivAt).deriv]
    push_cast
    ring

/-- The polynomially weighted exponential envelope belongs to L² on both half-lines. -/
private theorem memLp_decayEnvelope (s b : ℝ) (hs : 0 < s) (hb : 0 ≤ b) :
    MemLp (fun x : ℝ ↦ |x| ^ b * Real.exp (-s * |x|)) 2 volume := by
  have hcont : Continuous (fun x : ℝ ↦ |x| ^ b * Real.exp (-s * |x|)) :=
    ((Real.continuous_rpow_const hb).comp continuous_abs).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs))
  apply (integrable_norm_rpow_iff hcont.aestronglyMeasurable (by norm_num) (by norm_num)).mp
  have hpos : IntegrableOn
      (fun x : ℝ ↦ ‖|x| ^ b * Real.exp (-s * |x|)‖ ^ (2 : ℝ≥0∞).toReal) (Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (b := 2 * s) (s := b * 2)
      (by linarith) (by norm_num) (by positivity)).congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
    change 0 < x at hx
    dsimp only
    rw [abs_of_pos hx, Real.norm_of_nonneg (by positivity), ENNReal.toReal_ofNat,
      Real.rpow_two, mul_pow, Real.rpow_one, ← Real.rpow_mul_natCast hx.le, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hpos⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simpa [Function.comp_def, neg_preimage] using hpos

private def decayL2ProfileMap (a b : ℝ) (m : ℕ) : PositiveRealExponentialDecay univ →ₗ[ℂ] (ℝ → ℂ) :=
  (LinearMap.mulLeft ℂ fun x : ℝ ↦ ((Real.exp (a * |x|) * |x| ^ b : ℝ) : ℂ)).comp
    (realSchwartzCoe.comp (decayWeightedDeriv 0 m).toLinearMap)

private theorem decayL2ProfileMap_apply (a b : ℝ) (m : ℕ) (f : PositiveRealExponentialDecay univ)
    (x : ℝ) :
    decayL2ProfileMap a b m f x = exponentialDecayL2Integrand a b m f x := by
  change _ * (decayWeightedDeriv 0 m f x) = _
  rw [congrFun (decayWeightedDeriv_apply 0 m f) x]
  simp [exponentialDecayL2Integrand]

/-- Paper: Lemma D.3.2.7(1), p. 803. Each weighted derivative is in L² and its
L² norm defines a continuous seminorm. The choice b = 0 includes (D.3.2.3). -/
theorem exponentialDecayL2_continuous_seminorm (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (m : ℕ) :
    let w := exponentialDecayL2Integrand a b m
    (∀ f, MemLp (w f) 2 volume) ∧
      ∃ p : Seminorm ℂ (PositiveRealExponentialDecay univ), Continuous p ∧
        ∀ f, ENNReal.ofReal (p f) = eLpNorm (w f) 2 volume := by
  let T := decayL2ProfileMap a b m
  have hT (f : PositiveRealExponentialDecay univ) : T f = exponentialDecayL2Integrand a b m f :=
    funext (decayL2ProfileMap_apply a b m f)
  let H (x : ℝ) := |x| ^ b * Real.exp (-a * |x|)
  have hH : MemLp H 2 volume := memLp_decayEnvelope a b ha hb
  let q (c : ℝ) := (SchwartzMap.seminorm ℂ 0 0).comp (decayWeightedDeriv c m).toLinearMap
  let Q := q (2 * a) + q (-(2 * a))
  have hc (c : ℝ) : Continuous (q c) :=
    ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (0, 0)).comp
      (decayWeightedDeriv c m).continuous
  have hQ : Continuous Q := (hc _).add (hc _)
  have hmeas (f : PositiveRealExponentialDecay univ) : AEStronglyMeasurable (T f) volume := by
    rw [hT]
    apply Continuous.aestronglyMeasurable
    exact (Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
        ((Real.continuous_rpow_const hb).comp continuous_abs))).mul
      ((decayProfile_smooth f).continuous_iteratedDeriv m (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤)))
  have hbound (f : PositiveRealExponentialDecay univ) : ∀ᵐ x ∂volume, ‖T f x‖ ≤ Q f * ‖H x‖ := by
    apply Eventually.of_forall
    intro x
    have hside (c : ℝ) (hx : c * x = (2 * a) * |x|) : ‖T f x‖ ≤ q c f * ‖H x‖ := by
      have he : Real.exp (a * |x|) = Real.exp (c * x) * Real.exp (-a * |x|) := by
        rw [← Real.exp_add, hx]
        congr 1
        ring
      have h := (decayWeightedDeriv c m f).norm_le_seminorm ℂ x
      change ‖decayWeightedDeriv c m f x‖ ≤ q c f at h
      calc
        ‖T f x‖ = ‖decayWeightedDeriv c m f x‖ * ‖H x‖ := by
          rw [hT, congrFun (decayWeightedDeriv_apply c m f) x]
          simp only [exponentialDecayL2Integrand, H, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (Real.exp_pos _).le,
            Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg x) b), he]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    rcases le_total 0 x with hx | hx
    · exact (hside (2 * a) (by rw [abs_of_nonneg hx])).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (apply_nonneg _ _)) (norm_nonneg _))
    · exact (hside (-(2 * a)) (by rw [abs_of_nonpos hx]; ring)).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (apply_nonneg _ _)) (norm_nonneg _))
  have hm (f : PositiveRealExponentialDecay univ) : MemLp (T f) 2 volume :=
    hH.of_le_mul (hmeas f) (hbound f)
  let L : PositiveRealExponentialDecay univ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
    { toFun := fun f ↦ (hm f).toLp (T f)
      map_add' := fun f g ↦ by simp only [map_add]; rfl
      map_smul' := fun c f ↦ by simp only [map_smul]; rfl }
  let p := (normSeminorm ℂ _).comp L
  have hp (f : PositiveRealExponentialDecay univ) : p f = (eLpNorm (T f) 2 volume).toReal :=
    Lp.norm_toLp _ (hm f)
  refine ⟨fun f ↦ hT f ▸ hm f, p, ?_, fun f ↦ ?_⟩
  · let C := (eLpNorm H 2 volume).toNNReal
    apply Seminorm.continuous_of_le (q := C • Q) (hQ.const_smul C)
    intro f
    rw [hp]
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hH.eLpNorm_ne_top)
      (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hmeas f) (hbound f) 2)
    change _ ≤ (eLpNorm H 2 volume).toReal * Q f
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (apply_nonneg Q f), mul_comm] using h
  · rw [hp, hT f, ENNReal.ofReal_toReal]
    exact (hT f ▸ hm f).eLpNorm_ne_top

/-- Paper: Lemma D.3.2.7(2), p. 803. Exponential weights on an unbounded sequence
of positive exponents generate the topology. -/
theorem exponentialDecayL2_generates (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hunbounded : ¬ BddAbove (range a)) :
    GeneratesLpSeminorms volume 2
      (fun (i : ℕ × ℕ) ↦ exponentialDecayL2Integrand (a i.1) 0 i.2) := by sorry

/-- Paper: Lemma D.3.2.7(3), p. 803. The same topology is generated by including
all nonnegative integer logarithmic weights. -/
theorem exponentialDecayL2_log_generates (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hunbounded : ¬ BddAbove (range a)) :
    GeneratesLpSeminorms volume 2
      (fun (i : ℕ × ℕ × ℕ) ↦ exponentialDecayL2Integrand (a i.1) i.2.1 i.2.2) := by sorry

end PositiveReal

section Modulated

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (I : Set ℝ)

/-- Paper: Definition D.3.3.1, p. 804. Multiply a function by the real power
of the modulation at each point. -/
def modulationWeight (a : ℝ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
  LinearMap.mulLeft ℂ (fun g : G ↦ (((m g).val : ℝ) ^ a : ℝ))

/-- Paper: Definition D.3.3.1, p. 804. Weighting at exponent zero is
the identity. -/
theorem modulationWeight_zero (f : G → ℂ) : modulationWeight m 0 f = f := by
  ext g
  simp [modulationWeight]

/-- Paper: Definition D.3.3.1, p. 804. All real twists with exponents in I
must lie in the Schwartz–Bruhat submodule.
Forward, backward and two-sided exponential decay use `Ici 0`, `Iic 0` and `univ`.
Deviation: Continuity follows from any one twist when I is nonempty. -/
def modulatedExponentialDecaySubmodule : Submodule ℂ (G → ℂ) :=
  ⨅ a : I, (schwartzBruhatSubmodule G).comap (modulationWeight m a)

/-- Paper: Definition D.3.3.1, p. 804. The exponent set containing only zero
recovers the ordinary Schwartz–Bruhat functions. -/
theorem modulatedExponentialDecaySubmodule_singleton_zero :
    modulatedExponentialDecaySubmodule m {0} = schwartzBruhatSubmodule G := by
  ext f
  simp only [modulatedExponentialDecaySubmodule, Submodule.mem_iInf, Submodule.mem_comap]
  constructor
  · intro h
    simpa [modulationWeight_zero] using h ⟨0, rfl⟩
  · rintro hf ⟨a, ha⟩
    obtain rfl : a = 0 := ha
    simpa [modulationWeight_zero] using hf

/-- Paper: (D.3.3.2), p. 805. The given exponent supplies the corresponding
Schwartz–Bruhat membership. -/
theorem modulationWeight_mem_schwartzBruhat (a : I) (f : modulatedExponentialDecaySubmodule m I) :
    modulationWeight m a f.val ∈ schwartzBruhatSubmodule G :=
  Submodule.mem_comap.1 (Submodule.mem_iInf _ |>.1 f.2 a)

/-- Paper: (D.3.3.2), p. 805. The linear map Tₐ sends a function in the decay
submodule to its weighted Schwartz–Bruhat function. -/
def modulatedExponentialDecayTwist (a : I) :
    modulatedExponentialDecaySubmodule m I →ₗ[ℂ] SchwartzBruhat G :=
  ((modulationWeight m a).comp (modulatedExponentialDecaySubmodule m I).subtype).codRestrict
    (schwartzBruhatSubmodule G) (modulationWeight_mem_schwartzBruhat m I a)

/-- Paper: (D.3.3.2), p. 805. The bundled twist evaluates to the pointwise
product with the power of the modulation. -/
theorem modulatedExponentialDecayTwist_apply (a : I) (f : modulatedExponentialDecaySubmodule m I)
    (g : G) :
    modulatedExponentialDecayTwist m I a f g = ((((m g).val : ℝ) ^ (a : ℝ) : ℝ) : ℂ) * f.val g :=
  rfl

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Paper: Definition D.3.3.1, p. 804. Inverse left translation preserves
the decay submodule. -/
theorem modulatedExponentialDecaySubmodule_translate (hm : IsModulation m) (hms : Surjective m)
    (g : G) (f : modulatedExponentialDecaySubmodule m I) :
    (fun x : G ↦ f.val (g⁻¹ * x)) ∈ modulatedExponentialDecaySubmodule m I := by sorry

/-- Paper: Lemma D.3.3.2, p. 804. If two exponent twists are Schwartz–Bruhat,
every intermediate exponent twist is Schwartz–Bruhat as well. -/
theorem modulationWeight_mem_schwartzBruhat_between (hm : IsModulation m) (hms : Surjective m)
    (f : G → ℂ) (a c b : ℝ) (hac : a < c) (hcb : c < b)
    (ha : modulationWeight m a f ∈ schwartzBruhatSubmodule G)
    (hb : modulationWeight m b f ∈ schwartzBruhatSubmodule G) :
    modulationWeight m c f ∈ schwartzBruhatSubmodule G := by sorry

-- TODO(paper-gap): The finite-generation wording in Definition D.3.3.3
-- refers to the annihilator in the dual of the norm-one subgroup. In
-- the full dual the opening compact-generation condition applies.
local notation "GoodCompact" => {k : Subgroup G // IsCompact (k : Set G) ∧
  IsCompactlyGeneratedGroup (lcaAnnihilator k)}

/-- Paper: Definition D.3.3.3, p. 805. The modulation is trivial on each
compact subgroup because the positive-real group has no nontrivial compact subgroup. -/
theorem compactSubgroup_le_modulation_ker (k : Subgroup G) (hk : IsCompact (k : Set G)) :
    k ≤ m.toMonoidHom.ker := by
  obtain ⟨y, hy, hmax⟩ := hk.exists_isMaxOn ⟨1, k.one_mem⟩
    (Units.continuous_val.comp m.continuous).continuousOn
  have bound (x : G) (hx : x ∈ k) : (m x).val ≤ 1 := by
    apply (mul_le_iff_le_one_right (Units.zero_lt (m y))).mp
    have h : (m (y * x)).val ≤ (m y).val := hmax (k.mul_mem hy hx)
    simpa only [map_mul, Units.val_mul] using h
  intro x hx
  apply Units.ext
  exact le_antisymm (bound x hx) (by simpa using bound x⁻¹ (k.inv_mem hx))

/-- Paper: Definition D.3.3.3, p. 805. The homomorphism induced by the
modulation on a compact-subgroup quotient is continuous. -/
theorem continuous_quotientModulation (k : Subgroup G) (hk : IsCompact (k : Set G)) :
    Continuous (QuotientGroup.lift k m.toMonoidHom (compactSubgroup_le_modulation_ker m k hk)) :=
  continuous_coinduced_dom.2 m.continuous

/-- Paper: Definition D.3.3.3, p. 805. Use the descended modulation to form
the projective system on the quotient by a compact subgroup. -/
def quotientModulation (k : Subgroup G) (hk : IsCompact (k : Set G)) : (G ⧸ k) →ₜ* ℝ≥0ˣ where
  toMonoidHom := QuotientGroup.lift k m.toMonoidHom (compactSubgroup_le_modulation_ker m k hk)
  continuous_toFun := continuous_quotientModulation m k hk

/-- Paper: Definition D.3.3.3, p. 805. The descended modulation agrees with
the original one on each coset representative. -/
theorem quotientModulation_apply (k : Subgroup G) (hk : IsCompact (k : Set G)) (g : G) :
    quotientModulation m k hk (g : G ⧸ k) = m g := rfl

/-- Paper: Definition D.3.3.3, p. 805. The stage S_I(k,G) carries the topology
induced by the Schwartz–Bruhat twists on G/k.
Deviation: The k-invariant functions are represented on the quotient. -/
abbrev ModulatedExponentialDecayStage (k : GoodCompact) :=
  let n := quotientModulation m k.val k.property.1
  WithGeneratingSeminorms (modulatedExponentialDecaySubmodule n I)
    (fun i : I × {p : Seminorm ℂ (SchwartzBruhat (G ⧸ k.val)) // Continuous p} ↦
      i.2.val.comp (modulatedExponentialDecayTwist n I i.1))

/-- Paper: Definition D.3.3.3, p. 805. Pulling a stage profile back along
the quotient map lands in the ambient decay submodule. -/
theorem modulatedExponentialDecayStage_pullback_mem (k : GoodCompact)
    (f : ModulatedExponentialDecayStage m I k) :
    (fun g : G ↦ f.val (g : G ⧸ k.val)) ∈ modulatedExponentialDecaySubmodule m I := by sorry

/-- Paper: (D.3.3.1), p. 805. The canonical stage map is pullback from G/k. -/
def modulatedExponentialDecayStageInclusion (k : GoodCompact) :
    ModulatedExponentialDecayStage m I k →ₗ[ℂ] modulatedExponentialDecaySubmodule m I :=
  ((LinearMap.pi fun g : G ↦ LinearMap.proj (g : G ⧸ k.val)).comp
    (modulatedExponentialDecaySubmodule (quotientModulation m k.val k.property.1) I).subtype
  ).codRestrict (modulatedExponentialDecaySubmodule m I)
    (modulatedExponentialDecayStage_pullback_mem m I k)

/-- Paper: (D.3.3.1), p. 805. A stage maps bijectively onto the k-invariant
functions in the ambient decay submodule. -/
theorem modulatedExponentialDecayStageInclusion_range (k : GoodCompact) :
    Injective (modulatedExponentialDecayStageInclusion m I k) ∧
      ∀ f : modulatedExponentialDecaySubmodule m I,
        f ∈ (modulatedExponentialDecayStageInclusion m I k).range ↔
          ∀ (g : G) (u : k.val), f.val (g * u.val) = f.val g := by sorry

/-- Paper: Definition D.3.3.3, p. 805. The topology of S_I(G) is the final
locally convex topology for the inclusions of the compact-subgroup stages. -/
abbrev ModulatedExponentialDecay :=
  WithGeneratingSeminorms (modulatedExponentialDecaySubmodule m I)
    (Subtype.val : {p : Seminorm ℂ (modulatedExponentialDecaySubmodule m I) //
      ∀ k : GoodCompact, Continuous (p ∘ modulatedExponentialDecayStageInclusion m I k)} → _)

/-- Paper: Definition D.3.3.3, p. 805. The stage inclusions exhaust the
underlying space. -/
theorem modulatedExponentialDecay_exists_stage (hm : IsModulation m) (hms : Surjective m)
    (hInt : OrdConnected I) (hne : I.Nonempty) :
    ∀ f : ModulatedExponentialDecay m I, ∃ k : GoodCompact,
      f ∈ (modulatedExponentialDecayStageInclusion m I k).range := by sorry

end Modulated

/-- Paper: Example D.3.3.4, p. 805. For the identity modulation, the inductive
space agrees with the positive-real projective space in logarithmic coordinates. -/
theorem identityModulationExponentialDecay_equiv (I : Set ℝ) (hInt : OrdConnected I)
    (hne : I.Nonempty) :
    ∃ e : PositiveRealExponentialDecay I ≃L[ℂ]
        ModulatedExponentialDecay (ContinuousMonoidHom.id ℝ≥0ˣ) I,
      ∀ (f : PositiveRealExponentialDecay I) (t : ℝ≥0ˣ),
        (e f).val t = f.val (Real.log (t.val : ℝ)) := by sorry

section ModulatedExamples

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
  [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)

local notation "GoodCompact" => {k : Subgroup G // IsCompact (k : Set G) ∧
  IsCompactlyGeneratedGroup (lcaAnnihilator k)}

include hm hms

/-- Paper: Example D.3.3.5, p. 805. Weighting by the difference of exponents
identifies the two singleton decay spaces.
Deviation: This includes the ordinary Schwartz–Bruhat case at exponent zero
via the continuous equivalence in the next declaration. -/
theorem modulatedExponentialDecay_singleton_equiv (a b : ℝ) :
    ∃ e : ModulatedExponentialDecay m {a} ≃L[ℂ] ModulatedExponentialDecay m {b},
      ∀ f, (e f).val = modulationWeight m (a - b) f.val := by sorry

/-- Paper: Example D.3.3.5, p. 805. Weighting by the given exponent identifies
the singleton decay space with the ordinary Schwartz–Bruhat space. -/
theorem modulatedExponentialDecay_singleton_schwartz (a : ℝ) :
    ∃ e : ModulatedExponentialDecay m {a} ≃L[ℂ] SchwartzBruhat G,
      ∀ f, (e f : G → ℂ) = modulationWeight m a f.val := by sorry

/-- Paper: Example D.3.3.5, p. 805. The diagonal map from a stage over a
compact interval to the two endpoint stages is a closed topological embedding. -/
theorem modulatedExponentialDecayStage_endpoints_closedEmbedding (k : GoodCompact)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ T : ModulatedExponentialDecayStage m (Icc a b) k →L[ℂ]
        ModulatedExponentialDecayStage m {a} k × ModulatedExponentialDecayStage m {b} k,
      IsClosedEmbedding T ∧ ∀ f, (T f).1.val = f.val ∧ (T f).2.val = f.val := by sorry

/-- Paper: Example D.3.3.5, p. 805. For a nonempty interval, each stage is Fréchet. -/
theorem modulatedExponentialDecayStage_frechet (I : Set ℝ) (hInt : OrdConnected I)
    (hne : I.Nonempty) (k : GoodCompact) :
    IsFrechetTVS (ModulatedExponentialDecayStage m I k) := by sorry

/-- Paper: Example D.3.3.5, p. 805. For a nonempty interval, each stage is nuclear. -/
theorem modulatedExponentialDecayStage_nuclear (I : Set ℝ) (hInt : OrdConnected I)
    (hne : I.Nonempty) (k : GoodCompact) :
    IsNuclearTVS (ModulatedExponentialDecayStage m I k) := by sorry

/-- Paper: Example D.3.3.5, p. 805. For a nonempty interval, each stage is separable. -/
theorem modulatedExponentialDecayStage_separable (I : Set ℝ) (hInt : OrdConnected I)
    (hne : I.Nonempty) (k : GoodCompact) :
    SeparableSpace (ModulatedExponentialDecayStage m I k) := by sorry

end ModulatedExamples

-- The remaining part starts with the transition maps at the end of Example
-- D.3.3.5, p. 805.
-- TODO(paper-gap): Proposition D.3.3.10(3) misses included endpoints when
-- J only accumulates at them. On [0,1], translates of a fixed smooth bump
-- centered at n and scaled by exp(-n) are bounded at every a < 1, while the
-- a = 1 twists have an unbounded first polynomial Schwartz seminorm.
-- TODO(paper-gap): In Theorem D.3.3.13 the tensor formula requires the
-- Haar measures on the group and compact factor to be chosen compatibly.

end RiemannMasullo
