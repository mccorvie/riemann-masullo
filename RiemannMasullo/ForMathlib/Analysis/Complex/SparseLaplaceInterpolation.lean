module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-! # Compactly supported interpolation at sparse complex frequencies

A smooth function supported in any given interval can have bilateral Laplace integral one
at a prescribed frequency and zero at every other frequency in a family whose reciprocal
heights are summable. The finite exceptional frequencies are removed by differentiation.
The remaining frequencies are removed by convolution with a compactly supported probability
measure. Its support length is bounded by the sum of the reciprocal vertical separations
multiplied by π.

This supplies test functions for the exterior sum in Masullo, Theorem 12.5.1.1, pp. 519–520
(issue #5571). The summability assumption is explicit. Whether the omitted exterior zero
terms always sum to zero remains open.
-/

public noncomputable section

open Set MeasureTheory Function Filter
open scoped ContDiff Convolution Topology

namespace RiemannMasullo

private def transform (g : ℝ → ℂ) (w : ℂ) : ℂ := ∫ x : ℝ, g x * Complex.exp (w * x)

private theorem integrable_weight (g : ℝ → ℂ) (hg : Continuous g) (hc : HasCompactSupport g)
    (w : ℂ) : Integrable (fun x : ℝ ↦ g x * Complex.exp (w * x)) :=
  (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right

private theorem exp_deriv (w : ℂ) (x : ℝ) : HasDerivAt
    (fun t : ℝ ↦ Complex.exp (w * t)) (w * Complex.exp (w * x)) x := by
  have h : HasDerivAt (fun t : ℝ ↦ w * (t : ℂ)) w x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul w
  simpa [mul_comm] using h.cexp

private theorem transform_deriv (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (w : ℂ) : transform (deriv g) w = -w * transform g w := by
  let e := fun t : ℝ ↦ Complex.exp (w * t)
  have h0 := integrable_weight g hg.continuous hc w
  have h1 := integrable_weight (deriv g) (hg.deriv' (n := ∞)).continuous hc.deriv w
  have h2 : Integrable (g * (fun x ↦ w * e x)) := by
    convert h0.const_mul w using 1
    ext x
    simp only [Pi.mul_apply, e]
    ring
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := g) (v := e)
    (u' := deriv g) (v' := fun x ↦ w * e x) (fun x _ ↦ (hg.differentiable (by simp) x).hasDerivAt)
    (fun x _ ↦ exp_deriv w x) h2 h1 h0
  have h3 : (fun x ↦ g x * (w * e x)) = fun x ↦ w * (g x * e x) := by funext x; ring
  rw [h3, integral_const_mul] at key
  change w * transform g w = -transform (deriv g) w at key
  linear_combination key

/-- Finite spectral filtering without enlarging the support of a smooth profile. -/
private theorem finite_filter (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (u : ℂ) (S : Finset ℂ) (hu : u ∉ S) :
    ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ tsupport h ⊆ tsupport g ∧
      transform h u = transform g u ∧ ∀ v ∈ S, transform h v = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨g, hg, hc, Subset.rfl, rfl, by simp⟩
  | @insert v S hv ih =>
    obtain ⟨f, hf, hfc, hsupp, hfu, hfS⟩ := ih fun h ↦ hu (Finset.mem_insert_of_mem h)
    have hvu : v - u ≠ 0 := sub_ne_zero.mpr (fun h ↦ hu (by simp [h]))
    let a := v / (v - u)
    let b := (v - u)⁻¹
    let h := fun x ↦ a * f x + b * deriv f x
    have hfd : ContDiff ℝ ∞ (deriv f) := hf.deriv'
    have hhc : HasCompactSupport h := (hfc.mul_left (f := fun _ ↦ a)).add hfc.deriv.mul_left
    have hhs : tsupport h ⊆ tsupport g := by
      refine (tsupport_add (fun x ↦ a * f x) (fun x ↦ b * deriv f x)).trans (union_subset ?_ ?_)
      · exact tsupport_mul_subset_right.trans hsupp
      · exact tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans hsupp)
    have hm (w : ℂ) : transform h w = (a - b * w) * transform f w := by
      have hpt : (fun x : ℝ ↦ h x * Complex.exp (w * x)) = fun x : ℝ ↦
          a * (f x * Complex.exp (w * x)) + b * (deriv f x * Complex.exp (w * x)) := by
        funext x; dsimp [h]; ring
      rw [transform, hpt, integral_add ((integrable_weight f hf.continuous hfc w).const_mul a)
        ((integrable_weight (deriv f) hfd.continuous hfc.deriv w).const_mul b),
        integral_const_mul, integral_const_mul]
      change a * transform f w + b * transform (deriv f) w = _
      rw [transform_deriv f hf hfc]
      ring
    refine ⟨h, (contDiff_const.mul hf).add (contDiff_const.mul hfd), hhc, hhs, ?_, ?_⟩
    · rw [hm, ← hfu]
      dsimp [a, b]; field_simp [hvu]
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hS
      · rw [hm]; dsimp [a, b]; ring
      · rw [hm, hfS w hS, mul_zero]

/-- Finite cancellability of continuous complex moments on one fixed compact space suffices
for a single probability measure to cancel all the moments, for an arbitrary index type. -/
private theorem probability_zero_moments {X ι : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (f : ι → C(X, ℂ))
    (hfin : ∀ s : Finset ι, ∃ μ : ProbabilityMeasure X, ∀ i ∈ s, ∫ x, f i x ∂μ = 0) :
    ∃ μ : ProbabilityMeasure X, ∀ i, ∫ x, f i x ∂μ = 0 := by
  let fr (i : ι) : C(X, ℝ) := ⟨fun x ↦ (f i x).re, Complex.continuous_re.comp (f i).continuous⟩
  let fi (i : ι) : C(X, ℝ) := ⟨fun x ↦ (f i x).im, Complex.continuous_im.comp (f i).continuous⟩
  let K (i : ι) : Set (ProbabilityMeasure X) :=
    {μ | (∫ x, fr i x ∂μ) = 0} ∩ {μ | (∫ x, fi i x ∂μ) = 0}
  have hK (i : ι) : IsClosed (K i) :=
    (isClosed_eq (ProbabilityMeasure.continuous_integral_continuousMap (fr i)) continuous_const).inter
      (isClosed_eq (ProbabilityMeasure.continuous_integral_continuousMap (fi i)) continuous_const)
  have hmem (μ : ProbabilityMeasure X) (i : ι) : μ ∈ K i ↔ ∫ x, f i x ∂μ = 0 := by
    have hint : Integrable (f i) (μ : Measure X) :=
      (f i).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    change (∫ x, RCLike.re (f i x) ∂μ) = 0 ∧ (∫ x, RCLike.im (f i x) ∂μ) = 0 ↔ _
    rw [integral_re hint, integral_im hint]
    exact ⟨fun h ↦ Complex.ext h.1 h.2, fun h ↦ by rw [h]; simp⟩
  obtain ⟨μ, hμ⟩ := CompactSpace.iInter_nonempty hK (fun s ↦ by
    obtain ⟨μ, hμ⟩ := hfin s
    exact ⟨μ, mem_iInter₂.mpr fun i hi ↦ (hmem μ i).2 (hμ i hi)⟩)
  exact ⟨μ, fun i ↦ (hmem μ i).1 (mem_iInter.mp hμ i)⟩

/-- Combining positive factors of bounded total support length annihilates every frequency. -/
private theorem probability_exp_filter {ι : Type*} (v : ι → ℂ) (a : ι → ℝ) (L : ℝ)
    (hL : ∀ s : Finset ι, ∑ j : s, a j ≤ L)
    (ν : (i : ι) → ProbabilityMeasure (Icc 0 (a i)))
    (hν : ∀ i, ∫ x : Icc 0 (a i), Complex.exp (v i * (x.val : ℂ)) ∂ν i = 0) :
    ∃ μ : ProbabilityMeasure (Icc 0 L), ∀ i, ∫ x : Icc 0 L, Complex.exp (v i * (x.val : ℂ)) ∂μ = 0 := by
  classical
  let g (i : ι) : C(Icc 0 L, ℂ) := ⟨fun x ↦ Complex.exp (v i * (x.val : ℂ)), by fun_prop⟩
  apply probability_zero_moments g
  intro s
  let X := (j : s) → Icc 0 (a j)
  let μs : (j : s) → Measure (Icc 0 (a j)) := fun j ↦ ν j
  let (j : s) : IsProbabilityMeasure (μs j) := (ν j).prop
  let prodμ : ProbabilityMeasure X := ⟨Measure.pi μs, inferInstance⟩
  let total (x : X) : Icc 0 L := ⟨∑ j : s, (x j).val,
    Finset.sum_nonneg fun j _ ↦ (x j).property.1,
    (Finset.sum_le_sum fun j _ ↦ (x j).property.2).trans (hL s)⟩
  have ht : Measurable total := by
    apply Measurable.subtype_mk
    exact Finset.measurable_sum _ fun j _ ↦ measurable_subtype_coe.comp (measurable_pi_apply j)
  refine ⟨prodμ.map total, fun i hi ↦ ?_⟩
  change ∫ x, g i x ∂(Measure.map total (Measure.pi μs)) = 0
  rw [integral_map ht.aemeasurable (g i).continuous.aestronglyMeasurable]
  have hpoint (x : X) : g i (total x) = ∏ j : s, Complex.exp (v i * ((x j).val : ℂ)) := by
    change Complex.exp (v i * ((∑ j : s, (x j).val : ℝ) : ℂ)) = _
    rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  simp_rw [hpoint]
  refine (integral_fintype_prod_eq_prod (μ := μs)
    (fun (j : s) (x : Icc 0 (a j)) ↦ Complex.exp (v i * (x.val : ℂ)))).trans ?_
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨i, hi⟩ : s)) (hν i)

/-- A probability on the endpoints of a short interval with one prescribed transform zero. -/
private theorem exp_two_atom_filter (v : ℂ) (hv : v.im ≠ 0) :
    let a := Real.pi / |v.im|
    ∃ ν : ProbabilityMeasure (Icc 0 a), ∫ x : Icc 0 a, Complex.exp (v * (x.val : ℂ)) ∂ν = 0 := by
  dsimp only
  let a := Real.pi / |v.im|
  have ha : 0 ≤ a := div_nonneg Real.pi_pos.le (abs_nonneg _)
  let M := Real.exp (v.re * a)
  have hM : 0 < M := Real.exp_pos _
  let p : unitInterval := ⟨(1 + M)⁻¹, inv_nonneg.mpr (by linarith), inv_le_one_of_one_le₀ (by linarith)⟩
  let x0 : Icc 0 a := ⟨0, le_rfl, ha⟩
  let x1 : Icc 0 a := ⟨a, ha, le_rfl⟩
  have hphase : Complex.exp (((v.im * a : ℝ) : ℂ) * Complex.I) = -1 := by
    rcases lt_or_gt_of_ne hv with h | h
    · have harg : v.im * a = -Real.pi := by dsimp [a]; rw [abs_of_neg h]; field_simp
      rw [harg, Complex.ofReal_neg, neg_mul, Complex.exp_neg_pi_mul_I]
    · have harg : v.im * a = Real.pi := by dsimp [a]; rw [abs_of_pos h]; field_simp
      rw [harg, Complex.exp_pi_mul_I]
  have he : Complex.exp (v * (a : ℂ)) = -(M : ℂ) := by
    have hsplit : v * (a : ℂ) = ((v.re * a : ℝ) : ℂ) + ((v.im * a : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hsplit, Complex.exp_add, hphase, mul_neg_one, ← Complex.ofReal_exp]
  refine ⟨⟨ProbabilityTheory.bernoulliMeasure x1 x0 p, inferInstance⟩, ?_⟩
  change ∫ x : Icc 0 a, Complex.exp (v * (x.val : ℂ)) ∂ProbabilityTheory.bernoulliMeasure x1 x0 p = 0
  rw [ProbabilityTheory.integral_bernoulliMeasure]
  change ((1 + M)⁻¹ : ℝ) • Complex.exp (v * (a : ℂ)) + (1 - (1 + M)⁻¹ : ℝ) • Complex.exp (v * (0 : ℂ)) = 0
  rw [he, mul_zero, Complex.exp_zero, Complex.real_smul, Complex.real_smul]
  push_cast
  have hp : (1 : ℂ) + (M : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 : ℝ) + M ≠ 0)
  field_simp [hp]
  ring

/-- A probability measure annihilating all frequencies with summable reciprocal ordinates. -/
private theorem summable_reciprocal_exp_filter {ι : Type*} (v : ι → ℂ) (hv : ∀ i, (v i).im ≠ 0)
    (ha : Summable (fun i ↦ Real.pi / |(v i).im|)) :
    let L := ∑' i, Real.pi / |(v i).im|
    ∃ μ : ProbabilityMeasure (Icc 0 L), ∀ i, ∫ x : Icc 0 L, Complex.exp (v i * (x.val : ℂ)) ∂μ = 0 := by
  classical
  dsimp only
  choose ν hν using fun i ↦ exp_two_atom_filter (v i) (hv i)
  apply probability_exp_filter v _ _ _ ν hν
  intro s
  change (∑ j ∈ s.attach, Real.pi / |(v j.val).im|) ≤ _
  rw [Finset.sum_attach s (fun i ↦ Real.pi / |(v i).im|)]
  exact ha.sum_le_tsum s (fun i _ ↦ div_nonneg Real.pi_pos.le (abs_nonneg _))

/-- Smoothing a compactly supported probability law multiplies bilateral transforms and
adds at most the support length of that law to the original interval. -/
private theorem smooth_probability_filter {L A B : ℝ} (μ : ProbabilityMeasure (Icc 0 L))
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hz : ∀ x ∉ Icc A B, b x = 0) :
    ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ (∀ x ∉ Icc A (B + L), h x = 0) ∧
      ∀ w : ℂ, (∫ x : ℝ, h x * Complex.exp (w * x)) =
        (∫ x : ℝ, b x * Complex.exp (w * x)) * (∫ t : Icc 0 L, Complex.exp (w * (t.val : ℂ)) ∂μ) := by
  let h (x : ℝ) := ∫ t : Icc 0 L, b (x - t.val) ∂μ
  let ν : Measure ℝ := (μ : Measure (Icc 0 L)).map Subtype.val
  let : IsFiniteMeasure ν := inferInstanceAs (IsFiniteMeasure ((μ : Measure (Icc 0 L)).map Subtype.val))
  have hbc : HasCompactSupport b := exists_compact_iff_hasCompactSupport.mp ⟨_, isCompact_Icc, hz⟩
  have heq : h = convolution (fun _ : ℝ ↦ (1 : ℝ)) b (ContinuousLinearMap.lsmul ℝ ℝ) ν := by
    funext x
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, one_smul]
    exact (integral_map measurable_subtype_coe.aemeasurable
      (hb.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).symm
  have hh : ContDiff ℝ ∞ h := by
    rw [heq]
    exact hbc.contDiff_convolution_right _ (locallyIntegrable_const _) hb
  have hvan (x : ℝ) (hx : x ∉ Icc A (B + L)) (t : Icc 0 L) : b (x - t.val) = 0 := by
    apply hz
    intro hc
    exact hx ⟨by linarith [hc.1, t.property.1], by linarith [hc.2, t.property.2]⟩
  refine ⟨h, hh, fun x hx ↦ ?_, fun w ↦ ?_⟩
  · simp [h, hvan x hx]
  let k (x : ℝ) (t : Icc 0 L) := b (x - t.val) * Complex.exp (w * x)
  have hk : Continuous k.uncurry := by
    change Continuous (fun p : ℝ × Icc 0 L ↦ b (p.1 - p.2.val) * Complex.exp (w * (p.1 : ℂ)))
    fun_prop (disch := exact hb.continuous)
  have hkc : HasCompactSupport k.uncurry := by
    refine exists_compact_iff_hasCompactSupport.mp ⟨Icc A (B + L) ×ˢ (univ : Set (Icc 0 L)),
      isCompact_Icc.prod isCompact_univ, ?_⟩
    rintro ⟨x, t⟩ hx
    have hxt : x ∉ Icc A (B + L) := fun h' ↦ hx ⟨h', mem_univ _⟩
    simp only [k, uncurry_apply_pair, hvan x hxt, zero_mul]
  have hshift (t : Icc 0 L) : ∫ x : ℝ, k x t =
      (∫ x : ℝ, b x * Complex.exp (w * x)) * Complex.exp (w * (t.val : ℂ)) := by
    calc
      ∫ x : ℝ, k x t = ∫ x : ℝ, (b (x - t.val) * Complex.exp (w * ((x - t.val : ℝ) : ℂ))) *
          Complex.exp (w * (t.val : ℂ)) := by
        congr 1; funext x
        rw [mul_assoc, ← Complex.exp_add]
        simp only [k, Complex.ofReal_sub]; congr 2; ring
      _ = _ := by rw [integral_mul_const, integral_sub_right_eq_self
        (fun y : ℝ ↦ b y * Complex.exp (w * y)) t.val]
  calc
    (∫ x : ℝ, h x * Complex.exp (w * x)) = ∫ x : ℝ, ∫ t : Icc 0 L, k x t ∂μ := by
      congr 1; funext x; exact (integral_mul_const _ _).symm
    _ = ∫ t : Icc 0 L, (∫ x : ℝ, k x t) ∂μ := integral_integral_swap_of_hasCompactSupport hk hkc
    _ = _ := by simp_rw [hshift]; rw [integral_const_mul]

private theorem normalized_interval_bump {A B : ℝ} (hAB : A < B) :
    ∃ b : ℝ → ℂ, ContDiff ℝ ∞ b ∧ (∀ x ∉ Icc A B, b x = 0) ∧ transform b 0 = 1 := by
  let c := (A + B) / 2
  let β : ContDiffBump c := ⟨(B - A) / 8, (B - A) / 4, by linarith, by linarith⟩
  let b (x : ℝ) : ℂ := β.normed volume x
  refine ⟨b, Complex.ofRealCLM.contDiff.comp β.contDiff_normed, ?_, ?_⟩
  · intro x hx
    have hx' : x ∉ tsupport (β.normed volume) := by
      rw [β.tsupport_normed_eq]
      intro h
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at h
      exact hx ⟨by dsimp [c, β] at h; linarith [h.1], by dsimp [c, β] at h; linarith [h.2]⟩
    simp [b, image_eq_zero_of_notMem_tsupport hx']
  · simp [transform, b, integral_complex_ofReal, β.integral_normed]

/-- A finite set of exceptional offsets costs no support. All remaining offsets together
cost at most the sum of their reciprocal vertical separations multiplied by π. -/
private theorem isolate_with_tail {ι : Type*} (u : ℂ) (v : ι → ℂ) (S : Finset ℂ) (hS : 0 ∉ S)
    (hv : ∀ i, (v i).im ≠ 0) (ha : Summable (fun i ↦ Real.pi / |(v i).im|)) {A B : ℝ}
    (hL : (∑' i, Real.pi / |(v i).im|) < B - A) :
    ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ (∀ x ∉ Icc A B, h x = 0) ∧ transform h u = 1 ∧
      (∀ w ∈ S, transform h (u + w) = 0) ∧ (∀ i, transform h (u + v i) = 0) := by
  let L := ∑' i, Real.pi / |(v i).im|
  obtain ⟨μ, hμ⟩ := summable_reciprocal_exp_filter v hv ha
  change L < B - A at hL
  obtain ⟨b, hb, hbz, hb0⟩ := normalized_interval_bump (show A < B - L by linarith)
  have hbc : HasCompactSupport b := exists_compact_iff_hasCompactSupport.mp ⟨_, isCompact_Icc, hbz⟩
  have hbs : tsupport b ⊆ Icc A (B - L) := closure_minimal
    (fun x hx ↦ by by_contra h; exact hx (hbz x h)) isClosed_Icc
  obtain ⟨f, hf, _, hfs, hf0, hfS⟩ := finite_filter b hb hbc 0 S hS
  have hfz (x : ℝ) (hx : x ∉ Icc A (B - L)) : f x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hbs (hfs h))
  obtain ⟨j, hj, hjz, hjH⟩ := smooth_probability_filter μ f hf hfz
  change ∀ w : ℂ, transform j w = transform f w * _ at hjH
  let h (x : ℝ) := j x * Complex.exp (-(u * x))
  have hshift (w : ℂ) : transform h (u + w) = transform j w := by
    unfold transform
    congr 1; funext x
    dsimp only [h]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2; ring
  refine ⟨h, hj.mul ((contDiff_const.mul Complex.ofRealCLM.contDiff).neg.cexp), ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : x ∉ Icc A ((B - L) + L) := by simpa using hx
    simp [h, hjz x hx']
  · simpa [hjH, hf0, hb0] using hshift 0
  · intro w hw
    rw [hshift, hjH, hfS w hw, zero_mul]
  · intro i
    rw [hshift, hjH, hμ i, mul_zero]
/-- A smooth profile in any interval can have transform one at a target and zero on
a family whose reciprocal vertical separations from the target are summable. -/
private theorem sparse_interval_interpolation {ι : Type*} (w : ι → ℂ) (u : ℂ) (hwu : ∀ i, w i ≠ u)
    (hs : Summable (fun i ↦ 1 / (1 + |(w i - u).im|))) {A B : ℝ} (hAB : A < B) :
    ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ (∀ x ∉ Icc A B, h x = 0) ∧ transform h u = 1 ∧
      ∀ i, transform h (w i) = 0 := by
  classical
  let v (i : ι) := w i - u
  let y (i : ι) := |(v i).im|
  have hsmall : {i : ι | ¬ 1 / (1 + y i) < 1 / 2}.Finite :=
    Filter.eventually_cofinite.mp (hs.tendsto_cofinite_zero.eventually_lt_const (by norm_num))
  let s₀ := hsmall.toFinset
  have hlarge (i : ι) (hi : i ∉ s₀) : 1 < y i := by
    have hin : 1 / (1 + y i) < 1 / 2 := by
      by_contra! h
      exact hi (hsmall.mem_toFinset.mpr (not_lt.mpr h))
    have hy : 0 ≤ y i := abs_nonneg _
    rw [div_lt_iff₀ (by linarith)] at hin
    linarith
  let a (i : ι) := if i ∈ s₀ then 0 else Real.pi / y i
  have ha : Summable a := by
    apply Summable.of_nonneg_of_le (f := fun i ↦ (2 * Real.pi) * (1 / (1 + y i)))
    · intro i
      dsimp only [a]
      split <;> first | exact le_rfl | exact div_nonneg Real.pi_pos.le (abs_nonneg _)
    · intro i
      by_cases hi : i ∈ s₀
      · simp only [a, ite_eq_left hi]
        have hy : 0 ≤ y i := abs_nonneg _
        positivity
      · simp only [a, ite_eq_right hi]
        have hy := hlarge i hi
        rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith [mul_le_mul_of_nonneg_left hy.le Real.pi_pos.le]
    · exact hs.mul_left (2 * Real.pi)
  obtain ⟨s₁, hs₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_tsum_compl_atTop_zero a).eventually_lt_const (sub_pos.mpr hAB))
  let T := s₀ ∪ s₁
  let J := {i : ι // i ∉ T}
  have hJ (i : J) : i.val ∉ s₀ := fun hi ↦ i.property (Finset.mem_union_left _ hi)
  have hvJ (i : J) : (v i.val).im ≠ 0 := by
    intro h
    have h1 := hlarge i.val (hJ i)
    simp [y, h] at h1
    linarith
  have haJ (i : J) : a i.val = Real.pi / |(v i.val).im| := ite_eq_right (hJ i)
  have hsumJ : Summable (fun i : J ↦ Real.pi / |(v i.val).im|) := (ha.subtype _).congr haJ
  have hL : (∑' i : J, Real.pi / |(v i.val).im|) < B - A := by
    simp_rw [← haJ]
    exact hs₁ T Finset.subset_union_right
  have hzero : 0 ∉ T.image v := by
    intro he
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
    exact hwu i (sub_eq_zero.mp hi)
  obtain ⟨h, hh, hz, h1, hT, hJ'⟩ :=
    isolate_with_tail u (fun i : J ↦ v i.val) (T.image v) hzero hvJ hsumJ hL
  refine ⟨h, hh, hz, h1, fun i ↦ ?_⟩
  have he : u + v i = w i := by dsimp [v]; ring
  rw [← he]
  by_cases hi : i ∈ T
  · exact hT (v i) (Finset.mem_image_of_mem v hi)
  · exact hJ' ⟨i, hi⟩
private theorem summable_shifted_heights {ι : Type*} {w : ι → ℂ}
    (hs : Summable (fun i ↦ 1 / (1 + |(w i).im|))) (u : ℂ) :
    Summable (fun i ↦ 1 / (1 + |(w i - u).im|)) := by
  apply Summable.of_nonneg_of_le (f := fun i ↦ (1 + |u.im|) * (1 / (1 + |(w i).im|)))
  · intro i; positivity
  · intro i
    have htri : |(w i).im| ≤ |(w i - u).im| + |u.im| := by
      have he : (w i).im = (w i - u).im + u.im := by simp
      calc
        |(w i).im| = |(w i - u).im + u.im| := congrArg abs he
        _ ≤ _ := abs_add_le _ _
    rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (abs_nonneg u.im) (abs_nonneg (w i - u).im)]
  · exact hs.mul_left (1 + |u.im|)

/-- A smooth test supported in a prescribed interval can retain one given complex frequency
while annihilating a family with summable reciprocal heights. -/
theorem exists_smooth_sparse_laplace_interpolant {ι : Type*} (w : ι → ℂ) (u : ℂ)
    (hwu : ∀ i, w i ≠ u) (hs : Summable (fun i ↦ 1 / (1 + |(w i).im|)))
    {A B : ℝ} (hAB : A < B) :
    ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ (∀ x ∉ Icc A B, h x = 0) ∧
      (∫ x : ℝ, h x * Complex.exp (u * x)) = 1 ∧
      ∀ i, (∫ x : ℝ, h x * Complex.exp (w i * x)) = 0 :=
  sparse_interval_interpolation w u hwu (summable_shifted_heights hs u) hAB

/-- For an injective frequency family with summable reciprocal heights, a test in any interval
can make the weighted spectral sum equal the coefficient at any one index. -/
theorem exists_smooth_sparse_laplace_weighted_sum {ι : Type*} (w : ι → ℂ)
    (hinj : Injective w) (m : ι → ℂ) (hs : Summable (fun i ↦ 1 / (1 + |(w i).im|)))
    (i₀ : ι) {A B : ℝ} (hAB : A < B) :
    ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ (∀ x ∉ Icc A B, h x = 0) ∧
      (∫ x : ℝ, h x * Complex.exp (w i₀ * x)) = 1 ∧
      (∀ i, i ≠ i₀ → (∫ x : ℝ, h x * Complex.exp (w i * x)) = 0) ∧
      HasSum (fun i ↦ m i * ∫ x : ℝ, h x * Complex.exp (w i * x)) (m i₀) := by
  let J := {i : ι // i ≠ i₀}
  obtain ⟨h, hh, hz, h1, hJ⟩ := exists_smooth_sparse_laplace_interpolant (fun i : J ↦ w i.val) (w i₀)
    (fun i he ↦ i.property (hinj he)) (hs.subtype _) hAB
  change transform h (w i₀) = 1 at h1
  have hk (i : ι) (hi : i ≠ i₀) : transform h (w i) = 0 := hJ ⟨i, hi⟩
  refine ⟨h, hh, hz, h1, hk, ?_⟩
  change HasSum (fun i ↦ m i * transform h (w i)) (m i₀)
  simpa only [h1, mul_one] using
    (hasSum_single i₀ (f := fun i ↦ m i * transform h (w i)) fun i hi ↦ by rw [hk i hi, mul_zero])

end RiemannMasullo
