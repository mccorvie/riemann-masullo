module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

/-! # Compactly supported tests with prescribed sparse Laplace zeros

Finite products of positive two-point measures cancel finitely many exponential
moments. Compactness of probability measures keeps all the cancellations on a
common interval when the total displacement is summable.
-/

@[expose] public noncomputable section

open Classical Set MeasureTheory Filter Complex
open scoped ENNReal Topology ContDiff

namespace RiemannMasullo.SparseLaplace

private theorem exists_finite_moment_measure {ι : Type*} (w : ι → ℂ) (d l : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hs : Summable d) (hl : ∀ i, 0 < l i)
    (hz : ∀ i, 1 + (l i : ℂ) * cexp (w i * (d i : ℂ)) = 0) (s : Finset ι) :
    ∃ μ : ProbabilityMeasure (Icc 0 (∑' i, d i)), ∀ i ∈ s,
      ∫ x : Icc 0 (∑' i, d i), cexp (w i * (x.val : ℂ)) ∂(μ : Measure _) = 0 := by
  classical
  let X := Icc 0 (∑' i, d i)
  let point (t : Finset ι) : X :=
    ⟨∑ j ∈ t, d j, Finset.sum_nonneg (fun j _ ↦ hd j), hs.sum_le_tsum t (fun j _ ↦ hd j)⟩
  let Z := ∏ j ∈ s, (1 + l j)
  have hZ : 0 < Z := Finset.prod_pos fun j _ ↦ by have := hl j; positivity
  let mass (t : Finset ι) := (∏ j ∈ t, l j) / Z
  have hmass (t) : 0 ≤ mass t :=
    div_nonneg (Finset.prod_nonneg fun j _ ↦ (hl j).le) hZ.le
  have htotal : ∑ t ∈ s.powerset, mass t = 1 := by
    simp only [mass, ← Finset.sum_div, ← Finset.prod_one_add]
    exact div_self hZ.ne'
  let atom (t : Finset ι) : Measure X := ENNReal.ofReal (mass t) • Measure.dirac (point t)
  let μ := ∑ t ∈ s.powerset, atom t
  have hprob : IsProbabilityMeasure μ := by
    constructor
    simpa [μ, atom, sum_apply, smul_apply,
      ← ENNReal.ofReal_sum_of_nonneg (fun t _ ↦ hmass t)] using
        congrArg ENNReal.ofReal htotal
  refine ⟨⟨μ, hprob⟩, fun i hi ↦ ?_⟩
  change ∫ x : X, cexp (w i * (x.val : ℂ)) ∂(∑ t ∈ s.powerset, atom t) = 0
  rw [integral_finsetSum_measure (μ := atom) (fun t _ ↦
    (integrable_dirac eNorm_lt_top).smul_measure ENNReal.ofReal_ne_top)]
  have hterm (t : Finset ι) :
      ∫ x : X, cexp (w i * (x.val : ℂ)) ∂(atom t) =
        (∏ j ∈ t, (l j : ℂ) * cexp (w i * (d j : ℂ))) / (Z : ℂ) := by
    simp only [atom, integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hmass t),
      real_smul, mass, ofReal_div, ofReal_prod, point, ofReal_sum, Finset.mul_sum,
      Complex.exp_sum, Finset.prod_mul_distrib]
    ring
  simp only [hterm, ← Finset.sum_div, ← Finset.prod_one_add]
  rw [Finset.prod_eq_zero hi (hz i), zero_div]

/-- Summable displacements realizing two-point cancellations give one compact
probability measure with every prescribed exponential moment zero. -/
theorem exists_moment_measure {ι : Type*} (w : ι → ℂ) (d l : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hs : Summable d) (hl : ∀ i, 0 < l i)
    (hz : ∀ i, 1 + (l i : ℂ) * cexp (w i * (d i : ℂ)) = 0) :
    ∃ μ : ProbabilityMeasure (Icc 0 (∑' i, d i)), ∀ i,
      ∫ x : Icc 0 (∑' i, d i), cexp (w i * (x.val : ℂ)) ∂(μ : Measure _) = 0 := by
  classical
  let X := Icc 0 (∑' i, d i)
  let C (i : ι) : Set (ProbabilityMeasure X) :=
    {μ | ∫ x : X, cexp (w i * (x.val : ℂ)) ∂(μ : Measure X) = 0}
  have hclosed (i) : IsClosed (C i) := by
    apply isClosed_eq _ continuous_const
    apply continuous_iff_continuousAt.mpr
    intro μ
    let f : C(X, ℂ) := ⟨fun x ↦ cexp (w i * (x.val : ℂ)), by fun_prop⟩
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
      (tendsto_id (x := 𝓝 μ)) (ContinuousMap.equivBoundedOfCompact X ℂ f)
  obtain ⟨μ, hμ⟩ := CompactSpace.iInter_nonempty hclosed (fun s ↦ by
    obtain ⟨μ, hμ⟩ := exists_finite_moment_measure w d l hd hs hl hz s
    exact ⟨μ, mem_iInter₂.mpr hμ⟩)
  exact ⟨μ, mem_iInter.mp hμ⟩

private theorem half_period_cancel (z : ℂ) (hy : 0 < |z.im|) :
    1 + (Real.exp (-z.re * (Real.pi / |z.im|)) : ℂ) *
      cexp (z * (Real.pi / |z.im| : ℝ)) = 0 := by
  let d := Real.pi / |z.im|
  have he : (↑(-z.re * d) : ℂ) + z * d = ((z.im * d : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  change 1 + (Real.exp (-z.re * d) : ℂ) * cexp (z * d) = 0
  rw [Complex.ofReal_exp, ← Complex.exp_add, he]
  rcases lt_or_gt_of_ne (abs_pos.mp hy) with h | h
  · have hs : z.im * d = -Real.pi := by
      dsimp [d]; rw [abs_of_neg h]; field_simp [h.ne]
    rw [hs, Complex.ofReal_neg, neg_mul, Complex.exp_neg_pi_mul_I]; ring
  · have hs : z.im * d = Real.pi := by
      dsimp [d]; rw [abs_of_pos h]; field_simp
    rw [hs, Complex.exp_pi_mul_I]; ring

private theorem exists_tail_measure {ι : Type*} (w : ι → ℂ)
    (hs : Summable fun i ↦ 1 / (1 + |(w i).im|)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ι) (L : ℝ) (μ : ProbabilityMeasure (Icc 0 L)), 0 ≤ L ∧ L < ε ∧
      ∀ i ∉ s, ∫ x : Icc 0 L, cexp (w i * (x.val : ℂ)) ∂(μ : Measure _) = 0 := by
  classical
  let d (i : ι) := Real.pi / max 1 |(w i).im|
  have hd (i) : 0 ≤ d i := by dsimp [d]; positivity
  have hds : Summable d := by
    apply Summable.of_nonneg_of_le hd _ (hs.mul_left (2 * Real.pi))
    intro i
    have hm : 0 < max 1 |(w i).im| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    dsimp [d]
    rw [mul_one_div, div_le_div_iff₀ hm (by positivity)]
    have hsum := add_le_add (le_max_left 1 |(w i).im|) (le_max_right 1 |(w i).im|)
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hsum)]
  have hlow : ∀ᶠ i in cofinite, 1 ≤ |(w i).im| := by
    filter_upwards [(hs.tendsto_cofinite_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1/2))] with i hi
    have := (div_lt_iff₀ (by positivity : 0 < 1 + |(w i).im|)).mp hi
    linarith
  let bad := (eventually_cofinite.mp hlow).toFinset
  obtain ⟨s, hs'⟩ := eventually_atTop.mp
    ((tendsto_tsum_compl_atTop_zero d).eventually_lt_const hε)
  let t := s ∪ bad
  let J := {i : ι // i ∉ t}
  have htail (j : J) : 1 ≤ |(w j).im| := by
    by_contra! hj
    exact j.property (Finset.mem_union_right _ (by simpa [bad] using hj))
  let l (j : J) := Real.exp (-(w j).re * d j)
  obtain ⟨μ, hμ⟩ := exists_moment_measure (fun j : J ↦ w j) (fun j : J ↦ d j) l
    (fun j ↦ hd j) (hds.subtype _) (fun j ↦ Real.exp_pos _)
    (fun j ↦ by simpa [l, d, max_eq_right (htail j)] using
      half_period_cancel (w j) (zero_lt_one.trans_le (htail j)))
  exact ⟨t, _, μ, tsum_nonneg (fun j ↦ hd j), hs' t (Finset.subset_union_left),
    fun i hi ↦ hμ ⟨i, hi⟩⟩

/-- Translating a physical test multiplies its bilateral Laplace transform by the
corresponding exponential. -/
theorem bilateralLaplace_translate (h : ℝ → ℂ) (t : ℝ) (z : ℂ) :
    bilateralLaplace (fun x ↦ h (x - t)) z = bilateralLaplace h z * cexp (z * t) := by
  unfold bilateralLaplace
  rw [← integral_mul_const, ← integral_add_right_eq_self
    (fun x : ℝ ↦ h x * cexp (z * x) * cexp (z * t)) (-t)]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  rw [mul_assoc, ← Complex.exp_add, ← mul_add]
  simp [sub_eq_add_neg]

private theorem smooth_measure {L b : ℝ} (μ : ProbabilityMeasure (Icc 0 L))
    (h : ℝ → ℂ) (hh : ContDiff ℝ (∞) h) (hb : tsupport h ⊆ Icc 0 b) :
    ∃ g : ℝ → ℂ, ContDiff ℝ (∞) g ∧ tsupport g ⊆ Icc 0 (b + L) ∧ ∀ z,
      bilateralLaplace g z =
        bilateralLaplace h z * ∫ t : Icc 0 L, cexp (z * (t.val : ℂ)) ∂(μ : Measure _) := by
  let g (x : ℝ) := ∫ t : Icc 0 L, h (x - t.val) ∂(μ : Measure _)
  let ν := (μ : Measure (Icc 0 L)).map Subtype.val
  have hge (x) : (∫ t in Icc 0 L, h (x - t) ∂ν) = g x := by
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Icc).setIntegral_map]
    simp [g, Subtype.coe_preimage_self]
  have hsm := ContDiff.parametric_integral (μ := ν) (f := fun x t : ℝ ↦ h (x - t))
    isCompact_Icc (Subset.rfl : Icc 0 L ⊆ _) (measure_ne_top _ _)
    (hh.comp (contDiff_fst.sub contDiff_snd))
  have hzero {x : ℝ} (hx : x ∉ Icc 0 (b + L)) (t : Icc 0 L) : h (x - t.val) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have ⟨h₁, h₂⟩ := hb hm
    exact hx ⟨by linarith [t.property.1], by linarith [t.property.2]⟩
  refine ⟨g, by simpa only [hge] using hsm, ?_, fun z ↦ ?_⟩
  · apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hn
    exact hx (by simp [g, hzero hn])
  let f (x : ℝ) (t : Icc 0 L) := h (x - t.val) * cexp (z * x)
  have hf : Continuous (Function.uncurry f) := by
    exact (hh.continuous.comp (continuous_fst.sub (continuous_subtype_val.comp continuous_snd))).mul
      (by fun_prop)
  have hfc : HasCompactSupport (Function.uncurry f) := by
    apply HasCompactSupport.intro (K := (Icc 0 (b + L)) ×ˢ (univ : Set (Icc 0 L)))
      (isCompact_Icc.prod isCompact_univ)
    intro p hp
    have hx : p.1 ∉ Icc 0 (b + L) := fun h ↦ hp ⟨h, mem_univ _⟩
    simp [Function.uncurry, f, hzero hx]
  calc bilateralLaplace g z = ∫ x : ℝ, ∫ t : Icc 0 L, f x t ∂(μ : Measure _) := by
          simp only [bilateralLaplace, g, f, integral_mul_const]
    _ = ∫ t : Icc 0 L, ∫ x : ℝ, f x t ∂volume ∂(μ : Measure _) :=
      integral_integral_swap_of_hasCompactSupport hf hfc
    _ = _ := by
      change (∫ t : Icc 0 L, bilateralLaplace (fun x ↦ h (x - t.val)) z ∂(μ : Measure _)) = _
      simp only [bilateralLaplace_translate, integral_const_mul]

private theorem laplace_deriv {h : ℝ → ℂ} (hh : ContDiff ℝ (∞) h) (hc : HasCompactSupport h)
    (z : ℂ) : bilateralLaplace (deriv h) z = -z * bilateralLaplace h z := by
  let E (x : ℝ) := cexp (z * x)
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hE' (x : ℝ) : HasDerivAt E (z * E x) x := by
    change HasDerivAt (fun t : ℝ ↦ cexp (z * t)) (z * cexp (z * x)) x
    convert (((hasDerivAt_id' (x : ℂ)).const_mul z).cexp).comp_ofReal using 1
    ring
  have hp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := E) (u' := fun x ↦ z * E x) (v := h) (v' := deriv h) (fun x _ ↦ hE' x)
    (fun x _ ↦ ((hh.differentiable (by simp)) x).hasDerivAt)
    ((hE.mul (hh.continuous_deriv (by simp))).integrable_of_hasCompactSupport hc.deriv.mul_left)
    (((continuous_const.mul hE).mul hh.continuous).integrable_of_hasCompactSupport hc.mul_left)
    ((hE.mul hh.continuous).integrable_of_hasCompactSupport hc.mul_left)
  change (∫ x : ℝ, deriv h x * E x) = -z * ∫ x : ℝ, h x * E x
  calc ∫ x : ℝ, deriv h x * E x = ∫ x : ℝ, E x * deriv h x := by simp only [mul_comm]
    _ = -∫ x : ℝ, z * E x * h x := hp
    _ = _ := by rw [neg_mul, ← integral_const_mul]; congr 2; funext x; ring

private theorem finite_filters {ι : Type*} (w : ι → ℂ) {b : ℝ} (s : Finset ι)
    {h : ℝ → ℂ} (hh : ContDiff ℝ (∞) h) (hb : tsupport h ⊆ Icc 0 b) :
    ∃ g : ℝ → ℂ, ContDiff ℝ (∞) g ∧ tsupport g ⊆ Icc 0 b ∧ ∀ z,
      bilateralLaplace g z = (∏ i ∈ s, (w i - z)) * bilateralLaplace h z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨h, hh, hb, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨g, hg, hgb, hgz⟩ := ih
    have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hgb
    let G (x : ℝ) := w i * g x + deriv g x
    have hD := (contDiff_infty_iff_deriv.mp hg).2
    refine ⟨G, (contDiff_const.mul hg).add hD, ?_, fun z ↦ ?_⟩
    · apply closure_minimal _ isClosed_Icc
      intro x hx
      by_contra h
      have hn : x ∉ tsupport g := fun hx ↦ h (hgb hx)
      exact hx (by simp [G, image_eq_zero_of_notMem_tsupport hn,
        image_eq_zero_of_notMem_tsupport (fun h ↦ hn (tsupport_deriv_subset h))])
    have hi₁ : Integrable fun x : ℝ ↦ (w i * g x) * cexp (z * x) :=
      ((continuous_const.mul hg.continuous).mul (by fun_prop)).integrable_of_hasCompactSupport
        hgc.mul_left.mul_right
    have hi₂ : Integrable fun x : ℝ ↦ deriv g x * cexp (z * x) :=
      (hD.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.deriv.mul_right
    calc bilateralLaplace G z = w i * bilateralLaplace g z + bilateralLaplace (deriv g) z := by
          simp only [G, bilateralLaplace, add_mul]
          rw [integral_add hi₁ hi₂]
          simp only [mul_assoc, integral_const_mul]
      _ = _ := by rw [laplace_deriv hg hgc, hgz, Finset.prod_insert hi]; ring

private theorem summable_inverse_height_sub {ι : Type*} {w : ι → ℂ}
    (hs : Summable (fun i ↦ 1/(1+|(w i).im|))) (r : ℂ) :
    Summable (fun i ↦ 1/(1+|(w i-r).im|)) := by
  apply (hs.mul_left (1+|r.im|)).of_nonneg_of_le (fun i ↦ by positivity)
  intro i
  rw [Complex.sub_im,← mul_div_assoc, mul_one,div_le_div_iff₀ (by positivity) (by positivity)]
  have ht := abs_add_le ((w i).im-r.im) r.im
  rw [sub_add_cancel] at ht
  nlinarith only [ht,mul_nonneg (abs_nonneg r.im) (abs_nonneg ((w i).im-r.im))]

/-- In an arbitrarily short interval there is a smooth test whose transform vanishes
at every prescribed sparse frequency and is nonzero at a specified complex point.
Finitely many exceptional frequencies need no height separation. -/
theorem exists_compact_probe_complex {ι : Type*} (w : ι → ℂ) (r : ℂ) (hne : ∀ i, w i ≠ r)
    (hs : Summable fun i ↦ 1 / (1 + |(w i).im|)) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℝ → ℂ, ContDiff ℝ (∞) G ∧ tsupport G ⊆ Icc 0 ε ∧
      bilateralLaplace G r ≠ 0 ∧ ∀ i, bilateralLaplace G (w i) = 0 := by
  classical
  let v (i : ι) := w i - r
  obtain ⟨s, L, μ, _, hL, hμ⟩ := exists_tail_measure v (summable_inverse_height_sub hs r)
    (half_pos hε)
  let B : ContDiffBump (ε / 4) := ⟨ε / 8, ε / 4, by positivity, by linarith⟩
  let h (x : ℝ) : ℂ := B.normed volume x
  have hh : ContDiff ℝ (∞) h := Complex.ofRealCLM.contDiff.comp B.contDiff_normed
  have hb : tsupport h ⊆ Icc 0 (ε / 2) := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have hx' : x ∈ Function.support (B.normed volume) := by simpa [Function.mem_support, h] using hx
    have := B.support_normed_eq (μ := volume) ▸ hx'
    change dist x (ε / 4) < ε / 4 at this
    rw [Real.dist_eq, abs_lt] at this
    constructor <;> linarith
  obtain ⟨g, hg, hgb, hgz⟩ := smooth_measure μ h hh hb
  have h0 : bilateralLaplace g 0 = 1 := by
    rw [hgz]
    simp [bilateralLaplace, h, integral_complex_ofReal, B.integral_normed]
  obtain ⟨f, hf, hfb, hfz⟩ := finite_filters v s hg hgb
  let G (x : ℝ) := f x * cexp (-r * x)
  have hG (z : ℂ) : bilateralLaplace G z = bilateralLaplace f (z - r) := by
    unfold bilateralLaplace
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    change f x * cexp (-r * x) * cexp (z * x) = _
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  refine ⟨G, hf.mul ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp), tsupport_mul_subset_left.trans
    (hfb.trans (Icc_subset_Icc_right (by linarith))), ?_, fun i ↦ ?_⟩
  · rw [hG, sub_self, hfz, h0, mul_one]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ by simpa [v] using sub_ne_zero.mpr (hne i)
  · rw [hG, hfz]
    by_cases hi : i ∈ s
    · rw [Finset.prod_eq_zero hi (sub_self (v i)), zero_mul]
    · rw [hgz, hμ i hi, mul_zero, mul_zero]

/-- In an arbitrarily short interval there is a smooth test whose transform vanishes
at every prescribed sparse frequency and is nonzero at a specified real point.
Finitely many exceptional frequencies need no height separation. -/
theorem exists_compact_probe {ι : Type*} (w : ι → ℂ) (r : ℝ) (hne : ∀ i, w i ≠ r)
    (hs : Summable fun i ↦ 1 / (1 + |(w i).im|)) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℝ → ℂ, ContDiff ℝ (∞) G ∧ tsupport G ⊆ Icc 0 ε ∧
      bilateralLaplace G r ≠ 0 ∧ ∀ i, bilateralLaplace G (w i) = 0 :=
  exists_compact_probe_complex w (r:ℂ) hne hs hε

/-- A sparse family of bilateral Laplace zeros is compatible with prescribing the
value one at the center of any open interval. -/
theorem exists_compact_probe_at {ι : Type*} (w : ι → ℂ) (r : ℝ) (hne : ∀ i, w i ≠ r)
    (hs : Summable fun i ↦ 1 / (1 + |(w i).im|)) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℝ → ℂ, ContDiff ℝ (∞) H ∧ tsupport H ⊆ Icc (c - ε) (c + ε) ∧
      H c = 1 ∧ ∀ i, bilateralLaplace H (w i) = 0 := by
  obtain ⟨G, hg, hb, hr, hz⟩ := exists_compact_probe w r hne hs hε
  obtain ⟨a, ha⟩ : ∃ x, G x ≠ 0 := by
    by_contra! hn
    exact hr (by simp [bilateralLaplace, hn])
  have ham := hb (subset_tsupport G ha)
  let t := c - a
  let H (x : ℝ) := (G a)⁻¹ * G (x - t)
  refine ⟨H, contDiff_const.mul (hg.comp (contDiff_id.sub contDiff_const)), ?_, ?_, fun i ↦ ?_⟩
  · apply closure_minimal _ isClosed_Icc
    intro x hx
    have hg' : G (x - t) ≠ 0 := fun he ↦ hx (by simp [H, he])
    obtain ⟨h₁, h₂⟩ := hb (subset_tsupport G hg')
    dsimp [t] at h₁ h₂
    exact ⟨by linarith [ham.2], by linarith [ham.1]⟩
  · simp [H, t, ha]
  · calc bilateralLaplace H (w i) = (G a)⁻¹ * bilateralLaplace (fun x ↦ G (x - t)) (w i) := by
          simp only [bilateralLaplace, H, mul_assoc, integral_const_mul]
      _ = 0 := by rw [bilateralLaplace_translate, hz, zero_mul, mul_zero]

private theorem exists_complex_moment_cardinal {ι κ : Type*} [Fintype κ] (w : ι → ℂ)
    (hs : Summable fun i ↦ 1 / (1 + |(w i).im|)) (r : κ → ℂ) (hr : Function.Injective r)
    (hw : ∀ i j, w i ≠ r j) (j : κ) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ H : ℝ → ℂ, ContDiff ℝ (∞) H ∧ tsupport H ⊆ Icc a (a + b) ∧
      (∀ i, bilateralLaplace H (w i) = 0) ∧
      ∀ k, bilateralLaplace H (r k) = if k = j then 1 else 0 := by
  classical
  let W : ι ⊕ {k : κ // k ≠ j} → ℂ := Sum.elim w (fun k ↦ (r k.val))
  have hn (i) : W i ≠ r j := by
    cases i with
    | inl i => exact hw i j
    | inr k => exact fun h ↦ k.property (hr h)
  have hsum : Summable (fun i ↦ 1 / (1 + |(W i).im|)) :=
    Summable.sum _ hs (hasSum_fintype _).summable
  obtain ⟨G, hg, hG, hnG, hz⟩ := exists_compact_probe_complex W (r j) hn hsum hb
  let A := bilateralLaplace G (r j) * cexp (r j * a : ℂ)
  have hA : A ≠ 0 := mul_ne_zero hnG (Complex.exp_ne_zero _)
  let H (x : ℝ) := A⁻¹ * G (x - a)
  have hH (z : ℂ) : bilateralLaplace H z = A⁻¹ * (bilateralLaplace G z * cexp (z * a)) := by
    rw [← bilateralLaplace_translate]
    simp only [H, bilateralLaplace, mul_assoc, integral_const_mul]
  refine ⟨H, contDiff_const.mul (hg.comp (contDiff_id.sub contDiff_const)), ?_,
    fun i ↦ by rw [hH, show bilateralLaplace G (w i) = 0 from hz (.inl i), zero_mul, mul_zero], fun k ↦ ?_⟩
  · apply closure_minimal _ isClosed_Icc
    intro x hx
    have hn : G (x - a) ≠ 0 := fun he ↦ hx (by simp [H, he])
    obtain ⟨h₁, h₂⟩ := hG (subset_tsupport G hn)
    exact ⟨by linarith, by linarith⟩
  · rw [hH]
    split_ifs with he
    · subst k; exact inv_mul_cancel₀ hA
    · rw [show bilateralLaplace G (r k) = 0 from hz (.inr ⟨k, he⟩), zero_mul, mul_zero]

private theorem exists_moment_cardinal {ι κ : Type*} [Fintype κ] (w : ι → ℂ)
    (hs : Summable fun i ↦ 1 / (1 + |(w i).im|)) (r : κ → ℝ) (hr : Function.Injective r)
    (hw : ∀ i j, w i ≠ r j) (j : κ) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ H : ℝ → ℂ, ContDiff ℝ (∞) H ∧ tsupport H ⊆ Icc a (a + b) ∧
      (∀ i, bilateralLaplace H (w i) = 0) ∧
      ∀ k, bilateralLaplace H (r k) = if k = j then 1 else 0 :=
  exists_complex_moment_cardinal w hs (fun k ↦ (r k : ℂ)) (Complex.ofReal_injective.comp hr) hw j a hb

/-- A compact smooth probe in a prescribed short window can interpolate finitely
many complex Laplace moments and one physical sample while cancelling an infinite
sparse frequency family. The correcting probes are supported to the right of the
physical sample. -/
theorem exists_complex_interpolating_probe {ι κ : Type*} [Fintype κ] (w : ι → ℂ)
    (hs : Summable fun i ↦ 1 / (1 + |(w i).im|)) (r : κ → ℂ) (hr : Function.Injective r)
    (hw : ∀ i j, w i ≠ r j) (r₀ : ℝ) (hw₀ : ∀ i, w i ≠ r₀)
    (hr₀ : ∀ j, r j ≠ r₀) (v : κ → ℂ) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℝ → ℂ, ContDiff ℝ (∞) H ∧ tsupport H ⊆ Icc (c - ε) (c + ε) ∧ H c = 1 ∧
      (∀ i, bilateralLaplace H (w i) = 0) ∧ ∀ j, bilateralLaplace H (r j) = v j := by
  classical
  let W : ι ⊕ κ → ℂ := Sum.elim w r
  have hn (i) : W i ≠ r₀ := by
    cases i with
    | inl i => exact hw₀ i
    | inr j => exact fun h ↦ hr₀ j h
  have hsum : Summable (fun i ↦ 1 / (1 + |(W i).im|)) :=
    Summable.sum _ hs (hasSum_fintype _).summable
  obtain ⟨G, hg, hG, hGc, hz⟩ := exists_compact_probe_at W r₀ hn hsum c hε
  choose F hd hF hFw hFr using fun j ↦ exists_complex_moment_cardinal w hs r hr hw j (c + ε / 2) (half_pos hε)
  let H (x : ℝ) := G x + ∑ j, v j * F j x
  let J := Icc (c - ε) (c + ε)
  have hb (j) : tsupport (F j) ⊆ J :=
    (hF j).trans (Icc_subset_Icc (by linarith) (by linarith))
  have hFc (j) : F j c = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ by
    have := (hF j h).1
    linarith
  have hM (z : ℂ) : bilateralLaplace H z =
      bilateralLaplace G z + ∑ j, v j * bilateralLaplace (F j) z := by
    let E (x : ℝ) := cexp (z * x)
    have he : Continuous E := by dsimp [E]; fun_prop
    have hcF (j) : HasCompactSupport (F j) :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hb j)
    have hcG : HasCompactSupport G := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hG
    have hi (j) : Integrable (fun x ↦ (v j * F j x) * E x) :=
      (((continuous_const.mul (hd j).continuous).mul he).integrable_of_hasCompactSupport
        (hcF j).mul_left.mul_right)
    have hgi : Integrable (fun x ↦ G x * E x) := (hg.continuous.mul he).integrable_of_hasCompactSupport
      hcG.mul_right
    change (∫ x, (G x + ∑ j, v j * F j x) * E x) = _
    simp only [add_mul, Finset.sum_mul]
    rw [integral_add hgi (integrable_finsetSum _ fun j _ ↦ hi j), integral_finsetSum _ fun j _ ↦ hi j]
    simp only [bilateralLaplace, E, mul_assoc, integral_const_mul]
  refine ⟨H, hg.add (ContDiff.sum fun j _ ↦ contDiff_const.mul (hd j)), ?_,
    by simp [H, hGc, hFc], fun i ↦ ?_, fun j ↦ ?_⟩
  · apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hn
    have h₁ := image_eq_zero_of_notMem_tsupport (fun h ↦ hn (hG h))
    have h₂ (j) := image_eq_zero_of_notMem_tsupport (fun h ↦ hn (hb j h))
    exact hx (by simp [H, h₁, h₂])
  · rw [hM, show bilateralLaplace G (w i) = 0 from hz (.inl i)]
    simp [hFw]
  · rw [hM, show bilateralLaplace G (r j) = 0 from hz (.inr j)]
    simp [hFr]

/-- A compact smooth probe in a prescribed short window can interpolate finitely
many real Laplace moments and one physical sample while cancelling an infinite
sparse frequency family. The correcting probes are supported to the right of the
physical sample. -/
theorem exists_interpolating_probe {ι κ : Type*} [Fintype κ] (w : ι → ℂ)
    (hs : Summable fun i ↦ 1 / (1 + |(w i).im|)) (r : κ → ℝ) (hr : Function.Injective r)
    (hw : ∀ i j, w i ≠ r j) (r₀ : ℝ) (hw₀ : ∀ i, w i ≠ r₀)
    (hr₀ : ∀ j, r j ≠ r₀) (v : κ → ℂ) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℝ → ℂ, ContDiff ℝ (∞) H ∧ tsupport H ⊆ Icc (c - ε) (c + ε) ∧ H c = 1 ∧
      (∀ i, bilateralLaplace H (w i) = 0) ∧ ∀ j, bilateralLaplace H (r j) = v j :=
  exists_complex_interpolating_probe w hs (fun j ↦ (r j : ℂ)) (Complex.ofReal_injective.comp hr) hw r₀ hw₀
    (fun j h ↦ hr₀ j (Complex.ofReal_injective h)) v c hε

end RiemannMasullo.SparseLaplace
