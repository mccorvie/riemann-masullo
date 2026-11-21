module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Complete
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

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

/-- Paper: Lemma D.3.1.2, p. 799. Weighted Lᵖ norms on a sequence of lines
reaching both ends of the interval generate the Schwartz–Bergman topology.
Deviation: The endpoint condition is expressed by bracketing every real point of I. -/
theorem schwartzBergman_lp_generates (I : Set ℝ) (hI : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) (a : ℕ → I)
    (ha : ∀ x : I, (∃ n, (a n : ℝ) < x) ∧ ∃ n, (x : ℝ) < a n)
    (p : ℝ≥0∞) (hp : 1 < p) (hp' : p < ⊤) :
    GeneratesLpSeminorms volume p
      (fun (i : ℕ × ℕ) (f : SchwartzBergman I) ↦ weightedVerticalTrace (a i.1) i.2 f.val) :=
  by sorry

/-- Paper: Lemma D.3.1.2, p. 799. The topology also comes from taking the
Schwartz restriction to each vertical line. -/
theorem schwartzBergman_schwartzLine_topology (I : Set ℝ) (hI : IsOpen I)
    (hInt : OrdConnected I) (hne : I.Nonempty) :
    ∃ T : SchwartzBergman I → (I → 𝓢(ℝ, ℂ)),
      (∀ f (a : I) x, T f a x = weightedVerticalTrace a 0 f.val x) ∧ IsEmbedding T :=
  by sorry

/-- Paper: Lemma D.3.1.2, p. 799. The Schwartz–Bergman space is Fréchet. -/
theorem schwartzBergman_frechet (I : Set ℝ) (hI : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) : IsFrechetTVS (SchwartzBergman I) := by sorry

/-- Paper: Lemma D.3.1.2, p. 799. The Schwartz–Bergman space is separable. -/
theorem schwartzBergman_separable (I : Set ℝ) (hI : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) : SeparableSpace (SchwartzBergman I) := by sorry

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
    BarrelledSpace ℂ E ∧ MontelSpace ℂ E := by sorry

/-- Paper: Lemma D.3.2.3(2), p. 801. The strong dual is complete. -/
theorem positiveRealExponentialDecay_strongDual_complete (hInt : OrdConnected I) (hne : I.Nonempty) :
    CompleteSpace D := by sorry

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
    MellinConvergent (fun t ↦ f.val (Real.log t)) s := by sorry

/-- Paper: Proposition D.3.2.5, p. 802. The Mellin integral induces a unique
continuous linear equivalence with the Schwartz–Bergman space on the strip. -/
theorem existsUnique_positiveRealFourierMellin (hOpen : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) :
    ∃! M : E ≃L[ℂ] SchwartzBergman I, ∀ (f : E) (s : ℂ), s.re ∈ I →
      (M f).val s = mellin (fun t ↦ f.val (Real.log t)) s := by sorry

/-- Paper: Definition D.3.2.6, p. 803. The Fourier–Mellin transform is
the continuous linear equivalence furnished by the Mellin integral. -/
def positiveRealFourierMellin (hOpen : IsOpen I) (hInt : OrdConnected I) (hne : I.Nonempty) :
    E ≃L[ℂ] SchwartzBergman I :=
  Classical.choose (existsUnique_positiveRealFourierMellin I hOpen hInt hne).exists

/-- Paper: Definition D.3.2.6, p. 803. Evaluation of the Fourier–Mellin
transform on the strip gives the absolutely convergent Mellin integral. -/
theorem positiveRealFourierMellin_apply (hOpen : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) (f : E) (s : ℂ) (hs : s.re ∈ I) :
    (positiveRealFourierMellin I hOpen hInt hne f).val s =
      mellin (fun t ↦ f.val (Real.log t)) s := by sorry

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

/-- Paper: Lemma D.3.2.7(1), p. 803. Each weighted derivative is in L² and its
L² norm defines a continuous seminorm. The choice b = 0 includes (D.3.2.3). -/
theorem exponentialDecayL2_continuous_seminorm (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (m : ℕ) :
    let w := exponentialDecayL2Integrand a b m
    (∀ f, MemLp (w f) 2 volume) ∧
      ∃ p : Seminorm ℂ (PositiveRealExponentialDecay univ), Continuous p ∧
        ∀ f, ENNReal.ofReal (p f) = eLpNorm (w f) 2 volume := by sorry

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
    modulatedExponentialDecaySubmodule m {0} = schwartzBruhatSubmodule G := by sorry

/-- Paper: (D.3.3.2), p. 805. The given exponent supplies the corresponding
Schwartz–Bruhat membership. -/
theorem modulationWeight_mem_schwartzBruhat (a : I) (f : modulatedExponentialDecaySubmodule m I) :
    modulationWeight m a f.val ∈ schwartzBruhatSubmodule G := by sorry

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
  by sorry

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
  by sorry

/-- Paper: Definition D.3.3.3, p. 805. Use the descended modulation to form
the projective system on the quotient by a compact subgroup. -/
def quotientModulation (k : Subgroup G) (hk : IsCompact (k : Set G)) : (G ⧸ k) →ₜ* ℝ≥0ˣ where
  toMonoidHom := QuotientGroup.lift k m.toMonoidHom (compactSubgroup_le_modulation_ker m k hk)
  continuous_toFun := continuous_quotientModulation m k hk

/-- Paper: Definition D.3.3.3, p. 805. The descended modulation agrees with
the original one on each coset representative. -/
theorem quotientModulation_apply (k : Subgroup G) (hk : IsCompact (k : Set G)) (g : G) :
    quotientModulation m k hk (g : G ⧸ k) = m g := by sorry

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
