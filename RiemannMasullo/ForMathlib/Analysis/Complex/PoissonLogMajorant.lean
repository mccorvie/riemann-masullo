module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Poisson majorization of the logarithm on a finite disk

Reflect each interior linear zero factor to a zero-free factor with the same boundary modulus.
The logarithm of the reflected product gives a harmonic majorant at every nonzero interior value. -/

public noncomputable section

open Complex Metric Set Filter
open scoped ComplexConjugate
namespace RiemannMasullo

private theorem disk_reflected_normSq (R : ℝ) (a z : ℂ) :
    Complex.normSq ((R : ℂ)^2 - conj a * z) - R^2 * Complex.normSq (z-a) =
      (R^2-Complex.normSq a)*(R^2-Complex.normSq z) := by
  simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, ← Complex.ofReal_pow]
  ring

/-- The reflected linear factor on a disk is harmonic after taking its log norm.
It agrees in modulus with the original factor on the circle and majorizes it inside. -/
private def reflectedLogFactor (R : ℝ) (a z : ℂ) : ℝ :=
  Real.log ‖((R : ℂ)^2-conj a*z)/(R : ℂ)‖

private theorem reflectedLogFactor_spec {R : ℝ} {a q : ℂ} (ha : a ∈ ball 0 R)
    (hq : q ∈ ball 0 R) (hneq : q ≠ a) :
    InnerProductSpace.HarmonicOnNhd (reflectedLogFactor R a) (closedBall 0 R) ∧
    (∀ z ∈ sphere 0 R, reflectedLogFactor R a z = Real.log ‖z-a‖) ∧
    Real.log ‖q-a‖ ≤ reflectedLogFactor R a q := by
  have hR : 0 < R := pos_of_mem_ball ha
  have haR := mem_ball_zero_iff.1 ha
  have hqR := mem_ball_zero_iff.1 hq
  let g (z : ℂ) := ((R : ℂ)^2-conj a*z) / (R : ℂ)
  have hg : AnalyticOnNhd ℂ g (closedBall 0 R) := by
    intro z _
    dsimp [g]
    fun_prop
  have hg0 (z : ℂ) (hz : z ∈ closedBall 0 R) : g z ≠ 0 := by
    have hmul : ‖conj a * z‖ < (R : ℝ)^2 := by
      rw [norm_mul,Complex.norm_conj, pow_two]
      exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos haR
        (mem_closedBall_zero_iff.1 hz) (norm_nonneg _) hR
    have hn : (R : ℂ)^2 ≠ conj a*z := by
      intro he
      rw [←he,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR] at hmul
      exact (lt_irrefl _ hmul)
    exact div_ne_zero (sub_ne_zero.2 hn) (by exact_mod_cast hR.ne')
  have hlog : InnerProductSpace.HarmonicOnNhd (fun z : ℂ ↦ Real.log ‖g z‖) (closedBall 0 R) :=
    fun z hz ↦ (hg z hz).harmonicAt_log_norm (hg0 z hz)
  have hbound (z : ℂ) (hz : z ∈ sphere 0 R) : ‖g z‖ = ‖z-a‖ := by
    have hn := Complex.norm_canonicalFactor_eval_circle_eq_one ha hz
    have hza : z-a ≠ 0 := by
      intro h
      have he : z=a := sub_eq_zero.1 h
      exact haR.ne (he ▸ mem_sphere_zero_iff_norm.1 hz)
    rw [Complex.canonicalFactor_apply, norm_div, norm_mul, div_eq_one_iff_eq] at hn
    · dsimp [g]
      rw [norm_div, hn, mul_div_cancel_left₀ _ (norm_ne_zero_iff.2 (by exact_mod_cast hR.ne'))]
    · exact mul_ne_zero (norm_ne_zero_iff.2 (by exact_mod_cast hR.ne')) (norm_ne_zero_iff.2 hza)
  have hcomp : ‖q-a‖ ≤ ‖g q‖ := by
    dsimp [g]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, le_div_iff₀ hR]
    have h := disk_reflected_normSq R a q
    simp only [Complex.normSq_eq_norm_sq] at h
    have hp : 0 ≤ (R^2-‖a‖^2)*(R^2-‖q‖^2) := mul_nonneg
      (sub_nonneg.2 (pow_le_pow_left₀ (norm_nonneg _) haR.le 2))
      (sub_nonneg.2 (pow_le_pow_left₀ (norm_nonneg _) hqR.le 2))
    nlinarith [norm_nonneg (q-a),norm_nonneg ((R:ℂ)^2-conj a*q), mul_nonneg (norm_nonneg (q-a)) hR.le]
  exact ⟨hlog, fun z hz ↦ congrArg Real.log (hbound z hz),
    Real.log_le_log (norm_pos_iff.2 (sub_ne_zero.2 hneq)) hcomp⟩

/-- Finite-disk Poisson majorization of the logarithm. A zero-free boundary is
sufficient because the radii with a boundary zero form a countable set. -/
theorem log_norm_le_circleAverage_poisson_of_boundary_nonzero {R : ℝ} {q : ℂ}
    {f : ℂ → ℂ} (hq : q ∈ ball 0 R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hq0 : f q ≠ 0) (hcircle : ∀ z ∈ sphere 0 R, f z ≠ 0) :
    Real.log ‖f q‖ ≤ Real.circleAverage (poissonKernel 0 q • (fun z : ℂ ↦ Real.log ‖f z‖)) 0 R := by
  classical
  let CB := closedBall (0 : ℂ) R
  let D := MeromorphicOn.divisor f CB
  have hR := pos_of_mem_ball hq
  have hqc : q ∈ CB := ball_subset_closedBall hq
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall 0 R)
  let S := hfin.toFinset
  have hs (a : ℂ) : a ∈ S ↔ D a ≠ 0 := hfin.mem_toFinset
  have hdiv (z : ℂ) (hz : z ∈ CB) (h0 : f z ≠ 0) : D z = 0 := by
    rw [show D z = (meromorphicOrderAt f z).untop₀ from hf.meromorphicOn.divisor_apply hz,
      (hf z hz).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2 h0]
    rfl
  have interior (a : ℂ) (ha : a ∈ S) : a ∈ ball 0 R := by
    have hcb := D.supportWithinDomain ((hs a).1 ha)
    by_contra hh
    have he : a ∈ sphere 0 R := mem_sphere_zero_iff_norm.2
      (le_antisymm (mem_closedBall_zero_iff.1 hcb) (not_lt.1 (fun t ↦ hh (mem_ball_zero_iff.2 t))))
    exact (hs a).1 ha (hdiv a hcb (hcircle a he))
  have htop (a : CB) : meromorphicOrderAt f a ≠ ⊤ :=
    hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall (0 : ℂ) R).isPreconnected hqc a.property
      (by rw [(hf q hqc).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2 hq0]; simp)
  obtain ⟨g,hg,hg0,hfg⟩ := hf.meromorphicOn.extract_zeros_poles htop hfin
  have hspec (a : ℂ) (ha : a ∈ S) := reflectedLogFactor_spec (interior a ha) hq
    (show q ≠ a from fun h ↦ (hs a).1 ha (h ▸ hdiv q hqc hq0))
  let H : ℂ → ℝ := (∑ a ∈ S, (D a : ℝ) • reflectedLogFactor R a) + (fun z ↦ Real.log ‖g z‖)
  have hH : InnerProductSpace.HarmonicOnNhd H CB := by
    refine InnerProductSpace.HarmonicOnNhd.add ?_ (fun z hz ↦ (hg z hz).harmonicAt_log_norm (hg0 ⟨z,hz⟩))
    have hsum (A : Finset ℂ) (hA : A ⊆ S) :
        InnerProductSpace.HarmonicOnNhd (∑ a ∈ A, (D a : ℝ) • reflectedLogFactor R a) CB := by
      induction A using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty]
        exact fun z _ ↦ InnerProductSpace.harmonicAt_const (x := z) (0 : ℝ)
      | insert a A ha ih =>
        rw [Finset.sum_insert ha]
        exact ((hspec a (hA (Finset.mem_insert_self a A))).1.const_smul).add
          (ih (fun z hz ↦ hA (Finset.mem_insert_of_mem hz)))
    exact hsum S (fun _ h ↦ h)
  have finlog (z : ℂ) : ∑ᶠ a, (D a : ℝ) * Real.log ‖z-a‖ = ∑ a ∈ S, (D a : ℝ)*Real.log ‖z-a‖ := by
    apply finsum_eq_sum_of_support_subset
    intro a ha
    apply (hs a).2
    intro h
    exact ha (by simp [h])
  have acc : AccPt q (Filter.principal CB) := by
    apply accPt_iff_frequently_nhdsNE.2
    have hev : CB ∈ nhds q := Filter.mem_of_superset (isOpen_ball.mem_nhds hq) ball_subset_closedBall
    exact (show ∀ᶠ z in nhdsWithin q {q}ᶜ, z ∈ CB from nhdsWithin_le_nhds hev).frequently
  have atq := MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles
    (D := fun z ↦ D z) hfin hqc acc (hf q hqc).meromorphicAt (hg q hqc) (hg0 ⟨q,hqc⟩) hfg
  rw [(hf q hqc).meromorphicTrailingCoeffAt_of_ne_zero hq0, finlog] at atq
  have hu : Real.log ‖f q‖ ≤ H q := by
    rw [atq]
    simp only [H, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact add_le_add (Finset.sum_le_sum (fun a ha ↦
      mul_le_mul_of_nonneg_left (hspec a ha).2.2 (by exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf) a))) le_rfl
  rw [← hH.circleAverage_poissonKernel_smul hq] at hu
  apply hu.trans_eq
  let hlog := MeromorphicOn.extract_zeros_poles_log hg0 hfg
  have hfs : (∑ᶠ a, (fun z : ℂ ↦ (D a : ℝ)*Real.log ‖z-a‖)) =
      fun z ↦ ∑ a ∈ S, (D a : ℝ)*Real.log ‖z-a‖ := by
    rw [finsum_eq_sum_of_support_subset (s := S)]
    · ext z
      simp
    · intro a ha
      apply (hs a).2
      intro h
      exact ha (by funext z; simp [h])
  have hsc : sphere (0 : ℂ) |R| ⊆ CB := by simpa only [abs_of_pos hR] using (sphere_subset_closedBall (x := (0 : ℂ)) (ε := R))
  apply Real.circleAverage_congr_codiscreteWithin _ hR.ne'
  filter_upwards [hlog.filter_mono (codiscreteWithin_mono hsc),
    self_mem_codiscreteWithin (sphere (0 : ℂ) |R|)] with z hz hzc
  rw [abs_of_pos hR] at hzc
  change poissonKernel 0 q z * (H z) = poissonKernel 0 q z * Real.log ‖f z‖
  congr 1
  rw [hz]
  change H z = (∑ᶠ a, (fun z : ℂ ↦ (D a : ℝ)*Real.log ‖z-a‖)) z + Real.log ‖g z‖
  rw [hfs]
  simp only [H, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_left_inj]
  exact Finset.sum_congr rfl (fun a ha ↦ congrArg ((D a : ℝ) * ·) ((hspec a ha).2.1 z hzc))

end RiemannMasullo
