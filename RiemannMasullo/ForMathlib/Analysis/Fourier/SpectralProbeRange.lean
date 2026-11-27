module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
public import RiemannMasullo.ForMathlib.Analysis.Complex.ExpSumUniqueness
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic

/-! # Finite-dimensional spectral data of compact tests on a half-line

Every vector in the algebraic span of the atom weights is realized by one compact
smooth test supported beyond any fixed point. This uses uniqueness of absolutely
summable exponential sums in a vertical half-plane and finite-dimensional duality.
-/

@[expose] public noncomputable section

open Classical Complex Filter Set MeasureTheory
open scoped ContDiff Topology

namespace RiemannMasullo

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

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

/-- Additivity of the bilateral Laplace transform on compact continuous tests. -/
theorem bilateralLaplace_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (z : ℂ) :
    bilateralLaplace (fun x ↦ f x + g x) z = bilateralLaplace f z + bilateralLaplace g z := by
  unfold bilateralLaplace
  simp only [add_mul]
  exact integral_add ((hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right)
    ((hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right)

/-- Multiplication of a physical test by a complex constant factors out of its transform. -/
theorem bilateralLaplace_const_mul (c : ℂ) (g : ℝ → ℂ) (z : ℂ) :
    bilateralLaplace (fun x ↦ c * g x) z = c * bilateralLaplace g z := by
  simp only [bilateralLaplace, mul_assoc, integral_const_mul]

private def tailProbeRange (w : ι → ℂ) (v : ι → E) (B : ℝ) : Submodule ℂ E where
  carrier := {e | ∃ H : ℝ → ℂ, ContDiff ℝ (∞) H ∧ HasCompactSupport H ∧ tsupport H ⊆ Ioi B ∧
    HasSum (fun i ↦ bilateralLaplace H (w i) • v i) e}
  zero_mem' := ⟨0, contDiff_const, HasCompactSupport.zero, by simp, by simp [bilateralLaplace]⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, hfc, hBf, hSf⟩ ⟨g, hg, hgc, hBg, hSg⟩
    refine ⟨fun x ↦ f x + g x, hf.add hg, hfc.add hgc, (tsupport_add f g).trans
      (union_subset hBf hBg), (hSf.add hSg).congr_fun (fun i ↦ ?_)⟩
    simp [bilateralLaplace_add hf.continuous hg.continuous hfc hgc, add_smul]
  smul_mem' := by
    rintro c _ ⟨g, hg, hgc, hBg, hSg⟩
    refine ⟨fun x ↦ c * g x, contDiff_const.mul hg, hgc.mul_left,
      tsupport_mul_subset_right.trans hBg, (hSg.const_smul c).congr_fun (fun i ↦ ?_)⟩
    rw [bilateralLaplace_const_mul, mul_smul]

private theorem exists_tail_bump (B : ℝ) (z : ℂ) :
    ∃ g : ℝ → ℂ, ContDiff ℝ (∞) g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ioi B ∧
      bilateralLaplace g z = 1 := by
  let β : ContDiffBump (B + 1) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let g (x : ℝ) := (β.normed volume x : ℂ) * cexp (-(z * x))
  have hg : ContDiff ℝ (∞) g := (Complex.ofRealCLM.contDiff.comp β.contDiff_normed).mul
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).neg.cexp)
  have hc : HasCompactSupport (fun x ↦ (β.normed volume x : ℂ)) :=
    β.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  refine ⟨g, hg, hc.mul_right, ?_, ?_⟩
  · intro x hx
    have h := (tsupport_comp_subset Complex.ofReal_zero _)
      (tsupport_mul_subset_left (f := fun x ↦ (β.normed volume x : ℂ)) hx)
    rw [β.tsupport_normed_eq] at h
    change dist x (B + 1) ≤ 1 / 2 at h
    rw [Real.dist_eq, abs_le] at h
    exact show B < x by linarith [h.1]
  · simp only [bilateralLaplace, g, mul_assoc, ← Complex.exp_add, neg_add_cancel,
      Complex.exp_zero, mul_one, integral_complex_ofReal, β.integral_normed, Complex.ofReal_one]

/-- For discrete distinct frequencies with real parts at most one half, the possible
finite-dimensional observations on smooth compact tests supported in a right half-line
are exactly the span of the atom vectors. Only absolute convergence for individual tests
on that half-line is needed. -/
theorem exists_tail_probe_iff_mem_span (w : ι → ℂ) (v : ι → E) (B : ℝ)
    (hw : Function.Injective w) (hdisc : ∀ z : ℂ, ∀ᶠ u in 𝓝[≠] z, u ∉ range w)
    (hre : ∀ i, (w i).re ≤ 1 / 2)
    (hs : ∀ H : ℝ → ℂ, ContDiff ℝ (∞) H → HasCompactSupport H → tsupport H ⊆ Ioi B →
      Summable (fun i ↦ bilateralLaplace H (w i) • v i)) (e : E) :
    (∃ H : ℝ → ℂ, ContDiff ℝ (∞) H ∧ HasCompactSupport H ∧ tsupport H ⊆ Ioi B ∧
      HasSum (fun i ↦ bilateralLaplace H (w i) • v i) e) ↔ e ∈ Submodule.span ℂ (range v) := by
  let W := tailProbeRange w v B
  change e ∈ W ↔ _
  constructor
  · rintro ⟨H, _, _, _, hH⟩
    rw [← hH.tsum_eq]
    exact tsum_mem (Submodule.span ℂ (range v)).isClosed_of_finiteDimensional fun i ↦
      Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))
  · apply (show Submodule.span ℂ (range v) ≤ W from ?_)
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_contra hn
    obtain ⟨l, hl, hker⟩ := Submodule.exists_le_ker_of_notMem hn
    let L : E →L[ℂ] ℂ := ⟨l, l.continuous_of_finiteDimensional⟩
    obtain ⟨g, hg, hgc, hBg, hgi⟩ := exists_tail_bump B (w i)
    let b (j : ι) := bilateralLaplace g (w j) * L (v j)
    have hsum (y : ℝ) (hy : 0 ≤ y) : HasSum (fun j ↦ b j * cexp (w j * y)) 0 := by
      let G (x : ℝ) := g (x - y)
      have hG : ContDiff ℝ (∞) G := hg.comp (contDiff_id.sub contDiff_const)
      have hGc : HasCompactSupport G := hgc.comp_homeomorph (Homeomorph.subRight y)
      have hGB : tsupport G ⊆ Ioi B := by
        intro x hx
        have h := hBg (tsupport_comp_subset_preimage g (continuous_id.sub continuous_const) hx)
        change B < x - y at h
        exact show B < x by linarith
      have h := (hs G hG hGc hGB).hasSum
      have hW : (∑' j, bilateralLaplace G (w j) • v j) ∈ W := ⟨G, hG, hGc, hGB, h⟩
      have hz : L (∑' j, bilateralLaplace G (w j) • v j) = 0 := hker hW
      rw [← hz]
      apply (L.hasSum h).congr_fun
      intro j
      simp only [G, b, map_smul, smul_eq_mul, bilateralLaplace_translate]
      ring
    have hb : Summable b := by simpa using (hsum 0 le_rfl).summable
    have hzero := eq_zero_of_hasSum_exp_eq_zero w b hw hdisc hre hb hsum i
    apply hl
    change L (v i) = 0
    simpa only [b, hgi, one_mul] using hzero

end RiemannMasullo
