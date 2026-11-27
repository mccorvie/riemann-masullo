module
public import RiemannMasullo.ForMathlib.Analysis.Fourier.CompactCardinal
@[expose] public noncomputable section
open MeasureTheory Set Function Filter
open scoped SchwartzMap ContDiff Topology FourierTransform
namespace RiemannMasullo

private theorem schwartz_fourier_zero (f : 𝓢(ℝ, ℂ)) : 𝓕 f 0 = ∫ x, f x := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  simp

private theorem schwartz_fourier_deriv_zero (f : 𝓢(ℝ, ℂ)) :
    deriv (fun x ↦ 𝓕 f x) 0 = (-2 * Real.pi * Complex.I) * ∫ x : ℝ, (x : ℂ) * f x := by
  have hxi : Integrable (fun x : ℝ ↦ x • f x) := by
    apply (f.integrable_pow_mul volume 1).mono' (by fun_prop)
    exact .of_forall fun x ↦ by simp
  change deriv (𝓕 (f : ℝ → ℂ)) 0 = _
  rw [Real.deriv_fourier f.integrable hxi, Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, smul_eq_mul]
  simpa only [one_mul, mul_assoc] using
    (integral_const_mul (μ := volume) (-2 * (Real.pi : ℂ) * Complex.I)
      (fun x : ℝ ↦ (x : ℂ) * f x))

private theorem exists_schwartz_modulation (f : 𝓢(ℝ, ℂ))
    (hf : HasCompactSupport (f : ℝ → ℂ)) (a : ℝ) :
    ∃ g : 𝓢(ℝ, ℂ), HasCompactSupport (g : ℝ → ℂ) ∧
      tsupport (g : ℝ → ℂ) ⊆ tsupport (f : ℝ → ℂ) ∧
      (∀ x, g x = Complex.exp ((2 * Real.pi * a * x : ℝ) * Complex.I) * f x) ∧
      ∀ ξ, 𝓕 g ξ = 𝓕 f (ξ - a) := by
  let v (x : ℝ) := Complex.exp ((2 * Real.pi * a * x : ℝ) * Complex.I) * f x
  have hc : HasCompactSupport v := hf.mul_left
  have hs : ContDiff ℝ ∞ v := by
    have hp : ContDiff ℝ ∞ (fun x : ℝ ↦ ((2 * Real.pi * a * x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
    exact (hp.mul contDiff_const).cexp.mul (f.smooth ⊤)
  let g := hc.toSchwartzMap hs
  refine ⟨g, hc, ?_, fun _ ↦ rfl, fun ξ ↦ ?_⟩
  · exact closure_mono (support_mul_subset_right _ _)
  · rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
      Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae (.of_forall fun x ↦ ?_)
    change Complex.exp _ • (Complex.exp _ * f x) = _
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring

private theorem exists_schwartz_nonzero_cardinal {L : ℝ}
    (b : 𝓢(ℝ, ℂ)) (hb : HasCompactSupport (b : ℝ → ℂ))
    (hm : ∀ j : ℤ, 𝓕 b ((j : ℝ) / L) = if j = 0 then 1 else 0)
    (hd : ∀ j : ℤ, j ≠ 0 → deriv (fun x ↦ 𝓕 b x) ((j : ℝ) / L) = 0)
    (n : ℤ) (hn : n ≠ 0) :
    ∃ g : 𝓢(ℝ, ℂ), HasCompactSupport (g : ℝ → ℂ) ∧
      tsupport (g : ℝ → ℂ) ⊆ tsupport (b : ℝ → ℂ) ∧
      (∫ x, g x) = 0 ∧ (∫ x : ℝ, (x : ℂ) * g x) = 0 ∧
      ∀ j : ℤ, 𝓕 g ((j : ℝ) / L) = if j = n then 1 else 0 := by
  obtain ⟨g, hg, hgb, hpoint, hF⟩ := exists_schwartz_modulation b hb ((n : ℝ) / L)
  have hmesh (j : ℤ) : 𝓕 g ((j : ℝ) / L) = if j = n then 1 else 0 := by
    rw [hF, ← sub_div, ← Int.cast_sub, hm]
    simp only [sub_eq_zero]
  have hmass : (∫ x, g x) = 0 := by
    rw [← schwartz_fourier_zero]
    simpa [hn, eq_comm] using hmesh 0
  have hderiv : deriv (fun x ↦ 𝓕 g x) 0 = 0 := by
    have hshift := ((𝓕 b : 𝓢(ℝ, ℂ)).hasDerivAt (0 - (n : ℝ) / L)).scomp 0
      (show HasDerivAt (fun x : ℝ ↦ x - (n : ℝ) / L) 1 0 from
        (hasDerivAt_id (0 : ℝ)).sub_const ((n : ℝ) / L))
    have hb' : deriv (fun x ↦ 𝓕 b x) (0 - (n : ℝ) / L) = 0 := by
      simpa only [zero_sub, Int.cast_neg, neg_div] using hd (-n) (neg_ne_zero.mpr hn)
    rw [show (fun x ↦ 𝓕 g x) = (fun x ↦ 𝓕 b (x - (n : ℝ) / L)) from funext hF]
    simpa only [Function.comp_def, hb', smul_zero] using hshift.deriv
  have hmom : (∫ x : ℝ, (x : ℂ) * g x) = 0 := by
    rw [schwartz_fourier_deriv_zero] at hderiv
    exact (mul_eq_zero.mp hderiv).resolve_left (by
      simp only [mul_eq_zero, neg_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_eq_zero,
        Real.pi_ne_zero, Complex.I_ne_zero, or_self, not_false_eq_true])
  exact ⟨g, hg, hgb, hmass, hmom, hmesh⟩

private theorem exists_schwartz_zero_cardinal {L : ℝ} (b : 𝓢(ℝ, ℂ))
    (hb : HasCompactSupport (b : ℝ → ℂ))
    (hm : ∀ j : ℤ, 𝓕 b ((j : ℝ) / L) = if j = 0 then 1 else 0) :
    ∃ g : 𝓢(ℝ, ℂ), HasCompactSupport (g : ℝ → ℂ) ∧
      tsupport (g : ℝ → ℂ) ⊆ tsupport (b : ℝ → ℂ) ∧
      (∫ x, g x) = 0 ∧ 2 * (∫ x : ℝ, (x : ℂ) * g x) = 1 ∧
      ∀ j : ℤ, 𝓕 g ((j : ℝ) / L) = 0 := by
  let d := SchwartzMap.derivCLM ℂ ℂ b
  let g := (-1 / 2 : ℂ) • d
  have hdc : HasCompactSupport (d : ℝ → ℂ) := hb.deriv
  have hgc : HasCompactSupport (g : ℝ → ℂ) := hdc.smul_left
  have hgb : tsupport (g : ℝ → ℂ) ⊆ tsupport (b : ℝ → ℂ) :=
    (closure_mono (support_smul_subset_right _ _)).trans (SchwartzMap.tsupport_derivCLM_subset ℂ b)
  have hF (ξ : ℝ) : 𝓕 g ξ = -(Real.pi : ℂ) * Complex.I * ξ * 𝓕 b ξ := by
    change 𝓕 ((-1 / 2 : ℂ) • d) ξ = _
    rw [FourierTransform.fourier_smul, smul_apply]
    have hdF := congrFun (Real.fourier_deriv b.integrable b.differentiable d.integrable) ξ
    change 𝓕 (d : ℝ → ℂ) ξ = _ at hdF
    rw [SchwartzMap.fourier_coe, hdF, SchwartzMap.fourier_coe]
    simp only [smul_eq_mul]
    ring
  have hb0 : 𝓕 b 0 = 1 := by simpa using hm 0
  have hmom : 2 * (∫ x : ℝ, (x : ℂ) * g x) = 1 := by
    have hg' := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul
      (-(Real.pi : ℂ) * Complex.I)).mul ((𝓕 b : 𝓢(ℝ, ℂ)).hasDerivAt 0)
    have hgder : deriv (fun x ↦ 𝓕 g x) 0 = -(Real.pi : ℂ) * Complex.I := by
      rw [show (fun x ↦ 𝓕 g x) = (fun x : ℝ ↦ -(Real.pi : ℂ) * Complex.I * x * 𝓕 b x)
        from funext hF]
      simpa only [id_eq, Pi.mul_def, Complex.ofReal_zero, Complex.ofReal_one, mul_zero, zero_mul, add_zero, mul_one, hb0] using hg'.deriv
    rw [schwartz_fourier_deriv_zero] at hgder
    have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
    apply (mul_left_cancel₀ hpi)
    calc
      (Real.pi : ℂ) * Complex.I * (2 * ∫ x : ℝ, (x : ℂ) * g x) =
          -((-2 * Real.pi * Complex.I) * ∫ x : ℝ, (x : ℂ) * g x) := by ring
      _ = (Real.pi : ℂ) * Complex.I * 1 := by rw [hgder]; ring
  refine ⟨g, hgc, hgb, ?_, hmom, fun j ↦ ?_⟩
  · rw [← schwartz_fourier_zero, hF]; simp
  · rw [hF, hm]
    split_ifs with hj
    · simp [hj]
    · simp

/-- Compact smooth profiles in one common support set, with zero mass, a prescribed
first moment for the zero mode, and arbitrary cardinal values on every nonzero
Fourier mesh row. -/
theorem exists_compact_schwartz_polar_cardinals {L : ℝ} (hL : 0 < L) (U : ℝ)
    (c : ℤ → ℂ) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Iio U ∧ ∃ H : ℤ → 𝓢(ℝ, ℂ), ∀ n : ℤ,
      HasCompactSupport (H n : ℝ → ℂ) ∧ tsupport (H n : ℝ → ℂ) ⊆ K ∧
      (∫ x, H n x) = 0 ∧ 2 * (∫ x : ℝ, (x : ℂ) * H n x) = (if n = 0 then 1 else 0) ∧
      ∀ j : ℤ, j ≠ 0 → 𝓕 (H n) ((j : ℝ) / L) = if j = n then c n else 0 := by
  classical
  obtain ⟨b, hb, hbU, hm, hd⟩ := exists_compact_schwartz_double_mesh hL U
  refine ⟨tsupport (b : ℝ → ℂ), hb, hbU, ?_⟩
  suffices hdata : ∀ n : ℤ, ∃ g : 𝓢(ℝ, ℂ), HasCompactSupport (g : ℝ → ℂ) ∧
      tsupport (g : ℝ → ℂ) ⊆ tsupport (b : ℝ → ℂ) ∧ (∫ x, g x) = 0 ∧
      2 * (∫ x : ℝ, (x : ℂ) * g x) = (if n = 0 then 1 else 0) ∧
      ∀ j : ℤ, j ≠ 0 → 𝓕 g ((j : ℝ) / L) = if j = n then c n else 0 by
    choose H hH using hdata
    exact ⟨H, hH⟩
  intro n
  by_cases hn : n = 0
  · subst n
    obtain ⟨g, hg, hgb, hmass, hmom, hmesh⟩ := exists_schwartz_zero_cardinal b hb hm
    exact ⟨g, hg, hgb, hmass, by simpa using hmom, fun j hj ↦ by simp [hmesh, hj]⟩
  · obtain ⟨g, hg, hgb, hmass, hmom, hmesh⟩ := exists_schwartz_nonzero_cardinal b hb hm hd n hn
    refine ⟨c n • g, hg.smul_left, (closure_mono (support_smul_subset_right _ _)).trans hgb, ?_, ?_, ?_⟩
    · simp only [smul_apply, integral_smul, hmass, smul_zero]
    · simp only [smul_apply, smul_eq_mul]
      have heq (x : ℝ) : (x : ℂ) * (c n * g x) = c n * ((x : ℂ) * g x) := by ring
      simp_rw [heq]
      rw [integral_const_mul, hmom]
      simp [hn]
    · intro j hj
      rw [FourierTransform.fourier_smul, smul_apply, hmesh]
      split_ifs <;> simp

end RiemannMasullo
