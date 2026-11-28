module
public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxMellin
public import RiemannMasullo.ForMathlib.Analysis.Fourier.PolarCardinal
public import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.LogAnnulus

/-! # Common-box cardinal lifts for rational theta packets

A double-zero compact log profile supplies the nonzero modes by modulation and
the zero mode by differentiation. Its inverse-Jacobian annular lift has both
polar values zero. Poisson/Mellin factorization normalizes the nonzero rows by
`2 ζ(1-it)`; the logarithmic moment supplies the removable row at zero. Earlier
Euler factors then give the actual normalized successive-stage rows.

The construction follows the rational packet argument of fpet19 in
https://github.com/mccorvie/riemann-masullo/issues/7351#issuecomment-7149080501.
-/

@[expose] public noncomputable section
open Filter MeasureTheory Set Function FourierTransform
open scoped FourierTransform SchwartzMap Topology
namespace RiemannMasullo.RationalPacket

/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496. All imaginary-line cardinal
modes of one rational trivial-angular packet have actual polar Schwartz lifts
whose Fourier transforms lie in a single compact annulus inside a prescribed box.
Deviation: this establishes the simultaneous smooth lifts and their exact rows;
it does not assert a basis theorem for the completed packet. -/
theorem exists_fixedBox_theta_cardinals {p U : ℝ} (hp : 1 < p) (hU : 0 < U) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ f : ℤ → 𝓢(ℝ, ℂ), ∀ n : ℤ,
      f n 0 = 0 ∧ (𝓕 (f n)) 0 = 0 ∧
      HasCompactSupport (⇑(𝓕 (f n) : 𝓢(ℝ, ℂ))) ∧
      (∀ r, (𝓕 (f n)) (-r) = (𝓕 (f n)) r) ∧
      (∀ r, |r| < ε ∨ U < |r| → (𝓕 (f n)) r = 0) ∧
      ∀ j : ℤ, thetaBoundaryMellin (f n)
        (((2 * Real.pi * ((j : ℝ) / Real.log p) : ℝ) : ℂ) * Complex.I) =
          if j = n then 1 else 0 := by
  classical
  let L := Real.log p
  have hL : 0 < L := Real.log_pos hp
  let c (n : ℤ) : ℂ := (2 * riemannZeta
    (1 - (((2 * Real.pi * ((n : ℝ) / L) : ℝ) : ℂ) * Complex.I)))⁻¹
  obtain ⟨K, hK, hKU, H, hH⟩ := exists_compact_schwartz_polar_cardinals hL (Real.log U) c
  obtain ⟨A, hA⟩ := hK.bddBelow
  suffices hdata : ∀ n : ℤ, ∃ f : 𝓢(ℝ, ℂ), f 0 = 0 ∧ (𝓕 f) 0 = 0 ∧
      HasCompactSupport (⇑(𝓕 f : 𝓢(ℝ, ℂ))) ∧ (∀ r, (𝓕 f) (-r) = (𝓕 f) r) ∧
      (∀ r, |r| < Real.exp A ∨ U < |r| → (𝓕 f) r = 0) ∧
      ∀ j : ℤ, thetaBoundaryMellin f
        (((2 * Real.pi * ((j : ℝ) / L) : ℝ) : ℂ) * Complex.I) = if j = n then 1 else 0 by
    choose f hf using hdata
    exact ⟨Real.exp A, Real.exp_pos A, f, hf⟩
  intro n
  obtain ⟨hHc, hHK, hmass, hmom, hmesh⟩ := hH n
  obtain ⟨h, hc, hz, he, hh⟩ := exists_schwartz_log_annulus (H n) hHc
  let f := 𝓕⁻ h
  have hF : 𝓕 f = h := fourier_fourierInv_eq h
  have hf0 : f 0 = 0 := by
    change (𝓕⁻ h) 0 = 0
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_zero,
      Real.fourier_real_eq_integral_exp_smul]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    rw [integral_log_annulus (H n) h hh, hmass, mul_zero]
  have hb (r : ℝ) (hr : |r| < Real.exp A ∨ U < |r|) : h r = 0 := by
    by_cases hr0 : r = 0
    · simpa [hr0] using hz
    have hHz : H n (Real.log |r|) = 0 := by
      by_contra hnz
      have hmem := hHK (subset_tsupport (H n : ℝ → ℂ) hnz)
      rcases hr with hr | hr
      · exact (not_le_of_gt ((Real.log_lt_iff_lt_exp (abs_pos.mpr hr0)).mpr hr)) (hA hmem)
      · exact (not_lt_of_ge ((Real.log_le_log_iff hU (abs_pos.mpr hr0)).mpr hr.le)) (hKU hmem)
    rw [hh, hHz, smul_zero]
  have hfactor := thetaBoundaryMellin_factor_and_zero hU f hf0
    (by rw [hF]; exact hz) (by simpa only [hF] using he)
    (fun r hr ↦ by rw [hF]; exact hb r (Or.inr hr))
  refine ⟨f, hf0, by rw [hF]; exact hz, by rw [hF]; exact hc,
    by simpa only [hF] using he, by simpa only [hF] using hb, fun j ↦ ?_⟩
  by_cases hj : j = 0
  · subst j
    simp only [Int.cast_zero, zero_div, mul_zero, Complex.ofReal_zero, zero_mul]
    rw [hfactor.2, hF, logMoment_log_annulus (H n) h hHc hh, hmom]
    simp only [eq_comm]
  · have ht : 2 * Real.pi * ((j : ℝ) / L) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (div_ne_zero (Int.cast_ne_zero.mpr hj) hL.ne')
    obtain ⟨hfactors, hζ⟩ := hfactor.1 (2 * Real.pi * ((j : ℝ) / L)) ht
    rw [hfactors, hF, show (⇑h) = (fun r : ℝ ↦ (|r|⁻¹ : ℝ) • H n (Real.log |r|)) from funext hh,
      mellin_log_annulus_fourier, ← SchwartzMap.fourier_coe, hmesh j hj]
    by_cases hjn : j = n
    · subst j
      simpa only [c, ite_true] using
        mul_inv_cancel₀ (mul_ne_zero (show (2 : ℂ) ≠ 0 by norm_num) hζ)
    · simp [hjn]

private theorem cardinals_damped_integrable {U : ℝ} (hU : 0 < U)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) (f : 𝓢(ℝ, ℂ))
    (hf : f 0 = 0) (hF0 : (𝓕 f) 0 = 0) (hb : ∀ r, U < |r| → (𝓕 f) r = 0) :
    ∀ S ⊆ T, Integrable (dampedStage S f) := by
  intro S hS
  have hprod : 0 < ∏ q ∈ S, (q : ℝ) := Finset.prod_pos fun q hq ↦ by
    exact_mod_cast (hT q (hS hq)).pos
  exact (stage_memLp_and_dampedStage_integrable (X := U * ∏ q ∈ S, (q : ℝ))
    (mul_pos hU hprod) S (fun q hq ↦ (hT q (hS hq)).one_lt.le) hf hF0
    (by simpa only [mul_div_cancel_right₀ _ hprod.ne'] using hb)).2

/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496. The actual normalized rows of
any earlier-prime rational stage have simultaneous cardinal lifts in one fixed
Fourier annulus. The zero row is the leading coefficient of order `T.card`,
including when the raw earlier-stage value at zero vanishes automatically.
Deviation: this is a theorem about actual smooth sources, before completion. -/
theorem exists_fixedBox_stage_cardinals {p : ℕ} (hp : p.Prime)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) (hpT : p ∉ T) {U : ℝ} (hU : 0 < U) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ f : ℤ → 𝓢(ℝ, ℂ), ∀ n : ℤ,
      f n 0 = 0 ∧ (𝓕 (f n)) 0 = 0 ∧
      HasCompactSupport (⇑(𝓕 (f n) : 𝓢(ℝ, ℂ))) ∧
      (∀ r, (𝓕 (f n)) (-r) = (𝓕 (f n)) r) ∧
      (∀ r, |r| < ε ∨ U < |r| → (𝓕 (f n)) r = 0) ∧
      (∀ j : ℤ, j ≠ 0 →
        𝓕 (dampedStage T (f n)) ((j : ℝ) / Real.log p) /
          (∏ q ∈ T, (1 - (Real.fourierChar (Real.log q * ((j : ℝ) / Real.log p)) : ℂ))) =
            if j = n then 1 else 0) ∧
      Tendsto (fun ξ : ℝ ↦ 𝓕 (dampedStage T (f n)) ξ /
        ((∏ q ∈ T, -(2 * (Real.pi : ℂ) * Complex.I * Real.log q)) * (ξ : ℂ)^T.card))
        (𝓝[≠] 0) (𝓝 (if n = 0 then 1 else 0)) := by
  classical
  obtain ⟨ε, hε, f, hf⟩ := exists_fixedBox_theta_cardinals
    (show (1 : ℝ) < p by exact_mod_cast hp.one_lt) hU
  refine ⟨ε, hε, fun n ↦ f (-n), fun n ↦ ?_⟩
  obtain ⟨hf0, hF0, hFc, he, hb, hrows⟩ := hf (-n)
  have hempty (j : ℤ) : 𝓕 (dampedStage ∅ (f (-n))) ((j : ℝ) / Real.log p) =
      if j = n then 1 else 0 := by
    have hphase : (((2 * Real.pi * (((-j : ℤ) : ℝ) / Real.log p) : ℝ) : ℂ) * Complex.I) =
        ((-2 * Real.pi * ((j : ℝ) / Real.log p) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have h := hrows (-j)
    rw [hphase, thetaBoundaryMellin_fourier] at h
    simpa only [neg_inj] using h
  have hi := cardinals_damped_integrable hU T hT (f (-n)) hf0 hF0
    (fun r hr ↦ hb r (Or.inr hr))
  refine ⟨hf0, hF0, hFc, he, hb, fun j hj ↦ ?_, ?_⟩
  · rw [fourier_dampedStage_prod T (f (-n)) _ (fun q hq ↦ (hT q hq).pos) hi, hempty]
    rw [mul_div_cancel_left₀ _ (prime_mesh_euler_prod_ne_zero T hp hpT hT hj)]
  · let C : ℂ := ∏ q ∈ T, -(2 * (Real.pi : ℂ) * Complex.I * Real.log q)
    have hC : C ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro q hq
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
        (Complex.ofReal_ne_zero.mpr (Real.log_pos (show (1 : ℝ) < q by exact_mod_cast (hT q hq).one_lt)).ne'))
    have ht := (tendsto_fourier_dampedStage_leading T (f (-n)) hT hi).div_const C
    have hz : 𝓕 (dampedStage ∅ (f (-n))) 0 = if n = 0 then 1 else 0 := by
      simpa only [Int.cast_zero, zero_div, eq_comm] using hempty 0
    rw [hz, mul_div_cancel_left₀ _ hC] at ht
    convert ht using 1
    ext ξ
    dsimp only [C]
    ring

end RiemannMasullo.RationalPacket
