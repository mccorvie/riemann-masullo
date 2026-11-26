module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.FractionalEnergy
public import RiemannMasullo.ForMathlib.Analysis.Fourier.FractionalEmbedding

/-! # Fractional Fourier and jump pairings

The positive jump form has exactly the weighted Fourier norm and pairing on its full
finite-energy domain. Null-set changes of a representative do not affect either endpoint
of a translation jump. Polarization then identifies the bilinear forms.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Real
open scoped FourierTransform
namespace RiemannMasullo

private theorem lintegral_sq_norm_eq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ) = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The Fourier half-weight is square-integrable exactly when the jump differences are. -/
theorem memLp_fractionalWeight_iff_memLp_jump {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) {f : ℝ → ℂ} (hm : Measurable f) (hf : MemLp f 2) :
    MemLp (fun ξ : ℝ ↦ ((1 + (2 * Real.pi * ξ) ^ 2) ^ (θ / 2) : ℝ) •
      (𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) ξ) 2 ↔
    MemLp (fun p : ℝ × ℝ ↦ f p.1 - f p.2) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ)) := by
  let F : ℝ → ℂ := (𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝ))
  have hF : Measurable F := (Lp.stronglyMeasurable (𝓕 (hf.toLp f))).measurable
  rw [memLp_fractionalWeight_iff_integrable hF,
    ← lintegral_ofReal_ne_top_iff_integrable (by apply Measurable.aestronglyMeasurable; fun_prop)
      (.of_forall fun ξ ↦ mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))]
  rw [← lt_top_iff_ne_top]
  have hi (ξ : ℝ) : ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ θ * ‖F ξ‖ ^ 2) =
      ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ θ) * ‖F ξ‖ₑ ^ 2 := by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp_rw [hi]
  change (∫⁻ ξ : ℝ, ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ θ) *
    ‖(𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) ξ‖ₑ ^ 2) < ⊤ ↔ _
  rw [fractionalSobolev_energy_lt_top_iff_memLp_jump hθ₀ hθ₁]
  apply memLp_congr_ae
  have he := ae_eq_realJumpPair_endpoints (fractionalJumpMeasure θ)
    (Lp.stronglyMeasurable (hf.toLp f)).measurable hm hf.coeFn_toLp
  filter_upwards [he] with p hp
  rw [hp.1, hp.2]

/-- The ordinary finite jump energy equals the Fourier-defined fractional energy for
any measurable representative, with no physical-space `L¹` assumption. -/
theorem nonlocalEnergy_eq_fractionalFourierEnergy {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) {f : ℝ → ℂ} (hm : Measurable f) (hf : MemLp f 2)
    (hJ : MemLp (fun p : ℝ × ℝ ↦ f p.1 - f p.2) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ))) :
    nonlocalEnergy volume (realJumpPairMeasure (fractionalJumpMeasure θ)) f =
      ∫ ξ : ℝ, (1 + (2 * Real.pi * ξ) ^ 2) ^ θ *
        ‖(𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) ξ‖ ^ 2 := by
  let ν := realJumpPairMeasure (fractionalJumpMeasure θ)
  have he := lintegral_fractionalSobolev_energy_L2 hθ₀ hθ₁ (hf.toLp f)
  have hl : (∫⁻ x, ‖(hf.toLp f) x‖ₑ ^ 2) = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
    apply lintegral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  have hj : (∫⁻ r : ℝ, ∫⁻ x : ℝ, ‖(hf.toLp f) (x + r) - (hf.toLp f) x‖ₑ ^ 2
      ∂volume ∂fractionalJumpMeasure θ) = ∫⁻ p : ℝ × ℝ, ‖f p.1 - f p.2‖ₑ ^ 2 ∂ν := by
    rw [← lintegral_realJumpPairMeasure _
      (fun p : ℝ × ℝ ↦ ‖(hf.toLp f) p.1 - (hf.toLp f) p.2‖ₑ ^ 2) (by fun_prop)]
    apply lintegral_congr_ae
    have hae := ae_eq_realJumpPair_endpoints (fractionalJumpMeasure θ)
      (Lp.stronglyMeasurable (hf.toLp f)).measurable hm hf.coeFn_toLp
    filter_upwards [hae] with p hp
    rw [hp.1, hp.2]
  rw [hl, hj] at he
  have hln : (∫⁻ x, ‖f x‖ₑ ^ 2) ≠ ⊤ := by
    have ht := (eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero
      ENNReal.ofNat_ne_top hf.aestronglyMeasurable).mp hf.eLpNorm_lt_top
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using ht.ne
  have hjn : (∫⁻ p : ℝ × ℝ, ‖f p.1 - f p.2‖ₑ ^ 2 ∂ν) ≠ ⊤ := by
    have ht := (eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero
      ENNReal.ofNat_ne_top hJ.aestronglyMeasurable).mp hJ.eLpNorm_lt_top
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using ht.ne
  have hreal := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add hln (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hjn),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hreal
  have hFm : Measurable ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    (Lp.stronglyMeasurable (𝓕 (hf.toLp f))).measurable
  unfold nonlocalEnergy
  rw [integral_eq_lintegral_of_nonneg_ae (.of_forall fun _ ↦ sq_nonneg _)
      (by fun_prop), lintegral_sq_norm_eq,
    integral_eq_lintegral_of_nonneg_ae (.of_forall fun _ ↦ sq_nonneg _)
      (by fun_prop), lintegral_sq_norm_eq,
    integral_eq_lintegral_of_nonneg_ae
      (.of_forall fun ξ ↦ mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
      (by fun_prop)]
  convert hreal using 1
  congr 1
  apply lintegral_congr
  intro ξ
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

private theorem integral_norm_add_sq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, ‖f x + g x‖ ^ 2 ∂μ) = (∫ x, ‖f x‖ ^ 2 ∂μ) +
      (∫ x, ‖g x‖ ^ 2 ∂μ) + 2 * ∫ x, (star (f x) * g x).re ∂μ := by
  have hfi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hgi := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hci : Integrable (fun x ↦ (star (f x) * g x).re) μ := by
    simpa only [Pi.mul_def, Pi.star_apply, RCLike.re_to_complex] using
      (hf.star.integrable_mul hg).re
  have he (x : X) : ‖f x + g x‖ ^ 2 =
      ‖f x‖ ^ 2 + ‖g x‖ ^ 2 + 2 * (star (f x) * g x).re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  simp_rw [he]
  have hsum : Integrable (fun x ↦ ‖f x‖ ^ 2 + ‖g x‖ ^ 2) μ := by
    simpa only [Pi.add_def] using hfi.add hgi
  rw [integral_add hsum (hci.const_mul 2), integral_add hfi hgi, integral_const_mul]

private theorem norm_fractionalHalfWeight_sq (θ ξ : ℝ) (u : ℂ) :
    ‖((1 + (2 * Real.pi * ξ) ^ 2) ^ (θ / 2) : ℝ) • u‖ ^ 2 =
      (1 + (2 * Real.pi * ξ) ^ 2) ^ θ * ‖u‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _),
    mul_pow, ← Real.rpow_mul_natCast (by positivity)]
  congr 2
  ring

/-- Polarization identifies the real part of the jump pairing with the weighted Fourier
pairing. Both functions may be arbitrary measurable finite-energy representatives. -/
theorem nonlocalPairing_re_eq_fractionalFourierPairing_re {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) {f g : ℝ → ℂ}
    (fm : Measurable f) (gm : Measurable g) (hf : MemLp f 2) (hg : MemLp g 2)
    (fJ : MemLp (fun p : ℝ × ℝ ↦ f p.1 - f p.2) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ)))
    (gJ : MemLp (fun p : ℝ × ℝ ↦ g p.1 - g p.2) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ))) :
    (∫ x : ℝ, (star (f x) * g x).re) + (1 / 2 : ℝ) *
      (∫ p : ℝ × ℝ, (star (f p.1 - f p.2) * (g p.1 - g p.2)).re
        ∂realJumpPairMeasure (fractionalJumpMeasure θ)) =
    ∫ ξ : ℝ, (1 + (2 * Real.pi * ξ) ^ 2) ^ θ *
      (star ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) ξ) *
        (𝓕 (hg.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) ξ).re := by
  let ν := realJumpPairMeasure (fractionalJumpMeasure θ)
  let w (ξ : ℝ) := (1 + (2 * Real.pi * ξ) ^ 2) ^ (θ / 2)
  let F : ℝ → ℂ := (𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝ))
  let G : ℝ → ℂ := (𝓕 (hg.toLp g) : Lp ℂ 2 (volume : Measure ℝ))
  have hF : MemLp (fun ξ ↦ w ξ • F ξ) 2 :=
    (memLp_fractionalWeight_iff_memLp_jump hθ₀ hθ₁ fm hf).mpr fJ
  have hG : MemLp (fun ξ ↦ w ξ • G ξ) 2 :=
    (memLp_fractionalWeight_iff_memLp_jump hθ₀ hθ₁ gm hg).mpr gJ
  have hfg : MemLp (fun x ↦ f x + g x) 2 := hf.add hg
  have hfgJ : MemLp (fun p : ℝ × ℝ ↦ (f p.1 + g p.1) - (f p.2 + g p.2)) 2 ν := by
    apply (fJ.add gJ).ae_eq
    exact .of_forall fun p ↦ by dsimp; ring
  have he := nonlocalEnergy_eq_fractionalFourierEnergy hθ₀ hθ₁
    (fm.add gm) hfg hfgJ
  have hFadd : ((𝓕 (hfg.toLp (fun x ↦ f x + g x)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] fun ξ ↦ F ξ + G ξ := by
    rw [show hfg.toLp (fun x ↦ f x + g x) = hf.toLp f + hg.toLp g from rfl,
      FourierTransform.fourier_add]
    exact Lp.coeFn_add _ _
  have hphysical : nonlocalEnergy volume ν (fun x ↦ f x + g x) =
      nonlocalEnergy volume ν f + nonlocalEnergy volume ν g +
        2 * ((∫ x : ℝ, (star (f x) * g x).re) + (1 / 2 : ℝ) *
          ∫ p : ℝ × ℝ, (star (f p.1 - f p.2) * (g p.1 - g p.2)).re ∂ν) := by
    have hdiff (p : ℝ × ℝ) : (f p.1 + g p.1) - (f p.2 + g p.2) =
        (f p.1 - f p.2) + (g p.1 - g p.2) := by ring
    unfold nonlocalEnergy
    simp_rw [hdiff]
    rw [integral_norm_add_sq volume hf hg, integral_norm_add_sq ν fJ gJ]
    ring
  have hfourier : (∫ ξ : ℝ, (1 + (2 * Real.pi * ξ) ^ 2) ^ θ *
      ‖(𝓕 (hfg.toLp (fun x ↦ f x + g x)) : Lp ℂ 2 (volume : Measure ℝ)) ξ‖ ^ 2) =
      (∫ ξ : ℝ, (1 + (2 * Real.pi * ξ) ^ 2) ^ θ * ‖F ξ‖ ^ 2) +
      (∫ ξ : ℝ, (1 + (2 * Real.pi * ξ) ^ 2) ^ θ * ‖G ξ‖ ^ 2) +
      2 * ∫ ξ : ℝ, (1 + (2 * Real.pi * ξ) ^ 2) ^ θ * (star (F ξ) * G ξ).re := by
    calc
      _ = ∫ ξ : ℝ, ‖w ξ • F ξ + w ξ • G ξ‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hFadd] with ξ hξ
        rw [hξ, ← smul_add, norm_fractionalHalfWeight_sq]
      _ = _ := by
        rw [integral_norm_add_sq volume hF hG]
        dsimp only [w]
        simp_rw [norm_fractionalHalfWeight_sq]
        congr 2
        apply integral_congr_ae
        exact .of_forall fun ξ ↦ by
          have hw : ((1 + (2 * Real.pi * ξ) ^ 2) ^ (θ / 2)) ^ 2 =
              (1 + (2 * Real.pi * ξ) ^ 2) ^ θ := by
            rw [← Real.rpow_mul_natCast (by positivity)]
            congr 1
            ring
          have heq (a : ℝ) (u v : ℂ) : (star (a • u) * (a • v)).re =
              a ^ 2 * (star u * v).re := by
            simp only [Complex.real_smul, Complex.star_def, Complex.mul_re, Complex.mul_im,
              Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
            ring
          dsimp only
          rw [heq, hw]
  simp only [Pi.add_def] at he
  rw [hphysical, hfourier,
    nonlocalEnergy_eq_fractionalFourierEnergy hθ₀ hθ₁ fm hf fJ,
    nonlocalEnergy_eq_fractionalFourierEnergy hθ₀ hθ₁ gm hg gJ] at he
  linarith

/-- The real jump pairing is the real part of the fractional Fourier pairing. -/
theorem realNonlocalPairing_eq_fractionalFourierPairing_re {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) {f g : ℝ → ℝ}
    (fm : Measurable f) (gm : Measurable g) (hf : MemLp f 2) (hg : MemLp g 2)
    (fJ : MemLp (fun p : ℝ × ℝ ↦ f p.1 - f p.2) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ)))
    (gJ : MemLp (fun p : ℝ × ℝ ↦ g p.1 - g p.2) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ))) :
    realNonlocalPairing volume (realJumpPairMeasure (fractionalJumpMeasure θ)) f g =
    ∫ ξ : ℝ, (1 + (2 * Real.pi * ξ) ^ 2) ^ θ *
      (star ((𝓕 (hf.ofReal.toLp (fun x ↦ (f x : ℂ))) : Lp ℂ 2 (volume : Measure ℝ)) ξ) *
        (𝓕 (hg.ofReal.toLp (fun x ↦ (g x : ℂ))) : Lp ℂ 2 (volume : Measure ℝ)) ξ).re := by
  have fJc : MemLp (fun p : ℝ × ℝ ↦ (f p.1 : ℂ) - (f p.2 : ℂ)) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ)) := by
    apply (fJ.ofReal (K := ℂ)).ae_eq
    exact .of_forall fun p ↦ by dsimp only; exact RCLike.ofReal_sub _ _
  have gJc : MemLp (fun p : ℝ × ℝ ↦ (g p.1 : ℂ) - (g p.2 : ℂ)) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ)) := by
    apply (gJ.ofReal (K := ℂ)).ae_eq
    exact .of_forall fun p ↦ by dsimp only; exact RCLike.ofReal_sub _ _
  have he := nonlocalPairing_re_eq_fractionalFourierPairing_re hθ₀ hθ₁
    (f := fun x ↦ (f x : ℂ)) (g := fun x ↦ (g x : ℂ))
    (by fun_prop) (by fun_prop) hf.ofReal hg.ofReal fJc gJc
  simpa only [realNonlocalPairing, ← Complex.ofReal_sub, Complex.star_def,
    Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re] using he

end RiemannMasullo
