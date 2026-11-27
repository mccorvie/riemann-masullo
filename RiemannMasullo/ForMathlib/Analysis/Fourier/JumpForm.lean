module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Prod

/-! # Fourier representation of translation jump forms -/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

namespace RiemannMasullo

private theorem schwartz_integrable_norm_sq (f : 𝓢(ℝ, ℂ)) :
    Integrable (fun x ↦ ‖f x‖ ^ 2) := by
  simpa using (f.memLp (2 : ℝ≥0∞) volume).integrable_norm_rpow
    (by norm_num) (by simp)

private theorem schwartz_fourier_compSubConst (f : 𝓢(ℝ, ℂ)) (h ξ : ℝ) :
    𝓕 (f.compSubConstCLM ℂ (-h)) ξ = (𝐞 (h * ξ) : ℂ) * 𝓕 f ξ := by
  simp only [SchwartzMap.fourier_coe]
  convert congrFun (Fourier.fourierIntegral_comp_add_right 𝐞 volume (f : ℝ → ℂ) h) ξ
    using 1 <;> simp [Real.fourier_eq, Fourier.fourierIntegral, VectorFourier.fourierIntegral,
      sub_neg_eq_add, Circle.smul_def, mul_comm ξ]

private theorem schwartz_lintegral_norm_sq_fourier (f : 𝓢(ℝ, ℂ)) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) =
      ∫⁻ ξ, ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (schwartz_integrable_norm_sq f)
      (ae_of_all _ fun _ ↦ sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal (schwartz_integrable_norm_sq (𝓕 f))
      (ae_of_all _ fun _ ↦ sq_nonneg _),
    SchwartzMap.integral_norm_sq_fourier]

/-- The squared (L^2) norm of a Schwartz translation difference is the Fourier
energy weighted by the squared character difference. -/
theorem schwartz_lintegral_sq_translate_sub (f : 𝓢(ℝ, ℂ)) (h : ℝ) :
    (∫⁻ x, ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2)) =
      ∫⁻ ξ, ENNReal.ofReal (‖(𝐞 (h * ξ) : ℂ) - 1‖ ^ 2) *
        ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2) := by
  let d := f.compSubConstCLM ℂ (-h) - f
  calc
    _ = ∫⁻ x, ENNReal.ofReal (‖d x‖ ^ 2) := by
      simp [d, sub_neg_eq_add]
    _ = ∫⁻ ξ, ENNReal.ofReal (‖𝓕 d ξ‖ ^ 2) := schwartz_lintegral_norm_sq_fourier d
    _ = _ := by
      apply lintegral_congr fun ξ ↦ ?_
      have he : 𝓕 d ξ = ((𝐞 (h * ξ) : ℂ) - 1) * 𝓕 f ξ := by
        simp [d, schwartz_fourier_compSubConst, sub_mul]
      rw [he, norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]


local notation "LineL2" => Lp ℂ 2 (volume : Measure ℝ)

private noncomputable def linePhase (h x : ℝ) : ℂ := (𝐞 (h * x) : ℂ)

private theorem linePhase_memLp (h : ℝ) (u : LineL2) :
    MemLp (fun x ↦ linePhase h x * u x) 2 volume := by
  have hc : Continuous (linePhase h) := by unfold linePhase; fun_prop
  refine (Lp.memLp u).of_le (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
    (ae_of_all _ fun x ↦ ?_)
  simp [linePhase, Circle.norm_coe]

private noncomputable def linePhaseCLM (h : ℝ) : LineL2 →L[ℂ] LineL2 := by
  let T : LineL2 →ₗ[ℂ] LineL2 :=
    { toFun := fun u ↦ (linePhase_memLp h u).toLp _
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [(linePhase_memLp h (u + v)).coeFn_toLp,
          (linePhase_memLp h u).coeFn_toLp, (linePhase_memLp h v).coeFn_toLp,
          Lp.coeFn_add u v, Lp.coeFn_add ((linePhase_memLp h u).toLp _)
            ((linePhase_memLp h v).toLp _)] with x hw hu hv huv hadd
        rw [hw, hadd, huv, Pi.add_apply, Pi.add_apply, hu, hv, mul_add]
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [(linePhase_memLp h (c • u)).coeFn_toLp,
          (linePhase_memLp h u).coeFn_toLp, Lp.coeFn_smul c u,
          Lp.coeFn_smul c ((linePhase_memLp h u).toLp _)] with x hw hu hcu hsmul
        rw [RingHom.id_apply, hw, hsmul, hcu, Pi.smul_apply, Pi.smul_apply, hu,
          smul_eq_mul, smul_eq_mul]
        ring }
  refine T.mkContinuous 1 fun u ↦ ?_
  change ‖(linePhase_memLp h u).toLp _‖ ≤ 1 * ‖u‖
  rw [one_mul, Lp.norm_toLp, Lp.norm_def u, eLpNorm_congr_norm_ae
    (linePhase_memLp h u).aestronglyMeasurable (Lp.aestronglyMeasurable u)
    (ae_of_all _ fun x ↦ by simp [linePhase, Circle.norm_coe])]

private theorem linePhaseCLM_ae (h : ℝ) (u : LineL2) :
    ⇑(linePhaseCLM h u) =ᵐ[volume] fun x ↦ linePhase h x * u x :=
  (linePhase_memLp h u).coeFn_toLp

private noncomputable def lineTranslateCLM (h : ℝ) : LineL2 →L[ℂ] LineL2 :=
  (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ _
    (measurePreserving_add_right volume h)).toContinuousLinearMap

private theorem lineTranslateCLM_ae (h : ℝ) (u : LineL2) :
    ⇑(lineTranslateCLM h u) =ᵐ[volume] fun x ↦ u (x + h) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume h)

private theorem lineTranslateCLM_schwartz (h : ℝ) (f : 𝓢(ℝ, ℂ)) :
    lineTranslateCLM h (f.toLp 2) = (f.compSubConstCLM ℂ (-h)).toLp 2 := by
  apply Lp.ext
  filter_upwards [lineTranslateCLM_ae h (f.toLp 2),
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp (f.coeFn_toLp 2),
    (f.compSubConstCLM ℂ (-h)).coeFn_toLp 2] with x hx hf hy
  rw [hx, hy, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
  exact hf

private theorem fourier_lineTranslateCLM (h : ℝ) (u : LineL2) :
    𝓕 (lineTranslateCLM h u) = linePhaseCLM h (𝓕 u) := by
  have hd := SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
    (μ := volume) (p := 2) ENNReal.ofNat_ne_top
  apply congrFun (hd.equalizer (continuous_fourier.comp (lineTranslateCLM h).continuous)
    ((linePhaseCLM h).continuous.comp continuous_fourier) ?_) u
  funext f
  change 𝓕 (lineTranslateCLM h (f.toLp 2)) = linePhaseCLM h (𝓕 (f.toLp 2))
  rw [lineTranslateCLM_schwartz, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (f.compSubConstCLM ℂ (-h))).coeFn_toLp 2,
    linePhaseCLM_ae h ((𝓕 f).toLp 2), (𝓕 f).coeFn_toLp 2] with x hx hy hz
  rw [hx, hy, hz]
  exact schwartz_fourier_compSubConst f h x

private theorem lineL2_lintegral_norm_sq (u : LineL2) :
    (∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2)) = ‖u‖ₑ ^ (2 : ℕ) := by
  rw [Lp.eNorm_def, eLpNorm_eq_eLpNorm' (by norm_num) (by simp) (Lp.aestronglyMeasurable u)]
  have hr (x : ℝ≥0∞) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := ENNReal.rpow_natCast x 2
  simpa only [ENNReal.toReal_ofNat, hr,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using
    (lintegral_rpow_eNorm_eq_rpow_eLpNorm' (μ := volume) (f := fun x ↦ u x)
      (q := 2) (by norm_num))

private theorem lineL2_lintegral_norm_sq_fourier (u : LineL2) :
    (∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2)) = ∫⁻ ξ, ENNReal.ofReal (‖(𝓕 u) ξ‖ ^ 2) := by
  rw [lineL2_lintegral_norm_sq, lineL2_lintegral_norm_sq,
    ← ofReal_norm, ← ofReal_norm, Lp.norm_fourier_eq]

/-- Plancherel for squared first differences of any logarithmic L² function. -/
theorem lineL2_lintegral_sq_translate_sub (u : Lp ℂ 2 (volume : Measure ℝ)) (h : ℝ) :
    (∫⁻ x, ENNReal.ofReal (‖u (x + h) - u x‖ ^ 2)) =
      ∫⁻ ξ, ENNReal.ofReal (‖(𝐞 (h * ξ) : ℂ) - 1‖ ^ 2) *
        ENNReal.ofReal (‖(𝓕 u) ξ‖ ^ 2) := by
  let d := lineTranslateCLM h u - u
  calc
    _ = ∫⁻ x, ENNReal.ofReal (‖d x‖ ^ 2) := by
      apply lintegral_congr_ae
      filter_upwards [lineTranslateCLM_ae h u, Lp.coeFn_sub (lineTranslateCLM h u) u] with x hx hd
      change _ = ENNReal.ofReal (‖(lineTranslateCLM h u - u) x‖ ^ 2)
      rw [hd, Pi.sub_apply, hx]
    _ = ∫⁻ ξ, ENNReal.ofReal (‖(𝓕 d) ξ‖ ^ 2) := lineL2_lintegral_norm_sq_fourier d
    _ = _ := by
      dsimp only [d]
      rw [FourierTransform.fourier_sub, fourier_lineTranslateCLM]
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_sub (linePhaseCLM h (𝓕 u)) (𝓕 u), linePhaseCLM_ae h (𝓕 u)]
        with ξ hd hphase
      rw [hd, Pi.sub_apply, hphase, ← sub_one_mul, norm_mul, mul_pow,
        ENNReal.ofReal_mul (sq_nonneg _), linePhase]

private theorem line_fractional_energy_eq_of_jump_symbol
    (f g : ℝ → ℂ) (hg : Measurable g)
    (hmass : (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) = ∫⁻ ξ, ENNReal.ofReal (‖g ξ‖ ^ 2))
    (hshift : ∀ h : ℝ,
      (∫⁻ x, ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2)) =
        ∫⁻ ξ, ENNReal.ofReal (‖(𝐞 (h * ξ) : ℂ) - 1‖ ^ 2) * ENNReal.ofReal (‖g ξ‖ ^ 2))
    (s : ℝ) (hs : 0 ≤ s) (μ : Measure ℝ) [SFinite μ]
    (hsymbol : ∀ ξ : ℝ,
      (2 : ℝ≥0∞)⁻¹ * (∫⁻ h, ENNReal.ofReal (‖(𝐞 (h * ξ) : ℂ) - 1‖ ^ 2) ∂μ) =
        ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ s - 1)) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) +
        (2 : ℝ≥0∞)⁻¹ * (∫⁻ h, (∫⁻ x, ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2)) ∂μ) =
      ∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ s) *
        ENNReal.ofReal (‖g ξ‖ ^ 2) := by
  let a (ξ : ℝ) := ENNReal.ofReal (‖g ξ‖ ^ 2)
  let b (h ξ : ℝ) := ENNReal.ofReal (‖(𝐞 (h * ξ) : ℂ) - 1‖ ^ 2)
  let w (ξ : ℝ) := (1 + (2 * Real.pi * ξ) ^ 2) ^ s
  have ha : Measurable a := ENNReal.measurable_ofReal.comp
    (hg.norm.pow_const 2)
  have hb : Measurable (Function.uncurry b) := ENNReal.measurable_ofReal.comp
    (by fun_prop : Continuous (fun z : ℝ × ℝ ↦ ‖(𝐞 (z.1 * z.2) : ℂ) - 1‖ ^ 2)).measurable
  have hj : (∫⁻ h, (∫⁻ x, ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2)) ∂μ) =
      ∫⁻ ξ, (∫⁻ h, b h ξ ∂μ) * a ξ := by
    simp_rw [hshift]
    change (∫⁻ h, (∫⁻ ξ, b h ξ * a ξ) ∂μ) = _
    rw [lintegral_lintegral_swap (f := fun h ξ ↦ b h ξ * a ξ)
      (hb.mul (ha.comp measurable_snd)).aemeasurable]
    exact lintegral_congr fun ξ ↦ lintegral_mul_const' (a ξ) (b · ξ)
      ENNReal.ofReal_ne_top
  rw [hmass, hj]
  change (∫⁻ ξ, a ξ) + (2 : ℝ≥0∞)⁻¹ * (∫⁻ ξ, (∫⁻ h, b h ξ ∂μ) * a ξ) =
    ∫⁻ ξ, ENNReal.ofReal (w ξ) * a ξ
  have hhalf (ξ : ℝ) :
      (2 : ℝ≥0∞)⁻¹ * ((∫⁻ h, b h ξ ∂μ) * a ξ) =
        ENNReal.ofReal (w ξ - 1) * a ξ := by
    rw [← mul_assoc, hsymbol ξ]
  rw [← lintegral_const_mul' _ _ (by simp)]
  simp_rw [hhalf]
  rw [← lintegral_add_left ha]
  refine lintegral_congr fun ξ ↦ ?_
  have h1 : 1 ≤ w ξ := Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg _)) hs
  rw [← one_add_mul, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (sub_nonneg.mpr h1)]
  congr 2
  ring

/-- A translation jump measure with the stated Fourier symbol gives precisely the
Schwartz fractional Sobolev energy. The measure is on displacements, and the
physical frequency corresponding to Mathlib's variable `ξ` is `2 * π * ξ`. -/
theorem schwartz_fractional_energy_eq_of_jump_symbol
    (f : 𝓢(ℝ, ℂ)) (s : ℝ) (hs : 0 ≤ s) (μ : Measure ℝ) [SFinite μ]
    (hsymbol : ∀ ξ : ℝ,
      (2 : ℝ≥0∞)⁻¹ * (∫⁻ h, ENNReal.ofReal (‖(𝐞 (h * ξ) : ℂ) - 1‖ ^ 2) ∂μ) =
        ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ s - 1)) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) +
        (2 : ℝ≥0∞)⁻¹ * (∫⁻ h, (∫⁻ x, ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2)) ∂μ) =
      ∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ s) *
        ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2) :=
  line_fractional_energy_eq_of_jump_symbol f (𝓕 f : 𝓢(ℝ, ℂ))
    (𝓕 f : 𝓢(ℝ, ℂ)).continuous.measurable (schwartz_lintegral_norm_sq_fourier f)
    (schwartz_lintegral_sq_translate_sub f) s hs μ hsymbol

/-- The exact jump form determined by the Fourier symbol, including functions in the
Sobolev completion. The equality allows either side to be infinite. -/
theorem lineL2_fractional_energy_eq_of_jump_symbol
    (f : Lp ℂ 2 (volume : Measure ℝ)) (s : ℝ) (hs : 0 ≤ s) (μ : Measure ℝ) [SFinite μ]
    (hsymbol : ∀ ξ : ℝ,
      (2 : ℝ≥0∞)⁻¹ * (∫⁻ h, ENNReal.ofReal (‖(𝐞 (h * ξ) : ℂ) - 1‖ ^ 2) ∂μ) =
        ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ s - 1)) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) +
        (2 : ℝ≥0∞)⁻¹ * (∫⁻ h, (∫⁻ x, ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2)) ∂μ) =
      ∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ s) *
        ENNReal.ofReal (‖(𝓕 f) ξ‖ ^ 2) :=
  line_fractional_energy_eq_of_jump_symbol f (𝓕 f : Lp ℂ 2 (volume : Measure ℝ))
    (Lp.stronglyMeasurable (𝓕 f : LineL2)).measurable (lineL2_lintegral_norm_sq_fourier f)
    (lineL2_lintegral_sq_translate_sub f) s hs μ hsymbol

end RiemannMasullo
