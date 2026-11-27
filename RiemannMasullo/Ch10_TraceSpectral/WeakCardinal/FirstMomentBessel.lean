module

public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.FirstMoment
public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.RadiusSixBessel
import Mathlib.Tactic

/-! The finite first-moment identity is Proposition 3 of k-ieren’s calculation on #7406.

 Attach the exact first moment to the inverse column of the normalized angular Gram matrix. -/

@[expose] public noncomputable section
open MeasureTheory Filter Set Complex Finset
open scoped InnerProductSpace ComplexConjugate ENNReal Matrix

namespace RiemannMasullo.WeakCardinal

private theorem phase_mul_phase (a b x : ℝ) : phase a x * phase b x = phase (a+b) x := by
  simp only [phase,add_mul,Circle.exp_add,Circle.coe_mul]

private theorem conj_wave_phase (a x : ℝ) : conj (CardinalMoment.wave a x) = phase (-a) x := by
  simp only [phase,Circle.coe_exp,CardinalMoment.wave,← Complex.exp_conj,map_mul,Complex.conj_ofReal,
    Complex.conj_I,neg_mul,Complex.ofReal_neg]
  ring_nf

private theorem angular_memLp_energy {r : ℝ} (U : ℝ → ℂ) (hc : Continuous U)
    (hi : Integrable (fun x ↦ CardinalMoment.symbol r x*‖U x‖^2)) :
    MemLp U 2 (sobolevMeasure r) := by
  have hmc : Continuous (weight r) := continuous_iff_continuousAt.mpr fun x ↦
    (CardinalMoment.hasDerivAt_symbol r x).continuousAt
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable,sobolevMeasure,
    integrable_withDensity_iff hmc.measurable.ennreal_ofReal (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  exact (hi.smul_measure_nnreal (c := angularFactor)).congr (.of_forall fun x ↦ by
    dsimp only
    rw [ENNReal.toReal_ofReal (show 0 ≤ weight r x from (CardinalMoment.symbol_pos r x).le)]
    exact mul_comm _ _)

private theorem angular_norm_real {r : ℝ} (f : Lp ℂ 2 (sobolevMeasure r)) (U : ℝ → ℂ)
    (hu : (f : ℝ → ℂ) =ᵐ[volume] U) :
    ‖f‖^2 = (angularFactor:ℝ)*∫ x, CardinalMoment.symbol r x*‖U x‖^2 := by
  rw [norm_sq_eq_weightedIntegral r f U ((ae_sobolevMeasure_iff _ _).mpr hu),
    angularMeasure, integral_smul_nnreal_measure, NNReal.smul_def,smul_eq_mul]
  rfl

/-- For a finite cardinal with the actual strong Gram equations, multiplication by
`x-w` on the Mellin line comes from an element of the normalized strong Hilbert
space with the sharp first-moment bound in terms of its weak image. -/
theorem exists_firstMoment_gram_exact {ι : Type*} [Fintype ι] [DecidableEq ι]
    {θ : ℝ} (hθ : 1 < θ) (site : ι → ℝ) (hinj : Function.Injective site)
    (j : ι) (c : ι → ℂ) (hsolve : gramMatrix θ site *ᵥ c = fun i ↦ if site i = site j then 1 else 0) :
    let w := site j
    let hE := ∑ i, c i • evaluationVector θ (by linarith) (site i)
    ∃ u : Lp ℂ 2 (sobolevMeasure θ),
      (∀ y : ℝ, (∫ ξ, phase y ξ*u ξ ∂angularMeasure) =
        (↑(y-w):ℂ)*(∫ ξ, phase y ξ*hE ξ ∂angularMeasure)) ∧
      ‖u‖^2 = (∫ ξ, CardinalMoment.symbolCurvature θ ξ*‖hE ξ‖^2 ∂angularMeasure)/2 ∧
      θ*‖besselWeakening θ hE‖^2 ≤ ‖u‖^2 ∧
      ‖u‖ ≤ Real.sqrt (θ*(2*θ-1))*‖besselWeakening θ hE‖ := by
  classical
  let : Nonempty ι := ⟨j⟩
  intro w hE
  let P (x : ℝ) := ∑ i, c i*evaluationWave θ (site i) x
  let H (x : ℝ) := phase w x * P x
  let g (i : ι) := -site i
  let S := Finset.univ.image g
  let b (t : ℝ) := c (Function.invFun g t)
  have hg : Function.Injective g := neg_injective.comp hinj
  have hb (i : ι) : b (g i) = c i := congrArg c (Function.leftInverse_invFun hg i)
  have hEae : (hE : ℝ → ℂ) =ᵐ[volume] P :=
    (ae_sobolevMeasure_iff θ _).mp (coeFn_sum_evaluationVectorAt θ θ (by linarith) site c)
  have hrep (x : ℝ) : CardinalMoment.symbol θ x • H x = CardinalMoment.centeredPolynomial S (-w) b x := by
    dsimp only [CardinalMoment.centeredPolynomial,S]
    rw [Finset.sum_image (fun i _ k _ h ↦ hg h)]
    simp_rw [hb]
    dsimp only [H,P]
    rw [Complex.real_smul,← mul_assoc,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hp : (CardinalMoment.symbol θ x : ℂ)*evaluationWave θ (site i) x = phase (-site i) x := by
      rw [evaluationWave_eq_exp_div,phase,Circle.coe_exp]
      change (↑(CardinalMoment.symbol θ x):ℂ)*(Complex.exp _ / (↑(CardinalMoment.symbol θ x):ℂ)) = _
      field_simp [(show (↑(CardinalMoment.symbol θ x):ℂ) ≠ 0 by exact_mod_cast (CardinalMoment.symbol_pos θ x).ne')]
    have hph : phase w x * phase (-site i) x = CardinalMoment.wave (g i - -w) x := by
      rw [phase_mul_phase,show w + -site i = g i - -w by dsimp [g]; ring]
      simp only [phase,Circle.coe_exp,CardinalMoment.wave]
    calc
      _ = c i*(phase w x*((CardinalMoment.symbol θ x:ℂ)*evaluationWave θ (site i) x)) := by ring
      _ = _ := by rw [hp,hph]
  have hdemod (y x : ℝ) : conj (CardinalMoment.wave (w-y) x)*H x = phase y x*P x := by
    dsimp only [H]
    rw [conj_wave_phase,← mul_assoc,phase_mul_phase,show -(w-y)+w=y by ring]
  have hangular (y : ℝ) : (∫ x, phase y x*hE x ∂angularMeasure) =
      ((angularFactor:ℝ):ℂ)*(∫ x, phase y x*P x) := by
    rw [integral_angularMeasure]
    congr 1
    exact integral_congr_ae (hEae.mono fun x hx ↦ congrArg ((phase y x) * ·) hx)
  have hvalues := (isMinimumCardinal_of_gram_solution θ (by linarith) site w c hsolve).values
  have hcard (z : ℝ) (hz : z ∈ S) (hz0 : z ≠ -w) :
      (∫ x, conj (CardinalMoment.wave (z- -w) x)*H x) = 0 := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    have hzw : site i ≠ w := fun h ↦ hz0 (congrArg Neg.neg h)
    have hv := hvalues (site i) (mem_range_self i)
    simp only [hzw,ite_false,evaluationVector_inner] at hv
    change (∫ x, phase (site i) x*hE x ∂angularMeasure) = 0 at hv
    rw [hangular] at hv
    have hfac : ((angularFactor:ℝ):ℂ) ≠ 0 := by
      change (↑((2*Real.pi)⁻¹):ℂ) ≠ 0
      exact_mod_cast (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
    rw [show g i - -w = w-site i by dsimp [g]; ring]
    simp_rw [hdemod]
    exact (mul_eq_zero.mp hv).resolve_left hfac
  obtain ⟨hd,hc,hiH,hiD,_,hwD,_⟩ := CardinalMoment.finite_profile_regular S (-w) θ hθ.le b H hrep
  let U (x : ℝ) := phase (-w) x*(I*deriv H x)
  have hphaseC (t : ℝ) : Continuous (phase t) := continuous_iff_continuousAt.mpr fun x ↦ by
    rw [show phase t = CardinalMoment.wave t by funext ξ; simp only [phase,Circle.coe_exp,CardinalMoment.wave]]
    exact (CardinalMoment.hasDerivAt_wave t x).continuousAt
  have hnphase (t x : ℝ) : ‖phase t x‖ = 1 := Circle.norm_coe _
  have hUn (x : ℝ) : ‖U x‖ = ‖deriv H x‖ := by simp only [U,norm_mul,hnphase,Complex.norm_I,one_mul]
  have hHn (x : ℝ) : ‖H x‖ = ‖P x‖ := by simp only [H,norm_mul,hnphase,one_mul]
  let hu := angular_memLp_energy (r := θ) U ((hphaseC _).mul (continuous_const.mul hc))
    (by simpa only [hUn] using hwD)
  let u := hu.toLp U
  have huae : (u : ℝ → ℂ) =ᵐ[volume] U := (ae_sobolevMeasure_iff θ _).mp hu.coeFn_toLp
  refine ⟨u,fun y ↦ ?_,?_⟩
  · have hmod (x : ℝ) : phase y x*U x = -(conj (CardinalMoment.wave (w-y) x)*(-I*deriv H x)) := by
      dsimp only [U]
      rw [conj_wave_phase,← mul_assoc,phase_mul_phase,show y + -w = -(w-y) by ring]
      ring
    have hval := CardinalMoment.centered_value_firstMoment H hd hiH hiD (w-y)
    simp_rw [hdemod] at hval
    rw [integral_angularMeasure,hangular]
    have hpoint : (∫ x, phase y x*u x) = -(∫ x, conj (CardinalMoment.wave (w-y) x)*(-I*deriv H x)) := by
      rw [← integral_neg]
      exact integral_congr_ae (huae.mono fun x hx ↦ (congrArg ((phase y x) * ·) hx).trans (hmod x))
    rw [hpoint,hval]
    change (↑((2*Real.pi)⁻¹):ℂ)* _ = _ * ((↑((2*Real.pi)⁻¹):ℂ)*_)
    push_cast
    ring
  · have hwAE : (besselWeakening θ hE : ℝ → ℂ) =ᵐ[volume] P :=
      by
        have hw0 : (besselWeakening θ hE : ℝ → ℂ) =ᵐ[volume] hE :=
          (ae_sobolevMeasure_iff (θ-1) _).mp (besselWeakening_coeFn θ hE)
        exact hw0.trans hEae
    have huc := angular_norm_real u U huae
    simp only [hUn] at huc
    have hvc := angular_norm_real (besselWeakening θ hE) P hwAE
    simp_rw [← hHn] at hvc
    obtain ⟨hexact,hlo,hhi⟩ := CardinalMoment.finite_cardinal_firstMoment S (-w) θ hθ.le b H hrep hcard
    have hcurv : (∫ ξ, CardinalMoment.symbolCurvature θ ξ*‖hE ξ‖^2 ∂angularMeasure) =
        (angularFactor:ℝ)*(∫ ξ, CardinalMoment.symbolCurvature θ ξ*‖H ξ‖^2) := by
      rw [angularMeasure,integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul]
      congr 1
      exact integral_congr_ae (hEae.mono fun x hx ↦ by dsimp only; rw [hx,hHn])
    refine ⟨?_,?_,?_⟩
    · rw [huc,hcurv,hexact]
      ring
    · rw [huc,hvc]
      nlinarith only [mul_le_mul_of_nonneg_left hlo angularFactor.coe_nonneg]
    · apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      rw [mul_pow,Real.sq_sqrt (mul_nonneg (by linarith) (by linarith)),huc,hvc]
      calc
        _ ≤ (angularFactor:ℝ)*(θ*(2*θ-1)*(∫ x, CardinalMoment.symbol (θ-1) x*‖H x‖^2)) :=
          mul_le_mul_of_nonneg_left hhi angularFactor.coe_nonneg
        _ = _ := by ring

/-- The sharp upper estimate extracted from the exact normalized moment identity. -/
theorem exists_firstMoment_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    {θ : ℝ} (hθ : 1 < θ) (site : ι → ℝ) (hinj : Function.Injective site)
    (j : ι) (c : ι → ℂ) (hsolve : gramMatrix θ site *ᵥ c = fun i ↦ if site i = site j then 1 else 0) :
    let w := site j
    let hE := ∑ i, c i • evaluationVector θ (by linarith) (site i)
    ∃ u : Lp ℂ 2 (sobolevMeasure θ),
      (∀ y : ℝ, (∫ ξ, phase y ξ*u ξ ∂angularMeasure) =
        (↑(y-w):ℂ)*(∫ ξ, phase y ξ*hE ξ ∂angularMeasure)) ∧
      ‖u‖ ≤ Real.sqrt (θ*(2*θ-1))*‖besselWeakening θ hE‖ := by
  intro w hE
  obtain ⟨u,hv,_,_,hu⟩ := exists_firstMoment_gram_exact hθ site hinj j c hsolve
  exact ⟨u,hv,hu⟩

/-- The normalized curvature identity, both inequalities, and the pointwise
Mellin multiplier for the computed inverse Gram column. -/
theorem exists_firstMoment_inverseGram_exact {ι : Type*} [Fintype ι] [DecidableEq ι]
    {θ : ℝ} (hθ : 1 < θ) (site : ι → ℝ) (hinj : Function.Injective site) (j : ι) :
    let w := site j
    let c (i : ι) := (gramMatrix θ site)⁻¹ i j
    let hE := ∑ i, c i • evaluationVector θ (by linarith) (site i)
    ∃ u : Lp ℂ 2 (sobolevMeasure θ),
      (∀ y : ℝ, (∫ ξ, phase y ξ*u ξ ∂angularMeasure) =
        (↑(y-w):ℂ)*(∫ ξ, phase y ξ*hE ξ ∂angularMeasure)) ∧
      ‖u‖^2 = (∫ ξ, CardinalMoment.symbolCurvature θ ξ*‖hE ξ‖^2 ∂angularMeasure)/2 ∧
      θ*‖besselWeakening θ hE‖^2 ≤ ‖u‖^2 ∧
      ‖u‖ ≤ Real.sqrt (θ*(2*θ-1))*‖besselWeakening θ hE‖ := by
  intro w c hE
  apply exists_firstMoment_gram_exact hθ site hinj j c
  funext i
  exact gramMatrix_mulVec_inverse_column θ (by linarith) hinj i j

/-- First-moment vector for the actual inverse Gram column, evaluated at every ordinate. -/
theorem exists_firstMoment_inverseGram {ι : Type*} [Fintype ι] [DecidableEq ι]
    {θ : ℝ} (hθ : 1 < θ) (site : ι → ℝ) (hinj : Function.Injective site) (j : ι) :
    let w := site j
    let c (i : ι) := (gramMatrix θ site)⁻¹ i j
    let hE := ∑ i, c i • evaluationVector θ (by linarith) (site i)
    ∃ u : Lp ℂ 2 (sobolevMeasure θ),
      (∀ y : ℝ, (∫ ξ, phase y ξ*u ξ ∂angularMeasure) =
        (↑(y-w):ℂ)*(∫ ξ, phase y ξ*hE ξ ∂angularMeasure)) ∧
      ‖u‖ ≤ Real.sqrt (θ*(2*θ-1))*‖besselWeakening θ hE‖ := by
  intro w c hE
  obtain ⟨u,hv,_,_,hu⟩ := exists_firstMoment_inverseGram_exact hθ site hinj j
  exact ⟨u,hv,hu⟩

end RiemannMasullo.WeakCardinal
