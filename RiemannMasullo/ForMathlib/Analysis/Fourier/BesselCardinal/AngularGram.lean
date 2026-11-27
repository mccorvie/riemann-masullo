module

public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.FiniteGramCardinal
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Weighted real-line evaluation waves and their finite Gram matrices in angular Fourier coordinates. -/

@[expose] public noncomputable section

open Filter MeasureTheory RCLike
open scoped InnerProductSpace Matrix NNReal ENNReal ComplexOrder

namespace RiemannMasullo.WeakCardinal

/-- The positive normalization used by the angular-frequency Fourier transform. -/
def angularFactor : ℝ≥0 := ⟨(2 * Real.pi)⁻¹, by positivity⟩

/-- Angular-frequency integration is Lebesgue integration divided by `2π`. -/
def angularMeasure : Measure ℝ := angularFactor • (volume : Measure ℝ)

/-- The width-zero density in the physical log-norm variable. -/
def weight (r x : ℝ) : ℝ := (1+x^2)^r

private theorem weight_pos (r x : ℝ) : 0 < weight r x := Real.rpow_pos_of_pos (by positivity) _
private theorem continuous_weight (r : ℝ) : Continuous (weight r) := by
  exact (show Continuous (fun x : ℝ ↦ 1+x^2) by fun_prop).rpow_const (fun x ↦ .inl (by dsimp; positivity))

private theorem weight_add (a b x : ℝ) : weight (a+b) x = weight a x * weight b x :=
  Real.rpow_add (by positivity) _ _

private theorem weight_product (t r x : ℝ) :
    weight t x * weight (-r) x * weight (-r) x = weight (-(2*r-t)) x := by
  rw [← weight_add, ← weight_add]
  congr 1
  ring

/-- The order-`r` real-line Hilbert measure uses the density `(1+x²)^r`. -/
def sobolevMeasure (r : ℝ) : Measure ℝ :=
  angularMeasure.withDensity fun x ↦ ENNReal.ofReal (weight r x)

private theorem integral_sobolevMeasure (t : ℝ) (f : ℝ → ℂ) :
    (∫ x, f x ∂sobolevMeasure t) = ∫ x, (weight t x : ℂ) * f x ∂angularMeasure := by
  rw [sobolevMeasure, integral_withDensity_eq_integral_toReal_smul
    ((continuous_weight t).measurable.ennreal_ofReal) (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae (.of_forall fun x ↦ ?_)
  rw [ENNReal.toReal_ofReal (weight_pos _ _).le, Complex.real_smul]

/-- On the unscaled real line the reciprocal Sobolev weight is integrable above one half. -/
theorem integrable_weight_neg_volume {d : ℝ} (hd : 1/2 < d) : Integrable (weight (-d)) volume := by
  have hi := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2*d) (by
    simp only [Module.finrank_self, Nat.cast_one]
    linarith)
  exact hi.congr (.of_forall fun x ↦ by
    simp only [weight, Real.norm_eq_abs, sq_abs]
    rw [show -(2*d)/2 = -d by ring])

private theorem integrable_invWeight {d : ℝ} (hd : 1/2 < d) : Integrable (weight (-d)) angularMeasure :=
  (integrable_weight_neg_volume hd).smul_measure_nnreal (c := angularFactor)

/-- The angular-frequency phase of a physical translation. -/
def phase (w x : ℝ) : ℂ := (Circle.exp (w*x) : ℂ)

private theorem continuous_phase (w : ℝ) : Continuous (phase w) :=
  continuous_subtype_val.comp (Circle.exp.continuous.comp (continuous_const.mul continuous_id))

/-- The frequency representative of evaluation at `w`, with negative phase and the
reciprocal of the strong Sobolev density. -/
def evaluationWave (r w x : ℝ) : ℂ := (weight (-r) x : ℂ) * phase (-w) x

theorem evaluationWave_eq_exp_div (r w x : ℝ) :
    evaluationWave r w x = Complex.exp ((-w*x : ℝ) * Complex.I) / ((1+x^2)^r : ℝ) := by
  rw [evaluationWave, phase, Circle.coe_exp]
  simp only [weight, Real.rpow_neg (by positivity : (0:ℝ) ≤ 1+x^2), Complex.ofReal_inv, div_eq_mul_inv]
  ring

private theorem continuous_wave (r w : ℝ) : Continuous (evaluationWave r w) :=
  (Complex.continuous_ofReal.comp (continuous_weight _)).mul (continuous_phase _)

private theorem norm_wave (r w x : ℝ) : ‖evaluationWave r w x‖ = weight (-r) x := by
  simp only [evaluationWave, phase, norm_mul, Complex.norm_of_nonneg (weight_pos _ _).le,
    Circle.norm_coe, mul_one]

/-- A strong evaluation representer belongs to every weighted `L²` for which its
resulting reciprocal density has exponent strictly greater than `1/2`. -/
theorem memLp_evaluationWave {r t : ℝ} (h : 1/2 < 2*r-t) (w : ℝ) :
    MemLp (evaluationWave r w) 2 (sobolevMeasure t) := by
  rw [memLp_two_iff_integrable_sq_norm (continuous_wave _ _).aestronglyMeasurable,
    sobolevMeasure, integrable_withDensity_iff ((continuous_weight t).measurable.ennreal_ofReal)
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  exact (integrable_invWeight h).congr (.of_forall fun x ↦ by
    dsimp only
    rw [ENNReal.toReal_ofReal (weight_pos _ _).le, norm_wave, ← weight_product t r x]
    ring)

/-- The continuous evaluation wave bundled in the actual weighted Hilbert space of order `t`. -/
def evaluationVectorAt (r t : ℝ) (h : 1/2 < 2*r-t) (w : ℝ) : Lp ℂ 2 (sobolevMeasure t) :=
  (memLp_evaluationWave h w).toLp (evaluationWave r w)

theorem evaluationVectorAt_coeFn (r t : ℝ) (h : 1/2 < 2*r-t) (w : ℝ) :
    (evaluationVectorAt r t h w : ℝ → ℂ) =ᵐ[sobolevMeasure t] evaluationWave r w :=
  (memLp_evaluationWave h w).coeFn_toLp

/-- The strong Riesz evaluation vector at the specified ordinate. -/
def evaluationVector (r : ℝ) (hr : 1/2 < r) (w : ℝ) : Lp ℂ 2 (sobolevMeasure r) :=
  evaluationVectorAt r r (by linarith) w

/-- The finite Gram entries are the angular Fourier transform of the indicated reciprocal density. -/
def gramMatrix {ι : Type*} (d : ℝ) (site : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.of fun i j ↦ ∫ x : ℝ, (weight (-d) x : ℂ) * phase (site i-site j) x ∂angularMeasure

private theorem inner_phase (u v x : ℝ) : ⟪phase (-u) x, phase (-v) x⟫_ℂ = phase (u-v) x := by
  rw [RCLike.inner_apply, phase, phase, phase, starRingEnd_apply, Complex.star_def, ← Circle.coe_inv_eq_conj]
  rw [show (u-v)*x = (-v)*x-(-u)*x by ring, Circle.exp_sub, div_eq_mul_inv, Circle.coe_mul]

private theorem weighted_inner_wave (t r u v x : ℝ) :
    (weight t x : ℂ) * ⟪evaluationWave r u x, evaluationWave r v x⟫_ℂ =
      (weight (-(2*r-t)) x : ℂ) * phase (u-v) x := by
  have he := inner_phase u v x
  rw [RCLike.inner_apply] at he
  simp only [evaluationWave, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  rw [← weight_product t r x]
  push_cast
  linear_combination ((weight t x : ℂ) * (weight (-r) x : ℂ)^2) * he

/-- Taking the inner products at order `t` gives the stronger reciprocal exponent `2r-t`.
This includes both the true strong evaluation Gram and the weak norm of the same waves. -/
theorem gram_evaluationVectorAt {ι : Type*} (r t : ℝ) (h : 1/2 < 2*r-t) (site : ι → ℝ) :
    Matrix.gram ℂ (fun i ↦ evaluationVectorAt r t h (site i)) = gramMatrix (2*r-t) site := by
  ext i j
  rw [Matrix.gram_apply, L2.inner_def]
  calc
    _ = ∫ x : ℝ, ⟪evaluationWave r (site i) x, evaluationWave r (site j) x⟫_ℂ ∂sobolevMeasure t := by
      apply integral_congr_ae
      filter_upwards [evaluationVectorAt_coeFn r t h (site i), evaluationVectorAt_coeFn r t h (site j)]
        with x hi hj
      rw [hi, hj]
    _ = _ := by
      rw [integral_sobolevMeasure]
      exact integral_congr_ae (.of_forall fun x ↦ weighted_inner_wave t r _ _ x)

/-- The positive finite form has exactly the weighted Hilbert norm of these actual evaluation waves. -/
theorem quadraticForm_eq_norm_sq {ι : Type*} [Fintype ι] (r t : ℝ) (h : 1/2 < 2*r-t)
    (site : ι → ℝ) (c : ι → ℂ) :
    (star c ⬝ᵥ (gramMatrix (2*r-t) site) *ᵥ c).re =
      ‖∑ i, c i • evaluationVectorAt r t h (site i)‖ ^ 2 := by
  rw [← gram_evaluationVectorAt r t h, Matrix.star_dotProduct_gram_mulVec]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _


/-- The explicit normalization of the angular integral in ordinary Lebesgue coordinates. -/
theorem integral_angularMeasure (f : ℝ → ℂ) :
    (∫ x, f x ∂angularMeasure) = (((2*Real.pi)⁻¹ : ℝ) : ℂ) * ∫ x, f x := by
  rw [angularMeasure, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  rfl

/-- Reflection of the physical log-norm variable reverses the difference of angular sites. -/
theorem integral_even_weight_phase (r u v : ℝ) :
    (∫ x : ℝ, (weight (-r) x : ℂ)*phase (v-u) x) =
      ∫ x : ℝ, (weight (-r) x : ℂ)*phase (u-v) x := by
  rw [← integral_neg_eq_self (fun x : ℝ ↦ (weight (-r) x : ℂ)*phase (v-u) x) volume]
  apply integral_congr_ae (.of_forall fun x ↦ ?_)
  change (weight (-r) (-x) : ℂ)*phase (v-u) (-x) = _
  rw [show weight (-r) (-x) = weight (-r) x by simp [weight], phase, phase,
    show (v-u)*(-x)=(u-v)*x by ring]

/-- The angular Gram kernel is symmetric in its two real sites at every real exponent. -/
theorem gramMatrix_apply_comm {ι : Type*} (r : ℝ) (site : ι → ℝ) (i k : ι) :
    gramMatrix r site k i = gramMatrix r site i k := by
  unfold gramMatrix
  simp only [Matrix.of_apply, integral_angularMeasure]
  rw [integral_even_weight_phase r (site i) (site k)]

/-- All real Sobolev exponents have exactly the Lebesgue null sets on this Fourier line. -/
theorem ae_sobolevMeasure_iff (t : ℝ) (p : ℝ → Prop) :
    (∀ᵐ x ∂sobolevMeasure t, p x) ↔ ∀ᵐ x ∂(volume : Measure ℝ), p x := by
  rw [sobolevMeasure, ae_withDensity_iff (continuous_weight t).measurable.ennreal_ofReal]
  have hfac : angularFactor ≠ 0 := by
    change (⟨(2*Real.pi)⁻¹, _⟩ : ℝ≥0) ≠ 0
    apply NNReal.coe_ne_zero.mp
    change (2 * Real.pi)⁻¹ ≠ 0
    positivity
  rw [angularMeasure, Measure.ae_smul_measure_iff hfac]
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact hx (ENNReal.ofReal_ne_zero_iff.mpr (weight_pos t x))
  · intro h
    filter_upwards [h] with x hx
    exact fun _ ↦ hx

private theorem star_phase_neg (w x : ℝ) : starRingEnd ℂ (phase (-w) x) = phase w x := by
  rw [starRingEnd_apply, Complex.star_def, phase, ← Circle.coe_inv_eq_conj, neg_mul, Circle.exp_neg, inv_inv]
  rfl

/-- Entries of the angular Gram kernel are real, since its two opposite phases have equal integrals. -/
theorem gramMatrix_conj_apply {ι : Type*} (r : ℝ) (site : ι → ℝ) (i k : ι) :
    starRingEnd ℂ (gramMatrix r site i k) = gramMatrix r site i k := by
  rw [← gramMatrix_apply_comm r site i k]
  change starRingEnd ℂ (∫ x : ℝ, (weight (-r) x : ℂ) * phase (site k-site i) x ∂angularMeasure) = _
  rw [← integral_conj]
  calc
    _ = gramMatrix r site i k := by
      apply integral_congr_ae (.of_forall fun x ↦ ?_)
      change starRingEnd ℂ ((weight (-r) x : ℂ) * phase (site k-site i) x) = _
      rw [map_mul, Complex.conj_ofReal, show site k-site i = -(site i-site k) by ring, star_phase_neg]
    _ = _ := (gramMatrix_apply_comm r site i k).symm

private theorem weight_mul_inv (r x : ℝ) : weight r x * weight (-r) x = 1 := by
  rw [← weight_add, add_neg_cancel]
  exact Real.rpow_zero _

private theorem weighted_inner_evaluation (r w x : ℝ) (v : ℂ) :
    (weight r x : ℂ) * ⟪evaluationWave r w x,v⟫_ℂ = phase w x * v := by
  simp only [RCLike.inner_apply, evaluationWave, map_mul, Complex.conj_ofReal, star_phase_neg]
  have h : (weight r x : ℂ) * (weight (-r) x : ℂ) = 1 := by exact_mod_cast weight_mul_inv r x
  linear_combination (phase w x * v) * h

/-- Pairing with the true evaluation vector gives the angular Fourier integral of every input
in the strong weighted Hilbert space. -/
theorem evaluationVector_inner (r : ℝ) (hr : 1/2 < r) (w : ℝ) (f : Lp ℂ 2 (sobolevMeasure r)) :
    ⟪evaluationVector r hr w, f⟫_ℂ = ∫ x, phase w x * f x ∂angularMeasure := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, ⟪evaluationWave r w x, f x⟫_ℂ ∂sobolevMeasure r := by
      apply integral_congr_ae
      filter_upwards [evaluationVectorAt_coeFn r r (by linarith) w] with x hx
      change ⟪evaluationVectorAt r r _ w x, f x⟫_ℂ = _
      rw [hx]
    _ = _ := by
      rw [integral_sobolevMeasure]
      exact integral_congr_ae (.of_forall fun x ↦ weighted_inner_evaluation r w x _)

private theorem integrable_weight_iff (r : ℝ) (g : ℝ → ℂ) :
    Integrable g (sobolevMeasure r) ↔ Integrable (fun x ↦ (weight r x : ℂ) * g x) angularMeasure := by
  rw [sobolevMeasure, integrable_withDensity_iff_integrable_smul'
    (continuous_weight r).measurable.ennreal_ofReal (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integrable_congr (.of_forall fun x ↦ ?_)
  rw [ENNReal.toReal_ofReal (weight_pos _ _).le, Complex.real_smul]

/-- The reproducing Fourier integral is absolutely integrable at every evaluation site. -/
theorem integrable_evaluation (r : ℝ) (hr : 1/2 < r) (w : ℝ) (f : Lp ℂ 2 (sobolevMeasure r)) :
    Integrable (fun x ↦ phase w x * f x) angularMeasure := by
  have h : Integrable (fun x ↦ ⟪evaluationWave r w x, f x⟫_ℂ) (sobolevMeasure r) := by
    apply (L2.integrable_inner (𝕜 := ℂ) (evaluationVector r hr w) f).congr
    filter_upwards [evaluationVectorAt_coeFn r r (by linarith) w] with x hx
    change ⟪evaluationVectorAt r r _ w x, f x⟫_ℂ = _
    rw [hx]
  exact ((integrable_weight_iff r _).mp h).congr
    (.of_forall fun x ↦ weighted_inner_evaluation r w x _)

/-- A finite Hilbert sum has exactly the advertised pointwise physical log-norm profile
almost everywhere for the same weighted measure. -/
theorem coeFn_sum_evaluationVectorAt {ι : Type*} [Fintype ι] (r t : ℝ) (h : 1/2 < 2*r-t)
    (site : ι → ℝ) (c : ι → ℂ) :
    (∑ i, c i • evaluationVectorAt r t h (site i) : Lp ℂ 2 (sobolevMeasure t)) =ᵐ[sobolevMeasure t]
      (fun x ↦ ∑ i, c i * evaluationWave r (site i) x) := by
  have hrow (i : ι) : (c i • evaluationVectorAt r t h (site i) : Lp ℂ 2 (sobolevMeasure t)) =ᵐ[sobolevMeasure t]
      fun x ↦ c i * evaluationWave r (site i) x := by
    filter_upwards [Lp.coeFn_smul (c i) (evaluationVectorAt r t h (site i)),
      evaluationVectorAt_coeFn r t h (site i)] with x h₁ h₂
    simpa only [Pi.smul_apply, h₂, smul_eq_mul] using h₁
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i ↦ c i • evaluationVectorAt r t h (site i)),
    ae_all_iff.mpr hrow] with x h₁ h₂
  simpa only [Finset.sum_apply, h₂] using h₁

/-- The squared norm of any actual weighted Hilbert vector is the weighted integral of a chosen representative. -/
theorem norm_sq_eq_weightedIntegral (t : ℝ) (f : Lp ℂ 2 (sobolevMeasure t)) (F : ℝ → ℂ)
    (hF : (f : ℝ → ℂ) =ᵐ[sobolevMeasure t] F) :
    ‖f‖^2 = ∫ x, weight t x * ‖F x‖^2 ∂angularMeasure := by
  apply Complex.ofReal_injective
  have hnorm : ((‖f‖^2 : ℝ) : ℂ) = ⟪f,f⟫_ℂ := by
    simpa only [Complex.ofReal_pow, RCLike.ofReal_eq_complex_ofReal] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f).symm
  rw [hnorm, L2.inner_def, ← integral_complex_ofReal]
  calc
    _ = ∫ x, ⟪F x, F x⟫_ℂ ∂sobolevMeasure t := integral_congr_ae (hF.mono fun x hx ↦ by rw [hx])
    _ = _ := by
      rw [integral_sobolevMeasure]
      apply integral_congr_ae (.of_forall fun x ↦ ?_)
      rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul, Complex.ofReal_pow]

/-- The exact finite Gram quadratic form is the displayed physical weighted integral, with
the `dξ/(2π)` normalization also for noninteger Sobolev exponents. -/
theorem quadraticForm_eq_weightedIntegral {ι : Type*} [Fintype ι] (r t : ℝ) (h : 1/2 < 2*r-t)
    (site : ι → ℝ) (c : ι → ℂ) :
    (star c ⬝ᵥ (gramMatrix (2*r-t) site) *ᵥ c).re =
      ∫ x, weight t x * ‖∑ i, c i * evaluationWave r (site i) x‖^2 ∂angularMeasure :=
  (quadraticForm_eq_norm_sq r t h site c).trans
    (norm_sq_eq_weightedIntegral t _ _ (coeFn_sum_evaluationVectorAt r t h site c))

private def phaseHom (w : ℝ) : Multiplicative ℝ →* ℂ where
  toFun t := phase (-w) t.toAdd
  map_one' := by simp [phase]
  map_mul' a b := by
    change (Circle.exp ((-w)*(a.toAdd+b.toAdd)) : ℂ) = _ * _
    rw [mul_add, Circle.exp_add, Circle.coe_mul]
    rfl

private theorem phaseHom_injective : Function.Injective phaseHom := by
  intro a b hab
  by_contra hn
  let t := Real.pi/(b-a)
  have he : (Circle.exp ((-a)*t) : ℂ) = (Circle.exp ((-b)*t) : ℂ) :=
    congrArg (fun f : Multiplicative ℝ →* ℂ ↦ f (Multiplicative.ofAdd t)) hab
  have hz : Circle.exp ((b-a)*t) = 1 := by
    apply Subtype.ext
    rw [show (b-a)*t=(-a)*t-(-b)*t by ring, Circle.exp_sub, Circle.coe_div, Circle.coe_one,
      he, div_self (Circle.coe_ne_zero _)]
  have hπ : (b-a)*t = Real.pi := by dsimp only [t]; field_simp [sub_ne_zero.mpr (Ne.symm hn)]
  exact Circle.exp_pi_ne_one (hπ ▸ hz)

private theorem continuous_wave_sum {ι : Type*} [Fintype ι] (r : ℝ) (site : ι → ℝ) (c : ι → ℂ) :
    Continuous (fun x ↦ ∑ i, c i * evaluationWave r (site i) x) :=
  continuous_finsetSum _ (fun i _ ↦ continuous_const.mul (continuous_wave r (site i)))

/-- Distinct real sites give genuinely independent evaluation vectors in every admissible
weighted Hilbert space. Positivity of the density lets continuity recover pointwise equality. -/
theorem linearIndependent_evaluationVectorAt {ι : Type*} [Fintype ι] (r t : ℝ)
    (h : 1/2 < 2*r-t) {site : ι → ℝ} (hs : Function.Injective site) :
    LinearIndependent ℂ (fun i ↦ evaluationVectorAt r t h (site i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have he := coeFn_sum_evaluationVectorAt r t h site c
  rw [hc] at he
  have hzero : (fun x ↦ ∑ i, c i * evaluationWave r (site i) x) =ᵐ[sobolevMeasure t] (0 : ℝ → ℂ) :=
    he.symm.trans (Lp.coeFn_zero ℂ 2 _)
  have hevery := (continuous_wave_sum r site c).ae_eq_iff_eq (μ := (volume : Measure ℝ)) (continuous_const : Continuous (0 : ℝ → ℂ))
  have hp : (fun x ↦ ∑ i, c i * evaluationWave r (site i) x) = (0 : ℝ → ℂ) :=
    hevery.mp ((ae_sobolevMeasure_iff t _).mp hzero)
  have hli := (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp
    (fun i ↦ phaseHom (site i)) (phaseHom_injective.comp hs)
  apply Fintype.linearIndependent_iff.mp hli c
  funext z
  have hh := congrFun hp z.toAdd
  change (∑ i, c i * ((weight (-r) z.toAdd : ℂ) * phase (-(site i)) z.toAdd)) = 0 at hh
  change (∑ i, c i • (phaseHom (site i) : Multiplicative ℝ → ℂ)) z = 0
  rw [Finset.sum_apply]
  have hw : (weight (-r) z.toAdd : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (weight_pos _ _).ne'
  apply (mul_eq_zero.mp ?_).resolve_left hw
  rw [Finset.mul_sum]
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  change (weight (-r) z.toAdd : ℂ) * (c i * phase (-(site i)) z.toAdd) = _
  ring

/-- The concrete Fourier integral matrix is strictly positive definite on distinct sites. -/
theorem gramMatrix_posDef {ι : Type*} [Fintype ι] (r : ℝ) (hr : 1/2 < r) {site : ι → ℝ}
    (hs : Function.Injective site) : (gramMatrix r site).PosDef := by
  have h : 1/2 < 2*r-r := by linarith
  have hg := gram_evaluationVectorAt r r h site
  rw [show 2*r-r=r by ring] at hg
  rw [← hg]
  exact Matrix.posDef_gram_of_linearIndependent (linearIndependent_evaluationVectorAt r r h hs)

/-- In particular the actual finite Gram system is invertible for a finite set of distinct ordinates. -/
theorem gramMatrix_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ)
    (hr : 1/2 < r) {site : ι → ℝ} (hs : Function.Injective site) :
    (gramMatrix r site).det ≠ 0 :=
  (gramMatrix_posDef r hr hs).posSemidef.posDef_iff_det_ne_zero.mp (gramMatrix_posDef r hr hs)

/-- The strong evaluation vectors have the inverse-`r` Fourier Gram, with no change of exponent. -/
theorem gram_evaluationVector {ι : Type*} (r : ℝ) (hr : 1/2 < r) (site : ι → ℝ) :
    Matrix.gram ℂ (fun i ↦ evaluationVector r hr (site i)) = gramMatrix r site := by
  simpa only [evaluationVector, two_mul, add_sub_cancel_right] using
    gram_evaluationVectorAt r r (by linarith) site

/-- The literal inverse column solves the finite trace-data problem at distinct real sites. -/
theorem gramMatrix_mulVec_inverse_column {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ)
    (hr : 1/2 < r) {site : ι → ℝ} (hs : Function.Injective site) (i j : ι) :
    ((gramMatrix r site) *ᵥ (fun k ↦ (gramMatrix r site)⁻¹ k j)) i =
      if site i = site j then 1 else 0 := by
  have he := congrArg (fun M : Matrix ι ι ℂ ↦ M i j)
    ((gramMatrix r site).mul_nonsing_inv (isUnit_iff_ne_zero.mpr (gramMatrix_det_ne_zero r hr hs)))
  simpa only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.one_apply, hs.eq_iff] using he

/-- The vector from the inverse column has the specified pointwise Fourier values at all the sites. -/
theorem integral_finiteGramCardinal {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ)
    (hr : 1/2 < r) {site : ι → ℝ} (hs : Function.Injective site) (i j : ι) :
    (∫ x, phase (site i) x *
      (finiteGramCardinal (H := Lp ℂ 2 (sobolevMeasure r)) (fun k ↦ evaluationVector r hr (site k)) j : ℝ → ℂ) x ∂angularMeasure) =
        if i = j then 1 else 0 := by
  rw [← evaluationVector_inner r hr]
  exact inner_finiteGramCardinal _ (linearIndependent_evaluationVectorAt r r (by linarith) hs) i j

/-- The very same inverse column and continuous frequency functions, now regarded at weak order `r-1`. -/
def weakGramCardinal {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ) (hr : 1/2 < r)
    (site : ι → ℝ) (w : ι) : Lp ℂ 2 (sobolevMeasure (r-1)) :=
  ∑ i, (gramMatrix r site)⁻¹ i w • evaluationVectorAt r (r-1) (by linarith) (site i)

/-- Weakening the finite cardinal preserves its Lebesgue representative exactly. -/
theorem weakGramCardinal_ae_finiteGramCardinal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (hr : 1/2 < r) (site : ι → ℝ) (w : ι) :
    (weakGramCardinal r hr site w : ℝ → ℂ) =ᵐ[volume]
      (finiteGramCardinal (H := Lp ℂ 2 (sobolevMeasure r)) (fun k ↦ evaluationVector r hr (site k)) w : ℝ → ℂ) := by
  let c (i : ι) := (gramMatrix r site)⁻¹ i w
  have hw := (ae_sobolevMeasure_iff (r-1) _).mp (coeFn_sum_evaluationVectorAt r (r-1) (by linarith) site c)
  have hs := (ae_sobolevMeasure_iff r _).mp (coeFn_sum_evaluationVectorAt r r (by linarith) site c)
  rw [finiteGramCardinal, gram_evaluationVector r hr site]
  filter_upwards [hw, hs] with x hx hy
  exact hx.trans hy.symm

/-- In particular the exact weak norm of the inverse-column cardinal is the positive
quadratic form with the second Gram exponent `r+1`. -/
theorem weakGramCardinal_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ) (hr : 1/2 < r)
    (site : ι → ℝ) (w : ι) :
    let c (i : ι) := (gramMatrix r site)⁻¹ i w
    ‖weakGramCardinal r hr site w‖^2 = (star c ⬝ᵥ (gramMatrix (r+1) site) *ᵥ c).re := by
  let c (i : ι) := (gramMatrix r site)⁻¹ i w
  have h := quadraticForm_eq_norm_sq r (r-1) (by linarith) site c
  exact h.symm.trans (congrArg (fun d : ℝ ↦ (star c ⬝ᵥ (gramMatrix d site) *ᵥ c).re)
    (by ring : 2*r-(r-1)=r+1))

end RiemannMasullo.WeakCardinal
