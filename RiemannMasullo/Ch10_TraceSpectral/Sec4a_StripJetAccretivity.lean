module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Numerical range of the strip-jet generator

In the order-zero adelic strip Sobolev space, the real part of the shifted generator
on a finite sum of Riesz vectors in one angular mode is bounded below by the shift
minus the strip half-width. The Riesz isometry identifies the reciprocal-space profiles
with exponential polynomials in the logarithm of the idele norm. Integration by parts
on the two half-lines gives the bound with all mixed terms included.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter
open scoped ComplexConjugate Topology

namespace RiemannMasullo

private theorem polynomial_exp_integrable {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Integrable (fun x : ℝ ↦ |x| ^ n * Real.exp (-a * |x|)) := by
  let f (x : ℝ) := |x| ^ n * Real.exp (-a * |x|)
  have hp : IntegrableOn f (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n : ℝ))
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : -1 < (n : ℝ)) one_pos ha
    simp only [Real.rpow_one, Real.rpow_natCast] at h
    refine h.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
    simp [f, abs_of_pos (mem_Ioi.mp hx)]
  have hn : IntegrableOn f (Iic 0) := by
    apply Iff.mpr integrableOn_Iic_iff_integrableOn_Iio
    have hp' : IntegrableOn f (Ioi (-(0 : ℝ))) := by simpa only [neg_zero] using hp
    have hn' := IntegrableOn.comp_neg_Iio (c := (0 : ℝ)) hp'
    simpa only [Function.comp_def, f, abs_neg] using hn'
  simpa only [Iic_union_Ioi, integrableOn_univ] using hn.union hp

private def jetMonomial (k : ℕ) (z : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ k * exp (z * x)

private def damp (α : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := Real.exp (-α * |x|) • f x

private theorem jetMonomial_damped_memLp {α : ℝ} {z : ℂ} (hz : |z.re| < α) (k : ℕ) :
    MemLp (damp α (jetMonomial k z)) 2 := by
  have hcont : Continuous (damp α (jetMonomial k z)) := by unfold damp jetMonomial; fun_prop
  apply (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr
  refine (polynomial_exp_integrable (a := 2 * (α - |z.re|)) (by linarith) (2 * k)).mono'
    (hcont.norm.pow 2).aestronglyMeasurable (.of_forall fun x ↦ ?_)
  have hest : z.re * x ≤ |z.re| * |x| := (le_abs_self (z.re * x)).trans_eq (abs_mul _ _)
  have hn : ‖damp α (jetMonomial k z) x‖ =
      |x| ^ k * Real.exp (-α * |x| + z.re * x) := by
    simp only [damp, jetMonomial, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      norm_mul, norm_pow, norm_real, norm_exp, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
      Real.exp_add]
    ring
  rw [Real.norm_of_nonneg (sq_nonneg _), hn, mul_pow, ← pow_mul, mul_comm k 2,
    ← Real.exp_nat_mul]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg _) _)
  apply Real.exp_le_exp.mpr
  push_cast
  linarith

private theorem jetMonomial_hasDerivAt (k : ℕ) (z : ℂ) (x : ℝ) :
    HasDerivAt (jetMonomial k z)
      ((k : ℂ) * jetMonomial (k - 1) z x + z * jetMonomial k z x) x := by
  have hx := (hasDerivAt_id x).ofReal_comp
  have h := (hx.pow k).mul ((hx.const_mul z).cexp)
  convert h using 1
  · rfl
  · simp [jetMonomial]; ring

/-- A finite sum of exponential monomials, with arbitrary coefficients, orders, and sites. -/
private def stripExpPolynomial {ι : Type*} (S : Finset ι) (c : ι → ℂ) (k : ι → ℕ) (z : ι → ℂ)
    (x : ℝ) : ℂ := ∑ i ∈ S, c i * (x : ℂ) ^ (k i) * exp (z i * x)

/-- The derivative lowers each positive jet order by one and retains the site. -/
private theorem hasDerivAt_stripExpPolynomial {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (k : ι → ℕ) (z : ι → ℂ) (x : ℝ) :
    HasDerivAt (stripExpPolynomial S c k z)
      (∑ i ∈ S, c i * ((k i : ℂ) * ((x : ℂ) ^ (k i - 1) * exp (z i * x)) +
        z i * ((x : ℂ) ^ (k i) * exp (z i * x)))) x := by
  convert HasDerivAt.fun_sum (u := S)
    (fun i _ ↦ (jetMonomial_hasDerivAt (k i) (z i) x).const_mul (c i)) using 1
  · funext y
    simp [stripExpPolynomial, jetMonomial, mul_assoc]
  · rfl

private theorem polynomial_memLp_and_deriv {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (k : ι → ℕ) (z : ι → ℂ) {α : ℝ} (hz : ∀ i ∈ S, |(z i).re| < α) :
    let f := stripExpPolynomial S c k z
    Differentiable ℝ f ∧ MemLp (damp α f) 2 ∧ MemLp (damp α (deriv f)) 2 := by
  let f := stripExpPolynomial S c k z
  let D (x : ℝ) := ∑ i ∈ S, c i *
    ((k i : ℂ) * jetMonomial (k i - 1) (z i) x + z i * jetMonomial (k i) (z i) x)
  have hd (x : ℝ) : HasDerivAt f (D x) x := hasDerivAt_stripExpPolynomial S c k z x
  refine ⟨fun x ↦ (hd x).differentiableAt, ?_, ?_⟩
  · have h := memLp_finsetSum S (fun i hi ↦ (jetMonomial_damped_memLp (hz i hi) (k i)).const_mul (c i))
    refine (memLp_congr_ae (.of_forall fun x ↦ ?_)).mp h
    simp [damp, stripExpPolynomial, jetMonomial, Complex.real_smul, Finset.mul_sum, mul_left_comm, mul_assoc]
  · have h := memLp_finsetSum S (fun i hi ↦
      (((jetMonomial_damped_memLp (hz i hi) (k i - 1)).const_mul (k i : ℂ)).add
       ((jetMonomial_damped_memLp (hz i hi) (k i)).const_mul (z i))).const_mul (c i))
    refine (memLp_congr_ae (.of_forall fun x ↦ ?_)).mp h
    change _ = damp α (deriv f) x
    rw [damp, (hd x).deriv]
    simp only [D, Complex.real_smul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply, damp, Complex.real_smul]
    ring

private theorem damped_product_integrable {α : ℝ} {f g : ℝ → ℂ}
    (hf : MemLp (damp α f) 2) (hg : MemLp (damp α g) 2) :
    Integrable (fun x : ℝ ↦ conj (f x) * g x * (Real.exp (-2 * α * |x|) : ℂ)) := by
  have h := hf.star.integrable_mul hg
  refine h.congr (.of_forall fun x ↦ ?_)
  change conj (damp α f x) * damp α g x = _
  have he : Real.exp (-2 * α * |x|) = Real.exp (-α * |x|) * Real.exp (-α * |x|) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [damp, he, Complex.real_smul, map_mul, conj_ofReal, ofReal_mul]
  ring

private theorem product_boundary_identity {f : ℝ → ℂ} {α : ℝ} (hf : Differentiable ℝ f)
    (hu : MemLp (damp α f) 2) (hv : MemLp (damp α (deriv f)) 2) :
    let w (x : ℝ) := Real.exp (-2 * α * |x|)
    let E (x : ℝ) := ‖f x‖ ^ 2 * w x
    let P (x : ℝ) := conj (f x) * deriv f x * (w x : ℂ)
    Integrable E ∧ Integrable P ∧
      (∫ x, P x).re = α * ((∫ x in Ioi 0, E x) - ∫ x in Iic 0, E x) := by
  intro w E P
  have heq (x : ℝ) : (conj (f x) * f x * (w x : ℂ)) = (E x : ℂ) := by
    simp only [E, ofReal_mul, ← normSq_eq_conj_mul_self, normSq_eq_norm_sq]
  have hE : Integrable E := by
    have h := (damped_product_integrable hu hu).re
    refine h.congr (.of_forall fun x ↦ ?_)
    change (conj (f x) * f x * (w x : ℂ)).re = E x
    rw [heq, ofReal_re]
  have hP : Integrable P := damped_product_integrable hu hv
  let J (x : ℝ) := (P x).re
  have hJ : Integrable J := hP.re
  let Q (a x : ℝ) := ‖f x‖ ^ 2 * Real.exp (a * x)
  let D (a x : ℝ) := (2 * (conj (f x) * deriv f x).re + a * ‖f x‖ ^ 2) * Real.exp (a * x)
  have hd (a x : ℝ) : HasDerivAt (Q a) (D a x) x := by
    have h := ((hf x).hasDerivAt.norm_sq).mul (((hasDerivAt_id x).const_mul a).exp)
    convert h using 1
    · rfl
    · dsimp [D]
      rw [mul_comm (deriv f x) (conj (f x))]
      ring
  have half (a : ℝ) (U : Set ℝ) (hm : MeasurableSet U)
      (hw : ∀ x ∈ U, Real.exp (a * x) = w x) :
      IntegrableOn (Q a) U ∧ IntegrableOn (D a) U ∧
      (∫ x in U, D a x) = 2 * (∫ x in U, J x) + a * (∫ x in U, E x) := by
    have he x (hx : x ∈ U) : Q a x = E x := by simp only [Q, E, hw x hx]
    have hd' x (hx : x ∈ U) : D a x = 2 * J x + a * E x := by
      simp only [D, J, P, E, hw x hx, Complex.re_mul_ofReal]
      ring
    have hsum := (hJ.const_mul 2).add (hE.const_mul a)
    refine ⟨hE.integrableOn.congr_fun (fun x hx ↦ (he x hx).symm) hm,
      hsum.integrableOn.congr_fun (fun x hx ↦ (hd' x hx).symm) hm, ?_⟩
    rw [setIntegral_congr_fun hm hd', integral_add (hJ.const_mul 2).integrableOn
      (hE.const_mul a).integrableOn, integral_const_mul, integral_const_mul]
  obtain ⟨hQr, hDr, hir⟩ := half (-2 * α) (Ioi 0) measurableSet_Ioi
    (fun x hx ↦ by simp [w, abs_of_pos (mem_Ioi.mp hx)])
  obtain ⟨hQl, hDl, hil⟩ := half (2 * α) (Iic 0) measurableSet_Iic
    (fun x hx ↦ by dsimp [w]; rw [abs_of_nonpos (mem_Iic.mp hx)]; congr 1; ring)
  have hr := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ ↦ hd (-2 * α) x) hDr
    (tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun x _ ↦ hd (-2 * α) x) hDr hQr)
  have hl := integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ ↦ hd (2 * α) x) hDl
    (tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (fun x _ ↦ hd (2 * α) x) hDl hQl)
  simp only [Q, mul_zero, Real.exp_zero, mul_one, sub_zero, zero_sub] at hl hr
  have htot := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hJ
  rw [compl_Iic] at htot
  have hpr : (∫ x, P x).re = ∫ x, J x := (integral_re hP).symm
  refine ⟨hE, hP, ?_⟩
  rw [hpr, ← htot]
  linarith only [hir, hr, hil, hl]

/-- The two half-line boundary terms yield the lower bound for the shifted derivative. -/
private theorem stripExpPolynomial_accretive {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (k : ι → ℕ) (z : ι → ℂ) {α : ℝ} (hα : 0 ≤ α) (hz : ∀ i ∈ S, |(z i).re| < α)
    (L : ℝ) :
    let f := stripExpPolynomial S c k z
    let w (x : ℝ) := Real.exp (-2 * α * |x|)
    let E (x : ℝ) := ‖f x‖ ^ 2 * w x
    let action (x : ℝ) := conj (f x) * ((L : ℂ) * f x - deriv f x) * (w x : ℂ)
    Integrable E ∧ Integrable action ∧ (L - α) * (∫ x, E x) ≤ (∫ x, action x).re := by
  intro f w E action
  let P (x : ℝ) := conj (f x) * deriv f x * (w x : ℂ)
  obtain ⟨hf, hu, hv⟩ := polynomial_memLp_and_deriv S c k z hz
  obtain ⟨hE, hP, hid⟩ := product_boundary_identity hf hu hv
  change Integrable E at hE
  change Integrable P at hP
  change (∫ x, P x).re = α * ((∫ x in Ioi 0, E x) - ∫ x in Iic 0, E x) at hid
  have heq : action = fun x ↦ ((L * E x : ℝ) : ℂ) - P x := by
    funext x
    have hnorm : conj (f x) * f x = ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
      rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq]
    simp only [action, E, P, ofReal_mul]
    rw [← hnorm]
    ring
  refine ⟨hE, heq.symm ▸ (hE.const_mul L).ofReal.sub hP, ?_⟩
  have hmass := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hE
  rw [compl_Iic] at hmass
  have hsplit : (∫ x : ℝ, ((L * E x : ℝ) : ℂ) - P x) =
      (∫ x : ℝ, ((L * E x : ℝ) : ℂ)) - ∫ x : ℝ, P x :=
    integral_sub (hE.const_mul L).ofReal hP
  change (L - α) * (∫ x, E x) ≤ (∫ x, action x).re
  simp only [heq]
  rw [hsplit, integral_complex_ofReal,
    integral_const_mul, sub_re, ofReal_re, hid, ← hmass]
  have hl : 0 ≤ ∫ x in Iic 0, E x :=
    integral_nonneg fun _ ↦ mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  linarith only [mul_nonneg hα hl]

open IsDedekindDomain NumberField
open scoped NNReal NumberField.AdeleRing InnerProductSpace

section

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (logIdeleClassNorm F)
local notation "ν𝔽" => canonicalModulatedHaar m𝔽
  (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "μ'(" α ")" => intervalSobolevMeasure μ𝔽 logNorm (-α) α 0 true
local notation "W(" α ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α 0
local notation "W'(" α ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α 0 true
local notation "stripJet(" χ ", " j ")" =>
  spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "site(" j ")" => ((j).val.2.1 : ℂ) + ((j).val.2.2.1 : ℂ) * I
local notation "jetVec(" χ ", " hα ", " j ")" =>
  (spectralStripJet_memLp χ hα le_rfl j).toLp (stripJet(χ,j))

private theorem instStripJetCanonicalHaar : (ν𝔽).IsHaarMeasure :=
  (existsUnique_canonicalModulatedHaar m𝔽
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩).exists.choose_spec.1

attribute [local instance] instStripJetCanonicalHaar

/-- Projection along the probability Haar measure on the norm-one classes and the
logarithm on the positive reals give Lebesgue measure for the log-norm. -/
private theorem stripJet_logNorm_preserving : MeasurePreserving logNorm ν𝔽 volume := by
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  obtain ⟨τ, hτc, hτ⟩ := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.2.1
  let τ' : ℝ≥0ˣ →ₜ* C𝔽 := ⟨τ, hτc⟩
  let : CompactSpace (m𝔽).toMonoidHom.ker := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let μ₁ : Measure (m𝔽).toMonoidHom.ker := Measure.haarMeasure ⊤
  let : IsProbabilityMeasure μ₁ := ⟨Measure.haarMeasure_self⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let l (t : ℝ≥0ˣ) := Real.log (t.val : ℝ)
  have hl : Measurable l := Real.measurable_log.comp (NNReal.continuous_coe.comp Units.continuous_val).measurable
  have hp : MeasurePreserving l positiveRealHaar volume := by
    refine ⟨hl, ?_⟩
    let e (x : ℝ) := Units.mk0 (Real.exp x).toNNReal (Real.toNNReal_eq_zero.not.mpr (Real.exp_pos x).not_ge)
    have he : Measurable e := measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
    change (volume.map e).map l = volume
    rw [Measure.map_map hl he, show l ∘ e = id from funext fun x ↦ by
      change Real.log ((Real.exp x).toNNReal : ℝ) = x
      rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp], Measure.map_id]
  have hg : Measurable logNorm := hl.comp (m𝔽).continuous.measurable
  let j (p : (m𝔽).toMonoidHom.ker × ℝ≥0ˣ) := (p.1 : C𝔽) * τ' p.2
  have hj : Measurable j := ((continuous_subtype_val.comp continuous_fst).mul (τ'.continuous.comp continuous_snd)).measurable
  have hlj : logNorm ∘ j = l ∘ Prod.snd := by
    funext ⟨k, t⟩
    change l (ideleClassNorm F ((k : C𝔽) * τ t)) = l t
    rw [map_mul, MonoidHom.mem_ker.mp k.property, one_mul, hτ t]
  refine ⟨hg, ?_⟩
  rw [canonicalModulatedHaar_eq_map_prod m𝔽 hm τ' hτ μ₁ Measure.haarMeasure_self,
    Measure.map_map hg hj, hlj]
  exact (hp.comp (measurePreserving_snd (μ := μ₁) (ν := positiveRealHaar))).map_eq

private theorem stripJetDensity_inv_zero {α : ℝ} (hα : 0 ≤ α) (x : ℝ) :
    (intervalSobolevDensity (-α) α 0 x)⁻¹ = Real.exp (-(2 * α * |x|)) := by
  simp only [intervalSobolevDensity, zero_div, Real.rpow_zero, mul_one]
  rcases le_total 0 x with hx | hx
  · rw [max_eq_right (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hα hx])),
      abs_of_nonneg hx, Real.exp_neg]
  · rw [max_eq_left (Real.exp_le_exp.mpr (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hα hx])),
      abs_of_nonpos hx, ← Real.exp_neg]
    congr 1
    ring

private theorem reciprocalStrip_radial_integral {α : ℝ} (hα : 0 ≤ α) (H : ℝ → ℂ)
    (hm : AEStronglyMeasurable (fun x ↦ H x * (Real.exp (-2 * α * |x|) : ℂ)) volume) :
    ∫ g : C𝔽, H (logNorm g) ∂μ'(α) =
      ((Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) : ℂ) *
        ∫ x : ℝ, H x * (Real.exp (-2 * α * |x|) : ℂ) := by
  let V (x : ℝ) := H x * (Real.exp (-2 * α * |x|) : ℂ)
  have hp : MeasurePreserving logNorm ν𝔽 volume := stripJet_logNorm_preserving
  have hInt : ∫ g : C𝔽, V (logNorm g) ∂ν𝔽 = ∫ x : ℝ, V x := by
    have hv : AEStronglyMeasurable V ((ν𝔽).map logNorm) := hp.map_eq.symm ▸ hm
    rw [← hp.map_eq, integral_map hp.measurable.aemeasurable hv]
  have hden : Measurable (fun g : C𝔽 ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α 0 (logNorm g))⁻¹) := by
    simp_rw [stripJetDensity_inv_zero hα]
    exact ((measurable_const.mul (continuous_abs.measurable.comp hp.measurable)).neg.exp).ennreal_ofReal
  calc
    _ = ∫ g : C𝔽, V (logNorm g) ∂μ𝔽 := by
      change ∫ g : C𝔽, H (logNorm g)
        ∂((μ𝔽).withDensity (fun g : C𝔽 ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α 0 (logNorm g))⁻¹)) = _
      rw [integral_withDensity_eq_integral_toReal_smul hden (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (.of_forall fun g ↦ ?_)
      dsimp only
      rw [stripJetDensity_inv_zero hα, ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul]
      simp only [V, neg_mul, mul_comm (H _)]
    _ = _ := by
      conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν𝔽]
      rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, hInt]

private theorem reciprocalStrip_inner_profiles {α : ℝ} (hα : 0 ≤ α) (ψ : PontryaginDual C𝔽)
    {u v : W'(α)} {f h : ℝ → ℂ}
    (hu : (u : C𝔽 → ℂ) =ᵐ[μ'(α)] fun g ↦ (ψ g : ℂ) * f (logNorm g))
    (hv : (v : C𝔽 → ℂ) =ᵐ[μ'(α)] fun g ↦ (ψ g : ℂ) * h (logNorm g))
    (hm : AEStronglyMeasurable (fun x ↦ conj (f x) * h x * (Real.exp (-2 * α * |x|) : ℂ)) volume) :
    ⟪u,v⟫_ℂ = ((Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) : ℂ) *
      ∫ x : ℝ, conj (f x) * h x * (Real.exp (-2 * α * |x|) : ℂ) := by
  rw [MeasureTheory.L2.inner_def]
  refine Eq.trans (integral_congr_ae ?_) (reciprocalStrip_radial_integral hα (fun x ↦ conj (f x) * h x) hm)
  filter_upwards [hu, hv] with g h₁ h₂
  rw [h₁, h₂, RCLike.inner_apply', map_mul]
  have hunit : conj ((ψ g : Circle) : ℂ) * ((ψ g : Circle) : ℂ) = 1 := by
    rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq, Circle.norm_coe, one_pow, ofReal_one]
  calc
    _ = (conj ((ψ g : Circle) : ℂ) * ((ψ g : Circle) : ℂ)) *
        (conj (f (logNorm g)) * h (logNorm g)) := by ring
    _ = _ := by rw [hunit, one_mul]

/-- Lower an admitted strip jet by one at the same character and spectral site.
At degree zero its lower term has coefficient zero. -/
def SpectralStripJetIndex.lowerOne {χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽}
    {a α s : ℝ} (j : SpectralStripJetIndex χ a α s) : SpectralStripJetIndex χ a α s :=
  ⟨(j.val.1, j.val.2.1, j.val.2.2.1, j.val.2.2.2 - 1), (Nat.sub_le _ _).trans_lt j.property⟩

private theorem stripJet_exp_profile (ψ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) (g : C𝔽) :
    spectralZeroJet ψ b t k g =
      (ψ g : ℂ) * jetMonomial k ((b : ℂ) + (t : ℂ) * I) (logNorm g) := by
  let q : ℝ := ((ideleClassNorm F g).val : ℝ)
  have hq : 0 < q := NNReal.coe_pos.mpr (Units.zero_lt _)
  have he (z : ℂ) : ideleClassNormTwist ψ z g = (ψ g : ℂ) * exp (((logNorm g : ℝ) : ℂ) * z) := by
    change (ψ g : ℂ) * (q : ℂ) ^ z = _
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hq.ne'), ← ofReal_log hq.le]
  simp only [spectralZeroJet, he, jetMonomial]
  rw [mul_comm ((logNorm g : ℝ) : ℂ)]
  ring

/-- Every retained jet at Sobolev order zero lies strictly inside the strip. -/
theorem SpectralStripJetIndex.abs_re_lt_width {χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽}
    {a α : ℝ} (j : SpectralStripJetIndex χ a α 0) : |(site(j)).re| < α := by
  simp only [add_re, mul_I_re, ofReal_im, neg_zero, ofReal_re, add_zero]
  have h := j.property
  unfold spectralStripMultiplicity at h
  split_ifs at h with h₁ h₂
  · exact abs_lt.mpr h₁
  · have hbad := ((lt_spectralBoundaryMultiplicity 0 _ _).mp h).2
    linarith [Nat.cast_nonneg (α := ℝ) j.val.2.2.2]
  · omega

private theorem coe_sum_smul_profile {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (S : Finset ι) (c : ι → ℂ) (v : ι → Lp ℂ 2 μ) (f : ι → X → ℂ)
    (hv : ∀ i ∈ S, (v i : X → ℂ) =ᵐ[μ] f i) :
    ((∑ i ∈ S, c i • v i : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] fun x ↦ ∑ i ∈ S, c i * f i x := by
  refine (Lp.coeFn_finsetSum S _).trans ?_
  have hi (i) (hi : i ∈ S) : ((c i • v i : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] fun x ↦ c i * f i x := by
    filter_upwards [Lp.coeFn_smul (c i) (v i), hv i hi] with x hx hy
    simp only [hx, Pi.smul_apply, smul_eq_mul, hy]
  refine (eventuallyEq_sum hi).trans (.of_forall fun x ↦ ?_)
  simp only [Finset.sum_apply]

private theorem stripJetRiesz_antiIsometry
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    {a α : ℝ} (hα : 0 ≤ α) (r : SpectralStripJetIndex χ a α 0 → W(α))
    (hr : ∀ j f, ⟪r j,f⟫_ℂ = spectralSobolevPairing f (jetVec(χ,hα,j))) :
    ∃ J : W(α) ≃ₗᵢ⋆[ℂ] W'(α), ∀ j, J (r j) = jetVec(χ,hα,j) := by
  let E := modulatedIntervalSobolev_dual m𝔽
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽
    (-α) α 0 (neg_le_self hα) le_rfl |>.exists.choose
  refine ⟨(InnerProductSpace.toDual ℂ W(α)).trans E, fun j ↦ ?_⟩
  apply E.symm.injective
  change E.symm (E ((InnerProductSpace.toDual ℂ W(α)) (r j))) = _
  rw [E.symm_apply_apply]
  ext f
  rw [InnerProductSpace.toDual_apply_apply, hr]
  have h := (spectralSobolevPairing_dual (F := F) (neg_le_self hα) (le_rfl : 0 ≤ (0 : ℝ))
    (E.symm (jetVec(χ,hα,j))) f).2
  change _ = spectralSobolevPairing f (E (E.symm (jetVec(χ,hα,j)))) at h
  simpa only [E.apply_symm_apply] using h.symm

private theorem stripJetAntiIsometry_re_inner {A B : Type*} [NormedAddCommGroup A]
    [InnerProductSpace ℂ A] [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (J : A ≃ₗᵢ⋆[ℂ] B) (x y : A) : (⟪J x,J y⟫_ℂ).re = (⟪x,y⟫_ℂ).re := by
  have hp := norm_add_sq (𝕜 := ℂ) (J x) (J y)
  rw [← J.map_add, J.norm_map, J.norm_map, J.norm_map] at hp
  have hxy := norm_add_sq (𝕜 := ℂ) x y
  simp only [RCLike.re_to_complex] at hp hxy
  linarith

private theorem reciprocalStrip_norm_sq_profile {α : ℝ} (hα : 0 ≤ α) (ψ : PontryaginDual C𝔽)
    {u : W'(α)} {f : ℝ → ℂ}
    (hu : (u : C𝔽 → ℂ) =ᵐ[μ'(α)] fun g ↦ (ψ g : ℂ) * f (logNorm g))
    (he : Integrable (fun x ↦ ‖f x‖ ^ 2 * Real.exp (-2 * α * |x|))) :
    ‖u‖ ^ 2 = (Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) * ∫ x, ‖f x‖ ^ 2 * Real.exp (-2 * α * |x|) := by
  let w (x : ℝ) := Real.exp (-2 * α * |x|)
  let E (x : ℝ) := ‖f x‖ ^ 2 * w x
  have hnorm (x : ℝ) : conj (f x) * f x * (w x : ℂ) = (E x : ℂ) := by
    simp only [E, ofReal_mul, ← normSq_eq_conj_mul_self, normSq_eq_norm_sq]
  have hm : AEStronglyMeasurable (fun x ↦ conj (f x) * f x * (w x : ℂ)) volume := by
    simp_rw [hnorm]
    exact he.ofReal.aestronglyMeasurable
  have h := reciprocalStrip_inner_profiles (f := f) (h := f) (u := u) (v := u) hα ψ hu hu hm
  change _ = _ * ∫ x, conj (f x) * f x * (w x : ℂ) at h
  simp_rw [hnorm] at h
  rw [integral_complex_ofReal] at h
  calc
    _ = (⟪u,u⟫_ℂ).re := (inner_self_eq_norm_sq (𝕜 := ℂ) u).symm
    _ = _ := by rw [h, re_ofReal_mul, ofReal_re]

private theorem reciprocalStrip_accretive_of_profiles {ι : Type*}
    {α : ℝ} (hα : 0 ≤ α) (ψ : PontryaginDual C𝔽)
    (S : Finset ι) (c : ι → ℂ) (k : ι → ℕ) (z : ι → ℂ)
    (hz : ∀ i ∈ S, |(z i).re| < α) (L : ℝ) (u v : W'(α))
    (hu : (u : C𝔽 → ℂ) =ᵐ[μ'(α)] fun g ↦ (ψ g : ℂ) * stripExpPolynomial S c k z (logNorm g))
    (hv : (v : C𝔽 → ℂ) =ᵐ[μ'(α)] fun g ↦ (ψ g : ℂ) *
      ((L : ℂ) * stripExpPolynomial S c k z (logNorm g) - deriv (stripExpPolynomial S c k z) (logNorm g))) :
    (L - α) * ‖u‖ ^ 2 ≤ (⟪u,v⟫_ℂ).re := by
  let f := stripExpPolynomial S c k z
  let w (x : ℝ) := Real.exp (-2 * α * |x|)
  let G (x : ℝ) := (L : ℂ) * f x - deriv f x
  let C : ℝ := Measure.haarScalarFactor μ𝔽 ν𝔽
  have hc : 0 ≤ C := NNReal.coe_nonneg _
  obtain ⟨he,hh⟩ := stripExpPolynomial_accretive S c k z hα hz L
  change Integrable (fun x ↦ conj (f x) * G x * (w x : ℂ)) ∧
    (L - α) * (∫ x, ‖f x‖ ^ 2 * w x) ≤ (∫ x, conj (f x) * G x * (w x : ℂ)).re at hh
  have hself := reciprocalStrip_norm_sq_profile (u := u) (f := f) hα ψ hu he
  have hgen := reciprocalStrip_inner_profiles (f := f) (h := G) (u := u) (v := v) hα ψ hu hv hh.1.aestronglyMeasurable
  change ⟪u,v⟫_ℂ = (C : ℂ) * ∫ x, conj (f x) * G x * (w x : ℂ) at hgen
  rw [hself, hgen, re_ofReal_mul]
  change (L - α) * (C * _) ≤ C * _
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left hh.2 hc

private theorem stripJetReciprocal_profiles
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽) {a α : ℝ} (hα : 0 ≤ α)
    (S : Finset (SpectralStripJetIndex χ a α 0)) (ω : PontryaginDual (ideleClassNorm F).ker)
    (hω : ∀ j ∈ S, j.val.1 = ω) (c : SpectralStripJetIndex χ a α 0 → ℂ) (L : ℝ) :
    let k (j : SpectralStripJetIndex χ a α 0) := j.val.2.2.2
    let z (j : SpectralStripJetIndex χ a α 0) := site(j)
    let v (j : SpectralStripJetIndex χ a α 0) : W'(α) := jetVec(χ,hα,j)
    let f := stripExpPolynomial S c k z
    (((∑ j ∈ S, c j • v j : W'(α)) : C𝔽 → ℂ) =ᵐ[μ'(α)]
        fun g ↦ (χ ω g : ℂ) * f (logNorm g)) ∧
      (((∑ j ∈ S, c j • (((L : ℂ) - z j) • v j - (k j : ℂ) • v j.lowerOne) : W'(α)) : C𝔽 → ℂ)
        =ᵐ[μ'(α)] fun g ↦ (χ ω g : ℂ) * ((L : ℂ) * f (logNorm g) - deriv f (logNorm g))) := by
  intro k z v f
  let m (j : SpectralStripJetIndex χ a α 0) := jetMonomial (k j) (z j)
  have hm (j : SpectralStripJetIndex χ a α 0) (hj : j.val.1 = ω) :
      (v j : C𝔽 → ℂ) =ᵐ[μ'(α)] fun g ↦ (χ ω g : ℂ) * m j (logNorm g) := by
    refine (spectralStripJet_memLp χ hα le_rfl j).coeFn_toLp.trans (.of_forall fun g ↦ ?_)
    exact (stripJet_exp_profile (χ j.val.1) _ _ _ g).trans (by rw [hj])
  have hm' (j : SpectralStripJetIndex χ a α 0) (hj : j.val.1 = ω) :
      ((((L : ℂ) - z j) • v j - (k j : ℂ) • v j.lowerOne : W'(α)) : C𝔽 → ℂ) =ᵐ[μ'(α)]
        fun g ↦ (χ ω g : ℂ) * (((L : ℂ) - z j) * m j (logNorm g) - (k j : ℂ) * m j.lowerOne (logNorm g)) := by
    filter_upwards [Lp.coeFn_sub (((L : ℂ) - z j) • v j) ((k j : ℂ) • v j.lowerOne),
      Lp.coeFn_smul ((L : ℂ) - z j) (v j), Lp.coeFn_smul (k j : ℂ) (v j.lowerOne),
      hm j hj, hm j.lowerOne hj] with g hab ha hb h₁ h₂
    simp only [hab, Pi.sub_apply, ha, hb, Pi.smul_apply, smul_eq_mul, h₁, h₂]
    ring
  constructor
  · refine (coe_sum_smul_profile S c v _ (fun j hj ↦ hm j (hω j hj))).trans (.of_forall fun g ↦ ?_)
    simp only [f, stripExpPolynomial, m, jetMonomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · refine (coe_sum_smul_profile S c _ _ (fun j hj ↦ hm' j (hω j hj))).trans (.of_forall fun g ↦ ?_)
    have hd := (hasDerivAt_stripExpPolynomial S c k z (logNorm g)).deriv
    change deriv f (logNorm g) = _ at hd
    dsimp only
    rw [hd]
    simp only [f, stripExpPolynomial, mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [m, jetMonomial, show k j.lowerOne = k j - 1 from rfl,
      show z j.lowerOne = z j from rfl]
    ring

/-- In the primal adelic Sobolev norm the real part of the shifted generator on every
finite family of admitted jets in one angular mode is bounded below by the shift minus
the strip half-width. The lowered jet need not belong to the finite family. -/
theorem spectralStripJet_riesz_generator_accretive
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    {a α : ℝ} (hα : 0 ≤ α) (r : SpectralStripJetIndex χ a α 0 → W(α))
    (hr : ∀ j f, ⟪r j,f⟫_ℂ = spectralSobolevPairing f (jetVec(χ,hα,j)))
    (S : Finset (SpectralStripJetIndex χ a α 0)) (ω : PontryaginDual (ideleClassNorm F).ker)
    (hω : ∀ j ∈ S, j.val.1 = ω) (d : SpectralStripJetIndex χ a α 0 → ℂ) (L : ℝ) :
    (L - α) * ‖∑ j ∈ S, d j • r j‖ ^ 2 ≤
      (⟪∑ j ∈ S, d j • r j, ∑ j ∈ S, d j •
        (((L : ℂ) - conj site(j)) • r j - (j.val.2.2.2 : ℂ) • r j.lowerOne)⟫_ℂ).re := by
  let c (j : SpectralStripJetIndex χ a α 0) := conj (d j)
  let k (j : SpectralStripJetIndex χ a α 0) := j.val.2.2.2
  let z (j : SpectralStripJetIndex χ a α 0) := site(j)
  let v (j : SpectralStripJetIndex χ a α 0) : W'(α) := jetVec(χ,hα,j)
  obtain ⟨J,hJ⟩ := stripJetRiesz_antiIsometry χ hα r hr
  obtain ⟨hu,hv⟩ := stripJetReciprocal_profiles χ hα S ω hω c L
  have h := reciprocalStrip_accretive_of_profiles hα (χ ω) S c k z (fun j _ ↦ j.abs_re_lt_width) L
    (∑ j ∈ S, c j • v j) (∑ j ∈ S, c j • (((L : ℂ) - z j) • v j - (k j : ℂ) • v j.lowerOne)) hu hv
  rw [← J.norm_map (∑ j ∈ S, d j • r j), ← stripJetAntiIsometry_re_inner J]
  simpa only [map_sum, J.map_smulₛₗ, map_sub, map_natCast, conj_ofReal, conj_conj, hJ, v, z, k, c] using h

end
end RiemannMasullo
