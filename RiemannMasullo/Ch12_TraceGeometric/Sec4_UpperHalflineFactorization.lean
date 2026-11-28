module

public import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertSchmidtProduct
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_UpperHalflineKernels
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Regular

/-! # Hilbert–Schmidt factorization of the real upper half-line cutoff -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology

namespace RiemannMasullo

/-- The kernel `exp(-|x - y|) / 2` inverts `1 - ∂²` on a Schwartz test.
The integral is in the incoming variable `y`, against Lebesgue measure. -/
private theorem realGreenKernel_integral_sub_secondDeriv (q : 𝓢(ℝ, ℂ)) (x : ℝ) :
    let d := SchwartzMap.derivCLM ℂ ℂ q
    let r := q - SchwartzMap.derivCLM ℂ ℂ d
    let G (y : ℝ) : ℂ := (Real.exp (-|x - y|) : ℂ) / 2
    Integrable (fun y ↦ G y * r y) ∧ ∫ y, G y * r y = q x := by
  intro d r G
  let d₂ := SchwartzMap.derivCLM ℂ ℂ d
  let ep (y : ℝ) : ℂ := Real.exp y
  let em (y : ℝ) : ℂ := Real.exp (-y)
  let L (y : ℝ) : ℂ := ep y * (q y - d y)
  let R (y : ℝ) : ℂ := -em y * (q y + d y)
  have hq (y : ℝ) : HasDerivAt q (d y) y := q.hasDerivAt y
  have hd (y : ℝ) : HasDerivAt d (d₂ y) y := d.hasDerivAt y
  have hep (y : ℝ) : HasDerivAt ep (ep y) y := (Real.hasDerivAt_exp y).ofReal_comp
  have hem (y : ℝ) : HasDerivAt em (-em y) y := by
    simpa only [em, mul_neg_one, Complex.ofReal_neg] using (hasDerivAt_neg y).exp.ofReal_comp
  have hL (y : ℝ) : HasDerivAt L (ep y * r y) y := by
    convert (hep y).mul ((hq y).sub (hd y)) using 1
    change _ = ep y * (q y - d y) + ep y * (d y - d₂ y)
    change ep y * (q y - d₂ y) = _
    ring
  have hR (y : ℝ) : HasDerivAt R (em y * r y) y := by
    convert (hem y).neg.mul ((hq y).add (hd y)) using 1
    change _ = -(-em y) * (q y + d y) + (-em y) * (d y + d₂ y)
    change em y * (q y - d₂ y) = _
    ring
  have hepC : Continuous ep := Complex.continuous_ofReal.comp Real.continuous_exp
  have hemC : Continuous em := hepC.comp continuous_neg
  have hiL : IntegrableOn (fun y ↦ ep y * r y) (Iic x) := by
    refine r.integrable.integrableOn.bdd_mul (c := Real.exp x) hepC.aestronglyMeasurable ?_
    exact (ae_restrict_iff' measurableSet_Iic).2 (ae_of_all _ fun y hy ↦ by
      simp only [ep, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr hy)
  have hiR : IntegrableOn (fun y ↦ em y * r y) (Ioi x) := by
    refine r.integrable.integrableOn.bdd_mul (c := Real.exp (-x)) hemC.aestronglyMeasurable ?_
    exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun y hy ↦ by
      simp only [em, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (neg_le_neg (mem_Ioi.mp hy).le))
  have hep₀ : Tendsto ep atBot (𝓝 (0 : ℂ)) := by
    simpa only [ep, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto' 0 0 Complex.ofReal_zero).comp Real.tendsto_exp_atBot
  have hem₀ : Tendsto em atTop (𝓝 (0 : ℂ)) := hep₀.comp tendsto_neg_atTop_atBot
  have hL₀ : Tendsto L atBot (𝓝 (0 : ℂ)) := by
    simpa only [L, sub_apply, zero_mul] using
      hep₀.mul ((q - d).tendsto_cocompact.mono_left atBot_le_cocompact)
  have hR₀ : Tendsto R atTop (𝓝 (0 : ℂ)) := by
    simpa only [R, add_apply, neg_zero, zero_mul] using
      hem₀.neg.mul ((q + d).tendsto_cocompact.mono_left atTop_le_cocompact)
  have hIL : (∫ y in Iic x, ep y * r y) = L x := by
    simpa only [sub_zero] using
      integral_Iic_of_hasDerivAt_of_tendsto' (fun y _ ↦ hL y) hiL hL₀
  have hIR : (∫ y in Ioi x, em y * r y) = -R x := by
    simpa only [zero_sub] using
      integral_Ioi_of_hasDerivAt_of_tendsto' (fun y _ ↦ hR y) hiR hR₀
  have hGL : EqOn (fun y ↦ G y * r y) (fun y ↦ (em x / 2) * (ep y * r y)) (Iic x) := by
    intro y hy
    dsimp only [G, em, ep]
    rw [abs_of_nonneg (sub_nonneg.mpr hy), show -(x - y) = -x + y by ring,
      Real.exp_add, Complex.ofReal_mul]
    ring
  have hGR : EqOn (fun y ↦ G y * r y) (fun y ↦ (ep x / 2) * (em y * r y)) (Ioi x) := by
    intro y hy
    dsimp only [G, em, ep]
    rw [abs_of_nonpos (sub_nonpos.mpr (mem_Ioi.mp hy).le), neg_neg,
      sub_eq_add_neg, Real.exp_add, Complex.ofReal_mul]
    ring
  have hGC : Continuous G := by dsimp only [G]; fun_prop
  have hG : Integrable (fun y ↦ G y * r y) := by
    refine r.integrable.bdd_mul (c := 1 / 2) hGC.aestronglyMeasurable (ae_of_all _ fun y ↦ ?_)
    have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg (x - y)))
    calc
      ‖G y‖ = Real.exp (-|x - y|) / 2 := by
        dsimp only [G]
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        norm_num
      _ ≤ _ := div_le_div_of_nonneg_right h (by norm_num)
  have hprod : em x * ep x = 1 := by
    dsimp only [em, ep]
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  refine ⟨hG, ?_⟩
  calc
    (∫ y, G y * r y) = (∫ y in Iic x, G y * r y) + ∫ y in Ioi x, G y * r y := by
      simpa only [compl_Iic] using (integral_add_compl (s := Iic x) measurableSet_Iic hG).symm
    _ = (em x / 2) * L x + (ep x / 2) * (-R x) := by
      rw [setIntegral_congr_fun measurableSet_Iic hGL, setIntegral_congr_fun measurableSet_Ioi hGR,
        integral_const_mul, integral_const_mul, hIL, hIR]
    _ = (em x * ep x) * ((q x - d x) / 2 + (q x + d x) / 2) := by
      dsimp only [L, R]
      ring
    _ = q x := by rw [hprod]; ring

/-- Compose the rows of two square-integrable kernels with potentially different
source, middle, and target measures. The operator hypotheses can be obtained
from the Hilbert–Schmidt kernel correspondence. The conclusion uses the
original kernel functions and gives the integrability needed for Fubini. -/
private theorem comp_squareIntegrableKernel_rows
    {X Z Y : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
    (μX : Measure X) (μZ : Measure Z) (μY : Measure Y)
    [SFinite μX] [SFinite μZ] [SFinite μY]
    {A : X × Z → ℂ} {B : Z × Y → ℂ}
    (hA : MemLp A 2 (μX.prod μZ)) (hB : MemLp B 2 (μZ.prod μY))
    (TA : Lp ℂ 2 μZ →L[ℂ] Lp ℂ 2 μX) (TB : Lp ℂ 2 μY →L[ℂ] Lp ℂ 2 μZ)
    (hTA : ∀ g, ∀ᵐ x ∂μX, TA g x = ∫ z, A (x, z) * g z ∂μZ)
    (hTB : ∀ f, ∀ᵐ z ∂μZ, TB f z = ∫ y, B (z, y) * f y ∂μY)
    (f : Lp ℂ 2 μY) :
    ∀ᵐ x ∂μX,
      Integrable (fun y ↦ (∫ z, A (x, z) * B (z, y) ∂μZ) * f y) μY ∧
      TA (TB f) x = ∫ y, (∫ z, A (x, z) * B (z, y) ∂μZ) * f y ∂μY := by
  let a := hA.toLp A
  have haEq : ∀ᵐ x ∂μX, ∀ᵐ z ∂μZ, a (x, z) = A (x, z) :=
    Measure.ae_ae_of_ae_prod hA.coeFn_toLp
  have haSq := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable a)).mp (Lp.memLp a)
  have hArows : ∀ᵐ x ∂μX, MemLp (fun z ↦ A (x, z)) 2 μZ := by
    filter_upwards [haSq.prod_right_ae, haEq] with x hx hEq
    have hr : MemLp (fun z ↦ a (x, z)) 2 μZ :=
      (memLp_two_iff_integrable_sq_norm
        ((Lp.stronglyMeasurable a).comp_measurable
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr hx
    exact MemLp.ae_eq hEq hr
  filter_upwards [hTA (TB f), hArows] with x hx hrow
  let J (p : Z × Y) : ℂ := A (x, p.1) * B p * f p.2
  have hJm : AEStronglyMeasurable J (μZ.prod μY) :=
    ((hrow.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst).mul hB.aestronglyMeasurable).mul
      ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd)
  have hJs : Integrable J (μZ.prod μY) := by
    have hra := (memLp_two_iff_integrable_sq_norm hrow.aestronglyMeasurable).mp hrow
    have hfb := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
    have hbs := (memLp_two_iff_integrable_sq_norm hB.aestronglyMeasurable).mp hB
    refine (((hra.mul_prod hfb).add hbs).const_mul (1 / 2 : ℝ)).mono' hJm ?_
    filter_upwards with p
    dsimp only [J, Pi.add_apply]
    simp only [norm_mul]
    nlinarith [sq_nonneg (‖A (x, p.1)‖ * ‖f p.2‖ - ‖B p‖)]
  have hJright (y : Y) :
      (∫ z, J (z, y) ∂μZ) = (∫ z, A (x, z) * B (z, y) ∂μZ) * f y := by
    change (∫ z, (A (x, z) * B (z, y)) * f y ∂μZ) = _
    exact integral_mul_const (f y) (fun z ↦ A (x, z) * B (z, y))
  refine ⟨hJs.integral_prod_right.congr (ae_of_all _ hJright), ?_⟩
  calc
    _ = ∫ z, A (x, z) * TB f z ∂μZ := hx
    _ = ∫ z, ∫ y, J (z, y) ∂μY ∂μZ := by
      apply integral_congr_ae
      filter_upwards [hTB f] with z hz
      rw [hz, ← integral_const_mul]
      simp only [J, mul_assoc]
    _ = ∫ y, ∫ z, J (z, y) ∂μZ ∂μY :=
      (integral_prod J hJs).symm.trans (integral_prod_symm J hJs)
    _ = _ := integral_congr_ae (ae_of_all _ hJright)

/-- The source-first Hilbert–Schmidt correspondence on real measure spaces
acts on the originally chosen representative, with an integrable row. -/
private theorem realSourceFirstHilbertSchmidt_apply_raw
    (μ ν : Measure ℝ) [IsFiniteMeasureOnCompacts μ] [Measure.InnerRegular μ]
    [IsFiniteMeasureOnCompacts ν] [Measure.InnerRegular ν]
    {K : ℝ × ℝ → ℂ} (hK : MemLp K 2 (μ.prod ν)) (f : Lp ℂ 2 μ) :
    ∀ᵐ x ∂ν, Integrable (fun y ↦ K (y, x) * f y) μ ∧
      ((hilbertSchmidtOperators_equiv_Lp_prod μ ν).choose (hK.toLp K)).val f x =
        ∫ y, K (y, x) * f y ∂μ := by
  let swapBack := Measure.measurePreserving_swap (μ := ν) (ν := μ)
  have hker : ∀ᵐ p ∂(ν.prod μ), (hK.toLp K) p.swap = K p.swap :=
    swapBack.quasiMeasurePreserving.ae hK.coeFn_toLp
  filter_upwards [(hilbertSchmidtOperators_equiv_Lp_prod μ ν).choose_spec.2 (hK.toLp K) f,
    Measure.ae_ae_of_ae_prod hker] with x hx hxrow
  have hmul : (fun y ↦ (hK.toLp K) (y, x) * f y) =ᵐ[μ] fun y ↦ K (y, x) * f y :=
    hxrow.mono fun y hy ↦ congrArg (· * f y) hy
  exact ⟨hx.1.congr hmul, hx.2.trans (integral_congr_ae hmul)⟩

/-- Factor a convolution from the right half-line into two rectangular
Hilbert–Schmidt maps. The input domain is an (L^2) space for the restricted
measure, so its source-first kernel needs no additional mask. The output
can carry a different measure, such as the polynomial Sobolev density. -/
private theorem rectangularGreenFactorization_apply
    (μX : Measure ℝ) [IsFiniteMeasureOnCompacts μX] [Measure.InnerRegular μX]
    (a : ℝ) (c w G r q : ℝ → ℂ) (hw : ∀ z, w z ≠ 0)
    (hGreen : ∀ t, (∫ z : ℝ, G (t - z) * r z) = q t) :
    let μY := (volume : Measure ℝ).restrict (Ici a)
    let A (p : ℝ × ℝ) := c p.2 * G (p.2 - p.1) * w p.1
    let B (p : ℝ × ℝ) := (w p.2)⁻¹ * r (p.2 - p.1)
    ∀ (hA : MemLp A 2 ((volume : Measure ℝ).prod μX))
      (hB : MemLp B 2 (μY.prod volume)),
    let TA := (hilbertSchmidtOperators_equiv_Lp_prod (volume : Measure ℝ) μX).choose
      (hA.toLp A)
    let TB := (hilbertSchmidtOperators_equiv_Lp_prod μY (volume : Measure ℝ)).choose
      (hB.toLp B)
    ∀ f : Lp ℂ 2 μY, ∀ᵐ x ∂μX,
      Integrable (fun y ↦ (c x * q (x - y)) * f y) μY ∧
      TA.val (TB.val f) x = c x * ∫ y, q (x - y) * f y ∂μY := by
  intro μY A B hA hB TA TB f
  let A' (p : ℝ × ℝ) := A p.swap
  let B' (p : ℝ × ℝ) := B p.swap
  have hA' : MemLp A' 2 (μX.prod (volume : Measure ℝ)) :=
    hA.comp_measurePreserving (Measure.measurePreserving_swap (μ := μX) (ν := volume))
  have hB' : MemLp B' 2 ((volume : Measure ℝ).prod μY) :=
    hB.comp_measurePreserving (Measure.measurePreserving_swap (μ := volume) (ν := μY))
  have hTA (g : Lp ℂ 2 (volume : Measure ℝ)) :
      ∀ᵐ x ∂μX, TA.val g x = ∫ z, A' (x, z) * g z := by
    exact (realSourceFirstHilbertSchmidt_apply_raw volume μX hA g).mono fun _ hx ↦ hx.2
  have hTB (g : Lp ℂ 2 μY) :
      ∀ᵐ z ∂volume, TB.val g z = ∫ y, B' (z, y) * g y ∂μY := by
    exact (realSourceFirstHilbertSchmidt_apply_raw μY volume hB g).mono fun _ hx ↦ hx.2
  have hkernel (x y : ℝ) : (∫ z, A' (x, z) * B' (z, y)) = c x * q (x - y) := by
    have hshift : (∫ z : ℝ, G (x - z) * r (z - y)) =
        ∫ z : ℝ, G ((x - y) - z) * r z := by
      have he (z : ℝ) : (x - y) - (z - y) = x - z := by ring
      simpa only [he] using
        (integral_sub_right_eq_self (μ := volume) (fun z : ℝ ↦ G ((x - y) - z) * r z) y)
    calc
      _ = ∫ z, c x * (G (x - z) * r (z - y)) := by
        refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
        change (c x * G (x - z) * w z) * ((w z)⁻¹ * r (z - y)) = _
        calc
          _ = (c x * (G (x - z) * r (z - y))) * (w z * (w z)⁻¹) := by ring
          _ = _ := by rw [mul_inv_cancel₀ (hw z), mul_one]
      _ = c x * ∫ z : ℝ, G (x - z) * r (z - y) := integral_const_mul _ _
      _ = _ := congrArg (c x * ·) (hshift.trans (hGreen (x - y)))
  filter_upwards [comp_squareIntegrableKernel_rows μX volume μY hA' hB'
    TA.val TB.val hTA hTB f] with x hx
  have heq : (fun y ↦ (∫ z, A' (x, z) * B' (z, y)) * f y) =
      fun y ↦ (c x * q (x - y)) * f y :=
    funext fun y ↦ congrArg (· * f y) (hkernel x y)
  refine ⟨hx.1.congr (ae_of_all _ (congrFun heq)), hx.2.trans ?_⟩
  rw [heq, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun _ ↦ mul_assoc _ _ _)

/-- Paper: Theorem 12.4.1.1, pp. 514–517 (n. 2 and Step II).
For an upper real cutoff and a lower bound on the input support,
Schwartz convolution into the logarithmic Sobolev measure factors through
two Hilbert–Schmidt operators. Their product is rectangular trace class
and acts by the cutoff convolution against restricted Lebesgue measure.
Deviation: This is the convolution model in the real logarithmic coordinate. -/
theorem exists_upperHalflineWeightedConvolutionFactors
    (s : ℝ) (hs : 0 ≤ s) (a T : ℝ) (ρ : ℝ → ℝ) (hρm : Measurable ρ)
    (hρ : ∀ t, |ρ t| ≤ 1) (hρT : ∀ t, T < t → ρ t = 0) (q : 𝓢(ℝ, ℂ)) :
    let ν := intervalSobolevMeasure (volume : Measure ℝ) id 0 0 s
    let μ := (volume : Measure ℝ).restrict (Ici a)
    ∃ (A : hilbertSchmidtOperators (Lp ℂ 2 (volume : Measure ℝ)) (Lp ℂ 2 ν))
      (B : hilbertSchmidtOperators (Lp ℂ 2 μ) (Lp ℂ 2 (volume : Measure ℝ))),
      A.val.comp B.val ∈ traceClassOperators (Lp ℂ 2 μ) (Lp ℂ 2 ν) ∧
      ∀ f : Lp ℂ 2 μ, ∀ᵐ x ∂ν,
        Integrable (fun y ↦ ((ρ x : ℂ) * q (x - y)) * f y) μ ∧
        A.val (B.val f) x = (ρ x : ℂ) * ∫ y, q (x - y) * f y ∂μ := by
  intro ν μ
  have hw : Continuous (intervalSobolevDensity 0 0 s) := by
    unfold intervalSobolevDensity
    refine Continuous.mul (by fun_prop)
      ((continuous_const.add (continuous_id.pow 2)).rpow_const fun x ↦ ?_)
    exact Or.inl (ne_of_gt (show 0 < 1 + x ^ 2 from by positivity))
  let : IsLocallyFiniteMeasure ν := by
    change IsLocallyFiniteMeasure ((volume : Measure ℝ).withDensity
      (fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s x)))
    exact IsLocallyFiniteMeasure.withDensity_ofReal (μ := volume) hw
  obtain ⟨m, hm⟩ := exists_nat_gt ((s + 1) / 2)
  have hms : s + 1 < 2 * (m : ℝ) := by linarith
  have hmb : 1 < 2 * (m : ℝ) := by linarith
  let c (t : ℝ) : ℂ := ρ t
  let w (t : ℝ) : ℂ := upperHalflinePolynomialWeight m t
  let G (t : ℝ) : ℂ := (Real.exp (-|t|) : ℂ) / 2
  let r := q - SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)
  let aK (p : ℝ × ℝ) : ℂ := c p.2 * G (p.2 - p.1) * w p.1
  let bK (p : ℝ × ℝ) : ℂ := (w p.2)⁻¹ * r (p.2 - p.1)
  have haK : MemLp aK 2 ((volume : Measure ℝ).prod ν) :=
    memLp_upperHalflineGreenFactor s hs m hms T ρ hρm hρ hρT
  have hbK : MemLp bK 2 (μ.prod (volume : Measure ℝ)) :=
    memLp_upperHalflineSchwartzFactor m hmb a r
  have hw₀ (z : ℝ) : w z ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (upperHalflinePolynomialWeight_pos m z).ne'
  have hG (t : ℝ) : (∫ z, G (t - z) * r z) = q t :=
    (realGreenKernel_integral_sub_secondDeriv q t).2
  let A := (hilbertSchmidtOperators_equiv_Lp_prod (volume : Measure ℝ) ν).choose
    (haK.toLp aK)
  let B := (hilbertSchmidtOperators_equiv_Lp_prod μ (volume : Measure ℝ)).choose
    (hbK.toLp bK)
  exact ⟨A, B, comp_mem_traceClass A B,
    rectangularGreenFactorization_apply ν a c w G r q hw₀ hG haK hbK⟩

end RiemannMasullo
