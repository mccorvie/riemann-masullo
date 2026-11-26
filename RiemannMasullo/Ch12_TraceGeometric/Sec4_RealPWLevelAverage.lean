module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelOperator
public import RiemannMasullo.ForMathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! # The compression of the averaged dilation to the real Paley–Wiener level

Paper: Theorem 12.4.1.1, pp. 514–519, as used on p. 520.

`Sec4_RealPWLevelOperator` computes the Hilbert trace of `P ∘ M_L ∘ D_g ∘ P` for one dilation
`g`, and the limit of the average of these traces against `φ(g) dg / g`. This file forms the
average of the operators. The action of the test `φ` is the operator
`A = ∫ g in a..b, (φ g / g) • D_g`, a Bochner integral in `L²(ℝ)` applied vector by vector, and
the trace of `P ∘ M_L ∘ A ∘ P` is the average of the traces.

* `realDilationAverage φ a b`: the operator `A`, a continuous linear map on `L²(ℝ)`.
* `isNuclearOperator_realPWLevel_average_compression`: `P ∘ M_L ∘ A ∘ P` is nuclear.
* `hilbertTrace_realPWLevel_average_compression`: its Hilbert trace is
  `∫ g in a..b, φ g * Tr (P ∘ M_L ∘ D_g ∘ P) / g`.
* `tendsto_hilbertTrace_realPWLevel_average_compression`: as `Y * L → ∞` the traces tend to the
  real-place term of (12.5.1.1) minus `∫ φ(g) min(g^(1/2), g^(-1/2)) d×g`, for `φ` continuous on
  an interval of `(0, ∞)` that does not contain `1`.

The proof goes through kernels. The kernel of `M_L ∘ D_g ∘ P` is a vector of `L²` of the plane
that is strongly measurable in `g` and bounded for `g` away from zero, so its weighted integral
exists there. The correspondence from kernels to operators is a continuous linear map, hence the
integral operator of the integrated kernel is `M_L ∘ A ∘ P`. The trace of a composite of two
kernel operators is a continuous linear functional of the second kernel, hence it commutes with
the integral. Strong measurability is obtained from measurable inner products
(`stronglyMeasurable_of_measurable_inner`), so no continuity of the dilations is needed.
-/

open MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate InnerProductSpace SchwartzMap ContDiff ENNReal

@[expose] public noncomputable section

namespace RiemannMasullo

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)
local notation "H₂" => Lp ℂ 2 (Measure.prod (volume : Measure ℝ) (volume : Measure ℝ))

/-! ### Kernels and operators -/

/-- The operator norm of an integral operator is at most the `L²` norm of its kernel. -/
theorem norm_integralKernelOperator_le_norm (k : H₂) :
    ‖(integralKernelOperator volume k).val‖ ≤ ‖k‖ := by
  let A := integralKernelOperator volume k
  have hA : IsCompactOperator A.val ∧ Summable (fun n ↦ approximationNumber A.val n ^ (2 : ℝ)) :=
    A.property
  have hbound := hA.2.le_tsum 0 (fun n _ ↦ by rw [Real.rpow_two]; positivity)
  rw [approximationNumber_zero_eq_opNorm A.val hA.1, Real.rpow_two] at hbound
  rw [← schattenNorm_integralKernelOperator volume k]
  change ‖A.val‖ ≤ (∑' n, approximationNumber A.val n ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq (norm_nonneg A.val)]
  exact Real.sqrt_le_sqrt hbound

/-- The kernel correspondence is additive. -/
theorem integralKernelOperator_add_real (k k' : H₂) :
    integralKernelOperator volume (k + k') =
      integralKernelOperator volume k + integralKernelOperator volume k' := by
  unfold integralKernelOperator
  rw [map_add, map_add]

/-- The kernel correspondence is homogeneous. -/
theorem integralKernelOperator_smul_real (c : ℂ) (k : H₂) :
    integralKernelOperator volume (c • k) = c • integralKernelOperator volume k := by
  have hswap := Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))
  have h : Lp.compMeasurePreserving Prod.swap hswap (c • k) =
      c • Lp.compMeasurePreserving Prod.swap hswap k := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_compMeasurePreserving (c • k) hswap,
      Lp.coeFn_smul c (Lp.compMeasurePreserving Prod.swap hswap k),
      Lp.coeFn_compMeasurePreserving k hswap,
      hswap.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_smul c k)] with p h1 h2 h3 h4
    rw [h1, h2, Pi.smul_apply, h3]
    exact h4
  unfold integralKernelOperator
  rw [h, map_smul]

/-- The correspondence from square-integrable kernels on the plane to operators on `L²(ℝ)`, as a
continuous linear map. -/
def realKernelOperatorCLM : H₂ →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := fun k ↦ (integralKernelOperator volume k).val
      map_add' := fun k k' ↦ by
        rw [integralKernelOperator_add_real]
        rfl
      map_smul' := fun c k ↦ by
        rw [integralKernelOperator_smul_real]
        rfl }
    1 (fun k ↦ by
      rw [one_mul]
      exact norm_integralKernelOperator_le_norm k)

/-- The continuous linear map applied to a kernel is the integral operator of that kernel. -/
theorem realKernelOperatorCLM_apply (k : H₂) :
    realKernelOperatorCLM k = (integralKernelOperator volume k).val := rfl

/-! ### Measurability in the dilation parameter -/

/-- The kernel of the level is measurable in its two variables jointly. -/
theorem measurable_realPWLevelKernel (Y : ℝ) :
    Measurable fun r : ℝ × ℝ ↦ realPWLevelKernel Y r.1 r.2 := by
  have hS := (continuous_realBandKernel Y).measurable
  have hfun : (fun r : ℝ × ℝ ↦ realPWLevelKernel Y r.1 r.2) = fun r ↦
      (realBandKernel Y (r.1 - r.2) + realBandKernel Y (r.1 + r.2)) / 2 -
        realBandKernel Y r.1 * realBandKernel Y r.2 / (2 * Y) := rfl
  rw [hfun]
  exact (((hS.comp (measurable_fst.sub measurable_snd)).add
    (hS.comp (measurable_fst.add measurable_snd))).div_const 2).sub
    (((hS.comp measurable_fst).mul (hS.comp measurable_snd)).div_const (2 * Y))

private theorem measurable_dilationKernel_aux1 (L : ℝ) : Measurable fun q : ℝ × (ℝ × ℝ) ↦
    (Icc (-L) L).indicator (fun _ ↦ (1 : ℂ)) q.2.1 := by
  have hi : Measurable ((Icc (-L) L).indicator (fun _ : ℝ ↦ (1 : ℂ))) :=
    measurable_const.indicator measurableSet_Icc
  exact hi.comp (measurable_fst.comp measurable_snd)

private theorem measurable_dilationKernel_aux2 :
    Measurable fun q : ℝ × (ℝ × ℝ) ↦ q.2.1 / q.1 := by
  have h1 : Measurable fun q : ℝ × (ℝ × ℝ) ↦ q.2.1 := measurable_fst.comp measurable_snd
  have h2 : Measurable fun q : ℝ × (ℝ × ℝ) ↦ q.1 := measurable_fst
  exact h1.div h2

private theorem measurable_dilationKernel_aux3 :
    Measurable fun q : ℝ × (ℝ × ℝ) ↦ (q.2.1 / q.1, q.2.2) := by
  have h3 : Measurable fun q : ℝ × (ℝ × ℝ) ↦ q.2.2 := measurable_snd.comp measurable_snd
  exact measurable_dilationKernel_aux2.prodMk h3

private theorem measurable_dilationKernel_aux4 (Y : ℝ) :
    Measurable fun q : ℝ × (ℝ × ℝ) ↦ realPWLevelKernel Y (q.2.1 / q.1) q.2.2 := by
  have h := (measurable_realPWLevelKernel Y).comp measurable_dilationKernel_aux3
  exact h

private theorem measurable_dilationKernel_aux5 : Measurable fun q : ℝ × (ℝ × ℝ) ↦ (√q.1)⁻¹ :=
  (Real.continuous_sqrt.measurable.comp measurable_fst).inv

private theorem measurable_dilationKernel_aux6 (Y : ℝ) : Measurable fun q : ℝ × (ℝ × ℝ) ↦
    (((√q.1)⁻¹ * realPWLevelKernel Y (q.2.1 / q.1) q.2.2 : ℝ) : ℂ) := by
  have h := measurable_dilationKernel_aux5.mul (measurable_dilationKernel_aux4 Y)
  exact Complex.measurable_ofReal.comp h

private theorem measurable_dilationKernel_aux7 (Y L : ℝ) : Measurable fun q : ℝ × (ℝ × ℝ) ↦
    (Icc (-L) L).indicator (fun _ ↦ (1 : ℂ)) q.2.1 *
      (((√q.1)⁻¹ * realPWLevelKernel Y (q.2.1 / q.1) q.2.2 : ℝ) : ℂ) :=
  (measurable_dilationKernel_aux1 L).mul (measurable_dilationKernel_aux6 Y)

/-- The kernel of the cutoff dilation after the projection is measurable in the dilation and
the two variables jointly. -/
theorem measurable_realLevelDilationKernel (Y L : ℝ) :
    Measurable fun q : ℝ × (ℝ × ℝ) ↦ realLevelDilationKernel Y q.1 L q.2 :=
  measurable_dilationKernel_aux7 Y L

/-- The kernel of `M_L ∘ D_g ∘ P` as a vector of `L²` of the plane. -/
def realLevelDilationVector (Y L g : ℝ) : H₂ :=
  if hY : 0 ≤ Y then (memLp_realLevelDilationKernel hY g L).toLp (realLevelDilationKernel Y g L)
  else 0

/-- The vector is the class of the kernel `1_[-L, L] (z) g^(-1/2) q (z / g, y)`. -/
theorem coeFn_realLevelDilationVector {Y : ℝ} (hY : 0 ≤ Y) (L g : ℝ) :
    (realLevelDilationVector Y L g : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
      realLevelDilationKernel Y g L := by
  simp only [realLevelDilationVector, hY, ↓reduceDIte]
  exact MemLp.coeFn_toLp _

/-- The inner product of a fixed vector with the kernel of `M_L ∘ D_g ∘ P` is measurable in
`g`. -/
theorem measurable_inner_realLevelDilationVector {Y : ℝ} (hY : 0 ≤ Y) (L : ℝ) (h : H₂) :
    Measurable fun g : ℝ ↦ ⟪h, realLevelDilationVector Y L g⟫_ℂ := by
  have hsm : StronglyMeasurable (fun q : ℝ × (ℝ × ℝ) ↦
      conj ((h : ℝ × ℝ → ℂ) q.2) * realLevelDilationKernel Y q.1 L q.2) :=
    ((Complex.continuous_conj.measurable.comp
      ((Lp.stronglyMeasurable h).measurable.comp measurable_snd)).mul
      (measurable_realLevelDilationKernel Y L)).stronglyMeasurable
  have hint := (hsm.integral_prod_right' (ν := (volume : Measure ℝ).prod volume)).measurable
  have heq : (fun g : ℝ ↦ ⟪h, realLevelDilationVector Y L g⟫_ℂ) = fun g ↦
      ∫ p, conj ((h : ℝ × ℝ → ℂ) p) * realLevelDilationKernel Y g L p ∂(volume.prod volume) := by
    funext g
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_realLevelDilationVector hY L g] with p hp
    rw [hp, RCLike.inner_apply]
    ring
  rw [heq]
  exact hint

/-- The kernel of `M_L ∘ D_g ∘ P` is strongly measurable in `g`. -/
theorem stronglyMeasurable_realLevelDilationVector {Y : ℝ} (hY : 0 ≤ Y) (L : ℝ) :
    StronglyMeasurable (realLevelDilationVector Y L) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  have : SecondCountableTopology H₂ := Lp.SecondCountableTopology
  exact stronglyMeasurable_of_measurable_inner (measurable_inner_realLevelDilationVector hY L)

/-- The inner product of a fixed vector with a dilate is measurable in the dilation. -/
theorem measurable_inner_realDilation (h f : H) :
    Measurable fun g : ℝ ↦ ⟪h, realDilation g f⟫_ℂ := by
  have hsm : StronglyMeasurable (fun p : ℝ × ℝ ↦
      conj ((h : ℝ → ℂ) p.2) * ((((√p.1)⁻¹ : ℝ) : ℂ) * (f : ℝ → ℂ) (p.2 / p.1))) := by
    refine Measurable.stronglyMeasurable ?_
    have h1 : Measurable fun p : ℝ × ℝ ↦ (h : ℝ → ℂ) p.2 :=
      (Lp.stronglyMeasurable h).measurable.comp measurable_snd
    have h2 : Measurable fun p : ℝ × ℝ ↦ (f : ℝ → ℂ) (p.2 / p.1) :=
      (Lp.stronglyMeasurable f).measurable.comp (measurable_snd.div measurable_fst)
    have h3 : Measurable fun p : ℝ × ℝ ↦ (((√p.1)⁻¹ : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp measurable_fst).inv
    exact (Complex.continuous_conj.measurable.comp h1).mul (h3.mul h2)
  have hint := (hsm.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  have heq : (fun g : ℝ ↦ ⟪h, realDilation g f⟫_ℂ) = fun g ↦
      if 0 < g then ∫ x, conj ((h : ℝ → ℂ) x) * ((((√g)⁻¹ : ℝ) : ℂ) * (f : ℝ → ℂ) (x / g))
      else 0 := by
    funext g
    split_ifs with hg
    · rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_realDilation hg f] with x hx
      rw [hx, RCLike.inner_apply]
      ring
    · simp [realDilation, hg]
  rw [heq]
  exact Measurable.ite measurableSet_Ioi hint measurable_const

/-- The dilate of a fixed vector is strongly measurable in the dilation. -/
theorem stronglyMeasurable_realDilation (f : H) :
    StronglyMeasurable fun g : ℝ ↦ realDilation g f := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  have : SecondCountableTopology H := Lp.SecondCountableTopology
  exact stronglyMeasurable_of_measurable_inner fun h ↦ measurable_inner_realDilation h f

/-! ### A bound for the kernels -/

/-- The kernel of the level is symmetric. -/
theorem realPWLevelKernel_comm (Y u y : ℝ) :
    realPWLevelKernel Y u y = realPWLevelKernel Y y u := by
  unfold realPWLevelKernel
  rw [show u - y = -(y - u) by ring, realBandKernel_neg, add_comm u y]
  ring

/-- The band kernel is at most the width `2 Y` of the band. -/
theorem realBandKernel_le {Y : ℝ} (hY : 0 ≤ Y) (u : ℝ) : realBandKernel Y u ≤ 2 * Y := by
  unfold realBandKernel
  have h := Real.sinc_le_one (2 * π * Y * u)
  nlinarith

/-- The square integral of a row of the kernel of the level is its value on the diagonal. -/
theorem integral_realPWLevelKernel_sq {Y : ℝ} (hY : 0 < Y) (u : ℝ) :
    ∫ y, realPWLevelKernel Y u y ^ 2 = realPWLevelKernel Y u u := by
  rw [← integral_realPWLevelKernel_mul_realPWLevelKernel hY u u]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  change realPWLevelKernel Y u x ^ 2 = realPWLevelKernel Y x u * realPWLevelKernel Y u x
  rw [realPWLevelKernel_comm Y x u]
  ring

/-- The kernel of the level on the diagonal is at most `2 Y`. -/
theorem realPWLevelKernel_self_le {Y : ℝ} (hY : 0 < Y) (u : ℝ) :
    realPWLevelKernel Y u u ≤ 2 * Y := by
  unfold realPWLevelKernel
  have h1 := realBandKernel_le hY.le (u - u)
  have h2 := realBandKernel_le hY.le (u + u)
  have h3 : 0 ≤ realBandKernel Y u * realBandKernel Y u / (2 * Y) :=
    div_nonneg (mul_self_nonneg _) (by positivity)
  linarith

/-- The kernel of the level on the dilated diagonal is continuous. -/
theorem continuous_realPWLevelKernel_diag (Y g : ℝ) :
    Continuous fun z : ℝ ↦ realPWLevelKernel Y (z / g) (z / g) := by
  have hS := continuous_realBandKernel Y
  have hd : Continuous fun z : ℝ ↦ z / g := continuous_id.div_const g
  have hfun : (fun z : ℝ ↦ realPWLevelKernel Y (z / g) (z / g)) = fun z ↦
      (realBandKernel Y (z / g - z / g) + realBandKernel Y (z / g + z / g)) / 2 -
        realBandKernel Y (z / g) * realBandKernel Y (z / g) / (2 * Y) := rfl
  rw [hfun]
  exact (((hS.comp (hd.sub hd)).add (hS.comp (hd.add hd))).div_const 2).sub
    (((hS.comp hd).mul (hS.comp hd)).div_const (2 * Y))

/-- The `L²` norm of the kernel of `M_L ∘ D_g ∘ P` is bounded uniformly for `g` away from zero. -/
theorem norm_realLevelDilationVector_sq_le {Y : ℝ} (hY : 0 < Y) {L : ℝ} (hL : 0 ≤ L) {g : ℝ}
    (hg : 0 < g) : ‖realLevelDilationVector Y L g‖ ^ 2 ≤ g⁻¹ * (2 * L * (2 * Y)) := by
  have hco := coeFn_realLevelDilationVector hY.le L g
  have hmem := memLp_realLevelDilationKernel hY.le g L
  have hnorm : ((‖realLevelDilationVector Y L g‖ ^ 2 : ℝ) : ℂ) =
      ∫ p, ((‖realLevelDilationKernel Y g L p‖ ^ 2 : ℝ) : ℂ) ∂(volume.prod volume) := by
    have h1 : ⟪realLevelDilationVector Y L g, realLevelDilationVector Y L g⟫_ℂ =
        ((‖realLevelDilationVector Y L g‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [← h1, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hco] with p hp
    rw [hp, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [integral_complex_ofReal] at hnorm
  have hnorm' : ‖realLevelDilationVector Y L g‖ ^ 2 =
      ∫ p, ‖realLevelDilationKernel Y g L p‖ ^ 2 ∂(volume.prod volume) := by
    exact_mod_cast hnorm
  rw [hnorm']
  have hint : Integrable (fun p : ℝ × ℝ ↦ ‖realLevelDilationKernel Y g L p‖ ^ 2)
      (volume.prod volume) :=
    (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  rw [integral_prod _ hint]
  have hin : ∀ z : ℝ, ∫ y, ‖realLevelDilationKernel Y g L (z, y)‖ ^ 2 =
      (Icc (-L) L).indicator (fun z ↦ g⁻¹ * realPWLevelKernel Y (z / g) (z / g)) z := by
    intro z
    by_cases hz : z ∈ Icc (-L) L
    · have hpt : ∀ y : ℝ, ‖realLevelDilationKernel Y g L (z, y)‖ ^ 2 =
          g⁻¹ * realPWLevelKernel Y (z / g) y ^ 2 := fun y ↦ by
        simp only [realLevelDilationKernel, indicator_of_mem hz, one_mul, Complex.norm_real,
          Real.norm_eq_abs, sq_abs, mul_pow, inv_pow, Real.sq_sqrt hg.le]
      simp_rw [hpt]
      rw [integral_const_mul, integral_realPWLevelKernel_sq hY, indicator_of_mem hz]
    · simp [realLevelDilationKernel, hz]
  simp_rw [hin]
  rw [integral_indicator measurableSet_Icc]
  have hmono : ∫ z in Icc (-L) L, g⁻¹ * realPWLevelKernel Y (z / g) (z / g) ≤
      ∫ z in Icc (-L) L, g⁻¹ * (2 * Y) := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun z _ ↦ ?_
    · exact (continuous_const.mul
        (continuous_realPWLevelKernel_diag Y g)).continuousOn.integrableOn_Icc
    · exact integrableOn_const (by simp)
    · exact mul_le_mul_of_nonneg_left (realPWLevelKernel_self_le hY _) (inv_nonneg.mpr hg.le)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_const, smul_eq_mul]
  ring

/-! ### Integrability in the dilation parameter -/

/-- A bounded strongly measurable family, weighted by `φ(g) / g` with `φ` continuous on an
interval `[a, b]` of `(0, ∞)`, is interval integrable. -/
theorem intervalIntegrable_smul_of_bounded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc a b))
    {F : ℝ → E} (hF : StronglyMeasurable F) {C : ℝ} (hC : ∀ g ∈ Icc a b, ‖F g‖ ≤ C) :
    IntervalIntegrable (fun g ↦ ((φ g / g : ℝ) : ℂ) • F g) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hw : ContinuousOn (fun g : ℝ ↦ ((φ g / g : ℝ) : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn
      (hφ.div continuousOn_id fun g hg ↦ (ha.trans_le hg.1).ne')
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  have hmeas : AEStronglyMeasurable (fun g ↦ ((φ g / g : ℝ) : ℂ) • F g)
      (volume.restrict (Icc a b)) :=
    (hw.aestronglyMeasurable measurableSet_Icc).smul hF.aestronglyMeasurable
  have hconst : IntegrableOn (fun _ : ℝ ↦ M * C) (Icc a b) volume := integrableOn_const (by simp)
  refine Integrable.mono' hconst hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with g hg
  rw [norm_smul]
  exact mul_le_mul (hM g hg) (hC g hg) (norm_nonneg _) ((norm_nonneg _).trans (hM g hg))

/-! ### The average of the dilations -/

variable {Y L a b : ℝ} {φ : ℝ → ℝ}

/-- The weighted dilates of a vector are interval integrable. -/
theorem intervalIntegrable_smul_realDilation (ha : 0 < a) (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) (f : H) :
    IntervalIntegrable (fun g ↦ ((φ g / g : ℝ) : ℂ) • realDilation g f) volume a b :=
  intervalIntegrable_smul_of_bounded ha hab hφ (stronglyMeasurable_realDilation f) (C := ‖f‖)
    fun _ hg ↦ (norm_realDilation (ha.trans_le hg.1) f).le

/-- The weighted kernels of `M_L ∘ D_g ∘ P` are interval integrable in `L²` of the plane. -/
theorem intervalIntegrable_smul_realLevelDilationVector (hY : 0 < Y) (hL : 0 ≤ L) (ha : 0 < a)
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) :
    IntervalIntegrable (fun g ↦ ((φ g / g : ℝ) : ℂ) • realLevelDilationVector Y L g)
      volume a b :=
  intervalIntegrable_smul_of_bounded ha hab hφ (stronglyMeasurable_realLevelDilationVector hY.le L)
    (C := √(a⁻¹ * (2 * L * (2 * Y)))) fun g hg ↦ by
      have hg0 := ha.trans_le hg.1
      have h := norm_realLevelDilationVector_sq_le hY hL hg0
      have h2 : g⁻¹ * (2 * L * (2 * Y)) ≤ a⁻¹ * (2 * L * (2 * Y)) :=
        mul_le_mul_of_nonneg_right (inv_anti₀ ha hg.1) (by positivity)
      exact (le_abs_self _).trans (Real.abs_le_sqrt (h.trans h2))

/-- The average of the unitary dilations against `φ(g) dg / g` over `[a, b]`, as an operator on
`L²(ℝ)`: `A f = ∫ g in a..b, (φ g / g) • D_g f`. It is set to zero unless `0 < a ≤ b` and `φ` is
continuous on `[a, b]`. -/
def realDilationAverage (φ : ℝ → ℝ) (a b : ℝ) : H →L[ℂ] H :=
  open Classical in
  if h : 0 < a ∧ a ≤ b ∧ ContinuousOn φ (Icc a b) then
    LinearMap.mkContinuous
      { toFun := fun f ↦ ∫ g in a..b, ((φ g / g : ℝ) : ℂ) • realDilation g f
        map_add' := fun f f' ↦ by
          rw [← intervalIntegral.integral_add
            (intervalIntegrable_smul_realDilation h.1 h.2.1 h.2.2 f)
            (intervalIntegrable_smul_realDilation h.1 h.2.1 h.2.2 f')]
          refine intervalIntegral.integral_congr fun g _ ↦ ?_
          simp only [map_add, smul_add]
        map_smul' := fun c f ↦ by
          rw [RingHom.id_apply, ← intervalIntegral.integral_smul]
          refine intervalIntegral.integral_congr fun g _ ↦ ?_
          simp only [map_smul, smul_comm c] }
      (∫ g in a..b, ‖((φ g / g : ℝ) : ℂ)‖)
      (fun f ↦ by
        have hw : ContinuousOn (fun g : ℝ ↦ ‖((φ g / g : ℝ) : ℂ)‖ * ‖f‖) (Icc a b) :=
          ((Complex.continuous_ofReal.comp_continuousOn
            (h.2.2.div continuousOn_id fun g hg ↦ (h.1.trans_le hg.1).ne')).norm).mul
            continuousOn_const
        refine (intervalIntegral.norm_integral_le_integral_norm h.2.1).trans ?_
        rw [← intervalIntegral.integral_mul_const]
        refine intervalIntegral.integral_mono_on h.2.1
          (intervalIntegrable_smul_realDilation h.1 h.2.1 h.2.2 f).norm
          (hw.intervalIntegrable_of_Icc h.2.1) fun g hg ↦ ?_
        rw [norm_smul, norm_realDilation (h.1.trans_le hg.1)])
  else 0

/-- The averaged dilation applied to a vector is the integral of its weighted dilates. -/
theorem realDilationAverage_apply (ha : 0 < a) (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b))
    (f : H) :
    realDilationAverage φ a b f = ∫ g in a..b, ((φ g / g : ℝ) : ℂ) • realDilation g f := by
  simp only [realDilationAverage, ha, hab, hφ, and_self, ↓reduceDIte]
  rfl

/-- The kernel of `M_L ∘ A ∘ P`, as the integral of the kernels of `M_L ∘ D_g ∘ P`. -/
def realLevelAverageVector (Y L : ℝ) (φ : ℝ → ℝ) (a b : ℝ) : H₂ :=
  ∫ g in a..b, ((φ g / g : ℝ) : ℂ) • realLevelDilationVector Y L g

/-- The integral operator with the averaged kernel is the cutoff after the averaged dilation
after the projection onto the level. -/
theorem realKernelOperatorCLM_realLevelAverageVector (hY : 0 < Y) (hL : 0 ≤ L) (ha : 0 < a)
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) :
    realKernelOperatorCLM (realLevelAverageVector Y L φ a b) =
      realCutoff L ∘L realDilationAverage φ a b ∘L (realPWLevel Y).starProjection := by
  ext1 f
  have hint := intervalIntegrable_smul_realLevelDilationVector hY hL ha hab hφ
  have h1 : realKernelOperatorCLM (realLevelAverageVector Y L φ a b) f =
      ∫ g in a..b, ((ContinuousLinearMap.apply ℂ H f).comp realKernelOperatorCLM)
        (((φ g / g : ℝ) : ℂ) • realLevelDilationVector Y L g) := by
    rw [ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
    rfl
  rw [h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    realDilationAverage_apply ha hab hφ,
    ← ContinuousLinearMap.intervalIntegral_comp_comm (realCutoff L)
      (intervalIntegrable_smul_realDilation ha hab hφ _)]
  refine intervalIntegral.integral_congr fun g hg ↦ ?_
  rw [uIcc_of_le hab] at hg
  have hg0 := ha.trans_le hg.1
  have hk : (integralKernelOperator volume (realLevelDilationVector Y L g)).val =
      realCutoff L ∘L realDilation g ∘L (realPWLevel Y).starProjection := by
    simp only [realLevelDilationVector, hY.le, ↓reduceDIte]
    exact integralKernelOperator_realLevelDilationKernel hY hg0 L
  simp only [ContinuousLinearMap.comp_apply, map_smul, ContinuousLinearMap.apply_apply,
    realKernelOperatorCLM_apply, hk]

/-- The pairing `b ↦ ∫ k (p) b (p.swap)` against a fixed kernel is a continuous linear
functional of the kernel `b`. -/
theorem exists_kernelPairingCLM (k : H₂) :
    ∃ ℓ : H₂ →L[ℂ] ℂ, ∀ b : H₂, ℓ b = ∫ p, k p * b p.swap ∂(volume.prod volume) := by
  have hswap := Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))
  have hm : MemLp (fun p : ℝ × ℝ ↦ star ((k : ℝ × ℝ → ℂ) p.swap)) 2 (volume.prod volume) :=
    ((Lp.memLp k).comp_measurePreserving hswap).star
  refine ⟨innerSL ℂ (hm.toLp _), fun b ↦ ?_⟩
  rw [innerSL_apply_apply, L2.inner_def]
  have h1 : ∫ p, ⟪(hm.toLp _ : H₂) p, b p⟫_ℂ ∂(volume.prod volume) =
      ∫ p, (k : ℝ × ℝ → ℂ) p.swap * b p ∂(volume.prod volume) := by
    refine integral_congr_ae ?_
    filter_upwards [hm.coeFn_toLp] with p hp
    rw [hp, RCLike.inner_apply]
    rw [starRingEnd_apply, star_star]
    exact mul_comm _ _
  rw [h1]
  have h2 := hswap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding
    (fun p : ℝ × ℝ ↦ (k : ℝ × ℝ → ℂ) p.swap * b p)
  rw [← h2]
  simp only [Prod.swap_swap]

/-! ### The trace of the compression of the averaged dilation -/

/-- The compression of the cutoff averaged dilation to the level is the composite of the two
kernel operators, the second with the averaged kernel. -/
theorem realPWLevel_average_compression_eq (hY : 0 < Y) (hL : 0 ≤ L) (ha : 0 < a)
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) :
    (realPWLevel Y).starProjection ∘L realCutoff L ∘L realDilationAverage φ a b ∘L
        (realPWLevel Y).starProjection =
      (integralKernelOperator volume
        (MemLp.toLp (realLevelCutKernel Y L) (memLp_realLevelCutKernel hY.le L))).val.comp
      (integralKernelOperator volume (realLevelAverageVector Y L φ a b)).val := by
  rw [integralKernelOperator_realLevelCutKernel hY L, ← realKernelOperatorCLM_apply,
    realKernelOperatorCLM_realLevelAverageVector hY hL ha hab hφ]
  ext1 f
  simp only [ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.comp_apply (realCutoff L) (realCutoff L),
    realCutoff_comp_realCutoff]

/-- The compression of the cutoff averaged dilation to the level is nuclear. -/
theorem isNuclearOperator_realPWLevel_average_compression (hY : 0 < Y) (hL : 0 ≤ L)
    (ha : 0 < a) (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) :
    IsNuclearOperator ((realPWLevel Y).starProjection ∘L realCutoff L ∘L
      realDilationAverage φ a b ∘L (realPWLevel Y).starProjection) := by
  rw [realPWLevel_average_compression_eq hY hL ha hab hφ]
  exact nuclear_hilbertSchmidt_comp _ _

/-- **The trace of the compression of the averaged dilation.** With `A = ∫ φ(g) D_g dg / g`, the
Hilbert trace of `P ∘ M_L ∘ A ∘ P` is the average of the traces of `P ∘ M_L ∘ D_g ∘ P`. -/
theorem hilbertTrace_realPWLevel_average_compression (hY : 0 < Y) (hL : 0 ≤ L) (ha : 0 < a)
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) :
    hilbertTrace ⟨(realPWLevel Y).starProjection ∘L realCutoff L ∘L
        realDilationAverage φ a b ∘L (realPWLevel Y).starProjection,
      isNuclearOperator_realPWLevel_average_compression hY hL ha hab hφ⟩ =
      ∫ g in a..b, (φ g : ℂ) * realPWLevelCompressionTrace Y L g / (g : ℂ) := by
  have hsub : (⟨(realPWLevel Y).starProjection ∘L realCutoff L ∘L
        realDilationAverage φ a b ∘L (realPWLevel Y).starProjection,
      isNuclearOperator_realPWLevel_average_compression hY hL ha hab hφ⟩ :
        nuclearEndomorphisms H) =
      ⟨(integralKernelOperator volume
        (MemLp.toLp (realLevelCutKernel Y L) (memLp_realLevelCutKernel hY.le L))).val.comp
      (integralKernelOperator volume (realLevelAverageVector Y L φ a b)).val,
      nuclear_hilbertSchmidt_comp _ _⟩ :=
    Subtype.ext (realPWLevel_average_compression_eq hY hL ha hab hφ)
  rw [hsub, hilbertTrace_integralKernelOperator_comp]
  obtain ⟨ℓ, hℓ⟩ := exists_kernelPairingCLM
    (MemLp.toLp (realLevelCutKernel Y L) (memLp_realLevelCutKernel hY.le L))
  rw [← hℓ, realLevelAverageVector, ← ContinuousLinearMap.intervalIntegral_comp_comm ℓ
    (intervalIntegrable_smul_realLevelDilationVector hY hL ha hab hφ)]
  refine intervalIntegral.integral_congr fun g hg ↦ ?_
  rw [uIcc_of_le hab] at hg
  have hg0 := ha.trans_le hg.1
  have htr : ∫ p, (MemLp.toLp (realLevelCutKernel Y L) (memLp_realLevelCutKernel hY.le L) :
      ℝ × ℝ → ℂ) p * (realLevelDilationVector Y L g : ℝ × ℝ → ℂ) p.swap ∂(volume.prod volume) =
      realPWLevelCompressionTrace Y L g := by
    have hκ : realLevelDilationVector Y L g = MemLp.toLp (realLevelDilationKernel Y g L)
        (memLp_realLevelDilationKernel hY.le g L) := by
      simp only [realLevelDilationVector, hY.le, ↓reduceDIte]
    rw [hκ, ← hilbertTrace_integralKernelOperator_comp volume _ _
      (nuclear_hilbertSchmidt_comp _ _), realPWLevelCompressionTrace_eq hY hg0 hL,
      ← hilbertTrace_realPWLevel_compression_eq hY hg0 hL]
    congr 1
    exact Subtype.ext (realPWLevel_compression_eq hY hg0 L).symm
  change ℓ (((φ g / g : ℝ) : ℂ) • realLevelDilationVector Y L g) = _
  rw [map_smul, hℓ, htr, smul_eq_mul]
  push_cast
  ring

section Limit

variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {Ys Ls : ι → ℝ}

/-- Paper: Theorem 12.4.1.1, pp. 514–519, as used on p. 520. With `A = ∫ φ(g) D_g dg / g` the
averaged dilation, the Hilbert traces of the compressions `P ∘ M_L ∘ A ∘ P` tend, as
`Y * L → ∞`, to the real-place term of (12.5.1.1) minus `∫ φ(g) min(g^(1/2), g^(-1/2)) d×g`.
Reconstruction: the rational real-place model at order zero, with the sharp spatial cutoff and
no lower cutoff, for `φ` continuous on an interval `[a, b]` of `(0, ∞)` that does not contain
`1`. -/
theorem tendsto_hilbertTrace_realPWLevel_average_compression (ha : 0 < a) (hab : a ≤ b)
    (h1 : 1 ∉ Icc a b) (hφ : ContinuousOn φ (Icc a b)) (hY : ∀ i, 0 < Ys i)
    (hL : ∀ i, 0 ≤ Ls i) (hYL : Tendsto (fun i ↦ Ys i * Ls i) l atTop) :
    Tendsto (fun i ↦ hilbertTrace ⟨(realPWLevel (Ys i)).starProjection ∘L realCutoff (Ls i) ∘L
        realDilationAverage φ a b ∘L (realPWLevel (Ys i)).starProjection,
      isNuclearOperator_realPWLevel_average_compression (hY i) (hL i) ha hab hφ⟩) l
      (𝓝 (((∫ g in a..b, φ g * (1 / 2 * (√g / |1 - g| + √g / |1 + g|)) / g) -
        ∫ g in a..b, φ g * min (√g) (√g)⁻¹ / g : ℝ) : ℂ)) := by
  refine (tendsto_integral_realPWLevelCompressionTrace ha hab h1 hφ hY hL hYL).congr fun i ↦ ?_
  exact (hilbertTrace_realPWLevel_average_compression (hY i) (hL i) ha hab hφ).symm

end Limit

end RiemannMasullo
