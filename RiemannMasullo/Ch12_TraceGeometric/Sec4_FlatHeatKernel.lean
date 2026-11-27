module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatHeatEvaluation
public import RiemannMasullo.AppC_LCTVS.Sec3b
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# The continuous kernel of a heat-regularized positive-ray operator

The Riesz vector of Gaussian point evaluation varies continuously with the
positive radius. Its matrix coefficient represents the actual two-sided heat
compression. For a Hilbert–Schmidt operator it gives the product-L² kernel,
and for a nuclear operator the integrated continuous diagonal is the trace.
-/

open Filter MeasureTheory Set
open scoped ComplexConjugate ComplexInnerProductSpace ENNReal NNReal Topology

@[expose] public noncomputable section

namespace RiemannMasullo.FlatPolar

local notation "ν" => volume.restrict (Ioi (0 : ℝ))
local notation "H" => Lp ℂ 2 ν

/-- Riesz vector of evaluation at radius `x` after heat smoothing, with Lebesgue
normalization on the positive ray. -/
def heatKernelVector (τ : ℝ≥0) (x : ℝ) : H :=
  (Real.sqrt x)⁻¹ • logDilation (-Real.log x) (heatEvaluationVector τ)

/-- The Gaussian evaluation vector varies in Hilbert norm with the positive radius. -/
theorem continuousAt_heatKernelVector (τ : ℝ≥0) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (heatKernelVector τ) x :=
  (Real.continuous_sqrt.continuousAt.inv₀ (Real.sqrt_pos.mpr hx).ne').smul
    ((continuous_logDilation _).continuousAt.comp (Real.continuousAt_log hx.ne').neg)

/-- The Riesz vector represents point evaluation throughout the positive ray. -/
theorem inner_heatKernelVector {τ : ℝ≥0} (hτ : 0 < τ) (f : H) {x : ℝ} (hx : 0 < x) :
    ⟪heatKernelVector τ x, f⟫ = heatRepresentative τ f x := by
  rw [heatKernelVector, inner_smul_left_eq_smul, Complex.real_smul, Complex.ofReal_inv,
    heatRepresentative_eq_inner hτ f hx]
  congr 1
  let k := heatEvaluationVector τ
  have hleft : logDilation (Real.log x) (logDilation (-Real.log x) k) = k := by
    rw [logDilation_add, add_neg_cancel, logDilation_zero]
  have hright : logDilation (Real.log x) f = positiveRayDilation x hx f := by
    simp only [logDilation, Real.exp_log hx]
  exact (by simpa only [hleft, hright] using
    ((logDilation (Real.log x)).inner_map_map (logDilation (-Real.log x) k) f).symm)

/-- The kernel `K(x,y)` of `Sτ T Sτ`, with target first. -/
def heatSandwichKernel (τ : ℝ≥0) (T : H →L[ℂ] H) (p : ℝ × ℝ) : ℂ :=
  ⟪heatKernelVector τ p.1, T (heatKernelVector τ p.2)⟫

/-- The specified representative is jointly continuous at every pair of positive radii. -/
theorem continuousAt_heatSandwichKernel (τ : ℝ≥0) (T : H →L[ℂ] H)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : ContinuousAt (heatSandwichKernel τ T) (x, y) := by
  have h₁ : ContinuousAt (heatKernelVector τ ∘ Prod.fst) (x, y) :=
    (continuousAt_heatKernelVector τ hx).comp continuousAt_fst
  have h₂ : ContinuousAt (heatKernelVector τ ∘ Prod.snd) (x, y) :=
    (continuousAt_heatKernelVector τ hy).comp continuousAt_snd
  exact h₁.inner (𝕜 := ℂ) (T.continuous.continuousAt.comp h₂)

/-- The continuous kernel has an explicit bound on every positive rectangle. -/
theorem norm_heatSandwichKernel_le {τ : ℝ≥0} (hτ : 0 < τ) (T : H →L[ℂ] H) (x y : ℝ) :
    ‖heatSandwichKernel τ T (x, y)‖ ≤
      ‖T‖ * (Real.sqrt x)⁻¹ * (Real.sqrt y)⁻¹ * (2 * Real.sqrt (Real.pi * τ))⁻¹ := by
  have hv (z : ℝ) : ‖heatKernelVector τ z‖ =
      (Real.sqrt z)⁻¹ * ‖heatEvaluationVector τ‖ := by
    simp only [heatKernelVector, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
      LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖heatKernelVector τ x‖ * (‖T‖ * ‖heatKernelVector τ y‖) :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _))
    _ = _ := by
      rw [hv x, hv y, ← norm_heatEvaluationVector_sq hτ]
      ring

private theorem measurable_heatSandwichKernel (τ : ℝ≥0) (T : H →L[ℂ] H) :
    Measurable (heatSandwichKernel τ T) := by
  let : MeasurableSpace H := borel _
  have : BorelSpace H := ⟨rfl⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  have : SecondCountableTopology H := Lp.SecondCountableTopology
  have hm : Measurable (heatKernelVector τ) :=
    Real.continuous_sqrt.measurable.inv.smul
      ((continuous_logDilation _).measurable.comp Real.measurable_log.neg)
  exact continuous_inner.measurable.comp
    ((hm.comp measurable_fst).prodMk (T.continuous.measurable.comp (hm.comp measurable_snd)))

private theorem heatSandwichKernel_row {τ : ℝ≥0} (hτ : 0 < τ) (T : H →L[ℂ] H) (x : ℝ) :
    (fun y ↦ heatSandwichKernel τ T (x, y)) =ᵐ[ν]
      (fun y ↦ conj (logHeat τ (T.adjoint (heatKernelVector τ x)) y)) := by
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ))),
    logHeat_ae_eq_heatRepresentative τ (T.adjoint (heatKernelVector τ x))] with y hy hey
  change ⟪heatKernelVector τ x, T (heatKernelVector τ y)⟫ = _
  rw [hey, ← inner_heatKernelVector hτ _ hy, inner_conj_symm, T.adjoint_inner_left]

/-- Every bounded operator has the literal kernel action after two-sided heat.
At every positive target radius the indicated integral is absolutely convergent and
equals the continuous output representative. -/
theorem heatSandwichKernel_integral {τ : ℝ≥0} (hτ : 0 < τ) (T : H →L[ℂ] H)
    (f : H) {x : ℝ} (hx : 0 < x) :
    Integrable (fun y ↦ heatSandwichKernel τ T (x, y) * f y) ν ∧
      (∫ y, heatSandwichKernel τ T (x, y) * f y ∂ν) =
        heatRepresentative τ (T (logHeat τ f)) x := by
  let r := logHeat τ (T.adjoint (heatKernelVector τ x))
  have he : (fun y ↦ heatSandwichKernel τ T (x, y) * f y) =ᵐ[ν] fun y ↦ ⟪r y, f y⟫ := by
    filter_upwards [heatSandwichKernel_row hτ T x] with y hy
    rw [hy, RCLike.inner_apply']
  refine ⟨(L2.integrable_inner r f).congr he.symm, ?_⟩
  rw [integral_congr_ae he, ← L2.inner_def, ← inner_heatKernelVector hτ _ hx]
  exact ((isSelfAdjoint_logHeat τ).isSymmetric _ _).trans (T.adjoint_inner_left _ _)

/-- A countable dense family of inputs identifies the canonical Gaussian kernel with
the product-L² representative of the Hilbert–Schmidt operator. -/
private theorem heatSandwichKernel_eq_of_integralKernel {τ : ℝ≥0} (hτ : 0 < τ)
    (T : H →L[ℂ] H) (k : Lp ℂ 2 ((ν).prod ν))
    (hk : (integralKernelOperator ν k).val = (logHeat τ).comp (T.comp (logHeat τ))) :
    (k : ℝ × ℝ → ℂ) =ᵐ[(ν).prod ν] heatSandwichKernel τ T := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  have : SecondCountableTopology H := Lp.SecondCountableTopology
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq H
  let r (x : ℝ) := logHeat τ (T.adjoint (heatKernelVector τ x))
  have hact (f : H) : ∀ᵐ x ∂ν, (∫ y, k (x, y) * f y ∂ν) = ⟪r x, f⟫ := by
    filter_upwards [integralKernelOperator_apply ν k f,
      logHeat_ae_eq_heatRepresentative τ (T (logHeat τ f)),
      ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with x hkx hs hx
    rw [← hkx.2, hk, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hs,
      ← inner_heatKernelVector hτ _ hx, ← T.adjoint_inner_left]
    exact ((isSelfAdjoint_logHeat τ).isSymmetric _ _).symm
  have hrows : ∀ᵐ x ∂ν, MemLp (fun y ↦ k (x, y)) 2 ν := by
    have hsq := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable k)).mp (Lp.memLp k)
    filter_upwards [hsq.prod_right_ae] with x hrow
    exact (memLp_two_iff_integrable_sq_norm
      ((Lp.stronglyMeasurable k).comp_measurable measurable_prodMk_left).aestronglyMeasurable).mpr hrow
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (Lp.stronglyMeasurable k).measurable
    (measurable_heatSandwichKernel τ T))).mpr
  filter_upwards [hrows, ae_all_iff.2 (fun n ↦ hact (u n))] with x hrow hactx
  have hc : MemLp (fun y ↦ conj (k (x, y))) 2 ν :=
    hrow.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hrow.aestronglyMeasurable)
      (.of_forall fun _ ↦ (Complex.norm_conj _).symm)
  let v := hc.toLp (fun y ↦ conj (k (x, y)))
  have hv (n : ℕ) : ⟪v, u n⟫ = ⟪r x, u n⟫ := by
    rw [← hactx n, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hc.coeFn_toLp] with y hy
    change v y = _ at hy
    change ⟪v y, u n y⟫ = k (x, y) * u n y
    rw [RCLike.inner_apply', hy]
    simp
  have hvr : v = r x := ext_inner_right ℂ (fun g ↦
    congrFun (hu.equalizer (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
      (funext hv)) g)
  filter_upwards [hc.coeFn_toLp, heatSandwichKernel_row hτ T x] with y hy hky
  change v y = conj (k (x, y)) at hy
  rw [hvr] at hy
  have hc' : conj (r x y) = k (x, y) := by simpa only [Complex.conj_conj] using congrArg conj hy
  exact hc'.symm.trans hky.symm

private theorem nuclear_mem_hilbertSchmidt {A : H →L[ℂ] H} (hA : IsNuclearOperator A) :
    A ∈ hilbertSchmidtOperators H H := by
  obtain ⟨hcomp, hsum⟩ : IsCompactOperator A ∧
      Summable (fun n ↦ approximationNumber A n ^ (1 : ℝ)) :=
    (mem_traceClassOperators_iff_isNuclearOperator A).mpr hA
  simp only [Real.rpow_one] at hsum
  refine ⟨hcomp, Summable.of_norm_bounded_eventually_nat hsum.norm ?_⟩
  have hlim := hsum.norm.tendsto_atTop_zero.eventually (Iio_mem_nhds zero_lt_one)
  filter_upwards [hlim] with n hn
  have hn' : ‖approximationNumber A n‖ ≤ 1 := hn.le
  simpa only [Real.rpow_two, Real.norm_eq_abs, sq, abs_mul] using
    mul_le_of_le_one_left (norm_nonneg (approximationNumber A n)) hn'

/-- The continuous heat kernel of each Hilbert–Schmidt input belongs to product L²
and induces exactly the original two-sided heat composition. -/
theorem heatSandwichKernel_hilbertSchmidt {τ : ℝ≥0} (hτ : 0 < τ)
    (T : hilbertSchmidtOperators H H) :
    ∃ hk : MemLp (heatSandwichKernel τ T.val) 2 ((ν).prod ν),
      (integralKernelOperator ν (hk.toLp (heatSandwichKernel τ T.val))).val =
        (logHeat τ).comp (T.val.comp (logHeat τ)) := by
  let S := logHeat τ
  obtain ⟨_, hHS, _⟩ := tendsto_schattenNorm_comp_both T (fun _ ↦ S) S
    (fun _ ↦ tendsto_const_nhds) (fun _ ↦ isSelfAdjoint_logHeat τ) (fun _ ↦ S) S
    (fun _ ↦ tendsto_const_nhds)
  obtain ⟨k, heq⟩ := (bijective_integralKernelOperator ν).surjective ⟨_, hHS⟩
  have hk := congrArg Subtype.val heq
  have hae := heatSandwichKernel_eq_of_integralKernel hτ T.val k hk
  let hK := (Lp.memLp k).ae_eq hae
  refine ⟨hK, ?_⟩
  have hLp : hK.toLp (heatSandwichKernel τ T.val) = k :=
    Lp.ext (hK.coeFn_toLp.trans hae.symm)
  rw [hLp]
  exact hk

/-- For every fixed nuclear input the actual positive-ray two-sided heat kernel
has an integrable canonical diagonal whose Lebesgue integral is the Hilbert trace. -/
theorem heatSandwichKernel_nuclearTrace {τ : ℝ≥0} (hτ : 0 < τ) (T : nuclearEndomorphisms H) :
    ∃ (hk : MemLp (heatSandwichKernel τ T.val) 2 ((ν).prod ν))
      (hn : IsNuclearOperator ((logHeat τ).comp (T.val.comp (logHeat τ)))),
      (integralKernelOperator ν (hk.toLp (heatSandwichKernel τ T.val))).val =
        (logHeat τ).comp (T.val.comp (logHeat τ)) ∧
      Integrable (fun x ↦ heatSandwichKernel τ T.val (x, x)) ν ∧
      (∫ x, heatSandwichKernel τ T.val (x, x) ∂ν) =
        hilbertTrace ⟨(logHeat τ).comp (T.val.comp (logHeat τ)), hn⟩ := by
  obtain ⟨hk, hop⟩ := heatSandwichKernel_hilbertSchmidt hτ ⟨T.val, nuclear_mem_hilbertSchmidt T.property⟩
  have hn : IsNuclearOperator ((logHeat τ).comp (T.val.comp (logHeat τ))) :=
    mul_mem_nuclearEndomorphisms_left (logHeat τ) ⟨_, mul_mem_nuclearEndomorphisms_right (logHeat τ) T⟩
  have hnK : IsNuclearOperator (integralKernelOperator ν (hk.toLp (heatSandwichKernel τ T.val))).val :=
    hop ▸ hn
  have hcont : ∀ᵐ x ∂ν, ContinuousAt (heatSandwichKernel τ T.val) (x, x) :=
    (ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))).mono fun _ hx ↦
      continuousAt_heatSandwichKernel τ T.val hx hx
  obtain ⟨hint, htrace⟩ := hilbertTrace_integralKernelOperator_of_ae_continuous ν hk hnK hcont
  refine ⟨hk, hn, hop, hint, htrace.symm.trans ?_⟩
  exact congrArg hilbertTrace (Subtype.ext hop)

end RiemannMasullo.FlatPolar
