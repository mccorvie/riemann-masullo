module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-! # Hilbert tensor products of complex L² spaces -/

public section

open Filter Function MeasureTheory MeasureTheory.Measure Set UniformSpace
open scoped ENNReal TensorProduct

namespace RiemannMasullo

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]

/-- A square-integrable function whose integral vanishes on every finite-measure
rectangle vanishes almost everywhere. -/
private theorem ae_zero_of_integral_rectangles (z : Lp ℂ 2 (μ.prod ν))
    (hz : ∀ s t, MeasurableSet s → MeasurableSet t → μ s < ∞ → ν t < ∞ →
      ∫ p in s ×ˢ t, z p ∂μ.prod ν = 0) : (z : X × Y → ℂ) =ᵐ[μ.prod ν] 0 := by
  have local_zero (s : Set X) (t : Set Y) (hs : MeasurableSet s) (ht : MeasurableSet t)
      (hμ : μ s < ∞) (hν : ν t < ∞) : ∀ᵐ p ∂μ.prod ν, p ∈ s ×ˢ t → z p = 0 := by
    let η := (μ.prod ν).restrict (s ×ˢ t)
    have hfin : (μ.prod ν) (s ×ˢ t) < ∞ := by rw [Measure.prod_prod]; exact ENNReal.mul_lt_top hμ hν
    let : IsFiniteMeasure η := ⟨by simpa [η] using hfin⟩
    have hint : Integrable z η := ((Lp.memLp z).restrict (s := s ×ˢ t)).integrable one_le_two
    have rect (a : Set X) (b : Set Y) (ha : MeasurableSet a) (hb : MeasurableSet b) :
        η.withDensityᵥ (z : X × Y → ℂ) (a ×ˢ b) = 0 := by
      rw [withDensityᵥ_apply hint (ha.prod hb)]
      dsimp only [η]
      rw [Measure.restrict_restrict (ha.prod hb), prod_inter_prod]
      exact hz _ _ (ha.inter hs) (hb.inter ht) ((measure_mono inter_subset_right).trans_lt hμ)
        ((measure_mono inter_subset_right).trans_lt hν)
    have hη : η.withDensityᵥ (z : X × Y → ℂ) = 0 := by
      apply VectorMeasure.ext_of_generateFrom _ _ generateFrom_prod.symm
        isPiSystem_prod
      · rw [← univ_prod_univ]
        exact rect _ _ MeasurableSet.univ MeasurableSet.univ
      · rintro _ ⟨a, ha, b, hb, rfl⟩
        exact rect a b ha hb
    have h0 := hint.ae_eq_of_withDensityᵥ_eq (integrable_zero _ ℂ η)
      (hη.trans withDensityᵥ_zero.symm)
    exact (ae_restrict_iff' (hs.prod ht)).mp h0
  have h := ae_all_iff.mpr fun n ↦ ae_all_iff.mpr fun m ↦ local_zero
    (spanningSets μ n) (spanningSets ν m) (measurableSet_spanningSets μ n) (measurableSet_spanningSets ν m)
    (measure_spanningSets_lt_top μ n) (measure_spanningSets_lt_top ν m)
  filter_upwards [h] with p hp
  obtain ⟨n, hn⟩ := iUnion_eq_univ_iff.mp (iUnion_spanningSets μ) p.1
  obtain ⟨m, hm⟩ := iUnion_eq_univ_iff.mp (iUnion_spanningSets ν) p.2
  exact hp n m ⟨hn, hm⟩

omit [SigmaFinite μ] [SigmaFinite ν] in
/-- The elementary tensor of two L² functions is their product in split variables. -/
private theorem memLp_tensorProduct (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    MemLp (fun p : X × Y ↦ f p.1 * g p.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm
    (((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving quasiMeasurePreserving_fst).mul
      ((Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving quasiMeasurePreserving_snd))).2
  simpa only [Pi.mul_apply, comp_apply, norm_mul, mul_pow] using
    ((Lp.memLp f).norm.integrable_sq.mul_prod (Lp.memLp g).norm.integrable_sq)

private noncomputable def l2ProductMap :
    Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 (μ.prod ν) := by
  let P (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) := (memLp_tensorProduct f g).toLp _
  have rep (f g) : (P f g : X × Y → ℂ) =ᵐ[μ.prod ν] fun p ↦ f p.1 * g p.2 :=
    (memLp_tensorProduct f g).coeFn_toLp
  apply TensorProduct.lift
  apply LinearMap.mk₂ ℂ P
  · intro f h g
    apply Lp.ext
    filter_upwards [rep (f + h) g, rep f g, rep h g, Lp.coeFn_add (P f g) (P h g),
      (quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae (Lp.coeFn_add f h)] with p h1 h2 h3 h4 h5
    simp only [h1, h4, Pi.add_apply, h2, h3, h5, add_mul]
  · intro c f g
    apply Lp.ext
    filter_upwards [rep (c • f) g, rep f g, Lp.coeFn_smul c (P f g),
      (quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae (Lp.coeFn_smul c f)] with p h1 h2 h3 h4
    simp only [h1, h3, Pi.smul_apply, h2, h4, smul_eq_mul, mul_assoc]
  · intro f g h
    apply Lp.ext
    filter_upwards [rep f (g + h), rep f g, rep f h, Lp.coeFn_add (P f g) (P f h),
      (quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae (Lp.coeFn_add g h)] with p h1 h2 h3 h4 h5
    simp only [h1, h4, Pi.add_apply, h2, h3, h5, mul_add]
  · intro c f g
    apply Lp.ext
    filter_upwards [rep f (c • g), rep f g, Lp.coeFn_smul c (P f g),
      (quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae (Lp.coeFn_smul c g)] with p h1 h2 h3 h4
    simp only [h1, h3, Pi.smul_apply, h2, h4, smul_eq_mul, mul_left_comm]

private theorem l2ProductMap_tmul (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    (l2ProductMap (f ⊗ₜ[ℂ] g) : X × Y → ℂ) =ᵐ[μ.prod ν] fun p ↦ f p.1 * g p.2 :=
  (memLp_tensorProduct f g).coeFn_toLp

private theorem l2ProductMap_inner (v w : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) :
    inner ℂ (l2ProductMap v) (l2ProductMap w) = inner ℂ v w := by
  induction v using TensorProduct.inductionOn with
  | add v v' hv hv' => simp [map_add, inner_add_left, hv, hv']
  | tmul f g =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp [map_add, inner_add_right, hw, hw']
    | tmul h k =>
      rw [TensorProduct.inner_tmul, L2.inner_def, L2.inner_def, L2.inner_def, ← integral_prod_mul]
      apply integral_congr_ae
      filter_upwards [l2ProductMap_tmul f g, l2ProductMap_tmul h k] with p hp hq
      simp [RCLike.inner_apply, hp, hq, mul_mul_mul_comm]

/-- The Hilbert completion of the algebraic tensor product of complex L² spaces over
σ-finite measures is isometric to L² of the product measure, by multiplication on
elementary tensors. -/
theorem exists_l2TensorProduct_isometry (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν] :
    ∃ P : Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) ≃ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν),
      ∀ (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν), (P ↑(f ⊗ₜ[ℂ] g) : X × Y → ℂ) =ᵐ[μ.prod ν] fun p ↦ f p.1 * g p.2 := by
  let L : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) :=
    { toLinearMap := l2ProductMap
      norm_map' := fun v ↦ by
        rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) (x := v), l2ProductMap_inner] }
  let P := L.fromCompletion
  have hP (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
      (P ↑(f ⊗ₜ[ℂ] g) : X × Y → ℂ) =ᵐ[μ.prod ν] fun p ↦ f p.1 * g p.2 := by
    rw [show P ↑(f ⊗ₜ[ℂ] g) = L (f ⊗ₜ[ℂ] g) from L.fromCompletion_apply_coe _]
    exact l2ProductMap_tmul f g
  have hc : IsClosed (P.toLinearMap.range : Set (Lp ℂ 2 (μ.prod ν))) := P.isometry.isClosedEmbedding.isClosed_range
  have : CompleteSpace P.toLinearMap.range := hc.completeSpace_coe
  refine ⟨LinearIsometryEquiv.ofSurjective P (LinearMap.range_eq_top.mp (Submodule.orthogonal_eq_bot_iff.mp ?_)), hP⟩
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  apply Lp.ext
  refine (ae_zero_of_integral_rectangles z ?_).trans (Lp.coeFn_zero ℂ 2 _).symm
  intro s t hs ht hμ hν
  let f := indicatorConstLp 2 hs hμ.ne (1 : ℂ)
  let g := indicatorConstLp 2 ht hν.ne (1 : ℂ)
  have ho : inner ℂ (P ↑(f ⊗ₜ[ℂ] g)) z = 0 := hz _ ⟨_, rfl⟩
  rw [L2.inner_def] at ho
  rw [← integral_indicator (hs.prod ht)]
  refine (integral_congr_ae ?_).trans ho
  have hf' : (f : X → ℂ) =ᵐ[μ] s.indicator (fun _ ↦ 1) := indicatorConstLp_coeFn
  have hg' : (g : Y → ℂ) =ᵐ[ν] t.indicator (fun _ ↦ 1) := indicatorConstLp_coeFn
  filter_upwards [hP f g, (quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hf',
    (quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hg'] with p hp hf hg
  rw [RCLike.inner_apply, hp, show f p.1 = _ from hf, show g p.2 = _ from hg]
  by_cases hs' : p.1 ∈ s <;> by_cases ht' : p.2 ∈ t <;> simp [hs', ht', Set.indicator, Set.mem_prod]

end RiemannMasullo
