module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedExponentialCorrelation
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The unit vector representing the reflected polar moment -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace RiemannMasullo

local notation "e(" a ")" =>
  Set.indicator (Ici a) (fun y : ℝ ↦ Real.exp ((a - y) / 2))

local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)

private theorem memLp_normalizedHalflineExponential (a : ℝ) :
    MemLp (fun x : ℝ ↦ (e(a) x : ℂ)) 2 volume := by
  have he : Measurable (e(a)) :=
    (Real.continuous_exp.comp
      ((continuous_const.sub continuous_id).div_const 2)).measurable.indicator
      measurableSet_Ici
  apply (memLp_two_iff_integrable_sq_norm
    (Complex.measurable_ofReal.comp he).aestronglyMeasurable).2
  have hSq (x : ℝ) : ‖(e(a) x : ℂ)‖ ^ 2 = e(a) x * e(a) x := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, pow_two]
  change Integrable (fun x : ℝ ↦ ‖(e(a) x : ℂ)‖ ^ 2) volume
  simp_rw [hSq]
  simpa only [sub_zero] using integrable_normalizedHalflineExponential_mul_shift a 0

/-- The normalized right-half-line exponential as a flat complex L² class. -/
def normalizedHalflineExponentialL2 (a : ℝ) : FlatL2 :=
  (memLp_normalizedHalflineExponential a).toLp _

theorem normalizedHalflineExponentialL2_ae_eq (a : ℝ) :
    (normalizedHalflineExponentialL2 a : ℝ → ℂ) =ᵐ[volume]
      fun x ↦ (e(a) x : ℂ) :=
  (memLp_normalizedHalflineExponential a).coeFn_toLp

theorem normalizedHalflineExponentialL2_ae_zero_lt (a : ℝ) :
    ∀ᵐ x : ℝ ∂volume, x < a → normalizedHalflineExponentialL2 a x = 0 := by
  filter_upwards [normalizedHalflineExponentialL2_ae_eq a] with x hx
  intro hxa
  rw [hx, indicator_of_notMem (show x ∉ Ici a from not_le_of_gt hxa), Complex.ofReal_zero]

/-- The L² inner product against the exponential is its scalar pairing
with the almost-everywhere representative. -/
theorem normalizedHalflineExponentialL2_inner_spec (a : ℝ) (v : FlatL2) :
    Integrable (fun x ↦ (e(a) x : ℂ) * v x) ∧
      inner ℂ (normalizedHalflineExponentialL2 a) v = ∫ x, (e(a) x : ℂ) * v x := by
  let w := normalizedHalflineExponentialL2 a
  have hp : (fun x ↦ inner ℂ (w x) (v x)) =ᵐ[volume] fun x ↦ (e(a) x : ℂ) * v x := by
    filter_upwards [normalizedHalflineExponentialL2_ae_eq a] with x hx
    change w x = (e(a) x : ℂ) at hx
    rw [RCLike.inner_apply', hx, Complex.conj_ofReal]
  exact ⟨(L2.integrable_inner (𝕜 := ℂ) w v).congr hp,
    (L2.inner_def w v).trans (integral_congr_ae hp)⟩

/-- The square norm is the autocorrelation at zero. -/
theorem norm_normalizedHalflineExponentialL2 (a : ℝ) :
    ‖normalizedHalflineExponentialL2 a‖ = 1 := by
  let w := normalizedHalflineExponentialL2 a
  have h0 : (∫ x : ℝ, e(a) x * e(a) x) = 1 := by
    simpa only [sub_zero, abs_zero, neg_zero, zero_div, Real.exp_zero] using
      integral_normalizedHalflineExponential_mul_shift a 0
  have hinner : inner ℂ w w = 1 := by
    calc
      _ = ∫ x, (e(a) x : ℂ) * w x := (normalizedHalflineExponentialL2_inner_spec a w).2
      _ = ∫ x, ((e(a) x * e(a) x : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [normalizedHalflineExponentialL2_ae_eq a] with x hx
        change w x = (e(a) x : ℂ) at hx
        rw [hx, Complex.ofReal_mul]
      _ = _ := by rw [integral_complex_ofReal, h0, Complex.ofReal_one]
  change ‖w‖ = 1
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), hinner]
  norm_num

/-- On the supported subspace, pairing against the unit exponential
is the reflected exponential moment times the normalizing factor. -/
theorem normalizedHalflineExponentialL2_inner_supported (a : ℝ) (v : FlatL2)
    (hv : ∀ᵐ x : ℝ ∂volume, x < a → v x = 0) :
    Integrable (fun x ↦ (Real.exp (-x / 2) : ℂ) * v x) ∧
      inner ℂ (normalizedHalflineExponentialL2 a) v =
        (Real.exp (a / 2) : ℂ) * (∫ x, (Real.exp (-x / 2) : ℂ) * v x) := by
  let d : ℂ := Real.exp (a / 2)
  let p (x : ℝ) : ℂ := (Real.exp (-x / 2) : ℂ) * v x
  have hd : IsUnit d :=
    isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
  have hp : (fun x ↦ (e(a) x : ℂ) * v x) =ᵐ[volume] fun x ↦ d * p x := by
    filter_upwards [hv] with x hx
    by_cases hxa : x ∈ Ici a
    · rw [indicator_of_mem hxa, show (a - x) / 2 = a / 2 + -x / 2 by ring, Real.exp_add,
        Complex.ofReal_mul]
      exact mul_assoc _ _ _
    · simp only [p, hx (lt_of_not_ge hxa), mul_zero]
  obtain ⟨hi, h⟩ := normalizedHalflineExponentialL2_inner_spec a v
  refine ⟨(integrable_const_mul_iff hd p).mp (hi.congr hp), h.trans ?_⟩
  rw [integral_congr_ae hp, integral_const_mul]

/-- If the image of the polar subspace in an isometric full-band model is
orthogonal to a unit vector, the unit preimage spans the polar complement
as soon as that image is the entire hyperplane in the full range. -/
theorem existsUnique_unit_preimage_span_orthogonalComplement
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (Vfull Vpolar : Submodule ℂ H) (hLe : Vpolar ≤ Vfull)
    (T : H →L[ℂ] G) (hIso : ∀ w ∈ Vfull, ‖T w‖ = ‖w‖)
    (e : G) (heNorm : ‖e‖ = 1)
    (he : e ∈ Set.range (fun w : Vfull ↦ T w.val))
    (hPolar : Set.range (fun w : Vpolar ↦ T w.val) =
      {y : G | y ∈ Set.range (fun w : Vfull ↦ T w.val) ∧ ⟪e, y⟫_ℂ = 0}) :
    ∃! u : Vfull, T u.val = e ∧ ‖u.val‖ = 1 ∧ Vfull ⊓ Vpolarᗮ = ℂ ∙ u.val := by
  let I : Vfull →ₗᵢ[ℂ] G :=
    ⟨(T.comp Vfull.subtypeL).toLinearMap, fun w ↦ hIso w.val w.property⟩
  obtain ⟨u, hu⟩ := he
  change T u.val = e at hu
  have huNorm : ‖u.val‖ = 1 := by
    rw [← hIso u.val u.property, hu, heNorm]
  have hMem (w : H) (hw : w ∈ Vfull) : w ∈ Vpolar ↔ ⟪(u : H), w⟫_ℂ = 0 := by
    have hInner : ⟪e, T w⟫_ℂ = ⟪(u : H), w⟫_ℂ := by
      rw [← hu]
      exact I.inner_map_map u ⟨w, hw⟩
    rw [← hInner]
    constructor
    · intro hwPolar
      have hRange : T w ∈ Set.range (fun v : Vpolar ↦ T v.val) := ⟨⟨w, hwPolar⟩, rfl⟩
      rw [hPolar] at hRange
      exact hRange.2
    · intro hzero
      have hRange : T w ∈ Set.range (fun v : Vpolar ↦ T v.val) := by
        rw [hPolar]
        exact ⟨⟨⟨w, hw⟩, rfl⟩, hzero⟩
      obtain ⟨v, hv⟩ := hRange
      have heq : (⟨v.val, hLe v.property⟩ : Vfull) = ⟨w, hw⟩ := I.injective hv
      have hval : v.val = w := congrArg Subtype.val heq
      rw [← hval]
      exact v.property
  have huOrth : u.val ∈ Vpolarᗮ :=
    (Vpolar.mem_orthogonal' u.val).2 fun w hw ↦ (hMem w (hLe hw)).1 hw
  have hComplement : Vfull ⊓ Vpolarᗮ = ℂ ∙ u.val := by
    apply le_antisymm
    · intro w hw
      let c := ⟪(u : H), w⟫_ℂ
      have hDiffFull : w - c • u.val ∈ Vfull :=
        Vfull.sub_mem hw.1 (Vfull.smul_mem c u.property)
      have huInner : ⟪(u : H), (u : H)⟫_ℂ = 1 := by
        simp [inner_self_eq_norm_sq_to_K, huNorm]
      have hDiffPolar : w - c • u.val ∈ Vpolar := (hMem _ hDiffFull).2 (by
        rw [inner_sub_right, inner_smul_right, huInner, mul_one]
        exact sub_self c)
      have hDiffOrth : w - c • u.val ∈ Vpolarᗮ :=
        Vpolarᗮ.sub_mem hw.2 (Vpolarᗮ.smul_mem c huOrth)
      have hDiffZero : w - c • u.val = 0 :=
        inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hDiffPolar hDiffOrth)
      exact Submodule.mem_span_singleton.mpr ⟨c, (sub_eq_zero.mp hDiffZero).symm⟩
    · apply Submodule.span_le.mpr
      intro w hw
      have heq : w = u.val := Set.mem_singleton_iff.mp hw
      subst w
      exact ⟨u.property, huOrth⟩
  refine ⟨u, ⟨hu, huNorm, hComplement⟩, ?_⟩
  intro w hw
  exact I.injective (hw.1.trans hu.symm)

end RiemannMasullo
