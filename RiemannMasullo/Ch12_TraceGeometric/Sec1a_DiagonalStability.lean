module

public import RiemannMasullo.Ch12_TraceGeometric.Sec1a
import RiemannMasullo.AppC_LCTVS.Sec3a_SchattenInclusion
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! # Weighted diagonals of nuclear operators

The D′ smoothing of a quotient kernel is independent of the representative and
the smoothing sequence. Trace-norm comparison then controls the entire diagonal
in weighted L¹.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology
open scoped ComplexConjugate ENNReal NNReal

namespace RiemannMasullo

private theorem ae_eq_of_forall_integral_mul_lpTop_eq {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {f g : X → ℂ} (hf : Integrable f ν) (hg : Integrable g ν)
    (h : ∀ ρ : Lp ℂ ∞ ν, (∫ x, ρ x * f x ∂ν) = ∫ x, ρ x * g x ∂ν) :
    f =ᵐ[ν] g := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq f g hf hg
  intro s hs _
  let b : X → ℂ := s.indicator (fun _ ↦ 1)
  have hb : Measurable b := measurable_const.indicator hs
  have hbLp : MemLp b ∞ ν := memLp_top_of_bound hb.aestronglyMeasurable 1 (.of_forall fun x ↦ by
    by_cases hx : x ∈ s <;> simp [b, hx])
  let ρ : Lp ℂ ∞ ν := hbLp.toLp b
  have hset (u : X → ℂ) : (∫ x, ρ x * u x ∂ν) = ∫ x in s, u x ∂ν := by
    rw [← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [hbLp.coeFn_toLp] with x hx
    change ρ x = b x at hx
    by_cases hxs : x ∈ s <;> simp [hx, b, hxs]
  exact (hset f).symm.trans ((h ρ).trans (hset g))

section WeightedDiagonal

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {μ ν : Measure G} [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts ν] [ν.InnerRegular]
  {w : G → ℝ≥0}

local notation "M[" ρ "]" => ContinuousLinearMap.holderL ν ∞ 2 2 (ContinuousLinearMap.mul ℂ ℂ) ρ

/-- Paper: Theorem 12.1.1.2(2), p. 499 and Theorem 12.4.1.1, Step III, p. 517.
On weighted Haar L², a nuclear operator has a square-integrable kernel and an L¹ diagonal. Pairing the diagonal with bounded multipliers computes localized
traces. Every D′ smoothing of a representative of the operator kernel gives
the same weighted L¹ diagonal. -/
theorem exists_kernel_and_L1Diagonal_of_nuclear
    (hw : Continuous w) (hwpos : ∀ x, 0 < w x)
    (hν : ν = μ.withDensity (fun x ↦ ↑(w x)))
    {U : ℕ → Set G} (hU : IsDPrimeSequence μ U) (hUBorel : ∀ n, MeasurableSet (U n))
    (T : nuclearEndomorphisms (Lp ℂ 2 ν)) :
    ∃ k : Lp ℂ 2 (ν.prod ν), ∃ d : Lp ℂ 1 ν,
      (integralKernelOperator ν k).val = T.val ∧
      (∀ ρ : Lp ℂ ∞ ν, (∫ x, ρ x * d x ∂ν) =
        hilbertTrace ⟨M[ρ] * T.val, mul_mem_nuclearEndomorphisms_left M[ρ] T⟩) ∧
      ∀ {k' : Lp ℂ 2 (ν.prod ν)} {κ : G × G → ℂ} {V : ℕ → Set G},
        (integralKernelOperator ν k').val = T.val → κ =ᵐ[ν.prod ν] k' →
        IsDPrimeSequence μ V → (∀ n, MeasurableSet (V n)) →
        (fun x ↦ dSequenceKernelSmoothening μ V κ (x, x)) =ᵐ[ν] (d : G → ℂ) := by
  let A : hilbertSchmidtOperators (Lp ℂ 2 ν) (Lp ℂ 2 ν) :=
    ⟨T.val, mem_hilbertSchmidtOperators_of_isNuclearOperator T.property⟩
  obtain ⟨k, hk⟩ := (bijective_integralKernelOperator ν).surjective A
  have hkv : (integralKernelOperator ν k).val = T.val := congrArg Subtype.val hk
  have hN {k' : Lp ℂ 2 (ν.prod ν)} (heq : (integralKernelOperator ν k').val = T.val) :
      IsNuclearOperator (integralKernelOperator ν k').val := by rw [heq]; exact T.property
  have hpair {k' : Lp ℂ 2 (ν.prod ν)} {κ : G × G → ℂ} {V : ℕ → Set G}
      (heq : (integralKernelOperator ν k').val = T.val) (hκ : κ =ᵐ[ν.prod ν] k')
      (hV : IsDPrimeSequence μ V) (hVBorel : ∀ n, MeasurableSet (V n)) (ρ : Lp ℂ ∞ ν) :
      (∫ x, ρ x * dSequenceKernelSmoothening μ V κ (x, x) ∂ν) =
        hilbertTrace ⟨M[ρ] * T.val, mul_mem_nuclearEndomorphisms_left M[ρ] T⟩ := by
    refine (integral_mul_dSequenceKernelSmoothening_diagonal hκ hV hVBorel hw hwpos hν
      (hN heq) ρ).2.trans (congrArg hilbertTrace (Subtype.ext ?_))
    exact congrArg (M[ρ] * ·) heq
  let δ (x : G) := dSequenceKernelSmoothening μ U (k : G × G → ℂ) (x, x)
  have hself : (k : G × G → ℂ) =ᵐ[ν.prod ν] k := Filter.EventuallyEq.rfl
  have hδ : Integrable δ ν :=
    (integral_dSequenceKernelSmoothening_diagonal hself hU hUBorel hw hwpos hν (hN hkv)).1
  have hδLp : MemLp δ 1 ν := memLp_one_iff_integrable.2 hδ
  let d : Lp ℂ 1 ν := hδLp.toLp δ
  have hd : (d : G → ℂ) =ᵐ[ν] δ := hδLp.coeFn_toLp
  have hd_pair (ρ : Lp ℂ ∞ ν) : (∫ x, ρ x * d x ∂ν) =
      hilbertTrace ⟨M[ρ] * T.val, mul_mem_nuclearEndomorphisms_left M[ρ] T⟩ := by
    refine (integral_congr_ae (hd.mono fun x hx ↦ ?_)).trans (hpair hkv hself hU hUBorel ρ)
    exact congrArg (ρ x * ·) hx
  refine ⟨k, d, hkv, hd_pair, ?_⟩
  intro k' κ V heq hκ hV hVBorel
  have hκint := (integral_dSequenceKernelSmoothening_diagonal hκ hV hVBorel hw hwpos hν
    (hN heq)).1
  exact ae_eq_of_forall_integral_mul_lpTop_eq hκint (hδ.congr hd.symm) fun ρ ↦
    (hpair heq hκ hV hVBorel ρ).trans (hd_pair ρ).symm

end WeightedDiagonal

local notation "M[" ν "," ρ "]" => ContinuousLinearMap.holderL ν ∞ 2 2 (ContinuousLinearMap.mul ℂ ℂ) ρ

private theorem exists_lpInfty_dual_phase {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {d : X → ℂ} (hd : AEStronglyMeasurable d ν) :
    ∃ ρ : Lp ℂ ∞ ν, ‖ρ‖ ≤ 1 ∧ ∀ᵐ x ∂ν, ρ x * d x = (‖d x‖ : ℂ) := by
  let phase (x : X) : ℂ := star (d x) / (‖d x‖ : ℂ)
  have hphase : AEStronglyMeasurable phase ν := by
    apply AEMeasurable.aestronglyMeasurable
    exact (Complex.continuous_conj.measurable.comp_aemeasurable hd.aemeasurable).div
      (Complex.measurable_ofReal.comp_aemeasurable hd.aemeasurable.norm)
  have hbound : ∀ᵐ x ∂ν, ‖phase x‖ ≤ 1 := .of_forall fun x ↦ by
    dsimp only [phase]
    rw [norm_div, Complex.star_def, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg (d x))]
    exact div_self_le_one _
  have hp := memLp_top_of_bound hphase 1 hbound
  let ρ : Lp ℂ ∞ ν := hp.toLp phase
  refine ⟨ρ, ?_, ?_⟩
  · rw [Lp.norm_toLp, eLpNorm_exponent_top hphase]
    simpa only [ENNReal.ofReal_one, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound hbound)
  · filter_upwards [hp.coeFn_toLp] with x hx
    change ρ x = phase x at hx
    rw [hx]
    dsimp only [phase]
    rw [div_mul_eq_mul_div, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, Complex.ofReal_pow, pow_two, mul_self_div_self]

private theorem norm_holderL_mul_le_one {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {ρ : Lp ℂ ∞ ν} (hρ : ‖ρ‖ ≤ 1) : ‖M[ν,ρ]‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [ContinuousLinearMap.holderL_apply_apply]
  calc
    _ ≤ ‖ContinuousLinearMap.mul ℂ ℂ‖ * ‖ρ‖ * ‖v‖ :=
      (ContinuousLinearMap.mul ℂ ℂ).norm_holder_apply_apply_le ρ v
    _ ≤ 1 * 1 * ‖v‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul (ContinuousLinearMap.opNorm_mul_le ℂ ℂ) hρ (norm_nonneg ρ) zero_le_one)
      (norm_nonneg v)
    _ = _ := by rw [one_mul]

private theorem integral_norm_le_traceNorm_of_mul_pairing {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {d : X → ℂ} (hd : Integrable d ν) (T : nuclearEndomorphisms (Lp ℂ 2 ν))
    (hpair : ∀ ρ : Lp ℂ ∞ ν, (∫ x, ρ x * d x ∂ν) =
      hilbertTrace ⟨M[ν,ρ] * T.val, mul_mem_nuclearEndomorphisms_left M[ν,ρ] T⟩) :
    (∫ x, ‖d x‖ ∂ν) ≤ traceNorm T := by
  obtain ⟨ρ, hρ, heq⟩ := exists_lpInfty_dual_phase hd.aestronglyMeasurable
  have hpos : 0 ≤ ∫ x, ‖d x‖ ∂ν := integral_nonneg fun x ↦ norm_nonneg (d x)
  calc
    (∫ x, ‖d x‖ ∂ν) = ‖∫ x, (‖d x‖ : ℂ) ∂ν‖ := by
      rw [integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg hpos]
    _ = ‖∫ x, ρ x * d x ∂ν‖ := congrArg norm (integral_congr_ae heq).symm
    _ = ‖hilbertTrace ⟨M[ν,ρ] * T.val, mul_mem_nuclearEndomorphisms_left M[ν,ρ] T⟩‖ :=
      congrArg norm (hpair ρ)
    _ ≤ ‖M[ν,ρ]‖ * traceNorm T :=
      (norm_hilbertTrace_le _).trans (traceNorm_mul_left_le M[ν,ρ] T)
    _ ≤ traceNorm T := mul_le_of_le_one_left ((norm_nonneg _).trans (norm_hilbertTrace_le T))
      (norm_holderL_mul_le_one hρ)

section DPrimeDiagonals

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {μ ν : Measure G} [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts ν] [ν.InnerRegular]
  {U : ℕ → Set G} {w : G → ℝ≥0}

/-- Paper: Theorem 12.1.1.2(2), p. 499. The L¹ difference of two D′-smoothed
diagonals is bounded by the trace norm of the difference of their nuclear operators. -/
theorem integral_norm_sub_dSequenceKernelSmoothening_diagonal_le_traceNorm
    {k₁ k₂ : Lp ℂ 2 (ν.prod ν)} {κ₁ κ₂ : G × G → ℂ}
    (hκ₁ : κ₁ =ᵐ[ν.prod ν] k₁) (hκ₂ : κ₂ =ᵐ[ν.prod ν] k₂)
    (hU : IsDPrimeSequence μ U) (hBorel : ∀ n, MeasurableSet (U n))
    (hw : Continuous w) (hwpos : ∀ x, 0 < w x)
    (hν : ν = μ.withDensity (fun x ↦ ↑(w x)))
    (hT₁ : IsNuclearOperator (integralKernelOperator ν k₁).val)
    (hT₂ : IsNuclearOperator (integralKernelOperator ν k₂).val) :
    let T₁ : nuclearEndomorphisms (Lp ℂ 2 ν) := ⟨(integralKernelOperator ν k₁).val, hT₁⟩
    let T₂ : nuclearEndomorphisms (Lp ℂ 2 ν) := ⟨(integralKernelOperator ν k₂).val, hT₂⟩
    (∫ x, ‖dSequenceKernelSmoothening μ U κ₁ (x, x) -
      dSequenceKernelSmoothening μ U κ₂ (x, x)‖ ∂ν) ≤ traceNorm (T₁ - T₂) := by
  intro T₁ T₂
  have hd₁ := (integral_dSequenceKernelSmoothening_diagonal hκ₁ hU hBorel hw hwpos hν hT₁).1
  have hd₂ := (integral_dSequenceKernelSmoothening_diagonal hκ₂ hU hBorel hw hwpos hν hT₂).1
  apply integral_norm_le_traceNorm_of_mul_pairing (hd₁.sub hd₂) (T₁ - T₂)
  intro ρ
  let left (T : nuclearEndomorphisms (Lp ℂ 2 ν)) : nuclearEndomorphisms (Lp ℂ 2 ν) :=
    ⟨M[ν,ρ] * T.val, mul_mem_nuclearEndomorphisms_left M[ν,ρ] T⟩
  have hleft : left T₁ - left T₂ = left (T₁ - T₂) := Subtype.ext (mul_sub ..).symm
  have hp₁ := integral_mul_dSequenceKernelSmoothening_diagonal hκ₁ hU hBorel hw hwpos hν hT₁ ρ
  have hp₂ := integral_mul_dSequenceKernelSmoothening_diagonal hκ₂ hU hBorel hw hwpos hν hT₂ ρ
  change (∫ x, ρ x * (dSequenceKernelSmoothening μ U κ₁ (x, x) -
    dSequenceKernelSmoothening μ U κ₂ (x, x)) ∂ν) = hilbertTrace (left (T₁ - T₂))
  simp_rw [mul_sub]
  rw [integral_sub hp₁.1 hp₂.1, hp₁.2, hp₂.2]
  change hilbertTrace (left T₁) - hilbertTrace (left T₂) = hilbertTrace (left (T₁ - T₂))
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := Lp ℂ 2 ν)
  simp only [← htr, ← map_sub, hleft]

end DPrimeDiagonals
end RiemannMasullo
