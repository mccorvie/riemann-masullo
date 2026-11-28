module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_UpperHalflineFactorization
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Removing the lower output cutoff in Schatten norm -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology

namespace RiemannMasullo

private theorem lowerFloorLp_norm_sq {ν : Measure ℝ} (f : Lp ℂ 2 ν) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
  rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ, L2.inner_def]
  simp_rw [inner_self_eq_norm_sq_to_K]
  norm_cast

private theorem exists_lowerFloorCutoff (ν : Measure ℝ) :
    ∃ M : ℝ → Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν,
      (∀ b (f : Lp ℂ 2 ν), (M b f : ℝ → ℂ) =ᵐ[ν] (Ici b).indicator f) ∧
      ∀ f : Lp ℂ 2 ν, Tendsto (fun b ↦ M b f) atBot (𝓝 f) := by
  let e (b : ℝ) : ℝ → ℂ := (Ici b).indicator (fun _ ↦ 1)
  have he (b : ℝ) : MemLp (e b) ∞ ν := by
    have hm : Measurable (e b) := measurable_const.indicator measurableSet_Ici
    refine memLp_top_of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun x ↦ ?_)
    by_cases hx : b ≤ x <;> simp [e, hx]
  let mul := ContinuousLinearMap.mul ℂ ℂ
  let M (b : ℝ) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
    mul.holderL ν ∞ 2 2 ((he b).toLp (e b))
  have hM (b : ℝ) (f : Lp ℂ 2 ν) : (M b f : ℝ → ℂ) =ᵐ[ν] (Ici b).indicator f := by
    have hprod : (M b f : ℝ → ℂ) =ᵐ[ν] fun x ↦ ((he b).toLp (e b)) x * f x :=
      mul.coeFn_holder (r := 2) ((he b).toLp (e b)) f
    filter_upwards [hprod, (he b).coeFn_toLp] with x hp hx
    rw [hp, hx]
    by_cases hb : b ≤ x <;> simp [e, hb]
  refine ⟨M, hM, fun f ↦ ?_⟩
  have hs (b : ℝ) : ‖M b f - f‖ ^ 2 = ∫ x in Iio b, ‖f x‖ ^ 2 ∂ν := by
    rw [lowerFloorLp_norm_sq, ← integral_indicator measurableSet_Iio]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (M b f) f, hM b f] with x hd hx
    change (M b f - f) x = M b f x - f x at hd
    rw [hd, hx]
    rcases le_or_gt b x with h | h
    · simp [h, not_lt_of_ge h]
    · simp [h, not_le_of_gt h]
  have ht : Tendsto (fun b : ℝ ↦ ∫ x in Iio b, ‖f x‖ ^ 2 ∂ν) atBot (𝓝 0) :=
    tendsto_integral_Iio_zero (f := fun x ↦ ‖f x‖ ^ 2) (μ := ν) tendsto_id
  have hsqrt : Tendsto (fun b : ℝ ↦ √(∫ x in Iio b, ‖f x‖ ^ 2 ∂ν)) atBot (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp ht
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (hsqrt.congr fun b ↦ ?_)
  rw [← hs b, Real.sqrt_sq (norm_nonneg _)]

private theorem exists_lowerFloorSchattenApproximation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {p : ℝ} {hp : 1 ≤ p} {ν : Measure ℝ} (K : schattenClass E (Lp ℂ 2 ν) p hp)
    (M : ℝ → Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hM : ∀ f : Lp ℂ 2 ν, Tendsto (fun b ↦ M b f) atBot (𝓝 f)) :
    ∃ Kb : ℝ → schattenClass E (Lp ℂ 2 ν) p hp,
      (∀ b, (Kb b).val = (M b).comp K.val) ∧
      Tendsto (fun b ↦ schattenNorm (Kb b - K)) atBot (𝓝 0) := by
  have hmem (b : ℝ) : (M b).comp K.val ∈ schattenClass E (Lp ℂ 2 ν) p hp := by
    obtain ⟨_, h, _⟩ := tendsto_schattenNorm_comp_left K (fun _ ↦ M b) (M b)
      (fun _ ↦ tendsto_const_nhds)
    exact h
  let Kb (b : ℝ) : schattenClass E (Lp ℂ 2 ν) p hp := ⟨_, hmem b⟩
  refine ⟨Kb, fun _ ↦ rfl, Filter.tendsto_iff_seq_tendsto.mpr ?_⟩
  intro L hL
  let I := ContinuousLinearMap.id ℂ (Lp ℂ 2 ν)
  obtain ⟨hj, hlim, hconv⟩ := tendsto_schattenNorm_comp_left K (fun j ↦ M (L j)) I
    (fun f ↦ (hM f).comp hL)
  have hI : (⟨I.comp K.val, hlim⟩ : schattenClass E (Lp ℂ 2 ν) p hp) = K :=
    Subtype.ext (ContinuousLinearMap.id_comp _)
  rw [hI] at hconv
  exact hconv.congr fun _ ↦ rfl

/-- Lower truncation in the real output variable converges in Hilbert–Schmidt
norm for the left factor and in trace norm for the composite with the fixed
right factor. The measure in the output variable may include a Sobolev weight. -/
theorem exists_hilbertSchmidt_comp_lowerFloor
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (ν : Measure ℝ) (A : hilbertSchmidtOperators F (Lp ℂ 2 ν))
    (B : hilbertSchmidtOperators E F) :
    ∃ Ab : ℝ → hilbertSchmidtOperators F (Lp ℂ 2 ν),
      (∀ b g, ((Ab b).val g : ℝ → ℂ) =ᵐ[ν] (Ici b).indicator (A.val g)) ∧
      Tendsto (fun b ↦ schattenNorm (Ab b - A)) atBot (𝓝 0) ∧
      Tendsto (fun b ↦ schattenNorm
        ((⟨(Ab b).val.comp B.val, comp_mem_traceClass (Ab b) B⟩ :
          traceClassOperators E (Lp ℂ 2 ν)) -
          ⟨A.val.comp B.val, comp_mem_traceClass A B⟩)) atBot (𝓝 0) := by
  obtain ⟨M, hm, hstrong⟩ := exists_lowerFloorCutoff ν
  obtain ⟨Ab, hAb, hHS⟩ := exists_lowerFloorSchattenApproximation A M hstrong
  let C : traceClassOperators E (Lp ℂ 2 ν) := ⟨A.val.comp B.val, comp_mem_traceClass A B⟩
  obtain ⟨Cb, hCb, hC⟩ := exists_lowerFloorSchattenApproximation C M hstrong
  refine ⟨Ab, fun b g ↦ ?_, hHS, hC.congr fun b ↦ ?_⟩
  · rw [hAb b, ContinuousLinearMap.comp_apply]
    exact hm b (A.val g)
  · have hEq : Cb b = (⟨(Ab b).val.comp B.val, comp_mem_traceClass (Ab b) B⟩ :
        traceClassOperators E (Lp ℂ 2 ν)) := by
      apply Subtype.ext
      calc
        (Cb b).val = (M b).comp C.val := hCb b
        _ = ((M b).comp A.val).comp B.val := rfl
        _ = (Ab b).val.comp B.val :=
          congrArg (fun T : F →L[ℂ] Lp ℂ 2 ν ↦ T.comp B.val) (hAb b).symm
    rw [hEq]

/-- Paper: Theorem 12.4.1.1, p. 514 n. 2 and pp. 516–517, Step II.
In the real logarithmic convolution model, removing the lower output cutoff
converges in rectangular trace norm. The factor on the input half-line
remains fixed. -/
theorem exists_upperHalflineWeightedConvolutionFactors_lowerFloor
    (s : ℝ) (hs : 0 ≤ s) (a T : ℝ) (ρ : ℝ → ℝ) (hρm : Measurable ρ)
    (hρ : ∀ t, |ρ t| ≤ 1) (hρT : ∀ t, T < t → ρ t = 0) (q : 𝓢(ℝ, ℂ)) :
    let ν := intervalSobolevMeasure (volume : Measure ℝ) id 0 0 s
    let μ := (volume : Measure ℝ).restrict (Ici a)
    ∃ (A : hilbertSchmidtOperators (Lp ℂ 2 (volume : Measure ℝ)) (Lp ℂ 2 ν))
      (B : hilbertSchmidtOperators (Lp ℂ 2 μ) (Lp ℂ 2 (volume : Measure ℝ)))
      (Ab : ℝ → hilbertSchmidtOperators (Lp ℂ 2 (volume : Measure ℝ)) (Lp ℂ 2 ν)),
      (∀ (f : Lp ℂ 2 μ), ∀ᵐ x ∂ν,
        A.val (B.val f) x = (ρ x : ℂ) * ∫ y, q (x - y) * f y ∂μ) ∧
      (∀ b (f : Lp ℂ 2 μ), ∀ᵐ x ∂ν, (Ab b).val (B.val f) x =
        (Ici b).indicator (fun t ↦ (ρ t : ℂ) * ∫ y, q (t - y) * f y ∂μ) x) ∧
      Tendsto (fun b ↦ schattenNorm
        ((⟨(Ab b).val.comp B.val, comp_mem_traceClass (Ab b) B⟩ :
          traceClassOperators (Lp ℂ 2 μ) (Lp ℂ 2 ν)) -
          ⟨A.val.comp B.val, comp_mem_traceClass A B⟩)) atBot (𝓝 0) := by
  intro ν μ
  obtain ⟨A, B, _, hrow⟩ := exists_upperHalflineWeightedConvolutionFactors s hs a T ρ hρm hρ hρT q
  obtain ⟨Ab, hm, _, hlim⟩ := exists_hilbertSchmidt_comp_lowerFloor ν A B
  refine ⟨A, B, Ab, fun f ↦ (hrow f).mono fun _ h ↦ h.2, fun b f ↦ ?_, hlim⟩
  filter_upwards [hm b (B.val f), hrow f] with x hx hg
  refine hx.trans ?_
  by_cases h : x ∈ Ici b
  · rw [indicator_of_mem h, indicator_of_mem h]
    exact hg.2
  · rw [indicator_of_notMem h, indicator_of_notMem h]

end RiemannMasullo
