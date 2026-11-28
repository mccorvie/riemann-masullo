module

public import RiemannMasullo.AppC_LCTVS.Sec3a_part2
public import RiemannMasullo.Ch09_HardySobolev.Sec3
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.MeasureTheory.Measure.Module
import Mathlib.Tactic.Ring

/-! # Transport of the lower output cutoff to the weighted quotient -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace RiemannMasullo

section Rectangular

variable {D E F G : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- Composition with fixed bounded maps preserves each finite-rank cutoff
in the approximation numbers, with the product of their operator norms. -/
private theorem approximationNumber_rectangularSandwich_le (A : E →L[ℂ] F)
    (B : D →L[ℂ] E) (C : F →L[ℂ] G) (n : ℕ) :
    approximationNumber (C.comp (A.comp B)) n ≤ (‖C‖ * ‖B‖) * approximationNumber A n := by
  apply le_mul_of_forall_lt₀
  intro a ha b hb
  have hzero : (0 : E →L[ℂ] F).toLinearMap.rank ≤ (n : Cardinal) := by simp
  unfold approximationNumber at hb
  obtain ⟨_, ⟨S, hS, rfl⟩, herr⟩ := exists_lt_of_csInf_lt (by exact ⟨_, 0, hzero, rfl⟩) hb
  have hpre : (S.comp B).toLinearMap.rank ≤ (n : Cardinal) :=
    (LinearMap.rank_comp_le_left B.toLinearMap S.toLinearMap).trans hS
  have hpost : (C.comp (S.comp B)).toLinearMap.rank ≤ (n : Cardinal) := by
    apply Cardinal.lift_le.mp
    exact (LinearMap.lift_rank_comp_le_right (S.comp B).toLinearMap C.toLinearMap).trans
      (by simpa only [Cardinal.lift_natCast] using Cardinal.lift_le.mpr hpre)
  calc
    _ ≤ ‖C.comp (S.comp B) - C.comp (A.comp B)‖ := by
      unfold approximationNumber
      exact csInf_le ⟨0, fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _⟩ ⟨_, hpost, rfl⟩
    _ = ‖C.comp ((S - A).comp B)‖ := by
      rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    _ ≤ ‖C‖ * (‖S - A‖ * ‖B‖) :=
      (C.opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left ((S - A).opNorm_comp_le B) (norm_nonneg C))
    _ = (‖C‖ * ‖B‖) * ‖S - A‖ := by ring
    _ ≤ a * b := mul_le_mul ha.le herr.le (norm_nonneg _)
      ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans ha.le)

variable [CompleteSpace D] [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]

/-- Fixed bounded maps on either side of a rectangular trace-class operator
multiply its trace norm by at most the product of their norms. -/
private theorem schattenNorm_rectangularSandwich_le (A : traceClassOperators E F)
    (B : D →L[ℂ] E) (C : F →L[ℂ] G) :
    ∃ h : C.comp (A.val.comp B) ∈ traceClassOperators D G,
      schattenNorm (⟨C.comp (A.val.comp B), h⟩ : traceClassOperators D G) ≤
        (‖C‖ * ‖B‖) * schattenNorm A := by
  let V := C.comp (A.val.comp B)
  have hA : Summable (approximationNumber A.val) := by
    simpa only [Real.rpow_one] using A.property.2
  have hnonneg (n : ℕ) : 0 ≤ approximationNumber V n :=
    Real.sInf_nonneg fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _
  have hbound (n : ℕ) := approximationNumber_rectangularSandwich_le A.val B C n
  have hsum : Summable (approximationNumber V) :=
    (hA.mul_left (‖C‖ * ‖B‖)).of_nonneg_of_le hnonneg hbound
  have hV : V ∈ traceClassOperators D G :=
    ⟨(A.property.1.comp_clm B).clm_comp C, by simpa only [Real.rpow_one] using hsum⟩
  refine ⟨hV, ?_⟩
  simp only [schattenNorm, Real.rpow_one, div_one]
  exact (hsum.tsum_le_tsum hbound (hA.mul_left _)).trans_eq tsum_mul_left

/-- A fixed bounded restriction on the source and a fixed bounded map on
the target preserve convergence in rectangular trace norm. -/
theorem tendsto_schattenNorm_rectangularSandwich {ι : Type*} {l : Filter ι}
    (A : ι → traceClassOperators E F) (A₀ : traceClassOperators E F)
    (B : D →L[ℂ] E) (C : F →L[ℂ] G)
    (hA : Tendsto (fun i ↦ schattenNorm (A i - A₀)) l (𝓝 0)) :
    ∃ (V : ι → traceClassOperators D G) (V₀ : traceClassOperators D G),
      (∀ i, (V i).val = C.comp ((A i).val.comp B)) ∧
      V₀.val = C.comp (A₀.val.comp B) ∧
      Tendsto (fun i ↦ schattenNorm (V i - V₀)) l (𝓝 0) := by
  let R (S : traceClassOperators E F) : traceClassOperators D G :=
    ⟨C.comp (S.val.comp B), (schattenNorm_rectangularSandwich_le S B C).choose⟩
  refine ⟨fun i ↦ R (A i), R A₀, fun _ ↦ rfl, rfl, ?_⟩
  have hsub (i : ι) : R (A i) - R A₀ = R (A i - A₀) := by
    apply Subtype.ext
    change C.comp ((A i).val.comp B) - C.comp (A₀.val.comp B) =
      C.comp (((A i).val - A₀.val).comp B)
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  have hlim : Tendsto (fun i ↦ (‖C‖ * ‖B‖) * schattenNorm (A i - A₀)) l (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := ‖C‖ * ‖B‖)).mul hA
  refine squeeze_zero (fun i ↦ ?_) (fun i ↦ ?_) hlim
  · simp only [schattenNorm, Real.rpow_one, div_one]
    exact tsum_nonneg fun _ ↦ Real.sInf_nonneg fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _
  · rw [hsub i]
    exact (schattenNorm_rectangularSandwich_le (A i - A₀) B C).choose_spec

end Rectangular

/-- A fixed weighted lift with a logarithmic pullback representative
intertwines the real lower mask with its pullback on the quotient. -/
private theorem ae_eq_preimage_lowerFloor_of_weightedLift
    {X : Type*} [MeasurableSpace X] (ν : Measure ℝ) (μ : Measure X)
    (ℓ : X → ℝ) (mass : ℝ≥0∞) (hℓ : MeasurePreserving ℓ μ (mass • ν))
    (L : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) (c : X → ℂ)
    (hL : ∀ v, (L v : X → ℂ) =ᵐ[μ] fun x ↦ c x * v (ℓ x))
    (b : ℝ) (v w : Lp ℂ 2 ν)
    (hw : (w : ℝ → ℂ) =ᵐ[ν] (Ici b).indicator (v : ℝ → ℂ)) :
    (L w : X → ℂ) =ᵐ[μ] (ℓ ⁻¹' Ici b).indicator (L v : X → ℂ) := by
  have hPull := hℓ.quasiMeasurePreserving.ae_eq_comp (Measure.ae_smul_measure hw mass)
  filter_upwards [hL w, hL v, hPull] with x hx hv hwx
  change w (ℓ x) = (Ici b).indicator (v : ℝ → ℂ) (ℓ x) at hwx
  rw [hx, hwx]
  by_cases h : ℓ x ∈ Ici b
  · have hx' : x ∈ ℓ ⁻¹' Ici b := h
    rw [indicator_of_mem h, indicator_of_mem hx', hv]
  · have hx' : x ∉ ℓ ⁻¹' Ici b := h
    rw [indicator_of_notMem h, indicator_of_notMem hx', mul_zero]

/-- Paper: Theorem 12.4.1.1, p. 514 n. 2. A fixed input map and a fixed
weighted lift transport real lower-floor convergence in trace norm to
the compressed quotient cutoffs.
Deviation: The upper-cutoff operator equality is assumed before projection. -/
theorem tendsto_schattenNorm_quotientLowerFloor
    {D E X : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ν : Measure ℝ) (μ : Measure X)
    (ℓ : X → ℝ) (mass : ℝ≥0∞) (hℓ : MeasurePreserving ℓ μ (mass • ν))
    (L : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) (c : X → ℂ)
    (hL : ∀ v, (L v : X → ℂ) =ᵐ[μ] fun x ↦ c x * v (ℓ x))
    (T : ℝ → traceClassOperators E (Lp ℂ 2 ν)) (T₀ : traceClassOperators E (Lp ℂ 2 ν))
    (hMask : ∀ b v, ((T b).val v : ℝ → ℂ) =ᵐ[ν]
      (Ici b).indicator (T₀.val v : ℝ → ℂ))
    (hT : Tendsto (fun b ↦ schattenNorm (T b - T₀)) atBot (𝓝 0))
    (J : D →L[ℂ] E) (P : Lp ℂ 2 μ →L[ℂ] D) (A : D →L[ℂ] Lp ℂ 2 μ)
    (ρ : X → ℝ) (hρm : Measurable ρ) (hρ : ∀ x, |ρ x| ≤ 1)
    (hUpper : L.comp (T₀.val.comp J) = (lpCutoffMultiplier μ ρ hρm hρ).comp A) :
    let ρb (b : ℝ) : X → ℝ := (ℓ ⁻¹' Ici b).indicator ρ
    let hρbm (b : ℝ) : Measurable (ρb b) :=
      hρm.indicator (hℓ.measurable measurableSet_Ici)
    let hρb (b : ℝ) (x : X) : |ρb b x| ≤ 1 := by
      by_cases hx : x ∈ ℓ ⁻¹' Ici b
      · simpa only [ρb, indicator_of_mem hx] using hρ x
      · simp only [ρb, indicator_of_notMem hx, abs_zero, zero_le_one]
    let M (b : ℝ) := lpCutoffMultiplier μ (ρb b) (hρbm b) (hρb b)
    ∃ (K : ℝ → traceClassOperators D D) (K₀ : traceClassOperators D D),
      (∀ b, (K b).val = P.comp ((M b).comp A)) ∧
      K₀.val = P.comp ((lpCutoffMultiplier μ ρ hρm hρ).comp A) ∧
      Tendsto (fun b ↦ schattenNorm (K b - K₀)) atBot (𝓝 0) := by
  intro ρb hρbm hρb M
  obtain ⟨K, K₀, hK, hK₀, hlim⟩ :=
    tendsto_schattenNorm_rectangularSandwich T T₀ J (P.comp L) hT
  refine ⟨K, K₀, ?_, ?_, hlim⟩
  · intro b
    rw [hK b]
    change P.comp (L.comp ((T b).val.comp J)) = P.comp ((M b).comp A)
    apply congrArg (fun U : D →L[ℂ] Lp ℂ 2 μ ↦ P.comp U)
    apply ContinuousLinearMap.ext
    intro u
    change L ((T b).val (J u)) = M b (A u)
    apply Lp.ext
    have hLiftMask := ae_eq_preimage_lowerFloor_of_weightedLift
      ν μ ℓ mass hℓ L c hL b (T₀.val (J u)) ((T b).val (J u)) (hMask b (J u))
    have hUp : L (T₀.val (J u)) = lpCutoffMultiplier μ ρ hρm hρ (A u) :=
      DFunLike.congr_fun hUpper u
    rw [hUp] at hLiftMask
    have hFloor :=
      lpCutoffMultiplier_apply μ (ρb b) (hρbm b) (hρb b) (A u)
    filter_upwards [hLiftMask, hFloor, lpCutoffMultiplier_apply μ ρ hρm hρ (A u)]
      with x hx hxFloor hxUpper
    change L ((T b).val (J u)) x = M b (A u) x
    rw [hx, hxFloor]
    by_cases hm : x ∈ ℓ ⁻¹' Ici b
    · simpa only [ρb, indicator_of_mem hm] using hxUpper
    · simp only [ρb, indicator_of_notMem hm, Complex.ofReal_zero, zero_mul]
  · rw [hK₀]
    change P.comp (L.comp (T₀.val.comp J)) =
      P.comp ((lpCutoffMultiplier μ ρ hρm hρ).comp A)
    rw [hUpper]

end RiemannMasullo
