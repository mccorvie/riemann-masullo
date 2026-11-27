module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCompactCosineTrace
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatPolarHeat
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatNuclearHeat

/-!
# Log heat on the rational real-even mean-zero compression

Reconstruction: Theorem 12.4.1.1, pp. 516–518, after composing the actual sharp
band and compact dilation operators. This section uses the spatial and heat
sandwich estimates for the removed constant band vector.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped CompactlySupported InnerProductSpace NNReal Topology

namespace RiemannMasullo.FlatPolar

local notation "ν" => volume.restrict (Ioi (0 : ℝ))
local notation "H" => Lp ℂ 2 ν

/-- Compress the compact radial dilation operator to the actual mean-zero frequency
subspace, regarded as a nuclear endomorphism of the positive-ray Hilbert space. -/
def meanZeroCompactCosineTraceOperator (h L B : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    nuclearEndomorphisms H :=
  let P := (meanZeroFrequencyBand B).starProjection
  let A := compactCosineTraceOperator 0 B h L φ
  ⟨P.comp (A.val.comp P), mul_mem_nuclearEndomorphisms_left P
    ⟨_, mul_mem_nuclearEndomorphisms_right P A⟩⟩

/-- Both appearances of the mean-zero projection surround the ungated compact
dilation action with its physical cutoff. -/
theorem meanZeroCompactCosineTraceOperator_val (h L B : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    let P := (meanZeroFrequencyBand B).starProjection
    (meanZeroCompactCosineTraceOperator h L B φ).val =
      P.comp (((spatialCutoffInChart positiveRayInverseCosine h L).comp (compactDilationAction φ)).comp P) := by
  let P := (meanZeroFrequencyBand B).starProjection
  let E := (frequencyBand B).starProjection
  have hle : meanZeroFrequencyBand B ≤ frequencyBand B := inf_le_left
  have hPE (x : H) : P (E x) = P x := DFunLike.congr_fun
    (Submodule.starProjection_comp_starProjection_of_le hle) x
  have hEP (x : H) : E (P x) = P x := Submodule.starProjection_eq_self_iff.mpr
    (hle ((meanZeroFrequencyBand B).starProjection_apply_mem x))
  change P.comp ((compactCosineTraceOperator 0 B h L φ).val.comp P) = _
  rw [compactCosineTraceOperator_frequencyBand_eq]
  ext x : 1
  change P (E ((spatialCutoffInChart positiveRayInverseCosine h L) ((compactDilationAction φ) (E (P x))))) =
    P ((spatialCutoffInChart positiveRayInverseCosine h L) ((compactDilationAction φ) (P x)))
  rw [hPE, hEP]

/-- The heat sandwich of the canonical nuclear witness has exactly the two-sided
mean-zero compression as its middle operator. -/
theorem meanZeroCompactCosine_heat_val (h L B : ℝ) (τ : ℝ≥0) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    let P := (meanZeroFrequencyBand B).starProjection
    let T := (spatialCutoffInChart positiveRayInverseCosine h L).comp (compactDilationAction φ)
    (logHeatSandwich τ (meanZeroCompactCosineTraceOperator h L B φ)).val =
      (logHeat τ).comp ((P.comp (T.comp P)).comp (logHeat τ)) := by
  rw [logHeatSandwich_val, meanZeroCompactCosineTraceOperator_val]

private theorem compactCosine_heatDifference_val (h L B : ℝ) (τ : ℝ≥0) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    let E := (frequencyBand B).starProjection
    let P := (meanZeroFrequencyBand B).starProjection
    let T := (spatialCutoffInChart positiveRayInverseCosine h L).comp (compactDilationAction φ)
    (logHeatSandwich τ (meanZeroCompactCosineTraceOperator h L B φ) -
      logHeatSandwich τ (compactCosineTraceOperator 0 B h L φ)).val =
      (logHeat τ).comp ((P.comp (T.comp P) - E.comp (T.comp E)).comp (logHeat τ)) := by
  dsimp only
  change (logHeatSandwich τ _).val - (logHeatSandwich τ _).val = _
  rw [meanZeroCompactCosine_heat_val, logHeatSandwich_val, compactCosineTraceOperator_frequencyBand_eq]
  ext x : 1
  simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub]

/-- The difference between the canonical mean-zero and ambient nuclear heat operators
has the two explicit rank-one rows for the normalized constant band vector. -/
theorem meanZeroCompactCosine_heatDifference_eq_two_rows {B : ℝ} (hB : 0 < B) (h L : ℝ)
    (τ : ℝ≥0) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    let E := (frequencyBand B).starProjection
    let e := bandVector B
    let T := (spatialCutoffInChart positiveRayInverseCosine h L).comp (compactDilationAction φ)
    let w := ⟪e,T e⟫_ℂ • e - E (T e)
    let v := E (T.adjoint e)
    (logHeatSandwich τ (meanZeroCompactCosineTraceOperator h L B φ) -
      logHeatSandwich τ (compactCosineTraceOperator 0 B h L φ)).val =
      (innerSL ℂ (logHeat τ e)).smulRight (logHeat τ w) -
        (innerSL ℂ (logHeat τ v)).smulRight (logHeat τ e) := by
  dsimp only
  rw [compactCosine_heatDifference_val]
  simpa only [frequencyBand_starProjection_sub_line] using
    sandwich_compressionDifference_eq_two_rows (logHeat τ) _ (isSelfAdjoint_logHeat τ)
      (frequencyBand B) (norm_bandVector hB)

private theorem trace_compactCosine_sub (A D : nuclearEndomorphisms H) :
    hilbertTrace (A - D) = hilbertTrace A - hilbertTrace D := by
  obtain ⟨f, hf⟩ := hilbertTrace_linear («H» := H)
  exact (hf _).symm.trans ((map_sub f A D).trans (congrArg₂ (fun z w : ℂ ↦ z-w) (hf A) (hf D)))

/-- The norm of the actual integrated dilation action is bounded by the Haar
`L¹` norm of its radial test. -/
theorem norm_compactDilationAction_le_integral (φ : C_c(ℝ≥0ˣ, ℂ)) :
    ‖compactDilationAction φ‖ ≤ ∫ a : ℝ≥0ˣ, ‖φ a‖ ∂positiveRealHaar := by
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg (fun _ ↦ norm_nonneg _))
  intro v
  rw [compactDilationAction_apply]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  simp only [norm_smul, LinearIsometryEquiv.norm_map, integral_mul_const]

private theorem meanZero_spatial_comp_norm_le (h L : ℝ) (U : H →L[ℂ] H) :
    ‖(spatialCutoffInChart positiveRayInverseCosine h L).comp U‖ ≤ ‖U‖ := by
  let V := positiveRayInverseCosine
  have hV : ‖spatialCutoffInChart V h L‖ ≤ 1 := calc
    _ ≤ ‖V.toContinuousLinearMap.adjoint‖ * ‖(spatialCutoff h L).comp V.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (1 * 1) := by
      apply mul_le_mul _ _ (norm_nonneg _) zero_le_one
      · simpa only [ContinuousLinearMap.adjoint.norm_map] using V.norm_toContinuousLinearMap_le
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (norm_spatialCutoff_le _ _)
          V.norm_toContinuousLinearMap_le (norm_nonneg _) zero_le_one)
    _ = _ := by norm_num
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right hV (norm_nonneg U)).trans_eq (one_mul _))

/-- On dilations at least one, the polar scalar with constant gate `Q=1` is
the negative half-moment of the original compact Haar test. -/
theorem inner_bandVector_compactDilation_at_upper_support {B : ℝ} (hB : 0 < B)
    (φ : C_c(ℝ≥0ˣ, ℂ)) (hs : ∀ a ∈ tsupport φ, 1 ≤ (a.val : ℝ)) :
    ⟪bandVector B, compactDilationAction φ (bandVector B)⟫_ℂ =
      ∫ a : ℝ≥0ˣ, φ a / (Real.sqrt a.val : ℂ) ∂positiveRealHaar := by
  let Q (_ : ℝ) := (1 : ℂ)
  have hn (t : ℝ) : ‖Q t‖ ≤ 1 := by simp [Q]
  have hm : positiveRayMultiplier Q measurable_const 1 zero_le_one hn B (bandVector B) = bandVector B := by
    apply Lp.ext
    simpa only [Q, one_mul] using positiveRayMultiplier_apply Q measurable_const 1 zero_le_one hn B (bandVector B)
  have hc := hilbertTrace_compactDilation_multiplier_polar φ Q measurable_const 1 zero_le_one hn hB
  simp only [polarRankOne, hilbertTrace_smulRight, innerSL_apply_apply, ContinuousLinearMap.comp_apply, hm] at hc
  refine hc.trans (integral_congr_ae (.of_forall fun a ↦ ?_))
  by_cases hx : a ∈ tsupport φ
  · dsimp only
    rw [min_eq_left (hs a hx)]
    simp [Q, div_eq_mul_inv, Measure.real, Real.volume_Ioc]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- An error bound for the difference of the actual mean-zero and ambient heat
traces. It uses the same nuclear witness at every heat variance. -/
theorem norm_meanZeroCompactCosine_heat_trace_error {B : ℝ} (hB : 0 < B) (h L : ℝ) (τ : ℝ≥0)
    (φ : C_c(ℝ≥0ˣ, ℂ)) (hs : ∀ a ∈ tsupport φ, 1 ≤ (a.val : ℝ)) :
    ‖hilbertTrace (logHeatSandwich τ (meanZeroCompactCosineTraceOperator h L B φ)) -
      hilbertTrace (logHeatSandwich τ (compactCosineTraceOperator 0 B h L φ)) +
      (∫ a : ℝ≥0ˣ, φ a / (Real.sqrt a.val : ℂ) ∂positiveRealHaar)‖ ≤
      ‖compactDilationAction φ‖ * (2 * ‖logHeat (τ + τ) (bandVector B) - bandVector B‖ +
        ‖spatialCutoff (B*h) (B*L) (positiveRayInverseCosine (bandVector 1)) -
          positiveRayInverseCosine (bandVector 1)‖) := by
  let U := compactDilationAction φ
  let V := positiveRayInverseCosine
  let T := (spatialCutoffInChart V h L).comp U
  let S := logHeat τ
  let e := bandVector B
  let A := compactCosineTraceOperator 0 B h L φ
  let M := meanZeroCompactCosineTraceOperator h L B φ
  obtain ⟨R, hR, htr⟩ := exists_sandwich_compressionDifference S T (isSelfAdjoint_logHeat τ)
    (frequencyBand B) (norm_bandVector hB) (bandVector_mem_frequencyBand B)
  have hRM : R = logHeatSandwich τ M - logHeatSandwich τ A := by
    apply Subtype.ext
    rw [hR, frequencyBand_starProjection_sub_line]
    exact (compactCosine_heatDifference_val h L B τ φ).symm
  have hdiff : hilbertTrace (logHeatSandwich τ M) - hilbertTrace (logHeatSandwich τ A) = hilbertTrace R :=
    (trace_compactCosine_sub _ _).symm.trans (congrArg hilbertTrace hRM.symm)
  let u := U e
  let q := ‖spatialCutoff (B*h) (B*L) (V (bandVector 1)) - V (bandVector 1)‖
  have hu : ‖u‖ ≤ ‖U‖ := by
    simpa only [u, e, norm_bandVector hB, mul_one] using U.le_opNorm (bandVector B)
  have hq : ‖⟪e,T e⟫_ℂ - ⟪e,u⟫_ℂ‖ ≤ ‖U‖ * q := by
    change ‖⟪e,V.toContinuousLinearMap.adjoint _⟫_ℂ - _‖ ≤ _
    rw [V.toContinuousLinearMap.adjoint_inner_right]
    exact (norm_inner_spatialCutoff_bandVector_isometry_sub_le V B hB (by
      simpa only [inv_inv] using positiveRayInverseCosine_dilation B⁻¹ (inv_pos.mpr hB) (bandVector 1))
      h L u).trans (mul_le_mul_of_nonneg_right hu (norm_nonneg _))
  have hT : ‖T‖ ≤ ‖U‖ := meanZero_spatial_comp_norm_le h L U
  change ‖hilbertTrace (logHeatSandwich τ M) - hilbertTrace (logHeatSandwich τ A) + _‖ ≤ _
  rw [hdiff, ← inner_bandVector_compactDilation_at_upper_support hB φ hs]
  change ‖hilbertTrace R + ⟪e,u⟫_ℂ‖ ≤ _
  rw [show hilbertTrace R + ⟪e,u⟫_ℂ = (hilbertTrace R + ⟪e,T e⟫_ℂ) -
    (⟪e,T e⟫_ℂ - ⟪e,u⟫_ℂ) by abel]
  refine (norm_sub_le _ _).trans ((add_le_add (htr.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hT (by norm_num)) (norm_nonneg _))) hq).trans_eq ?_)
  simp only [logHeat_add]
  change 2 * ‖U‖ * ‖S (S e) - e‖ + ‖U‖ * q = ‖U‖ * (2 * ‖S (S e) - e‖ + q)
  ring

/-- The rank-two trace correction converges uniformly for tests with bounded integrated
dilation operator norm supported on the expanding side. -/
theorem tendstoUniformlyOn_meanZeroCompactCosine_heatDifference
    {ι : Type*} {l : Filter ι} {B h L : ι → ℝ} {τ : ι → ℝ≥0} (hB : ∀ i, 0 < B i)
    (hh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hL : Tendsto (fun i ↦ B i * L i) l atTop)
    (hτ : Tendsto τ l (𝓝 0)) {F : Set C_c(ℝ≥0ˣ, ℂ)} {C : ℝ}
    (hF : ∀ φ ∈ F, ‖compactDilationAction φ‖ ≤ C)
    (hs : ∀ φ ∈ F, ∀ a ∈ tsupport φ, 1 ≤ (a.val : ℝ)) :
    TendstoUniformlyOn (fun i φ ↦
      hilbertTrace (logHeatSandwich (τ i) (meanZeroCompactCosineTraceOperator (h i) (L i) (B i) φ)) -
      hilbertTrace (logHeatSandwich (τ i) (compactCosineTraceOperator 0 (B i) (h i) (L i) φ)))
      (fun φ ↦ -(∫ a : ℝ≥0ˣ, φ a / (Real.sqrt a.val : ℂ) ∂positiveRealHaar)) l F := by
  let v := positiveRayInverseCosine (bandVector 1)
  have ht := tendsto_logHeat_sub_bandVector
    (show Tendsto (fun i ↦ τ i + τ i) l (𝓝 0) by simpa only [zero_add] using hτ.add hτ) B hB
  have hx := tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_spatialCutoff hh hL v)
  have hε : Tendsto (fun i ↦ C * (2 * ‖logHeat (τ i + τ i) (bandVector (B i)) - bandVector (B i)‖ +
      ‖spatialCutoff (B i * h i) (B i * L i) v - v‖)) l (𝓝 0) := by
    simpa only [mul_zero, add_zero] using ((ht.const_mul 2).add hx).const_mul C
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hεpos
  filter_upwards [hε.eventually (gt_mem_nhds hεpos)] with i hi
  intro φ hφ
  rw [dist_comm, dist_eq_norm, sub_neg_eq_add]
  exact ((norm_meanZeroCompactCosine_heat_trace_error (hB i) (h i) (L i) (τ i) φ (hs φ hφ)).trans
    (mul_le_mul_of_nonneg_right (hF φ hφ) (by positivity))).trans_lt hi

/-- Uniform control of the ambient heat traces gives uniform control of the
mean-zero heat traces of the same tests after subtracting their half-moments. -/
theorem tendstoUniformlyOn_meanZeroCompactCosine_heatTrace_of_ambient
    {ι : Type*} {l : Filter ι} {B h L : ι → ℝ} {τ : ι → ℝ≥0} (hB : ∀ i, 0 < B i)
    (hh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hL : Tendsto (fun i ↦ B i * L i) l atTop)
    (hτ : Tendsto τ l (𝓝 0)) {F : Set C_c(ℝ≥0ˣ, ℂ)} {C : ℝ}
    (hF : ∀ φ ∈ F, ‖compactDilationAction φ‖ ≤ C)
    (hs : ∀ φ ∈ F, ∀ a ∈ tsupport φ, 1 ≤ (a.val : ℝ)) (c : C_c(ℝ≥0ˣ, ℂ) → ℂ)
    (hc : TendstoUniformlyOn (fun i φ ↦ hilbertTrace (logHeatSandwich (τ i)
      (compactCosineTraceOperator 0 (B i) (h i) (L i) φ))) c l F) :
    TendstoUniformlyOn (fun i φ ↦ hilbertTrace (logHeatSandwich (τ i)
      (meanZeroCompactCosineTraceOperator (h i) (L i) (B i) φ)))
      (fun φ ↦ c φ - ∫ a : ℝ≥0ˣ, φ a / (Real.sqrt a.val : ℂ) ∂positiveRealHaar) l F := by
  have hd := tendstoUniformlyOn_meanZeroCompactCosine_heatDifference hB hh hL hτ hF hs
  convert hc.add hd using 1
  funext i φ
  dsimp only [Pi.add_apply]
  abel

/-- A single ambient heat trace limit determines the trace of the explicit mean-zero
nuclear operator along the very same cutoffs and heat variances. -/
theorem tendsto_meanZeroCompactCosine_heatTrace_of_ambient
    {ι : Type*} {l : Filter ι} {B h L : ι → ℝ} {τ : ι → ℝ≥0} (hB : ∀ i, 0 < B i)
    (hh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hL : Tendsto (fun i ↦ B i * L i) l atTop)
    (hτ : Tendsto τ l (𝓝 0)) (φ : C_c(ℝ≥0ˣ, ℂ)) (hs : ∀ a ∈ tsupport φ, 1 ≤ (a.val : ℝ))
    {c : ℂ} (hc : Tendsto (fun i ↦ hilbertTrace (logHeatSandwich (τ i)
      (compactCosineTraceOperator 0 (B i) (h i) (L i) φ))) l (𝓝 c)) :
    Tendsto (fun i ↦ hilbertTrace (logHeatSandwich (τ i)
      (meanZeroCompactCosineTraceOperator (h i) (L i) (B i) φ))) l
      (𝓝 (c - ∫ a : ℝ≥0ˣ, φ a / (Real.sqrt a.val : ℂ) ∂positiveRealHaar)) := by
  have hd := (tendstoUniformlyOn_meanZeroCompactCosine_heatDifference (F := {φ})
    (C := ‖compactDilationAction φ‖) hB hh hL hτ (by intro ψ hψ; obtain rfl := Set.mem_singleton_iff.mp hψ; exact le_rfl)
    (by intro ψ hψ; obtain rfl := Set.mem_singleton_iff.mp hψ; exact hs)).tendsto_at (mem_singleton φ)
  have he (z w : ℂ) : z + (w - z) = w := by abel
  rw [sub_eq_add_neg]
  simpa only [he] using hc.add hd

/-- On a fixed upper radial window, unit sup norm gives a common Haar `L¹`
bound for all the dilation actions. -/
theorem norm_compactDilationAction_le_log_upper {a₀ a₁ : ℝ} (ha₀ : 1 ≤ a₀) (ha₁ : a₀ ≤ a₁)
    (φ : C_c(ℝ≥0ˣ, ℂ)) (hs : ∀ a ∈ tsupport φ, (a.val : ℝ) ∈ Icc a₀ a₁)
    (hn : ∀ a, ‖φ a‖ ≤ 1) : ‖compactDilationAction φ‖ ≤ Real.log a₁ := by
  have htop := ha₀.trans ha₁
  let b : ℝ≥0ˣ := Units.mk0 a₁.toNNReal (Real.toNNReal_eq_zero.not.mpr
    (not_le_of_gt (zero_lt_one.trans_le htop)))
  have hb : (b.val : ℝ) = a₁ := Real.coe_toNNReal _ (zero_le_one.trans htop)
  let W := {a : ℝ≥0ˣ | (a.val : ℝ) ∈ Icc 1 a₁}
  have hw : positiveRealHaar W = ENNReal.ofReal (Real.log a₁) := by
    simpa only [hb, W] using positiveRealHaar_interval b (hb.symm ▸ htop)
  refine (norm_compactDilationAction_le_integral φ).trans ?_
  have heq : (∫ a in W, ‖φ a‖ ∂positiveRealHaar) = ∫ a : ℝ≥0ˣ, ‖φ a‖ ∂positiveRealHaar := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro a ha
    have hz : a ∉ tsupport φ := fun ht ↦ ha ⟨ha₀.trans (hs a ht).1, (hs a ht).2⟩
    rw [image_eq_zero_of_notMem_tsupport (f := φ) hz, norm_zero]
  rw [← heq]
  have hi := norm_setIntegral_le_of_norm_le_const (μ := positiveRealHaar) (s := W) (f := fun a ↦ ‖φ a‖)
    (C := 1) (hw ▸ ENNReal.ofReal_lt_top) (fun a _ ↦ by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hn a)
  simpa only [Real.norm_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _)), one_mul,
    Measure.real, hw, ENNReal.toReal_ofReal (Real.log_nonneg htop)] using hi

/-- The conditional convergence is uniform on the sup-norm unit ball of compact
radial tests in a fixed window above one. -/
theorem tendstoUniformlyOn_meanZeroCompactCosine_heatTrace_unitBall
    {ι : Type*} {l : Filter ι} {B h L : ι → ℝ} {τ : ι → ℝ≥0} (hB : ∀ i, 0 < B i)
    (hh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hL : Tendsto (fun i ↦ B i * L i) l atTop)
    (hτ : Tendsto τ l (𝓝 0)) {a₀ a₁ : ℝ} (ha₀ : 1 < a₀) (ha₁ : a₀ ≤ a₁)
    (c : C_c(ℝ≥0ˣ, ℂ) → ℂ) :
    let F := {φ : C_c(ℝ≥0ˣ, ℂ) | (∀ a ∈ tsupport φ, (a.val : ℝ) ∈ Icc a₀ a₁) ∧ ∀ a, ‖φ a‖ ≤ 1}
    TendstoUniformlyOn (fun i φ ↦ hilbertTrace (logHeatSandwich (τ i)
      (compactCosineTraceOperator 0 (B i) (h i) (L i) φ))) c l F →
    TendstoUniformlyOn (fun i φ ↦ hilbertTrace (logHeatSandwich (τ i)
      (meanZeroCompactCosineTraceOperator (h i) (L i) (B i) φ)))
      (fun φ ↦ c φ - ∫ a : ℝ≥0ˣ, φ a / (Real.sqrt a.val : ℂ) ∂positiveRealHaar) l F := by
  intro F hc
  exact tendstoUniformlyOn_meanZeroCompactCosine_heatTrace_of_ambient (F := F) (C := Real.log a₁) hB hh hL hτ
    (fun φ hφ ↦ norm_compactDilationAction_le_log_upper ha₀.le ha₁ φ hφ.1 hφ.2)
    (fun φ hφ a ha ↦ ha₀.le.trans (hφ.1 a ha).1) c hc

end RiemannMasullo.FlatPolar
