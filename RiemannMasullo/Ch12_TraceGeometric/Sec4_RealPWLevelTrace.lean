module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWTestTrace
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWJetTrials
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The real-place trace of a test function on the level of functions vanishing at the origin

Paper: Theorem 12.4.1.1, pp. 514–517, the real term, in the fixed-bandwidth model of the real
place of `ℚ` of #7354, on the level of Definition 11.2.1.1.

`Sec4_RealPWTestTrace` computes the limit of the trace of the cutoff of the action of a test
function `ψ` of the dilation on the whole weighted even band. For `0 ≤ α < 1 / 2` the level of
the model, the closure of the polar-free core, is the smaller space of band vectors that vanish
at the origin (#7770). This file computes the trace on that level.

* `realPWZeroLevel` is the level, as the orthogonal complement of the evaluation vector at the
  origin.
* `exists_realPWTestCutoff_level_nuclear`. The cutoff action, projected onto the level on both
  sides, is nuclear. Its trace is the trace on the whole band minus the diagonal entry of the
  cutoff action at the normalized evaluation vector at the origin.
  `exists_realPWTestCutoff_compl_nuclear` is the same statement for the orthogonal complement
  of any band vector.
* `tendsto_realPWZeroLevelCorrection`. As the cutoff is removed that entry tends to the
  integral of `ψ g g ^ (-1/2)`. `tendsto_realPWTestCorrection` is the statement for any band
  vector whose pairing with its own contractions is known.
* `exists_realPWTestCutoff_level_trace_limit`. So the traces on the level converge to the limit
  on the whole band minus that integral. By `realPWSharpTraceLimit_sub_of_lt_half` the
  integrand of the difference is `ψ g g ^ (-1/2) g ^ (-2) / (1 - g ^ (-2))`, the limit for one
  dilation with one even jet removed.

The limit of the entry rests on `integral_star_evaluationVector_zero_mul_dilate`: for `g > 1`
the contraction `x ↦ f (g⁻¹ x)` of a band vector pairs with the evaluation vector at the origin
as a band vector does. The contraction is not shown to be a band vector. It is cut off by the
smoothed masks of `Sec4_RealPWSmoothedAction`, for which the product is one, and the masks are
then removed (`exists_realPWBand_maskedDilate`).

Reconstruction: The paper does not state this. The operator is stated on the whole band, as
`P₀ T P₀` with `P₀` the orthogonal projection onto the level. On the level it is the
compression of the cutoff action, and it is zero on the orthogonal complement, so its trace is
the trace of the compression.

Not treated here: test functions whose support meets `g = 1` or `g < 1`. The comparison with
the adelic operator of the paper. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology InnerProductSpace

namespace RiemannMasullo.Isolated

section Level

variable (Y α s : ℝ) (hs : 0 ≤ s)

local notation "μw" => realPWIntervalMeasure α s
local notation "hμw" => volume_le_realPWIntervalMeasure α s hs
local notation "V" => RealPWBand.space Y hμw
local notation "ev" => RealPWBand.evaluation Y hμw
local notation "evv" => RealPWBand.evaluationVector Y hμw

/-- The level of the model: the band vectors that vanish at the origin, as the orthogonal
complement of the evaluation vector at the origin. -/
def realPWZeroLevel : Submodule ℂ V := (ℂ ∙ evv 0)ᗮ

/-- A band vector is in the level exactly when it vanishes at the origin. -/
theorem mem_realPWZeroLevel_iff (f : V) : f ∈ realPWZeroLevel Y α s hs ↔ ev 0 f = 0 := by
  rw [realPWZeroLevel, Submodule.mem_orthogonal_singleton_iff_inner_right,
    ← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]

/-- The level has an orthogonal projection. -/
instance realPWZeroLevel.instHasOrthogonalProjection :
    (realPWZeroLevel Y α s hs).HasOrthogonalProjection := by
  unfold realPWZeroLevel
  infer_instance

/-- The orthogonal projection onto the level subtracts the multiple of the evaluation vector
at the origin that carries the value at the origin. -/
theorem realPWZeroLevel_starProjection_apply (f : V) :
    (realPWZeroLevel Y α s hs).starProjection f =
      f - (ev 0 f / ((‖evv 0‖ ^ 2 : ℝ) : ℂ)) • evv 0 := by
  have h : (realPWZeroLevel Y α s hs).starProjection f =
      f - (ℂ ∙ evv 0).starProjection f := Submodule.starProjection_orthogonal_val f
  rw [h, Submodule.starProjection_singleton, ← InnerProductSpace.toDual_apply_apply,
    RealPWBand.toDual_evaluationVector]
  rfl

/-- The diagonal entry of the cutoff of the action of `ψ` at a band vector `e`, before division
by the square of its norm. -/
def realPWTestCorrection (e : V) (ψ : ℝ → ℂ) (L : ℝ) : ℂ :=
  ∫ x, sharpIntervalMask L x * (star (ev x e) *
    ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) e)) ∂μw

/-- The diagonal entry of the cutoff of the action of `ψ` at the evaluation vector at the
origin, before division by the square of its norm. -/
def realPWZeroLevelCorrection (ψ : ℝ → ℂ) (L : ℝ) : ℂ :=
  realPWTestCorrection Y α s hs (evv 0) ψ L

/-- The orthogonal projection onto the complement of a vector subtracts the component along
it. -/
private theorem starProjection_orthogonal_singleton_apply (e f : V) :
    (ℂ ∙ e)ᗮ.starProjection f = f - (⟪e, f⟫_ℂ / ((‖e‖ ^ 2 : ℝ) : ℂ)) • e := by
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton]
  rfl

/-- The sharp mask is real. -/
private theorem star_mask (L x : ℝ) : star (sharpIntervalMask L x) = sharpIntervalMask L x := by
  by_cases h : x ∈ Icc (-L) L <;> simp [sharpIntervalMask, h]

/-- Reconstruction: the cutoff of the action of `ψ`, projected on both sides onto the
orthogonal complement of a band vector `e`, is nuclear. Its trace is the trace on the whole
band minus the diagonal entry at the normalized vector. On the complement this operator is the
compression of the cutoff action, and it vanishes on the line of `e`. -/
theorem exists_realPWTestCutoff_compl_nuclear (hY : 0 < Y) (ha : 0 ≤ α) {a b : ℝ}
    (ha1 : 1 ≤ a) (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) (L : ℝ)
    (e : V) :
    ∃ T : nuclearEndomorphisms V,
      (∀ f : V, ∃ r : Lp ℂ 2 μw,
        (∀ᵐ x ∂μw, r x = sharpIntervalMask L x *
          ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev (g⁻¹ * x) ((ℂ ∙ e)ᗮ.starProjection f))) ∧
        T.val f = (ℂ ∙ e)ᗮ.starProjection ((V).orthogonalProjectionOnto r)) ∧
      hilbertTrace T = (∫ g, ψ g * realPWSharpTrace Y α s hs g L) -
        (((‖e‖ ^ 2 : ℝ) : ℂ))⁻¹ * realPWTestCorrection Y α s hs e ψ L := by
  have hμac := realPWIntervalMeasure_absolutelyContinuous α s
  let P : V →L[ℂ] V := (ℂ ∙ e)ᗮ.starProjection
  let U : ℝ → V := realPWTestLeftFamily Y α s hs L
  let R : ℝ → V := realPWTestRightFamily Y α s hs ψ L
  have hU : MemLp U 2 μw := memLp_realPWTestLeftFamily Y α s hs hY.le ha L
  have hR : MemLp R 2 μw := memLp_realPWTestRightFamily Y α s hs hY.le ha ha1 hψc hψ0 L
  have hU' : MemLp (fun x ↦ P (U x)) 2 μw := P.comp_memLp' hU
  have hR' : MemLp (fun x ↦ P (R x)) 2 μw := P.comp_memLp' hR
  obtain ⟨ι, bs, _⟩ := exists_hilbertBasis ℂ V
  have := RealPWBand.countable_hilbertBasis Y hμw hμac bs
  let A := hilbertFamilyAnalysisCLM hU
  let B := hilbertFamilyAnalysisCLM hR
  let A' := hilbertFamilyAnalysisCLM hU'
  let B' := hilbertFamilyAnalysisCLM hR'
  have hA (f : V) : A f =ᵐ[μw] fun x ↦ ⟪U x, f⟫_ℂ := hilbertFamilyAnalysisCLM_apply_ae hU f
  have hB (f : V) : B f =ᵐ[μw] fun x ↦ ⟪R x, f⟫_ℂ := hilbertFamilyAnalysisCLM_apply_ae hR f
  have hA' (f : V) : A' f =ᵐ[μw] fun x ↦ ⟪P (U x), f⟫_ℂ :=
    hilbertFamilyAnalysisCLM_apply_ae hU' f
  have hB' (f : V) : B' f =ᵐ[μw] fun x ↦ ⟪P (R x), f⟫_ℂ :=
    hilbertFamilyAnalysisCLM_apply_ae hR' f
  have hAP (z : V) : A' z = A (P z) := by
    apply Lp.ext
    filter_upwards [hA' z, hA (P z)] with x h1 h2
    rw [h1, h2]
    exact Submodule.inner_starProjection_left_eq_right _ _ _
  have hBP (f : V) : B' f = B (P f) := by
    apply Lp.ext
    filter_upwards [hB' f, hB (P f)] with x h1 h2
    rw [h1, h2]
    exact Submodule.inner_starProjection_left_eq_right _ _ _
  let Ah : hilbertSchmidtOperators V (Lp ℂ 2 μw) :=
    ⟨A', familyAnalysis_mem_hilbertSchmidtOperators bs hU' A' hA'⟩
  let Bh : hilbertSchmidtOperators V (Lp ℂ 2 μw) :=
    ⟨B', familyAnalysis_mem_hilbertSchmidtOperators bs hR' B' hB'⟩
  have hn : IsNuclearOperator (A'.adjoint.comp B') :=
    nuclear_hilbertSchmidt_comp ⟨_, mem_hilbertSchmidtOperators_adjoint Ah.property⟩ Bh
  have htrace := hilbertTrace_familyAnalysisProduct bs (fun x ↦ P (U x)) (fun x ↦ P (R x))
    Ah Bh (fun i ↦ hA' (bs i)) (fun i ↦ hB' (bs i))
  refine ⟨⟨_, hn⟩, fun f ↦ ⟨B (P f), ?_, ?_⟩, htrace.trans ?_⟩
  · filter_upwards [hB (P f)] with x hx
    rw [hx]
    exact inner_realPWTestRightFamily_eq Y α s hs hY.le ha ha1 hψc hψ0 L x (P f)
  · change A'.adjoint (B' f) = P ((V).orthogonalProjectionOnto (B (P f)))
    rw [← realPWTest_adjoint_analysis_apply Y α s hs hY.le ha ha1 hψc hψ0 L hU hR (P f)]
    apply ext_inner_left ℂ
    intro z
    rw [A'.adjoint_inner_right, hAP, hBP,
      ← Submodule.inner_starProjection_left_eq_right, A.adjoint_inner_right]
  · -- the trace
    let N : ℂ := ((‖e‖ ^ 2 : ℝ) : ℂ)
    let F₂ : ℝ → ℂ := fun x ↦ sharpIntervalMask L x * (star (ev x (e)) *
      ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) (e)))
    have hRE (x : ℝ) : ⟪R x, e⟫_ℂ = sharpIntervalMask L x *
        ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) (e)) :=
      inner_realPWTestRightFamily_eq Y α s hs hY.le ha ha1 hψc hψ0 L x (e)
    have hUE (x : ℝ) : ⟪e, U x⟫_ℂ = sharpIntervalMask L x * star (ev x e) := by
      change ⟪e, sharpIntervalMask L x • evv x⟫_ℂ = _
      rw [inner_smul_right]
      congr 1
      have h2 : ev x e = ⟪evv x, e⟫_ℂ := by
        rw [← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]
      rw [h2, ← inner_conj_symm, starRingEnd_apply]
    have hpt (x : ℝ) : ⟪P (R x), P (U x)⟫_ℂ = ⟪R x, U x⟫_ℂ - N⁻¹ * F₂ x := by
      have hPP : P (P (U x)) = P (U x) :=
        Submodule.starProjection_eq_self_iff.mpr
          ((ℂ ∙ e)ᗮ.orthogonalProjectionOnto (U x)).2
      rw [Submodule.inner_starProjection_left_eq_right, hPP]
      change ⟪R x, (ℂ ∙ e)ᗮ.starProjection (U x)⟫_ℂ = _
      rw [starProjection_orthogonal_singleton_apply Y α s hs, inner_sub_right,
        inner_smul_right, hRE, hUE]
      change _ = _ - N⁻¹ * (sharpIntervalMask L x * (star (ev x e) *
        ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) e)))
      rw [div_eq_mul_inv]
      linear_combination (N⁻¹ * star (ev x e) *
        ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) e)) *
          (sharpIntervalMask_mul_self L x).symm
    have hF₁ : Integrable (fun x ↦ ⟪R x, U x⟫_ℂ) μw :=
      (L2.integrable_inner (𝕜 := ℂ) (hR.toLp _) (hU.toLp _)).congr (by
        filter_upwards [hR.coeFn_toLp, hU.coeFn_toLp] with x hx hy
        rw [hx, hy])
    have hF₂ : Integrable F₂ μw := by
      refine (L2.integrable_inner (𝕜 := ℂ) (A (e)) (B (e))).congr ?_
      filter_upwards [hA (e), hB (e)] with x h1 h2
      rw [h1, h2, hRE]
      have hUz : ⟪U x, e⟫_ℂ = star (sharpIntervalMask L x) * ev x (e) := by
        change ⟪sharpIntervalMask L x • evv x, e⟫_ℂ = _
        rw [inner_smul_left, starRingEnd_apply, ← InnerProductSpace.toDual_apply_apply,
          RealPWBand.toDual_evaluationVector]
      rw [hUz, star_mask]
      simp only [RCLike.inner_apply, starRingEnd_apply, star_mul', star_mask]
      change _ = sharpIntervalMask L x * (star (ev x (e)) *
        ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) (e)))
      linear_combination (star (ev x (e)) *
        ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev (g⁻¹ * x) (e))) *
          sharpIntervalMask_mul_self L x
    calc ∫ x, ⟪P (R x), P (U x)⟫_ℂ ∂μw = ∫ x, (⟪R x, U x⟫_ℂ - N⁻¹ * F₂ x) ∂μw :=
          integral_congr_ae (ae_of_all _ hpt)
      _ = (∫ x, ⟪R x, U x⟫_ℂ ∂μw) - N⁻¹ * ∫ x, F₂ x ∂μw := by
          rw [integral_sub hF₁ (hF₂.const_mul _), integral_const_mul]
      _ = _ := by
          rw [integral_inner_realPWTestFamilies Y α s hs hY.le ha ha1 hψc hψ0 L]
          rfl

/-- Reconstruction: the cutoff of the action of `ψ`, projected onto the level on both sides,
is nuclear. Its trace is the trace on the whole band minus the diagonal entry at the normalized
evaluation vector at the origin. On the level this operator is the compression of the cutoff
action, and it vanishes on the orthogonal complement of the level. -/
theorem exists_realPWTestCutoff_level_nuclear (hY : 0 < Y) (ha : 0 ≤ α) {a b : ℝ}
    (ha1 : 1 ≤ a) (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) (L : ℝ) :
    ∃ T : nuclearEndomorphisms V,
      (∀ f : V, ∃ r : Lp ℂ 2 μw,
        (∀ᵐ x ∂μw, r x = sharpIntervalMask L x *
          ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev (g⁻¹ * x) ((realPWZeroLevel Y α s hs).starProjection f))) ∧
        T.val f = (realPWZeroLevel Y α s hs).starProjection ((V).orthogonalProjectionOnto r)) ∧
      hilbertTrace T = (∫ g, ψ g * realPWSharpTrace Y α s hs g L) -
        (((‖evv 0‖ ^ 2 : ℝ) : ℂ))⁻¹ * realPWZeroLevelCorrection Y α s hs ψ L :=
  exists_realPWTestCutoff_compl_nuclear Y α s hs hY ha ha1 ψ hψc hψ0 L (evv 0)

/-- The pointwise values of a band vector are square integrable for the weighted measure. -/
private theorem memLp_evaluation (f : V) : MemLp (fun x ↦ ev x f) 2 μw :=
  (memLp_congr_ae (RealPWBand.evaluation_ae Y hμw
    (realPWIntervalMeasure_absolutelyContinuous α s) f)).2 (Lp.memLp f.val)

/-- The product of the conjugate of one band vector with a contraction of another is
integrable for the weighted measure. -/
private theorem integrable_star_evaluation_mul_dilate {g : ℝ} (hg : 0 < g) (e f : V) :
    Integrable (fun x ↦ star (ev x e) * ev (g⁻¹ * x) f) μw := by
  let v : ℝ → ℂ := fun x ↦ ev x f
  have hv : MemLp v 2 μw := memLp_evaluation Y α s hs f
  have hd : MemLp (fun x ↦ v (g⁻¹ * x)) 2 μw :=
    memLp_realPWIntervalMeasure_dilation hs (inv_pos.mpr hg) hv
  have hE := memLp_evaluation Y α s hs e
  refine (L2.integrable_inner (𝕜 := ℂ) (hE.toLp _) (hd.toLp _)).congr ?_
  filter_upwards [hE.coeFn_toLp, hd.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  ring

/-- Reconstruction: for `g > 1` the contraction `x ↦ f (g⁻¹ x)` of a band vector is a limit of
band vectors in a weak sense. There are bounded continuous masks `m L` tending pointwise to one
and band vectors `q L` with values `m L x * f (g⁻¹ x)`, and for every band vector `e` the inner
products `⟪e, q L⟫` tend to the weighted integral of the product of the conjugate of `e` with
the contraction. The masks are the smoothed masks of `Sec4_RealPWSmoothedAction`. The
contraction itself is not shown to be a band vector. -/
theorem exists_realPWBand_maskedDilate (hY : 0 < Y) {g : ℝ} (hg : 1 < g) (f : V) :
    ∃ (m : ℝ → ℝ → ℂ) (q : ℝ → V) (C : ℝ),
      (∀ L, Continuous (m L)) ∧ (∀ L x, ‖m L x‖ ≤ C) ∧
      (∀ x, Tendsto (fun L ↦ m L x) atTop (𝓝 1)) ∧
      (∀ L x, ev x (q L) = m L x * ev (g⁻¹ * x) f) ∧
      ∀ e : V, Tendsto (fun L ↦ ⟪e, q L⟫_ℂ) atTop
        (𝓝 (∫ x, star (ev x e) * ev (g⁻¹ * x) f ∂μw)) := by
  have hμac := realPWIntervalMeasure_absolutelyContinuous α s
  have hg0 : 0 < g := zero_lt_one.trans hg
  have hginv : g⁻¹ < 1 := inv_lt_one_of_one_lt₀ hg
  let c := (1 - g⁻¹) * Y / 2
  have hc : 0 < c := half_pos (mul_pos (sub_pos.mpr hginv) hY)
  have hmargin : c ≤ (1 - g⁻¹) * Y :=
    half_le_self (mul_nonneg (sub_nonneg.mpr hginv.le) hY.le)
  obtain ⟨η, he, hm, hη, -⟩ := exists_evenSchwartz_smoothingKernel c hc
  choose q hq using fun L ↦ exists_realPW_smoothIntervalMask_mul_dilate_evaluation hY hs
    (inv_pos.mpr hg0) hc.le hmargin η he hη L 1 f
  refine ⟨fun L x ↦ smoothIntervalMask η L x, q, ∫ t, ‖η t‖,
    fun L ↦ continuous_smoothIntervalMask η L,
    fun L x ↦ norm_smoothIntervalMask_le η.integrable L x, fun x ↦ ?_, fun L x ↦ ?_,
    fun e ↦ ?_⟩
  · have h := tendsto_smoothIntervalMask η η.integrable x
    rwa [hm] at h
  · rw [hq L x, one_mul]
  · let F : ℝ → ℂ := fun x ↦ star (ev x e) * ev (g⁻¹ * x) f
    have hF : Integrable F μw := integrable_star_evaluation_mul_dilate Y α s hs hg0 e f
    have key : ∀ L, ∫ x, smoothIntervalMask η L x * F x ∂μw = ⟪e, q L⟫_ℂ := by
      intro L
      have h2 : ⟪e, q L⟫_ℂ =
          ∫ x, ⟪(e.val : Lp ℂ 2 μw) x, ((q L).val : Lp ℂ 2 μw) x⟫_ℂ ∂μw := by
        rw [← L2.inner_def]
        rfl
      rw [h2]
      apply integral_congr_ae
      filter_upwards [RealPWBand.evaluation_ae Y hμw hμac e,
        RealPWBand.evaluation_ae Y hμw hμac (q L)] with x hx1 hx2
      rw [← hx1, ← hx2]
      change smoothIntervalMask η L x * (star (ev x e) * ev (g⁻¹ * x) f) =
        ⟪ev x e, ev x (q L)⟫_ℂ
      rw [hq L x]
      simp only [RCLike.inner_apply, starRingEnd_apply]
      ring
    have hlimL : Tendsto (fun L ↦ ∫ x, smoothIntervalMask η L x * F x ∂μw) atTop
        (𝓝 (∫ x, F x ∂μw)) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (fun x ↦ (∫ t, ‖η t‖) * ‖F x‖) (.of_forall fun L ↦ ?_)
        (.of_forall fun L ↦ ae_of_all _ fun x ↦ ?_) (hF.norm.const_mul _)
        (ae_of_all _ fun x ↦ ?_)
      · exact ((continuous_smoothIntervalMask η L).aestronglyMeasurable).mul
          hF.aestronglyMeasurable
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_smoothIntervalMask_le η.integrable L x)
          (norm_nonneg _)
      · have h := (tendsto_smoothIntervalMask η η.integrable x).mul_const (F x)
        rwa [hm, one_mul] at h
    exact hlimL.congr key

/-- Reconstruction: for `g > 1` the contraction `x ↦ f (g⁻¹ x)` of a band vector pairs with the
evaluation vector at the origin as a band vector does: the weighted integral of its product
with the conjugate of that vector is `f 0`. -/
theorem integral_star_evaluationVector_zero_mul_dilate (hY : 0 < Y) {g : ℝ} (hg : 1 < g)
    (f : V) : ∫ x, star (ev x (evv 0)) * ev (g⁻¹ * x) f ∂μw = ev 0 f := by
  obtain ⟨m, q, C, -, -, hm1, hq, hlim⟩ := exists_realPWBand_maskedDilate Y α s hs hY hg f
  have h1 (L : ℝ) : ⟪evv 0, q L⟫_ℂ = m L 0 * ev 0 f := by
    have h : ev 0 (q L) = ⟪evv 0, q L⟫_ℂ := by
      rw [← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]
    rw [← h, hq L 0, mul_zero]
  have h2 : Tendsto (fun L ↦ m L 0 * ev 0 f) atTop (𝓝 (ev 0 f)) := by
    have h := (hm1 0).mul_const (ev 0 f)
    rwa [one_mul] at h
  exact tendsto_nhds_unique ((hlim (evv 0)).congr h1) h2

/-- The weighted integral of the product of a band vector with its contraction by `g⁻¹` is
bounded uniformly for `g` between `1` and `b`. -/
private theorem exists_integral_norm_star_mul_dilate_le (ha : 0 ≤ α) (b : ℝ) (e : V) :
    ∃ D : ℝ, ∀ g ∈ Icc 1 b, ∫ x, ‖star (ev x e) * ev (g⁻¹ * x) e‖ ∂μw ≤ D := by
  let w := realPWIntervalWeight α s
  have hw0 (x : ℝ) : 0 ≤ w x := zero_le_one.trans (one_le_realPWIntervalWeight α s hs x)
  have hWm : Measurable fun x ↦ ENNReal.ofReal (w x) :=
    (measurable_realPWIntervalWeight α s).ennreal_ofReal
  have hWlt : ∀ᵐ x ∂(volume : Measure ℝ), ENNReal.ofReal (w x) < ⊤ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hEc : Continuous (fun x ↦ ev x e) := (RealPWBand.contDiff_evaluation Y hμw e 0).continuous
  let Φ : ℝ → ℝ := fun x ↦ ‖ev x e‖ ^ 2 * w x
  have hΦ0 (x : ℝ) : 0 ≤ Φ x := mul_nonneg (sq_nonneg _) (hw0 x)
  have hΦ : Integrable Φ := by
    have h : Integrable (fun x ↦ ‖ev x e‖ ^ 2) μw :=
      (memLp_two_iff_integrable_sq_norm hEc.aestronglyMeasurable).mp
        (memLp_evaluation Y α s hs e)
    have h2 := (integrable_withDensity_iff hWm hWlt).1 h
    refine h2.congr (ae_of_all _ fun x ↦ ?_)
    change ‖ev x e‖ ^ 2 * (ENNReal.ofReal (w x)).toReal = ‖ev x e‖ ^ 2 * w x
    rw [ENNReal.toReal_ofReal (hw0 x)]
  let I := ∫ x, Φ x
  have hI0 : 0 ≤ I := integral_nonneg hΦ0
  obtain ⟨Kb, hKb0, hKdil⟩ := exists_realPWIntervalWeight_le_dilation (α := α) ha hs b
  refine ⟨1 / 2 * (I + Kb * (b * I)), fun g hg ↦ ?_⟩
  have hg0 : 0 < g := zero_lt_one.trans_le hg.1
  have hΦg : Integrable (fun x ↦ Φ (g⁻¹ * x)) := hΦ.comp_mul_left' (inv_ne_zero hg0.ne')
  have hbound : Integrable (fun x ↦ 1 / 2 * (Φ x + Kb * Φ (g⁻¹ * x))) :=
    (hΦ.add (hΦg.const_mul Kb)).const_mul _
  have hpt : ∀ x, ‖star (ev x e) * ev (g⁻¹ * x) e‖ * w x ≤
      1 / 2 * (Φ x + Kb * Φ (g⁻¹ * x)) := by
    intro x
    rw [norm_mul, norm_star]
    have h2 : ‖ev (g⁻¹ * x) e‖ ^ 2 * w x ≤ Kb * (‖ev (g⁻¹ * x) e‖ ^ 2 * w (g⁻¹ * x)) := by
      calc ‖ev (g⁻¹ * x) e‖ ^ 2 * w x ≤ ‖ev (g⁻¹ * x) e‖ ^ 2 * (Kb * w (g⁻¹ * x)) :=
            mul_le_mul_of_nonneg_left (hKdil g hg x) (sq_nonneg _)
        _ = _ := by ring
    have h3 : ‖ev x e‖ * ‖ev (g⁻¹ * x) e‖ * w x ≤
        1 / 2 * (‖ev x e‖ ^ 2 * w x + ‖ev (g⁻¹ * x) e‖ ^ 2 * w x) := by
      nlinarith [mul_nonneg (hw0 x) (sq_nonneg (‖ev x e‖ - ‖ev (g⁻¹ * x) e‖))]
    change _ ≤ 1 / 2 * (‖ev x e‖ ^ 2 * w x + Kb * (‖ev (g⁻¹ * x) e‖ ^ 2 * w (g⁻¹ * x)))
    linarith
  have hconv : ∫ x, ‖star (ev x e) * ev (g⁻¹ * x) e‖ ∂μw =
      ∫ x, ‖star (ev x e) * ev (g⁻¹ * x) e‖ * w x := by
    change ∫ x, ‖star (ev x e) * ev (g⁻¹ * x) e‖
      ∂(volume.withDensity fun x ↦ ENNReal.ofReal (w x)) = _
    rw [integral_withDensity_eq_integral_toReal_smul hWm hWlt]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    change (ENNReal.ofReal (w x)).toReal • ‖star (ev x e) * ev (g⁻¹ * x) e‖ = _
    rw [ENNReal.toReal_ofReal (hw0 x), smul_eq_mul, mul_comm]
  rw [hconv]
  calc ∫ x, ‖star (ev x e) * ev (g⁻¹ * x) e‖ * w x
      ≤ ∫ x, 1 / 2 * (Φ x + Kb * Φ (g⁻¹ * x)) :=
        integral_mono_of_nonneg (ae_of_all _ fun x ↦ mul_nonneg (norm_nonneg _) (hw0 x))
          hbound (ae_of_all _ hpt)
    _ = 1 / 2 * (I + Kb * (g * I)) := by
        rw [integral_const_mul, integral_add hΦ (hΦg.const_mul Kb), integral_const_mul,
          Measure.integral_comp_mul_left Φ g⁻¹, inv_inv, abs_of_pos hg0, smul_eq_mul]
    _ ≤ 1 / 2 * (I + Kb * (b * I)) := by
        have h := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hg.2 hI0) hKb0
        linarith

/-- Reconstruction: let `e` be a band vector and suppose that for each `g` in the support of
`ψ` the weighted integral of the product of the conjugate of `e` with its contraction by `g⁻¹`
is `κ g`. As the cutoff is removed, the diagonal entry of the cutoff action of `ψ` at `e` tends
to the integral of `ψ g g ^ (-1/2) κ g`. -/
theorem tendsto_realPWTestCorrection (hY : 0 < Y) (ha : 0 ≤ α) {a b : ℝ} (ha1 : 1 ≤ a)
    (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) (e : V) (κ : ℝ → ℂ)
    (hκ : ∀ g ∈ Icc a b, ∫ x, star (ev x e) * ev (g⁻¹ * x) e ∂μw = κ g) :
    Tendsto (fun L ↦ realPWTestCorrection Y α s hs e ψ L) atTop
      (𝓝 (∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * κ g))) := by
  have hψm : Measurable ψ := hψc.measurable
  have hψi : Integrable ψ :=
    hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hψ0)
  let E : ℝ → ℂ := fun x ↦ ev x e
  have hEc : Continuous E := (RealPWBand.contDiff_evaluation Y hμw e 0).continuous
  obtain ⟨C, hC0, hC⟩ := exists_norm_realPWEvaluationVector_dilate_le Y α s hs hY.le ha
  let k := 2 * realPWOriginJetCount α
  have hEb : ∀ g : ℝ, 1 ≤ g → ∀ x, ‖E (g⁻¹ * x)‖ ≤ C * |x| ^ k * ‖e‖ := by
    intro g hg x
    have h : E (g⁻¹ * x) = ⟪evv (g⁻¹ * x), e⟫_ℂ := by
      change ev (g⁻¹ * x) e = _
      rw [← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]
    rw [h]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hC g hg x) (norm_nonneg _))
  have hEb1 : ∀ x, ‖E x‖ ≤ C * |x| ^ k * ‖e‖ := by
    intro x
    have h := hEb 1 le_rfl x
    rwa [inv_one, one_mul] at h
  let J : ℝ → ℝ → ℂ := fun L g ↦
    ∫ x, sharpIntervalMask L x * (star (E x) * E (g⁻¹ * x)) ∂μw
  have : SFinite μw := by
    unfold realPWIntervalMeasure
    infer_instance
  have hampn : ∀ g : ℝ, 1 ≤ g → ‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ ≤ 1 := by
    intro g hg1
    rw [Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans_le hg1).le _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hg1 (by norm_num)
  -- the two integrals are exchanged at a fixed cutoff
  have hfub : ∀ L, realPWTestCorrection Y α s hs e ψ L =
      ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * J L g) := by
    intro L
    let K : ℝ → ℝ → ℂ := fun x g ↦ ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (sharpIntervalMask L x * (star (E x) * E (g⁻¹ * x))))
    have hKm : Measurable (Function.uncurry K) := by
      have h1 : Measurable (fun p : ℝ × ℝ ↦ ψ p.2) := hψm.comp measurable_snd
      have h2 : Measurable (fun p : ℝ × ℝ ↦ sharpIntervalMask L p.1) :=
        (sharpIntervalMask_measurable L).comp measurable_fst
      have h3 : Measurable (fun p : ℝ × ℝ ↦ ((p.2 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) :=
        Complex.measurable_ofReal.comp (measurable_snd.pow_const _)
      have h4 : Measurable (fun p : ℝ × ℝ ↦ star (E p.1)) :=
        continuous_star.measurable.comp (hEc.measurable.comp measurable_fst)
      have h5 : Measurable (fun p : ℝ × ℝ ↦ E (p.2⁻¹ * p.1)) :=
        hEc.measurable.comp (measurable_snd.inv.mul measurable_fst)
      exact h1.mul (h3.mul (h2.mul (h4.mul h5)))
    have hKb : ∀ x g, ‖K x g‖ ≤
        ((C * ‖e‖) ^ 2 * (‖sharpIntervalMask L x‖ * |x| ^ (2 * k))) * ‖ψ g‖ := by
      intro x g
      change ‖ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (sharpIntervalMask L x * (star (E x) * E (g⁻¹ * x))))‖ ≤ _
      by_cases hg : g ∈ Icc a b
      · have hg1 : 1 ≤ g := ha1.trans hg.1
        have hp0 : 0 ≤ C * |x| ^ k * ‖e‖ :=
          mul_nonneg (mul_nonneg hC0 (pow_nonneg (abs_nonneg x) k)) (norm_nonneg _)
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_star]
        calc ‖ψ g‖ * (‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
              (‖sharpIntervalMask L x‖ * (‖E x‖ * ‖E (g⁻¹ * x)‖)))
            ≤ ‖ψ g‖ * (1 * (‖sharpIntervalMask L x‖ *
                ((C * |x| ^ k * ‖e‖) * (C * |x| ^ k * ‖e‖)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul (hampn g hg1)
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul (hEb1 x) (hEb g hg1 x) (norm_nonneg _) hp0) (norm_nonneg _))
                (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
                zero_le_one) (norm_nonneg _)
          _ = _ := by ring
      · rw [hψ0 g hg]
        simp
    have hKint : Integrable (Function.uncurry K) (Measure.prod μw volume) :=
      (((integrable_sharpIntervalMask_abs_pow_realPW α s hs ha L).const_mul
        ((C * ‖e‖) ^ 2)).mul_prod hψi.norm).mono' hKm.aestronglyMeasurable
          (ae_of_all _ fun z ↦ hKb z.1 z.2)
    calc realPWTestCorrection Y α s hs e ψ L = ∫ x, (∫ g, K x g) ∂μw := by
          refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
          change sharpIntervalMask L x * (star (E x) *
            ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * E (g⁻¹ * x))) = ∫ g, K x g
          rw [← integral_const_mul, ← integral_const_mul]
          refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
          change sharpIntervalMask L x * (star (E x) *
            (ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * E (g⁻¹ * x)))) =
            ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              (sharpIntervalMask L x * (star (E x) * E (g⁻¹ * x))))
          ring
      _ = ∫ g, (∫ x, K x g ∂μw) := integral_integral_swap hKint
      _ = _ := by
          refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
          change ∫ x, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            (sharpIntervalMask L x * (star (E x) * E (g⁻¹ * x)))) ∂μw =
            ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * J L g)
          rw [integral_const_mul, integral_const_mul]
  -- the limit of the inner integral for one dilation
  have hJlim : ∀ g ∈ Icc a b, Tendsto (fun L ↦ J L g) atTop (𝓝 (κ g)) := by
    intro g hg
    have hg1 : 1 ≤ g := ha1.trans hg.1
    have hF := integrable_star_evaluation_mul_dilate Y α s hs (zero_lt_one.trans_le hg1) e e
    rw [← hκ g hg]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x ↦ ‖star (E x) * E (g⁻¹ * x)‖) (.of_forall fun L ↦ ?_)
      (.of_forall fun L ↦ ae_of_all _ fun x ↦ ?_) hF.norm (ae_of_all _ fun x ↦ ?_)
    · exact ((sharpIntervalMask_measurable L).aestronglyMeasurable).mul
        hF.aestronglyMeasurable
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (sharpIntervalMask_norm_le_one L x)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop |x|] with L hL
      have hm : sharpIntervalMask L x = 1 := by simp [sharpIntervalMask, abs_le.mp hL]
      rw [hm, one_mul]
  -- a bound for it that is uniform in the dilation and the cutoff
  obtain ⟨D, hD⟩ := exists_integral_norm_star_mul_dilate_le Y α s hs ha b e
  have hJb : ∀ g ∈ Icc a b, ∀ L, ‖J L g‖ ≤ D := by
    intro g hg L
    have hg1 : 1 ≤ g := ha1.trans hg.1
    have hF := integrable_star_evaluation_mul_dilate Y α s hs (zero_lt_one.trans_le hg1)
      e e
    calc ‖J L g‖ ≤ ∫ x, ‖sharpIntervalMask L x * (star (E x) * E (g⁻¹ * x))‖ ∂μw :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖star (E x) * E (g⁻¹ * x)‖ ∂μw :=
          integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) hF.norm
            (ae_of_all _ fun x ↦ by
              change ‖sharpIntervalMask L x * (star (E x) * E (g⁻¹ * x))‖ ≤
                ‖star (E x) * E (g⁻¹ * x)‖
              rw [norm_mul]
              exact mul_le_of_le_one_left (norm_nonneg _)
                (sharpIntervalMask_norm_le_one L x))
      _ ≤ D := hD g ⟨hg1, hg.2⟩
  have hJm : ∀ L, Measurable (fun g ↦ J L g) := by
    intro L
    have hF : Measurable (fun p : ℝ × ℝ ↦
        sharpIntervalMask L p.2 * (star (E p.2) * E (p.1⁻¹ * p.2))) :=
      ((sharpIntervalMask_measurable L).comp measurable_snd).mul
        ((continuous_star.measurable.comp (hEc.measurable.comp measurable_snd)).mul
          (hEc.measurable.comp (measurable_fst.inv.mul measurable_snd)))
    exact (hF.stronglyMeasurable.integral_prod_right' (ν := μw)).measurable
  have hfun : (fun L ↦ realPWTestCorrection Y α s hs e ψ L) =
      fun L ↦ ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * J L g) := funext hfub
  rw [hfun]
  refine tendsto_integral_filter_of_dominated_convergence (fun g ↦ ‖ψ g‖ * D)
    (.of_forall fun L ↦ ?_) (.of_forall fun L ↦ ae_of_all _ fun g ↦ ?_)
    (hψi.norm.mul_const D) (ae_of_all _ fun g ↦ ?_)
  · exact hψi.aestronglyMeasurable.mul
      ((Complex.measurable_ofReal.comp (measurable_id.pow_const _)).mul
        (hJm L)).aestronglyMeasurable
  · by_cases hg : g ∈ Icc a b
    · rw [norm_mul, norm_mul]
      calc ‖ψ g‖ * (‖((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * ‖J L g‖) ≤ ‖ψ g‖ * (1 * D) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hampn g (ha1.trans hg.1)) (hJb g hg L)
              (norm_nonneg _) zero_le_one) (norm_nonneg _)
        _ = ‖ψ g‖ * D := by ring
    · rw [hψ0 g hg, zero_mul, norm_zero, zero_mul]
  · by_cases hg : g ∈ Icc a b
    · exact ((hJlim g hg).const_mul _).const_mul _
    · simp only [hψ0 g hg, zero_mul]
      exact tendsto_const_nhds

/-- Reconstruction: as the cutoff is removed, the diagonal entry of the cutoff action of `ψ` at
the evaluation vector at the origin tends to the integral of `ψ g g ^ (-1/2)` times the value
at the origin of that vector. -/
theorem tendsto_realPWZeroLevelCorrection (hY : 0 < Y) (ha : 0 ≤ α) {a b : ℝ} (ha1 : 1 < a)
    (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) :
    Tendsto (fun L ↦ realPWZeroLevelCorrection Y α s hs ψ L) atTop
      (𝓝 ((∫ g, ψ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * ev 0 (evv 0))) := by
  have hgoal : (∫ g, ψ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * ev 0 (evv 0) =
      ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev 0 (evv 0)) := by
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    ring
  rw [hgoal]
  exact tendsto_realPWTestCorrection Y α s hs hY ha ha1.le ψ hψc hψ0 (evv 0)
    (fun _ ↦ ev 0 (evv 0)) fun g hg ↦
      integral_star_evaluationVector_zero_mul_dilate Y α s hs hY (ha1.trans_le hg.1) (evv 0)

/-- Below width one half the evaluation at the origin is not zero on the band. -/
theorem realPWEvaluationVector_zero_ne_zero (hY : 0 < Y) (ha : 0 ≤ α) (hα : α < 1 / 2) :
    evv 0 ≠ 0 := by
  obtain ⟨φ, he, hsupp, hpos⟩ := exists_evenSchwartz_band_trial hY (ε := Y) hY
  have hφ0 : φ 0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hpos
    simp at hpos
  have hm : MemLp (φ : ℝ → ℂ) 2 μw :=
    memLp_realPWIntervalMeasure_of_evenSchwartz_order ha hs φ he 0 (by
      push_cast
      linarith) ⟨SchwartzMap.seminorm ℝ 0 0 φ, fun x _ ↦ by
        simpa using φ.norm_le_seminorm ℝ x⟩
  have hb : ∀ t ∉ Icc (-Y) Y, (𝓕 φ) t = 0 := by
    intro t ht
    have h : 𝓕 (φ : ℝ → ℂ) t = 0 :=
      Function.notMem_support.mp fun h ↦ ht (Ioo_subset_Icc_self (hsupp h))
    rwa [SchwartzMap.fourier_coe]
  obtain ⟨f, hf⟩ := RealPWBand.exists_evaluation_eq_of_weightedSchwartz Y φ he hb hμw hm
  intro h0
  apply hφ0
  have h1 : ev 0 f = φ 0 := congrFun hf 0
  have h2 : ev 0 f = ⟪evv 0, f⟫_ℂ := by
    rw [← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]
  rw [← h1, h2, h0, inner_zero_left]

/-- Below width one half, the limit of the sharp trace of the dilation by `g⁻¹` minus
`g ^ (-1/2)` is `g ^ (-1/2) g ^ (-2) / (1 - g ^ (-2))`: the limit with one even jet removed. -/
theorem realPWSharpTraceLimit_sub_of_lt_half {α g : ℝ} (hα : α < 1 / 2) (hg : 1 < g) :
    realPWSharpTraceLimit α g - ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
      ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((g⁻¹ : ℝ) : ℂ) ^ 2 / (1 - ((g⁻¹ : ℝ) : ℂ) ^ 2) := by
  have hg0 : 0 < g := zero_lt_one.trans hg
  have hden : (1 : ℂ) - ((g⁻¹ : ℝ) : ℂ) ^ 2 ≠ 0 := by
    have hc : (1 : ℂ) - ((g⁻¹ : ℝ) : ℂ) ^ 2 = ((1 - g⁻¹ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hc]
    have : g⁻¹ ^ 2 < 1 :=
      pow_lt_one₀ (inv_nonneg.mpr hg0.le) (inv_lt_one_of_one_lt₀ hg) (by norm_num)
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  rw [realPWSharpTraceLimit, realPWOriginJetCount_eq_zero hα, mul_zero, pow_zero, mul_one,
    eq_div_iff hden, sub_mul, div_mul_cancel₀ _ hden]
  ring

/-- Reconstruction: for `0 ≤ α < 1/2` and a continuous test function `ψ` of the dilation
supported in `[a, b]` with `1 < a`, the traces of the cutoffs of its action, compressed to the
level of band vectors vanishing at the origin, converge as the cutoff is removed. The limit is
the limit on the whole band minus the integral of `ψ g g ^ (-1/2)`, which is the contribution
of the direction removed by the level. -/
theorem exists_realPWTestCutoff_level_trace_limit (hY : 0 < Y) (ha : 0 ≤ α) (hα : α < 1 / 2)
    {a b : ℝ} (ha1 : 1 < a) (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hψ0 : ∀ g ∉ Icc a b, ψ g = 0) :
    ∃ T : ℝ → nuclearEndomorphisms V,
      (∀ L (f : V), ∃ r : Lp ℂ 2 μw,
        (∀ᵐ x ∂μw, r x = sharpIntervalMask L x *
          ∫ g, ψ g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev (g⁻¹ * x) ((realPWZeroLevel Y α s hs).starProjection f))) ∧
        (T L).val f =
          (realPWZeroLevel Y α s hs).starProjection ((V).orthogonalProjectionOnto r)) ∧
      Tendsto (fun L ↦ hilbertTrace (T L)) atTop
        (𝓝 ((∫ g, ψ g * realPWSharpTraceLimit α g) -
          ∫ g, ψ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) := by
  choose T hT1 hT2 using fun L ↦
    exists_realPWTestCutoff_level_nuclear Y α s hs hY ha ha1.le ψ hψc hψ0 L
  refine ⟨T, hT1, ?_⟩
  have h : (fun L ↦ hilbertTrace (T L)) = fun L ↦
      (∫ g, ψ g * realPWSharpTrace Y α s hs g L) -
        (((‖evv 0‖ ^ 2 : ℝ) : ℂ))⁻¹ * realPWZeroLevelCorrection Y α s hs ψ L := funext hT2
  rw [h]
  have h1 := tendsto_integral_realPWSharpTrace hY ha hs ha1 ψ
    (hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hψ0)) hψ0
  have h2 := (tendsto_realPWZeroLevelCorrection Y α s hs hY ha ha1 ψ hψc hψ0).const_mul
    (((‖evv 0‖ ^ 2 : ℝ) : ℂ))⁻¹
  have hE0 := realPWEvaluationVector_zero_ne_zero Y α s hs hY ha hα
  have hN : ev 0 (evv 0) = ((‖evv 0‖ ^ 2 : ℝ) : ℂ) := by
    have h3 : ev 0 (evv 0) = ⟪evv 0, evv 0⟫_ℂ := by
      rw [← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]
    rw [h3, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hN0 : ((‖evv 0‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hE0))
  have h3 : (((‖evv 0‖ ^ 2 : ℝ) : ℂ))⁻¹ *
      ((∫ g, ψ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * ev 0 (evv 0)) =
      ∫ g, ψ g * ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [hN]
    field_simp
  rw [h3] at h2
  exact h1.sub h2

end Level

end RiemannMasullo.Isolated
