module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWConcentration
public import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertFamilyTrace
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.Algebra.Order.Archimedean

/-! # Weighted real cutoff compression as a product of analysis maps -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace RiemannMasullo.RealPWBand

open scoped ContDiff

/-- A Hilbert basis of the real weighted band is countable: each basis vector is
seen at some rational sample, and each sample sees only countably many basis vectors. -/
theorem countable_hilbertBasis (Y : ℝ) {μ : Measure ℝ} (hμ : volume ≤ μ)
    (hμac : μ ≪ volume) {ι : Type*} (b : HilbertBasis ι ℂ (space Y hμ)) : Countable ι := by
  let e (q : ℚ) := evaluationVector Y hμ (q : ℝ)
  let S (q : ℚ) : Set ι := {i | inner ℂ (b i) (e q) ≠ 0}
  have hS (q : ℚ) : (S q).Countable := by
    refine (hasSum_norm_inner_sq_hilbertBasis b (e q)).summable.countable_support.mono ?_
    intro i hi
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hi)
  have hcover : (univ : Set ι) ⊆ ⋃ q, S q := by
    intro i _
    by_contra h
    have hz (q : ℚ) : evaluation Y hμ (q : ℝ) (b i) = 0 := by
      have hi : inner ℂ (b i) (e q) = 0 := by
        by_contra hn
        exact h (mem_iUnion.mpr ⟨q, hn⟩)
      rw [← toDual_evaluationVector, InnerProductSpace.toDual_apply_apply,
        ← inner_conj_symm, hi, map_zero]
    have hall (x : ℝ) : evaluation Y hμ x (b i) = 0 :=
      (Rat.denseRange_cast (𝕜 := ℝ)).induction_on x
        (isClosed_eq (contDiff_evaluation Y hμ (b i) 0).continuous continuous_const) hz
    have hzi : b i = 0 := by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [evaluation_ae Y hμ hμac (b i), Lp.coeFn_zero ℂ 2 μ] with x hae h0
      exact hae.symm.trans ((hall x).trans h0.symm)
    exact (b.orthonormal.ne_zero i) hzi
  exact Set.countable_univ_iff.mp ((Set.countable_iUnion hS).mono hcover)

/-- Taylor's estimate for each smooth trace becomes an operator-norm estimate by
uniform boundedness on the complete weighted band. -/
theorem exists_norm_evaluation_le_abs_pow (Y : ℝ) (hY : 0 ≤ Y) {μ : Measure ℝ}
    (hμ : volume ≤ μ) (m : ℕ)
    (hjet : ∀ (f : space Y hμ) (k : ℕ), k < m →
      iteratedDeriv k (fun t ↦ evaluation Y hμ t f) 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |x| ≤ 1 → ‖evaluation Y hμ x‖ ≤ C * |x| ^ m := by
  cases m with
  | zero =>
    exact ⟨Real.sqrt (2 * Y), Real.sqrt_nonneg _, fun x _ ↦ by
      simpa using norm_evaluation_le Y hY hμ x⟩
  | succ n =>
    let T (r : Ioc (0 : ℝ) 1) : space Y hμ →L[ℂ] ℂ :=
      (((r.val ^ (n + 1))⁻¹ : ℝ) : ℂ) • evaluation Y hμ r.val
    have hpoint (f : space Y hμ) : ∃ C : ℝ, ∀ r, ‖T r f‖ ≤ C := by
      let F : ℝ → ℂ := fun t ↦ evaluation Y hμ t f
      have hs : ContDiffOn ℝ ((n : ℕ∞ω) + 1) F (Icc 0 1) := by
        simpa using (contDiff_evaluation Y hμ f (n + 1)).contDiffOn (s := Icc 0 1)
      obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (n := n) hs
      refine ⟨C, fun r ↦ ?_⟩
      have hpoly : taylorWithinEval F n (Icc 0 1) 0 r.val = 0 := by
        rw [taylor_within_apply]
        apply Finset.sum_eq_zero
        intro k hk
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
          (contDiff_evaluation Y hμ f k).contDiffAt (by norm_num : (0 : ℝ) ∈ Icc 0 1),
          show iteratedDeriv k F 0 = 0 from hjet f k (Finset.mem_range.mp hk), smul_zero]
      have hb := hC r.val ⟨r.property.1.le, r.property.2⟩
      rw [hpoly, sub_zero, sub_zero] at hb
      have hr : 0 < r.val ^ (n + 1) := pow_pos r.property.1 _
      change ‖(((r.val ^ (n + 1))⁻¹ : ℝ) : ℂ) • F r.val‖ ≤ C
      rwa [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), mul_comm,
        ← div_eq_mul_inv, div_le_iff₀ hr]
    obtain ⟨C, hC⟩ := banach_steinhaus (g := T) hpoint
    refine ⟨max C 0, le_max_right _ _, fun x hx ↦ ?_⟩
    have habs : evaluation Y hμ x = evaluation Y hμ |x| := by
      apply ContinuousLinearMap.ext
      intro f
      rcases le_total 0 x with hp | hn
      · rw [abs_of_nonneg hp]
      · rw [abs_of_nonpos hn, evaluation_even]
    rw [habs]
    by_cases hz : |x| = 0
    · have hzero : evaluation Y hμ 0 = 0 := by
        apply ContinuousLinearMap.ext
        intro f
        simpa using hjet f 0 (Nat.zero_lt_succ n)
      simp [hz, hzero]
    · let r : Ioc (0 : ℝ) 1 := ⟨|x|, lt_of_le_of_ne (abs_nonneg x) (Ne.symm hz), hx⟩
      have hr : 0 < r.val ^ (n + 1) := pow_pos r.property.1 _
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro f
      have hTf := ((T r).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right ((hC r).trans (le_max_left C 0)) (norm_nonneg f))
      change ‖(((r.val ^ (n + 1))⁻¹ : ℝ) : ℂ) • evaluation Y hμ r.val f‖ ≤
        max C 0 * ‖f‖ at hTf
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), mul_comm,
        ← div_eq_mul_inv, div_le_iff₀ hr] at hTf
      simpa only [r, mul_assoc, mul_left_comm, mul_comm] using hTf

/-- The Riesz vectors obey the same order of vanishing as the evaluation maps. -/
theorem exists_norm_evaluationVector_le_abs_pow (Y : ℝ) (hY : 0 ≤ Y) {μ : Measure ℝ}
    (hμ : volume ≤ μ) (m : ℕ)
    (hjet : ∀ (f : space Y hμ) (k : ℕ), k < m →
      iteratedDeriv k (fun t ↦ evaluation Y hμ t f) 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |x| ≤ 1 → ‖evaluationVector Y hμ x‖ ≤ C * |x| ^ m := by
  obtain ⟨C, hC, hb⟩ := exists_norm_evaluation_le_abs_pow Y hY hμ m hjet
  refine ⟨C, hC, fun x hx ↦ ?_⟩
  rw [← (InnerProductSpace.toDual ℂ (space Y hμ)).norm_map (evaluationVector Y hμ x),
    toDual_evaluationVector]
  exact hb x hx

end RiemannMasullo.RealPWBand

namespace RiemannMasullo.Isolated

section
variable (Y α s : ℝ) (hs : 0 ≤ s) (g : ℝ)
local notation "μw" => realPWIntervalMeasure α s
local notation "hw" => volume_le_realPWIntervalMeasure α s hs
local notation "V" => RealPWBand.space Y hw
local notation "ev" => RealPWBand.evaluation Y hw
local notation "evv" => RealPWBand.evaluationVector Y hw
local notation "amp" => ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

private theorem cutoff_inner_eval (x : ℝ) (f : V) : ⟪evv x, f⟫_ℂ = ev x f := by
  rw [← InnerProductSpace.toDual_apply_apply, RealPWBand.toDual_evaluationVector]

/-- The factors may split the mask in any way; no positivity is needed. The
conjugation on the dilated vector is essential for complex smoothing kernels. -/
def realPWCutoffLeftFamily (p : ℝ → ℂ) (x : ℝ) : V := p x • evv x

def realPWCutoffRightFamily (q : ℝ → ℂ) (x : ℝ) : V :=
  star (amp * q x) • evv (g⁻¹ * x)

local notation "U" => realPWCutoffLeftFamily Y α s hs
local notation "D" => realPWCutoffRightFamily Y α s hs g

private theorem cutoff_left_pair (p : ℝ → ℂ) (x : ℝ) (f : V) :
    ⟪U p x, f⟫_ℂ = star (p x) * ev x f := by
  change ⟪p x • evv x, f⟫_ℂ = _
  rw [inner_smul_left (𝕜 := ℂ) (evv x) f (p x), starRingEnd_apply,
    cutoff_inner_eval Y α s hs x f]

private theorem cutoff_right_pair (q : ℝ → ℂ) (x : ℝ) (f : V) :
    ⟪D q x, f⟫_ℂ = amp * q x * ev (g⁻¹ * x) f := by
  change ⟪star (amp * q x) • evv (g⁻¹ * x), f⟫_ℂ = _
  rw [inner_smul_left (𝕜 := ℂ) (evv (g⁻¹ * x)) f (star (amp * q x)),
    starRingEnd_apply, star_star, cutoff_inner_eval Y α s hs (g⁻¹ * x) f]

/-- Once the ambient masked dilation is in weighted L², its actual orthogonal
compression agrees with the product of the two analysis maps. -/
theorem realPWCutoff_analysisProduct_eq_projection (p q m : ℝ → ℂ)
    (hm : ∀ x, p x * q x = m x)
    (A B : V →L[ℂ] Lp ℂ 2 μw)
    (hA : ∀ f, ∀ᵐ x ∂μw, A f x = ⟪U p x, f⟫_ℂ)
    (hB : ∀ f, ∀ᵐ x ∂μw, B f x = ⟪D q x, f⟫_ℂ)
    (f : V) (r : Lp ℂ 2 μw)
    (hr : ∀ᵐ x ∂μw, r x = amp * m x * ev (g⁻¹ * x) f) :
    A.adjoint (B f) = (V).orthogonalProjectionOnto r := by
  apply ext_inner_left ℂ
  intro z
  rw [A.adjoint_inner_right, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hA z, hB f, hr, RealPWBand.evaluation_ae Y hw
    (realPWIntervalMeasure_absolutelyContinuous α s) z] with x ha hb hval hz
  rw [ha, hb, hval, ← hz, ← hm x]
  rw [cutoff_left_pair, cutoff_right_pair]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_mul', star_star]
  ring

/-- If the masked dilation belongs to the band, the product really gives its
pointwise action (in contrast with a general sharp compression). -/
theorem realPWCutoff_analysisProduct_evaluation (p q m : ℝ → ℂ)
    (hm : ∀ x, p x * q x = m x) (A B : V →L[ℂ] Lp ℂ 2 μw)
    (hA : ∀ f, ∀ᵐ x ∂μw, A f x = ⟪U p x, f⟫_ℂ)
    (hB : ∀ f, ∀ᵐ x ∂μw, B f x = ⟪D q x, f⟫_ℂ)
    (f r : V) (hr : ∀ x, ev x r = amp * m x * ev (g⁻¹ * x) f) (x : ℝ) :
    ev x (A.adjoint (B f)) = amp * m x * ev (g⁻¹ * x) f := by
  have hae := RealPWBand.evaluation_ae Y hw (realPWIntervalMeasure_absolutelyContinuous α s) r
  have he := realPWCutoff_analysisProduct_eq_projection Y α s hs g p q m hm A B hA hB f r.val
    (hae.mono fun t ht ↦ ht.symm.trans (hr t))
  have he' : A.adjoint (B f) = r := by simpa using he
  rw [he', hr]

private theorem cutoff_density_pointwise (p q m : ℝ → ℂ) (hm : ∀ x, p x * q x = m x)
    (x : ℝ) :
    (ENNReal.ofReal (realPWIntervalWeight α s x)).toReal • ⟪D q x, U p x⟫_ℂ =
      m x * realPWSharpDensity Y α s hs g x := by
  have hw0 := (zero_le_one : (0 : ℝ) ≤ 1).trans (one_le_realPWIntervalWeight α s hs x)
  simp only [ENNReal.toReal_ofReal hw0, Complex.real_smul, realPWSharpDensity,
    Complex.ofReal_mul, ← hm x]
  rw [cutoff_right_pair]
  rw [show U p x = p x • evv x from rfl, map_smul, smul_eq_mul]
  ring

/-- Absolute integrability of the Lebesgue diagonal; in particular subtraction
of two such traces can be taken inside the integral. -/
theorem realPWCutoff_integrable_diagonal (p q m : ℝ → ℂ) (hm : ∀ x, p x * q x = m x)
    (hu : MemLp (U p) 2 μw) (hv : MemLp (D q) 2 μw) :
    Integrable (fun x ↦ m x * realPWSharpDensity Y α s hs g x) := by
  have h := L2.integrable_inner (𝕜 := ℂ) (hv.toLp _) (hu.toLp _)
  have hi : Integrable (fun x ↦ ⟪D q x, U p x⟫_ℂ) μw :=
    h.congr (by filter_upwards [hv.coeFn_toLp, hu.coeFn_toLp] with x hx hy; rw [hx, hy])
  let ρ (x : ℝ) := ENNReal.ofReal (realPWIntervalWeight α s x)
  have hρ : Measurable ρ := (measurable_realPWIntervalWeight α s).ennreal_ofReal
  have hf : ∀ᵐ x ∂volume, ρ x < ∞ := .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  exact ((integrable_withDensity_iff_integrable_smul' hρ hf).mp hi).congr
    (.of_forall (cutoff_density_pointwise Y α s hs g p q m hm))

/-- Specialize the generic analysis-product trace identity to the real weighted
band. The orientation is evaluation at the dilated argument of the vector at
`x`, and the weight is present exactly once when passing to Lebesgue measure. -/
theorem realPWCutoff_integral_familyDiagonal (p q m : ℝ → ℂ) (hm : ∀ x, p x * q x = m x) :
    (∫ x, ⟪D q x, U p x⟫_ℂ ∂μw) = ∫ x, m x * realPWSharpDensity Y α s hs g x := by
  let ρ (x : ℝ) := ENNReal.ofReal (realPWIntervalWeight α s x)
  have hρ : Measurable ρ := (measurable_realPWIntervalWeight α s).ennreal_ofReal
  have hf : ∀ᵐ x ∂volume, ρ x < ∞ := .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  change (∫ x, ⟪D q x, U p x⟫_ℂ ∂volume.withDensity ρ) = _
  rw [integral_withDensity_eq_integral_toReal_smul hρ hf]
  apply integral_congr_ae
  exact .of_forall (cutoff_density_pointwise Y α s hs g p q m hm)

/-- Square-integrable evaluation families give the actual weighted cutoff
compression and its trace, even when the weight is not locally finite. -/
theorem realPWCutoff_exists_compression
    (p q m : ℝ → ℂ) (hm : ∀ x, p x * q x = m x)
    (hu : MemLp (U p) 2 μw) (hv : MemLp (D q) 2 μw) :
    ∃ T : nuclearEndomorphisms V,
      hilbertTrace T = (∫ x, m x * realPWSharpDensity Y α s hs g x) ∧
      (∀ (f : V) (r : Lp ℂ 2 μw),
        (∀ᵐ x ∂μw, r x = amp * m x * ev (g⁻¹ * x) f) →
        T.val f = (V).orthogonalProjectionOnto r) ∧
      (∀ (f r : V), (∀ x, ev x r = amp * m x * ev (g⁻¹ * x) f) →
        ∀ x, ev x (T.val f) = amp * m x * ev (g⁻¹ * x) f) := by
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℂ V
  have := RealPWBand.countable_hilbertBasis Y hw (realPWIntervalMeasure_absolutelyContinuous α s) b
  let A := hilbertFamilyAnalysisCLM hu
  let B := hilbertFamilyAnalysisCLM hv
  have hA (f : V) : A f =ᵐ[μw] fun x ↦ ⟪U p x, f⟫_ℂ :=
    hilbertFamilyAnalysisCLM_apply_ae hu f
  have hB (f : V) : B f =ᵐ[μw] fun x ↦ ⟪D q x, f⟫_ℂ :=
    hilbertFamilyAnalysisCLM_apply_ae hv f
  let Ah : hilbertSchmidtOperators V (Lp ℂ 2 μw) :=
    ⟨A, familyAnalysis_mem_hilbertSchmidtOperators b hu A hA⟩
  let Bh : hilbertSchmidtOperators V (Lp ℂ 2 μw) :=
    ⟨B, familyAnalysis_mem_hilbertSchmidtOperators b hv B hB⟩
  have hn : IsNuclearOperator (A.adjoint.comp B) :=
    nuclear_hilbertSchmidt_comp ⟨_, mem_hilbertSchmidtOperators_adjoint Ah.property⟩ Bh
  have htrace := hilbertTrace_familyAnalysisProduct b (U p) (D q) Ah Bh
    (fun i ↦ hA (b i)) (fun i ↦ hB (b i))
  exact ⟨⟨_, hn⟩, htrace.trans (realPWCutoff_integral_familyDiagonal Y α s hs g p q m hm),
    realPWCutoff_analysisProduct_eq_projection Y α s hs g p q m hm A B hA hB,
    realPWCutoff_analysisProduct_evaluation Y α s hs g p q m hm A B hA hB⟩

end

end RiemannMasullo.Isolated
