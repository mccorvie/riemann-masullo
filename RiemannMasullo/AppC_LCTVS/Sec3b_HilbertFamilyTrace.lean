module

public import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertSchmidtProduct
public import Mathlib.MeasureTheory.Function.L2Space
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Trace of a product of Hilbert-space-valued analysis operators

A square-integrable family gives a Hilbert–Schmidt map into scalar `L²`. Pairing two
such maps gives a nuclear operator and its trace by Parseval and termwise integration.
No finiteness on compact sets is required of the measure.
-/

public noncomputable section

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace

namespace RiemannMasullo

section Analysis

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {μ : Measure X} {u : X → H}

private def hilbertFamilyAnalysisLinear (hu : MemLp u 2 μ) : H →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (hu.inner_const (𝕜 := ℂ) f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add (hu.inner_const (𝕜 := ℂ) f) (hu.inner_const (𝕜 := ℂ) g)]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x ↦ inner_add_right (u x) f g
  map_smul' c f := by
    change (hu.inner_const (𝕜 := ℂ) (c • f)).toLp _ = c • (hu.inner_const (𝕜 := ℂ) f).toLp _
    rw [← MemLp.toLp_const_smul c (hu.inner_const (𝕜 := ℂ) f)]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x ↦ inner_smul_right (u x) f c

private theorem hilbertFamilyAnalysisLinear_bound (hu : MemLp u 2 μ) (f : H) :
    ‖hilbertFamilyAnalysisLinear hu f‖ ≤ ‖hu.toLp u‖ * ‖f‖ := by
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  change ∀ᵐ x ∂μ, ‖((hu.inner_const (𝕜 := ℂ) f).toLp _) x‖ ≤ ‖f‖ * ‖(hu.toLp u) x‖
  filter_upwards [(hu.inner_const (𝕜 := ℂ) f).coeFn_toLp, hu.coeFn_toLp] with x hx hux
  rw [hx, hux, mul_comm]
  exact norm_inner_le_norm (u x) f

/-- Analysis by a square-integrable Hilbert-space-valued family, linear in the input vector. -/
def hilbertFamilyAnalysisCLM (hu : MemLp u 2 μ) : H →L[ℂ] Lp ℂ 2 μ :=
  (hilbertFamilyAnalysisLinear hu).mkContinuous ‖hu.toLp u‖ (hilbertFamilyAnalysisLinear_bound hu)

theorem hilbertFamilyAnalysisCLM_apply (hu : MemLp u 2 μ) (f : H) :
    hilbertFamilyAnalysisCLM hu f = (hu.inner_const (𝕜 := ℂ) f).toLp _ := by
  unfold hilbertFamilyAnalysisCLM
  change hilbertFamilyAnalysisLinear hu f = _
  unfold hilbertFamilyAnalysisLinear
  rfl

theorem hilbertFamilyAnalysisCLM_apply_ae (hu : MemLp u 2 μ) (f : H) :
    ∀ᵐ x ∂μ, (hilbertFamilyAnalysisCLM hu f) x = ⟪u x, f⟫_ℂ :=
  (hu.inner_const (𝕜 := ℂ) f).coeFn_toLp

theorem norm_hilbertFamilyAnalysisCLM_le (hu : MemLp u 2 μ) :
    ‖hilbertFamilyAnalysisCLM hu‖ ≤ ‖hu.toLp u‖ :=
  (hilbertFamilyAnalysisCLM hu).opNorm_le_bound (norm_nonneg _) (hilbertFamilyAnalysisLinear_bound hu)

end Analysis

/-- The analysis operator of a square-integrable Hilbert-valued family is Hilbert–Schmidt.
Countability allows the basis-column identities to hold on a single conull set. -/
theorem familyAnalysis_mem_hilbertSchmidtOperators {X H ι : Type*} [MeasurableSpace X]
    {μ : Measure X} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Countable ι] (b : HilbertBasis ι ℂ H) {u : X → H} (hu : MemLp u 2 μ)
    (A : H →L[ℂ] Lp ℂ 2 μ) (hA : ∀ f, ⇑(A f) =ᵐ[μ] fun x ↦ ⟪u x, f⟫_ℂ) :
    A ∈ hilbertSchmidtOperators H (Lp ℂ 2 μ) := by
  apply (mem_hilbertSchmidtOperators_iff_summable_basis b A).mpr
  let F (i : ι) (x : X) := ‖A (b i) x‖ ^ 2
  have hF (i : ι) : Integrable (F i) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hpoint : ∀ᵐ x ∂μ, (∑' i, ENNReal.ofReal (F i x)) = ENNReal.ofReal (‖u x‖ ^ 2) := by
    filter_upwards [ae_all_iff.mpr (fun i ↦ hA (b i))] with x hx
    change ∀ i, A (b i) x = ⟪u x, b i⟫_ℂ at hx
    have hsum : HasSum (fun i ↦ F i x) (‖u x‖ ^ 2) := by
      simpa only [F, hx, ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
        b.repr_apply_apply, norm_inner_symm (b _) (u x)] using
        lp.hasSum_norm (p := 2) (by norm_num) (b.repr (u x))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _) hsum.summable, hsum.tsum_eq]
  have hcol (i : ι) : ENNReal.ofReal (‖A (b i)‖ ^ 2) = ∫⁻ x, ENNReal.ofReal (F i x) ∂μ := by
    rw [← L2.integral_sq_norm (𝕜 := ℂ), ofReal_integral_eq_lintegral_ofReal (hF i) (ae_of_all _ fun _ ↦ sq_nonneg _)]
  have hfin : (∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2)) ≠ ⊤ := by
    simp_rw [hcol]
    rw [← lintegral_tsum (fun i ↦ (hF i).aemeasurable.ennreal_ofReal), lintegral_congr_ae hpoint,
      ← ofReal_integral_eq_lintegral_ofReal ((memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu)
        (ae_of_all _ fun _ ↦ sq_nonneg _)]
    exact ENNReal.ofReal_ne_top
  have hn := ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hfin
  simpa only [Real.coe_toNNReal _ (sq_nonneg _)] using hn

variable {X H ι : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The analysis formulas are needed only on the specified countable basis.
Square integrability of the two families need not be assumed a second time:
the Hilbert–Schmidt bounds control the absolute integral sum directly. -/
theorem hilbertTrace_familyAnalysisProduct [Countable ι] (b : HilbertBasis ι ℂ H)
    (u v : X → H) (A B : hilbertSchmidtOperators H (Lp ℂ 2 μ))
    (hA : ∀ i, ∀ᵐ x ∂μ, A.val (b i) x = ⟪u x, b i⟫_ℂ)
    (hB : ∀ i, ∀ᵐ x ∂μ, B.val (b i) x = ⟪v x, b i⟫_ℂ) :
    hilbertTrace ⟨A.val.adjoint.comp B.val,
      nuclear_hilbertSchmidt_comp ⟨_, mem_hilbertSchmidtOperators_adjoint A.property⟩ B⟩ = ∫ x, ⟪v x, u x⟫_ℂ ∂μ := by
  classical
  let d (i : ι) (x : X) := ⟪A.val (b i) x, B.val (b i) x⟫_ℂ
  have hi (i : ι) : Integrable (d i) μ := L2.integrable_inner _ _
  have ha := (mem_hilbertSchmidtOperators_iff_summable_basis b A.val).1 A.property
  have hb := (mem_hilbertSchmidtOperators_iff_summable_basis b B.val).1 B.property
  have hs : Summable fun i ↦ ∫ x, ‖d i x‖ ∂μ := by
    refine ((hb.add ha).div_const 2).of_nonneg_of_le
      (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) fun i ↦ ?_
    have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
      (by simpa using Lp.memLp (B.val (b i))) (by simpa using Lp.memLp (A.val (b i)))
    simp only [← Real.sqrt_eq_rpow, Real.rpow_two, L2.integral_sq_norm (𝕜 := ℂ),
      Real.sqrt_sq (norm_nonneg _)] at h
    simp only [d, RCLike.inner_apply, norm_mul, Complex.norm_conj]
    exact h.trans ((le_div_iff₀ (by norm_num)).2 (by
      linarith only [two_mul_le_add_sq ‖B.val (b i)‖ ‖A.val (b i)‖]))
  let T := A.val.adjoint.comp B.val
  have hn : IsNuclearOperator T := nuclear_hilbertSchmidt_comp ⟨_, mem_hilbertSchmidtOperators_adjoint A.property⟩ B
  let c := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  change (∑' j, ⟪c j, T (c j)⟫_ℂ) = _
  calc
    _ = ∑' i, ⟪b i, T (b i)⟫_ℂ := tsum_hilbertDiagonal_eq c b T hn
    _ = ∑' i, ⟪A.val (b i), B.val (b i)⟫_ℂ := tsum_congr fun i ↦
      A.val.adjoint_inner_right _ _
    _ = ∫ x, ∑' i, d i x ∂μ := by
      simpa only [d, L2.inner_def] using (hasSum_integral_of_summable_integral_norm hi hs).tsum_eq
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.2 hA, ae_all_iff.2 hB] with x hx hy
      refine ((b.hasSum_inner_mul_inner (v x) (u x)).congr_fun fun i ↦ ?_).tsum_eq
      rw [show d i x = ⟪A.val (b i) x, B.val (b i) x⟫_ℂ from rfl,
        RCLike.inner_apply, hx, hy, inner_conj_symm]

end RiemannMasullo
