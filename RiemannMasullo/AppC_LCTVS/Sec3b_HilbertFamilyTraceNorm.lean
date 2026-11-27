module

public import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertFamilyTrace
public import RiemannMasullo.AppC_LCTVS.Sec3a_part2
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Trace norm of a product of Hilbert-space-valued analysis operators

Paper: §C.3.7, pp. 707–708, the trace of a product of two Hilbert–Schmidt factors.

`Sec3b_HilbertFamilyTrace` shows that the analysis operators `A_u` and `A_v` of two
square-integrable families `u` and `v` give a nuclear operator `A_u† A_v`, and computes its
trace. This file bounds its trace norm.

* `tsum_sq_adjoint_eq_tsum_sq`. The squared norms of an operator on one Hilbert basis and of
  its adjoint on another have the same sum.
* `hasSum_sq_norm_familyAnalysis`. For the analysis operator of a family `u`, that sum is the
  integral of `‖u x‖²`.
* `exists_traceNorm_familyAnalysis_comp_le`. The trace norm of `A_u† A_v` is at most half the
  sum of the integrals of `‖u x‖²` and of `‖v x‖²`.
* `exists_traceNorm_familyAnalysis_comp_le_of_weight`. The same bound after `u` is multiplied
  by a real weight and `v` by its inverse, which leaves `A_u† A_v` unchanged.
* `exists_hasSum_hilbertTrace_of_hasSum`. A sum of nuclear operators with summable trace norms
  is nuclear, and its trace is the sum of the traces.

Reconstruction: The paper does not state the bound. It is the inequality between the trace
norm of a product and the Hilbert–Schmidt norms of its factors, in the form with the
arithmetic mean. -/

public noncomputable section

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace Topology

namespace RiemannMasullo

/-- The squared norms of an operator on a Hilbert basis and of its adjoint on another Hilbert
basis have the same sum, when the first is summable. -/
theorem tsum_sq_adjoint_eq_tsum_sq {E G ι κ : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] (b : HilbertBasis ι ℂ E)
    (f : HilbertBasis κ ℂ G) (T : E →L[ℂ] G)
    (hT : Summable (fun i ↦ ‖T (b i)‖ ^ (2 : ℕ))) :
    ∑' j, ‖T.adjoint (f j)‖ ^ (2 : ℕ) = ∑' i, ‖T (b i)‖ ^ (2 : ℕ) := by
  let c (i : ι) (j : κ) : ℝ := ‖inner ℂ (f j) (T (b i))‖ ^ (2 : ℕ)
  have hnn (i : ι) (j : κ) : 0 ≤ c i j := by positivity
  have hrow (i : ι) : HasSum (c i) (‖T (b i)‖ ^ (2 : ℕ)) :=
    hasSum_norm_inner_sq_hilbertBasis f (T (b i))
  have hcol (j : κ) : HasSum (fun i ↦ c i j) (‖T.adjoint (f j)‖ ^ (2 : ℕ)) := by
    have h := hasSum_norm_inner_sq_hilbertBasis b (T.adjoint (f j))
    convert h using 2 with i
    simp only [c]
    rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
  have hsum : Summable (Function.uncurry c) := by
    have h : Summable (fun p : ι × κ ↦ c p.1 p.2) := by
      rw [summable_prod_of_nonneg (fun p ↦ hnn p.1 p.2)]
      refine ⟨fun i ↦ (hrow i).summable, ?_⟩
      simpa only [fun i ↦ (hrow i).tsum_eq] using hT
    exact h
  calc ∑' j, ‖T.adjoint (f j)‖ ^ (2 : ℕ) = ∑' j, ∑' i, c i j :=
        tsum_congr fun j ↦ (hcol j).tsum_eq.symm
    _ = ∑' i, ∑' j, c i j :=
        hsum.tsum_comm' (fun i ↦ (hrow i).summable) (fun j ↦ (hcol j).summable)
    _ = ∑' i, ‖T (b i)‖ ^ (2 : ℕ) := tsum_congr fun i ↦ (hrow i).tsum_eq

variable {X H ι : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The squared norms of the analysis operator of a square-integrable family on a countable
Hilbert basis sum to the integral of the squared norm of the family. -/
theorem hasSum_sq_norm_familyAnalysis [Countable ι] (b : HilbertBasis ι ℂ H) {u : X → H}
    (hu : MemLp u 2 μ) :
    HasSum (fun i ↦ ‖hilbertFamilyAnalysisCLM hu (b i)‖ ^ (2 : ℕ)) (∫ x, ‖u x‖ ^ 2 ∂μ) := by
  let A := hilbertFamilyAnalysisCLM hu
  have hA : ∀ f, ⇑(A f) =ᵐ[μ] fun x ↦ ⟪u x, f⟫_ℂ := fun f ↦
    hilbertFamilyAnalysisCLM_apply_ae hu f
  have hmem := familyAnalysis_mem_hilbertSchmidtOperators b hu A hA
  have hsummable : Summable (fun i ↦ ‖A (b i)‖ ^ (2 : ℕ)) :=
    (mem_hilbertSchmidtOperators_iff_summable_basis b A).mp hmem
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
    rw [← L2.integral_sq_norm (𝕜 := ℂ),
      ofReal_integral_eq_lintegral_ofReal (hF i) (ae_of_all _ fun _ ↦ sq_nonneg _)]
  have hint : Integrable (fun x ↦ ‖u x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have heq : (∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2)) = ENNReal.ofReal (∫ x, ‖u x‖ ^ 2 ∂μ) := by
    simp_rw [hcol]
    rw [← lintegral_tsum (fun i ↦ (hF i).aemeasurable.ennreal_ofReal),
      lintegral_congr_ae hpoint,
      ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ sq_nonneg _)]
  have h2 : ENNReal.ofReal (∑' i, ‖A (b i)‖ ^ (2 : ℕ)) =
      ENNReal.ofReal (∫ x, ‖u x‖ ^ 2 ∂μ) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _) hsummable]
    exact heq
  have h3 : ∑' i, ‖A (b i)‖ ^ (2 : ℕ) = ∫ x, ‖u x‖ ^ 2 ∂μ :=
    (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg fun _ ↦ sq_nonneg _)
      (integral_nonneg fun _ ↦ sq_nonneg _)).mp h2
  rw [← h3]
  exact hsummable.hasSum

/-- Reconstruction: the product `A_u† A_v` of the analysis operators of two square-integrable
families is nuclear, and its trace norm is at most half the sum of the integrals of `‖u x‖²`
and `‖v x‖²`. The product is the sum over a Hilbert basis `e` of `L²` of the rank-one operators
`f ↦ ⟪A_v† e j, f⟫ A_u† e j`, whose trace norms are `‖A_v† e j‖ ‖A_u† e j‖`. -/
theorem exists_traceNorm_familyAnalysis_comp_le [Countable ι] (b : HilbertBasis ι ℂ H)
    {u v : X → H} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    ∃ h : IsNuclearOperator
        ((hilbertFamilyAnalysisCLM hu).adjoint.comp (hilbertFamilyAnalysisCLM hv)),
      traceNorm ⟨(hilbertFamilyAnalysisCLM hu).adjoint.comp (hilbertFamilyAnalysisCLM hv), h⟩ ≤
        ((∫ x, ‖u x‖ ^ 2 ∂μ) + ∫ x, ‖v x‖ ^ 2 ∂μ) / 2 := by
  let A := hilbertFamilyAnalysisCLM hu
  let B := hilbertFamilyAnalysisCLM hv
  obtain ⟨κ, e, -⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 μ)
  have hSA0 := hasSum_sq_norm_familyAnalysis b hu
  have hSB0 := hasSum_sq_norm_familyAnalysis b hv
  have hSA : HasSum (fun j ↦ ‖A.adjoint (e j)‖ ^ (2 : ℕ)) (∫ x, ‖u x‖ ^ 2 ∂μ) := by
    have h := tsum_sq_adjoint_eq_tsum_sq b e A hSA0.summable
    have hs : Summable (fun j ↦ ‖A.adjoint (e j)‖ ^ (2 : ℕ)) :=
      (summable_sq_basis_iff_summable_sq_adjoint b e A).mp hSA0.summable
    rw [← hSA0.tsum_eq, ← h]
    exact hs.hasSum
  have hSB : HasSum (fun j ↦ ‖B.adjoint (e j)‖ ^ (2 : ℕ)) (∫ x, ‖v x‖ ^ 2 ∂μ) := by
    have h := tsum_sq_adjoint_eq_tsum_sq b e B hSB0.summable
    have hs : Summable (fun j ↦ ‖B.adjoint (e j)‖ ^ (2 : ℕ)) :=
      (summable_sq_basis_iff_summable_sq_adjoint b e B).mp hSB0.summable
    rw [← hSB0.tsum_eq, ← h]
    exact hs.hasSum
  let S (j : κ) : nuclearEndomorphisms H :=
    ⟨(innerSL ℂ (B.adjoint (e j))).smulRight (A.adjoint (e j)),
      smulRight_mem_nuclearEndomorphisms _ _⟩
  let c (j : κ) : ℝ := (‖A.adjoint (e j)‖ ^ (2 : ℕ) + ‖B.adjoint (e j)‖ ^ (2 : ℕ)) / 2
  have hc : HasSum c (((∫ x, ‖u x‖ ^ 2 ∂μ) + ∫ x, ‖v x‖ ^ 2 ∂μ) / 2) :=
    (hSA.add hSB).div_const 2
  have hb : ∀ j, traceNorm (S j) ≤ c j := by
    intro j
    have h1 : traceNorm (S j) = ‖innerSL ℂ (B.adjoint (e j))‖ * ‖A.adjoint (e j)‖ :=
      traceNorm_smulRight _ _
    rw [h1, innerSL_apply_norm]
    change _ ≤ (‖A.adjoint (e j)‖ ^ (2 : ℕ) + ‖B.adjoint (e j)‖ ^ (2 : ℕ)) / 2
    nlinarith [sq_nonneg (‖B.adjoint (e j)‖ - ‖A.adjoint (e j)‖)]
  have hnorm : ∀ j, ‖(S j).val‖ ≤ c j := by
    intro j
    have h1 : ‖(S j).val‖ = ‖innerSL ℂ (B.adjoint (e j))‖ * ‖A.adjoint (e j)‖ :=
      ContinuousLinearMap.norm_smulRight_apply _ _
    rw [h1, innerSL_apply_norm]
    change _ ≤ (‖A.adjoint (e j)‖ ^ (2 : ℕ) + ‖B.adjoint (e j)‖ ^ (2 : ℕ)) / 2
    nlinarith [sq_nonneg (‖B.adjoint (e j)‖ - ‖A.adjoint (e j)‖)]
  have hsummable : Summable (fun j ↦ (S j).val) := Summable.of_norm_bounded hc.summable hnorm
  have hs : HasSum (fun j ↦ (S j).val) (A.adjoint.comp B) := by
    have h0 := hsummable.hasSum
    have heq : ∑' j, (S j).val = A.adjoint.comp B := by
      ext f
      have h1 := (ContinuousLinearMap.apply ℂ H f).hasSum h0
      have h2 : HasSum (fun j ↦ (S j).val f) (A.adjoint (B f)) := by
        have h3 := A.adjoint.hasSum (e.hasSum_repr (B f))
        convert h3 using 2 with j
        change ⟪B.adjoint (e j), f⟫_ℂ • A.adjoint (e j) = A.adjoint (e.repr (B f) j • e j)
        rw [map_smul, e.repr_apply_apply, ContinuousLinearMap.adjoint_inner_left]
      exact h1.unique h2
    rw [← heq]
    exact h0
  obtain ⟨h, hle⟩ := traceNorm_le_of_hasSum S (A.adjoint.comp B) hs c hc.summable hb
  exact ⟨h, hle.trans hc.tsum_eq.le⟩

/-- The matrix element of `A_u† A_v` between `z` and `f` is the integral of the product of the
pairings of `z` with `u` and of `v` with `f`. -/
theorem inner_adjoint_familyAnalysis_comp {u v : X → H} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (z f : H) :
    ⟪z, (hilbertFamilyAnalysisCLM hu).adjoint (hilbertFamilyAnalysisCLM hv f)⟫_ℂ =
      ∫ x, ⟪z, u x⟫_ℂ * ⟪v x, f⟫_ℂ ∂μ := by
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hilbertFamilyAnalysisCLM_apply_ae hu z, hilbertFamilyAnalysisCLM_apply_ae hv f]
    with x hx hy
  rw [hx, hy, RCLike.inner_apply, inner_conj_symm, mul_comm]

/-- Two pairs of families with the same products of pairings almost everywhere give the same
operator `A_u† A_v`. -/
theorem familyAnalysis_adjoint_comp_congr {u v u' v' : X → H} (hu : MemLp u 2 μ)
    (hv : MemLp v 2 μ) (hu' : MemLp u' 2 μ) (hv' : MemLp v' 2 μ)
    (h : ∀ z f : H, ∀ᵐ x ∂μ, ⟪z, u x⟫_ℂ * ⟪v x, f⟫_ℂ = ⟪z, u' x⟫_ℂ * ⟪v' x, f⟫_ℂ) :
    (hilbertFamilyAnalysisCLM hu).adjoint.comp (hilbertFamilyAnalysisCLM hv) =
      (hilbertFamilyAnalysisCLM hu').adjoint.comp (hilbertFamilyAnalysisCLM hv') := by
  refine ContinuousLinearMap.ext fun f ↦ ext_inner_left ℂ fun z ↦ ?_
  change ⟪z, (hilbertFamilyAnalysisCLM hu).adjoint (hilbertFamilyAnalysisCLM hv f)⟫_ℂ =
    ⟪z, (hilbertFamilyAnalysisCLM hu').adjoint (hilbertFamilyAnalysisCLM hv' f)⟫_ℂ
  rw [inner_adjoint_familyAnalysis_comp, inner_adjoint_familyAnalysis_comp]
  exact integral_congr_ae (h z f)

/-- Multiplying `u` by a real weight and `v` by its inverse leaves `A_u† A_v` unchanged, so the
trace norm of `A_u† A_v` is bounded through any such pair. -/
theorem exists_traceNorm_familyAnalysis_comp_le_of_weight [Countable ι]
    (b : HilbertBasis ι ℂ H) {u v : X → H} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) {w : X → ℝ}
    (hw : ∀ᵐ x ∂μ, w x ≠ 0) (hu' : MemLp (fun x ↦ ((w x : ℝ) : ℂ) • u x) 2 μ)
    (hv' : MemLp (fun x ↦ (((w x)⁻¹ : ℝ) : ℂ) • v x) 2 μ) :
    ∃ h : IsNuclearOperator
        ((hilbertFamilyAnalysisCLM hu).adjoint.comp (hilbertFamilyAnalysisCLM hv)),
      traceNorm ⟨(hilbertFamilyAnalysisCLM hu).adjoint.comp (hilbertFamilyAnalysisCLM hv), h⟩ ≤
        ((∫ x, ‖((w x : ℝ) : ℂ) • u x‖ ^ 2 ∂μ) +
          ∫ x, ‖(((w x)⁻¹ : ℝ) : ℂ) • v x‖ ^ 2 ∂μ) / 2 := by
  have heq := familyAnalysis_adjoint_comp_congr hu hv hu' hv' (fun z f ↦ by
    filter_upwards [hw] with x hx
    have hx' : ((w x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    rw [inner_smul_right, inner_smul_left, Complex.conj_ofReal, Complex.ofReal_inv]
    field_simp)
  rw [heq]
  exact exists_traceNorm_familyAnalysis_comp_le b hu' hv'

/-- The operator norm of a nuclear endomorphism is at most its trace norm. -/
theorem norm_val_le_traceNorm (T : nuclearEndomorphisms H) : ‖T.val‖ ≤ traceNorm T := by
  have hmem := (mem_traceClassOperators_iff_isNuclearOperator T.val).2 T.property
  have hsum : Summable (approximationNumber T.val) := by simpa using hmem.2
  have ht := schattenNorm_one_eq_traceNorm T
  simp only [schattenNorm, Real.rpow_one, div_one] at ht
  rw [← ht, ← approximationNumber_zero_eq_opNorm T.val hmem.1]
  exact hsum.le_tsum 0 fun n _ ↦ Real.sInf_nonneg fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _

/-- The trace norm of a scalar multiple of a nuclear endomorphism. -/
theorem traceNorm_smul_eq (c : ℂ) (T : nuclearEndomorphisms H) :
    traceNorm (c • T) = ‖c‖ * traceNorm T := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  exact (traceNorm_normedSpaceCore (H := H)).norm_smul c T

/-- A sum of nuclear operators whose trace norms have a summable majorant is nuclear, its trace
norm is at most the sum of the majorant, and its trace is the sum of the traces. -/
theorem exists_hasSum_hilbertTrace_of_hasSum {κ : Type*} (S : κ → nuclearEndomorphisms H)
    (T : H →L[ℂ] H) (hS : HasSum (fun i ↦ (S i).val) T) (c : κ → ℝ) (hc : Summable c)
    (hb : ∀ i, traceNorm (S i) ≤ c i) :
    ∃ h : IsNuclearOperator T, traceNorm ⟨T, h⟩ ≤ ∑' i, c i ∧
      HasSum (fun i ↦ hilbertTrace (S i)) (hilbertTrace ⟨T, h⟩) := by
  classical
  obtain ⟨h, hle⟩ := traceNorm_le_of_hasSum S T hS c hc hb
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  refine ⟨h, hle, ?_⟩
  change Tendsto (fun F : Finset κ ↦ ∑ i ∈ F, hilbertTrace (S i)) atTop
    (𝓝 (hilbertTrace ⟨T, h⟩))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun F ↦ ?_) (tendsto_tsum_compl_atTop_zero c)
  have hF : HasSum (fun i : {i // i ∉ F} ↦ (S i).val) (T - ∑ i ∈ F, (S i).val) :=
    (Finset.hasSum_compl_iff (f := fun i ↦ (S i).val) F).2 (by rw [sub_add_cancel]; exact hS)
  obtain ⟨hn, hnle⟩ := traceNorm_le_of_hasSum (fun i : {i // i ∉ F} ↦ S i) _ hF
    (fun i ↦ c i) (hc.subtype _) (fun i ↦ hb i)
  have hval : (⟨T - ∑ i ∈ F, (S i).val, hn⟩ : nuclearEndomorphisms H) =
      (⟨T, h⟩ : nuclearEndomorphisms H) - ∑ i ∈ F, S i :=
    Subtype.ext (by simp)
  have htrace : hilbertTrace (⟨T - ∑ i ∈ F, (S i).val, hn⟩ : nuclearEndomorphisms H) =
      hilbertTrace ⟨T, h⟩ - ∑ i ∈ F, hilbertTrace (S i) := by
    rw [hval, ← htr, map_sub, map_sum, htr]
    simp only [htr]
  rw [norm_sub_rev, ← htrace]
  exact (norm_hilbertTrace_le _).trans hnle

/-- The trace of a sum of two nuclear endomorphisms. -/
theorem hilbertTrace_add_eq (S T : nuclearEndomorphisms H) :
    hilbertTrace (S + T) = hilbertTrace S + hilbertTrace T := by
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  rw [← htr, ← htr, ← htr, map_add]

/-- The trace of a scalar multiple of a nuclear endomorphism. -/
theorem hilbertTrace_smul_eq (c : ℂ) (T : nuclearEndomorphisms H) :
    hilbertTrace (c • T) = c * hilbertTrace T := by
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  rw [← htr, ← htr, map_smul, smul_eq_mul]

/-- A series of scalar multiples of nuclear operators, with a summable majorant for the moduli
of the scalars times the trace norms, converges to a nuclear operator, and the trace of the sum
is the series of the traces. -/
theorem exists_nuclear_tsum_smul {κ : Type*} (c : κ → ℂ) (T : κ → nuclearEndomorphisms H)
    (m : κ → ℝ) (hm : Summable m) (hb : ∀ i, ‖c i‖ * traceNorm (T i) ≤ m i) :
    ∃ h : IsNuclearOperator (∑' i, c i • (T i).val),
      hilbertTrace ⟨∑' i, c i • (T i).val, h⟩ = ∑' i, c i * hilbertTrace (T i) := by
  let S : κ → nuclearEndomorphisms H := fun i ↦ c i • T i
  have hS : ∀ i, traceNorm (S i) ≤ m i := fun i ↦ by
    change traceNorm (c i • T i) ≤ m i
    rw [traceNorm_smul_eq]
    exact hb i
  have hsum : Summable fun i ↦ (S i).val :=
    Summable.of_norm_bounded hm fun i ↦ (norm_val_le_traceNorm (S i)).trans (hS i)
  obtain ⟨h, -, htr⟩ := exists_hasSum_hilbertTrace_of_hasSum S _ hsum.hasSum m hm hS
  exact ⟨h, htr.tsum_eq.symm.trans (tsum_congr fun i ↦ hilbertTrace_smul_eq (c i) (T i))⟩

end RiemannMasullo
