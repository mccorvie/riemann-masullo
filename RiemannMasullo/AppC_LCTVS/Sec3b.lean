module

public import RiemannMasullo.AppC_LCTVS.Sec3a_part2
import RiemannMasullo.ForMathlib.Analysis.Normed.Lp.lpSpace
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integral kernels

Masullo, Appendix C, §C.3.7, pp. 707–708.
-/

@[expose] public noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

namespace RiemannMasullo

variable {X : Type*}
  [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [Measure.InnerRegular μ]

-- TODO(paper-gap): The diagonal need not be product-null as asserted on p. 707.
-- For a one-point space with unit point mass, the diagonal has product measure one.

/-- Paper: (C.3.7.1), p. 708. A square-integrable kernel defines a Hilbert-Schmidt
endomorphism of L².
Deviation: The kernel is an L² class. The correspondence from (C.3.6.5)–(C.3.6.6)
uses source-first coordinates, so the operator is obtained by swapping the coordinates. -/
def integralKernelOperator (k : Lp ℂ 2 (μ.prod μ)) :
    hilbertSchmidtOperators (Lp ℂ 2 μ) (Lp ℂ 2 μ) :=
  (hilbertSchmidtOperators_equiv_Lp_prod μ μ).choose
    (Lp.compMeasurePreserving Prod.swap (Measure.measurePreserving_swap (μ := μ) (ν := μ)) k)

/-- Paper: (C.3.7.1), p. 708. The operator acts by integrating the product of the
kernel and the input function in the source variable.
Deviation: The integral is required to be defined and to give the operator value
almost everywhere in the target variable. -/
theorem integralKernelOperator_apply (k : Lp ℂ 2 (μ.prod μ)) (f : Lp ℂ 2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ k (x, y) * f y) μ ∧
      (integralKernelOperator μ k).val f x = ∫ y, k (x, y) * f y ∂μ := by
  let hswap := Measure.measurePreserving_swap (μ := μ) (ν := μ)
  let swapped := Lp.compMeasurePreserving Prod.swap hswap k
  have hkernel : ∀ᵐ p ∂(μ.prod μ), swapped p.swap = k p :=
    hswap.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving k hswap)
  filter_upwards [Measure.ae_ae_of_ae_prod hkernel,
    (hilbertSchmidtOperators_equiv_Lp_prod μ μ).choose_spec.2 swapped f] with x hx happly
  have hmul : (fun y ↦ swapped (y, x) * f y) =ᵐ[μ] fun y ↦ k (x, y) * f y := by
    filter_upwards [hx] with y hy
    exact congrArg (· * f y) hy
  exact ⟨happly.1.congr hmul, happly.2.trans (integral_congr_ae hmul)⟩

/-- Paper: Theorem C.3.7.1(1), p. 708. The Hilbert-Schmidt norm of the integral
operator is the L² norm of the kernel. -/
theorem schattenNorm_integralKernelOperator (k : Lp ℂ 2 (μ.prod μ)) :
    schattenNorm (integralKernelOperator μ k) = ‖k‖ := by
  unfold integralKernelOperator
  rw [(hilbertSchmidtOperators_equiv_Lp_prod μ μ).choose_spec.1]
  exact Lp.norm_compMeasurePreserving k (Measure.measurePreserving_swap (μ := μ) (ν := μ))

/-- The kernel correspondence is continuous in operator norm. -/
private theorem norm_integralKernelOperator_le (k : Lp ℂ 2 (μ.prod μ)) :
    ‖(integralKernelOperator μ k).val‖ ≤ ‖k‖ := by
  let A := integralKernelOperator μ k
  have hA : IsCompactOperator A.val ∧ Summable (fun n ↦ approximationNumber A.val n ^ (2 : ℝ)) :=
    A.property
  have hbound := hA.2.le_tsum 0 (fun n _ ↦ by rw [Real.rpow_two]; positivity)
  rw [approximationNumber_zero_eq_opNorm A.val hA.1, Real.rpow_two] at hbound
  rw [← schattenNorm_integralKernelOperator μ k]
  change ‖A.val‖ ≤ (∑' n, approximationNumber A.val n ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq (norm_nonneg A.val)]
  exact Real.sqrt_le_sqrt hbound

/-- The integral operator of an outer-product kernel is the corresponding rank-one map. -/
private theorem integralKernelOperator_outerProduct {K : Lp ℂ 2 (μ.prod μ)}
    {u v : Lp ℂ 2 μ} (hK : (K : X × X → ℂ) =ᵐ[μ.prod μ]
      fun p ↦ ⟪v p.2, u p.1⟫_ℂ) :
    (integralKernelOperator μ K).val = (innerSL ℂ v).smulRight u := by
  ext f : 1
  apply Lp.ext
  filter_upwards [integralKernelOperator_apply μ K f, Measure.ae_ae_of_ae_prod hK,
    Lp.coeFn_smul ⟪v, f⟫_ℂ u] with x hx hxy hsmul
  have h : (fun y ↦ K (x, y) * f y) =ᵐ[μ] fun y ↦ u x * ⟪v y, f y⟫_ℂ := by
    filter_upwards [hxy] with y hy
    rw [show K (x, y) = ⟪v y, u x⟫_ℂ from hy, RCLike.inner_apply, RCLike.inner_apply]
    ring
  change (integralKernelOperator μ K).val f x = (⟪v, f⟫_ℂ • u : Lp ℂ 2 μ) x
  rw [hx.2, integral_congr_ae h, integral_const_mul, hsmul]
  change u x * (∫ y, ⟪v y, f y⟫_ℂ ∂μ) = ⟪v, f⟫_ℂ * u x
  rw [L2.inner_def, mul_comm]

/-- Divide the summable coefficients of a nuclear presentation between its vectors and
Riesz representatives, giving two square-summable families. -/
private theorem NuclearPresentation.exists_squareSummable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {T : H →L[ℂ] H} (r : NuclearPresentation T) :
    ∃ u v : ℕ → H, (Summable fun n ↦ ‖u n‖ ^ 2) ∧ (Summable fun n ↦ ‖v n‖ ^ 2) ∧
      ∀ f, HasSum (fun n ↦ ⟪v n, f⟫_ℂ • u n) (T f) := by
  obtain ⟨C, hC, hφ⟩ :=
    ((NormedSpace.equicontinuous_tfae r.functional).out 1 7).mp r.equicontinuous
  obtain ⟨D, hD⟩ := ((NormedSpace.isVonNBounded_iff ℂ).mp r.isBanachDisc.bounded).exists_norm_le
  let d (n : ℕ) : ℝ := Real.sqrt ‖r.coeff n‖
  let c (n : ℕ) : ℂ := r.coeff n / (d n : ℂ)
  have hd (n : ℕ) : ‖(d n : ℂ)‖ = d n := by simp [d, Real.sqrt_nonneg]
  have hdsq (n : ℕ) : d n ^ 2 = ‖r.coeff n‖ := Real.sq_sqrt (norm_nonneg _)
  have hcoeff (n : ℕ) : c n * (d n : ℂ) = r.coeff n := by
    by_cases hr : r.coeff n = 0
    · simp [c, hr]
    · exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_pos.2 (norm_pos_iff.mpr hr)).ne')
  have hc (n : ℕ) : ‖c n‖ = d n := by
    rw [show ‖c n‖ = ‖r.coeff n‖ / d n from (norm_div _ _).trans (by rw [hd]), ← hdsq]
    by_cases hn : d n = 0
    · simp [hn]
    · rw [pow_two, mul_div_cancel_right₀ _ hn]
  let u (n : ℕ) : H := c n • (r.vector n : H)
  let v (n : ℕ) : H := (d n : ℂ) • (InnerProductSpace.toDual ℂ H).symm (r.functional n)
  have hvinner (n : ℕ) (f : H) : ⟪v n, f⟫_ℂ = (d n : ℂ) * r.functional n f := by
    rw [show v n = (d n : ℂ) • (InnerProductSpace.toDual ℂ H).symm (r.functional n) from rfl,
      inner_smul_left, InnerProductSpace.toDual_symm_apply]
    have hreal : (starRingEnd ℂ) (d n : ℂ) = (d n : ℂ) := by
      apply Complex.ext <;> simp
    rw [hreal]
  refine ⟨u, v, ?_, ?_, ?_⟩
  · apply (r.summable_coeff.mul_left (D ^ 2)).of_nonneg_of_le (fun _ ↦ sq_nonneg _)
    intro n
    rw [show ‖u n‖ = d n * ‖(r.vector n : H)‖ by rw [norm_smul, hc], mul_pow, hdsq, mul_comm]
    gcongr
    exact hD _ (r.vector_mem n)
  · apply (r.summable_coeff.mul_left (C ^ 2)).of_nonneg_of_le (fun _ ↦ sq_nonneg _)
    intro n
    rw [show ‖v n‖ = d n * ‖r.functional n‖ by
      rw [norm_smul, hd, LinearIsometryEquiv.norm_map], mul_pow, hdsq, mul_comm]
    gcongr
    exact hφ n
  · intro f
    refine (r.hasSum f).congr_fun fun n ↦ ?_
    rw [hvinner, show u n = c n • (r.vector n : H) from rfl, smul_smul,
      mul_right_comm, mul_comm (↑(d n) : ℂ) (c n), hcoeff]

/-- The trace of a square-summable rank-one expansion is the sum of the pairings
of its vectors. Absolute convergence permits exchanging the two sums. -/
private theorem hilbertTrace_eq_tsum_inner_of_rankOne_series {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : nuclearEndomorphisms H)
    {u v : ℕ → H} (hu : Summable fun n ↦ ‖u n‖ ^ 2) (hv : Summable fun n ↦ ‖v n‖ ^ 2)
    (hT : ∀ f, HasSum (fun n ↦ ⟪v n, f⟫_ℂ • u n) (T.val f)) :
    hilbertTrace T = ∑' n, ⟪v n, u n⟫_ℂ := by
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  let d (n : ℕ) i := ⟪v n, b i⟫_ℂ * ⟪b i, u n⟫_ℂ
  have hrow (n : ℕ) : HasSum (d n) ⟪v n, u n⟫_ℂ := by
    have h := (innerSL ℂ (v n)).hasSum (b.hasSum_repr (u n))
    simp only [map_smul, smul_eq_mul, b.repr_apply_apply, innerSL_apply_apply] at h
    exact h.congr_fun fun i ↦ mul_comm _ _
  have hcol (i : _) : HasSum (fun n ↦ d n i) ⟪b i, T.val (b i)⟫_ℂ := by
    simpa only [d, innerSL_apply_apply, inner_smul_right] using (innerSL ℂ (b i)).hasSum (hT (b i))
  have hholder : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [ENNReal.toReal_ofNat, Real.holderConjugate_iff]
    norm_num
  have hnorm (n : ℕ) : (Summable fun i ↦ ‖d n i‖) ∧ ∑' i, ‖d n i‖ ≤ ‖v n‖ * ‖u n‖ := by
    simpa only [d, norm_mul, norm_inner_symm (v n), ← b.repr_apply_apply,
      LinearIsometryEquiv.norm_map] using lp.tsum_mul_le_mul_norm hholder (b.repr (v n)) (b.repr (u n))
  have habs : Summable fun p : ℕ × _ ↦ ‖d p.1 p.2‖ := by
    apply (summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)).2
    refine ⟨fun n ↦ (hnorm n).1, ((hu.add hv).div_const 2).of_nonneg_of_le
      (fun n ↦ tsum_nonneg fun i ↦ norm_nonneg (d n i)) fun n ↦ (hnorm n).2.trans ?_⟩
    exact (le_div_iff₀ (by norm_num)).2 (by
      linarith only [two_mul_le_add_sq ‖v n‖ ‖u n‖])
  change (∑' i, ⟪b i, T.val (b i)⟫_ℂ) = _
  calc
    _ = ∑' i, ∑' n, d n i := tsum_congr fun i ↦ (hcol i).tsum_eq.symm
    _ = ∑' n, ∑' i, d n i := habs.of_norm.tsum_comm
    _ = _ := tsum_congr fun n ↦ (hrow n).tsum_eq

/-- A square-summable rank-one expansion represents the original kernel almost everywhere
by pairing the two families of coordinates in ℓ². -/
private theorem ae_eq_inner_of_rankOne_series {K : Lp ℂ 2 (μ.prod μ)}
    {u v : ℕ → Lp ℂ 2 μ} (hu : Summable fun n ↦ ‖u n‖ ^ 2)
    (hv : Summable fun n ↦ ‖v n‖ ^ 2)
    (hT : ∀ f, HasSum (fun n ↦ ⟪v n, f⟫_ℂ • u n) ((integralKernelOperator μ K).val f))
    {a b : X → lp (fun _ : ℕ ↦ ℂ) 2} (ha : ∀ᵐ x ∂μ, ∀ n, a x n = u n x)
    (hb : ∀ᵐ x ∂μ, ∀ n, b x n = v n x) :
    (K : X × X → ℂ) =ᵐ[μ.prod μ] fun p ↦ ⟪b p.2, a p.1⟫_ℂ := by
  let swap : Lp ℂ 2 (μ.prod μ) →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod μ) :=
    Lp.compMeasurePreservingₗᵢ ℂ Prod.swap Measure.measurePreserving_swap
  let e := (hilbertSchmidtOperators_equiv_Lp_prod μ μ).choose
  let L := (hilbertSchmidtOperators (Lp ℂ 2 μ) (Lp ℂ 2 μ)).subtype.comp
    (e.toLinearMap.comp swap.toLinearMap)
  let A := L.mkContinuous 1 (by
    intro k
    change ‖(integralKernelOperator μ k).val‖ ≤ 1 * ‖k‖
    rw [one_mul]
    exact norm_integralKernelOperator_le μ k)
  have hinj : Function.Injective A :=
    Subtype.val_injective.comp (e.injective.comp swap.injective)
  choose Kn hKn hnorm using fun n ↦ L2.exists_outerProduct (u n) (v n)
  have hsum : Summable fun n ↦ ‖Kn n‖ := by
    apply ((hu.add hv).div_const 2).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    intro n
    rw [hnorm]
    exact (le_div_iff₀ (by norm_num)).2 (by
      linarith only [two_mul_le_add_sq ‖u n‖ ‖v n‖])
  have hKnT : ∀ f, A (∑' n, Kn n) f = A K f := by
    intro f
    have hs := (ContinuousLinearMap.apply ℂ _ f).hasSum
      (A.hasSum hsum.of_norm.hasSum)
    have hterm (n : ℕ) : A (Kn n) f = ⟪v n, f⟫_ℂ • u n :=
      DFunLike.congr_fun (integralKernelOperator_outerProduct μ (hKn n)) f
    exact (hs.congr_fun fun n ↦ (hterm n).symm).unique (hT f)
  have heq : (∑' n, Kn n) = K := hinj (ContinuousLinearMap.ext hKnT)
  have hsumAE := Lp.hasSum_coeFn_tsum (tsum_eNorm_ne_top_iff_summable_norm.mpr hsum)
  rw [heq] at hsumAE
  filter_upwards [hsumAE, ae_all_iff.2 hKn, Measure.quasiMeasurePreserving_fst.ae ha,
    Measure.quasiMeasurePreserving_snd.ae hb] with p hp hterms hpa hpb
  refine hp.unique ((lp.hasSum_inner (b p.2) (a p.1)).congr_fun fun n ↦ ?_)
  rw [hterms n, hpa n, hpb n]

/-- Paper: Theorem C.3.7.1(2)(a), p. 708. If a square-integrable kernel is jointly
continuous at almost every diagonal point and its operator is nuclear, the diagonal
is integrable and its integral is the trace.
Deviation: The continuity and diagonal evaluation use a specified representative
of the L² kernel class. -/
theorem hilbertTrace_integralKernelOperator_of_ae_continuous {k : X × X → ℂ}
    (hk : MemLp k 2 (μ.prod μ))
    (hT : IsNuclearOperator (integralKernelOperator μ (hk.toLp k)).val)
    (hcont : ∀ᵐ x ∂μ, ContinuousAt k (x, x)) :
    Integrable (fun x ↦ k (x, x)) μ ∧
      hilbertTrace ⟨(integralKernelOperator μ (hk.toLp k)).val, hT⟩ =
        ∫ x, k (x, x) ∂μ := by
  let T := (integralKernelOperator μ (hk.toLp k)).val
  obtain ⟨r⟩ := (isNuclearOperator_iff_nonempty_presentation T).mp hT
  obtain ⟨u, v, hu, hv, hseries⟩ := r.exists_squareSummable
  obtain ⟨a, ha, ha'⟩ := L2.exists_memLp_coordinates u hu
  obtain ⟨b, hb, hb'⟩ := L2.exists_memLp_coordinates v hv
  let : SeparableSpace (lp (fun _ : ℕ ↦ ℂ) 2) := lp.separableSpace (by simp)
  let : MeasurableSpace (lp (fun _ : ℕ ↦ ℂ) 2) := borel _
  have : BorelSpace (lp (fun _ : ℕ ↦ ℂ) 2) := ⟨rfl⟩
  have hkernel := hk.coeFn_toLp.symm.trans (ae_eq_inner_of_rankOne_series μ hu hv hseries ha' hb')
  have hdiag := ae_diagonal_eq_of_ae_eq_comp_prod ha.aestronglyMeasurable.aemeasurable
    hb.aestronglyMeasurable.aemeasurable (continuous_snd.inner continuous_fst) hkernel hcont
  have hinner : Integrable (fun x ↦ ⟪b x, a x⟫_ℂ) μ := by
    apply (L2.integrable_inner (𝕜 := ℂ) (hb.toLp b) (ha.toLp a)).congr
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hx hy
    rw [hx, hy]
  refine ⟨hinner.congr hdiag.symm, ?_⟩
  rw [integral_congr_ae hdiag, hilbertTrace_eq_tsum_inner_of_rankOne_series _ hu hv hseries]
  have hInt (n : ℕ) : Integrable (fun x ↦ ⟪v n x, u n x⟫_ℂ) μ := L2.integrable_inner _ _
  have hNormSum : Summable fun n ↦ ∫ x, ‖⟪v n x, u n x⟫_ℂ‖ ∂μ := by
    have hbound : Summable fun n ↦ (‖u n‖ ^ 2 + ‖v n‖ ^ 2) / 2 := (hu.add hv).div_const 2
    apply hbound.of_nonneg_of_le (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _)
    intro n
    rw [← L2.integral_sq_norm (𝕜 := ℂ) (u n), ← L2.integral_sq_norm (𝕜 := ℂ) (v n),
      ← integral_add ((Lp.memLp (u n)).integrable_norm_pow (by decide : 2 ≠ 0))
        ((Lp.memLp (v n)).integrable_norm_pow (by decide : 2 ≠ 0)),
      ← integral_div]
    apply integral_mono (hInt n).norm
      ((((Lp.memLp (u n)).integrable_norm_pow (by decide : 2 ≠ 0)).add
        ((Lp.memLp (v n)).integrable_norm_pow (by decide : 2 ≠ 0))).div_const _)
    intro x
    apply (norm_inner_le_norm _ _).trans
    change ‖v n x‖ * ‖u n x‖ ≤ (‖u n x‖ ^ 2 + ‖v n x‖ ^ 2) / 2
    nlinarith [sq_nonneg (‖u n x‖ - ‖v n x‖)]
  have hsum := hasSum_integral_of_summable_integral_norm hInt hNormSum
  have hsumDiag : (fun x ↦ ∑' n, ⟪v n x, u n x⟫_ℂ) =ᵐ[μ] fun x ↦ ⟪b x, a x⟫_ℂ := by
    filter_upwards [ha', hb'] with x hx hy
    simpa only [hx, hy] using (lp.hasSum_inner (b x) (a x)).tsum_eq
  rw [integral_congr_ae hsumDiag] at hsum
  simpa only [L2.inner_def] using hsum.tsum_eq

/-- Paper: Theorem C.3.7.1(2)(b), p. 708. A nuclear integral operator has
Hilbert-Schmidt factors whose kernel convolution represents the original kernel.
The convolution is defined almost everywhere on the diagonal, where it is
integrable and computes the trace.
Deviation: The smoothening is expressed by the factor-kernel convolution
described on pp. 707–708. -/
theorem exists_integralKernel_smoothening (k : Lp ℂ 2 (μ.prod μ))
    (hT : IsNuclearOperator (integralKernelOperator μ k).val) :
    ∃ a b : Lp ℂ 2 (μ.prod μ),
      (integralKernelOperator μ k).val =
        (integralKernelOperator μ a).val.comp (integralKernelOperator μ b).val ∧
      let integrand (p : X × X) (z : X) := a (p.1, z) * b (z, p.2)
      let smoothened (p : X × X) := ∫ z, integrand p z ∂μ
      (∀ᵐ p ∂(μ.prod μ), Integrable (integrand p) μ ∧ smoothened p = k p) ∧
        (∀ᵐ x ∂μ, Integrable (integrand (x, x)) μ) ∧
        Integrable (fun x ↦ smoothened (x, x)) μ ∧
        hilbertTrace ⟨(integralKernelOperator μ k).val, hT⟩ =
          ∫ x, smoothened (x, x) ∂μ := by sorry

end RiemannMasullo
