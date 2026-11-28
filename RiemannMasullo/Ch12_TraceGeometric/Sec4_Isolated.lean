module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
public import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertSchmidtProduct
public import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Integral.Prod
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.RegularDomination

/-! # Fixed-level quotient kernels, cutoff stability, and polar defects for §12.4

This file formalizes the fixed-level kernel construction described by dyknapp
in #7354. It replaces the factor through the flat Schwartz space with two
Hilbert–Schmidt factors. The hypotheses are continuous, uniformly bounded
evaluation on the closed level and square integrability of the masked vector
families. On the rational real-place level, the evaluation bound follows
from additive Fourier inversion on the fixed band.

Beyond the initial continuous-square cutoff theorems (`sLocalTrace_evaluationKernel`,
`sLocalTrace_projectedCutoffKernel`), this file develops four further layers:

* Section `SchattenHolderAndCutoff`: the sharp Schatten–Hölder trace-norm bound
  `‖A ∘ B‖₁ ≤ ‖A‖₂ ‖B‖₂` (`traceNorm_hilbertSchmidt_comp_le`); generalization of the
  cutoff compression to arbitrary integrable complex/signed/discontinuous cutoffs
  (including sharp indicator balls and annuli), with joint kernel continuity, collapse
  of the double diagonal integral to the reproducing diagonal `∫ ρ(z) ⟪e z, D (e z)⟫ dμ`,
  and sharp trace-norm bounds (`sLocalTrace_measurableCutoffKernel`); simultaneous
  cutoff/operator trace-norm perturbation bounds (`sLocalTrace_cutoff_perturbation_bound`);
  and smooth-vs-sharp cutoff trace equivalence under cocompact decay of the reproducing
  diagonal (`sLocalTrace_cutoff_tendsto_of_cocompact_decay`,
  `sLocalTrace_cutoff_tendsto_of_cocompact_decay_ae`).
* Section `SubspacePolarDefect`: orthogonal splitting of cutoff compression traces along
  closed sublevels `W ≤ V` (`sLocalTrace_subspace_compression_split`); convergence of the
  finite-codimension trace defect to the linear trace on `V ⊓ Wᗮ` along any uniformly
  bounded cutoff family `ρ_i → 1` a.e. (`sLocalTrace_finiteCodim_defect_tendsto`); and
  exact identification of the trace defect with `∑ k, A k k` (respectively `∑ k, ev k`)
  for any finite linearly independent family of `D`-invariant or eigenfunctional constraints
  (`sLocalTrace_invariantFunctionals_defect_tendsto`,
  `sLocalTrace_eigenfunctionals_defect_tendsto`), without requiring orthogonal Riesz vectors.
* Section `DensityTwistTransport`: conversion of weighted-space (`ν = w · μ`) kernels and
  traces to a jointly continuous twisted kernel `α(x) α(y)⁻¹ w(y) k_ν(x, y)` relative to
  the reference measure `μ` (`sLocalTrace_densityTwist_kernel`).
* Section `SharpComparisonAndPolarDefect`: direct bridge on `SIdeleQuotient F S` to
  `sLocalTrace_asymptotic_of_sharp_comparison`, `sLocalTraceLift_global_polar_sum`, and
  `sLocalTraceLift_global_norm_integral`, giving the normalized Hilbert-trace asymptotic
  (`sLocalTrace_weightedCutoff_asymptotic_of_sharp_comparison`) and the exact two-pole and
  single-pole sublevel asymptotic defects (`sLocalTrace_polarSublevel_asymptotic_defect`,
  `sLocalTrace_singlePolarSublevel_asymptotic_defect`) for every number field `F` and finite
  set of places `S`. -/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped ComplexConjugate ENNReal InnerProductSpace Topology

namespace RiemannMasullo.Isolated

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] [Measure.InnerRegular μ]

local notation "H" => Lp ℂ 2 μ

/-- An evaluable family of square-integrable vectors gives a square-integrable scalar kernel. -/
private theorem memLp_evaluation_kernel
    {e u : X → H} (he : Continuous e) (hu : Continuous u) (hu₂ : MemLp u 2 μ)
    (hrep : ∀ z, (fun x ↦ ⟪e x, u z⟫_ℂ) =ᵐ[μ] (u z : X → ℂ)) :
    MemLp (fun p : X × X ↦ ⟪e p.1, u p.2⟫_ℂ) 2 (μ.prod μ) := by
  have hm : StronglyMeasurable (fun p : X × X ↦ ⟪e p.1, u p.2⟫_ℂ) :=
    ((he.comp continuous_fst).inner (hu.comp continuous_snd)).stronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have hswap := Measure.measurePreserving_swap (μ := μ) (ν := μ)
  have hms : StronglyMeasurable (fun p : X × X ↦ ‖⟪e p.2, u p.1⟫_ℂ‖ ^ 2) :=
    (hm.comp_measurable measurable_swap).norm.pow 2
  have h : Integrable (fun p : X × X ↦ ‖⟪e p.2, u p.1⟫_ℂ‖ ^ 2) (μ.prod μ) := by
    apply (integrable_prod_iff hms.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall fun z ↦ ?_, ?_⟩
    · exact ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (u z))).mp
        (Lp.memLp (u z))).congr ((hrep z).symm.mono fun _ h ↦ congrArg (fun t : ℂ ↦ ‖t‖ ^ 2) h)
    · have hU := (memLp_two_iff_integrable_sq_norm hu₂.aestronglyMeasurable).mp hu₂
      refine hU.congr (Eventually.of_forall fun z ↦ ?_)
      change ‖u z‖ ^ 2 = ∫ y, ‖‖⟪e y, u z⟫_ℂ‖ ^ 2‖ ∂μ
      rw [← L2.integral_sq_norm (𝕜 := ℂ) (u z)]
      apply integral_congr_ae
      filter_upwards [hrep z] with y hy
      change ‖(u z) y‖ ^ 2 = ‖‖⟪e y, u z⟫_ℂ‖ ^ 2‖
      rw [hy, Real.norm_of_nonneg (sq_nonneg _)]
  exact hswap.integrable_comp_of_integrable h

/-- A subspace-valued Bochner integral gives a kernel row after pairing. -/
private theorem inner_integral_kernel_row {Z : Type*} {m : MeasurableSpace Z}
    {ν : Measure Z} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (V : Submodule ℂ E) [CompleteSpace V] (a : Z → ℂ) (v : Z → V)
    (hint : Integrable (fun z ↦ conj (a z) • v z) ν) (f : E) :
    ⟪((∫ z, conj (a z) • v z ∂ν : V) : E), f⟫_ℂ =
      ∫ z, a z * ⟪(v z : E), f⟫_ℂ ∂ν := by
  let L : V →L[ℝ] ℂ := (Complex.conjCLE.toContinuousLinearMap).comp
    (((innerSL ℂ f).comp V.subtypeL).restrictScalars ℝ)
  calc
    _ = L (∫ z, conj (a z) • v z ∂ν) := (inner_conj_symm _ _).symm
    _ = ∫ z, L (conj (a z) • v z) ∂ν := (L.integral_comp_comm hint).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      change conj ⟪f, conj (a z) • (v z : E)⟫_ℂ = _
      rw [inner_smul_right, map_mul, Complex.conj_conj, inner_conj_symm]

/-- The row family is Bochner integrable by Cauchy–Schwarz. -/
private theorem integrable_kernel_row {E G : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (f : E) {u : X → E} {v : X → G} (hu : Continuous u) (hv : Continuous v)
    (hnorm : Integrable (fun z ↦ ‖u z‖ * ‖v z‖) μ) :
    Integrable (fun z ↦ conj ⟪f, u z⟫_ℂ • v z) μ := by
  have hcont : Continuous (fun z ↦ ⟪f, u z⟫_ℂ) := continuous_const.inner hu
  refine (hnorm.const_mul ‖f‖).mono'
    ((Complex.continuous_conj.comp hcont).smul hv).aestronglyMeasurable ?_
  filter_upwards with z
  rw [norm_smul, Complex.norm_conj, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)

/-- The kernel composition is continuous for a uniformly bounded evaluation family. -/
private theorem continuous_evaluation_kernel {E G : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    {e : X → E} {d : X → G} {u : X → E} {v : X → G}
    (he : Continuous e) (hd : Continuous d) (hu : Continuous u) (hv : Continuous v)
    (C : ℝ) (heC : ∀ x, ‖e x‖ ≤ C) (hdC : ∀ x, ‖d x‖ ≤ C)
    (hnorm : Integrable (fun z ↦ ‖u z‖ * ‖v z‖) μ) :
    Continuous (fun p : X × X ↦ ∫ z, ⟪e p.1, u z⟫_ℂ * ⟪v z, d p.2⟫_ℂ ∂μ) := by
  apply continuous_of_dominated (bound := fun z ↦ C * C * (‖u z‖ * ‖v z‖))
  · intro p
    exact ((continuous_const.inner hu).mul (hv.inner continuous_const)).aestronglyMeasurable
  · intro p
    filter_upwards with z
    rw [norm_mul]
    have hx := (norm_inner_le_norm (𝕜 := ℂ) (e p.1) (u z)).trans
      (mul_le_mul_of_nonneg_right (heC p.1) (norm_nonneg _))
    have hy := (norm_inner_le_norm (𝕜 := ℂ) (v z) (d p.2)).trans
      (mul_le_mul_of_nonneg_left (hdC p.2) (norm_nonneg _))
    calc
      _ ≤ (C * ‖u z‖) * (‖v z‖ * C) :=
        mul_le_mul hx hy (norm_nonneg _) (le_trans (norm_nonneg _) hx)
      _ = _ := by ring
  · exact hnorm.const_mul _
  · exact Eventually.of_forall fun z ↦
      ((he.comp continuous_fst).inner continuous_const).mul
        (continuous_const.inner (hd.comp continuous_snd))

/-- Paper: Theorem 12.4.1.1, pp. 515–517. At a fixed Hilbert level with bounded,
continuous evaluations, two square-integrable families of level vectors define a
nuclear operator with a continuous quotient kernel and an absolutely integrable
diagonal. The diagonal integral equals its Hilbert trace.
Reconstruction: The factorized kernel represents the cutoff dilation compression
when the two families are the cutoff-weighted evaluation vector and the
cutoff-weighted adjoint dilation average of the evaluation vector, respectively.
Deviation: This is a fixed-level result with evaluation and integrability hypotheses.
It gives no comparison with the sharp orbital masses as the levels change. -/
theorem sLocalTrace_evaluationKernel
    (V : Submodule ℂ H) [CompleteSpace V]
    (e u : X → H) (v : X → V)
    (he : Continuous e) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C)
    (hu : Continuous u) (hu₂ : MemLp u 2 μ) (huV : ∀ z, u z ∈ V)
    (hv : Continuous v) (hv₂ : MemLp v 2 μ)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, (f : H)⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ)) :
    let k (p : X × X) := ∫ z, ⟪e p.1, u z⟫_ℂ * ⟪(v z : H), e p.2⟫_ℂ ∂μ
    ∃ (T : H →L[ℂ] H) (hT : IsNuclearOperator T),
      (∀ f : H, ∀ᵐ x ∂μ, T f x = ∫ z, ⟪e x, u z⟫_ℂ * ⟪(v z : H), f⟫_ℂ ∂μ) ∧
      Continuous k ∧
      (∀ f : H, ∀ᵐ x ∂μ, Integrable (fun y ↦ k (x, y) * f y) μ ∧
        T f x = ∫ y, k (x, y) * f y ∂μ) ∧
      Integrable (fun x ↦ k (x, x)) μ ∧
      hilbertTrace ⟨T, hT⟩ = ∫ x, k (x, x) ∂μ := by
  intro k
  let a (p : X × X) := ⟪e p.1, u p.2⟫_ℂ
  let b (p : X × X) := ⟪(v p.1 : H), e p.2⟫_ℂ
  have ha : MemLp a 2 (μ.prod μ) := memLp_evaluation_kernel he hu hu₂
    (fun z ↦ hrep ⟨u z, huV z⟩)
  have hV : MemLp (fun z ↦ (v z : H)) 2 μ := V.subtypeL.comp_memLp' hv₂
  have hv' : Continuous (fun z ↦ (v z : H)) := V.subtypeL.continuous.comp hv
  have hB := memLp_evaluation_kernel he hv' hV (fun z ↦ hrep (v z))
  have hB' := hB.comp_measurePreserving (Measure.measurePreserving_swap (μ := μ) (ν := μ))
  have hb : MemLp b 2 (μ.prod μ) := hB'.congr_norm
    ((hv'.comp continuous_fst).inner (he.comp continuous_snd)).aestronglyMeasurable
    (Eventually.of_forall fun p ↦ (norm_inner_symm (𝕜 := ℂ) _ _).symm)
  let A := integralKernelOperator μ (ha.toLp a)
  let B := integralKernelOperator μ (hb.toLp b)
  let T := A.val.comp B.val
  have hT : IsNuclearOperator T := nuclear_hilbertSchmidt_comp A B
  have hBe (f : H) : ∀ᵐ z ∂μ, B.val f z = ⟪(v z : H), f⟫_ℂ := by
    filter_upwards [integralKernelOperator_apply μ (hb.toLp b) f,
      Measure.ae_ae_of_ae_prod hb.coeFn_toLp] with z hz hbz
    rw [hz.2, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hbz, hrep (v z)] with y hy hy'
    rw [show (hb.toLp b : Lp ℂ 2 (μ.prod μ)) (z,y) = b (z,y) from hy,
      show b (z,y) = conj (⟪e y, (v z : H)⟫_ℂ) from (inner_conj_symm _ _).symm,
      hy', RCLike.inner_apply, mul_comm]
  have hTf (f : H) :
      ∀ᵐ x ∂μ, T f x = ∫ z, a (x,z) * ⟪(v z : H), f⟫_ℂ ∂μ := by
    filter_upwards [integralKernelOperator_apply μ (ha.toLp a) (B.val f),
      Measure.ae_ae_of_ae_prod ha.coeFn_toLp] with x hx hax
    change A.val (B.val f) x = _
    rw [hx.2]
    apply integral_congr_ae
    filter_upwards [hax, hBe f] with z hz hz'
    rw [show (ha.toLp a : Lp ℂ 2 (μ.prod μ)) (x,z) = a (x,z) from hz, hz']
  have hnorm : Integrable (fun z ↦ ‖u z‖ * ‖v z‖) μ :=
    hu₂.norm.integrable_mul hv₂.norm
  have hnorm' : Integrable (fun z ↦ ‖u z‖ * ‖(v z : H)‖) μ := hnorm
  have hk : Continuous k := continuous_evaluation_kernel he he hu hv' C hC hC hnorm'
  let w (x : X) : V := ∫ z, conj (a (x,z)) • v z ∂μ
  have hwPair (x : X) (f : H) :
      ⟪(w x : H), f⟫_ℂ = ∫ z, a (x,z) * ⟪(v z : H), f⟫_ℂ ∂μ :=
    inner_integral_kernel_row V (fun z ↦ a (x,z)) v
      (integrable_kernel_row (e x) hu hv hnorm) f
  have hmass : Integrable (fun p : X × X ↦ a p * b p.swap) (μ.prod μ) :=
    ha.integrable_mul (hb.comp_measurePreserving (Measure.measurePreserving_swap (μ := μ) (ν := μ)))
  have hdiag := hmass.integral_prod_left
  refine ⟨T, hT, hTf, hk, ?_, hdiag, ?_⟩
  · intro f
    filter_upwards [hTf f] with x hx
    have heq : (fun y ↦ conj ((w x : H) y) * f y) =ᵐ[μ] fun y ↦ k (x,y) * f y := by
      filter_upwards [hrep (w x)] with y hy
      rw [← hy, inner_conj_symm, hwPair]
    refine ⟨(L2.integrable_inner (w x : H) f).congr ?_, ?_⟩
    · exact heq.mono fun _ h ↦ by simpa only [RCLike.inner_apply, mul_comm] using h
    · rw [hx, ← hwPair, L2.inner_def]
      exact integral_congr_ae (heq.mono fun _ h ↦ by simpa only [RCLike.inner_apply, mul_comm] using h)
  · change hilbertTrace ⟨A.val.comp B.val, hT⟩ = _
    rw [hilbertTrace_integralKernelOperator_comp]
    change _ = ∫ x, ∫ y, a (x,y) * b (x,y).swap ∂μ ∂μ
    rw [← integral_prod _ hmass]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp,
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hb.coeFn_toLp]
      with p hp hq
    rw [show (ha.toLp a : Lp ℂ 2 (μ.prod μ)) p = a p from hp, hq]

/-- Paper: Theorem 12.4.1.1, pp. 515–517. The orthogonal compression of a spatial
cutoff and a bounded action preserving an evaluable Hilbert level admits a
continuous integral kernel. Its diagonal is integrable and computes its trace.
Reconstruction: The two projections specify the meaning of compression on the
fixed level. The kernel is constructed directly on the quotient Hilbert space.
Deviation: The operator on the level is assumed bounded, evaluation is assumed
uniformly bounded and continuous, and the density is included in the measure
`μ`. The cutoff is written as a square, with its square root in L². -/
theorem sLocalTrace_projectedCutoffKernel
    (V : Submodule ℂ H) [CompleteSpace V]
    (e : X → V) (he : Continuous e) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, f⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ))
    (c : X → ℝ) (hc : Continuous c) (hc₂ : MemLp c 2 μ)
    (M : H →L[ℂ] H) (hM : ∀ f : H, ∀ᵐ x ∂μ, M f x = c x ^ 2 • f x)
    (D : V →L[ℂ] V) :
    let j := V.subtypeL
    let q := V.orthogonalProjectionOnto
    let L := q.comp (M.comp (j.comp D))
    let T := j.comp (L.comp q)
    let k (p : X × X) := ∫ z,
      (c z ^ 2 : ℝ) • (⟪e p.1, e z⟫_ℂ * ⟪e z, D (e p.2)⟫_ℂ) ∂μ
    ∃ (hT : IsNuclearOperator T) (hL : IsNuclearOperator L),
      Continuous k ∧
      (∀ f : H, ∀ᵐ x ∂μ, Integrable (fun y ↦ k (x, y) * f y) μ ∧
        T f x = ∫ y, k (x, y) * f y ∂μ) ∧
      Integrable (fun x ↦ k (x, x)) μ ∧
      hilbertTrace ⟨T, hT⟩ = (∫ x, k (x, x) ∂μ) ∧
      hilbertTrace ⟨L, hL⟩ = ∫ x, k (x, x) ∂μ := by
  intro j q L T k
  let u₀ (z : X) : V := c z • e z
  let v (z : X) : V := c z • D.adjoint (e z)
  let u (z : X) : H := j (u₀ z)
  have hu₀ : Continuous u₀ := hc.smul he
  have hu : Continuous u := j.continuous.comp hu₀
  have hv : Continuous v := hc.smul (D.adjoint.continuous.comp he)
  have hu₀₂ : MemLp u₀ 2 μ := by
    refine (hc₂.norm.const_smul C).mono' hu₀.aestronglyMeasurable (Eventually.of_forall fun z ↦ ?_)
    change ‖c z • e z‖ ≤ C * ‖c z‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC z) (norm_nonneg (c z)) |>.trans_eq (mul_comm _ _)
  have hv₂ : MemLp v 2 μ := by
    refine (hc₂.norm.const_smul (‖D.adjoint‖ * C)).mono' hv.aestronglyMeasurable
      (Eventually.of_forall fun z ↦ ?_)
    change ‖c z • D.adjoint (e z)‖ ≤ (‖D.adjoint‖ * C) * ‖c z‖
    rw [norm_smul, mul_comm ‖c z‖]
    exact mul_le_mul_of_nonneg_right ((D.adjoint.le_opNorm (e z)).trans
      (mul_le_mul_of_nonneg_left (hC z) (norm_nonneg _))) (norm_nonneg _)
  obtain ⟨U, hU, hUapply, hcont, hkernel, hdiag, htrace⟩ :=
    sLocalTrace_evaluationKernel V (fun x ↦ j (e x)) u v (j.continuous.comp he)
      C hC hu (j.comp_memLp' hu₀₂) (fun z ↦ (u₀ z).property) hv hv₂ hrep
  have hpair (z : X) (f : H) : ⟪(v z : H), f⟫_ℂ = c z • ⟪e z, D (q f)⟫_ℂ := by
    have h := V.inner_orthogonalProjectionOnto_eq_of_mem_left (v z) f
    rw [← h]
    change ⟪(c z : ℂ) • D.adjoint (e z), q f⟫_ℂ = _
    rw [inner_smul_left, D.adjoint_inner_left, Complex.conj_ofReal, Complex.real_smul]
  have hout (x z : X) : ⟪j (e x), u z⟫_ℂ = c z • ⟪e x, e z⟫_ℂ := by
    change ⟪e x, (c z : ℂ) • e z⟫_ℂ = _
    exact inner_smul_real_right _ _ _
  have hsc (z : X) (a b : ℂ) : (c z • a) * (c z • b) = (c z ^ 2 : ℝ) • (a * b) := by
    simp only [Complex.real_smul, Complex.ofReal_pow]
    ring
  have heq : T = U := by
    apply ContinuousLinearMap.ext
    intro f
    let d := D (q f)
    let g := M (j d)
    apply Lp.ext
    filter_upwards [hrep (q g), hUapply f] with x hx hux
    change (q g : H) x = U f x
    rw [← hx, V.inner_orthogonalProjectionOnto_eq_of_mem_left, hux, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrep d, hrep (e x), hM (j d)] with z hdz hxz hz
    rw [hout, hpair, hsc]
    change ⟪(e x : H) z, g z⟫_ℂ = _
    change ⟪e z, d⟫_ℂ = (j d) z at hdz
    rw [show g z = _ from hz, ← hdz, ← hxz, RCLike.inner_apply, inner_conj_symm]
    simp only [Complex.real_smul]
    ring
  have hk (p : X × X) :
      (∫ z, ⟪j (e p.1), u z⟫_ℂ * ⟪(v z : H), j (e p.2)⟫_ℂ ∂μ) = k p := by
    apply integral_congr_ae
    filter_upwards with z
    rw [hout, hpair, hsc]
    rw [show q (j (e p.2)) = e p.2 from V.orthogonalProjectionOnto_mem_subspace_eq_self _]
  have hk' : (fun p : X × X ↦
      ∫ z, ⟪j (e p.1), u z⟫_ℂ * ⟪(v z : H), j (e p.2)⟫_ℂ ∂μ) = k := funext hk
  rw [hk'] at hcont hkernel hdiag htrace
  have hT : IsNuclearOperator T := heq ▸ hU
  have hTtrace : hilbertTrace ⟨T, hT⟩ = ∫ x, k (x, x) ∂μ :=
    (congrArg hilbertTrace (Subtype.ext heq)).trans htrace
  have hqj (f : V) : q (j f) = f := V.orthogonalProjectionOnto_mem_subspace_eq_self f
  have hqT : q.comp T = L.comp q := by
    ext f : 1
    exact hqj (L (q f))
  have hLq : IsNuclearOperator (L.comp q) := by
    rw [← hqT]
    obtain ⟨a, l, y, ha, hl, hy, hs⟩ := (isNuclearOperator_iff_isBanachNuclear T).mp hT
    apply (isNuclearOperator_iff_isBanachNuclear _).mpr
    refine ⟨a, l, q ∘ y, ha, hl, ?_, fun x ↦ ?_⟩
    · simpa only [map_zero] using (q.continuous.tendsto 0).comp hy
    · simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, map_smul] using
        q.hasSum (hs x)
  have hj : Function.Injective j := Subtype.val_injective
  have hLqj : (L.comp q).comp j = L := by
    ext f : 1
    exact congrArg L (hqj f)
  have hL : IsNuclearOperator L := hLqj ▸ (isNuclearOperator_factor_comps j hj _ hLq).1
  refine ⟨hT, hL, hcont, heq ▸ hkernel, hdiag, hTtrace, ?_⟩
  rw [← hTtrace, hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
  have hn := nuclearTrace_factor_comps hilbert_approximationProperty
    hilbert_approximationProperty j hj _ hLq
  simpa only [hLqj] using hn

section SchattenHolderAndCutoff

/-- On a source singular vector, a compact operator scales the matching target vector. -/
private theorem singularExpansion_apply_source {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {T : E →L[ℂ] F} (d : SingularExpansion T) (j : {n // d.coeff n ≠ 0}) :
    T (d.source j) = ((d.coeff j : ℝ) : ℂ) • d.target j := by
  have h := d.hasSum_apply (d.source j)
  have hsingle : HasSum
      (fun n : {n // d.coeff n ≠ 0} ↦
        (((d.coeff n : ℝ) : ℂ) * ⟪d.source n, d.source j⟫_ℂ) • d.target n)
      (((d.coeff j : ℝ) : ℂ) • d.target j) := by
    convert hasSum_single j (fun k hk ↦ ?_) using 1
    · rw [inner_self_eq_norm_sq_to_K, d.orthonormal_source.1 j]
      simp
    · rw [d.orthonormal_source.2 hk, mul_zero, zero_smul]
  exact h.unique hsingle

/-- The adjoint of a compact operator has a singular expansion with the same singular values
and swapped source and target families. -/
private def singularExpansion_adjoint {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {T : E →L[ℂ] F} (d : SingularExpansion T) : SingularExpansion T.adjoint where
  coeff := d.coeff
  antitone_coeff := d.antitone_coeff
  tendsto_coeff := d.tendsto_coeff
  source := d.target
  target := d.source
  orthonormal_source := d.orthonormal_target
  orthonormal_target := d.orthonormal_source
  hasSum_apply x := by
    have hadj : HasSum (fun n : {n // d.coeff n ≠ 0} ↦
        ((((d.coeff n : ℝ) : ℂ) •
          (innerSL ℂ (d.source n)).smulRight (d.target n)).adjoint)) T.adjoint := by
      change Tendsto (fun s : Finset {n // d.coeff n ≠ 0} ↦ ∑ n ∈ s,
        ((((d.coeff n : ℝ) : ℂ) •
          (innerSL ℂ (d.source n)).smulRight (d.target n)).adjoint)) atTop (𝓝 T.adjoint)
      have hcomp := (ContinuousLinearMap.adjoint.continuous.tendsto T).comp d.hasSum_opNorm
      refine hcomp.congr fun s ↦ ?_
      change ContinuousLinearMap.adjoint (∑ n ∈ s, _) = _
      exact map_sum ContinuousLinearMap.adjoint _ s
    have happ := (ContinuousLinearMap.apply ℂ E x).hasSum hadj
    refine happ.congr_fun fun n ↦ ?_
    apply ext_inner_right ℂ
    intro y
    symm
    change ⟪(((((d.coeff n : ℝ) : ℂ) •
      (innerSL ℂ (d.source n)).smulRight (d.target n)).adjoint) x), y⟫_ℂ = _
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, inner_smul_right, inner_smul_left, map_mul, Complex.conj_ofReal,
      inner_conj_symm]
    ring

/-- The squared norm of a compact operator on any vector is given by its singular expansion. -/
private theorem singularExpansion_hasSum_norm_sq {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {T : E →L[ℂ] F} (d : SingularExpansion T) (x : E) :
    HasSum (fun n : {n // d.coeff n ≠ 0} ↦
      (d.coeff n : ℝ) ^ 2 * ‖⟪d.source n, x⟫_ℂ‖ ^ 2) (‖T x‖ ^ 2) := by
  let c (n : {n // d.coeff n ≠ 0}) : ℂ := ((d.coeff n : ℝ) : ℂ) * ⟪d.source n, x⟫_ℂ
  have hnorm (s : Finset {n // d.coeff n ≠ 0}) :
      ‖∑ n ∈ s, c n • d.target n‖ ^ 2 = ∑ n ∈ s, (d.coeff n : ℝ) ^ 2 * ‖⟪d.source n, x⟫_ℂ‖ ^ 2 := by
    simpa only [LinearIsometry.toSpanSingleton_apply, c, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (NNReal.coe_nonneg _), mul_pow] using
      d.orthonormal_target.orthogonalFamily.norm_sum c s
  exact ((d.hasSum_apply x).norm.pow 2).congr hnorm

/-- On any finite orthonormal family, the sum of squared image norms of a Hilbert–Schmidt
operator is at most its squared Hilbert–Schmidt norm. -/
private theorem sum_norm_sq_apply_le_schattenNorm_sq {E F ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {T : E →L[ℂ] F} (d : SingularExpansion T)
    (hs : Summable (fun n ↦ (d.coeff n : ℝ) ^ 2))
    {u : ι → E} (hu : Orthonormal ℂ u) (s : Finset ι) :
    ∑ i ∈ s, ‖T (u i)‖ ^ 2 ≤ ∑' n, (d.coeff n : ℝ) ^ 2 := by
  let J := {n // d.coeff n ≠ 0}
  have hJ : Summable (fun n : J ↦ (d.coeff n : ℝ) ^ 2) := hs.subtype _
  have hterm (i : ι) :
      Summable (fun n : J ↦ (d.coeff n : ℝ) ^ 2 * ‖⟪d.source n, u i⟫_ℂ‖ ^ 2) :=
    (singularExpansion_hasSum_norm_sq d (u i)).summable
  have hsum :
      (∑ i ∈ s, ‖T (u i)‖ ^ 2) =
        ∑' n : J, (d.coeff n : ℝ) ^ 2 * ∑ i ∈ s, ‖⟪u i, d.source n⟫_ℂ‖ ^ 2 := by
    calc
      ∑ i ∈ s, ‖T (u i)‖ ^ 2
          = ∑ i ∈ s, ∑' n : J, (d.coeff n : ℝ) ^ 2 * ‖⟪d.source n, u i⟫_ℂ‖ ^ 2 :=
            Finset.sum_congr rfl fun i _ ↦ (singularExpansion_hasSum_norm_sq d (u i)).tsum_eq.symm
      _ = ∑' n : J, ∑ i ∈ s, (d.coeff n : ℝ) ^ 2 * ‖⟪d.source n, u i⟫_ℂ‖ ^ 2 :=
            (Summable.tsum_finsetSum fun i _ ↦ hterm i).symm
      _ = ∑' n : J, (d.coeff n : ℝ) ^ 2 * ∑ i ∈ s, ‖⟪u i, d.source n⟫_ℂ‖ ^ 2 := by
            refine tsum_congr fun n ↦ ?_
            rw [← Finset.mul_sum]
            refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
            rw [norm_inner_symm]
  have hle :
      (∑' n : J, (d.coeff n : ℝ) ^ 2 * ∑ i ∈ s, ‖⟪u i, d.source n⟫_ℂ‖ ^ 2) ≤
        ∑' n : J, (d.coeff n : ℝ) ^ 2 := by
    refine Summable.tsum_le_tsum (fun n ↦ ?_) ?_ hJ
    · have hb := (hu.sum_inner_products_le (s := s) (d.source n)).trans_eq
        (by rw [d.orthonormal_source.norm_eq_one n, one_pow])
      exact (mul_le_mul_of_nonneg_left hb (sq_nonneg _)).trans_eq (mul_one _)
    · exact hJ.of_nonneg_of_le (fun n ↦ mul_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)) fun n ↦
        (mul_le_mul_of_nonneg_left ((hu.sum_inner_products_le (s := s) (d.source n)).trans_eq
          (by rw [d.orthonormal_source.norm_eq_one n, one_pow])) (sq_nonneg _)).trans_eq
          (mul_one _)
  have hsub : (∑' n : J, (d.coeff n : ℝ) ^ 2) = ∑' n : ℕ, (d.coeff n : ℝ) ^ 2 := by
    have hsupp : Function.support (fun n ↦ (d.coeff n : ℝ) ^ 2) ⊆ {n | d.coeff n ≠ 0} := by
      intro n hn hz
      exact hn (by simp [hz])
    exact ((hasSum_subtype_iff_of_support_subset hsupp).mp hJ.hasSum).tsum_eq.symm
  exact hsum.le.trans (hle.trans_eq hsub)

/-- Paper: Theorem C.3.6.5, p. 705, and Theorem 12.4.1.1, pp. 515–517. The trace norm of the
composite of two Hilbert–Schmidt operators is bounded by the product of their Hilbert–Schmidt
norms (`‖A ∘ B‖₁ ≤ ‖A‖₂ ‖B‖₂`).
Reconstruction: `Sec3b_HilbertSchmidtProduct.comp_mem_traceClass` proves membership in the trace
class via `2ab ≤ a² + b²`, without an explicit trace-norm inequality. This supplies the sharp
Cauchy–Schwarz Schatten–Hölder bound directly from singular value expansions and Bessel's
inequality, with no separability hypothesis. -/
theorem traceNorm_hilbertSchmidt_comp_le {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : hilbertSchmidtOperators F E) (B : hilbertSchmidtOperators E F) :
    traceNorm ⟨A.val.comp B.val, nuclear_hilbertSchmidt_comp A B⟩ ≤
      schattenNorm A * schattenNorm B := by
  let T := A.val.comp B.val
  have hT : IsNuclearOperator T := nuclear_hilbertSchmidt_comp A B
  obtain ⟨d⟩ := (isCompactOperator_iff_nonempty_singularExpansion T).mp
    (comp_mem_traceClass A B).1
  obtain ⟨dA⟩ := (isCompactOperator_iff_nonempty_singularExpansion A.val).mp A.property.1
  obtain ⟨dB⟩ := (isCompactOperator_iff_nonempty_singularExpansion B.val).mp B.property.1
  have hsA : Summable (fun n ↦ (dA.coeff n : ℝ) ^ 2) := by
    simpa only [Real.rpow_two, dA.coeff_eq_approximationNumber] using A.property.2
  have hsB : Summable (fun n ↦ (dB.coeff n : ℝ) ^ 2) := by
    simpa only [Real.rpow_two, dB.coeff_eq_approximationNumber] using B.property.2
  have hschA : schattenNorm A = Real.sqrt (∑' n, (dA.coeff n : ℝ) ^ 2) := by
    rw [schattenNorm, ← Real.sqrt_eq_rpow]
    congr 1
    exact tsum_congr fun n ↦ by rw [Real.rpow_two, dA.coeff_eq_approximationNumber]
  have hschB : schattenNorm B = Real.sqrt (∑' n, (dB.coeff n : ℝ) ^ 2) := by
    rw [schattenNorm, ← Real.sqrt_eq_rpow]
    congr 1
    exact tsum_congr fun n ↦ by rw [Real.rpow_two, dB.coeff_eq_approximationNumber]
  have htr : traceNorm ⟨T, hT⟩ = ∑' n : {n // d.coeff n ≠ 0}, (d.coeff n : ℝ) := by
    rw [← schattenNorm_one_eq_traceNorm ⟨T, hT⟩, schattenNorm]
    simp only [Real.rpow_one, div_one]
    have hEq : (fun n ↦ approximationNumber T n) = fun n ↦ (d.coeff n : ℝ) :=
      funext fun n ↦ (d.coeff_eq_approximationNumber n).symm
    rw [hEq]
    have hsupp : Function.support (fun n ↦ (d.coeff n : ℝ)) ⊆ {n | d.coeff n ≠ 0} := by
      intro n hn hz
      exact hn (by simp [hz])
    have hsT : Summable (fun n ↦ (d.coeff n : ℝ)) := by
      simpa only [Real.rpow_one, d.coeff_eq_approximationNumber] using
        (mem_traceClassOperators_iff_isNuclearOperator T).mpr hT |>.2
    exact ((hasSum_subtype_iff_of_support_subset hsupp).mpr hsT.hasSum).tsum_eq.symm
  rw [htr, hschA, hschB]
  have hsSub : Summable (fun n : {n // d.coeff n ≠ 0} ↦ (d.coeff n : ℝ)) := by
    have hsT : Summable (fun n ↦ (d.coeff n : ℝ)) := by
      simpa only [Real.rpow_one, d.coeff_eq_approximationNumber] using
        (mem_traceClassOperators_iff_isNuclearOperator T).mpr hT |>.2
    exact hsT.subtype _
  refine hsSub.tsum_le_of_sum_le fun s ↦ ?_
  have hterm (j : {n // d.coeff n ≠ 0}) :
      (d.coeff j : ℝ) ≤ ‖A.val.adjoint (d.target j)‖ * ‖B.val (d.source j)‖ := by
    have hval : ((d.coeff j : ℝ) : ℂ) = ⟪d.target j, T (d.source j)⟫_ℂ := by
      rw [singularExpansion_apply_source d j, inner_smul_right,
        inner_self_eq_norm_sq_to_K, d.orthonormal_target.1 j]
      simp
    have hinner : ⟪d.target j, T (d.source j)⟫_ℂ =
        ⟪A.val.adjoint (d.target j), B.val (d.source j)⟫_ℂ := by
      change ⟪d.target j, A.val (B.val (d.source j))⟫_ℂ = _
      exact (A.val.adjoint_inner_left (B.val (d.source j)) (d.target j)).symm
    have hnorm : ‖((d.coeff j : ℝ) : ℂ)‖ = (d.coeff j : ℝ) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    calc
      (d.coeff j : ℝ) = ‖⟪A.val.adjoint (d.target j), B.val (d.source j)⟫_ℂ‖ := by
        rw [← hnorm, hval, hinner]
      _ ≤ ‖A.val.adjoint (d.target j)‖ * ‖B.val (d.source j)‖ := norm_inner_le_norm _ _
  calc
    ∑ j ∈ s, (d.coeff j : ℝ)
        ≤ ∑ j ∈ s, ‖A.val.adjoint (d.target j)‖ * ‖B.val (d.source j)‖ :=
          Finset.sum_le_sum fun j _ ↦ hterm j
    _ ≤ Real.sqrt (∑ j ∈ s, ‖A.val.adjoint (d.target j)‖ ^ 2) *
          Real.sqrt (∑ j ∈ s, ‖B.val (d.source j)‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt s _ _
    _ ≤ Real.sqrt (∑' n, (dA.coeff n : ℝ) ^ 2) * Real.sqrt (∑' n, (dB.coeff n : ℝ) ^ 2) :=
          mul_le_mul
            (Real.sqrt_le_sqrt (sum_norm_sq_apply_le_schattenNorm_sq
              (singularExpansion_adjoint dA) hsA d.orthonormal_target s))
            (Real.sqrt_le_sqrt (sum_norm_sq_apply_le_schattenNorm_sq
              dB hsB d.orthonormal_source s))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- An a.e. strongly measurable square-integrable family of level vectors yields a
square-integrable kernel whose squared L² norm equals the L² energy of the vector family. -/
private theorem memLp_evaluation_kernel_ae
    {e u : X → H} (he : Continuous e) (hu₂ : MemLp u 2 μ)
    (hrep : ∀ z, (fun x ↦ ⟪e x, u z⟫_ℂ) =ᵐ[μ] (u z : X → ℂ)) :
    MemLp (fun p : X × X ↦ ⟪e p.1, u p.2⟫_ℂ) 2 (μ.prod μ) ∧
      ‖(memLp_two_iff_integrable_sq_norm
        ((he.comp continuous_fst).aestronglyMeasurable.inner
          (hu₂.aestronglyMeasurable.comp_quasiMeasurePreserving
            Measure.quasiMeasurePreserving_snd))).mpr
          (by
            have hswap := Measure.measurePreserving_swap (μ := μ) (ν := μ)
            have hm : AEStronglyMeasurable (fun p : X × X ↦ ⟪e p.1, u p.2⟫_ℂ) (μ.prod μ) :=
              (he.comp continuous_fst).aestronglyMeasurable.inner
                (hu₂.aestronglyMeasurable.comp_quasiMeasurePreserving
                  Measure.quasiMeasurePreserving_snd)
            have hms : AEStronglyMeasurable (fun p : X × X ↦ ‖⟪e p.2, u p.1⟫_ℂ‖ ^ 2) (μ.prod μ) :=
              (hm.comp_measurePreserving hswap).norm.pow 2
            have h : Integrable (fun p : X × X ↦ ‖⟪e p.2, u p.1⟫_ℂ‖ ^ 2) (μ.prod μ) := by
              apply (integrable_prod_iff hms).mpr
              refine ⟨Eventually.of_forall fun z ↦ ?_, ?_⟩
              · exact ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (u z))).mp
                  (Lp.memLp (u z))).congr
                  ((hrep z).symm.mono fun _ h ↦ congrArg (fun t : ℂ ↦ ‖t‖ ^ 2) h)
              · have hU := (memLp_two_iff_integrable_sq_norm hu₂.aestronglyMeasurable).mp hu₂
                refine hU.congr (Eventually.of_forall fun z ↦ ?_)
                change ‖u z‖ ^ 2 = ∫ y, ‖‖⟪e y, u z⟫_ℂ‖ ^ 2‖ ∂μ
                rw [← L2.integral_sq_norm (𝕜 := ℂ) (u z)]
                apply integral_congr_ae
                filter_upwards [hrep z] with y hy
                change ‖(u z) y‖ ^ 2 = ‖‖⟪e y, u z⟫_ℂ‖ ^ 2‖
                rw [hy, Real.norm_of_nonneg (sq_nonneg _)]
            exact hswap.integrable_comp_of_integrable h) |>.toLp
            (fun p : X × X ↦ ⟪e p.1, u p.2⟫_ℂ)‖ =
        Real.sqrt (∫ z, ‖u z‖ ^ 2 ∂μ) := by
  have hm : AEStronglyMeasurable (fun p : X × X ↦ ⟪e p.1, u p.2⟫_ℂ) (μ.prod μ) :=
    (he.comp continuous_fst).aestronglyMeasurable.inner
      (hu₂.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hswap := Measure.measurePreserving_swap (μ := μ) (ν := μ)
  have hms : AEStronglyMeasurable (fun p : X × X ↦ ‖⟪e p.2, u p.1⟫_ℂ‖ ^ 2) (μ.prod μ) :=
    (hm.comp_measurePreserving hswap).norm.pow 2
  have h : Integrable (fun p : X × X ↦ ‖⟪e p.2, u p.1⟫_ℂ‖ ^ 2) (μ.prod μ) := by
    apply (integrable_prod_iff hms).mpr
    refine ⟨Eventually.of_forall fun z ↦ ?_, ?_⟩
    · exact ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (u z))).mp
        (Lp.memLp (u z))).congr ((hrep z).symm.mono fun _ h ↦ congrArg (fun t : ℂ ↦ ‖t‖ ^ 2) h)
    · have hU := (memLp_two_iff_integrable_sq_norm hu₂.aestronglyMeasurable).mp hu₂
      refine hU.congr (Eventually.of_forall fun z ↦ ?_)
      change ‖u z‖ ^ 2 = ∫ y, ‖‖⟪e y, u z⟫_ℂ‖ ^ 2‖ ∂μ
      rw [← L2.integral_sq_norm (𝕜 := ℂ) (u z)]
      apply integral_congr_ae
      filter_upwards [hrep z] with y hy
      change ‖(u z) y‖ ^ 2 = ‖‖⟪e y, u z⟫_ℂ‖ ^ 2‖
      rw [hy, Real.norm_of_nonneg (sq_nonneg _)]
  have hmem : MemLp (fun p : X × X ↦ ⟪e p.1, u p.2⟫_ℂ) 2 (μ.prod μ) :=
    (memLp_two_iff_integrable_sq_norm hm).mpr (hswap.integrable_comp_of_integrable h)
  refine ⟨hmem, ?_⟩
  have hsq : ‖hmem.toLp (fun p : X × X ↦ ⟪e p.1, u p.2⟫_ℂ)‖ ^ 2 = ∫ z, ‖u z‖ ^ 2 ∂μ := by
    rw [← L2.integral_sq_norm (𝕜 := ℂ)]
    have hcongr : (∫ p : X × X, ‖(hmem.toLp (fun p : X × X ↦ ⟪e p.1, u p.2⟫_ℂ)) p‖ ^ 2 ∂(μ.prod μ)) =
        ∫ p : X × X, ‖⟪e p.1, u p.2⟫_ℂ‖ ^ 2 ∂(μ.prod μ) :=
      integral_congr_ae (hmem.coeFn_toLp.mono fun _ hp ↦ congrArg (fun t : ℂ ↦ ‖t‖ ^ 2) hp)
    rw [hcongr, ← hswap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding
      (fun p : X × X ↦ ‖⟪e p.1, u p.2⟫_ℂ‖ ^ 2)]
    change (∫ p : X × X, ‖⟪e p.2, u p.1⟫_ℂ‖ ^ 2 ∂(μ.prod μ)) = _
    rw [integral_prod _ h]
    refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
    change (∫ y, ‖⟪e y, u z⟫_ℂ‖ ^ 2 ∂μ) = ‖u z‖ ^ 2
    rw [← L2.integral_sq_norm (𝕜 := ℂ) (u z)]
    exact integral_congr_ae ((hrep z).mono fun _ hy ↦ congrArg (fun t : ℂ ↦ ‖t‖ ^ 2) hy)
  rw [← Real.sqrt_sq (norm_nonneg _), hsq]

/-- The row family for an a.e. measurable pair of vector families is Bochner integrable. -/
private theorem integrable_kernel_row_ae {E G : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (f : E) {u : X → E} {v : X → G}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
    (hnorm : Integrable (fun z ↦ ‖u z‖ * ‖v z‖) μ) :
    Integrable (fun z ↦ conj ⟪f, u z⟫_ℂ • v z) μ := by
  have hinner : AEStronglyMeasurable (fun z ↦ ⟪f, u z⟫_ℂ) μ :=
    aestronglyMeasurable_const.inner hu
  refine (hnorm.const_mul ‖f‖).mono'
    ((Complex.continuous_conj.comp_aestronglyMeasurable hinner).smul hv) ?_
  filter_upwards with z
  rw [norm_smul, Complex.norm_conj, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)

/-- The composed reproducing kernel remains jointly continuous even when the internal vector
families are only a.e. strongly measurable with integrable norm product. -/
private theorem continuous_evaluation_kernel_ae {E G : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    {e : X → E} {d : X → G} {u : X → E} {v : X → G}
    (he : Continuous e) (hd : Continuous d)
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
    (C : ℝ) (heC : ∀ x, ‖e x‖ ≤ C) (hdC : ∀ x, ‖d x‖ ≤ C)
    (hnorm : Integrable (fun z ↦ ‖u z‖ * ‖v z‖) μ) :
    Continuous (fun p : X × X ↦ ∫ z, ⟪e p.1, u z⟫_ℂ * ⟪v z, d p.2⟫_ℂ ∂μ) := by
  apply continuous_of_dominated (bound := fun z ↦ C * C * (‖u z‖ * ‖v z‖))
  · intro p
    exact (aestronglyMeasurable_const.inner hu).mul (hv.inner aestronglyMeasurable_const)
  · intro p
    filter_upwards with z
    rw [norm_mul]
    have hx := (norm_inner_le_norm (𝕜 := ℂ) (e p.1) (u z)).trans
      (mul_le_mul_of_nonneg_right (heC p.1) (norm_nonneg _))
    have hy := (norm_inner_le_norm (𝕜 := ℂ) (v z) (d p.2)).trans
      (mul_le_mul_of_nonneg_left (hdC p.2) (norm_nonneg _))
    calc
      _ ≤ (C * ‖u z‖) * (‖v z‖ * C) :=
        mul_le_mul hx hy (norm_nonneg _) (le_trans (norm_nonneg _) hx)
      _ = _ := by ring
  · exact hnorm.const_mul _
  · exact Eventually.of_forall fun z ↦
      ((he.comp continuous_fst).inner continuous_const).mul
        (continuous_const.inner (hd.comp continuous_snd))

/-- Measurable evaluation-kernel factorization with explicit trace-norm bound. -/
private theorem sLocalTrace_evaluationKernel_ae
    (V : Submodule ℂ H) [CompleteSpace V]
    (e u : X → H) (v : X → V)
    (he : Continuous e) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C)
    (hu₂ : MemLp u 2 μ) (huV : ∀ z, u z ∈ V)
    (hv₂ : MemLp v 2 μ)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, (f : H)⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ)) :
    let k (p : X × X) := ∫ z, ⟪e p.1, u z⟫_ℂ * ⟪(v z : H), e p.2⟫_ℂ ∂μ
    ∃ (T : H →L[ℂ] H) (hT : IsNuclearOperator T),
      (∀ f : H, ∀ᵐ x ∂μ, T f x = ∫ z, ⟪e x, u z⟫_ℂ * ⟪(v z : H), f⟫_ℂ ∂μ) ∧
      Continuous k ∧
      (∀ f : H, ∀ᵐ x ∂μ, Integrable (fun y ↦ k (x, y) * f y) μ ∧
        T f x = ∫ y, k (x, y) * f y ∂μ) ∧
      Integrable (fun p : X × X ↦ ⟪e p.1, u p.2⟫_ℂ * ⟪(v p.2 : H), e p.1⟫_ℂ) (μ.prod μ) ∧
      Integrable (fun x ↦ k (x, x)) μ ∧
      hilbertTrace ⟨T, hT⟩ = (∫ x, k (x, x) ∂μ) ∧
      traceNorm ⟨T, hT⟩ ≤ Real.sqrt (∫ z, ‖u z‖ ^ 2 ∂μ) * Real.sqrt (∫ z, ‖(v z : H)‖ ^ 2 ∂μ) := by
  intro k
  let a (p : X × X) := ⟪e p.1, u p.2⟫_ℂ
  let b (p : X × X) := ⟪(v p.1 : H), e p.2⟫_ℂ
  obtain ⟨ha, haNorm⟩ := memLp_evaluation_kernel_ae he hu₂ (fun z ↦ hrep ⟨u z, huV z⟩)
  have hV : MemLp (fun z ↦ (v z : H)) 2 μ := V.subtypeL.comp_memLp' hv₂
  obtain ⟨hB, hBNorm⟩ := memLp_evaluation_kernel_ae he hV (fun z ↦ hrep (v z))
  have hswap := Measure.measurePreserving_swap (μ := μ) (ν := μ)
  have hB' := hB.comp_measurePreserving hswap
  have hbMeas : AEStronglyMeasurable b (μ.prod μ) :=
    (hV.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).inner
      (he.comp continuous_snd).aestronglyMeasurable
  have hb : MemLp b 2 (μ.prod μ) := hB'.congr_norm hbMeas
    (Eventually.of_forall fun p ↦ (norm_inner_symm (𝕜 := ℂ) _ _).symm)
  have hbNorm : ‖hb.toLp b‖ = Real.sqrt (∫ z, ‖(v z : H)‖ ^ 2 ∂μ) := by
    have hnormEq : ‖hb.toLp b‖ = ‖hB.toLp (fun p : X × X ↦ ⟪e p.1, (v p.2 : H)⟫_ℂ)‖ := by
      have hsq : ‖hb.toLp b‖ ^ 2 = ‖hB.toLp (fun p : X × X ↦ ⟪e p.1, (v p.2 : H)⟫_ℂ)‖ ^ 2 := by
        rw [← L2.integral_sq_norm (𝕜 := ℂ), ← L2.integral_sq_norm (𝕜 := ℂ)]
        have h1 : (∫ p : X × X, ‖(hb.toLp b) p‖ ^ 2 ∂(μ.prod μ)) =
            ∫ p : X × X, ‖b p‖ ^ 2 ∂(μ.prod μ) :=
          integral_congr_ae (hb.coeFn_toLp.mono fun _ hp ↦ congrArg (fun t : ℂ ↦ ‖t‖ ^ 2) hp)
        have h2 : (∫ p : X × X, ‖(hB.toLp (fun p : X × X ↦ ⟪e p.1, (v p.2 : H)⟫_ℂ)) p‖ ^ 2
              ∂(μ.prod μ)) =
            ∫ p : X × X, ‖⟪e p.1, (v p.2 : H)⟫_ℂ‖ ^ 2 ∂(μ.prod μ) :=
          integral_congr_ae (hB.coeFn_toLp.mono fun _ hp ↦ congrArg (fun t : ℂ ↦ ‖t‖ ^ 2) hp)
        rw [h1, h2, ← hswap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding
          (fun p : X × X ↦ ‖⟪e p.1, (v p.2 : H)⟫_ℂ‖ ^ 2)]
        refine integral_congr_ae (Eventually.of_forall fun p ↦ ?_)
        change ‖⟪(v p.1 : H), e p.2⟫_ℂ‖ ^ 2 = ‖⟪e p.2, (v p.1 : H)⟫_ℂ‖ ^ 2
        rw [norm_inner_symm]
      nlinarith [norm_nonneg (hb.toLp b),
        norm_nonneg (hB.toLp (fun p : X × X ↦ ⟪e p.1, (v p.2 : H)⟫_ℂ))]
    exact hnormEq.trans hBNorm
  let A := integralKernelOperator μ (ha.toLp a)
  let B := integralKernelOperator μ (hb.toLp b)
  let T := A.val.comp B.val
  have hT : IsNuclearOperator T := nuclear_hilbertSchmidt_comp A B
  have hBe (f : H) : ∀ᵐ z ∂μ, B.val f z = ⟪(v z : H), f⟫_ℂ := by
    filter_upwards [integralKernelOperator_apply μ (hb.toLp b) f,
      Measure.ae_ae_of_ae_prod hb.coeFn_toLp] with z hz hbz
    rw [hz.2, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hbz, hrep (v z)] with y hy hy'
    rw [show (hb.toLp b : Lp ℂ 2 (μ.prod μ)) (z, y) = b (z, y) from hy,
      show b (z, y) = conj (⟪e y, (v z : H)⟫_ℂ) from (inner_conj_symm _ _).symm,
      hy', RCLike.inner_apply, mul_comm]
  have hTf (f : H) :
      ∀ᵐ x ∂μ, T f x = ∫ z, a (x, z) * ⟪(v z : H), f⟫_ℂ ∂μ := by
    filter_upwards [integralKernelOperator_apply μ (ha.toLp a) (B.val f),
      Measure.ae_ae_of_ae_prod ha.coeFn_toLp] with x hx hax
    change A.val (B.val f) x = _
    rw [hx.2]
    apply integral_congr_ae
    filter_upwards [hax, hBe f] with z hz hz'
    rw [show (ha.toLp a : Lp ℂ 2 (μ.prod μ)) (x, z) = a (x, z) from hz, hz']
  have hnorm : Integrable (fun z ↦ ‖u z‖ * ‖v z‖) μ := hu₂.norm.integrable_mul hv₂.norm
  have hnorm' : Integrable (fun z ↦ ‖u z‖ * ‖(v z : H)‖) μ := hnorm
  have hk : Continuous k := continuous_evaluation_kernel_ae he he
    hu₂.aestronglyMeasurable hV.aestronglyMeasurable C hC hC hnorm'
  let w (x : X) : V := ∫ z, conj (a (x, z)) • v z ∂μ
  have hwPair (x : X) (f : H) :
      ⟪(w x : H), f⟫_ℂ = ∫ z, a (x, z) * ⟪(v z : H), f⟫_ℂ ∂μ :=
    inner_integral_kernel_row V (fun z ↦ a (x, z)) v
      (integrable_kernel_row_ae (e x) hu₂.aestronglyMeasurable hv₂.aestronglyMeasurable hnorm) f
  have hmass : Integrable (fun p : X × X ↦ a p * b p.swap) (μ.prod μ) :=
    ha.integrable_mul (hb.comp_measurePreserving hswap)
  have hdiag := hmass.integral_prod_left
  refine ⟨T, hT, hTf, hk, ?_, hmass, hdiag, ?_, ?_⟩
  · intro f
    filter_upwards [hTf f] with x hx
    have heq : (fun y ↦ conj ((w x : H) y) * f y) =ᵐ[μ] fun y ↦ k (x, y) * f y := by
      filter_upwards [hrep (w x)] with y hy
      rw [← hy, inner_conj_symm, hwPair]
    refine ⟨(L2.integrable_inner (w x : H) f).congr ?_, ?_⟩
    · exact heq.mono fun _ h ↦ by simpa only [RCLike.inner_apply, mul_comm] using h
    · rw [hx, ← hwPair, L2.inner_def]
      exact integral_congr_ae
        (heq.mono fun _ h ↦ by simpa only [RCLike.inner_apply, mul_comm] using h)
  · change hilbertTrace ⟨A.val.comp B.val, hT⟩ = _
    rw [hilbertTrace_integralKernelOperator_comp]
    change _ = ∫ x, ∫ y, a (x, y) * b (x, y).swap ∂μ ∂μ
    rw [← integral_prod _ hmass]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hswap.quasiMeasurePreserving.ae hb.coeFn_toLp] with p hp hq
    rw [show (ha.toLp a : Lp ℂ 2 (μ.prod μ)) p = a p from hp, hq]
  · refine (traceNorm_hilbertSchmidt_comp_le A B).trans_eq ?_
    rw [schattenNorm_integralKernelOperator, schattenNorm_integralKernelOperator, haNorm, hbNorm]

/-- Abstract trace-norm nonnegativity helper (avoids unfolding subtype instances). -/
private theorem traceNorm_nonneg_of {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (T : nuclearEndomorphisms E) :
    0 ≤ traceNorm T := by
  let _ : Norm (nuclearEndomorphisms E) := ⟨traceNorm⟩
  exact traceNorm_normedSpaceCore.norm_nonneg T

/-- Abstract trace-norm triangle inequality helper (avoids unfolding subtype instances). -/
private theorem traceNorm_add_le_of {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (T S : nuclearEndomorphisms E) :
    traceNorm (T + S) ≤ traceNorm T + traceNorm S := by
  let _ : Norm (nuclearEndomorphisms E) := ⟨traceNorm⟩
  exact traceNorm_normedSpaceCore.norm_triangle T S

/-- Compression of a nuclear endomorphism to a closed subspace does not increase trace norm. -/
private theorem traceNorm_subspace_compression_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (W : Submodule ℂ E) [CompleteSpace W]
    (T : E →L[ℂ] E) (hT : IsNuclearOperator T) (L : W →L[ℂ] W) (hL : IsNuclearOperator L)
    (hEq : W.orthogonalProjectionOnto.comp (T.comp W.subtypeL) = L) :
    traceNorm ⟨L, hL⟩ ≤ traceNorm ⟨T, hT⟩ := by
  obtain ⟨hN, hle⟩ := traceNorm_sandwich_le T hT W.subtypeL W.orthogonalProjectionOnto
  have hSub : traceNorm ⟨L, hL⟩ =
      traceNorm ⟨W.orthogonalProjectionOnto.comp (T.comp W.subtypeL), hN⟩ :=
    congrArg traceNorm (Subtype.ext hEq.symm)
  rw [hSub]
  have hqNorm : ‖W.orthogonalProjectionOnto‖ ≤ 1 := W.orthogonalProjectionOnto_norm_le
  have hjNorm : ‖W.subtypeL‖ ≤ 1 := W.subtypeL.opNorm_le_bound zero_le_one fun x ↦ by simp
  have hmul : ‖W.orthogonalProjectionOnto‖ * ‖W.subtypeL‖ ≤ 1 :=
    (mul_le_mul hqNorm hjNorm (norm_nonneg W.subtypeL) zero_le_one).trans_eq (mul_one 1)
  exact hle.trans (mul_le_of_le_one_left (traceNorm_nonneg_of ⟨T, hT⟩) hmul)

/-- Abstract subspace lift preserves nuclearity and Hilbert trace. -/
private theorem isNuclearOperator_and_hilbertTrace_subspace_lift {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (W : Submodule ℂ E) [CompleteSpace W] (L : W →L[ℂ] W)
    (hT : IsNuclearOperator (W.subtypeL.comp (L.comp W.orthogonalProjectionOnto))) :
    ∃ hL : IsNuclearOperator L,
      hilbertTrace ⟨L, hL⟩ =
        hilbertTrace ⟨W.subtypeL.comp (L.comp W.orthogonalProjectionOnto), hT⟩ := by
  let j := W.subtypeL
  let q := W.orthogonalProjectionOnto
  let T := j.comp (L.comp q)
  have hqj (f : W) : q (j f) = f := W.orthogonalProjectionOnto_mem_subspace_eq_self f
  have hqT : q.comp T = L.comp q := by
    ext f : 1
    exact hqj (L (q f))
  have hLq : IsNuclearOperator (L.comp q) := by
    rw [← hqT]
    obtain ⟨aa, l, y, haa, hl, hy, hs⟩ := (isNuclearOperator_iff_isBanachNuclear T).mp hT
    apply (isNuclearOperator_iff_isBanachNuclear _).mpr
    refine ⟨aa, l, q ∘ y, haa, hl, ?_, fun x ↦ ?_⟩
    · simpa only [map_zero] using (q.continuous.tendsto 0).comp hy
    · simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, map_smul] using
        q.hasSum (hs x)
  have hj : Function.Injective j := Subtype.val_injective
  have hLqj : (L.comp q).comp j = L := by
    ext f : 1
    exact congrArg L (hqj f)
  have hL : IsNuclearOperator L := hLqj ▸ (isNuclearOperator_factor_comps j hj _ hLq).1
  refine ⟨hL, ?_⟩
  rw [hilbertTrace_eq_nuclearTrace ⟨L, hL⟩, hilbertTrace_eq_nuclearTrace ⟨T, hT⟩]
  have hn := nuclearTrace_factor_comps hilbert_approximationProperty
    hilbert_approximationProperty j hj _ hLq
  simpa only [hLqj] using hn

/-- Pointwise `L²` polar factorization of an integrable complex cutoff `ρ = a · b`. -/
private theorem measurableCutoff_polar_factor (ρ : X → ℂ) (hρ : Integrable ρ μ) :
    ∃ (a : X → ℝ) (b : X → ℂ),
      MemLp a 2 μ ∧ MemLp b 2 μ ∧
      (∀ z, (a z : ℂ) * b z = ρ z) ∧
      (∀ z, ‖a z‖ ^ 2 = ‖ρ z‖) ∧
      (∀ z, ‖b z‖ ^ 2 = ‖ρ z‖) := by
  let a (z : X) : ℝ := Real.sqrt ‖ρ z‖
  let b (z : X) : ℂ := ρ z / (a z : ℂ)
  have haMeas : AEStronglyMeasurable a μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hρ.aestronglyMeasurable.norm
  have hbMeas : AEStronglyMeasurable b μ :=
    hρ.aestronglyMeasurable.mul
      (measurable_inv.comp_aemeasurable
        (Complex.continuous_ofReal.comp_aestronglyMeasurable haMeas).aemeasurable).aestronglyMeasurable
  have haSq (z : X) : ‖a z‖ ^ 2 = ‖ρ z‖ := by
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (norm_nonneg _)]
  have hbSq (z : X) : ‖b z‖ ^ 2 = ‖ρ z‖ := by
    by_cases hz : ρ z = 0
    · simp [b, hz]
    · have hsq : ‖a z‖ ^ 2 = ‖ρ z‖ := haSq z
      dsimp only [b]
      rw [norm_div, Complex.norm_real, div_pow, hsq, sq,
        mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hz)]
  have hab (z : X) : (a z : ℂ) * b z = ρ z := by
    by_cases hz : ρ z = 0
    · simp [a, b, hz]
    · have ha0 : (a z : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (norm_pos_iff.mpr hz)).ne'
      dsimp only [b]
      exact mul_div_cancel₀ _ ha0
  have ha₂ : MemLp a 2 μ :=
    (memLp_two_iff_integrable_sq_norm haMeas).mpr
      (hρ.norm.congr (Eventually.of_forall fun z ↦ (haSq z).symm))
  have hb₂ : MemLp b 2 μ :=
    (memLp_two_iff_integrable_sq_norm hbMeas).mpr
      (hρ.norm.congr (Eventually.of_forall fun z ↦ (hbSq z).symm))
  exact ⟨a, b, ha₂, hb₂, hab, haSq, hbSq⟩

/-- Elementary bound reducing the weighted Cauchy–Schwarz trace-norm bound to `C² ‖D‖ ∫ ‖ρ‖`. -/
private theorem measurableCutoff_traceNorm_le_uniform
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (e : X → E) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C) (ρ : X → ℂ) (hρ : Integrable ρ μ)
    (D : E →L[ℂ] E) :
    Real.sqrt (∫ z, ‖ρ z‖ * ‖e z‖ ^ 2 ∂μ) *
      Real.sqrt (∫ z, ‖ρ z‖ * ‖D.adjoint (e z)‖ ^ 2 ∂μ) ≤
      C ^ 2 * ‖D‖ * ∫ z, ‖ρ z‖ ∂μ := by
  have h1 : (∫ z, ‖ρ z‖ * ‖e z‖ ^ 2 ∂μ) ≤ C ^ 2 * ∫ z, ‖ρ z‖ ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun z ↦ mul_nonneg (norm_nonneg _)
      (sq_nonneg _)) (hρ.norm.const_mul (C ^ 2)) (Eventually.of_forall fun z ↦ ?_)
    have hCe : ‖e z‖ ^ 2 ≤ C ^ 2 := by
      have hCnn : 0 ≤ C := (norm_nonneg (e z)).trans (hC z)
      nlinarith [hC z, norm_nonneg (e z)]
    dsimp only
    rw [mul_comm (C ^ 2)]
    exact mul_le_mul_of_nonneg_left hCe (norm_nonneg _)
  have h2 : (∫ z, ‖ρ z‖ * ‖D.adjoint (e z)‖ ^ 2 ∂μ) ≤ (C ^ 2 * ‖D‖ ^ 2) * ∫ z, ‖ρ z‖ ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun z ↦ mul_nonneg (norm_nonneg _)
      (sq_nonneg _)) (hρ.norm.const_mul (C ^ 2 * ‖D‖ ^ 2)) (Eventually.of_forall fun z ↦ ?_)
    have hDe : ‖D.adjoint (e z)‖ ≤ ‖D‖ * C := by
      calc
        ‖D.adjoint (e z)‖ ≤ ‖D.adjoint‖ * ‖e z‖ := D.adjoint.le_opNorm (e z)
        _ = ‖D‖ * ‖e z‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
        _ ≤ ‖D‖ * C := mul_le_mul_of_nonneg_left (hC z) (norm_nonneg D)
    have hDeSq : ‖D.adjoint (e z)‖ ^ 2 ≤ C ^ 2 * ‖D‖ ^ 2 := by
      have hDCnn : 0 ≤ ‖D‖ * C := (norm_nonneg (D.adjoint (e z))).trans hDe
      nlinarith [hDe, norm_nonneg (D.adjoint (e z))]
    dsimp only
    rw [mul_comm (C ^ 2 * ‖D‖ ^ 2)]
    exact mul_le_mul_of_nonneg_left hDeSq (norm_nonneg _)
  have hIntNN : 0 ≤ ∫ z, ‖ρ z‖ ∂μ := integral_nonneg fun _ ↦ norm_nonneg _
  have hprod :
      Real.sqrt (C ^ 2 * ∫ z, ‖ρ z‖ ∂μ) * Real.sqrt ((C ^ 2 * ‖D‖ ^ 2) * ∫ z, ‖ρ z‖ ∂μ) =
        C ^ 2 * ‖D‖ * ∫ z, ‖ρ z‖ ∂μ := by
    rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_mul (mul_nonneg (sq_nonneg C) (sq_nonneg ‖D‖)),
      Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg D)]
    calc
      |C| * Real.sqrt (∫ z, ‖ρ z‖ ∂μ) * (|C| * ‖D‖ * Real.sqrt (∫ z, ‖ρ z‖ ∂μ))
          = (|C| * |C|) * ‖D‖ * (Real.sqrt (∫ z, ‖ρ z‖ ∂μ) * Real.sqrt (∫ z, ‖ρ z‖ ∂μ)) := by
            ring
      _ = C ^ 2 * ‖D‖ * ∫ z, ‖ρ z‖ ∂μ := by
            rw [← sq, sq_abs, Real.mul_self_sqrt hIntNN]
  exact (mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)).trans_eq hprod

/-- Scalar multiplication of an `L²` complex function by a bounded continuous vector family
remains in `L²`. -/
private theorem memLp_smul_continuous_bounded {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {c : X → ℂ} (hc : MemLp c 2 μ) {f : X → E} (hf : Continuous f)
    (M : ℝ) (hM : ∀ x, ‖f x‖ ≤ M) :
    MemLp (fun z ↦ c z • f z) 2 μ := by
  have : SecondCountableTopologyEither ℂ E := ⟨Or.inl inferInstance⟩
  refine (hc.norm.const_smul M).mono' (hc.aestronglyMeasurable.smul hf.aestronglyMeasurable)
    (Eventually.of_forall fun z ↦ ?_)
  change ‖c z • f z‖ ≤ M * ‖c z‖
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hM z) (norm_nonneg (c z))).trans_eq (mul_comm _ _)

/-- Collapse the double diagonal integral of the reproducing kernel to the single diagonal
integral `∫ ρ(z) ⟪e z, D (e z)⟫ dμ`. -/
private theorem sLocalTrace_reproducing_diagonal_collapse
    (V : Submodule ℂ H) [CompleteSpace V] (e : X → V)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, f⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ))
    (ρ : X → ℂ) (D : V →L[ℂ] V)
    (hmass : Integrable (fun p : X × X ↦ ρ p.2 * (⟪e p.1, e p.2⟫_ℂ * ⟪e p.2, D (e p.1)⟫_ℂ))
      (μ.prod μ)) :
    Integrable (fun z ↦ ρ z * ⟪e z, D (e z)⟫_ℂ) μ ∧
      (∫ x, ∫ z, ρ z * (⟪e x, e z⟫_ℂ * ⟪e z, D (e x)⟫_ℂ) ∂μ ∂μ) =
        ∫ z, ρ z * ⟪e z, D (e z)⟫_ℂ ∂μ := by
  have hinner_x (z : X) :
      (∫ x, ρ z * (⟪e x, e z⟫_ℂ * ⟪e z, D (e x)⟫_ℂ) ∂μ) = ρ z * ⟪e z, D (e z)⟫_ℂ := by
    rw [integral_const_mul]
    congr 1
    rw [← D.adjoint_inner_left,
      show ⟪D.adjoint (e z), e z⟫_ℂ = ⟪(D.adjoint (e z) : H), (e z : H)⟫_ℂ from rfl, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrep (e z), hrep (D.adjoint (e z))] with x hxz hDz
    have h1 : ⟪e z, D (e x)⟫_ℂ = conj ((D.adjoint (e z) : H) x) := by
      rw [← D.adjoint_inner_left, ← inner_conj_symm]
      exact congrArg conj hDz
    rw [hxz, h1, RCLike.inner_apply, mul_comm]
  refine ⟨by simpa only [hinner_x] using hmass.integral_prod_right, ?_⟩
  rw [← integral_prod _ hmass, integral_prod_symm _ hmass]
  exact integral_congr_ae (Eventually.of_forall hinner_x)

/-- Identify the compressed cutoff operator `T = j ∘ q ∘ M ∘ j ∘ D ∘ q` with the evaluation-kernel
operator `U` built from a polar factorization `ρ = a · b`. -/
private theorem sLocalTrace_measurableCutoff_op_eq
    (V : Submodule ℂ H) [CompleteSpace V] (e : X → V)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, f⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ))
    (ρ : X → ℂ) (a : X → ℝ) (b : X → ℂ) (hab : ∀ z, (a z : ℂ) * b z = ρ z)
    (M : H →L[ℂ] H) (hM : ∀ f : H, ∀ᵐ x ∂μ, M f x = ρ x * f x)
    (D : V →L[ℂ] V) (U : H →L[ℂ] H)
    (hUapply : ∀ f : H, ∀ᵐ x ∂μ, U f x =
      ∫ z, ⟪(e x : H), ((a z : ℂ) • e z : V)⟫_ℂ *
        ⟪((conj (b z) • D.adjoint (e z) : V) : H), f⟫_ℂ ∂μ) :
    V.subtypeL.comp ((V.orthogonalProjectionOnto.comp (M.comp (V.subtypeL.comp D))).comp
      V.orthogonalProjectionOnto) = U := by
  let j := V.subtypeL
  let q := V.orthogonalProjectionOnto
  apply ContinuousLinearMap.ext
  intro f
  let d := D (q f)
  let g := M (j d)
  apply Lp.ext
  filter_upwards [hrep (q g), hUapply f] with x hx hux
  change (q g : H) x = U f x
  rw [← hx, V.inner_orthogonalProjectionOnto_eq_of_mem_left, hux, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hrep d, hrep (e x), hM (j d)] with z hdz hxz hz
  have hout : ⟪(e x : H), ((a z : ℂ) • e z : V)⟫_ℂ = (a z : ℂ) * ⟪e x, e z⟫_ℂ :=
    inner_smul_right _ _ _
  have hpair : ⟪((conj (b z) • D.adjoint (e z) : V) : H), f⟫_ℂ = b z * ⟪e z, d⟫_ℂ := by
    rw [← V.inner_orthogonalProjectionOnto_eq_of_mem_left]
    change ⟪conj (b z) • D.adjoint (e z), q f⟫_ℂ = _
    rw [inner_smul_left, D.adjoint_inner_left, Complex.conj_conj]
  rw [hout, hpair]
  change ⟪(e x : H) z, g z⟫_ℂ = _
  change ⟪e z, d⟫_ℂ = (j d) z at hdz
  rw [show g z = _ from hz, ← hdz, ← hxz, RCLike.inner_apply, inner_conj_symm]
  calc
    ρ z * ⟪e z, d⟫_ℂ * ⟪e x, e z⟫_ℂ
        = ((a z : ℂ) * b z) * (⟪e x, e z⟫_ℂ * ⟪e z, d⟫_ℂ) := by rw [hab z]; ring
    _ = (a z : ℂ) * ⟪e x, e z⟫_ℂ * (b z * ⟪e z, d⟫_ℂ) := by ring

/-- Ambient Hilbert-space half of `sLocalTrace_measurableCutoffKernel`: builds `hT`, continuity,
kernel action, product-space integrability, diagonal trace, and sharp trace-norm bound on `H`. -/
private theorem sLocalTrace_measurableCutoff_ambient
    (V : Submodule ℂ H) [CompleteSpace V]
    (e : X → V) (he : Continuous e) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, f⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ))
    (ρ : X → ℂ) (hρ : Integrable ρ μ)
    (M : H →L[ℂ] H) (hM : ∀ f : H, ∀ᵐ x ∂μ, M f x = ρ x * f x)
    (D : V →L[ℂ] V) :
    let j := V.subtypeL
    let q := V.orthogonalProjectionOnto
    let L := q.comp (M.comp (j.comp D))
    let T := j.comp (L.comp q)
    let k (p : X × X) := ∫ z, ρ z * (⟪e p.1, e z⟫_ℂ * ⟪e z, D (e p.2)⟫_ℂ) ∂μ
    ∃ hT : IsNuclearOperator T,
      Continuous k ∧
      (∀ f : H, ∀ᵐ x ∂μ, Integrable (fun y ↦ k (x, y) * f y) μ ∧
        T f x = ∫ y, k (x, y) * f y ∂μ) ∧
      Integrable (fun p : X × X ↦ ρ p.2 * (⟪e p.1, e p.2⟫_ℂ * ⟪e p.2, D (e p.1)⟫_ℂ))
        (μ.prod μ) ∧
      Integrable (fun x ↦ k (x, x)) μ ∧
      hilbertTrace ⟨T, hT⟩ = (∫ x, k (x, x) ∂μ) ∧
      traceNorm ⟨T, hT⟩ ≤
        Real.sqrt (∫ z, ‖ρ z‖ * ‖e z‖ ^ 2 ∂μ) *
          Real.sqrt (∫ z, ‖ρ z‖ * ‖D.adjoint (e z)‖ ^ 2 ∂μ) := by
  intro j q L T k
  obtain ⟨a, b, ha₂, hb₂, hab, haSq, hbSq⟩ := measurableCutoff_polar_factor ρ hρ
  let u₀ (z : X) : V := (a z : ℂ) • e z
  let v (z : X) : V := conj (b z) • D.adjoint (e z)
  let u (z : X) : H := j (u₀ z)
  have haC₂ : MemLp (fun z ↦ (a z : ℂ)) 2 μ := Complex.ofRealCLM.comp_memLp' ha₂
  have hbC₂ : MemLp (fun z ↦ conj (b z)) 2 μ :=
    Complex.conjCLE.toContinuousLinearMap.comp_memLp' hb₂
  have hu₀₂ : MemLp u₀ 2 μ := memLp_smul_continuous_bounded haC₂ he C hC
  have hv₂ : MemLp v 2 μ :=
    memLp_smul_continuous_bounded hbC₂ (D.adjoint.continuous.comp he) (‖D.adjoint‖ * C) fun z ↦
      (D.adjoint.le_opNorm (e z)).trans (mul_le_mul_of_nonneg_left (hC z) (norm_nonneg _))
  obtain ⟨U, hU, hUapply, hcont, hkernel, hmass, hdiag, htrace, htrNorm⟩ :=
    sLocalTrace_evaluationKernel_ae V (fun x ↦ j (e x)) u v (j.continuous.comp he)
      C hC (j.comp_memLp' hu₀₂) (fun z ↦ (u₀ z).property) hv₂ hrep
  have hpair (z : X) (f : H) : ⟪(v z : H), f⟫_ℂ = b z * ⟪e z, D (q f)⟫_ℂ := by
    rw [← V.inner_orthogonalProjectionOnto_eq_of_mem_left (v z) f]
    change ⟪conj (b z) • D.adjoint (e z), q f⟫_ℂ = _
    rw [inner_smul_left, D.adjoint_inner_left, Complex.conj_conj]
  have hout (x z : X) : ⟪j (e x), u z⟫_ℂ = (a z : ℂ) * ⟪e x, e z⟫_ℂ :=
    inner_smul_right _ _ _
  have hsc (z : X) (p₁ p₂ : ℂ) : ((a z : ℂ) * p₁) * (b z * p₂) = ρ z * (p₁ * p₂) := by
    calc
      ((a z : ℂ) * p₁) * (b z * p₂) = ((a z : ℂ) * b z) * (p₁ * p₂) := by ring
      _ = ρ z * (p₁ * p₂) := by rw [hab z]
  have heq : T = U :=
    sLocalTrace_measurableCutoff_op_eq V e hrep ρ a b hab M hM D U hUapply
  have hqj (f : V) : q (j f) = f := V.orthogonalProjectionOnto_mem_subspace_eq_self f
  have hk' : (fun p : X × X ↦
      ∫ z, ⟪j (e p.1), u z⟫_ℂ * ⟪(v z : H), j (e p.2)⟫_ℂ ∂μ) = k :=
    funext fun p ↦ integral_congr_ae (Eventually.of_forall fun z ↦ by
      dsimp only
      rw [hout, hpair, hsc, hqj])
  have hmass_eq : (fun p : X × X ↦ ⟪j (e p.1), u p.2⟫_ℂ * ⟪(v p.2 : H), j (e p.1)⟫_ℂ) =
      fun p : X × X ↦ ρ p.2 * (⟪e p.1, e p.2⟫_ℂ * ⟪e p.2, D (e p.1)⟫_ℂ) :=
    funext fun p ↦ by rw [hout, hpair, hsc, hqj]
  have huNormEq (z : X) : ‖u z‖ ^ 2 = ‖ρ z‖ * ‖e z‖ ^ 2 := by
    change ‖(a z : ℂ) • e z‖ ^ 2 = _
    rw [norm_smul, Complex.norm_real, mul_pow, haSq]
  have hvNormEq (z : X) : ‖(v z : H)‖ ^ 2 = ‖ρ z‖ * ‖D.adjoint (e z)‖ ^ 2 := by
    change ‖conj (b z) • D.adjoint (e z)‖ ^ 2 = _
    rw [norm_smul, Complex.norm_conj, mul_pow, hbSq]
  have hT : IsNuclearOperator T := heq ▸ hU
  have hTnorm : traceNorm ⟨T, hT⟩ ≤
      Real.sqrt (∫ z, ‖ρ z‖ * ‖e z‖ ^ 2 ∂μ) *
        Real.sqrt (∫ z, ‖ρ z‖ * ‖D.adjoint (e z)‖ ^ 2 ∂μ) := by
    have hEqN : (⟨T, hT⟩ : nuclearEndomorphisms H) = ⟨U, hU⟩ := Subtype.ext heq
    rw [hEqN]
    simpa only [huNormEq, hvNormEq] using htrNorm
  exact ⟨hT, hk' ▸ hcont, heq ▸ hk' ▸ hkernel, hmass_eq ▸ hmass, hk' ▸ hdiag,
    (congrArg hilbertTrace (Subtype.ext heq)).trans (hk' ▸ htrace), hTnorm⟩

/-- Paper: Theorem 12.4.1.1, pp. 515–517. Any integrable complex spatial cutoff `ρ` (including
sharp indicator balls, annular cutoffs, smooth cutoffs, and signed cutoff differences) with
bounded multiplication operator `M` and bounded level operator `D` produces a nuclear compression
whose integral kernel is still jointly continuous on `X × X`. Its diagonal trace collapses to the
single reproducing-kernel diagonal integral `∫ ρ(z) ⟪e z, D (e z)⟫ dμ`, and its trace norm obeys
the sharp Cauchy–Schwarz bound `√(∫ ‖ρ‖ ‖e‖²) · √(∫ ‖ρ‖ ‖D* e‖²) ≤ C² ‖D‖ ∫ ‖ρ‖`.
Reconstruction: Factors `ρ = a · b` with `a(z) = √‖ρ(z)‖` and `b(z) = ρ(z) / √‖ρ(z)‖` in `L²(μ)`
without requiring `ρ` to be continuous or nonnegative.
Deviation: The operator `D` is assumed bounded on the fixed evaluable level `V`, and the weight
density is absorbed into `μ` (see `sLocalTrace_densityTwist_kernel` for the explicit conversion). -/
theorem sLocalTrace_measurableCutoffKernel
    (V : Submodule ℂ H) [CompleteSpace V]
    (e : X → V) (he : Continuous e) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, f⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ))
    (ρ : X → ℂ) (hρ : Integrable ρ μ)
    (M : H →L[ℂ] H) (hM : ∀ f : H, ∀ᵐ x ∂μ, M f x = ρ x * f x)
    (D : V →L[ℂ] V) :
    let j := V.subtypeL
    let q := V.orthogonalProjectionOnto
    let L := q.comp (M.comp (j.comp D))
    let T := j.comp (L.comp q)
    let k (p : X × X) := ∫ z, ρ z * (⟪e p.1, e z⟫_ℂ * ⟪e z, D (e p.2)⟫_ℂ) ∂μ
    ∃ (hT : IsNuclearOperator T) (hL : IsNuclearOperator L),
      Continuous k ∧
      (∀ f : H, ∀ᵐ x ∂μ, Integrable (fun y ↦ k (x, y) * f y) μ ∧
        T f x = ∫ y, k (x, y) * f y ∂μ) ∧
      Integrable (fun x ↦ k (x, x)) μ ∧
      Integrable (fun z ↦ ρ z * ⟪e z, D (e z)⟫_ℂ) μ ∧
      hilbertTrace ⟨T, hT⟩ = (∫ x, k (x, x) ∂μ) ∧
      hilbertTrace ⟨L, hL⟩ = (∫ x, k (x, x) ∂μ) ∧
      hilbertTrace ⟨L, hL⟩ = (∫ z, ρ z * ⟪e z, D (e z)⟫_ℂ ∂μ) ∧
      traceNorm ⟨T, hT⟩ ≤
        Real.sqrt (∫ z, ‖ρ z‖ * ‖e z‖ ^ 2 ∂μ) *
          Real.sqrt (∫ z, ‖ρ z‖ * ‖D.adjoint (e z)‖ ^ 2 ∂μ) ∧
      traceNorm ⟨L, hL⟩ ≤ C ^ 2 * ‖D‖ * ∫ z, ‖ρ z‖ ∂μ := by
  intro j q L T k
  obtain ⟨hT, hcont, hkernel, hmass, hdiag, hTtrace, hTnorm⟩ :=
    sLocalTrace_measurableCutoff_ambient V e he C hC hrep ρ hρ M hM D
  obtain ⟨hL, hLT⟩ := isNuclearOperator_and_hilbertTrace_subspace_lift V L hT
  have hLtrace : hilbertTrace ⟨L, hL⟩ = ∫ x, k (x, x) ∂μ := hLT.trans hTtrace
  obtain ⟨hrepDiagInt, hcollapse⟩ :=
    sLocalTrace_reproducing_diagonal_collapse V e hrep ρ D hmass
  have hLrepDiag : hilbertTrace ⟨L, hL⟩ = ∫ z, ρ z * ⟪e z, D (e z)⟫_ℂ ∂μ :=
    hLtrace.trans hcollapse
  have hLleT : traceNorm ⟨L, hL⟩ ≤ traceNorm ⟨T, hT⟩ :=
    traceNorm_subspace_compression_le V T hT L hL (by
      ext f : 1
      change V.orthogonalProjectionOnto ((L (V.orthogonalProjectionOnto (f : H))) : H) = L f
      rw [V.orthogonalProjectionOnto_mem_subspace_eq_self,
        V.orthogonalProjectionOnto_mem_subspace_eq_self])
  have hLnorm : traceNorm ⟨L, hL⟩ ≤ C ^ 2 * ‖D‖ * ∫ z, ‖ρ z‖ ∂μ :=
    (hLleT.trans hTnorm).trans (measurableCutoff_traceNorm_le_uniform e C hC ρ hρ D)
  exact ⟨hT, hL, hcont, hkernel, hdiag, hrepDiagInt, hTtrace, hLtrace, hLrepDiag, hTnorm, hLnorm⟩

/-- Compact summary of `sLocalTrace_measurableCutoffKernel` returning just nuclearity,
reproducing-diagonal trace, and uniform trace-norm bound. -/
private theorem sLocalTrace_measurableCutoff_summary
    (V : Submodule ℂ H) [CompleteSpace V]
    (e : X → V) (he : Continuous e) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, f⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ))
    (ρ : X → ℂ) (hρ : Integrable ρ μ)
    (M : H →L[ℂ] H) (hM : ∀ f : H, ∀ᵐ x ∂μ, M f x = ρ x * f x)
    (D : V →L[ℂ] V) :
    let L := V.orthogonalProjectionOnto.comp (M.comp (V.subtypeL.comp D))
    ∃ hL : IsNuclearOperator L,
      Integrable (fun z ↦ ρ z * ⟪e z, D (e z)⟫_ℂ) μ ∧
      hilbertTrace ⟨L, hL⟩ = (∫ z, ρ z * ⟪e z, D (e z)⟫_ℂ ∂μ) ∧
      traceNorm ⟨L, hL⟩ ≤ C ^ 2 * ‖D‖ * ∫ z, ‖ρ z‖ ∂μ := by
  obtain ⟨_, hL, _, _, _, hInt, _, _, hTr, _, hNorm⟩ :=
    sLocalTrace_measurableCutoffKernel V e he C hC hrep ρ hρ M hM D
  exact ⟨hL, hInt, hTr, hNorm⟩

/-- Paper: Theorem 12.4.1.1, pp. 515–517. Simultaneous perturbation of the spatial cutoff `ρ`
(in `L¹(μ)`) and the level operator `D` (in operator norm) controls both the exact trace
difference and the trace norm of the difference of the compressed operators.
Reconstruction: Applies `sLocalTrace_measurableCutoffKernel` to the bilinear splitting
`L₁ - L₂ = q (M₁ - M₂) j D₁ + q M₂ j (D₁ - D₂)`. -/
theorem sLocalTrace_cutoff_perturbation_bound
    (V : Submodule ℂ H) [CompleteSpace V]
    (e : X → V) (he : Continuous e) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, f⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ))
    (ρ₁ ρ₂ : X → ℂ) (hρ₁ : Integrable ρ₁ μ) (hρ₂ : Integrable ρ₂ μ)
    (M₁ M₂ : H →L[ℂ] H)
    (hM₁ : ∀ f : H, ∀ᵐ x ∂μ, M₁ f x = ρ₁ x * f x)
    (hM₂ : ∀ f : H, ∀ᵐ x ∂μ, M₂ f x = ρ₂ x * f x)
    (D₁ D₂ : V →L[ℂ] V) :
    let j := V.subtypeL
    let q := V.orthogonalProjectionOnto
    let L₁ := q.comp (M₁.comp (j.comp D₁))
    let L₂ := q.comp (M₂.comp (j.comp D₂))
    ∃ (hL₁ : IsNuclearOperator L₁) (hL₂ : IsNuclearOperator L₂)
      (hSub : IsNuclearOperator (L₁ - L₂)),
      hilbertTrace ⟨L₁, hL₁⟩ - hilbertTrace ⟨L₂, hL₂⟩ =
        ∫ z, (ρ₁ z * ⟪e z, D₁ (e z)⟫_ℂ - ρ₂ z * ⟪e z, D₂ (e z)⟫_ℂ) ∂μ ∧
      traceNorm ⟨L₁ - L₂, hSub⟩ ≤
        C ^ 2 * ‖D₁‖ * (∫ z, ‖ρ₁ z - ρ₂ z‖ ∂μ) +
          C ^ 2 * ‖D₁ - D₂‖ * (∫ z, ‖ρ₂ z‖ ∂μ) := by
  intro j q L₁ L₂
  obtain ⟨hL₁, hInt₁, hTr₁, _⟩ :=
    sLocalTrace_measurableCutoff_summary V e he C hC hrep ρ₁ hρ₁ M₁ hM₁ D₁
  obtain ⟨hL₂, hInt₂, hTr₂, _⟩ :=
    sLocalTrace_measurableCutoff_summary V e he C hC hrep ρ₂ hρ₂ M₂ hM₂ D₂
  have hMsub : ∀ f : H, ∀ᵐ x ∂μ, (M₁ - M₂) f x = (ρ₁ x - ρ₂ x) * f x := by
    intro f
    filter_upwards [Lp.coeFn_sub (M₁ f) (M₂ f), hM₁ f, hM₂ f] with x hsub h1 h2
    change (M₁ f - M₂ f) x = _
    rw [hsub, Pi.sub_apply, h1, h2]
    ring
  obtain ⟨hA, _, _, hAnorm⟩ :=
    sLocalTrace_measurableCutoff_summary V e he C hC hrep (fun z ↦ ρ₁ z - ρ₂ z)
      (hρ₁.sub hρ₂) (M₁ - M₂) hMsub D₁
  obtain ⟨hB, _, _, hBnorm⟩ :=
    sLocalTrace_measurableCutoff_summary V e he C hC hrep ρ₂ hρ₂ M₂ hM₂ (D₁ - D₂)
  have hsplit : L₁ - L₂ =
      q.comp ((M₁ - M₂).comp (j.comp D₁)) + q.comp (M₂.comp (j.comp (D₁ - D₂))) := by
    ext f : 1
    simp [L₁, L₂]
  have hSub : IsNuclearOperator (L₁ - L₂) :=
    hsplit.symm ▸ (nuclearEndomorphisms V).add_mem hA hB
  refine ⟨hL₁, hL₂, hSub, ?_, ?_⟩
  · exact (congrArg₂ (· - ·) hTr₁ hTr₂).trans (integral_sub hInt₁ hInt₂).symm
  · have hEq : (⟨L₁ - L₂, hSub⟩ : nuclearEndomorphisms V) =
        ⟨q.comp ((M₁ - M₂).comp (j.comp D₁)), hA⟩ +
          ⟨q.comp (M₂.comp (j.comp (D₁ - D₂))), hB⟩ := Subtype.ext hsplit
    exact (congrArg traceNorm hEq).le.trans
      ((traceNorm_add_le_of _ _).trans (add_le_add hAnorm hBnorm))

/-- Paper: Theorem 12.4.1.1, pp. 515–517. If the reproducing-kernel diagonal `z ↦ ⟪e z, D (e z)⟫`
vanishes at infinity (`cocompact X`), then any two families of integrable cutoffs whose difference
is uniformly bounded in `L¹(μ)` and vanishes in `L¹(μ)` on every compact set produce asymptotically
identical Hilbert traces.
Reconstruction: Formalizes the abstract smooth-vs-sharp cutoff equivalence used in the `#7354`
fixed-level trace limit arguments (`ρ_L = η * 1_{[-L, L]}` versus `1_{[-L, L]}`), where the cutoff
difference stays bounded in `L¹` without vanishing globally in `L¹`. -/
theorem sLocalTrace_cutoff_tendsto_of_cocompact_decay
    {ι : Type*} {l : Filter ι}
    (V : Submodule ℂ H) [CompleteSpace V]
    (e : X → V) (he : Continuous e) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, f⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ))
    (D : V →L[ℂ] V)
    (hdecay : Tendsto (fun z ↦ ⟪e z, D (e z)⟫_ℂ) (cocompact X) (𝓝 0))
    (ρ σ : ι → X → ℂ) (hρ : ∀ i, Integrable (ρ i) μ) (hσ : ∀ i, Integrable (σ i) μ)
    (M N : ι → H →L[ℂ] H)
    (hM : ∀ i (f : H), ∀ᵐ x ∂μ, M i f x = ρ i x * f x)
    (hN : ∀ i (f : H), ∀ᵐ x ∂μ, N i f x = σ i x * f x)
    (hL1 : ∃ B : ℝ, ∀ᶠ i in l, ∫ z, ‖ρ i z - σ i z‖ ∂μ ≤ B)
    (hloc : ∀ K : Set X, IsCompact K →
      Tendsto (fun i ↦ ∫ z in K, ‖ρ i z - σ i z‖ ∂μ) l (𝓝 0)) :
    let j := V.subtypeL
    let q := V.orthogonalProjectionOnto
    let Lρ (i : ι) := q.comp ((M i).comp (j.comp D))
    let Lσ (i : ι) := q.comp ((N i).comp (j.comp D))
    ∀ (hLρ : ∀ i, IsNuclearOperator (Lρ i)) (hLσ : ∀ i, IsNuclearOperator (Lσ i)),
      Tendsto (fun i ↦ hilbertTrace ⟨Lρ i, hLρ i⟩ - hilbertTrace ⟨Lσ i, hLσ i⟩) l (𝓝 0) := by
  intro j q Lρ Lσ hLρ hLσ
  obtain ⟨B, hB⟩ := hL1
  have hBpos : 0 < max B 0 + 1 := by positivity
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / (2 * (max B 0 + 1))
  have hδ : 0 < δ := by positivity
  have hcomp := (Filter.hasBasis_cocompact.tendsto_left_iff.mp hdecay)
    (Metric.ball 0 δ) (Metric.ball_mem_nhds 0 hδ)
  obtain ⟨K, hK, hKbound⟩ := hcomp
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hDbound (z : X) : ‖⟪e z, D (e z)⟫_ℂ‖ ≤ C ^ 2 * ‖D‖ := by
    have hCnn : 0 ≤ C := (norm_nonneg (e z)).trans (hC z)
    calc
      ‖⟪e z, D (e z)⟫_ℂ‖ ≤ ‖e z‖ * ‖D (e z)‖ := norm_inner_le_norm _ _
      _ ≤ ‖e z‖ * (‖D‖ * ‖e z‖) := mul_le_mul_of_nonneg_left (D.le_opNorm _) (norm_nonneg _)
      _ = ‖e z‖ ^ 2 * ‖D‖ := by ring
      _ ≤ C ^ 2 * ‖D‖ := mul_le_mul_of_nonneg_right (by nlinarith [hC z, norm_nonneg (e z)])
        (norm_nonneg D)
  let Mbound : ℝ := C ^ 2 * ‖D‖ + 1
  have hMpos : 0 < Mbound := by positivity
  have hKev : ∀ᶠ i in l, ∫ z in K, ‖ρ i z - σ i z‖ ∂μ < ε / (2 * Mbound) := by
    have h := (Metric.tendsto_nhds.mp (hloc K hK)) (ε / (2 * Mbound)) (by positivity)
    filter_upwards [h] with i hi
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)] at hi
    exact hi
  filter_upwards [hB, hKev] with i hBi hKi
  rw [dist_zero_right]
  obtain ⟨hL₁, hL₂, _, hdiff, _⟩ :=
    sLocalTrace_cutoff_perturbation_bound V e he C hC hrep (ρ i) (σ i) (hρ i) (hσ i)
      (M i) (N i) (hM i) (hN i) D D
  have htrEq : hilbertTrace ⟨Lρ i, hLρ i⟩ - hilbertTrace ⟨Lσ i, hLσ i⟩ =
      ∫ z, (ρ i z - σ i z) * ⟪e z, D (e z)⟫_ℂ ∂μ := by
    have h1 : hilbertTrace ⟨Lρ i, hLρ i⟩ = hilbertTrace ⟨Lρ i, hL₁⟩ := rfl
    have h2 : hilbertTrace ⟨Lσ i, hLσ i⟩ = hilbertTrace ⟨Lσ i, hL₂⟩ := rfl
    rw [h1, h2, hdiff]
    exact integral_congr_ae (Eventually.of_forall fun z ↦ by ring)
  rw [htrEq]
  have hIntDiff : Integrable (fun z ↦ ‖ρ i z - σ i z‖) μ := (hρ i).sub (hσ i) |>.norm
  have hIntProd : Integrable (fun z ↦ ‖ρ i z - σ i z‖ * ‖⟪e z, D (e z)⟫_ℂ‖) μ := by
    refine (hIntDiff.mul_const (C ^ 2 * ‖D‖)).mono'
      (hIntDiff.aestronglyMeasurable.mul
        ((he.inner (D.continuous.comp he)).norm.aestronglyMeasurable)) ?_
    filter_upwards with z
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hDbound z) (norm_nonneg _)
  have hsplit : (∫ z, ‖ρ i z - σ i z‖ * ‖⟪e z, D (e z)⟫_ℂ‖ ∂μ) =
      (∫ z in K, ‖ρ i z - σ i z‖ * ‖⟪e z, D (e z)⟫_ℂ‖ ∂μ) +
        (∫ z in Kᶜ, ‖ρ i z - σ i z‖ * ‖⟪e z, D (e z)⟫_ℂ‖ ∂μ) :=
    (integral_add_compl hKmeas hIntProd).symm
  have hOnK : (∫ z in K, ‖ρ i z - σ i z‖ * ‖⟪e z, D (e z)⟫_ℂ‖ ∂μ) ≤
      Mbound * ∫ z in K, ‖ρ i z - σ i z‖ ∂μ := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hIntProd.integrableOn)
      (hIntDiff.integrableOn.const_mul Mbound) hKmeas fun z _ ↦ ?_
    rw [mul_comm Mbound]
    exact mul_le_mul_of_nonneg_left ((hDbound z).trans (by linarith)) (norm_nonneg _)
  have hOffK : (∫ z in Kᶜ, ‖ρ i z - σ i z‖ * ‖⟪e z, D (e z)⟫_ℂ‖ ∂μ) ≤
      δ * ∫ z, ‖ρ i z - σ i z‖ ∂μ := by
    have h1 : (∫ z in Kᶜ, ‖ρ i z - σ i z‖ * ‖⟪e z, D (e z)⟫_ℂ‖ ∂μ) ≤
        ∫ z in Kᶜ, δ * ‖ρ i z - σ i z‖ ∂μ := by
      refine setIntegral_mono_on hIntProd.integrableOn
        (hIntDiff.integrableOn.const_mul δ) hKmeas.compl fun z hz ↦ ?_
      have hzd : ‖⟪e z, D (e z)⟫_ℂ‖ < δ := by
        simpa only [Metric.mem_ball, dist_zero_right] using hKbound hz
      rw [mul_comm δ]
      exact mul_le_mul_of_nonneg_left hzd.le (norm_nonneg _)
    rw [integral_const_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hIntDiff (Eventually.of_forall fun _ ↦ norm_nonneg _)) hδ.le)
  have hpart1 : Mbound * ∫ z in K, ‖ρ i z - σ i z‖ ∂μ < ε / 2 := by
    calc
      Mbound * ∫ z in K, ‖ρ i z - σ i z‖ ∂μ < Mbound * (ε / (2 * Mbound)) :=
        mul_lt_mul_of_pos_left hKi hMpos
      _ = ε / 2 := by field_simp [hMpos.ne']
  have hpart2 : δ * ∫ z, ‖ρ i z - σ i z‖ ∂μ < ε / 2 := by
    have hB' : ∫ z, ‖ρ i z - σ i z‖ ∂μ < max B 0 + 1 :=
      lt_of_le_of_lt (hBi.trans (le_max_left B 0)) (lt_add_one _)
    calc
      δ * ∫ z, ‖ρ i z - σ i z‖ ∂μ < δ * (max B 0 + 1) := mul_lt_mul_of_pos_left hB' hδ
      _ = ε / 2 := by dsimp only [δ]; field_simp [hBpos.ne']
  calc
    ‖∫ z, (ρ i z - σ i z) * ⟪e z, D (e z)⟫_ℂ ∂μ‖
        ≤ ∫ z, ‖(ρ i z - σ i z) * ⟪e z, D (e z)⟫_ℂ‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ z, ‖ρ i z - σ i z‖ * ‖⟪e z, D (e z)⟫_ℂ‖ ∂μ :=
        integral_congr_ae (Eventually.of_forall fun _ ↦ norm_mul _ _)
    _ ≤ Mbound * (∫ z in K, ‖ρ i z - σ i z‖ ∂μ) + δ * (∫ z, ‖ρ i z - σ i z‖ ∂μ) := by
        rw [hsplit]
        exact add_le_add hOnK hOffK
    _ < ε / 2 + ε / 2 := add_lt_add hpart1 hpart2
    _ = ε := add_halves ε

/-- Paper: Theorem 12.4.1.1, pp. 515–517. Dominated-convergence specialization of
`sLocalTrace_cutoff_tendsto_of_cocompact_decay`: if `ρ_i - σ_i → 0` pointwise a.e. along a
countably generated filter with uniformly bounded supremum norm and uniformly bounded `L¹(μ)` norm,
and `⟪e z, D (e z)⟫ → 0` at `cocompact X`, then the two cutoff compressions have asymptotically
equal Hilbert traces. -/
theorem sLocalTrace_cutoff_tendsto_of_cocompact_decay_ae
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (V : Submodule ℂ H) [CompleteSpace V]
    (e : X → V) (he : Continuous e) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, f⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ))
    (D : V →L[ℂ] V)
    (hdecay : Tendsto (fun z ↦ ⟪e z, D (e z)⟫_ℂ) (cocompact X) (𝓝 0))
    (ρ σ : ι → X → ℂ) (hρ : ∀ i, Integrable (ρ i) μ) (hσ : ∀ i, Integrable (σ i) μ)
    (M N : ι → H →L[ℂ] H)
    (hM : ∀ i (f : H), ∀ᵐ x ∂μ, M i f x = ρ i x * f x)
    (hN : ∀ i (f : H), ∀ᵐ x ∂μ, N i f x = σ i x * f x)
    (hL1 : ∃ B : ℝ, ∀ᶠ i in l, ∫ z, ‖ρ i z - σ i z‖ ∂μ ≤ B)
    (hsup : ∃ K : ℝ, ∀ᶠ i in l, ∀ᵐ z ∂μ, ‖ρ i z - σ i z‖ ≤ K)
    (hae : ∀ᵐ z ∂μ, Tendsto (fun i ↦ ρ i z - σ i z) l (𝓝 0)) :
    let j := V.subtypeL
    let q := V.orthogonalProjectionOnto
    let Lρ (i : ι) := q.comp ((M i).comp (j.comp D))
    let Lσ (i : ι) := q.comp ((N i).comp (j.comp D))
    ∀ (hLρ : ∀ i, IsNuclearOperator (Lρ i)) (hLσ : ∀ i, IsNuclearOperator (Lσ i)),
      Tendsto (fun i ↦ hilbertTrace ⟨Lρ i, hLρ i⟩ - hilbertTrace ⟨Lσ i, hLσ i⟩) l (𝓝 0) := by
  refine sLocalTrace_cutoff_tendsto_of_cocompact_decay V e he C hC hrep D hdecay
    ρ σ hρ hσ M N hM hN hL1 ?_
  intro K hK
  obtain ⟨Bsup, hBsup⟩ := hsup
  have hfin : (μ.restrict K) Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top
  have hdom : Integrable (fun _ : X ↦ Bsup) (μ.restrict K) :=
    integrable_const_iff.mpr (Or.inr ⟨hfin⟩)
  have hlim : Tendsto (fun i ↦ ∫ z in K, ‖ρ i z - σ i z‖ ∂μ) l (𝓝 (∫ _ in K, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ Bsup) ?_ ?_ hdom ?_
    · exact Eventually.of_forall fun i ↦
        ((hρ i).sub (hσ i)).norm.aestronglyMeasurable.restrict
    · filter_upwards [hBsup] with i hi
      filter_upwards [ae_restrict_of_ae hi] with z hz
      simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hz
    · filter_upwards [ae_restrict_of_ae hae] with z hz
      simpa only [norm_zero] using hz.norm
  simpa only [integral_zero] using hlim

end SchattenHolderAndCutoff

section SubspacePolarDefect

/-- For a closed subspace `W` of a Hilbert space `E` and any nuclear endomorphism `A : E →L[ℂ] E`,
the projection compression `W.orthogonalProjectionOnto ∘ A ∘ W.subtypeL` is nuclear and has the
same Hilbert trace as `W.starProjection ∘ A`. -/
private theorem isNuclearOperator_and_hilbertTrace_compression {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (W : Submodule ℂ E) [CompleteSpace W] (A : E →L[ℂ] E) (hA : IsNuclearOperator A) :
    let A_W := W.orthogonalProjectionOnto.comp (A.comp W.subtypeL)
    ∃ hAW : IsNuclearOperator A_W,
      hilbertTrace ⟨A_W, hAW⟩ =
        hilbertTrace ⟨W.starProjection.comp A,
          mul_mem_nuclearEndomorphisms_left W.starProjection ⟨A, hA⟩⟩ := by
  intro A_W
  let j := W.subtypeL
  let q := W.orthogonalProjectionOnto
  have hqA : IsNuclearOperator (q.comp A) := by
    obtain ⟨a, l, y, ha, hl, hy, hs⟩ := (isNuclearOperator_iff_isBanachNuclear A).mp hA
    apply (isNuclearOperator_iff_isBanachNuclear _).mpr
    refine ⟨a, l, q ∘ y, ha, hl, ?_, fun x ↦ ?_⟩
    · simpa only [map_zero] using (q.continuous.tendsto 0).comp hy
    · simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, map_smul] using
        q.hasSum (hs x)
  have hj : Function.Injective j := Subtype.val_injective
  have hcomp : (q.comp A).comp j = A_W := rfl
  have hstar : j.comp (q.comp A) = W.starProjection.comp A := by
    ext x : 1
    rfl
  have hAW : IsNuclearOperator A_W := hcomp ▸ (isNuclearOperator_factor_comps j hj (q.comp A) hqA).1
  have hPA : IsNuclearOperator (W.starProjection.comp A) :=
    mul_mem_nuclearEndomorphisms_left W.starProjection ⟨A, hA⟩
  refine ⟨hAW, ?_⟩
  rw [hilbertTrace_eq_nuclearTrace ⟨A_W, hAW⟩, hilbertTrace_eq_nuclearTrace ⟨W.starProjection.comp A, hPA⟩]
  have hn := nuclearTrace_factor_comps hilbert_approximationProperty
    hilbert_approximationProperty j hj (q.comp A) hqA
  have hL : nuclearTrace hilbert_approximationProperty A_W hAW =
      nuclearTrace hilbert_approximationProperty ((q.comp A).comp j)
        (isNuclearOperator_factor_comps j hj (q.comp A) hqA).1 := rfl
  have hR : nuclearTrace hilbert_approximationProperty (j.comp (q.comp A))
        (isNuclearOperator_factor_comps j hj (q.comp A) hqA).2 =
      nuclearTrace hilbert_approximationProperty (W.starProjection.comp A) hPA := by
    congr 1
  exact hL.trans (hn.trans hR)

/-- The intersection `V ⊓ Wᗮ` of a complete subspace `V` and the orthogonal complement `Wᗮ` is
complete. -/
private theorem completeSpace_inf_orthogonal {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (V W : Submodule ℂ E) [CompleteSpace V] :
    CompleteSpace (V ⊓ Wᗮ : Submodule ℂ E) := by
  have hV : IsClosed (V : Set E) := (completeSpace_coe_iff_isComplete.mp ‹CompleteSpace V›).isClosed
  exact completeSpace_coe_iff_isComplete.mpr (hV.inter W.isClosed_orthogonal).isComplete

/-- Finite sum of convergent nets in `ℂ`. -/
private theorem tendsto_finset_sum_complex {ι κ : Type*} {l : Filter ι}
    (s : Finset κ) (f : κ → ι → ℂ) (a : κ → ℂ)
    (hf : ∀ k ∈ s, Tendsto (f k) l (𝓝 (a k))) :
    Tendsto (fun i ↦ ∑ k ∈ s, f k i) l (𝓝 (∑ k ∈ s, a k)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using tendsto_const_nhds
  | @insert k s hk ih =>
    have h1 := hf k (Finset.mem_insert_self k s)
    have h2 := ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
    simpa only [Finset.sum_insert hk] using h1.add h2

/-- For closed subspaces `W ≤ V` of a Hilbert space `E`, the projection onto `V` splits
orthogonally as the sum of the projections onto `W` and `V ⊓ Wᗮ`. -/
private theorem starProjection_split_of_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (V W : Submodule ℂ E) [CompleteSpace V] [CompleteSpace W]
    [CompleteSpace (V ⊓ Wᗮ : Submodule ℂ E)] (hWV : W ≤ V) :
    V.starProjection = W.starProjection + (V ⊓ Wᗮ).starProjection := by
  ext x : 1
  rw [add_apply]
  let pV := V.starProjection x
  let pW := W.starProjection x
  have hpWV : pW ∈ V := hWV (W.starProjection_apply_mem x)
  have hdiffV : pV - pW ∈ V := V.sub_mem (V.starProjection_apply_mem x) hpWV
  have hdiffW : pV - pW ∈ Wᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    have h1 : ⟪w, pV⟫_ℂ = ⟪w, x⟫_ℂ := by
      rw [← V.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr (hWV hw)]
    have h2 : ⟪w, pW⟫_ℂ = ⟪w, x⟫_ℂ := by
      rw [← W.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hw]
    rw [inner_sub_right, h1, h2, sub_self]
  have hdiffMem : pV - pW ∈ (V ⊓ Wᗮ : Submodule ℂ E) := ⟨hdiffV, hdiffW⟩
  have hK : (V ⊓ Wᗮ).starProjection x = pV - pW := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hdiffMem fun k hk ↦ ?_
    have h1 : ⟪x - pV, k⟫_ℂ = 0 := V.starProjection_inner_eq_zero x k hk.1
    have h2 : ⟪pW, k⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal W k).mp hk.2 pW (W.starProjection_apply_mem x)
    have hsplit : x - (pV - pW) = (x - pV) + pW := by abel
    rw [hsplit, inner_add_left, h1, h2, add_zero]
  rw [hK]
  exact (add_sub_cancel pW pV).symm

/-- For closed subspaces `W ≤ V` of a Hilbert space `E` and any nuclear endomorphism `T` of `E`
whose range lies in `V` (`V.starProjection ∘ T = T`), the compression `T_W` to `W` is nuclear,
and for any finite orthonormal basis `b` of `V ⊓ Wᗮ` the trace difference `Tr(T) - Tr(T_W)` equals
the diagonal sum `∑ i, ⟪b i, T (b i)⟫`. -/
private theorem hilbertTrace_subspace_split_ambient {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (V W : Submodule ℂ E) [CompleteSpace V] [CompleteSpace W]
    [CompleteSpace (V ⊓ Wᗮ : Submodule ℂ E)] (hWV : W ≤ V)
    (T : E →L[ℂ] E) (hT : IsNuclearOperator T) (hTV : V.starProjection.comp T = T) :
    let K : Submodule ℂ E := V ⊓ Wᗮ
    let T_W := W.orthogonalProjectionOnto.comp (T.comp W.subtypeL)
    ∃ hTW : IsNuclearOperator T_W,
      ∀ {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ K),
        hilbertTrace ⟨T, hT⟩ - hilbertTrace ⟨T_W, hTW⟩ =
          ∑ i : Fin n, ⟪(b i : E), T (b i : E)⟫_ℂ := by
  intro K T_W
  obtain ⟨hTW, htrW⟩ := isNuclearOperator_and_hilbertTrace_compression W T hT
  have hPW : IsNuclearOperator (W.starProjection.comp T) :=
    mul_mem_nuclearEndomorphisms_left W.starProjection ⟨T, hT⟩
  have hPK : IsNuclearOperator (K.starProjection.comp T) :=
    mul_mem_nuclearEndomorphisms_left K.starProjection ⟨T, hT⟩
  have hsum : W.starProjection.comp T + K.starProjection.comp T = T := by
    rw [← ContinuousLinearMap.add_comp, ← starProjection_split_of_le V W hWV, hTV]
  obtain ⟨f, hf⟩ := @hilbertTrace_linear E _ _ _
  have hEq : (⟨T, hT⟩ : nuclearEndomorphisms E) =
      ⟨W.starProjection.comp T, hPW⟩ + ⟨K.starProjection.comp T, hPK⟩ :=
    Subtype.ext hsum.symm
  have hsplit : hilbertTrace ⟨T, hT⟩ =
      hilbertTrace ⟨T_W, hTW⟩ + hilbertTrace ⟨K.starProjection.comp T, hPK⟩ := by
    calc
      hilbertTrace ⟨T, hT⟩ = f ⟨T, hT⟩ := (hf _).symm
      _ = f (⟨W.starProjection.comp T, hPW⟩ + ⟨K.starProjection.comp T, hPK⟩) := congrArg f hEq
      _ = f ⟨W.starProjection.comp T, hPW⟩ + f ⟨K.starProjection.comp T, hPK⟩ := map_add f _ _
      _ = hilbertTrace ⟨W.starProjection.comp T, hPW⟩ +
            hilbertTrace ⟨K.starProjection.comp T, hPK⟩ := by rw [hf, hf]
      _ = hilbertTrace ⟨T_W, hTW⟩ + hilbertTrace ⟨K.starProjection.comp T, hPK⟩ := by rw [htrW]
  refine ⟨hTW, fun {n} b ↦ ?_⟩
  rw [hsplit, add_sub_cancel_left]
  have hPdecomp : K.starProjection.comp T =
      ∑ i : Fin n, ((innerSL ℂ (b i : E)).comp T).smulRight (b i : E) := by
    ext x : 1
    rw [ContinuousLinearMap.comp_apply, sum_apply, Submodule.starProjection_apply,
      b.orthogonalProjectionOnto_apply_eq_sum (T x), Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [SetLike.val_smul]
  let R (i : Fin n) : nuclearEndomorphisms E :=
    ⟨((innerSL ℂ (b i : E)).comp T).smulRight (b i : E), smulRight_mem_nuclearEndomorphisms _ _⟩
  have hREq : (⟨K.starProjection.comp T, hPK⟩ : nuclearEndomorphisms E) = ∑ i : Fin n, R i := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum] using hPdecomp
  calc
    hilbertTrace ⟨K.starProjection.comp T, hPK⟩ = f ⟨K.starProjection.comp T, hPK⟩ := (hf _).symm
    _ = f (∑ i : Fin n, R i) := congrArg f hREq
    _ = ∑ i : Fin n, f (R i) := map_sum f R Finset.univ
    _ = ∑ i : Fin n, hilbertTrace (R i) := Finset.sum_congr rfl fun i _ ↦ hf (R i)
    _ = ∑ i : Fin n, ⟪(b i : E), T (b i : E)⟫_ℂ :=
          Finset.sum_congr rfl fun i _ ↦ hilbertTrace_smulRight _ _

/-- In a finite orthonormal basis, the diagonal inner-product sum equals `LinearMap.trace`. -/
private theorem sum_orthonormalBasis_inner_eq_linearTrace {K ι : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ K) (B : K →ₗ[ℂ] K) :
    (∑ i : ι, ⟪b i, B (b i)⟫_ℂ) = LinearMap.trace ℂ K B := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis B, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change ⟪b i, B (b i)⟫_ℂ = (LinearMap.toMatrix b.toBasis b.toBasis B) i i
  rw [LinearMap.toMatrix_apply, b.coe_toBasis, b.coe_toBasis_repr_apply, b.repr_apply_apply]

/-- Paper: Theorem 12.4.1.1, pp. 515–517, and its sublevel restriction on p. 520. For a closed
subspace `W ≤ V` of an evaluable Hilbert level `V` in `L²(μ)` that is invariant under `D`
(with restriction `D_W : W →L[ℂ] W`), the projected evaluation family `e_W(x) = P_W e(x)` keeps
the uniform evaluation bound `C` and reproduces `W`. The cutoff compression trace on `V` splits
additively as the sum of the cutoff compression trace on `W` and the trace on the relative
orthogonal complement `K = V ⊓ Wᗮ`, and when `K` has a finite orthonormal basis `b` the difference
`Tr_V - Tr_W` is the explicit finite sum of cutoff-weighted diagonal pairings over `b`. -/
theorem sLocalTrace_subspace_compression_split
    (V W : Submodule ℂ H) [CompleteSpace V] [CompleteSpace W] (hWV : W ≤ V)
    (e : X → V) (he : Continuous e) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, f⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ))
    (ρ : X → ℂ) (hρ : Integrable ρ μ)
    (M : H →L[ℂ] H) (hM : ∀ f : H, ∀ᵐ x ∂μ, M f x = ρ x * f x)
    (D : V →L[ℂ] V) (D_W : W →L[ℂ] W)
    (hDW : ∀ f : W, (D ⟨f.1, hWV f.2⟩ : H) = (D_W f : H)) :
    let K : Submodule ℂ H := V ⊓ Wᗮ
    let eW (x : X) : W := W.orthogonalProjectionOnto (e x : H)
    let L_V := V.orthogonalProjectionOnto.comp (M.comp (V.subtypeL.comp D))
    let L_W := W.orthogonalProjectionOnto.comp (M.comp (W.subtypeL.comp D_W))
    Continuous eW ∧
    (∀ x, ‖eW x‖ ≤ C) ∧
    (∀ f : W, (fun x ↦ ⟪eW x, f⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ)) ∧
    ∃ (hLV : IsNuclearOperator L_V) (hLW : IsNuclearOperator L_W),
      ∀ {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ K),
        hilbertTrace ⟨L_V, hLV⟩ - hilbertTrace ⟨L_W, hLW⟩ =
          ∑ i : Fin n, ∫ z, ρ z * (conj (((b i : K) : H) z) *
            ((D ⟨(b i : H), (b i).2.1⟩ : H) z)) ∂μ := by
  intro K eW L_V L_W
  have heWCont : Continuous eW := W.orthogonalProjectionOnto.continuous.comp (V.subtypeL.continuous.comp he)
  have heWBound (x : X) : ‖eW x‖ ≤ C :=
    (W.norm_orthogonalProjectionOnto_apply_le (e x : H)).trans (hC x)
  have heWRep (f : W) : (fun x ↦ ⟪eW x, f⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ) := by
    filter_upwards [hrep ⟨f.1, hWV f.2⟩] with x hx
    change ⟪W.orthogonalProjectionOnto (e x : H), f⟫_ℂ = ((f : H) : X → ℂ) x
    rw [W.inner_orthogonalProjectionOnto_eq_of_mem_right f (e x : H)]
    exact hx
  have : CompleteSpace K := completeSpace_inf_orthogonal V W
  obtain ⟨hTV, hLV, _, _, _, _, hTtr, hLtr, _, _, _⟩ :=
    sLocalTrace_measurableCutoffKernel V e he C hC hrep ρ hρ M hM D
  let T_V := V.subtypeL.comp (L_V.comp V.orthogonalProjectionOnto)
  have hTVproj : V.starProjection.comp T_V = T_V := by
    ext f : 1
    exact V.starProjection_eq_self_iff.mpr (L_V (V.orthogonalProjectionOnto f)).property
  obtain ⟨hTW', hbasis⟩ :=
    hilbertTrace_subspace_split_ambient V W hWV T_V hTV hTVproj
  have hTW_eq : W.orthogonalProjectionOnto.comp (T_V.comp W.subtypeL) = L_W := by
    ext f : 1
    apply Subtype.ext
    change (W.orthogonalProjectionOnto (V.subtypeL (L_V (V.orthogonalProjectionOnto (f : H)))) : H) =
      (W.orthogonalProjectionOnto (M (D_W f : H)) : H)
    have hqV : V.orthogonalProjectionOnto (f : H) = ⟨f.1, hWV f.2⟩ :=
      V.orthogonalProjectionOnto_mem_subspace_eq_self ⟨f.1, hWV f.2⟩
    have hVtoW (y : H) :
        (W.orthogonalProjectionOnto (V.orthogonalProjectionOnto y : H) : H) =
          (W.orthogonalProjectionOnto y : H) := by
      have h := congrArg (fun op : H →L[ℂ] H ↦ op y) (Submodule.starProjection_comp_starProjection_of_le hWV)
      simpa only [ContinuousLinearMap.comp_apply, Submodule.starProjection_apply] using h
    rw [hqV]
    change (W.orthogonalProjectionOnto (V.orthogonalProjectionOnto (M (D ⟨f.1, hWV f.2⟩ : H)) : H) : H) =
      (W.orthogonalProjectionOnto (M (D_W f : H)) : H)
    rw [hVtoW, hDW f]
  have hLW : IsNuclearOperator L_W := hTW_eq ▸ hTW'
  have hLVeqT : hilbertTrace ⟨L_V, hLV⟩ = hilbertTrace ⟨T_V, hTV⟩ := hLtr.trans hTtr.symm
  have hLWeq : hilbertTrace ⟨L_W, hLW⟩ =
      hilbertTrace ⟨W.orthogonalProjectionOnto.comp (T_V.comp W.subtypeL), hTW'⟩ :=
    congrArg hilbertTrace (Subtype.ext hTW_eq.symm)
  refine ⟨heWCont, heWBound, heWRep, hLV, hLW, ?_⟩
  intro n b
  have hdiff : hilbertTrace ⟨L_V, hLV⟩ - hilbertTrace ⟨L_W, hLW⟩ =
      ∑ i : Fin n, ⟪(b i : H), T_V (b i : H)⟫_ℂ :=
    (congrArg₂ (· - ·) hLVeqT hLWeq).trans (hbasis b)
  rw [hdiff]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  let uV : V := ⟨(b i : H), (b i).2.1⟩
  have hqV : V.orthogonalProjectionOnto (b i : H) = uV :=
    V.orthogonalProjectionOnto_mem_subspace_eq_self uV
  change ⟪(uV : H), (V.orthogonalProjectionOnto (M (D (V.orthogonalProjectionOnto (b i : H)) : H)) : H)⟫_ℂ = _
  rw [hqV]
  change ⟪uV, V.orthogonalProjectionOnto (M (D uV : H))⟫_ℂ = _
  rw [V.inner_orthogonalProjectionOnto_eq_of_mem_left uV (M (D uV : H)), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hM (D uV : H)] with z hz
  change ⟪(uV : H) z, M (D uV : H) z⟫_ℂ = _
  rw [hz, RCLike.inner_apply]
  ring

/-- Paper: Theorem 12.4.1.1, pp. 515–517, and p. 520. For closed subspaces `W ≤ V` of `L²(μ)`
where `V` is an evaluable level, `D` preserves `W` (with restriction `D_W`), and the relative
orthogonal complement `K = V ⊓ Wᗮ` is finite-dimensional, for any uniformly bounded family of
integrable cutoffs `ρ_i → 1` a.e. along a countably generated filter, the trace difference
`Tr_V(L_V(ρ_i)) - Tr_W(L_W(ρ_i))` converges to the finite-dimensional linear trace of the
compression of `D` to `K`. -/
theorem sLocalTrace_finiteCodim_defect_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (V W : Submodule ℂ H) [CompleteSpace V] [CompleteSpace W] (hWV : W ≤ V)
    [FiniteDimensional ℂ (V ⊓ Wᗮ : Submodule ℂ H)]
    (e : X → V) (he : Continuous e) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, f⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ))
    (D : V →L[ℂ] V) (D_W : W →L[ℂ] W)
    (hDW : ∀ f : W, (D ⟨f.1, hWV f.2⟩ : H) = (D_W f : H))
    (ρ : ι → X → ℂ) (hρ : ∀ i, Integrable (ρ i) μ)
    (M : ι → H →L[ℂ] H) (hM : ∀ i (f : H), ∀ᵐ x ∂μ, M i f x = ρ i x * f x)
    (hbound : ∃ B : ℝ, ∀ᶠ i in l, ∀ᵐ z ∂μ, ‖ρ i z‖ ≤ B)
    (hae : ∀ᵐ z ∂μ, Tendsto (fun i ↦ ρ i z) l (𝓝 1)) :
    let K : Submodule ℂ H := V ⊓ Wᗮ
    let L_V (i : ι) := V.orthogonalProjectionOnto.comp ((M i).comp (V.subtypeL.comp D))
    let L_W (i : ι) := W.orthogonalProjectionOnto.comp ((M i).comp (W.subtypeL.comp D_W))
    let D_K : K →ₗ[ℂ] K :=
      { toFun := fun u ↦ K.orthogonalProjectionOnto (D ⟨u.1, u.2.1⟩ : H)
        map_add' := fun u v ↦ by
          change K.orthogonalProjectionOnto (D (⟨u.1, u.2.1⟩ + ⟨v.1, v.2.1⟩) : H) = _
          rw [map_add, Submodule.coe_add, map_add]
        map_smul' := fun c u ↦ by
          change K.orthogonalProjectionOnto (D (c • ⟨u.1, u.2.1⟩) : H) = _
          rw [map_smul, SetLike.val_smul, map_smul, RingHom.id_apply] }
    ∀ (hLV : ∀ i, IsNuclearOperator (L_V i)) (hLW : ∀ i, IsNuclearOperator (L_W i)),
      Tendsto (fun i ↦ hilbertTrace ⟨L_V i, hLV i⟩ - hilbertTrace ⟨L_W i, hLW i⟩) l
        (𝓝 (LinearMap.trace ℂ K D_K)) := by
  intro K L_V L_W D_K hLV hLW
  obtain ⟨B, hB⟩ := hbound
  let b := stdOrthonormalBasis ℂ K
  have hdiff (i : ι) :
      hilbertTrace ⟨L_V i, hLV i⟩ - hilbertTrace ⟨L_W i, hLW i⟩ =
        ∑ k, ∫ z, ρ i z * (conj (((b k : K) : H) z) *
          ((D ⟨(b k : H), (b k).2.1⟩ : H) z)) ∂μ := by
    obtain ⟨_, _, _, hLV', hLW', hbasis⟩ :=
      sLocalTrace_subspace_compression_split V W hWV e he C hC hrep (ρ i) (hρ i) (M i) (hM i)
        D D_W hDW
    have h1 : hilbertTrace ⟨L_V i, hLV i⟩ = hilbertTrace ⟨L_V i, hLV'⟩ := rfl
    have h2 : hilbertTrace ⟨L_W i, hLW i⟩ = hilbertTrace ⟨L_W i, hLW'⟩ := rfl
    rw [h1, h2]
    exact hbasis b
  have hterm (k : Fin (Module.finrank ℂ K)) :
      Tendsto (fun i ↦ ∫ z, ρ i z * (conj (((b k : K) : H) z) *
          ((D ⟨(b k : H), (b k).2.1⟩ : H) z)) ∂μ) l
        (𝓝 ⟪b k, D_K (b k)⟫_ℂ) := by
    let u : H := (b k : H)
    let v : H := (D ⟨(b k : H), (b k).2.1⟩ : H)
    have hpair : ⟪b k, D_K (b k)⟫_ℂ = ∫ z, conj (u z) * v z ∂μ := by
      change ⟪b k, K.orthogonalProjectionOnto v⟫_ℂ = _
      rw [K.inner_orthogonalProjectionOnto_eq_of_mem_left (b k) v]
      change ⟪u, v⟫_ℂ = _
      rw [L2.inner_def]
      exact integral_congr_ae (Eventually.of_forall fun z ↦ by
        dsimp only
        rw [RCLike.inner_apply, mul_comm])
    rw [hpair]
    have huvInt : Integrable (fun z ↦ ‖u z‖ * ‖v z‖) μ :=
      (Lp.memLp u).norm.integrable_mul (Lp.memLp v).norm
    have hdom : Integrable (fun z ↦ max B 0 * (‖u z‖ * ‖v z‖)) μ := huvInt.const_mul (max B 0)
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z ↦ max B 0 * (‖u z‖ * ‖v z‖)) ?_ ?_ hdom ?_
    · refine Eventually.of_forall fun i ↦ ?_
      exact (hρ i).aestronglyMeasurable.mul
        ((Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).mul
          (Lp.aestronglyMeasurable v))
    · filter_upwards [hB] with i hBi
      filter_upwards [hBi] with z hBz
      rw [norm_mul, norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_right (hBz.trans (le_max_left B 0))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    · filter_upwards [hae] with z hz
      simpa only [one_mul] using hz.mul_const (conj (u z) * v z)
  have hsum := tendsto_finset_sum_complex Finset.univ _ _ fun k _ ↦ hterm k
  have hlim : (∑ k, ⟪b k, D_K (b k)⟫_ℂ) = LinearMap.trace ℂ K D_K :=
    sum_orthonormalBasis_inner_eq_linearTrace b D_K
  rw [hlim] at hsum
  exact hsum.congr fun i ↦ (hdiff i).symm

/-- Abstract finite-codimension invariant-functional trace identity inside a closed ambient
subspace `V` of a Hilbert space `E`. -/
private theorem invariantFunctionals_ambient_subspace_and_trace {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (V W : Submodule ℂ E) [CompleteSpace V] [CompleteSpace W] (hWV : W ≤ V)
    {m : ℕ} (D : V →L[ℂ] V) (ℓ : Fin m → (V →L[ℂ] ℂ)) (hlin : LinearIndependent ℂ ℓ)
    (A : Fin m → Fin m → ℂ) (hinv : ∀ k (f : V), ℓ k (D f) = ∑ j, A k j * ℓ j f)
    (hW : ∀ f : V, (f : E) ∈ W ↔ ∀ k : Fin m, ℓ k f = 0) :
    let K : Submodule ℂ E := V ⊓ Wᗮ
    FiniteDimensional ℂ K ∧
      (∀ f : W, (D ⟨f.1, hWV f.2⟩ : E) ∈ W) ∧
      ∀ [CompleteSpace K],
        let D_K : K →ₗ[ℂ] K :=
          { toFun := fun u ↦ K.orthogonalProjectionOnto (D ⟨u.1, u.2.1⟩ : E)
            map_add' := fun u v ↦ by
              change K.orthogonalProjectionOnto (D (⟨u.1, u.2.1⟩ + ⟨v.1, v.2.1⟩) : E) = _
              rw [map_add, Submodule.coe_add, map_add]
            map_smul' := fun c u ↦ by
              change K.orthogonalProjectionOnto (D (c • ⟨u.1, u.2.1⟩) : E) = _
              rw [map_smul, SetLike.val_smul, map_smul, RingHom.id_apply] }
        LinearMap.trace ℂ K D_K = ∑ k : Fin m, A k k := by
  intro K
  let r : Fin m → V := fun k ↦ (InnerProductSpace.toDual ℂ V).symm (ℓ k)
  have hr (k : Fin m) (f : V) : ⟪r k, f⟫_ℂ = ℓ k f := InnerProductSpace.toDual_symm_apply
  let rE : Fin m → E := fun k ↦ (r k : E)
  let Rspan : Submodule ℂ E := Submodule.span ℂ (Set.range rE)
  have hRfin : FiniteDimensional ℂ Rspan := FiniteDimensional.span_of_finite ℂ (Set.finite_range rE)
  have hRcomp : CompleteSpace Rspan := FiniteDimensional.completeSpace ℂ Rspan
  have hRleV : Rspan ≤ V := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact (r k).property
  have hKeq : K = Rspan := by
    have hW_eq : W = V ⊓ Rspanᗮ := by
      ext x
      constructor
      · intro hx
        refine ⟨hWV hx, ?_⟩
        change x ∈ Rspanᗮ
        rw [Submodule.mem_orthogonal]
        intro u hu
        refine Submodule.span_induction ?_ (by simp)
          (fun a b _ _ ha hb ↦ by rw [inner_add_left, ha, hb, add_zero])
          (fun c a _ ha ↦ by rw [inner_smul_left, ha, mul_zero]) hu
        rintro _ ⟨k, rfl⟩
        change ⟪r k, (⟨x, hWV hx⟩ : V)⟫_ℂ = 0
        rw [hr k ⟨x, hWV hx⟩]
        exact (hW ⟨x, hWV hx⟩).mp hx k
      · rintro ⟨hxV, hxR⟩
        refine (hW ⟨x, hxV⟩).mpr fun k ↦ ?_
        rw [← hr k ⟨x, hxV⟩]
        exact (Submodule.mem_orthogonal Rspan x).mp hxR (rE k) (Submodule.subset_span ⟨k, rfl⟩)
    apply le_antisymm
    · intro x hx
      have hprojV : Rspan.starProjection x ∈ V := hRleV (Rspan.starProjection_apply_mem x)
      have hremV : x - Rspan.starProjection x ∈ V := V.sub_mem hx.1 hprojV
      have hremR : x - Rspan.starProjection x ∈ Rspanᗮ := Rspan.sub_starProjection_mem_orthogonal x
      have hremW : x - Rspan.starProjection x ∈ W := hW_eq.symm ▸ ⟨hremV, hremR⟩
      have hzero : ⟪x - Rspan.starProjection x, x - Rspan.starProjection x⟫_ℂ = 0 := by
        have h1 : ⟪x - Rspan.starProjection x, x⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal W x).mp hx.2 _ hremW
        have h2 : ⟪x - Rspan.starProjection x, Rspan.starProjection x⟫_ℂ = 0 := by
          rw [inner_eq_zero_symm]
          exact (Submodule.mem_orthogonal Rspan _).mp hremR _ (Rspan.starProjection_apply_mem x)
        rw [inner_sub_right, h1, h2, sub_zero]
      have hxeq : x = Rspan.starProjection x := sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
      exact hxeq ▸ Rspan.starProjection_apply_mem x
    · intro x hx
      refine ⟨hRleV hx, ?_⟩
      change x ∈ Wᗮ
      rw [Submodule.mem_orthogonal]
      intro w hw
      have hwR : w ∈ Rspanᗮ := (hW_eq ▸ hw).2
      rw [inner_eq_zero_symm]
      exact (Submodule.mem_orthogonal Rspan w).mp hwR x hx
  have hKfin : FiniteDimensional ℂ K := hKeq ▸ hRfin
  have hDinv : ∀ f : W, (D ⟨f.1, hWV f.2⟩ : E) ∈ W := by
    intro f
    refine (hW (D ⟨f.1, hWV f.2⟩)).mpr fun k ↦ ?_
    rw [hinv k ⟨f.1, hWV f.2⟩]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [(hW ⟨f.1, hWV f.2⟩).mp f.property j, mul_zero]
  have hDadj (k : Fin m) : D.adjoint (r k) = ∑ j : Fin m, conj (A k j) • r j := by
    apply ext_inner_right ℂ
    intro f
    rw [D.adjoint_inner_left, hr k (D f), hinv k f, sum_inner]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [inner_smul_left, Complex.conj_conj, hr j f]
  have hrLin : LinearIndependent ℂ r := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hdual : ∑ k : Fin m, conj (g k) • ℓ k = 0 := by
      have h0 : InnerProductSpace.toDual ℂ V (∑ k : Fin m, g k • r k) = 0 := by
        rw [hg, map_zero]
      rw [map_sum] at h0
      refine (Finset.sum_congr rfl fun k _ ↦ ?_).symm.trans h0
      rw [LinearIsometryEquiv.map_smulₛₗ]
      simp [r]
    intro k
    have hzk := (Fintype.linearIndependent_iff.mp hlin) (fun j ↦ conj (g j)) hdual k
    exact (starRingEnd ℂ).injective (by simpa using hzk)
  let rK : Fin m → K := fun k ↦ ⟨rE k, by rw [hKeq]; exact Submodule.subset_span ⟨k, rfl⟩⟩
  have hrKLin : LinearIndependent ℂ rK := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    apply Fintype.linearIndependent_iff.mp hrLin g
    apply Subtype.ext
    have hval := congrArg Subtype.val hg
    simpa only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero, rK, rE] using hval
  have hrKSpan : ⊤ ≤ Submodule.span ℂ (Set.range rK) := by
    intro u _
    have hu : (u : E) ∈ Rspan := hKeq ▸ u.property
    have hmap : (Submodule.span ℂ (Set.range rK)).map K.subtype = Rspan := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    have : (u : E) ∈ (Submodule.span ℂ (Set.range rK)).map K.subtype := hmap.symm ▸ hu
    obtain ⟨v, hv, hvu⟩ := this
    exact Subtype.ext hvu ▸ hv
  let bR : Module.Basis (Fin m) ℂ K := Module.Basis.mk hrKLin hrKSpan
  have hbR (k : Fin m) : bR k = rK k := Module.Basis.mk_apply hrKLin hrKSpan k
  have hDadjMem : ∀ u : K, (D.adjoint ⟨u.1, u.2.1⟩ : E) ∈ K := by
    intro u
    have huEq : (⟨u.1, u.2.1⟩ : V) = ∑ k : Fin m, bR.repr u k • r k := by
      have hu := (bR.sum_repr u).symm
      apply Subtype.ext
      have hval := congrArg Subtype.val hu
      simpa only [Submodule.coe_sum, SetLike.val_smul, hbR, rK, rE] using hval
    rw [huEq, map_sum, Submodule.coe_sum]
    refine K.sum_mem fun k _ ↦ ?_
    rw [map_smul, SetLike.val_smul, hDadj k, Submodule.coe_sum]
    refine K.smul_mem _ (K.sum_mem fun j _ ↦ K.smul_mem _ ?_)
    exact (rK j).property
  let Dadj : K →ₗ[ℂ] K :=
    { toFun := fun u ↦ ⟨(D.adjoint ⟨u.1, u.2.1⟩ : E), hDadjMem u⟩
      map_add' := fun u v ↦ by
        apply Subtype.ext
        change (D.adjoint (⟨u.1, u.2.1⟩ + ⟨v.1, v.2.1⟩) : E) = _
        rw [map_add, Submodule.coe_add]
        rfl
      map_smul' := fun c u ↦ by
        apply Subtype.ext
        change (D.adjoint (c • ⟨u.1, u.2.1⟩) : E) = _
        rw [map_smul, SetLike.val_smul]
        rfl }
  have hDadjTrace : LinearMap.trace ℂ K Dadj = ∑ k : Fin m, conj (A k k) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ bR Dadj, Matrix.trace]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    change (LinearMap.toMatrix bR bR Dadj) k k = conj (A k k)
    rw [LinearMap.toMatrix_apply, hbR k]
    have hDadjEq : Dadj (rK k) = ∑ j : Fin m, conj (A k j) • bR j := by
      apply Subtype.ext
      change (D.adjoint (r k) : E) = _
      rw [hDadj k, Submodule.coe_sum, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [SetLike.val_smul, SetLike.val_smul, hbR j]
    have hrepr : bR.repr (Dadj (rK k)) = ∑ j : Fin m, conj (A k j) • Finsupp.single j (1 : ℂ) := by
      rw [hDadjEq, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_smul, bR.repr_self]
    rw [hrepr]
    simp [Finsupp.single_apply]
  refine ⟨hKfin, hDinv, ?_⟩
  intro _ D_K
  let b := stdOrthonormalBasis ℂ K
  have hconjEq : LinearMap.trace ℂ K D_K = conj (LinearMap.trace ℂ K Dadj) := by
    rw [← sum_orthonormalBasis_inner_eq_linearTrace b D_K,
      ← sum_orthonormalBasis_inner_eq_linearTrace b Dadj, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change ⟪b i, K.orthogonalProjectionOnto (D ⟨(b i : E), (b i).2.1⟩ : E)⟫_ℂ =
      conj ⟪b i, Dadj (b i)⟫_ℂ
    rw [K.inner_orthogonalProjectionOnto_eq_of_mem_left]
    change ⟪(⟨(b i : E), (b i).2.1⟩ : V), D ⟨(b i : E), (b i).2.1⟩⟫_ℂ =
      conj ⟪(⟨(b i : E), (b i).2.1⟩ : V), D.adjoint ⟨(b i : E), (b i).2.1⟩⟫_ℂ
    rw [inner_conj_symm, D.adjoint_inner_left]
  rw [hconjEq, hDadjTrace, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ Complex.conj_conj (A k k)

/-- Paper: Theorem 12.4.1.1, pp. 515–517, and p. 520. Let `ℓ_0, …, ℓ_{m-1}` be linearly
independent bounded linear functionals on an evaluable Hilbert level `V ⊆ L²(μ)` closed under
pullback by `D` (`ℓ_k ∘ D = ∑_j A_{k,j} ℓ_j`, covering diagonal polar eigenfunctionals as well as
triangular Taylor-jet flags `f^{(2k)}(0)`). On the closed sublevel `W ≤ V` cut out by `ℓ_k = 0`,
`D` restricts to a bounded endomorphism `D_W : W →L[ℂ] W`, and along every uniformly bounded family
of integrable cutoffs `ρ_i → 1` a.e. (countably generated filter), the trace defect
`Tr_V(L_V(ρ_i)) - Tr_W(L_W(ρ_i))` converges to `∑_k A_{k,k}` independently of the weight measure
`μ` and without requiring orthogonality of the Riesz representers of `ℓ_k`. -/
theorem sLocalTrace_invariantFunctionals_defect_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (V W : Submodule ℂ H) [CompleteSpace V] [CompleteSpace W] (hWV : W ≤ V)
    (e : X → V) (he : Continuous e) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, f⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ))
    (D : V →L[ℂ] V) {m : ℕ}
    (ℓ : Fin m → (V →L[ℂ] ℂ)) (hlin : LinearIndependent ℂ ℓ)
    (A : Fin m → Fin m → ℂ) (hinv : ∀ k (f : V), ℓ k (D f) = ∑ j, A k j * ℓ j f)
    (hW : ∀ f : V, (f : H) ∈ W ↔ ∀ k : Fin m, ℓ k f = 0)
    (D_W : W →L[ℂ] W) (hDW : ∀ f : W, (D ⟨f.1, hWV f.2⟩ : H) = (D_W f : H))
    (ρ : ι → X → ℂ) (hρ : ∀ i, Integrable (ρ i) μ)
    (M : ι → H →L[ℂ] H) (hM : ∀ i (f : H), ∀ᵐ x ∂μ, M i f x = ρ i x * f x)
    (hbound : ∃ B : ℝ, ∀ᶠ i in l, ∀ᵐ z ∂μ, ‖ρ i z‖ ≤ B)
    (hae : ∀ᵐ z ∂μ, Tendsto (fun i ↦ ρ i z) l (𝓝 1)) :
    let L_V (i : ι) := V.orthogonalProjectionOnto.comp ((M i).comp (V.subtypeL.comp D))
    let L_W (i : ι) := W.orthogonalProjectionOnto.comp ((M i).comp (W.subtypeL.comp D_W))
    ∃ (hLV : ∀ i, IsNuclearOperator (L_V i)) (hLW : ∀ i, IsNuclearOperator (L_W i)),
      Tendsto (fun i ↦ hilbertTrace ⟨L_V i, hLV i⟩ - hilbertTrace ⟨L_W i, hLW i⟩) l
        (𝓝 (∑ k : Fin m, A k k)) := by
  intro L_V L_W
  obtain ⟨hKfin, _, htr⟩ :=
    invariantFunctionals_ambient_subspace_and_trace V W hWV D ℓ hlin A hinv hW
  have hnuc (i : ι) : ∃ (hLV : IsNuclearOperator (L_V i)) (hLW : IsNuclearOperator (L_W i)), True := by
    obtain ⟨_, _, _, hLV, hLW, _⟩ :=
      sLocalTrace_subspace_compression_split V W hWV e he C hC hrep (ρ i) (hρ i) (M i) (hM i)
        D D_W hDW
    exact ⟨hLV, hLW, trivial⟩
  choose hLV hLW _ using hnuc
  refine ⟨hLV, hLW, ?_⟩
  rw [← htr]
  exact sLocalTrace_finiteCodim_defect_tendsto V W hWV e he C hC hrep D D_W hDW
    ρ hρ M hM hbound hae hLV hLW

/-- Paper: Theorem 12.4.1.1, pp. 515–517, and p. 520. Diagonal eigenfunctional specialization of
`sLocalTrace_invariantFunctionals_defect_tendsto`: if `ℓ_0, …, ℓ_{m-1}` are linearly independent
bounded eigenfunctionals of `D` with eigenvalues `ev_0, …, ev_{m-1}` (`ℓ_k ∘ D = ev_k • ℓ_k`),
then restricting to the closed sublevel `W ≤ V` where `ℓ_k = 0` subtracts `∑_k ev_k` from the
cutoff-compression trace limit along every uniformly bounded cutoff family `ρ_i → 1` a.e. -/
theorem sLocalTrace_eigenfunctionals_defect_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (V W : Submodule ℂ H) [CompleteSpace V] [CompleteSpace W] (hWV : W ≤ V)
    (e : X → V) (he : Continuous e) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, f⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ))
    (D : V →L[ℂ] V) {m : ℕ}
    (ℓ : Fin m → (V →L[ℂ] ℂ)) (hlin : LinearIndependent ℂ ℓ)
    (ev : Fin m → ℂ) (hev : ∀ k (f : V), ℓ k (D f) = ev k * ℓ k f)
    (hW : ∀ f : V, (f : H) ∈ W ↔ ∀ k : Fin m, ℓ k f = 0)
    (D_W : W →L[ℂ] W) (hDW : ∀ f : W, (D ⟨f.1, hWV f.2⟩ : H) = (D_W f : H))
    (ρ : ι → X → ℂ) (hρ : ∀ i, Integrable (ρ i) μ)
    (M : ι → H →L[ℂ] H) (hM : ∀ i (f : H), ∀ᵐ x ∂μ, M i f x = ρ i x * f x)
    (hbound : ∃ B : ℝ, ∀ᶠ i in l, ∀ᵐ z ∂μ, ‖ρ i z‖ ≤ B)
    (hae : ∀ᵐ z ∂μ, Tendsto (fun i ↦ ρ i z) l (𝓝 1)) :
    let L_V (i : ι) := V.orthogonalProjectionOnto.comp ((M i).comp (V.subtypeL.comp D))
    let L_W (i : ι) := W.orthogonalProjectionOnto.comp ((M i).comp (W.subtypeL.comp D_W))
    ∃ (hLV : ∀ i, IsNuclearOperator (L_V i)) (hLW : ∀ i, IsNuclearOperator (L_W i)),
      Tendsto (fun i ↦ hilbertTrace ⟨L_V i, hLV i⟩ - hilbertTrace ⟨L_W i, hLW i⟩) l
        (𝓝 (∑ k : Fin m, ev k)) := by
  let A : Fin m → Fin m → ℂ := fun k j ↦ if j = k then ev k else 0
  have hinv (k : Fin m) (f : V) : ℓ k (D f) = ∑ j, A k j * ℓ j f := by
    simp [A, hev k f]
  have hdiag : (∑ k : Fin m, A k k) = ∑ k : Fin m, ev k := by
    simp [A]
  simpa only [hdiag] using
    sLocalTrace_invariantFunctionals_defect_tendsto V W hWV e he C hC hrep D ℓ hlin A hinv hW
      D_W hDW ρ hρ M hM hbound hae

end SubspacePolarDefect

section DensityTwistTransport

open scoped NNReal

/-- A continuous nonnegative density preserves finiteness of measure on compact sets. -/
private theorem isFiniteMeasureOnCompacts_withDensity_continuous
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    {w : X → ℝ} (hw : Continuous w) :
    IsFiniteMeasureOnCompacts (μ.withDensity (fun x ↦ ENNReal.ofReal (w x))) := by
  refine ⟨fun K hK ↦ ?_⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hw.continuousOn
  have hle : (μ.withDensity (fun x ↦ ENNReal.ofReal (w x))) K ≤
      ENNReal.ofReal (max M 0) * μ K := by
    rw [withDensity_apply _ hK.isClosed.measurableSet]
    calc
      ∫⁻ x in K, ENNReal.ofReal (w x) ∂μ
          ≤ ∫⁻ _ in K, ENNReal.ofReal (max M 0) ∂μ := by
            refine setLIntegral_mono' hK.isClosed.measurableSet fun x hx ↦ ?_
            exact ENNReal.ofReal_le_ofReal
              ((le_abs_self (w x)).trans ((hM x hx).trans (le_max_left M 0)))
      _ = ENNReal.ofReal (max M 0) * μ K := by
            rw [setLIntegral_const]
  exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top)

/-- A continuous density over a regular Borel measure on a locally compact second-countable T2
space is inner regular. -/
private theorem innerRegular_withDensity_continuous
    (μ : Measure X) [μ.Regular] {w : X → ℝ} (hw : Continuous w) :
    (μ.withDensity (fun x ↦ ENNReal.ofReal (w x))).InnerRegular := by
  let ν := μ.withDensity (fun x ↦ ENNReal.ofReal (w x))
  let L := compactCovering X
  have hL (n : ℕ) : IsCompact (L n) := isCompact_compactCovering X n
  have hLm (n : ℕ) : MeasurableSet (L n) := (hL n).isClosed.measurableSet
  have hRestr (n : ℕ) : (ν.restrict (L n)).InnerRegular := by
    obtain ⟨M, hM⟩ := (hL n).exists_bound_of_continuousOn hw.continuousOn
    let C : ℝ≥0 := ⟨max M 0, le_max_right M 0⟩
    have hBound (x : X) (hx : x ∈ L n) : ENNReal.ofReal (w x) ≤ (C : ℝ≥0∞) := by
      have h1 : w x ≤ (C : ℝ) := (le_abs_self (w x)).trans ((hM x hx).trans (le_max_left M 0))
      simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal h1
    let : Fact (μ (L n) < ∞) := ⟨(hL n).measure_lt_top⟩
    let : (μ.restrict (L n)).Regular :=
      Measure.Regular.restrict_of_measure_ne_top (hL n).measure_lt_top.ne
    let Cμ := C • μ.restrict (L n)
    let : Cμ.Regular := inferInstanceAs (C • μ.restrict (L n)).Regular
    have hDom : ν.restrict (L n) ≤ Cμ := by
      rw [show ν = μ.withDensity (fun x ↦ ENNReal.ofReal (w x)) from rfl,
        restrict_withDensity (hLm n), show Cμ = (C : ℝ≥0∞) • μ.restrict (L n) from rfl,
        ← withDensity_const]
      refine withDensity_mono ?_
      filter_upwards [ae_restrict_mem (hLm n)] with x hx
      exact hBound x hx
    let : IsFiniteMeasure (ν.restrict (L n)) := isFiniteMeasure_of_le Cμ hDom
    let := regular_of_le_finite_regular _ Cμ hDom
    infer_instance
  constructor
  intro s hs r hr
  have hEq : ν s = ⨆ n, ν (s ∩ L n) := by
    have hmono : Monotone (fun n ↦ s ∩ L n) :=
      monotone_const.inter fun _ _ h ↦ compactCovering_subset X h
    have hU : (⋃ n, s ∩ L n) = s := by
      rw [← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
    rw [← hmono.measure_iUnion, hU]
  rw [hEq] at hr
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hr
  let := hRestr n
  rw [← Measure.restrict_apply hs] at hn
  obtain ⟨A, hA, hAc, hAn⟩ := hs.exists_lt_isCompact hn
  exact ⟨A, hA, hAc, hAn.trans_le (Measure.restrict_apply_le _ _)⟩

/-- Convert integrability and Bochner integrals across a continuous strictly positive density
`ν = μ.withDensity (ENNReal.ofReal ∘ w)`. -/
private theorem integrable_and_integral_withDensity_ofReal
    (μ : Measure X) {w : X → ℝ} (hw : Continuous w) (hwpos : ∀ x, 0 < w x)
    {g : X → ℂ} (hg : Integrable g (μ.withDensity (fun x ↦ ENNReal.ofReal (w x)))) :
    Integrable (fun x ↦ (w x : ℂ) * g x) μ ∧
      (∫ x, g x ∂(μ.withDensity (fun x ↦ ENNReal.ofReal (w x)))) =
        ∫ x, (w x : ℂ) * g x ∂μ := by
  let wNN : X → ℝ≥0 := fun x ↦ ⟨w x, (hwpos x).le⟩
  have hwNN : Measurable wNN := hw.measurable.subtype_mk
  have hmeasEq : (fun x ↦ ENNReal.ofReal (w x)) = fun x ↦ (wNN x : ℝ≥0∞) :=
    funext fun x ↦ ENNReal.ofReal_eq_coe_nnreal (hwpos x).le
  have hsmul (x : X) : (wNN x : ℝ≥0) • g x = (w x : ℂ) * g x := by
    change (w x : ℝ) • g x = _
    exact Complex.real_smul
  rw [hmeasEq] at hg ⊢
  refine ⟨((integrable_withDensity_iff_integrable_smul hwNN).mp hg).congr
    (Eventually.of_forall hsmul), ?_⟩
  rw [integral_withDensity_eq_integral_smul hwNN]
  exact integral_congr_ae (Eventually.of_forall hsmul)

/-- Paper: Theorem 12.4.1.1, pp. 515–517. Given a regular reference measure `μ`, a continuous
strictly positive density `w : X → ℝ` (`ν = w · μ`), and a continuous nonvanishing half-twist
`α : X → ℂ`, the fixed-level cutoff compression on `L²(ν)` converts to a jointly continuous kernel
`k(x, y) = α(x) α(y)⁻¹ w(y) k_ν(x, y)` relative to `μ`. Its twisted `μ`-integral represents the
conjugated action `α · (T f)`, its diagonal is `μ`-integrable, and its `μ`-diagonal integral
equals the Hilbert trace on both `L²(ν)` and `V` as well as the weighted reproducing diagonal
`∫ ρ(z) ⟪e z, D (e z)⟫ w(z) dμ`.
Reconstruction: Formalizes the input-density and half-twist conversion back to quotient Haar
measure described in `#7354` (converting `L²(w dx)` kernels to quotient Haar kernels
`√(uv) w(v) k(u, v)` without changing the diagonal trace integral). -/
theorem sLocalTrace_densityTwist_kernel
    (μ : Measure X) [μ.Regular]
    (w : X → ℝ) (hw : Continuous w) (hwpos : ∀ x, 0 < w x)
    (α : X → ℂ) (hα : Continuous α) (hαne : ∀ x, α x ≠ 0)
    (V : Submodule ℂ (Lp ℂ 2 (μ.withDensity (fun x ↦ ENNReal.ofReal (w x))))) [CompleteSpace V]
    (e : X → V) (he : Continuous e) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, f⟫_ℂ) =ᵐ[μ.withDensity (fun x ↦ ENNReal.ofReal (w x))]
      ((f : Lp ℂ 2 (μ.withDensity (fun x ↦ ENNReal.ofReal (w x)))) : X → ℂ))
    (ρ : X → ℂ) (hρ : Integrable ρ (μ.withDensity (fun x ↦ ENNReal.ofReal (w x))))
    (M : Lp ℂ 2 (μ.withDensity (fun x ↦ ENNReal.ofReal (w x))) →L[ℂ]
      Lp ℂ 2 (μ.withDensity (fun x ↦ ENNReal.ofReal (w x))))
    (hM : ∀ f : Lp ℂ 2 (μ.withDensity (fun x ↦ ENNReal.ofReal (w x))),
      ∀ᵐ x ∂(μ.withDensity (fun x ↦ ENNReal.ofReal (w x))), M f x = ρ x * f x)
    (D : V →L[ℂ] V) :
    let ν := μ.withDensity (fun x ↦ ENNReal.ofReal (w x))
    let j := V.subtypeL
    let q := V.orthogonalProjectionOnto
    let L := q.comp (M.comp (j.comp D))
    let T := j.comp (L.comp q)
    let k (p : X × X) := α p.1 * (α p.2)⁻¹ * (w p.2 : ℂ) *
      ∫ z, ρ z * (⟪e p.1, e z⟫_ℂ * ⟪e z, D (e p.2)⟫_ℂ) ∂ν
    ∃ (hT : IsNuclearOperator T) (hL : IsNuclearOperator L),
      Continuous k ∧
      (∀ f : Lp ℂ 2 ν, ∀ᵐ x ∂μ,
        Integrable (fun y ↦ k (x, y) * (α y * f y)) μ ∧
        α x * T f x = ∫ y, k (x, y) * (α y * f y) ∂μ) ∧
      Integrable (fun x ↦ k (x, x)) μ ∧
      Integrable (fun z ↦ ρ z * ⟪e z, D (e z)⟫_ℂ * (w z : ℂ)) μ ∧
      hilbertTrace ⟨T, hT⟩ = (∫ x, k (x, x) ∂μ) ∧
      hilbertTrace ⟨L, hL⟩ = (∫ x, k (x, x) ∂μ) ∧
      hilbertTrace ⟨L, hL⟩ = (∫ z, ρ z * ⟪e z, D (e z)⟫_ℂ * (w z : ℂ) ∂μ) := by
  intro ν j q L T k
  let : IsFiniteMeasureOnCompacts ν := isFiniteMeasureOnCompacts_withDensity_continuous μ hw
  let : ν.InnerRegular := innerRegular_withDensity_continuous μ hw
  let kν (p : X × X) := ∫ z, ρ z * (⟪e p.1, e z⟫_ℂ * ⟪e z, D (e p.2)⟫_ℂ) ∂ν
  obtain ⟨hT, hL, hcontν, hkerν, hdiagν, hrepDiagν, hTtr, hLtr, hLrep, _, _⟩ :=
    sLocalTrace_measurableCutoffKernel (μ := ν) V e he C hC hrep ρ hρ M hM D
  have hwMeas : Measurable (fun x ↦ ENNReal.ofReal (w x)) := hw.measurable.ennreal_ofReal
  have hae_iff {P : X → Prop} (h : ∀ᵐ x ∂ν, P x) : ∀ᵐ x ∂μ, P x := by
    rw [ae_withDensity_iff hwMeas] at h
    filter_upwards [h] with x hx
    exact hx (ENNReal.ofReal_pos.mpr (hwpos x)).ne'
  have hcont : Continuous k :=
    (((hα.comp continuous_fst).mul ((hα.comp continuous_snd).inv₀ fun p ↦ hαne p.2)).mul
      (Complex.continuous_ofReal.comp (hw.comp continuous_snd))).mul hcontν
  have hk_diag (x : X) : k (x, x) = (w x : ℂ) * kν (x, x) := by
    dsimp only [k, kν]
    rw [mul_inv_cancel₀ (hαne x), one_mul]
  obtain ⟨hdiagW, hdiagEqW⟩ := integrable_and_integral_withDensity_ofReal μ hw hwpos hdiagν
  have hdiag : Integrable (fun x ↦ k (x, x)) μ :=
    hdiagW.congr (Eventually.of_forall fun x ↦ (hk_diag x).symm)
  have hdiagEq : (∫ x, kν (x, x) ∂ν) = ∫ x, k (x, x) ∂μ :=
    hdiagEqW.trans (integral_congr_ae (Eventually.of_forall fun x ↦ (hk_diag x).symm))
  obtain ⟨hrepW, hrepEqW⟩ := integrable_and_integral_withDensity_ofReal μ hw hwpos hrepDiagν
  have hrepInt : Integrable (fun z ↦ ρ z * ⟪e z, D (e z)⟫_ℂ * (w z : ℂ)) μ :=
    hrepW.congr (Eventually.of_forall fun z ↦ mul_comm _ _)
  have hrepEq : (∫ z, ρ z * ⟪e z, D (e z)⟫_ℂ ∂ν) =
      ∫ z, ρ z * ⟪e z, D (e z)⟫_ℂ * (w z : ℂ) ∂μ :=
    hrepEqW.trans (integral_congr_ae (Eventually.of_forall fun z ↦ mul_comm _ _))
  refine ⟨hT, hL, hcont, ?_, hdiag, hrepInt, hTtr.trans hdiagEq, hLtr.trans hdiagEq,
    hLrep.trans hrepEq⟩
  intro f
  filter_upwards [hae_iff (hkerν f)] with x ⟨hintν, hactν⟩
  have hpt (y : X) :
      k (x, y) * (α y * f y) = α x * ((w y : ℂ) * (kν (x, y) * f y)) := by
    dsimp only [k, kν]
    have hcancel : (α y)⁻¹ * α y = 1 := inv_mul_cancel₀ (hαne y)
    calc
      α x * (α y)⁻¹ * (w y : ℂ) * (∫ z, ρ z * (⟪e x, e z⟫_ℂ * ⟪e z, D (e y)⟫_ℂ) ∂ν) * (α y * f y)
          = α x * ((α y)⁻¹ * α y) * ((w y : ℂ) *
              ((∫ z, ρ z * (⟪e x, e z⟫_ℂ * ⟪e z, D (e y)⟫_ℂ) ∂ν) * f y)) := by ring
      _ = α x * ((w y : ℂ) * ((∫ z, ρ z * (⟪e x, e z⟫_ℂ * ⟪e z, D (e y)⟫_ℂ) ∂ν) * f y)) := by
            rw [hcancel, mul_one]
  obtain ⟨hintμ, hintEqμ⟩ := integrable_and_integral_withDensity_ofReal μ hw hwpos hintν
  refine ⟨(hintμ.const_mul (α x)).congr (Eventually.of_forall fun y ↦ (hpt y).symm), ?_⟩
  rw [hactν, hintEqμ, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun y ↦ (hpt y).symm)

end DensityTwistTransport

section SharpComparisonAndPolarDefect

set_option quotPrecheck false

open IsDedekindDomain NumberField Set
open scoped NNReal

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b

local instance instSIdeleT2Sec4Iso : T2Space (SAdeleRing F S)ˣ :=
  (sIdeleGroup_description F S).2.1

local notation "Vₚ" => HeightOneSpectrum (𝓞 F)
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Hₛ" => sProjectedDiagonal F S
local notation "classAtS(" g ")" => (QuotientGroup.mk (sIdeleInsertion F S g) : C𝔽)
local notation "normS(" x ")" => (((sIdeleNorm F S x).val : ℝ))
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "volume₁" => ((sLocalNormOneQuotientMeasure F S) Set.univ).toReal
local notation "globalVolume₁" => ((normOneIdeleClassTamagawaMeasure F) Set.univ).toReal
local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : S) → BruhatCompactSupport (v.val.adicCompletion F)ˣ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finiteVolume(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal
local notation "principalValues(" a "," b ")" =>
  ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
    ∑ v : S, ((Real.log (v.val.asIdeal.absNorm : ℝ) / finiteVolume(v.val) : ℝ) : ℂ) *
      finiteConnesWeilPrincipalValue v.val 1 (b v))

/-- The S-local norm-one quotient volume is nonzero. -/
private theorem sLocalNormOneVolume_ne_zero : (volume₁ : ℂ) ≠ 0 := by
  let G := (sIdeleQuotientNorm F S).ker
  let : BorelSpace Jₛ := ⟨rfl⟩
  let : T2Space Jₛ := instSIdeleQuotientT2Sec1
  let : LocallyCompactSpace Jₛ := instSIdeleQuotientLocallyCompactSec1
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let η := sLocalNormOneQuotientMeasure F S
  have : η.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  refine Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨?_, ?_⟩)
  · exact isOpen_univ.measure_ne_zero η univ_nonempty
  · exact measure_ne_top η Set.univ

/-- The global norm-one idele class volume is nonzero. -/
private theorem globalNormOneVolume_ne_zero : (globalVolume₁ : ℂ) ≠ 0 := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  have hν := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure := hν.1
  let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  let : IsFiniteMeasure (normOneIdeleClassTamagawaMeasure F) := CompactSpace.isFiniteMeasure
  refine Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨?_, ?_⟩)
  · exact isOpen_univ.measure_ne_zero _ univ_nonempty
  · exact measure_ne_top _ Set.univ

/-- Paper: Theorem 12.4.1.1, pp. 514–519. On `SIdeleQuotient F S` equipped with any continuous
strictly positive weight `w` (`ν = w · μJ`), a joint family of evaluable levels `(V p, e p, C p)`,
`ν`-integrable spatial cutoffs `ρ p` (with bounded multiplications `M p`), and bounded level
operators `D p` produces nuclear compressions `L p` with jointly continuous quotient kernels.
Whenever the single weighted reproducing-kernel diagonal integral agrees asymptotically with the
summed sharp orbital mass `M_sharp (p.1 * p.2)`, the normalized Hilbert traces of `L p` converge
jointly to the sum of local Connes–Weil principal values.
Reconstruction: Discharges the abstract kernel and diagonal-integrability hypotheses of
`sLocalTrace_asymptotic_of_sharp_comparison` by constructing the actual nuclear compressions and
their density-converted continuous quotient kernels via `sLocalTrace_densityTwist_kernel`. -/
theorem sLocalTrace_weightedCutoff_asymptotic_of_sharp_comparison
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set Vₚ).integer F)))
    (hRamified : ∀ v : Vₚ, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (w : Jₛ → ℝ) (hw : Continuous w) (hwpos : ∀ x, 0 < w x)
    (V : ℝ × ℝ → Submodule ℂ (Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x)))))
    [∀ p, CompleteSpace (V p)]
    (e : ∀ p, Jₛ → V p) (he : ∀ p, Continuous (e p))
    (C : ℝ × ℝ → ℝ) (hC : ∀ p x, ‖e p x‖ ≤ C p)
    (hrep : ∀ p (u : V p),
      (fun x ↦ ⟪e p x, u⟫_ℂ) =ᵐ[(μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))]
        ((u : Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x)))) : Jₛ → ℂ))
    (ρ : ℝ × ℝ → Jₛ → ℂ)
    (hρ : ∀ p, Integrable (ρ p) ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))))
    (M : ℝ × ℝ → Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))) →L[ℂ]
      Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))))
    (hM : ∀ p (u : Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x)))),
      ∀ᵐ x ∂((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))), M p u x = ρ p x * u x)
    (D : ∀ p, V p →L[ℂ] V p)
    (Msharp : ℝ → ℂ)
    (hSum : ∀ᶠ R in atTop, HasSum (fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ R) (Msharp R))
    (hComparison : Tendsto
      (fun p : ℝ × ℝ ↦
        (∫ z, ρ p z * ⟪e p z, D p (e p z)⟫_ℂ * (w z : ℂ) ∂μJ) - Msharp (p.1 * p.2))
      (atTop ×ˢ atTop) (𝓝 0)) :
    let L (p : ℝ × ℝ) := (V p).orthogonalProjectionOnto.comp ((M p).comp ((V p).subtypeL.comp (D p)))
    ∃ (hL : ∀ p, IsNuclearOperator (L p)) (a : archTest) (b : finiteTest),
      (∀ (w' : InfinitePlace F) (u : w'.Completionˣ),
        (a w').val u = φ.val (archClass(w') u)) ∧
      (∀ (v : S) (u : (v.val.adicCompletion F)ˣ),
        (b v).val u = φ.val (finiteClass(v.val) u)) ∧
      Tendsto (fun p : ℝ × ℝ ↦ hilbertTrace ⟨L p, hL p⟩ / (volume₁ : ℂ) -
        φ.val 1 * (Real.log (p.1 * p.2) : ℂ)) (atTop ×ˢ atTop) (𝓝 principalValues(a, b)) := by
  intro L
  let : BorelSpace Jₛ := ⟨rfl⟩
  let : T2Space Jₛ := instSIdeleQuotientT2Sec1
  let : LocallyCompactSpace Jₛ := instSIdeleQuotientLocallyCompactSec1
  let : SecondCountableTopology Jₛ := instSIdeleQuotientSecondCountableSec1
  let : (μJ).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1
  let : (μJ).Regular := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).2.1
  let ν := (μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))
  let k (p : ℝ × ℝ) (x y : Jₛ) : ℂ :=
    (1 : ℂ) * (1 : ℂ)⁻¹ * (w y : ℂ) *
      ∫ z, ρ p z * (⟪e p x, e p z⟫_ℂ * ⟪e p z, D p (e p y)⟫_ℂ) ∂ν
  have hlevel (p : ℝ × ℝ) :
      ∃ hLp : IsNuclearOperator (L p),
        Integrable (fun x ↦ k p x x) μJ ∧
        hilbertTrace ⟨L p, hLp⟩ = (∫ x, k p x x ∂μJ) ∧
        hilbertTrace ⟨L p, hLp⟩ = ∫ z, ρ p z * ⟪e p z, D p (e p z)⟫_ℂ * (w z : ℂ) ∂μJ := by
    obtain ⟨_, hLp, _, _, hdiag, _, _, htr1, htr2⟩ :=
      sLocalTrace_densityTwist_kernel μJ w hw hwpos (fun _ ↦ (1 : ℂ)) continuous_const
        (fun _ ↦ one_ne_zero) (V p) (e p) (he p) (C p) (hC p) (hrep p) (ρ p) (hρ p) (M p)
        (hM p) (D p)
    exact ⟨hLp, hdiag, htr1, htr2⟩
  choose hL hdiag htrK htrRep using hlevel
  have hCompK : Tendsto
      (fun p : ℝ × ℝ ↦ (∫ x, k p x x ∂μJ) - Msharp (p.1 * p.2))
      (atTop ×ˢ atTop) (𝓝 0) := by
    refine hComparison.congr fun p ↦ ?_
    rw [(htrK p).symm.trans (htrRep p)]
  obtain ⟨a, b, ha, hb, hlim⟩ :=
    sLocalTrace_asymptotic_of_sharp_comparison (F := F) (S := S) φ hPic hRamified hOutside f
      hLift k Msharp hSum (Eventually.of_forall hdiag) hCompK
  refine ⟨hL, a, b, ha, hb, ?_⟩
  refine hlim.congr fun p ↦ ?_
  rw [htrK p]

/-- Algebraic combination of the uncompressed asymptotic and the normalized trace defect. -/
private theorem tendsto_normalized_sub_of_defect {ι : Type*} {l : Filter ι}
    (xV xW logTerm : ι → ℂ) (v₁ P Δ : ℂ)
    (hV : Tendsto (fun i ↦ xV i / v₁ - logTerm i) l (𝓝 P))
    (hD : Tendsto (fun i ↦ (xV i - xW i) / v₁) l (𝓝 Δ)) :
    Tendsto (fun i ↦ xW i / v₁ - logTerm i) l (𝓝 (P - Δ)) := by
  refine (hV.sub hD).congr fun i ↦ ?_
  ring

/-- Normalized ratio identifying the sum of the two local polar moments with the sum of both
global polar Fourier–Mellin terms. -/
private theorem sLocalTrace_doublePolarRatio
    (hPic : Subsingleton (CommRing.Pic ((S : Set Vₚ).integer F)))
    (φ : BruhatCompactSupport C𝔽)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g)))) :
    let pole (s : ℂ) := modulatedFourierMellin (continuousIdeleClassNorm F) Set.univ
      ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
      (ideleClassTamagawaMeasure F) φ.val (ideleClassNormTwist 1 s)
    ((∫ g : Iₛ, f.val g * (Real.sqrt (normS(g)) : ℂ) ∂μₛ) +
      ∫ g : Iₛ, f.val g / (Real.sqrt (normS(g)) : ℂ) ∂μₛ) / (volume₁ : ℂ) =
      (pole (1 / 2) + pole (-1 / 2)) / (globalVolume₁ : ℂ) := by
  intro pole
  have hpolar := sLocalTraceLift_global_polar_sum (F := F) (S := S) hPic φ hOutside f hLift
  have hv₁ : (volume₁ : ℂ) ≠ 0 := sLocalNormOneVolume_ne_zero (F := F) (S := S)
  have hvG : (globalVolume₁ : ℂ) ≠ 0 := globalNormOneVolume_ne_zero (F := F)
  rw [div_eq_div_iff hv₁ hvG, mul_comm _ (globalVolume₁ : ℂ), mul_comm _ (volume₁ : ℂ)]
  exact hpolar

/-- Normalized ratio identifying the negative-half local polar moment with the global polar
Fourier–Mellin term at `-1/2`. -/
private theorem sLocalTrace_singlePolarRatio
    (hPic : Subsingleton (CommRing.Pic ((S : Set Vₚ).integer F)))
    (φ : BruhatCompactSupport C𝔽)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g)))) :
    let pole (s : ℂ) := modulatedFourierMellin (continuousIdeleClassNorm F) Set.univ
      ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
      (ideleClassTamagawaMeasure F) φ.val (ideleClassNormTwist 1 s)
    (∫ g : Iₛ, f.val g / (Real.sqrt (normS(g)) : ℂ) ∂μₛ) / (volume₁ : ℂ) =
      pole (-1 / 2) / (globalVolume₁ : ℂ) := by
  intro pole
  let root (t : ℝ≥0ˣ) : ℂ := (Real.sqrt (t.val : ℝ) : ℂ)
  have hrc : Continuous root :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp Units.continuous_val).sqrt
  have hrne (t : ℝ≥0ˣ) : root t ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (NNReal.coe_pos.mpr (Units.zero_lt t))).ne'
  have hneg := sLocalTraceLift_global_norm_integral (F := F) (S := S) hPic φ hOutside f hLift
    (fun t ↦ (root t)⁻¹) (hrc.inv₀ hrne)
  have hm (c : C𝔽) : ideleClassNormTwist 1 (-1 / 2) c = (root (ideleClassNorm F c))⁻¹ := by
    change (1 : ℂ) * (((ideleClassNorm F c).val : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = _
    rw [one_mul, neg_div, Complex.cpow_neg]
    dsimp only [root]
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (NNReal.coe_nonneg _)]
    norm_num
  have hpolar :
      (globalVolume₁ : ℂ) * (∫ g : Iₛ, f.val g / (Real.sqrt (normS(g)) : ℂ) ∂μₛ) =
        (volume₁ : ℂ) * pole (-1 / 2) := by
    have hL : (∫ g : Iₛ, f.val g / (Real.sqrt (normS(g)) : ℂ) ∂μₛ) =
        ∫ g : Iₛ, f.val g * (root (sIdeleNorm F S g))⁻¹ ∂μₛ :=
      integral_congr_ae (Eventually.of_forall fun g ↦ div_eq_mul_inv _ _)
    have hR : pole (-1 / 2) =
        ∫ c : C𝔽, φ.val c * (root (ideleClassNorm F c))⁻¹ ∂(ideleClassTamagawaMeasure F) := by
      simp only [pole, modulatedFourierMellin, relativeVerticalStrip, preimage_univ,
        indicator_univ, hm]
    rw [hL, hR]
    exact hneg
  have hv₁ : (volume₁ : ℂ) ≠ 0 := sLocalNormOneVolume_ne_zero (F := F) (S := S)
  have hvG : (globalVolume₁ : ℂ) ≠ 0 := globalNormOneVolume_ne_zero (F := F)
  rw [div_eq_div_iff hv₁ hvG, mul_comm _ (globalVolume₁ : ℂ), mul_comm _ (volume₁ : ℂ)]
  exact hpolar

/-- Paper: Theorem 12.4.1.1, pp. 514–519, and Theorem 12.5.1.1, pp. 519–520. On `SIdeleQuotient F S`
with any continuous strictly positive weight `w` (`ν = w · μJ`), let `V` be an evaluable Hilbert
level and `D : V →L[ℂ] V` a bounded operator admitting two linearly independent bounded polar
eigenfunctionals `ℓ₊, ℓ₋ : V →L[ℂ] ℂ` whose eigenvalues are the two local half-Mellin moments of
the compact S-idelic lift `f` (`∫ f · √|·|` and `∫ f / √|·|`, matching
`integral_sLocalTraceDilationKernel` and `sLocalTraceDilationKernel_apply_zero`). Along any
uniformly bounded family of `ν`-integrable cutoffs `ρ p → 1` a.e. for which the uncompressed level
`V` asymptotically matches the sharp orbital mass `M_sharp (p.1 * p.2)`, the normalized Hilbert
traces on the polar-constrained sublevel `W = ker ℓ₊ ∩ ker ℓ₋` converge jointly to the sum of
local principal values minus the normalized sum of both global polar Fourier–Mellin terms
`(pole(1/2) + pole(-1/2)) / vol(C_F^1)`.
Reconstruction: Unifies `sLocalTrace_weightedCutoff_asymptotic_of_sharp_comparison`,
`sLocalTrace_eigenfunctionals_defect_tendsto`, and `sLocalTraceLift_global_polar_sum` for every
number field `F` and finite set of places `S`. -/
theorem sLocalTrace_polarSublevel_asymptotic_defect
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set Vₚ).integer F)))
    (hRamified : ∀ v : Vₚ, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (w : Jₛ → ℝ) (hw : Continuous w) (hwpos : ∀ x, 0 < w x)
    (V W : Submodule ℂ (Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x)))))
    [CompleteSpace V] [CompleteSpace W] (hWV : W ≤ V)
    (e : Jₛ → V) (he : Continuous e) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C)
    (hrep : ∀ u : V, (fun x ↦ ⟪e x, u⟫_ℂ) =ᵐ[(μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))]
      ((u : Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x)))) : Jₛ → ℂ))
    (D : V →L[ℂ] V) (D_W : W →L[ℂ] W)
    (hDW : ∀ u : W, (D ⟨u.1, hWV u.2⟩ : Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x)))) =
      (D_W u : Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x)))))
    (ℓPos ℓNeg : V →L[ℂ] ℂ) (hlin : LinearIndependent ℂ ![ℓPos, ℓNeg])
    (hℓPos : ∀ u : V, ℓPos (D u) = (∫ g : Iₛ, f.val g * (Real.sqrt (normS(g)) : ℂ) ∂μₛ) * ℓPos u)
    (hℓNeg : ∀ u : V, ℓNeg (D u) = (∫ g : Iₛ, f.val g / (Real.sqrt (normS(g)) : ℂ) ∂μₛ) * ℓNeg u)
    (hW : ∀ u : V, (u : Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x)))) ∈ W ↔
      ℓPos u = 0 ∧ ℓNeg u = 0)
    (ρ : ℝ × ℝ → Jₛ → ℂ)
    (hρ : ∀ p, Integrable (ρ p) ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))))
    (M : ℝ × ℝ → Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))) →L[ℂ]
      Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))))
    (hM : ∀ p (u : Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x)))),
      ∀ᵐ x ∂((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))), M p u x = ρ p x * u x)
    (hbound : ∃ B : ℝ, ∀ᶠ p in atTop ×ˢ atTop,
      ∀ᵐ z ∂((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))), ‖ρ p z‖ ≤ B)
    (hae : ∀ᵐ z ∂((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))),
      Tendsto (fun p ↦ ρ p z) (atTop ×ˢ atTop) (𝓝 1))
    (Msharp : ℝ → ℂ)
    (hSum : ∀ᶠ R in atTop, HasSum (fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ R) (Msharp R))
    (hComparison : Tendsto
      (fun p : ℝ × ℝ ↦
        (∫ z, ρ p z * ⟪e z, D (e z)⟫_ℂ * (w z : ℂ) ∂μJ) - Msharp (p.1 * p.2))
      (atTop ×ˢ atTop) (𝓝 0)) :
    let pole (s : ℂ) := modulatedFourierMellin (continuousIdeleClassNorm F) Set.univ
      ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
      (ideleClassTamagawaMeasure F) φ.val (ideleClassNormTwist 1 s)
    let L_W (p : ℝ × ℝ) := W.orthogonalProjectionOnto.comp ((M p).comp (W.subtypeL.comp D_W))
    ∃ (hLW : ∀ p, IsNuclearOperator (L_W p)) (a : archTest) (b : finiteTest),
      (∀ (w' : InfinitePlace F) (u : w'.Completionˣ),
        (a w').val u = φ.val (archClass(w') u)) ∧
      (∀ (v : S) (u : (v.val.adicCompletion F)ˣ),
        (b v).val u = φ.val (finiteClass(v.val) u)) ∧
      Tendsto (fun p : ℝ × ℝ ↦ hilbertTrace ⟨L_W p, hLW p⟩ / (volume₁ : ℂ) -
        φ.val 1 * (Real.log (p.1 * p.2) : ℂ)) (atTop ×ˢ atTop)
        (𝓝 (principalValues(a, b) - (pole (1 / 2) + pole (-1 / 2)) / (globalVolume₁ : ℂ))) := by
  intro pole L_W
  let : BorelSpace Jₛ := ⟨rfl⟩
  let : T2Space Jₛ := instSIdeleQuotientT2Sec1
  let : LocallyCompactSpace Jₛ := instSIdeleQuotientLocallyCompactSec1
  let : SecondCountableTopology Jₛ := instSIdeleQuotientSecondCountableSec1
  let : (μJ).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1
  let : (μJ).Regular := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).2.1
  let ν := (μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))
  let : IsFiniteMeasureOnCompacts ν := isFiniteMeasureOnCompacts_withDensity_continuous μJ hw
  let : ν.InnerRegular := innerRegular_withDensity_continuous μJ hw
  obtain ⟨hLV, a, b, ha, hb, hlimV⟩ :=
    sLocalTrace_weightedCutoff_asymptotic_of_sharp_comparison φ hPic hRamified hOutside f hLift
      w hw hwpos (fun _ ↦ V) (fun _ ↦ e) (fun _ ↦ he) (fun _ ↦ C) (fun _ ↦ hC) (fun _ ↦ hrep)
      ρ hρ M hM (fun _ ↦ D) Msharp hSum hComparison
  let ev : Fin 2 → ℂ :=
    ![∫ g : Iₛ, f.val g * (Real.sqrt (normS(g)) : ℂ) ∂μₛ,
      ∫ g : Iₛ, f.val g / (Real.sqrt (normS(g)) : ℂ) ∂μₛ]
  have hev (k : Fin 2) (u : V) : (![ℓPos, ℓNeg] k) (D u) = ev k * (![ℓPos, ℓNeg] k) u := by
    fin_cases k
    · exact hℓPos u
    · exact hℓNeg u
  have hW' (u : V) : (u : Lp ℂ 2 ν) ∈ W ↔ ∀ k : Fin 2, (![ℓPos, ℓNeg] k) u = 0 := by
    rw [hW u, Fin.forall_fin_two]
    rfl
  obtain ⟨hLV', hLW, hdefect⟩ :=
    sLocalTrace_eigenfunctionals_defect_tendsto (μ := ν) (l := atTop ×ˢ atTop)
      V W hWV e he C hC hrep D ![ℓPos, ℓNeg] hlin ev hev hW' D_W hDW ρ hρ M hM hbound hae
  have hsumEv : (∑ k : Fin 2, ev k) =
      (∫ g : Iₛ, f.val g * (Real.sqrt (normS(g)) : ℂ) ∂μₛ) +
        ∫ g : Iₛ, f.val g / (Real.sqrt (normS(g)) : ℂ) ∂μₛ := by
    simp [Fin.sum_univ_two, ev]
  rw [hsumEv] at hdefect
  have hdefDiv := hdefect.div_const (volume₁ : ℂ)
  rw [sLocalTrace_doublePolarRatio (F := F) (S := S) hPic φ hOutside f hLift] at hdefDiv
  refine ⟨hLW, a, b, ha, hb, ?_⟩
  exact tendsto_normalized_sub_of_defect _ _ _ _ _ _ hlimV hdefDiv

/-- Paper: Theorem 12.4.1.1, pp. 514–519, and p. 520 (single surviving polar condition). When only
one nonzero bounded polar eigenfunctional `ℓ₋ : V →L[ℂ] ℂ` survives closure on the weighted level
`V` (with eigenvalue `∫ f / √|·|`, modeling the unweighted and narrow-width `0 ≤ α < 1/2` regimes
discussed on `#7354`), restricting to `W = ker ℓ₋` shifts the normalized trace limit by exactly
`- pole(-1/2) / vol(C_F^1)` rather than both polar terms. -/
theorem sLocalTrace_singlePolarSublevel_asymptotic_defect
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set Vₚ).integer F)))
    (hRamified : ∀ v : Vₚ, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (w : Jₛ → ℝ) (hw : Continuous w) (hwpos : ∀ x, 0 < w x)
    (V W : Submodule ℂ (Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x)))))
    [CompleteSpace V] [CompleteSpace W] (hWV : W ≤ V)
    (e : Jₛ → V) (he : Continuous e) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C)
    (hrep : ∀ u : V, (fun x ↦ ⟪e x, u⟫_ℂ) =ᵐ[(μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))]
      ((u : Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x)))) : Jₛ → ℂ))
    (D : V →L[ℂ] V) (D_W : W →L[ℂ] W)
    (hDW : ∀ u : W, (D ⟨u.1, hWV u.2⟩ : Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x)))) =
      (D_W u : Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x)))))
    (ℓNeg : V →L[ℂ] ℂ) (hℓne : ℓNeg ≠ 0)
    (hℓNeg : ∀ u : V, ℓNeg (D u) = (∫ g : Iₛ, f.val g / (Real.sqrt (normS(g)) : ℂ) ∂μₛ) * ℓNeg u)
    (hW : ∀ u : V, (u : Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x)))) ∈ W ↔ ℓNeg u = 0)
    (ρ : ℝ × ℝ → Jₛ → ℂ)
    (hρ : ∀ p, Integrable (ρ p) ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))))
    (M : ℝ × ℝ → Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))) →L[ℂ]
      Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))))
    (hM : ∀ p (u : Lp ℂ 2 ((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x)))),
      ∀ᵐ x ∂((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))), M p u x = ρ p x * u x)
    (hbound : ∃ B : ℝ, ∀ᶠ p in atTop ×ˢ atTop,
      ∀ᵐ z ∂((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))), ‖ρ p z‖ ≤ B)
    (hae : ∀ᵐ z ∂((μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))),
      Tendsto (fun p ↦ ρ p z) (atTop ×ˢ atTop) (𝓝 1))
    (Msharp : ℝ → ℂ)
    (hSum : ∀ᶠ R in atTop, HasSum (fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ R) (Msharp R))
    (hComparison : Tendsto
      (fun p : ℝ × ℝ ↦
        (∫ z, ρ p z * ⟪e z, D (e z)⟫_ℂ * (w z : ℂ) ∂μJ) - Msharp (p.1 * p.2))
      (atTop ×ˢ atTop) (𝓝 0)) :
    let pole (s : ℂ) := modulatedFourierMellin (continuousIdeleClassNorm F) Set.univ
      ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
      (ideleClassTamagawaMeasure F) φ.val (ideleClassNormTwist 1 s)
    let L_W (p : ℝ × ℝ) := W.orthogonalProjectionOnto.comp ((M p).comp (W.subtypeL.comp D_W))
    ∃ (hLW : ∀ p, IsNuclearOperator (L_W p)) (a : archTest) (b : finiteTest),
      (∀ (w' : InfinitePlace F) (u : w'.Completionˣ),
        (a w').val u = φ.val (archClass(w') u)) ∧
      (∀ (v : S) (u : (v.val.adicCompletion F)ˣ),
        (b v).val u = φ.val (finiteClass(v.val) u)) ∧
      Tendsto (fun p : ℝ × ℝ ↦ hilbertTrace ⟨L_W p, hLW p⟩ / (volume₁ : ℂ) -
        φ.val 1 * (Real.log (p.1 * p.2) : ℂ)) (atTop ×ˢ atTop)
        (𝓝 (principalValues(a, b) - pole (-1 / 2) / (globalVolume₁ : ℂ))) := by
  intro pole L_W
  let : BorelSpace Jₛ := ⟨rfl⟩
  let : T2Space Jₛ := instSIdeleQuotientT2Sec1
  let : LocallyCompactSpace Jₛ := instSIdeleQuotientLocallyCompactSec1
  let : SecondCountableTopology Jₛ := instSIdeleQuotientSecondCountableSec1
  let : (μJ).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1
  let : (μJ).Regular := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).2.1
  let ν := (μJ).withDensity (fun x ↦ ENNReal.ofReal (w x))
  let : IsFiniteMeasureOnCompacts ν := isFiniteMeasureOnCompacts_withDensity_continuous μJ hw
  let : ν.InnerRegular := innerRegular_withDensity_continuous μJ hw
  obtain ⟨hLV, a, b, ha, hb, hlimV⟩ :=
    sLocalTrace_weightedCutoff_asymptotic_of_sharp_comparison φ hPic hRamified hOutside f hLift
      w hw hwpos (fun _ ↦ V) (fun _ ↦ e) (fun _ ↦ he) (fun _ ↦ C) (fun _ ↦ hC) (fun _ ↦ hrep)
      ρ hρ M hM (fun _ ↦ D) Msharp hSum hComparison
  have hlin : LinearIndependent ℂ (fun _ : Fin 1 ↦ ℓNeg) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have hk : k = 0 := Subsingleton.elim k 0
    subst hk
    have h0 : g 0 • ℓNeg = 0 := by simpa only [Fin.sum_univ_one] using hg
    exact (smul_eq_zero.mp h0).resolve_right hℓne
  let ev : Fin 1 → ℂ := fun _ ↦ ∫ g : Iₛ, f.val g / (Real.sqrt (normS(g)) : ℂ) ∂μₛ
  have hW' (u : V) : (u : Lp ℂ 2 ν) ∈ W ↔ ∀ _ : Fin 1, ℓNeg u = 0 := by
    rw [hW u]
    simp
  obtain ⟨hLV', hLW, hdefect⟩ :=
    sLocalTrace_eigenfunctionals_defect_tendsto (μ := ν) (l := atTop ×ˢ atTop)
      V W hWV e he C hC hrep D (fun _ : Fin 1 ↦ ℓNeg) hlin ev (fun _ u ↦ hℓNeg u) hW' D_W hDW
      ρ hρ M hM hbound hae
  have hsumEv : (∑ k : Fin 1, ev k) = ∫ g : Iₛ, f.val g / (Real.sqrt (normS(g)) : ℂ) ∂μₛ := by
    simp [ev]
  rw [hsumEv] at hdefect
  have hdefDiv := hdefect.div_const (volume₁ : ℂ)
  rw [sLocalTrace_singlePolarRatio (F := F) (S := S) hPic φ hOutside f hLift] at hdefDiv
  refine ⟨hLW, a, b, ha, hb, ?_⟩
  exact tendsto_normalized_sub_of_defect _ _ _ _ _ _ hlimV hdefDiv

end SharpComparisonAndPolarDefect

end RiemannMasullo.Isolated
