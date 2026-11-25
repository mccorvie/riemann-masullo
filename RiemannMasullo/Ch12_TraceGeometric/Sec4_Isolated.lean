module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
public import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertSchmidtProduct
import Mathlib.MeasureTheory.Integral.Prod
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space

/-! # Fixed-level quotient kernels for §12.4

This file formalizes the fixed-level kernel construction described by dyknapp
in #7354. It replaces the factor through the flat Schwartz space with two
Hilbert–Schmidt factors. The hypotheses are continuous, uniformly bounded
evaluation on the closed level and square integrability of the masked vector
families. On the rational real-place level, the evaluation bound follows
from additive Fourier inversion on the fixed band. That specialization and
the comparison with the sharp orbital masses are outside these declarations. -/

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

end RiemannMasullo.Isolated
