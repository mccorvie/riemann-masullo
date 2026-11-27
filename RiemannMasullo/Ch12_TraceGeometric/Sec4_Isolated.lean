module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
public import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertSchmidtProduct
import Mathlib.MeasureTheory.Integral.Prod
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space

/-! # Fixed-level quotient kernels for §12.4

A continuous family of evaluation vectors on a closed Hilbert level gives a continuous
kernel for its spatial cutoff compression whenever the masked vectors lie in L². Two
Hilbert–Schmidt factors give the trace as an absolutely convergent diagonal integral.
In the positive real Haar chart, square-root evaluation growth suffices for a bounded
measurable upper cutoff. The absolute trace contributed by (0, r] is bounded linearly in r. -/

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
    {e u : X → H} (he : Continuous e) (hu : StronglyMeasurable u) (hu₂ : MemLp u 2 μ)
    (hrep : ∀ z, (fun x ↦ ⟪e x, u z⟫_ℂ) =ᵐ[μ] (u z : X → ℂ)) :
    MemLp (fun p : X × X ↦ ⟪e p.1, u p.2⟫_ℂ) 2 (μ.prod μ) := by
  have hm : StronglyMeasurable (fun p : X × X ↦ ⟪e p.1, u p.2⟫_ℂ) :=
    (he.stronglyMeasurable.comp_measurable measurable_fst).inner (hu.comp_measurable measurable_snd)
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
    (f : E) {u : X → E} {v : X → G} (hu : StronglyMeasurable u) (hv : StronglyMeasurable v)
    (hnorm : Integrable (fun z ↦ ‖u z‖ * ‖v z‖) μ) :
    Integrable (fun z ↦ conj ⟪f, u z⟫_ℂ • v z) μ := by
  have hm : StronglyMeasurable (fun z ↦ ⟪f, u z⟫_ℂ) := stronglyMeasurable_const.inner hu
  refine (hnorm.const_mul ‖f‖).mono'
    ((Complex.continuous_conj.comp_stronglyMeasurable hm).smul hv).aestronglyMeasurable ?_
  filter_upwards with z
  rw [norm_smul, Complex.norm_conj, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)

/-- Local bounds on the evaluation vectors give a continuous kernel by dominated convergence. -/
private theorem continuous_evaluation_kernel {E G : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    {e : X → E} {d : X → G} {u : X → E} {v : X → G}
    (he : Continuous e) (hd : Continuous d) (hu : StronglyMeasurable u) (hv : StronglyMeasurable v)
    (hnorm : Integrable (fun z ↦ ‖u z‖ * ‖v z‖) μ) :
    Continuous (fun p : X × X ↦ ∫ z, ⟪e p.1, u z⟫_ℂ * ⟪v z, d p.2⟫_ℂ ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let A := ‖e p.1‖ + 1
  let B := ‖d p.2‖ + 1
  have hA : ∀ᶠ q : X × X in 𝓝 p, ‖e q.1‖ < A :=
    (isOpen_lt (he.comp continuous_fst).norm continuous_const).mem_nhds (lt_add_one _)
  have hB : ∀ᶠ q : X × X in 𝓝 p, ‖d q.2‖ < B :=
    (isOpen_lt (hd.comp continuous_snd).norm continuous_const).mem_nhds (lt_add_one _)
  apply continuousAt_of_dominated (bound := fun z ↦ A * B * (‖u z‖ * ‖v z‖))
  · exact Eventually.of_forall fun q ↦
      ((stronglyMeasurable_const.inner hu).mul (hv.inner stronglyMeasurable_const)).aestronglyMeasurable
  · filter_upwards [hA, hB] with q hq₁ hq₂
    filter_upwards with z
    rw [norm_mul]
    have hx := (norm_inner_le_norm (𝕜 := ℂ) (e q.1) (u z)).trans
      (mul_le_mul_of_nonneg_right hq₁.le (norm_nonneg _))
    have hy := (norm_inner_le_norm (𝕜 := ℂ) (v z) (d q.2)).trans
      (mul_le_mul_of_nonneg_left hq₂.le (norm_nonneg _))
    calc
      _ ≤ (A * ‖u z‖) * (‖v z‖ * B) :=
        mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)
      _ = _ := by ring
  · exact hnorm.const_mul _
  · exact Eventually.of_forall fun z ↦
      (((he.comp continuous_fst).inner continuous_const).mul
        (continuous_const.inner (hd.comp continuous_snd))).continuousAt

/-- Paper: Theorem 12.4.1.1, pp. 515–517. At a fixed Hilbert level with continuous
evaluations, two strongly measurable square-integrable families of level vectors define a
nuclear operator with a continuous quotient kernel and an absolutely integrable
diagonal. The diagonal integral equals its Hilbert trace.
Reconstruction: The factorized kernel represents the cutoff dilation compression
when the two families are the cutoff-weighted evaluation vector and the
cutoff-weighted adjoint dilation average of the evaluation vector, respectively.
Deviation: This is a fixed-level result with evaluation and integrability hypotheses.
It gives no comparison with the sharp orbital masses as the levels change. -/
theorem sLocalTrace_evaluationKernel_of_memLp
    (V : Submodule ℂ H) [CompleteSpace V]
    (e u : X → H) (v : X → V)
    (he : Continuous e)
    (hu : StronglyMeasurable u) (hu₂ : MemLp u 2 μ) (huV : ∀ z, u z ∈ V)
    (hv : StronglyMeasurable v) (hv₂ : MemLp v 2 μ)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, (f : H)⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ)) :
    let k (p : X × X) := ∫ z, ⟪e p.1, u z⟫_ℂ * ⟪(v z : H), e p.2⟫_ℂ ∂μ
    ∃ (T : H →L[ℂ] H) (hT : IsNuclearOperator T),
      (∀ f : H, ∀ᵐ x ∂μ, T f x = ∫ z, ⟪e x, u z⟫_ℂ * ⟪(v z : H), f⟫_ℂ ∂μ) ∧
      Continuous k ∧
      (∀ f : H, ∀ᵐ x ∂μ, Integrable (fun y ↦ k (x, y) * f y) μ ∧
        T f x = ∫ y, k (x, y) * f y ∂μ) ∧
      Integrable (fun x ↦ k (x, x)) μ ∧
      hilbertTrace ⟨T, hT⟩ = (∫ x, k (x, x) ∂μ) ∧
      (∫ x, k (x, x) ∂μ) = ∫ z, ⟪(v z : H), u z⟫_ℂ ∂μ := by
  intro k
  let a (p : X × X) := ⟪e p.1, u p.2⟫_ℂ
  let b (p : X × X) := ⟪(v p.1 : H), e p.2⟫_ℂ
  have ha : MemLp a 2 (μ.prod μ) := memLp_evaluation_kernel he hu hu₂
    (fun z ↦ hrep ⟨u z, huV z⟩)
  have hV : MemLp (fun z ↦ (v z : H)) 2 μ := V.subtypeL.comp_memLp' hv₂
  have hv' : StronglyMeasurable (fun z ↦ (v z : H)) :=
    V.subtypeL.continuous.comp_stronglyMeasurable hv
  have hB := memLp_evaluation_kernel he hv' hV (fun z ↦ hrep (v z))
  have hB' := hB.comp_measurePreserving (Measure.measurePreserving_swap (μ := μ) (ν := μ))
  have hb : MemLp b 2 (μ.prod μ) := hB'.congr_norm
    ((hv'.comp_measurable measurable_fst).inner
      (he.stronglyMeasurable.comp_measurable measurable_snd)).aestronglyMeasurable
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
  have hk : Continuous k := continuous_evaluation_kernel he he hu hv' hnorm'
  let w (x : X) : V := ∫ z, conj (a (x,z)) • v z ∂μ
  have hwPair (x : X) (f : H) :
      ⟪(w x : H), f⟫_ℂ = ∫ z, a (x,z) * ⟪(v z : H), f⟫_ℂ ∂μ :=
    inner_integral_kernel_row V (fun z ↦ a (x,z)) v
      (integrable_kernel_row (e x) hu hv hnorm) f
  have hmass : Integrable (fun p : X × X ↦ a p * b p.swap) (μ.prod μ) :=
    ha.integrable_mul (hb.comp_measurePreserving (Measure.measurePreserving_swap (μ := μ) (ν := μ)))
  have hdiag := hmass.integral_prod_left
  refine ⟨T, hT, hTf, hk, ?_, hdiag, ?_, ?_⟩
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
  · change (∫ x, ∫ z, a (x,z) * b (z,x) ∂μ ∂μ) = _
    rw [integral_integral_swap (f := fun x z ↦ a (x,z) * b (z,x)) hmass]
    apply integral_congr_ae
    filter_upwards with z
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrep ⟨u z, huV z⟩, hrep (v z)] with x hu' hv'
    change ⟪e x, u z⟫_ℂ * ⟪(v z : H), e x⟫_ℂ = _
    rw [show ⟪(v z : H), e x⟫_ℂ = conj ⟪e x, (v z : H)⟫_ℂ from (inner_conj_symm _ _).symm,
      hv', hu', RCLike.inner_apply]

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
  have _ := hC
  obtain ⟨T, hT, hTf, hk, hkernel, hdiag, htrace, _⟩ :=
    sLocalTrace_evaluationKernel_of_memLp V e u v he hu.stronglyMeasurable hu₂ huV
      hv.stronglyMeasurable hv₂ hrep
  exact ⟨T, hT, hTf, hk, hkernel, hdiag, htrace⟩

/-- Paper: Theorem 12.4.1.1, Steps II–III, pp. 516–517. The fixed-level cutoff compression
has a continuous quotient kernel whose integrable diagonal computes both the ambient and level
traces. Integrating out the reproducing kernel gives the single integral of the symbol against
`⟪e z, D (e z)⟫`. A measurable cutoff with square-integrable masked evaluations suffices.
Deviation: The result assumes a continuous family reproducing the level and a bounded action
on it. It treats a single cutoff. -/
theorem sLocalTrace_projectedCutoffKernel_of_memLp_smul
    (V : Submodule ℂ H) [CompleteSpace V]
    (e : X → V) (he : Continuous e)
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, f⟫_ℂ) =ᵐ[μ] ((f : H) : X → ℂ))
    (c : X → ℝ) (hc : Measurable c) (hce : MemLp (fun z ↦ c z • e z) 2 μ)
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
      hilbertTrace ⟨L, hL⟩ = (∫ x, k (x, x) ∂μ) ∧
      (∫ x, k (x, x) ∂μ) = ∫ z, (c z ^ 2 : ℝ) • ⟪e z, D (e z)⟫_ℂ ∂μ := by
  intro j q L T k
  let u₀ (z : X) : V := c z • e z
  let v (z : X) : V := c z • D.adjoint (e z)
  let u (z : X) : H := j (u₀ z)
  have hu₀ : StronglyMeasurable u₀ := hc.stronglyMeasurable.smul he.stronglyMeasurable
  have hu : StronglyMeasurable u := j.continuous.comp_stronglyMeasurable hu₀
  have hv : StronglyMeasurable v :=
    hc.stronglyMeasurable.smul (D.adjoint.continuous.comp he).stronglyMeasurable
  have hv₂ : MemLp v 2 μ := by
    refine (D.adjoint.comp_memLp' hce).ae_eq (Eventually.of_forall fun z ↦ ?_)
    change D.adjoint ((c z : ℂ) • e z) = (c z : ℂ) • D.adjoint (e z)
    exact map_smul _ _ _
  obtain ⟨U, hU, hUapply, hcont, hkernel, hdiag, htrace, hsingle⟩ :=
    sLocalTrace_evaluationKernel_of_memLp V (fun x ↦ j (e x)) u v (j.continuous.comp he)
      hu (j.comp_memLp' hce) (fun z ↦ (u₀ z).property) hv hv₂ hrep
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
  rw [hk'] at hcont hkernel hdiag htrace hsingle
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
  have hsingle' : (∫ x, k (x, x) ∂μ) = ∫ z, (c z ^ 2 : ℝ) • ⟪e z, D (e z)⟫_ℂ ∂μ := by
    rw [hsingle]
    apply integral_congr_ae
    filter_upwards with z
    change ⟪(c z : ℂ) • D.adjoint (e z), (c z : ℂ) • e z⟫_ℂ = _
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, D.adjoint_inner_left]
    simp only [Complex.real_smul, Complex.ofReal_pow]
    ring
  refine ⟨hT, hL, hcont, heq ▸ hkernel, hdiag, hTtrace, ?_, hsingle'⟩
  rw [← hTtrace, hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
  have hn := nuclearTrace_factor_comps hilbert_approximationProperty
    hilbert_approximationProperty j hj _ hLq
  simpa only [hLqj] using hn

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
  have hce : MemLp (fun z ↦ c z • e z) 2 μ := by
    refine (hc₂.norm.const_smul C).mono' (hc.smul he).aestronglyMeasurable
      (Eventually.of_forall fun z ↦ ?_)
    change ‖c z • e z‖ ≤ C * ‖c z‖
    rw [norm_smul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC z) (norm_nonneg _)
  obtain ⟨hT, hL, hk, hkernel, hdiag, hTtr, hLtr, _⟩ :=
    sLocalTrace_projectedCutoffKernel_of_memLp_smul V e he hrep c hc.measurable hce M hM D
  exact ⟨hT, hL, hk, hkernel, hdiag, hTtr, hLtr⟩

open scoped NNReal in
/-- Paper: Theorem 12.4.1.1, Step II, pp. 516–517. In the rational real-place
Haar chart, evaluation vectors bounded by a constant times the square root of
the radius become square integrable after any bounded measurable upper cutoff.
The squared norm has integral at most the upper radius times the square of
the two bounds. The cutoff may extend all the way down to zero. -/
theorem sLocalTrace_memLp_upperCutoff_halfDensity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : ℝ≥0ˣ → E) (he : Continuous e) (C : ℝ≥0)
    (heC : ∀ x, ‖e x‖ ≤ C * Real.sqrt (x.val : ℝ))
    (c : ℝ≥0ˣ → ℝ) (hc : Measurable c) (B : ℝ≥0) (hcB : ∀ x, ‖c x‖ ≤ B)
    {r : ℝ} (hr : 0 < r) (hsupp : ∀ x : ℝ≥0ˣ, r < (x.val : ℝ) → c x = 0) :
    MemLp (fun x ↦ c x • e x) 2 positiveRealHaar ∧
      (∫ x, ‖c x • e x‖ ^ 2 ∂positiveRealHaar) ≤ ((B : ℝ) * C) ^ 2 * r := by
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let p (t : ℝ) := Units.mk0 (Real.exp t).toNNReal (by positivity)
  have hp : Measurable p :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hval (t : ℝ) : ((p t).val : ℝ) = Real.exp t :=
    Real.coe_toNNReal _ (Real.exp_pos _).le
  have hm := hc.stronglyMeasurable.smul he.stronglyMeasurable
  let g (t : ℝ) := ((B : ℝ) * C) ^ 2 * (Set.Iic (Real.log r)).indicator Real.exp t
  have hg : Integrable g := ((integrableOn_exp_Iic (Real.log r)).integrable_indicator
    measurableSet_Iic).const_mul _
  have hbound (t : ℝ) : ‖c (p t) • e (p t)‖ ^ 2 ≤ g t := by
    dsimp only [g]
    by_cases ht : t ≤ Real.log r
    · rw [Set.indicator_of_mem ht, norm_smul]
      have h := mul_le_mul (hcB (p t)) (heC (p t)) (norm_nonneg _) B.coe_nonneg
      rw [hval, ← mul_assoc] at h
      simpa only [mul_pow, Real.sq_sqrt (Real.exp_pos _).le] using
        pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h 2
    · have hrt : r < ((p t).val : ℝ) := by
        rw [hval, ← Real.exp_log hr]
        exact Real.exp_lt_exp.mpr (lt_of_not_ge ht)
      have hout : t ∉ Set.Iic (Real.log r) := ht
      simp [hsupp _ hrt, Set.indicator_of_notMem hout]
  have hi : Integrable (fun t ↦ ‖c (p t) • e (p t)‖ ^ 2) :=
    hg.mono' (((hm.norm.pow 2).comp_measurable hp).aestronglyMeasurable)
      (Eventually.of_forall fun t ↦ (Real.norm_of_nonneg (sq_nonneg _)).trans_le (hbound t))
  refine ⟨(memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
    ((integrable_map_measure (hm.norm.pow 2).aestronglyMeasurable hp.aemeasurable).2 hi), ?_⟩
  calc
    _ = ∫ t, ‖c (p t) • e (p t)‖ ^ 2 :=
      integral_map hp.aemeasurable (hm.norm.pow 2).aestronglyMeasurable
    _ ≤ ∫ t, g t := integral_mono hi hg hbound
    _ = _ := by
      simp only [g, integral_const_mul, integral_indicator measurableSet_Iic,
        integral_exp_Iic, Real.exp_log hr]

/-- The masked L² norm bounds the integral of the reproducing diagonal. -/
private theorem norm_integral_masked_pairing_le {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] {μ : Measure X}
    (e : X → E) (c : X → ℝ) (hce : MemLp (fun x ↦ c x • e x) 2 μ) (D : E →L[ℂ] E) :
    ‖∫ x, (c x ^ 2 : ℝ) • ⟪e x, D (e x)⟫_ℂ ∂μ‖ ≤ ‖D‖ * ∫ x, ‖c x • e x‖ ^ 2 ∂μ := by
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le
    (((memLp_two_iff_integrable_sq_norm hce.aestronglyMeasurable).mp hce).const_mul _)
  filter_upwards with x
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ c x ^ 2 * (‖e x‖ * (‖D‖ * ‖e x‖)) := by
      gcongr
      exact (norm_inner_le_norm (e x) _).trans
        (mul_le_mul_of_nonneg_left (D.le_opNorm _) (norm_nonneg _))
    _ = _ := by ring

open scoped NNReal in
/-- Paper: Theorem 12.4.1.1, p. 514 n. 2 and Steps II–III, pp. 516–517. In the
positive real Haar chart, a spatial mask supported in (0, r] contributes at most
`‖D‖ * C² * r` to the absolute level trace when evaluation has norm at most
`C * √x`. The multiplier acts on the ambient L² space by the given mask.
Deviation: This estimate fixes the level and the action. The evaluation bound is a hypothesis. -/
theorem sLocalTrace_upperCutoff_halfDensity_trace
    (V : Submodule ℂ (Lp ℂ 2 positiveRealHaar)) [CompleteSpace V]
    (e : ℝ≥0ˣ → V) (he : Continuous e) (C : ℝ≥0)
    (heC : ∀ x, ‖e x‖ ≤ C * Real.sqrt (x.val : ℝ))
    (hrep : ∀ f : V, (fun x ↦ ⟪e x, f⟫_ℂ) =ᵐ[positiveRealHaar]
      ((f : Lp ℂ 2 positiveRealHaar) : ℝ≥0ˣ → ℂ))
    (ρ : ℝ≥0ˣ → ℝ) (hm : Measurable ρ) (hρ : ∀ x, ρ x ∈ Set.Icc 0 1)
    {r : ℝ} (hr : 0 < r) (hsupp : ∀ x : ℝ≥0ˣ, r < (x.val : ℝ) → ρ x = 0)
    (D : V →L[ℂ] V) :
    ∃ M : Lp ℂ 2 positiveRealHaar →L[ℂ] Lp ℂ 2 positiveRealHaar,
      (∀ f : Lp ℂ 2 positiveRealHaar, ∀ᵐ x ∂positiveRealHaar, M f x = ρ x • f x) ∧
      let L := V.orthogonalProjectionOnto.comp (M.comp (V.subtypeL.comp D))
      ∃ hL : IsNuclearOperator L,
        hilbertTrace ⟨L, hL⟩ = (∫ x, ρ x • ⟪e x, D (e x)⟫_ℂ ∂positiveRealHaar) ∧
        ‖hilbertTrace ⟨L, hL⟩‖ ≤ ‖D‖ * (C : ℝ) ^ 2 * r := by
  let p : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : LocallyCompactSpace ℝ≥0ˣ := p.symm.isOpenEmbedding.locallyCompactSpace
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  have hμ : positiveRealHaar = volume.map p := by
    apply congrArg (fun a : ℝ → ℝ≥0ˣ ↦ volume.map a)
    funext x
    apply Units.ext
    exact NNReal.eq (Real.coe_toNNReal _ (Real.exp_pos x).le)
  let : IsFiniteMeasureOnCompacts positiveRealHaar :=
    hμ ▸ Measure.IsFiniteMeasureOnCompacts.map volume p
  let : Measure.InnerRegular positiveRealHaar := hμ ▸ Measure.InnerRegular.map p
  let c (x : ℝ≥0ˣ) := Real.sqrt (ρ x)
  have hc : Measurable c := Real.continuous_sqrt.measurable.comp hm
  have hcB (x) : ‖c x‖ ≤ (1 : ℝ≥0) := by
    simpa only [c, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), NNReal.coe_one,
      Real.sqrt_one] using Real.sqrt_le_sqrt (hρ x).2
  have hcρ (x) : c x ^ 2 = ρ x := Real.sq_sqrt (hρ x).1
  obtain ⟨hce, henergy⟩ := sLocalTrace_memLp_upperCutoff_halfDensity e he C heC c hc 1 hcB hr
    (fun x hx ↦ by simp [c, hsupp x hx])
  have hb (x) : |ρ x| ≤ 1 := (abs_of_nonneg (hρ x).1).trans_le (hρ x).2
  let M := lpCutoffMultiplier positiveRealHaar ρ hm hb
  have hM (f : Lp ℂ 2 positiveRealHaar) :
      ∀ᵐ x ∂positiveRealHaar, M f x = ρ x • f x := lpCutoffMultiplier_apply _ _ hm hb f
  have hMc (f : Lp ℂ 2 positiveRealHaar) :
      ∀ᵐ x ∂positiveRealHaar, M f x = (c x ^ 2 : ℝ) • f x := by simpa only [hcρ] using hM f
  obtain ⟨_, hL, _, _, _, _, htr, hsingle⟩ :=
    sLocalTrace_projectedCutoffKernel_of_memLp_smul V e he hrep c hc hce M hMc D
  refine ⟨M, hM, hL, ?_, ?_⟩
  · simpa only [hcρ] using htr.trans hsingle
  · rw [htr, hsingle]
    refine (norm_integral_masked_pairing_le e c hce D).trans ?_
    rw [mul_assoc]
    simp only [NNReal.coe_one, one_mul] at henergy
    exact mul_le_mul_of_nonneg_left henergy (norm_nonneg _)

end RiemannMasullo.Isolated
