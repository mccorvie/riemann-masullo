module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # The geometric part of the projective kernel in Theorem 10.4.3.5 -/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set UniformSpace
open scoped NNReal NumberField.AdeleRing TensorProduct Topology

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

/-- Applying a bounded map to every output of convergent projective rectangles gives a Cauchy net. -/
private theorem cauchy_rectangles_map_output {Z J E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (e : Z ↪ ℕ × ℕ) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (u : J → E) (v : J → V) (P : V →L[ℂ] V)
    {K : Completion (ProjectiveTensor E V)} (hK : Tendsto (spectralKernelRectangle e N jet u v) atTop (𝓝 K)) :
    Cauchy (Filter.map (spectralKernelRectangle e N jet u (fun i ↦ P (v i))) atTop) := by
  let idE := ContinuousLinearMap.id ℂ E
  let L : ProjectiveTensor E V →L[ℂ] ProjectiveTensor E V :=
    ⟨projectiveTensorMap idE.toLinearMap P.toLinearMap, projectiveTensorMap_continuous idE P⟩
  apply Filter.Tendsto.cauchy_map (a := L.completion K)
  apply ((L.completion.continuous.tendsto K).comp hK).congr
  intro ij
  unfold Function.comp spectralKernelRectangle
  rw [ContinuousLinearMap.completion_apply_coe]
  apply congrArg ((↑) : ProjectiveTensor E V → Completion (ProjectiveTensor E V))
  change projectiveTensorMap idE.toLinearMap P.toLinearMap _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact (map_sum (TensorProduct.map idE.toLinearMap P.toLinearMap)
    (fun m : Fin (N z) ↦ u (jet z m) ⊗ₜ[ℂ] v (jet z m)) Finset.univ).trans
    (Finset.sum_congr rfl fun m _ ↦ TensorProduct.map_tmul _ _ _ _)

open scoped ComplexOrder in
/-- The projective gauge of the unit pure tensors controls every zero-neighborhood.
A copy of the private `spectralLineQuotientKernel_tendsto_gauge` of `Sec4b`. -/
private theorem spectralStripGeometricKernel_cauchy_gauge {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (U : Set (ProjectiveTensor X Y)) (hU : U ∈ 𝓝 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ProjectiveTensor X Y,
      gauge (convexHull ℝ (image2 (TensorProduct.tmul ℂ)
        (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))) z < ε → z ∈ U := by
  let B (r s : ℝ) : Set (ProjectiveTensor X Y) :=
    image2 (TensorProduct.tmul ℂ) (Metric.closedBall 0 r) (Metric.closedBall 0 s)
  let : PolynormableSpace ℂ X := (norm_withSeminorms ℂ X).toPolynormableSpace
  let : PolynormableSpace ℂ Y := (norm_withSeminorms ℂ Y).toPolynormableSpace
  let : IsScalarTower ℝ ℂ (ProjectiveTensor X Y) := IsScalarTower.restrictScalars ℝ ℂ _
  let : ContinuousSMul ℂ (ProjectiveTensor X Y) := PolynormableSpace.continuousSMul ℂ _
  let : ContinuousSMul ℝ (ProjectiveTensor X Y) := IsScalarTower.continuousSMul ℂ
  have hb := projectiveTensor_zero_basis (E := X) (F := Y) (Metric.nhds_basis_closedBall (x := (0 : X)))
    (Metric.nhds_basis_closedBall (x := (0 : Y)))
  have hbal : Balanced ℂ (B 1 1) := by
    intro c hc
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    refine ⟨c • x, ?_, y, hy, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg x)).trans
      (by simpa using hx)
  have hrect : absConvexHull ℂ (B 1 1) ⊆ convexHull ℝ (B 1 1) := by
    rw [absConvexHull_eq_convexHull_balancedHull, show balancedHull ℂ (B 1 1) = B 1 1 from
      le_antisymm (hbal.balancedHull_subset_of_subset Subset.rfl) (subset_balancedHull ℂ)]
    exact convexHull_min (subset_convexHull ..) (convex_RCLike_iff_convex_real.mpr (convex_convexHull ..))
  have hunit : convexHull ℝ (B 1 1) ∈ 𝓝 (0 : ProjectiveTensor X Y) :=
    Filter.mem_of_superset (hb.mem_of_mem (i := (1, 1)) ⟨one_pos, one_pos⟩) hrect
  obtain ⟨⟨r, s⟩, ⟨hr, hs⟩, hsub⟩ := hb.mem_iff.mp hU
  refine ⟨r * s, mul_pos hr hs, fun z hz ↦ ?_⟩
  obtain ⟨t, ht, htrs, hz⟩ := exists_lt_of_gauge_lt (absorbent_nhds_zero hunit) hz
  apply hsub
  rw [← convexHull_smul] at hz
  refine convexHull_min ?_ (convex_absConvexHull.lift ℝ) hz
  rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  apply subset_absConvexHull
  refine ⟨(t / s : ℝ) • x, ?_, s • y, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (div_nonneg ht.le hs.le)]
    exact (mul_le_of_le_one_right (div_nonneg ht.le hs.le) (by simpa using hx)).trans
      ((div_lt_iff₀ hs).mpr htrs).le
  · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hs.le]
    exact mul_le_of_le_one_right hs.le (by simpa using hy)
  · rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, div_mul_cancel₀ _ hs.ne']
    rfl

/-- Trace-norm Cauchy rectangles of finite-rank operators give Cauchy tensor rectangles.
A copy of the private `spectralLineQuotientKernel_tendsto_of_traceCauchy` of `Sec4b`. -/
private theorem spectralStripGeometricKernel_cauchy_of_traceCauchy {H Z J : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (x : J → H) (f : J → StrongDual ℂ H) (e : Z ↪ ℕ × ℕ)
    (N : Z → ℕ) (i : (z : Z) → Fin (N z) → J)
    (hc : SpectralRectanglesTraceCauchy (fun ij ↦ spectralConvolutionFiniteSum A x f
      (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn) N i)) :
    ∃ K, Tendsto (spectralKernelRectangle e N i (fun j ↦ (f j).comp A) x) atTop (𝓝 K) := by
  classical
  let P := ProjectiveTensor (StrongDual ℂ H) H
  let box (ij : ℕ × ℕ) := ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn
  let w (ij : ℕ × ℕ) : P := ∑ z ∈ box ij, ∑ m : Fin (N z), (f (i z m)).comp A ⊗ₜ[ℂ] x (i z m)
  have hop (ij) : tensorToFiniteRank (w ij) = spectralConvolutionFiniteSum A x f (box ij) N i := by
    change tensorToFiniteRank (∑ z ∈ box ij, ∑ m : Fin (N z), (f (i z m)).comp A ⊗ₜ[ℂ] x (i z m)) = _
    simp only [map_sum, spectralConvolutionFiniteSum]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro m _
    exact ContinuousLinearMap.ext fun y ↦ tensorToFiniteRank_tmul _ _ y
  obtain ⟨huc, equiv, hval, hnorm⟩ := exists_projectiveTensorCompletion_traceClassIsometry (E := H) (F := H)
  have hcauchy : CauchySeq w := by
    apply (cauchySeq_iff_sub_mem w).mpr
    intro U hU
    obtain ⟨ε, hε, hball⟩ := spectralStripGeometricKernel_cauchy_gauge U hU
    obtain ⟨b, hb⟩ := hc ε hε
    refine ⟨b, fun j hj k hk ↦ hball _ ?_⟩
    obtain ⟨T, hT, hsmall⟩ := hb j k hj hk
    have heq : (equiv ((w j - w k : P) : Completion P)).val = T.val := by
      rw [hval, completedProjectiveTensorToOperators_coe]
      exact (map_sub tensorToFiniteRank (w j : StrongDual ℂ H ⊗[ℂ] H) (w k)).trans
        ((congrArg₂ (· - ·) (hop j) (hop k)).trans hT.symm)
    have hnorm' := (hnorm ((w j - w k : P) : Completion P)).trans (Completion.extension_coe huc _)
    exact hnorm'.symm.trans_lt ((congrArg schattenNorm (Subtype.ext heq)).trans_lt
      ((schattenNorm_one_eq_traceNorm T).trans_lt hsmall))
  exact cauchySeq_tendsto_of_complete
    (UniformContinuous.comp_cauchySeq (Completion.uniformContinuous_coe (α := P)) hcauchy)

/-- Classical input: in the trace class of a Hilbert space, a family whose finite sums are
bounded in trace norm (a weakly unconditionally Cauchy family) is unconditionally summable, so
its finite sums away from a large finite set are small. By the theorem of Bessaga and
Pełczyński (Studia Math. 17 (1958), 151–164; Albiac–Kalton, *Topics in Banach Space Theory*,
Theorem 2.4.11) this holds in every Banach space containing no copy of `c₀`. The trace class
contains none: it has cotype 2 (N. Tomczak-Jaegermann, Studia Math. 50 (1974), 163–182), and it
is weakly sequentially complete as the predual of `B(H)` (Takesaki, *Theory of Operator
Algebras I*, Ch. III §5). Only countably many members of such a family are nonzero, and the
countable case is the cited one.
Deviation: Stated for an arbitrary index type, with tails taken over finite sets disjoint from
a finite exceptional set. -/
theorem traceClass_blockSums_tails_of_bddAbove {H Z : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : Z → nuclearEndomorphisms H)
    (hbound : BddAbove (range fun K : Finset Z ↦ traceNorm (∑ z ∈ K, R z))) :
    ∀ ε > (0 : ℝ), ∃ F : Finset Z, ∀ K : Finset Z, Disjoint K F →
      traceNorm (∑ z ∈ K, R z) < ε := by
  sorry

/-- Small tails of a family of nuclear operators make its rectangular sums Cauchy in trace norm. -/
private theorem spectralStripGeometricKernel_traceCauchy_of_tails {H Z : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : Z → nuclearEndomorphisms H) (e : Z ↪ ℕ × ℕ)
    (htail : ∀ ε > (0 : ℝ), ∃ F : Finset Z, ∀ K : Finset Z, Disjoint K F →
      traceNorm (∑ z ∈ K, R z) < ε) :
    SpectralRectanglesTraceCauchy (fun ij : ℕ × ℕ ↦
      (∑ z ∈ ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn, R z).val) := by
  classical
  intro ε hε
  obtain ⟨F, hF⟩ := htail (ε / 2) (half_pos hε)
  let box (ij : ℕ × ℕ) := ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn
  have hsub (ij : ℕ × ℕ) (h : F.sup e ≤ ij) : F ⊆ box ij := by
    intro z hz
    have hle : e z ≤ ij := (Finset.le_sup (f := e) hz).trans h
    simp only [box, Finset.mem_preimage]
    exact Finset.mem_product.mpr ⟨Finset.mem_Iic.mpr hle.1, Finset.mem_Iic.mpr hle.2⟩
  refine ⟨F.sup e, fun j k hj hk ↦ ?_⟩
  let X := ∑ z ∈ box j \ box k, R z
  let Y := ∑ z ∈ box k \ box j, R z
  refine ⟨X - Y, ?_, ?_⟩
  · have h := Finset.sum_sdiff_sub_sum_sdiff (s₁ := box k) (s₂ := box j) (f := R)
    change (X - Y).val = (∑ z ∈ box j, R z).val - (∑ z ∈ box k, R z).val
    rw [← Submodule.coe_sub, ← h]
  · let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
    have hc := traceNorm_normedSpaceCore (H := H)
    have hneg : traceNorm (-Y) = traceNorm Y := by
      rw [← neg_one_smul ℂ Y]
      simpa only [norm_neg, norm_one, one_mul] using hc.norm_smul (-1 : ℂ) Y
    have htr := hc.norm_triangle X (-Y)
    change traceNorm (X + -Y) ≤ traceNorm X + traceNorm (-Y) at htr
    rw [← sub_eq_add_neg, hneg] at htr
    have hX := hF (box j \ box k) (Finset.disjoint_of_subset_right (hsub k hk) Finset.sdiff_disjoint)
    have hY := hF (box k \ box j) (Finset.disjoint_of_subset_right (hsub j hj) Finset.sdiff_disjoint)
    change traceNorm X < ε / 2 at hX
    change traceNorm Y < ε / 2 at hY
    linarith

/-- Bounded block sums of the rank-one operators `v ↦ f_j(q v) • v_j` make the rectangles of the
tensors `d(f_j ∘ q) ⊗ v_j` Cauchy, by the classical input and the trace-class isometry. -/
private theorem spectralStripGeometricKernel_cauchy_of_blocks {W W' H Z J : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    [NormedAddCommGroup W'] [NormedSpace ℂ W'] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (d : StrongDual ℂ W →L[ℂ] W') (q : W →L[ℂ] H)
    (e : Z ↪ ℕ × ℕ) (N : Z → ℕ) (i : (z : Z) → Fin (N z) → J)
    (u : J → W') (f : J → StrongDual ℂ H) (v : J → W) (hu : ∀ j, d ((f j).comp q) = u j)
    (hbound : BddAbove (range fun K : Finset Z ↦ traceNorm (∑ z ∈ K, ∑ m : Fin (N z),
      (⟨((f (i z m)).comp q).smulRight (v (i z m)), smulRight_mem_nuclearEndomorphisms _ _⟩ :
        nuclearEndomorphisms W)))) :
    Cauchy (Filter.map (spectralKernelRectangle e N i u v) atTop) := by
  classical
  have hrect := spectralStripGeometricKernel_traceCauchy_of_tails _ e
    (traceClass_blockSums_tails_of_bddAbove _ hbound)
  have hc : SpectralRectanglesTraceCauchy (fun ij : ℕ × ℕ ↦ spectralConvolutionFiniteSum
      (ContinuousLinearMap.id ℂ W) v (fun j ↦ (f j).comp q)
      (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn) N i) := by
    convert hrect using 2 with ij
    simp only [spectralConvolutionFiniteSum, Submodule.coe_sum, ContinuousLinearMap.comp_id]
  obtain ⟨K, hK⟩ := spectralStripGeometricKernel_cauchy_of_traceCauchy _ v _ e N i hc
  let idW := ContinuousLinearMap.id ℂ W
  let L : ProjectiveTensor (StrongDual ℂ W) W →L[ℂ] ProjectiveTensor W' W :=
    ⟨projectiveTensorMap d.toLinearMap idW.toLinearMap, projectiveTensorMap_continuous d idW⟩
  apply Filter.Tendsto.cauchy_map (a := L.completion K)
  apply ((L.completion.continuous.tendsto K).comp hK).congr
  intro ij
  unfold Function.comp spectralKernelRectangle
  rw [ContinuousLinearMap.completion_apply_coe]
  apply congrArg ((↑) : ProjectiveTensor W' W → Completion (ProjectiveTensor W' W))
  change projectiveTensorMap d.toLinearMap idW.toLinearMap _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  refine (map_sum (TensorProduct.map d.toLinearMap idW.toLinearMap) _ Finset.univ).trans
    (Finset.sum_congr rfl fun m _ ↦ ?_)
  rw [TensorProduct.map_tmul]
  change d (((f (i z m)).comp q).comp idW) ⊗ₜ[ℂ] v (i z m) = u (i z m) ⊗ₜ[ℂ] v (i z m)
  rw [ContinuousLinearMap.comp_id, hu]

variable {F : Type*} [Field F] [NumberField F]
variable (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
  (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)) (ha : 0 < a)
  (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual (IdeleClassGroup (𝓞 F) F))

local notation "hs₀" => (zero_le_one.trans hs.le)
local notation "hI" => (neg_nonpos.mpr hα).trans hα
local notation "Θ₀" => globalThetaSobolev F a hI hs₀
local notation "H(" F ", " a ", " hα ", " hs ")" =>
  spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) (zero_le_one.trans (le_of_lt hs))
local notation "Sₐ(" v ")" => ((Θ₀).quotientEquivOrthogonal v).val
local notation "Aφ" => hardySobolevTestAction (ideleClassTamagawaMeasure F) (continuousIdeleClassNorm F)
  (-α) α s hI hs₀ φ
local notation "Gₐ" => geometricProjection (F := F) a hα hs₀
local notation "Pₐ" => spectralProjection (F := F) a hα hs₀
local notation "Dₐ" => spectralSobolevDualEmbedding F a hI hs₀

local notation "order(" χ ", " a ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (χ (z).1))
  (((a + (z).2.1 : ℝ) : ℂ) + ((z).2.2 : ℂ) * Complex.I)
local notation "zeros(" F ", " χ ", " a ", " α ")" => {z : PontryaginDual (ideleClassNorm F).ker × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ, a, z)}
local notation "jetCount(" z ")" => spectralStripMultiplicity α s (z).val.2.1 (order(χ, a, (z).val)).untop₀.toNat
local notation "jets" => SpectralStripJetIndex (F := F) χ a α s

variable (eχ : PontryaginDual (ideleClassNorm F).ker ↪ ℕ) (e : zeros(F, χ, a, α) ↪ ℕ × ℕ)
  (x : SpectralStripJetIndex χ a α s → H(F, a, hα, hs))
  (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(F, a, hα, hs))
  (hχ : IsSpectralBasepointChoice χ) (he : ∀ z, (e z).1 = eχ z.val.1)
  (horder : ∀ z z' : zeros(F, χ, a, α), z.val.1 = z'.val.1 → (e z).2 ≤ (e z').2 → |z.val.2.2| ≤ |z'.val.2.2|)
  (hb : IsSpectralMarkushevichBasis x f ∧ ∀ j,
    spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) (zero_le_one.trans hs.le) (f j) =
    (spectralStripJet_memLp χ hα (zero_le_one.trans hs.le) j).toLp
      (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))

local notation "rectangles(" output ")" =>
  spectralKernelRectangle e (fun z ↦ jetCount(z))
    (fun z m ↦ (⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩ : jets))
    (fun j ↦ Dₐ (f j)) (output)
local notation "geometricRectangles" => rectangles((fun j ↦ Gₐ (Aφ (Sₐ(x j)))))
local notation "ambientRectangles" => rectangles((fun j ↦ Aφ (Sₐ(x j))))

include ha hχ he horder hb

local notation "jet(" z ", " m ")" =>
  (⟨((z).val.1, (z).val.2.1, (z).val.2.2, (m).val), (m).isLt⟩ : jets)
local notation "geometricBlock(" z ")" =>
  (∑ m : Fin (jetCount(z)),
    (⟨((f jet(z, m)).comp (Θ₀).mkQL).smulRight (Gₐ (Aφ (Sₐ(x jet(z, m))))),
      smulRight_mem_nuclearEndomorphisms _ _⟩ : nuclearEndomorphisms _))

/-- Paper: Theorem 10.4.3.5(2), p. 472. For each zero `z` of the strip, let `R_z` be the
finite-rank operator `v ↦ ∑ₘ f_{z,m}(q v) • P^geom_a(A(φ)(S_a x_{z,m}))` on the Sobolev space,
summed over the jets kept at `z`; here `q` is the quotient map and `S_a` its isometric section.
The finite sums of the `R_z`, over arbitrary finite sets of zeros, are bounded in trace norm.
Reconstruction: The paper gives no estimate for the geometric component (p. 472). This is the
geometric analogue of the bound that `spectralStripConvolution_traceCauchy` obtains for the
quotient sums; with `traceClass_blockSums_tails_of_bddAbove` it implies
`spectralStripGeometricKernel_cauchy`. It asks for more than that statement: summability of
the blocks in every order, where the theorem needs convergence along its rectangles only. It
is equivalent to the summability, for every compact
operator `U`, of `z ↦ ∑ₘ f_{z,m}(q(U(P^geom_a(A(φ)(S_a x_{z,m})))))`, by uniform boundedness.
Gap: No bound is known for the geometric output of convolution on the biorthogonal vectors,
that is, for the part of `A(φ)(S_a x_{z,m})` outside the spectral subspace; the bound
(10.4.2.34) on p. 464 does not give one. The statement implies that `P^geom_a ∘ A(φ) ∘ P^spec_a`
is nuclear on the Sobolev space, which is not known either. Nothing in the Lean uses this statement, and it is not
known how it connects with the rest of the proof in Lean; in the paper it is used on pp. 471–474. -/
theorem spectralStripGeometricKernel_blocks_bddAbove :
    BddAbove (range fun K : Finset zeros(F, χ, a, α) ↦ traceNorm (∑ z ∈ K, geometricBlock(z))) := by
  sorry

/-- Paper: Theorem 10.4.3.5(2), p. 472. At positive twist and Sobolev order above one, the
geometric projections of the corrected ambient rectangles are Cauchy in the completed
projective tensor product.
Deviation: For the operator in (10.4.3.45), convolution acts on the orthogonal output lift.
The rectangles use injections of the actual strip zeros and the strict §10.2 boundary cutoff.
Reconstruction: This is the geometric component of the convergence claimed on pp. 472–473,
with the operator order repaired in §10.4.3. The paper gives no separate geometric estimate.
Proved here (#7427) from the open statement `spectralStripGeometricKernel_blocks_bddAbove`
and the classical input `traceClass_blockSums_tails_of_bddAbove`. The quotient estimates
control the spectral component only, and the bound (10.4.2.34) on p. 464 gives no bound
tending to zero for these projective tails. Nothing in the Lean outside this file uses this
statement, and it is not known how it connects with the rest of the proof in Lean; in the
paper it is used on pp. 471–474. -/
theorem spectralStripGeometricKernel_cauchy : Cauchy (Filter.map geometricRectangles atTop) :=
  spectralStripGeometricKernel_cauchy_of_blocks
    (modulatedIntervalSobolev_dual (continuousIdeleClassNorm F : IdeleClassGroup (𝓞 F) F →ₜ* ℝ≥0ˣ)
      ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ (ideleClassTamagawaMeasure F)
      (-α) α s hI hs₀).exists.choose.toContinuousLinearEquiv.toContinuousLinearMap
    (Θ₀).mkQL e _ _ _ f _ (fun _ ↦ rfl)
    (spectralStripGeometricKernel_blocks_bddAbove a hα hs φ ha χ eχ e x f hχ he horder hb)

/-- Paper: Theorem 10.4.3.5(2)–(3), p. 472. The corrected ambient net converges to a kernel
representing convolution after projection (p. 473) exactly when its geometric rectangles are Cauchy.
Deviation: Both conclusions concern the same ambient rectangles, with convolution on the output
and the repaired indexing of §10.4.3.
Reconstruction: The equivalence identifies exactly what the geometric estimate on pp. 471–473 must supply. -/
theorem spectralStripAmbientKernel_exists_iff_geometric_cauchy :
    (∃ K, Tendsto ambientRectangles atTop (𝓝 K) ∧
      sobolevProjectiveKernelOperator (F := F) hα hs₀ K = (Aφ).comp Pₐ) ↔
      Cauchy (Filter.map geometricRectangles atTop) := by
  constructor
  · rintro ⟨K, hK, _⟩
    exact cauchy_rectangles_map_output e _ _ _ (fun j ↦ Aφ (Sₐ(x j))) Gₐ hK
  · intro hgeom
    exact (spectralStripAmbientKernel_tendsto (F := F) a hα hs φ ha χ eχ e x f hχ he horder hb hgeom).imp
      fun K hK ↦ ⟨hK, spectralStripAmbientKernel_operator (F := F) a hα hs φ ha χ eχ e x f hχ he horder hb K hK⟩

/-- Paper: Theorem 10.4.3.5(2)–(3), p. 472. The isolated geometric Cauchy estimate supplies
the limit and the operator identity (10.4.3.45) on p. 473.
Deviation: The ambient tensors use the repaired output action and strip indexing of §10.4.3. -/
theorem spectralStripAmbientKernel_exists :
    ∃ K, Tendsto ambientRectangles atTop (𝓝 K) ∧
      sobolevProjectiveKernelOperator (F := F) hα hs₀ K = (Aφ).comp Pₐ :=
  (spectralStripAmbientKernel_exists_iff_geometric_cauchy a hα hs φ ha χ eχ e x f hχ he horder hb).mpr
    (spectralStripGeometricKernel_cauchy a hα hs φ ha χ eχ e x f hχ he horder hb)

end RiemannMasullo.Isolated
