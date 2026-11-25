module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_ClusterSums
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # The kernels of §10.4.3 with the zeros summed by clusters

Theorems 10.4.3.1(2) and 10.4.3.5(2), pp. 467 and 472–473, say that the kernel tensors of the
spectral convolution, summed over the rectangles of an arbitrary enumeration of the zeros,
converge in the completed projective tensor product. In `Sec4b` these statements are proved from
the trace-norm statements of §10.3 for single zeros, which rest on the recorded gap
`spectralStripConvolution_traceCauchy_compact_block_series` (#7241).

`Sec3_ClusterSums` proves the trace-norm statements for sums by clusters, without the gap. This
file draws from them the kernel statements for sums by clusters: the quotient tensors and the
ambient tensors on the line, the quotient tensors and the transposed tensors on the strip
(`spectralLineQuotientKernel_clusters_tendsto`, `spectralLineAmbientKernel_clusters_tendsto`,
`spectralStripQuotientKernel_clusters_tendsto`,
`spectralStripTransposedKernel_clusters_tendsto`).

The limits are identified. The limit of the quotient tensors is the kernel of the convolution
(`SpectralClusterSumsTraceTendsto.kernels_tendsto_to`). The limits of the ambient tensors on the
line and of the transposed tensors on the strip represent spectral projection after
convolution, as in Theorem 10.4.3.1(3) (`spectralLineAmbientKernel_clusters_operator`,
`spectralStripTransposedKernel_clusters_operator`).

Not treated: `spectralStripAmbientKernel_tendsto` of `Sec4b`, which assumes in addition that the
geometric-output components are Cauchy. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set UniformSpace
open scoped NNReal NumberField.AdeleRing TensorProduct Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

universe u

local notation "Π(" E ", " G ")" => Completion (ProjectiveTensor E G)

section FiniteTensors

variable {J E G : Type*} {Z : Type u}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Paper: (10.4.3.13)–(10.4.3.14), p. 467, and (10.4.3.42)–(10.4.3.43), p. 472. Sum the tensor
terms for all jets of the zeros in a finite set. `spectralKernelRectangle` of `Sec4b` is the case
of the rectangles of an enumeration. -/
def spectralKernelSum (K : Finset Z) (N : Z → ℕ)
    (jet : (z : Z) → Fin (N z) → J) (u : J → E) (v : J → G) : Π(E, G) :=
  ↑(∑ z ∈ K, ∑ m : Fin (N z), u (jet z m) ⊗ₜ[ℂ] v (jet z m) : ProjectiveTensor E G)

/-- The tensor sum over a rectangle of an enumeration is the tensor sum over the zeros that the
rectangle contains. -/
theorem spectralKernelRectangle_eq_spectralKernelSum {Z : Type*} (e : Z ↪ ℕ × ℕ) (N : Z → ℕ)
    (jet : (z : Z) → Fin (N z) → J) (u : J → E) (v : J → G) (ij : ℕ × ℕ) :
    spectralKernelRectangle e N jet u v ij = spectralKernelSum
      (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn) N jet u v :=
  rfl

/-- Paper: (10.4.3.13)–(10.4.3.14), p. 467, and (10.4.3.42)–(10.4.3.43), p. 472, for sums by
clusters. The zeros can be grouped into finite clusters `K i`, pairwise disjoint and covering
all the zeros, so that the tensor sums over finite unions of clusters converge in the completed
projective tensor product, along the finite sets of clusters ordered by inclusion.
Reconstruction: The paper does not state this. Its statement is for the rectangles of an
arbitrary enumeration of the single zeros (`spectralKernelRectangle` of `Sec4b`). Such a
rectangle can cut a cluster. The sums here do not. -/
def SpectralClusterKernelsTendsto (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (u : J → E) (v : J → G) : Prop :=
  ∃ (ι : Type u) (K : ι → Finset Z) (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)),
    (∀ z, ∃ i, z ∈ K i) ∧
    ∃ κ : Π(E, G), Tendsto (fun C : Finset ι ↦
      spectralKernelSum (C.disjiUnion K fun i _ j _ h ↦ hd i j h) N jet u v) atTop (𝓝 κ)

/-- Paper: (10.4.3.13)–(10.4.3.14), p. 467, and (10.4.3.42)–(10.4.3.43), p. 472, for sums by
clusters. `SpectralClusterKernelsTendsto` with the limit named: the tensor sums over finite
unions of clusters converge to `κ`. -/
def SpectralClusterKernelsTendstoTo (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (u : J → E) (v : J → G) (κ : Π(E, G)) : Prop :=
  ∃ (ι : Type u) (K : ι → Finset Z) (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)),
    (∀ z, ∃ i, z ∈ K i) ∧
    Tendsto (fun C : Finset ι ↦
      spectralKernelSum (C.disjiUnion K fun i _ j _ h ↦ hd i j h) N jet u v) atTop (𝓝 κ)

/-- The tensor sums by clusters converge exactly when they converge to some limit. -/
theorem spectralClusterKernelsTendsto_iff {N : Z → ℕ} {jet : (z : Z) → Fin (N z) → J}
    {u : J → E} {v : J → G} :
    SpectralClusterKernelsTendsto N jet u v ↔ ∃ κ, SpectralClusterKernelsTendstoTo N jet u v κ :=
  ⟨fun ⟨ι, K, hd, hc, κ, h⟩ ↦ ⟨κ, ι, K, hd, hc, h⟩, fun ⟨κ, ι, K, hd, hc, h⟩ ↦ ⟨ι, K, hd, hc, κ, h⟩⟩

/-- Continuous linear maps on the two factors carry convergent tensor sums by clusters to
convergent tensor sums by clusters, with the same clusters. -/
theorem SpectralClusterKernelsTendsto.map {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (d : E →L[ℂ] X) (j : G →L[ℂ] Y) {N : Z → ℕ} {jet : (z : Z) → Fin (N z) → J}
    {u : J → E} {v : J → G} (h : SpectralClusterKernelsTendsto N jet u v) :
    SpectralClusterKernelsTendsto N jet (fun z ↦ d (u z)) (fun z ↦ j (v z)) := by
  obtain ⟨ι, K, hd, hc, κ, hκ⟩ := h
  let L : ProjectiveTensor E G →L[ℂ] ProjectiveTensor X Y :=
    ⟨projectiveTensorMap d.toLinearMap j.toLinearMap, projectiveTensorMap_continuous d j⟩
  refine ⟨ι, K, hd, hc, L.completion κ,
    (L.completion.continuous.continuousAt.tendsto.comp hκ).congr fun C ↦ ?_⟩
  unfold Function.comp spectralKernelSum
  rw [ContinuousLinearMap.completion_apply_coe]
  apply congrArg ((↑) : ProjectiveTensor X Y → Π(X, Y))
  change projectiveTensorMap d.toLinearMap j.toLinearMap _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact (map_sum (TensorProduct.map d.toLinearMap j.toLinearMap)
    (fun m : Fin (N z) ↦ u (jet z m) ⊗ₜ[ℂ] v (jet z m)) Finset.univ).trans
    (Finset.sum_congr rfl fun m _ ↦ TensorProduct.map_tmul _ _ _ _)

/-- A limit of lifted biorthogonal sums by clusters recovers its prescribed quotient
coordinates: once a finite set of clusters contains the cluster of a zero, the coordinates at
the jets of that zero are those of the vector. This is the cluster form of the argument for
rectangles in `Sec4b`. -/
theorem spectralClusterSums_limit_eq {ι H V : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (q : V →L[ℂ] H) (S : H →L[ℂ] V) (hq : ∀ y, q (S y) = y)
    (N : Z → ℕ) (j : (z : Z) → Fin (N z) → J)
    (hj : Bijective (fun p : (z : Z) × Fin (N z) ↦ j p.1 p.2))
    (x : J → H) (f : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x f)
    (K : ι → Finset Z) (hd : ∀ a b, a ≠ b → Disjoint (K a) (K b)) (hc : ∀ z, ∃ a, z ∈ K a)
    (y : H) (w : V)
    (h : Tendsto (fun C : Finset ι ↦ ∑ z ∈ C.disjiUnion K fun a _ b _ hab ↦ hd a b hab,
      ∑ m : Fin (N z), f (j z m) y • S (x (j z m))) atTop (𝓝 w)) :
    w = S y := by
  classical
  let box (C : Finset ι) : Finset Z := C.disjiUnion K fun a _ b _ hab ↦ hd a b hab
  let b (C : Finset ι) := ∑ z ∈ box C, ∑ m : Fin (N z), f (j z m) y • x (j z m)
  have hS : Tendsto (fun C ↦ S (b C)) atTop (𝓝 w) := by
    simpa only [b, map_sum, map_smul] using h
  have hq' : Tendsto b atTop (𝓝 (q w)) := by
    simpa only [Function.comp_def, hq] using (q.continuous.tendsto w).comp hS
  have he : ContinuousLinearMap.apply ℂ ℂ (q w) = ContinuousLinearMap.apply ℂ ℂ y := by
    apply ContinuousLinearMap.ext_on hb.2.2.2
    rintro _ ⟨i, rfl⟩
    change f i (q w) = f i y
    apply tendsto_nhds_unique ((f i).continuous.continuousAt.tendsto.comp hq')
    apply tendsto_const_nhds.congr'
    obtain ⟨p, hp⟩ := hj.surjective i
    have hp' : j p.1 p.2 = i := hp
    obtain ⟨a₀, ha₀⟩ := hc p.1
    filter_upwards [eventually_ge_atTop ({a₀} : Finset ι)] with C hC
    have hmem : p.1 ∈ box C :=
      Finset.mem_disjiUnion.mpr ⟨a₀, hC (Finset.mem_singleton_self a₀), ha₀⟩
    change f i y = f i (b C)
    simp only [b, map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_sigma', Finset.sum_eq_single_of_mem p
      (Finset.mem_sigma.mpr ⟨hmem, Finset.mem_univ _⟩)]
    · change f i y = f (j p.1 p.2) y * f i (x (j p.1 p.2))
      rw [hp', hb.1, mul_one]
    · intro r _ hr
      change f (j r.1 r.2) y * f i (x (j r.1 r.2)) = 0
      rw [hb.2.1 _ i (fun h ↦ hr (hj.injective (h.trans hp'.symm))), mul_zero]
  have hqy : q w = y := (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    (fun ℓ ↦ DFunLike.congr_fun he ℓ)
  rw [← hqy]
  exact tendsto_nhds_unique hS ((S.continuous.tendsto _).comp hq')

end FiniteTensors

section TraceToKernels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The trace norm of a difference of nuclear endomorphisms. -/
private theorem traceNorm_sub_le (S T : nuclearEndomorphisms H) :
    traceNorm (S - T) ≤ traceNorm S + traceNorm T := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hcore := traceNorm_normedSpaceCore (H := H)
  have hneg : traceNorm (-T) = traceNorm T := by
    have h := hcore.norm_smul (-1 : ℂ) T
    rw [← neg_one_smul ℂ T]
    simpa only [norm_neg, norm_one, one_mul] using h
  rw [sub_eq_add_neg, ← hneg]
  exact hcore.norm_triangle S (-T)

/-- The operator norm of a nuclear endomorphism is at most its trace norm. -/
private theorem opNorm_le_traceNorm (T : nuclearEndomorphisms H) : ‖T.val‖ ≤ traceNorm T := by
  have hmem := (mem_traceClassOperators_iff_isNuclearOperator T.val).2 T.property
  have hsum : Summable (approximationNumber T.val) := by simpa using hmem.2
  have ht := schattenNorm_one_eq_traceNorm T
  simp only [schattenNorm, Real.rpow_one, div_one] at ht
  rw [← ht, ← approximationNumber_zero_eq_opNorm T.val hmem.1]
  exact hsum.le_tsum 0 fun n _ ↦ Real.sInf_nonneg fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _

/-- For given clusters, trace-norm convergence of the finite sections gives a limit of the
quotient kernel tensors, and that limit is the kernel of the operator. On algebraic tensors the
projective norm is the trace norm of the finite-rank operator
(`exists_projectiveTensorCompletion_traceClassIsometry`). -/
private theorem exists_kernel_limit_of_traceNorm_tendsto {J ι : Type*} {Z : Type u}
    (A : H →L[ℂ] H) (x : J → H) (f : J → StrongDual ℂ H) (N : Z → ℕ)
    (jet : (z : Z) → Fin (N z) → J)
    (K : ι → Finset Z) (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (T : Finset ι → nuclearEndomorphisms H)
    (hT : ∀ C, (T C).val = spectralConvolutionFiniteSum A x f
      (C.disjiUnion K fun i _ j _ h ↦ hd i j h) N jet - A)
    (hlim : Tendsto (fun C ↦ traceNorm (T C)) atTop (𝓝 0)) :
    ∃ κ : Π(StrongDual ℂ H, H), Tendsto (fun C : Finset ι ↦
      spectralKernelSum (C.disjiUnion K fun i _ j _ h ↦ hd i j h) N jet
        (fun j ↦ (f j).comp A) x) atTop (𝓝 κ) ∧
      completedProjectiveTensorToOperators κ = A := by
  classical
  let P := ProjectiveTensor (StrongDual ℂ H) H
  let box (C : Finset ι) : Finset Z := C.disjiUnion K fun i _ j _ h ↦ hd i j h
  let w (C : Finset ι) : P :=
    ∑ z ∈ box C, ∑ m : Fin (N z), (f (jet z m)).comp A ⊗ₜ[ℂ] x (jet z m)
  have hop (C) : tensorToFiniteRank (w C) = spectralConvolutionFiniteSum A x f (box C) N jet := by
    change tensorToFiniteRank
      (∑ z ∈ box C, ∑ m : Fin (N z), (f (jet z m)).comp A ⊗ₜ[ℂ] x (jet z m)) = _
    simp only [map_sum, spectralConvolutionFiniteSum]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro m _
    exact ContinuousLinearMap.ext fun y ↦ tensorToFiniteRank_tmul _ _ y
  obtain ⟨huc, equiv, hval, hnorm⟩ :=
    exists_projectiveTensorCompletion_traceClassIsometry (E := H) (F := H)
  have hcauchy : CauchySeq w := by
    apply (cauchySeq_iff_sub_mem w).mpr
    intro U hU
    obtain ⟨ε, hε, hball⟩ := spectralLineQuotientKernel_tendsto_gauge U hU
    obtain ⟨b, hb⟩ := eventually_atTop.mp ((tendsto_order.1 hlim).2 (ε / 2) (half_pos hε))
    refine ⟨b, fun j hj k hk ↦ hball _ ?_⟩
    have hD : (T j - T k).val = spectralConvolutionFiniteSum A x f (box j) N jet -
        spectralConvolutionFiniteSum A x f (box k) N jet := by
      change (T j).val - (T k).val = _
      rw [hT j, hT k, sub_sub_sub_cancel_right]
    have heq : (equiv ((w j - w k : P) : Completion P)).val = (T j - T k).val := by
      rw [hval, completedProjectiveTensorToOperators_coe]
      exact (map_sub tensorToFiniteRank (w j : StrongDual ℂ H ⊗[ℂ] H) (w k)).trans
        ((congrArg₂ (· - ·) (hop j) (hop k)).trans hD.symm)
    have hnorm' := (hnorm ((w j - w k : P) : Completion P)).trans (Completion.extension_coe huc _)
    have hsmall : traceNorm (T j - T k) < ε :=
      (traceNorm_sub_le (T j) (T k)).trans_lt (by linarith [hb j hj, hb k hk])
    exact hnorm'.symm.trans_lt ((congrArg schattenNorm (Subtype.ext heq)).trans_lt
      ((schattenNorm_one_eq_traceNorm (T j - T k)).trans_lt hsmall))
  obtain ⟨κ, hκ⟩ := cauchySeq_tendsto_of_complete
    (UniformContinuous.comp_cauchySeq (Completion.uniformContinuous_coe (α := P)) hcauchy)
  refine ⟨κ, hκ, ?_⟩
  have h1 : Tendsto (fun C ↦ completedProjectiveTensorToOperators ((w C : P) : Completion P))
      atTop (𝓝 (completedProjectiveTensorToOperators κ)) :=
    ((completedProjectiveTensorToOperators (E := H) (F := H)).continuous.tendsto κ).comp hκ
  have hz : Tendsto (fun C ↦ (T C).val) atTop (𝓝 0) :=
    squeeze_zero_norm (fun C ↦ opNorm_le_traceNorm (T C)) hlim
  have h2 : Tendsto (fun C ↦ completedProjectiveTensorToOperators ((w C : P) : Completion P))
      atTop (𝓝 A) := by
    have h := (tendsto_const_nhds (x := A)).add hz
    rw [add_zero] at h
    refine h.congr fun C ↦ ?_
    rw [completedProjectiveTensorToOperators_coe, hop, hT C, add_sub_cancel]
  exact tendsto_nhds_unique h1 h2

/-- Paper: Theorem 10.4.3.1(2), p. 467, and Theorem 10.4.3.5(2), pp. 472–473, for sums by
clusters. If the finite sections of `A` over finite unions of clusters converge to `A` in trace
norm, the quotient kernel tensors summed over the same unions of clusters converge in the
completed projective tensor product. -/
theorem SpectralClusterSumsTraceTendsto.kernels_tendsto {J : Type*} {Z : Type u}
    {A : H →L[ℂ] H} {x : J → H} {f : J → StrongDual ℂ H} {N : Z → ℕ}
    {jet : (z : Z) → Fin (N z) → J} (h : SpectralClusterSumsTraceTendsto A x f N jet) :
    SpectralClusterKernelsTendsto N jet (fun j ↦ (f j).comp A) x := by
  obtain ⟨ι, K, hd, hc, T, hT, hlim⟩ := h
  obtain ⟨κ, hκ, -⟩ := exists_kernel_limit_of_traceNorm_tendsto A x f N jet K hd T hT hlim
  exact ⟨ι, K, hd, hc, κ, hκ⟩

/-- Paper: Theorem 10.4.3.1(2)–(3), p. 467, and Theorem 10.4.3.5(2)–(3), pp. 472–473, for the
quotient kernel and sums by clusters. The limit of the quotient kernel tensors summed by
clusters is the kernel of the operator: the canonical map to operators sends it to `A`. -/
theorem SpectralClusterSumsTraceTendsto.kernels_tendsto_to {J : Type*} {Z : Type u}
    {A : H →L[ℂ] H} {x : J → H} {f : J → StrongDual ℂ H} {N : Z → ℕ}
    {jet : (z : Z) → Fin (N z) → J} (h : SpectralClusterSumsTraceTendsto A x f N jet) :
    ∃ κ : Π(StrongDual ℂ H, H),
      SpectralClusterKernelsTendstoTo N jet (fun j ↦ (f j).comp A) x κ ∧
      completedProjectiveTensorToOperators κ = A := by
  obtain ⟨ι, K, hd, hc, T, hT, hlim⟩ := h
  obtain ⟨κ, hκ, hop⟩ := exists_kernel_limit_of_traceNorm_tendsto A x f N jet K hd T hT hlim
  exact ⟨κ, ⟨ι, K, hd, hc, hκ⟩, hop⟩

end TraceToKernels

variable {F : Type u} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (logIdeleClassNorm F)
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => (le_of_lt (zero_lt_one.trans hs))
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s
local notation "W'(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s true
local notation "Θ(" a ", " hα ", " hs ")" => globalThetaSobolev F a (hStrip(hα)) hs
local notation "H(" a ", " hα ", " hs ")" => spectralSobolevQuotient F a (hStrip(hα)) hs
local notation "S(" a ", " hα ", " hs ")" =>
  (fun u : H(a, hα, hs) ↦
    ((Θ(a, hα, hs)).quotientEquivOrthogonal u).val)
local notation "Aq(" a ", " hα ", " hs ", " φ ")" =>
  spectralConvolution (F := F) a (hStrip(hα)) hs φ
local notation "Q(" a ", " hα ", " hs ")" => (Θ(a, hα, hs)).mkQL
local notation "A(" hα ", " hs ", " φ ")" =>
  hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (hStrip(hα)) hs φ
local notation "Pspec(" a ", " hα ", " hs ")" => spectralProjection (F := F) a hα hs

/-- Evaluation of an ambient kernel sum over a finite set of zeros is the finite sum of its
rank-one actions. -/
private theorem sobolevProjectiveKernelOperator_spectralKernelSum {Z : Type u} {J : Type*}
    {α s : ℝ} (a : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (K : Finset Z) (N : Z → ℕ)
    (j : (z : Z) → Fin (N z) → J) (f : J → StrongDual ℂ H(a, hα, hs))
    (y : J → W(α, s)) (v : W(α, s)) :
    sobolevProjectiveKernelOperator (F := F) hα hs
      (spectralKernelSum K N j
        (fun k ↦ spectralSobolevDualEmbedding F a (hStrip(hα)) hs (f k)) y) v =
      ∑ z ∈ K, ∑ m : Fin (N z), f (j z m) (Q(a, hα, hs) v) • y (j z m) := by
  let M := (((ContinuousLinearMap.apply ℂ (W(α, s)) v).comp
    (sobolevProjectiveKernelOperator (F := F) hα hs)).comp
    (Completion.toComplL : ProjectiveTensor W'(α, s) W(α, s) →L[ℂ] _))
  change M _ = _
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  let term (m : Fin (N z)) : ProjectiveTensor W'(α, s) W(α, s) :=
    spectralSobolevDualEmbedding F a (hStrip(hα)) hs (f (j z m)) ⊗ₜ[ℂ] y (j z m)
  refine (map_sum M term Finset.univ).trans (Finset.sum_congr rfl ?_)
  intro m _
  apply (sobolevProjectiveKernelOperator_tmul hα hs _ _ v).trans
  exact congrArg (fun c : ℂ ↦ c • y (j z m))
    (spectralSobolevPairing_dual (hStrip(hα)) hs ((f (j z m)).comp (Q(a, hα, hs))) v).2.symm

section LineTensors

variable (a : ℝ) {s : ℝ} (hs : 1 < s)

local notation "S₀" => (fun u : H(a, (le_refl (0 : ℝ)), hs₀(hs)) ↦
  ((Θ(a, (le_refl (0 : ℝ)), hs₀(hs))).quotientEquivOrthogonal u : W(0, s)))
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat
local notation "Z(" χ ")" => {z : PontryaginDual C₁ × ℝ // 0 < order(χ z.1, shift(a, z.2))}
local notation "N(" χ ", " z ")" => spectralBoundaryMultiplicity s (mult(χ (z).val.1,
  shift(a, (z).val.2)))
local notation "jet" => (fun z m ↦ ⟨(z.val.1, z.val.2, m.val), m.isLt⟩)
local notation "Aq₀(" φ ")" => Aq(a, (le_refl (0 : ℝ)), hs₀(hs), φ)
local notation "A₀(" φ ")" => A((le_refl (0 : ℝ)), hs₀(hs), φ)
local notation "D₀" => spectralSobolevDualEmbedding F a
  (hStrip(le_refl (0 : ℝ))) hs₀(hs)
local notation "Bases₀(" χ ", " x ", " f ")" => (IsSpectralMarkushevichBasis x f ∧
  ∀ j, D₀ (f j) =
    cast (congrArg (fun l : ℝ ↦ CompactIntervalSobolev μ𝔽 logNorm l 0 s true) neg_zero.symm)
      ((spectralLineJet_memLp χ hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2)))

/-- Transport the line statement for sums by clusters from the endpoint zero to an equal
endpoint. -/
private theorem spectralLineConvolution_clusters_traceNorm_tendsto_endpoint
    {F : Type u} [Field F] [NumberField F] (a : ℝ) {s : ℝ} (hs : 1 < s)
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (hχ : IsSpectralBasepointChoice χ)
    (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)) (l : ℝ) (hl : 0 = l) (hI : l ≤ 0)
    (x' : SpectralLineJetIndex χ a s → spectralSobolevQuotient F a hI hs₀(hs))
    (f' : SpectralLineJetIndex χ a s → StrongDual ℂ (spectralSobolevQuotient F a hI hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x' f')
    (hj : ∀ j, spectralSobolevDualEmbedding F a hI hs₀(hs) (f' j) =
      cast (congrArg (fun r : ℝ ↦ CompactIntervalSobolev (ideleClassTamagawaMeasure F)
        (fun g ↦ Real.log ((ideleClassNorm F g).val : ℝ)) r 0 s true) hl)
        ((spectralLineJet_memLp χ hs j).toLp
          (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2))) :
    SpectralClusterSumsTraceTendsto (spectralConvolution (F := F) a hI hs₀(hs) φ) x' f'
      (fun z : {z : PontryaginDual (ideleClassNorm F).ker × ℝ //
        0 < order(χ z.1, shift(a, z.2))} ↦
        spectralBoundaryMultiplicity s (mult(χ z.val.1, shift(a, z.val.2)))) jet := by
  subst l
  exact spectralLineConvolution_clusters_traceNorm_tendsto (F := F) a χ hχ hs φ x' f' hb hj

/-- Paper: Theorem 10.4.3.1(2), p. 467, equation (10.4.3.13), with the zeros summed by
clusters. The quotient kernel tensors summed over finite unions of clusters converge in the
completed projective tensor product. It is proved from
`spectralLineConvolution_clusters_traceNorm_tendsto`, so it does not use the recorded gap #7241.
Reconstruction: The paper does not state this. `spectralLineQuotientKernel_tendsto` of `Sec4b`
is its statement for the rectangles of an enumeration of the single zeros, and rests on the gap. -/
theorem spectralLineQuotientKernel_clusters_tendsto
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : SpectralLineJetIndex χ a s → H(a, (le_refl (0 : ℝ)), hs₀(hs)))
    (f : SpectralLineJetIndex χ a s → StrongDual ℂ H(a, (le_refl (0 : ℝ)), hs₀(hs)))
    (hχ : IsSpectralBasepointChoice χ) (hb : Bases₀(χ, x, f)) (φ : BruhatCompactSupport C𝔽) :
    SpectralClusterKernelsTendsto (fun z : Z(χ) ↦ N(χ, z)) jet
      (fun j ↦ (f j).comp (Aq₀(φ))) x :=
  (spectralLineConvolution_clusters_traceNorm_tendsto_endpoint a hs χ hχ φ _ neg_zero.symm _
    x f hb.1 hb.2).kernels_tendsto

/-- Paper: Theorem 10.4.3.1(2), p. 467, equation (10.4.3.14), with the zeros summed by
clusters. The ambient kernel tensors summed over finite unions of clusters converge in the
completed projective tensor product. It does not use the recorded gap #7241.
Reconstruction: The paper does not state this. `spectralLineAmbientKernel_tendsto` of `Sec4b`
is its statement for the rectangles of an enumeration. -/
theorem spectralLineAmbientKernel_clusters_tendsto
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : SpectralLineJetIndex χ a s → H(a, (le_refl (0 : ℝ)), hs₀(hs)))
    (f : SpectralLineJetIndex χ a s → StrongDual ℂ H(a, (le_refl (0 : ℝ)), hs₀(hs)))
    (hχ : IsSpectralBasepointChoice χ) (hb : Bases₀(χ, x, f)) (φ : BruhatCompactSupport C𝔽) :
    SpectralClusterKernelsTendsto (fun z : Z(χ) ↦ N(χ, z)) jet
      (fun j ↦ D₀ ((f j).comp (Aq₀(φ)))) (fun j ↦ S₀ (x j)) := by
  let E := H(a, (le_refl (0 : ℝ)), hs₀(hs))
  let θ := Θ(a, (le_refl (0 : ℝ)), hs₀(hs))
  let d : StrongDual ℂ E →L[ℂ] W'(0, s) := ⟨D₀,
    (spectralSobolevDualEmbedding_isometry_range (F := F) a (hStrip((le_refl (0 : ℝ))))
      hs₀(hs)).1.continuous⟩
  let j : E →L[ℂ] W(0, s) := θ.orthogonal.subtypeL.comp
    θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  exact (spectralLineQuotientKernel_clusters_tendsto (F := F) a hs χ x f hχ hb φ).map d j

-- The statement and its packaging are on the concrete Sobolev quotient, as in `Sec4b`.
set_option maxHeartbeats 400000 in
/-- Paper: Theorem 10.4.3.1(3), p. 467, with the zeros summed by clusters. The ambient kernel
tensors summed over finite unions of clusters converge to a kernel that represents spectral
projection after convolution. It does not use the recorded gap #7241.
Reconstruction: The paper does not state this. `spectralLineAmbientKernel_operator` of `Sec4b`
is its statement for a limit along the rectangles of an enumeration. -/
theorem spectralLineAmbientKernel_clusters_operator
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : SpectralLineJetIndex χ a s → H(a, (le_refl (0 : ℝ)), hs₀(hs)))
    (f : SpectralLineJetIndex χ a s → StrongDual ℂ H(a, (le_refl (0 : ℝ)), hs₀(hs)))
    (hχ : IsSpectralBasepointChoice χ) (hb : Bases₀(χ, x, f)) (φ : BruhatCompactSupport C𝔽) :
    ∃ κ : Π(W'(0, s), W(0, s)),
      SpectralClusterKernelsTendstoTo (fun z : Z(χ) ↦ N(χ, z)) jet
        (fun j ↦ D₀ ((f j).comp (Aq₀(φ)))) (fun j ↦ S₀ (x j)) κ ∧
      sobolevProjectiveKernelOperator (F := F) (le_refl (0 : ℝ)) hs₀(hs) κ =
        (Pspec(a, (le_refl (0 : ℝ)), hs₀(hs))).comp (A₀(φ)) := by
  obtain ⟨ι, K, hd, hc, κ, hκ⟩ :=
    spectralLineAmbientKernel_clusters_tendsto (F := F) a hs χ x f hχ hb φ
  refine ⟨κ, ⟨ι, K, hd, hc, hκ⟩, ?_⟩
  let θ := Θ(a, (le_refl (0 : ℝ)), hs₀(hs))
  let lift := θ.orthogonal.subtypeL.comp
    θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  have hsection (u) : θ.mkQL (lift u) = u :=
    (θ.quotientEquivOrthogonal_symm_eq_mk _ (θ.quotientEquivOrthogonal u).property).symm.trans
      (θ.quotientEquivOrthogonal.symm_apply_apply u)
  let key (z : Z(χ)) (m : Fin N(χ, z)) : SpectralLineJetIndex χ a s :=
    ⟨(z.val.1, z.val.2, m.val), m.isLt⟩
  let index : ((z : Z(χ)) × Fin N(χ, z)) ≃ SpectralLineJetIndex χ a s :=
    ⟨fun p ↦ key p.1 p.2,
      fun j ↦ ⟨⟨(j.val.1, j.val.2.1), SpectralLineJetIndex.order_pos j⟩, ⟨j.val.2.2, j.property⟩⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
  apply Eq.trans _
    (spectralProjection_convolution_factor (F := F) a (le_refl (0 : ℝ)) hs₀(hs) φ).symm
  apply ContinuousLinearMap.ext
  intro v
  apply spectralClusterSums_limit_eq θ.mkQL lift hsection (fun z : Z(χ) ↦ N(χ, z)) key
    index.bijective x f hb.1 K hd hc ((Aq₀(φ)) (θ.mkQL v))
  let ev := (ContinuousLinearMap.apply ℂ (W(0, s)) v).comp
    (sobolevProjectiveKernelOperator (F := F) (le_refl (0 : ℝ)) hs₀(hs))
  refine ((ev.continuous.tendsto κ).comp hκ).congr fun C ↦ ?_
  exact sobolevProjectiveKernelOperator_spectralKernelSum a (le_refl (0 : ℝ)) hs₀(hs) _
    (fun z : Z(χ) ↦ N(χ, z)) key (fun j ↦ (f j).comp (Aq₀(φ))) (fun j ↦ lift (x j)) v

end LineTensors

section StripTensors

variable (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
  (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))

local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat
local notation "Z(" χ ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))
local notation "jet(" z ", " m ")" => ⟨((z).val.1, (z).val.2.1, (z).val.2.2, (m).val), (m).isLt⟩
local notation "D" => spectralSobolevDualEmbedding F a (hStrip(hα)) hs₀(hs)
local notation "Bases(" χ ", " x ", " f ")" => (IsSpectralMarkushevichBasis x f ∧
  ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp
    (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))

/-- Paper: Theorem 10.4.3.5(2), pp. 472–473, equation (10.4.3.42), with the zeros summed by
clusters. The quotient tensors summed over finite unions of clusters converge in the completed
projective tensor topology. It is proved from
`spectralStripConvolution_clusters_traceNorm_tendsto`, so it does not use the recorded gap
#7241.
Reconstruction: The paper does not state this. `spectralStripQuotientKernel_tendsto` of `Sec4b`
is its statement for the rectangles of an enumeration of the single zeros, and rests on the gap. -/
theorem spectralStripQuotientKernel_clusters_tendsto
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (hχ : IsSpectralBasepointChoice χ) (hb : Bases(χ, x, f)) :
    SpectralClusterKernelsTendsto (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m))
      (fun j ↦ (f j).comp (Aq(a, hα, hs₀(hs), φ))) x :=
  (spectralStripConvolution_clusters_traceNorm_tendsto (F := F) a hα hs₀(hs) φ χ hχ x f
    hb.1 hb.2).kernels_tendsto

/-- Paper: Theorem 10.4.3.5(2), pp. 472–473, equation (10.4.3.43), with the zeros summed by
clusters. The ambient tensors with convolution transposed onto the input factor, summed over
finite unions of clusters, converge in the projective topology. It does not use the recorded
gap #7241.
Reconstruction: The paper does not state this. `spectralStripTransposedKernel_tendsto` of
`Sec4b` is its statement for the rectangles of an enumeration. -/
theorem spectralStripTransposedKernel_clusters_tendsto
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (hχ : IsSpectralBasepointChoice χ) (hb : Bases(χ, x, f)) :
    SpectralClusterKernelsTendsto (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m))
      (fun j ↦ D ((f j).comp (Aq(a, hα, hs₀(hs), φ))))
      (fun j ↦ S(a, hα, hs₀(hs)) (x j)) := by
  let E := H(a, hα, hs₀(hs))
  let θ := Θ(a, hα, hs₀(hs))
  let d : StrongDual ℂ E →L[ℂ] W'(α, s) := ⟨D,
    (spectralSobolevDualEmbedding_isometry_range (F := F) a (hStrip(hα)) hs₀(hs)).1.continuous⟩
  let j : E →L[ℂ] W(α, s) := θ.orthogonal.subtypeL.comp
    θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  exact (spectralStripQuotientKernel_clusters_tendsto (F := F) a hα hs φ χ x f hχ hb).map d j

-- The statement and its packaging are on the concrete Sobolev quotient, as in `Sec4b`.
set_option maxHeartbeats 400000 in
/-- Paper: Theorem 10.4.3.5(2)–(3), pp. 472–473, with the zeros summed by clusters. The
transposed tensors of (10.4.3.43) summed over finite unions of clusters converge to a kernel
that represents spectral projection after convolution, as on the line. It does not use the
recorded gap #7241.
Reconstruction: The paper does not state this. Its identity (10.4.3.45) has convolution after
projection, which `Sec4b` attaches to the ambient tensors with convolution on the output factor
(`spectralStripAmbientKernel_operator`). -/
theorem spectralStripTransposedKernel_clusters_operator
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (hχ : IsSpectralBasepointChoice χ) (hb : Bases(χ, x, f)) :
    ∃ κ : Π(W'(α, s), W(α, s)),
      SpectralClusterKernelsTendstoTo (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m))
        (fun j ↦ D ((f j).comp (Aq(a, hα, hs₀(hs), φ))))
        (fun j ↦ S(a, hα, hs₀(hs)) (x j)) κ ∧
      sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) κ =
        (Pspec(a, hα, hs₀(hs))).comp (A(hα, hs₀(hs), φ)) := by
  obtain ⟨ι, K, hd, hc, κ, hκ⟩ :=
    spectralStripTransposedKernel_clusters_tendsto (F := F) a hα hs φ χ x f hχ hb
  refine ⟨κ, ⟨ι, K, hd, hc, hκ⟩, ?_⟩
  let θ := Θ(a, hα, hs₀(hs))
  let lift := θ.orthogonal.subtypeL.comp
    θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  have hsection (u) : θ.mkQL (lift u) = u :=
    (θ.quotientEquivOrthogonal_symm_eq_mk _ (θ.quotientEquivOrthogonal u).property).symm.trans
      (θ.quotientEquivOrthogonal.symm_apply_apply u)
  let key (z : Z(χ)) (m : Fin N(χ, z)) : SpectralStripJetIndex χ a α s := jet(z, m)
  let index : ((z : Z(χ)) × Fin N(χ, z)) ≃ SpectralStripJetIndex χ a α s :=
    ⟨fun p ↦ key p.1 p.2,
      fun j ↦ ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1),
        SpectralStripJetIndex.mem_strip_order_pos hα j⟩, ⟨j.val.2.2.2, j.property⟩⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
  apply Eq.trans _ (spectralProjection_convolution_factor (F := F) a hα hs₀(hs) φ).symm
  apply ContinuousLinearMap.ext
  intro v
  apply spectralClusterSums_limit_eq θ.mkQL lift hsection (fun z : Z(χ) ↦ N(χ, z)) key
    index.bijective x f hb.1 K hd hc ((Aq(a, hα, hs₀(hs), φ)) (θ.mkQL v))
  let ev := (ContinuousLinearMap.apply ℂ (W(α, s)) v).comp
    (sobolevProjectiveKernelOperator (F := F) hα hs₀(hs))
  refine ((ev.continuous.tendsto κ).comp hκ).congr fun C ↦ ?_
  exact sobolevProjectiveKernelOperator_spectralKernelSum a hα hs₀(hs) _
    (fun z : Z(χ) ↦ N(χ, z)) key (fun j ↦ (f j).comp (Aq(a, hα, hs₀(hs), φ)))
    (fun j ↦ lift (x j)) v

end StripTensors

end RiemannMasullo
