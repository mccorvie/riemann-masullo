module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_ClusterKernels
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_ProjectedKernels
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # The geometric part of Theorem 10.4.3.5 with the zeros summed by clusters

Theorem 10.4.3.5(2)–(3), pp. 472–473, takes the ambient kernel tensors of the strip to converge
to a kernel of convolution after spectral projection, the operator `A(φ) ∘ P^spec` of
(10.4.3.45). The printed tensors (10.4.3.43) carry the convolution on the input factor; summed
by clusters they converge to a kernel of `P^spec ∘ A(φ)`
(`spectralStripTransposedKernel_clusters_operator` of `Sec4b_ClusterKernels`). The operator
order of (10.4.3.45) needs the convolution on the output factor, and then each tensor has a
component in the theta subspace, its geometric component, for which the paper gives no estimate
(`spectralStripGeometricKernel_blocks_bddAbove` of `Sec4b_Isolated`).

This file collects what holds for the geometric component with no estimate.

* The two operators differ by `P^geom ∘ A(φ) ∘ P^spec`, the commutator of the convolution with
  the spectral projection (`stripTestAction_comp_spectralProjection_sub`). It is nuclear and has
  a projective kernel (`geometricProjection_stripTestAction_spectralProjection_nuclear`,
  `geometricProjection_stripTestAction_spectralProjection_has_projectiveKernel`).
* A limit of the ambient tensors summed by clusters, if there is one, represents
  `A(φ) ∘ P^spec` (`spectralStripAmbientKernel_clusters_operator`).
* For a test split in two, with one convolution on the input factor and the other on the output
  factor, the tensors summed by clusters converge, and the limit represents
  `A(φ) ∘ P^spec ∘ A(ψ)` (`spectralStripSplitKernel_clusters_operator`); so do their geometric
  components (`spectralStripSplitGeometricKernel_clusters_operator`).
* For suitable clusters, the ambient tensors summed by clusters converge exactly when their
  geometric components do, and the limits are then kernels of `A(φ) ∘ P^spec` and of the
  commutator (`spectralStripAmbientKernel_clusters_tendsto_iff_geometric`).

`Sec4b_Isolated` shows that bounded trace norms of the geometric cluster sums suffice for that
convergence. Whether they are bounded is open. -/

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

variable {J E G Y : Type*} {Z : Type u}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The map of completed projective tensor products given by a continuous linear map on the
output factor. On the kernel side it is composition of the operator with that map
(`sobolevProjectiveKernelOperator_mapOutput`). -/
def projectiveKernelMapOutput (B : G →L[ℂ] Y) : Π(E, G) →L[ℂ] Π(E, Y) :=
  (⟨projectiveTensorMap (ContinuousLinearMap.id ℂ E).toLinearMap B.toLinearMap,
    projectiveTensorMap_continuous (ContinuousLinearMap.id ℂ E) B⟩ :
      ProjectiveTensor E G →L[ℂ] ProjectiveTensor E Y).completion

/-- On an algebraic tensor the output map is the algebraic map of tensors. -/
theorem projectiveKernelMapOutput_coe (B : G →L[ℂ] Y) (t : ProjectiveTensor E G) :
    projectiveKernelMapOutput B (t : Π(E, G)) =
      ((projectiveTensorMap (ContinuousLinearMap.id ℂ E).toLinearMap B.toLinearMap t :
        ProjectiveTensor E Y) : Π(E, Y)) :=
  ContinuousLinearMap.completion_apply_coe _ t

/-- The tensor sums over the finite unions of given clusters `K i`, pairwise disjoint, converge
to `κ` in the completed projective tensor product, along the finite sets of clusters ordered by
inclusion. `SpectralClusterKernelsTendstoTo` of `Sec4b_ClusterKernels` says that such clusters
exist and cover the zeros. -/
def SpectralKernelSumsTendstoAlong {ι : Type*} (K : ι → Finset Z)
    (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (u : J → E) (v : J → G) (κ : Π(E, G)) : Prop :=
  Tendsto (fun C : Finset ι ↦
    spectralKernelSum (C.disjiUnion K fun i _ j _ h ↦ hd i j h) N jet u v) atTop (𝓝 κ)

/-- Convergence of the tensor sums by clusters to a named limit, with the clusters named. -/
theorem spectralClusterKernelsTendstoTo_iff_along {N : Z → ℕ} {jet : (z : Z) → Fin (N z) → J}
    {u : J → E} {v : J → G} {κ : Π(E, G)} :
    SpectralClusterKernelsTendstoTo N jet u v κ ↔
      ∃ (ι : Type u) (K : ι → Finset Z) (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)),
        (∀ z, ∃ i, z ∈ K i) ∧ SpectralKernelSumsTendstoAlong K hd N jet u v κ :=
  Iff.rfl

/-- Splitting each output vector splits the kernel sum. -/
theorem spectralKernelSum_add (K : Finset Z) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (u : J → E) (v w : J → G) :
    spectralKernelSum K N jet u (fun k ↦ v k + w k) =
      spectralKernelSum K N jet u v + spectralKernelSum K N jet u w := by
  unfold spectralKernelSum
  rw [← Completion.coe_add]
  apply congrArg ((↑) : ProjectiveTensor E G → Π(E, G))
  change (∑ z ∈ K, ∑ m, u (jet z m) ⊗ₜ[ℂ] (v (jet z m) + w (jet z m)) : E ⊗[ℂ] G) =
    (∑ z ∈ K, ∑ m, u (jet z m) ⊗ₜ[ℂ] v (jet z m)) + ∑ z ∈ K, ∑ m, u (jet z m) ⊗ₜ[ℂ] w (jet z m)
  simp only [TensorProduct.tmul_add, Finset.sum_add_distrib]

/-- A continuous linear map on the output factor, applied to a kernel sum, acts on each output
vector. -/
theorem projectiveKernelMapOutput_spectralKernelSum (B : G →L[ℂ] Y) (K : Finset Z) (N : Z → ℕ)
    (jet : (z : Z) → Fin (N z) → J) (u : J → E) (v : J → G) :
    projectiveKernelMapOutput B (spectralKernelSum K N jet u v) =
      spectralKernelSum K N jet u (fun k ↦ B (v k)) := by
  unfold projectiveKernelMapOutput spectralKernelSum
  rw [ContinuousLinearMap.completion_apply_coe]
  apply congrArg ((↑) : ProjectiveTensor E Y → Π(E, Y))
  change projectiveTensorMap (ContinuousLinearMap.id ℂ E).toLinearMap B.toLinearMap _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact (map_sum (TensorProduct.map (ContinuousLinearMap.id ℂ E).toLinearMap B.toLinearMap)
    (fun m : Fin (N z) ↦ u (jet z m) ⊗ₜ[ℂ] v (jet z m)) Finset.univ).trans
    (Finset.sum_congr rfl fun m _ ↦ TensorProduct.map_tmul _ _ _ _)

/-- A continuous linear map on the output factor carries a limit of kernel sums along given
clusters to the limit of the kernel sums with the mapped outputs. -/
theorem SpectralKernelSumsTendstoAlong.mapOutput (B : G →L[ℂ] Y) {ι : Type*} {K : ι → Finset Z}
    {hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)} {N : Z → ℕ}
    {jet : (z : Z) → Fin (N z) → J} {u : J → E} {v : J → G} {κ : Π(E, G)}
    (h : SpectralKernelSumsTendstoAlong K hd N jet u v κ) :
    SpectralKernelSumsTendstoAlong K hd N jet u (fun k ↦ B (v k))
      (projectiveKernelMapOutput B κ) :=
  (((projectiveKernelMapOutput (E := E) B).continuous.tendsto κ).comp h).congr fun _ ↦
    projectiveKernelMapOutput_spectralKernelSum B _ N jet u v

/-- A continuous linear map on the output factor carries a limit of kernel sums by clusters to
the limit of the kernel sums with the mapped outputs, with the same clusters. -/
theorem SpectralClusterKernelsTendstoTo.mapOutput (B : G →L[ℂ] Y) {N : Z → ℕ}
    {jet : (z : Z) → Fin (N z) → J} {u : J → E} {v : J → G} {κ : Π(E, G)}
    (h : SpectralClusterKernelsTendstoTo N jet u v κ) :
    SpectralClusterKernelsTendstoTo N jet u (fun k ↦ B (v k)) (projectiveKernelMapOutput B κ) := by
  obtain ⟨ι, K, hd, hc, hκ⟩ := h
  exact ⟨ι, K, hd, hc, SpectralKernelSumsTendstoAlong.mapOutput B hκ⟩

/-- If every finite tensor sum splits as a sum of two tensor sums, and the second sums converge
along given clusters, then the first sums converge along these clusters exactly when the total
sums do, and the limits add. -/
theorem spectralKernelSumsTendstoAlong_add_iff {ι : Type*} (K : ι → Finset Z)
    (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (u : J → E) (v g : J → G) (u' : J → E) (t : J → G) (κT : Π(E, G))
    (hdec : ∀ K₀ : Finset Z, spectralKernelSum K₀ N jet u v =
      spectralKernelSum K₀ N jet u g + spectralKernelSum K₀ N jet u' t)
    (hT : SpectralKernelSumsTendstoAlong K hd N jet u' t κT) (κ : Π(E, G)) :
    SpectralKernelSumsTendstoAlong K hd N jet u g κ ↔
      SpectralKernelSumsTendstoAlong K hd N jet u v (κ + κT) := by
  unfold SpectralKernelSumsTendstoAlong at hT ⊢
  constructor
  · intro hg
    exact (hg.add hT).congr fun C ↦ (hdec _).symm
  · intro ha
    have h := (ha.sub hT).congr fun C ↦ sub_eq_of_eq_add (hdec _)
    rwa [add_sub_cancel_right] at h

/-- A limit of the ambient sums by clusters is the operator on lifted inputs: on the lift of a
biorthogonal vector the sums are constant once the cluster of its zero is included, and the
biorthogonal vectors are total. This is the cluster form of the argument for rectangles in
`Sec4b`. -/
theorem spectralClusterAmbientSums_limit_eq {ι H V : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (q : V →L[ℂ] H) (S : H →L[ℂ] V) (hq : ∀ y, q (S y) = y) (A T : V →L[ℂ] V)
    (N : Z → ℕ) (j : (z : Z) → Fin (N z) → J)
    (hj : Bijective (fun p : (z : Z) × Fin (N z) ↦ j p.1 p.2))
    (x : J → H) (f : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x f)
    (K : ι → Finset Z) (hd : ∀ a b, a ≠ b → Disjoint (K a) (K b)) (hc : ∀ z, ∃ a, z ∈ K a)
    (h : ∀ v, Tendsto (fun C : Finset ι ↦ ∑ z ∈ C.disjiUnion K fun a _ b _ hab ↦ hd a b hab,
      ∑ m : Fin (N z), f (j z m) (q v) • A (S (x (j z m)))) atTop (𝓝 (T v))) :
    ∀ v, T v = A (S (q v)) := by
  classical
  let box (C : Finset ι) : Finset Z := C.disjiUnion K fun a _ b _ hab ↦ hd a b hab
  have hlift : T.comp S = A.comp S := by
    apply ContinuousLinearMap.ext_on hb.2.2.1
    rintro _ ⟨i, rfl⟩
    apply tendsto_nhds_unique (h (S (x i)))
    apply tendsto_const_nhds.congr'
    obtain ⟨p, hp⟩ := hj.surjective i
    have hp' : j p.1 p.2 = i := hp
    obtain ⟨a₀, ha₀⟩ := hc p.1
    filter_upwards [eventually_ge_atTop ({a₀} : Finset ι)] with C hC
    have hmem : p.1 ∈ box C :=
      Finset.mem_disjiUnion.mpr ⟨a₀, hC (Finset.mem_singleton_self a₀), ha₀⟩
    change A (S (x i)) = ∑ z ∈ box C, ∑ m : Fin (N z), f (j z m) (q (S (x i))) • A (S (x (j z m)))
    simp only [hq]
    rw [Finset.sum_sigma', Finset.sum_eq_single_of_mem p
      (Finset.mem_sigma.mpr ⟨hmem, Finset.mem_univ _⟩)]
    · change A (S (x i)) = f (j p.1 p.2) (x i) • A (S (x (j p.1 p.2)))
      rw [hp', hb.1, one_smul]
    · intro r _ hr
      change f (j r.1 r.2) (x i) • A (S (x (j r.1 r.2))) = 0
      rw [hb.2.1 i _ (fun h ↦ hr (hj.injective (hp'.trans h).symm)), zero_smul]
  intro v
  have hv := h (S (q v))
  simp only [hq] at hv
  exact (tendsto_nhds_unique (h v) hv).trans (DFunLike.congr_fun hlift (q v))

/-- The kernel composite of `sobolevProjectiveKernelOperator`, for general normed spaces: a
bounded operator on the output factor composes with the operator of the kernel. -/
private theorem kernelOperator_mapOutput_aux {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] (e : StrongDual ℂ V ≃ₗᵢ[ℂ] X) (B : V →L[ℂ] V)
    (κ : Completion (ProjectiveTensor X V)) :
    (completedProjectiveTensorToOperators.comp
      (⟨projectiveTensorMap e.symm.toContinuousLinearEquiv.toContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.id ℂ V).toLinearMap,
        projectiveTensorMap_continuous e.symm.toContinuousLinearEquiv.toContinuousLinearMap
          (ContinuousLinearMap.id ℂ V)⟩ :
          ProjectiveTensor X V →L[ℂ] ProjectiveTensor (StrongDual ℂ V) V).completion)
      (projectiveKernelMapOutput B κ) =
    B.comp ((completedProjectiveTensorToOperators.comp
      (⟨projectiveTensorMap e.symm.toContinuousLinearEquiv.toContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.id ℂ V).toLinearMap,
        projectiveTensorMap_continuous e.symm.toContinuousLinearEquiv.toContinuousLinearMap
          (ContinuousLinearMap.id ℂ V)⟩ :
          ProjectiveTensor X V →L[ℂ] ProjectiveTensor (StrongDual ℂ V) V).completion) κ) := by
  let i : ProjectiveTensor X V →L[ℂ] ProjectiveTensor (StrongDual ℂ V) V :=
    ⟨projectiveTensorMap e.symm.toContinuousLinearEquiv.toContinuousLinearMap.toLinearMap
        (ContinuousLinearMap.id ℂ V).toLinearMap,
      projectiveTensorMap_continuous e.symm.toContinuousLinearEquiv.toContinuousLinearMap
        (ContinuousLinearMap.id ℂ V)⟩
  let ξ : Completion (ProjectiveTensor X V) →L[ℂ] (V →L[ℂ] V) :=
    completedProjectiveTensorToOperators.comp i.completion
  let post : (V →L[ℂ] V) →L[ℂ] (V →L[ℂ] V) := ContinuousLinearMap.compL ℂ V V V B
  let M₁ : ProjectiveTensor X V →L[ℂ] (V →L[ℂ] V) :=
    (ξ.comp (projectiveKernelMapOutput B)).comp Completion.toComplL
  let M₂ : ProjectiveTensor X V →L[ℂ] (V →L[ℂ] V) := (post.comp ξ).comp Completion.toComplL
  have hξ (u : X) (w y : V) :
      ξ (((↑) : ProjectiveTensor X V → Completion (ProjectiveTensor X V)) (u ⊗ₜ[ℂ] w)) y =
        e.symm u y • w :=
    (congrArg (fun T : V →L[ℂ] V ↦ T y)
      ((congrArg completedProjectiveTensorToOperators
        (ContinuousLinearMap.completion_apply_coe i (u ⊗ₜ[ℂ] w : ProjectiveTensor X V))).trans
        (completedProjectiveTensorToOperators_coe _))).trans
      (tensorToFiniteRank_tmul (e.symm u) w y)
  have hM (t : ProjectiveTensor X V) : M₁ t = M₂ t := by
    induction t using TensorProduct.inductionOn with
    | tmul u w =>
      apply ContinuousLinearMap.ext
      intro y
      have h₁ : M₁ (u ⊗ₜ[ℂ] w : ProjectiveTensor X V) y =
          ξ (((↑) : ProjectiveTensor X V → Completion (ProjectiveTensor X V)) (u ⊗ₜ[ℂ] B w)) y :=
        congrArg (fun κ' ↦ ξ κ' y) (projectiveKernelMapOutput_coe B (u ⊗ₜ[ℂ] w))
      exact h₁.trans ((hξ u (B w) y).trans
        (((congrArg B (hξ u w y)).trans (map_smul B _ w)).symm))
    | add x y hx hy =>
      exact (map_add M₁ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add M₂ x y).symm)
  exact Completion.induction_on κ
    (isClosed_eq (ξ.continuous.comp (projectiveKernelMapOutput B).continuous)
      (post.continuous.comp ξ.continuous)) hM

end FiniteTensors

section BlockSums

/-- A block-diagonal operator commutes with every finite sum of whole coordinate-block
projections. A copy of the private `spectralStripAmbientKernel_tendsto_blocks` of `Sec4b`. -/
private theorem spectralBlockSums_comm {E J Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : J → E) (f : J → StrongDual ℂ E) (hb : IsSpectralMarkushevichBasis x f)
    (N : Z → ℕ) (j : (z : Z) → Fin (N z) → J)
    (hj : Bijective (fun p : (z : Z) × Fin (N z) ↦ j p.1 p.2))
    (op : E →L[ℂ] E)
    (hcross : ∀ z z', z ≠ z' → ∀ m n, f (j z m) (op (x (j z' n))) = 0)
    (K : Finset Z) (u : E) :
    (∑ z ∈ K, ∑ m, f (j z m) u • op (x (j z m))) =
      ∑ z ∈ K, ∑ m, f (j z m) (op u) • x (j z m) := by
  classical
  have same (z : Z) (m n : Fin (N z)) :
      f (j z m) (x (j z n)) = if n = m then 1 else 0 := by
    split_ifs with h
    · subst n
      exact hb.1 _
    · apply hb.2.1
      intro e
      exact h (eq_of_heq (Sigma.mk.inj (hj.1 e)).2)
  have other {z z' : Z} (h : z ≠ z') (m : Fin (N z)) (n : Fin (N z')) :
      f (j z m) (x (j z' n)) = 0 := by
    apply hb.2.1
    intro e
    exact h (congrArg Sigma.fst (hj.1 (a₁ := ⟨z', n⟩) (a₂ := ⟨z, m⟩) e)).symm
  have separate {v w : E} (h : ∀ i, f i v = f i w) : v = w := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    have he : ContinuousLinearMap.apply ℂ ℂ v = ContinuousLinearMap.apply ℂ ℂ w := by
      apply ContinuousLinearMap.ext_on hb.2.2.2
      rintro _ ⟨i, rfl⟩
      exact h i
    exact fun ℓ ↦ DFunLike.congr_fun he ℓ
  apply Finset.sum_congr rfl
  intro z _
  let P : E →L[ℂ] E := ∑ m : Fin (N z), (f (j z m)).smulRight (x (j z m))
  have vec (z' : Z) (n : Fin (N z')) :
      P (x (j z' n)) = if z' = z then x (j z' n) else 0 := by
    by_cases h : z' = z
    · subst z'
      simp [P, same, ite_smul]
    · simp [P, other (Ne.symm h), h]
  have coord (z' : Z) (n : Fin (N z')) (v : E) :
      f (j z' n) (P v) = if z' = z then f (j z' n) v else 0 := by
    by_cases h : z' = z
    · subst z'
      simp [P, map_sum, same, smul_eq_mul, mul_ite]
    · simp [P, map_sum, other h, h]
  have comm : op.comp P = P.comp op := by
    apply ContinuousLinearMap.ext_on hb.2.2.1
    rintro _ ⟨i, rfl⟩
    obtain ⟨⟨z', n⟩, rfl⟩ := hj.2 i
    apply separate
    intro k
    obtain ⟨⟨z'', m⟩, rfl⟩ := hj.2 k
    change f (j z'' m) (op (P (x (j z' n)))) = f (j z'' m) (P (op (x (j z' n))))
    rw [vec, coord]
    by_cases hi : z' = z <;> by_cases ho : z'' = z
    · simp [hi, ho]
    · subst z'
      simp [ho, hcross _ _ ho]
    · subst z''
      simp [hi, hcross _ _ (Ne.symm hi)]
    · simp [hi, ho]
  simpa [P, map_sum] using DFunLike.congr_fun comm u

end BlockSums

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
local notation "Pgeom(" a ", " hα ", " hs ")" => geometricProjection (F := F) a hα hs

section KernelOperators

variable {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)

/-- A bounded operator applied to the output factor of a kernel composes with the operator of
the kernel. -/
theorem sobolevProjectiveKernelOperator_mapOutput (B : W(α, s) →L[ℂ] W(α, s))
    (κ : Π(W'(α, s), W(α, s))) :
    sobolevProjectiveKernelOperator (F := F) hα hs (projectiveKernelMapOutput B κ) =
      B.comp (sobolevProjectiveKernelOperator (F := F) hα hs κ) :=
  kernelOperator_mapOutput_aux
    ((modulatedIntervalSobolev_dual m𝔽
      ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
      μ𝔽 (-α) α s (hStrip(hα)) hs).exists.choose) B κ

/-- The spectral projection of a vector is the orthogonal lift of its class in the quotient. -/
theorem spectralProjection_eq_orthogonalLift (a : ℝ) (v : W(α, s)) :
    Pspec(a, hα, hs) v = S(a, hα, hs) (Q(a, hα, hs) v) := by
  let θ := Θ(a, hα, hs)
  have hzero : θ.mkQ (Pgeom(a, hα, hs) v) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (θ.starProjection_apply_mem v)
  have hsame : θ.mkQ v = θ.mkQ (Pspec(a, hα, hs) v) := calc
    _ = θ.mkQ (Pgeom(a, hα, hs) v + Pspec(a, hα, hs) v) :=
      congrArg θ.mkQ (θ.starProjection_add_starProjection_orthogonal v).symm
    _ = _ := (map_add θ.mkQ _ _).trans (by rw [hzero, zero_add])
  have hrep := θ.quotientEquivOrthogonal_mk (Pspec(a, hα, hs) v)
    (θ.orthogonal.starProjection_apply_mem v)
  exact (congrArg Subtype.val hrep).symm.trans
    (congrArg (fun y ↦ (θ.quotientEquivOrthogonal y).val) hsame.symm)

/-- Paper: Remark 10.4.1.4, pp. 457–458. Convolution after the spectral projection and the
spectral projection after convolution differ by the geometric part of the first: the commutator
of the convolution with the spectral projection is `P^geom ∘ A(φ) ∘ P^spec`, because the theta
subspace is invariant. -/
theorem stripTestAction_comp_spectralProjection_sub (a : ℝ) (φ : BruhatCompactSupport C𝔽) :
    (A(hα, hs, φ)).comp (Pspec(a, hα, hs)) - (Pspec(a, hα, hs)).comp (A(hα, hs, φ)) =
      (Pgeom(a, hα, hs)).comp ((A(hα, hs, φ)).comp (Pspec(a, hα, hs))) := by
  let θ := Θ(a, hα, hs)
  let P := Pspec(a, hα, hs)
  let G := Pgeom(a, hα, hs)
  let B : W(α, s) →L[ℂ] W(α, s) := A(hα, hs, φ)
  have hsplit (w : W(α, s)) : G w + P w = w := θ.starProjection_add_starProjection_orthogonal w
  have hPG (w : W(α, s)) : P (G w) = 0 := by
    have h1 := hsplit (G w)
    have h2 : G (G w) = G w :=
      geometricProjection_apply_of_mem a hα hs (θ.starProjection_apply_mem w)
    rw [h2] at h1
    exact add_left_cancel (h1.trans (add_zero _).symm)
  apply ContinuousLinearMap.ext
  intro u
  have hinv : G (B (G u)) = B (G u) :=
    DFunLike.congr_fun (geometricProjection_convolution_geometricProjection (F := F) a hα hs φ) u
  have hPBG : P (B (G u)) = 0 := hinv ▸ hPG (B (G u))
  have hBu : B u = B (G u) + B (P u) := by rw [← map_add, hsplit]
  change B (P u) - P (B u) = G (B (P u))
  rw [hBu, map_add, hPBG, zero_add]
  exact sub_eq_of_eq_add (hsplit (B (P u))).symm

/-- Paper: Theorem 10.4.3.5(3), p. 473, the geometric part. The geometric part
`P^geom ∘ A(φ) ∘ P^spec` of convolution after spectral projection has a projective Sobolev
kernel, at every symmetric strip, nonnegative Sobolev order and real twist. It is the image of a
kernel of `A(φ) ∘ P^spec` (`stripTestAction_spectralProjection_has_projectiveKernel`) under the
geometric projection on the output factor. -/
theorem geometricProjection_stripTestAction_spectralProjection_has_projectiveKernel (a : ℝ)
    (φ : BruhatCompactSupport C𝔽) :
    ∃ κ, sobolevProjectiveKernelOperator (F := F) hα hs κ =
      (Pgeom(a, hα, hs)).comp ((A(hα, hs, φ)).comp (Pspec(a, hα, hs))) := by
  obtain ⟨K, hK⟩ := stripTestAction_spectralProjection_has_projectiveKernel (F := F) a hα hs φ
  exact ⟨projectiveKernelMapOutput (Pgeom(a, hα, hs)) K,
    (sobolevProjectiveKernelOperator_mapOutput hα hs _ K).trans
      (congrArg (fun T ↦ (Pgeom(a, hα, hs)).comp T) hK)⟩

/-- Paper: Theorem 10.4.3.5(3), p. 473, the geometric part. The commutator
`P^geom ∘ A(φ) ∘ P^spec` of convolution with the spectral projection is nuclear on the Sobolev
space, at every symmetric strip, nonnegative Sobolev order and real twist. -/
theorem geometricProjection_stripTestAction_spectralProjection_nuclear (a : ℝ)
    (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator ((Pgeom(a, hα, hs)).comp ((A(hα, hs, φ)).comp (Pspec(a, hα, hs)))) := by
  obtain ⟨κ, hκ⟩ :=
    geometricProjection_stripTestAction_spectralProjection_has_projectiveKernel hα hs a φ
  exact (existsUnique_sobolevProjectiveKernel_iff_nuclear (F := F) hα hs _).mp
    ⟨κ, hκ, fun L hL ↦ sobolevProjectiveKernelOperator_injective hα hs (hL.trans hκ.symm)⟩

end KernelOperators

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

-- The statement and its packaging are on the concrete Sobolev quotient, as in `Sec4b`.
set_option maxHeartbeats 400000 in
/-- Paper: Theorem 10.4.3.5(3), p. 473, equation (10.4.3.45), with the zeros summed by clusters.
If the ambient tensors, with convolution on the output factor, summed over finite unions of
clusters converge in the completed projective tensor product, their limit represents
convolution after spectral projection. No estimate enters: on the lift of a biorthogonal vector
the sums are constant once the cluster of its zero is included.
Reconstruction: The paper does not state this. `spectralStripAmbientKernel_operator` of `Sec4b`
is its statement for a limit along the rectangles of an enumeration. -/
theorem spectralStripAmbientKernel_clusters_operator
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x f) (κ : Π(W'(α, s), W(α, s)))
    (hκ : SpectralClusterKernelsTendstoTo (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m))
      (fun j ↦ D (f j)) (fun j ↦ A(hα, hs₀(hs), φ) (S(a, hα, hs₀(hs)) (x j))) κ) :
    sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) κ =
      (A(hα, hs₀(hs), φ)).comp (Pspec(a, hα, hs₀(hs))) := by
  obtain ⟨ι, K, hd, hc, hlim⟩ := hκ
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
  apply ContinuousLinearMap.ext
  intro v
  refine (spectralClusterAmbientSums_limit_eq θ.mkQL lift hsection (A(hα, hs₀(hs), φ))
    (sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) κ) (fun z : Z(χ) ↦ N(χ, z)) key
    index.bijective x f hb K hd hc (fun w ↦ ?_) v).trans
    (congrArg (A(hα, hs₀(hs), φ)) (spectralProjection_eq_orthogonalLift hα hs₀(hs) a v).symm)
  let ev := (ContinuousLinearMap.apply ℂ (W(α, s)) w).comp
    (sobolevProjectiveKernelOperator (F := F) hα hs₀(hs))
  refine ((ev.continuous.tendsto κ).comp hlim).congr fun C ↦ ?_
  exact sobolevProjectiveKernelOperator_spectralKernelSum a hα hs₀(hs) _
    (fun z : Z(χ) ↦ N(χ, z)) key f (fun j ↦ A(hα, hs₀(hs), φ) (lift (x j))) w

-- The statement and its packaging are on the concrete Sobolev quotient, as in `Sec4b`.
set_option maxHeartbeats 400000 in
/-- Paper: Theorem 10.4.3.5(2)–(3), pp. 472–473, for a test split in two, with the zeros summed
by clusters. Let convolution by `ψ` act on the input factor, as in the printed tensors
(10.4.3.43), and convolution by `φ` on the output factor, as the operator order of (10.4.3.45)
requires. These tensors, summed over finite unions of clusters, converge in the completed
projective tensor product, and the limit represents `A(φ) ∘ P^spec ∘ A(ψ)`. No estimate for the
geometric component is used, and the recorded gap #7241 is not used.
Reconstruction: The paper does not state this. With all of the convolution on the output
factor the convergence is open (`spectralStripAmbientKernel_tendsto` of `Sec4b` assumes the
geometric components Cauchy). With all of it on the input factor the sums converge to a kernel
of `P^spec ∘ A(ψ)` (`spectralStripTransposedKernel_clusters_operator`). -/
theorem spectralStripSplitKernel_clusters_operator
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (hχ : IsSpectralBasepointChoice χ) (hb : Bases(χ, x, f))
    (ψ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)) :
    ∃ κ : Π(W'(α, s), W(α, s)),
      SpectralClusterKernelsTendstoTo (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m))
        (fun j ↦ D ((f j).comp (Aq(a, hα, hs₀(hs), ψ))))
        (fun j ↦ A(hα, hs₀(hs), φ) (S(a, hα, hs₀(hs)) (x j))) κ ∧
      sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) κ =
        (A(hα, hs₀(hs), φ)).comp ((Pspec(a, hα, hs₀(hs))).comp (A(hα, hs₀(hs), ψ))) := by
  obtain ⟨κ, hκ, hop⟩ :=
    spectralStripTransposedKernel_clusters_operator (F := F) a hα hs ψ χ x f hχ hb
  exact ⟨projectiveKernelMapOutput (A(hα, hs₀(hs), φ)) κ, hκ.mapOutput _,
    (sobolevProjectiveKernelOperator_mapOutput hα hs₀(hs) _ κ).trans
      (congrArg (fun T ↦ (A(hα, hs₀(hs), φ)).comp T) hop)⟩

-- The statement and its packaging are on the concrete Sobolev quotient, as in `Sec4b`.
set_option maxHeartbeats 400000 in
/-- Paper: Theorem 10.4.3.5(2), p. 472, the geometric component, for a test split in two, with
the zeros summed by clusters. The geometric components of the split tensors of
`spectralStripSplitKernel_clusters_operator` converge by clusters, and the limit represents
`P^geom ∘ A(φ) ∘ P^spec ∘ A(ψ)`. So the geometric component converges as soon as any
convolution acts on the input factor.
Reconstruction: The paper does not state this. For the geometric components with no convolution
on the input factor see `spectralStripGeometricKernel_blocks_bddAbove` of `Sec4b_Isolated`. -/
theorem spectralStripSplitGeometricKernel_clusters_operator
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (hχ : IsSpectralBasepointChoice χ) (hb : Bases(χ, x, f))
    (ψ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)) :
    ∃ κ : Π(W'(α, s), W(α, s)),
      SpectralClusterKernelsTendstoTo (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m))
        (fun j ↦ D ((f j).comp (Aq(a, hα, hs₀(hs), ψ))))
        (fun j ↦ Pgeom(a, hα, hs₀(hs)) (A(hα, hs₀(hs), φ) (S(a, hα, hs₀(hs)) (x j)))) κ ∧
      sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) κ =
        (Pgeom(a, hα, hs₀(hs))).comp ((A(hα, hs₀(hs), φ)).comp
          ((Pspec(a, hα, hs₀(hs))).comp (A(hα, hs₀(hs), ψ)))) := by
  obtain ⟨κ, hκ, hop⟩ :=
    spectralStripSplitKernel_clusters_operator (F := F) a hα hs φ χ x f hχ hb ψ
  exact ⟨projectiveKernelMapOutput (Pgeom(a, hα, hs₀(hs))) κ, hκ.mapOutput _,
    (sobolevProjectiveKernelOperator_mapOutput hα hs₀(hs) _ κ).trans
      (congrArg (fun T ↦ (Pgeom(a, hα, hs₀(hs))).comp T) hop)⟩

-- The statement and its packaging are on the concrete Sobolev quotient, as in `Sec4b`.
set_option maxHeartbeats 400000 in
/-- Paper: Theorem 10.4.3.5(2), pp. 472–473. Over every finite set of zeros, the ambient tensor
sum with convolution on the output factor is the sum of its geometric component and of the
printed tensor sum (10.4.3.43) with convolution transposed onto the input factor. The spectral
component of the output is the lift of the quotient convolution, and convolution commutes with
the block projection of each zero. This is the identity in the proof of
`spectralStripAmbientKernel_tendsto` of `Sec4b`, for an arbitrary finite set of zeros in place
of a rectangle. -/
theorem spectralStripAmbientKernelSum_eq_geometric_add_transposed
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (hb : Bases(χ, x, f)) (K₀ : Finset Z(χ)) :
    spectralKernelSum K₀ (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m)) (fun j ↦ D (f j))
        (fun j ↦ A(hα, hs₀(hs), φ) (S(a, hα, hs₀(hs)) (x j))) =
      spectralKernelSum K₀ (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m)) (fun j ↦ D (f j))
        (fun j ↦ Pgeom(a, hα, hs₀(hs)) (A(hα, hs₀(hs), φ) (S(a, hα, hs₀(hs)) (x j)))) +
      spectralKernelSum K₀ (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m))
        (fun j ↦ D ((f j).comp (Aq(a, hα, hs₀(hs), φ)))) (fun j ↦ S(a, hα, hs₀(hs)) (x j)) := by
  let θ := Θ(a, hα, hs₀(hs))
  let lift := θ.orthogonal.subtypeL.comp
    θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  let T := Aq(a, hα, hs₀(hs), φ)
  let B : W(α, s) →L[ℂ] W(α, s) := A(hα, hs₀(hs), φ)
  let Pg := Pgeom(a, hα, hs₀(hs))
  have hsection (u) : θ.mkQL (lift u) = u :=
    (θ.quotientEquivOrthogonal_symm_eq_mk _ (θ.quotientEquivOrthogonal u).property).symm.trans
      (θ.quotientEquivOrthogonal.symm_apply_apply u)
  have hsplit (u : H(a, hα, hs₀(hs))) : Pg (B (lift u)) + lift (T u) = B (lift u) := by
    have hp := DFunLike.congr_fun
      (spectralProjection_convolution_factor (F := F) a hα hs₀(hs) φ) (lift u)
    change Pspec(a, hα, hs₀(hs)) (B (lift u)) = lift (T (θ.mkQL (lift u))) at hp
    rw [hsection] at hp
    exact (congrArg (Pg (B (lift u)) + ·) hp.symm).trans
      (θ.starProjection_add_starProjection_orthogonal _)
  let key (z : Z(χ)) (m : Fin N(χ, z)) : SpectralStripJetIndex χ a α s := jet(z, m)
  let index : ((z : Z(χ)) × Fin N(χ, z)) ≃ SpectralStripJetIndex χ a α s :=
    ⟨fun p ↦ key p.1 p.2,
      fun j ↦ ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1),
        SpectralStripJetIndex.mem_strip_order_pos hα j⟩, ⟨j.val.2.2.2, j.property⟩⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hcross (z z' : Z(χ)) (hne : z ≠ z') (m : Fin N(χ, z)) (n : Fin N(χ, z')) :
      f (key z m) (T (x (key z' n))) = 0 :=
    (spectralStripConvolution_jetCoefficients a hα hs χ x f hb.1 hb.2 φ).1 z z' hne m n
  have hcomm := spectralBlockSums_comm x f hb.1 (fun z : Z(χ) ↦ N(χ, z)) key
    index.bijective T hcross
  have hswap : spectralKernelSum K₀ (fun z : Z(χ) ↦ N(χ, z)) key (fun j ↦ D (f j))
      (fun j ↦ lift (T (x j))) =
      spectralKernelSum K₀ (fun z : Z(χ) ↦ N(χ, z)) key (fun j ↦ D ((f j).comp T))
        (fun j ↦ lift (x j)) := by
    apply sobolevProjectiveKernelOperator_injective (F := F) hα hs₀(hs)
    apply ContinuousLinearMap.ext
    intro v
    have h₁ := sobolevProjectiveKernelOperator_spectralKernelSum a hα hs₀(hs) K₀
      (fun z : Z(χ) ↦ N(χ, z)) key f (fun j ↦ lift (T (x j))) v
    have h₂ := sobolevProjectiveKernelOperator_spectralKernelSum a hα hs₀(hs) K₀
      (fun z : Z(χ) ↦ N(χ, z)) key (fun j ↦ (f j).comp T) (fun j ↦ lift (x j)) v
    refine h₁.trans (Eq.trans ?_ h₂.symm)
    simpa only [map_sum, map_smul, ContinuousLinearMap.comp_apply] using
      congrArg lift (hcomm K₀ (θ.mkQL v))
  have hfinal := congrArg (fun outputs ↦ spectralKernelSum K₀ (fun z : Z(χ) ↦ N(χ, z)) key
    (fun j ↦ D (f j)) outputs) (funext fun j ↦ (hsplit (x j)).symm)
  exact hfinal.trans ((spectralKernelSum_add K₀ (fun z : Z(χ) ↦ N(χ, z)) key (fun j ↦ D (f j))
    (fun j ↦ Pg (B (lift (x j)))) (fun j ↦ lift (T (x j)))).trans (congrArg (_ + ·) hswap))

-- The statement and its packaging are on the concrete Sobolev quotient, as in `Sec4b`.
set_option maxHeartbeats 400000 in
/-- Paper: Theorem 10.4.3.5(2)–(3), pp. 472–473, with the zeros summed by clusters: what the
geometric estimate must supply. There are clusters, and a kernel `κT` of spectral projection
after convolution, such that for every `κ` the geometric components of the ambient tensors
summed by clusters converge to `κ` exactly when the ambient tensors summed by clusters converge
to `κ + κT`. In that case `κ` represents the commutator `P^geom ∘ A(φ) ∘ P^spec`, and `κ + κT`
represents convolution after spectral projection, the operator of (10.4.3.45).
Reconstruction: The paper does not state this. It is the cluster form of
`spectralStripAmbientKernel_exists_iff_geometric_cauchy` of `Sec4b_Isolated`, with the limits
named. The spectral component is supplied by `spectralStripTransposedKernel_clusters_operator`,
so the recorded gap #7241 is not used. -/
theorem spectralStripAmbientKernel_clusters_tendsto_iff_geometric
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (hχ : IsSpectralBasepointChoice χ) (hb : Bases(χ, x, f)) :
    ∃ (ι : Type u) (K : ι → Finset Z(χ)) (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j))
      (κT : Π(W'(α, s), W(α, s))),
      (∀ z, ∃ i, z ∈ K i) ∧
      sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) κT =
        (Pspec(a, hα, hs₀(hs))).comp (A(hα, hs₀(hs), φ)) ∧
      ∀ κ : Π(W'(α, s), W(α, s)),
        (SpectralKernelSumsTendstoAlong K hd (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m))
            (fun j ↦ D (f j))
            (fun j ↦ Pgeom(a, hα, hs₀(hs)) (A(hα, hs₀(hs), φ) (S(a, hα, hs₀(hs)) (x j)))) κ ↔
          SpectralKernelSumsTendstoAlong K hd (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m))
            (fun j ↦ D (f j))
            (fun j ↦ A(hα, hs₀(hs), φ) (S(a, hα, hs₀(hs)) (x j))) (κ + κT)) ∧
        (SpectralKernelSumsTendstoAlong K hd (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m))
            (fun j ↦ D (f j))
            (fun j ↦ Pgeom(a, hα, hs₀(hs)) (A(hα, hs₀(hs), φ) (S(a, hα, hs₀(hs)) (x j)))) κ →
          sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) κ =
            (Pgeom(a, hα, hs₀(hs))).comp
              ((A(hα, hs₀(hs), φ)).comp (Pspec(a, hα, hs₀(hs))))) := by
  obtain ⟨κT, ⟨ι, K, hd, hc, hT⟩, hop⟩ :=
    spectralStripTransposedKernel_clusters_operator (F := F) a hα hs φ χ x f hχ hb
  refine ⟨ι, K, hd, κT, hc, hop, fun κ ↦ ?_⟩
  have hiff := spectralKernelSumsTendstoAlong_add_iff K hd (fun z : Z(χ) ↦ N(χ, z))
    (fun z m ↦ jet(z, m)) (fun j ↦ D (f j))
    (fun j ↦ A(hα, hs₀(hs), φ) (S(a, hα, hs₀(hs)) (x j)))
    (fun j ↦ Pgeom(a, hα, hs₀(hs)) (A(hα, hs₀(hs), φ) (S(a, hα, hs₀(hs)) (x j))))
    (fun j ↦ D ((f j).comp (Aq(a, hα, hs₀(hs), φ)))) (fun j ↦ S(a, hα, hs₀(hs)) (x j)) κT
    (spectralStripAmbientKernelSum_eq_geometric_add_transposed (F := F) a hα hs φ χ x f hb)
    hT κ
  refine ⟨hiff, fun hg ↦ ?_⟩
  have h := spectralStripAmbientKernel_clusters_operator (F := F) a hα hs φ χ x f hb.1 (κ + κT)
    ⟨ι, K, hd, hc, hiff.mp hg⟩
  have h' : sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) κ +
      (Pspec(a, hα, hs₀(hs))).comp (A(hα, hs₀(hs), φ)) =
      (A(hα, hs₀(hs), φ)).comp (Pspec(a, hα, hs₀(hs))) :=
    ((congrArg (sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) κ + ·) hop.symm).trans
      (map_add (sobolevProjectiveKernelOperator (F := F) hα hs₀(hs)) κ κT).symm).trans h
  exact (eq_sub_of_add_eq h').trans (stripTestAction_comp_spectralProjection_sub hα hs₀(hs) a φ)

end StripTensors

end RiemannMasullo
