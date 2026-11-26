module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3
public import RiemannMasullo.ForMathlib.Analysis.Complex.RectangleInterpolation
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.ForMathlib.Analysis.Fourier.PaleyWienerStrip

/-! # Zero clusters for Theorem 10.3.2.1: trace class from data on rectangle boundaries

Convolution on the strip spectral quotient is trace class as soon as the zeros of the strip can
be grouped into finite clusters whose blocks of the spectral convolution have summable trace
norms (`spectralStripConvolution_nuclear_of_clusters`). This file reduces that summability, step
by step, to data that mention no operator: kernels on the idele class group
(`spectralStripConvolution_summable_clusterTraceNorms_of_kernels`), functions on the real line
(`…_of_scalarKernels`), entire multipliers (`…_of_multipliers`), and at the end, for each
angular component, one entire function that vanishes at the zeros, with lower bounds on the
boundaries of the rectangles between chosen heights
(`spectralStripConvolution_summable_clusterTraceNorms_of_boundaryData`). No bound at a single
zero is used, so no distance between two zeros enters.

`Sec3_TraceClass` produces these data for every number field and every test. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "Q(" a ", " hI ", " hs ")" => spectralSobolevQuotient F a hI hs
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat

variable (a : ℝ)

local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

-- Select the norm topology directly when using the locally convex nuclear ideal, as in `Sec3`.
attribute [local instance] instSpectralQuotientPolynormableSec3

/-- A coordinate of a finite section: the jets of the selected zeros reproduce the coordinates
of the image of the operator, and the coordinates at all the other zeros vanish. -/
private theorem spectralStripConvolution_nuclear_of_clusters_coordinate
    {H J Z : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [DecidableEq Z]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x Λ)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (hjet : Injective (fun j : (z : Z) × Fin (N z) ↦ jet j.1 j.2))
    (K : Finset Z) (z : Z) (m : Fin (N z)) (v : H) :
    Λ (jet z m) (spectralConvolutionFiniteSum A x Λ K N jet v) =
      if z ∈ K then Λ (jet z m) (A v) else 0 := by
  simp only [spectralConvolutionFiniteSum, sum_apply, map_sum,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
  split_ifs with hz
  · rw [Finset.sum_eq_single_of_mem z hz]
    · rw [Finset.sum_eq_single m]
      · rw [hb.1, mul_one]
      · intro k _ hk
        have hne : jet z k ≠ jet z m :=
          fun h ↦ hk (eq_of_heq (Sigma.mk.inj_iff.mp (hjet (a₁ := ⟨z, k⟩) (a₂ := ⟨z, m⟩) h)).2)
        rw [hb.2.1 _ _ hne, mul_zero]
      · simp
    · intro w _ hw
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      have hne : jet w k ≠ jet z m :=
        fun h ↦ hw (congrArg Sigma.fst (hjet (a₁ := ⟨w, k⟩) (a₂ := ⟨z, m⟩) h))
      rw [hb.2.1 _ _ hne, mul_zero]
  · refine Finset.sum_eq_zero fun w hw ↦ Finset.sum_eq_zero fun k _ ↦ ?_
    have hne : jet w k ≠ jet z m := fun h ↦ by
      have hwz : w = z := congrArg Sigma.fst (hjet (a₁ := ⟨w, k⟩) (a₂ := ⟨z, m⟩) h)
      exact hz (hwz ▸ hw)
    rw [hb.2.1 _ _ hne, mul_zero]

/-- The operator norm of a nuclear endomorphism is at most its trace norm. -/
private theorem spectralStripConvolution_nuclear_of_clusters_opNorm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) : ‖T.val‖ ≤ traceNorm T := by
  have hmem := (mem_traceClassOperators_iff_isNuclearOperator T.val).2 T.property
  have hsum : Summable (approximationNumber T.val) := by simpa using hmem.2
  have ht := schattenNorm_one_eq_traceNorm T
  simp only [schattenNorm, Real.rpow_one, div_one] at ht
  rw [← ht, ← approximationNumber_zero_eq_opNorm T.val hmem.1]
  exact hsum.le_tsum 0 fun n _ ↦ Real.sInf_nonneg fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _

/-- If the zeros are grouped into finite clusters whose blocks have summable trace norms, the
cluster blocks sum to the operator in operator norm, by biorthogonality and totality of the
coordinate functionals, and the operator is nuclear. No bound for a single zero is used. -/
theorem spectralStripConvolution_nuclear_of_clusters_abstract
    {H J Z ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x Λ)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (hjet : Bijective (fun j : (z : Z) × Fin (N z) ↦ jet j.1 j.2))
    (K : ι → Finset Z) (hdisj : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (hcover : ∀ z, ∃ i, z ∈ K i) (R : ι → nuclearEndomorphisms H)
    (hR : ∀ i, (R i).val = spectralConvolutionFiniteSum A x Λ (K i) N jet)
    (hsum : Summable (fun i ↦ traceNorm (R i))) :
    ∃ hA : IsNuclearOperator A, HasSum (fun i ↦ (R i).val) A ∧
      traceNorm ⟨A, hA⟩ ≤ ∑' i, traceNorm (R i) := by
  classical
  obtain ⟨C, hC⟩ : Summable (fun i ↦ (R i).val) := Summable.of_norm_bounded hsum fun i ↦
    spectralStripConvolution_nuclear_of_clusters_opNorm (R i)
  have hCA : C = A := by
    ext v
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    have hev : ContinuousLinearMap.apply ℂ ℂ (C v) = ContinuousLinearMap.apply ℂ ℂ (A v) := by
      apply ContinuousLinearMap.ext_on hb.2.2.2
      rintro _ ⟨j, rfl⟩
      obtain ⟨⟨z, m⟩, rfl⟩ := hjet.2 j
      change Λ (jet z m) (C v) = Λ (jet z m) (A v)
      obtain ⟨i₀, hi₀⟩ := hcover z
      have h1 : HasSum (fun i ↦ Λ (jet z m) ((R i).val v)) (Λ (jet z m) (C v)) :=
        (Λ (jet z m)).hasSum ((ContinuousLinearMap.apply ℂ H v).hasSum hC)
      have h2 : HasSum (fun i ↦ Λ (jet z m) ((R i).val v)) (Λ (jet z m) (A v)) := by
        refine (hasSum_ite_eq i₀ (Λ (jet z m) (A v))).congr_fun fun i ↦ ?_
        rw [hR, spectralStripConvolution_nuclear_of_clusters_coordinate A x Λ hb
          N jet hjet.1]
        by_cases hi : i = i₀
        · subst hi
          simp [hi₀]
        · have hz : z ∉ K i := fun hz ↦ Finset.disjoint_left.mp (hdisj i i₀ hi) hz hi₀
          simp [hi, hz]
      exact h1.unique h2
    exact fun ℓ ↦ DFunLike.congr_fun hev ℓ
  subst hCA
  obtain ⟨hA, hle⟩ := traceNorm_le_of_hasSum R C hC (fun i ↦ traceNorm (R i)) hsum fun _ ↦ le_rfl
  exact ⟨hA, hC, hle⟩

/-- The clusters of a partition into finite sets, as a family indexed by the partition. -/
private theorem spectralStripConvolution_nuclear_of_clusters_partition
    {H J Z : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x Λ)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (hjet : Bijective (fun j : (z : Z) × Fin (N z) ↦ jet j.1 j.2))
    (P : Set (Finset Z)) (R : P → nuclearEndomorphisms H) (hdisj : P.PairwiseDisjoint id)
    (hcover : ∀ z : Z, ∃ K ∈ P, z ∈ K)
    (hR : ∀ K : P, (R K).val = spectralConvolutionFiniteSum A x Λ K.val N jet)
    (hsum : Summable (fun K : P ↦ traceNorm (R K))) :
    IsNuclearOperator A := by
  obtain ⟨hA, -⟩ := spectralStripConvolution_nuclear_of_clusters_abstract
    A x Λ hb N jet hjet (fun K : P ↦ K.val)
    (fun K L hKL ↦ hdisj K.property L.property fun h ↦ hKL (Subtype.ext h))
    (fun z ↦ by
      obtain ⟨K, hK, hz⟩ := hcover z
      exact ⟨⟨K, hK⟩, hz⟩) R hR hsum
  exact hA

/-- Paper: Theorem 10.3.2.1(2), p. 454. Convolution on the strip spectral quotient is trace class
as soon as, for one Markushevich basis of the strip jets, the zeros can be grouped into finite
clusters whose blocks have summable trace norms. Only biorthogonality and totality of the basis
are used: the cluster blocks then sum to the convolution in operator norm.
Deviation: Stated for every Sobolev order `s ≥ 0`; §10.3 of the paper assumes `s > 1` (p. 455). -/
theorem spectralStripConvolution_nuclear_of_clusters
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (P : Set (Finset Z(χ, α))) (R : P → nuclearEndomorphisms Q(a, hStrip(hα), hs))
    (hdisj : P.PairwiseDisjoint id) (hcover : ∀ z : Z(χ, α), ∃ K ∈ P, z ∈ K)
    (hR : ∀ K : P, (R K).val = spectralConvolutionFiniteSum
      (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ K.val
      (fun z ↦ N(χ, α, s, z)) (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩))
    (hsum : Summable (fun K : P ↦ traceNorm (R K))) :
    let H := Q(a, hStrip(hα), hs)
    IsNuclearOperator (E := H) (F := H) (spectralConvolution (F := F) a hStrip(hα) hs φ) := by
  let count (z : Z(χ, α)) := N(χ, α, s, z)
  let jet (z : Z(χ, α)) (m : Fin (count z)) : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
  let index (j : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s) :
      (z : Z(χ, α)) × Fin (count z) :=
    ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩,
      ⟨j.val.2.2.2, j.property⟩⟩
  let equiv : ((z : Z(χ, α)) × Fin (count z)) ≃
      SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨fun zm ↦ jet zm.1 zm.2, index, fun _ ↦ rfl, fun _ ↦ rfl⟩
  exact spectralStripConvolution_nuclear_of_clusters_partition
    (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ hb count jet equiv.bijective
    P R hdisj hcover hR hsum

/-- The trace norm of a nuclear endomorphism whose range has dimension at most `n` is at most
`n` times its operator norm: its approximation numbers vanish from the index `n` on, and each
is at most the operator norm. -/
theorem spectralStripConvolution_summable_clusterTraceNorms_of_summable_clusterNorms_rank
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) (n : ℕ)
    (hrank : Module.rank ℂ T.val.toLinearMap.range ≤ (n : Cardinal)) :
    traceNorm T ≤ n * ‖T.val‖ := by
  have hmem := (mem_traceClassOperators_iff_isNuclearOperator T.val).2 T.property
  have ht := schattenNorm_one_eq_traceNorm T
  simp only [schattenNorm, Real.rpow_one, div_one] at ht
  have hlow (k : ℕ) : ∀ r ∈ {r | ∃ S : H →L[ℂ] H,
      Module.rank ℂ S.toLinearMap.range ≤ (k : Cardinal) ∧ r = ‖S - T.val‖}, 0 ≤ r :=
    fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _
  have hle (k : ℕ) : approximationNumber T.val k ≤ ‖T.val‖ := by
    refine (csInf_le ⟨0, hlow k⟩ ⟨0, ?_, rfl⟩).trans_eq (by simp)
    rw [show (0 : H →L[ℂ] H).toLinearMap.range = ⊥ from LinearMap.range_zero, rank_bot]
    exact zero_le
  have hzero (k : ℕ) (hk : k ∉ Finset.range n) : approximationNumber T.val k = 0 := by
    have hnk : (n : Cardinal) ≤ (k : Cardinal) := by
      exact_mod_cast not_lt.mp (Finset.mem_range.not.mp hk)
    apply le_antisymm
    · exact (csInf_le ⟨0, hlow k⟩ ⟨T.val, hrank.trans hnk, rfl⟩).trans_eq (by simp)
    · exact le_csInf ⟨_, T.val, hrank.trans hnk, rfl⟩ (hlow k)
  rw [← ht, tsum_eq_sum hzero]
  refine (Finset.sum_le_sum fun k _ ↦ hle k).trans_eq ?_
  simp

/-- The range of a finite section lies in the span of the biorthogonal vectors of its jets, so
its dimension is at most the number of these jets. -/
theorem spectralStripConvolution_summable_clusterTraceNorms_of_summable_clusterNorms_range
    {H J Z : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H)
    (K : Finset Z) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) :
    Module.rank ℂ (spectralConvolutionFiniteSum A x Λ K N jet).toLinearMap.range ≤
      ((∑ z ∈ K, N z : ℕ) : Cardinal) := by
  classical
  let Y := (K.sigma fun z ↦ (Finset.univ : Finset (Fin (N z)))).image (fun p ↦ x (jet p.1 p.2))
  have hsub : (spectralConvolutionFiniteSum A x Λ K N jet).toLinearMap.range ≤
      Submodule.span ℂ (Y : Set H) := by
    rintro _ ⟨v, rfl⟩
    change spectralConvolutionFiniteSum A x Λ K N jet v ∈ Submodule.span ℂ (Y : Set H)
    simp only [spectralConvolutionFiniteSum, sum_apply, ContinuousLinearMap.smulRight_apply]
    refine Submodule.sum_mem _ fun z hz ↦ Submodule.sum_mem _ fun m _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Finset.mem_image.mpr ⟨⟨z, m⟩, Finset.mem_sigma.mpr ⟨hz, Finset.mem_univ _⟩, rfl⟩
  refine (Submodule.rank_mono hsub).trans ((rank_span_finset_le Y).trans ?_)
  have hcard : Y.card ≤ ∑ z ∈ K, N z := by
    refine Finset.card_image_le.trans_eq ?_
    simp
  exact_mod_cast hcard

/-- A summable bound by the number of jets of each cluster times the operator norm of its block
gives summable trace norms of the cluster blocks. -/
private theorem spectralStripConvolution_summable_clusterTraceNorms_of_summable_clusterNorms_abstract
    {H J Z : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) (P : Set (Finset Z))
    (hdisj : P.PairwiseDisjoint id) (hcover : ∀ z : Z, ∃ K ∈ P, z ∈ K)
    (hsum : Summable (fun K : P ↦ ((∑ z ∈ K.val, N z : ℕ) : ℝ) *
      ‖spectralConvolutionFiniteSum A x Λ K.val N jet‖)) :
    ∃ (P : Set (Finset Z)) (R : P → nuclearEndomorphisms H),
      P.PairwiseDisjoint id ∧ (∀ z : Z, ∃ K ∈ P, z ∈ K) ∧
      (∀ K : P, (R K).val = spectralConvolutionFiniteSum A x Λ K.val N jet) ∧
      Summable (fun K : P ↦ traceNorm (R K)) := by
  let R (K : P) : nuclearEndomorphisms H := ⟨spectralConvolutionFiniteSum A x Λ K.val N jet,
    (nuclearEndomorphisms H).sum_mem fun z _ ↦ (nuclearEndomorphisms H).sum_mem fun m _ ↦
      smulRight_mem_nuclearEndomorphisms _ _⟩
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hcore := traceNorm_normedSpaceCore (H := H)
  refine ⟨P, R, hdisj, hcover, fun _ ↦ rfl, ?_⟩
  exact Summable.of_nonneg_of_le (fun K ↦ hcore.norm_nonneg (R K)) (fun K ↦
    spectralStripConvolution_summable_clusterTraceNorms_of_summable_clusterNorms_rank (R K) _
      (spectralStripConvolution_summable_clusterTraceNorms_of_summable_clusterNorms_range A x Λ K.val N jet))
    hsum

/-- An operator that acts on the jets of a finite set of zeros as the given operator does, and
annihilates the jets of all the other zeros, is the block of that set: the two have the same
coordinates, and the coordinate functionals are total. -/
theorem spectralStripConvolution_summable_clusterTraceNorms_of_kernels_block
    {H J Z : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x Λ)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (hjet : Bijective (fun j : (z : Z) × Fin (N z) ↦ jet j.1 j.2))
    (K : Finset Z) (Ψ : H →L[ℂ] H)
    (hin : ∀ z ∈ K, ∀ (m : Fin (N z)) (u : H), Λ (jet z m) (Ψ u) = Λ (jet z m) (A u))
    (hout : ∀ z ∉ K, ∀ (m : Fin (N z)) (u : H), Λ (jet z m) (Ψ u) = 0) :
    spectralConvolutionFiniteSum A x Λ K N jet = Ψ := by
  classical
  ext v
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  have hev : ContinuousLinearMap.apply ℂ ℂ (spectralConvolutionFiniteSum A x Λ K N jet v) =
      ContinuousLinearMap.apply ℂ ℂ (Ψ v) := by
    apply ContinuousLinearMap.ext_on hb.2.2.2
    rintro _ ⟨j, rfl⟩
    obtain ⟨⟨z, m⟩, rfl⟩ := hjet.2 j
    change Λ (jet z m) (spectralConvolutionFiniteSum A x Λ K N jet v) = Λ (jet z m) (Ψ v)
    rw [spectralStripConvolution_nuclear_of_clusters_coordinate A x Λ hb N jet hjet.1]
    by_cases hz : z ∈ K
    · rw [ite_eq_left hz, hin z hz m v]
    · rw [ite_eq_right hz, hout z hz m v]
  exact fun ℓ ↦ DFunLike.congr_fun hev ℓ

/-- Summable bounds for the norms of interpolating operators of the clusters, weighted by the
numbers of jets, give summable trace norms of the cluster blocks. -/
private theorem spectralStripConvolution_summable_clusterTraceNorms_of_kernels_abstract
    {H J Z : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x Λ)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (hjet : Bijective (fun j : (z : Z) × Fin (N z) ↦ jet j.1 j.2))
    (P : Set (Finset Z)) (hdisj : P.PairwiseDisjoint id) (hcover : ∀ z : Z, ∃ K ∈ P, z ∈ K)
    (b : P → ℝ) (hsum : Summable (fun K : P ↦ ((∑ z ∈ K.val, N z : ℕ) : ℝ) * b K))
    (hop : ∀ K : P, ∃ Ψ : H →L[ℂ] H, ‖Ψ‖ ≤ b K ∧
      (∀ z ∈ K.val, ∀ (m : Fin (N z)) (u : H), Λ (jet z m) (Ψ u) = Λ (jet z m) (A u)) ∧
      (∀ z ∉ K.val, ∀ (m : Fin (N z)) (u : H), Λ (jet z m) (Ψ u) = 0)) :
    ∃ (P : Set (Finset Z)) (R : P → nuclearEndomorphisms H),
      P.PairwiseDisjoint id ∧ (∀ z : Z, ∃ K ∈ P, z ∈ K) ∧
      (∀ K : P, (R K).val = spectralConvolutionFiniteSum A x Λ K.val N jet) ∧
      Summable (fun K : P ↦ traceNorm (R K)) := by
  refine spectralStripConvolution_summable_clusterTraceNorms_of_summable_clusterNorms_abstract A x Λ
    N jet P hdisj hcover (Summable.of_nonneg_of_le (fun K ↦ mul_nonneg (Nat.cast_nonneg _)
      (norm_nonneg _)) (fun K ↦ ?_) hsum)
  obtain ⟨Ψ, hΨ, hin, hout⟩ := hop K
  rw [spectralStripConvolution_summable_clusterTraceNorms_of_kernels_block A x Λ hb N jet hjet
    K.val Ψ hin hout]
  exact mul_le_mul_of_nonneg_left hΨ (Nat.cast_nonneg _)

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. A criterion for the clustered statement
`spectralStripConvolution_summable_clusterTraceNorms` with no operator and no biorthogonal
vector in it. Suppose that each cluster of a grouping of the zeros has a kernel on the idele
class group whose logarithmic Mellin moments, below the surviving multiplicity, agree with those
of the test at the zeros of the cluster and vanish at all the other zeros, and that the
integrals of these kernels against the bound for the norms of the translations, multiplied by
the numbers of jets of the clusters, are summable. Then the clustered statement holds: by
`exists_spectralStripKernelOperator` of `Sec3` each kernel gives an operator on the quotient
with the jets of the cluster block, and the jets are total.
Deviation: Stated for every Sobolev order `s ≥ 0`; §10.3 of the paper assumes `s > 1` (p. 455). -/
theorem spectralStripConvolution_summable_clusterTraceNorms_of_kernels
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (P : Set (Finset Z(χ, α))) (hdisj : P.PairwiseDisjoint id)
    (hcover : ∀ z : Z(χ, α), ∃ K ∈ P, z ∈ K)
    (κ : P → C𝔽 → ℂ) (hκ : ∀ K, AEStronglyMeasurable (κ K) μ𝔽)
    (hint : ∀ K, Integrable (fun g : C𝔽 ↦ ‖κ K g‖ *
      (max (Real.exp (-α * logIdeleClassNorm F g)) (Real.exp (α * logIdeleClassNorm F g)) *
        (1 + |logIdeleClassNorm F g|) ^ (s / 2))) μ𝔽)
    (hmom : ∀ (K : P) (z : Z(χ, α)), ∀ q < N(χ, α, s, z), Integrable (fun g : C𝔽 ↦ κ K g *
      ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2)) g *
        (logIdeleClassNorm F g : ℂ) ^ q) μ𝔽)
    (hin : ∀ K : P, ∀ z ∈ K.val, ∀ q < N(χ, α, s, z),
      ∫ g : C𝔽, κ K g * ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2)) g *
        (logIdeleClassNorm F g : ℂ) ^ q ∂μ𝔽 =
      ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2)) g *
        (logIdeleClassNorm F g : ℂ) ^ q ∂μ𝔽)
    (hout : ∀ K : P, ∀ z ∉ K.val, ∀ q < N(χ, α, s, z),
      ∫ g : C𝔽, κ K g * ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2)) g *
        (logIdeleClassNorm F g : ℂ) ^ q ∂μ𝔽 = 0)
    (hsum : Summable (fun K : P ↦ ((∑ z ∈ K.val, N(χ, α, s, z) : ℕ) : ℝ) *
      ∫ g : C𝔽, ‖κ K g‖ *
        (max (Real.exp (-α * logIdeleClassNorm F g)) (Real.exp (α * logIdeleClassNorm F g)) *
          (1 + |logIdeleClassNorm F g|) ^ (s / 2)) ∂μ𝔽)) :
    ∃ (P : Set (Finset Z(χ, α))) (R : P → nuclearEndomorphisms Q(a, hStrip(hα), hs)),
      P.PairwiseDisjoint id ∧ (∀ z : Z(χ, α), ∃ K ∈ P, z ∈ K) ∧
      (∀ K : P, (R K).val = spectralConvolutionFiniteSum
        (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ K.val
        (fun z ↦ N(χ, α, s, z)) (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)) ∧
      Summable (fun K : P ↦ traceNorm (R K)) := by
  let count (z : Z(χ, α)) := N(χ, α, s, z)
  let jet (z : Z(χ, α)) (m : Fin (count z)) : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
  let index (j : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s) :
      (z : Z(χ, α)) × Fin (count z) :=
    ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩,
      ⟨j.val.2.2.2, j.property⟩⟩
  let equiv : ((z : Z(χ, α)) × Fin (count z)) ≃
      SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨fun zm ↦ jet zm.1 zm.2, index, fun _ ↦ rfl, fun _ ↦ rfl⟩
  refine spectralStripConvolution_summable_clusterTraceNorms_of_kernels_abstract
    (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ hb count jet equiv.bijective
    P hdisj hcover _ hsum fun K ↦ ?_
  obtain ⟨Ψ, hΨ, hjets⟩ := exists_spectralStripKernelOperator a hα hs χ Λ hj φ (κ K) (hκ K) (hint K)
  exact ⟨Ψ, hΨ, fun z hz m u ↦ ((hjets z (hmom K z)).1 (hin K z hz)) m u,
    fun z hz m u ↦ ((hjets z (hmom K z)).2 (hout K z hz)) m u⟩

/-- The norm twist of a unitary character is the character times the exponential of the exponent
times the logarithm of the norm. -/
theorem spectralStripConvolution_summable_clusterTraceNorms_of_scalarKernels_twist
    (η : PontryaginDual C𝔽) (w : ℂ) (g : C𝔽) :
    ideleClassNormTwist (F := F) η w g =
      (η g : ℂ) * Complex.exp (w * (logIdeleClassNorm F g : ℂ)) := by
  have hp : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  change (η g : ℂ) * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ w) = _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le]
  exact congrArg ((η g : ℂ) * ·) (congrArg Complex.exp (mul_comm _ _))

/-- Orthogonality of the angular components: the inverse of the basepoint character of one
component times a function of the norm has vanishing integral against the norm twists of the
basepoint character of any other component. -/
theorem spectralStripConvolution_summable_clusterTraceNorms_of_scalarKernels_orthogonal
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {ω ω₀ : PontryaginDual C₁} (hne : ω ≠ ω₀) (w : ℂ) (H : ℝ → ℂ) :
    ∫ g : C𝔽, (((χ ω₀ g)⁻¹ : Circle) : ℂ) * H (logIdeleClassNorm F g) *
      ideleClassNormTwist (F := F) (χ ω) w g ∂μ𝔽 = 0 := by
  obtain ⟨k, hk⟩ : ∃ k : C₁, (ω k : ℂ) ≠ (ω₀ k : ℂ) := by
    by_contra! heq
    exact hne (DFunLike.ext _ _ fun k ↦ Subtype.ext (heq k))
  let ξ := ideleClassNormTwist (F := F) (χ ω) w
  have hkξ : ξ k.val = (ω k : ℂ) := by
    have h := DFunLike.congr_fun (hχ ω) k
    change (χ ω) k.val = ω k at h
    change (χ ω k.val : ℂ) * (((ideleClassNorm F k.val).val : ℝ) : ℂ) ^ w = _
    rw [k.property]
    simpa using congrArg (fun u : Circle ↦ (u : ℂ)) h
  have hk₀ : (χ ω₀) k.val = ω₀ k := DFunLike.congr_fun (hχ ω₀) k
  have hL (g : C𝔽) : logIdeleClassNorm F (k.val * g) = logIdeleClassNorm F g := by
    change Real.log ((ideleClassNorm F (k.val * g)).val : ℝ) =
      Real.log ((ideleClassNorm F g).val : ℝ)
    rw [map_mul, k.property, one_mul]
  let Fn (g : C𝔽) : ℂ := (((χ ω₀ g)⁻¹ : Circle) : ℂ) * H (logIdeleClassNorm F g) * ξ g
  let I := ∫ g, Fn g ∂μ𝔽
  have heq : I = ((((ω₀ k)⁻¹ : Circle) : ℂ) * (ω k : ℂ)) * I := calc
    I = ∫ g, Fn (k.val * g) ∂μ𝔽 := (integral_mul_left_eq_self Fn k.val).symm
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae (.of_forall fun g ↦ ?_)
      change (((χ ω₀ (k.val * g))⁻¹ : Circle) : ℂ) * H (logIdeleClassNorm F (k.val * g)) *
        ξ (k.val * g) = _
      rw [hL, map_mul, map_mul, hkξ, hk₀, mul_inv, Circle.coe_mul]
      ring
  have hunit : (((ω₀ k)⁻¹ : Circle) : ℂ) * (ω k : ℂ) ≠ 1 := by
    intro h
    apply hk
    have h1 : (((ω₀ k)⁻¹ * ω k : Circle) : ℂ) = ((1 : Circle) : ℂ) := by
      rw [Circle.coe_mul, h, Circle.coe_one]
    have h2 : (ω₀ k)⁻¹ * ω k = 1 := Circle.ext h1
    rw [inv_mul_eq_one.mp h2]
  have hzero : (1 - (((ω₀ k)⁻¹ : Circle) : ℂ) * (ω k : ℂ)) * I = 0 := by
    rw [sub_mul, one_mul, ← heq, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hunit.symm)

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. A criterion for the clustered statement
`spectralStripConvolution_summable_clusterTraceNorms` in terms of functions on the real line
only. Group the zeros into finite clusters, each inside one angular component. Suppose each
cluster has a measurable function on `ℝ`, integrable against the exponentials of the strip times every power, whose Laplace
moments for the pushforward of the class measure under the logarithm of the norm, below the
surviving multiplicity, agree with the logarithmic Mellin moments of the test at the zeros of
the cluster and vanish at the other zeros of the same component. If its integrals against the
weight of the strip, multiplied by the numbers of jets of the clusters, are summable, the
clustered statement holds. The kernel on the class group is the inverse of the basepoint
character of the component times the function of the logarithm of the norm; its moments at the
zeros of the other components vanish by orthogonality.
Deviation: Stated for every Sobolev order `s ≥ 0`; §10.3 of the paper assumes `s > 1` (p. 455). -/
theorem spectralStripConvolution_summable_clusterTraceNorms_of_scalarKernels
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (P : Set (Finset Z(χ, α))) (hdisj : P.PairwiseDisjoint id)
    (hcover : ∀ z : Z(χ, α), ∃ K ∈ P, z ∈ K)
    (comp : P → PontryaginDual C₁) (hcomp : ∀ K : P, ∀ z ∈ K.val, z.val.1 = comp K)
    (k : P → ℝ → ℂ) (hk : ∀ K, Measurable (k K))
    (hint : ∀ K, Integrable (fun y : ℝ ↦ ‖k K y‖ *
      (max (Real.exp (-α * y)) (Real.exp (α * y)) * (1 + |y|) ^ (s / 2)))
      (Measure.map (logIdeleClassNorm F) μ𝔽))
    (hdecay : ∀ (K : P) (b : ℝ), b ∈ Icc (-α) α → ∀ q : ℕ, Integrable (fun y : ℝ ↦ ‖k K y‖ *
      (Real.exp (b * y) * |y| ^ q)) (Measure.map (logIdeleClassNorm F) μ𝔽))
    (hin : ∀ K : P, ∀ z ∈ K.val, ∀ q < N(χ, α, s, z),
      ∫ y : ℝ, k K y * (Complex.exp (shift(z.val.2.1, z.val.2.2) * (y : ℂ)) * (y : ℂ) ^ q)
        ∂(Measure.map (logIdeleClassNorm F) μ𝔽) =
      ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2)) g *
        (logIdeleClassNorm F g : ℂ) ^ q ∂μ𝔽)
    (hout : ∀ K : P, ∀ z : Z(χ, α), z ∉ K.val → z.val.1 = comp K → ∀ q < N(χ, α, s, z),
      ∫ y : ℝ, k K y * (Complex.exp (shift(z.val.2.1, z.val.2.2) * (y : ℂ)) * (y : ℂ) ^ q)
        ∂(Measure.map (logIdeleClassNorm F) μ𝔽) = 0)
    (hsum : Summable (fun K : P ↦ ((∑ z ∈ K.val, N(χ, α, s, z) : ℕ) : ℝ) *
      ∫ y : ℝ, ‖k K y‖ * (max (Real.exp (-α * y)) (Real.exp (α * y)) * (1 + |y|) ^ (s / 2))
        ∂(Measure.map (logIdeleClassNorm F) μ𝔽))) :
    ∃ (P : Set (Finset Z(χ, α))) (R : P → nuclearEndomorphisms Q(a, hStrip(hα), hs)),
      P.PairwiseDisjoint id ∧ (∀ z : Z(χ, α), ∃ K ∈ P, z ∈ K) ∧
      (∀ K : P, (R K).val = spectralConvolutionFiniteSum
        (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ K.val
        (fun z ↦ N(χ, α, s, z)) (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)) ∧
      Summable (fun K : P ↦ traceNorm (R K)) := by
  let L : C𝔽 → ℝ := logIdeleClassNorm F
  have hLc : Continuous L :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_ideleClassNorm F).continuous)).log
      fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  let wt (y : ℝ) : ℝ := max (Real.exp (-α * y)) (Real.exp (α * y)) * (1 + |y|) ^ (s / 2)
  have hwt : Measurable wt := by fun_prop
  let κ (K : P) (g : C𝔽) : ℂ := (((χ (comp K) g)⁻¹ : Circle) : ℂ) * k K (L g)
  have hκnorm (K : P) (g : C𝔽) : ‖κ K g‖ = ‖k K (L g)‖ := by
    change ‖(((χ (comp K) g)⁻¹ : Circle) : ℂ) * k K (L g)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul]
  have hκm (K : P) : AEStronglyMeasurable (κ K) μ𝔽 :=
    ((continuous_subtype_val.comp ((χ (comp K)).continuous.inv)).aestronglyMeasurable).mul
      ((hk K).comp hLc.measurable).aestronglyMeasurable
  have htw (η : PontryaginDual C𝔽) (w : ℂ) (g : C𝔽) :=
    spectralStripConvolution_summable_clusterTraceNorms_of_scalarKernels_twist (F := F) η w g
  -- The moments at the zeros of the component of the cluster are Laplace moments on the line.
  have hmomEq (K : P) (z : Z(χ, α)) (hc : z.val.1 = comp K) (q : ℕ) :
      ∫ g : C𝔽, κ K g * ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2)) g *
        (logIdeleClassNorm F g : ℂ) ^ q ∂μ𝔽 =
      ∫ y : ℝ, k K y * (Complex.exp (shift(z.val.2.1, z.val.2.2) * (y : ℂ)) * (y : ℂ) ^ q)
        ∂(Measure.map (logIdeleClassNorm F) μ𝔽) := by
    have hG : AEStronglyMeasurable (fun y : ℝ ↦ k K y *
        (Complex.exp (shift(z.val.2.1, z.val.2.2) * (y : ℂ)) * (y : ℂ) ^ q))
        (Measure.map (logIdeleClassNorm F) μ𝔽) :=
      ((hk K).mul (by fun_prop)).aestronglyMeasurable
    rw [integral_map hLc.aemeasurable hG]
    refine integral_congr_ae (.of_forall fun g ↦ ?_)
    change (((χ (comp K) g)⁻¹ : Circle) : ℂ) * k K (L g) *
      ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2)) g * (L g : ℂ) ^ q =
      k K (L g) * (Complex.exp (shift(z.val.2.1, z.val.2.2) * (L g : ℂ)) * (L g : ℂ) ^ q)
    rw [htw, hc]
    have hone : (((χ (comp K) g)⁻¹ : Circle) : ℂ) * (χ (comp K) g : ℂ) = 1 := by
      rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
    linear_combination (k K (L g) * Complex.exp (shift(z.val.2.1, z.val.2.2) * (L g : ℂ)) *
      (L g : ℂ) ^ q) * hone
  refine spectralStripConvolution_summable_clusterTraceNorms_of_kernels a χ hα hs φ x Λ hb hj P
    hdisj hcover κ hκm (fun K ↦ ?_) (fun K z q _ ↦ ?_) (fun K z hz q hq ↦ ?_)
    (fun K z hz q hq ↦ ?_) ?_
  · have hF : AEStronglyMeasurable (fun y : ℝ ↦ ‖k K y‖ * wt y)
        (Measure.map (logIdeleClassNorm F) μ𝔽) :=
      ((hk K).norm.mul hwt).aestronglyMeasurable
    refine ((integrable_map_measure hF hLc.aemeasurable).mp (hint K)).congr (.of_forall fun g ↦ ?_)
    change ‖k K (L g)‖ * wt (L g) = ‖κ K g‖ * wt (L g)
    rw [hκnorm]
  · have hF : AEStronglyMeasurable (fun y : ℝ ↦ ‖k K y‖ * (Real.exp (z.val.2.1 * y) * |y| ^ q))
        (Measure.map (logIdeleClassNorm F) μ𝔽) :=
      ((hk K).norm.mul (by fun_prop)).aestronglyMeasurable
    have h := (integrable_map_measure hF hLc.aemeasurable).mp (hdecay K z.val.2.1 z.property.1 q)
    refine h.mono' (((hκm K).mul
      (ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2))).continuous.aestronglyMeasurable).mul
      ((Complex.continuous_ofReal.comp hLc).pow q).aestronglyMeasurable) (.of_forall fun g ↦ ?_)
    change ‖κ K g * ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2)) g *
      (L g : ℂ) ^ q‖ ≤ ‖k K (L g)‖ * (Real.exp (z.val.2.1 * L g) * |L g| ^ q)
    rw [norm_mul, norm_mul, hκnorm, htw, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    have hre : (shift(z.val.2.1, z.val.2.2) * ((L g : ℝ) : ℂ)).re = z.val.2.1 * L g := by
      simp [Complex.mul_re]
    exact le_of_eq (congrArg (fun r : ℝ ↦ ‖k K (L g)‖ * (Real.exp r * |L g| ^ q)) hre)
  · rw [hmomEq K z (hcomp K z hz) q]
    exact hin K z hz q hq
  · by_cases hc : z.val.1 = comp K
    · rw [hmomEq K z hc q]
      exact hout K z hz hc q hq
    · have horth := spectralStripConvolution_summable_clusterTraceNorms_of_scalarKernels_orthogonal
        (F := F) χ hχ hc (shift(z.val.2.1, z.val.2.2)) (fun y : ℝ ↦ k K y * (y : ℂ) ^ q)
      refine Eq.trans (integral_congr_ae (.of_forall fun g ↦ ?_)) horth
      change (((χ (comp K) g)⁻¹ : Circle) : ℂ) * k K (L g) *
        ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2)) g * (L g : ℂ) ^ q =
        (((χ (comp K) g)⁻¹ : Circle) : ℂ) * (k K (L g) * (L g : ℂ) ^ q) *
          ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2)) g
      ring
  · refine hsum.congr fun K ↦ ?_
    have hF : AEStronglyMeasurable (fun y : ℝ ↦ ‖k K y‖ * wt y)
        (Measure.map (logIdeleClassNorm F) μ𝔽) :=
      ((hk K).norm.mul hwt).aestronglyMeasurable
    change _ * ∫ y : ℝ, ‖k K y‖ * wt y ∂(Measure.map (logIdeleClassNorm F) μ𝔽) =
      _ * ∫ g : C𝔽, ‖κ K g‖ * wt (L g) ∂μ𝔽
    rw [integral_map hLc.aemeasurable hF]
    refine congrArg _ (integral_congr_ae (.of_forall fun g ↦ ?_))
    change ‖k K (L g)‖ * wt (L g) = ‖κ K g‖ * wt (L g)
    rw [hκnorm]

/-- The logarithm of the norm sends the class measure to a positive multiple of Lebesgue
measure, since the class norm is proper and surjective. This is a third private copy of one
lemma: the private `exists_map_logClassNorm_eq_smul_volume` of `AppB_AnalyticNT/Sec1` and the
private `tate_exists_map_logClassNorm_eq_smul_volume` of `Ch03_IdelicZeta/Sec2`. It is copied
here because those are private; this copy adds that the constant is not zero. -/
theorem spectralStripConvolution_summable_clusterTraceNorms_of_multipliers_map_logNorm :
    ∃ c : ℝ≥0, c ≠ 0 ∧ Measure.map (logIdeleClassNorm F) μ𝔽 = c • (volume : Measure ℝ) := by
  let μ := ideleClassTamagawaMeasure F
  let ν : Measure (Multiplicative ℝ) := (volume : Measure ℝ)
  let : ν.IsHaarMeasure := by
    have : IsFiniteMeasureOnCompacts ν :=
      inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
    have : Measure.IsOpenPosMeasure ν :=
      inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ℝ))
    have : ν.IsMulLeftInvariant :=
      ⟨fun t ↦ (measurePreserving_add_left (volume : Measure ℝ) t.toAdd).map_eq⟩
    constructor
  let e : ℝ≥0ˣ ≃ₜ ℝ :=
    (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.toHomeomorph.symm
  have he (t : ℝ≥0ˣ) : e t = Real.log (t.val : ℝ) :=
    (Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))).symm
  let m : C𝔽 →* Multiplicative ℝ :=
    { toFun := fun g ↦ Multiplicative.ofAdd (e (ideleClassNorm F g))
      map_one' := by
        change e (ideleClassNorm F 1) = 0
        simp [he]
      map_mul' := fun g h ↦ by
        change e (ideleClassNorm F (g * h)) = e (ideleClassNorm F g) + e (ideleClassNorm F h)
        rw [he, map_mul, Units.val_mul, NNReal.coe_mul, he, he]
        exact Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
          (NNReal.coe_pos.mpr (Units.zero_lt _)).ne' }
  have hm : IsProperMap m :=
    e.isProperMap.comp (isProperMap_ideleClassNorm F)
  obtain ⟨_, _, _, _, _, _, _, _, _, hsurj, _⟩ := ideleGroup_quotient.{_, 0} F
  have hsurj : Surjective m := e.surjective.comp hsurj
  let : (μ.map m).IsHaarMeasure :=
    Measure.isHaarMeasure_map μ m hm.continuous hsurj (isProperMap_iff_tendsto_cocompact.mp hm).2
  refine ⟨Measure.haarScalarFactor (μ.map m) ν,
    (Measure.haarScalarFactor_pos_of_isHaarMeasure (μ.map m) ν).ne', ?_⟩
  have hMap := Measure.isMulLeftInvariant_eq_smul (μ.map m) ν
  have hFun : (m : C𝔽 → ℝ) = logIdeleClassNorm F :=
    funext fun g ↦ he (ideleClassNorm F g)
  rw [← hFun]
  exact hMap

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. A criterion for the clustered statement
`spectralStripConvolution_summable_clusterTraceNorms` in terms of entire functions only. Group
the zeros into finite clusters, each inside one angular component. Suppose each cluster `K` has
an entire function `m K`, bounded by `B K / (1 + t²)` on a closed vertical strip wider than the
strip of the zeros, whose derivatives below the surviving multiplicity agree with the
logarithmic Mellin moments of the test at the zeros of the cluster and vanish at the other
zeros of the same component. If the bounds `B K`, multiplied by the numbers of jets of the
clusters, are summable, the clustered statement holds. The kernel of `m K` is given by the
Paley–Wiener theorem for a strip (`exists_laplaceKernel_of_strip_bound`).
Deviation: Stated for every Sobolev order `s ≥ 0`; §10.3 of the paper assumes `s > 1` (p. 455). -/
theorem spectralStripConvolution_summable_clusterTraceNorms_of_multipliers
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s β : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hβ : α < β) (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (P : Set (Finset Z(χ, α))) (hdisj : P.PairwiseDisjoint id)
    (hcover : ∀ z : Z(χ, α), ∃ K ∈ P, z ∈ K)
    (comp : P → PontryaginDual C₁) (hcomp : ∀ K : P, ∀ z ∈ K.val, z.val.1 = comp K)
    (m : P → ℂ → ℂ) (hm : ∀ K, Differentiable ℂ (m K)) (B : P → ℝ)
    (hbound : ∀ (K : P) (u : ℂ), |u.re| ≤ β → ‖m K u‖ ≤ B K / (1 + u.im ^ 2))
    (hin : ∀ K : P, ∀ z ∈ K.val, ∀ q < N(χ, α, s, z),
      iteratedDeriv q (m K) (shift(z.val.2.1, z.val.2.2)) =
      ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2)) g *
        (logIdeleClassNorm F g : ℂ) ^ q ∂μ𝔽)
    (hout : ∀ K : P, ∀ z : Z(χ, α), z ∉ K.val → z.val.1 = comp K → ∀ q < N(χ, α, s, z),
      iteratedDeriv q (m K) (shift(z.val.2.1, z.val.2.2)) = 0)
    (hsum : Summable (fun K : P ↦ ((∑ z ∈ K.val, N(χ, α, s, z) : ℕ) : ℝ) * B K)) :
    ∃ (P : Set (Finset Z(χ, α))) (R : P → nuclearEndomorphisms Q(a, hStrip(hα), hs)),
      P.PairwiseDisjoint id ∧ (∀ z : Z(χ, α), ∃ K ∈ P, z ∈ K) ∧
      (∀ K : P, (R K).val = spectralConvolutionFiniteSum
        (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ K.val
        (fun z ↦ N(χ, α, s, z)) (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)) ∧
      Summable (fun K : P ↦ traceNorm (R K)) := by
  have hmap :=
    spectralStripConvolution_summable_clusterTraceNorms_of_multipliers_map_logNorm (F := F)
  let c : ℝ≥0 := hmap.choose
  have hc0 : c ≠ 0 := hmap.choose_spec.1
  have hc : Measure.map (logIdeleClassNorm F) μ𝔽 = c • (volume : Measure ℝ) :=
    hmap.choose_spec.2
  have hcpos : (0 : ℝ) < c := lt_of_le_of_ne c.coe_nonneg (NNReal.coe_ne_zero.mpr hc0).symm
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
  have hβ0 : 0 < β := hα.trans_lt hβ
  choose k hkc hkb hkm using fun K : P ↦
    RiemannMasullo.exists_laplaceKernel_of_strip_bound (hm K) hβ0 (hbound K)
  have hB (K : P) : 0 ≤ B K := by
    have h := (norm_nonneg _).trans (hbound K 0 (by simpa using hβ0.le))
    simpa using h
  let wt (y : ℝ) : ℝ := max (Real.exp (-α * y)) (Real.exp (α * y)) * (1 + |y|) ^ (s / 2)
  have hwtc : Continuous wt :=
    (Continuous.max (by fun_prop) (by fun_prop)).mul
      ((continuous_const.add continuous_abs).rpow_const fun y ↦
        Or.inl (by positivity : (0 : ℝ) < 1 + |y|).ne')
  have hwt (y : ℝ) : wt y = Real.exp (α * |y|) * (1 + |y|) ^ (s / 2) := by
    change max (Real.exp (-α * y)) (Real.exp (α * y)) * _ = _
    congr 1
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy, max_eq_right (Real.exp_le_exp.mpr (by nlinarith))]
    · rw [abs_of_nonpos hy, max_eq_left (Real.exp_le_exp.mpr (by nlinarith))]
      ring_nf
  have hE : Integrable (fun y : ℝ ↦ (1 + |y|) ^ (s / 2) * Real.exp (-(β - α) * |y|)) :=
    RiemannMasullo.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs (sub_pos.mpr hβ) _
  have hpt (K : P) (y : ℝ) : ‖k K y‖ * wt y ≤
      B K / 2 * ((1 + |y|) ^ (s / 2) * Real.exp (-(β - α) * |y|)) := by
    rw [hwt]
    have hexp : Real.exp (-β * |y|) * Real.exp (α * |y|) = Real.exp (-(β - α) * |y|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc ‖k K y‖ * (Real.exp (α * |y|) * (1 + |y|) ^ (s / 2))
        ≤ (B K / 2 * Real.exp (-β * |y|)) * (Real.exp (α * |y|) * (1 + |y|) ^ (s / 2)) :=
          mul_le_mul_of_nonneg_right (hkb K y) (by positivity)
      _ = B K / 2 * ((1 + |y|) ^ (s / 2) * (Real.exp (-β * |y|) * Real.exp (α * |y|))) := by ring
      _ = _ := by rw [hexp]
  have hkwt (K : P) : Integrable (fun y : ℝ ↦ ‖k K y‖ * wt y) :=
    (hE.const_mul (B K / 2)).mono' ((hkc K).norm.mul hwtc).aestronglyMeasurable
      (.of_forall fun y ↦ by
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (by
          change 0 ≤ max _ _ * _
          positivity))]
        exact hpt K y)
  let k' (K : P) (y : ℝ) : ℂ := ((c : ℝ) : ℂ)⁻¹ * k K y
  have hk'norm (K : P) (y : ℝ) : ‖k' K y‖ = (c : ℝ)⁻¹ * ‖k K y‖ := by
    change ‖((c : ℝ) : ℂ)⁻¹ * k K y‖ = _
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hcpos.le]
  -- The Laplace moments of the rescaled kernel for the pushforward measure.
  have hmomν (K : P) (z : Z(χ, α)) (q : ℕ) :
      ∫ y : ℝ, k' K y * (Complex.exp (shift(z.val.2.1, z.val.2.2) * (y : ℂ)) * (y : ℂ) ^ q)
        ∂(Measure.map (logIdeleClassNorm F) μ𝔽) =
      iteratedDeriv q (m K) (shift(z.val.2.1, z.val.2.2)) := by
    have hre : |(shift(z.val.2.1, z.val.2.2)).re| < β := by
      have h1 : (shift(z.val.2.1, z.val.2.2)).re = z.val.2.1 := by simp
      rw [h1]
      exact (abs_le.mpr z.property.1).trans_lt hβ
    rw [hc, integral_smul_nnreal_measure, ← hkm K _ hre q, NNReal.smul_def, Complex.real_smul,
      ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    have hcc : ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hcC
    change ((c : ℝ) : ℂ) * (((c : ℝ) : ℂ)⁻¹ * k K y *
      (Complex.exp (shift(z.val.2.1, z.val.2.2) * (y : ℂ)) * (y : ℂ) ^ q)) =
      k K y * (Complex.exp (shift(z.val.2.1, z.val.2.2) * (y : ℂ)) * (y : ℂ) ^ q)
    linear_combination (k K y * (Complex.exp (shift(z.val.2.1, z.val.2.2) * (y : ℂ)) *
      (y : ℂ) ^ q)) * hcc
  refine spectralStripConvolution_summable_clusterTraceNorms_of_scalarKernels a χ hχ hα hs φ x Λ hb
    hj P hdisj hcover comp hcomp k' (fun K ↦ (continuous_const.mul (hkc K)).measurable)
    (fun K ↦ ?_) (fun K b hb' q ↦ ?_) (fun K z hz q hq ↦ ?_) (fun K z hz hcz q hq ↦ ?_) ?_
  · rw [hc]
    refine Integrable.smul_measure_nnreal ?_
    refine ((hkwt K).const_mul (c : ℝ)⁻¹).congr (.of_forall fun y ↦ ?_)
    change (c : ℝ)⁻¹ * (‖k K y‖ * wt y) = ‖k' K y‖ * wt y
    rw [hk'norm, mul_assoc]
  · rw [hc]
    refine Integrable.smul_measure_nnreal ?_
    refine ((RiemannMasullo.integrable_abs_pow_mul_exp_neg_mul_abs (sub_pos.mpr hβ) q).const_mul
      ((c : ℝ)⁻¹ * (B K / 2))).mono'
      (((continuous_const.mul (hkc K)).norm.mul (by fun_prop)).aestronglyMeasurable)
      (.of_forall fun y ↦ ?_)
    rw [Real.norm_of_nonneg (by positivity), hk'norm]
    have hby : Real.exp (b * y) ≤ Real.exp (α * |y|) := by
      refine Real.exp_le_exp.mpr ?_
      calc b * y ≤ |b * y| := le_abs_self _
        _ = |b| * |y| := abs_mul b y
        _ ≤ α * |y| := mul_le_mul_of_nonneg_right (abs_le.mpr hb') (abs_nonneg y)
    have hexp : Real.exp (-β * |y|) * Real.exp (α * |y|) = Real.exp (-(β - α) * |y|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc (c : ℝ)⁻¹ * ‖k K y‖ * (Real.exp (b * y) * |y| ^ q)
        ≤ (c : ℝ)⁻¹ * (B K / 2 * Real.exp (-β * |y|)) * (Real.exp (α * |y|) * |y| ^ q) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hkb K y) (inv_nonneg.mpr hcpos.le))
            (mul_le_mul_of_nonneg_right hby (by positivity)) (by positivity)
            (mul_nonneg (inv_nonneg.mpr hcpos.le)
              (mul_nonneg (div_nonneg (hB K) zero_le_two) (Real.exp_pos _).le))
      _ = (c : ℝ)⁻¹ * (B K / 2) * (|y| ^ q * (Real.exp (-β * |y|) * Real.exp (α * |y|))) := by
          ring
      _ = _ := by rw [hexp]
  · rw [hmomν K z q]
    exact hin K z hz q hq
  · rw [hmomν K z q]
    exact hout K z hz hcz q hq
  · refine Summable.of_nonneg_of_le (fun K ↦ mul_nonneg (Nat.cast_nonneg _)
      (integral_nonneg fun y ↦ mul_nonneg (norm_nonneg _) (by
        change 0 ≤ max _ _ * _
        positivity))) (fun K ↦ ?_)
      (hsum.mul_left ((∫ y : ℝ, (1 + |y|) ^ (s / 2) * Real.exp (-(β - α) * |y|)) / 2))
    have hval : ∫ y : ℝ, ‖k' K y‖ * wt y ∂(Measure.map (logIdeleClassNorm F) μ𝔽) =
        ∫ y : ℝ, ‖k K y‖ * wt y := by
      rw [hc, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae (.of_forall fun y ↦ ?_)
      have hcc : (c : ℝ) * (c : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hcpos.ne'
      change (c : ℝ) * (‖k' K y‖ * wt y) = ‖k K y‖ * wt y
      rw [hk'norm]
      linear_combination (‖k K y‖ * wt y) * hcc
    have hle : ∫ y : ℝ, ‖k K y‖ * wt y ≤
        B K / 2 * ∫ y : ℝ, (1 + |y|) ^ (s / 2) * Real.exp (-(β - α) * |y|) := by
      rw [← integral_const_mul]
      exact integral_mono (hkwt K) (hE.const_mul _) (hpt K)
    change _ * ∫ y : ℝ, ‖k' K y‖ * wt y ∂(Measure.map (logIdeleClassNorm F) μ𝔽) ≤ _
    rw [hval]
    calc ((∑ z ∈ K.val, N(χ, α, s, z) : ℕ) : ℝ) * ∫ y : ℝ, ‖k K y‖ * wt y
        ≤ ((∑ z ∈ K.val, N(χ, α, s, z) : ℕ) : ℝ) *
            (B K / 2 * ∫ y : ℝ, (1 + |y|) ^ (s / 2) * Real.exp (-(β - α) * |y|)) :=
          mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
      _ = _ := by ring

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. The criterion
`spectralStripConvolution_summable_clusterTraceNorms_of_multipliers` for a family of clusters
indexed by an arbitrary type: the clusters are pairwise disjoint finite sets of zeros covering
all the zeros, each inside one angular component, and empty clusters may repeat.
Deviation: Stated for every Sobolev order `s ≥ 0`; §10.3 of the paper assumes `s > 1` (p. 455). -/
theorem spectralStripConvolution_summable_clusterTraceNorms_of_multipliers_indexed
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s β : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hβ : α < β) (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    {ι : Type*} (K : ι → Finset Z(χ, α)) (hdisj : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (hcover : ∀ z : Z(χ, α), ∃ i, z ∈ K i)
    (comp : ι → PontryaginDual C₁) (hcomp : ∀ i, ∀ z ∈ K i, z.val.1 = comp i)
    (m : ι → ℂ → ℂ) (hm : ∀ i, Differentiable ℂ (m i)) (B : ι → ℝ)
    (hbound : ∀ (i : ι) (u : ℂ), |u.re| ≤ β → ‖m i u‖ ≤ B i / (1 + u.im ^ 2))
    (hin : ∀ i, ∀ z ∈ K i, ∀ q < N(χ, α, s, z),
      iteratedDeriv q (m i) (shift(z.val.2.1, z.val.2.2)) =
      ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2)) g *
        (logIdeleClassNorm F g : ℂ) ^ q ∂μ𝔽)
    (hout : ∀ i, ∀ z : Z(χ, α), z ∉ K i → z.val.1 = comp i → ∀ q < N(χ, α, s, z),
      iteratedDeriv q (m i) (shift(z.val.2.1, z.val.2.2)) = 0)
    (hsum : Summable (fun i ↦ ((∑ z ∈ K i, N(χ, α, s, z) : ℕ) : ℝ) * B i)) :
    ∃ (P : Set (Finset Z(χ, α))) (R : P → nuclearEndomorphisms Q(a, hStrip(hα), hs)),
      P.PairwiseDisjoint id ∧ (∀ z : Z(χ, α), ∃ K ∈ P, z ∈ K) ∧
      (∀ K : P, (R K).val = spectralConvolutionFiniteSum
        (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ K.val
        (fun z ↦ N(χ, α, s, z)) (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)) ∧
      Summable (fun K : P ↦ traceNorm (R K)) := by
  have hidx (p : range K) : ∃ i, K i = p.val := p.property
  choose idx hidx' using hidx
  have hinj : Injective idx := fun p p' h ↦
    Subtype.ext ((hidx' p).symm.trans ((congrArg K h).trans (hidx' p')))
  refine spectralStripConvolution_summable_clusterTraceNorms_of_multipliers a χ hχ hα hs hβ φ x Λ
    hb hj (range K) ?_ (fun z ↦ ?_) (fun p ↦ comp (idx p)) (fun p z hz ↦ ?_)
    (fun p ↦ m (idx p)) (fun p ↦ hm (idx p)) (fun p ↦ B (idx p)) (fun p ↦ hbound (idx p))
    (fun p z hz ↦ ?_) (fun p z hz ↦ ?_) ?_
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact hdisj i j fun h ↦ hij (congrArg K h)
  · obtain ⟨i, hi⟩ := hcover z
    exact ⟨K i, ⟨i, rfl⟩, hi⟩
  · exact hcomp (idx p) z (by rw [hidx' p]; exact hz)
  · exact hin (idx p) z (by rw [hidx' p]; exact hz)
  · exact hout (idx p) z (by rw [hidx' p]; exact hz)
  · refine (hsum.comp_injective hinj).congr fun p ↦ ?_
    change ((∑ z ∈ K (idx p), N(χ, α, s, z) : ℕ) : ℝ) * B (idx p) =
      ((∑ z ∈ p.val, N(χ, α, s, z) : ℕ) : ℝ) * B (idx p)
    rw [hidx' p]

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. The clustered statement from data on rectangle
boundaries for a set `S` of angular components outside of which the Mellin transform of the test
vanishes identically. For each component in `S` take an entire function `ϑ ω` of polynomial
growth on a wider vertical strip, vanishing at every zero of the component to at least the
surviving multiplicity, and heights `T ω k` in `[2k, 2k + 1]`; its clusters are its zeros
between two consecutive heights, and the multiplier of a cluster is the contour integral
`rectInterpolant` with `ϑ ω` times a Gaussian centred at the height of the cluster, so no
distance between two zeros enters. Every zero of a component outside `S` is a cluster by
itself, whose block is zero, so nothing is asked of those components. The numbers of jets of
the clusters enter through upper bounds `cnt ω k`. The summable family is `cnt ω k` times the
constant `rectInterpolantGaussianConstant X β (A ω)`, which depends on the component through
its growth exponent `A ω`, times `φb ω k / ℓ ω k`, times the power `(1 + |T ω k|) ^ (A ω + 2)`
of the height, over `ω ∈ S` and the integers `k`.
Deviation: Stated for every Sobolev order `s ≥ 0`; §10.3 of the paper assumes `s > 1` (p. 455). -/
theorem spectralStripConvolution_summable_clusterTraceNorms_of_boundaryData_on
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s β X : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hβ : α < β) (hβX : β < X)
    (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (S : Set (PontryaginDual C₁))
    (hS : ∀ ω ∉ S, ∀ w : ℂ, ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ ω) w g ∂μ𝔽 = 0)
    (A : PontryaginDual C₁ → ℕ) (ϑ : PontryaginDual C₁ → ℂ → ℂ)
    (hϑ : ∀ ω ∈ S, Differentiable ℂ (ϑ ω))
    (hgrowth : ∀ ω ∈ S, ∀ u : ℂ, |u.re| ≤ X + 2 → ‖ϑ ω u‖ ≤ (1 + |u.im|) ^ A ω)
    (hord : ∀ z : Z(χ, α), z.val.1 ∈ S → ((N(χ, α, s, z) : ℕ) : ℕ∞) ≤
      analyticOrderAt (ϑ z.val.1) (shift(z.val.2.1, z.val.2.2)))
    (T : PontryaginDual C₁ → ℤ → ℝ)
    (hT : ∀ ω ∈ S, ∀ k : ℤ, T ω k ∈ Icc (2 * (k : ℝ)) (2 * (k : ℝ) + 1))
    (φb ℓ : PontryaginDual C₁ → ℤ → ℝ) (hℓ : ∀ ω ∈ S, ∀ k, 0 < ℓ ω k)
    (hlow : ∀ ω ∈ S, ∀ k, ∀ w ∈ rectBoundary (-X) X (T ω k) (T ω (k + 1)), ℓ ω k ≤ ‖ϑ ω w‖)
    (hφb : ∀ ω ∈ S, ∀ k, ∀ w ∈ rectBoundary (-X) X (T ω k) (T ω (k + 1)),
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ ω) w g ∂μ𝔽‖ ≤ φb ω k)
    (hfin : ∀ ω ∈ S, ∀ k : ℤ,
      {z : Z(χ, α) | z.val.1 = ω ∧ T ω k ≤ z.val.2.2 ∧ z.val.2.2 < T ω (k + 1)}.Finite)
    (cnt : PontryaginDual C₁ → ℤ → ℝ)
    (hcnt : ∀ ω ∈ S, ∀ (k : ℤ) (K : Finset Z(χ, α)),
      (∀ z ∈ K, z.val.1 = ω ∧ T ω k ≤ z.val.2.2 ∧ z.val.2.2 < T ω (k + 1)) →
      ((∑ z ∈ K, N(χ, α, s, z) : ℕ) : ℝ) ≤ cnt ω k)
    (hsum : Summable (fun p : S × ℤ ↦ cnt p.1.val p.2 *
      (rectInterpolantGaussianConstant X β (A p.1.val) *
        (φb p.1.val p.2 / ℓ p.1.val p.2 * (1 + |T p.1.val p.2|) ^ (A p.1.val + 2))))) :
    ∃ (P : Set (Finset Z(χ, α))) (R : P → nuclearEndomorphisms Q(a, hStrip(hα), hs)),
      P.PairwiseDisjoint id ∧ (∀ z : Z(χ, α), ∃ K ∈ P, z ∈ K) ∧
      (∀ K : P, (R K).val = spectralConvolutionFiniteSum
        (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ K.val
        (fun z ↦ N(χ, α, s, z)) (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)) ∧
      Summable (fun K : P ↦ traceNorm (R K)) := by
  classical
  have hβ0 : 0 < β := hα.trans_lt hβ
  have hX : 0 < X := hβ0.trans hβX
  have hx : -X ≤ X := by linarith
  have hΦ (ω : PontryaginDual C₁) := spectralStripTest_mellin_iteratedDeriv (F := F) (χ ω) φ
  have hT1 (ω : PontryaginDual C₁) (hω : ω ∈ S) (k : ℤ) : T ω k + 1 ≤ T ω (k + 1) := by
    have h1 := (hT ω hω k).2
    have h2 := (hT ω hω (k + 1)).1
    push_cast at h2
    linarith
  have hT3 (ω : PontryaginDual C₁) (hω : ω ∈ S) (k : ℤ) : T ω (k + 1) ≤ T ω k + 3 := by
    have h1 := (hT ω hω k).1
    have h2 := (hT ω hω (k + 1)).2
    push_cast at h2
    linarith
  have hTmono (ω : PontryaginDual C₁) (hω : ω ∈ S) {j j' : ℤ} (h : j ≤ j') :
      T ω j ≤ T ω j' := by
    rcases h.eq_or_lt with rfl | hlt
    · exact le_rfl
    · have h1 := (hT ω hω j).2
      have h2 := (hT ω hω j').1
      have h3 : (j : ℝ) + 1 ≤ j' := by exact_mod_cast hlt
      linarith
  let θ (p : S × ℤ) (u : ℂ) : ℂ :=
    ϑ p.1.val u * Complex.exp ((u - T p.1.val p.2 * Complex.I) ^ 2)
  have hθ (p : S × ℤ) : Differentiable ℂ (θ p) :=
    (hϑ p.1.val p.1.property).mul (((differentiable_id.sub_const _).pow 2).cexp)
  have hθne (p : S × ℤ) :
      ∀ w ∈ rectBoundary (-X) X (T p.1.val p.2) (T p.1.val (p.2 + 1)), θ p w ≠ 0 := fun w hw ↦
    mul_ne_zero (fun h0 ↦ by
      have := hlow p.1.val p.1.property p.2 w hw
      rw [h0, norm_zero] at this
      linarith [hℓ p.1.val p.1.property p.2]) (Complex.exp_ne_zero _)
  have hθord (p : S × ℤ) (z : Z(χ, α)) (hz : z.val.1 = p.1.val) :
      ((N(χ, α, s, z) : ℕ) : ℕ∞) ≤ analyticOrderAt (θ p) (shift(z.val.2.1, z.val.2.2)) := by
    have hzS : z.val.1 ∈ S := by
      rw [hz]
      exact p.1.property
    have hϑeq : ϑ z.val.1 = ϑ p.1.val := congrArg ϑ hz
    have h1 := hord z hzS
    rw [hϑeq] at h1
    have hE : AnalyticAt ℂ (fun u : ℂ ↦ Complex.exp ((u - T p.1.val p.2 * Complex.I) ^ 2))
        (shift(z.val.2.1, z.val.2.2)) :=
      (((differentiable_id.sub_const _).pow 2).cexp).analyticAt _
    change _ ≤ analyticOrderAt
      (ϑ p.1.val * fun u : ℂ ↦ Complex.exp ((u - T p.1.val p.2 * Complex.I) ^ 2)) _
    rw [analyticOrderAt_mul ((hϑ p.1.val p.1.property).analyticAt _) hE]
    exact h1.trans le_self_add
  have hzero (p : S × ℤ) (z : Z(χ, α)) (hz : z.val.1 = p.1.val)
      (hN : 0 < N(χ, α, s, z)) : θ p (shift(z.val.2.1, z.val.2.2)) = 0 := by
    have h1 := hθord p z hz
    by_contra hne
    rw [((hθ p).analyticAt _).analyticOrderAt_eq_zero.mpr hne] at h1
    have h2 : N(χ, α, s, z) = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp h1
    omega
  have hre (z : Z(χ, α)) : (shift(z.val.2.1, z.val.2.2)).re = z.val.2.1 := by simp
  have him (z : Z(χ, α)) : (shift(z.val.2.1, z.val.2.2)).im = z.val.2.2 := by simp
  have hbX (z : Z(χ, α)) : -X < z.val.2.1 ∧ z.val.2.1 < X :=
    ⟨by linarith [z.property.1.1], by linarith [z.property.1.2]⟩
  let K₀ (p : S × ℤ) : Finset Z(χ, α) := (hfin p.1.val p.1.property p.2).toFinset
  have hK (p : S × ℤ) (z : Z(χ, α)) :
      z ∈ K₀ p ↔ z.val.1 = p.1.val ∧ T p.1.val p.2 ≤ z.val.2.2 ∧ z.val.2.2 < T p.1.val (p.2 + 1) :=
    (hfin p.1.val p.1.property p.2).mem_toFinset
  let m₀ (p : S × ℤ) : ℂ → ℂ :=
    rectInterpolant (fun u ↦ ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ p.1.val) u g ∂μ𝔽)
      (θ p) (-X) X (T p.1.val p.2) (T p.1.val (p.2 + 1))
  let B₀ (p : S × ℤ) : ℝ := rectInterpolantGaussianConstant X β (A p.1.val) *
    (φb p.1.val p.2 / ℓ p.1.val p.2 * (1 + |T p.1.val p.2|) ^ (A p.1.val + 2))
  have hm₀ (p : S × ℤ) : Differentiable ℂ (m₀ p) :=
    differentiable_rectInterpolant (hΦ p.1.val).1 (hθ p) hx
      (by linarith [hT1 p.1.val p.1.property p.2]) (hθne p)
  have hbound₀ (p : S × ℤ) (u : ℂ) (hu : |u.re| ≤ β) : ‖m₀ p u‖ ≤ B₀ p / (1 + u.im ^ 2) :=
    norm_rectInterpolant_gaussian_le (hϑ p.1.val p.1.property) (hΦ p.1.val).1 hβ0 hβX
      (hT1 p.1.val p.1.property p.2) (hT3 p.1.val p.1.property p.2)
      (hgrowth p.1.val p.1.property) (hℓ p.1.val p.1.property p.2)
      (hlow p.1.val p.1.property p.2) (hφb p.1.val p.1.property p.2) hu
  have hB₀ (p : S × ℤ) : 0 ≤ B₀ p := by
    have h := (norm_nonneg _).trans (hbound₀ p 0 (by simpa using hβ0.le))
    simpa using h
  refine spectralStripConvolution_summable_clusterTraceNorms_of_multipliers_indexed a χ hχ hα hs hβ
    φ x Λ hb hj (ι := (S × ℤ) ⊕ {z : Z(χ, α) // z.val.1 ∉ S})
    (Sum.elim K₀ fun z ↦ ({z.val} : Finset Z(χ, α))) ?_ ?_
    (Sum.elim (fun p ↦ p.1.val) fun z ↦ z.val.val.1) ?_
    (Sum.elim m₀ fun _ _ ↦ 0) ?_ (Sum.elim B₀ fun _ ↦ 0) ?_ ?_ ?_ ?_
  · -- Clusters are pairwise disjoint.
    rintro (p | z₀) (p' | z₀') hne
    · refine Finset.disjoint_left.mpr fun z hz hz' ↦ ?_
      obtain ⟨h1, h2, h3⟩ := (hK p z).mp hz
      obtain ⟨h1', h2', h3'⟩ := (hK p' z).mp hz'
      have hω : p.1.val = p'.1.val := h1.symm.trans h1'
      have hk : p.2 ≠ p'.2 := fun h ↦ hne (congrArg Sum.inl (Prod.ext (Subtype.ext hω) h))
      rcases lt_or_gt_of_ne hk with hlt | hlt
      · have := hTmono p.1.val p.1.property (Int.add_one_le_iff.mpr hlt)
        rw [hω] at this h3
        linarith
      · have := hTmono p'.1.val p'.1.property (Int.add_one_le_iff.mpr hlt)
        rw [← hω] at this h3'
        linarith
    · refine Finset.disjoint_left.mpr fun z hz hz' ↦ ?_
      have h1 := ((hK p z).mp hz).1
      have h2 : z = z₀'.val := Finset.mem_singleton.mp hz'
      exact z₀'.property (by rw [← h2, h1]; exact p.1.property)
    · refine Finset.disjoint_left.mpr fun z hz hz' ↦ ?_
      have h1 := ((hK p' z).mp hz').1
      have h2 : z = z₀.val := Finset.mem_singleton.mp hz
      exact z₀.property (by rw [← h2, h1]; exact p'.1.property)
    · refine Finset.disjoint_left.mpr fun z hz hz' ↦ ?_
      have h1 : z = z₀.val := Finset.mem_singleton.mp hz
      have h2 : z = z₀'.val := Finset.mem_singleton.mp hz'
      exact hne (congrArg Sum.inr (Subtype.ext (h1.symm.trans h2)))
  · -- Clusters cover the zeros.
    intro z
    by_cases hzS : z.val.1 ∈ S
    · let j : ℤ := ⌊z.val.2.2 / 2⌋
      have hj1 : (j : ℝ) ≤ z.val.2.2 / 2 := Int.floor_le _
      have hj2 : z.val.2.2 / 2 < (j : ℝ) + 1 := Int.lt_floor_add_one _
      have hlo : T z.val.1 (j - 1) ≤ z.val.2.2 := by
        have h := (hT z.val.1 hzS (j - 1)).2
        push_cast at h
        linarith
      have hhi : z.val.2.2 < T z.val.1 (j + 1) := by
        have h := (hT z.val.1 hzS (j + 1)).1
        push_cast at h
        linarith
      by_cases hmid : z.val.2.2 < T z.val.1 j
      · refine ⟨Sum.inl (⟨z.val.1, hzS⟩, j - 1),
          (hK (⟨z.val.1, hzS⟩, j - 1) z).mpr ⟨rfl, hlo, ?_⟩⟩
        change z.val.2.2 < T z.val.1 (j - 1 + 1)
        rwa [sub_add_cancel]
      · exact ⟨Sum.inl (⟨z.val.1, hzS⟩, j),
          (hK (⟨z.val.1, hzS⟩, j) z).mpr ⟨rfl, not_lt.mp hmid, hhi⟩⟩
    · exact ⟨Sum.inr ⟨z, hzS⟩, Finset.mem_singleton_self z⟩
  · -- Each cluster lies in one component.
    rintro (p | z₀) z hz
    · exact ((hK p z).mp hz).1
    · have h1 : z = z₀.val := Finset.mem_singleton.mp hz
      rw [h1]
      rfl
  · rintro (p | z₀)
    · exact hm₀ p
    · exact differentiable_const 0
  · rintro (p | z₀) u hu
    · exact hbound₀ p u hu
    · change ‖(0 : ℂ)‖ ≤ (0 : ℝ) / (1 + u.im ^ 2)
      simp
  · -- At a zero of the cluster the multiplier has the derivatives of the Mellin transform.
    rintro (p | z₀) z hz q hq
    · obtain ⟨hz1, hz2, hz3⟩ := (hK p z).mp hz
      have hz0 := hzero p z hz1 (Nat.zero_lt_of_lt hq)
      have hstrict : T p.1.val p.2 < z.val.2.2 := by
        rcases hz2.eq_or_lt with heq | hlt
        · exact absurd hz0 (hθne p _ (mem_rectBoundary_horizontal (x := z.val.2.1)
            (y := z.val.2.2) ⟨(hbX z).1.le, (hbX z).2.le⟩ (Or.inl heq.symm)))
        · exact hlt
      change iteratedDeriv q
        (rectInterpolant (fun u ↦ ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ p.1.val) u g ∂μ𝔽)
          (θ p) (-X) X (T p.1.val p.2) (T p.1.val (p.2 + 1))) (shift(z.val.2.1, z.val.2.2)) = _
      rw [iteratedDeriv_rectInterpolant_of_mem (hΦ p.1.val).1 (hθ p) hx
        (by linarith [hT1 p.1.val p.1.property p.2])
        (hθne p) (by rw [hre]; exact (hbX z).1) (by rw [hre]; exact (hbX z).2)
        (by rw [him]; exact hstrict) (by rw [him]; exact hz3) (hθord p z hz1) hq,
        (hΦ p.1.val).2 q, hz1]
    · have h1 : z = z₀.val := Finset.mem_singleton.mp hz
      have hzS : z.val.1 ∉ S := by
        rw [h1]
        exact z₀.property
      have hzero' : (fun u : ℂ ↦ ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) u g ∂μ𝔽) =
          fun _ ↦ 0 := funext (hS _ hzS)
      calc iteratedDeriv q (fun _ : ℂ ↦ (0 : ℂ)) (shift(z.val.2.1, z.val.2.2))
          = iteratedDeriv q
              (fun u : ℂ ↦ ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) u g ∂μ𝔽)
              (shift(z.val.2.1, z.val.2.2)) := by rw [hzero']
        _ = _ := (hΦ z.val.1).2 q _
  · -- At a zero of the same component outside the cluster its derivatives vanish.
    rintro (p | z₀) z hz hzc q hq
    · have hz0 := hzero p z hzc (Nat.zero_lt_of_lt hq)
      refine iteratedDeriv_rectInterpolant_of_notMem (hΦ p.1.val).1 (hθ p) hx
        (by linarith [hT1 p.1.val p.1.property p.2]) (hθne p) (fun hmem ↦ ?_)
        (hθord p z hzc) hq
      obtain ⟨-, ht1, ht2⟩ := hmem
      rw [him] at ht1 ht2
      rcases ht2.eq_or_lt with heq | hlt
      · exact hθne p _ (mem_rectBoundary_horizontal (x := z.val.2.1) (y := z.val.2.2)
          ⟨(hbX z).1.le, (hbX z).2.le⟩ (Or.inr heq)) hz0
      · exact hz ((hK p z).mpr ⟨hzc, ht1, hlt⟩)
    · change iteratedDeriv q (fun _ : ℂ ↦ (0 : ℂ)) _ = 0
      simp
  · -- Only the clusters cut along the heights contribute to the sum.
    refine (Sum.inl_injective.summable_iff fun i hi ↦ ?_).mp
      (Summable.of_nonneg_of_le (fun p ↦ ?_) (fun p ↦ ?_) hsum)
    · rcases i with p | z₀
      · exact absurd ⟨p, rfl⟩ hi
      · exact mul_zero _
    · exact mul_nonneg (Nat.cast_nonneg _) (hB₀ p)
    · exact mul_le_mul_of_nonneg_right
        (hcnt p.1.val p.1.property p.2 (K₀ p) fun z hz ↦ (hK p z).mp hz) (hB₀ p)

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. The clustered statement
`spectralStripConvolution_summable_clusterTraceNorms` from data on rectangle boundaries only.
For each angular component take an entire function `ϑ ω` of polynomial growth on a wider
vertical strip, vanishing at every zero of the component to at least the surviving
multiplicity, and heights `T ω k` in `[2k, 2k + 1]`. The clusters are the zeros of one component
between two consecutive heights. If `ϑ ω` is at least `ℓ ω k > 0` and the Mellin transform of the
test is at most `φb ω k` on the boundary of the rectangle `[-X, X] × [T ω k, T ω (k + 1)]`, and
the numbers of jets of the clusters, times the constant `rectInterpolantGaussianConstant X β (A ω)`
(which depends on the component through its growth exponent `A ω`), times `φb ω k / ℓ ω k`,
times the power `(1 + |T ω k|) ^ (A ω + 2)` of the height, are summable, then
the clustered statement holds. The multiplier of a cluster is the contour integral
`rectInterpolant` with `ϑ ω` times a Gaussian centred at the height of the cluster; no distance
between two zeros enters.
Deviation: Stated for every Sobolev order `s ≥ 0`; §10.3 of the paper assumes `s > 1` (p. 455). -/
theorem spectralStripConvolution_summable_clusterTraceNorms_of_boundaryData
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s β X : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hβ : α < β) (hβX : β < X)
    (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (A : PontryaginDual C₁ → ℕ) (ϑ : PontryaginDual C₁ → ℂ → ℂ)
    (hϑ : ∀ ω, Differentiable ℂ (ϑ ω))
    (hgrowth : ∀ ω (u : ℂ), |u.re| ≤ X + 2 → ‖ϑ ω u‖ ≤ (1 + |u.im|) ^ A ω)
    (hord : ∀ z : Z(χ, α), ((N(χ, α, s, z) : ℕ) : ℕ∞) ≤
      analyticOrderAt (ϑ z.val.1) (shift(z.val.2.1, z.val.2.2)))
    (T : PontryaginDual C₁ → ℤ → ℝ)
    (hT : ∀ ω (k : ℤ), T ω k ∈ Icc (2 * (k : ℝ)) (2 * (k : ℝ) + 1))
    (φb ℓ : PontryaginDual C₁ → ℤ → ℝ) (hℓ : ∀ ω k, 0 < ℓ ω k)
    (hlow : ∀ ω k, ∀ w ∈ rectBoundary (-X) X (T ω k) (T ω (k + 1)), ℓ ω k ≤ ‖ϑ ω w‖)
    (hφb : ∀ ω k, ∀ w ∈ rectBoundary (-X) X (T ω k) (T ω (k + 1)),
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ ω) w g ∂μ𝔽‖ ≤ φb ω k)
    (hfin : ∀ ω (k : ℤ),
      {z : Z(χ, α) | z.val.1 = ω ∧ T ω k ≤ z.val.2.2 ∧ z.val.2.2 < T ω (k + 1)}.Finite)
    (hsum : Summable (fun p : PontryaginDual C₁ × ℤ ↦
      ((∑ z ∈ (hfin p.1 p.2).toFinset, N(χ, α, s, z) : ℕ) : ℝ) *
        (rectInterpolantGaussianConstant X β (A p.1) *
          (φb p.1 p.2 / ℓ p.1 p.2 * (1 + |T p.1 p.2|) ^ (A p.1 + 2))))) :
    ∃ (P : Set (Finset Z(χ, α))) (R : P → nuclearEndomorphisms Q(a, hStrip(hα), hs)),
      P.PairwiseDisjoint id ∧ (∀ z : Z(χ, α), ∃ K ∈ P, z ∈ K) ∧
      (∀ K : P, (R K).val = spectralConvolutionFiniteSum
        (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ K.val
        (fun z ↦ N(χ, α, s, z)) (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)) ∧
      Summable (fun K : P ↦ traceNorm (R K)) := by
  refine spectralStripConvolution_summable_clusterTraceNorms_of_boundaryData_on a χ hχ hα hs hβ hβX
    φ x Λ hb hj univ (fun ω hω ↦ absurd (mem_univ ω) hω) A ϑ (fun ω _ ↦ hϑ ω)
    (fun ω _ ↦ hgrowth ω) (fun z _ ↦ hord z) T (fun ω _ ↦ hT ω) φb ℓ (fun ω _ ↦ hℓ ω)
    (fun ω _ ↦ hlow ω) (fun ω _ ↦ hφb ω) (fun ω _ ↦ hfin ω)
    (fun ω k ↦ ((∑ z ∈ (hfin ω k).toFinset, N(χ, α, s, z) : ℕ) : ℝ)) (fun ω _ k K hK ↦ ?_) ?_
  · exact_mod_cast Finset.sum_le_sum_of_subset fun z hz ↦ (hfin ω k).mem_toFinset.mpr (hK z hz)
  · exact hsum.comp_injective
      (i := fun p : ↥(univ : Set (PontryaginDual C₁)) × ℤ ↦ (p.1.val, p.2)) fun p p' h ↦
        Prod.ext (Subtype.ext (Prod.mk.inj h).1) (Prod.mk.inj h).2

/-- The surviving multiplicity at a zero of the strip is at most the vanishing order of any
function that vanishes to the order of the completed `L`-function in the chart `s = a + u`. -/
theorem spectralStripMultiplicity_le_analyticOrderAt
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {α s : ℝ} (z : Z(χ, α)) {ϑ : ℂ → ℂ}
    (h : ∀ u : ℂ, ((mult(χ z.val.1, (a : ℂ) + u) : ℕ) : ℕ∞) ≤ analyticOrderAt ϑ u) :
    ((N(χ, α, s, z) : ℕ) : ℕ∞) ≤ analyticOrderAt ϑ (shift(z.val.2.1, z.val.2.2)) := by
  have hpt : (a : ℂ) + shift(z.val.2.1, z.val.2.2) = shift(a + z.val.2.1, z.val.2.2) := by
    push_cast
    ring
  have h1 := h (shift(z.val.2.1, z.val.2.2))
  rw [hpt] at h1
  refine le_trans ?_ h1
  have hle : N(χ, α, s, z) ≤ mult(χ z.val.1, shift(a + z.val.2.1, z.val.2.2)) := by
    unfold spectralStripMultiplicity spectralBoundaryMultiplicity
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
    · exact Nat.zero_le _
  exact_mod_cast hle

/-- The completed `L`-function of a unitary character has finite order at every point. -/
private theorem spectralStripComponent_finite_window_order_ne_top (ψ : PontryaginDual C𝔽)
    (z : ℂ) : order(ψ, z) ≠ ⊤ := by
  obtain ⟨hΛ, hval⟩ := continuedCompletedHeckeL_spec ψ
  have h2 : order(ψ, (2 : ℂ)) ≠ ⊤ := fun htop ↦ by
    have hbad := completedHeckeL_continuation_zeros ψ _ hΛ hval (by norm_num : 0 < (2 : ℂ).re)
      (by rw [htop]; exact WithTop.coe_lt_top 0)
    norm_num at hbad
  exact hΛ.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ _) (mem_univ z) h2

/-- Paper: Notation 10.2.2.1, p. 445. The zeros of one angular component of the strip with
heights in a bounded window form a finite set: they are zeros of one meromorphic function, not
identically zero, in a compact rectangle. -/
theorem spectralStripComponent_finite_window (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {α : ℝ} (ω : PontryaginDual C₁) (t₁ t₂ : ℝ) :
    {z : Z(χ, α) | z.val.1 = ω ∧ t₁ ≤ z.val.2.2 ∧ z.val.2.2 < t₂}.Finite := by
  have hK : IsCompact (Icc (a - α) (a + α) ×ℂ Icc t₁ t₂) := isCompact_Icc.reProdIm isCompact_Icc
  have hΛ : MeromorphicOn (continuedCompletedHeckeL (F := F) (χ ω))
      (Icc (a - α) (a + α) ×ℂ Icc t₁ t₂) := fun z _ ↦
    (continuedCompletedHeckeL_spec (χ ω)).1.meromorphicOn z (mem_univ z)
  have hfin := (MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) (χ ω))
    (Icc (a - α) (a + α) ×ℂ Icc t₁ t₂)).finiteSupport hK
  refine Set.Finite.of_injOn
    (f := fun z : Z(χ, α) ↦ (shift(a + z.val.2.1, z.val.2.2) : ℂ)) (fun z hz ↦ ?_)
    (fun z hz z' hz' h ↦ ?_) hfin
  · obtain ⟨hω, h1, h2⟩ := hz
    have hmem : shift(a + z.val.2.1, z.val.2.2) ∈ Icc (a - α) (a + α) ×ℂ Icc t₁ t₂ := by
      refine ⟨?_, ?_⟩
      · have hre : (shift(a + z.val.2.1, z.val.2.2)).re = a + z.val.2.1 := by simp
        change (shift(a + z.val.2.1, z.val.2.2)).re ∈ Icc (a - α) (a + α)
        rw [hre]
        exact ⟨by linarith [z.property.1.1], by linarith [z.property.1.2]⟩
      · have him : (shift(a + z.val.2.1, z.val.2.2)).im = z.val.2.2 := by simp
        change (shift(a + z.val.2.1, z.val.2.2)).im ∈ Icc t₁ t₂
        rw [him]
        exact ⟨h1, h2.le⟩
    change MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) (χ ω)) _
      (shift(a + z.val.2.1, z.val.2.2)) ≠ 0
    rw [hΛ.divisor_apply hmem]
    have hpos : 0 < order(χ ω, shift(a + z.val.2.1, z.val.2.2)) := by
      have := z.property.2
      rwa [hω] at this
    have hne := spectralStripComponent_finite_window_order_ne_top (χ ω)
      (shift(a + z.val.2.1, z.val.2.2))
    cases h : order(χ ω, shift(a + z.val.2.1, z.val.2.2)) with
    | top => exact absurd h hne
    | coe k =>
      rw [h] at hpos
      have hk : 0 < k := by exact_mod_cast hpos
      simpa using hk.ne'
  · obtain ⟨hω, -, -⟩ := hz
    obtain ⟨hω', -, -⟩ := hz'
    have hre : a + z.val.2.1 = a + z'.val.2.1 := by simpa using congrArg Complex.re h
    have him : z.val.2.2 = z'.val.2.2 := by simpa using congrArg Complex.im h
    exact Subtype.ext (Prod.ext (hω.trans hω'.symm) (Prod.ext (add_left_cancel hre) him))

end RiemannMasullo
