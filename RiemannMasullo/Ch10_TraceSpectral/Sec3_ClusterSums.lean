module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3_TraceClass
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # Theorems 10.3.1.1(1) and 10.3.2.1(1) with the zeros summed by clusters

Parts (1) of Theorems 10.3.1.1 and 10.3.2.1, pp. 448 and 453, say that the finite sections of the
spectral convolution over the rectangles of an arbitrary enumeration of the zeros converge to it
in trace norm. In `Sec3` this rests on the recorded gap
`spectralStripConvolution_traceCauchy_compact_block_series` (#7241): a rectangle can cut through
a group of zeros that lie close together, and nothing bounds such a partial sum.

`Sec3_TraceClass` groups the zeros into finite clusters whose blocks have summable trace norms.
This file draws the conclusion in the form of parts (1): the finite sections over finite unions
of clusters converge to the convolution in trace norm, and so in every Schatten norm
(`spectralStripConvolution_clusters_traceNorm_tendsto`,
`spectralLineConvolution_clusters_traceNorm_tendsto`,
`SpectralClusterSumsTraceTendsto.schatten_tendsto`). The gap is not used. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

universe u

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Schatten norm of index `p ≥ 1` of a nuclear endomorphism is at most its trace norm:
its approximation numbers are at most their sum. -/
theorem schattenNorm_le_traceNorm (T : nuclearEndomorphisms H) (p : ℝ) (hp : 1 ≤ p) :
    ∃ h : T.val ∈ schattenClass H H p hp,
      schattenNorm (⟨T.val, h⟩ : schattenClass H H p hp) ≤ traceNorm T := by
  have hmem := (mem_traceClassOperators_iff_isNuclearOperator T.val).2 T.property
  have hsum : Summable (approximationNumber T.val) := by simpa using hmem.2
  have hnn (n : ℕ) : 0 ≤ approximationNumber T.val n :=
    Real.sInf_nonneg fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _
  have ht := schattenNorm_one_eq_traceNorm T
  simp only [schattenNorm, Real.rpow_one, div_one] at ht
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hs0 : 0 ≤ traceNorm T := by
    rw [← ht]
    exact tsum_nonneg hnn
  have hle (n : ℕ) : approximationNumber T.val n ≤ traceNorm T := by
    rw [← ht]
    exact hsum.le_tsum n fun m _ ↦ hnn m
  have hpow (n : ℕ) : approximationNumber T.val n ^ p ≤
      approximationNumber T.val n * traceNorm T ^ (p - 1) := by
    rcases (hnn n).eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow hp0.ne', zero_mul]
    · calc approximationNumber T.val n ^ p
          = approximationNumber T.val n ^ (1 + (p - 1)) := by rw [add_sub_cancel]
        _ = approximationNumber T.val n * approximationNumber T.val n ^ (p - 1) := by
          rw [Real.rpow_add hpos, Real.rpow_one]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hnn n) (hle n) (sub_nonneg.mpr hp)) (hnn n)
  have hsp : Summable (fun n ↦ approximationNumber T.val n ^ p) :=
    Summable.of_nonneg_of_le (fun n ↦ Real.rpow_nonneg (hnn n) p) hpow (hsum.mul_right _)
  refine ⟨⟨hmem.1, hsp⟩, ?_⟩
  have h1 : ∑' n, approximationNumber T.val n ^ p ≤ traceNorm T ^ p := by
    calc ∑' n, approximationNumber T.val n ^ p
        ≤ ∑' n, approximationNumber T.val n * traceNorm T ^ (p - 1) :=
          hsp.tsum_le_tsum hpow (hsum.mul_right _)
      _ = traceNorm T * traceNorm T ^ (p - 1) := by rw [tsum_mul_right, ht]
      _ = traceNorm T ^ p := by
          rcases hs0.eq_or_lt with h0 | hpos
          · rw [← h0, zero_mul, Real.zero_rpow hp0.ne']
          · conv_lhs => rw [← Real.rpow_one (traceNorm T)]
            rw [Real.rpow_one, ← Real.rpow_one_add' hs0 (by linarith), add_sub_cancel]
  calc schattenNorm (⟨T.val, ⟨hmem.1, hsp⟩⟩ : schattenClass H H p hp)
      = (∑' n, approximationNumber T.val n ^ p) ^ (1 / p) := rfl
    _ ≤ (traceNorm T ^ p) ^ (1 / p) := Real.rpow_le_rpow
        (tsum_nonneg fun n ↦ Real.rpow_nonneg (hnn n) p) h1 (by positivity)
    _ = traceNorm T := by
        rw [← Real.rpow_mul hs0, mul_one_div_cancel hp0.ne', Real.rpow_one]

/-- The trace norm of the negative of a nuclear endomorphism. -/
private theorem traceNorm_neg_eq (T : nuclearEndomorphisms H) : traceNorm (-T) = traceNorm T := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have h := (traceNorm_normedSpaceCore (H := H)).norm_smul (-1 : ℂ) T
  rw [← neg_one_smul ℂ T]
  simpa only [norm_neg, norm_one, one_mul] using h

/-- Paper: (10.3.1.23), p. 452, and (10.3.2.1), p. 453, for sums by clusters. The zeros can be
grouped into finite clusters `K i`, pairwise disjoint and covering all the zeros, so that the
finite sections of `A` over finite unions of clusters converge to `A` in trace norm: for every
finite set `C` of clusters the difference of the section over their union and `A` is nuclear,
and its trace norm tends to zero along the finite sets of clusters ordered by inclusion.
Reconstruction: The paper does not state this. Its statement is for the rectangles of an
arbitrary enumeration of the single zeros (`SpectralRectanglesTraceCauchy` of `Sec3`). Such a
rectangle can cut a cluster. The sums here do not. -/
def SpectralClusterSumsTraceTendsto {J : Type*} {Z : Type u} (A : H →L[ℂ] H) (x : J → H)
    (Λ : J → StrongDual ℂ H) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) : Prop :=
  ∃ (ι : Type u) (K : ι → Finset Z) (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)),
    (∀ z, ∃ i, z ∈ K i) ∧
    ∃ T : Finset ι → nuclearEndomorphisms H,
      (∀ C, (T C).val = spectralConvolutionFiniteSum A x Λ
        (C.disjiUnion K fun i _ j _ h ↦ hd i j h) N jet - A) ∧
      Tendsto (fun C ↦ traceNorm (T C)) atTop (𝓝 0)

/-- If the zeros are grouped into finite clusters, pairwise disjoint, whose blocks have summable
trace norms and sum to the operator in operator norm, then the finite sections over finite
unions of clusters converge to the operator in trace norm: the remainder is nuclear, and its
trace norm is at most the sum of the trace norms of the clusters left out. -/
private theorem spectralConvolutionFiniteSum_clusters_traceNorm_tendsto {J Z ι : Type*}
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (K : ι → Finset Z) (hdisj : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (R : ι → nuclearEndomorphisms H)
    (hR : ∀ i, (R i).val = spectralConvolutionFiniteSum A x Λ (K i) N jet)
    (hsum : Summable (fun i ↦ traceNorm (R i)))
    (hA : HasSum (fun i ↦ (R i).val) A) :
    ∃ T : Finset ι → nuclearEndomorphisms H,
      (∀ C, (T C).val = spectralConvolutionFiniteSum A x Λ
        (C.disjiUnion K fun i _ j _ h ↦ hdisj i j h) N jet - A) ∧
      Tendsto (fun C ↦ traceNorm (T C)) atTop (𝓝 0) := by
  classical
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hcore := traceNorm_normedSpaceCore (H := H)
  have hB (C : Finset ι) : spectralConvolutionFiniteSum A x Λ
      (C.disjiUnion K fun i _ j _ h ↦ hdisj i j h) N jet = ∑ i ∈ C, (R i).val := by
    simp only [hR]
    unfold spectralConvolutionFiniteSum
    exact Finset.sum_disjiUnion _ _ _
  have key (C : Finset ι) : ∃ h : IsNuclearOperator (A - ∑ i ∈ C, (R i).val),
      traceNorm ⟨_, h⟩ ≤ ∑' i, (↑C : Set ι)ᶜ.indicator (fun i ↦ traceNorm (R i)) i := by
    let S : ι → nuclearEndomorphisms H := fun i ↦ if i ∈ C then 0 else R i
    have h1 : HasSum (fun i ↦ if i ∈ C then (R i).val else 0) (∑ i ∈ C, (R i).val) := by
      have h : HasSum (fun i ↦ if i ∈ C then (R i).val else 0)
          (∑ i ∈ C, if i ∈ C then (R i).val else 0) :=
        hasSum_sum_of_ne_finset_zero fun i hi ↦ by simp [hi]
      have h2 : (∑ i ∈ C, if i ∈ C then (R i).val else 0) = ∑ i ∈ C, (R i).val :=
        Finset.sum_congr rfl fun i hi ↦ by simp [hi]
      rwa [h2] at h
    have hS : HasSum (fun i ↦ (S i).val) (A - ∑ i ∈ C, (R i).val) := by
      convert hA.sub h1 using 2 with i
      by_cases hi : i ∈ C <;> simp [S, hi]
    refine traceNorm_le_of_hasSum S _ hS _ (hsum.indicator _) fun i ↦ ?_
    by_cases hi : i ∈ C
    · have hz : traceNorm (0 : nuclearEndomorphisms H) = 0 := (hcore.norm_eq_zero_iff _).mpr rfl
      simp [S, hi, hz]
    · simp [S, hi]
  have hlim : Tendsto (fun C : Finset ι ↦
      ∑' i, (↑C : Set ι)ᶜ.indicator (fun i ↦ traceNorm (R i)) i) atTop (𝓝 0) := by
    refine (tendsto_tsum_compl_atTop_zero fun i ↦ traceNorm (R i)).congr fun C ↦ ?_
    exact tsum_subtype (↑C : Set ι)ᶜ fun i ↦ traceNorm (R i)
  refine ⟨fun C ↦ -⟨A - ∑ i ∈ C, (R i).val, (key C).choose⟩, fun C ↦ ?_, ?_⟩
  · rw [hB]
    exact neg_sub _ _
  · refine squeeze_zero (fun C ↦ hcore.norm_nonneg _) (fun C ↦ ?_) hlim
    rw [traceNorm_neg_eq]
    exact (key C).choose_spec


/-- Paper: (10.3.1.23), p. 452, and (10.3.2.1), p. 453, for sums by clusters. Clusters whose
blocks have summable trace norms and sum to the operator in operator norm give the convergence
of the sums by clusters in trace norm. -/
theorem spectralClusterSumsTraceTendsto_of_hasSum {J : Type*} {Z ι : Type u}
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (K : ι → Finset Z) (hdisj : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (hcover : ∀ z, ∃ i, z ∈ K i) (R : ι → nuclearEndomorphisms H)
    (hR : ∀ i, (R i).val = spectralConvolutionFiniteSum A x Λ (K i) N jet)
    (hsum : Summable (fun i ↦ traceNorm (R i)))
    (hA : HasSum (fun i ↦ (R i).val) A) :
    SpectralClusterSumsTraceTendsto A x Λ N jet :=
  ⟨ι, K, hdisj, hcover, spectralConvolutionFiniteSum_clusters_traceNorm_tendsto
    A x Λ N jet K hdisj R hR hsum hA⟩

/-- Paper: (10.3.1.23), p. 452, and (10.3.2.1), p. 453, for sums by clusters. A partition of the
zeros into finite clusters whose blocks have summable trace norms gives the convergence of the
sums by clusters in trace norm. The blocks sum to the operator in operator norm by
biorthogonality and totality of the coordinate functionals
(`spectralStripConvolution_nuclear_of_clusters_abstract` of `Sec3_Clusters`). -/
theorem spectralClusterSumsTraceTendsto_of_partition {J : Type*} {Z : Type u}
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x Λ)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (hjet : Bijective (fun j : (z : Z) × Fin (N z) ↦ jet j.1 j.2))
    (P : Set (Finset Z)) (R : P → nuclearEndomorphisms H) (hdisj : P.PairwiseDisjoint id)
    (hcover : ∀ z : Z, ∃ K ∈ P, z ∈ K)
    (hR : ∀ K : P, (R K).val = spectralConvolutionFiniteSum A x Λ K.val N jet)
    (hsum : Summable (fun K : P ↦ traceNorm (R K))) :
    SpectralClusterSumsTraceTendsto A x Λ N jet := by
  have hd : ∀ K L : P, K ≠ L → Disjoint K.val L.val := fun K L hKL ↦
    hdisj K.property L.property fun h ↦ hKL (Subtype.ext h)
  have hc : ∀ z : Z, ∃ K : P, z ∈ K.val := fun z ↦ by
    obtain ⟨K, hK, hz⟩ := hcover z
    exact ⟨⟨K, hK⟩, hz⟩
  obtain ⟨-, hA, -⟩ := spectralStripConvolution_nuclear_of_clusters_abstract
    A x Λ hb N jet hjet (fun K : P ↦ K.val) hd hc R hR hsum
  exact spectralClusterSumsTraceTendsto_of_hasSum A x Λ N jet (fun K : P ↦ K.val) hd hc R hR
    hsum hA

/-- An operator whose sums by clusters converge to it in trace norm is trace class. -/
theorem SpectralClusterSumsTraceTendsto.isNuclearOperator {J : Type*} {Z : Type u}
    {A : H →L[ℂ] H} {x : J → H} {Λ : J → StrongDual ℂ H} {N : Z → ℕ}
    {jet : (z : Z) → Fin (N z) → J} (h : SpectralClusterSumsTraceTendsto A x Λ N jet) :
    IsNuclearOperator A := by
  obtain ⟨ι, K, hd, -, T, hT, -⟩ := h
  have h0 : (-(T ∅)).val = A := by
    change -(T ∅).val = A
    rw [hT ∅]
    simp [spectralConvolutionFiniteSum]
  exact h0 ▸ (-(T ∅)).property

/-- Paper: (10.3.1.23), p. 452, and (10.3.2.1), p. 453, for sums by clusters. If the sums by
clusters converge in trace norm, they converge in every Schatten norm: the finite sections over
finite unions of clusters and the operator lie in every Schatten class of index `p ≥ 1`, and
the Schatten norm of their difference tends to zero. This is the conclusion of
`spectralConvolutionFiniteSum_limit_of_traceCauchy` of `Sec3` with the rectangles of an
enumeration replaced by the finite unions of clusters. -/
theorem SpectralClusterSumsTraceTendsto.schatten_tendsto {J : Type*} {Z : Type u}
    {A : H →L[ℂ] H} {x : J → H} {Λ : J → StrongDual ℂ H} {N : Z → ℕ}
    {jet : (z : Z) → Fin (N z) → J} (h : SpectralClusterSumsTraceTendsto A x Λ N jet) :
    ∃ (ι : Type u) (K : ι → Finset Z) (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)),
      (∀ z, ∃ i, z ∈ K i) ∧ ∀ (p : ℝ) (hp : 1 ≤ p),
        let B (C : Finset ι) := spectralConvolutionFiniteSum A x Λ
          (C.disjiUnion K fun i _ j _ h ↦ hd i j h) N jet
        let S := schattenClass H H p hp
        ∃ (hA : A ∈ S) (hB : ∀ C, B C ∈ S),
          Tendsto (fun C ↦ schattenNorm (E := H) (F := H) (p := p) (hp := hp)
            (⟨B C, hB C⟩ - ⟨A, hA⟩ : S)) atTop (𝓝 0) := by
  obtain ⟨ι, K, hd, hc, T, hT, hlim⟩ := h
  refine ⟨ι, K, hd, hc, fun p hp ↦ ?_⟩
  intro B S
  have hB (C : Finset ι) : B C ∈ S :=
    S.sum_mem fun z _ ↦ S.sum_mem fun m _ ↦ smulRight_mem_schattenClass hp _ _
  have hmem (C : Finset ι) : B C - A ∈ S := by
    rw [← hT C]
    exact (schattenNorm_le_traceNorm (T C) p hp).choose
  have hA' : A ∈ S := by
    simpa only [sub_sub_cancel] using S.sub_mem (hB ∅) (hmem ∅)
  refine ⟨hA', hB, squeeze_zero (fun C ↦ ?_) (fun C ↦ ?_) hlim⟩
  · have hnn (D : H →L[ℂ] H) (n : ℕ) : 0 ≤ approximationNumber D n :=
      Real.sInf_nonneg fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _
    exact Real.rpow_nonneg (tsum_nonneg fun n ↦ Real.rpow_nonneg (hnn _ n) p) _
  · have heq : (⟨B C, hB C⟩ - ⟨A, hA'⟩ : S) = ⟨(T C).val, hT C ▸ hmem C⟩ :=
      Subtype.ext (hT C).symm
    rw [heq]
    exact (schattenNorm_le_traceNorm (T C) p hp).choose_spec

/-- Relabeling a biorthogonal system by a bijection preserves its two dense spans. -/
private theorem spectralMarkushevichBasis_reindex
    {I J E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (r : J ≃ I)
    (x : I → E) (f : I → StrongDual ℂ E) (h : IsSpectralMarkushevichBasis x f) :
    IsSpectralMarkushevichBasis (x ∘ r) (f ∘ r) := by
  refine ⟨fun j ↦ h.1 (r j), fun i j hij ↦ h.2.1 _ _ (r.injective.ne hij), ?_, ?_⟩
  · simpa only [r.surjective.range_comp] using h.2.2.1
  · simpa only [r.surjective.range_comp] using h.2.2.2

/-- Relabeling both the zeros and their derivative indices carries the finite section over a
set of zeros to the finite section over its image. -/
private theorem spectralConvolutionFiniteSum_map_reindex
    {I J Z W E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (r : J ≃ I) (u : W ≃ Z) (A : E →L[ℂ] E)
    (x : I → E) (f : I → StrongDual ℂ E) (N : Z → ℕ) (M : W → ℕ)
    (i : (z : Z) → Fin (N z) → I) (j : (w : W) → Fin (M w) → J)
    (hN : ∀ w, M w = N (u w)) (hj : ∀ w m, r (j w m) = i (u w) (Fin.cast (hN w) m))
    (k : Finset W) :
    spectralConvolutionFiniteSum A (x ∘ r) (f ∘ r) k M j =
      spectralConvolutionFiniteSum A x f (k.map u.toEmbedding) N i := by
  unfold spectralConvolutionFiniteSum
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  apply Fintype.sum_equiv (finCongr (hN w))
  intro m
  simp only [Function.comp_apply, hj, finCongr_apply, Equiv.coe_toEmbedding]

/-- Relabeling both the zeros and their derivative indices by bijections carries the convergence
of the sums by clusters from one labelling to the other. -/
theorem SpectralClusterSumsTraceTendsto.reindex {I J : Type*} {Z W : Type u}
    (r : J ≃ I) (u : W ≃ Z) (A : H →L[ℂ] H)
    (x : I → H) (f : I → StrongDual ℂ H) (N : Z → ℕ) (M : W → ℕ)
    (i : (z : Z) → Fin (N z) → I) (j : (w : W) → Fin (M w) → J)
    (hN : ∀ w, M w = N (u w)) (hj : ∀ w m, r (j w m) = i (u w) (Fin.cast (hN w) m))
    (h : SpectralClusterSumsTraceTendsto A (x ∘ r) (f ∘ r) M j) :
    SpectralClusterSumsTraceTendsto A x f N i := by
  obtain ⟨ι, K, hd, hc, T, hT, hlim⟩ := h
  refine ⟨ι, fun a ↦ (K a).map u.toEmbedding,
    fun a b hab ↦ (Finset.disjoint_map _).mpr (hd a b hab), fun z ↦ ?_, T, fun C ↦ ?_, hlim⟩
  · obtain ⟨a, ha⟩ := hc (u.symm z)
    exact ⟨a, Finset.mem_map.mpr ⟨u.symm z, ha, u.apply_symm_apply z⟩⟩
  · rw [hT C, spectralConvolutionFiniteSum_map_reindex r u A x f N M i j hN hj]
    exact congrArg (fun k ↦ spectralConvolutionFiniteSum A x f k N i - A) Finset.disjiUnion_map

end Abstract

variable {F : Type u} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "Q(" a ", " hI ", " hs ")" => spectralSobolevQuotient F a hI hs
local notation "h₀" => le_rfl (a := (0 : ℝ))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat

-- Select the norm topology directly when using the locally convex nuclear ideal, as in `Sec3`.
attribute [local instance] instSpectralQuotientPolynormableSec3

variable (a : ℝ)

section Strip

local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

/-- Paper: Theorem 10.3.2.1(1) and (10.3.2.1), p. 453, with the zeros summed by clusters. For
every choice of the unitary extensions of the norm-one characters and every Markushevich basis
realizing the strip jets, the zeros of the strip can be grouped into finite clusters, pairwise
disjoint and covering all the zeros, so that the finite sections of the spectral convolution
over finite unions of clusters converge to it in trace norm. Convergence in every Schatten norm
follows (`SpectralClusterSumsTraceTendsto.schatten_tendsto`).
It is proved from `spectralStripConvolution_summable_clusterTraceNorms_forall`, so it does not
use the recorded gap #7241 and no distance between two zeros enters.
Reconstruction: The paper does not state this. Theorem 10.3.2.1(1) asserts the convergence for
the rectangles of an arbitrary enumeration of the single zeros
(`spectralStripConvolution_traceCauchy` of `Sec3`, which rests on the gap). Such a rectangle
can cut a cluster. This is the same convergence for the sums that do not.
Deviation: Stated for every Sobolev order `s ≥ 0`. §10.3 of the paper assumes `s > 1`
(p. 455). -/
theorem spectralStripConvolution_clusters_traceNorm_tendsto
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s →
      StrongDual ℂ Q(a, hStrip(hα), hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    SpectralClusterSumsTraceTendsto (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ
      (fun z : Z(χ, α) ↦ N(χ, α, s, z))
      (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩) := by
  obtain ⟨P, R, hdisj, hcover, hR, hsum⟩ :=
    spectralStripConvolution_summable_clusterTraceNorms_forall a hα hs φ χ hχ x Λ hb hj
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
  exact spectralClusterSumsTraceTendsto_of_partition
    (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ hb count jet equiv.bijective
    P R hdisj hcover hR hsum

end Strip

section Line

local notation "Z(" χ ")" => {z : PontryaginDual C₁ × ℝ // 0 < order(χ z.1, shift(a, z.2))}
local notation "N(" χ ", " s ", " z ")" => spectralBoundaryMultiplicity s (mult(χ (z).val.1,
  shift(a, (z).val.2)))

/-- Paper: Theorem 10.3.1.1(1) and (10.3.1.1), p. 448, with the zeros summed by clusters. For
every choice of the unitary extensions of the norm-one characters and every Markushevich basis
realizing the jets on the line, the zeros on the line can be grouped into finite clusters,
pairwise disjoint and covering all the zeros, so that the finite sections of the spectral
convolution over finite unions of clusters converge to it in trace norm. Convergence in every
Schatten norm follows (`SpectralClusterSumsTraceTendsto.schatten_tendsto`).
It is the strip statement `spectralStripConvolution_clusters_traceNorm_tendsto` at width zero,
where every strip zero lies on the line and has the same boundary multiplicity. It does not use
the recorded gap #7241.
Reconstruction: The paper does not state this. Theorem 10.3.1.1(1) asserts the convergence for
the rectangles of an arbitrary enumeration of the single zeros
(`spectralLineConvolution_traceCauchy` of `Sec3`, which rests on the gap). -/
theorem spectralLineConvolution_clusters_traceNorm_tendsto
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (x : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s → Q(a, h₀, hs₀(hs)))
    (Λ : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) (fun ω ↦ χ ω) hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2)) :
    SpectralClusterSumsTraceTendsto (spectralConvolution (F := F) a h₀ hs₀(hs) φ) x Λ
      (fun z : Z(χ) ↦ N(χ, s, z))
      (fun z m ↦ ⟨(z.val.1, z.val.2, m.val), m.isLt⟩) := by
  let Z₀ := {z : PontryaginDual C₁ × ℝ × ℝ //
    z.2.1 ∈ Icc (-(0 : ℝ)) 0 ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
  have hz (z : Z₀) : z.val.2.1 = 0 := by simpa using z.property.1
  let zeros : Z₀ ≃ Z(χ) :=
    { toFun := fun z ↦ ⟨(z.val.1, z.val.2.2), by simpa only [hz z, add_zero] using z.property.2⟩
      invFun := fun z ↦ ⟨(z.val.1, 0, z.val.2), by simp, by simpa only [add_zero] using z.property⟩
      left_inv := fun z ↦ Subtype.ext (Prod.ext rfl (Prod.ext (hz z).symm rfl))
      right_inv := fun _ ↦ Subtype.ext rfl }
  let J := SpectralStripJetIndex (F := F) χ a 0 s
  have hzero (j : J) : j.val.2.1 = 0 := by
    simpa using (SpectralStripJetIndex.mem_strip_order_pos h₀ j).1
  have hbound (k : ℕ) : spectralStripMultiplicity 0 s 0 k = spectralBoundaryMultiplicity s k :=
    spectralStripMultiplicity_boundary le_rfl (Or.inr rfl) s k
  let jets : J ≃ SpectralLineJetIndex (F := F) χ a s :=
    { toFun := fun j ↦ ⟨(j.val.1, j.val.2.2.1, j.val.2.2.2), by
        simpa only [hzero j, add_zero, hbound] using j.property⟩
      invFun := fun i ↦ ⟨(i.val.1, 0, i.val.2.1, i.val.2.2), by
        simpa only [add_zero, hbound] using i.property⟩
      left_inv := fun j ↦ Subtype.ext (Prod.ext rfl (Prod.ext (hzero j).symm rfl))
      right_inv := fun _ ↦ Subtype.ext rfl }
  let lineCount (z : Z(χ)) := N(χ, s, z)
  let stripCount (w : Z₀) := spectralStripMultiplicity 0 s w.val.2.1 (mult(χ w.val.1,
    shift(a + w.val.2.1, w.val.2.2)))
  have hm (w : Z₀) : stripCount w = lineCount (zeros w) := by
    simp only [stripCount, lineCount, zeros, Equiv.coe_fn_mk, hz w, add_zero, hbound]
  let lineJet (z : Z(χ)) (m : Fin (lineCount z)) : SpectralLineJetIndex (F := F) χ a s :=
    ⟨(z.val.1, z.val.2, m.val), m.isLt⟩
  let stripJet (w : Z₀) (m : Fin (stripCount w)) : J :=
    ⟨(w.val.1, w.val.2.1, w.val.2.2, m.val), m.isLt⟩
  let raw (k : SpectralLineJetIndex (F := F) χ a s) :=
    spectralZeroJet (F := F) (χ k.val.1) 0 k.val.2.1 k.val.2.2
  -- Vary the lower endpoint to transport the quotient and its dual embedding together.
  let claim (l : ℝ) (hl : l ≤ 0) :=
    ∀ (X : SpectralLineJetIndex (F := F) χ a s → Q(a, hl, hs₀(hs)))
      (L : SpectralLineJetIndex (F := F) χ a s → StrongDual ℂ Q(a, hl, hs₀(hs))),
      IsSpectralMarkushevichBasis X L →
      ∀ (hv : ∀ k, MemLp (raw k) 2 _),
      (∀ k, spectralSobolevDualEmbedding F a hl hs₀(hs) (L k) = (hv k).toLp (raw k)) →
      SpectralClusterSumsTraceTendsto (spectralConvolution (F := F) a hl hs₀(hs) φ) X L
        lineCount lineJet
  suffices claim 0 h₀ from this x Λ hb (spectralLineJet_memLp (F := F) χ hs) hj
  suffices claim (-0) hStrip(h₀) by simpa only [neg_zero] using this
  intro X L hb hv hj
  have strip := spectralStripConvolution_clusters_traceNorm_tendsto (F := F) a h₀ hs₀(hs) φ χ hχ
    (X ∘ jets) (L ∘ jets) (spectralMarkushevichBasis_reindex jets X L hb) (by
      rintro ⟨⟨ω, b, t, k⟩, hk⟩
      obtain rfl : b = 0 := hzero ⟨(ω, b, t, k), hk⟩
      exact hj (jets ⟨(ω, 0, t, k), hk⟩))
  exact strip.reindex jets zeros _ X L lineCount stripCount lineJet stripJet hm
    (fun _ _ ↦ Subtype.ext rfl)

end Line

end RiemannMasullo
