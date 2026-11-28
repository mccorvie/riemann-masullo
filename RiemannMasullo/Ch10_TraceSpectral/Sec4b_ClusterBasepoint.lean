module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_ClusterLine
import RiemannMasullo.Ch10_TraceSpectral.Sec3_BasepointChoice
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # Theorem 10.4.3.5 on the line, by clusters, for every choice of the unitary extensions

`Sec4b_ClusterLine` proves the cluster form of the estimate for the geometric component of
Theorem 10.4.3.5(2), pp. 472–473, on the line, for one choice of the unitary extensions of the
norm-one characters (Notation 10.2.1.1, p. 440): the choice of a norm section. This file
carries it to every choice.

Two choices differ on each angular component by an imaginary power of the norm, so the zeros
and the jets written in the chart of one choice are those of the other with the heights of
each component translated. `Sec3_BasepointChoice` gives the two bijections. The quotient, the
convolutions and the two projections do not depend on the choice, so the tensor sums and the
block sums over a set of zeros are the same sums after relabelling
(`spectralKernelSum_map_equiv`, `spectralJetBlockSum_map_equiv`), and clusters for one choice
are carried to clusters for the other
(`spectralStripGeometricBlocks_clusters_of_basepointChoice`).

`spectralStripGeometricBlocks_clusters_bddAbove_of_rpowDensity_of_basepointChoice` is the
resulting statement at width zero, for every order, every test and every choice.
`Sec4b_Isolated` draws the convergence of the ambient kernel tensors from it. -/

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

section Relabel

variable {J J' E G W H ι : Type*} {Z Z' : Type u}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Reindexing one tensor sum along bijections of the zeros and of the jets. The jets are
indexed by a natural number below the multiplicity, so that no cast between the index sets of
two multiplicities enters. -/
theorem spectralKernelSum_map_equiv (eZ : Z' ≃ Z) (eJ : J' ≃ J) (N : Z → ℕ) (N' : Z' → ℕ)
    (hN : ∀ z', N' z' = N (eZ z'))
    (jet : (z : Z) → (m : ℕ) → m < N z → J) (jet' : (z' : Z') → (m : ℕ) → m < N' z' → J')
    (hjet : ∀ z' (m : ℕ) (hm : m < N' z') (hm' : m < N (eZ z')),
      eJ (jet' z' m hm) = jet (eZ z') m hm')
    (u' : J' → E) (v' : J' → G) (K' : Finset Z') :
    spectralKernelSum (K'.map eZ.toEmbedding) N (fun z m ↦ jet z m.val m.isLt)
        (u' ∘ eJ.symm) (v' ∘ eJ.symm) =
      spectralKernelSum K' N' (fun z' m ↦ jet' z' m.val m.isLt) u' v' := by
  unfold spectralKernelSum
  apply congrArg ((↑) : ProjectiveTensor E G → Π(E, G))
  change (∑ z ∈ K'.map eZ.toEmbedding, ∑ m : Fin (N z),
      u' (eJ.symm (jet z m.val m.isLt)) ⊗ₜ[ℂ] v' (eJ.symm (jet z m.val m.isLt)) : E ⊗[ℂ] G) =
    ∑ z' ∈ K', ∑ m : Fin (N' z'), u' (jet' z' m.val m.isLt) ⊗ₜ[ℂ] v' (jet' z' m.val m.isLt)
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun z' _ ↦ ?_
  refine (Fintype.sum_equiv (finCongr (hN z')) _ _ fun m ↦ ?_).symm
  have hj : eJ.symm (jet (eZ z') (finCongr (hN z') m).val (finCongr (hN z') m).isLt) =
      jet' z' m.val m.isLt :=
    (Equiv.symm_apply_eq eJ).mpr (hjet z' m.val m.isLt (finCongr (hN z') m).isLt).symm
  change _ = u' (eJ.symm (jet (eZ z') (finCongr (hN z') m).val (finCongr (hN z') m).isLt)) ⊗ₜ[ℂ]
    v' (eJ.symm (jet (eZ z') (finCongr (hN z') m).val (finCongr (hN z') m).isLt))
  rw [hj]

/-- Reindexing one sum of jet blocks along bijections of the zeros and of the jets. -/
theorem spectralJetBlockSum_map_equiv (q : W →L[ℂ] H) (eZ : Z' ≃ Z) (eJ : J' ≃ J) (N : Z → ℕ)
    (N' : Z' → ℕ) (hN : ∀ z', N' z' = N (eZ z'))
    (jet : (z : Z) → (m : ℕ) → m < N z → J) (jet' : (z' : Z') → (m : ℕ) → m < N' z' → J')
    (hjet : ∀ z' (m : ℕ) (hm : m < N' z') (hm' : m < N (eZ z')),
      eJ (jet' z' m hm) = jet (eZ z') m hm')
    (f' : J' → StrongDual ℂ H) (w' : J' → W) (K' : Finset Z') :
    spectralJetBlockSum q N (fun z m ↦ jet z m.val m.isLt) (f' ∘ eJ.symm) (w' ∘ eJ.symm)
        (K'.map eZ.toEmbedding) =
      spectralJetBlockSum q N' (fun z' m ↦ jet' z' m.val m.isLt) f' w' K' := by
  unfold spectralJetBlockSum
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun z' _ ↦ ?_
  refine (Fintype.sum_equiv (finCongr (hN z')) _ _ fun m ↦ ?_).symm
  have hj : eJ.symm (jet (eZ z') (finCongr (hN z') m).val (finCongr (hN z') m).isLt) =
      jet' z' m.val m.isLt :=
    (Equiv.symm_apply_eq eJ).mpr (hjet z' m.val m.isLt (finCongr (hN z') m).isLt).symm
  apply Subtype.ext
  change _ = ((f' (eJ.symm (jet (eZ z') (finCongr (hN z') m).val
    (finCongr (hN z') m).isLt))).comp q).smulRight
      (w' (eJ.symm (jet (eZ z') (finCongr (hN z') m).val (finCongr (hN z') m).isLt)))
  rw [hj]

/-- The union of clusters carried back along a bijection of the zeros, carried forward again,
is the union of the clusters. -/
theorem map_disjiUnion_map_symm (eZ : Z' ≃ Z) (K : ι → Finset Z)
    (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (hd' : ∀ i j, i ≠ j →
      Disjoint ((K i).map eZ.symm.toEmbedding) ((K j).map eZ.symm.toEmbedding))
    (C : Finset ι) :
    (C.disjiUnion (fun i ↦ (K i).map eZ.symm.toEmbedding) fun i _ j _ h ↦ hd' i j h).map
        eZ.toEmbedding = C.disjiUnion K fun i _ j _ h ↦ hd i j h := by
  ext z
  constructor
  · intro hz
    obtain ⟨z', hz', rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨i, hi, hzi⟩ := Finset.mem_disjiUnion.mp hz'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hzi
    refine Finset.mem_disjiUnion.mpr ⟨i, hi, ?_⟩
    change eZ (eZ.symm y) ∈ K i
    rwa [Equiv.apply_symm_apply]
  · intro hz
    obtain ⟨i, hi, hzi⟩ := Finset.mem_disjiUnion.mp hz
    exact Finset.mem_map.mpr ⟨eZ.symm z,
      Finset.mem_disjiUnion.mpr ⟨i, hi, Finset.mem_map.mpr ⟨z, hzi, rfl⟩⟩,
      eZ.apply_symm_apply z⟩

/-- Clusters along which tensor sums converge and block sums are bounded in trace norm are
carried along bijections of the zeros and of the jets. Nothing is used about the zeros except
the two bijections. -/
theorem spectralClusters_tendstoAlong_bddAbove_map_equiv (q : W →L[ℂ] H) (eZ : Z' ≃ Z)
    (eJ : J' ≃ J) (N : Z → ℕ) (N' : Z' → ℕ) (hN : ∀ z', N' z' = N (eZ z'))
    (jet : (z : Z) → (m : ℕ) → m < N z → J) (jet' : (z' : Z') → (m : ℕ) → m < N' z' → J')
    (hjet : ∀ z' (m : ℕ) (hm : m < N' z') (hm' : m < N (eZ z')),
      eJ (jet' z' m hm) = jet (eZ z') m hm')
    (u' : J' → E) (v' : J' → G) (f' : J' → StrongDual ℂ H) (w' : J' → W)
    (h : ∃ (K : ι → Finset Z) (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)),
      (∀ z, ∃ i, z ∈ K i) ∧
      (∃ κT : Π(E, G), SpectralKernelSumsTendstoAlong K hd N (fun z m ↦ jet z m.val m.isLt)
        (u' ∘ eJ.symm) (v' ∘ eJ.symm) κT) ∧
      BddAbove (range fun C : Finset ι ↦ traceNorm
        (spectralJetBlockSum q N (fun z m ↦ jet z m.val m.isLt) (f' ∘ eJ.symm) (w' ∘ eJ.symm)
          (C.disjiUnion K fun i _ j _ h ↦ hd i j h)))) :
    ∃ (K' : ι → Finset Z') (hd' : ∀ i j, i ≠ j → Disjoint (K' i) (K' j)),
      (∀ z', ∃ i, z' ∈ K' i) ∧
      (∃ κT : Π(E, G), SpectralKernelSumsTendstoAlong K' hd' N'
        (fun z' m ↦ jet' z' m.val m.isLt) u' v' κT) ∧
      BddAbove (range fun C : Finset ι ↦ traceNorm
        (spectralJetBlockSum q N' (fun z' m ↦ jet' z' m.val m.isLt) f' w'
          (C.disjiUnion K' fun i _ j _ h ↦ hd' i j h))) := by
  obtain ⟨K, hd, hc, ⟨κT, hT⟩, hB⟩ := h
  have hd' : ∀ i j, i ≠ j →
      Disjoint ((K i).map eZ.symm.toEmbedding) ((K j).map eZ.symm.toEmbedding) :=
    fun i j hij ↦ (Finset.disjoint_map eZ.symm.toEmbedding).mpr (hd i j hij)
  have hmap := map_disjiUnion_map_symm eZ K hd hd'
  refine ⟨fun i ↦ (K i).map eZ.symm.toEmbedding, hd', fun z' ↦ ?_, ⟨κT, ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := hc (eZ z')
    exact ⟨i, Finset.mem_map.mpr ⟨eZ z', hi, eZ.symm_apply_apply z'⟩⟩
  · unfold SpectralKernelSumsTendstoAlong at hT ⊢
    refine hT.congr fun C ↦ ?_
    rw [← hmap C]
    exact spectralKernelSum_map_equiv eZ eJ N N' hN jet jet' hjet u' v' _
  · refine (bddAbove_def.mpr ?_)
    obtain ⟨B, hB⟩ := bddAbove_def.mp hB
    refine ⟨B, ?_⟩
    rintro _ ⟨C, rfl⟩
    have h1 : traceNorm (spectralJetBlockSum q N (fun z m ↦ jet z m.val m.isLt) (f' ∘ eJ.symm)
        (w' ∘ eJ.symm) (C.disjiUnion K fun i _ j _ h ↦ hd i j h)) ≤ B := hB _ ⟨C, rfl⟩
    rw [← hmap C] at h1
    rwa [spectralJetBlockSum_map_equiv q eZ eJ N N' hN jet jet' hjet f' w' _] at h1

end Relabel

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
local notation "Pgeom(" a ", " hα ", " hs ")" => geometricProjection (F := F) a hα hs

section Clusters

variable (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)

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

/-- Paper: Notation 10.2.1.1, p. 440, and Theorem 10.4.3.5(2), pp. 472–473, with the zeros
summed by clusters. The cluster form of the estimate does not depend on the choice of the
unitary extensions of the norm-one characters. Suppose that for one choice `χ` and every
Markushevich basis realizing its strip jets there are clusters, indexed by `ι`, pairwise
disjoint and covering the zeros, along which the printed tensors (10.4.3.43) converge and the
sums of the geometric blocks over finite unions of clusters are bounded in trace norm. Then the
same holds for every other choice `χ'`. Two choices differ on each component by an imaginary
power of the norm, so the zeros and the jets of one are those of the other with the heights of
each component translated
(`spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_relabel` of
`Sec3_BasepointChoice`); the clusters, the tensor sums and the block sums are carried along
this relabelling.
Reconstruction: The paper does not state this. -/
theorem spectralStripGeometricBlocks_clusters_of_basepointChoice
    (φ : BruhatCompactSupport C𝔽) (χ χ' : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (hχ' : IsSpectralBasepointChoice χ') {ι : Type*}
    (h : ∀ (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
        (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs))),
        Bases(χ, x, f) →
        ∃ (K : ι → Finset Z(χ)) (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)),
          (∀ z, ∃ i, z ∈ K i) ∧
          (∃ κT : Π(W'(α, s), W(α, s)),
            SpectralKernelSumsTendstoAlong K hd (fun z : Z(χ) ↦ N(χ, z))
              (fun z m ↦ jet(z, m)) (fun j ↦ D ((f j).comp (Aq(a, hα, hs₀(hs), φ))))
              (fun j ↦ S(a, hα, hs₀(hs)) (x j)) κT) ∧
          BddAbove (range fun C : Finset ι ↦ traceNorm
            (spectralJetBlockSum Q(a, hα, hs₀(hs)) (fun z : Z(χ) ↦ N(χ, z))
              (fun z m ↦ jet(z, m)) f
              (fun j ↦ Pgeom(a, hα, hs₀(hs))
                ((A(hα, hs₀(hs), φ) : W(α, s) →L[ℂ] W(α, s)) (S(a, hα, hs₀(hs)) (x j))))
              (C.disjiUnion K fun i _ j _ h ↦ hd i j h))))
    (x' : SpectralStripJetIndex χ' a α s → H(a, hα, hs₀(hs)))
    (f' : SpectralStripJetIndex χ' a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (hb' : Bases(χ', x', f')) :
    ∃ (K' : ι → Finset Z(χ')) (hd' : ∀ i j, i ≠ j → Disjoint (K' i) (K' j)),
      (∀ z, ∃ i, z ∈ K' i) ∧
      (∃ κT : Π(W'(α, s), W(α, s)),
        SpectralKernelSumsTendstoAlong K' hd' (fun z : Z(χ') ↦ N(χ', z))
          (fun z m ↦ jet(z, m)) (fun j ↦ D ((f' j).comp (Aq(a, hα, hs₀(hs), φ))))
          (fun j ↦ S(a, hα, hs₀(hs)) (x' j)) κT) ∧
      BddAbove (range fun C : Finset ι ↦ traceNorm
        (spectralJetBlockSum Q(a, hα, hs₀(hs)) (fun z : Z(χ') ↦ N(χ', z))
          (fun z m ↦ jet(z, m)) f'
          (fun j ↦ Pgeom(a, hα, hs₀(hs))
            ((A(hα, hs₀(hs), φ) : W(α, s) →L[ℂ] W(α, s)) (S(a, hα, hs₀(hs)) (x' j))))
          (C.disjiUnion K' fun i _ j _ h ↦ hd' i j h))) :=
  (spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_relabel a χ χ' hχ hχ'
    α s).elim fun eZ hrel ↦ hrel.elim fun eJ hrel ↦
      spectralClusters_tendstoAlong_bddAbove_map_equiv Q(a, hα, hs₀(hs)) eZ eJ
        (fun z ↦ N(χ, z)) (fun z ↦ N(χ', z)) hrel.1
        (fun z m hm ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m), hm⟩)
        (fun z m hm ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m), hm⟩) hrel.2.1
        (fun j ↦ D ((f' j).comp (Aq(a, hα, hs₀(hs), φ)))) (fun j ↦ S(a, hα, hs₀(hs)) (x' j)) f'
        (fun j ↦ Pgeom(a, hα, hs₀(hs))
          ((A(hα, hs₀(hs), φ) : W(α, s) →L[ℂ] W(α, s)) (S(a, hα, hs₀(hs)) (x' j))))
        (h (x' ∘ eJ.symm) (f' ∘ eJ.symm)
          ⟨spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_basis hb'.1
            eJ.symm, fun j ↦ (hb'.2 (eJ.symm j)).trans
              (MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (hrel.2.2 j)))⟩)

/-- Paper: Theorem 10.4.3.5(2), pp. 472–473, on the line at every order, for every test and
every choice of the unitary extensions of the norm-one characters, with the zeros summed by
clusters. Let the density of the Sobolev space be `(1 + t ^ 2) ^ σ` for a real `σ`; this is
the line, width zero, at the order `s = 2 σ` (`intervalSobolevDensity_width_zero`). For every
test `φ`, every choice `χ` and every Markushevich basis realizing the strip jets of `χ`, the
zeros can be grouped into finite clusters, pairwise disjoint and covering all the zeros, along
which
* the printed tensors (10.4.3.43), with convolution on the input factor, converge in the
  completed projective tensor product, and
* the sums of the geometric blocks `R_z` of `spectralStripGeometricKernel_blocks_bddAbove` of
  `Sec4b_Isolated` over finite unions of clusters are bounded in trace norm.
This is `spectralStripGeometricBlocks_clusters_bddAbove_of_rpowDensity` of `Sec4b_ClusterLine`,
which holds for the choice of a norm section, carried to `χ` by
`spectralStripGeometricBlocks_clusters_of_basepointChoice`.
Reconstruction: The paper does not state this. For positive widths the estimate of the
geometric component stays open; that is the recorded gap #7406.
Deviation: Stated for sums over unions of whole clusters. -/
theorem spectralStripGeometricBlocks_clusters_bddAbove_of_rpowDensity_of_basepointChoice
    (σ : ℝ) (hdens : ∀ t, intervalSobolevDensity (-α) α s t = (1 + t ^ 2) ^ σ)
    (φ : BruhatCompactSupport C𝔽) (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (hb : Bases(χ, x, f)) :
    ∃ (K : PontryaginDual C₁ × ℤ → Finset Z(χ))
      (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)),
      (∀ z, ∃ i, z ∈ K i) ∧
      (∃ κT : Π(W'(α, s), W(α, s)),
        SpectralKernelSumsTendstoAlong K hd (fun z : Z(χ) ↦ N(χ, z))
          (fun z m ↦ jet(z, m)) (fun j ↦ D ((f j).comp (Aq(a, hα, hs₀(hs), φ))))
          (fun j ↦ S(a, hα, hs₀(hs)) (x j)) κT) ∧
      BddAbove (range fun C : Finset (PontryaginDual C₁ × ℤ) ↦ traceNorm
        (spectralJetBlockSum Q(a, hα, hs₀(hs)) (fun z : Z(χ) ↦ N(χ, z))
          (fun z m ↦ jet(z, m)) f
          (fun j ↦ Pgeom(a, hα, hs₀(hs))
            ((A(hα, hs₀(hs), φ) : W(α, s) →L[ℂ] W(α, s)) (S(a, hα, hs₀(hs)) (x j))))
          (C.disjiUnion K fun i _ j _ h ↦ hd i j h))) :=
  (spectralStripGeometricBlocks_clusters_bddAbove_of_rpowDensity a hα hs σ hdens φ).elim
    fun χ₀ h ↦ spectralStripGeometricBlocks_clusters_of_basepointChoice a hα hs φ χ₀ χ h.1 hχ
      h.2 x f hb

end Clusters

end RiemannMasullo
