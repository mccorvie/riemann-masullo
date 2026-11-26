module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # The clustered block series does not depend on the basepoint choice

The zeros of the strip, their surviving multiplicities and their jets are written in the chart
of a choice `χ` of unitary extensions of the norm-one characters (Notation 10.2.1.1). Two
choices differ on each angular component by an imaginary power of the norm, so everything for
one choice is everything for the other with the heights of each component translated. The
statement that the zeros can be grouped into finite clusters whose blocks of the spectral
convolution have summable trace norms is carried along this relabelling: if it holds for one
choice, it holds for every choice.

The orders of the completed `L`-functions are compared through
`isLeast_globalThetaMellinIntegral_orders`, which describes their positive parts by the
quasi-characters alone; no identity between two `L`-functions is used.
-/

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

-- Select the norm topology directly when using the locally convex nuclear ideal, as in `Sec3`.
attribute [local instance] instSpectralQuotientPolynormableSec3

/-- The completed `L`-function of a unitary character has finite order at every point. -/
private theorem spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_ne_top
    (ψ : PontryaginDual C𝔽) (z : ℂ) : order(ψ, z) ≠ ⊤ := by
  obtain ⟨hΛ, hval⟩ := continuedCompletedHeckeL_spec ψ
  have h2 : order(ψ, (2 : ℂ)) ≠ ⊤ := fun htop ↦ by
    have hbad := completedHeckeL_continuation_zeros ψ _ hΛ hval (by norm_num : 0 < (2 : ℂ).re)
      (by rw [htop]; exact WithTop.coe_lt_top 0)
    norm_num at hbad
  exact hΛ.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ _) (mem_univ z) h2

/-- Two choices of the unitary extension of a norm-one character differ by an imaginary power
of the norm: their norm twists are translates of each other along the imaginary axis. -/
private theorem spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_twist
    (χ χ' : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    (hχ' : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ' ω)) (ω : PontryaginDual C₁) :
    ∃ τ : ℝ, ∀ z : ℂ, ideleClassNormTwist (F := F) (χ' ω) z =
      ideleClassNormTwist (χ ω) ((τ : ℂ) * Complex.I + z) := by
  have hnorm (ψ : PontryaginDual C𝔽) (z : ℂ) (g : C𝔽) :
      ‖ideleClassNormTwist (F := F) ψ z g‖ = ((ideleClassNorm F g).val : ℝ) ^ z.re := by
    have hpos : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    change ‖((ψ g : Circle) : ℂ) * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ z)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hc : ∀ g : C₁, ideleClassNormTwist (F := F) (χ' ω) 0 g.val = (ω g : ℂ) := by
    intro g
    have hres : χ' ω (g : C𝔽) = ω g := DFunLike.congr_fun (hχ' ω) g
    change ((χ' ω g.val : Circle) : ℂ) * ((((ideleClassNorm F g.val).val : ℝ) : ℂ) ^ (0 : ℂ)) = _
    rw [Complex.cpow_zero, mul_one, hres]
  obtain ⟨c, hcz, -⟩ := hχ.existsUnique_normTwist ω _ hc
  obtain ⟨g, hg⟩ := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
    (Units.mk0 (2 : ℝ≥0) (by norm_num))
  have hre : c.re = 0 := by
    have h1 := hnorm (χ' ω) 0 g
    have h2 := hnorm (χ ω) c g
    rw [hcz, h2, hg] at h1
    have h3 : (2 : ℝ) ^ c.re = 1 := by simpa using h1
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] at h3
    have h4 : Real.log 2 * c.re = 0 := (Real.exp_eq_one_iff _).mp h3
    exact (mul_eq_zero.mp h4).resolve_left (Real.log_pos (by norm_num)).ne'
  refine ⟨c.im, fun z ↦ ?_⟩
  have hci : ((c.im : ℝ) : ℂ) * Complex.I = c := by
    apply Complex.ext <;> simp [hre]
  have h := ideleClassNormTwist_add_of_eq hcz z
  rwa [zero_add, ← hci] at h

/-- The positive parts of the orders of the completed `L`-functions of two unitary characters
whose norm twists are translates of each other agree at translated points: both are the least
vanishing order of the polar-free theta Mellin transforms along the same quasi-characters. -/
private theorem spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_order
    {ψ ψ' : PontryaginDual C𝔽} {c : ℂ}
    (h : ∀ z : ℂ, ideleClassNormTwist (F := F) ψ' z = ideleClassNormTwist ψ (c + z)) (w : ℂ) :
    (0 < order(ψ', w) ↔ 0 < order(ψ, c + w)) ∧ mult(ψ', w) = mult(ψ, c + w) := by
  have hset : (Set.range fun f : adelePolarSubspace F ↦ meromorphicOrderAt
        (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist ψ' z)) w) =
      Set.range fun f : adelePolarSubspace F ↦ meromorphicOrderAt
        (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist ψ z)) (c + w) := by
    congr 1
    funext f
    have hfun : (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist ψ' z)) =
        (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist ψ z)) ∘
          fun z : ℂ ↦ c + z := funext fun z ↦ by rw [h z]; rfl
    rw [hfun]
    exact meromorphicOrderAt_comp_of_deriv_ne_zero
      ((differentiable_id.const_add c).analyticAt w)
      (show deriv (fun z : ℂ ↦ c + z) w ≠ 0 by simp)
  have h1 := isLeast_globalThetaMellinIntegral_orders (F := F) ψ' w
  have h2 := isLeast_globalThetaMellinIntegral_orders (F := F) ψ (c + w)
  rw [hset] at h1
  have hmax : max 0 (order(ψ', w)) = max 0 (order(ψ, c + w)) := h1.unique h2
  have hne' := spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_ne_top ψ' w
  have hne :=
    spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_ne_top ψ (c + w)
  cases ho' : order(ψ', w) with
  | top => exact absurd ho' hne'
  | coe k' =>
    cases ho : order(ψ, c + w) with
    | top => exact absurd ho hne
    | coe k =>
      rw [ho', ho] at hmax
      have hk : max 0 k' = max 0 k := by exact_mod_cast hmax
      refine ⟨?_, ?_⟩
      · have e1 : (0 : WithTop ℤ) < (k' : WithTop ℤ) ↔ 0 < k' := by exact_mod_cast Iff.rfl
        have e2 : (0 : WithTop ℤ) < (k : WithTop ℤ) ↔ 0 < k := by exact_mod_cast Iff.rfl
        rw [e1, e2]
        omega
      · simp only [WithTop.untop₀_coe]
        omega

/-- Reindexing one cluster block along bijections of the zeros and of the jets. The jets are
indexed by a natural number below the multiplicity, so that no cast between the index sets of
two multiplicities enters. -/
private theorem spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_block
    {J J' Z Z' E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E →L[ℂ] E) (x' : J' → E) (Λ' : J' → StrongDual ℂ E)
    (eZ : Z' ≃ Z) (eJ : J' ≃ J)
    (N : Z → ℕ) (N' : Z' → ℕ) (hN : ∀ z', N' z' = N (eZ z'))
    (jet : (z : Z) → (m : ℕ) → m < N z → J) (jet' : (z' : Z') → (m : ℕ) → m < N' z' → J')
    (hjet : ∀ z' (m : ℕ) (hm : m < N' z') (hm' : m < N (eZ z')),
      eJ (jet' z' m hm) = jet (eZ z') m hm')
    (K' : Finset Z') :
    spectralConvolutionFiniteSum A (x' ∘ eJ.symm) (Λ' ∘ eJ.symm) (K'.map eZ.toEmbedding) N
        (fun z m ↦ jet z m.val m.isLt) =
      spectralConvolutionFiniteSum A x' Λ' K' N' (fun z' m ↦ jet' z' m.val m.isLt) := by
  unfold spectralConvolutionFiniteSum
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun z' _ ↦ ?_
  refine (Fintype.sum_equiv (finCongr (hN z')) _ _ fun m ↦ ?_).symm
  have hj : eJ.symm (jet (eZ z') (finCongr (hN z') m).val (finCongr (hN z') m).isLt) =
      jet' z' m.val m.isLt :=
    (Equiv.symm_apply_eq eJ).mpr (hjet z' m.val m.isLt (finCongr (hN z') m).isLt).symm
  change _ = ((Λ' (eJ.symm (jet (eZ z') (finCongr (hN z') m).val
    (finCongr (hN z') m).isLt))).comp A).smulRight
      (x' (eJ.symm (jet (eZ z') (finCongr (hN z') m).val (finCongr (hN z') m).isLt)))
  rw [hj]

/-- Carrying a family of clusters with prescribed blocks along a bijection of the zeros. Nothing
is used about the blocks except that they agree along the bijection. -/
private theorem spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_abstract
    {M L Z Z' : Type*} (val : M → L) (tn : M → ℝ) (eZ : Z' ≃ Z)
    (B : Finset Z → L) (B' : Finset Z' → L)
    (hblock : ∀ K' : Finset Z', B (K'.map eZ.toEmbedding) = B' K')
    (h : ∃ (P : Set (Finset Z)) (R : P → M),
      P.PairwiseDisjoint id ∧ (∀ z : Z, ∃ K ∈ P, z ∈ K) ∧
      (∀ K : P, val (R K) = B K.val) ∧ Summable (fun K : P ↦ tn (R K))) :
    ∃ (P' : Set (Finset Z')) (R' : P' → M),
      P'.PairwiseDisjoint id ∧ (∀ z' : Z', ∃ K' ∈ P', z' ∈ K') ∧
      (∀ K' : P', val (R' K') = B' K'.val) ∧ Summable (fun K' : P' ↦ tn (R' K')) := by
  classical
  obtain ⟨P, R, hdisj, hcover, hR, hsum⟩ := h
  refine ⟨{K' | K'.map eZ.toEmbedding ∈ P},
    fun K' ↦ R ⟨K'.val.map eZ.toEmbedding, K'.property⟩, ?_, ?_, ?_, ?_⟩
  · intro K₁ h₁ K₂ h₂ hne
    have hne' : K₁.map eZ.toEmbedding ≠ K₂.map eZ.toEmbedding := fun h ↦
      hne (Finset.map_injective _ h)
    exact (Finset.disjoint_map eZ.toEmbedding).mp (hdisj h₁ h₂ hne')
  · intro z'
    obtain ⟨K, hK, hz⟩ := hcover (eZ z')
    refine ⟨K.map eZ.symm.toEmbedding, ?_, ?_⟩
    · have hmap : (K.map eZ.symm.toEmbedding).map eZ.toEmbedding = K := by
        ext y
        simp
      change (K.map eZ.symm.toEmbedding).map eZ.toEmbedding ∈ P
      rw [hmap]
      exact hK
    · exact Finset.mem_map.mpr ⟨eZ z', hz, eZ.symm_apply_apply z'⟩
  · intro K'
    rw [hR ⟨_, K'.property⟩]
    exact hblock K'.val
  · exact hsum.comp_injective
      (i := fun K' : {K' : Finset Z' | K'.map eZ.toEmbedding ∈ P} ↦
        (⟨K'.val.map eZ.toEmbedding, K'.property⟩ : P)) fun K₁ K₂ h ↦
        Subtype.ext (Finset.map_injective _ (congrArg Subtype.val h))

/-- A Markushevich basis stays one after reindexing by a bijection. -/
private theorem spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_basis
    {ι ι' E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x' : ι' → E}
    {Λ' : ι' → StrongDual ℂ E} (h : IsSpectralMarkushevichBasis x' Λ') (e : ι ≃ ι') :
    IsSpectralMarkushevichBasis (x' ∘ e) (Λ' ∘ e) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun i ↦ h1 (e i), fun i j hij ↦ h2 (e i) (e j) fun he ↦ hij (e.injective he), ?_, ?_⟩
  · rw [e.surjective.range_comp]
    exact h3
  · rw [e.surjective.range_comp]
    exact h4

variable (a : ℝ)

local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

/-- Translating the heights of each component by `τ` is a bijection between the zeros of two
choices of the unitary extensions, when it carries zeros to zeros. -/
private theorem spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_relabel_zeros
    (χ χ' : PontryaginDual C₁ → PontryaginDual C𝔽) (α : ℝ) (τ : PontryaginDual C₁ → ℝ)
    (hord : ∀ (ω : PontryaginDual C₁) (b t : ℝ),
      0 < order(χ' ω, shift(b, t)) ↔ 0 < order(χ ω, shift(b, t + τ ω))) :
    ∃ eZ : Z(χ', α) ≃ Z(χ, α), ∀ z' : Z(χ', α),
      (eZ z').val = (z'.val.1, z'.val.2.1, z'.val.2.2 + τ z'.val.1) := by
  let e₃ : PontryaginDual C₁ × ℝ × ℝ ≃ PontryaginDual C₁ × ℝ × ℝ :=
    ⟨fun p ↦ (p.1, p.2.1, p.2.2 + τ p.1), fun p ↦ (p.1, p.2.1, p.2.2 - τ p.1),
      fun p ↦ Prod.ext rfl (Prod.ext rfl (add_sub_cancel_right p.2.2 (τ p.1))),
      fun p ↦ Prod.ext rfl (Prod.ext rfl (sub_add_cancel p.2.2 (τ p.1)))⟩
  have he₃ : ∀ p : PontryaginDual C₁ × ℝ × ℝ, e₃ p = (p.1, p.2.1, p.2.2 + τ p.1) := fun _ ↦ rfl
  have h₃ : ∀ p : PontryaginDual C₁ × ℝ × ℝ,
      (p.2.1 ∈ Icc (-α) α ∧ 0 < order(χ' p.1, shift(a + p.2.1, p.2.2))) ↔
        ((e₃ p).2.1 ∈ Icc (-α) α ∧
          0 < order(χ (e₃ p).1, shift(a + (e₃ p).2.1, (e₃ p).2.2))) := fun p ↦ by
    rw [he₃ p]
    exact and_congr Iff.rfl (hord p.1 (a + p.2.1) p.2.2)
  exact ⟨e₃.subtypeEquiv h₃, fun z' ↦ he₃ z'.val⟩

/-- Translating the heights of each component by `τ` is a bijection between the jets of two
choices of the unitary extensions, when it keeps the multiplicities. -/
private theorem spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_relabel_jets
    (χ χ' : PontryaginDual C₁ → PontryaginDual C𝔽) (α s : ℝ) (τ : PontryaginDual C₁ → ℝ)
    (hmult : ∀ (ω : PontryaginDual C₁) (b t : ℝ),
      mult(χ' ω, shift(b, t)) = mult(χ ω, shift(b, t + τ ω))) :
    ∃ eJ : SpectralStripJetIndex (F := F) (fun ω ↦ χ' ω) a α s ≃
        SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s,
      (∀ j' : SpectralStripJetIndex (F := F) (fun ω ↦ χ' ω) a α s,
        (eJ j').val = (j'.val.1, j'.val.2.1, j'.val.2.2.1 + τ j'.val.1, j'.val.2.2.2)) ∧
      ∀ j : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s,
        (eJ.symm j).val = (j.val.1, j.val.2.1, j.val.2.2.1 - τ j.val.1, j.val.2.2.2) := by
  let e₄ : PontryaginDual C₁ × ℝ × ℝ × ℕ ≃ PontryaginDual C₁ × ℝ × ℝ × ℕ :=
    ⟨fun p ↦ (p.1, p.2.1, p.2.2.1 + τ p.1, p.2.2.2),
      fun p ↦ (p.1, p.2.1, p.2.2.1 - τ p.1, p.2.2.2),
      fun p ↦ Prod.ext rfl (Prod.ext rfl
        (Prod.ext (add_sub_cancel_right p.2.2.1 (τ p.1)) rfl)),
      fun p ↦ Prod.ext rfl (Prod.ext rfl (Prod.ext (sub_add_cancel p.2.2.1 (τ p.1)) rfl))⟩
  have he₄ : ∀ p : PontryaginDual C₁ × ℝ × ℝ × ℕ,
      e₄ p = (p.1, p.2.1, p.2.2.1 + τ p.1, p.2.2.2) := fun _ ↦ rfl
  have he₄s : ∀ p : PontryaginDual C₁ × ℝ × ℝ × ℕ,
      e₄.symm p = (p.1, p.2.1, p.2.2.1 - τ p.1, p.2.2.2) := fun _ ↦ rfl
  have h₄ : ∀ p : PontryaginDual C₁ × ℝ × ℝ × ℕ,
      p.2.2.2 < spectralStripMultiplicity α s p.2.1
          (mult(χ' p.1, shift(a + p.2.1, p.2.2.1))) ↔
        (e₄ p).2.2.2 < spectralStripMultiplicity α s (e₄ p).2.1
          (mult(χ (e₄ p).1, shift(a + (e₄ p).2.1, (e₄ p).2.2.1))) := fun p ↦ by
    rw [he₄ p, hmult p.1 (a + p.2.1) p.2.2.1]
  exact ⟨e₄.subtypeEquiv h₄, fun j' ↦ he₄ j'.val, fun j ↦ he₄s j.val⟩

/-- The relabelling between two choices of the unitary extensions: bijections of the zeros and
of the jets that translate the heights of each component, keep the surviving multiplicities,
and carry the jets of one choice to the jets of the other. -/
private theorem spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_relabel
    (χ χ' : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    (hχ' : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ' ω)) (α s : ℝ) :
    ∃ (eZ : Z(χ', α) ≃ Z(χ, α))
      (eJ : SpectralStripJetIndex (F := F) (fun ω ↦ χ' ω) a α s ≃
        SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s),
      (∀ z' : Z(χ', α), N(χ', α, s, z') = N(χ, α, s, eZ z')) ∧
      (∀ (z' : Z(χ', α)) (m : ℕ) (hm : m < N(χ', α, s, z')) (hm' : m < N(χ, α, s, eZ z')),
        eJ ⟨(z'.val.1, z'.val.2.1, z'.val.2.2, m), hm⟩ =
          ⟨((eZ z').val.1, (eZ z').val.2.1, (eZ z').val.2.2, m), hm'⟩) ∧
      ∀ j : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s,
        spectralZeroJet (F := F) (χ' (eJ.symm j).val.1) (eJ.symm j).val.2.1
          (eJ.symm j).val.2.2.1 (eJ.symm j).val.2.2.2 =
        spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2 := by
  choose τ hτ using fun ω : PontryaginDual C₁ ↦
    spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_twist χ χ' hχ hχ' ω
  have hpt (ω : PontryaginDual C₁) (b t : ℝ) :
      ((τ ω : ℝ) : ℂ) * Complex.I + shift(b, t) = shift(b, t + τ ω) := by
    push_cast
    ring
  have hord (ω : PontryaginDual C₁) (b t : ℝ) :
      (0 < order(χ' ω, shift(b, t)) ↔ 0 < order(χ ω, shift(b, t + τ ω))) ∧
        mult(χ' ω, shift(b, t)) = mult(χ ω, shift(b, t + τ ω)) := by
    have h0 := spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_order
      (hτ ω) (shift(b, t))
    rwa [hpt] at h0
  obtain ⟨eZ, hZ⟩ :=
    spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_relabel_zeros a χ χ'
      α τ fun ω b t ↦ (hord ω b t).1
  obtain ⟨eJ, hJ, hJs⟩ :=
    spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_relabel_jets a χ χ'
      α s τ fun ω b t ↦ (hord ω b t).2
  refine ⟨eZ, eJ, fun z' ↦ ?_, fun z' m hm hm' ↦ ?_, fun j ↦ ?_⟩
  · rw [hZ z']
    exact congrArg (spectralStripMultiplicity α s z'.val.2.1)
      (hord z'.val.1 (a + z'.val.2.1) z'.val.2.2).2
  · apply Subtype.ext
    change (eJ ⟨(z'.val.1, z'.val.2.1, z'.val.2.2, m), hm⟩).val =
      ((eZ z').val.1, (eZ z').val.2.1, (eZ z').val.2.2, m)
    rw [hJ, hZ z']
  · rw [hJs j]
    funext g
    change ideleClassNormTwist (χ' j.val.1) (shift(j.val.2.1, j.val.2.2.1 - τ j.val.1)) g *
        ((logIdeleClassNorm F g : ℂ)) ^ j.val.2.2.2 =
      ideleClassNormTwist (χ j.val.1) (shift(j.val.2.1, j.val.2.2.1)) g *
        ((logIdeleClassNorm F g : ℂ)) ^ j.val.2.2.2
    rw [hτ j.val.1, hpt, sub_add_cancel]

/-- Paper: Notation 10.2.1.1, p. 440, and Theorem 10.3.2.1(1), pp. 453–455. The clustered
statement does not depend on the choice of the unitary extensions of the norm-one characters:
if, for one choice `χ` and every Markushevich basis realizing its strip jets, the zeros can be
grouped into finite clusters whose blocks of the spectral convolution have summable trace
norms, then the same holds for every other choice `χ'`. Two choices differ on each component by
an imaginary power of the norm, so the zeros, their multiplicities and their jets for one
choice are those of the other with the heights of each component translated; clusters and
their blocks are carried along this relabelling. No condition on either choice is needed.
Deviation: Stated for every Sobolev order `s ≥ 0`; §10.3 of the paper assumes `s > 1` (p. 455). -/
theorem spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice
    (χ χ' : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    (hχ' : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ' ω))
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    (h : ∀ (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs))
      (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s →
        StrongDual ℂ Q(a, hStrip(hα), hs)),
      IsSpectralMarkushevichBasis x Λ →
      (∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs (Λ j) =
        (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs j).toLp
          (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) →
      ∃ (P : Set (Finset Z(χ, α))) (R : P → nuclearEndomorphisms Q(a, hStrip(hα), hs)),
        P.PairwiseDisjoint id ∧ (∀ z : Z(χ, α), ∃ K ∈ P, z ∈ K) ∧
        (∀ K : P, (R K).val = spectralConvolutionFiniteSum
          (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ K.val
          (fun z ↦ N(χ, α, s, z))
          (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)) ∧
        Summable (fun K : P ↦ traceNorm (R K)))
    (x' : SpectralStripJetIndex (F := F) (fun ω ↦ χ' ω) a α s → Q(a, hStrip(hα), hs))
    (Λ' : SpectralStripJetIndex (F := F) (fun ω ↦ χ' ω) a α s →
      StrongDual ℂ Q(a, hStrip(hα), hs))
    (hb' : IsSpectralMarkushevichBasis x' Λ')
    (hj' : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs (Λ' j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ' ω) hα hs j).toLp
        (spectralZeroJet (F := F) (χ' j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    ∃ (P : Set (Finset Z(χ', α))) (R : P → nuclearEndomorphisms Q(a, hStrip(hα), hs)),
      P.PairwiseDisjoint id ∧ (∀ z : Z(χ', α), ∃ K ∈ P, z ∈ K) ∧
      (∀ K : P, (R K).val = spectralConvolutionFiniteSum
        (spectralConvolution (F := F) a hStrip(hα) hs φ) x' Λ' K.val
        (fun z ↦ N(χ', α, s, z)) (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)) ∧
      Summable (fun K : P ↦ traceNorm (R K)) :=
  (spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_relabel a χ χ' hχ hχ'
    α s).elim fun eZ hrel ↦ hrel.elim fun eJ hrel ↦
      spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_abstract
        (M := nuclearEndomorphisms Q(a, hStrip(hα), hs)) Subtype.val traceNorm eZ
        (fun K ↦ spectralConvolutionFiniteSum
          (spectralConvolution (F := F) a hStrip(hα) hs φ) (x' ∘ eJ.symm) (Λ' ∘ eJ.symm) K
          (fun z ↦ N(χ, α, s, z)) (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩))
        (fun K' ↦ spectralConvolutionFiniteSum
          (spectralConvolution (F := F) a hStrip(hα) hs φ) x' Λ' K'
          (fun z ↦ N(χ', α, s, z))
          (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩))
        (fun K' ↦ spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_block
          (spectralConvolution (F := F) a hStrip(hα) hs φ) x' Λ' eZ eJ
          (fun z ↦ N(χ, α, s, z)) (fun z ↦ N(χ', α, s, z)) hrel.1
          (fun z m hm ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m), hm⟩)
          (fun z m hm ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m), hm⟩) hrel.2.1 K')
        (h (x' ∘ eJ.symm) (Λ' ∘ eJ.symm)
          (spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice_basis hb'
            eJ.symm)
          fun j ↦ (hj' (eJ.symm j)).trans
            (MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (hrel.2.2 j))))

/-- Paper: Notation 10.2.1.1, p. 440, and Theorem 10.3.2.1(1), pp. 453–455. If the clustered
statement holds for some choice of the unitary extensions of the norm-one characters, it holds
for every choice: for every choice `χ` and every Markushevich basis realizing its strip jets,
the zeros of the strip can be grouped into finite clusters, pairwise disjoint and covering all
the zeros, so that the trace norms of the cluster blocks of the spectral convolution form a
summable series.
Deviation: Stated for every Sobolev order `s ≥ 0`; §10.3 of the paper assumes `s > 1` (p. 455). -/
theorem spectralStripConvolution_summable_clusterTraceNorms_forall_of_exists
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    (h : ∃ χ₀ : PontryaginDual C₁ → PontryaginDual C𝔽,
      IsSpectralBasepointChoice (F := F) (fun ω ↦ χ₀ ω) ∧
      ∀ (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ₀ ω) a α s → Q(a, hStrip(hα), hs))
        (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ₀ ω) a α s →
          StrongDual ℂ Q(a, hStrip(hα), hs)),
        IsSpectralMarkushevichBasis x Λ →
        (∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs (Λ j) =
          (spectralStripJet_memLp (F := F) (fun ω ↦ χ₀ ω) hα hs j).toLp
            (spectralZeroJet (F := F) (χ₀ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) →
        ∃ (P : Set (Finset Z(χ₀, α))) (R : P → nuclearEndomorphisms Q(a, hStrip(hα), hs)),
          P.PairwiseDisjoint id ∧ (∀ z : Z(χ₀, α), ∃ K ∈ P, z ∈ K) ∧
          (∀ K : P, (R K).val = spectralConvolutionFiniteSum
            (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ K.val
            (fun z ↦ N(χ₀, α, s, z))
            (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)) ∧
          Summable (fun K : P ↦ traceNorm (R K)))
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    ∃ (P : Set (Finset Z(χ, α))) (R : P → nuclearEndomorphisms Q(a, hStrip(hα), hs)),
      P.PairwiseDisjoint id ∧ (∀ z : Z(χ, α), ∃ K ∈ P, z ∈ K) ∧
      (∀ K : P, (R K).val = spectralConvolutionFiniteSum
        (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ K.val
        (fun z ↦ N(χ, α, s, z)) (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)) ∧
      Summable (fun K : P ↦ traceNorm (R K)) :=
  h.elim fun χ₀ h₀ ↦
    spectralStripConvolution_summable_clusterTraceNorms_of_basepointChoice a χ₀ χ h₀.1 hχ hα hs φ
      h₀.2 x Λ hb hj

end RiemannMasullo
