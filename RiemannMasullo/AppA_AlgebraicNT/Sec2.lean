module

public import RiemannMasullo.AppA_AlgebraicNT.Sec1
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Algebra.Group.Units
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Orbital structures on adeles and ideles

Appendix A.2.1–A.2.2 of Masullo. We use the Minkowski embedding to specify the
archimedean parallelepiped for a chosen integral basis. Idelic norms take values in
the positive reals `ℝ≥0ˣ`, as in §A.1.
-/

@[expose] public section

noncomputable section

namespace RiemannMasullo

open Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical NNRat NNReal NumberField.AdeleRing Pointwise

variable (F : Type*) [Field F] [NumberField F]

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F

section Additive

variable {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))

-- TODO(paper-gap): (A.2.1.1) uses only r₁ + r₂ indices and bounds absolute values.
-- The proof on p. 554 specifies [0,1)^[F:ℚ] in the real basis induced by the integral basis.

/-- Paper: Definition A.2.1.1, p. 545. The infinite fundamental domain is the half-open
parallelepiped of the chosen integral basis in Minkowski space, pulled back to the completions.
Deviation: We use the signed real coordinates and all the basis vectors specified on p. 554. -/
def infiniteAdeleFundamentalDomain : Set (InfiniteAdeleRing F) :=
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  (InfiniteAdeleRing.ringEquiv_mixedSpace F) ⁻¹'
    ZSpan.fundamentalDomain ((b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F))

/-- Paper: Definition A.2.1.1, p. 545. Along any basis vector, precisely the real
multiples with coefficient in the half-open unit interval belong to the infinite domain.
Deviation: This checks the coordinate convention given on p. 554. -/
theorem infiniteAdeleFundamentalDomain_basis_line (i : ι) (t : ℝ) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • mixedEmbedding F (b i : F)) ∈
      infiniteAdeleFundamentalDomain F b ↔ t ∈ Set.Ico 0 1 := by
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  have hB : B i = mixedEmbedding F (b i : F) := by
    simp only [B, Module.Basis.ofZLatticeBasis_apply, Module.Basis.map_apply]
    rfl
  simp only [infiniteAdeleFundamentalDomain, Set.mem_preimage, RingEquiv.apply_symm_apply]
  change t • mixedEmbedding F (b i : F) ∈ ZSpan.fundamentalDomain B ↔ _
  rw [← hB, ZSpan.mem_fundamentalDomain, map_smul, Module.Basis.repr_self,
    Finsupp.smul_single', mul_one]
  refine ⟨fun h ↦ ?_, fun ht k ↦ ?_⟩
  · simpa only [Finsupp.single_eq_same] using h i
  · by_cases h : k = i
    · simpa only [h, Finsupp.single_eq_same] using ht
    · rw [Finsupp.single_eq_of_ne h]
      exact ⟨le_rfl, zero_lt_one⟩

/-- Paper: Definition A.2.1.1, p. 545. The adelic fundamental domain consists of the
adeles in the infinite parallelepiped whose finite components are all integral.
Deviation: Its infinite factor uses the coordinate convention on p. 554. -/
def adeleFundamentalDomain : Set 𝔸[F] :=
  {a | a.1 ∈ infiniteAdeleFundamentalDomain F b ∧ a ∈ integralAdelesOutside F ∅}

/-- Paper: Definition A.2.1.1, p. 545. The adelic domain contains exactly one
diagonal element of the number field, namely zero. -/
theorem diagonal_mem_adeleFundamentalDomain (x : F) :
    algebraMap F 𝔸[F] x ∈ adeleFundamentalDomain F b ↔ x = 0 := by
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  simp only [adeleFundamentalDomain, Set.mem_ofPred_eq, AdeleRing.algebraMap_fst_def,
    infiniteAdeleFundamentalDomain, Set.mem_preimage,
    ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  change mixedEmbedding F x ∈ ZSpan.fundamentalDomain B ∧ _ ↔ _
  constructor
  · rintro ⟨hinf, hfin⟩
    have hx := (diagonal_mem_integralAdelesOutside F ∅ x).mp hfin
    simp only [Finset.coe_empty, integer_empty, Algebra.mem_bot] at hx
    obtain ⟨r, rfl⟩ := hx
    apply mixedEmbedding_injective F
    rw [map_zero]
    apply B.ext_elem
    intro i
    have hi := (ZSpan.mem_fundamentalDomain B).mp hinf i
    change B.repr (e r : mixedEmbedding.mixedSpace F) i ∈ Set.Ico 0 1 at hi
    rw [Module.Basis.ofZLatticeBasis_repr_apply, Set.mem_Ico] at hi
    let n := (b.map e).repr (e r) i
    have hnonneg : 0 ≤ n := by exact_mod_cast hi.1
    have hlt : n < 1 := by exact_mod_cast hi.2
    have hn : n = 0 := by omega
    change B.repr (e r : mixedEmbedding.mixedSpace F) i = B.repr 0 i
    rw [Module.Basis.ofZLatticeBasis_repr_apply, map_zero, Finsupp.zero_apply]
    exact_mod_cast hn
  · rintro rfl
    rw [map_zero, map_zero, ZSpan.mem_fundamentalDomain]
    refine ⟨fun i ↦ ?_, (integralAdelesOutside F ∅).zero_mem⟩
    rw [map_zero, Finsupp.zero_apply]
    exact ⟨le_rfl, zero_lt_one⟩

/-- Paper: §A.2.1, p. 545. The adelic fundamental domain has compact closure. -/
theorem adeleFundamentalDomain_precompact : IsCompact (closure (adeleFundamentalDomain F b)) := by
  classical
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  let : Fintype ι := FiniteDimensional.fintypeBasisIndex B
  let h : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
    (Homeomorph.piEquivPiSubtypeProd InfinitePlace.IsReal
      (fun w : InfinitePlace F ↦ w.Completion)).trans
      ((Homeomorph.piCongrRight fun w ↦ (isometryEquivRealOfIsReal w.2).toHomeomorph).prodCongr
        ((Homeomorph.piCongrRight fun w ↦
          (isometryEquivComplexOfIsComplex
            (InfinitePlace.not_isReal_iff_isComplex.mp w.2)).toHomeomorph).trans
          (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
            (Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex))))
  have (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let integral (x : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) : 𝔸ᶠ[F] :=
    ⟨fun v ↦ x v, Filter.Eventually.of_forall fun v ↦ (x v).property⟩
  have hIntegral : Continuous integral :=
    continuous_restrictedProduct_of_uniform
      (fun v ↦ continuous_subtype_val.comp (continuous_apply v))
      (Filter.Eventually.of_forall fun v x ↦ (x v).property)
  apply ((B.parallelepiped.isCompact.image h.symm.continuous).prod
    (isCompact_range hIntegral)).closure_of_subset
  rintro a ⟨haInf, haf⟩
  refine ⟨⟨h a.1, ZSpan.fundamentalDomain_subset_parallelepiped B haInf, h.symm_apply_apply _⟩, ?_⟩
  simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
    true_implies] at haf
  exact ⟨fun v ↦ ⟨a.2 v, haf v⟩, rfl⟩

/-- Paper: §A.2.1, p. 545. The adelic fundamental domain has nonempty interior. -/
theorem adeleFundamentalDomain_interior : (interior (adeleFundamentalDomain F b)).Nonempty := by
  classical
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  let : Fintype ι := FiniteDimensional.fintypeBasisIndex B
  let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have hm : Continuous m := by
    change Continuous (fun x : InfiniteAdeleRing F ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F x)
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (continuous_pi fun v ↦ (isometryEquivRealOfIsReal v.2).continuous.comp
      (continuous_apply v.1)).prodMk
      (continuous_pi fun v ↦ (isometryEquivComplexOfIsComplex v.2).continuous.comp
        (continuous_apply v.1))
  have hIntegral : IsOpen (integralAdelesOutside F ∅ : Set 𝔸[F]) := by
    simp only [integralAdelesOutside, Subring.coe_iInf, Set.iInter_ofPred, Finset.notMem_empty,
      not_false_eq_true, true_implies]
    exact (RestrictedProduct.isOpen_forall_mem (fun v : HeightOneSpectrum (𝓞 F) ↦
      Valued.isOpen_integer (v.adicCompletion F))).preimage continuous_snd
  let coords : 𝔸[F] → ι → ℝ := fun a ↦ B.equivFun (m a.1)
  let cube := Set.pi Set.univ (fun _ : ι ↦ Set.Ioo (0 : ℝ) 1)
  let U := (coords ⁻¹' cube) ∩ (integralAdelesOutside F ∅ : Set 𝔸[F])
  have hU : IsOpen U :=
    ((isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo).preimage
      ((continuous_equivFun_basis B).comp (hm.comp continuous_fst))).inter hIntegral
  let a : 𝔸[F] := (m.symm (B.equivFun.symm fun _ ↦ 1 / 2), 0)
  refine ⟨a, mem_interior.mpr ⟨U, ?_, hU, ?_⟩⟩
  · rintro x ⟨hx, hInt⟩
    refine ⟨(ZSpan.mem_fundamentalDomain B).mpr fun i ↦ ?_, hInt⟩
    exact Set.Ioo_subset_Ico_self (hx i (Set.mem_univ i))
  · refine ⟨?_, ?_⟩
    · change B.equivFun (m (m.symm (B.equivFun.symm fun _ ↦ 1 / 2))) ∈ cube
      rw [RingEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      exact fun _ _ ↦ ⟨by norm_num, by norm_num⟩
    · change a ∈ integralAdelesOutside F ∅
      simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
        true_implies]
      exact fun v ↦ (v.adicCompletionIntegers F).zero_mem

/-- Paper: §A.2.1, p. 545. Every nonzero diagonal translation moves the fundamental
domain off itself, including its half-open boundary. -/
theorem adeleFundamentalDomain_disjoint (x : F) (hx : x ≠ 0) :
    Disjoint (algebraMap F 𝔸[F] x +ᵥ adeleFundamentalDomain F b) (adeleFundamentalDomain F b) := by
  rw [Set.disjoint_left]
  intro y hy hyDomain
  obtain ⟨a, ha, rfl⟩ := Set.mem_vadd_set.mp hy
  have hxFin : algebraMap F 𝔸[F] x ∈ integralAdelesOutside F ∅ := by
    have h := (integralAdelesOutside F ∅).sub_mem hyDomain.2 ha.2
    change (algebraMap F 𝔸[F] x + a) - a ∈ integralAdelesOutside F ∅ at h
    rwa [add_sub_cancel_right] at h
  have hxInt := (diagonal_mem_integralAdelesOutside F ∅ x).mp hxFin
  simp only [Finset.coe_empty, integer_empty, Algebra.mem_bot] at hxInt
  obtain ⟨r, rfl⟩ := hxInt
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  let : Fintype ι := FiniteDimensional.fintypeBasisIndex B
  let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let z := mixedEmbedding F (algebraMap (𝓞 F) F r)
  have hz : z ∈ Submodule.span ℤ (Set.range B) := by
    rw [(b.map e).ofZLatticeBasis_span ℝ]
    exact ⟨r, rfl⟩
  have haInf : m a.1 ∈ ZSpan.fundamentalDomain B := ha.1
  have hyInf : z + m a.1 ∈ ZSpan.fundamentalDomain B := by
    have h := hyDomain.1
    change m ((algebraMap F 𝔸[F] (algebraMap (𝓞 F) F r)).1 + a.1) ∈
      ZSpan.fundamentalDomain B at h
    rwa [map_add, AdeleRing.algebraMap_fst_def,
      ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp] at h
  have h := ZSpan.fract_eq_self.mpr hyInf
  rw [ZSpan.fract_zSpan_add B _ hz, ZSpan.fract_eq_self.mpr haInf] at h
  apply hx (mixedEmbedding_injective F ?_)
  rw [map_zero]
  exact add_eq_right.mp h.symm

/-- Paper: Lemma A.2.1.2, p. 545. The additive translates by field elements
of the adelic fundamental domain cover the adele ring. -/
theorem adeleFundamentalDomain_cover :
    (⋃ x : F, algebraMap F 𝔸[F] x +ᵥ adeleFundamentalDomain F b) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro a
  -- Choose a representative of the adelic class that is integral at all finite places.
  let P := AdeleRing.principalSubgroup (𝓞 F) F
  let q := QuotientAddGroup.mk' P
  obtain ⟨-, -, -, -, -, -, -, -, ⟨e, he⟩, -⟩ := adele_additive_quotient.{_, 0} F
  obtain ⟨a₀, ha₀⟩ := QuotientAddGroup.mk'_surjective _ (e.symm (q a))
  have hq : q a = q a₀.val := by
    rw [← he, ha₀, e.apply_symm_apply]
  obtain ⟨x, hx⟩ : a - a₀.val ∈ P := QuotientAddGroup.eq_iff_sub_mem.mp hq
  -- Translate by an integer to put the archimedean component in the parallelepiped.
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let i := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map i).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  let : Fintype ι := FiniteDimensional.fintypeBasisIndex B
  let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
  obtain ⟨z, hz, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B (m a₀.val.1)
  have hspan : Submodule.span ℤ (Set.range B) = mixedEmbedding.integerLattice F :=
    (b.map i).ofZLatticeBasis_span ℝ
  have hz' : z.val ∈ mixedEmbedding.integerLattice F := hspan ▸ z.property
  obtain ⟨r, hr⟩ : ∃ r : 𝓞 F, mixedEmbedding F (r : F) = z.val := hz'
  let d := algebraMap F 𝔸[F] (r : F)
  refine Set.mem_iUnion.mpr ⟨x - (r : F), Set.mem_vadd_set.mpr
    ⟨a₀.val + d, ⟨?_, ?_⟩, ?_⟩⟩
  · change m (a₀.val.1 + d.1) ∈ ZSpan.fundamentalDomain B
    rw [map_add, show d.1 = algebraMap F (InfiniteAdeleRing F) (r : F) from rfl,
      ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, hr, add_comm]
    exact hz
  · have hd : d ∈ integralAdelesOutside F ∅ := by
      apply (diagonal_mem_integralAdelesOutside F ∅ _).mpr
      simp only [Finset.coe_empty, integer_empty, Algebra.mem_bot]
      exact ⟨r, rfl⟩
    exact (integralAdelesOutside F ∅).add_mem a₀.property hd
  · change algebraMap F 𝔸[F] (x - (r : F)) + (a₀.val + d) = a
    change algebraMap F 𝔸[F] x = a - a₀.val at hx
    rw [map_sub, hx, show algebraMap F 𝔸[F] (r : F) = d from rfl]
    abel

/-- Paper: Lemma A.2.1.2, p. 545. Only finitely many field translates of the
closure of the fundamental domain meet a given compact subset of the adeles. -/
theorem adeleFundamentalDomain_finite_translates (K : Set 𝔸[F]) (hK : IsCompact K) :
    {x : F | ((algebraMap F 𝔸[F] x +ᵥ closure (adeleFundamentalDomain F b)) ∩ K).Nonempty}.Finite := by
  sorry

/-- Paper: Example A.2.1.3, p. 545. For the rational field the domain is the interval
from zero inclusive to one exclusive times the product of the finite local integer rings. -/
def ratAdeleFundamentalDomain : Set 𝔸[ℚ] :=
  {a | extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (a.1 Rat.infinitePlace) ∈ Set.Ico 0 1 ∧
    a ∈ integralAdelesOutside ℚ ∅}

/-- Paper: Example A.2.1.3, p. 545. Every rational adele belongs to exactly one
rational translate of the displayed domain. -/
theorem ratAdeleFundamentalDomain_unique_translate (a : 𝔸[ℚ]) :
    ∃! q : ℚ, a ∈ algebraMap ℚ 𝔸[ℚ] q +ᵥ ratAdeleFundamentalDomain := by
  sorry

/-- Paper: Example A.2.1.3, p. 546. Each member of the rationally indexed cover
has compact closure. -/
theorem ratAdeleFundamentalDomain_precompact_translate (q : ℚ) :
    IsCompact (closure (algebraMap ℚ 𝔸[ℚ] q +ᵥ ratAdeleFundamentalDomain)) := by
  sorry

end Additive

section NormSections

/-- Paper: Equations (A.2.2.1)–(A.2.2.2), p. 546. Rational ideles split into a real
unit, a discrete positive rational and a tuple of local integer units. The rational
factor acts diagonally, and the idelic norm is the absolute value of the real factor. -/
theorem ratIdeleGroup_decomposition :
    letI : TopologicalSpace ℚ≥0ˣ := ⊥
    let U := (v : HeightOneSpectrum (𝓞 ℚ)) → (v.adicCompletionIntegers ℚ)ˣ
    ∃ e : (ℝˣ × ℚ≥0ˣ × U) ≃ₜ* 𝕀[ℚ], ∀ t q h,
      let g := e (t, q, h)
      let a : ℚ := q.val
      extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (g.val.1 Rat.infinitePlace) =
        t.val * (a : ℝ) ∧
      (∀ v, g.val.2 v = algebraMap ℚ (v.adicCompletion ℚ) a * (h v).val.val) ∧
      ((ideleNorm ℚ g).val : ℝ) = |t.val| := by
  sorry

/-- Paper: Equation (A.2.2.3), p. 546. Rational idele classes identify with the product
of the positive reals and the finite integral units, by sending the tuple to its class. -/
theorem ratIdeleClassGroup_decomposition :
    let U := (v : HeightOneSpectrum (𝓞 ℚ)) → (v.adicCompletionIntegers ℚ)ˣ
    ∃ e : (ℝ≥0ˣ × U) ≃ₜ* IdeleClassGroup (𝓞 ℚ) ℚ, ∀ t h, ∃ g : 𝕀[ℚ],
      extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (g.val.1 Rat.infinitePlace) = t.val ∧
      (∀ v, g.val.2 v = (h v).val.val) ∧ e (t, h) = QuotientGroup.mk g := by
  sorry

-- TODO(paper-gap): A.2.2.1 writes an idele-valued section and a class-group norm in
-- the same identity. The introductory paragraph on p. 546 specifies the quotient map.

/-- Paper: Lemma A.2.2.1, p. 546. The rational section inserts a positive real at
the unique real place of the rationals and one at every finite place. -/
def ratIdeleNormSection : ℝ≥0ˣ →* 𝕀[ℚ] :=
  let atInfinity := (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm.toRingHom
  (IdeleGroup.ofCompletion (𝓞 ℚ) ℚ Rat.infinitePlace).comp
    (Units.map (atInfinity.comp NNReal.toRealHom).toMonoidHom)

/-- Paper: Lemma A.2.2.1, p. 546. Insertion at the real place is continuous. -/
theorem ratIdeleNormSection_continuous : Continuous ratIdeleNormSection := by
  unfold ratIdeleNormSection IdeleGroup.ofCompletion
  simp only [MonoidHom.coe_comp]
  apply Continuous.comp <;> apply Continuous.units_map
  · exact (continuous_mulSingle (A := InfinitePlace.Completion) Rat.infinitePlace).prodMk
      continuous_const
  · exact (isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm.continuous.comp
      NNReal.continuous_coe

/-- Paper: Lemma A.2.2.1, p. 546. The rational section is a right inverse to the
idelic norm before passage to classes. -/
theorem ratIdeleNormSection_rightInverse : RightInverse ratIdeleNormSection (ideleNorm ℚ) := by
  intro t
  apply Units.ext
  change Real.toNNReal ‖(ratIdeleNormSection t).val‖ = t.val
  rw [AdeleRing.norm_apply_of_isUnit (ratIdeleNormSection t).isUnit,
    Fintype.prod_subsingleton _ Rat.infinitePlace]
  have hfin (v : HeightOneSpectrum (𝓞 ℚ)) : (ratIdeleNormSection t).val.2 v = 1 := rfl
  simp only [hfin, norm_one, finprod_one, mul_one]
  have hnorm : ‖(ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm (t.val : ℝ)‖ =
      ‖(t.val : ℝ)‖ :=
    (isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm.isometry.norm_map_of_map_zero
      (map_zero (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm) _
  simp [ratIdeleNormSection, InfinitePlace.mult, Rat.isReal_infinitePlace, hnorm]

/-- Paper: Lemma A.2.2.1, p. 546. The class of the rational section has the
prescribed class norm.
Deviation: The paper's class-valued statement requires composition with the quotient map. -/
theorem ratIdeleNormSection_class_rightInverse :
    RightInverse ((QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ)).comp
      ratIdeleNormSection) (ideleClassNorm ℚ) := by
  exact ratIdeleNormSection_rightInverse

/-- Paper: Lemma A.2.2.2, p. 546. Scalar extension from the rational adeles is the
unique adelic extension of the rational embedding supplied by Lemma A.1.2.1. -/
def rationalAdeleEmbedding : 𝔸[ℚ] →+* 𝔸[F] :=
  let ⟨_, _, _, _, _, _, _, _, _, extensions⟩ := adele_additive_quotient ℚ
  (extensions F (algebraMap ℚ F)).1.exists.choose

/-- Paper: Lemma A.2.2.2, p. 546. The scalar embedding on adeles extends the
diagonal rational embedding and respects the places below each component. -/
theorem rationalAdeleEmbedding_spec : IsAdeleExtension ℚ (algebraMap ℚ F) (rationalAdeleEmbedding F) := by
  sorry

/-- Paper: Lemma A.2.2.2, p. 546. The relative idelic norm to the rationals is
the determinant of multiplication on the adele algebra, restricted to units. -/
def relativeIdeleNormRat : 𝕀[F] →* 𝕀[ℚ] :=
  letI := (rationalAdeleEmbedding F).toAlgebra
  Units.map (Algebra.norm 𝔸[ℚ])

/-- Paper: Lemma A.2.2.2, p. 546. The adele algebra on which the relative norm
takes a determinant is finite free of the field degree.
Deviation: This sanity check rules out the default determinant on modules without a finite basis. -/
theorem rationalAdeleEmbedding_hasBasis :
    letI := (rationalAdeleEmbedding F).toAlgebra
    Nonempty (Module.Basis (Fin (Module.finrank ℚ F)) 𝔸[ℚ] 𝔸[F]) := by
  sorry

/-- Paper: Lemma A.2.2.2, p. 546. The relative norm to the rational ideles is continuous. -/
theorem relativeIdeleNormRat_continuous : Continuous (relativeIdeleNormRat F) := by
  sorry

/-- Paper: Lemma A.2.2.2, p. 546. Taking the rational idelic norm after the relative
norm gives the idelic norm of the original idele. -/
theorem ideleNorm_comp_relativeIdeleNormRat :
    (ideleNorm ℚ).comp (relativeIdeleNormRat F) = ideleNorm F := by
  sorry

/-- Paper: Lemma A.2.2.2, p. 546. Scalar extension embeds the rational ideles as a
closed subgroup of the ideles of the field. -/
theorem rationalIdeleEmbedding_isClosedEmbedding :
    IsClosedEmbedding (Units.map (rationalAdeleEmbedding F).toMonoidHom) := by
  sorry

/-- Paper: Lemma A.2.2.2, p. 546. The relative norm of an extended rational
idele is the original idele raised to the field degree. -/
theorem relativeIdeleNormRat_on_rational (g : 𝕀[ℚ]) :
    relativeIdeleNormRat F (Units.map (rationalAdeleEmbedding F).toMonoidHom g) =
      g ^ Module.finrank ℚ F := by
  sorry

/-- Paper: Definition A.2.2.3, p. 547. The canonical section takes the positive
root of order the field degree, applies the rational section and extends scalars. -/
def canonicalIdeleNormSection : ℝ≥0ˣ →* 𝕀[F] :=
  (Units.map (rationalAdeleEmbedding F).toMonoidHom).comp
    (ratIdeleNormSection.comp (Units.map (NNReal.rpowMonoidHom (Module.finrank ℚ F : ℝ)⁻¹)))

/-- Paper: Lemma A.2.2.4, p. 547. The canonical homomorphism is continuous. -/
theorem canonicalIdeleNormSection_continuous : Continuous (canonicalIdeleNormSection F) := by
  sorry

/-- Paper: Lemma A.2.2.4, p. 547. The canonical homomorphism splits the idelic norm. -/
theorem canonicalIdeleNormSection_rightInverse :
    RightInverse (canonicalIdeleNormSection F) (ideleNorm F) := by
  sorry

/-- Paper: Lemma A.2.2.4, p. 547. Every infinite component of the canonical section
is the positive real root of order the field degree, viewed in the local field. -/
theorem canonicalIdeleNormSection_infinite (t : ℝ≥0ˣ) (v : InfinitePlace F) :
    extensionEmbedding v ((canonicalIdeleNormSection F t).val.1 v) =
      (((t.val : ℝ) ^ (Module.finrank ℚ F : ℝ)⁻¹ : ℝ) : ℂ) := by
  sorry

/-- Paper: Lemma A.2.2.4, p. 547. The finite part of the canonical section is one. -/
theorem canonicalIdeleNormSection_finite (t : ℝ≥0ˣ) :
    (canonicalIdeleNormSection F t).val.2 = 1 := by
  apply FiniteAdeleRing.ext
  intro w
  let v := w.under (𝓞 ℚ)
  let a : 𝔸[ℚ] := (ratIdeleNormSection
    (Units.map (NNReal.rpowMonoidHom (Module.finrank ℚ F : ℝ)⁻¹) t)).val
  let f := (RestrictedProduct.evalRingHom (fun u : HeightOneSpectrum (𝓞 F) ↦
    u.adicCompletion F) w).comp ((RingHom.snd _ _).comp (rationalAdeleEmbedding F))
  have ha : (a - 1).2 v = 0 := by
    change (1 : v.adicCompletion ℚ) - 1 = 0
    exact sub_self 1
  have h := (rationalAdeleEmbedding_spec F).2.2.2 v w rfl (a - 1) ha
  change f (a - 1) = 0 at h
  change f a = 1
  simpa only [map_sub, map_one, sub_eq_zero] using h

/-- Paper: Definition A.2.2.5, p. 547. This local homomorphism sends a positive real
to its specified real power inside the completion at an infinite place. -/
def infinitePlaceRealPower (v : InfinitePlace F) (r : ℝ) : ℝ≥0ˣ →* v.Completionˣ :=
  let realScalars := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toRingHom.comp
    (algebraMap ℝ (mixedEmbedding.mixedSpace F))
  let atPlace := (Pi.evalRingHom (fun w : InfinitePlace F ↦ w.Completion) v).comp realScalars
  Units.map ((atPlace.comp NNReal.toRealHom).toMonoidHom.comp (NNReal.rpowMonoidHom r))

/-- Paper: Definition A.2.2.5, p. 547. Under the archimedean embedding the value
is the positive real power itself, including at a complex place. -/
theorem infinitePlaceRealPower_apply (v : InfinitePlace F) (r : ℝ) (t : ℝ≥0ˣ) :
    extensionEmbedding v (infinitePlaceRealPower F v r t).val = (((t.val : ℝ) ^ r : ℝ) : ℂ) := by
  let x : ℝ := (t.val : ℝ) ^ r
  let y := algebraMap ℝ (mixedEmbedding.mixedSpace F) x
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  change extensionEmbedding v (e.symm y v) = (x : ℂ)
  have h := e.apply_symm_apply y
  by_cases hv : v.IsReal
  · simpa only [e, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, y, Prod.algebraMap_apply,
      Pi.algebraMap_apply, Algebra.algebraMap_self_apply, extensionEmbeddingOfIsReal_apply] using
      congrArg (fun z : mixedEmbedding.mixedSpace F => (z.1 ⟨v, hv⟩ : ℂ)) h
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hv
    simpa only [e, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, y, Prod.algebraMap_apply,
      Pi.algebraMap_apply] using!
      congrArg (fun z : mixedEmbedding.mixedSpace F => z.2 ⟨v, hc⟩) h

/-- Paper: Definition A.2.2.5, p. 547. The single-place section inserts the positive
root of order the local degree at the chosen infinite place and one elsewhere. -/
def singlePlaceIdeleNormSection (v : InfinitePlace F) : ℝ≥0ˣ →* 𝕀[F] :=
  (IdeleGroup.ofCompletion (𝓞 F) F v).comp (infinitePlaceRealPower F v (v.mult : ℝ)⁻¹)

/-- Paper: Lemma A.2.2.6, p. 547. The section at one infinite place is continuous. -/
theorem singlePlaceIdeleNormSection_continuous (v : InfinitePlace F) :
    Continuous (singlePlaceIdeleNormSection F v) := by
  unfold singlePlaceIdeleNormSection IdeleGroup.ofCompletion
  simp only [MonoidHom.coe_comp]
  apply Continuous.comp
  · apply Continuous.units_map
    exact (continuous_mulSingle (A := InfinitePlace.Completion) v).prodMk continuous_const
  · apply Continuous.of_coeHom_comp
    apply (isometry_extensionEmbedding v).isEmbedding.continuous_iff.mpr
    change Continuous (fun t : ℝ≥0ˣ ↦
      extensionEmbedding v (infinitePlaceRealPower F v (v.mult : ℝ)⁻¹ t).val)
    simp only [infinitePlaceRealPower_apply]
    exact Complex.continuous_ofReal.comp
      ((Real.continuous_rpow_const (by positivity : 0 ≤ (v.mult : ℝ)⁻¹)).comp
        (NNReal.continuous_coe.comp Units.continuous_val))

/-- Paper: Lemma A.2.2.6, p. 547. The section at one infinite place splits the idelic norm. -/
theorem singlePlaceIdeleNormSection_rightInverse (v : InfinitePlace F) :
    RightInverse (singlePlaceIdeleNormSection F v) (ideleNorm F) := by
  intro t
  apply Units.ext
  apply NNReal.eq
  rw [((ideleNorm_spec F).1 (singlePlaceIdeleNormSection F v t)).2]
  let x := (infinitePlaceRealPower F v (v.mult : ℝ)⁻¹ t).val
  change (∏ w : InfinitePlace F, ‖Pi.mulSingle v x w‖ ^ w.mult) *
    (∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖(1 : w.adicCompletion F)‖) = (t.val : ℝ)
  simp only [norm_one, finprod_one, mul_one]
  rw [Finset.prod_eq_single_of_mem v (Finset.mem_univ _), Pi.mulSingle_eq_same]
  · have ht : 0 ≤ (t.val : ℝ) := t.val.coe_nonneg
    have hx : ‖x‖ = (t.val : ℝ) ^ (v.mult : ℝ)⁻¹ := by
      rw [← (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) x]
      change ‖extensionEmbedding v (infinitePlaceRealPower F v (v.mult : ℝ)⁻¹ t).val‖ = _
      rw [infinitePlaceRealPower_apply, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg ht _)]
    rw [hx, ← Real.rpow_mul_natCast ht, inv_mul_cancel₀ v.mult_coe_ne_zero, Real.rpow_one]
  · intro w _ hw
    simp only [Pi.mulSingle_eq_of_ne hw, norm_one, one_pow]

/-- Paper: Definition A.2.2.7, p. 547. The diagonal section inserts a positive real
power at every infinite place, dividing the exponent by both the local degree and the
number of infinite places. Its finite components are one. -/
def diagonalIdeleNormSection : ℝ≥0ˣ →* 𝕀[F] :=
  ∏ v : InfinitePlace F, (IdeleGroup.ofCompletion (𝓞 F) F v).comp
    (infinitePlaceRealPower F v ((v.mult : ℝ) * Fintype.card (InfinitePlace F))⁻¹)

/-- Paper: Lemma A.2.2.8, p. 547. The diagonal homomorphism is continuous. -/
theorem diagonalIdeleNormSection_continuous : Continuous (diagonalIdeleNormSection F) := by
  simp only [diagonalIdeleNormSection, MonoidHom.coe_finsetProd, Finset.prod_fn,
    MonoidHom.coe_comp]
  refine continuous_finsetProd _ fun v _ ↦ ?_
  apply Continuous.comp
  · unfold IdeleGroup.ofCompletion
    apply Continuous.units_map
    exact (continuous_mulSingle (A := InfinitePlace.Completion) v).prodMk continuous_const
  · apply Continuous.of_coeHom_comp
    apply (isometry_extensionEmbedding v).isEmbedding.continuous_iff.mpr
    change Continuous (fun t : ℝ≥0ˣ ↦ extensionEmbedding v (infinitePlaceRealPower F v _ t).val)
    simp only [infinitePlaceRealPower_apply]
    exact Complex.continuous_ofReal.comp
      ((Real.continuous_rpow_const (by positivity)).comp
        (NNReal.continuous_coe.comp Units.continuous_val))

/-- Paper: Lemma A.2.2.8, p. 547. The diagonal homomorphism splits the idelic norm. -/
theorem diagonalIdeleNormSection_rightInverse :
    RightInverse (diagonalIdeleNormSection F) (ideleNorm F) := by
  intro t
  let n := Fintype.card (InfinitePlace F)
  let root := Units.map (NNReal.rpowMonoidHom (n : ℝ)⁻¹) t
  have hpower (v : InfinitePlace F) :
      infinitePlaceRealPower F v ((v.mult : ℝ) * n)⁻¹ t =
        infinitePlaceRealPower F v (v.mult : ℝ)⁻¹ root := by
    apply Units.ext
    apply (isometry_extensionEmbedding v).injective
    rw [infinitePlaceRealPower_apply, infinitePlaceRealPower_apply]
    apply congrArg Complex.ofReal
    change ((t.val : ℝ) ^ ((v.mult : ℝ) * n)⁻¹ : ℝ) =
      (((t.val ^ (n : ℝ)⁻¹ : ℝ≥0) : ℝ) ^ (v.mult : ℝ)⁻¹ : ℝ)
    rw [NNReal.coe_rpow, ← Real.rpow_mul t.val.coe_nonneg, mul_inv_rev]
  have hsection : diagonalIdeleNormSection F t =
      ∏ v : InfinitePlace F, singlePlaceIdeleNormSection F v root := by
    simp only [diagonalIdeleNormSection, MonoidHom.finsetProd_apply, MonoidHom.comp_apply,
      singlePlaceIdeleNormSection]
    exact Finset.prod_congr rfl fun v _ ↦ congrArg _ (hpower v)
  have hnorm (v : InfinitePlace F) : ideleNorm F (singlePlaceIdeleNormSection F v root) = root :=
    singlePlaceIdeleNormSection_rightInverse F v root
  rw [hsection, map_prod]
  simp only [hnorm, Finset.prod_const, Finset.card_univ]
  apply Units.ext
  exact NNReal.rpow_inv_natCast_pow t.val Fintype.card_ne_zero

-- TODO(paper-gap): The hypothesis of A.2.2.9 says only "continuous section". A
-- continuous right inverse need not even preserve one. The start of §A.2.2 specifies homomorphisms.

/-- Paper: Lemma A.2.2.9, p. 547. Multiplying a section value by a norm-one idele
identifies the product of the positive reals and the kernel with the full topological group.
Deviation: We use a homomorphic section, as in the introduction to §A.2.2. -/
theorem ideleNormSection_product (s : ℝ≥0ˣ →* 𝕀[F]) (hs : Continuous s)
    (hn : RightInverse s (ideleNorm F)) :
    ∃ e : (ℝ≥0ˣ × (ideleNorm F).ker) ≃ₜ* 𝕀[F], ∀ t g, e (t, g) = s t * g.val := by
  sorry

end NormSections

end RiemannMasullo
