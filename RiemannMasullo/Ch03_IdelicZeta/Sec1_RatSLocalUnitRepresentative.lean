module

public import RiemannMasullo.Ch03_IdelicZeta.Sec1
import RiemannMasullo.AppA_AlgebraicNT.Sec2
import RiemannMasullo.AppD_SchwartzBruhat.Sec1d

/-! # Exact positive unit representatives in a finite rational idelic quotient

Clearing the selected valuations and making the rational real coordinate
positive gives a unique representative modulo the actual projected S-units. -/

public noncomputable section
namespace RiemannMasullo.RatFinitePositiveUnitRep
open NumberField IsDedekindDomain InfinitePlace.Completion
open scoped Classical NNReal NumberField.AdeleRing

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
variable (S : Finset V)

abbrev realCoord : (SAdeleRing ℚ S)ˣ →* ℝ :=
  (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).toMonoidHom.comp
    ((((Pi.evalRingHom _ Rat.infinitePlace).comp (RingHom.fst _ _)).toMonoidHom).comp
      (Units.coeHom _))

@[expose] def Normalized (x : (SAdeleRing ℚ S)ˣ) : Prop :=
  0 < realCoord S x ∧ ∀ v : S, Valued.v (x.val.2 v) = 1

/-- A positive, valuation-zero representative has idele norm equal to its real coordinate. -/
theorem norm_normalized {x : (SAdeleRing ℚ S)ˣ} (hx : Normalized S x) :
    ((sIdeleNorm ℚ S x).val : ℝ) = realCoord S x := by
  let a := sIdeleInsertion ℚ S x
  obtain ⟨harch, hin, hout⟩ := sIdeleInsertion_apply ℚ S x
  have hf (v : V) : ‖a.val.2 v‖ = 1 := by
    by_cases hv : v ∈ S
    · rw [show a.val.2 v = _ from hin ⟨v, hv⟩]
      exact Valued.toNormedField.norm_eq_one_iff.mpr (hx.2 ⟨v, hv⟩)
    · rw [show a.val.2 v = 1 from hout v hv, norm_one]
  rw [← ideleNorm_sIdeleInsertion, ((ideleNorm_spec ℚ).1 a).2,
    finprod_eq_one_of_forall_eq_one hf, mul_one, Fintype.prod_subsingleton _ Rat.infinitePlace,
    Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  change ‖(sIdeleInsertion ℚ S x).val.1 Rat.infinitePlace‖ = _
  rw [harch, ← (isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero
    (map_zero _), Real.norm_eq_abs]
  exact abs_of_pos hx.1

private abbrev proj := Units.map ((adeleProjection ℚ S).comp
  (integralAdelesOutside ℚ S).subtype).toMonoidHom

private def classProj : SIdeleClassGroup ℚ S →* SIdeleQuotient ℚ S :=
  QuotientGroup.lift _ ((QuotientGroup.mk' _).comp (proj S)) (by
    intro u hu
    exact (QuotientGroup.eq_one_iff _).mpr ⟨u, hu, rfl⟩)

private theorem exists_normalized (x : (SAdeleRing ℚ S)ˣ) :
    ∃ y, Normalized S y ∧ (QuotientGroup.mk y : SIdeleQuotient ℚ S) = QuotientGroup.mk x := by
  let j := sIdeleInsertion ℚ S
  obtain ⟨ha, hi, ho⟩ := sIdeleInsertion_apply ℚ S x
  obtain ⟨e, he⟩ := ratIdeleClassGroup_decomposition
  obtain ⟨⟨t, h⟩, ht⟩ := e.surjective (QuotientGroup.mk (j x))
  obtain ⟨g, hg, hf, hc⟩ := he t h
  let ev (v : V) := Units.map (((RestrictedProduct.evalRingHom
    (fun w : V ↦ w.adicCompletion ℚ) v).comp (RingHom.snd (InfiniteAdeleRing ℚ)
      (FiniteAdeleRing (𝓞 ℚ) ℚ))).toMonoidHom)
  have heval (v : V) : ev v g = Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom (h v) :=
    Units.ext (hf v)
  obtain ⟨b, hb⟩ := (mem_range_integralIdeleInsertion ℚ S g).mpr (by
    intro v _
    have hinv : g.inv.2 v = (h v).inv.val := congrArg Units.inv (heval v)
    rw [hf v, hinv]
    exact ⟨(h v).val.property, (h v).inv.property⟩)
  obtain ⟨a, hax⟩ := (mem_range_integralIdeleInsertion ℚ S (j x)).mpr (by
    intro v hv
    constructor
    · rw [show (j x).val.2 v = 1 from ho v hv]; exact one_mem _
    · have H := (sIdeleInsertion_apply ℚ S x⁻¹).2.2 v hv
      rw [map_inv] at H
      rw [show (j x).inv.2 v = 1 from H]; exact one_mem _)
  have hclasses : (QuotientGroup.mk b : SIdeleClassGroup ℚ S) = QuotientGroup.mk a := by
    apply (sIdeleClassInsertion_isOpenEmbedding ℚ S).injective
    change QuotientGroup.mk (integralIdeleInsertion ℚ S b) = QuotientGroup.mk (integralIdeleInsertion ℚ S a)
    rw [hb, hax]; exact hc.symm.trans ht
  have hp : proj S a = x := by
    change Units.map (adeleProjection ℚ S).toMonoidHom (integralIdeleInsertion ℚ S a) = x
    rw [hax]; exact Units.ext (Prod.ext ha (funext hi))
  refine ⟨proj S b, ⟨?_, ?_⟩, (congrArg (classProj S) hclasses).trans (congrArg QuotientGroup.mk hp)⟩
  · change 0 < extensionEmbeddingOfIsReal _ ((integralIdeleInsertion ℚ S b).val.1 Rat.infinitePlace)
    rw [hb, hg]; exact_mod_cast (pos_iff_ne_zero.mpr t.ne_zero : 0 < t.val)
  · intro v
    change Valued.v ((integralIdeleInsertion ℚ S b).val.2 v.val) = 1
    rw [hb, hf]; exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := Units.map (v.val.adicCompletionIntegers ℚ).subtype.toMonoidHom (h v.val))).mp
        ⟨(h v.val).val.property, (h v.val).inv.property⟩

/-- Positive archimedean and valuation-zero representatives form an exact transversal. -/
theorem existsUnique_normalized (c : SIdeleQuotient ℚ S) :
    ∃! y, Normalized S y ∧ QuotientGroup.mk y = c := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨y, hy, he⟩ := exists_normalized S x
  refine ⟨y, ⟨hy, he⟩, ?_⟩
  rintro z ⟨hz, hzc⟩
  have hzy := hzc.trans he.symm
  have hr : realCoord S z = realCoord S y := (norm_normalized S hz).symm.trans
    ((congrArg (fun c : SIdeleQuotient ℚ S ↦ ((sIdeleQuotientNorm ℚ S c).val : ℝ)) hzy).trans
      (norm_normalized S hy))
  obtain ⟨u, hu⟩ := (sIdeleQuotient_mk_eq_one ℚ S (z / y)).mp (by
    change (QuotientGroup.mk' _ : _ →* SIdeleQuotient ℚ S) (z / y) = 1
    rw [map_div]; exact div_eq_one.mpr hzy)
  have hm := congrArg (realCoord S) hu
  have hzy' : realCoord S (z / y) = 1 := by
    rw [div_eq_mul_inv, map_mul, hr, ← map_mul, mul_inv_cancel, map_one]
  rw [hzy'] at hm
  change 1 = extensionEmbeddingOfIsReal _ (algebraMap ℚ Rat.infinitePlace.Completion (u.val.val : ℚ)) at hm
  have hur : (u.val.val : ℚ) = 1 := by
    have : ((u.val.val : ℚ) : ℝ) = 1 := by simpa using hm.symm
    exact_mod_cast this
  have hu1 : u = 1 := Units.ext (Subtype.ext hur)
  apply div_eq_one.mp
  simpa [hu1] using hu

/-- Compensation is exactly by an element of the actual projected diagonal. -/
theorem existsUnique_compensation (x : (SAdeleRing ℚ S)ˣ) :
    ∃! d : sProjectedDiagonal ℚ S, Normalized S (d.val * x) := by
  obtain ⟨y, ⟨hy, he⟩, hu⟩ := existsUnique_normalized S (QuotientGroup.mk x)
  let d : sProjectedDiagonal ℚ S := ⟨y / x, QuotientGroup.eq_iff_div_mem.mp he⟩
  have hd : d.val * x = y := div_mul_cancel _ _
  refine ⟨d, ?_, ?_⟩
  · change Normalized S (d.val * x)
    rwa [hd]
  · intro b hb
    have hq : (QuotientGroup.mk (b.val * x) : SIdeleQuotient ℚ S) = QuotientGroup.mk x := by
      change (QuotientGroup.mk' (sProjectedDiagonal ℚ S)) (b.val * x) =
        (QuotientGroup.mk' (sProjectedDiagonal ℚ S)) x
      rw [map_mul, show (QuotientGroup.mk' _) b.val = 1 from (QuotientGroup.eq_one_iff _).mpr b.property]
      exact one_mul ((QuotientGroup.mk' (sProjectedDiagonal ℚ S)) x)
    exact Subtype.ext (mul_right_cancel ((hu _ ⟨hb, hq⟩).trans hd.symm))
end RiemannMasullo.RatFinitePositiveUnitRep
