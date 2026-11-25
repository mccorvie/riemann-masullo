module

public import RiemannMasullo.Ch03_IdelicZeta.Sec1_RatSLocalUnitRepresentative

/-! # Topology of the genuine rational finite-box quotient

The quotient projection is a multiplicative homeomorphism on the open set of
positive representatives with valuation one at every selected place. -/

public noncomputable section
namespace RiemannMasullo.RatFinitePositiveUnitRep
open NumberField IsDedekindDomain InfinitePlace.Completion
open scoped Classical NumberField.AdeleRing

variable (S : Finset (HeightOneSpectrum (𝓞 ℚ)))

/-- The positive valuation-one representatives, with their inherited multiplication. -/
def normalizedSubmonoid : Submonoid (SAdeleRing ℚ S)ˣ where
  carrier := {x | Normalized S x}
  one_mem' := ⟨by rw [map_one]; exact zero_lt_one, fun v ↦ Valued.v.map_one⟩
  mul_mem' := by
    intro x y hx hy
    refine ⟨(map_mul (realCoord S) x y).symm ▸ mul_pos hx.1 hy.1, fun v ↦ ?_⟩
    change Valued.v (x.val.2 v * y.val.2 v) = 1
    rw [map_mul, hx.2 v, hy.2 v, one_mul]

theorem isOpen_normalized : IsOpen (normalizedSubmonoid S : Set (SAdeleRing ℚ S)ˣ) := by
  have hr : Continuous (realCoord S) :=
    (isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
      (show Continuous (fun x : (SAdeleRing ℚ S)ˣ ↦ x.val.1 Rat.infinitePlace) by fun_prop)
  have hv (v : S) : IsOpen {x : (SAdeleRing ℚ S)ˣ | Valued.v (x.val.2 v) = 1} := by
    have h : IsOpen {a : v.val.adicCompletion ℚ | Valued.v a = 1} := by
      simpa only [Valuation.restrict_eq_one_iff] using
        (Valued.isOpen_sphere (v.val.adicCompletion ℚ) (r := 1) one_ne_zero)
    exact h.preimage (show Continuous (fun x : (SAdeleRing ℚ S)ˣ ↦ x.val.2 v) by fun_prop)
  change IsOpen ({x | 0 < realCoord S x} ∩ {x : (SAdeleRing ℚ S)ˣ | ∀ v : S, Valued.v (x.val.2 v) = 1})
  exact (isOpen_lt continuous_const hr).inter (by simpa only [← Set.ofPred_forall] using isOpen_iInter_of_finite hv)

/-- The actual quotient projection is a multiplicative homeomorphism on the open transversal. -/
def normalizedChart : normalizedSubmonoid S ≃ₜ* SIdeleQuotient ℚ S := by
  let q : normalizedSubmonoid S →* SIdeleQuotient ℚ S :=
    (QuotientGroup.mk' (sProjectedDiagonal ℚ S)).comp (normalizedSubmonoid S).subtype
  have hb : Function.Bijective q := by
    constructor
    · intro x y h
      exact Subtype.ext ((existsUnique_normalized S (q y)).unique ⟨x.property, h⟩ ⟨y.property, rfl⟩)
    · intro c
      obtain ⟨x, ⟨hx, hxc⟩, _⟩ := existsUnique_normalized S c
      exact ⟨⟨x, hx⟩, hxc⟩
  let e := MulEquiv.ofBijective q hb
  let h := e.toEquiv.toHomeomorphOfContinuousOpen
    (QuotientGroup.continuous_mk.comp continuous_subtype_val)
    (QuotientGroup.isOpenQuotientMap_mk.isOpenMap.comp (isOpen_normalized S).isOpenMap_subtype_val)
  exact { e with continuous_toFun := h.continuous_toFun, continuous_invFun := h.continuous_invFun }

@[simp] theorem normalizedChart_apply (x : normalizedSubmonoid S) :
    normalizedChart S x = QuotientGroup.mk x.val := by rw [normalizedChart]; rfl
end RiemannMasullo.RatFinitePositiveUnitRep
