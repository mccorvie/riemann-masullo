module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The Gaussian integers at the complex place of the Gaussian number field

The fourth cyclotomic field has one infinite place. We identify its integer ring with
the Gaussian integers using the complex embedding selected by that place.
-/

@[expose] public noncomputable section

namespace NumberField.Gaussian

local notation "K" => CyclotomicField 4 ℚ

private theorem exists_complex_place :
    ∃ w : InfinitePlace K, w.IsComplex ∧ ∀ v : InfinitePlace K, v = w := by
  let : IsCyclotomicExtension {4} ℚ K := CyclotomicField.isCyclotomicExtension 4 ℚ
  let : NumberField.IsTotallyComplex K :=
    IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) K (by decide)
  have hn : InfinitePlace.nrComplexPlaces K = 1 := by
    rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 4]
    decide
  have hcard : Fintype.card (InfinitePlace K) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hn,
      IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add]
  obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.mp hcard
  exact ⟨w, IsTotallyComplex.isComplex w, hw⟩

/-- The unique infinite place of the fourth cyclotomic field. -/
def place : InfinitePlace K := Classical.arbitrary _

/-- The Gaussian place is complex. -/
theorem isComplex_place : place.IsComplex := by
  obtain ⟨w, hw, heq⟩ := exists_complex_place
  rwa [heq place]

/-- Every infinite place of the Gaussian field is this place. -/
theorem eq_place (w : InfinitePlace K) : w = place := by
  obtain ⟨v, _, heq⟩ := exists_complex_place
  exact (heq w).trans (heq place).symm

/-- For either complex embedding, the Gaussian integers identify with the full integer
ring in a way that takes the imaginary generator to the standard complex unit. -/
theorem exists_integersEquiv_of_embedding (σ : K →+* ℂ) :
    ∃ e : GaussianInt ≃+* 𝓞 K, ∀ z : GaussianInt, σ (e z : K) = (z : ℂ) := by
  let : IsCyclotomicExtension {4} ℚ K := CyclotomicField.isCyclotomicExtension 4 ℚ
  let ζ := IsCyclotomicExtension.zeta 4 ℚ K
  have hζ : IsPrimitiveRoot ζ 4 := IsCyclotomicExtension.zeta_spec 4 ℚ K
  obtain ⟨n, _, hn⟩ := (hζ.map_of_injective σ.injective).eq_pow_of_pow_eq_one Complex.I_pow_four
  let x := ζ ^ n
  have hx : σ x = Complex.I := by simpa [x] using hn
  have hxprim : IsPrimitiveRoot x 4 :=
    (show IsPrimitiveRoot (σ x) 4 by rw [hx]; exact Complex.isPrimitiveRoot_I).of_map_of_injective
      σ.injective
  let t : 𝓞 K := hxprim.toInteger
  have ht : t * t = ((-1 : ℤ) : 𝓞 K) := by
    apply Subtype.ext
    apply σ.injective
    change σ (x * x) = σ ((-1 : ℤ) : K)
    simp [hx]
  let φ : GaussianInt →+* 𝓞 K := Zsqrtd.lift ⟨t, ht⟩
  have hcompat (z : GaussianInt) : σ (φ z : K) = (z : ℂ) := by
    change σ ((z.re : K) + (z.im : K) * x) = _
    simp [hx, GaussianInt.toComplex_def]
  have hinj : Function.Injective φ := by
    intro a b hab
    apply GaussianInt.toComplex_injective
    exact (hcompat a).symm.trans ((congrArg (fun y : 𝓞 K ↦ σ (y : K)) hab).trans (hcompat b))
  have hsurj : Function.Surjective φ := by
    apply φ.toIntAlgHom.range_eq_top.mp
    apply top_unique
    rw [← IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hxprim]
    apply Algebra.adjoin_le
    intro y hy
    obtain rfl : y = t := Set.mem_singleton_iff.mp hy
    refine ⟨Zsqrtd.sqrtd, ?_⟩
    change φ Zsqrtd.sqrtd = t
    simp [φ, Zsqrtd.lift_apply_apply]
  exact ⟨RingEquiv.ofBijective φ ⟨hinj, hsurj⟩, hcompat⟩

/-- The Gaussian integer isomorphism oriented by the embedding chosen for the infinite place. -/
def integersEquiv : GaussianInt ≃+* 𝓞 K :=
  (exists_integersEquiv_of_embedding place.embedding).choose

/-- The chosen field embedding agrees with the standard complex value of every Gaussian integer. -/
@[simp] theorem embedding_integersEquiv (z : GaussianInt) :
    place.embedding (integersEquiv z : K) = (z : ℂ) :=
  (exists_integersEquiv_of_embedding place.embedding).choose_spec z

/-- The completion isomorphism used for the complex place has the same orientation. -/
@[simp] theorem completion_integersEquiv (z : GaussianInt) :
    InfinitePlace.Completion.ringEquivComplexOfIsComplex isComplex_place
      ((integersEquiv z : K) : place.Completion) = (z : ℂ) := by
  rw [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
  change InfinitePlace.Completion.extensionEmbedding place
    (((WithAbs.equiv place.1).symm (integersEquiv z : K) : WithAbs place.1) : place.Completion) = _
  rw [InfinitePlace.Completion.extensionEmbedding_coe, RingEquiv.apply_symm_apply]
  exact embedding_integersEquiv z

end NumberField.Gaussian
