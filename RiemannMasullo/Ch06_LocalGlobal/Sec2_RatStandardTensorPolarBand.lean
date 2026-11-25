module

public import RiemannMasullo.Ch06_LocalGlobal.Sec2_RatUnramifiedThetaLattice
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b
public import RiemannMasullo.Ch03_IdelicZeta.RatEmptyFourier
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! # Polar membership for the actual rational standard tensor

The Tamagawa transform is the ordinary real transform times the finite
integer indicators, which are self-dual over ℚ. Hence the two real polar
conditions and a real Fourier band imply membership in the genuine S-local
product-band space and its homogeneous theta image. -/

public noncomputable section
namespace RiemannMasullo.RatUnramifiedThetaLattice
open Function Set NumberField IsDedekindDomain
open scoped Classical NumberField.AdeleRing

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "rc" => InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
variable {S : Finset V}
local instance (v : V) : MeasurableSpace (v.adicCompletion ℚ) := borel _
local notation "B∞" => SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ))
local notation "tensor" => sLocalStandardThetaTensor (F := ℚ) (S := S) 1

private abbrev integerIndicator (v : V) : v.adicCompletion ℚ → ℂ :=
  (v.adicCompletionIntegers ℚ : Set _).indicator (fun _ ↦ 1)

private theorem finite_fixed (v : V) : tamagawaFourier (finiteLocalAdditiveTamagawaMeasure ℚ v)
    (finiteLocalStandardCharacter ℚ v) (integerIndicator v) = integerIndicator v := by
  apply (finiteLocalTamagawaFourier_fixes_integers_iff ℚ v).mpr
  have hd : differentIdeal ℤ (𝓞 ℚ) = 1 := by
    rw [Ideal.one_eq_top, ← Ideal.absNorm_eq_one_iff, NumberField.absNorm_differentIdeal ℚ (𝓞 ℚ), NumberField.discr_rat]
    rfl
  rw [hd, Ideal.one_eq_top, Ideal.dvd_iff_le, top_le_iff]
  exact v.isPrime.ne_top

/-- The pointwise additive Tamagawa product-transform formula is the sole Fourier
factorization input. In particular it is imposed on all adeles, not only units. -/
private def StandardProductFourier (f : B∞) (φ : SchwartzMap ℝ ℂ) : Prop :=
  ∀ x : SAdeleRing ℚ S, sAdeleSchwartzFourier (tensor f) (Multiplicative.ofAdd x) =
    (FourierTransform.fourier φ : SchwartzMap ℝ ℂ) (rc (x.1 Rat.infinitePlace)) *
    ∏ v : S, tamagawaFourier (finiteLocalAdditiveTamagawaMeasure ℚ v.val)
      (finiteLocalStandardCharacter ℚ v.val) (integerIndicator v.val) (x.2 v)

private theorem standardTensor_polar_band (f : B∞) (φ : SchwartzMap ℝ ℂ) {Y : ℝ}
    (hf : ∀ a : InfiniteAdeleRing ℚ, f (Multiplicative.ofAdd a) = φ (rc (a Rat.infinitePlace)))
    (hp : StandardProductFourier (S := S) f φ) (h0 : φ 0 = 0)
    (hF0 : (FourierTransform.fourier φ : SchwartzMap ℝ ℂ) 0 = 0)
    (hband : tsupport ⇑(FourierTransform.fourier φ : SchwartzMap ℝ ℂ) ⊆ Metric.closedBall 0 Y) :
    tensor f ∈ sAdelePolarSubspace ℚ S ∧ HasCompactSupport (sAdeleSchwartzFourier (tensor f)).val ∧
    tsupport (sAdeleSchwartzFourier (tensor f)).val ⊆ Multiplicative.toAdd ⁻¹' sLocalPWProductRegion S Y := by
  classical
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  have hp' (x : SAdeleRing ℚ S) := hp x
  change ∀ x : SAdeleRing ℚ S, _ at hp'
  simp_rw [finite_fixed] at hp'
  refine ⟨(mem_sAdelePolarSubspace _).mpr ⟨?_, ?_⟩, ?_⟩
  · rw [sLocalStandardThetaTensor_apply, hf]
    change φ (rc 0) * _ = 0
    rw [map_zero, h0, zero_mul]
  · rw [hp']
    change (FourierTransform.fourier φ : SchwartzMap ℝ ℂ) (rc 0) * _ = 0
    rw [map_zero, hF0, zero_mul]
  · let G := (sAdeleSchwartzFourier (tensor f)).val
    let r (x : Multiplicative (SAdeleRing ℚ S)) := rc (x.toAdd.1 Rat.infinitePlace)
    have hr : Continuous r := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
      ((continuous_apply _).comp (continuous_fst.comp continuous_toAdd))
    have ha : tsupport G ⊆ r ⁻¹' Metric.closedBall 0 Y := by
      refine closure_minimal (fun x hx ↦ hband (subset_tsupport _ ?_)) (Metric.isClosed_closedBall.preimage hr)
      intro hz
      exact hx ((hp' x.toAdd).trans (by rw [show (FourierTransform.fourier φ : SchwartzMap ℝ ℂ) (rc (x.toAdd.1 Rat.infinitePlace)) = 0 from hz, zero_mul]))
    have hb (v : S) : tsupport G ⊆ {x | ‖x.toAdd.2 v‖ ≤ 1} := by
      refine closure_minimal (fun x hx ↦ ?_) (isClosed_le (((continuous_apply v).comp (continuous_snd.comp continuous_toAdd)).norm) continuous_const)
      by_contra hn
      have hout : x.toAdd.2 v ∉ v.val.adicCompletionIntegers ℚ := fun h ↦ hn (Valued.toNormedField.norm_le_one_iff.mpr h)
      exact hx ((hp' x.toAdd).trans (by rw [Finset.prod_eq_zero (Finset.mem_univ v) (Set.indicator_of_notMem hout _), mul_zero]))
    have harch {x} (hx : x ∈ tsupport G) : ‖x.toAdd.1 Rat.infinitePlace‖ ≤ Y := by
      have hh := Metric.mem_closedBall.mp (ha hx)
      rw [dist_zero_right] at hh
      exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _) _).ge.trans hh
    constructor
    · refine (isCompact_sLocalPWBox (F := ℚ) (S := S) (max Y 1)).of_isClosed_subset (isClosed_tsupport _) (fun x hx ↦ ⟨fun w ↦ ?_, fun v ↦ (hb v hx).trans (le_max_right _ _)⟩)
      obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
      rw [Rat.isReal_infinitePlace.mult_eq_one, pow_one]
      exact (harch hx).trans (le_max_left _ _)
    · intro x hx
      change (∏ w : InfinitePlace ℚ, ‖x.toAdd.1 w‖ ^ w.mult) * _ ≤ Y
      rw [Fintype.prod_unique]
      change ‖x.toAdd.1 Rat.infinitePlace‖ ^ Rat.infinitePlace.mult * _ ≤ Y
      rw [Rat.isReal_infinitePlace.mult_eq_one, pow_one]
      exact (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ hb v hx))).trans (harch hx)

/-- The actual homogeneous theta class belongs to the polar invariant level. -/
private theorem standardTensor_generator (f : B∞) {Y : ℝ}
    (h : tensor f ∈ sAdelePolarSubspace ℚ S ∧ HasCompactSupport (sAdeleSchwartzFourier (tensor f)).val ∧
      tsupport (sAdeleSchwartzFourier (tensor f)).val ⊆ Multiplicative.toAdd ⁻¹' sLocalPWProductRegion S Y) :
    (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap ℚ S 1)).mkQ (tensor f) ∈
      sLocalInvariantPW (Finset.Subset.refl S) Y (sAdelePolarSubspace ℚ S) 1 := by
  have hi : sAdeleSchwartzTransition ℚ (Finset.Subset.refl S) (tensor f) = tensor f := by
    apply Subtype.ext
    funext x
    change sAdeleSchwartzTransition ℚ _ _ (Multiplicative.ofAdd x.toAdd) = _
    rw [sAdeleSchwartzTransition_apply, ite_eq_left (fun w hn ↦ (hn w.property).elim)]
    congr 2
  have hm := sLocalInvariantPW_mk_mem (Finset.Subset.refl S) Y (sAdelePolarSubspace ℚ S)
    1 (tensor f) h.2 (hi.symm ▸ h.1)
  rw [hi] at hm
  exact hm

local instance (w : InfinitePlace ℚ) : MeasurableSpace w.Completion := borel _

private def archPart (f : B∞) (w : InfinitePlace ℚ) (z : w.Completion) :=
  f (Multiplicative.ofAdd (Pi.single w z : InfiniteAdeleRing ℚ))

private theorem tensor_product_input (f : B∞) (x : SAdeleRing ℚ S) :
    sLocalStandardThetaTensor (F := ℚ) (S := S) 1 f (Multiplicative.ofAdd x) =
      (∏ w, archPart f w (x.1 w)) * ∏ v : S, integerIndicator v.val (x.2 v) := by
  classical
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  have ha : (∏ w : InfinitePlace ℚ, archPart f w (x.1 w)) =
      f (Multiplicative.ofAdd x.1) := by
    rw [Fintype.prod_unique]
    unfold archPart
    apply congrArg (fun z : InfiniteAdeleRing ℚ ↦ f (Multiplicative.ofAdd z))
    funext w
    obtain rfl : w = default := Subsingleton.elim _ _
    exact @Pi.single_eq_same (InfinitePlace ℚ) InfinitePlace.Completion _
      (fun a b ↦ Classical.propDecidable (a = b)) _ _
  rw [sLocalStandardThetaTensor_apply, ha]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    change finiteStandardGaussianValue _ _ _ = _
    rw [finiteStandardGaussianValue]
    have ht : ∀ a ∈ (v.val.adicCompletionIntegers ℚ).units,
        sLocalFiniteRestriction v (1 : QuasiCharacter (SIdeleQuotient ℚ S)) a = 1 := by
      intro a _
      rfl
    rw [ite_eq_left ht]
    rfl

/-- The empty-stage transform identifies exactly the same archimedean product
as the general product formula, with its Tamagawa measure and character intact. -/
private theorem standardProductFourier_actual (f : B∞) (φ : SchwartzMap ℝ ℂ)
    (hf : ∀ a : InfiniteAdeleRing ℚ, f (Multiplicative.ofAdd a) = φ (rc (a Rat.infinitePlace))) :
    StandardProductFourier (S := S) f φ := by
  classical
  unfold StandardProductFourier
  intro x
  let f₀ := sLocalStandardThetaTensor (F := ℚ) (S := ∅) 1 f
  let y : SAdeleRing ℚ ∅ := (x.1, 0)
  have h₀ := sLocal_fourier_prod f₀ (archPart f) (fun v ↦ integerIndicator v.val)
    (tensor_product_input (S := ∅) f) y
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at h₀
  have hreal := sAdeleSchwartzFourier_ratEmpty_apply φ f₀ (fun z ↦ by
    dsimp only [f₀]
    rw [sLocalStandardThetaTensor_apply, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    exact hf _) y
  rw [sLocal_fourier_prod _ (archPart f) (fun v ↦ integerIndicator v.val) (tensor_product_input f) x]
  exact congrArg (fun t : ℂ ↦ t * _) (h₀.symm.trans hreal)

theorem standardTensor_polar_band_actual (f : B∞) (φ : SchwartzMap ℝ ℂ) {Y : ℝ}
    (hf : ∀ a : InfiniteAdeleRing ℚ, f (Multiplicative.ofAdd a) = φ (rc (a Rat.infinitePlace)))
    (h0 : φ 0 = 0) (hF0 : (FourierTransform.fourier φ : SchwartzMap ℝ ℂ) 0 = 0)
    (hband : tsupport ⇑(FourierTransform.fourier φ : SchwartzMap ℝ ℂ) ⊆ Metric.closedBall 0 Y) :
    let t := sLocalStandardThetaTensor (F := ℚ) (S := S) 1 f
    t ∈ sAdelePolarSubspace ℚ S ∧ HasCompactSupport (sAdeleSchwartzFourier t).val ∧
      tsupport (sAdeleSchwartzFourier t).val ⊆ Multiplicative.toAdd ⁻¹' sLocalPWProductRegion S Y :=
  standardTensor_polar_band f φ hf (standardProductFourier_actual f φ hf) h0 hF0 hband


/-- The true unramified rational standard tensor gives an actual polar invariant
theta generator whenever its real test satisfies the two polar conditions and band. -/
theorem standardTensor_generator_actual (f : B∞) (φ : SchwartzMap ℝ ℂ) {Y : ℝ}
    (hf : ∀ a : InfiniteAdeleRing ℚ, f (Multiplicative.ofAdd a) = φ (rc (a Rat.infinitePlace)))
    (h0 : φ 0 = 0) (hF0 : (FourierTransform.fourier φ : SchwartzMap ℝ ℂ) 0 = 0)
    (hband : tsupport ⇑(FourierTransform.fourier φ : SchwartzMap ℝ ℂ) ⊆ Metric.closedBall 0 Y) :
    (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap ℚ S 1)).mkQ (tensor f) ∈
      sLocalInvariantPW (Finset.Subset.refl S) Y (sAdelePolarSubspace ℚ S) 1 :=
  standardTensor_generator f (standardTensor_polar_band_actual f φ hf h0 hF0 hband)

end RiemannMasullo.RatUnramifiedThetaLattice
