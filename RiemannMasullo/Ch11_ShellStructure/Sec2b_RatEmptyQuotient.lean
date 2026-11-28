module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Norm and theta on the rational quotient with no finite places -/

public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)

private theorem ratEmpty_sInteger_unit_cases (ξ : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ) :
    ξ = 1 ∨ ξ = -1 := by
  have hmem : ∀ x : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ),
      ∃ y : 𝓞 ℚ, algebraMap (𝓞 ℚ) ℚ y = (x : ℚ) := by
    intro x
    have he : ((∅ : Finset V(ℚ)) : Set V(ℚ)).integer ℚ = ⊥ := by
      rw [Finset.coe_empty, integer_empty]
    have hx : (x : ℚ) ∈ (⊥ : Subalgebra (𝓞 ℚ) ℚ) := he ▸ x.property
    exact Algebra.mem_bot.mp hx
  obtain ⟨a, ha⟩ := hmem ξ.val
  obtain ⟨b, hb⟩ := hmem (ξ⁻¹).val
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (𝓞 ℚ) ℚ
    rw [map_mul, ha, hb, map_one]
    have h := congrArg Subtype.val ξ.mul_inv
    exact h
  have hu : IsUnit (Rat.ringOfIntegersEquiv a) := (IsUnit.of_mul_eq_one b hab).map _
  rcases Int.isUnit_iff.mp hu with h | h
  · left
    have ha1 : a = 1 := Rat.ringOfIntegersEquiv.injective (h.trans (map_one _).symm)
    apply Units.ext
    apply Subtype.ext
    rw [← ha, ha1, map_one]
    rfl
  · right
    have ha1 : a = -1 := Rat.ringOfIntegersEquiv.injective (h.trans (by simp))
    apply Units.ext
    apply Subtype.ext
    rw [← ha, ha1, map_neg, map_one]
    rfl

private theorem ratEmpty_sInteger_one_ne_neg_one :
    (1 : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ) ≠ -1 := by
  intro h
  have h' := congrArg (fun u : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ ↦
    Subtype.val (Units.val u)) h
  norm_num at h'

private theorem ratEmpty_sIdeleNorm_eq_realNorm (x : (SAdeleRing ℚ ∅)ˣ) :
    ((sIdeleNorm ℚ ∅ x : ℝ≥0) : ℝ) = ‖x.val.1 Rat.infinitePlace‖ := by
  simp [sIdeleNorm]
  rw [Unique.eq_default Rat.infinitePlace]

/-- The real coordinate preserves the absolute value of the rational completion. -/
theorem ratEmpty_realCompletion_abs (z : Rat.infinitePlace.Completion) :
    |InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace z| = ‖z‖ := by
  rw [← Real.norm_eq_abs, ← dist_zero_right, ← dist_zero_right z,
    ← map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)]
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).dist_eq z 0

private theorem ratEmpty_thetaOnClasses_real (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (φ : ℝ → ℂ) (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace)))
    (x : (SAdeleRing ℚ ∅)ˣ) :
    sLocalAdelicThetaOnClasses ℚ ∅ f (QuotientGroup.mk x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.val.1 Rat.infinitePlace)) +
      φ (-(InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.val.1 Rat.infinitePlace))) := by
  have hU : (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection ℚ ∅)
      (Subring.subtype (integralAdelesOutside ℚ ∅)))))
      (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal ℚ ∅)) (-1)) = -1 := by
    apply Units.ext
    change ((adeleProjection ℚ ∅).comp (integralAdelesOutside ℚ ∅).subtype)
      (integralAdeleDiagonal ℚ ∅
        (-1 : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ).val) =
      (-1 : (SAdeleRing ℚ ∅)ˣ).val
    simp
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
  dsimp only
  rw [tsum_eq_sum (s := {1, -1}) (fun ξ hξ ↦ ?_)]
  · rw [Finset.sum_pair ratEmpty_sInteger_one_ne_neg_one]
    simp only [MonoidHom.comp_apply, hU, map_one, one_mul, hf]
    simp only [Units.val_neg, neg_mul, one_mul]
    rw [show ((-(x : SAdeleRing ℚ ∅)).1 Rat.infinitePlace) =
      -((x : SAdeleRing ℚ ∅).1 Rat.infinitePlace) from rfl, map_neg]
  · rcases ratEmpty_sInteger_unit_cases ξ with h | h <;> simp_all

/-- Every norm-one class of rational real idèles is the identity. -/
theorem ratEmpty_normOne_eq_one (h : (sIdeleQuotientNorm ℚ ∅).ker) : h = 1 := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  apply Subtype.ext
  change (QuotientGroup.mk x : SIdeleQuotient ℚ ∅) = 1
  rw [sIdeleQuotient_mk_eq_one]
  have hn : ‖x.val.1 Rat.infinitePlace‖ = 1 := by
    rw [← ratEmpty_sIdeleNorm_eq_realNorm]
    have h1 : sIdeleNorm ℚ ∅ x = 1 := hg
    rw [h1]
    simp
  rw [← ratEmpty_realCompletion_abs] at hn
  rcases (abs_eq zero_le_one).mp hn with h1 | h1
  · refine ⟨1, ?_⟩
    simp only [map_one]
    apply Units.ext
    refine Prod.ext (funext fun w ↦ ?_) (Subsingleton.elim _ _)
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    apply (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).injective
    exact h1.trans (map_one _).symm
  · refine ⟨-1, ?_⟩
    apply Units.ext
    change (x : SAdeleRing ℚ ∅) = ((adeleProjection ℚ ∅).comp (integralAdelesOutside ℚ ∅).subtype)
      (integralAdeleDiagonal ℚ ∅
        (-1 : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ).val)
    simp only [Units.val_neg, Units.val_one, map_neg, map_one]
    refine Prod.ext (funext fun w ↦ ?_) (Subsingleton.elim _ _)
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    apply (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).injective
    exact h1.trans ((map_neg _ _).trans (congrArg Neg.neg (map_one _))).symm

/-- Over ℚ with `S = ∅` the homogeneous theta function is the theta function on classes
times the total norm-one mass. -/
private theorem ratEmpty_homogeneousTheta_eq_mass_mul (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))) (g : SIdeleQuotient ℚ ∅) :
    sLocalHomogeneousAdelicThetaLinearMap ℚ ∅ ω f g =
      ((sLocalNormOneQuotientMeasure ℚ ∅).real univ : ℂ) * sLocalAdelicThetaOnClasses ℚ ∅ f g := by
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply,
    integral_congr_ae (g := fun _ ↦ sLocalAdelicThetaOnClasses ℚ ∅ f g) (ae_of_all _ fun h ↦ ?_)]
  · rw [integral_const, Complex.real_smul]
  · have := ratEmpty_normOne_eq_one h
    subst this
    simp

/-- The norm separates actual quotient classes of rational real idèles. -/
theorem ratEmpty_sIdeleQuotientNorm_injective : Injective (sIdeleQuotientNorm ℚ ∅) := by
  intro x y h
  have hk : x / y ∈ (sIdeleQuotientNorm ℚ ∅).ker := by simp [MonoidHom.mem_ker, map_div, h]
  exact div_eq_one.mp (congrArg Subtype.val (ratEmpty_normOne_eq_one ⟨x / y, hk⟩))

/-- The actual rational homogeneous theta sum in norm coordinates, with its
norm-one Tamagawa mass retained. The two terms are the two global signs. -/
theorem ratEmpty_homogeneousTheta_real (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)
    (φ : SchwartzMap ℝ ℂ) (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace))) (g : SIdeleQuotient ℚ ∅) :
    sLocalHomogeneousAdelicThetaLinearMap ℚ ∅ ω f g =
      ((sLocalNormOneQuotientMeasure ℚ ∅).real univ : ℂ) *
        (φ (((sIdeleQuotientNorm ℚ ∅ g).val : ℝ≥0) : ℝ) +
          φ (-(((sIdeleQuotientNorm ℚ ∅ g).val : ℝ≥0) : ℝ))) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  let t := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
    (x.val.1 Rat.infinitePlace)
  have hr : (((sIdeleQuotientNorm ℚ ∅ (QuotientGroup.mk x)).val : ℝ≥0) : ℝ) = |t| := by
    rw [show |t| = ‖x.val.1 Rat.infinitePlace‖ from ratEmpty_realCompletion_abs _]
    exact ratEmpty_sIdeleNorm_eq_realNorm x
  rw [ratEmpty_homogeneousTheta_eq_mass_mul, ratEmpty_thetaOnClasses_real f φ hf x, hr]
  change _ * (φ t + φ (-t)) = _ * (φ |t| + φ (-|t|))
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, neg_neg, add_comm (φ (-t))]

end RiemannMasullo
