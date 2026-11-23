module

public import RiemannMasullo.Ch11_ShellStructure.Sec2b
import RiemannMasullo.Ch03_IdelicZeta.RatEmptyFourier
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch11_ShellStructure.Sec2a_PrimePVRefutation
import all RiemannMasullo.Ch06_LocalGlobal.Sec2
import all RiemannMasullo.Ch03_IdelicZeta.Sec3
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Normed.Operator.Banach

/-! # §11.2.1–11.2.2 assertions that are false as printed -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8
set_option Elab.async false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSIdeleQuotientMeasurableSpaceSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "m𝔽(" F ")" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽(F) →ₜ* ℝ≥0ˣ)
local notation "mₛ(" F ", " S ")" =>
  (⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ :
    SIdeleQuotient F S →ₜ* ℝ≥0ˣ)
local notation "μₛ(" F ", " S ")" => sLocalQuotientTamagawaMeasure F S
local notation "Wω(" F ", " hs ", " ω ")" =>
  actionIsotype ((hardySobolevTranslation (ideleClassTamagawaMeasure F) (m𝔽(F))
    0 0 _ (le_rfl (a := (0 : ℝ))) hs).comp (ideleClassNorm F).ker.subtype) ω
local notation "localMeasure(" F ", " S ", " s ")" =>
  (μₛ(F, S)).withDensity (fun g ↦
    ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (((mₛ(F, S)) g).val : ℝ))))
local notation "localTheta(" F ", " S ", " a ", " ω ", " f ")" =>
  modulationWeight (mₛ(F, S)) a (sLocalHomogeneousAdelicThetaLinearMap F S ω f)

local notation "qₛ(" F ", " S ", " ω ")" =>
  (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)).mkQ

private theorem sec2bP_units (ξ : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ) :
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

private theorem sec2bP_one_ne_neg_one :
    (1 : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ) ≠ -1 := by
  intro h
  have h' := congrArg (fun u : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ ↦
    Subtype.val (Units.val u)) h
  norm_num at h'

private theorem sec2bP_norm (x : (SAdeleRing ℚ ∅)ˣ) :
    ((sIdeleNorm ℚ ∅ x : ℝ≥0) : ℝ) = ‖x.val.1 Rat.infinitePlace‖ := by
  simp [sIdeleNorm]
  rw [Unique.eq_default Rat.infinitePlace]

private theorem sec2bP_abs (z : Rat.infinitePlace.Completion) :
    |InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace z| = ‖z‖ := by
  rw [← Real.norm_eq_abs, ← dist_zero_right, ← dist_zero_right z,
    ← map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)]
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).dist_eq z 0

private theorem sec2bP_thetaClasses (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
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
  · rw [Finset.sum_pair sec2bP_one_ne_neg_one]
    simp only [MonoidHom.comp_apply, hU, map_one, one_mul, hf]
    simp only [Units.val_neg, neg_mul, one_mul]
    rw [show ((-(x : SAdeleRing ℚ ∅)).1 Rat.infinitePlace) =
      -((x : SAdeleRing ℚ ∅).1 Rat.infinitePlace) from rfl, map_neg]
  · rcases sec2bP_units ξ with h | h <;> simp_all

private theorem sec2bP_normOne_trivial (h : (sIdeleQuotientNorm ℚ ∅).ker) : h = 1 := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  apply Subtype.ext
  change (QuotientGroup.mk x : SIdeleQuotient ℚ ∅) = 1
  rw [sIdeleQuotient_mk_eq_one]
  have hn : ‖x.val.1 Rat.infinitePlace‖ = 1 := by
    rw [← sec2bP_norm]
    have h1 : sIdeleNorm ℚ ∅ x = 1 := hg
    rw [h1]
    simp
  rw [← sec2bP_abs] at hn
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

open LineDeriv in
private theorem sec2bP_lineDeriv_tsupport (f : SchwartzMap ℝ ℂ) :
    tsupport ⇑(∂_{(1 : ℝ)} f : SchwartzMap ℝ ℂ) ⊆ tsupport ⇑f := by
  apply closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra h
  apply hx
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    image_eq_zero_of_notMem_tsupport (fun h' ↦ h (tsupport_fderiv_subset ℝ h'))]
  rfl

open scoped FourierTransform in
open LineDeriv in
private theorem sec2bP_test : ∃ φ : SchwartzMap ℝ ℂ,
    φ 0 = 0 ∧ (𝓕 φ : SchwartzMap ℝ ℂ) 0 = 0 ∧ HasCompactSupport ⇑(𝓕 φ : SchwartzMap ℝ ℂ) ∧
      tsupport ⇑(𝓕 φ : SchwartzMap ℝ ℂ) ⊆ Metric.closedBall 0 1 ∧
      ∃ c > 0, ∀ t : ℝ, |t| ≤ 1 → c * t ^ 2 ≤ ‖φ t + φ (-t)‖ := by
  let b : ContDiffBump (1 / 16 : ℝ) := ⟨1 / 64, 1 / 32, by norm_num, by norm_num⟩
  have hb_supp : HasCompactSupport (fun ξ : ℝ ↦ (b ξ : ℂ)) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hb_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ ↦ (b ξ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  let ψ₀ : SchwartzMap ℝ ℂ := hb_supp.toSchwartzMap hb_smooth
  have hψ₀ (ξ : ℝ) : ψ₀ ξ = (b ξ : ℂ) := rfl
  let ψ : SchwartzMap ℝ ℂ := ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} ψ₀)
  have hφ (t : ℝ) : (𝓕⁻ ψ) t = ((-(4 * Real.pi ^ 2 * t ^ 2) : ℝ) : ℂ) * (𝓕⁻ ψ₀) t := by
    have hg : (fun x : ℝ ↦ inner ℝ x (1 : ℝ)).HasTemperateGrowth := by fun_prop
    simp only [ψ, SchwartzMap.fourierInv_lineDerivOp_eq, smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
    simp only [inner, one_mul, star_trivial, RCLike.re_to_real, Complex.real_smul]
    push_cast
    linear_combination ((4 : ℂ) * Real.pi ^ 2 * t ^ 2 * (𝓕⁻ ψ₀) t) * Complex.I_sq
  have htsψ₀ : tsupport ⇑ψ₀ ⊆ Metric.closedBall (1 / 16) (1 / 32) := by
    rw [← b.tsupport_eq]
    exact tsupport_comp_subset Complex.ofReal_zero _
  have htsψ : tsupport ⇑ψ ⊆ Metric.closedBall (1 / 16) (1 / 32) :=
    (sec2bP_lineDeriv_tsupport _).trans ((sec2bP_lineDeriv_tsupport _).trans htsψ₀)
  have hF : 𝓕 (𝓕⁻ ψ) = ψ := FourierTransform.fourier_fourierInv_eq ψ
  refine ⟨𝓕⁻ ψ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hφ]
    simp
  · rw [hF]
    refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
    have h' := htsψ h
    rw [Metric.mem_closedBall, Real.dist_eq] at h'
    norm_num [abs_le] at h'
  · rw [hF]
    exact (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) htsψ
  · rw [hF]
    refine htsψ.trans (Metric.closedBall_subset_closedBall' ?_)
    norm_num
  · have hint (t : ℝ) : Integrable (fun ξ : ℝ ↦ 𝐞 (inner ℝ ξ t) • ψ₀ ξ) := by
      refine ψ₀.integrable.norm.mono' (by fun_prop) (ae_of_all _ fun ξ ↦ ?_)
      rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
    have hsum (t : ℝ) : ((𝓕⁻ ψ₀) t + (𝓕⁻ ψ₀) (-t)).re =
        ∫ ξ, 2 * Real.cos (2 * Real.pi * (ξ * t)) * b ξ := by
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, Real.fourierInv_eq,
        ← integral_add (hint t) (hint (-t))]
      refine (integral_re ((hint t).add (hint (-t)))).symm.trans ?_
      congr 1
      funext ξ
      simp only [Circle.smul_def, hψ₀, Real.fourierChar_apply, inner, star_trivial, RCLike.re_to_real]
      simp only [Pi.add_apply, smul_eq_mul, RCLike.re_to_complex, Complex.add_re,
        Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
      rw [show -t * ξ = -(t * ξ) by ring, mul_neg, Real.cos_neg, mul_comm ξ t]
      ring
    have hb_int : 0 < ∫ ξ, b ξ := b.integral_pos
    refine ⟨4 * Real.pi ^ 2 * ∫ ξ, b ξ, by positivity, fun t ht ↦ ?_⟩
    have hle : ∫ ξ, b ξ ≤ ∫ ξ, 2 * Real.cos (2 * Real.pi * (ξ * t)) * b ξ := by
      refine integral_mono b.integrable ?_ fun ξ ↦ ?_
      · exact (b.integrable.const_mul 2).mono'
          (Continuous.aestronglyMeasurable (by have := b.continuous; fun_prop))
          (ae_of_all _ fun ξ ↦ by
            rw [norm_mul, norm_mul, Real.norm_of_nonneg (b.nonneg' ξ), Real.norm_two,
              Real.norm_eq_abs]
            have := Real.abs_cos_le_one (2 * Real.pi * (ξ * t))
            have := b.nonneg' ξ
            calc 2 * |Real.cos (2 * Real.pi * (ξ * t))| * b ξ ≤ 2 * 1 * b ξ := by gcongr
              _ = 2 * b ξ := by ring)
      · by_cases hξ : b ξ = 0
        · simp [hξ]
        have hmem : ξ ∈ Metric.ball (1 / 16 : ℝ) (1 / 32) := by
          rw [← b.support_eq]; exact hξ
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hmem
        have hx : |2 * Real.pi * (ξ * t)| ≤ 2 * 3.15 * (3 / 32) := by
          rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]
          have h1 : |ξ| ≤ 3 / 32 := by rw [abs_le]; constructor <;> linarith
          have := Real.pi_lt_d2
          have h2 : |ξ| * |t| ≤ 3 / 32 := by
            calc |ξ| * |t| ≤ 3 / 32 * 1 := by gcongr
              _ = 3 / 32 := by ring
          have h3 : 2 * Real.pi * (|ξ| * |t|) ≤ 2 * 3.15 * (3 / 32) := by
            gcongr
          exact h3
        have hc := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * (ξ * t))
        have hsq : (2 * Real.pi * (ξ * t)) ^ 2 ≤ (2 * 3.15 * (3 / 32)) ^ 2 := by
          rw [← sq_abs]; gcongr
        have hcos : 1 / 2 ≤ Real.cos (2 * Real.pi * (ξ * t)) := by norm_num at hsq; linarith
        have h2c : (1 : ℝ) ≤ 2 * Real.cos (2 * Real.pi * (ξ * t)) := by linarith
        have h4 := mul_le_mul_of_nonneg_right h2c (b.nonneg' ξ)
        rwa [one_mul] at h4
    have heq : (𝓕⁻ ψ) t + (𝓕⁻ ψ) (-t) =
        (((-(4 * Real.pi ^ 2 * t ^ 2)) : ℝ) : ℂ) * ((𝓕⁻ ψ₀) t + (𝓕⁻ ψ₀) (-t)) := by
      rw [hφ, hφ]; push_cast; ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by positivity)]
    calc 4 * Real.pi ^ 2 * (∫ ξ, b ξ) * t ^ 2
        ≤ 4 * Real.pi ^ 2 * t ^ 2 * ((𝓕⁻ ψ₀) t + (𝓕⁻ ψ₀) (-t)).re := by
          rw [hsum]
          have : 0 ≤ 4 * Real.pi ^ 2 * t ^ 2 := by positivity
          calc 4 * Real.pi ^ 2 * (∫ ξ, b ξ) * t ^ 2 = 4 * Real.pi ^ 2 * t ^ 2 * (∫ ξ, b ξ) := by
                ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hle this
      _ ≤ 4 * Real.pi ^ 2 * t ^ 2 * ‖(𝓕⁻ ψ₀) t + (𝓕⁻ ψ₀) (-t)‖ := by
          gcongr; exact Complex.re_le_norm _
    exact le_rfl

/-- The trivial character restricted to the norm-one classes is unramified outside `S = ∅`. -/
private theorem sec2bP_unramified :
    NormOneCharacterUnramifiedOutside ((1 : PontryaginDual C𝔽(ℚ)).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))) ∅ :=
  ⟨⟨1, (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩

/-- Over ℚ with `S = ∅` the S-integers are a principal ideal ring. -/
private theorem sec2bP_pic :
    Subsingleton (CommRing.Pic (((∅ : Finset V(ℚ)) : Set V(ℚ)).integer ℚ)) := by
  rw [Finset.coe_empty, integer_empty]
  let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
  let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
  let := IsPrincipalIdealRing.of_surjective i i.surjective
  infer_instance

/-- The norm-one quotient over ℚ with `S = ∅` is a point of positive finite mass. -/
private theorem sec2bP_mass_pos : 0 < (sLocalNormOneQuotientMeasure ℚ ∅).real univ := by
  have := (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := ∅)).1
  have : Subsingleton (sIdeleQuotientNorm ℚ ∅).ker :=
    ⟨fun a b ↦ (sec2bP_normOne_trivial a).trans (sec2bP_normOne_trivial b).symm⟩
  have : Finite (sIdeleQuotientNorm ℚ ∅).ker := Finite.of_subsingleton
  have : CompactSpace (sIdeleQuotientNorm ℚ ∅).ker := Finite.compactSpace
  exact ENNReal.toReal_pos (isOpen_univ.measure_pos _ ⟨1, trivial⟩).ne'
    isCompact_univ.measure_lt_top.ne

/-- Over ℚ with `S = ∅` the homogeneous theta function is the theta function on classes
times the total norm-one mass. -/
private theorem sec2bP_homTheta (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))) (g : SIdeleQuotient ℚ ∅) :
    sLocalHomogeneousAdelicThetaLinearMap ℚ ∅ ω f g =
      ((sLocalNormOneQuotientMeasure ℚ ∅).real univ : ℂ) * sLocalAdelicThetaOnClasses ℚ ∅ f g := by
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply,
    integral_congr_ae (g := fun _ ↦ sLocalAdelicThetaOnClasses ℚ ∅ f g) (ae_of_all _ fun h ↦ ?_)]
  · rw [integral_const, Complex.real_smul]
  · have := sec2bP_normOne_trivial h
    subst this
    simp

/-- The test of the counterexample weighted by the inverse square of the norm stays
bounded below on classes of norm less than one. -/
private theorem sec2bP_lower (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)
    (φ : SchwartzMap ℝ ℂ) (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace)))
    (c : ℝ) (hlow : ∀ t : ℝ, |t| ≤ 1 → c * t ^ 2 ≤ ‖φ t + φ (-t)‖) (x : (SAdeleRing ℚ ∅)ˣ)
    (hx : ((sIdeleQuotientNorm ℚ ∅ (QuotientGroup.mk x) : ℝ≥0) : ℝ) < 1) :
    (sLocalNormOneQuotientMeasure ℚ ∅).real univ * c ≤
      ‖localTheta(ℚ, ∅, -2, ω, f) (QuotientGroup.mk x)‖ := by
  set t := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
    (x.val.1 Rat.infinitePlace) with ht
  have hr : ((sIdeleQuotientNorm ℚ ∅ (QuotientGroup.mk x) : ℝ≥0) : ℝ) = |t| := by
    rw [ht, sec2bP_abs]; exact sec2bP_norm x
  have hpos : 0 < |t| := by
    rw [← hr]; exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hν := sec2bP_mass_pos
  have h1 := hlow t (by rw [← hr]; exact hx.le)
  change ‖((((sIdeleQuotientNorm ℚ ∅ (QuotientGroup.mk x) : ℝ≥0) : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) *
    sLocalHomogeneousAdelicThetaLinearMap ℚ ∅ ω f (QuotientGroup.mk x)‖ ≥ _
  rw [sec2bP_homTheta, sec2bP_thetaClasses f φ hf x, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg hν.le, hr,
    Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _),
    Real.rpow_neg (abs_nonneg t), Real.rpow_two, ← ht]
  have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have hne : |t| ^ 2 ≠ 0 := by positivity
  calc (sLocalNormOneQuotientMeasure ℚ ∅).real univ * c
      = (|t| ^ 2)⁻¹ * ((sLocalNormOneQuotientMeasure ℚ ∅).real univ * (c * t ^ 2)) := by
        rw [ht2]; field_simp
    _ ≤ _ := by gcongr

/-- A left-invariant measure on a group with a continuous surjection onto the positive reals
gives infinite mass to the elements of norm less than one. -/
private theorem sec2bP_measure {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure]
    (N : G →* ℝ≥0ˣ) (hN : Continuous N) (hs : Function.Surjective N) :
    μ {g | ((N g : ℝ≥0) : ℝ) < 1} = ⊤ := by
  obtain ⟨t, ht⟩ := hs (Units.mk0 (2 : ℝ≥0) two_ne_zero)
  obtain ⟨g₀, hg₀⟩ := hs (Units.mk0 (3 / 4 : ℝ≥0) (by norm_num))
  have hcont : Continuous fun g ↦ ((N g : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp hN)
  let A : Set G := {g | 1 / 2 < ((N g : ℝ≥0) : ℝ) ∧ ((N g : ℝ≥0) : ℝ) < 1}
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)
  have hg₀A : g₀ ∈ A := by
    simp only [A, mem_ofPred_eq, hg₀, Units.val_mk0, NNReal.coe_div, NNReal.coe_ofNat]
    norm_num
  have hA0 : μ A ≠ 0 := (hAo.measure_pos μ ⟨g₀, hg₀A⟩).ne'
  let B (k : ℕ) : Set G := (fun g ↦ t ^ k * g) ⁻¹' A
  have hB (k : ℕ) (g : G) : g ∈ B k ↔
      1 / 2 < 2 ^ k * ((N g : ℝ≥0) : ℝ) ∧ 2 ^ k * ((N g : ℝ≥0) : ℝ) < 1 := by
    show (1 / 2 < ((N (t ^ k * g) : ℝ≥0) : ℝ) ∧ ((N (t ^ k * g) : ℝ≥0) : ℝ) < 1) ↔ _
    rw [map_mul, map_pow, ht]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, NNReal.coe_mul,
      NNReal.coe_pow, NNReal.coe_ofNat]
  have hmeas (k : ℕ) : μ (B k) = μ A := measure_preimage_mul μ (t ^ k) A
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    have key (k l : ℕ) (h : k < l) (g : G) (h1 : g ∈ B k) (h2 : g ∈ B l) : False := by
      rw [hB] at h1 h2
      have h2l : (2 : ℝ) * 2 ^ k ≤ 2 ^ l := by
        calc (2 : ℝ) * 2 ^ k = 2 ^ (k + 1) := by ring
          _ ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) h
      have hr : 0 ≤ ((N g : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      nlinarith
    intro k l hkl
    rw [Function.onFun, Set.disjoint_left]
    intro g h1 h2
    rcases lt_or_gt_of_ne hkl with h | h
    · exact key k l h g h1 h2
    · exact key l k h g h2 h1
  have hsub : (⋃ k, B k) ⊆ {g | ((N g : ℝ≥0) : ℝ) < 1} := by
    intro g hg
    obtain ⟨k, hk⟩ := mem_iUnion.mp hg
    rw [hB] at hk
    have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hr : 0 ≤ ((N g : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    simp only [mem_ofPred_eq]
    nlinarith
  refine eq_top_mono (measure_mono hsub) ?_
  rw [measure_iUnion hdisj (fun k ↦ (measurable_const_mul (t ^ k)) hAo.measurableSet)]
  simp only [hmeas]
  exact ENNReal.tsum_const_eq_top_of_ne_zero hA0

/-- The weighted theta function of the counterexample is not square integrable. -/
private theorem sec2bP_not_memLp (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)
    (φ : SchwartzMap ℝ ℂ) (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace)))
    (c : ℝ) (hc : 0 < c) (hlow : ∀ t : ℝ, |t| ≤ 1 → c * t ^ 2 ≤ ‖φ t + φ (-t)‖) :
    ¬ MemLp (localTheta(ℚ, ∅, -2, ω, f)) 2 (localMeasure(ℚ, ∅, 0)) := by
  intro hm
  have hμ : localMeasure(ℚ, ∅, 0) = μₛ(ℚ, ∅) := by
    conv_rhs => rw [← withDensity_one (μ := μₛ(ℚ, ∅))]
    congr 1
    funext g
    simp [intervalSobolevDensity]
  rw [hμ] at hm
  let Θ := localTheta(ℚ, ∅, -2, ω, f)
  have hint : Integrable (fun g ↦ ‖Θ g‖ ^ (2 : ℝ)) μₛ(ℚ, ∅) := by
    simpa using hm.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
  have : BorelSpace (SIdeleQuotient ℚ ∅) := ⟨rfl⟩
  have hW := sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := ∅)
  have : (sLocalQuotientTamagawaMeasure ℚ ∅).IsHaarMeasure := hW.1
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section (F := ℚ) (S := ∅)
  have hNc : Continuous (sIdeleQuotientNorm ℚ ∅) :=
    (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
  have hB := sec2bP_measure (sLocalQuotientTamagawaMeasure ℚ ∅)
    (sIdeleQuotientNorm ℚ ∅) hNc hσ.surjective
  let B := {g : SIdeleQuotient ℚ ∅ | ((sIdeleQuotientNorm ℚ ∅ g : ℝ≥0) : ℝ) < 1}
  have hBm : MeasurableSet B :=
    (isOpen_lt (NNReal.continuous_coe.comp (Units.continuous_val.comp hNc))
      continuous_const).measurableSet
  set K := (sLocalNormOneQuotientMeasure ℚ ∅).real univ * c with hK
  have hKpos : 0 < K := mul_pos sec2bP_mass_pos hc
  have hlow' : ∀ g ∈ B, ENNReal.ofReal (K ^ (2 : ℝ)) ≤ ‖‖Θ g‖ ^ (2 : ℝ)‖ₑ := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 := sec2bP_lower ω φ f hf c hlow x hg
    rw [Real.eNorm_eq_ofReal (by positivity)]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hKpos.le h1 (by norm_num))
  have hfin : (∫⁻ g, ‖‖Θ g‖ ^ (2 : ℝ)‖ₑ ∂μₛ(ℚ, ∅)) < ⊤ := hint.hasFiniteIntegral
  have hge : ⊤ ≤ ∫⁻ g, ‖‖Θ g‖ ^ (2 : ℝ)‖ₑ ∂μₛ(ℚ, ∅) :=
    calc (⊤ : ENNReal) = ENNReal.ofReal (K ^ (2 : ℝ)) * μₛ(ℚ, ∅) B := by
          rw [hB, ENNReal.mul_top (by simp; positivity)]
      _ = ∫⁻ _ in B, ENNReal.ofReal (K ^ (2 : ℝ)) ∂μₛ(ℚ, ∅) := (setLIntegral_const B _).symm
      _ ≤ ∫⁻ g in B, ‖‖Θ g‖ ^ (2 : ℝ)‖ₑ ∂μₛ(ℚ, ∅) := setLIntegral_mono' hBm hlow'
      _ ≤ _ := setLIntegral_le_lintegral B _
  exact absurd (lt_of_le_of_lt hge hfin) (lt_irrefl _)

/-- The transition from `∅` to itself is the identity. -/
private theorem sec2bP_transition (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))) :
    sAdeleSchwartzTransition ℚ (le_refl (∅ : Finset V(ℚ))) f = f := by
  refine Subtype.ext (funext fun x ↦ ?_)
  change sAdeleSchwartzTransition ℚ (le_refl (∅ : Finset V(ℚ))) f
    (Multiplicative.ofAdd (Multiplicative.toAdd x)) = f x
  rw [sAdeleSchwartzTransition_apply, ite_eq_left (fun w ↦ absurd w.2 (Finset.notMem_empty _))]
  rfl

/-- The test of the counterexample has compact Fourier support inside the unit ball
at the real place. -/
private theorem sec2bP_inBand (φ : SchwartzMap ℝ ℂ)
    (hts : tsupport ⇑(FourierTransform.fourier φ : SchwartzMap ℝ ℂ) ⊆ Metric.closedBall 0 1)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace))) :
    HasCompactSupport (sAdeleSchwartzFourier f).val ∧
      tsupport (sAdeleSchwartzFourier f).val ⊆
        Multiplicative.toAdd ⁻¹' {x : SAdeleRing ℚ ∅ | ‖x.1 Rat.infinitePlace‖ ≤ 1} := by
  let r : Multiplicative (SAdeleRing ℚ ∅) → ℝ := fun y ↦
    InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
      ((Multiplicative.toAdd y).1 Rat.infinitePlace)
  have hr : Continuous r :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous.comp
      ((continuous_apply _).comp (continuous_fst.comp continuous_toAdd))
  have hsub : tsupport (sAdeleSchwartzFourier f).val ⊆
      r ⁻¹' tsupport ⇑(FourierTransform.fourier φ : SchwartzMap ℝ ℂ) := by
    refine closure_minimal (fun y hy ↦ ?_) ((isClosed_tsupport _).preimage hr)
    refine subset_tsupport _ ?_
    rw [mem_support] at hy ⊢
    rwa [← sAdeleSchwartzFourier_ratEmpty_apply φ f hf]
  have hsub' : tsupport (sAdeleSchwartzFourier f).val ⊆
      Multiplicative.toAdd ⁻¹' {x : SAdeleRing ℚ ∅ | ‖x.1 Rat.infinitePlace‖ ≤ 1} := by
    intro y hy
    have h := hts (hsub hy)
    rw [Metric.mem_closedBall, dist_zero_right] at h
    change ‖(Multiplicative.toAdd y).1 Rat.infinitePlace‖ ≤ 1
    rwa [← sec2bP_abs, ← Real.norm_eq_abs]
  refine ⟨?_, hsub'⟩
  refine (isCompact_sLocalPWBox (F := ℚ) (S := ∅) 1).of_isClosed_subset (isClosed_tsupport _)
    (fun y hy ↦ ⟨fun w ↦ ?_, fun v ↦ absurd v.2 (Finset.notMem_empty _)⟩)
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  rw [Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  exact hsub' hy

/-- The test of the counterexample lies in the polar subspace. -/
private theorem sec2bP_polar (φ : SchwartzMap ℝ ℂ) (hφ0 : φ 0 = 0)
    (hFφ0 : (FourierTransform.fourier φ : SchwartzMap ℝ ℂ) 0 = 0)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace))) :
    sAdeleSchwartzTransition ℚ (le_refl (∅ : Finset V(ℚ))) f ∈ sAdelePolarSubspace ℚ ∅ := by
  rw [sec2bP_transition, mem_sAdelePolarSubspace, sAdeleSchwartzFourier_ratEmpty_apply φ f hf, hf]
  exact ⟨by rw [show ((0 : SAdeleRing ℚ ∅).1 Rat.infinitePlace) = 0 from rfl, map_zero, hφ0],
    by rw [show ((0 : SAdeleRing ℚ ∅).1 Rat.infinitePlace) = 0 from rfl, map_zero]; exact hFφ0⟩

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.1), pp. 487–488.
The absolute local closure presupposes that each weighted class in the §7.3.2 level is in
the ambient Sobolev space, for every real twist and every nonnegative degree.
Deviation: Express membership on representatives of all classes in the §7.3.2 level. -/
def Printed.sLocalAbsolutePWSobolev_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F))
    (hω : NormOneCharacterUnramifiedOutside
      (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))) S),
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (Λ a s : ℝ), 0 < Λ → 0 ≤ s →
      let ω := sLocalNormOneCharacter S _ hω
      ∀ f, qₛ(F, S, ω) f ∈ sLocalAbsolutePW (S := S) (T := S) le_rfl Λ
          (sAdelePolarSubspace F S) ω →
        MemLp (localTheta(F, S, a, ω, f)) 2 (localMeasure(F, S, s))

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.1), pp. 487–488.
Take F = ℚ, S = {∞, 2}, χ = 1, Λ = 1 and a = s = 0.
Let H be the inverse Fourier transform of a nonzero nonnegative even smooth bump
supported where 1/8 < |ξ| < 1/4. The test is (H(u) - H(2u)) times the 2-adic
integer indicator. Both zero moments vanish. At the class of (t, 1), the local
theta series telescopes to 2 H(t), up to the positive norm-one Haar mass.
Since H(0) > 0, its squared integral against dt/t diverges at zero. -/
theorem Printed.sLocalAbsolutePWSobolev_memLp_false :
    ¬ Printed.sLocalAbsolutePWSobolev_memLp := by
  intro h
  obtain ⟨E, hE⟩ := ratTrivialHomogeneousTheta_quotient_realEquiv
  obtain ⟨φ, hφ0, hFφ0, -, hts, c, hc, hlow⟩ := sec2bP_test
  refine sec2bP_not_memLp _ φ (E φ) (hE φ) c hc hlow
    (h ℚ 1 ∅ sec2bP_unramified sec2bP_pic 1 (-2) 0 one_pos le_rfl (E φ) ?_)
  have hb := sec2bP_inBand φ hts (E φ) (hE φ)
  rw [← sec2bP_transition (E φ)]
  refine sLocalAbsolutePW_mk_mem _ _ _ _ (E φ) ⟨hb.1, hb.2.trans fun y hy ↦
    ⟨fun w ↦ ?_, fun v ↦ absurd v.2 (Finset.notMem_empty _)⟩⟩ (sec2bP_polar φ hφ0 hFφ0 _ (hE φ))
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  rw [Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  exact hy

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), pp. 488–489.
The invariant local closure presupposes Sobolev membership of the weighted
classes in the §7.3.2 level for every real twist and every nonnegative degree.
Deviation: Express membership on representatives of all classes in the §7.3.2 level. -/
def Printed.sLocalInvariantPWSobolev_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F))
    (hω : NormOneCharacterUnramifiedOutside
      (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))) S),
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (Λ a s : ℝ), 0 < Λ → 0 ≤ s →
      let ω := sLocalNormOneCharacter S _ hω
      ∀ f, qₛ(F, S, ω) f ∈ sLocalInvariantPW (S := S) (T := S) le_rfl Λ
          (sAdelePolarSubspace F S) ω →
        MemLp (localTheta(F, S, a, ω, f)) 2 (localMeasure(F, S, s))

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), pp. 488–489.
Use ℚ, S = {∞, 2}, χ = 1, Λ = 1 and a = s = 0. The test
(H(u) - H(2u)) times the 2-adic integer indicator from the absolute-level
counterexample also lies in the invariant region. Its Fourier support satisfies
|ξ∞| ≤ 1 and |ξ₂|₂ ≤ 1. The local theta is proportional to 2 H(t) and is outside L²(dt/t). -/
theorem Printed.sLocalInvariantPWSobolev_memLp_false :
    ¬ Printed.sLocalInvariantPWSobolev_memLp := by
  intro h
  obtain ⟨E, hE⟩ := ratTrivialHomogeneousTheta_quotient_realEquiv
  obtain ⟨φ, hφ0, hFφ0, -, hts, c, hc, hlow⟩ := sec2bP_test
  refine sec2bP_not_memLp _ φ (E φ) (hE φ) c hc hlow
    (h ℚ 1 ∅ sec2bP_unramified sec2bP_pic 1 (-2) 0 one_pos le_rfl (E φ) ?_)
  have hb := sec2bP_inBand φ hts (E φ) (hE φ)
  rw [← sec2bP_transition (E φ)]
  refine sLocalInvariantPW_mk_mem _ _ _ _ (E φ) ⟨hb.1, hb.2.trans fun y hy ↦ ?_⟩
    (sec2bP_polar φ hφ0 hFφ0 _ (hE φ))
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  change (∏ w : InfinitePlace ℚ, ‖(Multiplicative.toAdd y).1 w‖ ^ w.mult) *
    (∏ v : (∅ : Finset V(ℚ)), ‖(Multiplicative.toAdd y).2 v‖) ≤ 1
  rw [Fintype.prod_unique, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  change ‖(Multiplicative.toAdd y).1 Rat.infinitePlace‖ ^ Rat.infinitePlace.mult ≤ 1
  rw [Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  exact hy

local notation "GeoIsotype(" F ", " hs ", " ω ")" =>
  actionIsotype ((hardySobolevTranslation (ideleClassTamagawaMeasure F) (m𝔽(F))
    (-(0 : ℝ)) 0 _ (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) hs).comp
    (ideleClassNorm F).ker.subtype) ω

local notation "cutoffConv(" F ", " hs ", " ω ", " a ", " hρ ", " φ ")" =>
  ((GeoIsotype(F, hs, ω)).orthogonalProjectionOnto.comp
    ((geometricTruncatedConvolution (F := F) a (le_rfl (a := (0 : ℝ))) hs hρ φ).comp
      (GeoIsotype(F, hs, ω)).subtypeL))
local notation "aboveOne(" F ", " φ ")" =>
  (tsupport (φ : BruhatCompactSupport C𝔽(F)).val ⊆ {g | 1 ≤ ((m𝔽(F) g).val : ℝ)})
local notation "productTraceClass(" T ", " P ")" =>
  (⟨(T).val * (P), mul_mem_nuclearEndomorphisms_right (P) (T)⟩ : nuclearEndomorphisms _)

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.4), p. 488.
For every fixed cutoff, the trace-norm limit of absolute condensation is asserted
to be the uncompressed cutoff geometric convolution.
Deviation: Use the global absolute projector specified by the declared codomain
in (11.2.1.3), with the Fourier box bound X = Λ. -/
def Printed.absolutePWCondensation_traceNorm_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
    letI : CompleteSpace ↥(GeoIsotype(F, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := F) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    NormOneCharacterUnramifiedOutside ω S →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (φ : BruhatCompactSupport C𝔽(F)), aboveOne(F, φ) →
      ∀ (R ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff (m𝔽(F)) R ε ρ),
        ∃ T : nuclearEndomorphisms GeoIsotype(F, hs, ω),
          T.val = cutoffConv(F, hs, ω, a, hρ, φ) ∧
            Tendsto (fun Λ ↦ traceNorm
              (productTraceClass(T, absolutePWProjection (F := F) (S := S) hs a ω Λ) - T))
              atTop (𝓝 0)

/-- A trace-norm limit of right products determines the operator value on a pointwise limit. -/
private theorem absolutePWCondensation_traceNorm_tendsto_false_apply
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) (P : ℝ → H →L[ℂ] H) (u v : H)
    (hP : Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 v))
    (hT : Tendsto (fun Λ ↦ traceNorm
      ((⟨T.val * P Λ, mul_mem_nuclearEndomorphisms_right (P Λ) T⟩ : nuclearEndomorphisms H) - T))
      atTop (𝓝 0)) : T.val v = T.val u := by
  by_cases hu : u = 0
  · subst u
    simp only [map_zero] at hP ⊢
    rw [tendsto_nhds_unique hP tendsto_const_nhds, map_zero]
  let f := innerSL ℂ u
  let A := f.smulRight u
  let D (Λ : ℝ) : nuclearEndomorphisms H :=
    ⟨T.val * P Λ, mul_mem_nuclearEndomorphisms_right (P Λ) T⟩ - T
  have hbound (Λ : ℝ) : ‖f‖ * ‖T.val (P Λ u) - T.val u‖ ≤ ‖A‖ * traceNorm (D Λ) := by
    have hmul : (D Λ).val * A = f.smulRight (T.val (P Λ u) - T.val u) := by
      ext1 x
      simp [D, A, smul_sub]
    rw [← traceNorm_smulRight f (T.val (P Λ u) - T.val u)]
    have hprod : (⟨(D Λ).val * A, mul_mem_nuclearEndomorphisms_right A (D Λ)⟩ :
        nuclearEndomorphisms H) =
        ⟨f.smulRight (T.val (P Λ u) - T.val u), smulRight_mem_nuclearEndomorphisms _ _⟩ :=
      Subtype.ext hmul
    rw [← hprod]
    exact traceNorm_mul_right_le A (D Λ)
  have hLeft : Tendsto (fun Λ ↦ ‖f‖ * ‖T.val (P Λ u) - T.val u‖) atTop
      (𝓝 (‖f‖ * ‖T.val v - T.val u‖)) :=
    tendsto_const_nhds.mul (((T.val.continuous.tendsto v).comp hP).sub tendsto_const_nhds).norm
  have hRight : Tendsto (fun Λ ↦ ‖A‖ * traceNorm (D Λ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hT
  have hle := le_of_tendsto_of_tendsto' hLeft hRight hbound
  have hf : 0 < ‖f‖ := by simpa only [f, innerSL_apply_norm, norm_pos_iff] using hu
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (nonpos_of_mul_nonpos_right hle hf) (norm_nonneg _)))

open scoped nonZeroDivisors in
/-- The rational integers have trivial Picard group. -/
private theorem rational_empty_picTrivial :
    Subsingleton (CommRing.Pic (((∅ : Finset V(ℚ)) : Set V(ℚ)).integer ℚ)) := by
  rw [Finset.coe_empty, integer_empty]
  let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
  let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
  let := IsPrincipalIdealRing.of_surjective i i.surjective
  infer_instance

/-- The restriction of the trivial rational character is unramified everywhere. -/
private theorem rational_one_unramifiedOutside_empty :
    NormOneCharacterUnramifiedOutside
      ((1 : PontryaginDual C𝔽(ℚ)).comp
        (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))) ∅ := by
  refine ⟨⟨1, (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩

/-- Expanding smooth cutoffs preserve the nonzero image of a vector under a continuous map. -/
private theorem rational_cutoffConv_cutoff_image_ne_zero
    {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [TopologicalSpace E] [T1Space E] [Zero E]
    (m : G →ₜ* ℝ≥0ˣ) (ν : Measure G) (Q : Lp ℂ 2 ν → E) (hQ : Continuous Q)
    (y : Lp ℂ 2 ν) (hy : Q y ≠ 0) :
    ∃ (R ε : ℝ) (ρ : G → ℝ) (hρ : IsModulatedCutoff m R ε ρ),
      Q (modulatedCutoffOperator m ν hρ y) ≠ 0 := by
  classical
  let ε (R : ℝ) := R⁻¹ ^ 2
  have hcut (R : ℝ) (hR : 3 ≤ R) : ∃ ρ : G → ℝ, IsModulatedCutoff m R (ε R) ρ := by
    have hRpos : 0 < R := by positivity
    have hi : 0 < R⁻¹ := inv_pos.mpr hRpos
    have hie : R⁻¹ ≤ 1 / 3 := by
      simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 3) hR
    have he : 0 < ε R := by dsimp [ε]; positivity
    have he' : ε R ≤ R⁻¹ / 3 := by
      dsimp [ε]
      nlinarith [mul_nonneg hi.le (sub_nonneg.mpr hie)]
    have hRight : 1 < R - ε R := by linarith
    have hRightpos : 0 < R - ε R := by linarith
    have hInv : (R - ε R)⁻¹ ≤ R⁻¹ + ε R := by
      rw [← one_div]
      apply (div_le_iff₀ hRightpos).2
      have hRI : R⁻¹ * R = 1 := inv_mul_cancel₀ hRpos.ne'
      have hDifference : 0 ≤ ε R * ((R - ε R) - R⁻¹) :=
        mul_nonneg he.le (by linarith)
      nlinarith only [hDifference, hRI]
    let B : ContDiffBump (0 : ℝ) :=
      ⟨Real.log (R - ε R), Real.log R, Real.log_pos hRight,
        Real.log_lt_log hRightpos (sub_lt_self R he)⟩
    let r (x : G) : ℝ := (m x).val
    have hr : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
    have hpos (x : G) : 0 < r x := NNReal.coe_pos.mpr (Units.zero_lt _)
    let ρ (x : G) := B (Real.log (r x))
    have h1 : ρ 1 = 1 := by
      apply B.one_of_mem_closedBall
      simp [r, B.rIn_pos.le]
    refine ⟨ρ, hRpos, he, by linarith, by linarith,
      fun _ ↦ B.nonneg, fun x ↦ (abs_of_nonneg (B.nonneg (x := Real.log (r x)))) ▸ B.le_one,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact IsGreatest.csSup_eq ⟨⟨1, h1⟩, forall_mem_range.mpr fun _ ↦ B.le_one⟩
    · refine ⟨fun t ↦ B (Real.log t), ∅, fun _ ↦ rfl, by simp, ?_, by simp⟩
      simp only [Finset.coe_empty, sdiff_empty]
      exact B.contDiff.comp_contDiffOn
        (fun x hx ↦ (Real.contDiffAt_log.mpr (mem_Ioi.mp hx).ne').contDiffWithinAt)
    · intro x
      change B (Real.log ((m x).val : ℝ)) = B (Real.log ((m x⁻¹).val : ℝ))
      rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv, B.neg]
    · apply closure_minimal _ (isClosed_Icc.preimage hr)
      intro x hx
      have hmem : Real.log (r x) ∈ support B := hx
      rw [B.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
      obtain ⟨hl, hu⟩ := abs_lt.mp hmem
      change R⁻¹ ≤ r x ∧ r x ≤ R
      rw [← Real.log_le_log_iff hi (hpos x), Real.log_inv,
        ← Real.log_le_log_iff (hpos x) hRpos]
      exact ⟨hl.le, hu.le⟩
    · intro x hx
      apply B.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
      change -Real.log (R - ε R) ≤ _ ∧ _ ≤ Real.log (R - ε R)
      rw [← Real.log_inv, Real.log_le_log_iff (inv_pos.mpr hRightpos) (hpos x),
        Real.log_le_log_iff (hpos x) hRightpos]
      change R⁻¹ + ε R ≤ r x ∧ r x ≤ R - ε R at hx
      exact ⟨hInv.trans hx.1, hx.2⟩
  let ρ (R : ℝ) : G → ℝ := if h : 3 ≤ R then (hcut R h).choose else 1
  have hρ : ∀ᶠ R in atTop, IsModulatedCutoff m R (ε R) (ρ R) := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with R hR
    simpa only [ρ, dite_eq_left hR] using (hcut R hR).choose_spec
  let σ (R : ℝ) : G → ℝ := if IsModulatedCutoff m R (ε R) (ρ R) then ρ R else 1
  let P (R : ℝ) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
    if h : IsModulatedCutoff m R (ε R) (ρ R) then modulatedCutoffOperator m ν h else 1
  have hσ (R : ℝ) : Measurable (σ R) := by
    dsimp only [σ]
    split_ifs with h
    · exact h.measurable
    · exact measurable_const
  have hσbound (R : ℝ) (x : G) : |σ R x| ≤ 1 := by
    dsimp only [σ]
    split_ifs with h
    · exact h.abs_le_one x
    · simp
  have hP (R : ℝ) : (P R y : G → ℂ) =ᵐ[ν] fun x ↦ (σ R x : ℂ) * y x := by
    dsimp only [P, σ]
    split_ifs with h
    · exact modulatedCutoffOperator_apply m ν h y
    · simp
  have hinv : Tendsto (fun R : ℝ ↦ R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have heps : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hinv.pow 2
  have hl : Tendsto (fun R : ℝ ↦ R⁻¹ + ε R) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.add heps
  have hright : Tendsto (fun R : ℝ ↦ R - ε R) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [heps.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      eventually_ge_atTop (b + 1)] with R he hR
    linarith
  have hpoint (x : G) : ∀ᶠ R in atTop, σ R x = 1 := by
    have hx : 0 < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    filter_upwards [hρ, hl.eventually (gt_mem_nhds hx), hright.eventually_ge_atTop ((m x).val : ℝ)]
      with R hR hleft hright
    simpa only [σ, ite_eq_left hR, Pi.one_apply] using hR.eq_one ⟨hleft.le, hright⟩
  let d (R : ℝ) (x : G) : ℂ := (σ R x : ℂ) * y x - y x
  have hd (R : ℝ) : AEStronglyMeasurable (d R) ν :=
    (((Complex.measurable_ofReal.comp (hσ R)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable y)).sub (Lp.aestronglyMeasurable y))
  have hbound (R : ℝ) (x : G) : ‖d R x‖ ^ 2 ≤ 4 * ‖y x‖ ^ 2 := by
    have h : ‖d R x‖ ≤ 2 * ‖y x‖ := calc
      ‖d R x‖ ≤ ‖(σ R x : ℂ) * y x‖ + ‖y x‖ := norm_sub_le _ _
      _ = |σ R x| * ‖y x‖ + ‖y x‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := by nlinarith [hσbound R x, norm_nonneg (y x)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ 2 * ‖y x‖ + ‖d R x‖ by positivity)]
  have hint : Integrable (fun x ↦ 4 * ‖y x‖ ^ 2) ν :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable y)).mp (Lp.memLp y)).const_mul 4
  have hconv : Tendsto (fun R ↦ ∫ x, ‖d R x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (l := (atTop : Filter ℝ))
      (F := fun R x ↦ ‖d R x‖ ^ 2) (f := fun _ : G ↦ (0 : ℝ)) (fun x ↦ 4 * ‖y x‖ ^ 2)
      (.of_forall fun R ↦ (hd R).norm.pow 2) (.of_forall fun R ↦ .of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hbound R x) hint
      (.of_forall fun x ↦ tendsto_const_nhds.congr' ((hpoint x).mono fun R hR ↦ by simp [d, hR]))
    simpa using h
  have heq (R : ℝ) : ‖P R y - y‖ ^ 2 = ∫ x, ‖d R x‖ ^ 2 ∂ν := by
    let v := P R y - y
    have hv : ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂ν := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def, ← integral_re]
      · exact integral_congr_ae (.of_forall fun x ↦ (norm_sq_eq_re_inner (𝕜 := ℂ) (v x)).symm)
      · exact L2.integrable_inner v v
    rw [hv]
    apply integral_congr_ae
    filter_upwards [hP R, Lp.coeFn_sub (P R y) y] with x hx hsub
    rw [show v x = P R y x - y x from hsub, hx]
  have hP_lim : Tendsto (fun R ↦ P R y) atTop (𝓝 y) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hsq : Tendsto (fun R ↦ ‖P R y - y‖ ^ 2) atTop (𝓝 0) := by
      simpa only [heq] using hconv
    simpa using hsq.sqrt
  have hlim : Tendsto (fun R ↦ Q (P R y)) atTop (𝓝 (Q y)) := (hQ.tendsto (x := y)).comp hP_lim
  have hne : ∀ᶠ R in atTop, Q (P R y) ≠ 0 := hlim.eventually (isOpen_ne.mem_nhds hy)
  obtain ⟨R, hR, hneR⟩ := (hρ.and hne).exists
  exact ⟨R, ε R, ρ R, hR, by simpa only [P, dite_eq_left hR] using hneR⟩

/-- A smooth function of the logarithmic module is Bruhat smooth. On each
structural quotient, compose the descended positive quasi-character with log. -/
private theorem rational_cutoffConv_bruhatSmooth_logProfile
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (m : G →ₜ* ℝ≥0ˣ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f) :
    IsBruhatSmooth (fun x ↦ (f (Real.log ((m x).val : ℝ)) : ℂ)) := by
  let χ : QuasiCharacter G :=
    { toFun := fun x ↦ ((m x).val : ℝ)
      map_one' := by simp
      map_mul' := fun x y ↦ by simp
      continuous_toFun := Complex.continuous_ofReal.comp
        (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)) }
  intro p
  obtain ⟨k, hk, hinv, hdesc⟩ :=
    (mem_bruhatSmoothSubmodule_iff _).1 (quasiCharacter_mem_bruhatSmooth χ) p
  refine ⟨k, hk, fun h x ↦ congrArg (fun z : ℂ ↦ (f (Real.log z.re) : ℂ)) (hinv h x), ?_⟩
  intro a ha
  obtain ⟨q, hq, hdiff⟩ := hdesc a ha
  have hpos (y : a.quotient) : 0 < (q y).re := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hq]
    exact NNReal.coe_pos.mpr (Units.zero_lt _)
  refine ⟨fun y ↦ (f (Real.log (q y).re) : ℂ),
    fun x ↦ congrArg (fun z : ℂ ↦ (f (Real.log z.re) : ℂ)) (hq x), ?_⟩
  intro e z b
  exact Complex.ofRealCLM.contDiff.comp ((hf.of_le (by simp)).comp
    ((Complex.reCLM.contDiff.comp (hdiff e z b)).log fun x ↦ (hpos _).ne'))

/-- A nonzero projected translate at norm greater than one survives averaging by a
smooth compactly supported function of the log norm. -/
private theorem rational_cutoffConv_positive_test
    {G E H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsProperMap m) (j : ℝ≥0ˣ → G)
    (hj : Continuous j) (hj' : RightInverse j m) (μ : Measure G) [μ.IsHaarMeasure]
    (τ : G →* (E →L[ℂ] E)) (hτ : Continuous (fun p : G × E ↦ τ p.1 p.2))
    (Q : E →L[ℂ] H) (u : E) (hu : ∀ k : m.toMonoidHom.ker, τ k.val u = u)
    (g₀ : G) (hg₀ : 1 < ((m g₀).val : ℝ)) (hne : Q (τ g₀ u) ≠ 0) :
    ∃ φ : BruhatCompactSupport G, tsupport φ.val ⊆ {g | 1 ≤ ((m g).val : ℝ)} ∧
      Q (bruhatRegularizedAction μ τ hτ φ u) ≠ 0 := by
  have hfiber (g : G) : τ g u = τ (j (m g)) u := by
    let t := j (m g)
    let k : m.toMonoidHom.ker := ⟨g / t, by
      change m (g / t) = 1
      rw [map_div, show m t = m g from hj' (m g), div_self']⟩
    have ht : t * k.val = g := by
      rw [mul_comm t k.val]
      exact div_mul_cancel g t
    calc
      τ g u = τ (t * k.val) u := congrArg (fun x ↦ τ x u) ht.symm
      _ = τ t (τ k.val u) := congrArg (fun A : E →L[ℂ] E ↦ A u) (τ.map_mul t k.val)
      _ = τ t u := congrArg (τ t) (hu k)
  let l : ℝ≥0ˣ ≃ₜ ℝ := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have hl (t : ℝ≥0ˣ) : l t = Real.log (t.val : ℝ) :=
    (Real.log_of_pos (NNReal.coe_pos.mpr t.zero_lt)).symm
  let x₀ := l (m g₀)
  have hx₀ : 0 < x₀ := by
    rw [show x₀ = Real.log ((m g₀).val : ℝ) from hl _]
    exact Real.log_pos hg₀
  let ζ := Q (τ g₀ u)
  let δ : E →L[ℂ] ℂ := (innerSL ℂ ζ).comp Q
  let c (x : ℝ) : ℝ := (δ (τ (j (l.symm x)) u)).re
  have horbit : Continuous (fun g ↦ τ g u) := hτ.comp (continuous_id.prodMk continuous_const)
  have hc : Continuous c := Complex.continuous_re.comp
    (δ.continuous.comp (horbit.comp (hj.comp l.symm.continuous)))
  have hcenter : 0 < c x₀ := by
    change 0 < (δ (τ (j (l.symm (l (m g₀)))) u)).re
    rw [l.symm_apply_apply, ← hfiber g₀]
    change 0 < (innerSL ℂ ζ ζ).re
    rw [innerSL_apply_apply]
    change 0 < RCLike.re (inner ℂ ζ ζ)
    rw [← norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hne)
  have hnhds : {x | 0 < c x} ∩ Ioi 0 ∈ 𝓝 x₀ :=
    ((isOpen_lt continuous_const hc).inter isOpen_Ioi).mem_nhds ⟨hcenter, hx₀⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let b : ContDiffBump x₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let f (g : G) : ℂ := (b (l (m g)) : ℂ)
  have hzero (g : G) (hg : l (m g) ∉ Metric.closedBall x₀ (r / 2)) : f g = 0 := by
    change (b (l (m g)) : ℂ) = 0
    rw [image_eq_zero_of_notMem_tsupport (f := (b : ℝ → ℝ)) (by simpa only [b.tsupport_eq] using hg), Complex.ofReal_zero]
  have hcomp : HasCompactSupport f :=
    HasCompactSupport.intro ((l.isProperMap.comp hm).isCompact_preimage (isCompact_closedBall x₀ (r / 2))) hzero
  have hbs : IsBruhatSmooth f := by
    simpa only [f, hl] using rational_cutoffConv_bruhatSmooth_logProfile m b.contDiff
  let φ : BruhatCompactSupport G := ⟨f, (mem_bruhatSmoothSubmodule_iff _).mpr hbs, hcomp⟩
  have hsupport : tsupport f ⊆ (l ∘ m) ⁻¹' Metric.closedBall x₀ (r / 2) :=
    closure_minimal (fun g hg ↦ by
      by_contra hn
      exact hg (hzero g hn)) (Metric.isClosed_closedBall.preimage (l.continuous.comp hm.continuous))
  refine ⟨φ, fun g hg ↦ ?_, ?_⟩
  · have hg' := (hball (Metric.closedBall_subset_ball (by linarith) (hsupport hg))).2
    change 0 < l (m g) at hg'
    rw [hl] at hg'
    exact (Real.log_pos_iff (NNReal.coe_nonneg _)).mp hg' |>.le
  · let k (g : G) : ℂ := f g * δ (τ g u)
    have hk : Continuous k := (continuous_of_bruhatSmooth hbs).mul (δ.continuous.comp horbit)
    have hkc : HasCompactSupport k := hcomp.mul_right
    have hreal (g : G) : (k g).re = b (l (m g)) * c (l (m g)) := by
      change ((b (l (m g)) : ℂ) * δ (τ g u)).re = _
      rw [Complex.re_ofReal_mul, hfiber g]
      simp only [c, l.symm_apply_apply]
    have hnonneg : 0 ≤ fun g ↦ (k g).re := by
      intro g
      change 0 ≤ (k g).re
      rw [hreal]
      by_cases hb : b (l (m g)) = 0
      · simp [hb]
      · have hb' : l (m g) ∈ Metric.ball x₀ (r / 2) := by
          rw [← b.support_eq]
          exact hb
        exact mul_nonneg b.nonneg (hball (Metric.ball_subset_ball (by linarith) hb')).1.le
    have hval : (k g₀).re ≠ 0 := by
      rw [hreal]
      change b x₀ * c x₀ ≠ 0
      rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), one_mul]
      exact hcenter.ne'
    have hpos : 0 < ∫ g, (k g).re ∂μ :=
      (Complex.continuous_re.comp hk).integral_pos_of_hasCompactSupport_nonneg_ne_zero
        (hkc.comp_left Complex.zero_re) hnonneg hval
    have hIntegral : δ (bruhatRegularizedAction μ τ hτ φ u) = ∫ g, k g ∂μ := by
      have h := bruhatRegularizedAction_apply μ τ hτ φ u
      refine (congrArg (fun z : PettisWeakCompletion E ↦
        (show Module.Dual ℂ (StrongDual ℂ E) from z) δ) h.2).trans ?_
      exact integral_congr_ae (.of_forall fun g ↦ δ.map_smul (f g) (τ g u))
    intro heq
    have hδ : δ (bruhatRegularizedAction μ τ hτ φ u) = 0 := by
      change (innerSL ℂ ζ) (Q (bruhatRegularizedAction μ τ hτ φ u)) = 0
      rw [heq, map_zero]
    have hIreal : (∫ g, (k g).re ∂μ) = (∫ g, k g ∂μ).re :=
      integral_re (𝕜 := ℂ) (hk.integrable_of_hasCompactSupport hkc)
    rw [hIreal, ← hIntegral, hδ, Complex.zero_re] at hpos
    exact (lt_irrefl 0) hpos

/-- The action on the trivial isotype fixes vectors along the restricted subgroup. -/
private theorem rational_cutoffConv_fixed
    {G L E : Type*} [Monoid G] [Monoid L] [TopologicalSpace L]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (τ : G →* (E →L[ℂ] E)) (i : L →* G) (ω : PontryaginDual L)
    (hω : ∀ k, (ω k : ℂ) = 1) (u : actionIsotype (τ.comp i) ω) (k : L) :
    τ (i k) u.val = u.val := by
  have h := (mem_actionIsotype (τ.comp i) ω u.val).mp u.property k
  change τ (i k) u.val = (ω k : ℂ) • u.val at h
  rw [hω k, one_smul] at h
  exact h

/-- Bruhat averaging and then cutoff multiplication preserve some nonzero
projected orbit value when the orbit is fixed by the norm-one subgroup. -/
private theorem rational_cutoffConv_of_projected_translate
    {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsProperMap m) (j : ℝ≥0ˣ → G)
    (hj : Continuous j) (hj' : RightInverse j m) (μ ν : Measure G) [μ.IsHaarMeasure]
    (τ : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν))
    (hτ : Continuous (fun p : G × Lp ℂ 2 ν ↦ τ p.1 p.2))
    (P : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (O : Lp ℂ 2 ν →L[ℂ] H) (u : Lp ℂ 2 ν)
    (hu : ∀ k : m.toMonoidHom.ker, τ k.val u = u) (g : G)
    (hg : 1 < ((m g).val : ℝ)) (hne : O (P (τ g u)) ≠ 0) :
    ∃ (φ : BruhatCompactSupport G), tsupport φ.val ⊆ {g | 1 ≤ ((m g).val : ℝ)} ∧
      ∃ (R ε : ℝ) (ρ : G → ℝ) (hρ : IsModulatedCutoff m R ε ρ),
        O (modulatedCutoffOperator m ν hρ (P (bruhatRegularizedAction μ τ hτ φ u))) ≠ 0 := by
  obtain ⟨φ, hφ, htest⟩ := rational_cutoffConv_positive_test m hm j hj hj' μ τ hτ (O.comp P) u hu g hg hne
  obtain ⟨R, ε, ρ, hρ, hcut⟩ := rational_cutoffConv_cutoff_image_ne_zero m ν O O.continuous
    (P (bruhatRegularizedAction μ τ hτ φ u)) htest
  exact ⟨φ, hφ, R, ε, ρ, hρ, hcut⟩

/-- A theta-orthogonal vector in the rational trivial isotype has a translate with
nonzero geometric projection at some norm greater than one. At an ordinate γ of a
critical-line zero, use the Riesz vector `exp(-iγx)/(1+x²)` in log norm. Mellin
factorization gives its orthogonality. The pairing with a nonzero radial theta
profile is a Cauchy convolution with a nowhere-zero Fourier multiplier. Its
nonvanishing somewhere, together with inversion and the conjugate zero, gives
a positive translation. -/
private theorem rational_cutoffConv_positive_translate (hs : (0 : ℝ) ≤ 2)
    (ω : PontryaginDual C₁(ℚ))
    (_hω : ω = (1 : PontryaginDual C𝔽(ℚ)).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))) :
    let K := GeoIsotype(ℚ, hs, ω)
    letI : CompleteSpace ↥K :=
      (instClosedSpectralIsotypeSec2 (F := ℚ) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    let τ := hardySobolevTranslation (ideleClassTamagawaMeasure ℚ) (m𝔽(ℚ))
      (-(0 : ℝ)) 0 2 (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) hs
    let P := geometricProjection (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs
    ∃ (u : K) (g : C𝔽(ℚ)), 1 < ((m𝔽(ℚ) g).val : ℝ) ∧
      K.orthogonalProjectionOnto (P u.val) = 0 ∧
      K.orthogonalProjectionOnto (P (τ g u.val)) ≠ 0 := by sorry

/-- A fixed-cutoff geometric convolution is nonzero on a vector orthogonal to theta
in the trivial rational isotype. Use a critical-line ordinate γ and the log-norm
vector `exp(-iγx)/(1+x²)`. Pair its translates with the theta vector from
`(3u² - 2πu⁴) exp(-πu²)` and the finite integer indicators. The pairing is analytic,
and the Cauchy kernel has a nonvanishing Fourier multiplier, so it is nonzero at some
positive translation. A bump near that point and a large cutoff preserve the
nonzero geometric output. -/
private theorem rational_cutoffConv_ne_zero_of_geometricProjection_eq_zero :
    let hs : (0 : ℝ) ≤ 2 := by norm_num
    let ω := (1 : PontryaginDual C𝔽(ℚ)).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))
    letI : CompleteSpace ↥(GeoIsotype(ℚ, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := ℚ) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    ∃ (φ : BruhatCompactSupport C𝔽(ℚ)), aboveOne(ℚ, φ) ∧
      ∃ (R ε : ℝ) (ρ : C𝔽(ℚ) → ℝ) (hρ : IsModulatedCutoff (m𝔽(ℚ)) R ε ρ)
          (u : GeoIsotype(ℚ, hs, ω)),
        ((GeoIsotype(ℚ, hs, ω)).orthogonalProjectionOnto.comp
          ((geometricProjection (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs).comp
            (GeoIsotype(ℚ, hs, ω)).subtypeL)) u = 0 ∧
        ((GeoIsotype(ℚ, hs, ω)).orthogonalProjectionOnto.comp
          ((geometricTruncatedConvolution (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs hρ φ).comp
            (GeoIsotype(ℚ, hs, ω)).subtypeL)) u ≠ 0 := by
  intro hs ω
  let K := GeoIsotype(ℚ, hs, ω)
  let : CompleteSpace ↥K :=
    (instClosedSpectralIsotypeSec2 (F := ℚ) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
      hs ω).completeSpace_coe
  let μ := ideleClassTamagawaMeasure ℚ
  let τ := hardySobolevTranslation μ (m𝔽(ℚ)) (-(0 : ℝ)) 0 2
    (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) hs
  let ν := μ.withDensity fun g ↦ ENNReal.ofReal
    (intervalSobolevDensity (-(0 : ℝ)) 0 2 (Real.log (((m𝔽(ℚ)) g).val : ℝ)))
  let W := Lp ℂ 2 ν
  let P : W →L[ℂ] W := geometricProjection (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs
  let O : W →L[ℂ] K := K.orthogonalProjectionOnto
  let j : ℝ≥0ˣ → C𝔽(ℚ) := (QuotientGroup.mk' _).comp ratIdeleNormSection
  have hj : Continuous j := QuotientGroup.continuous_mk.comp ratIdeleNormSection_continuous
  have witness : ∃ (u : ↥K) (g : C𝔽(ℚ)), 1 < ((m𝔽(ℚ) g).val : ℝ) ∧
      O (P u.val) = 0 ∧ O (P (τ g u.val)) ≠ 0 := rational_cutoffConv_positive_translate hs ω rfl
  obtain ⟨u, g, hg, hPu, hPg⟩ := witness
  have hτ : Continuous (fun p : C𝔽(ℚ) × W ↦ τ p.1 p.2) :=
    (exists_hardySobolevTranslation μ (m𝔽(ℚ)) (-(0 : ℝ)) 0 2
      (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) hs).choose_spec.2
  have hu (k : C₁(ℚ)) : τ k.val u.val = u.val :=
    rational_cutoffConv_fixed (G := C𝔽(ℚ)) (L := C₁(ℚ)) (E := W)
      τ (ideleClassNorm ℚ).ker.subtype ω (fun _ ↦ rfl) u k
  have hcut := rational_cutoffConv_of_projected_translate (G := C𝔽(ℚ)) (H := ↥K)
    (m𝔽(ℚ)) (isProperMap_ideleClassNorm ℚ) j hj ratIdeleNormSection_class_rightInverse
    μ ν τ hτ P O u.val hu g hg hPg
  obtain ⟨φ, hφ, R, ε, ρ, hρ, hρne⟩ := hcut
  exact ⟨φ, hφ, R, ε, ρ, hρ, u, hPu, hρne⟩

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.4), p. 488.
On the trivial rational component with no finite places, a = 1/2 and s = 2, let γ be
the first positive ordinate of a critical-line zeta zero. The vector
v(x) = exp(-iγx)/(1+x²) is orthogonal to theta by the Mellin zero.
Use the nonzero half-weighted theta profile G of
(3u² - 2πu⁴) exp(-πu²) with integer indicators at finite places.
The inner products of the translates v(x-t) with G cannot vanish for all t > 0.
Up to a phase they convolve G(x) exp(iγx)(1+x²) with 1/(1+x²).
That convolution is real analytic and its Fourier multiplier is nowhere zero.
A nonnegative test bump near a positive t with nonzero inner product still pairs
nontrivially, and a sufficiently large fixed symmetric cutoff preserves a nonzero
part of its geometric projection. Every right PW projection kills v. -/
theorem Printed.absolutePWCondensation_traceNorm_tendsto_false :
    ¬ Printed.absolutePWCondensation_traceNorm_tendsto := by
  intro h
  have hs : (0 : ℝ) ≤ 2 := by norm_num
  let ω := (1 : PontryaginDual C𝔽(ℚ)).comp
    (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))
  let H := ↥(GeoIsotype(ℚ, hs, ω))
  let : CompleteSpace H :=
    (instClosedSpectralIsotypeSec2 (F := ℚ) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
      hs ω).completeSpace_coe
  let P (Λ : ℝ) : H →L[ℂ] H := absolutePWProjection (F := ℚ) (S := ∅) hs (1 / 2) ω Λ
  obtain ⟨φ, hφ, R, ε, ρ, hρ, u, hu, hcut⟩ :=
    rational_cutoffConv_ne_zero_of_geometricProjection_eq_zero
  obtain ⟨T, hT, hlim⟩ := h ℚ 1 ∅ (1 / 2) 2 hs
    rational_one_unramifiedOutside_empty rational_empty_picTrivial φ hφ R ε ρ hρ
  have hstrong := absolutePWProjection_tendsto (F := ℚ) (S := ∅) hs (1 / 2) ω
    rational_one_unramifiedOutside_empty rational_empty_picTrivial u
  have hzero : Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 0) :=
    (congrArg (fun v : H ↦ Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 v)) hu).mp hstrong
  have heq : T.val 0 = T.val u :=
    absolutePWCondensation_traceNorm_tendsto_false_apply H T P u 0 hzero hlim
  exact hcut ((congrArg (fun A : H →L[ℂ] H ↦ A u) hT).symm.trans
    (heq.symm.trans (map_zero T.val)))

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.9), p. 489.
For every fixed cutoff, the trace-norm limit of invariant condensation is asserted
to be the uncompressed cutoff geometric convolution. -/
def Printed.invariantPWCondensation_traceNorm_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
    letI : CompleteSpace ↥(GeoIsotype(F, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := F) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    NormOneCharacterUnramifiedOutside ω S →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (φ : BruhatCompactSupport C𝔽(F)), aboveOne(F, φ) →
      ∀ (R ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff (m𝔽(F)) R ε ρ),
        ∃ T : nuclearEndomorphisms GeoIsotype(F, hs, ω),
          T.val = cutoffConv(F, hs, ω, a, hρ, φ) ∧
            Tendsto (fun Λ ↦ traceNorm
              (productTraceClass(T, invariantPWProjection (F := F) (S := S) hs a ω Λ) - T))
              atTop (𝓝 0)

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.9), p. 489.
For ℚ with no finite places, the trivial character, a = 1/2 and s = 2, the product
region is the same interval as the absolute box. The zeta-zero vector, positive test bump and
fixed symmetric cutoff of the absolute counterexample also refute this limit. -/
theorem Printed.invariantPWCondensation_traceNorm_tendsto_false :
    ¬ Printed.invariantPWCondensation_traceNorm_tendsto := by
  intro h
  have hs : (0 : ℝ) ≤ 2 := by norm_num
  let ω := (1 : PontryaginDual C𝔽(ℚ)).comp
    (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))
  let H := ↥(GeoIsotype(ℚ, hs, ω))
  let : CompleteSpace H :=
    (instClosedSpectralIsotypeSec2 (F := ℚ) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
      hs ω).completeSpace_coe
  let P (Λ : ℝ) : H →L[ℂ] H := invariantPWProjection (F := ℚ) (S := ∅) hs (1 / 2) ω Λ
  obtain ⟨φ, hφ, R, ε, ρ, hρ, u, hu, hcut⟩ :=
    rational_cutoffConv_ne_zero_of_geometricProjection_eq_zero
  obtain ⟨T, hT, hlim⟩ := h ℚ 1 ∅ (1 / 2) 2 hs
    rational_one_unramifiedOutside_empty rational_empty_picTrivial φ hφ R ε ρ hρ
  have hstrong := invariantPWProjection_tendsto (F := ℚ) (S := ∅) hs (1 / 2) ω
    rational_one_unramifiedOutside_empty rational_empty_picTrivial u
  have hzero : Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 0) :=
    (congrArg (fun v : H ↦ Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 v)) hu).mp hstrong
  have heq : T.val 0 = T.val u :=
    absolutePWCondensation_traceNorm_tendsto_false_apply H T P u 0 hzero hlim
  exact hcut ((congrArg (fun A : H →L[ℂ] H ↦ A u) hT).symm.trans
    (heq.symm.trans (map_zero T.val)))

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.5), p. 488.
The traces at fixed cutoff are asserted to converge to the trace of the
uncompressed cutoff geometric convolution.
Deviation: Interpret the absolute projector by the PW codomain of (11.2.1.3)
and take the box parameter X = Λ, as for the operator assertion. -/
def Printed.absolutePWCondensation_trace_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
    letI : CompleteSpace ↥(GeoIsotype(F, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := F) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    NormOneCharacterUnramifiedOutside ω S →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (φ : BruhatCompactSupport C𝔽(F)), aboveOne(F, φ) →
      ∀ (R ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff (m𝔽(F)) R ε ρ),
        ∃ T : nuclearEndomorphisms GeoIsotype(F, hs, ω),
          T.val = cutoffConv(F, hs, ω, a, hρ, φ) ∧
            Tendsto (fun Λ ↦ hilbertTrace
              (productTraceClass(T, absolutePWProjection (F := F) (S := S) hs a ω Λ)))
              atTop (𝓝 (hilbertTrace T))

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.5), p. 488.
In the rational trivial isotype take S = {∞}, a = 1/2 and s = 2.
In Fourier H¹ let E project onto the complement of the functions vanishing
at the critical-line ordinates. A smooth frequency multiplier supported
around a single ordinate γ and equal to one there induces a rank-one
idempotent in the quotient. A fixed large symmetric cutoff leaves its trace
near one. Translate the inverse transform far to the right, compensate by
the phase at γ and cut the Schwartz tails to obtain a positive-time test.
The spatially cut translated operator on E tends to zero in trace norm,
while its quotient action retains the rank-one trace. The two fixed-cutoff
traces thus differ. See the rational calculation in the PR review. -/
theorem Printed.absolutePWCondensation_trace_tendsto_false :
    ¬ Printed.absolutePWCondensation_trace_tendsto := by sorry

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.10), p. 489.
The traces at fixed cutoff are asserted to converge to the trace of the
uncompressed cutoff geometric convolution. -/
def Printed.invariantPWCondensation_trace_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
    letI : CompleteSpace ↥(GeoIsotype(F, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := F) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    NormOneCharacterUnramifiedOutside ω S →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (φ : BruhatCompactSupport C𝔽(F)), aboveOne(F, φ) →
      ∀ (R ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff (m𝔽(F)) R ε ρ),
        ∃ T : nuclearEndomorphisms GeoIsotype(F, hs, ω),
          T.val = cutoffConv(F, hs, ω, a, hρ, φ) ∧
            Tendsto (fun Λ ↦ hilbertTrace
              (productTraceClass(T, invariantPWProjection (F := F) (S := S) hs a ω Λ)))
              atTop (𝓝 (hilbertTrace T))

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.10), p. 489.
For the rational data of the absolute scalar counterexample the
only place in S is real. The product region equals the box at every level,
so both scalar limits have the same discrepancy. -/
theorem Printed.invariantPWCondensation_trace_tendsto_false :
    ¬ Printed.invariantPWCondensation_trace_tendsto := by sorry

local notation "theta0(" F ", " hs ")" => globalThetaSobolev F 0 (le_rfl (a := (0 : ℝ))) hs
local notation "Sₚ(" F ", " p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset

/-- Paper: Paragraph before (11.2.2.1), p. 489.
The raw principal-value range defining the prime quotient is asserted to be
closed in the zero-line theta isotype.
Deviation: Use the equivalent ambient isotypic model at zero twist. -/
def Printed.primeOrbitalSobolevDenominator_closed : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (p : HeightOneSpectrum (𝓞 ℚ)),
    (∀ v ∈ Sₚ(F, p), (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    ∀ (s : ℝ) (hs : 0 ≤ s),
      let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
      IsClosed {x : Wω(F, hs, ω) | ∃ y : theta0(F, hs), y.val ∈ Wω(F, hs, ω) ∧
        (globalThetaSobolevPrincipalValue F (Sₚ(F, p)) 0 hs y).val = x.val}

private theorem rat_placesAbove_eq_singleton (p : V(ℚ)) :
    (finite_nuclearityPlacesAbove (F := ℚ) p).toFinset = {p} := by
  classical
  ext v
  simp only [Set.Finite.mem_toFinset, mem_ofPred_eq, Finset.mem_singleton]
  rfl

/-- A closed range on a closed submodule gives a lower bound for an injective operator. -/
private theorem norm_le_mul_of_closed_isotype_range {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [CompleteSpace W] (E H : Submodule ℂ W) (P : H →L[ℂ] H)
    [CompleteSpace H] (hcE : IsClosed (E : Set W)) (hinj : Injective P)
    (hPres : ∀ y : H, y.val ∈ E → (P y).val ∈ E)
    (hclosed : IsClosed {x : E | ∃ y : H, y.val ∈ E ∧ (P y).val = x.val}) :
    ∃ K : ℝ≥0, ∀ z : H, z.val ∈ E → ‖z‖ ≤ (K : ℝ) * ‖P z‖ := by
  let D := E.comap H.subtype
  have hD : IsClosed (D : Set H) := hcE.preimage continuous_subtype_val
  let : CompleteSpace D := hD.completeSpace_coe
  let A := H.subtypeL.comp (P.comp D.subtypeL)
  have hA : range A = Subtype.val '' {x : E | ∃ y : H, y.val ∈ E ∧ (P y).val = x.val} := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨⟨(P z.val).val, hPres z.val z.property⟩, ⟨z.val, z.property, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨y, hy, hEq⟩, rfl⟩
      exact ⟨⟨y, hy⟩, hEq⟩
  have hA_closed : IsClosed (range A) := by
    rw [hA]
    exact hcE.isClosedMap_subtype_val _ hclosed
  have hA_inj : Injective A := Subtype.val_injective.comp (hinj.comp Subtype.val_injective)
  obtain ⟨K, hK⟩ := (A.isClosed_range_iff_antilipschitz_of_injective hA_inj).mp hA_closed
  refine ⟨K, fun z hz ↦ ?_⟩
  have hb := hK.le_mul_dist (⟨z, hz⟩ : D) 0
  rw [map_zero, dist_zero_right, dist_zero_right] at hb
  change ‖z‖ ≤ (K : ℝ) * ‖P z‖ at hb
  exact hb

/-- A continuous linear map commuting with a group action that restricts an ambient
action preserves every ambient isotype. -/
private theorem primePV_mem_actionIsotype_of_commute {K E : Type*} [Monoid K] [TopologicalSpace K]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (ρ : K →* (E →L[ℂ] E))
    (ω : PontryaginDual K) (H : Submodule ℂ E) (R : K → H →L[ℂ] H)
    (hR : ∀ k u, (R k u : E) = ρ k u) (P : H →L[ℂ] H) (hP : ∀ k u, P (R k u) = R k (P u))
    (u : H) (hu : (u : E) ∈ actionIsotype ρ ω) : (P u : E) ∈ actionIsotype ρ ω := by
  rw [mem_actionIsotype] at hu ⊢
  intro k
  have hRk : R k u = (ω k : ℂ) • u := Subtype.ext ((hR k u).trans (hu k))
  rw [← hR, ← hP, hRk, map_smul]
  rfl

private theorem primePV_preserves_trivial_isotype
    (S : Finset V(ℚ)) (hs : (0 : ℝ) ≤ 2) (y : theta0(ℚ, hs))
    (hy : y.val ∈ Wω(ℚ, hs, (1 : PontryaginDual C₁(ℚ)))) :
    (globalThetaSobolevPrincipalValue ℚ S 0 hs y).val ∈
      Wω(ℚ, hs, (1 : PontryaginDual C₁(ℚ))) := by
  let P := globalThetaSobolevPrincipalValue ℚ S 0 hs
  let R := (exists_globalThetaSobolevAction (F := ℚ) 0 (le_rfl (a := (0 : ℝ))) hs).choose
  have hR := (exists_globalThetaSobolevAction (F := ℚ) 0 (le_rfl (a := (0 : ℝ))) hs).choose_spec.1
  exact primePV_mem_actionIsotype_of_commute _ _ _ (fun k ↦ R k.val)
    (fun k ↦ hR k.val) P (fun k ↦ globalThetaSobolevPrincipalValue_equivariant (F := ℚ) S 0 hs k)
    y hy

private theorem rat_trivial_unramified (w : V(ℚ)) :
    (ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ)) 0).IsUnramifiedAt w := by
  have hone : ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ)) 0 = 1 := by
    ext a
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  rw [hone, HeckeCharacter.isUnramifiedAt_iff]
  simp

private theorem rat_primeOrbital_range_closed (v : V(ℚ)) (hs : (0 : ℝ) ≤ 2)
    (h : Printed.primeOrbitalSobolevDenominator_closed) :
    let E := Wω(ℚ, hs, (1 : PontryaginDual C₁(ℚ)))
    let H := theta0(ℚ, hs)
    let P := globalThetaSobolevPrincipalValue ℚ {v} 0 hs
    IsClosed {x : E | ∃ y : H, y.val ∈ E ∧ (P y).val = x.val} := by
  classical
  intro E H P
  let χ : PontryaginDual C𝔽(ℚ) := 1
  have hclosed := h ℚ χ v (fun w _ ↦ rat_trivial_unramified w) 2 hs
  rw [rat_placesAbove_eq_singleton] at hclosed
  exact hclosed

/-- Paper: Paragraph before (11.2.2.1), p. 489.
Over ℚ, take the trivial norm-one isotype of degree two and the place over 2.
Log-radial exponentials are approximate invariants under the uniformizer
translation. Their prime principal values contradict the norm lower bound
that closed range would imply on this isotype. -/
theorem Printed.primeOrbitalSobolevDenominator_closed_false :
    ¬ Printed.primeOrbitalSobolevDenominator_closed := by
  intro h
  let v : V(ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
  have hs : (0 : ℝ) ≤ 2 := by norm_num
  let E := Wω(ℚ, hs, (1 : PontryaginDual C₁(ℚ)))
  let H := theta0(ℚ, hs)
  let P := globalThetaSobolevPrincipalValue ℚ {v} 0 hs
  let : CompleteSpace H := (globalThetaSobolev_closed_complete_separable (F := ℚ) 0
    (le_rfl (a := (0 : ℝ))) hs).2.1
  have hcE := isClosed_actionIsotype
    ((hardySobolevTranslation (ideleClassTamagawaMeasure ℚ) (m𝔽(ℚ))
      0 0 2 (le_rfl (a := (0 : ℝ))) hs).comp (ideleClassNorm ℚ).ker.subtype) (1 : PontryaginDual C₁(ℚ))
  have hinj : Injective P := globalThetaSobolevPrincipalValue_injective {v} 0 hs
  obtain ⟨K, hK⟩ := norm_le_mul_of_closed_isotype_range E H P hcE hinj
    (primePV_preserves_trivial_isotype {v} hs) (rat_primeOrbital_range_closed v hs h)
  obtain ⟨z, hz, hc⟩ := exists_ratPrimePrincipalValue_small_norm v hs K
  exact hc.not_ge (hK z hz)

end RiemannMasullo
