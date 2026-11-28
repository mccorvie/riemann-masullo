module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_CriticalLineFourierPhase
import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec5
import RiemannMasullo.ForMathlib.Analysis.Fourier.CompactGroup
import Mathlib.Tactic.Ring

/-! # Compact smooth generators for the reflected S-local band -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo


attribute [local instance] instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Jₛ" => SIdeleQuotient F S
local notation "Bₛ" => SchwartzBruhat (Multiplicative Aₛ)
local notation "m" => sIdeleQuotientNorm F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "ℓ" => logSIdeleQuotientNorm F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "C₁" => Measure.real η univ
local notation "d₁" => (Real.sqrt C₁ : ℂ)
local notation "include₁" =>
  (ContinuousMonoidHom.mk (Subgroup.subtype (MonoidHom.ker (sIdeleQuotientNorm F S)))
    continuous_subtype_val : J₁ →ₜ* Jₛ)

/-- The compact quotient test producing a reflected log profile has inverse
half-density and compensates for both the raw norm-one integral and the L²
normalization. Its support tracks the reflected log profile. -/
theorem exists_sLocalQuotient_reflectedProfile (χ : PontryaginDual Jₛ)
    (r : ℝ → ℂ) (hr : ContDiff ℝ (∞ : ℕ∞ω) r) (hrc : HasCompactSupport r) :
    ∃ Φ : BruhatCompactSupport Jₛ,
      tsupport Φ.val ⊆ (fun q : Jₛ ↦ -ℓ q) ⁻¹' tsupport r ∧
      ∀ q : Jₛ, Φ.val q = (χ q : ℂ) *
        ((d₁ * (C₁ : ℂ))⁻¹ * (Real.exp (-ℓ q / 2) : ℂ) * r (-ℓ q)) := by
  let e : ℝ≥0ˣ ≃ₜ ℝ := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have he : e ∘ m = ℓ := funext fun q ↦
    (Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (m q)))).symm
  have hl : IsProperMap ℓ := he ▸ e.isProperMap.comp (isProperMap_sIdeleQuotientNorm F S)
  have hn : IsProperMap (fun q : Jₛ ↦ -ℓ q) := (Homeomorph.neg ℝ).isProperMap.comp hl
  let a : ℂ := (d₁ * (C₁ : ℂ))⁻¹
  let p (x : ℝ) := a * (Real.exp (-x / 2) : ℂ) * r (-x)
  have hp : ContDiff ℝ (∞ : ℕ∞ω) p :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp (contDiff_neg.div_const 2)))).mul (hr.comp contDiff_neg)
  let ψ : QuasiCharacter Jₛ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  have hψ : IsBruhatSmooth (fun q : Jₛ ↦ (χ q : ℂ)) :=
    (mem_bruhatSmoothSubmodule_iff _).mp (quasiCharacter_mem_bruhatSmooth ψ)
  let f (q : Jₛ) := (χ q : ℂ) * p (ℓ q)
  have hs : IsBruhatSmooth f := fun j ↦ isBruhatContDiff_mul (hψ j)
    (isBruhatSmooth_logProfile (continuousSIdeleQuotientNorm F S) hp j)
  have ht : tsupport f ⊆ (fun q : Jₛ ↦ -ℓ q) ⁻¹' tsupport r := by
    apply closure_minimal _ (isClosed_closure.preimage hn.continuous)
    intro q hq
    by_contra h
    have hz : r (-ℓ q) = 0 := image_eq_zero_of_notMem_tsupport h
    exact hq (by simp [f, p, hz])
  have hc : HasCompactSupport f := (hn.isCompact_preimage hrc).of_isClosed_subset
    isClosed_closure ht
  exact ⟨⟨f, (mem_bruhatSmoothSubmodule_iff _).mpr hs, hc⟩, ht, fun _ ↦ rfl⟩

/-- Additive lifts realize the entire smooth reflected core at the same
product bandwidth. This gives ordinary theta for the polar moment and
homogeneous theta for the reflected profile. -/
theorem exists_sLocalTrace_reflectedThetaCore (χ : PontryaginDual Jₛ)
    (r : ℝ → ℂ) (hr : ContDiff ℝ (∞ : ℕ∞ω) r) (hrc : HasCompactSupport r)
    {B : ℝ} (hB : 0 < B) (hrs : tsupport r ⊆ Ioi (-Real.log B)) :
    ∃ g : Bₛ,
      HasCompactSupport (fun x : Aₛ ↦ g (Multiplicative.ofAdd x)) ∧
      tsupport (fun x : Aₛ ↦ g (Multiplicative.ofAdd x)) ⊆ sLocalPWProductRegion S B ∧
      g (Multiplicative.ofAdd (0 : Aₛ)) = 0 ∧
      (∀ q : Jₛ, sLocalAdelicThetaOnClasses F S g q = (χ q : ℂ) *
        ((d₁ * (C₁ : ℂ))⁻¹ * (Real.exp (-ℓ q / 2) : ℂ) * r (-ℓ q))) ∧
      ∀ q : Jₛ,
        d₁ * (sLocalHomogeneousAdelicThetaLinearMap F S (χ⁻¹.comp include₁) g q *
          ((χ⁻¹) q : ℂ)) = (Real.exp (-ℓ q / 2) : ℂ) * r (-ℓ q) := by
  obtain ⟨Φ, hΦS, hΦ⟩ := exists_sLocalQuotient_reflectedProfile χ r hr hrc
  obtain ⟨g, hgc, hgs, hθ⟩ := exists_sLocalTraceAdditiveThetaLift Φ
  have hgθ (q : Jₛ) : sLocalAdelicThetaOnClasses F S g q = (χ q : ℂ) *
      ((d₁ * (C₁ : ℂ))⁻¹ * (Real.exp (-ℓ q / 2) : ℂ) * r (-ℓ q)) :=
    (hθ q).trans (hΦ q)
  have hband : tsupport (fun x : Aₛ ↦ g (Multiplicative.ofAdd x)) ⊆
      sLocalPWProductRegion S B := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := hgs hx
    have hn : (((sIdeleNorm F S u).val : ℝ)) < B := by
      apply (Real.log_lt_log_iff (NNReal.coe_pos.mpr (Units.zero_lt _)) hB).mp
      have h := hrs (hΦS hu)
      change -Real.log B < -ℓ (QuotientGroup.mk u) at h
      change Real.log ((sIdeleNorm F S u).val : ℝ) < Real.log B
      change -Real.log B < -Real.log ((m (QuotientGroup.mk u)).val : ℝ) at h
      rw [sIdeleQuotientNorm_mk] at h
      linarith
    exact (mem_sLocalPWProductRegion_units B u).2 hn.le
  have hgzero : g (Multiplicative.ofAdd (0 : Aₛ)) = 0 := by
    by_contra hn
    obtain ⟨u, -, hu⟩ := hgs (subset_tsupport _ hn)
    exact not_isUnit_zero (hu ▸ u.isUnit)
  refine ⟨g, hgc, hband, hgzero, hgθ, fun q ↦ ?_⟩
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : Measure.IsHaarMeasure η := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : IsFiniteMeasure η := CompactSpace.isFiniteMeasure
  have hC : 0 < C₁ := measureReal_univ_pos
  have hCne : (C₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
  have hdne : d₁ ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hC).ne'
  have hlog (h : J₁) : ℓ (q * h.val) = ℓ q := by
    change Real.log ((m (q * h.val)).val : ℝ) = Real.log ((m q).val : ℝ)
    rw [map_mul, MonoidHom.mem_ker.mp h.property, mul_one]
  have hχinv (v : Jₛ) : ((χ⁻¹) v : ℂ) = (χ v : ℂ)⁻¹ := by
    rw [show (χ⁻¹) v = (χ v)⁻¹ from rfl, Circle.coe_inv]
  let p := (d₁ * (C₁ : ℂ))⁻¹ * (Real.exp (-ℓ q / 2) : ℂ) * r (-ℓ q)
  have hh : sLocalHomogeneousAdelicThetaLinearMap F S (χ⁻¹.comp include₁) g q =
      (C₁ : ℂ) * ((χ q : ℂ) * p) := by
    let ψ : PontryaginDual J₁ := χ⁻¹.comp include₁
    calc
      _ = ∫ h : J₁, sLocalAdelicThetaOnClasses F S g (q * h.val) * (ψ h : ℂ) ∂η :=
        sLocalHomogeneousAdelicThetaLinearMap_apply (F := F) (S := S) ψ g q
      _ = ∫ _ : J₁, (χ q : ℂ) * p ∂η := by
        apply integral_congr_ae (ae_of_all _ fun h ↦ ?_)
        rw [hgθ, hlog]
        change (χ (q * h.val) : ℂ) * p * ((χ⁻¹) h.val : ℂ) = _
        rw [map_mul, Circle.coe_mul, hχinv]
        rw [show (χ q : ℂ) * (χ h.val : ℂ) * p * (χ h.val : ℂ)⁻¹ =
          ((χ q : ℂ) * p) * ((χ h.val : ℂ) * (χ h.val : ℂ)⁻¹) by ring,
          mul_inv_cancel₀ (Circle.coe_ne_zero _), mul_one]
      _ = _ := by rw [integral_const, Complex.real_smul]
  rw [hh, hχinv]
  dsimp only [p]
  field_simp [hCne, hdne, Circle.coe_ne_zero (χ q)]

private theorem sLocalTrace_trivialTheta_eq_zero_of_reflectedProfile
    (χ : PontryaginDual Jₛ) (hχ : χ.comp include₁ ≠ 1) (g : Bₛ) (p : Jₛ → ℂ)
    (hp : ∀ (q : Jₛ) (h : J₁), p (q * h.val) = p q)
    (hθ : ∀ q : Jₛ, sLocalAdelicThetaOnClasses F S g q = (χ q : ℂ) * p q) (q : Jₛ) :
    sLocalHomogeneousAdelicThetaLinearMap F S 1 g q = 0 := by
  classical
  let : BorelSpace J₁ := ⟨rfl⟩
  let : Measure.IsHaarMeasure η := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have hχint : (∫ h : J₁, (χ h.val : ℂ) ∂η) = 0 := by
    let ψ : PontryaginDual J₁ := χ.comp include₁
    have hne : (1 : PontryaginDual J₁) ≠ ψ := fun he ↦ hχ he.symm
    have hi := integral_character_pair η (1 : PontryaginDual J₁) ψ
    rw [ite_eq_right hne] at hi
    change (∫ h : J₁, (ψ h : ℂ) ∂η) = 0
    simpa only [PontryaginDual.one_apply, Circle.coe_one, star_one, one_mul] using hi
  calc
    _ = ∫ h : J₁, sLocalAdelicThetaOnClasses F S g (q * h.val) *
        (((1 : PontryaginDual J₁) h : Circle) : ℂ) ∂η :=
      sLocalHomogeneousAdelicThetaLinearMap_apply (F := F) (S := S) 1 g q
    _ = ∫ h : J₁, ((χ q : ℂ) * p q) * (χ h.val : ℂ) ∂η := by
      apply integral_congr_ae (ae_of_all _ fun h ↦ ?_)
      rw [hθ, hp, PontryaginDual.one_apply, Circle.coe_one, mul_one, map_mul, Circle.coe_mul]
      ring
    _ = 0 := by rw [integral_const_mul, hχint, mul_zero]

/-- Every compact smooth reflected profile inside the half-line is the
reflected Fourier theta of a same-stage polar product-band test. The trivial
norm-one character requires the exponential moment to vanish. -/
theorem exists_sLocalPolarPW_reflectedSmoothGenerator
    (τ : ℝ≥0ˣ →ₜ* Aₛˣ) (hτ : RightInverse τ (sIdeleNorm F S))
    (χ : PontryaginDual Jₛ) (hχτ : ∀ t, χ (QuotientGroup.mk (τ t)) = 1)
    (r : ℝ → ℂ) (hr : ContDiff ℝ (∞ : ℕ∞ω) r) (hrc : HasCompactSupport r)
    {B : ℝ} (hB : 0 < B) (hrs : tsupport r ⊆ Ioi (-Real.log B))
    (hmoment : χ.comp include₁ = 1 → (∫ y : ℝ, (Real.exp (-y / 2) : ℂ) * r y) = 0) :
    ∃ f : Bₛ,
      f ∈ sAdelePolarSubspace F S ∧
      f ∈ sLocalPWTests (F := F) (S := S) (T := S) le_rfl (sLocalPWProductRegion S B) ∧
      ∀ y : ℝ, d₁ * sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f) (-y) = r y := by
  obtain ⟨g, hgc, hgs, hgzero, hθ, hhom⟩ := exists_sLocalTrace_reflectedThetaCore χ r hr hrc hB hrs
  let f := sAdeleSchwartzFourier (sAdeleSchwartzFourier (sAdeleSchwartzFourier g))
  have hF : sAdeleSchwartzFourier f = g := by
    apply Subtype.ext
    funext z
    exact (sLocal_fourier_inversion (sAdeleSchwartzFourier (sAdeleSchwartzFourier g))
      z.toAdd).trans ((sLocal_fourier_inversion g (-z.toAdd)).trans
        (congrArg (fun y ↦ g (Multiplicative.ofAdd y)) (neg_neg z.toAdd)))
  let t (x : ℝ) : ℝ≥0ˣ := Units.mk0 (Real.exp x).toNNReal (by positivity)
  let q (y : ℝ) : Jₛ := QuotientGroup.mk (τ (t (-y)))
  have hq (y : ℝ) : ℓ (q y) = -y := by
    change Real.log ((m (QuotientGroup.mk (τ (t (-y))))).val : ℝ) = -y
    rw [sIdeleQuotientNorm_mk, hτ]
    change Real.log ((Real.exp (-y)).toNNReal : ℝ) = -y
    rw [Real.coe_toNNReal _ (Real.exp_pos _).le, Real.log_exp]
  have hscaled (y : ℝ) : d₁ * (sLocalHomogeneousAdelicThetaLinearMap F S
      (χ⁻¹.comp include₁) g (q y) * ((χ⁻¹) (q y) : ℂ)) = (Real.exp (y / 2) : ℂ) * r y := by
    simpa only [hq y, neg_neg] using hhom (q y)
  have hInt : (∫ y : ℝ, sLocalHomogeneousAdelicThetaLinearMap F S 1 g (q y) *
      (Real.exp (-y) : ℂ)) = 0 := by
    by_cases hχ : χ.comp include₁ = 1
    · let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
        ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
      let : Measure.IsHaarMeasure η := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
      let : IsFiniteMeasure η := CompactSpace.isFiniteMeasure
      have hC : 0 < C₁ := measureReal_univ_pos
      have hd : d₁ ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hC).ne'
      have hχinv : χ⁻¹.comp include₁ = 1 := by
        apply DFunLike.ext
        intro h
        have hh : χ h.val = 1 := DFunLike.congr_fun hχ h
        change (χ h.val)⁻¹ = 1
        rw [hh, inv_one]
      have hchar (y : ℝ) : ((χ⁻¹) (q y) : ℂ) = 1 := by
        change (((χ (q y))⁻¹ : Circle) : ℂ) = 1
        rw [show χ (q y) = 1 from hχτ (t (-y)), inv_one, Circle.coe_one]
      have hval (y : ℝ) : sLocalHomogeneousAdelicThetaLinearMap F S 1 g (q y) =
          d₁⁻¹ * ((Real.exp (y / 2) : ℂ) * r y) := by
        apply (eq_inv_mul_iff_mul_eq₀ hd).2
        have hy := hscaled y
        rw [hχinv, hchar y, mul_one] at hy
        exact hy
      calc
        _ = ∫ y : ℝ, d₁⁻¹ * ((Real.exp (-y / 2) : ℂ) * r y) := by
          apply integral_congr_ae (ae_of_all _ fun y ↦ ?_)
          have he : (Real.exp (y / 2) : ℂ) * (Real.exp (-y) : ℂ) = (Real.exp (-y / 2) : ℂ) := by
            rw [← Complex.ofReal_mul, ← Real.exp_add, show y / 2 + -y = -y / 2 from by ring]
          rw [hval]
          calc
            _ = d₁⁻¹ * (((Real.exp (y / 2) : ℂ) * (Real.exp (-y) : ℂ)) * r y) := by ring
            _ = _ := by rw [he]
        _ = 0 := by rw [integral_const_mul, hmoment hχ, mul_zero]
    · let p (v : Jₛ) := (d₁ * (C₁ : ℂ))⁻¹ * (Real.exp (-ℓ v / 2) : ℂ) * r (-ℓ v)
      have hp (v : Jₛ) (h : J₁) : p (v * h.val) = p v := by
        have hlog : ℓ (v * h.val) = ℓ v := by
          change Real.log ((m (v * h.val)).val : ℝ) = Real.log ((m v).val : ℝ)
          rw [map_mul, MonoidHom.mem_ker.mp h.property, mul_one]
        simp only [p, hlog]
      have hz := sLocalTrace_trivialTheta_eq_zero_of_reflectedProfile χ hχ g p hp hθ
      simp only [hz, zero_mul, integral_zero]
  have hfzero : f (Multiplicative.ofAdd (0 : Aₛ)) = 0 := by
    have hfac : 0 < sLocalTraceMeasureFactor S := by
      unfold sLocalTraceMeasureFactor
      apply Finset.prod_pos
      intro v _
      have hv : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
      exact div_pos (zero_lt_one.trans hv) (sub_pos.mpr hv)
    have h := sLocalTrace_reflectedFourier_exponentialMoment τ hτ f
    change (∫ y : ℝ, sLocalHomogeneousAdelicThetaLinearMap F S 1 (sAdeleSchwartzFourier f)
      (q y) * (Real.exp (-y) : ℂ)) = (sLocalTraceMeasureFactor S : ℂ) *
        f (Multiplicative.ofAdd (0 : Aₛ)) at h
    rw [hF, hInt] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (Complex.ofReal_ne_zero.mpr hfac.ne')
  have hfpolar : f ∈ sAdelePolarSubspace F S :=
    (mem_sAdelePolarSubspace f).2 ⟨hfzero, by simpa only [hF] using hgzero⟩
  have hfband : f ∈ sLocalPWTests (F := F) (S := S) (T := S) le_rfl (sLocalPWProductRegion S B) := by
    have hself : sAdeleSchwartzTransition F (le_rfl (a := S)) f = f := by
      classical
      apply Subtype.ext
      funext x
      rw [← show Multiplicative.ofAdd x.toAdd = x from rfl, sAdeleSchwartzTransition_apply,
        ite_eq_left (fun w hw ↦ (hw w.property).elim)]
    refine (mem_sLocalPWTests (F := F) (S := S) (T := S) le_rfl (sLocalPWProductRegion S B) f).2
      ⟨f, hself, ?_⟩
    rw [hF]
    let e : Multiplicative Aₛ ≃ₜ Aₛ := (Homeomorph.ofAdd : Aₛ ≃ₜ Multiplicative Aₛ).symm
    have he : g.val = (fun x : Aₛ ↦ g (Multiplicative.ofAdd x)) ∘ e := rfl
    refine ⟨hgc.comp_homeomorph e, ?_⟩
    rw [he, tsupport_comp_eq_preimage]
    exact preimage_mono hgs
  refine ⟨f, hfpolar, hfband, fun y ↦ ?_⟩
  rw [hF]
  change d₁ * ((sLocalHomogeneousAdelicThetaLinearMap F S (χ⁻¹.comp include₁) g (q y) *
    ((χ⁻¹) (q y) : ℂ)) * (Real.exp (-y / 2) : ℂ)) = r y
  have he : (Real.exp (y / 2) : ℂ) * (Real.exp (-y / 2) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, show y / 2 + -y / 2 = 0 from by ring,
      Real.exp_zero, Complex.ofReal_one]
  rw [← mul_assoc, hscaled]
  calc
    _ = ((Real.exp (y / 2) : ℂ) * (Real.exp (-y / 2) : ℂ)) * r y := by ring
    _ = _ := by rw [he, one_mul]

end RiemannMasullo
