module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FixedAnnulusOrbit
import RiemannMasullo.Ch12_TraceGeometric.Sec4_RadialOrbitLinear
import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import Mathlib.MeasureTheory.Group.Integral

/-! # Compact lift independence and separate angular covariance -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "Hₛ" => sProjectedDiagonal F S
set_option quotPrecheck false in
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "Q" => continuousSIdeleQuotientNorm F S
local notation "νₛ" => sAdditiveTamagawaMeasure F S
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "ψₛ" => sAdeleStandardCharacter F S
set_option quotPrecheck false in
local notation "normS(" x ")" => (((sIdeleNorm F S x).val : ℝ))
local notation "modS(" x ")" => ((∏ w : InfinitePlace F, ‖(x : Aₛ).1 w‖ ^ InfinitePlace.mult w) *
  ∏ v : S, ‖(x : Aₛ).2 v‖)
set_option quotPrecheck false in
local notation "raw(" f "," ρ "," b ")" =>
  sLocalTraceCutoffKernel f ρ (fun w : Aₛ ↦ b (modS(w)))

attribute [local instance] instSAdeleMeasurableSpaceSec1 instSIdeleLocallyCompactSec1
  instSIdeleQuotientMeasurableSpaceSec1 instNormOneSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1

local instance instSIdeleT2RadialOrbitLiftIndependence : T2Space Iₛ :=
  (sIdeleGroup_description F S).2.1

private theorem exists_sLocalTrace_compactTranslate
    (a : Iₛ) (f : BruhatCompactSupport Iₛ) :
    ∃ g : BruhatCompactSupport Iₛ, ∀ z : Iₛ, g.val z = f.val (a⁻¹ * z) := by
  let f₀ : bruhatSmoothSubmodule (G := Iₛ) := ⟨f.val, f.property.1⟩
  obtain ⟨g, hg, -⟩ := bruhatFirstOrder_translate (1 : LCATopologicalLie Iₛ) f₀ a
  refine ⟨⟨fun z ↦ f.val (a⁻¹ * z), ?_, ?_⟩, fun _ ↦ rfl⟩
  · rw [← funext hg]
    exact g.property
  · exact f.property.2.comp_homeomorph (Homeomorph.mulLeft a⁻¹)

private theorem sLocalTraceCutoffKernel_eq_of_translated_lift
    (ρ : Iₛ → ℂ) (σ : Aₛ → ℂ) (a : Iₛ) (ha : sIdeleNorm F S a = 1)
    (hρ : ∀ x, ρ (a⁻¹ * x) = ρ x)
    (f g : BruhatCompactSupport Iₛ) (hg : ∀ t : Iₛ, g.val t = f.val (a⁻¹ * t))
    (x : Iₛ) (y : Aₛ) :
    sLocalTraceCutoffKernel g ρ σ x y =
      sLocalTraceCutoffKernel f ρ σ (a⁻¹ * x) y := by
  let : BorelSpace Iₛ := sIdeleGroup_borelSpace (F := F) (S := S)
  let : (μₛ).IsHaarMeasure := sMultiplicativeTamagawaMeasure_isHaarMeasure
  unfold sLocalTraceCutoffKernel
  rw [hρ x]
  apply congrArg (ρ x * ·)
  apply integral_congr_ae
  refine ae_of_all _ fun u ↦ ?_
  apply congrArg (σ u * ·)
  unfold sLocalTraceDilationKernel
  let G (t : Iₛ) := g.val t / (Real.sqrt (normS(t)) : ℂ) *
    (ψₛ (((t⁻¹).val * x.val - y) * u) : ℂ)
  change (∫ t, G t ∂μₛ) = _
  rw [← integral_mul_left_eq_self G a]
  apply integral_congr_ae
  refine ae_of_all _ fun t ↦ ?_
  have hnorm : sIdeleNorm F S (a * t) = sIdeleNorm F S t := by
    rw [map_mul, ha, one_mul]
  have harg : ((a * t)⁻¹).val * x.val = (t⁻¹).val * (a⁻¹ * x).val :=
    congrArg Units.val (show (a * t)⁻¹ * x = t⁻¹ * (a⁻¹ * x) by
      rw [mul_inv_rev, mul_assoc])
  change g.val (a * t) / (Real.sqrt (normS(a * t)) : ℂ) *
    (ψₛ ((((a * t)⁻¹).val * x.val - y) * u) : ℂ) = _
  rw [hg, inv_mul_cancel_left, hnorm, harg]

private def sLocalTraceRadialOrbitEvaluationLinear
    (ρ : Iₛ → ℂ) (b : ℝ → ℂ) (hb : Continuous b) {B : ℝ}
    (hB : ∀ t, 0 ≤ t → ‖b t‖ ≤ B) (x y : Iₛ)
    (hSum : ∀ v : BruhatCompactSupport Iₛ,
      Summable fun ξ : Hₛ ↦ raw(v,ρ,b) x (ξ.val * y).val) :
    BruhatCompactSupport Iₛ →ₗ[ℂ] ℂ where
  toFun v := ∑' ξ : Hₛ, raw(v,ρ,b) x (ξ.val * y).val
  map_add' f g := by
    have hadd (ξ : Hₛ) : raw(f + g,ρ,b) x (ξ.val * y).val =
        raw(f,ρ,b) x (ξ.val * y).val + raw(g,ρ,b) x (ξ.val * y).val :=
      (sLocalTraceCutoffKernel_radial_lift_isLinear ρ b hb hB x (ξ.val * y).val).map_add f g
    simp_rw [hadd]
    exact (hSum f).tsum_add (hSum g)
  map_smul' c f := by
    change (∑' ξ : Hₛ, raw(c • f,ρ,b) x (ξ.val * y).val) =
      c * ∑' ξ : Hₛ, raw(f,ρ,b) x (ξ.val * y).val
    have hsmul (ξ : Hₛ) : raw(c • f,ρ,b) x (ξ.val * y).val =
        c * raw(f,ρ,b) x (ξ.val * y).val :=
      (sLocalTraceCutoffKernel_radial_lift_isLinear ρ b hb hB x (ξ.val * y).val).map_smul c f
    simp_rw [hsmul, tsum_mul_left]

private theorem sLocalTraceRadialOrbitEvaluationLinear_eq_of_periodization
    (ρ : Iₛ → ℂ) (b : ℝ → ℂ) (hb : Continuous b) {B : ℝ}
    (hB : ∀ t, 0 ≤ t → ‖b t‖ ≤ B)
    (hρ : ∀ (a : Iₛ), sIdeleNorm F S a = 1 → ∀ z, ρ (a * z) = ρ z)
    (hDesc : ∀ v : BruhatCompactSupport Iₛ, ∃ κ : Jₛ → Jₛ → ℂ,
      ∀ x y : Iₛ, κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : Hₛ, raw(v,ρ,b) x (ξ.val * y).val)
    (x y : Iₛ)
    (hSum : ∀ v : BruhatCompactSupport Iₛ,
      Summable fun ξ : Hₛ ↦ raw(v,ρ,b) x (ξ.val * y).val)
    {Φ : Jₛ → ℂ} (f g : BruhatCompactSupport Iₛ)
    (hf : ∀ z : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * z)) (Φ (QuotientGroup.mk z)))
    (hg : ∀ z : Iₛ, HasSum (fun ξ : Hₛ ↦ g.val (ξ.val * z)) (Φ (QuotientGroup.mk z))) :
    (∑' ξ : Hₛ, raw(f,ρ,b) x (ξ.val * y).val) =
      ∑' ξ : Hₛ, raw(g,ρ,b) x (ξ.val * y).val := by
  let E := sLocalTraceRadialOrbitEvaluationLinear ρ b hb hB x y hSum
  have hTranslate (ξ : Hₛ) (v w : BruhatCompactSupport Iₛ)
      (hw : ∀ z : Iₛ, w.val z = v.val (ξ.val⁻¹ * z)) : E w = E v := by
    have hξ : sIdeleNorm F S ξ.val = 1 := by
      obtain ⟨a, ha, he⟩ := Subgroup.mem_map.mp ξ.property
      exact he ▸ (sIdeleNorm_spec F S).2 ha
    have hξinv : sIdeleNorm F S ξ.val⁻¹ = 1 := by rw [map_inv, hξ, inv_one]
    have hξclass : (QuotientGroup.mk ξ.val : Jₛ) = 1 :=
      (QuotientGroup.eq_one_iff ξ.val).mpr ξ.property
    have hclass : (QuotientGroup.mk (ξ.val⁻¹ * x) : Jₛ) = QuotientGroup.mk x := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hξclass, inv_one, one_mul]
    obtain ⟨κ, hRep⟩ := hDesc v
    calc
      E w = ∑' η : Hₛ, raw(w,ρ,b) x (η.val * y).val := rfl
      _ = ∑' η : Hₛ, raw(v,ρ,b) (ξ.val⁻¹ * x) (η.val * y).val := by
        apply tsum_congr
        intro η
        exact sLocalTraceCutoffKernel_eq_of_translated_lift ρ _ ξ.val hξ
          (hρ ξ.val⁻¹ hξinv) v w hw x (η.val * y).val
      _ = κ (QuotientGroup.mk (ξ.val⁻¹ * x)) (QuotientGroup.mk y) :=
        (hRep (ξ.val⁻¹ * x) y).symm
      _ = κ (QuotientGroup.mk x) (QuotientGroup.mk y) := by rw [hclass]
      _ = E v := hRep x y
  exact sLocalTraceLift_linearMap_eq_of_periodization_eq E hTranslate f g hf hg

/-- Paper: Theorem 12.4.1.1, Step II, p. 517.
At a fixed annulus the periodized kernel depends on the quotient test.
A pure norm-one character of the quotient test gives separate covariance
of the kernel in its two variables, with inverse characters.
Deviation: The statement concerns the raw descended kernel. -/
theorem sLocalTrace_fixedAnnulus_orbitLift_independence_and_angular_covariance
    (b : ℝ → ℂ) {Λ ερ εb Cb : ℝ} {ρ : Jₛ → ℝ}
    (hρ : IsModulatedCutoff Q Λ ερ ρ)
    (hb : ContDiff ℝ (2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1) : ℕ) b)
    (hε : 0 < εb) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 εb))
    (hderiv : ∀ j ≤ 2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1),
      ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ Cb) :
    let π (x : Iₛ) : Jₛ := QuotientGroup.mk x
    let ρI (x : Iₛ) : ℂ := ρ (π x)
    let R (f : BruhatCompactSupport Iₛ) (x y : Iₛ) :=
      ∑' ξ : Hₛ, raw(f,ρI,b) x (ξ.val * y).val
    let IsLift (f : BruhatCompactSupport Iₛ) (Φ : Jₛ → ℂ) :=
      ∀ x : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * x)) (Φ (π x))
    (∀ (f g : BruhatCompactSupport Iₛ) (Φ : Jₛ → ℂ),
      IsLift f Φ → IsLift g Φ → ∀ x y : Iₛ, R f x y = R g x y) ∧
    ∀ (f : BruhatCompactSupport Iₛ) (Φ : Jₛ → ℂ), IsLift f Φ →
      ∀ (κ : Jₛ → Jₛ → ℂ), (∀ x y : Iₛ, κ (π x) (π y) = R f x y) →
        ∀ (angular : PontryaginDual J₁),
          (∀ (q : Jₛ) (h : J₁), Φ (q * h.val) = (angular h : ℂ)⁻¹ * Φ q) →
          (∀ (q y : Jₛ) (h : J₁), κ (q * h.val) y = (angular h : ℂ)⁻¹ * κ q y) ∧
            (∀ (q y : Jₛ) (h : J₁), κ q (y * h.val) = (angular h : ℂ) * κ q y) := by
  intro π ρI R IsLift
  have hbnd (r : ℝ) (hr : 0 ≤ r) : ‖b r‖ ≤ Cb := by
    simpa only [iteratedDeriv_zero] using hderiv 0 (Nat.zero_le _) r hr
  obtain ⟨p, _, hp, _⟩ := hρ.profile
  have hρInv (a : Iₛ) (ha : sIdeleNorm F S a = 1) (x : Iₛ) : ρI (a * x) = ρI x := by
    have hn : Q (π (a * x)) = Q (π x) := by
      change sIdeleQuotientNorm F S (QuotientGroup.mk (a * x)) =
        sIdeleQuotientNorm F S (QuotientGroup.mk x)
      rw [sIdeleQuotientNorm_mk, sIdeleQuotientNorm_mk, map_mul, ha, one_mul]
    have hr := (hp (π (a * x))).trans
      ((congrArg (fun t : ℝ≥0ˣ ↦ p (t.val : ℝ)) hn).trans (hp (π x)).symm)
    exact congrArg Complex.ofReal hr
  have hData (v : BruhatCompactSupport Iₛ) : ∃ κ : Jₛ → Jₛ → ℂ,
      (∀ x y : Iₛ, κ (π x) (π y) = R v x y) ∧
      (∀ x y : Iₛ, Summable fun ξ : Hₛ ↦ raw(v,ρI,b) x (ξ.val * y).val) ∧
      (∀ (q y : Jₛ) (h : J₁), κ (q * h.val) (y * h.val) = κ q y) := by
    obtain ⟨_, κ, _, _, _, _, hRep, _, hDiag, hAbs, _⟩ :=
      exists_sLocalTrace_halfDensityOrbitKernel_fixed_annulus_data (s := 0) v b hρ
        le_rfl hb hε hplateau hderiv
    exact ⟨κ, hRep, fun x y ↦ (hAbs x y).1.of_norm, hDiag⟩
  have hDesc (v : BruhatCompactSupport Iₛ) : ∃ κ : Jₛ → Jₛ → ℂ,
      ∀ x y : Iₛ, κ (π x) (π y) = R v x y := by
    obtain ⟨κ, hκ, _, _⟩ := hData v
    exact ⟨κ, hκ⟩
  have hSum (v : BruhatCompactSupport Iₛ) (x y : Iₛ) :
      Summable fun ξ : Hₛ ↦ raw(v,ρI,b) x (ξ.val * y).val := by
    obtain ⟨_, _, hv, _⟩ := hData v
    exact hv x y
  have hInd (f g : BruhatCompactSupport Iₛ) (Φ : Jₛ → ℂ)
      (hf : IsLift f Φ) (hg : IsLift g Φ) (x y : Iₛ) : R f x y = R g x y :=
    sLocalTraceRadialOrbitEvaluationLinear_eq_of_periodization ρI b hb.continuous
      hbnd hρInv hDesc x y (fun v ↦ hSum v x y) f g hf hg
  refine ⟨hInd, ?_⟩
  intro f Φ hLift κ hRep angular hΦ
  have hOut (q y : Jₛ) (h : J₁) : κ (q * h.val) y = (angular h : ℂ)⁻¹ * κ q y := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    let a : Iₛ := h.val.out
    have haClass : π a = h.val := QuotientGroup.out_eq' h.val
    have ha : sIdeleNorm F S a = 1 := by
      rw [← sIdeleQuotientNorm_mk F S a]
      change sIdeleQuotientNorm F S (π a) = 1
      rw [haClass]
      exact MonoidHom.mem_ker.mp h.property
    have haInv : sIdeleNorm F S a⁻¹ = 1 := by rw [map_inv, ha, inv_one]
    let c : ℂ := (angular h : ℂ)⁻¹
    obtain ⟨w, hw⟩ := exists_sLocalTrace_compactTranslate a⁻¹ f
    have hwLift : IsLift w (fun q ↦ c * Φ q) := by
      intro z
      change HasSum (fun ξ : Hₛ ↦ w.val (ξ.val * z)) (c * Φ (π z))
      have he : (fun ξ : Hₛ ↦ w.val (ξ.val * z)) =
          fun ξ : Hₛ ↦ f.val (ξ.val * (a * z)) := by
        funext ξ
        rw [hw, inv_inv, mul_left_comm]
      have hz : π (a * z) = π z * h.val := by
        change (QuotientGroup.mk (a * z) : Jₛ) = π z * h.val
        rw [QuotientGroup.mk_mul, ← haClass]
        exact mul_comm _ _
      have hValue : Φ (π (a * z)) = c * Φ (π z) := by
        rw [hz]
        exact hΦ (π z) h
      rw [he, ← hValue]
      exact hLift (a * z)
    have hcLift : IsLift (c • f) (fun q ↦ c * Φ q) := by
      intro z
      change HasSum (fun ξ : Hₛ ↦ c * f.val (ξ.val * z)) (c * Φ (π z))
      exact (hLift z).mul_left c
    have hshift : R f (a * x) y = R w x y := by
      apply tsum_congr
      intro ξ
      simpa only [inv_inv] using
        (sLocalTraceCutoffKernel_eq_of_translated_lift ρI _ a⁻¹ haInv
          (by simpa only [inv_inv] using hρInv a ha) f w hw x (ξ.val * y).val).symm
    have hq : π x * h.val = π (a * x) := calc
      π x * h.val = π a * π x := by rw [← haClass, mul_comm]
      _ = π (a * x) := by
        change (QuotientGroup.mk a : Jₛ) * QuotientGroup.mk x = QuotientGroup.mk (a * x)
        rw [QuotientGroup.mk_mul]
    let E := sLocalTraceRadialOrbitEvaluationLinear ρI b hb.continuous hbnd x y
      (fun v ↦ hSum v x y)
    have hScalar : R (c • f) x y = c * R f x y := E.map_smul c f
    change κ (π x * h.val) (π y) = c * κ (π x) (π y)
    rw [hq, hRep (a * x) y, hRep x y, hshift]
    exact (hInd w (c • f) (fun q ↦ c * Φ q) hwLift hcLift x y).trans hScalar
  refine ⟨hOut, ?_⟩
  obtain ⟨κ₀, hRep₀, _, hDiag₀⟩ := hData f
  have hEq : κ = κ₀ := by
    funext q y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    exact (hRep x z).trans (hRep₀ x z).symm
  have hDiag (q y : Jₛ) (h : J₁) : κ (q * h.val) (y * h.val) = κ q y := by
    rw [hEq]
    exact hDiag₀ q y h
  intro q y h
  calc
    κ q (y * h.val) = κ (q * (h⁻¹).val) ((y * h.val) * (h⁻¹).val) :=
      (hDiag q (y * h.val) h⁻¹).symm
    _ = κ (q * (h⁻¹).val) y := by
      have hi : (y * h.val) * (h⁻¹).val = y := by
        change (y * h.val) * h.val⁻¹ = y
        rw [mul_assoc, mul_inv_cancel, mul_one]
      rw [hi]
    _ = (angular h : ℂ) * κ q y := by
      rw [hOut, map_inv, Circle.coe_inv, inv_inv]

end RiemannMasullo
