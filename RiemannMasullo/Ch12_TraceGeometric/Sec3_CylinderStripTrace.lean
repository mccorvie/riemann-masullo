module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_PrimitiveDirichletFormula
public import RiemannMasullo.Ch10_TraceSpectral.Sec3
import Mathlib.Tactic

/-! # The quotient Hilbert trace of a rational conductor cylinder

A choice of angular lifts can include every primitive idelic row at the given
level. Congruence-kernel orthogonality removes the other rows in the genuine
Hilbert trace, at the boundary as well as in the strip interior.
-/

@[expose] public noncomputable section

open Classical Filter Function MeasureTheory Set NumberField
open scoped ComplexConjugate ContDiff NumberField.AdeleRing Topology

namespace RiemannMasullo.ConductorCylinder

open NumberFieldKB.Chebotarev.RatIdele ConductorDensity RationalConductor

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "K" => (ideleClassNorm ℚ).ker
local notation "res" => (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : K →ₜ* Cℚ)
local notation "band(" ha ")" => (neg_nonpos.mpr ha |>.trans ha)
local notation "Q(" ha ", " hs ")" => spectralSobolevQuotient ℚ (1/2) (band(ha)) (zero_lt_one.trans hs).le
local notation "pt(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "ord(" ψ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := ℚ) ψ) z
local notation "div(" ψ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := ℚ) ψ) univ z
local notation "M(" φ ", " ψ ", " z ")" => modulatedFourierMellin (continuousIdeleClassNorm ℚ) univ
  ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩ (ideleClassTamagawaMeasure ℚ)
  (φ : BruhatCompactSupport Cℚ).val (ideleClassNormTwist ψ z)
local notation "Y(" χ ", " a ")" => {y : PontryaginDual K × ℝ × ℝ // y.2.1 ∈ Icc (-a) a ∧
  0 < ord(χ y.1, pt(1/2+y.2.1,y.2.2))}
local notation "N(" χ ", " a ", " s ", " y ")" => spectralStripMultiplicity a s ((y).val.2.1)
  (ord(χ (y).val.1,pt(1/2+(y).val.2.1,(y).val.2.2))).untop₀.toNat

private def rowRestriction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : PontryaginDual K :=
  (packetRow χ).comp res

private theorem rowRestriction_injective (q : ℕ) [NeZero q] :
    Injective (rowRestriction (q := q)) := by
  intro χ η he
  apply angular_lift_injective q
  funext k
  change ((ratDirichletChar q χ k.val : ℂˣ) : ℂ) = ((ratDirichletChar q η k.val : ℂˣ) : ℂ)
  rw [← packetRow_value χ, ← packetRow_value η]
  exact congrArg (fun ξ : PontryaginDual K ↦ (ξ k : ℂ)) he

private theorem packet_basepoints (q : ℕ) [NeZero q] :
    ∃ χ : PontryaginDual K → PontryaginDual Cℚ, IsSpectralBasepointChoice χ ∧
      ∀ η : DirichletCharacter ℂ q, χ (rowRestriction η) = packetRow η := by
  obtain ⟨χ₀, hχ₀⟩ := exists_spectralBasepointChoice ℚ
  let e := rowRestriction (q := q)
  let χ (ξ : PontryaginDual K) := if h : ξ ∈ range e then packetRow h.choose else χ₀ ξ
  refine ⟨χ, fun ξ ↦ ?_, fun η ↦ ?_⟩
  · dsimp only [χ]
    split
    next h => exact h.choose_spec
    next => exact hχ₀ ξ
  · change χ (e η) = _
    dsimp only [χ]
    split
    next h => exact congrArg packetRow (rowRestriction_injective q h.choose_spec)
    next h => exact (h ⟨η,rfl⟩).elim

private theorem off_packet {q : ℕ} [NeZero q] (χ : PontryaginDual K → PontryaginDual Cℚ)
    (hχ : IsSpectralBasepointChoice χ) {ξ : PontryaginDual K}
    (hoff : ξ ∉ range (rowRestriction (q := q))) :
    ∃ k : K, angularResidue q k = 1 ∧ χ ξ k.val ≠ 1 := by
  by_contra! h
  obtain ⟨η, hη, _⟩ := existsUnique_angular_lift_of_trivial_on_kernel q (χ ξ) h
  apply hoff
  refine ⟨η, ?_⟩
  rw [← hχ ξ]
  ext1 k
  apply Circle.ext
  exact (packetRow_value η k.val).trans (hη k)

private theorem chart_point (z : ℂ) : pt(1/2+(z.re-1/2),z.im) = z := by
  apply Complex.ext <;> simp

private theorem chart_offset (z : ℂ) : pt(z.re-1/2,z.im) = z - 1/2 := by
  apply Complex.ext <;> simp

private theorem order_eq_divisor (ψ : PontryaginDual Cℚ) (z : ℂ) : (ord(ψ,z)).untop₀ = div(ψ,z) :=
  (MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec ψ).1.meromorphicOn (mem_univ _)).symm

private theorem positive_order {ψ : PontryaginDual Cℚ} (z : rowZeroSites ψ) : 0 < ord(ψ,z.val) := by
  have hz : 0 < div(ψ,z.val) := z.property
  rw [← order_eq_divisor] at hz
  cases h : ord(ψ,z.val) with
  | top => simp
  | coe n => rw [h, WithTop.untop₀_coe] at hz; exact_mod_cast hz

private theorem no_jets_outside {a x : ℝ} (ha : 0 ≤ a) (hx : x ∉ Icc (-a) a) (s : ℝ) (n : ℕ) :
    spectralStripMultiplicity a s x n = 0 := by
  have hi : ¬(-a < x ∧ x < a) := fun h ↦ hx ⟨h.1.le, h.2.le⟩
  have he : ¬(x = -a ∨ x = a) := by
    rintro (rfl | rfl) <;> apply hx <;> constructor <;> linarith
  simp only [spectralStripMultiplicity, ite_eq_right hi, ite_eq_right he]

/-- Paper: Theorem 10.3.2.1 and §12.3, pp. 454, 514. The Hilbert trace of the
centered quotient convolution equals the physical Dirichlet sum on the single
residue cylinder at every width, with the actual partial boundary multiplicities. -/
theorem hilbertTrace_eq_physicalCenteredRetained (q : ℕ) [NeZero q] (r : (ZMod q)ˣ)
    (H : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ) (hφ : IsNormalizedCylinder q r H φ)
    {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s) (T : nuclearEndomorphisms Q(ha,hs))
    (hT : T.val = spectralConvolution (F := ℚ) (1/2) (band(ha)) (zero_lt_one.trans hs).le φ) :
    hilbertTrace T = physicalCenteredRetained q φ a s := by
  obtain ⟨χ, hχ, hpack⟩ := packet_basepoints q
  let Z := Σ η : DirichletCharacter ℂ q, rowZeroSites (packetRow η)
  let B := {z : Z // z.2.val.re - 1/2 ∈ Icc (-a) a}
  let Y := Y(χ,a)
  let f (y : Y) := (N(χ,a,s,y) : ℂ) * M(φ,χ y.val.1,pt(y.val.2.1,y.val.2.2))
  let W (z : Z) := (spectralStripMultiplicity a s (z.2.val.re-1/2)
    (div(packetRow z.1,z.2.val)).toNat : ℂ) * M(φ,packetRow z.1,z.2.val-1/2)
  let e (z : B) : Y := ⟨(rowRestriction z.val.1, z.val.2.val.re-1/2, z.val.2.val.im), z.property,
    by rw [hpack, chart_point]; exact positive_order _⟩
  have hi : Injective e := by
    rintro ⟨⟨η,z⟩,hz⟩ ⟨⟨θ,u⟩,hu⟩ he
    have hη := rowRestriction_injective q (congrArg (fun y : Y ↦ y.val.1) he)
    obtain rfl : η = θ := hη
    have hr := congrArg (fun y : Y ↦ y.val.2.1) he
    have him := congrArg (fun y : Y ↦ y.val.2.2) he
    obtain rfl : z = u := Subtype.ext (Complex.ext (sub_left_inj.mp hr) him)
    rfl
  have hoff (y : Y) (hy : y ∉ range e) : f y = 0 := by
    by_cases hξ : y.val.1 ∈ range (rowRestriction (q := q))
    · obtain ⟨η,hη⟩ := hξ
      let u := pt(1/2+y.val.2.1,y.val.2.2)
      have hr : u.re - 1/2 = y.val.2.1 := by simp [u]
      have him : u.im = y.val.2.2 := by simp [u]
      by_cases hD : 0 < div(packetRow η,u)
      · let z : Z := ⟨η, ⟨u,hD⟩⟩
        exact (hy ⟨⟨z, hr ▸ y.property.1⟩, Subtype.ext (Prod.ext hη (Prod.ext hr him))⟩).elim
      have hm : (div(packetRow η,u)).toNat = 0 := Int.toNat_eq_zero.mpr (le_of_not_gt hD)
      have hw : N(χ,a,s,y) = 0 := by
        rw [← hη, hpack, order_eq_divisor]
        change spectralStripMultiplicity a s _ (div(packetRow η,u)).toNat = 0
        simp [hm, spectralStripMultiplicity, spectralBoundaryMultiplicity]
      simp only [f, hw, Nat.cast_zero, zero_mul]
    · have hzero := normalized_cylinder_mellin_eq_zero q r H φ hφ (χ y.val.1)
        (off_packet χ hχ hξ) pt(y.val.2.1,y.val.2.2)
      simp only [f, hzero, mul_zero]
  have hsub := (hi.hasSum_iff hoff).mpr (spectralStripConvolution_trace (1/2) χ hχ ha hs φ T hT).2
  have he (z : B) : f (e z) = W z.val := by
    dsimp only [f,e,W]
    rw [hpack, chart_point, chart_offset, order_eq_divisor]
  have htotal : HasSum W (hilbertTrace T) := by
    apply (Subtype.val_injective (p := fun z : Z ↦ z.2.val.re - 1/2 ∈ Icc (-a) a)).hasSum_iff ?_ |>.mp
    · exact hsub.congr_fun fun z ↦ (he z).symm
    · intro z hz
      have hb : z.2.val.re-1/2 ∉ Icc (-a) a := fun h ↦ hz ⟨⟨z,h⟩,rfl⟩
      simp only [W, no_jets_outside ha hb, Nat.cast_zero, zero_mul]
  rw [← htotal.tsum_eq, htotal.summable.tsum_sigma' htotal.summable.sigma_factor, tsum_fintype]
  simp only [physicalCenteredRetained, physicalWidthSum, W, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat]

end RiemannMasullo.ConductorCylinder
