module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_ZetaPositiveLog
public import RiemannMasullo.Ch12_TraceGeometric.Sec5_SharpOrbitalDiagonal
import RiemannMasullo.ForMathlib.RingTheory.PicardGroup

/-! # Signed prime comparison for the rational radial strip trace

A radial test kills every nonprincipal angular row. The surviving row of
the genuine Hilbert trace therefore has a description directly on Mathlib's
completed zeta divisor. The half twist gives the factor `n^(-1/2)` in its
prime-power samples. The entire fixed-width error is the signed sum with the
missing Sobolev multiplicities, including partially retained boundary jets.
-/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ArithmeticFunction ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "K" => (ideleClassNorm ℚ).ker
local notation "X" => (1 : PontryaginDual Cℚ)
local notation "V" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "mℚ" => (continuousIdeleClassNorm ℚ : Cℚ →ₜ* ℝ≥0ˣ)
local notation "M(" φ ", " χ ", " z ")" => modulatedFourierMellin mℚ univ
  ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩ (ideleClassTamagawaMeasure ℚ)
  (φ : BruhatCompactSupport Cℚ).val (ideleClassNormTwist (χ : PontryaginDual Cℚ) z)
local notation "D" => MeromorphicOn.divisor completedRiemannZeta univ
local notation "Z" => {z : ℂ // 0 < D z}
local notation "r(" z ")" => ((D ((z : Z).val)).toNat)
local notation "keep(" a ", " s ", " z ")" =>
  spectralStripMultiplicity a s ((z : Z).val.re - 1 / 2) (r(z))
local notation "band(" ha ")" => (neg_nonpos.mpr ha |>.trans ha)
local notation "Q(" ha ", " hs ")" => spectralSobolevQuotient ℚ (1 / 2) (band(ha)) (zero_lt_one.trans hs).le
local notation "pt(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" ψ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := ℚ) ψ) z
local notation "Y(" χ ", " a ")" => {y : PontryaginDual K × ℝ × ℝ //
  y.2.1 ∈ Icc (-a) a ∧ 0 < order(χ y.1, pt(1 / 2 + y.2.1, y.2.2))}
local notation "N(" χ ", " a ", " s ", " y ")" => spectralStripMultiplicity a s ((y).val.2.1)
  (order(χ (y).val.1, pt(1 / 2 + (y).val.2.1, (y).val.2.2))).untop₀.toNat
local notation "radial(" φ ", " H ")" => ∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x =
  (H : ℝ → ℂ) (Real.log ((ideleClassNorm ℚ x : ℝ≥0) : ℝ))

private theorem radial_principal_order (z : ℂ) :
    (order(X, z)).untop₀ = D z := by
  rw [← divisor_rat_principal_eq_zeta,
    MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec X).1.meromorphicOn (mem_univ _)]

private theorem radial_principal_positive (z : Z) : 0 < order(X, z.val) := by
  have hz := z.property
  rw [← radial_principal_order] at hz
  cases he : order(X, z.val) with
  | top => simp
  | coe n => rw [he, WithTop.untop₀_coe] at hz; exact_mod_cast hz

private theorem radial_M (H : ℝ → ℂ) (hH : Continuous H) (φ : BruhatCompactSupport Cℚ)
    (hφ : radial(φ, H)) (z : ℂ) : M(φ, X, z) = V * bilateralLaplace H z := by
  rw [normTest_mellin H hH φ hφ]
  have h := grh_shift_integral H hH (fun _ ↦ (1 : ℂ)) (fun _ ↦ rfl) 0 z
  simpa [bilateralLaplace] using congrArg (fun c : ℂ ↦ V * c) h

private theorem radial_shift (z : ℂ) : pt(1 / 2 + (z.re - 1 / 2), z.im) = z := by
  apply Complex.ext <;> simp

private theorem radial_offset (z : ℂ) : pt(z.re - 1 / 2, z.im) = z - 1 / 2 := by
  apply Complex.ext <;> simp

private theorem radial_basepoints :
    ∃ χ : PontryaginDual K → PontryaginDual Cℚ, IsSpectralBasepointChoice χ ∧ χ 1 = 1 := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  let ψ (ξ : PontryaginDual K) := if ξ = 1 then 1 else χ ξ
  refine ⟨ψ, fun ξ ↦ ?_, by simp [ψ]⟩
  by_cases hw : ξ = 1
  · subst ξ; simp only [ψ, ite_true]; ext1 u; rfl
  · simpa [ψ, hw] using hχ ξ

private theorem radial_off_row (χ : PontryaginDual K → PontryaginDual Cℚ)
    (hχ : IsSpectralBasepointChoice χ) {ξ : PontryaginDual K} (hw : ξ ≠ 1)
    (H : ℝ → ℂ) (hH : Continuous H) (φ : BruhatCompactSupport Cℚ)
    (hφ : radial(φ, H)) (z : ℂ) : M(φ, χ ξ, z) = 0 := by
  have hn : ¬ ∀ u : K, χ ξ u.val = 1 := by
    intro h
    apply hw
    ext1 u
    exact (congrArg (fun ψ : PontryaginDual K ↦ ψ u) (hχ ξ)).symm.trans (h u)
  rw [normTest_mellin H hH φ hφ, ite_eq_right hn, zero_mul]

/-- Paper: §12.3, p. 514, and (10.3.2.4), p. 454. A physical rational norm
test on the centered strip has only one angular row. Its Hilbert trace counts
the positive divisor of completed Riemann zeta with the strict Sobolev edge cutoff. -/
theorem hasSum_radialStripTrace (H : ℝ → ℂ) (hH : Continuous H) (φ : BruhatCompactSupport Cℚ)
    (hφ : radial(φ, H)) {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s)
    (T : nuclearEndomorphisms Q(ha, hs))
    (hT : T.val = spectralConvolution (F := ℚ) (1 / 2) (band(ha)) (zero_lt_one.trans hs).le φ) :
    HasSum (fun z : Z ↦ V * ((keep(a, s, z) : ℂ) * bilateralLaplace H (z.val - 1 / 2)))
      (hilbertTrace T) := by
  obtain ⟨χ, hχ, hχ₁⟩ := radial_basepoints
  let B := {z : Z // z.val.re - 1 / 2 ∈ Icc (-a) a}
  let Y := Y(χ, a)
  let f (y : Y) := (N(χ, a, s, y) : ℂ) * M(φ, χ y.val.1, pt(y.val.2.1, y.val.2.2))
  let e (z : B) : Y := ⟨(1, z.val.val.re - 1 / 2, z.val.val.im), z.property,
    by rw [hχ₁, radial_shift]; exact radial_principal_positive z.val⟩
  have ei : Injective e := by
    intro z w he
    have hr := congrArg (fun y : Y ↦ y.val.2.1) he
    have hi := congrArg (fun y : Y ↦ y.val.2.2) he
    exact Subtype.ext (Subtype.ext (Complex.ext (sub_left_inj.mp hr) hi))
  have hz (y : Y) (hy : y ∉ range e) : f y = 0 := by
    by_cases hξ : y.val.1 = 1
    · let u := pt(1 / 2 + y.val.2.1, y.val.2.2)
      have hu : 0 < order(X, u) := by simpa only [hξ, hχ₁] using y.property.2
      by_cases hd : 0 < D u
      · let z : Z := ⟨u, hd⟩
        have hr : u.re - 1 / 2 = y.val.2.1 := by simp [u]
        have hi : u.im = y.val.2.2 := by simp [u]
        exact (hy ⟨⟨z, hr ▸ y.property.1⟩, Subtype.ext (Prod.ext hξ.symm (Prod.ext hr hi))⟩).elim
      · have htop : order(X, u) = ⊤ := by
          cases ho : order(X, u) with
          | top => rfl
          | coe n =>
            exfalso
            rw [← radial_principal_order, ho, WithTop.untop₀_coe] at hd
            rw [ho] at hu
            exact hd (by exact_mod_cast hu)
        have hN : N(χ, a, s, y) = 0 := by
          rw [hξ, hχ₁]
          change spectralStripMultiplicity a s _ ((order(X, u)).untop₀.toNat) = 0
          simp [htop, spectralStripMultiplicity, spectralBoundaryMultiplicity]
        simp only [f, hN, Nat.cast_zero, zero_mul]
    · simp only [f, radial_off_row χ hχ hξ H hH φ hφ, mul_zero]
  have hfull : HasSum f (hilbertTrace T) :=
    (spectralStripConvolution_trace (1 / 2) χ hχ ha hs φ T hT).2
  have hsub : HasSum (fun z : B ↦ f (e z)) (hilbertTrace T) := (ei.hasSum_iff hz).mpr hfull
  let p (z : Z) := V * ((keep(a, s, z) : ℂ) * bilateralLaplace H (z.val - 1 / 2))
  have he (z : B) : f (e z) = p z.val := by
    dsimp only [e, f, p]
    rw [hχ₁, radial_shift, radial_offset, radial_principal_order, radial_M H hH φ hφ]
    ring
  apply (Subtype.val_injective (p := fun z : Z ↦ z.val.re - 1 / 2 ∈ Icc (-a) a)).hasSum_iff ?_ |>.mp
  · exact hsub.congr_fun fun z ↦ (he z).symm
  · intro z hz
    have hb : z.val.re - 1 / 2 ∉ Icc (-a) a := fun h ↦ hz ⟨⟨z, h⟩, rfl⟩
    simp [p, spectralStripMultiplicity, mem_Icc] at *
    grind

/-- The prime side of the positive-log rational formula at the spectral center
one half. The two subtracted terms are the actual prime-power samples and the
infinite-place remainder after the pole at zero cancels. -/
def centeredVonMangoldtValue (H : ℝ → ℂ) : ℂ :=
  bilateralLaplace H (1 / 2) -
    (∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * H (Real.log n)) -
    ∫ x in Ioi (0 : ℝ), (Real.exp (-x / 2) : ℂ) * H x / ((Real.exp (2 * x) : ℂ) - 1)

/-- Paper: §12.3, p. 514. The centered positive-log explicit formula with full zeta multiplicities. -/
theorem hasSum_zetaZeros_centeredVonMangoldt (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H)
    (hc : HasCompactSupport H) (hs : tsupport H ⊆ Ioi 0) :
    HasSum (fun z : Z ↦ (r(z) : ℂ) * bilateralLaplace H (z.val - 1 / 2))
      (centeredVonMangoldtValue H) := by
  let G (x : ℝ) := (Real.exp (-x / 2) : ℂ) * H x
  have hG : ContDiff ℝ (∞) G := (Complex.ofRealCLM.contDiff.comp (by fun_prop :
    ContDiff ℝ (∞) (fun x : ℝ ↦ Real.exp (-x / 2)))).mul hH
  have hcG : HasCompactSupport G := hc.mul_left
  have hsG : tsupport G ⊆ Ioi 0 := tsupport_mul_subset_right.trans hs
  have h := hasSum_zetaZeros_positiveLog G hG hcG hsG
  have hM (z : ℂ) : bilateralLaplace G z = bilateralLaplace H (z - 1 / 2) := by
    unfold bilateralLaplace
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [G, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
    calc
      _ = H x * (Complex.exp (-(x : ℂ) / 2) * Complex.exp (z * x)) := by ring
      _ = _ := by rw [← Complex.exp_add]; congr 2; ring
  have hp (n : ℕ) : (Λ n : ℂ) * G (Real.log n) = ((Λ n / Real.sqrt n : ℝ) : ℂ) * H (Real.log n) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have he : Real.exp (-Real.log n / 2) = (Real.sqrt n)⁻¹ := by
        rw [neg_div, Real.exp_neg, Real.exp_half, Real.exp_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
      dsimp only [G]
      rw [he, Complex.ofReal_div, Complex.ofReal_inv, div_eq_mul_inv, mul_assoc]
  simp_rw [hM, hp] at h
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at h
  apply h.congr_fun
  intro z
  rw [show ((D z.val).toNat : ℂ) = (D z.val : ℂ) by exact_mod_cast Int.toNat_of_nonneg z.property.le]

/-- Paper: §12.3, p. 514, as used on pp. 519–520. For every positive-log
rational radial test, the signed difference between the explicit prime side
and the genuine nuclear quotient trace is exactly the absolutely convergent
sum of the lost Mellin samples, with the partially retained boundary orders.
The normalization is the Tamagawa volume of the norm-one classes. -/
theorem hasSum_centeredVonMangoldt_sub_radialStripTrace (H : ℝ → ℂ)
    (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, H)) {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s)
    (T : nuclearEndomorphisms Q(ha, hs))
    (hT : T.val = spectralConvolution (F := ℚ) (1 / 2) (band(ha)) (zero_lt_one.trans hs).le φ) :
    HasSum (fun z : Z ↦ V * (((r(z) - keep(a, s, z) : ℕ) : ℂ) * bilateralLaplace H (z.val - 1 / 2)))
      (V * centeredVonMangoldtValue H - hilbertTrace T) := by
  have hF := (hasSum_zetaZeros_centeredVonMangoldt H hH hc hp).mul_left V
  have hR := hasSum_radialStripTrace H hH.continuous φ hφ ha hs T hT
  apply (hF.sub hR).congr_fun
  intro z
  have hm : keep(a, s, z) ≤ r(z) := by
    unfold spectralStripMultiplicity
    split
    · exact le_rfl
    split
    · exact min_le_left _ _
    · exact Nat.zero_le _
  rw [Nat.cast_sub hm]
  ring

/-- Every positive divisor site of completed zeta is strictly inside the critical strip. -/
theorem completedZetaZero_mem_centeredCriticalStrip (z : Z) : |z.val.re - 1 / 2| < (1 / 2 : ℝ) := by
  obtain ⟨hL, ha⟩ := continuedCompletedHeckeL_spec X
  have upper (w : ℂ) (hw : 0 < order(X, w)) : w.re < 1 := by
    rcases le_or_gt w.re 0 with h | h
    · exact h.trans_lt zero_lt_one
    · exact completedHeckeL_continuation_zeros X _ hL ha h hw
  have hp := radial_principal_positive z
  have hu := upper z.val hp
  obtain ⟨ε, hε, hn, he⟩ := completedHeckeL_continuation_functionalEquation X _ _ hL ha hL
    (by simpa using ha)
  let refl (w : ℂ) := 1 - w
  have hr := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL X)
    (show AnalyticAt ℂ refl z.val by dsimp [refl]; fun_prop)
    (show deriv refl z.val ≠ 0 by simp [refl])
  rw [show continuedCompletedHeckeL X ∘ refl = ε * continuedCompletedHeckeL X from funext he,
    meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt _) (hn _)] at hr
  have hl := upper (1 - z.val) (hr ▸ hp)
  rw [Complex.sub_re, Complex.one_re] at hl
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

local notation "χS(" τ ")" => {χ : PontryaginDual Cℚ // ∀ t : ℝ≥0ˣ, χ (τ t) = 1}
local notation "sites(" τ ")" => {z : χS(τ) × ℂ //
  0 < MeromorphicOn.divisor (continuedCompletedHeckeL z.1.val) univ z.2 ∧ |z.2.re - 1 / 2| < (1 / 2 : ℝ)}
local notation "term(" φ ", " z ")" => ((MeromorphicOn.divisor (continuedCompletedHeckeL (z).val.1.val)
  univ (z).val.2 : ℤ) : ℂ) * M(φ, (z).val.1.val, (z).val.2 - 1 / 2)

private theorem radial_full_chart (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H)
    (hp : tsupport H ⊆ Ioi 0) (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, H))
    (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ)) :
    HasSum (fun z : sites(τ) ↦ term(φ, z)) (V * centeredVonMangoldtValue H) := by
  let Y := sites(τ)
  let e (z : Z) : Y := ⟨(⟨1, by simp⟩, z.val),
    by rw [divisor_rat_principal_eq_zeta]; exact z.property, completedZetaZero_mem_centeredCriticalStrip z⟩
  have ei : Injective e := fun _ _ h ↦ Subtype.ext (congrArg (fun y : Y ↦ y.val.2) h)
  apply (ei.hasSum_iff ?_).mp
  · apply ((hasSum_zetaZeros_centeredVonMangoldt H hH hc hp).mul_left V).congr_fun
    intro z
    change (MeromorphicOn.divisor (continuedCompletedHeckeL X) univ z.val : ℂ) *
        M(φ, X, z.val - 1 / 2) = _
    rw [divisor_rat_principal_eq_zeta, radial_M H hH.continuous φ hφ,
      show (r(z) : ℂ) = (D z.val : ℂ) by exact_mod_cast Int.toNat_of_nonneg z.property.le]
    ring
  · intro y hy
    let ψ := y.val.1.val
    have hn : ¬ ∀ u : K, ψ u.val = 1 := by
      intro hu
      have hψ : ψ = 1 := by
        ext1 g
        let v := τ (ideleClassNorm ℚ g)
        have hk : g / v ∈ K := by change ideleClassNorm ℚ (g / v) = 1; rw [map_div, hτ _, div_self']
        have h := hu ⟨g / v, hk⟩
        have hv : ψ v = 1 := y.val.1.property _
        change ψ g = 1
        simpa only [map_div, hv, div_one] using h
      have hd := y.property.1
      change 0 < MeromorphicOn.divisor (continuedCompletedHeckeL ψ) univ y.val.2 at hd
      rw [hψ, divisor_rat_principal_eq_zeta] at hd
      exact hy ⟨⟨y.val.2, hd⟩, Subtype.ext (Prod.ext (Subtype.ext hψ.symm) rfl)⟩
    change _ * M(φ, ψ, _) = 0
    rw [normTest_mellin H hH.continuous φ hφ, ite_eq_right hn, zero_mul, mul_zero]

/-- The full positive-divisor trace for a rational radial test equals its centered von Mangoldt value. -/
theorem hasSum_rationalNormTest_fullTrace (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H)
    (hp : tsupport H ⊆ Ioi 0) (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, H))
    (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ)) :
    HasSum (fun z : sites(τ) ↦ term(φ, z)) (V * centeredVonMangoldtValue H) :=
  radial_full_chart H hH hc hp φ hφ τ hτ

section SharpMass

attribute [local instance] instFiniteCompletionUnitsLocallyCompactSec4b
  instSIdeleQuotientMeasurableSpaceSec1 instNormOneSIdeleQuotientMeasurableSpaceSec1
  instSIdeleLocallyCompactSec1 instSIdeleT2Sec4

local notation "Pl" => IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)
variable {S : Finset Pl}
local notation "Iₛ" => (SAdeleRing ℚ S)ˣ
local notation "Hₛ" => sProjectedDiagonal ℚ S
local notation "μₛ" => sMultiplicativeTamagawaMeasure ℚ S
local notation "volS" => (((sLocalNormOneQuotientMeasure ℚ S) univ).toReal : ℂ)
local notation "rootS(" g ")" => (Real.sqrt (((sIdeleNorm ℚ S g).val : ℝ)) : ℂ)
local notation "classAtS(" g ")" => (QuotientGroup.mk (sIdeleInsertion ℚ S g) : Cℚ)
local notation "normR(" g ")" => (((ideleClassNorm ℚ g).val : ℝ))
local notation "finPV(" v "," b ")" =>
  ((Real.log ((v : Pl).asIdeal.absNorm : ℝ) /
    ((finiteLocalMultiplicativeTamagawaMeasure ℚ v)
      (((v : Pl).adicCompletionIntegers ℚ).units : Set _)).toReal : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v 1 b
local notation "archPV(" A ")" => (∑ w : InfinitePlace ℚ, infiniteConnesWeilPrincipalValue w (A w))
local notation "P(" f ")" => ((∫ g : Iₛ, (f : BruhatCompactSupport Iₛ).val g * rootS(g) ∂μₛ) +
  ∫ g : Iₛ, (f : BruhatCompactSupport Iₛ).val g / rootS(g) ∂μₛ)
/-- Sharp rational orbital mass with both local polar moments subtracted and
with the ratio of global and local norm-one volumes. -/
def rationalCorrectedSharpMass (f : BruhatCompactSupport Iₛ) (R : ℝ) : ℂ :=
  V / volS * ((∑' ξ : Hₛ, sLocalTraceSharpMass f ξ R) - P(f))

private theorem radial_pic (S : Finset Pl) : Subsingleton (CommRing.Pic ((S : Set Pl).integer ℚ)) := by
  have : IsPrincipalIdealRing (𝓞 ℚ) := classNumber_eq_one_iff.mp Rat.classNumber_eq
  have h := picMapAlgebra_surjective_of_isLocalization (Localization.submonoid (S : Set Pl))
    (R := 𝓞 ℚ) (A := (S : Set Pl).integer ℚ)
  exact h.subsingleton

/-- The rational S-integer class group is trivial for every finite level. -/
theorem subsingleton_rational_sInteger_pic (S : Finset Pl) : Subsingleton (CommRing.Pic ((S : Set Pl).integer ℚ)) :=
  radial_pic S

private theorem radial_outside (H : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, H))
    (u : outsideIntegralIdeleUnits ℚ S) (g : Cℚ) : φ.val (QuotientGroup.mk u.val * g) = φ.val g := by
  obtain ⟨harch, hS, hout⟩ := (mem_outsideIntegralIdeleUnits_iff u.val).mp u.property
  have hf (v : Pl) : ‖u.val.val.2 v‖ = 1 := by
    by_cases hv : v ∈ S
    · rw [hS v hv, norm_one]
    · let ev := (RestrictedProduct.evalRingHom (fun w : Pl ↦ w.adicCompletion ℚ) v).comp
        (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      apply Valued.toNormedField.norm_eq_one_iff.mpr
      exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
        (a := Units.map ev.toMonoidHom u.val)).mp (hout v hv)
  have hn : ideleNorm ℚ u.val = 1 := by
    apply Units.ext
    apply NNReal.coe_injective
    rw [((ideleNorm_spec ℚ).1 u.val).2, harch, finprod_eq_one_of_forall_eq_one hf]
    simp
    exact norm_one
  rw [hφ, hφ, map_mul]
  change H (Real.log ((((ideleNorm ℚ u.val * ideleClassNorm ℚ g).val : ℝ≥0) : ℝ))) = _
  rw [hn, one_mul]

/-- A rational radial test is invariant under integral units outside any finite level. -/
theorem rationalNormTest_outside_invariant (H : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, H))
    (u : outsideIntegralIdeleUnits ℚ S) (g : Cℚ) : φ.val (QuotientGroup.mk u.val * g) = φ.val g :=
  radial_outside H φ hφ u g

/-- Paper: §12.3, p. 514, and (12.4.1.25)–(12.4.1.28), p. 519. For a positive-log
rational norm test, the negative of the polar-corrected sharp orbital mass tends to
the centered von Mangoldt sum, with the actual norm-one Tamagawa normalization.
This local computation requires no projective kernel or wide-strip nuclear witness. -/
theorem sLocalTraceSharpMass_tendsto_centeredVonMangoldt
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, H))
    (hRam : ∀ v : Pl, differentIdeal ℤ (𝓞 ℚ) ≤ v.asIdeal → v ∈ S)
    {B : ℝ} (hB : ∀ g ∈ tsupport φ.val, normR(g) < B ∧ (normR(g))⁻¹ < B)
    (hS : ∀ v : Pl, v ∉ S → B ≤ (v.asIdeal.absNorm : ℝ))
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g)))) :
    Tendsto (fun R : ℝ ↦ -rationalCorrectedSharpMass f R) atTop (𝓝 (V * centeredVonMangoldtValue H)) := by
  have hPic := radial_pic S
  have hOutside := radial_outside (S := S) H φ hφ
  have h0 : H 0 = 0 := by
    by_contra hn
    exact (lt_irrefl (0 : ℝ)) (hp (subset_tsupport _ hn))
  have hker (u : K) : φ.val u.val = 0 := by rw [hφ, u.property]; simpa using h0
  have hφ₁ : φ.val 1 = 0 := hker 1
  let π : IdeleGroup (𝓞 ℚ) ℚ →ₜ* Cℚ := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ := π.comp ⟨canonicalIdeleNormSection ℚ, canonicalIdeleNormSection_continuous ℚ⟩
  have hτ : RightInverse τ (ideleClassNorm ℚ) := canonicalIdeleNormSection_rightInverse ℚ
  obtain ⟨A, b, hA, hb, _, hZ⟩ := traceFormula_of_half_le τ hτ φ (le_refl (1 / 2 : ℝ))
  have hz := hZ.unique (radial_full_chart H hH hc hp φ hφ τ hτ)
  obtain ⟨A', b', J, hA', hb', hJ, hj⟩ := sLocalTraceSharpMass_asymptotic φ hPic hRam hOutside f hLift
  have hArch : A' = A := funext (fun w ↦ Subtype.ext (funext (fun u ↦ (hA' w u).trans (hA w u).symm)))
  subst A'
  have hFinite : ∑' v : Pl, finPV(v, b v) = ∑ v : S, finPV(v.val, b' v) := by
    rw [tsum_eq_sum (s := S) (fun v hv ↦ ?_), ← Finset.sum_coe_sort]
    · exact Finset.sum_congr rfl fun v _ ↦ by
        rw [show b v.val = b' v from Subtype.ext (funext (fun u ↦ (hb _ u).trans (hb' v u).symm))]
    · have hb0 : b v = 0 := Subtype.ext (funext (fun u ↦ (hb v u).trans
          (traceComparison_finiteRestriction_eq_zero φ hker v hB (hS v hv) u)))
      simp [hb0]
  rw [hFinite] at hz
  have hPol : V * P(f) = volS * (M(φ, X, 1 / 2) + M(φ, X, -1 / 2)) :=
    sLocalTraceLift_global_polar_sum hPic φ hOutside f hLift
  have hvol : (volS : ℂ) ≠ 0 := by
    let G := (sIdeleQuotientNorm ℚ S).ker
    let : CompactSpace G := isCompact_iff_compactSpace.mp
      ((isProperMap_sIdeleQuotientNorm ℚ S).isCompact_preimage (isCompact_singleton (x := 1)))
    let μ := sLocalNormOneQuotientMeasure ℚ S
    have : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := S)).1
    exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr
      ⟨isOpen_univ.measure_ne_zero μ univ_nonempty, measure_ne_top μ univ⟩)
  have he : -(V / volS * (volS * (archPV(A) + ∑ v : S, finPV(v.val, b' v)) - P(f))) =
      V * centeredVonMangoldtValue H := by
    field_simp [hvol]
    linear_combination hPol + volS * hz
  simp only [hφ₁, mul_zero, zero_mul, sub_zero] at hj
  have hsharp := hj.congr' (hJ.mono fun R h ↦ h.tsum_eq.symm)
  exact he ▸ ((hsharp.sub_const P(f)).const_mul (V / volS)).neg


private theorem radial_level (B : ℝ) :
    ∃ S : Finset Pl, (∀ v : Pl, differentIdeal ℤ (𝓞 ℚ) ≤ v.asIdeal → v ∈ S) ∧
      ∀ v : Pl, v ∉ S → B ≤ (v.asIdeal.absNorm : ℝ) := by
  let A := (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le (S := 𝓞 ℚ) ⌈B⌉₊).toFinset
  let J := (Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 ℚ))).toFinset
  let S := A ∪ J
  have hRam (v : Pl) (hv : differentIdeal ℤ (𝓞 ℚ) ≤ v.asIdeal) : v ∈ S :=
    Finset.mem_union_right _ (by simpa [J] using Ideal.dvd_iff_le.mpr hv)
  have hS (v : Pl) (hv : v ∉ S) : B ≤ (v.asIdeal.absNorm : ℝ) := by
    by_contra! h
    apply hv
    have hle : v.asIdeal.absNorm ≤ ⌈B⌉₊ := by exact_mod_cast h.le.trans (Nat.le_ceil B)
    exact Finset.mem_union_left _ (by simpa [A] using hle)
  exact ⟨S, hRam, hS⟩

private theorem radial_norm_bounds {l u : ℝ} (H : ℝ → ℂ) (hJ : tsupport H ⊆ Icc l u)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, H)) (g : Cℚ) (hg : g ∈ tsupport φ.val) :
    normR(g) < max (Real.exp u) (Real.exp (-l)) + 1 ∧
      (normR(g))⁻¹ < max (Real.exp u) (Real.exp (-l)) + 1 := by
  let n (x : Cℚ) := normR(x)
  have hn : Continuous n :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm ℚ).continuous)
  have hpos (x : Cℚ) : 0 < n x := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hlog := hn.log (fun x ↦ (hpos x).ne')
  have he : φ.val = H ∘ (fun x : Cℚ ↦ Real.log (n x)) := funext hφ
  rw [he] at hg
  have hj := hJ (tsupport_comp_subset_preimage H hlog hg)
  have hu : n g ≤ Real.exp u := (Real.log_le_iff_le_exp (hpos g)).mp hj.2
  have hl : (n g)⁻¹ ≤ Real.exp (-l) := by
    rw [← Real.exp_log (hpos g), ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (neg_le_neg hj.1)
  exact ⟨lt_of_le_of_lt (hu.trans (le_max_left _ _)) (lt_add_one _),
    lt_of_le_of_lt (hl.trans (le_max_right _ _)) (lt_add_one _)⟩

/-- Paper: §12.3, p. 514. One finite set of places works for every positive-log
profile in the prescribed log-norm interval. Each profile has a global Bruhat
test and an actual finite-place lift. At every strip width and Sobolev order the
negative corrected sharp mass minus the nuclear quotient trace tends to the signed
sum over omitted zeta jets. -/
theorem exists_radialSharpMass_stripTrace_comparison (l u : ℝ) :
    ∃ S : Finset Pl, ∀ (H : ℝ → ℂ), ContDiff ℝ (∞) H → HasCompactSupport H →
      tsupport H ⊆ Ioi 0 → tsupport H ⊆ Icc l u →
      ∃ (φ : BruhatCompactSupport Cℚ) (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ),
      radial(φ, H) ∧
      (∀ g : (SAdeleRing ℚ S)ˣ, HasSum (fun ξ : sProjectedDiagonal ℚ S ↦ f.val (ξ.val * g))
        (φ.val (QuotientGroup.mk (sIdeleInsertion ℚ S g)))) ∧
      Tendsto (fun R : ℝ ↦ -rationalCorrectedSharpMass f R) atTop (𝓝 (V * centeredVonMangoldtValue H)) ∧
      ∀ {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s) (T : nuclearEndomorphisms Q(ha, hs)),
        T.val = spectralConvolution (F := ℚ) (1 / 2) (band(ha)) (zero_lt_one.trans hs).le φ →
          Tendsto (fun R : ℝ ↦ -rationalCorrectedSharpMass f R - hilbertTrace T) atTop
            (𝓝 (∑' z : Z, V * (((r(z) - keep(a, s, z) : ℕ) : ℂ) * bilateralLaplace H (z.val - 1 / 2)))) := by
  obtain ⟨S, hRam, hS⟩ := radial_level (max (Real.exp u) (Real.exp (-l)) + 1)
  refine ⟨S, ?_⟩
  intro H hH hc hp hJ
  apply (exists_normTest (F := ℚ) H hH hc).elim
  intro φ hφ
  have hB := radial_norm_bounds H hJ φ hφ
  apply (exists_sLocalTraceLift (radial_pic S) φ (radial_outside H φ hφ)).elim
  intro f hf
  have hlim := sLocalTraceSharpMass_tendsto_centeredVonMangoldt H hH hc hp φ hφ hRam hB hS f hf
  refine ⟨φ, f, hφ, hf, hlim, ?_⟩
  intro a s ha hs T hT
  rw [(hasSum_centeredVonMangoldt_sub_radialStripTrace H hH hc hp φ hφ ha hs T hT).tsum_eq]
  exact hlim.sub_const (hilbertTrace T)

end SharpMass
end RiemannMasullo
