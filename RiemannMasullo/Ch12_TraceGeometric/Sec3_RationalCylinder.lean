module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_RationalCongruence
public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.PrimitiveFourier
public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
import Mathlib.Tactic

/-! # Genuine Bruhat angular cylinders and their complete Mellin transforms -/

@[expose] public noncomputable section
open NumberFieldKB.Chebotarev.RatIdele NumberField
open Filter Function MeasureTheory Set
open scoped ComplexConjugate ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.ConductorCylinder

set_option quotPrecheck false

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "K" => MonoidHom.ker (ideleClassNorm ℚ)
local notation "ν" => normOneIdeleClassTamagawaMeasure ℚ
local notation "V" => ((normOneIdeleClassTamagawaMeasure ℚ).real univ : ℂ)
local notation "mℚ" => (continuousIdeleClassNorm ℚ : Cℚ →ₜ* ℝ≥0ˣ)
local notation "hmℚ" => (⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩ : IsModulation mℚ)
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "logN(" g ")" => Real.log ((ideleClassNorm ℚ g : ℝ≥0) : ℝ)

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

private local instance : CompactSpace K := (ideleClassGroup_finiteness ℚ).2.1
private local instance : (ν).IsHaarMeasure :=
  (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1

private theorem V_ne_zero : V ≠ 0 := Complex.ofReal_ne_zero.mpr measureReal_univ_pos.ne'

/-- The single normalized congruence cylinder times a smooth radial profile is an actual
compactly supported Bruhat test on the rational idele class group. -/
theorem exists_normalized_cylinder_test (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (H : ℝ → ℂ)
    (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) :
    ∃ φ : BruhatCompactSupport Cℚ, ∀ x : Cℚ,
      φ.val x = if classResidue q x = r then V⁻¹ * H logN(x) else 0 := by
  classical
  let A : ℂ := (q.totient : ℂ)⁻¹ * V⁻¹
  let G := fun y : ℝ ↦ A * H y
  have hG : ContDiff ℝ (∞) G := contDiff_const.mul hH
  have hGc : HasCompactSupport G := hc.mul_left
  choose ψ _hfin hψ _hL _ho _hcoeff using (exists_primitive_row q)
  choose φ hφ using fun χ : DirichletCharacter ℂ q ↦ exists_characterNormTest (ψ χ) G hG hGc
  let ev (x : Cℚ) : BruhatCompactSupport Cℚ →ₗ[ℂ] ℂ :=
    { toFun := fun b ↦ b.val x, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  refine ⟨∑ χ : DirichletCharacter ℂ q, χ r.val • φ χ, fun x ↦ ?_⟩
  change ev x _ = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  have hterm (χ : DirichletCharacter ℂ q) :
      χ r.val * ev x (φ χ) = (χ ((classResidue q x).val)⁻¹ * χ r.val) * G logN(x) := by
    change χ r.val * (φ χ).val x = _
    rw [hφ, hψ, ratDirichletChar_eq_conj, RationalConductor.conj_apply_unit]
    ring
  simp only [hterm, ← Finset.sum_mul, DirichletCharacter.sum_char_inv_mul_char_eq ℂ
    (classResidue q x).isUnit]
  have hq : (q.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  by_cases hz : classResidue q x = r
  · simp [hz, G, A, hq, ← mul_assoc]
  · have hz' : (classResidue q x).val ≠ r.val := fun h ↦ hz (Units.ext h)
    simp [hz, hz']


/-- For the actual single test, the primitive row Mellin transform is the one-coset
coefficient times the radial bilateral Laplace transform at every complex parameter. -/
theorem normalized_cylinder_mellin (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (H : ℝ → ℂ)
    (hH : Continuous H) (φ : BruhatCompactSupport Cℚ)
    (hφ : ∀ x : Cℚ, φ.val x = if classResidue q x = r then V⁻¹ * H logN(x) else 0)
    (χ : DirichletCharacter ℂ q) (ψ : PontryaginDual Cℚ)
    (hψ : ∀ x : Cℚ, (ψ x : ℂ) = ((ratDirichletChar q χ x : ℂˣ) : ℂ)) (z : ℂ) :
    modulatedFourierMellin mℚ univ hmℚ μℚ φ.val (ideleClassNormTwist ψ z) =
      (conj (χ (r : ZMod q)) / (q.totient : ℂ)) * bilateralLaplace H z := by
  classical
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let σ := (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ)).comp ratIdeleNormSection
  have hσ : Continuous σ := continuous_quotient_mk'.comp ratIdeleNormSection_continuous
  have hr : RightInverse σ (ideleClassNorm ℚ) := ratIdeleNormSection_class_rightInverse
  let j := fun p : ℝ≥0ˣ × K ↦ σ p.1 * p.2.val
  have hj : Continuous j := (hσ.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  let radial (t : ℝ≥0ˣ) := H (Real.log ((t : ℝ≥0) : ℝ)) * (((t : ℝ≥0) : ℝ) : ℂ) ^ z
  let angular (u : K) := (cylinder q r).indicator (fun k : K ↦ ((ratDirichletChar q χ k.val : ℂˣ) : ℂ)) u / V
  have hp (p : ℝ≥0ˣ × K) : φ.val (j p) * ideleClassNormTwist ψ z (j p) =
      radial p.1 * angular p.2 := by
    have hx : classResidue q (j p) = angularResidue q p.2 := by
      change classResidue q (σ p.1 * p.2.val) = _
      rw [map_mul, classResidue_on_section, one_mul]
      rfl
    have hn : ideleClassNorm ℚ (j p) = p.1 := by
      change ideleClassNorm ℚ (σ p.1 * p.2.val) = _
      rw [map_mul, hr, show ideleClassNorm ℚ p.2.val = 1 from p.2.property, mul_one]
    have hv : (ψ (j p) : ℂ) = ((ratDirichletChar q χ p.2.val : ℂˣ) : ℂ) := by
      rw [hψ, ratDirichletChar_eq_conj, ratDirichletChar_eq_conj, hx]
      rfl
    change φ.val (j p) * ((ψ (j p) : ℂ) * (((ideleClassNorm ℚ (j p) : ℝ≥0) : ℝ) : ℂ) ^ z) = _
    rw [hφ, hx, hn, hv]
    by_cases he : angularResidue q p.2 = r
    · have hin : p.2 ∈ cylinder q r := he
      simp only [he, ite_true, angular, indicator_of_mem hin, radial, div_eq_mul_inv]
      ring
    · have hout : p.2 ∉ cylinder q r := he
      simp [he, angular, hout]
  have hrad : (∫ t, radial t ∂positiveRealHaar) = bilateralLaplace H z := by
    simpa only [radial, bilateralLaplace, sub_zero, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] using
      grh_shift_integral H hH (fun _ ↦ (1 : ℂ)) (fun _ ↦ rfl) 0 z
  have hang : (∫ u, angular u ∂ν) = conj (χ (r : ZMod q)) / (q.totient : ℂ) := by
    rw [show (∫ u, angular u ∂ν) =
        (∫ u, (cylinder q r).indicator (fun k : K ↦ ((ratDirichletChar q χ k.val : ℂˣ) : ℂ)) u ∂ν) / V
        from integral_div _ _, integral_indicator (isClopen_cylinder q r).isClosed.measurableSet]
    exact cylinder_dirichlet_integral q r χ
  have hφc := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hcont : Continuous (fun x : Cℚ ↦ φ.val x * ideleClassNormTwist ψ z x) :=
    hφc.mul (map_continuous (ideleClassNormTwist ψ z))
  simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
  trans (∫ p, φ.val (j p) * ideleClassNormTwist ψ z (j p) ∂positiveRealHaar.prod ν)
  · rw [← classTamagawa_normProduct σ hσ hr]
    exact integral_map hj.measurable.aemeasurable hcont.aestronglyMeasurable
  simp only [hp, integral_prod_mul, hrad, hang, mul_comm]


/-- The genuine cylinder test has zero Mellin transform on every angular row nontrivial
on the congruence kernel, at every complex Mellin argument. -/
theorem normalized_cylinder_mellin_eq_zero (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (H : ℝ → ℂ)
    (φ : BruhatCompactSupport Cℚ)
    (hφ : ∀ x : Cℚ, φ.val x = if classResidue q x = r then V⁻¹ * H logN(x) else 0)
    (ψ : PontryaginDual Cℚ) (hne : ∃ u : K, angularResidue q u = 1 ∧ ψ u.val ≠ 1) (z : ℂ) :
    modulatedFourierMellin mℚ univ hmℚ μℚ φ.val (ideleClassNormTwist ψ z) = 0 := by
  obtain ⟨u, hu, hψ⟩ := hne
  let f := fun x : Cℚ ↦ φ.val x * ideleClassNormTwist ψ z x
  have htr (x : Cℚ) : f (u.val * x) = (ψ u.val : ℂ) * f x := by
    have hu' : classResidue q u.val = 1 := hu
    have hn : ideleClassNorm ℚ u.val = 1 := u.property
    have htest : φ.val (u.val * x) = φ.val x := by
      rw [hφ, hφ, map_mul, hu', one_mul, map_mul, hn, one_mul]
    have htw : ideleClassNormTwist ψ z u.val = (ψ u.val : ℂ) := by
      change (ψ u.val : ℂ) * (((ideleClassNorm ℚ u.val : ℝ≥0) : ℝ) : ℂ) ^ z = _
      simp [hn]
    simp only [f, htest, map_mul, htw]
    ring
  let : (μℚ).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil ℚ).1
  have hi := integral_mul_left_eq_self (μ := ideleClassTamagawaMeasure ℚ) f u.val
  simp only [htr, integral_const_mul] at hi
  have h' : (ψ u.val : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr fun h ↦ hψ (Circle.ext h)
  have hzero : ((ψ u.val : ℂ) - 1) * ∫ x, f x ∂μℚ = 0 := by rw [sub_mul, one_mul, hi, sub_self]
  simpa only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ] using
    (mul_eq_zero.mp hzero).resolve_left h'

end RiemannMasullo.ConductorCylinder
