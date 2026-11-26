module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_RationalCylinderLimits
public import RiemannMasullo.Ch12_TraceGeometric.Sec3_RationalConductorSelector
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.Tactic

/-! # A physical test for finitely many primitive rational characters -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set NumberFieldKB.Chebotarev.RatIdele
open scoped ComplexConjugate ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.ConductorSelector

open ConductorCylinder Classical
set_option quotPrecheck false

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "K" => (ideleClassNorm ℚ).ker
local notation "ν" => normOneIdeleClassTamagawaMeasure ℚ
local notation "V" => ((ν).real univ : ℂ)
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "mℚ" => (continuousIdeleClassNorm ℚ : Cℚ →ₜ* ℝ≥0ˣ)
local notation "hmℚ" => (⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩ : IsModulation mℚ)
local notation "ord(" ψ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL ψ) univ z
local notation "M(" φ ", " ψ ", " z ")" =>
  modulatedFourierMellin mℚ univ hmℚ μℚ (φ : BruhatCompactSupport Cℚ).val (ideleClassNormTwist ψ z)
local notation "logN(" g ")" => Real.log ((ideleClassNorm ℚ g : ℝ≥0) : ℝ)

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

private theorem lift_injective (N : ℕ) [NeZero N] :
    Injective (packetRow (q := N)) := by
  intro χ ξ h
  apply angular_lift_injective N
  funext u
  change ((ratDirichletChar N χ u.val : ℂˣ) : ℂ) = ((ratDirichletChar N ξ u.val : ℂˣ) : ℂ)
  exact (packetRow_value χ u.val).symm.trans ((congrArg (fun ψ : PontryaginDual Cℚ ↦ (ψ u.val : ℂ)) h).trans
    (packetRow_value ξ u.val))

private theorem lift_changeLevel {d n : ℕ} [NeZero d] [NeZero n] (h : d ∣ n)
    (χ : DirichletCharacter ℂ d) : packetRow (χ.changeLevel h) = packetRow χ := by
  apply ContinuousMonoidHom.ext
  intro g
  apply Circle.ext
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  refine (packetRow_value (χ.changeLevel h) _).trans ((Eq.trans ?_ (packetRow_value χ _).symm))
  rw [ratDirichletChar_mk, ratDirichletChar_mk, ideleChar_changeLevel h]

/-- The finite-order idelic row associated with the primitive character. -/
def primitiveRow {Q : ℕ} (i : PrimitiveRow Q) : PontryaginDual Cℚ :=
  haveI : NeZero i.1.val := ⟨(Finset.mem_Ioc.mp i.1.property).1.ne'⟩
  packetRow i.2.val

theorem primitiveRow_injective (Q : ℕ) : Injective (primitiveRow (Q := Q)) := by
  rintro ⟨⟨d, hd⟩, ⟨χ, hχ⟩⟩ ⟨⟨n, hn⟩, ⟨ξ, hξ⟩⟩ h
  have : NeZero d := ⟨(Finset.mem_Ioc.mp hd).1.ne'⟩
  have : NeZero n := ⟨(Finset.mem_Ioc.mp hn).1.ne'⟩
  let L := Q.factorial
  have : NeZero L := ⟨Nat.factorial_ne_zero _⟩
  have hdL : d ∣ L := Nat.dvd_factorial (Finset.mem_Ioc.mp hd).1 (Finset.mem_Ioc.mp hd).2
  have hnL : n ∣ L := Nat.dvd_factorial (Finset.mem_Ioc.mp hn).1 (Finset.mem_Ioc.mp hn).2
  have he : χ.changeLevel hdL = ξ.changeLevel hnL := lift_injective L (by
    rw [lift_changeLevel, lift_changeLevel]; exact h)
  have hdn : d = n := by
    simpa only [DirichletCharacter.conductor_changeLevel, show χ.conductor = d from hχ,
      show ξ.conductor = n from hξ] using congrArg DirichletCharacter.conductor he
  subst n
  have hχξ : χ = ξ := DirichletCharacter.changeLevel_injective hdL he
  subst ξ
  rfl

/-- The ordinary Dirichlet multiplicity at the primitive character's own conductor. -/
def primitiveOrder {Q : ℕ} (i : PrimitiveRow Q) (ρ : ℂ) : ℕ :=
  haveI : NeZero i.1.val := ⟨(Finset.mem_Ioc.mp i.1.property).1.ne'⟩
  (meromorphicOrderAt (DirichletCharacter.LFunction i.2.val) ρ).untop₀.toNat

/-- On the open critical strip the idelic multiplicity of a selected row is the actual
order of its ordinary Dirichlet L-function at its own primitive conductor. -/
theorem primitiveRow_divisor_eq_dirichlet {Q : ℕ} (i : PrimitiveRow Q)
    (z : {z : ℂ // 0 < z.re ∧ z.re < 1}) :
    (ord(primitiveRow i, z.val)).toNat = primitiveOrder i z.val := by
  have : NeZero i.1.val := ⟨(Finset.mem_Ioc.mp i.1.property).1.ne'⟩
  exact (packetRow_divisor_eq i.2.val z).trans
    (ConductorDensity.ordinaryOrder_eq_completedPrimitiveOrder (i.2.val, z)).symm

/-- An arithmetic character is normalized on every positive-real norm section. -/
theorem primitiveRow_on_section {Q : ℕ} (i : PrimitiveRow Q) (τ : ℝ≥0ˣ →* Cℚ) (t : ℝ≥0ˣ) :
    primitiveRow i (τ t) = 1 := by
  have : NeZero i.1.val := ⟨(Finset.mem_Ioc.mp i.1.property).1.ne'⟩
  apply Circle.ext
  exact (packetRow_value i.2.val (τ t)).trans (arithmetic_row_on_section _ i.2.val τ t)

private theorem restricted_eq {τ : ℝ≥0ˣ →ₜ* Cℚ} (hτ : RightInverse τ (ideleClassNorm ℚ))
    {ψ η : PontryaginDual Cℚ} (hψ : ∀ t, ψ (τ t) = 1) (hη : ∀ t, η (τ t) = 1)
    (h : ∀ u : K, (ψ * η⁻¹) u.val = 1) : ψ = η := by
  apply ContinuousMonoidHom.ext
  intro x
  change ψ x = η x
  let t := ideleClassNorm ℚ x
  let u : K := ⟨x / τ t, by change ideleClassNorm ℚ (x / τ t) = 1; rw [map_div, hτ]; change t / t = 1; simp⟩
  have he : ψ u.val = η u.val := mul_inv_eq_one.mp (h u)
  simpa only [u, map_div, hψ, hη, div_one] using he

/-- With the project Tamagawa convention the norm-one rational idele classes have mass one. -/
theorem rational_normOne_volume : (normOneIdeleClassTamagawaMeasure ℚ).real univ = 1 := by
  classical
  have hr := InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ)
  have hc := InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ)
  have ht : NumberField.Units.torsionOrder ℚ = 2 :=
    NumberField.Units.torsionOrder_eq_two_of_odd_finrank (by simp)
  have hreg : NumberField.Units.regulator ℚ = 1 := by
    let : DecidableEq (InfinitePlace ℚ) := fun a b ↦ Classical.propDecidable (a = b)
    let p : InfinitePlace ℚ := default
    let : IsEmpty {v : InfinitePlace ℚ // v ≠ p} := ⟨fun v ↦ v.property (Subsingleton.elim _ _)⟩
    let e : {v : InfinitePlace ℚ // v ≠ p} ≃ Fin (NumberField.Units.rank ℚ) :=
      Fintype.equivFinOfCardEq (by simp [NumberField.Units.rank])
    rw [NumberField.Units.regulator_eq_det ℚ p e]
    exact (congrArg (abs : ℝ → ℝ) Matrix.det_isEmpty).trans abs_one
  change ((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal = 1
  rw [normOneIdeleClassTamagawaMeasure_volume]
  norm_num [hr, hc, Rat.classNumber_eq, hreg, NumberField.discr_rat, ht]

private theorem volume_ne_zero : V ≠ 0 := by simp [rational_normOne_volume]

private theorem character_test_mellin {τ : ℝ≥0ˣ →ₜ* Cℚ} (hτ : RightInverse τ (ideleClassNorm ℚ))
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H)
    (η ψ : PontryaginDual Cℚ) (hη : ∀ t, η (τ t) = 1) (hψ : ∀ t, ψ (τ t) = 1)
    (φ : BruhatCompactSupport Cℚ) (hφ : ∀ g, φ.val g = (η⁻¹ g : ℂ) * H logN(g)) (w : ℂ) :
    M(φ, ψ, w) = if ψ = η then V * bilateralLaplace H w else 0 := by
  classical
  obtain ⟨φr, hr⟩ := exists_normTest (F := ℚ) H hH hc
  have hx : M(φ, ψ, w) = M(φr, ψ * η⁻¹, w) := by
    simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
    apply integral_congr_ae (.of_forall ?_)
    intro g
    let R := (((ideleClassNorm ℚ g : ℝ≥0) : ℝ) : ℂ) ^ w
    change φ.val g * ((ψ g : ℂ) * R) = φr.val g * (((ψ * η⁻¹) g : ℂ) * R)
    rw [hφ, hr]
    change ((_ : Circle) : ℂ) * _ * ((ψ g : ℂ) * R) = _ * (((ψ g * η⁻¹ g : Circle) : ℂ) * R)
    rw [Circle.coe_mul]
    ring
  rw [hx, normTest_mellin _ hH.continuous _ hr]
  by_cases h : ψ = η
  · subst ψ
    simp only [mul_inv_cancel, PontryaginDual.one_apply, implies_true, ite_true, Circle.coe_one, mul_one]
    congr 1
    simpa only [bilateralLaplace, Complex.ofReal_zero, sub_zero, mul_zero, Complex.exp_zero, one_mul,
      mul_one] using grh_shift_integral H hH.continuous (fun _ ↦ (1 : ℂ)) (fun _ ↦ rfl) 0 w
  · have hn : ¬ ∀ u : K, (ψ * η⁻¹) u.val = 1 := fun hh ↦ h (restricted_eq hτ hψ hη hh)
    rw [ite_eq_right hn, ite_eq_right h, zero_mul]

/-- The single physical test has the inverse of each of the finite idelic characters in
its angular factor. The norm-one Tamagawa volume normalizes every selected multiplier to one. -/
def primitiveTest (Q : ℕ) (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) :
    BruhatCompactSupport Cℚ := open Classical in
  V⁻¹ • ∑ i : PrimitiveRow Q, (exists_characterNormTest (primitiveRow i)⁻¹ H hH hc).choose

theorem primitiveTest_value (Q : ℕ) (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H)
    (g : Cℚ) : (primitiveTest Q H hH hc).val g =
      V⁻¹ * ((∑ i : PrimitiveRow Q, ((primitiveRow i)⁻¹ g : ℂ)) * H logN(g)) := by
  classical
  let ev : BruhatCompactSupport Cℚ →ₗ[ℂ] ℂ :=
    { toFun f := f.val g, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  change ev (primitiveTest Q H hH hc) = _
  unfold primitiveTest
  rw [map_smul, map_sum, Finset.sum_mul]
  simp only [smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ (exists_characterNormTest (primitiveRow i)⁻¹ H hH hc).choose_spec g

/-- Each selected character has exactly the supplied bilateral Laplace transform, and
every other section-normalized character has zero Mellin transform. -/
theorem primitiveTest_mellin (Q : ℕ) (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H)
    (ψ : PontryaginDual Cℚ) (hψ : ∀ t, ψ (τ t) = 1) (w : ℂ) :
    M(primitiveTest Q H hH hc, ψ, w) =
      if ψ ∈ range (primitiveRow (Q := Q)) then bilateralLaplace H w else 0 := by
  classical
  obtain ⟨D, hD⟩ := idelicExplicitFormula_integralDistribution (F := ℚ)
    (ideleClassNormTwist ψ w) (map_continuous _)
  have hDM (φ : BruhatCompactSupport Cℚ) : D φ = M(φ, ψ, w) := by
    simpa only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ] using hD φ
  rw [← hDM, primitiveTest, map_smul, map_sum, smul_eq_mul]
  have hi (i : PrimitiveRow Q) : D (exists_characterNormTest (primitiveRow i)⁻¹ H hH hc).choose =
      if ψ = primitiveRow i then V * bilateralLaplace H w else 0 := by
    rw [hDM]
    exact character_test_mellin hτ H hH hc _ ψ (primitiveRow_on_section i τ.toMonoidHom) hψ _
      (exists_characterNormTest (primitiveRow i)⁻¹ H hH hc).choose_spec w
  simp only [hi]
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    simp only [Function.Injective.eq_iff (primitiveRow_injective Q), Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, ← mul_assoc, inv_mul_cancel₀ volume_ne_zero, one_mul]
  · have hj (j : PrimitiveRow Q) : ψ ≠ primitiveRow j := fun he ↦ h ⟨j, he.symm⟩
    simp only [ite_eq_right (hj _), Finset.sum_const_zero, mul_zero]

/-- Admissibility and calibration of a supplied radial test. Vanishing at log norm zero
gives pointwise vanishing on the whole norm-one group. The two polar Mellin values vanish
and the reference value on each selected row is one. -/
theorem primitiveTest_conditions (Q : ℕ) (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (h₀ : H 0 = 0)
    (hm : bilateralLaplace H (-(1 / 2)) = 0) (hp : bilateralLaplace H (1 / 2) = 0)
    (href : bilateralLaplace H (1 / 4) = 1) :
    (∀ u : K, (primitiveTest Q H hH hc).val u.val = 0) ∧
    M(primitiveTest Q H hH hc, 1, -(1 / 2)) = 0 ∧ M(primitiveTest Q H hH hc, 1, 1 / 2) = 0 ∧
    ∀ ψ : PontryaginDual Cℚ, (∀ t, ψ (τ t) = 1) →
      M(primitiveTest Q H hH hc, ψ, 1 / 4) = if ψ ∈ range (primitiveRow (Q := Q)) then 1 else 0 := by
  have hone : ∀ t, (1 : PontryaginDual Cℚ) (τ t) = 1 := fun _ ↦ rfl
  refine ⟨fun u ↦ ?_, ?_, ?_, fun ψ hψ ↦ ?_⟩
  · rw [primitiveTest_value, u.property]
    simp [h₀]
  · rw [primitiveTest_mellin _ τ hτ _ hH hc _ hone, hm, ite_self]
  · rw [primitiveTest_mellin _ τ hτ _ hH hc _ hone, hp, ite_self]
  · rw [primitiveTest_mellin _ τ hτ _ hH hc _ hψ, href]

/-- Pointwise finite residue formula for this same physical test. -/
theorem primitiveTest_cylinders (Q : ℕ) (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H)
    (hc : HasCompactSupport H) (g : Cℚ) : (primitiveTest Q H hH hc).val g =
      V⁻¹ * ((∑ d ∈ Finset.Ioc 0 Q, if classUnit g d = 1 then
        (d.totient : ℂ) * (mertens (Q / d) : ℂ) else 0) * H logN(g)) := by
  rw [primitiveTest_value, ← sum_primitiveSum_classUnit]
  congr 2
  let f (q : ℕ) (χ : DirichletCharacter ℂ q) := χ (classUnit g q : ZMod q)
  calc
    _ = ∑ i : PrimitiveRow Q, f i.1.val i.2.val := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have : NeZero i.1.val := ⟨(Finset.mem_Ioc.mp i.1.property).1.ne'⟩
      change (((packetRow i.2.val g)⁻¹ : Circle) : ℂ) = _
      rw [Circle.coe_inv_eq_conj, packetRow_value, ratDirichletChar_eq_conj, Complex.conj_conj]
      simp only [f, classUnit_eq]
    _ = _ := sum_primitiveRow Q f

/-- Every section-normalized rational idelic row arises at some primitive conductor stage. -/
theorem exists_primitiveRow_of_section (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    (ψ : PontryaginDual Cℚ) (hn : ∀ t, ψ (τ t) = 1) :
    ∃ Q : ℕ, ψ ∈ range (primitiveRow (Q := Q)) := by
  obtain ⟨N, hN, hker⟩ := exists_level_of_trivial_on_section τ hτ ψ hn
  have : NeZero N := hN
  have hk (u : K) (hu : angularResidue N u = 1) : ψ u.val = 1 := by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective u.val
    rw [← hx]
    apply hker
    change classResidue N u.val = 1 at hu
    rw [← hx] at hu
    change (resMod N).toHomUnits x = 1 at hu
    exact congrArg Units.val hu
  obtain ⟨χ, hx, _⟩ := existsUnique_full_row_of_level N ψ τ.toMonoidHom hτ hn hk
  let d := χ.conductor
  have : NeZero d := ⟨χ.conductor_ne_zero⟩
  let i : PrimitiveRow d := ⟨⟨d, Finset.mem_Ioc.mpr ⟨NeZero.pos d, le_rfl⟩⟩,
    ⟨χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive⟩⟩
  refine ⟨d, i, ContinuousMonoidHom.ext fun g ↦ Circle.ext ?_⟩
  exact (packetRow_value χ.primitiveCharacter g).trans (by rw [← ratDirichletChar_primitive]; exact hx g)

/-- The image of the primitive characters increases with the conductor cutoff. -/
theorem primitiveRow_range_mono {Q R : ℕ} (h : Q ≤ R) :
    range (primitiveRow (Q := Q)) ⊆ range (primitiveRow (Q := R)) := by
  rintro _ ⟨⟨⟨q, hq⟩, χ⟩, rfl⟩
  exact ⟨⟨⟨q, Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hq).1,
    (Finset.mem_Ioc.mp hq).2.trans h⟩⟩, χ⟩, rfl⟩

/-- The exterior index of Theorem 12.5.1.1, with both boundary lines included. -/
abbrev ExteriorSite (τ : ℝ≥0ˣ →ₜ* Cℚ) (α : ℝ) :=
  {z : {ψ : PontryaginDual Cℚ // ∀ t : ℝ≥0ˣ, ψ (τ t) = 1} × ℂ //
    0 < ord(z.1.val, z.2) ∧ α ≤ |z.2.re - 1 / 2|}

/-- The exterior sites of one genuine completed idelic row. -/
abbrev RowExteriorSite (ψ : PontryaginDual Cℚ) (α : ℝ) :=
  {z : ℂ // 0 < ord(ψ, z) ∧ α ≤ |z.re - 1 / 2|}

/-- The original complex zero term of §12.5, including the full integer divisor. -/
def traceZeroTerm {τ : ℝ≥0ˣ →ₜ* Cℚ} {α : ℝ} (φ : BruhatCompactSupport Cℚ)
    (z : ExteriorSite τ α) : ℂ :=
  (ord(z.val.1.val, z.val.2) : ℂ) * M(φ, z.val.1.val, z.val.2 - 1 / 2)

private theorem row_norm_summable (φ : BruhatCompactSupport Cℚ) (ψ : PontryaginDual Cℚ) (α : ℝ) :
    Summable (fun z : RowExteriorSite ψ α ↦ ‖(ord(ψ, z.val) : ℂ) * M(φ, ψ, z.val - 1 / 2)‖) := by
  let e (z : RowExteriorSite ψ α) : rowZeroSites ψ := ⟨z.val, z.property.1⟩
  have hi : Injective e := fun _ _ he ↦ Subtype.ext (congrArg (fun z : rowZeroSites ψ ↦ z.val) he)
  apply ((idelicExplicitFormula_summable_spectral_fiber φ ψ).comp_injective hi).congr
  intro z
  apply congrArg (fun x : ℂ ↦ ‖(ord(ψ, z.val) : ℂ) * x‖)
  simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
  apply integral_congr_ae (.of_forall ?_)
  intro g
  let t : ℂ := (((ideleClassNorm ℚ g : ℝ≥0) : ℝ) : ℂ)
  have ht : t ≠ 0 := Complex.ofReal_ne_zero.mpr (by exact_mod_cast (Units.zero_lt (ideleClassNorm ℚ g)).ne')
  change φ.val g * ((ψ g : ℂ) * t ^ z.val) * t ^ (-1 / 2 : ℂ) =
    φ.val g * ((ψ g : ℂ) * t ^ (z.val - 1 / 2))
  rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, sub_eq_add_neg, Complex.cpow_add _ _ ht]
  ac_rfl

/-- On the stage-selected rows the original absolute zero term is the completed
primitive multiplicity times the radial Mellin norm. -/
theorem norm_zeroTerm_primitive (Q : ℕ) (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    (α : ℝ) (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H)
    (z : ExteriorSite τ α) :
    ‖traceZeroTerm (primitiveTest Q H hH hc) z‖ =
      if z.val.1.val ∈ range (primitiveRow (Q := Q)) then
        (ord(z.val.1.val, z.val.2) : ℝ) * ‖bilateralLaplace H (z.val.2 - 1 / 2)‖ else 0 := by
  rw [traceZeroTerm, primitiveTest_mellin _ τ hτ _ hH hc _ z.val.1.property]
  split_ifs with h
  · rw [norm_mul, Complex.norm_intCast, abs_of_nonneg (by exact_mod_cast z.property.1.le)]
  · simp

/-- The full sum of the norms of the original zero terms equals the finite sum of
the primitive-character exterior masses. Both the convergence and its value are asserted. -/
theorem primitiveTest_exterior_hasSum (Q : ℕ) (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    (α : ℝ) (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) :
    HasSum (fun z : ExteriorSite τ α ↦ ‖traceZeroTerm (primitiveTest Q H hH hc) z‖)
      (∑ i : PrimitiveRow Q, ∑' ρ : RowExteriorSite (primitiveRow i) α,
        (ord(primitiveRow i, ρ.val) : ℝ) * ‖bilateralLaplace H (ρ.val - 1 / 2)‖) := by
  let φ := primitiveTest Q H hH hc
  let f (z : ExteriorSite τ α) := ‖traceZeroTerm φ z‖
  let e (w : (i : PrimitiveRow Q) × RowExteriorSite (primitiveRow i) α) : ExteriorSite τ α :=
    ⟨⟨⟨primitiveRow w.1, primitiveRow_on_section w.1 τ.toMonoidHom⟩, w.2.val⟩, w.2.property⟩
  have hi : Injective e := by
    rintro ⟨i, x⟩ ⟨j, y⟩ he
    have hij : i = j := primitiveRow_injective Q (congrArg (fun z : ExteriorSite τ α ↦ z.val.1.val) he)
    subst j
    have hxy : x = y := Subtype.ext (congrArg (fun z : ExteriorSite τ α ↦ z.val.2) he)
    subst y; rfl
  have hzero (z : ExteriorSite τ α) (hz : z ∉ range e) : f z = 0 := by
    have hn : z.val.1.val ∉ range (primitiveRow (Q := Q)) := by
      rintro ⟨i, he⟩
      obtain ⟨⟨⟨ψ, hψ⟩, ρ⟩, hp⟩ := z
      change primitiveRow i = ψ at he
      subst ψ
      exact hz ⟨⟨i, ⟨ρ, hp⟩⟩, rfl⟩
    exact (norm_zeroTerm_primitive Q τ hτ α H hH hc z).trans (ite_eq_right hn)
  have hrow (i : PrimitiveRow Q) : Summable fun ρ : RowExteriorSite (primitiveRow i) α ↦ f (e ⟨i, ρ⟩) :=
    row_norm_summable φ _ α
  have hsum : Summable (f ∘ e) :=
    (summable_sigma_of_nonneg (f := f ∘ e) (fun _ ↦ norm_nonneg _)).mpr ⟨hrow, Summable.of_finite⟩
  apply (hi.hasSum_iff hzero).mp
  convert hsum.hasSum using 1
  symm
  rw [Summable.tsum_sigma' hrow hsum, tsum_fintype]
  refine Finset.sum_congr rfl fun i _ ↦ tsum_congr (fun ρ ↦ ?_)
  exact (norm_zeroTerm_primitive Q τ hτ α H hH hc (e ⟨i, ρ⟩)).trans (ite_eq_left ⟨i, rfl⟩)

/-- The actual ordinary Dirichlet zeros, at the character's primitive conductor, that lie
in the open critical strip and on or beyond either edge of the centered open window. -/
abbrev DirichletExteriorSite {Q : ℕ} (i : PrimitiveRow Q) (α : ℝ) :=
  {ρ : ℂ // 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < primitiveOrder i ρ ∧ α ≤ |ρ.re - 1 / 2|}

private def exteriorSiteEquiv {Q : ℕ} (i : PrimitiveRow Q) (α : ℝ) :
    RowExteriorSite (primitiveRow i) α ≃ DirichletExteriorSite i α where
  toFun z := by
    have hs := row_site_in_strip (primitiveRow i) ⟨z.val, z.property.1⟩
    exact ⟨z.val, hs.1, hs.2, (primitiveRow_divisor_eq_dirichlet i ⟨z.val, hs⟩) ▸
      (Int.pos_iff_toNat_pos.mp z.property.1), z.property.2⟩
  invFun z := ⟨z.val, Int.pos_iff_toNat_pos.mpr
    ((primitiveRow_divisor_eq_dirichlet i ⟨z.val, z.property.1, z.property.2.1⟩).symm ▸
      z.property.2.2.1), z.property.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The original absolute exterior sum is exactly the finite sum over primitive ordinary
Dirichlet L-functions, with their full zero orders and the same fixed radial transform. -/
theorem primitiveTest_dirichlet_hasSum (Q : ℕ) (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    (α : ℝ) (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) :
    HasSum (fun z : ExteriorSite τ α ↦ ‖traceZeroTerm (primitiveTest Q H hH hc) z‖)
      (∑ i : PrimitiveRow Q, ∑' ρ : DirichletExteriorSite i α,
        (primitiveOrder i ρ.val : ℝ) * ‖bilateralLaplace H (ρ.val - 1 / 2)‖) := by
  convert (primitiveTest_exterior_hasSum Q τ hτ α H hH hc) using 1
  symm
  apply Finset.sum_congr rfl
  intro i _
  rw [← (exteriorSiteEquiv i α).tsum_eq (fun ρ : DirichletExteriorSite i α ↦
    (primitiveOrder i ρ.val : ℝ) * ‖bilateralLaplace H (ρ.val - 1 / 2)‖)]
  apply tsum_congr
  intro z
  have hs := row_site_in_strip (primitiveRow i) ⟨z.val, z.property.1⟩
  have hc' : (ord(primitiveRow i, z.val) : ℝ) = (primitiveOrder i z.val : ℝ) := by
    rw [← primitiveRow_divisor_eq_dirichlet i ⟨z.val, hs⟩]
    exact_mod_cast (Int.toNat_of_nonneg z.property.1.le).symm
  exact congrArg (fun c : ℝ ↦ c * ‖bilateralLaplace H (z.val - 1 / 2)‖) hc'

/-- The absolute sum of the original zero terms for the physical finite-conductor test. -/
def exteriorMass (Q : ℕ) (τ : ℝ≥0ˣ →ₜ* Cℚ) (α : ℝ) (H : ℝ → ℂ)
    (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) : ℝ :=
  ∑' z : ExteriorSite τ α, ‖traceZeroTerm (primitiveTest Q H hH hc) z‖

/-- Increasing the primitive conductor cutoff and decreasing the open strip width
can only increase the measured exterior mass of the same radial profile. -/
theorem exteriorMass_le {Q R : ℕ} (hQR : Q ≤ R) (τ : ℝ≥0ˣ →ₜ* Cℚ)
    (hτ : RightInverse τ (ideleClassNorm ℚ)) {α β : ℝ} (hβα : β ≤ α) (H : ℝ → ℂ)
    (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) :
    exteriorMass Q τ α H hH hc ≤ exteriorMass R τ β H hH hc := by
  let e (z : ExteriorSite τ α) : ExteriorSite τ β := ⟨z.val, z.property.1, hβα.trans z.property.2⟩
  have hi : Injective e := fun _ _ he ↦ Subtype.ext (congrArg (fun z : ExteriorSite τ β ↦ z.val) he)
  refine (primitiveTest_exterior_hasSum Q τ hτ α H hH hc).summable.tsum_le_tsum_of_inj e hi
    (fun _ _ ↦ norm_nonneg _) (fun z ↦ ?_) (primitiveTest_exterior_hasSum R τ hτ β H hH hc).summable
  rw [norm_zeroTerm_primitive Q τ hτ, norm_zeroTerm_primitive R τ hτ]
  change (if z.val.1.val ∈ range (primitiveRow (Q := Q)) then _ else 0) ≤
    if z.val.1.val ∈ range (primitiveRow (Q := R)) then _ else 0
  by_cases hz : z.val.1.val ∈ range (primitiveRow (Q := Q))
  · rw [ite_eq_left hz, ite_eq_left (primitiveRow_range_mono hQR hz)]
  · rw [ite_eq_right hz]
    split_ifs with h
    · exact mul_nonneg (by exact_mod_cast z.property.1.le) (norm_nonneg _)
    · rfl

/-- Stage `n+1` selects every primitive conductor up to `n+1` and measures the closed
exterior of the open strip of half-width `1/(n+1)`. -/
def stageMass (τ : ℝ≥0ˣ →ₜ* Cℚ) (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H)
    (hc : HasCompactSupport H) (n : ℕ) : ℝ :=
  exteriorMass (n + 1) τ (1 / (n + 1 : ℝ)) H hH hc

theorem monotone_stageMass (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) :
    Monotone (stageMass τ H hH hc) := fun _ _ h ↦
  exteriorMass_le (Nat.succ_le_succ h) τ hτ (Nat.one_div_le_one_div h) H hH hc

/-- A fixed off-axis zero of an original section-normalized character gives a persistent
positive lower bound along the whole conductor sequence, for any radial profile detecting it. -/
theorem stageMass_lower_of_exterior_site
    (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H)
    (ψ : PontryaginDual Cℚ) (hψ : ∀ t, ψ (τ t) = 1) {ρ : ℂ}
    (hρ : 0 < ord(ψ, ρ)) (hfar : ρ.re ≠ 1 / 2) :
    ∀ᶠ n : ℕ in atTop, (ord(ψ, ρ) : ℝ) * ‖bilateralLaplace H (ρ - 1 / 2)‖ ≤
      stageMass τ H hH hc n := by
  obtain ⟨Q, hQ⟩ := exists_primitiveRow_of_section τ hτ ψ hψ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (abs_pos.mpr (sub_ne_zero.mpr hfar))
  filter_upwards [eventually_ge_atTop (max Q N)] with n hn
  have hlevel : ψ ∈ range (primitiveRow (Q := n + 1)) :=
    primitiveRow_range_mono ((le_max_left Q N).trans (hn.trans (Nat.le_succ _))) hQ
  let z : ExteriorSite τ (1 / (n + 1 : ℝ)) :=
    ⟨⟨⟨ψ, hψ⟩, ρ⟩, hρ, (Nat.one_div_le_one_div ((le_max_right Q N).trans hn)).trans hN.le⟩
  have hterm := norm_zeroTerm_primitive (n + 1) τ hτ _ H hH hc z
  rw [ite_eq_left hlevel] at hterm
  exact hterm.symm.le.trans ((primitiveTest_exterior_hasSum (n + 1) τ hτ _ H hH hc).summable.le_tsum
    z (fun _ _ ↦ norm_nonneg _))

end RiemannMasullo.ConductorSelector
