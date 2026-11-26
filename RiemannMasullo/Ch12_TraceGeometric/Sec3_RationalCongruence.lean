module

public import RiemannMasullo.Ch13_ZerosHecke.RationalExteriorZeros
public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.PrimitiveFourier
public import Mathlib.Topology.Instances.ZMod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Tactic

/-! # Rational idèle-class residues, their Tamagawa masses and primitive Dirichlet rows -/

@[expose] public noncomputable section

open NumberFieldKB.Chebotarev.RatIdele NumberField
open Filter Function IsDedekindDomain MeasureTheory Set
open scoped ComplexConjugate NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.ConductorCylinder

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "K" => MonoidHom.ker (ideleClassNorm ℚ)
local notation "ν" => normOneIdeleClassTamagawaMeasure ℚ
private local instance : MeasurableSpace Cℚ := borel _
private local instance : BorelSpace Cℚ := ⟨rfl⟩

local notation "πℚ" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ)

/-- Reduction of the unit part, descended to the actual rational idele class group. -/
def classResidue (q : ℕ) [NeZero q] : Cℚ →ₜ* (ZMod q)ˣ :=
  ⟨QuotientGroup.lift _ (resMod q).toHomUnits (by
      rintro _ ⟨a, rfl⟩
      exact MonoidHom.mem_ker.mpr (Units.ext (resMod_diag q a))),
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (by
      apply continuous_of_continuousAt_one (resMod q).toHomUnits
      have h : ∀ᶠ x in 𝓝 (1 : IdQ), (resMod q).toHomUnits 1 = (resMod q).toHomUnits x := by
        filter_upwards [eventually_resMod_eq_one q] with x hx
        exact Units.ext (by change resMod q 1 = resMod q x; rw [map_one, hx])
      exact continuousAt_const.congr h)⟩

@[simp] theorem classResidue_mk (q : ℕ) [NeZero q] (x : IdQ) :
    classResidue q (πℚ x) = (resMod q).toHomUnits x := rfl

/-- Reduction restricted to the kernel of the actual idele class norm. -/
def angularResidue (q : ℕ) [NeZero q] : K →ₜ* (ZMod q)ˣ :=
  (classResidue q).comp ⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩

/-- A finite quotient is trivial along every positive-real norm section. -/
theorem classResidue_on_section (q : ℕ) [NeZero q] (σ : ℝ≥0ˣ →* Cℚ) (t : ℝ≥0ˣ) :
    classResidue q (σ t) = 1 := by
  let n := Fintype.card (ZMod q)ˣ
  have hn : 0 < n := Fintype.card_pos
  let u : ℝ≥0ˣ := Units.mk0 ((t : ℝ≥0) ^ ((n : ℝ)⁻¹)) (NNReal.rpow_pos (Units.zero_lt t)).ne'
  have hu : u ^ n = t := Units.ext (NNReal.rpow_inv_natCast_pow _ hn.ne')
  rw [← hu, map_pow, map_pow]
  exact pow_card_eq_one

theorem angularResidue_surjective (q : ℕ) [NeZero q] : Surjective (angularResidue q) := by
  intro a
  obtain ⟨x, hx⟩ := resMod_toHomUnits_surjective q a
  let y := πℚ x
  let σ := (πℚ).comp ratIdeleNormSection
  let t := ideleClassNorm ℚ y
  let u : K := ⟨y / σ t, by
    change ideleClassNorm ℚ (y / σ t) = 1
    rw [map_div, ratIdeleNormSection_class_rightInverse t]
    change t / t = 1
    simp⟩
  refine ⟨u, ?_⟩
  change classResidue q (y / σ t) = a
  rw [map_div, classResidue_on_section, div_one]
  exact hx

/-- The actual angular cylinder at a specified invertible residue. -/
def cylinder (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) : Set K := angularResidue q ⁻¹' {r}

theorem isClopen_cylinder (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) : IsClopen (cylinder q r) :=
  (isClopen_discrete _).preimage (angularResidue q).continuous

private local instance : (ν).IsHaarMeasure :=
  (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1

private local instance : CompactSpace K := (ideleClassGroup_finiteness ℚ).2.1

/-- The Tamagawa measure of each norm-one cylinder is exactly its total mass divided by φ(q). -/
theorem cylinder_mass (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) :
    (ν).real (cylinder q r) = (ν).real univ / q.totient := by
  let f := (angularResidue q).toMonoidHom
  have hsur : Surjective f := angularResidue_surjective q
  have hker : MeasurableSet (f.ker : Set K) := (isClopen_cylinder q 1).isClosed.measurableSet
  have hi : f.ker.index = q.totient := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsur, Subgroup.card_top,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  obtain ⟨g, hg⟩ := hsur r
  have he : (fun k ↦ g * k) ⁻¹' (cylinder q r) = (f.ker : Set K) := by
    ext k
    change f (g * k) = r ↔ f k = 1
    rw [map_mul, hg, mul_eq_left]
  have hm := measure_preimage_mul ν g (cylinder q r)
  rw [he] at hm
  have h := f.ker.index_mul_measure hker ν
  rw [hi, hm] at h
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h'
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne')).mpr
  exact (mul_comm _ _).trans h'

/-- The inverse in the arithmetic idelic lift is complex conjugation on a finite unit character. -/
theorem ratDirichletChar_eq_conj (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (g : Cℚ) :
    ((ratDirichletChar q χ g : ℂˣ) : ℂ) = conj (χ (classResidue q g : ZMod q)) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  rw [ratDirichletChar_mk, coe_ideleChar]
  change (χ (resMod q x))⁻¹ = star (χ (resMod q x))
  rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']

/-- The normalized one-coset Mellin angular coefficient on the genuine rational norm-one group. -/
theorem cylinder_dirichlet_integral (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) :
    (∫ k in cylinder q r, ((ratDirichletChar q χ k.val : ℂˣ) : ℂ) ∂ν) / ((ν).real univ : ℂ) =
      conj (χ (r : ZMod q)) / (q.totient : ℂ) := by
  have he (k : K) (hk : k ∈ cylinder q r) :
      ((ratDirichletChar q χ k.val : ℂˣ) : ℂ) = conj (χ (r : ZMod q)) := by
    rw [ratDirichletChar_eq_conj]
    change conj (χ ((angularResidue q k : (ZMod q)ˣ) : ZMod q)) = _
    rw [show angularResidue q k = r from hk]
  rw [setIntegral_congr_fun (isClopen_cylinder q r).isClosed.measurableSet he, setIntegral_const,
    Complex.real_smul, cylinder_mass, Complex.ofReal_div, Complex.ofReal_natCast]
  have hV : ((ν).real univ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr measureReal_univ_pos.ne'
  have hq : (q.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  field_simp

/-- A row nontrivial on the congruence kernel contributes zero on every congruence cylinder. -/
theorem cylinder_integral_eq_zero_of_nontrivial_on_kernel (q : ℕ) [NeZero q] (r : (ZMod q)ˣ)
    (ψ : PontryaginDual Cℚ) (hne : ∃ u : K, angularResidue q u = 1 ∧ ψ u.val ≠ 1) :
    (∫ k in cylinder q r, (ψ k.val : ℂ) ∂ν) = 0 := by
  classical
  obtain ⟨u, hu, hψ⟩ := hne
  let f := (cylinder q r).indicator (fun k : K ↦ (ψ k.val : ℂ))
  have htr (k : K) : f (u * k) = (ψ u.val : ℂ) * f k := by
    have he : u * k ∈ cylinder q r ↔ k ∈ cylinder q r := by
      change angularResidue q (u * k) = r ↔ angularResidue q k = r
      rw [map_mul, hu, one_mul]
    by_cases hk : k ∈ cylinder q r
    · simp only [f, indicator_of_mem (he.mpr hk), indicator_of_mem hk, Subgroup.coe_mul, map_mul,
        Circle.coe_mul]
    · simp only [f, indicator_of_notMem (he.not.mpr hk), indicator_of_notMem hk, mul_zero]
  have hi := integral_mul_left_eq_self (μ := ν) f u
  simp only [htr, integral_const_mul] at hi
  have hu' : (ψ u.val : ℂ) ≠ 1 := fun h ↦ hψ (Circle.ext h)
  have hn : (ψ u.val : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hu'
  have hz : ((ψ u.val : ℂ) - 1) * ∫ k, f k ∂ν = 0 := by rw [sub_mul, one_mul, hi, sub_self]
  rw [← integral_indicator (isClopen_cylinder q r).isClosed.measurableSet]
  exact (mul_eq_zero.mp hz).resolve_left hn

/-- Distinct characters mod q have distinct restrictions to the actual norm-one group. -/
theorem angular_lift_injective (q : ℕ) [NeZero q] :
    Injective (fun χ : DirichletCharacter ℂ q ↦ fun k : K ↦ ((ratDirichletChar q χ k.val : ℂˣ) : ℂ)) := by
  intro χ χ' h
  apply MulChar.ext
  intro r
  obtain ⟨k, hk⟩ := angularResidue_surjective q r
  have he := congrFun h k
  simp only [ratDirichletChar_eq_conj] at he
  change conj (χ (angularResidue q k : ZMod q)) = conj (χ' (angularResidue q k : ZMod q)) at he
  exact (starRingEnd ℂ).injective (hk ▸ he)

/-- A genuine angular row trivial on the congruence kernel factors through a unique Dirichlet
character modulo q. -/
theorem existsUnique_angular_lift_of_trivial_on_kernel (q : ℕ) [NeZero q] (ψ : PontryaginDual Cℚ)
    (hker : ∀ k : K, angularResidue q k = 1 → ψ k.val = 1) :
    ∃! χ : DirichletCharacter ℂ q, ∀ k : K,
      ((ratDirichletChar q χ k.val : ℂˣ) : ℂ) = (ψ k.val : ℂ) := by
  let f := (angularResidue q).toMonoidHom
  let g : K →* ℂˣ := (Circle.toUnits.comp
    (ψ.toMonoidHom.comp (ideleClassNorm ℚ).ker.subtype))⁻¹
  have hfg : f.ker ≤ g.ker := by
    intro k hk
    apply MonoidHom.mem_ker.mpr
    change (Circle.toUnits (ψ k.val))⁻¹ = 1
    rw [hker k (MonoidHom.mem_ker.mp hk), map_one, inv_one]
  let φ := f.liftOfSurjective (angularResidue_surjective q) ⟨g, hfg⟩
  let χ := MulChar.ofUnitHom φ
  have hval (k : K) : ((ratDirichletChar q χ k.val : ℂˣ) : ℂ) = (ψ k.val : ℂ) := by
    have hφ : φ (f k) = g k := MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨g, hfg⟩ k
    rw [ratDirichletChar_eq_conj]
    change star (χ (f k : ZMod q)) = _
    rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
    rw [show χ (f k : ZMod q) = (φ (f k) : ℂ) from MulChar.ofUnitHom_coe _ _, hφ]
    simp [g]
    rfl
  refine ⟨χ, hval, fun χ' hχ' ↦ angular_lift_injective q (funext fun k ↦ (hχ' k).trans (hval k).symm)⟩

local instance {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : NeZero χ.conductor :=
  ⟨χ.conductor_ne_zero⟩

/-- The actual class-valued Dirichlet lift is identical to the lift at its primitive conductor. -/
theorem ratDirichletChar_primitive (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ratDirichletChar q χ = ratDirichletChar χ.conductor χ.primitiveCharacter := by
  ext1 g
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  rw [ratDirichletChar_mk, ratDirichletChar_mk, ← ideleChar_changeLevel χ.conductor_dvd_level,
    DirichletCharacter.changeLevel_primitiveCharacter]

/-- At level q the row has exactly the primitive series and zero multiplicities of the
inducing character, and its actual angular Fourier weight is the conjugate at r over φ(q). -/
theorem exists_primitive_row (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ ψ : PontryaginDual Cℚ, IsOfFinOrder ψ ∧
      (∀ x : Cℚ, (ψ x : ℂ) = ((ratDirichletChar q χ x : ℂˣ) : ℂ)) ∧
      (∀ s : ℂ, ∀ hs : 1 < s.re,
        finiteHeckeL ψ ⟨s, hs⟩ = LSeries (χ.primitiveCharacter ·) s) ∧
      (∀ z : ℂ, 0 < z.re → meromorphicOrderAt (continuedCompletedHeckeL ψ) z =
        meromorphicOrderAt (DirichletCharacter.LFunction χ.primitiveCharacter) z) ∧
      ∀ r : (ZMod q)ˣ, (∫ k in cylinder q r, (ψ k.val : ℂ) ∂ν) / ((ν).real univ : ℂ) =
        conj (χ (r : ZMod q)) / (q.totient : ℂ) := by
  obtain ⟨ψ, hfin, hval, hL⟩ :=
    DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values χ.primitiveCharacter_isPrimitive
  have hx (g : Cℚ) : (ψ g : ℂ) = ((ratDirichletChar q χ g : ℂˣ) : ℂ) := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    rw [hval, ratDirichletChar_mk, ← ideleChar_changeLevel χ.conductor_dvd_level,
      DirichletCharacter.changeLevel_primitiveCharacter]
  refine ⟨ψ, hfin, hx, hL, ?_, ?_⟩
  · intro z hz
    symm
    exact meromorphicOrderAt_finiteHeckeL_continuation ψ (meromorphic_dirichletLFunction χ.primitiveCharacter)
      (fun u ↦ by rw [DirichletCharacter.LFunction_eq_LSeries _ u.2, hL u.val u.2]) hz
  · intro r
    simpa only [hx] using cylinder_dirichlet_integral q r χ

/-- The arithmetic Dirichlet row is trivial along every positive-real section. -/
theorem arithmetic_row_on_section (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ : ℝ≥0ˣ →* Cℚ) (t : ℝ≥0ˣ) : ((ratDirichletChar q χ (σ t) : ℂˣ) : ℂ) = 1 := by
  rw [ratDirichletChar_eq_conj, classResidue_on_section]
  simp

/-- Among genuine spectral labels trivial on the chosen norm section, the congruence
kernel singles out exactly the full Dirichlet lifts modulo q, each once. -/
theorem existsUnique_full_row_of_level (q : ℕ) [NeZero q] (ψ : PontryaginDual Cℚ)
    (σ : ℝ≥0ˣ →* Cℚ) (hr : RightInverse σ (ideleClassNorm ℚ))
    (hσ : ∀ t, ψ (σ t) = 1) (hk : ∀ u : K, angularResidue q u = 1 → ψ u.val = 1) :
    ∃! χ : DirichletCharacter ℂ q, ∀ x : Cℚ,
      ((ratDirichletChar q χ x : ℂˣ) : ℂ) = (ψ x : ℂ) := by
  obtain ⟨χ, hχ, hunique⟩ := existsUnique_angular_lift_of_trivial_on_kernel q ψ hk
  refine ⟨χ, ?_, fun χ' hh ↦ hunique χ' (fun u ↦ hh u.val)⟩
  intro x
  let t := ideleClassNorm ℚ x
  let u : K := ⟨x / σ t, by
    change ideleClassNorm ℚ (x / σ t) = 1
    rw [map_div, hr]
    change t / t = 1
    simp⟩
  have h := hχ u
  have hx : classResidue q (x / σ t) = classResidue q x := by
    rw [map_div, classResidue_on_section, div_one]
  have hy : ψ (x / σ t) = ψ x := by rw [map_div, hσ, div_one]
  change ((ratDirichletChar q χ (x / σ t) : ℂˣ) : ℂ) = (ψ (x / σ t) : ℂ) at h
  rw [ratDirichletChar_eq_conj, hx, hy] at h
  rw [ratDirichletChar_eq_conj]
  exact h

/-- The coefficient of the degree-one local Euler factor, with value zero at a ramified place. -/
def localPrimeValue (ψ : PontryaginDual Cℚ) (v : Pl) : ℂ := open Classical in
  if (ideleClassNormTwist ψ 0).IsUnramifiedAt v then (ideleClassNormTwist ψ 0).localValue v else 0

/-- At every finite place, the local coefficient of the actual Hecke row is the
primitive Dirichlet value, including when the original level is imprimitive. -/
theorem localPrimeValue_eq_primitive (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (ψ : PontryaginDual Cℚ) (hψ : ∀ x, (ψ x : ℂ) = ((ratDirichletChar q χ x : ℂˣ) : ℂ))
    (v : Pl) : localPrimeValue ψ v = χ.primitiveCharacter (pr v) := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  let η := ideleClassNormTwist ψ 0
  have hres (u : (v.adicCompletion ℚ)ˣ) : η.restrict v u.val =
      (ideleChar χ.conductor χ.primitiveCharacter (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) : ℂ) := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (ψ (QuotientGroup.mk _) : ℂ) * (_ : ℂ) ^ (0 : ℂ) = _
    rw [Complex.cpow_zero, mul_one, hψ, ratDirichletChar_primitive, ratDirichletChar_mk]
  by_cases hc : (pr v).Coprime χ.conductor
  · obtain ⟨hU, hv⟩ := rationalDirichletLift_unramified χ.primitiveCharacter η v hc hres
    exact (ite_eq_left hU).trans hv
  · have hp := not_not.mp (mt (pr_prime v).coprime_iff_not_dvd.mpr hc)
    exact (ite_eq_right (rationalDirichletLift_ramified χ.primitiveCharacter_isPrimitive η v hp hres)).trans
      (χ.primitiveCharacter.map_nonunit (mt (ZMod.isUnit_iff_coprime _ _).mp hc)).symm

/-- Every Euler factor of the finite-level angular row is the Euler factor at its
primitive conductor, including at primes dividing the level and coprime to the conductor. -/
theorem finiteHeckeEulerFactor_primitive (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (ψ : PontryaginDual Cℚ) (hψ : ∀ x, (ψ x : ℂ) = ((ratDirichletChar q χ x : ℂˣ) : ℂ))
    (v : Pl) (s : ℂ) : finiteHeckeEulerFactor ψ v s =
      (1 - χ.primitiveCharacter (pr v) * (pr v : ℂ) ^ (-s))⁻¹ := by
  rw [← localPrimeValue_eq_primitive q χ ψ hψ v, finiteHeckeEulerFactor, localPrimeValue, absNorm_asIdeal]
  split_ifs <;> simp

/-- The true local Hecke coefficients, averaged with the physical cylinder's angular
weights, detect the residue modulo the prime-to-`p` part with mass `1 / φ(p^e)`. -/
theorem cylinderAverage_localPrimeValue_pow (q : ℕ) [NeZero q] (r : (ZMod q)ˣ)
    (ψ : DirichletCharacter ℂ q → PontryaginDual Cℚ)
    (hψ : ∀ χ x, (ψ χ x : ℂ) = ((ratDirichletChar q χ x : ℂˣ) : ℂ))
    (v : Pl) {e m k : ℕ} (hk : k ≠ 0) (hq : q = pr v ^ e * m) (hpm : ¬ pr v ∣ m) :
    RationalConductor.cylinderAverage q r (fun χ ↦ localPrimeValue (ψ χ) v ^ k) =
      if (ZMod.cast (r : ZMod q) : ZMod m) = (pr v ^ k : ℕ) then
        ((pr v ^ e).totient : ℂ)⁻¹ else 0 := by
  convert RationalConductor.primeWeight_prime_pow (pr_prime v) hk hq hpm r using 1
  unfold RationalConductor.primeWeight
  congr 1
  funext χ
  rw [localPrimeValue_eq_primitive q χ _ (hψ χ), Nat.cast_pow, map_pow]

end RiemannMasullo.ConductorCylinder
