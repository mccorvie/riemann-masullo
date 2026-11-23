module

public import RiemannMasullo.Ch10_TraceSpectral.Sec1
public import RiemannMasullo.Ch11_ShellStructure.Sec1a

import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import RiemannMasullo.Ch05_ThetaZSpaces.Sec5
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b
import RiemannMasullo.Ch09_HardySobolev.Sec2
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# S-local carvings

Masullo, §11.1.2, pp. 480–483. A finite set of places in the base records its
finite places, with all archimedean places included throughout.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "μ₁" => normOneIdeleClassTamagawaMeasure F
local notation "ℬ₀" => ↥(adelePolarSubspace F)
local notation "ℬₛ(" S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "norm𝔽" => fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ)
local notation "classOf" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)

local instance instIdeleClassMeasurableSpaceSec1b : MeasurableSpace C𝔽 := borel _
local instance instIdeleClassBorelSpaceSec1b : BorelSpace C𝔽 := ⟨rfl⟩
local instance instIdeleClassT2SpaceSec1b : T2Space C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
local instance instIdeleClassLocallyCompactSpaceSec1b : LocallyCompactSpace C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
local instance instIdeleClassSecondCountableSec1b : SecondCountableTopology C𝔽 :=
  letI := idele_secondCountable F
  inferInstanceAs (SecondCountableTopology
    (I𝔽 ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))
local instance instIdeleClassHaarMeasureSec1b : Measure.IsHaarMeasure μ𝔽 :=
  (ideleClassTamagawaMeasure_isWeil F).1

/-- Paper: (11.1.2.1), p. 480. The indices are the finite sets of places outside
the base set, ordered by inclusion. All the archimedean places are in the base. -/
abbrev SLocalCarvingIndex (S : Finset V) := {T : Finset V // Disjoint S T}

/-- Paper: (11.1.2.1), p. 480. A finite set occurs as an index exactly when
each of its places is outside the base set. -/
theorem exists_sLocalCarvingIndex_iff (S T : Finset V) :
    (∃ i : SLocalCarvingIndex (F := F) S, i.val = T) ↔ ∀ v ∈ T, v ∉ S := by
  constructor
  · rintro ⟨⟨T', h⟩, rfl⟩ v hv hS
    exact Finset.disjoint_left.1 h hS hv
  · intro h
    exact ⟨⟨T, Finset.disjoint_left.2 fun v hS hT ↦ h v hT hS⟩, rfl⟩

/-- Paper: (11.1.2.1), p. 480. There are countably many finite-place indices. -/
theorem countable_sLocalCarvingIndex (S : Finset V) :
    Countable (SLocalCarvingIndex (F := F) S) := by
  have hR : Countable (𝓞 F) := (RingOfIntegers.basis F).repr.injective.countable
  have hV : Countable V := by
    have hfg : ∀ I : Ideal (𝓞 F), ∃ s : Finset (𝓞 F), Ideal.span (s : Set (𝓞 F)) = I :=
      fun I ↦ (IsNoetherian.noetherian I)
    choose g hg using hfg
    have hinj : Injective (fun v : V ↦ g v.asIdeal) := fun a b h ↦
      HeightOneSpectrum.ext (by rw [← hg a.asIdeal, ← hg b.asIdeal]; exact congrArg _ (congrArg _ h))
    exact hinj.countable
  unfold SLocalCarvingIndex
  infer_instance

variable (F) in
/-- Paper: Theorem 11.1.2.1, p. 480. The zero-line ambient space is weighted L²
on the idele classes. It is the singleton-base case of the space used in §10.1. -/
abbrev IdeleClassZeroLineSobolev (s : ℝ) :=
  CompactIntervalSobolev μ𝔽 (fun g ↦ Real.log (norm𝔽 g)) 0 0 s

local notation "W(" s ")" => IdeleClassZeroLineSobolev F s
local notation "ν(" s ")" =>
  (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (norm𝔽 g))))
local notation "M(" s ", " J ", " hJ ")" => modulatedAbsoluteCutoffOperator m𝔽 (ν(s)) J hJ
local notation "Wω(" s ", " hs ", " ω ")" =>
  actionIsotype ((hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs).comp
    (ideleClassNorm F).ker.subtype) ω

/-- Paper: (11.1.2.2)–(11.1.2.3), p. 480. The two cutoff choices are the
positive half-line and the two-sided band in the idelic norm variable. -/
def sLocalCarvingBand (twoSided : Bool) (Λ : ℝ) : Set ℝ :=
  if twoSided then Icc Λ⁻¹ Λ else Ici Λ⁻¹

/-- Paper: (11.1.2.3), p. 480. Both cutoff bands are Borel. -/
theorem measurableSet_sLocalCarvingBand (twoSided : Bool) (Λ : ℝ) :
    MeasurableSet (sLocalCarvingBand twoSided Λ) := by
  unfold sLocalCarvingBand
  split_ifs
  · exact measurableSet_Icc
  · exact measurableSet_Ici

/-- Paper: (11.1.2.3), p. 480. The half-line retains norm one at radius two
and the bounded band excludes norm three.
Deviation: Sanity check distinguishing the two cutoffs. -/
theorem sLocalCarvingBand_radius_two :
    (1 : ℝ) ∈ sLocalCarvingBand false 2 ∧ (3 : ℝ) ∉ sLocalCarvingBand true 2 := by
  simp only [sLocalCarvingBand, ite_true, ite_false, Bool.false_eq_true, mem_Ici, mem_Icc, not_and,
    not_le]
  constructor <;> norm_num

/-- Paper: (11.1.2.3), p. 480. Homogeneous theta of an adelic test with both
polar values zero is in weighted L² on the zero line. -/
theorem memLp_homogeneousTheta_zeroLine (s : ℝ) (ω : PontryaginDual C₁) (f : ℬ₀) :
    MemLp (homogeneousAdelicTheta ω f.val : C𝔽 → ℂ) 2 (ν(s)) := by
  have hs₀ : (0 : ℝ) ≤ max s 0 := le_max_right _ _
  obtain ⟨j, -, -, hj⟩ :=
    exists_globalHomogeneousThetaSobolevInclusion (F := F) (a := 0) (le_refl (0 : ℝ)) hs₀ ω
  have hf := (mem_adelePolarSubspace f.val).mp f.property
  let x : ↥(globalPolarFreeThetaSubmodule (F := F) ω) :=
    ⟨Submodule.Quotient.mk f.val,
      (mem_globalPolarFreeThetaSubmodule ω _).mpr ⟨f.val, hf.1, hf.2, rfl⟩⟩
  have hx := (hj f x rfl).2.trans (Filter.EventuallyEq.of_eq (modulationWeight_zero m𝔽 _))
  have hmem := (Lp.memLp (j x).val.val).ae_eq
    ((withDensity_absolutelyContinuous _ _).ae_le hx)
  refine hmem.mono_measure (withDensity_mono (.of_forall fun g ↦ ?_))
  simp only [Bool.false_eq_true, ite_false]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (Real.log (norm𝔽 g))])
    (by linarith [le_max_left s 0])

open scoped TensorProduct in
/-- A linear functional that scales by `c` under an operator on the pure tensors of an
inductive tensor product scales by `c` on the whole space. -/
private theorem adelePrincipalValue_mem_polarSubspace_ind {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] {ι : Type*} {D : ι → Type*}
    [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, D i)) ≃L[ℂ] B)
    (P : B →ₗ[ℂ] B) (Λ : B →ₗ[ℂ] ℂ) (c : ℂ)
    (h : ∀ (a : A) (g : ∀ i, D i), Λ (P (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i)))) =
      c * Λ (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i)))) (x : B) :
    Λ (P x) = c * Λ x := by
  obtain ⟨t, rfl⟩ := e.surjective x
  let W := FinestLocallyConvex (⨂[ℂ] i, D i)
  let L₁ : A ⊗[ℂ] W →ₗ[ℂ] ℂ := Λ ∘ₗ P ∘ₗ (e.toLinearMap : InductiveTensor A W →ₗ[ℂ] B)
  let L₂ : A ⊗[ℂ] W →ₗ[ℂ] ℂ := c • (Λ ∘ₗ (e.toLinearMap : InductiveTensor A W →ₗ[ℂ] B))
  have hL : L₁ = L₂ := by
    refine TensorProduct.ext' fun a z ↦ ?_
    refine PiTensorProduct.induction_on (motive := fun z : ⨂[ℂ] i, D i ↦
      L₁ (a ⊗ₜ[ℂ] (z : W)) = L₂ (a ⊗ₜ[ℂ] (z : W))) z ?_ ?_
    · intro r g
      have ht : (a ⊗ₜ[ℂ] (((r • (⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i)) : W) : A ⊗[ℂ] W) =
          r • (a ⊗ₜ[ℂ] (((⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i) : W)) :=
        (TensorProduct.mk ℂ A W a).map_smul r (((⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i) : W)
      have hp : L₁ (a ⊗ₜ[ℂ] (((⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i) : W)) =
          L₂ (a ⊗ₜ[ℂ] (((⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i) : W)) := by
        change Λ (P (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i)))) = c • Λ (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i)))
        rw [h a g, smul_eq_mul]
      exact (congrArg L₁ ht).trans ((map_smul L₁ r _).trans ((congrArg (r • ·) hp).trans
        ((map_smul L₂ r _).symm.trans (congrArg L₂ ht.symm))))
    · intro z₁ z₂ h₁ h₂
      have ht : (a ⊗ₜ[ℂ] (((z₁ + z₂ : ⨂[ℂ] i, D i)) : W) : A ⊗[ℂ] W) =
          a ⊗ₜ[ℂ] (z₁ : W) + a ⊗ₜ[ℂ] (z₂ : W) :=
        (TensorProduct.mk ℂ A W a).map_add (z₁ : W) (z₂ : W)
      exact (congrArg L₁ ht).trans ((map_add L₁ _ _).trans ((congrArg₂ (· + ·) h₁ h₂).trans
        ((map_add L₂ _ _).symm.trans (congrArg L₂ ht.symm))))
  exact LinearMap.congr_fun hL t

/-- Weil's local principal value of any test vanishes at zero. -/
private theorem adelePrincipalValue_mem_polarSubspace_localZero (v : V)
    (g : SchwartzBruhat (Multiplicative (v.adicCompletion F))) :
    finitePlacePrincipalValue v g (Multiplicative.ofAdd 0) = 0 := by
  let h := (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (h.choose : v.adicCompletion F) h.choose_spec.ne_zero
  rw [finitePlacePrincipalValue_spec v π h.choose_spec]
  unfold finitePlacePrincipalValueFun
  simp only [show (Multiplicative.ofAdd (0 : v.adicCompletion F)).toAdd = 0 from rfl, mul_zero,
    setIntegral_const, Complex.real_smul]
  have hm : (((finiteLocalMultiplicativeTamagawaMeasure F v).real
      (v.adicCompletionIntegers F).units : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (finitePlacePrincipalValue_integrable v π g (Multiplicative.ofAdd 0)).1.ne'
  field_simp
  ring

/-- Multiplication by a unit pushes the local additive measure forward to a multiple of
itself, by the distributive Haar character of the inverse. -/
private theorem adelePrincipalValue_mem_polarSubspace_map_mul (v : V)
    [LocallyCompactSpace (v.adicCompletion F)] (a : (v.adicCompletion F)ˣ) :
    let : MeasurableSpace (v.adicCompletion F) := borel _
    (finiteLocalAdditiveTamagawaMeasure F v).map (fun x ↦ (a : v.adicCompletion F) * x) =
      ((distribHaarChar (G := (v.adicCompletion F)ˣ) (v.adicCompletion F) (a⁻¹ : (v.adicCompletion F)ˣ) : ℝ≥0) : ENNReal) •
        finiteLocalAdditiveTamagawaMeasure F v := by
  let : MeasurableSpace (v.adicCompletion F) := borel _
  have : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  have : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  have : SecondCountableTopology (v.adicCompletion F) := secondCountable_of_proper
  have := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  ext s hs
  rw [Measure.map_apply (measurable_const_mul (a : v.adicCompletion F)) hs, smul_apply,
    smul_eq_mul, distribHaarChar_mul]
  congr 1
  ext x
  simp [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def]

open scoped Pointwise in
/-- The distributive Haar character is trivial on the local integer units. -/
private theorem adelePrincipalValue_mem_polarSubspace_char_unit (v : V)
    [LocallyCompactSpace (v.adicCompletion F)] (u : (v.adicCompletion F)ˣ) (hu : u ∈ (v.adicCompletionIntegers F).units) :
    distribHaarChar (G := (v.adicCompletion F)ˣ) (v.adicCompletion F) u = 1 := by
  let : MeasurableSpace (v.adicCompletion F) := borel _
  have : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  have : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  have : SecondCountableTopology (v.adicCompletion F) := secondCountable_of_proper
  have := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let O := (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hO : IsOpen O := Valued.isOpen_valuationSubring _
  have hK : IsCompact O := isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)
  have h1 : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F := hu.1
  have h2 : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F :=
    hu.2
  have hset : u • O = O := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def]
    constructor
    · intro hy
      have := mul_mem h1 hy
      rwa [smul_eq_mul, ← mul_assoc, Units.mul_inv, one_mul] at this
    · intro hy
      exact mul_mem h2 hy
  exact distribHaarChar_eq_of_measure_smul_eq_mul (μ := finiteLocalAdditiveTamagawaMeasure F v)
    (hO.measure_pos _ ⟨0, (v.adicCompletionIntegers F).zero_mem⟩).ne' hK.measure_ne_top
    (by rw [hset, ENNReal.coe_one, one_mul])

/-- Scaling by `u⁻¹ π⁻¹` with `u` an integer unit multiplies a local integral by the
distributive Haar character of `π`. -/
private theorem adelePrincipalValue_mem_polarSubspace_integral_scale (v : V)
    [LocallyCompactSpace (v.adicCompletion F)] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (π u : (v.adicCompletion F)ˣ)
    (hu : u ∈ (v.adicCompletionIntegers F).units) (φ : v.adicCompletion F → E)
    (hφ : Continuous φ) :
    ∫ x, φ ((↑u⁻¹ : v.adicCompletion F) * ((↑π⁻¹ : v.adicCompletion F) * x))
        ∂finiteLocalAdditiveTamagawaMeasure F v =
      (distribHaarChar (G := (v.adicCompletion F)ˣ) (v.adicCompletion F) π : ℝ) •
        ∫ x, φ x ∂finiteLocalAdditiveTamagawaMeasure F v := by
  let : MeasurableSpace (v.adicCompletion F) := borel _
  have : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  have : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  have : SecondCountableTopology (v.adicCompletion F) := secondCountable_of_proper
  have hmap := adelePrincipalValue_mem_polarSubspace_map_mul v (u⁻¹ * π⁻¹)
  have heq (x : v.adicCompletion F) :
      φ ((↑u⁻¹ : v.adicCompletion F) * ((↑π⁻¹ : v.adicCompletion F) * x)) =
        φ (((u⁻¹ * π⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) := by
    simp [mul_assoc]
  refine (integral_congr_ae (.of_forall heq)).trans ?_
  rw [← integral_map
      (measurable_const_mul ((u⁻¹ * π⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)).aemeasurable
      hφ.aestronglyMeasurable, hmap, integral_smul_measure]
  have hΔ : distribHaarChar (G := (v.adicCompletion F)ˣ) (v.adicCompletion F) (u⁻¹ * π⁻¹)⁻¹ =
      distribHaarChar (G := (v.adicCompletion F)ˣ) (v.adicCompletion F) π := by
    rw [mul_inv_rev, inv_inv, inv_inv, map_mul,
      adelePrincipalValue_mem_polarSubspace_char_unit v u hu, mul_one]
  rw [hΔ]
  rfl

/-- Weil's local principal value multiplies the local integral of every test by one
constant. -/
private theorem adelePrincipalValue_mem_polarSubspace_localIntegral (v : V) :
    ∃ κ : ℂ, ∀ g : SchwartzBruhat (Multiplicative (v.adicCompletion F)),
      ∫ x, finitePlacePrincipalValue v g (Multiplicative.ofAdd x)
          ∂finiteLocalAdditiveTamagawaMeasure F v =
        κ * ∫ x, g (Multiplicative.ofAdd x) ∂finiteLocalAdditiveTamagawaMeasure F v := by
  let : MeasurableSpace (v.adicCompletion F) := borel _
  have : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  have : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  have : SecondCountableTopology (v.adicCompletion F) := secondCountable_of_proper
  let : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  have : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  have : SecondCountableTopology (v.adicCompletion F)ˣ :=
    (Units.isEmbedding_val₀ (G₀ := v.adicCompletion F)).secondCountableTopology
  let μ := finiteLocalAdditiveTamagawaMeasure F v
  have hμ : μ.IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let μm : Measure (Multiplicative (v.adicCompletion F)) := μ
  have : μm.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.map_add_left_eq_self x.toAdd }
  have hint (h : SchwartzBruhat (Multiplicative (v.adicCompletion F))) :
      Integrable (fun x : v.adicCompletion F ↦ h (Multiplicative.ofAdd x)) μ :=
    SchwartzBruhat.integrable μm h
  let hπ0 := (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (hπ0.choose : v.adicCompletion F) hπ0.choose_spec.ne_zero
  let Δ : ℝ≥0 := distribHaarChar (G := (v.adicCompletion F)ˣ) (v.adicCompletion F) π
  refine ⟨1 - (Δ : ℂ), fun g ↦ ?_⟩
  let U := (v.adicCompletionIntegers F).units
  let μU := finiteLocalMultiplicativeTamagawaMeasure F v
  have hUo : IsOpen (U : Set (v.adicCompletion F)ˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hUc : IsCompact (U : Set (v.adicCompletion F)ˣ) :=
    Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr
      (compactSpace_adicCompletionIntegers v))
  have hUm : MeasurableSet (U : Set (v.adicCompletion F)ˣ) := hUo.measurableSet
  have : μU.IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let ν := μU.restrict (U : Set (v.adicCompletion F)ˣ)
  have : IsFiniteMeasure ν :=
    ⟨by simpa [ν, Measure.restrict_apply_univ] using hUc.measure_lt_top⟩
  let m : ℝ := μU.real U
  have hm : 0 < m := (finitePlacePrincipalValue_integrable v π g 1).1
  let G : v.adicCompletion F → (v.adicCompletion F)ˣ → ℂ := fun x u ↦
    g (Multiplicative.ofAdd ((↑u⁻¹ : v.adicCompletion F) * ((↑π⁻¹ : v.adicCompletion F) * x)))
  have hG : Continuous (Function.uncurry G) :=
    (schwartzBruhat_continuous g).comp (continuous_ofAdd.comp
      ((Units.continuous_val.comp (continuous_inv.comp continuous_snd)).mul
        (continuous_const.mul continuous_fst)))
  have hgc : Continuous fun x : v.adicCompletion F ↦ g (Multiplicative.ofAdd x) :=
    (schwartzBruhat_continuous g).comp continuous_ofAdd
  have hP (x : v.adicCompletion F) : finitePlacePrincipalValue v g (Multiplicative.ofAdd x) =
      g (Multiplicative.ofAdd x) - (m : ℂ)⁻¹ * ∫ u, G x u ∂ν :=
    (finitePlacePrincipalValue_spec v π hπ0.choose_spec g _).trans rfl
  have hinner (u : (v.adicCompletion F)ˣ) (hu : u ∈ U) :
      ∫ x, G x u ∂μ = (Δ : ℂ) * ∫ x, g (Multiplicative.ofAdd x) ∂μ := by
    have h := adelePrincipalValue_mem_polarSubspace_integral_scale v π u hu
      (fun y ↦ g (Multiplicative.ofAdd y)) hgc
    exact h.trans (by rw [Complex.real_smul])
  have hprod : Integrable (Function.uncurry G) (μ.prod ν) := by
    rw [integrable_prod_iff' hG.aestronglyMeasurable]
    constructor
    · refine (ae_restrict_iff' hUm).mpr (.of_forall fun u hu ↦ ?_)
      have hmap := adelePrincipalValue_mem_polarSubspace_map_mul v (u⁻¹ * π⁻¹)
      have h1 : Integrable (fun y ↦ g (Multiplicative.ofAdd y))
          (μ.map fun x ↦ ((u⁻¹ * π⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) := by
        rw [hmap]
        exact (hint g).smul_measure ENNReal.coe_ne_top
      refine (h1.comp_measurable (continuous_const.mul continuous_id).measurable).congr
        (.of_forall fun x ↦ ?_)
      simp [G, Function.uncurry, mul_assoc]
    · have hc : ∀ u ∈ (U : Set (v.adicCompletion F)ˣ),
          ∫ x, ‖Function.uncurry G (x, u)‖ ∂μ =
            (Δ : ℝ) • ∫ x, ‖g (Multiplicative.ofAdd x)‖ ∂μ := fun u hu ↦
        adelePrincipalValue_mem_polarSubspace_integral_scale v π u hu
          (fun y ↦ ‖g (Multiplicative.ofAdd y)‖) hgc.norm
      refine (integrable_const ((Δ : ℝ) • ∫ x, ‖g (Multiplicative.ofAdd x)‖ ∂μ)).congr ?_
      exact ((ae_restrict_iff' hUm).mpr (.of_forall fun u hu ↦ (hc u hu).symm))
  have hA : Integrable (fun x ↦ ∫ u, G x u ∂ν) μ := hprod.integral_prod_left
  have hν : ν.real Set.univ = m := by
    simp [ν, m, Measure.real]
  calc ∫ x, finitePlacePrincipalValue v g (Multiplicative.ofAdd x) ∂μ
      = ∫ x, (g (Multiplicative.ofAdd x) - (m : ℂ)⁻¹ * ∫ u, G x u ∂ν) ∂μ :=
        integral_congr_ae (.of_forall hP)
    _ = ∫ x, g (Multiplicative.ofAdd x) ∂μ - (m : ℂ)⁻¹ * ∫ x, ∫ u, G x u ∂ν ∂μ := by
        rw [integral_sub (hint g) (hA.const_mul _), integral_const_mul]
    _ = ∫ x, g (Multiplicative.ofAdd x) ∂μ - (m : ℂ)⁻¹ * ∫ u, ∫ x, G x u ∂μ ∂ν := by
        rw [integral_integral_swap hprod]
    _ = ∫ x, g (Multiplicative.ofAdd x) ∂μ -
          (m : ℂ)⁻¹ * ∫ u, (Δ : ℂ) * ∫ x, g (Multiplicative.ofAdd x) ∂μ ∂ν := by
        rw [setIntegral_congr_fun hUm fun u hu ↦ hinner u hu]
    _ = (1 - (Δ : ℂ)) * ∫ x, g (Multiplicative.ofAdd x) ∂μ := by
        rw [integral_const, hν, Complex.real_smul]
        have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
        field_simp

/-- The global inclusion of an S-local test keeps its value at zero. -/
private theorem adelePrincipalValue_mem_polarSubspace_toGlobal_zero (S : Finset V) (k : ℬₛ(S)) :
    sAdeleSchwartzToGlobal F S k (Multiplicative.ofAdd 0) = k (Multiplicative.ofAdd 0) := by
  rw [sAdeleSchwartzToGlobal_apply, if_pos fun w _ ↦ (w.adicCompletionIntegers F).zero_mem,
    map_zero]

/-- Integrating the global inclusion of an S-local test multiplies its S-local integral by a
constant, the mass of the integral tail. -/
private theorem sAdeleSchwartzToGlobal_integral_scale (S : Finset V) :
    ∃ M : ℂ, M ≠ 0 ∧ ∀ k : ℬₛ(S),
      ∫ x, sAdeleSchwartzToGlobal F S k (Multiplicative.ofAdd x) ∂additiveTamagawaMeasure F =
        M * ∫ y, k (Multiplicative.ofAdd y) ∂sAdditiveTamagawaMeasure F S := by
  obtain ⟨c, hc, -, hm, -⟩ := sAdeleProjection_dual_masses F S
  refine ⟨((c : ℝ) : ℂ), ?_, fun k ↦ ?_⟩
  · exact_mod_cast hc
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (v : V) : MeasurableSpace (v.adicCompletion F) := borel _
  let (v : V) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let (v : V) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let (v : V) : SecondCountableTopology (v.adicCompletion F) := secondCountable_of_proper
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  let : BorelSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (BorelSpace ((w : InfinitePlace F) → w.Completion))
  let : MeasurableSpace (SAdeleRing F S) := instMeasurableSpaceSAdeleRing F S
  let : BorelSpace (SAdeleRing F S) :=
    inferInstanceAs (BorelSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  let : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
  let : BorelSpace (AdeleRing (𝓞 F) F) := ⟨rfl⟩
  let I := (integralAdelesOutside F S : Set (AdeleRing (𝓞 F) F))
  have hIo : IsOpen I := by
    have h : I = Prod.snd ⁻¹' {a : FiniteAdeleRing (𝓞 F) F | ∀ v ∈ (S : Set V)ᶜ,
        a v ∈ v.adicCompletionIntegers F} := by
      ext a
      simp only [I, SetLike.mem_coe, integralAdelesOutside, Subring.mem_iInf]
      rfl
    rw [h]
    exact (isOpen_restrictedProduct_forall_mem (G := fun v : V ↦ v.adicCompletion F)
      (A := fun v ↦ v.adicCompletionIntegers F) ((S : Set V)ᶜ)
      (fun _ _ ↦ Valued.isOpen_valuationSubring _)).preimage continuous_snd
  have hk : Continuous fun y : SAdeleRing F S ↦ k (Multiplicative.ofAdd y) :=
    (schwartzBruhat_continuous k).comp continuous_ofAdd
  have hfun : (fun x ↦ sAdeleSchwartzToGlobal F S k (Multiplicative.ofAdd x)) =
      I.indicator (fun x ↦ k (Multiplicative.ofAdd (adeleProjection F S x))) := by
    funext x
    rw [sAdeleSchwartzToGlobal_apply]
    by_cases hx : x ∈ I
    · rw [Set.indicator_of_mem hx, if_pos]
      intro w hw
      have hx' : x ∈ integralAdelesOutside F S := hx
      simp only [integralAdelesOutside, Subring.mem_iInf] at hx'
      exact hx' w hw
    · rw [Set.indicator_of_notMem hx, if_neg]
      intro hall
      apply hx
      change x ∈ integralAdelesOutside F S
      simp only [integralAdelesOutside, Subring.mem_iInf]
      exact hall
  rw [hfun, integral_indicator hIo.measurableSet]
  have h2 := integral_map (μ := (additiveTamagawaMeasure F).restrict I)
    hm.measurable.aemeasurable (f := fun y ↦ k (Multiplicative.ofAdd y))
    (by rw [hm.map_eq]; exact hk.aestronglyMeasurable)
  refine h2.symm.trans ?_
  rw [hm.map_eq, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

private theorem adelePrincipalValue_mem_polarSubspace_toGlobal_integral (S : Finset V) :
    ∃ M : ℂ, ∀ k : ℬₛ(S),
      ∫ x, sAdeleSchwartzToGlobal F S k (Multiplicative.ofAdd x) ∂additiveTamagawaMeasure F =
        M * ∫ y, k (Multiplicative.ofAdd y) ∂sAdditiveTamagawaMeasure F S := by
  obtain ⟨M, -, hM⟩ := sAdeleSchwartzToGlobal_integral_scale (F := F) S
  exact ⟨M, hM⟩

/-- Insertion preserves and detects both zero moments. Fourier evaluation at zero
is multiplied by the nonzero additive mass of the integer tail. -/
theorem sAdeleSchwartzToGlobal_mem_polarSubspace_iff (S : Finset V) (f : ℬₛ(S)) :
    sAdeleSchwartzToGlobal F S f ∈ adelePolarSubspace F ↔
      f (Multiplicative.ofAdd 0) = 0 ∧ sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0 := by
  obtain ⟨M, hM, h⟩ := sAdeleSchwartzToGlobal_integral_scale (F := F) S
  rw [mem_adelePolarSubspace,
    adelePrincipalValue_mem_polarSubspace_toGlobal_zero,
    (adeleSchwartzFourier_apply_zero _).2, h f, ← sAdeleSchwartzFourier_apply_zero,
    mul_eq_zero, or_iff_right hM]

open scoped TensorProduct in
/-- On a pure tensor the S-local integral is the product of the archimedean integral and
the local integrals. -/
private theorem adelePrincipalValue_mem_polarSubspace_integral_tmul (S : Finset V) :
    ∃ Φ : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) → ℂ,
      ∀ (a : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
        (g : ∀ w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F))),
        ∫ y, (sAdeleSchwartz_inductiveTensor_equiv F S).choose (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))
            (Multiplicative.ofAdd y) ∂sAdditiveTamagawaMeasure F S =
          Φ a * ∏ w : S, ∫ t, g w (Multiplicative.ofAdd t)
            ∂finiteLocalAdditiveTamagawaMeasure F w.val := by
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (v : V) : MeasurableSpace (v.adicCompletion F) := borel _
  let (v : V) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let (v : V) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let (v : V) : SecondCountableTopology (v.adicCompletion F) := secondCountable_of_proper
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : V) : (finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  refine ⟨fun a ↦ ∫ z, a (Multiplicative.ofAdd z) ∂Measure.pi (infiniteLocalAdditiveTamagawaMeasure F),
    fun a g ↦ ?_⟩
  have he := (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a g
  refine (integral_congr_ae (.of_forall he)).trans ?_
  exact (integral_prod_mul (μ := Measure.pi (infiniteLocalAdditiveTamagawaMeasure F))
    (ν := Measure.pi fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)
    (fun z ↦ a (Multiplicative.ofAdd z))
    (fun z ↦ ∏ w : S, g w (Multiplicative.ofAdd (z w)))).trans
    (congrArg _ (integral_fintype_prod_eq_prod (fun w : S ↦ fun t ↦ g w (Multiplicative.ofAdd t))))

open scoped TensorProduct in
/-- Through a stage containing the selected places, the global principal value of an
inserted test is the insertion of the S-local principal value. The integer tail indicator
is obtained by slicing the inserted test `k₀`, whose value at zero is one. -/
private theorem adelePrincipalValue_mem_polarSubspace_toGlobal_comm {S T : Finset V}
    (hTS : T ⊆ S) (k₀ : ℬₛ(S)) (hk₀ : k₀ (Multiplicative.ofAdd 0) = 1) (k : ℬₛ(S)) :
    adelePrincipalValue F T (sAdeleSchwartzToGlobal F S k) =
      sAdeleSchwartzToGlobal F S (sAdelePrincipalValue F hTS k) := by
  let Tl := SchwartzBruhat (Multiplicative (FiniteAdeleTail F S))
  let e := (sAdeleTailSchwartz_inductiveTensor_equiv F S).choose
  have he := (sAdeleTailSchwartz_inductiveTensor_equiv F S).choose_spec
  let ev : ℬₛ(S) →ₗ[ℂ] ℂ :=
    { toFun := fun a ↦ a (Multiplicative.ofAdd 0)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let L : ℬₛ(S) ⊗[ℂ] Tl →ₗ[ℂ] Tl := TensorProduct.lift ((LinearMap.lsmul ℂ Tl).comp ev)
  let c : Tl := L (e.symm (sAdeleSchwartzToGlobal F S k₀))
  have hc (y : FiniteAdeleTail F S) : c (Multiplicative.ofAdd y) =
      if ∀ w, y w ∈ w.val.adicCompletionIntegers F then 1 else 0 := by
    let f : ∀ w : V, w.adicCompletion F := fun w ↦ if h : w ∈ S then 0 else y ⟨w, h⟩
    have hf : ∀ᶠ w in Filter.cofinite, f w ∈ w.adicCompletionIntegers F := by
      filter_upwards [S.eventually_cofinite_notMem, Filter.eventually_comap.mp
        (y.2.filter_mono (Filter.comap_cofinite_le Subtype.val))] with w hw h
      simp only [f, dif_neg hw]
      exact h ⟨w, hw⟩ rfl
    let z : FiniteAdeleRing (𝓞 F) F := ⟨f, hf⟩
    let x : AdeleRing (𝓞 F) F := (0, z)
    have hx (w : V) (hw : w ∉ S) : x.2 w = y ⟨w, hw⟩ := dif_neg hw
    have hp : adeleProjection F S x = 0 :=
      Prod.ext rfl (funext fun w ↦ (dif_pos w.2 : f w.val = 0))
    have ht : finiteAdeleTailProjection F S x.2 = y := by
      apply RestrictedProduct.ext
      intro w
      exact dif_neg w.2
    let evy : Tl →ₗ[ℂ] ℂ :=
      { toFun := fun b ↦ b (Multiplicative.ofAdd y)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    let evx : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)) →ₗ[ℂ] ℂ :=
      { toFun := fun b ↦ b (Multiplicative.ofAdd x)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have key : evy ∘ₗ L = evx ∘ₗ (e.toLinearMap : InductiveTensor ℬₛ(S) Tl →ₗ[ℂ] _) := by
      refine TensorProduct.ext' fun a b ↦ ?_
      change (a (Multiplicative.ofAdd 0) • b) (Multiplicative.ofAdd y) =
        e (a ⊗ₜ[ℂ] b) (Multiplicative.ofAdd x)
      rw [he a b x, hp, ht]
      rfl
    have h2 : c (Multiplicative.ofAdd y) =
        sAdeleSchwartzToGlobal F S k₀ (Multiplicative.ofAdd x) :=
      (LinearMap.congr_fun key (e.symm (sAdeleSchwartzToGlobal F S k₀))).trans
        (congrArg (fun φ : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)) ↦
          φ (Multiplicative.ofAdd x)) (e.apply_symm_apply _))
    rw [h2, sAdeleSchwartzToGlobal_apply, hp, hk₀]
    by_cases hy : ∀ w, y w ∈ w.val.adicCompletionIntegers F
    · rw [if_pos hy, if_pos fun w hw ↦ by rw [hx w hw]; exact hy ⟨w, hw⟩]
    · rw [if_neg hy, if_neg fun h ↦ hy fun w ↦ by rw [← hx w.val w.2]; exact h w.val w.2]
  have hslice (a : ℬₛ(S)) : e (a ⊗ₜ[ℂ] c) = sAdeleSchwartzToGlobal F S a := by
    apply Subtype.ext
    funext x
    change e (a ⊗ₜ[ℂ] c) (Multiplicative.ofAdd x.toAdd) =
      sAdeleSchwartzToGlobal F S a (Multiplicative.ofAdd x.toAdd)
    rw [he a c x.toAdd, hc, sAdeleSchwartzToGlobal_apply]
    by_cases hx : ∀ w : V, w ∉ S → x.toAdd.2 w ∈ w.adicCompletionIntegers F
    · rw [if_pos hx, if_pos (show ∀ w : {w : V // w ∉ S},
        finiteAdeleTailProjection F S x.toAdd.2 w ∈ w.val.adicCompletionIntegers F from
          fun w ↦ hx w.val w.2), mul_one]
    · rw [if_neg hx, if_neg (show ¬ ∀ w : {w : V // w ∉ S},
        finiteAdeleTailProjection F S x.toAdd.2 w ∈ w.val.adicCompletionIntegers F from
          fun h ↦ hx fun w hw ↦ h ⟨w, hw⟩), mul_zero]
  rw [← hslice k, ← hslice (sAdelePrincipalValue F hTS k)]
  exact adelePrincipalValue_tmul hTS k c

open scoped TensorProduct in
/-- On a stage containing the selected places, the S-local principal value multiplies the
value at zero and the Fourier value at zero of the inserted test by constants. -/
private theorem adelePrincipalValue_mem_polarSubspace_stage {S T : Finset V} (hTS : T ⊆ S)
    (k : ℬₛ(S)) :
    ∃ c₀ c₁ : ℂ,
      sAdeleSchwartzToGlobal F S (sAdelePrincipalValue F hTS k) (Multiplicative.ofAdd 0) =
        c₀ * sAdeleSchwartzToGlobal F S k (Multiplicative.ofAdd 0) ∧
      adeleSchwartzFourier (sAdeleSchwartzToGlobal F S (sAdelePrincipalValue F hTS k))
          (Multiplicative.ofAdd 0) =
        c₁ * adeleSchwartzFourier (sAdeleSchwartzToGlobal F S k) (Multiplicative.ofAdd 0) := by
  let e' := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  have he' := (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec
  let P := sAdelePrincipalValue F hTS
  have hpure (a : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
      (g : ∀ w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F))) :
      P (e' (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) = e' (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w,
        if w.val ∈ T then finitePlacePrincipalValue w.val (g w) else g w)) :=
    sAdelePrincipalValue_tmul hTS a g
  let Λ₀ : ℬₛ(S) →ₗ[ℂ] ℂ :=
    { toFun := fun h ↦ sAdeleSchwartzToGlobal F S h (Multiplicative.ofAdd 0)
      map_add' := fun x y ↦ by rw [map_add]; rfl
      map_smul' := fun r x ↦ by rw [map_smul]; rfl }
  let Λ₁ : ℬₛ(S) →ₗ[ℂ] ℂ :=
    { toFun := fun h ↦ adeleSchwartzFourier (sAdeleSchwartzToGlobal F S h) (Multiplicative.ofAdd 0)
      map_add' := fun x y ↦ by
        rw [map_add]
        exact congrArg Prod.snd
          (map_add adelePolarValues (sAdeleSchwartzToGlobal F S x) (sAdeleSchwartzToGlobal F S y))
      map_smul' := fun r x ↦ by
        rw [map_smul]
        exact congrArg Prod.snd (map_smul adelePolarValues r (sAdeleSchwartzToGlobal F S x)) }
  choose κ hκ using fun w : V ↦ adelePrincipalValue_mem_polarSubspace_localIntegral (F := F) w
  obtain ⟨M, hM⟩ := adelePrincipalValue_mem_polarSubspace_toGlobal_integral (F := F) S
  obtain ⟨Φ, hΦ⟩ := adelePrincipalValue_mem_polarSubspace_integral_tmul (F := F) S
  let gP (g : ∀ w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F))) (w : S) :=
    if w.val ∈ T then finitePlacePrincipalValue w.val (g w) else g w
  have hyp₀ : ∀ (a : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
      (g : ∀ w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F))),
      Λ₀ (P (e' (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)))) =
        (∏ w : S, if w.val ∈ T then (0 : ℂ) else 1) * Λ₀ (e' (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) := by
    intro a g
    have hL := (adelePrincipalValue_mem_polarSubspace_toGlobal_zero S _).trans (he' a (gP g) 0)
    have hR := (adelePrincipalValue_mem_polarSubspace_toGlobal_zero S _).trans (he' a g 0)
    refine (congrArg Λ₀ (hpure a g)).trans ((hL.trans ?_).trans (congrArg (_ * ·) hR.symm))
    have hfac (w : S) : gP g w (Multiplicative.ofAdd ((0 : SAdeleRing F S).2 w)) =
        (if w.val ∈ T then (0 : ℂ) else 1) *
          g w (Multiplicative.ofAdd ((0 : SAdeleRing F S).2 w)) := by
      simp only [gP]
      split_ifs
      · rw [zero_mul]
        exact adelePrincipalValue_mem_polarSubspace_localZero w.val (g w)
      · rw [one_mul]
    rw [Finset.prod_congr rfl fun w _ ↦ hfac w, Finset.prod_mul_distrib]
    ring
  have hyp₁ : ∀ (a : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
      (g : ∀ w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F))),
      Λ₁ (P (e' (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)))) =
        (∏ w : S, if w.val ∈ T then κ w.val else 1) * Λ₁ (e' (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) := by
    intro a g
    have hL := ((adeleSchwartzFourier_apply_zero _).2.trans (hM _)).trans
      (congrArg (M * ·) (hΦ a (gP g)))
    have hR := ((adeleSchwartzFourier_apply_zero _).2.trans (hM _)).trans
      (congrArg (M * ·) (hΦ a g))
    refine (congrArg Λ₁ (hpure a g)).trans ((hL.trans ?_).trans (congrArg (_ * ·) hR.symm))
    have hfac (w : S) : ∫ t, gP g w (Multiplicative.ofAdd t)
        ∂finiteLocalAdditiveTamagawaMeasure F w.val =
          (if w.val ∈ T then κ w.val else 1) *
            ∫ t, g w (Multiplicative.ofAdd t) ∂finiteLocalAdditiveTamagawaMeasure F w.val := by
      simp only [gP]
      split_ifs
      · exact hκ w.val (g w)
      · rw [one_mul]
    rw [Finset.prod_congr rfl fun w _ ↦ hfac w, Finset.prod_mul_distrib]
    ring
  have i₀ := adelePrincipalValue_mem_polarSubspace_ind
    (D := fun w : S ↦ SchwartzBruhat (Multiplicative (w.val.adicCompletion F))) e' P Λ₀ _
    (by with_reducible exact hyp₀) k
  have i₁ := adelePrincipalValue_mem_polarSubspace_ind
    (D := fun w : S ↦ SchwartzBruhat (Multiplicative (w.val.adicCompletion F))) e' P Λ₁ _
    (by with_reducible exact hyp₁) k
  exact ⟨_, _, i₀, i₁⟩

/-- Paper: (11.1.2.3), p. 480. A global finite-place principal value preserves
the two polar vanishing conditions. -/
theorem adelePrincipalValue_mem_polarSubspace (T : Finset V) (f : ℬ₀) :
    adelePrincipalValue F T f.val ∈ adelePolarSubspace F := by
  obtain ⟨hf0, hfF⟩ := (mem_adelePolarSubspace f.val).1 f.2
  obtain ⟨S₁, h₁, hh₁⟩ := sAdeleSchwartzToGlobal_exhaustive F f.val
  obtain ⟨S₂, h₂, hh₂⟩ := sAdeleSchwartzToGlobal_exhaustive F
    (adelicStandardGaussian (F := F) (1 : PontryaginDual C𝔽))
  have hS₁ : S₁ ⊆ S₁ ∪ S₂ ∪ T := Finset.subset_union_left.trans Finset.subset_union_left
  have hS₂ : S₂ ⊆ S₁ ∪ S₂ ∪ T := Finset.subset_union_right.trans Finset.subset_union_left
  have hTS : T ⊆ S₁ ∪ S₂ ∪ T := Finset.subset_union_right
  have hk : sAdeleSchwartzToGlobal F _ (sAdeleSchwartzTransition F hS₁ h₁) = f.val :=
    (LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp F hS₁) h₁).trans hh₁
  have hk₂ : sAdeleSchwartzTransition F hS₂ h₂ (Multiplicative.ofAdd 0) ≠ 0 := by
    have h2' : sAdeleSchwartzToGlobal F _ (sAdeleSchwartzTransition F hS₂ h₂) =
        sAdeleSchwartzToGlobal F S₂ h₂ :=
      LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp F hS₂) h₂
    rw [← adelePrincipalValue_mem_polarSubspace_toGlobal_zero, h2', hh₂,
      adelicStandardGaussian_trivial_zero]
    exact pow_ne_zero _ (inv_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  have hk₀ : ((sAdeleSchwartzTransition F hS₂ h₂ (Multiplicative.ofAdd 0))⁻¹ •
      sAdeleSchwartzTransition F hS₂ h₂) (Multiplicative.ofAdd 0) = 1 :=
    inv_mul_cancel₀ hk₂
  obtain ⟨c₀, c₁, h0, h1⟩ :=
    adelePrincipalValue_mem_polarSubspace_stage hTS (sAdeleSchwartzTransition F hS₁ h₁)
  rw [← hk, adelePrincipalValue_mem_polarSubspace_toGlobal_comm hTS _ hk₀,
    mem_adelePolarSubspace]
  rw [hk] at h0 h1
  exact ⟨h0.trans (by rw [hf0, mul_zero]), h1.trans (by rw [hfF, mul_zero])⟩

local notation "P(" T ", " f ")" =>
  (⟨adelePrincipalValue F T (f).val, adelePrincipalValue_mem_polarSubspace T f⟩ : ℬ₀)
local notation "θ(" s ", " ω ", " f ")" =>
  (memLp_homogeneousTheta_zeroLine s ω f).toLp (homogeneousAdelicTheta ω (f).val)

/-- Paper: (11.1.2.5), p. 480. The uncut stage is the closure of the homogeneous
polar-free theta image after applying the selected finite-place principal values.
Deviation: The image is presented by its linear span in the full weighted L² model. -/
def sLocalUncutCarving (s : ℝ) (ω : PontryaginDual C₁) (T : Finset V) :
    Submodule ℂ (W(s)) :=
  (Submodule.span ℂ (range (fun f : ℬ₀ ↦ θ(s, ω, P(T, f))))).topologicalClosure

/-- Conjugating `map id P` by an equivalence gives the identity when `P` fixes every vector.
Stated in the shape of `sAdelePrincipalValue`, so that it applies syntactically. -/
private theorem sLocalUncutCarving_empty_conj_left {E G N : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (P : G →ₗ[ℂ] G) (hP : ∀ x, P x = x) :
    e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) P).comp
      e.symm.toLinearMap) = LinearMap.id := by
  have hP' : P = LinearMap.id := LinearMap.ext hP
  subst hP'
  refine LinearMap.ext fun x ↦ ?_
  have h := LinearMap.congr_fun (TensorProduct.map_id (R := ℂ) (M := E) (N := G)) (e.symm x)
  exact (congrArg e h).trans (e.apply_symm_apply x)

/-- Conjugating `map P id` by an equivalence gives the identity when `P` fixes every vector.
Stated in the shape of `adelePrincipalValue`, so that it applies syntactically. -/
private theorem sLocalUncutCarving_empty_conj_right {E G N : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (P : E →ₗ[ℂ] E) (hP : ∀ x, P x = x) :
    e.toLinearMap.comp ((TensorProduct.map P (LinearMap.id : G →ₗ[ℂ] G)).comp
      e.symm.toLinearMap) = LinearMap.id := by
  have hP' : P = LinearMap.id := LinearMap.ext hP
  subst hP'
  refine LinearMap.ext fun x ↦ ?_
  have h := LinearMap.congr_fun (TensorProduct.map_id (R := ℂ) (M := E) (N := G)) (e.symm x)
  exact (congrArg e h).trans (e.apply_symm_apply x)

open scoped TensorProduct in
/-- A tensor power of identity maps fixes every vector of the finest locally convex copy. -/
private theorem sLocalUncutCarving_empty_piMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (f : ∀ i, M i →ₗ[ℂ] M i) (hf : ∀ i, f i = LinearMap.id)
    (x : FinestLocallyConvex (⨂[ℂ] i, M i)) :
    (PiTensorProduct.map f : FinestLocallyConvex (⨂[ℂ] i, M i) →ₗ[ℂ]
      FinestLocallyConvex (⨂[ℂ] i, M i)) x = x := by
  have : f = fun _ ↦ LinearMap.id := funext hf
  subst this
  rw [PiTensorProduct.map_id]
  rfl

/-- With no selected places the S-local principal value is the identity. -/
private theorem sLocalUncutCarving_empty_sPV (h : (∅ : Finset V) ⊆ ∅) :
    sAdelePrincipalValue F h = LinearMap.id := by
  unfold sAdelePrincipalValue
  exact sLocalUncutCarving_empty_conj_left _ _
    (sLocalUncutCarving_empty_piMap _ fun w ↦ absurd w.2 (Finset.notMem_empty _))

/-- With no selected places the global principal value is the identity. -/
private theorem sLocalUncutCarving_empty_PV : adelePrincipalValue F (∅ : Finset V) = LinearMap.id := by
  unfold adelePrincipalValue
  exact sLocalUncutCarving_empty_conj_right _ _ fun x ↦
    LinearMap.congr_fun (sLocalUncutCarving_empty_sPV _) x

/-- Paper: (11.1.2.5), p. 480. The empty stage is the closure of the unrestricted
homogeneous polar-free theta image.
Deviation: Sanity check for the uncut stage. -/
theorem sLocalUncutCarving_empty (s : ℝ) (ω : PontryaginDual C₁) :
    sLocalUncutCarving s ω ∅ =
      (Submodule.span ℂ (range (fun f : ℬ₀ ↦ θ(s, ω, f)))).topologicalClosure := by
  have hP : ∀ f : ℬ₀, adelePrincipalValue F ∅ f.val = f.val := fun f ↦
    LinearMap.ext_iff.mp sLocalUncutCarving_empty_PV f.val
  simp only [sLocalUncutCarving, hP]

/-- The norm-one isotype of the ambient space is closed: it is an intersection of kernels of
continuous operators. -/
private theorem sLocalCutoffCarving_le_cutoffIsotype_closed (s : ℝ) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) : IsClosed (Wω(s, hs, ω) : Set (W(s))) := by
  simp only [actionIsotype, Submodule.coe_iInf]
  refine isClosed_iInter fun g ↦ ?_
  have hc : Continuous fun u : W(s) ↦ ((hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs).comp
      (ideleClassNorm F).ker.subtype) g u - (ω g : ℂ) • u :=
    (((hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs).comp
      (ideleClassNorm F).ker.subtype) g).continuous.sub (continuous_const_smul (ω g : ℂ))
  exact isClosed_eq hc continuous_const

/-- Homogeneous theta of a polar-free test lies in the norm-one isotype of the ambient space:
it is the inclusion of the homogeneous theta class of §10.1, on which norm-one translation acts
by the character. -/
private theorem sLocalCutoffCarving_le_cutoffIsotype_theta (s : ℝ) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (f : ℬ₀) : θ(s, ω, f) ∈ Wω(s, hs, ω) := by
  obtain ⟨j, -, -, hj⟩ :=
    exists_globalHomogeneousThetaSobolevInclusion (F := F) (a := 0) (le_refl (0 : ℝ)) hs ω
  have hf := (mem_adelePolarSubspace f.val).mp f.property
  let x : ↥(globalPolarFreeThetaSubmodule (F := F) ω) :=
    ⟨Submodule.Quotient.mk f.val,
      (mem_globalPolarFreeThetaSubmodule ω _).mpr ⟨f.val, hf.1, hf.2, rfl⟩⟩
  have hx := (hj f x rfl).2.trans (Filter.EventuallyEq.of_eq (modulationWeight_zero m𝔽 _))
  have hx' : ((j x).val.val : C𝔽 → ℂ) =ᵐ[ν(s)] (homogeneousAdelicTheta ω f.val : C𝔽 → ℂ) :=
    (withDensity_absolutelyContinuous _ _).ae_le hx
  have heq : θ(s, ω, f) = (j x).val.val := Lp.ext ((MemLp.coeFn_toLp _).trans hx'.symm)
  have hiso := (mem_actionIsotype _ ω _).mp (j x).property
  have hspec := (exists_globalThetaSobolevAction (F := F) 0 (le_refl (0 : ℝ)) hs).choose_spec.1
  rw [mem_actionIsotype]
  intro h
  rw [heq]
  exact (hspec h.val (j x).val).symm.trans (congrArg Subtype.val (hiso h))

/-- Paper: (11.1.2.5), p. 480. Before any prime condition the uncut stage is the
norm-one isotype of the global theta completion from Definition 10.1.1.1. -/
theorem sLocalUncutCarving_empty_eq_globalThetaSobolev (s : ℝ) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :
    sLocalUncutCarving s ω ∅ =
      globalThetaSobolev F 0 (α := 0) (β := 0) le_rfl hs ⊓ Wω(s, hs, ω) := by
  obtain ⟨j, -, hdense, hj⟩ :=
    exists_globalHomogeneousThetaSobolevInclusion (F := F) (a := 0) (le_refl (0 : ℝ)) hs ω
  have hspec := (exists_globalThetaSobolevAction (F := F) 0 (le_refl (0 : ℝ)) hs).choose_spec.1
  -- Every vector of the range of `j` is a homogeneous theta, and conversely.
  have hθ (f : ℬ₀) (x : ↥(globalPolarFreeThetaSubmodule (F := F) ω))
      (hx : x.val = Submodule.Quotient.mk f.val) : θ(s, ω, f) = (j x).val.val := by
    have h := (hj f x hx).2.trans (Filter.EventuallyEq.of_eq (modulationWeight_zero m𝔽 _))
    have h' : ((j x).val.val : C𝔽 → ℂ) =ᵐ[ν(s)] (homogeneousAdelicTheta ω f.val : C𝔽 → ℂ) :=
      (withDensity_absolutelyContinuous _ _).ae_le h
    exact Lp.ext ((MemLp.coeFn_toLp _).trans h'.symm)
  rw [sLocalUncutCarving_empty]
  apply le_antisymm
  · refine Submodule.topologicalClosure_minimal _ ?_
      ((Submodule.isClosed_topologicalClosure _).inter
        (sLocalCutoffCarving_le_cutoffIsotype_closed s hs ω))
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, rfl⟩
    have hf := (mem_adelePolarSubspace f.val).mp f.property
    let x : ↥(globalPolarFreeThetaSubmodule (F := F) ω) :=
      ⟨Submodule.Quotient.mk f.val,
        (mem_globalPolarFreeThetaSubmodule ω _).mpr ⟨f.val, hf.1, hf.2, rfl⟩⟩
    refine ⟨?_, sLocalCutoffCarving_le_cutoffIsotype_theta s hs ω f⟩
    have hm := (j x).val.property
    rw [← hθ f x rfl] at hm
    exact hm
  · intro u hu
    obtain ⟨huH, huW⟩ := Submodule.mem_inf.mp hu
    let y₀ : ↥(globalThetaSobolev F 0 (α := 0) (β := 0) le_rfl hs) := ⟨u, huH⟩
    have hy₀ : y₀ ∈ actionIsotype
        ((exists_globalThetaSobolevAction (F := F) 0 (le_refl (0 : ℝ)) hs).choose.comp
          (ideleClassNorm F).ker.subtype) ω := by
      rw [mem_actionIsotype]
      intro h
      exact Subtype.ext ((hspec h.val y₀).trans ((mem_actionIsotype _ ω u).mp huW h))
    have hι : Continuous fun z : ↥(actionIsotype
        ((exists_globalThetaSobolevAction (F := F) 0 (le_refl (0 : ℝ)) hs).choose.comp
          (ideleClassNorm F).ker.subtype) ω) ↦ (z.val.val : W(s)) :=
      continuous_subtype_val.comp continuous_subtype_val
    let Φ : ℬ₀ → ↥(globalPolarFreeThetaSubmodule (F := F) ω) := fun f ↦
      ⟨Submodule.Quotient.mk f.val, (mem_globalPolarFreeThetaSubmodule ω _).mpr
        ⟨f.val, ((mem_adelePolarSubspace f.val).mp f.property).1,
          ((mem_adelePolarSubspace f.val).mp f.property).2, rfl⟩⟩
    have hΦ : Function.Surjective Φ := by
      intro x
      obtain ⟨f', hf', hx⟩ := x.property
      exact ⟨⟨f', hf'⟩, Subtype.ext hx⟩
    have hd2 : DenseRange (j ∘ Φ) := hdense.comp hΦ.denseRange j.continuous
    have hcl := image_closure_subset_closure_image hι ⟨⟨y₀, hy₀⟩, hd2 _, rfl⟩
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    refine closure_mono ?_ hcl
    rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
    change (j (Φ f)).val.val ∈ _
    rw [← hθ f (Φ f) rfl]
    exact Submodule.subset_span ⟨f, rfl⟩

/-- Paper: (11.1.2.3), p. 480. The cutoff stage is the closure of the linear
space obtained by applying the cutoff to the restricted theta tests.
Deviation: Read the printed P as the principal value PV used on p. 481. The
definition accepts any measurable norm band, including both in `sLocalCarvingBand`. -/
def sLocalCutoffCarving (s : ℝ) (ω : PontryaginDual C₁) (T : Finset V)
    (J : Set ℝ) (hJ : MeasurableSet J) : Submodule ℂ (W(s)) :=
  (Submodule.span ℂ (range (fun f : ℬ₀ ↦ M(s, J, hJ) (θ(s, ω, P(T, f)))))).topologicalClosure

/-- The absolute cutoff commutes with translation by a norm-one class, which does not move
the idelic norm. -/
private theorem sLocalCutoffCarving_le_cutoffIsotype_comm (s : ℝ) (hs : 0 ≤ s)
    (J : Set ℝ) (hJ : MeasurableSet J) (h : C₁) (u : W(s)) :
    M(s, J, hJ) (hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs h.val u) =
      hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs h.val (M(s, J, hJ) u) := by
  have hn : Continuous norm𝔽 :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hdens : Continuous (intervalSobolevDensity 0 0 s) := by
    unfold intervalSobolevDensity
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).max
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
      (Continuous.rpow_const (f := fun x : ℝ ↦ 1 + x ^ 2) (by fun_prop)
        fun x ↦ Or.inl (by positivity))
  have hpos (g : C𝔽) : 0 < intervalSobolevDensity 0 0 s (Real.log (norm𝔽 g)) :=
    mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  have hνμ : ν(s) ≪ μ𝔽 := withDensity_absolutelyContinuous _ _
  have hμν : μ𝔽 ≪ ν(s) := withDensity_absolutelyContinuous'
    ((hdens.measurable.comp (Real.measurable_log.comp hn.measurable)).ennreal_ofReal.aemeasurable)
    (.of_forall fun g ↦ (ENNReal.ofReal_pos.mpr (hpos g)).ne')
  let c : C𝔽 → ℂ := fun g ↦ (modulatedAbsoluteCutoff m𝔽 J g : ℂ)
  have hc (g : C𝔽) : c (h.val⁻¹ * g) = c g := by
    have hh : ideleClassNorm F h.val = 1 := h.property
    have hng : ((m𝔽 (h.val⁻¹ * g)).val : ℝ) = ((m𝔽 g).val : ℝ) := by
      change ((ideleClassNorm F (h.val⁻¹ * g)).val : ℝ) = ((ideleClassNorm F g).val : ℝ)
      rw [map_mul, map_inv, hh, inv_one, one_mul]
    simp only [c, modulatedAbsoluteCutoff, Set.indicator_apply, Set.mem_preimage, hng, Pi.one_apply]
  have hq := (measurePreserving_mul_left μ𝔽 h.val⁻¹).quasiMeasurePreserving
  have hT (v : W(s)) := hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s le_rfl hs h.val v
  have hM (v : W(s)) := modulatedAbsoluteCutoffOperator_apply m𝔽 (ν(s)) J hJ v
  refine Lp.ext ?_
  have hL : (M(s, J, hJ) (hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs h.val u) : C𝔽 → ℂ)
      =ᵐ[ν(s)] fun g ↦ c g * u (h.val⁻¹ * g) := by
    filter_upwards [hM (hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs h.val u),
      hνμ.ae_le (hT u)] with g h1 h2
    rw [h1, h2]
  have hR : (hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs h.val (M(s, J, hJ) u) : C𝔽 → ℂ)
      =ᵐ[ν(s)] fun g ↦ c g * u (h.val⁻¹ * g) := by
    have h3 := hq.ae_eq_comp (hμν.ae_le (hM u))
    filter_upwards [hνμ.ae_le (hT (M(s, J, hJ) u)), hνμ.ae_le h3] with g h1 h2
    rw [h1]
    simp only [Function.comp_apply] at h2
    rw [h2]
    exact congrArg (· * u (h.val⁻¹ * g)) (hc g)
  exact hL.trans hR.symm

/-- Paper: (11.1.2.3), p. 480. Each finite cutoff stage belongs to the cutoff
image of the ambient norm-one isotype. -/
theorem sLocalCutoffCarving_le_cutoffIsotype (s : ℝ) (hs : 0 ≤ s) (ω : PontryaginDual C₁)
    (T : Finset V) (J : Set ℝ) (hJ : MeasurableSet J) :
    sLocalCutoffCarving s ω T J hJ ≤ (Wω(s, hs, ω)).map (M(s, J, hJ)).toLinearMap := by
  have hproj := modulatedAbsoluteCutoffOperator_projection m𝔽 (ν(s)) J hJ
  have hidem : ∀ y, M(s, J, hJ) (M(s, J, hJ) y) = M(s, J, hJ) y := fun y ↦
    congrArg (fun L : W(s) →L[ℂ] W(s) ↦ L y) hproj.1.isIdempotentElem.eq
  -- The image of the isotype is the isotype intersected with the range, which is closed.
  have himage : (((Wω(s, hs, ω)).map (M(s, J, hJ)).toLinearMap : Submodule ℂ (W(s))) :
        Set (W(s))) = (Wω(s, hs, ω) : Set (W(s))) ∩ (range (M(s, J, hJ)) : Set (W(s))) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, z, rfl⟩
      rw [SetLike.mem_coe, mem_actionIsotype] at hz ⊢
      intro h
      change hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs h.val (M(s, J, hJ) z) = _
      rw [← sLocalCutoffCarving_le_cutoffIsotype_comm s hs J hJ h z]
      have hz' := hz h
      change hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs h.val z = _ at hz'
      rw [hz', map_smul]
      rfl
    · rintro ⟨hy, z, rfl⟩
      exact ⟨M(s, J, hJ) z, hy, hidem z⟩
  have hclosed : IsClosed (((Wω(s, hs, ω)).map (M(s, J, hJ)).toLinearMap : Submodule ℂ (W(s))) :
      Set (W(s))) := by
    rw [himage]
    exact (sLocalCutoffCarving_le_cutoffIsotype_closed s hs ω).inter hproj.2
  refine Submodule.topologicalClosure_minimal _ ?_ hclosed
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, rfl⟩
  exact ⟨_, sLocalCutoffCarving_le_cutoffIsotype_theta s hs ω _, rfl⟩

private theorem hardySobolevCutoff_univ_aux {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (U : Set A) (hU : MeasurableSet U) (hUu : U = univ) (f : Lp ℂ 2 μ) :
    hardySobolevCutoff hU f = f := by
  subst hUu
  refine Lp.ext ?_
  unfold hardySobolevCutoff
  filter_upwards [MemLp.coeFn_toLp ((Lp.memLp f).indicator hU.nullMeasurableSet)] with x hx
  rw [hx]
  simp

/-- Paper: (11.1.2.3), p. 480. The full norm band leaves the uncut stage unchanged.
Deviation: Sanity check for the cutoff-stage definition. -/
theorem sLocalCutoffCarving_univ (s : ℝ) (ω : PontryaginDual C₁) (T : Finset V) :
    sLocalCutoffCarving s ω T univ MeasurableSet.univ = sLocalUncutCarving s ω T := by
  have h : ∀ x : W(s), M(s, univ, MeasurableSet.univ) x = x := fun x ↦
    (modulatedAbsoluteCutoffOperator_eq_hardySobolevCutoff m𝔽 (ν(s)) univ MeasurableSet.univ x).trans
      (hardySobolevCutoff_univ_aux _ _ (preimage_univ) x)
  simp only [sLocalCutoffCarving, sLocalUncutCarving, h]

/-- Paper: (11.1.2.4), p. 480. The cofinal limit is the intersection of all
finite-place cutoff stages outside the base set. -/
def sLocalCarvingLimit (s : ℝ) (ω : PontryaginDual C₁) (S : Finset V)
    (J : Set ℝ) (hJ : MeasurableSet J) : Submodule ℂ (W(s)) :=
  ⨅ i : SLocalCarvingIndex (F := F) S, sLocalCutoffCarving s ω i.val J hJ

/-- Paper: Remark 11.1.2.2, p. 480. A cofinal sequence increases by inclusion
and exhausts the finite places outside the base set. -/
def IsSLocalCarvingCofinal {S : Finset V} (A : ℕ → SLocalCarvingIndex (F := F) S) : Prop :=
  Monotone A ∧ (⋃ k, ((A k).val : Set V)) = (S : Set V)ᶜ

/-- Paper: Remark 11.1.2.2, p. 480. An increasing sequence exhausts the outside
places exactly when every finite set of them is contained in some term. -/
theorem isSLocalCarvingCofinal_iff {S : Finset V} (A : ℕ → SLocalCarvingIndex (F := F) S) :
    IsSLocalCarvingCofinal A ↔ Monotone A ∧ ∀ i : SLocalCarvingIndex (F := F) S, ∃ k, i ≤ A k := by
  unfold IsSLocalCarvingCofinal
  refine and_congr_right fun hA ↦ ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · have hv : ∀ v ∈ i.val, ∃ k, v ∈ (A k).val := fun v hv ↦ by
      have : v ∈ (S : Set V)ᶜ := fun hS ↦ Finset.disjoint_left.mp i.2 hS hv
      rw [← h] at this
      simpa using this
    choose! k hk using hv
    refine ⟨i.val.sup k, fun v hv' ↦ ?_⟩
    exact hA (Finset.le_sup (f := k) hv') (hk v hv')
  · refine Set.Subset.antisymm ?_ ?_
    · intro v hv
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hv
      intro hS
      exact Finset.disjoint_left.mp (A k).2 (by simpa using hS) hk
    · intro v hv
      obtain ⟨k, hk⟩ := h ⟨{v}, by simpa using hv⟩
      exact Set.mem_iUnion.mpr ⟨k, hk (Finset.mem_singleton_self v)⟩

/-- The finite places of a number field form a countable type: their ideals are
finitely generated over the countable ring of integers. -/
private theorem exists_sLocalCarvingCofinal_countable (K : Type*) [Field K] [NumberField K] :
    Countable (HeightOneSpectrum (𝓞 K)) := by
  have : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  have : Countable (𝓞 K) := (RingOfIntegers.coe_injective (K := K)).countable
  have h : Surjective (fun s : Finset (𝓞 K) ↦ Ideal.span (s : Set (𝓞 K))) :=
    fun I ↦ IsNoetherian.noetherian I
  have : Countable (Ideal (𝓞 K)) := h.countable
  exact (show Injective (HeightOneSpectrum.asIdeal (R := 𝓞 K)) from fun _ _ h ↦
    HeightOneSpectrum.ext h).countable

/-- Paper: Remark 11.1.2.2, p. 480. Every base admits a cofinal sequence
of finite sets of outside places. -/
theorem exists_sLocalCarvingCofinal (S : Finset V) :
    ∃ A : ℕ → SLocalCarvingIndex (F := F) S, IsSLocalCarvingCofinal A := by
  have := exists_sLocalCarvingCofinal_countable F
  let := Encodable.ofCountable V
  refine ⟨fun k ↦ ⟨((Finset.range k).biUnion fun n ↦ (Encodable.decode₂ V n).toFinset) \ S,
    Finset.disjoint_sdiff⟩, ?_, ?_⟩
  · intro a b hab
    exact Finset.sdiff_subset_sdiff
      (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_subset_range.2 hab)) le_rfl
  · ext v
    simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_biUnion,
      Finset.mem_range, Option.mem_toFinset, Set.mem_compl_iff]
    constructor
    · rintro ⟨k, _, h⟩
      exact h
    · intro h
      exact ⟨Encodable.encode v + 1,
        ⟨Encodable.encode v, Nat.lt_succ_self _, Encodable.mem_decode₂.2 rfl⟩, h⟩

 
open scoped TensorProduct in
/-- Two linear maps agree once they agree on the pure tensors of an
inductive tensor product with a finite tensor product. -/
private theorem sLocalCutoffCarving_antitone_extPi {ι : Type*} [Fintype ι] {E N : Type*}
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E (FinestLocallyConvex (⨂[ℂ] i, M i)) ≃L[ℂ] N) (L₁ L₂ : N →ₗ[ℂ] N)
    (h : ∀ (a : E) (g : ∀ i, M i), L₁ (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i))) = L₂ (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i)))) :
    L₁ = L₂ := by
  have key : ∀ y : E ⊗[ℂ] (⨂[ℂ] i, M i), L₁ (e y) = L₂ (e y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      exact (congrArg L₁ (map_zero e)).trans ((map_zero L₁).trans
        ((map_zero L₂).symm.trans (congrArg L₂ (map_zero e)).symm))
    | tmul a b =>
      induction b using PiTensorProduct.induction_on with
      | smul_tprod r g =>
        rw [show a ⊗ₜ[ℂ] (r • PiTensorProduct.tprod ℂ g) = r • (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ g)
            from TensorProduct.tmul_smul r a _,
          show e (r • (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ g)) =
            r • e (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ g) from map_smul e r _,
          map_smul, map_smul, h]
      | add b c hb hc =>
        rw [TensorProduct.tmul_add]
        exact (congrArg L₁ (map_add e _ _)).trans ((map_add L₁ _ _).trans
          ((congrArg₂ (· + ·) hb hc).trans ((map_add L₂ _ _).symm.trans
            (congrArg L₂ (map_add e _ _)).symm)))
    | add y z hy hz =>
      exact (congrArg L₁ (map_add e y z)).trans ((map_add L₁ _ _).trans
        ((congrArg₂ (· + ·) hy hz).trans ((map_add L₂ _ _).symm.trans
          (congrArg L₂ (map_add e y z)).symm)))
  refine LinearMap.ext fun x ↦ ?_
  calc L₁ x = L₁ (e (e.symm x)) := by rw [e.apply_symm_apply]
    _ = L₂ (e (e.symm x)) := key (e.symm x)
    _ = L₂ x := by rw [e.apply_symm_apply]

/-- The S-local principal values compose over disjoint sets of selected places. -/
private theorem sLocalCutoffCarving_antitone_sPV {T T' : Finset (HeightOneSpectrum (𝓞 F))} (hT : T ⊆ T') :
    sAdelePrincipalValue F (Finset.Subset.refl T') =
      (sAdelePrincipalValue F hT).comp (sAdelePrincipalValue F (Finset.sdiff_subset (s := T') (t := T))) := by
  refine sLocalCutoffCarving_antitone_extPi (sAdeleSchwartz_inductiveTensor_equiv F T').choose _ _ fun a g ↦ ?_
  have h1 := sAdelePrincipalValue_tmul (F := F) (Finset.Subset.refl T') a g
  have h2 := sAdelePrincipalValue_tmul (F := F) (Finset.sdiff_subset (s := T') (t := T)) a g
  have h3 := sAdelePrincipalValue_tmul (F := F) hT a
    (fun w : T' ↦ if (w : HeightOneSpectrum (𝓞 F)) ∈ T' \ T then
      finitePlacePrincipalValue (F := F) w.val (g w) else g w)
  refine h1.trans ?_
  refine Eq.trans ?_ (LinearMap.comp_apply _ _ _).symm
  refine Eq.trans ?_ (congrArg (sAdelePrincipalValue F hT) h2.symm)
  refine Eq.trans ?_ h3.symm
  apply congrArg
  apply congrArg
  apply congrArg
  funext w
  by_cases hw : (w : HeightOneSpectrum (𝓞 F)) ∈ T
  · simp [hw, w.2, Finset.mem_sdiff]
  · simp [hw, w.2, Finset.mem_sdiff]

/-- Two linear maps agree once they agree on the pure tensors of an inductive tensor product. -/
private theorem sLocalCutoffCarving_antitone_extTail {E G N : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (L₁ L₂ : N →ₗ[ℂ] N)
    (h : ∀ (a : E) (b : G), L₁ (e (a ⊗ₜ[ℂ] b)) = L₂ (e (a ⊗ₜ[ℂ] b))) :
    L₁ = L₂ := by
  have key : ∀ y : TensorProduct ℂ E G, L₁ (e y) = L₂ (e y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      exact (congrArg L₁ (map_zero e)).trans ((map_zero L₁).trans
        ((map_zero L₂).symm.trans (congrArg L₂ (map_zero e)).symm))
    | tmul a b => exact h a b
    | add y z hy hz =>
      exact (congrArg L₁ (map_add e y z)).trans ((map_add L₁ _ _).trans
        ((congrArg₂ (· + ·) hy hz).trans ((map_add L₂ _ _).symm.trans
          (congrArg L₂ (map_add e y z)).symm)))
  refine LinearMap.ext fun x ↦ ?_
  calc L₁ x = L₁ (e (e.symm x)) := by rw [e.apply_symm_apply]
    _ = L₂ (e (e.symm x)) := key (e.symm x)
    _ = L₂ x := by rw [e.apply_symm_apply]

/-- The global principal value at a larger set is the one at the smaller set after the one
at the difference. -/
private theorem sLocalCutoffCarving_antitone_PV {T T' : Finset (HeightOneSpectrum (𝓞 F))} (hT : T ⊆ T') :
    adelePrincipalValue F T' =
      (adelePrincipalValue F T).comp (adelePrincipalValue F (T' \ T)) := by
  refine sLocalCutoffCarving_antitone_extTail (sAdeleTailSchwartz_inductiveTensor_equiv F T').choose _ _ fun a b ↦ ?_
  have h1 := adelePrincipalValue_tmul (F := F) (Finset.Subset.refl T') a b
  have h2 := adelePrincipalValue_tmul (F := F) (Finset.sdiff_subset (s := T') (t := T)) a b
  have h3 := adelePrincipalValue_tmul (F := F) hT
    (sAdelePrincipalValue F (Finset.sdiff_subset (s := T') (t := T)) a) b
  refine h1.trans ?_
  refine Eq.trans ?_ (LinearMap.comp_apply _ _ _).symm
  refine Eq.trans ?_ (congrArg (adelePrincipalValue F T) h2.symm)
  refine Eq.trans ?_ h3.symm
  apply congrArg
  apply congrArg₂ _ _ rfl
  exact (LinearMap.ext_iff.mp (sLocalCutoffCarving_antitone_sPV hT) a).trans (LinearMap.comp_apply _ _ _)

/-- Generic range inclusion: no project definitions occur, so nothing is unfolded. -/
private theorem sLocalCutoffCarving_antitone_range {A β : Type*} [AddCommMonoid A] [Module ℂ A]
    (B : Submodule ℂ A) (Φ : B → β) (L L' R : A → A)
    (h : ∀ f : B, L f.val ∈ B) (h' : ∀ f : B, L' f.val ∈ B) (hR : ∀ f : B, R f.val ∈ B)
    (hc : ∀ f : B, L (R f.val) = L' f.val) :
    range (fun f : B ↦ Φ ⟨L' f.val, h' f⟩) ⊆ range (fun f : B ↦ Φ ⟨L f.val, h f⟩) := by
  rintro _ ⟨f, rfl⟩
  exact ⟨⟨R f.val, hR f⟩, congrArg Φ (Subtype.ext (hc f))⟩

/-- Paper: (11.1.2.12), p. 481. Adding finite-place conditions gives a smaller
cutoff stage in the inclusion order.
Deviation: The monotonicity applies to any measurable norm band. -/
theorem sLocalCutoffCarving_antitone (s : ℝ) (ω : PontryaginDual C₁)
    (J : Set ℝ) (hJ : MeasurableSet J) :
    Antitone (fun T : Finset V ↦ sLocalCutoffCarving s ω T J hJ) := by
  intro T T' hTT'
  have hP : ∀ f : ℬ₀, adelePrincipalValue F T (adelePrincipalValue F (T' \ T) f.val) =
      adelePrincipalValue F T' f.val := fun f ↦
    ((LinearMap.ext_iff.mp (sLocalCutoffCarving_antitone_PV hTT') f.val).trans
      (LinearMap.comp_apply _ _ _)).symm
  show sLocalCutoffCarving s ω T' J hJ ≤ sLocalCutoffCarving s ω T J hJ
  unfold sLocalCutoffCarving
  have key := sLocalCutoffCarving_antitone_range (adelePolarSubspace F)
    (fun g : ℬ₀ ↦ M(s, J, hJ) (θ(s, ω, g)))
    (adelePrincipalValue F T) (adelePrincipalValue F T') (adelePrincipalValue F (T' \ T))
    (adelePrincipalValue_mem_polarSubspace T) (adelePrincipalValue_mem_polarSubspace T')
    (adelePrincipalValue_mem_polarSubspace (T' \ T)) hP
  with_reducible exact Submodule.topologicalClosure_mono (Submodule.span_mono key)

local notation "ωOf(" χ ")" =>
  (χ).comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
    C₁ →ₜ* C𝔽)
local notation "Unramified(" χ ", " S ")" => ideleClassNormTwist χ 0 ∈ unramifiedOutside F S
local notation "TrivialPic(" S ")" => Subsingleton (CommRing.Pic (Set.integer (R := 𝓞 F) S F))
local notation "DegreeBound(" s ")" => 2 * (Module.finrank ℚ F : ℝ) ≤ s
local notation "J(" b ", " Λ ")" => sLocalCarvingBand b Λ
local notation "hJ(" b ", " Λ ")" => measurableSet_sLocalCarvingBand b Λ

/-- Paper: Theorem 11.1.2.1(1), p. 480, and (11.1.2.13)–(11.1.2.15),
pp. 481–482. Every cofinal sequence realizes the same limit by intersection.
Deviation: Equality to the intersection over all indices also gives a sanity
check for the sequence-independent definition. -/
theorem sLocalCarvingLimit_eq_iInf {S : Finset V} (s : ℝ) (ω : PontryaginDual C₁)
    (J : Set ℝ) (hJ : MeasurableSet J)
    (A : ℕ → SLocalCarvingIndex (F := F) S) (_hA : IsSLocalCarvingCofinal A) :
    sLocalCarvingLimit s ω S J hJ = ⨅ k, sLocalCutoffCarving s ω (A k).val J hJ := by
  unfold sLocalCarvingLimit
  apply le_antisymm
  · exact le_iInf fun k ↦ iInf_le _ (A k)
  · refine le_iInf fun i ↦ ?_
    obtain ⟨k, hik⟩ := ((isSLocalCarvingCofinal_iff A).1 _hA).2 i
    exact (iInf_le _ k).trans (sLocalCutoffCarving_antitone s ω J hJ hik)

/-- Paper: Theorem 11.1.2.1(1), p. 480. The cofinal limit is closed in the
ambient weighted L² space. -/
theorem isClosed_sLocalCarvingLimit (S : Finset V) (s : ℝ) (ω : PontryaginDual C₁)
    (J : Set ℝ) (hJ : MeasurableSet J) :
    IsClosed (sLocalCarvingLimit s ω S J hJ : Set (W(s))) := by
  rw [sLocalCarvingLimit, Submodule.coe_iInf]
  exact isClosed_iInter fun i ↦ Submodule.isClosed_topologicalClosure _

/-- Paper: Theorem 11.1.2.1(1), p. 480. The cofinal limit lies in the image
of the ambient isotype under the cutoff. -/
theorem sLocalCarvingLimit_le_cutoffIsotype {S : Finset V} (χ : PontryaginDual C𝔽)
    (_hχ : Unramified(χ, S)) (_hPic : TrivialPic((S : Set V)))
    (s : ℝ) (hs : DegreeBound(s)) (twoSided : Bool) (Λ : ℝ) (_hΛ : 0 < Λ) :
    let hs₀ : 0 ≤ s := (mul_nonneg zero_le_two (Nat.cast_nonneg _)).trans hs
    sLocalCarvingLimit s (ωOf(χ)) S (J(twoSided, Λ)) (hJ(twoSided, Λ)) ≤
      (Wω(s, hs₀, ωOf(χ))).map (M(s, J(twoSided, Λ), hJ(twoSided, Λ))).toLinearMap := by
  intro hs₀
  exact (iInf_le _ (⟨∅, Finset.disjoint_empty_right S⟩ : SLocalCarvingIndex (F := F) S)).trans
    (sLocalCutoffCarving_le_cutoffIsotype _ _ _ _ _ _)

local notation "reciprocalMeasure(" s ")" =>
  (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (norm𝔽 g)))⁻¹)

/-- At degree greater than one, a unitary character represents a continuous Mellin
evaluation on the zero-line Sobolev space. -/
private theorem sLocalUncutCarving_lt_mellinFunctional (χ : PontryaginDual C𝔽) (z : ℂ)
    (hz : z.re = 0) {s : ℝ} (hs : 1 < s) :
    ∃ Λ : StrongDual ℂ W(s), ∀ f : W(s),
      Λ f = ∫ g, f g * ideleClassNormTwist χ z g ∂μ𝔽 := by
  let hm : IsModulation m𝔽 :=
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hsurj : Surjective m𝔽 := fun x ↦
    ⟨classOf (canonicalIdeleNormSection F x), canonicalIdeleNormSection_rightInverse F x⟩
  have h₀ : 0 ≤ s := zero_le_one.trans hs.le
  let ρ (g : C𝔽) := (intervalSobolevDensity 0 0 s (Real.log (norm𝔽 g)))⁻¹
  have hρ_eq (g : C𝔽) : ρ g = (1 + |Real.log (norm𝔽 g)| ^ 2) ^ (-s / 2) := by
    simp only [ρ, intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero, max_self, one_mul,
      sq_abs]
    rw [show -s / 2 = -(s / 2) by ring, Real.rpow_neg (by positivity)]
  have hρ_cont : Continuous ρ := by
    simp_rw [show ρ = fun g ↦ (1 + (Real.log (norm𝔽 g)) ^ 2) ^ (-s / 2) from
      funext fun g ↦ by rw [hρ_eq, sq_abs]]
    have hn : Continuous norm𝔽 := NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)
    have hl : Continuous (fun g ↦ Real.log (norm𝔽 g)) :=
      hn.log (fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))).ne')
    exact ((continuous_const (y := (1 : ℝ))).add (hl.pow 2)).rpow_const (fun g ↦
      Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _))))
  have hρ_int : Integrable ρ μ𝔽 :=
    ((modulatedSobolev_reciprocal_integrable_iff m𝔽 μ𝔽 hm hsurj h₀).mpr hs).congr
      (Filter.Eventually.of_forall fun g ↦ (hρ_eq g).symm)
  have hc (g : C𝔽) : ‖ideleClassNormTwist χ z g‖ = 1 := by
    change ‖(χ g : ℂ) * (norm𝔽 g : ℂ) ^ z‖ = 1
    rw [norm_mul, Circle.norm_coe, Complex.norm_cpow_eq_rpow_re_of_pos
      (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))), hz, Real.rpow_zero, mul_one]
  have hmem : MemLp (ideleClassNormTwist χ z) 2 (reciprocalMeasure(s)) := by
    apply (memLp_two_iff_integrable_sq_norm (ideleClassNormTwist χ z).continuous.aestronglyMeasurable).mpr
    apply (integrable_withDensity_iff hρ_cont.measurable.ennreal_ofReal
      (ae_of_all μ𝔽 fun _ ↦ ENNReal.ofReal_lt_top)).mpr
    refine hρ_int.congr (ae_of_all μ𝔽 fun g ↦ ?_)
    change ρ g = ‖ideleClassNormTwist χ z g‖ ^ 2 * (ENNReal.ofReal (ρ g)).toReal
    simp [hc, ENNReal.toReal_ofReal (show 0 ≤ ρ g from inv_nonneg.mpr (by
      unfold intervalSobolevDensity
      positivity))]
  obtain ⟨e, he, _⟩ := modulatedIntervalSobolev_dual m𝔽 hm μ𝔽 0 0 s le_rfl h₀
  let u : CompactIntervalSobolev μ𝔽 (fun g ↦ Real.log (norm𝔽 g)) 0 0 s true :=
    hmem.toLp _
  let Λ : StrongDual ℂ W(s) := e.symm u
  refine ⟨Λ, fun f ↦ (he Λ f).2.trans (integral_congr_ae ?_)⟩
  have hu : (u : C𝔽 → ℂ) =ᵐ[reciprocalMeasure(s)] (ideleClassNormTwist χ z : C𝔽 → ℂ) :=
    MemLp.coeFn_toLp _
  have hu' := (ae_withDensity_iff hρ_cont.measurable.ennreal_ofReal).mp hu
  have heq : e Λ = u := e.apply_symm_apply u
  rw [heq]
  filter_upwards [hu'] with g hg
  have hp : 0 < ρ g := by
    rw [hρ_eq]
    positivity
  exact congrArg (f g * ·) (hg (ENNReal.ofReal_pos.mpr hp).ne')

/-- Weil integration on a polar test identifies the zero-line pairing with global
Mellin evaluation times the mass of the norm-one class group. This is the polar-test
version of `homogeneousTheta_classMellin_eq_mass_mul`. -/
private theorem sLocalUncutCarving_lt_classMellin (χ : PontryaginDual C𝔽) (z : ℂ) (f : ℬ₀) :
    (∫ g : C𝔽, homogeneousAdelicTheta (ωOf(χ)) f.val g * ideleClassNormTwist χ z g ∂μ𝔽) =
      ((μ₁ univ).toReal : ℂ) * globalIdelicZFunction f.val (ideleClassNormTwist χ z) := by
  let ν := normOneIdeleClassTamagawaMeasure F
  let μ := ideleClassTamagawaMeasure F
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : ν.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : μ.IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  let ω : PontryaginDual C₁ := ωOf(χ)
  let c := ideleClassNormTwist χ z
  let W (g : C𝔽) := adelicTheta f.val g * c g
  let A (g : C𝔽) := homogeneousAdelicTheta ω f.val g * c g
  let Φ (p : C𝔽 × C₁) := W (p.2.val * p.1)
  have hf := (mem_adelePolarSubspace f.val).mp f.property
  have hi : Integrable W μ :=
    globalThetaMellinIntegral_integrable_of_vanishing f.val hf.1 hf.2 c
  have hP : AEStronglyMeasurable Φ (μ.prod ν) := by
    apply Continuous.aestronglyMeasurable
    exact ((adelicTheta f.val).continuous.mul c.continuous).comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
  have hp : Integrable Φ (μ.prod ν) := by
    apply (integrable_prod_iff' hP).mpr
    constructor
    · filter_upwards with u
      change Integrable (fun g ↦ W (u.val * g)) μ
      have hm : Measure.map (fun g : C𝔽 ↦ u.val * g) μ = μ := map_mul_left_eq_self μ u.val
      have hw : AEStronglyMeasurable W (Measure.map (fun g : C𝔽 ↦ u.val * g) μ) := by
        rw [hm]; exact hi.aestronglyMeasurable
      have hi' : Integrable W (Measure.map (fun g : C𝔽 ↦ u.val * g) μ) := by rw [hm]; exact hi
      have h := (integrable_map_measure hw ((continuous_const.mul continuous_id).measurable.aemeasurable)).mp hi'
      exact h
    · have he : (fun u : C₁ ↦ ∫ g, ‖Φ (g,u)‖ ∂μ) = fun _ ↦ ∫ g, ‖W g‖ ∂μ := by
        funext u
        change (∫ g, ‖W (u.val * g)‖ ∂μ) = _
        exact integral_mul_left_eq_self (fun g ↦ ‖W g‖) u.val
      rw [he]
      exact integrable_const _
  have ha (g : C𝔽) : (∫ u, Φ (g,u) ∂ν) = A g := by
    have hu (u : C₁) : c u.val = (ω u : ℂ) := by
      change (χ u.val : ℂ) * (((ideleClassNorm F u.val : ℝ≥0) : ℝ) : ℂ) ^ z = _
      simp only [MonoidHom.mem_ker.mp u.property, Units.val_one, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, mul_one]
      rfl
    change (∫ u, adelicTheta f.val (u.val * g) * c (u.val * g) ∂ν) = _
    simp_rw [map_mul c, hu, ← mul_assoc, integral_mul_const]
    rfl
  change (∫ g, A g ∂μ) = ((ν univ).toReal : ℂ) * globalIdelicZFunction f c
  rw [← integral_congr_ae (Filter.Eventually.of_forall ha), ← integral_prod Φ hp, integral_prod_symm Φ hp]
  have he (u : C₁) : (∫ g, Φ (g,u) ∂μ) = ∫ g, W g ∂μ := integral_mul_left_eq_self W u.val
  simp_rw [he, integral_const]
  rw [RCLike.real_smul_eq_coe_mul]
  congr 1
  exact congrFun (globalThetaMellinIntegral_eq_continuation_of_vanishing f.val hf.1 hf.2) c

/-- On a polar test the principal-value multiplier identity extends across every
point, since both sides are continuous. -/
private theorem sLocalUncutCarving_lt_pvMellin (χ : PontryaginDual C𝔽) (T : Finset V)
    (f : ℬ₀) (z : ℂ) :
    globalIdelicZFunction (adelePrincipalValue F T f.val) (ideleClassNormTwist χ z) =
      reciprocalPartialHeckeEulerProduct χ T z * globalIdelicZFunction f.val (ideleClassNormTwist χ z) := by
  have h₁ := (globalIdelicZFunction_entire_of_vanishing _
    (adelePrincipalValue_mem_polarSubspace T f) χ).continuous.continuousAt (x := z)
  have h₂ := (globalIdelicZFunction_entire_of_vanishing _ f.property χ).continuous.continuousAt (x := z)
  have hfactor (v : V) : Differentiable ℂ (fun w ↦ (finiteHeckeEulerFactor χ v w)⁻¹) := by
    unfold finiteHeckeEulerFactor
    split_ifs
    · simp_rw [inv_inv]
      have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr ((Ideal.absNorm_eq_zero_iff).not.mpr v.ne_bot)
      exact (differentiable_const _).sub ((differentiable_const _).mul
        (differentiable_neg.const_cpow (Or.inl hq)))
    · simp_rw [inv_one]
      exact differentiable_const _
  have hprod : Continuous (reciprocalPartialHeckeEulerProduct χ T) := by
    unfold reciprocalPartialHeckeEulerProduct
    exact (Differentiable.fun_finsetProd (𝕜 := ℂ) fun v _ ↦ hfactor v).continuous
  exact ((h₁.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE ((hprod.continuousAt (x := z)).mul h₂)).mp
    ((globalPrincipalValueConverse_mellin T χ f.val).filter_mono (nhdsNE_le_codiscrete z))).eq_of_nhds

/-- On a principal-value generator the ambient Mellin functional reads the product of the
norm-one class mass, the Euler multiplier and the polar test's Mellin value. -/
private theorem sLocalUncutCarving_lt_evalGenerator (χ : PontryaginDual C𝔽) (z : ℂ)
    {s : ℝ} {Λ : StrongDual ℂ W(s)}
    (hΛ : ∀ f : W(s), Λ f = ∫ g, f g * ideleClassNormTwist χ z g ∂μ𝔽)
    (T : Finset V) (f : ℬ₀) :
    Λ (θ(s, ωOf(χ), P(T, f))) = ((μ₁ univ).toReal : ℂ) *
      (reciprocalPartialHeckeEulerProduct χ T z * globalIdelicZFunction f.val (ideleClassNormTwist χ z)) := by
  have hn : Continuous norm𝔽 :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hdens : Continuous (intervalSobolevDensity 0 0 s) := by
    unfold intervalSobolevDensity
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).max
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
      (Continuous.rpow_const (f := fun x : ℝ ↦ 1 + x ^ 2) (by fun_prop)
        fun x ↦ Or.inl (by positivity))
  have hpos (g : C𝔽) : 0 < intervalSobolevDensity 0 0 s (Real.log (norm𝔽 g)) :=
    mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  have hμν : μ𝔽 ≪ ν(s) := withDensity_absolutelyContinuous'
    ((hdens.measurable.comp (Real.measurable_log.comp hn.measurable)).ennreal_ofReal.aemeasurable)
    (.of_forall fun g ↦ (ENNReal.ofReal_pos.mpr (hpos g)).ne')
  have hf := (MemLp.coeFn_toLp
    (memLp_homogeneousTheta_zeroLine s (ωOf(χ)) (P(T, f)))).filter_mono hμν.ae_le
  rw [hΛ]
  convert (sLocalUncutCarving_lt_classMellin χ z (P(T, f))).trans ?_ using 1
  · apply integral_congr_ae
    filter_upwards [hf] with g hg using congrArg (· * ideleClassNormTwist χ z g) hg
  · rw [sLocalUncutCarving_lt_pvMellin χ T f z]

/-- A zero of the reciprocal Euler factor at an unramified place is a simple pole. -/
private theorem sLocalUncutCarving_lt_eulerPole (χ : PontryaginDual C𝔽) (v : V)
    (hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v) {z : ℂ}
    (hz : (finiteHeckeEulerFactor χ v z)⁻¹ = 0) :
    meromorphicOrderAt (finiteHeckeEulerFactor χ v) z < 0 := by
  have hq : (1 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans hq).ne'
  let L := Complex.log (v.asIdeal.absNorm : ℂ)
  have hL : L ≠ 0 := by
    simp only [L, ← Complex.natCast_log]
    exact_mod_cast (Real.log_pos hq).ne'
  let a := (ideleClassNormTwist χ 0).localValue v
  let d (w : ℂ) := 1 - a * Complex.exp (-(L * w))
  have hd : (fun w ↦ (finiteHeckeEulerFactor χ v w)⁻¹) = d := by
    funext w
    rw [finiteHeckeEulerFactor, ite_eq_left hu, inv_inv, Complex.cpow_def_of_ne_zero hq0]
    unfold d
    congr 3
    ring
  have hv : d z = 0 := congrFun hd z ▸ hz
  have ha : a ≠ 0 := by
    intro h
    simp [d, h] at hv
  have hder : HasDerivAt d (-(a * (Complex.exp (-(L * z)) * -(L * 1)))) z :=
    ((((hasDerivAt_id z).const_mul L).neg.cexp).const_mul a).const_sub 1
  have han : AnalyticAt ℂ d z := by unfold d; fun_prop
  have ho := han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hv (by
    rw [hder.deriv]
    simp [ha, hL, Complex.exp_ne_zero])
  have hm : meromorphicOrderAt d z = 1 := by rw [han.meromorphicOrderAt_eq, ho]; rfl
  have hfun : finiteHeckeEulerFactor χ v = fun w ↦ (d w)⁻¹ := by
    funext w
    rw [← congrFun hd w, inv_inv]
  rw [hfun]
  change meromorphicOrderAt d⁻¹ z < 0
  rw [meromorphicOrderAt_inv, hm]
  exact WithTop.coe_lt_coe.mpr (by decide : (-1 : ℤ) < 0)

/-- Different exponents give different global norm twists of a fixed character. -/
private theorem sLocalUncutCarving_lt_chart_injective (χ : PontryaginDual C𝔽) :
    Injective (ideleClassNormTwist χ) := by
  intro s t h
  let w := quasiCharacterNormTwist (MonoidHom.id ℝ≥0ˣ) continuous_id 1 s
  have hw (u : ℝ≥0ˣ) : w u = ((u.val : ℝ) : ℂ) ^ s := one_mul _
  apply (existsUnique_complexPower w).unique hw
  intro u
  let g : C𝔽 := classOf (canonicalIdeleNormSection F u)
  have hg : ideleClassNorm F g = u := canonicalIdeleNormSection_rightInverse F u
  have he := DFunLike.congr_fun h g
  change (χ g : ℂ) * (norm𝔽 g : ℂ) ^ s = (χ g : ℂ) * (norm𝔽 g : ℂ) ^ t at he
  rw [show norm𝔽 g = (u.val : ℝ) from congrArg (fun x : ℝ≥0ˣ ↦ (x.val : ℝ)) hg] at he
  exact (hw u).trans (mul_left_cancel₀ (Circle.coe_ne_zero _) he)

/-- A newly selected rational prime supplies infinitely many potential Euler zeros. Each old
place rules out at most one, by the distinct-prime common-pole bound. -/
private theorem sLocalUncutCarving_lt_newZero {S T T' : Finset V} (χ : PontryaginDual C𝔽)
    (hχ : Unramified(χ, S)) (hT : Disjoint S T) (hT' : Disjoint S T')
    {p : ℕ} (hpT : ∀ v ∈ T, (p : 𝓞 F) ∉ v.asIdeal)
    (v : V) (hv : v ∈ T') (hpv : (p : 𝓞 F) ∈ v.asIdeal) :
    ∃ z : ℂ, z.re = 0 ∧ ideleClassNormTwist χ z ≠ 1 ∧
      reciprocalPartialHeckeEulerProduct χ T z ≠ 0 ∧
      reciprocalPartialHeckeEulerProduct χ T' z = 0 := by
  classical
  have hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v :=
    hχ v (fun h ↦ Finset.disjoint_left.mp hT' h hv)
  obtain ⟨π₀, hπ₀⟩ := (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (π₀ : v.adicCompletion F) hπ₀.ne_zero
  have hπ : Valued.v.IsUniformizer (π : v.adicCompletion F) := hπ₀
  obtain ⟨t, ⟨_, ht, _⟩, _⟩ := unramifiedHeckeCharacter_existsUnique_phase χ v hu π hπ
  have hval : (ideleClassNormTwist χ 0).localValue v =
      (v.asIdeal.absNorm : ℂ) ^ (-(t : ℂ) * Complex.I) := by
    rw [hu.localValue_eq π hπ, HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    exact ht
  have hq : (1 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans hq).ne'
  let L := Real.log (v.asIdeal.absNorm : ℝ)
  have hL : 0 < L := Real.log_pos hq
  let d := 2 * Real.pi / L
  have hd : 0 < d := div_pos Real.two_pi_pos hL
  let z (n : ℕ) := (((n : ℝ) * d - t : ℝ) : ℂ) * Complex.I
  have hzreal (n : ℕ) : (z n).re = 0 := by simp [z]
  have hzinj : Injective z := by
    intro a b h
    have he := congrArg Complex.im h
    simp only [z, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero] at he
    have heq : (a : ℝ) = b := mul_right_cancel₀ hd.ne' (by linarith only [he])
    exact_mod_cast heq
  have hzv (n : ℕ) : (finiteHeckeEulerFactor χ v (z n))⁻¹ = 0 := by
    rw [finiteHeckeEulerFactor_inv_eq_phase χ v hu t hval,
      Complex.cpow_def_of_ne_zero hq0]
    apply sub_eq_zero.mpr
    symm
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨-(n : ℤ), ?_⟩
    have hdL : (d : ℂ) * (L : ℂ) = 2 * (Real.pi : ℂ) := by
      exact_mod_cast (div_mul_cancel₀ (2 * Real.pi) hL.ne')
    rw [← Complex.natCast_log]
    change (L : ℂ) * (-z n - (t : ℂ) * Complex.I) = _
    simp only [z, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast, Int.cast_neg, Int.cast_natCast]
    change (L : ℂ) * (-(((n : ℂ) * (d : ℂ) - (t : ℂ)) * Complex.I) - (t : ℂ) * Complex.I) = _
    linear_combination -(n : ℂ) * Complex.I * hdL
  let excluded (w : V) : Set ℂ := {a | meromorphicOrderAt (finiteHeckeEulerFactor χ v) a < 0 ∧
    meromorphicOrderAt (finiteHeckeEulerFactor χ w) a < 0}
  have hfinite (w : V) (hw : w ∈ T) : (excluded w).Finite := by
    let R := S ∪ T ∪ T'
    let a : R := ⟨v, Finset.mem_union_right _ hv⟩
    let b : R := ⟨w, Finset.mem_union_left _ (Finset.mem_union_right _ hw)⟩
    have hχR : Unramified(χ, R) := fun w h ↦ hχ w
      (fun hS ↦ h (Finset.mem_union_left _ (Finset.mem_union_left _ hS)))
    have hwχ : (ideleClassNormTwist χ 0).IsUnramifiedAt w :=
      hχ w (fun h ↦ Finset.disjoint_left.mp hT h hw)
    have hne : v.under (𝓞 ℚ) ≠ w.under (𝓞 ℚ) := by
      intro h
      apply hpT w hw
      have he := congrArg HeightOneSpectrum.asIdeal h
      change v.asIdeal.under (𝓞 ℚ) = w.asIdeal.under (𝓞 ℚ) at he
      have hmem : (p : 𝓞 ℚ) ∈ v.asIdeal.under (𝓞 ℚ) := by
        change algebraMap (𝓞 ℚ) (𝓞 F) (p : 𝓞 ℚ) ∈ v.asIdeal
        simpa only [map_natCast] using hpv
      rw [he] at hmem
      change algebraMap (𝓞 ℚ) (𝓞 F) (p : 𝓞 ℚ) ∈ w.asIdeal at hmem
      simpa only [map_natCast] using hmem
    exact (finiteHeckeEulerFactors_common_pole_subsingleton χ hχR a b hu hwχ hne).finite
  let bad := (⋃ w ∈ T, excluded w) ∪ {a | ideleClassNormTwist χ a = 1}
  have hbad : bad.Finite := T.finite_toSet.biUnion hfinite |>.union
    ((show {a | ideleClassNormTwist χ a = 1}.Subsingleton from
      fun _ hz _ hw ↦ sLocalUncutCarving_lt_chart_injective χ (hz.trans hw.symm)).finite)
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := (infinite_range_of_injective hzinj).exists_notMem_finite hbad
  refine ⟨z n, hzreal n, (fun h ↦ hn (Or.inr h)), ?_, ?_⟩
  · unfold reciprocalPartialHeckeEulerProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro w hw hz
    have hwχ : (ideleClassNormTwist χ 0).IsUnramifiedAt w :=
      hχ w (fun h ↦ Finset.disjoint_left.mp hT h hw)
    exact hn (Or.inl (mem_iUnion₂.mpr ⟨w, hw, sLocalUncutCarving_lt_eulerPole χ v hu (hzv n),
      sLocalUncutCarving_lt_eulerPole χ w hwχ hz⟩))
  · unfold reciprocalPartialHeckeEulerProduct
    exact Finset.prod_eq_zero hv (hzv n)

/-- Unit translation preserves evaluation at zero and scales Fourier evaluation by the norm. -/
private theorem sLocalUncutCarving_lt_translatePolar
    (u : IdeleGroup (𝓞 F) F)
    (f : SchwartzBruhat (Multiplicative 𝔸[F])) :
    adelePolarValues (F := F) (schwartzBruhatUnitTranslate u f) =
      ((adelePolarValues (F := F) f).1,
        (((ideleNorm F u).val : ℝ) : ℂ) * (adelePolarValues (F := F) f).2) := by
  apply Prod.ext
  · change f (Multiplicative.ofAdd (u.inv * 0)) = f (Multiplicative.ofAdd 0)
    rw [mul_zero]
  · have h := globalThetaPolarValues_snd_translate (F := F) (QuotientGroup.mk u)
      (Submodule.Quotient.mk f)
    rw [(existsUnique_globalThetaAction (F := F)).exists.choose_spec.2 u f] at h
    exact h

/-- Reflection across the critical strip gives a test nonzero at any nontrivial unitary
character. Two translation differences annihilate evaluation at zero and Fourier evaluation
at zero while preserving nonvanishing of the Mellin value. -/
private theorem sLocalUncutCarving_lt_polarNonzero (χ : PontryaginDual C𝔽) (z : ℂ) (hz : z.re = 0)
    (hc : ideleClassNormTwist χ z ≠ 1) :
    ∃ f : adelePolarSubspace F, globalIdelicZFunction f.val (ideleClassNormTwist χ z) ≠ 0 := by
  let c := ideleClassNormTwist χ z
  have h₁ : ideleClassNormTwist (1 : PontryaginDual C𝔽) 0 = 1 := by
    ext1 g
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hDual (η : PontryaginDual C𝔽) (s : ℂ) :
      dualQuasiCharacter (G := C𝔽) (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous
        (ideleClassNormTwist η s) = ideleClassNormTwist η⁻¹ (1 - s) := by
    ext1 g
    let N : ℂ := (((ideleClassNorm F g).val : ℝ) : ℂ)
    have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (ideleClassNorm F g).ne_zero)
    change N * ideleClassNormTwist η s g⁻¹ = ideleClassNormTwist η⁻¹ (1 - s) g
    rw [map_inv]
    change N * ((η g : ℂ) * N ^ s)⁻¹ = (η g : ℂ)⁻¹ * N ^ (1 - s)
    rw [mul_inv_rev, Complex.cpow_sub 1 s hN, Complex.cpow_one, div_eq_mul_inv]
    ac_rfl
  have hr : (1 - z).re = 1 := by simp [hz]
  have hreg₁ : ideleClassNormTwist χ⁻¹ (1 - z) ≠ 1 := by
    intro e
    have h := quasiCharacterAbscissa_ideleClassNormTwist χ⁻¹ (1 - z)
    rw [e, ← h₁, quasiCharacterAbscissa_ideleClassNormTwist, hr] at h
    norm_num at h
  have hreg₂ : ideleClassNormTwist χ⁻¹ (1 - z) ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) 1 := by
    intro e
    have h := congrArg (fun c : HeckeCharacter (𝓞 F) F ↦
      dualQuasiCharacter (G := C𝔽) (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous c) e
    rw [hDual, hDual,
      inv_inv, inv_one, sub_sub_cancel, sub_self, h₁] at h
    exact hc h
  obtain ⟨g, hg⟩ := exists_globalIdelicZetaIntegral_eq_completedHeckeL χ⁻¹
  let L (s : ℂ) := globalIdelicZFunction g (ideleClassNormTwist χ⁻¹ s)
  have hL : MeromorphicNFOn L univ := globalIdelicZFunction_meromorphic g χ⁻¹
  have hn : L (1 - z) ≠ 0 := by
    intro he
    have han : AnalyticAt ℂ L (1 - z) := (globalIdelicZFunction_poles g χ⁻¹).1 _ ⟨hreg₁, hreg₂⟩
    have hpos : 0 < meromorphicOrderAt L (1 - z) :=
      lt_of_le_of_ne han.meromorphicOrderAt_nonneg
        (fun h ↦ ((hL (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mp h.symm) he)
    have hlt := completedHeckeL_continuation_zeros χ⁻¹ L hL (fun s ↦ by
      change globalIdelicZFunction _ _ = _
      rw [globalIdelicZFunction_eq_integral, hg s]
      change 1 < quasiCharacterAbscissa _ _ _ _
      rw [quasiCharacterAbscissa_ideleClassNormTwist]
      exact s.2) (by rw [hr]; norm_num) hpos
    linarith
  let E := adeleSchwartzFourier g
  have hE : globalIdelicZFunction E c ≠ 0 := by
    change globalIdelicZFunction g (ideleClassNormTwist χ⁻¹ (1 - z)) ≠ 0 at hn
    rwa [globalIdelicZFunction_functionalEquation, hDual,
      inv_inv, sub_sub_cancel] at hn
  have hcn : c ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) 1 := by
    intro e
    have h := quasiCharacterAbscissa_ideleClassNormTwist χ z
    change ideleClassNormTwist χ z = _ at e
    rw [e, quasiCharacterAbscissa_ideleClassNormTwist, hz] at h
    norm_num at h
  have hreg : 0 ≤ globalIdelicOrderBound c := by
    rw [globalIdelicOrderBound, ite_eq_right (not_or.mpr ⟨hc, hcn⟩)]
  let Z : SchwartzBruhat (Multiplicative 𝔸[F]) →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ (globalIdelicMellin (F := F) f).val ⟨c, hreg⟩
      map_add' := by intro f g; rw [map_add]; rfl
      map_smul' := by intro a g; rw [map_smul]; rfl }
  have hZT (t : I𝔽) (f : SchwartzBruhat (Multiplicative 𝔸[F])) :
      Z (schwartzBruhatUnitTranslate t f) = c (QuotientGroup.mk t) * Z f :=
    globalIdelicMellin_unitTranslate t f ⟨c, hreg⟩
  have hZE : Z E ≠ 0 := hE
  let r : NNRealˣ := Units.mk0 2 (by norm_num)
  let u := canonicalIdeleNormSection F r
  have hn' : (((ideleNorm F u).val : ℝ) : ℂ) = 2 := by
    rw [canonicalIdeleNormSection_rightInverse F r]
    rfl
  have hcu : c (QuotientGroup.mk u) ≠ 2 := by
    intro h
    have hnrm (q : C𝔽) : ‖c q‖ = 1 := by
      change ‖(χ q : ℂ) * (((ideleClassNorm F q : NNReal) : ℝ) : ℂ) ^ z‖ = 1
      rw [norm_mul, Circle.norm_coe,
        Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)), hz]
      simp
    have hb := hnrm (QuotientGroup.mk u)
    rw [h] at hb
    norm_num at hb
  obtain ⟨q, hq⟩ : ∃ q : C𝔽, c q ≠ 1 := by
    by_contra! h
    exact hc (ContinuousMonoidHom.ext fun q ↦ h q)
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
  let d := schwartzBruhatUnitTranslate u E - (2 : ℂ) • E
  let f := schwartzBruhatUnitTranslate v d - d
  have hp : f ∈ adelePolarSubspace F := by
    change adelePolarValues (F := F) f = 0
    dsimp only [f, d]
    rw [map_sub, sLocalUncutCarving_lt_translatePolar, map_sub, map_smul, sLocalUncutCarving_lt_translatePolar, hn']
    apply Prod.ext <;> simp
  refine ⟨⟨f, hp⟩, ?_⟩
  change Z f ≠ 0
  have he : Z f = (c (QuotientGroup.mk v) - 1) * (c (QuotientGroup.mk u) - 2) * Z E := by
    dsimp only [f, d]
    rw [map_sub, hZT, map_sub, hZT, map_smul]
    simp only [smul_eq_mul]
    ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hq) (sub_ne_zero.mpr hcu)) hZE

/-- Paper: Theorem 11.1.2.1(2), p. 480, (11.1.2.5). If the larger stage adds
a place over a rational prime absent at the smaller stage, the inclusion of the
uncut completions is strict.
Deviation: A continuous Mellin evaluation at a new reciprocal Euler zero separates the stages. -/
theorem sLocalUncutCarving_lt {S : Finset V} (χ : PontryaginDual C𝔽)
    (_hχ : Unramified(χ, S)) (_hPic : TrivialPic((S : Set V)))
    (s : ℝ) (_hs : DegreeBound(s)) (i i' : SLocalCarvingIndex (F := F) S) (_hii' : i < i')
    (_hp : ∃ p : ℕ, p.Prime ∧
      (∀ v ∈ i.val, (p : 𝓞 F) ∉ v.asIdeal) ∧ ∃ v ∈ i'.val, (p : 𝓞 F) ∈ v.asIdeal) :
    sLocalUncutCarving s (ωOf(χ)) i'.val < sLocalUncutCarving s (ωOf(χ)) i.val := by
  obtain ⟨p, _, hpT, v, hv, hpv⟩ := _hp
  obtain ⟨z, hz, hzunit, hzT, hzT'⟩ :=
    sLocalUncutCarving_lt_newZero χ _hχ i.property i'.property hpT v hv hpv
  have hd : 1 ≤ (Module.finrank ℚ F : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Module.finrank_pos (R := ℚ) (M := F)))
  have hs : 1 < s := by linarith
  obtain ⟨Λ, hΛ⟩ := sLocalUncutCarving_lt_mellinFunctional χ z hz hs
  have hsubset : sLocalUncutCarving s (ωOf(χ)) i'.val ≤ sLocalUncutCarving s (ωOf(χ)) i.val := by
    let ω : PontryaginDual C₁ := ωOf(χ)
    exact (sLocalCutoffCarving_univ s ω i'.val).ge.trans
      ((sLocalCutoffCarving_antitone s ω univ MeasurableSet.univ _hii'.le).trans
        (sLocalCutoffCarving_univ s ω i.val).le)
  refine hsubset.lt_of_not_ge fun hreverse ↦ ?_
  have hvan : sLocalUncutCarving s (ωOf(χ)) i'.val ≤ Λ.ker := by
    unfold sLocalUncutCarving
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) Λ.isClosed_ker
    rintro _ ⟨f, rfl⟩
    apply LinearMap.mem_ker.mpr
    have h := sLocalUncutCarving_lt_evalGenerator χ z hΛ i'.val f
    rw [hzT', zero_mul, mul_zero] at h
    exact h
  obtain ⟨f, hf⟩ := sLocalUncutCarving_lt_polarNonzero χ z hz hzunit
  have hmass : ((μ₁ univ).toReal : ℂ) ≠ 0 := by
    let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
    let : (μ₁).IsHaarMeasure :=
      (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
    exact Complex.ofReal_ne_zero.mpr measureReal_univ_pos.ne'
  have hmem : θ(s, ωOf(χ), P(i.val, f)) ∈ sLocalUncutCarving s (ωOf(χ)) i.val :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, rfl⟩)
  have hzero := LinearMap.mem_ker.mp (hvan (hreverse hmem))
  exact (mul_ne_zero hmass (mul_ne_zero hzT hf)) <|
    (sLocalUncutCarving_lt_evalGenerator χ z hΛ i.val f).symm.trans hzero

/-- Paper: Theorem 11.1.2.1(2), p. 480, (11.1.2.6). The cutoff stages
are nested under the inclusion order of their finite-place indices.
Deviation: The inclusion permits equality. The printed subsequence claim fails
for the bounded cutoffs over ℚ, already when one prime is added. -/
theorem sLocalCutoffCarving_le {S : Finset V} (χ : PontryaginDual C𝔽)
    (_hχ : Unramified(χ, S)) (_hPic : TrivialPic((S : Set V)))
    (s : ℝ) (_hs : DegreeBound(s)) (i i' : SLocalCarvingIndex (F := F) S) (_hii' : i ≤ i')
    (twoSided : Bool) (Λ : ℝ) (_hΛ : 0 < Λ) :
    let J := J(twoSided, Λ)
    let hJ : MeasurableSet J := hJ(twoSided, Λ)
    sLocalCutoffCarving s (ωOf(χ)) i'.val J hJ ≤
      sLocalCutoffCarving s (ωOf(χ)) i.val J hJ := by
  exact sLocalCutoffCarving_antitone s (ωOf(χ)) _ _ _hii'

-- TODO(paper-gap): In (11.1.2.16) eventual equality gives equality at all
-- earlier radii by applying their nested cutoffs. The representatives can vary
-- with the radius, so strong convergence on fixed inputs gives no contradiction.

/-- Paper: (11.1.2.7), p. 480. The local test is extended to ideles by
multiplying by the indicator of integer units at every place outside S. -/
def sLocalCarvingIdeleTest (S : Finset V) (f : ℬₛ(S)) : I𝔽 → ℂ :=
  {g : I𝔽 | ∀ v ∉ S, Valued.v (g.val.2 v) = 1}.indicator
    (fun g ↦ f (Multiplicative.ofAdd (adeleProjection F S g.val)))

/-- Paper: (11.1.2.7), p. 480. At the identity idele the outside unit factor
is one.
Deviation: Sanity check for extension by the outside unit factor. -/
theorem sLocalCarvingIdeleTest_one (S : Finset V) (f : ℬₛ(S)) :
    sLocalCarvingIdeleTest S f 1 = f (Multiplicative.ofAdd 1) := by
  have h1 : (1 : I𝔽) ∈ {g : I𝔽 | ∀ v ∉ S, Valued.v (g.val.2 v) = 1} := fun v _ ↦ by
    show Valued.v (1 : v.adicCompletion F) = 1
    exact map_one _
  rw [sLocalCarvingIdeleTest, Set.indicator_of_mem h1]
  simp

/-- Paper: (11.1.2.7), p. 480. The raw theta generator sums the extended local
test over nonzero principal multiples of an idele representing the class. -/
def sLocalCarvingTheta (S : Finset V) (f : ℬₛ(S)) (g : C𝔽) : ℂ :=
  ideleThetaSum (sLocalCarvingIdeleTest S f) g.out

/-- The raw theta value at a class is the orbit series at any representative: changing the
representative by a principal idele reindexes the series over `Fˣ`. -/
private theorem sLocalCarvingTheta_classOf (S : Finset V) (f : ℬₛ(S)) (g : I𝔽) :
    sLocalCarvingTheta S f (classOf g) = ideleThetaSum (sLocalCarvingIdeleTest S f) g := by
  unfold sLocalCarvingTheta
  obtain ⟨⟨h, η, rfl⟩, he⟩ :=
    QuotientGroup.mk_out_eq_mul (IdeleGroup.principalSubgroup (𝓞 F) F) g
  change ideleThetaSum _ (QuotientGroup.mk g : C𝔽).out = _
  rw [he]
  unfold ideleThetaSum
  refine Eq.trans ?_ ((Equiv.mulRight η).tsum_eq fun ξ ↦
    sLocalCarvingIdeleTest S f (IdeleGroup.unitEmbedding (𝓞 F) F ξ * g))
  refine tsum_congr fun ξ ↦ congrArg _ ?_
  rw [Equiv.coe_mulRight, map_mul]
  change IdeleGroup.unitEmbedding (𝓞 F) F ξ * (g * IdeleGroup.unitEmbedding (𝓞 F) F η) = _
  rw [mul_comm g, mul_assoc]

/-- Outside `S`, the valuation of a principal translate is the valuation of the field element
times the valuation of the idele. -/
private theorem sLocalCarvingTheta_spec_valuation (g : I𝔽) (ξ : Fˣ) (v : V) :
    Valued.v ((IdeleGroup.unitEmbedding (𝓞 F) F ξ * g).val.2 v) =
      v.valuation F (ξ : F) * Valued.v (g.val.2 v) := by
  change Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ : F)) v * g.val.2 v) = _
  rw [Valuation.map_mul]
  congr 1
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (ξ : F)

/-- If one principal translate of `g` is a unit outside `S`, then another one is exactly when
the ratio of the field elements is an S-unit. -/
private theorem sLocalCarvingTheta_spec_mem (S : Finset V) (g : I𝔽) (ξ₀ ξ : Fˣ)
    (h₀ : IdeleGroup.unitEmbedding (𝓞 F) F ξ₀ * g ∈
      {g' : I𝔽 | ∀ v ∉ S, Valued.v (g'.val.2 v) = 1}) :
    IdeleGroup.unitEmbedding (𝓞 F) F ξ * g ∈ {g' : I𝔽 | ∀ v ∉ S, Valued.v (g'.val.2 v) = 1} ↔
      ξ * ξ₀⁻¹ ∈ (S : Set V).unit F := by
  refine forall₂_congr fun v hv ↦ ?_
  have h0 := h₀ v hv
  rw [sLocalCarvingTheta_spec_valuation] at h0 ⊢
  have hξ₀ : v.valuation F (ξ₀ : F) ≠ 0 := by simp
  change _ ↔ v.valuation F ((ξ : F) * ((ξ₀⁻¹ : Fˣ) : F)) = 1
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · intro h
    rw [← h0] at h
    exact (mul_inv_eq_one₀ hξ₀).mpr (mul_right_cancel₀ (by
      intro h'; rw [h', mul_zero] at h0; exact zero_ne_one h0) h)
  · intro h
    rw [(mul_inv_eq_one₀ hξ₀).mp h]
    exact h0

/-- The orbit series of the extended local test is absolutely summable: its nonzero terms lie on
one coset of the S-units, where they form the S-local theta series at an S-idele. -/
private theorem sLocalCarvingTheta_spec_summable (S : Finset V) (f : ℬₛ(S)) (g : I𝔽) :
    Summable (fun ξ : Fˣ ↦ sLocalCarvingIdeleTest S f
      (IdeleGroup.unitEmbedding (𝓞 F) F ξ * g)) := by
  by_cases hex : ∃ ξ₀ : Fˣ, IdeleGroup.unitEmbedding (𝓞 F) F ξ₀ * g ∈
      {g' : I𝔽 | ∀ v ∉ S, Valued.v (g'.val.2 v) = 1}
  swap
  · push Not at hex
    refine summable_zero.congr fun ξ ↦ ?_
    unfold sLocalCarvingIdeleTest
    rw [Set.indicator_of_notMem (hex ξ)]
  obtain ⟨ξ₀, h₀⟩ := hex
  let P : Set Fˣ := ((S : Set V).unit F : Set Fˣ)
  let h : Fˣ → ℂ := fun ξ ↦ f (Multiplicative.ofAdd (adeleProjection F S
    (IdeleGroup.unitEmbedding (𝓞 F) F ξ * g).val))
  have hterm (ξ : Fˣ) : sLocalCarvingIdeleTest S f (IdeleGroup.unitEmbedding (𝓞 F) F ξ * g) =
      P.indicator (fun ξ ↦ h (ξ * ξ₀)) (ξ * ξ₀⁻¹) := by
    unfold sLocalCarvingIdeleTest
    by_cases hξ : ξ * ξ₀⁻¹ ∈ P
    · rw [Set.indicator_of_mem ((sLocalCarvingTheta_spec_mem S g ξ₀ ξ h₀).mpr hξ),
        Set.indicator_of_mem hξ, inv_mul_cancel_right]
    · rw [Set.indicator_of_notMem (mt (sLocalCarvingTheta_spec_mem S g ξ₀ ξ h₀).mp hξ),
        Set.indicator_of_notMem hξ]
  refine (summable_congr hterm).mpr ?_
  refine ((Equiv.mulRight ξ₀⁻¹).summable_iff (f := P.indicator fun ξ ↦ h (ξ * ξ₀))).mpr ?_
  refine summable_subtype_iff_indicator.mp ?_
  let g'' : (SAdeleRing F S)ˣ :=
    Units.map (adeleProjection F S).toMonoidHom (IdeleGroup.unitEmbedding (𝓞 F) F ξ₀ * g)
  have hS := ((sLocalAdelicTheta_hasSumUniformlyOn F S f {g''} isCompact_singleton).hasSum
    (Set.mem_singleton g'')).summable
  have hG : Summable (fun u : ((S : Set V).integer F)ˣ ↦
      h (((Set.unitEquivUnitsInteger (S : Set V) F).symm u : Fˣ) * ξ₀)) := by
    refine hS.congr fun u ↦ congrArg f (congrArg Multiplicative.ofAdd ?_)
    simp only [map_mul, Units.val_mul]
    rw [mul_assoc]
    rfl
  refine (((Set.unitEquivUnitsInteger (S : Set V) F).toEquiv.summable_iff).mpr hG).congr
    fun x ↦ ?_
  simp

/-- Paper: (11.1.2.7), p. 480. At any representative of the class the displayed
orbit series is absolutely convergent and gives the raw theta generator. -/
theorem sLocalCarvingTheta_spec (S : Finset V) (f : ℬₛ(S)) (g : I𝔽) :
    Summable (fun ξ : Fˣ ↦ sLocalCarvingIdeleTest S f
      (IdeleGroup.unitEmbedding (𝓞 F) F ξ * g)) ∧
    sLocalCarvingTheta S f (classOf g) = ideleThetaSum (sLocalCarvingIdeleTest S f) g :=
  ⟨sLocalCarvingTheta_spec_summable S f g, sLocalCarvingTheta_classOf S f g⟩

/-- The S-component of an inserted S-idele is the S-idele itself. -/
private theorem sLocalCarvingTheta_sIdeleInsertion_proj (S : Finset V) (g : (SAdeleRing F S)ˣ) :
    adeleProjection F S (sIdeleInsertion F S g).val = g.val := by
  obtain ⟨h1, h2, -⟩ := sIdeleInsertion_apply F S g
  exact Prod.ext h1 (funext fun v ↦ h2 v)

/-- At an inserted S-idele, the outside unit condition on a principal translate holds exactly
for the S-units. -/
private theorem sLocalCarvingTheta_sIdeleInsertion_mem (S : Finset V) (g : (SAdeleRing F S)ˣ)
    (ξ : Fˣ) :
    (IdeleGroup.unitEmbedding (𝓞 F) F ξ * sIdeleInsertion F S g ∈
      {g' : I𝔽 | ∀ v ∉ S, Valued.v (g'.val.2 v) = 1}) ↔ ξ ∈ (S : Set V).unit F := by
  refine forall₂_congr fun v hv ↦ ?_
  have h1 : (IdeleGroup.unitEmbedding (𝓞 F) F ξ * sIdeleInsertion F S g).val.2 v =
      ((ξ : F) : v.adicCompletion F) := by
    change (algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ : F)) v * (sIdeleInsertion F S g).val.2 v = _
    rw [(sIdeleInsertion_apply F S g).2.2 v (by exact_mod_cast hv), mul_one]
    rfl
  rw [h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/-- Paper: (11.1.2.7), p. 480. At an inserted S-idele the outside unit condition
selects exactly the S-units, giving the S-local theta of Definition 2.3.1.1. -/
theorem sLocalCarvingTheta_sIdeleInsertion (S : Finset V) (f : ℬₛ(S)) (g : (SAdeleRing F S)ˣ) :
    sLocalCarvingTheta S f (classOf (sIdeleInsertion F S g)) = sLocalAdelicTheta F S f g := by
  rw [sLocalCarvingTheta_classOf, sLocalAdelicTheta_apply]
  unfold ideleThetaSum
  let P : Set Fˣ := ((S : Set V).unit F : Set Fˣ)
  let h : Fˣ → ℂ := fun ξ ↦ f (Multiplicative.ofAdd (adeleProjection F S
    (IdeleGroup.unitEmbedding (𝓞 F) F ξ * sIdeleInsertion F S g).val))
  have hterm (ξ : Fˣ) : sLocalCarvingIdeleTest S f
      (IdeleGroup.unitEmbedding (𝓞 F) F ξ * sIdeleInsertion F S g) = P.indicator h ξ := by
    unfold sLocalCarvingIdeleTest
    by_cases hξ : ξ ∈ P
    · rw [Set.indicator_of_mem ((sLocalCarvingTheta_sIdeleInsertion_mem S g ξ).mpr hξ),
        Set.indicator_of_mem hξ]
    · rw [Set.indicator_of_notMem (mt (sLocalCarvingTheta_sIdeleInsertion_mem S g ξ).mp hξ),
        Set.indicator_of_notMem hξ]
  rw [tsum_congr hterm, ← tsum_subtype P h]
  refine Eq.trans ?_ ((Set.unitEquivUnitsInteger (S : Set V) F).toEquiv.tsum_eq _)
  refine tsum_congr fun x ↦ congrArg f (congrArg Multiplicative.ofAdd ?_)
  rw [Units.val_mul, Units.val_mul, map_mul, sLocalCarvingTheta_sIdeleInsertion_proj]
  rfl

/-- The ideles that are units at every finite place outside `S` form an open set: they are
the range of the open insertion of the units of the adeles integral outside `S`. -/
private theorem integrable_sLocalCarvingTheta_normOne_isOpen (S : Finset V) :
    IsOpen {g : I𝔽 | ∀ v ∉ S, Valued.v (g.val.2 v) = 1} := by
  convert (integralIdeleInsertion_isOpenEmbedding F S).isOpen_range using 1
  ext g
  rw [Set.mem_setOf_eq, mem_range_integralIdeleInsertion]
  refine forall₂_congr fun v _ ↦ ?_
  have h1 : g.val.2 v * g.inv.2 v = 1 :=
    congrArg (fun x : AdeleRing (𝓞 F) F ↦ x.2 v) g.val_inv
  have h2 : g.inv.2 v * g.val.2 v = 1 :=
    congrArg (fun x : AdeleRing (𝓞 F) F ↦ x.2 v) g.inv_val
  exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
    (a := ⟨g.val.2 v, g.inv.2 v, h1, h2⟩)).symm

/-- At an idele that is a unit outside `S`, the raw theta series is the S-local theta of
its projection. -/
private theorem integrable_sLocalCarvingTheta_normOne_eq (S : Finset V) (f : ℬₛ(S)) (g : I𝔽)
    (hg : ∀ v ∉ S, Valued.v (g.val.2 v) = 1) :
    ideleThetaSum (sLocalCarvingIdeleTest S f) g =
      sLocalAdelicTheta F S f (Units.map (adeleProjection F S).toMonoidHom g) := by
  rw [sLocalAdelicTheta_apply]
  unfold ideleThetaSum
  let P : Set Fˣ := ((S : Set V).unit F : Set Fˣ)
  let h : Fˣ → ℂ := fun ξ ↦ f (Multiplicative.ofAdd (adeleProjection F S
    (IdeleGroup.unitEmbedding (𝓞 F) F ξ * g).val))
  have h₀ : IdeleGroup.unitEmbedding (𝓞 F) F 1 * g ∈
      {g' : I𝔽 | ∀ v ∉ S, Valued.v (g'.val.2 v) = 1} := by
    rw [map_one, one_mul]
    exact hg
  have hterm (ξ : Fˣ) : sLocalCarvingIdeleTest S f (IdeleGroup.unitEmbedding (𝓞 F) F ξ * g) =
      P.indicator h ξ := by
    have hmem := sLocalCarvingTheta_spec_mem S g 1 ξ h₀
    rw [inv_one, mul_one] at hmem
    unfold sLocalCarvingIdeleTest
    by_cases hξ : ξ ∈ P
    · rw [Set.indicator_of_mem (hmem.mpr hξ), Set.indicator_of_mem hξ]
    · rw [Set.indicator_of_notMem (mt hmem.mp hξ), Set.indicator_of_notMem hξ]
  rw [tsum_congr hterm, ← tsum_subtype P h]
  refine Eq.trans ?_ ((Set.unitEquivUnitsInteger (S : Set V) F).toEquiv.tsum_eq _)
  refine tsum_congr fun x ↦ congrArg f (congrArg Multiplicative.ofAdd ?_)
  rw [Units.val_mul, map_mul]
  rfl

/-- The raw theta series is continuous on the ideles: near an idele with a principal
translate that is a unit outside `S` it is the S-local theta of the projected translate, and
near any other idele it vanishes. -/
private theorem integrable_sLocalCarvingTheta_normOne_continuous (S : Finset V) (f : ℬₛ(S)) :
    Continuous (ideleThetaSum (sLocalCarvingIdeleTest S f)) := by
  let U := {g : I𝔽 | ∀ v ∉ S, Valued.v (g.val.2 v) = 1}
  have hU : IsOpen U := integrable_sLocalCarvingTheta_normOne_isOpen S
  have hUmul (a b : I𝔽) (ha : a ∈ U) (hb : b ∈ U) : a * b ∈ U := fun v hv ↦ by
    change Valued.v (a.val.2 v * b.val.2 v) = 1
    rw [Valuation.map_mul, ha v hv, hb v hv, one_mul]
  have hUinv (a : I𝔽) (ha : a ∈ U) : a⁻¹ ∈ U := fun v hv ↦ by
    have h := congrArg (fun x : AdeleRing (𝓞 F) F ↦ Valued.v (x.2 v)) a.inv_val
    change Valued.v (a.inv.2 v * a.val.2 v) = Valued.v (1 : v.adicCompletion F) at h
    rw [Valuation.map_mul, ha v hv, mul_one, map_one] at h
    exact h
  have hU1 : (1 : I𝔽) ∈ U := fun v _ ↦ map_one _
  have hshift (ξ : Fˣ) (g : I𝔽) : ideleThetaSum (sLocalCarvingIdeleTest S f)
      (IdeleGroup.unitEmbedding (𝓞 F) F ξ * g) = ideleThetaSum (sLocalCarvingIdeleTest S f) g := by
    rw [← sLocalCarvingTheta_classOf, ← sLocalCarvingTheta_classOf]
    congr 1
    rw [map_mul, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff (N := IdeleGroup.principalSubgroup (𝓞 F) F)
        (IdeleGroup.unitEmbedding (𝓞 F) F ξ)).mpr ⟨ξ, rfl⟩, one_mul]
  have hproj : Continuous (Units.map (adeleProjection F S).toMonoidHom) :=
    Continuous.units_map _ (continuous_adeleProjection F S)
  rw [continuous_iff_continuousAt]
  intro g₀
  by_cases h : ∃ ξ₀ : Fˣ, IdeleGroup.unitEmbedding (𝓞 F) F ξ₀ * g₀ ∈ U
  · obtain ⟨ξ₀, h₀⟩ := h
    have hmul : Continuous fun g : I𝔽 ↦ IdeleGroup.unitEmbedding (𝓞 F) F ξ₀ * g :=
      continuous_const.mul continuous_id
    have hnhds : ∀ᶠ g in 𝓝 g₀, IdeleGroup.unitEmbedding (𝓞 F) F ξ₀ * g ∈ U :=
      (hU.preimage hmul).mem_nhds h₀
    refine ((sLocalAdelicTheta F S f).continuous.comp (hproj.comp hmul)).continuousAt.congr
      (hnhds.mono fun g hg ↦ ?_)
    exact (integrable_sLocalCarvingTheta_normOne_eq S f _ hg).symm.trans (hshift ξ₀ g)
  · push_neg at h
    have hmul : Continuous fun g : I𝔽 ↦ g₀⁻¹ * g := continuous_const.mul continuous_id
    have hnhds : ∀ᶠ g in 𝓝 g₀, g₀⁻¹ * g ∈ U :=
      (hU.preimage hmul).mem_nhds (by simpa using hU1)
    refine (continuousAt_const (y := (0 : ℂ))).congr (hnhds.mono fun g hg ↦ ?_)
    symm
    unfold ideleThetaSum
    refine (tsum_congr fun ξ ↦ ?_).trans tsum_zero
    unfold sLocalCarvingIdeleTest
    refine Set.indicator_of_notMem (fun hmem ↦ h ξ ?_) _
    have := hUmul _ _ hmem (hUinv _ hg)
    convert this using 1
    group

/-- The principal-orbit sum is continuous on the idele class group. -/
theorem continuous_sLocalCarvingTheta (S : Finset V)
    (f : ℬₛ(S)) : Continuous (sLocalCarvingTheta S f) := by
  rw [(QuotientGroup.isQuotientMap_mk (IdeleGroup.principalSubgroup (𝓞 F) F)).continuous_iff]
  have h : sLocalCarvingTheta S f ∘ QuotientGroup.mk =
      ideleThetaSum (sLocalCarvingIdeleTest S f) :=
    funext fun g ↦ sLocalCarvingTheta_classOf S f g
  rw [h]
  exact integrable_sLocalCarvingTheta_normOne_continuous S f

/-- Paper: (11.1.2.7), p. 480. The raw theta is integrable on each norm-one
coset against a continuous norm-one character.
Deviation: This is the integrability needed for the character projection. -/
theorem integrable_sLocalCarvingTheta_normOne (S : Finset V) (ω : PontryaginDual C₁)
    (f : ℬₛ(S)) (g : C𝔽) :
    Integrable (fun h : C₁ ↦ sLocalCarvingTheta S f (h.val * g) * (ω h : ℂ)) μ₁ := by
  have : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  have : (μ₁).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hc : Continuous (fun h : C₁ ↦ sLocalCarvingTheta S f (h.val * g) * (ω h : ℂ)) :=
    ((continuous_sLocalCarvingTheta S f).comp
      (continuous_subtype_val.mul continuous_const)).mul
      (continuous_subtype_val.comp ω.continuous)
  exact hc.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))

/-- Paper: (11.1.2.7), p. 480. Average the raw theta generator against the
norm-one character and then apply the cutoff.
Deviation: The norm-one average places the generator in the claimed isotype. -/
def sLocalCarvingGenerator (S : Finset V) (ω : PontryaginDual C₁)
    (J : Set ℝ) (f : ℬₛ(S)) : C𝔽 → ℂ :=
  (norm𝔽 ⁻¹' J).indicator (fun g ↦ ∫ h : C₁,
    sLocalCarvingTheta S f (h.val * g) * (ω h : ℂ) ∂μ₁)

/-- Paper: (11.1.2.7), p. 480. For the trivial norm-one character the average
of a norm-one-invariant generator multiplies its cutoff by the Haar mass.
Deviation: Sanity check for the character average in the repaired generator. -/
theorem sLocalCarvingGenerator_trivial (S : Finset V) (J : Set ℝ) (f : ℬₛ(S))
    (_hf : ∀ (h : C₁) (g : C𝔽), sLocalCarvingTheta S f (h.val * g) = sLocalCarvingTheta S f g) :
    sLocalCarvingGenerator S 1 J f =
      fun g ↦ (μ₁).real univ • (norm𝔽 ⁻¹' J).indicator (sLocalCarvingTheta S f) g := by
  funext g
  unfold sLocalCarvingGenerator
  by_cases hg : g ∈ norm𝔽 ⁻¹' J
  · simp only [Set.indicator_of_mem hg, _hf]
    simp [integral_const]
  · simp [Set.indicator_of_notMem hg]

/-- At an idele that is a unit outside `S`, the class norm is the S-norm of its projection. -/
private theorem memLp_sLocalCarvingGenerator_norm (S : Finset V) (y : I𝔽)
    (hy : ∀ v ∉ S, Valued.v (y.val.2 v) = 1) :
    ((ideleClassNorm F (classOf y)).val : ℝ) =
      ((sIdeleNorm F S (Units.map (adeleProjection F S).toMonoidHom y)).val : ℝ) := by
  have hU : y ∈ range (integralIdeleInsertion F S) := by
    rw [mem_range_integralIdeleInsertion]
    intro v hv
    have h1 : y.val.2 v * y.inv.2 v = 1 :=
      congrArg (fun x : AdeleRing (𝓞 F) F ↦ x.2 v) y.val_inv
    have h2 : y.inv.2 v * y.val.2 v = 1 :=
      congrArg (fun x : AdeleRing (𝓞 F) F ↦ x.2 v) y.inv_val
    exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := ⟨y.val.2 v, y.inv.2 v, h1, h2⟩)).mpr (hy v hv)
  obtain ⟨u, rfl⟩ := hU
  exact congrArg (fun t : ℝ≥0ˣ ↦ ((t : ℝ≥0) : ℝ)) ((sIdeleNorm_spec F S).1 u)

/-- The raw theta generator decays at every inverse power of the class norm. -/
private theorem memLp_sLocalCarvingGenerator_decay (S : Finset V) (f : ℬₛ(S)) (k : ℕ)
    (hk : 1 ≤ k) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C𝔽, T < ((ideleClassNorm F g).val : ℝ) →
      ‖sLocalCarvingTheta S f g‖ ≤ C * (((ideleClassNorm F g).val : ℝ) ^ k)⁻¹ := by
  obtain ⟨C, T, hC, hT, hdec⟩ := sLocalAdelicTheta_decay_large F S f k hk
  refine ⟨C, T, hC, hT, fun g hg ↦ ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (IdeleGroup.principalSubgroup (𝓞 F) F) g
  rw [sLocalCarvingTheta_classOf]
  by_cases hex : ∃ ξ₀ : Fˣ, IdeleGroup.unitEmbedding (𝓞 F) F ξ₀ * x ∈
      {g' : I𝔽 | ∀ v ∉ S, Valued.v (g'.val.2 v) = 1}
  · obtain ⟨ξ₀, h₀⟩ := hex
    have hcl : classOf (IdeleGroup.unitEmbedding (𝓞 F) F ξ₀ * x) = classOf x := by
      rw [map_mul, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff (N := IdeleGroup.principalSubgroup (𝓞 F) F)
          (IdeleGroup.unitEmbedding (𝓞 F) F ξ₀)).mpr ⟨ξ₀, rfl⟩, one_mul]
    have heq : ideleThetaSum (sLocalCarvingIdeleTest S f) x =
        sLocalAdelicTheta F S f (Units.map (adeleProjection F S).toMonoidHom
          (IdeleGroup.unitEmbedding (𝓞 F) F ξ₀ * x)) := by
      rw [← sLocalCarvingTheta_classOf, ← hcl, sLocalCarvingTheta_classOf]
      exact integrable_sLocalCarvingTheta_normOne_eq S f _ h₀
    have hn := memLp_sLocalCarvingGenerator_norm S _ h₀
    rw [hcl] at hn
    rw [heq, hn]
    rw [hn] at hg
    exact hdec _ hg
  · push Not at hex
    have h0 : ideleThetaSum (sLocalCarvingIdeleTest S f) x = 0 := by
      unfold ideleThetaSum
      refine (tsum_congr fun ξ ↦ ?_).trans tsum_zero
      unfold sLocalCarvingIdeleTest
      exact Set.indicator_of_notMem (hex ξ) _
    rw [h0, norm_zero]
    have hpos : 0 < ((ideleClassNorm F (classOf x)).val : ℝ) :=
      NNReal.coe_pos.mpr (Units.zero_lt _)
    positivity

/-- The norm band from `a` to `T` is compact in the positive reals. -/
private theorem memLp_sLocalCarvingGenerator_isCompact (a T : ℝ) (ha : 0 < a) :
    IsCompact {t : ℝ≥0ˣ | ((t : ℝ≥0) : ℝ) ∈ Icc a T} := by
  let E : ℝ → ℝ≥0ˣ := fun x ↦ Units.mk0 (Real.exp x).toNNReal
    (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))
  have hE : Continuous E := by
    rw [Units.continuous_iff]
    refine ⟨continuous_real_toNNReal.comp Real.continuous_exp, ?_⟩
    simp only [E, Units.val_inv_eq_inv_val, Units.val_mk0]
    exact (continuous_real_toNNReal.comp Real.continuous_exp).inv₀ fun x ↦
      Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x))
  refine ((isCompact_Icc (a := Real.log a) (b := Real.log T)).image hE).of_isClosed_subset
    (isClosed_Icc.preimage (NNReal.continuous_coe.comp Units.continuous_val)) ?_
  rintro t ⟨h1, h2⟩
  have ht : 0 < ((t : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  refine ⟨Real.log ((t : ℝ≥0) : ℝ), ⟨Real.log_le_log ha h1, Real.log_le_log ht h2⟩, ?_⟩
  apply Units.ext
  apply NNReal.coe_injective
  change ((Real.exp (Real.log ((t : ℝ≥0) : ℝ))).toNNReal : ℝ) = _
  rw [Real.exp_log ht, Real.coe_toNNReal _ ht.le]

/-- Above any positive norm, the raw theta generator is bounded by a multiple of an
inverse power of the class norm. -/
private theorem memLp_sLocalCarvingGenerator_bound (S : Finset V) (f : ℬₛ(S)) (a : ℝ)
    (ha : 0 < a) (k : ℕ) (hk : 1 ≤ k) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ g : C𝔽, a ≤ ((ideleClassNorm F g).val : ℝ) →
      ‖sLocalCarvingTheta S f g‖ ≤ D * (((ideleClassNorm F g).val : ℝ) ^ k)⁻¹ := by
  obtain ⟨C, T, hC, hT, hdec⟩ := memLp_sLocalCarvingGenerator_decay S f k hk
  have hK : IsCompact ((m𝔽) ⁻¹' {t : ℝ≥0ˣ | ((t : ℝ≥0) : ℝ) ∈ Icc a T}) :=
    (isProperMap_ideleClassNorm F).isCompact_preimage
      (memLp_sLocalCarvingGenerator_isCompact a T ha)
  obtain ⟨K, hKb⟩ := hK.exists_bound_of_continuousOn
    (continuous_sLocalCarvingTheta S f).continuousOn
  refine ⟨max (max K 0 * T ^ k) C, le_max_of_le_right hC.le, fun g hg ↦ ?_⟩
  have hpos : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hinv : 0 < (((ideleClassNorm F g).val : ℝ) ^ k)⁻¹ := by positivity
  by_cases hgT : ((ideleClassNorm F g).val : ℝ) ≤ T
  · have h1 := hKb g ⟨hg, hgT⟩
    have h2 : (T ^ k)⁻¹ ≤ (((ideleClassNorm F g).val : ℝ) ^ k)⁻¹ :=
      inv_anti₀ (pow_pos hpos k) (pow_le_pow_left₀ hpos.le hgT k)
    calc ‖sLocalCarvingTheta S f g‖ ≤ max K 0 * T ^ k * (T ^ k)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ (pow_pos hT k).ne', mul_one]
          exact h1.trans (le_max_left _ _)
      _ ≤ max K 0 * T ^ k * (((ideleClassNorm F g).val : ℝ) ^ k)⁻¹ := by
          gcongr
      _ ≤ _ := by
          gcongr
          exact le_max_left _ _
  · calc ‖sLocalCarvingTheta S f g‖ ≤ C * (((ideleClassNorm F g).val : ℝ) ^ k)⁻¹ :=
          hdec g (lt_of_not_ge hgT)
      _ ≤ _ := by
          gcongr
          exact le_max_right _ _

/-- The norm-one character average of the raw theta generator is continuous. -/
private theorem memLp_sLocalCarvingGenerator_continuous (S : Finset V)
    (ω : PontryaginDual C₁) (f : ℬₛ(S)) :
    Continuous (fun g : C𝔽 ↦ ∫ h : C₁, sLocalCarvingTheta S f (h.val * g) * (ω h : ℂ) ∂μ₁) := by
  have : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  have : (μ₁).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hθ := continuous_sLocalCarvingTheta S f
  have hjoint : Continuous (fun p : C𝔽 × C₁ ↦
      sLocalCarvingTheta S f (p.2.val * p.1) * (ω p.2 : ℂ)) :=
    (hθ.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)).mul
      (continuous_subtype_val.comp (ω.continuous.comp continuous_snd))
  let Φ : C𝔽 → C(C₁, ℂ) := fun g ↦ ⟨fun h ↦ sLocalCarvingTheta S f (h.val * g) * (ω h : ℂ),
    (hθ.comp (continuous_subtype_val.mul continuous_const)).mul
      (continuous_subtype_val.comp ω.continuous)⟩
  have hΦ : Continuous Φ := ContinuousMap.continuous_of_continuous_uncurry Φ hjoint
  have hint (u : C(C₁, ℂ)) : Integrable u μ₁ :=
    u.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlip : LipschitzWith ((μ₁).real univ).toNNReal
      (fun u : C(C₁, ℂ) ↦ ∫ h, u h ∂μ₁) := by
    refine LipschitzWith.of_dist_le_mul fun u v ↦ ?_
    rw [dist_eq_norm, dist_eq_norm, ← integral_sub (hint u) (hint v),
      Real.coe_toNNReal _ measureReal_nonneg, mul_comm]
    exact norm_integral_le_of_norm_le_const
      (.of_forall fun h ↦ (u - v).norm_coe_le_norm h)
  exact hlip.continuous.comp hΦ

/-- On its band the projected generator is bounded by a decaying exponential of the
logarithmic norm. -/
private theorem memLp_sLocalCarvingGenerator_pointwise (S : Finset V) (ω : PontryaginDual C₁)
    (J : Set ℝ) (f : ℬₛ(S)) (a D : ℝ) (ha : 0 < a) (hD0 : 0 ≤ D) (k : ℕ)
    (hJ : ∀ x ∈ J, a ≤ x)
    (hD : ∀ g : C𝔽, a ≤ ((ideleClassNorm F g).val : ℝ) →
      ‖sLocalCarvingTheta S f g‖ ≤ D * (((ideleClassNorm F g).val : ℝ) ^ k)⁻¹)
    (g : C𝔽) :
    ‖sLocalCarvingGenerator S ω J f g‖ ≤ (Ici (Real.log a)).indicator
      (fun x ↦ (μ₁).real univ * D * Real.exp (-(k : ℝ) * x))
      (Real.log ((ideleClassNorm F g).val : ℝ)) := by
  have : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  have : (μ₁).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  unfold sLocalCarvingGenerator
  by_cases hg : g ∈ (fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ)) ⁻¹' J
  · have hag : a ≤ ((ideleClassNorm F g).val : ℝ) := hJ _ hg
    have hpos : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    have hlog : Real.log ((ideleClassNorm F g).val : ℝ) ∈ Ici (Real.log a) :=
      Real.log_le_log ha hag
    rw [Set.indicator_of_mem hg, Set.indicator_of_mem hlog]
    have hexp : Real.exp (-(k : ℝ) * Real.log ((ideleClassNorm F g).val : ℝ)) =
        (((ideleClassNorm F g).val : ℝ) ^ k)⁻¹ := by
      rw [neg_mul, Real.exp_neg, ← Real.log_pow, Real.exp_log (pow_pos hpos k)]
    rw [hexp]
    have hb : ∀ h : C₁, ‖sLocalCarvingTheta S f (h.val * g) * (ω h : ℂ)‖ ≤
        D * (((ideleClassNorm F g).val : ℝ) ^ k)⁻¹ := by
      intro h
      have hN : ideleClassNorm F (h.val * g) = ideleClassNorm F g := by
        rw [map_mul, MonoidHom.mem_ker.mp h.property, one_mul]
      rw [norm_mul, Circle.norm_coe, mul_one]
      have h1 := hD (h.val * g) (by rw [hN]; exact hag)
      rwa [hN] at h1
    calc ‖∫ h : C₁, sLocalCarvingTheta S f (h.val * g) * (ω h : ℂ) ∂μ₁‖
        ≤ D * (((ideleClassNorm F g).val : ℝ) ^ k)⁻¹ * (μ₁).real univ :=
          norm_integral_le_of_norm_le_const (.of_forall hb)
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hg, norm_zero]
    exact Set.indicator_nonneg (fun x _ ↦
      mul_nonneg (mul_nonneg measureReal_nonneg hD0) (Real.exp_pos _).le) _

/-- The zero-line weight times the square of a one-sided decaying exponential is
Lebesgue integrable once the decay rate beats the Sobolev degree. -/
private theorem memLp_sLocalCarvingGenerator_integrable_real (s c E : ℝ) (k : ℕ)
    (hs : 0 ≤ s) (hks : s + 1 ≤ 2 * (k : ℝ)) :
    Integrable (fun x : ℝ ↦ (ENNReal.ofReal (intervalSobolevDensity 0 0 s x)).toReal •
      ‖(Ici c).indicator (fun x ↦ E * Real.exp (-(k : ℝ) * x)) x‖ ^ 2) := by
  let φ : ℝ → ℝ := fun x ↦ E ^ 2 * Real.exp (s * |x| - 2 * k * x)
  have hφc : Continuous φ := by fun_prop
  have hφ : IntegrableOn φ (Ici c) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine integrable_of_isBigO_exp_neg one_pos hφc.continuousOn ?_
    refine Asymptotics.IsBigO.of_bound (E ^ 2) ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    simp only [φ]
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg hx]
    gcongr
    nlinarith
  have hw : Continuous (intervalSobolevDensity 0 0 s) := by
    unfold intervalSobolevDensity
    refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun t ↦ Or.inl ?_)
    positivity
  have hmeas : Measurable (fun x : ℝ ↦ (ENNReal.ofReal (intervalSobolevDensity 0 0 s x)).toReal •
      ‖(Ici c).indicator (fun x ↦ E * Real.exp (-(k : ℝ) * x)) x‖ ^ 2) :=
    (ENNReal.measurable_ofReal.comp hw.measurable).ennreal_toReal.smul
      (((Measurable.indicator (by fun_prop) measurableSet_Ici).norm).pow_const 2)
  refine ((integrable_indicator_iff measurableSet_Ici).mpr hφ).mono'
    hmeas.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  by_cases hx : x ∈ Ici c
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    have hw0 : 0 ≤ intervalSobolevDensity 0 0 s x := by
      unfold intervalSobolevDensity
      positivity
    rw [ENNReal.toReal_ofReal hw0, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
    have hden : intervalSobolevDensity 0 0 s x ≤ Real.exp (s * |x|) := by
      unfold intervalSobolevDensity
      simp only [mul_zero, zero_mul, Real.exp_zero, max_self, one_mul]
      have h1 : 1 + x ^ 2 ≤ Real.exp (2 * |x|) := by
        have h := Real.add_one_le_exp |x|
        have h2 : Real.exp (2 * |x|) = Real.exp |x| ^ 2 := by rw [two_mul, Real.exp_add, sq]
        rw [h2]
        nlinarith [abs_nonneg x, sq_abs x]
      calc (1 + x ^ 2) ^ (s / 2) ≤ Real.exp (2 * |x|) ^ (s / 2) :=
            Real.rpow_le_rpow (by positivity) h1 (by positivity)
        _ = Real.exp (s * |x|) := by rw [← Real.exp_mul]; ring_nf
    have hsq : ‖E * Real.exp (-(k : ℝ) * x)‖ ^ 2 = E ^ 2 * Real.exp (-(2 * k * x)) := by
      rw [Real.norm_eq_abs, sq_abs, mul_pow, ← Real.exp_nat_mul]
      ring_nf
    rw [hsq]
    calc intervalSobolevDensity 0 0 s x * (E ^ 2 * Real.exp (-(2 * k * x)))
        ≤ Real.exp (s * |x|) * (E ^ 2 * Real.exp (-(2 * k * x))) := by gcongr
      _ = φ x := by
          simp only [φ]
          rw [sub_eq_add_neg, Real.exp_add]
          ring
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

/-- The logarithm of the class norm carries the canonical modulated Haar measure to
Lebesgue measure. -/
private theorem memLp_sLocalCarvingGenerator_measurePreserving :
    MeasurePreserving (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
      (canonicalModulatedHaar m𝔽
        (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽))
      volume := by
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hcont : Continuous (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ)) :=
    Real.continuousOn_log.comp_continuous
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous))
      fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  obtain ⟨τ, hτc, hτ⟩ := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.2.1
  let τ' : ℝ≥0ˣ →ₜ* C𝔽 := ⟨τ, hτc⟩
  let : CompactSpace (m𝔽).toMonoidHom.ker :=
    isCompact_iff_compactSpace.mp (IsModulation.isCompact_ker hm)
  let μk : Measure (m𝔽).toMonoidHom.ker := Measure.haarMeasure ⊤
  let : IsProbabilityMeasure μk := ⟨Measure.haarMeasure_self⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  refine ⟨hcont.measurable, ?_⟩
  rw [canonicalModulatedHaar_eq_map_prod m𝔽 hm τ' hτ μk Measure.haarMeasure_self]
  have hsplit_meas : Measurable (fun z : (m𝔽).toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : C𝔽) * τ' z.2) :=
    ((continuous_subtype_val.comp continuous_fst).mul
      (τ'.continuous.comp continuous_snd)).measurable
  rw [Measure.map_map hcont.measurable hsplit_meas]
  have hcomp : ((fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ)) ∘
      fun z : (m𝔽).toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : C𝔽) * τ' z.2) =
      (fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) ∘ Prod.snd := by
    funext ⟨k, t⟩
    change Real.log ((ideleClassNorm F ((k : C𝔽) * τ t)).val : ℝ) =
      Real.log ((t.val : ℝ≥0) : ℝ)
    have hk : ideleClassNorm F (k : C𝔽) = 1 := k.property
    rw [map_mul, hk, one_mul, hτ t]
  have hlogt : Measurable (fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) :=
    (Real.continuousOn_log.comp_continuous (NNReal.continuous_coe.comp Units.continuous_val)
      fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne').measurable
  rw [hcomp, ← Measure.map_map hlogt measurable_snd,
    (measurePreserving_snd (μ := μk) (ν := positiveRealHaar)).map_eq]
  unfold positiveRealHaar
  have hexp : Measurable (fun x : ℝ ↦
      Units.mk0 (Real.exp x).toNNReal
        (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))) :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  rw [Measure.map_map hlogt hexp]
  have hid : ((fun t : ℝ≥0ˣ ↦ Real.log ((t.val : ℝ≥0) : ℝ)) ∘ fun x : ℝ ↦
      Units.mk0 (Real.exp x).toNNReal
        (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))) = id := by
    funext x
    change Real.log ((Real.exp x).toNNReal : ℝ) = x
    rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]
  rw [hid, Measure.map_id]

/-- Paper: Theorem 11.1.2.1(3), p. 480. The projected cutoff generators are
square-integrable for the zero-line weight. -/
theorem memLp_sLocalCarvingGenerator {S : Finset V} (χ : PontryaginDual C𝔽)
    (_hχ : Unramified(χ, S)) (_hPic : TrivialPic((S : Set V)))
    (s : ℝ) (_hs : DegreeBound(s)) (twoSided : Bool) (Λ : ℝ) (_hΛ : 0 < Λ)
    (f : ℬₛ(S)) (_hf : f (Multiplicative.ofAdd 0) = 0)
    (_hFf : sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0) :
    MemLp (sLocalCarvingGenerator S (ωOf(χ)) (J(twoSided, Λ)) f) 2 (ν(s)) := by
  have hs0 : 0 ≤ s := (mul_nonneg zero_le_two (Nat.cast_nonneg _)).trans _hs
  have hk1 : 1 ≤ ⌈s⌉₊ + 1 := Nat.le_add_left 1 _
  have hks : s + 1 ≤ 2 * ((⌈s⌉₊ + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil s
    push_cast
    linarith
  have ha : 0 < Λ⁻¹ := inv_pos.mpr _hΛ
  have hJ : ∀ x ∈ J(twoSided, Λ), Λ⁻¹ ≤ x := by
    intro x hx
    unfold sLocalCarvingBand at hx
    split_ifs at hx
    · exact hx.1
    · exact hx
  obtain ⟨D, hD0, hD⟩ := memLp_sLocalCarvingGenerator_bound S f Λ⁻¹ ha (⌈s⌉₊ + 1) hk1
  have : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  have : (μ₁).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let r : ℝ → ℝ := (Ici (Real.log Λ⁻¹)).indicator
    (fun x ↦ (μ₁).real univ * D * Real.exp (-((⌈s⌉₊ + 1 : ℕ) : ℝ) * x))
  have hL : Continuous (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ)) :=
    Real.continuousOn_log.comp_continuous
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous))
      fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  have hr : Measurable r := Measurable.indicator (by fun_prop) measurableSet_Ici
  have hRmeas : AEStronglyMeasurable (fun g : C𝔽 ↦ r (Real.log ((ideleClassNorm F g).val : ℝ)))
      (ν(s)) := (hr.comp hL.measurable).aestronglyMeasurable
  have hgen : sLocalCarvingGenerator S (ωOf(χ)) (J(twoSided, Λ)) f =
      ((fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ)) ⁻¹' J(twoSided, Λ)).indicator
        (fun g ↦ ∫ h : C₁, sLocalCarvingTheta S f (h.val * g) * ((ωOf(χ)) h : ℂ) ∂μ₁) := rfl
  have hmeasJ : MeasurableSet ((fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ)) ⁻¹'
      J(twoSided, Λ)) :=
    (hJ(twoSided, Λ)).preimage
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).measurable
  have hmeas : AEStronglyMeasurable (sLocalCarvingGenerator S (ωOf(χ)) (J(twoSided, Λ)) f)
      (ν(s)) := by
    rw [hgen]
    exact ((memLp_sLocalCarvingGenerator_continuous S (ωOf(χ)) f).measurable.indicator
      hmeasJ).aestronglyMeasurable
  refine MemLp.of_le (g := fun g : C𝔽 ↦ r (Real.log ((ideleClassNorm F g).val : ℝ))) ?_ hmeas
    (ae_of_all _ fun g ↦ ?_)
  · rw [memLp_two_iff_integrable_sq_norm hRmeas]
    have hwc : Continuous (intervalSobolevDensity 0 0 s) := by
      unfold intervalSobolevDensity
      refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun t ↦ Or.inl ?_)
      positivity
    refine (integrable_withDensity_iff_integrable_smul'
      (f := fun g : C𝔽 ↦ ENNReal.ofReal
        (intervalSobolevDensity 0 0 s (Real.log ((ideleClassNorm F g).val : ℝ))))
      (ENNReal.measurable_ofReal.comp (hwc.comp hL).measurable)
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mpr ?_
    have hreal := memLp_sLocalCarvingGenerator_integrable_real s (Real.log Λ⁻¹)
      ((μ₁).real univ * D) (⌈s⌉₊ + 1) hs0 hks
    change Integrable ((fun x : ℝ ↦ (ENNReal.ofReal (intervalSobolevDensity 0 0 s x)).toReal •
      ‖r x‖ ^ 2) ∘ (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))) μ𝔽
    rw [ideleClassTamagawaMeasure_eq_smul_canonical]
    refine Integrable.smul_measure ?_ (measure_ne_top _ _)
    exact (memLp_sLocalCarvingGenerator_measurePreserving.integrable_comp
      hreal.aestronglyMeasurable).mpr hreal
  · exact (memLp_sLocalCarvingGenerator_pointwise S (ωOf(χ)) (J(twoSided, Λ)) f Λ⁻¹ D ha hD0
      (⌈s⌉₊ + 1) hJ hD g).trans (Real.le_norm_self _)

/-- At the trivial character the cutoff carving limit consists of vectors that
are almost everywhere invariant under each fixed norm-one translation. -/
theorem sLocalCarvingLimit_trivial_ae_translate {S : Finset V}
    (hχ : Unramified((1 : PontryaginDual C𝔽), S)) (hPic : TrivialPic((S : Set V)))
    (s : ℝ) (hs : DegreeBound(s)) (twoSided : Bool) (Λ : ℝ) (hΛ : 0 < Λ)
    {u : W(s)}
    (hu : u ∈ sLocalCarvingLimit s (ωOf((1 : PontryaginDual C𝔽))) S
      (J(twoSided, Λ)) (hJ(twoSided, Λ))) (g : C₁) :
    (fun x ↦ u (g.val⁻¹ * x)) =ᵐ[μ𝔽] (u : C𝔽 → ℂ) := by
  let hs₀ : 0 ≤ s := (mul_nonneg zero_le_two (Nat.cast_nonneg _)).trans hs
  let J := J(twoSided, Λ)
  let hJ := hJ(twoSided, Λ)
  let M := M(s, J, hJ)
  obtain ⟨v, hv, he⟩ := Submodule.mem_map.mp
    (sLocalCarvingLimit_le_cutoffIsotype 1 hχ hPic s hs twoSided Λ hΛ hu)
  have hMv : M v = u := he
  have hvfix : hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs₀ g.val v = v := by
    have h := (mem_actionIsotype _ _ _).mp hv g
    change hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs₀ g.val v = (1 : ℂ) • v at h
    simpa only [one_smul] using h
  have hufix : hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs₀ g.val u = u := by
    rw [← hMv, ← sLocalCutoffCarving_le_cutoffIsotype_comm s hs₀ J hJ g v, hvfix]
  simpa only [hufix] using (hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s le_rfl hs₀ g.val u).symm

-- TODO(paper-gap): Page 483 uses R_{Λ,S} without defining it. Both spans in
-- the quotient already have Fourier value zero. The argument still needs to
-- approximate every vector of the intersection by projected local generators.

/-- Paper: Theorem 11.1.2.1(3), pp. 482-483. Every projected S-local generator lies
in every finite-place cutoff stage. This is the convergence step of the printed
proof of (3): by Proposition 11.1.1.2 the generator is the limit of the projected
local generators along a cofinal sequence, whose tail from any stage on lies in that
stage, and the stages are closed.
Remaining input: this file has no Proposition 11.1.1.2 for the extension by the unit
ideles outside `S`, so that convergence is not available here. -/
private theorem sLocalCarvingLimit_eq_closedSpan_generator_mem {S : Finset V}
    (χ : PontryaginDual C𝔽) (hχ : Unramified(χ, S)) (hPic : TrivialPic((S : Set V)))
    (s : ℝ) (hs : DegreeBound(s)) (twoSided : Bool) (Λ : ℝ) (hΛ : 0 < Λ)
    (f : ℬₛ(S)) (hf : f (Multiplicative.ofAdd 0) = 0)
    (hFf : sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0)
    (i : SLocalCarvingIndex (F := F) S) :
    (memLp_sLocalCarvingGenerator χ hχ hPic s hs twoSided Λ hΛ f hf hFf).toLp
        (sLocalCarvingGenerator S (ωOf(χ)) (J(twoSided, Λ)) f) ∈
      sLocalCutoffCarving s (ωOf(χ)) i.val (J(twoSided, Λ)) (hJ(twoSided, Λ)) := by
  sorry

/-- Paper: Theorem 11.1.2.1(3), pp. 482-483. The closed span of the projected
generators is contained in the cofinal limit, which is closed and contains each of
them by `sLocalCarvingLimit_eq_closedSpan_generator_mem`. -/
private theorem sLocalCarvingLimit_eq_closedSpan_ge {S : Finset V} (χ : PontryaginDual C𝔽)
    (hχ : Unramified(χ, S)) (hPic : TrivialPic((S : Set V)))
    (s : ℝ) (hs : DegreeBound(s)) (twoSided : Bool) (Λ : ℝ) (hΛ : 0 < Λ) :
    (Submodule.span ℂ {u : W(s) |
      ∃ (f : ℬₛ(S)) (hf : f (Multiplicative.ofAdd 0) = 0)
        (hFf : sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0),
        u = (memLp_sLocalCarvingGenerator χ hχ hPic s hs twoSided Λ hΛ f hf hFf).toLp
          (sLocalCarvingGenerator S (ωOf(χ)) (J(twoSided, Λ)) f)}).topologicalClosure ≤
      sLocalCarvingLimit s (ωOf(χ)) S (J(twoSided, Λ)) (hJ(twoSided, Λ)) := by
  refine le_iInf fun i ↦ ?_
  unfold sLocalCutoffCarving
  refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_)
    (Submodule.isClosed_topologicalClosure _)
  rintro u ⟨f, hf, hFf, rfl⟩
  exact sLocalCarvingLimit_eq_closedSpan_generator_mem χ hχ hPic s hs twoSided Λ hΛ f hf hFf i

/-- Paper: Theorem 11.1.2.1(3), p. 483. The cofinal limit is contained in the closed
span of the projected generators. This is the quotient step of the printed proof: if the
closure of the span of the tests with both vanishing conditions were smaller than the
span of those with only `\widehat{f}(0) = 0`, the quotient would extend `\widehat{\delta}_0`
continuously, which multiplication by the idelic norm contradicts.
Remaining input: the object `R_{Λ,S}` that the printed argument uses at this point is
never defined, and the approximation of a vector of the intersection by projected local
generators is not established. -/
private theorem sLocalCarvingLimit_eq_closedSpan_le {S : Finset V} (χ : PontryaginDual C𝔽)
    (hχ : Unramified(χ, S)) (hPic : TrivialPic((S : Set V)))
    (s : ℝ) (hs : DegreeBound(s)) (twoSided : Bool) (Λ : ℝ) (hΛ : 0 < Λ) :
    sLocalCarvingLimit s (ωOf(χ)) S (J(twoSided, Λ)) (hJ(twoSided, Λ)) ≤
      (Submodule.span ℂ {u : W(s) |
        ∃ (f : ℬₛ(S)) (hf : f (Multiplicative.ofAdd 0) = 0)
          (hFf : sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0),
          u = (memLp_sLocalCarvingGenerator χ hχ hPic s hs twoSided Λ hΛ f hf hFf).toLp
            (sLocalCarvingGenerator S (ωOf(χ)) (J(twoSided, Λ)) f)}).topologicalClosure := by
  sorry

/-- Paper: Theorem 11.1.2.1(3), p. 480. The cofinal limit is the closed span of
the projected cutoff theta functions of local tests whose value and Fourier value
at zero vanish.
Deviation: Use the norm-one character average in (11.1.2.7). The closure is
taken in the full weighted L² space, where the cutoff isotype is closed. -/
theorem sLocalCarvingLimit_eq_closedSpan {S : Finset V} (χ : PontryaginDual C𝔽)
    (hχ : Unramified(χ, S)) (hPic : TrivialPic((S : Set V)))
    (s : ℝ) (hs : DegreeBound(s)) (twoSided : Bool) (Λ : ℝ) (hΛ : 0 < Λ) :
    sLocalCarvingLimit s (ωOf(χ)) S (J(twoSided, Λ)) (hJ(twoSided, Λ)) = (Submodule.span ℂ {u : W(s) |
      ∃ (f : ℬₛ(S)) (hf : f (Multiplicative.ofAdd 0) = 0)
        (hFf : sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0),
        u = (memLp_sLocalCarvingGenerator χ hχ hPic s hs twoSided Λ hΛ f hf hFf).toLp
          (sLocalCarvingGenerator S (ωOf(χ)) (J(twoSided, Λ)) f)}).topologicalClosure :=
  le_antisymm
    (sLocalCarvingLimit_eq_closedSpan_le χ hχ hPic s hs twoSided Λ hΛ)
    (sLocalCarvingLimit_eq_closedSpan_ge χ hχ hPic s hs twoSided Λ hΛ)

/-- The L² norm of a vector of a weighted L² space that agrees almost everywhere with the
restriction of another vector to a measurable set is the weighted integral of the square of
the other vector over the set. -/
private theorem sLocalCarving_cutoff_norm_aux {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (w : A → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (E : Set A) (hE : MeasurableSet E)
    (u v : Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (w x)))
    (hv : (v : A → ℂ) =ᵐ[μ.withDensity fun x ↦ ENNReal.ofReal (w x)] E.indicator (u : A → ℂ)) :
    IntegrableOn (fun x ↦ ‖u x‖ ^ 2 * w x) E μ ∧
      ‖v‖ = Real.sqrt (∫ x in E, ‖u x‖ ^ 2 * w x ∂μ) := by
  have hd : Measurable fun x ↦ ENNReal.ofReal (w x) := hw.ennreal_ofReal
  have hfin : ∀ᵐ x ∂μ, ENNReal.ofReal (w x) < ⊤ := .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hreal (x : A) : (ENNReal.ofReal (w x)).toReal = w x := ENNReal.toReal_ofReal (hw0 x)
  have hsq (f : Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (w x))) : Integrable (fun x ↦ ‖f x‖ ^ 2) (μ.withDensity fun x ↦ ENNReal.ofReal (w x)) := by
    have h := (Lp.memLp f).integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hu : Integrable (fun x ↦ ‖u x‖ ^ 2 * w x) μ := by
    have h := (integrable_withDensity_iff_integrable_smul' hd hfin).mp (hsq u)
    refine h.congr (.of_forall fun x ↦ ?_)
    simp only [hreal, smul_eq_mul, mul_comm]
  refine ⟨hu.integrableOn, ?_⟩
  have hnorm : ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂(μ.withDensity fun x ↦ ENNReal.ofReal (w x)) := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner v v)]
    congr 1
    funext x
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (v x)
  have hint : ∫ x, ‖v x‖ ^ 2 ∂(μ.withDensity fun x ↦ ENNReal.ofReal (w x)) = ∫ x in E, ‖u x‖ ^ 2 * w x ∂μ := by
    calc ∫ x, ‖v x‖ ^ 2 ∂(μ.withDensity fun x ↦ ENNReal.ofReal (w x)) = ∫ x, E.indicator (fun x ↦ ‖u x‖ ^ 2) x ∂(μ.withDensity fun x ↦ ENNReal.ofReal (w x)) := by
          refine integral_congr_ae (hv.mono fun x hx ↦ ?_)
          change ‖v x‖ ^ 2 = _
          rw [hx]
          by_cases hxE : x ∈ E
          · simp [hxE]
          · simp [hxE]
      _ = ∫ x in E, ‖u x‖ ^ 2 ∂(μ.withDensity fun x ↦ ENNReal.ofReal (w x)) := integral_indicator hE
      _ = ∫ x in E, (ENNReal.ofReal (w x)).toReal • ‖u x‖ ^ 2 ∂μ :=
          setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hd.aemeasurable (ae_restrict_of_ae hfin) _ hE
      _ = _ := by
          refine setIntegral_congr_fun hE fun x _ ↦ ?_
          simp only [hreal, smul_eq_mul, mul_comm]
  rw [← hint, ← hnorm, Real.sqrt_sq (norm_nonneg v)]

/-- Paper: (11.1.2.8)–(11.1.2.9), p. 481. The cutoff norm is the weighted
L² norm restricted to the idelic norm band.
Deviation: For the two-sided cutoff the integral is over the bounded band. -/
theorem sLocalCarving_cutoff_norm (s : ℝ) (twoSided : Bool) (Λ : ℝ) (u : W(s)) :
    let E := norm𝔽 ⁻¹' J(twoSided, Λ)
    let integrand := fun g : C𝔽 ↦ ‖u g‖ ^ 2 * (1 + Real.log (norm𝔽 g) ^ 2) ^ (s / 2)
    IntegrableOn integrand E μ𝔽 ∧
      ‖M(s, J(twoSided, Λ), hJ(twoSided, Λ)) u‖ =
        Real.sqrt (∫ g in E, integrand g ∂μ𝔽) := by
  intro E integrand
  have hn : Continuous norm𝔽 :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hdens : Continuous (intervalSobolevDensity 0 0 s) := by
    unfold intervalSobolevDensity
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).max
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
      (Continuous.rpow_const (f := fun x : ℝ ↦ 1 + x ^ 2) (by fun_prop)
        fun x ↦ Or.inl (by positivity))
  have hm : Measurable fun g : C𝔽 ↦ intervalSobolevDensity 0 0 s (Real.log (norm𝔽 g)) :=
    hdens.measurable.comp (Real.measurable_log.comp hn.measurable)
  have hw0 (g : C𝔽) : 0 ≤ intervalSobolevDensity 0 0 s (Real.log (norm𝔽 g)) :=
    mul_nonneg (le_max_of_le_left (Real.exp_pos _).le) (Real.rpow_nonneg (by positivity) _)
  have hv : (M(s, J(twoSided, Λ), hJ(twoSided, Λ)) u : C𝔽 → ℂ) =ᵐ[ν(s)] E.indicator (u : C𝔽 → ℂ) := by
    refine (modulatedAbsoluteCutoffOperator_apply m𝔽 (ν(s)) _ _ u).trans (.of_forall fun g ↦ ?_)
    by_cases hg : g ∈ E
    · have hg' : ((m𝔽 g).val : ℝ) ∈ J(twoSided, Λ) := hg
      simp [modulatedAbsoluteCutoff, indicator, hg, hg']
    · have hg' : ((m𝔽 g).val : ℝ) ∉ J(twoSided, Λ) := hg
      simp [modulatedAbsoluteCutoff, indicator, hg, hg']
  have h := sLocalCarving_cutoff_norm_aux μ𝔽
    (fun g ↦ intervalSobolevDensity 0 0 s (Real.log (norm𝔽 g))) hm hw0 E
    (hn.measurable (hJ(twoSided, Λ))) u _ hv
  have hw (g : C𝔽) : intervalSobolevDensity 0 0 s (Real.log (norm𝔽 g)) =
      (1 + Real.log (norm𝔽 g) ^ 2) ^ (s / 2) := by
    simp [intervalSobolevDensity]
  simp only [hw] at h
  exact h

/-- Paper: (11.1.2.10)–(11.1.2.11), p. 481. The image under the cutoff of the
completed uncut stage lies in the cutoff stage, and its closure is the cutoff stage.
Deviation: The equality takes the closure of the image of the completed stage.
The argument in print establishes density there. -/
theorem sLocalCutoffCarving_eq_closure_map (s : ℝ) (ω : PontryaginDual C₁)
    (T : Finset V) (J : Set ℝ) (hJ : MeasurableSet J) :
    sLocalCutoffCarving s ω T J hJ =
      ((sLocalUncutCarving s ω T).map (M(s, J, hJ)).toLinearMap).topologicalClosure := by
  have closureImage {E G ι : Type _} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
      [ContinuousAdd E] [ContinuousSMul ℂ E] [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
      [ContinuousAdd G] [ContinuousSMul ℂ G] (L : E →L[ℂ] G) (f : ι → E) :
      (Submodule.span ℂ (range (fun i ↦ L (f i)))).topologicalClosure =
        ((Submodule.span ℂ (range f)).topologicalClosure.map L.toLinearMap).topologicalClosure := by
    let B := Submodule.span ℂ (range f)
    have h : Submodule.span ℂ (range (fun i ↦ L (f i))) = B.map L.toLinearMap :=
      (congrArg (Submodule.span ℂ) (Set.range_comp' (L : E → G) f)).trans
        (Submodule.map_span L.toLinearMap (range f)).symm
    refine (congrArg Submodule.topologicalClosure h).trans (le_antisymm ?_ ?_)
    · exact Submodule.topologicalClosure_mono (Submodule.map_mono B.le_topologicalClosure)
    · exact Submodule.topologicalClosure_minimal _ (B.topologicalClosure_map L) (Submodule.isClosed_topologicalClosure _)
  dsimp only [sLocalCutoffCarving, sLocalUncutCarving, IdeleClassZeroLineSobolev, CompactIntervalSobolev, Bool.false_eq_true, ite_false]
  with_reducible_and_instances
    exact closureImage (E := Lp ℂ 2 (ν(s))) (G := Lp ℂ 2 (ν(s))) (ι := ℬ₀)
      (M(s, J, hJ)) (fun g : ℬ₀ ↦ θ(s, ω, P(T, g)))

-- TODO(paper-gap): For (11.1.2.11), closed range of the cutoff on the ambient space
-- does not establish closed range on each completed uncut stage.

end RiemannMasullo
