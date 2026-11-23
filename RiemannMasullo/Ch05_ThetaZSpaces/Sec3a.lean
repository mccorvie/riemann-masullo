module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
public import RiemannMasullo.Ch03_IdelicZeta.Sec4
public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.PiTopology
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Non-archimedean principal values and distributions supported at the origin

Masullo, §5.3.1–5.3.2, pp. 240–249.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set TopologicalSpace Topology
open scoped ContDiff Distributions NNReal NumberField.AdeleRing SchwartzMap TensorProduct

namespace RiemannMasullo

set_option quotPrecheck false

section FinitePlace

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Fᵥ(" v ")" => HeightOneSpectrum.adicCompletion F v
local notation "Uᵥ(" v ")" => (HeightOneSpectrum.adicCompletionIntegers F v).units
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "vval(" v ")" => (Valued.v : Valuation Fᵥ(v) (WithZero (Multiplicative ℤ)))

/-- Paper: Lemma 5.3.1.1, p. 240.
The difference of a local test function and its inverse-unit pullback is linear. -/
theorem finitePlaceDifference_isLinear (v : V) (π : Fᵥ(v)ˣ) :
    IsLinearMap ℂ (fun f : ℬ(Fᵥ(v)) ↦ f - schwartzBruhatUnitTranslate π f) := by
  have hT : IsLinearMap ℂ (fun f : ℬ(Fᵥ(v)) ↦ schwartzBruhatUnitTranslate π f) := by
    refine ⟨fun f g ↦ ?_, fun c f ↦ ?_⟩
    · exact Subtype.ext (funext fun x ↦ rfl)
    · exact Subtype.ext (funext fun x ↦ rfl)
  exact (LinearMap.id - hT.mk' _).isLinear

/-- Paper: Lemma 5.3.1.1, p. 240.
The local difference subtracts pullback by multiplication by the inverse of the chosen unit
in the local field. The lemma applies this definition to uniformizers. -/
def finitePlaceDifference (v : V) (π : Fᵥ(v)ˣ) : ℬ(Fᵥ(v)) →ₗ[ℂ] ℬ(Fᵥ(v)) :=
  (finitePlaceDifference_isLinear v π).mk' _

/-- Paper: Lemma 5.3.1.1, p. 240.
The difference of the integer-ring indicator at a uniformizer is the integer-unit indicator.
Deviation: The integer-ring indicator is represented by the trivial standard Gaussian of §3.4. -/
theorem finitePlaceDifference_integerIndicator (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) (x : Fᵥ(v)) :
    finitePlaceDifference v π (finiteStandardGaussian v 1) (Multiplicative.ofAdd x) =
      (Units.val '' (Uᵥ(v) : Set Fᵥ(v)ˣ)).indicator (fun _ ↦ (1 : ℂ)) x := by
  classical
  have hG (y : Fᵥ(v)) : finiteStandardGaussian v 1 (Multiplicative.ofAdd y) =
      (v.adicCompletionIntegers F : Set Fᵥ(v)).indicator (fun _ ↦ (1 : ℂ)) y := by
    change finiteStandardGaussianValue v 1 y = _
    unfold finiteStandardGaussianValue
    exact ite_eq_left fun u _ ↦ rfl
  have hval : vval(v) π.val = WithZero.exp (-1 : ℤ) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective F)))
  have hmem (y : Fᵥ(v)) : y ∈ Units.val '' (Uᵥ(v) : Set Fᵥ(v)ˣ) ↔ vval(v) y = 1 := by
    refine ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨u, hu, rfl⟩
      exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hu
    · have hy0 : y ≠ 0 := fun h0 ↦ by simp [h0] at hy
      exact ⟨Units.mk0 y hy0,
        HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hy, rfl⟩
  have hπx : vval(v) ((↑π⁻¹ : Fᵥ(v)) * x) = WithZero.exp (1 : ℤ) * vval(v) x := by
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, hval, ← WithZero.exp_neg, neg_neg]
  change finiteStandardGaussian v 1 (Multiplicative.ofAdd x) -
    finiteStandardGaussian v 1 (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x)) = _
  rw [hG, hG]
  rcases lt_trichotomy (vval(v) x) 1 with h | h | h
  · have h1 : vval(v) ((↑π⁻¹ : Fᵥ(v)) * x) ≤ 1 := by
      have h2 := (WithZero.lt_mul_exp_iff_le (x := vval(v) x * WithZero.exp (1 : ℤ)) (y := 1)
        one_ne_zero).mp
      rw [one_mul] at h2
      rw [hπx, mul_comm]
      exact h2 (mul_lt_mul_of_pos_right h (by simp))
    rw [indicator_of_mem (show x ∈ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h.le),
      indicator_of_mem (show _ ∈ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h1),
      indicator_of_notMem fun hx ↦ h.ne ((hmem x).mp hx), sub_self]
  · have h1 : ¬ vval(v) ((↑π⁻¹ : Fᵥ(v)) * x) ≤ 1 := by
      rw [hπx, h, mul_one]
      simp
    rw [indicator_of_mem (show x ∈ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h.le),
      indicator_of_notMem (show _ ∉ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h1),
      indicator_of_mem ((hmem x).mpr h), sub_zero]
  · have h1 : ¬ vval(v) ((↑π⁻¹ : Fᵥ(v)) * x) ≤ 1 := by
      rw [hπx, not_le]
      exact h.trans_le (le_mul_of_one_le_left zero_le (by simp))
    rw [indicator_of_notMem (show x ∉ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h.not_ge),
      indicator_of_notMem (show _ ∉ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h1),
      indicator_of_notMem fun hx ↦ h.ne' ((hmem x).mp hx), sub_zero]

/-- Paper: Lemma 5.3.1.1, p. 240.
For each fixed uniformizer the local difference is a topological embedding. -/
theorem finitePlaceDifference_isEmbedding (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) :
    IsEmbedding (finitePlaceDifference v π) := by sorry

/-- Paper: Lemma 5.3.1.1, pp. 240–241.
The range of the difference for a fixed uniformizer is closed on the full test space. -/
theorem finitePlaceDifference_isClosed_range (v : V) (π : Fᵥ(v)ˣ)
    (_hπ : vval(v).IsUniformizer π.val) :
    IsClosed (Set.range (finitePlaceDifference v π)) := by sorry

-- TODO(paper-gap): ERRATA R7 gives the failure of independence and range on the whole space.

/-- Paper: Lemma 5.3.1.1, p. 240.
The local difference on integer-unit-invariant functions is independent of the uniformizer.
Deviation: The independence claim is restricted to integer-unit invariants by ERRATA R7. -/
theorem finitePlaceDifference_eq_of_unitInvariant (v : V) (π π' : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) (hπ' : vval(v).IsUniformizer π'.val) (f : ℬ(Fᵥ(v)))
    (hf : ∀ u ∈ Uᵥ(v), schwartzBruhatUnitTranslate u f = f) :
    finitePlaceDifference v π f = finitePlaceDifference v π' f := by
  have hu : π * π'⁻¹ ∈ Uᵥ(v) :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr (by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hπ.val, ← hπ'.val]
      exact mul_inv_cancel₀ hπ'.val_ne_zero)
  refine Subtype.ext (funext fun x ↦ ?_)
  have h : f (Multiplicative.ofAdd ((↑(π * π'⁻¹)⁻¹ : Fᵥ(v)) * ((↑π'⁻¹ : Fᵥ(v)) * x.toAdd))) =
      f (Multiplicative.ofAdd ((↑π'⁻¹ : Fᵥ(v)) * x.toAdd)) :=
    congrArg (fun k : ℬ(Fᵥ(v)) ↦ k (Multiplicative.ofAdd ((↑π'⁻¹ : Fᵥ(v)) * x.toAdd))) (hf _ hu)
  rw [← mul_assoc, ← Units.val_mul, show (π * π'⁻¹)⁻¹ * π'⁻¹ = π⁻¹ by
    rw [mul_inv_rev, inv_inv, mul_right_comm, mul_inv_cancel, one_mul]] at h
  exact congrArg (fun a ↦ f x - a) h

/-- Paper: Lemma 5.3.1.1, p. 240.
The image of the integer-unit-invariant subspace under the local difference consists of the
integer-unit-invariant functions vanishing at zero.
Deviation: The domain and the evaluation kernel are restricted by ERRATA R7. -/
theorem finitePlaceDifference_range_on_unitInvariants (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) :
    finitePlaceDifference v π '' {f | ∀ u ∈ Uᵥ(v), schwartzBruhatUnitTranslate u f = f} =
      {f | (∀ u ∈ Uᵥ(v), schwartzBruhatUnitTranslate u f = f) ∧
        f (Multiplicative.ofAdd 0) = 0} := by sorry

-- TODO(paper-gap): At the trivial quasi-character, the eigendistribution in (5.3.1.3)
-- is a multiple of Dirac evaluation and vanishes on the integer-unit indicator.
-- For a nontrivial unramified character the unit-shell and integer-ring
-- normalizations differ by the following factor.

/-- Paper: (5.3.1.3), p. 240.
An eigendistribution normalized on the integer ring as in §3.4 takes the value
one minus the weight of the uniformizer on the unit shell.
Deviation: The shell normalization requires dividing by this factor when it is nonzero. -/
theorem finiteEigendistribution_unitShell (v : V) (π : Fᵥ(v)ˣ)
    (_hπ : vval(v).IsUniformizer π.val) (c : QuasiCharacter Fᵥ(v)ˣ)
    (T : StrongDual ℂ ℬ(Fᵥ(v))) (hT : T ∈ schwartzBruhatEigendistributions (R := Fᵥ(v)) c)
    (hnorm : T (finiteStandardGaussian v 1) = 1) :
    T (finitePlaceDifference v π (finiteStandardGaussian v 1)) = 1 - c π := by
  let f : ℬ(Fᵥ(v)) := finiteStandardGaussian v 1
  change T (f - schwartzBruhatUnitTranslate π f) = 1 - c π
  have heigen : ∀ (g : Fᵥ(v)ˣ) (h : ℬ(Fᵥ(v))),
      T (schwartzBruhatUnitTranslate g h) = c g * T h := hT
  calc
    _ = T f - T (schwartzBruhatUnitTranslate π f) := map_sub T _ _
    _ = T f - c π * T f := congrArg (fun a ↦ T f - a) (heigen π f)
    _ = 1 - c π := by rw [show T f = 1 from hnorm, mul_one]

local instance instMeasurableSpaceAdicUnitsSec3a (v : V) : MeasurableSpace Fᵥ(v)ˣ :=
  borel _

local notation "μᵥ(" v ")" => finiteLocalMultiplicativeTamagawaMeasure F v

/-- Paper: Definition 5.3.1.2 and Lemma 5.3.1.3, p. 241.
Weil's local principal value subtracts the uniformizer translate of the normalized
integer-unit average. -/
def finitePlacePrincipalValueFun (v : V) (π : Fᵥ(v)ˣ) (f : ℬ(Fᵥ(v)))
    (x : Multiplicative Fᵥ(v)) : ℂ :=
  f x - (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹ *
    ∫ u in Uᵥ(v), f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * x.toAdd)))
      ∂μᵥ(v)

/-- Paper: Lemma 5.3.1.3, p. 241.
The local Haar mass on integer units is positive and finite, and the scalar orbit integrals
defining the principal value exist. -/
theorem finitePlacePrincipalValue_integrable (v : V) (π : Fᵥ(v)ˣ) (f : ℬ(Fᵥ(v)))
    (x : Multiplicative Fᵥ(v)) :
    0 < μᵥ(v).real Uᵥ(v) ∧
      IntegrableOn
        (fun u : Fᵥ(v)ˣ ↦
          f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * x.toAdd))))
        Uᵥ(v) μᵥ(v) := by
  have : BorelSpace Fᵥ(v)ˣ := ⟨rfl⟩
  have : (μᵥ(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  have hO : IsOpen (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hK : IsCompact (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr
      (compactSpace_adicCompletionIntegers v))
  refine ⟨ENNReal.toReal_pos (hO.measure_pos _ ⟨1, Uᵥ(v).one_mem⟩).ne' hK.measure_lt_top.ne, ?_⟩
  refine ContinuousOn.integrableOn_compact hK (Continuous.continuousOn ?_)
  exact (schwartzBruhat_continuous f).comp (continuous_ofAdd.comp
    ((Units.continuous_val.comp continuous_inv).mul continuous_const))

/-- The unit average of a locally constant compactly supported function, after scaling by a
fixed unit, is again locally constant with compact support. -/
private theorem finitePlacePrincipalValue_mem_average {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [MeasurableSpace Kˣ] [OpensMeasurableSpace Kˣ]
    (μ : Measure Kˣ) (U : Set Kˣ) (hO : IsOpen U) (hK : IsCompact U) (c : Kˣ) (F0 : K → ℂ)
    (hlc : IsLocallyConstant F0) (hcs : HasCompactSupport F0) :
    IsLocallyConstant (fun y : K ↦ ∫ u in U, F0 ((↑u⁻¹ : K) * ((↑c⁻¹ : K) * y)) ∂μ) ∧
      HasCompactSupport (fun y : K ↦ ∫ u in U, F0 ((↑u⁻¹ : K) * ((↑c⁻¹ : K) * y)) ∂μ) := by
  have hinv : Continuous fun u : Kˣ ↦ (↑u⁻¹ : K) := Units.continuous_val.comp continuous_inv
  refine ⟨(IsLocallyConstant.iff_exists_open _).mpr fun x ↦ ?_, ?_⟩
  · have hΦ : IsLocallyConstant fun p : K × Kˣ ↦
        (F0 ((↑p.2⁻¹ : K) * ((↑c⁻¹ : K) * p.1)), F0 ((↑p.2⁻¹ : K) * ((↑c⁻¹ : K) * x))) :=
      (hlc.comp_continuous ((hinv.comp continuous_snd).mul
        (continuous_const.mul continuous_fst))).prodMk
        (hlc.comp_continuous ((hinv.comp continuous_snd).mul continuous_const))
    obtain ⟨A, B, hA, -, hxA, hUB, hAB⟩ := generalized_tube_lemma isCompact_singleton hK
      (hΦ {q | q.1 = q.2}) (fun p hp ↦ by
        obtain ⟨hp1, -⟩ := hp
        change F0 _ = F0 _
        rw [Set.mem_singleton_iff.mp hp1])
    exact ⟨A, hA, hxA rfl, fun x' hx' ↦
      setIntegral_congr_fun hO.measurableSet fun u hu ↦
        hAB (show ((x', u) : K × Kˣ) ∈ A ×ˢ B from ⟨hx', hUB hu⟩)⟩
  · refine HasCompactSupport.intro
      ((hK.prod hcs.isCompact).image (f := fun p : Kˣ × K ↦ (↑c : K) * ((↑p.1 : K) * p.2))
        (continuous_const.mul ((Units.continuous_val.comp continuous_fst).mul continuous_snd)))
      fun x hx ↦ setIntegral_eq_zero_of_forall_eq_zero fun u hu ↦ ?_
    by_contra hne
    refine hx ⟨(u, (↑u⁻¹ : K) * ((↑c⁻¹ : K) * x)), ⟨hu, subset_tsupport _ hne⟩, ?_⟩
    change (↑c : K) * ((↑u : K) * ((↑u⁻¹ : K) * ((↑c⁻¹ : K) * x))) = x
    rw [Units.mul_inv_cancel_left, Units.mul_inv_cancel_left]

/-- Paper: Lemma 5.3.1.3, p. 241.
The formula for the local principal value produces a Schwartz–Bruhat test function. -/
theorem finitePlacePrincipalValue_mem (v : V) (π : Fᵥ(v)ˣ) (f : ℬ(Fᵥ(v))) :
    finitePlacePrincipalValueFun v π f ∈ schwartzBruhatSubmodule (Multiplicative Fᵥ(v)) :=
  by
  have hlc := (mem_finitePlaceSchwartz_iff F v (fun y ↦ f (Multiplicative.ofAdd y))).mp
    ⟨f, fun _ ↦ rfl⟩
  have : BorelSpace Fᵥ(v)ˣ := ⟨rfl⟩
  have hO : IsOpen (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hK : IsCompact (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr
      (compactSpace_adicCompletionIntegers v))
  have h := finitePlacePrincipalValue_mem_average μᵥ(v) _ hO hK π _ hlc.1 hlc.2
  obtain ⟨g, hg⟩ := (mem_finitePlaceSchwartz_iff F v _).mpr h
  have heq : finitePlacePrincipalValueFun v π f =
      (f : Multiplicative Fᵥ(v) → ℂ) -
        (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹ • (g : Multiplicative Fᵥ(v) → ℂ) :=
    funext fun x ↦ by
      change _ = f x - (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹ * g (Multiplicative.ofAdd x.toAdd)
      rw [hg]
      rfl
  rw [heq]
  exact Submodule.sub_mem _ (show schwartzBruhatSubmodule _ from f).property
    (Submodule.smul_mem _ _ (show schwartzBruhatSubmodule _ from g).property)

local notation "pvBundle(" v ", " π ")" =>
  (fun f : ℬ(Fᵥ(v)) ↦
    (⟨finitePlacePrincipalValueFun v π f, finitePlacePrincipalValue_mem v π f⟩ : ℬ(Fᵥ(v))))

/-- Paper: Lemma 5.3.1.3, p. 241.
The bundled local averaging formula is linear. -/
theorem finitePlacePrincipalValue_isLinear (v : V) (π : Fᵥ(v)ˣ) :
    IsLinearMap ℂ (pvBundle(v, π)) := by
  refine ⟨fun f g ↦ ?_, fun c f ↦ ?_⟩
  · refine Subtype.ext (funext fun x ↦ ?_)
    have hf := (finitePlacePrincipalValue_integrable v π f x).2
    have hg := (finitePlacePrincipalValue_integrable v π g x).2
    change finitePlacePrincipalValueFun v π (f + g) x =
      finitePlacePrincipalValueFun v π f x + finitePlacePrincipalValueFun v π g x
    unfold finitePlacePrincipalValueFun
    simp only [show ∀ y, (f + g) y = f y + g y from fun _ ↦ rfl]
    rw [integral_add hf hg]
    ring
  · refine Subtype.ext (funext fun x ↦ ?_)
    change finitePlacePrincipalValueFun v π (c • f) x = c * finitePlacePrincipalValueFun v π f x
    unfold finitePlacePrincipalValueFun
    simp only [show ∀ y, (c • f) y = c * f y from fun _ ↦ rfl]
    rw [integral_const_mul]
    ring

/-- Paper: Lemma 5.3.1.3, p. 241.
The local principal value formula is continuous. -/
theorem finitePlacePrincipalValue_continuous (v : V) (π : Fᵥ(v)ˣ) :
    @Continuous ℬ(Fᵥ(v)) ℬ(Fᵥ(v)) _ _
      ((finitePlacePrincipalValue_isLinear v π).mk' (pvBundle(v, π))).toFun := by
  let E := FinestLocallyConvex ℬ(Fᵥ(v))
  let L : E →ₗ[ℂ] E := (finitePlacePrincipalValue_isLinear v π).mk' (pvBundle(v, π))
  apply (congrArg (fun t ↦ @Continuous ℬ(Fᵥ(v)) ℬ(Fᵥ(v)) t t L.toFun)
    (finitePlaceSchwartz_finestTopology F v)).mpr
  have h := finestLocallyConvex_withSeminorms ℬ(Fᵥ(v))
  haveI : IsTopologicalAddGroup E := h.isTopologicalAddGroup
  exact h.continuous_of_continuous_comp L fun p ↦ h.continuous_seminorm (p.comp L)

/-- Paper: Definition 5.3.1.2, p. 241.
The principal value is the identity minus the uniformizer pullback of the trivial-isotype
projection. A uniformizer is chosen from the discrete local valuation. -/
def finitePlacePrincipalValue (v : V) : ℬ(Fᵥ(v)) →L[ℂ] ℬ(Fᵥ(v)) :=
  let h := vval(v).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (h.choose : Fᵥ(v)) h.choose_spec.ne_zero
  ⟨(finitePlacePrincipalValue_isLinear v π).mk' (pvBundle(v, π)),
    finitePlacePrincipalValue_continuous v π⟩

/-- A left-invariant set integral is unchanged by left translation by an element that
preserves the set. -/
private theorem finitePlacePrincipalValue_spec_setIntegral_mul_left {G : Type*} [Group G]
    [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] (S : Set G)
    (hS : MeasurableSet S) (g : G → ℂ) (w : G) (hw : ∀ u, w * u ∈ S ↔ u ∈ S) :
    ∫ u in S, g (w * u) ∂μ = ∫ u in S, g u ∂μ := by
  rw [← integral_indicator hS, ← integral_indicator hS,
    ← integral_mul_left_eq_self (S.indicator g) w]
  congr 1
  funext u
  by_cases hu : u ∈ S
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem ((hw u).mpr hu)]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (fun h ↦ hu ((hw u).mp h))]

/-- The scalar principal-value formula does not depend on the choice of uniformizer, by left
invariance of the multiplicative Haar measure on the integer units. -/
private theorem finitePlacePrincipalValue_spec_indep (v : V) (π π' : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) (hπ' : vval(v).IsUniformizer π'.val) (f : ℬ(Fᵥ(v)))
    (x : Multiplicative Fᵥ(v)) :
    finitePlacePrincipalValueFun v π f x = finitePlacePrincipalValueFun v π' f x := by
  have : BorelSpace Fᵥ(v)ˣ := ⟨rfl⟩
  have : μᵥ(v).IsMulLeftInvariant := by
    unfold finiteLocalMultiplicativeTamagawaMeasure
    infer_instance
  have hu : π * π'⁻¹ ∈ Uᵥ(v) :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr (by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hπ.val, ← hπ'.val]
      exact mul_inv_cancel₀ hπ'.val_ne_zero)
  have hw : π'⁻¹ * π ∈ Uᵥ(v) := mul_comm π π'⁻¹ ▸ hu
  have hU : MeasurableSet (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  unfold finitePlacePrincipalValueFun
  congr 2
  refine Eq.trans ?_ (finitePlacePrincipalValue_spec_setIntegral_mul_left μᵥ(v) _ hU
    (fun u : Fᵥ(v)ˣ ↦ f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * ((↑π'⁻¹ : Fᵥ(v)) * x.toAdd))))
    (π'⁻¹ * π) (fun u ↦ Subgroup.mul_mem_cancel_left _ hw))
  congr 1
  funext u
  rw [← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul]
  group

/-- Paper: Definition 5.3.1.2 and Lemma 5.3.1.3, p. 241.
The scalar formula for the operator works with every choice of uniformizer. -/
theorem finitePlacePrincipalValue_spec (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) :
    ∀ (f : ℬ(Fᵥ(v))) (x : Multiplicative Fᵥ(v)),
      finitePlacePrincipalValue v f x = finitePlacePrincipalValueFun v π f x := by
  intro f x
  let h := vval(v).exists_isUniformizer_of_isCyclic_of_nontrivial
  exact finitePlacePrincipalValue_spec_indep v (Units.mk0 (h.choose : Fᵥ(v))
    h.choose_spec.ne_zero) π h.choose_spec hπ f x

open Classical in
/-- Paper: Definition 5.3.1.2 and Lemma 5.3.1.3, p. 241.
Weil's operator is uniquely specified by acting as the local difference on the trivial isotype
and as the identity on every nontrivial integer-unit isotype. Both formulas preserve the
corresponding isotype. -/
theorem finitePlacePrincipalValue_unique (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) :
    let obeys := fun P : ℬ(Fᵥ(v)) →L[ℂ] ℬ(Fᵥ(v)) ↦
      ∀ (χ : PontryaginDual Uᵥ(v)) (f : ℬ(Fᵥ(v))),
        (∀ u : Uᵥ(v), schwartzBruhatUnitTranslate u.val f = (χ u : ℂ) • f) →
        P f = if χ = 1 then finitePlaceDifference v π f else f
    obeys (finitePlacePrincipalValue v) ∧
      ∀ P, obeys P → P = finitePlacePrincipalValue v := by sorry

/-- Paper: Lemma 5.3.1.3, p. 241.
Weil's local principal value is a topological embedding with closed range. -/
theorem finitePlacePrincipalValue_isClosedEmbedding (v : V) :
    IsClosedEmbedding (finitePlacePrincipalValue v) := by sorry

private theorem finitePlacePrincipalValue_range_integral {G : Type*} [CommGroup G]
    [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (K : Subgroup G) (a : G) (ha : a ∈ K) (f : G → ℂ) :
    ∫ x in K, f (a * x) ∂μ = ∫ x in K, f x ∂μ := by
  have he : (fun x : G ↦ a * x) ⁻¹' (K : Set G) = K := by
    ext x
    simp only [mem_preimage]
    constructor
    · intro h
      have := K.mul_mem (K.inv_mem ha) h
      simpa using this
    · exact K.mul_mem ha
  have hp := (measurePreserving_mul_left μ a).setIntegral_preimage_emb
    (MeasurableEquiv.mulLeft a).measurableEmbedding f (K : Set G)
  rw [he] at hp
  exact hp

private theorem finitePlacePrincipalValue_range_zero (v : V) (f : ℬ(Fᵥ(v))) :
    finitePlacePrincipalValue v f (Multiplicative.ofAdd 0) = 0 := by
  let h := (Valued.v : Valuation Fᵥ(v) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (h.choose : Fᵥ(v)) h.choose_spec.ne_zero
  rw [finitePlacePrincipalValue_spec v π h.choose_spec]
  unfold finitePlacePrincipalValueFun
  simp only [show (Multiplicative.ofAdd (0 : Fᵥ(v))).toAdd = 0 from rfl, mul_zero,
    setIntegral_const, Complex.real_smul]
  have hm : (μᵥ(v).real Uᵥ(v) : ℂ) ≠ 0 := by
    exact_mod_cast (finitePlacePrincipalValue_integrable v π f (Multiplicative.ofAdd 0)).1.ne'
  field_simp
  ring

private theorem finitePlacePrincipalValue_range_invariant (v : V) (f : ℬ(Fᵥ(v))) :
    ∀ u ∈ Uᵥ(v), schwartzBruhatUnitTranslate u (f - finitePlacePrincipalValue v f) =
      f - finitePlacePrincipalValue v f := by
  intro u hu
  let h := (Valued.v : Valuation Fᵥ(v) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (h.choose : Fᵥ(v)) h.choose_spec.ne_zero
  letI : BorelSpace Fᵥ(v)ˣ := ⟨rfl⟩
  let : (μᵥ(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  apply Subtype.ext
  funext x
  change (f - finitePlacePrincipalValue v f) (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * x.toAdd)) = _
  change f _ - finitePlacePrincipalValue v f _ = f x - finitePlacePrincipalValue v f x
  have hp1 := finitePlacePrincipalValue_spec v π h.choose_spec f
    (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * x.toAdd))
  have hp2 := finitePlacePrincipalValue_spec v π h.choose_spec f x
  apply (congrArg₂ (fun a b : ℂ ↦
    f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * x.toAdd)) - a = f x - b) hp1 hp2).mpr
  unfold finitePlacePrincipalValueFun
  have hi := finitePlacePrincipalValue_range_integral (μᵥ(v)) Uᵥ(v) u hu
    (fun a : Fᵥ(v)ˣ ↦ f (Multiplicative.ofAdd ((↑a⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * x.toAdd))))
  have hi' : (∫ a : Fᵥ(v)ˣ in Uᵥ(v),
      f (Multiplicative.ofAdd ((↑a⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * ((↑u⁻¹ : Fᵥ(v)) * x.toAdd)))) ∂μᵥ(v)) =
      ∫ a : Fᵥ(v)ˣ in Uᵥ(v), f (Multiplicative.ofAdd ((↑a⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * x.toAdd))) ∂μᵥ(v) := by
    convert hi using 1
    congr 1
    funext a
    simp only [mul_inv_rev, Units.val_mul]
    ring
  change _ - (_ - (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹ *
      (∫ a : Fᵥ(v)ˣ in Uᵥ(v), f (Multiplicative.ofAdd ((↑a⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * ((↑u⁻¹ : Fᵥ(v)) * x.toAdd)))) ∂μᵥ(v))) = _
  rw [hi']
  ring

/-- Paper: Lemmas 5.3.1.1 and 5.3.1.3, pp. 240–241.
Weil's operator maps onto all tests vanishing at zero.
Deviation: The full evaluation kernel belongs to the averaged operator from (5.3.1.5). -/
theorem finitePlacePrincipalValue_range (v : V) :
    Set.range (finitePlacePrincipalValue v) =
      {f : ℬ(Fᵥ(v)) | f (Multiplicative.ofAdd 0) = 0} := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact finitePlacePrincipalValue_range_zero v g
  · intro hf
    let h := (Valued.v : Valuation Fᵥ(v) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
    let π := Units.mk0 (h.choose : Fᵥ(v)) h.choose_spec.ne_zero
    have hb : (f - finitePlacePrincipalValue v f) ∈
        {f | (∀ u ∈ Uᵥ(v), schwartzBruhatUnitTranslate u f = f) ∧ f (Multiplicative.ofAdd 0) = 0} := by
      refine ⟨finitePlacePrincipalValue_range_invariant v f, ?_⟩
      change f (Multiplicative.ofAdd 0) - finitePlacePrincipalValue v f (Multiplicative.ofAdd 0) = 0
      exact sub_eq_zero.mpr (hf.trans (finitePlacePrincipalValue_range_zero v f).symm)
    have hb' := (Set.ext_iff.mp (finitePlaceDifference_range_on_unitInvariants v π h.choose_spec)
      (f - finitePlacePrincipalValue v f)).mpr hb
    obtain ⟨g, hg, hge⟩ := hb'
    have hP : finitePlacePrincipalValue v g = finitePlaceDifference v π g := by
      have huniq := (finitePlacePrincipalValue_unique v π h.choose_spec).1 1 g
      have hh : ∀ u : Uᵥ(v), schwartzBruhatUnitTranslate u.val g = ((1 : PontryaginDual Uᵥ(v)) u : ℂ) • g := by
        intro u
        simpa using hg u.val u.property
      simpa only [if_pos rfl, ite_true] using huniq hh
    refine ⟨f + g, ?_⟩
    calc
      finitePlacePrincipalValue v (f + g) = finitePlacePrincipalValue v f + finitePlacePrincipalValue v g := map_add _ _ _
      _ = finitePlacePrincipalValue v f + (f - finitePlacePrincipalValue v f) := congrArg (finitePlacePrincipalValue v f + ·) (hP.trans hge)
      _ = f := by abel

end FinitePlace

section AdelicPrincipalValue

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "ℬₛ(" S ")" => ℬ(SAdeleRing F S)
local notation "Θₛ(" S ")" => SLocalAdelicThetaSpace F S
local notation "Θ𝔽" => GlobalAdelicThetaSpace F
local notation "Kₛ(" S ")" => LinearMap.ker (sLocalAdelicTheta F S)
local notation "K𝔽" => LinearMap.ker (adelicThetaLinearMap F)

open Classical in
variable (F) in
/-- Paper: Definition 5.3.1.4(1), p. 242.
The S-local principal value applies the local operators in the selected finite factors.
Deviation: The tensor decomposition is the one from the Lean version of Proposition 2.1.4.1. -/
def sAdelePrincipalValue {S S₀ : Finset V} (_h₀ : S₀ ⊆ S) : ℬₛ(S) →ₗ[ℂ] ℬₛ(S) :=
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  let W := FinestLocallyConvex (⨂[ℂ] w : S, ℬ(w.val.adicCompletion F))
  let P : W →ₗ[ℂ] W := PiTensorProduct.map (R := ℂ) fun w : S ↦
    if w.val ∈ S₀ then (finitePlacePrincipalValue w.val).toLinearMap else LinearMap.id
  let idArch : ℬ(InfiniteAdeleRing F) →ₗ[ℂ] ℬ(InfiniteAdeleRing F) := LinearMap.id
  e.toLinearMap.comp ((TensorProduct.map idArch P).comp e.symm.toLinearMap)

variable (F) in
/-- Paper: Definition 5.3.1.4(2), p. 242.
The global principal value acts in the S₀-local factor and leaves the complementary factor
unchanged. -/
def adelePrincipalValue (S₀ : Finset V) : ℬ(𝔸[F]) →ₗ[ℂ] ℬ(𝔸[F]) :=
  let e := (sAdeleTailSchwartz_inductiveTensor_equiv F S₀).choose
  let idTail : ℬ(FiniteAdeleTail F S₀) →ₗ[ℂ] ℬ(FiniteAdeleTail F S₀) := LinearMap.id
  e.toLinearMap.comp
    ((TensorProduct.map (sAdelePrincipalValue F (Finset.Subset.refl S₀)) idTail).comp
      e.symm.toLinearMap)

private theorem sAdelePrincipalValue_tmul_aux {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] {ι : Type*} {D : ι → Type*}
    [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)] [∀ i, TopologicalSpace (D i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, D i)) ≃L[ℂ] B)
    (p : ι → Prop) [DecidablePred p] (T : ∀ i, D i →L[ℂ] D i) (f : A) (g : ∀ i, D i) :
    let W := FinestLocallyConvex (⨂[ℂ] i, D i)
    let P : W →ₗ[ℂ] W := PiTensorProduct.map fun i ↦
      if p i then (T i).toLinearMap else LinearMap.id
    let I : A →ₗ[ℂ] A := LinearMap.id
    (e.toLinearMap.comp ((TensorProduct.map I P).comp e.symm.toLinearMap))
      (e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i))) = e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, if p i then T i (g i) else g i)) := by
  intro W P I
  change e (TensorProduct.map I P (e.symm (e _))) = e _
  erw [e.symm_apply_apply, TensorProduct.map_tmul]
  apply congrArg e
  apply congrArg (TensorProduct.tmul ℂ f)
  exact (PiTensorProduct.map_tprod _ g).trans (congrArg (PiTensorProduct.tprod ℂ)
    (funext fun i ↦ DFunLike.ite_apply (P := p i) (T i).toLinearMap LinearMap.id (g i)))

open Classical in
/-- Paper: Definition 5.3.1.4(1), p. 242.
On pure tensors the S-local operator acts by the local principal value in each selected factor. -/
theorem sAdelePrincipalValue_tmul {S S₀ : Finset V} (h₀ : S₀ ⊆ S)
    (f : ℬ(InfiniteAdeleRing F)) (g : ∀ w : S, ℬ(w.val.adicCompletion F)) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    sAdelePrincipalValue F h₀ (e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) =
      e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, if w.val ∈ S₀ then finitePlacePrincipalValue w.val (g w) else g w)) := by
  intro e
  unfold sAdelePrincipalValue
  with_reducible
    exact sAdelePrincipalValue_tmul_aux e (fun w : S ↦ w.val ∈ S₀)
      (fun w ↦ finitePlacePrincipalValue w.val) f g

/-- Paper: Definition 5.3.1.4(2), p. 242.
Through any stage containing S₀ the global operator acts as the S-local operator on the stage
factor and as the identity on the tail. -/
theorem adelePrincipalValue_tmul {S S₀ : Finset V} (h₀ : S₀ ⊆ S)
    (f : ℬₛ(S)) (g : ℬ(FiniteAdeleTail F S)) :
    let e := (sAdeleTailSchwartz_inductiveTensor_equiv F S).choose
    adelePrincipalValue F S₀ (e (f ⊗ₜ[ℂ] g)) = e (sAdelePrincipalValue F h₀ f ⊗ₜ[ℂ] g) :=
  by sorry

/-- Paper: Definition 5.3.1.4(1), p. 242.
The S-local principal value is a topological embedding with closed range. -/
theorem sAdelePrincipalValue_isClosedEmbedding {S S₀ : Finset V} (h₀ : S₀ ⊆ S) :
    IsClosedEmbedding (sAdelePrincipalValue F h₀) := by sorry

/-- Paper: Definition 5.3.1.4(2), p. 242.
The global principal value is a topological embedding with closed range. -/
theorem adelePrincipalValue_isClosedEmbedding (S₀ : Finset V) :
    IsClosedEmbedding (adelePrincipalValue F S₀) := by sorry

/-- Paper: (5.3.1.9), p. 242.
The S-local principal value preserves the kernel of theta averaging. -/
theorem sAdelePrincipalValue_preserves_thetaKernel {S S₀ : Finset V} (h₀ : S₀ ⊆ S) :
    Kₛ(S) ≤ (Kₛ(S)).comap (sAdelePrincipalValue F h₀) := by sorry

/-- Paper: (5.3.1.10), p. 242.
The global principal value preserves the kernel of theta averaging. -/
theorem adelePrincipalValue_preserves_thetaKernel (S₀ : Finset V) :
    K𝔽 ≤ (K𝔽).comap (adelePrincipalValue F S₀) := by sorry

variable (F) in
/-- Paper: (5.3.1.9), p. 242.
The S-local principal value acts on the S-local theta quotient by descent. -/
def sLocalThetaPrincipalValue {S S₀ : Finset V} (h₀ : S₀ ⊆ S) : Θₛ(S) →ₗ[ℂ] Θₛ(S) :=
  (Kₛ(S)).mapQ (Kₛ(S)) (sAdelePrincipalValue F h₀)
    (sAdelePrincipalValue_preserves_thetaKernel h₀)

variable (F) in
/-- Paper: (5.3.1.10), p. 242.
The global principal value acts on the global theta quotient by descent. -/
def globalThetaPrincipalValue (S₀ : Finset V) : Θ𝔽 →ₗ[ℂ] Θ𝔽 :=
  (K𝔽).mapQ K𝔽 (adelePrincipalValue F S₀) (adelePrincipalValue_preserves_thetaKernel S₀)

/-- Paper: (5.3.1.9), p. 242.
On a class represented by a test function the S-local operator gives the class of its image. -/
theorem sLocalThetaPrincipalValue_mk {S S₀ : Finset V} (h₀ : S₀ ⊆ S) (f : ℬₛ(S)) :
    sLocalThetaPrincipalValue F h₀ (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sAdelePrincipalValue F h₀ f) := by
  rfl

/-- Paper: (5.3.1.10), p. 242.
On a class represented by a test function the global operator gives the class of its image. -/
theorem globalThetaPrincipalValue_mk (S₀ : Finset V) (f : ℬ(𝔸[F])) :
    globalThetaPrincipalValue F S₀ (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (adelePrincipalValue F S₀ f) := by
  rfl

/-- Paper: (5.3.1.9), p. 242.
The S-local operator descends continuously for every set of selected places. -/
theorem sLocalThetaPrincipalValue_continuous {S S₀ : Finset V} (h₀ : S₀ ⊆ S) :
    Continuous (sLocalThetaPrincipalValue F h₀) := by
  apply (Kₛ(S)).isQuotientMap_mkQ.continuous_iff.mpr
  exact (Kₛ(S)).isQuotientMap_mkQ.continuous.comp
    (sAdelePrincipalValue_isClosedEmbedding h₀).continuous

/-- Paper: (5.3.1.10), p. 242.
The global operator descends continuously for every set of selected places. -/
theorem globalThetaPrincipalValue_continuous (S₀ : Finset V) :
    Continuous (globalThetaPrincipalValue F S₀) := by
  apply (K𝔽).isQuotientMap_mkQ.continuous_iff.mpr
  exact (K𝔽).isQuotientMap_mkQ.continuous.comp
    (adelePrincipalValue_isClosedEmbedding S₀).continuous

-- TODO(paper-gap): Let K be the theta kernel and P the operator on tests.
-- On the quotient the preimage of the range is range P + K. Closedness of
-- range P and injectivity after descent do not establish closedness of this
-- sum or continuity of the inverse on its image. This affects both quotients.

/-- Paper: Lemma 5.3.1.5, p. 242.
The S-local principal value on theta classes is a closed topological embedding. -/
theorem sLocalThetaPrincipalValue_isClosedEmbedding {S S₀ : Finset V} (h₀ : S₀ ⊆ S)
    (hn : S₀.Nonempty) :
    IsClosedEmbedding (sLocalThetaPrincipalValue F h₀) := by sorry

-- TODO(paper-gap): The proof of global closed range claims that the image is contained in
-- any fixed S-stage. This does not follow from stage compatibility and fails at larger stages.

/-- Paper: Lemma 5.3.1.5, p. 242.
The global principal value on theta classes is a closed topological embedding. -/
theorem globalThetaPrincipalValue_isClosedEmbedding {S₀ : Finset V} (hn : S₀.Nonempty) :
    IsClosedEmbedding (globalThetaPrincipalValue F S₀) := by sorry

private theorem sLocalThetaPrincipalValue_transition_ext {ι A X Y : Type*} {M : ι → Type*}
    [TopologicalSpace A] [AddCommGroup A] [Module ℂ A] [TopologicalSpace X]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, M i)) ≃L[ℂ] X)
    (i : X →ₗ[ℂ] Y) (p : X →ₗ[ℂ] X) (q : Y →ₗ[ℂ] Y)
    (h : ∀ (a : A) (g : ∀ i, M i),
      i (p (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)))) = q (i (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))))) :
    i.comp p = q.comp i := by
  apply (LinearMap.cancel_right (g := e.toLinearMap) e.surjective).mp
  apply TensorProduct.ext
  exact LinearMap.ext fun a ↦ LinearMap.ext_on_range PiTensorProduct.span_tprod_eq_top (h a)

private theorem sLocalThetaPrincipalValue_transition_tmul {ι A X : Type*} {M : ι → Type*}
    [TopologicalSpace A] [AddCommGroup A] [Module ℂ A] [TopologicalSpace X]
    [AddCommGroup X] [Module ℂ X] [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, M i)) ≃L[ℂ] X)
    (P : ∀ i, M i →ₗ[ℂ] M i) (a : A) (b : ∀ i, M i) :
    let W := FinestLocallyConvex (⨂[ℂ] i, M i)
    let Q : W →ₗ[ℂ] W := PiTensorProduct.map P
    (e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A)
      Q).comp e.symm.toLinearMap)) (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, b i))) =
        e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, P i (b i))) := by
  change e ((TensorProduct.map _ (PiTensorProduct.map P)) (e.symm (e _))) = _
  erw [e.symm_apply_apply]
  apply congrArg e
  exact (TensorProduct.map_tmul LinearMap.id (PiTensorProduct.map P) a _).trans
    (congrArg (TensorProduct.tmul ℂ a) (PiTensorProduct.map_tprod P b))

open Classical in
private theorem sLocalThetaPrincipalValue_transition_factors {ι : Type*} {M : ι → Type*}
    [∀ v, AddCommGroup (M v)] [∀ v, Module ℂ (M v)]
    {S₀ S T : Finset ι} (h₀ : S₀ ⊆ S) (P : ∀ v, M v →ₗ[ℂ] M v) (c : ∀ v, M v)
    (g : ∀ w : S, M w.val) :
    let extend := fun (b : ∀ w : S, M w.val) (w : T) ↦
      if hw : w.val ∈ S then b ⟨w.val, hw⟩ else c w.val
    let op := fun (R : Finset ι) (b : ∀ w : R, M w.val) (w : R) ↦
      (if w.val ∈ S₀ then P w.val else LinearMap.id) (b w)
    extend (op S g) = op T (extend g) := by
  funext w
  by_cases hw : w.val ∈ S
  · simp [hw]
  · simp [hw, show w.val ∉ S₀ from fun h ↦ hw (h₀ h)]

open Classical in
private theorem sLocalThetaPrincipalValue_transition_tests {S₀ S T : Finset V}
    (h₀ : S₀ ⊆ S) (hST : S ⊆ T) :
    (sAdeleSchwartzTransition F hST).comp (sAdelePrincipalValue F h₀) =
      (sAdelePrincipalValue F (h₀.trans hST)).comp (sAdeleSchwartzTransition F hST) := by
  let e (R : Finset V) := (sAdeleSchwartz_inductiveTensor_equiv F R).choose
  apply sLocalThetaPrincipalValue_transition_ext (e S)
  intro a g
  let pureTest (R : Finset V) (b : ∀ w : R, ℬ(w.val.adicCompletion F)) : ℬₛ(R) :=
    e R (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w))
  let P (v : V) : ℬ(v.adicCompletion F) →ₗ[ℂ] ℬ(v.adicCompletion F) :=
    if v ∈ S₀ then (finitePlacePrincipalValue v).toLinearMap else LinearMap.id
  let op (R : Finset V) (b : ∀ w : R, ℬ(w.val.adicCompletion F)) (w : R) :=
    P w.val (b w)
  have pv (R : Finset V) (hR : S₀ ⊆ R) (b : ∀ w : R, ℬ(w.val.adicCompletion F)) :
      sAdelePrincipalValue F hR (pureTest R b) = pureTest R (op R b) := by
    unfold sAdelePrincipalValue
    with_reducible exact sLocalThetaPrincipalValue_transition_tmul (e R) (fun w : R ↦ P w.val) a b
  let extend (b : ∀ w : S, ℬ(w.val.adicCompletion F)) (w : T) :=
    if hw : w.val ∈ S then b ⟨w.val, hw⟩ else finiteStandardGaussian w.val 1
  have insertTest (b : ∀ w : S, ℬ(w.val.adicCompletion F)) :
      sAdeleSchwartzTransition F hST (pureTest S b) = pureTest T (extend b) := by
    apply Subtype.ext
    funext x
    have hg (w : T) (hw : w.val ∉ S) (y : w.val.adicCompletion F) :
        extend b w (Multiplicative.ofAdd y) =
          (w.val.adicCompletionIntegers F : Set (w.val.adicCompletion F)).indicator
            (fun _ ↦ (1 : ℂ)) y := by
      rw [show extend b w = finiteStandardGaussian w.val 1 by simp [extend, hw]]
      change finiteStandardGaussianValue w.val 1 y = _
      unfold finiteStandardGaussianValue
      exact ite_eq_left fun u _ ↦ rfl
    have hr (w : S) : extend b ⟨w.val, hST w.property⟩ = b w := by
      simp only [extend, dite_eq_left w.property]
    have spec (R : Finset V) (d : ∀ w : R, ℬ(w.val.adicCompletion F)) (y : SAdeleRing F R) :
        pureTest R d (Multiplicative.ofAdd y) = a (Multiplicative.ofAdd y.1) *
          ∏ w : R, d w (Multiplicative.ofAdd (y.2 w)) := by
      with_reducible exact (sAdeleSchwartz_inductiveTensor_equiv F R).choose_spec a d y
    with_reducible refine Eq.trans ?_ (spec T (extend b) x.toAdd).symm
    change sAdeleSchwartzTransition F hST (pureTest S b) (Multiplicative.ofAdd x.toAdd) = _
    with_reducible
      refine sAdeleSchwartzTransition_pure F hST a (extend b) hg (pureTest S b) ?_ x.toAdd
    intro y
    simp only [hr]
    with_reducible exact spec S b y
  with_reducible change sAdeleSchwartzTransition F hST (sAdelePrincipalValue F h₀ (pureTest S g)) =
    sAdelePrincipalValue F (h₀.trans hST) (sAdeleSchwartzTransition F hST (pureTest S g))
  have hcomm : extend (op S g) = op T (extend g) := by
    with_reducible
      exact sLocalThetaPrincipalValue_transition_factors (M := fun v : V ↦ ℬ(v.adicCompletion F))
        (T := T) h₀ (fun v ↦ (finitePlacePrincipalValue v).toLinearMap)
        (fun v ↦ finiteStandardGaussian v 1) g
  with_reducible
    exact (congrArg (sAdeleSchwartzTransition F hST) (pv S h₀ g)).trans
      ((insertTest (op S g)).trans ((congrArg (pureTest T) hcomm).trans
        ((pv T (h₀.trans hST) (extend g)).symm.trans
          (congrArg (sAdelePrincipalValue F (h₀.trans hST)) (insertTest g).symm))))

private theorem sLocalThetaPrincipalValue_transition_mapQ {X Y : Type*} [AddCommGroup X]
    [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (K : Submodule ℂ X) (L : Submodule ℂ Y)
    (i : X →ₗ[ℂ] Y) (p : X →ₗ[ℂ] X) (q : Y →ₗ[ℂ] Y) (hi : K ≤ L.comap i)
    (hp : K ≤ K.comap p) (hq : L ≤ L.comap q) (h : i.comp p = q.comp i) :
    (K.mapQ L i hi).comp (K.mapQ K p hp) = (L.mapQ L q hq).comp (K.mapQ L i hi) := by
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := K.mkQ_surjective x
  exact congrArg L.mkQ (DFunLike.congr_fun h f)

/-- Paper: Lemma 5.3.1.5, p. 242.
The principal value commutes with passage from an S-local theta stage to a larger stage. -/
theorem sLocalThetaPrincipalValue_transition {S₀ S T : Finset V}
    (h₀ : S₀ ⊆ S) (hST : S ⊆ T) (hn : S₀.Nonempty) :
    (sLocalThetaTransition (F := F) hST).comp (sLocalThetaPrincipalValue F h₀) =
      (sLocalThetaPrincipalValue F (h₀.trans hST)).comp (sLocalThetaTransition hST) := by
  unfold sLocalThetaTransition sLocalThetaPrincipalValue
  apply sLocalThetaPrincipalValue_transition_mapQ
  exact sLocalThetaPrincipalValue_transition_tests h₀ hST

/-- Paper: Lemma 5.3.1.5, p. 242.
The local and global principal value operators commute with insertion of an S-local theta stage. -/
theorem sLocalThetaPrincipalValue_toGlobal {S₀ S : Finset V}
    (h₀ : S₀ ⊆ S) (hn : S₀.Nonempty) :
    (sLocalThetaToGlobal F S).comp (sLocalThetaPrincipalValue F h₀) =
      (globalThetaPrincipalValue F S₀).comp (sLocalThetaToGlobal F S) := by sorry

/-- Paper: Lemma 5.3.1.5, p. 242.
The S-local principal value commutes with each S-idele translation on theta classes. -/
theorem sLocalThetaPrincipalValue_equivariant {S₀ S : Finset V}
    (h₀ : S₀ ⊆ S) (hn : S₀.Nonempty) (g : (SAdeleRing F S)ˣ) (f : ℬₛ(S)) :
    Submodule.Quotient.mk
        (sAdelePrincipalValue F h₀ (schwartzBruhatUnitTranslate g f)) =
      (Submodule.Quotient.mk
        (schwartzBruhatUnitTranslate g (sAdelePrincipalValue F h₀ f)) : Θₛ(S)) := by sorry

/-- Paper: Lemma 5.3.1.5, p. 242.
The global principal value commutes with each idele translation on theta classes. -/
theorem globalThetaPrincipalValue_equivariant {S₀ : Finset V}
    (hn : S₀.Nonempty) (g : IdeleGroup (𝓞 F) F) (f : ℬ(𝔸[F])) :
    Submodule.Quotient.mk (adelePrincipalValue F S₀ (schwartzBruhatUnitTranslate g f)) =
      (Submodule.Quotient.mk
        (schwartzBruhatUnitTranslate g (adelePrincipalValue F S₀ f)) : Θ𝔽) := by sorry

/-- Paper: Lemma 5.3.1.5, p. 242.
The S-local principal value commutes with the norm-one character average of §5.2.3. -/
theorem sLocalThetaPrincipalValue_isotypicAverage {S₀ S : Finset V}
    (h₀ : S₀ ⊆ S) (χ : PontryaginDual (sIdeleQuotientNorm F S).ker) (x : Θₛ(S)) :
    let A := (existsUnique_sLocalThetaIsotypicAverage (F := F) χ).exists.choose
    sLocalThetaPrincipalValue F h₀ (A x) = A (sLocalThetaPrincipalValue F h₀ x) := by sorry

/-- Paper: Lemma 5.3.1.5, p. 242.
The global principal value commutes with the norm-one character average of §5.2.3. -/
theorem globalThetaPrincipalValue_isotypicAverage (S₀ : Finset V)
    (χ : PontryaginDual (ideleClassNorm F).ker) (x : Θ𝔽) :
    let A := (existsUnique_globalThetaIsotypicAverage (F := F) χ).exists.choose
    globalThetaPrincipalValue F S₀ (A x) = A (globalThetaPrincipalValue F S₀ x) := by sorry

end AdelicPrincipalValue


section DistributionOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "𝒟(" E ")" => 𝓓((⊤ : TopologicalSpace.Opens E), ℂ)

/-- Paper: Theorem 5.3.2.3, p. 245.
A distribution has order at most N if on each compact support it is bounded by the sup norms
of derivatives of orders zero through N. The same predicate applies to a tempered distribution
by restricting it to compactly supported test functions. -/
def DistributionOrderLE (T : 𝒟(E) → ℂ) (N : ℕ) : Prop :=
  ∀ K : Compacts E, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f : 𝒟(E)), tsupport (f : E → ℂ) ⊆ (K : Set E) →
      ∀ B : ℝ, 0 ≤ B →
        (∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j (f : E → ℂ) x‖ ≤ B) →
        ‖T f‖ ≤ C * B

/-- Paper: Theorem 5.3.2.1, p. 243.
Point evaluation on compactly supported tests has order at most zero. -/
theorem distributionOrderLE_eval (x : E) :
    DistributionOrderLE (fun f : 𝒟(E) ↦ f x) 0 := by
  intro K
  refine ⟨1, zero_le_one, fun f _ B _ h ↦ ?_⟩
  have hx := h 0 le_rfl x
  rw [norm_iteratedFDeriv_zero] at hx
  rw [one_mul]
  exact hx

/-- Paper: Theorem 5.3.2.1, p. 243.
The distributional support of a tempered distribution is contained in the origin. -/
abbrev TemperedSupportedAtOrigin (T : StrongDual ℂ 𝓢(E, ℂ)) : Prop :=
  Distribution.dsupport (⇑T) ⊆ {(0 : E)}

/-- Paper: Theorem 5.3.2.1, p. 243.
The Dirac distribution at zero is supported at zero. -/
theorem temperedSupportedAtOrigin_delta :
    TemperedSupportedAtOrigin (TemperedDistribution.delta (0 : E)) := by
  intro x hx
  exact (Distribution.mem_dsupport_iff x).mp hx {0}
    (TemperedDistribution.isVanishingOn_delta 0) isClosed_singleton

/-- Paper: Theorem 5.3.2.1, p. 243 and Definition D.1.8.2, p. 779.
A pointwise identification with additive Schwartz–Bruhat functions transports
the support of Appendix D to the distributional support of the classical test space. -/
theorem temperedSupport_eq_bruhatSupport_preimage
    (e : 𝓢(E, ℂ) ≃L[ℂ] SchwartzBruhat (Multiplicative E))
    (he : ∀ (f : 𝓢(E, ℂ)) (x : E), e f (Multiplicative.ofAdd x) = f x)
    (T : StrongDual ℂ 𝓢(E, ℂ)) :
    Distribution.dsupport (⇑T) = Multiplicative.ofAdd ⁻¹'
      schwartzBruhatDistributionSupport (T.comp e.symm.toContinuousLinearMap) := by
  let a : E ≃ₜ Multiplicative E := Homeomorph.refl E
  have hs (f : 𝓢(E, ℂ)) :
      tsupport (f : E → ℂ) = a ⁻¹' tsupport (e f : Multiplicative E → ℂ) := by
    have h : (e f : Multiplicative E → ℂ) ∘ a = (f : E → ℂ) := funext (he f)
    rw [← tsupport_comp_eq_preimage _ a, h]
  ext x
  change x ∈ Distribution.dsupport (⇑T) ↔ a x ∈ schwartzBruhatDistributionSupport _
  apply not_iff_not.mp
  refine (Distribution.notMem_dsupport_iff (f := (T : 𝓢(E, ℂ) → ℂ)) x).trans ?_
  simp only [schwartzBruhatDistributionSupport, Set.mem_compl_iff, not_not,
    schwartzBruhatVanishingLocus, Set.mem_sUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨U, hU, ho, hx⟩
    refine ⟨a '' U, ⟨a.isOpenMap U ho, ?_⟩, ⟨x, hx, rfl⟩⟩
    intro g hg
    change T (e.symm g) = 0
    apply hU
    rw [hs, e.apply_symm_apply]
    exact (Set.preimage_mono hg).trans (by rw [Set.preimage_image_eq _ a.injective])
  · rintro ⟨U, ⟨ho, hU⟩, hx⟩
    refine ⟨a ⁻¹' U, ?_, ho.preimage a.continuous, hx⟩
    intro f hf
    have h := hU (e f) (fun y hy ↦ by
      obtain ⟨z, rfl⟩ := a.surjective y
      exact hf (by rwa [hs]))
    change T (e.symm (e f)) = 0 at h
    simpa only [e.symm_apply_apply] using h

end DistributionOrder

section RealOrigin

open scoped PowerSeries.WithPiTopology

local notation "𝒟ℝ" => 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ)

/-- Paper: Theorem 5.3.2.1, p. 243.
The kth derivative of the real Dirac distribution uses the negative transpose of
differentiation on real Schwartz functions. -/
def realDiracDerivative (k : ℕ) : StrongDual ℂ 𝓢(ℝ, ℂ) :=
  (-1 : ℂ)^k •
    (TemperedDistribution.delta (0 : ℝ)).comp ((SchwartzMap.derivCLM ℂ ℂ)^k)

/-- Paper: Theorem 5.3.2.1, p. 243.
The first derivative of the real Dirac distribution evaluates to minus the derivative at zero. -/
theorem realDiracDerivative_one (f : 𝓢(ℝ, ℂ)) :
    realDiracDerivative 1 f = -deriv (f : ℝ → ℂ) 0 := by
  change (-1 : ℂ) ^ 1 • (((SchwartzMap.derivCLM ℂ ℂ) ^ 1) f) 0 = _
  rw [pow_one, pow_one, SchwartzMap.derivCLM_apply, neg_one_smul]

/-- Paper: Theorem 5.3.2.1, p. 243.
Every real tempered distribution supported at zero is a finite linear combination of
derivatives of the Dirac distribution at zero. -/
theorem realTemperedDistribution_eq_sum_diracDerivative (T : StrongDual ℂ 𝓢(ℝ, ℂ))
    (hT : TemperedSupportedAtOrigin T) :
    ∃ (N : ℕ) (c : Fin (N + 1) → ℂ),
      T = ∑ k : Fin (N + 1), c k • realDiracDerivative k.val := by sorry

/-- Paper: Theorem 5.3.2.1(1), p. 243.
The flat real Schwartz subspace is the intersection of the kernels of all Dirac derivatives. -/
def realSchwartzFlatAtOrigin : Submodule ℂ 𝓢(ℝ, ℂ) :=
  ⨅ k : ℕ, LinearMap.ker (realDiracDerivative k).toLinearMap

/-- Paper: Theorem 5.3.2.1(1), p. 243.
A real Schwartz function lies in the flat subspace exactly when every derivative at zero
vanishes. -/
theorem mem_realSchwartzFlatAtOrigin_iff (f : 𝓢(ℝ, ℂ)) :
    f ∈ realSchwartzFlatAtOrigin ↔
      ∀ k : ℕ, iteratedDeriv k (f : ℝ → ℂ) 0 = 0 := by
  have hd (k : ℕ) : ⇑((SchwartzMap.derivCLM ℂ ℂ ^ k) f) = iteratedDeriv k f := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', iteratedDeriv_succ]
      change deriv (⇑((SchwartzMap.derivCLM ℂ ℂ ^ k) f)) = _
      rw [ih]
  rw [realSchwartzFlatAtOrigin, Submodule.mem_iInf]
  apply forall_congr'
  intro k
  change (-1 : ℂ) ^ k * ((SchwartzMap.derivCLM ℂ ℂ ^ k) f) 0 = 0 ↔ _
  rw [congrFun (hd k) 0, mul_eq_zero]
  simp

/-- Paper: Theorem 5.3.2.1(1), p. 243.
The flat real Schwartz subspace is closed. -/
theorem realSchwartzFlatAtOrigin_isClosed :
    IsClosed (realSchwartzFlatAtOrigin : Set 𝓢(ℝ, ℂ)) := by
  rw [realSchwartzFlatAtOrigin, Submodule.coe_iInf]
  exact isClosed_iInter fun k ↦ (realDiracDerivative k).isClosed_ker

-- TODO(paper-gap): The coefficient seminorms in (5.3.2.2) give the coefficientwise
-- topology on the whole polynomial space and do not give its finest locally convex topology.

/-- Paper: Theorem 5.3.2.1(1), p. 243.
Polynomials with the finest locally convex topology identify with the strong dual of the
real Schwartz quotient by flat functions through the factorial-normalized Dirac derivatives.
The least order bound of the distribution is the polynomial's natural degree.
Deviation: Uses the finest locally convex topology and omits the false equivalence in (5.3.2.2). -/
theorem realDiracDerivatives_polynomialEquiv :
    ∃ e : FinestLocallyConvex (Polynomial ℂ) ≃L[ℂ]
        StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin),
      (∀ k : ℕ, ∀ f : 𝓢(ℝ, ℂ),
        e (Polynomial.monomial k 1) (realSchwartzFlatAtOrigin.mkQ f) =
          realDiracDerivative k f / (k.factorial : ℂ)) ∧
      ∀ (p : Polynomial ℂ) (N : ℕ),
        DistributionOrderLE
          (fun f : 𝒟ℝ ↦ e p (realSchwartzFlatAtOrigin.mkQ
            (f.hasCompactSupport.toSchwartzMap f.contDiff))) N ↔ p.natDegree ≤ N := by sorry

/-- Paper: Theorem 5.3.2.1(2), p. 243.
The real Schwartz quotient by flat functions is identified with formal power series by the
Taylor map. The topology of coefficientwise convergence is generated by (5.3.2.3).
Deviation: The Taylor formula is applied to test functions, as required by the quotient domain. -/
theorem realSchwartzTaylor_equiv :
    ∃ e : (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) ≃L[ℂ] PowerSeries ℂ,
      ∀ (f : 𝓢(ℝ, ℂ)) (k : ℕ),
        PowerSeries.coeff k (e (realSchwartzFlatAtOrigin.mkQ f)) =
          iteratedDeriv k (f : ℝ → ℂ) 0 / (k.factorial : ℂ) := by sorry

/-- Paper: Remark 5.3.2.2, p. 243.
Pullback from the strong dual of the real flat quotient embeds it in the strong dual of the
real Schwartz space with image the annihilator of the flat subspace. -/
theorem realSchwartzFlatQuotient_strongDual :
    let pull := fun T : StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) ↦
      T.comp realSchwartzFlatAtOrigin.mkQL
    IsEmbedding pull ∧ Set.range pull =
      {T : StrongDual ℂ 𝓢(ℝ, ℂ) | ∀ f ∈ realSchwartzFlatAtOrigin, T f = 0} := by sorry

end RealOrigin

section CoordinatePlane

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "Eᵣ(" ι ")" => EuclideanSpace ℝ ι
local notation "𝒟(" ι ")" => 𝓓((⊤ : TopologicalSpace.Opens Eᵣ(ι)), ℂ)
local notation "𝒮(" ι ")" => 𝓢(Eᵣ(ι), ℂ)
local notation "𝒟'(" ι ")" => StrongDual ℂ 𝒟(ι)
local notation "𝒮'(" ι ")" => StrongDual ℂ 𝒮(ι)

open Classical in
/-- Paper: Theorem 5.3.2.3, p. 245.
The coordinate derivative for a multi-index acts by the indicated number of derivatives
in each coordinate. The factors can be ordered arbitrarily on smooth tests. -/
def coordinateDerivative {ι A : Type*} [Fintype ι] [Monoid A] (derivative : ι → A)
    (α : ι → ℕ) : A :=
  ((Finset.univ.toList : List ι).map (fun i ↦ derivative i ^ α i)).prod

/-- The coordinate derivative of the zero multi-index is the identity. -/
theorem coordinateDerivative_zero {ι A : Type*} [Fintype ι] [Monoid A] (derivative : ι → A) :
    coordinateDerivative derivative (0 : ι → ℕ) = 1 := by
  simp [coordinateDerivative]

open Classical in
/-- Paper: Theorem 5.3.2.3, p. 245.
A multi-index supported in one coordinate acts by the corresponding power
of that coordinate's derivative. -/
theorem coordinateDerivative_single {ι A : Type*} [Fintype ι] [Monoid A] (derivative : ι → A)
    (i : ι) (k : ℕ) :
    coordinateDerivative derivative (Pi.single i k) = derivative i ^ k := by
  have key : ∀ l : List ι, l.Nodup →
      (l.map fun j ↦ derivative j ^ (Pi.single i k : ι → ℕ) j).prod =
        if i ∈ l then derivative i ^ k else 1 := by
    intro l hl
    induction l with
    | nil => simp
    | cons a t ih =>
      rw [List.nodup_cons] at hl
      by_cases h : a = i
      · subst h
        simp [hl.1, ih hl.2]
      · rw [List.map_cons, List.prod_cons, ih hl.2, Pi.single_apply, if_neg h,
          pow_zero, one_mul]
        simp [Ne.symm h]
  unfold coordinateDerivative
  rw [key _ (Finset.nodup_toList _)]
  simp

open Classical in
local notation "eᵣ" i => WithLp.toLp 2 (Pi.single i (1 : ℝ))

local notation "∂𝒟[" I ", " α "]" =>
  coordinateDerivative
    (fun i : I ↦ (LineDeriv.lineDerivOpCLM ℂ 𝒟(I) (eᵣ i : Eᵣ(I)) : 𝒟(I) →L[ℂ] 𝒟(I))) α
local notation "∂𝒮[" I ", " α "]" =>
  coordinateDerivative
    (fun i : I ↦ (LineDeriv.lineDerivOpCLM ℂ 𝒮(I) (eᵣ i : Eᵣ(I)) : 𝒮(I) →L[ℂ] 𝒮(I))) α

local notation "insertPlane" y =>
  WithLp.toLp 2 (Sum.elim (fun _ ↦ (0 : ℝ)) (fun j ↦ y j))

/-- Precomposition with a closed-embedding continuous linear map of norm at most one is a
continuous linear map between spaces of test functions. -/
private theorem exists_testFunction_coordinatePlaneRestriction_comp {E E' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (g : E' →L[ℝ] E) (hg : IsClosedEmbedding g) (hn : ‖g‖ ≤ 1) :
    ∃ R : 𝓓((⊤ : TopologicalSpace.Opens E), ℂ) →L[ℂ] 𝓓((⊤ : TopologicalSpace.Opens E'), ℂ),
      ∀ (f : 𝓓((⊤ : TopologicalSpace.Opens E), ℂ)) (y : E'), R f y = f (g y) := by
  have hloc (K : TopologicalSpace.Compacts E) :
      ∃ M : ContDiffMapSupportedIn E ℂ ⊤ K →L[ℂ]
          ContDiffMapSupportedIn E' ℂ ⊤ ⟨g ⁻¹' K, hg.isCompact_preimage K.isCompact⟩,
        ∀ f y, M f y = f (g y) := by
    let M : ContDiffMapSupportedIn E ℂ ⊤ K →ₗ[ℂ]
        ContDiffMapSupportedIn E' ℂ ⊤ ⟨g ⁻¹' K, hg.isCompact_preimage K.isCompact⟩ :=
      { toFun := fun f ↦ ContDiffMapSupportedIn.of_support_subset
          (f.contDiff.comp g.contDiff) (fun _ hy ↦ f.support_subset hy)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    refine ⟨⟨M, WithSeminorms.continuous_of_isBounded
      (ContDiffMapSupportedIn.withSeminorms ℂ _ ℂ _ _)
      (ContDiffMapSupportedIn.withSeminorms ℂ _ ℂ _ _) _
      (Seminorm.IsBounded.of_real fun i ↦ ⟨{i}, 1, fun f ↦ ?_⟩)⟩, fun _ _ ↦ rfl⟩
    rw [Finset.sup_singleton, one_mul]
    refine (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (apply_nonneg _ _) i _).mpr
      fun y _ ↦ ?_
    change ‖iteratedFDeriv ℝ i (⇑f ∘ g) y‖ ≤ _
    rw [g.iteratedFDeriv_comp_right f.contDiff y (mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    calc _ ≤ ‖iteratedFDeriv ℝ i f (g y)‖ * 1 := by
          gcongr
          exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun _ _ ↦ hn
      _ ≤ _ := by
          rw [mul_one]
          exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ
  let L : 𝓓((⊤ : TopologicalSpace.Opens E), ℂ) →ₗ[ℂ] 𝓓((⊤ : TopologicalSpace.Opens E'), ℂ) :=
    { toFun := fun f ↦ ⟨f ∘ g, f.contDiff.comp g.contDiff,
        f.hasCompactSupport.comp_isClosedEmbedding hg, fun _ _ ↦ trivial⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hL : Continuous L := by
    refine (TestFunction.continuous_iff_continuous_comp L).mpr fun K hK ↦ ?_
    obtain ⟨M, hM⟩ := hloc K
    have h : L ∘ TestFunction.ofSupportedIn hK =
        TestFunction.ofSupportedIn (fun _ _ ↦ trivial) ∘ M :=
      funext fun f ↦ TestFunction.ext fun y ↦ (hM f y).symm
    rw [h]
    exact (TestFunction.continuous_ofSupportedIn _).comp M.continuous
  exact ⟨⟨L, hL⟩, fun _ _ ↦ rfl⟩

/-- Inserting zeros into the normal coordinates is a continuous linear map of norm at most one
whose norm is preserved, hence a closed embedding. -/
private theorem exists_coordinatePlaneRestriction_inclusion :
    ∃ g : Eᵣ(κ) →L[ℝ] Eᵣ(ι ⊕ κ), (∀ y : Eᵣ(κ), g y = insertPlane y) ∧
      IsClosedEmbedding g ∧ ‖g‖ ≤ 1 ∧ ∀ y, ‖g y‖ = ‖y‖ := by
  let g : Eᵣ(κ) →L[ℝ] Eᵣ(ι ⊕ κ) := LinearMap.toContinuousLinearMap
    { toFun := fun y ↦ insertPlane y
      map_add' := fun y y' ↦ by ext i; cases i <;> simp
      map_smul' := fun c y ↦ by ext i; cases i <;> simp }
  have hnorm (y : Eᵣ(κ)) : ‖g y‖ = ‖y‖ := by
    simp [g, EuclideanSpace.norm_eq, Fintype.sum_sum_type]
  exact ⟨g, fun _ ↦ rfl, (AddMonoidHomClass.isometry_of_norm _ hnorm).isClosedEmbedding,
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y ↦ by rw [hnorm, one_mul], hnorm⟩

/-- Paper: Theorem 5.3.2.3(1), p. 245.
Inserting zeros into the normal coordinates gives a continuous linear restriction map
on compactly supported smooth functions. -/
theorem exists_testFunction_coordinatePlaneRestriction :
    ∃ R : 𝒟(ι ⊕ κ) →L[ℂ] 𝒟(κ), ∀ (f : 𝒟(ι ⊕ κ)) (y : Eᵣ(κ)),
      R f y = f (insertPlane y) := by
  obtain ⟨g, hg, hce, hn, -⟩ := exists_coordinatePlaneRestriction_inclusion (ι := ι) (κ := κ)
  obtain ⟨R, hR⟩ := exists_testFunction_coordinatePlaneRestriction_comp g hce hn
  exact ⟨R, fun f y ↦ (hR f y).trans (congrArg f (hg y))⟩

/-- Paper: Theorem 5.3.2.3(1), p. 245.
Inserting zeros into the normal coordinates gives a continuous linear restriction map
on Schwartz functions. -/
theorem exists_schwartz_coordinatePlaneRestriction :
    ∃ R : 𝒮(ι ⊕ κ) →L[ℂ] 𝒮(κ), ∀ (f : 𝒮(ι ⊕ κ)) (y : Eᵣ(κ)),
      R f y = f (insertPlane y) := by
  obtain ⟨g, hg, -, -, hnorm⟩ := exists_coordinatePlaneRestriction_inclusion (ι := ι) (κ := κ)
  have hA : AntilipschitzWith 1 g := AntilipschitzWith.of_le_mul_dist fun y y' ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, hnorm, NNReal.coe_one, one_mul]
  exact ⟨SchwartzMap.compCLMOfAntilipschitz ℂ g.hasTemperateGrowth hA,
    fun f y ↦ congrArg f (hg y)⟩

local notation "R𝒟" => (exists_testFunction_coordinatePlaneRestriction (ι := ι) (κ := κ)).choose
local notation "R𝒮" => (exists_schwartz_coordinatePlaneRestriction (ι := ι) (κ := κ)).choose
local notation "weight(" α ")" => (∑ i, α i)
local notation "index(" N ")" =>
  {α : (ι ⊕ κ) → Fin (N + 1) // (∑ i, (α i : ℕ)) ≤ N}
local notation "multi(" α ")" => (fun i ↦ ((((α).val) i).val : ℕ))
local notation "normal(" α ")" => (fun i : ι ↦ multi(α) (Sum.inl i))
local notation "tangent(" α ")" => (fun i : κ ↦ multi(α) (Sum.inr i))
local notation "factors(" f ", " g ", " x ")" =>
  f (WithLp.toLp 2 (fun i : ι ↦ x (.inl i))) * g (WithLp.toLp 2 (fun j : κ ↦ x (.inr j)))

-- TODO(paper-gap): The count N^m in (2) disagrees with the sum in (5.3.2.4).
-- In (2)–(5) the coefficient orders must be upper bounds. The distributional transpose
-- also introduces the factor (-1)^|α| in (5.3.2.5) and (5.3.2.6).

open Classical in
/-- Paper: Theorem 5.3.2.3(2), p. 245.
A compactly supported distribution of order at most N supported on a coordinate plane is a sum
of transposed restrictions of derivatives. Each coefficient has compact support and its order
is bounded by N minus the derivative degree.
Deviation: The finite indices are exactly those in (5.3.2.4). Orders are upper bounds. -/
theorem distribution_coordinatePlane_decomposition [Nonempty ι] (T : 𝒟'(ι ⊕ κ)) (N : ℕ)
    (hT : DistributionOrderLE T N)
    (hK : IsCompact (Distribution.dsupport (⇑T)))
    (hplane : Distribution.dsupport (⇑T) ⊆
      Set.range (fun y : Eᵣ(κ) ↦ (insertPlane y : Eᵣ(ι ⊕ κ)))) :
    ∃ A : index(N) → 𝒟'(κ),
      (∀ α, DistributionOrderLE (A α) (N - weight(multi(α))) ∧
        IsCompact (Distribution.dsupport (⇑(A α)))) ∧
      ∀ f : 𝒟(ι ⊕ κ), T f = ∑ α : index(N), A α (R𝒟 (∂𝒟[ι ⊕ κ, multi(α)] f)) := by sorry

open Classical in
/-- Paper: Theorem 5.3.2.3(3), p. 245.
On a pure tensor, the summand factors as the normal derivative evaluated at zero and the
tangential coefficient applied to the derivative of the tangential test.
Deviation: This is the test-function derivative form of (5.3.2.5), with the transpose signs
canceled. Using distributional derivatives in both factors requires a sign of (-1)^|α|. -/
theorem distribution_coordinatePlane_decomposition_apply_tmul {N : ℕ} (T : 𝒟'(ι ⊕ κ))
    (A : index(N) → 𝒟'(κ))
    (hA : ∀ f : 𝒟(ι ⊕ κ), T f = ∑ α : index(N), A α (R𝒟 (∂𝒟[ι ⊕ κ, multi(α)] f)))
    (f : 𝒟(ι ⊕ κ)) (g : 𝒟(ι)) (h : 𝒟(κ))
    (hf : ∀ x : Eᵣ(ι ⊕ κ), f x = factors(g, h, x)) :
    T f = ∑ α : index(N), (∂𝒟[ι, normal(α)] g) 0 * A α (∂𝒟[κ, tangent(α)] h) := by sorry

open Classical in
/-- Paper: Theorem 5.3.2.3(4), p. 245.
Tensoring a normal Dirac derivative with a tangential distribution is the transposed normal
derivative of the restriction to the coordinate plane. -/
def coordinatePlaneDiracTensor (β : ι → ℕ) (U : 𝒟'(κ)) : 𝒟'(ι ⊕ κ) :=
  (-1 : ℂ)^weight(β) • U.comp ((R𝒟).comp ∂𝒟[ι ⊕ κ, Sum.elim β (0 : κ → ℕ)])

/-- Paper: Theorem 5.3.2.3(4), p. 245.
At derivative order zero the tensor restricts the test to the coordinate plane and applies
the tangential distribution. -/
theorem coordinatePlaneDiracTensor_zero (U : 𝒟'(κ)) (f : 𝒟(ι ⊕ κ)) :
    coordinatePlaneDiracTensor (0 : ι → ℕ) U f = U (R𝒟 f) := by
  have h0 : Sum.elim (0 : ι → ℕ) (0 : κ → ℕ) = 0 := by
    ext i; cases i <;> rfl
  simp [coordinatePlaneDiracTensor, h0, coordinateDerivative_zero]

open Classical in
/-- Paper: Theorem 5.3.2.3(4), p. 245.
The decomposition is a finite sum of tensor products of normal Dirac derivatives with
tangential distributional derivatives.
Deviation: Each tensor in (5.3.2.6) has the factor (-1)^|α| required by (5.3.2.4). -/
theorem distribution_coordinatePlane_decomposition_eq_sum {N : ℕ} (T : 𝒟'(ι ⊕ κ))
    (A : index(N) → 𝒟'(κ))
    (hA : ∀ f : 𝒟(ι ⊕ κ), T f = ∑ α : index(N), A α (R𝒟 (∂𝒟[ι ⊕ κ, multi(α)] f))) :
    T = ∑ α : index(N), (-1 : ℂ)^weight(multi(α)) •
      coordinatePlaneDiracTensor (normal(α))
        ((-1 : ℂ)^weight(tangent(α)) • (A α).comp ∂𝒟[κ, tangent(α)]) := by sorry

open Classical in
/-- Paper: Theorem 5.3.2.3(5), p. 245.
Passing from a compactly supported test to its Schwartz function commutes with all
coordinate derivatives. This also identifies derivatives of the tempered extensions. -/
theorem coordinateDerivative_testFunction_toSchwartz {ι : Type*} [Fintype ι]
    (β : ι → ℕ) (f : 𝒟(ι)) :
    let g := ∂𝒟[ι, β] f
    g.hasCompactSupport.toSchwartzMap g.contDiff =
      ∂𝒮[ι, β] (f.hasCompactSupport.toSchwartzMap f.contDiff) := by
  intro g
  have hpow : ∀ i (k : ℕ) (f : 𝒟(ι)),
      ((LineDeriv.lineDerivOpCLM ℂ 𝒟(ι) (eᵣ i : Eᵣ(ι)) ^ k) f).hasCompactSupport.toSchwartzMap
          ((LineDeriv.lineDerivOpCLM ℂ 𝒟(ι) (eᵣ i : Eᵣ(ι)) ^ k) f).contDiff =
        (LineDeriv.lineDerivOpCLM ℂ 𝒮(ι) (eᵣ i : Eᵣ(ι)) ^ k)
          (f.hasCompactSupport.toSchwartzMap f.contDiff) := by
    intro i k
    induction k with
    | zero => intro f; rfl
    | succ k ih =>
      intro f
      rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, ih]
      congr 1
  show (∂𝒟[ι, β] f).hasCompactSupport.toSchwartzMap (∂𝒟[ι, β] f).contDiff = _
  unfold coordinateDerivative
  generalize (Finset.univ.toList : List ι) = l
  induction l generalizing f with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
    rw [← ih, ← hpow]

open Classical in
/-- Paper: Theorem 5.3.2.3(5), p. 245.
The coefficient distributions and the ambient distribution have tempered extensions.
The identity holds for every Schwartz test after extension.
Deviation: The tempered identity uses the test-function derivative convention of (5.3.2.4),
equivalent to the signed tensor identity with distributional derivatives. -/
theorem distribution_coordinatePlane_decomposition_tempered {N : ℕ} (T : 𝒟'(ι ⊕ κ))
    (A : index(N) → 𝒟'(κ))
    (hK : ∀ α, IsCompact (Distribution.dsupport (⇑(A α))))
    (hA : ∀ f : 𝒟(ι ⊕ κ), T f = ∑ α : index(N), A α (R𝒟 (∂𝒟[ι ⊕ κ, multi(α)] f))) :
    ∃ (U : 𝒮'(ι ⊕ κ)) (B : index(N) → 𝒮'(κ)),
      (∀ f : 𝒟(ι ⊕ κ), U (f.hasCompactSupport.toSchwartzMap f.contDiff) = T f) ∧
      (∀ α, ∀ g : 𝒟(κ), B α (g.hasCompactSupport.toSchwartzMap g.contDiff) = A α g) ∧
      ∀ f : 𝒮(ι ⊕ κ), U f = ∑ α : index(N), B α (R𝒮 (∂𝒮[ι ⊕ κ, multi(α)] f)) := by sorry

/-- Paper: Remark 5.3.2.4, p. 246.
Products of test functions define a map from the inductive tensor product with
sequentially dense range. The completed inductive tensor product is isomorphic
to the test space on the product by the same pure tensor formula.
Deviation: The isomorphism uses the completion, as required for the full test space. -/
theorem testFunction_inductiveTensor_equiv :
    let W := InductiveTensor 𝒟(ι) 𝒟(κ)
    letI : ContinuousSMul ℂ W := WithSeminorms.continuousSMul (E := W)
      (withGeneratingSeminorms_spec _ _)
    letI : UniformContinuousConstSMul ℂ W := uniformContinuousConstSMul_of_continuousConstSMul ℂ W
    ∃ e : UniformSpace.Completion W ≃L[ℂ] 𝒟(ι ⊕ κ),
      (∀ (f : 𝒟(ι)) (g : 𝒟(κ)) (x : Eᵣ(ι ⊕ κ)),
        e (UniformSpace.Completion.coe' (α := W) (f ⊗ₜ[ℂ] g)) x = factors(f, g, x)) ∧
      ∀ h : 𝒟(ι ⊕ κ), ∃ s : ℕ → W,
        Tendsto (fun n ↦ e (s n : UniformSpace.Completion W))
          atTop (𝓝 h) := by sorry

-- TODO(paper-gap): If the tangential dimension is zero, its test space is ℂ
-- and the projective and inductive tensor products agree.

/-- Paper: Remark 5.3.2.4, p. 246.
In positive dimensions the product of test functions is not represented by a
continuous linear map out of the projective tensor product.
Deviation: The exception of a zero-dimensional factor is excluded explicitly. -/
theorem testFunction_no_projectiveTensor_product [Nonempty ι] [Nonempty κ] :
    ¬ ∃ L : ProjectiveTensor 𝒟(ι) 𝒟(κ) →L[ℂ] 𝒟(ι ⊕ κ),
      ∀ (f : 𝒟(ι)) (g : 𝒟(κ)) (x : Eᵣ(ι ⊕ κ)),
        L (f ⊗ₜ[ℂ] g) x = factors(f, g, x) := by sorry

end CoordinatePlane

section ComplexOrigin

open scoped MvPowerSeries.WithPiTopology

local notation "𝒟ℂ" => 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)
local notation "∂x" => LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) (1 : ℂ)
local notation "∂y" => LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) Complex.I

/-- Paper: Theorem 5.3.2.5, p. 246.
The holomorphic Wirtinger operator on Schwartz functions is half of the real
directional derivative minus i times the imaginary directional derivative. -/
def schwartzWirtingerZ : 𝓢(ℂ, ℂ) →L[ℂ] 𝓢(ℂ, ℂ) :=
  (2 : ℂ)⁻¹ • (∂x - Complex.I • ∂y)

/-- Paper: Theorem 5.3.2.5, p. 246.
The antiholomorphic Wirtinger operator on Schwartz functions is half of the real
directional derivative plus i times the imaginary directional derivative. -/
def schwartzWirtingerZBar : 𝓢(ℂ, ℂ) →L[ℂ] 𝓢(ℂ, ℂ) :=
  (2 : ℂ)⁻¹ • (∂x + Complex.I • ∂y)

/-- Paper: Theorem 5.3.2.5, pp. 246–247.
The bundled Schwartz derivatives have the pointwise Wirtinger conventions of §3.3.2. -/
theorem schwartzWirtinger_apply (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    schwartzWirtingerZ f z = wirtingerDeriv f z ∧
    schwartzWirtingerZBar f z = wirtingerConjDeriv f z := by
  let a := fderiv ℝ (f : ℂ → ℂ) z 1
  let b := Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I
  change (2 : ℂ)⁻¹ * (a - b) = (a - b) / 2 ∧ (2 : ℂ)⁻¹ * (a + b) = (a + b) / 2
  constructor <;> ring

/-- Paper: Theorem 5.3.2.5, p. 246.
The sum of the Wirtinger derivatives recovers the real directional derivative. -/
theorem schwartzWirtingerZ_add_zBar (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    schwartzWirtingerZ f z + schwartzWirtingerZBar f z = fderiv ℝ (f : ℂ → ℂ) z 1 := by
  let a := fderiv ℝ (f : ℂ → ℂ) z 1
  let b := Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I
  change (2 : ℂ)⁻¹ * (a - b) + (2 : ℂ)⁻¹ * (a + b) = a
  ring

/-- Paper: Theorem 5.3.2.5, p. 246.
The difference of the Wirtinger derivatives recovers the imaginary directional derivative
times i. -/
theorem schwartzWirtingerZBar_sub_z (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    schwartzWirtingerZBar f z - schwartzWirtingerZ f z =
      Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I := by
  let a := fderiv ℝ (f : ℂ → ℂ) z 1
  let b := Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I
  change (2 : ℂ)⁻¹ * (a + b) - (2 : ℂ)⁻¹ * (a - b) = b
  ring

/-- Paper: Theorem 5.3.2.5, p. 246.
A mixed Wirtinger derivative of the Dirac distribution at zero uses the negative transpose
of each Wirtinger differentiation on the test space. -/
def complexDiracDerivative (k l : ℕ) : StrongDual ℂ 𝓢(ℂ, ℂ) :=
  (-1 : ℂ)^(k + l) •
    (TemperedDistribution.delta (0 : ℂ)).comp
      ((schwartzWirtingerZ^k).comp (schwartzWirtingerZBar^l))

/-- Paper: Theorem 5.3.2.5, p. 246.
The first holomorphic derivative of the Dirac distribution is minus the test function's
holomorphic Wirtinger derivative at zero. -/
theorem complexDiracDerivative_one_zero (f : 𝓢(ℂ, ℂ)) :
    complexDiracDerivative 1 0 f = -schwartzWirtingerZ f 0 := by
  change (-1 : ℂ) ^ (1 + 0) • ((schwartzWirtingerZ ^ 1) ((schwartzWirtingerZBar ^ 0) f)) 0 = _
  simp

-- TODO(paper-gap): In (5.3.2.15)–(16) only the sum of tangential
-- derivatives for each normal index is determined. For a point support,
-- take both real coordinates normal in Theorem 5.3.2.3, then change basis.

/-- Paper: Theorem 5.3.2.5, p. 246.
Every complex tempered distribution supported at zero is a finite linear combination of
mixed Wirtinger derivatives of the Dirac distribution. -/
theorem complexTemperedDistribution_eq_sum_diracDerivative (T : StrongDual ℂ 𝓢(ℂ, ℂ))
    (hT : TemperedSupportedAtOrigin T) :
    ∃ (N : ℕ) (c : (k : Fin (N + 1)) → Fin (N + 1 - k.val) → ℂ),
      T = ∑ k : Fin (N + 1), ∑ l : Fin (N + 1 - k.val),
        c k l • complexDiracDerivative k.val l.val := by sorry

/-- Paper: Theorem 5.3.2.5(1), p. 246.
The flat complex Schwartz subspace is the common kernel of the mixed Dirac derivatives. -/
def complexSchwartzFlatAtOrigin : Submodule ℂ 𝓢(ℂ, ℂ) :=
  ⨅ k : ℕ, ⨅ l : ℕ, LinearMap.ker (complexDiracDerivative k l).toLinearMap

/-- Paper: Theorem 5.3.2.5(1), p. 246.
Membership in the flat complex subspace means all mixed Wirtinger derivatives vanish at zero. -/
theorem mem_complexSchwartzFlatAtOrigin_iff (f : 𝓢(ℂ, ℂ)) :
    f ∈ complexSchwartzFlatAtOrigin ↔
      ∀ k l : ℕ, (schwartzWirtingerZ^k) ((schwartzWirtingerZBar^l) f) 0 = 0 := by
  simp only [complexSchwartzFlatAtOrigin, Submodule.mem_iInf, LinearMap.mem_ker]
  refine forall₂_congr fun k l ↦ ?_
  change (-1 : ℂ) ^ (k + l) • ((schwartzWirtingerZ ^ k) ((schwartzWirtingerZBar ^ l) f)) 0 = 0 ↔ _
  rw [smul_eq_zero]
  exact or_iff_right (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

/-- Paper: Theorem 5.3.2.5(1), p. 246.
The flat complex Schwartz subspace is closed. -/
theorem complexSchwartzFlatAtOrigin_isClosed :
    IsClosed (complexSchwartzFlatAtOrigin : Set 𝓢(ℂ, ℂ)) := by
  simp only [complexSchwartzFlatAtOrigin, Submodule.coe_iInf]
  exact isClosed_iInter fun k ↦ isClosed_iInter fun l ↦ (complexDiracDerivative k l).isClosed_ker

/-- Paper: Theorem 5.3.2.5(1), p. 246.
The quotient adjoint identifies the strong dual of the complex flat quotient with
the annihilator in the strong dual of the complex Schwartz space. -/
theorem complexSchwartzFlatQuotient_strongDual :
    let pull := fun T : StrongDual ℂ (𝓢(ℂ, ℂ) ⧸ complexSchwartzFlatAtOrigin) ↦
      T.comp complexSchwartzFlatAtOrigin.mkQL
    IsEmbedding pull ∧ Set.range pull =
      {T : StrongDual ℂ 𝓢(ℂ, ℂ) | ∀ f ∈ complexSchwartzFlatAtOrigin, T f = 0} := by sorry

-- TODO(paper-gap): The coefficient seminorms in (5.3.2.12) give the coefficientwise
-- topology on the whole polynomial space and do not give its finest locally convex topology.

/-- Paper: Theorem 5.3.2.5(1), p. 246.
Polynomials in two variables with the finest locally convex topology identify with the strong
dual of the complex flat quotient through factorial-normalized mixed Dirac derivatives.
The least order bound of the distribution is the polynomial's total degree.
Deviation: Uses the finest locally convex topology and omits the false equivalence in
(5.3.2.12). -/
theorem complexDiracDerivatives_polynomialEquiv :
    ∃ e : FinestLocallyConvex (MvPolynomial (Fin 2) ℂ) ≃L[ℂ]
        StrongDual ℂ (𝓢(ℂ, ℂ) ⧸ complexSchwartzFlatAtOrigin),
      (∀ s : Fin 2 →₀ ℕ, ∀ f : 𝓢(ℂ, ℂ),
        e (MvPolynomial.monomial s 1) (complexSchwartzFlatAtOrigin.mkQ f) =
          complexDiracDerivative (s 0) (s 1) f /
            ((s 0).factorial * (s 1).factorial : ℂ)) ∧
      ∀ (p : MvPolynomial (Fin 2) ℂ) (N : ℕ),
        DistributionOrderLE
          (fun f : 𝒟ℂ ↦ e p (complexSchwartzFlatAtOrigin.mkQ
            (f.hasCompactSupport.toSchwartzMap f.contDiff))) N ↔ p.totalDegree ≤ N := by sorry

-- TODO(paper-gap): Under ordinary coefficient pairing the adjoint on p. 249
-- has a sign for each odd total degree and includes all degrees. The positive
-- Taylor map below differs from that adjoint by (X,Y) ↦ (-X,-Y).

/-- Paper: Theorem 5.3.2.5(2), p. 246.
The complex flat quotient is identified with formal power series in two variables by the
mixed Wirtinger Taylor coefficients, with the coefficientwise topology of (5.3.2.13).
Deviation: The Taylor formula takes a Schwartz test as input, as required by the domain. -/
theorem complexSchwartzTaylor_equiv :
    ∃ e : (𝓢(ℂ, ℂ) ⧸ complexSchwartzFlatAtOrigin) ≃L[ℂ] MvPowerSeries (Fin 2) ℂ,
      ∀ (f : 𝓢(ℂ, ℂ)) (s : Fin 2 →₀ ℕ),
        MvPowerSeries.coeff s (e (complexSchwartzFlatAtOrigin.mkQ f)) =
          (schwartzWirtingerZ^(s 0)) ((schwartzWirtingerZBar^(s 1)) f) 0 /
            ((s 0).factorial * (s 1).factorial : ℂ) := by sorry

end ComplexOrigin

end RiemannMasullo
