module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Topological spaces of adelic theta functions and idelic Z-functions

Masullo, §5.1, pp. 221–230. The finite set in the S-local declarations indexes the
finite places. All archimedean places are included.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Topology
open scoped NumberField.AdeleRing NNReal

namespace RiemannMasullo

set_option quotPrecheck false

section MeromorphicTarget

variable {X : Type*} [TopologicalSpace X]
variable (chart : X → ℂ → X) (orderBound : X → WithTop ℤ)

local notation "Regular" => {c : X // 0 ≤ orderBound c}

/-- Paper: Definition 5.1.1.1(1)–(2), p. 223.
A function on the regular locus admits a continuation with bounded poles if it
extends in the complex coordinates with the prescribed lower bounds on order.
Deviation: The coordinates are centered at each point. The continuation is required
to be analytic at every point where the order bound permits no pole. -/
def HasMeromorphicContinuationWithPoleBound (u : C(Regular, ℂ)) : Prop :=
  ∃ Z : X → ℂ, (∀ c : Regular, Z c = u c) ∧ ∀ c : X,
    let germ := fun z ↦ Z (chart c z)
    MeromorphicAt germ 0 ∧ orderBound c ≤ meromorphicOrderAt germ 0 ∧
      (0 ≤ orderBound c → AnalyticAt ℂ germ 0)

/-- Paper: Definition 5.1.1.1(1)–(2), p. 223.
The continuation condition is preserved by the complex vector space operations.
Deviation: These are the closure fields for the submodule of regular restrictions. -/
theorem meromorphicContinuationWithPoleBound_closed :
    let admissible := HasMeromorphicContinuationWithPoleBound chart orderBound
    admissible 0 ∧ (∀ u v, admissible u → admissible v → admissible (u + v)) ∧
      (∀ (a : ℂ) u, admissible u → admissible (a • u)) := by
  refine ⟨⟨0, fun _ ↦ rfl, fun c ↦ ?_⟩, ?_, ?_⟩
  · refine ⟨analyticAt_const.meromorphicAt, ?_, fun _ ↦ analyticAt_const⟩
    exact le_top.trans_eq (meromorphicOrderAt_eq_top_iff.2
      (Filter.Eventually.of_forall fun _ ↦ rfl)).symm
  · rintro u v ⟨Zu, hu, hZu⟩ ⟨Zv, hv, hZv⟩
    refine ⟨Zu + Zv, fun c ↦ by simp [hu, hv], fun c ↦ ?_⟩
    obtain ⟨mu, ou, au⟩ := hZu c
    obtain ⟨mv, ov, av⟩ := hZv c
    refine ⟨mu.add mv, ?_, fun h ↦ (au h).add (av h)⟩
    exact (le_min ou ov).trans (meromorphicOrderAt_add mu mv)
  · rintro a u ⟨Z, hu, hZ⟩
    refine ⟨a • Z, fun c ↦ by simp [hu], fun c ↦ ?_⟩
    obtain ⟨m, o, an⟩ := hZ c
    refine ⟨m.const_smul a, ?_, fun h ↦ (an h).const_smul⟩
    show orderBound c ≤ meromorphicOrderAt (a • fun z ↦ Z (chart c z)) 0
    by_cases ha : a = 0
    · subst ha
      exact le_top.trans_eq (meromorphicOrderAt_eq_top_iff.2
        (Filter.Eventually.of_forall fun _ ↦ zero_smul ℂ _)).symm
    · rwa [meromorphicOrderAt_const_smul_eq_meromorphicOrderAt ha]

/-- Paper: Definition 5.1.1.1(1)–(2), p. 223.
Meromorphic functions with bounded poles form a complex vector space with the
compact-open topology of their restrictions to the complement of the allowed poles.
Deviation: We represent the functions by their regular values and use the pole order
bounds and compact convergence topology specified in §5.1.3. -/
def meromorphicWithPoleBound : Submodule ℂ C(Regular, ℂ) where
  carrier := {u | HasMeromorphicContinuationWithPoleBound chart orderBound u}
  zero_mem' := (meromorphicContinuationWithPoleBound_closed chart orderBound).1
  add_mem' := fun hu hv ↦ (meromorphicContinuationWithPoleBound_closed chart orderBound).2.1
    _ _ hu hv
  smul_mem' := (meromorphicContinuationWithPoleBound_closed chart orderBound).2.2

/-- Paper: Definition 5.1.1.1(1)–(2), p. 223.
With the zero divisor, membership in the meromorphic target amounts to holomorphy.
Deviation: This checks the target in the case where no poles are allowed. -/
theorem mem_meromorphicWithPoleBound_zero_iff
    (u : C({c : X // 0 ≤ (0 : WithTop ℤ)}, ℂ)) :
    u ∈ meromorphicWithPoleBound chart (fun _ ↦ 0) ↔
      ∀ c : X, AnalyticAt ℂ (fun z ↦ u ⟨chart c z, le_rfl⟩) 0 := by
  constructor
  · rintro ⟨Z, hZ, h⟩ c
    have hZ' : Z = fun x ↦ u ⟨x, le_rfl⟩ := funext fun x ↦ hZ ⟨x, le_rfl⟩
    subst hZ'
    exact (h c).2.2 le_rfl
  · intro h
    refine ⟨fun x ↦ u ⟨x, le_rfl⟩, fun _ ↦ rfl, fun c ↦ ?_⟩
    exact ⟨(h c).meromorphicAt, (h c).meromorphicOrderAt_nonneg, fun _ ↦ h c⟩

end MeromorphicTarget

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Jₛ" => SIdeleQuotient F S
local notation "ℬ𝔽" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "X𝔽" => QuasiCharacter C𝔽
local notation "Xₛ" => QuasiCharacter Jₛ
local notation "m𝔽" => ideleClassNorm F
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "normChart𝔽" => quasiCharacterNormTwist (G := C𝔽) m𝔽
  (isProperMap_ideleClassNorm F).continuous
local notation "normChartₛ" => quasiCharacterNormTwist (G := Jₛ) mₛ
  (isProperMap_sIdeleQuotientNorm F S).continuous

/-- Paper: Definition 5.1.1.1(1), p. 223.
The possible global poles are simple and occur at the trivial and norm characters.
Deviation: The simple-pole bound from §5.1.3 is built into the target here. -/
def globalIdelicOrderBound (c : X𝔽) : WithTop ℤ :=
  open Classical in
  if c = 1 ∨ c = ideleClassNormTwist (1 : PontryaginDual C𝔽) 1 then -1 else 0

/-- Paper: Definition 5.1.1.1(1), p. 223.
The trivial character allows a simple pole and the squared norm character allows none. -/
theorem globalIdelicOrderBound_one_and_normSquared :
    globalIdelicOrderBound (1 : X𝔽) = -1 ∧
      globalIdelicOrderBound (ideleClassNormTwist (1 : PontryaginDual C𝔽) 2) = 0 := by
  refine ⟨ite_eq_left (Or.inl rfl), ite_eq_right ?_⟩
  obtain ⟨g, hg⟩ :=
    (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1 (Units.mk0 (2 : ℝ≥0) two_ne_zero)
  have hval : ∀ s : ℂ, ideleClassNormTwist (1 : PontryaginDual C𝔽) s g = (2 : ℂ) ^ s := by
    intro s
    change (((1 : PontryaginDual C𝔽) g : Circle) : ℂ) *
      (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ s = _
    rw [hg]
    simp
  rintro (h | h)
  · have := DFunLike.congr_fun h g
    rw [hval] at this
    norm_num at this
  · have := DFunLike.congr_fun h g
    rw [hval, hval] at this
    norm_num at this

local notation "globalMeromorphic" =>
  meromorphicWithPoleBound (X := X𝔽) normChart𝔽 (globalIdelicOrderBound (F := F))

/-- Paper: Definition 5.1.1.1(1), p. 223.
The global Z-function is continuous on the locus with no allowed pole. -/
theorem globalIdelicZFunction_continuous_regular (f : ℬ𝔽) :
    Continuous (fun c : {c : X𝔽 // 0 ≤ globalIdelicOrderBound c} ↦
      globalIdelicZFunction f c.val) := by sorry

local notation "globalZValues" => fun f : ℬ𝔽 ↦
  (⟨fun c ↦ globalIdelicZFunction f c.val, globalIdelicZFunction_continuous_regular f⟩ :
    C({c : X𝔽 // 0 ≤ globalIdelicOrderBound c}, ℂ))

/-- Paper: Definition 5.1.1.1(1), p. 223.
The global Z-function satisfies the prescribed global pole bounds. -/
theorem globalIdelicZFunction_mem (f : ℬ𝔽) :
    globalZValues f ∈ globalMeromorphic := by sorry

/-- Paper: Definition 5.1.1.1(1), p. 223.
The regular values of global Z-functions depend complex linearly on the test function. -/
theorem globalIdelicZFunction_isLinear :
    IsLinearMap ℂ (globalZValues : ℬ𝔽 → _) := by sorry

/-- Paper: Definition 5.1.1.1(1), p. 223.
The global idelic Mellin transform sends a test function to its continued Z-function.
Deviation: The target uses the bounded-pole model of §5.1.3. -/
def globalIdelicMellin : ℬ𝔽 →ₗ[ℂ] ↥globalMeromorphic :=
  LinearMap.codRestrict globalMeromorphic
    (IsLinearMap.mk' globalZValues globalIdelicZFunction_isLinear) globalIdelicZFunction_mem

/-- Paper: Definition 5.1.1.1(1), p. 223.
At a regular character the global transform evaluates to the continued global zeta integral. -/
theorem globalIdelicMellin_apply (f : ℬ𝔽) (c : {c : X𝔽 // 0 ≤ globalIdelicOrderBound c}) :
    (globalIdelicMellin (F := F) f).val c = globalIdelicZFunction f c.val := rfl

/-- Paper: Definition 5.1.1.1(2), p. 223.
The allowed S-local pole multiplicity is that of the correcting factor.
Deviation: We use the nonpositive part of the meromorphic order, as in §3.3.1.
The bound is zero at the zeros of the correcting factor. -/
def sLocalIdelicOrderBound (c : Xₛ) : WithTop ℤ :=
  min 0 (meromorphicOrderAt (fun z ↦ sLocalRhoFactor (F := F) (S := S) (normChartₛ c z)) 0)

/-- Paper: Definition 5.1.1.1(2), p. 223.
For the rational field with only the real place, the trivial character allows a simple pole
and the norm character allows no pole.
Deviation: This checks the order bound against the real Tate factor. -/
theorem sLocalIdelicOrderBound_rat_archimedean :
    sLocalIdelicOrderBound (F := ℚ) (S := ∅) 1 = -1 ∧
      sLocalIdelicOrderBound (F := ℚ) (S := ∅)
        (quasiCharacterNormTwist (G := SIdeleQuotient ℚ ∅) (sIdeleQuotientNorm ℚ ∅)
          (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous 1 1) = 0 := by sorry

local notation "sLocalMeromorphic" =>
  meromorphicWithPoleBound (X := Xₛ) normChartₛ (sLocalIdelicOrderBound (F := F) (S := S))

/-- Paper: Definition 5.1.1.1(2), p. 223.
The S-local Z-function is continuous on the locus with no allowed pole. -/
theorem sLocalIdelicZFunction_continuous_regular (f : ℬₛ) :
    Continuous (fun c : {c : Xₛ // 0 ≤ sLocalIdelicOrderBound c} ↦
      sLocalIdelicZFunction f c.val) := by sorry

local notation "sLocalZValues" => fun f : ℬₛ ↦
  (⟨fun c ↦ sLocalIdelicZFunction f c.val, sLocalIdelicZFunction_continuous_regular f⟩ :
    C({c : Xₛ // 0 ≤ sLocalIdelicOrderBound c}, ℂ))

/-- Paper: Definition 5.1.1.1(2), p. 223.
The S-local Z-function satisfies the prescribed S-local pole bounds. -/
theorem sLocalIdelicZFunction_mem (f : ℬₛ) :
    sLocalZValues f ∈ sLocalMeromorphic := by sorry

/-- Paper: Definition 5.1.1.1(2), p. 223.
The regular values of S-local Z-functions depend complex linearly on the test function. -/
theorem sLocalIdelicZFunction_isLinear :
    IsLinearMap ℂ (sLocalZValues : ℬₛ → _) := by sorry

/-- Paper: Definition 5.1.1.1(2), p. 223.
The S-local idelic Mellin transform sends a test function to its continued Z-function.
Deviation: The target uses the bounded-pole model of §5.1.3. -/
def sLocalIdelicMellin : ℬₛ →ₗ[ℂ] ↥sLocalMeromorphic :=
  LinearMap.codRestrict sLocalMeromorphic
    (IsLinearMap.mk' sLocalZValues sLocalIdelicZFunction_isLinear) sLocalIdelicZFunction_mem

/-- Paper: Definition 5.1.1.1(2), p. 223.
At a regular character the S-local transform evaluates to the continued S-local zeta integral. -/
theorem sLocalIdelicMellin_apply (f : ℬₛ) (c : {c : Xₛ // 0 ≤ sLocalIdelicOrderBound c}) :
    (sLocalIdelicMellin (F := F) (S := S) f).val c = sLocalIdelicZFunction f c.val := rfl

variable (F) in
/-- Paper: Definition 5.1.1.1(3), p. 223.
The global theta operator is the complex-linear map of §2.2.3. -/
def adelicThetaLinearMap : ℬ𝔽 →ₗ[ℂ] C(C𝔽, ℂ) :=
  IsLinearMap.mk' (adelicTheta (F := F)) (adelicTheta_isLinear (F := F))

/-- Paper: Definition 5.1.1.1(3), p. 223.
Evaluating the linear theta map returns the adelic theta function. -/
theorem adelicThetaLinearMap_apply (f : ℬ𝔽) :
    adelicThetaLinearMap F f = adelicTheta f := rfl

local notation "theta𝔽" => adelicThetaLinearMap F
local notation "thetaₛ" => sLocalAdelicTheta F S

variable (F) in
/-- Paper: Definition 5.1.1.1(3), p. 223.
The space of global adelic theta functions is the quotient by the global theta kernel,
with the quotient topology. -/
abbrev GlobalAdelicThetaSpace := ℬ𝔽 ⧸ LinearMap.ker theta𝔽

/-- Paper: Definition 5.1.1.1(3), p. 223.
Two test functions give the same global quotient class exactly when their theta functions agree. -/
theorem globalAdelicThetaSpace_mk_eq_iff (f g : ℬ𝔽) :
    (Submodule.Quotient.mk f : GlobalAdelicThetaSpace F) = Submodule.Quotient.mk g ↔
      adelicTheta f = adelicTheta g := by
  rw [Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero]
  rfl

variable (F S) in
/-- Paper: Definition 5.1.1.1(3), p. 223.
The space of S-local adelic theta functions is the quotient by the S-local theta kernel,
with the quotient topology.
Deviation: We take the kernel on S-ideles. The descended theta map has the same
kernel because the map from S-ideles to S-idele classes is surjective. -/
abbrev SLocalAdelicThetaSpace := ℬₛ ⧸ LinearMap.ker thetaₛ

/-- Paper: Definition 5.1.1.1(3), p. 223.
Two test functions give the same S-local quotient class exactly when their class theta
functions agree. -/
theorem sLocalAdelicThetaSpace_mk_eq_iff (f g : ℬₛ) :
    (Submodule.Quotient.mk f : SLocalAdelicThetaSpace F S) = Submodule.Quotient.mk g ↔
      sLocalAdelicThetaOnClasses F S f = sLocalAdelicThetaOnClasses F S g := by
  rw [Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero]
  constructor
  · intro h
    refine ContinuousMap.ext fun x ↦ QuotientGroup.induction_on x fun g' ↦ ?_
    exact (sLocalAdelicThetaOnClasses_mk F S f g').trans
      ((DFunLike.congr_fun h g').trans (sLocalAdelicThetaOnClasses_mk F S g g').symm)
  · intro h
    refine ContinuousMap.ext fun x ↦ ?_
    exact (sLocalAdelicThetaOnClasses_mk F S f x).symm.trans
      ((DFunLike.congr_fun h _).trans (sLocalAdelicThetaOnClasses_mk F S g x))

/-- Paper: Definition 5.1.1.1(3), p. 223.
The global zeta continuation vanishes for every test function with zero theta function.
Deviation: This is the compatibility field for the quotient lift in (5.1.1.4). -/
theorem globalIdelicMellin_vanishes_on_theta_kernel :
    LinearMap.ker theta𝔽 ≤ LinearMap.ker (globalIdelicMellin (F := F)) := by sorry

/-- Paper: Definition 5.1.1.1(3), p. 223.
The S-local zeta continuation vanishes for every test function with zero S-local theta function.
Deviation: This is the compatibility field for the quotient lift in (5.1.1.4). -/
theorem sLocalIdelicMellin_vanishes_on_theta_kernel :
    LinearMap.ker thetaₛ ≤ LinearMap.ker (sLocalIdelicMellin (F := F) (S := S)) := by sorry

/-- Paper: Definition 5.1.1.1(3), p. 223.
The Mellin transform of global theta functions is the map induced on the theta quotient. -/
def globalThetaMellin : GlobalAdelicThetaSpace F →ₗ[ℂ] ↥globalMeromorphic :=
  (LinearMap.ker theta𝔽).liftQ (globalIdelicMellin (F := F))
    (globalIdelicMellin_vanishes_on_theta_kernel (F := F))

/-- Paper: Definition 5.1.1.1(3), p. 223.
The global quotient transform recovers the test-function transform on every representative. -/
theorem globalThetaMellin_mk (f : ℬ𝔽) :
    globalThetaMellin (F := F) (Submodule.Quotient.mk f) =
      globalIdelicMellin (F := F) f := rfl

/-- Paper: Definition 5.1.1.1(3), p. 223.
The Mellin transform of S-local theta functions is the map induced on the theta quotient. -/
def sLocalThetaMellin : SLocalAdelicThetaSpace F S →ₗ[ℂ] ↥sLocalMeromorphic :=
  (LinearMap.ker thetaₛ).liftQ (sLocalIdelicMellin (F := F) (S := S))
    (sLocalIdelicMellin_vanishes_on_theta_kernel (F := F) (S := S))

/-- Paper: Definition 5.1.1.1(3), p. 223.
The S-local quotient transform recovers the test-function transform on every representative. -/
theorem sLocalThetaMellin_mk (f : ℬₛ) :
    sLocalThetaMellin (F := F) (S := S) (Submodule.Quotient.mk f) =
      sLocalIdelicMellin (F := F) (S := S) f := rfl

variable (F) in
/-- Paper: Definition 5.1.1.1(4), p. 223.
The global idelic Z-space is the linear range of the Mellin transform of global theta functions. -/
def GlobalIdelicZSpace := ↥(globalThetaMellin (F := F)).range

/-- Paper: Definition 5.1.1.1(4), p. 223.
Addition and negation on the global Z-space are inherited from the linear range. -/
instance : AddCommGroup (GlobalIdelicZSpace F) :=
  inferInstanceAs (AddCommGroup ↥(globalThetaMellin (F := F)).range)

/-- Paper: Definition 5.1.1.1(4), p. 223.
The global Z-space inherits complex scalar multiplication from the linear range. -/
instance : Module ℂ (GlobalIdelicZSpace F) :=
  inferInstanceAs (Module ℂ ↥(globalThetaMellin (F := F)).range)

/-- Paper: Definition 5.1.1.1(4), p. 223.
The global Z-space carries the topology transported from the theta quotient by the transform. -/
instance : TopologicalSpace (GlobalIdelicZSpace F) :=
  TopologicalSpace.coinduced (globalThetaMellin (F := F)).rangeRestrict inferInstance

/-- Paper: Definition 5.1.1.1(4), p. 223.
The Mellin transform as a linear map from the global theta space onto the global Z-space.
Statements about the topology of the Z-space must go through this map: `GlobalIdelicZSpace F`
unfolds to a range subtype, and a map whose codomain is written as that subtype is given the
subspace topology of compact convergence, not the transported topology of the paper. -/
def globalThetaToZ : GlobalAdelicThetaSpace F →ₗ[ℂ] GlobalIdelicZSpace F :=
  (globalThetaMellin (F := F)).rangeRestrict

/-- Paper: Definition 5.1.1.1(4), p. 223.
The map from the global theta space onto its Z-space is a quotient map. -/
theorem globalThetaToZ_isQuotientMap : IsQuotientMap (globalThetaToZ (F := F)) :=
  { eq_coinduced := rfl, surjective := LinearMap.surjective_rangeRestrict _ }

variable (F S) in
/-- Paper: Definition 5.1.1.1(4), p. 223.
The S-local idelic Z-space is the linear range of the Mellin transform of S-local theta functions. -/
def SLocalIdelicZSpace := ↥(sLocalThetaMellin (F := F) (S := S)).range

/-- Paper: Definition 5.1.1.1(4), p. 223.
Addition and negation on the S-local Z-space are inherited from the linear range. -/
instance : AddCommGroup (SLocalIdelicZSpace F S) :=
  inferInstanceAs (AddCommGroup ↥(sLocalThetaMellin (F := F) (S := S)).range)

/-- Paper: Definition 5.1.1.1(4), p. 223.
The S-local Z-space inherits complex scalar multiplication from the linear range. -/
instance : Module ℂ (SLocalIdelicZSpace F S) :=
  inferInstanceAs (Module ℂ ↥(sLocalThetaMellin (F := F) (S := S)).range)

/-- Paper: Definition 5.1.1.1(4), p. 223.
The S-local Z-space carries the topology transported from the theta quotient by the transform. -/
instance : TopologicalSpace (SLocalIdelicZSpace F S) :=
  TopologicalSpace.coinduced (sLocalThetaMellin (F := F) (S := S)).rangeRestrict inferInstance

/-- Paper: Definition 5.1.1.1(4), p. 223.
The Mellin transform as a linear map from the S-local theta space onto the S-local Z-space.
As for `globalThetaToZ`, statements about the topology of the Z-space must go through this map. -/
def sLocalThetaToZ : SLocalAdelicThetaSpace F S →ₗ[ℂ] SLocalIdelicZSpace F S :=
  (sLocalThetaMellin (F := F) (S := S)).rangeRestrict

/-- Paper: Definition 5.1.1.1(4), p. 223.
The map from the S-local theta space onto its Z-space is a quotient map. -/
theorem sLocalThetaToZ_isQuotientMap :
    IsQuotientMap (sLocalThetaToZ (F := F) (S := S)) :=
  { eq_coinduced := rfl, surjective := LinearMap.surjective_rangeRestrict _ }

/-- Paper: Remark 5.1.1.2, p. 223.
The global theta quotient is locally convex. -/
theorem globalAdelicThetaSpace_polynormable : PolynormableSpace ℂ (GlobalAdelicThetaSpace F) :=
  by sorry

/-- Paper: Remark 5.1.1.2, p. 223.
The S-local theta quotient is locally convex. -/
theorem sLocalAdelicThetaSpace_polynormable : PolynormableSpace ℂ (SLocalAdelicThetaSpace F S) :=
  by sorry

/-- Paper: Remark 5.1.1.2, p. 223.
The global theta quotient is Hausdorff if the global theta kernel is closed. -/
theorem globalAdelicThetaSpace_t2_of_isClosed
    (h : IsClosed (LinearMap.ker theta𝔽 : Set ℬ𝔽)) :
    T2Space (GlobalAdelicThetaSpace F) := by
  have : IsClosed (LinearMap.ker theta𝔽 : Set ℬ𝔽) := h
  infer_instance

/-- Paper: Remark 5.1.1.2, p. 223.
The S-local theta quotient is Hausdorff if the S-local theta kernel is closed. -/
theorem sLocalAdelicThetaSpace_t2_of_isClosed
    (h : IsClosed (LinearMap.ker thetaₛ : Set ℬₛ)) :
    T2Space (SLocalAdelicThetaSpace F S) := by
  have : IsClosed (LinearMap.ker thetaₛ : Set ℬₛ) := h
  infer_instance

/-- Paper: Theorem 5.1.1.3, p. 223.
The Mellin transform is injective on the global theta quotient. -/
theorem globalThetaMellin_injective : Injective (globalThetaMellin (F := F)) := by sorry

/-- Paper: Theorem 5.1.1.3, p. 223.
The Mellin transform is injective on the S-local theta quotient. -/
theorem sLocalThetaMellin_injective : Injective (sLocalThetaMellin (F := F) (S := S)) := by sorry

open scoped ENNReal in
/-- Point evaluation is continuous in the Schwartz–Bruhat topology since its
norm is bounded on each stage by the zeroth Schwartz seminorm. -/
private theorem schwartzBruhat_eval_continuous {G : Type*} [CommGroup G] [TopologicalSpace G]
    (x : G) : Continuous (fun f : SchwartzBruhat G ↦ f x) := by
  classical
  let L : SchwartzBruhat G →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let p := (normSeminorm ℂ ℂ).comp L
  have hstage (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
      Continuous (p ∘ schwartzBruhatStageInclusion a e) := by
    let _ := e.finiteGroup
    let q : Seminorm ℂ (SchwartzBruhatStage e) := elementarySchwartzSeminorm (0, 0, 0, 0)
    have hq : Continuous q := elementarySchwartz_withSeminorms.continuous_seminorm (0, 0, 0, 0)
    change Continuous (p.comp (schwartzBruhatStageInclusion a e))
    refine Seminorm.continuous_of_le hq ?_
    intro f
    change ‖schwartzBruhatStageRealization a e f x‖ ≤ q f
    rw [schwartzBruhatStageRealization_apply]
    split_ifs with hx
    · let y := Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩))
      change (‖f y‖₊ : ℝ≥0∞).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
      refine ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne ?_
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun z ↦ (‖f z‖₊ : ℝ≥0∞)) y
    · simpa only [norm_zero] using apply_nonneg q f
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦
    (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm ⟨p, hstage⟩

/-- At a fixed idele class, global theta is continuous in the test function. It is the
pointwise limit of the finite partial sums of point evaluations, and the global
Schwartz–Bruhat space is barrelled, so the Banach–Steinhaus theorem applies. -/
private theorem adelicTheta_eval_continuous (c : C𝔽) :
    Continuous (fun f : ℬ𝔽 ↦ adelicTheta f c) := by
  induction c using QuotientGroup.induction_on with | H g => ?_
  let : BarrelledSpace ℂ ℬ𝔽 := (adeleSchwartz_montel (F := F)).2.1
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable Fˣ := Units.val_injective.countable
  let pt (ξ : Fˣ) : Multiplicative 𝔸[F] :=
    Multiplicative.ofAdd (algebraMap F 𝔸[F] (ξ : F) * g.val)
  let ev (ξ : Fˣ) : ℬ𝔽 →L[ℂ] ℂ :=
    ⟨(LinearMap.proj (pt ξ)).comp (schwartzBruhatSubmodule _).subtype,
      schwartzBruhat_eval_continuous (pt ξ)⟩
  let L (s : Finset Fˣ) : ℬ𝔽 →L[ℂ] ℂ := ∑ ξ ∈ s, ev ξ
  have hL (s : Finset Fˣ) (f : ℬ𝔽) : L s f = ∑ ξ ∈ s, f (pt ξ) := by
    simp only [L, ContinuousLinearMap.coe_sum', Finset.sum_apply]
    rfl
  have hsum (f : ℬ𝔽) : HasSum (fun ξ ↦ f (pt ξ)) (adelicTheta f (QuotientGroup.mk g)) := by
    rw [adelicTheta_mk]
    refine Summable.hasSum ?_
    have hs := ((adelicAverage_summableUniformlyOn f {(g, 0)} isCompact_singleton).summable
      rfl).of_norm
    simpa only [add_zero, mul_comm g.val] using hs
  have hT : Filter.Tendsto (fun s f ↦ L s f) Filter.atTop
      (𝓝 fun f ↦ adelicTheta f (QuotientGroup.mk g)) :=
    tendsto_pi_nhds.mpr fun f ↦ by
      simp only [hL]
      exact hsum f
  exact (continuousLinearMapOfTendsto L hT).continuous

/-- Paper: Theorem 5.1.1.3(1), p. 224.
The global theta kernel is a closed subspace of the global Schwartz–Bruhat space. -/
theorem adelicTheta_ker_isClosed : IsClosed (LinearMap.ker theta𝔽 : Set ℬ𝔽) := by
  have hker : (⋂ c : C𝔽, (fun f : ℬ𝔽 ↦ adelicTheta f c) ⁻¹' {0}) =
      (LinearMap.ker theta𝔽 : Set ℬ𝔽) := by
    refine Set.ext fun f ↦ Set.mem_iInter.trans
      ((forall_congr' fun c ↦ Set.mem_singleton_iff).trans ?_)
    rw [SetLike.mem_coe, LinearMap.mem_ker, adelicThetaLinearMap_apply]
    exact ⟨fun h ↦ ContinuousMap.ext h, fun h c ↦ congrArg (fun φ : C(C𝔽, ℂ) ↦ φ c) h⟩
  exact (congrArg (IsClosed (X := ℬ𝔽)) hker).mp
    (isClosed_iInter fun c ↦ isClosed_singleton.preimage (adelicTheta_eval_continuous c))

/-- Paper: Theorem 5.1.1.3(1), p. 224.
The S-local theta kernel is a closed subspace of the S-local Schwartz–Bruhat space. -/
theorem sLocalAdelicTheta_ker_isClosed : IsClosed (LinearMap.ker thetaₛ : Set ℬₛ) := by sorry

local notation "homogeneousTheta𝔽" =>
  fun ω : PontryaginDual (MonoidHom.ker m𝔽) ↦
    IsLinearMap.mk' (homogeneousAdelicTheta (F := F) ω)
      (homogeneousAdelicTheta_isLinear (F := F) ω)

/-- Paper: Theorem 5.1.1.3(2), p. 224.
The kernel of global homogeneous theta at each norm-one character is closed. -/
theorem homogeneousAdelicTheta_ker_isClosed (ω : PontryaginDual (MonoidHom.ker m𝔽)) :
    IsClosed (LinearMap.ker (homogeneousTheta𝔽 ω) : Set ℬ𝔽) := by sorry

/-- Paper: Theorem 5.1.1.3(3), p. 224.
The norm-one S-idele quotient carries the Borel measurable structure used in §3.3. -/
local instance : MeasurableSpace (MonoidHom.ker mₛ) := borel _

/-- Paper: Theorem 5.1.1.3(3), p. 224.
The norm-one quotient Tamagawa measure of §3.3 is Haar. -/
local instance : Measure.IsHaarMeasure (sLocalNormOneQuotientMeasure F S) :=
  (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1

local notation "homogeneousThetaₛ" =>
  sLocalHomogeneousAdelicTheta F S (sLocalNormOneQuotientMeasure F S)

/-- Paper: Theorem 5.1.1.3(3), p. 224.
The kernel of S-local homogeneous theta at each norm-one character is closed. -/
theorem sLocalHomogeneousAdelicTheta_ker_isClosed (ω : PontryaginDual (MonoidHom.ker mₛ)) :
    IsClosed (LinearMap.ker (homogeneousThetaₛ ω) : Set ℬₛ) := by sorry

/-- Paper: Lemma 5.1.2.1(1), p. 224.
The kernels of the global zeta and global theta transforms agree. -/
theorem globalIdelicMellin_ker_eq :
    LinearMap.ker (globalIdelicMellin (F := F)) = LinearMap.ker theta𝔽 := by
  refine le_antisymm (fun f hf ↦ ?_) (globalIdelicMellin_vanishes_on_theta_kernel (F := F))
  have hinj : Injective (globalThetaMellin (F := F)) := globalThetaMellin_injective
  have h1 : globalThetaMellin (F := F) (Submodule.Quotient.mk f) = 0 :=
    (globalThetaMellin_mk f).trans (LinearMap.mem_ker.mp hf)
  have h2 : (Submodule.Quotient.mk f : GlobalAdelicThetaSpace F) = 0 :=
    hinj (h1.trans (map_zero (globalThetaMellin (F := F))).symm)
  exact (Submodule.Quotient.mk_eq_zero _).mp h2

/-- Paper: Lemma 5.1.2.1(2), p. 224.
Global homogeneous theta vanishes exactly when the global Z-function vanishes on
the component indexed by the same norm-one character.
Deviation: Vanishing of the meromorphic restriction is tested on the complement of the
allowed poles. -/
theorem mem_homogeneousAdelicTheta_ker_iff (ω : PontryaginDual (MonoidHom.ker m𝔽)) (f : ℬ𝔽) :
    f ∈ LinearMap.ker (homogeneousTheta𝔽 ω) ↔
      ∀ c : {c : X𝔽 // 0 ≤ globalIdelicOrderBound c},
        (∀ h : MonoidHom.ker m𝔽, normOneRestriction m𝔽 c.val h = (ω h : ℂ)) →
        (globalIdelicMellin (F := F) f).val c = 0 := by sorry

/-- Paper: Lemma 5.1.2.2(1), p. 225.
The kernels of the S-local zeta and S-local theta transforms agree. -/
theorem sLocalIdelicMellin_ker_eq :
    LinearMap.ker (sLocalIdelicMellin (F := F) (S := S)) = LinearMap.ker thetaₛ := by
  refine le_antisymm (fun f hf ↦ ?_)
    (sLocalIdelicMellin_vanishes_on_theta_kernel (F := F) (S := S))
  have hinj : Injective (sLocalThetaMellin (F := F) (S := S)) := sLocalThetaMellin_injective
  have h1 : sLocalThetaMellin (F := F) (S := S) (Submodule.Quotient.mk f) = 0 :=
    (sLocalThetaMellin_mk f).trans (LinearMap.mem_ker.mp hf)
  have h2 : (Submodule.Quotient.mk f : SLocalAdelicThetaSpace F S) = 0 :=
    hinj (h1.trans (map_zero (sLocalThetaMellin (F := F) (S := S))).symm)
  exact (Submodule.Quotient.mk_eq_zero _).mp h2

/-- Paper: Lemma 5.1.2.2(2), p. 225.
S-local homogeneous theta vanishes exactly when the S-local Z-function vanishes on
the component indexed by the same norm-one character.
Deviation: Vanishing of the meromorphic restriction is tested on the complement of the
allowed poles. -/
theorem mem_sLocalHomogeneousAdelicTheta_ker_iff (ω : PontryaginDual (MonoidHom.ker mₛ)) (f : ℬₛ) :
    f ∈ LinearMap.ker (homogeneousThetaₛ ω) ↔
      ∀ c : {c : Xₛ // 0 ≤ sLocalIdelicOrderBound c},
        (∀ h : MonoidHom.ker mₛ, normOneRestriction mₛ c.val h = (ω h : ℂ)) →
        (sLocalIdelicMellin (F := F) (S := S) f).val c = 0 := by sorry

/-- Paper: Lemma 5.1.3.1(1), p. 227.
The global idelic Mellin transform is continuous for compact convergence away from
the trivial and norm characters. -/
theorem globalIdelicMellin_continuous :
    Continuous (globalIdelicMellin (F := F)) := by sorry

/-- Paper: Lemma 5.1.3.1(1), p. 227.
Global Mellin evaluation at a regular character intertwines inverse left translation
with multiplication by that character on the class of the translating idele.
Deviation: Equality of the operators is stated by evaluation on every test function. -/
theorem globalIdelicMellin_unitTranslate (g : IdeleGroup (𝓞 F) F) (f : ℬ𝔽)
    (c : {c : X𝔽 // 0 ≤ globalIdelicOrderBound c}) :
    (globalIdelicMellin (F := F) (schwartzBruhatUnitTranslate g f)).val c =
      c.val (QuotientGroup.mk g) * (globalIdelicMellin (F := F) f).val c := by sorry

-- TODO(paper-gap): Lemma 5.1.3.1(2) calls D_S the divisor of rho_S, whereas its
-- prelude uses the divisor of L_S. The full divisor of rho_S has positive coefficients
-- at its zeros. These are not vanishing conditions on the image of the transform.

/-- Paper: Lemma 5.1.3.1(2), p. 227.
The S-local idelic Mellin transform is continuous for compact convergence away from
the poles of the correcting factor.
Deviation: The source is the S-local Schwartz–Bruhat space, as in the displayed map.
The target uses only the pole part of the divisor, as in §3.3.1. -/
theorem sLocalIdelicMellin_continuous :
    Continuous (sLocalIdelicMellin (F := F) (S := S)) := by sorry

/-- Paper: Lemma 5.1.3.1(2), p. 227.
S-local Mellin evaluation at a regular character intertwines inverse left translation
with multiplication by that character on the class of the translating S-idele.
Deviation: Equality of the operators is stated by evaluation on every test function. -/
theorem sLocalIdelicMellin_unitTranslate (g : (SAdeleRing F S)ˣ) (f : ℬₛ)
    (c : {c : Xₛ // 0 ≤ sLocalIdelicOrderBound c}) :
    (sLocalIdelicMellin (F := F) (S := S) (schwartzBruhatUnitTranslate g f)).val c =
      c.val (QuotientGroup.mk g) * (sLocalIdelicMellin (F := F) (S := S) f).val c := by sorry

-- TODO(paper-gap): The polar denominators in (5.1.3.3) have the wrong sign on i x₀.
-- If χ = |·|^(i x₀), the exponent of c is s + i x₀.

-- TODO(paper-gap): Footnote 1 on p. 230 asks for a version with an I-exponentially
-- decaying target but gives no statement.

end RiemannMasullo
