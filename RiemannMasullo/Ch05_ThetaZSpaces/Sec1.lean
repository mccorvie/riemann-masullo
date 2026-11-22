module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.UniformSpace.CompactConvergence
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.WithSeminorms

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
    IsLinearMap ℂ (globalZValues : ℬ𝔽 → _) := by
  classical
  let : T2Space C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  have hpos (g : C𝔽) : 0 < ((ideleClassNorm F g : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt _)
  have hne (g : C𝔽) : (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hpos g).ne'
  -- Every quasi-character lies on a norm-twist chart of a unitary character.
  have hdecomp (c : X𝔽) : ∃ (χ : PontryaginDual C𝔽) (s : ℂ), ideleClassNormTwist χ s = c := by
    let s := quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      (ideleClassNorm_ne_one (F := F)) c
    let d := c * ideleClassNormTwist (1 : PontryaginDual C𝔽) (-(s : ℂ))
    have hd (g : C𝔽) : ‖d g‖ = 1 := by
      change ‖c g * (1 * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (-(s : ℂ)))‖ = 1
      rw [one_mul, norm_mul, norm_quasiCharacter_eq_rpow_abscissa _
        (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F)),
        Complex.norm_cpow_eq_rpow_re_of_pos (hpos g), Complex.neg_re, Complex.ofReal_re]
      change ((ideleClassNorm F g : ℝ≥0) : ℝ) ^ s * ((ideleClassNorm F g : ℝ≥0) : ℝ) ^ (-s) = 1
      rw [← Real.rpow_add (hpos g), add_neg_cancel, Real.rpow_zero]
    let χ : PontryaginDual C𝔽 :=
      { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (hd g)⟩
        map_one' := Circle.ext (map_one d)
        map_mul' := fun g h ↦ Circle.ext (map_mul d g h)
        continuous_toFun := d.continuous.subtype_mk _ }
    refine ⟨χ, s, ?_⟩
    ext1 g
    change (c g * (1 * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (-(s : ℂ)))) *
      (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (s : ℂ) = c g
    rw [one_mul, mul_assoc, ← Complex.cpow_add _ _ (hne g), neg_add_cancel, Complex.cpow_zero,
      mul_one]
  -- The norm-twist chart centred at a point of such a chart is a translate of it.
  have hchart (χ : PontryaginDual C𝔽) (w z : ℂ) :
      normChart𝔽 (ideleClassNormTwist χ w) z = ideleClassNormTwist χ (w + z) := by
    ext1 g
    change ((χ g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ w) *
      (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ z =
        (χ g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (w + z)
    rw [Complex.cpow_add _ _ (hne g), mul_assoc]
  have habs (χ : PontryaginDual C𝔽) (s : ℂ) :
      quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
        (ideleClassNorm_ne_one (F := F)) (ideleClassNormTwist χ s) = s.re :=
    quasiCharacterAbscissa_ideleClassNormTwist χ s
  have habs₁ : quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      (ideleClassNorm_ne_one (F := F)) (1 : X𝔽) = 0 := by
    have := quasiCharacterAbscissa_of_unitary_twist (ideleClassNorm F)
      (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F)) (1 : X𝔽)
      (1 : PontryaginDual C𝔽) 0 (fun g ↦ by simp)
    simpa using this
  -- To the right of one every quasi-character is regular.
  have hregular (χ : PontryaginDual C𝔽) (w : ℂ) (hw : 1 < w.re) :
      0 ≤ globalIdelicOrderBound (ideleClassNormTwist χ w) := by
    have h₁ : ideleClassNormTwist χ w ≠ 1 := fun h ↦ by
      have := habs χ w
      rw [h, habs₁] at this
      linarith
    have h₂ : ideleClassNormTwist χ w ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) 1 :=
      fun h ↦ by
        have := habs χ w
        rw [h, habs] at this
        simp only [Complex.one_re] at this
        linarith
    simp [globalIdelicOrderBound, h₁, h₂]
  -- Linear relations between zeta integrals to the right of one persist at regular points.
  have key (f₁ f₂ f₃ : ℬ𝔽) (a b : ℂ)
      (hI : ∀ c : X𝔽, c ∈ (relativeRightHalfPlane (G := C𝔽) (ideleClassNorm F)
        (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F)) 1 : Set X𝔽) →
        globalIdelicZetaIntegral f₃ c =
          a * globalIdelicZetaIntegral f₁ c + b * globalIdelicZetaIntegral f₂ c)
      (c : X𝔽) (hc : 0 ≤ globalIdelicOrderBound c) :
      globalIdelicZFunction f₃ c =
        a * globalIdelicZFunction f₁ c + b * globalIdelicZFunction f₂ c := by
    obtain ⟨χ, s₀, rfl⟩ := hdecomp c
    obtain ⟨Z₁, hZ₁, h₁⟩ := globalIdelicZFunction_mem f₁
    obtain ⟨Z₂, hZ₂, h₂⟩ := globalIdelicZFunction_mem f₂
    obtain ⟨Z₃, hZ₃, h₃⟩ := globalIdelicZFunction_mem f₃
    have hM (Z : X𝔽 → ℂ)
        (hZ : ∀ c : X𝔽, MeromorphicAt (fun z ↦ Z (normChart𝔽 c z)) 0) (w : ℂ) :
        MeromorphicAt (fun w ↦ Z (ideleClassNormTwist χ w)) w := by
      have h := hZ (ideleClassNormTwist χ w)
      simp only [hchart] at h
      have h' : MeromorphicAt ((fun w ↦ Z (ideleClassNormTwist χ w)) ∘ (· + w)) 0 := by
        simpa only [Function.comp_def, add_comm] using h
      simpa using meromorphicAt_comp_add_const_iff_meromorphicAt.mp h'
    have hA (Z : X𝔽 → ℂ)
        (hZ : AnalyticAt ℂ (fun z ↦ Z (normChart𝔽 (ideleClassNormTwist χ s₀) z)) 0) :
        AnalyticAt ℂ (fun w ↦ Z (ideleClassNormTwist χ w)) s₀ := by
      simp only [hchart] at hZ
      have h := hZ.comp_of_eq
        (analyticAt_id.sub analyticAt_const : AnalyticAt ℂ (fun w : ℂ ↦ w - s₀) s₀)
        (sub_self s₀)
      simpa only [Function.comp_def, Pi.sub_apply, id_eq, add_sub_cancel] using h
    let D : ℂ → ℂ := fun w ↦ Z₃ (ideleClassNormTwist χ w) -
      (a * Z₁ (ideleClassNormTwist χ w) + b * Z₂ (ideleClassNormTwist χ w))
    have hDM : MeromorphicOn D Set.univ := fun w _ ↦
      (hM Z₃ (fun c ↦ (h₃ c).1) w).sub
        ((analyticAt_const.meromorphicAt.mul (hM Z₁ (fun c ↦ (h₁ c).1) w)).add
          (analyticAt_const.meromorphicAt.mul (hM Z₂ (fun c ↦ (h₂ c).1) w)))
    have hDA : AnalyticAt ℂ D s₀ :=
      (hA Z₃ ((h₃ _).2.2 hc)).sub ((analyticAt_const.mul (hA Z₁ ((h₁ _).2.2 hc))).add
        (analyticAt_const.mul (hA Z₂ ((h₂ _).2.2 hc))))
    have hval (Z : X𝔽 → ℂ) (f : ℬ𝔽) (hZ : ∀ c : {c : X𝔽 // 0 ≤ globalIdelicOrderBound c},
        Z c = globalZValues f c) (c : X𝔽) (hc : 0 ≤ globalIdelicOrderBound c) :
        Z c = globalIdelicZFunction f c :=
      hZ ⟨c, hc⟩
    have hEq (w : ℂ) (hw : 1 < w.re) : D w = 0 := by
      have hm : ideleClassNormTwist χ w ∈ (relativeRightHalfPlane (G := C𝔽) (ideleClassNorm F)
          (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F)) 1 : Set X𝔽) := by
        change 1 < quasiCharacterAbscissa _ _ _ _
        rwa [habs]
      have hr := hregular χ w hw
      simp only [D, hval Z₁ f₁ hZ₁ _ hr, hval Z₂ f₂ hZ₂ _ hr, hval Z₃ f₃ hZ₃ _ hr,
        globalIdelicZFunction_eq_integral _ hm, hI _ hm, sub_self]
    have hnear : ∀ᶠ z in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    have htop : meromorphicOrderAt D 2 = ⊤ :=
      meromorphicOrderAt_eq_top_iff.mpr ((hnear.mono hEq).filter_mono nhdsWithin_le_nhds)
    have ho := hDM.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ (2 : ℂ)) (Set.mem_univ s₀) htop
    have hloc : D =ᶠ[𝓝[≠] s₀] fun _ ↦ 0 := meromorphicOrderAt_eq_top_iff.mp ho
    have hD₀ : D s₀ = 0 :=
      tendsto_nhds_unique (hDA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (tendsto_const_nhds.congr' hloc.symm)
    rw [← hval Z₁ f₁ hZ₁ _ hc, ← hval Z₂ f₂ hZ₂ _ hc, ← hval Z₃ f₃ hZ₃ _ hc]
    exact sub_eq_zero.mp hD₀
  refine ⟨fun f g ↦ ?_, fun a f ↦ ?_⟩
  · ext c
    change globalIdelicZFunction (f + g) c.val =
      globalIdelicZFunction f c.val + globalIdelicZFunction g c.val
    have h := key f g (f + g) 1 1 (fun c hc ↦
      ((integral_congr_ae (Filter.Eventually.of_forall fun x ↦
        add_mul (f (Multiplicative.ofAdd x.val)) (g (Multiplicative.ofAdd x.val))
          (c (QuotientGroup.mk x)))).trans
        (integral_add (globalIdelicZetaIntegral_integrable f c hc)
          (globalIdelicZetaIntegral_integrable g c hc))).trans
        (congrArg₂ (· + ·) (one_mul _).symm (one_mul _).symm)) c.val c.property
    exact h.trans (congrArg₂ (· + ·) (one_mul _) (one_mul _))
  · ext c
    change globalIdelicZFunction (a • f) c.val = a * globalIdelicZFunction f c.val
    have h := key f f (a • f) a 0 (fun c hc ↦
      ((integral_congr_ae (Filter.Eventually.of_forall fun x ↦
        mul_assoc a (f (Multiplicative.ofAdd x.val)) (c (QuotientGroup.mk x)))).trans
        (integral_const_mul a _)).trans
        ((add_zero _).symm.trans (congrArg (_ + ·) (zero_mul _).symm))) c.val c.property
    exact h.trans ((congrArg (_ + ·) (zero_mul _)).trans (add_zero _))

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
    IsLinearMap ℂ (sLocalZValues : ℬₛ → _) := by
  classical
  let u : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  have : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  have hpos (g : Jₛ) : 0 < ((mₛ g : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hne (g : Jₛ) : (((mₛ g : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hpos g).ne'
  have hm : ∃ x, mₛ x ≠ 1 := by
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    exact ⟨σ t, (hσ t).trans_ne ht⟩
  -- Every quasi-character lies on a norm-twist chart of a unitary character.
  have hdecomp (c : Xₛ) : ∃ (χ : PontryaginDual Jₛ) (s : ℂ), normChartₛ (u.comp χ) s = c := by
    let s := quasiCharacterAbscissa (G := Jₛ) mₛ (isProperMap_sIdeleQuotientNorm F S) hm c
    let d := normChartₛ c (-(s : ℂ))
    have hd (g : Jₛ) : ‖d g‖ = 1 := by
      change ‖c g * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ (-(s : ℂ))‖ = 1
      rw [norm_mul, norm_quasiCharacter_eq_rpow_abscissa (G := Jₛ) mₛ
        (isProperMap_sIdeleQuotientNorm F S) hm,
        Complex.norm_cpow_eq_rpow_re_of_pos (hpos g), Complex.neg_re, Complex.ofReal_re]
      change ((mₛ g : ℝ≥0) : ℝ) ^ s * ((mₛ g : ℝ≥0) : ℝ) ^ (-s) = 1
      rw [← Real.rpow_add (hpos g), add_neg_cancel, Real.rpow_zero]
    let χ : PontryaginDual Jₛ :=
      { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (hd g)⟩
        map_one' := Circle.ext (map_one d)
        map_mul' := fun g h ↦ Circle.ext (map_mul d g h)
        continuous_toFun := d.continuous.subtype_mk _ }
    refine ⟨χ, s, ?_⟩
    ext1 g
    change (c g * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ (-(s : ℂ))) * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ (s : ℂ) =
      c g
    rw [mul_assoc, ← Complex.cpow_add _ _ (hne g), neg_add_cancel, Complex.cpow_zero, mul_one]
  -- The norm-twist chart centred at a point of a chart is a translate of it.
  have hchart (c : Xₛ) (w z : ℂ) : normChartₛ (normChartₛ c w) z = normChartₛ c (w + z) := by
    ext1 g
    change (c g * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ w) * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ z =
      c g * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ (w + z)
    rw [Complex.cpow_add _ _ (hne g), mul_assoc]
  -- Linear relations between zeta integrals on the positive half-plane persist at regular points.
  have key (f₁ f₂ f₃ : ℬₛ) (a b : ℂ)
      (hI : ∀ (χ : PontryaginDual Jₛ) (s : ℂ), 0 < s.re →
        sLocalIdelicZetaIntegral f₃ (normChartₛ (u.comp χ) s) =
          a * sLocalIdelicZetaIntegral f₁ (normChartₛ (u.comp χ) s) +
            b * sLocalIdelicZetaIntegral f₂ (normChartₛ (u.comp χ) s))
      (c : Xₛ) (hc : 0 ≤ sLocalIdelicOrderBound c) :
      sLocalIdelicZFunction f₃ c =
        a * sLocalIdelicZFunction f₁ c + b * sLocalIdelicZFunction f₂ c := by
    obtain ⟨χ, s₀, rfl⟩ := hdecomp c
    have hρ : 0 ≤ min 0 (meromorphicOrderAt
        (fun z ↦ sLocalRhoFactor (F := F) (S := S) (normChartₛ (u.comp χ) z)) s₀) := by
      have h := hc
      simp only [sLocalIdelicOrderBound, hchart] at h
      have e : meromorphicOrderAt
          (fun z ↦ sLocalRhoFactor (F := F) (S := S) (normChartₛ (u.comp χ) (s₀ + z))) 0 =
          meromorphicOrderAt
            (fun z ↦ sLocalRhoFactor (F := F) (S := S) (normChartₛ (u.comp χ) z)) s₀ := by
        have := meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (x := (0 : ℂ)) (c := s₀)
          (f := fun z ↦ sLocalRhoFactor (F := F) (S := S) (normChartₛ (u.comp χ) z))
        simpa only [Function.comp_def, add_comm, zero_add, add_zero] using this
      rwa [e] at h
    have hA (f : ℬₛ) :
        AnalyticAt ℂ (fun w ↦ sLocalIdelicZFunction f (normChartₛ (u.comp χ) w)) s₀ :=
      (sLocalIdelicZFunction_meromorphic f χ (Set.mem_univ s₀)
        ).meromorphicOrderAt_nonneg_iff_analyticAt.mp
          (hρ.trans (sLocalIdelicZFunction_poles f χ s₀))
    let D : ℂ → ℂ := fun w ↦ sLocalIdelicZFunction f₃ (normChartₛ (u.comp χ) w) -
      (a * sLocalIdelicZFunction f₁ (normChartₛ (u.comp χ) w) +
        b * sLocalIdelicZFunction f₂ (normChartₛ (u.comp χ) w))
    have hM (f : ℬₛ) (w : ℂ) :
        MeromorphicAt (fun w ↦ sLocalIdelicZFunction f (normChartₛ (u.comp χ) w)) w :=
      (sLocalIdelicZFunction_meromorphic f χ (Set.mem_univ w)).meromorphicAt
    have hDM : MeromorphicOn D Set.univ := fun w _ ↦
      (hM f₃ w).sub ((analyticAt_const.meromorphicAt.mul (hM f₁ w)).add
        (analyticAt_const.meromorphicAt.mul (hM f₂ w)))
    have hDA : AnalyticAt ℂ D s₀ :=
      (hA f₃).sub ((analyticAt_const.mul (hA f₁)).add (analyticAt_const.mul (hA f₂)))
    have hEq (w : ℂ) (hw : 0 < w.re) : D w = 0 := by
      have hp : normChartₛ (u.comp χ) w ∈ {c : Xₛ | ∃ (χ : PontryaginDual Jₛ) (s : ℂ),
          s ∈ Complex.re ⁻¹' Set.Ioi (0 : ℝ) ∧ c = normChartₛ (u.comp χ) s} :=
        ⟨χ, w, hw, rfl⟩
      simp only [D, sLocalIdelicZFunction_eq_integral _ hp, hI χ w hw, sub_self]
    have hnear : ∀ᶠ z in 𝓝 (1 : ℂ), 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    have htop : meromorphicOrderAt D 1 = ⊤ :=
      meromorphicOrderAt_eq_top_iff.mpr ((hnear.mono hEq).filter_mono nhdsWithin_le_nhds)
    have ho := hDM.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ (1 : ℂ)) (Set.mem_univ s₀) htop
    have hloc : D =ᶠ[𝓝[≠] s₀] fun _ ↦ 0 := meromorphicOrderAt_eq_top_iff.mp ho
    have hD₀ : D s₀ = 0 :=
      tendsto_nhds_unique (hDA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (tendsto_const_nhds.congr' hloc.symm)
    exact sub_eq_zero.mp hD₀
  refine ⟨fun f g ↦ ?_, fun a f ↦ ?_⟩
  · ext c
    change sLocalIdelicZFunction (f + g) c.val =
      sLocalIdelicZFunction f c.val + sLocalIdelicZFunction g c.val
    have h := key f g (f + g) 1 1 (fun χ s hs ↦
      ((integral_congr_ae (Filter.Eventually.of_forall fun x ↦
        add_mul (f (Multiplicative.ofAdd x.val)) (g (Multiplicative.ofAdd x.val))
          (normChartₛ (u.comp χ) s (QuotientGroup.mk x)))).trans
        (integral_add (sLocalIdelicZetaIntegral_integrable f _ ⟨χ, s, hs, rfl⟩)
          (sLocalIdelicZetaIntegral_integrable g _ ⟨χ, s, hs, rfl⟩))).trans
        (congrArg₂ (· + ·) (one_mul _).symm (one_mul _).symm)) c.val c.property
    exact h.trans (congrArg₂ (· + ·) (one_mul _) (one_mul _))
  · ext c
    change sLocalIdelicZFunction (a • f) c.val = a * sLocalIdelicZFunction f c.val
    have h := key f f (a • f) a 0 (fun χ s _ ↦
      ((integral_congr_ae (Filter.Eventually.of_forall fun x ↦
        mul_assoc a (f (Multiplicative.ofAdd x.val))
          (normChartₛ (u.comp χ) s (QuotientGroup.mk x)))).trans
        (integral_const_mul a _)).trans
        ((add_zero _).symm.trans (congrArg (_ + ·) (zero_mul _).symm))) c.val c.property
    exact h.trans ((congrArg (_ + ·) (zero_mul _)).trans (add_zero _))

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
  let : PolynormableSpace ℂ ℬ𝔽 := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  polynormableSpace_quotient _

/-- Paper: Remark 5.1.1.2, p. 223.
The S-local theta quotient is locally convex. -/
theorem sLocalAdelicThetaSpace_polynormable : PolynormableSpace ℂ (SLocalAdelicThetaSpace F S) :=
  let : PolynormableSpace ℂ ℬₛ := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  polynormableSpace_quotient _

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

/-- On a barrelled Schwartz–Bruhat space, a functional that is the sum of the values of
the test function at countably many points is continuous, by the Banach–Steinhaus theorem
applied to the finite partial sums of point evaluations. -/
private theorem schwartzBruhat_continuous_of_hasSum {G ι : Type*} [CommGroup G]
    [TopologicalSpace G] [Countable ι] [BarrelledSpace ℂ (SchwartzBruhat G)]
    (pt : ι → G) (φ : SchwartzBruhat G → ℂ)
    (h : ∀ f : SchwartzBruhat G, HasSum (fun i ↦ f (pt i)) (φ f)) :
    Continuous φ := by
  let ev (i : ι) : SchwartzBruhat G →L[ℂ] ℂ :=
    ⟨(LinearMap.proj (pt i)).comp (schwartzBruhatSubmodule _).subtype,
      schwartzBruhat_eval_continuous (pt i)⟩
  let L (s : Finset ι) : SchwartzBruhat G →L[ℂ] ℂ := ∑ i ∈ s, ev i
  have hL (s : Finset ι) (f : SchwartzBruhat G) : L s f = ∑ i ∈ s, f (pt i) := by
    simp only [L, ContinuousLinearMap.coe_sum', Finset.sum_apply]
    rfl
  have hT : Filter.Tendsto (fun s f ↦ L s f) Filter.atTop (𝓝 φ) :=
    tendsto_pi_nhds.mpr fun f ↦ by
      simp only [hL]
      exact h f
  exact (continuousLinearMapOfTendsto L hT).continuous

/-- Paper: Theorem 5.1.1.3(1), p. 224.
The S-local theta kernel is a closed subspace of the S-local Schwartz–Bruhat space. -/
theorem sLocalAdelicTheta_ker_isClosed : IsClosed (LinearMap.ker thetaₛ : Set ℬₛ) := by
  let : BarrelledSpace ℂ ℬₛ := (sAdeleSchwartz_montel (F := F) S).1
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ :=
    Units.val_injective.countable
  have hcont (g : (SAdeleRing F S)ˣ) : Continuous (fun f : ℬₛ ↦ thetaₛ f g) :=
    schwartzBruhat_continuous_of_hasSum _ _ fun f ↦
      (sLocalAdelicTheta_hasSumUniformlyOn F S f {g} isCompact_singleton).hasSum rfl
  have hker : (⋂ g : (SAdeleRing F S)ˣ, (fun f : ℬₛ ↦ thetaₛ f g) ⁻¹' {0}) =
      (LinearMap.ker thetaₛ : Set ℬₛ) := by
    refine Set.ext fun f ↦ Set.mem_iInter.trans
      ((forall_congr' fun g ↦ Set.mem_singleton_iff).trans
        (Iff.trans ?_ (SetLike.mem_coe.trans LinearMap.mem_ker).symm))
    exact ⟨fun h ↦ ContinuousMap.ext h,
      fun h g ↦ congrArg (fun φ : C((SAdeleRing F S)ˣ, ℂ) ↦ φ g) h⟩
  exact (congrArg (IsClosed (X := ℬₛ)) hker).mp
    (isClosed_iInter fun g ↦ isClosed_singleton.preimage (hcont g))

/-- On a barrelled space, the integral over a compact space against a finite measure of
a family of continuous linear functionals is continuous if each test vector gives a
continuous function of the parameter. The pointwise supremum of the absolute values of
the functionals is then a continuous seminorm, and the integral is bounded by the
total mass times this seminorm. -/
private theorem continuous_integral_of_continuous_eval {E H : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul ℂ E]
    [BarrelledSpace ℂ E] [TopologicalSpace H] [CompactSpace H] {m : MeasurableSpace H}
    (μ : Measure H) [IsFiniteMeasure μ]
    (Φ : E → H → ℂ) (hlin : ∀ h, IsLinearMap ℂ fun f ↦ Φ f h)
    (hE : ∀ h, Continuous fun f ↦ Φ f h) (hH : ∀ f, Continuous (Φ f))
    (hint : ∀ f, Integrable (Φ f) μ) : Continuous fun f ↦ ∫ h, Φ f h ∂μ := by
  let p (h : H) : Seminorm ℂ E := (normSeminorm ℂ ℂ).comp (IsLinearMap.mk' _ (hlin h))
  have hp (h : H) : Continuous (p h) := continuous_norm.comp (hE h)
  have hpt (f : E) : BddAbove (Set.range fun h ↦ p h f) :=
    (isCompact_range (hH f).norm).bddAbove
  have hbdd : BddAbove (Set.range p) := Seminorm.bddAbove_range_iff.mpr hpt
  have hsup : Continuous (⨆ h, p h : Seminorm ℂ E) :=
    (congrArg Continuous (Seminorm.coe_iSup_eq hbdd)).mpr (Seminorm.continuous_iSup p hp hbdd)
  let I : E →ₗ[ℂ] ℂ := IsLinearMap.mk' (fun f ↦ ∫ h, Φ f h ∂μ)
    ⟨fun f f' ↦ (integral_congr_ae (.of_forall fun h ↦ (hlin h).map_add f f')).trans
        (integral_add (hint f) (hint f')),
      fun c f ↦ (integral_congr_ae (.of_forall fun h ↦ (hlin h).map_smul c f)).trans
        (integral_smul c _)⟩
  have hq : Continuous ((μ Set.univ).toNNReal • ⨆ h, p h : Seminorm ℂ E) :=
    hsup.const_smul _
  refine (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp I fun _ ↦
    Seminorm.continuous_of_le hq fun f ↦ ?_
  have hle (h : H) : ‖Φ f h‖ ≤ (⨆ h, p h) f := by
    rw [Seminorm.coe_iSup_eq hbdd, iSup_apply]
    exact le_ciSup (hpt f) h
  exact (norm_integral_le_of_norm_le_const (.of_forall hle)).trans_eq
    (mul_comm _ ((μ Set.univ).toNNReal : ℝ))

local notation "homogeneousTheta𝔽" =>
  fun ω : PontryaginDual (MonoidHom.ker m𝔽) ↦
    IsLinearMap.mk' (homogeneousAdelicTheta (F := F) ω)
      (homogeneousAdelicTheta_isLinear (F := F) ω)

/-- Paper: Theorem 5.1.1.3(2), p. 224.
The kernel of global homogeneous theta at each norm-one character is closed. -/
theorem homogeneousAdelicTheta_ker_isClosed (ω : PontryaginDual (MonoidHom.ker m𝔽)) :
    IsClosed (LinearMap.ker (homogeneousTheta𝔽 ω) : Set ℬ𝔽) := by
  let : BarrelledSpace ℂ ℬ𝔽 := (adeleSchwartz_montel (F := F)).2.1
  let : MeasurableSpace C𝔽 := borel _
  let : CompactSpace (MonoidHom.ker m𝔽) := (ideleClassGroup_finiteness F).2.1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hθ := adelicTheta_isLinear (F := F)
  have hlin (c : C𝔽) : IsLinearMap ℂ fun f : ℬ𝔽 ↦ adelicTheta f c :=
    ⟨fun f f' ↦ congrArg (fun φ : C(C𝔽, ℂ) ↦ φ c) (hθ.map_add f f'),
      fun a f ↦ congrArg (fun φ : C(C𝔽, ℂ) ↦ φ c) (hθ.map_smul a f)⟩
  have hcont (g : C𝔽) : Continuous (fun f : ℬ𝔽 ↦ homogeneousAdelicTheta ω f g) :=
    continuous_integral_of_continuous_eval (normOneIdeleClassTamagawaMeasure F)
      (fun f h ↦ adelicTheta f (h.val * g) * (ω h : ℂ))
      (fun h ↦ ⟨fun f f' ↦ (congrArg (· * (ω h : ℂ)) ((hlin _).map_add f f')).trans
          (add_mul _ _ _),
        fun a f ↦ (congrArg (· * (ω h : ℂ)) ((hlin _).map_smul a f)).trans
          (smul_mul_assoc _ _ _)⟩)
      (fun h ↦ (adelicTheta_eval_continuous (h.val * g)).mul continuous_const)
      (fun f ↦ ((adelicTheta f).continuous.comp
        (continuous_subtype_val.mul continuous_const)).mul
          (continuous_subtype_val.comp ω.continuous))
      (fun f ↦ homogeneousAdelicTheta_integrable ω f g)
  have hker : (⋂ g : C𝔽, (fun f : ℬ𝔽 ↦ homogeneousAdelicTheta ω f g) ⁻¹' {0}) =
      (LinearMap.ker (homogeneousTheta𝔽 ω) : Set ℬ𝔽) := by
    refine Set.ext fun f ↦ Set.mem_iInter.trans
      ((forall_congr' fun g ↦ Set.mem_singleton_iff).trans
        (Iff.trans ?_ (SetLike.mem_coe.trans LinearMap.mem_ker).symm))
    exact ⟨fun h ↦ ContinuousMap.ext h, fun h g ↦ congrArg (fun φ : C(C𝔽, ℂ) ↦ φ g) h⟩
  exact (congrArg (IsClosed (X := ℬ𝔽)) hker).mp
    (isClosed_iInter fun g ↦ isClosed_singleton.preimage (hcont g))

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
    IsClosed (LinearMap.ker (homogeneousThetaₛ ω) : Set ℬₛ) := by
  let : BarrelledSpace ℂ ℬₛ := (sAdeleSchwartz_montel (F := F) S).1
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ :=
    Units.val_injective.countable
  have : CompactSpace (MonoidHom.ker mₛ) := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  have hθ (c : Jₛ) : IsLinearMap ℂ (fun f : ℬₛ ↦ sLocalAdelicThetaOnClasses F S f c) ∧
      Continuous (fun f : ℬₛ ↦ sLocalAdelicThetaOnClasses F S f c) := by
    induction c using QuotientGroup.induction_on with | H x => ?_
    simp only [sLocalAdelicThetaOnClasses_mk]
    exact ⟨⟨fun f f' ↦ congrArg (fun φ : C((SAdeleRing F S)ˣ, ℂ) ↦ φ x) (map_add thetaₛ f f'),
        fun a f ↦ congrArg (fun φ : C((SAdeleRing F S)ˣ, ℂ) ↦ φ x) (map_smul thetaₛ a f)⟩,
      schwartzBruhat_continuous_of_hasSum _ _ fun f ↦
        (sLocalAdelicTheta_hasSumUniformlyOn F S f {x} isCompact_singleton).hasSum rfl⟩
  have hcont (g : Jₛ) : Continuous (fun f : ℬₛ ↦ homogeneousThetaₛ ω f g) :=
    continuous_integral_of_continuous_eval (sLocalNormOneQuotientMeasure F S)
      (fun f h ↦ sLocalAdelicThetaOnClasses F S f (g * h.val) * (ω h : ℂ))
      (fun h ↦ ⟨fun f f' ↦ (congrArg (· * (ω h : ℂ)) ((hθ _).1.map_add f f')).trans
          (add_mul _ _ _),
        fun a f ↦ (congrArg (· * (ω h : ℂ)) ((hθ _).1.map_smul a f)).trans
          (smul_mul_assoc _ _ _)⟩)
      (fun h ↦ (hθ _).2.mul continuous_const)
      (fun f ↦ ((sLocalAdelicThetaOnClasses F S f).continuous.comp
        (continuous_const.mul continuous_subtype_val)).mul
          (continuous_subtype_val.comp ω.continuous))
      (fun f ↦ sLocalHomogeneousAdelicTheta_integrable F S _ ω f g)
  have hker : (⋂ g : Jₛ, (fun f : ℬₛ ↦ homogeneousThetaₛ ω f g) ⁻¹' {0}) =
      (LinearMap.ker (homogeneousThetaₛ ω) : Set ℬₛ) := by
    refine Set.ext fun f ↦ Set.mem_iInter.trans
      ((forall_congr' fun g ↦ Set.mem_singleton_iff).trans
        (Iff.trans ?_ (SetLike.mem_coe.trans LinearMap.mem_ker).symm))
    exact ⟨fun h ↦ ContinuousMap.ext h, fun h g ↦ congrArg (fun φ : C(Jₛ, ℂ) ↦ φ g) h⟩
  exact (congrArg (IsClosed (X := ℬₛ)) hker).mp
    (isClosed_iInter fun g ↦ isClosed_singleton.preimage (hcont g))

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
