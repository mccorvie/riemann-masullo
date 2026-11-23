module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec4
public import RiemannMasullo.Ch06_LocalGlobal.Sec3
public import RiemannMasullo.Ch09_HardySobolev.Sec3

import all RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.Ch02_AdelicTheta.Sec3
import all RiemannMasullo.Ch02_AdelicTheta.Sec2b

import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Hardy–Sobolev topologies on adelic theta spaces

Masullo, §10.1, pp. 434–438. The parameter S indexes the finite places, with all
archimedean places included. Compact nonempty intervals are given by ordered endpoints.
The ambient weighted L² spaces here use full quotient Tamagawa measure, as in (10.1.1.5).
The comparison maps below give the change of norm to the canonical spaces of §9.2.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Jₛ" => SIdeleQuotient F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "C₁" => (ideleClassNorm F).ker
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "μₛ" => sLocalQuotientTamagawaMeasure F S
local notation "μ𝔽₁" => normOneIdeleClassTamagawaMeasure F
local notation "μₛ₁" => sLocalNormOneQuotientMeasure F S

-- These are the Borel structures used when defining the Tamagawa measures.
local instance instIdeleClassMeasurableSpaceSec1 : MeasurableSpace C𝔽 := borel _
local instance instSIdeleQuotientMeasurableSpaceSec1 : MeasurableSpace Jₛ := borel _
local instance instNormOneSIdeleQuotientMeasurableSpaceSec1 : MeasurableSpace J₁ := borel _
local instance instSAdeleMeasurableSpaceSec1 : MeasurableSpace (SAdeleRing F S) :=
  instMeasurableSpaceSAdeleRing F S

local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "mₛ" =>
  (⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ :
    Jₛ →ₜ* ℝ≥0ˣ)
local notation "logNorm(" m ")" => (fun g ↦ Real.log (((m) g).val : ℝ))
local notation "W𝔽(" α ", " β ", " s ")" => CompactIntervalSobolev μ𝔽 (logNorm(m𝔽)) α β s
local notation "Wₛ(" α ", " β ", " s ")" => CompactIntervalSobolev μₛ (logNorm(mₛ)) α β s
local notation "Θₛ" => SLocalAdelicThetaSpace F S
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "ℬ₀" => ↥(adelePolarSubspace F)
local notation "Θ₀" => GlobalPolarFreeThetaSpace F
local notation "θ𝔽(" f ")" => adelicTheta (f : ℬ₀).val
local notation "θₛ(" f ")" => sLocalAdelicThetaOnClasses F S f
local notation "ρₛ" => (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose

/-- Paper: (10.1.1.1), p. 434. Weighted global polar-free theta functions are
continuous and have continuous derivatives of every order along every continuous
real one-parameter subgroup. The function realization is injective. -/
theorem globalPolarFreeTheta_directionallySmooth (a : ℝ) :
    ∃ E : Θ₀ →ₗ[ℂ] (C𝔽 → ℂ), Injective E ∧
      (∀ f : ℬ₀, E (Submodule.Quotient.mk f) = modulationWeight m𝔽 a (θ𝔽(f))) ∧
      ∀ u : Θ₀, Continuous (E u) ∧
        ∀ γ : Multiplicative ℝ →ₜ* C𝔽,
          (∀ (g : C𝔽) (k : ℕ), ContDiff ℝ k (fun t : ℝ ↦ E u (γ (Multiplicative.ofAdd t) * g))) ∧
          ∀ n : ℕ, Continuous (fun g : C𝔽 ↦
            iteratedDeriv n (fun t : ℝ ↦ E u (γ (Multiplicative.ofAdd t) * g)) 0) := by sorry

-- TODO(paper-gap): The assertion preceding (10.1.1.2) on p. 434 and the open
-- half-line on p. 435 require care. Every compact subinterval gives a finite norm.
-- The supremum over an unbounded interval can be infinite on a single theta test.

/-- Paper: (10.1.1.2), p. 434. Weighting the global polar-free theta function
gives a continuous injection into the compact-interval Sobolev space. -/
theorem existsUnique_globalThetaSobolevEmbedding (a α β s : ℝ) (_hI : α ≤ β) (_hs : 0 ≤ s) :
    ∃! E : Θ₀ →L[ℂ] W𝔽(α, β, s), Injective E ∧
      ∀ f : ℬ₀, (E (Submodule.Quotient.mk f) : C𝔽 → ℂ) =ᵐ[μ𝔽]
        modulationWeight m𝔽 a (θ𝔽(f)) := by sorry

local notation "E𝔽(" a ", " hI ", " hs ")" =>
  (existsUnique_globalThetaSobolevEmbedding (F := F) a _ _ _ hI hs).exists.choose

variable (F) in
/-- Paper: Definition 10.1.1.1(1), p. 434. Take the closure of the weighted
polar-free theta image in the compact-interval Sobolev space of idele classes. -/
abbrev globalThetaSobolev (a : ℝ) {α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s) :
    Submodule ℂ W𝔽(α, β, s) :=
  (E𝔽(a, hI, hs).toLinearMap.range).topologicalClosure

local notation "H𝔽(" a ", " hI ", " hs ")" => globalThetaSobolev F a hI hs

-- TODO(paper-gap): (10.1.1.5) requires a + α > 0. For ℚ with only the real place,
-- the Gaussian has theta value tending to 2 at norm zero, giving divergence at a + α = 0.

/-- Paper: Definition 10.1.1.1(2), p. 434. The weighted S-local theta embedding
sends a class to the almost-everywhere class of its weighted theta function.
Deviation: The smallest effective exponent a + α must be strictly positive. -/
theorem existsUnique_sLocalThetaSobolevEmbedding (a α β s : ℝ) (_ha : 0 < a)
    (_hI : α ≤ β) (_hs : 0 ≤ s) (_hpos : 0 < a + α) :
    ∃! E : Θₛ →L[ℂ] Wₛ(α, β, s), Injective E ∧
      ∀ f : ℬₛ, (E (Submodule.Quotient.mk f) : Jₛ → ℂ) =ᵐ[μₛ]
        modulationWeight mₛ a (θₛ(f)) := by sorry

local notation "Eₛ(" ha ", " hI ", " hs ", " hp ")" =>
  (existsUnique_sLocalThetaSobolevEmbedding (F := F) (S := S) _ _ _ _ ha hI hs hp).exists.choose

variable (F S) in
/-- Paper: Definition 10.1.1.1(2), p. 434. The local norm completion is the
closure of the weighted theta image in the compact-interval Sobolev space.
Deviation: Require a + α > 0 for the norm to be finite. The closure model
uses quotient Haar measure, as in (10.1.1.5). -/
abbrev sLocalThetaSobolev {a α β s : ℝ} (ha : 0 < a) (hI : α ≤ β) (hs : 0 ≤ s)
    (hp : 0 < a + α) : Submodule ℂ Wₛ(α, β, s) :=
  (Eₛ(ha, hI, hs, hp).toLinearMap.range).topologicalClosure

local notation "Hₛ(" ha ", " hI ", " hs ", " hp ")" =>
  sLocalThetaSobolev F S ha hI hs hp
variable (F) in
/-- Paper: (10.1.2.3), p. 437. The global completion map sends a theta class to the
class of its norm-weighted theta function in the closed theta subspace. -/
def globalThetaSobolevInclusion (a : ℝ) {α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s) :
    Θ₀ →L[ℂ] H𝔽(a, hI, hs) :=
  (E𝔽(a, hI, hs)).codRestrict (H𝔽(a, hI, hs))
    (fun u ↦ Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ u))

variable (F S) in
/-- Paper: Definition 10.1.1.1(2), p. 434. The local completion map realizes a
theta class as its weighted theta function in the closed local theta subspace.
Deviation: The smallest effective exponent a + α is strictly positive. -/
def sLocalThetaSobolevInclusion {a α β s : ℝ} (ha : 0 < a) (hI : α ≤ β)
    (hs : 0 ≤ s) (hp : 0 < a + α) : Θₛ →L[ℂ] Hₛ(ha, hI, hs, hp) :=
  (Eₛ(ha, hI, hs, hp)).codRestrict (Hₛ(ha, hI, hs, hp))
    (fun u ↦ Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ u))

local notation "j𝔽(" a ", " hI ", " hs ")" => globalThetaSobolevInclusion F a hI hs
local notation "jₛ(" ha ", " hI ", " hs ", " hp ")" => sLocalThetaSobolevInclusion F S ha hI hs hp

/-- Paper: Definition 10.1.1.1, p. 434. The weighted test-class embeddings have
dense image in their respective completions.
Deviation: Sanity checks for the closure models. -/
theorem globalThetaSobolev_dense (a : ℝ) {α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s) :
    DenseRange (j𝔽(a, hI, hs)) := by
  intro x
  apply closure_subtype.mpr
  rw [← Set.range_comp]
  exact x.property

/-- Paper: Definition 10.1.1.1(2), p. 434. The weighted S-local test classes are
dense in the local Sobolev completion.
Deviation: Sanity check for the closure model at the admissible exponents. -/
theorem sLocalThetaSobolev_dense {a α β s : ℝ} (ha : 0 < a) (hI : α ≤ β)
    (hs : 0 ≤ s) (hp : 0 < a + α) :
    DenseRange (jₛ(ha, hI, hs, hp)) := by
  intro x
  have hr : Set.range (Eₛ(ha, hI, hs, hp)) =
      Subtype.val '' Set.range (jₛ(ha, hI, hs, hp)) :=
    Set.range_comp (Subtype.val : Hₛ(ha, hI, hs, hp) → Wₛ(α, β, s)) (jₛ(ha, hI, hs, hp))
  apply closure_subtype.mpr
  exact (congrArg (fun R : Set Wₛ(α, β, s) ↦ x.val ∈ closure R) hr).mp x.property

/-- Paper: Remark 10.1.1.2, pp. 434–435. The original S-local left action
extends jointly continuously to the norm completion via the completion map.
Deviation: The smallest effective exponent a + α is strictly positive. -/
theorem exists_sLocalThetaSobolevUnweightedAction {a α β s : ℝ} (ha : 0 < a)
    (hI : α ≤ β) (hs : 0 ≤ s) (hp : 0 < a + α) :
    ∃ ρ : Jₛ →* (Hₛ(ha, hI, hs, hp) →L[ℂ] Hₛ(ha, hI, hs, hp)),
      Continuous (fun p : Jₛ × Hₛ(ha, hI, hs, hp) ↦ ρ p.1 p.2) ∧
      ∀ (g : Jₛ) (u : Θₛ), ρ g (jₛ(ha, hI, hs, hp) u) = jₛ(ha, hI, hs, hp) (ρₛ g u) :=
  by sorry

/-- The modulation weight shifts the interval of the Sobolev density. -/
private theorem globalThetaSobolev_norm_density (a α β s l : ℝ) :
    Real.exp (a * l) ^ 2 * intervalSobolevDensity α β s l =
      intervalSobolevDensity (a + α) (a + β) s l := by
  unfold intervalSobolevDensity
  rw [← mul_assoc, mul_max_of_nonneg _ _ (by positivity), ← Real.exp_nat_mul,
    ← Real.exp_add, ← Real.exp_add]
  congr 3 <;> push_cast <;> ring

/-- The norm of a weighted L² class represented by a weighted function, on an abstract
measure space. -/
private theorem globalThetaSobolev_norm_aux {G : Type*} [MeasurableSpace G] (μ : Measure G)
    (r : G → ℝ) (hr : ∀ g, 0 < r g) (hrm : Measurable r) (a α β s : ℝ) (φ : G → ℂ)
    (u : CompactIntervalSobolev μ (fun g ↦ Real.log (r g)) α β s)
    (hu : (u : G → ℂ) =ᵐ[μ] fun g ↦ ((r g ^ a : ℝ) : ℂ) * φ g) :
    let w := fun g : G ↦ ‖φ g‖ ^ 2 * intervalSobolevDensity (a + α) (a + β) s (Real.log (r g))
    Integrable w μ ∧ ‖u‖ = Real.sqrt (∫ g, w g ∂μ) := by
  intro w
  set d : G → ℝ := fun g ↦ intervalSobolevDensity α β s (Real.log (r g)) with hd_def
  have hd0 (g : G) : 0 ≤ d g := by
    simp only [d, intervalSobolevDensity]
    exact mul_nonneg ((Real.exp_pos _).le.trans (le_max_left _ _)) (by positivity)
  have hdm : Measurable d := by
    simp only [d, intervalSobolevDensity]
    fun_prop
  have hdm' : Measurable fun g ↦ ENNReal.ofReal (d g) := ENNReal.measurable_ofReal.comp hdm
  have hlt : ∀ᵐ g ∂μ, ENNReal.ofReal (d g) < ⊤ := .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hpt : (fun g ↦ ENNReal.toReal (ENNReal.ofReal (d g)) • ‖(u : G → ℂ) g‖ ^ 2) =ᵐ[μ] w := by
    filter_upwards [hu] with g hg
    rw [hg, ENNReal.toReal_ofReal (hd0 g), smul_eq_mul, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (hr g).le _), Real.rpow_def_of_pos (hr g),
      mul_comm (Real.log (r g)) a]
    simp only [w, d]
    rw [← globalThetaSobolev_norm_density a α β s]
    ring
  have hint : Integrable (fun g ↦ ‖(u : G → ℂ) g‖ ^ 2)
      (μ.withDensity fun g ↦ ENNReal.ofReal (d g)) :=
    (Lp.memLp u).integrable_norm_pow two_ne_zero
  have hw : Integrable w μ :=
    ((integrable_withDensity_iff_integrable_smul' hdm' hlt).mp hint).congr hpt
  refine ⟨hw, ?_⟩
  have hsq : ‖u‖ ^ 2 = ∫ g, ‖(u : G → ℂ) g‖ ^ 2 ∂(μ.withDensity fun g ↦ ENNReal.ofReal (d g)) := by
    rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
    simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
    rw [integral_ofReal, RCLike.ofReal_re]
    rfl
  rw [← Real.sqrt_sq (norm_nonneg u), hsq,
    integral_withDensity_eq_integral_toReal_smul hdm' hlt, integral_congr_ae hpt]

/-- Paper: Lemma 10.1.1.3, p. 435. The continuous weighted embedding pulls
the ambient norm back to the norm in (10.1.1.6).
Deviation: Use the Haar measure on the full idele class group, denoted μ̄ in Appendix A.3. -/
theorem globalThetaSobolev_norm (a : ℝ) {α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s) (f : ℬ₀) :
    let w := fun g : C𝔽 ↦ ‖θ𝔽(f) g‖ ^ 2 *
      intervalSobolevDensity (a + α) (a + β) s (logNorm(m𝔽) g)
    Integrable w μ𝔽 ∧ ‖E𝔽(a, hI, hs) (Submodule.Quotient.mk f)‖ =
      Real.sqrt (∫ g, w g ∂μ𝔽) := by
  have hE := (existsUnique_globalThetaSobolevEmbedding (F := F) a α β s hI hs).exists.choose_spec.2 f
  have : BorelSpace C𝔽 := ⟨rfl⟩
  exact globalThetaSobolev_norm_aux μ𝔽 (fun g ↦ ((m𝔽 g).val : ℝ))
    (fun g ↦ NNReal.coe_pos.mpr (Units.zero_lt _))
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).measurable
    a α β s _ _ hE

/-- Paper: Lemma 10.1.1.3(1), p. 435. The global completion is a closed,
complete and separable subspace of the ambient Hilbert space. -/
theorem globalThetaSobolev_closed_complete_separable (a : ℝ) {α β s : ℝ}
    (hI : α ≤ β) (hs : 0 ≤ s) :
    IsClosed (H𝔽(a, hI, hs) : Set W𝔽(α, β, s)) ∧
      CompleteSpace (H𝔽(a, hI, hs)) ∧ TopologicalSpace.SeparableSpace (H𝔽(a, hI, hs)) := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : T2Space C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  let : SecondCountableTopology C𝔽 := by
    let := idele_secondCountable F
    exact inferInstanceAs (SecondCountableTopology
      (IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))
  let : (ideleClassTamagawaMeasure F).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have hc : IsClosed (H𝔽(a, hI, hs) : Set W𝔽(α, β, s)) :=
    Submodule.isClosed_topologicalClosure _
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology W𝔽(α, β, s) := Lp.SecondCountableTopology
  exact ⟨hc, hc.completeSpace_coe, inferInstance⟩

local instance instIdeleClassBorelSpaceSec1 : BorelSpace C𝔽 := ⟨rfl⟩
local instance instSIdeleQuotientBorelSpaceSec1 : BorelSpace Jₛ := ⟨rfl⟩
local instance instIdeleClassT2Sec1 : T2Space C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
local instance instIdeleClassLocallyCompactSec1 : LocallyCompactSpace C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
local instance instIdeleClassSecondCountableSec1 : SecondCountableTopology C𝔽 :=
  letI := idele_secondCountable F
  inferInstanceAs (SecondCountableTopology
    (IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))

local instance instSIdeleLocallyCompactSec1 : LocallyCompactSpace Iₛ :=
  (sIdeleGroup_description F S).2.2.1

set_option maxSynthPendingDepth 8 in
local instance instSIdeleSecondCountableSec1 : SecondCountableTopology Iₛ := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (v : S) : SecondCountableTopology (v.val.adicCompletion F) := secondCountable_of_proper
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology (InfiniteAdeleRing F) := inferInstanceAs
    (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))
  let : SecondCountableTopology ((v : S) → v.val.adicCompletion F) := inferInstance
  let : SecondCountableTopology (SAdeleRing F S) := inferInstanceAs
    (SecondCountableTopology (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  exact (sIdeleGroup_description F S).1.secondCountableTopology

local instance instSIdeleQuotientT2Sec1 : T2Space Jₛ :=
  letI := isClosed_sProjectedDiagonal (F := F) (S := S)
  inferInstance

local instance instSIdeleQuotientLocallyCompactSec1 : LocallyCompactSpace Jₛ :=
  inferInstanceAs (LocallyCompactSpace (Iₛ ⧸ _))

local instance instSIdeleQuotientSecondCountableSec1 : SecondCountableTopology Jₛ :=
  inferInstanceAs (SecondCountableTopology (Iₛ ⧸ _))

local instance instIdeleClassHaarMeasureSec1 : Measure.IsHaarMeasure μ𝔽 :=
  (ideleClassTamagawaMeasure_isWeil F).1

local instance instSIdeleQuotientHaarMeasureSec1 : Measure.IsHaarMeasure μₛ :=
  (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1

open scoped ENNReal in
/-- Scaling a measure by a finite positive constant gives the same weighted L² space
with the norm scaled by the square root of the constant. -/
private theorem globalThetaAmbient_equiv_canonical_aux {G : Type*} [MeasurableSpace G]
    (μ ν : Measure G) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤) (hμ : μ = c • ν)
    (d : G → ℝ≥0∞) (hdm : Measurable d) (hd : ∀ x, d x ≠ 0) :
    ∃ e : Lp ℂ 2 (μ.withDensity d) ≃L[ℂ] Lp ℂ 2 (ν.withDensity d),
      ∀ u, (e u : G → ℂ) =ᵐ[μ] u ∧ ‖u‖ = Real.sqrt c.toReal * ‖e u‖ := by
  subst hμ
  have hρ : (c • ν).withDensity d = c • ν.withDensity d := withDensity_smul_measure c d
  have hci : c⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hc0
  have hle : ν.withDensity d ≤ c⁻¹ • (c • ν).withDensity d := by
    rw [hρ, smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]
  have hle' : (c • ν).withDensity d ≤ c • ν.withDensity d := hρ.le
  have mem₁ (u : Lp ℂ 2 ((c • ν).withDensity d)) : MemLp u 2 (ν.withDensity d) :=
    (Lp.memLp u).of_measure_le_smul hci hle
  have mem₂ (u : Lp ℂ 2 (ν.withDensity d)) : MemLp u 2 ((c • ν).withDensity d) :=
    (Lp.memLp u).of_measure_le_smul hct hle'
  have hsmul {p : G → Prop} (ρ : Measure G) : (∀ᵐ x ∂(c • ρ), p x) ↔ ∀ᵐ x ∂ρ, p x := by
    simp only [ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero, hc0, false_or]
  have hae₁ {f g : G → ℂ} (h : f =ᵐ[(c • ν).withDensity d] g) : f =ᵐ[ν.withDensity d] g := by
    rw [hρ] at h
    exact (hsmul _).mp h
  have hae₂ {f g : G → ℂ} (h : f =ᵐ[ν.withDensity d] g) : f =ᵐ[(c • ν).withDensity d] g := by
    rw [hρ]
    exact (hsmul _).mpr h
  let T : Lp ℂ 2 ((c • ν).withDensity d) →ₗ[ℂ] Lp ℂ 2 (ν.withDensity d) :=
    { toFun := fun u ↦ (mem₁ u).toLp u
      map_add' := fun u v ↦ by
        apply Lp.ext
        filter_upwards [(mem₁ (u + v)).coeFn_toLp, (mem₁ u).coeFn_toLp, (mem₁ v).coeFn_toLp,
          Lp.coeFn_add ((mem₁ u).toLp u) ((mem₁ v).toLp v), hae₁ (Lp.coeFn_add u v)]
          with x h1 h2 h3 h4 h5
        rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply]
      map_smul' := fun r u ↦ by
        apply Lp.ext
        filter_upwards [(mem₁ (r • u)).coeFn_toLp, (mem₁ u).coeFn_toLp,
          Lp.coeFn_smul r ((mem₁ u).toLp u), hae₁ (Lp.coeFn_smul r u)]
          with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2, h4, Pi.smul_apply] }
  let S : Lp ℂ 2 (ν.withDensity d) → Lp ℂ 2 ((c • ν).withDensity d) := fun u ↦ (mem₂ u).toLp u
  have hTS (u) : T (S u) = u := by
    apply Lp.ext
    filter_upwards [(mem₁ (S u)).coeFn_toLp, hae₁ (mem₂ u).coeFn_toLp] with x h1 h2
    exact h1.trans h2
  have hST (u) : S (T u) = u := by
    apply Lp.ext
    filter_upwards [(mem₂ (T u)).coeFn_toLp, hae₂ (mem₁ u).coeFn_toLp] with x h1 h2
    exact h1.trans h2
  have hnorm (u : Lp ℂ 2 ((c • ν).withDensity d)) : ‖u‖ = Real.sqrt c.toReal * ‖T u‖ := by
    have hsm (f : G → ℂ) : eLpNorm f 2 ((c • ν).withDensity d) =
        c ^ (1 / (2 : ℝ≥0∞)).toReal • eLpNorm f 2 (ν.withDensity d) := by
      rw [hρ, eLpNorm_smul_measure_of_ne_zero hc0]
    have h1 : eLpNorm (T u : G → ℂ) 2 (ν.withDensity d) = eLpNorm (u : G → ℂ) 2 (ν.withDensity d) :=
      eLpNorm_congr_ae (mem₁ u).coeFn_toLp
    rw [Lp.norm_def, Lp.norm_def, h1, hsm, smul_eq_mul,
      ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Real.sqrt_eq_rpow]
    norm_num
  let e₀ : Lp ℂ 2 ((c • ν).withDensity d) ≃ₗ[ℂ] Lp ℂ 2 (ν.withDensity d) :=
    { T with invFun := S, left_inv := hST, right_inv := hTS }
  have hcpos : 0 < Real.sqrt c.toReal :=
    Real.sqrt_pos.mpr (ENNReal.toReal_pos hc0 hct)
  refine ⟨e₀.toContinuousLinearEquivOfBounds (Real.sqrt c.toReal)⁻¹ (Real.sqrt c.toReal)
    (fun u ↦ ?_) (fun u ↦ ?_), fun u ↦ ⟨?_, hnorm u⟩⟩
  · change ‖T u‖ ≤ _
    rw [hnorm u, ← mul_assoc, inv_mul_cancel₀ hcpos.ne', one_mul]
  · change ‖S u‖ ≤ _
    rw [hnorm (S u), hTS]
  · change ((mem₁ u).toLp u : G → ℂ) =ᵐ[c • ν] u
    have h := (mem₁ u).coeFn_toLp
    rw [Filter.EventuallyEq, ae_withDensity_iff hdm] at h
    exact (hsmul _).mpr (h.mono fun x hx ↦ hx (hd x))

/-- Paper: Definition 10.1.1.1(1) and Lemma 10.1.1.3, pp. 434–435.
The identity on functions compares the Tamagawa norm with the canonical norm of §9.2.
Deviation: The two full Haar measures differ by the mass of the norm-one classes. -/
theorem globalThetaAmbient_equiv_canonical (hm : IsModulation m𝔽) (α β s : ℝ) :
    ∃ e : W𝔽(α, β, s) ≃L[ℂ] ModulatedIntervalSobolev m𝔽 hm α β s,
      ∀ u, (e u : C𝔽 → ℂ) =ᵐ[μ𝔽] u ∧
        ‖u‖ = Real.sqrt (Measure.real μ𝔽₁ univ) * ‖e u‖ := by
  have hμ := ideleClassTamagawaMeasure_eq_smul_canonical (F := F)
  have hvol := normOneIdeleClassTamagawaMeasure_volume (F := F)
  have hc0 : μ𝔽₁ univ ≠ 0 := by
    rw [hvol, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have := NumberField.Units.regulator_pos F
    have := NumberField.classNumber_pos F
    have := NumberField.Units.torsionOrder_pos F
    have : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr F) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F))
    positivity
  have hct : μ𝔽₁ univ ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  have hdm : Measurable fun g : C𝔽 ↦
      ENNReal.ofReal (intervalSobolevDensity α β s (Real.log (((m𝔽 g).val : ℝ)))) := by
    have hLm : Measurable fun g : C𝔽 ↦ Real.log (((m𝔽 g).val : ℝ)) :=
      ((NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).log
        fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne').measurable
    unfold intervalSobolevDensity
    fun_prop
  have hd (g : C𝔽) :
      ENNReal.ofReal (intervalSobolevDensity α β s (Real.log (((m𝔽 g).val : ℝ)))) ≠ 0 := by
    refine (ENNReal.ofReal_pos.mpr ?_).ne'
    unfold intervalSobolevDensity
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _)) (by positivity)
  exact globalThetaAmbient_equiv_canonical_aux μ𝔽 (canonicalModulatedHaar m𝔽 hm)
    (μ𝔽₁ univ) hc0 hct hμ _ hdm hd

open scoped ENNReal in
/-- The S-local quotient Tamagawa measure is the canonical modulated Haar measure times the
mass of the norm-one quotient. Both measures give the band of norms in [1, e] the mass of
the norm-one part. -/
private theorem sLocalThetaAmbient_equiv_canonical_measure (hm : IsModulation mₛ) :
    μₛ = μₛ₁ univ • canonicalModulatedHaar mₛ hm := by
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : SFinite (positiveRealHaar : Measure ℝ≥0ˣ) := by unfold positiveRealHaar; infer_instance
  have : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
  have : BorelSpace J₁ := ⟨rfl⟩
  have : (μₛ₁).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  -- A continuous section of the S-idelic norm and its image in the quotient.
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let τ : ℝ≥0ˣ →ₜ* Iₛ := ⟨p.comp (canonicalIdeleNormSection F),
    hp.comp (canonicalIdeleNormSection_continuous F)⟩
  have hτ : RightInverse τ (sIdeleNorm F S) := thetaSection_rightInverse F S
  let σ : ℝ≥0ˣ →ₜ* Jₛ :=
    (⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩ : Iₛ →ₜ* Jₛ).comp τ
  have hσ : RightInverse σ mₛ := fun t ↦ (sIdeleQuotientNorm_mk F S (τ t)).trans (hτ t)
  -- The band of norms between 1 and e has `dt/t`-mass one.
  let Sb : Set ℝ≥0ˣ := {t | ((t.val : ℝ≥0) : ℝ) ∈ Icc 1 (Real.exp 1)}
  have hSm : MeasurableSet Sb :=
    (NNReal.continuous_coe.comp Units.continuous_val).measurable measurableSet_Icc
  have hPRS : positiveRealHaar Sb = 1 := by
    let T : ℝ≥0ˣ := Units.mk0 (Real.exp 1).toNNReal (by positivity)
    have hT : ((T.val : ℝ≥0) : ℝ) = Real.exp 1 := Real.coe_toNNReal _ (Real.exp_pos 1).le
    have h := positiveRealHaar_interval T (by rw [hT]; exact Real.one_le_exp zero_le_one)
    rw [hT, Real.log_exp, ENNReal.ofReal_one] at h
    exact h
  let B : Set Jₛ := mₛ ⁻¹' Sb
  have hBm : MeasurableSet B := (mₛ).continuous.measurable hSm
  have hnorm (k : Jₛ) (hk : mₛ k = 1) (t : ℝ≥0ˣ) : k * σ t ∈ B ↔ t ∈ Sb := by
    change mₛ (k * σ t) ∈ Sb ↔ _
    rw [map_mul, hk, one_mul, hσ t]
  -- The canonical measure gives the band mass one.
  have hcanB : canonicalModulatedHaar mₛ hm B = 1 := by
    letI : MeasurableSpace (mₛ).toMonoidHom.ker := Subtype.instMeasurableSpace
    have : CompactSpace (mₛ).toMonoidHom.ker := isCompact_iff_compactSpace.mp hm.isCompact_ker
    let μ₀ : Measure (mₛ).toMonoidHom.ker := Measure.haarMeasure ⊤
    have hcan := canonicalModulatedHaar_eq_map_prod mₛ hm σ hσ μ₀ Measure.haarMeasure_self
    have hφ : Continuous fun z : (mₛ).toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : Jₛ) * σ z.2 := by
      fun_prop
    rw [hcan, Measure.map_apply hφ.measurable hBm]
    have hpre : (fun z : (mₛ).toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : Jₛ) * σ z.2) ⁻¹' B =
        univ ×ˢ Sb := by
      ext ⟨k, t⟩
      simp only [mem_preimage, mem_prod, mem_univ, true_and]
      exact hnorm k k.property t
    rw [hpre, Measure.prod_prod, show μ₀ univ = 1 from Measure.haarMeasure_self, one_mul, hPRS]
  -- The quotient Tamagawa measure gives the band the mass of the norm-one part.
  have hμB : μₛ B = μₛ₁ univ := by
    have hJ := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 τ hτ
    have hφ : Continuous fun x : J₁ × ℝ≥0ˣ ↦ (x.1 : Jₛ) * QuotientGroup.mk (τ x.2) := by
      fun_prop
    rw [← hJ, Measure.map_apply hφ.measurable hBm]
    have hpre : (fun x : J₁ × ℝ≥0ˣ ↦ (x.1 : Jₛ) * QuotientGroup.mk (τ x.2)) ⁻¹' B =
        univ ×ˢ Sb := by
      ext ⟨k, t⟩
      simp only [mem_preimage, mem_prod, mem_univ, true_and]
      exact hnorm k k.property t
    rw [hpre, Measure.prod_prod, hPRS, mul_one]
  -- Compare the two Haar measures on the band.
  have : (canonicalModulatedHaar mₛ hm).IsHaarMeasure :=
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar mₛ hm).exists).1
  have hscale := Measure.isMulLeftInvariant_eq_smul μₛ (canonicalModulatedHaar mₛ hm)
  set c := Measure.haarScalarFactor μₛ (canonicalModulatedHaar mₛ hm)
  have hc : (c : ℝ≥0∞) = μₛ₁ univ := by
    have h := congrArg (fun ν : Measure Jₛ ↦ ν B) hscale
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    rw [← hμB, h, hcanB, mul_one]
  exact hscale.trans (by rw [ENNReal.smul_def, hc])

/-- Paper: Definition 10.1.1.1(2) and Lemma 10.1.1.4, pp. 434–436.
The identity on S-local functions compares the norm in (10.1.1.5) with §9.2.
Deviation: The Tamagawa squared norm includes the mass of the norm-one quotient. -/
theorem sLocalThetaAmbient_equiv_canonical (hm : IsModulation mₛ) (α β s : ℝ) :
    ∃ e : Wₛ(α, β, s) ≃L[ℂ] ModulatedIntervalSobolev mₛ hm α β s,
      ∀ u, (e u : Jₛ → ℂ) =ᵐ[μₛ] u ∧
        ‖u‖ = Real.sqrt (Measure.real μₛ₁ univ) * ‖e u‖ := by
  have : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
  have : (μₛ₁).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have hc0 : μₛ₁ univ ≠ 0 := (isOpen_univ.measure_pos _ univ_nonempty).ne'
  have hct : μₛ₁ univ ≠ ⊤ := measure_ne_top _ _
  have hdm : Measurable fun g : Jₛ ↦
      ENNReal.ofReal (intervalSobolevDensity α β s (Real.log (((mₛ g).val : ℝ)))) := by
    have hLm : Measurable fun g : Jₛ ↦ Real.log (((mₛ g).val : ℝ)) :=
      ((NNReal.continuous_coe.comp (Units.continuous_val.comp (mₛ).continuous)).log
        fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne').measurable
    unfold intervalSobolevDensity
    fun_prop
  have hd (g : Jₛ) :
      ENNReal.ofReal (intervalSobolevDensity α β s (Real.log (((mₛ g).val : ℝ)))) ≠ 0 := by
    refine (ENNReal.ofReal_pos.mpr ?_).ne'
    unfold intervalSobolevDensity
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _)) (by positivity)
  exact globalThetaAmbient_equiv_canonical_aux μₛ (canonicalModulatedHaar mₛ hm)
    (μₛ₁ univ) hc0 hct (sLocalThetaAmbient_equiv_canonical_measure hm) _ hdm hd

/-- Paper: Lemma 10.1.1.3(2), p. 435. Ambient left translation preserves the
global completion, acts jointly continuously there, and on weighted tests
has the factor |g|^(-a) multiplying the translated test. -/
theorem exists_globalThetaSobolevAction (a : ℝ) {α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s) :
    ∃ ρ : C𝔽 →* (H𝔽(a, hI, hs) →L[ℂ] H𝔽(a, hI, hs)),
      (∀ g u, (ρ g u : W𝔽(α, β, s)) = hardySobolevTranslation μ𝔽 m𝔽 α β s hI hs g u) ∧
      Continuous (fun p : C𝔽 × H𝔽(a, hI, hs) ↦ ρ p.1 p.2) ∧
      ∀ (g : IdeleGroup (𝓞 F) F) (f : ℬ₀), ∃ f' : ℬ₀,
        f'.val = schwartzBruhatUnitTranslate g f.val ∧
          ρ (QuotientGroup.mk g) (j𝔽(a, hI, hs) (Submodule.Quotient.mk f)) =
            (((m𝔽 (QuotientGroup.mk g)).val : ℝ) ^ (-a) : ℝ) •
              j𝔽(a, hI, hs) (Submodule.Quotient.mk f') := by sorry

local notation "R𝔽(" a ", " hI ", " hs ")" =>
  (exists_globalThetaSobolevAction (F := F) a hI hs).choose

variable (F S) in
/-- Paper: Lemma 10.1.1.4(1), p. 435. The measure μ_{I,s} on the S-ideles
has the compact-interval Sobolev density in the logarithmic norm coordinate. -/
def sIdeleIntervalSobolevMeasure (α β s : ℝ) : Measure Iₛ :=
  (sMultiplicativeTamagawaMeasure F S).withDensity fun g ↦
    ENNReal.ofReal (intervalSobolevDensity α β s (Real.log ((sIdeleNorm F S g).val : ℝ)))

-- The density need not vanish at infinity, as the proof on p. 436 claims.
-- Continuity is enough for local boundedness and the Radon property.

/-- Paper: Lemma 10.1.1.4(1), p. 435. The interval density is one for I = {0},
s = 0, so the measure is the original multiplicative Tamagawa measure.
Deviation: Sanity check for the measure. -/
theorem sIdeleIntervalSobolevMeasure_zero :
    sIdeleIntervalSobolevMeasure F S 0 0 0 = sMultiplicativeTamagawaMeasure F S := by
  simp [sIdeleIntervalSobolevMeasure, intervalSobolevDensity]

/-- The density of the weighted S-idele measure is continuous. -/
private theorem sIdeleIntervalSobolevMeasure_regular_density (α β s : ℝ) :
    Continuous fun g : Iₛ ↦
      intervalSobolevDensity α β s (Real.log ((sIdeleNorm F S g).val : ℝ)) := by
  have hn : Continuous fun g : Iₛ ↦ ((sIdeleNorm F S g).val : ℝ) := by
    have h : Continuous fun g : Iₛ ↦ sIdeleQuotientNorm F S (QuotientGroup.mk g) :=
      (isProperMap_sIdeleQuotientNorm F S).continuous.comp continuous_quot_mk
    exact NNReal.continuous_coe.comp (Units.continuous_val.comp h)
  have hl : Continuous fun g : Iₛ ↦ Real.log ((sIdeleNorm F S g).val : ℝ) :=
    hn.log fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S g))).ne'
  unfold intervalSobolevDensity
  refine ((Real.continuous_exp.comp (continuous_const.mul hl)).max
    (Real.continuous_exp.comp (continuous_const.mul hl))).mul ?_
  exact (continuous_const.add (hl.pow 2)).rpow_const fun g ↦
    Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne'

/-- Paper: Lemma 10.1.1.4(1), pp. 435–436. The weighted S-idele measure is
regular and finite on compact sets. -/
theorem sIdeleIntervalSobolevMeasure_regular (α β s : ℝ)
    (_hI : α ≤ β) (_hs : 0 ≤ s) :
    (sIdeleIntervalSobolevMeasure F S α β s).Regular := by
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace (F := F) (S := S)
  have : (sMultiplicativeTamagawaMeasure F S).IsHaarMeasure :=
    sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
  have : IsLocallyFiniteMeasure (sIdeleIntervalSobolevMeasure F S α β s) :=
    IsLocallyFiniteMeasure.withDensity_ofReal
      (sIdeleIntervalSobolevMeasure_regular_density α β s)
  infer_instance

/-- Paper: Lemma 10.1.1.4(1), pp. 435–436. The weighted S-idele measure is
invariant under left translation by the projected diagonal S-units. -/
theorem sIdeleIntervalSobolevMeasure_invariant (α β s : ℝ)
    (_hI : α ≤ β) (_hs : 0 ≤ s) :
    let ν := sIdeleIntervalSobolevMeasure F S α β s
    ∀ u : Iₛ, (QuotientGroup.mk u : Jₛ) = 1 →
      MeasurePreserving (fun g : Iₛ ↦ u * g) ν ν := by
  intro ν u hu
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace (F := F) (S := S)
  have : (sMultiplicativeTamagawaMeasure F S).IsHaarMeasure :=
    sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
  have hnu : sIdeleNorm F S u = 1 := by rw [← sIdeleQuotientNorm_mk, hu, map_one]
  have hmeas : Measurable fun g : Iₛ ↦ u * g := measurable_const_mul u
  refine ⟨hmeas, ?_⟩
  ext A hA
  rw [Measure.map_apply hmeas hA]
  simp only [ν, sIdeleIntervalSobolevMeasure, withDensity_apply _ hA,
    withDensity_apply _ (hmeas hA)]
  rw [← lintegral_indicator (hmeas hA), ← lintegral_indicator hA]
  conv_rhs => rw [← lintegral_mul_left_eq_self _ u]
  congr 1
  funext g
  simp only [indicator, map_mul, hnu, one_mul]
  rfl

/-- Paper: Lemma 10.1.1.4(2), pp. 435–436. On the local test classes the
subspace norm is (10.1.1.7) and is continuous for the theta quotient topology.
Deviation: Use μ̄_S on J_{F,S}, as in (10.1.1.5) and Appendix A.3. The formula
also applies whenever the smallest effective exponent a + α is positive. -/
theorem sLocalThetaSobolev_norm {a α β s : ℝ} (ha : 0 < a) (hI : α ≤ β)
    (hs : 0 ≤ s) (hp : 0 < a + α) (f : ℬₛ) :
    let w := fun g : Jₛ ↦ ‖θₛ(f) g‖ ^ 2 *
      intervalSobolevDensity (a + α) (a + β) s (logNorm(mₛ) g)
    Integrable w μₛ ∧ ‖Eₛ(ha, hI, hs, hp) (Submodule.Quotient.mk f)‖ =
      Real.sqrt (∫ g, w g ∂μₛ) := by
  have hE := (existsUnique_sLocalThetaSobolevEmbedding (F := F) (S := S) a α β s ha hI hs
    hp).exists.choose_spec.2 f
  exact globalThetaSobolev_norm_aux μₛ (fun g ↦ ((mₛ g).val : ℝ))
    (fun g ↦ NNReal.coe_pos.mpr (Units.zero_lt _))
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (mₛ).continuous)).measurable
    a α β s _ _ hE

/-- Paper: Lemma 10.1.1.4(3), p. 436. The local completion is a closed,
complete and separable subspace of the ambient Hilbert space. -/
theorem sLocalThetaSobolev_closed_complete_separable {a α β s : ℝ} (ha : 0 < a)
    (hI : α ≤ β) (hs : 0 ≤ s) (hp : 0 < a + α) :
    IsClosed (Hₛ(ha, hI, hs, hp) : Set Wₛ(α, β, s)) ∧
      CompleteSpace (Hₛ(ha, hI, hs, hp)) ∧
      TopologicalSpace.SeparableSpace (Hₛ(ha, hI, hs, hp)) := by
  have hc : IsClosed (Hₛ(ha, hI, hs, hp) : Set Wₛ(α, β, s)) :=
    Submodule.isClosed_topologicalClosure _
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology Wₛ(α, β, s) := Lp.SecondCountableTopology
  exact ⟨hc, hc.completeSpace_coe, inferInstance⟩

/-- Paper: Lemma 10.1.1.4(4), p. 436. Ambient left translation preserves the
S-local completion, acts jointly continuously there, and on weighted classes
it acts by translated theta classes times the factor |g|^(-a). -/
theorem exists_sLocalThetaSobolevAction {a α β s : ℝ} (ha : 0 < a)
    (hI : α ≤ β) (hs : 0 ≤ s) (hp : 0 < a + α) :
    ∃ ρ : Jₛ →* (Hₛ(ha, hI, hs, hp) →L[ℂ] Hₛ(ha, hI, hs, hp)),
      (∀ g u, (ρ g u : Wₛ(α, β, s)) = hardySobolevTranslation μₛ mₛ α β s hI hs g u) ∧
      Continuous (fun p : Jₛ × Hₛ(ha, hI, hs, hp) ↦ ρ p.1 p.2) ∧
      ∀ (g : Jₛ) (u : Θₛ), ρ g (jₛ(ha, hI, hs, hp) u) =
        (((mₛ g).val : ℝ) ^ (-a) : ℝ) • jₛ(ha, hI, hs, hp) (ρₛ g u) := by sorry

local notation "Rₛ(" ha ", " hI ", " hs ", " hp ")" =>
  (exists_sLocalThetaSobolevAction (F := F) (S := S) ha hI hs hp).choose


/-- Paper: §10.1.1, p. 436. The paper's pairing on the weighted S-idelic
L² space is the integral of the first function times the conjugate of the second.
Deviation: Swap the arguments of Mathlib's conjugate-linear-first inner product. -/
theorem sIdeleIntervalSobolev_inner (α β s : ℝ)
    (u v : Lp ℂ 2 (sIdeleIntervalSobolevMeasure F S α β s)) :
    inner ℂ v u =
      ∫ g : Iₛ, u g * star (v g) ∂(sIdeleIntervalSobolevMeasure F S α β s) := by
  rw [MeasureTheory.L2.inner_def]
  simp only [RCLike.inner_apply, starRingEnd_apply]

-- TODO(paper-gap): The global spaces in Proposition 10.1.1.5 drop the subscript 0.
-- At weight zero the usual rational adelic Gaussian does not have square-integrable theta.
-- The raw averages from (10.1.1.8) and (10.1.1.9) carry the norm-one Haar mass.

section GlobalIsotypes

variable {a α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s)

local notation "H" => ↥(H𝔽(a, hI, hs))
local notation "ρ₁" => (R𝔽(a, hI, hs)).comp (ideleClassNorm F).ker.subtype
local notation "Hω(" ω ")" => actionIsotype ρ₁ ω

section

universe u v

/-- The compact-group average, restricted to its isotype, is a unique open surjection. -/
private theorem existsUnique_thetaSobolevAverage_of_compact
    {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) [T2Space N] [CompactSpace N] [MeasurableSpace N] [BorelSpace N]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure N) [μ.IsHaarMeasure] (ρ : G →* (E →L[ℂ] E))
    (hρ : Continuous fun p : G × E ↦ ρ p.1 p.2) (ω : PontryaginDual N) :
    ∃! A : E →L[ℂ] actionIsotype (ρ.comp N.subtype) ω,
      IsPettisIsotypicAverageOn μ univ (ρ.comp N.subtype) ω
        ((actionIsotype (ρ.comp N.subtype) ω).subtypeL.comp A) ∧
      Surjective A ∧ IsOpenMap A := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  have hc : @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  obtain ⟨P, hP, huniq⟩ := existsUnique_globalThetaIsotypicAverage_of_compact N hc μ ρ hρ ω
  have hcρ : Continuous (fun p : N × E ↦ (ρ.comp N.subtype) p.1 p.2) :=
    hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hr := compactActionAverage_range μ (ρ.comp N.subtype) hcρ ω P hP
  let V := actionIsotype (ρ.comp N.subtype) ω
  have hmem (x : E) : P x ∈ V := by
    change P x ∈ actionIsotype (ρ.comp N.subtype) ω
    rw [← hr]
    exact LinearMap.mem_range_self P.toLinearMap x
  let A : E →L[ℂ] V := P.codRestrict V hmem
  have hcomp : V.subtypeL.comp A = P := by ext; rfl
  have hsurj : Surjective A := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := (show x ∈ LinearMap.range P.toLinearMap from hr.symm ▸ hx)
    exact ⟨y, Subtype.ext hy⟩
  obtain ⟨e, he⟩ := compactActionAverage_quotient_equiv μ (ρ.comp N.subtype) hcρ ω P hP
  have hA : (A : E → V) = e ∘ P.ker.mkQ := by
    funext x
    exact Subtype.ext (he x).symm
  refine ⟨A, ⟨by rwa [hcomp], hsurj, ?_⟩, ?_⟩
  · rw [hA]
    exact e.isOpenMap.comp P.ker.isOpenMap_mkQ
  · intro B hB
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun (huniq _ hB.1) x

end

/-- Paper: Proposition 10.1.1.5(1), p. 436. The global Pettis average for the
norm-one Tamagawa measure is a continuous open linear surjection onto its isotype.
Deviation: Use polar-free global theta functions, as in Definition 10.1.1.1(1). -/
theorem existsUnique_globalThetaSobolevAverage (ω : PontryaginDual C₁) :
    ∃! P : H →L[ℂ] Hω(ω),
      IsPettisIsotypicAverageOn μ𝔽₁ univ ρ₁ ω ((Hω(ω)).subtypeL.comp P) ∧
      Surjective P ∧ IsOpenMap P := by
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (μ𝔽₁).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : CompleteSpace H := (globalThetaSobolev_closed_complete_separable a hI hs).2.1
  with_reducible_and_instances
    exact existsUnique_thetaSobolevAverage_of_compact (E := H) (ideleClassNorm F).ker
      μ𝔽₁ (R𝔽(a, hI, hs)) (exists_globalThetaSobolevAction (F := F) a hI hs).choose_spec.2.1 ω

local notation "P(" ω ")" =>
  (existsUnique_globalThetaSobolevAverage (F := F) (a := a) hI hs ω).exists.choose

/-- Paper: Proposition 10.1.1.5(1), pp. 436–437. The global isotype completes
the polar-free homogeneous classes of §6.3 with their weighted function norm.
On representatives its inclusion is the unnormalized homogeneous theta function.
Deviation: The global domain uses polar-free tests. -/
theorem exists_globalHomogeneousThetaSobolevInclusion (ω : PontryaginDual C₁) :
    ∃ j : ↥(globalPolarFreeThetaSubmodule (F := F) ω) →L[ℂ] Hω(ω),
      Injective j ∧ DenseRange j ∧
       ∀ (f : ℬ₀) (x : globalPolarFreeThetaSubmodule (F := F) ω),
        x.val = Submodule.Quotient.mk f.val →
          j x = P(ω) (j𝔽(a, hI, hs) (Submodule.Quotient.mk f)) ∧
          ((j x).val.val : C𝔽 → ℂ) =ᵐ[μ𝔽]
            modulationWeight m𝔽 a (homogeneousAdelicTheta ω f.val) := by sorry

section

universe u v

/-- The kernel of a compact isotypic average is the closed span of twisted differences. -/
private theorem thetaSobolevAverage_quotient_equiv_of_compact
    {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (μ : Measure G) [μ.IsHaarMeasure] (ρ : G →* (E →L[ℂ] E))
    (hρ : Continuous fun p : G × E ↦ ρ p.1 p.2) (ω : PontryaginDual G)
    (P : E →L[ℂ] actionIsotype ρ ω)
    (hP : IsPettisIsotypicAverageOn μ univ ρ ω ((actionIsotype ρ ω).subtypeL.comp P)) :
    let D := (Submodule.span ℂ (range (fun p : G × E ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1 p.2))).topologicalClosure
    ∃ T : (E ⧸ D) ≃L[ℂ] actionIsotype ρ ω, ∀ u, T (D.mkQ u) = P u := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let Q := (actionIsotype ρ ω).subtypeL.comp P
  have hker := compactActionAverage_ker μ ρ hρ ω Q hP
  obtain ⟨e, he⟩ := compactActionAverage_quotient_equiv μ ρ hρ ω Q hP
  dsimp only
  rw [← hker]
  exact ⟨e, fun u ↦ Subtype.ext (he u)⟩

end

/-- Paper: Proposition 10.1.1.5(1), p. 437. The global raw average induces a
topological linear isomorphism from the completed homogeneous quotient to the isotype.
Deviation: Use polar-free tests. The completed coinvariant quotient is realized by
dividing the completed space by the closed span of the twisted differences. -/
theorem globalThetaSobolevAverage_quotient_equiv (ω : PontryaginDual C₁) :
    let D := (Submodule.span ℂ (range (fun p : C₁ × H ↦
      p.2 - star (ω p.1 : ℂ) • ρ₁ p.1 p.2))).topologicalClosure
    ∃ T : (H ⧸ D) ≃L[ℂ] Hω(ω), ∀ u : H, T (D.mkQ u) = P(ω) u := by
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (μ𝔽₁).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hρ : Continuous (fun p : C₁ × H ↦ ρ₁ p.1 p.2) :=
    (exists_globalThetaSobolevAction (F := F) a hI hs).choose_spec.2.1.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  with_reducible_and_instances
    exact thetaSobolevAverage_quotient_equiv_of_compact μ𝔽₁ ρ₁ hρ ω (P(ω))
      (existsUnique_globalThetaSobolevAverage (F := F) (a := a) hI hs ω).exists.choose_spec.1

/-- Paper: Proposition 10.1.1.5(2), p. 437. The global coordinate map is a
continuous injection into the product and factors through the isometric Hilbert sum.
Deviation: Use the polar-free space and divide each raw average by the mass of
the norm-one Tamagawa measure. The homogeneous targets are identified with their isotypes. -/
theorem globalThetaSobolev_isotypeDecomposition :
    ∃ (Pprod : H →L[ℂ] (∀ ω : PontryaginDual C₁, Hω(ω)))
      (T : H ≃ₗᵢ[ℂ] lp (fun ω : PontryaginDual C₁ ↦ ↥(Hω(ω))) 2),
      Injective Pprod ∧ ∀ (u : H) (ω : PontryaginDual C₁),
        Pprod u ω = T u ω ∧ T u ω = (Measure.real μ𝔽₁ univ)⁻¹ • P(ω) u := by sorry

end GlobalIsotypes

section SLocalIsotypes

variable {a α β s : ℝ} (ha : 0 < a) (hI : α ≤ β) (hs : 0 ≤ s) (hα : 0 < α)

local notation "hp" => (add_pos ha hα)
local notation "H" => ↥(Hₛ(ha, hI, hs, hp))
local notation "ρ₁" => (Rₛ(ha, hI, hs, hp)).comp (sIdeleQuotientNorm F S).ker.subtype
local notation "Hω(" ω ")" => actionIsotype ρ₁ ω

/-- Paper: Proposition 10.1.1.5(1), pp. 436–437. The S-local Pettis average for
the norm-one quotient measure is a continuous open linear surjection onto its isotype.
Deviation: The letter a represents the local weight b of the proposition. -/
theorem existsUnique_sLocalThetaSobolevAverage (ω : PontryaginDual J₁) :
    ∃! P : H →L[ℂ] Hω(ω),
      IsPettisIsotypicAverageOn μₛ₁ univ ρ₁ ω ((Hω(ω)).subtypeL.comp P) ∧
      Surjective P ∧ IsOpenMap P := by
  let : BorelSpace J₁ := ⟨rfl⟩
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : (μₛ₁).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : CompleteSpace H := (sLocalThetaSobolev_closed_complete_separable ha hI hs hp).2.1
  with_reducible_and_instances
    exact existsUnique_thetaSobolevAverage_of_compact (E := H) (sIdeleQuotientNorm F S).ker
      μₛ₁ (Rₛ(ha, hI, hs, hp))
      (exists_sLocalThetaSobolevAction (F := F) (S := S) ha hI hs hp).choose_spec.2.1 ω

local notation "P(" ω ")" =>
  (existsUnique_sLocalThetaSobolevAverage (F := F) (S := S) ha hI hs hα ω).exists.choose

/-- Paper: Proposition 10.1.1.5(1), pp. 436–437. The S-local isotype completes
the homogeneous classes of §5.2 with their weighted function norm. Its test-class
inclusion is given by the unnormalized S-local homogeneous theta function. -/
theorem exists_sLocalHomogeneousThetaSobolevInclusion (ω : PontryaginDual J₁) :
    ∃ j : SLocalHomogeneousThetaSpace F S ω →L[ℂ] Hω(ω),
      Injective j ∧ DenseRange j ∧ ∀ f : ℬₛ,
        j (Submodule.Quotient.mk f) = P(ω) (jₛ(ha, hI, hs, hp) (Submodule.Quotient.mk f)) ∧
        ((j (Submodule.Quotient.mk f)).val.val : Jₛ → ℂ) =ᵐ[μₛ]
          modulationWeight mₛ a (sLocalHomogeneousAdelicThetaLinearMap F S ω f) := by sorry

/-- Paper: Proposition 10.1.1.5(1), p. 437. The S-local raw average induces a
topological linear isomorphism from the completed homogeneous quotient to the isotype.
Deviation: The completed coinvariant quotient is realized by dividing the completed
space by the closed span of the twisted differences. -/
theorem sLocalThetaSobolevAverage_quotient_equiv (ω : PontryaginDual J₁) :
    let D := (Submodule.span ℂ (range (fun p : J₁ × H ↦
      p.2 - star (ω p.1 : ℂ) • ρ₁ p.1 p.2))).topologicalClosure
    ∃ T : (H ⧸ D) ≃L[ℂ] Hω(ω), ∀ u : H, T (D.mkQ u) = P(ω) u := by
  let : BorelSpace J₁ := ⟨rfl⟩
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : (μₛ₁).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have hρ : Continuous (fun p : J₁ × H ↦ ρ₁ p.1 p.2) :=
    (exists_sLocalThetaSobolevAction (F := F) (S := S) ha hI hs hp).choose_spec.2.1.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  with_reducible_and_instances
    exact thetaSobolevAverage_quotient_equiv_of_compact μₛ₁ ρ₁ hρ ω (P(ω))
      (existsUnique_sLocalThetaSobolevAverage (F := F) (S := S) ha hI hs hα ω).exists.choose_spec.1

/-- Paper: Proposition 10.1.1.5(2), p. 437. The S-local coordinate map is a
continuous injection into the product and factors through the isometric Hilbert sum.
Deviation: Divide each raw average by the mass of the norm-one quotient measure.
The homogeneous targets are identified with their isotypes. -/
theorem sLocalThetaSobolev_isotypeDecomposition :
    ∃ (Pprod : H →L[ℂ] (∀ ω : PontryaginDual J₁, Hω(ω)))
      (T : H ≃ₗᵢ[ℂ] lp (fun ω : PontryaginDual J₁ ↦ ↥(Hω(ω))) 2),
      Injective Pprod ∧ ∀ (u : H) (ω : PontryaginDual J₁),
        Pprod u ω = T u ω ∧ T u ω = (Measure.real μₛ₁ univ)⁻¹ • P(ω) u := by sorry

end SLocalIsotypes

section Fourier

-- TODO(paper-gap): The ambient inversion automorphism in Theorem 10.1.2.1
-- fails for nonsymmetric I. The types in (10.1.2.5) also swap the weight labels.

/-- Reflecting the logarithmic coordinate reflects the interval of the density. -/
private theorem ideleClassSobolevInversion_density (α β s x : ℝ) :
    intervalSobolevDensity α β s (-x) = intervalSobolevDensity (-β) (-α) s x := by
  unfold intervalSobolevDensity
  rw [max_comm, neg_sq]
  congr 3 <;> ring

/-- Inversion carries the reflected weighted measure to the weighted measure. -/
private theorem ideleClassSobolevInversion_measurePreserving {G : Type*} [CommGroup G]
    [MeasurableSpace G] [MeasurableInv G] (μ : Measure G) [μ.IsInvInvariant] (L : G → ℝ)
    (hL : ∀ g, L g⁻¹ = - L g) (α β s : ℝ) :
    MeasurePreserving Inv.inv
      (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity (-β) (-α) s (L x)))
      (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity α β s (L x))) := by
  refine ⟨measurable_inv, ?_⟩
  ext A hA
  rw [Measure.map_apply measurable_inv hA, withDensity_apply _ hA,
    withDensity_apply _ (measurable_inv hA), ← lintegral_indicator hA,
    ← lintegral_indicator (measurable_inv hA), ← lintegral_inv_eq_self]
  congr 1
  funext g
  simp only [Set.indicator, hL, neg_neg, ideleClassSobolevInversion_density]
  classical
  exact if_congr (by simp) rfl rfl

/-- Inversion as an isometry between weighted L² spaces for reflected intervals, on an
abstract group with an inversion-invariant measure. -/
private theorem ideleClassSobolevInversion_aux {G : Type*} [CommGroup G]
    [MeasurableSpace G] [MeasurableInv G] (μ : Measure G) [μ.IsInvInvariant] (L : G → ℝ)
    (hLm : Measurable L) (hL : ∀ g, L g⁻¹ = - L g) (α β s : ℝ) :
    ∃! J : CompactIntervalSobolev μ L α β s ≃ₗᵢ[ℂ] CompactIntervalSobolev μ L (-β) (-α) s,
      ∀ u, (J u : G → ℂ) =ᵐ[μ] fun g ↦ u g⁻¹ := by
  have h := ideleClassSobolevInversion_measurePreserving μ L hL α β s
  have h' : MeasurePreserving Inv.inv
      (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity α β s (L x)))
      (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity (-β) (-α) s (L x))) := by
    simpa only [neg_neg] using ideleClassSobolevInversion_measurePreserving μ L hL (-β) (-α) s
  have hpos (a b : ℝ) (x : G) : ENNReal.ofReal (intervalSobolevDensity a b s (L x)) ≠ 0 := by
    refine (ENNReal.ofReal_pos.mpr ?_).ne'
    unfold intervalSobolevDensity
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _)) (by positivity)
  have hmeas (a b : ℝ) :
      Measurable fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (L x)) := by
    unfold intervalSobolevDensity
    fun_prop
  -- almost-everywhere statements for the weighted measure give ones for μ
  have hae (a b : ℝ) {f g : G → ℂ}
      (hfg : f =ᵐ[μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (L x))] g) :
      f =ᵐ[μ] g := by
    rw [Filter.EventuallyEq, ae_withDensity_iff (hmeas a b)] at hfg
    filter_upwards [hfg] with x hx using hx (hpos a b x)
  let T := Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ Inv.inv h
  let T' := Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ Inv.inv h'
  have hTT' (u) : T (T' u) = u := by
    apply Lp.ext
    refine (Lp.coeFn_compMeasurePreserving _ h).trans ?_
    refine ((h.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving u h'))).trans ?_
    filter_upwards with x
    simp
  have hT'T (u) : T' (T u) = u := by
    apply Lp.ext
    refine (Lp.coeFn_compMeasurePreserving _ h').trans ?_
    refine ((h'.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving u h))).trans ?_
    filter_upwards with x
    simp
  let J : CompactIntervalSobolev μ L α β s ≃ₗᵢ[ℂ] CompactIntervalSobolev μ L (-β) (-α) s :=
    { toLinearEquiv := LinearEquiv.ofLinearMap T.toLinearMap T'.toLinearMap
        (LinearMap.ext hTT') (LinearMap.ext hT'T)
      norm_map' := T.norm_map }
  refine ⟨J, fun u ↦ hae (-β) (-α) (Lp.coeFn_compMeasurePreserving u h), ?_⟩
  intro J₂ hJ₂
  refine LinearIsometryEquiv.ext fun u ↦ Lp.ext ?_
  have h₁ := hJ₂ u
  have h₂ := hae (-β) (-α) (Lp.coeFn_compMeasurePreserving u h)
  exact (withDensity_absolutelyContinuous _ _).ae_le (h₁.trans h₂.symm)

/-- Paper: Theorem 10.1.2.1, p. 437. Inversion gives an isometric linear
equivalence of the ambient Sobolev spaces for opposite intervals.
Deviation: The target interval is [-β,-α]. Inversion is an automorphism at I = -I. -/
theorem existsUnique_ideleClassSobolevInversion (α β s : ℝ) (_hI : α ≤ β) (_hs : 0 ≤ s) :
    ∃! J : W𝔽(α, β, s) ≃ₗᵢ[ℂ] W𝔽(-β, -α, s),
      ∀ u, (J u : C𝔽 → ℂ) =ᵐ[μ𝔽] fun g ↦ u g⁻¹ := by
  have : (μ𝔽).Regular := (ideleClassTamagawaMeasure_isWeil F).2.1
  have hLm : Measurable fun g : C𝔽 ↦ Real.log (((m𝔽 g).val : ℝ)) :=
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).log
      fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne').measurable
  exact ideleClassSobolevInversion_aux μ𝔽 _ hLm
    (fun g ↦ by simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv]) α β s

local notation "J𝔽(" hI ", " hs ")" =>
  (existsUnique_ideleClassSobolevInversion (F := F) _ _ _ hI hs).exists.choose

/-- If a constant is bounded by `K / r` for arbitrarily large `r`, it vanishes. -/
private theorem adelePolarSubspace_fourier_eq_zero (c : ℂ) (K T : ℝ)
    (h : ∀ R : ℝ, T < R → ‖c‖ ≤ K * R⁻¹) : c = 0 := by
  by_contra hc
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set R : ℝ := max (T + 1) ((|K| + 1) / ‖c‖ + 1) with hR
  have hR1 : T < R := (lt_add_one T).trans_le (le_max_left _ _)
  have hR2 : (|K| + 1) / ‖c‖ < R := (lt_add_one _).trans_le (le_max_right _ _)
  have hR0 : 0 < R := (div_pos (by positivity) hpos).trans hR2
  have h1 := h R hR1
  have h2 : K * R⁻¹ < ‖c‖ := by
    rw [← div_eq_mul_inv, div_lt_iff₀ hR0]
    rw [div_lt_iff₀ hpos] at hR2
    nlinarith [le_abs_self K]
  linarith

/-- Riemann–Roch for a theta transform, together with decay at large norm, forces the
double Fourier transform of a test with two vanishing polar values to vanish at zero.
Stated for abstract data, so that it elaborates without unfolding the adelic types. -/
private theorem adelePolarSubspace_fourier_abstract {B X : Type*} [InvolutiveInv X]
    (Θ : B → X → ℂ) (Fo : B → B) (e : B → ℂ) (n : X → ℝ)
    (hn : ∀ g, n g⁻¹ = (n g)⁻¹) (hpos : ∀ g, 0 < n g)
    (hRR : ∀ f g, Θ f g = (n g)⁻¹ • Θ (Fo f) g⁻¹ + (n g)⁻¹ • e (Fo f) - e f)
    (hdec : ∀ f, ∃ K T : ℝ, 0 < K ∧ 0 < T ∧ ∀ g, T < n g → ‖Θ f g‖ ≤ K * ((n g) ^ 1)⁻¹)
    (hsurj : ∀ R : ℝ, 0 < R → ∃ g, n g = R)
    (f : B) (hf0 : e f = 0) (hF0 : e (Fo f) = 0) : e (Fo (Fo f)) = 0 := by
  have hid (g : X) : Θ f g = Θ (Fo (Fo f)) g + e (Fo (Fo f)) := by
    have h1 := hRR f g
    have h2 := hRR (Fo f) g⁻¹
    have hr : n g ≠ 0 := (hpos g).ne'
    simp only [hf0, hF0, smul_zero, add_zero, sub_zero, inv_inv, hn] at h1 h2
    rw [h1, h2, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hr, one_smul, one_smul]
  obtain ⟨K₁, T₁, -, -, hd₁⟩ := hdec f
  obtain ⟨K₂, T₂, -, -, hd₂⟩ := hdec (Fo (Fo f))
  refine adelePolarSubspace_fourier_eq_zero _ (K₁ + K₂) (max T₁ (max T₂ 0)) fun R hR ↦ ?_
  have hR0 : 0 < R := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hR)
  obtain ⟨g, hgR⟩ := hsurj R hR0
  have hT₁ : T₁ < n g := hgR ▸ (le_max_left _ _).trans_lt hR
  have hT₂ : T₂ < n g := hgR ▸ (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hR)
  have e₁ := hd₁ g hT₁
  have e₂ := hd₂ g hT₂
  rw [hgR, pow_one] at e₁ e₂
  rw [eq_sub_of_add_eq' (hid g).symm]
  calc _ ≤ ‖Θ f g‖ + ‖Θ (Fo (Fo f)) g‖ := norm_sub_le _ _
    _ ≤ K₁ * R⁻¹ + K₂ * R⁻¹ := add_le_add e₁ e₂
    _ = _ := by ring

/-- Paper: (10.1.2.2)–(10.1.2.4), pp. 437–438. Fourier transform preserves
the polar-free test space, so the global theta Fourier transform restricts to it. -/
theorem adelePolarSubspace_fourier (f : ℬ₀) :
    adeleSchwartzFourier f.val ∈ adelePolarSubspace F := by
  have hz := (mem_adelePolarSubspace (F := F) f.val).mp f.property
  rw [mem_adelePolarSubspace]
  refine ⟨hz.2, ?_⟩
  have hsurj : Surjective (ideleClassNorm F) :=
    (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  have hn (g : C𝔽) :
      ((ideleClassNorm F g⁻¹ : NNReal) : ℝ) = ((ideleClassNorm F g : NNReal) : ℝ)⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
  have hpos (g : C𝔽) : 0 < ((ideleClassNorm F g : NNReal) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))
  have hR (R : ℝ) (hR : 0 < R) :
      ∃ g : C𝔽, ((ideleClassNorm F g : NNReal) : ℝ) = R := by
    obtain ⟨g, hg⟩ := hsurj (Units.mk0 R.toNNReal (by simpa using hR))
    exact ⟨g, by rw [hg, Units.val_mk0, Real.coe_toNNReal _ hR.le]⟩
  have hRR := adelicTheta_riemannRoch (F := F)
  have hdec := fun f ↦ adelicTheta_decay_large (F := F) f 1
  exact adelePolarSubspace_fourier_abstract (fun f g ↦ adelicTheta (F := F) f g)
    adeleSchwartzFourier (fun f ↦ f (Multiplicative.ofAdd 0))
    (fun g ↦ ((ideleClassNorm F g : NNReal) : ℝ)) hn hpos hRR hdec hR f.val hz.1 hz.2

local notation "fourier₀(" f ")" =>
  (⟨adeleSchwartzFourier (f : ℬ₀).val, adelePolarSubspace_fourier f⟩ : ℬ₀)

/-- Paper: (10.1.2.4), p. 438. The weight-a theta function of the Fourier test
equals inversion of the theta function at complementary weight 1-a. -/
theorem globalThetaSobolev_fourier_weight (a : ℝ) (f : ℬ₀) (g : C𝔽) :
    modulationWeight m𝔽 a (θ𝔽(fourier₀(f))) g =
      modulationWeight m𝔽 (1 - a) (θ𝔽(f)) g⁻¹ := by
  have weights (r t : ℝ) (x y : ℂ) (hr : 0 < r) (ht : t = r⁻¹) (hy : y = r • x) :
      (↑(r ^ a) : ℂ) * x = (↑(t ^ (1 - a)) : ℂ) * y := by
    have hpow : (r⁻¹) ^ (1 - a) * r = r ^ a := by
      rw [← Real.rpow_neg_eq_inv_rpow]
      calc
        _ = r ^ (-(1 - a)) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = r ^ a := by
          rw [← Real.rpow_add hr]
          congr 1
          ring
    rw [ht, hy, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hpow]
  let r : ℝ := ((ideleClassNorm F g).val : ℝ)
  have hr : 0 < r := NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))
  have hinv : ((ideleClassNorm F g⁻¹).val : ℝ) = r⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, r]
  have hz := (mem_adelePolarSubspace (F := F) f.val).mp f.property
  have hθ : adelicTheta (F := F) f.val g⁻¹ =
      r • adelicTheta (F := F) (adeleSchwartzFourier (F := F) f.val) g := by
    simpa only [hz.1, hz.2, smul_zero, add_zero, sub_zero, inv_inv, hinv]
      using adelicTheta_riemannRoch (F := F) f.val g⁻¹
  exact weights r ((ideleClassNorm F g⁻¹).val : ℝ) _ _ hr hinv hθ

/-- A continuous linear map that preserves a submodule, preserves the kernel of a linear map
on it, and is an involution modulo that kernel induces a unique continuous linear automorphism
of the quotient. Stated for abstract modules, so that it elaborates without unfolding the
Schwartz–Bruhat instances. -/
private theorem existsUnique_globalPolarFreeThetaFourier_quotient {M N : Type*}
    [AddCommGroup M] [Module ℂ M] [TopologicalSpace M] [AddCommGroup N] [Module ℂ N]
    (P : Submodule ℂ M) (θ : M →ₗ[ℂ] N) (Φ : M →L[ℂ] M) (φ : M → M) (hΦ : ∀ f, Φ f = φ f)
    (hP : ∀ f : P, φ f ∈ P) (hker : ∀ f : P, θ f = 0 → θ (φ f) = 0)
    (hinv : ∀ f : P, θ (φ (φ f)) = θ f) :
    ∃! T : (P ⧸ (LinearMap.ker θ).comap P.subtype) ≃L[ℂ]
        (P ⧸ (LinearMap.ker θ).comap P.subtype),
      ∀ f : P, T (Submodule.Quotient.mk f) = Submodule.Quotient.mk ⟨φ f, hP f⟩ := by
  set Q := (LinearMap.ker θ).comap P.subtype
  let Φ₀ : P →L[ℂ] P := (Φ.comp P.subtypeL).codRestrict P fun f ↦ by
    rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, hΦ]
    exact hP f
  have hΦ₀ (f : P) : Φ₀ f = ⟨φ f, hP f⟩ := Subtype.ext (hΦ f)
  have hQ : Q ≤ (Q.mkQL.comp Φ₀).ker := by
    intro f hf
    change Q.mkQ (Φ₀ f) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hΦ₀]
    exact hker f hf
  let T₀ := Q.liftQL (Q.mkQL.comp Φ₀) hQ
  have hT₀ (f : P) : T₀ (Submodule.Quotient.mk f) = Submodule.Quotient.mk ⟨φ f, hP f⟩ := by
    change Q.mkQ (Φ₀ f) = _
    rw [hΦ₀]
    rfl
  have hTT (x : P ⧸ Q) : T₀ (T₀ x) = x := by
    refine Submodule.Quotient.induction_on _ x fun f ↦ ?_
    rw [hT₀, hT₀, Submodule.Quotient.eq, Submodule.mem_comap, LinearMap.mem_ker, map_sub,
      map_sub]
    change θ (φ (φ f)) - θ f = 0
    rw [hinv, sub_self]
  refine ⟨ContinuousLinearEquiv.equivOfInverse T₀ T₀ hTT hTT, hT₀, fun T hT ↦ ?_⟩
  refine ContinuousLinearEquiv.ext (funext fun x ↦ ?_)
  refine Submodule.Quotient.induction_on _ x fun f ↦ ?_
  exact (hT f).trans (hT₀ f).symm

/-- Riemann–Roch for a theta transform, for a test whose polar values vanish together with
those of its Fourier transform: the Fourier transform preserves vanishing of theta, and the
double Fourier transform has the same theta. Stated for abstract data, so that it elaborates
without unfolding the adelic types. -/
private theorem existsUnique_globalPolarFreeThetaFourier_rr {B X : Type*} [InvolutiveInv X]
    (Θ : B → X → ℂ) (Fo : B → B) (e : B → ℂ) (n : X → ℝ)
    (hn : ∀ g, n g⁻¹ = (n g)⁻¹) (hpos : ∀ g, 0 < n g)
    (hRR : ∀ f g, Θ f g = (n g)⁻¹ • Θ (Fo f) g⁻¹ + (n g)⁻¹ • e (Fo f) - e f)
    (f : B) (hf0 : e f = 0) (hF0 : e (Fo f) = 0) :
    ((∀ g, Θ f g = 0) → ∀ g, Θ (Fo f) g = 0) ∧
      (e (Fo (Fo f)) = 0 → ∀ g, Θ (Fo (Fo f)) g = Θ f g) := by
  refine ⟨fun hΘ g ↦ ?_, fun hFF0 g ↦ ?_⟩
  · have h := hRR f g⁻¹
    simp only [hf0, hF0, smul_zero, add_zero, sub_zero, inv_inv, hn, hΘ] at h
    exact (smul_eq_zero.mp h.symm).resolve_left (hpos g).ne'
  · have h1 := hRR f g
    have h2 := hRR (Fo f) g⁻¹
    have hr : n g ≠ 0 := (hpos g).ne'
    simp only [hf0, hF0, smul_zero, add_zero, sub_zero, inv_inv, hn] at h1 h2
    rw [h1, h2, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hr, one_smul, one_smul, hFF0,
      add_zero]

/-- The Fourier transform of a polar-free test whose theta vanishes has vanishing theta. -/
private theorem existsUnique_globalPolarFreeThetaFourier_ker (f : ℬ₀)
    (hf : adelicThetaLinearMap F f.val = 0) :
    adelicThetaLinearMap F (adeleSchwartzFourier f.val) = 0 := by
  have hz := (mem_adelePolarSubspace (F := F) f.val).mp f.property
  have hn (g : C𝔽) :
      ((ideleClassNorm F g⁻¹ : NNReal) : ℝ) = ((ideleClassNorm F g : NNReal) : ℝ)⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
  have hpos (g : C𝔽) : 0 < ((ideleClassNorm F g : NNReal) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))
  have h := (existsUnique_globalPolarFreeThetaFourier_rr (fun f g ↦ adelicTheta (F := F) f g)
    adeleSchwartzFourier (fun f ↦ f (Multiplicative.ofAdd 0))
    (fun g ↦ ((ideleClassNorm F g : NNReal) : ℝ)) hn hpos (adelicTheta_riemannRoch (F := F))
    f.val hz.1 hz.2).1 fun g ↦ DFunLike.congr_fun hf g
  exact ContinuousMap.ext h

/-- The double Fourier transform of a polar-free test has the same theta. -/
private theorem existsUnique_globalPolarFreeThetaFourier_inv (f : ℬ₀) :
    adelicThetaLinearMap F (adeleSchwartzFourier (adeleSchwartzFourier f.val)) =
      adelicThetaLinearMap F f.val := by
  have hz := (mem_adelePolarSubspace (F := F) f.val).mp f.property
  have hz' := (mem_adelePolarSubspace (F := F) (adeleSchwartzFourier f.val)).mp
    (adelePolarSubspace_fourier f)
  have hn (g : C𝔽) :
      ((ideleClassNorm F g⁻¹ : NNReal) : ℝ) = ((ideleClassNorm F g : NNReal) : ℝ)⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
  have hpos (g : C𝔽) : 0 < ((ideleClassNorm F g : NNReal) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))
  have h := (existsUnique_globalPolarFreeThetaFourier_rr (fun f g ↦ adelicTheta (F := F) f g)
    adeleSchwartzFourier (fun f ↦ f (Multiplicative.ofAdd 0))
    (fun g ↦ ((ideleClassNorm F g : NNReal) : ℝ)) hn hpos (adelicTheta_riemannRoch (F := F))
    f.val hz.1 hz.2).2 hz'.2
  exact ContinuousMap.ext h

/-- Paper: Theorem 10.1.2.1, pp. 437–438. The polar-free theta quotient has the
continuous Fourier automorphism induced by the adelic transform of its tests. -/
theorem existsUnique_globalPolarFreeThetaFourier :
    ∃! T : Θ₀ ≃L[ℂ] Θ₀, ∀ f : ℬ₀,
      T (Submodule.Quotient.mk f) = Submodule.Quotient.mk (fourier₀(f)) := by
  obtain ⟨Φ, hΦ⟩ := exists_adeleFourier_clm (F := F)
  exact existsUnique_globalPolarFreeThetaFourier_quotient (adelePolarSubspace F)
    (adelicThetaLinearMap F) Φ adeleSchwartzFourier hΦ adelePolarSubspace_fourier
    existsUnique_globalPolarFreeThetaFourier_ker existsUnique_globalPolarFreeThetaFourier_inv

local notation "Fourier𝔽" => (existsUnique_globalPolarFreeThetaFourier (F := F)).exists.choose

/-- A map that intertwines two maps through a surjection of their common domain sends the
range of the first onto the range of the second. -/
private theorem exists_globalThetaSobolevInversion_image {X W₁ W₂ : Type*} (k : W₁ → W₂)
    (e₁ : X → W₁) (e₂ : X → W₂) (Fo : X → X) (hFo : Surjective Fo)
    (h : ∀ x, k (e₁ x) = e₂ (Fo x)) : k '' range e₁ = range e₂ := by
  rw [← range_comp]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Fo x, (h x).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := hFo x
    exact ⟨z, h z⟩

/-- Inversion carries the weight-a theta embedding of a polar-free test to the weight-(1-a)
theta embedding of its Fourier transform. -/
private theorem exists_globalThetaSobolevInversion_mk (a : ℝ) {α β s : ℝ} (hI : α ≤ β)
    (hs : 0 ≤ s) (f : ℬ₀) :
    J𝔽(hI, hs) (E𝔽(a, hI, hs) (Submodule.Quotient.mk f)) =
      E𝔽(1 - a, neg_le_neg hI, hs) (Submodule.Quotient.mk (fourier₀(f))) := by
  have : (μ𝔽).Regular := (ideleClassTamagawaMeasure_isWeil F).2.1
  have hinvMP : MeasurePreserving (fun g : C𝔽 ↦ g⁻¹) μ𝔽 μ𝔽 := Measure.measurePreserving_inv μ𝔽
  have hK := (existsUnique_ideleClassSobolevInversion (F := F) α β s hI hs).exists.choose_spec
  have hE₁ := (existsUnique_globalThetaSobolevEmbedding (F := F) a α β s hI hs).exists.choose_spec.2
  have hE₂ := (existsUnique_globalThetaSobolevEmbedding (F := F) (1 - a) (-β) (-α) s
    (neg_le_neg hI) hs).exists.choose_spec.2
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
  have h₂ := hinvMP.quasiMeasurePreserving.ae_eq_comp (hE₁ f)
  filter_upwards [hK (E𝔽(a, hI, hs) (Submodule.Quotient.mk f)), h₂, hE₂ (fourier₀(f))]
    with g hg h₂ h₃
  rw [hg, h₃]
  refine h₂.trans ?_
  have hw := globalThetaSobolev_fourier_weight (F := F) (1 - a) f g
  rw [sub_sub_cancel] at hw
  exact hw.symm

/-- Inversion intertwines the weight-a and weight-(1-a) theta embeddings with the Fourier
automorphism of the polar-free theta space. -/
private theorem exists_globalThetaSobolevInversion_key (a : ℝ) {α β s : ℝ} (hI : α ≤ β)
    (hs : 0 ≤ s) (u : Θ₀) :
    J𝔽(hI, hs) (E𝔽(a, hI, hs) u) = E𝔽(1 - a, neg_le_neg hI, hs) (Fourier𝔽 u) := by
  have hFo := (existsUnique_globalPolarFreeThetaFourier (F := F)).exists.choose_spec
  induction u using Quot.ind with
  | mk f =>
    exact (exists_globalThetaSobolevInversion_mk a hI hs f).trans
      (congrArg (E𝔽(1 - a, neg_le_neg hI, hs)) (hFo f).symm)

/-- Paper: Theorem 10.1.2.1, (10.1.2.1), and (10.1.2.5), pp. 437–438.
Ambient inversion restricts to an isometric equivalence of the weighted theta
completions and intertwines the weighted embeddings with Fourier transform.
Deviation: The target uses weight 1-a and reflected interval [-β,-α]. In the
commuting diagram each horizontal arrow uses the weight of its own target. -/
theorem exists_globalThetaSobolevInversion (a : ℝ) {α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s) :
    ∃ J : H𝔽(a, hI, hs) ≃ₗᵢ[ℂ] H𝔽(1 - a, neg_le_neg hI, hs),
      (∀ u, (J u : W𝔽(-β, -α, s)) = J𝔽(hI, hs) u) ∧
      ∀ u : Θ₀, J (j𝔽(a, hI, hs) u) =
        j𝔽(1 - a, neg_le_neg hI, hs) (Fourier𝔽 u) := by
  refine ⟨((J𝔽(hI, hs)).submoduleMap _).trans (LinearIsometryEquiv.ofEq _ _ ?_),
    fun _ ↦ rfl, fun u ↦ Subtype.ext (exists_globalThetaSobolevInversion_key a hI hs u)⟩
  apply SetLike.coe_injective
  rw [Submodule.map_coe, Submodule.topologicalClosure_coe, Submodule.topologicalClosure_coe]
  change (J𝔽(hI, hs)).toHomeomorph '' closure (range (E𝔽(a, hI, hs))) =
    closure (range (E𝔽(1 - a, neg_le_neg hI, hs)))
  rw [Homeomorph.image_closure]
  exact congrArg closure (exists_globalThetaSobolevInversion_image _ _ _ _ (Fourier𝔽).surjective
    (exists_globalThetaSobolevInversion_key a hI hs))

/-- Inversion intertwines left translation by `g` with left translation by `g⁻¹`, for
closed subspaces of weighted L² spaces over an abstract commutative group. -/
private theorem globalThetaSobolevInversion_mem_isotype_key {G : Type*} [CommGroup G]
    [MeasurableSpace G] (μ : Measure G) {ν₁ : Measure G} (ν₂ : Measure G) (hν₂ : ν₂ ≪ μ)
    (hinv : Measure.QuasiMeasurePreserving (fun x : G ↦ x⁻¹) μ μ)
    (hmul : ∀ g : G, Measure.QuasiMeasurePreserving (fun x ↦ g * x) μ μ)
    (H₁ : Submodule ℂ (Lp ℂ 2 ν₁)) (H₂ : Submodule ℂ (Lp ℂ 2 ν₂))
    (Jamb : Lp ℂ 2 ν₁ → Lp ℂ 2 ν₂) (hJamb : ∀ v, (Jamb v : G → ℂ) =ᵐ[μ] fun x ↦ v x⁻¹)
    (J : H₁ ≃ₗᵢ[ℂ] H₂) (hJ : ∀ u, (J u : Lp ℂ 2 ν₂) = Jamb u)
    (T₁ : G → Lp ℂ 2 ν₁ → Lp ℂ 2 ν₁) (hT₁ : ∀ g v, (T₁ g v : G → ℂ) =ᵐ[μ] fun x ↦ v (g⁻¹ * x))
    (T₂ : G → Lp ℂ 2 ν₂ → Lp ℂ 2 ν₂) (hT₂ : ∀ g v, (T₂ g v : G → ℂ) =ᵐ[μ] fun x ↦ v (g⁻¹ * x))
    (ρ₁ : G →* (H₁ →L[ℂ] H₁)) (hρ₁ : ∀ g u, (ρ₁ g u : Lp ℂ 2 ν₁) = T₁ g u)
    (ρ₂ : G →* (H₂ →L[ℂ] H₂)) (hρ₂ : ∀ g u, (ρ₂ g u : Lp ℂ 2 ν₂) = T₂ g u)
    (g : G) (v : H₁) : J (ρ₁ g v) = ρ₂ g⁻¹ (J v) := by
  apply Subtype.ext
  rw [hJ, hρ₂, hJ, hρ₁]
  apply Lp.ext
  apply hν₂.ae_le
  have e₁ := hJamb (T₁ g v)
  have e₂ := hT₂ g⁻¹ (Jamb v)
  have e₃ := Measure.QuasiMeasurePreserving.ae hinv (hT₁ g v)
  have e₄ := Measure.QuasiMeasurePreserving.ae (hmul g) (hJamb v)
  filter_upwards [e₁, e₂, e₃, e₄] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, inv_inv, h₃, h₄, mul_inv, mul_comm]

/-- An intertwiner of `g` with `g⁻¹` carries the isotype of a character to the isotype of
the inverse character, stated for abstract spaces. -/
private theorem globalThetaSobolevInversion_mem_isotype_iff {G K E₁ E₂ : Type*} [CommGroup G]
    [CommGroup K] [TopologicalSpace K] [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂]
    [NormedSpace ℂ E₂] (J : E₁ ≃ₗᵢ[ℂ] E₂) (ρ₁ : G →* (E₁ →L[ℂ] E₁))
    (ρ₂ : G →* (E₂ →L[ℂ] E₂)) (key : ∀ g v, J (ρ₁ g v) = ρ₂ g⁻¹ (J v)) (ι : K →* G)
    (ω : PontryaginDual K) (u : E₁) :
    J u ∈ actionIsotype (ρ₂.comp ι) ω⁻¹ ↔ u ∈ actionIsotype (ρ₁.comp ι) ω := by
  have hω (k : K) : ((ω⁻¹ : PontryaginDual K) k) = (ω k)⁻¹ := rfl
  rw [mem_actionIsotype, mem_actionIsotype]
  simp only [MonoidHom.comp_apply]
  constructor
  · intro h k
    apply J.injective
    rw [key, J.map_smul, ← map_inv, h, hω, map_inv, inv_inv]
  · intro h k
    rw [show ι k = (ι k⁻¹)⁻¹ by rw [map_inv, inv_inv], ← key, h, J.map_smul, hω, map_inv]

/-- Paper: Theorem 10.1.2.1, p. 437. The induced inversion sends each norm-one
isotype onto the inverse-character isotype of the reflected completion. -/
theorem globalThetaSobolevInversion_mem_isotype (a : ℝ) {α β s : ℝ} (hI : α ≤ β)
    (hs : 0 ≤ s) (ω : PontryaginDual C₁) (u : H𝔽(a, hI, hs)) :
    let J := (exists_globalThetaSobolevInversion (F := F) a hI hs).choose
    J u ∈ actionIsotype ((R𝔽(1 - a, neg_le_neg hI, hs)).comp (ideleClassNorm F).ker.subtype) ω⁻¹ ↔
      u ∈ actionIsotype ((R𝔽(a, hI, hs)).comp (ideleClassNorm F).ker.subtype) ω := by
  intro J
  have : (μ𝔽).Regular := (ideleClassTamagawaMeasure_isWeil F).2.1
  have hinvMP : MeasurePreserving (fun g : C𝔽 ↦ g⁻¹) μ𝔽 μ𝔽 := Measure.measurePreserving_inv μ𝔽
  have hJ := (exists_globalThetaSobolevInversion (F := F) a hI hs).choose_spec.1
  have hR := (exists_globalThetaSobolevAction (F := F) a hI hs).choose_spec.1
  have hR' := (exists_globalThetaSobolevAction (F := F) (1 - a) (neg_le_neg hI) hs).choose_spec.1
  have hinv := (existsUnique_ideleClassSobolevInversion (F := F) α β s hI hs).exists.choose_spec
  have hT₁ := hardySobolevTranslation_apply μ𝔽 m𝔽 α β s hI hs
  have hT₂ := hardySobolevTranslation_apply μ𝔽 m𝔽 (-β) (-α) s (neg_le_neg hI) hs
  have key := globalThetaSobolevInversion_mem_isotype_key μ𝔽 _
    (withDensity_absolutelyContinuous μ𝔽 _) hinvMP.quasiMeasurePreserving
    (fun g ↦ (measurePreserving_mul_left μ𝔽 g).quasiMeasurePreserving) _ _ _ hinv J hJ _ hT₁ _ hT₂
    _ hR _ hR'
  exact globalThetaSobolevInversion_mem_isotype_iff J _ _ key (ideleClassNorm F).ker.subtype ω u

-- TODO(paper-gap): The unbounded multiplier argument on p. 438 is on the ambient W_I^s,
-- whereas necessity in the theorem needs unboundedness on the weighted theta subspace.

/-- Paper: Theorem 10.1.2.1(1)–(2), (10.1.2.2), pp. 437–438. On a symmetric compact
interval, the global Fourier transform extends uniquely to a continuous linear
automorphism of the same weighted completion exactly at weight one half. -/
theorem globalThetaSobolev_fourier_extension_iff (a α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let hI := (neg_nonpos.mpr hα).trans hα
    (∃! T : H𝔽(a, hI, hs) ≃L[ℂ] H𝔽(a, hI, hs), ∀ u : Θ₀,
      T (j𝔽(a, hI, hs) u) = j𝔽(a, hI, hs) (Fourier𝔽 u)) ↔ a = 1 / 2 := by sorry

-- TODO(paper-gap): The announcement on p. 435 extends beyond the degree-zero
-- local result on p. 438. For ℚ and S = {∞}, at a = 1/2, I = {0}, the even
-- Gaussians exp(-πx²) cos(2πNx) have bounded input norms for each s > 0.
-- Their Fourier transforms have a Gaussian peak at N, with squared weighted
-- norm bounded below by a positive constant times (log N)^s.

/-- Paper: (10.1.2.6), p. 438. The local weighted L² completion of §5.4
identifies isometrically with the degree-zero Sobolev completion at weight one half.
On test representatives the isometry multiplies by the square root of the norm. -/
theorem sLocalThetaSobolev_halfWeight_equiv :
    let ha : (0 : ℝ) < 1 / 2 := one_half_pos
    let hp : (0 : ℝ) < 1 / 2 + 0 := add_pos_of_pos_of_nonneg ha le_rfl
    ∃ T : SLocalThetaL2 F S ≃ₗᵢ[ℂ] Hₛ(ha, le_refl (0 : ℝ), le_refl (0 : ℝ), hp),
      ∀ u : SLocalThetaL2 F S,
        ((T u).val : Jₛ → ℂ) =ᵐ[μₛ] modulationWeight mₛ (1 / 2) (⇑u.val) := by sorry

end Fourier

end RiemannMasullo
