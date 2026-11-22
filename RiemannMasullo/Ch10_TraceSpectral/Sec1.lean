module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec4
public import RiemannMasullo.Ch06_LocalGlobal.Sec3
public import RiemannMasullo.Ch09_HardySobolev.Sec3

import all RiemannMasullo.AppA_AlgebraicNT.Sec3

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
    DenseRange (j𝔽(a, hI, hs)) := by sorry

/-- Paper: Definition 10.1.1.1(2), p. 434. The weighted S-local test classes are
dense in the local Sobolev completion.
Deviation: Sanity check for the closure model at the admissible exponents. -/
theorem sLocalThetaSobolev_dense {a α β s : ℝ} (ha : 0 < a) (hI : α ≤ β)
    (hs : 0 ≤ s) (hp : 0 < a + α) :
    DenseRange (jₛ(ha, hI, hs, hp)) := by sorry

/-- Paper: Remark 10.1.1.2, pp. 434–435. The original S-local left action
extends jointly continuously to the norm completion via the completion map.
Deviation: The smallest effective exponent a + α is strictly positive. -/
theorem exists_sLocalThetaSobolevUnweightedAction {a α β s : ℝ} (ha : 0 < a)
    (hI : α ≤ β) (hs : 0 ≤ s) (hp : 0 < a + α) :
    ∃ ρ : Jₛ →* (Hₛ(ha, hI, hs, hp) →L[ℂ] Hₛ(ha, hI, hs, hp)),
      Continuous (fun p : Jₛ × Hₛ(ha, hI, hs, hp) ↦ ρ p.1 p.2) ∧
      ∀ (g : Jₛ) (u : Θₛ), ρ g (jₛ(ha, hI, hs, hp) u) = jₛ(ha, hI, hs, hp) (ρₛ g u) :=
  by sorry

/-- Paper: Lemma 10.1.1.3, p. 435. The continuous weighted embedding pulls
the ambient norm back to the norm in (10.1.1.6).
Deviation: Use the Haar measure on the full idele class group, denoted μ̄ in Appendix A.3. -/
theorem globalThetaSobolev_norm (a : ℝ) {α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s) (f : ℬ₀) :
    let w := fun g : C𝔽 ↦ ‖θ𝔽(f) g‖ ^ 2 *
      intervalSobolevDensity (a + α) (a + β) s (logNorm(m𝔽) g)
    Integrable w μ𝔽 ∧ ‖E𝔽(a, hI, hs) (Submodule.Quotient.mk f)‖ =
      Real.sqrt (∫ g, w g ∂μ𝔽) := by sorry

/-- Paper: Lemma 10.1.1.3(1), p. 435. The global completion is a closed,
complete and separable subspace of the ambient Hilbert space. -/
theorem globalThetaSobolev_closed_complete_separable (a : ℝ) {α β s : ℝ}
    (hI : α ≤ β) (hs : 0 ≤ s) :
    IsClosed (H𝔽(a, hI, hs) : Set W𝔽(α, β, s)) ∧
      CompleteSpace (H𝔽(a, hI, hs)) ∧ TopologicalSpace.SeparableSpace (H𝔽(a, hI, hs)) := by sorry

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

/-- Paper: Definition 10.1.1.1(1) and Lemma 10.1.1.3, pp. 434–435.
The identity on functions compares the Tamagawa norm with the canonical norm of §9.2.
Deviation: The two full Haar measures differ by the mass of the norm-one classes. -/
theorem globalThetaAmbient_equiv_canonical (hm : IsModulation m𝔽) (α β s : ℝ) :
    ∃ e : W𝔽(α, β, s) ≃L[ℂ] ModulatedIntervalSobolev m𝔽 hm α β s,
      ∀ u, (e u : C𝔽 → ℂ) =ᵐ[μ𝔽] u ∧
        ‖u‖ = Real.sqrt (Measure.real μ𝔽₁ univ) * ‖e u‖ := by sorry

/-- Paper: Definition 10.1.1.1(2) and Lemma 10.1.1.4, pp. 434–436.
The identity on S-local functions compares the norm in (10.1.1.5) with §9.2.
Deviation: The Tamagawa squared norm includes the mass of the norm-one quotient. -/
theorem sLocalThetaAmbient_equiv_canonical (hm : IsModulation mₛ) (α β s : ℝ) :
    ∃ e : Wₛ(α, β, s) ≃L[ℂ] ModulatedIntervalSobolev mₛ hm α β s,
      ∀ u, (e u : Jₛ → ℂ) =ᵐ[μₛ] u ∧
        ‖u‖ = Real.sqrt (Measure.real μₛ₁ univ) * ‖e u‖ := by sorry

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

/-- Paper: Lemma 10.1.1.4(1), pp. 435–436. The weighted S-idele measure is
regular and finite on compact sets. -/
theorem sIdeleIntervalSobolevMeasure_regular (α β s : ℝ)
    (_hI : α ≤ β) (_hs : 0 ≤ s) :
    (sIdeleIntervalSobolevMeasure F S α β s).Regular := by sorry

/-- Paper: Lemma 10.1.1.4(1), pp. 435–436. The weighted S-idele measure is
invariant under left translation by the projected diagonal S-units. -/
theorem sIdeleIntervalSobolevMeasure_invariant (α β s : ℝ)
    (_hI : α ≤ β) (_hs : 0 ≤ s) :
    let ν := sIdeleIntervalSobolevMeasure F S α β s
    ∀ u : Iₛ, (QuotientGroup.mk u : Jₛ) = 1 →
      MeasurePreserving (fun g : Iₛ ↦ u * g) ν ν := by sorry

/-- Paper: Lemma 10.1.1.4(2), pp. 435–436. On the local test classes the
subspace norm is (10.1.1.7) and is continuous for the theta quotient topology.
Deviation: Use μ̄_S on J_{F,S}, as in (10.1.1.5) and Appendix A.3. The formula
also applies whenever the smallest effective exponent a + α is positive. -/
theorem sLocalThetaSobolev_norm {a α β s : ℝ} (ha : 0 < a) (hI : α ≤ β)
    (hs : 0 ≤ s) (hp : 0 < a + α) (f : ℬₛ) :
    let w := fun g : Jₛ ↦ ‖θₛ(f) g‖ ^ 2 *
      intervalSobolevDensity (a + α) (a + β) s (logNorm(mₛ) g)
    Integrable w μₛ ∧ ‖Eₛ(ha, hI, hs, hp) (Submodule.Quotient.mk f)‖ =
      Real.sqrt (∫ g, w g ∂μₛ) := by sorry

/-- Paper: Lemma 10.1.1.4(3), p. 436. The local completion is a closed,
complete and separable subspace of the ambient Hilbert space. -/
theorem sLocalThetaSobolev_closed_complete_separable {a α β s : ℝ} (ha : 0 < a)
    (hI : α ≤ β) (hs : 0 ≤ s) (hp : 0 < a + α) :
    IsClosed (Hₛ(ha, hI, hs, hp) : Set Wₛ(α, β, s)) ∧
      CompleteSpace (Hₛ(ha, hI, hs, hp)) ∧
      TopologicalSpace.SeparableSpace (Hₛ(ha, hI, hs, hp)) := by sorry

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
      ∫ g : Iₛ, u g * star (v g) ∂(sIdeleIntervalSobolevMeasure F S α β s) := by sorry

-- TODO(paper-gap): The global spaces in Proposition 10.1.1.5 drop the subscript 0.
-- At weight zero the usual rational adelic Gaussian does not have square-integrable theta.
-- The raw averages from (10.1.1.8) and (10.1.1.9) carry the norm-one Haar mass.

section GlobalIsotypes

variable {a α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s)

local notation "H" => ↥(H𝔽(a, hI, hs))
local notation "ρ₁" => (R𝔽(a, hI, hs)).comp (ideleClassNorm F).ker.subtype
local notation "Hω(" ω ")" => actionIsotype ρ₁ ω

/-- Paper: Proposition 10.1.1.5(1), p. 436. The global Pettis average for the
norm-one Tamagawa measure is a continuous open linear surjection onto its isotype.
Deviation: Use polar-free global theta functions, as in Definition 10.1.1.1(1). -/
theorem existsUnique_globalThetaSobolevAverage (ω : PontryaginDual C₁) :
    ∃! P : H →L[ℂ] Hω(ω),
      IsPettisIsotypicAverageOn μ𝔽₁ univ ρ₁ ω ((Hω(ω)).subtypeL.comp P) ∧
      Surjective P ∧ IsOpenMap P := by sorry

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

/-- Paper: Proposition 10.1.1.5(1), p. 437. The global raw average induces a
topological linear isomorphism from the completed homogeneous quotient to the isotype.
Deviation: Use polar-free tests. The completed coinvariant quotient is realized by
dividing the completed space by the closed span of the twisted differences. -/
theorem globalThetaSobolevAverage_quotient_equiv (ω : PontryaginDual C₁) :
    let D := (Submodule.span ℂ (range (fun p : C₁ × H ↦
      p.2 - star (ω p.1 : ℂ) • ρ₁ p.1 p.2))).topologicalClosure
    ∃ T : (H ⧸ D) ≃L[ℂ] Hω(ω), ∀ u : H, T (D.mkQ u) = P(ω) u := by sorry

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
      Surjective P ∧ IsOpenMap P := by sorry

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
    ∃ T : (H ⧸ D) ≃L[ℂ] Hω(ω), ∀ u : H, T (D.mkQ u) = P(ω) u := by sorry

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

/-- Paper: Theorem 10.1.2.1, p. 437. Inversion gives an isometric linear
equivalence of the ambient Sobolev spaces for opposite intervals.
Deviation: The target interval is [-β,-α]. Inversion is an automorphism at I = -I. -/
theorem existsUnique_ideleClassSobolevInversion (α β s : ℝ) (_hI : α ≤ β) (_hs : 0 ≤ s) :
    ∃! J : W𝔽(α, β, s) ≃ₗᵢ[ℂ] W𝔽(-β, -α, s),
      ∀ u, (J u : C𝔽 → ℂ) =ᵐ[μ𝔽] fun g ↦ u g⁻¹ := by sorry

local notation "J𝔽(" hI ", " hs ")" =>
  (existsUnique_ideleClassSobolevInversion (F := F) _ _ _ hI hs).exists.choose

/-- Paper: (10.1.2.2)–(10.1.2.4), pp. 437–438. Fourier transform preserves
the polar-free test space, so the global theta Fourier transform restricts to it. -/
theorem adelePolarSubspace_fourier (f : ℬ₀) :
    adeleSchwartzFourier f.val ∈ adelePolarSubspace F := by sorry

local notation "fourier₀(" f ")" =>
  (⟨adeleSchwartzFourier (f : ℬ₀).val, adelePolarSubspace_fourier f⟩ : ℬ₀)

/-- Paper: (10.1.2.4), p. 438. The weight-a theta function of the Fourier test
equals inversion of the theta function at complementary weight 1-a. -/
theorem globalThetaSobolev_fourier_weight (a : ℝ) (f : ℬ₀) (g : C𝔽) :
    modulationWeight m𝔽 a (θ𝔽(fourier₀(f))) g =
      modulationWeight m𝔽 (1 - a) (θ𝔽(f)) g⁻¹ := by sorry

/-- Paper: Theorem 10.1.2.1, pp. 437–438. The polar-free theta quotient has the
continuous Fourier automorphism induced by the adelic transform of its tests. -/
theorem existsUnique_globalPolarFreeThetaFourier :
    ∃! T : Θ₀ ≃L[ℂ] Θ₀, ∀ f : ℬ₀,
      T (Submodule.Quotient.mk f) = Submodule.Quotient.mk (fourier₀(f)) := by sorry

local notation "Fourier𝔽" => (existsUnique_globalPolarFreeThetaFourier (F := F)).exists.choose

/-- Paper: Theorem 10.1.2.1, (10.1.2.1), and (10.1.2.5), pp. 437–438.
Ambient inversion restricts to an isometric equivalence of the weighted theta
completions and intertwines the weighted embeddings with Fourier transform.
Deviation: The target uses weight 1-a and reflected interval [-β,-α]. In the
commuting diagram each horizontal arrow uses the weight of its own target. -/
theorem exists_globalThetaSobolevInversion (a : ℝ) {α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s) :
    ∃ J : H𝔽(a, hI, hs) ≃ₗᵢ[ℂ] H𝔽(1 - a, neg_le_neg hI, hs),
      (∀ u, (J u : W𝔽(-β, -α, s)) = J𝔽(hI, hs) u) ∧
      ∀ u : Θ₀, J (j𝔽(a, hI, hs) u) =
        j𝔽(1 - a, neg_le_neg hI, hs) (Fourier𝔽 u) := by sorry

/-- Paper: Theorem 10.1.2.1, p. 437. The induced inversion sends each norm-one
isotype onto the inverse-character isotype of the reflected completion. -/
theorem globalThetaSobolevInversion_mem_isotype (a : ℝ) {α β s : ℝ} (hI : α ≤ β)
    (hs : 0 ≤ s) (ω : PontryaginDual C₁) (u : H𝔽(a, hI, hs)) :
    let J := (exists_globalThetaSobolevInversion (F := F) a hI hs).choose
    J u ∈ actionIsotype ((R𝔽(1 - a, neg_le_neg hI, hs)).comp (ideleClassNorm F).ker.subtype) ω⁻¹ ↔
      u ∈ actionIsotype ((R𝔽(a, hI, hs)).comp (ideleClassNorm F).ker.subtype) ω := by sorry

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
