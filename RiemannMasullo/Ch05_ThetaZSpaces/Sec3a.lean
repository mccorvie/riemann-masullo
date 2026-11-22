module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
public import RiemannMasullo.Ch03_IdelicZeta.Sec4
public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.PiTopology

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
    IsLinearMap ℂ (fun f : ℬ(Fᵥ(v)) ↦ f - schwartzBruhatUnitTranslate π f) := by sorry

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
      (Units.val '' (Uᵥ(v) : Set Fᵥ(v)ˣ)).indicator (fun _ ↦ (1 : ℂ)) x := by sorry

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
    finitePlaceDifference v π f = finitePlaceDifference v π' f := by sorry

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
        Uᵥ(v) μᵥ(v) := by sorry

/-- Paper: Lemma 5.3.1.3, p. 241.
The formula for the local principal value produces a Schwartz–Bruhat test function. -/
theorem finitePlacePrincipalValue_mem (v : V) (π : Fᵥ(v)ˣ) (f : ℬ(Fᵥ(v))) :
    finitePlacePrincipalValueFun v π f ∈ schwartzBruhatSubmodule (Multiplicative Fᵥ(v)) :=
  by sorry

local notation "pvBundle(" v ", " π ")" =>
  (fun f : ℬ(Fᵥ(v)) ↦
    (⟨finitePlacePrincipalValueFun v π f, finitePlacePrincipalValue_mem v π f⟩ : ℬ(Fᵥ(v))))

/-- Paper: Lemma 5.3.1.3, p. 241.
The bundled local averaging formula is linear. -/
theorem finitePlacePrincipalValue_isLinear (v : V) (π : Fᵥ(v)ˣ) :
    IsLinearMap ℂ (pvBundle(v, π)) := by sorry

/-- Paper: Lemma 5.3.1.3, p. 241.
The local principal value formula is continuous. -/
theorem finitePlacePrincipalValue_continuous (v : V) (π : Fᵥ(v)ˣ) :
    @Continuous ℬ(Fᵥ(v)) ℬ(Fᵥ(v)) _ _
      ((finitePlacePrincipalValue_isLinear v π).mk' (pvBundle(v, π))).toFun :=
  by sorry

/-- Paper: Definition 5.3.1.2, p. 241.
The principal value is the identity minus the uniformizer pullback of the trivial-isotype
projection. A uniformizer is chosen from the discrete local valuation. -/
def finitePlacePrincipalValue (v : V) : ℬ(Fᵥ(v)) →L[ℂ] ℬ(Fᵥ(v)) :=
  let h := vval(v).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (h.choose : Fᵥ(v)) h.choose_spec.ne_zero
  ⟨(finitePlacePrincipalValue_isLinear v π).mk' (pvBundle(v, π)),
    finitePlacePrincipalValue_continuous v π⟩

/-- Paper: Definition 5.3.1.2 and Lemma 5.3.1.3, p. 241.
The scalar formula for the operator works with every choice of uniformizer. -/
theorem finitePlacePrincipalValue_spec (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) :
    ∀ (f : ℬ(Fᵥ(v))) (x : Multiplicative Fᵥ(v)),
      finitePlacePrincipalValue v f x = finitePlacePrincipalValueFun v π f x := by sorry

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

/-- Paper: Lemmas 5.3.1.1 and 5.3.1.3, pp. 240–241.
Weil's operator maps onto all tests vanishing at zero.
Deviation: The full evaluation kernel belongs to the averaged operator from (5.3.1.5). -/
theorem finitePlacePrincipalValue_range (v : V) :
    Set.range (finitePlacePrincipalValue v) =
      {f : ℬ(Fᵥ(v)) | f (Multiplicative.ofAdd 0) = 0} := by sorry

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

open Classical in
/-- Paper: Definition 5.3.1.4(1), p. 242.
On pure tensors the S-local operator acts by the local principal value in each selected factor. -/
theorem sAdelePrincipalValue_tmul {S S₀ : Finset V} (h₀ : S₀ ⊆ S)
    (f : ℬ(InfiniteAdeleRing F)) (g : ∀ w : S, ℬ(w.val.adicCompletion F)) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    sAdelePrincipalValue F h₀ (e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) =
      e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, if w.val ∈ S₀ then finitePlacePrincipalValue w.val (g w) else g w)) :=
  by sorry

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
      Submodule.Quotient.mk (sAdelePrincipalValue F h₀ f) := by sorry

/-- Paper: (5.3.1.10), p. 242.
On a class represented by a test function the global operator gives the class of its image. -/
theorem globalThetaPrincipalValue_mk (S₀ : Finset V) (f : ℬ(𝔸[F])) :
    globalThetaPrincipalValue F S₀ (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (adelePrincipalValue F S₀ f) := by sorry

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

/-- Paper: Lemma 5.3.1.5, p. 242.
The principal value commutes with passage from an S-local theta stage to a larger stage. -/
theorem sLocalThetaPrincipalValue_transition {S₀ S T : Finset V}
    (h₀ : S₀ ⊆ S) (hST : S ⊆ T) (hn : S₀.Nonempty) :
    (sLocalThetaTransition (F := F) hST).comp (sLocalThetaPrincipalValue F h₀) =
      (sLocalThetaPrincipalValue F (h₀.trans hST)).comp (sLocalThetaTransition hST) :=
  by sorry

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
    DistributionOrderLE (fun f : 𝒟(E) ↦ f x) 0 := by sorry

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
      schwartzBruhatDistributionSupport (T.comp e.symm.toContinuousLinearMap) := by sorry

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
    realDiracDerivative 1 f = -deriv (f : ℝ → ℂ) 0 := by sorry

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
      ∀ k : ℕ, iteratedDeriv k (f : ℝ → ℂ) 0 = 0 := by sorry

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

open Classical in
/-- Paper: Theorem 5.3.2.3, p. 245.
A multi-index supported in one coordinate acts by the corresponding power
of that coordinate's derivative. -/
theorem coordinateDerivative_single {ι A : Type*} [Fintype ι] [Monoid A] (derivative : ι → A)
    (i : ι) (k : ℕ) :
    coordinateDerivative derivative (Pi.single i k) = derivative i ^ k := by sorry

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

/-- Paper: Theorem 5.3.2.3(1), p. 245.
Inserting zeros into the normal coordinates gives a continuous linear restriction map
on compactly supported smooth functions. -/
theorem exists_testFunction_coordinatePlaneRestriction :
    ∃ R : 𝒟(ι ⊕ κ) →L[ℂ] 𝒟(κ), ∀ (f : 𝒟(ι ⊕ κ)) (y : Eᵣ(κ)),
      R f y = f (insertPlane y) := by sorry

/-- Paper: Theorem 5.3.2.3(1), p. 245.
Inserting zeros into the normal coordinates gives a continuous linear restriction map
on Schwartz functions. -/
theorem exists_schwartz_coordinatePlaneRestriction :
    ∃ R : 𝒮(ι ⊕ κ) →L[ℂ] 𝒮(κ), ∀ (f : 𝒮(ι ⊕ κ)) (y : Eᵣ(κ)),
      R f y = f (insertPlane y) := by sorry

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
    coordinatePlaneDiracTensor (0 : ι → ℕ) U f = U (R𝒟 f) := by sorry

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
      ∂𝒮[ι, β] (f.hasCompactSupport.toSchwartzMap f.contDiff) := by sorry

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
    schwartzWirtingerZ f z + schwartzWirtingerZBar f z = fderiv ℝ (f : ℂ → ℂ) z 1 := by sorry

/-- Paper: Theorem 5.3.2.5, p. 246.
The difference of the Wirtinger derivatives recovers the imaginary directional derivative
times i. -/
theorem schwartzWirtingerZBar_sub_z (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    schwartzWirtingerZBar f z - schwartzWirtingerZ f z =
      Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I := by sorry

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
    complexDiracDerivative 1 0 f = -schwartzWirtingerZ f 0 := by sorry

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
      ∀ k l : ℕ, (schwartzWirtingerZ^k) ((schwartzWirtingerZBar^l) f) 0 = 0 := by sorry

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
