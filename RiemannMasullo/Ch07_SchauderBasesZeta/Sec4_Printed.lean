module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec4

/-! # False claims printed in §7.4 -/

@[expose] public noncomputable section

open Classical Function IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 150000
set_option Elab.async false

local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "I[" F "]" => IdeleGroup (𝓞 F) F
local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "ω[" F ", " χ "]" => (χ : U[F]).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
    (ideleClassNorm F).ker →ₜ* C[F])
local notation "B" => SchwartzBergman (univ : Set ℝ)

local instance instIdeleClassT2Sec4Printed (F : Type*) [Field F] [NumberField F] :
    T2Space C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1

local instance instIdeleClassLocallyCompactSec4Printed (F : Type*) [Field F] [NumberField F] :
    LocallyCompactSpace C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1

/-- Paper: Theorem 7.4.1.1(2), equation (7.4.1.1), p. 366.
The printed spectral trace evaluates the test at the unshifted zero z. Its summation
variable ρ is z + a, so the printed weight and multiplicity use ρ − a = z.
The cited §7.1.4.2 family lives in the unshifted quotient. To type the reference
for general a, use its transport by f(s) ↦ f(s+a), which gives evaluation at z−a.
At a = 0 the statement and its counterexample require no transport. -/
def Printed.spectralNuclearity_trace : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)) (a : ℝ) (N : ℕ),
    0 < N → ∀ φ : BruhatCompactSupport C[F],
    let L := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
      (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    let Zeros := {z : ℂ // 0 < analyticOrderAt (L.val : ℂ → ℂ) z}
    let order := fun z : Zeros ↦ (analyticOrderAt (L.val : ℂ → ℂ) z.val).toNat
    let J := Σ z : Zeros, Fin (order z)
    let D := spectralNuclearityDenominator χ τ hτ a
    let Q := SpectralNuclearityQuotient χ τ hτ a
    ∀ (d : J → StrongDual ℂ Q) (b : J → Q),
      (∀ i f, d i (D.mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) →
      (∀ i j, d i (b j) = if i = j then 1 else 0) →
      let E := (Submodule.span ℂ (b '' {i | i.2.val < N})).topologicalClosure
      letI _instSpectralUniformSec4Printed : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
      ∃ (A : B →L[ℂ] B) (Aq : Q →L[ℂ] Q) (T : E →L[ℂ] E),
        (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) ∧
        (∀ f, Aq (D.mkQ f) = D.mkQ (A f)) ∧
        (∀ x : E, (T x).val = Aq x.val) ∧ IsStronglyNuclearOperator T ∧
        ∀ r : NuclearPresentation T, HasSum
          (fun n ↦ r.coeff n * r.functional n (r.vector n).val)
          (∑' z : Zeros, ((min N (order z) : ℕ) : ℂ) * nuclearityTestMellin χ φ z.val)

/-- Paper: Theorem 7.4.1.1(2), equation (7.4.1.1), p. 366.
Take the trivial character of a field with a multiple central zeta zero, as on
p. 529, a = 0 and N = 1. A nonzero nonnegative radial test supported at norms
between 2 and 3 has positive Mellin derivative at 1/2. The first-derivative
functional there vanishes on the printed closed span, yet takes this positive
value on the ambient image of its zeroth biorthogonal vector. -/
theorem Printed.spectralNuclearity_trace_false : ¬ Printed.spectralNuclearity_trace := by sorry

open scoped TensorProduct in
/-- Paper: Equation (7.4.3.1), p. 368.
With the displayed projective tensor topology, multiplication of the two factors
realizes the tensor product as a closed subspace of adelic Schwartz functions. -/
def Printed.archFlatProjectiveTensorEmbedding : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    let A := archimedeanFlatSchwartz (ι := {v : InfinitePlace F // v.IsReal})
      (κ := {v : InfinitePlace F // v.IsComplex})
    let V := SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F))
    ∃ e : ProjectiveTensor (↥A) V →L[ℂ] SchwartzBruhat (Multiplicative 𝔸[F]),
      IsClosedEmbedding e ∧ ∀ (h : A) (g : V) (x : 𝔸[F]),
        e (h ⊗ₜ[ℂ] g) (Multiplicative.ofAdd x) =
          h.val (fun v ↦ InfinitePlace.Completion.ringEquivRealOfIsReal v.property (x.1 v.val),
            fun v ↦ InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property (x.1 v.val)) *
          g (Multiplicative.ofAdd x.2)

/-- Paper: Equation (7.4.3.1), p. 368.
Over ℚ choose a basis of the finite test space and flat real functions supported
in (2,3). In the ambient locally convex direct sum one continuous seminorm can
use derivative order j on basis coordinate j. Projective continuity would
bound all those orders by one continuous archimedean seminorm with a separate
constant per coordinate. A fixed bump times exp(i n x) contradicts this bound. -/
theorem Printed.archFlatProjectiveTensorEmbedding_false :
    ¬ Printed.archFlatProjectiveTensorEmbedding := by sorry

/-- Paper: Theorem 7.4.3.1(1), p. 368.
The theta image of the printed unrestricted archimedean-flat tests is a nonzero
closed subspace contained in the zero-moment theta image. -/
def Printed.archNuclearityDenominator_nonzero_closed : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]),
    let q := (LinearMap.ker (homogeneousAdelicThetaLinearMap F (ω[F, χ]))).mkQ
    let D := (globalArchimedeanFlatTests F).map q
    D ≠ ⊥ ∧ IsClosed (D : Set (GlobalHomogeneousThetaSpace F (ω[F, χ]))) ∧
      D ≤ globalPolarFreeThetaSubmodule (ω[F, χ])

/-- Paper: Theorem 7.4.3.1(1), p. 368.
Over ℚ with the trivial character, tensor a nonnegative nonzero smooth bump
supported in (2,3) with the indicator of the finite integral adeles. The test is
archimedean-flat and its Fourier value at zero is its strictly positive integral.
That value survives on the trivial homogeneous theta quotient, so no zero-moment
test represents the same class. -/
theorem Printed.archNuclearityDenominator_nonzero_closed_false :
    ¬ Printed.archNuclearityDenominator_nonzero_closed := by sorry

local notation "Θ₀[" F ", " χ "]" => ↥(adelePolarSubspace F) ⧸
  LinearMap.ker ((homogeneousAdelicThetaLinearMap F (ω[F, χ])).domRestrict (adelePolarSubspace F))
local notation "gammaOrder(" χ ", " s ")" =>
  (analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) s).toNat
local notation "Z(" χ ", " τ ", " hτ ")" => (exists_globalPolarThetaMellin χ τ hτ).choose
local notation "Aθ(" χ ", " τ ", " hτ ", " φ ")" => (exists_polarThetaNuclearityAction χ τ hτ φ).choose

/-- Paper: Theorem 7.4.3.1(2), p. 368.
The page subtracts one at the quasi-character |·|^(it₀), with χ = |·|^(−it₀)
when the norm-one restriction is trivial. The natural-number difference gives
exactly the allowed derivative orders, including the empty range off the pole set. -/
def Printed.archNuclearityMultiplicity {F : Type*} [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)) (s : ℂ) : ℕ :=
  let x := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  gammaOrder(χ, s) -
    (if ω[F, χ] = 1 ∧ ideleClassNormTwist χ s =
      ideleClassNormTwist (1 : U[F]) (-((x : ℂ) * Complex.I)) then 1 else 0)

/-- Paper: Theorem 7.4.3.1(2), p. 368.
The printed derivative indices use the multiplicity at the character specified on the page. -/
abbrev Printed.ArchNuclearityJetIndex {F : Type*} [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)) :=
  {j : ℂ × ℕ // j.2 < Printed.archNuclearityMultiplicity χ τ hτ j.1}

/-- Paper: Equation (7.4.3.4), p. 368. Evaluate a derivative at a printed jet index. -/
def Printed.archNuclearityJet {F : Type*} [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F))
    (j : Printed.ArchNuclearityJetIndex χ τ hτ) : StrongDual ℂ (Θ₀[F, χ]) :=
  ((entireJet j.val.1 j.val.2).comp schwartzBergmanEntireInclusion).comp (Z(χ, τ, hτ))

section QuotientPredicates

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] {J : Type*}

/-- Paper: Theorem 7.4.3.1(2), p. 368. The strong closure of the derivative
span equals the annihilator of the denominator. -/
def Printed.JetsSpanAnnihilator (D : Submodule ℂ E) (jet : J → StrongDual ℂ E) : Prop :=
  ((Submodule.span ℂ (Set.range jet)).topologicalClosure : Set (StrongDual ℂ E)) =
    {ℓ | ∀ x : D, ℓ x.val = 0}

/-- Paper: Theorem 7.4.3.1(3), p. 368. The specified derivatives descend to a
Schauder basis of the strong quotient dual in each enumeration. -/
def Printed.HasQuotientJetBasis (D : Submodule ℂ E) (jet : J → StrongDual ℂ E) : Prop :=
  ∀ σ : ℕ ≃ J, ∃ (d : ℕ → StrongDual ℂ (E ⧸ D))
    (b : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ D))),
    (∀ n (x : E), d n (D.mkQ x) = jet (σ n) x) ∧ IsSchauderBasis d b

/-- Paper: Equation (7.4.3.14), p. 373. The induced operator has the stated
matrix trace in each enumeration of the specified derivative basis. -/
def Printed.HasQuotientJetTrace (D : Submodule ℂ E) (jet : J → StrongDual ℂ E)
    (A : E →L[ℂ] E) (value : ℂ) : Prop :=
  Printed.HasQuotientJetBasis D jet ∧
    ∃ T : (E ⧸ D) →L[ℂ] (E ⧸ D), (∀ x : E, T (D.mkQ x) = D.mkQ (A x)) ∧
      ∀ (σ : ℕ ≃ J) (d : ℕ → StrongDual ℂ (E ⧸ D))
        (b : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ D))),
        (∀ n (x : E), d n (D.mkQ x) = jet (σ n) x) → IsSchauderBasis d b →
          HasSum (fun n ↦ b n ((d n).comp T)) value

/-- Paper: Remark 7.4.3.3, p. 373. The action descends to a nonnuclear
endomorphism of the quotient. -/
def Printed.HasNonnuclearQuotientAction (D : Submodule ℂ E) (A : E →L[ℂ] E) : Prop :=
  letI : UniformSpace (E ⧸ D) := IsTopologicalAddGroup.rightUniformSpace (E ⧸ D)
  ∃ T : (E ⧸ D) →L[ℂ] (E ⧸ D), (∀ x : E, T (D.mkQ x) = D.mkQ (A x)) ∧
    ¬ Nonempty (NuclearPresentation T)

end QuotientPredicates

/-- Paper: Theorem 7.4.3.1(2), p. 368.
With the multiplicity exception as written on the page, the indicated derivatives
generate the annihilator of the flat image in the strong dual. -/
def Printed.archNuclearityJet_span : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)),
    Printed.JetsSpanAnnihilator (archNuclearityDenominator χ) (Printed.archNuclearityJet χ τ hτ)

/-- Paper: Theorem 7.4.3.1(2), p. 368.
For χ = |·|^i over ℚ the printed index includes evaluation at s = −i. Let h be
a nonzero nonnegative bump in (2,3). The real test h(x) − 2 h(2x) is flat with
integral zero. With finite integer indicators its zeta value at the trivial
quasi-character is proportional to (1 − 2) ζ(0) times the nonzero Mellin moment
of h at zero. This jet is nonzero on the flat denominator. -/
theorem Printed.archNuclearityJet_span_false : ¬ Printed.archNuclearityJet_span := by sorry

/-- Paper: Theorem 7.4.3.1(3), p. 368.
Every enumeration of the printed derivatives gives a basis of the strong quotient dual. -/
def Printed.archNuclearityJet_basis : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)),
    Printed.HasQuotientJetBasis (archNuclearityDenominator χ) (Printed.archNuclearityJet χ τ hτ)

/-- Paper: Theorem 7.4.3.1(3), p. 368.
The same flat test h(x) − 2 h(2x) has nonzero evaluation at the printed index
(−i, 0) for the rational character |·|^i. A functional on the quotient vanishes
on the class of this test. -/
theorem Printed.archNuclearityJet_basis_false : ¬ Printed.archNuclearityJet_basis := by sorry

/-- Paper: Equation (7.4.3.4), p. 368.
The unnormalized vertical integral in the printed jet formula is 2πi times the
inverse Mellin transform, so its logarithmic moment carries that factor. -/
def Printed.archNuclearityJet_apply : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F))
    (j : Printed.ArchNuclearityJetIndex χ τ hτ) (f : adelePolarSubspace F),
    let u := fun s ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ s)
    let moment := fun t : ℝ ↦ (Real.log t : ℂ) ^ j.val.2 * mellinInv 0 u t
    iteratedDeriv j.val.2 u j.val.1 =
      (2 * (Real.pi : ℂ) * Complex.I) * mellin moment j.val.1

/-- Paper: Equation (7.4.3.4), p. 368.
For ℚ and the trivial character, take the jet at −2 of order zero. Tensor
exp(−πx²) − 3 exp(−4πx²) + 2 exp(−16πx²) with the finite integral indicator.
The coefficients make the two polar moments vanish. The x² coefficient is
−21π, so the simple archimedean Mellin pole at −2 cancels the simple zeta zero
with nonzero result. The missing factor therefore changes the value. -/
theorem Printed.archNuclearityJet_apply_false : ¬ Printed.archNuclearityJet_apply := by sorry

/-- Paper: Equation (7.4.3.14), p. 373. The printed gamma-pole sum with its
norm-character correction. -/
def Printed.archNuclearityTraceValue {F : Type*} [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)) (φ : BruhatCompactSupport C[F]) : ℂ :=
  let invΓ := fun z ↦ (heckeGammaFactor χ z)⁻¹
  let Poles := {z : ℂ // 0 < analyticOrderAt invΓ z}
  let term := fun z : Poles ↦
    ((analyticOrderAt invΓ z.val).toNat : ℂ) * nuclearityTestMellin χ φ z.val
  let x := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  let correction := if ω[F, χ] = 1 then
    nuclearityTestMellin (1 : U[F]) φ (-((x : ℂ) * Complex.I)) else 0
  (∑' z, term z) - correction

/-- Paper: Equation (7.4.3.14), p. 373.
The printed numerical expression changes when the same trivial norm-one
component is parametrized by the unitary norm power with exponent i.
A positive log-norm bump in (1/4,1/2) has real pole weights in both charts.
The correction in the shifted chart has strictly negative imaginary part. -/
theorem Printed.archNuclearityTraceValue_changes_in_norm_chart
    (τ : ℝ≥0ˣ →ₜ* I[ℚ]) (hτ : RightInverse τ (ideleNorm ℚ)) :
    ∃ (χ : U[ℚ]) (φ : BruhatCompactSupport C[ℚ]),
      (∀ g : C[ℚ], (χ g : ℂ) = ((((ideleClassNorm ℚ g).val : ℝ) : ℂ) ^ Complex.I)) ∧
      tsupport φ.val ⊆ {g : C[ℚ] | 1 < ((ideleClassNorm ℚ g).val : ℝ)} ∧
      Printed.archNuclearityTraceValue χ τ hτ φ ≠
        Printed.archNuclearityTraceValue (1 : U[ℚ]) τ hτ φ := by sorry

/-- Paper: Theorem 7.4.3.2(2), equation (7.4.3.14), p. 373.
The matrix trace in the derivative basis is the sum of its diagonal weights.
The printed correction to the gamma-pole series uses the norm to the power −ix₀. -/
def Printed.archNuclearity_trace : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F))
    (φ : BruhatCompactSupport C[F]),
    tsupport φ.val ⊆ {g : C[F] | 1 < ((ideleClassNorm F g).val : ℝ)} →
    Printed.HasQuotientJetTrace (archNuclearityDenominator χ) (Printed.archNuclearityJet χ τ hτ)
      (Aθ(χ, τ, hτ, φ)) (Printed.archNuclearityTraceValue χ τ hτ φ)

/-- Paper: Theorem 7.4.3.2(2), equation (7.4.3.14), p. 373.
Over ℚ take χ = |·|^i and a nonzero nonnegative radial bump with log-norm
support in (1/4,1/2). The selected gamma poles have parameters −i−2n, giving
real diagonal values in any claimed derivative basis, by the product rule.
The pole sum is real and the printed correction has strictly negative imaginary part. -/
theorem Printed.archNuclearity_trace_false : ¬ Printed.archNuclearity_trace := by sorry

/-- Paper: Remark 7.4.3.3, p. 373.
The remark asserts that the operator induced on the quotient is nonnuclear for
every test with the preceding support condition. Its argument uses the strong dual. -/
def Printed.archNuclearityStrongDual_not_nuclear : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F))
    (φ : BruhatCompactSupport C[F]),
    tsupport φ.val ⊆ {g : C[F] | 1 < ((ideleClassNorm F g).val : ℝ)} →
    Printed.HasNonnuclearQuotientAction (archNuclearityDenominator χ) (Aθ(χ, τ, hτ, φ))

/-- Paper: Remark 7.4.3.3, p. 373.
Take F = ℚ, the trivial character, and the zero Bruhat test. Its support is empty
and every multiplier derivative vanishes. The induced action and transpose have
rank zero and admit nuclear presentations. -/
theorem Printed.archNuclearityStrongDual_not_nuclear_false :
    ¬ Printed.archNuclearityStrongDual_not_nuclear := by sorry

end RiemannMasullo
