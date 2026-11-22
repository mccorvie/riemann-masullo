module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3b

/-!
# §5.3.3–5.3.4: statements that are false as printed

The repaired statements are in `Sec3b.lean`. Nothing imports this file.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain NumberField Set Topology
open scoped ContDiff NNReal NumberField.AdeleRing SchwartzMap TensorProduct

namespace RiemannMasullo

set_option quotPrecheck false

/-- Paper: Example 5.3.3.1, p. 249. As printed: On every nonempty interval of exponents I,
the logarithmic profiles in the weighted space are precisely the smooth functions for which
the values of each twisted profile decay faster than every inverse power at both ends.
The repaired statement is `positiveRealExponentialDecay_log_equiv`. See ERRATA F52. -/
def Printed.positiveRealExponentialDecay_valueDecay : Prop :=
  ∀ (I : Set ℝ), OrdConnected I → I.Nonempty → ∀ (f : ℝ → ℂ),
    f ∈ logExponentialDecaySubmodule I ↔
      ContDiff ℝ (∞) f ∧ ∀ a ∈ I, ∀ k : ℝ, 0 < k →
        Tendsto (fun x : ℝ ↦ ‖x‖ ^ k * ‖logExponentialWeight a f x‖) (cocompact ℝ) (𝓝 0)

/-- Paper: Example 5.3.3.1, p. 249. Take I = ℝ and
f(x) = exp(−x²) sin(exp(2x²)). The Gaussian bounds every twisted value, while at
x = √(log(2πn)/2) for positive integers n the derivative is 4x exp(x²). Even the
twist with exponent zero fails the Schwartz derivative bounds. -/
theorem Printed.positiveRealExponentialDecay_valueDecay_false :
    ¬ Printed.positiveRealExponentialDecay_valueDecay := by
  sorry

local notation "complexDecay(" I ")" => ModulatedExponentialDecay (archimedeanUnitModulation ℂ 2) I
local notation "zeroExtension(" f ")" =>
  (fun x ↦ if hx : x ≠ 0 then f (Units.mk0 x hx) else (0 : ℂ))

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250. As printed: For every m ≥ 0 and a < 0,
the first holomorphic Wirtinger derivative is continuous from the complex multiplicative
space of weights (a, ∞) to the one of weights (a + m, ∞). This is the assertion for ∂z.
The repaired statement is `iteratedWirtinger_exponentialDecay`. See ERRATA F53. -/
def Printed.wirtinger_exponentialDecay : Prop :=
  ∀ (m : ℕ) (a : ℝ), a < 0 →
    ∃ D : complexDecay(Ioi a) →L[ℂ] complexDecay(Ioi (a + m)),
      ∀ f z, (D f).val z = wirtingerDeriv zeroExtension(f.val) z.val

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250. Take m = 0, a = −1/4 and a smooth
radial cutoff of |z|^(3/4), equal to |z|^(3/4) near zero and zero for |z| ≥ 2.
Each source twist has exponent 2b + 3/4 > 0 at zero. The first holomorphic derivative
has modulus (3/8)|z|^(−1/4) near zero, so the target twist with b = 0 is unbounded. -/
theorem Printed.wirtinger_exponentialDecay_false :
    ¬ Printed.wirtinger_exponentialDecay := by
  sorry

local notation "realDecay(" I ")" => ModulatedExponentialDecay (archimedeanUnitModulation ℝ 1) I

/-- Paper: Lemma 5.3.3.3(2), p. 252. As printed: For any numbers of real and complex
coordinates and any nonempty open interval I, the projective tensor product of the
one-coordinate weighted spaces embeds topologically in the product space of (5.3.3.6)
by multiplying the pure factors. The repaired statement is `archimedeanWeightedSchwartz_tensor`.
See ERRATA F54. -/
def Printed.archimedeanWeightedSchwartz_tensor : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (I : Set ℝ), IsOpen I → OrdConnected I → I.Nonempty →
    let R := realDecay(I)
    let C := complexDecay(I)
    let T := ProjectiveTensor (FiniteProjectiveTensor (fun _ : ι ↦ R))
      (FiniteProjectiveTensor (fun _ : κ ↦ C))
    ∃ L : T →L[ℂ] ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I,
      IsEmbedding L ∧ ∀ (f : ι → R) (g : κ → C) (u : (ι → ℝˣ) × (κ → ℂˣ)),
        (L ((⨂ₜ[ℂ] i, f i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, g j))).val u =
          (∏ i, (f i).val (u.1 i)) * ∏ j, (g j).val (u.2 j)

/-- Paper: Lemma 5.3.3.3(2), p. 252. Take one real factor, no complex factors, and
I = (0, ∞). The restriction of the Gaussian exp(−πx²) to ℝˣ meets every positive twist.
Its product with the empty tensor has logarithmic profile tending to one at −∞, contrary
to the unweighted Schwartz condition of (5.3.3.6). -/
theorem Printed.archimedeanWeightedSchwartz_tensor_false :
    ¬ Printed.archimedeanWeightedSchwartz_tensor := by
  sorry

/-- Paper: Proposition 5.3.3.4(1), p. 258. As printed: For every real Schwartz test and
sign parity, shifting the Mellin exponent by n and the sign parity by n modulo two keeps
the same meromorphic transform of that test. The repaired statement is
`realArchimedeanMellin_monomial`. See ERRATA F55. -/
def Printed.realArchimedeanMellin_monomial : Prop :=
  ∀ (n : ℕ) (ε : Fin 2) (f : 𝓢(ℝ, ℂ)),
    ∀ᶠ s : ℂ in codiscrete ℂ,
      realArchimedeanMellin f ε s = realArchimedeanMellin f (Fin.ofNat 2 (ε.val + n)) (s + n)

/-- Paper: Proposition 5.3.3.4(1), p. 258. Take n = 1, the trivial sign parity and
f(x) = exp(−πx²). At s = 1 the even Mellin integral is strictly positive. The shifted
odd profile vanishes identically. Both sides are analytic near s = 1. -/
theorem Printed.realArchimedeanMellin_monomial_false :
    ¬ Printed.realArchimedeanMellin_monomial := by
  sorry

section SAdele

local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "ℬ(" A ")" => SchwartzBruhat (Multiplicative A)
local notation "RealPlaces(" F ")" => {w : InfinitePlace F // w.IsReal}
local notation "ComplexPlaces(" F ")" => {w : InfinitePlace F // w.IsComplex}
local notation "RealModels(" F ")" => ((w : RealPlaces(F)) →
  {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
local notation "ComplexModels(" F ")" => ((w : ComplexPlaces(F)) →
  {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)})
local notation "ArchCoordinates(" F ")" => ((RealPlaces(F) → ℝ) × (ComplexPlaces(F) → ℂ))

open Classical in
/-- Paper: Definition 5.3.4.1, p. 259. As printed: For every number field and finite set
of places containing the archimedean places, the polar-free tensor factors give additive
S-adelic Schwartz–Bruhat functions. This is the inclusion in (5.3.4.1) on pure tensors, with
finite multiplicative factors extended by zero. The repaired declarations are `sAdelePolarFree`,
`sAdelePolarFree_eq_span_tmul` and `exists_finitePlaceSchwartz_zeroExtension_iff`.
See ERRATA F56. -/
def Printed.sAdelePolarFree_inclusion : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset V(F))
    (r : RealModels(F)) (c : ComplexModels(F))
    (f : archimedeanFlatSchwartz (ι := RealPlaces(F)) (κ := ComplexPlaces(F)))
    (g : ∀ v : S, SchwartzBruhat (v.val.adicCompletion F)ˣ),
    ∃ h : ℬ(SAdeleRing F S),
      ∀ (x : ArchCoordinates(F)) (y : (v : S) → v.val.adicCompletion F),
        let xArch : InfiniteAdeleRing F := fun w ↦
          if hw : w.IsReal then (r ⟨w, hw⟩).val.symm (x.1 ⟨w, hw⟩)
          else
            let w' : ComplexPlaces(F) := ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩
            (c w').val.symm (x.2 w')
        h (Multiplicative.ofAdd (xArch, y)) = f.val x * ∏ v : S, zeroExtension(g v) (y v)

/-- Paper: Definition 5.3.4.1, p. 259. Take ℚ with its real and 3-adic places. Take a
nonzero smooth real bump supported in (1, 2) and the 3-adic multiplicative test
g(3ᵏu) = 3⁻ᵏ for k ≥ 0 and zero for k < 0, where u is an integer unit. Its shell sequence
is Schwartz. At any real point where the bump is nonzero, the finite slice of the prescribed
product vanishes at zero and is nonzero at every 3ᵏ for k ≥ 0, violating local constancy. -/
theorem Printed.sAdelePolarFree_inclusion_false :
    ¬ Printed.sAdelePolarFree_inclusion := by
  sorry

/-- Paper: Lemma 5.3.4.2(2), proof, p. 260. As printed: For every number field, finite set
of places containing the archimedean places and place in the set, restriction of S-idele
quotient quasi-characters onto the local quasi-character space is surjective. This is the
surjectivity assertion also made for the archimedean places in Proposition 5.3.4.5(2).
`sLocalArchimedeanPoleMultiplicity` uses the actual restrictions. See ERRATA F57. -/
def Printed.sLocalRestriction_surjective : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset V(F)),
    (∀ w : InfinitePlace F, Function.Surjective (sLocalInfiniteRestriction (S := S) w)) ∧
    ∀ v : S, Function.Surjective (sLocalFiniteRestriction v)

/-- Paper: Lemma 5.3.4.2(2), proof, p. 260. For ℚ and the set consisting of the real place,
the local unit −1 maps to the identity of the S-idele quotient because it is the diagonal
S-unit −1. The local sign character takes value −1 there and so lies outside the image. -/
theorem Printed.sLocalRestriction_surjective_false :
    ¬ Printed.sLocalRestriction_surjective := by
  sorry

local notation "Jₛ(" F ", " S ")" => SIdeleQuotient F S
local notation "chart(" F ", " S ", " χ ")" =>
  quasiCharacterNormTwist (G := Jₛ(F, S)) (sIdeleQuotientNorm F S)
    (isProperMap_sIdeleQuotientNorm F S).continuous
    ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)

/-- Paper: Proposition 5.3.4.5(2), p. 264. On the reading that the listed poles occur
with their multiplicities, every point of (5.3.4.13) is a pole after applying all finite
principal values to any S-adelic test. This isolates occurrence from the multiplicity formula.
The repaired statements are `sLocalIdelicZFunction_principalValue_pole_bound` and
`exists_sLocalIdelicZFunction_principalValue_attaining_poles`. See ERRATA F58. -/
def Printed.sLocalIdelicZFunction_principalValue_has_poles : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset V(F))
    (f : ℬ(SAdeleRing F S)) (χ : PontryaginDual Jₛ(F, S)) (s : ℂ),
    0 < sLocalArchimedeanPoleMultiplicity χ s →
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction
        (sAdelePrincipalValue F (Finset.Subset.refl S) f) (chart(F, S, χ) z)) s < 0

/-- Paper: Proposition 5.3.4.5(2), p. 264. For ℚ with only the real place, take the
trivial character at s = 0 and a nonzero even, nonnegative smooth bump supported on
1 < |x| < 2. There are no finite principal values to apply. The Mellin transform is entire,
while the real Euler factor Γℝ(s) has a simple pole at zero. -/
theorem Printed.sLocalIdelicZFunction_principalValue_has_poles_false :
    ¬ Printed.sLocalIdelicZFunction_principalValue_has_poles := by
  sorry

/-- Paper: Proposition 5.3.4.5(2), p. 264. As printed: At each point in the union of pulled-back
archimedean pole sets, the sum of the signed orders of the local Euler factors is the value
of a natural-valued multiplicity function, as in (5.3.4.14). The sum is compared with the
multiplicity after coercing the latter to signed orders. The repaired statement is
`sLocalArchimedeanPoleMultiplicity_eq_sum`. See ERRATA F59. -/
def Printed.sLocalArchimedeanPoleMultiplicity_eq_sum : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset V(F)) (χ : PontryaginDual Jₛ(F, S)),
    ∃ N : {s : ℂ // 0 < sLocalArchimedeanPoleMultiplicity χ s} → ℕ,
      ∀ s, (↑(N s : ℤ) : WithTop ℤ) = ∑ w : InfinitePlace F,
        meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
          (sLocalInfiniteRestriction w (chart(F, S, χ) z))) s.val

/-- Paper: Proposition 5.3.4.5(2), p. 264. Take ℚ with only the real place and the trivial
norm-twist line at s = 0. Its Euler factor Γℝ(s) has a simple pole, so the sole summand is
−1 in the divisor convention of (7.1.2.1). No natural multiplicity has this signed value. -/
theorem Printed.sLocalArchimedeanPoleMultiplicity_eq_sum_false :
    ¬ Printed.sLocalArchimedeanPoleMultiplicity_eq_sum := by
  sorry

end SAdele

end RiemannMasullo
