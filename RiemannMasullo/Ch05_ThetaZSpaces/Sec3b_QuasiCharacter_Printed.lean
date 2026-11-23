module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3b

/-! # The polar-free multiplication claim in §5.3.4 -/

@[expose] public noncomputable section

open IsDedekindDomain NumberField
open scoped BigOperators

namespace RiemannMasullo

local notation "RealPlaces(" F ")" => {w : InfinitePlace F // InfinitePlace.IsReal w}
local notation "ComplexPlaces(" F ")" => {w : InfinitePlace F // InfinitePlace.IsComplex w}

open Classical in
/-- Paper: Definition 5.3.4.1, p. 259. The function image of the tensor
product in (5.3.4.1) on the S-ideles is the span of the pure products with an
archimedean flat factor and multiplicative Schwartz–Bruhat finite factors. -/
def Printed.polarFreeTensorFunctions {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (r : (w : RealPlaces(F)) →
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
    (c : (w : ComplexPlaces(F)) →
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)}) :
    Submodule ℂ ((SAdeleRing F S)ˣ → ℂ) :=
  Submodule.span ℂ {f | ∃ (h : archimedeanFlatSchwartz
      (ι := RealPlaces(F)) (κ := ComplexPlaces(F)))
    (k : ∀ v : S, SchwartzBruhat (v.val.adicCompletion F)ˣ),
    ∀ g, f g = h.val ((fun w ↦ (r w).val (g.val.1 w.val)),
      (fun w ↦ (c w).val (g.val.1 w.val))) *
        ∏ v : S, k v (Units.map ((Pi.evalRingHom _ v).comp (RingHom.snd _ _)).toMonoidHom g)}

/-- Paper: Lemma 5.3.4.2(3), p. 260. As printed: For every number field and finite
set of places containing the archimedean places, multiplication by any continuous
quasi-character trivial on the diagonal S-units preserves the polar-free tensor
functions of (5.3.4.1). This is the closure under multiplication clause, on the
S-ideles where the quasi-character is defined. The finite factors are those on
the multiplicative local groups. See `sAdelePolarFree_quasiCharacter_mul` and ERRATA F236. -/
def Printed.sAdelePolarFreeTensor_quasiCharacter_mul : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (r : (w : RealPlaces(F)) →
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
    (c : (w : ComplexPlaces(F)) →
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)})
    (b : QuasiCharacter (SIdeleQuotient F S)) (f : (SAdeleRing F S)ˣ → ℂ),
    f ∈ Printed.polarFreeTensorFunctions S r c →
      (fun g ↦ b (QuotientGroup.mk g) * f g) ∈ Printed.polarFreeTensorFunctions S r c

/-- Paper: Lemma 5.3.4.2(3), p. 260. Take ℚ with the real and 2-adic places.
Use a nonzero smooth real bump in (1, 2) and the unit-invariant finite factor
with value 2^(−2ʲ) on 2^(4ʲ)ℤ₂ˣ for j ≥ 1 and zero on the other shells.
The finite factor is Schwartz by rapid decay of its valuation profile.
The multiplier |x|⁻¹ |y|₂⁻¹ is trivial on the diagonal units ±2ᵏ. At a fixed
real coordinate where the bump is nonzero, the new finite slice has values
proportional to 2^(4ʲ−2ʲ) and is unbounded. Every finite slice of a tensor
function is a finite linear combination of bounded Schwartz–Bruhat functions. -/
theorem Printed.sAdelePolarFreeTensor_quasiCharacter_mul_false :
    ¬ Printed.sAdelePolarFreeTensor_quasiCharacter_mul := by sorry

end RiemannMasullo
