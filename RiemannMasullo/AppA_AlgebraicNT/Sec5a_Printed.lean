module

public import RiemannMasullo.AppA_AlgebraicNT.Sec5a
public import RiemannMasullo.Ch03_IdelicZeta.Sec1
public import Mathlib.Topology.Algebra.RestrictedProduct.Units

/-! # Appendix A.5.2: statements that are false as printed -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal Pointwise

section QuotientGroups

local instance printedSec5aQuotientMeasurableSpace {G : Type} [CommGroup G]
    [TopologicalSpace G] (H : Subgroup G) : MeasurableSpace (G ⧸ H) := borel _

/-- Paper: Proposition A.5.2.6, end of proof, p. 574.
As printed: for a symmetric, relatively compact Borel transversal `E` containing the identity
in its interior, a decreasing Borel family on the quotient and its specified auxiliary sets
form a D″-sequence exactly when their preimages intersected with `E` do. The ambient group is
second countable, the subgroup is closed and discrete, and counting measure on the subgroup
determines the quotient Haar measure for the given ambient measure. The D and D′ assertions
are `isDSequence_quotient_iff` and `isDPrimeSequence_quotient_iff`. See ERRATA F218. -/
def Printed.isDDoublePrimeSequence_quotient_iff : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) [DiscreteTopology H],
    IsClosed (H : Set G) →
    ∀ (μ : Measure G) [μ.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]
      (ν : Measure (G ⧸ H)),
    IsWeilQuotientMeasure H μ μH ν → μH {1} = 1 →
    ∀ (E : Set G), MeasurableSet E → IsCompact (closure E) → 1 ∈ interior E → E⁻¹ = E →
    Bijective (fun x : E ↦ QuotientGroup.mk' H (x : G)) →
    ∀ (U V : ℕ → Set (G ⧸ H)), (∀ k, MeasurableSet (U k)) → Antitone U →
    let lift := fun (W : ℕ → Set (G ⧸ H)) k ↦ (QuotientGroup.mk' H) ⁻¹' W k ∩ E
    IsDDoublePrimeSequence ν U V ↔ IsDDoublePrimeSequence μ (lift U) (lift V)

/-- Paper: Proposition A.5.2.6, end of proof, p. 574.
Use the discrete additive group `ℤ`, the subgroup `3ℤ`, counting measures, and the symmetric
transversal `E = {-1, 0, 1}`. In `ℤ/3ℤ` set `U 0 = V 0 = univ` and `U k = V k = {0}`
for `k ≥ 1`. These satisfy the D″ conditions with constants `2` and `1`, respectively.
The two lifts at zero are `E`, and `1 - (-1) = 2` lies outside `E`. -/
theorem Printed.isDDoublePrimeSequence_quotient_iff_false :
    ¬ Printed.isDDoublePrimeSequence_quotient_iff := by
  sorry

end QuotientGroups

section Ideles

set_option maxSynthPendingDepth 3

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "RegulatorBasis(" F ")" =>
  Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F))
set_option quotPrecheck false in
local notation "FiniteUnitsAt(" F ", " S ")" =>
  (∀ v : {v : Primes(F) // v ∈ S}, (v.val.adicCompletionIntegers F)ˣ)
set_option quotPrecheck false in
local notation "FiniteIntegralUnits(" F ")" =>
  (∀ v : Primes(F), ↥((v.adicCompletionIntegers F).units))
local notation "I(" F ")" => IdeleGroup (𝓞 F) F
local notation "C(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "outsideInclusion" =>
  Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside _ _)))
local notation "outsideNorm(" F ", " S ")" =>
  MonoidHom.comp (ideleNorm F)
    (Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside F S))))

local instance printedSec5aInfiniteNormOneMeasurableSpace (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (infiniteIdeleNorm F).ker := borel _

local instance printedSec5aSLocalNormOneMeasurableSpace (F : Type) [Field F] [NumberField F]
    (S : Finset (Primes(F))) : MeasurableSpace (sIdeleNorm F S).ker := borel _

local instance printedSec5aSLocalQuotientNormOneMeasurableSpace (F : Type) [Field F] [NumberField F]
    (S : Finset (Primes(F))) : MeasurableSpace (sIdeleQuotientNorm F S).ker := borel _

local instance printedSec5aGlobalNormOneMeasurableSpace (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (ideleNorm F).ker := borel _

local instance printedSec5aOutsideNormOneMeasurableSpace (F : Type) [Field F] [NumberField F]
    (S : Finset (Primes(F))) : MeasurableSpace outsideNorm(F, S).ker := borel _

local instance printedSec5aGlobalClassNormOneMeasurableSpace (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (ideleClassNorm F).ker := borel _

local instance printedSec5aSClassNormOneMeasurableSpace (F : Type) [Field F] [NumberField F]
    (S : Finset (Primes(F))) : MeasurableSpace (sIdeleClassNorm F S).ker := borel _

private def IsCompactOpenUnitBasis {G : Type} [Group G] [TopologicalSpace G]
    (B : ℕ → OpenSubgroup G) : Prop :=
  (∀ k, IsCompact (B k : Set G)) ∧ Antitone B ∧
    ∀ W ∈ 𝓝 (1 : G), ∃ k, (B k : Set G) ⊆ W

private def sLocalLogSets (F : Type) [Field F] [NumberField F] (b : RegulatorBasis(F))
    (S : Finset (Primes(F))) (B : ℕ → OpenSubgroup FiniteUnitsAt(F, S)) :
    ℕ → Set (sIdeleNorm F S).ker :=
  let insert := fun g : FiniteUnitsAt(F, S) ↦ (ContinuousMulEquiv.piUnits
    (M := fun v : {v : Primes(F) // v ∈ S} ↦ v.val.adicCompletion F)).symm
    (fun v ↦ Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom (g v))
  sLocalIdeleLogNeighborhood F b S (fun k ↦ insert '' (B k : Set _))

private def globalLogSets (F : Type) [Field F] [NumberField F] (b : RegulatorBasis(F))
    (B : ℕ → OpenSubgroup FiniteIntegralUnits(F)) : ℕ → Set (ideleNorm F).ker :=
  let insert := fun g : FiniteIntegralUnits(F) ↦ RestrictedProduct.mkUnit
    (B := fun v : Primes(F) ↦ v.adicCompletionIntegers F)
    (fun v ↦ (g v).val) (Filter.Eventually.of_forall fun v ↦ (g v).property)
  ideleLogNeighborhood F b (fun k ↦ insert '' (B k : Set _))

/-- Paper: Lemma A.5.2.13(2), p. 576.
As printed: for every number field and choice of regulator basis, the archimedean log-cube
preimages are a D′-sequence and pairing them with the preimages at indices `2 * k` gives a
D″-sequence. These are the two sequence assertions of part (2). The symmetry is proved in
`inv_infiniteIdeleLogNeighborhood`. See ERRATA F219. -/
def Printed.isDPrimeSequence_infiniteIdeleLogNeighborhood : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (b : RegulatorBasis(F))
    (μ : Measure (infiniteIdeleNorm F).ker) [μ.IsHaarMeasure],
    let U := infiniteIdeleLogNeighborhood F b
    IsDPrimeSequence μ U ∧ IsDDoublePrimeSequence μ U (fun k ↦ U (2 * k))

/-- Paper: Lemma A.5.2.13(2), p. 576.
For `F = ℚ`, the archimedean norm-one group is `{1, -1}` and the log rank is zero.
All the sets contain `-1`, while `{1}` is an open identity neighborhood. Both sequence
conditions require a member contained in `{1}`. -/
theorem Printed.isDPrimeSequence_infiniteIdeleLogNeighborhood_false :
    ¬ Printed.isDPrimeSequence_infiniteIdeleLogNeighborhood := by
  sorry

/-- Paper: Lemma A.5.2.14, p. 576.
As printed: for every number field, finite set of places containing the infinite places,
unit basis, and decreasing compact open subgroup basis of the finite integral units at those
places, the log-cube products and their images in the norm-one S-idele quotient `J¹` are
D′-sequences. This records the two D′ assertions. The product symmetry is proved in
`inv_sLocalIdeleLogNeighborhood`. See ERRATA F219. -/
def Printed.isDPrimeSequence_sLocalIdeleLogNeighborhood : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (b : RegulatorBasis(F)) (S : Finset (Primes(F)))
    (B : ℕ → OpenSubgroup FiniteUnitsAt(F, S)), IsCompactOpenUnitBasis B →
    ∀ (μ : Measure (sIdeleNorm F S).ker) [μ.IsHaarMeasure]
      (ν : Measure (sIdeleQuotientNorm F S).ker) [ν.IsHaarMeasure],
    let U := sLocalLogSets F b S B
    let q := fun g : (sIdeleNorm F S).ker ↦
      (⟨QuotientGroup.mk g.val, (sIdeleQuotientNorm_mk F S g.val).trans g.property⟩ :
        (sIdeleQuotientNorm F S).ker)
    IsDPrimeSequence μ U ∧ IsDPrimeSequence ν (fun k ↦ q '' U k)

/-- Paper: Lemma A.5.2.14, p. 576.
Take `F = ℚ(i)` and `S` consisting of the unique complex place. There are no finite factors,
so `B k` is the trivial group for all `k`. The unit rank is zero and `U k` is the whole
norm-one circle. Its image is the whole quotient circle modulo the fourth roots of unity.
Each group has a proper identity neighborhood, so neither sequence is cofinal. -/
theorem Printed.isDPrimeSequence_sLocalIdeleLogNeighborhood_false :
    ¬ Printed.isDPrimeSequence_sLocalIdeleLogNeighborhood := by
  sorry

/-- Paper: Lemma A.5.2.16, p. 577.
As printed: for every number field, finite set of places containing the infinite places,
unit basis, and decreasing compact open subgroup basis of the finite integral units, the
log-cube products are D′-sequences in the global and the integral-outside-S norm-one idele
groups, as are their images in both norm-one class groups. This records the D′ assertions
of parts (1)–(3). The product symmetry is proved in `inv_ideleLogNeighborhood`.
See ERRATA F219. -/
def Printed.isDPrimeSequence_ideleLogNeighborhood : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (b : RegulatorBasis(F)) (S : Finset (Primes(F)))
    (B : ℕ → OpenSubgroup FiniteIntegralUnits(F)), IsCompactOpenUnitBasis B →
    ∀ (μ : Measure (ideleNorm F).ker) [μ.IsHaarMeasure]
      (μS : Measure outsideNorm(F, S).ker) [μS.IsHaarMeasure]
      (ν : Measure (ideleClassNorm F).ker) [ν.IsHaarMeasure]
      (νS : Measure (sIdeleClassNorm F S).ker) [νS.IsHaarMeasure],
    let U := globalLogSets F b B
    let incl := fun g : outsideNorm(F, S).ker ↦
      (⟨outsideInclusion g.val, g.property⟩ : (ideleNorm F).ker)
    let US := fun k ↦ incl ⁻¹' U k
    let q := fun g : (ideleNorm F).ker ↦
      (⟨QuotientGroup.mk g.val, g.property⟩ : (ideleClassNorm F).ker)
    let qS := fun g : outsideNorm(F, S).ker ↦
      (⟨QuotientGroup.mk g.val, ((sIdeleNorm_spec F S).1 g.val).symm.trans g.property⟩ :
        (sIdeleClassNorm F S).ker)
    IsDPrimeSequence μ U ∧ IsDPrimeSequence μS US ∧
      IsDPrimeSequence ν (fun k ↦ q '' U k) ∧ IsDPrimeSequence νS (fun k ↦ qS '' US k)

/-- Paper: Lemma A.5.2.16, p. 577.
Take `F = ℚ`, no finite places in `S`, and let `B k` impose congruence to `1` modulo `p^(k+1)`
at the first `k` rational primes in increasing order. The idele with real component `-1` and
all finite components `1` belongs to every product. It has nonidentity class in both quotients:
a diagonal rational with value `1` at a finite place is `1` everywhere. In each Hausdorff
group an identity neighborhood excluding the persistent element witnesses failure of D′. -/
theorem Printed.isDPrimeSequence_ideleLogNeighborhood_false :
    ¬ Printed.isDPrimeSequence_ideleLogNeighborhood := by
  sorry

/-- Paper: Lemma A.5.2.15, (A.5.2.22), p. 577.
As printed: for every number field and finite set of places containing the infinite places,
every finite unit subgroup basis as in Lemma A.5.2.14, and every continuous homomorphic
S-norm section, the stated products and their images in `J` are symmetric. See ERRATA F220.
Deviation: This records the symmetry clause at positive indices using `normSectionNeighborhood`.
The printed formula divides by zero at index zero. The finite factor is the one at S in
(A.5.2.21), which this lemma cites. Its introductory sentence on p. 577 names the full
finite unit group. -/
def Printed.inv_sLocalNormSectionNeighborhood : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (b : RegulatorBasis(F)) (S : Finset (Primes(F)))
    (B : ℕ → OpenSubgroup FiniteUnitsAt(F, S)), IsCompactOpenUnitBasis B →
    ∀ (τ : ℝ≥0ˣ →* (SAdeleRing F S)ˣ), Continuous τ → RightInverse τ (sIdeleNorm F S) →
    ∀ k : ℕ+,
      let U := normSectionNeighborhood τ
        (fun j ↦ (sIdeleNorm F S).ker.subtype '' sLocalLogSets F b S B j) k
      let image := (QuotientGroup.mk : (SAdeleRing F S)ˣ → SIdeleQuotient F S) '' U
      U⁻¹ = U ∧ image⁻¹ = image

/-- Paper: Lemma A.5.2.15, (A.5.2.22), p. 577.
Take `F = ℚ`, `S` consisting of the real place, the trivial finite unit basis, and the
section inserting the positive real in the real place. For `k = 2`, `τ (3/5)` is in the
product because the norm-one factor contains `1`. Its inverse has norm `5/3`, outside
`(1/2, 3/2)`. The same norms apply after quotienting by the diagonal units `{1, -1}`. -/
theorem Printed.inv_sLocalNormSectionNeighborhood_false :
    ¬ Printed.inv_sLocalNormSectionNeighborhood := by
  sorry

/-- Paper: Lemma A.5.2.17, (A.5.2.24), p. 577.
As printed: for every number field and finite set of places containing the infinite places,
every finite unit subgroup basis as in Lemma A.5.2.16, and every continuous homomorphic
norm section, the products and their global class images are symmetric. If the section
lands among the ideles integral outside S, symmetry also holds there and in their S-class
images. See ERRATA F220.
Deviation: This records the symmetry clause at positive indices using `normSectionNeighborhood`.
The printed formula divides by zero at index zero. -/
def Printed.inv_ideleNormSectionNeighborhood : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (b : RegulatorBasis(F)) (S : Finset (Primes(F)))
    (B : ℕ → OpenSubgroup FiniteIntegralUnits(F)), IsCompactOpenUnitBasis B →
    ∀ (τ : ℝ≥0ˣ →* I(F)), Continuous τ → RightInverse τ (ideleNorm F) →
    ∀ k : ℕ+,
      let U := normSectionNeighborhood τ
        (fun j ↦ (ideleNorm F).ker.subtype '' globalLogSets F b B j) k
      let image := (QuotientGroup.mk : I(F) → C(F)) '' U
      let incl : (integralAdelesOutside F S)ˣ →* I(F) := outsideInclusion
      let US := incl ⁻¹' U
      let imageS := (QuotientGroup.mk : (integralAdelesOutside F S)ˣ → SIdeleClassGroup F S) '' US
      U⁻¹ = U ∧ image⁻¹ = image ∧
        ((∃ τS : ℝ≥0ˣ →* (integralAdelesOutside F S)ˣ, Continuous τS ∧ incl.comp τS = τ) →
          US⁻¹ = US ∧ imageS⁻¹ = imageS)

/-- Paper: Lemma A.5.2.17, (A.5.2.24), p. 577.
Take `F = ℚ`, no finite places in `S`, the finite subgroup basis given by congruence to `1`
modulo `p^(k+1)` at the first `k` rational primes, and `ratIdeleNormSection`. The section
has all finite components `1`, so it lands among the ideles integral outside S. At `k = 2`
its value at `3/5` belongs to the product. The inverse has norm `5/3`, outside `(1/2, 3/2)`,
also under the descended norms on both class groups. -/
theorem Printed.inv_ideleNormSectionNeighborhood_false :
    ¬ Printed.inv_ideleNormSectionNeighborhood := by
  sorry

end Ideles

end RiemannMasullo
