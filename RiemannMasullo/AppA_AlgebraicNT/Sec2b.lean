module

public import RiemannMasullo.AppA_AlgebraicNT.Sec2
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import Mathlib.Geometry.Manifold.Submersion

/-!
# Logarithmic coordinates and idelic fundamental domains

Appendix A.2.3–A.2.4 of Masullo. For lattice calculations we use Mathlib's coordinates
on the trace-zero hyperplane, which omit one place. The omitted coordinate is minus
the sum of the others. All interiors and closures are taken in the indicated groups.
-/

@[expose] public section

noncomputable section

-- Integer module instances on the additive versions of quotient unit groups.
set_option maxSynthPendingDepth 8

namespace RiemannMasullo

open Function NumberField IsDedekindDomain Topology
open NumberField.Units.dirichletUnitTheorem InfinitePlace.Completion
open scoped Classical NNReal Pointwise ContDiff Manifold

variable (F : Type*) [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "𝓤" => Additive ((𝓞 F)ˣ ⧸ Units.torsion F)
local notation "unitAtInfinity" => Units.map (RingHom.toMonoidHom
  (RingHom.comp (algebraMap F (InfiniteAdeleRing F)) (algebraMap (𝓞 F) F)))
local notation "atInfinity" =>
  Units.map (RingHom.toMonoidHom (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
local notation "fromInfinity" =>
  (Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))

/-- Paper: Definition A.2.3.1, p. 548. The archimedean norm multiplies the local
absolute values with exponent one at real places and two at complex places. Its
kernel is the group of norm-one archimedean ideles. -/
def infiniteIdeleNorm : 𝕀∞ →* ℝ≥0ˣ :=
  ∏ v : InfinitePlace F, ((Units.map nnNormHom.toMonoidHom).comp
    (Units.map (Pi.evalRingHom _ v).toMonoidHom)) ^ v.mult

local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)
local notation "N₁" => MonoidHom.ker (ideleNorm F)

/-- Paper: Definition A.2.3.1, p. 548. Giving an archimedean idele finite components
equal to one preserves its norm. -/
theorem infiniteIdeleNorm_eq_global (g : 𝕀∞) :
    infiniteIdeleNorm F g = ideleNorm F (fromInfinity g) := by
  sorry

/-- Paper: Definition A.2.3.1, p. 548. The archimedean norm is continuous. -/
theorem infiniteIdeleNorm_continuous : Continuous (infiniteIdeleNorm F) := by
  sorry

/-- Paper: Definition A.2.3.1, p. 548. The norm-one archimedean ideles form a closed subgroup. -/
theorem infiniteIdeleNorm_ker_closed : IsClosed (N∞ : Set 𝕀∞) := by
  sorry

/-- Paper: Definition A.2.3.1, p. 548. The full logarithm records the logarithm of
the normalized absolute value at every archimedean place. -/
def infiniteIdeleLog (g : 𝕀∞) (v : InfinitePlace F) : ℝ :=
  v.mult * Real.log ‖g.val v‖

/-- Paper: Definition A.2.3.1, p. 548. Every real tuple is the logarithm of an
archimedean idele. -/
theorem infiniteIdeleLog_surjective : Surjective (infiniteIdeleLog F) := by
  sorry

/-- Paper: Lemma A.2.3.2(1), p. 548. The logarithm takes products to sums. -/
theorem infiniteIdeleLog_mul (g h : 𝕀∞) :
    infiniteIdeleLog F (g * h) = infiniteIdeleLog F g + infiniteIdeleLog F h := by
  sorry

/-- Paper: Lemma A.2.3.2(1), p. 548. The full logarithm is continuous. -/
theorem infiniteIdeleLog_continuous : Continuous (infiniteIdeleLog F) := by
  sorry

/-- Paper: Lemma A.2.3.2(1), p. 548. The coordinates of the logarithm of a norm-one
idele sum to zero, the defining equation of the logarithmic hyperplane. -/
theorem infiniteIdeleLog_sum_zero (g : N∞) : ∑ v, infiniteIdeleLog F g.val v = 0 := by
  sorry

local notation "mixedUnits" => Units.mapEquiv (RingEquiv.toMulEquiv (InfiniteAdeleRing.ringEquiv_mixedSpace F))

/-- Paper: Lemma A.2.3.2(2), p. 548. In the real and complex completion coordinates the
full logarithm is a smooth submersion of real manifolds. -/
theorem infiniteIdeleLog_submersion :
    Manifold.IsSubmersion 𝓘(ℝ, mixedEmbedding.mixedSpace F) 𝓘(ℝ, InfinitePlace F → ℝ) ∞
      (fun g : (mixedEmbedding.mixedSpace F)ˣ ↦ infiniteIdeleLog F ((mixedUnits).symm g)) := by
  sorry

/-- Paper: Lemma A.2.3.2(2), p. 548. The logarithm kernel is the product of the real
sign groups and the complex circles. The equivalence is the identity in the ambient
real and complex coordinates, identifying the embedded Lie groups. -/
theorem infiniteIdeleLog_kernel :
    let L : 𝕀∞ →* Multiplicative (InfinitePlace F → ℝ) :=
      MonoidHom.mk' (fun g ↦ Multiplicative.ofAdd (infiniteIdeleLog F g)) (infiniteIdeleLog_mul F)
    ∃ e : L.ker ≃ₜ* (({v : InfinitePlace F // v.IsReal} → rootsOfUnity 2 ℝ) ×
        ({v : InfinitePlace F // v.IsComplex} → Circle)), ∀ g,
      let z := InfiniteAdeleRing.ringEquiv_mixedSpace F g.val.val
      (∀ v, ((e g).1 v).val.val = z.1 v) ∧ (∀ v, (((e g).2 v : Circle) : ℂ) = z.2 v) := by
  sorry

/-- Paper: Lemma A.2.3.2(3), p. 548. The full logarithm is proper. -/
theorem infiniteIdeleLog_proper : IsProperMap (infiniteIdeleLog F) := by
  sorry

/-- Paper: Definition A.2.3.3, p. 548. Mathlib's logarithmic embedding of units is
the restriction of the full idelic logarithm to diagonal units, in the coordinates
on the sum-zero hyperplane obtained by omitting the distinguished place. -/
theorem regulator_eq_infiniteIdeleLog (u : (𝓞 F)ˣ) (v : {w : InfinitePlace F // w ≠ w₀}) :
    Units.logEmbedding F (Additive.ofMul u) v = infiniteIdeleLog F (unitAtInfinity u) v.val := by
  sorry

/-- Paper: Lemma A.2.3.4(1), p. 548. The regulator image is discrete in the hyperplane. -/
theorem regulator_discrete : IsDiscrete (Set.range (Units.logEmbedding F)) := by
  sorry

/-- Paper: Lemma A.2.3.4(1), p. 548. The regulator image is closed in the hyperplane. -/
theorem regulator_closed : IsClosed (Set.range (Units.logEmbedding F)) := by
  sorry

/-- Paper: Lemma A.2.3.4(1), p. 548. The quotient of the hyperplane by the regulator
image is compact. -/
theorem regulator_cocompact : CompactSpace (logSpace F ⧸ (Units.logEmbedding F).range) := by
  sorry

/-- Paper: Lemma A.2.3.4(2), p. 548. The regulator kernel is exactly the torsion subgroup. -/
theorem regulator_kernel : (Units.logEmbedding F).ker = (Units.torsion F).toAddSubgroup := by
  sorry

/-- Paper: Lemma A.2.3.4(2), p. 548. The torsion units are the roots of unity of
order dividing the number of torsion units. -/
theorem regulator_torsion_roots : Units.torsion F = rootsOfUnity (Units.torsionOrder F) (𝓞 F) := by
  sorry

/-- Paper: Lemma A.2.3.4(2), p. 548. The group of torsion units is finite. -/
theorem regulator_torsion_finite : Finite (Units.torsion F) := by
  sorry

/-- Paper: Lemma A.2.3.4(2), p. 548. The group of torsion units is cyclic. -/
theorem regulator_torsion_cyclic : IsCyclic (Units.torsion F) := by
  sorry

/-- Paper: Lemma A.2.3.4(3), p. 548. The unit group is finitely generated. -/
theorem regulator_units_finitelyGenerated : Group.FG (𝓞 F)ˣ := by
  sorry

/-- Paper: Lemma A.2.3.4(3), p. 548. The units modulo torsion have an integral basis
of cardinality the number of infinite places minus one. -/
theorem regulator_units_mod_torsion_basis : Nonempty (Module.Basis (Fin (Units.rank F)) ℤ 𝓤) := by
  sorry

variable (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))

/-- Paper: Equation (A.2.3.8), p. 549. Every norm-one archimedean logarithm has unique
real coordinates in the logarithms of the chosen basis of units modulo torsion. -/
theorem regulator_coordinates_unique (g : N∞) :
    ∃! t : Fin (Units.rank F) → ℝ, ∀ w : {w : InfinitePlace F // w ≠ w₀},
      infiniteIdeleLog F g.val w.val = ∑ i, t i * Units.logEmbeddingQuot F (b i) w := by
  sorry

/-- Paper: Equation (A.2.3.9), p. 549. The regulator parallelotope is the half-open
fundamental parallelepiped of the image of the chosen basis of units modulo torsion. -/
def regulatorParallelotope : Set (logSpace F) :=
  ZSpan.fundamentalDomain ((b.map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ (Units.unitLattice F))

/-- Paper: Equations (A.2.3.9)–(A.2.3.10), p. 549. On a basis direction a real
multiple belongs to the regulator parallelotope exactly for coefficients in [0,1). -/
theorem regulatorParallelotope_basis_line (i : Fin (Units.rank F)) (t : ℝ) :
    t • Units.logEmbeddingQuot F (b i) ∈ regulatorParallelotope F b ↔ t ∈ Set.Ico 0 1 := by
  sorry

-- TODO(paper-gap): Lemma A.2.3.5 calls F a hyperplane. Equations (A.2.3.5) and (A.2.3.9)
-- define the hyperplane and parallelotope for the number field F.

/-- Paper: Lemma A.2.3.5(1), p. 549. The closure of the parallelotope in the
logarithmic hyperplane is compact.
Deviation: We take F to be the number field of (A.2.3.5). -/
theorem regulatorParallelotope_precompact : IsCompact (closure (regulatorParallelotope F b)) := by
  sorry

/-- Paper: Lemma A.2.3.5(1), p. 549. The parallelotope has nonempty relative interior. -/
theorem regulatorParallelotope_interior : (interior (regulatorParallelotope F b)).Nonempty := by
  sorry

/-- Paper: Lemma A.2.3.5(2), p. 549. Regulator translates cover the hyperplane. -/
theorem regulatorParallelotope_cover :
    (⋃ x : (Units.logEmbedding F).range, x.val +ᵥ regulatorParallelotope F b) = Set.univ := by
  sorry

/-- Paper: Lemma A.2.3.5(2), p. 549. Every nonzero regulator translate misses the parallelotope. -/
theorem regulatorParallelotope_disjoint (x : (Units.logEmbedding F).range) (hx : x ≠ 0) :
    Disjoint (x.val +ᵥ regulatorParallelotope F b) (regulatorParallelotope F b) := by
  sorry

/-- Paper: Equation (A.2.3.12), p. 549. The natural ideal class of an idele is the
product of its finite local contributions, with the valuation convention of §A.1. -/
def ideleIdealClass (g : 𝕀[F]) : CommRing.Pic (𝓞 F) :=
  ∏ᶠ v : Primes(F), localIdealClass F v (Units.map
    ((RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
      (RingHom.snd _ _)).toMonoidHom g)

/-- Paper: Equation (A.2.3.12), p. 549. Only finitely many local factors in the
idele's ideal class can be nontrivial. -/
theorem ideleIdealClass_finite_support (g : 𝕀[F]) :
    (fun v : Primes(F) ↦ localIdealClass F v (Units.map
      ((RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
        (RingHom.snd _ _)).toMonoidHom g)).HasFiniteMulSupport := by
  sorry

/-- Paper: Equation (A.2.3.12), p. 549. An idele supported at one finite place
has exactly the local ideal class from §A.1. -/
theorem ideleIdealClass_ofAdicCompletion (v : Primes(F)) (x : (v.adicCompletion F)ˣ) :
    ideleIdealClass F (IdeleGroup.ofAdicCompletion (𝓞 F) F v x) = localIdealClass F v x := by
  sorry

/-- Paper: Equation (A.2.3.12), p. 549. Every ideal class has a norm-one representative,
and the representative of the trivial class can be chosen to be one. -/
theorem exists_normOne_class_representatives :
    ∃ r : CommRing.Pic (𝓞 F) → N₁, r 1 = 1 ∧ ∀ c, ideleIdealClass F (r c).val = c := by
  sorry

variable (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)

/-- Paper: Definition A.2.3.6, p. 549. At the chosen place keep the half-open sector
from angle zero to two pi divided by the number of roots of unity. Postcomposition
by a real algebra automorphism of ℂ allows either embedding at a complex place. -/
def inTorsionSector (x : v₀.Completionˣ) : Prop :=
  (σ (extensionEmbedding v₀ x.val)).arg ∈ Set.Ico 0 (2 * Real.pi / Units.torsionOrder F)

/-- Paper: Definition A.2.3.6, p. 549. At a real place the angular condition selects
exactly the positive component. -/
theorem inTorsionSector_real (hv : v₀.IsReal) (x : v₀.Completionˣ) :
    inTorsionSector F v₀ σ x ↔ 0 < extensionEmbeddingOfIsReal hv x.val := by
  sorry

local notation "atPlace" => Units.map (RingHom.toMonoidHom (Pi.evalRingHom InfinitePlace.Completion v₀))
local notation "inLogBox" => fun g : N∞ ↦
  (fun w : {w : InfinitePlace F // w ≠ w₀} ↦ infiniteIdeleLog F (Subtype.val g) (Subtype.val w)) ∈
    regulatorParallelotope F b

/-- Paper: Definition A.2.3.6, p. 549. The archimedean domain consists of norm-one
ideles with logarithm in the parallelotope and chosen coordinate in the torsion sector. -/
def infiniteIdeleFundamentalDomain : Set N∞ :=
  {g | inLogBox g ∧ inTorsionSector F v₀ σ (atPlace g.val)}

/-- Paper: Definition A.2.3.6, p. 549. The only diagonal unit in the archimedean
domain is the identity. -/
theorem unit_mem_infiniteIdeleFundamentalDomain (u : (𝓞 F)ˣ) :
    unitAtInfinity u ∈ (N∞).subtype '' infiniteIdeleFundamentalDomain F b v₀ σ ↔ u = 1 := by
  sorry

variable (r : CommRing.Pic (𝓞 F) → (ideleNorm F).ker)
local notation "E∞" => infiniteIdeleFundamentalDomain F b v₀ σ
local notation "integralUnits" =>
  MonoidHom.range (Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside F ∅))))

/-- Paper: Definition A.2.3.6, p. 549. The global norm-one domain is the union of
the class representative translates of the archimedean domain times the finite integral units. -/
def ideleFundamentalDomain : Set N₁ :=
  ⋃ c, r c • {g : N₁ | g.val ∈ integralUnits ∧ atInfinity g.val ∈ (N∞).subtype '' E∞}

local notation "E₁" => ideleFundamentalDomain F b v₀ σ r
local notation "principal₁" =>
  MonoidHom.codRestrict (IdeleGroup.unitEmbedding (𝓞 F) F) N₁
    (fun x ↦ And.right (ideleNorm_spec F) (Set.mem_range_self x))

variable (hr₁ : r 1 = 1) (hr : ∀ c, ideleIdealClass F (r c).val = c)

include hr₁ hr in
/-- Paper: Definition A.2.3.6, p. 549. With the trivial class represented by one,
the only principal idele in the global domain is the identity. -/
theorem principal_mem_ideleFundamentalDomain (x : Fˣ) :
    principal₁ x ∈ E₁ ↔ x = 1 := by
  sorry

-- Remark A.2.3.7, p. 549, is a bibliographic identification of (A.2.3.14).

/-- Paper: Lemma A.2.3.8(1), p. 550. The archimedean domain has compact closure in
the norm-one group. -/
theorem infiniteIdeleFundamentalDomain_precompact : IsCompact (closure E∞) := by
  sorry

/-- Paper: Lemma A.2.3.8(1), p. 550. The archimedean domain also has compact closure
in the full archimedean idele group. -/
theorem infiniteIdeleFundamentalDomain_precompact_ambient :
    IsCompact (closure ((N∞).subtype '' E∞)) := by
  sorry

/-- Paper: Lemma A.2.3.8(1), p. 550. The archimedean domain has nonempty interior
relative to the norm-one group. -/
theorem infiniteIdeleFundamentalDomain_interior : (interior E∞).Nonempty := by
  sorry

local notation "archDomain" => (Subgroup.subtype N∞ '' E∞)

/-- Paper: Lemma A.2.3.8(2), p. 550. Diagonal unit translates cover exactly the
norm-one archimedean ideles. -/
theorem infiniteIdeleFundamentalDomain_cover :
    (⋃ u : (𝓞 F)ˣ, unitAtInfinity u • archDomain) = N∞ := by
  sorry

/-- Paper: Lemma A.2.3.8(2), p. 550. A nonidentity unit translates the archimedean
domain disjointly from itself. -/
theorem infiniteIdeleFundamentalDomain_disjoint (u : (𝓞 F)ˣ) (hu : u ≠ 1) :
    Disjoint (unitAtInfinity u • archDomain) archDomain := by
  sorry

/-- Paper: Lemma A.2.3.8(2), p. 550. The torsion translates recover the whole
preimage of the logarithmic parallelotope in the norm-one group. -/
theorem infiniteIdeleFundamentalDomain_torsion_cover :
    (⋃ u : Units.torsion F, unitAtInfinity u.val • archDomain) =
      (N∞).subtype '' {g : N∞ | inLogBox g} := by
  sorry

-- TODO(paper-gap): (A.2.3.18) repeats the closure where the preceding sentence specifies K.
-- The proof on p. 551 reduces the general compact K to the case K equal to the closure.

/-- Paper: Lemma A.2.3.8(3), p. 550. Only finitely many diagonal unit translates of
the closure meet a given compact set in the norm-one group.
Deviation: We use K as in the preceding sentence and the proof on p. 551. -/
theorem infiniteIdeleFundamentalDomain_finite_translates (K : Set N∞) (hK : IsCompact K) :
    {u : (𝓞 F)ˣ | ((unitAtInfinity u • ((N∞).subtype '' closure E∞)) ∩
      ((N∞).subtype '' K)).Nonempty}.Finite := by
  sorry

-- TODO(paper-gap): (A.2.3.20) describes a positive real ray. For complex v₀ the
-- sector in Definition A.2.3.6 is wider, as (A.2.3.21) on p. 551 also shows.

section ExactSequences

local notation "H" => (IdeleGroup.principalSubgroup (𝓞 F) F ⊔ integralUnits)

-- TODO(paper-gap): (A.2.3.22) leaves the arrows implicit. With multiplication as the
-- quotient map, diagonal units must enter the two factors with opposite exponents.

/-- Paper: Proposition A.2.3.9, p. 552. Multiplication of a principal idele and an
idele integral and invertible at all finite places is a strict quotient onto their
product subgroup. Its kernel is the diagonally embedded discrete group of global units.
Deviation: We order the factors as the discrete field units followed by the integral
idele group. For the multiplication map the two copies of a kernel unit are inverse. -/
theorem idele_principal_integral_exact :
    letI : TopologicalSpace Fˣ := ⊥
    letI : TopologicalSpace (𝓞 F)ˣ := ⊥
    let d := IdeleGroup.unitEmbedding (𝓞 F) F
    let j := Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom
    ∃ (i : (𝓞 F)ˣ →* Fˣ × (integralAdelesOutside F ∅)ˣ)
      (p : Fˣ × (integralAdelesOutside F ∅)ˣ →* ↥(H : Subgroup 𝕀[F])),
      (∀ u, (i u).1 = Units.map (algebraMap (𝓞 F) F).toMonoidHom u ∧
        j (i u).2 = (d (i u).1)⁻¹) ∧
      (∀ x, (p x).val = d x.1 * j x.2) ∧ IsClosedEmbedding i ∧
        MulExact i p ∧ IsOpenQuotientMap p := by
  sorry

/-- Paper: Proposition A.2.3.9, p. 552. The ideal class map is a strict quotient of
the ideles onto the discrete Picard group, with the principal times integral subgroup
as its closed kernel. -/
theorem idele_ideal_class_exact :
    letI : TopologicalSpace (CommRing.Pic (𝓞 F)) := ⊥
    ∃ p : 𝕀[F] →* CommRing.Pic (𝓞 F), (∀ g, p g = ideleIdealClass F g) ∧
      IsClosedEmbedding (Subgroup.subtype H) ∧ MulExact (Subgroup.subtype H) p ∧
      IsOpenQuotientMap p := by
  sorry

/-- Paper: Proposition A.2.3.9, p. 552. Restriction to norm one still gives a strict
quotient onto the discrete Picard group, with the norm-one part of the same kernel. -/
theorem normOne_ideal_class_exact :
    letI : TopologicalSpace (CommRing.Pic (𝓞 F)) := ⊥
    let H₁ := Subgroup.comap (Subgroup.subtype N₁) H
    ∃ p : N₁ →* CommRing.Pic (𝓞 F), (∀ g, p g = ideleIdealClass F g.val) ∧
      IsClosedEmbedding H₁.subtype ∧ MulExact H₁.subtype p ∧ IsOpenQuotientMap p := by
  sorry

end ExactSequences

section Representatives

include hr₁ hr in
/-- Paper: Proposition A.2.3.10(1), p. 552. The global domain has compact closure
in the norm-one ideles. -/
theorem ideleFundamentalDomain_precompact : IsCompact (closure E₁) := by
  sorry

include hr₁ hr in
/-- Paper: Proposition A.2.3.10(1), p. 552. The global domain has nonempty interior
in the norm-one ideles. -/
theorem ideleFundamentalDomain_interior : (interior E₁).Nonempty := by
  sorry

include hr₁ hr in
/-- Paper: Proposition A.2.3.10(2), p. 552. Principal translates cover the norm-one ideles. -/
theorem ideleFundamentalDomain_cover : (⋃ x : Fˣ, principal₁ x • E₁) = Set.univ := by
  sorry

include hr₁ hr in
/-- Paper: Proposition A.2.3.10(2), p. 552. A nonidentity principal translate is
disjoint from the global domain. -/
theorem ideleFundamentalDomain_disjoint (x : Fˣ) (hx : x ≠ 1) :
    Disjoint (principal₁ x • E₁) E₁ := by
  sorry

include hr₁ hr in
/-- Paper: Proposition A.2.3.10(3), p. 552. Only finitely many principal translates
of the closure of the global domain meet a given compact subset of the norm-one ideles. -/
theorem ideleFundamentalDomain_finite_translates (K : Set N₁) (hK : IsCompact K) :
    {x : Fˣ | ((principal₁ x • closure E₁) ∩ K).Nonempty}.Finite := by
  sorry

variable (s : ℝ≥0ˣ →* (InfiniteAdeleRing F)ˣ) (hs : Continuous s) (hn : RightInverse s (infiniteIdeleNorm F))

include hs hn in
/-- Paper: Lemma A.2.3.11, p. 553. Multiplication by any continuous homomorphic
section splits the archimedean norm as a Lie group product. In mixed real and complex
coordinates both directions extend smoothly to open neighborhoods of their domains. -/
theorem infiniteIdeleNormSection_product :
    let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
    ∃ e : (ℝ≥0ˣ × N∞) ≃ₜ* 𝕀∞, (∀ t g, e (t, g) = s t * g.val) ∧
      (∃ f : ℝ × mixedEmbedding.mixedSpace F → mixedEmbedding.mixedSpace F,
        ContDiffOn ℝ ∞ f {z | 0 < z.1} ∧
        ∀ (t : ℝ≥0ˣ) (g : N∞), f ((t.val : ℝ), m g.val.val) = m (e (t, g)).val) ∧
      (∃ f : mixedEmbedding.mixedSpace F → ℝ × mixedEmbedding.mixedSpace F,
        ContDiffOn ℝ ∞ f {z | IsUnit z} ∧ ∀ g : 𝕀∞, f (m g.val) =
          (((e.symm g).1.val : ℝ), m (e.symm g).2.val.val)) := by
  sorry

include hr₁ hr hs hn in
/-- Paper: Lemma A.2.3.12, p. 553. Multiplication of a principal idele, a section
value supported at infinity and a global domain element parametrizes all ideles bijectively. -/
theorem ideleFundamentalDomain_bijective :
    let j : 𝕀∞ →* 𝕀[F] := fromInfinity
    Bijective (fun z : Fˣ × ℝ≥0ˣ × E₁ ↦
      IdeleGroup.unitEmbedding (𝓞 F) F z.1 * j (s z.2.1) * z.2.2.val.val) := by
  sorry

end Representatives

local notation "placeSection" =>
  MonoidHom.comp (Units.map (InfiniteAdeleRing.ofCompletion v₀))
    (infinitePlaceRealPower F v₀ ((InfinitePlace.mult v₀ : ℝ)⁻¹))

variable (K : Set ℝ≥0ˣ) (hK : IsCompact K)
local notation "productLocus" => (placeSection '' K) * (Subgroup.subtype N∞ '' closure E∞)

include hK in
/-- Paper: Lemma A.2.3.13(1), p. 553. Multiplying the closed archimedean domain by
a compact subset of the positive subgroup at the chosen place gives a compact set.
The positive subgroup is parametrized by the single-place norm section. -/
theorem infiniteIdele_product_compact : IsCompact productLocus := by
  sorry

include hK in
/-- Paper: Lemma A.2.3.13(1), p. 553. If the compact set has interior in the
positive subgroup, the product has interior in the archimedean ideles. -/
theorem infiniteIdele_product_interior (hi : (interior K).Nonempty) :
    (interior productLocus).Nonempty := by
  sorry

include hK in
/-- Paper: Lemma A.2.3.13(2), p. 553. The product in the archimedean adele ring
misses every coordinate hyperplane. -/
theorem infiniteIdele_product_disjoint_hyperplanes :
    Disjoint (Units.val '' productLocus) (⋃ v : InfinitePlace F, {a : InfiniteAdeleRing F | a v = 0}) := by
  sorry

include hK in
/-- Paper: Lemma A.2.3.13(3), p. 553. If the compact set has interior in the positive
subgroup, the product also has interior in the archimedean adele ring. -/
theorem infiniteIdele_product_adele_interior (hi : (interior K).Nonempty) :
    (interior (Units.val '' productLocus)).Nonempty := by
  sorry

section SLocal

variable (S : Finset (Primes(F)))
local notation "Oₛ(" F ", " S ")" => Set.integer (S : Set (Primes(F))) F
local notation "𝕀ₛ" => (SAdeleRing F S)ˣ
local notation "Nₛ" => MonoidHom.ker (sIdeleNorm F S)
local notation "projectS" => Units.map (RingHom.toMonoidHom (adeleProjection F S))
local notation "outsideInclusion" =>
  Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside F S)))
local notation "diagonalS" => Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S))
local notation "unitAtS" => MonoidHom.comp projectS (MonoidHom.comp outsideInclusion diagonalS)

variable {ι : Type*} (a : Module.Basis ι ℤ (𝓞 F))

/-- Paper: Definition A.2.4.1, p. 554. The S-adelic domain is the archimedean half-open
parallelepiped of the integral basis times the local integer rings at the finite places in S. -/
def sAdeleFundamentalDomain : Set (SAdeleRing F S) :=
  {x | x.1 ∈ infiniteAdeleFundamentalDomain F a ∧ ∀ v : S, x.2 v ∈ v.val.adicCompletionIntegers F}

local notation "Dₛ" => sAdeleFundamentalDomain F S a
local notation "addAtS" =>
  RingHom.comp (adeleProjection F S)
    (RingHom.comp (Subring.subtype (integralAdelesOutside F S)) (integralAdeleDiagonal F S))

/-- Paper: Definition A.2.4.1, p. 554. The only diagonal S-integer in the domain is zero. -/
theorem diagonal_mem_sAdeleFundamentalDomain (x : Oₛ(F, S)) : addAtS x ∈ Dₛ ↔ x = 0 := by
  sorry

/-- Paper: Lemma A.2.4.2(1), p. 554. S-integer translates of the additive domain
cover the S-adeles. -/
theorem sAdeleFundamentalDomain_cover : (⋃ x : Oₛ(F, S), addAtS x +ᵥ Dₛ) = Set.univ := by
  sorry

/-- Paper: Lemma A.2.4.2(2), p. 554. Only finitely many diagonal S-integer translates
of the closure meet a given compact subset of the S-adeles. -/
theorem sAdeleFundamentalDomain_finite_translates (K : Set (SAdeleRing F S)) (hK : IsCompact K) :
    {x : Oₛ(F, S) | ((addAtS x +ᵥ closure Dₛ) ∩ K).Nonempty}.Finite := by
  sorry

/-- Paper: Definition A.2.4.3, p. 554. The S-logarithm has one normalized log absolute
value for each infinite place and each selected finite place, as in (A.2.4.7) on p. 555. -/
def sIdeleLog (g : 𝕀ₛ) : InfinitePlace F ⊕ S → ℝ :=
  Sum.elim (fun v ↦ v.mult * Real.log ‖g.val.1 v‖) (fun v ↦ Real.log ‖g.val.2 v‖)

/-- Paper: Definition A.2.4.3, p. 555. Summing all S-logarithmic coordinates gives
the logarithm of the S-idelic norm. -/
theorem sIdeleLog_sum (g : 𝕀ₛ) :
    ∑ v, sIdeleLog F S g v = Real.log ((sIdeleNorm F S g).val : ℝ) := by
  sorry

/-- Paper: Definition A.2.4.3, p. 554. On diagonal S-units the S-logarithm vanishes
exactly on torsion units. -/
theorem sIdeleLog_unit_eq_zero (u : Oₛ(F, S)ˣ) :
    sIdeleLog F S (unitAtS u) = 0 ↔ u ∈ CommGroup.torsion Oₛ(F, S)ˣ := by
  sorry

/-- Paper: §A.2.4.2, p. 554. The roots of unity in the ordinary units map onto
the full torsion subgroup of the S-units, so its order is independent of S. -/
theorem sUnit_torsion_eq_image :
    (Units.torsion F).map (Units.map (algebraMap (𝓞 F) Oₛ(F, S)).toMonoidHom) =
      CommGroup.torsion Oₛ(F, S)ˣ := by
  sorry

local notation "sRank(" F ", " S ")" => (Fintype.card (InfinitePlace F) + Finset.card S - 1)
variable (bₛ : Module.Basis (Fin sRank(F, S)) ℤ (Additive (Oₛ(F, S)ˣ ⧸ CommGroup.torsion Oₛ(F, S)ˣ)))

-- TODO(paper-gap): (A.2.4.8) says to choose a basis of the full S-unit group, which
-- contains the nonidentity torsion unit -1. As in (A.2.3.7), a basis is taken modulo torsion.

/-- Paper: Definition A.2.4.3, p. 555. The S-parallelotope consists of the sums of
basis logarithms with each real coefficient in the half-open unit interval.
Deviation: The integral basis is of the S-units modulo torsion. We take representatives
to evaluate their logarithms. -/
def sRegulatorParallelotope : Set (InfinitePlace F ⊕ S → ℝ) :=
  {y | ∃ t : Fin sRank(F, S) → ℝ, (∀ i, t i ∈ Set.Ico 0 1) ∧
    y = ∑ i, t i • sIdeleLog F S (unitAtS (bₛ i).toMul.out)}

/-- Paper: Definition A.2.4.3, p. 555. The S-parallelotope is contained in the
hyperplane where the sum of the coordinates vanishes. -/
theorem sRegulatorParallelotope_sum_zero (y : InfinitePlace F ⊕ S → ℝ)
    (hy : y ∈ sRegulatorParallelotope F S bₛ) : ∑ v, y v = 0 := by
  sorry

/-- Paper: Definition A.2.4.3, p. 555. Along a basis logarithm the parallelotope
includes the coefficient zero and excludes one. Any lift of the basis unit gives the same test.
Deviation: We use the basis modulo torsion specified for (A.2.4.8). -/
theorem sRegulatorParallelotope_basis_line (i : Fin sRank(F, S)) (u : Oₛ(F, S)ˣ)
    (hu : QuotientGroup.mk u = (bₛ i).toMul) (t : ℝ) :
    t • sIdeleLog F S (unitAtS u) ∈ sRegulatorParallelotope F S bₛ ↔ t ∈ Set.Ico 0 1 := by
  sorry

/-- Paper: Definition A.2.4.3, p. 554. The local norm-one domain cuts out the
S-parallelotope in logarithmic coordinates and the torsion sector at the chosen infinite place. -/
def sLocalIdeleFundamentalDomain : Set Nₛ :=
  {g | sIdeleLog F S g.val ∈ sRegulatorParallelotope F S bₛ ∧
    inTorsionSector F v₀ σ (atPlace (Units.map (RingHom.fst _ _).toMonoidHom g.val))}

local notation "Eₛ" => sLocalIdeleFundamentalDomain F v₀ σ S bₛ

/-- Paper: Definition A.2.4.3, p. 554. The local domain contains exactly one
diagonal S-unit, namely the identity. -/
theorem unit_mem_sLocalIdeleFundamentalDomain (u : Oₛ(F, S)ˣ) :
    unitAtS u ∈ Subgroup.subtype Nₛ '' Eₛ ↔ u = 1 := by
  sorry

local notation "outsideNormOne(" F ", " S ")" => MonoidHom.ker (MonoidHom.comp (ideleNorm F)
  (Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside F S)))))
local notation "Picₛ(" F ", " S ")" => CommRing.Pic Oₛ(F, S)

-- TODO(paper-gap): In (A.2.4.4) every allowed representative is a unit outside S and
-- therefore has trivial S-ideal class. The prescribed family need not exist.

/-- Paper: Definition A.2.4.3, p. 554. Every idele integral and invertible outside
S has trivial ideal class after extension to the S-integers.
Deviation: This is the obstruction to the representatives prescribed for (A.2.4.4). -/
theorem sIdele_ideal_class_trivial (g : (integralAdelesOutside F S)ˣ) :
    CommRing.Pic.mapAlgebra (𝓞 F) Oₛ(F, S) (ideleIdealClass F (outsideInclusion g)) = 1 := by
  sorry

/-- Paper: Definition A.2.4.3, p. 554. Equation (A.2.4.4) takes a union of translates
of the local domain times the outside integral units, inside the norm-one group integral
and invertible outside S.
Deviation: The displayed union is defined for supplied translating elements. The paper's
class representative condition is impossible when the S-class group is nontrivial. -/
def sIdeleFundamentalDomain (rₛ : Picₛ(F, S) → outsideNormOne(F, S)) : Set outsideNormOne(F, S) :=
  ⋃ c, rₛ c • {g : outsideNormOne(F, S) |
    projectS (outsideInclusion g.val) ∈ (Subgroup.subtype Nₛ '' Eₛ)}

/-- Paper: Definition A.2.4.3, p. 554. With trivial S-class group and its prescribed
identity representative, membership in the displayed union is tested by projection to S. -/
theorem mem_sIdeleFundamentalDomain_of_classNumberOne [Subsingleton Picₛ(F, S)]
    (rₛ : Picₛ(F, S) → outsideNormOne(F, S)) (h₁ : rₛ 1 = 1) (g : outsideNormOne(F, S)) :
    g ∈ sIdeleFundamentalDomain F v₀ σ S bₛ rₛ ↔
      projectS (outsideInclusion g.val) ∈ (Subgroup.subtype Nₛ '' Eₛ) := by
  sorry

/-- Paper: Proposition A.2.4.4(1), p. 555. The local domain has compact closure in
the norm-one S-ideles. -/
theorem sLocalIdeleFundamentalDomain_precompact : IsCompact (closure Eₛ) := by
  sorry

/-- Paper: Proposition A.2.4.4(1), p. 555. The local domain has nonempty interior in
the norm-one S-ideles. -/
theorem sLocalIdeleFundamentalDomain_interior : (interior Eₛ).Nonempty := by
  sorry

local notation "localDomain" => (Subgroup.subtype Nₛ '' Eₛ)

/-- Paper: Proposition A.2.4.4(2), p. 555. The diagonal S-unit translates of the local
domain cover exactly the norm-one S-ideles. -/
theorem sLocalIdeleFundamentalDomain_cover :
    (⋃ u : Oₛ(F, S)ˣ, unitAtS u • localDomain) = Nₛ := by
  sorry

/-- Paper: Proposition A.2.4.4(2), p. 555. Every nonidentity S-unit translates the
local domain disjointly from itself. -/
theorem sLocalIdeleFundamentalDomain_disjoint (u : Oₛ(F, S)ˣ) (hu : u ≠ 1) :
    Disjoint (unitAtS u • localDomain) localDomain := by
  sorry

/-- Paper: Proposition A.2.4.4(3), p. 555. Only finitely many S-unit translates of
the closure meet a given compact subset of the norm-one S-ideles. -/
theorem sLocalIdeleFundamentalDomain_finite_translates (K : Set Nₛ) (hK : IsCompact K) :
    {u : Oₛ(F, S)ˣ | ((unitAtS u • (Subgroup.subtype Nₛ '' closure Eₛ)) ∩
      (Subgroup.subtype Nₛ '' K)).Nonempty}.Finite := by
  sorry

-- TODO(paper-gap): Proposition A.2.4.4(4) requires the nonexistent representatives
-- of (A.2.4.4) in the nontrivial class group case. The identity represents the trivial case.

variable [Subsingleton Picₛ(F, S)] (rₛ : Picₛ(F, S) → outsideNormOne(F, S)) (h₁ : rₛ 1 = 1)
local notation "globalSDomain" => sIdeleFundamentalDomain F v₀ σ S bₛ rₛ

include h₁ in
/-- Paper: Proposition A.2.4.4(4), p. 555. The domain with outside unit factors has
compact closure in the norm-one group integral and invertible outside S.
Deviation: We state the case where the prescribed representatives exist. -/
theorem sIdeleFundamentalDomain_precompact : IsCompact (closure globalSDomain) := by
  sorry

include h₁ in
/-- Paper: Proposition A.2.4.4(4), p. 555. The domain with outside unit factors has
nonempty interior relative to that group.
Deviation: We assume the S-class group is trivial. -/
theorem sIdeleFundamentalDomain_interior : (interior globalSDomain).Nonempty := by
  sorry

include h₁ in
/-- Paper: Proposition A.2.4.4(4), p. 555. S-unit translates cover the norm-one
group integral and invertible outside S.
Deviation: We assume the S-class group is trivial. -/
theorem sIdeleFundamentalDomain_cover :
    (⋃ u : Oₛ(F, S)ˣ, diagonalS u • (Subgroup.subtype outsideNormOne(F, S) '' globalSDomain)) =
      outsideNormOne(F, S) := by
  sorry

include h₁ in
/-- Paper: Proposition A.2.4.4(4), p. 555. A nonidentity S-unit translates the domain
with outside unit factors disjointly from itself.
Deviation: We assume the S-class group is trivial. -/
theorem sIdeleFundamentalDomain_disjoint (u : Oₛ(F, S)ˣ) (hu : u ≠ 1) :
    let E := Subgroup.subtype outsideNormOne(F, S) '' globalSDomain
    Disjoint (diagonalS u • E) E := by
  sorry

/-- Paper: Remark A.2.4.5, p. 555. All sufficiently large finite sets of places have
trivial S-ideal class group. The finite set parameter lists the finite places only. -/
theorem eventually_trivial_sIdealClassGroup :
    ∃ T : Finset (Primes(F)), ∀ S : Finset (Primes(F)), T ⊆ S →
      Subsingleton (CommRing.Pic (Set.integer (S : Set (Primes(F))) F)) := by
  sorry

/-- Paper: Remark A.2.4.5, p. 555. When the S-class group is trivial the inclusion
induces a topological isomorphism on idele classes, compatible with both norms. -/
theorem sIdeleClassGroup_equiv_of_classNumberOne :
    ∃ e : SIdeleClassGroup F S ≃ₜ* IdeleClassGroup (𝓞 F) F,
      (∀ g : (integralAdelesOutside F S)ˣ, e (QuotientGroup.mk g) =
        QuotientGroup.mk (outsideInclusion g)) ∧ ∀ c, ideleClassNorm F (e c) = sIdeleClassNorm F S c := by
  sorry

-- TODO(paper-gap): Remark A.2.4.5 asserts coverage of the full norm-one ideles before
-- taking classes. For F = ℚ a principal prime outside S is a norm-one idele and is
-- not a unit at that prime. All the proposed S-unit translates are units there.

/-- Paper: Remark A.2.4.5, p. 555. For any finite set of rational places a principal
prime idele has norm one and lies outside the group of ideles invertible off that set.
Deviation: This gives a counterexample to the asserted cover inside the full norm-one group. -/
theorem exists_rat_prime_idele_outside (S : Finset (Primes(ℚ))) :
    ∃ (p : ℕ) (u : ℚˣ), p.Prime ∧ u.val = (p : ℚ) ∧
      let g := IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ u
      g ∈ (ideleNorm ℚ).ker ∧ g ∉ (Units.map (integralAdelesOutside ℚ S).subtype.toMonoidHom).range := by
  sorry

end SLocal

end RiemannMasullo
