module

public import RiemannMasullo.Ch02_AdelicTheta.Sec1
public import RiemannMasullo.AppA_AlgebraicNT.Sec3
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Schwartz–Bruhat topologies on elementary groups and idele class groups

Masullo, §D.1.10, pp. 783–792.
-/

@[expose] public noncomputable section

open Bornology Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Distributions ENNReal FourierTransform NNReal NumberField.AdeleRing Real SchwartzMap

namespace RiemannMasullo

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F

section IdeleInsertion

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "SUnits" => (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ

-- TODO(paper-gap): The sentence before (D.1.10.1) includes the outside-S integer
-- factors in A_{F,S}, although the insertion formula and (A.1.5.1) separate them.

/-- Paper: (D.1.10.1), p. 783. Take units of the subring of adeles integral
outside S and include them into the global idele group.
Deviation: Appendix A's integral-outside-S subring already includes the outside
factors. The finite set records the finite part of S. -/
def integralIdeleInsertion : (integralAdelesOutside F S)ˣ →* 𝕀[F] :=
  Units.map (integralAdelesOutside F S).subtype.toMonoidHom

/-- Paper: (D.1.10.1), p. 783. An idele in the image is a unit at every finite place
outside S, and every such idele occurs.
Deviation: Sanity check on the domain of insertion, phrased using the integral
coordinates of an idele and its inverse. -/
theorem mem_range_integralIdeleInsertion (g : 𝕀[F]) :
    g ∈ range (integralIdeleInsertion F S) ↔
      ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
        g.val.2 v ∈ v.adicCompletionIntegers F ∧
          g.inv.2 v ∈ v.adicCompletionIntegers F := by sorry

/-- Paper: Lemma D.1.10.1(1), p. 784. Insertion from the full S-stage is a continuous
injective open map. -/
theorem integralIdeleInsertion_isOpenEmbedding :
    IsOpenEmbedding (integralIdeleInsertion F S) := by sorry

/-- Paper: Lemma D.1.10.1(1), p. 784. The diagonal S-unit actions on the stage and
on the global ideles are continuous, and insertion intertwines left translation.
Deviation: The target diagonal is evaluated by mapping S-units to F-units. -/
theorem integralIdeleInsertion_equivariant :
    letI : TopologicalSpace SUnits := ⊥
    let d := Units.map (integralAdeleDiagonal F S).toMonoidHom
    let e := (IdeleGroup.unitEmbedding (𝓞 F) F).comp
      (Units.map (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F).val.toRingHom.toMonoidHom)
    Continuous (fun x : SUnits × (integralAdelesOutside F S)ˣ ↦ d x.1 * x.2) ∧
    Continuous (fun x : SUnits × 𝕀[F] ↦ e x.1 * x.2) ∧
    ∀ u g, integralIdeleInsertion F S (d u * g) =
      e u * integralIdeleInsertion F S g := by sorry

-- TODO(paper-gap): D.1.10.1(2) names only GL₁(A_{F,S}). With the finite-product
-- convention of (A.1.5.1), inserting 1 off S misses ideles with infinitely many
-- nonidentity unit coordinates. The colimit below uses the full stages of (D.1.10.1).

/-- Paper: Lemma D.1.10.1(2), p. 784. Images of the full S-stages increase
with S and exhaust the global ideles.
Deviation: The source is the full stage in (D.1.10.1), with the outside local units. -/
theorem integralIdeleInsertion_exhaustive :
    Monotone (fun T : Finset (HeightOneSpectrum (𝓞 F)) ↦
      range (integralIdeleInsertion F T)) ∧
    ∀ g : 𝕀[F], ∃ T, g ∈ range (integralIdeleInsertion F T) := by sorry

/-- Paper: Lemma D.1.10.1(2), p. 784. The topology on the union of the full S-stages
is final for their insertions. Their transition maps are the inclusions of the images.
Deviation: The source is the full stage in (D.1.10.1), with the outside local units. -/
theorem integralIdeleInsertion_finalTopology (U : Set 𝕀[F]) :
    IsOpen U ↔ ∀ T : Finset (HeightOneSpectrum (𝓞 F)),
      IsOpen (integralIdeleInsertion F T ⁻¹' U) := by sorry

/-- Paper: (D.1.10.2), p. 784. The composite of insertion with the global class map
kills the diagonal S-units. -/
theorem integralIdeleInsertion_descends :
    (Units.map (integralAdeleDiagonal F S).toMonoidHom).range ≤
      ((QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)).comp
        (integralIdeleInsertion F S)).ker := by sorry

/-- Paper: (D.1.10.2), p. 784. Insert an S-idele representative and take its global
idele class. The source is Appendix A's S-idele class group. -/
def sIdeleClassInsertion : SIdeleClassGroup F S →* C[F] :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)).comp
      (integralIdeleInsertion F S)) (integralIdeleInsertion_descends F S)

/-- Paper: (D.1.10.2), p. 784. The class insertion is determined by insertion on
representatives.
Deviation: Sanity check stated as the unique descent of the representative map. -/
theorem sIdeleClassInsertion_unique :
    (∀ u : (integralAdelesOutside F S)ˣ,
      sIdeleClassInsertion F S (QuotientGroup.mk u) =
        QuotientGroup.mk (integralIdeleInsertion F S u)) ∧
    ∀ j : SIdeleClassGroup F S →* C[F],
      (∀ u : (integralAdelesOutside F S)ˣ,
        j (QuotientGroup.mk u) = QuotientGroup.mk (integralIdeleInsertion F S u)) →
      j = sIdeleClassInsertion F S := by sorry

/-- Paper: Lemma D.1.10.1(3), p. 784. The induced map of class groups is
continuous, injective and open. -/
theorem sIdeleClassInsertion_isOpenEmbedding : IsOpenEmbedding (sIdeleClassInsertion F S) :=
  by sorry

/-- Paper: Lemma D.1.10.1(3), p. 784. The quotient by the image of the S-idele
classes is isomorphic to the finite Picard group of the S-integer ring. -/
theorem sIdeleClassInsertion_cokernel :
    Nonempty ((C[F] ⧸ (sIdeleClassInsertion F S).range) ≃*
      CommRing.Pic (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)) ∧
    Finite (C[F] ⧸ (sIdeleClassInsertion F S).range) := by sorry

/-- Paper: Lemma D.1.10.1(3), p. 784. Insertion restricts to a topological
group isomorphism between the identity components. -/
theorem sIdeleClassInsertion_connectedComponent :
    ∃ e : Subgroup.connectedComponentOfOne (SIdeleClassGroup F S) ≃ₜ*
        Subgroup.connectedComponentOfOne C[F],
      ∀ x, (e x).val = sIdeleClassInsertion F S x.val := by sorry

/-- Paper: Lemma D.1.10.1(3), p. 784. For all sufficiently large finite sets the
insertion is surjective, and hence is an isomorphism by openness and injectivity. -/
theorem sIdeleClassInsertion_eventually_surjective :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ U, T ⊆ U →
      Surjective (sIdeleClassInsertion F U) := by sorry

end IdeleInsertion

section SchwartzTopologies

/-- Paper: Proposition D.1.10.2, p. 784. A family of extended values generates
the topology when its values are exactly those of real generating seminorms.
Deviation: This common formulation also records finiteness of all the values. -/
def GeneratesSeminormTopology {E ι : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (v : ι → E → ℝ≥0∞) : Prop :=
  ∃ P : ι → Seminorm ℂ E, WithSeminorms P ∧ ∀ i f, ENNReal.ofReal (P i f) = v i f

/-- Paper: Proposition D.1.10.2, p. 784. Boundedness is equivalent to an upper bound
for the values of each generating seminorm on the set.
Deviation: Sanity check on the topology formulation, stated with finite bounds. -/
theorem GeneratesSeminormTopology.isVonNBounded_iff
    {E ι : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {v : ι → E → ℝ≥0∞} (hv : GeneratesSeminormTopology v) (B : Set E) :
    IsVonNBounded ℂ B ↔ ∀ i, ∃ C : ℝ≥0, ∀ f ∈ B, v i f ≤ (C : ℝ≥0∞) := by
  obtain ⟨P, hP, hvalues⟩ := hv
  simp_rw [hP.isVonNBounded_iff_seminorm_bounded, ← hvalues, ENNReal.ofReal_le_coe]
  constructor
  · intro h i
    obtain ⟨r, hr, hbound⟩ := h i
    exact ⟨⟨r, hr.le⟩, fun f hf ↦ (hbound f hf).le⟩
  · intro h i
    obtain ⟨C, hbound⟩ := h i
    exact ⟨(C : ℝ) + 1, by positivity, fun f hf ↦ lt_of_le_of_lt (hbound f hf) (lt_add_one _)⟩

/-- Paper: Proposition D.1.10.2, p. 784. A family of function transforms gives a
generating Lᵖ family if the transforms belong to Lᵖ and their norms generate the topology.
Deviation: Membership is explicit so the extended norm cannot hide a measurability
or integrability condition. -/
def GeneratesLpSeminorms {E ι X : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [MeasurableSpace X] (μ : Measure X) (p : ℝ≥0∞)
    (u : ι → E → X → ℂ) : Prop :=
  (∀ i f, MemLp (u i f) p μ) ∧
    GeneratesSeminormTopology (fun i f ↦ eLpNorm (u i f) p μ)

/-- Paper: Proposition D.1.10.2, p. 784. Bounds on each Lᵖ norm characterize
bounded sets when the Lᵖ family generates.
Deviation: Sanity check stated in terms of the actual extended norms. -/
theorem GeneratesLpSeminorms.isVonNBounded_iff
    {E ι X : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞} {u : ι → E → X → ℂ}
    (h : GeneratesLpSeminorms μ p u) (B : Set E) :
    IsVonNBounded ℂ B ↔
      ∀ i, ∃ C : ℝ≥0, ∀ f ∈ B, eLpNorm (u i f) p μ ≤ (C : ℝ≥0∞) := by sorry

/-- Paper: (D.1.10.3), p. 784. Apply the nth derivative, Fourier transform,
and then apply the mth derivative. -/
def realSchwartzFourierDeriv (m n : ℕ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (SchwartzMap.derivCLM ℂ ℂ)^[m] (𝓕 ((SchwartzMap.derivCLM ℂ ℂ)^[n] f))

/-- Paper: (D.1.10.3), p. 784. With both differentiation orders zero only
the Fourier transform remains.
Deviation: Sanity check on the differential orders. -/
theorem realSchwartzFourierDeriv_zero (f : 𝓢(ℝ, ℂ)) :
    realSchwartzFourierDeriv 0 0 f = 𝓕 f := by sorry

/-- Paper: Proposition D.1.10.2, p. 784. L² norms of the differentiated real
Fourier transforms in (D.1.10.3) generate the Schwartz topology. -/
theorem realSchwartz_fourierLp_generates :
    GeneratesLpSeminorms (volume : Measure ℝ) 2
      (fun i : ℕ × ℕ ↦ fun f : 𝓢(ℝ, ℂ) ↦
        (realSchwartzFourierDeriv i.1 i.2 f : ℝ → ℂ)) := by sorry

/-- Paper: Proposition D.1.10.2, p. 784. A set of real Schwartz functions is bounded
exactly when each Fourier L² seminorm is bounded on it. -/
theorem realSchwartz_fourierLp_bounded_iff (B : Set (𝓢(ℝ, ℂ))) :
    IsVonNBounded ℂ B ↔ ∀ m n : ℕ, ∃ C : ℝ≥0, ∀ f ∈ B,
      eLpNorm (realSchwartzFourierDeriv m n f : ℝ → ℂ) 2 volume ≤ (C : ℝ≥0∞) := by sorry

-- TODO(paper-gap): The last sum in (D.1.10.5) omits the constant term k = 0.
-- For m = n = 0 and N = 1, bumps concentrated at 0 disprove that estimate.

/-- Paper: (D.1.10.6)–(D.1.10.8), p. 785. Multiply the coordinate mixed partial
of a Euclidean Schwartz function by the coordinate monomial. -/
def euclideanSchwartzMonomialPartial {m : ℕ} (α β : Fin m → ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (x : EuclideanSpace ℝ (Fin m)) : ℂ :=
  (∏ i, (x i : ℂ) ^ α i) *
    elementaryPartial (fun g : ElementaryLieGroup m 0 0 PUnit.{1} ↦ f g.1)
      β 0 (x, 0) 0 PUnit.unit

/-- Paper: (D.1.10.6)–(D.1.10.8), p. 785. At zero multi-indices the weighted
partial is the original function.
Deviation: Sanity check on the weight and derivative. -/
theorem euclideanSchwartzMonomialPartial_zero {m : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (x : EuclideanSpace ℝ (Fin m)) :
    euclideanSchwartzMonomialPartial 0 0 f x = f x := by sorry

/-- Paper: Example D.1.10.3, p. 785. Supremum norms of the monomial-weighted
Euclidean partials generate the usual Schwartz topology. -/
theorem euclideanSchwartz_monomialSup_generates (m : ℕ) (hm : 1 ≤ m) :
    GeneratesSeminormTopology (fun i : (Fin m → ℕ) × (Fin m → ℕ) ↦
      fun f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ) ↦
        ⨆ x, (‖euclideanSchwartzMonomialPartial i.1 i.2 f x‖₊ : ℝ≥0∞)) := by sorry

/-- Paper: Example D.1.10.3(1)–(2), p. 785. For every real p at least one,
the Lᵖ norms of the monomial-weighted Euclidean partials generate the topology.
Deviation: The same statement includes p = 1 and p > 1. -/
theorem euclideanSchwartz_monomialLp_generates (m : ℕ) (hm : 1 ≤ m) (p : ℝ) (hp : 1 ≤ p) :
    GeneratesLpSeminorms (volume : Measure (EuclideanSpace ℝ (Fin m))) (ENNReal.ofReal p)
      (fun i : (Fin m → ℕ) × (Fin m → ℕ) ↦ euclideanSchwartzMonomialPartial i.1 i.2) := by sorry

/-- Paper: (D.1.10.9)–(D.1.10.10), p. 785. On the torus take the mixed partial
by differentiating the periodic lift.
Deviation: We evaluate the lifted partial at the representative in the unit cube. -/
def torusSchwartzPartial {n : ℕ} (β : Fin n → ℕ)
    (f : ElementarySchwartz 0 n 0 PUnit) (z : Fin n → AddCircle (1 : ℝ)) : ℂ :=
  elementaryPartial f 0 β
    (0, WithLp.toLp 2 (fun i ↦ (AddCircle.equivIco (1 : ℝ) 0 (z i)).val)) 0 PUnit.unit

/-- Paper: (D.1.10.9)–(D.1.10.10), p. 785. The partial of order zero evaluates
the original function on the torus.
Deviation: Sanity check for the chosen lift. -/
theorem torusSchwartzPartial_zero {n : ℕ}
    (f : ElementarySchwartz 0 n 0 PUnit) (z : Fin n → AddCircle (1 : ℝ)) :
    torusSchwartzPartial 0 f z = f (0, z, 0, PUnit.unit) := by sorry

/-- Paper: Example D.1.10.4, p. 785. Supremum norms of the torus partials
generate the smooth topology. -/
theorem torusSchwartz_sup_generates (n : ℕ) (hn : 1 ≤ n) :
    GeneratesSeminormTopology (fun β : Fin n → ℕ ↦
      fun f : ElementarySchwartz 0 n 0 PUnit ↦
        ⨆ z, (‖torusSchwartzPartial β f z‖₊ : ℝ≥0∞)) := by sorry

/-- Paper: Example D.1.10.4, p. 785. With product probability Haar measure, the Lᵖ
norms of torus partials generate the smooth topology for each finite real p ≥ 1.
Deviation: The stage with only torus coordinates represents the smooth space. -/
theorem torusSchwartz_lp_generates (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp : 1 ≤ p) :
    GeneratesLpSeminorms (Measure.pi (fun _ : Fin n ↦ AddCircle.haarAddCircle (T := (1 : ℝ))))
      (ENNReal.ofReal p) (torusSchwartzPartial (n := n)) := by sorry

/-- Paper: (D.1.10.12), p. 786. Multiply a rapidly decreasing sequence
by the integer coordinate monomial. -/
def latticeSchwartzMonomial {r : ℕ} (γ : Fin r → ℕ)
    (f : RapidDecaySequence r) (a : Fin r → ℤ) : ℂ :=
  (∏ i, (a i : ℂ) ^ γ i) * f a

/-- Paper: (D.1.10.12), p. 786. The zero weight leaves the sequence unchanged.
Deviation: Sanity check on the weight. -/
theorem latticeSchwartzMonomial_zero {r : ℕ} (f : RapidDecaySequence r) (a : Fin r → ℤ) :
    latticeSchwartzMonomial 0 f a = f a := by sorry

/-- Paper: Example D.1.10.5, p. 786. The weighted sup norms generate the
rapidly decreasing sequence topology on the integer lattice. -/
theorem latticeSchwartz_sup_generates (r : ℕ) :
    GeneratesSeminormTopology (fun γ : Fin r → ℕ ↦ fun f : RapidDecaySequence r ↦
      ⨆ a, (‖latticeSchwartzMonomial γ f a‖₊ : ℝ≥0∞)) := by sorry

/-- Paper: Example D.1.10.5, p. 786. The counting-measure Lᵖ seminorms of
the monomial-weighted sequences generate the rapidly decreasing sequence topology. -/
theorem latticeSchwartz_lp_generates (r p : ℕ) (hp : 1 ≤ p) :
    GeneratesLpSeminorms (Measure.count : Measure (Fin r → ℤ)) (p : ℝ≥0∞)
      (latticeSchwartzMonomial (r := r)) := by sorry

end SchwartzTopologies

section ElementaryOperators

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Paper: Proposition D.1.10.6(3)–(4), p. 787. Repeat the first-order operator
in each direction according to its multi-index and compose the resulting operators. -/
def bruhatDiffMonomial {d : ℕ} (a : Fin d → LCATopologicalLie G) (α : Fin d → ℕ) :
    bruhatDiffAlgebra G :=
  bruhatDiffWord ((List.finRange d).flatMap fun j ↦ List.replicate (α j) (a j))

/-- Paper: Proposition D.1.10.6(3)–(4), p. 787. The multi-index of weight one in
one direction gives the corresponding first-order operator.
Deviation: Sanity check on repetition of directions. -/
theorem bruhatDiffMonomial_single {d : ℕ} (a : Fin d → LCATopologicalLie G) (j : Fin d) :
    bruhatDiffMonomial a (Pi.single j 1) = bruhatDiffGenerator (a j) := by sorry

/-- Paper: Proposition D.1.10.6(1)–(2), p. 787. Differentiate a Schwartz–Bruhat
function and multiply it by the symbol of the dual operator through biduality. -/
def bruhatDiffSymbolWeightedApply (b : G ≃ₜ* PontryaginDual (PontryaginDual G))
    (D : bruhatDiffAlgebra G) (E : bruhatDiffAlgebra (PontryaginDual G))
    (f : SchwartzBruhat G) (x : G) : ℂ :=
  bruhatDiffSymbol E (b x) *
    (D.val ⟨f, (mem_bruhatSmoothSubmodule_iff _).2 (schwartzBruhat_isBruhatSmooth f)⟩).val x

/-- Paper: Proposition D.1.10.6(1)–(2), p. 787. Applying the pair of identity
operators returns the original function.
Deviation: Sanity check on the symbol and application conventions. -/
theorem bruhatDiffSymbolWeightedApply_one
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (f : SchwartzBruhat G) :
    bruhatDiffSymbolWeightedApply b 1 1 f = (f : G → ℂ) := by sorry

variable (e : ElementaryLCAPresentation G)
variable (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (hb : ∀ x χ, b x χ = χ x)

include e hb

/-- Paper: Proposition D.1.10.6(1), p. 787. The sup norms of the symbol-weighted
derivatives for arbitrary pairs of invariant operators generate the Schwartz topology. -/
theorem elementarySchwartz_operatorSup_generates :
    GeneratesSeminormTopology (fun i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G) ↦
      fun f : SchwartzBruhat G ↦
        ⨆ x, (‖bruhatDiffSymbolWeightedApply b i.1 i.2 f x‖₊ : ℝ≥0∞)) := by sorry

/-- Paper: Proposition D.1.10.6(2), p. 787. For each integer q at least one,
the Lᵠ norms of the symbol-weighted derivatives generate the Schwartz topology. -/
theorem elementarySchwartz_operatorLp_generates [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (q : ℕ) (hq : 1 ≤ q) :
    GeneratesLpSeminorms μ (q : ℝ≥0∞)
      (fun i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G) ↦
        bruhatDiffSymbolWeightedApply b i.1 i.2) := by sorry

variable {d d' : ℕ}
variable (a : Fin d → LCATopologicalLie G) (a' : Fin d' → LCATopologicalLie (PontryaginDual G))
variable
  (ha : LinearIndependent ℝ (fun j ↦ bruhatFirstOrder (a j)))
  (hspan : Submodule.span ℝ (range (fun j ↦ bruhatFirstOrder (a j))) =
    bruhatDiffDegreeOneReal (G := G))
  (ha' : LinearIndependent ℝ (fun j ↦ bruhatFirstOrder (a' j)))
  (hspan' : Submodule.span ℝ (range (fun j ↦ bruhatFirstOrder (a' j))) =
    bruhatDiffDegreeOneReal (G := PontryaginDual G))

include ha hspan ha' hspan'

/-- Paper: Proposition D.1.10.6(3), p. 787. The monomials in any pair of real
first-order bases suffice for the sup family. -/
theorem elementarySchwartz_basisSup_generates :
    GeneratesSeminormTopology (fun i : (Fin d → ℕ) × (Fin d' → ℕ) ↦
      fun f : SchwartzBruhat G ↦ ⨆ x,
        (‖bruhatDiffSymbolWeightedApply b (bruhatDiffMonomial a i.1)
          (bruhatDiffMonomial a' i.2) f x‖₊ : ℝ≥0∞)) := by sorry

/-- Paper: Proposition D.1.10.6(4), p. 787. The monomials in any pair of real
first-order bases suffice for each finite integer Lᵠ family. -/
theorem elementarySchwartz_basisLp_generates [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (q : ℕ) (hq : 1 ≤ q) :
    GeneratesLpSeminorms μ (q : ℝ≥0∞)
      (fun i : (Fin d → ℕ) × (Fin d' → ℕ) ↦
        bruhatDiffSymbolWeightedApply b (bruhatDiffMonomial a i.1)
          (bruhatDiffMonomial a' i.2)) := by sorry

-- TODO(paper-gap): On p. 789 the proof uses convergence in the new seminorm
-- to identify its value at the limit before proving its continuity.

end ElementaryOperators

section IdeleClassSeminorms

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Paper: Proposition D.1.10.7, p. 789. Realize the space of k-invariant
Schwartz–Bruhat functions as a submodule with the inherited topology. -/
def schwartzBruhatInvariantSubmodule (k : Subgroup G) : Submodule ℂ (SchwartzBruhat G) :=
  let ev (x : G) : SchwartzBruhat G →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  ⨅ (g : G) (u : k), (ev (g * u.val) - ev g).ker

/-- Paper: Proposition D.1.10.7, p. 789. The fixed submodule consists exactly
of the functions invariant under translation by the subgroup.
Deviation: Sanity check on the fixed subspace used for S(k,G). -/
theorem mem_schwartzBruhatInvariantSubmodule_iff
    (k : Subgroup G) (f : SchwartzBruhat G) :
    f ∈ schwartzBruhatInvariantSubmodule k ↔
      ∀ (x : G) (u : k), f (x * u.val) = f x := by sorry

/-- Paper: (D.1.10.15), p. 789. Apply the compact-direction derivatives and the
derivatives along the norm section, then multiply by a weight in the absolute log norm.
Deviation: The radial derivatives use the exponential coordinate, so differentiation
with respect to its parameter is the operator t∂t. -/
def ideleClassWeightedDeriv {d : ℕ} (n : G →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G)
    (γ : Fin d → LCATopologicalLie n.ker) (m : ℕ) (α : Fin d → ℕ) (weight : ℝ → ℝ)
    (f : SchwartzBruhat G) (t : ℝ≥0ˣ) (x : G) : ℂ :=
  let j : n.ker →ₜ* G := ⟨n.ker.subtype, continuous_subtype_val⟩
  let D := bruhatDiffMonomial (fun i ↦ j.comp (γ i)) α
  let Df := D.val ⟨f, (mem_bruhatSmoothSubmodule_iff _).2 (schwartzBruhat_isBruhatSmooth f)⟩
  (weight |Real.log (t.val : ℝ)| : ℂ) *
    iteratedDeriv m (fun s : ℝ ↦
      Df.val (τ (Units.mk0 (Real.exp s).toNNReal
        (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos s)))) * x)) 0

/-- Paper: (D.1.10.15), p. 789. At zero differential orders the result is the
value of the original function multiplied by the weight in the absolute log norm.
Deviation: Sanity check on the derivatives and the argument of the weight. -/
theorem ideleClassWeightedDeriv_zero {d : ℕ} (n : G →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G)
    (γ : Fin d → LCATopologicalLie n.ker) (weight : ℝ → ℝ) (f : SchwartzBruhat G)
    (t : ℝ≥0ˣ) (x : G) :
    ideleClassWeightedDeriv n τ γ 0 0 weight f t x =
      (weight |Real.log (t.val : ℝ)| : ℂ) * f x := by sorry

universe u

variable (F : Type u) [Field F] [NumberField F]

local instance : T2Space C[F] := (ideleGroup_quotient.{u, 0} F).2.2.2.2.2.1
local instance : LocallyCompactSpace C[F] := (ideleGroup_quotient.{u, 0} F).2.2.2.2.2.2.1

local notation "C₀[" F "]" => Subgroup.connectedComponentOfOne C[F]
local notation "C₁[" F "]" => MonoidHom.ker (ideleClassNorm F)
local notation "d[" F "]" => (Module.finrank ℚ F - 1)

local instance : LocallyCompactSpace C₀[F] := isClosed_connectedComponent.locallyCompactSpace
local instance : LocallyCompactSpace C₁[F] :=
  (ideleClassGroup_finiteness F).1.locallyCompactSpace

/-- Paper: Proposition D.1.10.7, p. 789. On all sufficiently small compact
good-subgroup stages of the identity component, weighted sup norms of the radial
and norm-one directional derivatives generate the Schwartz–Bruhat topology.
Deviation: The section and directions take values directly in the identity
component, since their domains are connected. The supremum is over all
representatives of the quotient. -/
theorem ideleClassComponent_weightedSup_generates
    (τ : ℝ≥0ˣ →ₜ* C₀[F]) (hτ : RightInverse τ ((ideleClassNorm F).comp (C₀[F]).subtype)) :
    let n := (ideleClassNorm F).comp (C₀[F]).subtype
    ∃ k₀ : Subgroup C₀[F], IsCompact (k₀ : Set C₀[F]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup C₀[F], k ≤ k₀ → IsCompact (k : Set C₀[F]) → IsBruhatGoodSubgroup k →
        ∃ γ : Fin d[F] → LCATopologicalLie n.ker,
          GeneratesSeminormTopology
            (fun i : ℕ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
              ⨆ x : C₀[F], (‖ideleClassWeightedDeriv n τ γ i.2.1 i.2.2
                (fun t ↦ 1 + t ^ i.1) f.val (n x) x‖₊ : ℝ≥0∞)) := by sorry

/-- Paper: Remark D.1.10.8, p. 789. Every continuous one-parameter subgroup
of the norm-one idele classes has image in their identity component. -/
theorem normOneIdeleClass_direction_mem_connectedComponent
    (γ : LCATopologicalLie C₁[F]) (t : ℝ) :
    γ (Multiplicative.ofAdd t) ∈ Subgroup.connectedComponentOfOne C₁[F] := by sorry

-- TODO(paper-gap): In D.1.10.9 the subgroup Γ is unbound. The stage S(k,C_F) in
-- the title and conclusion uses the full group, which is compactly generated.
-- TODO(paper-gap): On p. 791 the proof claims generation on the entire LF-space.
-- Over ℚ, fixed radial bumps times indicators of shrinking open subgroups of
-- the norm-one group tend to zero in the listed Lᵖ norms but retain their value at 1.

/-- Paper: (D.1.10.17) and (D.1.10.20), pp. 790–791. Evaluate the weighted
directional derivative in the product chart of a norm section and its kernel. -/
def ideleClassProductWeightedDeriv {d : ℕ} (n : G →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G)
    (γ : Fin d → LCATopologicalLie n.ker) (m : ℕ) (α : Fin d → ℕ) (weight : ℝ → ℝ)
    (f : SchwartzBruhat G) (z : ℝ≥0ˣ × n.ker) : ℂ :=
  ideleClassWeightedDeriv n τ γ m α weight f z.1 (τ z.1 * z.2.val)

/-- Paper: (D.1.10.17) and (D.1.10.20), pp. 790–791. At zero differential orders
and unit weight evaluation is at the idele class represented by the product chart.
Deviation: Sanity check on the section and kernel factors. -/
theorem ideleClassProductWeightedDeriv_zero {d : ℕ} (n : G →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G)
    (γ : Fin d → LCATopologicalLie n.ker) (f : SchwartzBruhat G) (z : ℝ≥0ˣ × n.ker) :
    ideleClassProductWeightedDeriv n τ γ 0 0 (fun _ ↦ 1) f z = f (τ z.1 * z.2.val) := by sorry

section Global
local instance : MeasurableSpace C[F] := borel _

variable (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F))
variable (γ : Fin d[F] → LCATopologicalLie C₁[F])
variable
  (hγ : LinearIndependent ℝ (fun j ↦ bruhatFirstOrder (γ j)))
  (hspan : Submodule.span ℝ (range (fun j ↦ bruhatFirstOrder (γ j))) =
    bruhatDiffDegreeOneReal (G := C₁[F]))

include hτ hγ hspan

local notation "μ₁[" F "]" => positiveRealHaar.prod (normOneIdeleClassTamagawaMeasure F)

/-- Paper: Proposition D.1.10.9(1), p. 790. For sufficiently small compact
good subgroups, the weighted Lᵖ norms using one plus powers of the absolute
log norm generate the topology on the fixed subspace.
Deviation: The norm-one directions are specified by their real basis property
and the integration measure is the product in (D.1.10.17). -/
theorem ideleClass_weightedLp_generates :
    ∃ k₀ : Subgroup C[F], IsCompact (k₀ : Set C[F]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup C[F], k ≤ k₀ → IsCompact (k : Set C[F]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms μ₁[F] (ENNReal.ofReal p)
          (fun i : ℕ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (ideleClassNorm F) τ γ i.2.1 i.2.2
              (fun t ↦ 1 + t ^ i.1) f.val) := by sorry

/-- Paper: Proposition D.1.10.9(2), p. 790. Powers of the absolute log norm
alone give an Lᵖ seminorm family generating the same fixed-subspace topology.
Deviation: The norm-one directions are specified by their real basis property. -/
theorem ideleClass_logPowerLp_generates :
    ∃ k₀ : Subgroup C[F], IsCompact (k₀ : Set C[F]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup C[F], k ≤ k₀ → IsCompact (k : Set C[F]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms μ₁[F] (ENNReal.ofReal p)
          (fun i : ℕ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (ideleClassNorm F) τ γ i.2.1 i.2.2
              (fun t ↦ t ^ i.1) f.val) := by sorry

/-- Paper: Proposition D.1.10.9(3), p. 790. Absolute values of arbitrary complex
polynomials in the absolute log norm give a generating Lᵖ family on the fixed stage.
Deviation: The norm-one directions are specified by their real basis property. -/
theorem ideleClass_logPolynomialLp_generates :
    ∃ k₀ : Subgroup C[F], IsCompact (k₀ : Set C[F]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup C[F], k ≤ k₀ → IsCompact (k : Set C[F]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms μ₁[F] (ENNReal.ofReal p)
          (fun i : Polynomial ℂ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (ideleClassNorm F) τ γ i.2.1 i.2.2
              (fun t ↦ ‖i.1.eval (t : ℂ)‖) f.val) := by sorry

end Global

section SLocal

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Cₛ[" F ", " S "]" => SIdeleClassGroup F S
local notation "Cₛ₁[" F ", " S "]" => MonoidHom.ker (sIdeleClassNorm F S)

local instance : T2Space Cₛ[F, S] := (sIdeleClassNorm_descent F S).1
local instance : LocallyCompactSpace Cₛ[F, S] := (sIdeleClassNorm_descent F S).2.1
local instance : LocallyCompactSpace Cₛ₁[F, S] :=
  (sIdeleClassGroup_finiteness F S).1.locallyCompactSpace
local instance : MeasurableSpace Cₛ₁[F, S] := borel _

variable (τ : ℝ≥0ˣ →ₜ* Cₛ[F, S]) (hτ : RightInverse τ (sIdeleClassNorm F S))
variable (γ : Fin d[F] → LCATopologicalLie Cₛ₁[F, S])
variable
  (hγ : LinearIndependent ℝ (fun j ↦ bruhatFirstOrder (γ j)))
  (hspan : Submodule.span ℝ (range (fun j ↦ bruhatFirstOrder (γ j))) =
    bruhatDiffDegreeOneReal (G := Cₛ₁[F, S]))
variable (μ : Measure Cₛ₁[F, S]) [hμ : μ.IsHaarMeasure]

include hτ hγ hspan hμ

-- TODO(paper-gap): The normalization of the measure in (D.1.10.20) refers
-- to (A.3.4.1)(3), which omits the outside-S unit factors from the numerator.
-- The topology assertions below hold for any Haar measure on the full kernel.

/-- Paper: Proposition D.1.10.10(1), p. 791. For sufficiently small compact
good subgroups, the Lᵖ family with weights one plus powers of the absolute log
S-norm generates the fixed-subspace topology.
Deviation: The norm-one directions are specified by their real basis property
and the compact kernel carries any Haar measure. -/
theorem sIdeleClass_weightedLp_generates :
    ∃ k₀ : Subgroup Cₛ[F, S], IsCompact (k₀ : Set Cₛ[F, S]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup Cₛ[F, S], k ≤ k₀ → IsCompact (k : Set Cₛ[F, S]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms (positiveRealHaar.prod μ) (ENNReal.ofReal p)
          (fun i : ℕ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (sIdeleClassNorm F S) τ γ i.2.1 i.2.2
              (fun t ↦ 1 + t ^ i.1) f.val) := by sorry

/-- Paper: Proposition D.1.10.10(2), p. 791. Powers of the absolute log S-norm
give a generating family on the fixed subspace.
Deviation: The directions satisfy the real basis property and the compact
kernel carries any Haar measure. -/
theorem sIdeleClass_logPowerLp_generates :
    ∃ k₀ : Subgroup Cₛ[F, S], IsCompact (k₀ : Set Cₛ[F, S]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup Cₛ[F, S], k ≤ k₀ → IsCompact (k : Set Cₛ[F, S]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms (positiveRealHaar.prod μ) (ENNReal.ofReal p)
          (fun i : ℕ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (sIdeleClassNorm F S) τ γ i.2.1 i.2.2
              (fun t ↦ t ^ i.1) f.val) := by sorry

/-- Paper: Proposition D.1.10.10(3), p. 792. Absolute values of polynomials in
the absolute log S-norm give a generating family on the fixed subspace.
Deviation: The coefficients are complex as in D.1.10.9(3). The directions
satisfy the real basis property and the compact kernel carries any Haar measure. -/
theorem sIdeleClass_logPolynomialLp_generates :
    ∃ k₀ : Subgroup Cₛ[F, S], IsCompact (k₀ : Set Cₛ[F, S]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup Cₛ[F, S], k ≤ k₀ → IsCompact (k : Set Cₛ[F, S]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms (positiveRealHaar.prod μ) (ENNReal.ofReal p)
          (fun i : Polynomial ℂ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (sIdeleClassNorm F S) τ γ i.2.1 i.2.2
              (fun t ↦ ‖i.1.eval (t : ℂ)‖) f.val) := by sorry

-- TODO(paper-gap): The equality after D.1.10.10(3) also requires compatible
-- section and Haar choices. Even for identical classes, Haar rescaling changes
-- the seminorms.

end SLocal

end IdeleClassSeminorms

end RiemannMasullo
