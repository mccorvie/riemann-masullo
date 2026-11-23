module

public import RiemannMasullo.AppA_AlgebraicNT.Sec2
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Separation.GDelta

/-! # §8.2. Stack-theoretic periodic orbits and fixed points

The parameter `S` records the finite part of the paper's set of places. Every
infinite place is already included in `SAdeleRing`.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function IsDedekindDomain NumberField TopologicalSpace Topology
open scoped NNReal NumberField.AdeleRing

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Aₛ" => SAdeleRing F S
local notation "𝕀ₛ" => (SAdeleRing F S)ˣ
local notation "Nₛ" => MonoidHom.ker (sIdeleNorm F S)
local notation "N₁" => MonoidHom.ker (ideleNorm F)

/-- Paper: Definition 8.2.0.1(1), p. 384. The base point $e_v$ has zero at $v$
and one elsewhere. The index `none` denotes the ordinary base point 1. -/
def adeleOrbitBasepoint : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)) → 𝔸[F]
  | none => 1
  | some (.inl v) => AdeleRing.ofCompletion (𝓞 F) F v 0
  | some (.inr v) => AdeleRing.ofAdicCompletion (𝓞 F) F v 0

/-- Paper: Definition 8.2.0.1(1), p. 384. Coordinate formulas for the global base points. -/
theorem adeleOrbitBasepoint_coordinates :
    adeleOrbitBasepoint F none = 1 ∧
      (∀ v : InfinitePlace F,
        (adeleOrbitBasepoint F (some (.inl v))).1 v = 0 ∧
        (∀ w : InfinitePlace F, w ≠ v → (adeleOrbitBasepoint F (some (.inl v))).1 w = 1) ∧
        (adeleOrbitBasepoint F (some (.inl v))).2 = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        (adeleOrbitBasepoint F (some (.inr v))).1 = 1 ∧
        (adeleOrbitBasepoint F (some (.inr v))).2 v = 0 ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
          (adeleOrbitBasepoint F (some (.inr v))).2 w = 1) := by
  sorry

/-- Paper: Definition 8.2.0.1(1), p. 384. The S-local base points keep all infinite
places and the finite places in S. -/
def sAdeleOrbitBasepoint (i : Option (InfinitePlace F ⊕ S)) : Aₛ :=
  adeleProjection F S (adeleOrbitBasepoint F (i.map (Sum.map id Subtype.val)))

/-- Paper: Definition 8.2.0.1(1), p. 384. The base point at a selected finite place
has zero at that place, including after projection to the S-adeles. -/
theorem sAdeleOrbitBasepoint_finite (v : S) :
    (sAdeleOrbitBasepoint F S (some (.inr v))).2 v = 0 := by
  sorry

/-- Paper: Definition 8.2.0.1(1), p. 384. The set $Z_{F,S}$ in (8.2.0.1)
consists of 1 and the single-zero base points, with the adelic subspace topology. -/
def sAdeleOrbitBasepoints : Set Aₛ :=
  Set.range (sAdeleOrbitBasepoint F S)

/-- Paper: Definition 8.2.0.1(1), p. 384. The ordinary base point lies in $Z_{F,S}$. -/
theorem one_mem_sAdeleOrbitBasepoints : 1 ∈ sAdeleOrbitBasepoints F S := by
  sorry

/-- Paper: Definition 8.2.0.1(1), p. 384. The set $Z_F$ in (8.2.0.2)
consists of 1 and the single-zero base points, with the adelic subspace topology. -/
def adeleOrbitBasepoints : Set 𝔸[F] :=
  Set.range (adeleOrbitBasepoint F)

/-- Paper: Definition 8.2.0.1(1), p. 384. The ordinary base point lies in $Z_F$. -/
theorem one_mem_adeleOrbitBasepoints : 1 ∈ adeleOrbitBasepoints F := by
  sorry

/-- Paper: Definition 8.2.0.1(2), p. 384. The family in (8.2.0.3) consists of the
S-local full-idele orbits with their adelic subspace topologies. -/
def sAdeleFullOrbit (i : Option (InfinitePlace F ⊕ S)) : Set Aₛ :=
  MulAction.orbit 𝕀ₛ (sAdeleOrbitBasepoint F S i)

/-- Paper: Definition 8.2.0.1(2), p. 384. The ordinary S-local orbit consists of
the $S$-adeles that are units. -/
theorem mem_sAdeleFullOrbit_none_iff (x : Aₛ) :
    x ∈ sAdeleFullOrbit F S none ↔ IsUnit x := by
  sorry

/-- Paper: Definition 8.2.0.1(2), p. 384. The family in (8.2.0.4) consists of the
global full-idele orbits with their adelic subspace topologies. -/
def adeleFullOrbit (i : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F))) : Set 𝔸[F] :=
  MulAction.orbit 𝔸[F]ˣ (adeleOrbitBasepoint F i)

/-- Paper: Definition 8.2.0.1(2), p. 384. The ordinary global orbit consists of
the adeles that are units. -/
theorem mem_adeleFullOrbit_none_iff (x : 𝔸[F]) :
    x ∈ adeleFullOrbit F none ↔ IsUnit x := by
  sorry

/-- Paper: Definition 8.2.0.1(3), p. 385. The S-local set $D_{F,S}$ in (8.2.0.5)
is the union of the full-idele orbits with the adelic subspace topology. -/
def sAdeleFullOrbitUnion : Set Aₛ :=
  ⋃ i, sAdeleFullOrbit F S i

/-- Paper: Definition 8.2.0.1(3), p. 385. The S-local full-orbit union is the
set of translates of the special S-adeles by full ideles. -/
theorem mem_sAdeleFullOrbitUnion_iff (x : Aₛ) :
    x ∈ sAdeleFullOrbitUnion F S ↔
      ∃ (g : 𝕀ₛ) (z : sAdeleOrbitBasepoints F S), g • z.val = x := by
  sorry

/-- Paper: Definition 8.2.0.1(3), p. 385. The global set $D_F$ in (8.2.0.5)
is the union of the full-idele orbits with the adelic subspace topology. -/
def adeleFullOrbitUnion : Set 𝔸[F] :=
  ⋃ i, adeleFullOrbit F i

/-- Paper: Definition 8.2.0.1(3), p. 385. The global full-orbit union is the
set of translates of the special adeles by full ideles. -/
theorem mem_adeleFullOrbitUnion_iff (x : 𝔸[F]) :
    x ∈ adeleFullOrbitUnion F ↔
      ∃ (g : 𝔸[F]ˣ) (z : adeleOrbitBasepoints F), g • z.val = x := by
  sorry

-- Read the full-group stability sentence on p. 385 with (8.2.0.3)–(8.2.0.5).
-- The norm-one orbits in (8.2.0.6)–(8.2.0.8) are stable under the norm kernel.

/-- Paper: Definition 8.2.0.2(1), p. 385. The family in (8.2.0.6) consists of the
S-local norm-one orbits with their adelic subspace topologies. -/
def sAdeleNormOneOrbit (i : Option (InfinitePlace F ⊕ S)) : Set Aₛ :=
  MulAction.orbit Nₛ (sAdeleOrbitBasepoint F S i)

/-- Paper: Definition 8.2.0.2(1), p. 385. The ordinary S-local norm-one orbit
is the image of the norm kernel in the S-adeles. -/
theorem mem_sAdeleNormOneOrbit_none_iff (x : Aₛ) :
    x ∈ sAdeleNormOneOrbit F S none ↔
      ∃ g : 𝕀ₛ, sIdeleNorm F S g = 1 ∧ g.val = x := by
  sorry

/-- Paper: Definition 8.2.0.2(1), p. 385. The family in (8.2.0.7) consists of the
global norm-one orbits with their adelic subspace topologies. -/
def adeleNormOneOrbit (i : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F))) :
    Set 𝔸[F] :=
  MulAction.orbit N₁ (adeleOrbitBasepoint F i)

/-- Paper: Definition 8.2.0.2(1), p. 385. The ordinary global norm-one orbit is the
image of the norm kernel in the adeles. -/
theorem mem_adeleNormOneOrbit_none_iff (x : 𝔸[F]) :
    x ∈ adeleNormOneOrbit F none ↔ ∃ g : 𝔸[F]ˣ, ideleNorm F g = 1 ∧ g.val = x := by
  sorry

/-- Paper: Definition 8.2.0.2(2), p. 385. The S-local set $D^1_{F,S}$ in (8.2.0.8)
is the union of the norm-one orbits with the adelic subspace topology. -/
def sAdeleNormOneOrbitUnion : Set Aₛ :=
  ⋃ i, sAdeleNormOneOrbit F S i

/-- Paper: Definition 8.2.0.2(2), p. 385. An S-adele lies in the union exactly when
it is a norm-one translate of a special S-adele. -/
theorem mem_sAdeleNormOneOrbitUnion_iff (x : Aₛ) :
    x ∈ sAdeleNormOneOrbitUnion F S ↔
      ∃ (g : Nₛ) (z : sAdeleOrbitBasepoints F S), g • z.val = x := by
  sorry

/-- Paper: Definition 8.2.0.2(2), p. 385. The global set $D^1_F$ in (8.2.0.8)
is the union of the norm-one orbits with the adelic subspace topology. -/
def adeleNormOneOrbitUnion : Set 𝔸[F] :=
  ⋃ i, adeleNormOneOrbit F i

/-- Paper: Definition 8.2.0.2(2), p. 385. An adele lies in the union exactly when
it is a norm-one translate of a special adele. -/
theorem mem_adeleNormOneOrbitUnion_iff (x : 𝔸[F]) :
    x ∈ adeleNormOneOrbitUnion F ↔
      ∃ (g : N₁) (z : adeleOrbitBasepoints F), g • z.val = x := by
  sorry

/-- Paper: Lemma 8.2.0.3(1), p. 385. The S-local orbit map applies the norm-one
idele to the given special S-adele. -/
def sAdeleNormOneOrbitMap (gz : Nₛ × sAdeleOrbitBasepoints F S) :
    sAdeleNormOneOrbitUnion F S :=
  ⟨gz.1 • gz.2.val, (mem_sAdeleNormOneOrbitUnion_iff F S _).mpr ⟨gz.1, gz.2, rfl⟩⟩

/-- Paper: Lemma 8.2.0.3(1), p. 385. The underlying S-adele of the orbit map
is given by the norm-one action. -/
theorem sAdeleNormOneOrbitMap_val (g : Nₛ) (z : sAdeleOrbitBasepoints F S) :
    (sAdeleNormOneOrbitMap F S (g, z)).val = g • z.val := by
  sorry

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global orbit map applies the norm-one
idele to the given special adele. -/
def adeleNormOneOrbitMap (gz : N₁ × adeleOrbitBasepoints F) : adeleNormOneOrbitUnion F :=
  ⟨gz.1 • gz.2.val, (mem_adeleNormOneOrbitUnion_iff F _).mpr ⟨gz.1, gz.2, rfl⟩⟩

/-- Paper: Lemma 8.2.0.3(2), p. 385. The underlying adele of the orbit map is
given by the norm-one action. -/
theorem adeleNormOneOrbitMap_val (g : N₁) (z : adeleOrbitBasepoints F) :
    (adeleNormOneOrbitMap F (g, z)).val = g • z.val := by
  sorry

/-- Paper: Lemma 8.2.0.3(1), p. 385. The adelic subspace topology on the S-local
norm-one orbit union is the quotient topology of the S-local orbit map. -/
theorem sAdeleNormOneOrbitMap_isQuotientMap : IsQuotientMap (sAdeleNormOneOrbitMap F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global orbit map is continuous for the
adelic subspace topology on the target.
Deviation: The adelic subspace topology is coarser than the quotient topology.
The equality of topologies fails by ERRATA R12. -/
theorem adeleNormOneOrbitMap_continuous : Continuous (adeleNormOneOrbitMap F) := by
  sorry

/-- Paper: Lemma 8.2.0.3(2), p. 385. Every point in the global norm-one orbit union
has a preimage under the orbit map. -/
theorem adeleNormOneOrbitMap_surjective : Surjective (adeleNormOneOrbitMap F) := by
  sorry

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global orbit map is an open quotient map
for its coinduced topology.
Deviation: The target carries the quotient topology of the global orbit map.
ERRATA R12 distinguishes this topology from the adelic subspace topology. -/
theorem adeleNormOneOrbitMap_isOpenQuotientMap :
    @IsOpenQuotientMap _ _ inferInstance
      (TopologicalSpace.coinduced (adeleNormOneOrbitMap F) inferInstance)
      (adeleNormOneOrbitMap F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is Hausdorff. -/
theorem sAdeleNormOneOrbitUnion_t2Space : T2Space (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is Hausdorff. -/
theorem adeleNormOneOrbitUnion_t2Space : T2Space (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is metrizable. -/
theorem sAdeleNormOneOrbitUnion_metrizableSpace :
    MetrizableSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is metrizable. -/
theorem adeleNormOneOrbitUnion_metrizableSpace : MetrizableSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is second-countable. -/
theorem sAdeleNormOneOrbitUnion_secondCountable :
    SecondCountableTopology (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is second-countable. -/
theorem adeleNormOneOrbitUnion_secondCountable :
    SecondCountableTopology (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is perfectly normal. -/
theorem sAdeleNormOneOrbitUnion_perfectlyNormal :
    PerfectlyNormalSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is perfectly normal. -/
theorem adeleNormOneOrbitUnion_perfectlyNormal :
    PerfectlyNormalSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is separable. -/
theorem sAdeleNormOneOrbitUnion_separableSpace : SeparableSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is separable. -/
theorem adeleNormOneOrbitUnion_separableSpace : SeparableSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is locally compact. -/
theorem sAdeleNormOneOrbitUnion_locallyCompactSpace :
    LocallyCompactSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is locally compact
in the quotient topology of the orbit map.
Deviation: The adelic subspace topology fails to be locally compact by ERRATA R13. -/
theorem adeleNormOneOrbitUnion_locallyCompactSpace :
    @LocallyCompactSpace (adeleNormOneOrbitUnion F)
      (TopologicalSpace.coinduced (adeleNormOneOrbitMap F) inferInstance) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is σ-compact. -/
theorem sAdeleNormOneOrbitUnion_sigmaCompactSpace :
    SigmaCompactSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is σ-compact
in the adelic subspace topology. -/
theorem adeleNormOneOrbitUnion_sigmaCompactSpace :
    SigmaCompactSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is paracompact. -/
theorem sAdeleNormOneOrbitUnion_paracompactSpace :
    ParacompactSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is paracompact. -/
theorem adeleNormOneOrbitUnion_paracompactSpace : ParacompactSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Proposition 8.2.0.4, p. 386. The subgroup of global ideles obtained by
inserting the units of the local valuation ring at the specified finite place. -/
def embeddedFiniteLocalUnits (v : HeightOneSpectrum (𝓞 F)) : Subgroup 𝔸[F]ˣ :=
  ((IdeleGroup.ofAdicCompletion (𝓞 F) F v).comp
    (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom)).range

/-- Paper: Proposition 8.2.0.4, p. 386. The inserted local units have norm one at
the specified place and value one at all other places. -/
theorem mem_embeddedFiniteLocalUnits_iff (v : HeightOneSpectrum (𝓞 F)) (g : 𝔸[F]ˣ) :
    g ∈ embeddedFiniteLocalUnits F v ↔
      g.val.1 = 1 ∧ ‖g.val.2 v‖ = 1 ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → g.val.2 w = 1 := by
  sorry

/-- Paper: Equation (8.2.0.9), p. 386. The S-local section at a finite place takes
parameters in the half-open interval from 1 to the absolute prime ideal norm. -/
def sAdeleFiniteOrbitSection (v : S) (τ : ℝ≥0ˣ →* 𝕀ₛ) : Set Aₛ :=
  (fun t : ℝ≥0ˣ ↦ τ t • sAdeleOrbitBasepoint F S (some (.inr v))) ''
    {t | t.val ∈ Set.Ico 1 (v.val.asIdeal.absNorm : ℝ≥0)}

/-- Paper: Equation (8.2.0.9), p. 386. The included left endpoint gives the S-local
single-zero base point. -/
theorem sAdeleOrbitBasepoint_mem_finiteOrbitSection (v : S) (τ : ℝ≥0ˣ →* 𝕀ₛ) :
    sAdeleOrbitBasepoint F S (some (.inr v)) ∈ sAdeleFiniteOrbitSection F S v τ := by
  sorry

/-- Paper: Equation (8.2.0.10), p. 386. The global section at a finite place takes
parameters in the half-open interval from 1 to the absolute prime ideal norm. -/
def adeleFiniteOrbitSection (v : HeightOneSpectrum (𝓞 F)) (τ : ℝ≥0ˣ →* 𝔸[F]ˣ) :
    Set 𝔸[F] :=
  (fun t : ℝ≥0ˣ ↦ τ t • adeleOrbitBasepoint F (some (.inr v))) ''
    {t | t.val ∈ Set.Ico 1 (v.asIdeal.absNorm : ℝ≥0)}

/-- Paper: Equation (8.2.0.10), p. 386. The included left endpoint gives the global
single-zero base point. -/
theorem adeleOrbitBasepoint_mem_finiteOrbitSection (v : HeightOneSpectrum (𝓞 F))
    (τ : ℝ≥0ˣ →* 𝔸[F]ˣ) :
    adeleOrbitBasepoint F (some (.inr v)) ∈ adeleFiniteOrbitSection F v τ := by
  sorry

/-- Paper: Proposition 8.2.0.4(1), p. 386. Every point in the full S-local finite-place
orbit can be moved into the half-open section by a norm-one idele. The transporter
is unique up to the embedded local units.
Deviation: The transporter lies in the norm-one subgroup, correcting ERRATA R1. -/
theorem sAdeleFiniteOrbit_transporter (v : S) (τ : ℝ≥0ˣ →* 𝕀ₛ) (hτ : Continuous τ)
    (hsection : RightInverse τ (sIdeleNorm F S)) (x : Aₛ)
    (hx : x ∈ sAdeleFullOrbit F S (some (.inr v))) :
    ∃ g : Nₛ, g⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ ∧
      ∀ h : Nₛ, h⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ →
        g.val⁻¹ * h.val ∈ (embeddedFiniteLocalUnits F v.val).map
          (Units.map (adeleProjection F S).toMonoidHom) := by
  sorry

/-- Paper: Proposition 8.2.0.4(2), p. 386. Every point in the full global finite-place
orbit can be moved into the half-open section by a norm-one idele. The transporter
is unique up to the embedded local units.
Deviation: The transporter lies in the norm-one subgroup, correcting ERRATA R1. -/
theorem adeleFiniteOrbit_transporter (v : HeightOneSpectrum (𝓞 F)) (τ : ℝ≥0ˣ →* 𝔸[F]ˣ)
    (hτ : Continuous τ) (hsection : RightInverse τ (ideleNorm F)) (x : 𝔸[F])
    (hx : x ∈ adeleFullOrbit F (some (.inr v))) :
    ∃ g : N₁, g⁻¹ • x ∈ adeleFiniteOrbitSection F v τ ∧
      ∀ h : N₁, h⁻¹ • x ∈ adeleFiniteOrbitSection F v τ →
        g.val⁻¹ * h.val ∈ embeddedFiniteLocalUnits F v := by
  sorry

/-- Paper: Proposition 8.2.0.5, p. 386. At an infinite place the full S-local orbit is
already the norm-one orbit of the distinguished base point. -/
theorem sAdeleNormOneOrbit_infinite_eq_full (v : InfinitePlace F) :
    sAdeleNormOneOrbit F S (some (.inl v)) = sAdeleFullOrbit F S (some (.inl v)) := by
  sorry

/-- Paper: Proposition 8.2.0.5, p. 386. At an infinite place the full global orbit is
already the norm-one orbit of the distinguished base point. -/
theorem adeleNormOneOrbit_infinite_eq_full (v : InfinitePlace F) :
    adeleNormOneOrbit F (some (.inl v)) = adeleFullOrbit F (some (.inl v)) := by
  sorry

/-- Paper: Proposition 8.2.0.5(1), p. 386. At a real place the norm-one
stabilizer of every point of the S-local orbit is the image of the two local signs. -/
theorem sAdeleFullOrbit_real_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsReal)
    (x : Aₛ) (hx : x ∈ sAdeleFullOrbit F S (some (.inl v))) (g : 𝕀ₛ) :
    (sIdeleNorm F S g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, (u.val = 1 ∨ u.val = -1) ∧
        g = Units.map (adeleProjection F S).toMonoidHom (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  sorry

/-- Paper: Proposition 8.2.0.5(1), p. 386. At a real place the norm-one
stabilizer of every point of the global orbit is the image of the two local signs. -/
theorem adeleFullOrbit_real_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsReal)
    (x : 𝔸[F]) (hx : x ∈ adeleFullOrbit F (some (.inl v))) (g : 𝔸[F]ˣ) :
    (ideleNorm F g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, (u.val = 1 ∨ u.val = -1) ∧
        g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  sorry

/-- Paper: Proposition 8.2.0.5(2), p. 387. At a complex place the norm-one
stabilizer of every point of the S-local orbit is the image of the local unit circle. -/
theorem sAdeleFullOrbit_complex_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsComplex)
    (x : Aₛ) (hx : x ∈ sAdeleFullOrbit F S (some (.inl v))) (g : 𝕀ₛ) :
    (sIdeleNorm F S g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧
        g = Units.map (adeleProjection F S).toMonoidHom (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  sorry

/-- Paper: Proposition 8.2.0.5(2), p. 387. At a complex place the norm-one
stabilizer of every point of the global orbit is the image of the local unit circle. -/
theorem adeleFullOrbit_complex_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsComplex)
    (x : 𝔸[F]) (hx : x ∈ adeleFullOrbit F (some (.inl v))) (g : 𝔸[F]ˣ) :
    (ideleNorm F g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧
        g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  sorry

/-- Paper: Proposition 8.2.0.6(1), p. 387. The closure of the positive section ray
relative to the S-local full-orbit union adds the single-zero base point. -/
theorem sAdeleFullOrbitUnion_closure_sectionRay (v : InfinitePlace F) :
    let ray : Set Aₛ := Set.range fun t : ℝ≥0ˣ ↦
      adeleProjection F S (singlePlaceIdeleNormSection F v t).val
    closure ray ∩ sAdeleFullOrbitUnion F S =
      ray ∪ {sAdeleOrbitBasepoint F S (some (.inl v))} := by
  sorry

/-- Paper: Proposition 8.2.0.6(2), p. 387. The closure of the positive section ray
relative to the global full-orbit union adds the single-zero base point. -/
theorem adeleFullOrbitUnion_closure_sectionRay (v : InfinitePlace F) :
    let ray : Set 𝔸[F] := Set.range fun t : ℝ≥0ˣ ↦ (singlePlaceIdeleNormSection F v t).val
    closure ray ∩ adeleFullOrbitUnion F = ray ∪ {adeleOrbitBasepoint F (some (.inl v))} := by
  sorry

end RiemannMasullo
