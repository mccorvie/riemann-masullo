module

public import RiemannMasullo.AppA_AlgebraicNT.Sec1
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.NumberTheory.NumberField.HeckeLFunction
public import Mathlib.Topology.Algebra.PontryaginDual

/-!
# Riemann surfaces of continuous quasi-characters

Section 3.1 of Masullo. We use the compact-open topology on continuous monoid homomorphisms.
On a group, such a map into ℂ takes values in ℂˣ. This convention makes the global space
definitionally Mathlib's space of Hecke characters. The complex coordinates below use the
normalized module, including its exponent two at a complex place.
-/

@[expose] public section

noncomputable section

namespace RiemannMasullo

open Function NumberField IsDedekindDomain Topology
open scoped NNReal Manifold ContDiff

/-- Paper: §3.1.1, p. 118. The space of quasi-characters has the compact-open topology.
Deviation: We use complex-valued continuous homomorphisms on a group, whose values are units. -/
abbrev QuasiCharacter (G : Type*) [Group G] [TopologicalSpace G] := G →ₜ* ℂ

section Generalities

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)

local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

/-- Paper: Equation (3.1.1.1), p. 119. Restricting a quasi-character to the kernel of the
module gives the projection indexing the components. We view its values as complex numbers. -/
def normOneRestriction : C(QuasiCharacter G, QuasiCharacter m.ker) :=
  let i : m.ker →ₜ* G := ⟨m.ker.subtype, continuous_subtype_val⟩
  ⟨fun c => c.comp i, i.continuous_comp_left⟩

/-- Paper: Equation (3.1.1.1), p. 119. Two quasi-characters are in the same connected
component exactly when their restrictions to the norm-one subgroup agree. -/
theorem mem_connectedComponent_iff_normOneRestriction [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1)
    (c d : QuasiCharacter G) :
    d ∈ connectedComponent c ↔ normOneRestriction m d = normOneRestriction m c := by
  sorry

/-- Paper: Equation (3.1.1.1), p. 119. The restrictions to the norm-one subgroup are
exactly its unitary characters. In particular every such character lifts. -/
theorem range_normOneRestriction [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) :
    Set.range (normOneRestriction m) = Set.range (fun χ : PontryaginDual m.ker =>
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) := by
  sorry

/-- Paper: §3.1.1, p. 119. Near each quasi-character the complex exponent is a coordinate
centered at zero. Its inverse sends z to the character twisted by the z-th power of the module. -/
def HasNormTwistCharts : Prop :=
  ∀ c : QuasiCharacter G, ∃ e : OpenPartialHomeomorph (QuasiCharacter G) ℂ,
    c ∈ e.source ∧ e c = 0 ∧
      ∀ z ∈ e.target, ∀ g, e.symm z g = c g * (modℝ g : ℂ) ^ z

/-- Paper: §3.1.1, p. 119. Every modulated group admits local norm-twist coordinates,
including when the complex exponent is defined globally only modulo a period. -/
theorem hasNormTwistCharts_of_proper [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) : HasNormTwistCharts m := by
  sorry

/-- Paper: §3.1.1, p. 119. Choose one norm-twist chart around each point. These charts form
an atlas on the existing compact-open space. -/
@[instance_reducible] def quasiCharacterChartedSpace (h : HasNormTwistCharts m) :
    ChartedSpace ℂ (QuasiCharacter G) where
  atlas := Set.range fun c => (h c).choose
  chartAt c := (h c).choose
  mem_chart_source c := (h c).choose_spec.1
  chart_mem_atlas c := ⟨c, rfl⟩

/-- Paper: §3.1.1, p. 119. The atlas of complex norm-twist coordinates is analytic. -/
theorem quasiCharacter_isManifold (h : HasNormTwistCharts m) :
    letI := quasiCharacterChartedSpace m h
    IsManifold 𝓘(ℂ) ω (QuasiCharacter G) := by
  sorry

/-- Paper: Definition 3.1.1.1, p. 119. The abscissa is the real exponent in the modulus of
a quasi-character. We evaluate the ratio of logarithms at a point where the module differs from one.
Deviation: This formula computes (3.1.1.2) without choosing a unitary base-point. -/
def quasiCharacterAbscissa (_hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (c : QuasiCharacter G) : ℝ :=
  Real.log ‖c hne.choose‖ / Real.log (modℝ hne.choose)

/-- Paper: Equation (3.1.1.2), p. 119. Twisting any unitary character by the s-th power
of the module gives a quasi-character of abscissa Re(s). -/
theorem quasiCharacterAbscissa_of_unitary_twist (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1)
    (c : QuasiCharacter G) (χ : PontryaginDual G) (s : ℂ)
    (hc : ∀ g, c g = (χ g : ℂ) * (modℝ g : ℂ) ^ s) :
    quasiCharacterAbscissa m hm hne c = s.re := by
  sorry

/-- Paper: Equation (3.1.1.2), p. 119. At every element of a modulated group, the modulus
of a quasi-character equals the module raised to its abscissa. -/
theorem norm_quasiCharacter_eq_rpow_abscissa [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1)
    (c : QuasiCharacter G) (g : G) :
    ‖c g‖ = (modℝ g) ^ quasiCharacterAbscissa m hm hne c := by
  sorry

/-- Paper: Equation (3.1.1.2), p. 119. The abscissa is continuous in the compact-open topology. -/
theorem continuous_quasiCharacterAbscissa (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) :
    Continuous (quasiCharacterAbscissa m hm hne) := by
  have hev : Continuous (fun c : QuasiCharacter G => c hne.choose) := continuous_eval_const _
  have hneval (c : QuasiCharacter G) : c hne.choose ≠ 0 :=
    ((Group.isUnit hne.choose).map c).ne_zero
  exact (hev.norm.log fun c => norm_ne_zero_iff.mpr (hneval c)).div_const _

/-- Paper: Equation (3.1.1.2), p. 119. Every real number occurs as an abscissa. -/
theorem surjective_quasiCharacterAbscissa (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) :
    Surjective (quasiCharacterAbscissa m hm hne) := by
  sorry

/-- Paper: Definition 3.1.1.2(1), p. 119. The relative vertical strip over an interval is
the inverse image under the abscissa, with the topology inherited on its subtype.
Deviation: The same inverse image is defined for every real set. -/
def relativeVerticalStrip (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (I : Set ℝ) :
    Set (QuasiCharacter G) :=
  quasiCharacterAbscissa m hm hne ⁻¹' I

/-- Paper: Definition 3.1.1.2(2), p. 119. The relative right half-plane has abscissa
strictly larger than its boundary. -/
def relativeRightHalfPlane (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (a : ℝ) :
    TopologicalSpace.Opens (QuasiCharacter G) :=
  ⟨relativeVerticalStrip m hm hne (Set.Ioi a),
    isOpen_Ioi.preimage (continuous_quasiCharacterAbscissa m hm hne)⟩

/-- Paper: Definition 3.1.1.2(3), p. 119. The strip in the component indexed by ω also
requires the restriction of the quasi-character to the norm-one subgroup to equal ω. -/
def componentVerticalStrip (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1)
    (χ : PontryaginDual m.ker) (I : Set ℝ) : Set (QuasiCharacter G) :=
  relativeVerticalStrip m hm hne I ∩ {c | ∀ g : m.ker, normOneRestriction m c g = (χ g : ℂ)}

/-- Paper: Definition 3.1.1.2(2), p. 119. The trivial character lies in the relative
right half-plane precisely when its boundary is strictly negative. -/
theorem one_mem_relativeRightHalfPlane (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (a : ℝ) :
    1 ∈ relativeRightHalfPlane m hm hne a ↔ a < 0 := by
  change a < quasiCharacterAbscissa m hm hne 1 ↔ a < 0
  simp [quasiCharacterAbscissa]

/-- Paper: Definition 3.1.1.2, p. 119. The trivial character belongs to the strip in
the trivial component exactly when the interval contains zero. -/
theorem one_mem_componentVerticalStrip (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (I : Set ℝ) :
    1 ∈ componentVerticalStrip m hm hne 1 I ↔ 0 ∈ I := by
  simp [componentVerticalStrip, relativeVerticalStrip, quasiCharacterAbscissa, normOneRestriction]

/-- Paper: Equation (3.1.1.4), p. 119. The dual quasi-character is the module times
the inverse character, evaluated by composing the original character with inversion. -/
def dualQuasiCharacter [IsTopologicalGroup G] (hm : Continuous m) (c : QuasiCharacter G) :
    QuasiCharacter G :=
  let n : QuasiCharacter G :=
    ⟨Complex.ofRealHom.toMonoidHom.comp (NNReal.toRealHom.toMonoidHom.comp
      ((Units.coeHom ℝ≥0).comp m)),
      Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (Units.continuous_val.comp hm))⟩
  n * c.comp (ContinuousMonoidHom.inv G)

/-- Paper: Equation (3.1.1.4), p. 119. Duality reflects the abscissa in the line σ = 1/2. -/
theorem quasiCharacterAbscissa_dual [IsTopologicalGroup G] (hm : IsProperMap m)
    (hne : ∃ g, m g ≠ 1) (c : QuasiCharacter G) :
    quasiCharacterAbscissa m hm hne (dualQuasiCharacter m hm.continuous c) =
      1 - quasiCharacterAbscissa m hm hne c := by
  let g := hne.choose
  have hmod : 0 < modℝ g := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m g).ne_zero)
  have hmod_one : modℝ g ≠ 1 := fun h =>
    hne.choose_spec (Units.val_inj.mp (NNReal.coe_inj.mp h))
  have hlog := Real.log_ne_zero_of_pos_of_ne_one hmod hmod_one
  have hnorm : ‖c g‖ ≠ 0 := norm_ne_zero_iff.mpr ((Group.isUnit g).map c).ne_zero
  change Real.log ‖(modℝ g : ℂ) * c (g⁻¹)‖ / Real.log (modℝ g) =
    1 - Real.log ‖c g‖ / Real.log (modℝ g)
  rw [map_inv, ← div_eq_mul_inv, norm_div, Complex.norm_of_nonneg hmod.le,
    Real.log_div hmod.ne' hnorm, sub_div, div_self hlog]

/-- Paper: Equation (3.1.1.4), p. 119. The duality map is an analytic automorphism and
serves as its own inverse. -/
theorem dualQuasiCharacter_analyticEquiv [IsTopologicalGroup G] (hm : Continuous m)
    (h : HasNormTwistCharts m) :
    letI := quasiCharacterChartedSpace m h
    ∃ e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (QuasiCharacter G) (QuasiCharacter G) ω,
      (∀ c, e c = dualQuasiCharacter m hm c) ∧ ∀ c, e.symm c = dualQuasiCharacter m hm c := by
  sorry

end Generalities

section Ideles

variable (F : Type*) [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)

variable (S : Finset (Primes(F)))

local notation "projectedDiagonal" =>
  Subgroup.map (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection F S)
    (Subring.subtype (integralAdelesOutside F S)))))
    (MonoidHom.range (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S))))

/-- Paper: Equation (3.1.2.1), p. 120. The group J_{F,S} is the quotient of the S-ideles
by the projected diagonal S-units. As in §A.1, S specifies the finite places only. -/
abbrev SIdeleQuotient := (SAdeleRing F S)ˣ ⧸ projectedDiagonal

/-- Paper: Equation (3.1.2.1), p. 120. An S-idele represents the identity of J_{F,S}
precisely when it is the projection of a diagonal S-unit. -/
theorem sIdeleQuotient_mk_eq_one (g : (SAdeleRing F S)ˣ) :
    (QuotientGroup.mk g : SIdeleQuotient F S) = 1 ↔
      ∃ u : ((S : Set (Primes(F))).integer F)ˣ, g = Units.map
        ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom
        (Units.map (integralAdeleDiagonal F S).toMonoidHom u) := by
  rw [QuotientGroup.eq_one_iff, MonoidHom.map_range, MonoidHom.mem_range]
  exact exists_congr fun _ ↦ eq_comm

/-- Paper: Equation (3.1.2.1), p. 120. The product of normalized absolute values in S
descends to J_{F,S} by the S-unit product formula. -/
def sIdeleQuotientNorm : SIdeleQuotient F S →* ℝ≥0ˣ :=
  QuotientGroup.lift _ (sIdeleNorm F S)
    (Subgroup.map_le_iff_le_comap.mpr (sIdeleNorm_spec F S).2)

/-- Paper: Equation (3.1.2.1), p. 120. The norm on J_{F,S} takes the S-idelic norm of
any representative. -/
theorem sIdeleQuotientNorm_mk (g : (SAdeleRing F S)ˣ) :
    sIdeleQuotientNorm F S (QuotientGroup.mk g) = sIdeleNorm F S g := by
  rfl

-- TODO(paper-gap): Theorem A.1.5.2 gives compactness for the norm-one part of C_{F,S}.
-- Applying it to J_{F,S} requires projecting away the integer units outside S.

/-- Paper: §3.1.2, p. 120. The norm on J_{F,S} is proper. In particular its fiber over
one is compact. -/
theorem isProperMap_sIdeleQuotientNorm : IsProperMap (sIdeleQuotientNorm F S) := by
  sorry

/-- Paper: §3.1.2.3, p. 121. The S-idelic norm admits a continuous homomorphic section,
as used to parametrize the components in (3.1.2.5). -/
theorem sIdeleQuotientNorm_exists_section :
    ∃ σ : ℝ≥0ˣ →ₜ* SIdeleQuotient F S, RightInverse σ (sIdeleQuotientNorm F S) := by
  sorry

/-- Paper: §3.1.2, p. 120. The global idele class norm is a proper module. -/
theorem isProperMap_ideleClassNorm : IsProperMap (ideleClassNorm F) := by
  sorry

/-- Paper: §3.1.2, p. 120. The global idelic module supplies complex exponent charts on
the space of Hecke characters. -/
theorem ideleClass_hasNormTwistCharts : HasNormTwistCharts (ideleClassNorm F) := by
  sorry

/-- Paper: Equation (3.1.2.4), p. 121. Inserting the multiplicative group of a finite completion and
passing to idele classes is continuous. -/
theorem continuous_ideleClass_ofAdicCompletion (v : Primes(F)) :
    Continuous (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v) := by
  sorry

/-- Paper: Equation (3.1.2.4), p. 121. Inserting an infinite local multiplicative group
into the idele class group is continuous. -/
theorem continuous_ideleClass_ofCompletion (w : InfinitePlace F) :
    Continuous (IdeleClassGroup.ofCompletion (𝓞 F) F w) := by
  sorry

/-- Paper: Equation (3.1.2.4), p. 121. Restriction at a finite place is precomposition
with insertion in that coordinate followed by passage to idele classes. -/
def finitePlaceRestriction (v : Primes(F)) (c : HeckeCharacter (𝓞 F) F) :
    QuasiCharacter (v.adicCompletion F)ˣ :=
  c.comp ⟨IdeleClassGroup.ofAdicCompletion (𝓞 F) F v, continuous_ideleClass_ofAdicCompletion F v⟩

/-- Paper: Equation (3.1.2.4), p. 121. Restriction at an infinite place is precomposition
with insertion in that coordinate followed by passage to idele classes. -/
def infinitePlaceRestriction (w : InfinitePlace F) (c : HeckeCharacter (𝓞 F) F) :
    QuasiCharacter w.Completionˣ :=
  c.comp ⟨IdeleClassGroup.ofCompletion (𝓞 F) F w, continuous_ideleClass_ofCompletion F w⟩

/-- Paper: §3.1.2, p. 120. The value of a global character is the product of its local
values on an idele. Only finitely many finite-place factors differ from one. -/
theorem heckeCharacter_eq_prod_restrictions (c : HeckeCharacter (𝓞 F) F)
    (g : IdeleGroup (𝓞 F) F) :
    let a := fun w : InfinitePlace F => infinitePlaceRestriction F w c
      (Units.map ((Pi.evalRingHom _ w).comp (RingHom.fst _ _)).toMonoidHom g)
    let b := fun v : Primes(F) => finitePlaceRestriction F v c
      (Units.map ((RestrictedProduct.evalRingHom (fun w : Primes(F) => w.adicCompletion F) v).comp
        (RingHom.snd _ _)).toMonoidHom g)
    b.HasFiniteMulSupport ∧ c (QuotientGroup.mk g) = (∏ w, a w) * ∏ᶠ v, b v := by
  sorry

local notation "finiteNorm" => Units.map nnNormHom.toMonoidHom
local notation "infiniteNorm(" w ")" => (Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w

-- TODO(paper-gap): At a finite place the section in (3.1.2.2) must be taken over the
-- value group q^ℤ. The absolute value has no right inverse on all positive reals.

/-- Paper: Equation (3.1.2.2), p. 120. The finite-place surface is a cylinder for each
character of the local integer units. In exponent coordinates a uniformizer contributes q⁻ˢ.
Deviation: The auxiliary character of the discrete value group is specified by its value b
at the module of the chosen uniformizer. The coordinate equations specify the biholomorphism. -/
theorem finitePlace_quasiCharacterParametrization (v : Primes(F)) (π : (v.adicCompletion F)ˣ)
    (hπ : ‖π.val‖ = (v.asIdeal.absNorm : ℝ)⁻¹) (b : ℂˣ) :
    let q : ℝ := v.asIdeal.absNorm
    let periods := AddSubgroup.zmultiples (2 * (Real.pi : ℂ) * Complex.I / (Real.log q : ℂ))
    ∃ e : QuasiCharacter (v.adicCompletion F)ˣ ≃ₜ
        ((ℂ ⧸ periods) × PontryaginDual (v.adicCompletionIntegers F)ˣ),
      ∀ c, (∀ s : ℂ, (e c).1 = QuotientAddGroup.mk s ↔ c π = (b : ℂ) * (q : ℂ) ^ (-s)) ∧
        ∀ u, ((e c).2 u : ℂ) = c (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) := by
  sorry

/-- Paper: Equation (3.1.2.2), p. 120. At a finite place the locally defined complex
exponent is a chart for the normalized absolute value. -/
theorem finitePlace_hasNormTwistCharts (v : Primes(F)) :
    HasNormTwistCharts (finiteNorm : (v.adicCompletion F)ˣ →* ℝ≥0ˣ) := by
  sorry

/-- Paper: Equation (3.1.2.3), p. 121. A continuous splitting of the normalized absolute
value identifies the surface with a complex plane for each character of the norm-one group.
Deviation: We use the norm-one kernel specified below (3.1.2.3) for its archimedean unit
group. We state the homeomorphism with the coordinate formulas that determine its analytic maps. -/
theorem infinitePlace_quasiCharacterParametrization (w : InfinitePlace F)
    (σ : ℝ≥0ˣ →ₜ* w.Completionˣ) (hσ : RightInverse σ (infiniteNorm(w))) :
    let n : w.Completionˣ →* ℝ≥0ˣ := infiniteNorm(w)
    ∃ e : QuasiCharacter w.Completionˣ ≃ₜ (ℂ × PontryaginDual n.ker), ∀ c,
      (∀ t : ℝ≥0ˣ, c (σ t) = (((t : ℝ≥0) : ℝ) : ℂ) ^ (e c).1) ∧
        ∀ u : n.ker, ((e c).2 u : ℂ) = c u.val := by
  sorry

/-- Paper: Equation (3.1.2.3), p. 121. At an infinite place the normalized absolute value
gives complex exponent charts. Its multiplicity is one at real places and two at complex places. -/
theorem infinitePlace_hasNormTwistCharts (w : InfinitePlace F) :
    HasNormTwistCharts (infiniteNorm(w) : w.Completionˣ →* ℝ≥0ˣ) := by
  sorry

/-- Paper: §3.1.2, p. 120. Equip the Hecke characters with the norm-twist atlas. -/
scoped instance heckeCharacterChartedSpace : ChartedSpace ℂ (HeckeCharacter (𝓞 F) F) :=
  quasiCharacterChartedSpace _ (ideleClass_hasNormTwistCharts F)

/-- Paper: Lemma 3.1.2.1, p. 121. Restriction to a finite completion is a local
complex analytic isomorphism in the norm-twist atlases. -/
theorem finitePlaceRestriction_isLocalDiffeomorph (v : Primes(F)) :
    letI := quasiCharacterChartedSpace _ (finitePlace_hasNormTwistCharts F v)
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (finitePlaceRestriction F v) := by
  sorry

/-- Paper: Lemma 3.1.2.1, p. 121. Restriction to an infinite completion is a local
complex analytic isomorphism in the norm-twist atlases. -/
theorem infinitePlaceRestriction_isLocalDiffeomorph (w : InfinitePlace F) :
    letI := quasiCharacterChartedSpace _ (infinitePlace_hasNormTwistCharts F w)
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (infinitePlaceRestriction F w) := by
  sorry

/-- Paper: Equation (3.1.2.5), p. 121. A continuous splitting of the S-idelic norm
identifies the surface with a complex plane for each character of its norm-one subgroup.
Deviation: We give the homeomorphism with its analytic coordinates fixed by evaluation along
the splitting and restriction to the kernel. -/
theorem sIdeleQuotient_quasiCharacterParametrization (σ : ℝ≥0ˣ →ₜ* SIdeleQuotient F S)
    (hσ : RightInverse σ (sIdeleQuotientNorm F S)) :
    let n := sIdeleQuotientNorm F S
    ∃ e : QuasiCharacter (SIdeleQuotient F S) ≃ₜ (ℂ × PontryaginDual n.ker), ∀ c,
      (∀ t : ℝ≥0ˣ, c (σ t) = (((t : ℝ≥0) : ℝ) : ℂ) ^ (e c).1) ∧
        ∀ u : n.ker, ((e c).2 u : ℂ) = c u.val := by
  sorry

/-- Paper: Equation (3.1.2.5), p. 121. The S-idelic module gives complex exponent
charts on the space of quasi-characters of J_{F,S}. -/
theorem sIdeleQuotient_hasNormTwistCharts : HasNormTwistCharts (sIdeleQuotientNorm F S) := by
  sorry

/-- Paper: Equation (3.1.2.6), p. 121. The global quasi-characters trivial on the
local integer units at every finite place outside S form an open set. -/
theorem isOpen_unramifiedOutside :
    IsOpen {c : HeckeCharacter (𝓞 F) F | ∀ v ∉ S, c.IsUnramifiedAt v} := by
  sorry

/-- Paper: Equation (3.1.2.6), p. 121. The open subspace Ω_S(C_F) consists of the
Hecke characters unramified at every finite place outside S. -/
def unramifiedOutside : TopologicalSpace.Opens (HeckeCharacter (𝓞 F) F) :=
  ⟨{c | ∀ v ∉ S, c.IsUnramifiedAt v}, isOpen_unramifiedOutside F S⟩

/-- Paper: Equation (3.1.2.6), p. 121. Membership in Ω_S is equivalent to triviality
of the continuous local restrictions on all integer units outside S. -/
theorem mem_unramifiedOutside_iff (c : HeckeCharacter (𝓞 F) F) :
    c ∈ unramifiedOutside F S ↔ ∀ v ∉ S, ∀ u : (v.adicCompletionIntegers F)ˣ,
      finitePlaceRestriction F v c (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) = 1 := by
  change (∀ v ∉ S, c.IsUnramifiedAt v) ↔ _
  simp only [HeckeCharacter.isUnramifiedAt_iff]
  refine forall_congr' fun v => imp_congr_right fun _ => forall_congr' fun u => ?_
  change c.restrict v ↑(Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) = 1 ↔ _
  rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  rfl

/-- Paper: Equations (3.1.2.7)–(3.1.2.8), p. 121. Insert an S-idele into the full idele
group by multiplying its single-coordinate insertions over S, including all infinite places. -/
def sIdeleInsertion : (SAdeleRing F S)ˣ →* IdeleGroup (𝓞 F) F :=
  (∏ w : InfinitePlace F, (IdeleGroup.ofCompletion (𝓞 F) F w).comp
    (Units.map ((Pi.evalRingHom _ w).comp (RingHom.fst _ _)).toMonoidHom)) *
  ∏ v : S, (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val).comp
    (Units.map ((Pi.evalRingHom _ v).comp (RingHom.snd _ _)).toMonoidHom)

/-- Paper: Equation (3.1.2.8), p. 121. The inserted idele has the given components in S
and component one at every finite place outside S. -/
theorem sIdeleInsertion_apply (g : (SAdeleRing F S)ˣ) :
    (sIdeleInsertion F S g).val.1 = g.val.1 ∧
    (∀ v : S, (sIdeleInsertion F S g).val.2 v.val = g.val.2 v) ∧
    ∀ v ∉ S, (sIdeleInsertion F S g).val.2 v = 1 := by
  classical
  have hfinite (v : Primes(F)) :
      (sIdeleInsertion F S g).val.2 v =
        ∏ u : S, (FiniteAdeleRing.ofAdicCompletion F u.val (g.val.2 u)) v := by
    let eval : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
      RestrictedProduct.evalRingHom _ v
    change eval (sIdeleInsertion F S g).val.2 =
      ∏ u : S, eval (FiniteAdeleRing.ofAdicCompletion F u.val (g.val.2 u))
    rw [← map_prod]
    apply congrArg eval
    simp [sIdeleInsertion, MonoidHom.finsetProd_apply, AdeleRing, Prod.snd_prod]
  refine ⟨?_, ?_, ?_⟩
  · simp [sIdeleInsertion, MonoidHom.finsetProd_apply, AdeleRing, Prod.fst_prod,
      InfiniteAdeleRing.ofCompletion]
    exact Finset.univ_prod_mulSingle g.val.1
  · intro v
    rw [hfinite, Finset.prod_eq_single_of_mem v (Finset.mem_univ v)]
    · exact RestrictedProduct.mulSingle_eq_same _ _ _
    · intro u _ huv
      have h : v.val ≠ u.val := fun h => huv (Subtype.ext h.symm)
      exact RestrictedProduct.mulSingle_eq_of_ne _ _ h
  · intro v hv
    rw [hfinite]
    apply Finset.prod_eq_one
    intro u _
    have h : v ≠ u.val := fun h => hv (h ▸ u.property)
    exact RestrictedProduct.mulSingle_eq_of_ne _ _ h

/-- Paper: Equation (3.1.2.7), p. 121. Extension by one is a closed topological embedding. -/
theorem isClosedEmbedding_sIdeleInsertion : IsClosedEmbedding (sIdeleInsertion F S) := by
  sorry

local notation "pullbackS(" c ")" => MonoidHom.comp (ContinuousMonoidHom.toMonoidHom c)
  (MonoidHom.comp (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)) (sIdeleInsertion F S))

/-- Paper: Equation (3.1.2.9), p. 121. For a character unramified outside S, pullback
along insertion kills the projected diagonal S-units. -/
theorem sIdeleRestriction_descent (c : unramifiedOutside F S) :
    projectedDiagonal ≤ (pullbackS(c.val)).ker := by
  sorry

/-- Paper: Equation (3.1.2.9), p. 121. The S-local restriction is the quotient lift of
the pullback from idele classes. Its domain carries the open subspace topology. -/
def sIdeleRestriction (c : unramifiedOutside F S) : QuasiCharacter (SIdeleQuotient F S) :=
  ⟨QuotientGroup.lift _ (pullbackS(c.val)) (sIdeleRestriction_descent F S c),
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
      (c.val.continuous.comp (QuotientGroup.continuous_mk.comp
        (isClosedEmbedding_sIdeleInsertion F S).continuous))⟩

/-- Paper: Equation (3.1.2.9), p. 121. On an S-idele representative, the restriction
evaluates the original character on the class of the inserted idele. -/
theorem sIdeleRestriction_mk (c : unramifiedOutside F S) (g : (SAdeleRing F S)ˣ) :
    sIdeleRestriction F S c (QuotientGroup.mk g) = c.val (QuotientGroup.mk (sIdeleInsertion F S g)) := by
  sorry

/-- Paper: Lemma 3.1.2.2, p. 121. Every quasi-character of J_{F,S} extends to an
idele class character unramified outside S. -/
theorem sIdeleRestriction_surjective : Surjective (sIdeleRestriction F S) := by
  sorry

/-- Paper: Lemma 3.1.2.2, p. 121. Restriction from the open unramified locus to the
S-idelic character surface is a local complex analytic isomorphism. -/
theorem sIdeleRestriction_isLocalDiffeomorph :
    letI := quasiCharacterChartedSpace _ (sIdeleQuotient_hasNormTwistCharts F S)
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (sIdeleRestriction F S) := by
  sorry

/-- Paper: §3.1.2.3, p. 122. As S varies, the open loci of characters unramified
outside S cover the entire space of Hecke characters. -/
theorem iUnion_unramifiedOutside :
    (⋃ T : Finset (Primes(F)), (unramifiedOutside F T : Set (HeckeCharacter (𝓞 F) F))) = Set.univ := by
  sorry

end Ideles

end RiemannMasullo
