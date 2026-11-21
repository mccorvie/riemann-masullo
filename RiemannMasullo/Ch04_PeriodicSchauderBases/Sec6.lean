module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec2
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec5

/-!
# Periodic Schauder bases in the presence of multiplicity

Masullo, §4.6, pp. 209–220. Lists of cyclic differences retain repetitions.
-/

@[expose] public noncomputable section

open Function MeasureTheory Set Topology TopologicalSpace
open scoped NNReal Pointwise

set_option quotPrecheck false

namespace RiemannMasullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [hSC : SecondCountableTopology G]
variable (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)

local notation "K" => m.toMonoidHom.ker
local notation "E" => ModulatedExponentialDecay m (univ : Set ℝ)
local notation "ρK" => (schwartzBruhatTranslationAction (G := G)).comp (K).subtype
local notation "period" x => Real.log ((m x).val : ℝ)

/-! ## 4.6.1 Bases in the presence of multiplicity -/

-- Situation 4.6.1.1 uses the section frequency and normalized phase from
-- existsUnique_modulatedMellinSectionFrequency and existsUnique_modulatedCharacterPhase.

-- TODO(paper-gap): Situation 4.6.1.1(4) omits the right-hand side of the restriction
-- equation. The real phase in (5) is unique only modulo 2π / log |γₖ|.

variable (ω : PontryaginDual m.toMonoidHom.ker) (γ : G)

/-- Paper: Notation 4.6.1.1, p. 209. The fiber consists of characters that
annihilate the generator and restrict to the indicated norm-one character.
Deviation: The restriction itself indexes the fiber. -/
def modulatedCyclicAnnihilatorFiber (m : G →ₜ* ℝ≥0ˣ)
    (ω : PontryaginDual m.toMonoidHom.ker) (γ : G) : Set (PontryaginDual G) :=
  let K₁ := m.toMonoidHom.ker
  {ξ | ξ ∈ lcaAnnihilator (Subgroup.zpowers γ) ∧
    PontryaginDual.map (⟨K₁.subtype, continuous_subtype_val⟩ : K₁ →ₜ* G) ξ = ω}

/-- Paper: Notation 4.6.1.1, p. 209. The fiber can be tested at the generator
and on each element of the norm-one subgroup. -/
theorem mem_modulatedCyclicAnnihilatorFiber_iff (ξ : PontryaginDual G) :
    ξ ∈ modulatedCyclicAnnihilatorFiber m ω γ ↔
      ξ γ = 1 ∧ ∀ u : K, ξ u.val = ω u := by
  constructor
  · rintro ⟨hann, hres⟩
    exact ⟨(mem_lcaAnnihilator_iff _ ξ).mp hann ⟨γ, Subgroup.mem_zpowers γ⟩,
      DFunLike.congr_fun hres⟩
  · rintro ⟨hγ, hres⟩
    refine ⟨(mem_lcaAnnihilator_iff _ ξ).mpr ?_, PontryaginDual.ext hres⟩
    have hker : Subgroup.zpowers γ ≤ ξ.toMonoidHom.ker := Subgroup.zpowers_le.mpr hγ
    exact fun u ↦ hker u.property

include hm hSC in
/-- Paper: Remark 4.6.1.2, p. 210. Every norm-one character has a compact
kernel subgroup with finitely generated annihilator. For that subgroup the
entire cyclic fiber annihilates its product with the cyclic subgroup. -/
theorem modulatedCyclicAnnihilatorFiber_subset :
    ∃ k : Subgroup K, IsCompact (k : Set K) ∧ (lcaAnnihilator k).FG ∧
      ω ∈ lcaAnnihilator k ∧
      modulatedCyclicAnnihilatorFiber m ω γ ⊆
        (lcaAnnihilator (Subgroup.zpowers γ ⊔ k.map (K).subtype) : Set (PontryaginDual G)) := by sorry

section Difference

variable (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty)

/-- Paper: Lemma 4.6.1.3(1) and Corollary 4.6.3.1, pp. 210, 219.
The iterated difference composes the cyclic differences for the entries
of the list, with one factor for each occurrence.
Deviation: The operator is defined on the ambient decay space and then
restricted to isotypes. The empty list gives the identity. -/
def modulatedDifferenceProduct (S : List G) :
    ModulatedExponentialDecay m I →L[ℂ] ModulatedExponentialDecay m I :=
  (S.map fun g ↦ modulatedCyclicDifference m g hm hms I hInt hne).prod

/-- Paper: Lemma 4.6.1.3(1) and Example 4.6.1.6, pp. 210, 217.
A repeated generator gives the second finite difference at every point. -/
theorem modulatedDifferenceProduct_pair_apply (f : ModulatedExponentialDecay m I) (x : G) :
    (modulatedDifferenceProduct m hm hms I hInt hne [γ, γ] f).val x =
      f.val x - 2 * f.val (γ * x) + f.val (γ ^ 2 * x) := by sorry

end Difference

/-- Paper: Lemma 4.6.1.3 and Corollary 4.6.3.1, pp. 210, 219.
The decay isotype consists of the functions whose zero twist belongs to
the ordinary Schwartz–Bruhat isotype for the same norm-one character. -/
def modulatedDecayIsotype (m : G →ₜ* ℝ≥0ˣ) (I : Set ℝ) (h0 : 0 ∈ I)
    (ω : PontryaginDual m.toMonoidHom.ker) : Submodule ℂ (ModulatedExponentialDecay m I) :=
  let ρ := (schwartzBruhatTranslationAction (G := G)).comp m.toMonoidHom.ker.subtype
  (actionIsotype ρ ω).comap (modulatedExponentialDecayTwist m I ⟨0, h0⟩)

local notation "H₀[" w "]" =>
  (modulatedDecayIsotype m (Set.univ : Set ℝ) (Set.mem_univ (0 : ℝ)) w)

/-- Paper: Lemma 4.6.1.3, p. 210. Isotype membership means left
translation by each norm-one element acts by its character value. -/
theorem mem_modulatedDecayIsotype_iff (I : Set ℝ) (h0 : 0 ∈ I)
    (f : ModulatedExponentialDecay m I) :
    f ∈ (modulatedDecayIsotype m I h0 ω) ↔ ∀ (u : K) (x : G),
      f.val (u.val⁻¹ * x) = (ω u : ℂ) * f.val x := by sorry

/-- Paper: Lemma 4.6.1.3(1), p. 210. The difference product preserves each
norm-one isotype. The same restriction is used for intervals containing zero
in Corollary 4.6.3.1. -/
theorem modulatedDifferenceProduct_mem_isotype
    (I : Set ℝ) (hInt : OrdConnected I) (h0 : 0 ∈ I) (S : List G) :
    ∀ f ∈ modulatedDecayIsotype m I h0 ω,
      modulatedDifferenceProduct m hm hms I hInt ⟨0, h0⟩ S f ∈
        modulatedDecayIsotype m I h0 ω := by sorry

/-- Paper: Equation (4.6.1.3), p. 210. The cyclic difference product on
the isotype is the restriction of the ambient operator. -/
def modulatedIsotypicDifferenceProduct (I : Set ℝ) (hInt : OrdConnected I) (h0 : 0 ∈ I)
    (S : List G) : (modulatedDecayIsotype m I h0 ω) →L[ℂ] (modulatedDecayIsotype m I h0 ω) :=
  (modulatedDifferenceProduct m hm hms I hInt ⟨0, h0⟩ S).restrict
    (modulatedDifferenceProduct_mem_isotype (m := m) (hm := hm) (hms := hms) (ω := ω) I hInt h0 S)

/-- Paper: Equation (4.6.1.3), p. 210. Forgetting the isotype condition
recovers the same difference product on the ambient decay space. -/
theorem modulatedIsotypicDifferenceProduct_apply_coe
    (I : Set ℝ) (hInt : OrdConnected I) (h0 : 0 ∈ I) (S : List G)
    (f : modulatedDecayIsotype m I h0 ω) :
    (modulatedIsotypicDifferenceProduct (m := m) (hm := hm) (hms := hms) (ω := ω) I hInt h0 S f).val =
      modulatedDifferenceProduct m hm hms I hInt ⟨0, h0⟩ S f.val := by sorry

local notation "P[" w "," s "]" =>
  (modulatedIsotypicDifferenceProduct (m := m) (hm := hm) (hms := hms) (ω := w)
    univ ordConnected_univ (mem_univ (0 : ℝ)) s)

section IsotypicQuotient

variable (S₀ : List G) (hS₀ : ∀ g ∈ S₀, 1 < (m g).val)
variable (hγ : 1 < (m γ).val)

include hS₀ in
/-- Paper: Lemma 4.6.1.3(1), p. 210. The product of expanding cyclic
differences has closed range in the norm-one isotype of the decay space. -/
theorem modulatedIsotypicDifferenceProduct_isClosed_range :
    IsClosed (range (P[ω, S₀])) := by sorry

include hS₀ in
/-- Paper: Lemma 4.6.1.3(2), p. 210. The isotypic quotient by the difference
product is a separable nuclear Fréchet space. -/
theorem modulatedIsotypicDifferenceProduct_quotient :
    let U := H₀[ω] ⧸ (P[ω, S₀]).range
    SeparableSpace U ∧ IsNuclearTVS U ∧ IsFrechetTVS U := by sorry

include hS₀ hγ in
/-- Paper: Lemma 4.6.1.3(3), pp. 210–211. Applying the last cyclic difference
identifies the shorter quotient with the last difference image modulo the
full product image. The isomorphism intertwines the jointly continuous
left translation actions on the two quotients. -/
theorem modulatedIsotypicDifferenceProduct_cancel_equiv :
    let A := P[ω, [γ]]
    let R := A.range
    let N := (P[ω, S₀]).range
    let M := (P[ω, S₀ ++ [γ]]).range.comap R.subtype
    let X := H₀[ω] ⧸ N
    let Y := R ⧸ M
    ∃ F : X ≃L[ℂ] Y,
      (∀ f, F (N.mkQ f) = M.mkQ (A.rangeRestrict f)) ∧
      (∃ (ρ : G × X → X) (τ : G × Y → Y), Continuous ρ ∧ Continuous τ ∧
        (∀ g (f : H₀[ω]), ∃ f' : H₀[ω],
          (∀ x, f'.val.val x = f.val.val (g⁻¹ * x)) ∧ ρ (g, N.mkQ f) = N.mkQ f') ∧
        (∀ g (u : R), ∃ u' : R,
          (∀ x, u'.val.val.val x = u.val.val.val (g⁻¹ * x)) ∧ τ (g, M.mkQ u) = M.mkQ u') ∧
        ∀ g v, F (ρ (g, v)) = τ (g, F v)) ∧
      SeparableSpace (R ⧸ M) ∧ IsNuclearTVS (R ⧸ M) ∧ IsFrechetTVS (R ⧸ M) := by sorry

end IsotypicQuotient

-- TODO(paper-gap): In Lemma 4.6.1.4(1), bₖ must be replaced by log bₖ.
-- The printed condition holds for b₁ = 2 and b₂ = 3, but log 2 / log 3 is irrational.

/-- Paper: Lemma 4.6.1.4, p. 211. Logarithmic commensurability of the bases
is equivalent to finiteness of all mutual cyclic phases.
Deviation: Part (1) uses log bₖ as in both directions of the proof. -/
theorem finite_cyclicPhases_iff {N : ℕ} (hN : 0 < N) (b : Fin N → ℝ) (hb : ∀ k, 1 < b k) :
    (∃ a : ℝ, 1 < a ∧ ∀ k, ∃ r : ℚ, Real.log (b k) = (r : ℝ) * Real.log a) ↔
      (range fun p : Fin N × Fin N × ℤ ↦
        Circle.exp (2 * Real.pi * (p.2.2 : ℝ) * (Real.log (b p.1) / Real.log (b p.2.1)))).Finite := by
  let phases (x : ℝ) := range fun n : ℤ ↦ Circle.exp (2 * Real.pi * (n : ℝ) * x)
  -- The phases are the image of the subgroup generated by x in ℝ/ℤ.
  have finite_phases_iff (x : ℝ) : (phases x).Finite ↔ ∃ q : ℚ, (q : ℝ) = x := by
    have himage : phases x = AddCircle.toCircle ''
        (AddSubgroup.zmultiples (x : AddCircle (1 : ℝ)) : Set (AddCircle (1 : ℝ))) := by
      rw [AddSubgroup.coe_zmultiples, ← range_comp']
      apply congrArg range
      funext n
      rw [← AddCircle.coe_zsmul, AddCircle.toCircle_apply_mk, div_one, zsmul_eq_mul, mul_assoc]
    rw [himage, finite_image_iff (AddCircle.injective_toCircle one_ne_zero).injOn]
    change Finite (AddSubgroup.zmultiples (x : AddCircle (1 : ℝ))) ↔ _
    rw [finite_zmultiples, AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div, div_one]
  let ratio (i j : Fin N) := Real.log (b i) / Real.log (b j)
  have hunion : (range fun p : Fin N × Fin N × ℤ ↦
      Circle.exp (2 * Real.pi * (p.2.2 : ℝ) * ratio p.1 p.2.1)) =
      ⋃ i, ⋃ j, phases (ratio i j) := by
    ext z
    simp only [mem_range, Prod.exists, mem_iUnion, phases]
  rw [hunion]
  constructor
  · rintro ⟨a, ha, h⟩
    refine finite_iUnion fun i ↦ finite_iUnion fun j ↦ (finite_phases_iff _).2 ?_
    obtain ⟨r, hr⟩ := h i
    obtain ⟨s, hs⟩ := h j
    refine ⟨r / s, ?_⟩
    simp only [ratio, Rat.cast_div, hr, hs, mul_div_mul_right _ _ (Real.log_pos ha).ne']
  · intro h
    let j : Fin N := ⟨0, hN⟩
    refine ⟨b j, hb j, fun i ↦ ?_⟩
    have hi := h.subset (subset_iUnion₂ i j)
    obtain ⟨q, hq⟩ := (finite_phases_iff _).mp hi
    exact ⟨q, ((eq_div_iff (Real.log_pos (hb j)).ne').mp hq).symm⟩

section Moments

variable {N : ℕ} (γs : Fin N → G)

/-- Paper: Equation (4.6.1.12), p. 212. The periodic spectrum is the union of
the cyclic annihilator fibers for the given norm-one character. -/
def modulatedPeriodicSpectrum (m : G →ₜ* ℝ≥0ˣ) (ω : PontryaginDual m.toMonoidHom.ker)
    (γs : Fin N → G) : Set (PontryaginDual G) :=
  ⋃ k, modulatedCyclicAnnihilatorFiber m ω (γs k)

/-- Paper: Equations (4.6.1.12)–(4.6.1.13), p. 212. The spectrum multiplicity
counts the entries whose cyclic fiber contains the character, including repetitions.
Deviation: The multiplicity is extended by zero off the union. -/
def modulatedPeriodicMultiplicity (m : G →ₜ* ℝ≥0ˣ) (ω : PontryaginDual m.toMonoidHom.ker)
    (γs : Fin N → G) (ξ : PontryaginDual G) : ℕ :=
  haveI : DecidablePred (fun k : Fin N ↦ ξ ∈ modulatedCyclicAnnihilatorFiber m ω (γs k)) :=
    Classical.decPred _
  (Finset.univ.filter fun k ↦ ξ ∈ modulatedCyclicAnnihilatorFiber m ω (γs k)).card

/-- Paper: Equations (4.6.1.12)–(4.6.1.13), p. 212. The spectrum consists
exactly of the characters of positive multiplicity. -/
theorem mem_modulatedPeriodicSpectrum_iff (ξ : PontryaginDual G) :
    ξ ∈ modulatedPeriodicSpectrum m ω γs ↔ 0 < modulatedPeriodicMultiplicity m ω γs ξ := by sorry

/-- Paper: Equation (4.6.1.13) and Example 4.6.1.6, pp. 212, 217.
Every character in the fiber for a twice-repeated generator has multiplicity two. -/
theorem modulatedPeriodicMultiplicity_repeat (ξ : PontryaginDual G)
    (hξ : ξ ∈ modulatedCyclicAnnihilatorFiber m ω γ) :
    modulatedPeriodicMultiplicity m ω (fun _ : Fin 2 ↦ γ) ξ = 2 := by sorry

variable (hγs : ∀ k, 1 < (m (γs k)).val)

include hm hγs in
/-- Paper: Equation (4.6.1.12), p. 212. The finite union of the cyclic
fibers is discrete in the unitary dual. -/
theorem modulatedPeriodicSpectrum_isDiscrete :
    IsDiscrete (modulatedPeriodicSpectrum m ω γs) := by sorry

variable (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
variable (hχ : ∀ (ω' : PontryaginDual m.toMonoidHom.ker) (u : m.toMonoidHom.ker), χ ω' u.val = ω' u)
variable (t₀ : Fin N → PontryaginDual m.toMonoidHom.ker → ℝ)
variable (ht₀ : ∀ k ω',
  let L := Real.log ((m (γs k)).val : ℝ)
  t₀ k ω' ∈ Ico 0 (2 * Real.pi / L) ∧ Circle.exp (t₀ k ω' * L) = χ ω' (γs k))

local notation "freq[" k "," n "]" =>
  ((PontryaginDual.map
    (⟨QuotientGroup.mk' (Subgroup.zpowers (γs k)), QuotientGroup.continuous_mk⟩ :
      G →ₜ* (G ⧸ Subgroup.zpowers (γs k)))
    (modulatedCyclicCharacter m (γs k) (hγs k) χ (t₀ k) (ht₀ k) (ω, n)))⁻¹)

include hm hms hχ in
/-- Paper: Situation 4.6.1.1(5) and Theorem 4.6.1.5, pp. 209, 212.
The integer frequency parametrizes each cyclic fiber bijectively.
Deviation: Frequencies have denominator log |γₖ| and use the normalized phase.
The character is the inverse of the pulled-back basis character of §4.4. -/
theorem modulatedPeriodicFrequency_bijective (k : Fin N) :
    Injective (fun n : ℤ ↦ freq[k, n]) ∧
      range (fun n : ℤ ↦ freq[k, n]) = modulatedCyclicAnnihilatorFiber m ω (γs k) := by sorry

variable [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [hμHaar : μ.IsHaarMeasure]

local notation "integrand[" ξ "," r "," f "]" =>
  (fun g : G ↦ (f : H₀[ω]).val.val g * (ξ g : ℂ) * (period g : ℂ) ^ (r : ℕ))

include hm hms hμHaar in
/-- Paper: Equation (4.6.1.14), p. 212. Every log-moment is integrable and
its integral defines a continuous linear functional on the isotype.
Deviation: Integrability and continuity hold for all unitary characters and
all natural log-powers. Descent to the quotient imposes the multiplicity bound. -/
theorem modulatedLogMoment_linearContinuous (ξ : PontryaginDual G) (r : ℕ) :
    (∀ f : H₀[ω], Integrable (integrand[ξ, r, f]) μ) ∧
      IsLinearMap ℂ (fun f : H₀[ω] ↦ ∫ g, integrand[ξ, r, f] g ∂μ) ∧
      Continuous (fun f : H₀[ω] ↦ ∫ g, integrand[ξ, r, f] g ∂μ) := by sorry

/-- Paper: Equation (4.6.1.14), p. 212. The log-moment integrates the test
function against a unitary character times the indicated power of the log-module. -/
def modulatedLogMoment (ξ : PontryaginDual G) (r : ℕ) : StrongDual ℂ H₀[ω] :=
  let h := modulatedLogMoment_linearContinuous (m := m) (hm := hm) (hms := hms) (ω := ω) (μ := μ) ξ r
  ⟨IsLinearMap.mk' (fun f : H₀[ω] ↦ ∫ g, integrand[ξ, r, f] g ∂μ) h.2.1, h.2.2⟩

/-- Paper: Equation (4.6.1.14), p. 212. The zeroth moment at the trivial
character is the integral of the test function. -/
theorem modulatedLogMoment_one_zero (f : H₀[ω]) :
    modulatedLogMoment (m := m) (hm := hm) (hms := hms) (ω := ω) (μ := μ) 1 0 f = ∫ g, f.val.val g ∂μ := by sorry

local notation "J" => {p : PontryaginDual G × ℕ // p.2 < modulatedPeriodicMultiplicity m ω γs p.1}
local notation "S" => List.ofFn γs
local notation "R" => (P[ω, S]).range
local notation "U" => (H₀[ω] ⧸ R)

include hγs in
/-- Paper: Theorem 4.6.1.5 and Equation (4.6.1.15), p. 212.
Log-moments of order strictly below the multiplicity vanish on the
isotypic difference product, so they descend to the quotient. -/
theorem modulatedLogMoment_range_le_ker (j : J) :
    R ≤ (modulatedLogMoment (m := m) (hm := hm) (hms := hms) (ω := ω) (μ := μ) j.val.1 j.val.2).ker := by sorry

/-- Paper: Equation (4.6.1.15), p. 212. Each allowed log-moment is viewed
as a member of the strong dual of the difference quotient. -/
def modulatedQuotientLogMoment (j : J) : StrongDual ℂ U :=
  (R).liftQL (modulatedLogMoment (m := m) (hm := hm) (hms := hms) (ω := ω) (μ := μ) j.val.1 j.val.2)
    (modulatedLogMoment_range_le_ker (m := m) (hm := hm) (hms := hms)
      (ω := ω) (γs := γs) (hγs := hγs) (μ := μ) j)

local notation "D" =>
  (modulatedQuotientLogMoment (m := m) (hm := hm) (hms := hms)
    (ω := ω) (γs := γs) (hγs := hγs) (μ := μ))

/-- Paper: Equations (4.6.1.14)–(4.6.1.15), p. 212. On a quotient
representative the descended moment is the original log-moment integral. -/
theorem modulatedQuotientLogMoment_mkQ (j : J) (f : H₀[ω]) :
    D j ((R).mkQ f) = ∫ g, integrand[j.val.1, j.val.2, f] g ∂μ := by sorry

-- TODO(paper-gap): Theorem 4.6.1.5 as printed assumes commensurability of the
-- logarithms of the periods. A unit period and a Liouville period satisfy that
-- hypothesis, but their distinct lattice frequencies can approach each other
-- faster than any inverse power. See the report for the counterexample.

include hm hms hγs in
/-- Paper: Theorem 4.6.1.5, p. 212. The moment index is countably infinite,
so the arbitrary enumerations used for the bases exist. -/
theorem modulatedPeriodicMomentIndex_enumerable (hN : 0 < N) :
    Nonempty (ℕ ≃ J) := by sorry

variable (hcomm : ∃ a : ℝ, 0 < a ∧ ∀ k, ∃ r : ℚ, Real.log ((m (γs k)).val : ℝ) = (r : ℝ) * a)

include hcomm in
/-- Paper: Theorem 4.6.1.5 and Equations (4.6.1.15)–(4.6.1.16), p. 212.
Every enumeration of the moment family is an unconditional basis of the
strong dual. The biorthogonal vectors are an absolute basis of the quotient.
Deviation: The actual log-periods are commensurate, as required by the
finite-phase step (4.6.1.25). -/
theorem modulatedQuotientLogMoment_bases (σ : ℕ ≃ J) :
    ∃ ψ : J → U,
      let e := ψ ∘ σ
      let d := D ∘ σ
      let ev : ℕ → StrongDual ℂ (StrongDual ℂ U) :=
        fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (e n)
      IsSchauderBasis e d ∧ SchauderBasis.IsAbsolute e d ∧
        IsSchauderBasis d ev ∧ SchauderBasis.IsUnconditional d ev := by sorry

include hχ hcomm in
/-- Paper: Theorem 4.6.1.5(1), p. 212. A continuous seminorm of the
biorthogonal vectors grows at most polynomially in each lattice frequency,
uniformly in the moment order.
Deviation: The actual log-periods are commensurate. A positive multiple
of a power of one plus the frequency norm expresses polynomial growth. -/
theorem modulatedQuotientLogMoment_biorthogonal_growth (ψ : J → U)
    (hdiag : ∀ j, D j (ψ j) = 1) (hoff : ∀ j k, j ≠ k → D j (ψ k) = 0)
    (q : Seminorm ℂ U) (hq : Continuous q) :
    ∃ d : ℕ, ∀ k : Fin N, ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℤ) (j : J), j.val.1 = freq[k, n] →
        q (ψ j) ≤ C * (1 + |(n : ℝ)|) ^ d := by sorry

include hχ in
/-- Paper: Theorem 4.6.1.5(2), p. 212. At each fixed moment order, the
coefficients on each cyclic lattice give a Schwartz sequence.
Deviation: The sequence is extended by zero at indices where the moment
order is at least the multiplicity, consistent with (4.6.1.15).
The decay estimate does not require commensurability. -/
theorem modulatedLogMoment_lattice_schwartz (f : H₀[ω]) (r : Fin N) (k : Fin N) :
    ∃ v : SchwartzBruhat (Multiplicative ℤ), ∀ n : ℤ, v (Multiplicative.ofAdd n) =
      if r.val < modulatedPeriodicMultiplicity m ω γs (freq[k, n]) then
        modulatedLogMoment (m := m) (hm := hm) (hms := hms) (ω := ω) (μ := μ) (freq[k, n]) r.val f
      else 0 := by sorry

end Moments

section RepeatedGenerator

variable (a : ℝ≥0ˣ) (ha : 1 < a.val)

local notation "A" => SchwartzBergman (univ : Set ℝ)
local notation "mPos" => ContinuousMonoidHom.id ℝ≥0ˣ
local notation "Mellin" => positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty
local notation "factor[" z "]" => (1 - Complex.exp (-((Real.log (a.val : ℝ) : ℂ) * z)))

include ha in
/-- Paper: Example 4.6.1.6, p. 217. In logarithmic coordinates Mellin
transform carries the cyclic difference to multiplication by the given
entire factor. Its square has closed range and represents the repeated difference. -/
theorem repeatedCyclicDifference_mellin (hmId : IsModulation mPos) (hsId : Surjective mPos) :
    letI : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
    let EPos := ModulatedExponentialDecay mPos (univ : Set ℝ)
    let Δ := modulatedDifferenceProduct mPos hmId hsId univ ordConnected_univ univ_nonempty [a]
    let Δ₂ := modulatedDifferenceProduct mPos hmId hsId univ ordConnected_univ univ_nonempty [a, a]
    ∃ (e : PositiveRealExponentialDecay univ ≃L[ℂ] EPos) (T : A →L[ℂ] A),
      (∀ f t, (e f).val t = f.val (Real.log (t.val : ℝ))) ∧
      (∀ f z, (T f).val z = factor[z] * f.val z) ∧
      (∀ f, Mellin (e.symm (Δ f)) = T (Mellin (e.symm f))) ∧
      (∀ f, Mellin (e.symm (Δ₂ f)) = T (T (Mellin (e.symm f)))) ∧
      IsClosed (range (T.comp T)) := by sorry

variable (T : SchwartzBergman univ →L[ℂ] SchwartzBergman univ)
variable (hT : ∀ f z, (T f).val z =
  (1 - Complex.exp (-((Real.log (a.val : ℝ) : ℂ) * z))) * f.val z)

local notation "R₁" => T.range
local notation "R₂" => (T.comp T).range
local notation "N₂" => (R₂).comap (R₁).subtype

include ha hT in
/-- Paper: Example 4.6.1.6 and Equation (4.6.1.29), p. 217.
The first and second multiplier images give a short exact sequence.
Its left inclusion is a closed topological embedding. -/
theorem repeatedCyclicDifference_mellin_exact :
    ∃ (i : ((R₁) ⧸ N₂) →L[ℂ] (A ⧸ R₂)) (q : (A ⧸ R₂) →L[ℂ] (A ⧸ R₁)),
      (∀ f : R₁, i ((N₂).mkQ f) = (R₂).mkQ f.val) ∧
      (∀ f : A, q ((R₂).mkQ f) = (R₁).mkQ f) ∧
      IsClosedEmbedding i ∧ Function.Exact i q ∧ Surjective q := by sorry

include ha hT in
/-- Paper: Example 4.6.1.6 and Equation (4.6.1.30), p. 218.
Division by the entire factor identifies the image quotient with the
quotient by the single factor. The rule is specified on products so it
applies also at the zeros of the factor. -/
theorem repeatedCyclicDifference_mellin_division :
    ∃ F : ((R₁) ⧸ N₂) ≃L[ℂ] (A ⧸ R₁),
      ∀ f : A, F ((N₂).mkQ (T.rangeRestrict f)) = (R₁).mkQ f := by sorry

include ha hT in
/-- Paper: Example 4.6.1.6, p. 218. Evaluation of the analytic quotient at
a lattice zero equals the derivative of the numerator divided by the
logarithm of the generator. -/
theorem repeatedCyclicDifference_mellin_division_eval (f : A) (n : ℤ) :
    let z : ℂ := ((2 * Real.pi * (n : ℝ) / Real.log (a.val : ℝ) : ℝ) : ℂ) * Complex.I
    f.val z = deriv (T f).val z / (Real.log (a.val : ℝ) : ℂ) := by sorry

include ha hT in
/-- Paper: Example 4.6.1.6, p. 218. The normalized Fourier coefficient of
the periodized profile is a first derivative of the repeated-generator numerator.
Deviation: The coefficient in (4.2.1.4) contributes another inverse log-period
and uses the negative Mellin frequency. -/
theorem repeatedCyclicDifference_mellin_division_fourierCoeff
    (f : PositiveRealExponentialDecay univ) (n : ℤ) :
    let L := Real.log (a.val : ℝ)
    let z := (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) / (L : ℂ)
    cyclicFourierCoeff n (cyclicPeriodizationCLM (a.val : ℝ) (by exact_mod_cast ha) f) =
      deriv (T (Mellin f)).val (-z) / (L : ℂ) ^ 2 := by
  dsimp only
  have hreal : 1 < (a.val : ℝ) := by exact_mod_cast ha
  have hL : (Real.log (a.val : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hreal).ne'
  have hc := cyclicQuotientMellinCoeff_mk (a.val : ℝ) hreal n f
  change (Real.log (a.val : ℝ) : ℂ) * cyclicFourierCoeff n
    (cyclicPeriodizationCLM (a.val : ℝ) hreal f) = _ at hc
  rw [← positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ univ_nonempty
    f _ (mem_univ _)] at hc
  have hd := repeatedCyclicDifference_mellin_division_eval a ha T hT (Mellin f) (-n)
  dsimp only at hd
  have hz : ((2 * Real.pi * ((-n : ℤ) : ℝ) / Real.log (a.val : ℝ) : ℝ) : ℂ) * Complex.I =
      -(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (Real.log (a.val : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [hz] at hd
  rw [hd] at hc
  field_simp [hL] at hc ⊢
  linear_combination hc

end RepeatedGenerator

/-! ## 4.6.2 Support conditions in the presence of multiplicity -/

variable (S : List G) (hS : S ≠ []) (hγS : ∀ g ∈ S, 1 < (m g).val)

-- TODO(paper-gap): On p. 219 the window needs 2 log b′₁ > log |γ₁|. The
-- support enlargement uses γ₁⁻¹, and the final shift must have module below one.

include hS hγS in
/-- Paper: Theorem 4.6.2.1, p. 218. Each isotype has a compact norm-one-stable
support set of module below one. The supported functions surject onto the
difference quotient, and the quotient by the kernel is identified by inclusion.
Deviation: A stable compact support is represented by the preimage of its
compact module window. Its isotype has the inherited topology. -/
theorem modulatedDifferenceProduct_compactSupport_quotient :
    ∃ B : Set ℝ≥0ˣ, IsCompact B ∧ (∀ t ∈ B, t.val < 1) ∧
      let W := (modulatedCompactSupportSubmodule m B).comap (H₀[ω]).subtype
      let R := (P[ω, S]).range
      let M := R.comap W.subtype
      Surjective (R.mkQ ∘ W.subtype) ∧
      ∃ F : (W ⧸ M) ≃L[ℂ] (H₀[ω] ⧸ R),
        ∀ f : W, F (M.mkQ f) = R.mkQ f.val := by sorry

/-! ## 4.6.3 The case of an interval containing zero -/

/-- Paper: Corollary 4.6.3.1, p. 219. On ordinary Schwartz–Bruhat functions
the difference product composes the cyclic differences, retaining repetitions. -/
def schwartzBruhatDifferenceProduct (S : List G) : SchwartzBruhat G →L[ℂ] SchwartzBruhat G :=
  (S.map schwartzBruhatCyclicDifference).prod

/-- Paper: Corollary 4.6.3.1, p. 219. For a repeated generator the ordinary
Schwartz–Bruhat difference product is the second finite difference. -/
theorem schwartzBruhatDifferenceProduct_pair_apply (f : SchwartzBruhat G) (x : G) :
    schwartzBruhatDifferenceProduct [γ, γ] f x =
      f x - 2 * f (γ * x) + f (γ ^ 2 * x) := by sorry

/-- Paper: Corollary 4.6.3.1, pp. 219–220. The ordinary Schwartz–Bruhat
difference product preserves the norm-one isotype. -/
theorem schwartzBruhatDifferenceProduct_mem_isotype :
    ∀ f ∈ actionIsotype ρK ω, schwartzBruhatDifferenceProduct S f ∈ actionIsotype ρK ω :=
  by sorry

variable (I : Set ℝ) (hOpen : IsOpen I) (hInt : OrdConnected I) (h0 : 0 ∈ I)

local notation "V" => ModulatedExponentialDecay m I
local notation "T" => SchwartzBruhat G
local notation "ΔE" => modulatedDifferenceProduct m hm hms univ ordConnected_univ univ_nonempty S
local notation "ΔI" => modulatedDifferenceProduct m hm hms I hInt ⟨0, h0⟩ S
local notation "ΔT" => schwartzBruhatDifferenceProduct S
local notation "j₀" => modulatedExponentialDecayTwist m I ⟨0, h0⟩

-- TODO(paper-gap): In (4.6.3.2), the middle denominator must be P_S S_I(G).
-- The injection into P_γ E / P_S E has source E / P_{S₀} E.
-- The closedness argument needs higher moments at repeated frequencies.

include hS hγS hOpen in
/-- Paper: Corollary 4.6.3.1, pp. 219–220. The two canonical inclusions
induce topological linear isomorphisms of the difference quotients.
Each isomorphism carries the image of a norm-one isotype onto the image
of the same isotype in its target quotient. -/
theorem modulatedDifferenceProduct_quotient_equivs :
    let R₀ := (ΔE).toLinearMap.range
    let R₁ := (ΔI).toLinearMap.range
    let R₂ := (ΔT).toLinearMap.range
    ∃ (i : E →L[ℂ] V) (F : (E ⧸ R₀) ≃L[ℂ] (V ⧸ R₁))
      (J : (V ⧸ R₁) ≃L[ℂ] (T ⧸ R₂)),
      (∀ (f : E) (x : G), (i f).val x = f.val x) ∧
      (∀ f : E, F (R₀.mkQ f) = R₁.mkQ (i f)) ∧
      (∀ f : V, J (R₁.mkQ f) = R₂.mkQ (j₀ f)) ∧
      ∀ η : PontryaginDual m.toMonoidHom.ker,
        let H₁ := modulatedDecayIsotype m I h0 η
        let H₂ := actionIsotype ρK η
        F '' (R₀.mkQ '' (H₀[η] : Set E)) = R₁.mkQ '' (H₁ : Set V) ∧
          J '' (R₁.mkQ '' (H₁ : Set V)) = R₂.mkQ '' (H₂ : Set T) := by sorry

include hm hms hS hγS in
/-- Paper: Corollary 4.6.3.1, p. 220. The ordinary product range is closed.
The two equivalences in (4.6.3.1) therefore identify Hausdorff quotients. -/
theorem schwartzBruhatDifferenceProduct_isClosed_range :
    IsClosed ((ΔT).range : Set (SchwartzBruhat G)) := by sorry

include hS hγS hOpen in
/-- Paper: Corollary 4.6.3.1, pp. 219–220. On each norm-one isotype the
canonical inclusions identify the quotients by differences of isotypic functions. -/
theorem modulatedIsotypicDifferenceProduct_quotient_equivs :
    let H := H₀[ω]
    let H₁ := modulatedDecayIsotype m I h0 ω
    let H₂ := actionIsotype ρK ω
    let R₀ := (H.map (ΔE).toLinearMap).comap H.subtype
    let R₁ := (H₁.map (ΔI).toLinearMap).comap H₁.subtype
    let R₂ := (H₂.map (ΔT).toLinearMap).comap H₂.subtype
    ∃ (F : (H ⧸ R₀) ≃L[ℂ] (H₁ ⧸ R₁)) (J : (H₁ ⧸ R₁) ≃L[ℂ] (H₂ ⧸ R₂)),
      (∀ f : H, ∃ g : H₁, (∀ x, g.val.val x = f.val.val x) ∧ F (R₀.mkQ f) = R₁.mkQ g) ∧
      ∀ g : H₁, ∃ h : H₂, (∀ x, h.val x = g.val.val x) ∧ J (R₁.mkQ g) = R₂.mkQ h := by sorry

end RiemannMasullo
