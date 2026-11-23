module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec2

import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongBidual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec6
import RiemannMasullo.Ch03_IdelicZeta.Sec4
import RiemannMasullo.Ch02_AdelicTheta.Sec3
import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
import RiemannMasullo.Ch06_LocalGlobal.Sec3

import all RiemannMasullo.Ch03_IdelicZeta.Sec3
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec1

/-! # §7.3.1 Orbital Schauder bases

The set of places in the Lean notation lists the finite places. All archimedean places
are included in the definition of the S-adeles.
-/

@[expose] public noncomputable section

open Asymptotics Filter Function IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 600000
set_option Elab.async false

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "Jₛ" => SIdeleQuotient F S
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "J₁" => (mₛ).ker
local notation "Xₛ" => QuasiCharacter Jₛ
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "twistₛ" => quasiCharacterNormTwist (G := Jₛ) mₛ
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "dualₛ" => dualQuasiCharacter (G := Jₛ) mₛ
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "chart(" χ ")" => twistₛ ((circleToComplex).comp (χ))
local notation "onComponent(" c ", " ω ")" =>
  (normOneRestriction mₛ c = (circleToComplex).comp ω)
local notation "Θₛ(" ω ")" => SLocalHomogeneousThetaSpace F S ω
local notation "Kₛ(" ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)
local notation "PV(" places ", " hT ", " ω ")" =>
  (sLocalHomogeneousThetaPrincipalValue (F := F) (S := S) (T := places) hT ω).range
local notation "PicTrivial" => Subsingleton (CommRing.Pic ((S : Set V).integer F))

/-- Paper: Situation 7.3.1.1(1), p. 340.
A finite set of places is saturated if it contains the entire fiber over every
rational prime that occurs below a member. -/
def IsSaturatedPlaceSet (S : Finset V) : Prop :=
  ∀ ⦃v w : V⦄, v ∈ S → w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S

/-- Paper: Situation 7.3.1.1(1), p. 340.
The empty set of finite places is saturated. -/
theorem isSaturatedPlaceSet_empty : IsSaturatedPlaceSet (∅ : Finset V) := by
  intro v w hv _
  exact absurd hv (Finset.notMem_empty v)

open Classical in
/-- Paper: Situation 7.3.1.1(2), p. 340.
The primary part of S at p consists of its places lying over p.
Deviation: A rational prime is represented by its place in the ring of integers of ℚ. -/
def sLocalPrimaryPlaces (S : Finset V) (p : Vℚ) : Finset V :=
  S.filter fun v ↦ v.under (𝓞 ℚ) = p

/-- Paper: Situation 7.3.1.1(2), p. 340.
A place belongs to the primary part exactly when it belongs to S and lies over p. -/
theorem mem_sLocalPrimaryPlaces (p : Vℚ) (v : V) :
    v ∈ sLocalPrimaryPlaces S p ↔ v ∈ S ∧ v.under (𝓞 ℚ) = p := by
  simp [sLocalPrimaryPlaces]

/-- Paper: Situation 7.3.1.1(2), p. 340.
The primary part is a subset of the selected finite places. -/
theorem sLocalPrimaryPlaces_subset (S : Finset V) (p : Vℚ) :
    sLocalPrimaryPlaces S p ⊆ S := by
  intro v hv
  exact ((mem_sLocalPrimaryPlaces p v).1 hv).1

/-- Paper: Situation 7.3.1.1(1)–(2), p. 340.
If S is saturated and its primary part at p is nonempty, that part contains every place over p. -/
theorem mem_sLocalPrimaryPlaces_of_saturated (p : Vℚ) (_hS : IsSaturatedPlaceSet S)
    (_hp : (sLocalPrimaryPlaces S p).Nonempty) (v : V) :
    v ∈ sLocalPrimaryPlaces S p ↔ v.under (𝓞 ℚ) = p := by
  rw [mem_sLocalPrimaryPlaces]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  obtain ⟨w, hw⟩ := _hp
  rw [mem_sLocalPrimaryPlaces] at hw
  exact _hS hw.1 (h.trans hw.2.symm)

-- The unitary lifts in Situation 7.3.1.1(3) use the norm-twist chart of §3.3 and §5.4.
-- TODO(paper-gap): Theorem 7.3.1.2 specifies that S₀ contains the archimedean places,
-- but the principal-value operator of §5.3 and the introduction on p. 340 use finite places.
-- Its proof also replaces m_S - m_{S₀} by m_{S₀} in the coefficient cutoff.

/-- Paper: Theorem 7.3.1.2, p. 341.
The indices consist of a center on the chosen component and a zero-based offset among the
highest coefficients removed by the selected finite principal values.
Deviation: The offset r selects the printed coefficient of pole order m_S(c) - r. -/
def SLocalOrbitalIndex (T : Finset V) (ω : PontryaginDual J₁) :=
  {j : Xₛ × ℕ // onComponent(j.1, ω) ∧ j.2 < sLocalFinitePoleMultiplicity T j.1}

local notation "I(" T ", " ω ")" => SLocalOrbitalIndex (F := F) (S := S) T ω

/-- Paper: Theorem 7.3.1.2, p. 341.
At the trivial character the admissible offsets are precisely those below the number
of selected finite places. -/
theorem sLocalOrbitalIndex_one_iff {T : Finset V} (_hT : T ⊆ S) (r : ℕ) :
    (∃ j : I(T, (1 : PontryaginDual J₁)), j.val = (1, r)) ↔ r < T.card := by
  have h1 : onComponent((1 : Xₛ), (1 : PontryaginDual J₁)) := by
    ext x
    simp [normOneRestriction]
    exact (map_one Circle.coeHom).symm
  have hm := sLocalFinitePoleMultiplicity_one (F := F) (S := S) T _hT
  constructor
  · rintro ⟨j, hj⟩
    have := j.property.2
    rw [hj] at this
    simpa [hm] using this
  · intro h
    exact ⟨⟨(1, r), h1, by simpa [hm] using h⟩, rfl⟩

/-- Paper: Theorem 7.3.1.2, p. 341.
The indexed functional is the selected Laurent coefficient on homogeneous theta classes. -/
def sLocalOrbitalPrincipalPart {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) : StrongDual ℂ (Θₛ(ω)) :=
  sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1
    (sLocalRhoPoleOrder j.val.1 - j.val.2)

/-- Paper: Theorem 7.3.1.2, p. 341.
Offset zero gives the coefficient of the highest allowed pole order on a test. -/
theorem sLocalOrbitalPrincipalPart_mk_top {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) (_hj : j.val.2 = 0) (f : ℬₛ) :
    sLocalOrbitalPrincipalPart j ((Kₛ(ω)).mkQL f) =
      sLocalZLaurentCoeff f j.val.1 (-(sLocalRhoPoleOrder j.val.1 : ℤ)) := by
  unfold sLocalOrbitalPrincipalPart
  rw [sLocalThetaPrincipalPartCoeff_mk]
  simp [_hj]

private theorem sLocalOrbitalPrincipalPart_range_le_ker_chart (c : Xₛ) :
    ∃ (χ : PontryaginDual Jₛ) (s : ℂ), ∀ z : ℂ, twistₛ c z = chart(χ) (s + z) := by
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  have hp := isProperMap_sIdeleQuotientNorm F S
  have hne : ∃ g, mₛ g ≠ 1 := by
    obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    exact ⟨τ t, (hτ t).trans_ne ht⟩
  let a := quasiCharacterAbscissa mₛ hp hne c
  let d := twistₛ c (-(a : ℂ))
  have hrad (g : Jₛ) : (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ (a : ℂ) = (‖c g‖ : ℂ) := by
    rw [← Complex.ofReal_cpow (NNReal.coe_nonneg _) a,
      norm_quasiCharacter_eq_rpow_abscissa mₛ hp hne]
  have hd (g : Jₛ) : d g = c g / (‖c g‖ : ℂ) := by
    change c g * _ ^ (-(a : ℂ)) = _
    rw [Complex.cpow_neg, hrad, div_eq_mul_inv]
  have hn (g : Jₛ) : ‖c g‖ ≠ 0 := norm_ne_zero_iff.mpr ((Group.isUnit g).map c).ne_zero
  let χ : PontryaginDual Jₛ :=
    { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (by
        rw [hd, norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self (hn g)])⟩
      map_one' := Subtype.ext d.map_one
      map_mul' x y := Subtype.ext (d.map_mul x y)
      continuous_toFun := d.continuous.subtype_mk _ }
  refine ⟨χ, (a : ℂ), fun z ↦ ContinuousMonoidHom.ext fun g ↦ ?_⟩
  have hN : (((mₛ g : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (mₛ g).ne_zero)
  change c g * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ z =
    d g * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ ((a : ℂ) + z)
  rw [hd, Complex.cpow_add _ _ hN, hrad, ← mul_assoc, div_mul_cancel₀ _
    (Complex.ofReal_ne_zero.mpr (hn g))]

private theorem sLocalOrbitalPrincipalPart_range_le_ker_restrict (v : S) (c : Xₛ) (z : ℂ)
    (x : (v.val.adicCompletion F)ˣ) :
    sLocalFiniteRestriction v (twistₛ c z) x =
      sLocalFiniteRestriction v c x * (((‖(x : v.val.adicCompletion F)‖ : ℝ) : ℂ)) ^ z := by
  have h := sLocalFiniteRestriction_norm (F := F) (S := S) v x
  have e : ∀ (d : Xₛ) (w : ℂ), sLocalFiniteRestriction v (twistₛ d w) x =
      sLocalFiniteRestriction v d x * (sLocalFiniteRestriction v (chart(1) 1) x) ^ w := by
    intro d w
    obtain ⟨φ, hφ⟩ : ∃ φ : Jₛ, ∀ d : Xₛ, sLocalFiniteRestriction v d x = d φ :=
      ⟨_, fun d ↦ rfl⟩
    rw [hφ, hφ, hφ]
    change d φ * (((mₛ φ : ℝ≥0) : ℝ) : ℂ) ^ w = d φ * (((1 : PontryaginDual Jₛ) φ : Circle) *
      (((mₛ φ : ℝ≥0) : ℝ) : ℂ) ^ (1 : ℂ)) ^ w
    rw [Complex.cpow_one, PontryaginDual.one_apply, Circle.coe_one, one_mul]
  rw [e]
  congr 2


private theorem sLocalOrbitalPrincipalPart_range_le_ker_euler (v : S) (c : Xₛ) :
    AnalyticAt ℂ (fun z ↦
      (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹) 0 := by
  classical
  let ι := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom
  have hunit (z : ℂ) (u : (v.val.adicCompletionIntegers F)ˣ) :
      sLocalFiniteRestriction v (twistₛ c z) (ι u) = sLocalFiniteRestriction v c (ι u) := by
    rw [sLocalOrbitalPrincipalPart_range_le_ker_restrict]
    have hu : ‖((ι u : (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F)‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
          (a := ι u)).mp ⟨u.val.property, u.inv.property⟩)
    rw [hu, Complex.ofReal_one, Complex.one_cpow, mul_one]
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : (v.val.adicCompletion F)ˣ, ∀ d : QuasiCharacter (v.val.adicCompletion F)ˣ,
      finiteLocalEulerFactor v.val d = if (∀ u, d (ι u) = 1) then (1 - d ϖ)⁻¹ else 1 :=
    ⟨_, fun d ↦ rfl⟩
  have key (z : ℂ) : (∀ u, sLocalFiniteRestriction v (twistₛ c z) (ι u) = 1) ↔
      (∀ u, sLocalFiniteRestriction v c (ι u) = 1) :=
    forall_congr' fun u ↦ by rw [hunit z u]
  by_cases hu : ∀ u, sLocalFiniteRestriction v c (ι u) = 1
  · have hfun : (fun z ↦ (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹) =
        fun z ↦ 1 - sLocalFiniteRestriction v c ϖ *
          (((‖(ϖ : v.val.adicCompletion F)‖ : ℝ) : ℂ)) ^ z := by
      funext z
      rw [hϖ, ite_cond_eq_true _ _ (eq_true ((key z).mpr hu)), inv_inv,
        sLocalOrbitalPrincipalPart_range_le_ker_restrict]
    rw [hfun]
    have hne : (((‖(ϖ : v.val.adicCompletion F)‖ : ℝ) : ℂ)) ≠ 0 := by
      rw [Complex.ofReal_ne_zero, norm_ne_zero_iff]; exact ϖ.ne_zero
    simp_rw [Complex.cpow_def_of_ne_zero hne]
    fun_prop
  · have hfun : (fun z ↦ (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹) =
        fun _ ↦ 1 := by
      funext z
      rw [hϖ, ite_cond_eq_false _ _ (eq_false (fun h ↦ hu ((key z).mp h))), inv_one]
    rw [hfun]
    exact analyticAt_const

private theorem sLocalOrbitalPrincipalPart_range_le_ker_neg (o : WithTop ℤ) (h : o < 0) :
    1 ≤ -o := by
  induction o using WithTop.recTopCoe with
  | top => exact absurd h (by simp)
  | coe m =>
    have hm : m < 0 := by exact_mod_cast h
    have : ((-m : ℤ) : WithTop ℤ) = -(m : WithTop ℤ) := rfl
    rw [← this]
    exact_mod_cast (by omega : (1 : ℤ) ≤ -m)

open Classical in
private theorem sLocalOrbitalPrincipalPart_range_le_ker_prod (T : Finset V) (c : Xₛ) :
    MeromorphicAt (fun z : ℂ ↦ ∏ v : S, if v.val ∈ T then
        (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹ else 1) 0 ∧
      ((sLocalFinitePoleMultiplicity T c : ℕ) : WithTop ℤ) ≤ meromorphicOrderAt
        (fun z : ℂ ↦ ∏ v : S, if v.val ∈ T then
          (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹ else 1) 0 := by
  let E : S → ℂ → ℂ := fun v z ↦ finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z))
  let g : S → ℂ → ℂ := fun v z ↦ if v.val ∈ T then (E v z)⁻¹ else 1
  have hg (v : S) : AnalyticAt ℂ (g v) 0 := by
    by_cases hv : v.val ∈ T
    · simp only [g, hv, ite_true]; exact sLocalOrbitalPrincipalPart_range_le_ker_euler v c
    · simp only [g, hv, ite_false]; exact analyticAt_const
  have hQ : (fun z : ℂ ↦ ∏ v : S, if v.val ∈ T then
      (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹ else 1) =
      ∏ v : S, g v := by
    funext z; simp only [Finset.prod_apply, g, E]
  rw [hQ]
  refine ⟨MeromorphicAt.prod fun v _ ↦ (hg v).meromorphicAt, ?_⟩
  rw [meromorphicOrderAt_prod fun v _ ↦ (hg v).meromorphicAt]
  unfold sLocalFinitePoleMultiplicity sLocalFinitePolePlaces
  rw [Finset.filter_filter, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_le_sum fun v _ ↦ ?_
  split_ifs with h
  · have hv : g v = (E v)⁻¹ := by funext z; simp only [g, h.2, ite_true, Pi.inv_apply]
    rw [hv, meromorphicOrderAt_inv, Nat.cast_one]
    exact sLocalOrbitalPrincipalPart_range_le_ker_neg _ h.1
  · rw [Nat.cast_zero]; exact (hg v).meromorphicOrderAt_nonneg


private theorem sLocalOrbitalPrincipalPart_range_le_ker_zeta (f : ℬₛ) (χ : PontryaginDual Jₛ)
    (s : ℂ) (c : Xₛ)
    (hc : ∀ z, twistₛ c z = chart(χ) (s + z)) :
    MeromorphicAt (fun z ↦ sLocalIdelicZFunction f (twistₛ c z)) 0 ∧
      ((-(sLocalRhoPoleOrder c : ℤ) : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction f (twistₛ c z)) 0 := by
  have hb := sLocalIdelicOrderBound_eq_neg_poleOrder (F := F) (S := S) c
  rw [← hb]
  unfold sLocalIdelicOrderBound
  simp only [hc]
  refine ⟨?_, ?_⟩
  · exact (((sLocalIdelicZFunction_meromorphic f χ).meromorphicOn (s + 0) trivial)).comp_analyticAt
      (g := fun t ↦ s + t) (by fun_prop)
  · have h := sLocalIdelicZFunction_poles f χ s
    have e1 := meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (x := (0 : ℂ)) (c := s)
      (f := fun w ↦ sLocalRhoFactor (chart(χ) w))
    have e2 := meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (x := (0 : ℂ)) (c := s)
      (f := fun w ↦ sLocalIdelicZFunction f (chart(χ) w))
    rw [zero_add] at e1 e2
    simp only [add_comm s]
    rw [e1, e2]
    exact h


open Classical in
private theorem sLocalOrbitalPrincipalPart_range_le_ker_polar {T : Finset V} (hT : T ⊆ S)
    (f : ℬₛ) (c : Xₛ) :
    sLocalPolarMultiplicity (sAdelePrincipalValue F hT f) c ≤
      sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity T c := by
  let g := sAdelePrincipalValue F hT f
  obtain ⟨χ, s, hc⟩ := sLocalOrbitalPrincipalPart_range_le_ker_chart c
  obtain ⟨hZm, hZo⟩ := sLocalOrbitalPrincipalPart_range_le_ker_zeta f χ s c hc
  obtain ⟨hQm, hQo⟩ := sLocalOrbitalPrincipalPart_range_le_ker_prod T c
  have ht : Tendsto (fun z : ℂ ↦ s + z) (𝓝[≠] 0) (𝓝[≠] s) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_const.add continuous_id : Continuous fun z : ℂ ↦ s + z).tendsto'
        (0 : ℂ) s (add_zero s)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact fun h ↦ hz (add_eq_left.mp h)
  have hev : (fun z ↦ sLocalIdelicZFunction g (twistₛ c z)) =ᶠ[𝓝[≠] 0]
      (fun z ↦ sLocalIdelicZFunction f (twistₛ c z)) * (fun z : ℂ ↦ ∏ v : S, if v.val ∈ T then
        (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹ else 1) := by
    have h1 := nhdsNE_le_codiscrete s (sLocalIdelicZFunction_principalValue T hT f χ)
    filter_upwards [ht.eventually h1] with z hz
    try simp only at hz
    simp only [Pi.mul_apply, hc z]
    rw [hz, div_eq_mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    split_ifs <;> simp
  have hord : (((sLocalFinitePoleMultiplicity T c : ℤ) - sLocalRhoPoleOrder c : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction g (twistₛ c z)) 0 := by
    rw [meromorphicOrderAt_congr hev, meromorphicOrderAt_mul hZm hQm]
    have e2 : (((sLocalFinitePoleMultiplicity T c : ℤ) - sLocalRhoPoleOrder c : ℤ) : WithTop ℤ) =
        ((-(sLocalRhoPoleOrder c : ℤ) : ℤ) : WithTop ℤ) +
          ((sLocalFinitePoleMultiplicity T c : ℕ) : WithTop ℤ) := by
      rw [show ((sLocalFinitePoleMultiplicity T c : ℕ) : WithTop ℤ) =
        (((sLocalFinitePoleMultiplicity T c : ℕ) : ℤ) : WithTop ℤ) from rfl, ← WithTop.coe_add]
      congr 1
      ring
    rw [e2]
    exact add_le_add hZo hQo
  unfold sLocalPolarMultiplicity
  generalize meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction g (twistₛ c z)) 0 = o at hord ⊢
  induction o using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    have : (sLocalFinitePoleMultiplicity T c : ℤ) - sLocalRhoPoleOrder c ≤ n := by
      exact_mod_cast hord
    simp only [WithTop.untop₀_coe]
    omega

open Classical in
private theorem sLocalOrbitalPrincipalPart_range_le_ker_core {T : Finset V} (hT : T ⊆ S)
    (f : ℬₛ) (c : Xₛ) (r : ℕ)
    (hr' : r < sLocalFinitePoleMultiplicity T c) :
    sLocalZLaurentCoeff (sAdelePrincipalValue F hT f) c
      (-((sLocalRhoPoleOrder c - r : ℕ) : ℤ)) = 0 := by
  let g := sAdelePrincipalValue F hT f
  have hmult : sLocalFinitePoleMultiplicity T c ≤ sLocalRhoPoleOrder c := by
    rw [sLocalRhoPoleOrder_eq_card_polePlaces]
    unfold sLocalFinitePoleMultiplicity
    exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
  have hk : 0 < sLocalRhoPoleOrder c - r := by omega
  by_contra hne
  have hpole := (sLocalPrincipalPartCoeff_ne_zero_imp_pole c (sLocalRhoPoleOrder c - r) hk g
    (by rwa [sLocalPrincipalPartCoeff_apply])).2
  have hpm : sLocalPolarMultiplicity g c ≤
      sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity T c :=
    sLocalOrbitalPrincipalPart_range_le_ker_polar hT f c
  omega

private theorem sLocalOrbitalPrincipalPart_range_le_ker_range {M Q : Type*} [AddCommGroup M]
    [Module ℂ M] [AddCommGroup Q]
    [Module ℂ Q] [TopologicalSpace Q] (π : M →ₗ[ℂ] Q) (hπ : Function.Surjective π)
    (L : Q →ₗ[ℂ] Q) (φ : Q →L[ℂ] ℂ) (h : ∀ f, φ (L (π f)) = 0) :
    LinearMap.range L ≤ LinearMap.ker (φ : Q →ₗ[ℂ] ℂ) := by
  rintro x ⟨y, rfl⟩
  obtain ⟨f, rfl⟩ := hπ y
  exact h f

open Classical in
private theorem sLocalOrbitalPrincipalPart_range_le_ker_test {T : Finset V} (hT : T ⊆ S)
    (ω : PontryaginDual J₁) (j : I(T, ω)) (f : ℬₛ) :
    sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) j
      (sLocalHomogeneousThetaPrincipalValue hT ω ((Kₛ(ω)).mkQ f)) = 0 := by
  have e1 : sLocalHomogeneousThetaPrincipalValue hT ω ((Kₛ(ω)).mkQ f) =
      (Kₛ(ω)).mkQL (sAdelePrincipalValue F hT f) :=
    sLocalHomogeneousThetaPrincipalValue_mk hT ω f
  have e2 : sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) j
      ((Kₛ(ω)).mkQL (sAdelePrincipalValue F hT f)) =
      sLocalZLaurentCoeff (sAdelePrincipalValue F hT f) j.val.1
        (-((sLocalRhoPoleOrder j.val.1 - j.val.2 : ℕ) : ℤ)) :=
    sLocalThetaPrincipalPartCoeff_mk ω j.val.1 j.property.1 (sLocalRhoPoleOrder j.val.1 - j.val.2)
      (sAdelePrincipalValue F hT f)
  have e3 := sLocalOrbitalPrincipalPart_range_le_ker_core hT f j.val.1 j.val.2 j.property.2
  exact (congrArg _ e1).trans (e2.trans e3)

-- TODO(paper-gap): Theorem 7.2.1.1(4) describes a pole-bound subspace. The reverse
-- inclusion below requires division by the selected reciprocal Euler factors in the
-- componentwise Mellin image. Proposition 7.2.2.1 assumes unramifiedness outside T.
/-- Paper: Theorem 7.3.1.2(1), p. 341.
Every homogeneous theta class whose zeta transform obeys the remaining pole bound
on the component lies in the image of the finite principal value.
Deviation: The selected places are finite, as in Definition 5.3.1.4. This is the
reverse inclusion of `sLocalOrbitalPrincipalValue_eq_poleBound`. -/
theorem sLocalThetaPoleBound_le_orbitalPrincipalValue {T : Finset V} (hT : T ⊆ S)
    (_hne : T.Nonempty) (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial)
    (ω : PontryaginDual J₁) :
    sLocalThetaPoleBound ω (fun c ↦ sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity T c) ≤
      PV(T, hT, ω) := by sorry

/-- The principal-value range lies in the pole-bound subspace: on the component, the
zeta transform of a principal value has the selected Euler poles removed. -/
private theorem sLocalOrbitalPrincipalValue_eq_poleBound_le {T : Finset V} (hT : T ⊆ S)
    (ω : PontryaginDual J₁) :
    PV(T, hT, ω) ≤ sLocalThetaPoleBound ω
      (fun c ↦ sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity T c) := by
  rintro x ⟨y, rfl⟩
  obtain ⟨f, rfl⟩ := (Kₛ(ω)).mkQ_surjective y
  exact Submodule.subset_span ⟨sAdelePrincipalValue F hT f,
    (sLocalHomogeneousThetaPrincipalValue_mk hT ω f).symm,
    fun c _ ↦ sLocalOrbitalPrincipalPart_range_le_ker_polar hT f c⟩

/-- Paper: Theorem 7.3.1.2(1), p. 341.
The principal-value range is the pole-bound subspace with the remaining multiplicity.
Deviation: The selected places are finite, as in Definition 5.3.1.4. -/
theorem sLocalOrbitalPrincipalValue_eq_poleBound {T : Finset V} (hT : T ⊆ S) (_hne : T.Nonempty)
    (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial) (ω : PontryaginDual J₁) :
    PV(T, hT, ω) = sLocalThetaPoleBound ω
      (fun c ↦ sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity T c) := by
  exact le_antisymm (sLocalOrbitalPrincipalValue_eq_poleBound_le hT ω)
    (sLocalThetaPoleBound_le_orbitalPrincipalValue hT _hne _hS _hPic ω)

/-- Paper: Theorem 7.3.1.2(1), p. 341.
The principal-value image is the common kernel of the selected coefficients on the component.
Deviation: The selection is finite, as in the introduction and the principal-value operator
of §5.3. The cutoff is the one in the theorem statement. -/
theorem mem_sLocalOrbitalPrincipalValue_iff {T : Finset V} (h₀ : T ⊆ S) (_hne : T.Nonempty)
    (_hsat : IsSaturatedPlaceSet S) (_hclass : PicTrivial)
    (χ : PontryaginDual J₁) (x : Θₛ(χ)) :
    x ∈ PV(T, h₀, χ) ↔ ∀ j : I(T, χ),
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := χ) j x = 0 := by
  classical
  have hb := sLocalThetaRemovedPrincipalParts_ker (F := F) (S := S) χ ∅ T
  simp only [sLocalSelectedPoleMultiplicity_finite] at hb
  rw [sLocalOrbitalPrincipalValue_eq_poleBound h₀ _hne _hsat _hclass χ, ← hb,
    LinearMap.mem_ker]
  have hle (c : Xₛ) : sLocalFinitePoleMultiplicity T c ≤ sLocalRhoPoleOrder c := by
    rw [sLocalRhoPoleOrder_eq_card_polePlaces]
    unfold sLocalFinitePoleMultiplicity
    exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
  constructor
  · intro h j
    have hj := j.property.2
    have hm := hle j.val.1
    let k := sLocalRhoPoleOrder j.val.1 - j.val.2
    exact congrFun h ⟨(j.val.1, k), j.property.1, by
      rw [sLocalSelectedPoleMultiplicity_finite]; dsimp [k]; omega, Nat.sub_le _ _⟩
  · intro h
    funext i
    have hi := i.property.2.1
    rw [sLocalSelectedPoleMultiplicity_finite] at hi
    have hk := i.property.2.2
    let r := sLocalRhoPoleOrder i.val.1 - i.val.2
    have hr : r < sLocalFinitePoleMultiplicity T i.val.1 := by
      dsimp [r]; have := hle i.val.1; omega
    have hj := h ⟨(i.val.1, r), i.property.1, hr⟩
    change sLocalThetaPrincipalPartCoeff χ i.val.1 i.property.1
      (sLocalRhoPoleOrder i.val.1 - r) x = 0 at hj
    change sLocalThetaPrincipalPartCoeff χ i.val.1 i.property.1 i.val.2 x = 0
    rwa [show sLocalRhoPoleOrder i.val.1 - r = i.val.2 by dsimp [r]; omega] at hj

/-- Paper: Theorem 7.3.1.2(1), p. 341.
The finite principal-value image is closed in the homogeneous theta space.
Deviation: Uses the finite-place selection of part (1). -/
theorem sLocalOrbitalPrincipalValue_isClosed {T : Finset V} (hT : T ⊆ S) (_hTne : T.Nonempty)
    (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial) (ω : PontryaginDual J₁) :
    IsClosed (PV(T, hT, ω) : Set (Θₛ(ω))) := by
  exact (sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding (F := F) (S := S) hT ω).isClosed_range

/-- Paper: Theorem 7.3.1.2(2), p. 341.
Every continuous functional vanishing on the finite principal-value image lies in the
closed span of the selected coefficients in the strong dual.
Deviation: Uses the finite-place selection of part (1). This is the nontrivial inclusion
of `sLocalOrbitalPrincipalValue_annihilator`. -/
theorem sLocalOrbitalPrincipalValue_annihilator_le {T : Finset V} (hT : T ⊆ S)
    (_hTne : T.Nonempty) (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial)
    (ω : PontryaginDual J₁) :
    (PV(T, hT, ω)).dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ) ≤
      (Submodule.span ℂ
        (range (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω)))).topologicalClosure := by
  let E := Θₛ(ω)
  have hN : IsNuclearTVS.{0} E := sLocalHomogeneousThetaSpace_nuclear (F := F) (S := S) ω
  let : T2Space E := hN.1
  let : PolynormableSpace ℂ E := hN.2.1
  let : MontelSpace ℂ E := (sLocalHomogeneousThetaSpace_montel (F := F) (S := S) ω).2
  apply le_of_eq
  apply strongDual_annihilator_eq_closedSpan_of_kernels
  intro x
  simpa only [Set.forall_mem_range] using
    (mem_sLocalOrbitalPrincipalValue_iff (F := F) hT _hTne _hS _hPic ω x)

/-- Each selected coefficient vanishes on the principal-value image. -/
private theorem sLocalOrbitalPrincipalValue_annihilator_ker {T : Finset V} (hT : T ⊆ S)
    (ω : PontryaginDual J₁) (i : I(T, ω)) :
    PV(T, hT, ω) ≤ (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) i).ker :=
  sLocalOrbitalPrincipalPart_range_le_ker_range ((Kₛ(ω)).mkQ) (Submodule.mkQ_surjective _)
    (sLocalHomogeneousThetaPrincipalValue hT ω)
    (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) i)
    (sLocalOrbitalPrincipalPart_range_le_ker_test hT ω i)

/-- The closed span of functionals vanishing on a submodule lies in its annihilator. -/
private theorem sLocalOrbitalPrincipalValue_annihilator_ge {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [ContinuousAdd (StrongDual ℂ E)] [ContinuousConstSMul ℂ (StrongDual ℂ E)]
    (R : Submodule ℂ E) (s : Set (StrongDual ℂ E)) (hs : ∀ φ ∈ s, ∀ x ∈ R, φ x = 0) :
    (Submodule.span ℂ s).topologicalClosure ≤
      R.dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ) := by
  have hset : (R.dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ) : Set (StrongDual ℂ E)) =
      ⋂ x ∈ R, {φ : StrongDual ℂ E | φ x = 0} := by
    ext φ
    simp only [SetLike.mem_coe, Submodule.mem_comap, Submodule.mem_dualAnnihilator,
      Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  refine Submodule.topologicalClosure_minimal _ ?_ ?_
  · rw [Submodule.span_le, hset]
    intro φ hφ
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact hs φ hφ
  · rw [hset]
    exact isClosed_biInter fun x _ ↦ isClosed_eq (continuous_eval_const x) continuous_const

/-- Paper: Theorem 7.3.1.2(2), p. 341.
The annihilator of the finite principal-value image is the closed span of the selected
coefficients in the strong dual.
Deviation: Uses the finite-place selection of part (1). Lower Laurent coefficients can mix
under translations, as in §7.2. -/
theorem sLocalOrbitalPrincipalValue_annihilator {T : Finset V} (hT : T ⊆ S) (_hTne : T.Nonempty)
    (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial) (ω : PontryaginDual J₁) :
    (PV(T, hT, ω)).dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ) =
      (Submodule.span ℂ
        (range (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω)))).topologicalClosure := by
  refine le_antisymm (sLocalOrbitalPrincipalValue_annihilator_le hT _hTne _hS _hPic ω) ?_
  refine sLocalOrbitalPrincipalValue_annihilator_ge _ _ ?_
  rintro _ ⟨i, rfl⟩ x hx
  exact sLocalOrbitalPrincipalValue_annihilator_ker hT ω i hx

open Classical in
/-- Normalize a triangular witness and correct its later offsets at the same center. -/
private theorem sLocalOrbitalPrincipalPart_triangular_dual {E A C : Type*}
    [AddCommGroup E] [Module ℂ E] (center : A → C) (offset : A → ℕ)
    (cutoff : C → ℕ) (φ : A → E →ₗ[ℂ] ℂ)
    (hcut : ∀ i, offset i < cutoff (center i))
    (hinj : ∀ i j, center i = center j → offset i = offset j → i = j)
    (hwitness : ∀ j, ∃ x, φ j x ≠ 0 ∧
      ∀ i, center i ≠ center j ∨ offset i < offset j → φ i x = 0) :
    ∀ j, ∃ x, ∀ i, φ i x = if i = j then 1 else 0 := by
  classical
  let rank (i : A) := cutoff (center i) - offset i
  suffices h : ∀ n : ℕ, ∀ j, rank j = n → ∃ x, ∀ i, φ i x = if i = j then 1 else 0 by
    exact fun j ↦ h (rank j) j rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro j hj
    obtain ⟨x, hx, hzero⟩ := hwitness j
    let y := (φ j x)⁻¹ • x
    have hyj : φ j y = 1 := by simp [y, hx]
    let B := {i : A // center i = center j ∧ offset j < offset i}
    let index (i : B) : Fin (cutoff (center j)) :=
      ⟨offset i.val, by simpa only [i.property.1] using hcut i.val⟩
    let : Fintype B := Fintype.ofInjective index (fun i k h ↦ Subtype.ext
      (hinj i.val k.val (i.property.1.trans k.property.1.symm) (congrArg Fin.val h)))
    have hsmaller (i : B) : rank i.val < n := by
      have hlt := i.property.2
      have hc := hcut i.val
      rw [i.property.1] at hc
      rw [← hj]
      dsimp [rank]
      rw [i.property.1]
      omega
    choose z hz using fun i : B ↦ ih _ (hsmaller i) i.val rfl
    refine ⟨y - ∑ i : B, φ i.val y • z i, fun i ↦ ?_⟩
    simp only [map_sub, map_sum, map_smul, smul_eq_mul, hz, mul_ite, mul_one, mul_zero]
    have hsum : (∑ k : B, if i = k.val then φ k.val y else 0) =
        if center i = center j ∧ offset j < offset i then φ i y else 0 := by
      split_ifs with hi
      · let k : B := ⟨i, hi⟩
        rw [Finset.sum_eq_single k]
        · simp [k]
        · intro b _ hb
          exact ite_eq_right (fun h ↦ hb (Subtype.ext h.symm))
        · exact fun h ↦ (h (Finset.mem_univ k)).elim
      · apply Finset.sum_eq_zero
        intro k _
        apply ite_eq_right
        intro h
        exact hi (by simpa only [h] using k.property)
    rw [hsum]
    by_cases h : i = j
    · subst i
      simp [hyj]
    · rw [ite_eq_right h]
      by_cases hi : center i = center j ∧ offset j < offset i
      · simp [hi]
      · rw [ite_eq_right hi, sub_zero]
        have hz' : center i ≠ center j ∨ offset i < offset j := by
          by_cases hc : center i = center j
          · right
            have he : offset i ≠ offset j := fun h' ↦ h (hinj i j hc h')
            exact lt_of_le_of_ne (le_of_not_gt (fun h' ↦ hi ⟨hc, h'⟩)) he
          · exact Or.inl hc
        simp [y, hzero i hz']

section TriangularPrincipalPartTests

local notation "hmₛ" => (isProperMap_sIdeleQuotientNorm F S).continuous

local notation "Z(" f ", " c ")" => (fun z ↦ sLocalIdelicZFunction f (twistₛ c z))

private theorem sLocalOrbital_centered_order (f : Xₛ → ℂ) (d : Xₛ) (a : ℂ) :
    meromorphicOrderAt (fun z ↦ f (twistₛ (twistₛ d a) z)) 0 =
      meromorphicOrderAt (fun z ↦ f (twistₛ d z)) a := by
  have he : (fun z ↦ f (twistₛ (twistₛ d a) z)) =
      (fun z ↦ f (twistₛ d z)) ∘ (· + a) :=
    funext fun z ↦ congrArg f (normTwist_normTwist mₛ hmₛ d a z)
  rw [he, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add]

private theorem sLocalOrbital_eventually_regular (c : Xₛ) :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), 0 ≤ sLocalIdelicOrderBound (twistₛ c z) := by
  obtain ⟨χ, a, ha⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  have he : (fun z ↦ sLocalRhoFactor (twistₛ c z)) =
      (fun z ↦ sLocalRhoFactor (chart(χ) z)) ∘ (· + a) := by
    funext z
    rw [← ha]
    exact congrArg sLocalRhoFactor (normTwist_normTwist mₛ hmₛ _ a z)
  have hm : MeromorphicAt (fun z ↦ sLocalRhoFactor (twistₛ c z)) 0 := by
    rw [he]
    exact (sLocalRhoFactor_meromorphic χ (0 + a)).comp_analyticAt
      (g := fun z : ℂ ↦ z + a) (by fun_prop)
  filter_upwards [hm.eventually_analyticAt] with z hz
  change 0 ≤ min 0 (meromorphicOrderAt (fun w ↦ sLocalRhoFactor (twistₛ (twistₛ c z) w)) 0)
  rw [sLocalOrbital_centered_order]
  exact le_min le_rfl hz.meromorphicOrderAt_nonneg

/-- The product of the local standard Gaussians is normalized to a nonzero value at the given center. -/
private theorem exists_sLocalGaussian_normalized_ne_zero (c : Xₛ) :
    ∃ f : ℬₛ, sLocalNormalizedZFunction f c ≠ 0 := by
  classical
  obtain ⟨χ, a, rfl⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  let d := twistₛ ((circleToComplex).comp χ) a
  let i (w : InfinitePlace F) : w.Completionˣ →ₜ* Jₛ :=
    let h := sLocalInfiniteInsertion_properties (F := F) (S := S) w
    ⟨{ toFun := _, map_one' := h.1, map_mul' := h.2.1 }, h.2.2⟩
  let χArch (w : InfinitePlace F) := χ.comp (i w)
  have hχ (w : InfinitePlace F) :
      (circleToComplex).comp (χArch w) = sLocalInfiniteRestriction w ((circleToComplex).comp χ) := rfl
  let G (w : InfinitePlace F) := Multiplicative w.Completion
  let (w : InfinitePlace F) : T2Space (G w) := (inferInstance : T2Space w.Completion)
  let (w : InfinitePlace F) : LocallyCompactSpace (G w) := (inferInstance : LocallyCompactSpace w.Completion)
  let (w : InfinitePlace F) : SecondCountableTopology (G w) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  obtain ⟨g, hg⟩ := schwartzBruhat_pi_test G (fun w ↦ infiniteStandardGaussian w (χArch w))
  let e : Multiplicative (InfiniteAdeleRing F) ≃ₜ* ((w : InfinitePlace F) → G w) :=
    { toFun := fun x w ↦ Multiplicative.ofAdd (x.toAdd w)
      invFun := fun x ↦ Multiplicative.ofAdd (fun w ↦ (x w).toAdd)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }
  let : T2Space (Multiplicative (InfiniteAdeleRing F)) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing F)) :=
    e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let a₀ : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) :=
    ⟨g.val ∘ e, schwartzBruhat_mem_comp_equiv e g.property⟩
  let f := sLocalStandardThetaTensor d a₀
  have hf := sLocalNormalizedEigendistribution_gaussian χ a χArch hχ f
    (fun x ↦ (sLocalStandardThetaTensor_apply d a₀ x).trans (congrArg (· * _) (hg (e (Multiplicative.ofAdd x.1)))))
  have he := (existsUnique_sLocalNormalizedEigendistribution d).exists.choose_spec f
  change _ * sLocalNormalizedEigendistribution d f = sLocalNormalizedZFunction f d at he
  change sLocalNormalizedEigendistribution d f = 1 at hf
  refine ⟨f, ?_⟩
  change sLocalNormalizedZFunction f d ≠ 0
  rw [← he, hf, mul_one]
  apply Complex.ofReal_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_ne_zero]
  refine ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top, ENNReal.inv_ne_top.mpr ?_⟩
  refine (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (pow_pos ?_ _))).ne'
  exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v.val).trans' zero_lt_one


/-- A standard local test realizes the full Euler pole at a polar center. -/
private theorem exists_sLocalZeta_full_pole (c : Xₛ) (hc : 0 < sLocalRhoPoleOrder c) :
    ∃ f : ℬₛ, meromorphicOrderAt Z(f,c) 0 =
      ((-(sLocalRhoPoleOrder c : ℤ) : ℤ) : WithTop ℤ) := by
  obtain ⟨f, hf⟩ := exists_sLocalGaussian_normalized_ne_zero c
  refine ⟨f, ?_⟩
  obtain ⟨χ, a, ha⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  let L : ℂ → ℂ := fun z ↦ sLocalHeckeL (twistₛ c z)
  have hLbound : min 0 (meromorphicOrderAt L 0) =
      ((-(sLocalRhoPoleOrder c : ℤ) : ℤ) : WithTop ℤ) := by
    have he : min 0 (meromorphicOrderAt L 0) = sLocalIdelicOrderBound c := by
      dsimp only [L]
      unfold sLocalIdelicOrderBound
      rw [← ha, sLocalOrbital_centered_order, sLocalOrbital_centered_order]
      exact sLocalHeckeL_poleOrder_eq (F := F) S χ a
    exact he.trans (sLocalIdelicOrderBound_eq_neg_poleOrder c)
  have hlt : min 0 (meromorphicOrderAt L 0) < 0 := by
    rw [hLbound]
    exact_mod_cast (show -(sLocalRhoPoleOrder c : ℤ) < 0 by omega)
  have hLo : meromorphicOrderAt L 0 = ((-(sLocalRhoPoleOrder c : ℤ) : ℤ) : WithTop ℤ) :=
    (min_eq_right ((min_lt_iff.mp hlt).resolve_left (lt_irrefl _)).le).symm.trans hLbound
  let N := Z(f,c) / L
  change toMeromorphicNFOn N univ 0 ≠ 0 at hf
  have hN : MeromorphicOn N univ := by
    by_contra h
    exact hf (congrFun (toMeromorphicNFOn_of_not_meromorphicOn h) 0)
  have hNo : meromorphicOrderAt N 0 = 0 := by
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hN (mem_univ _)] at hf
    exact ((hN 0 trivial).meromorphicOrderAt_eq_zero_iff_toMeromorphicNFAt_ne_zero).mpr hf
  have hLm := meromorphicAt_of_meromorphicOrderAt_ne_zero
    (((min_lt_iff.mp hlt).resolve_left (lt_irrefl _)).ne)
  have hNZ : Z(f,c) =ᶠ[𝓝[≠] (0 : ℂ)] N * L := by
    filter_upwards [(meromorphicOrderAt_ne_top_iff_eventually_ne_zero hLm).mp
      (hLo.trans_ne WithTop.coe_ne_top)] with z hz
    exact (div_mul_cancel₀ _ hz).symm
  rw [meromorphicOrderAt_congr hNZ, meromorphicOrderAt_mul (hN 0 trivial) hLm, hNo, zero_add, hLo]

section CompactNormAverage

open Bornology Function MeasureTheory

private theorem exists_intervalAverage {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [T2Space E] [ContinuousSMul ℂ E]
    [LocallyConvexSpace ℝ E] [QuasiCompleteSpace ℂ E] (f : ℝ → E) (hf : Continuous f) :
    ∃ v : E, ∀ ℓ : StrongDual ℂ E, ℓ v = ∫ t in (0 : ℝ)..1, ℓ (f t) := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  have : IsFiniteMeasure μ := ⟨by
    change volume.restrict (Ioc (0 : ℝ) 1) univ < ⊤
    simp⟩
  have hμ : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1 :=
    (ae_restrict_mem measurableSet_Ioc).mono fun _ hx ↦ Ioc_subset_Icc_self hx
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  have hi : PettisWeaklyIntegrable (.positive μ) f := by
    intro ℓ
    have h := ℓ.continuous.comp hf
    obtain ⟨r, hr⟩ := isCompact_Icc.exists_bound_of_continuousOn h.continuousOn
    exact (integrable_const (μ := μ) r).mono' h.aestronglyMeasurable (hμ.mono hr)
  let C := closure (convexHull ℝ (insert 0 (f '' Icc (0 : ℝ) 1)))
  have hc : IsCompact (insert 0 (f '' Icc (0 : ℝ) 1)) := (isCompact_Icc.image hf).insert 0
  have hC : IsCompact C :=
    isCompact_closure_of_totallyBounded_quasiComplete (𝕜 := ℂ) hc.totallyBounded.convexHull
  obtain ⟨v, -, _, he⟩ := exists_hasPettisIntegral_mem_smul_of_isCompact_convex μ hi hC
    (convex_convexHull ..).closure (subset_closure (subset_convexHull _ _ (mem_insert _ _)))
    (hμ.mono fun x hx ↦ subset_closure (subset_convexHull _ _ (mem_insert_of_mem _ ⟨x, hx, rfl⟩)))
  refine ⟨v, fun ℓ ↦ ?_⟩
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact congrArg (fun z : PettisWeakCompletion E ↦
    (show Module.Dual ℂ (StrongDual ℂ E) from z) ℓ) he

private theorem exists_sLocalUnitOrbitAverage (u : ℝ → (SAdeleRing F S)ˣ) (hu : Continuous u)
    (w : ℝ → ℂ) (hw : Continuous w) (f : ℬₛ) :
    ∃ v : ℬₛ, ∀ ℓ : StrongDual ℂ ℬₛ,
      ℓ v = ∫ t in (0 : ℝ)..1, w t * ℓ (schwartzBruhatUnitTranslate (u t) f) := by
  let : T2Space ℬₛ := (sAdeleSchwartz_nuclear.{_,0} F S).1
  let : PolynormableSpace ℂ ℬₛ := (sAdeleSchwartz_nuclear.{_,0} F S).2.1
  let : LocallyConvexSpace ℝ ℬₛ := (PolynormableSpace.withSeminorms ℂ ℬₛ).toLocallyConvexSpace
  let : CompleteSpace ℬₛ := sAdeleSchwartz_complete F S
  have h : Continuous fun t ↦ schwartzBruhatUnitTranslate (u t) f :=
    continuous_sAdeleSchwartz_unitTranslate.comp (hu.prodMk continuous_const)
  obtain ⟨v, hv⟩ := exists_intervalAverage _ (hw.smul h)
  exact ⟨v, fun ℓ ↦ by simpa only [Pi.smul_apply', map_smul, smul_eq_mul, RingHom.id_apply] using hv ℓ⟩

private theorem exists_sLocalLogNormSection :
    ∃ u : ℝ → (SAdeleRing F S)ˣ, Continuous u ∧ ∀ t, ((sIdeleNorm F S (u t)).val : ℝ) = Real.exp t := by
  let σ := (Units.map (adeleProjection F S).toMonoidHom).comp (canonicalIdeleNormSection F)
  let r (t : ℝ) := (Nonneg.unitsHomeomorphPos ℝ).symm (Real.expOrderIso t)
  have hr : Continuous r := (Nonneg.unitsHomeomorphPos ℝ).symm.continuous.comp Real.expOrderIso.continuous
  have hp : Continuous (Units.map (adeleProjection F S).toMonoidHom) :=
    (continuous_fst.prodMk (continuous_pi fun v : S ↦
      (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  refine ⟨fun t ↦ σ (r t), hp.comp ((canonicalIdeleNormSection_continuous F).comp hr), ?_⟩
  intro t
  rw [show sIdeleNorm F S (σ (r t)) = r t from sIdeleNorm_project_canonicalSection F S _]
  rfl

private theorem intervalAverage_exp_neg (c : ℂ) (hc : c ≠ 0) :
    (∫ t in (0 : ℝ)..1, Complex.exp (-c * t)) = (1 - Complex.exp (-c)) / c := by
  rw [integral_exp_mul_complex (neg_ne_zero.mpr hc)]
  simp
  ring

private theorem exists_sLocalRegularEval (c : Xₛ) (hc : 0 ≤ sLocalIdelicOrderBound c) :
    ∃ ℓ : StrongDual ℂ ℬₛ, ∀ f, ℓ f = sLocalIdelicZFunction f c := by
  let d : {c : Xₛ // 0 ≤ sLocalIdelicOrderBound c} := ⟨c, hc⟩
  let M := (Submodule.subtype _).comp (sLocalIdelicMellin (F := F) (S := S))
  let ℓ : ℬₛ →ₗ[ℂ] ℂ := (ContinuousMap.evalCLM ℂ d).toLinearMap.comp M
  refine ⟨⟨ℓ, ?_⟩, fun _ ↦ rfl⟩
  exact (ContinuousMap.evalCLM ℂ d).continuous.comp sLocalIdelicMellin_continuous.subtype_val

private theorem sLocalLogSection_twist (c₀ : Xₛ) (g : (SAdeleRing F S)ˣ) (z : ℂ) (r : ℝ)
    (hr : ((sIdeleNorm F S g).val : ℝ) = Real.exp r) :
    (twistₛ c₀ z) (QuotientGroup.mk g) =
      c₀ (QuotientGroup.mk g) * Complex.exp ((r : ℂ) * z) := by
  change c₀ _ * (((((sIdeleNorm F S g).val : ℝ) : ℂ)) ^ z) = _
  rw [hr, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]

private theorem sLocalRegularEval_translate (c : Xₛ) (hc : 0 ≤ sLocalIdelicOrderBound c)
    (u : (SAdeleRing F S)ˣ) (f : ℬₛ) (ℓ : StrongDual ℂ ℬₛ)
    (hℓ : ∀ f, ℓ f = sLocalIdelicZFunction f c) :
    ℓ (schwartzBruhatUnitTranslate u f) = c (QuotientGroup.mk u) * ℓ f := by
  rw [hℓ, hℓ]
  exact sLocalIdelicMellin_unitTranslate (F := F) (S := S) u f ⟨c, hc⟩

private theorem exists_sLocalMellin_dividedFactor (c₀ : Xₛ) {L : ℝ} (hL : L ≠ 0) (f : ℬₛ) :
    ∃ v : ℬₛ, ∀ z : ℂ, z ≠ 0 → 0 ≤ sLocalIdelicOrderBound (twistₛ c₀ z) →
      sLocalIdelicZFunction v (twistₛ c₀ z) =
        (1 - Complex.exp (-(L : ℂ) * z)) / ((L : ℂ) * z) * sLocalIdelicZFunction f (twistₛ c₀ z) := by
  obtain ⟨u, hu, hN⟩ := exists_sLocalLogNormSection (F := F) (S := S)
  let γ (t : ℝ) := u (-L * t)
  let x (t : ℝ) : Jₛ := QuotientGroup.mk (γ t)
  have hγ : Continuous γ := hu.comp (continuous_const.mul continuous_id)
  have hx : Continuous x := QuotientGroup.continuous_mk.comp hγ
  have hc (t : ℝ) : c₀ (x t) ≠ 0 := ((Group.isUnit _).map c₀).ne_zero
  obtain ⟨v, hv⟩ := exists_sLocalUnitOrbitAverage (F := F) (S := S) γ hγ _ ((c₀.continuous.comp hx).inv₀ hc) f
  refine ⟨v, ?_⟩
  intro z hz hreg
  let d : Xₛ := twistₛ c₀ z
  change 0 ≤ sLocalIdelicOrderBound d at hreg
  change sLocalIdelicZFunction v d = _ * sLocalIdelicZFunction f d
  obtain ⟨ℓ, hℓ⟩ := exists_sLocalRegularEval (F := F) (S := S) d hreg
  have hval (t : ℝ) : (twistₛ c₀ z) (x t) = c₀ (x t) * Complex.exp (-((L : ℂ) * z) * t) := by
    rw [show (twistₛ c₀ z) (x t) = _ from sLocalLogSection_twist (F := F) (S := S)
      c₀ (γ t) z (-L * t) (hN _), Complex.ofReal_mul, Complex.ofReal_neg]
    congr 2
    ring
  rw [← hℓ v, hv ℓ, ← hℓ f]
  calc
    _ = ∫ t in (0 : ℝ)..1, Complex.exp (-((L : ℂ) * z) * t) * ℓ f := by
      refine intervalIntegral.integral_congr fun t _ ↦ ?_
      change (c₀ (x t))⁻¹ * ℓ (schwartzBruhatUnitTranslate (γ t) f) = _
      rw [sLocalRegularEval_translate (F := F) (S := S) d hreg (γ t) f ℓ hℓ]
      change (c₀ (x t))⁻¹ * ((twistₛ c₀ z) (x t) * ℓ f) = _
      rw [hval, ← mul_assoc, inv_mul_cancel_left₀ (hc t)]
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, intervalAverage_exp_neg _ (mul_ne_zero
        (Complex.ofReal_ne_zero.mpr hL) hz), neg_mul]

/-- Averaging a local Schwartz test over a compact interval of norm translations
multiplies its centered Mellin germ by the divided exponential factor. -/
private theorem exists_sLocalMellin_dividedFactor_germ (c₀ : Xₛ) {L : ℝ} (hL : L ≠ 0) (f : ℬₛ) :
    ∃ v : ℬₛ, ∀ (c : Xₛ) (b : ℂ), twistₛ c₀ b = c →
      (fun z ↦ sLocalIdelicZFunction v (twistₛ c z)) =ᶠ[𝓝[≠] (0 : ℂ)]
        fun z ↦ ((1 - Complex.exp (-(L : ℂ) * (z + b))) / ((L : ℂ) * (z + b))) *
          sLocalIdelicZFunction f (twistₛ c z) := by
  obtain ⟨v, hv⟩ := exists_sLocalMellin_dividedFactor (F := F) (S := S) c₀ hL f
  refine ⟨v, ?_⟩
  intro c b hcb
  have hreg := sLocalOrbital_eventually_regular c
  have hne : ∀ᶠ z : ℂ in 𝓝[≠] 0, z ≠ 0 := self_mem_nhdsWithin (a := (0 : ℂ)) (s := {0}ᶜ)
  have hn : ∀ᶠ z : ℂ in 𝓝[≠] 0, z + b ≠ 0 := by
    by_cases hb : b = 0
    · simpa only [hb, add_zero] using hne
    · filter_upwards [eventually_ne_nhdsWithin (s := {(0 : ℂ)}ᶜ) (show (0 : ℂ) ≠ -b by simpa using hb)] with z hz
      exact fun h ↦ hz (eq_neg_of_add_eq_zero_left h)
  filter_upwards [hreg, hn] with z h hz'
  have heq : twistₛ c z = twistₛ c₀ (z + b) := by
    rw [← hcb]
    have e := normTwist_normTwist (G := Jₛ) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous c₀ b z
    exact e
  exact heq.symm ▸ hv (z + b) hz' (heq ▸ h)

end CompactNormAverage

/-- Residues only depend on the germ on a punctured neighbourhood. -/
private theorem orbitalResidue_congr {g h : ℂ → ℂ}
    (he : g =ᶠ[𝓝[≠] (0 : ℂ)] h) : complexResidue g 0 = complexResidue h 0 := by
  obtain ⟨δ, hδ, hEq⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp he
  unfold complexResidue limUnder
  refine congrArg lim (Filter.map_congr ?_)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  rw [circleIntegral.integral_congr hr.1.le fun z hz ↦ hEq ⟨?_, ?_⟩]
  · rw [Metric.mem_ball, Metric.mem_sphere.mp hz]
    exact hr.2
  · rintro rfl
    exact hr.1.ne (by simpa using hz)

/-- An exact pole order gives a nonzero coefficient at that order. -/
private theorem sLocalPrincipalPartCoeff_ne_zero_of_centered_order (f : ℬₛ) (c : Xₛ) (k : ℕ)
    (h : meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction f (twistₛ c z)) 0 = ((-(k : ℤ) : ℤ) : WithTop ℤ)) :
    sLocalPrincipalPartCoeff c k f ≠ 0 := by
  let Z : ℂ → ℂ := fun z ↦ sLocalIdelicZFunction f (twistₛ c z)
  obtain ⟨χ, s, hs⟩ := sLocalOrbitalPrincipalPart_range_le_ker_chart c
  have hmer : MeromorphicAt Z 0 := (sLocalOrbitalPrincipalPart_range_le_ker_zeta f χ s c hs).1
  obtain ⟨G, hG, hG0, hEq⟩ := (meromorphicOrderAt_eq_int_iff hmer).mp h
  rw [sLocalPrincipalPartCoeff_apply]
  change complexResidue (fun z ↦ Z z / z ^ (-(k : ℤ) + 1)) 0 ≠ 0
  have he : (fun z ↦ Z z / z ^ (-(k : ℤ) + 1)) =ᶠ[𝓝[≠] 0] (fun z ↦ G z / (z - 0)) := by
    filter_upwards [hEq, self_mem_nhdsWithin] with z hz hz0
    have hn : z ≠ 0 := hz0
    rw [hz, sub_zero, smul_eq_mul, zpow_add₀ hn, zpow_one]
    field_simp [zpow_ne_zero _ hn]
  rwa [orbitalResidue_congr he, complexResidue_div_sub hG]


private theorem orbitalCoeff_zero_of_centered_order (f : ℬₛ) (c : Xₛ) (k : ℕ)
    (hk : 0 < k) (h : ((-(k : ℤ) : ℤ) : WithTop ℤ) < meromorphicOrderAt Z(f,c) 0) :
    sLocalPrincipalPartCoeff c k f = 0 := by
  by_contra hne
  have hc := (sLocalPrincipalPartCoeff_ne_zero_imp_pole c k hk f hne).2
  unfold sLocalPolarMultiplicity at hc
  induction ho : meromorphicOrderAt Z(f,c) 0 using WithTop.recTopCoe with
  | top => simp only [ho, WithTop.untop₀_top, neg_zero, Int.toNat_zero] at hc; omega
  | coe n =>
    rw [ho, WithTop.coe_lt_coe] at h
    simp only [ho, WithTop.untop₀_coe] at hc
    omega

private theorem orbitalTriangularTest_of_centered_orders {T : Finset V} (ω : PontryaginDual J₁)
    (j : I(T,ω)) (f : ℬₛ)
    (hmain : meromorphicOrderAt Z(f,j.val.1) 0 =
      ((-(sLocalRhoPoleOrder j.val.1 - j.val.2 : ℕ) : ℤ) : WithTop ℤ))
    (hothers : ∀ i : I(T,ω), i.val.1 ≠ j.val.1 →
      (((sLocalFinitePoleMultiplicity T i.val.1 : ℤ) - sLocalRhoPoleOrder i.val.1 : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt Z(f,i.val.1) 0) :
    sLocalOrbitalPrincipalPart j ((Kₛ(ω)).mkQ f) ≠ 0 ∧
      ∀ i : I(T,ω), i.val.1 ≠ j.val.1 ∨ i.val.2 < j.val.2 →
        sLocalOrbitalPrincipalPart i ((Kₛ(ω)).mkQ f) = 0 := by
  classical
  have heval (i : I(T,ω)) :
      sLocalOrbitalPrincipalPart i ((Kₛ(ω)).mkQ f) =
        sLocalPrincipalPartCoeff i.val.1 (sLocalRhoPoleOrder i.val.1 - i.val.2) f :=
    sLocalThetaPrincipalPartCoeff_mk ω i.val.1 i.property.1 _ f
  rw [heval]
  refine ⟨sLocalPrincipalPartCoeff_ne_zero_of_centered_order f _ _ hmain, fun i hi ↦ ?_⟩
  rw [heval]
  have hr (i : I(T,ω)) : i.val.2 < sLocalRhoPoleOrder i.val.1 := by
    apply i.property.2.trans_le
    rw [sLocalRhoPoleOrder_eq_card_polePlaces]
    exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
  refine orbitalCoeff_zero_of_centered_order f _ _ (Nat.sub_pos_of_lt (hr i)) ?_
  by_cases hc : i.val.1 = j.val.1
  · have hlt := hi.resolve_left (not_not_intro hc)
    rw [hc, hmain, WithTop.coe_lt_coe]
    have hri := hr i
    have hrj := hr j
    rw [hc] at hri
    omega
  · apply lt_of_lt_of_le _ (hothers i hc)
    rw [WithTop.coe_lt_coe]
    have h := i.property.2
    have hri := hr i
    omega

private theorem orbitalEulerMultiplier_order {P E Z : ℂ → ℂ}
    (hE : AnalyticAt ℂ E 0) (hZ : MeromorphicAt Z 0) (b C : ℂ) (hC : C ≠ 0)
    (d : ℕ) (hEq : P =ᶠ[𝓝[≠] 0] fun z ↦ C * E z / (z + b) ^ d * Z z) :
    meromorphicOrderAt P 0 = meromorphicOrderAt E 0 -
      (if b = 0 then (d : WithTop ℤ) else 0) + meromorphicOrderAt Z 0 := by
  let D : ℂ → ℂ := fun z ↦ (z + b) ^ d
  have ha : AnalyticAt ℂ (fun z : ℂ ↦ z + b) 0 := analyticAt_id.add analyticAt_const
  have hD : AnalyticAt ℂ D 0 := ha.pow d
  have hden : meromorphicOrderAt D 0 = if b = 0 then (d : WithTop ℤ) else 0 := by
    by_cases hz : b = 0
    · simpa only [D, hz, add_zero, ite_true, sub_zero, Pi.pow_def] using (meromorphicOrderAt_pow_id_sub_const (x := (0 : ℂ)) (n := d))
    · rw [ite_eq_right hz, hD.meromorphicOrderAt_eq,
        hD.analyticOrderAt_eq_zero.mpr (by simpa [D] using pow_ne_zero d hz), ENat.map_zero]; rfl
  have hnum : AnalyticAt ℂ ((fun _ : ℂ ↦ C) * E) 0 := analyticAt_const.mul hE
  rw [meromorphicOrderAt_congr hEq]
  change meromorphicOrderAt (((fun _ : ℂ ↦ C) * E / D) * Z) 0 = _
  rw [meromorphicOrderAt_mul (hnum.meromorphicAt.div hD.meromorphicAt) hZ,
    meromorphicOrderAt_div hnum.meromorphicAt hD.meromorphicAt,
    meromorphicOrderAt_mul analyticAt_const.meromorphicAt hE.meromorphicAt,
    meromorphicOrderAt_const, ite_eq_right hC, zero_add, hden]

private theorem orbitalEulerMultiplier_center_order (n m r : ℕ) (hr : r < n) (hn : n ≤ m) :
    (n : WithTop ℤ) - ((n - r : ℕ) : WithTop ℤ) + ((-(m : ℤ) : ℤ) : WithTop ℤ) =
      ((-((m - r : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  change ((n : ℤ) : WithTop ℤ) - (((n - r : ℕ) : ℤ) : WithTop ℤ) +
    ((-(m : ℤ) : ℤ) : WithTop ℤ) = _
  rw [← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.coe_add, WithTop.coe_eq_coe]
  omega

private theorem orbitalEulerMultiplier_other_order (n m : ℕ) (o : WithTop ℤ)
    (h : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ o) :
    (((n : ℤ) - m : ℤ) : WithTop ℤ) ≤ (n : WithTop ℤ) + o := by
  change (((n : ℤ) - m : ℤ) : WithTop ℤ) ≤ ((n : ℤ) : WithTop ℤ) + o
  rw [sub_eq_add_neg, WithTop.coe_add]
  exact add_le_add_right h _

/-- Reduces triangular interpolation to multiplication by the selected reciprocal
Euler product with the prescribed number of its center zeros divided out. -/
private theorem orbitalTriangularTest_of_euler_multiplier {T : Finset V} (ω : PontryaginDual J₁)
    (j : I(T,ω)) (base target : ℬₛ)
    (hbase : meromorphicOrderAt Z(base,j.val.1) 0 =
      ((-(sLocalRhoPoleOrder j.val.1 : ℤ) : ℤ) : WithTop ℤ))
    (e : I(T,ω) → ℂ → ℂ)
    (he : ∀ i, AnalyticAt ℂ (e i) 0 ∧
      meromorphicOrderAt (e i) 0 = (sLocalFinitePoleMultiplicity T i.val.1 : WithTop ℤ))
    (b : I(T,ω) → ℂ) (hb : ∀ i, b i = 0 ↔ i.val.1 = j.val.1)
    (C : ℂ) (hC : C ≠ 0)
    (hM : ∀ i, Z(target,i.val.1) =ᶠ[𝓝[≠] 0]
      (fun z ↦ C * e i z / (z + b i) ^ (sLocalFinitePoleMultiplicity T j.val.1 - j.val.2) *
        Z(base,i.val.1) z)) :
    sLocalOrbitalPrincipalPart j ((Kₛ(ω)).mkQ target) ≠ 0 ∧
      ∀ i : I(T,ω), i.val.1 ≠ j.val.1 ∨ i.val.2 < j.val.2 →
        sLocalOrbitalPrincipalPart i ((Kₛ(ω)).mkQ target) = 0 := by
  classical
  let d := sLocalFinitePoleMultiplicity T j.val.1 - j.val.2
  have hZ (i : I(T,ω)) :
      MeromorphicAt Z(base,i.val.1) 0 ∧
        ((-(sLocalRhoPoleOrder i.val.1 : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Z(base,i.val.1) 0 := by
    obtain ⟨χ, s, hc⟩ := sLocalOrbitalPrincipalPart_range_le_ker_chart i.val.1
    exact sLocalOrbitalPrincipalPart_range_le_ker_zeta base χ s _ hc
  have ho (i : I(T,ω)) :
      meromorphicOrderAt Z(target,i.val.1) 0 =
        (sLocalFinitePoleMultiplicity T i.val.1 : WithTop ℤ) -
          (if b i = 0 then (d : WithTop ℤ) else 0) + meromorphicOrderAt Z(base,i.val.1) 0 := by
    have h := orbitalEulerMultiplier_order (he i).1 (hZ i).1 (b i) C hC d (hM i)
    rw [(he i).2] at h
    exact h
  apply orbitalTriangularTest_of_centered_orders ω j target
  · rw [ho, hbase, ite_eq_left ((hb j).mpr rfl)]
    have hr := j.property.2
    have hmr : sLocalFinitePoleMultiplicity T j.val.1 ≤ sLocalRhoPoleOrder j.val.1 := by
      rw [sLocalRhoPoleOrder_eq_card_polePlaces]
      exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
    exact orbitalEulerMultiplier_center_order _ _ _ hr hmr
  · intro i hi
    have hnot : b i ≠ 0 := fun h ↦ hi ((hb i).mp h)
    have horder := ho i
    simp only [ite_eq_right hnot, sub_zero] at horder
    exact (orbitalEulerMultiplier_other_order _ _ _ (hZ i).2).trans_eq horder.symm

local notation "Euler(" v ", " c ")" =>
  (fun z ↦ finiteLocalEulerFactor (Subtype.val v) (sLocalFiniteRestriction v (twistₛ c z)))

private theorem orbitalEuler_reciprocal_shape (v : S) (c : Xₛ) :
    let L := Real.log (v.val.asIdeal.absNorm : ℝ)
    0 < L ∧
      (Euler(v,c)⁻¹ = 1 ∨ ∃ a : ℂ, a ≠ 0 ∧ Euler(v,c)⁻¹ =
        fun z ↦ 1 - a * Complex.exp (-(L : ℂ) * z)) := by
  classical
  intro L
  have hq : 1 < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  refine ⟨Real.log_pos hq, ?_⟩
  let ι := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom
  have hunit (z : ℂ) (u : (v.val.adicCompletionIntegers F)ˣ) :
      sLocalFiniteRestriction v (twistₛ c z) (ι u) = sLocalFiniteRestriction v c (ι u) := by
    rw [sLocalOrbitalPrincipalPart_range_le_ker_restrict]
    have hu : ‖((ι u : (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F)‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
          (a := ι u)).mp ⟨u.val.property, u.inv.property⟩)
    rw [hu, Complex.ofReal_one, Complex.one_cpow, mul_one]
  let hv := (Valued.v : Valuation (v.val.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v.val.adicCompletion F)ˣ := Units.mk0 hv.choose hv.choose_spec.ne_zero
  have hp : ‖π.val‖ = (v.val.asIdeal.absNorm : ℝ)⁻¹ :=
    norm_uniformizer_adicCompletion v.val _ hv.choose_spec
  have key (z : ℂ) : (∀ u, sLocalFiniteRestriction v (twistₛ c z) (ι u) = 1) ↔
      (∀ u, sLocalFiniteRestriction v c (ι u) = 1) :=
    forall_congr' fun u ↦ by rw [hunit z u]
  by_cases hu : ∀ u, sLocalFiniteRestriction v c (ι u) = 1
  · right
    refine ⟨sLocalFiniteRestriction v c π, ((Group.isUnit π).map (sLocalFiniteRestriction v c)).ne_zero, ?_⟩
    funext z
    change (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹ = _
    unfold finiteLocalEulerFactor
    rw [ite_eq_left ((key z).mpr hu), inv_inv, sLocalOrbitalPrincipalPart_range_le_ker_restrict]
    change 1 - sLocalFiniteRestriction v c π * (‖π.val‖ : ℂ) ^ z = _
    have hp0 : (‖π.val‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr π.ne_zero)
    rw [Complex.cpow_def_of_ne_zero hp0, ← Complex.ofReal_log (norm_nonneg _),
      hp, Real.log_inv, Complex.ofReal_neg]
  · left
    funext z
    change (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹ = 1
    unfold finiteLocalEulerFactor
    rw [ite_eq_right (fun h ↦ hu ((key z).mp h)), inv_one]

private theorem orbitalEuler_geometric_order (L a : ℂ) (hL : L ≠ 0) (ha : a ≠ 0) :
    let f := fun z ↦ 1 - a * Complex.exp (-L * z)
    AnalyticAt ℂ f 0 ∧ meromorphicOrderAt f 0 = if a = 1 then 1 else 0 := by
  classical
  intro f
  have hA : AnalyticAt ℂ f 0 := by dsimp [f]; fun_prop
  refine ⟨hA, ?_⟩
  rw [hA.meromorphicOrderAt_eq]
  by_cases h : a = 1
  · have hder : HasDerivAt f (a * L) 0 := by
      have H := (((Complex.hasDerivAt_exp (-L * (0 : ℂ))).comp 0
        ((hasDerivAt_id (0 : ℂ)).const_mul (-L))).const_mul a).const_sub 1
      simpa [f] using H
    have h0 : f 0 = 0 := by simp [f, h]
    rw [ite_eq_left h, hA.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h0
      (hder.deriv ▸ mul_ne_zero ha hL), ENat.map_one]
    rfl
  · rw [ite_eq_right h, hA.analyticOrderAt_eq_zero.mpr (show f 0 ≠ 0 from by simpa only [f, mul_zero, Complex.exp_zero, mul_one, sub_ne_zero] using Ne.symm h),
      ENat.map_zero]
    rfl


open Classical in
private theorem orbitalEuler_reciprocal_data (v : S) (c : Xₛ) :
    AnalyticAt ℂ (Euler(v,c)⁻¹) 0 ∧
      meromorphicOrderAt (Euler(v,c)⁻¹) 0 = (if v ∈ sLocalFinitePolePlaces c then 1 else 0) ∧
      (v ∈ sLocalFinitePolePlaces c → Euler(v,c)⁻¹ =
        fun z ↦ 1 - Complex.exp (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * z)) := by
  classical
  obtain ⟨hL, h⟩ := orbitalEuler_reciprocal_shape v c
  have hmem : v ∈ sLocalFinitePolePlaces c ↔ meromorphicOrderAt Euler(v,c) 0 < 0 := by
    simp [sLocalFinitePolePlaces]
  have hb : meromorphicOrderAt Euler(v,c) 0 = -meromorphicOrderAt (Euler(v,c)⁻¹) 0 := by
    rw [← meromorphicOrderAt_inv, inv_inv]
  rcases h with h | ⟨a, ha, h⟩
  · have h1 : AnalyticAt ℂ (Euler(v,c)⁻¹) 0 := by rw [h]; exact analyticAt_const
    have h0 : meromorphicOrderAt (Euler(v,c)⁻¹) 0 = 0 := by
      rw [h]
      change meromorphicOrderAt (fun _ : ℂ ↦ (1 : ℂ)) 0 = _
      simp [meromorphicOrderAt_const]
    have hv : v ∉ sLocalFinitePolePlaces c := by
      rw [hmem, hb, h0, neg_zero]
      exact lt_irrefl _
    exact ⟨h1, by rw [h0, ite_eq_right hv], fun hc ↦ (hv hc).elim⟩
  · obtain ⟨hA, hO⟩ := orbitalEuler_geometric_order _ a (Complex.ofReal_ne_zero.mpr hL.ne') ha
    have ho : meromorphicOrderAt (Euler(v,c)⁻¹) 0 = if a = 1 then 1 else 0 := by rw [h]; exact hO
    have h1 : AnalyticAt ℂ (Euler(v,c)⁻¹) 0 := by rw [h]; exact hA
    have hh : v ∈ sLocalFinitePolePlaces c ↔ a = 1 := by
      rw [hmem, hb, ho]
      by_cases h' : a = 1
      · rw [ite_eq_left h']
        exact iff_of_true (WithTop.coe_lt_coe.mpr (by decide : (-1 : ℤ) < 0)) h'
      · simp [h']
    refine ⟨h1, by simpa only [hh] using ho, fun hp ↦ ?_⟩
    simpa only [hh.mp hp, one_mul] using h

private def orbitalReciprocalProduct (U : Finset S) (c : Xₛ) (z : ℂ) : ℂ :=
  ∏ v ∈ U, (Euler(v,c) z)⁻¹

open Classical in
private theorem orbitalReciprocalProduct_order (T : Finset V) (c : Xₛ) :
    let U := Finset.univ.filter (fun v : S ↦ v.val ∈ T)
    AnalyticAt ℂ (orbitalReciprocalProduct U c) 0 ∧
      meromorphicOrderAt (orbitalReciprocalProduct U c) 0 =
        (sLocalFinitePoleMultiplicity T c : WithTop ℤ) := by
  classical
  intro U
  have ha (v : S) : AnalyticAt ℂ (Euler(v,c)⁻¹) 0 := (orbitalEuler_reciprocal_data v c).1
  refine ⟨U.analyticAt_fun_prod fun v _ ↦ ha v, ?_⟩
  have ho := meromorphicOrderAt_fun_prod (s := U) (f := fun v ↦ Euler(v,c)⁻¹)
    (fun v _ ↦ (ha v).meromorphicAt)
  change meromorphicOrderAt (orbitalReciprocalProduct U c) 0 = _ at ho
  refine ho.trans ?_
  simp_rw [(orbitalEuler_reciprocal_data _ c).2.1]
  unfold U sLocalFinitePoleMultiplicity
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_filter]
  have hP : (Finset.univ.filter fun v : S ↦ v ∈ sLocalFinitePolePlaces c) = sLocalFinitePolePlaces c := by
    ext v
    simp
  let b (v : S) : WithTop ℤ := if v.val ∈ T then 1 else 0
  calc
    _ = ∑ v : S, if v ∈ sLocalFinitePolePlaces c then b v else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∈ sLocalFinitePolePlaces c <;> by_cases ht : v.val ∈ T <;> simp [b, hv, ht]
    _ = _ := by
      have hh := Finset.sum_filter (s := (Finset.univ : Finset S))
        (p := fun v ↦ v ∈ sLocalFinitePolePlaces c) (f := b)
      simpa only [hP, b] using hh.symm

local notation "ell(" v ")" => (Real.log ((Subtype.val v).asIdeal.absNorm : ℝ))

open Classical in
private theorem orbitalReciprocalProduct_principalValue (U : Finset S) (f : ℬₛ) (c : Xₛ)
    (hT : U.image Subtype.val ⊆ S) :
    Z(sAdelePrincipalValue F hT f,c) =ᶠ[𝓝[≠] 0]
      fun z ↦ orbitalReciprocalProduct U c z * Z(f,c) z := by
  classical
  let T : Finset V := U.image Subtype.val
  obtain ⟨χ, s, hc⟩ := sLocalOrbitalPrincipalPart_range_le_ker_chart c
  have ht : Tendsto (fun z : ℂ ↦ s + z) (𝓝[≠] 0) (𝓝[≠] s) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_const.add continuous_id : Continuous fun z : ℂ ↦ s + z).tendsto'
        (0 : ℂ) s (add_zero s)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact fun h ↦ hz (add_eq_left.mp h)
  have h := nhdsNE_le_codiscrete s (sLocalIdelicZFunction_principalValue T hT f χ)
  filter_upwards [ht.eventually h] with z hz
  simp only [← hc z] at hz
  rw [hz, div_eq_mul_inv, mul_comm, ← Finset.prod_inv_distrib]
  congr 1
  have hU : U = Finset.univ.filter (fun v : S ↦ v.val ∈ T) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun hv ↦ Finset.mem_image.mpr ⟨v, hv, rfl⟩
    · intro hv
      obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hv
      exact (Subtype.ext heq : w = v) ▸ hw
  rw [orbitalReciprocalProduct, hU, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro v _
  split_ifs <;> simp

private theorem orbitalReciprocalFactor_shift (c₀ c : Xₛ) (b : ℂ) (hc : twistₛ c₀ b = c)
    (v : S) (hv : v ∈ sLocalFinitePolePlaces c₀) (z : ℂ) :
    (1 - Complex.exp (-(ell(v) : ℂ) * (z + b))) = (Euler(v,c) z)⁻¹ := by
  have he := congrFun ((orbitalEuler_reciprocal_data v c₀).2.2 hv) (z + b)
  change (Euler(v,c₀) (z + b))⁻¹ = _ at he
  have hc' : twistₛ c z = twistₛ c₀ (z + b) := by
    rw [← hc]
    exact normTwist_normTwist _ _ _ _ _
  change _ = (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹
  rw [hc']
  exact he.symm

private theorem exists_orbitalReciprocalProduct_divided (D : Finset S) (c₀ : Xₛ)
    (hD : D ⊆ sLocalFinitePolePlaces c₀) (f : ℬₛ) :
    ∃ g : ℬₛ, ∀ (c : Xₛ) (b : ℂ), twistₛ c₀ b = c →
      Z(g,c) =ᶠ[𝓝[≠] 0] fun z ↦
        ((∏ v ∈ D, (ell(v) : ℂ)⁻¹) * orbitalReciprocalProduct D c z) /
          (z + b) ^ D.card * Z(f,c) z := by
  classical
  induction D using Finset.induction_on with
  | empty =>
    exact ⟨f, fun c b _ ↦ .of_forall fun z ↦ by simp [orbitalReciprocalProduct]⟩
  | insert v D hv ih =>
    obtain ⟨g, hg⟩ := ih (Finset.subset_insert _ _ |>.trans hD)
    have hp := hD (Finset.mem_insert_self v D)
    have hL := (orbitalEuler_reciprocal_shape v c₀).1.ne'
    obtain ⟨k, hk⟩ := exists_sLocalMellin_dividedFactor_germ (F := F) (S := S) c₀ hL g
    refine ⟨k, fun c b hc ↦ ?_⟩
    filter_upwards [hg c b hc, hk c b hc] with z hz hz'
    rw [hz', hz, orbitalReciprocalFactor_shift c₀ c b hc v hp]
    simp only [orbitalReciprocalProduct, Finset.prod_insert hv, Finset.card_insert_of_notMem hv,
      pow_succ, div_eq_mul_inv, mul_inv_rev]
    ring

private theorem orbitalNormTwist_zero (c : Xₛ) : twistₛ c 0 = c := by
  ext1 t
  change c t * _ ^ (0 : ℂ) = c t
  rw [Complex.cpow_zero, mul_one]

private theorem orbitalNormTwist_of_same_restriction (c d : Xₛ)
    (h : normOneRestriction mₛ c = normOneRestriction mₛ d) :
    ∃ b : ℂ, twistₛ c b = d := by
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨a, ha, -⟩ := existsUnique_complexPower (c.comp σ)
  obtain ⟨b, hb, -⟩ := existsUnique_complexPower (d.comp σ)
  refine ⟨b - a, ContinuousMonoidHom.ext fun x ↦ ?_⟩
  let t := mₛ x
  let k : J₁ := ⟨x / σ t, by
    change mₛ (x / σ t) = 1
    rw [map_div, hσ, div_self']⟩
  have hk : c k.val = d k.val := DFunLike.congr_fun h k
  have hx : k.val * σ t = x := div_mul_cancel _ _
  have hn : (((t : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr t.ne_zero)
  change c x * (((t : ℝ≥0) : ℝ) : ℂ) ^ (b - a) = d x
  rw [← hx, map_mul, map_mul, hk]
  change d k.val * (c.comp σ) t * _ = d k.val * (d.comp σ) t
  rw [ha, hb, mul_assoc, ← Complex.cpow_add _ _ hn]
  congr 2
  ring

private theorem orbitalReciprocal_lift_shift {T : Finset V} (ω : PontryaginDual J₁) (j : I(T,ω)) :
    ∃ b : I(T,ω) → ℂ, (∀ i, b i = 0 ↔ i.val.1 = j.val.1) ∧
      ∀ i, twistₛ j.val.1 (b i) = i.val.1 := by
  classical
  choose w hw using fun i : I(T,ω) ↦
    orbitalNormTwist_of_same_restriction _ _ (j.property.1.trans i.property.1.symm)
  let b (i : I(T,ω)) := if i.val.1 = j.val.1 then 0 else w i
  have he (i : I(T,ω)) : twistₛ j.val.1 (b i) = i.val.1 := by
    by_cases h : i.val.1 = j.val.1
    · simp only [b, ite_eq_left h]
      exact (orbitalNormTwist_zero j.val.1).trans h.symm
    · simpa only [b, ite_eq_right h] using hw i
  refine ⟨b, fun i ↦ ⟨?_, fun h ↦ ite_eq_left h⟩, he⟩
  intro h
  have h' := he i
  rw [h, orbitalNormTwist_zero] at h'
  exact h'.symm

open Classical in
private theorem exists_orbitalReciprocal_multiplier {T : Finset V} (c₀ : Xₛ) (d : ℕ)
    (hd : d ≤ sLocalFinitePoleMultiplicity T c₀) (f : ℬₛ) :
    let U : Finset S := Finset.univ.filter (fun v : S ↦ v.val ∈ T)
    ∃ C : ℂ, C ≠ 0 ∧ ∃ k : ℬₛ, ∀ (c : Xₛ) (b : ℂ), twistₛ c₀ b = c →
      Z(k,c) =ᶠ[𝓝[≠] (0 : ℂ)] fun z ↦
        C * orbitalReciprocalProduct U c z / (z + b) ^ d * Z(f,c) z := by
  classical
  intro U
  let V₀ : Finset S := (sLocalFinitePolePlaces c₀).filter (fun v : S ↦ v.val ∈ T)
  have hd' : d ≤ V₀.card := hd
  obtain ⟨D, hD, hcard⟩ := Finset.exists_subset_card_eq hd'
  have hDV : D ⊆ sLocalFinitePolePlaces c₀ := hD.trans (Finset.filter_subset _ _)
  have hDU : D ⊆ U := fun v hv ↦ Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (Finset.mem_filter.mp (hD hv)).2⟩
  obtain ⟨g, hg⟩ := exists_orbitalReciprocalProduct_divided D c₀ hDV f
  let C := ∏ v ∈ D, (ell(v) : ℂ)⁻¹
  have hC : C ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦ inv_ne_zero
    (Complex.ofReal_ne_zero.mpr (orbitalEuler_reciprocal_shape v c₀).1.ne')
  let W := U \ D
  have hW : W.image Subtype.val ⊆ S := by
    intro v hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact w.property
  let k := sAdelePrincipalValue F hW g
  refine ⟨C, hC, k, fun c b hc ↦ ?_⟩
  have h' := orbitalReciprocalProduct_principalValue W g c hW
  filter_upwards [h', hg c b hc] with z hz hz'
  have hp : orbitalReciprocalProduct U c z =
      orbitalReciprocalProduct W c z * orbitalReciprocalProduct D c z :=
    (Finset.prod_sdiff hDU).symm
  change Z(k,c) z = _
  change Z(k,c) z = _ at hz
  rw [hz, hz', hp, hcard]
  ring

/-- Realize a nonzero selected coefficient while killing selected coefficients at other
centers and higher selected orders at this center. Start from a standard Gaussian at
the center, then divide the selected reciprocal Euler product by the needed power of
the chart parameter. The divided factors act by compact averages of norm translations. -/
private theorem exists_sLocalOrbitalPrincipalPart_triangular_test {T : Finset V}
    (_hT : T ⊆ S) (_hTne : T.Nonempty) (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial)
    (ω : PontryaginDual J₁) (j : I(T, ω)) :
    ∃ f : ℬₛ,
      sLocalOrbitalPrincipalPart j ((Kₛ(ω)).mkQ f) ≠ 0 ∧
      ∀ i : I(T, ω), i.val.1 ≠ j.val.1 ∨ i.val.2 < j.val.2 →
        sLocalOrbitalPrincipalPart i ((Kₛ(ω)).mkQ f) = 0 := by
  classical
  let c₀ : Xₛ := j.val.1
  have hmul : sLocalFinitePoleMultiplicity T c₀ ≤ sLocalRhoPoleOrder c₀ := by
    rw [sLocalRhoPoleOrder_eq_card_polePlaces]
    exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
  have hn := lt_of_le_of_lt (Nat.zero_le _) j.property.2
  obtain ⟨f, hf⟩ := exists_sLocalZeta_full_pole c₀ (hn.trans_le hmul)
  let U : Finset S := Finset.univ.filter (fun v : S ↦ v.val ∈ T)
  let d := sLocalFinitePoleMultiplicity T c₀ - j.val.2
  obtain ⟨C, hC, k, hk⟩ := exists_orbitalReciprocal_multiplier (T := T) c₀ d (Nat.sub_le _ _) f
  obtain ⟨b, hb, hbt⟩ := orbitalReciprocal_lift_shift ω j
  refine ⟨k, orbitalTriangularTest_of_euler_multiplier ω j f k hf
    (fun i ↦ orbitalReciprocalProduct U i.val.1) (fun i ↦ orbitalReciprocalProduct_order T i.val.1)
    b hb C hC (fun i ↦ hk i.val.1 (b i) (hbt i))⟩

end TriangularPrincipalPartTests

open Classical in
/-- Paper: Theorem 7.3.1.2(2), p. 342.
For each selected coefficient there is a homogeneous theta class on which it takes the
value one while every other selected coefficient vanishes.
Deviation: Uses the finite-place selection of part (1). The paper obtains the class from
a test whose zeta transform has a single pole on the component, of the selected order. -/
theorem exists_sLocalOrbitalPrincipalPart_dual {T : Finset V} (_hT : T ⊆ S)
    (_hTne : T.Nonempty) (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial)
    (ω : PontryaginDual J₁) (j : I(T, ω)) :
    ∃ x : Θₛ(ω), ∀ i : I(T, ω),
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) i x =
        if i = j then 1 else 0 := by
  refine sLocalOrbitalPrincipalPart_triangular_dual
    (fun i : I(T, ω) ↦ i.val.1) (fun i ↦ i.val.2) (sLocalFinitePoleMultiplicity T)
    (fun i ↦ (sLocalOrbitalPrincipalPart i).toLinearMap) (fun i ↦ i.property.2) ?_ ?_ j
  · intro i k hc hr
    exact Subtype.ext (Prod.ext hc hr)
  · intro i
    obtain ⟨f, hf, hzero⟩ := exists_sLocalOrbitalPrincipalPart_triangular_test _hT _hTne _hS _hPic ω i
    exact ⟨(Kₛ(ω)).mkQ f, hf, hzero⟩

open Classical in
/-- Paper: Theorem 7.3.1.2(2), p. 341.
The selected coefficients have a biorthogonal family in the quotient. The pairing is
evaluated on a representative of each quotient vector.
Deviation: Uses the finite-place selection of part (1). -/
theorem sLocalOrbitalPrincipalValue_biorthogonal {T : Finset V} (hT : T ⊆ S) (_hTne : T.Nonempty)
    (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial) (ω : PontryaginDual J₁) :
    let R := PV(T, hT, ω)
    ∃ ψ : I(T, ω) → (Θₛ(ω) ⧸ R),
      ∀ (i j : I(T, ω)) (x : Θₛ(ω)), R.mkQ x = ψ j →
        sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) i x =
          if i = j then 1 else 0 := by
  intro R
  choose y hy using exists_sLocalOrbitalPrincipalPart_dual hT _hTne _hS _hPic ω
  refine ⟨fun j ↦ R.mkQ (y j), fun i j x hx ↦ ?_⟩
  have hmem : x - y j ∈ R := (Submodule.Quotient.eq R).mp hx
  have h0 := sLocalOrbitalPrincipalValue_annihilator_ker hT ω i hmem
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, sub_eq_zero] at h0
  exact h0.trans (hy j i)

/-- Paper: Theorem 7.3.1.2(2), p. 341.
The selected coefficients are topologically free. Two unconditionally convergent series
with the same limit have identical coefficients.
Deviation: Uses the finite-place selection of part (1). -/
theorem sLocalOrbitalPrincipalPart_hasSum_unique {T : Finset V} (_hT : T ⊆ S) (_hTne : T.Nonempty)
    (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial) (ω : PontryaginDual J₁)
    (a b : I(T, ω) → ℂ)
    (u : StrongDual ℂ (Θₛ(ω)))
    (ha : HasSum (fun j ↦ a j • sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) j) u)
    (hb : HasSum (fun j ↦ b j • sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) j) u) :
    a = b := by
  classical
  obtain ⟨ψ, hψ⟩ := sLocalOrbitalPrincipalValue_biorthogonal (F := F) (S := S) _hT _hTne _hS _hPic ω
  funext i
  obtain ⟨x, hx⟩ := (PV(T, _hT, ω)).mkQ_surjective (ψ i)
  let ev := ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) x
  have recover (t : I(T, ω) → ℂ)
      (ht : HasSum (fun j ↦ t j • sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) j) u) :
      t i = u x := by
    have hs : HasSum (fun j ↦ if j = i then t i else 0) (u x) := by
      refine (ev.hasSum ht).congr_fun fun j ↦ ?_
      change (if j = i then t i else 0) = t j * sLocalOrbitalPrincipalPart j x
      rw [hψ j i x hx]
      by_cases h : j = i <;> simp [h]
    exact (hasSum_ite_eq i (t i)).unique hs
  exact (recover a ha).trans (recover b hb).symm

local notation "Sₚ(" p ")" => sLocalPrimaryPlaces (F := F) S p
local notation "hₚ(" p ")" => sLocalPrimaryPlaces_subset (F := F) S p

/-- Paper: Definition 7.3.1.3, p. 343.
The denominator of the primary orbital quotient is the image of the corresponding
principal-value operator on the homogeneous theta space. -/
def sLocalPrimaryOrbitalSubmodule (p : Vℚ) (ω : PontryaginDual J₁) : Submodule ℂ (Θₛ(ω)) :=
  PV(Sₚ(p), hₚ(p), ω)

local notation "Rₚ(" p ", " ω ")" => sLocalPrimaryOrbitalSubmodule (F := F) (S := S) p ω

/-- Paper: Definition 7.3.1.3, p. 343.
The p-primary orbital quotient is the homogeneous theta space modulo its primary
principal-value image. It carries the quotient topology.

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its definition (#5398). -/
def SLocalPrimaryOrbitalQuotient (p : Vℚ) (ω : PontryaginDual J₁) :=
  Θₛ(ω) ⧸ Rₚ(p, ω)

namespace SLocalPrimaryOrbitalQuotient

instance instAddCommGroup (p : Vℚ) (ω : PontryaginDual J₁) :
    AddCommGroup (SLocalPrimaryOrbitalQuotient p ω) :=
  inferInstanceAs (AddCommGroup (Θₛ(ω) ⧸ Rₚ(p, ω)))

instance instModule (p : Vℚ) (ω : PontryaginDual J₁) :
    Module ℂ (SLocalPrimaryOrbitalQuotient p ω) :=
  inferInstanceAs (Module ℂ (Θₛ(ω) ⧸ Rₚ(p, ω)))

instance instTopologicalSpace (p : Vℚ) (ω : PontryaginDual J₁) :
    TopologicalSpace (SLocalPrimaryOrbitalQuotient p ω) :=
  inferInstanceAs (TopologicalSpace (Θₛ(ω) ⧸ Rₚ(p, ω)))

instance instIsTopologicalAddGroup (p : Vℚ) (ω : PontryaginDual J₁) :
    IsTopologicalAddGroup (SLocalPrimaryOrbitalQuotient p ω) :=
  inferInstanceAs (IsTopologicalAddGroup (Θₛ(ω) ⧸ Rₚ(p, ω)))

instance instContinuousSMul (p : Vℚ) (ω : PontryaginDual J₁) :
    ContinuousSMul ℂ (SLocalPrimaryOrbitalQuotient p ω) :=
  inferInstanceAs (ContinuousSMul ℂ (Θₛ(ω) ⧸ Rₚ(p, ω)))

end SLocalPrimaryOrbitalQuotient

local notation "Q(" p ", " ω ")" => SLocalPrimaryOrbitalQuotient (F := F) (S := S) p ω
local notation "π(" p ", " ω ")" => (Rₚ(p, ω)).mkQ

/-- Paper: Definition 7.3.1.3, p. 343.
A theta class represents zero in the p-primary quotient exactly when its selected
highest Laurent coefficients vanish. -/
theorem sLocalPrimaryOrbitalQuotient_mk_eq_zero (p : Vℚ) (_hS : IsSaturatedPlaceSet S)
    (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial) (ω : PontryaginDual J₁) (x : Θₛ(ω)) :
    π(p, ω) x = 0 ↔ ∀ j : I(Sₚ(p), ω), sLocalOrbitalPrincipalPart j x = 0 := by
  have h := mem_sLocalOrbitalPrincipalValue_iff (F := F) (S := S) hₚ(p) _hp _hS _hPic ω x
  exact (Submodule.Quotient.mk_eq_zero _).trans h

/-- Paper: Definition 7.3.1.4, p. 343.
The primary multiplicity counts the places over p which contribute a simple pole.
Deviation: Uses positive pole multiplicity and extends it by zero outside the pole locus. -/
def sLocalPrimaryPoleMultiplicity (p : Vℚ) (c : Xₛ) : ℕ :=
  sLocalFinitePoleMultiplicity (Sₚ(p)) c

/-- Paper: Definition 7.3.1.4, p. 343.
Every place in the primary part contributes at the trivial character. -/
theorem sLocalPrimaryPoleMultiplicity_one (p : Vℚ) :
    sLocalPrimaryPoleMultiplicity p (1 : Xₛ) = (Sₚ(p)).card :=
  sLocalFinitePoleMultiplicity_one _ hₚ(p)

section QuotientTransfer

variable {E₁ E₂ : Type*} [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
variable [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
variable [IsTopologicalAddGroup E₁]
variable [ContinuousSMul ℂ E₁] [ContinuousSMul ℂ E₂]
variable (H₁ : Submodule ℂ E₁) (H₂ : Submodule ℂ E₂)
variable (A : E₁ →L[ℂ] E₂) (A₀ : (E₁ ⧸ H₁) →L[ℂ] (E₂ ⧸ H₂))
variable (x : ℕ → E₂) (d : ℕ → StrongDual ℂ (E₂ ⧸ H₂))
variable (B : Seminorm ℂ (E₂ ⧸ H₂) → ℕ → ℝ≥0) (y : ℕ → E₁)

/-- Paper: Lemma 7.3.1.5(1), p. 343.
Lifts of the absolute basis vectors give an absolute basis in the first quotient.
Their biorthogonal functionals are an unconditional basis of its strong dual. -/
theorem orbitalQuotient_lift_bases
    (_hF₁ : IsFrechetTVS E₁) (_hF₂ : IsFrechetTVS E₂)
    (_hN₁ : IsNuclearTVS E₁) (_hN₂ : IsNuclearTVS E₂)
    (_hH₁ : IsClosed (H₁ : Set E₁)) (_hH₂ : IsClosed (H₂ : Set E₂))
    (_hA : Injective A) (_hpre : H₂.comap A.toLinearMap = H₁)
    (_hA₀ : A₀.comp H₁.mkQL = H₂.mkQL.comp A) (_hsurj : Surjective A₀)
    (_hb : IsSchauderBasis (H₂.mkQL ∘ x) d) (_habs : SchauderBasis.IsAbsolute (H₂.mkQL ∘ x) d)
    (_hB : ∀ q : Seminorm ℂ (E₂ ⧸ H₂), Continuous q →
      (fun n ↦ q (H₂.mkQL (x n))) =O[atTop] (fun n ↦ (B q n : ℝ)))
    (_hy : ∀ n, A (y n) = x n) :
    let e := H₁.mkQL ∘ y
    let a := fun n ↦ (d n).comp A₀
    let ev : ℕ → StrongDual ℂ (StrongDual ℂ (E₁ ⧸ H₁)) :=
      fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (e n)
    IsSchauderBasis e a ∧ SchauderBasis.IsAbsolute e a ∧
      IsSchauderBasis a ev ∧ SchauderBasis.IsUnconditional a ev := by sorry

/-- Paper: Lemma 7.3.1.5(2), p. 344.
The estimate for each seminorm on the first quotient uses the bound for that
seminorm transported to the second quotient by the inverse induced isomorphism. -/
theorem orbitalQuotient_lift_growth
    (_hF₁ : IsFrechetTVS E₁) (_hF₂ : IsFrechetTVS E₂)
    (_hN₁ : IsNuclearTVS E₁) (_hN₂ : IsNuclearTVS E₂)
    (_hH₁ : IsClosed (H₁ : Set E₁)) (_hH₂ : IsClosed (H₂ : Set E₂))
    (_hA : Injective A) (_hpre : H₂.comap A.toLinearMap = H₁)
    (_hA₀ : A₀.comp H₁.mkQL = H₂.mkQL.comp A) (_hsurj : Surjective A₀)
    (_hb : IsSchauderBasis (H₂.mkQL ∘ x) d) (_habs : SchauderBasis.IsAbsolute (H₂.mkQL ∘ x) d)
    (_hB : ∀ q : Seminorm ℂ (E₂ ⧸ H₂), Continuous q →
      (fun n ↦ q (H₂.mkQL (x n))) =O[atTop] (fun n ↦ (B q n : ℝ)))
    (_hy : ∀ n, A (y n) = x n) :
    ∃ e : (E₁ ⧸ H₁) ≃L[ℂ] (E₂ ⧸ H₂), e.toContinuousLinearMap = A₀ ∧
      ∀ q : Seminorm ℂ (E₁ ⧸ H₁), Continuous q →
        (fun n ↦ q (H₁.mkQL (y n))) =O[atTop]
          (fun n ↦ (B (q.comp e.symm.toLinearMap) n : ℝ)) := by sorry

end QuotientTransfer

local notation "period(" v ")" => (2 * Real.pi / Real.log ((v : S).val.asIdeal.absNorm : ℝ))
local notation "lattice(" χ ", " v ", " t ", " n ")" =>
  chart(χ) ((((n : ℝ) * period(v) - t : ℝ) : ℂ) * Complex.I)
local notation "phase(" χ ", " v ", " u ", " t ")" =>
  (t ∈ Ico 0 period(v) ∧
    sLocalFiniteRestriction v (chart(χ) (-(t : ℂ) * Complex.I)) u = 1)
local notation "uniformizerNorm(" v ", " u ")" =>
  (‖(↑(u) : (v : S).val.adicCompletion F)‖ = ((v : S).val.asIdeal.absNorm : ℝ)⁻¹)

/-- Paper: Equation (7.3.1.10), p. 344.
There is a unique phase in the given interval for which the adjusted character
is trivial on the chosen local uniformizer. -/
theorem existsUnique_sLocalOrbitalPhase (χ : PontryaginDual Jₛ) (v : S)
    (u : (v.val.adicCompletion F)ˣ) (_hu : uniformizerNorm(v, u)) :
    ∃! t : ℝ, phase(χ, v, u, t) := by
  have hq : (1 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  have hq_pos : (0 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := zero_lt_one.trans hq
  have hlog : (0 : ℝ) < Real.log (v.val.asIdeal.absNorm : ℝ) := Real.log_pos hq
  have hqinv_pos : (0 : ℝ) < ((v.val.asIdeal.absNorm : ℝ)⁻¹) := inv_pos.mpr hq_pos
  have hnorm_eq :
      sLocalFiniteRestriction v (chart((1 : PontryaginDual Jₛ)) 1) u =
        (((v.val.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [sLocalFiniteRestriction_norm v u]
    simpa [Units.map, nnNormHom] using congrArg (fun r : ℝ ↦ (r : ℂ)) _hu
  let eProd := ContinuousMulEquiv.prodUnits
    (InfiniteAdeleRing F) ((w : S) → HeightOneSpectrum.adicCompletion F (Subtype.val w))
  let eFin := ContinuousMulEquiv.piUnits
    (M := fun w : S ↦ HeightOneSpectrum.adicCompletion F (Subtype.val w))
  let g : Jₛ :=
    (QuotientGroup.mk : (SAdeleRing F S)ˣ → Jₛ)
      (eProd.symm (1, eFin.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v u)))
  have hmod : (((mₛ g : ℝ≥0) : ℝ) : ℂ) = (((v.val.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) := by
    have h1 := hnorm_eq
    change (((1 : PontryaginDual Jₛ) g : Circle) : ℂ) * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ (1 : ℂ) = _ at h1
    simpa [Complex.cpow_one] using h1
  have heval (t : ℝ) :
      sLocalFiniteRestriction v (chart(χ) (-(t : ℂ) * Complex.I)) u =
        ((χ g : Circle) : ℂ) *
          Complex.exp (((t * Real.log (v.val.asIdeal.absNorm : ℝ) : ℝ) : ℂ) * Complex.I) := by
    change ((χ g : Circle) : ℂ) * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) = _
    rw [hmod, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hqinv_pos.ne')]
    rw [← Complex.ofReal_log hqinv_pos.le, Real.log_inv]
    congr 2
    push_cast
    ring
  let w : ℂ := ((χ g)⁻¹ : Circle)
  have hw_norm : ‖w‖ = 1 := Circle.norm_coe _
  have hw_mul : ((χ g : Circle) : ℂ) * w = 1 := by
    change ((χ g : Circle) : ℂ) * (((χ g)⁻¹ : Circle) : ℂ) = 1
    rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
  let θ : ℝ := if 0 ≤ w.arg then w.arg else w.arg + 2 * Real.pi
  have hθ_mem : θ ∈ Ico 0 (2 * Real.pi) := by
    dsimp [θ]
    split_ifs with h
    · exact ⟨h, (Complex.arg_le_pi w).trans_lt (by linarith [Real.pi_pos])⟩
    · have hlt : w.arg < 0 := not_le.mp h
      exact ⟨by linarith [Complex.neg_pi_lt_arg w], by linarith⟩
  have hθ_exp : Complex.exp ((θ : ℂ) * Complex.I) = w := by
    have hbase : Complex.exp ((w.arg : ℂ) * Complex.I) = w := by
      have h := Complex.norm_mul_exp_arg_mul_I w
      rw [hw_norm, Complex.ofReal_one, one_mul] at h
      exact h
    dsimp [θ]
    split_ifs with h
    · exact hbase
    · push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      exact hbase
  refine ⟨θ / Real.log (v.val.asIdeal.absNorm : ℝ), ⟨?_, ?_⟩, ?_⟩
  · constructor
    · exact div_nonneg hθ_mem.1 hlog.le
    · exact div_lt_div_of_pos_right hθ_mem.2 hlog
  · rw [heval, div_mul_cancel₀ _ hlog.ne', hθ_exp, hw_mul]
  · rintro t ⟨ht_mem, ht_eq⟩
    rw [heval] at ht_eq
    have hexp :
        Complex.exp (((t * Real.log (v.val.asIdeal.absNorm : ℝ) : ℝ) : ℂ) * Complex.I) =
          Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [hθ_exp]
      exact mul_left_cancel₀ (Circle.coe_ne_zero (χ g)) (ht_eq.trans hw_mul.symm)
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    have him : t * Real.log (v.val.asIdeal.absNorm : ℝ) = θ + (k : ℝ) * (2 * Real.pi) := by
      have h := congrArg Complex.im hk
      simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
        Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, add_zero, sub_zero,
        mul_one] at h
      exact h
    have ht_lo : 0 ≤ t * Real.log (v.val.asIdeal.absNorm : ℝ) := mul_nonneg ht_mem.1 hlog.le
    have ht_hi : t * Real.log (v.val.asIdeal.absNorm : ℝ) < 2 * Real.pi :=
      (lt_div_iff₀ hlog).mp ht_mem.2
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hk_lt_mul : (k : ℝ) * (2 * Real.pi) < 1 * (2 * Real.pi) := by
      linarith [hθ_mem.1, ht_hi]
    have hk_gt_mul : (-1 : ℝ) * (2 * Real.pi) < (k : ℝ) * (2 * Real.pi) := by
      linarith [hθ_mem.2, ht_lo]
    have hk_lt : (k : ℝ) < 1 := lt_of_mul_lt_mul_right hk_lt_mul h2pi.le
    have hk_gt : (-1 : ℝ) < (k : ℝ) := lt_of_mul_lt_mul_right hk_gt_mul h2pi.le
    have hk0 : k = 0 := by
      have h1 : k < 1 := Int.cast_lt.mp (by simpa using hk_lt)
      have h2 : -1 < k := Int.cast_lt.mp (by simpa using hk_gt)
      omega
    subst hk0
    simp only [Int.cast_zero, zero_mul, add_zero] at him
    exact (eq_div_iff hlog.ne').mpr him

/-- Paper: Equation (7.3.1.11), p. 344.
At a contributing finite place, the pole on the given component has a unique lattice index. -/
theorem existsUnique_sLocalOrbitalLatticeIndex (χ : PontryaginDual Jₛ) (v : S)
    (u : (v.val.adicCompletion F)ˣ) (_hu : uniformizerNorm(v, u)) (t : ℝ)
    (_ht : phase(χ, v, u, t)) (c : Xₛ)
    (_hc : ∃ s, c = chart(χ) s) (_hv : v ∈ sLocalFinitePolePlaces c) :
    ∃! n : ℤ, c = lattice(χ, v, t, n) := by
  obtain ⟨s, rfl⟩ := _hc
  have hq : (1 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  have hq_pos : (0 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := zero_lt_one.trans hq
  have hlog : (0 : ℝ) < Real.log (v.val.asIdeal.absNorm : ℝ) := Real.log_pos hq
  have hqinv_pos : (0 : ℝ) < ((v.val.asIdeal.absNorm : ℝ)⁻¹) := inv_pos.mpr hq_pos
  let eProd := ContinuousMulEquiv.prodUnits
    (InfiniteAdeleRing F) ((w : S) → HeightOneSpectrum.adicCompletion F (Subtype.val w))
  let eFin := ContinuousMulEquiv.piUnits
    (M := fun w : S ↦ HeightOneSpectrum.adicCompletion F (Subtype.val w))
  let finAt : (v.val.adicCompletion F)ˣ → Jₛ := fun x ↦
    (QuotientGroup.mk : (SAdeleRing F S)ˣ → Jₛ)
      (eProd.symm (1, eFin.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x)))
  have hmod_val (x : (v.val.adicCompletion F)ˣ) :
      (((mₛ (finAt x) : ℝ≥0) : ℝ) : ℂ) = ((‖(x : v.val.adicCompletion F)‖ : ℝ) : ℂ) := by
    have h1 := sLocalFiniteRestriction_norm (F := F) (S := S) v x
    change (((1 : PontryaginDual Jₛ) (finAt x) : Circle) : ℂ) *
      (((mₛ (finAt x) : ℝ≥0) : ℝ) : ℂ) ^ (1 : ℂ) = _ at h1
    simpa [Complex.cpow_one, Units.map, nnNormHom] using h1
  have htwist_eval (z : ℂ) (x : (v.val.adicCompletion F)ˣ) :
      sLocalFiniteRestriction v (twistₛ (chart(χ) s) z) x =
        sLocalFiniteRestriction v (chart(χ) s) x * ((‖(x : v.val.adicCompletion F)‖ : ℝ) : ℂ) ^ z := by
    change sLocalFiniteRestriction v (chart(χ) s) x * (((mₛ (finAt x) : ℝ≥0) : ℝ) : ℂ) ^ z = _
    rw [hmod_val x]
  have hunr_iff (z : ℂ) :
      (∀ y : (HeightOneSpectrum.adicCompletionIntegers F v.val)ˣ,
          sLocalFiniteRestriction v (twistₛ (chart(χ) s) z)
            (Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom y) = 1) ↔
        (∀ y : (HeightOneSpectrum.adicCompletionIntegers F v.val)ˣ,
          sLocalFiniteRestriction v (chart(χ) s)
            (Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom y) = 1) := by
    have hunit_norm (y : (HeightOneSpectrum.adicCompletionIntegers F v.val)ˣ) :
        ‖((Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom y :
            (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F)‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
          (a := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom y)).mp
          ⟨y.val.property, y.inv.property⟩)
    constructor <;> intro h y
    · have hy := h y
      rw [htwist_eval, hunit_norm y, Complex.ofReal_one, Complex.one_cpow, mul_one] at hy
      exact hy
    · rw [htwist_eval, hunit_norm y, Complex.ofReal_one, Complex.one_cpow, mul_one]
      exact h y
  have hlt : meromorphicOrderAt
      (fun z : ℂ ↦ finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ (chart(χ) s) z))) 0 < 0 :=
    (Finset.mem_filter.mp _hv).2
  have hunr : ∀ y : (HeightOneSpectrum.adicCompletionIntegers F v.val)ˣ,
      sLocalFiniteRestriction v (chart(χ) s)
        (Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom y) = 1 := by
    by_contra hnot
    have hconst : (fun z : ℂ ↦ finiteLocalEulerFactor v.val
        (sLocalFiniteRestriction v (twistₛ (chart(χ) s) z))) = fun _ ↦ (1 : ℂ) := by
      funext z
      unfold finiteLocalEulerFactor
      rw [ite_eq_right (fun hz ↦ hnot ((hunr_iff z).mp hz))]
    rw [hconst] at hlt
    exact not_lt_of_ge (analyticAt_const.meromorphicOrderAt_nonneg) hlt
  let hπ := (Valued.v : Valuation (v.val.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v.val.adicCompletion F)ˣ := Units.mk0 hπ.choose hπ.choose_spec.ne_zero
  have hπ_norm : ‖(π : v.val.adicCompletion F)‖ = ((v.val.asIdeal.absNorm : ℝ)⁻¹) := by
    have hval : Valued.v (π : v.val.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
      hπ.choose_spec.trans (congrArg Units.val
        (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
          (v.val.valuedAdicCompletion_surjective F)))
    rw [FinitePlace.norm_def, hval, WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
    simp
  have hratio_norm : ‖((u * π⁻¹ : (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F)‖ = 1 := by
    rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, _hu, hπ_norm]
    exact mul_inv_cancel₀ hqinv_pos.ne'
  have hratio_mem : (u * π⁻¹ : (v.val.adicCompletion F)ˣ).val ∈
        HeightOneSpectrum.adicCompletionIntegers F v.val ∧
      ((u * π⁻¹ : (v.val.adicCompletion F)ˣ)⁻¹).val ∈
        HeightOneSpectrum.adicCompletionIntegers F v.val :=
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := u * π⁻¹)).mpr (Valued.toNormedField.norm_eq_one_iff.mp hratio_norm)
  let y : (HeightOneSpectrum.adicCompletionIntegers F v.val)ˣ :=
    ⟨⟨(u * π⁻¹ : (v.val.adicCompletion F)ˣ).val, hratio_mem.1⟩,
     ⟨((u * π⁻¹ : (v.val.adicCompletion F)ˣ)⁻¹).val, hratio_mem.2⟩,
     Subtype.ext (Units.mul_inv (u * π⁻¹)),
     Subtype.ext (Units.inv_mul (u * π⁻¹))⟩
  have hy_eq : Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom y =
      u * π⁻¹ := by
    ext
    rfl
  have hcu_eq_cπ : sLocalFiniteRestriction v (chart(χ) s) u = sLocalFiniteRestriction v (chart(χ) s) π := by
    have h1 := hunr y
    rw [hy_eq, map_mul, map_inv] at h1
    exact eq_of_mul_inv_eq_one h1
  have hcu : sLocalFiniteRestriction v (chart(χ) s) u = 1 := by
    by_contra hne
    have hfun : (fun z : ℂ ↦ finiteLocalEulerFactor v.val
        (sLocalFiniteRestriction v (twistₛ (chart(χ) s) z))) =
        fun z : ℂ ↦ (1 - sLocalFiniteRestriction v (chart(χ) s) u *
          Complex.exp (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * z))⁻¹ := by
      funext z
      unfold finiteLocalEulerFactor
      rw [ite_eq_left ((hunr_iff z).mpr hunr)]
      change (1 - sLocalFiniteRestriction v (twistₛ (chart(χ) s) z) π)⁻¹ = _
      rw [htwist_eval, hπ_norm, ← hcu_eq_cπ,
        Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hqinv_pos.ne'),
        ← Complex.ofReal_log hqinv_pos.le, Real.log_inv]
      push_cast
      rfl
    rw [hfun] at hlt
    have hden_ne : 1 - sLocalFiniteRestriction v (chart(χ) s) u *
        Complex.exp (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * 0) ≠ 0 := by
      simpa [sub_ne_zero] using Ne.symm hne
    have hdiff : Differentiable ℂ (fun z : ℂ ↦ 1 - sLocalFiniteRestriction v (chart(χ) s) u *
        Complex.exp (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * z)) :=
      (differentiable_const 1).sub
        ((differentiable_const _).mul (((differentiable_const _).mul differentiable_id).cexp))
    have han : AnalyticAt ℂ (fun z : ℂ ↦ (1 - sLocalFiniteRestriction v (chart(χ) s) u *
        Complex.exp (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * z))⁻¹) 0 :=
      (hdiff.analyticAt 0).inv hden_ne
    exact not_lt_of_ge han.meromorphicOrderAt_nonneg hlt
  have hmod_u : (((mₛ (finAt u) : ℝ≥0) : ℝ) : ℂ) = (((v.val.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [hmod_val u, _hu]
  have hcpow_eq : (((v.val.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) ^ s =
      (((v.val.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) := by
    have h1 : ((χ (finAt u) : Circle) : ℂ) * (((v.val.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) ^ s = 1 := by
      rw [← hmod_u]
      exact hcu
    have h2 : ((χ (finAt u) : Circle) : ℂ) *
        (((v.val.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) = 1 := by
      rw [← hmod_u]
      exact _ht.2
    exact mul_left_cancel₀ (Circle.coe_ne_zero (χ (finAt u))) (h1.trans h2.symm)
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hqinv_pos.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hqinv_pos.ne'),
    ← Complex.ofReal_log hqinv_pos.le, Real.log_inv] at hcpow_eq
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hcpow_eq
  have hlogC : (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hlog.ne'
  have hs_eq : s = ((((-k : ℤ) : ℝ) * period(v) - t : ℝ) : ℂ) * Complex.I := by
    have hmul : (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ)) * s =
        (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ)) *
          (((((-k : ℤ) : ℝ) * period(v) - t : ℝ) : ℂ) * Complex.I) := by
      rw [show ((-(Real.log (v.val.asIdeal.absNorm : ℝ)) : ℝ) : ℂ) =
          -(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) by rw [Complex.ofReal_neg]] at hk
      rw [hk]
      simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
        Int.cast_neg, Complex.ofReal_neg, Complex.ofReal_intCast]
      have hdiv : (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) *
          (2 * (Real.pi : ℂ) / (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ)) = 2 * (Real.pi : ℂ) :=
        mul_div_cancel₀ _ hlogC
      linear_combination (k : ℂ) * Complex.I * hdiv.symm
    exact mul_left_cancel₀ (neg_ne_zero.mpr hlogC) hmul
  have hinj : Injective (chart(χ)) := by
    intro s₁ s₂ he
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
    let P := quasiCharacterNormTwist (MonoidHom.id ℝ≥0ˣ) continuous_id 1 s₁
    have hs₁ (r : ℝ≥0ˣ) : P r = ((r.val : ℝ) : ℂ) ^ s₁ := one_mul _
    apply (existsUnique_complexPower P).unique hs₁
    intro r
    have h := DFunLike.congr_fun he (σ r)
    change (χ (σ r) : ℂ) * (((mₛ (σ r) : ℝ≥0) : ℝ) : ℂ) ^ s₁ =
      (χ (σ r) : ℂ) * (((mₛ (σ r) : ℝ≥0) : ℝ) : ℂ) ^ s₂ at h
    rw [hσ r] at h
    exact (hs₁ r).trans (mul_left_cancel₀ (Circle.coe_ne_zero _) h)
  refine ⟨-k, ?_, ?_⟩
  · rw [hs_eq]
  · intro n hn
    have h1 := congrArg Complex.im (hinj hn)
    rw [hs_eq] at h1
    simp only [Complex.mul_I_im, Complex.ofReal_re] at h1
    have hper_pos : (0 : ℝ) < period(v) := div_pos (by positivity) hlog
    have hn_cast : (n : ℝ) = ((-k : ℤ) : ℝ) :=
      mul_right_cancel₀ hper_pos.ne' (by linarith)
    exact Int.cast_injective hn_cast

/-- Paper: Discussion after (7.3.1.11), p. 344.
At a common pole, the phase difference is an integer combination of the two local periods.
Deviation: The periods use the residue-field cardinalities of the places. The phase
difference need not be an integer multiple of the period for the rational prime. -/
theorem sLocalOrbitalPhase_sub (χ : PontryaginDual Jₛ) (p : Vℚ)
    (_hS : IsSaturatedPlaceSet S) (v w : S)
    (_hv : v.val ∈ Sₚ(p)) (_hw : w.val ∈ Sₚ(p))
    (uᵥ : (v.val.adicCompletion F)ˣ) (u_w : (w.val.adicCompletion F)ˣ)
    (_hᵥ : uniformizerNorm(v, uᵥ)) (_h_w : uniformizerNorm(w, u_w))
    (tᵥ t_w : ℝ) (_htᵥ : phase(χ, v, uᵥ, tᵥ)) (_ht_w : phase(χ, w, u_w, t_w))
    (c : Xₛ) (_hc : ∃ s, c = chart(χ) s)
    (_hvc : v ∈ sLocalFinitePolePlaces c) (_hwc : w ∈ sLocalFinitePolePlaces c) :
    ∃ a b : ℤ, tᵥ - t_w = (a : ℝ) * period(v) - (b : ℝ) * period(w) := by
  have hinj : Injective (chart(χ)) := by
    intro s t he
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
    let P := quasiCharacterNormTwist (MonoidHom.id ℝ≥0ˣ) continuous_id 1 s
    have hs (u : ℝ≥0ˣ) : P u = ((u.val : ℝ) : ℂ) ^ s := one_mul _
    apply (existsUnique_complexPower P).unique hs
    intro u
    have h := DFunLike.congr_fun he (σ u)
    change (χ (σ u) : ℂ) * (((mₛ (σ u) : ℝ≥0) : ℝ) : ℂ) ^ s =
      (χ (σ u) : ℂ) * (((mₛ (σ u) : ℝ≥0) : ℝ) : ℂ) ^ t at h
    rw [hσ u] at h
    exact (hs u).trans (mul_left_cancel₀ (Circle.coe_ne_zero _) h)
  obtain ⟨a, ha⟩ := (existsUnique_sLocalOrbitalLatticeIndex χ v uᵥ _hᵥ tᵥ _htᵥ c _hc _hvc).exists
  obtain ⟨b, hb⟩ := (existsUnique_sLocalOrbitalLatticeIndex χ w u_w _h_w t_w _ht_w c _hc _hwc).exists
  refine ⟨a, b, ?_⟩
  have he := congrArg Complex.im (hinj (ha.symm.trans hb))
  simp only [Complex.mul_I_im, Complex.ofReal_re] at he
  linarith

local notation "fourierZeta(" c ")" =>
  (fun (f : ℬₛ) (z : ℂ) ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f)
    (dualₛ (twistₛ c z)))

/-- A selected finite pole lies in the closed left half-plane of any unitary chart. -/
private theorem sLocalOrbitalFourierZeta_chart {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) : ∃ (χ : PontryaginDual Jₛ) (a : ℂ),
      j.val.1 = chart(χ) a ∧ a.re ≤ 0 := by
  classical
  obtain ⟨χ, a, ha⟩ := exists_sLocalNormTwist (F := F) (S := S) j.val.1
  refine ⟨χ, a, ha.symm, ?_⟩
  have hm : 0 < sLocalRhoPoleOrder j.val.1 := by
    have hle : sLocalFinitePoleMultiplicity T j.val.1 ≤ sLocalRhoPoleOrder j.val.1 := by
      rw [sLocalRhoPoleOrder_eq_card_polePlaces]
      exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
    exact lt_of_le_of_lt (Nat.zero_le j.val.2) (j.property.2.trans_le hle)
  by_contra h
  have hpos : 0 < a.re := lt_of_not_ge h
  have hA : AnalyticAt ℂ (fun z ↦ sLocalRhoFactor (twistₛ j.val.1 z)) 0 := by
    have h := (sLocalRhoFactor_analyticOn χ a hpos).comp_of_eq
      (f := fun z : ℂ ↦ z + a) (x := 0) (by fun_prop) (zero_add a)
    simpa only [← ha, normTwist_normTwist, Function.comp_def] using h
  have hb : sLocalIdelicOrderBound j.val.1 = 0 :=
    min_eq_left hA.meromorphicOrderAt_nonneg
  simp [sLocalRhoPoleOrder, hb] at hm

/-- On the reflected convergence half-plane, the continued zeta function is analytic. -/
private theorem sLocalOrbitalFourierZeta_analyticOn (χ : PontryaginDual Jₛ) (a : ℂ)
    (f : ℬₛ) : AnalyticOnNhd ℂ
      (fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chart(χ⁻¹) (1 - (z + a))))
      {z : ℂ | 0 < (1 - (z + a)).re} := by
  have hZ : AnalyticOnNhd ℂ
      (fun s ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chart(χ⁻¹) s))
      {s : ℂ | 0 < s.re} :=
    (sLocalIdelicZetaIntegral_analyticOn (sAdeleSchwartzFourier f) χ⁻¹).congr
      (isOpen_Ioi.preimage Complex.continuous_re)
      (fun z hz ↦ (sLocalIdelicZFunction_eq_integral _ ⟨χ⁻¹, z, hz, rfl⟩).symm)
  intro z hz
  exact (hZ _ hz).comp (f := fun w : ℂ ↦ 1 - (w + a)) (by fun_prop)

/-- Paper: Equation (7.3.1.14), p. 344.
The reflected Fourier zeta transform is holomorphic near each selected finite pole
of the correcting factor. Its derivatives therefore evaluate the analytic germ there. -/
theorem sLocalOrbitalFourierZeta_analyticAt {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) (f : ℬₛ) :
    AnalyticAt ℂ (fourierZeta(j.val.1) f) 0 := by
  obtain ⟨χ, a, ha, hle⟩ := sLocalOrbitalFourierZeta_chart j
  have hpos : 0 < (1 - ((0 : ℂ) + a)).re := by simp; linarith
  simpa only [ha, normTwist_normTwist, sLocal_dual_normTwist] using
    sLocalOrbitalFourierZeta_analyticOn χ a f 0 hpos

section

universe u

/-- Difference quotients of continuous functionals give continuous jets on a barrelled space. -/
private theorem orbitalFourierJet_exists_continuousLinear
    {E : Type u} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [BarrelledSpace ℂ E] (Φ : E → ℂ → ℂ) {U : Set ℂ}
    (hU : IsOpen U) (hΦ : ∀ f, AnalyticOnNhd ℂ (Φ f) U)
    (hbase : ∀ z ∈ U, ∃ L : E →L[ℂ] ℂ, ∀ f, L f = Φ f z)
    (n : ℕ) {z : ℂ} (hz : z ∈ U) :
    ∃ L : E →L[ℂ] ℂ, ∀ f, L f = iteratedDeriv n (Φ f) z := by
  classical
  have analyticDeriv (f : E) {x : ℂ} (hx : x ∈ U) (k : ℕ) :
      AnalyticAt ℂ (iteratedDeriv k (Φ f)) x := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hΦ f x hx
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
  induction n generalizing z with
  | zero => simpa only [iteratedDeriv_zero] using hbase z hz
  | succ n ih =>
    let A (y : ℂ) : E →L[ℂ] ℂ := if hy : y ∈ U then (ih hy).choose else 0
    have hA {y : ℂ} (hy : y ∈ U) (f : E) : A y f = iteratedDeriv n (Φ f) y := by
      simpa only [A, dite_eq_left hy] using (ih hy).choose_spec f
    let D (y : ℂ) := (y - z)⁻¹ • (A y - A z)
    have hlim : Tendsto (fun y f ↦ D y f) (𝓝[≠] z)
        (𝓝 fun f ↦ iteratedDeriv (n + 1) (Φ f) z) := by
      refine tendsto_pi_nhds.mpr fun f ↦ ?_
      rw [iteratedDeriv_succ]
      refine (analyticDeriv f hz n).differentiableAt.hasDerivAt.tendsto_slope.congr' ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hz)] with y hy
      simp only [D, smul_apply, sub_apply,
        hA hy, hA hz, slope, vsub_eq_sub]
    exact ⟨continuousLinearMapOfTendsto D hlim, fun _ ↦ rfl⟩

end

/-- Paper: Equation (7.3.1.14), p. 344.
On S-adelic tests the Fourier jet is continuous and complex linear. -/
theorem sLocalOrbitalFourierJet_continuous_linear {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) :
    let D := fun f : ℬₛ ↦ iteratedDeriv j.val.2 (fourierZeta(j.val.1) f) 0
    Continuous D ∧ IsLinearMap ℂ D := by
  obtain ⟨χ, a, ha, hle⟩ := sLocalOrbitalFourierZeta_chart j
  let U := {z : ℂ | 0 < (1 - (z + a)).re}
  let Φ := fun (f : ℬₛ) (z : ℂ) ↦
    sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chart(χ⁻¹) (1 - (z + a)))
  have hU : IsOpen U := isOpen_lt continuous_const (by fun_prop)
  have hzero : (0 : ℂ) ∈ U := by change 0 < (1 - (0 + a)).re; simp; linarith
  have hbase : ∀ z ∈ U, ∃ L : ℬₛ →L[ℂ] ℂ, ∀ f, L f = Φ f z := by
    intro z hz
    obtain ⟨T, hT⟩ := sLocal_fourier_continuousLinear (F := F) (S := S)
    obtain ⟨Z, hZ⟩ := sLocalIdelicZetaIntegral_tempered
      (chart(χ⁻¹) (1 - (z + a))) ⟨χ⁻¹, _, hz, rfl⟩
    refine ⟨Z.comp T, fun f ↦ ?_⟩
    change Z (T f) = _
    rw [hT, hZ]
    exact (sLocalIdelicZFunction_eq_integral _ ⟨χ⁻¹, _, hz, rfl⟩).symm
  let : BarrelledSpace ℂ ℬₛ := (sAdeleSchwartz_montel (F := F) S).1
  obtain ⟨L, hL⟩ := orbitalFourierJet_exists_continuousLinear Φ hU
    (sLocalOrbitalFourierZeta_analyticOn χ a) hbase j.val.2 hzero
  have heq : (fun f : ℬₛ ↦ iteratedDeriv j.val.2 (fourierZeta(j.val.1) f) 0) = L := by
    funext f
    rw [hL]
    simp only [Φ, ha, normTwist_normTwist, sLocal_dual_normTwist]
  change Continuous _ ∧ IsLinearMap ℂ _
  rw [heq]
  exact ⟨L.continuous, L.toLinearMap.isLinear⟩

local notation "fourierJet(" j ")" =>
  (⟨(sLocalOrbitalFourierJet_continuous_linear j).2.mk' _,
    (sLocalOrbitalFourierJet_continuous_linear j).1⟩ : StrongDual ℂ ℬₛ)

/-- A homogeneous theta-kernel test has zero zeta function throughout its component. -/
private theorem orbitalFourierJet_kernel_zeta_zero (ω : PontryaginDual J₁) (c : Xₛ)
    (hc : onComponent(c, ω)) (f : ℬₛ) (hf : f ∈ Kₛ(ω))
    (χ : PontryaginDual Jₛ) (a : ℂ) (ha : chart(χ) a = c) :
    (fun z : ℂ ↦ sLocalIdelicZFunction f (chart(χ) z)) = 0 := by
  have hv := (mem_sLocalHomogeneousAdelicTheta_ker_iff (F := F) (S := S) ω f).mp hf
  have hω := (congrArg (normOneRestriction mₛ) ha).trans hc
  have hr (z : ℂ) (g : J₁) : normOneRestriction mₛ (chart(χ) z) g = (ω g : ℂ) :=
    (normOneRestriction_unitaryChart mₛ (isProperMap_sIdeleQuotientNorm F S).continuous χ z g).trans
      ((normOneRestriction_unitaryChart mₛ (isProperMap_sIdeleQuotientNorm F S).continuous χ a g).symm.trans
        (DFunLike.congr_fun hω g))
  refine eq_of_agree_rightHalf (sLocalIdelicZFunction_meromorphic f χ)
    (fun _ _ ↦ analyticAt_const.meromorphicNFAt) 0 fun z hz ↦ ?_
  let d := (⟨chart(χ) z, sLocalOrderBound_positive χ hz⟩ :
    {q : Xₛ // 0 ≤ sLocalIdelicOrderBound q})
  exact (sLocalIdelicMellin_apply f d).symm.trans (hv d (hr z))

/-- The functional equation transfers identically zero zeta functions to their reflected Fourier germs. -/
private theorem orbitalFourierJet_kernel_reflected_zero (χ : PontryaginDual Jₛ) (f : ℬₛ)
    (hf : (fun z : ℂ ↦ sLocalIdelicZFunction f (chart(χ) z)) = 0) :
    (fun z : ℂ ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chart(χ⁻¹) (1 - z)))
      =ᶠ[codiscrete ℂ] 0 := by
  let Z (g : ℬₛ) (η : PontryaginDual Jₛ) (z : ℂ) := sLocalIdelicZFunction g (chart(η) z)
  let R (z : ℂ) := sLocalRhoFactor (chart(χ) z)
  let D (z : ℂ) := Z (sAdeleSchwartzFourier f) χ⁻¹ (1 - z)
  have hZ (g : ℬₛ) (η : PontryaginDual Jₛ) (z : ℂ) : MeromorphicAt (Z g η) z :=
    ((sLocalIdelicZFunction_meromorphic g η) (mem_univ z)).meromorphicAt
  have hEq : Z f χ =ᶠ[codiscrete ℂ] R * D := by
    apply sLocal_meromorphic_identity (hZ f χ) (fun z ↦ (sLocalRhoFactor_meromorphic χ z).mul
      ((hZ _ _ (1 - z)).comp_analyticAt (analyticAt_const.sub analyticAt_id)))
    intro z hz
    have hd : 0 < (1 - z).re := by simp; linarith [hz.2]
    change sLocalIdelicZFunction f (chart(χ) z) =
      R z * sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chart(χ⁻¹) (1 - z))
    refine (sLocalIdelicZFunction_eq_integral f ⟨χ, z, hz.1, rfl⟩).trans ?_
    refine (sLocalIdelicZetaIntegral_functionalEquation f χ z hz).trans ?_
    refine (congrArg (fun c ↦ R z * sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f) c)
      (sLocal_dual_normTwist χ z)).trans ?_
    exact congrArg (R z * ·)
      (sLocalIdelicZFunction_eq_integral (sAdeleSchwartzFourier f) ⟨χ⁻¹, 1 - z, hd, rfl⟩).symm
  filter_upwards [hEq, sLocalRhoFactor_mul_dual χ] with z hz hprod
  have hr : R z ≠ 0 := left_ne_zero_of_mul
    (hprod.trans_ne ((Group.isUnit (QuotientGroup.mk (-1 : (SAdeleRing F S)ˣ) : Jₛ)).map
      (chart(χ) z)).ne_zero)
  have hzero : R z * D z = 0 := hz.symm.trans (congrFun hf z)
  exact (mul_eq_zero.mp hzero).resolve_left hr

/-- Paper: Equation (7.3.1.14), p. 344.
The Fourier jet annihilates the kernel of the homogeneous theta map. -/
theorem sLocalOrbitalFourierJet_ker {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) :
    Kₛ(ω) ≤ (fourierJet(j)).ker := by
  intro f hf
  obtain ⟨χ, a, ha, _⟩ := sLocalOrbitalFourierZeta_chart j
  have hzero := orbitalFourierJet_kernel_zeta_zero ω j.val.1 j.property.1 f hf χ a ha.symm
  have hcod := orbitalFourierJet_kernel_reflected_zero χ f hzero
  have hshift : Tendsto (fun z : ℂ ↦ z + a) (𝓝[≠] 0) (𝓝[≠] a) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_id.add continuous_const : Continuous fun z : ℂ ↦ z + a).tendsto'
        0 a (zero_add a)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact fun h ↦ hz (add_eq_right.mp h)
  have hev : fourierZeta(j.val.1) f =ᶠ[𝓝[≠] 0] 0 := by
    filter_upwards [hshift.eventually (hcod.filter_mono (nhdsNE_le_codiscrete a))] with z hz
    simpa only [ha, normTwist_normTwist, sLocal_dual_normTwist, Pi.zero_apply] using hz
  have hnhds := (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (sLocalOrbitalFourierZeta_analyticAt j f).continuousAt continuousAt_const).mp hev
  change iteratedDeriv j.val.2 (fourierZeta(j.val.1) f) 0 = 0
  exact (hnhds.iteratedDeriv_eq j.val.2).trans iteratedDeriv_const_zero

/-- Paper: Equations (7.3.1.13)–(7.3.1.14), p. 344.
The indexed Fourier functional is the jet of the reflected zeta transform at its center.
It differentiates in the original norm direction, as in the printed formula. -/
def sLocalOrbitalFourierJet {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) : StrongDual ℂ (Θₛ(ω)) :=
  (Kₛ(ω)).liftQL (fourierJet(j)) (sLocalOrbitalFourierJet_ker j)

/-- Paper: Equation (7.3.1.14), p. 344.
On a test representative the Fourier jet evaluates to the stated derivative. -/
theorem sLocalOrbitalFourierJet_mk {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) (f : ℬₛ) :
    sLocalOrbitalFourierJet j ((Kₛ(ω)).mkQL f) =
      iteratedDeriv j.val.2 (fourierZeta(j.val.1) f) 0 := rfl

local notation "Idx(" p ", " ω ")" => I(Sₚ(p), ω)

section PrimaryBases

/-- Paper: Theorem 7.3.1.6(1), p. 345.
Each primary polar functional vanishes on the primary principal-value image, so
it lies in the image of the transpose of the quotient map. -/
theorem sLocalOrbitalPrincipalPart_range_le_ker
    (p : Vℚ) (ω : PontryaginDual J₁) (j : Idx(p, ω)) :
    Rₚ(p, ω) ≤
      (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j).ker :=
  sLocalOrbitalPrincipalPart_range_le_ker_range ((Kₛ(ω)).mkQ) (Submodule.mkQ_surjective _)
    (sLocalHomogeneousThetaPrincipalValue hₚ(p) ω)
    (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j)
    (sLocalOrbitalPrincipalPart_range_le_ker_test hₚ(p) ω j)

/-- Paper: Theorem 7.3.1.6(1), p. 345.
Each primary Fourier functional vanishes on the primary principal-value image, so
it lies in the image of the transpose of the quotient map. -/
theorem sLocalOrbitalFourierJet_range_le_ker
    (p : Vℚ) (ω : PontryaginDual J₁) (j : Idx(p, ω)) :
    Rₚ(p, ω) ≤
      (sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j).ker := by
  classical
  apply sLocalOrbitalPrincipalPart_range_le_ker_range ((Kₛ(ω)).mkQ) (Submodule.mkQ_surjective _)
    (sLocalHomogeneousThetaPrincipalValue hₚ(p) ω)
    (sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j)
  intro f
  let c := j.val.1
  let g := sAdelePrincipalValue F hₚ(p) f
  rw [show sLocalHomogeneousThetaPrincipalValue hₚ(p) ω ((Kₛ(ω)).mkQ f) =
      (Kₛ(ω)).mkQL g from sLocalHomogeneousThetaPrincipalValue_mk hₚ(p) ω f,
    sLocalOrbitalFourierJet_mk]
  obtain ⟨χ, a, hx, -⟩ := sLocalOrbitalFourierZeta_chart j
  let Q (z : ℂ) := ∏ v : S, if v.val ∈ Sₚ(p) then
    (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹ else 1
  let Z (v : ℬₛ) (η : PontryaginDual Jₛ) (z : ℂ) := sLocalIdelicZFunction v (chart(η) z)
  let R (z : ℂ) := sLocalRhoFactor (chart(χ) z)
  let D (v : ℬₛ) (z : ℂ) := Z (sAdeleSchwartzFourier v) χ⁻¹ (1 - z)
  have heq (v : ℬₛ) : Z v χ =ᶠ[codiscrete ℂ] R * D v := by
    have hZ (w : ℬₛ) (η : PontryaginDual Jₛ) (z : ℂ) : MeromorphicAt (Z w η) z :=
      ((sLocalIdelicZFunction_meromorphic w η) (mem_univ z)).meromorphicAt
    apply sLocal_meromorphic_identity (hZ v χ) (fun z ↦ (sLocalRhoFactor_meromorphic χ z).mul
      ((hZ _ _ (1 - z)).comp_analyticAt (analyticAt_const.sub analyticAt_id)))
    intro z hz
    have hd : 0 < (1 - z).re := by simp; linarith [hz.2]
    exact (sLocalIdelicZFunction_eq_integral v ⟨χ, z, hz.1, rfl⟩).trans <|
      (sLocalIdelicZetaIntegral_functionalEquation v χ z hz).trans <|
      (congrArg (fun d ↦ R z * sLocalIdelicZetaIntegral (sAdeleSchwartzFourier v) d)
        (sLocal_dual_normTwist χ z)).trans <| congrArg (R z * ·)
        (sLocalIdelicZFunction_eq_integral (sAdeleSchwartzFourier v) ⟨χ⁻¹, 1 - z, hd, rfl⟩).symm
  have hc : ∀ᶠ z : ℂ in codiscrete ℂ, D g z = D f z *
      ∏ v : S, if v.val ∈ Sₚ(p) then
        (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chart(χ) z)))⁻¹ else 1 := by
    filter_upwards [heq g, heq f, sLocalRhoFactor_mul_dual χ,
      sLocalIdelicZFunction_principalValue Sₚ(p) hₚ(p) f χ] with z hg hf hr hpv
    have hn : R z ≠ 0 := left_ne_zero_of_mul
      (hr.trans_ne ((Group.isUnit (QuotientGroup.mk (-1 : (SAdeleRing F S)ˣ) : Jₛ)).map
        (chart(χ) z)).ne_zero)
    apply mul_left_cancel₀ hn
    rw [← mul_assoc, ← show Z f χ z = R z * D f z from hf,
      ← show Z g χ z = R z * D g z from hg]
    change sLocalIdelicZFunction (sAdelePrincipalValue F hₚ(p) f) _ = sLocalIdelicZFunction f _ * _
    rw [hpv, div_eq_mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    split_ifs <;> simp
  have ht : Tendsto (fun z : ℂ ↦ z + a) (𝓝[≠] 0) (𝓝[≠] a) := by
    have h : Tendsto (fun z : ℂ ↦ z + a) (𝓝[≠] 0) (𝓝[≠] (0 + a)) :=
      ((Homeomorph.addRight a).map_punctured_nhds_eq 0).le
    simpa only [zero_add] using h
  have hprod : fourierZeta(c) g =ᶠ[𝓝[≠] 0] fourierZeta(c) f * Q := by
    filter_upwards [ht.eventually (nhdsNE_le_codiscrete a hc)] with z hz
    simp only [c, hx, Q, normTwist_normTwist, sLocal_dual_normTwist, Pi.mul_apply]
    refine hz.trans (congrArg (D f (z + a) * ·) ?_)
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    split_ifs <;> rfl
  obtain ⟨hQ, horder⟩ := sLocalOrbitalPrincipalPart_range_le_ker_prod Sₚ(p) c
  have hg := sLocalOrbitalFourierZeta_analyticAt j g
  have hf := sLocalOrbitalFourierZeta_analyticAt j f
  have hm : ((sLocalFinitePoleMultiplicity Sₚ(p) c : ℕ) : WithTop ℤ) ≤
      meromorphicOrderAt (fourierZeta(c) g) 0 := by
    rw [meromorphicOrderAt_congr hprod, meromorphicOrderAt_mul hf.meromorphicAt hQ]
    exact horder.trans (le_add_of_nonneg_left hf.meromorphicOrderAt_nonneg)
  have ha : (sLocalFinitePoleMultiplicity Sₚ(p) c : ℕ∞) ≤ analyticOrderAt (fourierZeta(c) g) 0 := by
    rw [hg.meromorphicOrderAt_eq] at hm
    cases ho : analyticOrderAt (fourierZeta(c) g) 0 using ENat.recTopCoe with
    | top => exact le_top
    | coe n =>
      rw [ho, ENat.map_natCast] at hm
      exact_mod_cast hm
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg).mp ha j.val.2 j.property.2

/-- a unitary chart covers exactly the chosen norm-one component. -/
private theorem sLocalOrbitalIndex_enumerable_or_empty_chart
    {F : Type*} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))} (ω : PontryaginDual (((sIdeleQuotientNorm F S)).ker)) :
    ∃ χ : PontryaginDual (SIdeleQuotient F S),
      (∀ z : ℂ, (normOneRestriction (sIdeleQuotientNorm F S) (((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)) z) = (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω)) ∧
      ∀ d : (QuasiCharacter (SIdeleQuotient F S)), (normOneRestriction (sIdeleQuotientNorm F S) d = (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω) → ∃ z : ℂ, ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)) z = d := by
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨χ, hu, ht⟩ := exists_character_on_split (sIdeleQuotientNorm F S)
    (isProperMap_sIdeleQuotientNorm F S).continuous σ hσ ω 1
  refine ⟨χ, fun z ↦ ContinuousMonoidHom.ext fun u ↦
    (normOneRestriction_unitaryChart (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous χ z u).trans
      (congrArg Subtype.val (hu u)), ?_⟩
  intro d hd
  obtain ⟨z, hz, -⟩ := existsUnique_complexPower (d.comp σ)
  refine ⟨z, ContinuousMonoidHom.ext fun g ↦ ?_⟩
  let t := (sIdeleQuotientNorm F S) g
  let k : (((sIdeleQuotientNorm F S)).ker) := ⟨g / σ t, by change (sIdeleQuotientNorm F S) (g / σ t) = 1; rw [map_div, hσ]; exact div_self' _⟩
  have hg : k.val * σ t = g := div_mul_cancel _ _
  have hχg : χ g = ω k := by
    calc χ g = χ k.val * χ (σ t) := (congrArg χ hg.symm).trans (map_mul χ _ _)
         _ = ω k := by rw [hu, ht]; exact mul_one _
  have hdk : d k.val = (ω k : ℂ) := DFunLike.congr_fun hd k
  have hdt : d (σ t) = (((t : ℝ≥0) : ℝ) : ℂ) ^ z := hz t
  change (χ g : ℂ) * (((t : ℝ≥0) : ℝ) : ℂ) ^ z = d g
  rw [hχg, ← hdk, ← hdt, ← map_mul, hg]

/-- a local uniformizer has norm equal to the reciprocal residue cardinality. -/
private theorem sLocalOrbitalIndex_enumerable_or_empty_uniformizer
    {F : Type*} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))} (v : S) :
    ∃ u : (v.val.adicCompletion F)ˣ,
      ‖(u : v.val.adicCompletion F)‖ = ((v.val.asIdeal.absNorm : ℝ)⁻¹) := by
  let hπ := (Valued.v : Valuation (v.val.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  refine ⟨Units.mk0 hπ.choose hπ.choose_spec.ne_zero, ?_⟩
  have hval : Valued.v (hπ.choose : v.val.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
    hπ.choose_spec.trans (congrArg Units.val
      (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (v.val.valuedAdicCompletion_surjective F)))
  change ‖(hπ.choose : v.val.adicCompletion F)‖ = _
  rw [FinitePlace.norm_def, hval, WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
  simp

/-- Paper: Theorem 7.3.1.6(2), p. 345.
Primary pole centers on one norm component form a countable set. -/
private theorem sLocalOrbitalIndex_enumerable_or_empty_countable_centers
    {F : Type*} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))} (p : (HeightOneSpectrum (𝓞 ℚ))) (ω : PontryaginDual (((sIdeleQuotientNorm F S)).ker)) :
    Countable {c : (QuasiCharacter (SIdeleQuotient F S)) // (normOneRestriction (sIdeleQuotientNorm F S) c = (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω) ∧
      0 < sLocalFinitePoleMultiplicity ((sLocalPrimaryPlaces S p)) c} := by
  classical
  obtain ⟨χ, hcomp, hcover⟩ := sLocalOrbitalIndex_enumerable_or_empty_chart ω
  choose u hu using (sLocalOrbitalIndex_enumerable_or_empty_uniformizer (F := F) (S := S))
  have phases := fun v : S ↦ (existsUnique_sLocalOrbitalPhase χ v (u v) (hu v)).exists
  choose t ht using phases
  let lattice : S × ℤ → (QuasiCharacter (SIdeleQuotient F S)) := fun j ↦ ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ))
    (((j.2 : ℝ) * (2 * Real.pi / Real.log (j.1.val.asIdeal.absNorm : ℝ)) - t j.1 : ℝ) * Complex.I)
  have hsub : {c : (QuasiCharacter (SIdeleQuotient F S)) | (normOneRestriction (sIdeleQuotientNorm F S) c = (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω) ∧
      0 < sLocalFinitePoleMultiplicity ((sLocalPrimaryPlaces S p)) c} ⊆ Set.range lattice := by
    intro c hc
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hc.2
    obtain ⟨s, hs⟩ := hcover c hc.1
    obtain ⟨n, hn⟩ := (existsUnique_sLocalOrbitalLatticeIndex χ v (u v) (hu v)
      (t v) (ht v) c ⟨s, hs.symm⟩ (Finset.mem_filter.mp hv).1).exists
    exact ⟨(v, n), hn.symm⟩
  exact ((Set.countable_range lattice).mono hsub).to_subtype

/-- integer imaginary twists of the local period preserve the Euler factor. -/
private theorem sLocalOrbitalIndex_enumerable_or_empty_periodic
    {F : Type*} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))} (v : S) (c : (QuasiCharacter (SIdeleQuotient F S))) (n : ℕ) :
    finiteLocalEulerFactor v.val (sLocalFiniteRestriction v
      ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) c (((n : ℝ) * (2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)) : ℝ) * Complex.I))) =
      finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c) := by
  classical
  let a : ℂ := ((n : ℝ) * (2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)) : ℝ) * Complex.I
  let ι := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom
  have hunit (u : (v.val.adicCompletionIntegers F)ˣ) :
      sLocalFiniteRestriction v ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) c a) (ι u) = sLocalFiniteRestriction v c (ι u) := by
    rw [sLocalOrbitalPrincipalPart_range_le_ker_restrict]
    have hu : ‖((ι u : (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F)‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
          (a := ι u)).mp ⟨u.val.property, u.inv.property⟩)
    rw [hu, Complex.ofReal_one, Complex.one_cpow, mul_one]
  have key : (∀ u, sLocalFiniteRestriction v ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) c a) (ι u) = 1) ↔
      (∀ u, sLocalFiniteRestriction v c (ι u) = 1) := forall_congr' fun u ↦ by rw [hunit u]
  let hπ := (Valued.v : Valuation (v.val.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v.val.adicCompletion F)ˣ := Units.mk0 hπ.choose hπ.choose_spec.ne_zero
  have hπ_norm : ‖(π : v.val.adicCompletion F)‖ = ((v.val.asIdeal.absNorm : ℝ)⁻¹) := by
    have hval : Valued.v (π : v.val.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
      hπ.choose_spec.trans (congrArg Units.val
        (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
          (v.val.valuedAdicCompletion_surjective F)))
    rw [FinitePlace.norm_def, hval, WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
    simp
  have hq : (1 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  have hlog : Real.log (v.val.asIdeal.absNorm : ℝ) ≠ 0 := (Real.log_pos hq).ne'
  have hpow : (((‖(π : v.val.adicCompletion F)‖ : ℝ) : ℂ)) ^ a = 1 := by
    rw [hπ_norm, Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero (zero_lt_one.trans hq).ne')),
      ← Complex.ofReal_log (inv_pos.mpr (zero_lt_one.trans hq)).le, Real.log_inv]
    have he : (↑(-Real.log (v.val.asIdeal.absNorm : ℝ)) : ℂ) * a =
        ((-(n : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      dsimp [a]
      simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_div,
        Complex.ofReal_ofNat, Complex.ofReal_natCast, Int.cast_neg, Int.cast_natCast]
      calc
        _ = -(n : ℂ) * (2 * Real.pi * Complex.I) *
            ((Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) /
              (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ)) := by ring
        _ = _ := by rw [div_self (Complex.ofReal_ne_zero.mpr hlog), mul_one]
    rw [he]
    exact Complex.exp_int_mul_two_pi_mul_I (-(n : ℤ))
  have hval : sLocalFiniteRestriction v ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) c a) π = sLocalFiniteRestriction v c π := by
    rw [sLocalOrbitalPrincipalPart_range_le_ker_restrict, hpow, mul_one]
  change (if ∀ u, sLocalFiniteRestriction v ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) c a) (ι u) = 1 then
      (1 - sLocalFiniteRestriction v ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) c a) π)⁻¹ else 1) =
    (if ∀ u, sLocalFiniteRestriction v c (ι u) = 1 then
      (1 - sLocalFiniteRestriction v c π)⁻¹ else 1)
  rw [key, hval]

/-- Paper: Theorem 7.3.1.6(2), p. 345.
Every primary pole has infinitely many distinct primary poles on the same component,
obtained by imaginary twists preserving one contributing finite place. -/
private theorem sLocalOrbitalIndex_enumerable_or_empty_infinite_centers
    {F : Type*} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))} (p : (HeightOneSpectrum (𝓞 ℚ))) (ω : PontryaginDual (((sIdeleQuotientNorm F S)).ker)) (c : (QuasiCharacter (SIdeleQuotient F S)))
    (hc : (normOneRestriction (sIdeleQuotientNorm F S) c = (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω) ∧ 0 < sLocalFinitePoleMultiplicity ((sLocalPrimaryPlaces S p)) c) :
    ∃ f : ℕ → {d : (QuasiCharacter (SIdeleQuotient F S)) // (normOneRestriction (sIdeleQuotientNorm F S) d = (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω) ∧
      0 < sLocalFinitePoleMultiplicity ((sLocalPrimaryPlaces S p)) d}, Function.Injective f := by
  classical
  obtain ⟨χ, hcomp, hcover⟩ := sLocalOrbitalIndex_enumerable_or_empty_chart ω
  obtain ⟨a, rfl⟩ := hcover c hc.1
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hc.2
  obtain ⟨hv, hvp⟩ := Finset.mem_filter.mp hv
  let per : ℝ := 2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)
  let z (n : ℕ) : ℂ := ((n : ℝ) * per : ℝ) * Complex.I
  have hpos (n : ℕ) : 0 < sLocalFinitePoleMultiplicity ((sLocalPrimaryPlaces S p)) (((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)) (z n + a)) := by
    apply Finset.card_pos.mpr
    refine ⟨v, Finset.mem_filter.mpr ⟨?_, hvp⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have he : (fun w : ℂ ↦ finiteLocalEulerFactor v.val
        (sLocalFiniteRestriction v ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) (((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)) (z n + a)) w))) =
      (fun w : ℂ ↦ finiteLocalEulerFactor v.val
        (sLocalFiniteRestriction v ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) (((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)) a) w))) := by
      funext w
      have h := sLocalOrbitalIndex_enumerable_or_empty_periodic v ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) (((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)) a) w) n
      simpa only [normTwist_normTwist, add_assoc, add_left_comm, add_comm] using h
    rw [he]
    exact (Finset.mem_filter.mp hv).2
  have hinj : Injective (((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ))) := by
    intro s t he
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
    let P := quasiCharacterNormTwist (MonoidHom.id ℝ≥0ˣ) continuous_id 1 s
    have hs (u : ℝ≥0ˣ) : P u = ((u.val : ℝ) : ℂ) ^ s := one_mul _
    apply (existsUnique_complexPower P).unique hs
    intro u
    have h := DFunLike.congr_fun he (σ u)
    change (χ (σ u) : ℂ) * ((((sIdeleQuotientNorm F S) (σ u) : ℝ≥0) : ℝ) : ℂ) ^ s =
      (χ (σ u) : ℂ) * ((((sIdeleQuotientNorm F S) (σ u) : ℝ≥0) : ℝ) : ℂ) ^ t at h
    rw [hσ u] at h
    exact (hs u).trans (mul_left_cancel₀ (Circle.coe_ne_zero _) h)
  refine ⟨fun n ↦ ⟨((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)) (z n + a), hcomp _, hpos n⟩, ?_⟩
  intro n m h
  have he := congrArg Complex.im (add_right_cancel (hinj (congrArg Subtype.val h)))
  have hper : per ≠ 0 := by
    have hq : (1 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
    exact (div_pos (by positivity) (Real.log_pos hq)).ne'
  have he' : (n : ℝ) * per = (m : ℝ) * per := by
    simpa only [z, Complex.mul_I_im, Complex.ofReal_re] using he
  exact Nat.cast_injective (mul_right_cancel₀ hper he')

/-- Paper: Theorem 7.3.1.6(2), p. 345.
The common index set either admits an enumeration by the natural numbers or is
empty and the corresponding primary quotient is zero. -/
theorem sLocalOrbitalIndex_enumerable_or_empty
    (p : Vℚ) (ω : PontryaginDual J₁)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial) :
    Nonempty (ℕ ≃ Idx(p, ω)) ∨ (IsEmpty (Idx(p, ω)) ∧ Subsingleton (Q(p, ω))) := by
  classical
  by_cases h : Nonempty (Idx(p, ω))
  · have : Countable {c : Xₛ // onComponent(c, ω) ∧
        0 < sLocalFinitePoleMultiplicity (Sₚ(p)) c} :=
      sLocalOrbitalIndex_enumerable_or_empty_countable_centers p ω
    let centerOffset (j : Idx(p, ω)) :
        {c : Xₛ // onComponent(c, ω) ∧
          0 < sLocalFinitePoleMultiplicity (Sₚ(p)) c} × ℕ :=
      (⟨j.val.1, j.property.1, lt_of_le_of_lt (Nat.zero_le _) j.property.2⟩, j.val.2)
    have : Countable (Idx(p, ω)) := (show Function.Injective centerOffset from by
      intro a b hab
      apply Subtype.ext
      exact Prod.ext (congrArg (fun x ↦ x.1.val) hab)
        (congrArg (fun x :
          {c : Xₛ // onComponent(c, ω) ∧
            0 < sLocalFinitePoleMultiplicity (Sₚ(p)) c} × ℕ ↦ x.2) hab)).countable
    obtain ⟨j⟩ := h
    obtain ⟨f, hf⟩ := sLocalOrbitalIndex_enumerable_or_empty_infinite_centers
      p ω j.val.1 ⟨j.property.1, lt_of_le_of_lt (Nat.zero_le _) j.property.2⟩
    have : Infinite (Idx(p, ω)) := Infinite.of_injective
      (fun n : ℕ ↦ (⟨((f n).val, 0), (f n).property.1, (f n).property.2⟩ : Idx(p, ω)))
      (by
        intro a b hab
        apply hf
        apply Subtype.ext
        exact congrArg (fun j : Idx(p, ω) ↦ j.val.1) hab)
    exact Or.inl nonempty_equiv_of_countable
  · right
    have hEmpty : IsEmpty (Idx(p, ω)) := ⟨fun j ↦ h ⟨j⟩⟩
    refine ⟨hEmpty, ⟨?_⟩⟩
    intro x y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (Rₚ(p, ω)) x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (Rₚ(p, ω)) y
    have hx := (sLocalPrimaryOrbitalQuotient_mk_eq_zero p _hS _hp _hPic ω x).2
      (fun j ↦ isEmptyElim j)
    have hy := (sLocalPrimaryOrbitalQuotient_mk_eq_zero p _hS _hp _hPic ω y).2
      (fun j ↦ isEmptyElim j)
    exact hx.trans hy.symm

local notation "rhoCoeff(" c ", " r ")" =>
  complexResidue (fun z : ℂ ↦ sLocalRhoFactor (twistₛ (c) z) *
    z ^ ((sLocalRhoPoleOrder (c) : ℤ) - ((r : ℕ) : ℤ) - 1)) 0

/-- Paper: Theorem 7.3.1.6(2)–(3), p. 345.
Any enumeration of the polar functionals gives an unconditional basis of the strong dual.
With the same enumeration, its biorthogonal vectors are an absolute basis of the quotient.
Deviation: Assumes polynomial bounds on the ratios of lower to leading Laurent coefficients
of the correcting factor within each selected block. The hypothesis is vacuous at a
primary pole of multiplicity one. The general assertion on p. 349 needs uniform control
of the changes of basis across the different centers. -/
theorem sLocalPolarOrbital_bases_of_laurent_bounds
    (p : Vℚ) (ω : PontryaginDual J₁)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial) (σ : ℕ ≃ Idx(p, ω))
    (_hcoeff : ∀ χ : PontryaginDual Jₛ, ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (j : Idx(p, ω)) (s : ℂ), j.val.2 ≠ 0 → j.val.1 = chart(χ) s →
        ‖rhoCoeff(j.val.1, j.val.2)‖ ≤ C * (1 + ‖s‖) ^ d * ‖rhoCoeff(j.val.1, 0)‖) :
    ∃ (D : Idx(p, ω) → StrongDual ℂ (Q(p, ω))) (ψ : Idx(p, ω) → Q(p, ω))
      (ev : ℕ → StrongDual ℂ (StrongDual ℂ (Q(p, ω)))),
      (∀ (n : ℕ) (ℓ : StrongDual ℂ (Q(p, ω))), ev n ℓ = ℓ (ψ (σ n))) ∧
      (∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
        sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x) ∧
      let e := ψ ∘ σ
      let d := D ∘ σ
      IsSchauderBasis d ev ∧ SchauderBasis.IsUnconditional d ev ∧
        IsSchauderBasis e d ∧ SchauderBasis.IsAbsolute e d := by sorry

-- TODO(paper-gap): In (7.3.1.19) use the inverse uniformizers at the unramified
-- places above p for the generators of Chapter 4. At a ramified place Weil's
-- unit average vanishes on the isotype, and its principal value is the identity.
/-- Paper: Theorem 7.3.1.6(2)–(3), p. 345.
Any enumeration of the Fourier functionals gives an unconditional basis of the strong dual.
With the same enumeration, its biorthogonal vectors are an absolute basis of the quotient. -/
theorem sLocalFourierOrbital_bases
    (p : Vℚ) (ω : PontryaginDual J₁)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial) (σ : ℕ ≃ Idx(p, ω)) :
    ∃ (D : Idx(p, ω) → StrongDual ℂ (Q(p, ω))) (ψ : Idx(p, ω) → Q(p, ω))
      (ev : ℕ → StrongDual ℂ (StrongDual ℂ (Q(p, ω)))),
      (∀ (n : ℕ) (ℓ : StrongDual ℂ (Q(p, ω))), ev n ℓ = ℓ (ψ (σ n))) ∧
      (∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
        sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x) ∧
      let e := ψ ∘ σ
      let d := D ∘ σ
      IsSchauderBasis d ev ∧ SchauderBasis.IsUnconditional d ev ∧
        IsSchauderBasis e d ∧ SchauderBasis.IsAbsolute e d := by sorry

end PrimaryBases

local notation "restrict₁(" χ ")" => ((χ : PontryaginDual Jₛ).comp
  (⟨(mₛ).ker.subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ))

section LatticeEstimates

open Classical in
/-- Paper: Theorem 7.3.1.6(4), p. 345.
The seminorm of a biorthogonal Fourier vector grows at most polynomially along a
local pole lattice, uniformly over the derivative orders at each pole.
Deviation: A constant times a power of one plus the index norm expresses the polynomial bound.
The finite initial segment is absorbed into the constant. -/
theorem sLocalFourierOrbital_biorthogonal_growth
    (p : Vℚ) (χ : PontryaginDual Jₛ) (ω : PontryaginDual J₁)
    (v : S) (u : (v.val.adicCompletion F)ˣ) (t : ℝ)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial)
    (_hω : ω = restrict₁(χ))
    (_hv : v.val ∈ Sₚ(p)) (_hu : uniformizerNorm(v, u)) (_ht : phase(χ, v, u, t))
    (ψ : Idx(p, ω) → Q(p, ω))
    (_hψ : ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = ψ j →
      sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x = if i = j then 1 else 0)
    (q : Seminorm ℂ Q(p, ω)) (_hq : Continuous q) :
    ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℤ) (j : Idx(p, ω)), j.val.1 = lattice(χ, v, t, n) →
        v ∈ sLocalFinitePolePlaces (F := F) (S := S) j.val.1 → q (ψ j) ≤ C * (1 + |(n : ℝ)|) ^ d := by sorry

open Classical in
/-- Paper: Theorem 7.3.1.6(5), p. 345.
The Fourier jet of each test at fixed order gives a Schwartz sequence along a local
pole lattice.
Deviation: The sequence is extended by zero where the place does not contribute
a pole or the derivative order is outside the primary multiplicity. -/
theorem sLocalOrbitalFourierJet_lattice_schwartz
    (p : Vℚ) (χ : PontryaginDual Jₛ) (v : S) (u : (v.val.adicCompletion F)ˣ) (t : ℝ)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial)
    (_hv : v.val ∈ Sₚ(p)) (_hu : uniformizerNorm(v, u)) (_ht : phase(χ, v, u, t))
    (f : ℬₛ) (k : ℕ) :
    ∃ a : SchwartzBruhat (Multiplicative ℤ), ∀ n : ℤ,
      let c := lattice(χ, v, t, n)
      a (Multiplicative.ofAdd n) =
        if v ∈ sLocalFinitePolePlaces (F := F) (S := S) c ∧
          k < sLocalPrimaryPoleMultiplicity (F := F) (S := S) p c then
          iteratedDeriv k (fourierZeta(c) f) 0
        else 0 := by sorry

end LatticeEstimates

-- TODO(paper-gap): The proof of Theorem 7.3.1.6 alternates between 1+s and 1-s in
-- (7.3.1.24)–(7.3.1.25). For the displayed 1+s coordinate the multiplier is P(-s)
-- for P(s) the selected reciprocal Euler product. The remaining order at c can be
-- m_S(c) - N_p(c), which is positive when other places contribute there.
-- The pointwise triangular changes on p. 349 need a convergence argument for the polar basis.
-- The discrete oscillation assertion on p. 350 needs the estimate identified in ERRATA M8.

section OrbitalSystems

open Classical in
/-- Paper: Definition 7.3.1.7(1), p. 350.
The polar orbital system consists of the primary polar functionals in the ambient strong
dual and their biorthogonal vectors in the quotient. -/
def sLocalPolarOrbitalSystem (p : Vℚ) (ω : PontryaginDual J₁) : Set (StrongDual ℂ (Θₛ(ω))) × Set Q(p, ω) :=
  (range (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω)),
    {y : Q(p, ω) | ∃ j : Idx(p, ω), ∀ (i : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = y →
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x = if i = j then 1 else 0})

open Classical in
/-- Paper: Definition 7.3.1.7(2), p. 350.
The fourier orbital system consists of the primary fourier functionals in the ambient strong
dual and their biorthogonal vectors in the quotient. -/
def sLocalFourierOrbitalSystem (p : Vℚ) (ω : PontryaginDual J₁) : Set (StrongDual ℂ (Θₛ(ω))) × Set Q(p, ω) :=
  (range (sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω)),
    {y : Q(p, ω) | ∃ j : Idx(p, ω), ∀ (i : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = y →
      sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x = if i = j then 1 else 0})

/-- Paper: Definition 7.3.1.7(1), p. 350.
Each selected Laurent coefficient belongs to the polar orbital system's functional set. -/
theorem sLocalOrbitalPrincipalPart_mem_polarSystem (p : Vℚ) (ω : PontryaginDual J₁) (j : Idx(p, ω)) :
    sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j ∈
      (sLocalPolarOrbitalSystem (F := F) (S := S) p ω).1 := ⟨j, rfl⟩

/-- Paper: Definition 7.3.1.7(2), p. 350.
Each selected Fourier jet belongs to the Fourier orbital system's functional set. -/
theorem sLocalOrbitalFourierJet_mem_fourierSystem (p : Vℚ) (ω : PontryaginDual J₁) (j : Idx(p, ω)) :
    sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j ∈
      (sLocalFourierOrbitalSystem (F := F) (S := S) p ω).1 := ⟨j, rfl⟩

open Classical in
/-- Paper: Definition 7.3.1.7(1), p. 350.
The quotient vector paired with a specified index belongs to the system's second set. -/
theorem sLocalPolarOrbitalSystem_biorthogonal_mem (p : Vℚ) (ω : PontryaginDual J₁)
    (ψ : Idx(p, ω) → Q(p, ω))
    (hψ : ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = ψ j →
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x = if i = j then 1 else 0)
    (j : Idx(p, ω)) : ψ j ∈ (sLocalPolarOrbitalSystem (F := F) (S := S) p ω).2 :=
  ⟨j, fun i ↦ hψ i j⟩

open Classical in
/-- Paper: Definition 7.3.1.7(2), p. 350.
The quotient vector paired with a specified index belongs to the system's second set. -/
theorem sLocalFourierOrbitalSystem_biorthogonal_mem (p : Vℚ) (ω : PontryaginDual J₁)
    (ψ : Idx(p, ω) → Q(p, ω))
    (hψ : ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = ψ j →
      sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x = if i = j then 1 else 0)
    (j : Idx(p, ω)) : ψ j ∈ (sLocalFourierOrbitalSystem (F := F) (S := S) p ω).2 :=
  ⟨j, fun i ↦ hψ i j⟩

end OrbitalSystems

-- TODO(paper-gap): Corollary 7.3.1.8 cites the nonexistent Theorem 7.3.1.2(3).
-- Definition 7.3.1.7 identifies the S-local systems from Theorem 7.3.1.6.
-- The proof also mentions global systems but does not identify a global orbital quotient or basis.

section OrbitalBasisProperties

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F


/-- Paper: Corollary 7.3.1.8(1), p. 350.
The enumerated polar and Fourier systems give equicontinuous, shrinking and boundedly
complete bases of the strong dual.
Deviation: Assumes a basis in the S-local quotient. The printed reference to
Theorem 7.3.1.2(3) has no target. -/
theorem sLocalOrbitalSystem_strongDual_basis_properties
    (p : Vℚ) (χ : PontryaginDual C𝔽) (χₛ : PontryaginDual Jₛ) (ω : PontryaginDual J₁)
    (σ : ℕ ≃ Idx(p, ω)) (e : ℕ → Q(p, ω)) (d : ℕ → StrongDual ℂ (Q(p, ω)))
    (hχ : (circleToComplex).comp χ ∈ unramifiedOutside F S)
    (_hχₛ : (circleToComplex).comp χₛ = sIdeleRestriction F S ⟨(circleToComplex).comp χ, hχ⟩)
    (_hω : ω = restrict₁(χₛ))
    (_hd : (∀ (n : ℕ) (x : Θₛ(ω)), d n (π(p, ω) x) =
        sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) (σ n) x) ∨
      (∀ (n : ℕ) (x : Θₛ(ω)), d n (π(p, ω) x) =
        sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) (σ n) x))
    (_he : IsSchauderBasis e d) :
    let ev : ℕ → StrongDual ℂ (StrongDual ℂ (Q(p, ω))) :=
      fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (e n)
    SchauderBasis.IsEquicontinuous d ev ∧ SchauderBasis.IsShrinking d ev ∧
      SchauderBasis.IsBoundedlyComplete d := by sorry

/-- Paper: Corollary 7.3.1.8(2), p. 350.
The corresponding biorthogonal bases of the primary quotient are equicontinuous,
shrinking and boundedly complete.
Deviation: Assumes a basis in the S-local quotient associated to the descended character. -/
theorem sLocalOrbitalSystem_quotient_basis_properties
    (p : Vℚ) (χ : PontryaginDual C𝔽) (χₛ : PontryaginDual Jₛ) (ω : PontryaginDual J₁)
    (σ : ℕ ≃ Idx(p, ω)) (e : ℕ → Q(p, ω)) (d : ℕ → StrongDual ℂ (Q(p, ω)))
    (hχ : (circleToComplex).comp χ ∈ unramifiedOutside F S)
    (_hχₛ : (circleToComplex).comp χₛ = sIdeleRestriction F S ⟨(circleToComplex).comp χ, hχ⟩)
    (_hω : ω = restrict₁(χₛ))
    (_hd : (∀ (n : ℕ) (x : Θₛ(ω)), d n (π(p, ω) x) =
        sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) (σ n) x) ∨
      (∀ (n : ℕ) (x : Θₛ(ω)), d n (π(p, ω) x) =
        sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) (σ n) x))
    (_he : IsSchauderBasis e d) :
    SchauderBasis.IsEquicontinuous e d ∧ SchauderBasis.IsShrinking e d ∧
      SchauderBasis.IsBoundedlyComplete e := by sorry

end OrbitalBasisProperties

end RiemannMasullo
