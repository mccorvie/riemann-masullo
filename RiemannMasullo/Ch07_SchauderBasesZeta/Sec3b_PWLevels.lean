module

import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.MittagLefflerLift
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec1
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec5
public import RiemannMasullo.Ch06_LocalGlobal.Sec2
public import RiemannMasullo.Ch06_LocalGlobal.Sec3
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec2

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a_PrimaryPlaces
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec4
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.ProdPi
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Complex.ExpPolynomial
import RiemannMasullo.ForMathlib.NumberTheory.LinearFormsInLogarithms

public import RiemannMasullo.Ch03_IdelicZeta.Sec3

/-! # §7.3.2 Paley–Wiener levels

The first part of `RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b`, split off so that modules
that need only these declarations do not wait for the rest of that file.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 600000
set_option Elab.async false

variable {F : Type*} [Field F] [NumberField F]
variable {S T R : Finset (HeightOneSpectrum (𝓞 F))}

local notation "C₁" => (ideleClassNorm F).ker
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "J(" T ")" => SIdeleQuotient F T
local notation "m(" T ")" => sIdeleQuotientNorm F T
local notation "J₁(" T ")" => (m(T)).ker
local notation "B(" T ")" => SchwartzBruhat (Multiplicative (SAdeleRing F T))
local notation "Θ(" T ", " ω ")" => SLocalHomogeneousThetaSpace F T ω
local notation "q(" T ", " ω ")" => (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F T ω)).mkQ
local notation "Z₀(" T ")" => sAdelePolarSubspace F T
local notation "Π(" h ")" => sAdeleSchwartzTransition F h
local notation "PicTrivial" => Subsingleton (CommRing.Pic ((S : Set V).integer F))
local notation "A(" T ", " ω ")" =>
  (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T) ω).exists.choose
local notation "PV(" h ", " ω ")" => sLocalHomogeneousThetaPrincipalValue (F := F) h ω
local notation "count(" S ")" => (Fintype.card (InfinitePlace F) + Finset.card S)
local notation "size(" R ")" => (∏ v ∈ R, (v.asIdeal.absNorm : ℝ))
local notation "large(" g ")" => (1 ≤ ((m(T) g).val : ℝ))
local notation "descend(" h ", " ω ", " hu ")" =>
  sLocalNormOneCharacter (F := F) T ω
    (NormOneCharacterUnramifiedOutside.mono (F := F) hu h)
local notation "onComponent(" c ", " ω ")" =>
  (normOneRestriction (m(S)) c =
    (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω)

/-- Paper: Definition 7.3.2.1(1), p. 351.
The Fourier box bounds the normalized absolute value at every selected place. -/
def sLocalPWBox (_S : Finset V) (X : ℝ) : Set (SAdeleRing F _S) :=
  {x | (∀ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult ≤ X) ∧ ∀ v : _S, ‖x.2 v‖ ≤ X}

/-- Paper: Definition 7.3.2.1(1), p. 351.
The Fourier box is compact. -/
theorem isCompact_sLocalPWBox (X : ℝ) : IsCompact (sLocalPWBox S X) := by
  let A (w : InfinitePlace F) := {z : w.Completion | ‖z‖ ^ w.mult ≤ X}
  let D (v : S) := Metric.closedBall (0 : v.val.adicCompletion F) X
  have hA (w : InfinitePlace F) : IsCompact (A w) := by
    have he := InfinitePlace.Completion.isometry_extensionEmbedding w
    let : ProperSpace w.Completion :=
      LipschitzWith.properSpace he.isClosedEmbedding.isProperMap he.lipschitzWith
    refine (isCompact_closedBall (0 : w.Completion) (max 1 X)).of_isClosed_subset
      (isClosed_le (continuous_norm.pow w.mult) continuous_const) ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases h : ‖z‖ ≤ 1
    · exact h.trans (le_max_left _ _)
    · exact ((le_self_pow₀ (le_of_not_ge h) w.mult_ne_zero).trans hz).trans (le_max_right _ _)
  have hD (v : S) : IsCompact (D v) := by
    let := properSpace_adicCompletion v.val (K := F)
    exact isCompact_closedBall _ _
  have hbox : sLocalPWBox S X = (univ.pi A) ×ˢ (univ.pi D) := by
    apply Set.ext
    intro z
    simp only [sLocalPWBox, A, D, mem_ofPred_eq, mem_prod, Set.mem_pi, mem_univ, forall_const,
      Metric.mem_closedBall, dist_zero_right]
  rw [hbox]
  exact (isCompact_univ_pi hA).prod (isCompact_univ_pi hD)

local notation "inBand(" K ", " f ")" =>
  (HasCompactSupport (sAdeleSchwartzFourier f).val ∧
    tsupport (sAdeleSchwartzFourier f).val ⊆ Multiplicative.toAdd ⁻¹' K)

/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
The tests at the larger stage are insertions of small-stage tests with compact Fourier
support contained in the specified region.
Deviation: Uses the cited transition (2.1.4.2), which inserts integer-ring indicators,
as in the proofs on pp. 352–359. Equations (7.3.2.2) and (7.3.2.13) print unit indicators. -/
def sLocalPWTests (hST : S ⊆ T) (K : Set (SAdeleRing F S)) : Submodule ℂ (B(T)) :=
  (Submodule.span ℂ {f : B(S) | inBand(K, f)}).map (Π(hST))

/-- The compactly supported functions with support in a fixed set form a submodule.
Consequently, taking the span of their preimages under a linear map preserves the set. -/
private theorem mem_sLocalPWTests_map_span {G E E' : Type*} [TopologicalSpace G]
    [AddCommMonoid E] [Module ℂ E] [AddCommMonoid E'] [Module ℂ E']
    (s : Set G) (L : E →ₗ[ℂ] (G → ℂ)) (φ : E → G → ℂ) (hL : ∀ g, L g = φ g)
    (j : E →ₗ[ℂ] E') (f : E') :
    f ∈ (Submodule.span ℂ {g : E | HasCompactSupport (φ g) ∧ tsupport (φ g) ⊆ s}).map j ↔
      ∃ g, j g = f ∧ HasCompactSupport (φ g) ∧ tsupport (φ g) ⊆ s := by
  obtain rfl : φ = L := (funext hL).symm
  let Q : Submodule ℂ (G → ℂ) :=
    { carrier := {g | HasCompactSupport g ∧ tsupport g ⊆ s}
      zero_mem' := ⟨HasCompactSupport.zero, by simp⟩
      add_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        exact ⟨hx.add hy, (tsupport_add x y).trans (union_subset hx' hy')⟩
      smul_mem' := by
        rintro c x ⟨hx, hx'⟩
        exact ⟨hx.smul_left (f := fun _ ↦ c), (tsupport_smul_subset_right (fun _ ↦ c) x).trans hx'⟩ }
  have hgen : {g : E | HasCompactSupport (L g) ∧ tsupport (L g) ⊆ s} = (Q.comap L : Set E) := rfl
  rw [hgen, Submodule.span_eq]
  exact ⟨fun ⟨g, hg, hf⟩ ↦ ⟨g, hf, hg⟩, fun ⟨g, hf, hg⟩ ↦ ⟨g, hg, hf⟩⟩

/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
Every test in the Fourier level is the insertion of a single small-stage test
satisfying both Fourier-support conditions.
Deviation: The insertion uses the integer-ring indicators of (2.1.4.2). -/
theorem mem_sLocalPWTests (hST : S ⊆ T) (K : Set (SAdeleRing F S)) (f : B(T)) :
    f ∈ sLocalPWTests hST K ↔ ∃ g : B(S), Π(hST) g = f ∧ inBand(K, g) := by
  let hF := sLocal_fourier_continuousLinear (F := F) (S := S)
  let A : B(S) →L[ℂ] B(S) := hF.choose
  have hA (g : B(S)) : A g = sAdeleSchwartzFourier g := hF.choose_spec g
  let L : B(S) →ₗ[ℂ] (Multiplicative (SAdeleRing F S) → ℂ) :=
    (schwartzBruhatSubmodule _).subtype.comp A.toLinearMap
  have hL (g : B(S)) : L g = (sAdeleSchwartzFourier g).val :=
    congrArg (fun f : B(S) ↦ f.val) (hA g)
  unfold sLocalPWTests
  exact mem_sLocalPWTests_map_span (Multiplicative.toAdd ⁻¹' K) L
    (fun g : B(S) ↦ (sAdeleSchwartzFourier g).val) hL (Π(hST)) f

/-- Dirac support supplies a compactly supported test with prescribed value one. -/
private theorem sLocalPWTests_moments_surjective_bump
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (x : G) (U : Set G) (hU : U ∈ 𝓝 x) :
    ∃ f : SchwartzBruhat G, HasCompactSupport f.val ∧ tsupport f.val ⊆ U ∧ f x = 1 := by
  classical
  obtain ⟨U₀, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  obtain ⟨C, hC, hxC, hCV⟩ := exists_compact_subset hV hxV
  obtain ⟨δ, hδ, hvan, -⟩ := schwartzBruhat_dirac_support x
  have hex : ∃ f : SchwartzBruhat G, tsupport f.val ⊆ interior C ∧ f x ≠ 0 := by
    by_contra! hn
    have hxvan : x ∈ schwartzBruhatVanishingLocus δ := by
      apply Set.mem_sUnion.mpr
      refine ⟨interior C, ⟨isOpen_interior, ?_⟩, hxC⟩
      intro f hf
      rw [hδ]
      exact hn f hf
    rw [hvan] at hxvan
    exact hxvan (Set.mem_singleton x)
  obtain ⟨f, hf, hfx⟩ := hex
  have hc : HasCompactSupport f.val :=
    hC.of_isClosed_subset isClosed_closure (hf.trans interior_subset)
  refine ⟨(f x)⁻¹ • f, hc.smul_left (f := fun _ ↦ (f x)⁻¹), ?_, ?_⟩
  · exact (tsupport_smul_subset_right (fun _ ↦ (f x)⁻¹) f.val).trans
      (hf.trans (interior_subset.trans (hCV.trans hVU)))
  · change (f x)⁻¹ * f x = 1
    exact inv_mul_cancel₀ hfx

/-- Modulating a nonzero bump by a character can make its integral nonzero
without enlarging its support. -/
private theorem sLocalPWTests_moments_surjective_zero_bump_modulate
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure]
    (p : SchwartzBruhat G) (hp : p ≠ 0) :
    ∃ h : SchwartzBruhat G, tsupport h.val ⊆ tsupport p.val ∧
      MeasureTheory.integral μ h.val ≠ 0 := by
  obtain ⟨L, hL⟩ := schwartzBruhat_fourier_equiv μ
  obtain ⟨χ, hχ⟩ : ∃ χ, L p χ ≠ 0 := by
    by_contra! hall
    exact hp (L.map_eq_zero_iff.mp (Subtype.ext (funext hall)))
  let h : SchwartzBruhat G := ⟨_, pontryaginDual_mul_schwartzBruhat χ⁻¹ p⟩
  refine ⟨h, tsupport_mul_subset_right, ?_⟩
  rw [(hL p).2 χ] at hχ
  intro he
  apply hχ
  refine (MeasureTheory.integral_congr_ae ?_).trans he
  exact .of_forall fun x ↦ by
    change p x * star (χ x : ℂ) = (((χ x)⁻¹ : Circle) : ℂ) * p x
    rw [Circle.coe_inv_eq_conj, Complex.star_def, mul_comm]

/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
Every neighborhood of zero contains the support of a compact Schwartz–Bruhat
bump vanishing at zero and having nonzero additive Tamagawa integral.
One can place a nonnegative bump near a nonzero point in the neighborhood. -/
theorem sLocalPWTests_moments_surjective_zero_bump
    {F : Type*} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Set (SAdeleRing F S)) (hK : K ∈ 𝓝 0) :
    ∃ h : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
      HasCompactSupport h.val ∧ tsupport h.val ⊆ Multiplicative.toAdd ⁻¹' K ∧
      h (Multiplicative.ofAdd 0) = 0 ∧
      MeasureTheory.integral (sAdditiveTamagawaMeasure F S)
        (fun x ↦ h (Multiplicative.ofAdd x)) ≠ 0 := by
  classical
  let A := SAdeleRing F S
  let G := Multiplicative A
  let w : InfinitePlace F := Classical.arbitrary _
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
  let : NontriviallyNormedField w.Completion := ⟨⟨2, by
    rw [← hi.norm_map_of_map_zero (map_zero _) (2 : w.Completion), map_ofNat]
    norm_num⟩⟩
  let j (z : w.Completion) : A := (Pi.single w z, 0)
  have hj : Continuous j := (continuous_single w).prodMk continuous_const
  have h0 : j 0 = 0 := by
    change (Pi.single w 0, (0 : (v : S) → v.val.adicCompletion F)) = (0, 0)
    rw [Pi.single_zero]
  have hnear : ∀ᶠ z in 𝓝[≠] (0 : w.Completion), j z ∈ interior K :=
    ((hj.tendsto' _ _ h0).mono_left nhdsWithin_le_nhds) (interior_mem_nhds.mpr hK)
  obtain ⟨z, hzK, hz⟩ := (hnear.and (self_mem_nhdsWithin :
    {0}ᶜ ∈ 𝓝[≠] (0 : w.Completion))).exists
  have hjz : j z ≠ 0 := by
    intro he
    have hz0 : Pi.single w z w = (0 : w.Completion) := congrArg (fun a : A ↦ a.1 w) he
    exact hz (Set.mem_singleton_iff.mpr ((Pi.single_eq_same w z).symm.trans hz0))
  let (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
  let (v : InfinitePlace F) : MeasurableSpace v.Completion := borel _
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((v : InfinitePlace F) → v.Completion))
  let : MeasurableSpace A := inferInstanceAs
    (MeasurableSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  let : SecondCountableTopology G := inferInstanceAs (SecondCountableTopology
    (((v : InfinitePlace F) → v.Completion) × ((v : S) → v.val.adicCompletion F)))
  let μ : MeasureTheory.Measure G := sAdditiveTamagawaMeasure F S
  obtain ⟨hT₂, hLC, hBor, hHaar, -⟩ := sAdele_fourierMeasure (F := F) (S := S)
  let : T2Space G := hT₂
  let : LocallyCompactSpace G := hLC
  let : BorelSpace G := hBor
  let : μ.IsHaarMeasure := hHaar
  let U : Set G := (Multiplicative.toAdd ⁻¹' interior K) ∩ {Multiplicative.ofAdd (0 : A)}ᶜ
  have hU : IsOpen U := (isOpen_interior.preimage continuous_toAdd).inter isClosed_singleton.isOpen_compl
  obtain ⟨p, hpc, hpU, hpx⟩ := sLocalPWTests_moments_surjective_bump
    (Multiplicative.ofAdd (j z)) U (hU.mem_nhds ⟨hzK, hjz⟩)
  have hp : p ≠ 0 := fun he ↦ zero_ne_one ((congrArg
    (fun f : SchwartzBruhat G ↦ f (Multiplicative.ofAdd (j z))) he).symm.trans hpx)
  obtain ⟨h, hs, hI⟩ := sLocalPWTests_moments_surjective_zero_bump_modulate μ p hp
  refine ⟨h, hpc.of_isClosed_subset isClosed_closure hs, fun x hx ↦
    interior_subset (hpU (hs hx)).1, ?_, hI⟩
  exact image_eq_zero_of_notMem_tsupport fun hx ↦ (hpU (hs hx)).2 rfl

open MeasureTheory in
/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
Insertion of integer-ring indicators multiplies the Fourier value at zero by
one nonzero scalar, independent of the test.
The scalar is the product of the additive Tamagawa volumes of the inserted rings. -/
private theorem sLocalPWTests_moments_surjective_transition
    {F : Type*} [Field F] [NumberField F]
    {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ g : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
      sAdeleSchwartzFourier (sAdeleSchwartzTransition F hST g) (Multiplicative.ofAdd 0) =
        c * sAdeleSchwartzFourier g (Multiplicative.ofAdd 0) := by
  classical
  obtain ⟨D, hd, rfl⟩ : ∃ D : Finset (HeightOneSpectrum (𝓞 F)),
      Disjoint S D ∧ T = S ∪ D :=
    ⟨T \ S, Finset.disjoint_sdiff, (Finset.union_sdiff_of_subset hST).symm⟩
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
  let (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let μ := finiteLocalAdditiveTamagawaMeasure F
  let (v : HeightOneSpectrum (𝓞 F)) : (μ v).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let b (v : D) := (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ))
  refine ⟨∏ v : D, ∫ x, b v x ∂μ v, Finset.prod_ne_zero_iff.mpr ?_, fun g ↦ ?_⟩
  · intro v _
    let O := (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F))
    have ho : IsOpen O := Valued.isOpen_valuationSubring _
    have hc : IsCompact O := isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v.val)
    have hm : 0 < (μ v).real O := ENNReal.toReal_pos
      (ho.measure_pos (μ v) ⟨0, (v.val.adicCompletionIntegers F).zero_mem⟩).ne'
      (hc.measure_ne_top (μ := μ v))
    change (∫ x, O.indicator (fun _ ↦ (1 : ℂ)) x ∂μ v) ≠ 0
    rw [integral_indicator_const _ ho.measurableSet, Complex.real_smul, mul_one]
    exact Complex.ofReal_ne_zero.mpr hm.ne'
  rw [sAdeleSchwartzFourier_apply_zero, sAdeleSchwartzFourier_apply_zero, mul_comm]
  let (w : InfinitePlace F) : SigmaFinite (infiniteLocalAdditiveTamagawaMeasure F w) := by
    rw [infiniteLocalAdditiveTamagawaMeasure]
    split_ifs with hw
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.toHomeomorph.measurableEmbedding.sigmaFinite_map
    · rw [two_nsmul]
      exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)).symm.toHomeomorph.measurableEmbedding.sigmaFinite_map
  apply integral_prod_piFinsetUnion (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)) μ hd
    (fun z ↦ g (Multiplicative.ofAdd z)) b
  intro a x y
  rw [sAdeleSchwartzTransition_apply]
  let X (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F
  let t := MeasurableEquiv.piFinsetUnion X hd (x, y)
  have hmem : (∀ w : ↥(S ∪ D), w.val ∉ S → t w ∈ w.val.adicCompletionIntegers F) ↔
      ∀ v : D, y v ∈ v.val.adicCompletionIntegers F := by
    constructor
    · intro h v
      have hv := h ⟨v.val, Finset.mem_union_right S v.property⟩
        (fun hs ↦ Finset.disjoint_left.mp hd hs v.property)
      simpa only [t, MeasurableEquiv.piFinsetUnion_right X hd v.property] using hv
    · intro h w hw
      have hv := (Finset.mem_union.mp w.property).resolve_left hw
      simpa only [t, MeasurableEquiv.piFinsetUnion_right X hd hv] using! h ⟨w.val, hv⟩
  change (if _ then g (Multiplicative.ofAdd (a, fun v : S ↦ t ⟨v.val, hST v.property⟩)) else 0) = _
  have hx : (fun v : S ↦ t ⟨v.val, hST v.property⟩) = x :=
    funext fun v ↦ MeasurableEquiv.piFinsetUnion_left X hd v.property _
  simp only [b, indicator_apply, Fintype.prod_boole, mul_ite, mul_one, mul_zero]
  exact if_congr hmem (congrArg (fun u ↦ g (Multiplicative.ofAdd (a, u))) hx) rfl

/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
The two moments on the inserted test space can be specified independently whenever
the Fourier region contains a neighborhood of zero, as both positive levels do.
Deviation: This uses the integer-ring transition. -/
theorem sLocalPWTests_moments_surjective (hST : S ⊆ T) (K : Set (SAdeleRing F S))
    (hK : K ∈ 𝓝 0) (a b : ℂ) :
    ∃ f ∈ sLocalPWTests hST K, f (Multiplicative.ofAdd 0) = a ∧
      sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = b := by
  let G := Multiplicative (SAdeleRing F S)
  have hG := sAdele_fourierMeasure (F := F) (S := S)
  let : T2Space G := hG.1
  let : LocallyCompactSpace G := hG.2.1
  have hK' : Multiplicative.toAdd ⁻¹' K ∈ 𝓝 (Multiplicative.ofAdd (0 : SAdeleRing F S)) :=
    continuous_toAdd.continuousAt.preimage_mem_nhds hK
  obtain ⟨p, hpc, hpK, hp0⟩ :=
    sLocalPWTests_moments_surjective_bump (Multiplicative.ofAdd 0) _ hK'
  obtain ⟨q, hqc, hqK, hq0, hqI⟩ :=
    sLocalPWTests_moments_surjective_zero_bump S K hK
  obtain ⟨c, hc, htrans⟩ := sLocalPWTests_moments_surjective_transition (F := F) hST
  obtain ⟨L, hL⟩ := sLocal_fourier_continuousLinear (F := F) (S := S)
  let I := sAdeleSchwartzFourier q (Multiplicative.ofAdd 0)
  have hI : I ≠ 0 := by
    simpa only [I, sAdeleSchwartzFourier_apply_zero] using hqI
  let d := b / c
  let e := (a - d * sAdeleSchwartzFourier p (Multiplicative.ofAdd 0)) / I
  let u := e • q + d • p
  have hu0 : u (Multiplicative.ofAdd 0) = d := by
    change e * q (Multiplicative.ofAdd 0) + d * p (Multiplicative.ofAdd 0) = d
    rw [hq0, hp0, mul_zero, mul_one, zero_add]
  have huF : sAdeleSchwartzFourier u (Multiplicative.ofAdd 0) = a := by
    rw [← hL u]
    change L (e • q + d • p) (Multiplicative.ofAdd 0) = a
    rw [map_add, map_smul, map_smul]
    change e * L q (Multiplicative.ofAdd 0) + d * L p (Multiplicative.ofAdd 0) = a
    rw [hL q, hL p]
    change (a - d * sAdeleSchwartzFourier p (Multiplicative.ofAdd 0)) / I * I +
      d * sAdeleSchwartzFourier p (Multiplicative.ofAdd 0) = a
    rw [div_mul_cancel₀ _ hI, sub_add_cancel]
  have huc : HasCompactSupport u.val :=
    (hqc.smul_left (f := fun _ ↦ e)).add (hpc.smul_left (f := fun _ ↦ d))
  have huK : tsupport u.val ⊆ Multiplicative.toAdd ⁻¹' K :=
    (tsupport_add _ _).trans (union_subset
      ((tsupport_smul_subset_right (fun _ ↦ e) q.val).trans hqK)
      ((tsupport_smul_subset_right (fun _ ↦ d) p.val).trans hpK))
  let g := sAdeleSchwartzFourier (sAdeleSchwartzFourier (sAdeleSchwartzFourier u))
  have hgF : sAdeleSchwartzFourier g = u := by
    apply Subtype.ext
    funext x
    change sAdeleSchwartzFourier (sAdeleSchwartzFourier
      (sAdeleSchwartzFourier (sAdeleSchwartzFourier u))) x = u x
    exact (sLocal_fourier_inversion (sAdeleSchwartzFourier (sAdeleSchwartzFourier u))
      x.toAdd).trans ((sLocal_fourier_inversion u (-x.toAdd)).trans
        (congrArg (fun y ↦ u (Multiplicative.ofAdd y)) (neg_neg x.toAdd)))
  have hg0 : g (Multiplicative.ofAdd 0) = a := by
    simpa only [g, sLocal_fourier_inversion, neg_zero] using huF
  refine ⟨sAdeleSchwartzTransition F hST g,
    (mem_sLocalPWTests hST K _).mpr ⟨g, rfl, ?_⟩, ?_, ?_⟩
  · rw [hgF]
    exact ⟨huc, huK⟩
  · rw [sAdeleSchwartzTransition_apply]
    rw [ite_eq_left (show ∀ w : T, w.val ∉ S →
      (0 : SAdeleRing F T).2 w ∈ w.val.adicCompletionIntegers F from
      fun w _ ↦ (w.val.adicCompletionIntegers F).zero_mem)]
    exact hg0
  · rw [htrans g, hgF, hu0]
    exact mul_div_cancel₀ b hc

local notation "level(" h ", " K ", " D ", " ω ")" =>
  (((sLocalPWTests h K ⊓ D).map (q(_, ω))).topologicalClosure)

/-- Paper: Definition 7.3.2.1(2), p. 351.
The absolute PW level is the closure of the theta image of box-limited tests.
The test constraint is the whole space or the common kernel of the two zero evaluations.
Deviation: Uses the integer-ring insertion of the cited transition. -/
def sLocalAbsolutePW (hST : S ⊆ T) (X : ℝ) (D : Submodule ℂ (B(T)))
    (ω : PontryaginDual J₁(T)) : Submodule ℂ (Θ(T, ω)) :=
  level(hST, sLocalPWBox S X, D, ω)

/-- Paper: Definition 7.3.2.1(2), p. 351.
The theta class of an inserted box-limited test satisfying the chosen test constraint
belongs to the absolute level.
Deviation: Uses the integer-ring insertion of the cited transition. -/
theorem sLocalAbsolutePW_mk_mem (hST : S ⊆ T) (X : ℝ) (D : Submodule ℂ (B(T)))
    (ω : PontryaginDual J₁(T)) (f : B(S)) (_hf : inBand(sLocalPWBox S X, f))
    (_hD : Π(hST) f ∈ D) : q(T, ω) (Π(hST) f) ∈ sLocalAbsolutePW hST X D ω :=
  Submodule.le_topologicalClosure _
    (Submodule.mem_map_of_mem ⟨Submodule.mem_map_of_mem (Submodule.subset_span _hf), _hD⟩)

section LocalFourierSupport

open Classical

private theorem sLocalAbsolutePW_fourier_transition_support {S T : Finset V} (hST : S ⊆ T)
    (g : B(S)) (y : SAdeleRing F T)
    (hy : sAdeleSchwartzFourier (Π(hST) g) (Multiplicative.ofAdd y) ≠ 0) :
    let yS : SAdeleRing F S := (y.1, fun w : S ↦ y.2 ⟨w.val, hST w.property⟩)
    sAdeleSchwartzFourier g (Multiplicative.ofAdd yS) ≠ 0 ∧
      ∀ v : {v : T // v.val ∉ S},
        ‖y.2 v.val‖ ≤
          (v.val.val.asIdeal.absNorm : ℝ) ^ multiplicity v.val.val.asIdeal (differentIdeal ℤ (𝓞 F)) := by
  intro yS
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (v.adicCompletion F) :=
    properSpace_adicCompletion v
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : HeightOneSpectrum (𝓞 F)) :
      (finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  let (w : InfinitePlace F) :
      MeasureTheory.SigmaFinite (infiniteLocalAdditiveTamagawaMeasure F w) :=
    inferInstanceAs (MeasureTheory.SigmaFinite (infiniteLocalAdditiveTamagawaMeasure F w))
  let (v : HeightOneSpectrum (𝓞 F)) :
      MeasureTheory.SigmaFinite (finiteLocalAdditiveTamagawaMeasure F v) :=
    inferInstanceAs (MeasureTheory.SigmaFinite (finiteLocalAdditiveTamagawaMeasure F v))
  let μArch := MeasureTheory.Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)
  let μS := MeasureTheory.Measure.pi (fun w : S ↦ finiteLocalAdditiveTamagawaMeasure F w.val)
  let μT := MeasureTheory.Measure.pi (fun v : T ↦ finiteLocalAdditiveTamagawaMeasure F v.val)
  let μP := MeasureTheory.Measure.pi (fun v : {v : T // v.val ∈ S} ↦
    finiteLocalAdditiveTamagawaMeasure F v.val.val)
  let μU := MeasureTheory.Measure.pi (fun v : {v : T // v.val ∉ S} ↦
    finiteLocalAdditiveTamagawaMeasure F v.val.val)
  let eS : S ≃ {v : T // v.val ∈ S} :=
    { toFun := fun w ↦ ⟨⟨w.val, hST w.property⟩, w.property⟩
      invFun := fun v ↦ ⟨v.val.val, v.property⟩
      left_inv := fun ⟨_, _⟩ ↦ rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl }
  let B : T → Type _ := fun v ↦ v.val.adicCompletion F
  let e1 : ((v : T) → B v) ≃ᵐ
      ((v : {v : T // v.val ∈ S}) → B v.val) × ((v : {v : T // v.val ∉ S}) → B v.val) :=
    MeasurableEquiv.piEquivPiSubtypeProd B (fun v : T ↦ v.val ∈ S)
  let e2 : ((w : S) → B ⟨w.val, hST w.property⟩) ≃ᵐ ((v : {v : T // v.val ∈ S}) → B v.val) :=
    MeasurableEquiv.piCongrLeft (fun v : {v : T // v.val ∈ S} ↦ B v.val) eS
  let eFin : (((w : S) → B ⟨w.val, hST w.property⟩) ×
      ((v : {v : T // v.val ∉ S}) → B v.val)) ≃ᵐ ((v : T) → B v) :=
    (e2.prodCongr (MeasurableEquiv.refl _)).trans e1.symm
  let eTotal : (SAdeleRing F S × ((v : {v : T // v.val ∉ S}) → B v.val)) ≃ᵐ SAdeleRing F T :=
    (MeasurableEquiv.prodAssoc).trans ((MeasurableEquiv.refl _).prodCongr eFin)
  have he1 : MeasureTheory.MeasurePreserving e1 μT (μP.prod μU) :=
    MeasureTheory.measurePreserving_piEquivPiSubtypeProd
      (fun v : T ↦ finiteLocalAdditiveTamagawaMeasure F v.val) (fun v : T ↦ v.val ∈ S)
  have he2 : MeasureTheory.MeasurePreserving e2 μS μP :=
    MeasureTheory.measurePreserving_piCongrLeft
      (fun v : {v : T // v.val ∈ S} ↦ finiteLocalAdditiveTamagawaMeasure F v.val.val) eS
  have heFin : MeasureTheory.MeasurePreserving eFin (μS.prod μU) μT :=
    he1.symm.comp (he2.prod (MeasureTheory.MeasurePreserving.id μU))
  have heTotal : MeasureTheory.MeasurePreserving eTotal ((μArch.prod μS).prod μU) (μArch.prod μT) :=
    ((MeasureTheory.MeasurePreserving.id μArch).prod heFin).comp
      (MeasureTheory.measurePreserving_prodAssoc μArch μS μU)
  let Φ : SAdeleRing F T → ℂ := fun x ↦
    (Π(hST) g) (Multiplicative.ofAdd x) * star (sAdeleStandardCharacter F T (x * y) : ℂ)
  let H : SAdeleRing F S → ℂ := fun xS ↦
    g (Multiplicative.ofAdd xS) * star (sAdeleStandardCharacter F S (xS * yS) : ℂ)
  let b : (v : {v : T // v.val ∉ S}) → B v.val → ℂ := fun v xv ↦
    ((v.val.val.adicCompletionIntegers F : Set (B v.val)).indicator (fun _ ↦ (1 : ℂ)) xv) *
      star (finiteLocalStandardCharacter F v.val.val (xv * y.2 v.val) : ℂ)
  have hΦ (p : SAdeleRing F S × ((v : {v : T // v.val ∉ S}) → B v.val)) :
      Φ (eTotal p) = H p.1 * ∏ v : {v : T // v.val ∉ S}, b v (p.2 v) := by
    rcases p with ⟨⟨aArch, aS⟩, aU⟩
    let x := eTotal ((aArch, aS), aU)
    have hx1 : x.1 = aArch := rfl
    have hxS (w : S) : x.2 ⟨w.val, hST w.property⟩ = aS w := by
      change (e1.symm (e2 aS, aU)) ⟨w.val, hST w.property⟩ = aS w
      have hw : e1.symm (e2 aS, aU) (eS w).val = (e2 aS) (eS w) := by
        change (Equiv.piEquivPiSubtypeProd (fun v : T ↦ v.val ∈ S) B).symm
          (e2 aS, aU) (eS w).val = _
        simp [Equiv.piEquivPiSubtypeProd_symm_apply, (eS w).property]
      refine hw.trans ?_
      exact Equiv.piCongrLeft_apply_apply (fun v : {v : T // v.val ∈ S} ↦ B v.val) eS aS w
    have hxU (v : {v : T // v.val ∉ S}) : x.2 v.val = aU v := by
      change (Equiv.piEquivPiSubtypeProd (fun v : T ↦ v.val ∈ S) B).symm (e2 aS, aU) v.val = aU v
      simp [Equiv.piEquivPiSubtypeProd_symm_apply, v.property]
    have hproj : (x.1, fun w : S ↦ x.2 ⟨w.val, hST w.property⟩) = (aArch, aS) :=
      Prod.ext hx1 (funext hxS)
    have htrans : (Π(hST) g) (Multiplicative.ofAdd x) =
        g (Multiplicative.ofAdd (aArch, aS)) *
          ∏ v : {v : T // v.val ∉ S},
            ((v.val.val.adicCompletionIntegers F : Set (B v.val)).indicator
              (fun _ ↦ (1 : ℂ)) (aU v)) := by
      rw [sAdeleSchwartzTransition_apply, hproj]
      by_cases hmem : ∀ w : T, w.val ∉ S → x.2 w ∈ w.val.adicCompletionIntegers F
      · rw [ite_eq_left hmem]
        have hprod : (∏ v : {v : T // v.val ∉ S},
            ((v.val.val.adicCompletionIntegers F : Set (B v.val)).indicator
              (fun _ ↦ (1 : ℂ)) (aU v))) = 1 := by
          refine Finset.prod_eq_one fun v _ ↦ Set.indicator_of_mem ?_ _
          rw [← hxU v]
          exact hmem v.val v.property
        rw [hprod, mul_one]
      · rw [ite_eq_right hmem]
        push Not at hmem
        rcases hmem with ⟨w, hwS, hxw⟩
        have hprod : (∏ v : {v : T // v.val ∉ S},
            ((v.val.val.adicCompletionIntegers F : Set (B v.val)).indicator
              (fun _ ↦ (1 : ℂ)) (aU v))) = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ (⟨w, hwS⟩ : {v : T // v.val ∉ S})) ?_
          apply Set.indicator_of_notMem
          simpa only [SetLike.mem_coe, ← hxU ⟨w, hwS⟩] using hxw
        rw [hprod, mul_zero]
    have hchar : (sAdeleStandardCharacter F T (x * y) : ℂ) =
        (sAdeleStandardCharacter F S ((aArch, aS) * yS) : ℂ) *
          ∏ v : {v : T // v.val ∉ S},
            (finiteLocalStandardCharacter F v.val.val (aU v * y.2 v.val) : ℂ) := by
      unfold sAdeleStandardCharacter
      have hsplit := Fintype.prod_subtype_mul_prod_subtype (fun v : T ↦ v.val ∈ S)
        (fun v : T ↦ finiteLocalStandardCharacter F v.val ((x * y).2 v))
      have hfst : (∏ w : InfinitePlace F,
          adeleStandardCharacter F (Pi.single w ((x * y).1 w), 0)) =
          (∏ w : InfinitePlace F,
            adeleStandardCharacter F (Pi.single w (((aArch, aS) * yS).1 w), 0)) := by
        refine Finset.prod_congr rfl fun w _ ↦ ?_
        rw [Prod.fst_mul, Prod.fst_mul, hx1]
      have hsub : (∏ v : {v : T // v.val ∈ S},
          finiteLocalStandardCharacter F v.val.val ((x * y).2 v.val)) =
          ∏ w : S, finiteLocalStandardCharacter F w.val (((aArch, aS) * yS).2 w) := by
        refine Fintype.prod_equiv eS.symm _ _ fun v ↦ ?_
        change finiteLocalStandardCharacter F v.val.val (x.2 v.val * y.2 v.val) =
          finiteLocalStandardCharacter F v.val.val (aS ⟨v.val.val, v.property⟩ * y.2 v.val)
        rw [← hxS ⟨v.val.val, v.property⟩]
      have hsnd : (∏ v : {v : T // v.val ∉ S},
          finiteLocalStandardCharacter F v.val.val ((x * y).2 v.val)) =
          ∏ v : {v : T // v.val ∉ S},
            finiteLocalStandardCharacter F v.val.val (aU v * y.2 v.val) := by
        refine Finset.prod_congr rfl fun v _ ↦ ?_
        change finiteLocalStandardCharacter F v.val.val (x.2 v.val * y.2 v.val) = _
        rw [hxU v]
      have hcoe : (↑(∏ v : {v : T // v.val ∉ S},
            finiteLocalStandardCharacter F v.val.val (aU v * y.2 v.val)) : ℂ) =
          ∏ v : {v : T // v.val ∉ S},
            (finiteLocalStandardCharacter F v.val.val (aU v * y.2 v.val) : ℂ) :=
        map_prod Circle.coeHom _ Finset.univ
      rw [← hsplit, hfst, hsub, hsnd]
      simp only [Circle.coe_mul]
      rw [← mul_assoc]
      exact congrArg (fun z : ℂ ↦ _ * z) hcoe
    have hstar : star (sAdeleStandardCharacter F T (x * y) : ℂ) =
        star (sAdeleStandardCharacter F S ((aArch, aS) * yS) : ℂ) *
          ∏ v : {v : T // v.val ∉ S},
            star (finiteLocalStandardCharacter F v.val.val (aU v * y.2 v.val) : ℂ) := by
      rw [hchar, star_mul', star_prod]
    dsimp only [Φ]
    rw [htrans, hstar, Finset.prod_mul_distrib]
    dsimp only [H, b]
    ring
  have hfact : sAdeleSchwartzFourier (Π(hST) g) (Multiplicative.ofAdd y) =
      sAdeleSchwartzFourier g (Multiplicative.ofAdd yS) *
        ∏ v : {v : T // v.val ∉ S},
          tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v.val.val)
            (finiteLocalStandardCharacter F v.val.val)
            ((v.val.val.adicCompletionIntegers F : Set (B v.val)).indicator fun _ ↦ (1 : ℂ))
            (y.2 v.val) := by
    calc
      sAdeleSchwartzFourier (Π(hST) g) (Multiplicative.ofAdd y)
        = ∫ x : SAdeleRing F T, Φ x ∂(μArch.prod μT) := rfl
      _ = ∫ p : SAdeleRing F S × ((v : {v : T // v.val ∉ S}) → B v.val), Φ (eTotal p)
            ∂((μArch.prod μS).prod μU) := (heTotal.integral_comp' Φ).symm
      _ = ∫ p : SAdeleRing F S × ((v : {v : T // v.val ∉ S}) → B v.val),
            H p.1 * ∏ v : {v : T // v.val ∉ S}, b v (p.2 v) ∂((μArch.prod μS).prod μU) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hΦ)
      _ = (∫ xS : SAdeleRing F S, H xS ∂(μArch.prod μS)) *
            ∫ aU : (v : {v : T // v.val ∉ S}) → B v.val,
              ∏ v : {v : T // v.val ∉ S}, b v (aU v) ∂μU :=
          MeasureTheory.integral_prod_mul (μ := μArch.prod μS) (ν := μU) H
            (fun aU ↦ ∏ v : {v : T // v.val ∉ S}, b v (aU v))
      _ = sAdeleSchwartzFourier g (Multiplicative.ofAdd yS) *
            ∏ v : {v : T // v.val ∉ S},
              tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v.val.val)
                (finiteLocalStandardCharacter F v.val.val)
                ((v.val.val.adicCompletionIntegers F : Set (B v.val)).indicator fun _ ↦ (1 : ℂ))
                (y.2 v.val) :=
          congrArg₂ (· * ·) rfl (MeasureTheory.integral_fintype_prod_eq_prod b)
  rw [hfact] at hy
  refine ⟨left_ne_zero_of_mul hy, fun v ↦ ?_⟩
  have hFT : tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v.val.val)
      (finiteLocalStandardCharacter F v.val.val)
      ((v.val.val.adicCompletionIntegers F : Set (B v.val)).indicator fun _ ↦ (1 : ℂ))
      (y.2 v.val) ≠ 0 := by
    intro hv
    apply right_ne_zero_of_mul hy
    exact Finset.prod_eq_zero (Finset.mem_univ v) hv
  rw [finiteLocalTamagawaFourier_integers] at hFT
  by_contra hle
  apply hFT
  simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero]
  right
  exact Set.indicator_of_notMem hle _

end LocalFourierSupport

section AbsoluteLevels

open Classical

/-- Paper: Proposition 7.3.2.2(1), p. 352.
Increasing the box size enlarges each of the two absolute PW levels. -/
theorem sLocalAbsolutePW_mono (hST : S ⊆ T) {X Y : ℝ} (_hXY : X ≤ Y)
    (D : Submodule ℂ (B(T))) (ω : PontryaginDual J₁(T)) :
    sLocalAbsolutePW hST X D ω ≤ sLocalAbsolutePW hST Y D ω := by
  have hbox : sLocalPWBox S X ⊆ sLocalPWBox S Y := fun _ hx ↦
    ⟨fun w ↦ (hx.1 w).trans _hXY, fun v ↦ (hx.2 v).trans _hXY⟩
  have hgen : {f : B(S) | inBand(sLocalPWBox S X, f)} ⊆
      {f : B(S) | inBand(sLocalPWBox S Y, f)} :=
    fun _ hf ↦ ⟨hf.1, hf.2.trans (Set.preimage_mono hbox)⟩
  have htests : sLocalPWTests hST (sLocalPWBox S X) ≤ sLocalPWTests hST (sLocalPWBox S Y) :=
    Submodule.map_mono (Submodule.span_mono hgen)
  exact Submodule.topologicalClosure_mono (Submodule.map_mono (inf_le_inf htests le_rfl))

private theorem sLocalZeroMomentTheta_eq_top_of_translate
    {E W : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup W] [Module ℂ W]
    (p : E →ₗ[ℂ] ℂ × ℂ) (θ : E →ₗ[ℂ] W) (t : E → E)
    (a b : ℂ) (ha : a ≠ 1) (hab : a ≠ b)
    (hp : ∀ f, p (t f) = ((p f).1, b * (p f).2)) (hθ : ∀ f, θ (t f) = a • θ f) :
    p.ker.map θ.ker.mkQ = ⊤ := by
  apply top_unique
  rintro x -
  obtain ⟨f, rfl⟩ := θ.ker.mkQ_surjective x
  -- The first difference kills evaluation at zero. The second kills the Fourier value at zero.
  let k := t f - f
  let h := t k - b • k
  have hk : (p k).1 = 0 := by simp [k, hp]
  have hh : h ∈ p.ker := by
    change p (t k - b • k) = 0
    rw [map_sub, map_smul, hp, sub_eq_zero]
    exact Prod.ext (by simp [hk]) (by simp)
  have hθk : θ k = (a - 1) • θ f := by simp [k, hθ, sub_smul]
  have hθh : θ h = ((a - b) * (a - 1)) • θ f := by
    change θ (t k - b • k) = _
    rw [map_sub, map_smul, hθ, ← sub_smul, hθk, smul_smul]
  let c := (a - b) * (a - 1)
  have hc : c ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr ha)
  refine ⟨c⁻¹ • h, p.ker.smul_mem _ hh, ?_⟩
  simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
  change θ (c⁻¹ • h - f) = 0
  rw [map_sub, map_smul, hθh]
  change c⁻¹ • (c • θ f) - θ f = 0
  rw [inv_smul_smul₀ hc, sub_self]

open MeasureTheory in
private theorem sLocalZeroMomentTheta_eq_top_fourier {F : Type*} [Field F] [NumberField F]
    {T : Finset (HeightOneSpectrum (𝓞 F))} (u : (SAdeleRing F T)ˣ) :
    ∃ b : ℝ≥0, ∀ f : SchwartzBruhat (Multiplicative (SAdeleRing F T)),
      sAdeleSchwartzFourier (schwartzBruhatUnitTranslate u f) (Multiplicative.ofAdd 0) =
        ((b : ℝ) : ℂ) * sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) := by
  let A := SAdeleRing F T
  let G := Multiplicative A
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  let : MeasurableSpace A :=
    inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × ((v : T) → v.val.adicCompletion F)))
  let μ : Measure G := sAdditiveTamagawaMeasure F T
  obtain ⟨hT₂, hLC, hBor, hHaar, hReg⟩ := sAdele_fourierMeasure (F := F) (S := T)
  let : T2Space G := hT₂
  let : LocallyCompactSpace G := hLC
  let : BorelSpace G := hBor
  let : μ.IsHaarMeasure := hHaar
  let : μ.Regular := hReg
  let d : G ≃ₜ* G :=
    { toFun := fun x ↦ Multiplicative.ofAdd ((↑u⁻¹ : A) * x.toAdd)
      invFun := fun x ↦ Multiplicative.ofAdd ((u : A) * x.toAdd)
      left_inv := fun x ↦ Multiplicative.ext (by simp [← mul_assoc])
      right_inv := fun x ↦ Multiplicative.ext (by simp [← mul_assoc])
      map_mul' := fun x y ↦ Multiplicative.ext (mul_add _ _ _)
      continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
      continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd) }
  -- Dilation sends additive Haar measure to a nonnegative multiple of itself.
  let ν := μ.map d
  let : ν.IsHaarMeasure := d.isHaarMeasure_map μ
  let : ν.Regular := Measure.Regular.map d.toHomeomorph
  refine ⟨ν.haarScalarFactor μ, fun f ↦ ?_⟩
  rw [sAdeleSchwartzFourier_apply_zero, sAdeleSchwartzFourier_apply_zero]
  change (∫ x : G, f (d.toHomeomorph.toMeasurableEquiv x) ∂μ) = _ * ∫ x : G, f x ∂μ
  rw [← integral_map_equiv d.toHomeomorph.toMeasurableEquiv (fun x ↦ f x)]
  change (∫ x : G, f x ∂ν) = _
  calc
    _ = ∫ x : G, f x ∂(ν.haarScalarFactor μ • μ) :=
      congrArg (fun m : Measure G ↦ ∫ x : G, f x ∂m)
        (Measure.isMulLeftInvariant_eq_smul_of_regular ν μ)
    _ = _ := by
      rw [integral_smul_nnreal_measure]
      rfl

/-- Paper: Equation (7.3.3.25), p. 363.
For a nontrivial norm-one character the tests with both zero moments
have the same homogeneous theta image as the unrestricted tests. -/
theorem sLocalZeroMomentTheta_eq_top (ω : PontryaginDual J₁(T)) (_hω : ω ≠ 1) :
    (Z₀(T)).map (q(T, ω)) = ⊤ := by
  have hex : ∃ h : J₁(T), (ω h : ℂ) ≠ 1 :=
    not_forall.mp fun hall ↦ _hω (PontryaginDual.ext fun x ↦ Subtype.ext (hall x))
  obtain ⟨h, hh⟩ := hex
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective h.val
  obtain ⟨b, hb⟩ := sLocalZeroMomentTheta_eq_top_fourier u
  have hne : (ω h : ℂ) ≠ ((b : ℝ) : ℂ) := by
    intro he
    have hb1 : (b : ℝ) = 1 :=
      (Real.norm_of_nonneg b.property).symm.trans
        ((Complex.norm_real _).symm.trans ((congrArg norm he).symm.trans (Circle.norm_coe _)))
    exact hh (he.trans (by exact_mod_cast hb1))
  apply sLocalZeroMomentTheta_eq_top_of_translate
    ((sAdelePolarValues_isLinear (F := F) (S := T)).mk' _)
    (sLocalHomogeneousAdelicThetaLinearMap F T ω)
    (schwartzBruhatUnitTranslate u) (ω h : ℂ) ((b : ℝ) : ℂ) hh hne
  · intro f
    apply Prod.ext
    · exact congrArg f (congrArg Multiplicative.ofAdd (mul_zero _))
    · exact hb f
  · exact sLocalHomogeneousTheta_unitTranslate ω h u hu


/-- The S-adelic Fourier transform applied four times is the identity. -/
theorem sAdeleSchwartzFourier_fourfold (f : B(S)) :
    sAdeleSchwartzFourier (sAdeleSchwartzFourier (sAdeleSchwartzFourier
      (sAdeleSchwartzFourier f))) = f := by
  apply Subtype.ext
  funext x
  exact (sLocal_fourier_inversion (sAdeleSchwartzFourier (sAdeleSchwartzFourier f))
    x.toAdd).trans ((sLocal_fourier_inversion f (-x.toAdd)).trans
      (congrArg (fun y ↦ f (Multiplicative.ofAdd y)) (neg_neg x.toAdd)))

/-- The transition from `S` to itself is the identity. -/
theorem sAdeleSchwartzTransition_self (f : B(S)) : sAdeleSchwartzTransition F (le_rfl (a := S)) f = f := by
  classical
  apply Subtype.ext
  funext x
  rw [← show Multiplicative.ofAdd x.toAdd = x from rfl, sAdeleSchwartzTransition_apply,
    ite_eq_left (fun w hw ↦ (hw w.property).elim)]

/-- Tests with compact Fourier support approximate every local test. -/
private theorem sLocalAbsolutePW_fourier_compact_seq (f : B(S)) :
    ∃ fₙ : ℕ → B(S), (∀ n, HasCompactSupport (sAdeleSchwartzFourier (fₙ n)).val) ∧
      Tendsto fₙ atTop (𝓝 f) := by
  obtain ⟨L, hL⟩ := sLocal_fourier_continuousLinear (F := F) (S := S)
  obtain ⟨u, hu, ht⟩ := exists_sAdeleSchwartz_compact_support_seq (sAdeleSchwartzFourier f)
  let M := L.comp (L.comp L)
  have hM (g : B(S)) : M g = sAdeleSchwartzFourier (sAdeleSchwartzFourier (sAdeleSchwartzFourier g)) := by
    change L (L (L g)) = _
    rw [hL, hL, hL]
  refine ⟨M ∘ u, fun n ↦ ?_, ?_⟩
  · change HasCompactSupport (sAdeleSchwartzFourier (M (u n))).val
    rw [hM, sAdeleSchwartzFourier_fourfold]
    exact hu n
  · have he := M.continuous.continuousAt.tendsto.comp ht
    rwa [hM, sAdeleSchwartzFourier_fourfold] at he

/-- The two zero moments can be imposed by subtracting fixed tests whose Fourier
transforms are compactly supported. -/
private theorem sLocalAbsolutePW_fourier_compact_seq_polar (f : Z₀(S)) :
    ∃ fₙ : ℕ → B(S), (∀ n, fₙ n ∈ Z₀(S) ∧ HasCompactSupport (sAdeleSchwartzFourier (fₙ n)).val) ∧
      Tendsto fₙ atTop (𝓝 f.val) := by
  obtain ⟨L, hL⟩ := sLocal_fourier_continuousLinear (F := F) (S := S)
  let P (g : B(S)) := g (Multiplicative.ofAdd 0)
  let Q (g : B(S)) := L g (Multiplicative.ofAdd 0)
  let K : Set (SAdeleRing F S) := univ
  obtain ⟨a, haK, haP, haQ⟩ := sLocalPWTests_moments_surjective (F := F) (S := S) (T := S)
    le_rfl K univ_mem 1 0
  obtain ⟨b, hbK, hbP, hbQ⟩ := sLocalPWTests_moments_surjective (F := F) (S := S) (T := S)
    le_rfl K univ_mem 0 1
  have hc (z : B(S)) (hz : z ∈ sLocalPWTests le_rfl K) :
      HasCompactSupport (L z).val := by
    obtain ⟨w, hw, hwc, -⟩ := (mem_sLocalPWTests le_rfl K z).mp hz
    rw [sAdeleSchwartzTransition_self] at hw
    rw [hL, ← hw]
    exact hwc
  obtain ⟨u, hu, ht⟩ := sLocalAbsolutePW_fourier_compact_seq f.val
  let r (g : B(S)) := g - P g • a - Q g • b
  have hP : Continuous P := continuous_sAdeleSchwartz_eval 0
  have hQ : Continuous Q := hP.comp L.continuous
  have hr : Continuous r := (continuous_id.sub (hP.smul continuous_const)).sub (hQ.smul continuous_const)
  have hf := (mem_sAdelePolarSubspace f.val).mp f.property
  have hrf : r f.val = f.val := by
    change f.val - (f.val (Multiplicative.ofAdd 0)) • a - (L f.val (Multiplicative.ofAdd 0)) • b = f.val
    rw [hL, hf.1, hf.2, zero_smul, zero_smul, sub_zero, sub_zero]
  refine ⟨r ∘ u, fun n ↦ ?_, ?_⟩
  · have he : L (r (u n)) = L (u n) - P (u n) • L a - Q (u n) • L b := by
      change L (u n - P (u n) • a - Q (u n) • b) = _
      simp only [map_sub, map_smul]
    change r (u n) ∈ Z₀(S) ∧ HasCompactSupport (sAdeleSchwartzFourier (r (u n))).val
    constructor
    · apply (mem_sAdelePolarSubspace _).mpr
      constructor
      · change P (u n) - P (u n) * a (Multiplicative.ofAdd 0) -
          Q (u n) * b (Multiplicative.ofAdd 0) = 0
        rw [haP, hbP, mul_one, mul_zero, sub_self, sub_zero]
      · rw [← hL, he]
        change Q (u n) - P (u n) * L a (Multiplicative.ofAdd 0) -
          Q (u n) * L b (Multiplicative.ofAdd 0) = 0
        rw [hL, hL, haQ, hbQ, mul_zero, mul_one, sub_zero, sub_self]
    · rw [← hL, he]
      have huc : HasCompactSupport (L (u n)).val := (hL (u n)).symm ▸ hu n
      exact (huc.sub ((hc a haK).smul_left (f := fun _ ↦ P (u n)))).sub
        ((hc b hbK).smul_left (f := fun _ ↦ Q (u n)))
  · have h := hr.continuousAt.tendsto.comp ht
    rwa [hrf] at h

/-- A compact set is contained in a sufficiently large Fourier box. -/
theorem exists_subset_sLocalPWBox_of_isCompact {K : Set (Multiplicative (SAdeleRing F S))}
    (hK : IsCompact K) : ∃ X > 0, K ⊆ Multiplicative.toAdd ⁻¹' sLocalPWBox S X := by
  let N (x : SAdeleRing F S) :=
    (∑ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) + ∑ v : S, ‖x.2 v‖
  have hN : Continuous N := (continuous_finsetSum _ fun w _ ↦
    ((continuous_apply w).comp continuous_fst).norm.pow w.mult).add
      (continuous_finsetSum _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  obtain ⟨R, hR⟩ := (hK.image (hN.comp continuous_toAdd)).bddAbove
  refine ⟨max R 1, zero_lt_one.trans_le (le_max_right _ _), fun x hx ↦ ?_⟩
  have hxR : N x.toAdd ≤ max R 1 := (hR (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  refine ⟨fun w ↦ ?_, fun v ↦ ?_⟩
  · exact (Finset.single_le_sum (fun i _ ↦ by positivity) (Finset.mem_univ w)).trans
      ((le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).trans hxR)
  · exact (Finset.single_le_sum (fun i _ ↦ norm_nonneg _) (Finset.mem_univ v)).trans
      ((le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ ↦ by positivity)).trans hxR)

/-- A test lies in the polar subspace at `T` after transition from `S` exactly when it does at `S`. -/
theorem sAdeleSchwartzTransition_mem_sAdelePolarSubspace_iff (hST : S ⊆ T) (f : B(S)) :
    Π(hST) f ∈ Z₀(T) ↔ f ∈ Z₀(S) := by
  classical
  obtain ⟨c, hc, hF⟩ := sLocalPWTests_moments_surjective_transition (F := F) hST
  have h0 : Π(hST) f (Multiplicative.ofAdd 0) = f (Multiplicative.ofAdd 0) := by
    rw [sAdeleSchwartzTransition_apply, ite_eq_left (fun w _ ↦ (w.val.adicCompletionIntegers F).zero_mem)]
    rfl
  rw [mem_sAdelePolarSubspace, mem_sAdelePolarSubspace, h0, hF, mul_eq_zero, or_iff_right hc]

open MeasureTheory in
/-- On the trivial local component the theta kernel has both moments zero, as
seen by continuing the class into the global trivial-character residue map. -/
private theorem sLocalAbsolutePW_trivial_kernel_polar (f : B(T))
    (hf : f ∈ (sLocalHomogeneousAdelicThetaLinearMap F T 1).ker) :
    f ∈ Z₀(T) := by
  let c : unramifiedOutside F T := ⟨1, (mem_unramifiedOutside_iff F T 1).mpr (fun _ _ _ ↦ rfl)⟩
  have hc : ∀ x : C₁, c.val x.val = ((1 : PontryaginDual C₁) x : ℂ) := fun _ ↦ rfl
  let hω : NormOneCharacterUnramifiedOutside (F := F) 1 T := ⟨c, hc⟩
  have htriv : sLocalNormOneCharacter (F := F) T 1 hω = 1 := by
    apply PontryaginDual.ext
    intro y
    apply Subtype.ext
    have h := sLocalNormOneCharacter_eq_sIdeleRestriction 1 c hc y
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective y.val
    rw [← hg, sIdeleRestriction_mk] at h
    exact h
  have hf' : f ∈ (sLocalHomogeneousAdelicThetaLinearMap F T
      (sLocalNormOneCharacter (F := F) T 1 hω)).ker := by rw [htriv]; exact hf
  let G := sAdeleSchwartzToGlobal F T f
  have hG : G ∈ (homogeneousAdelicThetaLinearMap F 1).ker :=
    sLocalHomogeneousThetaToGlobal_preserves_kernel hω hf'
  obtain ⟨R, hR, -, -, -⟩ := globalConverse_normTwist_exact (F := F)
  have hp := hR G
  rw [show (LinearMap.ker (homogeneousAdelicThetaLinearMap F 1)).mkQ G = 0 from
    (Submodule.Quotient.mk_eq_zero (homogeneousAdelicThetaLinearMap F 1).ker).mpr hG, map_zero] at hp
  let : MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _
  let μ := normOneIdeleClassTamagawaMeasure F
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : μ.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hm : ((μ univ).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (measureReal_univ_pos (μ := μ)).ne'
  have hG0 : G (Multiplicative.ofAdd 0) = 0 :=
    (mul_eq_zero.mp (congrArg Prod.fst hp.symm)).resolve_left (neg_ne_zero.mpr hm)
  have hGF : adeleSchwartzFourier G (Multiplicative.ofAdd 0) = 0 :=
    (mul_eq_zero.mp (congrArg Prod.snd hp.symm)).resolve_left hm
  obtain ⟨m, hm₀, hM⟩ := sAdeleSchwartzToGlobal_fourier_zero_scale (F := F) (S := T)
  apply (mem_sAdelePolarSubspace f).mpr
  constructor
  · change sAdeleSchwartzToGlobal F T f (Multiplicative.ofAdd 0) = 0 at hG0
    rwa [sAdeleSchwartzToGlobal_apply, ite_eq_left (fun v _ ↦ (v.adicCompletionIntegers F).zero_mem),
      map_zero] at hG0
  · change adeleSchwartzFourier (sAdeleSchwartzToGlobal F T f) (Multiplicative.ofAdd 0) = 0 at hGF
    rw [hM] at hGF
    exact (mul_eq_zero.mp hGF).resolve_left hm₀

/-- Each larger-stage quotient representative can be replaced by an inserted
test with the same pole constraint. -/
theorem sLocalAbsolutePW_exists_insert_rep
    (hST : S ⊆ T) (hPic : PicTrivial) (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside ω S) (χ : PontryaginDual J₁(T))
    (hχ : χ = descend(hST, ω, hω))
    (f : B(T)) :
    ∃ g : B(S), q(T, χ) (Π(hST) g) = q(T, χ) f ∧ (f ∈ Z₀(T) → g ∈ Z₀(S)) := by
  classical
  rcases eq_or_lt_of_le hST with h | h
  · subst T
    exact ⟨f, congrArg (q(S, χ)) (sAdeleSchwartzTransition_self f), id⟩
  · have hU : ∀ (x : J₁(T)) (u : relativeIntegralIdeleUnits F S T),
        x.val = QuotientGroup.mk u.val → χ x = 1 := by
      rw [hχ]
      exact sLocalHomogeneousThetaToGlobal_equiv_of_unramified_units hST hω
    obtain ⟨η, e, hη, he⟩ := sLocalHomogeneousThetaTransition_equiv_of_unramified h hPic χ hU
    let x := e.symm (q(T, χ) f)
    have hx (g : B(S)) (hg : q(S, η) g = x) : q(T, χ) (Π(hST) g) = q(T, χ) f :=
      (he g).symm.trans ((congrArg e hg).trans (e.apply_symm_apply _))
    by_cases ht : η = 1
    · obtain ⟨g, hg⟩ := (sLocalHomogeneousAdelicThetaLinearMap F S η).ker.mkQ_surjective x
      refine ⟨g, hx g hg, fun hf ↦ ?_⟩
      have ht' : χ = 1 := by
        apply PontryaginDual.ext
        intro y
        have h := hη y
        rw [ht] at h
        exact h.symm
      have hker : Π(hST) g - f ∈ (sLocalHomogeneousAdelicThetaLinearMap F T (1 : PontryaginDual J₁(T))).ker := by
        rw [← ht']
        apply (Submodule.Quotient.mk_eq_zero (sLocalHomogeneousAdelicThetaLinearMap F T χ).ker).mp
        change q(T, χ) (Π(hST) g - f) = 0
        rw [map_sub, hx g hg, sub_self]
      have hzero := sLocalAbsolutePW_trivial_kernel_polar (Π(hST) g - f) hker
      have hsum := (Z₀(T)).add_mem hzero hf
      rw [sub_add_cancel] at hsum
      exact (sAdeleSchwartzTransition_mem_sAdelePolarSubspace_iff hST g).mp hsum
    · have hy : x ∈ (Z₀(S)).map (q(S, η)) := by
        rw [sLocalZeroMomentTheta_eq_top η ht]
        exact Submodule.mem_top
      obtain ⟨g, hg, hq⟩ := Submodule.mem_map.mp hy
      exact ⟨g, hx g hq, fun _ ↦ hg⟩

private theorem sLocalAbsolutePW_push_seq (hST : S ⊆ T) (D : Submodule ℂ (B(T)))
    (χ : PontryaginDual J₁(T)) (g : B(S))
    (u : ℕ → B(S)) (hu : ∀ n, HasCompactSupport (sAdeleSchwartzFourier (u n)).val)
    (hD : ∀ n, Π(hST) (u n) ∈ D) (ht : Tendsto u atTop (𝓝 g)) :
    ∃ v : ℕ → Θ(T, χ), (∀ n, ∃ X > 0, v n ∈ sLocalAbsolutePW hST X D χ) ∧
      Tendsto v atTop (𝓝 (q(T, χ) (Π(hST) g))) := by
  refine ⟨fun n ↦ q(T, χ) (Π(hST) (u n)), fun n ↦ ?_, ?_⟩
  · obtain ⟨X, hX, hbox⟩ := exists_subset_sLocalPWBox_of_isCompact (hu n)
    exact ⟨X, hX, sLocalAbsolutePW_mk_mem hST X D χ (u n) ⟨hu n, hbox⟩ (hD n)⟩
  · exact (((sLocalHomogeneousAdelicThetaLinearMap F T χ).ker.mkQL.continuous).comp
      (sAdeleSchwartzTransition_isEmbedding F hST).continuous).continuousAt.tendsto.comp ht

/-- Paper: Proposition 7.3.2.2(1), p. 352.
The union of the absolute PW levels is sequentially dense in the full or zero-moment
homogeneous theta space, according to the chosen test constraint.
Deviation: Uses integer-ring insertion, as required by the density argument and §6.2. -/
theorem sLocalAbsolutePW_seqDense {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀)
    (_hPic : PicTrivial) (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu))
    (D : Submodule ℂ (B(T))) (_hD : D = ⊤ ∨ D = Z₀(T)) :
    ∀ (x : Θ(T, χ)), x ∈ D.map (q(T, χ)) → ∃ u : ℕ → Θ(T, χ),
      (∀ n, ∃ X > 0, u n ∈ sLocalAbsolutePW hST X D χ) ∧
        Tendsto u atTop (𝓝 x) := by
  intro x hx
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨g, hg, hpol⟩ := sLocalAbsolutePW_exists_insert_rep hST _hPic ω hu χ _hχ f
  rcases _hD with rfl | rfl
  · obtain ⟨u, hu, ht⟩ := sLocalAbsolutePW_fourier_compact_seq g
    rw [← hg]
    exact sLocalAbsolutePW_push_seq hST ⊤ χ g u hu (fun _ ↦ Submodule.mem_top) ht
  · obtain ⟨u, hu, ht⟩ := sLocalAbsolutePW_fourier_compact_seq_polar ⟨g, hpol hf⟩
    rw [← hg]
    exact sLocalAbsolutePW_push_seq hST (Z₀(T)) χ g u (fun n ↦ (hu n).2)
      (fun n ↦ (sAdeleSchwartzTransition_mem_sAdelePolarSubspace_iff hST (u n)).mpr (hu n).1) ht

/-- Paper: Theorem 2.2.3.2, p. 82, and the proof of Proposition 7.3.2.2(2)–(3), p. 353.
The global Fourier transform of the global insertion of an S-local test vanishes at every
adele where the S-local Fourier transform vanishes at the projection, and at every adele
having a coordinate outside S beyond a fixed bound. The bounds are at least one and equal
to one at all but finitely many places.
The proof would integrate over the integer tail: translation by the omitted integer rings
leaves the inserted test invariant, so the transform vanishes off the annihilator of those
rings, and on the annihilator the tail integrates to a positive constant
(compare `tamagawaFourier_sAdeleLift` in `AppA_AlgebraicNT/Sec3.lean`, where the bound is
the absolute norm of the place raised to the exponent of the different). -/
private theorem sLocalAbsolutePW_globalSupport_fourier {F : Type*} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ D : HeightOneSpectrum (𝓞 F) → ℝ, (∀ v, 1 ≤ D v) ∧ (mulSupport D).Finite ∧
      ∀ (h : SchwartzBruhat (Multiplicative (SAdeleRing F S))) (y : AdeleRing (𝓞 F) F),
        adeleSchwartzFourier (sAdeleSchwartzToGlobal F S h) (Multiplicative.ofAdd y) ≠ 0 →
          sAdeleSchwartzFourier h (Multiplicative.ofAdd (adeleProjection F S y)) ≠ 0 ∧
            ∀ v, v ∉ S → ‖y.2 v‖ ≤ D v := by
  classical
  let D (v : HeightOneSpectrum (𝓞 F)) :=
    (v.asIdeal.absNorm : ℝ) ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
  refine ⟨D, fun v ↦ one_le_pow₀ (by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).le), ?_, ?_⟩
  · apply (Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))).subset
    intro v hv
    by_contra hn
    exact hv (by simp [D, multiplicity_eq_zero_of_not_dvd hn])
  · obtain ⟨c, _, hc⟩ := adeleSchwartzFourier_sAdeleSchwartzToGlobal (F := F) (S := S)
    intro h y hy
    rw [hc] at hy
    split at hy
    · rename_i htail
      exact ⟨fun hz ↦ hy (by rw [hz, smul_zero]), htail⟩
    · exact (hy rfl).elim

/-- An idele whose S-coordinates lie in the S-product region of size `Y` and whose other
finite coordinates are bounded by `D` has idelic norm at most `Y` times the product of `D`. -/
private theorem sLocalAbsolutePW_globalSupport_norm {F : Type*} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (D : HeightOneSpectrum (𝓞 F) → ℝ)
    (hD : ∀ v, 1 ≤ D v) (hDf : (mulSupport D).Finite) (Y : ℝ) (z : IdeleGroup (𝓞 F) F)
    (hz : (∏ w : InfinitePlace F, ‖(adeleProjection F S z.val).1 w‖ ^ w.mult) *
      (∏ v : S, ‖(adeleProjection F S z.val).2 v‖) ≤ Y)
    (hout : ∀ v, v ∉ S → ‖z.val.2 v‖ ≤ D v) :
    ((ideleNorm F z : ℝ≥0) : ℝ) ≤ Y * ∏ᶠ v, D v := by
  classical
  obtain ⟨hfin, hnorm⟩ := (ideleNorm_spec F).1 z
  let a : HeightOneSpectrum (𝓞 F) → ℝ := fun v ↦ ‖z.val.2 v‖
  let U : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ hDf.toFinset ∪ Set.Finite.toFinset hfin
  have ha : (∏ᶠ v, a v) = ∏ v ∈ U, a v :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by simp [U, (Set.Finite.mem_toFinset hfin).mpr hv]
  have hDU : (∏ᶠ v, D v) = ∏ v ∈ U, D v :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by
      have hv' : D v ≠ 1 := hv
      simp [U, hv']
  have hSU : S ⊆ U := fun v hv ↦ by simp [U, hv]
  have hD0 (v) : 0 ≤ D v := zero_le_one.trans (hD v)
  let P := ∏ w : InfinitePlace F, ‖z.val.1 w‖ ^ w.mult
  have hP : 0 ≤ P := Finset.prod_nonneg fun w _ ↦ pow_nonneg (norm_nonneg _) _
  have hS : (∏ v ∈ S, a v) = ∏ v : S, ‖(adeleProjection F S z.val).2 v‖ :=
    (Finset.prod_coe_sort S a).symm
  have hPS : P * ∏ v ∈ S, a v ≤ Y := by
    rw [hS]
    exact hz
  have hSnn : 0 ≤ ∏ v ∈ S, a v := Finset.prod_nonneg fun v _ ↦ norm_nonneg _
  have hY : 0 ≤ Y := (mul_nonneg hP hSnn).trans hPS
  have hrest : (∏ v ∈ U \ S, a v) ≤ ∏ v ∈ U \ S, D v :=
    Finset.prod_le_prod₀ (fun v _ ↦ norm_nonneg _)
      fun v hv ↦ hout v (Finset.mem_sdiff.mp hv).2
  have hrestD : (∏ v ∈ U \ S, D v) ≤ ∏ v ∈ U, D v := by
    rw [← Finset.prod_sdiff hSU]
    exact le_mul_of_one_le_right (Finset.prod_nonneg fun v _ ↦ hD0 v)
      (Finset.one_le_prod₀ fun v _ ↦ hD v)
  have hrestD0 : 0 ≤ ∏ v ∈ U \ S, D v := Finset.prod_nonneg fun v _ ↦ hD0 v
  rw [show ((ideleNorm F z : ℝ≥0) : ℝ) = P * ∏ᶠ v, a v from hnorm, ha, hDU,
    ← Finset.prod_sdiff hSU]
  calc P * ((∏ v ∈ U \ S, a v) * ∏ v ∈ S, a v)
      = (P * ∏ v ∈ S, a v) * ∏ v ∈ U \ S, a v := by ring
    _ ≤ Y * ∏ v ∈ U \ S, D v := mul_le_mul hPS hrest
        (Finset.prod_nonneg fun v _ ↦ norm_nonneg _) hY
    _ ≤ Y * ∏ v ∈ U, D v := mul_le_mul_of_nonneg_left hrestD hY

/-- Paper: Proposition 7.3.2.2(2), p. 352, and Proposition 7.3.2.4(2), p. 356.
For any Fourier region inside an S-product region, the global homogeneous theta functions
of the inserted zero-moment tests vanish below a uniform positive idelic norm.
By Riemann–Roch they are the theta functions of the Fourier transforms at the inverse
class, and those vanish above a uniform norm by the product formula. -/
private theorem sLocalAbsolutePW_globalSupport_region {F : Type*} [Field F] [NumberField F]
    {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T)
    (ω : PontryaginDual (ideleClassNorm F).ker) (K : Set (SAdeleRing F S)) (Y : ℝ)
    (hY : 0 < Y)
    (hK : ∀ x ∈ K, (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) * (∏ v : S, ‖x.2 v‖) ≤ Y) :
    ∃ bound > (0 : ℝ), ∀ (f : SchwartzBruhat (Multiplicative (SAdeleRing F T))),
      f ∈ sLocalPWTests hST K ⊓ sAdelePolarSubspace F T →
      tsupport (homogeneousAdelicTheta ω (sAdeleSchwartzToGlobal F T f)) ⊆
        {g | bound⁻¹ ≤ ((ideleClassNorm F g).val : ℝ)} := by
  classical
  obtain ⟨D, hD, hDf, hA⟩ := sLocalAbsolutePW_globalSupport_fourier (F := F) S
  have hD1 : 1 ≤ ∏ᶠ v, D v := by
    rw [finprod_eq_prod_of_mulSupport_subset D (s := hDf.toFinset) fun v hv ↦
      hDf.mem_toFinset.mpr hv]
    exact Finset.one_le_prod₀ fun v _ ↦ hD v
  let bound := Y * ∏ᶠ v, D v
  have hb : 0 < bound := mul_pos hY (zero_lt_one.trans_le hD1)
  refine ⟨bound, hb, ?_⟩
  rintro f ⟨hf, hf0⟩
  obtain ⟨h, rfl, -, hhK⟩ := (mem_sLocalPWTests hST K f).mp hf
  let Φ := sAdeleSchwartzToGlobal F T (sAdeleSchwartzTransition F hST h)
  have hΦ : Φ = sAdeleSchwartzToGlobal F S h :=
    LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp (F := F) hST) h
  obtain ⟨hΦ0, hΦ1⟩ := (mem_adelePolarSubspace Φ).mp
    (sAdeleSchwartzToGlobal_mem_polarSubspace (F := F) (S := T) ⟨_, hf0⟩)
  -- The theta function of the Fourier transform vanishes at classes of large norm.
  have hlarge (z : IdeleGroup (𝓞 F) F) (hz : bound < ((ideleNorm F z : ℝ≥0) : ℝ)) :
      adelicTheta (adeleSchwartzFourier Φ) (QuotientGroup.mk z) = 0 := by
    rw [adelicTheta_mk]
    refine (tsum_congr fun ξ ↦ ?_).trans tsum_zero
    by_contra hne
    rw [hΦ] at hne
    obtain ⟨hloc, htail⟩ := hA h _ hne
    let u : IdeleGroup (𝓞 F) F := IdeleGroup.unitEmbedding (𝓞 F) F ξ * z
    have hu : u.val = algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * z.val := rfl
    have huK : adeleProjection F S u.val ∈ K := by
      have hmem := hhK (subset_tsupport _ hloc)
      rw [hu]
      exact hmem
    have hn := sLocalAbsolutePW_globalSupport_norm S D hD hDf Y u (hK _ huK)
      (fun v hv ↦ by rw [hu]; exact htail v hv)
    have hprin : ideleNorm F u = ideleNorm F z := by
      rw [map_mul, MonoidHom.mem_ker.mp ((ideleNorm_spec F).2 ⟨ξ, rfl⟩), one_mul]
    rw [hprin] at hn
    exact absurd hz (not_lt.mpr hn)
  -- Hence theta of the test vanishes at classes of small norm.
  have hsmall (x : IdeleClassGroup (𝓞 F) F)
      (hx : ((ideleClassNorm F x).val : ℝ) < bound⁻¹) : adelicTheta Φ x = 0 := by
    have hpos : (0 : ℝ) < ((ideleClassNorm F x).val : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (ideleClassNorm F x).ne_zero)
    rw [adelicTheta_riemannRoch, hΦ0, hΦ1, smul_zero, add_zero, sub_zero]
    induction x using QuotientGroup.induction_on with
    | _ z =>
      rw [← QuotientGroup.mk_inv]
      have hz : ((ideleClassNorm F (QuotientGroup.mk z)).val : ℝ) =
          ((ideleNorm F z : ℝ≥0) : ℝ) := rfl
      have hinv : bound < ((ideleNorm F z⁻¹ : ℝ≥0) : ℝ) := by
        rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, ← hz]
        exact (lt_inv_comm₀ hpos hb).mp hx
      rw [hlarge z⁻¹ hinv, smul_zero]
  have hclosed : IsClosed {g : IdeleClassGroup (𝓞 F) F |
      bound⁻¹ ≤ ((ideleClassNorm F g).val : ℝ)} :=
    isClosed_le continuous_const (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous))
  refine closure_minimal (fun g hg ↦ ?_) hclosed
  by_contra hlt
  simp only [Set.mem_ofPred_eq, not_le] at hlt
  apply hg
  change (∫ k, adelicTheta Φ (k.val * g) * (ω k : ℂ) ∂_) = 0
  refine (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun k ↦ ?_)).trans
    (MeasureTheory.integral_zero _ _)
  have hk : ((ideleClassNorm F (k.val * g)).val : ℝ) < bound⁻¹ := by
    rw [map_mul, MonoidHom.mem_ker.mp k.property, one_mul]
    exact hlt
  change adelicTheta Φ (k.val * g) * (ω k : ℂ) = 0
  rw [hsmall _ hk, zero_mul]

/-- Paper: Proposition 7.3.2.2(2), p. 352.
At fixed finite stages, global theta of every inserted zero-moment test at this absolute
level vanishes below a uniform positive idelic norm. -/
theorem sLocalAbsolutePW_globalSupport {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀)
    (_hPic : PicTrivial) (ω : PontryaginDual C₁) (_hu : NormOneCharacterUnramifiedOutside ω S)
    (X : ℝ) (_hX : 0 < X) :
    ∃ bound > (0 : ℝ), ∀ (f : B(T)), f ∈ sLocalPWTests hST (sLocalPWBox S X) ⊓ Z₀(T) →
      tsupport (homogeneousAdelicTheta ω (sAdeleSchwartzToGlobal F T f)) ⊆
        {g | bound⁻¹ ≤ ((ideleClassNorm F g).val : ℝ)} := by
  refine sLocalAbsolutePW_globalSupport_region hST ω _ (X ^ count(S)) (pow_pos _hX _) ?_
  rintro x ⟨hinf, hfin⟩
  rw [pow_add]
  have h1 : (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) ≤ X ^ Fintype.card (InfinitePlace F) :=
    calc (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) ≤ ∏ _w : InfinitePlace F, X :=
          Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (norm_nonneg _) _) fun w _ ↦ hinf w
      _ = X ^ Fintype.card (InfinitePlace F) := by rw [Finset.prod_const, Finset.card_univ]
  have h2 : (∏ v : S, ‖x.2 v‖) ≤ X ^ S.card :=
    calc (∏ v : S, ‖x.2 v‖) ≤ ∏ _v : S, X :=
          Finset.prod_le_prod₀ (fun v _ ↦ norm_nonneg _) fun v _ ↦ hfin v
      _ = X ^ S.card := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  exact mul_le_mul h1 h2 (Finset.prod_nonneg fun v _ ↦ norm_nonneg _) (pow_nonneg _hX.le _)

/-- Paper: Proposition 7.3.2.2(3), p. 352.
The local homogeneous theta of the Fourier-transformed level tests has a uniform upper
norm bound.
Deviation: Part (3) leaves the test variable free. The Fourier support bound applies to
every band-limited input, since the product norm bounds each contributing orbit. -/
theorem sLocalAbsolutePW_localFourierSupport {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀)
    (_hPic : PicTrivial) (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu))
    (X : ℝ) (_hX : 0 < X) :
    ∃ bound > (0 : ℝ), ∀ (f : B(T)), f ∈ sLocalPWTests hST (sLocalPWBox S X) →
      tsupport (sLocalHomogeneousAdelicThetaLinearMap F T χ (sAdeleSchwartzFourier f)) ⊆
          {g | ((m(T) g).val : ℝ) ≤ bound} := by
  let U := {v : T // v.val ∉ S}
  let radius (v : V) : ℝ :=
    (v.asIdeal.absNorm : ℝ) ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
  let bound₀ : ℝ :=
    X ^ (Fintype.card (InfinitePlace F) + S.card) * ∏ v : U, radius v.val.val
  let bound : ℝ := max 1 bound₀
  refine ⟨bound, zero_lt_one.trans_le (le_max_left 1 bound₀), fun f hf ↦ ?_⟩
  obtain ⟨g, rfl, _, hsupp⟩ := (mem_sLocalPWTests hST (sLocalPWBox S X) f).mp hf
  let φ : B(T) := sAdeleSchwartzFourier (Π(hST) g)
  have hbound_adele : ∀ y : SAdeleRing F T,
      φ (Multiplicative.ofAdd y) ≠ 0 →
        (∏ w : InfinitePlace F, ‖y.1 w‖ ^ w.mult) * ∏ v : T, ‖y.2 v‖ ≤ bound := by
    intro y hy
    obtain ⟨hyS_ne, hyU_bound⟩ := sLocalAbsolutePW_fourier_transition_support (F := F) hST g y hy
    have hyS_box : (y.1, fun w : S ↦ y.2 ⟨w.val, hST w.property⟩) ∈ sLocalPWBox S X :=
      hsupp (subset_tsupport _ hyS_ne)
    have harch : (∏ w : InfinitePlace F, ‖y.1 w‖ ^ w.mult) ≤
        X ^ Fintype.card (InfinitePlace F) := by
      calc
        _ ≤ ∏ _w : InfinitePlace F, X :=
          Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (norm_nonneg _) _) fun w _ ↦ hyS_box.1 w
        _ = X ^ Fintype.card (InfinitePlace F) := by
          rw [Finset.prod_const, Finset.card_univ]
    have hfinS : (∏ v : {v : T // v.val ∈ S}, ‖y.2 v.val‖) ≤ X ^ S.card := by
      let eS : S ≃ {v : T // v.val ∈ S} :=
        { toFun := fun w ↦ ⟨⟨w.val, hST w.property⟩, w.property⟩
          invFun := fun v ↦ ⟨v.val.val, v.property⟩
          left_inv := fun ⟨_, _⟩ ↦ rfl
          right_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl }
      calc
        (∏ v : {v : T // v.val ∈ S}, ‖y.2 v.val‖)
          = ∏ w : S, ‖y.2 ⟨w.val, hST w.property⟩‖ := Fintype.prod_equiv eS.symm _ _ fun _ ↦ rfl
        _ ≤ ∏ _w : S, X :=
          Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun w _ ↦ hyS_box.2 w
        _ = X ^ S.card := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    have hfinU : (∏ v : U, ‖y.2 v.val‖) ≤ ∏ v : U, radius v.val.val :=
      Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun v _ ↦ hyU_bound v
    have hfin : (∏ v : T, ‖y.2 v‖) ≤ X ^ S.card * ∏ v : U, radius v.val.val := by
      rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : T ↦ v.val ∈ S) (fun v : T ↦ ‖y.2 v‖)]
      exact mul_le_mul hfinS hfinU (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
        (pow_nonneg _hX.le _)
    have htot : (∏ w : InfinitePlace F, ‖y.1 w‖ ^ w.mult) * (∏ v : T, ‖y.2 v‖) ≤ bound₀ := by
      calc
        _ ≤ X ^ Fintype.card (InfinitePlace F) * (X ^ S.card * ∏ v : U, radius v.val.val) :=
          mul_le_mul harch hfin (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
            (pow_nonneg _hX.le _)
        _ = bound₀ := by
          dsimp only [bound₀]
          rw [pow_add, mul_assoc]
    exact htot.trans (le_max_right 1 bound₀)
  have hvanish : ∀ q : J(T), bound < ((m(T) q).val : ℝ) →
      sLocalHomogeneousAdelicThetaLinearMap F T χ φ q = 0 := by
    intro q hq
    rw [sLocalHomogeneousAdelicThetaLinearMap_apply]
    have hint : ∀ h : J₁(T), sLocalAdelicThetaOnClasses F T φ (q * h.val) * (χ h : ℂ) = 0 := by
      intro h
      have hm_eq : m(T) (q * h.val) = m(T) q := by
        rw [map_mul, MonoidHom.mem_ker.mp h.property, mul_one]
      have hq' : bound < ((m(T) (q * h.val)).val : ℝ) := hm_eq.symm ▸ hq
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (q * h.val)
      have ha_theta : sLocalAdelicThetaOnClasses F T φ (QuotientGroup.mk a) = 0 := by
        rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
        have hzero : ∀ ξ : (Set.integer (T : Set V) F)ˣ,
            φ (Multiplicative.ofAdd (Units.val (sUnitEmbedding F T ξ * a))) = 0 := by
          intro ξ
          let unitAtT : (Set.integer (T : Set V) F)ˣ →* (SAdeleRing F T)ˣ :=
            sUnitEmbedding F T
          by_contra hnz
          have hle := hbound_adele (unitAtT ξ * a).val hnz
          have hnorm_unit : sIdeleNorm F T (unitAtT ξ) = 1 :=
            MonoidHom.mem_ker.mp ((sIdeleNorm_spec F T).2 ⟨ξ, rfl⟩)
          have hnorm_eq : ((sIdeleNorm F T (unitAtT ξ * a)).val : ℝ) =
              ((m(T) (q * h.val)).val : ℝ) := by
            rw [map_mul, hnorm_unit, one_mul, ← ha, sIdeleQuotientNorm_mk]
          have hmod_fn (z : (SAdeleRing F T)ˣ) : ((sIdeleNorm F T z).val : ℝ) =
              (∏ w : InfinitePlace F, ‖z.val.1 w‖ ^ w.mult) * ∏ v : T, ‖z.val.2 v‖ := by
            simp [sIdeleNorm]
          have hmod := hmod_fn (unitAtT ξ * a)
          linarith [hle, hmod, hnorm_eq, hq']
        exact (tsum_congr hzero).trans tsum_zero
      rw [← ha, ha_theta, zero_mul]
    simp only [hint]
    exact MeasureTheory.integral_zero (α := ↥J₁(T)) (G := ℂ)
  refine closure_minimal (fun q hq ↦ ?_) ?_
  · by_contra hle
    exact hq (hvanish q (lt_of_not_ge hle))
  · exact isClosed_le (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_sIdeleQuotientNorm F T).continuous)) continuous_const

end AbsoluteLevels

/-- A dilate of a compactly supported function by a self-homeomorphism is compactly supported,
and its support stays in a set whose preimage under the homeomorphism it contains. -/
private theorem sLocalAbsolutePW_translate_support {G : Type*} [TopologicalSpace G]
    (e : G ≃ₜ G) (b : ℂ) (φ ψ : G → ℂ) (hψ : ∀ x, ψ x = b * φ (e x)) (s : Set G)
    (hs : e ⁻¹' s ⊆ s) (hc : HasCompactSupport φ) (hφ : tsupport φ ⊆ s) :
    HasCompactSupport ψ ∧ tsupport ψ ⊆ s := by
  have hsub : tsupport ψ ⊆ e ⁻¹' tsupport φ := by
    refine closure_minimal (fun x hx ↦ ?_) ((isClosed_tsupport φ).preimage e.continuous)
    refine subset_tsupport φ ?_
    intro h0
    exact hx ((hψ x).trans (by rw [h0, mul_zero]))
  have hcomp : IsCompact (e ⁻¹' tsupport φ) := e.isCompact_preimage.mpr hc
  exact ⟨hcomp.of_isClosed_subset (isClosed_tsupport ψ) hsub,
    hsub.trans ((Set.preimage_mono hφ).trans hs)⟩

/-- The S-adelic Fourier transform of a unit translate is a nonnegative multiple of the
dilate of the Fourier transform by the same unit. -/
theorem sLocalAbsolutePW_translate_fourier {F : Type*} [Field F] [NumberField F]
    {T : Finset (HeightOneSpectrum (𝓞 F))} (u : (SAdeleRing F T)ˣ) :
    ∃ b : ℝ≥0, ∀ (f : SchwartzBruhat (Multiplicative (SAdeleRing F T))) (y : SAdeleRing F T),
      sAdeleSchwartzFourier (schwartzBruhatUnitTranslate u f) (Multiplicative.ofAdd y) =
        ((b : ℝ) : ℂ) * sAdeleSchwartzFourier f (Multiplicative.ofAdd ((u : SAdeleRing F T) * y)) := by
  let A := SAdeleRing F T
  let G := Multiplicative A
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  let : MeasurableSpace A :=
    inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × ((v : T) → v.val.adicCompletion F)))
  let μ : MeasureTheory.Measure G := sAdditiveTamagawaMeasure F T
  obtain ⟨hT₂, hLC, hBor, hHaar, hReg⟩ := sAdele_fourierMeasure (F := F) (S := T)
  let : T2Space G := hT₂
  let : LocallyCompactSpace G := hLC
  let : BorelSpace G := hBor
  let : μ.IsHaarMeasure := hHaar
  let : μ.Regular := hReg
  let d : G ≃ₜ* G :=
    { toFun := fun x ↦ Multiplicative.ofAdd ((↑u⁻¹ : A) * x.toAdd)
      invFun := fun x ↦ Multiplicative.ofAdd ((u : A) * x.toAdd)
      left_inv := fun x ↦ Multiplicative.ext (by simp [← mul_assoc])
      right_inv := fun x ↦ Multiplicative.ext (by simp [← mul_assoc])
      map_mul' := fun x y ↦ Multiplicative.ext (mul_add _ _ _)
      continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
      continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd) }
  let ν := μ.map d
  let : ν.IsHaarMeasure := d.isHaarMeasure_map μ
  let : ν.Regular := MeasureTheory.Measure.Regular.map d.toHomeomorph
  refine ⟨ν.haarScalarFactor μ, fun f y ↦ ?_⟩
  let k : G → ℂ := fun x ↦
    f x * star ((sAdeleStandardCharacter F T (x.toAdd * ((u : A) * y)) : Circle) : ℂ)
  have h1 : (∫ x : G, k (d.toHomeomorph.toMeasurableEquiv x) ∂μ) =
      ((ν.haarScalarFactor μ : ℝ) : ℂ) * ∫ x : G, k x ∂μ := by
    rw [← MeasureTheory.integral_map_equiv d.toHomeomorph.toMeasurableEquiv k]
    change (∫ x : G, k x ∂ν) = _
    calc
      _ = ∫ x : G, k x ∂(ν.haarScalarFactor μ • μ) :=
        congrArg (fun m : MeasureTheory.Measure G ↦ ∫ x : G, k x ∂m)
          (MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_regular ν μ)
      _ = _ := by
        rw [MeasureTheory.integral_smul_nnreal_measure]
        rfl
  refine Eq.trans ?_ h1
  change (∫ x : A, f (Multiplicative.ofAdd ((↑u⁻¹ : A) * x)) *
    star ((sAdeleStandardCharacter F T (x * y) : Circle) : ℂ) ∂(sAdditiveTamagawaMeasure F T)) =
    ∫ x : A, f (Multiplicative.ofAdd ((↑u⁻¹ : A) * x)) *
      star ((sAdeleStandardCharacter F T (((↑u⁻¹ : A) * x) * ((u : A) * y)) : Circle) : ℂ)
      ∂(sAdditiveTamagawaMeasure F T)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  change _ * star ((sAdeleStandardCharacter F T (x * y) : Circle) : ℂ) =
    _ * star ((sAdeleStandardCharacter F T (((↑u⁻¹ : A) * x) * ((u : A) * y)) : Circle) : ℂ)
  rw [mul_mul_mul_comm, Units.inv_mul, one_mul]

/-- A level built from a Fourier region that is stable under shrinking by ideles of absolute
value at least one at the infinite places and one at the finite places is preserved by the
classes of norm at least one. The norm-one part of a class acts by a scalar, and the remaining
part is represented by a positive real at one infinite place. -/
private theorem sLocalAbsolutePW_translate_level (hST : S ⊆ T) (K : Set (SAdeleRing F S))
    (hK : ∀ a : (SAdeleRing F S)ˣ, (∀ w : InfinitePlace F, 1 ≤ ‖a.val.1 w‖) →
      (∀ v : S, ‖a.val.2 v‖ = 1) → ∀ y : SAdeleRing F S, a.val * y ∈ K → y ∈ K)
    (D : Submodule ℂ (B(T))) (hD : D = ⊤ ∨ D = Z₀(T))
    (ω : PontryaginDual J₁(T)) (g : J(T)) (hg : large(g))
    (x : Θ(T, ω)) (hx : x ∈ level(hST, K, D, ω)) :
    A(T, ω) g x ∈ level(hST, K, D, ω) := by
  classical
  let ρ := A(T, ω)
  have hρ : ∀ (a : (SAdeleRing F T)ˣ) (f : B(T)),
      ρ (QuotientGroup.mk a) (q(T, ω) f) = q(T, ω) (schwartzBruhatUnitTranslate a f) :=
    (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T) ω).exists.choose_spec.2
  refine map_mem_closure (ρ g).continuous hx ?_
  rintro _ ⟨f, ⟨hf, hfD⟩, rfl⟩
  obtain ⟨h, rfl, hband⟩ := (mem_sLocalPWTests hST K f).mp hf
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let t : ℝ≥0ˣ := m(T) g
  let x₀ := (infinitePlaceRealPower F w (w.mult : ℝ)⁻¹ t).val
  have hx₀ : 1 ≤ ‖x₀‖ := by
    have hiso : ‖InfinitePlace.Completion.extensionEmbedding w x₀‖ = ‖x₀‖ :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _) x₀
    rw [← hiso, infinitePlaceRealPower_apply, Complex.norm_real, Real.norm_eq_abs]
    exact (Real.one_le_rpow hg (inv_nonneg.mpr (Nat.cast_nonneg _))).trans (le_abs_self _)
  have hsS : ∃ uS : (integralAdelesOutside F S)ˣ,
      integralIdeleInsertion F S uS = singlePlaceIdeleNormSection F w t := by
    refine (mem_range_integralIdeleInsertion F S _).mpr fun v _ ↦ ⟨?_, ?_⟩
    · exact (v.adicCompletionIntegers F).one_mem
    · change ((singlePlaceIdeleNormSection F w t)⁻¹).val.2 v ∈ _
      rw [← map_inv]
      exact (v.adicCompletionIntegers F).one_mem
  obtain ⟨uS, huS⟩ := hsS
  let gS := Units.map (adeleProjection F S).toMonoidHom (integralIdeleInsertion F S uS)
  let gT := Units.map (adeleProjection F T).toMonoidHom (integralIdeleInsertion F S uS)
  have htr : Π(hST) (schwartzBruhatUnitTranslate gS h) =
      schwartzBruhatUnitTranslate gT (Π(hST) h) := testTransition_translate_eq hST uS h
  have hnorm : m(T) (QuotientGroup.mk gT) = t := by
    obtain ⟨uT, huT⟩ := integralIdeleInsertion_mem_range_of_subset hST uS
    have hspec := (sIdeleNorm_spec F T).1 uT
    have hgT : gT = Units.map ((adeleProjection F T).comp
        (integralAdelesOutside F T).subtype).toMonoidHom uT := by
      change Units.map (adeleProjection F T).toMonoidHom (integralIdeleInsertion F S uS) = _
      rw [← huT]
      rfl
    change sIdeleNorm F T gT = t
    rw [hgT, ← hspec]
    change ideleNorm F (integralIdeleInsertion F T uT) = t
    rw [huT, huS]
    exact singlePlaceIdeleNormSection_rightInverse F w t
  let g₀ : J(T) := g * (QuotientGroup.mk gT)⁻¹
  have hg₀ : g₀ ∈ (m(T)).ker := MonoidHom.mem_ker.mpr (by
    change m(T) (g * (QuotientGroup.mk gT)⁻¹) = 1
    rw [map_mul, map_inv, hnorm]
    exact mul_inv_cancel t)
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective g₀
  have hgv : g = QuotientGroup.mk v * QuotientGroup.mk gT := by
    rw [hv]
    exact (inv_mul_cancel_right g _).symm
  let c : ℂ := (ω ⟨g₀, hg₀⟩ : ℂ)
  have hscal := sLocalHomogeneousTheta_unitTranslate ω ⟨g₀, hg₀⟩ v hv
    (schwartzBruhatUnitTranslate gT (Π(hST) h))
  have hq : q(T, ω) (schwartzBruhatUnitTranslate v (schwartzBruhatUnitTranslate gT (Π(hST) h))) =
      c • q(T, ω) (schwartzBruhatUnitTranslate gT (Π(hST) h)) := by
    rw [← map_smul]
    refine (Submodule.Quotient.eq _).mpr (LinearMap.mem_ker.mpr ?_)
    rw [map_sub, map_smul, hscal, sub_self]
  have key : ρ g (q(T, ω) (Π(hST) h)) =
      c • q(T, ω) (Π(hST) (schwartzBruhatUnitTranslate gS h)) := by
    rw [hgv, map_mul]
    change ρ (QuotientGroup.mk v) (ρ (QuotientGroup.mk gT) (q(T, ω) (Π(hST) h))) = _
    rw [hρ, hρ, hq, htr]
  change ρ g (q(T, ω) (Π(hST) h)) ∈ ((sLocalPWTests hST K ⊓ D).map (q(T, ω)))
  rw [key]
  refine Submodule.smul_mem _ _ (Submodule.mem_map_of_mem
    ⟨(mem_sLocalPWTests hST K _).mpr ⟨_, rfl, ?_⟩, ?_⟩)
  · obtain ⟨b, hb⟩ := sLocalAbsolutePW_translate_fourier gS
    let e : Multiplicative (SAdeleRing F S) ≃ₜ Multiplicative (SAdeleRing F S) :=
      { toFun := fun y ↦ Multiplicative.ofAdd ((gS : SAdeleRing F S) * y.toAdd)
        invFun := fun y ↦ Multiplicative.ofAdd ((↑gS⁻¹ : SAdeleRing F S) * y.toAdd)
        left_inv := fun y ↦ Multiplicative.ext (by simp [← mul_assoc])
        right_inv := fun y ↦ Multiplicative.ext (by simp [← mul_assoc])
        continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
        continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd) }
    refine sLocalAbsolutePW_translate_support e ((b : ℝ) : ℂ) (sAdeleSchwartzFourier h).val
      (sAdeleSchwartzFourier (schwartzBruhatUnitTranslate gS h)).val (fun y ↦ hb h y.toAdd)
      (Multiplicative.toAdd ⁻¹' K) ?_ hband.1 hband.2
    intro y hy
    refine hK gS (fun w' ↦ ?_) (fun v' ↦ ?_) y.toAdd hy
    · have h1 : (gS : SAdeleRing F S).1 w' = Pi.mulSingle w x₀ w' :=
        congrArg (fun z : IdeleGroup (𝓞 F) F ↦ z.val.1 w') huS
      rw [h1]
      by_cases hw : w' = w
      · subst hw
        rw [Pi.mulSingle_eq_same]
        exact hx₀
      · rw [Pi.mulSingle_eq_of_ne hw, norm_one]
    · have h2 : (gS : SAdeleRing F S).2 v' = 1 :=
        congrArg (fun z : IdeleGroup (𝓞 F) F ↦ z.val.2 v'.val) huS
      rw [h2, norm_one]
  · rcases hD with rfl | rfl
    · trivial
    · rw [htr]
      obtain ⟨h0, h1⟩ := (mem_sAdelePolarSubspace _).mp hfD
      obtain ⟨b, hb⟩ := sLocalAbsolutePW_translate_fourier gT
      refine (mem_sAdelePolarSubspace _).mpr ⟨?_, ?_⟩
      · refine (schwartzBruhatUnitTranslate_apply gT _ 0).trans ?_
        rw [mul_zero]
        exact h0
      · rw [hb, mul_zero, h1, mul_zero]

/-- Paper: Proposition 7.3.2.2(4), p. 352.
Left translation by an idele class of norm at least one preserves the absolute levels,
with or without the zero-moment constraint.
Deviation: Stated directly for the local norm-one character and the inclusion of stages.
The preservation uses no class-number assumption. -/
theorem sLocalAbsolutePW_translate (hST : S ⊆ T) {X : ℝ} (_hX : 0 < X)
    (D : Submodule ℂ (B(T))) (_hD : D = ⊤ ∨ D = Z₀(T))
    (ω : PontryaginDual J₁(T)) (g : J(T)) (_hg : large(g))
    (x : Θ(T, ω)) (_hx : x ∈ sLocalAbsolutePW hST X D ω) :
    A(T, ω) g x ∈ sLocalAbsolutePW hST X D ω := by
  refine sLocalAbsolutePW_translate_level hST (sLocalPWBox S X) ?_ D _hD ω g _hg x _hx
  intro a ha1 ha2 y hy
  refine ⟨fun w ↦ le_trans ?_ (hy.1 w), fun v ↦ le_trans ?_ (hy.2 v)⟩
  · refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    change ‖y.1 w‖ ≤ ‖a.val.1 w * y.1 w‖
    rw [norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) (ha1 w)
  · change ‖y.2 v‖ ≤ ‖a.val.2 v * y.2 v‖
    rw [norm_mul, ha2 v, one_mul]

/-- Paper: Definition 7.3.2.3(1), p. 354–355.
The invariant Fourier region bounds the product of the normalized local absolute values,
including at tuples having a zero coordinate. -/
def sLocalPWProductRegion (S : Finset V) (Y : ℝ) : Set (SAdeleRing F S) :=
  {x | (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) * (∏ v : S, ‖x.2 v‖) ≤ Y}

/-- Paper: Definition 7.3.2.3(1), p. 355.
On invertible adeles the product bound is the S-idelic norm bound. -/
theorem mem_sLocalPWProductRegion_units (Y : ℝ) (u : (SAdeleRing F S)ˣ) :
    u.val ∈ sLocalPWProductRegion S Y ↔ ((sIdeleNorm F S u).val : ℝ) ≤ Y := by
  simp [sLocalPWProductRegion, sIdeleNorm, Units.coe_prod]

/-- Paper: Definition 7.3.2.3(2), p. 355.
The invariant PW level is the closure of the theta image of tests with compact Fourier
support in the product region, optionally subject to the zero-moment constraint.
Deviation: Uses the cited integer-ring insertion and the unrestricted test space for
the unrestricted level. The sentence after (7.3.2.17) repeats the zero-moment space. -/
def sLocalInvariantPW (hST : S ⊆ T) (Y : ℝ) (D : Submodule ℂ (B(T)))
    (ω : PontryaginDual J₁(T)) : Submodule ℂ (Θ(T, ω)) :=
  level(hST, sLocalPWProductRegion S Y, D, ω)

/-- Paper: Definition 7.3.2.3(2), p. 355.
An inserted test with compact Fourier support in the product region and satisfying the
chosen test constraint represents an element of the invariant level.
Deviation: Uses the integer-ring insertion of the cited transition. -/
theorem sLocalInvariantPW_mk_mem (hST : S ⊆ T) (Y : ℝ) (D : Submodule ℂ (B(T)))
    (ω : PontryaginDual J₁(T)) (f : B(S)) (_hf : inBand(sLocalPWProductRegion S Y, f))
    (_hD : Π(hST) f ∈ D) : q(T, ω) (Π(hST) f) ∈ sLocalInvariantPW hST Y D ω :=
  Submodule.le_topologicalClosure _
    (Submodule.mem_map_of_mem ⟨Submodule.mem_map_of_mem (Submodule.subset_span _hf), _hD⟩)

/-- Paper: Proposition 7.3.2.4(1), p. 355.
Increasing the product bound enlarges each of the two invariant PW levels. -/
theorem sLocalInvariantPW_mono (hST : S ⊆ T) {Y Y' : ℝ} (_hYY' : Y ≤ Y')
    (D : Submodule ℂ (B(T))) (ω : PontryaginDual J₁(T)) :
    sLocalInvariantPW hST Y D ω ≤ sLocalInvariantPW hST Y' D ω := by
  have hbox : sLocalPWProductRegion S Y ⊆ sLocalPWProductRegion S Y' :=
    fun _ hx ↦ le_trans hx _hYY'
  have hgen : {f : B(S) | inBand(sLocalPWProductRegion S Y, f)} ⊆
      {f : B(S) | inBand(sLocalPWProductRegion S Y', f)} :=
    fun _ hf ↦ ⟨hf.1, hf.2.trans (Set.preimage_mono hbox)⟩
  have htests : sLocalPWTests hST (sLocalPWProductRegion S Y) ≤ sLocalPWTests hST (sLocalPWProductRegion S Y') :=
    Submodule.map_mono (Submodule.span_mono hgen)
  exact Submodule.topologicalClosure_mono (Submodule.map_mono (inf_le_inf htests le_rfl))

section InvariantLevels

open Classical

/-- Paper: Proposition 7.3.2.4(1), p. 356.
The union of the invariant PW levels is sequentially dense in the corresponding
full or zero-moment homogeneous theta space.
Deviation: Uses integer-ring insertion, as in the density proof. -/
theorem sLocalInvariantPW_seqDense {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀)
    (_hPic : PicTrivial) (ω : PontryaginDual C₁) (hu : NormOneCharacterUnramifiedOutside ω S)
    (χ : PontryaginDual J₁(T)) (_hχ : χ = descend(hST, ω, hu))
    (D : Submodule ℂ (B(T))) (_hD : D = ⊤ ∨ D = Z₀(T)) :
    ∀ (x : Θ(T, χ)), x ∈ D.map (q(T, χ)) → ∃ u : ℕ → Θ(T, χ),
      (∀ n, ∃ Y > 0, u n ∈ sLocalInvariantPW hST Y D χ) ∧
        Tendsto u atTop (𝓝 x) := by
  intro x hx
  have seq := sLocalAbsolutePW_seqDense (F := F) hST _hT _hdis _hsat _hPic ω hu χ _hχ D _hD x hx
  refine ⟨seq.choose, fun n ↦ ?_, seq.choose_spec.2⟩
  let X := (seq.choose_spec.1 n).choose
  have hn := (seq.choose_spec.1 n).choose_spec.2
  let m : SAdeleRing F S → ℝ := fun y ↦
    (∏ w : InfinitePlace F, ‖y.1 w‖ ^ w.mult) * (∏ v : S, ‖y.2 v‖)
  have hm : Continuous m := by
    dsimp only [m]
    exact (continuous_finsetProd Finset.univ (fun w _ ↦
      ((continuous_apply w).comp continuous_fst).norm.pow w.mult)).mul
      (continuous_finsetProd Finset.univ (fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm))
  have bounded := ((isCompact_sLocalPWBox (F := F) (S := S) X).image hm).bddAbove
  let Y : ℝ := bounded.choose
  have hY : Y ∈ upperBounds (m '' sLocalPWBox S X) := bounded.choose_spec
  have hbox : sLocalPWBox S X ⊆ sLocalPWProductRegion S (max 1 Y) :=
    fun y hy ↦ (hY (Set.mem_image_of_mem m hy)).trans (le_max_right _ _)
  have hgen : {f : B(S) | inBand(sLocalPWBox S X, f)} ⊆
      {f : B(S) | inBand(sLocalPWProductRegion S (max 1 Y), f)} :=
    fun _ hf ↦ ⟨hf.1, hf.2.trans (Set.preimage_mono hbox)⟩
  have htests : sLocalPWTests hST (sLocalPWBox S X) ≤
      sLocalPWTests hST (sLocalPWProductRegion S (max 1 Y)) :=
    Submodule.map_mono (Submodule.span_mono hgen)
  have hlevel : sLocalAbsolutePW hST X D χ ≤ sLocalInvariantPW hST (max 1 Y) D χ :=
    Submodule.topologicalClosure_mono (Submodule.map_mono (inf_le_inf htests (le_refl D)))
  exact ⟨max 1 Y, zero_lt_one.trans_le (le_max_left _ _), hlevel hn⟩

/-- Paper: Proposition 7.3.2.4(2), p. 356.
At fixed finite stages, the global theta of the invariant zero-moment level tests has
a uniform positive lower idelic norm bound. -/
theorem sLocalInvariantPW_globalSupport {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (_hT : T = S ∪ S₀)
    (_hdis : Disjoint S S₀) (_hsat : IsSaturatedPlaceSet (F := F) S₀)
    (_hPic : PicTrivial) (ω : PontryaginDual C₁) (_hu : NormOneCharacterUnramifiedOutside ω S)
    (Y : ℝ) (_hY : 0 < Y) :
    ∃ bound > (0 : ℝ), ∀ (f : B(T)), f ∈ sLocalPWTests hST (sLocalPWProductRegion S Y) ⊓ Z₀(T) →
      tsupport (homogeneousAdelicTheta ω (sAdeleSchwartzToGlobal F T f)) ⊆
        {g | bound⁻¹ ≤ ((ideleClassNorm F g).val : ℝ)} :=
  sLocalAbsolutePW_globalSupport_region hST ω _ Y _hY fun _ hx ↦ hx

end InvariantLevels

end RiemannMasullo
