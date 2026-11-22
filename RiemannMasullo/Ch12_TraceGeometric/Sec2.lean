module

public import RiemannMasullo.Ch12_TraceGeometric.Sec1a
public import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.Extension
public import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Lebesgue differentiation along the diagonal

Masullo, §12.2, pp. 504–513. Completed-measure measurability is expressed as
`AEMeasurable` on the Borel measure space. Kernel smoothenings use the extension
by zero from §12.1, with regularity hypotheses where the paper uses their values.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology
open scoped CompactlySupported ENNReal Pointwise

namespace RiemannMasullo

local instance instQuotientMeasurableSpaceSec2 {G : Type*} [Group G] [TopologicalSpace G]
    (H : Subgroup G) : MeasurableSpace (G ⧸ H) := borel _

section Indentations

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G]
  (H : Subgroup G)

local notation "Q" => G ⧸ H
local notation "π" => QuotientGroup.mk' H

/-- Paper: Definition 12.2.1.3, p. 506. An indentation is a continuous nonnegative real
function whose support meets the saturation of every compact set in a compact set, and
whose integral over each subgroup fibre converges and equals one. -/
def IsIndentation (μH : Measure H) (b : G → ℝ) : Prop :=
  Continuous b ∧ (∀ x, 0 ≤ b x) ∧
    (∀ K : Set G, IsCompact K → IsCompact (tsupport b ∩ π ⁻¹' (π '' K))) ∧
    ∀ x : G, Integrable (fun h : H ↦ b ((h : G)⁻¹ * x)) μH ∧
      (∫ h : H, b ((h : G)⁻¹ * x) ∂μH) = 1

/-- Paper: Definition 12.2.1.3, p. 506. For the trivial subgroup with unit counting
measure, the indentations are exactly the constant one function. -/
theorem isIndentation_bot_iff (b : G → ℝ) :
    IsIndentation (⊥ : Subgroup G) Measure.count b ↔ b = fun _ ↦ 1 := by
  have hcount := Subsingleton.count_eq_dirac (1 : (⊥ : Subgroup G))
  constructor
  · intro hb
    funext x
    simpa [hcount] using (hb.2.2.2 x).2
  · rintro rfl
    refine ⟨continuous_const, fun _ ↦ zero_le_one, ?_, ?_⟩
    · intro K hK
      have hinj : Function.Injective (QuotientGroup.mk' (⊥ : Subgroup G)) :=
        (QuotientGroup.quotientBot (G := G)).symm.injective
      rw [Set.preimage_image_eq _ hinj]
      exact hK.inter_left (isClosed_tsupport _)
    · intro x
      simp [hcount]

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G]
  (hH : IsClosed (H : Set G)) (μH : Measure H) [μH.IsHaarMeasure]

include hH in
/-- Paper: Lemma 12.2.1.1(1)–(3), p. 504. Every closed subgroup with a choice of
Haar measure has an indentation. The fibre integral is identically one on the group,
which entails continuity and invariance. -/
theorem exists_indentation : ∃ b : G → ℝ, IsIndentation H μH b := by sorry

/-- Paper: (12.2.1.8), p. 506. Lift a quotient function by pulling it back and
multiplying by the indentation. -/
def indentationLift (b : G → ℝ) (u : Q → ℂ) (x : G) : ℂ :=
  (b x : ℂ) * u (π x)

include hH in
/-- Paper: Lemma 12.2.1.1, p. 505. The lift of a continuous quotient function is
integrable on every subgroup fibre and its fibre integral recovers the quotient value. -/
theorem integral_indentationLift {b : G → ℝ} (hb : IsIndentation H μH b)
    (u : C(Q, ℂ)) (x : G) :
    Integrable (fun h : H ↦ indentationLift H b u ((h : G)⁻¹ * x)) μH ∧
      (∫ h : H, indentationLift H b u ((h : G)⁻¹ * x) ∂μH) = u (π x) := by
  obtain ⟨hi, he⟩ := hb.2.2.2 x
  have hcoset (h : H) : π ((h : G)⁻¹ * x) = π x := by
    have h1 : π (h : G) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
    rw [map_mul, map_inv, h1, inv_one, one_mul]
  simp only [indentationLift, hcoset]
  refine ⟨hi.ofReal.mul_const _, ?_⟩
  rw [integral_mul_const, integral_complex_ofReal, he, Complex.ofReal_one, one_mul]

/-- Paper: (12.2.1.5), p. 505. Fibre integration of a compactly supported test
commutes with complex scalar multiplication. -/
theorem indentationAverage_smul (c : ℂ) (f : C_c(G, ℂ)) :
    (TopologicalGroup.IsSES.ofClosedSubgroup H hH).pushforward μH (c • f) =
      c • (TopologicalGroup.IsSES.ofClosedSubgroup H hH).pushforward μH f := by
  let e := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  apply DFunLike.ext
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
  change e.pushforward μH (c • f) (π x) = c • e.pushforward μH f (π x)
  rw [e.pushforward_apply_apply, e.pushforward_apply_apply]
  simp only [TopologicalGroup.IsSES.pullback_def, CompactlySupportedContinuousMap.smul_apply,
    integral_smul]

/-- Paper: (12.2.1.5), p. 505. The quotient average of a compactly supported
continuous function integrates over the subgroup fibres and is a complex-linear
map into compactly supported continuous functions. -/
def indentationAverage : C_c(G, ℂ) →ₗ[ℂ] C_c(Q, ℂ) where
  toFun := (TopologicalGroup.IsSES.ofClosedSubgroup H hH).pushforward μH
  map_add' := ((TopologicalGroup.IsSES.ofClosedSubgroup H hH).pushforward μH).map_add
  map_smul' := indentationAverage_smul H hH μH

/-- Paper: (12.2.1.5), p. 506. Evaluate the quotient average at the coset of any
representative by integrating its inverse subgroup translates. -/
theorem indentationAverage_apply (f : C_c(G, ℂ)) (x : G) :
    Integrable (fun h : H ↦ f ((h : G)⁻¹ * x)) μH ∧
      indentationAverage H hH μH f (π x) = ∫ h : H, f ((h : G)⁻¹ * x) ∂μH := by
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : TopologicalSpace.PseudoMetrizableSpace H :=
    hH.isClosedEmbedding_subtypeVal.isInducing.pseudoMetrizableSpace
  let e := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  have hinv (h : H) : e.pullback f x h⁻¹ = f ((h : G)⁻¹ * x) := by
    rw [e.pullback_def]
    simp [mul_comm]
  constructor
  · simpa only [hinv] using ((e.pullback f x).integrable (μ := μH)).comp_inv
  · change e.pushforward μH f (π x) = _
    rw [e.pushforward_apply_apply]
    simpa only [hinv] using (integral_inv_eq_self (e.pullback f x) μH).symm

/-- Paper: (12.2.1.6), p. 506. A regular positive measure upstairs lifts a quotient
measure if its integrals on compactly supported continuous tests agree with the
quotient integrals of the fibre averages. -/
def IsIndentationMeasureLift (ν₀ : Measure Q) (μ₀ : Measure G) : Prop :=
  μ₀.Regular ∧
    ∀ f : C_c(G, ℂ), (∫ q, indentationAverage H hH μH f q ∂ν₀) = ∫ x, f x ∂μ₀

/-- Paper: (12.2.1.6), p. 506. Weil-normalized Haar measures give an instance of the
measure lift from the quotient. -/
theorem isIndentationMeasureLift_of_weil {μ : Measure G} [μ.IsHaarMeasure]
    {ν : Measure Q} (hν : IsWeilQuotientMeasure H μ μH ν) :
    IsIndentationMeasureLift H hH μH ν μ := by
  let e := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  refine ⟨inferInstance, fun f ↦ ?_⟩
  refine Eq.trans ?_ (hν.2.2 f.toContinuousMap f.hasCompactSupport).symm
  apply integral_congr_ae
  apply ae_of_all
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  change _ = lcaCosetIntegral H μH f (QuotientGroup.mk x)
  rw [lcaCosetIntegral_mk H μH f x]
  · exact e.pushforward_apply_apply μH f x
  · exact (e.pullback f x).integrable

/-- Paper: Corollary 12.2.1.2(1), p. 506. Each positive Radon measure on the quotient
has a unique positive Radon lift satisfying the normalization on compact tests.
Deviation: Regularity of the lift is explicit, as in the proof. -/
theorem existsUnique_indentationMeasureLift (ν₀ : Measure Q) [ν₀.Regular] :
    ∃! μ₀ : Measure G, IsIndentationMeasureLift H hH μH ν₀ μ₀ := by
  let : BorelSpace Q := ⟨rfl⟩
  let e := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  let L : C_c(G, ℝ) →ₚ[ℝ] ℝ :=
    ⟨{ toFun := fun f ↦ ∫ q, e.pushforward μH f q ∂ν₀
       map_add' := fun f g ↦ by
         rw [map_add]
         exact integral_add (e.pushforward μH f).integrable (e.pushforward μH g).integrable
       map_smul' := fun c f ↦ by
         rw [map_smul]
         exact integral_smul c (e.pushforward μH f) },
      fun f g h ↦ integral_mono (e.pushforward μH f).integrable
        (e.pushforward μH g).integrable (e.pushforward_mono μH h)⟩
  let μ := RealRMK.rieszMeasure L
  have hreal (f : C_c(G, ℝ)) :
      (∫ x, f x ∂μ) = ∫ q, e.pushforward μH f q ∂ν₀ :=
    RealRMK.integral_rieszMeasure L f
  have hcomplex (f : C_c(G, ℂ)) :
      (∫ x, f x ∂μ) = ∫ q, indentationAverage H hH μH f q ∂ν₀ := by
    let fr : C_c(G, ℝ) := ⟨⟨fun x ↦ (f x).re, Complex.continuous_re.comp f.continuous⟩,
      f.hasCompactSupport.comp_left (g := Complex.re) (by simp)⟩
    let fi : C_c(G, ℝ) := ⟨⟨fun x ↦ (f x).im, Complex.continuous_im.comp f.continuous⟩,
      f.hasCompactSupport.comp_left (g := Complex.im) (by simp)⟩
    apply Complex.ext
    · change RCLike.re (∫ x, f x ∂μ) = RCLike.re (∫ q, indentationAverage H hH μH f q ∂ν₀)
      rw [← integral_re f.integrable, ← integral_re (indentationAverage H hH μH f).integrable]
      change (∫ x, fr x ∂μ) = ∫ q, (indentationAverage H hH μH f q).re ∂ν₀
      rw [hreal fr]
      apply integral_congr_ae
      apply ae_of_all
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
      change e.pushforward μH fr (π x) = (e.pushforward μH f (π x)).re
      rw [e.pushforward_apply_apply, e.pushforward_apply_apply]
      simpa only [TopologicalGroup.IsSES.pullback_def, fr, CompactlySupportedContinuousMap.coe_mk,
        ContinuousMap.coe_mk, RCLike.re_eq_complex_re] using
        (integral_re ((e.pullback f x).integrable (μ := μH)))
    · change RCLike.im (∫ x, f x ∂μ) = RCLike.im (∫ q, indentationAverage H hH μH f q ∂ν₀)
      rw [← integral_im f.integrable, ← integral_im (indentationAverage H hH μH f).integrable]
      change (∫ x, fi x ∂μ) = ∫ q, (indentationAverage H hH μH f q).im ∂ν₀
      rw [hreal fi]
      apply integral_congr_ae
      apply ae_of_all
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
      change e.pushforward μH fi (π x) = (e.pushforward μH f (π x)).im
      rw [e.pushforward_apply_apply, e.pushforward_apply_apply]
      simpa only [TopologicalGroup.IsSES.pullback_def, fi, CompactlySupportedContinuousMap.coe_mk,
        ContinuousMap.coe_mk, RCLike.im_eq_complex_im] using
        (integral_im ((e.pullback f x).integrable (μ := μH)))
  refine ⟨μ, ⟨inferInstance, fun f ↦ (hcomplex f).symm⟩, ?_⟩
  intro μ' hμ'
  let : μ'.Regular := hμ'.1
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let F : C_c(G, ℂ) := ⟨⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩,
    f.hasCompactSupport.comp_left Complex.ofReal_zero⟩
  apply Complex.ofReal_injective
  simpa only [F, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk,
    integral_complex_ofReal] using (hμ'.2 F).symm.trans (hcomplex F).symm

/-- Paper: Corollary 12.2.1.2(1), p. 506. The lifted measure is invariant under
left translation by every subgroup element. -/
theorem map_mul_indentationMeasureLift {ν₀ : Measure Q} [ν₀.Regular] {μ₀ : Measure G}
    (hμ₀ : IsIndentationMeasureLift H hH μH ν₀ μ₀) (h : H) :
    μ₀.map (fun x : G ↦ (h : G) * x) = μ₀ := by
  let e := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  let L := Homeomorph.mulLeft (h : G)
  let : μ₀.Regular := hμ₀.1
  let : (μ₀.map L).Regular := Measure.Regular.map L
  change μ₀.map L = μ₀
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let F : C_c(G, ℂ) := ⟨⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩,
    f.hasCompactSupport.comp_left Complex.ofReal_zero⟩
  let Fh := F.comp L.toCocompactMap
  have havg (q : Q) : indentationAverage H hH μH Fh q = indentationAverage H hH μH F q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    change e.pushforward μH Fh (π x) = e.pushforward μH F (π x)
    rw [e.pushforward_apply_apply, e.pushforward_apply_apply]
    change (∫ k : H, F ((h : G) * (x * (k : G))) ∂μH) = ∫ k : H, F (x * (k : G)) ∂μH
    simpa only [Subgroup.coe_mul, mul_left_comm (h : G) x] using
      (integral_mul_left_eq_self (μ := μH) (fun k : H ↦ F (x * (k : G))) h)
  have hint := (hμ₀.2 Fh).symm.trans ((integral_congr_ae (ae_of_all ν₀ havg)).trans (hμ₀.2 F))
  refine (integral_map (μ := μ₀) (f := fun x ↦ f x) L.continuous.measurable.aemeasurable
    (map_continuous f).aestronglyMeasurable).trans ?_
  apply Complex.ofReal_injective
  simpa only [integral_complex_ofReal] using
    (show (∫ x, (f (L x) : ℂ) ∂μ₀) = ∫ x, (f x : ℂ) ∂μ₀ from hint)

/-- Paper: Corollary 12.2.1.2(2), p. 506. Fibre integration extends to a surjective
continuous complex-linear map of L¹ spaces, agreeing with the original map on compact tests. -/
theorem exists_indentationAverageL1 {ν₀ : Measure Q} [ν₀.Regular] {μ₀ : Measure G}
    (hμ₀ : IsIndentationMeasureLift H hH μH ν₀ μ₀) :
    ∃ A : Lp ℂ 1 μ₀ →L[ℂ] Lp ℂ 1 ν₀,
      Function.Surjective A ∧
        ∀ (f : C_c(G, ℂ)) (F : Lp ℂ 1 μ₀), (F : G → ℂ) =ᵐ[μ₀] f →
          (A F : Q → ℂ) =ᵐ[ν₀] indentationAverage H hH μH f := by sorry

/-- Paper: Corollary 12.2.1.2(2), p. 506. Multiplying the pulled-back L¹ representative
by any indentation defines an isometric continuous linear right inverse to the L¹ extension. -/
theorem exists_indentationLiftL1 {ν₀ : Measure Q} [ν₀.Regular] {μ₀ : Measure G}
    (hμ₀ : IsIndentationMeasureLift H hH μH ν₀ μ₀)
    (A : Lp ℂ 1 μ₀ →L[ℂ] Lp ℂ 1 ν₀)
    (hA : ∀ (f : C_c(G, ℂ)) (F : Lp ℂ 1 μ₀), (F : G → ℂ) =ᵐ[μ₀] f →
      (A F : Q → ℂ) =ᵐ[ν₀] indentationAverage H hH μH f)
    {b : G → ℝ} (hb : IsIndentation H μH b) :
    ∃ L : Lp ℂ 1 ν₀ →L[ℂ] Lp ℂ 1 μ₀,
      Isometry L ∧ Function.RightInverse L A ∧
        ∀ u : Lp ℂ 1 ν₀, (L u : G → ℂ) =ᵐ[μ₀] indentationLift H b u := by sorry

end Indentations

section ProperActions

variable {A X : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
  [T2Space A] [LocallyCompactSpace A] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MulAction A X] [ContinuousSMul A X] [ProperSMul A X]
  [IsCancelSMul A X] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace X] [BorelSpace X]

local notation "Ω" => MulAction.orbitRel.Quotient A X
local instance instOrbitQuotientMeasurableSpaceSec2 : MeasurableSpace Ω := borel _

-- Mathlib supplies the Hausdorff orbit quotient of a proper action, the open quotient map,
-- and second countability of the quotient of a second countable space.
/-- Paper: Remark 12.2.1.4, p. 507. For a free proper action, an invariant Radon measure
and a choice of Haar measure determine a unique Radon measure on the orbit space.
Deviation: The normalization formula is tested on compactly supported continuous functions. -/
theorem existsUnique_properActionQuotientMeasure (μA : Measure A) [μA.IsHaarMeasure]
    (μX : Measure X) [μX.Regular] [SMulInvariantMeasure A X μX] :
    ∃! ν : Measure Ω, ν.Regular ∧
      ∀ f : C_c(X, ℂ),
        Integrable (fun q : Ω ↦ ∫ a : A, f (a • q.out) ∂μA) ν ∧
          (∫ x, f x ∂μX) = ∫ q : Ω, ∫ a : A, f (a • q.out) ∂μA ∂ν := by sorry

end ProperActions

section FundamentalDomains

variable {A X : Type*} [Group A] [MulAction A X] [TopologicalSpace X] [MeasurableSpace X]

-- TODO(paper-gap): (12.2.1.13) lies in X but is assigned a measure on X/G.
-- For the discrete subgroup cases below, a null overlap upstairs is equivalent
-- to its image being null for the corresponding normalized quotient measure.
/-- Paper: Remark 12.2.1.4, p. 507. The domain has nonempty interior, each point has
a unique translate in it, and the closure has null overlap with each of its
nonidentity translates.
Deviation: The overlap is measured upstairs. We drop connectedness for §12.2.2:
already for the rational ideles a connected set has singleton projection to ℚₚˣ
at every finite place, and hence has empty interior. -/
def IsIndentationFundamentalDomain (A : Type*) [Group A] [MulAction A X]
    (μ : Measure X) (D : Set X) : Prop :=
  (interior D).Nonempty ∧
    (∀ x : X, ∃! a : A, a • x ∈ D) ∧
    ∀ a : A, a ≠ 1 → μ (closure D ∩ a • closure D) = 0

/-- Paper: Remark 12.2.1.4, p. 507. With the trivial group acting, the whole space is
a fundamental domain exactly when it is nonempty under the relaxed definition. -/
theorem isIndentationFundamentalDomain_univ_punit (μ : Measure X) :
    IsIndentationFundamentalDomain PUnit μ (univ : Set X) ↔
      (univ : Set X).Nonempty := by
  unfold IsIndentationFundamentalDomain
  rw [interior_univ]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun _ ↦ ⟨PUnit.unit, mem_univ _, fun _ _ ↦ rfl⟩,
    fun a ha ↦ absurd (Subsingleton.elim a 1) ha⟩⟩

/-- Paper: Remark 12.2.1.4, p. 507. With countably many translates and a Borel
measure, the paper's exact tiling gives a measure-theoretic fundamental domain. -/
theorem IsIndentationFundamentalDomain.isFundamentalDomain [Countable A] [BorelSpace X]
    {μ : Measure X} {D : Set X} (hD : IsIndentationFundamentalDomain A μ D) :
    IsFundamentalDomain A D μ := by
  have hnull : μ (closure D \ D) = 0 := by
    refine measure_mono_null (t := ⋃ a : {g : A // g ≠ 1}, closure D ∩ a.val • closure D) ?_
      (measure_iUnion_null fun a ↦ hD.2.2 a.val a.property)
    rintro x ⟨hx, hxD⟩
    obtain ⟨g, hg, -⟩ := hD.2.1 x
    have hg1 : g ≠ 1 := by
      rintro rfl
      exact hxD (by simpa only [one_smul] using hg)
    refine mem_iUnion.mpr ⟨⟨g⁻¹, inv_ne_one.mpr hg1⟩, hx, ?_⟩
    exact ⟨g • x, subset_closure hg, inv_smul_smul g x⟩
  have heq : closure D =ᵐ[μ] D := ae_eq_set.mpr
    ⟨hnull, by rw [sdiff_eq_empty.mpr subset_closure, measure_empty]⟩
  exact IsFundamentalDomain.mk' (isClosed_closure.measurableSet.nullMeasurableSet.congr heq)
    hD.2.1

end FundamentalDomains

section Diagonal

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)

local notation "Q" => G ⧸ H
local notation "π" => QuotientGroup.mk' H
local notation "q₂" => (Prod.map (QuotientGroup.mk' H) (QuotientGroup.mk' H))
local notation "countH" => (Measure.count : Measure H)

/-- Paper: Situation 12.2.2.1, p. 508. The domain for the translation action contains a
D′-sequence of relatively compact open symmetric neighborhoods of the identity. The discrete
closed subgroup and the compatible Haar measures are the standing hypotheses of the results. -/
def IsDiagonalIndentationSituation (μ : Measure G) (D : Set G) (U : ℕ → Set G) : Prop :=
  IsIndentationFundamentalDomain H μ D ∧ IsDPrimeSequence μ U ∧
    ∀ n, U n ⊆ D ∧ IsOpen (U n) ∧ IsCompact (closure (U n)) ∧ (U n)⁻¹ = U n

/-- Paper: Situation 12.2.2.1, p. 508. On the one-element group, the whole space
is a fundamental domain and also supplies the constant neighborhood sequence. -/
theorem isDiagonalIndentationSituation_subsingleton [Subsingleton G] :
    IsDiagonalIndentationSituation (⊥ : Subgroup G) Measure.count univ (fun _ ↦ univ) := by
  have hmass : (Measure.count : Measure G) univ = 1 := by
    simp [Subsingleton.count_eq_dirac (1 : G)]
  refine ⟨⟨by simp, fun x ↦ ⟨1, mem_univ _, fun h _ ↦ Subsingleton.elim _ _⟩,
    fun h hh ↦ (hh (Subsingleton.elim _ _)).elim⟩, ⟨⟨?_, antitone_const, ?_⟩, ?_⟩, ?_⟩
  · intro n
    simp [hmass]
  · refine ⟨2, by norm_num, fun n ↦ ?_⟩
    simp [hmass]
  · intro W hW
    refine ⟨0, fun x _ ↦ ?_⟩
    simpa only [Subsingleton.elim x (1 : G)] using mem_of_mem_nhds hW
  · intro n
    simp

variable [DiscreteTopology H] (hH : IsClosed (H : Set G))
  {μ : Measure G} [μ.IsHaarMeasure] {ν : Measure (G ⧸ H)}
  (hν : IsWeilQuotientMeasure H μ Measure.count ν)
  {D : Set G} {U : ℕ → Set G} (hS : IsDiagonalIndentationSituation H μ D U)

local notation "Ū" => (fun n ↦ (QuotientGroup.mk' H) '' U n)

include hH hν hS in
/-- Paper: Situation 12.2.2.1, p. 508. The quotient images of the neighborhoods in
the fundamental domain form a D′-sequence for the normalized quotient Haar measure. -/
theorem IsDiagonalIndentationSituation.quotient :
    IsDPrimeSequence ν Ū := by sorry

/-- Paper: (12.2.2.1), p. 508. Multiply the two indentation factors and integrate
their simultaneous subgroup translates. -/
def diagonalIndentationWeight (μH : Measure H) (b : G → ℝ) (p : G × G) : ℝ :=
  ∫ h : H, b ((h : G)⁻¹ * p.1) * b ((h : G)⁻¹ * p.2) ∂μH

/-- Paper: (12.2.2.1), p. 508. Averaging over the trivial subgroup with unit counting
measure returns the product of the two indentation factors. -/
theorem diagonalIndentationWeight_bot (b : G → ℝ) (p : G × G) :
    diagonalIndentationWeight (⊥ : Subgroup G) Measure.count b p = b p.1 * b p.2 := by
  simp [diagonalIndentationWeight, Subsingleton.count_eq_dirac (1 : (⊥ : Subgroup G))]

variable {b : G → ℝ} (hb : IsIndentation H Measure.count b)

include hH hν hS hb in
/-- Paper: Proposition 12.2.2.2(1), p. 508. The product of simultaneous translates is
integrable in the subgroup variable at every pair. -/
theorem integrable_diagonalIndentationWeight (p : G × G) :
    Integrable (fun h : H ↦ b ((h : G)⁻¹ * p.1) * b ((h : G)⁻¹ * p.2)) countH := by
  have hx := (hb.2.2.2 p.1).1
  have hy := (hb.2.2.2 p.2).1
  have hs := integrable_count_iff.mp hy
  exact hx.mul_bdd hy.aestronglyMeasurable
    (ae_of_all _ fun h ↦ hs.le_tsum h fun k _ ↦ norm_nonneg _)

include hH hν hS hb in
/-- Paper: Proposition 12.2.2.2(1), p. 508. The averaged indentation weight is continuous. -/
theorem continuous_diagonalIndentationWeight :
    Continuous (diagonalIndentationWeight H countH b) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨C, hC, hp⟩ := exists_compact_mem_nhds p.1
  let K := tsupport b ∩ π ⁻¹' (π '' C)
  have hK : IsCompact K := hb.2.2.1 C hC
  let T := (Subtype.val : H → G) ⁻¹' ((fun z : G × G ↦ z.1 * z.2⁻¹) '' (C ×ˢ K))
  have hT : T.Finite := (hH.isClosedEmbedding_subtypeVal.isCompact_preimage
    ((hC.prod hK).image (continuous_fst.mul continuous_snd.inv))).finite_of_discrete
  let term (h : H) (q : G × G) := b ((h : G)⁻¹ * q.1) * b ((h : G)⁻¹ * q.2)
  have hc (h : H) : Continuous (term h) :=
    (hb.1.comp (continuous_const.mul continuous_fst)).mul
      (hb.1.comp (continuous_const.mul continuous_snd))
  apply (continuous_finsetSum hT.toFinset fun h _ ↦ hc h).continuousAt.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt hp] with q hq
  have hzero (h : H) (hh : h ∉ hT.toFinset) : term h q = 0 := by
    suffices hz : b ((h : G)⁻¹ * q.1) = 0 by simp [term, hz]
    by_contra hn
    apply hh
    refine hT.mem_toFinset.mpr ⟨(q.1, (h : G)⁻¹ * q.1), ⟨hq, ?_⟩, ?_⟩
    · refine ⟨subset_tsupport b hn, q.1, hq, ?_⟩
      have hπ : π (h : G) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
      simp [map_mul, map_inv, hπ]
    · change q.1 * ((h : G)⁻¹ * q.1)⁻¹ = (h : G)
      simp [mul_inv_rev, ← mul_assoc]
  have hi : Integrable (fun h ↦ term h q) countH := integrable_count_iff.mpr
    (summable_of_ne_finset_zero (s := hT.toFinset) fun h hh ↦ by simp [hzero h hh])
  change (∫ h, term h q ∂countH) = _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (hT.toFinset : Set H)) hzero,
    setIntegral_finset hT.toFinset hi.integrableOn]
  simp only [count_real_singleton, one_smul]

include hH hν hS hb in
/-- Paper: Proposition 12.2.2.2(1), p. 508. The averaged indentation weight is nonnegative. -/
theorem diagonalIndentationWeight_nonneg (p : G × G) :
    0 ≤ diagonalIndentationWeight H countH b p := by
  exact integral_nonneg fun h ↦ mul_nonneg (hb.2.1 _) (hb.2.1 _)

include hH hν hS hb in
/-- Paper: Proposition 12.2.2.2(1), p. 508. Translating both coordinates by the same
subgroup element leaves the averaged weight invariant. -/
theorem diagonalIndentationWeight_mul (h : H) (p : G × G) :
    diagonalIndentationWeight H countH b ((h : G) * p.1, (h : G) * p.2) =
      diagonalIndentationWeight H countH b p := by
  let w (k : H) := b ((k : G)⁻¹ * p.1) * b ((k : G)⁻¹ * p.2)
  change (∫ k : H, b ((k : G)⁻¹ * ((h : G) * p.1)) *
    b ((k : G)⁻¹ * ((h : G) * p.2)) ∂countH) = ∫ k, w k ∂countH
  calc
    _ = ∫ k : H, w (h⁻¹ * k) ∂countH := by
      apply integral_congr_ae
      exact ae_of_all _ fun k ↦ by simp [w, mul_assoc]
    _ = _ := integral_mul_left_eq_self w h⁻¹

/-- Paper: (12.2.2.2), p. 508. Lift a quotient kernel by pulling it back in both
coordinates and multiplying by the subgroup-averaged indentation weight. -/
def diagonalIndentationLift (μH : Measure H) (b : G → ℝ) (u : Q × Q → ℂ)
    (p : G × G) : ℂ :=
  (diagonalIndentationWeight H μH b p : ℂ) * u (q₂ p)

/-- Paper: (12.2.2.2), p. 508. For the trivial subgroup with unit counting measure,
the kernel lift is a product of the two indentation factors and the pulled-back value. -/
theorem diagonalIndentationLift_bot (b : G → ℝ)
    (u : (G ⧸ (⊥ : Subgroup G)) × (G ⧸ (⊥ : Subgroup G)) → ℂ) (x y : G) :
    diagonalIndentationLift (⊥ : Subgroup G) Measure.count b u (x, y) =
      (b x : ℂ) * (b y : ℂ) * u (QuotientGroup.mk x, QuotientGroup.mk y) := by
  simp [diagonalIndentationLift, diagonalIndentationWeight,
    Subsingleton.count_eq_dirac (1 : (⊥ : Subgroup G))]

variable {u : (G ⧸ H) × (G ⧸ H) → ℂ} (hu : LocallyIntegrable u (ν.prod ν))

local notation "uSmooth" => (dSequenceKernelSmoothening ν Ū u)
local notation "Ψ" => (diagonalIndentationLift H (Measure.count : Measure H) b)

/-- Weil's formula makes the preimage of a quotient-null set null. -/
private theorem aemeasurable_diagonalIndentationLift_quotient_qmp
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
    [DiscreteTopology H] (hH : IsClosed (H : Set G))
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μ Measure.count ν) :
    QuasiMeasurePreserving (QuotientGroup.mk' H) μ ν := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : (Measure.count : Measure H).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let qmap : G → G ⧸ H := QuotientGroup.mk' H
  have hqmap : Measurable qmap := QuotientGroup.continuous_mk.measurable
  refine ⟨hqmap.aemeasurable, Measure.AbsolutelyContinuous.mk ?_⟩
  intro S hS hnull
  rw [Measure.map_apply hqmap hS]
  let f : G → ℂ := (qmap ⁻¹' S).indicator (fun _ ↦ 1)
  have hpre : MeasurableSet (qmap ⁻¹' S) := hS.preimage hqmap
  have hf : Measurable f := measurable_const.indicator hpre
  have hnot : ∀ᵐ q ∂ν, q ∉ S := measure_eq_zero_iff_ae_notMem.mp hnull
  have hquot (q : G ⧸ H) (h : H) : qmap (q.out * (h : G)) = q := by
    have hh : qmap (h : G) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
    change (QuotientGroup.mk' H) (q.out * (h : G)) = q
    dsimp only [qmap] at hh
    rw [map_mul, hh, mul_one]
    exact Quotient.out_eq' q
  have hzero (q : G ⧸ H) (hq : q ∉ S) (h : H) :
      f (q.out * (h : G)) = 0 := by
    exact indicator_of_notMem (by simpa only [mem_preimage, hquot] using hq) _
  have hnorm :
      (∫⁻ q, ∫⁻ h : H, ‖f (q.out * (h : G))‖₊ ∂Measure.count ∂ν) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hnot] with q hq
    simp [hzero q hq]
  obtain ⟨hi, he⟩ := integrable_of_weilNormIntegral H hH μ Measure.count ν hν hf
    (by rw [hnorm]; exact ENNReal.zero_lt_top)
  have hfib : lcaCosetIntegral H Measure.count f =ᵐ[ν] fun _ ↦ 0 := by
    filter_upwards [hnot] with q hq
    simp [lcaCosetIntegral, hzero q hq]
  rw [integral_congr_ae hfib, integral_zero] at he
  have hfinite : μ (qmap ⁻¹' S) < ∞ := by
    simpa using ((integrable_indicator_iff hpre).mp hi)
  have hreal : μ.real (qmap ⁻¹' S) = 0 := by
    apply Complex.ofReal_injective
    simpa only [f, integral_indicator_const (1 : ℂ) hpre,
      Complex.real_smul, mul_one, Complex.ofReal_zero] using he
  exact (measureReal_eq_zero_iff hfinite.ne).mp hreal

include hH hν hS hb hu in
/-- Paper: Proposition 12.2.2.2(2), p. 508. The lifted kernel is measurable for
completed product Haar measure.
Deviation: The local integrability hypothesis uses the product measure as in the proof. -/
theorem aemeasurable_diagonalIndentationLift :
    AEMeasurable (Ψ u) (μ.prod μ) := by
  let : IsClosed (H : Set G) := hH
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : ν.IsHaarMeasure := hν.1
  have hq := aemeasurable_diagonalIndentationLift_quotient_qmp H hH μ ν hν
  exact (continuous_diagonalIndentationWeight H hH hν hS hb).measurable.complex_ofReal.aemeasurable.mul
    (hu.aestronglyMeasurable.aemeasurable.comp_quasiMeasurePreserving (hq.prodMap hq))

variable (hdiag : ∀ᵐ q ∂ν, (q, q) ∈
    dSequenceRegularSet (ν.prod ν)
      (fun n ↦ (QuotientGroup.mk' H '' U n) ×ˢ (QuotientGroup.mk' H '' U n)) u)

/-- Translated averages of a measurable function are measurable in the center. -/
private theorem aemeasurable_dSequenceKernelSmoothening_diagonal_average
    {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
    (m : Measure A) [m.IsHaarMeasure] [SFinite m]
    (V : Set A) (g : A → ℂ) (hg : Measurable g) :
    Measurable (fun x : A ↦ dSequenceAverage m V g x) := by
  have hprod : StronglyMeasurable (fun p : A × A ↦ g (p.1 * p.2)) := by
    simpa only [Function.comp_def, Pi.mul_apply] using
      (hg.comp (measurable_fst.mul measurable_snd)).stronglyMeasurable
  have hint : Measurable (fun x : A ↦ ∫ y in V, g (x * y) ∂m) :=
    hprod.integral_prod_right'.measurable
  have havg (x : A) : dSequenceAverage m V g x =
      (m.real V)⁻¹ • ∫ y in V, g (x * y) ∂m := by
    rw [dSequenceAverage, setAverage_eq,
      show m.real (x • V) = m.real V by simp only [Measure.real, measure_smul]]
    congr 1
    exact (measurePreserving_smul x m).setIntegral_image_emb
      (measurableEmbedding_const_smul x) g V
  have hfun : (fun x : A ↦ dSequenceAverage m V g x) =
      (fun x : A ↦ (m.real V)⁻¹ • ∫ y in V, g (x * y) ∂m) := funext havg
  rw [hfun]
  simpa only [Pi.smul_def] using hint.const_smul (m.real V)⁻¹

include hH hν hS hu hdiag in
/-- Paper: Proposition 12.2.2.2(2), p. 508. The smoothened quotient diagonal is
measurable for the completed quotient Haar measure. -/
theorem aemeasurable_dSequenceKernelSmoothening_diagonal :
    AEMeasurable (fun q ↦ uSmooth (q, q)) ν := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : IsClosed (H : Set G) := hH
  let : ν.IsHaarMeasure := hν.1
  obtain ⟨g, hg, hug⟩ := hu.aestronglyMeasurable.aemeasurable
  have havg (n : ℕ) (p : Q × Q) :
      dSequenceAverage (ν.prod ν) (Ū n ×ˢ Ū n) u p =
        dSequenceAverage (ν.prod ν) (Ū n ×ˢ Ū n) g p := by
    exact average_congr (ae_restrict_of_ae hug)
  have hm (n : ℕ) : Measurable (fun q : Q ↦
      dSequenceAverage (ν.prod ν) (Ū n ×ˢ Ū n) u (q, q)) := by
    have h := (aemeasurable_dSequenceKernelSmoothening_diagonal_average
      (ν.prod ν) (Ū n ×ˢ Ū n) g hg).comp (measurable_id.prodMk measurable_id)
    simpa only [havg, Function.comp_def, id_eq] using h
  refine aemeasurable_of_tendsto_metrizable_ae atTop (fun n ↦ (hm n).aemeasurable) ?_
  filter_upwards [hdiag] with q hq
  simpa only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero,
    dite_eq_left hq, dSequenceSmoothening] using (tendsto_nhds_limUnder hq)

include hH hν hS hu hdiag in
/-- Paper: Proposition 12.2.2.2(2), p. 508. The quotient points used on both skew
diagonals of the lift are regular for almost every group coordinate. -/
theorem ae_quotient_diagonal_mem_dSequenceRegularSet :
    ∀ᵐ x ∂μ, (π x, π x) ∈ dSequenceRegularSet (ν.prod ν) (fun n ↦ Ū n ×ˢ Ū n) u := by
  exact (aemeasurable_diagonalIndentationLift_quotient_qmp H hH μ ν hν).tendsto_ae.eventually hdiag

variable (hi : Integrable (fun q ↦
  dSequenceKernelSmoothening ν (fun n ↦ QuotientGroup.mk' H '' U n) u (q, q)) ν)

include hH hν hS hb hu hdiag hi in
/-- Paper: Proposition 12.2.2.2(2), p. 508. Translating the first diagonal coordinate
gives a function measurable for the completed product measure.
Deviation: The product measure follows the coordinate order `(x, h)`. -/
theorem aemeasurable_diagonalIndentationLift_left :
    AEMeasurable (fun p : G × H ↦ Ψ uSmooth ((p.2 : G)⁻¹ * p.1, p.1)) (μ.prod countH) :=
  by
  let : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hq := aemeasurable_diagonalIndentationLift_quotient_qmp H hH μ ν hν
  have hd := hi.aestronglyMeasurable.aemeasurable.comp_quasiMeasurePreserving hq
  have hpull := hd.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := countH))
  have hw : Continuous (fun p : G × H ↦
      diagonalIndentationWeight H countH b ((p.2 : G)⁻¹ * p.1, p.1)) :=
    (continuous_diagonalIndentationWeight H hH hν hS hb).comp
      (((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst).prodMk continuous_fst)
  have hm := hw.measurable.complex_ofReal.aemeasurable.mul hpull
  convert hm using 1
  funext p
  have h1 : π (p.2 : G) = 1 := (QuotientGroup.eq_one_iff _).mpr p.2.property
  have hπ : π ((p.2 : G)⁻¹ * p.1) = π p.1 := by
    rw [map_mul, map_inv, h1, inv_one, one_mul]
  simp only [diagonalIndentationLift, Prod.map_apply, hπ, Function.comp_def, Pi.mul_apply]

include hH hν hS hb hu hdiag hi in
/-- Paper: Proposition 12.2.2.2(2), p. 508. Translating the second diagonal coordinate
gives a function measurable for the completed product measure.
Deviation: The product measure follows the coordinate order `(x, h)`. -/
theorem aemeasurable_diagonalIndentationLift_right :
    AEMeasurable (fun p : G × H ↦ Ψ uSmooth (p.1, (p.2 : G)⁻¹ * p.1)) (μ.prod countH) :=
  by
  have hweight (x y : G) :
      diagonalIndentationWeight H countH b (x, y) = diagonalIndentationWeight H countH b (y, x) :=
    integral_congr_ae (ae_of_all _ fun k ↦ mul_comm _ _)
  have hswap (h : H) (x : G) :
      Ψ uSmooth ((h : G)⁻¹ * x, x) = Ψ uSmooth (x, (h : G)⁻¹ * x) := by
    have h1 : π (h : G) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
    have hπ : π ((h : G)⁻¹ * x) = π x := by rw [map_mul, map_inv, h1, inv_one, one_mul]
    simp only [diagonalIndentationLift, Prod.map_apply, hπ, hweight ((h : G)⁻¹ * x) x]
  simpa only [hswap] using
    aemeasurable_diagonalIndentationLift_left H hH hν hS hb hu hdiag hi

include hH hν hS hb hu hdiag hi in
/-- Paper: (12.2.2.3), p. 508. The first skew-diagonal evaluation is absolutely
integrable on the fundamental domain times the subgroup. -/
theorem integrable_diagonalIndentationLift_left :
    Integrable (fun p : G × H ↦ Ψ uSmooth ((p.2 : G)⁻¹ * p.1, p.1))
      ((μ.restrict D).prod countH) := by sorry

include hH hν hS hb hu hdiag hi in
/-- Paper: Proposition 12.2.2.2(2), p. 508. The second skew-diagonal evaluation is
absolutely integrable on the fundamental domain times the subgroup. -/
theorem integrable_diagonalIndentationLift_right :
    Integrable (fun p : G × H ↦ Ψ uSmooth (p.1, (p.2 : G)⁻¹ * p.1))
      ((μ.restrict D).prod countH) := by
  have hweight (x y : G) :
      diagonalIndentationWeight H countH b (x, y) = diagonalIndentationWeight H countH b (y, x) :=
    integral_congr_ae (ae_of_all _ fun k ↦ mul_comm _ _)
  have hswap (h : H) (x : G) :
      Ψ uSmooth ((h : G)⁻¹ * x, x) = Ψ uSmooth (x, (h : G)⁻¹ * x) := by
    have h1 : π (h : G) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
    have hπ : π ((h : G)⁻¹ * x) = π x := by rw [map_mul, map_inv, h1, inv_one, one_mul]
    simp only [diagonalIndentationLift, Prod.map_apply, hπ, hweight ((h : G)⁻¹ * x) x]
  simpa only [hswap] using
    integrable_diagonalIndentationLift_left H hH hν hS hb hu hdiag hi

include hH hν hS hb hu hdiag hi in
/-- Paper: Proposition 12.2.2.2(2), p. 508. The integral of the smoothened quotient diagonal
equals the integral of the first skew diagonal, integrating subgroup translates first. -/
theorem integral_diagonalIndentationLift_left :
    (∫ q, uSmooth (q, q) ∂ν) =
      ∫ x in D, ∫ h : H, Ψ uSmooth ((h : G)⁻¹ * x, x) ∂countH ∂μ := by sorry

include hH hν hS hb hu hdiag hi in
/-- Paper: (12.2.2.5), p. 508. The first skew-diagonal integral is unchanged by
exchanging the order of integration. -/
theorem integral_diagonalIndentationLift_left_swap :
    (∫ x in D, ∫ h : H, Ψ uSmooth ((h : G)⁻¹ * x, x) ∂countH ∂μ) =
      ∫ h : H, ∫ x in D, Ψ uSmooth ((h : G)⁻¹ * x, x) ∂μ ∂countH := by
  let : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  exact (integral_integral_swap (integrable_diagonalIndentationLift_left H hH hν hS hb hu hdiag hi))

include hH hν hS hb hu hdiag hi in
/-- Paper: (12.2.2.6), p. 508. Translating the second coordinate gives the same
integral as translating the first. -/
theorem integral_diagonalIndentationLift_swap_coordinates :
    (∫ h : H, ∫ x in D, Ψ uSmooth ((h : G)⁻¹ * x, x) ∂μ ∂countH) =
      ∫ h : H, ∫ x in D, Ψ uSmooth (x, (h : G)⁻¹ * x) ∂μ ∂countH := by
  have hweight (x y : G) :
      diagonalIndentationWeight H countH b (x, y) = diagonalIndentationWeight H countH b (y, x) :=
    integral_congr_ae (ae_of_all _ fun k ↦ mul_comm _ _)
  have hswap (h : H) (x : G) :
      Ψ uSmooth ((h : G)⁻¹ * x, x) = Ψ uSmooth (x, (h : G)⁻¹ * x) := by
    have h1 : π (h : G) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
    have hπ : π ((h : G)⁻¹ * x) = π x := by rw [map_mul, map_inv, h1, inv_one, one_mul]
    simp only [diagonalIndentationLift, Prod.map_apply, hπ, hweight ((h : G)⁻¹ * x) x]
  simp only [hswap]

include hH hν hS hb hu hdiag hi in
/-- Paper: (12.2.2.7), p. 508. The second skew-diagonal integral is unchanged by
exchanging the order of integration. -/
theorem integral_diagonalIndentationLift_right_swap :
    (∫ h : H, ∫ x in D, Ψ uSmooth (x, (h : G)⁻¹ * x) ∂μ ∂countH) =
      ∫ x in D, ∫ h : H, Ψ uSmooth (x, (h : G)⁻¹ * x) ∂countH ∂μ := by
  let : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  exact (integral_integral_swap (integrable_diagonalIndentationLift_right H hH hν hS hb hu hdiag hi)).symm

include hH hν hS hb hu in
/-- Paper: Proposition 12.2.2.2(3), p. 508. Multiplication by a compactly supported
continuous quotient function commutes almost everywhere with the kernel lift after
pullback of the multiplier. -/
theorem diagonalIndentationLift_mul (ρ : C_c(Q × Q, ℂ)) :
    Ψ (fun p ↦ ρ p * u p) =ᵐ[μ.prod μ] fun p ↦ ρ (q₂ p) * Ψ u p := by
  apply ae_of_all
  intro p
  exact mul_left_comm _ _ _

-- TODO(paper-gap): The continuous multiplier step on p. 511 applies Corollary
-- A.5.4.3 at every regular point. The printed equivalence fails (ERRATA R8).
include hH hν hS hb hu in
/-- Paper: Proposition 12.2.2.2(4), p. 509. On product-Haar-almost every pair,
the averages of the lifted kernel converge to the lift of the quotient smoothening. -/
theorem ae_tendsto_diagonalIndentationLift_average :
    ∀ᵐ p ∂μ.prod μ, Tendsto (fun n ↦
      dSequenceAverage (μ.prod μ) (U n ×ˢ U n) (Ψ u) p) atTop (𝓝 (Ψ uSmooth p)) := by sorry

include hH hν hS hb hu in
/-- Paper: Proposition 12.2.2.2(4), p. 509. Regularity of a pair for the lifted kernel
agrees with regularity of its quotient pair for product-Haar-almost every pair.
Deviation: Product-almost-everywhere equivalence replaces the printed every-pair claim. -/
theorem ae_diagonalIndentationLift_regular_iff :
    ∀ᵐ p ∂μ.prod μ,
      p ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ U n ×ˢ U n) (Ψ u) ↔
        q₂ p ∈ dSequenceRegularSet (ν.prod ν) (fun n ↦ Ū n ×ˢ Ū n) u := by sorry

-- Remark 12.2.2.3, p. 509. Mathlib's AEMeasurable.nullMeasurable and
-- NullMeasurable.aemeasurable identify measurability on the completed source
-- with almost-everywhere measurability on the Borel source for complex functions.

/-- Paper: (12.2.2.26), p. 512. The tail kernel restricts the lifted smoothened
kernel to second coordinates outside the indicated subgroup. -/
def diagonalIndentationTail (μH : Measure H) (b : G → ℝ) (v : Q × Q → ℂ)
    (K : Subgroup G) (p : G × G) : ℂ :=
  ((K : Set G)ᶜ).indicator (fun y ↦ diagonalIndentationLift H μH b v (p.1, y)) p.2

/-- Paper: (12.2.2.26), p. 512. Outside the indicated subgroup in the second
coordinate, the tail kernel equals the lifted kernel. -/
theorem diagonalIndentationTail_of_notMem (μH : Measure H) (b : G → ℝ) (v : Q × Q → ℂ)
    {K : Subgroup G} {x y : G} (hy : y ∉ K) :
    diagonalIndentationTail H μH b v K (x, y) =
      diagonalIndentationLift H μH b v (x, y) := by
  simp [diagonalIndentationTail, hy]

-- TODO(paper-gap): The closing citation on p. 513 refers to the tail definition
-- (12.2.2.26); the convergence claim is (12.2.2.27).
-- TODO(paper-gap): In (12.2.2.31), u₁ is only defined on G₀, but the inner integral
-- evaluates u₁(h⁻¹ x) for arbitrary x in G. It needs a fibre representative in G₀.
include hH hν hS hu hdiag hi in
/-- Paper: Proposition 12.2.2.4, p. 512. For an exhaustive filtration by open
subgroups with cyclic infinite successive quotients and a common fundamental domain in
the first stage, there is a compatible indentation whose integrated skew-diagonal tails
tend to zero. On each stage the indicator times the indentation is its restriction.
Deviation: The absolute integrability of each tail is explicit, as in the proof. -/
theorem exists_indentation_tendsto_tail (K : ℕ → Subgroup G)
    (hKopen : ∀ n, IsOpen (K n : Set G)) (hKmono : Monotone K)
    (hKexhaust : (⋃ n, (K n : Set G)) = univ) (hD₀ : D ⊆ (K 0 : Set G))
    (hDk : ∀ n, IsIndentationFundamentalDomain (H.comap (K n).subtype)
      (μ.comap (Subtype.val : K n → G)) ((Subtype.val : K n → G) ⁻¹' D))
    (hKrank : ∀ n, Nonempty
      ((K (n + 1) ⧸ (K n).comap (K (n + 1)).subtype) ≃* Multiplicative ℤ)) :
    ∃ c : G → ℝ, IsIndentation H countH c ∧
      (∀ n, IsIndentation (H.comap (K n).subtype) Measure.count (fun x : K n ↦ c x)) ∧
      (∀ n, Integrable (fun p : G × H ↦
        diagonalIndentationTail H countH c uSmooth (K n) (p.1, (p.2 : G)⁻¹ * p.1))
          ((μ.restrict D).prod countH)) ∧
      Tendsto (fun n ↦ ∫ x in D, ∫ h : H,
        diagonalIndentationTail H countH c uSmooth (K n) (x, (h : G)⁻¹ * x) ∂countH ∂μ)
          atTop (𝓝 0) := by sorry

end Diagonal

end RiemannMasullo
