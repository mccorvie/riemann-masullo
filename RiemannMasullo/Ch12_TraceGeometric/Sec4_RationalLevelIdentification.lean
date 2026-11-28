module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalLevelPolarMellin
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_LevelPolarComplement
import Mathlib.Topology.Algebra.IsOpenUnits
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space

/-!
# Main's polar-free level for the rationals with no finite place

For `ℚ` with no finite place, at twist `1/2` and Sobolev order zero, `main`'s polar-free level
`sLocalInvariantPWSobolev` is the image of the level of the unweighted even Paley–Wiener band of
`Sec4_RealPWLevelTrace` under an explicit isometry. So the level traces computed in that model are
traces on `main`'s level.

* The S-idele quotient. The norm carries `main`'s quotient Tamagawa measure to `dt / t` on the
  positive reals (`ratQuotNorm_map`). This rests on `levelIdent_fundamentalDomain_map`, a copy of a
  private lemma of `Sec4`, and on `ratMul_map`.
* Theta. The S-units are `±1` (`ratSUnit_cases`), so `main`'s S-local theta function is
  `f(g) + f(-g)` (`ratTheta_apply`). The norm-one classes are trivial (`ratNormOne_eq_one`), so the
  homogeneous theta function is `volume₁ (f(g) + f(-g))` (`ratHomogeneousTheta_apply`), and
  `volume₁ > 0` (`ratNormOneMass_pos`).
* Tests. The Schwartz–Bruhat tests on the S-adeles are the Schwartz functions of the real
  coordinate (`ratSchwartzBruhat_iff`, through `levelIdent_mem_schwartzBruhatSubmodule_euclidean_iff`,
  a copy of a private lemma of `Ch02_AdelicTheta/Sec2b`), and the S-adelic Fourier transform is
  Mathlib's `𝓕` there (`ratSAdeleSchwartzFourier_apply`). So `main`'s band tests are the Schwartz
  functions whose Fourier transform vanishes outside `[-Y, Y]` (`ratBandTest_spec`, `ratCore_test`).
* The isometry. `ratLevelMap` sends a band vector `v` to `N ^ (1/2) · 2 · v(N)` on the quotient,
  with `‖ratLevelMap v‖ ^ 2 = 2 ‖v‖ ^ 2` (`norm_sq_ratLevelMap`), and `ratLevelIsometry` is its
  normalization. The weighted theta vector of a test is `volume₁` times the image of the band vector
  of the even part of its Schwartz function (`ratFullTheta_eq_smul`).
* The level. `main`'s level is the image of the model level, the band vectors that vanish at the
  origin (`ratLevel_eq_map`).
* Traces. Conjugating a nuclear endomorphism by a linear isometry keeps its trace
  (`hilbertTrace_conjNuclear`, from `nuclearTrace_factor_comps`). So the operators of
  `Sec4_RationalLevelPolarMellin`, conjugated by `ratLevelIsometry`, take values in `main`'s level.
  Their traces less the summed sharp masses tend to minus the polar term, and with the two polar
  Mellin values subtracted as on p. 520 they tend to `∫ ψ(h) max (h ^ (1/2), h ^ (-1/2)) dh`
  (`ratMainLevel_trace_tendsto`). That limit is not zero for a nonnegative test
  (`ratMainLevel_trace_not_tendsto_polarMellin`), and for a test supported on norms at least one it
  is `M(f)(|·|^(1/2))` (`ratMainLevel_limit_eq_of_one_le`).

Not covered: other twists and Sobolev orders, finite places, and the passage from these S-idelic
Mellin values to the global ones (`ERRATA.md`, M25). The operators on `main`'s level are the model's
cutoff operators transported by the isometry, not an operator printed in the paper.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set NumberField IsDedekindDomain
open scoped Topology NumberField ENNReal NNReal InnerProductSpace FourierTransform SchwartzMap

namespace RiemannMasullo.Isolated

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

section QuotientMeasure

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "Hₛ" => sProjectedDiagonal F S
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S

open scoped Pointwise

attribute [-instance] Quotient.instMeasurableSpace

/-- Paper: (12.4.1.23), p. 518. The image in the S-idele quotient of multiplicative Tamagawa
measure restricted to an S-unit fundamental domain is the quotient Tamagawa measure. The same
statement as the private `sLocalTrace_fundamentalDomain_map` of `Sec4`, repeated so that `Sec4`
does not change. -/
theorem levelIdent_fundamentalDomain_map (D : Set Iₛ)
    (hD : IsFundamentalDomain Hₛ D μₛ) :
    ((μₛ).restrict D).map (QuotientGroup.mk : Iₛ → Jₛ) = μJ := by
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  have : BorelSpace Jₛ := ⟨rfl⟩
  have : (μₛ).IsHaarMeasure := sMultiplicativeTamagawaMeasure_isHaarMeasure
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Iₛ := (sIdeleGroup_description F S).1.secondCountableTopology
  let : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  have : DiscreteTopology Hₛ := discreteTopology_sProjectedDiagonal
  have hcl : IsClosed (Hₛ : Set Iₛ) := isClosed_sProjectedDiagonal
  have : Countable Hₛ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let π : Iₛ → Jₛ := QuotientGroup.mk
  have hπ : Measurable π := Continuous.measurable (f := π) continuous_quotient_mk'
  let νD := ((μₛ).restrict D).map π
  -- The fundamental domain for the right action of the S-units.
  have hDop : IsFundamentalDomain (Subgroup.op (Hₛ)) D μₛ := by
    have h := hD.image_of_equiv (Equiv.refl Iₛ) (MeasureTheory.QuasiMeasurePreserving.id μₛ)
      (Subgroup.equivOp (Hₛ)).symm (fun g x ↦ ?_)
    · simpa using h
    · change ((g.1.unop : Iₛ)) * x = x * g.1.unop
      exact mul_comm _ _
  have : IsClosed (Hₛ : Set Iₛ) := hcl
  have : T2Space Iₛ := (sIdeleGroup_description F S).2.1
  have : T2Space Jₛ := inferInstance
  have : SecondCountableTopology Jₛ := inferInstance
  have : LocallyCompactSpace Jₛ := inferInstance
  -- Preimages of sets in the quotient are invariant under the S-units.
  have hinv (A : Set Jₛ) (g : Hₛ) : (fun x ↦ g • x) ⁻¹' (π ⁻¹' A) = π ⁻¹' A := by
    ext z
    change π ((g : Iₛ) * z) ∈ A ↔ π z ∈ A
    rw [show π ((g : Iₛ) * z) = π z from QuotientGroup.eq.mpr (by
      rw [mul_inv_rev, mul_assoc, mul_left_comm, inv_mul_cancel, mul_one]
      exact inv_mem g.2)]
  -- The image of a compact set has at most its mass.
  have hle (W : Set Iₛ) (hW : IsCompact W) : νD (π '' W) ≤ μₛ W := by
    have hm : MeasurableSet (π '' W) :=
      (IsCompact.image (f := π) hW continuous_quotient_mk').isClosed.measurableSet
    rw [Measure.map_apply hπ hm, Measure.restrict_apply (hπ hm),
      QuotientGroup.preimage_image_mk, iUnion_inter]
    refine (measure_iUnion_le _).trans (le_of_eq ?_)
    rw [hD.measure_eq_tsum W, ← (Equiv.inv Hₛ).tsum_eq]
    congr 1
    funext ξ
    congr 2
    ext y
    simp only [mem_preimage, Equiv.inv_apply, Set.mem_smul_set_iff_inv_smul_mem,
      Subgroup.coe_inv, Subgroup.smul_def, smul_eq_mul]
    rw [mul_comm]
  have hlocfin : IsLocallyFiniteMeasure νD := ⟨fun q ↦ by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨W, hWc, hWn⟩ := exists_compact_mem_nhds x
    exact ⟨π '' W, QuotientGroup.isOpenMap_coe.image_mem_nhds hWn,
      (hle W hWc).trans_lt hWc.measure_lt_top⟩⟩
  have hleft : νD.IsMulLeftInvariant := ⟨fun y ↦ by
    obtain ⟨x₁, rfl⟩ := QuotientGroup.mk_surjective y
    ext A hA
    have hA' : MeasurableSet ((fun z ↦ (QuotientGroup.mk x₁ : Jₛ) * z) ⁻¹' A) :=
      measurable_const_mul _ hA
    rw [Measure.map_apply (measurable_const_mul _) hA]
    simp only [νD, Measure.map_apply hπ hA', Measure.map_apply hπ hA,
      Measure.restrict_apply (hπ hA'), Measure.restrict_apply (hπ hA)]
    have hpre : π ⁻¹' ((fun z ↦ (QuotientGroup.mk x₁ : Jₛ) * z) ⁻¹' A) =
        (fun z ↦ x₁ * z) ⁻¹' (π ⁻¹' A) := rfl
    have hD1 : IsFundamentalDomain Hₛ (x₁ • D) μₛ := hD.smul_of_comm x₁
    rw [hpre]
    calc μₛ ((fun z ↦ x₁ * z) ⁻¹' (π ⁻¹' A) ∩ D)
        = μₛ ((fun z ↦ x₁ * z) ⁻¹' (π ⁻¹' A ∩ x₁ • D)) := by
          congr 1
          ext z
          simp only [mem_inter_iff, mem_preimage]
          rw [show x₁ * z = x₁ • z from rfl, smul_mem_smul_set_iff]
      _ = μₛ (π ⁻¹' A ∩ x₁ • D) := measure_preimage_mul μₛ x₁ _
      _ = μₛ (π ⁻¹' A ∩ D) := (hD.measure_set_eq hD1 (hπ hA) (hinv A)).symm⟩
  have hopen : νD.IsOpenPosMeasure := ⟨fun U hU hne h0 ↦ by
    rw [Measure.map_apply hπ hU.measurableSet, Measure.restrict_apply (hπ hU.measurableSet)] at h0
    have h1 := hD.measure_zero_of_invariant _ (fun g ↦ by
      rw [← Set.preimage_smul_inv]; exact hinv U g⁻¹) h0
    exact (hU.preimage continuous_quotient_mk').measure_ne_zero μₛ (hne.preimage
      QuotientGroup.mk_surjective) h1⟩
  have hhaar : νD.IsHaarMeasure := { }
  have hreg : νD.Regular := by
    obtain ⟨W, hWc, hWn⟩ := exists_compact_mem_nhds (1 : Iₛ)
    exact Measure.regular_of_isMulLeftInvariant (IsCompact.image (f := π) hWc continuous_quotient_mk')
      ⟨π 1, mem_interior_iff_mem_nhds.mpr (QuotientGroup.isOpenMap_coe.image_mem_nhds hWn)⟩
      ((hle W hWc).trans_lt hWc.measure_lt_top).ne
  have hweil : ∀ f : C(Iₛ, ℂ), HasCompactSupport f →
      (∫ x, f x ∂μₛ) = ∫ q, lcaCosetIntegral Hₛ Measure.count f q ∂νD := by
    intro f hf
    have : (Measure.count : Measure Hₛ).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
    have : (μₛ).IsMulRightInvariant := ⟨fun g ↦ by
      rw [show (fun x : Iₛ ↦ x * g) = fun x ↦ g * x from funext fun x ↦ mul_comm x g]
      exact map_mul_left_eq_self μₛ g⟩
    have : Countable (Subgroup.op (Hₛ)) := Countable.of_equiv _ (Subgroup.equivOp (Hₛ))
    -- Near any point only finitely many S-units move it into the support of f.
    have hfin (W : Set Iₛ) (hW : IsCompact W) :
        {γ : Hₛ | (γ : Iₛ) ∈ W⁻¹ * tsupport f}.Finite :=
      (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (hW.inv.mul hf)).finite_of_discrete
    have hzero (W : Set Iₛ) (y : Iₛ) (hy : y ∈ W) (γ : Hₛ)
        (hγ : γ ∉ {γ : Hₛ | (γ : Iₛ) ∈ W⁻¹ * tsupport f}) : f (y * γ) = 0 := by
      by_contra h
      refine hγ ⟨y⁻¹, inv_mem_inv.mpr hy, y * γ, subset_tsupport f h, ?_⟩
      simp
    have hsum (x : Iₛ) : (∑' γ : Hₛ, f (x * γ)) = ∑ γ ∈ (hfin {x} isCompact_singleton).toFinset,
        f (x * γ) :=
      tsum_eq_sum fun γ hγ ↦ hzero {x} x rfl γ (by simpa using hγ)
    have hcont : Continuous fun x : Iₛ ↦ ∑' γ : Hₛ, f (x * γ) := by
      refine continuous_iff_continuousAt.mpr fun x ↦ ?_
      obtain ⟨W, hWc, hWn⟩ := exists_compact_mem_nhds x
      have heq : (fun y : Iₛ ↦ ∑ γ ∈ (hfin W hWc).toFinset, f (y * γ)) =ᶠ[𝓝 x]
          fun y ↦ ∑' γ : Hₛ, f (y * γ) :=
        Filter.mem_of_superset hWn fun y hy ↦
          (tsum_eq_sum fun γ hγ ↦ hzero W y hy γ (by simpa using hγ)).symm
      exact ((continuous_finsetSum _ fun γ _ ↦
        f.continuous.comp (continuous_id.mul continuous_const)).continuousAt).congr heq
    have hint (x : Iₛ) : Integrable (fun γ : Hₛ ↦ f (x * γ)) Measure.count :=
      integrable_count_iff.mpr (summable_of_ne_finset_zero (s := (hfin {x} isCompact_singleton).toFinset)
        fun γ hγ ↦ by rw [hzero {x} x rfl γ (by simpa using hγ), norm_zero])
    have hcoset (x : Iₛ) : lcaCosetIntegral Hₛ Measure.count f (π x) = ∑' γ : Hₛ, f (x * γ) := by
      rw [lcaCosetIntegral_mk Hₛ Measure.count (f : Iₛ → ℂ) x (hint x), integral_countable (hint x)]
      simp [Measure.real]
    have haut : QuotientGroup.automorphize (Γ := Hₛ) (f : Iₛ → ℂ) =
        lcaCosetIntegral Hₛ Measure.count f := by
      funext q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [hcoset x]
      change ∑' γ : Subgroup.op (Hₛ), f (γ • x) = _
      rw [← (Subgroup.equivOp (Hₛ)).tsum_eq]
      rfl
    have hautc : Continuous (QuotientGroup.automorphize (Γ := Hₛ) (f : Iₛ → ℂ)) := by
      rw [haut]
      refine (isQuotientMap_quotient_mk' (s := QuotientGroup.leftRel (Hₛ))).continuous_iff.mpr ?_
      change Continuous fun x ↦ lcaCosetIntegral Hₛ Measure.count f (π x)
      simp_rw [hcoset]
      exact hcont
    rw [QuotientGroup.integral_eq_integral_automorphize hDop
      (f.continuous.integrable_of_hasCompactSupport hf) hautc.aestronglyMeasurable, haut]
  exact (sLocalQuotientTamagawaMeasure_existsUnique (F := F) (S := S)).unique
    ⟨hhaar, hreg, hweil⟩ sLocalQuotientTamagawaMeasure_isWeil

end QuotientMeasure

section SchwartzCriterion

open Function

/-- Euclidean coordinates identify the Schwartz–Bruhat functions with the classical Schwartz
functions. The same statement as the private `mem_schwartzBruhatSubmodule_euclidean_iff` of
`Ch02_AdelicTheta/Sec2b`, repeated so that that file does not change. -/
theorem levelIdent_mem_schwartzBruhatSubmodule_euclidean_iff
    {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    [LocallyCompactSpace A] {n : ℕ}
    (v : A ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin n))) (g : A → ℂ) :
    g ∈ schwartzBruhatSubmodule A ↔
      ∃ s : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, ∀ x, s (v x).toAdd = g x := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let P := ElementaryLieGroup n 0 0 PUnit
  let D := (Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit
  let : Unique D := uniqueOfSubsingleton 0
  let p : Multiplicative E ≃ₜ* Multiplicative P :=
    { toMulEquiv := (AddEquiv.prodUnique (M := E) (N := D)).symm.toMultiplicative
      continuous_toFun := (continuous_id.prodMk continuous_const :
        Continuous (fun x : E ↦ (x, (default : D))))
      continuous_invFun := (continuous_fst : Continuous (Prod.fst : E × D → E)) }
  let e : ElementaryLCAPresentation A :=
    { realDim := n, torusDim := 0, latticeRank := 0, finiteFactor := PUnit, equiv := v.trans p }
  have hA := (lca_elementary_iff (G := A)).mpr ⟨e⟩
  let i : (⊤ : Subgroup A) ≃ₜ* A :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  let a : BruhatStructuralPair A := ⟨(⊤, OrderDual.toDual ⊥), by simp,
    isCompactlyGeneratedGroup_of_continuousMulEquiv i.symm hA.1,
    isBruhatGoodSubgroup_bot_iff.mpr hA.2, bot_le⟩
  let q₀ : A →* a.quotient := (QuotientGroup.mk' _).comp i.symm.toMulEquiv.toMonoidHom
  have hq₀ : IsOpenQuotientMap q₀ :=
    QuotientGroup.isOpenQuotientMap_mk.comp i.symm.toHomeomorph.isOpenQuotientMap
  have hinj : Injective q₀ := (MonoidHom.ker_eq_bot_iff q₀).mp (eq_bot_iff.mpr fun x hx ↦ by
    exact (a.quotient_mk_eq_one (i.symm x)).mp hx)
  let q := (MulEquiv.ofBijective q₀ ⟨hinj, hq₀.surjective⟩).toContinuousMulEquiv
    (fun _ ↦ hq₀.isQuotientMap.isOpen_preimage)
  let e₀ : ElementaryLCAPresentation a.quotient := { e with equiv := q.symm.trans e.equiv }
  have hreal (s : SchwartzBruhatStage e₀) (x : A) :
      schwartzBruhatStageRealization a e₀ s x = s ((v x).toAdd, 0, 0, PUnit.unit) := by
    have hx : x ∈ a.val.1 := Subgroup.mem_top x
    rw [schwartzBruhatStageRealization_apply, dite_eq_left hx]
    change s ((e₀.equiv (q x)).toAdd) = _
    change s ((e.equiv (q.symm (q x))).toAdd) = _
    rw [q.symm_apply_apply]
    rfl
  have hrange : schwartzBruhatSubmodule A = (schwartzBruhatStageRealization a e₀).range := by
    refine le_antisymm (iSup_le fun b ↦ iSup_le fun eb ↦ ?_) ?_
    · rintro _ ⟨sb, rfl⟩
      obtain ⟨j, hj, _⟩ := schwartzBruhatStage_transition (show b ≤ a from ⟨le_top, le_top⟩) eb e₀
      exact ⟨j sb, hj sb⟩
    · exact le_iSup_of_le a (le_iSup (fun e ↦ (schwartzBruhatStageRealization a e).range) e₀)
  rw [hrange, LinearMap.mem_range]
  constructor
  · rintro ⟨s, hs⟩
    let f : E → ℂ := fun x ↦ s (x, 0, 0, PUnit.unit)
    have hs' (y : P) : f y.1 = s y :=
      congrArg (fun z : P ↦ s z) (Prod.ext rfl (Subsingleton.elim _ _))
    have hf : (fun y : P ↦ f y.1) ∈ elementarySchwartzSubmodule n 0 0 PUnit :=
      (funext hs').symm ▸ s.property
    obtain ⟨S, hS⟩ := (elementarySchwartzSubmodule_real_iff f).mp hf
    refine ⟨S, fun x ↦ ?_⟩
    exact (congrFun hS (v x).toAdd).trans
      ((hreal s x).symm.trans (congrFun hs x))
  · rintro ⟨s, hs⟩
    let t : SchwartzBruhatStage e₀ :=
      ⟨fun y : P ↦ s y.1, (elementarySchwartzSubmodule_real_iff _).mpr ⟨s, rfl⟩⟩
    exact ⟨t, funext fun x ↦ (hreal t x).trans (hs x)⟩

end SchwartzCriterion

section Transport

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The adjoint of a linear isometry is a left inverse of it. -/
theorem linearIsometry_adjoint_apply (W : E →ₗᵢ[ℂ] F) (x : E) :
    ContinuousLinearMap.adjoint W.toContinuousLinearMap (W x) = x := by
  refine ext_inner_right ℂ fun y ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact W.inner_map_map x y

/-- Conjugating a nuclear series by a continuous linear map on each side gives a nuclear
series. -/
theorem isNuclearOperator_conj {T : E →L[ℂ] E} (hT : IsNuclearOperator T) (R : E →L[ℂ] F)
    (S : F →L[ℂ] E) : IsNuclearOperator (R.comp (T.comp S)) := by
  obtain ⟨c, φ, y, hc, hφ, hy, hsum⟩ := (isNuclearOperator_iff_isBanachNuclear T).mp hT
  refine (isNuclearOperator_iff_isBanachNuclear _).mpr ⟨c, fun n ↦ (φ n).comp S, fun n ↦ R (y n),
    hc, ?_, ?_, fun x ↦ ?_⟩
  · have h := (((ContinuousLinearMap.compL ℂ F E ℂ).flip S).continuous.tendsto 0).comp hφ
    rw [map_zero] at h
    exact h.congr fun n ↦ rfl
  · have h := (R.continuous.tendsto 0).comp hy
    rw [map_zero] at h
    exact h
  · simpa only [ContinuousLinearMap.comp_apply, map_smul] using R.hasSum (hsum (S x))

/-- Precomposing a nuclear series with a continuous linear map gives a nuclear series. -/
theorem isNuclearOperator_comp_right {T : E →L[ℂ] E} (hT : IsNuclearOperator T)
    (S : F →L[ℂ] E) : IsNuclearOperator (T.comp S) := by
  obtain ⟨c, φ, y, hc, hφ, hy, hsum⟩ := (isNuclearOperator_iff_isBanachNuclear T).mp hT
  refine (isNuclearOperator_iff_isBanachNuclear _).mpr ⟨c, fun n ↦ (φ n).comp S, y,
    hc, ?_, hy, fun x ↦ hsum (S x)⟩
  have h := (((ContinuousLinearMap.compL ℂ F E ℂ).flip S).continuous.tendsto 0).comp hφ
  rw [map_zero] at h
  exact h.congr fun n ↦ rfl

/-- The conjugate `W T W†` of a nuclear endomorphism by a linear isometry. -/
def conjNuclear (W : E →ₗᵢ[ℂ] F) (T : nuclearEndomorphisms E) : nuclearEndomorphisms F :=
  ⟨W.toContinuousLinearMap.comp (T.val.comp (ContinuousLinearMap.adjoint W.toContinuousLinearMap)),
    isNuclearOperator_conj T.property _ _⟩

theorem conjNuclear_apply (W : E →ₗᵢ[ℂ] F) (T : nuclearEndomorphisms E) (x : F) :
    (conjNuclear W T).val x = W (T.val (ContinuousLinearMap.adjoint W.toContinuousLinearMap x)) :=
  rfl

/-- Reconstruction: conjugating a nuclear endomorphism by a linear isometry keeps its trace. -/
theorem hilbertTrace_conjNuclear (W : E →ₗᵢ[ℂ] F) (T : nuclearEndomorphisms E) :
    hilbertTrace (conjNuclear W T) = hilbertTrace T := by
  let Wc := W.toContinuousLinearMap
  have hA₀ := isNuclearOperator_comp_right T.property (ContinuousLinearMap.adjoint Wc)
  have h := nuclearTrace_factor_comps (hilbert_approximationProperty (H := E))
    (hilbert_approximationProperty (H := F)) Wc W.injective _ hA₀
  have e : (T.val.comp (ContinuousLinearMap.adjoint Wc)).comp Wc = T.val := by
    ext x
    change T.val (ContinuousLinearMap.adjoint W.toContinuousLinearMap (W x)) = T.val x
    rw [linearIsometry_adjoint_apply]
  have hc : ∀ (A B : E →L[ℂ] E) (_ : A = B) (hA : IsNuclearOperator A) (hB : IsNuclearOperator B),
      nuclearTrace (hilbert_approximationProperty (H := E)) A hA =
        nuclearTrace (hilbert_approximationProperty (H := E)) B hB := by
    rintro A B rfl hA hB
    rfl
  rw [hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
  exact h.symm.trans (hc _ _ e _ _)

end Transport

section RatQuotient

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b instMeasurableSpaceInfiniteAdeleRing_riemannMasullo
  instRatSIdeleT2 instRatSAdeleT2

attribute [-instance] Quotient.instMeasurableSpace

local notation "Sq" => (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
local notation "Iq" => (SAdeleRing ℚ Sq)ˣ
local notation "Jq" => SIdeleQuotient ℚ Sq
local notation "eq" => ratRealCoordEquiv
local notation "μq" => sMultiplicativeTamagawaMeasure ℚ Sq
local notation "μJq" => sLocalQuotientTamagawaMeasure ℚ Sq

/-- The S-ideles of `ℚ` with positive real coordinate form a measurable set. -/
theorem measurableSet_ratPos : MeasurableSet {x : Iq | 0 < eq x.val} := by
  have : BorelSpace (SAdeleRing ℚ Sq) := sAdeleRing_borelSpace
  have : BorelSpace Iq := sIdeleGroup_borelSpace
  exact measurableSet_lt measurable_const
    (measurable_ratRealCoordEquiv.comp Units.continuous_val.measurable)

/-- Reconstruction: for `ℚ` with no finite place, an integral over the S-idele quotient against
`main`'s quotient Tamagawa measure is the integral over the positive reals of the class of `t`
against `dt / t`. -/
theorem ratQuotient_integral (G : Jq → ℂ) (hG : AEStronglyMeasurable G μJq) :
    ∫ c, G c ∂μJq = ∫ t in Ioi 0, G (QuotientGroup.mk (ratUnit t)) / (t : ℂ) := by
  have : BorelSpace Iq := sIdeleGroup_borelSpace
  have : BorelSpace Jq := ⟨rfl⟩
  have hπ : Measurable (QuotientGroup.mk : Iq → Jq) :=
    Continuous.measurable (f := (QuotientGroup.mk : Iq → Jq)) continuous_quotient_mk'
  rw [← levelIdent_fundamentalDomain_map _ isFundamentalDomain_ratPos] at hG ⊢
  rw [integral_map hπ.aemeasurable hG, ← integral_indicator measurableSet_ratPos,
    ratIntegral_mul, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ))]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
    have hmem : ratUnit t ∈ {x : Iq | 0 < eq x.val} := by
      change 0 < eq (ratUnit t).val
      rwa [ratUnit_val ht.ne', RingEquiv.apply_symm_apply]
    rw [ratLift_of_ne ht.ne', indicator_of_mem hmem, abs_of_pos ht]
  · intro t ht
    rcases eq_or_ne t 0 with rfl | h0
    · simp [ratLift_zero]
    · have hnot : ratUnit t ∉ {x : Iq | 0 < eq x.val} := by
        change ¬ 0 < eq (ratUnit t).val
        rw [ratUnit_val h0, RingEquiv.apply_symm_apply]
        exact ht
      rw [ratLift_of_ne h0, indicator_of_notMem hnot, zero_div]

/-- The S-units of `ℚ` with no finite place. -/
local notation "Uq" => ((Sq : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)ˣ
local notation "Bq" => SchwartzBruhat (Multiplicative (SAdeleRing ℚ Sq))
local notation "volume₁" => ((sLocalNormOneQuotientMeasure ℚ Sq) univ).toReal

/-- An S-unit of `ℚ` with no finite place is `1` or `-1`. -/
theorem ratSUnit_cases (u : Uq) : u = 1 ∨ u = -1 := by
  rcases integer_empty_unit u with h | h
  · exact Or.inl (Units.ext (Subtype.ext (by simpa using h)))
  · exact Or.inr (Units.ext (Subtype.ext (by simpa using h)))

/-- The S-unit `-1` of `ℚ` is not `1`. -/
theorem ratSUnit_neg_one_ne_one : (-1 : Uq) ≠ 1 := by
  intro h
  have h' := congrArg (fun u : Uq ↦ (u.val.val : ℚ)) h
  norm_num at h'

/-- The two S-units of `ℚ` with no finite place. -/
def ratSUnitEquiv : Bool ≃ Uq where
  toFun b := if b then 1 else -1
  invFun u := decide (u = 1)
  left_inv b := by cases b <;> simp
  right_inv u := by
    rcases ratSUnit_cases u with rfl | rfl <;> simp

/-- The S-unit embedding sends `-1` to `-1`. -/
theorem ratSUnitEmbedding_neg_one : (sUnitEmbedding ℚ Sq (-1 : Uq) : SAdeleRing ℚ Sq) = -1 := by
  simp [sUnitEmbedding]

/-- Reconstruction: for `ℚ` with no finite place, `main`'s S-local theta function is the sum of
the values at `g` and `-g`. -/
theorem ratTheta_apply (f : Bq) (g : Iq) :
    sLocalAdelicTheta ℚ Sq f g =
      f (Multiplicative.ofAdd g.val) + f (Multiplicative.ofAdd (-g.val)) := by
  rw [sLocalAdelicTheta_apply]
  dsimp only
  rw [← ratSUnitEquiv.tsum_eq, tsum_fintype, Fintype.sum_bool]
  simp only [ratSUnitEquiv, Equiv.coe_fn_mk, ite_true, Bool.false_eq_true, ite_false, map_one,
    one_mul]
  rw [Units.val_mul, ratSUnitEmbedding_neg_one, neg_one_mul]

/-- For `ℚ` with no finite place, a class of norm one is trivial. -/
theorem ratNormOne_eq_one (c : (sIdeleQuotientNorm ℚ Sq).ker) : c = 1 := by
  obtain ⟨c, hc⟩ := c
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  have hn : sIdeleNorm ℚ Sq g = 1 := (sIdeleQuotientNorm_mk ℚ Sq g).symm.trans hc
  have habs : |eq g.val| = 1 := by
    have h := congrArg (fun t : ℝ≥0ˣ ↦ ((t : ℝ≥0) : ℝ)) hn
    simpa [ratNormq] using h
  have hmem : g ∈ sProjectedDiagonal ℚ Sq := by
    rw [mem_ratProjectedDiagonal_iff]
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 habs with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact Subtype.ext ((QuotientGroup.eq_one_iff g).2 hmem)

instance : Unique (sIdeleQuotientNorm ℚ Sq).ker where
  default := 1
  uniq c := ratNormOne_eq_one c

/-- Reconstruction: for `ℚ` with no finite place the norm-one classes are trivial, so `main`'s
homogeneous theta function, for any character `ω` of them, is `volume₁` times the sum of the values
at `g` and `-g`. -/
theorem ratHomogeneousTheta_apply (ω : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker) (f : Bq)
    (g : Iq) :
    sLocalHomogeneousAdelicThetaLinearMap ℚ Sq ω f (QuotientGroup.mk g) =
      (volume₁ : ℂ) * (f (Multiplicative.ofAdd g.val) + f (Multiplicative.ofAdd (-g.val))) := by
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply, integral_unique]
  have h1 : (default : (sIdeleQuotientNorm ℚ Sq).ker) = 1 := rfl
  simp only [h1, OneMemClass.coe_one, mul_one, map_one, Circle.coe_one]
  rw [sLocalAdelicThetaOnClasses_mk, ratTheta_apply, Complex.real_smul, measureReal_def]

/-- The real line as one-dimensional Euclidean space. -/
def ratEuclideanLine : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 1) ℝ).symm

/-- The real coordinate of the S-adeles of `ℚ` with no finite place, as an isomorphism of
topological groups onto one-dimensional Euclidean space. -/
def ratEuclideanCoord :
    Multiplicative (SAdeleRing ℚ Sq) ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin 1)) :=
  { toMulEquiv := (ratRealCoordEquiv.toAddEquiv.trans
      ratEuclideanLine.toLinearEquiv.toAddEquiv).toMultiplicative
    continuous_toFun := ratEuclideanLine.continuous.comp continuous_ratRealCoordEquiv
    continuous_invFun := continuous_ratRealCoordEquiv_symm.comp ratEuclideanLine.symm.continuous }

/-- The S-adeles of `ℚ` with no finite place are locally compact, as the real line is. -/
theorem ratSAdele_locallyCompact : LocallyCompactSpace (SAdeleRing ℚ Sq) :=
  (Homeomorph.mk ratRealCoordEquiv.toEquiv continuous_ratRealCoordEquiv
    continuous_ratRealCoordEquiv_symm).isClosedEmbedding.locallyCompactSpace

/-- Reconstruction: for `ℚ` with no finite place, the Schwartz–Bruhat functions on the
S-adeles are the Schwartz functions of the real coordinate. -/
theorem ratSchwartzBruhat_iff (g : Multiplicative (SAdeleRing ℚ Sq) → ℂ) :
    g ∈ schwartzBruhatSubmodule (Multiplicative (SAdeleRing ℚ Sq)) ↔
      ∃ s : 𝓢(ℝ, ℂ), ∀ x, s (eq x.toAdd) = g x := by
  have : LocallyCompactSpace (SAdeleRing ℚ Sq) := ratSAdele_locallyCompact
  have : LocallyCompactSpace (Multiplicative (SAdeleRing ℚ Sq)) := ‹LocallyCompactSpace _›
  have : T2Space (SAdeleRing ℚ Sq) := (Homeomorph.mk ratRealCoordEquiv.toEquiv
    continuous_ratRealCoordEquiv continuous_ratRealCoordEquiv_symm).isEmbedding.t2Space
  have : T2Space (Multiplicative (SAdeleRing ℚ Sq)) := ‹T2Space (SAdeleRing ℚ Sq)›
  rw [levelIdent_mem_schwartzBruhatSubmodule_euclidean_iff ratEuclideanCoord g]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ ratEuclideanLine s, fun x ↦ hs x⟩
  · rintro ⟨s, hs⟩
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ ratEuclideanLine.symm s, fun x ↦ ?_⟩
    change s (ratEuclideanLine.symm (ratEuclideanLine (eq x.toAdd))) = g x
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hs x

/-- Reconstruction: for `ℚ` with no finite place, the S-adelic Fourier transform of a test is
the Fourier transform of its Schwartz function in the real coordinate. -/
theorem ratSAdeleSchwartzFourier_apply (f : Bq) (s : 𝓢(ℝ, ℂ))
    (hs : ∀ x, s (eq x.toAdd) = f x) (y : SAdeleRing ℚ Sq) :
    sAdeleSchwartzFourier f (Multiplicative.ofAdd y) = 𝓕 s (eq y) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  change tamagawaFourier (sAdditiveTamagawaMeasure ℚ Sq) (sAdeleStandardCharacter ℚ Sq)
    (fun x ↦ f (Multiplicative.ofAdd x)) y = _
  rw [tamagawaFourier, ratIntegral_add]
  refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
  dsimp only
  have hst : s t = f (Multiplicative.ofAdd (ratRealCoordEquiv.symm t)) := by
    rw [← hs]
    simp
  rw [ratSAdeleStandardCharacter, map_mul ratRealCoordEquiv, RingEquiv.apply_symm_apply, hst,
    Circle.smul_def, mul_comm]
  congr 1
  rw [Real.fourierChar_apply, Circle.coe_exp, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Every S-adelic test of `ℚ` with no finite place is a Schwartz function of the real
coordinate. -/
theorem ratTest_schwartz (f : Bq) : ∃ s : 𝓢(ℝ, ℂ), ∀ x, s (eq x.toAdd) = f x :=
  (ratSchwartzBruhat_iff _).1 f.2

/-- Reconstruction: every test of `main`'s Paley–Wiener band of product radius `Y`, for `ℚ` with
no finite place, is a Schwartz function of the real coordinate whose Fourier transform vanishes
outside `[-Y, Y]`. -/
theorem ratBandTest_spec {Y : ℝ} (f : Bq)
    (hf : f ∈ sLocalPWTests (F := ℚ) (S := Sq) (T := Sq) le_rfl (sLocalPWProductRegion Sq Y)) :
    ∃ s : 𝓢(ℝ, ℂ), (∀ x, s (eq x.toAdd) = f x) ∧ ∀ ξ ∉ Icc (-Y) Y, 𝓕 s ξ = 0 := by
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hf
  clear hf
  rw [levelPolar_transition_self]
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨-, hts⟩ := hg
    obtain ⟨s, hs⟩ := ratTest_schwartz g
    refine ⟨s, hs, fun ξ hξ ↦ ?_⟩
    have hy : eq (ratRealCoordEquiv.symm ξ) = ξ := RingEquiv.apply_symm_apply _ _
    rw [← hy, ← ratSAdeleSchwartzFourier_apply g s hs]
    refine image_eq_zero_of_notMem_tsupport fun hmem ↦ hξ ?_
    have h := hts hmem
    simp only [Set.mem_preimage, toAdd_ofAdd, ratMem_band, hy] at h
    exact ⟨(abs_le.1 h).1, (abs_le.1 h).2⟩
  | zero => exact ⟨0, fun x ↦ by simp, fun ξ _ ↦ by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨sa, hsa, hfa⟩ := ha
    obtain ⟨sb, hsb, hfb⟩ := hb
    refine ⟨sa + sb, fun x ↦ ?_, fun ξ hξ ↦ ?_⟩
    · rw [add_apply, hsa, hsb]
      rfl
    · have h : 𝓕 (sa + sb) = 𝓕 sa + 𝓕 sb := (SchwartzMap.fourierTransformCLM ℂ).map_add sa sb
      rw [h, add_apply, hfa ξ hξ, hfb ξ hξ, add_zero]
  | smul c a _ ha =>
    obtain ⟨sa, hsa, hfa⟩ := ha
    refine ⟨c • sa, fun x ↦ ?_, fun ξ hξ ↦ ?_⟩
    · rw [smul_apply, hsa]
      rfl
    · have h : 𝓕 (c • sa) = c • 𝓕 sa := (SchwartzMap.fourierTransformCLM ℂ).map_smul c sa
      rw [h, smul_apply, hfa ξ hξ, smul_zero]

/-- Reconstruction: conversely, a Schwartz function of the real coordinate whose Fourier transform
vanishes outside `[-Y, Y]`, which vanishes at zero and has integral zero, is a polar-free test of
`main`'s Paley–Wiener band of product radius `Y`, for `ℚ` with no finite place. -/
theorem ratCore_test {Y : ℝ} (g : 𝓢(ℝ, ℂ)) (hb : ∀ ξ ∉ Icc (-Y) Y, 𝓕 g ξ = 0) (h0 : g 0 = 0)
    (hi : ∫ x, g x = 0) :
    ∃ f : Bq, (∀ x, f x = g (eq x.toAdd)) ∧
      f ∈ sLocalPWTests (F := ℚ) (S := Sq) (T := Sq) le_rfl (sLocalPWProductRegion Sq Y) ∧
      f ∈ sAdelePolarSubspace ℚ Sq := by
  let f : Bq := ⟨fun x ↦ g (eq x.toAdd), (ratSchwartzBruhat_iff _).2 ⟨g, fun _ ↦ rfl⟩⟩
  have hfs : ∀ x, g (eq x.toAdd) = f x := fun _ ↦ rfl
  have hF (y : SAdeleRing ℚ Sq) : sAdeleSchwartzFourier f (Multiplicative.ofAdd y) = 𝓕 g (eq y) :=
    ratSAdeleSchwartzFourier_apply f g hfs y
  let C : Set (Multiplicative (SAdeleRing ℚ Sq)) := {x | |eq x.toAdd| ≤ Y}
  have hCc : IsClosed C := isClosed_le (continuous_abs.comp
    (continuous_ratRealCoordEquiv.comp continuous_toAdd)) continuous_const
  have hCk : IsCompact C := by
    have h := (isCompact_Icc (a := -Y) (b := Y)).image
      (continuous_ofAdd.comp continuous_ratRealCoordEquiv_symm)
    convert h using 1
    ext x
    simp only [C, Set.mem_ofPred_eq, Set.mem_image, Set.mem_Icc, Function.comp_apply]
    constructor
    · intro hx
      exact ⟨eq x.toAdd, abs_le.1 hx, by simp⟩
    · rintro ⟨t, ht, rfl⟩
      simpa using abs_le.2 ht
  have hsupp : tsupport (sAdeleSchwartzFourier f).val ⊆ C := by
    refine closure_minimal (fun x hx ↦ ?_) hCc
    by_contra hxC
    apply hx
    change sAdeleSchwartzFourier f (Multiplicative.ofAdd x.toAdd) = 0
    rw [hF]
    refine hb _ fun h ↦ hxC ?_
    exact abs_le.2 h
  refine ⟨f, fun _ ↦ rfl, ?_, ?_⟩
  · refine Submodule.mem_map.2 ⟨f, Submodule.subset_span ⟨hCk.of_isClosed_subset
      (isClosed_tsupport _) hsupp, fun x hx ↦ ?_⟩, levelPolar_transition_self f⟩
    simp only [Set.mem_preimage, ratMem_band]
    exact hsupp hx
  · rw [mem_sAdelePolarSubspace]
    refine ⟨?_, ?_⟩
    · change g (eq 0) = 0
      rw [map_zero]
      exact h0
    · rw [sAdeleSchwartzFourier_apply_zero, ratIntegral_add]
      have hpt (t : ℝ) : f (Multiplicative.ofAdd (ratRealCoordEquiv.symm t)) = g t := by
        change g (eq (ratRealCoordEquiv.symm t)) = g t
        rw [RingEquiv.apply_symm_apply]
      simp only [hpt]
      exact hi

/-- The norm-one classes of `ℚ` with no finite place have positive mass. -/
theorem ratNormOneMass_pos : 0 < volume₁ := by
  have : BorelSpace (sIdeleQuotientNorm ℚ Sq).ker := ⟨rfl⟩
  have := (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := Sq)).1
  have : Finite (sIdeleQuotientNorm ℚ Sq).ker := Finite.of_subsingleton
  have : CompactSpace (sIdeleQuotientNorm ℚ Sq).ker := Finite.compactSpace
  exact ENNReal.toReal_pos (isOpen_univ.measure_pos _ ⟨1, trivial⟩).ne'
    isCompact_univ.measure_lt_top.ne

/-- Reconstruction: for `ℚ` with no finite place, the lower integral of a function of the real
coordinate against the multiplicative Tamagawa measure is its lower integral against
`dt / |t|`. -/
theorem ratLintegral_mul (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ g, G (eq g.val) ∂μq = ∫⁻ t, ENNReal.ofReal |t|⁻¹ * G t := by
  have : BorelSpace (SAdeleRing ℚ Sq) := sAdeleRing_borelSpace
  have : BorelSpace Iq := sIdeleGroup_borelSpace
  have ho : Topology.IsOpenEmbedding (Units.val : Iq → SAdeleRing ℚ Sq) :=
    IsOpenUnits.isOpenEmbedding_unitsVal
      (M := ((w : InfinitePlace ℚ) → w.Completion) × ((v : Sq) → v.val.adicCompletion ℚ))
  have hval := ho.measurableEmbedding
  have hR := hval.measurableSet_range
  have hmod : Continuous fun z : SAdeleRing ℚ Sq ↦ |eq z| :=
    continuous_abs.comp continuous_ratRealCoordEquiv
  let d : SAdeleRing ℚ Sq → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (1 / |eq z|)
  have hd : Measurable d := ENNReal.measurable_ofReal.comp (measurable_const.div hmod.measurable)
  have hGe : Measurable fun y : SAdeleRing ℚ Sq ↦ G (eq y) :=
    hG.comp measurable_ratRealCoordEquiv
  have hdens : (μq).map (Units.val : Iq → SAdeleRing ℚ Sq) =
      ((sAdditiveTamagawaMeasure ℚ Sq).restrict (range (Units.val : Iq → SAdeleRing ℚ Sq))).withDensity
        d := by
    rw [sLocalTrace_measure_density]
    congr 1
    funext z
    have hf : sLocalTraceMeasureFactor (F := ℚ) Sq = 1 := by simp [sLocalTraceMeasureFactor]
    rw [hf, ratModq]
  calc ∫⁻ g, G (eq g.val) ∂μq
      = ∫⁻ y, G (eq y) ∂((μq).map (Units.val : Iq → SAdeleRing ℚ Sq)) :=
        (hval.lintegral_map (fun y ↦ G (eq y))).symm
    _ = ∫⁻ y, d y * G (eq y) ∂((sAdditiveTamagawaMeasure ℚ Sq).restrict
          (range (Units.val : Iq → SAdeleRing ℚ Sq))) := by
        rw [hdens, lintegral_withDensity_eq_lintegral_mul _ hd hGe]
        rfl
    _ = ∫⁻ y, (range (Units.val : Iq → SAdeleRing ℚ Sq)).indicator
          (fun y ↦ d y * G (eq y)) y ∂(sAdditiveTamagawaMeasure ℚ Sq) :=
        (lintegral_indicator hR _).symm
    _ = ∫⁻ t, (range (Units.val : Iq → SAdeleRing ℚ Sq)).indicator
          (fun y ↦ d y * G (eq y)) (ratRealCoordEquiv.symm t) :=
        ((measurePreserving_ratRealCoord.symm ratRealMeasurableEquiv).lintegral_comp
          ((hd.mul hGe).indicator hR)).symm
    _ = ∫⁻ t, ENNReal.ofReal |t|⁻¹ * G t := by
        refine lintegral_congr fun t ↦ ?_
        rcases eq_or_ne t 0 with rfl | ht
        · have hnot : ratRealCoordEquiv.symm 0 ∉ range (Units.val : Iq → SAdeleRing ℚ Sq) := by
            rw [ratMem_range_units]
            simp
          rw [indicator_of_notMem hnot]
          simp
        · have hmem : ratRealCoordEquiv.symm t ∈ range (Units.val : Iq → SAdeleRing ℚ Sq) := by
            rw [ratMem_range_units, RingEquiv.apply_symm_apply]
            exact ht
          rw [indicator_of_mem hmem]
          simp only [d, RingEquiv.apply_symm_apply, one_div]

/-- Reconstruction: for `ℚ` with no finite place, the real coordinate carries the multiplicative
Tamagawa measure to `dt / |t|`. -/
theorem ratMul_map :
    (μq).map (fun g : Iq ↦ eq g.val) = volume.withDensity (fun t ↦ ENNReal.ofReal |t|⁻¹) := by
  have : BorelSpace (SAdeleRing ℚ Sq) := sAdeleRing_borelSpace
  have : BorelSpace Iq := sIdeleGroup_borelSpace
  have hm : Measurable fun g : Iq ↦ eq g.val :=
    measurable_ratRealCoordEquiv.comp Units.continuous_val.measurable
  ext A hA
  rw [Measure.map_apply hm hA, withDensity_apply _ hA, ← lintegral_indicator_one (hm hA),
    ← lintegral_indicator hA]
  have h := ratLintegral_mul (A.indicator 1) (measurable_one.indicator hA)
  calc _ = ∫⁻ g, A.indicator 1 (eq g.val) ∂μq := by
        refine lintegral_congr fun g ↦ ?_
        by_cases hg : eq g.val ∈ A
        · simp [hg]
        · simp [hg]
    _ = ∫⁻ t, ENNReal.ofReal |t|⁻¹ * A.indicator 1 t := h
    _ = _ := by
        refine lintegral_congr fun t ↦ ?_
        by_cases ht : t ∈ A
        · simp [ht]
        · simp [ht]

/-- The norm on the S-idele quotient of `ℚ` with no finite place, as a real number. -/
def ratQuotNorm (c : Jq) : ℝ := ((continuousSIdeleQuotientNorm ℚ Sq c).val : ℝ)

/-- The norm of the class of an S-idele is the absolute value of its real coordinate. -/
theorem ratQuotNorm_mk (g : Iq) : ratQuotNorm (QuotientGroup.mk g) = |eq g.val| := by
  change ((sIdeleQuotientNorm ℚ Sq (QuotientGroup.mk g)).val : ℝ) = _
  rw [sIdeleQuotientNorm_mk, ratNormq]

theorem ratQuotNorm_pos (c : Jq) : 0 < ratQuotNorm c := NNReal.coe_pos.mpr (Units.zero_lt _)

theorem continuous_ratQuotNorm : Continuous ratQuotNorm :=
  NNReal.continuous_coe.comp (Units.continuous_val.comp (continuousSIdeleQuotientNorm ℚ Sq).continuous)

/-- Reconstruction: for `ℚ` with no finite place, the norm carries `main`'s quotient Tamagawa
measure on the S-idele quotient to `dt / t` on the positive reals. -/
theorem ratQuotNorm_map :
    (μJq).map ratQuotNorm = (volume.restrict (Ioi 0)).withDensity (fun t ↦ ENNReal.ofReal t⁻¹) := by
  have : BorelSpace (SAdeleRing ℚ Sq) := sAdeleRing_borelSpace
  have : BorelSpace Iq := sIdeleGroup_borelSpace
  have : BorelSpace Jq := ⟨rfl⟩
  have hπ : Measurable (QuotientGroup.mk : Iq → Jq) :=
    Continuous.measurable (f := (QuotientGroup.mk : Iq → Jq)) continuous_quotient_mk'
  have hN : Measurable ratQuotNorm := continuous_ratQuotNorm.measurable
  have hm : Measurable fun g : Iq ↦ eq g.val :=
    measurable_ratRealCoordEquiv.comp Units.continuous_val.measurable
  rw [← levelIdent_fundamentalDomain_map _ isFundamentalDomain_ratPos, Measure.map_map hN hπ]
  have h1 : (ratQuotNorm ∘ (QuotientGroup.mk : Iq → Jq)) =ᵐ[(μq).restrict {x : Iq | 0 < eq x.val}]
      fun g ↦ eq g.val :=
    (ae_restrict_iff' measurableSet_ratPos).2 (ae_of_all _ fun g (hg : 0 < eq g.val) ↦ by
      change ratQuotNorm (QuotientGroup.mk g) = eq g.val
      rw [ratQuotNorm_mk, abs_of_pos hg])
  rw [Measure.map_congr h1,
    show {x : Iq | 0 < eq x.val} = (fun g : Iq ↦ eq g.val) ⁻¹' Ioi 0 from rfl,
    ← Measure.restrict_map hm measurableSet_Ioi, ratMul_map, restrict_withDensity measurableSet_Ioi]
  refine withDensity_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht ↦ ?_))
  simp only [abs_of_pos (show (0 : ℝ) < t from ht)]

/-- Reconstruction: a function of the norm on the S-idele quotient of `ℚ` with no finite place is
integrable for `main`'s quotient measure exactly when `t⁻¹ F t` is integrable on the positive
reals. -/
theorem ratQuotNorm_integrable_iff {F : ℝ → ℝ} (hF : Measurable F) :
    Integrable (fun c ↦ F (ratQuotNorm c)) μJq ↔ IntegrableOn (fun t ↦ t⁻¹ * F t) (Ioi 0) := by
  have : BorelSpace Jq := ⟨rfl⟩
  have hN : Measurable ratQuotNorm := continuous_ratQuotNorm.measurable
  have hd : Measurable fun t : ℝ ↦ ENNReal.ofReal t⁻¹ := ENNReal.measurable_ofReal.comp measurable_inv
  change Integrable (F ∘ ratQuotNorm) μJq ↔ _
  rw [← integrable_map_measure hF.aestronglyMeasurable hN.aemeasurable, ratQuotNorm_map,
    integrable_withDensity_iff_integrable_smul' hd (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integrable_congr ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht ↦ ?_))
  simp only [ENNReal.toReal_ofReal (inv_nonneg.2 (le_of_lt ht)), smul_eq_mul]

/-- Reconstruction: the integral of a function of the norm over the S-idele quotient of `ℚ` with
no finite place is the integral of `t⁻¹ F t` over the positive reals. -/
theorem ratQuotNorm_integral {F : ℝ → ℝ} (hF : Measurable F) :
    ∫ c, F (ratQuotNorm c) ∂μJq = ∫ t in Ioi 0, t⁻¹ * F t := by
  have : BorelSpace Jq := ⟨rfl⟩
  have hN : Measurable ratQuotNorm := continuous_ratQuotNorm.measurable
  have hd : Measurable fun t : ℝ ↦ ENNReal.ofReal t⁻¹ := ENNReal.measurable_ofReal.comp measurable_inv
  rw [← integral_map hN.aemeasurable hF.aestronglyMeasurable, ratQuotNorm_map,
    integral_withDensity_eq_integral_toReal_smul hd (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  rw [ENNReal.toReal_ofReal (inv_nonneg.2 (le_of_lt ht)), smul_eq_mul]

local notation "μ₀" => realPWIntervalMeasure 0 0
local notation "hμ₀" => volume_le_realPWIntervalMeasure 0 0 le_rfl
local notation "V₀(" Y ")" => RealPWBand.space Y hμ₀
local notation "ev(" Y ")" => RealPWBand.evaluation Y hμ₀

/-- An even integrable real function on the line has twice its integral over the positive
half-line. -/
theorem integral_eq_two_mul_integral_Ioi_of_even {f : ℝ → ℝ} (hf : Integrable f)
    (he : ∀ x, f (-x) = f x) : ∫ x, f x = 2 * ∫ x in Ioi 0, f x := by
  rw [← integral_add_compl measurableSet_Ioi hf, compl_Ioi, ← neg_zero, ← integral_comp_neg_Ioi,
    neg_zero]
  simp only [he]
  ring

/-- The evaluation of a band vector of the unweighted model is square integrable on the line. -/
theorem ratBand_memLp (Y : ℝ) (v : V₀(Y)) : MemLp (fun x ↦ ev(Y) x v) 2 volume := by
  exact ((Lp.memLp (v.val : Lp ℂ 2 μ₀)).ae_eq
    (RealPWBand.evaluation_ae Y hμ₀ (realPWIntervalMeasure_absolutelyContinuous 0 0)
      v).symm).mono_measure hμ₀

/-- The squared norm of a band vector of the unweighted model is the integral of the squared
modulus of its evaluation. -/
theorem ratBand_norm_sq (Y : ℝ) (v : V₀(Y)) : ‖v‖ ^ 2 = ∫ x, ‖ev(Y) x v‖ ^ 2 := by
  have e (F : ℝ → ℝ) : ∫ x, F x ∂μ₀ = ∫ x, F x := by rw [realPWIntervalMeasure_zero_zero]
  rw [norm_sq_realPWBand_of_evaluation_eq le_rfl v _ rfl, e]

/-- The function on the S-idele quotient attached to a band vector: `N ^ (1/2)` times twice its
evaluation at the norm `N`. -/
def ratLevelFun (Y : ℝ) (v : V₀(Y)) (c : Jq) : ℂ :=
  ((ratQuotNorm c ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (2 * ev(Y) (ratQuotNorm c) v)

theorem continuous_ratLevelFun (Y : ℝ) (v : V₀(Y)) : Continuous (ratLevelFun Y v) := by
  refine (Complex.continuous_ofReal.comp (continuous_ratQuotNorm.rpow_const fun c ↦
    Or.inl (ratQuotNorm_pos c).ne')).mul (continuous_const.mul ?_)
  exact ((RealPWBand.continuous_evaluation Y hμ₀).clm_apply continuous_const).comp
    continuous_ratQuotNorm

/-- The squared modulus of the profile of `ratLevelFun`, as a function of the norm. -/
theorem ratLevelFun_sq_norm_eq (Y : ℝ) (v : V₀(Y)) {t : ℝ} (ht : 0 < t) :
    t⁻¹ * ‖((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (2 * ev(Y) t v)‖ ^ 2 = 4 * ‖ev(Y) t v‖ ^ 2 := by
  have ht2 : (t ^ (1 / 2 : ℝ)) ^ 2 = t := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt ht.le]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),
    Complex.norm_two, mul_pow, mul_pow, ht2]
  field_simp
  ring

theorem measurable_ratLevelProfile (Y : ℝ) (v : V₀(Y)) :
    Measurable fun t : ℝ ↦ ‖((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (2 * ev(Y) t v)‖ ^ 2 :=
  (((Complex.continuous_ofReal.comp (Real.continuous_rpow_const (by norm_num))).mul
    (continuous_const.mul ((RealPWBand.continuous_evaluation Y hμ₀).clm_apply
      continuous_const))).norm.pow 2).measurable

/-- The function attached to a band vector is square integrable on the S-idele quotient. -/
theorem ratLevelFun_memLp (Y : ℝ) (v : V₀(Y)) : MemLp (ratLevelFun Y v) 2 μJq := by
  have : BorelSpace Jq := ⟨rfl⟩
  rw [memLp_two_iff_integrable_sq_norm (continuous_ratLevelFun Y v).aestronglyMeasurable]
  have h4 : IntegrableOn (fun t ↦ 4 * ‖ev(Y) t v‖ ^ 2) (Ioi 0) :=
    (((memLp_two_iff_integrable_sq_norm (ratBand_memLp Y v).aestronglyMeasurable).1 (ratBand_memLp Y v)).const_mul
      4).integrableOn
  exact (ratQuotNorm_integrable_iff (measurable_ratLevelProfile Y v)).2
    (h4.congr_fun (fun t ht ↦ (ratLevelFun_sq_norm_eq Y v ht).symm) measurableSet_Ioi)

/-- The integral of the squared modulus of the function attached to a band vector is twice the
squared norm of the vector. -/
theorem integral_ratLevelFun_sq (Y : ℝ) (v : V₀(Y)) :
    ∫ c, ‖ratLevelFun Y v c‖ ^ 2 ∂μJq = 2 * ‖v‖ ^ 2 := by
  have hint := (memLp_two_iff_integrable_sq_norm (ratBand_memLp Y v).aestronglyMeasurable).1 (ratBand_memLp Y v)
  have h := ratQuotNorm_integral (measurable_ratLevelProfile Y v)
  change ∫ c, (fun t : ℝ ↦ ‖((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (2 * ev(Y) t v)‖ ^ 2) (ratQuotNorm c)
    ∂μJq = _
  rw [h, setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ ratLevelFun_sq_norm_eq Y v ht),
    integral_const_mul, ratBand_norm_sq,
    integral_eq_two_mul_integral_Ioi_of_even hint
      (fun x ↦ by rw [RealPWBand.evaluation_even])]
  ring

local notation "mₛq" => (continuousSIdeleQuotientNorm ℚ Sq : SIdeleQuotient ℚ Sq →ₜ* ℝ≥0ˣ)
local notation "lwμ" => (sLocalQuotientTamagawaMeasure ℚ Sq).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 0 ((fun g ↦ Real.log (((mₛq) g).val : ℝ)) g)))

/-- At Sobolev order zero `main`'s local Sobolev measure is the quotient Tamagawa measure. -/
theorem ratLocalWMeasure_eq : lwμ = μJq := by
  have h : (fun g : Jq ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 0
      ((fun g ↦ Real.log (((mₛq) g).val : ℝ)) g))) = 1 := by
    funext g
    simp [intervalSobolevDensity]
  rw [h, withDensity_one]

theorem ratLevelFun_memLp' (Y : ℝ) (v : V₀(Y)) : MemLp (ratLevelFun Y v) 2 lwμ := by
  rw [ratLocalWMeasure_eq]
  exact ratLevelFun_memLp Y v

/-- The linear map from the unweighted model band to `main`'s local Sobolev space at order zero,
`v ↦ N ^ (1/2) · 2 · v(N)`. -/
def ratLevelMap (Y : ℝ) : V₀(Y) →ₗ[ℂ] Lp ℂ 2 lwμ where
  toFun v := (ratLevelFun_memLp' Y v).toLp
  map_add' v w := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun c ↦ ?_)
    simp only [ratLevelFun, map_add, Pi.add_apply]
    ring
  map_smul' a v := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun c ↦ ?_)
    simp only [ratLevelFun, map_smul, Pi.smul_apply, smul_eq_mul]
    ring

theorem ratLevelMap_ae (Y : ℝ) (v : V₀(Y)) : (ratLevelMap Y v : Jq → ℂ) =ᵐ[lwμ] ratLevelFun Y v :=
  (ratLevelFun_memLp' Y v).coeFn_toLp

theorem norm_sq_ratLevelMap (Y : ℝ) (v : V₀(Y)) : ‖ratLevelMap Y v‖ ^ 2 = 2 * ‖v‖ ^ 2 := by
  have e (F : Jq → ℝ) : ∫ c, F c ∂lwμ = ∫ c, F c ∂μJq := by rw [ratLocalWMeasure_eq]
  rw [← L2.integral_sq_norm (𝕜 := ℂ),
    integral_congr_ae (g := fun c ↦ ‖ratLevelFun Y v c‖ ^ 2)
      ((ratLevelMap_ae Y v).mono fun c hc ↦ by simp only [hc]), e,
    integral_ratLevelFun_sq]

theorem norm_ratLevelMap (Y : ℝ) (v : V₀(Y)) : ‖ratLevelMap Y v‖ = Real.sqrt 2 * ‖v‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (ratLevelMap Y v)), norm_sq_ratLevelMap, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (norm_nonneg v)]

/-- Reconstruction: the unweighted even band of `Sec4_RealPWLevelTrace` embeds isometrically in
`main`'s local Sobolev space of `ℚ` with no finite place, at order zero, by
`v ↦ 2 ^ (-1/2) · N ^ (1/2) · 2 · v(N)`. -/
def ratLevelIsometry (Y : ℝ) : V₀(Y) →ₗᵢ[ℂ] Lp ℂ 2 lwμ where
  toLinearMap := ((Real.sqrt 2)⁻¹ : ℂ) • ratLevelMap Y
  norm_map' v := by
    change ‖((Real.sqrt 2)⁻¹ : ℂ) • ratLevelMap Y v‖ = ‖v‖
    rw [norm_smul, norm_ratLevelMap, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg 2), ← mul_assoc,
      inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (by norm_num)), one_mul]

/-- Reflection commutes with the Fourier transform of a Schwartz function on the line. -/
theorem fourier_reflect (s : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) s) ξ =
      𝓕 s (-ξ) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_real_eq, Real.fourier_real_eq,
    ← integral_neg_eq_self (fun v ↦ 𝐞 (-(v * -ξ)) • s v)]
  congr 1
  funext v
  change 𝐞 (-(v * ξ)) • s (-v) = 𝐞 (-(-v * -ξ)) • s (-v)
  ring_nf

/-- The even part of a Schwartz function with Fourier transform vanishing outside `[-Y, Y]` is an
even Schwartz function with the same property. -/
theorem exists_evenPart {Y : ℝ} (s : 𝓢(ℝ, ℂ)) (hb : ∀ ξ ∉ Icc (-Y) Y, 𝓕 s ξ = 0) :
    ∃ g : 𝓢(ℝ, ℂ), (∀ t, g t = (s t + s (-t)) / 2) ∧ Function.Even (g : ℝ → ℂ) ∧
      ∀ ξ ∉ Icc (-Y) Y, 𝓕 g ξ = 0 := by
  let r := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) s
  have hr (t : ℝ) : r t = s (-t) := rfl
  refine ⟨(1 / 2 : ℂ) • (s + r), fun t ↦ ?_, fun t ↦ ?_, fun ξ hξ ↦ ?_⟩
  · rw [smul_apply, add_apply, hr, smul_eq_mul]
    ring
  · rw [smul_apply, smul_apply, add_apply, add_apply, hr, hr, neg_neg, add_comm]
  · have hξ' : -ξ ∉ Icc (-Y) Y := fun h ↦ hξ ⟨by linarith [h.2], by linarith [h.1]⟩
    have h1 : 𝓕 (s + r) = 𝓕 s + 𝓕 r := (SchwartzMap.fourierTransformCLM ℂ).map_add s r
    have h2 : 𝓕 ((1 / 2 : ℂ) • (s + r)) = (1 / 2 : ℂ) • 𝓕 (s + r) :=
      (SchwartzMap.fourierTransformCLM ℂ).map_smul _ _
    rw [h2, h1, smul_apply, add_apply, hb ξ hξ, fourier_reflect, hb _ hξ', add_zero, smul_zero]

/-- Reconstruction: for `ℚ` with no finite place, at twist `1/2` and Sobolev order zero, `main`'s
weighted theta vector of a test `f` is `volume₁` times the image under `ratLevelMap` of any band
vector whose evaluation is the even part of the Schwartz function of `f`. -/
theorem ratFullTheta_eq_smul {Y : ℝ} (χ : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker) (f : Bq)
    (s : 𝓢(ℝ, ℂ)) (hs : ∀ x, s (eq x.toAdd) = f x) (v : V₀(Y))
    (hv : ∀ t, ev(Y) t v = (s t + s (-t)) / 2) :
    (sLocalFullPWThetaSobolevMap (F := ℚ) (S := Sq) (s := 0) (a := 1 / 2) (by norm_num) χ f :
      Lp ℂ 2 lwμ) = (volume₁ : ℂ) • ratLevelMap Y v := by
  have h1 : (sLocalFullPWThetaSobolevMap (F := ℚ) (S := Sq) (s := 0) (a := 1 / 2) (by norm_num)
      χ f : Jq → ℂ) =ᵐ[lwμ] modulationWeight mₛq (1 / 2)
        (sLocalHomogeneousAdelicThetaLinearMap ℚ Sq χ f) :=
    (sLocalFullPWTheta_memLp (F := ℚ) (S := Sq) (s := 0) (by norm_num : (0 : ℝ) < 1 / 2) χ
      f).coeFn_toLp
  refine Lp.ext ?_
  filter_upwards [h1, Lp.coeFn_smul (volume₁ : ℂ) (ratLevelMap Y v), ratLevelMap_ae Y v]
    with c hc1 hc2 hc3
  rw [hc1, hc2, Pi.smul_apply, hc3, smul_eq_mul]
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  have hN : ratQuotNorm (QuotientGroup.mk x) = |eq x.val| := ratQuotNorm_mk x
  have hf1 : f (Multiplicative.ofAdd x.val) = s (eq x.val) := (hs _).symm
  have hf2 : f (Multiplicative.ofAdd (-x.val)) = s (-eq x.val) := by
    rw [← hs, toAdd_ofAdd, map_neg]
  have hev : ev(Y) |eq x.val| v = (s (eq x.val) + s (-eq x.val)) / 2 := by
    rw [hv]
    rcases abs_choice (eq x.val) with h | h <;> rw [h]
    · rw [neg_neg, add_comm]
  change ((ratQuotNorm (QuotientGroup.mk x) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      sLocalHomogeneousAdelicThetaLinearMap ℚ Sq χ f (QuotientGroup.mk x) = _
  rw [ratHomogeneousTheta_apply, hf1, hf2]
  unfold ratLevelFun
  rw [hN, hev]
  ring

local notation "testsq(" Y ")" =>
  sLocalPWTests (F := ℚ) (S := Sq) (T := Sq) le_rfl (sLocalPWProductRegion Sq Y)

theorem ratLevelMap_eq_smul_isometry (Y : ℝ) (v : V₀(Y)) :
    ratLevelMap Y v = ((Real.sqrt 2 : ℝ) : ℂ) • ratLevelIsometry Y v := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by norm_num))
  change ratLevelMap Y v = ((Real.sqrt 2 : ℝ) : ℂ) • (((Real.sqrt 2)⁻¹ : ℂ) • ratLevelMap Y v)
  rw [smul_smul, mul_inv_cancel₀ h2, one_smul]

/-- For a test of `main`'s band, a band vector of the model whose image is `volume₁⁻¹` times its
weighted theta vector. It lies in the model level when the test is polar-free. -/
theorem ratFullTheta_mem {Y : ℝ} (χ : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker) (f : Bq)
    (hf : f ∈ testsq(Y)) :
    ∃ v : V₀(Y), (sLocalFullPWThetaSobolevMap (F := ℚ) (S := Sq) (s := 0) (a := 1 / 2)
        (by norm_num) χ f : Lp ℂ 2 lwμ) = (volume₁ : ℂ) • ratLevelMap Y v ∧
      (f ∈ sAdelePolarSubspace ℚ Sq → v ∈ realPWZeroLevel Y 0 0 le_rfl) := by
  obtain ⟨s, hs, hb⟩ := ratBandTest_spec f hf
  obtain ⟨g, hg, he, hgb⟩ := exists_evenPart s hb
  have hm : MemLp (g : ℝ → ℂ) 2 μ₀ := by
    rw [realPWIntervalMeasure_zero_zero]
    exact g.memLp 2
  obtain ⟨v, hv⟩ := RealPWBand.exists_evaluation_eq_of_weightedSchwartz Y g he hgb hμ₀ hm
  refine ⟨v, ratFullTheta_eq_smul χ f s hs v (fun t ↦ by rw [congrFun hv t, hg]), fun hpol ↦ ?_⟩
  rw [mem_realPWZeroLevel_iff, congrFun hv 0, hg, neg_zero]
  have h0 : s 0 = 0 := by
    have h := hs (Multiplicative.ofAdd 0)
    rw [toAdd_ofAdd, map_zero] at h
    rw [h]
    exact ((mem_sAdelePolarSubspace f).1 hpol).1
  rw [h0]
  simp

set_option maxHeartbeats 800000 in
/-- The image of a core vector of the model band lies in `main`'s level. -/
theorem ratLevelIsometry_core_mem {Y : ℝ} (χ : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker)
    (u : V₀(Y)) (hu : u ∈ realPWBandPolarFreeCore Y 0 (le_rfl : (0 : ℝ) ≤ 0)) :
    ratLevelIsometry Y u ∈ ((testsq(Y) ⊓ LinearMap.ker (sAdelePolarValuesMap (F := ℚ) (S := Sq))).map
      (sLocalFullPWThetaSobolevMap (F := ℚ) (S := Sq) (s := 0) (a := 1 / 2) (by norm_num) χ)
        ).topologicalClosure := by
  obtain ⟨g, he, hb, h0, hi, hug⟩ := hu
  obtain ⟨f, hfg, htest, hpol⟩ := ratCore_test g hb h0 hi
  have hθ := ratFullTheta_eq_smul (Y := Y) χ f g (fun x ↦ (hfg x).symm) u
    (fun t ↦ by rw [congrFun hug t, he t]; ring)
  have hmem := Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem
    (f := sLocalFullPWThetaSobolevMap (F := ℚ) (S := Sq) (s := 0) (a := 1 / 2) (by norm_num) χ)
    (show f ∈ testsq(Y) ⊓ LinearMap.ker (sAdelePolarValuesMap (F := ℚ) (S := Sq)) from
      ⟨htest, hpol⟩))
  have hvol : ((volume₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ratNormOneMass_pos.ne'
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by norm_num))
  have hW : ratLevelIsometry Y u = (((Real.sqrt 2)⁻¹ : ℂ) * ((volume₁ : ℝ) : ℂ)⁻¹) •
      sLocalFullPWThetaSobolevMap (F := ℚ) (S := Sq) (s := 0) (a := 1 / 2) (by norm_num) χ f := by
    rw [hθ, smul_smul, mul_assoc, inv_mul_cancel₀ hvol, mul_one, ratLevelMap_eq_smul_isometry,
      smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [hW]
  exact Submodule.smul_mem _ _ hmem

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), p. 488, for `ℚ` with no finite place, twist
`1/2` and Sobolev order zero.
Reconstruction: `main`'s polar-free level `sLocalInvariantPWSobolev` is the image, under the
isometry `ratLevelIsometry`, of the level of the unweighted even band of `Sec4_RealPWLevelTrace`,
the band vectors that vanish at the origin. So the level traces of `Sec4_RationalLevelComparison`
and `Sec4_RationalLevelPolarMellin` are traces on `main`'s level. -/
theorem ratLevel_eq_map {Y : ℝ} (hY : 0 < Y) (χ : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker) :
    sLocalInvariantPWSobolev (F := ℚ) (S := Sq) (s := 0) le_rfl (a := 1 / 2) (by norm_num) χ Y =
      (realPWZeroLevel Y 0 0 le_rfl).map (ratLevelIsometry Y).toLinearMap := by
  have : CompleteSpace V₀(Y) := (RealPWBand.isClosed_space Y hμ₀).completeSpace_coe
  have hlevcl : IsClosed (realPWZeroLevel Y 0 0 le_rfl : Set V₀(Y)) := by
    unfold realPWZeroLevel
    exact Submodule.isClosed_orthogonal _
  have hcl : IsClosed (((realPWZeroLevel Y 0 0 le_rfl).map (ratLevelIsometry Y).toLinearMap :
      Submodule ℂ (Lp ℂ 2 lwμ)) : Set (Lp ℂ 2 lwμ)) := by
    rw [Submodule.map_coe]
    exact (ratLevelIsometry Y).isometry.isClosedEmbedding.isClosedMap _ hlevcl
  rw [sLocalInvariantPWSobolev_eq_closure_map]
  apply le_antisymm
  · refine Submodule.topologicalClosure_minimal _ ?_ hcl
    rintro _ ⟨f, ⟨htest, hpol⟩, rfl⟩
    obtain ⟨v, hθ, hlev⟩ := ratFullTheta_mem χ f htest
    rw [hθ, ratLevelMap_eq_smul_isometry, smul_smul]
    exact Submodule.smul_mem _ _ ⟨v, hlev hpol, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    have hvcl : v ∈ closure (realPWBandPolarFreeCore Y 0 (le_rfl : (0 : ℝ) ≤ 0)) := by
      rw [closure_realPWBandPolarFreeCore_eq le_rfl (by norm_num) le_rfl hY]
      exact (mem_realPWZeroLevel_iff Y 0 0 le_rfl v).1 hv
    have key := map_mem_closure (ratLevelIsometry Y).continuous hvcl
      (t := ((((testsq(Y) ⊓ LinearMap.ker (sAdelePolarValuesMap (F := ℚ) (S := Sq))).map
        (sLocalFullPWThetaSobolevMap (F := ℚ) (S := Sq) (s := 0) (a := 1 / 2) (by norm_num) χ)
          ).topologicalClosure : Submodule ℂ (Lp ℂ 2 lwμ)) : Set (Lp ℂ 2 lwμ)))
      (fun u hu ↦ ratLevelIsometry_core_mem χ u hu)
    rwa [(Submodule.isClosed_topologicalClosure _).closure_eq] at key

local notation "Hq" => sProjectedDiagonal ℚ Sq
local notation "normq(" x ")" => (((sIdeleNorm ℚ Sq x).val : ℝ))
local notation "mellin(" f ", " α ")" => ∫ g, (f).val g * ((normq(g) ^ (α : ℝ) : ℝ) : ℂ) ∂μq
local notation "mainLevel(" Y ", " χ ")" =>
  sLocalInvariantPWSobolev (F := ℚ) (S := Sq) (s := 0) le_rfl (a := 1 / 2) (by norm_num) χ Y
local notation "levelq(" Y ")" => realPWZeroLevel Y 0 0 le_rfl

/-- The conjugates of the model operators of `Sec4_RationalLevelComparison` take values in
`main`'s level. -/
theorem conjNuclear_mem_mainLevel {Y : ℝ} (hY : 0 < Y)
    (χ : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker) (T : nuclearEndomorphisms V₀(Y))
    (hT : ∀ v : V₀(Y), T.val v ∈ levelq(Y)) (x : Lp ℂ 2 lwμ) :
    (conjNuclear (ratLevelIsometry Y) T).val x ∈ mainLevel(Y, χ) := by
  refine (ratLevel_eq_map hY χ).ge ?_
  rw [conjNuclear_apply]
  exact Submodule.mem_map_of_mem (hT _)

set_option maxHeartbeats 4000000 in
/-- Paper: Theorem 12.4.1.1, Step III, p. 517, and the subtraction on p. 520, on `main`'s polar-free
level for `ℚ` with no finite place, at twist `1/2` and Sobolev order zero.
Reconstruction: the operators of `ratLevel_trace_add_polarMellin_tendsto`, conjugated by the
isometry `ratLevelIsometry`, take values in `main`'s level `sLocalInvariantPWSobolev` and keep their
traces. So on `main`'s level the trace less the summed sharp masses tends to minus the polar term,
and with the two polar Mellin values subtracted as on p. 520 it tends to
`∫ ψ(h) max (h ^ (1/2), h ^ (-1/2)) dh`, the part the level does not remove.
Deviation: The Mellin values are those of the S-idelic test `f`, not the global `M(φ)` (M25). The
bandwidth `Y` is fixed. -/
theorem ratMainLevel_trace_tendsto (f : BruhatCompactSupport Iq) {Y : ℝ} (hY : 0 < Y)
    (χ : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker) :
    ∃ T : ℝ → nuclearEndomorphisms V₀(Y),
      (∀ L, 0 < L → ∀ v : V₀(Y), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ratFold f g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ev(Y) (g⁻¹ * x) ((levelq(Y)).starProjection v))) ∧
        (T L).val v = (levelq(Y)).starProjection ((V₀(Y)).orthogonalProjectionOnto r)) ∧
      (∀ L, 0 < L → ∀ x, (conjNuclear (ratLevelIsometry Y) (T L)).val x ∈ mainLevel(Y, χ)) ∧
      Tendsto (fun L ↦ hilbertTrace (conjNuclear (ratLevelIsometry Y) (T L)) -
          ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y)) atTop (𝓝 (-ratPolarTerm f)) ∧
      Tendsto (fun L ↦ hilbertTrace (conjNuclear (ratLevelIsometry Y) (T L)) -
          ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y) + (mellin(f, 1 / 2) + mellin(f, -(1 / 2))))
        atTop (𝓝 (∫ h in Ioi 0, ratFold f h *
          ((max (h ^ (1 / 2 : ℝ)) (h ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ))) := by
  obtain ⟨T, hT, hlim⟩ := ratLevel_trace_add_polarMellin_tendsto f hY
  have hmem (L : ℝ) (hL : 0 < L) (x : Lp ℂ 2 lwμ) :
      (conjNuclear (ratLevelIsometry Y) (T L)).val x ∈ mainLevel(Y, χ) := by
    refine conjNuclear_mem_mainLevel hY χ (T L) (fun v ↦ ?_) x
    obtain ⟨r, -, hr⟩ := hT L hL v
    rw [hr]
    exact Submodule.starProjection_apply_mem _ _
  refine ⟨T, hT, hmem, ?_, ?_⟩
  · have h := hlim.add_const (-(mellin(f, 1 / 2) + mellin(f, -(1 / 2))))
    rw [← ratPolarMellin_sub_ratPolarTerm] at h
    simp only [hilbertTrace_conjNuclear]
    convert h using 2
    · ring
    · ring
  · simp only [hilbertTrace_conjNuclear]
    exact hlim

/-- Paper: Theorem 12.4.1.1 and the proof of Theorem 12.5.1.1, p. 520, on `main`'s polar-free level
for `ℚ` with no finite place.
Reconstruction: for a test with nonnegative real part, positive somewhere, the operators of
`ratMainLevel_trace_tendsto` on `main`'s level have traces less the summed sharp masses that do not
tend to minus the two polar Mellin values, which is what p. 520 needs. For a test supported on
norms at least one, the difference tends to exactly `M(f)(|·|^(1/2))`.
Deviation: The Mellin values are those of the S-idelic test `f`, not the global `M(φ)` (M25). -/
theorem ratMainLevel_trace_not_tendsto_polarMellin (f : BruhatCompactSupport Iq)
    (hf : ∀ g, 0 ≤ (f.val g).re) {g₀ : Iq} (hg₀ : 0 < (f.val g₀).re) {Y : ℝ}
    (T : ℝ → nuclearEndomorphisms V₀(Y))
    (hlim : Tendsto (fun L ↦ hilbertTrace (conjNuclear (ratLevelIsometry Y) (T L)) -
          ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y) + (mellin(f, 1 / 2) + mellin(f, -(1 / 2))))
        atTop (𝓝 (∫ h in Ioi 0, ratFold f h *
          ((max (h ^ (1 / 2 : ℝ)) (h ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ)))) :
    ¬ Tendsto (fun L ↦ hilbertTrace (conjNuclear (ratLevelIsometry Y) (T L)) -
        ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y))
      atTop (𝓝 (-(mellin(f, 1 / 2) + mellin(f, -(1 / 2))))) := by
  intro h0
  have h1 := h0.add_const (mellin(f, 1 / 2) + mellin(f, -(1 / 2)))
  rw [neg_add_cancel] at h1
  have hmaxc : ContinuousOn (fun h : ℝ ↦ max (h ^ (1 / 2 : ℝ)) (h ^ (-(1 / 2 : ℝ)))) (Ioi 0) :=
    continuous_max.comp_continuousOn ((continuousOn_rpow_Ioi _).prodMk (continuousOn_rpow_Ioi _))
  have hpos := integral_ratFold_mul_re_pos f hf hg₀ hmaxc
    fun h hh ↦ lt_max_of_lt_left (Real.rpow_pos_of_pos hh _)
  rw [tendsto_nhds_unique hlim h1, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

/-- For a test supported on norms at least one, the limit of `ratMainLevel_trace_tendsto` with the
two polar Mellin values subtracted is exactly `M(f)(|·|^(1/2))`: the level removes
`M(f)(|·|^(-1/2))` and leaves `M(f)(|·|^(1/2))`. -/
theorem ratMainLevel_limit_eq_of_one_le (f : BruhatCompactSupport Iq)
    (hf : ∀ g, f.val g ≠ 0 → 1 ≤ normq(g)) :
    (∫ h in Ioi 0, ratFold f h * ((max (h ^ (1 / 2 : ℝ)) (h ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ)) =
      mellin(f, 1 / 2) := by
  rw [← ratPolarMellin_sub_ratPolarTerm, ratPolarTerm_eq_mellin_neg_half f hf]
  ring

end RatQuotient

end RiemannMasullo.Isolated
