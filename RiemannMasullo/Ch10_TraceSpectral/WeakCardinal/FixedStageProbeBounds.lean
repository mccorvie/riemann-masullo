module

public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.SingletonProbeBounds
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b

/-! Realization of the fixed test stage used by the uniform boundedness necessity argument. -/

@[expose] public noncomputable section

open Set Topology TopologicalSpace NumberField
open scoped NumberField.AdeleRing
open scoped NNReal

namespace RiemannMasullo.WeakCardinal

section Stage

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (b : BruhatStructuralPair G) (e : ElementaryLCAPresentation b.quotient) (K : Compacts G)

local notation "X" => bruhatCompactSupportStage b e K

/-- The canonical inclusion of the fixed-support elementary test stage into the compact Bruhat tests. -/
def fixedStageInclusionCLM : X →L[ℂ] BruhatCompactSupport G :=
  ⟨bruhatCompactSupportStageInclusion b e K,
    (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp
      (show X →ₗ[ℂ] BruhatCompactSupport G from bruhatCompactSupportStageInclusion b e K)
      (fun p ↦ p.property b e K)⟩

/-- The intrinsic topology of this fixed-support stage uses exactly the restrictions of the
elementary Schwartz seminorms. -/
theorem fixedStage_withSeminorms :
    WithSeminorms (fun k ↦ (elementarySchwartzSeminorm k).comp (X).subtype) :=
  (X).subtype.withSeminorms_induced elementarySchwartz_withSeminorms

/-- A fixed compact support cuts out a closed subspace of the elementary Schwartz Fréchet
space, so the actual native stage is barrelled. -/
theorem fixedStage_barrelled : BarrelledSpace ℂ X := by
  have hfrechet : IsFrechetTVS (SchwartzBruhatStage e) := elementarySchwartz_isFrechet
  obtain ⟨_, _, hmet, hcomp⟩ := hfrechet
  have : CompleteSpace (SchwartzBruhatStage e) := by
    rwa [IsUniformAddGroup.rightUniformSpace_eq] at hcomp
  have : (uniformity (SchwartzBruhatStage e)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero (SchwartzBruhatStage e)]
    infer_instance
  have hclosed : IsClosed (X : Set (SchwartzBruhatStage e)) := by
    simp only [bruhatCompactSupportStage, Submodule.coe_iInf]
    apply isClosed_iInter
    intro g
    have heval := (continuous_schwartzBruhat_eval g.val).comp (schwartzBruhatStage_isEmbedding b e).continuous
    exact isClosed_singleton.preimage heval
  have : IsCompletelyPseudoMetrizableSpace X := hclosed.isCompletelyPseudoMetrizableSpace
  have : ContinuousSMul ℂ X := (fixedStage_withSeminorms b e K).continuousSMul
  exact BaireSpace.instBarrelledSpace

end Stage

section OriginalSites

set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
variable (a : ℝ) {s : ℝ} (hs : 1 < s)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "hs₀" => zero_le_one.trans hs.le
local notation "h₀" => (le_refl (0 : ℝ))
local notation "hI" => (neg_nonpos.mpr h₀).trans h₀
local notation "Q" => spectralSobolevQuotient F a (l := -(0 : ℝ)) (r := 0) (s := s) hI hs₀

variable (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual (IdeleClassGroup (𝓞 F) F))
variable (b : BruhatStructuralPair (IdeleClassGroup (𝓞 F) F))
  (e : ElementaryLCAPresentation b.quotient) (K : Compacts (IdeleClassGroup (𝓞 F) F))
local notation "X" => bruhatCompactSupportStage (G := C𝔽) b e K
local notation "incl" => fixedStageInclusionCLM (G := C𝔽) b e K
local notation "orderAt(" z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ (z).1))
  (((a + (z).2.1 : ℝ) : ℂ) + ((z).2.2 : ℂ) * Complex.I)
local notation "sites" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-(0 : ℝ)) 0 ∧ 0 < orderAt(z)}
local notation "rows(" z ")" => spectralStripMultiplicity 0 s (z).val.2.1 (orderAt((z).val)).untop₀.toNat
local notation "jets" => SpectralStripJetIndex (F := F) χ a 0 s
local notation "jet(" z "," m ")" =>
  (⟨((z).val.1, (z).val.2.1, (z).val.2.2, (m).val), (m).isLt⟩ : jets)

local notation "W" => CompactIntervalSobolev (ideleClassTamagawaMeasure F) (logIdeleClassNorm F) (-(0 : ℝ)) 0 s

include χ F a hs in
/-- The original zero-width geometric block is the finite sum over its retained jets. -/
def spectralStripGeometryAtSite (x : jets → Q) (f : jets → StrongDual ℂ Q)
    (φ : BruhatCompactSupport C𝔽) (z : sites) : nuclearEndomorphisms W :=
  ∑ m : Fin (rows(z)), nativeSingletonBlock (F := F) (α := 0) (s := s) a h₀ hs₀
    (x jet(z,m)) (f jet(z,m)) φ

end OriginalSites

end RiemannMasullo.WeakCardinal
