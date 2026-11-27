module

public import RiemannMasullo.AppD_SchwartzBruhat.ContinuousHom
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelBridge
import RiemannMasullo.ForMathlib.Analysis.Normed.Field.ProperSpace

/-!
# Real-place representatives of rational native Bruhat tests

At the empty finite stage a rational idèle class is determined by its norm.
Pulling a quotient test back by the absolute norm of the real completion and
the quotient norm section gives its representative on both real signs.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo.AnnularBand

local notation "J" => SIdeleQuotient ℚ ∅
local notation "N" => sIdeleQuotientNorm ℚ ∅
local notation "K∞" => Rat.infinitePlace.Completion

local instance : T2Space J := by
  have := isClosed_sProjectedDiagonal (F := ℚ) (S := ∅)
  exact inferInstanceAs (T2Space (_ ⧸ _))
local instance : LocallyCompactSpace J := by
  let : LocallyCompactSpace (SAdeleRing ℚ ∅)ˣ := (sIdeleGroup_description ℚ ∅).2.2.1
  exact inferInstanceAs (LocallyCompactSpace (_ ⧸ _))

/-- Each genuine Bruhat test on the rational quotient has a compact Bruhat
representative on the real-place units agreeing at every common absolute norm. -/
theorem exists_realPlaceBruhatTest_of_rationalQuotient (ψ : BruhatCompactSupport J) :
    ∃ f : BruhatCompactSupport K∞ˣ, ∀ (u : K∞ˣ) (g : J),
      ((N g).val : ℝ) = ‖u.val‖ → f.val u = ψ.val g := by
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section ℚ ∅
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding Rat.infinitePlace
  let : ProperSpace K∞ := LipschitzWith.properSpace hi.isClosedEmbedding.isProperMap hi.lipschitzWith
  let n : K∞ˣ →* ℝ≥0ˣ := Units.map nnNormHom.toMonoidHom
  have hn : IsProperMap n := by
    have hp := isProperMap_units_nnNorm_pow (K := K∞) 1 one_ne_zero
    have he : (⇑(n ^ (1 : ℕ)) : K∞ˣ → ℝ≥0ˣ) = n := by
      funext u
      change n u ^ 1 = n u
      exact pow_one _
    rw [← he]
    exact hp
  let π : K∞ˣ →ₜ* J := σ.comp ⟨n, hn.continuous⟩
  have hnorm (u : K∞ˣ) : N (π u) = n u := hσ _
  have hcompact : HasCompactSupport (ψ.val ∘ π) := by
    refine HasCompactSupport.intro
      (hn.isCompact_preimage (ψ.property.2.image (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous))
      (fun u hu ↦ show ψ.val (π u) = 0 from image_eq_zero_of_notMem_tsupport ?_)
    exact fun h ↦ hu ⟨π u, h, hnorm u⟩
  have hsmooth : IsBruhatSmooth (ψ.val ∘ π) :=
    isBruhatSmooth_comp_continuousMonoidHom π ((mem_bruhatSmoothSubmodule_iff ψ.val).mp ψ.property.1)
  refine ⟨⟨ψ.val ∘ π, (mem_bruhatSmoothSubmodule_iff _).mpr hsmooth, hcompact⟩, fun u g hg ↦ ?_⟩
  change ψ.val (π u) = ψ.val g
  apply congrArg ψ.val
  apply ratEmptyLevel_norm_injective
  exact (hnorm u).trans (Units.ext (NNReal.eq hg.symm))

end RiemannMasullo.AnnularBand
