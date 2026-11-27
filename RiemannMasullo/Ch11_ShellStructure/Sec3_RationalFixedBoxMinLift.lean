module

public import RiemannMasullo.AppC_LCTVS.Sec3a_part2
public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxNuclear
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Minimum-norm realization of the actual fixed-box packet

The quotient has a canonical isometric section given by the orthogonal
complement of the next closed stage. Extending the official nuclear quotient
operators by zero through this section preserves both trace norm and Hilbert trace. -/

public noncomputable section

open scoped BigOperators InnerProductSpace

namespace RiemannMasullo

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A Hilbert operator on an isometric copy, extended by zero on its orthogonal complement. -/
@[expose] def isometricOperatorLift (I : H →ₗᵢ[ℂ] K) (A : H →L[ℂ] H) : K →L[ℂ] K :=
  I.toContinuousLinearMap.comp (A.comp I.toContinuousLinearMap.adjoint)

/-- Extension by zero off an isometric copy preserves the trace norm, including
when the source is trivial. -/
theorem traceNorm_isometric_sandwich_eq (I : H →ₗᵢ[ℂ] K) (A : H →L[ℂ] H)
    (hA : IsNuclearOperator A) :
    ∃ h : IsNuclearOperator (isometricOperatorLift I A),
      traceNorm ⟨_, h⟩ = traceNorm ⟨A, hA⟩ := by
  let L := I.toContinuousLinearMap
  let V := L.comp (A.comp L.adjoint)
  have hleft (x : H) : L.adjoint (L x) = x :=
    DFunLike.congr_fun I.adjoint_comp_self x
  have hcancel : L.adjoint.comp (V.comp L) = A := by
    ext x
    change L.adjoint (L (A (L.adjoint (L x)))) = A x
    rw [hleft, hleft]
  have hn : ‖L‖ ≤ 1 := I.norm_toContinuousLinearMap_le
  have hd : ‖L.adjoint‖ ≤ 1 := (ContinuousLinearMap.adjoint.norm_map L).le.trans hn
  obtain ⟨hv, hforward⟩ := traceNorm_sandwich_le A hA L.adjoint L
  have hrecovery := traceNorm_sandwich_le V hv L L.adjoint
  rw [hcancel] at hrecovery
  obtain ⟨_, hreverse⟩ := hrecovery
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  let : Norm (nuclearEndomorphisms K) := ⟨traceNorm⟩
  have ha₀ := (traceNorm_normedSpaceCore (H := H)).norm_nonneg (⟨A, hA⟩ : nuclearEndomorphisms H)
  have hv₀ := (traceNorm_normedSpaceCore (H := K)).norm_nonneg (⟨V, hv⟩ : nuclearEndomorphisms K)
  refine ⟨hv, le_antisymm (hforward.trans ?_) (hreverse.trans ?_)⟩
  · apply mul_le_of_le_one_left ha₀
    exact (mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans (by simpa using hd)
  · apply mul_le_of_le_one_left hv₀
    exact (mul_le_mul_of_nonneg_right hd (norm_nonneg _)).trans (by simpa using hn)

/-- Extending a nuclear operator by zero along a linear isometry preserves Hilbert trace. -/
theorem hilbertTrace_isometricOperatorLift (I : H →ₗᵢ[ℂ] K) (A : H →L[ℂ] H)
    (hA : IsNuclearOperator A) :
    ∃ hLift : IsNuclearOperator (isometricOperatorLift I A),
      hilbertTrace ⟨_, hLift⟩ = hilbertTrace ⟨A, hA⟩ := by
  let L := I.toContinuousLinearMap
  let B := A.comp L.adjoint
  have hB : IsNuclearOperator B := by
    obtain ⟨c, f, y, hc, hf, hy, hs⟩ := (isNuclearOperator_iff_isBanachNuclear A).mp hA
    apply (isNuclearOperator_iff_isBanachNuclear B).mpr
    exact ⟨c, fun n ↦ (f n).comp L.adjoint, y, hc,
      ((L.adjoint.precomp ℂ).continuous.tendsto' 0 0 (map_zero _)).comp hf,
      hy, fun x ↦ hs (L.adjoint x)⟩
  have hc : B.comp L = A := by
    ext x
    change A (L.adjoint (L x)) = A x
    exact congrArg A (DFunLike.congr_fun I.adjoint_comp_self x)
  have hn := isNuclearOperator_factor_comps L I.injective B hB
  refine ⟨hn.2, ?_⟩
  calc
    hilbertTrace ⟨_, hn.2⟩ = hilbertTrace ⟨B.comp L, hn.1⟩ := by
      simp only [hilbertTrace_eq_nuclearTrace]
      exact (nuclearTrace_factor_comps hilbert_approximationProperty hilbert_approximationProperty
        L I.injective B hB).symm
    _ = hilbertTrace ⟨A, hA⟩ := congrArg hilbertTrace (Subtype.ext hc)

namespace RationalPacket

variable (X : ℝ) (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q) (p : ℕ)
  (hTp : ∀ q ∈ insert p T, 1 ≤ q)

local notation "E" => closedStageSubmodule X T hT
local notation "N" => ClosedSubmodule.toSubmodule (fixedBoxDenominator X T hT p hTp)
local notation "Q" => FixedBoxQuotient[X,T,hT,p,hTp]

/-- Isometric choice of the actual closed-stage representative perpendicular to the denominator. -/
def fixedBoxMinNormSection : Q →ₗᵢ[ℂ] E :=
  (N)ᗮ.subtypeₗᵢ.comp (N).quotientEquivOrthogonal.toLinearIsometry

theorem fixedBoxMinNormSection_spec (q : Q) :
    (N).mkQL (fixedBoxMinNormSection X T hT p hTp q) = q ∧
    ∀ x : E, (N).mkQL x = q → ‖fixedBoxMinNormSection X T hT p hTp q‖ ≤ ‖x‖ := by
  let y := (N).quotientEquivOrthogonal q
  constructor
  · change Submodule.Quotient.mk (y : E) = q
    exact ((N).quotientEquivOrthogonal_symm_eq_mk y.val y.property).symm.trans
      ((N).quotientEquivOrthogonal.symm_apply_apply q)
  · intro x hx
    rw [LinearIsometry.norm_map, ← hx]
    exact Submodule.Quotient.norm_mk_le (N) x

end RationalPacket
end RiemannMasullo

namespace RiemannMasullo
namespace RationalPacket

open scoped SchwartzMap

variable {X : ℝ} (T : Finset ℕ) (hT1 : ∀ q ∈ T, 1 ≤ q) (p : ℕ)
  (hTp : ∀ q ∈ insert p T, 1 ≤ q) (hX : 0 < X) (hp : p.Prime) (hpT : p ∉ T)
local notation "E" => closedStageSubmodule X T hT1
local notation "Q" => FixedBoxQuotient[X,T,hT1,p,hTp]
local notation "S" => fixedBoxMinNormSection X T hT1 p hTp
local notation "L" => Real.log (p : ℝ)
local notation "A" => fixedBoxTestAction T hT1 p hTp hX hp hpT

/-- The integrated Schwartz-test action, realized on the preceding closed stage
by its orthogonal minimum section, has the logarithmic lattice trace. -/
theorem fixedBoxMinLift_testAction_poisson_trace (hT : ∀ q ∈ T, q.Prime) (w : 𝓢(ℝ, ℂ)) :
    ∃ h : IsNuclearOperator (isometricOperatorLift (H := Q) (K := E) S (A w)),
      hilbertTrace ⟨_, h⟩ = (L : ℂ) * ∑' k : ℤ, w (L * k) := by
  obtain ⟨hA, ht⟩ := fixedBoxTestAction_poisson_trace T hT1 p hTp hX hp hpT hT w
  obtain ⟨hLift, he⟩ := hilbertTrace_isometricOperatorLift (H := Q) (K := E) S (A w) hA
  exact ⟨hLift, he.trans ht⟩

/-- Translating the Schwartz test by `a` samples the shifted physical lattice,
with the same period factor and with frequency zero retained. -/
theorem fixedBoxMinLift_translated_testAction_poisson_trace (hT : ∀ q ∈ T, q.Prime)
    (w : 𝓢(ℝ, ℂ)) (a : ℝ) :
    ∃ h : IsNuclearOperator (isometricOperatorLift (H := Q) (K := E) S (A (w.compSubConstCLM ℂ a))),
      hilbertTrace ⟨_, h⟩ = (L : ℂ) * ∑' k : ℤ, w (L * k - a) := by
  simpa only [SchwartzMap.compSubConstCLM_apply] using
    fixedBoxMinLift_testAction_poisson_trace T hT1 p hTp hX hp hpT hT (w.compSubConstCLM ℂ a)

end RationalPacket
end RiemannMasullo
