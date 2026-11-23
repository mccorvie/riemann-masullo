module

public import RiemannMasullo.AppA_AlgebraicNT.Sec2b

/-!
# S-unit counting in the adelic unit box

Appendix A.4, pp. 562–565. The finite set parameter lists the finite places of S.
The archimedean places are included in `SAdeleRing`.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open IsDedekindDomain NumberField
open scoped NNReal

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Oₛ" => Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Vₛ" => InfinitePlace F ⊕ S
local notation "sRank" => (Fintype.card (InfinitePlace F) + S.card - 1)
local notation "normℝ[" g "]" => ((Units.val (sIdeleNorm F S g) : ℝ≥0) : ℝ)
local notation "projectS" => Units.map (RingHom.toMonoidHom (adeleProjection F S))
local notation "outsideInclusion" =>
  Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside F S)))
local notation "unitAtS" =>
  MonoidHom.comp projectS
    (MonoidHom.comp outsideInclusion (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S))))

/-- Paper: Theorem A.4.1.1(1), (A.4.1.1), p. 562. The archimedean unit box consists
of adeles whose normalized absolute value at each infinite place is at most one. -/
def infiniteAdeleUnitBox : Set (InfiniteAdeleRing F) :=
  {x | ∀ w : InfinitePlace F, ‖x w‖ ^ w.mult ≤ 1}

/-- Paper: Theorem A.4.1.1(1), (A.4.1.1), p. 562. A point of the box has ordinary
completion norm at most one at every infinite place. -/
theorem mem_infiniteAdeleUnitBox_iff (x : InfiniteAdeleRing F) :
    x ∈ infiniteAdeleUnitBox F ↔ ∀ w : InfinitePlace F, ‖x w‖ ≤ 1 := by
  sorry

/-- Paper: Theorem A.4.1.1(1), p. 562. The archimedean unit box is compact. -/
theorem isCompact_infiniteAdeleUnitBox : IsCompact (infiniteAdeleUnitBox F) := by
  sorry

/-- Paper: Theorem A.4.1.1(1), p. 562. The archimedean unit box has nonempty interior. -/
theorem infiniteAdeleUnitBox_interior_nonempty : (interior (infiniteAdeleUnitBox F)).Nonempty := by
  sorry

/-- Paper: Theorem A.4.1.1(2), (A.4.1.2), p. 562. The test function is the indicator
of the archimedean unit box times the product of the finite-place integer-ring indicators. -/
def sAdeleUnitBoxIndicator (x : SAdeleRing F S) : ℝ :=
  (infiniteAdeleUnitBox F).indicator (fun _ ↦ (1 : ℝ)) x.1 *
    ∏ v : S, (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)).indicator
      (fun _ ↦ (1 : ℝ)) (x.2 v)

/-- Paper: Theorem A.4.1.1(2), (A.4.1.2), p. 562. The product indicator is one when
all coordinates have norm at most one and zero elsewhere. -/
theorem sAdeleUnitBoxIndicator_apply (x : SAdeleRing F S) :
    sAdeleUnitBoxIndicator F S x =
      if (∀ w : InfinitePlace F, ‖x.1 w‖ ≤ 1) ∧ (∀ v : S, ‖x.2 v‖ ≤ 1) then 1 else 0 := by
  sorry

/-- Paper: Theorem A.4.1.1(2), p. 562. The product indicator has compact support. -/
theorem hasCompactSupport_sAdeleUnitBoxIndicator :
    HasCompactSupport (sAdeleUnitBoxIndicator F S) := by
  sorry

/-- Paper: Theorem A.4.1.1(2), p. 562. The product indicator is continuous off the
boundary of the product box.
Deviation: The continuity assertion specifies where the piecewise constant function is
continuous by excluding the frontier of its support. -/
theorem continuousAt_sAdeleUnitBoxIndicator (x : SAdeleRing F S)
    (hx : x ∉ frontier (Function.support (sAdeleUnitBoxIndicator F S))) :
    ContinuousAt (sAdeleUnitBoxIndicator F S) x := by
  sorry

/-- Paper: Theorem A.4.1.1, (A.4.1.3), p. 562. Uniformly for S-ideles of sufficiently
small S-idelic norm, the number of diagonal S-unit multiples in the unit box is bounded
by a constant times the absolute log norm to the power `|S| - 1`.
Deviation: The statement makes the finite support of the displayed sum explicit. -/
theorem sUnit_unitBox_count_bound :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ g : Iₛ, normℝ[g] < ε →
      let term := fun u : Oₛˣ ↦ sAdeleUnitBoxIndicator F S (unitAtS u * g).val
      (Function.support term).Finite ∧ ∑' u, term u ≤ C * |Real.log (normℝ[g])| ^ sRank := by
  sorry

-- TODO(paper-gap): Page 562, note 3, proposes a remark about Connes without a statement.
-- TODO(paper-gap): Page 563, the image following (A.4.1.4) has discrete finite coordinates.
-- TODO(paper-gap): Page 563, (A.4.1.6) omits the torsion-fibre factor in the count.
-- TODO(paper-gap): Page 563, (A.4.1.7) can fail as a set equality. In ℚ(√2) take
-- the inert prime (3), the S-unit basis 3(1 + √2), 3 modulo torsion, and g₁ = 1.
-- At parallelotope coefficients (1/2, 1/2) the finite valuation is 1. Every basic
-- idele has finite valuation 0. Compare the domains modulo diagonal S-units.
-- TODO(paper-gap): Page 564, (A.4.1.8) pairs the normalized Haar measure with a Euclidean covolume.
-- TODO(paper-gap): Page 565, the proof of (A.4.1.9) assumes planar slicing preserves the face angles.
-- TODO(paper-gap): Page 565, the final constant omits the covolume and the counting error.

local notation "PicKernel" => MonoidHom.ker (CommRing.Pic.mapAlgebra (𝓞 F) Oₛ)
local notation "OutsideNormOne" => MonoidHom.ker (MonoidHom.comp (ideleNorm F) outsideInclusion)
local notation "Nₛ" => MonoidHom.ker (sIdeleNorm F S)

/-- Paper: Claim A.4.1.2, p. 564. For fixed F and S there is a common radius multiplier
for every choice of fundamental domains and class representatives. For sufficiently
small basic ideles the translated slice lies in the ball of that radius times the
absolute log norm, uniformly in the basic idele and the class.
Deviation: The representatives project from global norm-one ideles that are units
outside S. A basic idele is the diagonal section times an archimedean domain point
with finite components in the local unit groups. -/
theorem sIdeleLog_basic_slice_subset_closedBall :
    ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
      (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
      (bₛ : Module.Basis (Fin sRank) ℤ (Additive (Oₛˣ ⧸ CommGroup.torsion Oₛˣ)))
      (r : PicKernel → OutsideNormOne),
      (∀ i, ideleIdealClass F (outsideInclusion (r i).val) = i.val ∧
        projectS (outsideInclusion (r i).val) ∈
          Subgroup.subtype Nₛ '' sLocalIdeleFundamentalDomain F v₀ σ S bₛ) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ (t : ℝ≥0ˣ) (g₀ : Iₛ),
        Units.map (RingHom.fst _ _).toMonoidHom g₀ ∈
          Subgroup.subtype (infiniteIdeleNorm F).ker '' infiniteIdeleFundamentalDomain F b v₀ σ →
        (∀ v : S, g₀.val.2 v ∈ v.val.adicCompletionIntegers F ∧
          g₀.inv.2 v ∈ v.val.adicCompletionIntegers F) →
        let g := projectS (diagonalIdeleNormSection F t) * g₀
        normℝ[g] < ε → ∀ i : PicKernel,
          let gᵢ := projectS (outsideInclusion (r i).val)
          {x : EuclideanSpace ℝ Vₛ | (∑ v, x v) = 0 ∧
            ∀ v, x v + sIdeleLog F S (gᵢ * g) v ≤ 0} ⊆
            Metric.closedBall 0 (C₀ * |Real.log (normℝ[g])|) := by
  sorry

end RiemannMasullo
