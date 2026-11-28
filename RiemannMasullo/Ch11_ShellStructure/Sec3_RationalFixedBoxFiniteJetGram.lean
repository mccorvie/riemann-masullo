module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxFiniteJetQuotient
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Intrinsic Gram norm on the actual finite-prime quotient

The finite Euclidean jet Gram is strictly positive. Its inverse gives the
least-norm interpolation lift through the actual orthogonal representative. -/

public noncomputable section

namespace RiemannMasullo.RationalPacket
open scoped InnerProduct

variable {X : ℝ} (hX : 0 < X) (T K : Finset ℕ)
  (hT : ∀ p ∈ T, p.Prime) (hK : ∀ p ∈ K, p.Prime) (hd : Disjoint T K)
  {j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K.card)

local notation "C" => fixedBoxColumnIntersection hX T K hT hK hd hj hjK
local notation "N" => ClosedSubmodule.toSubmodule (fixedBoxColumnDenominator hX T K hT hK hd hj hjK)
local notation "L" => fixedBoxColumnJets hX T K hT hK hd hj hjK
local notation "D" => EuclideanSpace ℂ (Fin (K.card - j))
local notation "P" => (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (K.card - j) ↦ ℂ))

/-- The raw consecutive jets, with Euclidean rather than supremum norm on the datum. -/
def fixedBoxColumnEuclideanJets : C →L[ℂ] D := (P).symm.toContinuousLinearMap.comp L

local notation "J" => fixedBoxColumnEuclideanJets hX T K hT hK hd hj hjK

theorem fixedBoxColumnEuclideanJets_surjective : Function.Surjective J :=
  (P).symm.surjective.comp (fixedBoxColumnJets_surjective hX T K hT hK hd hj hjK)

private theorem jet_zero_iff (v : C) : J v = 0 ↔ v ∈ N := by
  rw [← ker_fixedBoxColumnJets hX T K hT hK hd hj hjK]
  change (P).symm (L v) = 0 ↔ L v = 0
  rw [← (P).symm.map_zero, (P).symm.injective.eq_iff]

private theorem jet_adjoint_injective : Function.Injective ((J).adjoint) := by
  intro a b hab
  apply ext_inner_left ℂ
  intro y
  obtain ⟨v, rfl⟩ := fixedBoxColumnEuclideanJets_surjective hX T K hT hK hd hj hjK y
  rw [← (J).adjoint_inner_right v a, ← (J).adjoint_inner_right v b, hab]

/-- Surjectivity of the actual jets makes the finite Gram operator `J J†` invertible. -/
def fixedBoxColumnGramEquiv : D ≃ₗ[ℂ] D :=
  LinearEquiv.ofInjectiveEndo ((J).comp (J).adjoint).toLinearMap
    ((J).self_comp_adjoint_injective_iff.mpr (jet_adjoint_injective hX T K hT hK hd hj hjK))

local notation "G" => fixedBoxColumnGramEquiv hX T K hT hK hd hj hjK

theorem fixedBoxColumnGramEquiv_apply (z : D) : G z = J ((J).adjoint z) := by
  unfold fixedBoxColumnGramEquiv
  rfl

theorem fixedBoxColumnGram_pos (z : D) (hz : z ≠ 0) : 0 < (inner ℂ z (G z)).re := by
  change 0 < (inner ℂ z (J ((J).adjoint z))).re
  rw [← (J).adjoint_inner_left]
  change 0 < RCLike.re (inner ℂ ((J).adjoint z) ((J).adjoint z))
  rw [inner_self_eq_norm_sq (𝕜 := ℂ)]
  exact sq_pos_of_pos (norm_pos_iff.mpr (fun h ↦ hz
    (jet_adjoint_injective hX T K hT hK hd hj hjK (h.trans (J).adjoint.map_zero.symm))))

/-- Mathlib's complex inner product is conjugate-linear in its first argument.
For the actual datum `y = J u`, the squared quotient norm is `re ⟪y,G⁻¹y⟫`.
The orthogonal representative is `J† G⁻¹y`, not an arbitrary interpolation lift. -/
theorem fixedBoxColumnQuotient_norm_sq (u : C) :
    ‖(Submodule.Quotient.mk u : C ⧸ N)‖ ^ 2 = (inner ℂ (J u) ((G).symm (J u))).re := by
  let z := (G).symm (J u)
  let w := (J).adjoint z
  have hw : J w = J u := (G).apply_symm_apply (J u)
  have horth : w ∈ (N)ᗮ := by
    intro v hv
    change inner ℂ v ((J).adjoint z) = 0
    rw [(J).adjoint_inner_right, (jet_zero_iff hX T K hT hK hd hj hjK v).2 hv, inner_zero_left]
  have hq : (Submodule.Quotient.mk u : C ⧸ N) = Submodule.Quotient.mk w := by
    apply (Submodule.Quotient.eq N).2
    apply (jet_zero_iff hX T K hT hK hd hj hjK _).1
    rw [map_sub, hw, sub_self]
  have hn : ‖(Submodule.Quotient.mk u : C ⧸ N)‖ = ‖w‖ := by
    calc
      _ = ‖(N).quotientEquivOrthogonal (Submodule.Quotient.mk w)‖ := by
        rw [hq, LinearIsometryEquiv.norm_map]
      _ = ‖w‖ := by
        rw [(N).quotientEquivOrthogonal_mk w horth]
        rfl
  rw [hn]
  change ‖w‖ ^ 2 = (inner ℂ (J u) z).re
  rw [← hw, ← (J).adjoint_inner_right]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) w).symm

end RiemannMasullo.RationalPacket
