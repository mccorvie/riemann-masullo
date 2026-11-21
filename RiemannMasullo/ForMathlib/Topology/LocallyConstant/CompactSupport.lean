module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Topology.Compactness.Bases

public section

open Function Set TopologicalSpace

namespace RiemannMasullo

/-- Locally constant, compactly supported functions lie in the span of compact-open
indicators, a countable family on a second-countable space. -/
theorem exists_countable_span_of_locallyConstant_compactSupport
    (X 𝕜 : Type*) [TopologicalSpace X] [SecondCountableTopology X] [Ring 𝕜] :
    ∃ s : Set (X → 𝕜), s.Countable ∧ ∀ f : X → 𝕜,
      IsLocallyConstant f → HasCompactSupport f → f ∈ Submodule.span 𝕜 s := by
  classical
  let compactOpens : Set (Set X) := {U | IsCompact U ∧ IsOpen U}
  let C := ↥compactOpens
  let : Countable (countableBasis X) := countable_countableBasis X
  let unionBasis (t : Finset (countableBasis X)) : Set X := (t : Set (countableBasis X)).sUnion
  let : Countable C := (countable_range unionBasis).mono fun U hU ↦ by
    obtain ⟨t, ht⟩ := eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open _
      (isBasis_countableBasis X) U hU.1 hU.2
    exact ⟨t, ht.symm⟩
  let χ (U : C) := U.val.indicator (1 : X → 𝕜)
  refine ⟨range χ, countable_range _, fun f hf hc ↦ ?_⟩
  have hfinite : (f '' tsupport f).Finite := by
    let : CompactSpace (tsupport f) := isCompact_iff_compactSpace.mp hc
    rw [← range_domRestrict]
    exact (hf.comp_continuous continuous_subtype_val).range_finite
  let A := hfinite.toFinset.erase 0
  have h₀ (a : A) : a.val ≠ 0 := (Finset.mem_erase.mp a.property).1
  let U (a : A) : C := ⟨{x | f x = a.val},
    hc.of_isClosed_subset (hf.isClosed_fiber a.val)
      (fun x hx ↦ subset_tsupport f (mem_support.mpr (fun h ↦ h₀ a (hx.symm.trans h)))),
    hf.isOpen_fiber a.val⟩
  have hsum : (∑ a : A, a.val • χ (U a)) = f := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, χ, U, indicator, mem_ofPred_eq, Pi.one_apply]
    by_cases hx : f x = 0
    · rw [hx]
      exact Finset.sum_eq_zero fun a _ ↦ by simp [(h₀ a).symm]
    · have hmem : f x ∈ A := Finset.mem_erase.mpr
        ⟨hx, hfinite.mem_toFinset.mpr ⟨x, subset_tsupport f (mem_support.mpr hx), rfl⟩⟩
      let a : A := ⟨f x, hmem⟩
      rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _) (fun b _ hb ↦ ?_)]
      · simp [a]
      · have hne : f x ≠ b.val := fun h ↦ hb (Subtype.ext h.symm)
        simp [hne]
  rw [← hsum]
  exact Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _
    (Submodule.subset_span (mem_range_self (U a)))

end RiemannMasullo
