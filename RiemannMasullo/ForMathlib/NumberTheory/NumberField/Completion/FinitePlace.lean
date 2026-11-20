module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

import Mathlib.Topology.Algebra.Valued.LocallyCompact

public section

namespace RiemannMasullo

open Filter IsDedekindDomain IsLocalRing Topology
open scoped WithZero

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The residue field of the completion is a quotient of `R / v`. -/
private theorem finite_residueField_adicCompletion (v : HeightOneSpectrum R) :
    Finite (ResidueField (v.adicCompletionIntegers K)) := by
  let O := v.adicCompletionIntegers K
  let f := (residue O).comp (algebraMap R O)
  let q : R ⧸ v.asIdeal →+* ResidueField O := Ideal.Quotient.lift v.asIdeal f (by
    intro r hr
    rw [RingHom.comp_apply, residue_eq_zero_iff]
    apply (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).2
    change Valued.v (algebraMap R (v.adicCompletion K) r) < (1 : ℤᵐ⁰)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
    exact (v.valuation_lt_one_iff_mem r).2 hr)
  have := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  apply Finite.of_surjective q
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  -- Approximate the representative first by an element of `K`, then by one of `R`.
  let ν : Valuation (v.adicCompletion K) ℤᵐ⁰ := Valued.v
  have hn : {z | ν (z - (x : v.adicCompletion K)) < 1} ∈ 𝓝 (x : v.adicCompletion K) := by
    refine Valued.mem_nhds.mpr ⟨1, ?_⟩
    intro z hz
    simpa only [Set.mem_ofPred_eq, Units.val_one, Valuation.restrict_lt_iff_lt_embedding,
      map_one] using hz
  obtain ⟨a, ha⟩ := (v.denseRange_algebraMap K).mem_nhds hn
  change ν (algebraMap K (v.adicCompletion K) a - x) < 1 at ha
  have ha' : v.valuation K a ≤ 1 := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    change ν (algebraMap K (v.adicCompletion K) a) ≤ 1
    simpa only [sub_add_cancel] using ν.map_add_le ha.le x.property
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer ha' 1
  have hr' : ν (algebraMap R (v.adicCompletion K) r - algebraMap K (v.adicCompletion K) a) < 1 := by
    rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K), ← map_sub]
    change Valued.v (((algebraMap R K) r - a : K) : v.adicCompletion K) < (1 : ℤᵐ⁰)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa only [Units.val_one] using hr
  refine ⟨Ideal.Quotient.mk _ r, sub_eq_zero.mp ?_⟩
  change residue O (algebraMap R O r) - residue O x = 0
  rw [← map_sub, residue_eq_zero_iff]
  apply (Valuation.mem_maximalIdeal_iff _ ν).2
  change ν (algebraMap R (v.adicCompletion K) r - x) < 1
  simpa only [sub_add_sub_cancel] using ν.map_add_lt hr' ha

open Valued.integer in
/-- The completion of the fraction field at a height-one prime is locally compact when the
base Dedekind domain has finite quotients. -/
theorem locallyCompactSpace_adicCompletion (v : HeightOneSpectrum R) :
    LocallyCompactSpace (v.adicCompletion K) := by
  have : IsDiscreteValuationRing (v.adicCompletionIntegers K) := inferInstance
  have : ProperSpace (v.adicCompletion K) :=
    (properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (Γ₀ := ℤᵐ⁰)).2 ⟨inferInstance, ‹_›, finite_residueField_adicCompletion v⟩
  infer_instance

/-- The integers of an adic completion are compact when the base Dedekind domain has finite
quotients. -/
theorem compactSpace_adicCompletionIntegers (v : HeightOneSpectrum R) :
    CompactSpace (v.adicCompletionIntegers K) := by
  have : IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Valued.isClosed_valuationSubring _
  have hcomplete : CompleteSpace (v.adicCompletionIntegers K) := IsClosed.completeSpace_coe
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    ⟨hcomplete, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K)),
      finite_residueField_adicCompletion v⟩

end RiemannMasullo
