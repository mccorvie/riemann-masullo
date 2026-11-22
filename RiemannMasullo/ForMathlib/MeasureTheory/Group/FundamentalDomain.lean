module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.Unique

public section

open Function MeasureTheory Set

namespace RiemannMasullo

open scoped Pointwise ENNReal in
/-- A fundamental domain with the prescribed quotient mass pushes Haar measure to
the given Haar measure on the compact quotient. -/
theorem map_restrict_fundamentalDomain_eq
    {G Q : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [CommGroup Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q]
    [MeasurableSpace Q] [BorelSpace Q]
    (p : G →* Q) (hp : Continuous p) (hsur : Surjective p) (H : Subgroup G)
    [Countable H] (hker : H ≤ p.ker) (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegularCompactLTTop]
    (ν : Measure Q) [ν.IsHaarMeasure] [ν.InnerRegularCompactLTTop] {D : Set G}
    (hD : IsFundamentalDomain H D μ) (hmass : μ D = ν univ) :
    (μ.restrict D).map p = ν := by
  let ρ := (μ.restrict D).map p
  have hρ : ρ univ = ν univ := by
    rwa [Measure.map_apply hp.measurable MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ]
  let : IsFiniteMeasure ρ := ⟨hρ.trans_lt (measure_lt_top _ _)⟩
  let : ρ.InnerRegularCompactLTTop :=
    Measure.InnerRegularCompactLTTop.map_of_continuous hp
  let : ρ.IsMulLeftInvariant := ⟨fun a ↦ by
    obtain ⟨u, rfl⟩ := hsur a
    ext S hS
    have hA : MeasurableSet (p ⁻¹' S) := hp.measurable hS
    have hinv (h : H) : (fun x : G ↦ h • x) ⁻¹' (p ⁻¹' S) = p ⁻¹' S := by
      ext x
      change p (h.val * x) ∈ S ↔ p x ∈ S
      rw [map_mul, MonoidHom.mem_ker.mp (hker h.property), one_mul]
    rw [Measure.map_apply (measurable_const_mul _) hS]
    change (μ.restrict D).map p _ = (μ.restrict D).map p S
    rw [Measure.map_apply hp.measurable ((measurable_const_mul _ ) hS),
      Measure.map_apply hp.measurable hS, Measure.restrict_apply (hp.measurable ((measurable_const_mul _) hS)),
      Measure.restrict_apply hA]
    calc
      _ = μ ((fun x : G ↦ u * x) ⁻¹' ((p ⁻¹' S) ∩ u • D)) := by
        congr 1
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, Set.mem_smul_set_iff_inv_smul_mem,
          smul_eq_mul, inv_mul_cancel_left]
      _ = μ ((p ⁻¹' S) ∩ u • D) := measure_preimage_mul μ u _
      _ = _ := (hD.smul_of_comm u).measure_set_eq hD hA hinv⟩
  let c := Measure.haarScalarFactor ρ ν
  have heq (S : Set Q) : ρ S = c • ν S :=
    Measure.measure_isMulLeftInvariant_eq_smul_of_ne_top ρ ν (measure_ne_top _ _) (measure_ne_top _ _)
  have hc : (c : ℝ≥0∞) = 1 := by
    apply (ENNReal.mul_left_inj (NeZero.ne (ν univ))
      (measure_ne_top ν univ)).mp
    simpa only [ENNReal.smul_def, smul_eq_mul, one_mul] using (heq univ).symm.trans hρ
  ext S
  simpa only [ENNReal.smul_def, smul_eq_mul, hc, one_mul] using heq S

end RiemannMasullo
