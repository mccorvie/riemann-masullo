module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.PrimeMeshCluster
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Absolute mass in fine frequency meshes -/

public noncomputable section
open Set Function
namespace RiemannMasullo

/-- A nonzero continuous profile has absolute lattice mass at least proportional
to the inverse mesh size, once the mesh is sufficiently fine. -/
theorem abs_mesh_sum_ge_linear (g : ℝ → ℂ) (ξ : ℝ)
    (hg : ContinuousAt g ξ) (hξ : g ξ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : ℝ, 0 < B ∧ ∀ L : ℝ, B < L →
      Summable (fun n : ℤ ↦ ‖g ((n : ℝ) / L)‖) →
      c * L ≤ ∑' n : ℤ, ‖g ((n : ℝ) / L)‖ := by
  have hc : 0 < ‖g ξ‖ := norm_pos_iff.mpr hξ
  obtain ⟨δ,hδ,hgδ⟩ := (Metric.continuousAt_iff.mp hg) (‖g ξ‖/2) (half_pos hc)
  refine ⟨δ * ‖g ξ‖ / 8, by positivity, 4/δ, by positivity, fun L hL hs ↦ ?_⟩
  have hLpos : 0 < L := lt_trans (by positivity : 0 < 4/δ) hL
  have hwide : 4 < L * δ := (div_lt_iff₀ hδ).mp hL
  let m : ℕ := ⌊δ * L / 2⌋₊
  have hmle : (m : ℝ) ≤ δ * L / 2 := Nat.floor_le (by positivity)
  have hmlt : δ * L / 2 < (m : ℝ)+1 := Nat.lt_floor_add_one _
  have hmlo : δ * L / 4 ≤ (m : ℝ) := by nlinarith
  obtain ⟨n,hn,hnear⟩ := exists_distinct_mesh_near ξ δ L m hLpos (by nlinarith)
  have hnorm (i : Fin m) : ‖g ξ‖ / 2 ≤ ‖g ((n i : ℝ) / L)‖ := by
    have hsmall : ‖g ((n i : ℝ) / L) - g ξ‖ < ‖g ξ‖ / 2 :=
      by simpa only [dist_eq_norm] using hgδ (hnear i)
    have htri := norm_sub_le_norm_sub_add_norm_sub (g ξ) (g ((n i : ℝ) / L)) 0
    rw [sub_zero, sub_zero, norm_sub_rev (g ξ)] at htri
    linarith
  have hsum : (∑ i : Fin m, ‖g ((n i : ℝ) / L)‖) ≤
      ∑' k : ℤ, ‖g ((k : ℝ) / L)‖ := by
    classical
    have he : (∑ k ∈ Finset.univ.image n, ‖g ((k : ℝ) / L)‖) =
        ∑ i : Fin m, ‖g ((n i : ℝ) / L)‖ :=
      Finset.sum_image (fun i _ j _ hij ↦ hn hij)
    rw [← he]
    exact Summable.sum_le_tsum _ (fun i _ ↦ norm_nonneg _) hs
  have hfinite : (m : ℝ) * (‖g ξ‖ / 2) ≤ ∑ i : Fin m, ‖g ((n i : ℝ) / L)‖ := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) ↦ hnorm i)
  have hprod := mul_le_mul_of_nonneg_right hmlo (half_pos hc).le
  nlinarith

end RiemannMasullo
