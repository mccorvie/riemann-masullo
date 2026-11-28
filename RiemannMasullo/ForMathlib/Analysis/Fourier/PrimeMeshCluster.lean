module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Topology.Instances.Int

/-! # Finite frequency clusters in fine prime logarithmic meshes -/

public noncomputable section
open Set Function
namespace RiemannMasullo

/-- A mesh interval of width greater than m+1 contains m distinct samples. -/
theorem exists_distinct_mesh_near (ξ δ L : ℝ) (m : ℕ) (hL : 0 < L)
    (hwide : (m : ℝ) + 1 < L * δ) :
    ∃ n : Fin m → ℤ, Injective n ∧ ∀ i, dist ((n i : ℝ) / L) ξ < δ := by
  let k : ℤ := ⌊ξ * L⌋
  have hklo : (k : ℝ) ≤ ξ * L := Int.floor_le _
  have hkhi : ξ * L < (k : ℝ)+1 := Int.lt_floor_add_one _
  refine ⟨fun i ↦ k + (i.val : ℤ),?_,fun i ↦ ?_⟩
  · intro i j hij
    apply Fin.ext
    exact_mod_cast (add_left_cancel hij)
  · have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    have him : (i.val : ℝ) < m := by exact_mod_cast i.isLt
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor
    · have hl : ξ - δ < ((k + (i.val : ℤ) : ℤ) : ℝ) / L := by
        apply (lt_div_iff₀ hL).mpr
        push_cast
        nlinarith
      linarith
    · have hu : ((k + (i.val : ℤ) : ℤ) : ℝ) / L < ξ + δ := by
        apply (div_lt_iff₀ hL).mpr
        push_cast
        nlinarith
      linarith

/-- Arbitrarily large prime logarithmic meshes contain any prescribed finite
number of distinct points in a continuity neighborhood of a real frequency. -/
theorem eventually_prime_mesh_cluster (g : ℝ → ℂ) (hg : Continuous g)
    (ξ ε : ℝ) (hε : 0 < ε) (m : ℕ) :
    ∃ B : ℕ, ∀ (p : ℕ), p.Prime → B < p →
      ∃ n : Fin m → ℤ, Injective n ∧
        ∀ i, ‖g ((n i : ℝ) / Real.log p) - g ξ‖ < ε := by
  obtain ⟨δ,hδ,hgδ⟩ := (Metric.continuousAt_iff.mp hg.continuousAt) ε hε
  obtain ⟨B,hB⟩ := exists_nat_gt (Real.exp (((m : ℝ)+1)/δ))
  refine ⟨B,fun p hp hBp ↦ ?_⟩
  have hBp' : (B : ℝ) < p := by exact_mod_cast hBp
  have hL : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlog : ((m : ℝ)+1)/δ < Real.log (p : ℝ) :=
    (Real.lt_log_iff_exp_lt (by exact_mod_cast hp.pos)).mpr
      (hB.trans hBp')
  have hwide : (m : ℝ)+1 < Real.log (p : ℝ) * δ := (div_lt_iff₀ hδ).mp hlog
  obtain ⟨n,hn,hnear⟩ := exists_distinct_mesh_near ξ δ (Real.log p) m hL hwide
  refine ⟨n,hn,fun i ↦ ?_⟩
  simpa only [dist_eq_norm] using hgδ (hnear i)

/-- Such a cluster can be chosen on a prime beyond any prescribed cutoff. -/
theorem exists_prime_mesh_cluster (g : ℝ → ℂ) (hg : Continuous g)
    (ξ ε : ℝ) (hε : 0 < ε) (m N : ℕ) :
    ∃ (p : ℕ), p.Prime ∧ N < p ∧
      ∃ n : Fin m → ℤ, Injective n ∧
        ∀ i, ‖g ((n i : ℝ) / Real.log p) - g ξ‖ < ε := by
  obtain ⟨B,hB⟩ := eventually_prime_mesh_cluster g hg ξ ε hε m
  obtain ⟨p,hpB,hp⟩ := Nat.exists_infinite_primes (max (B+1) (N+1))
  refine ⟨p,hp,by omega,hB p hp (by omega)⟩

end RiemannMasullo
