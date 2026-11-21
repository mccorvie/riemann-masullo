module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.DSlope

@[expose] public section

open Filter Set
open scoped Topology BigOperators

namespace RiemannMasullo

private theorem analyticAt_exists_polar_expansion {a : ℂ → ℂ} {ρ : ℂ}
    (ha : AnalyticAt ℂ a ρ) (n : ℕ) :
    ∃ (H : ℂ → ℂ) (c : ℕ → ℂ), AnalyticAt ℂ H ρ ∧
      ∀ z ≠ ρ, a z * (z - ρ) ^ (-(n : ℤ)) =
        H z + ∑ k ∈ Finset.range n, c k * (z - ρ) ^ (-(k : ℤ) - 1) := by
  induction n generalizing a with
  | zero => exact ⟨a, 0, ha, by simp⟩
  | succ n ih =>
    obtain ⟨H, c, hH, he⟩ := ih (ha.dslope ρ)
    refine ⟨H, Function.update c n (a ρ), hH, fun z hz ↦ ?_⟩
    have hn : ∀ k ∈ Finset.range n, Function.update c n (a ρ) k = c k :=
      fun k hk ↦ Function.update_of_ne (Finset.mem_range.mp hk).ne _ _
    have hsum :
        ∑ k ∈ Finset.range n, Function.update c n (a ρ) k * (z - ρ) ^ (-(k : ℤ) - 1) =
          ∑ k ∈ Finset.range n, c k * (z - ρ) ^ (-(k : ℤ) - 1) :=
      Finset.sum_congr rfl fun k hk ↦ by rw [hn k hk]
    have hsplit : a z = dslope a ρ z * (z - ρ) + a ρ := by
      rw [mul_comm, ← smul_eq_mul, sub_smul_dslope a ρ z, sub_add_cancel]
    have hpow :
        (z - ρ) * (z - ρ) ^ (-(↑(n + 1) : ℤ)) = (z - ρ) ^ (-(n : ℤ)) := by
      conv_lhs => enter [1]; rw [← zpow_one (z - ρ)]
      rw [← zpow_add₀ (sub_ne_zero.mpr hz)]
      congr 1
      omega
    rw [Finset.sum_range_succ, hsum, Function.update_self, ← add_assoc, ← he z hz]
    push_cast
    rw [show -(n : ℤ) - 1 = -((n : ℤ) + 1) by omega]
    conv_lhs => enter [1]; rw [hsplit]
    rw [add_mul, mul_assoc]
    push_cast at hpow
    rw [hpow]

/-- A meromorphic germ agrees on a punctured neighborhood with an analytic
germ plus a finite sum of negative powers of the displacement from its center.
The term indexed by `k` has exponent `-k - 1`. -/
theorem MeromorphicAt.exists_polar_expansion {f : ℂ → ℂ} {ρ : ℂ}
    (hf : MeromorphicAt f ρ) :
    ∃ (n : ℕ) (H : ℂ → ℂ) (c : ℕ → ℂ), AnalyticAt ℂ H ρ ∧
      f =ᶠ[𝓝[≠] ρ] (fun z ↦ H z + ∑ k ∈ Finset.range n, c k * (z - ρ) ^ (-(k : ℤ) - 1)) := by
  obtain ⟨n, hn⟩ := hf
  obtain ⟨H, c, hH, he⟩ := analyticAt_exists_polar_expansion hn n
  refine ⟨n, H, c, hH, ?_⟩
  filter_upwards [self_mem_nhdsWithin (a := ρ) (s := ({ρ}ᶜ : Set ℂ))] with z hz
  rw [← he z (mem_compl_singleton_iff.mp hz), smul_eq_mul, zpow_neg, zpow_natCast,
    mul_comm ((z - ρ) ^ n) (f z), mul_assoc, mul_inv_cancel₀, mul_one]
  exact pow_ne_zero _ (sub_ne_zero.mpr (mem_compl_singleton_iff.mp hz))

end RiemannMasullo
