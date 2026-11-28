module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-! # Eigenfunctionals and the spectrum of a quotient operator -/

public section

open Function
namespace RiemannMasullo

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- If normalized eigenfunctionals for an ambient operator have arbitrarily small
restrictions to an invariant closed subspace, their common eigenvalue lies in the spectrum
of the induced quotient operator. The preimage bound for a surjective map would otherwise
give a positive lower bound on every restriction. -/
theorem mem_spectrum_quotient_of_small_restrictions (N : Submodule ℂ E)
    [hN : IsClosed (N : Set E)] (T : E →L[ℂ] E) (U : (E ⧸ N) →L[ℂ] (E ⧸ N))
    (hU : ∀ x, U (N.mkQ x) = N.mkQ (T x)) (z : ℂ)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ L : E →L[ℂ] ℂ, ‖L‖ = 1 ∧
      (∀ x, L (T x) = z * L x) ∧ ‖L.comp N.subtypeL‖ < ε) :
    z ∈ spectrum ℂ U := by
  classical
  rw [spectrum.mem_iff]
  intro hinv
  let A : E →L[ℂ] E := z • ContinuousLinearMap.id ℂ E - T
  let D := A.coprod N.subtypeL
  have hsurj : Surjective D := by
    intro x
    obtain ⟨q, hq⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp hinv).surjective (N.mkQ x)
    obtain ⟨y, rfl⟩ := N.mkQ_surjective q
    change z • (N.mkQ y) - U (N.mkQ y) = N.mkQ x at hq
    have hmem : x - A y ∈ N := by
      apply (Submodule.Quotient.mk_eq_zero N).mp
      change N.mkQ (x - A y) = 0
      rw [map_sub, sub_eq_zero]
      change N.mkQ x = N.mkQ (z • y - T y)
      rw [map_sub, map_smul, ← hU]
      exact hq.symm
    refine ⟨(y, ⟨x - A y, hmem⟩), ?_⟩
    change A y + (x - A y) = x
    abel
  let : CompleteSpace N := hN.completeSpace_coe
  obtain ⟨C, hC, hpre⟩ := D.exists_preimage_norm_le hsurj
  obtain ⟨L, hL, he, hε⟩ := hsmall (1 / C) (by positivity)
  have hbound : ‖L‖ ≤ ‖L.comp N.subtypeL‖ * C := by
    apply L.opNorm_le_bound (by positivity)
    intro x
    obtain ⟨⟨y, v⟩, hy, hv⟩ := hpre x
    have hy' : A y + (v : E) = x := hy
    have hAy : L (A y) = 0 := by
      change L (z • y - T y) = 0
      rw [map_sub, map_smul, he, smul_eq_mul, sub_self]
    have hLx : L x = (L.comp N.subtypeL) v := by
      rw [← hy', map_add, hAy, zero_add]
      rfl
    rw [hLx, mul_assoc]
    exact ((L.comp N.subtypeL).le_opNorm v).trans (mul_le_mul_of_nonneg_left
      ((le_max_right ‖y‖ ‖v‖).trans hv) (norm_nonneg _))
  rw [hL] at hbound
  exact (not_lt_of_ge hbound) ((lt_div_iff₀ hC).mp hε)

/-- A spectral value outside the circle of radius `r` forces some orbit to be
unbounded after division by `r ^ n`. -/
theorem exists_unbounded_rescaled_orbit_of_mem_spectrum (U : E →L[ℂ] E)
    {z : ℂ} (hz : z ∈ spectrum ℂ U) {r : ℝ} (hr : 0 < r) (hrz : r < ‖z‖) :
    ∃ x : E, ∀ C : ℝ, ∃ n : ℕ, C < ‖(U ^ n) x‖ / r ^ n := by
  by_contra! h
  let A (n : ℕ) : E →L[ℂ] E := ((r ^ n : ℝ)⁻¹ : ℂ) • U ^ n
  have hA (n : ℕ) : ‖A n‖ = ‖U ^ n‖ / r ^ n := by
    simp [A, norm_smul, abs_of_pos hr, div_eq_inv_mul]
  obtain ⟨C, hC⟩ := banach_steinhaus (g := A) (fun x ↦ by
    obtain ⟨c, hc⟩ := h x
    refine ⟨c, fun n ↦ ?_⟩
    simpa [A, norm_smul, abs_of_pos hr, div_eq_inv_mul] using hc n)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C ((one_lt_div hr).mpr hrz)
  rcases subsingleton_or_nontrivial E with hE | hE
  · apply (spectrum.mem_iff.mp hz)
    rw [Subsingleton.elim (algebraMap ℂ (E →L[ℂ] E) z - U) 1]
    exact isUnit_one
  have hpow := spectrum.norm_le_norm_of_mem (spectrum.pow_mem_pow U n hz)
  rw [norm_pow] at hpow
  exact hn.not_ge (calc
    (‖z‖ / r) ^ n = ‖z‖ ^ n / r ^ n := div_pow ..
    _ ≤ ‖U ^ n‖ / r ^ n := div_le_div_of_nonneg_right hpow (pow_nonneg hr.le _)
    _ ≤ C := (hA n) ▸ hC n)

end RiemannMasullo
