module

public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.BakerLowerBound
public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.Explicit

/-! # The Baker core, proved

`BakerCoreExists` (`BakerLowerBound.lean`) is the statement of HOL Light's `BAKER_CORE_EXISTS`,
translated literally, with integer data written as reals that are integers. `baker_core_exists`
(`Baker/Explicit.lean`) proves the same statement with that data typed as integers. This file
translates between the two. `bakerCoreExists` proves `BakerCoreExists`, so the theorems of
`BakerLowerBound.lean` that take it as a hypothesis hold outright. -/

@[expose] public section

namespace RiemannMasullo.Baker

open Finset

/-- An `IntPoly` (coefficients real numbers that are integers) is an `intpoly` (coefficients
integers). -/
theorem intpoly_of_intPoly {v : Finset ℕ} {n : ℕ → ℕ} {b : ℝ} {g : (ℕ → ℂ) → ℂ}
    (h : IntPoly v n b g) : intpoly v n b g := by
  classical
  obtain ⟨s, c, e, hce, hb, hg⟩ := h
  let c' : ℕ → ℤ := fun k ↦ if hk : k ∈ s then (hce k hk).1.choose else 0
  have hc' : ∀ k ∈ s, ((c' k : ℤ) : ℝ) = c k := fun k hk ↦ by
    simp only [c', dif_pos hk]
    exact (hce k hk).1.choose_spec.symm
  refine ⟨s, c', e, fun k hk ↦ (hce k hk).2, ?_, fun x ↦ ?_⟩
  · rwa [sum_congr rfl fun k hk ↦ by rw [hc' k hk]]
  · rw [hg x]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [← hc' k hk, Complex.ofReal_intCast]

/-- The statement of HOL Light's `BAKER_CORE_EXISTS`, proved: `baker_core_exists` with its
integer data read as reals that are integers. -/
theorem bakerCoreExists : BakerCoreExists := by
  classical
  intro n m lg a d H e G0 Dx hn hDx hG0 ha hind
  -- the coefficients of the minimal relations, as integers
  let a' : ℕ → ℕ → ℤ := fun r j ↦
    if hr : r ∈ Icc 1 n then ((ha r hr).2.2.1 j).1.choose else 0
  have ha' : ∀ r ∈ Icc 1 n, ∀ j, ((a' r j : ℤ) : ℝ) = a r j := fun r hr j ↦ by
    simp only [a', dif_pos hr]
    exact ((ha r hr).2.2.1 j).1.choose_spec.symm
  have hcore := baker_core_exists n m lg a' d H e G0 Dx hn hDx hG0
    (fun r hr ↦ by
      obtain ⟨hd, hH, hbound, hlead, hroot⟩ := ha r hr
      refine ⟨hd, hH, fun j ↦ by rw [ha' r hr j]; exact (hbound j).2, ?_, ?_⟩
      · intro h0
        apply hlead
        rw [← ha' r hr (d r), h0, Int.cast_zero]
      · rw [← hroot]
        refine sum_congr rfl fun j _ ↦ ?_
        rw [← ha' r hr j, Complex.ofReal_intCast])
    (fun b hb r hr ↦ by
      have := hind (fun r ↦ (b r : ℝ)) (fun r _ ↦ ⟨b r, rfl⟩)
        (by simpa only [Complex.ofReal_intCast] using hb) r hr
      exact_mod_cast this)
  obtain ⟨C, hC⟩ := hcore
  refine ⟨C, fun B θ g dx ax hB hθ hax hg hgn ↦ ?_⟩
  -- the coefficients of the minimal relations of the further numbers, as integers
  let ax' : ℕ → ℕ → ℤ := fun r j ↦
    if hr : r ∈ Icc (n + 1) (n + m) then ((hax r hr).2.2.1 j).1.choose else 0
  have hax' : ∀ r ∈ Icc (n + 1) (n + m), ∀ j, ((ax' r j : ℤ) : ℝ) = ax r j := fun r hr j ↦ by
    simp only [ax', dif_pos hr]
    exact ((hax r hr).2.2.1 j).1.choose_spec.symm
  refine hC B θ g dx ax' hB hθ (fun r hr ↦ ?_) (fun j hj ↦ intpoly_of_intPoly (hg j hj)) hgn
  obtain ⟨h1, hD, hbound, hlead, hroot⟩ := hax r hr
  refine ⟨h1, hD, fun j ↦ by rw [hax' r hr j]; exact (hbound j).2, ?_, ?_⟩
  · intro h0
    apply hlead
    rw [← hax' r hr (dx r), h0, Int.cast_zero]
  · rw [← hroot]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [← hax' r hr j, Complex.ofReal_intCast]

end RiemannMasullo.Baker
