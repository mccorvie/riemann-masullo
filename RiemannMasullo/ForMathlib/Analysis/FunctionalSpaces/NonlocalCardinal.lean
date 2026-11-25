module

public import RiemannMasullo.ForMathlib.Analysis.FunctionalSpaces.NonlocalEnergy
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Spacing-independent comparison for nonlocal cardinal interpolants

Positive-part tests bound any real minimum-energy cardinal interpolant between zero and
a positive single-point Green kernel, without assumptions on the spacing of the sites.
-/

@[expose] public noncomputable section
open MeasureTheory Set
namespace RiemannMasullo

private theorem memLp_posPart_jump (ν : Measure (ℝ × ℝ)) {u : ℝ → ℝ}
    (hu : Continuous u) (hdu : MemLp (fun p : ℝ × ℝ ↦ u p.1 - u p.2) 2 ν) :
    MemLp (fun p : ℝ × ℝ ↦ max (u p.1) 0 - max (u p.2) 0) 2 ν := by
  apply hdu.norm.mono' (by fun_prop)
  exact .of_forall fun p ↦ by
    simpa only [Real.norm_eq_abs] using abs_max_sub_max_le_abs (u p.1) (u p.2) 0

private theorem realNonlocalPairing_neg_left (ν : Measure (ℝ × ℝ)) (h v : ℝ → ℝ) :
    realNonlocalPairing volume ν (fun x ↦ -h x) v = -realNonlocalPairing volume ν h v := by
  have he (p : ℝ × ℝ) : (-h p.1 - -h p.2) * (v p.1 - v p.2) =
      -((h p.1 - h p.2) * (v p.1 - v p.2)) := by ring
  unfold realNonlocalPairing
  simp_rw [he, neg_mul, integral_neg]
  ring

/-- A real finite-energy cardinal interpolant is nonnegative. No separation or local
finiteness assumption on the interpolation sites is needed for this comparison. -/
theorem nonlocal_cardinal_nonneg (ν : Measure (ℝ × ℝ)) (S : Set ℝ) (z : ℝ)
    {h : ℝ → ℝ} (hc : Continuous h) (hh : MemLp h 2)
    (hJ : MemLp (fun p : ℝ × ℝ ↦ h p.1 - h p.2) 2 ν)
    (hz : h z = 1) (hS : ∀ y ∈ S, h y = 0)
    (horth : ∀ v : ℝ → ℝ, Continuous v → MemLp v 2 →
      MemLp (fun p : ℝ × ℝ ↦ v p.1 - v p.2) 2 ν → v z = 0 →
      (∀ y ∈ S, v y = 0) → realNonlocalPairing volume ν h v = 0) (x : ℝ) :
    0 ≤ h x := by
  let u : ℝ → ℝ := fun x ↦ -h x
  let v : ℝ → ℝ := fun x ↦ max (u x) 0
  have hu : Continuous u := hc.neg
  have hu₂ : MemLp u 2 := by simpa only [u, Pi.neg_def] using hh.neg
  have huJ : MemLp (fun p : ℝ × ℝ ↦ u p.1 - u p.2) 2 ν := by
    simpa only [u, Pi.neg_def, neg_sub_neg, neg_sub] using hJ.neg
  have hv : Continuous v := hu.max continuous_const
  have hv₂ : MemLp v 2 := hu₂.pos_part
  have hvJ : MemLp (fun p : ℝ × ℝ ↦ v p.1 - v p.2) 2 ν := memLp_posPart_jump ν hu huJ
  have hvz : v z = 0 := by simp [v, u, hz]
  have hvS : ∀ y ∈ S, v y = 0 := by intro y hy; simp [v, u, hS y hy]
  have hp : realNonlocalPairing volume ν u v = 0 := by
    rw [realNonlocalPairing_neg_left, horth v hv hv₂ hvJ hvz hvS, neg_zero]
  have hn := nonpos_of_realNonlocalPairing_posPart_eq_zero volume ν hu hu₂ huJ hp x
  exact neg_nonpos.mp hn

/-- The cardinal interpolant is bounded above by a positive single-point Green kernel.
Both orthogonality premises use the full finite-energy class, so the positive-part test
is justified by the contraction property of the jump form. -/
theorem nonlocal_cardinal_le_green (ν : Measure (ℝ × ℝ)) (S : Set ℝ) (z : ℝ)
    {h g : ℝ → ℝ} (hc : Continuous h) (gc : Continuous g)
    (hh : MemLp h 2) (hg : MemLp g 2)
    (hJ : MemLp (fun p : ℝ × ℝ ↦ h p.1 - h p.2) 2 ν)
    (gJ : MemLp (fun p : ℝ × ℝ ↦ g p.1 - g p.2) 2 ν)
    (hz : h z = 1) (gz : g z = 1) (hS : ∀ y ∈ S, h y = 0) (gpos : ∀ y, 0 ≤ g y)
    (horth : ∀ v : ℝ → ℝ, Continuous v → MemLp v 2 →
      MemLp (fun p : ℝ × ℝ ↦ v p.1 - v p.2) 2 ν → v z = 0 →
      (∀ y ∈ S, v y = 0) → realNonlocalPairing volume ν h v = 0)
    (gorth : ∀ v : ℝ → ℝ, Continuous v → MemLp v 2 →
      MemLp (fun p : ℝ × ℝ ↦ v p.1 - v p.2) 2 ν → v z = 0 →
      realNonlocalPairing volume ν g v = 0) (x : ℝ) : h x ≤ g x := by
  let u : ℝ → ℝ := fun x ↦ h x - g x
  let v : ℝ → ℝ := fun x ↦ max (u x) 0
  have hu : Continuous u := hc.sub gc
  have hu₂ : MemLp u 2 := by simpa only [u, Pi.sub_def] using hh.sub hg
  have huJ : MemLp (fun p : ℝ × ℝ ↦ u p.1 - u p.2) 2 ν := by
    apply (hJ.sub gJ).ae_eq
    exact .of_forall fun p ↦ by dsimp [u]; ring
  have hv : Continuous v := hu.max continuous_const
  have hv₂ : MemLp v 2 := hu₂.pos_part
  have hvJ : MemLp (fun p : ℝ × ℝ ↦ v p.1 - v p.2) 2 ν := memLp_posPart_jump ν hu huJ
  have hvz : v z = 0 := by simp [v, u, hz, gz]
  have hvS : ∀ y ∈ S, v y = 0 := by
    intro y hy
    simp only [v, u, hS y hy, zero_sub]
    exact max_eq_right (neg_nonpos.mpr (gpos y))
  have hp : realNonlocalPairing volume ν u v = 0 := by
    rw [realNonlocalPairing_sub_left volume ν hh hg hv₂ hJ gJ hvJ,
      horth v hv hv₂ hvJ hvz hvS, gorth v hv hv₂ hvJ hvz, sub_self]
  exact sub_nonpos.mp
    (nonpos_of_realNonlocalPairing_posPart_eq_zero volume ν hu hu₂ huJ hp x)

end RiemannMasullo
