module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.TaperSpec
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.BulkLower

public section

open MeasureTheory

namespace RiemannMasullo.Selberg

/-- Card 44. For all sufficiently large N and every 0 < h ≤ 1/2, the absolute signal integral from
h to N¹⁰⁰ is bounded below by a positive constant times N⁷⁵.
Titchmarsh, Lemmas 10.20–10.21, pp. 277–278. -/
theorem bulk : ∃ D₀ > (0 : ℝ), ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℝ, 0 < h → h ≤ 1/2 →
    D₀ * (N : ℝ)^75 ≤ ∫ u in h..(H N : ℝ), |signal N u| := by
  obtain ⟨c, hc, η, hη, T₀, hT₀, hbulk⟩ := spectralLineJet_selberg_mollified_bulk_lower
  obtain ⟨N₀, h₀⟩ := exists_nat_ge (max (2 * T₀) (Real.sqrt 2 / η))
  refine ⟨c, hc, N₀, ?_⟩
  intro N hN h _ hh
  have hcut := h₀.trans (Nat.cast_le.mpr hN)
  have hlarge := (le_max_left _ _).trans hcut
  have hN₂ : 2 ≤ (N : ℝ) := by linarith
  have hN₁ : 1 ≤ (N : ℝ) := by linarith
  let X := (N : ℝ)^100 / 2
  have hX : T₀ ≤ X := by
    dsimp [X]
    linarith [le_self_pow₀ hN₁ (by decide : 100 ≠ 0)]
  have hlen : (N : ℝ) ≤ η * Real.sqrt X := by
    have hηN := (div_le_iff₀ hη).mp ((le_max_right _ _).trans hcut)
    have hsqrt : Real.sqrt X = (N : ℝ)^50 / Real.sqrt 2 := by
      dsimp only [X]
      rw [Real.sqrt_div (by positivity),
        show (N : ℝ)^100 = ((N : ℝ)^50)^2 by ring, Real.sqrt_sq (by positivity)]
    rw [hsqrt, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    calc (N : ℝ) * Real.sqrt 2 ≤ N * ((N : ℝ) * η) := by gcongr
         _ ≤ N * ((N : ℝ)^49 * η) := by
           gcongr
           exact le_self_pow₀ hN₁ (by decide)
         _ = η * (N : ℝ)^50 := by ring
  obtain ⟨hone, hbd⟩ := taper_spec N (by exact_mod_cast hN₂)
  have hb := hbulk X hX N (beta N) (by exact_mod_cast hN₁) hlen hone hbd h (by linarith)
  have hend : 2 * X = (H N : ℝ) := by simp only [X, H, Nat.cast_pow]; ring
  have hscale : 4 * X = 2 * (H N : ℝ) := by linarith
  have hpow : (H N : ℝ) ^ (3 / 4 : ℝ) = (N : ℝ)^75 := by
    rw [H, Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)]
    norm_num
  rw [hend, hpow, hscale] at hb
  have hw := (spectralLineJet_selbergWeight_spec (H N) N (beta N)).2
  simp_rw [signal, abs_mul, abs_of_nonneg (hw _)]
  simpa only [spectralLineJet_selbergWeight, Complex.ofReal_div, Complex.ofReal_ofNat] using hb

end RiemannMasullo.Selberg
