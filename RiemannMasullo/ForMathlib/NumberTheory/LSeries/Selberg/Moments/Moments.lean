module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.TaperSpec
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Moments.AbsoluteSecond
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Moments.Bulk
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Moments.ChooseWindow
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Moments.SignedSecond

public section

open MeasureTheory

namespace RiemannMasullo.Selberg

/-- Card 46. For arbitrarily short windows, a single normalized mollifier has positive bulk
mass. Its squared bulk mass bounds both scaled window second moments with a uniform positive
constant in the absolute-window bound.
Titchmarsh, §10.22, pp. 278–279, in the existing Lean normalization. -/
theorem moments : ∃ c > (0 : ℝ), ∀ ε > (0 : ℝ), ∃ (T N : ℕ) (b : ℕ → ℝ) (h : ℝ),
    1 ≤ T ∧ 1 ≤ N ∧ b 1 = 1 ∧ (∀ n ∈ Finset.Icc 1 N, |b n| ≤ 1) ∧
    0 < h ∧ h ≤ 1 ∧ h < ε ∧
    let w := spectralLineJet_selbergWeight T N b
    let P := h * ∫ u in h..(T : ℝ), |w u * hardyZ u|
    0 < P ∧ 4*T*second T (win (fun u ↦ w u*hardyZ u) h) ≤ P^2 ∧
      c*T*second T (win (fun u ↦ |w u*hardyZ u|) h) ≤ P^2 := by
  obtain ⟨B, hB, hsigned⟩ := signed_second
  obtain ⟨A, hA, habsolute⟩ := absolute_second
  obtain ⟨D₀, hD, N₀, hbulk⟩ := bulk
  let a := D₀^2 / (4 * B)
  let c := D₀^2 / A
  have ha : 0 < a := div_pos (sq_pos_of_pos hD) (by positivity)
  have hc : 0 < c := div_pos (sq_pos_of_pos hD) hA
  have hBa : 4 * B * a = D₀^2 := mul_div_cancel₀ _ (by positivity)
  have hcA : c * A = D₀^2 := div_mul_cancel₀ _ hA.ne'
  refine ⟨c, hc, ?_⟩
  intro ε hε
  obtain ⟨N, hN, hwindow⟩ := choose_window a ε ha hε N₀
  let h := (a * Real.log N)⁻¹
  obtain ⟨hh, hhalf, hsmall⟩ : 0 < h ∧ h ≤ 1/2 ∧ h < ε := hwindow
  have hN₂ : 2 ≤ N := (le_max_left ..).trans hN
  have hN₁ : 1 ≤ N := by omega
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN₁
  have hT : 1 ≤ H N := one_le_pow₀ hN₁
  have hTcast : (H N : ℝ) = (N : ℝ)^100 := by simp [H]
  have hlog : (Real.log N)⁻¹ = a * h := by
    rw [show h = (a * Real.log N)⁻¹ from rfl, mul_inv, mul_inv_cancel_left₀ ha.ne']
  obtain ⟨hone, hbd⟩ := taper_spec N hN₂
  refine ⟨H N, N, beta N, h, hT, hN₁, hone, hbd, hh, hhalf.trans (by norm_num), hsmall, ?_⟩
  let P := h * ∫ u in h..(H N : ℝ), |signal N u|
  have hmass : h * (D₀ * (N : ℝ)^75) ≤ P :=
    mul_le_mul_of_nonneg_left (hbulk N ((le_max_right ..).trans hN) h hh hhalf) hh.le
  have hpos : 0 < h * (D₀ * (N : ℝ)^75) := by positivity
  have hsq : D₀^2 * h^2 * (N : ℝ)^150 ≤ P^2 := calc
    _ = (h * (D₀ * (N : ℝ)^75))^2 := by ring
    _ ≤ P^2 := pow_le_pow_left₀ hpos.le hmass 2
  refine ⟨hpos.trans_le hmass, ?_, ?_⟩
  · calc
      4 * (H N : ℝ) * second (H N) (win (signal N) h)
          ≤ 4 * (H N : ℝ) * (B*h*(N : ℝ)^50 / Real.log N) :=
            mul_le_mul_of_nonneg_left (hsigned N hN₂ h hh hhalf) (by positivity)
      _ = D₀^2 * h^2 * (N : ℝ)^150 := by rw [hTcast, div_eq_mul_inv, hlog, ← hBa]; ring
      _ ≤ P^2 := hsq
  · calc
      c * (H N : ℝ) * second (H N) (win (fun u ↦ |signal N u|) h)
          ≤ c * (H N : ℝ) * (A*h^2*(N : ℝ)^50) :=
            mul_le_mul_of_nonneg_left (habsolute N hN₂ h hh hhalf) (by positivity)
      _ = D₀^2 * h^2 * (N : ℝ)^150 := by rw [hTcast, ← hcA]; ring
      _ ≤ P^2 := hsq

end RiemannMasullo.Selberg
