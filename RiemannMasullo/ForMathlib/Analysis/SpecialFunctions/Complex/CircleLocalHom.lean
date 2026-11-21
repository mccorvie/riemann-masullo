module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Local homomorphisms into the circle

Coordinatewise circle exponentials on Euclidean space, and the fact that a circle-valued
local homomorphism on a ball of a real normed space is the exponential of a linear functional.
-/

@[expose] public section

open Filter Set Topology

namespace RiemannMasullo

/-- Coordinatewise circle exponentials are injective on the closed unit ball. -/
theorem circleExp_coord_injective {ι : Type*} [Fintype ι] {v w : EuclideanSpace ℝ ι}
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (h : ∀ i, Circle.exp (v i) = Circle.exp (w i)) : v = w := by
  ext i
  have hvi : |v i| ≤ 1 := (by simpa using PiLp.norm_apply_le v i : |v i| ≤ ‖v‖).trans hv
  have hwi : |w i| ≤ 1 := (by simpa using PiLp.norm_apply_le w i : |w i| ≤ ‖w‖).trans hw
  have h2 : (1 : ℝ) - (-1) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  exact Circle.exp_injOn_Icc h2 (abs_le.mp hvi) (abs_le.mp hwi) (h i)

/-- Near the identity, every point of a finite-dimensional torus has a small coordinatewise
logarithm. -/
theorem eventually_exists_small_circleLog {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 (1 : ι → Circle), ∃ v : EuclideanSpace ℝ ι, ‖v‖ < ε ∧
      ∀ i, Circle.exp (v i) = z i := by
  let lg : (ι → Circle) → EuclideanSpace ℝ ι := fun z ↦
    (EuclideanSpace.equiv ι ℝ).symm (fun i ↦ Complex.arg (z i : ℂ))
  have hlg : ContinuousAt lg 1 := by
    apply (EuclideanSpace.equiv ι ℝ).symm.continuous.continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    have h1 : ((1 : ι → Circle) i : ℂ) ∈ Complex.slitPlane := by simp
    show ContinuousAt (fun z : ι → Circle ↦ Complex.arg (z i : ℂ)) 1
    exact (Complex.continuousAt_arg h1).comp (f := fun z : ι → Circle ↦ (z i : ℂ))
      ((continuous_subtype_val.comp (continuous_apply i)).continuousAt)
  have hlg1 : lg 1 = 0 := by
    ext i
    simp [lg]
  have hev := hlg (Metric.ball_mem_nhds (lg 1) hε)
  filter_upwards [hev] with z hz
  refine ⟨lg z, by simpa [hlg1] using hz, fun i ↦ ?_⟩
  simp [lg]
/-- A circle-valued function on a real normed space which is continuous at zero and
multiplicative on a ball is the exponential of a real linear functional on that ball. -/
theorem exists_linearMap_circleExp_of_localHom {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ρ : ℝ} (hρ : 0 < ρ) (h : F → Circle) (hc : ContinuousAt h 0)
    (hadd : ∀ v w : F, ‖v‖ < ρ → ‖w‖ < ρ → h (v + w) = h v * h w) :
    ∃ l : F →ₗ[ℝ] ℝ, ∀ v, ‖v‖ < ρ → h v = Circle.exp (l v) := by
  have h0 : h 0 = 1 := by
    have e := hadd 0 0 (by simpa using hρ) (by simpa using hρ)
    rw [add_zero] at e
    exact mul_eq_left.mp e.symm
  -- Small multiples of a vector stay small.
  have hsmall : ∀ (v : F) (r : ℝ) (n : ℕ), 0 < n → ‖v‖ < r → ∀ k : ℕ, k ≤ n →
      ‖((k : ℝ) * (n : ℝ)⁻¹) • v‖ < r ∨ k = 0 := by
    intro v r n hn hv k hk
    by_cases hk0 : k = 0
    · exact Or.inr hk0
    left
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [norm_smul]
    have hle : ‖(k : ℝ) * (n : ℝ)⁻¹‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← div_eq_mul_inv, div_le_one hn']
      exact_mod_cast hk
    calc ‖(k : ℝ) * (n : ℝ)⁻¹‖ * ‖v‖ ≤ 1 * ‖v‖ :=
          mul_le_mul_of_nonneg_right hle (norm_nonneg v)
      _ < r := by simpa using hv
  have hsplit : ∀ (v : F) (k n : ℕ), (((k + 1 : ℕ) : ℝ) * (n : ℝ)⁻¹) • v =
      ((k : ℝ) * (n : ℝ)⁻¹) • v + (n : ℝ)⁻¹ • v := by
    intro v k n
    push_cast
    rw [add_mul, one_mul, add_smul]
  have hpow : ∀ v : F, ‖v‖ < ρ → ∀ n : ℕ, 0 < n → h v = h ((n : ℝ)⁻¹ • v) ^ n := by
    intro v hv n hn
    have key : ∀ k : ℕ, k ≤ n → h (((k : ℝ) * (n : ℝ)⁻¹) • v) = h ((n : ℝ)⁻¹ • v) ^ k := by
      intro k
      induction k with
      | zero => intro _; simp [h0]
      | succ k ih =>
        intro hk
        have h1 : ‖(n : ℝ)⁻¹ • v‖ < ρ := by
          rcases hsmall v ρ n hn hv 1 (by omega) with h1 | h1
          · simpa using h1
          · omega
        have hk' : ‖((k : ℝ) * (n : ℝ)⁻¹) • v‖ < ρ := by
          rcases hsmall v ρ n hn hv k (by omega) with h2 | h2
          · exact h2
          · simpa [h2] using hρ
        rw [hsplit, hadd _ _ hk' h1, ih (by omega), pow_succ]
    have e := key n le_rfl
    rwa [mul_inv_cancel₀ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0), one_smul] at e
  -- A local logarithm.
  set g : F → ℝ := fun v ↦ Complex.arg (h v : ℂ) with hgdef
  have hg : ∀ v, Circle.exp (g v) = h v := fun v ↦ Circle.exp_arg (h v)
  have hg0 : g 0 = 0 := by simp [g, h0]
  have hgc : ContinuousAt g 0 := by
    have hs : ((h 0 : Circle) : ℂ) ∈ Complex.slitPlane := by rw [h0]; simp
    exact (Complex.continuousAt_arg hs).comp (f := fun v ↦ (h v : ℂ))
      (continuous_subtype_val.continuousAt.comp hc)
  obtain ⟨δ, hδ, hδg⟩ : ∃ δ > 0, ∀ v : F, ‖v‖ < δ → |g v| < 1 := by
    obtain ⟨δ, hδ, H⟩ := Metric.continuousAt_iff.mp hgc 1 one_pos
    refine ⟨δ, hδ, fun v hv ↦ ?_⟩
    have := H (x := v) (by simpa using hv)
    simpa [hg0, Real.dist_eq] using this
  set δ' := min δ ρ / 2 with hδ'def
  have hδ' : 0 < δ' := by positivity
  have hδ'δ : 2 * δ' ≤ δ := by
    rw [hδ'def]; linarith [min_le_left δ ρ]
  have hδ'ρ : 2 * δ' ≤ ρ := by
    rw [hδ'def]; linarith [min_le_right δ ρ]
  have hgadd : ∀ v w, ‖v‖ < δ' → ‖w‖ < δ' → g (v + w) = g v + g w := by
    intro v w hv hw
    have hvw : ‖v + w‖ < δ := (norm_add_le v w).trans_lt (by linarith)
    have e : Circle.exp (g (v + w)) = Circle.exp (g v + g w) := by
      rw [Circle.exp_add, hg, hg, hg, hadd v w (by linarith) (by linarith)]
    have h2 : (2 : ℝ) - (-2) < 2 * Real.pi := by linarith [Real.pi_gt_three]
    have a1 := abs_lt.mp (hδg _ hvw)
    have a2 := abs_lt.mp (hδg v (by linarith))
    have a3 := abs_lt.mp (hδg w (by linarith))
    exact Circle.exp_injOn_Icc h2 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ e
  have hgscale : ∀ v, ‖v‖ < δ' → ∀ n : ℕ, 0 < n → g v = n * g ((n : ℝ)⁻¹ • v) := by
    intro v hv n hn
    have key : ∀ k : ℕ, k ≤ n → g (((k : ℝ) * (n : ℝ)⁻¹) • v) = k * g ((n : ℝ)⁻¹ • v) := by
      intro k
      induction k with
      | zero => intro _; simp [hg0]
      | succ k ih =>
        intro hk
        have h1 : ‖(n : ℝ)⁻¹ • v‖ < δ' := by
          rcases hsmall v δ' n hn hv 1 (by omega) with h1 | h1
          · simpa using h1
          · omega
        have hk' : ‖((k : ℝ) * (n : ℝ)⁻¹) • v‖ < δ' := by
          rcases hsmall v δ' n hn hv k (by omega) with h2 | h2
          · exact h2
          · simpa [h2] using hδ'
        rw [hsplit, hgadd _ _ hk' h1, ih (by omega)]
        push_cast
        ring
    have e := key n le_rfl
    rwa [mul_inv_cancel₀ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0), one_smul] at e
  have hshrink : ∀ (v : F) (n : ℕ), 0 < n → ‖v‖ < n * δ' → ‖(n : ℝ)⁻¹ • v‖ < δ' := by
    intro v n hn hv
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn'), inv_mul_lt_iff₀ hn']
    exact hv
  -- The global linear extension.
  let N : F → ℕ := fun v ↦ ⌈‖v‖ / δ'⌉₊ + 1
  have hN : ∀ v, ‖v‖ < N v * δ' := by
    intro v
    have h1 : ‖v‖ / δ' < N v := by
      have := Nat.le_ceil (‖v‖ / δ')
      have h2 : (⌈‖v‖ / δ'⌉₊ : ℝ) < N v := by simp [N]
      linarith
    exact (div_lt_iff₀ hδ').mp h1
  have hNpos : ∀ v, 0 < N v := fun v ↦ Nat.succ_pos _
  let Λf : F → ℝ := fun v ↦ (N v : ℝ) * g ((N v : ℝ)⁻¹ • v)
  have hΛ : ∀ v (n : ℕ), 0 < n → ‖v‖ < n * δ' → Λf v = n * g ((n : ℝ)⁻¹ • v) := by
    intro v n hn hvn
    have e1 := hgscale _ (hshrink v (N v) (hNpos v) (hN v)) n hn
    have e2 := hgscale _ (hshrink v n hn hvn) (N v) (hNpos v)
    have comm : (n : ℝ)⁻¹ • (N v : ℝ)⁻¹ • v = (N v : ℝ)⁻¹ • (n : ℝ)⁻¹ • v := smul_comm _ _ _
    change (N v : ℝ) * g ((N v : ℝ)⁻¹ • v) = n * g ((n : ℝ)⁻¹ • v)
    rw [e1, e2, comm]
    ring
  have hlarge : ∀ r : ℝ, ∃ n : ℕ, 0 < n ∧ r < n * δ' := by
    intro r
    obtain ⟨n, hn⟩ := exists_nat_gt (max r 0 / δ')
    have hpos : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (le_max_right r 0) hδ'.le) hn
    refine ⟨n, by exact_mod_cast hpos, ?_⟩
    have := (div_lt_iff₀ hδ').mp hn
    linarith [le_max_left r 0]
  have hΛadd : ∀ v w, Λf (v + w) = Λf v + Λf w := by
    intro v w
    obtain ⟨n, hn0, hn⟩ := hlarge (‖v‖ + ‖w‖)
    have hv : ‖v‖ < n * δ' := by linarith [norm_nonneg w]
    have hw : ‖w‖ < n * δ' := by linarith [norm_nonneg v]
    have hvw : ‖v + w‖ < n * δ' := (norm_add_le v w).trans_lt hn
    rw [hΛ (v + w) n hn0 hvw, hΛ v n hn0 hv, hΛ w n hn0 hw, smul_add,
      hgadd _ _ (hshrink v n hn0 hv) (hshrink w n hn0 hw), mul_add]
  have hΛ0 : Λf 0 = 0 := by
    have e := hΛadd 0 0
    rw [add_zero] at e
    linarith
  let Λh : F →+ ℝ := { toFun := Λf, map_zero' := hΛ0, map_add' := hΛadd }
  have hΛeq : ∀ v, ‖v‖ < δ' → Λf v = g v := by
    intro v hv
    rw [hΛ v 1 one_pos (by simpa using hv)]
    simp
  have hΛc : Continuous Λh := by
    apply continuous_of_continuousAt_zero
    have e : g =ᶠ[𝓝 0] Λf := by
      filter_upwards [Metric.ball_mem_nhds (0 : F) hδ'] with v hv
      exact (hΛeq v (by simpa using hv)).symm
    exact hgc.congr e
  refine ⟨(Λh.toRealLinearMap hΛc).toLinearMap, fun v hv ↦ ?_⟩
  change h v = Circle.exp (Λf v)
  obtain ⟨n, hn0, hn⟩ := hlarge ‖v‖
  rw [hΛ v n hn0 hn, Circle.exp_natCast_mul, hg, ← hpow v hv n hn0]


/-- The circle exponential turns finite sums into products. -/
theorem circleExp_sum {α : Type*} (s : Finset α) (g : α → ℝ) :
    Circle.exp (∑ i ∈ s, g i) = ∏ i ∈ s, Circle.exp (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, Circle.exp_add, ih]

/-- The circle exponential moves points by at most the length of the arc. -/
theorem dist_circleExp_one_le (s : ℝ) : dist (Circle.exp s) 1 ≤ |s| := by
  change dist ((Circle.exp s : Circle) : ℂ) ((1 : Circle) : ℂ) ≤ |s|
  rw [Circle.coe_exp, Circle.coe_one, dist_eq_norm, mul_comm]
  simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := s)

end RiemannMasullo
