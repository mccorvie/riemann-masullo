module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_MixedFourierLimit

/-! # Decay of the mixed product cutoff kernel along the orbit of `p`

`Sec4_MixedFourierLimit` defines the kernel `mixedCutoffKernel p b` on `ℝ × ℚ_[p]`, the Fourier
distribution of the product cutoff with profile `b`, as the sum of the Fourier transforms of the
valuation shells. This file bounds it and follows it along the diagonal action of the powers of
`p`.

* `norm_mixedCutoffKernel_le`: off the two axes the kernel at `(u, v)` is at most a constant
  times `(|u| ‖v‖) ^ (-2)`. This is the reciprocal shell and the lacunary tail of
  `mixedShellFourier_hasSum`, with `Lacunary.absolute_sum_le`.
* `exists_mixedOrbit_separation`: for `x` and `z` with both coordinates bounded above and away
  from zero, the product `|z.1 - p ^ n x.1| ‖z.2 - p ^ n x.2‖` is at least a constant times
  `p ^ |n|` once `|n|` is large. For `n → +∞` the real factor grows and the `p`-adic factor is
  the norm of `z.2`; for `n → -∞` the real factor is about `|z.1|` and the `p`-adic factor
  grows.
* `exists_norm_mixedCutoffKernel_orbit_le`: so the kernel at `z - p ^ n x` is at most a constant
  times `p ^ (-2 |n|)`, uniformly in such `x` and `z`, and these bounds are summable over `n`
  (`summable_zpow_abs_inv_sq`).

Nothing is said here about the finitely many remaining `n`, where the kernel has its
logarithmic singularity, nor about any operator built from the kernel. -/

@[expose] public noncomputable section

namespace RiemannMasullo.MixedCutoff

open MeasureTheory Filter Set
open scoped Topology Classical

variable (p : ℕ) [Fact p.Prime]

local instance : MeasurableSpace ℚ_[p] := borel _
local instance : BorelSpace ℚ_[p] := ⟨rfl⟩

local notation "shellB" => tamagawaFourier volume realCutoffCharacter

/-- Paper: Theorem 12.4.1.1, (12.4.1.8), p. 517, for the rational field with the real place and
one prime. Off the two axes, the mixed product cutoff kernel at `(u, v)` is at most
`C (p + 1) / (|u| ‖v‖) ^ 2`, where `C` is the constant of the quadratic decay of the real
Fourier transform of the profile.
Reconstruction: The paper does not state this. The kernel is the one of
`Sec4_MixedFourierLimit`. -/
theorem norm_mixedCutoffKernel_le (b : ℝ → ℂ) (he : ∀ x, shellB b (-x) = shellB b x)
    {C : ℝ} (hC : 0 ≤ C) (hd : Lacunary.Decays (shellB b) C)
    {u : ℝ} (hu : u ≠ 0) {v : ℚ_[p]} (hv : v ≠ 0) :
    ‖mixedCutoffKernel p b (u, v)‖ ≤ C * ((p : ℝ) + 1) / (|u| * ‖v‖) ^ 2 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp
  have hr : 0 < |u| * ‖v‖ := mul_pos (abs_pos.mpr hu) (norm_pos_iff.mpr hv)
  have hr2 : 0 < (|u| * ‖v‖) ^ 2 := pow_pos hr 2
  have hval := (mixedShellFourier_hasSum p b he hC hd hu hv).tsum_eq
  change mixedCutoffKernel p b (u, v) = _ at hval
  rw [hval]
  have hpi : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
  have hpi1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have hn1 : ‖(-((p : ℝ)⁻¹ : ℂ))‖ = (p : ℝ)⁻¹ := by
    rw [norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg hp0.le]
  have hn2 : ‖(1 - ((p : ℝ)⁻¹ : ℂ))‖ = 1 - (p : ℝ)⁻¹ := by
    have h : (1 - ((p : ℝ)⁻¹ : ℂ)) = ((1 - (p : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [h, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have h1 : ‖shellB b ((p : ℝ) ^ (-1 : ℤ) * (|u| * ‖v‖)) * (-((p : ℝ)⁻¹ : ℂ))‖ ≤
      C * p / (|u| * ‖v‖) ^ 2 := by
    have hx : 0 < (p : ℝ) ^ (-1 : ℤ) * (|u| * ‖v‖) := mul_pos (zpow_pos hp0 _) hr
    have hB := hd _ hx
    rw [norm_mul, hn1]
    have hden : ((p : ℝ) ^ (-1 : ℤ) * (|u| * ‖v‖)) ^ 2 ≤
        (1 + (p : ℝ) ^ (-1 : ℤ) * (|u| * ‖v‖)) ^ 2 := by nlinarith
    have hpos : 0 < ((p : ℝ) ^ (-1 : ℤ) * (|u| * ‖v‖)) ^ 2 := pow_pos hx 2
    calc ‖shellB b ((p : ℝ) ^ (-1 : ℤ) * (|u| * ‖v‖))‖ * (p : ℝ)⁻¹
        ≤ C / ((p : ℝ) ^ (-1 : ℤ) * (|u| * ‖v‖)) ^ 2 * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (hB.trans (div_le_div_of_nonneg_left hC hpos hden)) hpi.le
      _ = C * p / (|u| * ‖v‖) ^ 2 := by
          rw [zpow_neg_one]
          field_simp
  have h2 : ‖(∑' j : ℕ, shellB b ((p : ℝ) ^ j * (|u| * ‖v‖))) * (1 - ((p : ℝ)⁻¹ : ℂ))‖ ≤
      C / (|u| * ‖v‖) ^ 2 := by
    rw [norm_mul, hn2]
    have habs := Lacunary.absolute hp hC hd hr
    have hsum := (norm_tsum_le_tsum_norm habs).trans (Lacunary.absolute_sum_le hp hC hd hr)
    calc ‖∑' j : ℕ, shellB b ((p : ℝ) ^ j * (|u| * ‖v‖))‖ * (1 - (p : ℝ)⁻¹)
        ≤ C / (|u| * ‖v‖) ^ 2 * (1 - (p : ℝ)⁻¹)⁻¹ * (1 - (p : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right hsum (by linarith)
      _ = C / (|u| * ‖v‖) ^ 2 := by
          rw [mul_assoc, inv_mul_cancel₀ (by linarith : (1 - (p : ℝ)⁻¹) ≠ 0), mul_one]
  calc ‖shellB b ((p : ℝ) ^ (-1 : ℤ) * (|u| * ‖v‖)) * (-((p : ℝ)⁻¹ : ℂ)) +
        (∑' j : ℕ, shellB b ((p : ℝ) ^ j * (|u| * ‖v‖))) * (1 - ((p : ℝ)⁻¹ : ℂ))‖
      ≤ C * p / (|u| * ‖v‖) ^ 2 + C / (|u| * ‖v‖) ^ 2 := (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = C * ((p : ℝ) + 1) / (|u| * ‖v‖) ^ 2 := by ring

/-- For points `x`, `z` of `ℝ × ℚ_[p]` whose coordinates have absolute value between `c > 0` and
`C₀`, the product of the real and `p`-adic distances from `z` to `p ^ n x` is at least
`c ^ 2 / 2 * p ^ |n|` for all `n` with `|n| ≥ N₀`, where `N₀` depends only on `p`, `c`, `C₀`. -/
theorem exists_mixedOrbit_separation {c : ℝ} (C₀ : ℝ) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ x z : ℝ × ℚ_[p],
      c ≤ |x.1| → |x.1| ≤ C₀ → c ≤ ‖x.2‖ → ‖x.2‖ ≤ C₀ →
      c ≤ |z.1| → |z.1| ≤ C₀ → c ≤ ‖z.2‖ → ‖z.2‖ ≤ C₀ →
      ∀ n : ℤ, (N₀ : ℤ) ≤ |n| →
        c ^ 2 / 2 * (p : ℝ) ^ |n| ≤
          |z.1 - (p : ℝ) ^ n * x.1| * ‖z.2 - (p : ℚ_[p]) ^ n * x.2‖ := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp
  obtain ⟨N₀, hN₀⟩ := pow_unbounded_of_one_lt (2 * C₀ / c) hp
  refine ⟨N₀, fun x z hx1 hx1' hx2 hx2' hz1 hz1' hz2 hz2' n hn ↦ ?_⟩
  have hC₀ : 0 < C₀ := hc.trans_le (hx1.trans hx1')
  set P : ℝ := (p : ℝ) ^ |n| with hP
  have hPpos : 0 < P := zpow_pos hp0 _
  have hPbig : 2 * C₀ < c * P := by
    have h1 : (p : ℝ) ^ N₀ ≤ P := by
      rw [hP, ← zpow_natCast]
      exact zpow_le_zpow_right₀ hp.le hn
    have h2 := (div_lt_iff₀ hc).mp (hN₀.trans_le h1)
    linarith
  have hPinv : P⁻¹ * C₀ ≤ c / 2 := by
    rw [inv_mul_le_iff₀ hPpos]
    linarith
  have hnormP (k : ℤ) : ‖(p : ℚ_[p]) ^ k * x.2‖ = (p : ℝ) ^ (-k) * ‖x.2‖ := by
    rw [norm_mul, Padic.norm_p_zpow]
  rcases le_or_gt 0 n with h0 | h0
  · -- `n ≥ 0`: the real factor grows, the `p`-adic factor is `‖z.2‖`.
    have habs : |n| = n := abs_of_nonneg h0
    have hPn : (p : ℝ) ^ n = P := by rw [hP, habs]
    have hPneg : (p : ℝ) ^ (-n) = P⁻¹ := by rw [zpow_neg, hPn]
    have hreal : c * P / 2 ≤ |z.1 - (p : ℝ) ^ n * x.1| := by
      rw [hPn]
      have h1 : |P * x.1| - |z.1| ≤ |z.1 - P * x.1| := by
        rw [abs_sub_comm z.1]
        exact abs_sub_abs_le_abs_sub _ _
      rw [abs_mul, abs_of_pos hPpos] at h1
      nlinarith [mul_le_mul_of_nonneg_left hx1 hPpos.le]
    have hsmall : ‖(p : ℚ_[p]) ^ n * x.2‖ < ‖z.2‖ := by
      rw [hnormP, hPneg]
      have h1 : P⁻¹ * ‖x.2‖ ≤ P⁻¹ * C₀ :=
        mul_le_mul_of_nonneg_left hx2' (inv_pos.mpr hPpos).le
      linarith
    have hpadic : c ≤ ‖z.2 - (p : ℚ_[p]) ^ n * x.2‖ := by
      have hne : ‖z.2‖ ≠ ‖-((p : ℚ_[p]) ^ n * x.2)‖ := by
        rw [norm_neg]
        exact hsmall.ne'
      rw [sub_eq_add_neg, Padic.add_eq_max_of_ne hne]
      exact hz2.trans (le_max_left _ _)
    calc c ^ 2 / 2 * P = c * P / 2 * c := by ring
      _ ≤ |z.1 - (p : ℝ) ^ n * x.1| * ‖z.2 - (p : ℚ_[p]) ^ n * x.2‖ :=
        mul_le_mul hreal hpadic hc.le (abs_nonneg _)
  · -- `n < 0`: the real factor is about `|z.1|`, the `p`-adic factor grows.
    have habs : |n| = -n := abs_of_neg h0
    have hPneg : (p : ℝ) ^ (-n) = P := by rw [hP, habs]
    have hPn : (p : ℝ) ^ n = P⁻¹ := by
      rw [← hPneg, zpow_neg, inv_inv]
    have hreal : c / 2 ≤ |z.1 - (p : ℝ) ^ n * x.1| := by
      rw [hPn]
      have h1 : |z.1| - |P⁻¹ * x.1| ≤ |z.1 - P⁻¹ * x.1| := abs_sub_abs_le_abs_sub _ _
      rw [abs_mul, abs_of_pos (inv_pos.mpr hPpos)] at h1
      have h2 : P⁻¹ * |x.1| ≤ P⁻¹ * C₀ :=
        mul_le_mul_of_nonneg_left hx1' (inv_pos.mpr hPpos).le
      linarith
    have hbig : ‖z.2‖ < ‖(p : ℚ_[p]) ^ n * x.2‖ := by
      rw [hnormP, hPneg]
      nlinarith [mul_le_mul_of_nonneg_left hx2 hPpos.le]
    have hpadic : c * P ≤ ‖z.2 - (p : ℚ_[p]) ^ n * x.2‖ := by
      have hne : ‖z.2‖ ≠ ‖-((p : ℚ_[p]) ^ n * x.2)‖ := by
        rw [norm_neg]
        exact hbig.ne
      rw [sub_eq_add_neg, Padic.add_eq_max_of_ne hne, norm_neg, hnormP, hPneg]
      refine le_trans ?_ (le_max_right _ _)
      rw [mul_comm c P]
      exact mul_le_mul_of_nonneg_left hx2 hPpos.le
    calc c ^ 2 / 2 * P = c / 2 * (c * P) := by ring
      _ ≤ |z.1 - (p : ℝ) ^ n * x.1| * ‖z.2 - (p : ℚ_[p]) ^ n * x.2‖ :=
        mul_le_mul hreal hpadic (mul_nonneg hc.le hPpos.le) (abs_nonneg _)

/-- The bounds `p ^ (-2 |n|)` are summable over the integers. -/
theorem summable_zpow_abs_inv_sq :
    Summable (fun n : ℤ ↦ (((p : ℝ) ^ |n|)⁻¹) ^ 2) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp
  have hq0 : 0 ≤ ((p : ℝ)⁻¹) ^ 2 := sq_nonneg _
  have hq1 : ((p : ℝ)⁻¹) ^ 2 < 1 :=
    pow_lt_one₀ (inv_pos.mpr hp0).le (inv_lt_one_of_one_lt₀ hp) (by norm_num)
  have hgeo : Summable (fun n : ℕ ↦ (((p : ℝ)⁻¹) ^ 2) ^ n) := summable_geometric_of_lt_one hq0 hq1
  have hterm (n : ℕ) : (((p : ℝ) ^ (n : ℤ))⁻¹) ^ 2 = (((p : ℝ)⁻¹) ^ 2) ^ n := by
    rw [zpow_natCast, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm]
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hgeo.congr fun n ↦ ?_
    rw [Nat.abs_cast, hterm]
  · refine hgeo.congr fun n ↦ ?_
    rw [abs_neg, Nat.abs_cast, hterm]

/-- Paper: Theorem 12.4.1.1, (12.4.1.8), p. 517, for the rational field with the real place and
one prime. Along the diagonal action of the powers of `p`, the mixed product cutoff kernel at
`z - p ^ n x` is at most a constant times `p ^ (-2 |n|)` once `|n|` is large, uniformly for `x`
and `z` with both coordinates between `c > 0` and `C₀` in absolute value. With
`summable_zpow_abs_inv_sq` this is the absolute convergence of the sum of the kernel over the
orbit, away from finitely many `n`.
Reconstruction: The paper does not state this. -/
theorem exists_norm_mixedCutoffKernel_orbit_le (b : ℝ → ℂ)
    (he : ∀ x, shellB b (-x) = shellB b x) {C : ℝ} (hC : 0 ≤ C)
    (hd : Lacunary.Decays (shellB b) C) {c : ℝ} (C₀ : ℝ) (hc : 0 < c) :
    ∃ (N₀ : ℕ) (A : ℝ), 0 ≤ A ∧ ∀ x z : ℝ × ℚ_[p],
      c ≤ |x.1| → |x.1| ≤ C₀ → c ≤ ‖x.2‖ → ‖x.2‖ ≤ C₀ →
      c ≤ |z.1| → |z.1| ≤ C₀ → c ≤ ‖z.2‖ → ‖z.2‖ ≤ C₀ →
      ∀ n : ℤ, (N₀ : ℤ) ≤ |n| →
        ‖mixedCutoffKernel p b (z.1 - (p : ℝ) ^ n * x.1, z.2 - (p : ℚ_[p]) ^ n * x.2)‖ ≤
          A * (((p : ℝ) ^ |n|)⁻¹) ^ 2 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp
  obtain ⟨N₀, hsep⟩ := exists_mixedOrbit_separation p C₀ hc
  have hc2 : 0 < c ^ 2 / 2 := by positivity
  refine ⟨N₀, C * ((p : ℝ) + 1) / (c ^ 2 / 2) ^ 2, by positivity,
    fun x z hx1 hx1' hx2 hx2' hz1 hz1' hz2 hz2' n hn ↦ ?_⟩
  have hPpos : 0 < (p : ℝ) ^ |n| := zpow_pos hp0 _
  have hlow := hsep x z hx1 hx1' hx2 hx2' hz1 hz1' hz2 hz2' n hn
  have hpos : 0 < c ^ 2 / 2 * (p : ℝ) ^ |n| := mul_pos hc2 hPpos
  have hprod : 0 < |z.1 - (p : ℝ) ^ n * x.1| * ‖z.2 - (p : ℚ_[p]) ^ n * x.2‖ :=
    hpos.trans_le hlow
  have hu : z.1 - (p : ℝ) ^ n * x.1 ≠ 0 := by
    intro h
    rw [h, abs_zero, zero_mul] at hprod
    exact lt_irrefl _ hprod
  have hv : z.2 - (p : ℚ_[p]) ^ n * x.2 ≠ 0 := by
    intro h
    rw [h, norm_zero, mul_zero] at hprod
    exact lt_irrefl _ hprod
  refine (norm_mixedCutoffKernel_le p b he hC hd hu hv).trans ?_
  have hCp : 0 ≤ C * ((p : ℝ) + 1) := mul_nonneg hC (by linarith)
  calc C * ((p : ℝ) + 1) / (|z.1 - (p : ℝ) ^ n * x.1| * ‖z.2 - (p : ℚ_[p]) ^ n * x.2‖) ^ 2
      ≤ C * ((p : ℝ) + 1) / (c ^ 2 / 2 * (p : ℝ) ^ |n|) ^ 2 :=
        div_le_div_of_nonneg_left hCp (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hlow 2)
    _ = C * ((p : ℝ) + 1) / (c ^ 2 / 2) ^ 2 * (((p : ℝ) ^ |n|)⁻¹) ^ 2 := by
        rw [mul_pow, inv_pow]
        field_simp

end RiemannMasullo.MixedCutoff
