module

public import Mathlib.NumberTheory.LSeries.Positivity
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.Convex

/-!
# Landau's theorem for Dirichlet series with nonnegative coefficients

A Dirichlet series with nonnegative coefficients has a singularity at its finite real
abscissa of absolute convergence. If a meromorphic continuation exists there, the
leading Laurent coefficient is positive. This gives a criterion for bounding the
abscissa using only the real poles of a continuation to a half-plane.
-/

open Set Filter Function Complex LSeries Metric
open scoped Topology ComplexOrder

public noncomputable section
namespace RiemannMasullo

private theorem landauSeries_taylor_nonneg {f : ℂ → ℂ} {c t r : ℝ}
    (hf : DifferentiableOn ℂ f (ball (c : ℂ) r))
    (hd : ∀ n : ℕ, 0 ≤ (-1) ^ n * iteratedDeriv n f (c : ℂ))
    (ht : t ≤ c) (hb : (t : ℂ) ∈ ball (c : ℂ) r) : 0 ≤ f t := by
  have h := Complex.hasSum_taylorSeries_on_ball hf hb
  rw [← h.tsum_eq]
  apply tsum_nonneg
  intro m
  have hv : (t : ℂ) - c = (-1 : ℂ) * ((c - t : ℝ) : ℂ) := by push_cast; ring
  simp only [hv, mul_pow, smul_eq_mul]
  have hw : 0 ≤ ((c - t : ℝ) : ℂ) ^ m := by exact pow_nonneg (by exact_mod_cast sub_nonneg.mpr ht) _
  have hk : 0 ≤ (m.factorial : ℂ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  convert mul_nonneg (mul_nonneg hk hw) (hd m) using 1
  ring

/-- A continuation on a disc centered in the absolute convergence half-plane forces the
nonnegative series to converge at every real point of the disc to the left of its center. -/
theorem LSeriesSummable_of_nonneg_of_analytic_disc {a : ℕ → ℂ} (ha : 0 ≤ a) {c r : ℝ}
    (hc : abscissaOfAbsConv a < c) {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (ball (c : ℂ) r)) (he : H =ᶠ[𝓝 (c : ℂ)] LSeries a)
    {t : ℝ} (ht : t ≤ c) (hb : (t : ℂ) ∈ ball (c : ℂ) r) : LSeriesSummable a (t : ℂ) := by
  apply Summable.of_norm
  apply summable_of_sum_le (fun n ↦ norm_nonneg _) (c := (H t).re)
  intro S
  let p (n : ℕ) := if n ∈ S then a n else 0
  let D (s : ℂ) := ∑ n ∈ S, term a s n
  have hP (s : ℂ) : HasSum (term p s) (D s) := by
    have hh : (∑ n ∈ S, term p s n) = D s := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [term_def, p, hn]
    rw [← hh]
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    simp [term_def, p, hn]
  have hD : Differentiable ℂ D := by
    intro z
    apply DifferentiableAt.fun_sum
    intro n _
    by_cases hn : n = 0
    · simp [hn, term_zero]
    · simp only [term_of_ne_zero hn, div_eq_mul_inv]
      fun_prop (disch := simp [Complex.cpow_eq_zero_iff, hn])
  have hpos : 0 ≤ a - p := by
    intro n
    by_cases hn : n ∈ S
    · simp [p, hn]
    · simpa [p, hn] using ha n
  have he' : (fun z ↦ H z - D z) =ᶠ[𝓝 (c : ℂ)] LSeries (a - p) := by
    filter_upwards [he, (isOpen_re_gt_EReal _).mem_nhds (show abscissaOfAbsConv a < (c : ℂ).re from hc)] with z hz ha'
    have hsum := LSeriesSummable_of_abscissaOfAbsConv_lt_re ha'
    rw [LSeries_sub hsum (hP z).summable, hz]
    exact congrArg (LSeries a z - ·) (hP z).tsum_eq.symm
  have hsame : a - p =ᶠ[atTop] a := by
    filter_upwards [S.eventually_cofinite_notMem.filter_mono atTop_le_cofinite] with n hn
    simp [p, hn]
  have hc' := (abscissaOfAbsConv_congr' hsame).symm ▸ hc
  have hd (m : ℕ) : 0 ≤ (-1) ^ m * iteratedDeriv m (fun z ↦ H z - D z) (c : ℂ) := by
    rw [he'.iteratedDeriv_eq m]
    exact iteratedDeriv_alternating hpos hc' m
  have h := landauSeries_taylor_nonneg (hH.sub hD.differentiableOn) hd ht hb
  have hr := (Complex.le_def.mp h).1
  have hterm (n : ℕ) : ‖term a (t : ℂ) n‖ = (term a (t : ℂ) n).re := by
    exact_mod_cast congrArg Complex.re (Complex.norm_of_nonneg' (term_nonneg (ha n) t))
  simp only [hterm, ← Complex.re_sum]
  change _ ≤ (H t).re
  simpa only [Pi.sub_apply, Complex.zero_re, Complex.sub_re, sub_nonneg] using hr

/-- Landau's theorem. At a finite abscissa of absolute convergence, a Dirichlet series with
nonnegative coefficients has no analytic continuation through the real boundary point. -/
theorem LSeries_not_analyticAt_abscissa_of_nonneg {a : ℕ → ℂ} (ha : 0 ≤ a) {b : ℝ} (hab : abscissaOfAbsConv a = b)
    {H : ℂ → ℂ} (he : H =ᶠ[𝓝[{s : ℂ | b < s.re}] (b : ℂ)] LSeries a) :
    ¬ AnalyticAt ℂ H (b : ℂ) := by
  intro hH
  have hnear := hH.eventually_analyticAt.and (eventually_nhdsWithin_iff.mp he)
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.mp hnear
  let c := b + r / 4
  let t := b - r / 4
  have hdist (x y : ℝ) : dist (x : ℂ) (y : ℂ) = |x - y| := by
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hc : dist (c : ℂ) (b : ℂ) = r / 4 := by rw [hdist, abs_of_nonneg]; all_goals dsimp [c]; linarith
  have hU : ball (c : ℂ) (3 * r / 4) ⊆ ball (b : ℂ) r := by
    intro s hs
    apply mem_ball.mpr
    calc dist s (b : ℂ) ≤ dist s (c : ℂ) + dist (c : ℂ) (b : ℂ) := dist_triangle ..
         _ < r := by rw [hc]; linarith [mem_ball.mp hs]
  have hc' : b < c := by dsimp [c]; linarith
  have hec : H =ᶠ[𝓝 (c : ℂ)] LSeries a := by
    filter_upwards [isOpen_ball.mem_nhds (show (c : ℂ) ∈ ball (b : ℂ) r from mem_ball.mpr (by rw [hc]; linarith)),
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show b < (c : ℂ).re from hc')] with s hs hx
    exact (h (mem_ball.mp hs)).2 hx
  have ht : t < b := by dsimp [t]; linarith
  have ht' : (t : ℂ) ∈ ball (c : ℂ) (3 * r / 4) := by
    rw [mem_ball, hdist, abs_of_nonpos (sub_nonpos.mpr (le_trans ht.le hc'.le))]
    dsimp [c, t]; linarith
  have hs := LSeriesSummable_of_nonneg_of_analytic_disc ha (hab ▸ (by exact_mod_cast hc' : (b : EReal) < c))
    (fun s hs ↦ (h (mem_ball.mp (hU hs))).1.differentiableAt.differentiableWithinAt) hec
    (le_trans ht.le hc'.le) ht'
  have hab' := hs.abscissaOfAbsConv_le
  rw [hab] at hab'
  exact ht.not_ge (by exact_mod_cast hab')

/-- If a nonnegative Dirichlet series continues meromorphically through its finite real abscissa,
the abscissa is a pole with positive leading Laurent coefficient. -/
theorem LSeries_pole_at_abscissa_of_nonneg {a : ℕ → ℂ} (ha : 0 ≤ a) {b : ℝ} (hab : abscissaOfAbsConv a = b)
    {H : ℂ → ℂ} (hm : MeromorphicAt H (b : ℂ))
    (he : H =ᶠ[𝓝[{s : ℂ | b < s.re}] (b : ℂ)] LSeries a) :
    meromorphicOrderAt H (b : ℂ) < 0 ∧ 0 < meromorphicTrailingCoeffAt H (b : ℂ) := by
  let U := {s : ℂ | b < s.re}
  have hsub : U ⊆ {(b : ℂ)}ᶜ := fun z hz e ↦ by change z = b at e; simp [U, e] at hz
  have ho : meromorphicOrderAt H (b : ℂ) < 0 := by
    by_contra! h
    obtain ⟨g, hg, hEq⟩ := hm.meromorphicOrderAt_nonneg_iff.mp h
    exact LSeries_not_analyticAt_abscissa_of_nonneg ha hab ((hEq.symm.filter_mono (nhdsWithin_mono _ hsub)).trans he) hg
  refine ⟨ho, lt_of_le_of_ne ?_ (Ne.symm (hm.meromorphicTrailingCoeffAt_ne_zero (ne_top_of_lt ho)))⟩
  have hlim : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[>] b) (𝓝 (b : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt (x := b)).tendsto.mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[>] b) (𝓝[U] (b : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, self_mem_nhdsWithin⟩
  have ht := hm.tendsto_nhds_meromorphicTrailingCoeffAt.comp (hr.mono_right (nhdsWithin_mono _ hsub))
  let := Complex.orderClosedTopology
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
  filter_upwards [hr.eventually he, self_mem_nhdsWithin] with t hEq (ht : b < t)
  change 0 ≤ ((t : ℂ) - (b : ℂ)) ^ (-(meromorphicOrderAt H ↑b).untop₀) * H t
  rw [hEq, ← Complex.ofReal_sub, ← Complex.ofReal_zpow]
  apply mul_nonneg (by exact_mod_cast zpow_nonneg (sub_nonneg.mpr ht.le) _) _
  exact tsum_nonneg fun n ↦ term_nonneg (ha n) t

private theorem landauSeries_germ_right {a : ℕ → ℂ} {b x B : ℝ} (hbx : b < x) (hx : x ≤ B) (hab : abscissaOfAbsConv a = x)
    {H : ℂ → ℂ} (hm : MeromorphicOn H {s | b < s.re}) (he : ∀ z : ℂ, B < z.re → H z = LSeries a z) :
    H =ᶠ[𝓝[{z : ℂ | x < z.re}] (x : ℂ)] LSeries a := by
  let U := {z : ℂ | x < z.re}
  have hA : AnalyticOnNhd ℂ (LSeries a) U := by
    intro z hz
    exact LSeries_analyticOnNhd a z (hab ▸ (by exact_mod_cast hz : (x : EReal) < z.re))
  have hM : MeromorphicOn (H - LSeries a) U := fun z hz ↦ (hm z (hbx.trans hz)).sub (hA z hz).meromorphicAt
  let w : ℂ := (B:ℂ) + 1
  have hw : B < w.re := by simp [w]
  have hp : meromorphicOrderAt (H - LSeries a) w = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have h : ∀ᶠ z in 𝓝 w, B < z.re := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw
    filter_upwards [h.filter_mono (nhdsWithin_le_nhds (s := {w}ᶜ))] with z hz
    exact sub_eq_zero.mpr (he z hz)
  have hsub : U ⊆ {(x : ℂ)}ᶜ := fun z hz e ↦ by change z = x at e; simp [U, e] at hz
  filter_upwards [((hm x hbx).eventually_analyticAt).filter_mono (nhdsWithin_mono _ hsub), self_mem_nhdsWithin] with z hH (hz : z ∈ U)
  have h := meromorphicOrderAt_eq_top_iff.mp
    (hM.meromorphicOrderAt_eq_top_of_isPreconnected (convex_halfSpace_re_gt x).isPreconnected (hx.trans_lt hw) hz hp)
  have heq : H =ᶠ[𝓝[≠] z] LSeries a := h.mono fun _ e ↦ sub_eq_zero.mp e
  exact tendsto_nhds_unique_of_eventuallyEq hH.continuousAt.continuousWithinAt (hA _ hz).continuousAt.continuousWithinAt heq

/-- For a nonnegative Dirichlet series with a meromorphic continuation, the absence of real
poles with positive leading coefficient gives an upper bound on the abscissa. -/
theorem LSeries_abscissa_le_of_no_positive_pole {a : ℕ → ℂ} (ha : 0 ≤ a) {b B : ℝ} (hab : abscissaOfAbsConv a ≤ B)
    {H : ℂ → ℂ} (hm : MeromorphicOn H {s | b < s.re}) (he : ∀ z : ℂ, B < z.re → H z = LSeries a z)
    (hr : ∀ x : ℝ, b < x → x ≤ B →
      meromorphicOrderAt H (x : ℂ) < 0 → ¬ 0 < meromorphicTrailingCoeffAt H (x : ℂ)) :
    abscissaOfAbsConv a ≤ b := by
  by_contra! h
  let x := (abscissaOfAbsConv a).toReal
  have hx : abscissaOfAbsConv a = (x : EReal) :=
    (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hab) (ne_bot_of_gt h)).symm
  rw [hx] at h hab
  have hb : b < x := by exact_mod_cast h
  have hB : x ≤ B := by exact_mod_cast hab
  have hp := LSeries_pole_at_abscissa_of_nonneg ha hx (hm x hb) (landauSeries_germ_right hb hB hx hm he)
  exact hr x hb hB hp.1 hp.2

/-- If the only possible real singularities of the continuation are simple poles with
nonpositive residues, the nonnegative series converges throughout the open half-plane. -/
theorem LSeries_abscissa_le_of_nonpositive_residues {a : ℕ → ℂ} (ha : 0 ≤ a) {b B : ℝ} (hab : abscissaOfAbsConv a ≤ B)
    {H : ℂ → ℂ} (hm : MeromorphicOn H {s | b < s.re}) (he : ∀ z : ℂ, B < z.re → H z = LSeries a z)
    (hr : ∀ x : ℝ, b < x → x ≤ B → ∃ (c : ℝ) (g : ℂ → ℂ), c ≤ 0 ∧ AnalyticAt ℂ g x ∧
      H =ᶠ[𝓝[≠] (x : ℂ)] fun z ↦ (c : ℂ) / (z - x) + g z) : abscissaOfAbsConv a ≤ b := by
  apply LSeries_abscissa_le_of_no_positive_pole ha hab hm he
  intro x hbx hxB ho hpos
  obtain ⟨c, g, hc, hg, hEq⟩ := hr x hbx hxB
  let K (z : ℂ) := (c : ℂ) + (z - x) * g z
  have hK : AnalyticAt ℂ K x := analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hg)
  have he' : H =ᶠ[𝓝[≠] (x : ℂ)] fun z ↦ (z - x) ^ (-1 : ℤ) • K z := by
    filter_upwards [hEq, self_mem_nhdsWithin] with z hz (hn : z ≠ x)
    rw [hz]; simp only [K, zpow_neg_one, smul_eq_mul]
    field_simp [sub_ne_zero.mpr hn]
  by_cases hzero : c = 0
  · have E : H =ᶠ[𝓝[≠] (x : ℂ)] g := by simpa [hzero] using hEq
    exact (not_lt_of_ge ((hm x hbx).meromorphicOrderAt_nonneg_iff.mpr ⟨g, hg, E⟩)) ho
  · have hK₀ : K x ≠ 0 := by simpa [K] using hzero
    have hC := hK.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hK₀ he'
    rw [hC] at hpos
    have hz : 0 < c := by simpa [K] using hpos
    exact hc.not_gt hz

/-- A right-hand limit of (t − x) H(t) with nonpositive real part at every real x suffices
to bound the abscissa. No bound on the order at a possible complex pole is needed. -/
theorem LSeries_abscissa_le_of_nonpositive_limits {a : ℕ → ℂ} (ha : 0 ≤ a) {b B : ℝ} (hab : abscissaOfAbsConv a ≤ B)
    {H : ℂ → ℂ} (hm : MeromorphicOn H {s | b < s.re}) (he : ∀ z : ℂ, B < z.re → H z = LSeries a z)
    (hr : ∀ x : ℝ, b < x → x ≤ B → ∃ c : ℂ, c.re ≤ 0 ∧
      Tendsto (fun t : ℝ ↦ ((t : ℂ) - x) * H t) (𝓝[>] x) (𝓝 c)) : abscissaOfAbsConv a ≤ b := by
  apply LSeries_abscissa_le_of_no_positive_pole ha hab hm he
  intro x hbx hxB ho hpos
  obtain ⟨c, hc, hlim⟩ := hr x hbx hxB
  have ht : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[>] x) (𝓝 (x : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt (x := x)).tendsto.mono_left nhdsWithin_le_nhds
  have hp : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[>] x) (𝓝[≠] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨ht, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t (h : x < t)
    exact fun e ↦ h.ne' (Complex.ofReal_injective e)
  have hlead := (hm x hbx).tendsto_nhds_meromorphicTrailingCoeffAt.comp hp
  generalize horder : meromorphicOrderAt H (x : ℂ) = o at ho hlead
  cases o with
  | top => simp at ho
  | coe m =>
    have hmneg : m < 0 := by exact_mod_cast ho
    let k := (-m - 1).toNat
    have hk : -(m : ℤ) = ((k + 1 : ℕ) : ℤ) := by dsimp [k]; omega
    have hpow := (ht.sub_const (x : ℂ)).pow k
    have hsame : meromorphicTrailingCoeffAt H (x : ℂ) = (0 : ℂ) ^ k * c := by
      apply tendsto_nhds_unique hlead
      have hv := hpow.mul hlim
      simp only [sub_self] at hv
      apply hv.congr'
      filter_upwards with t
      simp only [Function.comp_apply, WithTop.untop₀_coe, hk,
        zpow_natCast, pow_succ, mul_assoc, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
    have hreal : 0 < (meromorphicTrailingCoeffAt H (x : ℂ)).re := (Complex.pos_iff.mp hpos).1
    rw [hsame, ← Complex.ofReal_zero, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at hreal
    exact hreal.not_ge (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (le_refl _) _) hc)

end RiemannMasullo
