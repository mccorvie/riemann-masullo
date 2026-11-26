module

public import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Polynomial mass bounds on integer unit intervals and convergence on Schwartz tests. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set Real
open scoped BigOperators ENNReal NNReal SchwartzMap Topology

namespace RiemannMasullo

private theorem summable_one_div_one_add_abs_int_sq :
    Summable (fun k : ℤ ↦ 1 / (1 + |(k : ℝ)|) ^ 2) := by
  have h : Summable (fun n : ℕ ↦ 1 / (1 + (n : ℝ)) ^ 2) := by
    simpa [Nat.cast_add, add_comm] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  apply Summable.of_nat_of_neg
  · simpa using h
  · simpa using h

/-- A polynomial bound on the mass of every integer unit interval controls the global
absolute integral of any measurable function with two extra powers of pointwise decay. -/
theorem integral_norm_le_of_polynomial_window_mass {E : Type*} [NormedAddCommGroup E]
    (μ : Measure ℝ) (C : ℝ≥0) (d : ℕ)
    (hμ : ∀ k : ℤ, μ (Icc (k : ℝ) (k + 1)) ≤ ENNReal.ofReal ((C : ℝ) * (1 + |(k : ℝ)|) ^ d))
    (f : ℝ → E) (hf : AEStronglyMeasurable f μ) (P : ℝ) (hP : 0 ≤ P)
    (hb : ∀ x, (1 + |x|) ^ (d + 2) * ‖f x‖ ≤ P) :
    Integrable f μ ∧ ∫ x, ‖f x‖ ∂μ ≤
      (2 ^ (d + 2) * P * C) * ∑' k : ℤ, 1 / (1 + |(k : ℝ)|) ^ 2 := by
  let T (k : ℤ) := Ico (k : ℝ) (k + 1)
  let U (k : ℤ) := 1 + |(k : ℝ)|
  let A (k : ℤ) := 2 ^ (d + 2) * P / U k ^ (d + 2)
  let b (k : ℤ) := 1 / U k ^ 2
  let D : ℝ := 2 ^ (d + 2) * P * C
  have hu (k : ℤ) : 0 < U k := by dsimp [U]; positivity
  have hA (k : ℤ) : 0 ≤ A k := by dsimp [A]; positivity
  have hμk (k : ℤ) : μ (T k) ≤ ENNReal.ofReal ((C : ℝ) * U k ^ d) :=
    (measure_mono Ico_subset_Icc_self).trans (hμ k)
  have hc (k : ℤ) : IntegrableOn (fun _ : ℝ ↦ A k) (T k) μ :=
    integrableOn_const ((hμk k).trans_lt ENNReal.ofReal_lt_top).ne
  have hfx (k : ℤ) (x : ℝ) (hx : x ∈ T k) : ‖f x‖ ≤ A k := by
    have hd : |(k : ℝ) - x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hnear : U k ≤ 2 * (1 + |x|) := by
      have htri := abs_add_le ((k : ℝ) - x) x
      rw [sub_add_cancel] at htri
      dsimp [U]
      linarith [abs_nonneg x]
    apply (le_div_iff₀ (pow_pos (hu k) _)).mpr
    calc
      _ ≤ ‖f x‖ * (2 * (1 + |x|)) ^ (d + 2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hu k).le hnear _) (norm_nonneg _)
      _ = 2 ^ (d + 2) * ((1 + |x|) ^ (d + 2) * ‖f x‖) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb x) (by positivity)
  have he (k : ℤ) : ∀ᵐ x ∂μ.restrict (T k), ‖f x‖ ≤ A k :=
    (ae_restrict_mem (measurableSet_Ico (α := ℝ))).mono (hfx k ·)
  have hi (k : ℤ) : IntegrableOn f (T k) μ := (hc k).mono' hf.restrict (he k)
  have hw (k : ℤ) : ∫ x in T k, ‖f x‖ ∂μ ≤ D * b k := by
    calc
      _ ≤ ∫ _ in T k, A k ∂μ := integral_mono_ae (hi k).norm (hc k) (he k)
      _ = μ.real (T k) * A k := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ ((C : ℝ) * U k ^ d) * A k := by
        apply mul_le_mul_of_nonneg_right _ (hA k)
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hμk k)).trans_eq (ENNReal.toReal_ofReal (by positivity))
      _ = _ := by
        dsimp [A, D, b]
        rw [pow_add (U k)]
        field_simp [(hu k).ne']
  have hsum : Summable fun k : ℤ ↦ D * b k := summable_one_div_one_add_abs_int_sq.mul_left D
  have hsumf := Summable.of_nonneg_of_le (fun k ↦ integral_nonneg (fun x ↦ norm_nonneg (f x))) hw hsum
  have hT : ⋃ k, T k = univ := iUnion_Ico_intCast ℝ
  have hfi := integrableOn_iUnion_of_summable_integral_norm hi hsumf
  rw [hT, integrableOn_univ] at hfi
  refine ⟨hfi, ?_⟩
  have hmass := hasSum_integral_iUnion (s := T) (fun _ ↦ measurableSet_Ico)
    (pairwise_disjoint_Ico_intCast ℝ) (hfi.norm.integrableOn (s := ⋃ k, T k))
  rw [hT, setIntegral_univ] at hmass
  calc
    _ = ∑' k, ∫ x in T k, ‖f x‖ ∂μ := hmass.tsum_eq.symm
    _ ≤ ∑' k, D * b k := hsumf.tsum_le_tsum hw hsum
    _ = _ := tsum_mul_left

/-- Vague convergence on smooth compactly supported tests extends to all Schwartz tests
when the limiting measure and, eventually, all approximating measures satisfy the same
polynomial bound on integer unit intervals. The limiting measure may have atoms. -/
theorem tendsto_integral_schwartz_of_polynomial_window_mass
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (l : Filter ι) (μ : ι → Measure ℝ) (ν : Measure ℝ) (C : ℝ≥0) (d : ℕ)
    (hμ : ∀ᶠ i in l, ∀ k : ℤ, μ i (Icc (k : ℝ) (k + 1)) ≤
      ENNReal.ofReal ((C : ℝ) * (1 + |(k : ℝ)|) ^ d))
    (hν : ∀ k : ℤ, ν (Icc (k : ℝ) (k + 1)) ≤ ENNReal.ofReal ((C : ℝ) * (1 + |(k : ℝ)|) ^ d))
    (hcompact : ∀ g : 𝓢(ℝ, E), HasCompactSupport (g : ℝ → E) →
      Tendsto (fun i ↦ ∫ x, g x ∂μ i) l (𝓝 (∫ x, g x ∂ν)))
    (f : 𝓢(ℝ, E)) : Tendsto (fun i ↦ ∫ x, f x ∂μ i) l (𝓝 (∫ x, f x ∂ν)) := by
  let p : Seminorm ℝ 𝓢(ℝ, E) := (Finset.Iic (d + 2, 0)).sup (schwartzSeminormFamily ℝ ℝ E)
  have hfamily : schwartzSeminormFamily ℝ ℝ E = (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) := by
    funext ⟨k, n⟩
    exact SchwartzMap.schwartzSeminormFamily_apply ℝ ℝ E k n
  have hp : Continuous p := (schwartz_withSeminorms ℝ ℝ E).continuous_finsetSup_seminorm _
  let K : ℝ := 2 ^ (d + 2) * 2 ^ (d + 2) * C * ∑' k : ℤ, 1 / (1 + |(k : ℝ)|) ^ 2
  let bounds (θ : Measure ℝ) := ∀ k : ℤ, θ (Icc (k : ℝ) (k + 1)) ≤
    ENNReal.ofReal ((C : ℝ) * (1 + |(k : ℝ)|) ^ d)
  have hcontrol (θ : Measure ℝ) (hθ : bounds θ) (g : 𝓢(ℝ, E)) :
      Integrable g θ ∧ ‖∫ x, g x ∂θ‖ ≤ K * p g := by
    have hpoint (x : ℝ) : (1 + |x|) ^ (d + 2) * ‖g x‖ ≤ 2 ^ (d + 2) * p g := by
      simpa [p, hfamily, Real.norm_eq_abs] using
        SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (d + 2, 0)) (n := 0)
          le_rfl le_rfl g x
    have hi := integral_norm_le_of_polynomial_window_mass θ C d hθ g g.continuous.aestronglyMeasurable
      (2 ^ (d + 2) * p g) (mul_nonneg (by positivity) (apply_nonneg _ _)) hpoint
    exact ⟨hi.1, (norm_integral_le_integral_norm _).trans (hi.2.trans_eq (by dsimp [K]; ring))⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let U : Set 𝓢(ℝ, E) := {g | K * p (f - g) < ε / 3}
  have hU : IsOpen U := isOpen_lt (continuous_const.mul (hp.comp (continuous_const.sub continuous_id))) continuous_const
  have hfU : f ∈ U := by change K * p (f - f) < ε / 3; simpa using (show 0 < ε / 3 by positivity)
  obtain ⟨g, hg, hnear⟩ := (SchwartzMap.dense_hasCompactSupport (E := ℝ) (F := E)).exists_mem_open hU ⟨f, hfU⟩
  have hnear' : K * p (f - g) < ε / 3 := hnear
  have hdist (θ : Measure ℝ) (hθ : bounds θ) : dist (∫ x, f x ∂θ) (∫ x, g x ∂θ) < ε / 3 := by
    rw [dist_eq_norm, ← integral_sub (hcontrol θ hθ f).1 (hcontrol θ hθ g).1]
    exact (hcontrol θ hθ (f - g)).2.trans_lt hnear'
  filter_upwards [hμ, Metric.tendsto_nhds.mp (hcompact g hg) (ε / 3) (by positivity)] with i hi hgi
  have ha := hdist (μ i) hi
  have hb := hdist ν hν
  rw [dist_comm] at hb
  exact (dist_triangle4 (∫ x, f x ∂μ i) (∫ x, g x ∂μ i) (∫ x, g x ∂ν) (∫ x, f x ∂ν)).trans_lt
    (by linarith)

/-- A positive vague limit inherits the polynomial growth of the approximants on integer
unit intervals. Testing against a translated smooth cutoff costs at most three neighboring
intervals and a factor of two in their weights. -/
theorem polynomial_window_mass_of_tendsto_compact
    {ι : Type*} (l : Filter ι) [l.NeBot] (μ : ι → Measure ℝ) (ν : Measure ℝ)
    [IsFiniteMeasureOnCompacts ν] (C : ℝ≥0) (d : ℕ)
    (hμ : ∀ᶠ i in l, ∀ k : ℤ, μ i (Icc (k : ℝ) (k + 1)) ≤
      ENNReal.ofReal ((C : ℝ) * (1 + |(k : ℝ)|) ^ d))
    (hcompact : ∀ g : 𝓢(ℝ, ℝ), HasCompactSupport (g : ℝ → ℝ) →
      Tendsto (fun i ↦ ∫ x, g x ∂μ i) l (𝓝 (∫ x, g x ∂ν))) (k : ℤ) :
    ν (Icc (k : ℝ) (k + 1)) ≤ ENNReal.ofReal ((3 * 2 ^ d * C : ℝ) * (1 + |(k : ℝ)|) ^ d) := by
  let W (j : ℤ) := Icc (j : ℝ) (j + 1)
  let U := W (k - 1) ∪ W k ∪ W (k + 1)
  let b : ContDiffBump ((k : ℝ) + 1 / 2) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let g : 𝓢(ℝ, ℝ) := b.hasCompactSupport.toSchwartzMap b.contDiff
  have hg : (g : ℝ → ℝ) = b := rfl
  have hgc : HasCompactSupport (g : ℝ → ℝ) := hg ▸ b.hasCompactSupport
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hcompact g hgc)
  have hone (x : ℝ) (hx : x ∈ W k) : 1 ≤ g x := by
    change 1 ≤ b x
    apply le_of_eq
    apply Eq.symm
    apply b.one_of_mem_closedBall
    change |x - ((k : ℝ) + 1 / 2)| ≤ (1 / 2 : ℝ)
    exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hout (x : ℝ) (hx : x ∉ U) : g x ≤ 0 := by
    change b x ≤ 0
    apply le_of_eq
    apply b.zero_of_le_dist
    change (1 : ℝ) ≤ |x - ((k : ℝ) + 1 / 2)|
    by_contra! h
    obtain ⟨hlo, hhi⟩ := abs_lt.mp h
    apply hx
    change x ∈ W (k - 1) ∪ W k ∪ W (k + 1)
    simp only [W, mem_union, mem_Icc, Int.cast_sub, Int.cast_add, Int.cast_one]
    by_cases hl : x ≤ k
    · exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
    by_cases hm : x ≤ (k : ℝ) + 1
    · exact Or.inl (Or.inr ⟨le_of_not_ge hl, hm⟩)
    · exact Or.inr ⟨le_of_not_ge hm, by linarith⟩
  have hcover (i : ι) : ENNReal.ofReal (∫ x, g x ∂μ i) ≤ μ i U :=
    integral_le_measure (fun _ _ ↦ b.le_one) hout
  have hνle : ν (W k) ≤ ENNReal.ofReal (∫ x, g x ∂ν) :=
    (g.continuous.integrable_of_hasCompactSupport hgc).measure_le_integral
      (ae_of_all _ fun x ↦ b.nonneg' x) hone
  apply hνle.trans
  apply le_of_tendsto hlim
  filter_upwards [hμ] with i hi
  let A : ℝ := (C : ℝ) * (2 * (1 + |(k : ℝ)|)) ^ d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hj (j : ℤ) (hjk : |(j : ℝ) - k| ≤ 1) : μ i (W j) ≤ ENNReal.ofReal A := by
    apply (hi j).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
    apply pow_le_pow_left₀ (by positivity)
    have htri := abs_add_le ((j : ℝ) - k) (k : ℝ)
    rw [sub_add_cancel] at htri
    linarith [abs_nonneg (k : ℝ)]
  have hm : μ i U ≤ ENNReal.ofReal A + ENNReal.ofReal A + ENNReal.ofReal A := by
    refine (measure_union_le _ _).trans ((add_le_add (measure_union_le _ _) le_rfl).trans ?_)
    apply add_le_add
    · exact add_le_add (hj (k - 1) (by push_cast; simp)) (hj k (by simp))
    · exact hj (k + 1) (by push_cast; simp)
  refine (hcover i).trans (hm.trans_eq ?_)
  rw [← ENNReal.ofReal_add hA hA, ← ENNReal.ofReal_add (add_nonneg hA hA) hA]
  congr 1
  dsimp [A]
  rw [mul_pow]
  ring

end RiemannMasullo
